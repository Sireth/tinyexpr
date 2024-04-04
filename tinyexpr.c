// SPDX-License-Identifier: Zlib
/*
 * TINYEXPR - Tiny recursive descent parser and evaluation engine in C
 *
 * Copyright (c) 2015-2020 Lewis Van Winkle
 *
 * http://CodePlea.com
 *
 * This software is provided 'as-is', without any express or implied
 * warranty. In no event will the authors be held liable for any damages
 * arising from the use of this software.
 *
 * Permission is granted to anyone to use this software for any purpose,
 * including commercial applications, and to alter it and redistribute it
 * freely, subject to the following restrictions:
 *
 * 1. The origin of this software must not be misrepresented; you must not
 * claim that you wrote the original software. If you use this software
 * in a product, an acknowledgement in the product documentation would be
 * appreciated but is not required.
 * 2. Altered source versions must be plainly marked as such, and must not be
 * misrepresented as being the original software.
 * 3. This notice may not be removed or altered from any source distribution.
 */

/* COMPILE TIME OPTIONS */

/* Exponentiation associativity:
For a^b^c = (a^b)^c and -a^b = (-a)^b do nothing.
For a^b^c = a^(b^c) and -a^b = -(a^b) uncomment the next line.*/
/* #define TE_POW_FROM_RIGHT */

/* Logarithms
For log = base 10 log do nothing
For log = natural log uncomment the next line. */
/* #define TE_NAT_LOG */

#include "tinyexpr.h"
#include <stdlib.h>
#include <math.h>
#include <string.h>
#include <stdio.h>
#include <ctype.h>
#include <limits.h>

#ifndef NAN
#define NAN (0.0/0.0)
#endif

#ifndef INFINITY
#define INFINITY (1.0/0.0)
#endif


typedef double (*te_fun2)(double, double);

enum {
    /// Нет токена
    TOK_NULL = TE_CLOSURE7+1,
    /// Ошибка
    TOK_ERROR,
    /// Конец
    TOK_END,
    /// Разделитель
    TOK_SEP,
    /// Открытая скобка
    TOK_OPEN,
    /// Закрытая скобка
    TOK_CLOSE,
    /// Число
    TOK_NUMBER,
    /// Переменная
    TOK_VARIABLE,
    /// Оператор
    TOK_INFIX
};


enum {TE_CONSTANT = 1};


typedef struct state {
    /// Указатель на начало строки
    const char *start;
    /// Текущее положение в строке
    const char *next;
    /// Тип токена
    int type;
    union {
        /// Значение
        double value;
        /// Указатель на переменную
        const double *bound;
        /// Действие над операндами
        const void *function;
    };
    void *context;

    /// Переменные которые будут участвовать в обработке
    const te_variable *lookup;
    /// Количество переменных
    int lookup_len;
} state;

/// Определение типа
#define TYPE_MASK(TYPE) ((TYPE)&0x0000001F)

/// Проверка на чистую функцию
#define IS_PURE(TYPE) (((TYPE) & TE_FLAG_PURE) != 0)
/// Проверка на функцию
#define IS_FUNCTION(TYPE) (((TYPE) & TE_FUNCTION0) != 0)
#define IS_CLOSURE(TYPE) (((TYPE) & TE_CLOSURE0) != 0)
/// Получение количества параметров
#define ARITY(TYPE) ( ((TYPE) & (TE_FUNCTION0 | TE_CLOSURE0)) ? ((TYPE) & 0x00000007) : 0 )
/// Создание выражения
#define NEW_EXPR(type, ...) new_expr((type), (const te_expr*[]){__VA_ARGS__})
/// Проверка на nullptr
#define CHECK_NULL(ptr, ...) if ((ptr) == NULL) { __VA_ARGS__; return NULL; }

/**
 * Создание нового выражения
 * @param type      [in] Тип выражения
 * @param parameters[in] Параметры выражение
 * @return Созданное выражение
 */
static te_expr *new_expr(const int type, const te_expr *parameters[]) {
    /// Количество параметров у функции/оператора
    const int arity = ARITY(type);
    /// Размер параметров
    const int psize = sizeof(void*) * arity;
    /// Размер выражения
    const int size = (sizeof(te_expr) - sizeof(void*)) + psize + (IS_CLOSURE(type) ? sizeof(void*) : 0);
    /// Выделяем память для выражения
    te_expr *ret = malloc(size);
    CHECK_NULL(ret);

    /// Зануляем все
    memset(ret, 0, size);
    /// Копируем все параметры если они есть
    if (arity && parameters) {
        memcpy(ret->parameters, parameters, psize);
    }
    ret->type = type;
    ret->bound = 0;
    return ret;
}

/**
 * Очистка всех параметров выражения
 * @param n[in] Выражение
 */
void te_free_parameters(te_expr *n) {
    if (!n) return;
    switch (TYPE_MASK(n->type)) {
        case TE_FUNCTION7: case TE_CLOSURE7: te_free(n->parameters[6]);     /* Falls through. */
        case TE_FUNCTION6: case TE_CLOSURE6: te_free(n->parameters[5]);     /* Falls through. */
        case TE_FUNCTION5: case TE_CLOSURE5: te_free(n->parameters[4]);     /* Falls through. */
        case TE_FUNCTION4: case TE_CLOSURE4: te_free(n->parameters[3]);     /* Falls through. */
        case TE_FUNCTION3: case TE_CLOSURE3: te_free(n->parameters[2]);     /* Falls through. */
        case TE_FUNCTION2: case TE_CLOSURE2: te_free(n->parameters[1]);     /* Falls through. */
        case TE_FUNCTION1: case TE_CLOSURE1: te_free(n->parameters[0]);
    }
}

/**
 * Удаляем выражение
 * @param n[in] Выражение
 */
void te_free(te_expr *n) {
    if (!n) return;
    te_free_parameters(n);
    free(n);
}


static double pi(void) {return 3.14159265358979323846;}
static double e(void) {return 2.71828182845904523536;}
static double fac(double a) {/* simplest version of fac */
    if (a < 0.0)
        return NAN;
    if (a > UINT_MAX)
        return INFINITY;
    unsigned int ua = (unsigned int)(a);
    unsigned long int result = 1, i;
    for (i = 1; i <= ua; i++) {
        if (i > ULONG_MAX / result)
            return INFINITY;
        result *= i;
    }
    return (double)result;
}
static double ncr(double n, double r) {
    if (n < 0.0 || r < 0.0 || n < r) return NAN;
    if (n > UINT_MAX || r > UINT_MAX) return INFINITY;
    unsigned long int un = (unsigned int)(n), ur = (unsigned int)(r), i;
    unsigned long int result = 1;
    if (ur > un / 2) ur = un - ur;
    for (i = 1; i <= ur; i++) {
        if (result > ULONG_MAX / (un - ur + i))
            return INFINITY;
        result *= un - ur + i;
        result /= i;
    }
    return result;
}
static double npr(double n, double r) {return ncr(n, r) * fac(r);}

#ifdef _MSC_VER
#pragma function (ceil)
#pragma function (floor)
#endif

static const te_variable functions[] = {
    /* must be in alphabetical order */
    {"abs", fabs,     TE_FUNCTION1 | TE_FLAG_PURE, 0},
    {"acos", acos,    TE_FUNCTION1 | TE_FLAG_PURE, 0},
    {"asin", asin,    TE_FUNCTION1 | TE_FLAG_PURE, 0},
    {"atan", atan,    TE_FUNCTION1 | TE_FLAG_PURE, 0},
    {"atan2", atan2,  TE_FUNCTION2 | TE_FLAG_PURE, 0},
    {"ceil", ceil,    TE_FUNCTION1 | TE_FLAG_PURE, 0},
    {"cos", cos,      TE_FUNCTION1 | TE_FLAG_PURE, 0},
    {"cosh", cosh,    TE_FUNCTION1 | TE_FLAG_PURE, 0},
    {"e", e,          TE_FUNCTION0 | TE_FLAG_PURE, 0},
    {"exp", exp,      TE_FUNCTION1 | TE_FLAG_PURE, 0},
    {"fac", fac,      TE_FUNCTION1 | TE_FLAG_PURE, 0},
    {"floor", floor,  TE_FUNCTION1 | TE_FLAG_PURE, 0},
    {"ln", log,       TE_FUNCTION1 | TE_FLAG_PURE, 0},
#ifdef TE_NAT_LOG
    {"log", log,      TE_FUNCTION1 | TE_FLAG_PURE, 0},
#else
    {"log", log10,    TE_FUNCTION1 | TE_FLAG_PURE, 0},
#endif
    {"log10", log10,  TE_FUNCTION1 | TE_FLAG_PURE, 0},
    {"ncr", ncr,      TE_FUNCTION2 | TE_FLAG_PURE, 0},
    {"npr", npr,      TE_FUNCTION2 | TE_FLAG_PURE, 0},
    {"pi", pi,        TE_FUNCTION0 | TE_FLAG_PURE, 0},
    {"pow", pow,      TE_FUNCTION2 | TE_FLAG_PURE, 0},
    {"sin", sin,      TE_FUNCTION1 | TE_FLAG_PURE, 0},
    {"sinh", sinh,    TE_FUNCTION1 | TE_FLAG_PURE, 0},
    {"sqrt", sqrt,    TE_FUNCTION1 | TE_FLAG_PURE, 0},
    {"tan", tan,      TE_FUNCTION1 | TE_FLAG_PURE, 0},
    {"tanh", tanh,    TE_FUNCTION1 | TE_FLAG_PURE, 0},
    {0, 0, 0, 0}
};

/**
 * Поиск встроенной функции
 * @param name[in] Имя функции
 * @param len [in] Длина имени
 * @return функция или, если не нашли, то nullptr
 */
static const te_variable *find_builtin(const char *name, int len) {
    int imin = 0;
    /// Индекс последней функции в списке (-2 потому что последняя пустая)
    int imax = sizeof(functions) / sizeof(te_variable) - 2;

    /// Бинарный поиск можем применить поскольку функции отсортированы по имени
    while (imax >= imin) {
        const int i = (imin + ((imax-imin)/2));
        int c = strncmp(name, functions[i].name, len);
        if (!c) c = '\0' - functions[i].name[len];
        if (c == 0) {
            return functions + i;
        } else if (c > 0) {
            imin = i + 1;
        } else {
            imax = i - 1;
        }
    }

    return 0;
}

/**
 * Поиск переменной в строке
 * @param s[in]     Текущее состояние
 * @param name[in]  Указатель на начало имени предполагаемой переменной
 * @param len[in]   Длина имени
 * @return указатель на переменную или, если не нашли, то nullptr
 */
static const te_variable *find_lookup(const state *s, const char *name, int len) {
    /// Итератор по переменным
    int iters;
    /// Найденная переменная
    const te_variable *var;
    /// Проверка на существование переменных
    if (!s->lookup) return 0;

    /// Обход всех переменных (поиск по имени)
    for (var = s->lookup, iters = s->lookup_len; iters; ++var, --iters) {
        if (strncmp(name, var->name, len) == 0 && var->name[len] == '\0') {
            return var;
        }
    }
    return 0;
}



static double add(double a, double b) {return a + b;}
static double sub(double a, double b) {return a - b;}
static double mul(double a, double b) {return a * b;}
static double divide(double a, double b) {return a / b;}
static double negate(double a) {return -a;}
static double comma(double a, double b) {(void)a; return b;}

/**
 * Поиск токена
 * @param s[in,out] Текущее состояние
 */
void next_token(state *s) {
    s->type = TOK_NULL;

    do {
        /// Если мы дошли до конца строки
        if (!*s->next){
            s->type = TOK_END;
            return;
        }

        /// Пытаемся прочитать число
        if ((s->next[0] >= '0' && s->next[0] <= '9') || s->next[0] == '.') {
            /// Запись полученного значения
            s->value = strtod(s->next, (char**)&s->next);
            s->type = TOK_NUMBER;
        } else {
            /// Пытаемся найти переменную или вызов встроенной функции
            if (isalpha(s->next[0])) {
                const char *start;
                start = s->next;

                /// Идем до конца переменной/функции
                while (isalpha(s->next[0]) || isdigit(s->next[0]) || (s->next[0] == '_')) s->next++;

                /// Ищем переменную
                const te_variable *var = find_lookup(s, start, s->next - start);
                /// Если переменную не нашли, то ищем встроенную функцию
                if (!var) {
                    var = find_builtin(start, s->next - start);
                }

                /// Если не нашли то ошибка
                if (!var) {
                    s->type = TOK_ERROR;
                } else {
                    /// Определяем, что мы нашли
                    switch(TYPE_MASK(var->type))
                    {
                        /// Нашли переменную
                        case TE_VARIABLE:
                            s->type = TOK_VARIABLE;
                            s->bound = var->address;
                            break;
                        /// Нашли я пока хз что ?
                        case TE_CLOSURE0: case TE_CLOSURE1: case TE_CLOSURE2: case TE_CLOSURE3:         /* Falls through. */
                        case TE_CLOSURE4: case TE_CLOSURE5: case TE_CLOSURE6: case TE_CLOSURE7:         /* Falls through. */
                            s->context = var->context;                                                  /* Falls through. */

                        /// Нашли функцию
                        case TE_FUNCTION0: case TE_FUNCTION1: case TE_FUNCTION2: case TE_FUNCTION3:     /* Falls through. */
                        case TE_FUNCTION4: case TE_FUNCTION5: case TE_FUNCTION6: case TE_FUNCTION7:     /* Falls through. */
                            s->type = var->type;
                            s->function = var->address;
                            break;
                    }
                }

            } else {
                /// Ищем оператор или специальный символ
                switch (s->next++[0]) {
                    case '+': s->type = TOK_INFIX; s->function = add; break;
                    case '-': s->type = TOK_INFIX; s->function = sub; break;
                    case '*': s->type = TOK_INFIX; s->function = mul; break;
                    case '/': s->type = TOK_INFIX; s->function = divide; break;
                    case '^': s->type = TOK_INFIX; s->function = pow; break;
                    case '%': s->type = TOK_INFIX; s->function = fmod; break;
                    case '(': s->type = TOK_OPEN; break;
                    case ')': s->type = TOK_CLOSE; break;
                    case ',': s->type = TOK_SEP; break;
                    case ' ': case '\t': case '\n': case '\r': break;
                    default: s->type = TOK_ERROR; break;
                }
            }
        }
    } while (s->type == TOK_NULL); /// Все продолжается пока не найдем токен
}


static te_expr *list(state *s);
static te_expr *expr(state *s);
static te_expr *power(state *s);

/**
 * Создание базового выражения
 * @param s[in] Текущее состояние
 * @return Выражение
 */
static te_expr *base(state *s) {
    /* <base>      =    <constant> | <variable> | <function-0> {"(" ")"} | <function-1> <power> | <function-X> "(" <expr> {"," <expr>} ")" | "(" <list> ")" */
    te_expr *ret;
    int arity;

    /// Определяем какой был последний обработанный токен
    switch (TYPE_MASK(s->type)) {
        case TOK_NUMBER:
            ret = new_expr(TE_CONSTANT, 0);
            CHECK_NULL(ret);

            /// Записываем значение
            ret->value = s->value;
            next_token(s);
            break;

        case TOK_VARIABLE:
            ret = new_expr(TE_VARIABLE, 0);
            CHECK_NULL(ret);

            /// Настраиваем связь
            ret->bound = s->bound;
            next_token(s);
            break;

        case TE_FUNCTION0:
        case TE_CLOSURE0:
            ret = new_expr(s->type, 0);
            CHECK_NULL(ret);

            /// Задаем функциональную часть
            ret->function = s->function;
            /// ?
            if (IS_CLOSURE(s->type)) ret->parameters[0] = s->context;
            /// Идем дальше
            next_token(s);
            /// Если нашли открывающую скобку
            if (s->type == TOK_OPEN) {
                next_token(s);
                /// Поскольку функция с 0 параметров следом должна стоять закрывающая скобка "foo()"
                if (s->type != TOK_CLOSE) {
                    s->type = TOK_ERROR;
                } else {
                    next_token(s);
                }
            }
            break;

        case TE_FUNCTION1:
        case TE_CLOSURE1:
            ret = new_expr(s->type, 0);
            CHECK_NULL(ret);

            ret->function = s->function;
            if (IS_CLOSURE(s->type)) ret->parameters[1] = s->context;
            next_token(s);
            ret->parameters[0] = power(s);
            /// Если параметры nullptr, то чистим
            CHECK_NULL(ret->parameters[0], te_free(ret));
            break;

        case TE_FUNCTION2: case TE_FUNCTION3: case TE_FUNCTION4:
        case TE_FUNCTION5: case TE_FUNCTION6: case TE_FUNCTION7:
        case TE_CLOSURE2: case TE_CLOSURE3: case TE_CLOSURE4:
        case TE_CLOSURE5: case TE_CLOSURE6: case TE_CLOSURE7:
            /// Узнаем количество параметров
            arity = ARITY(s->type);

            ret = new_expr(s->type, 0);
            CHECK_NULL(ret);

            ret->function = s->function;
            if (IS_CLOSURE(s->type)) ret->parameters[arity] = s->context;
            next_token(s);

            /// Функция всегда начинается со скобки
            if (s->type != TOK_OPEN) {
                s->type = TOK_ERROR;
            } else {
                int i;
                for(i = 0; i < arity; i++) {
                    next_token(s);
                    /// Задаем параметры
                    ret->parameters[i] = expr(s);
                    CHECK_NULL(ret->parameters[i], te_free(ret));

                    /// Дошли до конца, все параметры заданы
                    if(s->type != TOK_SEP) {
                        break;
                    }
                }
                /// Указано неправильное количество параметров или не стоит закрывающая скобка
                if(s->type != TOK_CLOSE || i != arity - 1) {
                    s->type = TOK_ERROR;
                } else {
                    next_token(s);
                }
            }

            break;

        case TOK_OPEN:
            next_token(s);
            /// Формируем список
            ret = list(s);
            CHECK_NULL(ret);

            /// Список должен закрываться скобкой
            if (s->type != TOK_CLOSE) {
                s->type = TOK_ERROR;
            } else {
                next_token(s);
            }
            break;

        default:
            /// Допущена ошибка
            ret = new_expr(0, 0);
            CHECK_NULL(ret);

            s->type = TOK_ERROR;
            ret->value = NAN;
            break;
    }

    return ret;
}

/**
 * Раскручивание базовой операции (функция, значение и тп)
 * @param s[in] Текущее состояние
 * @return
 */
static te_expr *power(state *s) {
    /* <power>     =    {("-" | "+")} <base> */
    /// ?
    int sign = 1;
    /// Пока символы "-" | "+" идем до следующего токена
    while (s->type == TOK_INFIX && (s->function == add || s->function == sub)) {
        if (s->function == sub) sign = -sign;
        next_token(s);
    }

    te_expr *ret;

    /// Если перед выражением не стояло минуса или они компенсировали друг друга
    if (sign == 1) {
        ret = base(s);
    } else {
        te_expr *b = base(s);
        CHECK_NULL(b);

        /// Оборачиваем в функцию отрицания
        ret = NEW_EXPR(TE_FUNCTION1 | TE_FLAG_PURE, b);
        CHECK_NULL(ret, te_free(b));

        ret->function = negate;
    }

    return ret;
}

#ifdef TE_POW_FROM_RIGHT
static te_expr *factor(state *s) {
    /* <factor>    =    <power> {"^" <power>} */
    te_expr *ret = power(s);
    CHECK_NULL(ret);

    int neg = 0;

    if (ret->type == (TE_FUNCTION1 | TE_FLAG_PURE) && ret->function == negate) {
        te_expr *se = ret->parameters[0];
        free(ret);
        ret = se;
        neg = 1;
    }

    te_expr *insertion = 0;

    while (s->type == TOK_INFIX && (s->function == pow)) {
        te_fun2 t = s->function;
        next_token(s);

        if (insertion) {
            /* Make exponentiation go right-to-left. */
            te_expr *p = power(s);
            CHECK_NULL(p, te_free(ret));

            te_expr *insert = NEW_EXPR(TE_FUNCTION2 | TE_FLAG_PURE, insertion->parameters[1], p);
            CHECK_NULL(insert, te_free(p), te_free(ret));

            insert->function = t;
            insertion->parameters[1] = insert;
            insertion = insert;
        } else {
            te_expr *p = power(s);
            CHECK_NULL(p, te_free(ret));

            te_expr *prev = ret;
            ret = NEW_EXPR(TE_FUNCTION2 | TE_FLAG_PURE, ret, p);
            CHECK_NULL(ret, te_free(p), te_free(prev));

            ret->function = t;
            insertion = ret;
        }
    }

    if (neg) {
        te_expr *prev = ret;
        ret = NEW_EXPR(TE_FUNCTION1 | TE_FLAG_PURE, ret);
        CHECK_NULL(ret, te_free(prev));

        ret->function = negate;
    }

    return ret;
}
#else
/**
 * Раскручивание операции возведения в степень
 * @param s[in] Текущее состояние
 * @return
 */
static te_expr *factor(state *s) {
    /* <factor>    =    <power> {"^" <power>} */
    te_expr *ret = power(s);
    CHECK_NULL(ret);

    /// Идем пока идут знаки возведения в степень
    while (s->type == TOK_INFIX && (s->function == pow)) {
        /// Сохраняем функцию
        te_fun2 t = s->function;
        next_token(s);
        /// Находим в какую степень мы будем возводить
        te_expr *p = power(s);
        CHECK_NULL(p, te_free(ret));

        te_expr *prev = ret;
        /// Назначаем, что это функция двух параметров "pow(ret, p)"
        ret = NEW_EXPR(TE_FUNCTION2 | TE_FLAG_PURE, ret, p);
        CHECK_NULL(ret, te_free(p), te_free(prev));

        ret->function = t;
    }

    return ret;
}
#endif


/**
 * Раскручивание операций с умножением/делением/нахождением остатка
 * @param s[in] Текущее состояние
 * @return
 */
static te_expr *term(state *s) {
    /* <term>      =    <factor> {("*" | "/" | "%") <factor>} */
    /// Находим то, что будем умножать/делить/находить остаток
    te_expr *ret = factor(s);
    CHECK_NULL(ret);

    /// Пока идут последовательно эти функции
    while (s->type == TOK_INFIX && (s->function == mul || s->function == divide || s->function == fmod)) {
        /// Сохраняем функцию
        te_fun2 t = s->function;
        next_token(s);

        /// Находим второй операнд
        te_expr *f = factor(s);
        CHECK_NULL(f, te_free(ret));

        te_expr *prev = ret;
        /// Назначаем нужную функцию "ret "*" | "/" | "%" f"
        ret = NEW_EXPR(TE_FUNCTION2 | TE_FLAG_PURE, ret, f);
        CHECK_NULL(ret, te_free(f), te_free(prev));

        ret->function = t;
    }

    return ret;
}

/**
 * Раскручивание операций сложения/вычитания
 * @param s[in] Текущее состояние
 * @return
 */
static te_expr *expr(state *s) {
    /* <expr>      =    <term> {("+" | "-") <term>} */
    /// Находим первый операнд для сложения/вычитания
    te_expr *ret = term(s);
    CHECK_NULL(ret);

    while (s->type == TOK_INFIX && (s->function == add || s->function == sub)) {
        /// Сохраняем функцию
        te_fun2 t = s->function;
        next_token(s);
        /// Находим второй операнд для сложения/вычитания
        te_expr *te = term(s);
        CHECK_NULL(te, te_free(ret));

        te_expr *prev = ret;
        /// Назначаем нужную функцию "ret "+" | "-" te"
        ret = NEW_EXPR(TE_FUNCTION2 | TE_FLAG_PURE, ret, te);
        CHECK_NULL(ret, te_free(te), te_free(prev));

        ret->function = t;
    }

    return ret;
}

/**
 * Раскручивание списка
 * @param s[in] Текущее состояние
 * @return
 */
static te_expr *list(state *s) {
    /* <list>      =    <expr> {"," <expr>} */
    /// Находим первый операнд для списка
    te_expr *ret = expr(s);
    CHECK_NULL(ret);

    while (s->type == TOK_SEP) {
        next_token(s);
        /// Находим второй операнд для списка
        te_expr *e = expr(s);
        CHECK_NULL(e, te_free(ret));

        te_expr *prev = ret;
        /// Назначаем нужную функцию "ret, e"
        ret = NEW_EXPR(TE_FUNCTION2 | TE_FLAG_PURE, ret, e);
        CHECK_NULL(ret, te_free(e), te_free(prev));

        ret->function = comma;
    }

    return ret;
}


#define TE_FUN(...) ((double(*)(__VA_ARGS__))n->function)
#define M(e) te_eval(n->parameters[e])

/**
 * Вычисление значения выражения, но только если все ее параметры простые
 * @param n[in] Выражение которое необходимо вычислить
 * @return Значение выражения
 */
double te_eval(const te_expr *n) {
    if (!n) return NAN;

    switch(TYPE_MASK(n->type)) {
        case TE_CONSTANT: return n->value;
        case TE_VARIABLE: return *n->bound;

        case TE_FUNCTION0: case TE_FUNCTION1: case TE_FUNCTION2: case TE_FUNCTION3:
        case TE_FUNCTION4: case TE_FUNCTION5: case TE_FUNCTION6: case TE_FUNCTION7:
            switch(ARITY(n->type)) {
                case 0: return TE_FUN(void)();
                case 1: return TE_FUN(double)(M(0));
                case 2: return TE_FUN(double, double)(M(0), M(1));
                case 3: return TE_FUN(double, double, double)(M(0), M(1), M(2));
                case 4: return TE_FUN(double, double, double, double)(M(0), M(1), M(2), M(3));
                case 5: return TE_FUN(double, double, double, double, double)(M(0), M(1), M(2), M(3), M(4));
                case 6: return TE_FUN(double, double, double, double, double, double)(M(0), M(1), M(2), M(3), M(4), M(5));
                case 7: return TE_FUN(double, double, double, double, double, double, double)(M(0), M(1), M(2), M(3), M(4), M(5), M(6));
                default: return NAN;
            }

        case TE_CLOSURE0: case TE_CLOSURE1: case TE_CLOSURE2: case TE_CLOSURE3:
        case TE_CLOSURE4: case TE_CLOSURE5: case TE_CLOSURE6: case TE_CLOSURE7:
            switch(ARITY(n->type)) {
                case 0: return TE_FUN(void*)(n->parameters[0]);
                case 1: return TE_FUN(void*, double)(n->parameters[1], M(0));
                case 2: return TE_FUN(void*, double, double)(n->parameters[2], M(0), M(1));
                case 3: return TE_FUN(void*, double, double, double)(n->parameters[3], M(0), M(1), M(2));
                case 4: return TE_FUN(void*, double, double, double, double)(n->parameters[4], M(0), M(1), M(2), M(3));
                case 5: return TE_FUN(void*, double, double, double, double, double)(n->parameters[5], M(0), M(1), M(2), M(3), M(4));
                case 6: return TE_FUN(void*, double, double, double, double, double, double)(n->parameters[6], M(0), M(1), M(2), M(3), M(4), M(5));
                case 7: return TE_FUN(void*, double, double, double, double, double, double, double)(n->parameters[7], M(0), M(1), M(2), M(3), M(4), M(5), M(6));
                default: return NAN;
            }

        default: return NAN;
    }

}

#undef TE_FUN
#undef M

/**
 *
 * @param n
 */
static void optimize(te_expr *n) {
    /// Если у нас выражение состоит только из значения то можно не упрощать
    if (n->type == TE_CONSTANT) return;
    if (n->type == TE_VARIABLE) return;

    /// Оптимизируем только функции, отмеченные как "чистые"
    if (IS_PURE(n->type)) {
        /// Находим количество параметров функции
        const int arity = ARITY(n->type);

        /**
         * Если все параметры известны (то есть их значения - константы),
         * то переменная known устанавливается в значение 1,
         * а если хотя бы один из параметров не является константой,
         * то known устанавливается в значение 0.
         *
         * Таким образом, переменная known используется для определения того,
         * можно ли оптимизировать функцию n, используя известные значения ее параметров.
         */
        int known = 1;
        int i;
        /// Проходим по всем параметрам и оптимизируем их
        for (i = 0; i < arity; ++i) {
            optimize(n->parameters[i]);
            if (((te_expr*)(n->parameters[i]))->type != TE_CONSTANT) {
                known = 0;
            }
        }
        if (known) {
            /// Вычисляем значение простого выражения
            const double value = te_eval(n);
            /// Параметры больше не нужны, чистим их
            te_free_parameters(n);
            n->type = TE_CONSTANT;
            n->value = value;
        }
    }
}

/**
 *  Компиляция выражения
 * @param expression[in] Выражение в виде строки
 * @param variables[in]  Переменные
 * @param var_count[in]  Количество переменных
 * @param error[out]     Ошибка
 * @return
 */
te_expr *te_compile(const char *expression, const te_variable *variables, int var_count, int *error) {
    /// Текущее состояние
    state s;
    s.start = s.next = expression;
    s.lookup = variables;
    s.lookup_len = var_count;

    /// Поиск токена
    next_token(&s);
    /// Находим корень дерева выражений
    te_expr *root = list(&s);
    /// Если что-то не получилось создать, то ошибка
    if (root == NULL) {
        if (error) *error = -1;
        return NULL;
    }

    /// Если не дошли до конца, то ошибка
    if (s.type != TOK_END) {
        te_free(root);
        if (error) {
            *error = (s.next - s.start);
            if (*error == 0) *error = 1;
        }
        return 0;
    } else {
        /// Оптимизируем выражение если это можно сделать
        optimize(root);
        if (error) *error = 0;
        return root;
    }
}

/**
 * Вычисление простого выражения без пользовательских переменных
 * @param expression[in] Выражение в виде строки
 * @param error[out]     Ошибка
 * @return
 */
double te_interp(const char *expression, int *error) {
    /// Компилируем простое выражение не имеющее переменных
    te_expr *n = te_compile(expression, 0, 0, error);
    if (n == NULL) {
        return NAN;
    }

    double ret;
    if (n) {
        /// Вычисляем значение всего выражения
        ret = te_eval(n);
        /// Чистим за собой всю память
        te_free(n);
    } else {
        ret = NAN;
    }
    return ret;
}

/**
 * Вывод поддерева выражения
 * @param n[in]     Выражение
 * @param depth[in] Глубина поддерева
 */
static void pn (const te_expr *n, int depth) {
    int i, arity;
    /// Смещаемся
    printf("%*s", depth, "");

    switch(TYPE_MASK(n->type)) {
    case TE_CONSTANT: printf("%f\n", n->value); break;
    case TE_VARIABLE: printf("bound %p\n", n->bound); break;

    case TE_FUNCTION0: case TE_FUNCTION1: case TE_FUNCTION2: case TE_FUNCTION3:
    case TE_FUNCTION4: case TE_FUNCTION5: case TE_FUNCTION6: case TE_FUNCTION7:
    case TE_CLOSURE0: case TE_CLOSURE1: case TE_CLOSURE2: case TE_CLOSURE3:
    case TE_CLOSURE4: case TE_CLOSURE5: case TE_CLOSURE6: case TE_CLOSURE7:
         arity = ARITY(n->type);
         printf("f%d", arity);
         for(i = 0; i < arity; i++) {
             printf(" %p", n->parameters[i]);
         }
         printf("\n");
         for(i = 0; i < arity; i++) {
             pn(n->parameters[i], depth + 1);
         }
         break;
    }
}

/**
 * Вывод всего дерева
 * @param n[in] Выражение
 */
void te_print(const te_expr *n) {
    pn(n, 0);
}
