/*
;; TExp AST
;; ========
;; Type checking language
;; Syntax with optional type annotations for var declarations and function return types.

;; Type language
;; <texp>         ::= <atomic-te> | <compound-te> | <tvar>
;; <atomic-te>    ::= <num-te> | <bool-te> | <void-te>
;; <num-te>       ::= number   // num-te()
;; <bool-te>      ::= boolean  // bool-te()
;; <str-te>       ::= string   // str-te()
;; <void-te>      ::= void     // void-te()
;; <compound-te>  ::= <proc-te> | <tuple-te>
;; <non-tuple-te> ::= <atomic-te> | <proc-te> | <tvar>
;; <proc-te>      ::= [ <tuple-te> -> <non-tuple-te> ] // proc-te(param-tes: list(te), return-te: te)
;; <tuple-te>     ::= <non-empty-tuple-te> | <empty-te>
;; <non-empty-tuple-te> ::= ( <non-tuple-te> *)* <non-tuple-te> // tuple-te(tes: list(te))
;; <empty-te>     ::= Empty
;; <tvar>         ::= a symbol starting with T // tvar(id: Symbol, contents; Box(string|boolean))

;; Examples of type expressions
;; number
;; boolean
;; void
;; [number -> boolean]
;; [number * number -> boolean]
;; [number -> [number -> boolean]]
;; [Empty -> number]
;; [Empty -> void]
*/
import { chain, concat, equals, map, uniq } from "ramda";
import { Sexp } from "s-expression";
import { isEmpty, isNonEmptyList } from "../shared/list";
import { isArray, isBoolean, isString } from '../shared/type-predicates';
import { makeBox, setBox, unbox, Box } from '../shared/box';
import { cons, first, rest } from '../shared/list';
import { Result, bind, makeOk, makeFailure, mapResult, mapv, zipWithResult} from "../shared/result";
import { parse as p } from "../shared/parser";
import { format } from "../shared/format";

export type TExp =  AtomicTExp | CompoundTExp | TVar;
export const isTExp = (x: any): x is TExp => isAtomicTExp(x) || isCompoundTExp(x) || isTVar(x);
export type Subst = { [varName: string]: TExp };

export type AtomicTExp = NumTExp | BoolTExp | StrTExp | VoidTExp | LiteralTExp;
export const isAtomicTExp = (x: any): x is AtomicTExp =>
    isNumTExp(x) || isBoolTExp(x) || isStrTExp(x) || isVoidTExp(x) || isLiteralTExp(x);

export type LiteralTExp = { tag: "LiteralTExp" }; 
export const makeLiteralTExp = (): LiteralTExp => ({ tag: "LiteralTExp" });
export const isLiteralTExp = (x: any): x is LiteralTExp => x.tag === "LiteralTExp";

export type CompoundTExp = ProcTExp | TupleTExp | PairTExp;
export const isCompoundTExp = (x: any): x is CompoundTExp => isProcTExp(x) || isTupleTExp(x) || isPairTExp(x);

export type NonTupleTExp = AtomicTExp | ProcTExp | TVar;
export const isNonTupleTExp = (x: any): x is NonTupleTExp =>
    isAtomicTExp(x) || isProcTExp(x) || isTVar(x);

export type PairTExp = { tag: "PairTExp"; left: TExp; right: TExp; };
export const makePairTExp = (left: TExp, right: TExp): PairTExp =>
    ({tag: "PairTExp", left: left, right: right});
export const isPairTExp = (x: any): x is PairTExp => x.tag === "PairTExp";

export type NumTExp = { tag: "NumTExp" };
export const makeNumTExp = (): NumTExp => ({tag: "NumTExp"});
export const isNumTExp = (x: any): x is NumTExp => x.tag === "NumTExp";

export type BoolTExp = { tag: "BoolTExp" };
export const makeBoolTExp = (): BoolTExp => ({tag: "BoolTExp"});
export const isBoolTExp = (x: any): x is BoolTExp => x.tag === "BoolTExp";

export type StrTExp = { tag: "StrTExp" };
export const makeStrTExp = (): StrTExp => ({tag: "StrTExp"});
export const isStrTExp = (x: any): x is StrTExp => x.tag === "StrTExp";

export type VoidTExp = { tag: "VoidTExp" };
export const makeVoidTExp = (): VoidTExp => ({tag: "VoidTExp"});
export const isVoidTExp = (x: any): x is VoidTExp => x.tag === "VoidTExp";

// proc-te(param-tes: list(te), return-te: te)
export type ProcTExp = { tag: "ProcTExp"; paramTEs: TExp[]; returnTE: TExp; };
export const makeProcTExp = (paramTEs: TExp[], returnTE: TExp): ProcTExp =>
    ({tag: "ProcTExp", paramTEs: paramTEs, returnTE: returnTE});
export const isProcTExp = (x: any): x is ProcTExp => x.tag === "ProcTExp";
// Uniform access to all components of a ProcTExp
export const procTExpComponents = (pt: ProcTExp): TExp[] =>
    [...pt.paramTEs, pt.returnTE];

export type TupleTExp = NonEmptyTupleTExp | EmptyTupleTExp;
export const isTupleTExp = (x: any): x is TupleTExp =>
    isNonEmptyTupleTExp(x) || isEmptyTupleTExp(x);

export type EmptyTupleTExp = { tag: "EmptyTupleTExp" }
export const makeEmptyTupleTExp = (): EmptyTupleTExp => ({tag: "EmptyTupleTExp"});
export const isEmptyTupleTExp = (x: any): x is EmptyTupleTExp => x.tag === "EmptyTupleTExp";

// NonEmptyTupleTExp(TEs: NonTupleTExp[])
export type NonEmptyTupleTExp = { tag: "NonEmptyTupleTExp"; TEs: NonTupleTExp[]; }
export const makeNonEmptyTupleTExp = (tes: NonTupleTExp[]): NonEmptyTupleTExp =>
    ({tag: "NonEmptyTupleTExp", TEs: tes});
export const isNonEmptyTupleTExp = (x: any): x is NonEmptyTupleTExp => x.tag === "NonEmptyTupleTExp";

// TVar: Type Variable with support for dereferencing (TVar -> TVar)
export type TVar = { tag: "TVar"; var: string; contents: Box<undefined | TExp>; };
export const isEmptyTVar = (x: any): x is TVar =>
    (x.tag === "TVar") && unbox(x.contents) === undefined;
export const makeTVar = (v: string): TVar =>
    ({tag: "TVar", var: v, contents: makeBox(undefined)});
const makeTVarGen = (): () => TVar => {
    let count: number = 0;
    return () => {
        count++;
        return makeTVar(`T_${count}`);
    }
}
export const makeFreshTVar = makeTVarGen();
export const isTVar = (x: any): x is TVar => x.tag === "TVar";
export const eqTVar = (tv1: TVar, tv2: TVar): boolean => tv1.var === tv2.var;
export const tvarContents = (tv: TVar): undefined | TExp => unbox(tv.contents);
export const tvarSetContents = (tv: TVar, val: TExp): void =>
    setBox(tv.contents, val);
export const tvarIsNonEmpty = (tv: TVar): boolean => tvarContents(tv) !== undefined;
export const tvarDeref = (te: TExp): TExp => {
    if (! isTVar(te)) return te;
    const contents = tvarContents(te);
    if (contents === undefined)
        return te;
    else if (isTVar(contents))
        return tvarDeref(contents);
    else
        return contents;
}

// ========================================================
// TExp Utilities

// Purpose: uniform access to atomic types
export const atomicTExpName = (te: AtomicTExp): string => te.tag;

export const eqAtomicTExp = (te1: AtomicTExp, te2: AtomicTExp): boolean =>
    atomicTExpName(te1) === atomicTExpName(te2);


// ========================================================
// TExp parser

export const parseTE = (t: string): Result<TExp> =>
    bind(p(t), parseTExp);

/*
;; Purpose: Parse a type expression
;; Type: [SExp -> TExp[]]
;; Example:
;; parseTExp("number") => 'num-te
;; parseTExp('boolean') => 'bool-te
;; parseTExp('T1') => '(tvar T1)
;; parseTExp('(T * T -> boolean)') => '(proc-te ((tvar T) (tvar T)) bool-te)
;; parseTExp('(number -> (number -> number)') => '(proc-te (num-te) (proc-te (num-te) num-te))
*/
export const parseTExp = (texp: Sexp): Result<TExp> =>
    (texp === "number") ? makeOk(makeNumTExp()) :
    (texp === "boolean") ? makeOk(makeBoolTExp()) :
    (texp === "void") ? makeOk(makeVoidTExp()) :
    (texp === "string") ? makeOk(makeStrTExp()) :
    isString(texp) ? makeOk(makeTVar(texp)) :
    isArray(texp) ? parseCompoundTExp(texp) :
    makeFailure(`Unexpected TExp - ${format(texp)}`);

/*
;; expected structure: (<params> -> <returnte>)
;; expected exactly one -> in the list
;; We do not accept (a -> b -> c) - must parenthesize
*/
const parseCompoundTExp = (texps: Sexp[]): Result<CompoundTExp> => {
    if (texps.length === 0)
        return makeFailure(`Empty type expression - ${format(texps)}`);

    const pos = texps.indexOf('->');//ProcTExp
    if (pos !== -1) {
        return (pos === 0) ? makeFailure(`No param types in proc texp - ${format(texps)}`) :
           (pos === texps.length - 1) ? makeFailure(`No return type in proc texp - ${format(texps)}`) :
           (texps.slice(pos + 1).indexOf('->') > -1) ? makeFailure(`Only one -> allowed in a procexp - ${format(texps)}`) :
           bind(parseTupleTExp(texps.slice(0, pos)), (args: TExp[]) =>
               mapv(parseTExp(texps[pos + 1]), (returnTE: TExp) =>
                    makeProcTExp(args, returnTE)));
    }

    const head = texps[0];//PairTExp
    if( isString(head) && head === 'Pair') {
        return (texps.length !== 3) ?
            makeFailure(`Pair type expression must have exactly 2 elements - ${format(texps)}`) :
            bind(parseTExp(texps[1]), (left: TExp) =>
                mapv(parseTExp(texps[2]), (right: TExp) =>
                    makePairTExp(left, right)));
    }

    // TupleTExp
    return bind(parseTupleTExp(texps), (tes: TExp[]) =>{
        if (isEmpty(tes)) {
            return makeOk(makeEmptyTupleTExp());
        }
        const NonTupleTExps: NonTupleTExp[] = [];
        for (const element of tes) {
            if (!isNonTupleTExp(element)) {
                return makeFailure(`Tuple type expression must contain only non-tuple types - ${format(texps)}`);
            }
            else{
                NonTupleTExps.push(element);
            }
        }
        return makeOk(makeNonEmptyTupleTExp(NonTupleTExps));
    });

    
};


/*
;; Expected structure: <te1> [* <te2> ... * <ten>]?
;; Or: Empty
*/
const parseTupleTExp = (texps: Sexp[]): Result<TExp[]> => {
    const isEmptyTuple = (texps: Sexp[]): boolean =>
        (texps.length === 1) && (texps[0] === 'Empty');
    // [x1 * x2 * ... * xn] => [x1,...,xn]
    const splitEvenOdds = (texps: Sexp[]): Result<Sexp[]> =>
        isEmpty(texps) ? makeOk([]) :
        (texps.length === 1) ? makeOk(texps) :
        texps[1] !== '*' ? makeFailure(`Parameters of procedure type must be separated by '*': ${format(texps)}`) :
        mapv(splitEvenOdds(texps.slice(2)), (sexps: Sexp[]) => [texps[0], ...sexps]);

    return isEmptyTuple(texps) ? makeOk([]) : bind(splitEvenOdds(texps), (argTEs: Sexp[]) => 
                                                    mapResult(parseTExp, argTEs));
}

/*
;; Purpose: Unparse a type expression Texp into its concrete form
*/
export const unparseTExp = (te: TExp): Result<string> => {
    const unparseTuple = (paramTes: TExp[]): Result<string[]> =>
        isNonEmptyList<TExp>(paramTes) ? bind(unparseTExp(first(paramTes)), (paramTE: string) =>
            mapv(mapResult(unparseTExp, rest(paramTes)), (paramTEs: string[]) =>
                cons(paramTE, chain(te => ['*', te], paramTEs)))) :
        makeOk(["Empty"]);

    const up = (x?: TExp): Result<string | string[]> =>
        isNumTExp(x) ? makeOk('number') :
        isBoolTExp(x) ? makeOk('boolean') :
        isStrTExp(x) ? makeOk('string') :
        isVoidTExp(x) ? makeOk('void') :
        isLiteralTExp(x) ? makeOk('literal') :
        isEmptyTVar(x) ? makeOk(x.var) :
        isTVar(x) ? up(tvarContents(x)) :
        isProcTExp(x) ? bind(unparseTuple(x.paramTEs), (paramTEs: string[]) =>
                            mapv(unparseTExp(x.returnTE), (returnTE: string) =>
                                [...paramTEs, '->', returnTE])) :
        isPairTExp(x) ? bind(unparseTExp(x.left), (left: string) =>
                            mapv(unparseTExp(x.right), (right: string) =>
                                `(${['Pair', left, right].join(' ')})`)) :
        isEmptyTupleTExp(x) ? makeOk("Empty") :
        isNonEmptyTupleTExp(x) ? unparseTuple(x.TEs) :
        x === undefined ? makeFailure("Undefined TVar") :
        makeFailure(`Unexpected type expression in unparseTExp: ${JSON.stringify(x)}`);

    const unparsed = up(te);
    return mapv(unparsed,
                (x: string | string[]) => isString(x) ? x :
                                          isArray(x) ? `(${x.join(' ')})` :
                                          x);
}

// ============================================================
// equivalentTEs: 2 TEs are equivalent up to variable renaming.
// For example:
// equivalentTEs(parseTExp('(T1 -> T2)'), parseTExp('(T3 -> T4)'))


// Signature: matchTVarsInTE(te1, te2, succ, fail)
// Type: [Texp * Texp * [List(Pair(Tvar, Tvar)) -> T1] * [Empty -> T2]] |
//       [List(Texp) * List(Texp) * ...]
// Purpose:   Receives two type expressions or list(texps) plus continuation procedures
//            and, in case they are equivalent, pass a mapping between
//            type variable they include to succ. Otherwise, invoke fail.
// Examples:
// matchTVarsInTE(parseTExp('(Number * T1 -> T1)',
//                parseTExp('(Number * T7 -> T5)'),
//                (x) => x,
//                () => false) ==> [[T1, T7], [T1, T5]]
// matchTVarsInTE(parseTExp('(Boolean * T1 -> T1)'),
//                parseTExp('(Number * T7 -> T5)'),
//                (x) => x,
//                () => false)) ==> false

type Pair<T1, T2> = {left: T1; right: T2};

const matchTVarsInTE = <T1, T2>(te1: TExp, te2: TExp,
                                succ: (mapping: Array<Pair<TVar, TVar>>) => T1,
                                fail: () => T2): T1 | T2 =>
    (isTVar(te1) || isTVar(te2)) ? matchTVarsinTVars(tvarDeref(te1), tvarDeref(te2), succ, fail) :
    (isAtomicTExp(te1) || isAtomicTExp(te2)) ?
        ((isAtomicTExp(te1) && isAtomicTExp(te2) && eqAtomicTExp(te1, te2)) ? succ([]) : fail()) :
    matchTVarsInTProcs(te1, te2, succ, fail);

// te1 and te2 are the result of tvarDeref
const matchTVarsinTVars = <T1, T2>(te1: TExp, te2: TExp,
                                    succ: (mapping: Array<Pair<TVar, TVar>>) => T1,
                                    fail: () => T2): T1 | T2 =>
    (isTVar(te1) && isTVar(te2)) ? (eqTVar(te1, te2) ? succ([]) : succ([{left: te1, right: te2}])) :
    (isTVar(te1) || isTVar(te2)) ? fail() :
    matchTVarsInTE(te1, te2, succ, fail);

const matchTVarsInTProcs = <T1, T2>(te1: TExp, te2: TExp,
        succ: (mapping: Array<Pair<TVar, TVar>>) => T1,
        fail: () => T2): T1 | T2 =>
    (isProcTExp(te1) && isProcTExp(te2)) ? matchTVarsInTEs(procTExpComponents(te1), procTExpComponents(te2), succ, fail) :
    fail();

const matchTVarsInTEs = <T1, T2>(te1: TExp[], te2: TExp[],
                                    succ: (mapping: Array<Pair<TVar, TVar>>) => T1,
                                    fail: () => T2): T1 | T2 =>
    // Match first then continue on rest
    isNonEmptyList<TExp>(te1) && isNonEmptyList<TExp>(te2) ?
        matchTVarsInTE(first(te1), first(te2),
                        (subFirst) => matchTVarsInTEs(rest(te1), rest(te2), 
                                        (subRest) => succ(concat(subFirst, subRest)), 
                                        fail),
                        fail) :
    (isEmpty(te1) && isEmpty(te2)) ? succ([]) :
    fail();

// Signature: equivalent-tes?(te1, te2)
// Purpose:   Check whether 2 type expressions are equivalent up to
//            type variable renaming.
// Example:  equivalentTEs(parseTExp('(T1 * (Number -> T2) -> T3))',
//                         parseTExp('(T4 * (Number -> T5) -> T6))') => #t
export const equivalentTEs = (te1: TExp, te2: TExp): boolean => {
    // console.log(`EqTEs ${format(te1)} - ${format(te2)}`);
    const tvarsPairs = matchTVarsInTE(te1, te2, (x) => x, () => false);
    // console.log(`EqTEs pairs = ${map(JSON.stringify, tvarsPairs)}`)
    if (isBoolean(tvarsPairs))
        return false;
    else {
        return (uniq(map((p) => p.left.var, tvarsPairs)).length === uniq(map((p) => p.right.var, tvarsPairs)).length);
    }
};

const occursIn = (v: string, t: TExp): boolean => {
    const derefedT = tvarDeref(t);
    if (isTVar(derefedT)) {
        return v === derefedT.var;
    } else if (isProcTExp(derefedT)) {
        return occursIn(v, derefedT.returnTE) || derefedT.paramTEs.some(param => occursIn(v, param));
    } else if (isPairTExp(derefedT)) {
        return occursIn(v, derefedT.left) || occursIn(v, derefedT.right);
    } else if (isNonEmptyTupleTExp(derefedT)) {
        return derefedT.TEs.some(te => occursIn(v, te));
    }
    return false;
};

export const unify = (te1: TExp, te2: TExp): Result<true> => {
    const derefedTe1 = tvarDeref(te1);
    const derefedTe2 = tvarDeref(te2);

    if (equals(derefedTe1, derefedTe2)) {
        return makeOk(true);
    }
    else if (isTVar(derefedTe1)) {
        if (occursIn(derefedTe1.var, derefedTe2)) {
            return makeFailure(`Occurs check failed: ${derefedTe1.var} occurs in ${unparseTExp(derefedTe2)}`);
        }
        tvarSetContents(derefedTe1, derefedTe2);
        return makeOk(true);
    }
    else if (isTVar(derefedTe2)) {
        if (occursIn(derefedTe2.var, derefedTe1)) {
            return makeFailure(`Occurs check failed: ${derefedTe2.var} occurs in ${unparseTExp(derefedTe1)}`);
        }
        tvarSetContents(derefedTe2, derefedTe1);
        return makeOk(true);
    }
    else if (isAtomicTExp(derefedTe1) && isAtomicTExp(derefedTe2)) {
        return eqAtomicTExp(derefedTe1, derefedTe2) ? makeOk(true) :
            makeFailure(`Type mismatch: ${unparseTExp(te1)} and ${unparseTExp(te2)}`);
    }
    else if (isProcTExp(derefedTe1) && isProcTExp(derefedTe2)) {
        if (derefedTe1.paramTEs.length !== derefedTe2.paramTEs.length) {
            return makeFailure(`Procedure parameter count mismatch: ${unparseTExp(te1)} and ${unparseTExp(te2)}`);
        }
        const paramUnificationResults = zipWithResult(unify, derefedTe1.paramTEs, derefedTe2.paramTEs);
        const returnUnificationResult = unify(derefedTe1.returnTE, derefedTe2.returnTE);

        return bind(paramUnificationResults, _ =>
            bind(returnUnificationResult, _ => makeOk(true)));
    }
    else if (isPairTExp(derefedTe1) && isPairTExp(derefedTe2)) {
        const leftUnification = unify(derefedTe1.left, derefedTe2.left);
        const rightUnification = unify(derefedTe1.right, derefedTe2.right);
        return bind(leftUnification, _ => bind(rightUnification, _ => makeOk(true)));
    }
    else if (isTupleTExp(derefedTe1) && isTupleTExp(derefedTe2)) {
        if (isEmptyTupleTExp(derefedTe1) && isEmptyTupleTExp(derefedTe2)) {
            return makeOk(true);
        }
        if (isNonEmptyTupleTExp(derefedTe1) && isNonEmptyTupleTExp(derefedTe2)) {
            if (derefedTe1.TEs.length !== derefedTe2.TEs.length) {
                return makeFailure(`Tuple length mismatch: ${unparseTExp(te1)} and ${unparseTExp(te2)}`);
            }
            return bind(zipWithResult(unify, derefedTe1.TEs, derefedTe2.TEs), _ => makeOk(true));
        }
        return makeFailure(`Tuple type mismatch: ${unparseTExp(te1)} and ${unparseTExp(te2)}`);
    }
    else {
        return makeFailure(`Type mismatch: cannot unify ${unparseTExp(te1)} and ${unparseTExp(te2)}`);
    }
};

export const makeFreshTExp = (te: TExp): TExp => {
    const newVars: Map<string, TVar> = new Map();

    const freshRec = (currentTe: TExp): TExp => {
        const derefedTe = tvarDeref(currentTe);

        if (isTVar(derefedTe)) {
            if (newVars.has(derefedTe.var)) {
                return newVars.get(derefedTe.var)!;
            } else {
                const freshVar = makeFreshTVar();
                newVars.set(derefedTe.var, freshVar);
                return freshVar;
            }
        } else if (isProcTExp(derefedTe)) {
            return makeProcTExp(derefedTe.paramTEs.map(freshRec), freshRec(derefedTe.returnTE));
        } else if (isPairTExp(derefedTe)) {
            return makePairTExp(freshRec(derefedTe.left), freshRec(derefedTe.right));
        } else if (isNonEmptyTupleTExp(derefedTe)) {
            return makeNonEmptyTupleTExp(derefedTe.TEs.map(t => freshRec(t) as NonTupleTExp));
        } else {
            return derefedTe;
        }
    };
    return freshRec(te);
};