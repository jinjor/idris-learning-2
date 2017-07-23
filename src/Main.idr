module Main


import Data.Fin
import Data.Vect
import Debug.Trace

-- http://docs.idris-lang.org/en/latest/tutorial/interp.html


-- 式の型とコンテクストの型で表したい
-- コンテクスト（ローカル変数）を暗黙的に扱いたいのであらかじめ部分適用しておく
using (G:Vect n Ty)

    data Ty = TyInt | TyBool | TyFun Ty Ty


    interpTy : Ty -> Type
    interpTy TyInt       = Integer
    interpTy TyBool      = Bool
    interpTy (TyFun A T) = interpTy A -> interpTy T


    -- 式はそこに至るコンテクストとそれ自身の型を型引数にとって型を作る
    data Expr : Vect n Ty -> Ty -> Type

    -- 変数には名前をつけず相対位置を使う（ド・ブラン・インデックス）
    -- HasType i G T はコンテクスト G 中の変数 i の型が T であると言っている
    -- Stop は直近で宣言された変数、Pop Stop はその次、以下同様
    -- \x,\y. x y は x がインデックス 0 で Stop, y がインデックス 1 で Pop Stop
    data HasType : (i : Fin n) -> Vect n Ty -> Ty -> Type where
        Stop : HasType FZ (t :: G) t
        Pop  : HasType k G t -> HasType (FS k) (u :: G) t

    -- 変数 Var は、例えば \x,\y. x y なら x Var Stop, y Var (Pop Stop)
    -- 値 Val は整数を直接持たせる Val(1)
    -- ラムダはコンテクストに新しい変数 a を追加した上で評価。a -> t 型の式を作る
    -- 適用 App は関数と引数を評価して結果の式を返す
    -- ２項演算子 Op 、第１引数はメタな型情報から作られた実際の関数の型、第２・３は両辺のそれぞれ型づけされた式
    -- If は Bool 型の式を受け取って、then else は同じ型を生成する式を受け取る、評価は遅延。
    data Expr : Vect n Ty -> Ty -> Type where
        Var : HasType i G t -> Expr G t
        Val : (x : Integer) -> Expr G TyInt
        Lam : Expr (a :: G) t -> Expr G (TyFun a t)
        App : Expr G (TyFun a t) -> Expr G a -> Expr G t
        Op  : (interpTy a -> interpTy b -> interpTy c) ->
              Expr G a -> Expr G b -> Expr G c
        If  : Expr G TyBool ->
              Lazy (Expr G a) ->
              Lazy (Expr G a) -> Expr G a

    data Env : Vect n Ty -> Type where
        Nil  : Env Nil
        (::) : interpTy a -> Env G -> Env (a :: G)

    lookup : HasType i G t -> Env G -> interpTy t
    lookup Stop    (x :: xs) = x
    lookup (Pop k) (x :: xs) = lookup k xs

    -- t 型の値を産む式を評価すると t 型の値になる
    interp : Env G -> Expr G t -> interpTy t
    interp env (Var i)     = lookup i env -- i は HasType
    interp env (Val x)     = x -- 直接 Integer を返す
    interp env (Lam sc)    = \x => interp (x :: env) sc -- Env.(::) で 実際の型の値を cons している。sc は Expr (a :: G) t
    interp env (App f s)   = interp env f (interp env s) -- 評価された関数に評価された引数を渡して結果を返す
    interp env (Op op x y) = op (interp env x) (interp env y) -- 評価された２引数関数に評価された引数を2つ渡して結果を返す
    interp env (If x t e)  = if interp env x then interp env t
                                             else interp env e

    -- \x. \y. y + x
    -- y が Var Stop、 x が Var (Pop Stop)
    add : Expr G (TyFun TyInt (TyFun TyInt TyInt))
    add = Lam (Lam (Op (+) (Var Stop) (Var (Pop Stop))))


    -- \x. if (x == 0) then 1 else (fact (x-1) * x)
    fact : Expr G (TyFun TyInt TyInt)
    fact = Lam (If (Op (==) (Var Stop) (Val 0))
                   (Val 1)
                   (Op (*) (App fact (Op (-) (Var Stop) (Val 1)))
                           (Var Stop)))

    main : IO ()
    main = do putStr "Enter a number: "
              x <- getLine
              printLn (interp [] fact (cast x))
