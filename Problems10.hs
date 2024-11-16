{-# LANGUAGE StandaloneDeriving #-}
module Problems10 where

{-------------------------------------------------------------------------------

CS:3820 Fall 2024 Problem Set 10
================================

This problem set explores another extension of the λ-calculus with effects.

The new effect we're adding is *exceptions*.  We have two operations:

* The expression `Throw m` throws an exception; the exception's payload is the
  value of expression `m`.
* The expression `Catch m y n` runs expression `m`:
  - If that expression evaluates to `v`, then `Catch m y n` also evaluates to
    `v`.
  - If that expression throws an exception with payload `w`, then `Catch m y n`
    evaluates to `n[w/y]`.

To keep things interesting, our language will *also* have an accumulator.
Changes to the accumulator should persist, even if an exception is thrown.
Concretely, in the expression:

    Catch (Plus (Store (Const 2)) (Throw (Const 3))) "y" Recall

The `Recall` in the catch block should return the value `Const 2`, resulting
from the `Store` in the first addend, not whatever the initial value of the
accumulator was.

-------------------------------------------------------------------------------}

-- Here is our expression data type

data Expr = -- Arithmetic
            Const Int | Plus Expr Expr 
            -- λ-calculus
          | Var String | Lam String Expr | App Expr Expr
            -- accumulator
          | Store Expr | Recall 
            -- exceptions
          | Throw Expr | Catch Expr String Expr 
  deriving Eq          

deriving instance Show Expr

-- Here's a show instance that tries to be a little more readable than the
-- default Haskell one; feel free to uncomment it (but then, be sure to comment
-- out the `deriving instance` line above).

{-
instance Show Expr where
  showsPrec _ (Const i) = shows i
  showsPrec i (Plus m n) = showParen (i > 1) $ showsPrec 2 m . showString " + " . showsPrec 2 n
  showsPrec i (Var x) = showString x
  showsPrec i (Lam x m) = showParen (i > 0) $ showString "\\" . showString x . showString " . " . showsPrec 0 m
  showsPrec i (App m n) = showParen (i > 2) $ showsPrec 2 m . showChar ' ' . showsPrec 3 n
  showsPrec i (Store m) = showParen (i > 2) $ showString "store " . showsPrec 3 m
  showsPrec i Recall    = showString "recall"
  showsPrec i (Throw m) = showParen (i > 2) $ showString "throw " . showsPrec 3 m
  showsPrec i (Catch m y n) = showParen (i > 0) $ showString "try " . showsPrec 0 m . showString " catch " . showString y . showString " -> " . showsPrec 0 n
-}  

-- Values are, as usual, integer and function constants
isValue :: Expr -> Bool
isValue (Const _) = True
isValue (Lam _ _) = True
isValue _         = False

{-------------------------------------------------------------------------------

Problems 1 & 2: Substitution
----------------------------

For your first problems, you'll need to implement substitution for our language.

I've already provided the cases for the λ-calculus.  In the case for `Lam`, I've
used a helper function `substUnder`, which only substitutes if the new variable
does not shadow the variable being replaced.

In implementing your cases, remember: substitution is about variables.  While
most of the imperative features of this language don't interact with variables,
`Catch` absolutely *does*.

Consider this example:

    (\x -> try M catch x -> N) [L/x]

Or, in our `Expr` data type:

    subst "x" l (Lam "x" (Catch m "x" n))

Suppose there's an instance of variable `x` in `N`.  Do you think that it should
be replaced by the substitution?

-------------------------------------------------------------------------------}

substUnder :: String -> Expr -> String -> Expr -> Expr
substUnder x m y n 
  | x == y = n
  | otherwise = subst x m n

subst :: String -> Expr -> Expr -> Expr
subst _ _ (Const i) = Const i
subst x m (Plus n1 n2) = Plus (subst x m n1) (subst x m n2)
subst x m (Var y) 
  | x == y = m
  | otherwise = Var y
subst x m (Lam y n) = Lam y (substUnder x m y n)
subst x m (App n1 n2) = App (subst x m n1) (subst x m n2)

subst x m (Store n) = Store (subst x m n)
subst _ _ Recall = Recall
subst x m (Throw n) = Throw (subst x m n)
subst x m (Catch n1 y n2) = Catch (subst x m n1) y (substUnder x m y n2)


{-------------------------------------------------------------------------------

Problems 3 - 10: Small-step semantics
-------------------------------------

For the remaining problems, you'll need to implement a small-step semantics for
our language.

Your semantics should be *left-to-right* and *call-by-value*.

The program state is a pair `(prog, acc)`, where `prog` is the program being
evaluated, and `acc` is the current accumulator.

Because `Store` gets call-by-value treatment, `acc` should always be a value.

Intuitively, `Store m` needs to evaluate `m` (however many steps that takes),
and then replace the current accumulator contents with the value of `m`.
`Recall` returns the contents of the accumulator.  For more detailed treatment,
please see Lecture 12 on ICON.

The more interesting cases are for `Throw` and `Catch`.

We'll implement `Throw` by "bubbling" exceptions up through computations.

For example, consider this expression

    Plus (Const 1) (Plus (Const 2) (Plus (Const 3) (Throw (Const 4))))

For this expression to step, we need

    Plus (Const 3) (Throw (Const 4))

to step.  But we can't add anything here: the second argument is a thrown
exception.  Instead, we replace the entire `Plus` expression with the exception.
That is, the first step is:

    Plus (Const 1) (Plus (Const 2) (Plus (Const 3) (Throw (Const 4))))
      ~~>
    Plus (Const 1) (Plus (Const 2) (Throw (Const 4)))

Note: the exception is still being thrown!  Now, by the same logic, our next
step is:

    Plus (Const 1) (Plus (Const 2) (Throw (Const 4)))
      ~~>
    Plus (Const 1) (Throw (Const 4))

and finally:

    Plus (Const 1) (Throw (Const 4))
      ~~>
    Throw (Const 4)

Now we can't make any more progress; this isn't a value, it's a thrown
exception, but without something to catch the exception we can't simplify any
further.

Exceptions "bubble" through all the points evaluation can happen: `Plus`, `App`,
and `Store`.  

`Throw` itself also gets call-by-value treatment: an exception does not start
"bubbling" until the thrown expression is itself a value.  Here is an example:

  Plus (Const 1) (Throw (Plus (Const 2) (Const 3)))
    ~~>
  Plus (Const 1) (Throw (Const 5))
    ~~>
  Throw (Const 5)

Note: exceptions bubble through `Throw` itself as well.

Now we can explain `Catch`.  `Catch m y n` begins by evaluating `m`.  If `m`
evaluates to a value `v`, then so does `Catch m y n`.  But, if `m` evaluates to
a thrown exception `Throw w`, then `Catch m y n` evaluates to `n[w/y]`.

For example:

    Catch (Plus (Const 1) (Throw (Const 2))) "y" (Plus (Var "y") (Const 1))
      ~~>
    Catch (Throw (Const 2)) "y" (Plus (Var "y") (Const 1))
      ~~>
    Plus (Const 2) (Const 1)
      ~~>
    Const 3

When implementing your `smallStep` function: feel free to start from the code in
Lecture 12.  But be sure to handle *all* the cases where exceptions need to
bubble; this won't *just* be `Throw` and `Catch.

-------------------------------------------------------------------------------}

smallStep :: (Expr, Expr) -> Maybe (Expr, Expr)
smallStep (expr, acc) =
    handleApp (expr, acc)   `orElse`
    handleCatch (expr, acc) `orElse`
    handlePlus (expr, acc)  `orElse`
    handleStore (expr, acc) `orElse`
    handleThrow (expr, acc) `orElse`
    handleRecall (expr, acc)

handleApp :: (Expr, Expr) -> Maybe (Expr, Expr)
handleApp (App (Lam param body) (Throw exception), acc)
    | isValue exception = Just (Throw exception, acc)
handleApp (App (Throw func) argument, acc)
    | isValue func = Just (Throw func, acc)
handleApp (App (Lam param body) argument, acc)
    | isValue argument = Just (subst param argument body, acc)
handleApp (App func argument, acc) =
    case smallStep (func, acc) of
        Just (func', acc')    -> Just (App func' argument, acc')
        Nothing               -> fmap (\(argument', acc') -> (App func argument', acc')) 
                                     (smallStep (argument, acc))
handleApp _ = Nothing

handleCatch :: (Expr, Expr) -> Maybe (Expr, Expr)
handleCatch (Catch (Throw exception) param body, acc)
    | isValue exception = Just (subst param exception body, acc)
handleCatch (Catch expr param body, acc)
    | isValue expr = Just (expr, acc)
handleCatch (Catch expr param body, acc) = 
    fmap (\(expr', acc') -> (Catch expr' param body, acc')) 
         (smallStep (expr, acc))
handleCatch _ = Nothing

handlePlus :: (Expr, Expr) -> Maybe (Expr, Expr)
handlePlus (Plus (Const left) (Const right), acc) = 
    Just (Const (left + right), acc)
handlePlus (Plus (Throw exception) expr, acc) 
    | isValue exception = Just (Throw exception, acc)
handlePlus (Plus (Const left) (Throw exception), acc) 
    | isValue exception = Just (Throw exception, acc)
handlePlus (Plus leftExpr rightExpr, acc) = 
    case smallStep (leftExpr, acc) of
        Just (leftExpr', acc') -> Just (Plus leftExpr' rightExpr, acc')
        Nothing               -> fmap (\(rightExpr', acc') -> (Plus leftExpr rightExpr', acc'))
                                     (smallStep (rightExpr, acc))
handlePlus _ = Nothing

handleStore :: (Expr, Expr) -> Maybe (Expr, Expr)
handleStore (Store (Throw exception), acc) 
    | isValue exception = Just (Throw exception, acc)
handleStore (Store expr, acc)
    | isValue expr = Just (expr, expr)
handleStore (Store expr, acc) = 
    fmap (\(expr', acc') -> (Store expr', acc'))
         (smallStep (expr, acc))
handleStore _ = Nothing

handleThrow :: (Expr, Expr) -> Maybe (Expr, Expr)
handleThrow (Throw (Throw exception), acc) 
    | isValue exception = Just (Throw exception, acc)
handleThrow (Throw exception, acc)
    | isValue exception = Nothing
handleThrow (Throw expr, acc) = 
    fmap (\(expr', acc') -> (Throw expr', acc'))
         (smallStep (expr, acc))
handleThrow _ = Nothing

handleRecall :: (Expr, Expr) -> Maybe (Expr, Expr)
handleRecall (Recall, acc) = Just (acc, acc)
handleRecall _ = Nothing

orElse :: Maybe (Expr, Expr) -> Maybe (Expr, Expr) -> Maybe (Expr, Expr)
orElse (Just result) _        = Just result
orElse Nothing    (Just result) = Just result
orElse Nothing    Nothing       = Nothing


steps :: (Expr, Expr) -> [(Expr, Expr)]
steps s = case smallStep s of
            Nothing -> [s]
            Just s' -> s : steps s'

prints :: Show a => [a] -> IO ()
prints = mapM_ print
