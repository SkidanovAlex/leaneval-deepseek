/-
  WilE8 — extension of semi-Pfaffian data along a map of variables `e : Fin k → Fin k'`.

  Used for the `SOMin` axioms `prod_right` and `prod_left`: adding a dummy coordinate to a set
  in `ℝⁿ` corresponds, on the `Star`-side, to extending the semi-Pfaffian data along the
  injection `Fin (n+m) → Fin (n+1+m)` which skips the new coordinate.  The new coordinates not
  in the image of `e` are only required to lie in the cube (`SemiPf.set` always intersects with
  the cube).
-/
import Submission.Work.WilE8.Basic

set_option autoImplicit false
noncomputable section
open Classical Topology
namespace Work.WilE8
open WilkiesDesign WilkiesDesign.E

/-- Extend an EA chain along a map of variables: the coefficients of the new chain are those of
the old one, pulled back along `e`, and `0` on the new coordinates. -/
def EAChain.extend {k k' r : ℕ} (e : Fin k → Fin k') (c : EAChain k r) : EAChain k' r where
  a := fun j i' => if h : ∃ i, e i = i' then c.a j h.choose else 0
  b := c.b

/-- Extend an EA polynomial along a map of variables. -/
def EAPoly.extend {k k' r : ℕ} (e : Fin k → Fin k') (Q : EAPoly k r) : EAPoly k' r :=
  MvPolynomial.rename (Sum.map e id) Q

/-- Extend a basic set along a map of variables. -/
def Basic.extend {k k' r : ℕ} (e : Fin k → Fin k') (B : Basic k r) : Basic k' r where
  eqs := B.eqs.map (EAPoly.extend e)
  pos := B.pos.map (EAPoly.extend e)

/-- Extend a semi-Pfaffian set along a map of variables. -/
def SemiPf.extend {k k' : ℕ} (e : Fin k → Fin k') (X : SemiPf k) : SemiPf k' where
  r := X.r
  c := EAChain.extend e X.c
  basics := X.basics.map (Basic.extend e)

/-- The injection `Fin (n+m) → Fin (n+1+m)` skipping the last-but-`m` coordinate `n`; this is the
injection underlying `prod_right`. -/
def skipInj (n m : ℕ) : Fin (n + m) → Fin (n + 1 + m) :=
  fun i => if h : (i : ℕ) < n then ⟨i, by omega⟩ else ⟨(i : ℕ) + 1, by omega⟩

/-- The injection `Fin (n+m) → Fin (n+1+m)` shifting all coordinates up by one; this is the
injection underlying `prod_left`. -/
def shiftInj (n m : ℕ) : Fin (n + m) → Fin (n + 1 + m) :=
  fun i => ⟨(i : ℕ) + 1, by omega⟩

end Work.WilE8
