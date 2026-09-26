import Mathlib
import Submission.Work.FreeProduct.Basic
import Submission.Work.FreeProduct.Length
import Submission.Work.FreeProduct.T_zpow_injective

/-!
# Prefixes of reduced words in `ℤ/2 ∗ ℤ/3`

The main tool is `toList_equiv_toProd_mul`: if a list `l` of letters is a reduced word whose last
letter lies in a different factor from the first letter of a reduced word `w`, then the reduced
word of `toProd l * w.prod` is the concatenation `l ++ w.toList`.  In particular the length is
additive.

The second half records the explicit prefixes used in the proofs of the two directness statements
(`x`, `y x`, `y² x`, `x y² x`, ...).
-/

namespace Work.FreeProduct

open Work.Modular.PresGroup
open scoped MonoidAlgebra

noncomputable section

/-- **Concatenation of reduced words.**  If the junction between the prefix `l` and the word `w`
involves letters from different factors, the reduced word of the product is the concatenation. -/
theorem toList_equiv_toProd_mul (l : List Letter) (w : W)
    (hne : ∀ a ∈ l, a.2 ≠ 1) (hchain : l.IsChain (fun a b : Letter => a.1 ≠ b.1))
    (hjun : ∀ a ∈ l.getLast?, ∀ b ∈ w.toList.head?, a.1 ≠ b.1) :
    (Monoid.CoprodI.Word.equiv (toProd l * w.prod)).toList = l ++ w.toList := by
  have hchain' : (l ++ w.toList).IsChain (fun a b : Letter => a.1 ≠ b.1) :=
    List.IsChain.append hchain w.chain_ne hjun
  have hne' : ∀ a ∈ l ++ w.toList, a.2 ≠ 1 := by
    intro a ha
    rcases List.mem_append.mp ha with h | h
    · exact hne a h
    · exact w.ne_one a h
  have hprod : (⟨l ++ w.toList, hne', hchain'⟩ : W).prod = toProd l * w.prod := by
    simp only [Monoid.CoprodI.Word.prod, List.map_append, List.prod_append, toProd]
  have h1 : Monoid.CoprodI.Word.equiv (toProd l * w.prod) = ⟨l ++ w.toList, hne', hchain'⟩ :=
    eq_of_prod_eq (by rw [prod_equiv]; exact hprod.symm)
  rw [h1]

/-- The length is additive across such a concatenation. -/
theorem elen_toProd_mul (l : List Letter) (w : W)
    (hne : ∀ a ∈ l, a.2 ≠ 1) (hchain : l.IsChain (fun a b : Letter => a.1 ≠ b.1))
    (hjun : ∀ a ∈ l.getLast?, ∀ b ∈ w.toList.head?, a.1 ≠ b.1) :
    elen (toProd l * w.prod) = l.length + wlen w := by
  rw [elen, wlen, toList_equiv_toProd_mul l w hne hchain hjun, List.length_append, wlen]

/-- Version using the first letter of `w` instead of the head of the list. -/
theorem elen_toProd_mul_of_fstIdx (l : List Letter) (a : Letter) (w : W)
    (hne : ∀ b ∈ l, b.2 ≠ 1) (hchain : l.IsChain (fun a b : Letter => a.1 ≠ b.1))
    (hlast : l.getLast? = some a) (hj : w.fstIdx ≠ some a.1) :
    elen (toProd l * w.prod) = l.length + wlen w := by
  refine elen_toProd_mul l w hne hchain ?_
  intro a' ha' b hb
  have h1 : a' = a := by
    have ha'' : some a = some a' := by rw [← hlast]; exact ha'
    exact (Option.some.inj ha'').symm
  have h2 : w.fstIdx = some b.1 := by
    have hb' : w.toList.head? = some b := hb
    simp [Monoid.CoprodI.Word.fstIdx, hb']
  intro hcon
  exact hj (by rw [h2]; exact congrArg some (hcon.symm.trans (congrArg Sigma.fst h1)))

/-! ## The explicit prefixes -/

/-- `x` as a list of letters. -/
def pX : List Letter := [Lx]
/-- `y x` as a list of letters. -/
def pYX : List Letter := [Ly, Lx]
/-- `y² x` as a list of letters. -/
def pY2X : List Letter := [Ly2, Lx]
/-- `x y x` as a list of letters. -/
def pXYX : List Letter := [Lx, Ly, Lx]
/-- `x y² x` as a list of letters. -/
def pXY2X : List Letter := [Lx, Ly2, Lx]
/-- `x y` as a list of letters. -/
def pXY : List Letter := [Lx, Ly]
/-- `y x y x` as a list of letters. -/
def pYXYX : List Letter := [Ly, Lx, Ly, Lx]
/-- `y x y² x` as a list of letters. -/
def pYXY2X : List Letter := [Ly, Lx, Ly2, Lx]

@[simp] theorem toProd_pX : toProd pX = x := rfl
@[simp] theorem toProd_pYX : toProd pYX = y * x := rfl
@[simp] theorem toProd_pY2X : toProd pY2X = y2 * x := by
  rw [pY2X, toProd_cons, toProd_cons, toProd_nil, mul_one, of_Ly2, of_Lx]
@[simp] theorem toProd_pXY : toProd pXY = T := rfl
@[simp] theorem toProd_pXYX : toProd pXYX = x * y * x := rfl
@[simp] theorem toProd_pXY2X : toProd pXY2X = x * y2 * x := by
  rw [pXY2X, toProd_cons, toProd_cons, toProd_cons, toProd_nil, mul_one, of_Ly2, of_Lx, mul_assoc]

theorem chain_pX : pX.IsChain (fun a b : Letter => a.1 ≠ b.1) := by decide
theorem chain_pYX : pYX.IsChain (fun a b : Letter => a.1 ≠ b.1) := by decide
theorem chain_pY2X : pY2X.IsChain (fun a b : Letter => a.1 ≠ b.1) := by decide
theorem chain_pXY : pXY.IsChain (fun a b : Letter => a.1 ≠ b.1) := by decide
theorem chain_pXYX : pXYX.IsChain (fun a b : Letter => a.1 ≠ b.1) := by decide
theorem chain_pXY2X : pXY2X.IsChain (fun a b : Letter => a.1 ≠ b.1) := by decide

theorem last_pX : pX.getLast? = some Lx := rfl
theorem last_pYX : pYX.getLast? = some Lx := rfl
theorem last_pY2X : pY2X.getLast? = some Lx := rfl
theorem last_pXYX : pXYX.getLast? = some Lx := rfl
theorem last_pXY2X : pXY2X.getLast? = some Lx := rfl
theorem last_pXY : pXY.getLast? = some Ly := rfl

end

end Work.FreeProduct
