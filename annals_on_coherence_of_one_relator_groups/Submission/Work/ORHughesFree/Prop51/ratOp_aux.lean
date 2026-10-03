import Mathlib
import Submission.Work.ORHughesFree.Prop51.ConclB
import Submission.Work.ORHughesFree.Prop51.conj

set_option autoImplicit false

namespace Work.ORHughesFree.Prop51

open Work.ORHughesFree

variable {Γ : Type} [Group Γ] {P : Type} [Ring P] {DN : Subring P}
  [MulSemiringAction (Multiplicative ℤ) ↥DN]

/-- **The `⋄`-bound at the level of `P`.**  If `a, b ∈ D_{H,P}` are mutually inverse, then the
`H`-complexity of `b` is at most `exp (exp (Tree_H a))`: both are the `⋄`-inverse of the unit
`⟨a, ha⟩` of `D_{H,P}`, whose complexity is bounded by `Prop51Data.treeH_ratOp_le`.  (Both
one-sided equations are needed, since `IsUnit` in a general ring asks for a two-sided inverse.) -/
theorem treeH_inv_le (d : Prop51Data Γ P DN)
    {a : P} (ha : a ∈ d.DH) {b : P} (hb : b ∈ d.DH) (hab : a * b = 1) (hba : b * a = 1) :
    Tree.le (d.treeH b) (Tree.exp (Tree.exp (d.treeH a))) := by
  have hunit : IsUnit (⟨a, ha⟩ : ↥d.DH) :=
    ⟨⟨⟨a, ha⟩, ⟨b, hb⟩, Subtype.ext hab, Subtype.ext hba⟩, rfl⟩
  have hrat : (⟨a, ha⟩ : ↥d.DH) * d.rDH.ratOp ⟨a, ha⟩ = 1 := d.ratOp_of_isUnit _ hunit
  have hb_eq : (⟨b, hb⟩ : ↥d.DH) = d.rDH.ratOp ⟨a, ha⟩ := by
    have h1 : (⟨a, ha⟩ : ↥d.DH) * ⟨b, hb⟩ = (⟨a, ha⟩ : ↥d.DH) * d.rDH.ratOp ⟨a, ha⟩ := by
      rw [hrat]
      exact Subtype.ext hab
    exact IsUnit.mul_left_cancel hunit h1
  have h2 : Tree.le (d.treeH ((d.rDH.ratOp ⟨a, ha⟩ : ↥d.DH) : P))
      (Tree.exp (Tree.exp (d.treeH a))) := treeH_ratOp_le d ha
  rw [← hb_eq] at h2
  exact h2

/-- **The `dlog`-form of the bound `Prop51Data.treeH_ratOp_le`.**  If `z ∈ D_{H,P}` is a unit of
`P` with inverse `w ∈ D_{H,P}`, then the `d2log` of the complexity of `w` is bounded by the
complexity of `z` itself: `w = z⋄`, so `treeH w ≤ exp (exp (treeH z))`, and
`d2log (exp (exp c)) = some c`. -/
theorem olt_d2log_treeH_inv_le (d : Prop51Data Γ P DN)
    {a : P} (ha : a ∈ d.DH) {b : P} (hb : b ∈ d.DH) (hab : a * b = 1) (hba : b * a = 1) :
    Tree.Ole (Tree.d2log (d.treeH b)) (some (d.treeH a)) := by
  refine Tree.ole_trans (Tree.ole_d2log_of_le (treeH_inv_le d ha hb hab hba)) ?_
  rw [Tree.d2log_exp_exp]
  exact Tree.ole_refl _

/-- A tree strictly below `T` has `d2log` strictly below `some T`. -/
theorem olt_d2log_of_lt {x T : Tree} (h : Tree.lt x T) :
    Tree.Olt (Tree.d2log x) (some T) :=
  Tree.ole_olt_trans (Tree.ole_d2log_of_le (Tree.le_of_lt h)) (Tree.olt_d2log_self T)

/-- **Negation.**  If `z ∈ D_{H,P}` has `d2log`-complexity strictly below `some T`, and the same
holds for the constant element `-1`, then the same holds for `-z`: this is
`-z = (-1) · z` together with the multiplicativity of the `d2log` bound. -/
theorem olt_d2log_neg (d : Prop51Data Γ P DN) {T : Tree} {z : P}
    (hz : z ∈ d.DH) (h : Tree.Olt (Tree.d2log (d.treeH z)) (some T))
    (h1 : Tree.Olt (Tree.d2log (d.treeH (d.coeffToP (-1)))) (some T)) :
    Tree.Olt (Tree.d2log (d.treeH (-z))) (some T) := by
  have hm1 : d.coeffToP (-1 : ↥DN) ∈ d.DH := d.coeffToP_mem (-1)
  have hz' : (-1 : P) * z = -z := neg_one_mul z
  have hbound : Tree.le (d.treeH (-z)) (d.treeH (d.coeffToP (-1)) * d.treeH z) := by
    rw [← hz']
    exact treeH_le_mul d hm1 hz
  have hprod : Tree.Olt (Tree.d2log (d.treeH (d.coeffToP (-1)) * d.treeH z)) (some T) :=
    Tree.ole_olt_trans (Tree.ole_d2log_mul _ _) (Tree.olt_omax_of h1 h)
  exact Tree.ole_olt_trans (Tree.ole_d2log_of_le hbound) hprod

/-- **The twist of a coefficient.**  The `H`-complexity of the coefficient
`(ofAdd k) • w ∈ D_{N,P}` (the twist of an element of the skew Laurent series ring) is the same as
that of `w`: the two are conjugate by `Φ (ofGroup (t^k))`, and `treeH_conj_eq` says that
conjugation by this unit preserves the complexity. -/
theorem treeH_conj_coeffToP (d : Prop51Data Γ P DN) (k : ℤ) (w : ↥DN) :
    d.treeH (d.coeffToP ((Multiplicative.ofAdd k) • w)) = d.treeH (d.coeffToP w) := by
  rw [conj d k w, treeH_conj_eq d k (d.coeffToP_mem w)]

/-- The `d2log`-form of `treeH_conj_coeffToP`. -/
theorem olt_d2log_conj_coeffToP (d : Prop51Data Γ P DN) (k : ℤ) (w : ↥DN) {T : Tree}
    (h : Tree.Olt (Tree.d2log (d.treeH (d.coeffToP w))) (some T)) :
    Tree.Olt (Tree.d2log (d.treeH (d.coeffToP ((Multiplicative.ofAdd k) • w)))) (some T) := by
  rwa [treeH_conj_coeffToP]

end Work.ORHughesFree.Prop51
