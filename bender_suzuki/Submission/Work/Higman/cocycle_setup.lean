/-
# Elementary consequences of the hypotheses of `Work.Higman.cocycle_normal_form`

The target `Work.Higman.cocycle_normal_form` (Higman's Lemma 12 for the two-step groups of
order `q ^ 3`) is stated for a biadditive cocycle `b : V → V → W` with `|V| = |W| ^ 2`, all
involutions of `TwoStep V W b` central and `Z(TwoStep V W b) = kerFst`.  This file isolates the
elementary, but ubiquitous, consequences of those hypotheses, so that the (many) auxiliary
results needed by the classification can share them:

* `b_self_eq_zero_iff` — the squaring form `v ↦ b v v` is anisotropic;
* `sq_eq_one_iff_mem_kerFst` — the elements with `x ^ 2 = 1` are exactly `kerFst`;
* `orderOf_eq_two_iff` — the involutions are exactly `⟨0, w⟩` with `w ≠ 0`;
* `polar_nondegenerate` — the alternating form `b u v + b v u` is non-degenerate;
* `card_W_eq_two_pow`, `card_V_eq_two_pow` — `|W| = 2 ^ n` and `|V| = 2 ^ (2n)`;
* `isPGroup_twoStep` — `TwoStep V W b` is a `2`-group (every element has order dividing four);
* `kerFstAddEquiv` — `kerFst ≅ W` as additive groups.
-/

import Mathlib
import Submission.Work.Higman.Q3.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace Work.Higman

section Setup

variable {V W : Type} [AddCommGroup V] [AddExpTwo V] [AddCommGroup W] [AddExpTwo W]
variable {b : V → V → W} [Biadd b]

/-- In a group of exponent two, `a + c = 0` forces `a = c`. -/
theorem AddExpTwo.eq_of_add_eq_zero {Z : Type*} [AddCommGroup Z] [AddExpTwo Z] {a c : Z}
    (h : a + c = 0) : a = c := by
  calc a = a + (a + c) := by rw [h, add_zero]
    _ = a + a + c := by abel
    _ = c := by rw [AddExpTwo.add_self, zero_add]

/-- **Anisotropy of the squaring form.** -/
theorem b_self_eq_zero_iff
    (hinvol : ∀ x : TwoStep V W b, x ^ 2 = 1 → x ∈ Subgroup.center (TwoStep V W b))
    (hcenter : Subgroup.center (TwoStep V W b) = TwoStep.kerFst) (v : V) :
    b v v = 0 ↔ v = 0 := by
  constructor
  · intro hv
    have hx : (⟨v, (0 : W)⟩ : TwoStep V W b) ^ 2 = 1 := by
      rw [TwoStep.sq_eq, hv]
      rfl
    have hmem : (⟨v, (0 : W)⟩ : TwoStep V W b) ∈ TwoStep.kerFst := by
      rw [← hcenter]
      exact hinvol _ hx
    simpa using hmem
  · rintro rfl
    exact Biadd.zero_left (0 : V)

/-- The elements of the two-step group whose square is `1` are exactly `kerFst`. -/
theorem sq_eq_one_iff_mem_kerFst
    (hinvol : ∀ x : TwoStep V W b, x ^ 2 = 1 → x ∈ Subgroup.center (TwoStep V W b))
    (hcenter : Subgroup.center (TwoStep V W b) = TwoStep.kerFst)
    (x : TwoStep V W b) : x ^ 2 = 1 ↔ x ∈ TwoStep.kerFst := by
  rw [TwoStep.sq_eq_one_iff, TwoStep.mem_kerFst, ← b_self_eq_zero_iff hinvol hcenter]

/-- The involutions of the two-step group are exactly the elements of `kerFst` different from
`1`, i.e. the pairs `⟨0, w⟩` with `w ≠ 0`. -/
theorem orderOf_eq_two_iff
    (hinvol : ∀ x : TwoStep V W b, x ^ 2 = 1 → x ∈ Subgroup.center (TwoStep V W b))
    (hcenter : Subgroup.center (TwoStep V W b) = TwoStep.kerFst)
    (x : TwoStep V W b) : orderOf x = 2 ↔ x.fst = 0 ∧ x.snd ≠ 0 := by
  have hsq : x ^ 2 = 1 ↔ x.fst = 0 := by
    rw [sq_eq_one_iff_mem_kerFst hinvol hcenter, TwoStep.mem_kerFst]
  constructor
  · intro h
    have h2 : x ^ 2 = 1 := by rw [← h]; exact pow_orderOf_eq_one x
    have hfst : x.fst = 0 := hsq.mp h2
    refine ⟨hfst, ?_⟩
    intro hsnd
    have : x = 1 := by ext <;> simp [hfst, hsnd]
    rw [this, orderOf_one] at h
    exact absurd h (by omega)
  · rintro ⟨hfst, hsnd⟩
    have h2 : x ^ 2 = 1 := hsq.mpr hfst
    have hne : x ≠ 1 := by
      intro h
      apply hsnd
      simpa [h]
    have hdvd : orderOf x ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr h2
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h1
    · exact absurd h1 (by rw [orderOf_eq_one_iff]; exact hne)
    · exact h1

/-- The centre is exactly `kerFst`, so `x` is central iff `x.fst = 0`. -/
theorem mem_center_iff_kerFst
    (hcenter : Subgroup.center (TwoStep V W b) = TwoStep.kerFst) (x : TwoStep V W b) :
    x ∈ Subgroup.center (TwoStep V W b) ↔ x.fst = 0 := by
  rw [hcenter, TwoStep.mem_kerFst]

/-- **Non-degeneracy of the polar form** `(u,v) ↦ b u v + b v u`: its radical is trivial. -/
theorem polar_nondegenerate
    (hcenter : Subgroup.center (TwoStep V W b) = TwoStep.kerFst) (u : V)
    (h : ∀ v : V, b u v + b v u = 0) : u = 0 := by
  have hmem : (⟨u, (0 : W)⟩ : TwoStep V W b) ∈ TwoStep.kerFst := by
    rw [← hcenter, TwoStep.mem_center_iff]
    intro y
    exact AddExpTwo.eq_of_add_eq_zero (h y)
  simpa using hmem

/-- `|W|` is a power of two. -/
theorem card_W_eq_two_pow (hW : 4 ≤ Nat.card W) : ∃ n : ℕ, Nat.card W = 2 ^ n := by
  have hfin : Finite W := by
    by_contra hfin
    rw [not_finite_iff_infinite] at hfin
    rw [Nat.card_eq_zero_of_infinite] at hW
    omega
  letI : Module (ZMod 2) W := AddCommGroup.zmodModule fun z => by
    rw [two_nsmul]; exact AddExpTwo.add_self z
  haveI : Module.Finite (ZMod 2) W := Module.Finite.of_finite
  refine ⟨Module.finrank (ZMod 2) W, ?_⟩
  have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := W)
  rwa [Nat.card_zmod] at h

/-- `|V|` is a power of two as well. -/
theorem card_V_eq_two_pow (hcardV : Nat.card V = Nat.card W ^ 2) (hW : 4 ≤ Nat.card W) :
    ∃ n : ℕ, Nat.card W = 2 ^ n ∧ Nat.card V = 2 ^ (2 * n) := by
  obtain ⟨n, hn⟩ := card_W_eq_two_pow (W := W) hW
  refine ⟨n, hn, ?_⟩
  rw [hcardV, hn, ← pow_mul, Nat.mul_comm n 2]

/-- `W` is finite under the hypotheses. -/
theorem finite_of_hW (hW : 4 ≤ Nat.card W) : Finite W := by
  by_contra hfin
  rw [not_finite_iff_infinite] at hfin
  rw [Nat.card_eq_zero_of_infinite] at hW
  omega

/-- `V` is finite under the hypotheses. -/
theorem finite_V_of_hcardV (hcardV : Nat.card V = Nat.card W ^ 2) (hW : 4 ≤ Nat.card W) :
    Finite V := by
  have hWne : Nat.card W ≠ 0 := by omega
  have hVne : Nat.card V ≠ 0 := by rw [hcardV]; exact pow_ne_zero 2 hWne
  exact (Nat.card_ne_zero.mp hVne).2

/-- The two-step group is a `2`-group: every element has order dividing four. -/
theorem isPGroup_twoStep : IsPGroup 2 (TwoStep V W b) := by
  intro x
  have hx4 : x ^ 4 = 1 := by
    have h2 : x ^ 2 = (⟨0, b x.fst x.fst⟩ : TwoStep V W b) := TwoStep.sq_eq x
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, h2, TwoStep.sq_eq]
    ext <;> simp [Biadd.zero_left]
  refine ⟨2, ?_⟩
  rw [show (2 : ℕ) ^ 2 = 4 from rfl]
  exact hx4

/-- `kerFst ≅ W` (as a plain equivalence): the second coordinate.  The group law on `kerFst` is
addition of the second coordinates (`kerFst_mul_snd`). -/
def kerFstEquiv : ↥(TwoStep.kerFst (A := V) (Z := W) (b := b)) ≃ W where
  toFun x := x.1.snd
  invFun z := ⟨⟨0, z⟩, rfl⟩
  left_inv x := by
    refine Subtype.ext ?_
    ext
    · exact x.2.symm
    · rfl
  right_inv z := rfl

/-- Multiplication in `kerFst` is addition of the second coordinates. -/
theorem kerFst_mul_snd (x y : ↥(TwoStep.kerFst (A := V) (Z := W) (b := b))) :
    (x * y).1.snd = x.1.snd + y.1.snd := by
  have hx : x.1.fst = 0 := x.2
  have hy : y.1.fst = 0 := y.2
  simp only [Subgroup.coe_mul, TwoStep.snd_mul, hx, hy, Biadd.zero_left, add_zero]

/-- `|kerFst| = |W|`. -/
theorem card_kerFst : Nat.card ↥(TwoStep.kerFst (A := V) (Z := W) (b := b)) = Nat.card W :=
  Nat.card_congr kerFstEquiv

end Setup

/-- Removing one point from a finite type decreases its cardinality by one. -/
theorem card_subtype_ne_zero (α : Type*) [Finite α] (a : α) :
    Nat.card {x : α // x ≠ a} = Nat.card α - 1 := by
  classical
  haveI : Fintype α := Fintype.ofFinite α
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  have h := Fintype.card_subtype_compl (fun x : α => x = a)
  have h1 : Fintype.card {x : α // x = a} = 1 := Fintype.card_subtype_eq a
  rw [h1] at h
  exact h

end Work.Higman
