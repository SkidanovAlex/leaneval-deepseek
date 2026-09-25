/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# Hölder spaces on subsets of a real normed space

This file sets up the `C^{k,α}` (Hölder) norms for complex valued functions on a
subset `Ω` of a real normed space `X` (the intended cases are `X = ℂ ≅ ℝ²`,
`X = ℂⁿ = EuclideanSpace ℂ (Fin n) ≅ ℝ^{2n}`, and polydiscs therein).

## Conventions

For `f : X → ℂ`, `i : ℕ` and `Ω : Set X`:

* `iterDerivNorm i f Ω` is the supremum over `x ∈ Ω` of the operator norm of the
  `i`-th iterated derivative `iteratedFDerivWithin ℝ i f Ω x` (valued in `ℝ≥0∞`,
  so that it is `∞` when the derivative is unbounded and `0` on the empty set);
* `holderSeminorm i α f Ω` is the supremum over pairs `x ≠ y` in `Ω` of
  `‖D^i f x - D^i f y‖ / ‖x - y‖ ^ α`;
* `holderNorm k α f Ω` is the sum, over `0 ≤ i ≤ k`, of
  `iterDerivNorm i f Ω + holderSeminorm i α f Ω`.

The norm takes values in `ℝ≥0∞`, so no boundedness hypothesis on `Ω` or `f` is
needed.  The extra Hölder seminorms at orders `i < k` are included (rather than
just the top one) so that monotonicity in `k` is immediate; this does not change
the standard `C^{k,α}` topology.

All the derivatives are *within* derivatives relative to `Ω`.  As usual these
are the genuine derivatives as soon as `f` is `C^i` on `Ω`; the statements below
that need this carry the corresponding `ContDiffOn` hypothesis.  (The norm is
defined for every `f`, but it is only a norm on the space of `C^k` functions.)
-/
import Mathlib

noncomputable section

open scoped NNReal ENNReal
open Set

namespace Work.CR.Flat

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Supremum over `Ω` of the operator norm of the `i`-th iterated derivative of `f`. -/
noncomputable def iterDerivNorm (i : ℕ) (f : X → ℂ) (Ω : Set X) : ℝ≥0∞ :=
  ⨆ x ∈ Ω, ENNReal.ofReal ‖iteratedFDerivWithin ℝ i f Ω x‖

/-- Hölder seminorm of order `α` of the `i`-th iterated derivative of `f` on `Ω`. -/
noncomputable def holderSeminorm (i : ℕ) (α : ℝ) (f : X → ℂ) (Ω : Set X) : ℝ≥0∞ :=
  ⨆ x ∈ Ω, ⨆ y ∈ Ω, ⨆ (_ : x ≠ y),
    ENNReal.ofReal
      (‖iteratedFDerivWithin ℝ i f Ω x - iteratedFDerivWithin ℝ i f Ω y‖ / ‖x - y‖ ^ α)

/-- The `C^{k,α}` norm of `f` on `Ω`. -/
noncomputable def holderNorm (k : ℕ) (α : ℝ) (f : X → ℂ) (Ω : Set X) : ℝ≥0∞ :=
  ∑ i ∈ Finset.range (k + 1), (iterDerivNorm i f Ω + holderSeminorm i α f Ω)

@[simp] lemma iterDerivNorm_zero (f : X → ℂ) (Ω : Set X) :
    iterDerivNorm 0 f Ω = ⨆ x ∈ Ω, ENNReal.ofReal ‖f x‖ := by
  simp [iterDerivNorm, norm_iteratedFDerivWithin_zero]

lemma le_iterDerivNorm (i : ℕ) (f : X → ℂ) (Ω : Set X) {x : X} (hx : x ∈ Ω) :
    ENNReal.ofReal ‖iteratedFDerivWithin ℝ i f Ω x‖ ≤ iterDerivNorm i f Ω :=
  le_iSup₂_of_le x hx le_rfl

lemma le_holderSeminorm (i : ℕ) (α : ℝ) (f : X → ℂ) (Ω : Set X) {x y : X}
    (hx : x ∈ Ω) (hy : y ∈ Ω) (hxy : x ≠ y) :
    ENNReal.ofReal
        (‖iteratedFDerivWithin ℝ i f Ω x - iteratedFDerivWithin ℝ i f Ω y‖ / ‖x - y‖ ^ α)
      ≤ holderSeminorm i α f Ω :=
  le_iSup₂_of_le x hx (le_iSup₂_of_le y hy (le_iSup_of_le hxy le_rfl))

lemma iterDerivNorm_le_holderNorm (k : ℕ) (α : ℝ) (f : X → ℂ) (Ω : Set X) {i : ℕ}
    (hi : i ≤ k) :
    iterDerivNorm i f Ω ≤ holderNorm k α f Ω := by
  refine le_trans ?_ (Finset.single_le_sum (f := fun i => iterDerivNorm i f Ω + holderSeminorm i α f Ω)
    (fun _ _ => bot_le) (Finset.mem_range.mpr (Nat.lt_succ_of_le hi)))
  exact le_add_right le_rfl

lemma holderSeminorm_le_holderNorm (k : ℕ) (α : ℝ) (f : X → ℂ) (Ω : Set X) {i : ℕ}
    (hi : i ≤ k) :
    holderSeminorm i α f Ω ≤ holderNorm k α f Ω := by
  refine le_trans ?_ (Finset.single_le_sum (f := fun i => iterDerivNorm i f Ω + holderSeminorm i α f Ω)
    (fun _ _ => bot_le) (Finset.mem_range.mpr (Nat.lt_succ_of_le hi)))
  exact le_add_left le_rfl

lemma iterDerivNorm_mono_set {Ω Ω' : Set X} (hΩ : IsOpen Ω) (hΩ' : IsOpen Ω')
    (h : Ω' ⊆ Ω) (i : ℕ) (f : X → ℂ) :
    iterDerivNorm i f Ω' ≤ iterDerivNorm i f Ω := by
  have e1 : Set.EqOn (iteratedFDerivWithin ℝ i f Ω') (iteratedFDeriv ℝ i f) Ω' :=
    iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (s := Ω') (f := f) i hΩ'
  have e2 : Set.EqOn (iteratedFDerivWithin ℝ i f Ω) (iteratedFDeriv ℝ i f) Ω :=
    iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (s := Ω) (f := f) i hΩ
  refine iSup₂_le fun x hx => ?_
  rw [e1 hx, ← e2 (h hx)]
  exact le_iSup₂_of_le x (h hx) le_rfl

lemma holderSeminorm_mono_set {Ω Ω' : Set X} (hΩ : IsOpen Ω) (hΩ' : IsOpen Ω')
    (h : Ω' ⊆ Ω) (i : ℕ) (α : ℝ) (f : X → ℂ) :
    holderSeminorm i α f Ω' ≤ holderSeminorm i α f Ω := by
  have e1 : Set.EqOn (iteratedFDerivWithin ℝ i f Ω') (iteratedFDeriv ℝ i f) Ω' :=
    iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (s := Ω') (f := f) i hΩ'
  have e2 : Set.EqOn (iteratedFDerivWithin ℝ i f Ω) (iteratedFDeriv ℝ i f) Ω :=
    iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (s := Ω) (f := f) i hΩ
  refine iSup₂_le fun x hx => iSup₂_le fun y hy => iSup_le fun hxy => ?_
  have hx2 : iteratedFDerivWithin ℝ i f Ω' x = iteratedFDerivWithin ℝ i f Ω x := by
    rw [e1 hx, e2 (h hx)]
  have hy2 : iteratedFDerivWithin ℝ i f Ω' y = iteratedFDerivWithin ℝ i f Ω y := by
    rw [e1 hy, e2 (h hy)]
  rw [hx2, hy2]
  exact le_iSup₂_of_le x (h hx) (le_iSup₂_of_le y (h hy) (le_iSup_of_le hxy le_rfl))

lemma holderNorm_mono_set {Ω Ω' : Set X} (hΩ : IsOpen Ω) (hΩ' : IsOpen Ω')
    (h : Ω' ⊆ Ω) (k : ℕ) (α : ℝ) (f : X → ℂ) :
    holderNorm k α f Ω' ≤ holderNorm k α f Ω :=
  Finset.sum_le_sum fun i _ =>
    add_le_add (iterDerivNorm_mono_set hΩ hΩ' h i f) (holderSeminorm_mono_set hΩ hΩ' h i α f)

lemma holderNorm_mono_k {k k' : ℕ} (h : k ≤ k') (α : ℝ) (f : X → ℂ) (Ω : Set X) :
    holderNorm k α f Ω ≤ holderNorm k' α f Ω :=
  Finset.sum_le_sum_of_subset_of_nonneg (by
    intro a ha
    exact Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp ha) (Nat.succ_le_succ h)))
    fun _ _ _ => bot_le

lemma norm_apply_le_holderNorm (k : ℕ) (α : ℝ) (f : X → ℂ) (Ω : Set X) {x : X} (hx : x ∈ Ω) :
    ENNReal.ofReal ‖f x‖ ≤ holderNorm k α f Ω := by
  rw [← norm_iteratedFDerivWithin_zero (𝕜 := ℝ) (s := Ω) (f := f) (x := x)]
  exact le_trans (le_iterDerivNorm 0 f Ω hx) (iterDerivNorm_le_holderNorm k α f Ω (Nat.zero_le k))

@[simp] lemma iterDerivNorm_zero_fun (i : ℕ) (Ω : Set X) :
    iterDerivNorm i (0 : X → ℂ) Ω = 0 := by
  refine le_antisymm ?_ bot_le
  refine iSup₂_le fun x _ => ?_
  rw [iteratedFDerivWithin_zero]
  simp

@[simp] lemma holderSeminorm_zero_fun (i : ℕ) (α : ℝ) (Ω : Set X) :
    holderSeminorm i α (0 : X → ℂ) Ω = 0 := by
  refine le_antisymm ?_ bot_le
  refine iSup₂_le fun x _ => iSup₂_le fun y _ => iSup_le fun _ => ?_
  rw [iteratedFDerivWithin_zero]
  simp

@[simp] lemma holderNorm_zero (k : ℕ) (α : ℝ) (Ω : Set X) :
    holderNorm k α (0 : X → ℂ) Ω = 0 := by
  simp [holderNorm]

end Work.CR.Flat
