import Mathlib
import Submission.Work.BW.Defs
import Submission.Work.BW.lehmer_bound
import Submission.Work.BW.relation_lattice_aligned_basis

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-! Guidance from the project lead (the requester):

LEAD NOTES (Baker–Wüstholz drive). Route design: BW = Baker–Wüstholz, Crelle 442 (1993); section and lemma numbers are BW's. Shared definitions are in Submission.Work.BW.Defs (namespace Work.BW).
Sibling nodes are dispatched in parallel, each as module Submission.Work.BW.<name> with its statement already in place: liouville_logForm, lehmer_bound, minkowski_basis, kummer_indep, logHeight_intermediate, discriminant_bound, siegel_numberField, small_relation, kummer_reduction, aux_poly, analytic_core, bw_independent, logindep_reduction. multiplicity_prop and group_reduction come later.
If your proof needs a sibling's result, IMPORT its module and use its statement. Do NOT reprove it, and do not restate it under another name. Its sorry disappears when it lands.
The constants are tight (see the notes below): do not weaken any numeric constant in your statement. If you believe the statement is false, give a concrete counterexample.

# small_relation — Waldschmidt 1980 (Acta Arith. 37), 4.1, via BW §6; 3–6k lines, medium-high risk

**Claim.** Let `ℓ₁..ℓ_m` be logarithms of the `φαᵢ`. Suppose they are ℚ-dependent but every
`m-1` of them are independent, so the relation lattice has rank 1. Then there is an integer
relation with all `yᵢ ≠ 0` and `max|yᵢ| ≤ (9md³)^m ∏ h'(αᵢ)`.

This file formalises the reduction of the claim to the *structural* input
`Work.BW.relation_lattice_basis` (imported below), which is the geometric-of-numbers /
S-unit-lattice part of Waldschmidt's proof (Minkowski's second theorem applied to the body
`∑ |yᵢ| d h'(αᵢ) ≤ T`, together with the Lehmer lower bound for non-torsion elements).

## State of this file

This file is **sorry-free**.  It proves `small_relation` from the single covolume/regulator input
`Work.BW.relation_lattice_aligned_basis` (and the Lehmer bound `Work.BW.lehmer_bound`).

Proved here (no `sorry`):

* `muRel_of_theta_eq_zero` -- `theta y = 0` forces the product to be a root of unity;
* `gap` -- the *gap*: every `y` with non-torsion product has `sum |y_i| d h'_i > 1/(60 d log 6d)`
  (from the sibling `lehmer_bound` with subadditivity of heights and `|l_i|/d <= h'_i`);
* `exists_relation` -- `Q`-dependence of the `l_i` gives a nonzero *integer* relation;
* `coords_ne_zero_of_relation` -- such a relation has all coordinates nonzero (`hmin`);
* `rel_proportional` -- any two relations are proportional, so the relation lattice has rank 1;
* `theta_mem_two_pi_I_rat` -- for `y` in the torsion-relation lattice, `theta y = (n/q) 2 pi i`;
* `small_relation_one` -- the case `m = 1`;
* linearity of `theta`, the coordinate bound `|y_i| <= sum_j |y_j| d h'_j`, and the triangle
  inequality for the weighted `l^1` length;
* the main theorem, for `m = 0` (vacuous), `m = 1`, and for `m >= 2` both rank one (`e 1 = 0`,
  where `Gamma = Z . e 0` and `theta (e 0) = 0`) and rank two (`e 1 <> 0`, where the anti-aligned
  combination `e 0 + e 1` is a nonzero relation of weighted length `<= F (e 0) + F (e 1) <= T`).

## The single input

All the difficulty sits in the covolume/regulator statement
`Work.BW.relation_lattice_aligned_basis`: the `S`-unit transference between the relation lattice
`Gamma` and the log image (see `Submission/Work/BW/relation_covolume.lean` and
`Work.BW.transference_covolume`).  Writing `theta (e j) = c_j lambda_0` for a `Z`-basis of
`Gamma`, separate bounds `F (e j) <= B` give only `F y* <= max |c| * B <= B^2` -- the *quadratic*
bound of `Work.BW.rank_two_relation`.  The linear bound needs the basis *adapted to* `ker theta`
(`theta (e 0) + theta (e 1) = 0`), and the existence of such a basis with
`F (e 0) + F (e 1) <= T` is exactly the covolume bound.
-/

namespace Work.BW

open Complex

/-- The log-form `θ(y) = ∑ yᵢ ℓᵢ`. -/
noncomputable def theta {m : ℕ} (ℓ : Fin m → ℂ) (y : Fin m → ℤ) : ℂ := ∑ i, (y i : ℂ) * ℓ i

/-- `∏ᵢ αᵢ^{yᵢ}` is a root of unity. -/
def MuRel {K : Type*} [Field K] {m : ℕ} (α : Fin m → K) (y : Fin m → ℤ) : Prop :=
  IsOfFinOrder (∏ i, α i ^ (y i : ℤ))

/-- The weights `cᵢ = d · h'(αᵢ, ℓᵢ)` of the weighted `ℓ¹` body of BW §6. -/
private noncomputable def wgt {K : Type*} [Field K] [NumberField K] {m : ℕ} (α : Fin m → K)
    (ℓ : Fin m → ℂ) (i : Fin m) : ℝ := (Module.finrank ℚ K : ℝ) * hmod (α i) (ℓ i)

/-- The weighted `ℓ¹`-norm `∑ᵢ |yᵢ| cᵢ`. -/
noncomputable def wnorm {m : ℕ} (c : Fin m → ℝ) (y : Fin m → ℤ) : ℝ :=
  ∑ i, |(y i : ℝ)| * c i

lemma wnorm_nonneg {m : ℕ} (c : Fin m → ℝ) (hc : ∀ i, 0 ≤ c i) (y : Fin m → ℤ) :
    0 ≤ wnorm c y :=
  Finset.sum_nonneg fun i _ => mul_nonneg (abs_nonneg _) (hc i)

@[simp] lemma wnorm_zero {m : ℕ} (c : Fin m → ℝ) : wnorm c (0 : Fin m → ℤ) = 0 := by
  simp [wnorm]

lemma wnorm_smul {m : ℕ} (c : Fin m → ℝ) (k : ℤ) (y : Fin m → ℤ) :
    wnorm c (k • y) = |(k : ℝ)| * wnorm c y := by
  simp only [wnorm, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by
    rw [Int.cast_mul, abs_mul]; ring


section Helpers

variable {K : Type*} [Field K] [NumberField K]

lemma hmod_pos (β : K) (ℓ : ℂ) : 0 < hmod β ℓ := by
  have hd : (0 : ℝ) < (Module.finrank ℚ K : ℝ) := Nat.cast_pos.mpr Module.finrank_pos
  refine lt_of_lt_of_le ?_ (le_max_right _ _)
  exact lt_of_lt_of_le (div_pos one_pos hd) (le_max_right _ _)

lemma hmod_nonneg (β : K) (ℓ : ℂ) : 0 ≤ hmod β ℓ := (hmod_pos β ℓ).le

lemma div_d_le_hmod (β : K) (ℓ : ℂ) :
    Height.logHeight₁ β / (Module.finrank ℚ K : ℝ) ≤ hmod β ℓ := le_max_left _ _

lemma norm_le_d_mul_hmod (β : K) (ℓ : ℂ) :
    ‖ℓ‖ ≤ (Module.finrank ℚ K : ℝ) * hmod β ℓ := by
  have hd : (0 : ℝ) < (Module.finrank ℚ K : ℝ) := Nat.cast_pos.mpr Module.finrank_pos
  have h : ‖ℓ‖ / (Module.finrank ℚ K : ℝ) ≤ hmod β ℓ :=
    le_trans (le_max_left _ _) (le_max_right _ _)
  rw [div_le_iff₀ hd] at h
  linarith

end Helpers

section LogHeight

variable {K : Type*} [Field K] [NumberField K]

lemma logHeight₁_prod_le {ι : Type*} (s : Finset ι) (f : ι → K) :
    Height.logHeight₁ (∏ i ∈ s, f i) ≤ ∑ i ∈ s, Height.logHeight₁ (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha]
      exact le_trans (Height.logHeight₁_mul_le (f a) (∏ i ∈ s, f i)) (add_le_add le_rfl ih)

lemma logHeight₁_prod_zpow_le {m : ℕ} (α : Fin m → K) (y : Fin m → ℤ) :
    Height.logHeight₁ (∏ i, α i ^ (y i : ℤ)) ≤
      ∑ i, ((y i).natAbs : ℝ) * Height.logHeight₁ (α i) := by
  refine le_trans (logHeight₁_prod_le Finset.univ (fun i => α i ^ (y i : ℤ))) ?_
  exact le_of_eq (Finset.sum_congr rfl fun i _ => Height.logHeight₁_zpow (α i) (y i))

end LogHeight


section ThetaBound

variable {K : Type*} [Field K] [NumberField K]

/-- `θ(y) = 0` implies the product `∏ αᵢ^{yᵢ}` is a root of unity. -/
lemma muRel_of_theta_eq_zero {m : ℕ} (φ : K →+* ℂ) (α : Fin m → K) (ℓ : Fin m → ℂ)
    (hℓ : ∀ i, Complex.exp (ℓ i) = φ (α i)) {y : Fin m → ℤ} (hy : theta ℓ y = 0) :
    MuRel α y := by
  rw [MuRel]
  have hexp : Complex.exp (theta ℓ y) = φ (∏ i, α i ^ (y i : ℤ)) := by
    rw [theta, Complex.exp_sum, map_prod]
    exact Finset.prod_congr rfl fun i _ => by rw [Complex.exp_int_mul, hℓ i, map_zpow₀]
  have h1 : (∏ i, α i ^ (y i : ℤ)) = 1 := by
    apply φ.injective
    rw [map_one, ← hexp, hy, Complex.exp_zero]
  rw [h1]
  exact isOfFinOrder_iff_pow_eq_one.mpr ⟨1, one_pos, one_pow 1⟩

lemma theta_le_wnorm {m : ℕ} (α : Fin m → K) (ℓ : Fin m → ℂ) (y : Fin m → ℤ) :
    ‖theta ℓ y‖ ≤ wnorm (wgt α ℓ) y := by
  simp only [theta, wnorm]
  refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun i _ => ?_)
  rw [norm_mul, Complex.norm_intCast]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  simp only [wgt]
  exact norm_le_d_mul_hmod (α i) (ℓ i)

/-- **The gap.**  Every exponent vector whose product is *not* a root of unity has weighted
length `> 1/(60 d log 6d)`; this is BW L5 (`lehmer_bound`) together with subadditivity of heights
and `|ℓᵢ|/d ≤ h′(αᵢ, ℓᵢ)`. -/
theorem gap {m : ℕ} (φ : K →+* ℂ) (α : Fin m → K) (hα : ∀ i, α i ≠ 0) (ℓ : Fin m → ℂ)
    (hℓ : ∀ i, Complex.exp (ℓ i) = φ (α i)) {y : Fin m → ℤ} (hy : ¬ MuRel α y) :
    1 < 60 * (Module.finrank ℚ K : ℝ) * Real.log (6 * (Module.finrank ℚ K : ℝ)) *
      wnorm (wgt α ℓ) y := by
  classical
  set β : K := ∏ i, α i ^ (y i : ℤ) with hβdef
  have hβ0 : β ≠ 0 := by
    rw [hβdef, Finset.prod_ne_zero_iff]
    exact fun i _ => zpow_ne_zero _ (hα i)
  have hexp : Complex.exp (theta ℓ y) = φ β := by
    rw [hβdef, theta, Complex.exp_sum, map_prod]
    exact Finset.prod_congr rfl fun i _ => by rw [Complex.exp_int_mul, hℓ i, map_zpow₀]
  have hθ : theta ℓ y ≠ 0 := by
    intro h0
    exact hy (muRel_of_theta_eq_zero φ α ℓ hℓ h0)
  have hL := lehmer_bound φ β hβ0 (theta ℓ y) hexp hθ
  have hd1 : (1 : ℝ) ≤ (Module.finrank ℚ K : ℝ) := by
    exact_mod_cast (show 1 ≤ Module.finrank ℚ K from Module.finrank_pos)
  have hc : (0 : ℝ) ≤ 60 * (Module.finrank ℚ K : ℝ) * Real.log (6 * (Module.finrank ℚ K : ℝ)) := by
    have : 0 < Real.log (6 * (Module.finrank ℚ K : ℝ)) := Real.log_pos (by linarith)
    positivity
  refine lt_of_lt_of_le hL (mul_le_mul_of_nonneg_left (max_le ?_ ?_) hc)
  · refine le_trans (logHeight₁_prod_zpow_le α y) ?_
    simp only [wnorm, wgt]
    refine Finset.sum_le_sum fun i _ => ?_
    have hd : (0 : ℝ) < (Module.finrank ℚ K : ℝ) := Nat.cast_pos.mpr Module.finrank_pos
    have h1 : Height.logHeight₁ (α i) ≤ (Module.finrank ℚ K : ℝ) * hmod (α i) (ℓ i) := by
      have h2 := div_d_le_hmod (α i) (ℓ i)
      rw [div_le_iff₀ hd] at h2
      linarith
    rw [Nat.cast_natAbs, Int.cast_abs]
    exact mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
  · exact theta_le_wnorm α ℓ y

end ThetaBound


section Structure

variable {K : Type*} [Field K]

/-- A `ℚ`-dependent family of complex numbers admits a nonzero *integer* relation. -/
lemma exists_relation {m : ℕ} (ℓ : Fin m → ℂ) (hdep : ¬ LinearIndependent ℚ ℓ) :
    ∃ y : Fin m → ℤ, y ≠ 0 ∧ theta ℓ y = 0 := by
  classical
  rw [linearIndependent_iff'] at hdep
  push Not at hdep
  obtain ⟨s, g, hs, i, hi, hgi⟩ := hdep
  set M : ℚ := ∏ j ∈ s, ((g j).den : ℚ) with hM
  have hM0 : M ≠ 0 := by
    rw [hM]
    exact Finset.prod_ne_zero_iff.mpr fun j _ => by exact_mod_cast Rat.den_nz (g j)
  have hden : ∀ j ∈ s, (M * g j).den = 1 := by
    intro j hj
    have hnum : ((g j).num : ℚ) = g j * ((g j).den : ℚ) := by
      have h := Rat.num_div_den (g j)
      field_simp at h
      linarith
    have h1 : M * g j = (((∏ k ∈ s.erase j, (g k).den) * (g j).num : ℤ) : ℚ) := by
      rw [hM, ← Finset.prod_erase_mul s (fun k => ((g k).den : ℚ)) hj]
      push_cast
      rw [hnum]
      ring
    rw [h1, Rat.den_intCast]
  set y : Fin m → ℤ := fun j => if j ∈ s then (M * g j).num else 0 with hy
  have hys : ∀ j ∈ s, (y j : ℚ) = M * g j := by
    intro j hj
    simp only [hy, hj]
    exact (Rat.den_eq_one_iff (M * g j)).mp (hden j hj)
  have hyne : y ≠ 0 := by
    intro h
    have hi0 : y i = 0 := by rw [h]; rfl
    have hzero : M * g i = 0 := by
      rw [← hys i hi, hi0]; simp
    exact hgi ((mul_eq_zero.mp hzero).resolve_left hM0)
  refine ⟨y, hyne, ?_⟩
  have hsum : ∑ j : Fin m, (y j : ℂ) * ℓ j = (M : ℂ) * ∑ j ∈ s, (g j : ℂ) * ℓ j := by
    rw [Finset.mul_sum]
    rw [← Finset.sum_subset (Finset.subset_univ s)
      (fun x _ hx => by simp [hy, hx])]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hc : (y j : ℂ) = (M : ℂ) * (g j : ℂ) := by
      rw [← Rat.cast_intCast (y j), hys j hj, Rat.cast_mul]
    rw [hc]; ring
  rw [theta, hsum]
  have hsm : ∑ j ∈ s, (g j : ℂ) * ℓ j = ∑ j ∈ s, g j • ℓ j :=
    Finset.sum_congr rfl fun j _ => by rw [Rat.smul_def]
  rw [hsm, hs, mul_zero]

end Structure

section Coords

variable {K : Type*} [Field K] [NumberField K]

/-- A nonzero integer relation among `ℓ` has all coordinates nonzero (`hmin`). -/
lemma coords_ne_zero_of_relation {m : ℕ} {ℓ : Fin m → ℂ}
    (hmin : ∀ i, LinearIndependent ℚ (fun j : {j : Fin m // j ≠ i} => ℓ j))
    {y : Fin m → ℤ} (hne : y ≠ 0) (hy : theta ℓ y = 0) (i : Fin m) : y i ≠ 0 := by
  intro hi
  have hfull : ∑ j : Fin m, (y j : ℂ) * ℓ j = 0 := hy
  have hsplit : ∑ j ∈ (Finset.univ : Finset (Fin m)).erase i, (y j : ℂ) * ℓ j = 0 := by
    have h1 := Finset.sum_erase_add (Finset.univ : Finset (Fin m))
      (fun j => (y j : ℂ) * ℓ j) (Finset.mem_univ i)
    have h2 : ∑ j : Fin m, (y j : ℂ) * ℓ j = 0 := hfull
    have hi' : (y i : ℂ) * ℓ i = 0 := by rw [hi]; simp
    rw [h2, hi'] at h1
    simpa using h1
  have hsub : ∑ j : {j : Fin m // j ≠ i}, ((y j.1 : ℚ) • ℓ j.1) = 0 := by
    have h := hsplit
    rw [Finset.sum_subtype (s := (Finset.univ : Finset (Fin m)).erase i)
      (p := fun j => j ≠ i) (h := fun j => by simp [Finset.mem_erase])
      (f := fun j => (y j : ℂ) * ℓ j)] at h
    simpa only [Rat.smul_def, Rat.cast_intCast] using h
  have hall := (linearIndependent_iff'.mp (hmin i)) Finset.univ
    (fun j => (y j.1 : ℚ)) hsub
  apply hne
  funext j
  by_cases hj : j = i
  · rw [hj]; exact hi
  · have := hall ⟨j, hj⟩ (Finset.mem_univ _)
    exact_mod_cast this

end Coords


section ThetaAlg

variable {K : Type*} [Field K]

lemma theta_zero : theta (fun _ : Fin 0 => (0:ℂ)) (fun _ => (0:ℤ)) = 0 := by simp [theta]

lemma theta_smul {m : ℕ} (ℓ : Fin m → ℂ) (a : ℤ) (y : Fin m → ℤ) :
    theta ℓ (a • y) = (a : ℂ) * theta ℓ y := by
  simp only [theta, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by push_cast; ring

lemma theta_add {m : ℕ} (ℓ : Fin m → ℂ) (y z : Fin m → ℤ) :
    theta ℓ (y + z) = theta ℓ y + theta ℓ z := by
  simp only [theta, Pi.add_apply, Int.cast_add, add_mul, Finset.sum_add_distrib]

lemma theta_neg {m : ℕ} (ℓ : Fin m → ℂ) (y : Fin m → ℤ) : theta ℓ (-y) = -(theta ℓ y) := by
  simp only [theta, Pi.neg_apply, Int.cast_neg, neg_mul, Finset.sum_neg_distrib]

end ThetaAlg

section Assembly

variable {K : Type*} [Field K] [NumberField K]

/-- Any nonzero integer relation has all coordinates nonzero (hmin + nonzero relation). -/
lemma relation_all_ne_zero {m : ℕ} {ℓ : Fin m → ℂ}
    (hmin : ∀ i, LinearIndependent ℚ (fun j : {j : Fin m // j ≠ i} => ℓ j))
    {y : Fin m → ℤ} (hne : y ≠ 0) (hy : theta ℓ y = 0) : ∀ i, y i ≠ 0 :=
  fun i => coords_ne_zero_of_relation hmin hne hy i

end Assembly


section Main

variable {K : Type*} [Field K] [NumberField K]

/-- The `m = 1` case: a single dependent logarithm vanishes. -/
lemma small_relation_one (φ : K →+* ℂ) (α : Fin 1 → K) (hα : ∀ i, α i ≠ 0)
    (ℓ : Fin 1 → ℂ) (hℓ : ∀ i, Complex.exp (ℓ i) = φ (α i))
    (hdep : ¬ LinearIndependent ℚ ℓ)
    (hmin : ∀ i, LinearIndependent ℚ (fun j : {j : Fin 1 // j ≠ i} => ℓ j)) :
    ∃ y : Fin 1 → ℤ, (∀ i, y i ≠ 0) ∧ ∑ i, (y i : ℂ) * ℓ i = 0 ∧
      ∀ i, ((y i).natAbs : ℝ) ≤
        (9 * 1 * (Module.finrank ℚ K : ℝ) ^ 3) ^ 1 * ∏ j, hmod (α j) (ℓ j) := by
  have hℓ0 : ℓ 0 = 0 := by
    by_contra hne
    apply hdep
    rw [Fintype.linearIndependent_iff]
    intro g hg
    rw [Fintype.sum_unique] at hg
    have hg0 : g 0 = 0 := by
      rcases smul_eq_zero.mp hg with h | h
      · exact h
      · exact absurd h hne
    intro i
    rw [Subsingleton.elim i 0]
    exact hg0
  refine ⟨fun _ => 1, fun i => one_ne_zero, ?_, ?_⟩
  · have hdef : (default : Fin 1) = 0 := Subsingleton.elim _ _
    rw [Fintype.sum_unique, hdef, hℓ0]
    simp
  · intro i
    have hprod : ∏ j : Fin 1, hmod (α j) (ℓ j) = hmod (α 0) (ℓ 0) := Fintype.prod_unique _
    have hd : (0:ℝ) < (Module.finrank ℚ K : ℝ) := Nat.cast_pos.mpr Module.finrank_pos
    have h1 : (1:ℝ) / (Module.finrank ℚ K : ℝ) ≤ hmod (α 0) (ℓ 0) :=
      le_trans (le_max_right _ _) (le_max_right _ _)
    have h9 : (0:ℝ) < 9 * 1 * (Module.finrank ℚ K : ℝ) ^ 3 := by positivity
    have hbig : (1:ℝ) ≤ (9 * 1 * (Module.finrank ℚ K : ℝ) ^ 3) * hmod (α 0) (ℓ 0) := by
      have hmul := mul_le_mul_of_nonneg_left h1 (le_of_lt h9)
      have heq : (9 * 1 * (Module.finrank ℚ K : ℝ) ^ 3) * ((1:ℝ) / (Module.finrank ℚ K : ℝ)) =
          9 * (Module.finrank ℚ K : ℝ) ^ 2 := by
        field_simp
      rw [heq] at hmul
      have hd1 : (1:ℝ) ≤ (Module.finrank ℚ K : ℝ) := by exact_mod_cast Module.finrank_pos
      nlinarith [sq_nonneg ((Module.finrank ℚ K : ℝ) - 1)]
    rw [hprod]
    have hbound : (1:ℝ) ≤ (9 * 1 * (Module.finrank ℚ K : ℝ) ^ 3) ^ 1 * hmod (α 0) (ℓ 0) := by
      simpa using hbig
    have hone : ((((fun _ : Fin 1 => (1:ℤ)) i).natAbs : ℝ)) = 1 := by simp
    rw [hone]
    exact hbound

end Main

/-- Waldschmidt (Acta Arith. 37 (1980), L4.1), as quoted in BW §6: if `ℓ₁,…,ℓ_m`
(logarithms of `φ αᵢ`) are `ℚ`-dependent but every `m-1` of them are independent, there is a
relation `∑ yᵢ ℓᵢ = 0` with all `yᵢ ≠ 0` and `max|yᵢ| ≤ (9md³)^m h'(α₁)⋯h'(α_m)`. -/
theorem small_relation {K : Type*} [Field K] [NumberField K] {m : ℕ} (φ : K →+* ℂ)
    (α : Fin m → K) (hα : ∀ i, α i ≠ 0) (ℓ : Fin m → ℂ)
    (hℓ : ∀ i, Complex.exp (ℓ i) = φ (α i))
    (hdep : ¬ LinearIndependent ℚ ℓ)
    (hmin : ∀ i, LinearIndependent ℚ (fun j : {j : Fin m // j ≠ i} => ℓ j)) :
    ∃ y : Fin m → ℤ, (∀ i, y i ≠ 0) ∧ ∑ i, (y i : ℂ) * ℓ i = 0 ∧
      ∀ i, ((y i).natAbs : ℝ) ≤
        (9 * m * (Module.finrank ℚ K : ℝ) ^ 3) ^ m * ∏ j, hmod (α j) (ℓ j) := by
  classical
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · subst hm0
    exact absurd linearIndependent_empty_type hdep
  obtain ⟨z, hz0, hzθ⟩ := exists_relation ℓ hdep
  have hzΓ : IsOfFinOrder (∏ i, α i ^ (z i : ℤ)) := muRel_of_theta_eq_zero φ α ℓ hℓ hzθ
  obtain ⟨e, hspan, hind, hdeg, htwo⟩ :=
    relation_lattice_aligned_basis φ α hα ℓ hℓ hdep hmin
  have hd : (0:ℝ) < (Module.finrank ℚ K : ℝ) := Nat.cast_pos.mpr Module.finrank_pos
  have hweight : ∀ i, (0:ℝ) < (Module.finrank ℚ K : ℝ) * hmod (α i) (ℓ i) :=
    fun i => mul_pos hd (hmod_pos (α i) (ℓ i))
  have hone_le_w : ∀ i, (1:ℝ) ≤ (Module.finrank ℚ K : ℝ) * hmod (α i) (ℓ i) := by
    intro i
    have h1 : (1:ℝ) / (Module.finrank ℚ K : ℝ) ≤ hmod (α i) (ℓ i) :=
      le_trans (le_max_right _ _) (le_max_right _ _)
    rw [div_le_iff₀ hd] at h1
    linarith
  -- the weighted length of `y` dominates every coordinate
  have hcoord : ∀ (y : Fin m → ℤ) (i : Fin m),
      ((y i).natAbs : ℝ) ≤ ∑ j, |((y j : ℤ) : ℝ)| * ((Module.finrank ℚ K : ℝ) * hmod (α j) (ℓ j)) := by
    intro y i
    have h1 : (((y i).natAbs : ℝ)) = |((y i : ℤ) : ℝ)| := by
      rw [Nat.cast_natAbs, Int.cast_abs]
    rw [h1]
    refine le_trans (le_mul_of_one_le_right (abs_nonneg _) (hone_le_w i)) ?_
    exact Finset.single_le_sum
      (f := fun j => |((y j : ℤ) : ℝ)| * ((Module.finrank ℚ K : ℝ) * hmod (α j) (ℓ j)))
      (fun j _ => mul_nonneg (abs_nonneg _) (le_of_lt (hweight j))) (Finset.mem_univ i)
  by_cases he1 : e 1 = 0
  · -- rank one: `Γ = ℤ • e 0`, and `e 0` is a relation
    have hspan' : ∀ y : Fin m → ℤ, IsOfFinOrder (∏ i, α i ^ (y i : ℤ)) ↔ ∃ a : ℤ, y = a • e 0 := by
      intro y
      rw [hspan y]
      constructor
      · rintro ⟨a, b, h⟩
        exact ⟨a, by rw [h, he1]; simp⟩
      · rintro ⟨a, rfl⟩
        exact ⟨a, 0, by simp⟩
    obtain ⟨a, ha⟩ := (hspan' z).mp hzΓ
    have ha0 : a ≠ 0 := fun h0 => hz0 (by rw [ha, h0, zero_smul])
    have hθe0 : theta ℓ (e 0) = 0 := by
      have h1 : theta ℓ z = 0 := hzθ
      rw [ha, theta_smul] at h1
      exact (mul_eq_zero.mp h1).resolve_left (by exact_mod_cast ha0)
    have he0 : e 0 ≠ 0 := fun h => hz0 (by rw [ha, h, smul_zero])
    exact ⟨e 0, fun i => coords_ne_zero_of_relation hmin he0 hθe0 i, hθe0,
      fun i => le_trans (hcoord (e 0) i) (hdeg he1)⟩
  · -- rank two: `e 0 + e 1` (or `e 1` when `e 0 = 0`) is a relation
    obtain ⟨hθsum, hFsum⟩ := htwo he1
    have hF0 : (0:ℝ) ≤ ∑ j, |(((e 0 j : ℤ)) : ℝ)| * ((Module.finrank ℚ K : ℝ) * hmod (α j) (ℓ j)) :=
      Finset.sum_nonneg fun j _ => mul_nonneg (abs_nonneg _) (le_of_lt (hweight j))
    by_cases he0 : e 0 = 0
    · -- `e 0 = 0`: then `θ e 1 = 0`, so `e 1` is a relation
      have hθe1 : theta ℓ (e 1) = 0 := by
        have h := hθsum
        rw [he0] at h
        simpa [theta] using h
      refine ⟨e 1, fun i => coords_ne_zero_of_relation hmin he1 hθe1 i, hθe1, fun i => ?_⟩
      exact le_trans (hcoord (e 1) i) (le_trans (le_add_of_nonneg_left hF0) hFsum)
    · -- `e 0 ≠ 0`: the anti-aligned combination `e 0 + e 1` is a nonzero relation
      have hindep := (hind he0).resolve_left he1
      have hrel : theta ℓ (e 0 + e 1) = 0 := by
        rw [theta_add]
        simpa only [theta] using hθsum
      have hy0 : e 0 + e 1 ≠ 0 := by
        intro h
        have hlin : (1 : ℤ) • e 0 + (1 : ℤ) • e 1 = 0 := by simpa using h
        exact absurd (hindep 1 1 hlin).1 (by norm_num)
      have hFsplit : (∑ j, |(((e 0 + e 1) j : ℤ) : ℝ)| *
          ((Module.finrank ℚ K : ℝ) * hmod (α j) (ℓ j))) ≤
          (∑ j, |(((e 0 j : ℤ)) : ℝ)| * ((Module.finrank ℚ K : ℝ) * hmod (α j) (ℓ j))) +
          (∑ j, |(((e 1 j : ℤ)) : ℝ)| * ((Module.finrank ℚ K : ℝ) * hmod (α j) (ℓ j))) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_le_sum fun j _ => ?_
        have h3 : |(((e 0 + e 1) j : ℤ) : ℝ)| ≤ |((e 0 j : ℤ) : ℝ)| + |((e 1 j : ℤ) : ℝ)| := by
          rw [Pi.add_apply, Int.cast_add]
          exact abs_add_le _ _
        have h4 : (0:ℝ) < (Module.finrank ℚ K : ℝ) * hmod (α j) (ℓ j) := hweight j
        calc |(((e 0 + e 1) j : ℤ) : ℝ)| * ((Module.finrank ℚ K : ℝ) * hmod (α j) (ℓ j))
            ≤ (|((e 0 j : ℤ) : ℝ)| + |((e 1 j : ℤ) : ℝ)|) *
                ((Module.finrank ℚ K : ℝ) * hmod (α j) (ℓ j)) :=
              mul_le_mul_of_nonneg_right h3 (le_of_lt h4)
          _ = _ := by ring
      exact ⟨e 0 + e 1, fun i => coords_ne_zero_of_relation hmin hy0 hrel i, hrel,
        fun i => le_trans (hcoord (e 0 + e 1) i) (le_trans hFsplit hFsum)⟩

end Work.BW
