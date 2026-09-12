import Mathlib
import ChallengeDeps
import Submission.GeometryOfNumbers.FlowLattice
import Submission.GeometryOfNumbers.SuccessiveMinima

/-!
# Successive minima of the flow lattice: the ℓ short contracting directions

For `0 < ℓ ≤ d` the two-scale flow `scaleMap (twoScale a b ℓ)` contracts the first `ℓ`
standard directions by `a`.  Hence the flow lattice `flowLattice a b ℓ` contains the `ℓ`
independent vectors `a·e₁, ..., a·e_ℓ`, each of norm `|a|`; consequently its successive
minima satisfy

`λᵢ(flowLattice a b ℓ) ≤ |a|` for every `1 ≤ i ≤ ℓ`   (`successiveMinimum_le_abs_a`),

and in the exponential form `a = exp(-t/ℓ)`, `b = exp(t/(d−ℓ))`:

`λᵢ(a_t ℤᵈ) ≤ exp(-t/ℓ)` for every `1 ≤ i ≤ ℓ`       (`successiveMinimum_exp_le`).

This is the model/elementary half of the Section-3 statement "the first `ℓ` successive
minima of `a_t s_x ℤᵈ` are at most `e^{-t/ℓ}`" (paper: the flow has `ℓ` contracting
eigenvalues `e^{-t/ℓ}`).  The matching lower bound `λᵢ ≥ |a|` (any nonzero lattice vector
has norm `≥ min(|a|,|b|)`) and the upper bounds `λᵢ ≤ |b|` for `i > ℓ` are recorded as
`norm_ge_min_of_mem`-style TODO in the ROADMAP (they need the ℤ-coordinate representation of
members of the flow lattice, via `flowLattice_eq_map`).
-/

noncomputable section

open Module exteriorPower InnerProductGeometry Real
open scoped BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false

open LinearSubspaces
open Submission.ExteriorCoordinates
open Submission.DiagonalFlow
open Submission.FlowLattice

namespace Submission.FlowLatticeMinima

variable {d : ℕ}
local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)

/-- The family of the first `i ≤ ℓ` contracted standard basis vectors, as elements of the
flow lattice: `f r = a·e_{r.val}` for `r : Fin i` (`r.val < i ≤ ℓ` so `r.val < ℓ`). -/
def contractedFamily (a b : ℝ) (ℓ : ℕ) (hℓd : ℓ ≤ d) {i : ℕ} (hi : i ≤ ℓ) :
    Fin i → flowLattice (d := d) a b ℓ :=
  fun r => ⟨(scaleMap (twoScale a b ℓ)) ((B d) ⟨r.val, by omega⟩),
    flowLattice_mem_std a b ℓ ⟨r.val, by omega⟩⟩

/-- The `i` contracted vectors of the family are `ℤ`-linearly independent (when the flow is
invertible: `a ≠ 0`, `b ≠ 0`). -/
lemma contractedFamily_linearIndependent (a b : ℝ) (ℓ : ℕ) (hℓd : ℓ ≤ d) {i : ℕ}
    (hi : i ≤ ℓ) (ha : a ≠ 0) (hb : b ≠ 0) :
    LinearIndependent ℤ (fun r : Fin i => ((contractedFamily (d := d) a b ℓ hℓd hi r : flowLattice a b ℓ) : ℝᵈ)) := by
  classical
  let emb : Fin i → Fin d := fun r => ⟨r.val, by omega⟩
  have hemb_inj : Function.Injective emb := by
    intro r s hrs
    apply Fin.ext
    simpa [emb] using (congr_arg Fin.val hrs)
  have hfull : LinearIndependent ℤ
      (fun j : Fin d => (scaleMap (twoScale a b ℓ)) ((B d) j) : Fin d → ℝᵈ) := by
    exact linearIndependent_flow_basis (d := d) a b ℓ ha hb
  have hf : (fun r : Fin i => ((scaleMap (twoScale a b ℓ)) ((B d) (emb r)) : ℝᵈ)) =
      (fun j : Fin d => (scaleMap (twoScale a b ℓ)) ((B d) j) : Fin d → ℝᵈ) ∘ emb := by
    rfl
  have hLI : LinearIndependent ℤ
      (fun r : Fin i => ((scaleMap (twoScale a b ℓ)) ((B d) (emb r)) : ℝᵈ)) := by
    rw [hf]
    exact hfull.comp emb hemb_inj
  -- the family in the statement is the same as the family indexed through `emb`
  convert hLI using 1
  ext r
  simp [contractedFamily, emb]

/-- Each of the `i` contracted vectors has norm exactly `|a|`. -/
lemma contractedFamily_norm (a b : ℝ) (ℓ : ℕ) {i : ℕ} {r : Fin i} (hi : i ≤ ℓ)
    (hℓd : ℓ ≤ d) :
    ‖((contractedFamily (d := d) a b ℓ hℓd hi r : flowLattice a b ℓ) : ℝᵈ)‖ = |a| := by
  have hrℓ : r.val < ℓ := lt_of_lt_of_le r.isLt hi
  have hr_lt_d : r.val < d := lt_of_lt_of_le hrℓ hℓd
  calc
    ‖((contractedFamily (d := d) a b ℓ hℓd hi r : flowLattice a b ℓ) : ℝᵈ)‖
        = ‖(scaleMap (twoScale a b ℓ)) ((B d) ⟨r.val, hr_lt_d⟩)‖ := by
            simp [contractedFamily]
    _ = ‖twoScale a b ℓ ⟨r.val, hr_lt_d⟩ • ((B d) ⟨r.val, hr_lt_d⟩)‖ := by
            rw [scaleMap_basis]
    _ = |twoScale a b ℓ ⟨r.val, hr_lt_d⟩| * ‖((B d) ⟨r.val, hr_lt_d⟩ : ℝᵈ)‖ := by
            rw [norm_smul, Real.norm_eq_abs]
    _ = |a| := by
            have hts : twoScale a b ℓ ⟨r.val, hr_lt_d⟩ = a := by
              simp [twoScale_apply, hrℓ]
            rw [hts]
            have hb1 : ‖((B d) ⟨r.val, hr_lt_d⟩ : ℝᵈ)‖ = 1 := (B d).orthonormal.1 _
            rw [hb1, mul_one]

/-- **First upper bound on successive minima of the flow lattice**: for `1 ≤ i ≤ ℓ` and an
invertible flow, the `i`-th successive minimum satisfies `λᵢ ≤ |a|` (the `i` contracted
standard directions are independent lattice vectors of norm `|a|`). -/
lemma successiveMinimum_le_abs_a (a b : ℝ) (ℓ : ℕ) (hℓd : ℓ ≤ d)
    (ha : a ≠ 0) (hb : b ≠ 0) (i : ℕ) (hi1 : 1 ≤ i) (hi : i ≤ ℓ) :
    Submission.SuccessiveMinima.successiveMinimum (flowLattice (d := d) a b ℓ) i ≤ |a| := by
  -- the family of `i` contracted vectors witnesses `λᵢ ≤ |a|`
  exact Submission.SuccessiveMinima.successiveMinimum_le_of_exists
    (flowLattice (d := d) a b ℓ) i (abs_nonneg a)
    (contractedFamily (d := d) a b ℓ hℓd hi)
    (contractedFamily_linearIndependent (d := d) a b ℓ hℓd hi ha hb)
    (fun r => le_of_eq (contractedFamily_norm (d := d) a b ℓ hi hℓd))

/-- **Exponential form**: for `a = exp(-t/ℓ)`, `b = exp(t/(d−ℓ))` (so `0 < ℓ < d`, the
contracted directions have `0 < a ≤ b`), the successive minima satisfy
`λᵢ(a_t ℤᵈ) ≤ exp(-t/ℓ)` for every `1 ≤ i ≤ ℓ`. -/
theorem successiveMinimum_exp_le {ℓ : ℕ} (hℓd : ℓ < d) (hℓ0 : 0 < ℓ) (t : ℝ)
    (i : ℕ) (hi1 : 1 ≤ i) (hi : i ≤ ℓ) :
    Submission.SuccessiveMinima.successiveMinimum
      (flowLattice (d := d) (Real.exp (-t / (ℓ : ℝ))) (Real.exp (t / ((d : ℝ) - (ℓ : ℝ)))) ℓ) i ≤
        Real.exp (-t / (ℓ : ℝ)) := by
  have ha : Real.exp (-t / (ℓ : ℝ)) ≠ 0 := ne_of_gt (Real.exp_pos _)
  have hb : Real.exp (t / ((d : ℝ) - (ℓ : ℝ))) ≠ 0 := ne_of_gt (Real.exp_pos _)
  have hle : Submission.SuccessiveMinima.successiveMinimum
      (flowLattice (d := d) (Real.exp (-t / (ℓ : ℝ))) (Real.exp (t / ((d : ℝ) - (ℓ : ℝ)))) ℓ) i ≤
        |Real.exp (-t / (ℓ : ℝ))| := by
    exact successiveMinimum_le_abs_a (d := d) (Real.exp (-t / (ℓ : ℝ)))
      (Real.exp (t / ((d : ℝ) - (ℓ : ℝ)))) ℓ (le_of_lt hℓd) ha hb i hi1 hi
  simpa [abs_of_pos (Real.exp_pos _)] using hle

/-- The first `i ≤ d` flowed standard basis vectors, as elements of the flow lattice
(`r ↦ f((B d) r)`); every one of them has norm `≤ max(|a|,|b|)`. -/
def flowBasisFamily (a b : ℝ) (ℓ : ℕ) {i : ℕ} (hi : i ≤ d) : Fin i → flowLattice (d := d) a b ℓ :=
  fun r => ⟨(scaleMap (twoScale a b ℓ)) ((B d) ⟨r.val, by omega⟩),
    flowLattice_mem_std a b ℓ ⟨r.val, by omega⟩⟩

/-- The first `i ≤ d` flowed basis vectors are `ℤ`-linearly independent (invertible flow). -/
lemma flowBasisFamily_linearIndependent (a b : ℝ) (ℓ : ℕ) {i : ℕ} (hi : i ≤ d)
    (ha : a ≠ 0) (hb : b ≠ 0) :
    LinearIndependent ℤ (fun r : Fin i => ((flowBasisFamily (d := d) a b ℓ hi r : flowLattice a b ℓ) : ℝᵈ)) := by
  classical
  let emb : Fin i → Fin d := fun r => ⟨r.val, by omega⟩
  have hemb_inj : Function.Injective emb := by
    intro r s hrs
    apply Fin.ext
    simpa [emb] using (congr_arg Fin.val hrs)
  have hfull : LinearIndependent ℤ
      (fun j : Fin d => (scaleMap (twoScale a b ℓ)) ((B d) j) : Fin d → ℝᵈ) := by
    exact linearIndependent_flow_basis (d := d) a b ℓ ha hb
  have hf : (fun r : Fin i => ((scaleMap (twoScale a b ℓ)) ((B d) (emb r)) : ℝᵈ)) =
      (fun j : Fin d => (scaleMap (twoScale a b ℓ)) ((B d) j) : Fin d → ℝᵈ) ∘ emb := by
    rfl
  have hLI : LinearIndependent ℤ
      (fun r : Fin i => ((scaleMap (twoScale a b ℓ)) ((B d) (emb r)) : ℝᵈ)) := by
    rw [hf]
    exact hfull.comp emb hemb_inj
  convert hLI using 1
  ext r
  simp [flowBasisFamily, emb]

/-- Each of the first `i` flowed basis vectors has norm `≤ max(|a|,|b|)` (equal to `|a|` or
`|b|` according as its index is contracting or expanding). -/
lemma flowBasisFamily_norm_le (a b : ℝ) (ℓ : ℕ) {i : ℕ} {r : Fin i} (hi : i ≤ d) :
    ‖((flowBasisFamily (d := d) a b ℓ hi r : flowLattice a b ℓ) : ℝᵈ)‖ ≤ max |a| |b| := by
  have hr_lt_d : r.val < d := lt_of_lt_of_le r.isLt hi
  calc
    ‖((flowBasisFamily (d := d) a b ℓ hi r : flowLattice a b ℓ) : ℝᵈ)‖
        = ‖(scaleMap (twoScale a b ℓ)) ((B d) ⟨r.val, hr_lt_d⟩)‖ := by
            simp [flowBasisFamily]
    _ = ‖twoScale a b ℓ ⟨r.val, hr_lt_d⟩ • ((B d) ⟨r.val, hr_lt_d⟩)‖ := by
            rw [scaleMap_basis]
    _ = |twoScale a b ℓ ⟨r.val, hr_lt_d⟩| * ‖((B d) ⟨r.val, hr_lt_d⟩ : ℝᵈ)‖ := by
            rw [norm_smul, Real.norm_eq_abs]
    _ ≤ max |a| |b| := by
            have hb1 : ‖((B d) ⟨r.val, hr_lt_d⟩ : ℝᵈ)‖ = 1 := (B d).orthonormal.1 _
            rw [hb1, mul_one]
            simp [twoScale_apply]
            split_ifs <;> simp [le_max_iff, abs_nonneg]

/-- **Upper bound on all successive minima of the flow lattice**: when `0 < a ≤ b`, every
`i`-th minimum satisfies `λᵢ ≤ |b|` for `1 ≤ i ≤ d` (all `d` flowed basis vectors have norm
`≤ max(|a|,|b|) = b`). -/
lemma successiveMinimum_le_abs_b (a b : ℝ) (ℓ : ℕ) (ha : a ≠ 0) (hb : b ≠ 0)
    (hab : |a| ≤ |b|) (i : ℕ) (hi1 : 1 ≤ i) (hi : i ≤ d) :
    Submission.SuccessiveMinima.successiveMinimum (flowLattice (d := d) a b ℓ) i ≤ |b| := by
  have hmax : max |a| |b| = |b| := max_eq_right hab
  exact Submission.SuccessiveMinima.successiveMinimum_le_of_exists
    (flowLattice (d := d) a b ℓ) i (abs_nonneg b)
    (flowBasisFamily (d := d) a b ℓ hi)
    (flowBasisFamily_linearIndependent (d := d) a b ℓ hi ha hb)
    (fun r => by
      have hle := flowBasisFamily_norm_le (d := d) a b ℓ hi (r := r)
      simpa [hmax] using hle)

/-- **Exponential form**: for `t ≥ 0`, `λᵢ(a_t ℤᵈ) ≤ exp(t/(d−ℓ))` for every `1 ≤ i ≤ d`
(the expanding directions of the exponential flow bound all successive minima). -/
theorem successiveMinimum_exp_le_all {ℓ : ℕ} (hℓd : ℓ < d) (hℓ0 : 0 < ℓ) {t : ℝ}
    (ht : 0 ≤ t) (i : ℕ) (hi1 : 1 ≤ i) (hi : i ≤ d) :
    Submission.SuccessiveMinima.successiveMinimum
      (flowLattice (d := d) (Real.exp (-t / (ℓ : ℝ))) (Real.exp (t / ((d : ℝ) - (ℓ : ℝ)))) ℓ) i ≤
        Real.exp (t / ((d : ℝ) - (ℓ : ℝ))) := by
  have ha : Real.exp (-t / (ℓ : ℝ)) ≠ 0 := ne_of_gt (Real.exp_pos _)
  have hb : Real.exp (t / ((d : ℝ) - (ℓ : ℝ))) ≠ 0 := ne_of_gt (Real.exp_pos _)
  have hab : |Real.exp (-t / (ℓ : ℝ))| ≤ |Real.exp (t / ((d : ℝ) - (ℓ : ℝ)))| := by
    rw [abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr (by
      have hℓpos : (0 : ℝ) < (ℓ : ℝ) := by exact_mod_cast hℓ0
      have hdmℓpos : (0 : ℝ) < (d : ℝ) - (ℓ : ℝ) := by
        rw [← Nat.cast_sub (le_of_lt hℓd)]
        exact_mod_cast (Nat.sub_pos_of_lt hℓd)
      have hcross : -t * ((d : ℝ) - (ℓ : ℝ)) ≤ t * (ℓ : ℝ) := by
        have hd0 : 0 ≤ (d : ℝ) - (ℓ : ℝ) := le_of_lt hdmℓpos
        have htd : 0 ≤ t * ((d : ℝ) - (ℓ : ℝ)) := mul_nonneg ht hd0
        have htℓ : 0 ≤ t * (ℓ : ℝ) := mul_nonneg ht (le_of_lt hℓpos)
        nlinarith
      rw [div_le_div_iff₀ hℓpos hdmℓpos]
      nlinarith)
  have hle : Submission.SuccessiveMinima.successiveMinimum
      (flowLattice (d := d) (Real.exp (-t / (ℓ : ℝ))) (Real.exp (t / ((d : ℝ) - (ℓ : ℝ)))) ℓ) i ≤
        |Real.exp (t / ((d : ℝ) - (ℓ : ℝ)))| := by
    exact successiveMinimum_le_abs_b (d := d) (Real.exp (-t / (ℓ : ℝ)))
      (Real.exp (t / ((d : ℝ) - (ℓ : ℝ)))) ℓ ha hb hab i hi1 hi
  simpa [abs_of_pos (Real.exp_pos _)] using hle


/-- **First minimum of the exponential flow lattice**: `λ₁(a_t ℤᵈ) ≤ exp(-t/ℓ)` (the
contracting direction of the flow gives a nonzero lattice vector of that norm). -/
theorem first_successiveMinimum_exp_le {ℓ : ℕ} (hℓd : ℓ < d) (hℓ0 : 0 < ℓ) (t : ℝ) :
    Submission.SuccessiveMinima.successiveMinimum
      (flowLattice (d := d) (Real.exp (-t / (ℓ : ℝ))) (Real.exp (t / ((d : ℝ) - (ℓ : ℝ)))) ℓ) 1 ≤
        Real.exp (-t / (ℓ : ℝ)) := by
  exact successiveMinimum_exp_le (d := d) hℓd hℓ0 t 1 (by norm_num) (by omega)

end Submission.FlowLatticeMinima
