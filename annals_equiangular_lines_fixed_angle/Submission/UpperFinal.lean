import Submission.LowerFinal
import Submission.UpperB3
import Submission.Switch
import Submission.UpperB1
import Submission.UpperConfig
import Submission.NBridge
import Submission.Perron
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open EquiangularLinesFixedAngle
open Matrix
open Filter
open scoped BigOperators
open scoped RealInnerProductSpace

namespace Submission

set_option autoImplicit false

attribute [local instance] Classical.propDecidable

noncomputable section

/-! # Final assembly of the upper bounds and the main theorem -/

/-- the floor expression from the theorem (value of the eventual upper bound). -/
def upperVal (k0 : ℕ) (d : ℕ) : ℕ :=
  ⌊((k0 * (d - 1) : ℝ)) / ((k0 - 1 : ℝ))⌋₊

/-- the real value `k0(d-1)/(k0-1)`. -/
def ratioVal (k0 : ℕ) (d : ℕ) : ℝ :=
  ((k0 * (d - 1) : ℝ)) / ((k0 - 1 : ℝ))

/-- integer bound: `n ≤ r` with `r : ℝ` implies `n ≤ ⌊r⌋₊`. -/
lemma nat_le_floor_of_real_le {n : ℕ} {r : ℝ} (h : (n : ℝ) ≤ r) : n ≤ ⌊r⌋₊ := by
  exact Nat.le_floor h

/-- `ratioVal` as a real expression with casts. -/
lemma ratioVal_eq (k0 d : ℕ) :
    ratioVal k0 d = ((k0 : ℝ) * ((d : ℝ) - 1)) / ((k0 : ℝ) - 1) := rfl

/-- positivity of `k0 - 1` (real) for `k0 ≥ 2`. -/
lemma sub_one_pos (k0 : ℕ) (hk0 : 2 ≤ k0) : 0 < (k0 : ℝ) - 1 := by
  have hk0l : (1 : ℝ) < (k0 : ℝ) := by exact_mod_cast (by omega : 1 < k0)
  linarith

/-- `upperVal k0 d = ⌊ratioVal k0 d⌋₊`. -/
lemma upperVal_eq_floor (k0 d : ℕ) : upperVal k0 d = ⌊ratioVal k0 d⌋₊ := rfl

/-- if `d ≥ 2k0` then `d + 1 ≤ ratioVal`. -/
lemma ratioVal_ge_d_add_one (k0 d : ℕ) (hk0 : 2 ≤ k0) (hd : 2 * k0 ≤ d) :
    (d : ℝ) + 1 ≤ ratioVal k0 d := by
  rw [ratioVal_eq]
  have hk0r : 0 < (k0 : ℝ) - 1 := sub_one_pos k0 hk0
  rw [le_div_iff₀ hk0r]
  have hdR : (2 * (k0 : ℝ)) ≤ (d : ℝ) := by exact_mod_cast hd
  nlinarith

/-- if `d` is large then `d + 1 + c ≤ ratioVal` for any fixed real `c`. -/
lemma ratioVal_ge_d_add_one_add (k0 d : ℕ) (hk0 : 2 ≤ k0) (c : ℝ)
    (hd : (1 + ((k0 : ℝ) - 1) * (c + 2)) ≤ (d : ℝ)) :
    (d : ℝ) + 1 + c ≤ ratioVal k0 d := by
  rw [ratioVal_eq]
  have hk0r : 0 < (k0 : ℝ) - 1 := sub_one_pos k0 hk0
  have hdiv : ((k0 : ℝ) * ((d : ℝ) - 1)) / ((k0 : ℝ) - 1)
      = ((d : ℝ) - 1) + ((d : ℝ) - 1) / ((k0 : ℝ) - 1) := by
    field_simp [hk0r.ne']
    ring
  rw [hdiv]
  have h1 : c + 2 ≤ ((d : ℝ) - 1) / ((k0 : ℝ) - 1) := by
    rw [le_div_iff₀ hk0r]
    nlinarith
  nlinarith

/-- the `d + 1 + c ≤ ratioVal` bound holds eventually in `d`. -/
lemma eventually_ratioVal_ge_add (k0 : ℕ) (hk0 : 2 ≤ k0) (c : ℝ) :
    ∃ D : ℕ, ∀ d : ℕ, D ≤ d → (d : ℝ) + 1 + c ≤ ratioVal k0 d := by
  classical
  rcases exists_nat_ge (1 + ((k0 : ℝ) - 1) * (c + 2)) with ⟨D, hD⟩
  refine ⟨D, ?_⟩
  intro d hd
  apply ratioVal_ge_d_add_one_add k0 d hk0 c
  have hdR : (D : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  linarith

/-- `a/c ≤ b/d ↔ a*d ≤ b*c` for positive denominators. -/
lemma div_le_div_iff₀ {a b c d : ℝ} (hc : 0 < c) (hd : 0 < d) :
    a / c ≤ b / d ↔ a * d ≤ b * c := by
  have hbc : (b / d) * c = (b * c) / d := by
    field_simp [hd.ne']
  constructor
  · intro h
    have h1 : a ≤ (b / d) * c := (div_le_iff₀ hc).mp h
    have h2 : a ≤ (b * c) / d := by simpa [hbc] using h1
    exact (le_div_iff₀ hd).mp h2
  · intro h
    have h2 : a ≤ (b * c) / d := (le_div_iff₀ hd).mpr h
    have h1 : a ≤ (b / d) * c := by simpa [hbc] using h2
    exact (div_le_iff₀ hc).mpr h1

/-- if `d ≥ 4k0` then `(d+1)/(1-1/(2k0)) ≤ ratioVal`. -/
lemma ratioVal_ge_bound {k0 d : ℕ} (hk0 : 2 ≤ k0) (hd : 4 * k0 ≤ d) :
    ((d : ℝ) + 1) / (1 - (1 / (2 * (k0 : ℝ)))) ≤ ratioVal k0 d := by
  rw [ratioVal_eq]
  have hk0r : 0 < (k0 : ℝ) - 1 := sub_one_pos k0 hk0
  have hk0r2 : 0 < (2 * (k0 : ℝ)) := by positivity
  have hepos : 0 < 1 - (1 / (2 * (k0 : ℝ))) := by
    have hk0c : (4 : ℝ) ≤ 2 * (k0 : ℝ) := by exact_mod_cast (by omega : 4 ≤ 2 * k0)
    have hq : 1 / (2 * (k0 : ℝ)) ≤ 1 / 4 := by
      rw [div_le_iff₀ hk0r2]
      field_simp
      nlinarith
    linarith
  rw [div_le_div_iff₀ hepos hk0r]
  field_simp
  have hdR : (4 * (k0 : ℝ)) ≤ (d : ℝ) := by exact_mod_cast hd
  have hk0big : (2 : ℝ) ≤ (k0 : ℝ) := by exact_mod_cast hk0
  nlinarith

/-- eventually `d + 1 ≤ upperVal k0 d` (as naturals). -/
lemma eventually_upperVal_ge (k0 : ℕ) (hk0 : 2 ≤ k0) :
    ∃ D : ℕ, ∀ d : ℕ, D ≤ d → d + 1 ≤ upperVal k0 d := by
  refine ⟨2 * k0, ?_⟩
  intro d hd
  have h := ratioVal_ge_d_add_one k0 d hk0 hd
  have h' : ((d + 1 : ℕ) : ℝ) ≤ ratioVal k0 d := by exact_mod_cast h
  have hfl := nat_le_floor_of_real_le h'
  change d + 1 ≤ ⌊ratioVal k0 d⌋₊
  exact hfl

end
end Submission
