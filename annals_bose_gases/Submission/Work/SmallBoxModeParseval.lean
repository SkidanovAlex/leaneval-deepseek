import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.CentreBox
import Submission.Commons.Analysis.Fourier.box3_parseval_cos
import Submission.Work.SmallBoxFourierBasis
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The box-mode (cosine-basis) Parseval in the corpus normalisation

`Commons.Analysis.Fourier.cos_basis_parseval` (fleet, Session-267) is the
completeness of the Neumann cosine basis on `[−1/2, 1/2]`:

    ∫_{−1/2}^{1/2} f² = (∫_{−1/2}^{1/2} f)²
                          + ∑_k 2 (∫_{−1/2}^{1/2} f(x)·cos ((k+1)π(x+1/2)))² .

The corpus works on the centred box `[−ℓ/2, ℓ/2]` with the modes
`boxNeumann ℓ k x = cos ((kπ/ℓ)(x + ℓ/2))` (`SmallBoxFourierBasis`), whose
squared `L²`-norms are `ℓ` (`k = 0`) and `ℓ/2` (`k ≥ 1`).  This module
rescales:

  * **`cos_parseval_scaled`** — the ℓ-scaled Parseval
    `∫_{box} g² = (1/ℓ)(∫_{box} g)²
       + ∑_k (2/ℓ)(∫_{box} g(x)·cos(((k+1)π/ℓ)(x + ℓ/2)))²`;
  * **`boxNeumann_parseval`** — the same in the corpus mode notation
    `∫_{box} g² = (1/ℓ)(∫_{box} g)² + ∑_k (2/ℓ)(∫_{box} g·boxNeumann ℓ (k+1))²`;
  * `boxNeumann_parseval_normalised` — the orthonormal-basis form
    `∫_{box} g² = (∫_{box} g·boxNeumann ℓ 0)²/ℓ
       + ∑_k (∫_{box} g·boxNeumann ℓ (k+1))²/(ℓ/2)`,
    i.e. `‖g‖² = Σ_k ⟨g, e_k⟩²` for the normalised modes
    `e_0 = boxNeumann ℓ 0/√ℓ`, `e_k = boxNeumann ℓ k/√(ℓ/2)`.

Consumption (Session-267 design note, addendum part 2): this completeness is
the input to the D1 sharp-mass step — the box-mode counterpart of
`(2π)^{-3}∫\hat f²/p²dp = (1/(4π))∬f f/|x−y|`, obtained by writing
`Σ_{k≠0}(π‖k‖/s)^{-2}⟨ê_k,f⟩² = ∬_{box²} f f G_s` (Neumann Green's function
of the box) and comparing `G_s` with `1/(4π|x−y|)` (with `NewtonCoulomb`
supplying the latter's comparison with `g0w0Mass`).
-/

set_option autoImplicit false
set_option linter.unusedVariables false

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

noncomputable section

open MeasureTheory Set
open scoped Real BigOperators

namespace Submission
namespace BoseGases

/-- **The ℓ-scaled cosine Parseval** on the centred interval
`[−ℓ/2, ℓ/2]` (rescaled from `Commons.Analysis.Fourier.cos_basis_parseval`
by `x = ℓy`):

    ∫_{−ℓ/2}^{ℓ/2} g² = (1/ℓ)(∫_{−ℓ/2}^{ℓ/2} g)²
      + ∑_k (2/ℓ) (∫_{−ℓ/2}^{ℓ/2} g(x)·cos (((k+1)π/ℓ)(x + ℓ/2)))² . -/
theorem cos_parseval_scaled {ℓ : ℝ} (hℓ : 0 < ℓ) {g : ℝ → ℝ} (hg : Continuous g) :
    (∫ x in (-(ℓ / 2))..(ℓ / 2), (g x) ^ 2)
      = (1 / ℓ) * (∫ x in (-(ℓ / 2))..(ℓ / 2), g x) ^ 2
        + ∑' k : ℕ, (2 / ℓ) *
            (∫ x in (-(ℓ / 2))..(ℓ / 2),
              g x * Real.cos ((((k : ℝ) + 1) * Real.pi / ℓ) * (x + ℓ / 2))) ^ 2 := by
  have hne : ℓ ≠ 0 := ne_of_gt hℓ
  have hbase := Commons.Analysis.Fourier.cos_basis_parseval
    (f := fun y : ℝ => g (ℓ * y)) (hg.comp (continuous_const.mul continuous_id))
  -- rewrite the LHS integral
  have hL : (∫ y in (-(1 / 2))..(1 / 2), (g (ℓ * y)) ^ 2)
      = ℓ⁻¹ * ∫ x in (-(ℓ / 2))..(ℓ / 2), (g x) ^ 2 := by
    have := intervalIntegral.integral_comp_mul_left (fun x : ℝ => (g x) ^ 2) hne (a := -(1 / 2))
      (b := 1 / 2) (c := ℓ)
    simp only [smul_eq_mul] at this
    rw [this]
    congr 2 <;> ring
  have hA : (∫ y in (-(1 / 2))..(1 / 2), g (ℓ * y))
      = ℓ⁻¹ * ∫ x in (-(ℓ / 2))..(ℓ / 2), g x := by
    have := intervalIntegral.integral_comp_mul_left (fun x : ℝ => g x) hne (a := -(1 / 2))
      (b := 1 / 2) (c := ℓ)
    simp only [smul_eq_mul] at this
    rw [this]
    congr 2 <;> ring
  have hB : ∀ k : ℕ,
      (∫ y in (-(1 / 2))..(1 / 2), g (ℓ * y) * Real.cos (((k : ℝ) + 1) * Real.pi * (y + 1 / 2)))
        = ℓ⁻¹ * ∫ x in (-(ℓ / 2))..(ℓ / 2),
            g x * Real.cos ((((k : ℝ) + 1) * Real.pi / ℓ) * (x + ℓ / 2)) := by
    intro k
    have hpt : (fun y : ℝ => g (ℓ * y) * Real.cos (((k : ℝ) + 1) * Real.pi * (y + 1 / 2)))
        = fun y : ℝ => (fun x : ℝ =>
            g x * Real.cos ((((k : ℝ) + 1) * Real.pi / ℓ) * (x + ℓ / 2))) (ℓ * y) := by
      funext y
      simp only
      congr 1
      have h : (ℓ * y + ℓ / 2) = ℓ * (y + 1 / 2) := by ring
      rw [h]
      field_simp
    rw [hpt]
    have := intervalIntegral.integral_comp_mul_left
      (fun x : ℝ => g x * Real.cos ((((k : ℝ) + 1) * Real.pi / ℓ) * (x + ℓ / 2)))
      hne (a := -(1 / 2)) (b := 1 / 2) (c := ℓ)
    simp only [smul_eq_mul] at this
    rw [this]
    congr 2 <;> ring
  rw [hL, hA] at hbase
  have htsum : (∑' k : ℕ, 2 * (∫ y in (-(1 / 2))..(1 / 2),
        g (ℓ * y) * Real.cos (((k : ℝ) + 1) * Real.pi * (y + 1 / 2))) ^ 2)
      = (2 / ℓ ^ 2) * ∑' k : ℕ,
          (∫ x in (-(ℓ / 2))..(ℓ / 2),
            g x * Real.cos ((((k : ℝ) + 1) * Real.pi / ℓ) * (x + ℓ / 2))) ^ 2 := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro k
    rw [hB k]
    ring
  rw [htsum] at hbase
  rw [tsum_mul_left]
  set A : ℝ := ∫ x in (-(ℓ / 2))..(ℓ / 2), (g x) ^ 2 with hAset
  set C : ℝ := ∫ x in (-(ℓ / 2))..(ℓ / 2), g x with hCset
  set S : ℝ := ∑' k : ℕ, (∫ x in (-(ℓ / 2))..(ℓ / 2),
      g x * Real.cos ((((k : ℝ) + 1) * Real.pi / ℓ) * (x + ℓ / 2))) ^ 2 with hSset
  have key : A = (1 / ℓ) * C ^ 2 + (2 / ℓ) * S := by
    have h1 : ℓ * (ℓ⁻¹ * A) = ℓ * ((ℓ⁻¹ * C) ^ 2 + (2 / ℓ ^ 2) * S) := by rw [hbase]
    have h2 : ℓ * (ℓ⁻¹ * A) = A := by field_simp
    have h3 : ℓ * ((ℓ⁻¹ * C) ^ 2 + (2 / ℓ ^ 2) * S) = (1 / ℓ) * C ^ 2 + (2 / ℓ) * S := by
      field_simp
    rw [h2, h3] at h1
    exact h1
  exact key

/-- **The corpus box-mode Parseval**: in the `boxNeumann` notation
(`boxNeumann ℓ k x = cos ((kπ/ℓ)(x + ℓ/2))`),

    ∫_{−ℓ/2}^{ℓ/2} g² = (1/ℓ)(∫_{−ℓ/2}^{ℓ/2} g)²
      + ∑_k (2/ℓ) (∫_{−ℓ/2}^{ℓ/2} g·boxNeumann ℓ (k+1))² . -/
theorem boxNeumann_parseval {ℓ : ℝ} (hℓ : 0 < ℓ) {g : ℝ → ℝ} (hg : Continuous g) :
    (∫ x in (-(ℓ / 2))..(ℓ / 2), (g x) ^ 2)
      = (1 / ℓ) * (∫ x in (-(ℓ / 2))..(ℓ / 2), g x) ^ 2
        + ∑' k : ℕ, (2 / ℓ) *
            (∫ x in (-(ℓ / 2))..(ℓ / 2), g x * boxNeumann ℓ (k + 1) x) ^ 2 := by
  simpa only [boxNeumann, Nat.cast_add, Nat.cast_one] using
    cos_parseval_scaled (ℓ := ℓ) hℓ hg

/-- **The orthonormal-basis form**: with the normalised modes
`e_0 := boxNeumann ℓ 0 / √ℓ`, `e_k := boxNeumann ℓ k / √(ℓ/2)` (`k ≥ 1`),

    ∫_{−ℓ/2}^{ℓ/2} g² = (∫ g·boxNeumann ℓ 0)²/ℓ
      + ∑_k (∫ g·boxNeumann ℓ (k+1))²/(ℓ/2) . -/
theorem boxNeumann_parseval_normalised {ℓ : ℝ} (hℓ : 0 < ℓ) {g : ℝ → ℝ}
    (hg : Continuous g) :
    (∫ x in (-(ℓ / 2))..(ℓ / 2), (g x) ^ 2)
      = (∫ x in (-(ℓ / 2))..(ℓ / 2), g x * boxNeumann ℓ 0 x) ^ 2 / ℓ
        + ∑' k : ℕ, (∫ x in (-(ℓ / 2))..(ℓ / 2), g x * boxNeumann ℓ (k + 1) x) ^ 2
            / (ℓ / 2) := by
  have h := boxNeumann_parseval (ℓ := ℓ) hℓ hg
  have h0 : (∫ x in (-(ℓ / 2))..(ℓ / 2), g x * boxNeumann ℓ 0 x)
      = ∫ x in (-(ℓ / 2))..(ℓ / 2), g x := by
    apply intervalIntegral.integral_congr
    intro x _
    simp [boxNeumann]
  have hsum : (∑' k : ℕ, (2 / ℓ) *
        (∫ x in (-(ℓ / 2))..(ℓ / 2), g x * boxNeumann ℓ (k + 1) x) ^ 2)
      = ∑' k : ℕ, (∫ x in (-(ℓ / 2))..(ℓ / 2), g x * boxNeumann ℓ (k + 1) x) ^ 2
          / (ℓ / 2) := by
    apply tsum_congr
    intro k
    ring
  rw [h, h0, ← hsum]
  ring

/-- **The `Fin 3` box-mode Parseval in the corpus notation** (the coordinate
cube `acubeF` with the product Neumann modes `boxNeumann3`):

    ∫_{acubeF s} F² = ∑_{k : Fin 3 → ℕ} (∫_{acubeF s} F·boxNeumann3 s k)²
                        / ∏_j (if k_j = 0 then s else s/2) .

(The squared `L²`-norms of `boxNeumann3 s k` are `∏_j (if k_j = 0 then s else
s/2)`: `s` for `k_j = 0`, `s/2` otherwise.  Obtained from the fleet's
`Commons.Analysis.Fourier.box3_parseval_cos` via `acubeF_eq_pi` and
`boxNeumann3 = ∏_j boxNeumann (k_j)`.)

Transfer to the `ℝ³`-valued picture: `CentreBox.acube_restrict_eq_map`
identifies `(volume : Measure ℝ³).restrict (acube s)` with the image of
`(volume : Measure (Fin 3 → ℝ)).restrict (acubeF s)` under the
measure-preserving `cgEuc3`. -/
theorem acubeF_parseval_boxNeumann3 {s : ℝ} (hs : 0 < s) {F : (Fin 3 → ℝ) → ℝ}
    (hF : Continuous F) :
    (∫ x in acubeF s, (F x) ^ 2)
      = ∑' k : Fin 3 → ℕ,
          ((∫ x in acubeF s, F x * boxNeumann3 s k x) ^ 2)
          / ∏ j : Fin 3, (if k j = 0 then s else s / 2) := by
  have hbase := Commons.Analysis.Fourier.box3_parseval_cos (ℓ := s) hs (F := F) hF
  rw [acubeF_eq_pi s]
  simp only [neg_div]
  rw [hbase]
  apply tsum_congr
  intro k
  have hpt : ∀ x : Fin 3 → ℝ,
      F x * boxNeumann3 s k x
        = F x * ∏ j : Fin 3, Real.cos (((k j : ℝ) * Real.pi / s) * (x j + s / 2)) := by
    intro x
    congr 1
  rw [show (∫ x in Set.univ.pi fun _ : Fin 3 => Set.Icc (-(s / 2)) (s / 2),
        F x * boxNeumann3 s k x)
      = ∫ x in Set.univ.pi fun _ : Fin 3 => Set.Icc (-(s / 2)) (s / 2),
        F x * ∏ j : Fin 3, Real.cos (((k j : ℝ) * Real.pi / s) * (x j + s / 2)) from
    setIntegral_congr_fun (by measurability) (fun x _ => hpt x)]

/-- The `ℝ³`-valued box-mode Parseval (the form the corpus consumes: state
slices and kernels live on `ℝ³`, the product modes are pulled back by
`cgEuc3`): with `Û_k(x) := boxNeumann3 s k (cgEuc3.symm x)`,

    ∫_{acube s} F² = ∑_{k} (∫_{acube s} F·Û_k)² / ∏_j (if k_j = 0 then s else s/2) .

Transfer of `acubeF_parseval_boxNeumann3` along the measure-preserving
`cgEuc3` (`CentreBox.acube_restrict_eq_map`). -/
theorem acube_parseval_boxNeumann3 {s : ℝ} (hs : 0 < s) {F : ℝ³ → ℝ}
    (hF : Continuous fun y : Fin 3 → ℝ => F (cgEuc3 y)) :
    (∫ x in acube s, (F x) ^ 2)
      = ∑' k : Fin 3 → ℕ,
          ((∫ x in acube s, F x * boxNeumann3 s k (cgEuc3.symm x)) ^ 2)
          / ∏ j : Fin 3, (if k j = 0 then s else s / 2) := by
  have hmp : MeasurePreserving (⇑cgEuc3)
      ((volume : Measure (Fin 3 → ℝ)).restrict (acubeF s))
      ((volume : Measure ℝ³).restrict (acube s)) :=
    ⟨cgEuc3.measurable, by rw [← acube_restrict_eq_map s]⟩
  have hemb : MeasurableEmbedding (⇑cgEuc3) := cgEuc3.measurableEmbedding
  have hbase := acubeF_parseval_boxNeumann3 (s := s) hs
    (F := fun y : Fin 3 → ℝ => F (cgEuc3 y)) (by simpa using hF)
  -- transfer the LHS
  have hL : (∫ y in acubeF s, (F (cgEuc3 y)) ^ 2) = ∫ x in acube s, (F x) ^ 2 :=
    hmp.integral_comp hemb (fun x : ℝ³ => (F x) ^ 2)
  -- transfer each summand
  have hk : ∀ k : Fin 3 → ℕ,
      (∫ y in acubeF s, F (cgEuc3 y) * boxNeumann3 s k y)
        = ∫ x in acube s, F x * boxNeumann3 s k (cgEuc3.symm x) := by
    intro k
    have h1 := hmp.integral_comp hemb
      (fun x : ℝ³ => F x * boxNeumann3 s k (cgEuc3.symm x))
    -- h1 : ∫ y, (F (cgEuc3 y) * boxNeumann3 s k (cgEuc3.symm (cgEuc3 y))) ∂μ
    --        = ∫ x, F x * boxNeumann3 s k (cgEuc3.symm x) ∂ν
    simpa using h1
  rw [hL] at hbase
  rw [hbase]
  apply tsum_congr
  intro k
  rw [hk k]

end BoseGases
end Submission
