import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.RegExportIface.RXT.Leaves
import Submission.Work.FTS.LocDataExt.SepFactor
import Submission.Work.FTS.LocData6.DthIter_Gam_abs_le6
import Submission.Work.FTS_LocDatum3a.hB_locR8

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXT.datum_bound` — the localised datum is `O(ω)` with all six derivatives

The localised datum of the route is separable in the self-similar variables,
`locG6 α L β = locR α L β (z)·Γ(θ)`, and the weight is `ω α z θ = z²·Γ(θ)/(1+z)²` with the *same*
angular factor once the profile exponent `pExp α = 3α` is inserted, so the statement is the
product of

* the angular jet bound `|D_θ^i Γ| ≤ 10⁵·Γ` (`LocData6.DthIter_Gam_abs_le6`, the same `Γ` on both
  sides), and
* the radial pointwise bound `|D_z^j locR| ≤ A·z²/(1+z)²` (from `FTS_LocDatum3a.hB_locR8`, the
  pointwise radial majorant of the localised datum),

through the separability identity `LocDataExt.mixed_sepGam`.
-/

noncomputable section
open scoped Real Topology
open Set Filter MeasureTheory

namespace Work.FTS_RegExport.RXT

/-- The angular factor `Γ(θ) = (sin θ cos²θ)^α` of the weight `ω` is the `Gam`-factor at the
profile exponent `pExp α = 3α`. -/
lemma Gam_pExp_eq_Gamma (α θ : ℝ) :
    Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ = Work.FTS.Regularity.Gamma α θ := by
  rw [Work.Spaces.Gam, Work.FTS.Regularity.Gamma, Work.ConstructionInstance.Gamma,
    Work.FTS.Regularity.pExp]
  norm_num

/-- **The radial factor of the localised datum is `O(z²/(1+z)²)` with all its `D_z`-jets, up to
order `8`.**  This is the pointwise form of the squared weighted majorant
`FTS_LocDatum3a.hB_locR8` (`(D_z^j locR·w z)² ≤ R/(1+z)²`, `w z = (1+z)²/z²`), which unwinds to
`|D_z^j locR| ≤ √R·z²/(1+z)³ ≤ √R·z²/(1+z)²`.  (The proof is self-contained: if the delegated
`Work.FTS_RegExport.RXT.radial_jet_omega` is available, this is the same statement.) -/
lemma radial_jet_omega_local {α L β : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3) (hL : 1 ≤ L) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ j : ℕ, j ≤ 8 → ∀ z θ : ℝ, 0 < z →
      |Work.Spaces.DzIter j
        (fun z _ => Work.FTS.LocDataExt.locR (Work.FTS.Regularity.pExp α) L β z) z θ|
        ≤ A * (z ^ 2 / (1 + z) ^ 2) := by
  have hp : 0 < Work.FTS.Regularity.pExp α := Work.FTS.Regularity.pExp_pos hα
  have hp1 : Work.FTS.Regularity.pExp α ≤ 1 := Work.FTS.Regularity.pExp_le_one hα13
  obtain ⟨R, hR0, hR⟩ :=
    Work.FTS_LocDatum3a.hB_locR8 (Work.FTS.Regularity.pExp α) L β hp hp1 hL
  refine ⟨Real.sqrt R, Real.sqrt_nonneg R, fun j hj z θ hz => ?_⟩
  have hzI : z ∈ Work.Spaces.Iz := le_of_lt hz
  have hsq := hR j hj z hzI θ
  have hsq' : (|Work.Spaces.DzIter j
        (fun z _ => Work.FTS.LocDataExt.locR (Work.FTS.Regularity.pExp α) L β z) z θ|
        * Work.Spaces.w z) ^ 2 ≤ R / (1 + z) ^ 2 := by
    have he : (|Work.Spaces.DzIter j
          (fun z _ => Work.FTS.LocDataExt.locR (Work.FTS.Regularity.pExp α) L β z) z θ|
          * Work.Spaces.w z) ^ 2
        = (Work.Spaces.DzIter j
          (fun z _ => Work.FTS.LocDataExt.locR (Work.FTS.Regularity.pExp α) L β z) z θ
          * Work.Spaces.w z) ^ 2 := by
      rw [mul_pow, mul_pow, sq_abs]
    rw [he]; exact hsq
  have hle : |Work.Spaces.DzIter j
        (fun z _ => Work.FTS.LocDataExt.locR (Work.FTS.Regularity.pExp α) L β z) z θ|
        * Work.Spaces.w z ≤ Real.sqrt R / (1 + z) := by
    have hle0 : (0 : ℝ) ≤ |Work.Spaces.DzIter j
        (fun z _ => Work.FTS.LocDataExt.locR (Work.FTS.Regularity.pExp α) L β z) z θ|
        * Work.Spaces.w z := by rw [Work.Spaces.w]; positivity
    have h1 : |Work.Spaces.DzIter j
          (fun z _ => Work.FTS.LocDataExt.locR (Work.FTS.Regularity.pExp α) L β z) z θ|
          * Work.Spaces.w z ≤ Real.sqrt (R / (1 + z) ^ 2) :=
      (Real.le_sqrt hle0 (by positivity)).mpr hsq'
    have h2 : Real.sqrt (R / (1 + z) ^ 2) = Real.sqrt R / (1 + z) := by
      have he : R / (1 + z) ^ 2 = (Real.sqrt R / (1 + z)) ^ 2 := by
        rw [div_pow, Real.sq_sqrt hR0]
      rw [he, Real.sqrt_sq (by positivity)]
    rwa [h2] at h1
  rw [Work.Spaces.w] at hle
  have hmul := mul_le_mul_of_nonneg_right hle (show (0 : ℝ) ≤ z ^ 2 / (1 + z) ^ 2 by positivity)
  have hsimp : |Work.Spaces.DzIter j
        (fun z _ => Work.FTS.LocDataExt.locR (Work.FTS.Regularity.pExp α) L β z) z θ|
        * ((1 + z) ^ 2 / z ^ 2) * (z ^ 2 / (1 + z) ^ 2)
      = |Work.Spaces.DzIter j
        (fun z _ => Work.FTS.LocDataExt.locR (Work.FTS.Regularity.pExp α) L β z) z θ| := by
    field_simp
  rw [hsimp] at hmul
  refine hmul.trans ?_
  have h1 : Real.sqrt R / (1 + z) ≤ Real.sqrt R := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < 1 + z)]
    calc Real.sqrt R = Real.sqrt R * 1 := by ring
      _ ≤ Real.sqrt R * (1 + z) :=
          mul_le_mul_of_nonneg_left (by linarith) (Real.sqrt_nonneg R)
  exact mul_le_mul_of_nonneg_right h1 (by positivity)

/-- The six components `(j, i)` of `idx` have `j ≤ 2` and `i ≤ 2`. -/
private lemma idx_le_two (k : Fin 6) :
    (Work.FTS.RegExportIface.RXT.idx k).1 ≤ 2 ∧ (Work.FTS.RegExportIface.RXT.idx k).2 ≤ 2 := by
  fin_cases k <;> simp [Work.FTS.RegExportIface.RXT.idx]

theorem datum_bound {α : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3) {L β : ℝ} (hL : 1 ≤ L) :
    ∃ K₀ : ℝ, 0 ≤ K₀ ∧ ∀ k : Fin 6, ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.Spaces.mixed (Work.FTS.RegExportIface.RXT.idx k).1
        (Work.FTS.RegExportIface.RXT.idx k).2
        (Work.FTS.LocData6.locG6 (Work.FTS.Regularity.pExp α) L β) z θ|
        ≤ K₀ * Work.FTS.RegExportIface.ω α z θ := by
  obtain ⟨A, hA0, hA⟩ := radial_jet_omega_local hα hα13 hL
  refine ⟨100000 * A, mul_nonneg (by norm_num) hA0, fun k z θ hz hθ0 hθ1 => ?_⟩
  have hp : 0 < Work.FTS.Regularity.pExp α := Work.FTS.Regularity.pExp_pos hα
  have hp1 : Work.FTS.Regularity.pExp α ≤ 1 := Work.FTS.Regularity.pExp_le_one hα13
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ0, le_of_lt hθ1⟩
  have hji := idx_le_two k
  have hrad := hA (Work.FTS.RegExportIface.RXT.idx k).1 (by omega) z θ hz
  have hang := Work.FTS.LocData6.DthIter_Gam_abs_le6 (Work.FTS.RegExportIface.RXT.idx k).2
    (by omega) (Work.FTS.Regularity.pExp α) hp hp1 hθI
  have hfac : Work.FTS.LocData6.locG6 (Work.FTS.Regularity.pExp α) L β
      = fun z θ => Work.FTS.LocDataExt.locR (Work.FTS.Regularity.pExp α) L β z
          * Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ := by
    rw [Work.FTS.LocData6.locG6_eq, Work.FTS.LocDataExt.locG_eq_locR_Gam]
  rw [hfac, Work.FTS.LocDataExt.mixed_sepGam, abs_mul]
  refine (mul_le_mul hrad hang (abs_nonneg _) (mul_nonneg hA0 (by positivity))).trans ?_
  have heq : (A * (z ^ 2 / (1 + z) ^ 2)) * (100000 * Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ)
      = (100000 * A) * Work.FTS.RegExportIface.ω α z θ := by
    rw [Gam_pExp_eq_Gamma, Work.FTS.RegExportIface.ω]
    ring
  exact le_of_eq heq

end Work.FTS_RegExport.RXT
