import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS_MuLipC.Defs
import Submission.Work.FTS.LocData.L12_add_mul
import Submission.Work.FTS.GalFields.RHS.SharpAux.Core
import Submission.Work.FTS.ClassC.A1
import Submission.Work.FTS.StrongEps.EComparison.Reduction
import Submission.Work.FTS_MuLipC.RowT.Tf_slice_integrable
import Submission.Work.FTS_MuLipC.RowT.Tf_dens_integrable

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_MuLipC.RowT

set_option autoImplicit false

/-! ## Two elementary facts about the transport field on the domain of `L₁₂` -/

/-- **`L₁₂` only sees the values on `(0,∞) × [0,π/2]`**: at `z ≥ 0` its iterated integral runs
over `Ioi z ⊆ Ioi 0` in the radial variable and over `Iθ` in the angular one, so a pointwise
equality of the two profiles there gives equality of the zero-modes. -/
theorem L12_congr_Ioi_Iθ {a b : ℝ → ℝ → ℝ}
    (h : ∀ s θ : ℝ, 0 < s → θ ∈ Work.Spaces.Iθ → a s θ = b s θ) {z : ℝ} (hz : 0 ≤ z) :
    Work.Construction.L12 a z = Work.Construction.L12 b z := by
  simp only [Work.Construction.L12, Work.FM.L12, Work.FM.L12dens]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun s hs => ?_)
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ hθ => ?_)
  rw [h s θ (lt_of_le_of_lt hz (Set.mem_Ioi.mp hs)) hθ]

/-- `sin(2θ) = 0` at the two endpoints of `Iθ`: the angular weight of `D_θ` kills the (possibly
junk) values of the derivative there. -/
theorem sin_two_eq_zero_of_mem_Iθ_of_not_mem_Ioo {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ)
    (h : θ ∉ Set.Ioo 0 (π / 2)) : Real.sin (2 * θ) = 0 := by
  rcases eq_or_lt_of_le hθ.1 with h0 | h0
  · rw [← h0]; simp
  · have h1 : θ = π / 2 :=
      le_antisymm hθ.2 (le_of_not_gt fun hlt => h ⟨h0, hlt⟩)
    rw [h1]
    have h2 : 2 * (π / 2) = π := by ring
    rw [h2, Real.sin_pi]

/-- **The transport field is additive on two profiles `C^∞` on the open quadrant.**  In the
interior of `Iθ` this is the additivity of `∂_θ` on `SmoothOpen` data
(`Work.FTS.GalFields.RHS.Sharp.pth_add_Q0`), and at the two endpoints `sin(2θ)` kills both
sides.  (Only the *quadrant* values matter: `L₁₂` integrates over `z > 0`, `θ ∈ Iθ`.) -/
theorem Tf_add_open {g d : ℝ → ℝ → ℝ}
    (hg : Work.FTS.EllipticEst.SmoothOpen g) (hd : Work.FTS.EllipticEst.SmoothOpen d) :
    ∀ s θ : ℝ, 0 < s → θ ∈ Work.Spaces.Iθ →
      Work.FTS_MuLipC.Tf (fun z θ => g z θ + d z θ) s θ
        = Work.FTS_MuLipC.Tf g s θ + Work.FTS_MuLipC.Tf d s θ := by
  intro s θ hs hθ
  have hDth : Work.Spaces.Dth (fun z θ => g z θ + d z θ) s θ
      = Work.Spaces.Dth g s θ + Work.Spaces.Dth d s θ := by
    by_cases hIoo : θ ∈ Set.Ioo 0 (π / 2)
    · have hpth := Work.FTS.GalFields.RHS.Sharp.pth_add_Q0 hg hd s θ hs hIoo.1 hIoo.2
      simp only [Work.Spaces.Dth]
      rw [hpth]; ring
    · have hzero := sin_two_eq_zero_of_mem_Iθ_of_not_mem_Ioo hθ hIoo
      simp only [Work.Spaces.Dth, hzero, zero_mul, add_zero]
  simp only [Work.FTS_MuLipC.Tf]
  rw [hDth]; ring

/-! ## Additivity of the transport zero-mode over a difference -/

/-- **The transport zero-mode is additive over a difference of profiles**, in the conditional form
in which the four integrability certificates required by `Work.FTS.LocData.L12_add_mul` are
hypotheses (they are supplied, for `C^∞`-on-the-quadrant `ℋ⁴`-profiles, by
`Work.FTS_MuLipC.RowT.Tf_slice_integrable` and `Work.FTS_MuLipC.RowT.Tf_dens_integrable`).

`Tf` is additive on `SmoothOpen` data (`Tf_add_open`), so on `(0,∞) × Iθ` the field `Tf f` agrees
with `Tf f' + Tf (f - f')`; `L₁₂` of the sum splits by `L12_add_mul` (the integrals), and the
congruence of `L₁₂` on the domain of integration moves the identity to `Tf f`. -/
theorem L12_Tf_sub_of {f f' : ℝ → ℝ → ℝ}
    (hf' : Work.FTS.EllipticEst.SmoothOpen f')
    (hdS : Work.FTS.EllipticEst.SmoothOpen (f - f'))
    (hslice' : ∀ s ∈ Set.Ioi (0 : ℝ), MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.K θ * Work.FTS_MuLipC.Tf f' s θ / s) Work.Spaces.Iθ)
    (hsliceD : ∀ s ∈ Set.Ioi (0 : ℝ), MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.K θ * Work.FTS_MuLipC.Tf (f - f') s θ / s) Work.Spaces.Iθ)
    (hdens' : MeasureTheory.IntegrableOn
      (Work.FM.L12dens Work.Spaces.K (Work.FTS_MuLipC.Tf f')) (Set.Ioi (0 : ℝ)))
    (hdensD : MeasureTheory.IntegrableOn
      (Work.FM.L12dens Work.Spaces.K (Work.FTS_MuLipC.Tf (f - f'))) (Set.Ioi (0 : ℝ))) :
    Work.Construction.L12 (Work.FTS_MuLipC.Tf f) 0
      = Work.Construction.L12 (Work.FTS_MuLipC.Tf f') 0
        + Work.Construction.L12 (Work.FTS_MuLipC.Tf (f - f')) 0 := by
  have hadd := (Work.FTS.LocData.L12_add_mul (c := 0) (a := Work.FTS_MuLipC.Tf f')
    (b := Work.FTS_MuLipC.Tf (f - f')) (z := 0) hslice' hsliceD hdens' hdensD).1
  refine (L12_congr_Ioi_Iθ (a := Work.FTS_MuLipC.Tf f)
    (b := fun z θ => Work.FTS_MuLipC.Tf f' z θ + Work.FTS_MuLipC.Tf (f - f') z θ) ?_
    le_rfl).trans hadd
  intro s θ hs hθ
  conv_lhs =>
    rw [show (f : ℝ → ℝ → ℝ) = fun z θ => f' z θ + (f - f') z θ from by
      funext z θ
      simp]
  exact Tf_add_open hf' hdS s θ hs hθ

/-- **The transport zero-mode is additive over a difference of `ℋ⁴`-honest profiles**: the
`Tf g`-form of `L12_Tf_sub_of`, with the four integrability certificates supplied by
`Work.FTS_MuLipC.RowT.Tf_slice_integrable` and `Work.FTS_MuLipC.RowT.Tf_dens_integrable`. -/
theorem L12_Tf_sub {α : ℝ} (hα : 0 < α) {f f' : ℝ → ℝ → ℝ}
    (hf' : Work.FTS.EllipticEst.SmoothOpen f')
    (hdS : Work.FTS.EllipticEst.SmoothOpen (f - f'))
    (hmem' : Work.Spaces.HkMem α 4 f')
    (hmemd : Work.Spaces.HkMem α 4 (f - f')) :
    Work.Construction.L12 (Work.FTS_MuLipC.Tf f) 0
      = Work.Construction.L12 (Work.FTS_MuLipC.Tf f') 0
        + Work.Construction.L12 (Work.FTS_MuLipC.Tf (f - f')) 0 :=
  L12_Tf_sub_of hf' hdS
    (fun s hs => Tf_slice_integrable hα hf' hmem' s hs)
    (fun s hs => Tf_slice_integrable hα hdS hmemd s hs)
    (Tf_dens_integrable hα hf' hmem')
    (Tf_dens_integrable hα hdS hmemd)

/-- **The difference row of the transport term** (`DiffRow2 α C₀`,
`Submission/Work/FTS_MuLipC/Defs.lean`): for `ClassC α` profiles of `ℋ⁴`-size `≤ C₀α²`, the
`L₁₂`-zero-mode of the *linear* transport field `Tf g = 3·D_θg/(1+z)` is Lipschitz in the profile.
The transport functional is `L₁₂` of a linear image of the profile, so this row is the
single-profile row `KMu2_row` (`|L₁₂(3 D_θg/(1+z))(0)| ≤ 9·|g|_{ℋ⁴}`) transported to the
difference `f − f'` by the additivity of `L₁₂` on the class (`KMu2_row` is
`Work.FTS_MuLamOK.KMu2_row`; the linearity of `L₁₂` on honest fields is available as
`Work.FTS.LocData.L12_add_mul`, `Work.FTS.GalFields.RHS.Sharp.L12_sub_ge0`,
`Work.FTS.GalBasis.cc.L12_add_of_HkMem`). -/
theorem diffRow2 {α C₀ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    Work.FTS_MuLipC.DiffRow2 α C₀ := by
  refine ⟨Work.FTS_MuLamOK.KMu2, Work.FTS_MuLamOK.KMu2_pos, ?_⟩
  intro f f' hf hf' _hXf _hXf'
  have hd : Work.FTS.ClassC.ClassC α (f - f') :=
    Work.FTS.StrongEps.EComparison.classC_sub hf hf'
  have hmem' : Work.Spaces.HkMem α 4 f' := Work.FTS.ClassC.classC_hkMem_four hf'
  have hmemd : Work.Spaces.HkMem α 4 (f - f') := Work.FTS.ClassC.classC_hkMem_four hd
  have hsub := L12_Tf_sub hα hf'.reg hd.reg hmem' hmemd
  have hrow := Work.FTS_MuLamOK.KMu2_row hα hα1 hd.reg hmemd
  have hdiff : Work.Construction.L12 (Work.FTS_MuLipC.Tf f) 0
      - Work.Construction.L12 (Work.FTS_MuLipC.Tf f') 0
      = Work.Construction.L12 (Work.FTS_MuLipC.Tf (f - f')) 0 := by linarith
  rw [hdiff]
  exact hrow

end Work.FTS_MuLipC.RowT
