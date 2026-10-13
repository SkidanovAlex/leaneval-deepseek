import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.Vocab
import Submission.Work.FTS.LocData.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.FTS.H2.Defs
import Submission.Work.FTS.H2.InvOneAddSq
import Submission.Work.FTS.H2.CS1D
import Submission.Work.FTS.H2.L12densSlice
import Submission.Work.FTS.H2.L12Q.phiWeight_slice_le
import Submission.Work.Coercivity.L12dens_sq_slice
import Submission.Work.Coercivity.integral_Itheta_K
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.aesm_of_continuousOn_Qd
import Submission.Work.Spaces.aesm_slice_of_continuousOn_Qd

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2

/-! ## Ingredients of `L12ZeroQ`

The estimate `|L₁₂(f)(0)| ≤ C|f|_{ℋ⁴}` of Elgindi's Proposition `muestimate` in the interior
class `Work.FTS.Nonlin.RegQ α 4 f = SmoothQuad f ∧ HkMem α 4 f ∧ BdryTraces α 4 f` differs
from `Work.FTS.H2.L12ZeroLe` (the `SmoothNbhd` = analyticity version) only in the three
regularity inputs `SliceFacts`, `PhiWeight`, `L12densSlice`:

* the squared angular slice `θ ↦ (f z θ)²` is integrable on `Iθ` for `z > 0`
  (`l12q_slice_sq_integrableOn`) — in the interior class this comes from `HkMem` (the `i = 0`
  term of `HkIntegrand` dominates `f² w²` and `w ≥ 1`) and the `SmoothQuad`-continuity of the
  slice on the *open* interval (the endpoints are null);
* the angular density bound `|L₁₂dens(f)(z)| ≤ √3 √(∫_θ f(z,θ)²)/z` on a slice follows
  (`l12q_l12dens_slice`);
* the Hardy-weighted angular energy `r ↦ (∫_θ f(r,θ)²)·((1+r)/r)²` is a.e. strongly measurable
  on `(0,∞)` (`l12q_aesm`, `l12q_phi_aesm`), by Fubini from the joint continuity on the open
  quadrant (`Work.Spaces.aesm_of_continuousOn_Qd`), replacing the `SmoothNbhd`-based
  `Work.FTS.H2.PhiWeightAesm`;
* the radial comparison `∫_{r>0} (∫_θ f(r,θ)²)·((1+r)/r)² ≤ HkSq α 4 f` needs no smoothness at
  all and is proved from `HkMem` directly (`l12q_phiWeight_le`, using the pointwise Hardy-weight
  comparison of `Work.FTS.H2.L12Q.phiWeight_slice_le`).

The assembly below is that of `L12ZeroLe` verbatim: Cauchy–Schwarz in `r` against
`(1/(1+r))²` (`∫_{r>0} (1+r)^{-2} ≤ 2`), then `√3·√2 ≤ 3`. -/

/-- **Joint continuity of `(z,θ) ↦ (f z θ)²` on the open quadrant**, from `SmoothQuad f` (which
gives `C^∞` on `Ioi (-1) ×ˢ Ioo 0 (π/2)`; restrict to the smaller `Ioi 0 ×ˢ Ioo 0 (π/2)`). -/
private theorem l12q_quad_continuous (f : ℝ → ℝ → ℝ) (hsm : Work.FTS.LocData.SmoothQuad f) :
    ContinuousOn (fun p : ℝ × ℝ => (f p.1 p.2) ^ 2) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
  have hsub : (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo 0 (π / 2))
      ⊆ (Set.Ioi (-1) ×ˢ Set.Ioo 0 (π / 2)) := by
    rintro p hp
    rw [Set.mem_prod] at hp ⊢
    exact ⟨by simp only [Set.mem_Ioi] at hp ⊢; linarith [hp.1], hp.2⟩
  have h1 : ContinuousOn (Function.uncurry f) (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo 0 (π / 2)) :=
    hsm.continuousOn.mono hsub
  have h2 : ContinuousOn (fun p : ℝ × ℝ => (Function.uncurry f p) ^ 2)
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo 0 (π / 2)) := h1.pow 2
  simpa only [Function.uncurry] using h2

/-- **A.e. strong measurability of the angular energy in the interior class** (`SmoothQuad f`):
`r ↦ ∫_θ f(r,θ)²` on `(0,∞)`.  Replaces the `SmoothNbhd`-based route of
`Work.FTS.H2.SliceFacts`: by Fubini from the joint continuity of `(r,θ) ↦ (f r θ)²` on the open
quadrant (`Work.Spaces.aesm_of_continuousOn_Qd`), then restrict `Iz` to `Ioi 0`. -/
theorem l12q_phi_aesm (f : ℝ → ℝ → ℝ) (hsm : Work.FTS.LocData.SmoothQuad f) :
    MeasureTheory.AEStronglyMeasurable
      (fun r : ℝ => ∫ θ in Work.Spaces.Iθ, (f r θ) ^ 2)
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by
  have hquad : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => (f p.1 p.2) ^ 2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    Work.Spaces.aesm_of_continuousOn_Qd (fun p : ℝ × ℝ => (f p.1 p.2) ^ 2)
      (l12q_quad_continuous f hsm)
  have hslicemeas : MeasureTheory.AEStronglyMeasurable
      (fun r : ℝ => ∫ θ in Work.Spaces.Iθ, (f r θ) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    MeasureTheory.AEStronglyMeasurable.integral_prod_right' hquad
  have hmono : MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)) ≤
      MeasureTheory.volume.restrict Work.Spaces.Iz :=
    MeasureTheory.Measure.restrict_mono_set MeasureTheory.volume Set.Ioi_subset_Ici_self
  exact hslicemeas.mono_measure hmono

/-- **Integrability of the squared angular slice in the interior class.**  For `SmoothQuad f`
and `HkMem α 4 f`, every radial slice `θ ↦ (f z θ)²` with `z > 0` is integrable on `Iθ`.

Supplies the slice-integrability hypothesis of `Work.Coercivity.L12dens_sq_slice` in the class
`Work.FTS.Nonlin.RegQ`, where `Work.FTS.H2.slice_sq_integrableOn` (hypothesis `SmoothNbhd`)
cannot be used.  For a.e. `θ ∈ Iθ` (all `θ ∈ Ioo 0 (π/2)`) one has `0 < sin(2θ) ≤ 1` and
`w z ≥ 1`, so `(f z θ)² ≤ (f z θ·(w z/sin(2θ)^{η/2}))² ≤ HkIntegrand α 4 f z θ`
(`Work.Spaces.sq_le_HkIntegrand_z`, `i = 0`); the majorant is integrable on `Iθ` by `hmem.1`,
and the dominated function is a.e. strongly measurable there by
`Work.Spaces.aesm_slice_of_continuousOn_Qd` (continuity on the open quadrant from `hsm`). -/
theorem l12q_slice_sq_integrableOn (α : ℝ) (f : ℝ → ℝ → ℝ)
    (hsm : Work.FTS.LocData.SmoothQuad f) (hmem : Work.Spaces.HkMem α 4 f)
    {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn (fun θ : ℝ => (f z θ) ^ 2) Work.Spaces.Iθ := by
  have haesm : MeasureTheory.AEStronglyMeasurable (fun θ : ℝ => (f z θ) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    Work.Spaces.aesm_slice_of_continuousOn_Qd (fun p : ℝ × ℝ => (f p.1 p.2) ^ 2)
      (l12q_quad_continuous f hsm) hz
  refine MeasureTheory.Integrable.mono' (hmem.1 z (le_of_lt hz)) haesm ?_
  -- the pointwise bound only fails on the two null endpoints
  have hcongr : MeasureTheory.volume.restrict Work.Spaces.Iθ
      = MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (π / 2)) := by
    rw [Work.Spaces.Iθ]
    exact MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := (0 : ℝ))
        (b := (π / 2))).symm
  rw [hcongr]
  refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
  have hs0 : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hsle : (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) ≤ 1 :=
    Real.rpow_le_one (le_of_lt hs0) hs1 (by have := Work.Spaces.eta_pos; linarith)
  have hspos : 0 < (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) :=
    Real.rpow_pos_of_pos hs0 _
  have hw1 : 1 ≤ Work.Spaces.w z := by
    rw [Work.Spaces.w, one_le_div (by positivity)]
    nlinarith [hz]
  have hkey : 1 ≤ Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) := by
    rw [one_le_div hspos]
    exact le_trans hsle hw1
  have hW2 : 1 ≤ (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2 := by
    have h := mul_le_mul hkey hkey (zero_le_one) (le_trans zero_le_one hkey)
    simpa only [one_mul, pow_two] using h
  have hpt : (f z θ) ^ 2 ≤ (f z θ * (Work.Spaces.w z
      / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
    calc (f z θ) ^ 2 = (f z θ) ^ 2 * 1 := (mul_one _).symm
      _ ≤ (f z θ) ^ 2
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2 :=
          mul_le_mul_of_nonneg_left hW2 (sq_nonneg _)
      _ = (f z θ * (Work.Spaces.w z
            / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := (mul_pow _ _ 2).symm
  calc ‖(f z θ) ^ 2‖ = (f z θ) ^ 2 := Real.norm_of_nonneg (sq_nonneg _)
    _ ≤ (f z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := hpt
    _ = (Work.Spaces.DzIter 0 f z θ * (Work.Spaces.w z
          / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := rfl
    _ ≤ Work.Spaces.HkIntegrand α 4 f z θ :=
        Work.Spaces.sq_le_HkIntegrand_z α 4 f z θ 0 (by norm_num)

/-- **A.e. strong measurability of the Hardy-weighted angular energy in the interior class**
(`SmoothQuad f`): `r ↦ (∫_θ f(r,θ)²)·((1+r)/r)²` on `(0,∞)`.  Replaces the `SmoothNbhd`-based
`Work.FTS.H2.PhiWeightAesm`: `l12q_phi_aesm` gives the angular energy and the Hardy weight
`r ↦ ((1+r)/r)²` is continuous on `(0,∞)`. -/
theorem l12q_aesm (f : ℝ → ℝ → ℝ) (hsm : Work.FTS.LocData.SmoothQuad f) :
    MeasureTheory.AEStronglyMeasurable
      (fun r : ℝ => (∫ θ in Work.Spaces.Iθ, (f r θ) ^ 2) * ((1 + r) / r) ^ 2)
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by
  have hw : MeasureTheory.AEStronglyMeasurable (fun r : ℝ => ((1 + r) / r) ^ 2)
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by
    have h1 : ContinuousOn (fun r : ℝ => ((1 + r) / r) ^ 2) (Set.Ioi (0 : ℝ)) :=
      ((continuousOn_const.add continuousOn_id).div continuousOn_id
        (fun r hr => ne_of_gt (Set.mem_Ioi.mp hr))).pow 2
    exact h1.aestronglyMeasurable measurableSet_Ioi
  exact (l12q_phi_aesm f hsm).mul hw

/-- **The angular Cauchy–Schwarz bound for the `L₁₂` density on one radial slice**, with the
slice-square integrability as an explicit hypothesis (in the interior class it is
`l12q_slice_sq_integrableOn`).  This is `Work.FTS.H2.L12densSlice` with its `SmoothNbhd`
hypothesis replaced by `IntegrableOn (fun θ => (f z θ)²) Iθ`. -/
theorem l12q_l12dens_slice (f : ℝ → ℝ → ℝ) {z : ℝ} (hz : 0 < z)
    (hsl : MeasureTheory.IntegrableOn (fun θ : ℝ => (f z θ) ^ 2) Work.Spaces.Iθ) :
    |Work.Elliptic.L12dens f z|
      ≤ Real.sqrt 3 * Real.sqrt (∫ θ in Work.Spaces.Iθ, (f z θ) ^ 2) / z := by
  have hsq := Work.Coercivity.L12dens_sq_slice f Work.Coercivity.integral_Itheta_K hz hsl
  have hX : 0 ≤ ∫ θ in Work.Spaces.Iθ, (f z θ) ^ 2 :=
    MeasureTheory.setIntegral_nonneg (by rw [Work.Spaces.Iθ]; exact measurableSet_Icc)
      fun θ _ => by positivity
  rw [L12dens_eq_FM_K f z]
  exact abs_le_sqrt_three_mul_sqrt_div hz hX hsq

/-- **The radial Hardy-weight comparison.**  For `HkMem α 4 f` (no smoothness hypothesis),
`∫_{r>0} (∫_θ f(r,θ)²)·((1+r)/r)² ≤ HkSq α 4 f`: the slicewise comparison is
`Work.FTS.H2.L12Q.phiWeight_slice_le`, the majorant `r ↦ ∫_θ HkIntegrand α 4 f r θ` is
integrable on `(0,∞)` by `HkMem`, and `∫_{Iz}` is `∫_{Ioi 0}` (`MeasureTheory.Ioi_ae_eq_Ici`). -/
theorem l12q_phiWeight_le (α : ℝ) (f : ℝ → ℝ → ℝ) (hmem : Work.Spaces.HkMem α 4 f) :
    (∫ r in Set.Ioi (0 : ℝ),
        (∫ θ in Work.Spaces.Iθ, (f r θ) ^ 2) * ((1 + r) / r) ^ 2)
      ≤ Work.Spaces.HkSq α 4 f := by
  have hslice := Work.FTS.H2.L12Q.phiWeight_slice_le α f hmem
  have hK : MeasureTheory.IntegrableOn
      (fun r : ℝ => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f r θ)
      (Set.Ioi (0 : ℝ)) := hmem.2.mono_set Set.Ioi_subset_Ici_self
  have hle : (∫ r in Set.Ioi (0 : ℝ),
        (∫ θ in Work.Spaces.Iθ, (f r θ) ^ 2) * ((1 + r) / r) ^ 2)
      ≤ ∫ r in Set.Ioi (0 : ℝ), ∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α 4 f r θ := by
    refine MeasureTheory.integral_mono_of_nonneg ?_ hK ?_
    · exact Filter.Eventually.of_forall fun r =>
        mul_nonneg (integral_nonneg fun θ => sq_nonneg _) (sq_nonneg _)
    · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with r hr
      exact hslice r hr
  refine le_trans hle ?_
  rw [MeasureTheory.setIntegral_congr_set
    (MeasureTheory.Ioi_ae_eq_Ici (a := (0 : ℝ)))]
  rfl

/-- **Integrability of the Hardy-weighted angular energy.**  From `HkMem α 4 f` and the a.e.
strong measurability `l12q_aesm` of the weighted energy, dominated by the integrable majorant
`r ↦ ∫_θ HkIntegrand α 4 f r θ`. -/
theorem l12q_phiWeight_integrable (α : ℝ) (f : ℝ → ℝ → ℝ)
    (hsm : Work.FTS.LocData.SmoothQuad f) (hmem : Work.Spaces.HkMem α 4 f) :
    MeasureTheory.IntegrableOn
      (fun r : ℝ => (∫ θ in Work.Spaces.Iθ, (f r θ) ^ 2) * ((1 + r) / r) ^ 2)
      (Set.Ioi (0 : ℝ)) := by
  have hslice := Work.FTS.H2.L12Q.phiWeight_slice_le α f hmem
  have hK : MeasureTheory.IntegrableOn
      (fun r : ℝ => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f r θ)
      (Set.Ioi (0 : ℝ)) := hmem.2.mono_set Set.Ioi_subset_Ici_self
  refine hK.mono' (l12q_aesm f hsm) ?_
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with r hr
  rw [Real.norm_of_nonneg (mul_nonneg (integral_nonneg fun θ => sq_nonneg _) (sq_nonneg _))]
  exact hslice r hr

/-- Elgindi's `muestimate` (tex 1516, first line of the proof) in the *interior* class
`Work.FTS.Nonlin.RegQ` of the frozen `Submission/Work/FTS/Vocab.lean`: for
`RegQ α 4 f`, `|L₁₂(f)(0)| ≤ C |f|_{ℋ⁴}`, `C` universal.  This is the design document's
`L12ZeroQ` (§3.3 L-N4.5), the form in which N4 bounds every `L₁₂(piece)(0)`.

`RegQ α 4 f = SmoothQuad f ∧ HkMem α 4 f ∧ BdryTraces α 4 f` replaces `Spaces.SmoothNbhd`
(= analyticity on a neighbourhood of the closed quadrant) in `Work.FTS.H2.L12ZeroLe`, which is
the same statement with `SmoothNbhd`.  The proof is the paper's: `|L₁₂(f)(0)| ≤ C|((z+1)/z)f|_{L²}`
(split the `θ`-integral by Cauchy–Schwarz against `K ∈ L²(Iθ)` and the `r`-integral against
`(1+r)^{-2}`), then `∫∫ f² w ≤ ∫∫ f² w²/sin(2θ)^η ≤ HkSq α 4 f`; slice measurability and
integrability come from `SmoothQuad` and `HkMem` instead of `SmoothNbhd`. -/
theorem L12ZeroQ : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f : Work.FTS.Galerkin.Fn), 0 < α → α ≤ 1 →
    Work.FTS.Nonlin.RegQ α 4 f → |Work.Elliptic.L12 f 0| ≤ C * Work.FTS.Nonlin.Xn α f := by
  refine ⟨3, by norm_num, ?_⟩
  intro α f hα hα1 hreg
  obtain ⟨hsm, hmem, _hbdry⟩ := hreg
  -- the slicewise regularity inputs
  have hslice : ∀ z : ℝ, 0 < z →
      MeasureTheory.IntegrableOn (fun θ : ℝ => (f z θ) ^ 2) Work.Spaces.Iθ :=
    fun z hz => l12q_slice_sq_integrableOn α f hsm hmem hz
  have hdens : ∀ r : ℝ, 0 < r → |Work.Elliptic.L12dens f r|
      ≤ Real.sqrt 3 * Real.sqrt (∫ θ in Work.Spaces.Iθ, (f r θ) ^ 2) / r :=
    fun r hr => l12q_l12dens_slice f hr (hslice r hr)
  -- the radial inputs
  have hPhiw_le := l12q_phiWeight_le α f hmem
  have hPhiw_int := l12q_phiWeight_integrable α f hsm hmem
  have hPhi_aesm := l12q_phi_aesm f hsm
  have hPhi0 : ∀ r : ℝ, 0 ≤ ∫ θ in Work.Spaces.Iθ, (f r θ) ^ 2 := fun r =>
    MeasureTheory.integral_nonneg_of_ae (Filter.Eventually.of_forall fun θ => sq_nonneg _)
  -- abbreviations
  set A : ℝ → ℝ := fun r => Real.sqrt 3 * Real.sqrt (∫ θ in Work.Spaces.Iθ, (f r θ) ^ 2)
      * ((1 + r) / r) with hAdef
  set B : ℝ → ℝ := fun r => 1 / (1 + r) with hBdef
  set μ : MeasureTheory.Measure ℝ := MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)) with hμdef
  -- ## nonnegativity of `A` and `B` a.e.
  have hAe0 : ∀ᵐ r ∂μ, 0 ≤ A r := by
    filter_upwards [MeasureTheory.ae_restrict_mem (μ := MeasureTheory.volume) measurableSet_Ioi]
      with r hr
    rw [hAdef]
    have hr' : (0 : ℝ) < r := Set.mem_Ioi.mp hr
    exact mul_nonneg (mul_nonneg (Real.sqrt_nonneg 3) (Real.sqrt_nonneg _))
      (div_nonneg (by linarith) (le_of_lt hr'))
  have hBe0 : ∀ᵐ r ∂μ, 0 ≤ B r := by
    filter_upwards [MeasureTheory.ae_restrict_mem (μ := MeasureTheory.volume) measurableSet_Ioi]
      with r hr
    rw [hBdef]
    have hr' : (0 : ℝ) < r := Set.mem_Ioi.mp hr
    exact div_nonneg zero_le_one (by linarith)
  -- ## `A` is a.e. strongly measurable
  have hAmeas : MeasureTheory.AEStronglyMeasurable A μ := by
    rw [hμdef, hAdef]
    have h1 : MeasureTheory.AEStronglyMeasurable
        (fun r : ℝ => Real.sqrt (∫ θ in Work.Spaces.Iθ, (f r θ) ^ 2))
        (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
      Real.continuous_sqrt.comp_aestronglyMeasurable hPhi_aesm
    have h2 : MeasureTheory.AEStronglyMeasurable (fun r : ℝ => (1 + r) / r)
        (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
      (ContinuousOn.div (continuousOn_const.add continuousOn_id) continuousOn_id
        (fun r hr => ne_of_gt hr)).aestronglyMeasurable measurableSet_Ioi
    exact (aestronglyMeasurable_const.mul h1).mul h2
  -- ## `A²` is integrable and is the Hardy-weighted angular energy
  have hpt : ∀ r : ℝ,
      A r ^ 2 = 3 * ((∫ θ in Work.Spaces.Iθ, (f r θ) ^ 2) * ((1 + r) / r) ^ 2) := by
    intro r
    rw [hAdef, mul_pow, mul_pow, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num),
      Real.sq_sqrt (hPhi0 r)]
    ring
  have h33 : MeasureTheory.Integrable
      (fun r : ℝ => 3 * ((∫ θ in Work.Spaces.Iθ, (f r θ) ^ 2) * ((1 + r) / r) ^ 2)) μ := by
    rw [hμdef]
    exact hPhiw_int.const_mul 3
  have hAint : MeasureTheory.Integrable (fun r => A r ^ 2) μ := by
    refine h33.congr ?_
    filter_upwards with r
    exact (hpt r).symm
  have hmemA : MeasureTheory.MemLp A 2 μ :=
    (MeasureTheory.memLp_two_iff_integrable_sq hAmeas).mpr hAint
  -- ## `B` is a.e. strongly measurable and `B²` is integrable
  obtain ⟨hB_int, hB_le⟩ := InvOneAddSq
  have hBmeas : MeasureTheory.AEStronglyMeasurable B μ := by
    rw [hμdef, hBdef]
    have h2 : MeasureTheory.AEStronglyMeasurable (fun r : ℝ => 1 / (1 + r))
        (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
      (ContinuousOn.div continuousOn_const (continuousOn_const.add continuousOn_id)
        (fun r hr => by
          have hr' : (0 : ℝ) < r := Set.mem_Ioi.mp hr
          exact ne_of_gt (by show (0 : ℝ) < 1 + r; linarith))).aestronglyMeasurable
        measurableSet_Ioi
    simpa only using h2
  have hBint : MeasureTheory.Integrable (fun r => B r ^ 2) μ := by
    rw [hμdef, hBdef]
    exact hB_int
  have hmemB : MeasureTheory.MemLp B 2 μ :=
    (MeasureTheory.memLp_two_iff_integrable_sq hBmeas).mpr hBint
  -- ## the pointwise bound on the density
  have hbd : ∀ᵐ r ∂μ, |Work.Elliptic.L12dens f r| ≤ A r * B r := by
    filter_upwards [MeasureTheory.ae_restrict_mem (μ := MeasureTheory.volume) measurableSet_Ioi]
      with r hr
    have h5 := hdens r (Set.mem_Ioi.mp hr)
    have hr1 : 1 + r ≠ 0 := by have h := Set.mem_Ioi.mp hr; linarith
    have h5' : |Work.Elliptic.L12dens f r|
        ≤ Real.sqrt 3 * Real.sqrt (∫ θ in Work.Spaces.Iθ, (f r θ) ^ 2) * r⁻¹ := by
      simpa only [div_eq_mul_inv] using h5
    have hkey : ((1 + r) / r) * (1 / (1 + r)) = r⁻¹ := by
      field_simp
    rw [hAdef, hBdef]
    dsimp only
    calc |Work.Elliptic.L12dens f r|
        ≤ Real.sqrt 3 * Real.sqrt (∫ θ in Work.Spaces.Iθ, (f r θ) ^ 2) * r⁻¹ := h5'
      _ = Real.sqrt 3 * Real.sqrt (∫ θ in Work.Spaces.Iθ, (f r θ) ^ 2)
            * (((1 + r) / r) * (1 / (1 + r))) := by rw [hkey]
      _ = Real.sqrt 3 * Real.sqrt (∫ θ in Work.Spaces.Iθ, (f r θ) ^ 2)
            * ((1 + r) / r) * (1 / (1 + r)) := by ring
  -- ## Cauchy–Schwarz in the radial variable
  have hcs := CS1D (μ := μ) (g := fun r => Work.Elliptic.L12dens f r)
    hmemA hmemB hAe0 hBe0 hbd
  -- ## the two `L²` norms
  have hA2le : ∫ r, A r ^ 2 ∂μ ≤ 3 * Work.Spaces.HkSq α 4 f := by
    rw [hμdef]
    have hpt' : ∀ r ∈ Set.Ioi (0 : ℝ),
        A r ^ 2 = 3 * ((∫ θ in Work.Spaces.Iθ, (f r θ) ^ 2) * ((1 + r) / r) ^ 2) :=
      fun r _ => hpt r
    calc ∫ r in Set.Ioi (0 : ℝ), A r ^ 2
        = ∫ r in Set.Ioi (0 : ℝ),
            3 * ((∫ θ in Work.Spaces.Iθ, (f r θ) ^ 2) * ((1 + r) / r) ^ 2) :=
          MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hpt'
      _ = 3 * ∫ r in Set.Ioi (0 : ℝ),
            (∫ θ in Work.Spaces.Iθ, (f r θ) ^ 2) * ((1 + r) / r) ^ 2 :=
          MeasureTheory.integral_const_mul 3 _
      _ ≤ 3 * Work.Spaces.HkSq α 4 f := mul_le_mul_of_nonneg_left hPhiw_le (by norm_num)
  have hB2le : ∫ r, B r ^ 2 ∂μ ≤ 2 := by
    rw [hμdef]
    have hfun : (fun r : ℝ => B r ^ 2) = fun r : ℝ => (1 / (1 + r)) ^ 2 := by
      funext r
      rw [hBdef]
    rw [hfun]
    exact hB_le
  -- ## assembly
  have hfinal : |Work.Elliptic.L12 f 0| ≤ Real.sqrt (3 * Work.Spaces.HkSq α 4 f) * Real.sqrt 2 := by
    have h1 : (∫ r, Work.Elliptic.L12dens f r ∂μ) = Work.Elliptic.L12 f 0 := rfl
    rw [← h1]
    refine hcs.trans ?_
    exact mul_le_mul (Real.sqrt_le_sqrt hA2le) (Real.sqrt_le_sqrt hB2le)
      (Real.sqrt_nonneg (∫ r, B r ^ 2 ∂μ)) (Real.sqrt_nonneg _)
  have hsqrt : Real.sqrt (3 * Work.Spaces.HkSq α 4 f) * Real.sqrt 2
      = Real.sqrt 6 * Work.Spaces.HkNorm α 4 f := by
    rw [Real.sqrt_mul (show (0 : ℝ) ≤ 3 by norm_num) (Work.Spaces.HkSq α 4 f),
      Work.Spaces.HkNorm]
    rw [show Real.sqrt 3 * Real.sqrt (Work.Spaces.HkSq α 4 f) * Real.sqrt 2
        = (Real.sqrt 3 * Real.sqrt 2) * Real.sqrt (Work.Spaces.HkSq α 4 f) from by ring]
    rw [show Real.sqrt 3 * Real.sqrt 2 = Real.sqrt 6 from by
      rw [← Real.sqrt_mul (show (0 : ℝ) ≤ 3 by norm_num) (2 : ℝ)]
      norm_num]
  have h6le : Real.sqrt 6 ≤ 3 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 6 by norm_num), Real.sqrt_nonneg 6]
  calc |Work.Elliptic.L12 f 0|
      ≤ Real.sqrt (3 * Work.Spaces.HkSq α 4 f) * Real.sqrt 2 := hfinal
    _ = Real.sqrt 6 * Work.Spaces.HkNorm α 4 f := hsqrt
    _ ≤ 3 * Work.Spaces.HkNorm α 4 f :=
        mul_le_mul_of_nonneg_right h6le (Work.Spaces.HkNorm_nonneg α 4 f)
    _ = 3 * Work.FTS.Nonlin.Xn α f := rfl

end Work.FTS.H2
