import Mathlib
import Submission.Work.BourgainPlan.Maximal.annulusDiffSqfunL2Gain
import Submission.Work.BourgainPlan.Maximal.aeIntegrableMulSubOfMemLp
import Submission.Commons.Analysis.Convolution.eLpNorm_convolution_le_complex

namespace Work.BourgainPlan.Maximal

open MeasureTheory Filter
open scoped ENNReal Topology

noncomputable section

/-! ## The a.e. well-definedness, `Lp`-membership and linearity of `x ↦ ∫ y, K (x - y) * f y` -/

/-- The convolution integral `x ↦ ∫ y, K (x - y) * f y` of `f` against the kernel `K`. -/
def lpConv (K : ℝ → ℂ) (f : ℝ → ℂ) : ℝ → ℂ := fun x => ∫ y, K (x - y) * f y

/-- `lpConv K` only depends on the a.e. class of `f` (in fact pointwise). -/
lemma lpConv_congr {K f f' : ℝ → ℂ} (h : f =ᵐ[(volume : Measure ℝ)] f') :
    lpConv K f = lpConv K f' := by
  funext x
  exact integral_congr_ae (h.mono fun y hy => by simp only [hy])

/-- `lpConv K f` is a.e. strongly measurable for a.e. strongly measurable `K`, `f`. -/
lemma aestronglyMeasurable_lpConv {K f : ℝ → ℂ}
    (hK : AEStronglyMeasurable K (volume : Measure ℝ))
    (hf : AEStronglyMeasurable f (volume : Measure ℝ)) :
    AEStronglyMeasurable (lpConv K f) (volume : Measure ℝ) := by
  have hjoint : AEStronglyMeasurable (fun z : ℝ × ℝ => K (z.1 - z.2) * f z.2)
      ((volume : Measure ℝ).prod (volume : Measure ℝ)) :=
    (hK.comp_quasiMeasurePreserving
      (quasiMeasurePreserving_sub_of_right_invariant volume volume)).mul hf.comp_snd
  have hres : AEStronglyMeasurable (fun x : ℝ => ∫ y : ℝ, K (x - y) * f y)
      (volume : Measure ℝ) := hjoint.integral_prod_right'
  exact hres

/-- **Young's inequality**: for `K ∈ L¹` and `f ∈ Lᵖ` (`p ≥ 1`), the convolution `lpConv K f`
belongs to `Lᵖ`. -/
lemma memLp_lpConv {K : ℝ → ℂ} (hK : Integrable K volume) {p : ℝ} (hp : 1 ≤ p) {f : ℝ → ℂ}
    (hf : MemLp f (ENNReal.ofReal p) volume) :
    MemLp (lpConv K f) (ENNReal.ofReal p) volume := by
  have hK1 : MemLp K 1 volume := memLp_one_iff_integrable.mpr hK
  rw [memLp_iff]
  calc eLpNorm (lpConv K f) (ENNReal.ofReal p) volume
      ≤ eLpNorm K 1 volume * eLpNorm f (ENNReal.ofReal p) volume :=
        Commons.Analysis.Convolution.eLpNorm_convolution_le_complex K f p hp hK1 hf
    _ < ⊤ := ENNReal.mul_lt_top hK1.eLpNorm_lt_top hf.eLpNorm_lt_top

/-- Additivity of the convolution integral, almost everywhere. -/
lemma lpConv_add_ae {K : ℝ → ℂ} (hK : Integrable K volume) {p : ℝ} (hp : 1 ≤ p) {f g : ℝ → ℂ}
    (hf : MemLp f (ENNReal.ofReal p) volume) (hg : MemLp g (ENNReal.ofReal p) volume) :
    lpConv K (f + g) =ᵐ[volume] lpConv K f + lpConv K g := by
  have hK1 : MemLp K 1 volume := memLp_one_iff_integrable.mpr hK
  have h1 := aeIntegrableMulSubOfMemLp hp hK1 hf
  have h2 := aeIntegrableMulSubOfMemLp hp hK1 hg
  filter_upwards [h1, h2] with x hx1 hx2
  have hpt : (fun y : ℝ => K (x - y) * (f y + g y))
      = fun y : ℝ => K (x - y) * f y + K (x - y) * g y := by
    funext y; ring
  simp only [lpConv, Pi.add_apply]
  rw [hpt, integral_add hx1 hx2]

/-- Homogeneity of the convolution integral, almost everywhere. -/
lemma lpConv_smul_ae {K : ℝ → ℂ} (hK : Integrable K volume) {p : ℝ} (hp : 1 ≤ p) (c : ℂ)
    {f : ℝ → ℂ} (hf : MemLp f (ENNReal.ofReal p) volume) :
    lpConv K (fun y => c * f y) =ᵐ[volume] fun x => c * lpConv K f x := by
  have hK1 : MemLp K 1 volume := memLp_one_iff_integrable.mpr hK
  have h1 := aeIntegrableMulSubOfMemLp hp hK1 hf
  filter_upwards [h1] with x _
  have hpt : (fun y : ℝ => K (x - y) * (c * f y))
      = fun y : ℝ => c • (K (x - y) * f y) := by
    funext y; simp only [smul_eq_mul]; ring
  simp only [lpConv]
  rw [hpt, integral_smul, smul_eq_mul]

/-- The `ℂ`-linear map on `Lᵖ` realizing the convolution with the `L¹`-kernel `K`. -/
noncomputable def lpConvLinearMap {K : ℝ → ℂ} (hK : Integrable K (volume : Measure ℝ))
    {p : ℝ} (hp : 1 ≤ p) :
    Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ) →ₗ[ℂ]
      Lp ℂ (ENNReal.ofReal p) (volume : Measure ℝ) where
  toFun g := (memLp_lpConv hK hp (Lp.memLp g)).toLp (lpConv K (g : ℝ → ℂ))
  map_add' f g := by
    have hconv : lpConv K ((f + g : Lp ℂ (ENNReal.ofReal p) volume) : ℝ → ℂ)
        =ᵐ[volume] lpConv K (f : ℝ → ℂ) + lpConv K (g : ℝ → ℂ) :=
      (Filter.EventuallyEq.of_eq (lpConv_congr (Lp.coeFn_add f g))).trans
        (lpConv_add_ae hK hp (Lp.memLp f) (Lp.memLp g))
    refine Lp.ext ?_
    filter_upwards [hconv,
      MemLp.coeFn_toLp (memLp_lpConv hK hp (Lp.memLp (f + g))),
      MemLp.coeFn_toLp (memLp_lpConv hK hp (Lp.memLp f)),
      MemLp.coeFn_toLp (memLp_lpConv hK hp (Lp.memLp g)),
      Lp.coeFn_add
        (MemLp.toLp (lpConv K (f : ℝ → ℂ)) (memLp_lpConv hK hp (Lp.memLp f)))
        (MemLp.toLp (lpConv K (g : ℝ → ℂ)) (memLp_lpConv hK hp (Lp.memLp g)))]
      with x hx0 hx1 hx2 hx3 hx4
    simp only [Pi.add_apply] at hx4
    rw [hx1, hx4, hx2, hx3]
    exact hx0
  map_smul' c f := by
    have hcoe : ((c • f : Lp ℂ (ENNReal.ofReal p) volume) : ℝ → ℂ)
        =ᵐ[volume] fun y => c * (f : ℝ → ℂ) y :=
      (Lp.coeFn_smul c f).mono fun y hy => by simpa using hy
    have hconv : lpConv K ((c • f : Lp ℂ (ENNReal.ofReal p) volume) : ℝ → ℂ)
        =ᵐ[volume] fun x => c * lpConv K (f : ℝ → ℂ) x :=
      (Filter.EventuallyEq.of_eq (lpConv_congr hcoe)).trans
        (lpConv_smul_ae hK hp c (Lp.memLp f))
    refine Lp.ext ?_
    filter_upwards [hconv,
      MemLp.coeFn_toLp (memLp_lpConv hK hp (Lp.memLp (c • f))),
      MemLp.coeFn_toLp (memLp_lpConv hK hp (Lp.memLp f)),
      Lp.coeFn_smul c (MemLp.toLp (lpConv K (f : ℝ → ℂ)) (memLp_lpConv hK hp (Lp.memLp f)))]
      with x hx0 hx1 hx2 hx3
    simp only [Pi.smul_apply] at hx3
    simp only [RingHom.id_apply]
    rw [hx1, hx3, hx2]
    exact hx0

end

/-- **Convolution with an `L¹` kernel is an `Lp`-linear operator** (`1 ≤ p`): Young's inequality
gives `‖K * g‖_{Lp} ≤ ‖K‖_{L¹}‖g‖_{Lp}`, the convolution depends only on the a.e. class of `g`, and
it is additive, so it packages as a `ℂ`-linear map on `Lp ℂ (ofReal p)` realizing the convolution.

Mathlib has no `Lp` convolution API (`MeasureTheory.convolution` is defined on raw functions via a
`ContinuousLinearMap`, and `MeasureTheory.Measure.conv` is convolution of *measures*), so this is the
missing brick.  Together with `Work.BourgainPlan.Maximal.mzSquareFunctionLpDomain` it lets the
Marcinkiewicz–Zygmund square-function estimate be applied to the annulus convolutions and to the
Littlewood–Paley multipliers of MST §6.1 — neither of which is pointwise linear, so
`mz_square_function` cannot be used directly.

Suggested route: `MemLp` of `K * g` from the `ℝ≥0∞`-form Young inequality (the corpus already has
`lintegral_convolution_rpow_le_lin`, private in
`Commons/Analysis/Fourier/multiplier_eq_convolution_ae.lean`; a local copy is fine), then
`MemLp.toLp`, then `Lp.ext` plus `Lp.coeFn_add`/`Lp.coeFn_smul` and `MeasureTheory.integral_add`/
`integral_smul` for the linearity axioms, and `Filter.EventuallyEq`/Fubini for the well-definedness
on classes.  (The norm bound `‖T g‖ ≤ ‖K‖₁‖g‖` is not part of the statement: the consumers take the
`→ₗ[ℂ]` map and the `Lp` bound as a separate hypothesis.) -/
theorem convolutionLpLinear {K : ℝ → ℂ}
    (hK : MeasureTheory.Integrable K (MeasureTheory.volume : MeasureTheory.Measure ℝ))
    {p : ℝ} (hp : 1 ≤ p) :
    ∃ T : MeasureTheory.Lp ℂ (ENNReal.ofReal p) (MeasureTheory.volume : MeasureTheory.Measure ℝ)
        →ₗ[ℂ] MeasureTheory.Lp ℂ (ENNReal.ofReal p) (MeasureTheory.volume : MeasureTheory.Measure ℝ),
      ∀ g : MeasureTheory.Lp ℂ (ENNReal.ofReal p) (MeasureTheory.volume : MeasureTheory.Measure ℝ),
        (T g : ℝ → ℂ) =ᵐ[MeasureTheory.volume]
          fun x => ∫ y : ℝ, K (x - y) * (g : ℝ → ℂ) y := by
  refine ⟨lpConvLinearMap hK hp, fun g => ?_⟩
  show ((memLp_lpConv hK hp (Lp.memLp g)).toLp (lpConv K (g : ℝ → ℂ)) : ℝ → ℂ)
      =ᵐ[(volume : Measure ℝ)] fun x => ∫ y : ℝ, K (x - y) * (g : ℝ → ℂ) y
  exact MemLp.coeFn_toLp (memLp_lpConv hK hp (Lp.memLp g))

end Work.BourgainPlan.Maximal
