import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.H2.T1EasyBound
import Submission.Work.FTS.H2.HQ.Glue
import Submission.Work.FTS.H2.HQ.HardyZQ
import Submission.Work.FTS.H2.T1Q.Basic
import Submission.Work.H2.T1Q.SlotOpen
import Submission.Work.H2.T1Q.SlotPtQ

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

open Work.Spaces

namespace Work.H2.T1Q

set_option autoImplicit false
set_option maxHeartbeats 4000000

/-! ## Two elementary facts on the angular interval -/

/-- A point of `Iθ` at which `sin(2θ)` does not vanish is interior. -/
private theorem mem_Ioo_of_mem_Iθ_of_sin_ne {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ)
    (hne : Real.sin (2 * θ) ≠ 0) : θ ∈ Set.Ioo 0 (π / 2) := by
  rw [Work.Spaces.Iθ, Set.mem_Icc] at hθ
  refine ⟨?_, ?_⟩
  · rcases eq_or_lt_of_le hθ.1 with h | h
    · exact absurd (by rw [← h]; simp) hne
    · exact h
  · rcases eq_or_lt_of_le hθ.2 with h | h
    · exact absurd (by rw [h, show 2 * (π / 2) = π by ring, Real.sin_pi]) hne
    · exact h

/-- `supAbsThO` is nonnegative whenever the slice is bounded. -/
private theorem supAbsThO_nonneg_aux {u : ℝ → ℝ → ℝ} {z : ℝ}
    (hb : BddAbove {y : ℝ | ∃ θ ∈ Set.Ioo 0 (π / 2), y = |u z θ|}) :
    0 ≤ Work.FTS.H2.supAbsThO u z :=
  le_trans (abs_nonneg _) (Work.FTS.H2.abs_le_supAbsThO
    (show (π / 4 : ℝ) ∈ Set.Ioo 0 (π / 2) by
      constructor <;> linarith [Real.pi_pos]) hb)

/-- **The `f`-domination of the exceptional summand.**  For `SmoothQuad f` and `HkMem α 4 f` with
`0 < α ≤ 1`, the slice `θ ↦ D_z³f z θ` is bounded at every `z ∈ Iz` (so that `supAbsThO` is the
honest supremum of the open angular slice), whence

`(D_z³f z θ)² w(z)² ≤ (supAbsThO (D_z³f) z · w z)²`

for every `z ∈ Iz` and every `θ ∈ (0,π/2)`. -/
private theorem exc_fdom_qd (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (f : ℝ → ℝ → ℝ)
    (hf : Work.FTS.LocData.SmoothQuad f) (hmemf : HkMem α 4 f) :
    ∀ z ∈ Iz, ∀ θ ∈ Set.Ioo 0 (π / 2),
      (DzIter 3 f z θ) ^ 2 * (w z) ^ 2
        ≤ (Work.FTS.H2.supAbsThO (DzIter 3 f) z * w z) ^ 2 := by
  intro z hz θ hθ
  obtain ⟨S, _hS0, hS⟩ := Work.H2.T1Q.sup_DzIter_three_le α hα hα1 f hf hmemf z hz
  have hb : BddAbove {y : ℝ | ∃ θ ∈ Set.Ioo 0 (π / 2), y = |DzIter 3 f z θ|} :=
    ⟨S, by rintro y ⟨θ', hθ', rfl⟩; exact hS θ' hθ'.1 hθ'.2⟩
  have h1 : |DzIter 3 f z θ| ≤ Work.FTS.H2.supAbsThO (DzIter 3 f) z :=
    Work.FTS.H2.abs_le_supAbsThO hθ hb
  have h2 : 0 ≤ w z := by
    rw [w]
    exact div_nonneg (sq_nonneg _) (sq_nonneg _)
  have h3 : |DzIter 3 f z θ| * w z
      ≤ Work.FTS.H2.supAbsThO (DzIter 3 f) z * w z :=
    mul_le_mul_of_nonneg_right h1 h2
  have h4 : 0 ≤ |DzIter 3 f z θ| * w z := mul_nonneg (abs_nonneg _) h2
  have h5 : (|DzIter 3 f z θ| * w z) ^ 2
      ≤ (Work.FTS.H2.supAbsThO (DzIter 3 f) z * w z) ^ 2 := by
    rw [pow_two, pow_two]
    exact mul_le_mul h3 h3 h4 (mul_nonneg (supAbsThO_nonneg_aux hb) h2)
  calc (DzIter 3 f z θ) ^ 2 * (w z) ^ 2
      = (|DzIter 3 f z θ| * w z) ^ 2 := by rw [mul_pow, sq_abs]
    _ ≤ _ := h5

/-- **The `g`-domination of the exceptional summand** (the interior radial Hardy inequality
`Work.FTS.H2.HQ.HardyZQ` applied to the `θ`-slice of `mixed 0 2 g = D_θ²g`, whose `z`-derivative
is the slot `mixed 1 2 g`): for a.e. angle and every `z ∈ Iz`,

`(D_θ²g z θ)² sin(2θ)^{-γ} ≤ ∫_{Iz} (mixed 1 2 g z' θ · Wt α z' θ)² dz'`. -/
private theorem exc_gdom_qd (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (g : ℝ → ℝ → ℝ)
    (hg : Work.FTS.LocData.SmoothQuad g) (hdecg : DecayAll 4 g)
    (hint : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      (mixed 1 2 g p.1 p.2 * Wt α p.1 p.2) ^ 2) Work.FTS.H2.pm) :
    ∀ᵐ θ ∂(MeasureTheory.volume.restrict Iθ), ∀ z ∈ Iz,
      (mixed 0 2 g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(gam α))
        ≤ ∫ z' in Iz, (mixed 1 2 g z' θ * Wt α z' θ) ^ 2 := by
  have hsliceae : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Iθ),
      MeasureTheory.Integrable (fun z => (mixed 1 2 g z θ * Wt α z θ) ^ 2)
        (MeasureTheory.volume.restrict Iz) := hint.prod_left_ae
  filter_upwards [hsliceae, MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hintθ hθ
  intro z hz
  by_cases hzero : Real.sin (2 * θ) = 0
  · have hΦ : mixed 0 2 g z θ = 0 := by
      show Real.sin (2 * θ) * pth (DthIter 1 g) z θ = 0
      rw [hzero, zero_mul]
    rw [hΦ]
    simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul]
    exact integral_nonneg fun z' => sq_nonneg _
  · have hsinpos : 0 < Real.sin (2 * θ) :=
      lt_of_le_of_ne (bt_sin_nonneg hθ) (Ne.symm hzero)
    have hθi : θ ∈ Set.Ioo 0 (π / 2) := mem_Ioo_of_mem_Iθ_of_sin_ne hθ hzero
    set c : ℝ := (Real.sin (2 * θ)) ^ (-(gam α)) with hcdef
    have hcpos : 0 < c := Real.rpow_pos_of_pos hsinpos _
    have hpoint : ∀ s : ℝ, (mixed 1 2 g s θ * Wt α s θ) ^ 2
        = c * ((mixed 1 2 g s θ) ^ 2 * (w s) ^ 2) := by
      intro s
      rw [mul_pow, Work.FTS.H2.HQ.Wt_sq_quad α s θ hθi, hcdef]
      ring
    have hint' : MeasureTheory.IntegrableOn
        (fun s => (mixed 1 2 g s θ) ^ 2 * (w s) ^ 2) Iz := by
      have h1 := hintθ.const_mul c⁻¹
      refine h1.congr ?_
      filter_upwards with s
      rw [hpoint s]
      field_simp
    have hRHS : (∫ z' in Iz, (mixed 1 2 g z' θ * Wt α z' θ) ^ 2)
        = c * ∫ s in Iz, (mixed 1 2 g s θ) ^ 2 * (w s) ^ 2 := by
      rw [← MeasureTheory.integral_const_mul]
      refine MeasureTheory.integral_congr_ae (Eventually.of_forall fun s => ?_)
      exact hpoint s
    have hH := Work.H2.T1Q.hardyZQ_mixed_slice g hg hdecg 0 2 (by norm_num) hθi hint'
    rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
    · subst hz0
      have hcont : ContinuousAt (fun z' => (mixed 0 2 g z' θ) ^ 2) 0 :=
        ((((hg.mixed 0 2).curry_z hθi).continuousOn.continuousAt
          (isOpen_Ioi.mem_nhds (by norm_num : (-1 : ℝ) < 0)))).pow 2
      have hev : ∀ᶠ z' in nhdsWithin (0 : ℝ) (Set.Ioi 0),
          (mixed 0 2 g z' θ) ^ 2 * c
            ≤ ∫ z' in Iz, (mixed 1 2 g z' θ * Wt α z' θ) ^ 2 := by
        filter_upwards [self_mem_nhdsWithin] with z' hz'
        rw [hRHS]
        calc (mixed 0 2 g z' θ) ^ 2 * c = c * (mixed 0 2 g z' θ) ^ 2 := by ring
          _ ≤ c * ∫ s in Iz, (mixed 1 2 g s θ) ^ 2 * (w s) ^ 2 :=
              mul_le_mul_of_nonneg_left (hH z' hz') hcpos.le
      have hl : Filter.Tendsto (fun z' => (mixed 0 2 g z' θ) ^ 2 * c)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds ((mixed 0 2 g 0 θ) ^ 2 * c)) :=
        (hcont.tendsto.mono_left nhdsWithin_le_nhds).mul_const c
      exact le_of_tendsto hl hev
    · rw [hRHS]
      calc (mixed 0 2 g z θ) ^ 2 * c = c * (mixed 0 2 g z θ) ^ 2 := by ring
        _ ≤ c * ∫ s in Iz, (mixed 1 2 g s θ) ^ 2 * (w s) ^ 2 :=
            mul_le_mul_of_nonneg_left (hH z hzpos) hcpos.le

/-! ## The exceptional summand of `T1Easy` in the interior class -/

/-- **The exceptional summand of the interior `T1Easy` estimate.**  For `0 < α ≤ 1`, `SmoothQuad`
data `f`, `g` with `DecayAll 4` and `HkMem α 4`, and an `L²`-bound `K3` for the angular supremum
of `D_z³f·w`, the single Leibniz summand `D_z³f · D_θ²g · D_z³ D_θ g · Wm²` — the only one in
which the `f`-factor carries three `D_z`-derivatives — is integrable on the product measure `pm`
with integral at most `√K3 · |g|²_{ℋ⁴}`, in both the product-measure and the iterated form.

Route: copy `Work.FTS.H2.T1ExcBoundAux` of `Submission/Work/FTS/H2/T1EasyBound.lean`, replacing
`Spaces.SmoothNbhd` by `Work.FTS.LocData.SmoothQuad`, `supAbsTh` by `Work.FTS.H2.supAbsThO`
(the interior angular supremum, `Submission/Work/FTS/H2/T1Q/Basic.lean`), `Spaces.HardyZ` by
`Work.FTS.H2.HQ.HardyZQ` (the interior radial Hardy inequality for the `θ`-slice of
`mixed 0 2 g`, whose `z`-derivative is the slot `mixed 1 2 g`), `Spaces.bt_prod_integrable` by
`Work.FTS.H2.HQ.bt_prod_integrable_quad`, and the measurability helpers by
`Work.H2.T1Q.aesm_prod_three_qd`; Cauchy–Schwarz on `pm` is `Work.FTS.H2.cs_pm_of_nonneg` /
`Work.FTS.H2.memLp_abs_pm`.

One extra ingredient is needed: the *honesty* of `supAbsThO (D_z³ f) z` at every `z ∈ Iz`
(an unbounded slice would make `supAbsThO` the junk value `0`).  It is supplied by
`Work.H2.T1Q.sup_DzIter_three_le` (in `Submission/Work/H2/T1Q/SlotPtQ.lean`): for
`SmoothQuad f` and `HkMem α 4 f` with `0 < α ≤ 1` the slice `θ ↦ D_z³ f z θ` is *bounded* at
every `z ∈ Iz`, which gives the required `BddAbove` and hence
`(D_z³f z θ)² w(z)² ≤ (supAbsThO (D_z³f) z · w z)²` (`Work.FTS.H2.abs_le_supAbsThO`), as in the
template's `exc_fdom`. -/
theorem ExcBoundQ (α : ℝ) (f g : ℝ → ℝ → ℝ) (K3 : ℝ)
    (hα : 0 < α) (hα1 : α ≤ 1) (hf : Work.FTS.LocData.SmoothQuad f)
    (hg : Work.FTS.LocData.SmoothQuad g)
    (hdecf : Work.Spaces.DecayAll 4 f) (hdecg : Work.Spaces.DecayAll 4 g)
    (hmemf : Work.Spaces.HkMem α 4 f) (hmemg : Work.Spaces.HkMem α 4 g)
    (hGint : MeasureTheory.IntegrableOn
      (fun z => (Work.FTS.H2.supAbsThO (Work.Spaces.DzIter 3 f) z * Work.Spaces.w z) ^ 2)
      Work.Spaces.Iz)
    (hGle : (∫ z in Work.Spaces.Iz,
      (Work.FTS.H2.supAbsThO (Work.Spaces.DzIter 3 f) z * Work.Spaces.w z) ^ 2) ≤ K3)
    (hK3 : 0 ≤ K3) :
    (MeasureTheory.Integrable (fun p : ℝ × ℝ =>
        |Work.Spaces.DzIter 3 f p.1 p.2 * Work.Spaces.mixed 0 2 g p.1 p.2
          * Work.Spaces.mixed 3 1 g p.1 p.2 * (Work.FTS.H2.Wm α p.1 p.2) ^ 2|)
        Work.FTS.H2.pm ∧
      ∫ p, |Work.Spaces.DzIter 3 f p.1 p.2 * Work.Spaces.mixed 0 2 g p.1 p.2
          * Work.Spaces.mixed 3 1 g p.1 p.2 * (Work.FTS.H2.Wm α p.1 p.2) ^ 2| ∂Work.FTS.H2.pm
        ≤ Real.sqrt K3 * Work.Spaces.HkSq α 4 g) ∧
    (MeasureTheory.IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ,
        |Work.Spaces.DzIter 3 f z θ * Work.Spaces.mixed 0 2 g z θ
          * Work.Spaces.mixed 3 1 g z θ * (Work.FTS.H2.Wm α z θ) ^ 2|) Work.Spaces.Iz ∧
      ∫ z in Work.Spaces.Iz, (∫ θ in Work.Spaces.Iθ,
        |Work.Spaces.DzIter 3 f z θ * Work.Spaces.mixed 0 2 g z θ
          * Work.Spaces.mixed 3 1 g z θ * (Work.FTS.H2.Wm α z θ) ^ 2|)
        ≤ Real.sqrt K3 * Work.Spaces.HkSq α 4 g) := by
  have hpm : Work.FTS.H2.pm
      = (MeasureTheory.volume.restrict Iz).prod (MeasureTheory.volume.restrict Iθ) := rfl
  -- the two `ℋ⁴`-slots of `g`
  obtain ⟨hY_int, hY_val⟩ :=
    Work.FTS.H2.HQ.bt_prod_integrable_quad α g hg hmemg 3 1 (by norm_num) (by norm_num)
  obtain ⟨hV_int, hV_val⟩ :=
    Work.FTS.H2.HQ.bt_prod_integrable_quad α g hg hmemg 1 2 (by norm_num) (by norm_num)
  -- the `θ`-dominating function `Gb` of the `g`-factor
  have hGb_int : MeasureTheory.Integrable
      (fun θ => ∫ z' in Iz, (mixed 1 2 g z' θ * Wt α z' θ) ^ 2)
      (MeasureTheory.volume.restrict Iθ) := hV_int.integral_prod_right
  have hGb_le : ∫ θ in Iθ, (∫ z' in Iz, (mixed 1 2 g z' θ * Wt α z' θ) ^ 2)
      ≤ HkSq α 4 g := by
    have h1 : ∫ θ in Iθ, (∫ z' in Iz, (mixed 1 2 g z' θ * Wt α z' θ) ^ 2)
        = ∫ p, (mixed 1 2 g p.1 p.2 * Wt α p.1 p.2) ^ 2 ∂Work.FTS.H2.pm := by
      rw [hpm]
      rw [← MeasureTheory.integral_integral_swap
        (μ := MeasureTheory.volume.restrict Iz)
        (ν := MeasureTheory.volume.restrict Iθ)
        (f := fun z θ => (mixed 1 2 g z θ * Wt α z θ) ^ 2) hV_int]
      exact MeasureTheory.integral_integral hV_int
    rw [h1]
    rw [hpm]
    rw [hV_val]
    exact L2Sq_mixed_le_HkSq α 4 g hmemg 2 1 (by norm_num) (by norm_num)
  have hYsq_le : ∫ p, (mixed 3 1 g p.1 p.2 * Wt α p.1 p.2) ^ 2 ∂Work.FTS.H2.pm
      ≤ HkSq α 4 g := by
    rw [hpm]
    rw [hY_val]
    exact L2Sq_mixed_le_HkSq α 4 g hmemg 1 3 (by norm_num) (by norm_num)
  -- the `g`-domination
  have hgdom := exc_gdom_qd α hα hα1 g hg hdecg hV_int
  -- strong measurability of the two Cauchy–Schwarz factors
  have hXaesm : AEStronglyMeasurable
      (fun p : ℝ × ℝ => DzIter 3 f p.1 p.2 * mixed 0 2 g p.1 p.2
        * Wt α p.1 p.2) Work.FTS.H2.pm :=
    Work.FTS.H2.aesm_of_Qd ((((Work.FTS.LocData.contDiffOn_DzIter Work.Spaces.isOpen_quadU hf 3).continuousOn.mono
      Work.FTS.H2.HQ.quadQ_subset_quadU).mul
      ((Work.FTS.LocData.contDiffOn_DthIter Work.Spaces.isOpen_quadU hg 2).continuousOn.mono
        Work.FTS.H2.HQ.quadQ_subset_quadU)).mul
        (Work.FTS.H2.HQ.continuousOn_Wt_quad α))
  have hYaesm : AEStronglyMeasurable
      (fun p : ℝ × ℝ => mixed 3 1 g p.1 p.2 * Wt α p.1 p.2) Work.FTS.H2.pm :=
    Work.FTS.H2.aesm_of_Qd (((Work.FTS.LocData.contDiffOn_mixed Work.Spaces.isOpen_quadU hg 3 1).continuousOn.mono
      Work.FTS.H2.HQ.quadQ_subset_quadU).mul (Work.FTS.H2.HQ.continuousOn_Wt_quad α))
  -- the squared `θ`-weight identity
  have hXpoint : ∀ (z θ : ℝ), θ ∈ Set.Ioo 0 (π / 2) →
      (DzIter 3 f z θ * mixed 0 2 g z θ * Wt α z θ) ^ 2
        = (DzIter 3 f z θ) ^ 2 * (w z) ^ 2
          * ((mixed 0 2 g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(gam α))) := by
    intro z θ hθ
    rw [mul_pow, mul_pow, Work.FTS.H2.HQ.Wt_sq_quad α z θ hθ]
    ring
  -- the `θ`-integral bound for each `z ∈ Iz`
  have hXsq_theta : ∀ z ∈ Iz,
      ∫ θ in Iθ, (DzIter 3 f z θ * mixed 0 2 g z θ * Wt α z θ) ^ 2
        ≤ (Work.FTS.H2.supAbsThO (DzIter 3 f) z * w z) ^ 2
          * ∫ θ in Iθ, (∫ z' in Iz, (mixed 1 2 g z' θ * Wt α z' θ) ^ 2) := by
    intro z hz
    have hmono : ∫ θ in Iθ, (DzIter 3 f z θ * mixed 0 2 g z θ * Wt α z θ) ^ 2
        ≤ ∫ θ in Iθ, (Work.FTS.H2.supAbsThO (DzIter 3 f) z * w z) ^ 2
            * (∫ z' in Iz, (mixed 1 2 g z' θ * Wt α z' θ) ^ 2) := by
      refine integral_mono_of_nonneg (Eventually.of_forall fun θ => sq_nonneg _)
        (hGb_int.const_mul _) ?_
      filter_upwards [hgdom, ae_Iθ_mem_Ioo'] with θ hgd hθi
      rw [hXpoint z θ hθi]
      refine mul_le_mul (exc_fdom_qd α hα hα1 f hf hmemf z hz θ hθi) (hgd z hz) ?_ (sq_nonneg _)
      exact mul_nonneg (sq_nonneg _)
        (Real.rpow_nonneg (bt_sin_nonneg ⟨le_of_lt hθi.1, le_of_lt hθi.2⟩) _)
    rw [integral_const_mul] at hmono
    exact hmono
  -- the slice integrability and the Fubini identity for `X²`
  have hXsq_slice : ∀ᵐ z ∂(MeasureTheory.volume.restrict Iz),
      MeasureTheory.Integrable
        (fun θ => (DzIter 3 f z θ * mixed 0 2 g z θ * Wt α z θ) ^ 2)
        (MeasureTheory.volume.restrict Iθ) := by
    filter_upwards [hXaesm.prodMk_left, MeasureTheory.ae_restrict_mem measurableSet_Ici]
      with z hzmeas hz
    refine MeasureTheory.Integrable.mono'
      (hGb_int.const_mul ((Work.FTS.H2.supAbsThO (DzIter 3 f) z * w z) ^ 2))
      (hzmeas.pow 2) ?_
    filter_upwards [hgdom, ae_Iθ_mem_Ioo'] with θ hgd hθi
    rw [Real.norm_of_nonneg (sq_nonneg _), hXpoint z θ hθi]
    refine mul_le_mul (exc_fdom_qd α hα hα1 f hf hmemf z hz θ hθi) (hgd z hz) ?_ (sq_nonneg _)
    exact mul_nonneg (sq_nonneg _)
      (Real.rpow_nonneg (bt_sin_nonneg ⟨le_of_lt hθi.1, le_of_lt hθi.2⟩) _)
  have hXsq_outer : MeasureTheory.Integrable
      (fun z => ∫ θ in Iθ, (DzIter 3 f z θ * mixed 0 2 g z θ * Wt α z θ) ^ 2)
      (MeasureTheory.volume.restrict Iz) := by
    refine MeasureTheory.Integrable.mono'
      (hGint.mul_const (∫ θ in Iθ, (∫ z' in Iz, (mixed 1 2 g z' θ * Wt α z' θ) ^ 2)))
      ((hXaesm.pow 2).integral_prod_right') ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
    rw [Real.norm_of_nonneg (integral_nonneg fun θ => sq_nonneg _)]
    exact hXsq_theta z hz
  obtain ⟨hX_int, hX_val⟩ := Work.Spaces.integrable_prod_of_iterated
    (G := fun z θ => (DzIter 3 f z θ * mixed 0 2 g z θ * Wt α z θ) ^ 2)
    (fun z θ => sq_nonneg _) (hXaesm.pow 2) hXsq_slice hXsq_outer
  have hX_le : ∫ p, (DzIter 3 f p.1 p.2 * mixed 0 2 g p.1 p.2
        * Wt α p.1 p.2) ^ 2 ∂Work.FTS.H2.pm ≤ K3 * HkSq α 4 g := by
    rw [hpm]
    rw [hX_val]
    calc ∫ z in Iz, (∫ θ in Iθ,
            (DzIter 3 f z θ * mixed 0 2 g z θ * Wt α z θ) ^ 2)
        ≤ ∫ z in Iz, (Work.FTS.H2.supAbsThO (DzIter 3 f) z * w z) ^ 2
            * (∫ θ in Iθ, (∫ z' in Iz, (mixed 1 2 g z' θ * Wt α z' θ) ^ 2)) := by
          refine integral_mono_of_nonneg
            (Eventually.of_forall fun z => integral_nonneg fun θ => sq_nonneg _)
            (hGint.mul_const _) ?_
          exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici
            (fun z hz => hXsq_theta z hz)
      _ = (∫ z in Iz, (Work.FTS.H2.supAbsThO (DzIter 3 f) z * w z) ^ 2)
            * (∫ θ in Iθ, (∫ z' in Iz, (mixed 1 2 g z' θ * Wt α z' θ) ^ 2)) :=
          integral_mul_const _ _
      _ ≤ K3 * HkSq α 4 g :=
          mul_le_mul hGle hGb_le (integral_nonneg fun θ => integral_nonneg fun z' => sq_nonneg _)
            hK3
  -- Cauchy–Schwarz
  have hX_memLp : MemLp (fun p : ℝ × ℝ => DzIter 3 f p.1 p.2 * mixed 0 2 g p.1 p.2
      * Wt α p.1 p.2) 2 Work.FTS.H2.pm := (memLp_two_iff_integrable_sq hXaesm).mpr hX_int
  have hY_memLp : MemLp (fun p : ℝ × ℝ => mixed 3 1 g p.1 p.2 * Wt α p.1 p.2) 2
      Work.FTS.H2.pm :=
    (memLp_two_iff_integrable_sq hYaesm).mpr (by rw [hpm]; exact hY_int)
  have hCS := Work.FTS.H2.cs_pm_of_nonneg
    (X := fun p : ℝ × ℝ => |DzIter 3 f p.1 p.2 * mixed 0 2 g p.1 p.2 * Wt α p.1 p.2|)
    (Y := fun p : ℝ × ℝ => |mixed 3 1 g p.1 p.2 * Wt α p.1 p.2|)
    (Eventually.of_forall fun p => abs_nonneg _) (Eventually.of_forall fun p => abs_nonneg _)
    (Work.FTS.H2.memLp_abs_pm hX_memLp) (Work.FTS.H2.memLp_abs_pm hY_memLp)
  have hXY_le : ∫ p, |DzIter 3 f p.1 p.2 * mixed 0 2 g p.1 p.2
      * mixed 3 1 g p.1 p.2 * (Work.FTS.H2.Wm α p.1 p.2) ^ 2| ∂Work.FTS.H2.pm
      ≤ Real.sqrt K3 * HkSq α 4 g := by
    have h1 : ∫ p, |DzIter 3 f p.1 p.2 * mixed 0 2 g p.1 p.2
        * mixed 3 1 g p.1 p.2 * (Work.FTS.H2.Wm α p.1 p.2) ^ 2| ∂Work.FTS.H2.pm
        = ∫ p, |DzIter 3 f p.1 p.2 * mixed 0 2 g p.1 p.2 * Wt α p.1 p.2|
            * |mixed 3 1 g p.1 p.2 * Wt α p.1 p.2| ∂Work.FTS.H2.pm := by
      refine integral_congr_ae (Eventually.of_forall fun p => ?_)
      show |DzIter 3 f p.1 p.2 * mixed 0 2 g p.1 p.2
          * mixed 3 1 g p.1 p.2 * (Work.FTS.H2.Wm α p.1 p.2) ^ 2|
        = |DzIter 3 f p.1 p.2 * mixed 0 2 g p.1 p.2 * Wt α p.1 p.2|
            * |mixed 3 1 g p.1 p.2 * Wt α p.1 p.2|
      have h2 : DzIter 3 f p.1 p.2 * mixed 0 2 g p.1 p.2
          * mixed 3 1 g p.1 p.2 * (Work.FTS.H2.Wm α p.1 p.2) ^ 2
          = (DzIter 3 f p.1 p.2 * mixed 0 2 g p.1 p.2 * Wt α p.1 p.2)
            * (mixed 3 1 g p.1 p.2 * Wt α p.1 p.2) := by
        simp only [Work.FTS.H2.Wm]
        ring
      rw [h2, abs_mul]
    rw [h1]
    have h2 : ∫ p, |DzIter 3 f p.1 p.2 * mixed 0 2 g p.1 p.2
          * Wt α p.1 p.2| ^ 2 ∂Work.FTS.H2.pm
        = ∫ p, (DzIter 3 f p.1 p.2 * mixed 0 2 g p.1 p.2
          * Wt α p.1 p.2) ^ 2 ∂Work.FTS.H2.pm :=
      integral_congr_ae (Eventually.of_forall fun p => sq_abs _)
    have h3 : ∫ p, |mixed 3 1 g p.1 p.2 * Wt α p.1 p.2| ^ 2 ∂Work.FTS.H2.pm
        = ∫ p, (mixed 3 1 g p.1 p.2 * Wt α p.1 p.2) ^ 2 ∂Work.FTS.H2.pm :=
      integral_congr_ae (Eventually.of_forall fun p => sq_abs _)
    rw [h2, h3] at hCS
    refine le_trans hCS ?_
    calc Real.sqrt (∫ p, (DzIter 3 f p.1 p.2 * mixed 0 2 g p.1 p.2
            * Wt α p.1 p.2) ^ 2 ∂Work.FTS.H2.pm) * Real.sqrt (∫ p, (mixed 3 1 g p.1 p.2
            * Wt α p.1 p.2) ^ 2 ∂Work.FTS.H2.pm)
        ≤ Real.sqrt (K3 * HkSq α 4 g) * Real.sqrt (HkSq α 4 g) :=
          mul_le_mul (Real.sqrt_le_sqrt hX_le) (Real.sqrt_le_sqrt hYsq_le)
            (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      _ = Real.sqrt K3 * HkSq α 4 g := by
          rw [Real.sqrt_mul hK3, mul_assoc, Real.mul_self_sqrt (HkSq_nonneg α 4 g)]
  -- the integrability of the exceptional integrand on the plane
  have hXYaesm : AEStronglyMeasurable
      (fun p : ℝ × ℝ => |DzIter 3 f p.1 p.2 * mixed 0 2 g p.1 p.2
        * mixed 3 1 g p.1 p.2 * (Work.FTS.H2.Wm α p.1 p.2) ^ 2|) Work.FTS.H2.pm :=
    Work.FTS.H2.aesm_of_Qd
      ((((((Work.FTS.LocData.contDiffOn_DzIter Work.Spaces.isOpen_quadU hf 3).continuousOn.mono
        Work.FTS.H2.HQ.quadQ_subset_quadU).mul
        ((Work.FTS.LocData.contDiffOn_DthIter Work.Spaces.isOpen_quadU hg 2).continuousOn.mono
          Work.FTS.H2.HQ.quadQ_subset_quadU)).mul
        ((Work.FTS.LocData.contDiffOn_mixed Work.Spaces.isOpen_quadU hg 3 1).continuousOn.mono
          Work.FTS.H2.HQ.quadQ_subset_quadU)).mul
          ((Work.FTS.H2.HQ.continuousOn_Wt_quad α).pow 2)).abs)
  have hXY_int : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => |DzIter 3 f p.1 p.2 * mixed 0 2 g p.1 p.2
        * mixed 3 1 g p.1 p.2 * (Work.FTS.H2.Wm α p.1 p.2) ^ 2|) Work.FTS.H2.pm := by
    refine MeasureTheory.Integrable.mono'
      (((hX_int.add hY_int).const_mul (1 / 2))) hXYaesm ?_
    filter_upwards with p
    rw [Real.norm_of_nonneg (abs_nonneg _)]
    have hval : |DzIter 3 f p.1 p.2 * mixed 0 2 g p.1 p.2
        * mixed 3 1 g p.1 p.2 * (Work.FTS.H2.Wm α p.1 p.2) ^ 2|
        = |(DzIter 3 f p.1 p.2 * mixed 0 2 g p.1 p.2 * Wt α p.1 p.2)
            * (mixed 3 1 g p.1 p.2 * Wt α p.1 p.2)| := by
      have h2 : DzIter 3 f p.1 p.2 * mixed 0 2 g p.1 p.2
          * mixed 3 1 g p.1 p.2 * (Work.FTS.H2.Wm α p.1 p.2) ^ 2
          = (DzIter 3 f p.1 p.2 * mixed 0 2 g p.1 p.2 * Wt α p.1 p.2)
            * (mixed 3 1 g p.1 p.2 * Wt α p.1 p.2) := by
        simp only [Work.FTS.H2.Wm]
        ring
      rw [h2]
    rw [hval, abs_mul]
    have h1 : |DzIter 3 f p.1 p.2 * mixed 0 2 g p.1 p.2 * Wt α p.1 p.2|
          * |mixed 3 1 g p.1 p.2 * Wt α p.1 p.2|
        ≤ (1 / 2) * ((DzIter 3 f p.1 p.2 * mixed 0 2 g p.1 p.2
            * Wt α p.1 p.2) ^ 2
          + (mixed 3 1 g p.1 p.2 * Wt α p.1 p.2) ^ 2) := by
      have h2 : (DzIter 3 f p.1 p.2 * mixed 0 2 g p.1 p.2
            * Wt α p.1 p.2) ^ 2
          = |DzIter 3 f p.1 p.2 * mixed 0 2 g p.1 p.2 * Wt α p.1 p.2| ^ 2 :=
        (sq_abs _).symm
      have h3 : (mixed 3 1 g p.1 p.2 * Wt α p.1 p.2) ^ 2
          = |mixed 3 1 g p.1 p.2 * Wt α p.1 p.2| ^ 2 := (sq_abs _).symm
      rw [h2, h3]
      linarith [two_mul_le_add_sq
        (|DzIter 3 f p.1 p.2 * mixed 0 2 g p.1 p.2 * Wt α p.1 p.2|)
        (|mixed 3 1 g p.1 p.2 * Wt α p.1 p.2|)]
    exact h1
  have hXY_outer := hXY_int.integral_prod_left
  have hiter : ∫ z in Iz, (∫ θ in Iθ,
      |DzIter 3 f z θ * mixed 0 2 g z θ * mixed 3 1 g z θ
        * (Work.FTS.H2.Wm α z θ) ^ 2|) ≤ Real.sqrt K3 * HkSq α 4 g := by
    rw [MeasureTheory.integral_integral hXY_int]
    exact hXY_le
  exact ⟨⟨hXY_int, hXY_le⟩, hXY_outer, hiter⟩

end Work.H2.T1Q
