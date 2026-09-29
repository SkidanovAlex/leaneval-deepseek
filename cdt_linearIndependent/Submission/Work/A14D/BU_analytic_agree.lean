import Mathlib
import Submission.Work.A14.defs
import Submission.Work.A14D.LC_A_defs
import Submission.Work.A14D.BU_defs
import Submission.Work.A14D.fourteen_coeff_bounds
import Submission.Work.A14D.fourteen_subst_eval_disc
import Submission.Work.A14D.intY_pullback_hasDerivAt
import Submission.Work.A14D.GZ_eval
import Submission.Work.A14D.wC_mapsTo_SU_SL
import Submission.Work.A14D.wC_norm_lt_one
import Submission.Work.A14D.DyIter_diffOn_of_isOpen
import Submission.Work.A14D.DyIter_congr_of_eqOn
import Submission.Work.A14D.primSeg_hasDerivAt_of_convex
import Submission.Work.A14D.primSeg_eq_of_hasDerivAt
import Submission.Work.A14D.Yser_tq_identity
import Submission.Work.A14D.Yser_GZ_eq
import Submission.Work.A14D.BUint_diffOn_SU
import Submission.Work.C17I.DyIter_comp_yC
import Submission.Work.C17I.yC_norm_lt_fifth
import Submission.Work.C17g.segment_primitive

/-!
# `Work.A14D.BU_analytic_agree`

The `SU`-branch `BU` of the fourteen pullbacks (`Work.A14D.BU`, `Submission/Work/A14D/LC_A_defs.lean`)
is differentiable on `SU \ {2}` and agrees with the pullback series
`Σ_k [yᵏ]fourteenᵢ · yC(z)ᵏ` on `SU ∩ ball 0 (34/100) ∩ {Re z < 1/2}`.

* the seven pure slots are the continuations `BUp j` of the substituted pure series;
* the four `G`-slots are `∂_y^k (HU + HL∘wC)`, identified with the `y`-series of `dY^k GZ` by
  `Work.C17I.DyIter_comp_yC` (the agreement `HU + HL∘wC = Hfun + Hfun∘wC` is `GZ_eval`);
* the three integral slots are primitives of `y'·y^{-i}·(G − jets)`; the constancy of
  `Yser (intY (tq i GZ)) − primSeg ⋯` on the convex set `SU ∩ ball 0 (34/100)` (`primSeg_eq_of_hasDerivAt`)
  identifies them with `Yser (intY (tq i GZ))`.
-/

namespace Work.A14D

open Complex Metric Filter Polynomial
open scoped Topology BigOperators

noncomputable section

/-! ## Elementary facts -/

private lemma cSU_mem_SU : cSU ∈ SU := by
  rw [mem_SU_iff]; norm_num [cSU]

private lemma cSU_norm_sq : ‖cSU‖ ^ 2 = (29 : ℝ) / 1600 := by
  rw [Complex.sq_norm]
  simp only [cSU, Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.div_ofNat_re,
    Complex.div_ofNat_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero]
  norm_num

private lemma cSU_mem_ball : cSU ∈ Metric.ball (0 : ℂ) ((34 : ℝ) / 100) := by
  rw [Metric.mem_ball, Complex.dist_eq, sub_zero]
  nlinarith [norm_nonneg cSU, cSU_norm_sq]

private lemma yC_diffOn_SU : DifferentiableOn ℂ yC SU := by
  have h1 : (1 : ℂ) ∉ SU := one_notMem_SU
  unfold yC
  exact (differentiableOn_id.pow 2).div (differentiableOn_id.sub (differentiableOn_const 1))
    (fun z hz h => h1 (by rwa [sub_eq_zero.mp h] at hz))

private lemma yC_ne_zero_SU {z : ℂ} (hz : z ∈ SU) : yC z ≠ 0 := by
  intro hz0
  have hz1 : z ≠ 1 := fun h => one_notMem_SU (h ▸ hz)
  have h2 : z ^ 2 = 0 := by
    have h := hz0
    rw [yC] at h
    field_simp at h
    simpa using h
  have h3 : z = 0 := sq_eq_zero_iff.mp h2
  exact zero_notMem_SU (h3 ▸ hz)

private lemma diffOn_wC {S : Set ℂ} (h1 : (1 : ℂ) ∉ S) : DifferentiableOn ℂ wC S :=
  (differentiableOn_id.div (differentiableOn_id.sub (differentiableOn_const 1))
    (fun z hz h => h1 (by rw [sub_eq_zero.mp h] at hz; exact hz)))

private lemma diffOn_HU_HL {HU HL : ℂ → ℂ} {S : Set ℂ} (hSsub : S ⊆ SU) (h1 : (1 : ℂ) ∉ S)
    (hHU : DifferentiableOn ℂ HU SU) (hHL : DifferentiableOn ℂ HL SL) :
    DifferentiableOn ℂ (fun z => HU z + HL (wC z)) S :=
  (hHU.mono hSsub).add
    (hHL.comp (diffOn_wC h1) (fun z hz => wC_mapsTo_SU_SL (hSsub hz)))

/-! ## Slot bookkeeping -/

private lemma fourteen_pureIdxA (a b c : ℤ) (j : Fin 7) :
    Submission.CDTPlan.fourteen a b c (pureIdxA j) = Submission.CDTPlan.pureB j := by
  fin_cases j <;> rfl

private lemma fourteen_gIdxA (a b c : ℤ) (k : Fin 4) :
    Submission.CDTPlan.fourteen a b c (gIdxA k)
      = Submission.CDTPlan.dY^[(k : ℕ)] (Submission.CDTPlan.GZ a b c) := by
  fin_cases k <;> rfl

private lemma tq_zero (f : PowerSeries ℚ) : Submission.CDTPlan.tq 0 f = f := by
  ext n
  rw [Submission.CDTPlan.tq, PowerSeries.coeff_mk]
  simp

private lemma fourteen_iIdxA (a b c : ℤ) (i : Fin 3) :
    Submission.CDTPlan.fourteen a b c (iIdxA i)
      = Submission.CDTPlan.intY (Submission.CDTPlan.tq (i : ℕ) (Submission.CDTPlan.GZ a b c)) := by
  fin_cases i <;> simp [iIdxA, Submission.CDTPlan.fourteen, tq_zero]

private lemma coeff_tq_cast (f : PowerSeries ℚ) (i k : ℕ) :
    ((PowerSeries.coeff k (Submission.CDTPlan.tq i f) : ℚ) : ℂ)
      = ((PowerSeries.coeff (k + i) f : ℚ) : ℂ) := by
  rw [Submission.CDTPlan.tq, PowerSeries.coeff_mk]

private lemma tq_coeff_bound {f : PowerSeries ℚ} {C R : ℝ} (hR : 0 < R)
    (hf : ∀ k : ℕ, ‖((PowerSeries.coeff k f : ℚ) : ℂ)‖ * R ^ k ≤ C) (i k : ℕ) :
    ‖((PowerSeries.coeff k (Submission.CDTPlan.tq i f) : ℚ) : ℂ)‖ * R ^ k ≤ C / R ^ i := by
  rw [coeff_tq_cast, le_div_iff₀ (pow_pos hR i)]
  have h := hf (k + i)
  rw [pow_add] at h
  calc ‖((PowerSeries.coeff (k + i) f : ℚ) : ℂ)‖ * R ^ k * R ^ i
      = ‖((PowerSeries.coeff (k + i) f : ℚ) : ℂ)‖ * (R ^ k * R ^ i) := by ring
    _ ≤ C := h

/-- `‖z‖ ≤ 34/100` implies `z ∈ ball 0 1` and `z ≠ 1`, `z ≠ 2`. -/
private lemma ne_one_ne_two_of_norm_le_34 {z : ℂ} (hz : ‖z‖ ≤ (34 : ℝ) / 100) :
    z ≠ 1 ∧ z ≠ 2 := by
  refine ⟨?_, ?_⟩ <;> intro h <;> rw [h] at hz <;> norm_num at hz

/-! ## Differentiability on `SU \ {2}` -/

private lemma hA_pure (a b c : ℤ) (j : Fin 7) :
    DifferentiableOn ℂ (BUp j) (SU \ ({2} : Set ℂ)) :=
  (BUp_analytic_SU j).mono Set.sdiff_subset

private lemma hA_G {HU HL : ℂ → ℂ} (hHU : DifferentiableOn ℂ HU SU)
    (hHL : DifferentiableOn ℂ HL SL) (k : ℕ) :
    DifferentiableOn ℂ (BUg HU HL k) (SU \ ({2} : Set ℂ)) := by
  have hopen : IsOpen (SU \ ({2} : Set ℂ)) := isOpen_SU_H_cont.sdiff isClosed_singleton
  have hdiff : DifferentiableOn ℂ (fun z => HU z + HL (wC z)) (SU \ ({2} : Set ℂ)) :=
    diffOn_HU_HL Set.sdiff_subset (fun h => one_notMem_SU h.1) hHU hHL
  have h0 : (0 : ℂ) ∉ SU \ ({2} : Set ℂ) := fun h => zero_notMem_SU h.1
  have h2 : (2 : ℂ) ∉ SU \ ({2} : Set ℂ) := by simp
  exact DyIter_diffOn_of_isOpen hopen h0 h2 hdiff k

private lemma hA_I (a b c : ℤ) {HU HL : ℂ → ℂ} (hHU : DifferentiableOn ℂ HU SU)
    (hHL : DifferentiableOn ℂ HL SL) (i : Fin 3) :
    DifferentiableOn ℂ (BUi a b c HU HL i) (SU \ ({2} : Set ℂ)) := by
  have hgd : DifferentiableOn ℂ (BUint a b c HU HL i) SU := BUint_diffOn_SU a b c hHU hHL i
  have hprim : DifferentiableOn ℂ (primSeg (BUint a b c HU HL i) cSU) SU :=
    (primSeg_hasDerivAt_of_convex convex_SU isOpen_SU_H_cont cSU_mem_SU hgd).1
  have hBUi : BUi a b c HU HL i = fun z => (∑' k : ℕ,
      ((PowerSeries.coeff k (Submission.CDTPlan.fourteen a b c (iIdxA i)) : ℚ) : ℂ)
        * (yC cSU) ^ k) + primSeg (BUint a b c HU HL i) cSU z := rfl
  rw [hBUi]
  exact ((differentiableOn_const _).add hprim).mono Set.sdiff_subset

/-! ## The value identity on the small region -/

private lemma hB_pure (a b c : ℤ) (h : Submission.CDTPlan.ARel a b c) (j : Fin 7) :
    ∀ z ∈ SU ∩ Metric.ball (0 : ℂ) ((34 : ℝ) / 100) ∩ {z : ℂ | z.re < 1 / 2},
      BUp j z = ∑' k : ℕ,
        ((PowerSeries.coeff k (Submission.CDTPlan.fourteen a b c (pureIdxA j)) : ℚ) : ℂ)
          * (yC z) ^ k := by
  intro z hz
  have hzlt : ‖z‖ < 1 := by
    have h34 : ‖z‖ < (34 : ℝ) / 100 := by
      have := hz.1.2; rwa [Metric.mem_ball, Complex.dist_eq, sub_zero] at this
    linarith
  have hzle : ‖z‖ ≤ (34 : ℝ) / 100 := le_of_lt (by
    have := hz.1.2; rwa [Metric.mem_ball, Complex.dist_eq, sub_zero] at this)
  have hkey := (fourteen_subst_eval_disc a b c h (fourteen_coeff_bounds a b c h)
    (pureIdxA j) z hzle).tsum_eq
  rw [fourteen_pureIdxA a b c j] at hkey
  rw [BUp_series j hzlt, fourteen_pureIdxA a b c j]
  exact hkey

private lemma hB_G (a b c : ℤ) (h : Submission.CDTPlan.ARel a b c) {HU HL : ℂ → ℂ}
    (hHUeq : ∀ z ∈ SU ∩ Metric.ball (0 : ℂ) 1, HU z = Hfun a b c z)
    (hHLeq : ∀ z ∈ SL ∩ Metric.ball (0 : ℂ) 1, HL z = Hfun a b c z) (k : Fin 4) :
    ∀ z ∈ SU ∩ Metric.ball (0 : ℂ) ((34 : ℝ) / 100) ∩ {z : ℂ | z.re < 1 / 2},
      BUg HU HL (k : ℕ) z = ∑' n : ℕ,
        ((PowerSeries.coeff n (Submission.CDTPlan.fourteen a b c (gIdxA k)) : ℚ) : ℂ)
          * (yC z) ^ n := by
  obtain ⟨CG, RG, hCG, hRG5, hRG1, hGbound⟩ := fourteen_coeff_bounds a b c h 5
  have hRGpos : 0 < RG := by linarith
  intro z hz
  have hzSU : z ∈ SU := hz.1.1
  have hz34 : ‖z‖ < (34 : ℝ) / 100 := by
    have := hz.1.2; rwa [Metric.mem_ball, Complex.dist_eq, sub_zero] at this
  have hzle34 : ‖z‖ ≤ (34 : ℝ) / 100 := le_of_lt hz34
  have hzS : z ∈ SU ∩ Metric.ball (0 : ℂ) ((39 : ℝ) / 100) :=
    ⟨hzSU, by rw [Metric.mem_ball, Complex.dist_eq, sub_zero]; linarith⟩
  have hSopen : IsOpen (SU ∩ Metric.ball (0 : ℂ) ((39 : ℝ) / 100)) :=
    isOpen_SU_H_cont.inter Metric.isOpen_ball
  have heq : ∀ w ∈ SU ∩ Metric.ball (0 : ℂ) ((39 : ℝ) / 100),
      HU w + HL (wC w) = Yser (Submission.CDTPlan.GZ a b c) w := by
    intro w hw
    exact (Yser_GZ_eq a b c h HU HL hHUeq hHLeq w hw).symm
  have h1 : BUg HU HL (k : ℕ) z
      = DyIter (k : ℕ) (fun u => Yser (Submission.CDTPlan.GZ a b c) u) z :=
    DyIter_congr_of_eqOn hSopen heq (k : ℕ) z hzS
  obtain ⟨hz1, hz2⟩ := ne_one_ne_two_of_norm_le_34 hzle34
  have hz0 : z ≠ 0 := fun hh => zero_notMem_SU (hh ▸ hzSU)
  have hyR : ‖yC z‖ < RG := lt_trans (Work.C17I.yC_norm_lt_fifth z hzle34) hRG5
  have h2raw := Work.C17I.DyIter_comp_yC (Submission.CDTPlan.GZ a b c) hCG hRGpos
    hGbound z hyR hz0 hz1 hz2 (k : ℕ)
  have h2 : DyIter (k : ℕ) (fun u => Yser (Submission.CDTPlan.GZ a b c) u) z
      = ∑' n : ℕ, ((PowerSeries.coeff n (Submission.CDTPlan.dY^[(k : ℕ)]
          (Submission.CDTPlan.GZ a b c)) : ℚ) : ℂ) * (yC z) ^ n := h2raw
  rw [h1, h2, ← fourteen_gIdxA a b c k]

private lemma hB_I (a b c : ℤ) (h : Submission.CDTPlan.ARel a b c) {HU HL : ℂ → ℂ}
    (hHU : DifferentiableOn ℂ HU SU) (hHL : DifferentiableOn ℂ HL SL)
    (hHUeq : ∀ z ∈ SU ∩ Metric.ball (0 : ℂ) 1, HU z = Hfun a b c z)
    (hHLeq : ∀ z ∈ SL ∩ Metric.ball (0 : ℂ) 1, HL z = Hfun a b c z) (i : Fin 3) :
    ∀ z ∈ SU ∩ Metric.ball (0 : ℂ) ((34 : ℝ) / 100) ∩ {z : ℂ | z.re < 1 / 2},
      BUi a b c HU HL i z = ∑' n : ℕ,
        ((PowerSeries.coeff n (Submission.CDTPlan.fourteen a b c (iIdxA i)) : ℚ) : ℂ)
          * (yC z) ^ n := by
  obtain ⟨CG, RG, hCG, hRG5, hRG1, hGbound⟩ := fourteen_coeff_bounds a b c h 5
  have hRGpos : 0 < RG := by linarith
  have hbou := fourteen_coeff_bounds a b c h
  have htq : ∀ k : ℕ, ‖((PowerSeries.coeff k
      (Submission.CDTPlan.tq (i : ℕ) (Submission.CDTPlan.GZ a b c)) : ℚ) : ℂ)‖ * RG ^ k
      ≤ CG / RG ^ (i : ℕ) := tq_coeff_bound hRGpos hGbound (i : ℕ)
  intro z hz
  set S : Set ℂ := SU ∩ Metric.ball (0 : ℂ) ((34 : ℝ) / 100) with hSdef
  have hSopen : IsOpen S := isOpen_SU_H_cont.inter Metric.isOpen_ball
  have hSconv : Convex ℝ S := convex_SU.inter (convex_ball (0 : ℂ) _)
  have hzS : z ∈ S := ⟨hz.1.1, hz.1.2⟩
  have hcS : cSU ∈ S := ⟨cSU_mem_SU, cSU_mem_ball⟩
  have hgd : DifferentiableOn ℂ (BUint a b c HU HL i) S :=
    (BUint_diffOn_SU a b c hHU hHL i).mono Set.inter_subset_left
  -- the derivative of `Φ = Σ_k [yᵏ](intY (tq i GZ))·(yC ·)ᵏ` is the integrand
  have hderiv : ∀ w ∈ S, HasDerivAt
      (fun u : ℂ => ∑' k : ℕ, ((PowerSeries.coeff k
        (Submission.CDTPlan.intY (Submission.CDTPlan.tq (i : ℕ)
          (Submission.CDTPlan.GZ a b c))) : ℚ) : ℂ) * (yC u) ^ k)
      (BUint a b c HU HL i w) w := by
    intro w hw
    have hw34 : ‖w‖ ≤ (34 : ℝ) / 100 := le_of_lt (by
      have := hw.2; rwa [Metric.mem_ball, Complex.dist_eq, sub_zero] at this)
    have hwSU : w ∈ SU := hw.1
    have hw39 : ‖w‖ ≤ (39 : ℝ) / 100 := by linarith
    have hyw : ‖yC w‖ < RG := lt_trans (Work.C17I.yC_norm_lt_fifth w hw34) hRG5
    -- the pullback of `intY (tq i GZ)` as a substituted series
    have hC' : 0 < CG / RG ^ (i : ℕ) := div_pos hCG (pow_pos hRGpos _)
    have hpull := intY_pullback_hasDerivAt (Submission.CDTPlan.tq (i : ℕ)
      (Submission.CDTPlan.GZ a b c)) hC' hRGpos hRG5 hRG1 htq w hw34
    have hev : (fun u : ℂ => ∑' k : ℕ, ((PowerSeries.coeff k
          ((Submission.CDTPlan.intY (Submission.CDTPlan.tq (i : ℕ)
            (Submission.CDTPlan.GZ a b c))).subst Submission.CDT.sympY) : ℚ) : ℂ) * u ^ k)
        =ᶠ[𝓝 w] (fun u : ℂ => ∑' k : ℕ, ((PowerSeries.coeff k
          (Submission.CDTPlan.intY (Submission.CDTPlan.tq (i : ℕ)
            (Submission.CDTPlan.GZ a b c))) : ℚ) : ℂ) * (yC u) ^ k) := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hw.2] with u hu
      have hu' : ‖u‖ ≤ (34 : ℝ) / 100 := le_of_lt (by
        rwa [Metric.mem_ball, Complex.dist_eq, sub_zero] at hu)
      have hk := (fourteen_subst_eval_disc a b c h hbou (iIdxA i) u hu').tsum_eq
      rw [fourteen_iIdxA a b c i] at hk
      exact hk
    have hΨ := hpull.congr_of_eventuallyEq hev.symm
    -- the value of the derivative
    have hfin : (∑' k : ℕ, ((PowerSeries.coeff k
          (Submission.CDTPlan.tq (i : ℕ) (Submission.CDTPlan.GZ a b c)) : ℚ) : ℂ)
          * (yC w) ^ k)
        = (yC w)⁻¹ ^ (i : ℕ) * ((HU w + HL (wC w)) - GjetA a b c (i : ℕ) w) := by
      have hId := Yser_tq_identity (Submission.CDTPlan.GZ a b c) hCG hRGpos hGbound
        (i : ℕ) hyw
      have hGz := Yser_GZ_eq a b c h HU HL hHUeq hHLeq w
        ⟨hwSU, by rw [Metric.mem_ball, Complex.dist_eq, sub_zero]; linarith⟩
      have hjet : (∑ n ∈ Finset.range (i : ℕ), ((PowerSeries.coeff n
          (Submission.CDTPlan.GZ a b c) : ℚ) : ℂ) * (yC w) ^ n)
          = GjetA a b c (i : ℕ) w := rfl
      simp only [Yser] at hId hGz
      have hyne : yC w ≠ 0 := yC_ne_zero_SU hwSU
      have hkey : (yC w) ^ (i : ℕ) * (∑' k : ℕ, ((PowerSeries.coeff k
            (Submission.CDTPlan.tq (i : ℕ) (Submission.CDTPlan.GZ a b c)) : ℚ) : ℂ)
            * (yC w) ^ k)
          = (HU w + HL (wC w)) - GjetA a b c (i : ℕ) w := by
        rw [mul_comm, hId, hGz, hjet]
      have h1 : (yC w) ^ (i : ℕ) * (∑' k : ℕ, ((PowerSeries.coeff k
            (Submission.CDTPlan.tq (i : ℕ) (Submission.CDTPlan.GZ a b c)) : ℚ) : ℂ)
            * (yC w) ^ k)
          = (yC w) ^ (i : ℕ) * ((yC w)⁻¹ ^ (i : ℕ)
              * ((HU w + HL (wC w)) - GjetA a b c (i : ℕ) w)) := by
        rw [hkey, inv_pow, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hyne), one_mul]
      exact mul_left_cancel₀ (pow_ne_zero _ hyne) h1
    have hval : dyC w * (∑' k : ℕ, ((PowerSeries.coeff k
          (Submission.CDTPlan.tq (i : ℕ) (Submission.CDTPlan.GZ a b c)) : ℚ) : ℂ)
          * (yC w) ^ k) = BUint a b c HU HL i w := by
      rw [hfin, BUint]
      ring
    simpa only [hval] using hΨ
  have hftc := primSeg_eq_of_hasDerivAt hSopen hSconv hcS hzS hgd hderiv
  have hBUi : BUi a b c HU HL i z = (∑' k : ℕ, ((PowerSeries.coeff k
        (Submission.CDTPlan.fourteen a b c (iIdxA i)) : ℚ) : ℂ) * (yC cSU) ^ k)
      + primSeg (BUint a b c HU HL i) cSU z := rfl
  rw [hBUi, hftc, fourteen_iIdxA a b c i]
  ring

/-! ## The theorem -/

theorem BU_analytic_agree (a b c : ℤ) (h : Submission.CDTPlan.ARel a b c) (HU HL : ℂ → ℂ)
    (hHU : DifferentiableOn ℂ HU SU) (hHL : DifferentiableOn ℂ HL SL)
    (hHUeq : ∀ z ∈ SU ∩ Metric.ball (0 : ℂ) 1, HU z = Hfun a b c z)
    (hHLeq : ∀ z ∈ SL ∩ Metric.ball (0 : ℂ) 1, HL z = Hfun a b c z) :
    (∀ i : Fin 14, DifferentiableOn ℂ (BU a b c HU HL i) (SU \ ({2} : Set ℂ))) ∧
    (∀ i : Fin 14, ∀ z ∈ SU ∩ Metric.ball (0 : ℂ) ((34 : ℝ) / 100) ∩ {z : ℂ | z.re < 1 / 2},
      BU a b c HU HL i z = ∑' k : ℕ,
        ((PowerSeries.coeff k (Submission.CDTPlan.fourteen a b c i) : ℚ) : ℂ) * (yC z) ^ k) := by
  constructor
  · intro i
    fin_cases i
    · exact hA_pure a b c 0
    · exact hA_pure a b c 1
    · exact hA_pure a b c 2
    · exact hA_pure a b c 3
    · exact hA_pure a b c 4
    · exact hA_G hHU hHL 0
    · exact hA_G hHU hHL 1
    · exact hA_G hHU hHL 2
    · exact hA_G hHU hHL 3
    · exact hA_pure a b c 5
    · exact hA_pure a b c 6
    · exact hA_I a b c hHU hHL 0
    · exact hA_I a b c hHU hHL 1
    · exact hA_I a b c hHU hHL 2
  · intro i z hz
    fin_cases i
    · exact hB_pure a b c h 0 z hz
    · exact hB_pure a b c h 1 z hz
    · exact hB_pure a b c h 2 z hz
    · exact hB_pure a b c h 3 z hz
    · exact hB_pure a b c h 4 z hz
    · exact hB_G a b c h hHUeq hHLeq 0 z hz
    · exact hB_G a b c h hHUeq hHLeq 1 z hz
    · exact hB_G a b c h hHUeq hHLeq 2 z hz
    · exact hB_G a b c h hHUeq hHLeq 3 z hz
    · exact hB_pure a b c h 5 z hz
    · exact hB_pure a b c h 6 z hz
    · exact hB_I a b c h hHU hHL hHUeq hHLeq 0 z hz
    · exact hB_I a b c h hHU hHL hHUeq hHLeq 1 z hz
    · exact hB_I a b c h hHU hHL hHUeq hHLeq 2 z hz

end

end Work.A14D
