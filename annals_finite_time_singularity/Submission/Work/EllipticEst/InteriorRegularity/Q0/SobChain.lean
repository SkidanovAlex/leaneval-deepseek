/-
Sobolev chain (fresh, `sorry`-free copies) for the interior-regularity development of
`Work.EllipticEst.InteriorRegularity.Q0`.

The modules `MulSobolevDefs` / `mms_Phi_estimate` of the same directory contain the analytic
kernel `Λ^s ∘ M_γ ∘ Λ^{-s}` bounded on `L²`, but their final assembly goes through
`young_l1_l2_eLpNorm`, which carries a `sorry`.  Here we redo the two-line final assembly with the
proved `Q0.youngE` and derive, in this namespace,

* `phiEstimate`  : the Schwartz-level `L²` estimate for `Λ^s ∘ M_γ ∘ Λ^{-s}`;
* `mulSob`       : multiplication by a compactly supported `C^∞` function preserves every
                   Bessel-potential space `H^s = MemSobolev s 2`;
* `ccMemSobolev` : a compactly supported `C^∞` function (as an `L²` distribution) lies in `H^s`.

Everything here rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Analysis.FunctionalSpaces.BesselPotentialSpace
import Submission.Work.EllipticEst.InteriorRegularity.MulSobolevDefs
import Submission.Work.EllipticEst.InteriorRegularity.mms_Phi_estimate
import Submission.Work.EllipticEst.InteriorRegularity.Q0.youngE

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FourierTransform TemperedDistribution MeasureTheory Filter
open scoped SchwartzMap BesselPotentialSpace ENNReal Topology

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Work.EllipticEst.InteriorRegularity.Q0

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-! ## The Schwartz-level `L²` estimate -/

/-- **The key estimate** (copy of `mms_Phi_estimate` with the proved `youngE`): the operator
`Λ^s ∘ M_γ ∘ Λ^{-s}` is bounded for the `L²` norm. -/
theorem phiEstimate (s : ℝ) (γS k : SchwartzMap E ℂ) :
    ‖(mms_Phi s γS k).toLp 2 (volume : Measure E)‖
      ≤ (∫ ξ : E, ‖(((2 : ℝ) ^ (|s| / 2) : ℝ) : ℂ) *
            (mms_wfun (E := E) |s| ξ * FourierTransform.fourier γS ξ)‖) *
          ‖k.toLp 2 (volume : Measure E)‖ := by
  have hFnn : ∀ z : E, 0 ≤ ‖(((2 : ℝ) ^ (|s| / 2) : ℝ) : ℂ) *
      (mms_wfun (E := E) |s| z * FourierTransform.fourier γS z)‖ := fun _ => norm_nonneg _
  have hun : ∀ y : E, 0 ≤ ‖FourierTransform.fourier k y‖ := fun _ => norm_nonneg _
  have hFi : Integrable (fun z : E => ‖(((2 : ℝ) ^ (|s| / 2) : ℝ) : ℂ) *
      (mms_wfun (E := E) |s| z * FourierTransform.fourier γS z)‖) (volume : Measure E) := by
    have hSint : Integrable (fun z : E =>
        ‖⇑(SchwartzMap.smulLeftCLM ℂ (mms_wfun (E := E) |s|)
          (FourierTransform.fourier γS : 𝓢(E, ℂ))) z‖) (volume : Measure E) :=
      (SchwartzMap.integrable _).norm
    refine (hSint.mul_const (2 ^ (|s| / 2))).congr (Eventually.of_forall fun z => ?_)
    dsimp only
    rw [SchwartzMap.smulLeftCLM_apply_apply (mms_wfun_temperate (E := E) |s|), smul_eq_mul,
      norm_mul, norm_mul, norm_mul, norm_ofReal_complex,
      abs_of_nonneg (Real.rpow_nonneg (by norm_num) (|s| / 2))]
    ring
  have huM : MemLp (fun y : E => ‖FourierTransform.fourier k y‖) 2 (volume : Measure E) :=
    (SchwartzMap.memLp (FourierTransform.fourier k) 2 (volume : Measure E)).norm
  have hfm : AEStronglyMeasurable
      (⇑(FourierTransform.fourier (mms_Phi s γS k))) (volume : Measure E) :=
    (SchwartzMap.memLp (FourierTransform.fourier (mms_Phi s γS k)) 2
      (volume : Measure E)).aestronglyMeasurable
  have hpt : ∀ ξ : E, ‖(⇑(FourierTransform.fourier (mms_Phi s γS k))) ξ‖ₑ
      ≤ ∫⁻ y, ENNReal.ofReal ((‖(((2 : ℝ) ^ (|s| / 2) : ℝ) : ℂ) *
          (mms_wfun (E := E) |s| (ξ - y) * FourierTransform.fourier γS (ξ - y))‖) *
          ‖FourierTransform.fourier k y‖) ∂(volume : Measure E) :=
    fun ξ => mms_Phi_enorm_le s γS k ξ
  have hmain := youngE
    (F := fun z : E => ‖(((2 : ℝ) ^ (|s| / 2) : ℝ) : ℂ) *
      (mms_wfun (E := E) |s| z * FourierTransform.fourier γS z)‖)
    (u := fun y : E => ‖FourierTransform.fourier k y‖)
    (f := ⇑(FourierTransform.fourier (mms_Phi s γS k))) hFnn hun hFi huM hfm hpt
  have hPhi : ‖(mms_Phi s γS k).toLp 2 (volume : Measure E)‖
      = (eLpNorm (⇑(FourierTransform.fourier (mms_Phi s γS k))) 2
          (volume : Measure E)).toReal := by
    have h1 : ‖(mms_Phi s γS k).toLp 2 (volume : Measure E)‖
        = ‖(FourierTransform.fourier (mms_Phi s γS k)).toLp 2 (volume : Measure E)‖ := by
      rw [← MeasureTheory.Lp.norm_fourier_eq ((mms_Phi s γS k).toLp 2 (volume : Measure E)),
        SchwartzMap.toLp_fourier_eq]
    rw [h1, SchwartzMap.norm_toLp]
  have hk : ‖k.toLp 2 (volume : Measure E)‖
      = (eLpNorm (⇑(FourierTransform.fourier k)) 2 (volume : Measure E)).toReal := by
    have h1 : ‖k.toLp 2 (volume : Measure E)‖
        = ‖(FourierTransform.fourier k).toLp 2 (volume : Measure E)‖ := by
      rw [← MeasureTheory.Lp.norm_fourier_eq (k.toLp 2 (volume : Measure E)),
        SchwartzMap.toLp_fourier_eq]
    rw [h1, SchwartzMap.norm_toLp]
  have hnormu : eLpNorm (fun y : E => ‖FourierTransform.fourier k y‖) 2 (volume : Measure E)
      = eLpNorm (⇑(FourierTransform.fourier k)) 2 (volume : Measure E) :=
    eLpNorm_norm _ (SchwartzMap.memLp (FourierTransform.fourier k) 2
      (volume : Measure E)).aestronglyMeasurable
  have hne : ENNReal.ofReal (∫ ξ : E, ‖(((2 : ℝ) ^ (|s| / 2) : ℝ) : ℂ) *
        (mms_wfun (E := E) |s| ξ * FourierTransform.fourier γS ξ)‖)
        * eLpNorm (⇑(FourierTransform.fourier k)) 2 (volume : Measure E) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ne_of_lt (SchwartzMap.memLp
      (FourierTransform.fourier k) 2 (volume : Measure E)).eLpNorm_lt_top)
  rw [hPhi, hk]
  calc (eLpNorm (⇑(FourierTransform.fourier (mms_Phi s γS k))) 2
          (volume : Measure E)).toReal
      ≤ (ENNReal.ofReal (∫ ξ : E, ‖(((2 : ℝ) ^ (|s| / 2) : ℝ) : ℂ) *
            (mms_wfun (E := E) |s| ξ * FourierTransform.fourier γS ξ)‖)
          * eLpNorm (⇑(FourierTransform.fourier k)) 2 (volume : Measure E)).toReal :=
        ENNReal.toReal_mono hne (by rw [← hnormu]; exact hmain)
    _ = (∫ ξ : E, ‖(((2 : ℝ) ^ (|s| / 2) : ℝ) : ℂ) *
            (mms_wfun (E := E) |s| ξ * FourierTransform.fourier γS ξ)‖)
          * (eLpNorm (⇑(FourierTransform.fourier k)) 2 (volume : Measure E)).toReal := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (integral_nonneg fun _ => norm_nonneg _)]

/-! ## Extension from Schwartz functions to `L²` -/

/-- Multiplication by a compactly supported smooth function preserves `H^s` (copy of
`mul_memSobolev`/`mms_main`, using the proved `phiEstimate`). -/
theorem mulSobMain {s : ℝ} (γS : SchwartzMap E ℂ) (u : TemperedDistribution E ℂ)
    (U : Lp ℂ 2 (volume : Measure E))
    (hU : besselPotential E ℂ s u = (U : TemperedDistribution E ℂ)) :
    MemSobolev s 2 (smulLeftCLM ℂ (⇑γS) u) := by
  set C : ℝ := ∫ ξ : E, ‖(((2 : ℝ) ^ (|s| / 2) : ℝ) : ℂ) *
      (mms_wfun (E := E) |s| ξ * (FourierTransform.fourier γS) ξ)‖ with hCdef
  have hC_nonneg : 0 ≤ C := by
    rw [hCdef]
    exact integral_nonneg fun ξ => norm_nonneg _
  have hu_eq : u = besselPotential E ℂ (-s) (U : TemperedDistribution E ℂ) := by
    rw [← mms_bessel_neg_bessel s u, hU]
  let e : SchwartzMap E ℂ →L[ℂ] Lp ℂ 2 (volume : Measure E) :=
    SchwartzMap.toLpCLM ℂ ℂ 2 volume
  have hdense : DenseRange e := by
    show DenseRange fun f : SchwartzMap E ℂ => f.toLp 2 (volume : Measure E)
    have h := SchwartzMap.denseRange_toLpCLM (F := ℂ) (E := E) (p := 2)
      (μ := (volume : Measure E)) (by norm_num)
    have hfe : (fun f : SchwartzMap E ℂ => f.toLp 2 (volume : Measure E)) =
        ⇑(SchwartzMap.toLpCLM ℝ ℂ 2 (volume : Measure E)) := by
      funext f
      rw [SchwartzMap.toLpCLM_apply]
    rw [hfe]
    exact h
  have hseq : ∀ n : ℕ, ∃ k : SchwartzMap E ℂ, dist U (e k) < 1 / ((n : ℝ) + 1) := by
    intro n
    exact (Metric.denseRange_iff.mp hdense) U _ (by positivity)
  choose f hf using hseq
  have hnorm : ∀ n : ℕ, ‖U - e (f n)‖ ≤ 1 / ((n : ℝ) + 1) := by
    intro n
    have h := hf n
    rw [dist_eq_norm] at h
    exact le_of_lt h
  have hzero : Tendsto (fun n : ℕ => U - e (f n)) atTop (𝓝 0) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
    refine ⟨N, fun n hn => ?_⟩
    have h1 : 1 / ((n : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) := by
      refine one_div_le_one_div_of_le (by positivity) ?_
      have hh := Nat.add_le_add_right hn 1
      exact_mod_cast hh
    have h2 : 1 / ((N : ℝ) + 1) < ε := by
      have h3 : (1 : ℝ) < ((N : ℝ) + 1) * ε := by
        have hN' : (1 : ℝ) / ε < (N : ℝ) + 1 := by
          have : (N : ℝ) < (N : ℝ) + 1 := by linarith
          linarith
        exact (div_lt_iff₀ hε).mp hN'
      rw [div_lt_iff₀ (by positivity : (0 : ℝ) < (N : ℝ) + 1)]
      nlinarith [h3]
    calc dist (U - e (f n)) 0 = ‖U - e (f n)‖ := by rw [dist_zero_right]
      _ ≤ 1 / ((n : ℝ) + 1) := hnorm n
      _ ≤ 1 / ((N : ℝ) + 1) := h1
      _ < ε := h2
  have hftend : Tendsto (fun n : ℕ => e (f n)) atTop (𝓝 U) := by
    have h1 : Tendsto (fun n : ℕ => U - (U - e (f n))) atTop (𝓝 (U - 0)) := hzero.const_sub U
    simpa using h1
  let v : ℕ → Lp ℂ 2 (volume : Measure E) := fun n => (mms_Phi s γS (f n)).toLp 2 volume
  have hv_lip : ∀ m n : ℕ, dist (v m) (v n) ≤ C * dist (e (f m)) (e (f n)) := by
    intro m n
    have hL : mms_Phi s γS (f m) - mms_Phi s γS (f n) = mms_Phi s γS (f m - f n) := by
      simp only [mms_Phi, map_sub]
    have hA' : v m - v n = (mms_Phi s γS (f m - f n)).toLp 2 (volume : Measure E) := by
      rw [show v m = (SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure E)) (mms_Phi s γS (f m))
            from rfl,
        show v n = (SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure E)) (mms_Phi s γS (f n))
            from rfl,
        ← map_sub (SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure E)), hL]
      rfl
    have hB' : e (f m) - e (f n) = (f m - f n).toLp 2 (volume : Measure E) := by
      show e (f m) - e (f n) = _
      rw [← map_sub e]
      rfl
    rw [dist_eq_norm, dist_eq_norm, hA', hB', hCdef]
    exact phiEstimate s γS (f m - f n)
  have hv_cauchy : CauchySeq v := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    have hce : CauchySeq fun n : ℕ => e (f n) := hftend.cauchySeq
    obtain ⟨N, hN⟩ := (Metric.cauchySeq_iff.mp hce) (ε / (C + 1)) (by positivity)
    refine ⟨N, fun m hm n hn => ?_⟩
    have hC1 : 0 < C + 1 := by linarith
    have h1 := hv_lip m n
    have h2 := hN m hm n hn
    have h3 : C * dist (e (f m)) (e (f n)) ≤ (C + 1) * dist (e (f m)) (e (f n)) := by
      have hd : 0 ≤ dist (e (f m)) (e (f n)) := dist_nonneg
      nlinarith
    have h4 : (C + 1) * dist (e (f m)) (e (f n)) < (C + 1) * (ε / (C + 1)) :=
      mul_lt_mul_of_pos_left h2 hC1
    have h5 : (C + 1) * (ε / (C + 1)) = ε := by
      field_simp
    linarith [h1, h3, h4, h5.le, h5.ge]
  obtain ⟨V, hV⟩ := cauchySeq_tendsto_of_complete hv_cauchy
  let A : Lp ℂ 2 (volume : Measure E) →L[ℂ] TemperedDistribution E ℂ :=
    (besselPotential E ℂ s).comp ((smulLeftCLM ℂ (⇑γS)).comp
      ((besselPotential E ℂ (-s)).comp (Lp.toTemperedDistributionCLM (F := ℂ) (μ := volume) 2)))
  have hAapply : ∀ W : Lp ℂ 2 (volume : Measure E), A W = besselPotential E ℂ s
      (smulLeftCLM ℂ (⇑γS) (besselPotential E ℂ (-s) (W : TemperedDistribution E ℂ))) := by
    intro W
    rfl
  have hA : ∀ n : ℕ, A (e (f n)) = (v n : TemperedDistribution E ℂ) := by
    intro n
    rw [hAapply]
    have h1 : ((e (f n) : Lp ℂ 2 (volume : Measure E)) : TemperedDistribution E ℂ)
        = (f n : TemperedDistribution E ℂ) :=
      Lp.toTemperedDistribution_toLp_eq (f n)
    rw [h1, ← mms_Phi_toTempered s γS (f n)]
    exact (Lp.toTemperedDistribution_toLp_eq (mms_Phi s γS (f n))).symm
  have hAU : A U = besselPotential E ℂ s (smulLeftCLM ℂ (⇑γS) u) := by
    rw [hAapply, ← hU, mms_bessel_neg_bessel]
  have h1 : Tendsto (fun n : ℕ => (v n : TemperedDistribution E ℂ)) atTop
      (𝓝 (besselPotential E ℂ s (smulLeftCLM ℂ (⇑γS) u))) := by
    have hcomp : Tendsto (fun n : ℕ => A (e (f n))) atTop (𝓝 (A U)) :=
      (A.continuous.tendsto U).comp hftend
    rw [← hAU]
    simpa only [hA] using hcomp
  have h2 : Tendsto (fun n : ℕ => (v n : TemperedDistribution E ℂ)) atTop
      (𝓝 (V : TemperedDistribution E ℂ)) :=
    ((Lp.toTemperedDistributionCLM (F := ℂ) (μ := volume) 2).continuous.tendsto V).comp hV
  exact ⟨V, tendsto_nhds_unique h1 h2⟩

/-- **Multiplication by a compactly supported `C^∞` function preserves `H^s = MemSobolev s 2`**
(for every real `s`). -/
theorem mulSob {s : ℝ} {γ : E → ℂ} (hγc : HasCompactSupport γ) (hγs : ∀ n : ℕ, ContDiff ℝ n γ)
    {u : TemperedDistribution E ℂ} (hu : TemperedDistribution.MemSobolev s 2 u) :
    TemperedDistribution.MemSobolev s 2 (TemperedDistribution.smulLeftCLM ℂ γ u) := by
  have hγS_smooth : ContDiff ℝ (⊤ : ℕ∞) γ := contDiff_infty.mpr hγs
  let γS : SchwartzMap E ℂ := hγc.toSchwartzMap hγS_smooth
  obtain ⟨U, hU⟩ := hu
  exact mulSobMain γS u U hU

/-- A compactly supported `C^∞` function, viewed as the distribution of its `L²` class, lies in
every Bessel potential space `H^s`. -/
theorem ccMemSobolev {s : ℝ} {f : E → ℂ} {hf : MemLp f 2 (volume : Measure E)}
    (hc : HasCompactSupport f) (hs : ∀ n : ℕ, ContDiff ℝ n f) :
    TemperedDistribution.MemSobolev s 2
      (MeasureTheory.Lp.toTemperedDistribution (hf.toLp)) := by
  have hfs : ContDiff ℝ (⊤ : ℕ∞) f := contDiff_infty.mpr hs
  let fS : SchwartzMap E ℂ := hc.toSchwartzMap hfs
  have hcoe : (⇑fS : E → ℂ) = f := funext (HasCompactSupport.toSchwartzMap_toFun hc hfs)
  have hLp : fS.toLp 2 (volume : Measure E) = hf.toLp := by
    refine Lp.ext ?_
    filter_upwards [SchwartzMap.coeFn_toLp (f := fS) 2 (volume : Measure E),
      hf.coeFn_toLp] with x h1 h2
    rw [h1, h2, hcoe]
  rw [← hLp, Lp.toTemperedDistribution_toLp_eq fS]
  -- the Bessel potential of a Schwartz function is a Schwartz function, hence `L²`
  refine ⟨(SchwartzMap.fourierMultiplierCLM ℂ (mms_wfun (E := E) s) fS).toLp 2 volume, ?_⟩
  rw [mms_bessel_schwartz s fS]
  exact (Lp.toTemperedDistribution_toLp_eq
    (SchwartzMap.fourierMultiplierCLM ℂ (mms_wfun (E := E) s) fS)).symm

end Work.EllipticEst.InteriorRegularity.Q0
