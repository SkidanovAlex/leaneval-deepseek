/-
Copyright: work module for the Elgindi finite-time singularity project (area `FTS.EllSol`).

# The second angular slot of the truncation `uTr N b u` (the `Athree` slot)

This file proves `Work.FTS.EllSol.ShiftFT.uTr_Athree`: the second angular slot
`∫∫ (∂_θ² ·)² σ_η` of the truncated data `uTr N b u` is `IntegrableOn` the half-strip and is
bounded, with a constant independent of `N`, by the same slot of `u`.

## Structure of the proof

With `Gc N b u t θ = chi N t · u t θ + e^{bt} ∫_t^{2N} e^{-bs} (chi N)'(s) u s θ ds` and
`uTr N b u = phiTr N · Gc N b u`, the second `θ`-derivative of `uTr` is

`∂_θ²(uTr) t θ = phiTr N t · ( chi N t · ∂_θ²u t θ + tailE N b (∂_θ²u) t θ )`

(`UTrPthPth`), where `tailE N b f t θ = e^{bt} ∫_t^{2N} e^{-bs} (chi N)'(s) f s θ ds`
(`uTrAthree.tailE`).  Hence, for `θ ∈ Iθ`,

`(∂_θ²(uTr))² σ_η ≤ 2 (∂_θ²u)² σ_η + 2 (phiTr² · (tailE)² · σ_η)`

because `|phiTr| ≤ 1` and `|chi| ≤ 1` (`key_ineq`).  The first summand reproduces the
right-hand side; the second is the actual content.

For the second summand, `(chi N)'` is `O(1/N)` and vanishes off `(-2N,2N)`, so for fixed `θ` the
one-dimensional estimate `TailOneD` gives

`∫_t (tailE N b f t θ)² ≤ 40000 c² ∫_{[-2N,2N]} (f t θ)²`   uniformly in `N ≥ 2`,

with `c` the universal bound on `N · |(chi N)'|`.  Integrating in `θ` against `σ_η` (Tonelli,
all integrands being nonnegative) and using `hI` for the `∂_θ²u`-slot gives the claim.  The
`IntegrableOn` conclusions come from the finiteness of the corresponding `∫⁻`
(`ENNReal.lintegral_ofReal_ne_top_iff_integrable`).
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Have
import Submission.Work.FTS.EllSol.ShiftFT.uTrAthree.Defs
import Submission.Work.FTS.EllSol.ShiftFT.uTrAthree.UTrPthPth
import Submission.Work.FTS.EllSol.ShiftFT.uTrAthree.TailOneD
import Submission.Work.FTS.EllSol.ShiftFT.uTrAthree.TailECont
import Submission.Work.FTS.EllSol.Trunc.PassAux
import Submission.Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.ShiftFT

open MeasureTheory Set Filter
open scoped Real Topology ENNReal

noncomputable section

set_option autoImplicit false
open MeasureTheory Set Filter
open scoped Real Topology ENNReal

/-- The `ofReal` of a function continuous on the strip is a.e. strongly measurable.
(Local copy of the same-named lemma of `FlatFT/flatNiceAssembly.lean`, under a *fresh* name so
that modules importing both `FlatFT` and this file do not clash.) -/
theorem aesm_prod_of_continuousOnE {Phi : ℝ × ℝ → ℝ}
    (hPhi : ContinuousOn Phi ((Set.univ : Set ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2))) :
    AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal (Phi p))
      ((volume : Measure ℝ).prod (volume.restrict Work.Spaces.Iθ)) := by
  have hmeas : MeasurableSet ((Set.univ : Set ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    MeasurableSet.univ.prod measurableSet_Ioo
  have hcont : ContinuousOn (fun p : ℝ × ℝ => ENNReal.ofReal (Phi p))
      ((Set.univ : Set ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    ENNReal.continuous_ofReal.comp_continuousOn hPhi
  have h1 : AEStronglyMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal (Phi p))
      ((volume.prod volume).restrict ((Set.univ : Set ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2))) :=
    hcont.aestronglyMeasurable hmeas
  have h2 : (volume.prod volume).restrict ((Set.univ : Set ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2))
      = volume.prod (volume.restrict Work.Spaces.Iθ) := by
    rw [← Measure.prod_restrict (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
      Set.univ (Set.Ioo 0 (Real.pi / 2)), Measure.restrict_univ]
    rw [Work.Spaces.Iθ,
      Measure.restrict_congr_set (MeasureTheory.Ioo_ae_eq_Icc (μ := (volume : Measure ℝ)))]
  rw [h2] at h1
  exact h1.aemeasurable


/-! ## Elementary auxiliary facts

These are the little facts about the cutoffs used by the assembly; they do not depend on any of
the three delegated lemmas. -/

/-- The derivative of the cutoff at scale `N` vanishes for `2N ≤ |s|`. -/
theorem deriv_chi_eq_zero_of_two_mul_le {N s : ℝ} (hN : 0 < N) (hs : 2 * N ≤ |s|) :
    deriv (Trunc.chi N) s = 0 := by
  have hev : Trunc.chi N =ᶠ[𝓝 s] (fun _ : ℝ => (0 : ℝ)) := by
    rcases eq_or_lt_of_le hs with heq | hlt
    · -- `|s| = 2N`: the basic cutoff vanishes on a neighbourhood of `±2`
      have hsq : s ^ 2 = (2 * N) ^ 2 := by rw [← sq_abs, ← heq]
      have h4 : (s / N) ^ 2 = 4 := by
        rw [div_pow, hsq]
        field_simp
        ring
      have hneg : (2 : ℝ) - (s / N) ^ 2 < 0 := by rw [h4]; norm_num
      have hopen : IsOpen {y : ℝ | 2 - y ^ 2 < 0} :=
        isOpen_lt (continuous_const.sub (continuous_id.pow 2)) continuous_const
      have hc : Continuous fun t : ℝ => t / N := continuous_id.div_const N
      filter_upwards [hopen.preimage hc |>.mem_nhds hneg] with t ht
      show Real.smoothTransition (2 - (t / N) ^ 2) = 0
      exact Real.smoothTransition.zero_of_nonpos (le_of_lt ht)
    · -- `2N < |s|`
      have hopen : IsOpen {t : ℝ | 2 * N < |t|} := isOpen_lt continuous_const continuous_abs
      filter_upwards [hopen.mem_nhds hlt] with t ht
      exact Trunc.chi_eq_zero hN (le_of_lt ht)
  rw [hev.deriv_eq, deriv_const]

/-- `tailE` vanishes for `t ≥ 2N`. -/
theorem tailE_eq_zero_of_le {N b : ℝ} (hN : 0 < N) (f : ℝ → ℝ → ℝ) {t θ : ℝ}
    (ht : 2 * N ≤ t) : uTrAthree.tailE N b f t θ = 0 := by
  have hzero : ∀ s ∈ Set.Ioc (2 * N) t,
      Real.exp (-(b * s)) * deriv (Trunc.chi N) s * f s θ = 0 := by
    intro s hs
    have hs2 : 2 * N ≤ s := le_of_lt hs.1
    have habs : 2 * N ≤ |s| := by rw [abs_of_nonneg (by linarith)]; exact hs2
    rw [deriv_chi_eq_zero_of_two_mul_le hN habs, mul_zero, zero_mul]
  have h2 : (∫ x in Set.Ioc (2 * N) t,
      Real.exp (-(b * x)) * deriv (Trunc.chi N) x * f x θ) = 0 := by
    rw [show (∫ x in Set.Ioc (2 * N) t,
          Real.exp (-(b * x)) * deriv (Trunc.chi N) x * f x θ)
        = ∫ x in Set.Ioc (2 * N) t, (0 : ℝ) from
      setIntegral_congr_fun measurableSet_Ioc fun x hx => hzero x hx]
    simp
  rw [uTrAthree.tailE, intervalIntegral.integral_of_ge ht, h2, neg_zero, mul_zero]

/-- The elementary pointwise inequality behind the two-term domination of `∂_θ²(uTr)`: it keeps
the factor `A²` on the tail term, so that the `phiTr²` of the truncation stays available. -/
theorem key_ineq {A B X Y w : ℝ} (hA : A ^ 2 ≤ 1) (hB : B ^ 2 ≤ 1) (hw : 0 ≤ w) :
    (A * (B * X + Y)) ^ 2 * w ≤ 2 * (X ^ 2 * w) + 2 * (A ^ 2 * (Y ^ 2 * w)) := by
  have h2 : (B * X + Y) ^ 2 ≤ 2 * (B * X) ^ 2 + 2 * Y ^ 2 := by
    nlinarith [sq_nonneg (B * X - Y)]
  have h3 : (B * X) ^ 2 ≤ X ^ 2 := by nlinarith [sq_nonneg X, hB]
  have h4 : (B * X + Y) ^ 2 ≤ 2 * X ^ 2 + 2 * Y ^ 2 := by linarith
  have hA0 : 0 ≤ A ^ 2 := sq_nonneg A
  have hY0 : 0 ≤ Y ^ 2 := sq_nonneg Y
  have hX0 : 0 ≤ X ^ 2 := sq_nonneg X
  nlinarith [mul_nonneg (mul_nonneg hA0 hY0) hw, mul_nonneg hX0 hw, mul_nonneg hA0 hw,
    sq_nonneg (A * (B * X + Y))]

/-! ## The per-`θ` bound for the tail integral -/

/-- The per-`θ` (one-dimensional) bound for the tail integral. -/
theorem tail_per_theta {N b c : ℝ} (hN : 2 ≤ N) (hb : 0 ≤ b) (hc0 : 0 ≤ c)
    (hc : ∀ s, |deriv (Trunc.chi N) s| ≤ c / N) (hNpos : 0 < N)
    (f : ℝ → ℝ → ℝ) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    (∫⁻ t, ENNReal.ofReal (phiTr N t ^ 2 * uTrAthree.tailE N b f t θ ^ 2))
        * ENNReal.ofReal (FlatFT.wE θ)
      ≤ ENNReal.ofReal (40000 * c ^ 2)
        * (ENNReal.ofReal (FlatFT.wE θ)
            * ∫⁻ s in Set.Icc (-(2 * N)) (2 * N), ENNReal.ofReal (f s θ ^ 2)) := by
  have hk0 : ∀ s, 2 * N ≤ |s| → deriv (Trunc.chi N) s = 0 :=
    fun s hs => deriv_chi_eq_zero_of_two_mul_le hNpos hs
  -- restrict the `t`-integral to `[-8192N, 2N]`
  have hstep : ∫⁻ t, ENNReal.ofReal (phiTr N t ^ 2 * uTrAthree.tailE N b f t θ ^ 2)
      ≤ ∫⁻ t in Set.Icc (-(8192 * N)) (2 * N),
          ENNReal.ofReal (uTrAthree.tailE N b f t θ ^ 2) := by
    have hpt : ∀ t : ℝ, ENNReal.ofReal (phiTr N t ^ 2 * uTrAthree.tailE N b f t θ ^ 2)
        ≤ (Set.Icc (-(8192 * N)) (2 * N)).indicator
            (fun t => ENNReal.ofReal (uTrAthree.tailE N b f t θ ^ 2)) t := by
      intro t
      by_cases ht : t ∈ Set.Icc (-(8192 * N)) (2 * N)
      · rw [Set.indicator_of_mem ht,
          ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ phiTr N t ^ 2)]
        calc ENNReal.ofReal (phiTr N t ^ 2) * ENNReal.ofReal (uTrAthree.tailE N b f t θ ^ 2)
            ≤ 1 * ENNReal.ofReal (uTrAthree.tailE N b f t θ ^ 2) := by
              gcongr
              rw [ENNReal.ofReal_le_one]
              have h1 := phiTr_nonneg N t
              have h2 := phiTr_le_one N t
              nlinarith
          _ = ENNReal.ofReal (uTrAthree.tailE N b f t θ ^ 2) := one_mul _
      · rw [Set.indicator_of_notMem ht]
        have hz : phiTr N t ^ 2 * uTrAthree.tailE N b f t θ ^ 2 = 0 := by
          have hcases : t < -(8192 * N) ∨ 2 * N < t := by
            by_contra hcon
            rw [not_or] at hcon
            exact ht ⟨le_of_not_gt hcon.1, le_of_not_gt hcon.2⟩
          rcases hcases with hlt | hgt
          · have hz2 : phiTr N t = 0 :=
              phiTr_eq_zero hNpos (by rw [abs_of_nonpos (by linarith [hlt])]; linarith)
            rw [hz2]; ring
          · rw [tailE_eq_zero_of_le hNpos f (le_of_lt hgt)]; ring
        rw [hz, ENNReal.ofReal_zero]
    rw [← lintegral_indicator measurableSet_Icc]
    exact lintegral_mono hpt
  -- the one-dimensional estimate
  have hone : ∫⁻ t in Set.Icc (-(8192 * N)) (2 * N),
        ENNReal.ofReal (uTrAthree.tailE N b f t θ ^ 2)
      ≤ ENNReal.ofReal (40000 * c ^ 2)
        * ∫⁻ s in Set.Icc (-(2 * N)) (2 * N), ENNReal.ofReal (f s θ ^ 2) := by
    have h := Work.FTS.EllSol.ShiftFT.uTrAthree.TailOneD N b c hN hb hc0 (fun s => deriv (Trunc.chi N) s) hc hk0
      (fun s => f s θ)
    simpa [uTrAthree.tailE] using h
  have hmid : (∫⁻ t, ENNReal.ofReal (phiTr N t ^ 2 * uTrAthree.tailE N b f t θ ^ 2))
      ≤ ENNReal.ofReal (40000 * c ^ 2)
        * ∫⁻ s in Set.Icc (-(2 * N)) (2 * N), ENNReal.ofReal (f s θ ^ 2) :=
    le_trans hstep hone
  calc (∫⁻ t, ENNReal.ofReal (phiTr N t ^ 2 * uTrAthree.tailE N b f t θ ^ 2))
        * ENNReal.ofReal (FlatFT.wE θ)
      ≤ (ENNReal.ofReal (40000 * c ^ 2)
          * ∫⁻ s in Set.Icc (-(2 * N)) (2 * N), ENNReal.ofReal (f s θ ^ 2))
          * ENNReal.ofReal (FlatFT.wE θ) := by gcongr
    _ = ENNReal.ofReal (40000 * c ^ 2)
          * (ENNReal.ofReal (FlatFT.wE θ)
              * ∫⁻ s in Set.Icc (-(2 * N)) (2 * N), ENNReal.ofReal (f s θ ^ 2)) := by ring

/-! ## The main estimate -/

theorem uTr_Athree (b : ℝ) (u : ℝ → ℝ → ℝ) (hb : 0 ≤ b)
    (hu : ContDiffOn ℝ 2 (Function.uncurry u) (Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (h0 : ∀ t : ℝ, u t 0 = 0) (h1 : ∀ t : ℝ, u t (Real.pi / 2) = 0)
    (hI : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ =>
        (Work.Spaces.pth (Work.Spaces.pth u) p.1 p.2) ^ 2
          * Work.FTS.EllSol.FlatFT.wE p.2) (Set.univ ×ˢ Work.Spaces.Iθ)) :
    ∃ K : ℝ, 0 < K ∧ ∀ N ≥ (2 : ℝ),
      MeasureTheory.IntegrableOn (fun p : ℝ × ℝ =>
        (Work.Spaces.pth (Work.Spaces.pth (Work.FTS.EllSol.ShiftFT.uTr N b u)) p.1 p.2) ^ 2
          * Work.FTS.EllSol.FlatFT.wE p.2) (Set.univ ×ˢ Work.Spaces.Iθ) ∧
      (∫ p in Set.univ ×ˢ Work.Spaces.Iθ,
          (Work.Spaces.pth (Work.Spaces.pth (Work.FTS.EllSol.ShiftFT.uTr N b u)) p.1 p.2) ^ 2
            * Work.FTS.EllSol.FlatFT.wE p.2)
        ≤ K * (∫ p in Set.univ ×ˢ Work.Spaces.Iθ,
            (Work.Spaces.pth (Work.Spaces.pth u) p.1 p.2) ^ 2
              * Work.FTS.EllSol.FlatFT.wE p.2) := by
  obtain ⟨c, hc0, hcK⟩ := Work.FTS.EllSol.Trunc.exists_bound_deriv_tk
  refine ⟨2 + 80000 * c ^ 2, by positivity, ?_⟩
  intro N hN
  have hNpos : 0 < N := by linarith
  have hcN : ∀ s : ℝ, |deriv (Trunc.chi N) s| ≤ c / N :=
    fun s => Trunc.abs_deriv_chi_le hcK hNpos s
  -- abbreviations for the two functions occurring in the two slots
  set F : ℝ → ℝ → ℝ := Work.Spaces.pth (Work.Spaces.pth u) with hFdef
  set TE : ℝ → ℝ → ℝ := uTrAthree.tailE N b F with hTEdef
  set Fe : ℝ × ℝ → ℝ :=
    fun p => phiTr N p.1 ^ 2 * (TE p.1 p.2 ^ 2 * FlatFT.wE p.2) with hFedef
  -- the measure identity: the half-strip is the line times the angular measure
  have hmeas : ((volume : Measure (ℝ × ℝ))).restrict (Set.univ ×ˢ Work.Spaces.Iθ)
      = (volume : Measure ℝ).prod ((volume : Measure ℝ).restrict Work.Spaces.Iθ) := by
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]
  -- the `u`-slot, and the a.e. positivity of the weight
  have hI' : IntegrableOn (fun p : ℝ × ℝ => F p.1 p.2 ^ 2 * FlatFT.wE p.2)
      (Set.univ ×ˢ Work.Spaces.Iθ) := hI
  have hθIoo : ∀ᵐ θ ∂((volume : Measure ℝ).restrict Work.Spaces.Iθ),
      θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
    rw [Work.Spaces.Iθ]
    rw [ae_restrict_iff' measurableSet_Icc]
    refine (MeasureTheory.ae_iff).mpr ?_
    refine MeasureTheory.measure_mono_null ?_
      (Set.Finite.measure_zero ((Set.finite_singleton (Real.pi / 2)).insert (0 : ℝ)) volume)
    intro θ hθ
    simp only [Set.mem_setOf_eq, not_imp] at hθ
    obtain ⟨h1, h2⟩ := hθ
    rw [Set.mem_Icc] at h1
    rw [Set.mem_Ioo] at h2
    push_neg at h2
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    by_cases h : θ ≤ 0
    · left; linarith
    · right; push_neg at h; linarith [h2 h, h1.2]
  have haeIoo : ∀ᵐ p ∂(volume.restrict ((Set.univ : Set ℝ) ×ˢ Work.Spaces.Iθ)),
      p.2 ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
    rw [hmeas]
    rw [Measure.ae_prod_iff_ae_ae (μ := (volume : Measure ℝ))
      (ν := (volume : Measure ℝ).restrict Work.Spaces.Iθ)
      (p := fun z : ℝ × ℝ => z.2 ∈ Set.Ioo (0 : ℝ) (Real.pi / 2))
      (show MeasurableSet {z : ℝ × ℝ | z.2 ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)} from by
        have hset : ({z : ℝ × ℝ | z.2 ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)})
            = Set.univ ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
          ext z; simp
        rw [hset]
        exact MeasurableSet.univ.prod measurableSet_Ioo)]
    filter_upwards with t
    exact hθIoo
  have hw : ∀ᵐ p ∂(volume.restrict (Set.univ ×ˢ Work.Spaces.Iθ)), 0 ≤ FlatFT.wE p.2 :=
    haeIoo.mono fun p hp => FlatFT.wE_nonneg (Set.Ioo_subset_Icc_self hp)
  have hFf_nn : 0 ≤ᵐ[volume.restrict (Set.univ ×ˢ Work.Spaces.Iθ)]
      (fun p : ℝ × ℝ => F p.1 p.2 ^ 2 * FlatFT.wE p.2) :=
    hw.mono fun p hp => mul_nonneg (sq_nonneg _) hp
  have hFe_nn : 0 ≤ᵐ[volume.restrict (Set.univ ×ˢ Work.Spaces.Iθ)] Fe :=
    hw.mono fun p hp => by
      rw [hFedef]
      exact mul_nonneg (sq_nonneg _) (mul_nonneg (sq_nonneg _) hp)
  -- the pointwise formula for `∂_θ²(uTr)`
  have hpoint : ∀ t : ℝ, ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      Work.Spaces.pth (Work.Spaces.pth (uTr N b u)) t θ
        = phiTr N t * (Trunc.chi N t * F t θ + TE t θ) := by
    intro t θ hθ
    rw [hTEdef, hFdef]
    exact Work.FTS.EllSol.ShiftFT.uTrAthree.UTrPthPth N b u hu t θ hθ
  -- continuity on the open strip
  have hFcont : ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2) ((Set.univ : Set ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    rw [hFdef]
    exact Work.FTS.EllSol.Trunc.continuousOn_uncurry_pth_pth hu
  have hTEcont : ContinuousOn (fun p : ℝ × ℝ => TE p.1 p.2) ((Set.univ : Set ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    rw [hTEdef, hFdef]
    exact Work.FTS.EllSol.ShiftFT.uTrAthree.TailECont (Work.Spaces.pth (Work.Spaces.pth u)) N b
      (Work.FTS.EllSol.Trunc.continuousOn_uncurry_pth_pth hu)
  have hwEcont : ContinuousOn (fun p : ℝ × ℝ => FlatFT.wE p.2) ((Set.univ : Set ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    Work.FTS.EllSol.Trunc.continuousOn_wE_comp
  have hchicont : ContinuousOn (fun p : ℝ × ℝ => Trunc.chi N p.1) ((Set.univ : Set ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    ((Trunc.chi_contDiff 0 N).continuous.comp continuous_fst).continuousOn
  have hphicont : ContinuousOn (fun p : ℝ × ℝ => phiTr N p.1) ((Set.univ : Set ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    ((phiTr_contDiff 0 N).continuous.comp continuous_fst).continuousOn
  have hFecont : ContinuousOn (fun p : ℝ × ℝ => Fe p) ((Set.univ : Set ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    rw [hFedef]
    exact (hphicont.pow 2).mul ((hTEcont.pow 2).mul hwEcont)
  have hRcont : ContinuousOn (fun p : ℝ × ℝ =>
      (phiTr N p.1 * (Trunc.chi N p.1 * F p.1 p.2 + TE p.1 p.2)) ^ 2 * FlatFT.wE p.2)
      ((Set.univ : Set ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    ((hphicont.mul ((hchicont.mul hFcont).add hTEcont)).pow 2).mul hwEcont
  -- the a.e. equality replacing `∂_θ²(uTr)` by its explicit expression
  have haeeq : (fun p : ℝ × ℝ =>
        (Work.Spaces.pth (Work.Spaces.pth (uTr N b u)) p.1 p.2) ^ 2 * FlatFT.wE p.2)
      =ᵐ[volume.restrict (Set.univ ×ˢ Work.Spaces.Iθ)]
      (fun p : ℝ × ℝ =>
        (phiTr N p.1 * (Trunc.chi N p.1 * F p.1 p.2 + TE p.1 p.2)) ^ 2 * FlatFT.wE p.2) :=
    haeIoo.mono fun p hp => by
      show (Work.Spaces.pth (Work.Spaces.pth (uTr N b u)) p.1 p.2) ^ 2 * FlatFT.wE p.2
        = (phiTr N p.1 * (Trunc.chi N p.1 * F p.1 p.2 + TE p.1 p.2)) ^ 2 * FlatFT.wE p.2
      rw [hpoint p.1 p.2 hp]
  have hFu_aesm : AEStronglyMeasurable (fun p : ℝ × ℝ =>
      (Work.Spaces.pth (Work.Spaces.pth (uTr N b u)) p.1 p.2) ^ 2 * FlatFT.wE p.2)
      (volume.restrict (Set.univ ×ˢ Work.Spaces.Iθ)) :=
    (Work.FTS.EllSol.Trunc.aesm_strip hRcont).congr haeeq.symm
  have hFe_aesm : AEStronglyMeasurable Fe (volume.restrict (Set.univ ×ˢ Work.Spaces.Iθ)) :=
    Work.FTS.EllSol.Trunc.aesm_strip hFecont
  -- the pointwise real bound and its `ℝ≥0∞` counterpart
  have hpt_real : ∀ p : ℝ × ℝ, p.2 ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) →
      (Work.Spaces.pth (Work.Spaces.pth (uTr N b u)) p.1 p.2) ^ 2 * FlatFT.wE p.2
        ≤ 2 * (F p.1 p.2 ^ 2 * FlatFT.wE p.2) + 2 * Fe p := by
    intro p hp
    have hw' : 0 ≤ FlatFT.wE p.2 := FlatFT.wE_nonneg (Set.Ioo_subset_Icc_self hp)
    have hA : (phiTr N p.1) ^ 2 ≤ 1 := by
      have h1 := phiTr_nonneg N p.1
      have h2 := phiTr_le_one N p.1
      nlinarith
    have hB : (Trunc.chi N p.1) ^ 2 ≤ 1 := by
      have h1 := Trunc.chi_nonneg N p.1
      have h2 := Trunc.chi_le_one N p.1
      nlinarith
    have key := key_ineq (A := phiTr N p.1) (B := Trunc.chi N p.1) (X := F p.1 p.2)
      (Y := TE p.1 p.2) (w := FlatFT.wE p.2) hA hB hw'
    rw [hpoint p.1 p.2 hp]
    rw [hFedef]
    exact key
  have hreal_pt := haeIoo.mono hpt_real
  have hFu_nn : 0 ≤ᵐ[volume.restrict (Set.univ ×ˢ Work.Spaces.Iθ)]
      (fun p : ℝ × ℝ =>
        (Work.Spaces.pth (Work.Spaces.pth (uTr N b u)) p.1 p.2) ^ 2 * FlatFT.wE p.2) :=
    hw.mono fun p hp => mul_nonneg (sq_nonneg _) hp
  have hptAE : ∀ᵐ p ∂(volume.restrict (Set.univ ×ˢ Work.Spaces.Iθ)),
      ENNReal.ofReal ((Work.Spaces.pth (Work.Spaces.pth (uTr N b u)) p.1 p.2) ^ 2
          * FlatFT.wE p.2)
        ≤ 2 * ENNReal.ofReal (F p.1 p.2 ^ 2 * FlatFT.wE p.2) + 2 * ENNReal.ofReal (Fe p) := by
    refine haeIoo.mono fun p hp => ?_
    have hw' : 0 ≤ FlatFT.wE p.2 := FlatFT.wE_nonneg (Set.Ioo_subset_Icc_self hp)
    have hFnn : 0 ≤ F p.1 p.2 ^ 2 * FlatFT.wE p.2 := mul_nonneg (sq_nonneg _) hw'
    have hFenn : 0 ≤ Fe p := by
      rw [hFedef]
      exact mul_nonneg (sq_nonneg _) (mul_nonneg (sq_nonneg _) hw')
    calc ENNReal.ofReal ((Work.Spaces.pth (Work.Spaces.pth (uTr N b u)) p.1 p.2) ^ 2
          * FlatFT.wE p.2)
        ≤ ENNReal.ofReal (2 * (F p.1 p.2 ^ 2 * FlatFT.wE p.2) + 2 * Fe p) :=
          ENNReal.ofReal_le_ofReal (hpt_real p hp)
      _ = 2 * ENNReal.ofReal (F p.1 p.2 ^ 2 * FlatFT.wE p.2) + 2 * ENNReal.ofReal (Fe p) := by
          rw [ENNReal.ofReal_add (by positivity) (by positivity),
            ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
            ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
            show ENNReal.ofReal (2 : ℝ) = 2 by norm_num]
  -- the per-`θ` bound and its `θ`-integration (Tonelli)
  have hAEm : AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal (Fe p))
      (volume.prod ((volume : Measure ℝ).restrict Work.Spaces.Iθ)) :=
    aesm_prod_of_continuousOnE hFecont
  have hper : ∀ᵐ θ ∂((volume : Measure ℝ).restrict Work.Spaces.Iθ),
      (∫⁻ t : ℝ, ENNReal.ofReal (Fe (t, θ)))
        ≤ ENNReal.ofReal (40000 * c ^ 2)
            * (ENNReal.ofReal (FlatFT.wE θ)
                * ∫⁻ s in Set.Icc (-(2 * N)) (2 * N), ENNReal.ofReal (F s θ ^ 2)) := by
    refine Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo (fun θ hθ => ?_)
    rw [show (fun t : ℝ => ENNReal.ofReal (Fe (t, θ)))
        = fun t : ℝ => ENNReal.ofReal (phiTr N t ^ 2 * TE t θ ^ 2)
            * ENNReal.ofReal (FlatFT.wE θ) from by
      funext t
      show ENNReal.ofReal (phiTr N t ^ 2 * (TE t θ ^ 2 * FlatFT.wE θ))
        = ENNReal.ofReal (phiTr N t ^ 2 * TE t θ ^ 2) * ENNReal.ofReal (FlatFT.wE θ)
      rw [← mul_assoc, ENNReal.ofReal_mul (by positivity)]]
    rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
    exact tail_per_theta hN hb hc0 hcN hNpos F hθ
  -- the `Fe`-slot is bounded by the `u`-slot
  have hFeInf : (∫⁻ p in Set.univ ×ˢ Work.Spaces.Iθ, ENNReal.ofReal (Fe p))
      ≤ ENNReal.ofReal (40000 * c ^ 2)
        * ∫⁻ p in Set.univ ×ˢ Work.Spaces.Iθ,
            ENNReal.ofReal (F p.1 p.2 ^ 2 * FlatFT.wE p.2) := by
    have hFfae : AEMeasurable (fun p : ℝ × ℝ =>
        ENNReal.ofReal (F p.1 p.2 ^ 2 * FlatFT.wE p.2))
        (volume.prod ((volume : Measure ℝ).restrict Work.Spaces.Iθ)) := by
      have h1 : AEStronglyMeasurable (fun p : ℝ × ℝ => F p.1 p.2 ^ 2 * FlatFT.wE p.2)
          (volume.prod ((volume : Measure ℝ).restrict Work.Spaces.Iθ)) := by
        rw [← hmeas]
        exact hI'.1
      exact ENNReal.measurable_ofReal.comp_aemeasurable h1.aemeasurable
    rw [hmeas]
    rw [lintegral_prod_symm (μ := (volume : Measure ℝ))
        (ν := (volume : Measure ℝ).restrict Work.Spaces.Iθ) _ hAEm]
    rw [lintegral_prod_symm (μ := (volume : Measure ℝ))
        (ν := (volume : Measure ℝ).restrict Work.Spaces.Iθ) _ hFfae]
    have hinner : ∀ θ : ℝ,
        (∫⁻ s : ℝ, ENNReal.ofReal (F s θ ^ 2 * FlatFT.wE θ))
          = (∫⁻ s : ℝ, ENNReal.ofReal (F s θ ^ 2)) * ENNReal.ofReal (FlatFT.wE θ) := by
      intro θ
      rw [show (fun s : ℝ => ENNReal.ofReal (F s θ ^ 2 * FlatFT.wE θ))
          = fun s : ℝ => ENNReal.ofReal (F s θ ^ 2) * ENNReal.ofReal (FlatFT.wE θ) from by
        funext s
        rw [ENNReal.ofReal_mul (sq_nonneg _)]]
      rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
    refine le_trans (lintegral_mono_ae hper) ?_
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    gcongr
    rw [hinner]
    rw [mul_comm (ENNReal.ofReal (FlatFT.wE _))]
    gcongr
    exact MeasureTheory.Measure.restrict_le_self
  -- pass to the real-valued integrals
  have hFf_fin : (∫⁻ p in Set.univ ×ˢ Work.Spaces.Iθ,
        ENNReal.ofReal (F p.1 p.2 ^ 2 * FlatFT.wE p.2)) < ∞ :=
    (hasFiniteIntegral_iff_ofReal hFf_nn).mp hI'.2
  have hFe_lt : (∫⁻ p in Set.univ ×ˢ Work.Spaces.Iθ, ENNReal.ofReal (Fe p)) < ∞ :=
    lt_of_le_of_lt hFeInf (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hFf_fin)
  have hFe_int : Integrable Fe (volume.restrict (Set.univ ×ˢ Work.Spaces.Iθ)) :=
    (lintegral_ofReal_ne_top_iff_integrable hFe_aesm hFe_nn).mp hFe_lt.ne
  have hFf_lin : (∫⁻ p in Set.univ ×ˢ Work.Spaces.Iθ,
        ENNReal.ofReal (F p.1 p.2 ^ 2 * FlatFT.wE p.2))
      = ENNReal.ofReal (∫ p in Set.univ ×ˢ Work.Spaces.Iθ,
          F p.1 p.2 ^ 2 * FlatFT.wE p.2) :=
    (ofReal_integral_eq_lintegral_ofReal hI' hFf_nn).symm
  have hFe_lin : (∫⁻ p in Set.univ ×ˢ Work.Spaces.Iθ, ENNReal.ofReal (Fe p))
      = ENNReal.ofReal (∫ p in Set.univ ×ˢ Work.Spaces.Iθ, Fe p) :=
    (ofReal_integral_eq_lintegral_ofReal hFe_int hFe_nn).symm
  have hFe_real : (∫ p in Set.univ ×ˢ Work.Spaces.Iθ, Fe p)
      ≤ 40000 * c ^ 2 * ∫ p in Set.univ ×ˢ Work.Spaces.Iθ,
          F p.1 p.2 ^ 2 * FlatFT.wE p.2 := by
    have h1 : ENNReal.ofReal (∫ p in Set.univ ×ˢ Work.Spaces.Iθ, Fe p)
        ≤ ENNReal.ofReal (40000 * c ^ 2 * ∫ p in Set.univ ×ˢ Work.Spaces.Iθ,
            F p.1 p.2 ^ 2 * FlatFT.wE p.2) := by
      rw [← hFe_lin, ENNReal.ofReal_mul (by positivity), ← hFf_lin]
      exact hFeInf
    have hnn2 : 0 ≤ 40000 * c ^ 2 * ∫ p in Set.univ ×ˢ Work.Spaces.Iθ,
        F p.1 p.2 ^ 2 * FlatFT.wE p.2 :=
      mul_nonneg (by positivity) (integral_nonneg_of_ae hFf_nn)
    exact (ENNReal.ofReal_le_ofReal_iff hnn2).mp h1
  -- the `Fu`-slot
  have hsum_int : Integrable (fun p : ℝ × ℝ =>
      2 * (F p.1 p.2 ^ 2 * FlatFT.wE p.2) + 2 * Fe p)
      (volume.restrict (Set.univ ×ˢ Work.Spaces.Iθ)) := by
    have h1 : Integrable (fun p : ℝ × ℝ => 2 * (F p.1 p.2 ^ 2 * FlatFT.wE p.2))
        (volume.restrict (Set.univ ×ˢ Work.Spaces.Iθ)) := hI'.const_mul 2
    have h2 : Integrable (fun p : ℝ × ℝ => 2 * Fe p)
        (volume.restrict (Set.univ ×ˢ Work.Spaces.Iθ)) := hFe_int.const_mul 2
    exact h1.add h2
  have hFu_int : Integrable (fun p : ℝ × ℝ =>
      (Work.Spaces.pth (Work.Spaces.pth (uTr N b u)) p.1 p.2) ^ 2 * FlatFT.wE p.2)
      (volume.restrict (Set.univ ×ˢ Work.Spaces.Iθ)) :=
    Integrable.mono' hsum_int hFu_aesm
      ((hFu_nn.and hreal_pt).mono fun p hp => by
        rw [Real.norm_eq_abs, abs_of_nonneg hp.1]
        exact hp.2)
  refine ⟨hFu_int, ?_⟩
  have hmono : (∫ p in Set.univ ×ˢ Work.Spaces.Iθ,
        (Work.Spaces.pth (Work.Spaces.pth (uTr N b u)) p.1 p.2) ^ 2 * FlatFT.wE p.2)
      ≤ ∫ p in Set.univ ×ˢ Work.Spaces.Iθ,
          (2 * (F p.1 p.2 ^ 2 * FlatFT.wE p.2) + 2 * Fe p) :=
    integral_mono_ae hFu_int hsum_int hreal_pt
  have hsplit : (∫ p in Set.univ ×ˢ Work.Spaces.Iθ,
        (2 * (F p.1 p.2 ^ 2 * FlatFT.wE p.2) + 2 * Fe p))
      = 2 * (∫ p in Set.univ ×ˢ Work.Spaces.Iθ, F p.1 p.2 ^ 2 * FlatFT.wE p.2)
        + 2 * (∫ p in Set.univ ×ˢ Work.Spaces.Iθ, Fe p) := by
    rw [integral_add (hI'.const_mul 2) (hFe_int.const_mul 2),
      integral_const_mul, integral_const_mul]
  rw [hsplit] at hmono
  calc (∫ p in Set.univ ×ˢ Work.Spaces.Iθ,
        (Work.Spaces.pth (Work.Spaces.pth (uTr N b u)) p.1 p.2) ^ 2 * FlatFT.wE p.2)
      ≤ 2 * (∫ p in Set.univ ×ˢ Work.Spaces.Iθ, F p.1 p.2 ^ 2 * FlatFT.wE p.2)
        + 2 * (∫ p in Set.univ ×ˢ Work.Spaces.Iθ, Fe p) := hmono
    _ ≤ 2 * (∫ p in Set.univ ×ˢ Work.Spaces.Iθ, F p.1 p.2 ^ 2 * FlatFT.wE p.2)
        + 2 * (40000 * c ^ 2 * ∫ p in Set.univ ×ˢ Work.Spaces.Iθ,
            F p.1 p.2 ^ 2 * FlatFT.wE p.2) := by linarith [hFe_real]
    _ = (2 + 80000 * c ^ 2) * (∫ p in Set.univ ×ˢ Work.Spaces.Iθ,
          F p.1 p.2 ^ 2 * FlatFT.wE p.2) := by ring

end

end Work.FTS.EllSol.ShiftFT
