import Mathlib
import Submission.CDTPlan.InterfacesC
import Submission.Work.CPull.defs
import Submission.CDT.SympDescent
import Submission.Work.CPull.even_descent
import Submission.Work.CPull.evp_subst
import Submission.Work.CPull.evp_add_mul
import Submission.Work.CPull.evp_sympPhi
import Submission.Work.CPull.sympSym_radius
import Submission.Work.CPull.germs
import Submission.Work.CPhi.phiC_analytic
import Submission.Work.CPull.pullbackMero_B2
import Submission.Work.CPull.pullbackMero_B4
import Submission.Work.CPull.pullbackMero_B5
import Submission.Work.CPull.germ_B3
import Submission.Work.CPull.germ_B4
import Submission.Work.CPull.pullbackMero_deriv_iter
import Submission.Work.CPull.deriv_phiC_zeros_finite

/-! # Area CPull — meromorphic pullbacks of the 17 functions along `φ_C` (`CPullbacks`)

Main theorem `Work.CPull.c_pullbacks`, assembled from the case analysis of `seventeen`
(`Submission.CDTPlan.seventeen`) and the lift `Φ` of `phiC (z^2)` (`PhiLift`).

The engine is `pullbackMero_of_even`: if the germ of `Σ f_n Ψ(z^2)^n` at `0` is the even
holomorphic function `E`, then the pullback of `f` along `Ψ` is meromorphic (`P = 1`).
The pullback series of the 17 functions are computed through the lift `Φ` (`hΦ`) and the
symmetrization `Sym⁺` (`Submission.CDT.sympSym_subst`).

Proved here: `pullbackMero_of_even` (reduction), `lift_neg_eq` (`Φ(-z) = Φ z/(Φ z - 1)`),
the coefficient estimates `tsum_sympPhi_abs`, `tsum_sympY_abs` for the two `σ`-scales used by
`evp_subst`, and the `G = Sym⁺P` case `pullbackMero_GC` (the whole chain
`evp (Sym⁺P) (y(x)) = evp P x + evp P (x/(x-1))` via `evp_subst`, `evp_add_mul`, `evp_sympPhi`
and the lift relation), using the delegated lemmas `even_descent`, `evp_subst`, `evp_add_mul`,
`evp_sympPhi`, `sympSym_radius`.

**Remaining for the other 16 functions** (see `HANDOFF.md`): `B1` (trivial), `B2` (entire
series: direct composition), `B3, B4, B5` (descent identities of `-log(1-x)^2/2`,
`(x-φ(x))(2Li₂(x)+log(1-x)^2/2)`, `xJ/(x-1)`), `B6, B7` and the six integrals (primitives),
and the three derivatives (division by `deriv phiC` + a polynomial denominator built from the
finite zero set of `deriv phiC` on the disc).
-/

namespace Work.CPull

open Submission.CDTPlan
open PowerSeries
open scoped Topology BigOperators



/-! ## Φ facts -/

/-- From the two relations of the lift: `Φ (-z) = Φ z / (Φ z - 1)`. -/
lemma lift_neg_eq (Φ : ℂ → ℂ)
    (h : ∀ z ∈ Metric.ball (0 : ℂ) 1, Φ z + Φ (-z) = phiC (z ^ 2) ∧ Φ z * Φ (-z) = phiC (z ^ 2))
    (z : ℂ) (hz : z ∈ Metric.ball (0 : ℂ) 1) : Φ (-z) = Φ z / (Φ z - 1) := by
  have h1 := (h z hz).1
  have h2 := (h z hz).2
  have hne : Φ z - 1 ≠ 0 := by
    intro hc
    have hz1 : Φ z = 1 := sub_eq_zero.mp hc
    rw [hz1, one_mul] at h2
    rw [hz1] at h1
    have : (1 : ℂ) = 0 := by linear_combination h1 - h2
    exact one_ne_zero this
  have hsum : Φ z + Φ (-z) = Φ z * Φ (-z) := by rw [h1, h2]
  have key : Φ z - Φ (-z) * (Φ z - 1) = 0 := by
    have : Φ z - Φ (-z) * (Φ z - 1) = Φ z + Φ (-z) - Φ z * Φ (-z) := by ring
    rw [this, hsum]; ring
  rw [eq_div_iff hne]
  exact (sub_eq_zero.mp key).symm

/-! ## square roots -/

/-! ## the reduction: an even germ on `z ^ 2` gives a meromorphic pullback -/

lemma pullbackMero_of_even {Ψ : ℂ → ℂ} {f : PowerSeries ℚ} {E : ℂ → ℂ}
    (hE : DifferentiableOn ℂ E (Metric.ball 0 1))
    (heven : ∀ z ∈ Metric.ball (0 : ℂ) 1, E (-z) = E z)
    (hgerm : ∀ᶠ z in 𝓝 (0 : ℂ),
      HasSum (fun n : ℕ => ((PowerSeries.coeff n f : ℚ) : ℂ) * Ψ (z ^ 2) ^ n) (E z)) :
    PullbackMero f Ψ := by
  obtain ⟨N, hN, hNz⟩ := even_descent E hE heven
  refine ⟨1, N, by simp, hN, ?_⟩
  obtain ⟨ε, hεpos, hε⟩ := Metric.eventually_nhds_iff.mp hgerm
  set r : ℝ := min ε 1 with hrdef
  have hrpos : 0 < r := lt_min hεpos one_pos
  refine Filter.Eventually.mono
    (Metric.ball_mem_nhds (0 : ℂ) (by positivity : (0:ℝ) < r ^ 2)) ?_
  intro w hw
  have hwn : ‖w‖ < r ^ 2 := by simpa [dist_eq_norm] using hw
  set z : ℂ := Complex.sqrt w with hzdef
  have hzsq : z ^ 2 = w := by rw [hzdef]; exact sq_sqrt_c w
  have hzn : ‖z‖ ^ 2 = ‖w‖ := by rw [← norm_pow, hzsq]
  have hzr : ‖z‖ < r := by
    have h1 : ‖z‖ ^ 2 < r ^ 2 := by rw [hzn]; exact hwn
    nlinarith [norm_nonneg z, hrpos, h1]
  have hzmem : z ∈ Metric.ball (0 : ℂ) 1 := by
    rw [Metric.mem_ball, dist_zero_right]
    exact lt_of_lt_of_le hzr (min_le_right _ _)
  have hzeps : dist z 0 < ε := by
    rw [dist_zero_right]
    exact lt_of_lt_of_le hzr (min_le_left _ _)
  have h := hε hzeps
  rw [hzsq] at h
  rw [← hNz z hzmem] at h
  rw [hzsq] at h
  simpa using h





/-! ## coefficient facts for `sympPhi` and `sympY` -/

lemma norm_coeff_sympY_le (j : ℕ) :
    ‖((PowerSeries.coeff j Submission.CDT.sympY : ℚ) : ℂ)‖ ≤ 1 := by
  rw [norm_rat_cast_complex, coeff_sympY_eq]
  by_cases h0 : j = 0
  · simp [h0]
  by_cases h1 : j = 1
  · simp [h0, h1]
  · simp [h0, h1]

lemma norm_coeff_sympPhi_le (j : ℕ) :
    ‖((PowerSeries.coeff j Submission.CDT.sympPhi : ℚ) : ℂ)‖ ≤ 1 := by
  rw [coeff_sympPhi_eq]
  split <;> norm_num

lemma tsum_sympPhi_abs (x : ℂ) (hx : ‖x‖ < 1) :
    (∑' j : ℕ, ‖((PowerSeries.coeff j Submission.CDT.sympPhi : ℚ) : ℂ)‖ * ‖x‖ ^ j)
      ≤ ‖x‖ * (1 - ‖x‖)⁻¹ := by
  have hgeo : Summable (fun j : ℕ => ‖x‖ ^ j) :=
    summable_geometric_iff_norm_lt_one.mpr (by rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg x)]; exact hx)
  have hfin : Summable (fun j : ℕ => if j = 0 then (1:ℝ) else 0) :=
    (hasSum_ite_eq 0 (1:ℝ)).summable
  have hb : Summable (fun j : ℕ =>
      ‖((PowerSeries.coeff j Submission.CDT.sympPhi : ℚ) : ℂ)‖ * ‖x‖ ^ j) :=
    Summable.of_nonneg_of_le (fun j => by positivity)
      (fun j => mul_le_of_le_one_left (by positivity) (norm_coeff_sympPhi_le j)) hgeo
  have hg : ∀ j : ℕ, ‖((PowerSeries.coeff j Submission.CDT.sympPhi : ℚ) : ℂ)‖ * ‖x‖ ^ j
      ≤ ‖x‖ ^ j - (if j = 0 then (1:ℝ) else 0) := by
    intro j
    rw [norm_rat_cast_complex, coeff_sympPhi_eq]
    rcases eq_or_ne j 0 with rfl | hj
    · simp
    · simp [hj]
  calc (∑' j : ℕ, ‖((PowerSeries.coeff j Submission.CDT.sympPhi : ℚ) : ℂ)‖ * ‖x‖ ^ j)
      ≤ ∑' j : ℕ, (‖x‖ ^ j - (if j = 0 then (1:ℝ) else 0)) :=
        Summable.tsum_le_tsum hg hb (hgeo.sub hfin)
    _ = (∑' j : ℕ, ‖x‖ ^ j) - ∑' j : ℕ, (if j = 0 then (1:ℝ) else 0) := hgeo.tsum_sub hfin
    _ = (1 - ‖x‖)⁻¹ - 1 := by
        rw [tsum_geometric_of_norm_lt_one (by rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg x)]; exact hx),
          tsum_ite_eq]
    _ = ‖x‖ * (1 - ‖x‖)⁻¹ := by
        have h1 : (1:ℝ) - ‖x‖ ≠ 0 := by linarith
        field_simp
        ring

lemma tsum_sympY_abs (x : ℂ) (hx : ‖x‖ < 1) :
    (∑' j : ℕ, ‖((PowerSeries.coeff j Submission.CDT.sympY : ℚ) : ℂ)‖ * ‖x‖ ^ j)
      ≤ ‖x‖ ^ 2 * (1 - ‖x‖)⁻¹ := by
  have hgeo : Summable (fun j : ℕ => ‖x‖ ^ j) :=
    summable_geometric_iff_norm_lt_one.mpr (by rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg x)]; exact hx)
  have hfin1 : Summable (fun j : ℕ => if j = 0 then (1:ℝ) else 0) :=
    (hasSum_ite_eq 0 (1:ℝ)).summable
  have hfin2 : Summable (fun j : ℕ => if j = 1 then ‖x‖ else 0) :=
    (hasSum_ite_eq 1 ‖x‖).summable
  have hb : Summable (fun j : ℕ =>
      ‖((PowerSeries.coeff j Submission.CDT.sympY : ℚ) : ℂ)‖ * ‖x‖ ^ j) :=
    Summable.of_nonneg_of_le (fun j => by positivity)
      (fun j => mul_le_of_le_one_left (by positivity) (norm_coeff_sympY_le j)) hgeo
  have hg : ∀ j : ℕ, ‖((PowerSeries.coeff j Submission.CDT.sympY : ℚ) : ℂ)‖ * ‖x‖ ^ j
      ≤ ‖x‖ ^ j - (if j = 0 then (1:ℝ) else 0) - (if j = 1 then ‖x‖ else 0) := by
    intro j
    rw [norm_rat_cast_complex, coeff_sympY_eq]
    by_cases h0 : j = 0
    · simp [h0]
    by_cases h1 : j = 1
    · simp [h0, h1]
    · simp [h0, h1]
  calc (∑' j : ℕ, ‖((PowerSeries.coeff j Submission.CDT.sympY : ℚ) : ℂ)‖ * ‖x‖ ^ j)
      ≤ ∑' j : ℕ, (‖x‖ ^ j - (if j = 0 then (1:ℝ) else 0) - (if j = 1 then ‖x‖ else 0)) :=
        Summable.tsum_le_tsum hg hb ((hgeo.sub hfin1).sub hfin2)
    _ = (∑' j : ℕ, ‖x‖ ^ j) - ∑' j : ℕ, (if j = 0 then (1:ℝ) else 0)
        - ∑' j : ℕ, (if j = 1 then ‖x‖ else 0) := by
        rw [(hgeo.sub hfin1).tsum_sub hfin2, hgeo.tsum_sub hfin1]
    _ = (1 - ‖x‖)⁻¹ - 1 - ‖x‖ := by
        rw [tsum_geometric_of_norm_lt_one (by rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg x)]; exact hx),
          tsum_ite_eq, tsum_ite_eq]
    _ = ‖x‖ ^ 2 * (1 - ‖x‖)⁻¹ := by
        have h1 : (1:ℝ) - ‖x‖ ≠ 0 := by linarith
        field_simp
        ring

/-! ## the `G` case -/

theorem germ_GC_even (hL : PLiftCont) (hΦ : PhiLift) (hP : PsiCFacts) (m n : ℕ)
    (ra rb rab r0 : ℤ) (hadm : CAdm m n) (hrel : CRel m n ra rb rab r0) :
    ∃ E : ℂ → ℂ, DifferentiableOn ℂ E (Metric.ball 0 1) ∧
      (∀ z ∈ Metric.ball (0 : ℂ) 1, E (-z) = E z) ∧
      ∀ᶠ z in 𝓝 (0 : ℂ), HasSum (fun k : ℕ =>
        ((PowerSeries.coeff k (GC m n ra rb rab r0) : ℚ) : ℂ) * phiC (z ^ 2) ^ k) (E z) := by
  classical
  obtain ⟨Φ, hΦdiff, hΦrel, hΦzero⟩ := hΦ
  obtain ⟨F, hFdiff, hFsum⟩ := hL m n ra rb rab r0 hadm hrel Φ hΦdiff hΦrel hΦzero
  have hneg : Set.MapsTo (fun z : ℂ => -z) (Metric.ball 0 1) (Metric.ball 0 1) := by
    intro z hz
    rw [Metric.mem_ball, dist_zero_right] at hz ⊢
    simpa using hz
  refine ⟨fun z => F z + F (-z),
    hFdiff.add (hFdiff.comp differentiable_neg.differentiableOn hneg), ?_, ?_⟩
  · intro z hz
    simp only [neg_neg]
    ring
  · -- the germ identity
    obtain ⟨V, hVmem, hV⟩ := Filter.eventually_iff_exists_mem.mp hFsum
    obtain ⟨δ, hδpos, hδsub⟩ := Metric.mem_nhds_iff.mp hVmem
    set δ₁ : ℝ := min δ 1 with hδ₁def
    have hδ₁pos : 0 < δ₁ := lt_min hδpos one_pos
    have hδ₁le : δ₁ ≤ δ := min_le_left _ _
    have hδ₁sub : Metric.ball (0 : ℂ) δ₁ ⊆ V := fun z hz =>
      hδsub (Metric.ball_subset_ball hδ₁le hz)
    -- a reference point of `V` different from `0`
    have hz₁n : ‖((δ₁ / 2 : ℝ) : ℂ)‖ = δ₁ / 2 := by
      have h2 : ‖((δ₁ / 2 : ℝ) : ℂ)‖ ^ 2 = (δ₁ / 2) ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_ofReal]; ring
      nlinarith [norm_nonneg ((δ₁ / 2 : ℝ) : ℂ), h2, hδ₁pos]
    have hz₁mem : ((δ₁ / 2 : ℝ) : ℂ) ∈ V := by
      apply hδ₁sub
      rw [Metric.mem_ball, dist_zero_right, hz₁n]
      linarith
    have hz₁ball : ((δ₁ / 2 : ℝ) : ℂ) ∈ Metric.ball (0 : ℂ) 1 := by
      rw [Metric.mem_ball, dist_zero_right, hz₁n]
      have h : δ₁ / 2 < 1 := by
        have h2 : δ₁ ≤ 1 := min_le_right _ _
        linarith
      exact h
    have hz₁ne : ((δ₁ / 2 : ℝ) : ℂ) ≠ 0 := by
      simp only [ne_eq, Complex.ofReal_eq_zero]
      positivity
    set ρ : ℝ := ‖Φ ((δ₁ / 2 : ℝ) : ℂ)‖ with hρdef
    have hρpos : 0 < ρ := by
      rw [hρdef, norm_pos_iff]
      exact fun h => hz₁ne (hΦzero _ hz₁ball h)
    -- summability at the reference scale
    have hPsumρ : Summable fun k : ℕ =>
        ‖((PowerSeries.coeff k (PC m n ra rb rab r0) : ℚ) : ℂ)‖ * ρ ^ k := by
      have h := (hV _ hz₁mem).summable.norm
      simpa [ρ, norm_mul, norm_pow] using h
    -- the geometric coefficient bound for `P`
    obtain ⟨K, hK⟩ := Filter.eventually_atTop.mp
      (hPsumρ.tendsto_atTop_zero.eventually (eventually_lt_nhds (show (0:ℝ) < 1 by norm_num)))
    set C : ℝ := max 1 ((Finset.range (K + 1)).sup' ⟨0, by simp⟩
      (fun k => ‖((PowerSeries.coeff k (PC m n ra rb rab r0) : ℚ) : ℂ)‖ * ρ ^ k)) with hCdef
    have hCpos : 0 < C := lt_of_lt_of_le one_pos (le_max_left _ _)
    have hPbound : ∀ k : ℕ,
        ‖((PowerSeries.coeff k (PC m n ra rb rab r0) : ℚ) : ℂ)‖
          ≤ C * (ρ⁻¹) ^ k := by
      intro k
      have h1 : ‖((PowerSeries.coeff k (PC m n ra rb rab r0) : ℚ) : ℂ)‖ * ρ ^ k ≤ C := by
        rcases lt_or_ge k K with hk | hk
        · refine le_trans (Finset.le_sup' (s := Finset.range (K + 1))
            (f := fun k => ‖((PowerSeries.coeff k (PC m n ra rb rab r0) : ℚ) : ℂ)‖ * ρ ^ k)
            (Finset.mem_range.mpr (by omega))) (le_max_right _ _)
        · exact le_trans (le_of_lt (hK k hk)) (le_max_left _ _)
      have h2 : ρ ^ k * ρ⁻¹ ^ k = 1 := by
        rw [← mul_pow, mul_inv_cancel₀ (ne_of_gt hρpos), one_pow]
      calc ‖((PowerSeries.coeff k (PC m n ra rb rab r0) : ℚ) : ℂ)‖
          = ‖((PowerSeries.coeff k (PC m n ra rb rab r0) : ℚ) : ℂ)‖ * (ρ ^ k * ρ⁻¹ ^ k) := by
              rw [h2, mul_one]
        _ = (‖((PowerSeries.coeff k (PC m n ra rb rab r0) : ℚ) : ℂ)‖ * ρ ^ k) * ρ⁻¹ ^ k := by ring
        _ ≤ C * ρ⁻¹ ^ k := mul_le_mul_of_nonneg_right h1 (by positivity)
    obtain ⟨C', R', hC'pos, hR'pos, hGC⟩ :=
      sympSym_radius (PC m n ra rb rab r0) C ρ⁻¹ hCpos (by positivity) hPbound
    -- the small neighbourhood
    set ε : ℝ := min (1/4) (min (ρ/4) (1/(4*(R'+1)))) with hεdef
    have hεpos : 0 < ε := lt_min (by norm_num) (lt_min (by positivity) (by positivity))
    have hεle4 : ε ≤ 1/4 := min_le_left _ _
    have hεleρ : ε ≤ ρ/4 := le_trans (min_le_right _ _) (min_le_left _ _)
    have hεleR : ε ≤ 1/(4*(R'+1)) := le_trans (min_le_right _ _) (min_le_right _ _)
    have hΦ00 : Φ 0 = 0 := by
      have hmem : (0 : ℂ) ∈ Metric.ball (0 : ℂ) 1 := by simp [Metric.mem_ball]
      have h1 := (hΦrel 0 hmem).1
      have h2 : phiC 0 = 0 := by
        show hauptH (psiC 0) = 0
        rw [hP.2.2.1]
        simp [Submission.CDTPlan.hauptH]
      rw [show (0 : ℂ) ^ 2 = 0 from by norm_num, h2, neg_zero] at h1
      linear_combination h1 / 2
    have hΦcont : ContinuousAt Φ 0 :=
      hΦdiff.continuousOn.continuousAt (Metric.ball_mem_nhds 0 one_pos)
    obtain ⟨r1, hr1pos, hr1⟩ := Metric.continuousAt_iff.mp hΦcont ε hεpos
    have hrpos : 0 < min (min δ₁ r1) 1 :=
      lt_min (lt_min hδ₁pos hr1pos) one_pos
    refine Filter.Eventually.mono (Metric.ball_mem_nhds (0 : ℂ) hrpos) ?_
    intro z hz
    have hzr : ‖z‖ < min (min δ₁ r1) 1 := by simpa [dist_eq_norm] using hz
    have hzδ : ‖z‖ < δ₁ := lt_of_lt_of_le hzr (le_trans (min_le_left _ _) (min_le_left _ _))
    have hzr1 : ‖z‖ < r1 := lt_of_lt_of_le hzr (le_trans (min_le_left _ _) (min_le_right _ _))
    have hz1 : ‖z‖ < 1 := lt_of_lt_of_le hzr (min_le_right _ _)
    have hzV : z ∈ V := hδ₁sub (by rwa [Metric.mem_ball, dist_zero_right])
    have hnzV : -z ∈ V := by
      apply hδ₁sub
      rw [Metric.mem_ball, dist_zero_right, norm_neg]
      exact hzδ
    have hzball : z ∈ Metric.ball (0 : ℂ) 1 := by
      rw [Metric.mem_ball, dist_zero_right]; exact hz1
    have hΦzlt : ‖Φ z‖ < ε := by
      have h : dist (Φ z) (Φ 0) < ε := hr1 (by simpa [dist_eq_norm] using hzr1)
      rw [hΦ00, dist_zero_right] at h
      exact h
    have hΦnzlt : ‖Φ (-z)‖ < ε := by
      have h : dist (Φ (-z)) (Φ 0) < ε := hr1 (by rw [dist_eq_norm, sub_zero, norm_neg]; exact hzr1)
      rw [hΦ00, dist_zero_right] at h
      exact h
    rw [(hΦrel z hzball).2.symm]
    have hΦz1 : ‖Φ z‖ < 1 := by linarith [hεle4, hεpos]
    -- bounds on the two `σ`'s
    have hσPhi : (∑' j : ℕ, ‖((PowerSeries.coeff j Submission.CDT.sympPhi : ℚ) : ℂ)‖ * ‖Φ z‖ ^ j) ≤ ρ := by
      refine le_trans (tsum_sympPhi_abs (Φ z) hΦz1) ?_
      have h3 : (1 : ℝ) - ‖Φ z‖ ≥ 3/4 := by linarith [hεle4, hεpos]
      have h4 : (1 - ‖Φ z‖)⁻¹ ≤ 4/3 := by
        rw [inv_le_comm₀ (by linarith [norm_nonneg (Φ z), hΦz1]) (by norm_num)]
        linarith
      calc ‖Φ z‖ * (1 - ‖Φ z‖)⁻¹ ≤ (ρ/4) * (4/3) :=
            mul_le_mul (le_trans hΦzlt.le hεleρ) h4 (by positivity) (by positivity)
        _ ≤ ρ := by nlinarith [hρpos]
    have hσY : R' * (∑' j : ℕ, ‖((PowerSeries.coeff j Submission.CDT.sympY : ℚ) : ℂ)‖ * ‖Φ z‖ ^ j) ≤ 1/2 := by
      have h3 : (1 - ‖Φ z‖)⁻¹ ≤ 4/3 := by
        rw [inv_le_comm₀ (by linarith [norm_nonneg (Φ z), hΦz1]) (by norm_num)]
        linarith [hεle4, hεpos]
      have h4 : ‖Φ z‖ ^ 2 * (1 - ‖Φ z‖)⁻¹ ≤ ε ^ 2 * (4/3) := by
        refine mul_le_mul ?_ h3 (by positivity) (by positivity)
        rw [pow_two, pow_two]
        exact mul_self_le_mul_self (norm_nonneg _) hΦzlt.le
      have h5 : R' * (ε ^ 2 * (4/3)) ≤ 1/2 := by
        have hR1 : R'/(R'+1) ≤ 1 := by
          rw [div_le_one (by positivity)]; linarith
        have h6 : ε ^ 2 ≤ ε * (1/(4*(R'+1))) := by
          rw [pow_two]
          exact mul_le_mul_of_nonneg_left hεleR hεpos.le
        have h7 : R' * (ε ^ 2 * (4/3)) ≤ R' * ((ε * (1/(4*(R'+1)))) * (4/3)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h6 (by norm_num)) hR'pos.le
        have h8 : R' * ((ε * (1/(4*(R'+1)))) * (4/3)) = ε * (R'/(R'+1)) * (1/3) := by
          field_simp <;> ring
        have h9 : ε * (R'/(R'+1)) * (1/3) ≤ (1/4) * 1 * (1/3) := by
          refine mul_le_mul_of_nonneg_right ?_ (by norm_num)
          exact mul_le_mul hεle4 hR1 (by positivity) (by norm_num)
        rw [h8] at h7
        linarith [h7, h9]
      calc R' * (∑' j : ℕ, ‖((PowerSeries.coeff j Submission.CDT.sympY : ℚ) : ℂ)‖ * ‖Φ z‖ ^ j)
          ≤ R' * (‖Φ z‖ ^ 2 * (1 - ‖Φ z‖)⁻¹) :=
            mul_le_mul_of_nonneg_left (tsum_sympY_abs (Φ z) hΦz1) hR'pos.le
        _ ≤ R' * (ε ^ 2 * (4/3)) := mul_le_mul_of_nonneg_left h4 hR'pos.le
        _ ≤ 1/2 := h5
    -- the summability hypotheses of `evp_subst`
    have hYsum : Summable fun j : ℕ => ‖((PowerSeries.coeff j Submission.CDT.sympY : ℚ) : ℂ)‖ * ‖Φ z‖ ^ j :=
      Summable.of_nonneg_of_le (fun j => by positivity)
        (fun j => mul_le_of_le_one_left (by positivity) (norm_coeff_sympY_le j))
        (summable_geometric_iff_norm_lt_one.mpr
          (by rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]; exact hΦz1))
    have hPhisum : Summable fun j : ℕ => ‖((PowerSeries.coeff j Submission.CDT.sympPhi : ℚ) : ℂ)‖ * ‖Φ z‖ ^ j :=
      Summable.of_nonneg_of_le (fun j => by positivity)
        (fun j => mul_le_of_le_one_left (by positivity) (norm_coeff_sympPhi_le j))
        (summable_geometric_iff_norm_lt_one.mpr
          (by rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]; exact hΦz1))
    have hGCsum : Summable fun k : ℕ => ‖((PowerSeries.coeff k (GC m n ra rb rab r0) : ℚ) : ℂ)‖ *
        (∑' j : ℕ, ‖((PowerSeries.coeff j Submission.CDT.sympY : ℚ) : ℂ)‖ * ‖Φ z‖ ^ j) ^ k := by
      have hb : ∀ k : ℕ, ‖((PowerSeries.coeff k (GC m n ra rb rab r0) : ℚ) : ℂ)‖ *
          (∑' j : ℕ, ‖((PowerSeries.coeff j Submission.CDT.sympY : ℚ) : ℂ)‖ * ‖Φ z‖ ^ j) ^ k
          ≤ C' * (1/2) ^ k := by
        intro k
        have hRσ : R' ^ k * (∑' j : ℕ, ‖((PowerSeries.coeff j Submission.CDT.sympY : ℚ) : ℂ)‖ * ‖Φ z‖ ^ j) ^ k
            ≤ (1/2) ^ k := by
          have h1 : (R' * (∑' j : ℕ, ‖((PowerSeries.coeff j Submission.CDT.sympY : ℚ) : ℂ)‖ * ‖Φ z‖ ^ j)) ^ k
              ≤ (1/2) ^ k := by
            exact pow_le_pow_left₀ (by positivity) hσY k
          rwa [mul_pow] at h1
        calc ‖((PowerSeries.coeff k (GC m n ra rb rab r0) : ℚ) : ℂ)‖ *
              (∑' j : ℕ, ‖((PowerSeries.coeff j Submission.CDT.sympY : ℚ) : ℂ)‖ * ‖Φ z‖ ^ j) ^ k
            ≤ (C' * R' ^ k) *
              (∑' j : ℕ, ‖((PowerSeries.coeff j Submission.CDT.sympY : ℚ) : ℂ)‖ * ‖Φ z‖ ^ j) ^ k :=
              mul_le_mul_of_nonneg_right (by simpa [GC] using hGC k) (by positivity)
          _ = C' * (R' ^ k *
              (∑' j : ℕ, ‖((PowerSeries.coeff j Submission.CDT.sympY : ℚ) : ℂ)‖ * ‖Φ z‖ ^ j) ^ k) := by ring
          _ ≤ C' * (1/2) ^ k := mul_le_mul_of_nonneg_left hRσ hC'pos.le
      refine Summable.of_nonneg_of_le (fun k => by positivity) hb ?_
      exact (summable_geometric_iff_norm_lt_one.mpr (by norm_num : |(1/2 : ℝ)| < 1)).mul_left C'

    -- the chain of evaluations
    have hysym : evp Submission.CDT.sympY (Φ z) = Φ z * Φ (-z) := by
      rw [(evp_sympPhi (Φ z) hΦz1).2, lift_neg_eq Φ hΦrel z hzball]
      field_simp
    have h1 := (evp_subst (GC m n ra rb rab r0) Submission.CDT.sympY (Φ z)
      (by rw [Submission.CDT.sympY, map_mul, PowerSeries.constantCoeff_X, zero_mul])
      hYsum hGCsum).2
    rw [hysym] at h1
    have h2 := Submission.CDT.sympSym_subst (PC m n ra rb rab r0)
    have h3 := evp_subst (PC m n ra rb rab r0) Submission.CDT.sympPhi (Φ z)
      (by rw [Submission.CDT.sympPhi, map_mul, PowerSeries.constantCoeff_X, zero_mul])
      hPhisum (by
        refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hPsumρ
        have : (∑' j : ℕ, ‖((PowerSeries.coeff j Submission.CDT.sympPhi : ℚ) : ℂ)‖ * ‖Φ z‖ ^ j) ^ n
            ≤ ρ ^ n := pow_le_pow_left₀ (by positivity) hσPhi n
        exact mul_le_mul_of_nonneg_left this (by positivity))
    have h4 := (evp_add_mul (PC m n ra rb rab r0)
      ((PC m n ra rb rab r0).subst Submission.CDT.sympPhi) (Φ z)
      (hV z hzV).summable (h3.1)).1
    have h5 : evp ((GC m n ra rb rab r0).subst Submission.CDT.sympY) (Φ z)
        = evp (PC m n ra rb rab r0) (Φ z) + evp (PC m n ra rb rab r0) (Φ (-z)) := by
      rw [show GC m n ra rb rab r0 = Submission.CDT.sympSym (PC m n ra rb rab r0) from rfl,
        h2, h4, h3.2, (evp_sympPhi (Φ z) hΦz1).1, lift_neg_eq Φ hΦrel z hzball]
    have h6 : evp (PC m n ra rb rab r0) (Φ z) = F z := (hV z hzV).tsum_eq
    have h7 : evp (PC m n ra rb rab r0) (Φ (-z)) = F (-z) := (hV (-z) hnzV).tsum_eq
    have hval : evp (GC m n ra rb rab r0) (Φ z * Φ (-z)) = F z + F (-z) := by
      rw [← h1, h5, h6, h7]
    -- summability of the `GC` series at this point
    have hy : R' * ‖Φ z * Φ (-z)‖ < 1 := by
      have hle : ‖Φ z * Φ (-z)‖ ≤ ε * ε := by
        rw [norm_mul]
        exact mul_le_mul hΦzlt.le hΦnzlt.le (norm_nonneg _) hεpos.le
      have h6 : R' * (ε * ε) ≤ 1/2 := by
        have hε4 : ε ≤ 1/(4*(R'+1)) := hεleR
        have h7 : ε * ε ≤ ε * (1/(4*(R'+1))) := mul_le_mul_of_nonneg_left hε4 hεpos.le
        have h8 : R' * (ε * ε) ≤ R' * (ε * (1/(4*(R'+1)))) := mul_le_mul_of_nonneg_left h7 hR'pos.le
        have h9 : R' * (ε * (1/(4*(R'+1)))) ≤ 1/4 := by
          have h10 : ε * (1/(4*(R'+1))) ≤ (1/4) * (1/(4*(R'+1))) :=
            mul_le_mul_of_nonneg_right hεle4 (by positivity)
          have h11 : R' * ((1/4) * (1/(4*(R'+1)))) ≤ 1/4 := by
            rw [show R' * ((1/4) * (1/(4*(R'+1)))) = R' / (16*(R'+1)) by field_simp <;> ring]
            rw [div_le_iff₀ (by positivity)]
            nlinarith [hR'pos]
          linarith [h10, h11, mul_le_mul_of_nonneg_left h10 hR'pos.le, hR'pos]
        linarith [h8, h9]
      nlinarith [hle, hR'pos, h6, hεpos]
    have hyC : Summable fun k : ℕ => ((PowerSeries.coeff k (GC m n ra rb rab r0) : ℚ) : ℂ) *
        (Φ z * Φ (-z)) ^ k := by
      refine Summable.of_norm_bounded (g := fun k : ℕ => C' * (R' * ‖Φ z * Φ (-z)‖) ^ k) ?_ ?_
      · exact (summable_geometric_iff_norm_lt_one.mpr
          (by rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]; exact hy)).mul_left C'
      · intro k
        have h1 : ‖((PowerSeries.coeff k (GC m n ra rb rab r0) : ℚ) : ℂ) *
            (Φ z * Φ (-z)) ^ k‖
            = ‖((PowerSeries.coeff k (GC m n ra rb rab r0) : ℚ) : ℂ)‖ * ‖Φ z * Φ (-z)‖ ^ k := by
          rw [norm_mul, norm_pow]
        rw [h1]
        calc ‖((PowerSeries.coeff k (GC m n ra rb rab r0) : ℚ) : ℂ)‖ * ‖Φ z * Φ (-z)‖ ^ k
            ≤ (C' * R' ^ k) * ‖Φ z * Φ (-z)‖ ^ k :=
              mul_le_mul_of_nonneg_right (by simpa [GC] using hGC k) (by positivity)
          _ = C' * (R' * ‖Φ z * Φ (-z)‖) ^ k := by rw [mul_pow]; ring
    have hfinal : HasSum (fun k : ℕ =>
        ((PowerSeries.coeff k (GC m n ra rb rab r0) : ℚ) : ℂ) * (Φ z * Φ (-z)) ^ k) (F z + F (-z)) := by
      have := hyC.hasSum
      rwa [show (∑' k : ℕ, ((PowerSeries.coeff k (GC m n ra rb rab r0) : ℚ) : ℂ) *
          (Φ z * Φ (-z)) ^ k) = F z + F (-z) from hval] at this
    exact hfinal

/-- The `G = Sym⁺P` case: `PullbackMero (GC …) phiC`. -/
theorem pullbackMero_GC (hL : PLiftCont) (hΦ : PhiLift) (hP : PsiCFacts) (m n : ℕ)
    (ra rb rab r0 : ℤ) (hadm : CAdm m n) (hrel : CRel m n ra rb rab r0) :
    PullbackMero (GC m n ra rb rab r0) phiC := by
  obtain ⟨E, hE, heven, hgerm⟩ := germ_GC_even hL hΦ hP m n ra rb rab r0 hadm hrel
  exact pullbackMero_of_even hE heven hgerm

/-- The `G = Sym⁺P` case in germ form (denominator `1`, numerator exhibited); consumed by the
derivative and integral cases. -/
theorem germ_GC (hL : PLiftCont) (hΦ : PhiLift) (hP : PsiCFacts) (m n : ℕ)
    (ra rb rab r0 : ℤ) (hadm : CAdm m n) (hrel : CRel m n ra rb rab r0) :
    ∃ N : ℂ → ℂ, DifferentiableOn ℂ N (Metric.ball 0 1) ∧
      ∀ᶠ w in 𝓝 (0 : ℂ), HasSum (fun k : ℕ =>
        ((PowerSeries.coeff k (GC m n ra rb rab r0) : ℚ) : ℂ) * phiC w ^ k) (N w) := by
  obtain ⟨E, hE, heven, hgerm⟩ := germ_GC_even hL hΦ hP m n ra rb rab r0 hadm hrel
  exact germ_of_even hE heven hgerm


/-! ## The trivial case `B₁ = 1` -/

lemma pullbackMero_one (Ψ : ℂ → ℂ) : PullbackMero (1 : PowerSeries ℚ) Ψ := by
  refine ⟨1, fun _ => 1, by simp, differentiableOn_const 1, ?_⟩
  refine Filter.Eventually.of_forall fun z => ?_
  have h : (fun n : ℕ => ((PowerSeries.coeff n (1 : PowerSeries ℚ) : ℚ) : ℂ) * Ψ z ^ n)
      = fun n : ℕ => if n = 0 then (1 : ℂ) else 0 := by
    funext n
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · simp [PowerSeries.coeff_one, hn]
  rw [h]
  simpa using hasSum_ite_eq 0 (1 : ℂ)

/-! ## Assembly of `CPullbacks`

The 17 entries of `seventeen` are, in order,
`B₁, B₂, B₃, B₄, B₅, G, G', G'', G''', B₆, B₇, ∫yG, ∫G, ∫(G−jet₁)/y, …, ∫(G−jet₃)/y⁴`
(`Submission.CDTPlan.seventeen`).  Cases `B₁` (index 0) and `G` (index 5) are proved here;
the others are delegated (see `HANDOFF.md` for the intended statements). -/

theorem c_pullbacks (hL : PLiftCont) (hΦ : PhiLift) (hM : HauptFacts) (hP : PsiCFacts)
    (hN : CNumerics) : CPullbacks := by
  intro m n ra rb rab r0 hadm hrel i
  obtain ⟨hphiCdiff, hphiC0, hphiCderiv, _hphiCpsi, hphiCzero, _hphiCrest⟩ :=
    Work.CPhi.phiC_analytic hM hP
  fin_cases i
  · -- `B₁ = 1`
    exact pullbackMero_one phiC
  · -- `B₂`
    exact pullbackMero_B2 hM hP
  · -- `B₃`
    obtain ⟨Φ, hΦdiff, hΦrel, _⟩ := hΦ
    have hΦneq : ∀ z ∈ Metric.ball (0 : ℂ) 1, Φ z ≠ 1 :=
      fun z hz => Phi_ne_one_of_rel Φ hΦrel z hz
    exact pullbackMero_of_germ (germ_B3 Φ hΦdiff hΦneq hΦrel)
  · -- `B₄`
    obtain ⟨Φ, hΦdiff, hΦrel, _⟩ := hΦ
    have hΦneq : ∀ z ∈ Metric.ball (0 : ℂ) 1, Φ z ≠ 1 :=
      fun z hz => Phi_ne_one_of_rel Φ hΦrel z hz
    exact pullbackMero_B4 Φ hΦdiff hΦneq hΦrel
  · -- `B₅`
    obtain ⟨Φ, hΦdiff, hΦrel, hΦzero⟩ := hΦ
    exact pullbackMero_B5 Φ hΦdiff hΦzero hΦrel
  · -- `G = Sym⁺P`: proved
    exact pullbackMero_GC hL hΦ hP m n ra rb rab r0 hadm hrel
  · -- `G' = dY G`
    obtain ⟨S, hS⟩ := deriv_phiC_zeros_finite hM hP
    obtain ⟨NG, hNG, hgG⟩ := germ_GC hL hΦ hP m n ra rb rab r0 hadm hrel
    refine pullbackMero_deriv_iter S 1 hphiCdiff ?_ hS hNG hgG
    rw [hphiCderiv]; norm_num
  · -- `G'' = dY (dY G)`
    obtain ⟨S, hS⟩ := deriv_phiC_zeros_finite hM hP
    obtain ⟨NG, hNG, hgG⟩ := germ_GC hL hΦ hP m n ra rb rab r0 hadm hrel
    refine pullbackMero_deriv_iter S 2 hphiCdiff ?_ hS hNG hgG
    rw [hphiCderiv]; norm_num
  · -- `G''' = dY (dY (dY G))`
    obtain ⟨S, hS⟩ := deriv_phiC_zeros_finite hM hP
    obtain ⟨NG, hNG, hgG⟩ := germ_GC hL hΦ hP m n ra rb rab r0 hadm hrel
    refine pullbackMero_deriv_iter S 3 hphiCdiff ?_ hS hNG hgG
    rw [hphiCderiv]; norm_num
  · -- `B₆ = ∫ B₃/y = intY (tq 1 B3)`
    obtain ⟨Φ, hΦdiff, hΦrel, _⟩ := hΦ
    have hΦneq : ∀ z ∈ Metric.ball (0 : ℂ) 1, Φ z ≠ 1 :=
      fun z hz => Phi_ne_one_of_rel Φ hΦrel z hz
    obtain ⟨N₃, hN₃, hg₃⟩ := germ_B3 Φ hΦdiff hΦneq hΦrel
    obtain ⟨N₁, hN₁, hg₁⟩ :=
      germ_tq (f := B3) 1 hphiCdiff hphiC0 hphiCzero hN₃ hg₃
    obtain ⟨N, hN', hg⟩ := germ_intY (f := tq 1 B3) hphiCdiff hN₁ hg₁
    have h : PullbackMero
        (Submission.CDTPlan.intY (Submission.CDTPlan.tq 1 Submission.CDTPlan.B3)) phiC :=
      pullbackMero_of_germ ⟨N, hN', hg⟩
    rw [← B6_eq_intY] at h
    exact h
  · -- `B₇ = ∫ B₄/y = intY (tq 1 B4)`
    obtain ⟨Φ, hΦdiff, hΦrel, hΦzero⟩ := hΦ
    have hΦneq : ∀ z ∈ Metric.ball (0 : ℂ) 1, Φ z ≠ 1 :=
      fun z hz => Phi_ne_one_of_rel Φ hΦrel z hz
    obtain ⟨N₄, hN₄, hg₄⟩ := germ_B4 Φ hΦdiff hΦneq hΦzero hΦrel
    obtain ⟨N₁, hN₁, hg₁⟩ :=
      germ_tq (f := B4) 1 hphiCdiff hphiC0 hphiCzero hN₄ hg₄
    obtain ⟨N, hN', hg⟩ := germ_intY (f := tq 1 B4) hphiCdiff hN₁ hg₁
    have h : PullbackMero
        (Submission.CDTPlan.intY (Submission.CDTPlan.tq 1 Submission.CDTPlan.B4)) phiC :=
      pullbackMero_of_germ ⟨N, hN', hg⟩
    rw [← B7_eq_intY] at h
    exact h
  · -- `∫ yG = intY (X * G)`: `germ_intY` ∘ `germ_mulX` applied to the germ of `G`
    obtain ⟨NG, hNG, hgG⟩ := germ_GC hL hΦ hP m n ra rb rab r0 hadm hrel
    obtain ⟨N₁, hN₁, hg₁⟩ := germ_mulX (f := GC m n ra rb rab r0) hphiCdiff hNG hgG
    obtain ⟨N, hN, hg⟩ :=
      germ_intY (f := PowerSeries.X * GC m n ra rb rab r0) hphiCdiff hN₁ hg₁
    exact pullbackMero_of_germ ⟨N, hN, hg⟩
  · -- `∫ G = intY G`
    obtain ⟨NG, hNG, hgG⟩ := germ_GC hL hΦ hP m n ra rb rab r0 hadm hrel
    obtain ⟨N, hN, hg⟩ := germ_intY (f := GC m n ra rb rab r0) hphiCdiff hNG hgG
    exact pullbackMero_of_germ ⟨N, hN, hg⟩
  · -- `∫ (G-G(0))/y = intY (tq 1 G)`
    obtain ⟨NG, hNG, hgG⟩ := germ_GC hL hΦ hP m n ra rb rab r0 hadm hrel
    obtain ⟨N₁, hN₁, hg₁⟩ :=
      germ_tq (f := GC m n ra rb rab r0) 1 hphiCdiff hphiC0 hphiCzero hNG hgG
    obtain ⟨N, hN, hg⟩ := germ_intY (f := tq 1 (GC m n ra rb rab r0)) hphiCdiff hN₁ hg₁
    exact pullbackMero_of_germ ⟨N, hN, hg⟩
  · -- `∫ (G-G(0)-G'(0)y)/y² = intY (tq 2 G)`
    obtain ⟨NG, hNG, hgG⟩ := germ_GC hL hΦ hP m n ra rb rab r0 hadm hrel
    obtain ⟨N₁, hN₁, hg₁⟩ :=
      germ_tq (f := GC m n ra rb rab r0) 2 hphiCdiff hphiC0 hphiCzero hNG hgG
    obtain ⟨N, hN, hg⟩ := germ_intY (f := tq 2 (GC m n ra rb rab r0)) hphiCdiff hN₁ hg₁
    exact pullbackMero_of_germ ⟨N, hN, hg⟩
  · -- `∫ (G-G(0)-G'(0)y-G''(0)y²/2)/y³ = intY (tq 3 G)`
    obtain ⟨NG, hNG, hgG⟩ := germ_GC hL hΦ hP m n ra rb rab r0 hadm hrel
    obtain ⟨N₁, hN₁, hg₁⟩ :=
      germ_tq (f := GC m n ra rb rab r0) 3 hphiCdiff hphiC0 hphiCzero hNG hgG
    obtain ⟨N, hN, hg⟩ := germ_intY (f := tq 3 (GC m n ra rb rab r0)) hphiCdiff hN₁ hg₁
    exact pullbackMero_of_germ ⟨N, hN, hg⟩
  · -- `∫ (G-G(0)-G'(0)y-G''(0)y²/2-G'''(0)y³/6)/y⁴ = intY (tq 4 G)`
    obtain ⟨NG, hNG, hgG⟩ := germ_GC hL hΦ hP m n ra rb rab r0 hadm hrel
    obtain ⟨N₁, hN₁, hg₁⟩ :=
      germ_tq (f := GC m n ra rb rab r0) 4 hphiCdiff hphiC0 hphiCzero hNG hgG
    obtain ⟨N, hN, hg⟩ := germ_intY (f := tq 4 (GC m n ra rb rab r0)) hphiCdiff hN₁ hg₁
    exact pullbackMero_of_germ ⟨N, hN, hg⟩

end Work.CPull
