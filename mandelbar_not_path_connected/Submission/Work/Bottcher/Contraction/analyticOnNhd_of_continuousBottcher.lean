/-
# A continuous Böttcher coordinate is analytic

The Böttcher coordinate of the holomorphic quartic `p_c = T_c ∘ T_c` is usually produced by an
analytic construction (a contractive inverse branch, or a holomorphic logarithm of the
normalised factor).  This file shows that *analyticity comes for free*: any **continuous** `φ`
on the escape set `EscapeSet c = {z | 0 < green c z}` of a mandelbar parameter which

* satisfies the Böttcher equation `φ (p_c z) = (φ z)^4`,
* has modulus `‖φ z‖ = exp (green c z)`,
* is tangent to the identity at infinity, `φ z / z → 1`,

is automatically analytic on the escape set.

The argument has two parts.

* **Far region.**  On a far region `{R ≤ ‖z‖}` such a `φ` coincides with the product formula
  `bottcher c` (`Work.Bottcher.Contraction.eq_bottcher_on_far_of_continuousBottcher`); hence it
  is analytic there, by `Core.analyticAt_bottcher` for the product formula.
* **Propagation inwards.**  If `φ` is analytic near `p_c z` (`z` escaping), then `φ` is analytic
  at `z`: on a small ball `B ∋ z` the function `w ↦ φ (p_c w)` is analytic and nowhere zero,
  hence has a holomorphic logarithm `L` (`Work.Escape.exists_differentiableOn_ball_clog`); then
  `u = exp (L / 4)` is holomorphic on `B` with `u^4 = φ ∘ p_c = φ^4`, so `φ / u` is a continuous
  function on the (preconnected) ball with fourth power `1`, i.e. it is constant (`μ_4` is
  discrete), and `φ = ζ * u` is analytic.

Every escaping point reaches the far region after finitely many iterates, so the two parts
together give `AnalyticOnNhd ℂ φ (EscapeSet c)`.
-/
import Mathlib
import Submission.Work.Bottcher.Defs
import Submission.Work.Bottcher.Basic
import Submission.Work.Bottcher.Core.analyticAt_bottcher
import Submission.Work.Bottcher.Core.norm_bottcher_domain
import Submission.Work.Bottcher.Core.bottcher_comm_pMap_domain
import Submission.Work.Bottcher.Green.green_comm
import Submission.Work.Bottcher.Green.green_nonneg
import Submission.Work.Bottcher.Green.green_pos_iff
import Submission.Work.Bottcher.Green.greenParam_pos_iff
import Submission.Work.Bottcher.Contraction.bottcher_comm_Tantibar_of_analytic
import Submission.Work.Escape.exists_differentiableOn_ball_clog
import Submission.Work.Bottcher.Contraction.eq_bottcher_on_far_of_continuousBottcher
import Submission.Work.Escape.continuous_green
import Submission.Work.Escape.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Filter Function
open scoped Topology ComplexConjugate

namespace Work.Bottcher.Contraction

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-! ## Elementary facts -/

/-- The Green function of the second iterate: `G_c(p_c z) = 4 G_c z`. -/
theorem green_pMap_four (c z : ℂ) :
    Work.Bottcher.green c (Work.Bottcher.pMap c z) = 4 * Work.Bottcher.green c z := by
  have h : Work.Bottcher.pMap c z = Tantibar c (Tantibar c z) := by
    rw [Work.Bottcher.pMap_eq_iterate_two]; rfl
  rw [h, Work.Bottcher.Green.green_comm, Work.Bottcher.Green.green_comm]
  ring

/-- The Green function along the `p_c`-orbit: `G_c (p_c^[k] z) = 4^k G_c z`. -/
theorem green_pMap_iterate_four (c z : ℂ) (k : ℕ) :
    Work.Bottcher.green c ((Work.Bottcher.pMap c)^[k] z) = 4 ^ k * Work.Bottcher.green c z := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply', green_pMap_four, ih, pow_succ]
      ring

/-- The `p_c`-orbit of an escaping point escapes to infinity. -/
theorem tendsto_iterate_pMap_cocompact' (c : ℂ) {z : ℂ} (hz : 0 < Work.Bottcher.green c z) :
    Tendsto (fun k : ℕ => (Work.Bottcher.pMap c)^[k] z) atTop (cocompact ℂ) := by
  have hT : Tendsto (fun n : ℕ => ‖(Tantibar c)^[n] z‖) atTop atTop :=
    (Work.Bottcher.Green.green_pos_iff c z).mp hz
  have h2 : Tendsto (fun k : ℕ => 2 * k) atTop atTop :=
    tendsto_atTop_atTop.mpr (fun b => ⟨b, fun a ha => by omega⟩)
  have hnorm : Tendsto (fun k : ℕ => ‖(Work.Bottcher.pMap c)^[k] z‖) atTop atTop := by
    refine (hT.comp h2).congr' (Eventually.of_forall (fun k => ?_))
    simp only [Function.comp_apply]
    rw [Work.Bottcher.pMap_iterate]
  exact tendsto_cocompact_of_tendsto_dist_comp_atTop 0 (by simpa using hnorm)

/-- The escape set is open. -/
theorem isOpen_EscapeSet (c : ℂ) : IsOpen (Work.Bottcher.EscapeSet c) := by
  have hcont : Continuous (fun z : ℂ => Work.Bottcher.green c z) :=
    Work.Escape.continuous_green (Tantibar c) 2 ‖c‖ (Work.Escape.monicGrowth_Tantibar c) le_rfl
  exact isOpen_lt continuous_const hcont

/-- `p_c` is continuous. -/
theorem continuous_pMap (c : ℂ) : Continuous (Work.Bottcher.pMap c) := by
  show Continuous fun z : ℂ => (z ^ 2 + conj c) ^ 2 + c
  fun_prop

/-- `p_c` is analytic on every open set. -/
theorem analyticOnNhd_pMap (c : ℂ) {s : Set ℂ} (hs : IsOpen s) :
    AnalyticOnNhd ℂ (Work.Bottcher.pMap c) s := by
  refine DifferentiableOn.analyticOnNhd ?_ hs
  show DifferentiableOn ℂ (fun z : ℂ => (z ^ 2 + conj c) ^ 2 + c) s
  fun_prop

/-! ## An integer-valued continuous function is constant -/

/-- A continuous real function which takes only integer values on a preconnected set is
constant there. -/
theorem eq_of_continuousOn_int {α : Type*} [TopologicalSpace α] {U : Set α}
    (hU : IsPreconnected U) {m : α → ℝ} (hm : ContinuousOn m U)
    (hint : ∀ x ∈ U, ∃ k : ℤ, m x = k) {a b : α} (ha : a ∈ U) (hb : b ∈ U) :
    m a = m b := by
  have key : ∀ {x y : α}, x ∈ U → y ∈ U → m x ≤ m y → m x = m y := by
    intro x y hx hy hxy
    rcases eq_or_lt_of_le hxy with h | h
    · exact h
    · exfalso
      obtain ⟨kx, hkx⟩ := hint x hx
      obtain ⟨ky, hky⟩ := hint y hy
      have hge : (1 : ℝ) ≤ m y - m x := by
        have hk : (1 : ℤ) ≤ ky - kx := by
          have h0 : (0 : ℤ) < ky - kx := by
            by_contra hc
            push_neg at hc
            have hcast : ((ky - kx : ℤ) : ℝ) ≤ 0 := by exact_mod_cast hc
            push_cast [hky, hkx] at hcast
            linarith
          omega
        calc (1 : ℝ) = ((1 : ℤ) : ℝ) := by norm_num
          _ ≤ ((ky - kx : ℤ) : ℝ) := by exact_mod_cast hk
          _ = m y - m x := by push_cast [hky, hkx]; ring
      have hmid : m x + 1 / 3 ∈ Set.Icc (m x) (m y) := ⟨by linarith, by linarith⟩
      obtain ⟨c, hcU, hc⟩ := hU.intermediate_value hx hy hm hmid
      obtain ⟨kc, hkc⟩ := hint c hcU
      have hfrac : ((kc - kx : ℤ) : ℝ) = 1 / 3 := by
        have hmc : m c - m x = 1 / 3 := by rw [hc]; ring
        push_cast [hkc, hkx]
        linarith
      have h3 : ((kc - kx : ℤ) : ℝ) * 3 = 1 := by linarith
      have h3' : (kc - kx) * 3 = 1 := by exact_mod_cast h3
      omega
  rcases le_total (m a) (m b) with h | h
  · exact key ha hb h
  · exact (key hb ha h).symm

/-! ## The fourth roots of unity -/

/-- A complex number with `x ^ 4 = 1` is one of `1`, `-1`, `I`, `-I`. -/
theorem eq_one_or_neg_one_or_I_or_negI {x : ℂ} (hx : x ^ 4 = 1) :
    x = 1 ∨ x = -1 ∨ x = Complex.I ∨ x = -Complex.I := by
  have hI2 : Complex.I ^ 2 = -1 := by rw [pow_two]; exact Complex.I_mul_I
  have h2 : x ^ 2 = 1 ∨ x ^ 2 = -1 := by
    have hfac : (x ^ 2 - 1) * (x ^ 2 + 1) = 0 := by
      have : (x ^ 2 - 1) * (x ^ 2 + 1) = x ^ 4 - 1 := by ring
      rw [this, hx]; ring
    rcases mul_eq_zero.mp hfac with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (by linear_combination h)
  rcases h2 with h | h
  · rcases sq_eq_one_iff.mp h with h' | h'
    · exact Or.inl h'
    · exact Or.inr (Or.inl h')
  · have hfac : (x - Complex.I) * (x + Complex.I) = 0 := by
      have hsplit : (x - Complex.I) * (x + Complex.I) = x ^ 2 - Complex.I ^ 2 := by ring
      rw [hsplit, h, hI2]
      norm_num
    rcases mul_eq_zero.mp hfac with h' | h'
    · exact Or.inr (Or.inr (Or.inl (sub_eq_zero.mp h')))
    · exact Or.inr (Or.inr (Or.inr (by linear_combination h')))

/-- A continuous function on a preconnected set whose fourth power is `1` is constant. -/
theorem exists_const_of_pow_four_eq_one {U : Set ℂ} (hU : IsPreconnected U) {f : ℂ → ℂ}
    (hf : ContinuousOn f U) (h4 : ∀ z ∈ U, (f z) ^ 4 = 1) :
    ∃ c : ℂ, ∀ z ∈ U, f z = c := by
  rcases U.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
  · exact ⟨0, by simp⟩
  refine ⟨f a, fun z hz => ?_⟩
  have hre_int : ∀ z ∈ U, ∃ k : ℤ, (f z).re = k := by
    intro z hz
    rcases eq_one_or_neg_one_or_I_or_negI (h4 z hz) with h | h | h | h
    · exact ⟨1, by simp [h]⟩
    · exact ⟨-1, by simp [h]⟩
    · exact ⟨0, by simp [h, Complex.I_re]⟩
    · exact ⟨0, by simp [h, Complex.I_re]⟩
  have him_int : ∀ z ∈ U, ∃ k : ℤ, (f z).im = k := by
    intro z hz
    rcases eq_one_or_neg_one_or_I_or_negI (h4 z hz) with h | h | h | h
    · exact ⟨0, by simp [h]⟩
    · exact ⟨0, by simp [h]⟩
    · exact ⟨1, by simp [h, Complex.I_im]⟩
    · exact ⟨-1, by simp [h, Complex.I_im]⟩
  have hre : (f z).re = (f a).re :=
    eq_of_continuousOn_int hU (Complex.continuous_re.comp_continuousOn hf) hre_int hz ha
  have him : (f z).im = (f a).im :=
    eq_of_continuousOn_int hU (Complex.continuous_im.comp_continuousOn hf) him_int hz ha
  exact Complex.ext hre him

/-! ## Propagation of analyticity inwards along `p_c` -/

/-- **Analyticity propagates inwards.**  If `φ` is continuous on the escape set with the
Böttcher equation and the right modulus, and is analytic near `p_c z` for an escaping point
`z`, then it is analytic at `z`. -/
theorem analyticAt_of_analyticAt_pMap (c : ℂ) {φ : ℂ → ℂ}
    (hcont : ContinuousOn φ (Work.Bottcher.EscapeSet c))
    (hfe : ∀ z : ℂ, 0 < Work.Bottcher.green c z →
      φ (Work.Bottcher.pMap c z) = (φ z) ^ 4)
    (hmod : ∀ z : ℂ, 0 < Work.Bottcher.green c z →
      ‖φ z‖ = Real.exp (Work.Bottcher.green c z))
    {z : ℂ} (hz : 0 < Work.Bottcher.green c z)
    (han : AnalyticAt ℂ φ (Work.Bottcher.pMap c z)) :
    AnalyticAt ℂ φ z := by
  -- a ball around `pMap c z` on which `φ` is analytic
  obtain ⟨r, hr, hran⟩ := han.exists_ball_analyticOnNhd
  -- a ball around `z` mapped into it and contained in the escape set
  have hpm_cont : ContinuousAt (Work.Bottcher.pMap c) z := (continuous_pMap c).continuousAt
  have hpre : Work.Bottcher.pMap c ⁻¹' Metric.ball (Work.Bottcher.pMap c z) r ∈ 𝓝 z :=
    hpm_cont.preimage_mem_nhds (Metric.ball_mem_nhds _ hr)
  have hEopen : Work.Bottcher.EscapeSet c ∈ 𝓝 z :=
    (isOpen_EscapeSet c).mem_nhds (by rw [Work.Bottcher.mem_EscapeSet]; exact hz)
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp (inter_mem hpre hEopen)
  set B : Set ℂ := Metric.ball z ε with hBdef
  have hBopen : IsOpen B := Metric.isOpen_ball
  have hBpre : IsPreconnected B := Metric.isPreconnected_ball
  have hBmem : B ∈ 𝓝 z := Metric.ball_mem_nhds z hε
  have hBsub : B ⊆ Work.Bottcher.EscapeSet c := fun w hw => (hεsub hw).2
  have hBmap : ∀ w ∈ B, Work.Bottcher.pMap c w ∈ Metric.ball (Work.Bottcher.pMap c z) r :=
    fun w hw => (hεsub hw).1
  -- `φ ∘ p_c` is holomorphic and nowhere zero on `B`
  have hgan : AnalyticOnNhd ℂ (fun w => φ (Work.Bottcher.pMap c w)) B :=
    hran.comp (analyticOnNhd_pMap c hBopen) hBmap
  have hgnz : ∀ w ∈ B, φ (Work.Bottcher.pMap c w) ≠ 0 := by
    intro w hw h0
    have hgw : 0 < Work.Bottcher.green c (Work.Bottcher.pMap c w) := by
      rw [green_pMap_four]
      have hwE := hBsub hw
      rw [Work.Bottcher.mem_EscapeSet] at hwE
      linarith
    have h1 := hmod _ hgw
    rw [h0, norm_zero] at h1
    exact (Real.exp_pos _).ne' h1.symm
  obtain ⟨L, hLdiff, hLexp, _⟩ :=
    Work.Escape.exists_differentiableOn_ball_clog (g := fun w => φ (Work.Bottcher.pMap c w))
      hgan.differentiableOn hgnz
  -- the holomorphic fourth root `u = exp (L / 4)`
  set u : ℂ → ℂ := fun w => Complex.exp (L w / 4) with hudef
  have hudiff : DifferentiableOn ℂ u B := by
    have h1 : DifferentiableOn ℂ (fun w => L w / 4) B := hLdiff.div_const 4
    exact h1.cexp
  have hu4 : ∀ w ∈ B, (u w) ^ 4 = φ (Work.Bottcher.pMap c w) := by
    intro w hw
    have h1 : ((4 : ℕ) : ℂ) * (L w / 4) = L w := by ring_nf
    have h2 : (u w) ^ 4 = Complex.exp (L w) := by
      rw [hudef, ← Complex.exp_nat_mul (L w / 4) 4, h1]
    rw [h2]
    exact hLexp w hw
  -- `φ / u` has fourth power one, hence is constant on the ball
  have hhcont : ContinuousOn (fun w => φ w / u w) B :=
    (hcont.mono hBsub).div (hudiff.continuousOn) (fun w _ => Complex.exp_ne_zero _)
  have hh4 : ∀ w ∈ B, (φ w / u w) ^ 4 = 1 := by
    intro w hw
    have huw : u w ≠ 0 := Complex.exp_ne_zero _
    have hwE : w ∈ Work.Bottcher.EscapeSet c := hBsub hw
    have h1 : (φ w) ^ 4 = φ (Work.Bottcher.pMap c w) := by
      rw [Work.Bottcher.mem_EscapeSet] at hwE
      exact (hfe w hwE).symm
    rw [div_pow, h1, ← hu4 w hw, div_self (pow_ne_zero 4 huw)]
  obtain ⟨zeta, hzeta⟩ := exists_const_of_pow_four_eq_one hBpre hhcont hh4
  -- hence `φ` agrees on `B` with the holomorphic function `zeta * u`
  have hphi_eq : ∀ w ∈ B, φ w = zeta * u w := by
    intro w hw
    have h := hzeta w hw
    have huw : u w ≠ 0 := Complex.exp_ne_zero _
    rw [div_eq_iff huw] at h
    calc φ w = zeta * u w := h
      _ = zeta * u w := rfl
  have hdiff : DifferentiableOn ℂ φ B := by
    have h1 : DifferentiableOn ℂ (fun w => zeta * u w) B :=
      (differentiableOn_const zeta).mul hudiff
    refine h1.congr ?_
    intro w hw
    exact hphi_eq w hw
  exact hdiff.analyticAt hBmem

/-! ## Analyticity on the far region -/

/-- If a continuous Böttcher coordinate agrees with the product formula on the far region
`{R ≤ ‖z‖}`, then it is analytic there. -/
theorem analyticAt_of_far_eq_bottcher (c : ℂ) {φ : ℂ → ℂ} {R : ℝ}
    (hR : Work.Bottcher.escapeRadius c ≤ R)
    (hfar : ∀ z : ℂ, R ≤ ‖z‖ → φ z = Work.Bottcher.bottcher c z)
    {w : ℂ} (hw : R < ‖w‖) :
    AnalyticAt ℂ φ w := by
  have hbw : AnalyticAt ℂ (Work.Bottcher.bottcher c) w :=
    Work.Bottcher.Core.analyticAt_bottcher c w (le_of_lt (lt_of_le_of_lt hR hw))
  refine hbw.congr ?_
  refine Filter.eventually_of_mem (Metric.ball_mem_nhds w (sub_pos.mpr hw)) ?_
  intro u hu
  have h1 : dist u w < ‖w‖ - R := Metric.mem_ball.mp hu
  have h2 : R ≤ ‖u‖ := by
    have h3 : ‖w‖ - ‖u‖ ≤ ‖w - u‖ := norm_sub_norm_le w u
    rw [dist_eq_norm] at h1
    rw [norm_sub_rev] at h3
    linarith
  exact (hfar u h2).symm

/-! ## The main result -/

/-- **The analytic Böttcher coordinate from a continuous one.**  A continuous Böttcher
coordinate of the quartic `p_c = T_c ∘ T_c` at a mandelbar parameter, with the product formula
as its far-field model, is analytic on the whole escape set. -/
theorem analyticOnNhd_of_continuousBottcher_of_far (c : ℂ) (φ : ℂ → ℂ) (R : ℝ)
    (hR : Work.Bottcher.escapeRadius c ≤ R)
    (hcont : ContinuousOn φ (Work.Bottcher.EscapeSet c))
    (hfe : ∀ z : ℂ, 0 < Work.Bottcher.green c z →
      φ (Work.Bottcher.pMap c z) = (φ z) ^ 4)
    (hmod : ∀ z : ℂ, 0 < Work.Bottcher.green c z →
      ‖φ z‖ = Real.exp (Work.Bottcher.green c z))
    (hfar : ∀ z : ℂ, R ≤ ‖z‖ → φ z = Work.Bottcher.bottcher c z) :
    AnalyticOnNhd ℂ φ (Work.Bottcher.EscapeSet c) := by
  intro z hz
  -- find a far iterate of `z`
  have hbig : ∀ᶠ k : ℕ in atTop, R < ‖(Work.Bottcher.pMap c)^[k] z‖ :=
    (tendsto_iterate_pMap_cocompact' c hz).eventually
      (tendsto_norm_cocompact_atTop.eventually (eventually_gt_atTop R))
  obtain ⟨N, hN⟩ := eventually_atTop.mp hbig
  have hN' : R < ‖(Work.Bottcher.pMap c)^[N] z‖ := hN N le_rfl
  -- descending induction from the far iterate
  have hback : ∀ m : ℕ, m ≤ N → AnalyticAt ℂ φ ((Work.Bottcher.pMap c)^[N - m] z) := by
    intro m
    induction m with
    | zero =>
        intro _
        simpa using analyticAt_of_far_eq_bottcher c hR hfar hN'
    | succ m ih =>
        intro hm
        have ih' := ih (by omega)
        have hstep : (Work.Bottcher.pMap c)^[N - m] z
            = Work.Bottcher.pMap c ((Work.Bottcher.pMap c)^[N - (m + 1)] z) := by
          rw [show N - m = (N - (m + 1)) + 1 by omega, Function.iterate_succ_apply']
        rw [hstep] at ih'
        have hgpos : 0 < Work.Bottcher.green c ((Work.Bottcher.pMap c)^[N - (m + 1)] z) := by
          rw [green_pMap_iterate_four]
          exact mul_pos (pow_pos (by norm_num) _) hz
        exact analyticAt_of_analyticAt_pMap c hcont hfe hmod hgpos ih'
  have hfin := hback N le_rfl
  simpa using hfin

/-! ## The main result -/

/-- **A continuous Böttcher coordinate is analytic.**

`Work.Bottcher.Contraction.eq_bottcher_on_far_of_continuousBottcher` identifies any continuous
solution of the Böttcher problem of the quartic `p_c = T_c ∘ T_c` with the product formula on a
far region, and `analyticOnNhd_of_continuousBottcher_of_far` then propagates analyticity from
that far region to the whole escape set along the `p_c`-orbits. -/
theorem analyticOnNhd_of_continuousBottcher (c : ℂ) (hc : c ∈ Mandelbar) {φ : ℂ → ℂ}
    (hcont : ContinuousOn φ (Work.Bottcher.EscapeSet c))
    (hfe : ∀ z : ℂ, 0 < Work.Bottcher.green c z →
      φ (Work.Bottcher.pMap c z) = (φ z) ^ 4)
    (hmod : ∀ z : ℂ, 0 < Work.Bottcher.green c z →
      ‖φ z‖ = Real.exp (Work.Bottcher.green c z))
    (has : Filter.Tendsto (fun z : ℂ => φ z / z) (Filter.cocompact ℂ) (nhds (1 : ℂ))) :
    AnalyticOnNhd ℂ φ (Work.Bottcher.EscapeSet c) := by
  obtain ⟨R, hR, hfar⟩ :=
    eq_bottcher_on_far_of_continuousBottcher c hc φ hcont hfe hmod has
  exact analyticOnNhd_of_continuousBottcher_of_far c φ R hR hcont hfe hmod hfar

end Work.Bottcher.Contraction
