import Mathlib
import Submission.Commons.NumberTheory.Linnik.completedL_zeroCount
import Submission.Commons.NumberTheory.Linnik.completedL_pf_identity_rect
import Submission.Commons.NumberTheory.Linnik.nearSum_bound
import Submission.Commons.NumberTheory.Linnik.partialSum_far_bound
import Submission.Commons.NumberTheory.Linnik.partialFraction_tail
import Submission.Commons.NumberTheory.Linnik.divisor_eq_closedBall_subset
import Submission.Commons.Analysis.Complex.zeroFactor_g
import Submission.Commons.Analysis.Complex.circleLogDerivContour_bound

open Complex DirichletCharacter Metric Filter Topology
open scoped Real BigOperators Topology

set_option maxHeartbeats 800000

noncomputable section

namespace Commons.NumberTheory.Linnik

/-! # `logDeriv_estimate`

For a primitive non-trivial character `χ mod N`, the logarithmic derivative of the
completed Dirichlet L-function `Λ(χ, ·)` is bounded on the circle `|w| = R` (`R ≥ 2`) by
`c·ℓ(R)²` plus the explicit near-zero pole part, where `ℓ(R) = log(R+2) + log N + 2`.

Strategy: the partial-fraction identity `completedL_pf_identity_rect` expresses
`Λ'/Λ(w) = B + lim_T F_T(w)` with `F_T(w) = Σ_u divisor(0,T)(u)·(1/(w-u)+1/u)`.
The tail `|lim F - F_{5R}|` is bounded through `partialFraction_tail`.  The finite sum
`F_{5R}(w)` is split into the *near* zeros (`|u-w| ≤ 1`, handled by `nearSum_bound`, the
explicit near-pole part) and the *far* zeros (`1 < |u-w|`, handled by
`partialSum_far_bound` via `|1/(w-u)+1/u| = |w|/(|u||w-u|)`).  `|B|` and the near
`1/u`-terms are absorbed into the constant.
-/

/-- `log N ≥ 0`. -/
private lemma logN_nonneg0 {N : ℕ} [NeZero N] : 0 ≤ Real.log (N : ℝ) := by
  exact Real.log_nonneg (by exact_mod_cast (Nat.succ_le_of_lt (Nat.pos_of_ne_zero (NeZero.ne N))))

/-- analyticity of the completed L-function (for `χ ≠ 1`) on any set. -/
private lemma completedL_analytic {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (U : Set ℂ) : AnalyticOnNhd ℂ (fun z => DirichletCharacter.completedLFunction χ z) U := by
  intro z hz
  exact (DirichletCharacter.differentiable_completedLFunction hχ).analyticAt z

/-- `‖(n:ℂ)‖ = n` for `n ≥ 0`. -/
private lemma norm_int_cast {n : ℤ} (hn : 0 ≤ (n : ℝ)) : ‖((n : ℤ) : ℂ)‖ = (n : ℝ) := by
  have h1 : ‖((n : ℤ) : ℂ)‖ = |(n : ℝ)| := by norm_num
  rw [h1, abs_of_nonneg hn]

/-- `ℓ(R) ≥ 1` for `R ≥ 2`. -/
private lemma ell_ge_one {N : ℕ} [NeZero N] {R : ℝ} (hR : 2 ≤ R) :
    (1 : ℝ) ≤ Real.log (R + 2) + Real.log (N : ℝ) + 2 := by
  have h1 : 0 ≤ Real.log (R + 2) := by
    refine Real.log_nonneg ?_
    linarith
  have h2 : 0 ≤ Real.log (N : ℝ) := logN_nonneg0 (N := N)
  linarith

/-- `ℓ(5R) ≤ 2ℓ(R)` for `R ≥ 2`. -/
private lemma ell_five_mul_le_two {N : ℕ} [NeZero N] {R : ℝ} (hR : 2 ≤ R) :
    Real.log (5 * R + 2) + Real.log (N : ℝ) + 2 ≤
      2 * (Real.log (R + 2) + Real.log (N : ℝ) + 2) := by
  have h1 : 0 < 5 * R + 2 := by positivity
  have h2 : 5 * R + 2 ≤ (R + 2) ^ 2 := by nlinarith [sq_nonneg (R + 2)]
  have h3 : Real.log (5 * R + 2) ≤ 2 * Real.log (R + 2) := by
    have h4 := Real.log_le_log h1 h2
    rw [Real.log_pow (R + 2) 2] at h4
    norm_num at h4
    exact h4
  have h5 : 0 ≤ Real.log (N : ℝ) := logN_nonneg0 (N := N)
  nlinarith

/-- norm of the paired kernel at a point with `u ≠ w`, `u ≠ 0`. -/
private lemma inv_add_inv_norm {w u : ℂ} (huw : u ≠ w) (hu0 : u ≠ 0) :
    ‖(1 / (w - u) + 1 / u : ℂ)‖ = ‖w‖ / (‖u‖ * ‖w - u‖) := by
  have hsub : w - u ≠ 0 := sub_ne_zero.mpr huw.symm
  have hsum : (1 / (w - u) + 1 / u : ℂ) = w / (u * (w - u)) := by
    field_simp [hu0, hsub]
    ring
  rw [hsum]
  rw [norm_div, norm_mul]

/-- bound of a real limit from an eventual upper bound, specialised to `atTop`. -/
private lemma tendsto_norm_le_of_eventually {f : ℝ → ℝ} {y M : ℝ}
    (hlim : Tendsto f atTop (𝓝 y)) (hb : ∀ᶠ t in atTop, f t ≤ M) : y ≤ M :=
  le_of_tendsto hlim hb

/-- a pointwise eventual bound of `‖F R - F R₀‖` bounds the limit difference. -/
private lemma norm_sub_lim_le {F : ℝ → ℂ} {R₀ : ℝ} {L : ℂ} {M : ℝ}
    (hlim : Tendsto F atTop (𝓝 L))
    (hb : ∀ᶠ R : ℝ in atTop, ‖F R - F R₀‖ ≤ M) : ‖L - F R₀‖ ≤ M := by
  have hsub : Tendsto (fun R : ℝ => ‖F R - F R₀‖) atTop (𝓝 ‖L - F R₀‖) := by
    have h1 : Tendsto (fun R : ℝ => F R - F R₀) atTop (𝓝 (L - F R₀)) := by
      exact hlim.sub tendsto_const_nhds
    simpa using (continuous_norm.tendsto (L - F R₀)).comp h1 |>.congr' (by
      filter_upwards with R; rfl)
  exact tendsto_norm_le_of_eventually hsub hb

/-- real arithmetic: from `1 ≤ x` and `0 ≤ A` we get `A·(x²+1) ≤ 2·A·x²`. -/
private lemma quad_absorb {x A : ℝ} (hx : 1 ≤ x) (hA : 0 ≤ A) : A * (x ^ 2 + 1) ≤ 2 * A * x ^ 2 := by
  have hsq : 1 ≤ x ^ 2 := by nlinarith [sq_nonneg (x - 1)]
  nlinarith

theorem logDeriv_estimate {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive) :
    ∃ c : ℝ, ∀ R : ℝ, 2 ≤ R → ∀ w : ℂ, ‖w‖ = R →
      DirichletCharacter.completedLFunction χ w ≠ 0 →
      ‖deriv (DirichletCharacter.completedLFunction χ) w /
          DirichletCharacter.completedLFunction χ w‖ ≤
        c * (Real.log (R + 2) + Real.log (N : ℝ) + 2) ^ 2 +
          (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
              (Metric.closedBall w 1)) u : ℤ) : ℝ) * ((‖w - u‖ : ℝ)⁻¹)) := by
  classical
  let Λ : ℂ → ℂ := DirichletCharacter.completedLFunction χ
  let ell : ℝ → ℝ := fun x => Real.log (x + 2) + Real.log (N : ℝ) + 2
  rcases completedL_pf_identity_rect χ hχ hχprim with ⟨B, hB⟩
  rcases nearSum_bound χ hχ hχprim with ⟨Kn, hKn⟩
  rcases partialSum_far_bound χ hχ hχprim with ⟨Kf, hKf⟩
  rcases partialFraction_tail χ hχ hχprim with ⟨Kt, hKt⟩
  let Knn : ℝ := max Kn 0
  let Kfn : ℝ := max Kf 0
  let Ktn : ℝ := max Kt 0
  let c : ℝ := ‖B‖ + 2 * Knn + 2 * Kfn + 2 * Ktn
  refine ⟨c, ?_⟩
  intro R hR w hw hΛw
  let T₀ : ℝ := 5 * R
  have hT₀ : 2 ≤ T₀ := by dsimp [T₀]; nlinarith
  have hwT₀ : ‖w‖ ≤ T₀ / 4 := by
    rw [hw]
    dsimp [T₀]
    nlinarith
  have hT₀w : R + 1 ≤ T₀ := by dsimp [T₀]; nlinarith
  have hΛw' : Λ w ≠ 0 := by simpa [Λ] using hΛw
  have hΛ0 : Λ 0 ≠ 0 := by
    simpa [Λ] using (completedLFunction_zero_ne_zero χ hχ hχprim)
  have hAn : ∀ U : Set ℂ, AnalyticOnNhd ℂ Λ U := by
    intro U
    simpa [Λ] using completedL_analytic χ hχ U
  let F : ℝ → ℂ := fun R' => (∑ᶠ u : ℂ, (((MeromorphicOn.divisor Λ (Metric.closedBall 0 R')) u : ℤ) : ℂ) *
      (1 / (w - u) + 1 / u))
  have hBw : Tendsto F atTop (𝓝 (deriv Λ w / Λ w - B)) := by
    have hh := hB w hΛw
    simpa [F, Λ] using hh
  have hellT0 : 0 ≤ ell T₀ := by
    dsimp [ell]
    have hlg : 0 ≤ Real.log (T₀ + 2) := by
      refine Real.log_nonneg ?_
      dsimp [T₀]
      linarith
    have hlgN : 0 ≤ Real.log (N : ℝ) := logN_nonneg0 (N := N)
    linarith
  have htail_event : ∀ᶠ R' : ℝ in atTop, ‖F R' - F T₀‖ ≤ Ktn * ‖w‖ * ell T₀ / T₀ := by
    filter_upwards [eventually_ge_atTop T₀] with R' hR'
    have hpf := hKt w T₀ R' hT₀ hR' (by simpa [T₀] using hwT₀)
    have hKl : Kt ≤ Ktn := by dsimp [Ktn]; exact le_max_left Kt 0
    have hnn0 : 0 ≤ ‖w‖ * ell T₀ := mul_nonneg (norm_nonneg w) hellT0
    have hm : Kt * (‖w‖ * ell T₀) ≤ Ktn * (‖w‖ * ell T₀) := by
      exact mul_le_mul_of_nonneg_right hKl hnn0
    have hm' : Kt * ‖w‖ * ell T₀ ≤ Ktn * ‖w‖ * ell T₀ := by
      calc
        Kt * ‖w‖ * ell T₀ = Kt * (‖w‖ * ell T₀) := by ring
        _ ≤ Ktn * (‖w‖ * ell T₀) := hm
        _ = Ktn * ‖w‖ * ell T₀ := by ring
    have hle : Kt * ‖w‖ * ell T₀ / T₀ ≤ Ktn * ‖w‖ * ell T₀ / T₀ := by
      have hT0pos : 0 < T₀ := by dsimp [T₀]; positivity
      exact (div_le_div_of_nonneg_right hm' (le_of_lt hT0pos))
    calc
      ‖F R' - F T₀‖ ≤ Kt * ‖w‖ * ell T₀ / T₀ := by
        simpa [F, Λ, ell] using hpf
      _ ≤ Ktn * ‖w‖ * ell T₀ / T₀ := hle
  have htail : ‖(deriv Λ w / Λ w - B) - F T₀‖ ≤ Ktn * ‖w‖ * ell T₀ / T₀ := by
    exact norm_sub_lim_le (F := F) hBw htail_event
  -- near (|w-u| ≤ 1) and far (1 < |w-u|) contributions
  have hKn' : ‖(∑ᶠ u : ℂ, (((MeromorphicOn.divisor Λ (Metric.closedBall w 1)) u : ℤ) : ℂ) * (1 / (w - u) + 1 / u))‖ ≤
        Kn * (ell R ^ 2 + 1) +
          (∑ᶠ u : ℂ, (((MeromorphicOn.divisor Λ (Metric.closedBall w 1)) u : ℤ) : ℝ) * ((‖w - u‖ : ℝ)⁻¹)) := by
    simpa [Λ, ell] using (hKn R hR w hw hΛw)
  have hKf' : (∑ᶠ u : ℂ, (((MeromorphicOn.divisor Λ (Metric.closedBall (0 : ℂ) T₀)) u : ℤ) : ℝ) *
          (if (1 : ℝ) < ‖w - u‖ then ‖w‖ / (‖u‖ * ‖w - u‖) else 0)) ≤ Kf * (ell R ^ 2 + 1) := by
    simpa [Λ, ell] using (hKf R hR w hw T₀ hT₀w)
  have hdiv_nonneg (U : Set ℂ) (u : ℂ) : 0 ≤ (((MeromorphicOn.divisor Λ U) u : ℤ) : ℝ) := by
    have h0 : 0 ≤ (MeromorphicOn.divisor Λ U) u :=
      (MeromorphicOn.AnalyticOnNhd.divisor_nonneg (hAn U)) u
    exact_mod_cast h0
  -- |F T₀| splits into near (explicit) and far (c(ℓ²+1)) parts
  have hFsplit : ‖F T₀‖ ≤ Kn * (ell R ^ 2 + 1) + Kf * (ell R ^ 2 + 1) +
        (∑ᶠ u : ℂ, (((MeromorphicOn.divisor Λ (Metric.closedBall w 1)) u : ℤ) : ℝ) * ((‖w - u‖ : ℝ)⁻¹)) := by
    let dT : ℂ → ℤ := fun u => MeromorphicOn.divisor Λ (Metric.closedBall (0 : ℂ) T₀) u
    have hfinT : (Function.support dT).Finite := by
      dsimp [dT]
      exact MeromorphicOn.divisor_support_finite_of_subset (f := Λ) (V := Metric.closedBall (0 : ℂ) T₀)
        (U := Metric.closedBall (0 : ℂ) T₀) (hAn (closedBall (0 : ℂ) T₀)).meromorphicOn
        (isCompact_closedBall (0 : ℂ) T₀) (by intro z hz; exact hz)
    let S : Finset ℂ := hfinT.toFinset
    have hS_mem : ∀ u : ℂ, u ∈ S ↔ dT u ≠ 0 := by
      intro u
      dsimp [S]
      rw [hfinT.mem_toFinset]
      rfl
    let hterm : ℂ → ℂ := fun u => (((dT u : ℤ) : ℂ) * (1 / (w - u) + 1 / u))
    have hF_fin : F T₀ = ∑ u ∈ S, hterm u := by
      dsimp [F]
      have hsub : Function.support hterm ⊆ (S : Set ℂ) := by
        intro u hu
        have hdne : dT u ≠ 0 := by
          intro hd0
          have : hterm u = 0 := by dsimp [hterm]; simp [hd0]
          exact hu this
        exact (hS_mem u).mpr hdne
      have hfs := finsum_eq_sum_of_support_subset hterm (s := S) hsub
      simpa [Λ, hterm, dT] using hfs
    let near : Finset ℂ := S.filter (fun u => ‖w - u‖ ≤ 1)
    let far : Finset ℂ := S.filter (fun u => (1 : ℝ) < ‖w - u‖)
    have hpart : (∑ u ∈ S, hterm u) = (∑ u ∈ near, hterm u) + (∑ u ∈ far, hterm u) := by
      have hS_eq : S = near ∪ far := by
        ext u
        simp only [near, far, Finset.mem_filter, Finset.mem_union]
        constructor
        · intro hu
          by_cases h : ‖w - u‖ ≤ 1
          · exact Or.inl ⟨hu, h⟩
          · have hlt : (1 : ℝ) < ‖w - u‖ := lt_of_not_ge h
            exact Or.inr ⟨hu, hlt⟩
        · intro hu
          rcases hu with hu | hu
          · have huN : u ∈ S.filter (fun u => ‖w - u‖ ≤ 1) := by simpa [near] using hu
            exact (Finset.mem_filter.mp huN).1
          · have huF : u ∈ S.filter (fun u => (1 : ℝ) < ‖w - u‖) := by simpa [far] using hu
            exact (Finset.mem_filter.mp huF).1
      have hdisj : Disjoint near far := by
        rw [Finset.disjoint_left]
        intro u hu huf
        have huN : u ∈ S.filter (fun u => ‖w - u‖ ≤ 1) := by simpa [near] using hu
        have huF : u ∈ S.filter (fun u => (1 : ℝ) < ‖w - u‖) := by simpa [far] using huf
        have hle : ‖w - u‖ ≤ 1 := (Finset.mem_filter.mp huN).2
        have hgt : (1 : ℝ) < ‖w - u‖ := (Finset.mem_filter.mp huF).2
        linarith
      calc
        (∑ u ∈ S, hterm u) = (∑ u ∈ near ∪ far, hterm u) := by rw [hS_eq]
        _ = (∑ u ∈ near, hterm u) + (∑ u ∈ far, hterm u) := Finset.sum_union hdisj
    -- divisor values agree on the near slice
    have hdiv_near (u : ℂ) (huS : u ∈ S) (huw : ‖w - u‖ ≤ 1) :
        dT u = MeromorphicOn.divisor Λ (Metric.closedBall w 1) u := by
      have hdT : dT u ≠ 0 := (hS_mem u).mp huS
      have huT : u ∈ Metric.closedBall (0 : ℂ) T₀ := by
        exact Commons.Analysis.Complex.divisor_mem_of_ne_zero (f := Λ) (a := (0 : ℂ)) (ρ := T₀)
          (by simpa [dT] using hdT)
      have huW : u ∈ Metric.closedBall w 1 := by
        simpa [dist_eq_norm, norm_sub_rev] using huw
      have hEq := divisor_eq_closedBall_subset (f := Λ) (a := (0 : ℂ)) (b := w) (ra := T₀) (rb := 1)
        (by simpa [Λ] using (completedL_analytic χ hχ (Metric.closedBall (0 : ℂ) T₀ ∪ Metric.closedBall w 1))) huT huW
      simpa [dT] using hEq
    -- near-slice equality with the nearSum_bound finsum
    have hnear_eq : (∑ u ∈ near, hterm u) =
        (∑ᶠ u : ℂ, (((MeromorphicOn.divisor Λ (Metric.closedBall w 1)) u : ℤ) : ℂ) * (1 / (w - u) + 1 / u)) := by
      let dl : ℂ → ℤ := fun u => MeromorphicOn.divisor Λ (Metric.closedBall w 1) u
      have hfinl : (Function.support dl).Finite := by
        dsimp [dl]
        exact MeromorphicOn.divisor_support_finite_of_subset (f := Λ) (V := Metric.closedBall w 1)
          (U := Metric.closedBall w 1) (hAn (closedBall w 1)).meromorphicOn (isCompact_closedBall w 1)
          (by intro z hz; exact hz)
      let hnearF : ℂ → ℂ := fun u => (((dl u : ℤ) : ℂ) * (1 / (w - u) + 1 / u))
      have hsub' : Function.support hnearF ⊆ (near : Set ℂ) := by
        intro u hu
        have hdne : dl u ≠ 0 := by
          intro hd0
          have : hnearF u = 0 := by dsimp [hnearF]; simp [hd0]
          exact hu this
        have huW : u ∈ Metric.closedBall w 1 :=
          Commons.Analysis.Complex.divisor_mem_of_ne_zero (f := Λ) (a := w) (ρ := 1)
            (by simpa [dl] using hdne)
        have huT₀b : u ∈ Metric.closedBall (0 : ℂ) T₀ := by
          have hu1 : ‖u - w‖ ≤ 1 := by simpa [dist_eq_norm, norm_sub_rev] using (Metric.mem_closedBall.mp huW)
          have hwn : ‖w‖ ≤ R := by rw [hw]
          have huT : ‖u‖ ≤ T₀ := by
            have htri : ‖u‖ ≤ ‖u - w‖ + ‖w‖ := by
              simpa [sub_eq_add_neg] using (norm_add_le (u - w) w)
            dsimp [T₀]
            nlinarith
          simpa [Metric.mem_closedBall, dist_eq_norm] using huT
        have hdTne : dT u ≠ 0 := by
          have hEq := divisor_eq_closedBall_subset (f := Λ) (a := (0 : ℂ)) (b := w) (ra := T₀) (rb := 1)
            (by simpa [Λ] using (completedL_analytic χ hχ (Metric.closedBall (0 : ℂ) T₀ ∪ Metric.closedBall w 1))) huT₀b huW
          have hEq' : dT u = dl u := by simpa [dT, dl] using hEq
          intro hz
          have hdl0 : dl u = 0 := by rw [← hEq']; exact hz
          exact hdne hdl0
        exact (Finset.mem_filter.mpr ⟨(hS_mem u).mpr hdTne, by simpa [dist_eq_norm, norm_sub_rev] using (Metric.mem_closedBall.mp huW)⟩)
      have hfs' := finsum_eq_sum_of_support_subset hnearF (s := near) hsub'
      calc
        (∑ u ∈ near, hterm u) = ∑ u ∈ near, hnearF u := by
          refine Finset.sum_congr rfl ?_
          intro u hu
          have huS' : u ∈ S := (Finset.mem_filter.mp hu).1
          have huw' : ‖w - u‖ ≤ 1 := (Finset.mem_filter.mp hu).2
          dsimp [hnearF, hterm]
          rw [hdiv_near u huS' huw']
        _ = (∑ᶠ u : ℂ, hnearF u) := hfs'.symm
    -- bound the near slice
    have hnear_bound : ‖∑ u ∈ near, hterm u‖ ≤ Kn * (ell R ^ 2 + 1) +
        (∑ᶠ u : ℂ, (((MeromorphicOn.divisor Λ (Metric.closedBall w 1)) u : ℤ) : ℝ) * ((‖w - u‖ : ℝ)⁻¹)) := by
      rw [hnear_eq]
      exact hKn'
    -- far slice
    have hfar_norm_sum : ‖∑ u ∈ far, hterm u‖ ≤ ∑ u ∈ far, ((dT u : ℤ) : ℝ) * (‖w‖ / (‖u‖ * ‖w - u‖)) := by
      calc
        ‖∑ u ∈ far, hterm u‖ ≤ ∑ u ∈ far, ‖hterm u‖ := by
          exact norm_sum_le far hterm
        _ = ∑ u ∈ far, ((dT u : ℤ) : ℝ) * (‖w‖ / (‖u‖ * ‖w - u‖)) := by
          refine Finset.sum_congr rfl ?_
          intro u hu
          have hgt : (1 : ℝ) < ‖w - u‖ := (Finset.mem_filter.mp hu).2
          have hdTne : dT u ≠ 0 := (hS_mem u).mp (Finset.mem_filter.mp hu).1
          have hu0 : u ≠ 0 := by
            intro hz
            have hΛu : Λ u = 0 := by
              have huT : u ∈ Metric.closedBall (0 : ℂ) T₀ :=
                Commons.Analysis.Complex.divisor_mem_of_ne_zero (f := Λ) (a := (0 : ℂ)) (ρ := T₀)
                  (by simpa [dT] using hdTne)
              exact Commons.Analysis.Complex.zero_of_divisor_ne_zero (f := Λ) (a := (0 : ℂ)) (ρ := T₀)
                (hAn (closedBall (0 : ℂ) T₀)) (by simpa [dT] using hdTne)
            subst u
            exact hΛ0 hΛu
          have huw : u ≠ w := by
            intro hz
            have : ‖w - w‖ = 0 := by norm_num
            have : ‖w - u‖ = 0 := by simpa [hz]
            linarith
          have hd0 : 0 ≤ ((dT u : ℤ) : ℝ) := hdiv_nonneg (closedBall (0 : ℂ) T₀) u
          have hnm : ‖((dT u : ℤ) : ℂ)‖ = ((dT u : ℤ) : ℝ) := norm_int_cast hd0
          calc
            ‖hterm u‖ = ‖((dT u : ℤ) : ℂ)‖ * ‖(1 / (w - u) + 1 / u : ℂ)‖ := by
              dsimp [hterm]
              rw [norm_mul]
            _ = ((dT u : ℤ) : ℝ) * (‖w‖ / (‖u‖ * ‖w - u‖)) := by
              rw [hnm, inv_add_inv_norm huw hu0]
    have hfar_finsum : (∑ u ∈ far, ((dT u : ℤ) : ℝ) * (‖w‖ / (‖u‖ * ‖w - u‖))) =
        (∑ᶠ u : ℂ, (((MeromorphicOn.divisor Λ (Metric.closedBall (0 : ℂ) T₀)) u : ℤ) : ℝ) *
          (if (1 : ℝ) < ‖w - u‖ then ‖w‖ / (‖u‖ * ‖w - u‖) else 0)) := by
      let g : ℂ → ℝ := fun u => (((MeromorphicOn.divisor Λ (Metric.closedBall (0 : ℂ) T₀)) u : ℤ) : ℝ) *
          (if (1 : ℝ) < ‖w - u‖ then ‖w‖ / (‖u‖ * ‖w - u‖) else 0)
      have hsubg : Function.support g ⊆ (far : Set ℂ) := by
        intro u hu
        have hgne : g u ≠ 0 := hu
        have hgt : (1 : ℝ) < ‖w - u‖ := by
          by_cases h : (1 : ℝ) < ‖w - u‖
          · exact h
          · have : g u = 0 := by
              dsimp [g]
              simp [h]
            exact False.elim (hgne this)
        have hdTne : (MeromorphicOn.divisor Λ (Metric.closedBall (0 : ℂ) T₀)) u ≠ 0 := by
          intro hd0
          have : g u = 0 := by dsimp [g]; simp [hd0]
          exact hgne this
        exact (Finset.mem_filter.mpr ⟨(hS_mem u).mpr (by simpa [dT] using hdTne), hgt⟩)
      have hfsg := finsum_eq_sum_of_support_subset g (s := far) hsubg
      calc
        (∑ u ∈ far, ((dT u : ℤ) : ℝ) * (‖w‖ / (‖u‖ * ‖w - u‖))) = ∑ u ∈ far, g u := by
          refine Finset.sum_congr rfl ?_
          intro u hu
          have hgt : (1 : ℝ) < ‖w - u‖ := (Finset.mem_filter.mp hu).2
          dsimp [g]
          simp [hgt, dT]
        _ = (∑ᶠ u : ℂ, g u) := hfsg.symm
    have hfar_bound : ‖∑ u ∈ far, hterm u‖ ≤ Kf * (ell R ^ 2 + 1) := by
      calc
        ‖∑ u ∈ far, hterm u‖ ≤ ∑ u ∈ far, ((dT u : ℤ) : ℝ) * (‖w‖ / (‖u‖ * ‖w - u‖)) := hfar_norm_sum
        _ = (∑ᶠ u : ℂ, (((MeromorphicOn.divisor Λ (Metric.closedBall (0 : ℂ) T₀)) u : ℤ) : ℝ) *
          (if (1 : ℝ) < ‖w - u‖ then ‖w‖ / (‖u‖ * ‖w - u‖) else 0)) := hfar_finsum
        _ ≤ Kf * (ell R ^ 2 + 1) := hKf'
    -- assemble |F T₀| ≤ near + far
    calc
      ‖F T₀‖ = ‖(∑ u ∈ near, hterm u) + (∑ u ∈ far, hterm u)‖ := by rw [hF_fin, hpart]
      _ ≤ ‖∑ u ∈ near, hterm u‖ + ‖∑ u ∈ far, hterm u‖ := norm_add_le _ _
      _ ≤ (Kn * (ell R ^ 2 + 1) +
          (∑ᶠ u : ℂ, (((MeromorphicOn.divisor Λ (Metric.closedBall w 1)) u : ℤ) : ℝ) * ((‖w - u‖ : ℝ)⁻¹))) +
          Kf * (ell R ^ 2 + 1) := by
            exact add_le_add hnear_bound hfar_bound
      _ = Kn * (ell R ^ 2 + 1) + Kf * (ell R ^ 2 + 1) +
          (∑ᶠ u : ℂ, (((MeromorphicOn.divisor Λ (Metric.closedBall w 1)) u : ℤ) : ℝ) * ((‖w - u‖ : ℝ)⁻¹)) := by
            ring
  -- arithmetic assembly
  have hKnn0 : 0 ≤ Knn := by dsimp [Knn]; exact le_max_right Kn 0
  have hKfn0 : 0 ≤ Kfn := by dsimp [Kfn]; exact le_max_right Kf 0
  have hKtn0 : 0 ≤ Ktn := by dsimp [Ktn]; exact le_max_right Kt 0
  have hKnle : Kn ≤ Knn := by dsimp [Knn]; exact le_max_left Kn 0
  have hKfle : Kf ≤ Kfn := by dsimp [Kfn]; exact le_max_left Kf 0
  have hellR1 : (1 : ℝ) ≤ ell R := by simpa [ell] using (ell_ge_one (N := N) hR)
  have hellRsq : 1 ≤ (ell R) ^ 2 := by nlinarith [sq_nonneg (ell R - 1)]
  have hpos1 : 0 ≤ (ell R) ^ 2 + 1 := by nlinarith [sq_nonneg (ell R)]
  have hRpos : 0 < R := by linarith
  let nr : ℝ := ∑ᶠ u : ℂ, (((MeromorphicOn.divisor Λ (Metric.closedBall w 1)) u : ℤ) : ℝ) * ((‖w - u‖ : ℝ)⁻¹)
  -- |Λ'/Λ(w)| ≤ |B| + tail + near + far + nr
  have hsub1 : deriv Λ w / Λ w - B = ((deriv Λ w / Λ w - B) - F T₀) + F T₀ := by ring
  have hmain0 : ‖deriv Λ w / Λ w‖ ≤ ‖B‖ + (Ktn * ‖w‖ * ell T₀ / T₀) +
        Kn * (ell R ^ 2 + 1) + Kf * (ell R ^ 2 + 1) + nr := by
    have hnorm0 : ‖deriv Λ w / Λ w‖ ≤ ‖B‖ + ‖deriv Λ w / Λ w - B‖ := by
      have h1 := norm_add_le B (deriv Λ w / Λ w - B)
      have hEq0 : B + (deriv Λ w / Λ w - B) = deriv Λ w / Λ w := by ring
      rwa [hEq0] at h1
    have hnorm1 : ‖deriv Λ w / Λ w - B‖ ≤ Ktn * ‖w‖ * ell T₀ / T₀ + ‖F T₀‖ := by
      have hEq2 : ((deriv Λ w / Λ w - B) - F T₀) + F T₀ = deriv Λ w / Λ w - B := by ring
      calc
        ‖deriv Λ w / Λ w - B‖ = ‖((deriv Λ w / Λ w - B) - F T₀) + F T₀‖ := by rw [hEq2]
        _ ≤ ‖(deriv Λ w / Λ w - B) - F T₀‖ + ‖F T₀‖ := norm_add_le _ _
        _ ≤ Ktn * ‖w‖ * ell T₀ / T₀ + ‖F T₀‖ := by nlinarith [htail]
    nlinarith [hnorm0, hnorm1, hFsplit]
  -- per-part absorption into c·ℓ(R)²
  have hA1 : ‖B‖ ≤ ‖B‖ * (ell R) ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_right hellRsq (norm_nonneg B)]
  have hT1 : Ktn * ‖w‖ * ell T₀ / T₀ ≤ 2 * Ktn * (ell R) ^ 2 := by
    have hwR : ‖w‖ = R := hw
    have hdiv1 : ‖w‖ / T₀ ≤ 1 := by
      rw [hwR]
      dsimp [T₀]
      rw [div_le_iff₀ (by positivity : 0 < 5 * R)]
      nlinarith
    have heq : Ktn * ‖w‖ * ell T₀ / T₀ = Ktn * ell T₀ * (‖w‖ / T₀) := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      ring
    have hnn2 : 0 ≤ Ktn * ell T₀ := mul_nonneg hKtn0 hellT0
    have h3 : Ktn * ell T₀ * (‖w‖ / T₀) ≤ Ktn * ell T₀ := by
      calc
        Ktn * ell T₀ * (‖w‖ / T₀) ≤ Ktn * ell T₀ * 1 := by
          exact mul_le_mul_of_nonneg_left hdiv1 hnn2
        _ = Ktn * ell T₀ := by ring
    have h5 : ell T₀ ≤ 2 * ell R := by
      simpa [ell, T₀] using (ell_five_mul_le_two (N := N) hR)
    have h6 : Ktn * ell T₀ ≤ 2 * Ktn * ell R := by
      have h6' := mul_le_mul_of_nonneg_right h5 hKtn0
      nlinarith
    have h7 : 2 * Ktn * ell R ≤ 2 * Ktn * (ell R) ^ 2 := by
      have hnn3 : 0 ≤ 2 * Ktn := by positivity
      have hellle : ell R ≤ (ell R) ^ 2 := by nlinarith [sq_nonneg (ell R), hellR1]
      exact mul_le_mul_of_nonneg_left hellle hnn3
    calc
      Ktn * ‖w‖ * ell T₀ / T₀ = Ktn * ell T₀ * (‖w‖ / T₀) := heq
      _ ≤ Ktn * ell T₀ := h3
      _ ≤ 2 * Ktn * ell R := h6
      _ ≤ 2 * Ktn * (ell R) ^ 2 := h7
  have hN1 : Kn * (ell R ^ 2 + 1) ≤ 2 * Knn * (ell R) ^ 2 := by
    have h1 : Kn * ((ell R) ^ 2 + 1) ≤ Knn * ((ell R) ^ 2 + 1) :=
      mul_le_mul_of_nonneg_right hKnle hpos1
    have h2 : Knn * ((ell R) ^ 2 + 1) ≤ 2 * Knn * (ell R) ^ 2 := by
      exact quad_absorb hellR1 hKnn0
    exact le_trans h1 h2
  have hF1 : Kf * (ell R ^ 2 + 1) ≤ 2 * Kfn * (ell R) ^ 2 := by
    have h1 : Kf * ((ell R) ^ 2 + 1) ≤ Kfn * ((ell R) ^ 2 + 1) :=
      mul_le_mul_of_nonneg_right hKfle hpos1
    have h2 : Kfn * ((ell R) ^ 2 + 1) ≤ 2 * Kfn * (ell R) ^ 2 := by
      exact quad_absorb hellR1 hKfn0
    exact le_trans h1 h2
  have hfinal0 : ‖deriv Λ w / Λ w‖ ≤ c * (ell R) ^ 2 + nr := by
    calc
      ‖deriv Λ w / Λ w‖ ≤ ‖B‖ + (Ktn * ‖w‖ * ell T₀ / T₀) +
            Kn * (ell R ^ 2 + 1) + Kf * (ell R ^ 2 + 1) + nr := hmain0
      _ ≤ (‖B‖ + 2 * Ktn + 2 * Knn + 2 * Kfn) * (ell R) ^ 2 + nr := by
        nlinarith [hA1, hT1, hN1, hF1]
      _ = c * (ell R) ^ 2 + nr := by dsimp [c]; ring
  -- convert from Λ / ell / nr back to the statement's completedLFunction
  simpa [Λ, ell, nr] using hfinal0

end Commons.NumberTheory.Linnik
