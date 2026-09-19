import Mathlib.Analysis.Meromorphic.NormalForm
import Submission.Commons.NumberTheory.DirichletCharacter.zerosInStrip
import Submission.Commons.NumberTheory.DirichletCharacter.completedL_order_eq_one_sub
import Submission.Commons.NumberTheory.Linnik.divisor_eq_closedBall_subset
import Submission.Commons.Analysis.Complex.circleLogDerivContour_bound

noncomputable section
open scoped Real Topology BigOperators

namespace Commons.NumberTheory.DirichletCharacter

-- ======================= generic divisor / analyticity helpers =======================

private lemma inv_ne_one_of_ne_one {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) : χ⁻¹ ≠ 1 := by
  intro h
  apply hχ
  calc
    χ = (χ⁻¹)⁻¹ := by rw [inv_inv]
    _ = (1 : DirichletCharacter ℂ N)⁻¹ := by rw [h]
    _ = 1 := by simp

private lemma completedLFunction_analyticOnNhd {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (U : Set ℂ) :
    AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ) U := by
  intro z hz
  exact (DirichletCharacter.differentiable_completedLFunction hχ).analyticAt z

private lemma divisor_real_nonneg_of_analyticOnNhd {f : ℂ → ℂ} {U : Set ℂ} {z : ℂ}
    (hf : AnalyticOnNhd ℂ f U) :
    (0 : ℝ) ≤ ((MeromorphicOn.divisor f U z : ℤ) : ℝ) := by
  by_cases hz : z ∈ U
  · rw [MeromorphicOn.divisor_apply hf.meromorphicOn hz]
    have hAn : AnalyticAt ℂ f z := hf z hz
    have hNF := hAn.meromorphicNFAt
    have hord : (0 : WithTop ℤ) ≤ meromorphicOrderAt f z :=
      (MeromorphicNFAt.meromorphicOrderAt_nonneg_iff_analyticAt hNF).2 hAn
    have hnn : (0 : ℤ) ≤ (meromorphicOrderAt f z).untop₀ :=
      (WithTop.untop₀_nonneg (α := ℤ) (a := meromorphicOrderAt f z)).mpr hord
    exact_mod_cast hnn
  · rw [MeromorphicOn.divisor_def]
    rw [if_neg (by intro h; exact hz h.2)]
    norm_num

private lemma divisor_zero_of_analytic_ne_zero {f : ℂ → ℂ} {U : Set ℂ} {z : ℂ}
    (hf : AnalyticOnNhd ℂ f U) (hz : z ∈ U) (hfz : f z ≠ 0) :
    MeromorphicOn.divisor f U z = 0 := by
  rw [MeromorphicOn.divisor_apply hf.meromorphicOn hz]
  have hAn : AnalyticAt ℂ f z := hf z hz
  have hord : meromorphicOrderAt f z = 0 := by
    rw [hAn.meromorphicOrderAt_eq]
    have h0 : analyticOrderAt f z = 0 := analyticOrderAt_eq_zero.mpr (Or.inr hfz)
    simp [h0]
  simp [hord]

private lemma divisor_eq_zero_of_not_mem {f : ℂ → ℂ} (U : Set ℂ) {z : ℂ} (hz : z ∉ U) :
    MeromorphicOn.divisor f U z = 0 := by
  rw [MeromorphicOn.divisor_def, if_neg]
  intro h; exact hz h.2

private lemma divisor_real_finiteSupport_ball {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (_hχ : χ ≠ 1) (a : ℂ) (ρ : ℝ) :
    Function.HasFiniteSupport
      (fun u : ℂ => (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Metric.closedBall a ρ)) u : ℤ) : ℝ)) := by
  have hfinZ : (Function.support
      (fun u : ℂ => ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Metric.closedBall a ρ)) u : ℤ))).Finite := by
    simpa [Function.HasFiniteSupport] using
      ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Metric.closedBall a ρ)).finiteSupport (isCompact_closedBall a ρ))
  have hsub : Function.support
      (fun u : ℂ => (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Metric.closedBall a ρ)) u : ℤ) : ℝ)) ⊆
      Function.support
      (fun u : ℂ => ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Metric.closedBall a ρ)) u : ℤ)) := by
    intro u hu
    rw [Function.mem_support] at hu ⊢
    exact fun hz => hu (by exact_mod_cast hz)
  exact hfinZ.subset hsub

private lemma indicator_nonneg {p : Prop} [Decidable p] : (0 : ℝ) ≤ (if p then 1 else 0) := by
  split_ifs <;> norm_num

/-- A point in the critical strip with `|Im| ≤ r` lies in the disk of radius `r+1`. -/
private lemma norm_le_add_one_of_strip {u : ℂ} {r : ℝ}
    (hre_lo : 0 < u.re) (hre_hi : u.re < 1) (him : |u.im| ≤ r) :
    ‖u‖ ≤ r + 1 := by
  have hre : |u.re| ≤ 1 := by
    rw [abs_of_pos hre_lo]
    exact le_of_lt hre_hi
  calc
    ‖u‖ ≤ |u.re| + |u.im| := Complex.norm_le_abs_re_add_abs_im u
    _ ≤ 1 + r := by linarith
    _ = r + 1 := by ring

-- =================================== the theorem ===================================

/-- The divisor-weighted zero window `a ≤ |Im u| ≤ b` of the completed L-function of a
primitive non-trivial `χ` is bounded by the sum of two open-rectangle divisor counts
`(−1 < Re < 2, α < Im < β)` — one for `χ`, one for `χ⁻¹` — counted on the enlarged ball
`closedBall 0 (b+4)`.

Concretely, with `a ≥ 0` and containment heights `αχ < a ≤ b < βχ`, `αψ < a ≤ b < βψ`:

    ∑ᶠ_u (divisor Λχ on closedBall 0 (b+1)) u · 𝟙[a ≤ |Im u| ≤ b]
        ≤ ∑ᶠ_u (divisor Λχ on closedBall 0 (b+4)) u · 𝟙[−1 < Re u < 2 ∧ αχ < Im u < βχ]
        + ∑ᶠ_u (divisor Λ(χ⁻¹) on closedBall 0 (b+4)) u · 𝟙[−1 < Re u < 2 ∧ αψ < Im u < βψ]

Every zero of `Λ(ψ, ·)` lies in `0 < Re < 1` (`zerosInStrip`); zeros with positive
imaginary part `Im u ∈ [a,b] ⊆ (α, β)` contribute to the first rectangle count (their
`closedBall 0 (b+1)`-divisor equals the `closedBall 0 (b+4)`-divisor, both being the
finite zero order — use `Commons.NumberTheory.Linnik.divisor_eq_closedBall_subset`, the
analyticity of the entire `Λ`, and the elementary bound `‖u‖ ≤ b+1` from `Re u < 1`,
`|Im u| ≤ b`).  Zeros with negative imaginary part `Im u ∈ [−b,−a]` are mapped by the
functional equation `u ↦ 1−u` to zeros of `Λ(χ⁻¹,·)` with `Im(1−u) ∈ [a,b] ⊆ (αψ,βψ)`
and `Re(1−u) ∈ (0,1)`; their orders agree (`meromorphicOrderAt` transfer through
`completedLFunction_eq`, i.e. the lemma
`Commons.NumberTheory.DirichletCharacter.completedL_order_eq_one_sub` if already in the
commons, otherwise prove it inside this file as a private lemma).  Summing over the
finite supports (divisor finite support on the compact balls) gives the inequality;
all divisor coefficients are non-negative (whole functions).

Do not require any zero-free-height hypothesis here: the heights only need the strict
containment `α < a`, `b < β`.  You may assume `hχ : χ ≠ 1`, `hχprim : χ.IsPrimitive`,
and `0 ≤ a`, plus `a ≤ b` if needed. -/
theorem window_le_rectSum {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive) {a b αχ βχ αψ βψ : ℝ}
    (ha : (0 : ℝ) ≤ a) (hab : a ≤ b)
    (hαχ : αχ < a) (hbχ : b < βχ) (hαψ : αψ < a) (hbψ : b < βψ) :
    (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall (0 : ℂ) (b + 1))) u : ℤ) : ℝ) *
        (if (a ≤ |Complex.im u| ∧ |Complex.im u| ≤ b) then 1 else 0)) ≤
      (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Metric.closedBall (0 : ℂ) (b + 4))) u : ℤ) : ℝ) *
          (if (-1 < u.re ∧ u.re < 2 ∧ αχ < u.im ∧ u.im < βχ) then 1 else 0)) +
      (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction (χ⁻¹))
          (Metric.closedBall (0 : ℂ) (b + 4))) u : ℤ) : ℝ) *
          (if (-1 < u.re ∧ u.re < 2 ∧ αψ < u.im ∧ u.im < βψ) then 1 else 0)) := by
  classical
  have hb_nonneg : 0 ≤ b := le_trans ha hab
  let Λ : ℂ → ℂ := DirichletCharacter.completedLFunction χ
  let Λi : ℂ → ℂ := DirichletCharacter.completedLFunction (χ⁻¹)
  have hχi : χ⁻¹ ≠ 1 := inv_ne_one_of_ne_one χ hχ
  have hΛan (U : Set ℂ) : AnalyticOnNhd ℂ Λ U := by
    dsimp [Λ]
    exact completedLFunction_analyticOnNhd χ hχ U
  have hΛian (U : Set ℂ) : AnalyticOnNhd ℂ Λi U := by
    dsimp [Λi]
    exact completedLFunction_analyticOnNhd (χ := χ⁻¹) hχi U
  let F1 : ℂ → ℝ := fun u => (((MeromorphicOn.divisor Λ (Metric.closedBall (0 : ℂ) (b + 1))) u : ℤ) : ℝ)
  let F4 : ℂ → ℝ := fun u => (((MeromorphicOn.divisor Λ (Metric.closedBall (0 : ℂ) (b + 4))) u : ℤ) : ℝ)
  let Fi4 : ℂ → ℝ := fun u => (((MeromorphicOn.divisor Λi (Metric.closedBall (0 : ℂ) (b + 4))) u : ℤ) : ℝ)
  let W : ℂ → ℝ := fun u => if (a ≤ |u.im| ∧ |u.im| ≤ b) then 1 else 0
  let Wp : ℂ → ℝ := fun u => if ((a ≤ |u.im| ∧ |u.im| ≤ b) ∧ 0 ≤ u.im) then 1 else 0
  let Wn : ℂ → ℝ := fun u => if ((a ≤ |u.im| ∧ |u.im| ≤ b) ∧ u.im < 0) then 1 else 0
  let R1 : ℂ → ℝ := fun u => if (-1 < u.re ∧ u.re < 2 ∧ αχ < u.im ∧ u.im < βχ) then 1 else 0
  let R2 : ℂ → ℝ := fun u => if (-1 < u.re ∧ u.re < 2 ∧ αψ < u.im ∧ u.im < βψ) then 1 else 0
  -- nonnegativity of the divisor coefficients and of the rectangle indicators
  have hF4nonneg : ∀ u : ℂ, 0 ≤ F4 u := by
    intro u
    dsimp [F4]
    exact divisor_real_nonneg_of_analyticOnNhd (hΛan (Metric.closedBall (0 : ℂ) (b + 4)))
  have hFi4nonneg : ∀ u : ℂ, 0 ≤ Fi4 u := by
    intro u
    dsimp [Fi4]
    exact divisor_real_nonneg_of_analyticOnNhd (hΛian (Metric.closedBall (0 : ℂ) (b + 4)))
  have hR1ge0 : ∀ u : ℂ, 0 ≤ R1 u := by
    intro u; dsimp [R1]; exact indicator_nonneg
  have hR2ge0 : ∀ u : ℂ, 0 ≤ R2 u := by
    intro u; dsimp [R2]; exact indicator_nonneg
  -- finite support of every weighted divisor function
  have hfinF1 : Function.HasFiniteSupport F1 := by
    dsimp [F1, Λ]
    exact divisor_real_finiteSupport_ball χ hχ (0 : ℂ) (b + 1)
  have hfinF4 : Function.HasFiniteSupport F4 := by
    dsimp [F4, Λ]
    exact divisor_real_finiteSupport_ball χ hχ (0 : ℂ) (b + 4)
  have hfinFi4 : Function.HasFiniteSupport Fi4 := by
    dsimp [Fi4, Λi]
    exact divisor_real_finiteSupport_ball (χ := χ⁻¹) hχi (0 : ℂ) (b + 4)
  have hfinWp : Function.HasFiniteSupport (fun u : ℂ => F1 u * Wp u) := by
    exact Function.HasFiniteSupport.mul_left hfinF1 Wp
  have hfinWn : Function.HasFiniteSupport (fun u : ℂ => F1 u * Wn u) := by
    exact Function.HasFiniteSupport.mul_left hfinF1 Wn
  have hfinF4R1 : Function.HasFiniteSupport (fun u : ℂ => F4 u * R1 u) := by
    exact Function.HasFiniteSupport.mul_left hfinF4 R1
  have hfinFi4R2 : Function.HasFiniteSupport (fun u : ℂ => Fi4 u * R2 u) := by
    exact Function.HasFiniteSupport.mul_left hfinFi4 R2
  -- the window splits into its nonnegative- and negative-imaginary-part pieces
  have hWpt : ∀ u : ℂ, W u = Wp u + Wn u := by
    intro u
    by_cases hwin : a ≤ |u.im| ∧ |u.im| ≤ b
    · dsimp [W, Wp, Wn]
      rw [if_pos hwin]
      by_cases hge : 0 ≤ u.im
      · have hlt : ¬ u.im < 0 := by linarith
        rw [if_pos (And.intro hwin hge)]
        rw [if_neg (fun h => hlt h.2)]
        norm_num
      · have hlt : u.im < 0 := lt_of_not_ge hge
        rw [if_neg (fun h => hge h.2)]
        rw [if_pos (And.intro hwin hlt)]
        norm_num
    · dsimp [W, Wp, Wn]
      rw [if_neg hwin]
      have hnp : ¬ ((a ≤ |u.im| ∧ |u.im| ≤ b) ∧ 0 ≤ u.im) := fun h => hwin h.1
      have hnn : ¬ ((a ≤ |u.im| ∧ |u.im| ≤ b) ∧ u.im < 0) := fun h => hwin h.1
      rw [if_neg hnp, if_neg hnn]
      norm_num
  -- (positive imaginary part) pointwise: F1 u * Wp u ≤ F4 u * R1 u
  have hpoint_pos : ∀ u : ℂ, F1 u * Wp u ≤ F4 u * R1 u := by
    intro u
    by_cases hwin : (a ≤ |u.im| ∧ |u.im| ≤ b) ∧ 0 ≤ u.im
    · by_cases hF : F1 u = 0
      · have hwp : Wp u = 1 := by dsimp [Wp]; rw [if_pos hwin]
        rw [hF, hwp]
        simp
        exact mul_nonneg (hF4nonneg u) (hR1ge0 u)
      · have hwp : Wp u = 1 := by dsimp [Wp]; rw [if_pos hwin]
        have hFne_int : ((MeromorphicOn.divisor Λ (Metric.closedBall (0 : ℂ) (b + 1))) u : ℤ) ≠ 0 := by
          intro hz
          apply hF
          dsimp [F1]
          exact_mod_cast hz
        have huB1 : u ∈ Metric.closedBall (0 : ℂ) (b + 1) := by
          by_contra hnot
          have hz : (MeromorphicOn.divisor Λ (Metric.closedBall (0 : ℂ) (b + 1))) u = 0 :=
            divisor_eq_zero_of_not_mem (Metric.closedBall (0 : ℂ) (b + 1)) hnot
          exact hFne_int hz
        have hΛ0 : Λ u = 0 := by
          by_contra hnf
          have hd : (MeromorphicOn.divisor Λ (Metric.closedBall (0 : ℂ) (b + 1))) u = 0 :=
            divisor_zero_of_analytic_ne_zero (hΛan (Metric.closedBall (0 : ℂ) (b + 1))) huB1 hnf
          exact hFne_int hd
        have hst := zerosInStrip χ hχ hχprim u (by simpa [Λ] using hΛ0)
        have hwin' : a ≤ u.im ∧ u.im ≤ b := by
          have hge0 : 0 ≤ u.im := hwin.2
          have hlo : a ≤ |u.im| := hwin.1.1
          have hhi : |u.im| ≤ b := hwin.1.2
          constructor
          · rwa [abs_of_nonneg hge0] at hlo
          · rwa [abs_of_nonneg hge0] at hhi
        have huB4 : u ∈ Metric.closedBall (0 : ℂ) (b + 4) := by
          have hn := norm_le_add_one_of_strip (u := u) (r := b + 3) hst.1 hst.2 (by linarith [hwin.1.2])
          have hnorm : ‖u‖ ≤ b + 4 := by linarith
          simpa [Metric.mem_closedBall, dist_eq_norm] using hnorm
        have heq : F1 u = F4 u := by
          dsimp [F1, F4]
          have heqZ : MeromorphicOn.divisor Λ (Metric.closedBall (0 : ℂ) (b + 1)) u =
              MeromorphicOn.divisor Λ (Metric.closedBall (0 : ℂ) (b + 4)) u :=
            Commons.NumberTheory.Linnik.divisor_eq_closedBall_subset (f := Λ) (a := (0 : ℂ))
              (b := (0 : ℂ)) (ra := b + 1) (rb := b + 4)
              (hf := hΛan (Metric.closedBall (0 : ℂ) (b + 1) ∪ Metric.closedBall (0 : ℂ) (b + 4)))
              huB1 huB4
          exact congrArg (fun n : ℤ => (n : ℝ)) heqZ
        have hc1 : -1 < u.re := by linarith [hst.1]
        have hc2 : u.re < 2 := by linarith [hst.2]
        have hc3 : αχ < u.im := by linarith [hαχ, hwin'.1]
        have hc4 : u.im < βχ := by linarith [hbχ, hwin'.2]
        have hR1 : R1 u = 1 := by
          dsimp [R1]
          rw [if_pos (And.intro hc1 (And.intro hc2 (And.intro hc3 hc4)))]
        rw [hwp, hR1, heq]
    · have hwp : Wp u = 0 := by
        dsimp [Wp]
        rw [if_neg hwin]
      rw [hwp]
      simp
      exact mul_nonneg (hF4nonneg u) (hR1ge0 u)
  -- (negative imaginary part) pointwise, reflected: F1 u * Wn u ≤ Fi4 (1-u) * R2 (1-u)
  have hpoint_neg : ∀ u : ℂ, F1 u * Wn u ≤ Fi4 (1 - u) * R2 (1 - u) := by
    intro u
    by_cases hwin : (a ≤ |u.im| ∧ |u.im| ≤ b) ∧ u.im < 0
    · by_cases hF : F1 u = 0
      · have hwn : Wn u = 1 := by dsimp [Wn]; rw [if_pos hwin]
        rw [hF, hwn]
        simp
        exact mul_nonneg (hFi4nonneg (1 - u)) (hR2ge0 (1 - u))
      · have hwn : Wn u = 1 := by dsimp [Wn]; rw [if_pos hwin]
        have hFne_int : ((MeromorphicOn.divisor Λ (Metric.closedBall (0 : ℂ) (b + 1))) u : ℤ) ≠ 0 := by
          intro hz
          apply hF
          dsimp [F1]
          exact_mod_cast hz
        have huB1 : u ∈ Metric.closedBall (0 : ℂ) (b + 1) := by
          by_contra hnot
          have hz : (MeromorphicOn.divisor Λ (Metric.closedBall (0 : ℂ) (b + 1))) u = 0 :=
            divisor_eq_zero_of_not_mem (Metric.closedBall (0 : ℂ) (b + 1)) hnot
          exact hFne_int hz
        have hΛ0 : Λ u = 0 := by
          by_contra hnf
          have hd : (MeromorphicOn.divisor Λ (Metric.closedBall (0 : ℂ) (b + 1))) u = 0 :=
            divisor_zero_of_analytic_ne_zero (hΛan (Metric.closedBall (0 : ℂ) (b + 1))) huB1 hnf
          exact hFne_int hd
        have hst := zerosInStrip χ hχ hχprim u (by simpa [Λ] using hΛ0)
        let w : ℂ := 1 - u
        have hwinhi : |u.im| ≤ b := hwin.1.2
        have h_absu : |u.im| = -u.im := abs_of_neg hwin.2
        have hw_re : w.re = 1 - u.re := by dsimp [w]
        have hw_im : w.im = -u.im := by simp [w]
        have hwre_lo : 0 < w.re := by rw [hw_re]; linarith
        have hwre_hi : w.re < 1 := by rw [hw_re]; linarith
        have hwim_le : -u.im ≤ b := by
          rw [← h_absu]
          exact hwinhi
        have hwim_abs : |w.im| ≤ b := by
          rw [hw_im]
          rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ -u.im)]
          exact hwim_le
        have hw_norm : ‖w‖ ≤ b + 4 := by
          have hn := norm_le_add_one_of_strip (u := w) (r := b + 3) hwre_lo hwre_hi (by linarith)
          linarith
        have huB4w : w ∈ Metric.closedBall (0 : ℂ) (b + 4) := by
          simpa [Metric.mem_closedBall, dist_eq_norm] using hw_norm
        have hwin_lo : a ≤ |u.im| := hwin.1.1
        have hwim_ge_a : a ≤ w.im := by
          rw [hw_im]
          rwa [h_absu] at hwin_lo
        have hwim_le_b : w.im ≤ b := by
          rw [hw_im]
          exact hwim_le
        have hc1 : -1 < w.re := by linarith
        have hc2 : w.re < 2 := by linarith
        have hc3 : αψ < w.im := by linarith [hαψ, hwim_ge_a]
        have hc4 : w.im < βψ := by linarith [hbψ, hwim_le_b]
        have hR2w : R2 w = 1 := by
          dsimp [R2]
          rw [if_pos (And.intro hc1 (And.intro hc2 (And.intro hc3 hc4)))]
        have hord : meromorphicOrderAt (DirichletCharacter.completedLFunction χ) u =
            meromorphicOrderAt (DirichletCharacter.completedLFunction (χ⁻¹)) (1 - u) :=
          completedL_order_eq_one_sub χ hχ hχprim (by simpa [Λ] using hΛ0)
        have heq : F1 u = Fi4 w := by
          dsimp [F1, Fi4]
          have hdv1 : (MeromorphicOn.divisor Λ (Metric.closedBall (0 : ℂ) (b + 1))) u =
              (meromorphicOrderAt Λ u).untop₀ :=
            MeromorphicOn.divisor_apply (hΛan (Metric.closedBall (0 : ℂ) (b + 1))).meromorphicOn huB1
          have hdv2 : (MeromorphicOn.divisor Λi (Metric.closedBall (0 : ℂ) (b + 4))) w =
              (meromorphicOrderAt Λi w).untop₀ :=
            MeromorphicOn.divisor_apply (hΛian (Metric.closedBall (0 : ℂ) (b + 4))).meromorphicOn huB4w
          rw [hdv1, hdv2]
          have hord' : (meromorphicOrderAt Λ u).untop₀ = (meromorphicOrderAt Λi w).untop₀ :=
            congrArg (WithTop.untop₀ (α := ℤ)) (by simpa [Λ, Λi, w] using hord)
          exact congrArg (fun n : ℤ => (n : ℝ)) hord'
        rw [hwn, hR2w, heq]
    · have hwn : Wn u = 0 := by
        dsimp [Wn]
        rw [if_neg hwin]
      rw [hwn]
      simp
      exact mul_nonneg (hFi4nonneg (1 - u)) (hR2ge0 (1 - u))
  -- sums over the finite supports
  have hF1W_eq : (∑ᶠ u : ℂ, F1 u * W u) =
      (∑ᶠ u : ℂ, F1 u * Wp u) + (∑ᶠ u : ℂ, F1 u * Wn u) := by
    calc
      (∑ᶠ u : ℂ, F1 u * W u) = ∑ᶠ u : ℂ, (F1 u * Wp u + F1 u * Wn u) := by
        refine finsum_congr ?_
        intro u
        rw [hWpt u]
        ring
      _ = (∑ᶠ u : ℂ, F1 u * Wp u) + (∑ᶠ u : ℂ, F1 u * Wn u) := finsum_add_distrib hfinWp hfinWn
  have hpos_sum : (∑ᶠ u : ℂ, F1 u * Wp u) ≤ (∑ᶠ u : ℂ, F4 u * R1 u) := by
    exact finsum_le_finsum' hfinWp hfinF4R1 hpoint_pos
  have hg_inj : Function.Injective (fun u : ℂ => 1 - u) := by
    exact (sub_right_injective (b := (1 : ℂ)))
  have hbij : Function.Bijective (fun u : ℂ => 1 - u) := by
    refine ⟨hg_inj, ?_⟩
    intro w
    refine ⟨1 - w, ?_⟩
    ring
  have hfinFi4R2refl : Function.HasFiniteSupport
      (fun u : ℂ => Fi4 (1 - u) * R2 (1 - u)) := by
    change Function.HasFiniteSupport (((fun u : ℂ => Fi4 u * R2 u) ∘ (fun u : ℂ => 1 - u)))
    exact Function.HasFiniteSupport.comp_of_injective
      (f := fun u : ℂ => Fi4 u * R2 u) (g := fun u : ℂ => 1 - u) hg_inj hfinFi4R2
  have hneg_sum : (∑ᶠ u : ℂ, F1 u * Wn u) ≤ (∑ᶠ u : ℂ, Fi4 u * R2 u) := by
    have h1 : (∑ᶠ u : ℂ, F1 u * Wn u) ≤ (∑ᶠ u : ℂ, Fi4 (1 - u) * R2 (1 - u)) :=
      finsum_le_finsum' hfinWn hfinFi4R2refl hpoint_neg
    have h2 : (∑ᶠ u : ℂ, Fi4 (1 - u) * R2 (1 - u)) = (∑ᶠ u : ℂ, Fi4 u * R2 u) :=
      finsum_comp (e := fun u : ℂ => 1 - u) (g := fun u : ℂ => Fi4 u * R2 u) hbij
    rwa [h2] at h1
  have hbound : (∑ᶠ u : ℂ, F1 u * W u) ≤
      (∑ᶠ u : ℂ, F4 u * R1 u) + (∑ᶠ u : ℂ, Fi4 u * R2 u) := by
    calc
      (∑ᶠ u : ℂ, F1 u * W u) = (∑ᶠ u : ℂ, F1 u * Wp u) + (∑ᶠ u : ℂ, F1 u * Wn u) := hF1W_eq
      _ ≤ (∑ᶠ u : ℂ, F4 u * R1 u) + (∑ᶠ u : ℂ, Fi4 u * R2 u) := add_le_add hpos_sum hneg_sum
  simpa [F1, F4, Fi4, W, R1, R2, Λ, Λi] using hbound

end Commons.NumberTheory.DirichletCharacter