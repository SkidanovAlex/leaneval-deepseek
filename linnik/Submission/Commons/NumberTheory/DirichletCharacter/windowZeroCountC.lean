import Mathlib
import Submission.Commons.NumberTheory.DirichletCharacter.zerosInStrip
import Submission.Commons.NumberTheory.Linnik.divisor_eq_closedBall_subset
import Submission.Commons.NumberTheory.Linnik.completedL_local_zeroCount

noncomputable section
open Complex DirichletCharacter Metric
open scoped Real

namespace Commons.NumberTheory.DirichletCharacter

-- ============================ generic divisor helpers ============================

private lemma divisor_nonneg_of_analyticOnNhd {f : ℂ → ℂ} {U : Set ℂ} {z : ℂ}
    (hf : AnalyticOnNhd ℂ f U) :
    (0 : ℤ) ≤ MeromorphicOn.divisor f U z := by
  by_cases hz : z ∈ U
  · rw [MeromorphicOn.divisor_apply hf.meromorphicOn hz]
    have hAn : AnalyticAt ℂ f z := hf z hz
    have hNF := hAn.meromorphicNFAt
    have hord : (0 : WithTop ℤ) ≤ meromorphicOrderAt f z :=
      (MeromorphicNFAt.meromorphicOrderAt_nonneg_iff_analyticAt hNF).2 hAn
    exact (WithTop.untop₀_nonneg (α := ℤ) (a := meromorphicOrderAt f z)).mpr hord
  · rw [MeromorphicOn.divisor_def]
    rw [if_neg]
    intro h
    exact hz h.2

private lemma divisor_real_nonneg_of_analyticOnNhd {f : ℂ → ℂ} {U : Set ℂ} {z : ℂ}
    (hf : AnalyticOnNhd ℂ f U) :
    (0 : ℝ) ≤ ((MeromorphicOn.divisor f U z : ℤ) : ℝ) := by
  exact_mod_cast divisor_nonneg_of_analyticOnNhd hf

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

private lemma completedLFunction_analyticOnNhd {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (U : Set ℂ) :
    AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ) U := by
  intro z hz
  exact (differentiable_completedLFunction hχ).analyticAt z

-- ============================ containment of zeros ============================

private lemma zero_mem_upper_disk {u : ℂ} {a b t ρ : ℝ}
    (hre_lo : 0 < u.re) (hre_hi : u.re < 1)
    (haim : a ≤ u.im) (hbim : u.im ≤ b)
    (ht : t = (a + b) / 2) (hrho : ρ = (b - a) / 2 + 2) :
    u ∈ Metric.closedBall ((2 : ℂ) + Complex.I * (t : ℂ)) ρ := by
  rw [Metric.mem_closedBall, dist_eq_norm]
  let c : ℂ := (2 : ℂ) + Complex.I * (t : ℂ)
  have htri := Complex.norm_le_abs_re_add_abs_im (u - c)
  have hre : |u.re - 2| ≤ 2 := by
    have hlt : u.re - 2 < 0 := by linarith only [hre_lo, hre_hi]
    rw [abs_of_neg hlt]
    linarith only [hre_lo]
  have him : |u.im - t| ≤ (b - a) / 2 := by
    rw [ht]
    have h1 : u.im - (a + b) / 2 ≤ (b - a) / 2 := by linarith only [hbim]
    have h2 : -((b - a) / 2) ≤ u.im - (a + b) / 2 := by linarith only [haim]
    rw [abs_le]
    exact ⟨h2, h1⟩
  calc
    ‖u - c‖ ≤ |(u - c).re| + |(u - c).im| := htri
    _ = |u.re - 2| + |u.im - t| := by simp [c]
    _ ≤ 2 + (b - a) / 2 := add_le_add hre him
    _ = ρ := by rw [hrho]; ring

private lemma zero_mem_lower_disk {u : ℂ} {a b t ρ : ℝ}
    (hre_lo : 0 < u.re) (hre_hi : u.re < 1)
    (hlo : -b ≤ u.im) (hhi : u.im ≤ -a)
    (ht : t = (a + b) / 2) (hrho : ρ = (b - a) / 2 + 2) :
    u ∈ Metric.closedBall ((2 : ℂ) + Complex.I * ((-t : ℝ) : ℂ)) ρ := by
  rw [Metric.mem_closedBall, dist_eq_norm]
  let c : ℂ := (2 : ℂ) + Complex.I * ((-t : ℝ) : ℂ)
  have htri := Complex.norm_le_abs_re_add_abs_im (u - c)
  have hre : |u.re - 2| ≤ 2 := by
    have hlt : u.re - 2 < 0 := by linarith only [hre_lo, hre_hi]
    rw [abs_of_neg hlt]
    linarith only [hre_lo]
  have him : |u.im + t| ≤ (b - a) / 2 := by
    rw [ht]
    have h1 : u.im + (a + b) / 2 ≤ (b - a) / 2 := by linarith only [hhi]
    have h2 : -((b - a) / 2) ≤ u.im + (a + b) / 2 := by linarith only [hlo]
    rw [abs_le]
    exact ⟨h2, h1⟩
  calc
    ‖u - c‖ ≤ |(u - c).re| + |(u - c).im| := htri
    _ = |u.re - 2| + |u.im + t| := by simp [c]
    _ ≤ 2 + (b - a) / 2 := add_le_add hre him
    _ = ρ := by rw [hrho]; ring

private lemma window_split {u : ℂ} {a b : ℝ} (_ha : 1 ≤ a) (h : a ≤ |u.im| ∧ |u.im| ≤ b) :
    (a ≤ u.im ∧ u.im ≤ b) ∨ (-b ≤ u.im ∧ u.im ≤ -a) := by
  rcases h with ⟨hlo, hhi⟩
  have hb1 : u.im ≤ b := le_trans (le_abs_self u.im) hhi
  have hb2 : -b ≤ u.im := by
    have hneg : -|u.im| ≤ u.im := neg_abs_le u.im
    exact le_trans (by linarith only [hhi]) hneg
  by_cases hpos : 0 ≤ u.im
  · left
    rw [abs_of_nonneg hpos] at hlo
    exact ⟨hlo, hb1⟩
  · right
    have : u.im ≤ 0 := le_of_not_ge hpos
    rw [abs_of_nonpos this] at hlo
    exact ⟨hb2, by linarith only [hlo]⟩

-- ============================ the target theorem ============================

theorem windowZeroCountC {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive) :
    ∃ c : ℝ, 0 < c ∧ ∀ a b : ℝ, 1 ≤ a → a ≤ b →
      (∑ᶠ u : ℂ,
          (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
              (Metric.closedBall (0 : ℂ) (b + 1))) u : ℤ) : ℝ) *
            (if (a ≤ |Complex.im u| ∧ |Complex.im u| ≤ b) then 1 else 0)) ≤
        c * (b - a + 2) * (Real.log (b + 3) + Real.log (N : ℝ) + 2) := by
  classical
  rcases Commons.NumberTheory.Linnik.completedL_local_zeroCount χ hχ hχprim with ⟨c0, hc0⟩
  let c0n : ℝ := max c0 0
  let C : ℝ := max (4 * c0n) 1
  have hCpos : 0 < C := by
    dsimp [C]
    exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_right (4 * c0n) 1)
  refine ⟨C, hCpos, ?_⟩
  intro a b ha hab
  let Λ : ℂ → ℂ := DirichletCharacter.completedLFunction χ
  have hΛdiff : Differentiable ℂ Λ := by simpa [Λ] using (differentiable_completedLFunction hχ)
  have hΛan (U : Set ℂ) : AnalyticOnNhd ℂ Λ U := by
    intro z hz
    exact hΛdiff.analyticAt z
  have hstrip : ∀ u : ℂ, Λ u = 0 → 0 < u.re ∧ u.re < 1 := by
    intro u hu
    exact zerosInStrip χ hχ hχprim u (by simpa [Λ] using hu)
  let t : ℝ := (a + b) / 2
  let ρ : ℝ := (b - a) / 2 + 2
  let F : ℂ → ℝ := fun u => (((MeromorphicOn.divisor Λ (Metric.closedBall (0 : ℂ) (b + 1))) u : ℤ) : ℝ)
  let Gp : ℂ → ℝ := fun u => (((MeromorphicOn.divisor Λ (Metric.closedBall ((2 : ℂ) + Complex.I * (t : ℂ)) ρ)) u : ℤ) : ℝ)
  let Gm : ℂ → ℝ := fun u => (((MeromorphicOn.divisor Λ (Metric.closedBall ((2 : ℂ) + Complex.I * ((-t : ℝ) : ℂ)) ρ)) u : ℤ) : ℝ)
  let w : ℂ → ℝ := fun u => if a ≤ |u.im| ∧ |u.im| ≤ b then 1 else 0
  let L : ℝ := Real.log (b + 3) + Real.log (N : ℝ) + 2
  -- nonnegativity of the three divisor functions
  have hF0 : ∀ u : ℂ, 0 ≤ F u := by
    intro u
    dsimp [F]
    exact divisor_real_nonneg_of_analyticOnNhd (completedLFunction_analyticOnNhd χ hχ (Metric.closedBall (0 : ℂ) (b + 1)))
  have hGp0 : ∀ u : ℂ, 0 ≤ Gp u := by
    intro u
    dsimp [Gp]
    exact divisor_real_nonneg_of_analyticOnNhd (completedLFunction_analyticOnNhd χ hχ (Metric.closedBall ((2 : ℂ) + Complex.I * (t : ℂ)) ρ))
  have hGm0 : ∀ u : ℂ, 0 ≤ Gm u := by
    intro u
    dsimp [Gm]
    exact divisor_real_nonneg_of_analyticOnNhd (completedLFunction_analyticOnNhd χ hχ (Metric.closedBall ((2 : ℂ) + Complex.I * ((-t : ℝ) : ℂ)) ρ))
  -- finite support
  have hfinF : Function.HasFiniteSupport F := by
    dsimp [F, Λ]
    exact divisor_real_finiteSupport_ball χ hχ (0 : ℂ) (b + 1)
  have hfinGp : Function.HasFiniteSupport Gp := by
    dsimp [Gp, Λ]
    exact divisor_real_finiteSupport_ball χ hχ ((2 : ℂ) + Complex.I * (t : ℂ)) ρ
  have hfinGm : Function.HasFiniteSupport Gm := by
    dsimp [Gm, Λ]
    exact divisor_real_finiteSupport_ball χ hχ ((2 : ℂ) + Complex.I * ((-t : ℝ) : ℂ)) ρ
  have hfinFw : Function.HasFiniteSupport (F * w) := by
    exact Function.HasFiniteSupport.mul_left hfinF w
  -- pointwise inequality: (F * w) u ≤ (Gp + Gm) u
  have hpoint : ∀ u : ℂ, (F * w) u ≤ (Gp + Gm) u := by
    intro u
    simp only [Pi.mul_apply, Pi.add_apply]
    by_cases hwin : a ≤ |u.im| ∧ |u.im| ≤ b
    · -- w u = 1
      have hw1 : w u = 1 := by dsimp [w]; rw [if_pos hwin]
      rw [hw1]
      simp
      by_cases hFz : F u = 0
      · rw [hFz]
        linarith only [hGp0 u, hGm0 u, hGp0, hGm0]
      · have hFne_int : (((MeromorphicOn.divisor Λ (Metric.closedBall (0 : ℂ) (b + 1))) u : ℤ)) ≠ 0 := by
          intro h
          apply hFz
          dsimp [F]
          exact_mod_cast h
        have huB0 : u ∈ Metric.closedBall (0 : ℂ) (b + 1) := by
          by_contra hnot
          have hz : (MeromorphicOn.divisor Λ (Metric.closedBall (0 : ℂ) (b + 1))) u = 0 :=
            (MeromorphicOn.divisor Λ (Metric.closedBall (0 : ℂ) (b + 1))).apply_eq_zero_of_notMem hnot
          exact hFne_int hz
        have hΛ0 : Λ u = 0 := by
          by_contra hnf
          have hd : (MeromorphicOn.divisor Λ (Metric.closedBall (0 : ℂ) (b + 1))) u = 0 :=
            divisor_zero_of_analytic_ne_zero (completedLFunction_analyticOnNhd χ hχ (Metric.closedBall (0 : ℂ) (b + 1))) huB0 hnf
          exact hFne_int hd
        have hst := hstrip u hΛ0
        rcases window_split ha hwin with ⟨haim, hbim⟩ | ⟨hlo2, hhi2⟩
        · have huBp : u ∈ Metric.closedBall ((2 : ℂ) + Complex.I * (t : ℂ)) ρ :=
            zero_mem_upper_disk hst.1 hst.2 haim hbim (by rfl) (by rfl)
          have heq : F u = Gp u := by
            dsimp [F, Gp]
            have heqZ : MeromorphicOn.divisor Λ (Metric.closedBall (0 : ℂ) (b + 1)) u =
                MeromorphicOn.divisor Λ (Metric.closedBall ((2 : ℂ) + Complex.I * (t : ℂ)) ρ) u :=
              Commons.NumberTheory.Linnik.divisor_eq_closedBall_subset (f := Λ) (a := (0 : ℂ))
                (b := ((2 : ℂ) + Complex.I * (t : ℂ))) (ra := b + 1) (rb := ρ)
                (hf := completedLFunction_analyticOnNhd χ hχ (Metric.closedBall (0 : ℂ) (b + 1) ∪
                  Metric.closedBall ((2 : ℂ) + Complex.I * (t : ℂ)) ρ)) huB0 huBp
            exact congrArg (fun n : ℤ => (n : ℝ)) heqZ
          rw [heq]
          exact le_add_of_nonneg_right (hGm0 u)
        · have huBm : u ∈ Metric.closedBall ((2 : ℂ) + Complex.I * ((-t : ℝ) : ℂ)) ρ :=
            zero_mem_lower_disk hst.1 hst.2 hlo2 hhi2 (by rfl) (by rfl)
          have heq : F u = Gm u := by
            dsimp [F, Gm]
            have heqZ : MeromorphicOn.divisor Λ (Metric.closedBall (0 : ℂ) (b + 1)) u =
                MeromorphicOn.divisor Λ (Metric.closedBall ((2 : ℂ) + Complex.I * ((-t : ℝ) : ℂ)) ρ) u :=
              Commons.NumberTheory.Linnik.divisor_eq_closedBall_subset (f := Λ) (a := (0 : ℂ))
                (b := ((2 : ℂ) + Complex.I * ((-t : ℝ) : ℂ))) (ra := b + 1) (rb := ρ)
                (hf := completedLFunction_analyticOnNhd χ hχ (Metric.closedBall (0 : ℂ) (b + 1) ∪
                  Metric.closedBall ((2 : ℂ) + Complex.I * ((-t : ℝ) : ℂ)) ρ)) huB0 huBm
            exact congrArg (fun n : ℤ => (n : ℝ)) heqZ
          rw [heq]
          exact le_add_of_nonneg_left (hGp0 u)
    · -- w u = 0
      have hw0 : w u = 0 := by dsimp [w]; rw [if_neg hwin]
      rw [hw0]
      simp
      linarith only [hGp0 u, hGm0 u, hGp0, hGm0]
  have hsum_le : (∑ᶠ u : ℂ, (F * w) u) ≤ (∑ᶠ u : ℂ, Gp u) + (∑ᶠ u : ℂ, Gm u) := by
    have h1 : (∑ᶠ u : ℂ, (F * w) u) ≤ (∑ᶠ u : ℂ, (Gp u + Gm u)) := by
      simpa only [Pi.add_apply] using
        (finsum_le_finsum' hfinFw (Function.HasFiniteSupport.add hfinGp hfinGm) hpoint)
    rwa [finsum_add_distrib hfinGp hfinGm] at h1
  -- geometry and log-facts for the final estimate
  have hρ2 : 2 ≤ ρ := by dsimp [ρ]; linarith only [hab]
  have hρ0 : 0 ≤ ρ := by linarith only [hρ2]
  have hb1 : 1 ≤ b := le_trans ha hab
  have hL0 : 0 ≤ L := by
    dsimp [L]
    have h1 : 0 ≤ Real.log (b + 3) := by
      refine Real.log_nonneg ?_
      linarith only [ha, hab]
    have h2 : 0 ≤ Real.log (N : ℝ) := by
      exact Real.log_nonneg (by exact_mod_cast (Nat.succ_le_of_lt (Nat.pos_of_ne_zero (NeZero.ne N))))
    linarith only [h1, h2]
  have hρle : ρ ≤ b - a + 2 := by dsimp [ρ]; linarith only [hab]
  have hc0n0 : 0 ≤ c0n := by dsimp [c0n]; exact le_max_right c0 0
  have hc0n_le : c0 ≤ c0n := by dsimp [c0n]; exact le_max_left c0 0
  have hC4 : 4 * c0n ≤ C := by dsimp [C]; exact le_max_left (4 * c0n) 1
  -- the two local zero-count bounds
  let LP : ℝ := Real.log (2 + |t| + ρ) + Real.log (N : ℝ) + 2
  have hLP0 : 0 ≤ LP := by
    dsimp [LP]
    have h1 : 0 ≤ Real.log (2 + |t| + ρ) := by
      refine Real.log_nonneg ?_
      have : 0 ≤ |t| := abs_nonneg t
      linarith only [hρ2, this]
    have h2 : 0 ≤ Real.log (N : ℝ) := by
      exact Real.log_nonneg (by exact_mod_cast (Nat.succ_le_of_lt (Nat.pos_of_ne_zero (NeZero.ne N))))
    linarith only [h1, h2]
  have hbndP : (∑ᶠ u : ℂ, Gp u) ≤ c0 * ρ * LP := by
    have h := hc0 ρ hρ2 t
    simpa [Gp, LP, Λ] using h
  have hbndM : (∑ᶠ u : ℂ, Gm u) ≤ c0 * ρ * LP := by
    have h := hc0 ρ hρ2 (-t)
    simpa [Gm, LP, Λ, abs_neg] using h
  have hbndP' : (∑ᶠ u : ℂ, Gp u) ≤ c0n * ρ * LP := by
    calc
      (∑ᶠ u : ℂ, Gp u) ≤ c0 * ρ * LP := hbndP
      _ = c0 * (ρ * LP) := by ring
      _ ≤ c0n * (ρ * LP) := mul_le_mul_of_nonneg_right hc0n_le (mul_nonneg hρ0 hLP0)
      _ = c0n * ρ * LP := by ring
  have hbndM' : (∑ᶠ u : ℂ, Gm u) ≤ c0n * ρ * LP := by
    calc
      (∑ᶠ u : ℂ, Gm u) ≤ c0 * ρ * LP := hbndM
      _ = c0 * (ρ * LP) := by ring
      _ ≤ c0n * (ρ * LP) := mul_le_mul_of_nonneg_right hc0n_le (mul_nonneg hρ0 hLP0)
      _ = c0n * ρ * LP := by ring
  have hLP_le : LP ≤ 2 * L := by
    dsimp [LP, L]
    have ht_abs : |t| ≤ b := by
      have ht0 : 0 ≤ t := by
        dsimp [t]
        have ha0 : 0 ≤ a := by linarith only [ha]
        positivity
      rw [abs_of_nonneg ht0]
      dsimp [t]
      linarith only [hab]
    have harg_le : 2 + |t| + ρ ≤ 2 * (b + 3) := by
      have hρ_le' : ρ ≤ b + 3 := by dsimp [ρ]; linarith only [hab, ha]
      linarith only [ht_abs, hρ_le', ha, hρle]
    have harg_pos : 0 < 2 + |t| + ρ := by positivity
    have hlog1 : Real.log (2 + |t| + ρ) ≤ Real.log (2 * (b + 3)) :=
      Real.log_le_log harg_pos harg_le
    have hlog2 : Real.log (2 * (b + 3)) = Real.log 2 + Real.log (b + 3) := by
      rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by linarith only [ha, hab] : (b + 3 : ℝ) ≠ 0)]
    have hlog2le : Real.log 2 ≤ Real.log (b + 3) := by
      exact Real.log_le_log (by norm_num) (by linarith only [ha, hab] : (2 : ℝ) ≤ b + 3)
    have hsum : Real.log (2 + |t| + ρ) ≤ 2 * Real.log (b + 3) := by
      calc
        Real.log (2 + |t| + ρ) ≤ Real.log (2 * (b + 3)) := hlog1
        _ = Real.log 2 + Real.log (b + 3) := hlog2
        _ ≤ Real.log (b + 3) + Real.log (b + 3) := by linarith only [hlog2le]
        _ = 2 * Real.log (b + 3) := by ring
    have hN0 : 0 ≤ Real.log (N : ℝ) := by
      exact Real.log_nonneg (by exact_mod_cast (Nat.succ_le_of_lt (Nat.pos_of_ne_zero (NeZero.ne N))))
    linarith only [hsum, hN0, hlog1, hlog2, hlog2le]
  have hpos_c0n_rho : 0 ≤ c0n * ρ := mul_nonneg hc0n0 hρ0
  have hstep1 : (∑ᶠ u : ℂ, (F * w) u) ≤ 2 * (c0n * ρ * LP) := by
    calc
      (∑ᶠ u : ℂ, (F * w) u) ≤ (∑ᶠ u : ℂ, Gp u) + (∑ᶠ u : ℂ, Gm u) := hsum_le
      _ ≤ c0n * ρ * LP + c0n * ρ * LP := add_le_add hbndP' hbndM'
      _ = 2 * (c0n * ρ * LP) := by ring
  have hstep2 : 2 * (c0n * ρ * LP) ≤ 2 * (c0n * ρ * (2 * L)) := by
    have hm : c0n * ρ * LP ≤ c0n * ρ * (2 * L) := mul_le_mul_of_nonneg_left hLP_le hpos_c0n_rho
    exact mul_le_mul_of_nonneg_left hm (by norm_num : (0 : ℝ) ≤ 2)
  have hstep3 : 2 * (c0n * ρ * (2 * L)) = 4 * c0n * ρ * L := by ring
  have h4c0n0 : 0 ≤ 4 * c0n := by positivity
  have hba20 : 0 ≤ b - a + 2 := by linarith only [hab]
  have hbL0 : 0 ≤ (b - a + 2) * L := mul_nonneg hba20 hL0
  have hstep4 : 4 * c0n * ρ * L ≤ 4 * c0n * (b - a + 2) * L := by
    calc
      4 * c0n * ρ * L = (4 * c0n * L) * ρ := by ring
      _ ≤ (4 * c0n * L) * (b - a + 2) := mul_le_mul_of_nonneg_left hρle (mul_nonneg h4c0n0 hL0)
      _ = 4 * c0n * (b - a + 2) * L := by ring
  have hstep5 : 4 * c0n * (b - a + 2) * L ≤ C * (b - a + 2) * L := by
    calc
      4 * c0n * (b - a + 2) * L = (4 * c0n) * ((b - a + 2) * L) := by ring
      _ ≤ C * ((b - a + 2) * L) := mul_le_mul_of_nonneg_right hC4 hbL0
      _ = C * (b - a + 2) * L := by ring
  have hmain : (∑ᶠ u : ℂ, (F * w) u) ≤ C * (b - a + 2) * L := by
    calc
      (∑ᶠ u : ℂ, (F * w) u) ≤ 2 * (c0n * ρ * LP) := hstep1
      _ ≤ 2 * (c0n * ρ * (2 * L)) := hstep2
      _ = 4 * c0n * ρ * L := hstep3
      _ ≤ 4 * c0n * (b - a + 2) * L := hstep4
      _ ≤ C * (b - a + 2) * L := hstep5
  simpa [F, w, Λ, L] using hmain

end Commons.NumberTheory.DirichletCharacter
