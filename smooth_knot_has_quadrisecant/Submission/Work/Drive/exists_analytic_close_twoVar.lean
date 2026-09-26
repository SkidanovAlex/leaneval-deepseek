import Mathlib
import ChallengeDeps
import Submission.Work.Drive.exists_analytic_periodic_close

set_option maxHeartbeats 2000000

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant

open scoped Real

noncomputable section

/-! ### Small periodicity tools -/

private lemma periodPos : 0 < period := by
  rw [show period = 2 * Real.pi from rfl]; positivity

private lemma exists_int_sub_mul_mem_Ico {T x : ℝ} (hT : 0 < T) :
    ∃ n : ℤ, x - n * T ∈ Set.Ico 0 T := by
  refine ⟨⌊x / T⌋, ?_, ?_⟩
  · have h2 : Int.fract (x / T) = x / T - (⌊x / T⌋ : ℝ) := (Int.self_sub_floor (x / T)).symm
    have h1 : x - (⌊x / T⌋ : ℝ) * T = T * Int.fract (x / T) := by
      rw [h2]; field_simp
    rw [h1]; exact mul_nonneg hT.le (Int.fract_nonneg _)
  · have h2 : Int.fract (x / T) = x / T - (⌊x / T⌋ : ℝ) := (Int.self_sub_floor (x / T)).symm
    have h1 : x - (⌊x / T⌋ : ℝ) * T = T * Int.fract (x / T) := by
      rw [h2]; field_simp
    rw [h1]
    calc T * Int.fract (x / T) < T * 1 := mul_lt_mul_of_pos_left (Int.fract_lt_one _) hT
      _ = T := mul_one T

private lemma periodic_bound {W : ℝ → Space} (hWp : Function.Periodic W period) {c : ℝ}
    (h : ∀ t ∈ Set.Icc (0 : ℝ) period, ‖W t‖ < c) : ∀ t, ‖W t‖ < c := by
  intro t
  obtain ⟨n, hn⟩ := exists_int_sub_mul_mem_Ico (T := period) periodPos (x := t)
  have hdec : t - (n : ℝ) * period + (n : ℝ) * period = t := by ring
  have hper : W t = W (t - (n : ℝ) * period) := by
    calc W t = W (t - (n : ℝ) * period + (n : ℝ) * period) := congrArg W hdec.symm
      _ = W (t - (n : ℝ) * period) := by
          rw [show (n : ℝ) * period = n • period by rw [zsmul_eq_mul]]
          exact hWp.zsmul n _
  rw [hper]
  exact h _ ⟨hn.1, le_of_lt hn.2⟩

private lemma deriv_periodic {f : ℝ → Space} {c : ℝ} (hp : Function.Periodic f c)
    (hd : ∀ x, DifferentiableAt ℝ f x) : Function.Periodic (deriv f) c := by
  intro t
  have h1 : HasFDerivAt f (fderiv ℝ f (t + c)) (t + c) := (hd (t + c)).hasFDerivAt
  have h2 : HasFDerivAt (fun u : ℝ => u + c) (1 : ℝ →L[ℝ] ℝ) t :=
    (hasFDerivAt_id t).add_const c
  have h3 : HasDerivAt (fun u : ℝ => f (u + c)) (deriv f (t + c)) t := by
    have h4 := h1.comp t h2
    have h5 := h4.hasDerivAt
    simpa [ContinuousLinearMap.comp_apply, Function.comp_def] using h5
  have h6 : (fun u : ℝ => f (u + c)) = f := funext fun u => hp u
  rw [h6] at h3
  exact h3.deriv.symm

private lemma deriv_slice_eq {F : ℝ → ℝ → Space}
    (hF' : ContDiff ℝ 1 (fun p : ℝ × ℝ => F p.1 p.2)) (t s : ℝ) :
    deriv (fun u : ℝ => F u s) t
      = fderiv ℝ (fun p : ℝ × ℝ => F p.1 p.2) (t, s) (1, 0) := by
  have hd : HasFDerivAt (fun p : ℝ × ℝ => F p.1 p.2)
      (fderiv ℝ (fun p : ℝ × ℝ => F p.1 p.2) (t, s)) (t, s) :=
    ((hF'.differentiable one_ne_zero).differentiableAt).hasFDerivAt
  have h1 := hd.comp t (hasFDerivAt_prodMk_left (𝕜 := ℝ) t s)
  have h2 := h1.hasDerivAt
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply] at h2
  exact h2.deriv

theorem exists_analytic_close_twoVar {F : ℝ → ℝ → LeanEval.KnotTheory.Quadrisecant.Space}
    (hF : ContDiff ℝ 1 (fun p : ℝ × ℝ => F p.1 p.2))
    (hper : ∀ s t : ℝ, F (t + LeanEval.KnotTheory.Quadrisecant.period) s = F t s)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ G : ℝ → ℝ → LeanEval.KnotTheory.Quadrisecant.Space,
      ContDiff ℝ ⊤ (fun p : ℝ × ℝ => G p.1 p.2) ∧
        (∀ s t : ℝ, G (t + LeanEval.KnotTheory.Quadrisecant.period) s = G t s) ∧
          (∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ‖F t s - G t s‖ < ε) ∧
            (∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ,
              ‖deriv (fun u : ℝ => F u s) t - deriv (fun u : ℝ => G u s) t‖ < ε) := by
  have hT : 0 < period := periodPos
  set η : ℝ := ε / 3 with hη
  have hηpos : 0 < η := by rw [hη]; linarith
  have hηε : 2 * η < ε := by rw [hη]; linarith
  haveI : CompactSpace (Set.Icc (0 : ℝ) period) := isCompact_iff_compactSpace.mp isCompact_Icc
  haveI : CompactSpace (Set.Icc (0 : ℝ) 1) := isCompact_iff_compactSpace.mp isCompact_Icc
  -- the value family  s ↦ (t ↦ F t s)
  have hHv : Continuous (fun p : Set.Icc (0 : ℝ) 1 × Set.Icc (0 : ℝ) period => F p.2.1 p.1.1) := by
    have hpair : Continuous (fun p : Set.Icc (0 : ℝ) 1 × Set.Icc (0 : ℝ) period =>
        ((p.2.1, p.1.1) : ℝ × ℝ)) :=
      (continuous_subtype_val.comp continuous_snd).prodMk
        (continuous_subtype_val.comp continuous_fst)
    exact hF.continuous.comp hpair
  set Hv : C(Set.Icc (0 : ℝ) 1, C(Set.Icc (0 : ℝ) period, Space)) :=
    ContinuousMap.curry ⟨fun p : Set.Icc (0 : ℝ) 1 × Set.Icc (0 : ℝ) period => F p.2.1 p.1.1, hHv⟩
    with hHvdef
  -- the derivative family  s ↦ (t ↦ ∂₁ F (t,s))
  have hfderiv_cont : Continuous (fun p : (ℝ × ℝ) × (ℝ × ℝ) =>
      fderiv ℝ (fun q : ℝ × ℝ => F q.1 q.2) p.1 p.2) :=
    hF.continuous_fderiv_apply one_ne_zero
  have hHd : Continuous (fun p : Set.Icc (0 : ℝ) 1 × Set.Icc (0 : ℝ) period =>
      fderiv ℝ (fun q : ℝ × ℝ => F q.1 q.2) (p.2.1, p.1.1) (1, 0)) := by
    have hpair : Continuous (fun p : Set.Icc (0 : ℝ) 1 × Set.Icc (0 : ℝ) period =>
        ((p.2.1, p.1.1), ((1 : ℝ), (0 : ℝ))) : _ → (ℝ × ℝ) × (ℝ × ℝ)) :=
      ((continuous_subtype_val.comp continuous_snd).prodMk
        (continuous_subtype_val.comp continuous_fst)).prodMk continuous_const
    exact hfderiv_cont.comp hpair
  set Hd : C(Set.Icc (0 : ℝ) 1, C(Set.Icc (0 : ℝ) period, Space)) :=
    ContinuousMap.curry ⟨fun p : Set.Icc (0 : ℝ) 1 × Set.Icc (0 : ℝ) period =>
      fderiv ℝ (fun q : ℝ × ℝ => F q.1 q.2) (p.2.1, p.1.1) (1, 0), hHd⟩
    with hHddef
  -- Bernstein: choose a common degree
  have hNv : ∃ N : ℕ, ∀ n ≥ N, dist (bernsteinApproximation n Hv) Hv < η := by
    have hev : ∀ᶠ n in Filter.atTop, dist (bernsteinApproximation n Hv) Hv < η :=
      (bernsteinApproximation_uniform Hv).eventually (Metric.ball_mem_nhds Hv hηpos)
    rwa [Filter.eventually_atTop] at hev
  have hNd : ∃ N : ℕ, ∀ n ≥ N, dist (bernsteinApproximation n Hd) Hd < η := by
    have hev : ∀ᶠ n in Filter.atTop, dist (bernsteinApproximation n Hd) Hd < η :=
      (bernsteinApproximation_uniform Hd).eventually (Metric.ball_mem_nhds Hd hηpos)
    rwa [Filter.eventually_atTop] at hev
  obtain ⟨N₁, hN₁⟩ := hNv
  obtain ⟨N₂, hN₂⟩ := hNd
  set N : ℕ := max N₁ N₂ with hNdef
  have hBv : dist (bernsteinApproximation N Hv) Hv < η := hN₁ N (le_max_left N₁ N₂)
  have hBd : dist (bernsteinApproximation N Hd) Hd < η := hN₂ N (le_max_right N₁ N₂)
  -- evaluation lemmas
  have hHv_eval : ∀ (s : Set.Icc (0 : ℝ) 1) (t : Set.Icc (0 : ℝ) period),
      (Hv s) t = F t.1 s.1 := by
    intro s t
    change F t.1 s.1 = F t.1 s.1
    rfl
  have hHd_eval : ∀ (s : Set.Icc (0 : ℝ) 1) (t : Set.Icc (0 : ℝ) period),
      (Hd s) t = deriv (fun v : ℝ => F v s.1) t.1 := by
    intro s t
    change fderiv ℝ (fun q : ℝ × ℝ => F q.1 q.2) (t.1, s.1) (1, 0)
      = deriv (fun v : ℝ => F v s.1) t.1
    exact (deriv_slice_eq hF t.1 s.1).symm
  -- pointwise Bernstein bounds
  have hBv_pt : ∀ (s : Set.Icc (0 : ℝ) 1) (t : Set.Icc (0 : ℝ) period),
      ‖(bernsteinApproximation N Hv s) t - F t.1 s.1‖ < η := by
    intro s t
    have h0 : dist ((bernsteinApproximation N Hv) s) (Hv s) < η :=
      lt_of_le_of_lt (ContinuousMap.dist_apply_le_dist (f := bernsteinApproximation N Hv) (g := Hv) s) hBv
    have h1 : ‖(bernsteinApproximation N Hv) s - Hv s‖ < η := by
      rwa [dist_eq_norm] at h0
    have h2 : ∀ y : Set.Icc (0 : ℝ) period,
        ‖((bernsteinApproximation N Hv) s - Hv s) y‖ < η :=
      (ContinuousMap.norm_lt_iff ((bernsteinApproximation N Hv) s - Hv s) hηpos).mp h1
    have h3 := h2 t
    simp only [ContinuousMap.sub_apply] at h3
    rw [hHv_eval s t] at h3
    exact h3
  have hBd_pt : ∀ (s : Set.Icc (0 : ℝ) 1) (t : Set.Icc (0 : ℝ) period),
      ‖(bernsteinApproximation N Hd s) t - deriv (fun v : ℝ => F v s.1) t.1‖ < η := by
    intro s t
    have h0 : dist ((bernsteinApproximation N Hd) s) (Hd s) < η :=
      lt_of_le_of_lt (ContinuousMap.dist_apply_le_dist (f := bernsteinApproximation N Hd) (g := Hd) s) hBd
    have h1 : ‖(bernsteinApproximation N Hd) s - Hd s‖ < η := by
      rwa [dist_eq_norm] at h0
    have h2 : ∀ y : Set.Icc (0 : ℝ) period,
        ‖((bernsteinApproximation N Hd) s - Hd s) y‖ < η :=
      (ContinuousMap.norm_lt_iff ((bernsteinApproximation N Hd) s - Hd s) hηpos).mp h1
    have h3 := h2 t
    simp only [ContinuousMap.sub_apply] at h3
    rw [hHd_eval s t] at h3
    exact h3
  -- the Bernstein sums, in explicit form
  have hbsv : ∀ (s : Set.Icc (0 : ℝ) 1) (t : Set.Icc (0 : ℝ) period),
      (bernsteinApproximation N Hv s) t
        = ∑ k : Fin (N + 1), (bernstein N k s) • F t.1 (bernstein.z k : ℝ) := by
    intro s t
    rw [bernsteinApproximation.apply, ContinuousMap.sum_apply]
    exact Finset.sum_congr rfl fun k _ => by
      rw [ContinuousMap.smul_apply, hHv_eval (bernstein.z k) t]
  have hbsd : ∀ (s : Set.Icc (0 : ℝ) 1) (t : Set.Icc (0 : ℝ) period),
      (bernsteinApproximation N Hd s) t
        = ∑ k : Fin (N + 1), (bernstein N k s) •
            deriv (fun v : ℝ => F v (bernstein.z k : ℝ)) t.1 := by
    intro s t
    rw [bernsteinApproximation.apply, ContinuousMap.sum_apply]
    exact Finset.sum_congr rfl fun k _ => by
      rw [ContinuousMap.smul_apply, hHd_eval (bernstein.z k) t]
  -- the analytic approximants of the slices
  have hex : ∀ k : Fin (N + 1), ∃ g : ℝ → Space, ContDiff ℝ ⊤ g ∧ Function.Periodic g period ∧
      (∀ t : ℝ, ‖F t (bernstein.z k : ℝ) - g t‖ < η) ∧
      (∀ t : ℝ, ‖deriv (fun u : ℝ => F u (bernstein.z k : ℝ)) t - deriv g t‖ < η) := by
    intro k
    have hslice : ContDiff ℝ 1 (fun t : ℝ => F t (bernstein.z k : ℝ)) := by
      have h := hF.comp (contDiff_id.prodMk (contDiff_const (c := (bernstein.z k : ℝ))))
      simpa [Function.comp_def] using h
    have hperk : Function.Periodic (fun t : ℝ => F t (bernstein.z k : ℝ)) period :=
      fun t => hper _ t
    exact exists_analytic_periodic_close hslice hperk hηpos
  choose φ hφan hφper hφval hφder using hex
  -- Bernstein weights, as polynomials in `s`
  set w : ℝ → Fin (N + 1) → ℝ :=
    fun s k => (N.choose (k : ℕ) : ℝ) * s ^ (k : ℕ) * (1 - s) ^ (N - (k : ℕ)) with hwdef
  have hwbern : ∀ (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) (k : Fin (N + 1)),
      w s k = (bernstein N k ⟨s, hs⟩ : ℝ) := by
    intro s hs k
    simp only [hwdef, bernstein_apply]
  set G : ℝ → ℝ → Space := fun t s => ∑ k : Fin (N + 1), w s k • φ k t with hGdef
  have hG_eq : ∀ (s : Set.Icc (0 : ℝ) 1) (u : ℝ),
      G u s.1 = ∑ k : Fin (N + 1), (bernstein N k s) • φ k u := by
    intro s u
    simp only [hGdef]
    exact Finset.sum_congr rfl fun k _ => by rw [hwbern s.1 s.2 k]
  have hGper : ∀ s : ℝ, Function.Periodic (fun u : ℝ => G u s) period := by
    intro s u
    simp only [hGdef]
    exact Finset.sum_congr rfl fun k _ => by rw [hφper k u]
  refine ⟨G, ?_, ?_, ?_, ?_⟩
  · -- analyticity
    have hterm : ∀ k : Fin (N + 1),
        ContDiff ℝ ⊤ (fun p : ℝ × ℝ => w p.2 k • φ k p.1) := by
      intro k
      have hw : ContDiff ℝ ⊤ (fun p : ℝ × ℝ => w p.2 k) := by
        simp only [hwdef]
        exact ContDiff.mul (ContDiff.mul contDiff_const (contDiff_snd.pow _))
          ((contDiff_const.sub contDiff_snd).pow _)
      exact hw.smul ((hφan k).comp contDiff_fst)
    have := ContDiff.sum (s := Finset.univ) fun k _ => hterm k
    simpa [hGdef] using this
  · -- periodicity in `t`
    intro s t
    exact hGper s t
  · -- value estimate
    intro s hs t
    refine periodic_bound (W := fun t => F t s - G t s) ?_ ?_ t
    · intro u
      simp only [hGdef]
      rw [hper s u]
      congr 1
      exact Finset.sum_congr rfl fun k _ => by rw [hφper k u]
    · intro u hu
      set sI : Set.Icc (0 : ℝ) 1 := ⟨s, hs⟩ with hsIdef
      set uK : Set.Icc (0 : ℝ) period := ⟨u, hu⟩ with huKdef
      have hb1 : ‖F u s - (bernsteinApproximation N Hv sI) uK‖ < η := by
        rw [norm_sub_rev]
        exact hBv_pt sI uK
      have hb2 : ‖(bernsteinApproximation N Hv sI) uK - G u s‖ ≤ η := by
        rw [hbsv sI uK, hG_eq sI u]
        calc ‖(∑ k : Fin (N + 1), (bernstein N k sI) • F u (bernstein.z k : ℝ))
              - ∑ k : Fin (N + 1), (bernstein N k sI) • φ k u‖
            = ‖∑ k : Fin (N + 1),
                (bernstein N k sI) • (F u (bernstein.z k : ℝ) - φ k u)‖ := by
              congr 1
              rw [← Finset.sum_sub_distrib]
              exact Finset.sum_congr rfl fun k _ => (smul_sub _ _ _).symm
          _ ≤ ∑ k : Fin (N + 1),
                ‖(bernstein N k sI) • (F u (bernstein.z k : ℝ) - φ k u)‖ :=
              norm_sum_le _ _
          _ = ∑ k : Fin (N + 1),
                (bernstein N k sI) * ‖F u (bernstein.z k : ℝ) - φ k u‖ := by
              exact Finset.sum_congr rfl fun k _ => by
                rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg bernstein_nonneg]
          _ ≤ ∑ k : Fin (N + 1), (bernstein N k sI) * η := by
              exact Finset.sum_le_sum fun k _ =>
                mul_le_mul_of_nonneg_left (le_of_lt (hφval k u)) bernstein_nonneg
          _ = η := by
              rw [← Finset.sum_mul, bernstein.probability, one_mul]
      calc ‖F u s - G u s‖
          = ‖(F u s - (bernsteinApproximation N Hv sI) uK)
              + ((bernsteinApproximation N Hv sI) uK - G u s)‖ := by
            congr 1; abel
        _ ≤ ‖F u s - (bernsteinApproximation N Hv sI) uK‖
              + ‖(bernsteinApproximation N Hv sI) uK - G u s‖ := norm_add_le _ _
        _ < η + η := add_lt_add_of_lt_of_le hb1 hb2
        _ = 2 * η := by ring
        _ < ε := hηε
  · -- derivative estimate
    intro s hs t
    set sI : Set.Icc (0 : ℝ) 1 := ⟨s, hs⟩ with hsIdef
    have hslice_per : Function.Periodic (fun u : ℝ => F u s) period := fun u => hper s u
    have hslice_diff : ∀ x : ℝ, DifferentiableAt ℝ (fun u : ℝ => F u s) x := by
      intro x
      have hslice : ContDiff ℝ 1 (fun u : ℝ => F u s) := by
        have h := hF.comp (contDiff_id.prodMk (contDiff_const (c := s)))
        simpa [Function.comp_def] using h
      exact (hslice.differentiable one_ne_zero).differentiableAt
    have hGdiff : ∀ x : ℝ, DifferentiableAt ℝ (fun u : ℝ => G u s) x := by
      intro x
      have hslice : ContDiff ℝ 1 (fun u : ℝ => G u s) := by
        have hterm : ∀ k : Fin (N + 1),
            ContDiff ℝ 1 (fun u : ℝ => w s k • φ k u) := fun k =>
          ContDiff.const_smul (w s k) ((hφan k).of_le le_top)
        have := ContDiff.sum (s := Finset.univ) fun k _ => hterm k
        simpa [hGdef] using this
      exact (hslice.differentiable one_ne_zero).differentiableAt
    refine periodic_bound (W := fun t =>
      deriv (fun u : ℝ => F u s) t - deriv (fun u : ℝ => G u s) t) ?_ ?_ t
    · intro u
      beta_reduce
      rw [deriv_periodic hslice_per hslice_diff u, deriv_periodic (hGper s) hGdiff u]
    · intro u hu
      set uK : Set.Icc (0 : ℝ) period := ⟨u, hu⟩ with huKdef
      have hb1 : ‖(bernsteinApproximation N Hd sI) uK - deriv (fun v : ℝ => F v s) u‖ < η :=
        hBd_pt sI uK
      have hGd : deriv (fun v : ℝ => G v s) u
          = ∑ k : Fin (N + 1), (bernstein N k sI) • deriv (φ k) u := by
        have hfun : (fun v : ℝ => G v s)
            = ∑ k : Fin (N + 1), (fun v : ℝ => (bernstein N k sI) • φ k v) := by
          funext v
          simp only [hGdef, Finset.sum_apply]
          exact Finset.sum_congr rfl fun k _ => by rw [hwbern s hs k]
        have hdiff : ∀ k : Fin (N + 1),
            DifferentiableAt ℝ (fun v : ℝ => (bernstein N k sI) • φ k v) u := fun k =>
          ((ContDiff.const_smul (bernstein N k sI) (hφan k)).differentiable (by simp)).differentiableAt
        rw [hfun, deriv_sum (u := (Finset.univ : Finset (Fin (N + 1))))
          (A := fun k v => (bernstein N k sI) • φ k v) (fun k _ => hdiff k)]
        refine Finset.sum_congr rfl fun k _ => ?_
        have hd : DifferentiableAt ℝ (φ k) u :=
          ((hφan k).differentiable (by simp)).differentiableAt
        exact (hd.hasDerivAt.const_smul (bernstein N k sI)).deriv
      have hb2 : ‖(bernsteinApproximation N Hd sI) uK - deriv (fun v : ℝ => G v s) u‖ ≤ η := by
        rw [hbsd sI uK, hGd]
        calc ‖(∑ k : Fin (N + 1), (bernstein N k sI) •
                deriv (fun v : ℝ => F v (bernstein.z k : ℝ)) u)
              - ∑ k : Fin (N + 1), (bernstein N k sI) • deriv (φ k) u‖
            = ‖∑ k : Fin (N + 1), (bernstein N k sI) •
                (deriv (fun v : ℝ => F v (bernstein.z k : ℝ)) u - deriv (φ k) u)‖ := by
              congr 1
              rw [← Finset.sum_sub_distrib]
              exact Finset.sum_congr rfl fun k _ => (smul_sub _ _ _).symm
          _ ≤ ∑ k : Fin (N + 1), ‖(bernstein N k sI) •
                (deriv (fun v : ℝ => F v (bernstein.z k : ℝ)) u - deriv (φ k) u)‖ :=
              norm_sum_le _ _
          _ = ∑ k : Fin (N + 1), (bernstein N k sI) *
                ‖deriv (fun v : ℝ => F v (bernstein.z k : ℝ)) u - deriv (φ k) u‖ := by
              exact Finset.sum_congr rfl fun k _ => by
                rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg bernstein_nonneg]
          _ ≤ ∑ k : Fin (N + 1), (bernstein N k sI) * η := by
              exact Finset.sum_le_sum fun k _ =>
                mul_le_mul_of_nonneg_left (le_of_lt (hφder k u)) bernstein_nonneg
          _ = η := by
              rw [← Finset.sum_mul, bernstein.probability, one_mul]
      rw [show deriv (fun v : ℝ => F v s) u - deriv (fun v : ℝ => G v s) u
          = (deriv (fun v : ℝ => F v s) u - (bernsteinApproximation N Hd sI) uK)
            + ((bernsteinApproximation N Hd sI) uK - deriv (fun v : ℝ => G v s) u) from by
          abel]
      calc ‖(deriv (fun v : ℝ => F v s) u - (bernsteinApproximation N Hd sI) uK)
            + ((bernsteinApproximation N Hd sI) uK - deriv (fun v : ℝ => G v s) u)‖
          ≤ ‖deriv (fun v : ℝ => F v s) u - (bernsteinApproximation N Hd sI) uK‖
            + ‖(bernsteinApproximation N Hd sI) uK - deriv (fun v : ℝ => G v s) u‖ :=
              norm_add_le _ _
        _ = ‖(bernsteinApproximation N Hd sI) uK - deriv (fun v : ℝ => F v s) u‖
            + ‖(bernsteinApproximation N Hd sI) uK - deriv (fun v : ℝ => G v s) u‖ := by
              rw [norm_sub_rev]
        _ < η + η := add_lt_add_of_lt_of_le hb1 hb2
        _ = 2 * η := by ring
        _ < ε := hηε

end

end Work.Drive
