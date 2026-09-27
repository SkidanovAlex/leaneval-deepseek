import Mathlib

open MeasureTheory intervalIntegral Function
open scoped Interval Convolution

namespace Work.Drive

/-- **Smoothness of parametric interval integrals** (universe-polymorphic version).

If `(x, w) ↦ g x w` is jointly `C^n`, then `x ↦ ∫ w in 0..1, g x w` is `C^n`.
Mathlib has the first-order version of this statement
(`intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le`) but no `ContDiff` version;
this is the missing chapter.  Unlike `Work.Drive.parametric_integral_contDiff`, the parameter
space `P` and the codomain `E` are allowed to live in *different* universes, which is needed for
the application below.

The proof rewrites the interval integral as a convolution: with `ψ` a smooth bump function
which is `1` on `[-1,1]` and supported in `(-2,2)` and `f = 1_{(0,1]}`, one has pointwise
`(f ⋆ (fun p y => ψ y • g p (-y)) p) 0 = ∫ w in 0..1, g p w`; then
`contDiffOn_convolution_right_with_param_comp` (which is universe polymorphic) gives the
smoothness. -/
theorem parametric_integral_contDiff_univ {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {n : ℕ∞} {g : P → ℝ → E}
    (hg : ContDiff ℝ ((n : ℕ∞) : WithTop ℕ∞) (Function.uncurry g)) :
    ContDiff ℝ ((n : ℕ∞) : WithTop ℕ∞) (fun x => ∫ w in (0 : ℝ)..1, g x w) := by
  let ψ : ContDiffBump (0 : ℝ) := ⟨1, 2, by norm_num, by norm_num⟩
  have hψ1 : ∀ y : ℝ, |y| ≤ 1 → ψ y = 1 := by
    intro y hy
    refine ContDiffBump.one_of_mem_closedBall (f := ψ) ?_
    have hrin : (ψ.rIn : ℝ) = 1 := rfl
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero, hrin]
    exact hy
  have hψ0 : ∀ y : ℝ, 2 ≤ |y| → ψ y = 0 := by
    intro y hy
    refine ContDiffBump.zero_of_le_dist (f := ψ) ?_
    have hrout : (ψ.rOut : ℝ) = 2 := rfl
    rw [Real.dist_eq, sub_zero, hrout]
    exact hy
  let f : ℝ → ℝ := Set.indicator (Set.Ioc (0 : ℝ) 1) (fun _ => (1 : ℝ))
  let g' : P → ℝ → E := fun p y => ψ y • g p (-y)
  let L : ℝ →L[ℝ] E →L[ℝ] E := (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] E →L[ℝ] E)
  have hf : LocallyIntegrable f volume :=
    LocallyIntegrable.indicator (locallyIntegrable_const (1 : ℝ)) measurableSet_Ioc
  have hg' : ContDiffOn ℝ ((n : ℕ∞) : WithTop ℕ∞) (Function.uncurry g')
      (Set.univ ×ˢ Set.univ) := by
    have hψcd : ContDiff ℝ ((n : ℕ∞) : WithTop ℕ∞) (fun q : P × ℝ => ψ q.2) :=
      ψ.contDiff.comp contDiff_snd
    have hgcd : ContDiff ℝ ((n : ℕ∞) : WithTop ℕ∞) (fun q : P × ℝ => g q.1 (-q.2)) :=
      hg.comp (contDiff_fst.prodMk (contDiff_snd.neg))
    exact (hψcd.smul hgcd).contDiffOn
  have hmain : ContDiffOn ℝ ((n : ℕ∞) : WithTop ℕ∞)
      (fun x : P => (f ⋆[L, volume] g' x) (0 : ℝ)) Set.univ := by
    refine contDiffOn_convolution_right_with_param_comp (𝕜 := ℝ) (μ := volume) (s := Set.univ)
      (v := fun _ : P => (0 : ℝ)) (f := f) (g := g') (k := Metric.closedBall (0 : ℝ) 2)
      L contDiffOn_const isOpen_univ (isCompact_closedBall 0 2) ?_ hf hg'
    intro p x _ hx
    have hx2 : (2 : ℝ) ≤ |x| := by
      rw [Metric.mem_closedBall, Real.dist_eq, sub_zero, not_le] at hx
      exact le_of_lt hx
    show ψ x • g p (-x) = 0
    rw [hψ0 x hx2, zero_smul]
  rw [contDiffOn_univ] at hmain
  have hpt : ∀ p : P, (f ⋆[L, volume] g' p) (0 : ℝ) = ∫ w in (0 : ℝ)..1, g p w := by
    intro p
    rw [convolution_def]
    have h1 : ∀ t : ℝ, L (f t) (g' p (0 - t))
        = Set.indicator (Set.Ioc (0 : ℝ) 1) (fun w => g p w) t := by
      intro t
      by_cases ht : t ∈ Set.Ioc (0 : ℝ) 1
      · have hft : f t = 1 := Set.indicator_of_mem ht (fun _ => (1 : ℝ))
        have hψt : ψ (0 - t) = 1 := by
          apply hψ1
          rw [zero_sub, abs_neg, abs_of_pos ht.1]
          exact ht.2
        have hgt : g' p (0 - t) = g p t := by
          show ψ (0 - t) • g p (-(0 - t)) = g p t
          rw [hψt, one_smul, neg_sub, sub_zero]
        have hind : Set.indicator (Set.Ioc (0 : ℝ) 1) (fun w => g p w) t = g p t :=
          Set.indicator_of_mem ht (fun w => g p w)
        rw [hft, hind]
        show (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] E →L[ℝ] E) 1 (g' p (0 - t)) = g p t
        rw [ContinuousLinearMap.lsmul_apply, one_smul, hgt]
      · have hft : f t = 0 := Set.indicator_of_notMem ht (fun _ => (1 : ℝ))
        have hind : Set.indicator (Set.Ioc (0 : ℝ) 1) (fun w => g p w) t = 0 :=
          Set.indicator_of_notMem ht (fun w => g p w)
        rw [hft, hind]
        show (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] E →L[ℝ] E) 0 (g' p (0 - t)) = 0
        rw [ContinuousLinearMap.lsmul_apply, zero_smul]
    have hcongr : (∫ t, L (f t) (g' p (0 - t)))
        = ∫ t, Set.indicator (Set.Ioc (0 : ℝ) 1) (fun w => g p w) t :=
      MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall h1)
    rw [hcongr, MeasureTheory.integral_indicator measurableSet_Ioc]
    exact (intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num)).symm
  rw [show (fun x : P => (f ⋆[L, volume] g' x) (0 : ℝ)) = (fun x => ∫ w in (0 : ℝ)..1, g x w)
      from funext hpt] at hmain
  exact hmain

/-- **Hadamard's lemma / division by the coordinate.**

A `C^∞` function `G : X × ℝ → E` which vanishes on the hyperplane `{t = 0}` is divisible by `t`:
there is a `C^∞` function `M : X × ℝ → E` with `G (x, t) = t • M (x, t)` everywhere.

The witness is Hadamard's integral formula
`M (x, t) = ∫ u in 0..1, (fderiv ℝ G (x, u * t)) (0, 1)`; smoothness of `M` is
`Work.Drive.parametric_integral_contDiff_univ` applied to the jointly smooth integrand
`(p, u) ↦ (fderiv ℝ G (p.1, u * p.2)) (0, 1)` (using `ContDiff.fderiv`), and the identity
`G (x, t) = t • M (x, t)` is the fundamental theorem of calculus applied to `s ↦ G (x, s * t)`
together with the hypothesis `G (x, 0) = 0`. -/
theorem exists_contDiff_smul_factor {X E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {G : X × ℝ → E}
    (hG : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G) (h0 : ∀ x, G (x, 0) = 0) :
    ∃ M : X × ℝ → E, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) M ∧ ∀ x t, G (x, t) = t • M (x, t) := by
  have hΦcd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : (X × ℝ) × ℝ => (fderiv ℝ G ((q.1.1, q.2 * q.1.2))) ((0 : X), (1 : ℝ))) := by
    have hfam : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (Function.uncurry (fun (_ : (X × ℝ) × ℝ) (y : X × ℝ) => G y)) := hG.comp contDiff_snd
    have hcurve : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun q : (X × ℝ) × ℝ => ((q.1.1, q.2 * q.1.2) : X × ℝ)) :=
      (contDiff_fst.comp contDiff_fst).prodMk (contDiff_snd.mul (contDiff_snd.comp contDiff_fst))
    have hd := ContDiff.fderiv (𝕜 := ℝ)
      (f := fun (_ : (X × ℝ) × ℝ) (y : X × ℝ) => G y)
      (g := fun q : (X × ℝ) × ℝ => ((q.1.1, q.2 * q.1.2) : X × ℝ))
      (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) (m := ((⊤ : ℕ∞) : WithTop ℕ∞)) hfam hcurve (by simp)
    have hconst : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun _ : (X × ℝ) × ℝ => ((0 : X), (1 : ℝ))) := contDiff_const
    exact hd.clm_apply hconst
  refine ⟨fun p => ∫ u in (0 : ℝ)..1, (fderiv ℝ G ((p.1, u * p.2))) ((0 : X), (1 : ℝ)), ?_, ?_⟩
  · have hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (Function.uncurry (fun p : X × ℝ => fun u : ℝ =>
          (fderiv ℝ G ((p.1, u * p.2))) ((0 : X), (1 : ℝ)))) := hΦcd
    exact parametric_integral_contDiff_univ (P := X × ℝ) (E := E) (n := (⊤ : ℕ∞)) hg
  · intro x t
    have hstep1 : t • (∫ u in (0 : ℝ)..1, (fderiv ℝ G ((x, u * t))) ((0 : X), (1 : ℝ)))
        = ∫ u in (0 : ℝ)..1, t • (fderiv ℝ G ((x, u * t))) ((0 : X), (1 : ℝ)) := by
      rw [intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num),
          intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
      exact (MeasureTheory.integral_smul t
        (fun u : ℝ => (fderiv ℝ G ((x, u * t))) ((0 : X), (1 : ℝ)))).symm
    rw [hstep1]
    have hpt : ∀ u : ℝ,
        t • (fderiv ℝ G ((x, u * t))) ((0 : X), (1 : ℝ))
          = deriv (fun s : ℝ => G (x, s * t)) u := by
      intro u
      have h1 : t • (fderiv ℝ G ((x, u * t))) ((0 : X), (1 : ℝ))
          = (fderiv ℝ G ((x, u * t))) ((0 : X), t) := by
        rw [← ContinuousLinearMap.map_smul]
        congr 1
        ext <;> simp
      have h2 : deriv (fun s : ℝ => G (x, s * t)) u
          = (fderiv ℝ G ((x, u * t))) ((0 : X), t) := by
        have hψ : HasDerivAt (fun s : ℝ => ((x : X), s * t)) ((0 : X), t) u := by
          simpa using (hasDerivAt_const u x).prodMk ((hasDerivAt_id u).mul_const t)
        have hGd : HasFDerivAt G (fderiv ℝ G ((x, u * t))) ((x, u * t)) :=
          ((hG.differentiable (by simp)).differentiableAt).hasFDerivAt
        exact (HasFDerivAt.comp_hasDerivAt u hGd hψ).deriv
      rw [h1, ← h2]
    have hInt : (∫ u in (0 : ℝ)..1, deriv (fun s : ℝ => G (x, s * t)) u) = G (x, t) - G (x, 0) := by
      have hcd : ContDiffOn ℝ (1 : WithTop ℕ∞) (fun s : ℝ => G (x, s * t))
          (Set.uIcc (0 : ℝ) 1) :=
        ((hG.comp (contDiff_const.prodMk (contDiff_id.mul contDiff_const))).of_le (by simp)).contDiffOn
      simpa using intervalIntegral.integral_deriv_of_contDiffOn_uIcc hcd
    have hcongr : (∫ u in (0 : ℝ)..1, t • (fderiv ℝ G ((x, u * t))) ((0 : X), (1 : ℝ)))
        = ∫ u in (0 : ℝ)..1, deriv (fun s : ℝ => G (x, s * t)) u :=
      intervalIntegral.integral_congr (fun u _ => hpt u)
    rw [hcongr, hInt, h0 x, sub_zero]

end Work.Drive
