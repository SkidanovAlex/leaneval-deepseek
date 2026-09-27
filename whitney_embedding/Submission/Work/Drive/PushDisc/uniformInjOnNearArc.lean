import Mathlib
import Submission.Work.Drive.Slab.compactInjOnTube
import Submission.Work.Isotopy.exists_localInverse_param

/-!
# A uniform neighbourhood of injectivity along a compact arc

Let `Ψ : ℝ → E → E` (with `E = EuclideanSpace ℝ (Fin m)`) be smooth jointly in its two variables
and let `γ : ℝ → E` be smooth.  Suppose that

* for every parameter `λ ∈ [0,1]` the map `Ψ λ` is injective on the arc `γ '' [0,1]`
  (`hsep`), and that
* for every `λ ∈ [0,1]` and every point `γ t` of the arc the derivative of `Ψ λ` at `γ t` is
  bijective (`hinv`).

Then there is a **single** open set `Ω ⊇ γ '' [0,1]` on which `Ψ λ` is injective for *every*
`λ ∈ [0,1]`.  The proof is a compactness argument in the parameter-augmented space `[0,1] × E`:

* the arc `K = γ '' [0,1]` is compact, hence contained in a closed ball of some radius `R`;
* if no uniform `δ` worked, there would be a sequence `(λₙ, xₙ, yₙ)` with `xₙ ≠ yₙ`, `xₙ`, `yₙ`
  within distance `1/(n+1)` of `K` and `Ψ λₙ xₙ = Ψ λₙ yₙ`; by compactness (Bolzano-Weierstrass
  in the closed ball of radius `R+1`) a subsequence converges to `(λ, x, y)`, and since the
  distances to `K` tend to `0` we get `x, y ∈ K`; continuity gives `Ψ λ x = Ψ λ y`, so `hsep`
  forces `x = y = γ t`;
* at that point the *parametric* inverse function theorem
  (`Work.Isotopy.exists_localInverse_param`) supplies a neighbourhood `O ∋ λ` and a ball `U ∋ x`
  such that `Ψ s` is injective on `U` for every `s ∈ O`; the bad pair with `n` large has both
  points in `U` and its parameter in `O`, contradicting `xₙ ≠ yₙ`.
-/

open scoped Topology
open Filter

namespace Work.Drive.PushDisc

/-- The derivative of the slice `y ↦ Ψ λ y` is the derivative of the uncurried map followed by
the embedding `v ↦ (0, v)` of the second factor.  (Chain rule for `Ψ λ = uncurry Ψ ∘ (λ, ·)`.) -/
private theorem fderiv_slice_apply {m : ℕ}
    (Ψ : ℝ → EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m))
    (hΨ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × EuclideanSpace ℝ (Fin m) => Ψ p.1 p.2))
    (lam : ℝ) (p : EuclideanSpace ℝ (Fin m)) (v : EuclideanSpace ℝ (Fin m)) :
    fderiv ℝ (fun y : EuclideanSpace ℝ (Fin m) => Ψ lam y) p v
      = fderiv ℝ (fun q : ℝ × EuclideanSpace ℝ (Fin m) => Ψ q.1 q.2) (lam, p) (0, v) := by
  have hne : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  have hF : HasFDerivAt (fun q : ℝ × EuclideanSpace ℝ (Fin m) => Ψ q.1 q.2)
      (fderiv ℝ (fun q : ℝ × EuclideanSpace ℝ (Fin m) => Ψ q.1 q.2) (lam, p)) (lam, p) :=
    ((hΨ.contDiffAt).differentiableAt hne).hasFDerivAt
  have hg : HasFDerivAt (fun y : EuclideanSpace ℝ (Fin m) => (lam, y))
      (ContinuousLinearMap.inr ℝ ℝ (EuclideanSpace ℝ (Fin m))) p := by
    have h0 := hasFDerivAt_const (𝕜 := ℝ) (c := lam) (x := p)
    have h1 : HasFDerivAt (id : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m))
        (1 : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m)) p := hasFDerivAt_id p
    have h2 := h0.prodMk h1
    have h3 : ((0 : EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ).prod
        (1 : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m)))
        = ContinuousLinearMap.inr ℝ ℝ (EuclideanSpace ℝ (Fin m)) := by
      ext y : 1
      rw [ContinuousLinearMap.prod_apply, ContinuousLinearMap.inr_apply]
      exact Prod.ext rfl (by simp)
    rw [h3] at h2
    simpa using h2
  have hcomp := hF.comp p hg
  have hfun : (fun y : EuclideanSpace ℝ (Fin m) => Ψ lam y)
      = ((fun q : ℝ × EuclideanSpace ℝ (Fin m) => Ψ q.1 q.2) ∘ Prod.mk lam) := rfl
  calc fderiv ℝ (fun y : EuclideanSpace ℝ (Fin m) => Ψ lam y) p v
      = (fderiv ℝ ((fun q : ℝ × EuclideanSpace ℝ (Fin m) => Ψ q.1 q.2) ∘ Prod.mk lam) p) v := by
        rw [hfun]
    _ = ((fderiv ℝ (fun q : ℝ × EuclideanSpace ℝ (Fin m) => Ψ q.1 q.2) (lam, p)).comp
          (ContinuousLinearMap.inr ℝ ℝ (EuclideanSpace ℝ (Fin m)))) v := by rw [hcomp.fderiv]
    _ = fderiv ℝ (fun q : ℝ × EuclideanSpace ℝ (Fin m) => Ψ q.1 q.2) (lam, p) (0, v) := by
        simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply]

/-- **Uniform local injectivity in the parameter**, obtained from the parametric inverse function
theorem: at every point `(λ, γ t)` of `[0,1] × arc` there are a neighbourhood `O` of `λ` and a
ball `U` around `γ t` such that `Ψ s` is injective on `U` for every `s ∈ O`. -/
private theorem exists_uniform_localInj {m : ℕ}
    (Ψ : ℝ → EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m))
    (hΨ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × EuclideanSpace ℝ (Fin m) => Ψ p.1 p.2))
    (γ : ℝ → EuclideanSpace ℝ (Fin m))
    (hinv : ∀ lam ∈ Set.Icc (0:ℝ) 1, ∀ t ∈ Set.Icc (0:ℝ) 1,
      Function.Bijective (fderiv ℝ (Ψ lam) (γ t))) :
    ∀ lam ∈ Set.Icc (0:ℝ) 1, ∀ p ∈ γ '' Set.Icc (0:ℝ) 1,
      ∃ O : Set ℝ, ∃ U : Set (EuclideanSpace ℝ (Fin m)),
        IsOpen O ∧ lam ∈ O ∧ IsOpen U ∧ p ∈ U ∧ ∀ s ∈ O, Set.InjOn (Ψ s) U := by
  intro lam hlam p hp
  obtain ⟨t, ht, rfl⟩ := hp
  have hinj0 : Function.Injective
      (fun v : EuclideanSpace ℝ (Fin m) =>
        fderiv ℝ (fun q : ℝ × EuclideanSpace ℝ (Fin m) => Ψ q.1 q.2) (lam, γ t) (0, v)) := by
    intro v w hvw
    have hv := fderiv_slice_apply Ψ hΨ lam (γ t) v
    have hw := fderiv_slice_apply Ψ hΨ lam (γ t) w
    have h2 : fderiv ℝ (fun y => Ψ lam y) (γ t) v = fderiv ℝ (fun y => Ψ lam y) (γ t) w := by
      rw [hv, hw]
      exact hvw
    exact (hinv lam hlam t ht).1 h2
  obtain ⟨O, U, W, h, hOo, hlamO, hUo, hpU, _hWo, _hGW, _hVmem, _hsm, _hGW', hleft⟩ :=
    Work.Isotopy.exists_localInverse_param
      (fun q : ℝ × EuclideanSpace ℝ (Fin m) => Ψ q.1 q.2) Set.univ isOpen_univ lam (γ t)
      (Set.mem_univ _) hΨ.contDiffOn Set.univ isOpen_univ (Set.mem_univ _) hinj0
  refine ⟨O, U, hOo, hlamO, hUo, hpU, fun s hs x hx y hy hxy => ?_⟩
  have h1 : h s (Ψ s x) = x := hleft s hs x hx
  have h2 : h s (Ψ s y) = y := hleft s hs y hy
  rw [hxy] at h1
  exact h1.symm.trans h2

theorem uniformInjOnNearArc {m : ℕ}
    (Ψ : ℝ → EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m))
    (hΨ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × EuclideanSpace ℝ (Fin m) => Ψ p.1 p.2))
    (γ : ℝ → EuclideanSpace ℝ (Fin m))
    (hγ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) γ)
    (hsep : ∀ lam ∈ Set.Icc (0:ℝ) 1, Set.InjOn (fun t : ℝ => Ψ lam (γ t)) (Set.Icc (0:ℝ) 1))
    (hinv : ∀ lam ∈ Set.Icc (0:ℝ) 1, ∀ t ∈ Set.Icc (0:ℝ) 1,
      Function.Bijective (fderiv ℝ (Ψ lam) (γ t))) :
    ∃ Ω : Set (EuclideanSpace ℝ (Fin m)),
      IsOpen Ω ∧ (∀ t ∈ Set.Icc (0:ℝ) 1, γ t ∈ Ω) ∧
      (∀ lam ∈ Set.Icc (0:ℝ) 1, Set.InjOn (Ψ lam) Ω) := by
  classical
  -- the compact arc and a bound for it
  have hγc : Continuous γ := hγ.continuous
  have hKc : IsCompact (γ '' Set.Icc (0:ℝ) 1) := isCompact_Icc.image hγc
  have hKne : (γ '' Set.Icc (0:ℝ) 1).Nonempty := ⟨γ 0, 0, by norm_num, rfl⟩
  have hKcl : IsClosed (γ '' Set.Icc (0:ℝ) 1) := hKc.isClosed
  obtain ⟨R, hR⟩ := hKc.isBounded.exists_norm_le
  have hδle : ∀ n : ℕ, ((n:ℝ)+1)⁻¹ ≤ 1 := by
    intro n
    have h1 : (1:ℝ) ≤ (n:ℝ) + 1 := by
      have : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
      linarith
    exact inv_le_one_of_one_le₀ h1
  have hcontΨ : Continuous (Function.uncurry Ψ) := hΨ.continuous
  have hloc := exists_uniform_localInj Ψ hΨ γ hinv
  -- the uniform injectivity tube
  have hmain : ∃ δ > 0, ∀ lam ∈ Set.Icc (0:ℝ) 1, ∀ x y : EuclideanSpace ℝ (Fin m),
      Metric.infDist x (γ '' Set.Icc (0:ℝ) 1) < δ →
      Metric.infDist y (γ '' Set.Icc (0:ℝ) 1) < δ → Ψ lam x = Ψ lam y → x = y := by
    by_contra hcon
    have hbad : ∀ δ > 0, ∃ lam ∈ Set.Icc (0:ℝ) 1, ∃ x y : EuclideanSpace ℝ (Fin m),
        Metric.infDist x (γ '' Set.Icc (0:ℝ) 1) < δ ∧
        Metric.infDist y (γ '' Set.Icc (0:ℝ) 1) < δ ∧ Ψ lam x = Ψ lam y ∧ x ≠ y := by
      intro δ hδ
      by_contra hc
      apply hcon
      refine ⟨δ, hδ, ?_⟩
      intro lam hlam x y hx hy hxy
      by_contra hne
      exact hc ⟨lam, hlam, x, y, hx, hy, hxy, hne⟩
    -- a sequence of bad pairs approaching the arc
    have hseq : ∀ n : ℕ, ∃ t : ℝ × EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m),
        t.1 ∈ Set.Icc (0:ℝ) 1 ∧ Metric.infDist t.2.1 (γ '' Set.Icc (0:ℝ) 1) < ((n:ℝ)+1)⁻¹ ∧
        Metric.infDist t.2.2 (γ '' Set.Icc (0:ℝ) 1) < ((n:ℝ)+1)⁻¹ ∧
        Ψ t.1 t.2.1 = Ψ t.1 t.2.2 ∧ t.2.1 ≠ t.2.2 := by
      intro n
      obtain ⟨lam, hlam, x, y, hx, hy, hxy, hne⟩ := hbad (((n:ℝ)+1)⁻¹) (by positivity)
      exact ⟨(lam, x, y), hlam, hx, hy, hxy, hne⟩
    choose p hp using hseq
    -- the pairs stay in a compact set
    let A : Set (ℝ × EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) :=
      Set.Icc (0:ℝ) 1 ×ˢ Metric.closedBall 0 (R+1) ×ˢ Metric.closedBall 0 (R+1)
    have hAc : IsCompact A :=
      isCompact_Icc.prod ((isCompact_closedBall 0 (R+1)).prod (isCompact_closedBall 0 (R+1)))
    have hmemA : ∀ n, p n ∈ A := by
      intro n
      obtain ⟨z, hzK, hxz⟩ := (Metric.infDist_lt_iff hKne).mp (hp n).2.1
      obtain ⟨z', hz'K, hyz'⟩ := (Metric.infDist_lt_iff hKne).mp (hp n).2.2.1
      have hbd1 : dist (p n).2.1 0 ≤ R + 1 := by
        have h5 : dist (p n).2.1 0 ≤ dist (p n).2.1 z + dist z 0 := dist_triangle _ _ _
        have h7 : dist z 0 ≤ R := by
          rw [dist_eq_norm, sub_zero]; exact hR z hzK
        linarith [h5, hxz, h7, hδle n]
      have hbd2 : dist (p n).2.2 0 ≤ R + 1 := by
        have h5 : dist (p n).2.2 0 ≤ dist (p n).2.2 z' + dist z' 0 := dist_triangle _ _ _
        have h7 : dist z' 0 ≤ R := by
          rw [dist_eq_norm, sub_zero]; exact hR z' hz'K
        linarith [h5, hyz', h7, hδle n]
      exact ⟨(hp n).1, Metric.mem_closedBall.mpr hbd1, Metric.mem_closedBall.mpr hbd2⟩
    -- a convergent subsequence
    obtain ⟨a, haA, φ, hφmono, hφtend⟩ := hAc.tendsto_subseq (fun n => hmemA n)
    have ht1 : Tendsto (fun n => (p (φ n)).1) atTop (𝓝 a.1) :=
      ((Prod.tendsto_iff _ _).mp hφtend).1
    have ht2 : Tendsto (fun n => (p (φ n)).2) atTop (𝓝 a.2) :=
      ((Prod.tendsto_iff _ _).mp hφtend).2
    have htx : Tendsto (fun n => (p (φ n)).2.1) atTop (𝓝 a.2.1) :=
      ((Prod.tendsto_iff _ _).mp ht2).1
    have hty : Tendsto (fun n => (p (φ n)).2.2) atTop (𝓝 a.2.2) :=
      ((Prod.tendsto_iff _ _).mp ht2).2
    have hlam : a.1 ∈ Set.Icc (0:ℝ) 1 := haA.1
    have hφtop : Tendsto (fun n : ℕ => (φ n : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp hφmono.tendsto_atTop
    have hδtend : Tendsto (fun n : ℕ => ((φ n : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (hφtop.atTop_add tendsto_const_nhds)
    -- the limits lie on the arc
    have hxK : a.2.1 ∈ γ '' Set.Icc (0:ℝ) 1 := by
      have hcont : Tendsto (fun n => Metric.infDist (p (φ n)).2.1 (γ '' Set.Icc (0:ℝ) 1)) atTop
          (𝓝 (Metric.infDist a.2.1 (γ '' Set.Icc (0:ℝ) 1))) :=
        ((Metric.continuous_infDist_pt _).tendsto a.2.1).comp htx
      have hle : Metric.infDist a.2.1 (γ '' Set.Icc (0:ℝ) 1) ≤ 0 :=
        le_of_tendsto_of_tendsto' hcont hδtend (fun n => le_of_lt (hp (φ n)).2.1)
      have h0 : Metric.infDist a.2.1 (γ '' Set.Icc (0:ℝ) 1) = 0 :=
        le_antisymm hle Metric.infDist_nonneg
      exact hKcl.closure_eq ▸ (Metric.mem_closure_iff_infDist_zero hKne).mpr h0
    have hyK : a.2.2 ∈ γ '' Set.Icc (0:ℝ) 1 := by
      have hcont : Tendsto (fun n => Metric.infDist (p (φ n)).2.2 (γ '' Set.Icc (0:ℝ) 1)) atTop
          (𝓝 (Metric.infDist a.2.2 (γ '' Set.Icc (0:ℝ) 1))) :=
        ((Metric.continuous_infDist_pt _).tendsto a.2.2).comp hty
      have hle : Metric.infDist a.2.2 (γ '' Set.Icc (0:ℝ) 1) ≤ 0 :=
        le_of_tendsto_of_tendsto' hcont hδtend (fun n => le_of_lt (hp (φ n)).2.2.1)
      have h0 : Metric.infDist a.2.2 (γ '' Set.Icc (0:ℝ) 1) = 0 :=
        le_antisymm hle Metric.infDist_nonneg
      exact hKcl.closure_eq ▸ (Metric.mem_closure_iff_infDist_zero hKne).mpr h0
    -- their images agree
    have hxyt : (Function.uncurry Ψ) (a.1, a.2.1) = (Function.uncurry Ψ) (a.1, a.2.2) := by
      have h1t : Tendsto (fun n => (Function.uncurry Ψ) ((p (φ n)).1, (p (φ n)).2.1)) atTop
          (𝓝 ((Function.uncurry Ψ) (a.1, a.2.1))) :=
        (hcontΨ.tendsto (a.1, a.2.1)).comp
          ((Prod.tendsto_iff (fun n => ((p (φ n)).1, (p (φ n)).2.1)) (a.1, a.2.1)).mpr
            ⟨ht1, htx⟩)
      have h2t : Tendsto (fun n => (Function.uncurry Ψ) ((p (φ n)).1, (p (φ n)).2.2)) atTop
          (𝓝 ((Function.uncurry Ψ) (a.1, a.2.2))) :=
        (hcontΨ.tendsto (a.1, a.2.2)).comp
          ((Prod.tendsto_iff (fun n => ((p (φ n)).1, (p (φ n)).2.2)) (a.1, a.2.2)).mpr
            ⟨ht1, hty⟩)
      have heq : (fun n => (Function.uncurry Ψ) ((p (φ n)).1, (p (φ n)).2.1))
          = (fun n => (Function.uncurry Ψ) ((p (φ n)).1, (p (φ n)).2.2)) :=
        funext fun n => (hp (φ n)).2.2.2.1
      rw [heq] at h1t
      exact tendsto_nhds_unique h1t h2t
    -- so by `hsep` the two limits coincide
    have hxy : a.2.1 = a.2.2 := by
      obtain ⟨t, ht, hxt⟩ := hxK
      obtain ⟨t', ht', hyt⟩ := hyK
      have hEq : Ψ a.1 (γ t) = Ψ a.1 (γ t') := by
        have h0 : (Function.uncurry Ψ) (a.1, a.2.1) = (Function.uncurry Ψ) (a.1, a.2.2) := hxyt
        rw [hxt, hyt]
        exact h0
      have htt : t = t' := hsep a.1 hlam ht ht' hEq
      rw [← hxt, ← hyt, htt]
    -- and the parametric inverse function theorem kills the bad pairs
    obtain ⟨O, U, hOo, hlamO, hUo, hxU, hinjU⟩ := hloc a.1 hlam a.2.1 hxK
    have hev1 : ∀ᶠ n in atTop, (p (φ n)).1 ∈ O := ht1.eventually (hOo.mem_nhds hlamO)
    have hev2 : ∀ᶠ n in atTop, (p (φ n)).2.1 ∈ U := htx.eventually (hUo.mem_nhds hxU)
    have hty' : Tendsto (fun n => (p (φ n)).2.2) atTop (𝓝 a.2.1) := by rw [hxy]; exact hty
    have hev3 : ∀ᶠ n in atTop, (p (φ n)).2.2 ∈ U := hty'.eventually (hUo.mem_nhds hxU)
    obtain ⟨n, hn1, hn2, hn3⟩ := (hev1.and (hev2.and hev3)).exists
    exact (hp (φ n)).2.2.2.2 (hinjU (p (φ n)).1 hn1 hn2 hn3 (hp (φ n)).2.2.2.1)
  -- the tube around the arc
  obtain ⟨δ, hδpos, hδ⟩ := hmain
  exact ⟨{x | Metric.infDist x (γ '' Set.Icc (0:ℝ) 1) < δ},
    isOpen_lt (Metric.continuous_infDist_pt _) continuous_const,
    fun t ht => by
      show Metric.infDist (γ t) (γ '' Set.Icc (0:ℝ) 1) < δ
      rw [Metric.infDist_zero_of_mem (Set.mem_image_of_mem γ ht)]
      exact hδpos,
    fun lam hlam x hx y hy hxy => hδ lam hlam x y hx hy hxy⟩

end Work.Drive.PushDisc
