import Mathlib
import Submission.Work.Drive.OrderBase
import Submission.Work.Drive.isOpen_Zc
import Submission.Work.Drive.Interfaces
import Submission.Work.Drive.deriv_curve_periodic
import Submission.Work.Drive.exists_secant_dir_contDiff

namespace Work.Drive

/-! # Guidance (parent agent `orderSplit_chains`) — exists_continuous_chordDir

The paper's configuration map `μ` on unordered pairs of a smooth Jordan curve is continuous, with the
tangent direction at the diagonal.  In the Lean development the naive formula `dirC (γ x - γ y)` is
*discontinuous* at the diagonal (`dirC 0 = 0`), so the honest object is an explicit extension `D` of it
whose value at `(x,x)` is the doubled *tangent* direction.  This statement constructs that extension and
records its continuity and its two defining properties.

Proof plan (implemented below).

* Off the diagonal, `D (x,y) = dirC (γ x - γ y)`, and continuity is continuity of `dirC` composed with
  the chord map on the open set where the chord is non-zero
  (`Submission.Configuration.continuousOn_dirPair`).

* At a diagonal point `(x,x)` we use the local model of the chord direction supplied by
  `Work.Drive.exists_secant_dir_contDiff`: for `F = curve γ = fun s => γ (Circle.exp s)` and `t₀` with
  `Circle.exp t₀ = x` there are `ε > 0` and a map `W`, smooth on the square
  `(t₀-ε, t₀+ε) × (t₀-ε, t₀+ε)`, with `W (t,t) ≠ 0`, `dirC (W (t,t)) = dirC (deriv F t)` and
  `dirC (F s - F t) = dirC (W (s,t))` for `s ≠ t`.  Pulling `W` back through a local inverse `e` of
  `Circle.exp` at `t₀` gives a neighbourhood of `(x,x)` on which *both* branches of `D` agree with the
  continuous function `p ↦ dirC (W (e p.1, e p.2))`, whose value at `(x,x)` is
  `dirC (W (t₀,t₀)) = dirC (deriv F t₀)`.

* The diagonal value is well defined because `deriv F` is `2π`-periodic
  (`Work.Drive.deriv_curve_periodic`) and `Circle.exp_eq_exp`. -/

open Manifold Topology Filter
open scoped Manifold ContDiff Topology Classical
open Submission.Collision (dirC)
open Submission.Configuration (dirPair pairVec)

/-- The doubled tangent direction of `γ` at a point `x` of the circle, computed from an arbitrary
(classically chosen) lift of `x` under `Circle.exp`.  By `tangentDirC_exp` the value does not depend on
the lift. -/
noncomputable def tangentDirC (γ : Circle → ℝ × ℝ) (x : Circle) : UnitAddCircle :=
  dirC (deriv (curve γ) (Classical.choose (Circle.exp_surjective x)))

/-- **The doubled tangent direction depends only on the point of the circle, not on the lift.**  If
`Circle.exp t = Circle.exp t'` then the tangent vectors at `t` and at `t'` have the same doubled
direction.  Indeed `t = t' + m * 2π` for some `m : ℤ`, and `deriv (curve γ)` is `2π`-periodic. -/
lemma tangentDirC_eq_of_exp_eq (γ : Circle → ℝ × ℝ)
    (hγ : IsSmoothEmbedding (𝓡 1) (𝓘(ℝ, ℝ × ℝ)) ∞ γ) {t t' : ℝ}
    (h : Circle.exp t = Circle.exp t') :
    dirC (deriv (curve γ) t) = dirC (deriv (curve γ) t') := by
  obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp h
  have hper : Function.Periodic (deriv (curve γ)) (2 * Real.pi) := deriv_curve_periodic γ hγ
  rw [hm, ← zsmul_eq_mul]
  exact congrArg dirC (hper.zsmul m t')

/-- `tangentDirC` evaluated at `Circle.exp t` is the doubled direction of the tangent vector at `t`. -/
lemma tangentDirC_exp (γ : Circle → ℝ × ℝ)
    (hγ : IsSmoothEmbedding (𝓡 1) (𝓘(ℝ, ℝ × ℝ)) ∞ γ) (t : ℝ) :
    tangentDirC γ (Circle.exp t) = dirC (deriv (curve γ) t) :=
  tangentDirC_eq_of_exp_eq γ hγ (Classical.choose_spec (Circle.exp_surjective (Circle.exp t)))

/-- The value of `tangentDirC` at `x`, read through any lift `t` of `x`. -/
lemma tangentDirC_of_exp_eq (γ : Circle → ℝ × ℝ)
    (hγ : IsSmoothEmbedding (𝓡 1) (𝓘(ℝ, ℝ × ℝ)) ∞ γ) {x : Circle} {t : ℝ}
    (h : Circle.exp t = x) : tangentDirC γ x = dirC (deriv (curve γ) t) := by
  rw [← h, tangentDirC_exp γ hγ t]

/-- The doubled chord direction, extended to the diagonal by the doubled tangent direction. -/
noncomputable def chordDirExt (γ : Circle → ℝ × ℝ) : Circle × Circle → UnitAddCircle :=
  fun p => if _h : p.1 = p.2 then tangentDirC γ p.1 else dirC (γ p.1 - γ p.2)

/-- **Continuity of the extension off the diagonal**, where it is `dirC ∘ pairVec`, continuous as long
as the chord is non-zero. -/
lemma continuousAt_chordDirExt_offDiag {γ : Circle → ℝ × ℝ} (hγc : Continuous γ)
    (hinj : Function.Injective γ) {x y : Circle} (hxy : x ≠ y) :
    ContinuousAt (chordDirExt γ) (x, y) := by
  have hne : pairVec γ (x, y) ≠ 0 := by
    simp only [pairVec, sub_ne_zero]
    exact fun h => hxy (hinj h)
  have hcont : ContinuousAt (dirPair γ) (x, y) :=
    (Submission.Configuration.continuousOn_dirPair hγc).continuousAt
      ((isOpen_ne.preimage (Submission.Configuration.continuous_pairVec hγc)).mem_nhds hne)
  have hset : {p : Circle × Circle | p.1 ≠ p.2} ∈ 𝓝 (x, y) :=
    (isClosed_eq continuous_fst continuous_snd).isOpen_compl.mem_nhds (by simpa using hxy)
  refine hcont.congr ?_
  filter_upwards [hset] with p hp
  change dirPair γ p = (if h : p.1 = p.2 then tangentDirC γ p.1 else dirC (γ p.1 - γ p.2))
  rw [dif_neg hp]
  rfl

/-- **Continuity of the extension at the diagonal.**  Near `(x,x)` the extension agrees with the
pullback of the local model `W` of `exists_secant_dir_contDiff` through a local inverse of
`Circle.exp`. -/
lemma continuousAt_chordDirExt_diag (γ : Circle → ℝ × ℝ)
    (hγ : IsSmoothEmbedding (𝓡 1) (𝓘(ℝ, ℝ × ℝ)) ∞ γ) (x : Circle) :
    ContinuousAt (chordDirExt γ) (x, x) := by
  obtain ⟨t₀, ht₀⟩ := Circle.exp_surjective x
  have hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (curve γ) :=
    contMDiff_iff_contDiff.mp (hγ.contMDiff.comp (contMDiff_circleExp (m := ∞)))
  obtain ⟨ε, hε, W, hWcd, hWne, hWdir, hWsec⟩ :=
    exists_secant_dir_contDiff (F := curve γ) hF (curve_deriv_ne_zero γ hγ) t₀
  let I : Set ℝ := Set.Ioo (t₀ - ε) (t₀ + ε)
  have ht₀I : t₀ ∈ I := ⟨by linarith, by linarith⟩
  -- a local inverse of `Circle.exp` at `t₀`
  let e : OpenPartialHomeomorph Circle ℝ :=
    IsLocalHomeomorph.localInverseAt isLocalHomeomorph_circleExp t₀
  have hxsrc : x ∈ e.source := by
    have h := IsLocalHomeomorph.apply_self_mem_localInverseAt_source
      (f := (Circle.exp : ℝ → Circle)) isLocalHomeomorph_circleExp (x := t₀)
    rwa [ht₀] at h
  have hex : e x = t₀ := by
    have h := IsLocalHomeomorph.localInverseAt_apply_self
      (f := (Circle.exp : ℝ → Circle)) isLocalHomeomorph_circleExp (x := t₀)
    rwa [ht₀] at h
  have hleft : ∀ p ∈ e.source, Circle.exp (e p) = p := fun p hp =>
    IsLocalHomeomorph.apply_localInverseAt_of_mem (f := (Circle.exp : ℝ → Circle))
      isLocalHomeomorph_circleExp (x := t₀) hp
  -- the two lifted coordinates
  have htend1 : Tendsto (fun p : Circle × Circle => e p.1) (𝓝 (x, x)) (𝓝 t₀) := by
    have h1 : Tendsto (fun p : Circle × Circle => p.1) (𝓝 (x, x)) (𝓝[e.source] x) :=
      tendsto_nhdsWithin_iff.mpr
        ⟨continuous_fst.tendsto (x, x),
          (continuous_fst.tendsto (x, x)).eventually (e.open_source.mem_nhds hxsrc)⟩
    have h2 : Tendsto (fun a : Circle => e a) (𝓝[e.source] x) (𝓝 (e x)) :=
      e.continuousOn.continuousWithinAt hxsrc
    have h3 := h2.comp h1
    rwa [hex] at h3
  have htend2 : Tendsto (fun p : Circle × Circle => e p.2) (𝓝 (x, x)) (𝓝 t₀) := by
    have h1 : Tendsto (fun p : Circle × Circle => p.2) (𝓝 (x, x)) (𝓝[e.source] x) :=
      tendsto_nhdsWithin_iff.mpr
        ⟨continuous_snd.tendsto (x, x),
          (continuous_snd.tendsto (x, x)).eventually (e.open_source.mem_nhds hxsrc)⟩
    have h2 : Tendsto (fun a : Circle => e a) (𝓝[e.source] x) (𝓝 (e x)) :=
      e.continuousOn.continuousWithinAt hxsrc
    have h3 := h2.comp h1
    rwa [hex] at h3
  have htendpair : Tendsto (fun p : Circle × Circle => (e p.1, e p.2)) (𝓝 (x, x)) (𝓝 (t₀, t₀)) :=
    htend1.prodMk_nhds htend2
  -- the neighbourhood of `(x,x)` on which the local model applies
  have hev : ∀ᶠ p : Circle × Circle in 𝓝 (x, x),
      (p.1 ∈ e.source ∧ p.2 ∈ e.source) ∧ (e p.1 ∈ I ∧ e p.2 ∈ I) := by
    have h1 : ∀ᶠ p : Circle × Circle in 𝓝 (x, x), p.1 ∈ e.source :=
      (continuous_fst.tendsto (x, x)).eventually (e.open_source.mem_nhds hxsrc)
    have h2 : ∀ᶠ p : Circle × Circle in 𝓝 (x, x), p.2 ∈ e.source :=
      (continuous_snd.tendsto (x, x)).eventually (e.open_source.mem_nhds hxsrc)
    have h3 : ∀ᶠ p : Circle × Circle in 𝓝 (x, x), e p.1 ∈ I :=
      htend1.eventually (isOpen_Ioo.mem_nhds ht₀I)
    have h4 : ∀ᶠ p : Circle × Circle in 𝓝 (x, x), e p.2 ∈ I :=
      htend2.eventually (isOpen_Ioo.mem_nhds ht₀I)
    filter_upwards [h1, h2, h3, h4] with p h1p h2p h3p h4p
    exact ⟨⟨h1p, h2p⟩, h3p, h4p⟩
  -- on that neighbourhood the extension agrees with the local model
  have heq : (fun p : Circle × Circle => dirC (W (e p.1, e p.2))) =ᶠ[𝓝 (x, x)]
      (chordDirExt γ) := by
    filter_upwards [hev] with p ⟨⟨h1p, h2p⟩, h3p, h4p⟩
    by_cases hdiag : p.1 = p.2
    · change dirC (W (e p.1, e p.2)) =
        (if h : p.1 = p.2 then tangentDirC γ p.1 else dirC (γ p.1 - γ p.2))
      rw [dif_pos hdiag]
      have htan : tangentDirC γ p.1 = dirC (deriv (curve γ) (e p.1)) :=
        tangentDirC_of_exp_eq γ hγ (hleft p.1 h1p)
      rw [htan, ← hWdir (e p.1) h3p]
      have hpair : (e p.1, e p.1) = (e p.1, e p.2) := by rw [hdiag]
      rw [← hpair]
    · change dirC (W (e p.1, e p.2)) =
        (if h : p.1 = p.2 then tangentDirC γ p.1 else dirC (γ p.1 - γ p.2))
      rw [dif_neg hdiag]
      have hne : e p.1 ≠ e p.2 := by
        intro h
        exact hdiag (by rw [← hleft p.1 h1p, ← hleft p.2 h2p, h])
      rw [← hWsec (e p.1) (e p.2) h3p h4p hne]
      simp only [curve]
      rw [hleft p.1 h1p, hleft p.2 h2p]
  -- the local model tends to the tangent direction at `(x,x)`
  have htendbox : Tendsto (fun p : Circle × Circle => (e p.1, e p.2)) (𝓝 (x, x))
      (𝓝[I ×ˢ I] (t₀, t₀)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨htendpair, ?_⟩
    filter_upwards [htend1.eventually (isOpen_Ioo.mem_nhds ht₀I),
      htend2.eventually (isOpen_Ioo.mem_nhds ht₀I)] with p h3p h4p
    exact ⟨h3p, h4p⟩
  have hWlim : Tendsto (fun p : Circle × Circle => W (e p.1, e p.2)) (𝓝 (x, x))
      (𝓝 (W (t₀, t₀))) := by
    have hmem : (t₀, t₀) ∈ I ×ˢ I := ⟨ht₀I, ht₀I⟩
    have hcontW : ContinuousWithinAt W (I ×ˢ I) (t₀, t₀) :=
      hWcd.continuousOn.continuousWithinAt hmem
    have h := Filter.Tendsto.comp hcontW htendbox
    simpa only [Function.comp_def] using h
  have hWne₀ : W (t₀, t₀) ≠ 0 := hWne t₀ ht₀I
  have hdircont : ContinuousAt dirC (W (t₀, t₀)) :=
    Submission.Configuration.continuousOn_dirC.continuousAt (isOpen_ne.mem_nhds hWne₀)
  have hGlim : Tendsto (fun p : Circle × Circle => dirC (W (e p.1, e p.2))) (𝓝 (x, x))
      (𝓝 (dirC (W (t₀, t₀)))) :=
    hdircont.tendsto.comp hWlim
  have hWval : dirC (W (t₀, t₀)) = dirC (deriv (curve γ) t₀) := hWdir t₀ ht₀I
  have hval : chordDirExt γ (x, x) = dirC (deriv (curve γ) t₀) := by
    change (if h : x = x then tangentDirC γ x else dirC (γ x - γ x)) = dirC (deriv (curve γ) t₀)
    rw [dif_pos rfl, tangentDirC_of_exp_eq γ hγ ht₀]
  have hmain : Tendsto (chordDirExt γ) (𝓝 (x, x)) (𝓝 (chordDirExt γ (x, x))) := by
    rw [hval]
    simpa [hWval] using hGlim.congr' heq
  exact hmain

open Manifold in
open scoped Manifold ContDiff in
/-- The doubled chord direction extends continuously to the diagonal, where its value is the doubled
tangent direction. -/
theorem exists_continuous_chordDir (γ : Circle → ℝ × ℝ)
    (hγ : IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, ℝ × ℝ) ∞ γ) :
    ∃ D : Circle × Circle → UnitAddCircle, Continuous D ∧
      (∀ x y : Circle, x ≠ y → D (x, y) = Submission.Collision.dirC (γ x - γ y)) ∧
      (∀ (x : Circle) (t : ℝ), Circle.exp t = x →
        D (x, x) = Submission.Collision.dirC (deriv (fun s => γ (Circle.exp s)) t)) := by
  refine ⟨chordDirExt γ, ?_, ?_, ?_⟩
  · rw [continuous_iff_continuousAt]
    rintro ⟨x, y⟩
    by_cases hxy : x = y
    · subst hxy
      exact continuousAt_chordDirExt_diag γ hγ x
    · exact continuousAt_chordDirExt_offDiag hγ.isImmersion.contMDiff.continuous
        hγ.isEmbedding.injective hxy
  · intro x y hxy
    change (if h : x = y then tangentDirC γ x else dirC (γ x - γ y)) = dirC (γ x - γ y)
    rw [dif_neg hxy]
  · intro x t ht
    change (if h : x = x then tangentDirC γ x else dirC (γ x - γ x)) =
      dirC (deriv (curve γ) t)
    rw [dif_pos rfl, tangentDirC_of_exp_eq γ hγ ht]

end Work.Drive
