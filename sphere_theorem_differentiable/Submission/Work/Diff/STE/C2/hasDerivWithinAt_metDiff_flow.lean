/-
# Layer C2 (DeTurck pull-back): the first variation of a *changing* metric along a flow

## The target

`Work.Diff.STE.C2.hasDerivWithinAt_metDiff_flow` computes the time derivative of the difference

`λ s = (A s).inner (φ s x) (dφ_s u) (dφ_s v) - (A t).inner (φ s x) (dφ_s u) (dφ_s v)`

at `s = t`, and states that it is `dA t (φ t x) (dφ_t u) (dφ_t v)`.

## Why this is the right statement for the DeTurck step

The naive first-variation identity for `s ↦ (A s).inner (φ s x) (dφ_s u) (dφ_s v)` is

`dA t (φ t x) (dφ_t u) (dφ_t v) + ⟨∇_{dφ_t u} Y, dφ_t v⟩_{A t} + ⟨dφ_t u, ∇_{dφ_t v} Y⟩_{A t}`,

and its "raw" proof needs a hypothesis (`hvar` of `hasDerivWithinAt_pullMetBilin`) that is *false* on
this workspace's `ChartedSpace` (a smooth section need not have continuous raw values, see
`Submission/Work/Diff/STE/C2/hasDerivWithinAt_field_comp_flow.lean`).  In the Ricci–DeTurck equation
`∂_t ĝ = -2 Ric(ĝ) + L_W ĝ` the two Christoffel/`L_W` terms are precisely cancelled by the second
factor above, so the *difference* is exactly what the DeTurck computation needs — and it is
gauge-free: it only involves the metric family `A`, the flow `φ` and the claimed derivative `dA`.

## The proof (no chart, no uniformity argument)

Introduce the two-variable function

`Θ (s, σ) = (A s).inner (φ σ x) (dφ_σ u) (dφ_σ v) - (A t).inner (φ σ x) (dφ_σ u) (dφ_σ v)`.

Its key properties are

* `Θ` is `C^∞` within `J ×ˢ J` at `(t,t)`: the metric index `s` and the point index `σ` are
  *independent*, and both factors are jointly smooth — this is the delegated analytic input
  `Work.Diff.STE.C2.contMDiffWithinAt_metPair_twoVar` (for the `A s` factor) together with the same
  statement for the constant family `σ ↦ A t` (which follows from `ContMDiffRiemannianMetric.contMDiff`);
* `Θ (t, σ) = 0` — trivially, as `A t - A t = 0`;
* the `s`-slice `s ↦ Θ (s, t)` is `(A s) - (A t)` evaluated on the *fixed* vectors `dφ_t u`, `dφ_t v`,
  so `hAderiv` gives its derivative `dA t (φ t x) (dφ_t u) (dφ_t v)`.

Since `λ s = Θ (s, s)` is the composite of `Θ` with the diagonal `s ↦ (s, s)`, the chain rule for
`HasFDerivWithinAt` at `(t,t)` identifies the derivative of `λ` with `L (1,1)` where `L` is the
Fréchet derivative of `Θ` at `(t,t)`.  Decomposing `(1,1) = (1,0) + (0,1)`, the first slice gives
`L (1,0) = dA t (φ t x) (dφ_t u) (dφ_t v)` and `Θ (t, ·) ≡ 0` gives `L (0,1) = 0`.  This is exactly
the "uniform" information that a difference-quotient argument would have had to extract by hand: it
comes for free from the Fréchet differentiability of `Θ`, so no hypothesis on the geometry of `J`
(not even that `J` is an interval) is needed beyond `ContMDiffOn`, and the degenerate cases are
handled by `hasDerivWithinAt_of_nhdsWithin_eq_bot`/`eq_of_hasDerivWithinAt`.
-/

import Mathlib
import Submission.Work.Diff.STE.C2.Kit
import Submission.Work.Diff.STE.C2.formFamJoint_pullMetBilin

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

open Set Filter
open scoped Topology Manifold ContDiff Bundle
open Bundle ContDiff

namespace Work.Diff.STE.C2

/-! ## Two degenerate cases of `HasDerivWithinAt` on an arbitrary set of times

`J` is *not* assumed open (it is `Set.Ico 0 τ` in the intended application), so the within-filter at
`t` may be degenerate. -/

/-- If the within-filter at `t₀` is degenerate, every `HasDerivWithinAt` statement holds. -/
private lemma hasDerivWithinAt_of_nhdsWithin_eq_bot_aux {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {f : ℝ → F} {D : F} {J : Set ℝ} {t₀ : ℝ}
    (h : 𝓝[J \ {t₀}] t₀ = ⊥) : HasDerivWithinAt f D J t₀ := by
  rw [hasDerivWithinAt_iff_tendsto_slope, h]
  exact Filter.map_bot.trans_le bot_le

/-- Two within-derivatives of the same function agree unless the within-filter is degenerate. -/
private lemma eq_of_hasDerivWithinAt_aux {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [T2Space F] {f : ℝ → F} {D₁ D₂ : F} {J : Set ℝ} {t₀ : ℝ}
    (h₁ : HasDerivWithinAt f D₁ J t₀) (h₂ : HasDerivWithinAt f D₂ J t₀) :
    𝓝[J \ {t₀}] t₀ = ⊥ ∨ D₁ = D₂ := by
  by_cases h : NeBot (𝓝[J \ {t₀}] t₀)
  · exact Or.inr (tendsto_nhds_unique (hasDerivWithinAt_iff_tendsto_slope.mp h₁)
      (hasDerivWithinAt_iff_tendsto_slope.mp h₂))
  · exact Or.inl (Filter.not_neBot.mp h)

/-! ## Joint smoothness of the two-variable pairing

The analytic input of the main theorem: the metric time `s` and the flow time `σ` are *independent*,
and `(s, σ) ↦ (A s).inner (φ σ x) (dφ_σ u) (dφ_σ v)` is `C^∞` within `J ×ˢ J` at `(t, t)`.

The proof separates the two variables: `(s, σ) ↦ (A s).inner (φ σ x)` is the metric-family section
`hA` composed with `(s, σ) ↦ (s, φ σ x)`, and `(s, σ) ↦ ⟨φ σ x, dφ_σ u⟩` is a smooth tangent-bundle
section — obtained by restricting the tangent section of the family `φ`
(`Work.Diff.STE.C2.contMDiffWithinAt_tangentSection_mfderiv`, which does not need any hypothesis on
the time set `J`) along `(s, σ) ↦ (σ, x)` and expanding `u` in the coordinate frame at `x`, then
pairing with `ContMDiffWithinAt.clm_bundle_apply₂`.  The bilinearity of the pairing turns the frame
expansion of `u` and `v` into a finite sum of the frame-vector pairings, each of which is smooth. -/

/-- **Joint smoothness of the metric pairing along the flow.**  For a family `A` of smooth metrics
which is jointly smooth on `J` and a family `φ` of diffeomorphisms which is jointly smooth on
`J ×ˢ univ`, the function `(s, σ) ↦ (A s).inner (φ σ x) (dφ_σ u) (dφ_σ v)` is `C^∞` within
`J ×ˢ J` at `(t, t)`. -/
theorem contMDiffWithinAt_metPair_twoVar_aux
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M]
    (A : ℝ → Submission.Diff.SMet I M) (J : Set ℝ) (hA : Submission.Diff.JointSmooth A J)
    (φ : ℝ → Diffeomorph I I M M (⊤ : ℕ∞))
    (hφ : ContMDiffOn ((modelWithCornersSelf ℝ ℝ).prod I) I (⊤ : ℕ∞)
      (fun p : ℝ × M ↦ φ p.1 p.2) (J ×ˢ Set.univ))
    {t : ℝ} (ht : t ∈ J) (x : M) (u v : TangentSpace I x) :
    ContMDiffWithinAt ((modelWithCornersSelf ℝ ℝ).prod (modelWithCornersSelf ℝ ℝ))
      (modelWithCornersSelf ℝ ℝ) (⊤ : ℕ∞)
      (fun p : ℝ × ℝ ↦ (A p.1).inner (φ p.2 x) (mfderiv I I (φ p.2 : M → M) x u)
        (mfderiv I I (φ p.2 : M → M) x v))
      (J ×ˢ J) (t, t) := by
  classical
  have hmap2 : Set.MapsTo (fun q : ℝ × ℝ ↦ (q.2, x)) (J ×ˢ J) (J ×ˢ Set.univ) :=
    fun q hq => ⟨hq.2, Set.mem_univ x⟩
  have hmap1 : Set.MapsTo (fun q : ℝ × ℝ ↦ (q.1, φ q.2 x)) (J ×ˢ J) (J ×ˢ Set.univ) :=
    fun q hq => ⟨hq.1, Set.mem_univ _⟩
  -- the flow map, as a function of the second variable only
  have hφx : ContMDiffWithinAt ((modelWithCornersSelf ℝ ℝ).prod (modelWithCornersSelf ℝ ℝ)) I
      (⊤ : ℕ∞) (fun q : ℝ × ℝ ↦ φ q.2 x) (J ×ˢ J) (t, t) := by
    have hF : ContMDiffWithinAt ((modelWithCornersSelf ℝ ℝ).prod (modelWithCornersSelf ℝ ℝ))
        ((modelWithCornersSelf ℝ ℝ).prod I) (⊤ : ℕ∞)
        (fun q : ℝ × ℝ ↦ (q.2, x)) (J ×ˢ J) (t, t) :=
      (contMDiffWithinAt_snd (s := J ×ˢ J) (p := (t, t))).prodMk
        (contMDiffWithinAt_const (s := J ×ˢ J) (x := (t, t)) (c := x))
    exact (hφ (t, x) ⟨ht, Set.mem_univ x⟩).comp (t, t) hF hmap2
  -- the metric-family section, pulled back along `(s,σ) ↦ (s, φ σ x)`
  have hψ : ContMDiffWithinAt ((modelWithCornersSelf ℝ ℝ).prod (modelWithCornersSelf ℝ ℝ))
      (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) (⊤ : ℕ∞)
      (fun q : ℝ × ℝ ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun y : M ↦ TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
        (φ q.2 x) ((A q.1).inner (φ q.2 x))) (J ×ˢ J) (t, t) := by
    have hG : ContMDiffWithinAt ((modelWithCornersSelf ℝ ℝ).prod (modelWithCornersSelf ℝ ℝ))
        ((modelWithCornersSelf ℝ ℝ).prod I) (⊤ : ℕ∞)
        (fun q : ℝ × ℝ ↦ (q.1, φ q.2 x)) (J ×ˢ J) (t, t) :=
      (contMDiffWithinAt_fst (s := J ×ˢ J) (p := (t, t))).prodMk hφx
    exact (hA (t, φ t x) ⟨ht, Set.mem_univ _⟩).comp (t, t) hG hmap1
  -- the tangent sections of the family, over `q ↦ φ q.2 x`, for the coordinate frame at `x`
  have hsec : ∀ k : Fin (Module.finrank ℝ E),
      ContMDiffWithinAt ((modelWithCornersSelf ℝ ℝ).prod (modelWithCornersSelf ℝ ℝ))
        I.tangent (⊤ : ℕ∞)
        (fun q : ℝ × ℝ ↦ (⟨φ q.2 x,
          mfderiv I I (φ q.2 : M → M) x
            (Submission.Geodesic.frameVector (I := I) x x (Work.Diff.EXT.bB (E := E) k))⟩
          : TangentBundle I M)) (J ×ˢ J) (t, t) := by
    intro k
    have hbase := Work.Diff.STE.C2.contMDiffWithinAt_tangentSection_mfderiv (I := I) (φ := φ)
      (p₀ := (t, x)) ⟨ht, Set.mem_univ x⟩ (hφ (t, x) ⟨ht, Set.mem_univ x⟩) rfl k
    have hF : ContMDiffWithinAt ((modelWithCornersSelf ℝ ℝ).prod (modelWithCornersSelf ℝ ℝ))
        ((modelWithCornersSelf ℝ ℝ).prod I) (⊤ : ℕ∞)
        (fun q : ℝ × ℝ ↦ (q.2, x)) (J ×ˢ J) (t, t) :=
      (contMDiffWithinAt_snd (s := J ×ˢ J) (p := (t, t))).prodMk
        (contMDiffWithinAt_const (s := J ×ˢ J) (x := (t, t)) (c := x))
    exact hbase.comp (t, t) hF hmap2
  -- the pairing of the metric family with two frame-vector sections
  have key : ∀ i j : Fin (Module.finrank ℝ E),
      ContMDiffWithinAt ((modelWithCornersSelf ℝ ℝ).prod (modelWithCornersSelf ℝ ℝ))
        (modelWithCornersSelf ℝ ℝ) (⊤ : ℕ∞)
        (fun q : ℝ × ℝ ↦ (A q.1).inner (φ q.2 x)
          (mfderiv I I (φ q.2 : M → M) x
            (Submission.Geodesic.frameVector (I := I) x x (Work.Diff.EXT.bB (E := E) i)))
          (mfderiv I I (φ q.2 : M → M) x
            (Submission.Geodesic.frameVector (I := I) x x (Work.Diff.EXT.bB (E := E) j))))
        (J ×ˢ J) (t, t) := by
    intro i j
    have hmain := ContMDiffWithinAt.clm_bundle_apply₂ (𝕜 := ℝ) (B := M)
      (F₁ := E) (F₂ := E) (F₃ := ℝ)
      (E₁ := fun y : M ↦ TangentSpace I y) (E₂ := fun y : M ↦ TangentSpace I y)
      (E₃ := Bundle.Trivial M ℝ) (b := fun q : ℝ × ℝ ↦ φ q.2 x)
      (v := fun q : ℝ × ℝ ↦ mfderiv I I (φ q.2 : M → M) x
        (Submission.Geodesic.frameVector (I := I) x x (Work.Diff.EXT.bB (E := E) i)))
      (w := fun q : ℝ × ℝ ↦ mfderiv I I (φ q.2 : M → M) x
        (Submission.Geodesic.frameVector (I := I) x x (Work.Diff.EXT.bB (E := E) j)))
      (ψ := fun q : ℝ × ℝ ↦ (A q.1).inner (φ q.2 x))
      (s := J ×ˢ J) (x := (t, t)) hψ (hsec i) (hsec j)
    simp only [contMDiffWithinAt_totalSpace] at hmain
    exact hmain.2
  -- the coordinates of `u` and `v` in the coordinate frame at `x`
  have hbasex : x ∈ (trivializationAt E (TangentSpace I) x).baseSet :=
    mem_baseSet_trivializationAt E (TangentSpace I) x
  set a : E := (trivializationAt E (TangentSpace I) x).continuousLinearMapAt ℝ x u with ha
  set b : E := (trivializationAt E (TangentSpace I) x).continuousLinearMapAt ℝ x v with hb
  have hua : u = ∑ i, (Work.Diff.EXT.bB (E := E)).repr a i •
      Submission.Geodesic.frameVector (I := I) x x (Work.Diff.EXT.bB (E := E) i) := by
    have h1 : u = Submission.Geodesic.frameVector (I := I) x x a :=
      (Bundle.Trivialization.symmL_continuousLinearMapAt
        (e := trivializationAt E (TangentSpace I) x) hbasex u).symm
    conv_lhs => rw [h1]
    conv_lhs => rw [← (Work.Diff.EXT.bB (E := E)).sum_repr a]
    simp only [Submission.Geodesic.frameVector, map_sum, map_smul]
  have hvb : v = ∑ j, (Work.Diff.EXT.bB (E := E)).repr b j •
      Submission.Geodesic.frameVector (I := I) x x (Work.Diff.EXT.bB (E := E) j) := by
    have h1 : v = Submission.Geodesic.frameVector (I := I) x x b :=
      (Bundle.Trivialization.symmL_continuousLinearMapAt
        (e := trivializationAt E (TangentSpace I) x) hbasex v).symm
    conv_lhs => rw [h1]
    conv_lhs => rw [← (Work.Diff.EXT.bB (E := E)).sum_repr b]
    simp only [Submission.Geodesic.frameVector, map_sum, map_smul]
  -- the frame expansion of the pairing is smooth
  have hfin : ContMDiffWithinAt ((modelWithCornersSelf ℝ ℝ).prod (modelWithCornersSelf ℝ ℝ))
      (modelWithCornersSelf ℝ ℝ) (⊤ : ℕ∞)
      (fun q : ℝ × ℝ ↦ ∑ j, ∑ i,
        ((Work.Diff.EXT.bB (E := E)).repr a i * (Work.Diff.EXT.bB (E := E)).repr b j) *
        ((A q.1).inner (φ q.2 x)
          (mfderiv I I (φ q.2 : M → M) x
            (Submission.Geodesic.frameVector (I := I) x x (Work.Diff.EXT.bB (E := E) i)))
          (mfderiv I I (φ q.2 : M → M) x
            (Submission.Geodesic.frameVector (I := I) x x (Work.Diff.EXT.bB (E := E) j)))))
      (J ×ˢ J) (t, t) := by
    refine ContMDiffWithinAt.sum (fun j hj => ContMDiffWithinAt.sum (fun i hi => ?_))
    exact ((contMDiffWithinAt_const (c := (Work.Diff.EXT.bB (E := E)).repr a i)).mul
      (contMDiffWithinAt_const (c := (Work.Diff.EXT.bB (E := E)).repr b j))).mul (key i j)
  refine hfin.congr (fun q hq => ?_) ?_
  · simp only [hua, hvb, map_sum, map_smul, sum_apply, smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j hj => Finset.sum_congr rfl (fun i hi => ?_))
    ring
  · simp only [hua, hvb, map_sum, map_smul, sum_apply, smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j hj => Finset.sum_congr rfl (fun i hi => ?_))
    ring

theorem hasDerivWithinAt_metDiff_flow
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M]
    (A : ℝ → Submission.Diff.SMet I M) (J : Set ℝ) (hA : Submission.Diff.JointSmooth A J)
    (φ : ℝ → Diffeomorph I I M M (⊤ : ℕ∞)) (Y : ℝ → Π x : M, TangentSpace I x)
    (dA : ℝ → (x : M) → TangentSpace I x → TangentSpace I x → ℝ)
    (hφ : ContMDiffOn ((modelWithCornersSelf ℝ ℝ).prod I) I (⊤ : ℕ∞)
      (fun p : ℝ × M ↦ φ p.1 p.2) (J ×ˢ Set.univ))
    (hvel : ∀ t ∈ J, ∀ x : M,
      HasMFDerivWithinAt (modelWithCornersSelf ℝ ℝ) I (fun s ↦ φ s x) J t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (Y t (φ t x))))
    (hAderiv : ∀ t ∈ J, ∀ (x : M) (u v : TangentSpace I x),
      HasDerivWithinAt (fun s ↦ (A s).inner x u v) (dA t x u v) J t) :
    ∀ t ∈ J, ∀ (x : M) (u v : TangentSpace I x),
      HasDerivWithinAt
        (fun s ↦ (A s).inner (φ s x) (mfderiv I I (φ s : M → M) x u)
            (mfderiv I I (φ s : M → M) x v)
          - (A t).inner (φ s x) (mfderiv I I (φ s : M → M) x u)
            (mfderiv I I (φ s : M → M) x v))
        (dA t (φ t x) (mfderiv I I (φ t : M → M) x u) (mfderiv I I (φ t : M → M) x v))
        J t := by
  intro t ht x u v
  by_cases hdeg : 𝓝[J \ {t}] t = ⊥
  · exact hasDerivWithinAt_of_nhdsWithin_eq_bot_aux hdeg
  have hne : NeBot (𝓝[J \ {t}] t) := by
    by_contra h
    exact hdeg (Filter.not_neBot.mp h)
  -- the two-variable function whose diagonal is the function of the statement
  let Θ : ℝ × ℝ → ℝ := fun p ↦
      (A p.1).inner (φ p.2 x) (mfderiv I I (φ p.2 : M → M) x u)
        (mfderiv I I (φ p.2 : M → M) x v)
      - (A t).inner (φ p.2 x) (mfderiv I I (φ p.2 : M → M) x u)
        (mfderiv I I (φ p.2 : M → M) x v)
  -- the constant family `σ ↦ A t` is jointly smooth on `J`
  have hAt : Submission.Diff.JointSmooth (fun _ : ℝ => A t) J := by
    intro p hp
    exact ((A t).contMDiff p.2).contMDiffWithinAt.comp p contMDiffWithinAt_snd
      (fun q _ => Set.mem_univ q.2)
  -- joint smoothness of `Θ` within `J ×ˢ J` at `(t,t)`
  have hsm : ContMDiffWithinAt ((modelWithCornersSelf ℝ ℝ).prod (modelWithCornersSelf ℝ ℝ))
      (modelWithCornersSelf ℝ ℝ) (⊤ : ℕ∞) Θ (J ×ˢ J) (t, t) :=
    ContMDiffWithinAt.sub
      (Work.Diff.STE.C2.contMDiffWithinAt_metPair_twoVar_aux A J hA φ hφ ht x u v)
      (Work.Diff.STE.C2.contMDiffWithinAt_metPair_twoVar_aux (fun _ : ℝ => A t) J hAt φ hφ ht x u v)
  -- `Θ` is differentiable within `J ×ˢ J` at `(t,t)`; this is the uniformity we need
  have hsm' : ContDiffWithinAt ℝ (⊤ : ℕ∞) Θ (J ×ˢ J) (t, t) := by
    rw [← contMDiffWithinAt_iff_contDiffWithinAt, modelWithCornersSelf_prod]
    rw [show (prodChartedSpace ℝ ℝ ℝ ℝ) = (chartedSpaceSelf (ℝ × ℝ)) from
      chartedSpaceSelf_prod] at hsm
    exact hsm
  have hD : HasFDerivWithinAt Θ (fderivWithin ℝ Θ (J ×ˢ J) (t, t)) (J ×ˢ J) (t, t) :=
    (hsm'.differentiableWithinAt (by norm_num)).hasFDerivWithinAt
  let L : ℝ × ℝ →L[ℝ] ℝ := fderivWithin ℝ Θ (J ×ˢ J) (t, t)
  have hD' : HasFDerivWithinAt Θ L (J ×ˢ J) (t, t) := hD
  -- the `s`-slice of `Θ` at `σ = t` is `(A s) - (A t)` on the fixed vectors `dφ_t u`, `dφ_t v`
  have hγ1 : HasFDerivWithinAt (fun s : ℝ ↦ (s, t))
      ((1 : ℝ →L[ℝ] ℝ).prod (0 : ℝ →L[ℝ] ℝ)) J t :=
    (hasFDerivWithinAt_id t J).prodMk (hasFDerivWithinAt_const t t J)
  have hcomp1 : HasFDerivWithinAt (fun s : ℝ ↦ Θ (s, t))
      (L.comp ((1 : ℝ →L[ℝ] ℝ).prod (0 : ℝ →L[ℝ] ℝ))) J t :=
    HasFDerivWithinAt.comp (f := fun s : ℝ ↦ (s, t)) (x := t) (s := J) (t := J ×ˢ J)
      (g := Θ) (g' := L) hD' hγ1 (fun s hs ↦ ⟨hs, ht⟩)
  have hder1 : HasDerivWithinAt (fun s : ℝ ↦ Θ (s, t))
      (dA t (φ t x) (mfderiv I I (φ t : M → M) x u) (mfderiv I I (φ t : M → M) x v)) J t := by
    have h0 := (hAderiv t ht (φ t x) (mfderiv I I (φ t : M → M) x u)
      (mfderiv I I (φ t : M → M) x v)).sub_const
      ((A t).inner (φ t x) (mfderiv I I (φ t : M → M) x u) (mfderiv I I (φ t : M → M) x v))
    refine h0.congr (fun s hs => ?_) ?_
    · simp only [Θ]
    · simp only [Θ]
  have hL10 : L (1, 0) = dA t (φ t x) (mfderiv I I (φ t : M → M) x u)
      (mfderiv I I (φ t : M → M) x v) := by
    have h1 : (L.comp ((1 : ℝ →L[ℝ] ℝ).prod (0 : ℝ →L[ℝ] ℝ))) 1 = L (1, 0) := by
      simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply]
    rw [← h1]
    exact (eq_of_hasDerivWithinAt_aux hcomp1.hasDerivWithinAt hder1).resolve_left hdeg
  -- the `σ`-slice of `Θ` at `s = t` vanishes identically, hence `L (0,1) = 0`
  have hγ2 : HasFDerivWithinAt (fun σ : ℝ ↦ (t, σ))
      ((0 : ℝ →L[ℝ] ℝ).prod (1 : ℝ →L[ℝ] ℝ)) J t :=
    (hasFDerivWithinAt_const t t J).prodMk (hasFDerivWithinAt_id t J)
  have hcomp2 : HasFDerivWithinAt (fun σ : ℝ ↦ Θ (t, σ))
      (L.comp ((0 : ℝ →L[ℝ] ℝ).prod (1 : ℝ →L[ℝ] ℝ))) J t :=
    HasFDerivWithinAt.comp (f := fun σ : ℝ ↦ (t, σ)) (x := t) (s := J) (t := J ×ˢ J)
      (g := Θ) (g' := L) hD' hγ2 (fun σ hσ ↦ ⟨ht, hσ⟩)
  have hder2 : HasDerivWithinAt (fun σ : ℝ ↦ Θ (t, σ)) 0 J t :=
    (hasDerivWithinAt_const t J (0 : ℝ)).congr (fun σ hσ => by simp only [Θ, sub_self])
      (by simp only [Θ, sub_self])
  have hL01 : L (0, 1) = 0 := by
    have h1 : (L.comp ((0 : ℝ →L[ℝ] ℝ).prod (1 : ℝ →L[ℝ] ℝ))) 1 = L (0, 1) := by
      simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply]
    rw [← h1]
    exact (eq_of_hasDerivWithinAt_aux hcomp2.hasDerivWithinAt hder2).resolve_left hdeg
  -- the diagonal
  have hγ3 : HasFDerivWithinAt (fun s : ℝ ↦ (s, s))
      ((1 : ℝ →L[ℝ] ℝ).prod (1 : ℝ →L[ℝ] ℝ)) J t :=
    (hasFDerivWithinAt_id t J).prodMk (hasFDerivWithinAt_id t J)
  have hdiag : HasFDerivWithinAt (fun s : ℝ ↦ Θ (s, s))
      (L.comp ((1 : ℝ →L[ℝ] ℝ).prod (1 : ℝ →L[ℝ] ℝ))) J t :=
    HasFDerivWithinAt.comp (f := fun s : ℝ ↦ (s, s)) (x := t) (s := J) (t := J ×ˢ J)
      (g := Θ) (g' := L) hD' hγ3 (fun s hs ↦ ⟨hs, hs⟩)
  have hval : (L.comp ((1 : ℝ →L[ℝ] ℝ).prod (1 : ℝ →L[ℝ] ℝ))) 1
      = dA t (φ t x) (mfderiv I I (φ t : M → M) x u) (mfderiv I I (φ t : M → M) x v) := by
    rw [ContinuousLinearMap.comp_apply]
    have h2 : ((1 : ℝ →L[ℝ] ℝ).prod (1 : ℝ →L[ℝ] ℝ)) (1 : ℝ)
        = ((1 : ℝ), (0 : ℝ)) + ((0 : ℝ), (1 : ℝ)) := by
      simp [ContinuousLinearMap.prod_apply]
    rw [h2, map_add, hL10, hL01, add_zero]
  have hdiag' := hdiag.hasDerivWithinAt
  rw [hval] at hdiag'
  simpa [Θ] using hdiag'

end Work.Diff.STE.C2
