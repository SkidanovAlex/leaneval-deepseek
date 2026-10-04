import Mathlib
import Submission.Work.Diff.EXT.evolKDefs
import Submission.Work.Diff.EXT.covK_familySmooth
import Submission.Work.Diff.EXT.twoSided_of_within
import Submission.Work.EXT.lcSmooth_noBoundary

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Differentiability in time of the components of `∇^k Rm` along a Ricci flow

The target `Work.Diff.EXT.covKRm_derivWithin` is the *existence* half of the `k`-th order Shi
estimate (`Work.Diff.EXT.EvolCompKFix k`, `Work.Diff.EXT.EvolCompKFixReact k`): for every Ricci
flow `G` on `[0,T)`, every `t ∈ [0,T)`, every `x : M` and all tangent vectors `u : Fin k → TₓM`,
`a b c d : TₓM`, the function

`s ↦ covKRm (G s) x k u a b c d = (∇^k Rm)(G s)(x)(u, a, b, c, d)`

is differentiable in `s`, one-sidedly at the initial time `t = 0`, with derivative given by
`derivWithin … (Ioi 0) t` — the right derivative of the flow, which is the quantity that the
evolution equation `∂ₜ∇^k Rm = Δ∇^k Rm + R_k` computes.

## Route

The `s`-dependence of `covKRm (G s) x k u a b c d` is only through the metric family, and the value
at `x` of the tower `covKRmExt` is a `C^∞` function of the germ of the metric family at `x`.  The
joint smoothness of the tower family on an **open** set of times is `Work.Diff.EXT.covK_familySmooth`
(`covKRm_tower_jointSmooth` below, the instance for the constant field families
`smoothExt x ·`, using `Work.Diff.EXT.jointField_const`), so:

* for `t > 0` the family is smooth at `(t, x)` on the open time interval `(t/2, T) ⊆ [0,T)`
  (`JointSmooth` restricts), whence the slice `s ↦ covKRm (G s) x k u a b c d` is differentiable at
  `t` in the ordinary sense; and `derivWithin … (Ioi 0) t = deriv … t` because `Ioi 0 ∈ 𝓝 t`;
* for `t = 0` the family is only known to be smooth on the half-open set `[0,T) × M`
  (`IsRicciFlow` gives `JointSmooth G (Ico 0 T)`), and the derivative is one-sided.  Here the
  *two-sided* extension `Work.Diff.EXT.twoSided_of_within` is used: there are `ε > 0` and a family
  `K` jointly smooth on `(-ε, ε)`, agreeing with `G` on `[0, ε)`.  `K`'s tower family is smooth at
  `(0, x)` on the *open* slab `(-ε,ε) × M`, hence `s ↦ covKRm (K s) x k u a b c d` has an ordinary
  derivative `D` at `0`; and since `G = K` on `[0, ε)` the functions agree in the filters
  `𝓝[Ico 0 T] 0` and `𝓝[Ioi 0] 0` (they agree on `Ico 0 (min ε T)` respectively on
  `Ioo 0 (min ε T)`, both of which are neighbourhoods of `0` in the respective filters).  So
  `Filter.EventuallyEq.hasDerivWithinAt_iff` transfers `HasDerivWithinAt … D` to `G`'s function for
  both sets, and `HasDerivWithinAt.derivWithin` (`UniqueDiffWithinAt ℝ (Ioi 0) 0`) identifies
  `derivWithin … (Ioi 0) 0` with `D`, which is what the statement asks for.

All the analytic content is thus in the (already proved) `covK_familySmooth` and
`twoSided_of_within`; this file only assembles them.
-/

namespace Work.Diff.EXT

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]

/-- The family of tangent vectors `smoothExt x ·` is jointly smooth as a constant-in-`t` family of
fields. -/
theorem jointField_smoothExt_const [I.Boundaryless] [T2Space M] {V : Set (ℝ × M)} (x : M)
    (u : TangentSpace I x) :
    JointField (I := I) (M := M) (fun (_ : ℝ) => smoothExt x u) V :=
  (jointField_const (I := I) (M := M) (Work.Diff.GE.smoothExt_cmdiff x u)).mono (Set.subset_univ _)

/-- **Joint smoothness of the tower family on an open time interval.**  If `G` is jointly smooth on
`J × M` with `J` open, then so is `(t,y) ↦ (∇^k Rm)(G t)(y)` evaluated on the (constant in `t`)
fields `smoothExt x ·`.  This is the instance of `Work.Diff.EXT.covK_familySmooth` with the constant
field families; its value at `(s,x)` is `covKRm (G s) x k u a b c d` (`rfl`). -/
theorem covKRm_tower_jointSmooth
    [I.Boundaryless] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M)
    {G : ℝ → Submission.Diff.SMet I M} {J : Set ℝ} (hJ : IsOpen J) (hG : JointSmooth G J)
    (k : ℕ) (x : M) (u : Fin k → TangentSpace I x) (a b c d : TangentSpace I x) :
    ContMDiffOn ((𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => covKRmExt (G p.1) k (fun r : Fin k => smoothExt x (u r))
        (smoothExt x a) (smoothExt x b) (smoothExt x c) (smoothExt x d) p.2)
      (J ×ˢ (univ : Set M)) := by
  have hV : IsOpen (J ×ˢ (univ : Set M)) := hJ.prod isOpen_univ
  have hG' : JointMet (I := I) (M := M) G (J ×ˢ (univ : Set M)) := hG
  exact covK_familySmooth (I := I) (M := M) hLC (G := G) (V := J ×ˢ (univ : Set M)) hV hG' k
    (Vf := fun (_ : ℝ) (r : Fin k) => smoothExt x (u r))
    (fun r => jointField_smoothExt_const (I := I) (M := M) x (u r))
    (jointField_smoothExt_const (I := I) (M := M) x a)
    (jointField_smoothExt_const (I := I) (M := M) x b)
    (jointField_smoothExt_const (I := I) (M := M) x c)
    (jointField_smoothExt_const (I := I) (M := M) x d)

/-- **The slice at a point is differentiable.**  If the tower family of `G` is `C^∞` at `(t₀, x)`
in the ordinary (`ContMDiffAt`) sense, then the slice `s ↦ covKRm (G s) x k u a b c d` is
differentiable at `t₀` (chain rule with the curve `s ↦ (s,x)`). -/
theorem covKRm_slice_hasDerivAt
    [I.Boundaryless] [T2Space M]
    {G : ℝ → SMet I M} {t₀ : ℝ} {k : ℕ} {x : M} {u : Fin k → TangentSpace I x}
    {a b c d : TangentSpace I x}
    (hsmooth : ContMDiffAt ((𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => covKRmExt (G p.1) k (fun r : Fin k => smoothExt x (u r))
        (smoothExt x a) (smoothExt x b) (smoothExt x c) (smoothExt x d) p.2) (t₀, x)) :
    HasDerivAt (fun s => covKRm (G s) x k u a b c d)
      (deriv (fun s => covKRm (G s) x k u a b c d) t₀) t₀ := by
  have hγ : ContMDiffAt 𝓘(ℝ, ℝ) ((𝓘(ℝ, ℝ)).prod I) ∞ (fun s : ℝ => (s, x)) t₀ :=
    contMDiffAt_id.prodMk (contMDiffAt_const (c := x))
  have hcomp : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞
      ((fun p : ℝ × M => covKRmExt (G p.1) k (fun r : Fin k => smoothExt x (u r))
        (smoothExt x a) (smoothExt x b) (smoothExt x c) (smoothExt x d) p.2)
        ∘ (fun s : ℝ => (s, x))) t₀ :=
    hsmooth.comp t₀ hγ
  have hfun : ((fun p : ℝ × M => covKRmExt (G p.1) k (fun r : Fin k => smoothExt x (u r))
        (smoothExt x a) (smoothExt x b) (smoothExt x c) (smoothExt x d) p.2)
        ∘ (fun s : ℝ => (s, x)))
      = (fun s => covKRm (G s) x k u a b c d) := rfl
  rw [hfun] at hcomp
  exact (hcomp.contDiffAt.differentiableAt (by simp)).hasDerivAt

theorem covKRm_derivWithin
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M] [CompactSpace M]
    {G : ℝ → Submission.Diff.SMet I M} {T : ℝ} (hflow : Submission.Diff.IsRicciFlow G T)
    {t : ℝ} (ht : t ∈ Set.Ico 0 T) (x : M) (k : ℕ)
    (u : Fin k → TangentSpace I x) (a b c d : TangentSpace I x) :
    HasDerivWithinAt (fun s => Work.Diff.EXT.covKRm (G s) x k u a b c d)
      (derivWithin (fun s => Work.Diff.EXT.covKRm (G s) x k u a b c d) (Set.Ioi 0) t)
      (Set.Ico 0 T) t := by
  have hT : 0 < T := lt_of_le_of_lt ht.1 ht.2
  have hLC : Submission.Diff.LCSmooth I M := Work.EXT.lcSmooth_noBoundary (I := I) (M := M)
  by_cases ht0 : t = 0
  · -- ## the initial time: use the two-sided extension of the flow
    subst ht0
    obtain ⟨ε, hε, K, hKsm, hagree⟩ := twoSided_of_within (I := I) (M := M) G T hT hflow.1
    -- the tower family of the two-sided extension is smooth at `(0,x)`
    have hΦK := covKRm_tower_jointSmooth (I := I) (M := M) hLC (G := K) isOpen_Ioo hKsm k
      x u a b c d
    have hsm : ContMDiffAt ((𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => covKRmExt (K p.1) k (fun r : Fin k => smoothExt x (u r))
          (smoothExt x a) (smoothExt x b) (smoothExt x c) (smoothExt x d) p.2) (0, x) :=
      hΦK.contMDiffAt ((isOpen_Ioo.prod isOpen_univ).mem_nhds ⟨⟨by linarith, hε⟩, mem_univ _⟩)
    have hderK := covKRm_slice_hasDerivAt (I := I) (M := M) (G := K) (t₀ := 0) hsm
    -- the two functions agree near `0` in both filters
    have hmin : 0 < min ε T := lt_min hε hT
    have hSico : Set.Ico 0 (min ε T) ∈ 𝓝[Set.Ico 0 T] (0 : ℝ) := by
      rw [mem_nhdsWithin]
      exact ⟨Set.Ioo (-(min ε T)) (min ε T), isOpen_Ioo, ⟨by linarith, hmin⟩, fun y hy => ⟨hy.2.1, hy.1.2⟩⟩
    have hSioi : Set.Ioo 0 (min ε T) ∈ 𝓝[Set.Ioi 0] (0 : ℝ) := by
      rw [mem_nhdsWithin]
      exact ⟨Set.Ioo (-1) (min ε T), isOpen_Ioo, ⟨by norm_num, hmin⟩, fun y hy => ⟨hy.2, hy.1.2⟩⟩
    have hAgree : ∀ s ∈ Set.Ico 0 (min ε T), K s = G s :=
      fun s hs => hagree s ⟨hs.1, lt_of_lt_of_le hs.2 (min_le_left ε T)⟩
    have hevIco : (fun s => covKRm (G s) x k u a b c d) =ᶠ[𝓝[Set.Ico 0 T] (0 : ℝ)]
        (fun s => covKRm (K s) x k u a b c d) := by
      filter_upwards [hSico] with s hs
      rw [hAgree s hs]
    have hevIoi : (fun s => covKRm (G s) x k u a b c d) =ᶠ[𝓝[Set.Ioi 0] (0 : ℝ)]
        (fun s => covKRm (K s) x k u a b c d) := by
      filter_upwards [hSioi] with s hs
      rw [hAgree s ⟨le_of_lt hs.1, hs.2⟩]
    have h0eq : (fun s => covKRm (G s) x k u a b c d) 0
        = (fun s => covKRm (K s) x k u a b c d) 0 := by
      show covKRm (G 0) x k u a b c d = covKRm (K 0) x k u a b c d
      rw [hagree 0 ⟨le_refl 0, hε⟩]
    -- transfer the derivative to `G` on both sets, and identify the two derivatives
    have hIoi : HasDerivWithinAt (fun s => covKRm (G s) x k u a b c d)
        (deriv (fun s => covKRm (K s) x k u a b c d) 0) (Set.Ioi 0) 0 :=
      (Filter.EventuallyEq.hasDerivWithinAt_iff hevIoi h0eq).mpr hderK.hasDerivWithinAt
    have hD : derivWithin (fun s => covKRm (G s) x k u a b c d) (Set.Ioi 0) 0
        = deriv (fun s => covKRm (K s) x k u a b c d) 0 :=
      hIoi.derivWithin (uniqueDiffWithinAt_Ioi 0)
    rw [hD]
    exact (Filter.EventuallyEq.hasDerivWithinAt_iff hevIco h0eq).mpr hderK.hasDerivWithinAt
  · -- ## an interior time: the flow is smooth on the open interval `(t/2, T) ∋ t`
    have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
    have hJopen : IsOpen (Set.Ioo (t / 2) T) := isOpen_Ioo
    have htJ : t ∈ Set.Ioo (t / 2) T := ⟨by linarith, ht.2⟩
    have hJsub : Set.Ioo (t / 2) T ⊆ Set.Ico 0 T := fun s hs => ⟨by linarith [hs.1], hs.2⟩
    have hGJ : JointSmooth G (Set.Ioo (t / 2) T) := hflow.1.mono (fun p hp => ⟨hJsub hp.1, hp.2⟩)
    have hΦG := covKRm_tower_jointSmooth (I := I) (M := M) hLC (G := G) hJopen hGJ k x u a b c d
    have hsm : ContMDiffAt ((𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => covKRmExt (G p.1) k (fun r : Fin k => smoothExt x (u r))
          (smoothExt x a) (smoothExt x b) (smoothExt x c) (smoothExt x d) p.2) (t, x) :=
      hΦG.contMDiffAt ((hJopen.prod isOpen_univ).mem_nhds ⟨htJ, mem_univ _⟩)
    have hder : HasDerivAt (fun s => covKRm (G s) x k u a b c d)
        (deriv (fun s => covKRm (G s) x k u a b c d) t) t :=
      covKRm_slice_hasDerivAt (I := I) (M := M) (G := G) (t₀ := t) hsm
    have hdw : derivWithin (fun s => covKRm (G s) x k u a b c d) (Set.Ioi 0) t
        = deriv (fun s => covKRm (G s) x k u a b c d) t :=
      derivWithin_of_mem_nhds (isOpen_Ioi.mem_nhds htpos)
    rw [hdw]
    exact hder.hasDerivWithinAt

end Work.Diff.EXT
