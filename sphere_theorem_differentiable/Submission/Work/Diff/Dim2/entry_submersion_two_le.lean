/-
# The `q`-cap entry map (`d = 2` branch): the corrected `entry_submersion`

`Submission/Work/Diff/Dim2/entry_submersion.lean` asks, for a jointly smooth flow family `Φ` of a
smooth field `V`, a smooth function `t` and a map `y` with `y x = Φ 0 (t x) x`, that
`mfderiv I I y x ≠ 0` -- **under the hypothesis `hdim : 1 ≤ Module.finrank ℝ E`**.  That is FALSE in
dimension `1` and the statement is therefore not provable as written.

*Counterexample* (`E = ℝ`, `M = S¹` with the standard structure, `I = 𝓘(ℝ,ℝ)`, `N` a small open arc
around a point `a`, and `V = ∂_θ` the unit translation field with flow `Φ s t x = x + (t - s)`):
put `y := fun _ => a` (constant), `t x := a - x` read in a chart of `S¹` at `a` and extended to a
globally smooth function on `S¹` by a bump function supported in that chart, and
`g θ := c - sin (θ - a)`.  Then:

* `hVsm`, `hΦsm`, `hΦself`, `hΦcoc` hold for the translation flow, and `hΦderiv` says that the
  velocity of `τ ↦ x + τ - s` is the field `V` (true);
* `y x = Φ 0 (t x) x` for `x ∈ N`, because `x + t x = a` there;
* `g (y x) = g a = c` and `mfderiv I 𝓘(ℝ,ℝ) g (y x) (V (y x)) = g'(a) = -1` (with `g' = -cos`);
* `y` is constant, so `mfderiv I I y x = 0`, contradicting the conclusion.

Note that compactness of `M` does not help: `S¹` is compact, connected and regular, and `E = ℝ`
satisfies `1 ≤ finrank ℝ E`, `Nontrivial E`, `CompleteSpace E`.

The correct hypothesis is `2 ≤ Module.finrank ℝ E`, and this file proves the corrected statement.
For a `y` of the shape above on the open set `N` one has, for every `v : TₓM`,

`mfderiv I I y x v = (mfderiv I I (z ↦ Φ 0 (t x) z) x) v + (Dt x v) • V (y x)`,

and the map `z ↦ Φ (t x) 0 z` is a *left inverse* of `z ↦ Φ 0 (t x) z` by the cocycle axiom, so its
derivative `B` satisfies `B * A = id`.  If `mfderiv I I y x = 0` then every `v : TₓM` equals
`-(Dt x v) • (B (V (y x)))`, so `TₓM` is spanned by one vector and `finrank ℝ E ≤ 1`, contradicting
`2 ≤ finrank ℝ E`.

The two analytic ingredients (fixed-time slices of a jointly smooth flow are smooth; the chain rule
for `z ↦ Φ 0 (t z) z`) are separate lemmas below, for reuse.
-/
import Mathlib
import Submission.Work.Diff.Dim2.Lib
import Submission.Work.Diff.C.Defs

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option backward.isDefEq.respectTransparency false

namespace Work.Diff.Dim2

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter Submission.Geodesic

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Fixed-time slices of a jointly smooth flow family are smooth.** -/
lemma contMDiff_flow_fixed
    {V : (x : M) → TangentSpace I x} {Φ : ℝ → ℝ → M → M}
    (hΦsm : ContMDiff ((𝓘(ℝ,ℝ).prod 𝓘(ℝ,ℝ)).prod I) I ∞
      (fun q : (ℝ × ℝ) × M => Φ q.1.1 q.1.2 q.2))
    (a b : ℝ) : ContMDiff I I ∞ (fun z : M => Φ a b z) := by
  have h2 : ContMDiff I ((𝓘(ℝ,ℝ).prod 𝓘(ℝ,ℝ)).prod I) ∞
      (fun z : M => (((a, b) : ℝ × ℝ), z)) :=
    ContMDiff.prodMk contMDiff_const contMDiff_id
  exact hΦsm.comp h2

/-- **The chain rule for the "entry map" `z ↦ Φ 0 (t z) z`.**  Its derivative is the sum of the two
partial derivatives of the flow evaluated at `(t x, x)`: the time derivative
`r ↦ r • V (Φ 0 (t x) x)` (this is `hΦderiv` at `s = 0`) applied to `mfderiv t x v`, plus the
derivative of the spatial slice `z ↦ Φ 0 (t x) z` applied to `v`.

(Stated pointwise, with the real scalar `mvfderiv I t x v` in the `•`, so that no `TangentSpace`
coercions are needed at the use sites.) -/
lemma mfderiv_flow_map
    {V : (x : M) → TangentSpace I x} {Φ : ℝ → ℝ → M → M}
    (hΦsm : ContMDiff ((𝓘(ℝ,ℝ).prod 𝓘(ℝ,ℝ)).prod I) I ∞
      (fun q : (ℝ × ℝ) × M => Φ q.1.1 q.1.2 q.2))
    (hΦderiv : ∀ s t x, HasMFDerivAt 𝓘(ℝ,ℝ) I (fun τ : ℝ => Φ s τ x) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (V (Φ s t x))))
    {t : M → ℝ} {x : M} (ht : MDifferentiableAt I 𝓘(ℝ,ℝ) t x) :
    ∀ v : TangentSpace I x,
      mfderiv I I (fun z : M => Φ 0 (t z) z) x v
        = mfderiv I I (fun z : M => Φ 0 (t x) z) x v
          + (mvfderiv I t x v) • V (Φ 0 (t x) x) := by
  intro v
  set c : ℝ × M → M := fun q => Φ 0 q.1 q.2 with hc
  -- smoothness of the two-variable map
  have hc_sm : ContMDiff (𝓘(ℝ,ℝ).prod I) I ∞ c := by
    rw [hc]
    have hg1 : ContMDiff (𝓘(ℝ,ℝ).prod I) (𝓘(ℝ,ℝ).prod 𝓘(ℝ,ℝ)) ∞
        (fun q : ℝ × M => ((0 : ℝ), q.1)) :=
      ContMDiff.prodMk contMDiff_const contMDiff_fst
    exact hΦsm.comp (ContMDiff.prodMk hg1 contMDiff_snd)
  have hc_md : MDifferentiableAt (𝓘(ℝ,ℝ).prod I) I c (t x, x) :=
    (hc_sm.contMDiffAt).mdifferentiableAt (by simp)
  set Δ : M → ℝ × M := fun z => (t z, z) with hΔ
  have hΔ_md : MDifferentiableAt I (𝓘(ℝ,ℝ).prod I) Δ x := by
    rw [hΔ]
    exact ht.prodMk mdifferentiableAt_id
  have hcomp : mfderiv I I (c ∘ Δ) x
      = (mfderiv (𝓘(ℝ,ℝ).prod I) I c (t x, x)) ∘L (mfderiv I (𝓘(ℝ,ℝ).prod I) Δ x) :=
    mfderiv_comp x hc_md hΔ_md
  -- the derivative of the inner map `z ↦ (t z, z)`, componentwise
  have hΔfun : Δ = fun z : M => (t z, id z) := by funext z; rw [hΔ]; rfl
  have hΔ1 : ((mfderiv I (𝓘(ℝ,ℝ).prod I) Δ x) v).1 = (mfderiv I 𝓘(ℝ,ℝ) t x) v := by
    rw [hΔfun, mfderiv_prodMk ht mdifferentiableAt_id, mfderiv_id]
    rfl
  have hΔ2 : ((mfderiv I (𝓘(ℝ,ℝ).prod I) Δ x) v).2 = v := by
    rw [hΔfun, mfderiv_prodMk ht mdifferentiableAt_id, mfderiv_id]
    rfl
  -- the two partial derivatives of the flow
  have hfun : (fun z : ℝ => c (z, x)) = (fun τ : ℝ => Φ 0 τ x) := by funext z; simp only [hc]
  have hz : (fun z : M => c (t x, z)) = (fun z : M => Φ 0 (t x) z) := by funext z; simp only [hc]
  have hcv : (mfderiv (𝓘(ℝ,ℝ).prod I) I c (t x, x)) ((mfderiv I (𝓘(ℝ,ℝ).prod I) Δ x) v)
      = mfderiv I I (fun z : M => Φ 0 (t x) z) x v
        + (mvfderiv I t x v) • V (Φ 0 (t x) x) := by
    rw [mfderiv_prod_eq_add_apply hc_md, hΔ1, hΔ2, hfun, (hΦderiv 0 (t x) x).mfderiv, hz,
      add_comm]
    change (mfderiv I I (fun z : M => Φ 0 (t x) z) x) v + (mvfderiv I t x v) • V (Φ 0 (t x) x)
      = (mfderiv I I (fun z : M => Φ 0 (t x) z) x) v + (mvfderiv I t x v) • V (Φ 0 (t x) x)
    rfl
  -- assemble
  have hfun2 : (fun z : M => Φ 0 (t z) z) = c ∘ Δ := by
    funext z; simp only [hc, hΔ, Function.comp_apply]
  rw [hfun2, hcomp, ContinuousLinearMap.comp_apply, hcv]

/-- **The flow at time `s` followed by the flow backwards from `s` is the identity**: this is the
cocycle axiom (with `s = 0`, `t = s`, `u = 0`). -/
lemma flow_comp_inverse
    {Φ : ℝ → ℝ → M → M}
    (hΦself : ∀ s x, Φ s s x = x)
    (hΦcoc : ∀ s t u x, Φ t u (Φ s t x) = Φ s u x) (s : ℝ) (z : M) :
    Φ s 0 (Φ 0 s z) = z := by
  rw [hΦcoc 0 s 0 z, hΦself 0 z]

/-- **`mfderiv` depends only on the germ at the point** (for maps `M → M`). -/
lemma mfderiv_congr_of_eventuallyEq_mm
    {f g : M → M} {x : M} (h : f =ᶠ[𝓝 x] g) :
    mfderiv I I f x = mfderiv I I g x := by
  rw [Filter.EventuallyEq.mfderiv_eq h]
  ext v
  rfl

/-- **The `q`-cap entry map is an immersion** (the corrected form of
`Work.Diff.Dim2.entry_submersion`: the dimension hypothesis must be `2 ≤ finrank`).

For a jointly smooth flow family `Φ` of the smooth field `V` (axioms: `Φ s s x = x`, the velocity
axiom and the cocycle), a smooth `t` and a map `y` with `y x = Φ 0 (t x) x` on the open set `N`,
with `g (y x) = c` constant on `N` and `dg (V) = -1` at `y x`, the derivative of `y` is nonzero at
every point of `N` -- provided `2 ≤ dim M`. -/
theorem entry_submersion_two_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M] [RegularSpace M]
    (hdim : 2 ≤ Module.finrank ℝ E)
    {N : Set M} (hN : IsOpen N)
    {V : (x : M) → TangentSpace I x} {Φ : ℝ → ℝ → M → M}
    (hVsm : ContMDiff I (I.prod (modelWithCornersSelf ℝ E)) ∞
      (fun y : M => (⟨y, V y⟩ : Bundle.TotalSpace E (TangentSpace I))))
    (hΦsm : ContMDiff ((𝓘(ℝ,ℝ).prod 𝓘(ℝ,ℝ)).prod I) I ∞
      (fun q : (ℝ × ℝ) × M => Φ q.1.1 q.1.2 q.2))
    (hΦself : ∀ s x, Φ s s x = x)
    (hΦderiv : ∀ s t x, HasMFDerivAt 𝓘(ℝ,ℝ) I (fun τ : ℝ => Φ s τ x) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (V (Φ s t x))))
    (hΦcoc : ∀ s t u x, Φ t u (Φ s t x) = Φ s u x)
    {g : M → ℝ} {c : ℝ}
    {t : M → ℝ} (htsm : ∀ x ∈ N, ContMDiffAt I 𝓘(ℝ,ℝ) ∞ t x)
    {y : M → M} (hysm : ∀ x ∈ N, ContMDiffAt I I ∞ y x)
    (hyform : ∀ x ∈ N, y x = Φ 0 (t x) x)
    (hyc : ∀ x ∈ N, g (y x) = c)
    (hgmd : ∀ x ∈ N, MDifferentiableAt I 𝓘(ℝ,ℝ) g (y x))
    (hgV : ∀ x ∈ N, mfderiv I 𝓘(ℝ,ℝ) g (y x) (V (y x)) = -1) :
    ∀ x ∈ N, mfderiv I I y x ≠ 0 := by
  intro x hx h0
  have htmd : MDifferentiableAt I 𝓘(ℝ,ℝ) t x := (htsm x hx).mdifferentiableAt (by simp)
  -- `y` agrees with the explicit flow formula near `x`
  have hyev : y =ᶠ[𝓝 x] (fun z : M => Φ 0 (t z) z) := by
    filter_upwards [hN.mem_nhds hx] with z hz
    exact hyform z hz
  have hyder : mfderiv I I y x = mfderiv I I (fun z : M => Φ 0 (t z) z) x :=
    mfderiv_congr_of_eventuallyEq_mm hyev
  -- the chain rule for the explicit formula
  have hform := mfderiv_flow_map (V := V) (Φ := Φ) hΦsm hΦderiv htmd
  -- a vanishing derivative of `y` at `x` is an equation for the two partials (the transfer of the
  -- vanishing derivative from `y` to the explicit flow map is done with `HasMFDerivAt`, which
  -- avoids the `y x` / `Φ 0 (t x) x` mismatch of the two `TangentSpace` types)
  have hymd : MDifferentiableAt I I y x := (hysm x hx).mdifferentiableAt (by simp)
  have hy0 : HasMFDerivAt I I y x 0 := h0 ▸ hymd.hasMFDerivAt
  have hF0 : HasMFDerivAt I I (fun z : M => Φ 0 (t z) z) x 0 :=
    hy0.congr_of_eventuallyEq_abuse hyev.symm
  have hFder : mfderiv I I (fun z : M => Φ 0 (t z) z) x = 0 := hF0.mfderiv
  have hzero : ∀ w : TangentSpace I x,
      (mfderiv I I (fun z : M => Φ 0 (t x) z) x) w + (mvfderiv I t x w) • V (Φ 0 (t x) x)
        = 0 := by
    intro w
    have h1 : (mfderiv I I (fun z : M => Φ 0 (t z) z) x) w = 0 := by rw [hFder]; rfl
    rw [hform w] at h1
    exact h1
  -- the backward flow is a left inverse of the forward flow (cocycle axiom)
  have hψsm : ContMDiffAt I I ∞ (fun z : M => Φ 0 (t x) z) x :=
    (contMDiff_flow_fixed (I := I) (V := V) (Φ := Φ) hΦsm 0 (t x)).contMDiffAt
  have hφsm : ContMDiffAt I I ∞ (fun z : M => Φ (t x) 0 z) (Φ 0 (t x) x) :=
    (contMDiff_flow_fixed (I := I) (V := V) (Φ := Φ) hΦsm (t x) 0).contMDiffAt
  have hid : (fun z : M => Φ (t x) 0 (Φ 0 (t x) z)) = id := by
    funext z
    exact flow_comp_inverse hΦself hΦcoc (t x) z
  have hBA : mfderiv I I (fun z : M => Φ (t x) 0 z) (Φ 0 (t x) x) ∘L
      mfderiv I I (fun z : M => Φ 0 (t x) z) x
        = ContinuousLinearMap.id ℝ (TangentSpace I x) := by
    have h1 : mfderiv I I (fun z : M => Φ (t x) 0 (Φ 0 (t x) z)) x
        = mfderiv I I (fun z : M => Φ (t x) 0 z) (Φ 0 (t x) x) ∘L
          mfderiv I I (fun z : M => Φ 0 (t x) z) x :=
      mfderiv_comp x (hφsm.mdifferentiableAt (by simp)) (hψsm.mdifferentiableAt (by simp))
    rw [← h1, hid, mfderiv_id]
  -- hence every vector is a multiple of the single vector `B (V (Φ 0 (t x) x))`
  have hmem : ∀ w : TangentSpace I x, ∃ cc : ℝ,
      cc • ((mfderiv I I (fun z : M => Φ (t x) 0 z) (Φ 0 (t x) x)) (V (Φ 0 (t x) x)))
        = w := by
    intro w
    have h2 : (mfderiv I I (fun z : M => Φ 0 (t x) z) x) w
        = -((mvfderiv I t x w) • V (Φ 0 (t x) x)) :=
      eq_neg_of_add_eq_zero_left (hzero w)
    have h3 : (mfderiv I I (fun z : M => Φ (t x) 0 z) (Φ 0 (t x) x))
        ((mfderiv I I (fun z : M => Φ 0 (t x) z) x) w) = w := by
      have h4 : ((mfderiv I I (fun z : M => Φ (t x) 0 z) (Φ 0 (t x) x)) ∘L
          (mfderiv I I (fun z : M => Φ 0 (t x) z) x)) w = w := by
        rw [hBA]; rfl
      rwa [ContinuousLinearMap.comp_apply] at h4
    refine ⟨-(mvfderiv I t x w), ?_⟩
    calc (-(mvfderiv I t x w)) •
          ((mfderiv I I (fun z : M => Φ (t x) 0 z) (Φ 0 (t x) x)) (V (Φ 0 (t x) x)))
        = (mfderiv I I (fun z : M => Φ (t x) 0 z) (Φ 0 (t x) x))
            ((-(mvfderiv I t x w)) • V (Φ 0 (t x) x)) :=
          (map_smul _ _ _).symm
      _ = (mfderiv I I (fun z : M => Φ (t x) 0 z) (Φ 0 (t x) x))
            (-((mvfderiv I t x w) • V (Φ 0 (t x) x))) := by
          rw [neg_smul]
      _ = (mfderiv I I (fun z : M => Φ (t x) 0 z) (Φ 0 (t x) x))
            ((mfderiv I I (fun z : M => Φ 0 (t x) z) x) w) := by
          rw [← h2]
      _ = w := h3
  have hfin : Module.finrank ℝ (TangentSpace I x) ≤ 1 :=
    (finrank_le_one_iff (K := ℝ) (V := TangentSpace I x)).mpr ⟨_, hmem⟩
  have hfinE : Module.finrank ℝ E ≤ 1 := hfin
  omega

end

end Work.Diff.Dim2
