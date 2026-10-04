import Mathlib
import Submission.Work.Diff.Dim2.Lib
import Submission.Work.Diff.C.Defs
import Submission.Work.Diff.Dim2.entry_submersion_two_le

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option backward.isDefEq.respectTransparency false

namespace Work.Diff.Dim2

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter Submission.Geodesic

/-- **The `q`-cap entry map is an immersion** (`d = 2` branch of the differentiable sphere theorem).

`y x = Φ 0 (t x) x` is the point reached from `x` by flowing along the Reeb field `V` for time
`t x`, and `g` is a function with `g (y x) = c` on the open set `N` whose derivative in the `V`
direction at `y x` is `-1`.  Then `y` has nonzero derivative at every point of `N`.

The dimension hypothesis `2 ≤ finrank ℝ E` is sharp: in dimension `1` the statement is false (a
constant `y` with `t x` the time needed to flow `x` to a fixed point, and `g` built from `sin`, is a
counterexample).  See `Submission/Work/Diff/Dim2/entry_submersion_two_le.lean` for the analytic
ingredients of the proof:

* `contMDiff_flow_fixed` — fixed-time slices of a jointly smooth flow family are smooth;
* `mfderiv_flow_map` — the chain rule
  `d(y) x v = d(z ↦ Φ 0 (t x) z) x v + (Dt x v) • V (y x)`;
* `flow_comp_inverse` — the cocycle axiom `Φ s 0 (Φ 0 s z) = z`.

The argument: the backward flow `z ↦ Φ (t x) 0 z` is a smooth left inverse of the forward flow
`z ↦ Φ 0 (t x) z`, so its derivative `B` satisfies `B ∘L A = id` where `A = d(z ↦ Φ 0 (t x) z) x`;
hence `A` is injective.  If `d(y) x = 0`, the chain rule forces `A w = -(Dt x w) • V (y x)` for
every `w`, so every tangent vector lies in the span of the single vector `B (V (y x))`; therefore
`finrank ℝ (TₓM) ≤ 1`, contradicting `2 ≤ finrank ℝ E`. -/
theorem entry_submersion
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

end Work.Diff.Dim2
