import Mathlib
import Submission.Work.PTGeometric.SourceZero
import Submission.Work.PTGeometric.FDerivInChart

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Flatness of a defining function along the tail ray

`Work.PTGeometric.mfderiv_flat_of_ray`: if `ρ : EuclideanHalfSpace N → ℝ` is smooth (`C^∞` on the
manifold with boundary `EuclideanHalfSpace N`), nonnegative, vanishes at a boundary point `x`
(`x.1 0 = 0`) and vanishes identically on the "tail ray"

`{y | y.1 i = x.1 i (i ≠ 0), y.1 0 ≤ 1/2}`

through `x` (the segment through `x` in the inward normal direction `e₀` up to the level `1/2`),
then `mfderiv ρ x = 0`.

This is the analytic input of the source-region construction (`SOURCE_PLAN.md`): the defining
function of the source region is flat at the boundary points of its zero set along the tail, so its
manifold derivative vanishes there.

## The proof

At a boundary point of the half-space, `mfderiv` is a derivative *within* `range I = {z | 0 ≤ z 0}`
in the preferred chart, so it coincides with the ordinary within-derivative of the charted function
`z ↦ ρ (I.symm z)`.  For that function, read in coordinates:

* `ρ ≥ 0 = ρ x` says that `x` is a minimum, so every direction of the positive tangent cone
  `{v | 0 ≤ v 0}` at `x` has nonnegative derivative (`IsLocalMinOn.hasFDerivWithinAt_nonneg`), and
  every *tangential* direction (`v 0 = 0`) has derivative `0` (both `v` and `-v` are in the cone);
* the vanishing of `ρ` on the ray `x + t e₀`, `t ∈ [0, 1/2]`, forces `L e₀ = 0`: the composition
  `t ↦ ρ (x + t e₀)` is constant `ρ x = 0` on `[0, 1/2]`, hence has right derivative `0`, while the
  chain rule on the curve `t ↦ x + t e₀` gives right derivative `L e₀`.

Decomposing `v = (v - (v 0) e₀) + (v 0) e₀` finishes the argument.
-/

namespace Work.PTGeometric

noncomputable section

open scoped Manifold ContDiff Topology
open Function Set Topology Manifold Filter

/-- The first standard basis vector of `ℝ^N`. -/
def e0 (N : ℕ) [NeZero N] : EuclideanSpace ℝ (Fin N) := EuclideanSpace.single 0 1

lemma e0_apply {N : ℕ} [NeZero N] : (e0 N).ofLp 0 = 1 := by simp [e0]

lemma e0_apply_ne {N : ℕ} [NeZero N] {i : Fin N} (hi : i ≠ 0) : (e0 N).ofLp i = 0 := by
  simp [e0, hi]

/-- **Flatness of a nonnegative function on the half-space along the ray in the direction `e₀`.**
If `g` is differentiable within the half-space `{z | 0 ≤ z 0}` at the boundary point `x`
(`x 0 = 0`), is `≥ 0` on the half-space with `g x = 0`, and vanishes on the segment
`x + [0, 1/2] • e₀`, then its within-derivative `L` at `x` vanishes. -/
theorem fderivWithin_eq_zero_of_halfspace_ray {N : ℕ} [NeZero N]
    {g : EuclideanSpace ℝ (Fin N) → ℝ} {L : EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ}
    {x : EuclideanSpace ℝ (Fin N)} (hx : x.ofLp 0 = 0)
    (hg : HasFDerivWithinAt g L {z | 0 ≤ z.ofLp 0} x)
    (hnn : ∀ z, 0 ≤ z.ofLp 0 → 0 ≤ g z) (hgx : g x = 0)
    (hray : ∀ t ∈ Set.Icc (0 : ℝ) (1 / 2), g (x + t • e0 N) = 0) :
    L = 0 := by
  have hmin : IsLocalMinOn g {z | 0 ≤ z.ofLp 0} x := by
    rw [IsLocalMinOn]
    filter_upwards [self_mem_nhdsWithin] with z hz
    rw [hgx]
    exact hnn z hz
  -- every direction of the positive tangent cone at `x`
  have hcone : ∀ v : EuclideanSpace ℝ (Fin N), 0 ≤ v.ofLp 0 →
      v ∈ posTangentConeAt {z | 0 ≤ z.ofLp 0} x := by
    intro v hv
    have hsub : openSegment ℝ x (x + v) ⊆ {z : EuclideanSpace ℝ (Fin N) | 0 ≤ z.ofLp 0} := by
      rw [openSegment_eq_image]
      rintro _ ⟨θ, hθ, rfl⟩
      simp only [Set.mem_ofPred_eq]
      rw [show ((1 - θ) • x + θ • (x + v)).ofLp 0 =
          (1 - θ) * x.ofLp 0 + θ * (x.ofLp 0 + v.ofLp 0) by
        simp [PiLp.add_apply, PiLp.smul_apply]; ring]
      rw [hx]
      nlinarith [hθ.1, hv]
    have := sub_mem_posTangentConeAt_of_openSegment_subset hsub
    simpa using this
  -- the inward direction: `g` is constant along the ray, so `L e₀ = 0`
  have hrayDir : L (e0 N) = 0 := by
    have hmaps : MapsTo (fun t : ℝ => x + t • e0 N) (Set.Icc (0 : ℝ) (1 / 2))
        {z | 0 ≤ z.ofLp 0} := by
      intro t ht
      simp only [Set.mem_ofPred_eq]
      rw [show (x + t • e0 N).ofLp 0 = x.ofLp 0 + t * (e0 N).ofLp 0 by
        simp [PiLp.add_apply, PiLp.smul_apply]]
      rw [hx, e0_apply]
      linarith [ht.1]
    have hderiv : HasDerivWithinAt (fun t : ℝ => x + t • e0 N) (e0 N)
        (Set.Icc (0 : ℝ) (1 / 2)) 0 := by
      simpa using (((hasDerivAt_id (0 : ℝ)).smul_const (e0 N)).const_add x).hasDerivWithinAt
    have hg' : HasFDerivWithinAt g L {z | 0 ≤ z.ofLp 0} ((fun t : ℝ => x + t • e0 N) 0) := by
      simpa using hg
    have h1 : HasDerivWithinAt (fun t : ℝ => g (x + t • e0 N)) (L (e0 N))
        (Set.Icc (0 : ℝ) (1 / 2)) 0 := hg'.comp_hasDerivWithinAt (0 : ℝ) hderiv hmaps
    have h2 : HasDerivWithinAt (fun t : ℝ => g (x + t • e0 N)) (0 : ℝ)
        (Set.Icc (0 : ℝ) (1 / 2)) 0 := by
      have heq : (fun t : ℝ => g (x + t • e0 N)) =ᶠ[𝓝[Set.Icc (0 : ℝ) (1 / 2)] 0]
          (fun _ : ℝ => (0 : ℝ)) := by
        filter_upwards [self_mem_nhdsWithin] with t ht
        exact hray t ht
      refine heq.hasDerivWithinAt_iff ?_ |>.mpr ?_
      · simpa using hray 0 ⟨le_rfl, by norm_num⟩
      · exact hasDerivWithinAt_const _ _ _
    have hui : UniqueDiffWithinAt ℝ (Set.Icc (0 : ℝ) (1 / 2)) (0 : ℝ) :=
      (uniqueDiffOn_Icc (by norm_num : (0 : ℝ) < 1 / 2)) 0 (by norm_num)
    have e1 := h1.derivWithin hui
    have e2 := h2.derivWithin hui
    exact e1 ▸ e2
  apply ContinuousLinearMap.ext
  intro v
  have hzero : (v - (v.ofLp 0) • e0 N).ofLp 0 = 0 := by
    simp [PiLp.sub_apply, PiLp.smul_apply, e0_apply]
  have hzero' : (-(v - (v.ofLp 0) • e0 N)).ofLp 0 = 0 := by
    simp [PiLp.sub_apply, PiLp.smul_apply, e0_apply]
  have htang : v - (v.ofLp 0) • e0 N ∈ posTangentConeAt {z | 0 ≤ z.ofLp 0} x :=
    hcone _ (le_of_eq hzero.symm)
  have hnegt : -(v - (v.ofLp 0) • e0 N) ∈ posTangentConeAt {z | 0 ≤ z.ofLp 0} x :=
    hcone _ (le_of_eq hzero'.symm)
  have hL1 : L (v - (v.ofLp 0) • e0 N) = 0 :=
    hmin.hasFDerivWithinAt_eq_zero hg htang hnegt
  calc L v = L ((v - (v.ofLp 0) • e0 N) + (v.ofLp 0) • e0 N) := by rw [sub_add_cancel]
    _ = L (v - (v.ofLp 0) • e0 N) + L ((v.ofLp 0) • e0 N) := by rw [map_add]
    _ = (v.ofLp 0) * L (e0 N) := by rw [map_smul, hL1, zero_add]; rfl
    _ = 0 := by rw [hrayDir, mul_zero]

theorem mfderiv_flat_of_ray {N : ℕ} [NeZero N] (ρ : EuclideanHalfSpace N → ℝ)
    (hρsm : ContMDiff (modelWithCornersEuclideanHalfSpace N) (modelWithCornersSelf ℝ ℝ)
      ((⊤ : ℕ∞) : WithTop ℕ∞) ρ)
    (hρ0 : ∀ x, 0 ≤ ρ x)
    (x : EuclideanHalfSpace N) (hx : x.1 0 = 0) (hρx : ρ x = 0)
    (hray : ∀ y : EuclideanHalfSpace N, (∀ i : Fin N, i ≠ 0 → y.1 i = x.1 i) → y.1 0 ≤ 1/2 →
      ρ y = 0) :
    mfderiv (modelWithCornersEuclideanHalfSpace N) (modelWithCornersSelf ℝ ℝ) ρ x = 0 := by
  have hmd : MDifferentiableAt (modelWithCornersEuclideanHalfSpace N)
      (modelWithCornersSelf ℝ ℝ) ρ x := hρsm.mdifferentiableAt (by simp)
  -- `mfderiv` at a point of the half-space is the within-derivative of the charted function
  have hg0 := hasFDerivWithinAt_comp_extChartAt_symm (I := modelWithCornersEuclideanHalfSpace N) hmd
  have hg1 : HasFDerivWithinAt
      (fun z : EuclideanSpace ℝ (Fin N) => ρ ((modelWithCornersEuclideanHalfSpace N).symm z))
      (mfderiv (modelWithCornersEuclideanHalfSpace N) (modelWithCornersSelf ℝ ℝ) ρ x)
      {z : EuclideanSpace ℝ (Fin N) | 0 ≤ z.ofLp 0} x.1 := by
    rw [show range (modelWithCornersEuclideanHalfSpace N) =
        {z : EuclideanSpace ℝ (Fin N) | 0 ≤ z.ofLp 0} from
        range_modelWithCornersEuclideanHalfSpace N] at hg0
    exact hg0
  refine fderivWithin_eq_zero_of_halfspace_ray (hx := hx) hg1 ?_ ?_ ?_
  · intro z hz
    rw [modelWithCornersEuclideanHalfSpace_symm_apply_of_le hz]
    exact hρ0 _
  · rw [show (modelWithCornersEuclideanHalfSpace N).symm x.1 = x by
      rw [modelWithCornersEuclideanHalfSpace_symm_apply_of_le x.2]
      rfl]
    exact hρx
  · intro t ht
    have htz : 0 ≤ (x.1 + t • e0 N).ofLp 0 := by
      rw [show (x.1 + t • e0 N).ofLp 0 = x.1.ofLp 0 + t * (e0 N).ofLp 0 by
        simp [PiLp.add_apply, PiLp.smul_apply]]
      rw [show x.1.ofLp 0 = 0 from hx, e0_apply]
      linarith [ht.1]
    rw [show (modelWithCornersEuclideanHalfSpace N).symm (x.1 + t • e0 N) =
        ⟨x.1 + t • e0 N, htz⟩ from
        modelWithCornersEuclideanHalfSpace_symm_apply_of_le htz]
    refine hray _ ?_ ?_
    · intro i hi
      rw [show (x.1 + t • e0 N).ofLp i = x.1.ofLp i + t * (e0 N).ofLp i by
        simp [PiLp.add_apply, PiLp.smul_apply]]
      rw [e0_apply_ne hi, mul_zero, add_zero]
    · rw [show (x.1 + t • e0 N).ofLp 0 = x.1.ofLp 0 + t * (e0 N).ofLp 0 by
        simp [PiLp.add_apply, PiLp.smul_apply]]
      rw [show x.1.ofLp 0 = 0 from hx, e0_apply]
      linarith [ht.2]

end

end Work.PTGeometric

