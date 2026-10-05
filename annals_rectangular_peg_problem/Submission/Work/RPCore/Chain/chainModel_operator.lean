import Mathlib
import Submission.Work.RPCore.Chain.C4Defs
import Submission.Work.RPCore.Chain.BvForm_lin
import Submission.Work.RPCore.Chain.selfAdjointRep
import Submission.Work.RPCore.Chain.refForm_kernel

/-!
# C4: the quadratic model operator of the reference chain action

`ChainSp n = (Fin (n+1) → ℝ²) × (Fin n → ℝ²)` carries the reference bilinear form
`BvForm n N δ`, the polar form of the quadratic part of the reference chain action, and the
diagonal vector `diagVec n`.  For `n = 3N - 1`, `N ≥ 1`, `cos δ ≠ 0` and `sin (N δ) ≠ 0` the
kernel of `BvForm n N δ` is exactly the line `ℝ ∙ diagVec n` (`refForm_kernel`, recalled below as
`BvForm_radical_kernel`).

Consequently, for *any* linear isomorphism
`e : ℝ × EuclideanSpace ℝ (Fin M) ≃ₗ[ℝ] ChainSp n` sending `(1, 0)` to `diagVec n` (such an `e`
exists by `chainCoordEquiv`), the restriction of `BvForm n N δ` to the hyperplane `e ({0} × E)`
is a nondegenerate symmetric bilinear form.  Writing it as
`β v w = BvForm n N δ (e (0,v)) (e (0,w))` and applying the Riesz representation theorem
(`selfAdjointRep`), this file produces the continuous linear operator `A` of the quadratic model:

`inner ℝ (A v) w = BvForm n N δ (e (0, v)) (e (0, w))`,

self-adjoint (`inner ℝ (A v) w = inner ℝ v (A w)`) and injective.  This is precisely the
hypothesis pair consumed by the saddle-point theorem `saddle_point_periodic`, where the quadratic
model of the reference action is `½ inner (A v) v` on the second factor of the split
`ℝ × EuclideanSpace ℝ (Fin M)` (the first factor being the diagonal direction, on which the form
vanishes).

## Proof of nondegeneracy

If `v ≠ 0` had `β v w = 0` for all `w`, then, since `BvForm n N δ z (diagVec n) = 0` for every `z`
and the form is additive and homogeneous in its second argument, `BvForm n N δ (e (0,v)) z' = 0`
for *every* `z'` (writing `z' = e (a, u) = a • e (1,0) + e (0,u)`).  By the kernel computation
`e (0,v) = c • diagVec n`, which forces `v = c • 0 = 0` because
`e (0,v) = c • e (1,0) = e (c • 1, 0)` and `e` is injective.
-/

namespace Work.RPCore.Chain

open Work.RPV
open scoped BigOperators

noncomputable section

/-- For `n = 3N - 1`, `N ≥ 1`, `cos δ ≠ 0` and `sin (N δ) ≠ 0`, the kernel of the reference
bilinear form `BvForm n N δ` is the diagonal line spanned by `diagVec n`.  This is
`refForm_kernel`, restated in the form used below. -/
theorem BvForm_radical_kernel (n N : ℕ) (hN : 1 ≤ N) (hn : n = 3 * N - 1) (δ : ℝ)
    (hcos : Real.cos δ ≠ 0) (hsin : Real.sin ((N : ℝ) * δ) ≠ 0) (z : ChainSp n)
    (hz : ∀ z' : ChainSp n, BvForm n N δ z z' = 0) : ∃ c : ℝ, z = c • diagVec n :=
  refForm_kernel n N hN hn δ hcos hsin z hz

theorem chainModel_operator (n N : ℕ) (hN : 1 ≤ N) (hn : n = 3 * N - 1) (δ : ℝ)
    (hcos : Real.cos δ ≠ 0) (hsin : Real.sin ((N : ℝ) * δ) ≠ 0)
    {M : ℕ} (e : (ℝ × EuclideanSpace ℝ (Fin M)) ≃ₗ[ℝ] Work.RPCore.Chain.ChainSp n)
    (he : e (1, 0) = Work.RPCore.Chain.diagVec n) :
    ∃ A : EuclideanSpace ℝ (Fin M) →L[ℝ] EuclideanSpace ℝ (Fin M),
      (∀ v w, inner ℝ (A v) w = inner ℝ v (A w)) ∧ Function.Injective A ∧
      (∀ v w, inner ℝ (A v) w
        = Work.RPCore.Chain.BvForm n N δ (e (0, v)) (e (0, w))) := by
  obtain ⟨hsymm, hadd, hsmul, hdiag⟩ := BvForm_lin n N δ
  -- left-linearity, deduced from symmetry and right-linearity
  have hadd_left : ∀ z z' z'' : ChainSp n,
      BvForm n N δ (z + z') z'' = BvForm n N δ z z'' + BvForm n N δ z' z'' := by
    intro z z' z''
    rw [hsymm (z + z') z'', hadd z'' z z', hsymm z z'', hsymm z' z'']
  have hsmul_left : ∀ (c : ℝ) (z z' : ChainSp n),
      BvForm n N δ (c • z) z' = c * BvForm n N δ z z' := by
    intro c z z'
    rw [hsymm (c • z) z', hsmul c z' z, hsymm z z']
  -- the restricted form
  let β : EuclideanSpace ℝ (Fin M) → EuclideanSpace ℝ (Fin M) → ℝ :=
    fun v w => BvForm n N δ (e (0, v)) (e (0, w))
  have hcoe : ∀ v v' : EuclideanSpace ℝ (Fin M), e (0, v + v') = e (0, v) + e (0, v') := by
    intro v v'
    have h : ((0 : ℝ), v + v') = ((0 : ℝ), v) + ((0 : ℝ), v') := by ext <;> simp
    rw [h, map_add]
  have hcsmul : ∀ (c : ℝ) (v : EuclideanSpace ℝ (Fin M)), e (0, c • v) = c • e (0, v) := by
    intro c v
    have h : ((0 : ℝ), c • v) = c • ((0 : ℝ), v) := by ext <;> simp
    rw [h, map_smul]
  have hβadd₁ : ∀ v v' w, β (v + v') w = β v w + β v' w := by
    intro v v' w
    dsimp only [β]
    rw [hcoe v v', hadd_left]
  have hβsmul₁ : ∀ (c : ℝ) v w, β (c • v) w = c * β v w := by
    intro c v w
    dsimp only [β]
    rw [hcsmul c v, hsmul_left]
  have hβadd₂ : ∀ v w w', β v (w + w') = β v w + β v w' := by
    intro v w w'
    dsimp only [β]
    rw [hcoe w w', hadd]
  have hβsmul₂ : ∀ (c : ℝ) v w, β v (c • w) = c * β v w := by
    intro c v w
    dsimp only [β]
    rw [hcsmul c w, hsmul]
  have hβsymm : ∀ v w, β v w = β w v := by
    intro v w
    dsimp only [β]
    rw [hsymm]
  -- nondegeneracy of the restricted form
  have hβnondeg : ∀ v, (∀ w, β v w = 0) → v = 0 := by
    intro v hv
    have hv' : ∀ u : EuclideanSpace ℝ (Fin M), BvForm n N δ (e (0, v)) (e (0, u)) = 0 :=
      fun u => hv u
    have hz : ∀ z' : ChainSp n, BvForm n N δ (e (0, v)) z' = 0 := by
      intro z'
      obtain ⟨⟨a, u⟩, hu⟩ := e.surjective z'
      rw [← hu]
      have hsplit : (a, u) = a • ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin M))) + (0, u) := by
        ext <;> simp
      calc BvForm n N δ (e (0, v)) (e (a, u))
          = BvForm n N δ (e (0, v)) (e (a • ((1 : ℝ), 0) + (0, u))) := by rw [hsplit]
        _ = BvForm n N δ (e (0, v)) (a • e ((1 : ℝ), 0) + e (0, u)) := by
              rw [map_add, map_smul]
        _ = a * BvForm n N δ (e (0, v)) (e ((1 : ℝ), 0))
              + BvForm n N δ (e (0, v)) (e (0, u)) := by rw [hadd, hsmul]
        _ = a * 0 + 0 := by rw [he, hdiag, hv' u]
        _ = 0 := by ring
    obtain ⟨c, hc⟩ := BvForm_radical_kernel n N hN hn δ hcos hsin (e (0, v)) hz
    have h2 : e (0, v) = e (c • (1 : ℝ), 0) := by
      rw [hc, ← he, ← map_smul]
      congr 1
      ext <;> simp
    have h3 : (0, v) = (c • (1 : ℝ), (0 : EuclideanSpace ℝ (Fin M))) := e.injective h2
    simpa using congrArg Prod.snd h3
  obtain ⟨A, hAsa, hAinj, hArep⟩ :=
    selfAdjointRep β hβadd₁ hβsmul₁ hβadd₂ hβsmul₂ hβsymm hβnondeg
  exact ⟨A, hAsa, hAinj, fun v w => by simpa only [β] using hArep v w⟩

end

end Work.RPCore.Chain
