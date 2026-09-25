import Mathlib
import Submission.NK.CFTLib.Arl.Defs
import Submission.NK.GlobalCFT.Norm.globalCFT_normIdeleFun_principalIdele

open scoped NumberField.LiesOver

namespace NK.CFTLib.Arl

/-- The real number `ringEquivRealOfIsReal hv x`, seen inside `ℂ`, is the image of `x` under the
embedding `extensionEmbedding v`.  This is the dictionary that turns positivity of an element of
`v.Completion` (as expressed by `PosAtReal`) into a statement about `extensionEmbedding v`. -/
lemma ofReal_ringEquivRealOfIsReal {K : Type*} [Field K] {v : NumberField.InfinitePlace K}
    (hv : v.IsReal) (x : v.Completion) :
    ((NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hv x : ℝ) : ℂ)
      = NumberField.InfinitePlace.Completion.extensionEmbedding v x := by
  rw [NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal_apply,
      NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply]

/-- **Positivity of local norms at archimedean places.**  Let `v` be an infinite place of `K` and
`w | v` an infinite place of `L`.  If a unit `u` of `L_w` is positive at `w` (in the sense of
`NK.CFTLib.Arl.PosAtReal`, which is vacuous when `w` is complex), then its local norm
`N_{L_w/K_v} u` is positive at `v`.

For `v` complex this is vacuous; for `v` real and `w` real the local norm is the identity (up to
the ring isomorphisms `v.Completion ≃+* ℝ`, `w.Completion ≃+* ℝ`); for `v` real and `w` complex the
norm is `z ↦ z * conj z = |z|^2 > 0`.

Suggested proof: use `NK.GlobalCFT.Norm.factor_real_real` and
`NK.GlobalCFT.Norm.factor_real_complex` (which compute `extensionEmbedding v (N z)` as
`extensionEmbedding w z`, resp. `Complex.normSq (extensionEmbedding w z)`), together with
`NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply` and
`NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal_apply` to translate `PosAtReal` into a
positivity statement about `extensionEmbeddingOfIsReal`. -/
theorem posAtReal_localNormInfinite {K L : Type*} [Field K] [Field L] [Algebra K L]
    (v : NumberField.InfinitePlace K) (w : NumberField.InfinitePlace L) [hwv : w.LiesOver v]
    (u : w.Completionˣ) (hu : NK.CFTLib.Arl.PosAtReal w u) :
    NK.CFTLib.Arl.PosAtReal v (NK.GlobalCFT.Place.localNormInfinite w v u) := by
  intro hv
  have hcoe : ((NK.GlobalCFT.Place.localNormInfinite w v u : v.Completion))
      = Algebra.norm v.Completion (u : w.Completion) := by
    simp [NK.GlobalCFT.Place.localNormInfinite, Units.coe_map]
  rw [hcoe]
  rcases w.isReal_or_isComplex with hwR | hwC
  · -- `v` and `w` both real: the local norm is the identity after identifying with `ℝ`.
    have key : NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hv
        (Algebra.norm v.Completion (u : w.Completion))
        = NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hwR (u : w.Completion) := by
      apply Complex.ofReal_injective
      rw [ofReal_ringEquivRealOfIsReal hv, ofReal_ringEquivRealOfIsReal hwR,
        NK.GlobalCFT.Norm.factor_real_real hv hwR (u : w.Completion)]
    rw [key]
    exact hu hwR
  · -- `v` real, `w` complex: the local norm is `z ↦ normSq z`, and `u ≠ 0`.
    have key : NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hv
        (Algebra.norm v.Completion (u : w.Completion))
        = Complex.normSq (NumberField.InfinitePlace.Completion.extensionEmbedding w
            (u : w.Completion)) := by
      apply Complex.ofReal_injective
      rw [ofReal_ringEquivRealOfIsReal hv,
        NK.GlobalCFT.Norm.factor_real_complex hv hwC (u : w.Completion)]
    rw [key]
    refine Complex.normSq_pos.mpr fun h0 => Units.ne_zero u ?_
    exact (NumberField.InfinitePlace.Completion.extensionEmbedding w).injective
      (by rw [h0, map_zero])

end NK.CFTLib.Arl
