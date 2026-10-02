import Mathlib
import Submission.Work.ThomBordism.CofAtlas.Signs
import Submission.Work.PTGeometric.GrRank

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.ThomBordism.CofAtlas

open scoped Manifold ContDiff Topology
open Function Set Topology Manifold Filter ModelWithCorners
open Work.PTGeometric

/-- **An idempotent operator has range equal to its fixed space.**  For `Q : ℝⁿ →L ℝⁿ` with
`Q * Q = Q`, the range of `Q` is the kernel of `id - Q` (the set of fixed vectors of `Q`); this is
`LinearMap.IsIdempotentElem.range_eq_ker` for the underlying linear map. -/
theorem range_toLinearMap_eq_ker_id_sub {n : ℕ} {Q : EndOp n} (h : Q * Q = Q) :
    LinearMap.range Q.toLinearMap = LinearMap.ker (LinearMap.id - Q.toLinearMap) :=
  LinearMap.IsIdempotentElem.range_eq_ker (by
    show Q.toLinearMap * Q.toLinearMap = Q.toLinearMap
    rw [← ContinuousLinearMap.toLinearMap_mul]
    exact congrArg ContinuousLinearMap.toLinearMap h)

/-- **`range (mfderiv v q) = range (e (jx x) q)`.**  Both are the `k`-dimensional fixed space
`{z | P q z = z} = ker (P q - 1) = range (P q)` of the rank-`k` projection `P q`: the first by
`Cof.hlink`, the second because `ℓ (jx x) ∘ e (jx x) q = 1` (`Cof.hℓe`) and `e (jx x) q` is
injective (`Cof.heinj`), using `finrank (range (P q)) = k`
(`Work.PTGeometric.finrank_range_mem_Gr`, `Cof.hPgr`) and equality of finite ranks.
The hypothesis `hq : q ∈ D.src x` is used only through `Cof.src_subset_U`
(`(q : M) ∈ D.U (D.jx x)`). -/
theorem range_mfderiv_v_eq_range_e
    {k n : ℕ} {M : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanHalfSpace ((8 + k) + 1)) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace ((8 + k) + 1)) ((⊤ : ENat) : WithTop ENat) M]
    (D : Work.ThomBordism.CofAtlas.Cof k n M) (x : D.S.Pre) {q : D.S.Pre} (hq : q ∈ D.src x) :
    LinearMap.range (mfderiv (modelWithCornersEuclideanHalfSpace ((8 + k) + 1))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) D.v (q : M)).toLinearMap
      = LinearMap.range (D.e (D.jx x) (q : M)).toLinearMap := by
  -- Everything is done with the explicit codomain `ℝⁿ` (the `TangentSpace` of a vector space is a
  -- non-reducible type synonym, so type class inference needs the ascription).
  have hmain : (LinearMap.range (mfderiv (modelWithCornersEuclideanHalfSpace ((8 + k) + 1))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) D.v (q : M)).toLinearMap
        : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
      = LinearMap.range (D.e (D.jx x) (q : M)).toLinearMap := by
    have hqU : (q : M) ∈ D.U (D.jx x) := D.src_subset_U x hq
    -- The two candidate subspaces.
    have hidem : D.P (q : M) * D.P (q : M) = D.P (q : M) := (D.hPgr (q : M)).2.1
    have hPker := range_toLinearMap_eq_ker_id_sub (n := n) hidem
    have hdim_P : Module.finrank ℝ ↥(LinearMap.range (D.P (q : M)).toLinearMap) = k := by
      simpa using finrank_range_mem_Gr (D.hPgr (q : M))
    -- **The first range is the fixed space of `P q`**, by `hlink`.
    have hset : Set.range (⇑(mfderiv (modelWithCornersEuclideanHalfSpace ((8 + k) + 1))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) D.v (q : M)))
          = {z : EuclideanSpace ℝ (Fin n) | D.P (q : M) z = z} := D.hlink (q : M) q.2
    have key : ∀ z : EuclideanSpace ℝ (Fin n),
        z ∈ (LinearMap.range (mfderiv (modelWithCornersEuclideanHalfSpace ((8 + k) + 1))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) D.v (q : M)).toLinearMap
          : Submodule ℝ (EuclideanSpace ℝ (Fin n))) ↔ D.P (q : M) z = z := by
      intro z
      constructor
      · intro hz
        have hz' : z ∈ Set.range (⇑(mfderiv (modelWithCornersEuclideanHalfSpace ((8 + k) + 1))
            (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) D.v (q : M))) := hz
        rwa [hset] at hz'
      · intro hz
        have hz' : z ∈ Set.range (⇑(mfderiv (modelWithCornersEuclideanHalfSpace ((8 + k) + 1))
            (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) D.v (q : M))) := by
          rw [hset]; exact hz
        obtain ⟨w, hw⟩ := hz'
        exact ⟨w, hw⟩
    have hf : (LinearMap.range (mfderiv (modelWithCornersEuclideanHalfSpace ((8 + k) + 1))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) D.v (q : M)).toLinearMap
          : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
        = LinearMap.ker (LinearMap.id - (D.P (q : M)).toLinearMap) := by
      refine SetLike.ext fun z => ?_
      rw [key z, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply]
      constructor
      · intro h
        rw [sub_eq_zero]; exact h.symm
      · intro h
        exact (sub_eq_zero.mp h).symm
    -- **The second range lies in the fixed space of `P q`**, by `hℓe`.
    have hg : LinearMap.range (D.e (D.jx x) (q : M)).toLinearMap
        ≤ LinearMap.ker (LinearMap.id - (D.P (q : M)).toLinearMap) := by
      intro z hz
      obtain ⟨c, rfl⟩ := hz
      rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
      exact ((D.hℓe (D.jx x) (q : M) hqU c).2).symm
    -- Both are `k`-dimensional.
    have hdim_g : Module.finrank ℝ ↥(LinearMap.range (D.e (D.jx x) (q : M)).toLinearMap) = k := by
      rw [LinearMap.finrank_range_of_inj (f := (D.e (D.jx x) (q : M)).toLinearMap)
        (D.heinj (D.jx x) (q : M) hqU)]
      simp [finrank_euclideanSpace]
    have hle : LinearMap.range (D.e (D.jx x) (q : M)).toLinearMap
        ≤ (LinearMap.range (mfderiv (modelWithCornersEuclideanHalfSpace ((8 + k) + 1))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) D.v (q : M)).toLinearMap
          : Submodule ℝ (EuclideanSpace ℝ (Fin n))) := by
      rw [hf]; exact hg
    refine (Submodule.eq_of_le_of_finrank_eq hle ?_).symm
    rw [hf, ← hPker]
    exact hdim_g.trans hdim_P.symm
  exact hmain

end Work.ThomBordism.CofAtlas
