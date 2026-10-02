import Mathlib
import Submission.Work.Tubular.DiscManifold.ModelReindex

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Existence of the reindexing of the product model of the normal disc bundle

This file proves `Work.Tubular.DiscManifold.exists_halfModelReindex`: for every `k ≥ 1` there is a
reindexing `HalfModelReindex k` of the model space

  `EuclideanHalfSpace (8 + k) ≃ₜ ℝ^8 × Half (k - 1)`

which puts the **first `k`** coordinates of `ℝ^{8+k}` in the fibre factor `Half (k-1)` (so that the
half-space condition sits in the fibre direction) and the remaining `8` coordinates in the base
factor.

The reindexing is the plain permutation of coordinates: `split` sends `x` to
`((x_{k}, …, x_{k+7}), (x_0, …, x_{k-1}))` and `join` is its inverse.  The half-space condition is
`0 ≤ x 0` on `EuclideanHalfSpace (8+k)` and `0 ≤ b 0` on the fibre factor; since `(split x).2 0`
is the `0`-th coordinate of `x`, the condition transfers in both directions.
-/

open scoped Manifold ContDiff Topology

namespace Work.Tubular.DiscManifold

noncomputable section

set_option autoImplicit false

/-- The index of the ambient space `ℝ^{8+k}` corresponding to the `j`-th *fibre* coordinate: the
first `k` coordinates go to the fibre. -/
private def fibIdx (k : ℕ) [NeZero k] (j : Fin ((k - 1) + 1)) : Fin (8 + k) :=
  ⟨j.val, by have := j.isLt; omega⟩

/-- The index of the ambient space `ℝ^{8+k}` corresponding to the `i`-th *base* coordinate: the
coordinates `k, …, k+7` go to the base. -/
private def baseIdx (k : ℕ) [NeZero k] (i : Fin 8) : Fin (8 + k) :=
  ⟨k + i.val, by have := i.isLt; omega⟩

private lemma baseIdx_ge (k : ℕ) [NeZero k] (i : Fin 8) : k ≤ (baseIdx k i).val := by
  simp [baseIdx]

private lemma fibIdx_lt (k : ℕ) [NeZero k] (j : Fin ((k - 1) + 1)) : j.val < k := by
  have h1 := j.isLt
  have h2 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr (NeZero.ne k)
  omega

private lemma sub_lt_eight (k : ℕ) [NeZero k] (t : Fin (8 + k)) (h : k ≤ t.val) :
    t.val - k < 8 := by
  have ht := t.isLt
  have h' : t.val - k + k < 8 + k := by rwa [Nat.sub_add_cancel h]
  exact Nat.lt_of_add_lt_add_right h'

/-- The "split" of an ambient vector into its base part (`8` coordinates) and its fibre part (the
first `k` coordinates). -/
private def splitLin (k : ℕ) [NeZero k] :
    EuclideanSpace ℝ (Fin (8 + k)) →ₗ[ℝ]
      (EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin ((k - 1) + 1))) where
  toFun x := (WithLp.toLp 2 fun i : Fin 8 => x (baseIdx k i),
              WithLp.toLp 2 fun j : Fin ((k - 1) + 1) => x (fibIdx k j))
  map_add' x y := by
    apply Prod.ext
    · apply WithLp.ofLp_injective; funext i; simp
    · apply WithLp.ofLp_injective; funext j; simp
  map_smul' c x := by
    apply Prod.ext
    · apply WithLp.ofLp_injective; funext i; simp
    · apply WithLp.ofLp_injective; funext j; simp

private lemma splitLin_fst (k : ℕ) [NeZero k] (x : EuclideanSpace ℝ (Fin (8 + k)))
    (i : Fin 8) : ((splitLin k x).1).ofLp i = x.ofLp (baseIdx k i) := rfl

private lemma splitLin_snd (k : ℕ) [NeZero k] (x : EuclideanSpace ℝ (Fin (8 + k)))
    (j : Fin ((k - 1) + 1)) : ((splitLin k x).2).ofLp j = x.ofLp (fibIdx k j) := rfl

private lemma splitLin_snd_zero (k : ℕ) [NeZero k] (x : EuclideanSpace ℝ (Fin (8 + k))) :
    ((splitLin k x).2).ofLp 0 = x.ofLp 0 := rfl

/-- The split, as a continuous linear map. -/
private def splitCLM (k : ℕ) [NeZero k] :
    EuclideanSpace ℝ (Fin (8 + k)) →L[ℝ]
      (EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin ((k - 1) + 1))) :=
  ContinuousLinearMap.mk (splitLin k) (LinearMap.continuous_of_finiteDimensional (splitLin k))

private lemma splitCLM_snd_zero (k : ℕ) [NeZero k] (x : EuclideanSpace ℝ (Fin (8 + k))) :
    ((splitCLM k x).2).ofLp 0 = x.ofLp 0 := splitLin_snd_zero k x

/-- The "join" of a pair (base part, fibre part) into the ambient space. -/
private def joinFun (k : ℕ) [NeZero k]
    (p : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin ((k - 1) + 1))) :
    EuclideanSpace ℝ (Fin (8 + k)) :=
  WithLp.toLp 2 fun t : Fin (8 + k) =>
    if h : t.val < k then p.2 ⟨t.val, by omega⟩
    else p.1 ⟨t.val - k, sub_lt_eight k t (by omega)⟩

private lemma joinFun_apply_lt (k : ℕ) [NeZero k]
    (p : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin ((k - 1) + 1)))
    (t : Fin (8 + k)) (h : t.val < k) : (joinFun k p) t = p.2 ⟨t.val, by omega⟩ := by
  simp only [joinFun, dif_pos h]

private lemma joinFun_apply_ge (k : ℕ) [NeZero k]
    (p : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin ((k - 1) + 1)))
    (t : Fin (8 + k)) (h : k ≤ t.val) :
    (joinFun k p) t = p.1 ⟨t.val - k, sub_lt_eight k t h⟩ := by
  simp only [joinFun, dif_neg (not_lt.mpr h)]

/-- The join, as a linear map. -/
private def joinLin (k : ℕ) [NeZero k] :
    (EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin ((k - 1) + 1))) →ₗ[ℝ]
      EuclideanSpace ℝ (Fin (8 + k)) where
  toFun := joinFun k
  map_add' p q := by
    apply WithLp.ofLp_injective
    funext t
    by_cases h : t.val < k
    · simp [joinFun, h]
    · simp [joinFun, h]
  map_smul' c p := by
    apply WithLp.ofLp_injective
    funext t
    by_cases h : t.val < k
    · simp [joinFun, h]
    · simp [joinFun, h]

private lemma joinLin_lt (k : ℕ) [NeZero k]
    (p : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin ((k - 1) + 1)))
    (t : Fin (8 + k)) (h : t.val < k) :
    ((joinLin k p).ofLp) t = (p.2).ofLp ⟨t.val, by omega⟩ := by
  change (joinFun k p) t = _
  exact joinFun_apply_lt k p t h

private lemma joinLin_ge (k : ℕ) [NeZero k]
    (p : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin ((k - 1) + 1)))
    (t : Fin (8 + k)) (h : k ≤ t.val) :
    ((joinLin k p).ofLp) t = (p.1).ofLp ⟨t.val - k, sub_lt_eight k t h⟩ := by
  change (joinFun k p) t = _
  exact joinFun_apply_ge k p t h

private lemma joinLin_zero (k : ℕ) [NeZero k]
    (p : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin ((k - 1) + 1))) :
    ((joinLin k p).ofLp) 0 = (p.2).ofLp 0 := by
  rw [joinLin_lt k p 0 (Nat.pos_of_ne_zero (NeZero.ne k))]
  rfl

/-- `join` is a left inverse of `split`. -/
private lemma joinLin_splitLin (k : ℕ) [NeZero k] (x : EuclideanSpace ℝ (Fin (8 + k))) :
    joinLin k (splitLin k x) = x := by
  apply WithLp.ofLp_injective
  funext t
  by_cases h : t.val < k
  · rw [joinLin_lt k (splitLin k x) t h, splitLin_snd]
    exact congrArg (fun j => x.ofLp j) (Fin.ext rfl)
  · have hle : k ≤ t.val := by omega
    rw [joinLin_ge k (splitLin k x) t hle, splitLin_fst]
    exact congrArg (fun j => x.ofLp j) (Fin.ext (by simp [baseIdx]; omega))

/-- `split` is a left inverse of `join`. -/
private lemma splitLin_joinLin (k : ℕ) [NeZero k]
    (p : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin ((k - 1) + 1))) :
    splitLin k (joinLin k p) = p := by
  apply Prod.ext
  · apply WithLp.ofLp_injective
    funext i
    rw [splitLin_fst, joinLin_ge k p (baseIdx k i) (baseIdx_ge k i)]
    exact congrArg (fun j => p.1.ofLp j) (Fin.ext (by simp [baseIdx]))
  · apply WithLp.ofLp_injective
    funext j
    rw [splitLin_snd, joinLin_lt k p (fibIdx k j) (fibIdx_lt k j)]
    exact congrArg (fun j => p.2.ofLp j) (Fin.ext rfl)

/-- The join, as a continuous linear map. -/
private def joinCLM (k : ℕ) [NeZero k] :
    (EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin ((k - 1) + 1))) →L[ℝ]
      EuclideanSpace ℝ (Fin (8 + k)) :=
  ContinuousLinearMap.mk (joinLin k) (LinearMap.continuous_of_finiteDimensional (joinLin k))

private lemma joinCLM_zero (k : ℕ) [NeZero k]
    (p : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin ((k - 1) + 1))) :
    ((joinCLM k p).ofLp) 0 = (p.2).ofLp 0 := joinLin_zero k p

private lemma joinCLM_splitCLM (k : ℕ) [NeZero k] (x : EuclideanSpace ℝ (Fin (8 + k))) :
    joinCLM k (splitCLM k x) = x := joinLin_splitLin k x

private lemma splitCLM_joinCLM (k : ℕ) [NeZero k]
    (p : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin ((k - 1) + 1))) :
    splitCLM k (joinCLM k p) = p := splitLin_joinLin k p

/-- The reindexing homeomorphism. -/
private def reindexHomeo (k : ℕ) [NeZero k] :
    EuclideanHalfSpace (8 + k) ≃ₜ
      (EuclideanSpace ℝ (Fin 8) × EuclideanHalfSpace ((k - 1) + 1)) where
  toFun x :=
    ((splitCLM k x.val).1, ⟨(splitCLM k x.val).2, by
      have h := x.property
      rwa [← splitCLM_snd_zero] at h⟩)
  invFun p :=
    ⟨joinCLM k (p.1, p.2.val), by
      have h := p.2.property
      rw [show ((joinCLM k (p.1, p.2.val)).ofLp) 0 = (p.2.val).ofLp 0 from
        joinCLM_zero k (p.1, p.2.val)]
      exact h⟩
  left_inv x := by
    apply Subtype.ext
    exact joinCLM_splitCLM k x.val
  right_inv p := by
    have h1 : (splitCLM k (joinCLM k (p.1, p.2.val))).1 = p.1 :=
      congrArg Prod.fst (splitCLM_joinCLM k (p.1, p.2.val))
    have h2 : (splitCLM k (joinCLM k (p.1, p.2.val))).2 = p.2.val :=
      congrArg Prod.snd (splitCLM_joinCLM k (p.1, p.2.val))
    exact Prod.ext h1 (Subtype.ext h2)
  continuous_toFun := by
    apply Continuous.prodMk
    · exact continuous_fst.comp ((splitCLM k).continuous.comp continuous_subtype_val)
    · exact Continuous.subtype_mk
        (continuous_snd.comp ((splitCLM k).continuous.comp continuous_subtype_val))
        (fun x => by
          show 0 ≤ ((splitCLM k x.val).2).ofLp 0
          have h := x.property
          rw [show ((splitCLM k x.val).2).ofLp 0 = x.val.ofLp 0 from splitCLM_snd_zero k x.val]
          exact h)
  continuous_invFun := by
    exact Continuous.subtype_mk
      ((joinCLM k).continuous.comp
        (Continuous.prodMk continuous_fst (continuous_subtype_val.comp continuous_snd)))
      (fun p => by
        show 0 ≤ ((joinCLM k (p.1, p.2.val)).ofLp) 0
        have h := p.2.property
        rw [show ((joinCLM k (p.1, p.2.val)).ofLp) 0 = (p.2.val).ofLp 0 from
          joinCLM_zero k (p.1, p.2.val)]
        exact h)

/-- **Existence of the reindexing of the product model of the normal disc bundle.** -/
theorem exists_halfModelReindex (k : ℕ) [NeZero k] :
    Nonempty (Work.Tubular.DiscManifold.HalfModelReindex k) :=
  ⟨{ Λ := reindexHomeo k
     split := splitCLM k
     join := joinCLM k
     split_snd_zero := fun x => splitCLM_snd_zero k x
     Λ_fst := fun _ => rfl
     Λ_snd_val := fun _ => rfl
     Λ_symm_val := fun _ _ => rfl }⟩

end

end Work.Tubular.DiscManifold
