import Mathlib
import Submission.Work.Smooth.JordanSeparation.plApprox
import Submission.Work.Smooth.JordanSeparation.plCutAssemble

/-!
# Casts of composed paths, and casts of joins

* `cast_trans_general` — `Path.cast` distributes over `Path.trans`;
* `joinNat_cast` — if `F k` is the `Path.cast` of `G k` along pointwise endpoint equalities, then
  `joinNat F j` is the `Path.cast` of `joinNat G j`.

These are the transport lemmas needed to move between the loop of a lattice walk and the pieces of
its `joinNat` decomposition (see `PLAN_GRID_CRUX.md`).
-/

namespace Work.Smooth.JordanSeparation

open Set Metric

noncomputable section

/-- `Path.cast` distributes over `Path.trans`. -/
theorem cast_trans_general {X : Type*} [TopologicalSpace X] {x y z x' y' z' : X}
    (A : Path x y) (B : Path y z) (hx : x' = x) (hy : y' = y) (hz : z' = z) :
    Path.cast (A.trans B) hx hz = (Path.cast A hx hy).trans (Path.cast B hy hz) := by
  apply Path.ext
  funext t
  rw [congrFun (Path.cast_coe (A.trans B) hx hz) t, Path.trans_apply, Path.trans_apply]
  by_cases ht : (t : ℝ) ≤ 1 / 2
  · rw [dif_pos ht, dif_pos ht]
    exact congrFun (Path.cast_coe A hx hy) _
  · rw [dif_neg ht, dif_neg ht]
    exact congrFun (Path.cast_coe B hy hz) _

/-- If `F k` is the `Path.cast` of `G k` along the pointwise endpoint equalities `h`, then
`joinNat F j` is the `Path.cast` of `joinNat G j`. -/
theorem joinNat_cast {X : Type*} [TopologicalSpace X] {p q : ℕ → X} (h : ∀ k, p k = q k)
    (F : ∀ k, Path (p k) (p (k + 1))) (G : ∀ k, Path (q k) (q (k + 1)))
    (hFG : ∀ k, F k = Path.cast (G k) (h k) (h (k + 1))) :
    ∀ j, joinNat F j = Path.cast (joinNat G j) (h 0) (h j)
  | 0 => by
    rw [joinNat, joinNat]
    apply Path.ext
    funext t
    rw [Path.cast_coe]
    exact congrArg (fun z => Path.refl z t) (h 0)
  | j + 1 => by
    rw [show joinNat F (j + 1) = (joinNat F j).trans (F j) from rfl,
      show joinNat G (j + 1) = (joinNat G j).trans (G j) from rfl,
      joinNat_cast h F G hFG j, hFG j,
      cast_trans_general (joinNat G j) (G j) (h 0) (h j) (h (j + 1))]


/-- Bounded version of `joinNat_cast`: the endpoint equalities are only needed up to the length. -/
theorem joinNat_cast_bound {X : Type*} [TopologicalSpace X] {p q : ℕ → X} {J : ℕ}
    (h : ∀ k, k ≤ J → p k = q k)
    (F : ∀ k, Path (p k) (p (k + 1))) (G : ∀ k, Path (q k) (q (k + 1)))
    (hFG : ∀ k (hk : k < J), F k = Path.cast (G k) (h k (le_of_lt hk))
      (h (k + 1) (Nat.succ_le_of_lt hk))) :
    ∀ j, (hj : j ≤ J) → joinNat F j
      = Path.cast (joinNat G j) (h 0 (Nat.zero_le J)) (h j hj) := by
  intro j
  induction j with
  | zero =>
    intro hj
    rw [joinNat, joinNat]
    apply Path.ext
    funext t
    rw [Path.cast_coe]
    exact congrArg (fun z => Path.refl z t) (h 0 (Nat.zero_le J))
  | succ j ih =>
    intro hj
    have hj' : j ≤ J := by omega
    have hjJ : j < J := by omega
    rw [show joinNat F (j + 1) = (joinNat F j).trans (F j) from rfl,
      show joinNat G (j + 1) = (joinNat G j).trans (G j) from rfl,
      ih hj', hFG j hjJ,
      cast_trans_general (joinNat G j) (G j) (h 0 (Nat.zero_le J)) (h j hj')
        (h (j + 1) hj)]


/-- A `Path.cast` along reflexivity-type endpoint equalities is the original path. -/
theorem Path.cast_self {X : Type*} [TopologicalSpace X] {x y : X} (γ : Path x y)
    (hx : x = x) (hy : y = y) : Path.cast γ hx hy = γ := by
  apply Path.ext
  funext t
  rw [Path.cast_coe]

/-- Two successive `Path.cast`s compose. -/
theorem Path.cast_cast {X : Type*} [TopologicalSpace X] {x y x' y' x'' y'' : X} (γ : Path x y)
    (hx : x' = x) (hy : y' = y) (hx' : x'' = x') (hy' : y'' = y') :
    Path.cast (Path.cast γ hx hy) hx' hy' = Path.cast γ (hx'.trans hx) (hy'.trans hy) := by
  apply Path.ext
  funext t
  rw [Path.cast_coe, Path.cast_coe, Path.cast_coe]

end

end Work.Smooth.JordanSeparation
