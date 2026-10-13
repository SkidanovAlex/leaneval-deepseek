import Mathlib
import Submission.Work.DSMX0U.towerModelTopQuasiIso
import Submission.Work.DSMX0U.quasiIsoAt_towerModelMap_mid
import Submission.Work.DSMX0U.quasiIsoAt_towerModelMap_gt

/-!
# `Work.DSMX0U.quasiIso_towerModelMap2`

The model complex `P = towerModel hstep M s₀` (`Submission/Work/DSMX0U/ModelF.lean`) is the tower
of cells extended along the embedding `embeddingUpIntLE M`: the level `k` of the tower sits in
cohomological degree `levelDeg M k - 1 = M - k` and `P` vanishes above `M`.  This file proves: a
chain map `φ : P ⟶ C` whose components in the degrees of the levels are the maps `(tower k).φ` of
the cells (transported along the canonical isomorphism `towerModelXIso`) is a quasi-isomorphism,
provided that

* `C` has vanishing cohomology above a bound `N ≤ M` (`hN`, `hMN`),
* the base cell of the tower has zero differential (`hd0`).

The verification is degreewise.

* Above `M` the model vanishes (`towerModel_isZero_of_gt`) and `C` has vanishing cohomology
  (`hN`), so both homology objects vanish; this is `quasiIsoAt_towerModelMap_gt`
  (`Submission/Work/DSMX0U/quasiIsoAt_towerModelMap_gt.lean`).
* In the degree `levelDeg M (k+1) - 1 = M - k - 1` of a level `k + 1 ≥ 1` the short complex of `P`
  is, through the isomorphisms `towerModelXIso`, the short complex `G_{k+2} ⟶ G_{k+1} ⟶ G_k` of
  the tower, the short complex of `C` is the concrete short complex `scC` of
  `Submission/Work/DSMX0U/towerMap_quasiIsoAt_succ.lean`, and the induced map of short complexes
  is `psi` of that file, whose quasi-isomorphism is proved there; this is
  `quasiIsoAt_towerModelMap_mid` (`Submission/Work/DSMX0U/quasiIsoAt_towerModelMap_mid.lean`).
* In the remaining degree `M = levelDeg M 0 - 1` the short complex of `P` is `G_1 ⟶ G_0 ⟶ 0`, and
  the hypothesis `hd0` says that the differential of the base cell is zero: the induced map on
  homology is surjective by `Cell.hσ` of the base cell (the generators of `G_0` hit the cohomology
  modulo boundaries) and injective because a cycle of `G_0` whose image is a boundary lies in
  `Cell.K (tower 0) = range (towerD 0)` (by `hd0` and `tower_range_d`).  This is
  `TowerModelMapTop.quasiIsoAt_towerModelMap_top`, in
  `Submission/Work/DSMX0U/towerModelTopQuasiIso.lean` (whose setup is in
  `Submission/Work/DSMX0U/towerModelTopSetup.lean`).

The only degree bookkeeping left is the passage from `i ≤ M`, `i ≠ M` to a level `k + 1` such that
`i = levelDeg M (k + 1) - 1`, which is `exists_levelDeg_succ_eq_of_lt`.
-/

namespace Work.DSMX0U

open CategoryTheory Limits

universe a

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

variable {A : Type a} [CommRing A]
variable {C : CochainComplex (ModuleCat.{a} A) ℤ} {c₀ : ModuleCat.of A A ⟶ C.X 0}

/-- For `i < M` the degree `i` is the degree `levelDeg M (k + 1) - 1` of a level `k + 1`. -/
theorem exists_levelDeg_succ_eq_of_lt (M i : ℤ) (h : i < M) :
    ∃ k : ℕ, levelDeg M (k + 1) - 1 = i := by
  refine ⟨(M - 1 - i).toNat, ?_⟩
  rw [levelDeg_cur]
  have h2 : ((M - 1 - i).toNat : ℤ) = M - 1 - i := Int.toNat_of_nonneg (by omega)
  omega

/-- The model chain map `towerModel hstep M s₀ ⟶ C` with the prescribed components is a
quasi-isomorphism. -/
theorem quasiIso_towerModelMap2 {A : Type a} [CommRing A]
    {C : CochainComplex (ModuleCat.{a} A) ℤ} {c₀ : ModuleCat.of A A ⟶ C.X 0}
    (hstep : ∀ (q : ℤ) (s : Work.DSMX0U.Cell A C c₀ q), Work.DSMX0U.StepData A s)
    (M : ℤ) (s₀ : Work.DSMX0U.Cell A C c₀ (M + 1))
    (hd0 : Work.DSMX0U.Cell.d A (Work.DSMX0U.tower hstep M s₀ 0) = 0)
    (φ : Work.DSMX0U.towerModel hstep M s₀ ⟶ C)
    (hφ : ∀ k : ℕ, φ.f (Work.DSMX0U.levelDeg M k - 1) = CategoryTheory.CategoryStruct.comp
        (Work.DSMX0U.towerModelXIso hstep M s₀ k).hom (Work.DSMX0U.Cell.φ A (Work.DSMX0U.tower hstep M s₀ k)))
    (hqi : ∀ k : ℕ, QuasiIsoAt (Work.DSMX0U.towerMap hstep M s₀) (k + 1))
    {N : ℤ} (hN : ∀ i : ℤ, N < i → CategoryTheory.Limits.IsZero (C.homology i))
    (hMN : N ≤ M) :
    QuasiIso φ := by
  rw [quasiIso_iff]
  intro i
  by_cases hMi : M < i
  · exact quasiIsoAt_towerModelMap_gt hstep M s₀ φ hN hMN hMi
  · rw [not_lt] at hMi
    rcases lt_or_eq_of_le hMi with hlt | heq
    · obtain ⟨k, hk⟩ := exists_levelDeg_succ_eq_of_lt M i hlt
      rw [← hk]
      exact quasiIsoAt_towerModelMap_mid hstep M s₀ φ hφ k
    · have htop := TowerModelMapTop.quasiIsoAt_towerModelMap_top hstep M s₀ hd0 φ hφ
      rw [show levelDeg M 0 - 1 = i from by rw [levelDeg_zero, ← heq]; ring] at htop
      exact htop

end Work.DSMX0U
