-- Copied verbatim from `Submission/Work/Thom/subsingleton_relComplex_cube.lean`, with the import of
-- `Submission.Work.Thom.nonempty_thomClass_of_disjoint_cover` replaced by
-- `Submission.Work.Thom.Relocate.HonestFMV` (the same declarations, without the `prod_sphere_aux`
-- island, which is incompatible with `Submission/Work/TangentClasses/` and
-- `Submission/Work/Thom/Interface.lean`).
import Mathlib
import Submission.Work.Thom.EucCube
import Submission.Work.Thom.CubeSetup
import Submission.Work.Thom.homotopyRetractVanishing
import Submission.Work.Cohomology.relCohMV_honest_les
import Submission.Work.Cohomology.subsingleton_relCohomology_of_open_subset
import Submission.Work.Thom.subsingleton_overlapCoh_cube
import Submission.Work.Thom.subsingleton_pieceCoh_cube
import Submission.Work.Thom.Relocate.HonestFMV

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# `H^m(W × [-1,1]ⁿ, W × ∂[-1,1]ⁿ) = 0` for `m < n`

The proof is the Mayer–Vietoris induction described in `Submission/Work/Thom/CUBE_PLAN.md`: the cube
`euCube (n+1)` is covered by the two open pieces `Cube.pieceTop n W` (last coordinate `> -1/2`) and
`Cube.pieceBot n W` (last coordinate `< 1/2`), and one runs the honest relative
Mayer–Vietoris sequence of the pair `(X, A)` for `X = W × euCube (n+1)` and
`A = W × ∂euCube (n+1)`.

* In degree `0` the Mayer–Vietoris map `honestF` is injective into a biproduct of two vanishing
  groups.
* In degree `k+1` the middle term of the sequence vanishes as well, so the connecting map
  `honestDelta : H^k(overlap) → H^{k+1}(X,A)` is surjective; its source vanishes by the induction
  hypothesis, since the overlap `{|last| < 1/2}` splits off the last coordinate as the product
  `(W × (-1/2,1/2)) × euCube n` (`Cube.overlapCoh`).

The two vanishing statements for the pieces and for the overlap are the lemmas
`Work.Thom.subsingleton_pieceCoh_cube` and `Work.Thom.subsingleton_overlapCoh_cube`.
-/

set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits
open Work.Cohomology (pdCoh pdCohSub pdCohBiprod honestF honestDelta honest_exact₁)

namespace Work.Thom

/-- The induction step of `Work.Thom.subsingleton_relComplex_cube`, with the space `W` and its
topology made explicit arguments so that strong induction applies. -/
private theorem cube_vanishing_aux : ∀ n : ℕ, ∀ (W : Type) (_ : TopologicalSpace W) (m : ℕ),
    m < n → Subsingleton ((Work.Cohomology.relComplex ℤ (TopCat.of (W × ↥(euCube n)))
      {p : W × ↥(euCube n) | (p.2 : Fin n → ℝ) ∈ euCubeBdry n}).homology m) := by
  intro n
  refine Nat.strong_induction_on n ?_
  intro n ih W instW m hm
  rcases n with _ | u
  · exact absurd hm (Nat.not_lt_zero m)
  · let X : TopCat := TopCat.of (W × ↥(euCube (u+1)))
    let A : Set X := {p : W × ↥(euCube (u+1)) | (p.2 : Fin (u+1) → ℝ) ∈ euCubeBdry (u+1)}
    let U : Set X := {p : W × ↥(euCube (u+1)) |
      (p.2 : Fin (u+1) → ℝ) (Fin.last u) ∈ Set.Ioi (-1/2)}
    let V : Set X := {p : W × ↥(euCube (u+1)) |
      (p.2 : Fin (u+1) → ℝ) (Fin.last u) ∈ Set.Iio (1/2)}
    -- the two pieces are open and cover the cube
    have hU : IsOpen U := Cube.isOpen_pieceTop u W
    have hV : IsOpen V := Cube.isOpen_pieceBot u W
    have hcov : U ∪ V = Set.univ := Cube.pieceTop_union_pieceBot u W
    -- the induction hypothesis, in the form required by `subsingleton_overlapCoh_cube`
    have hIH : ∀ (Z : Type) [TopologicalSpace Z] (m : ℕ), m < u →
        Subsingleton ((Work.Cohomology.relComplex ℤ (TopCat.of (Z × ↥(euCube u)))
          {p : Z × ↥(euCube u) | (p.2 : Fin u → ℝ) ∈ euCubeBdry u}).homology m) :=
      fun Z instZ m hm => ih u (Nat.lt_succ_self u) Z instZ m hm
    rcases m with _ | k
    · -- degree `0`: `honestF` is injective into a vanishing biproduct
      have hinj := honestF_injective_zero X A U V hU hV hcov
      haveI : Subsingleton (pdCohSub X A U 0) :=
        subsingleton_pieceCoh_cube u W (Set.Ioi (-1/2)) 1 (by norm_num) (by norm_num)
          Cube.convex_Ioi_half Cube.unit_Ioi_half 0
      haveI : Subsingleton (pdCohSub X A V 0) :=
        subsingleton_pieceCoh_cube u W (Set.Iio (1/2)) (-1) (by norm_num) (by norm_num)
          Cube.convex_Iio_half Cube.unit_Iio_half 0
      have hzU : IsZero (pdCohSub X A U 0) := ModuleCat.isZero_of_subsingleton _
      have hzV : IsZero (pdCohSub X A V 0) := ModuleCat.isZero_of_subsingleton _
      have hz : IsZero (pdCohBiprod X A U V 0) := (biprod_isZero_iff _ _).mpr ⟨hzU, hzV⟩
      haveI : Subsingleton (pdCohBiprod X A U V 0) := ModuleCat.subsingleton_of_isZero hz
      exact ⟨fun a b => hinj (Subsingleton.elim _ _)⟩
    · -- degree `k+1`: the connecting map of the sequence is surjective out of a vanishing overlap
      haveI : Subsingleton (pdCohSub X A U (k+1)) :=
        subsingleton_pieceCoh_cube u W (Set.Ioi (-1/2)) 1 (by norm_num) (by norm_num)
          Cube.convex_Ioi_half Cube.unit_Ioi_half (k+1)
      haveI : Subsingleton (pdCohSub X A V (k+1)) :=
        subsingleton_pieceCoh_cube u W (Set.Iio (1/2)) (-1) (by norm_num) (by norm_num)
          Cube.convex_Iio_half Cube.unit_Iio_half (k+1)
      have hzU : IsZero (pdCohSub X A U (k+1)) := ModuleCat.isZero_of_subsingleton _
      have hzV : IsZero (pdCohSub X A V (k+1)) := ModuleCat.isZero_of_subsingleton _
      have hz : IsZero (pdCohBiprod X A U V (k+1)) := (biprod_isZero_iff _ _).mpr ⟨hzU, hzV⟩
      have hF0 : honestF X A U V (k+1) = 0 := IsZero.eq_zero_of_tgt hz _
      have hex := honest_exact₁ X A U V hU hV hcov k
      have hker : LinearMap.range (ModuleCat.Hom.hom
          (honestDelta X A U V hU hV hcov k)) = ⊤ := by
        have h := ShortComplex.Exact.moduleCat_range_eq_ker hex
        change LinearMap.range (ModuleCat.Hom.hom (honestDelta X A U V hU hV hcov k))
          = LinearMap.ker (ModuleCat.Hom.hom (honestF X A U V (k+1))) at h
        rw [hF0, ModuleCat.hom_zero, LinearMap.ker_zero] at h
        exact h
      have hsurj : Function.Surjective (ModuleCat.Hom.hom
          (honestDelta X A U V hU hV hcov k)) := LinearMap.range_eq_top.mp hker
      haveI : Subsingleton (pdCohSub X A (U ∩ V) k) :=
        subsingleton_overlapCoh_cube u W hIH k (by omega)
      exact ⟨fun a b => by
        obtain ⟨x, rfl⟩ := hsurj a
        obtain ⟨y, rfl⟩ := hsurj b
        rw [Subsingleton.elim x y]⟩

theorem subsingleton_relComplex_cube (n : ℕ) (W : Type) [TopologicalSpace W] (m : ℕ) (hm : m < n) :
    Subsingleton ((Work.Cohomology.relComplex ℤ (TopCat.of (W × ↥(euCube n)))
      {p : W × ↥(euCube n) | (p.2 : Fin n → ℝ) ∈ euCubeBdry n}).homology m) :=
  cube_vanishing_aux n W inferInstance m hm

end Work.Thom
