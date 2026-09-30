import Mathlib
import Submission.Work.Serre.serreC0KillHomologySets
import Submission.Work.Serre.Wedge.shellHomotopyEquiv
import Submission.Work.Cohomology.sphereHomologyZero
import Submission.Work.Cohomology.sphereHomologyTop
import Submission.Work.Cohomology.isZero_homology_of_homotopyEquiv
import Submission.Work.Cohomology.homologyContractible
import Submission.Work.RatHurewicz.AttachPush.CellInterior
import Submission.Work.Serre.killShellIsZeroHomologyOfPieces

set_option synthInstance.maxHeartbeats 400000

/-!
# `serreC0KillShellHomology`: the shell pieces of the cell attachment

This file proves the three point-set/homological facts about the covering `KillU ∪ KillV` of
`KillX f = attachCells n Y ι f` that the computation of `H_{n+1}(KillX f)` needs:

* **the shell pieces are homeomorphic to the model shell.**  The `i`-th shell piece
  `KillQ f i = cellImg f i (cellShellSet n (1/4) (1/2))` is the image of the model shell
  `{1/4 < ‖x‖ < 1/2}` under the characteristic map of the `i`-th cell, and the characteristic map
  restricts to a homeomorphism on every subset of the open model cell (`ks_cellImgHomeo`).

* **`H_n(KillZ f) = 0`.**  `KillZ f = KillU f ∩ KillV f` is the union of the pairwise disjoint open
  shell pieces `KillQ f i`, each of which is homeomorphic to the model shell, hence homotopy
  equivalent to `S^{n+1}` (`Work.Serre.Wedge.shellHomotopyEquiv`); as `n ≥ 1`, `H_n(S^{n+1}) = 0`
  (`Work.Cohomology.sphereHomologyZero`).  Vanishing is preserved by disjoint-union additivity
  (`Work.Serre.killShellIsZeroHomologyOfPieces`).

* **`H_{n+1}(KillV f) = 0`.**  `KillV f` is the union of the pairwise disjoint open pieces
  `cellImg f i (cellOpenBallSet n (1/2))`, each homeomorphic to an open ball, hence contractible, so
  its `(n+1)`-st homology vanishes (`Work.Cohomology.homologyContractible`); additivity gives the
  vanishing for the whole of `KillV f`.
-/

set_option maxHeartbeats 1000000

open CategoryTheory CategoryTheory.Limits
open scoped Topology

namespace Work.Serre

noncomputable section

open Work.RatHurewicz

variable {n : ℕ} {Y : Type} [TopologicalSpace Y] {ι : Type}

/-! ## Elementary helpers -/

/-- **The piece of a set over one of its subsets.**  If `B ⊆ A`, the subtype
`{z : A // (z : Z) ∈ B}` is canonically homeomorphic to `B`: the two descriptions of "an element of
`B`" differ only by the redundant membership proof. -/
theorem ks_subtypeOfSubset_homeo {Z : Type} [TopologicalSpace Z] {A B : Set Z} (h : B ⊆ A) :
    Nonempty ({z : ↥A // (z : Z) ∈ B} ≃ₜ ↥B) :=
  ⟨{ toFun := fun z => ⟨z.1.1, z.2⟩
     invFun := fun b => ⟨⟨b.1, h b.2⟩, b.2⟩
     left_inv := fun z => by ext <;> rfl
     right_inv := fun b => by ext <;> rfl
     continuous_toFun :=
       Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) _
     continuous_invFun :=
       Continuous.subtype_mk (Continuous.subtype_mk continuous_subtype_val _) _ }⟩

/-- **Vanishing of singular homology is a homeomorphism invariant** (in the direction
`Z ≅ X` ⟹ `H_k(Z) = 0` ⟹ `H_k(X) = 0`). -/
theorem ks_isZero_homology_of_homeomorph {X Z : Type} [TopologicalSpace X] [TopologicalSpace Z]
    (e : X ≃ₜ Z) (k : ℕ)
    (h : IsZero ((Work.Cohomology.singularChains ℤ (TopCat.of Z)).homology k)) :
    IsZero ((Work.Cohomology.singularChains ℤ (TopCat.of X)).homology k) :=
  Work.Cohomology.isZero_homology_of_homotopyEquiv e.toHomotopyEquiv k h

/-! ## The shell pieces are homeomorphic to the model shell -/

/-- **The characteristic map restricted to a subset of the open model cell is a homeomorphism onto
its image.**  The restriction `cellMap i|_S` is injective because `S` lies in the open cell, and a
continuous section of `cellMap i` over the cell interior
(`Work.RatHurewicz.cellInterior_section`) provides the continuous inverse. -/
theorem ks_cellImgHomeo {n : ℕ} {Y : Type} [TopologicalSpace Y] {ι : Type}
    (f : ι → C(cellSphere n, Y)) (i : ι) (S : Set (cellDisk n)) (hS : S ⊆ cellInner n) :
    Nonempty (↥S ≃ₜ ↥(cellImg f i S)) := by
  classical
  have himg : cellImg f i S ⊆ cellInterior n Y ι f i :=
    fun z ⟨x, hx, hxz⟩ => ⟨x, hS hx, hxz⟩
  obtain ⟨sec, hsec⟩ := cellInterior_section (f := f) i
  have hmem : ∀ z : ↥(cellImg f i S),
      ((sec ⟨z.1, himg z.2⟩ : ↥(cellInner n)) : cellDisk n) ∈ S := by
    intro z
    obtain ⟨x, hxS, hxz⟩ := z.2
    have h2 : cellMap n Y ι f i ((sec ⟨z.1, himg z.2⟩ : ↥(cellInner n)) : cellDisk n)
        = cellMap n Y ι f i ((⟨x, hS hxS⟩ : ↥(cellInner n)) : cellDisk n) := by
      rw [hsec ⟨z.1, himg z.2⟩]
      exact hxz.symm
    have h3 := cellMap_injective_cellInner (f := f) i h2
    exact (congrArg (fun w : ↥(cellInner n) => ((w : cellDisk n))) h3) ▸ hxS
  refine ⟨{ toFun := fun x => ⟨cellMap n Y ι f i (x : cellDisk n), ⟨(x : cellDisk n), x.2, rfl⟩⟩
            invFun := fun z =>
              ⟨((sec ⟨z.1, himg z.2⟩ : ↥(cellInner n)) : cellDisk n), hmem z⟩
            left_inv := ?_
            right_inv := ?_
            continuous_toFun := Continuous.subtype_mk
              ((cellMap n Y ι f i).continuous.comp continuous_subtype_val) _
            continuous_invFun := Continuous.subtype_mk
              ((continuous_subtype_val.comp sec.continuous).comp
                (Continuous.subtype_mk continuous_subtype_val _)) _ }⟩
  · intro x
    apply Subtype.ext
    have h2 : cellMap n Y ι f i
          ((sec ⟨cellMap n Y ι f i (x : cellDisk n), himg ⟨(x : cellDisk n), x.2, rfl⟩⟩ :
            ↥(cellInner n)) : cellDisk n)
        = cellMap n Y ι f i ((⟨(x : cellDisk n), hS x.2⟩ : ↥(cellInner n)) : cellDisk n) := by
      rw [hsec]
    exact congrArg (fun w : ↥(cellInner n) => ((w : cellDisk n)))
      (cellMap_injective_cellInner (f := f) i h2)
  · intro z
    apply Subtype.ext
    exact hsec ⟨z.1, himg z.2⟩

/-- **The shell piece `KillQ f i` is the image of the model shell** under the characteristic map of
the `i`-th cell. -/
theorem ks_KillQ_eq_cellImg_shell (f : ι → C(cellSphere n, Y)) (i : ι) :
    KillQ f i = cellImg f i (cellShellSet n (1/4) (1/2)) := by
  ext z
  rw [mem_KillQ f i z]
  simp only [cellImg, Set.mem_image, mem_cellShellSet]
  exact ⟨fun ⟨x, h1, h2, h3⟩ => ⟨x, ⟨h1, h2⟩, h3⟩,
    fun ⟨x, ⟨h1, h2⟩, h3⟩ => ⟨x, h1, h2, h3⟩⟩

/-! ## The vanishing of the homology of the model pieces -/

/-- **The `n`-th homology of the model shell `{1/4 < ‖x‖ < 1/2}` vanishes.**  The shell is homotopy
equivalent to `S^{n+1}`, whose `n`-th homology vanishes for `n ≥ 1`. -/
theorem ks_isZero_homology_cellShell (hn : 1 ≤ n) :
    IsZero ((Work.Cohomology.singularChains ℤ
      (TopCat.of ↥(cellShellSet n (1/4) (1/2)))).homology n) := by
  obtain ⟨e⟩ := Wedge.shellHomotopyEquiv n (1/4) (1/2) (by norm_num) (by norm_num) (by norm_num)
  exact Work.Cohomology.isZero_homology_of_homotopyEquiv e n
    (Work.Cohomology.sphereHomologyZero (n+1) n (by omega) (by omega) (by omega))

/-- The open model ball of radius `1/2` inside the model cell is the open ball of radius `1/2` of
the ambient Euclidean space. -/
def ks_cellOpenBallHomeo (n : ℕ) :
    ↥(cellOpenBallSet n (1/2)) ≃ₜ ↥(Metric.ball (0 : CellVec n) (1/2 : ℝ)) where
  toFun x := ⟨(x.1 : CellVec n), Metric.mem_ball.mpr (by rw [dist_zero_right]; exact x.2)⟩
  invFun v := ⟨⟨v.1, by
      rw [Metric.mem_closedBall, dist_zero_right]
      have hv : dist (v.1 : CellVec n) 0 < (1/2 : ℝ) := v.2
      rw [dist_zero_right] at hv
      exact le_trans (le_of_lt hv) (by norm_num)⟩,
    by
      have hv : dist (v.1 : CellVec n) 0 < (1/2 : ℝ) := v.2
      rw [dist_zero_right] at hv
      exact hv⟩
  left_inv x := by ext <;> rfl
  right_inv v := by ext <;> rfl
  continuous_toFun := Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) _
  continuous_invFun := Continuous.subtype_mk (Continuous.subtype_mk continuous_subtype_val _) _

/-- **The `(n+1)`-st homology of the open model ball of radius `1/2` vanishes.**  The open ball is
convex, hence contractible. -/
theorem ks_isZero_homology_cellOpenBall (n : ℕ) :
    IsZero ((Work.Cohomology.singularChains ℤ
      (TopCat.of ↥(cellOpenBallSet n (1/2)))).homology (n+1)) := by
  haveI : ContractibleSpace ↥(Metric.ball (0 : EuclideanSpace ℝ (Fin (n+2))) (1/2 : ℝ)) :=
    Convex.contractibleSpace (convex_ball _ _)
      ⟨0, by rw [Metric.mem_ball, dist_zero_right]; norm_num⟩
  exact ks_isZero_homology_of_homeomorph (ks_cellOpenBallHomeo n) (n+1)
    (Work.Cohomology.homologyContractible (n+1) (by omega))

/-! ## The theorem -/

/-- **The shell pieces of the cell attachment, and the homology of `KillZ` and `KillV`.**  For
`n ≥ 1`:

* every shell piece `KillQ f i` is homeomorphic to the model shell
  `cellShellSet n (1/4) (1/2) = {1/4 < ‖x‖ < 1/2} ⊆ D^{n+2}`;
* `H_n(KillZ f) = 0`, where `KillZ f = KillU f ∩ KillV f` is the union of the shell pieces;
* `H_{n+1}(KillV f) = 0`, where `KillV f` is the union of the images of the open balls of radius
  `1/2`. -/
theorem serreC0KillShellHomology {n : ℕ} (hn : 1 ≤ n) {Y : Type} [TopologicalSpace Y] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere n, Y)) :
    (∀ i : ι, Nonempty (↥(Work.Serre.KillQ f i) ≃ₜ ↥(Work.Serre.cellShellSet n (1 / 4) (1 / 2)))) ∧
    CategoryTheory.Limits.IsZero ((Work.Cohomology.singularChains ℤ (TopCat.of ↥(Work.Serre.KillZ f))).homology n) ∧
    CategoryTheory.Limits.IsZero ((Work.Cohomology.singularChains ℤ (TopCat.of ↥(Work.Serre.KillV f))).homology (n + 1)) := by
  classical
  have hShell : ∀ i : ι, Nonempty (↥(KillQ f i) ≃ₜ ↥(cellShellSet n (1/4) (1/2))) := by
    intro i
    obtain ⟨e⟩ := ks_cellImgHomeo f i (cellShellSet n (1/4) (1/2))
      (cellShellSet_subset_cellInner (by norm_num))
    exact ⟨(Homeomorph.setCongr (ks_KillQ_eq_cellImg_shell f i)).trans e.symm⟩
  refine ⟨hShell, ?_, ?_⟩
  · -- the homology of the union of the shell pieces vanishes in degree `n`
    have hopen : ∀ i : ι, IsOpen {z : ↥(KillZ f) | (z : KillX f) ∈ KillQ f i} :=
      fun i => (isOpen_KillQ f i).preimage continuous_subtype_val
    have hdisj : _root_.Pairwise fun i j => Disjoint {z : ↥(KillZ f) | (z : KillX f) ∈ KillQ f i}
        {z : ↥(KillZ f) | (z : KillX f) ∈ KillQ f j} := by
      intro i j hij
      rw [Set.disjoint_left]
      intro z hzi hzj
      exact Set.disjoint_left.mp (disjoint_KillQ f hij) hzi hzj
    have hcover : (⋃ i, {z : ↥(KillZ f) | (z : KillX f) ∈ KillQ f i}) = Set.univ := by
      ext z
      simp only [Set.mem_iUnion, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
      exact Set.mem_iUnion.mp (by rw [← KillZ_eq_iUnion_KillQ]; exact z.2)
    have hvan : ∀ i : ι, IsZero ((Work.Cohomology.singularChains ℤ
        (TopCat.of ↥{z : ↥(KillZ f) | (z : KillX f) ∈ KillQ f i})).homology n) := by
      intro i
      have hsub : KillQ f i ⊆ KillZ f := by
        rw [KillZ_eq_iUnion_KillQ]; exact Set.subset_iUnion _ i
      obtain ⟨e⟩ := ks_cellImgHomeo f i (cellShellSet n (1/4) (1/2))
        (cellShellSet_subset_cellInner (by norm_num))
      exact ks_isZero_homology_of_homeomorph
        ((ks_subtypeOfSubset_homeo hsub).some.trans
          ((Homeomorph.setCongr (ks_KillQ_eq_cellImg_shell f i)).trans e.symm)) n
        (ks_isZero_homology_cellShell hn)
    exact killShellIsZeroHomologyOfPieces _ hopen hdisj hcover n hvan
  · -- the homology of the union of the open balls vanishes in degree `n + 1`
    have hopen : ∀ i : ι, IsOpen {z : ↥(KillV f) |
        (z : KillX f) ∈ cellImg f i (cellOpenBallSet n (1/2))} := by
      intro i
      convert (isOpen_cellMap_image (f := f) (i := i)
        (isOpen_cellOpenBallSet n (1/2))
        (cellOpenBallSet_subset_cellInner (by norm_num))).preimage continuous_subtype_val using 1
      ext z
      simp [cellImg]
    have hdisj : _root_.Pairwise fun i j => Disjoint {z : ↥(KillV f) |
          (z : KillX f) ∈ cellImg f i (cellOpenBallSet n (1/2))}
        {z : ↥(KillV f) | (z : KillX f) ∈ cellImg f j (cellOpenBallSet n (1/2))} := by
      intro i j hij
      rw [Set.disjoint_left]
      intro z hzi hzj
      exact Set.disjoint_left.mp
        (disjoint_cellImg (f := f) hij (cellOpenBallSet_subset_cellInner (by norm_num))) hzi hzj
    have hcover : (⋃ i, {z : ↥(KillV f) |
        (z : KillX f) ∈ cellImg f i (cellOpenBallSet n (1/2))}) = Set.univ := by
      ext z
      simp only [Set.mem_iUnion, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
      exact (mem_cellOpenBallImg (f := f)).mp z.2
    have hvan : ∀ i : ι, IsZero ((Work.Cohomology.singularChains ℤ
        (TopCat.of ↥{z : ↥(KillV f) |
          (z : KillX f) ∈ cellImg f i (cellOpenBallSet n (1/2))})).homology (n+1)) := by
      intro i
      have hsub : cellImg f i (cellOpenBallSet n (1/2)) ⊆ KillV f :=
        fun z hz => Set.mem_iUnion.mpr ⟨i, hz⟩
      obtain ⟨e⟩ := ks_cellImgHomeo f i (cellOpenBallSet n (1/2))
        (cellOpenBallSet_subset_cellInner (by norm_num))
      exact ks_isZero_homology_of_homeomorph ((ks_subtypeOfSubset_homeo hsub).some.trans e.symm)
        (n+1) (ks_isZero_homology_cellOpenBall n)
    exact killShellIsZeroHomologyOfPieces _ hopen hdisj hcover (n+1) hvan

end

end Work.Serre
