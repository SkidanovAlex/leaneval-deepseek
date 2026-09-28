import Submission.Work.StemsB.CubeMidIso
import Submission.Work.Cohomology.homology_prod_contractible
import Submission.Work.Cohomology.relComplex_empty_homology_iso

/-!
# The relative homology of `(Iⁿ × Y, ∂Iⁿ × Y)`

Main result of the chapter: for every `n` and every parameter space `Y`,

  `H_{n+j}(Iⁿ × Y, ∂Iⁿ × Y; ℤ) ≅ H_j(Y; ℤ)`   and   `H_m(Iⁿ × Y, ∂Iⁿ × Y; ℤ) = 0`  for `m < n`.

The proof is by induction on `n`, the induction step being the Mayer–Vietoris files of this
directory:

* `Work.StemsB.cubePairStep_iso` (`CubePairStep.lean`) — the relative homology of the `(n+1)`-cube
  pair is that of the middle slab of the cover;
* `Work.StemsB.midRelIso` (`CubeMidIso.lean`) — the middle slab is `Iⁿ × (1/4,3/4) × Y`;
* `Work.Cohomology.homology_prod_contractible` — the factor `(1/4,3/4)` is contractible.

The degree-`0` vanishing needs a separate argument (`Work.StemsB.cubePairZero_isZero`): the first
term of the relative Mayer–Vietoris sequence (the small-chains complex) is killed in degree `0` by
the vanishing of the middle term, through `ShortComplex.ShortExact.exactAt_X₃`.
-/

set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open CategoryTheory CategoryTheory.Limits
open scoped unitInterval

namespace Work.StemsB

noncomputable section

variable {Y : Type} [TopologicalSpace Y]

/-! ## The empty relative set -/

/-- The singular chains of the empty space are a zero object. -/
theorem isZero_singularChains_empty (X : TopCat) :
    IsZero (Work.Cohomology.singularChains ℤ (TopCat.of (∅ : Set X))) := by
  rw [IsZero.iff_id_eq_zero]
  apply HomologicalComplex.hom_ext
  intro k
  rw [HomologicalComplex.id_f, HomologicalComplex.zero_f]
  exact (IsZero.iff_id_eq_zero _).mp (Work.Cohomology.isZero_singularChains_empty_set X k)

/-- The relative chain complex of `(X,∅)` is the absolute chain complex of `X`. -/
theorem relChains_empty_iso (X : TopCat) :
    Nonempty (Work.Cohomology.relChains X (∅ : Set X) ≅ Work.Cohomology.singularChains ℤ X) := by
  have hzero : Work.Cohomology.inclChains X (∅ : Set X) = 0 :=
    (isZero_singularChains_empty X).eq_zero_of_src _
  haveI : IsIso (cokernel.π (Work.Cohomology.inclChains X (∅ : Set X))) :=
    cokernel.π_of_zero hzero
  exact ⟨(asIso (cokernel.π (Work.Cohomology.inclChains X (∅ : Set X)))).symm⟩

/-! ## The degree-zero vanishing -/

/-- **The relative homology of the cube pair vanishes in degree zero.** -/
theorem cubePairZero_isZero (n : ℕ) :
    IsZero ((Work.Cohomology.relChains (CubeSpace (Y := Y) (n+1))
      (cubeBdry (Y := Y) n)).homology 0) := by
  haveI h₂ : IsZero (Work.Cohomology.relMVH₂ (CubeSpace (Y := Y) (n+1)) (cubeBdry (Y := Y) n)
      (slabA (Y := Y) n) (slabB (Y := Y) n) 0) := isZero_relMVH₂_cube (Y := Y) n 0
  have h₁ : Epi (HomologicalComplex.homologyMap
      (Work.Cohomology.relMVShort (CubeSpace (Y := Y) (n+1)) (cubeBdry (Y := Y) n)
        (slabA (Y := Y) n) (slabB (Y := Y) n)).f 0) :=
    h₂.epi (HomologicalComplex.homologyMap
      (Work.Cohomology.relMVShort (CubeSpace (Y := Y) (n+1)) (cubeBdry (Y := Y) n)
        (slabA (Y := Y) n) (slabB (Y := Y) n)).f 0)
  have hex : (Work.Cohomology.relMVShort (CubeSpace (Y := Y) (n+1)) (cubeBdry (Y := Y) n)
      (slabA (Y := Y) n) (slabB (Y := Y) n)).X₃.ExactAt 0 :=
    (Work.Cohomology.relMVShort_shortExact (CubeSpace (Y := Y) (n+1)) (cubeBdry (Y := Y) n)
      (slabA (Y := Y) n) (slabB (Y := Y) n)).exactAt_X₃ 0 h₁
      (fun j hj => absurd hj (by simp [ComplexShape.down]))
  have hz : IsZero (Work.Cohomology.relMVH₃ (CubeSpace (Y := Y) (n+1)) (cubeBdry (Y := Y) n)
      (slabA (Y := Y) n) (slabB (Y := Y) n) 0) :=
    (HomologicalComplex.exactAt_iff_isZero_homology
      (Work.Cohomology.relMVShort (CubeSpace (Y := Y) (n+1)) (cubeBdry (Y := Y) n)
        (slabA (Y := Y) n) (slabB (Y := Y) n)).X₃ 0).mp hex
  exact IsZero.of_iso hz (Work.Cohomology.relMVSmallIso (CubeSpace (Y := Y) (n+1))
    (cubeBdry (Y := Y) n) (slabA (Y := Y) n) (slabB (Y := Y) n)
    (isOpen_slabA (Y := Y) n) (isOpen_slabB (Y := Y) n) (slabA_union_slabB (Y := Y) n) 0).symm

/-! ## The induction -/

/-- The boundary of the `0`-cube is empty. -/
theorem cubeBdryK_zero : cubeBdryK Y 0 = (∅ : Set (CubeP Y 0)) := by
  ext p
  simp [cubeBdryK, Cube.boundary]

/-- **Base case: the `0`-cube.** -/
theorem cubePairZero_iso (j : ℕ) :
    Nonempty (((Work.Cohomology.relChains (CubeSpace (Y := Y) 0)
        (cubeBdryK Y 0)).homology j) ≅
      (Work.Cohomology.singularChains ℤ (TopCat.of Y)).homology j) := by
  obtain ⟨e₁⟩ := relChains_empty_iso (CubeSpace (Y := Y) 0)
  have hbdry : Work.Cohomology.relChains (CubeSpace (Y := Y) 0) (cubeBdryK Y 0) ≅
      Work.Cohomology.relChains (CubeSpace (Y := Y) 0) (∅ : Set (CubeP Y 0)) :=
    eqToIso (congrArg (fun s => Work.Cohomology.relChains (CubeSpace (Y := Y) 0) s)
      (cubeBdryK_zero (Y := Y)))
  obtain ⟨e₂⟩ := Work.Cohomology.homology_prod_contractible
    (TopCat.of (Fin 0 → unitInterval)) (TopCat.of Y) j
  exact ⟨HomologicalComplex.homologyMapIso (hbdry ≪≫ e₁) j ≪≫ e₂⟩

/-- **The relative homology of the cube pair.**  For every `k`, the `(j+k)`-th relative homology
of `(Iᵏ × Y, ∂Iᵏ × Y)` is the `j`-th homology of `Y`, and the relative homology vanishes below
degree `k`. -/
theorem cubePair_main (k : ℕ) :
    (∀ (Y : Type) [TopologicalSpace Y] (j : ℕ),
        Nonempty (((Work.Cohomology.relChains (CubeSpace Y k) (cubeBdryK Y k)).homology (j + k)) ≅
          (Work.Cohomology.singularChains ℤ (TopCat.of Y)).homology j)) ∧
      (∀ (Y : Type) [TopologicalSpace Y] (m : ℕ), m < k →
        IsZero ((Work.Cohomology.relChains (CubeSpace Y k) (cubeBdryK Y k)).homology m)) := by
  induction k with
  | zero =>
      exact ⟨fun Y _ j => cubePairZero_iso (Y := Y) j, fun Y _ m hm => absurd hm (by omega)⟩
  | succ k ih =>
      obtain ⟨ihiso, ihzero⟩ := ih
      refine ⟨fun Y _ j => ?_, fun Y _ m hm => ?_⟩
      · obtain ⟨e₁⟩ := cubePairStep_iso (Y := Y) k (j + k)
        obtain ⟨e₂⟩ := midRelIso (Y := Y) k (j + k)
        obtain ⟨e₃⟩ := ihiso (midParam Y) (j := j)
        haveI : ContractibleSpace ↥(Set.Ioo (1/4:ℝ) (3/4)) :=
          Convex.contractibleSpace (convex_Ioo (1/4:ℝ) (3/4)) ⟨1/2, by norm_num⟩
        obtain ⟨e₄⟩ := Work.Cohomology.homology_prod_contractible
          (TopCat.of ↥(Set.Ioo (1/4:ℝ) (3/4))) (TopCat.of Y) j
        exact ⟨e₁ ≪≫ e₂ ≪≫ e₃ ≪≫ e₄⟩
      · match m with
        | 0 => exact cubePairZero_isZero (Y := Y) k
        | (m' + 1) =>
          obtain ⟨e₁⟩ := cubePairStep_iso (Y := Y) k m'
          obtain ⟨e₂⟩ := midRelIso (Y := Y) k m'
          exact IsZero.of_iso (ihzero (midParam Y) m' (by omega)) (e₁ ≪≫ e₂)

/-- **The relative homology of the cube pair in the range above the dimension.** -/
theorem cubePair_iso (k : ℕ) (Y : Type) [TopologicalSpace Y] (j : ℕ) :
    Nonempty (((Work.Cohomology.relChains (CubeSpace Y k) (cubeBdryK Y k)).homology (j + k)) ≅
      (Work.Cohomology.singularChains ℤ (TopCat.of Y)).homology j) :=
  (cubePair_main k).1 Y j

/-- **The relative homology of the cube pair vanishes below the dimension.** -/
theorem cubePair_isZero (k : ℕ) (Y : Type) [TopologicalSpace Y] (m : ℕ) (hm : m < k) :
    IsZero ((Work.Cohomology.relChains (CubeSpace Y k) (cubeBdryK Y k)).homology m) :=
  (cubePair_main k).2 Y m hm

end

end Work.StemsB
