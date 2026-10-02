import Mathlib
import Submission.Work.ThomBordism.valuePmOneV2Defs
import Submission.Work.ThomBordism.localGenDefs
import Submission.Work.Cohomology.localCohomology

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.ThomBordism

/-- **The top relative homology of the punctured closed tube is `ℤ`.**

The punctured tube `tubePtSet E C x = C.U ∖ {E.e x}` is the complement of a point in the closed
tube; the local homology `H_{8+k}(C.U, C.U ∖ {E.e x})` of the tube at its centre is `ℤ`.

The proof shrinks the pair to the open tube (excision for the two-open cover
`openTube ∪ (C.U ∖ {pt}) = C.U`), then to the ambient Euclidean space (excision for the two-open
cover `openTube ∪ (ℝ^N ∖ {pt}) = ℝ^N`), and evaluates the resulting local homology of `ℝ^N` at a
point by `Work.Cohomology.localHomology`. -/
theorem tubeRelChains_tubePtSet_iso {V : Work.ThomBordism.Man8} [ConnectedSpace V.pt] {k : ℕ}
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) {ε : ℝ}
    (C : Work.Tubular.TubeChart E ε) (x : V.pt) :
    Nonempty ((Work.Cohomology.relChains (TopCat.of ↥C.U)
      (Work.ThomBordism.tubePtSet E C x)).homology (8 + k) ≅ ModuleCat.of ℤ ℤ) := by
  have hmem : E.e x ∈ C.openTube := C.mem_openTube x
  -- the two open sets covering the closed tube
  have hU'open : IsOpen {y : ↥C.U | (y : Work.Tubular.Euc (8 + k)) ∈ C.openTube} :=
    C.openTube_isOpen.preimage continuous_subtype_val
  have hVopen : IsOpen (Work.ThomBordism.tubePtSet E C x) :=
    (isClosed_singleton : IsClosed ({E.e x} : Set (Work.Tubular.Euc (8 + k)))).isOpen_compl.preimage
      continuous_subtype_val
  have hcov : {y : ↥C.U | (y : Work.Tubular.Euc (8 + k)) ∈ C.openTube}
      ∪ Work.ThomBordism.tubePtSet E C x = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    intro y
    by_cases hy : (y : Work.Tubular.Euc (8 + k)) ∈ C.openTube
    · exact Or.inl hy
    · exact Or.inr (by rw [Work.ThomBordism.mem_tubePtSet]; exact fun h => hy (h ▸ hmem))
  obtain ⟨e1⟩ := Work.Cohomology.homologyTwoCover (TopCat.of ↥C.U)
    {y : ↥C.U | (y : Work.Tubular.Euc (8 + k)) ∈ C.openTube}
    (Work.ThomBordism.tubePtSet E C x) hU'open hVopen hcov (8 + k)
  -- identify the small pair with the corresponding pair in the open tube
  let U' : Set ↥C.U := {y | (y : Work.Tubular.Euc (8 + k)) ∈ C.openTube}
  let e : ↥U' ≃ₜ ↥C.openTube :=
    { toFun := fun y => ⟨(y.1 : Work.Tubular.Euc (8 + k)), y.2⟩
      invFun := fun z => ⟨⟨z.1, C.openTube_subset_U z.2⟩, z.2⟩
      left_inv := fun y => by ext; rfl
      right_inv := fun z => by ext; rfl
      continuous_toFun := Continuous.subtype_mk
        ((continuous_subtype_val : Continuous (Subtype.val : ↥C.U → Work.Tubular.Euc (8 + k))).comp
          (continuous_subtype_val : Continuous (Subtype.val : ↥U' → ↥C.U))) _
      continuous_invFun := Continuous.subtype_mk (Continuous.subtype_mk
        (continuous_subtype_val : Continuous (Subtype.val : ↥C.openTube → Work.Tubular.Euc (8 + k))) _) _ }
  let A : Set ↥U' := {y | (y : ↥C.U) ∈ Work.ThomBordism.tubePtSet E C x}
  let B : Set ↥C.openTube := {y | (y : Work.Tubular.Euc (8 + k)) ≠ E.e x}
  have e_apply : ∀ y : ↥U',
      ((e y : ↥C.openTube) : Work.Tubular.Euc (8 + k)) = (y.1 : Work.Tubular.Euc (8 + k)) :=
    fun y => rfl
  have he : ∀ y : ↥U', y ∈ A ↔ e y ∈ B := by
    intro y
    simp only [A, B, Set.mem_ofPred_eq, Work.ThomBordism.mem_tubePtSet]
    rw [e_apply y]
  obtain ⟨e2⟩ := Work.Cohomology.relChains_homeomorph ↥U' ↥C.openTube A B e he (8 + k)
  -- the same pair in the ambient Euclidean space
  have hVopen2 : IsOpen {z : Work.Tubular.Euc (8 + k) | z ≠ E.e x} :=
    (isClosed_singleton : IsClosed ({E.e x} : Set (Work.Tubular.Euc (8 + k)))).isOpen_compl
  have hcov2 : C.openTube ∪ {z : Work.Tubular.Euc (8 + k) | z ≠ E.e x} = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    intro z
    by_cases hz : z ∈ C.openTube
    · exact Or.inl hz
    · exact Or.inr (fun h => hz (h ▸ hmem))
  obtain ⟨e3⟩ := Work.Cohomology.homologyTwoCover (TopCat.of (Work.Tubular.Euc (8 + k)))
    C.openTube {z : Work.Tubular.Euc (8 + k) | z ≠ E.e x} C.openTube_isOpen hVopen2 hcov2 (8 + k)
  -- the local homology of `ℝ^N` at a point
  obtain ⟨e4⟩ := Work.Cohomology.localHomology (8 + k) (by omega)
    (Work.Tubular.Euc (8 + k)) (E.e x)
  exact ⟨e1 ≪≫ e2 ≪≫ e3.symm ≪≫ e4⟩

end Work.ThomBordism
