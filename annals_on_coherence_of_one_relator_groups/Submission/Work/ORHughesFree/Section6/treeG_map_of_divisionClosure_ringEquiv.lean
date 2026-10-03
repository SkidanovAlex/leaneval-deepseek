import Mathlib
import Submission.Work.ORHughesFree.Section6.TreeG
import Submission.Work.ORHughesFree.Section6.RatStruct
import Submission.Work.ORHughesFree.Section6.Phi_surjective
import Submission.Work.ORHughesFree.Section6.imElem_isUnit

set_option autoImplicit false

namespace Work.ORHughesFree.Section6

open Work.ORHughesFree

variable {K : Type} [Field K] {G : Type} [Group G] {U : Type} [Ring U] {V : Type} [Ring V]

/-! ### `e` is compatible with the rational structure `ratStruct`

The three lemmas below show that a ring isomorphism `e : D_{K[G],U} ≃+* D_{K[G],V}` which
intertwines `φ` and `ψ` (hypothesis `he`) is a morphism of rational `Kˣ × G`-semirings from
`ratStruct φ` to `ratStruct ψ`. -/

/-- **A ring isomorphism of subrings preserves the rational operation** "inverse if a unit, `0`
otherwise": it preserves units (in both directions, `e` and `e⁻¹` being ring homomorphisms) and
inverses. -/
private theorem ratOpClosure_ringEquiv {W W' : Type} [Ring W] [Ring W'] (D : Subring W)
    (D' : Subring W') (e : ↥D ≃+* ↥D') (x : ↥D) :
    e (ratOpClosure D x) = ratOpClosure D' (e x) := by
  classical
  have hiff : IsUnit (e x) ↔ IsUnit x :=
    isUnit_map_of_leftInverse (f := (e : ↥D →+* ↥D')) (g := (e.symm : ↥D' →+* ↥D))
      (fun y => RingEquiv.symm_apply_apply e y)
  by_cases h : IsUnit x
  · have h' : IsUnit (e x) := h.map (e : ↥D →+* ↥D')
    rw [ratOpClosure, dif_pos h, ratOpClosure, dif_pos h']
    have hh : h' = h.map (e : ↥D →+* ↥D') := Subsingleton.elim _ _
    rw [hh, IsUnit.unit_inv_map]
  · have h' : ¬ IsUnit (e x) := fun hh => h (hiff.mp hh)
    rw [ratOpClosure, dif_neg h, ratOpClosure, dif_neg h']
    exact map_zero e

/-- The left action of `ratStruct φ` is multiplication by `imElem φ u`: the coefficientwise
statement `ratStruct_smul`. -/
private theorem ratStruct_smul_eq (φ : MonoidAlgebra K G →+* U) (u : Kˣ × G)
    (x : ↥(divisionClosure (Set.range φ))) :
    (ratStruct φ).smul u x = imElem φ u * x := by
  apply Subtype.ext
  rw [ratStruct_smul]
  rfl

/-- The right action of `ratStruct φ` is multiplication by `imElem φ u`: the coefficientwise
statement `ratStruct_smulRight`. -/
private theorem ratStruct_smulRight_eq (φ : MonoidAlgebra K G →+* U)
    (x : ↥(divisionClosure (Set.range φ))) (u : Kˣ × G) :
    (ratStruct φ).smulRight x u = x * imElem φ u := by
  apply Subtype.ext
  rw [ratStruct_smulRight]
  rfl

/-- `e` carries the image of the group-like unit `λ·g` to the corresponding image: this is the
hypothesis `he` at `unitOf u`. -/
private theorem imElem_ringEquiv (φ : MonoidAlgebra K G →+* U) (ψ : MonoidAlgebra K G →+* V)
    (e : ↥(divisionClosure (Set.range φ)) ≃+* ↥(divisionClosure (Set.range ψ)))
    (he : ∀ x : MonoidAlgebra K G,
      e ⟨φ x, subset_divisionClosure (Set.range φ) ⟨x, rfl⟩⟩ =
        ⟨ψ x, subset_divisionClosure (Set.range ψ) ⟨x, rfl⟩⟩)
    (u : Kˣ × G) : e (imElem φ u) = imElem ψ u :=
  he (unitOf u)

/-- `e` intertwines the left `Kˣ × G`-actions of `ratStruct φ` and `ratStruct ψ`. -/
private theorem ratStruct_smul_ringEquiv (φ : MonoidAlgebra K G →+* U)
    (ψ : MonoidAlgebra K G →+* V)
    (e : ↥(divisionClosure (Set.range φ)) ≃+* ↥(divisionClosure (Set.range ψ)))
    (he : ∀ x : MonoidAlgebra K G,
      e ⟨φ x, subset_divisionClosure (Set.range φ) ⟨x, rfl⟩⟩ =
        ⟨ψ x, subset_divisionClosure (Set.range ψ) ⟨x, rfl⟩⟩)
    (u : Kˣ × G) (x : ↥(divisionClosure (Set.range φ))) :
    e ((ratStruct φ).smul u x) = (ratStruct ψ).smul u (e x) := by
  calc e ((ratStruct φ).smul u x) = e (imElem φ u * x) := by rw [ratStruct_smul_eq]
    _ = e (imElem φ u) * e x := map_mul _ _ _
    _ = imElem ψ u * e x := by rw [imElem_ringEquiv φ ψ e he u]
    _ = (ratStruct ψ).smul u (e x) := (ratStruct_smul_eq ψ u (e x)).symm

/-- `e` intertwines the right `Kˣ × G`-actions of `ratStruct φ` and `ratStruct ψ`. -/
private theorem ratStruct_smulRight_ringEquiv (φ : MonoidAlgebra K G →+* U)
    (ψ : MonoidAlgebra K G →+* V)
    (e : ↥(divisionClosure (Set.range φ)) ≃+* ↥(divisionClosure (Set.range ψ)))
    (he : ∀ x : MonoidAlgebra K G,
      e ⟨φ x, subset_divisionClosure (Set.range φ) ⟨x, rfl⟩⟩ =
        ⟨ψ x, subset_divisionClosure (Set.range ψ) ⟨x, rfl⟩⟩)
    (x : ↥(divisionClosure (Set.range φ))) (u : Kˣ × G) :
    e ((ratStruct φ).smulRight x u) = (ratStruct ψ).smulRight (e x) u := by
  calc e ((ratStruct φ).smulRight x u) = e (x * imElem φ u) := by rw [ratStruct_smulRight_eq]
    _ = e x * e (imElem φ u) := map_mul _ _ _
    _ = e x * imElem ψ u := by rw [imElem_ringEquiv φ ψ e he u]
    _ = (ratStruct ψ).smulRight (e x) u := (ratStruct_smulRight_eq ψ (e x) u).symm

/-- `e` intertwines the rational operations of `ratStruct φ` and `ratStruct ψ`. -/
private theorem ratStruct_ratOp_ringEquiv (φ : MonoidAlgebra K G →+* U)
    (ψ : MonoidAlgebra K G →+* V)
    (e : ↥(divisionClosure (Set.range φ)) ≃+* ↥(divisionClosure (Set.range ψ)))
    (x : ↥(divisionClosure (Set.range φ))) :
    e ((ratStruct φ).ratOp x) = (ratStruct ψ).ratOp (e x) := by
  rw [ratStruct_ratOp, ratStruct_ratOp]
  exact ratOpClosure_ringEquiv (divisionClosure (Set.range φ))
    (divisionClosure (Set.range ψ)) e x

/-- The three compatibility lemmas above, assembled: `e ∘ Φ_φ` is a morphism of rational
`Kˣ × G`-semirings `Rat(Kˣ × G) → D_{K[G],V}`, so it agrees with `Φ_ψ`
(`RatU.lift_unique`). -/
private theorem Phi_comp_ringEquiv (φ : MonoidAlgebra K G →+* U)
    (ψ : MonoidAlgebra K G →+* V)
    (e : ↥(divisionClosure (Set.range φ)) ≃+* ↥(divisionClosure (Set.range ψ)))
    (he : ∀ x : MonoidAlgebra K G,
      e ⟨φ x, subset_divisionClosure (Set.range φ) ⟨x, rfl⟩⟩ =
        ⟨ψ x, subset_divisionClosure (Set.range ψ) ⟨x, rfl⟩⟩) :
    (e.toRingHom.comp (Phi φ)) = Phi ψ := by
  refine RatU.lift_unique _ (ratStruct ψ) _ ?_
  exact { map_rat := fun α => by
            change e ((Phi φ) (RatU.rational.ratOp α)) = (ratStruct ψ).ratOp (e ((Phi φ) α))
            rw [(Phi_isRational φ).map_rat α]
            exact ratStruct_ratOp_ringEquiv φ ψ e (Phi φ α)
          map_smul := fun u α => by
            change e ((Phi φ) (RatU.rational.smul u α)) = (ratStruct ψ).smul u (e ((Phi φ) α))
            rw [(Phi_isRational φ).map_smul u α]
            exact ratStruct_smul_ringEquiv φ ψ e he u (Phi φ α)
          map_smulRight := fun α u => by
            change e ((Phi φ) (RatU.rational.smulRight α u)) =
              (ratStruct ψ).smulRight (e ((Phi φ) α)) u
            rw [(Phi_isRational φ).map_smulRight α u]
            exact ratStruct_smulRight_ringEquiv φ ψ e he (Phi φ α) u }

/-- **An isomorphism of `K[G]`-division closures preserves the complexity.**  Let
`φ : K[G] →+* U`, `ψ : K[G] →+* V` be ring homomorphisms and let
`e : D_{K[G],U} ≃+* D_{K[G],V}` be a ring isomorphism with `e (φ x) = ψ x` for all `x` (viewing
`φ x`, `ψ x` as elements of the division closures).  Then `Tree_G (e a) = Tree_G a`.

Indeed `e` maps the rational `Kˣ × G`-structure of `D_{K[G],U}` (`Section6.ratStruct φ`) onto that
of `D_{K[G],V}`: it preserves units, hence the rational operation `⋄` (inversion on units, `0`
elsewhere), and it intertwines the two actions (multiplication by `φ (unitOf u)` and by
`ψ (unitOf u) = e (φ (unitOf u))`); by uniqueness of the morphism of rational semirings
(`RatU.lift_existsUnique`) this gives `e ∘ Phi φ = Phi ψ`, so the sets of complexities of the
realisers of `a` and of `e a` are equal, and so are their minima (`treeG`). -/
theorem treeG_map_of_divisionClosure_ringEquiv {K : Type} [Field K] {G : Type} [Group G]
    {U : Type} [Ring U] {V : Type} [Ring V] (φ : MonoidAlgebra K G →+* U)
    (ψ : MonoidAlgebra K G →+* V)
    (e : ↥(divisionClosure (Set.range φ)) ≃+* ↥(divisionClosure (Set.range ψ)))
    (he : ∀ x : MonoidAlgebra K G,
      e ⟨φ x, subset_divisionClosure (Set.range φ) ⟨x, rfl⟩⟩ =
        ⟨ψ x, subset_divisionClosure (Set.range ψ) ⟨x, rfl⟩⟩)
    (a : ↥(divisionClosure (Set.range φ))) : treeG ψ (e a) = treeG φ a := by
  -- `e` carries realisers of `a` to realisers of `e a`: `Φ_ψ = e ∘ Φ_φ`.
  have key : (e.toRingHom.comp (Phi φ)) = Phi ψ := Phi_comp_ringEquiv φ ψ e he
  have key_apply : ∀ x : RatU (Kˣ × G), e (Phi φ x) = Phi ψ x :=
    fun x => DFunLike.congr_fun key x
  -- a realiser of `a` of minimal complexity is a realiser of `e a`
  obtain ⟨⟨α, hα, hαt⟩, hminα⟩ := treeG_spec φ a
  -- and conversely, a realiser of `e a` of minimal complexity is a realiser of `a`, since `e`
  -- is injective
  obtain ⟨⟨β, hβ, hβt⟩, hminβ⟩ := treeG_spec ψ (e a)
  have hψα : Phi ψ α = e a := by rw [← key_apply α, hα]
  have hβ'' : e (Phi φ β) = e a := by rw [key_apply β]; exact hβ
  have hβ' : Phi φ β = a := e.injective hβ''
  -- hence the two complexities are each at most the other
  refine Tree.le_antisymm ?_ ?_
  · have h := hminβ α hψα
    rwa [hαt] at h
  · have h := hminα β hβ'
    rwa [hβt] at h

end Work.ORHughesFree.Section6
