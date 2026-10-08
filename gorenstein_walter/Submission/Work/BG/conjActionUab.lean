import Mathlib
import Submission.Work.BG.KappaCharDefs

/-!
# The conjugation action of `N_G(U)` on the abelianisation `U/U'`

For a subgroup `U ≤ G` and a subgroup `S ≤ N_G(U)`, conjugation by an element of `S` is an
automorphism of `U` that preserves the derived subgroup `U'`; hence it descends to an
automorphism of the abelianisation `Uab U = U/U'`.  This file constructs the resulting
monoid homomorphism `↥S →* MulAut (Uab U)` and verifies its value on the classes `UabMk U x`.

The construction factors through two homomorphisms:

* `conjAutH U S hnorm : ↥S →* MulAut ↥U` — conjugation on `U`;
* `abAut U : MulAut ↥U →* MulAut (Uab U)` — descent of an automorphism of `U` to `U/U'`
  (using that the derived subgroup is characteristic).
-/

namespace Work.BG

open Subgroup

variable {G : Type} [Group G]

/-- The derived subgroup `U' = ⁅U,U⁆` of `U ≤ G`, viewed as a subgroup of `↥U`, coincides with the
commutator subgroup of the group `↥U`. -/
lemma derivedU_eq_commutator (U : Subgroup G) : derivedU U = _root_.commutator ↥U := by
  rw [derivedU, Subgroup.subgroupOf, ← Subgroup.map_subtype_commutator U]
  rw [Subgroup.comap_map_eq, Subgroup.ker_subtype, sup_bot_eq]

/-- The derived subgroup `derivedU U` is characteristic: every automorphism of `↥U` maps it to
itself. -/
lemma map_derivedU (U : Subgroup G) (e : MulAut ↥U) :
    (derivedU U).map (e : ↥U →* ↥U) = derivedU U := by
  rw [derivedU_eq_commutator, map_commutator_eq, MonoidHom.range_eq_top.2 e.surjective]
  exact (commutator_def ↥U).symm

/-- Every automorphism of `↥U` descends to an automorphism of the abelianisation `Uab U`; this is
`MulAut ↥U →* MulAut (Uab U)`. -/
noncomputable def abAut (U : Subgroup G) : MulAut ↥U →* MulAut (Uab U) where
  toFun e := QuotientGroup.congr (derivedU U) (derivedU U) e (map_derivedU U e)
  map_one' := by
    ext q
    refine QuotientGroup.induction_on q ?_
    intro z
    rw [QuotientGroup.congr_apply]
    simp
  map_mul' := by
    intro e1 e2
    ext q
    refine QuotientGroup.induction_on q ?_
    intro z
    rw [QuotientGroup.congr_apply]
    simp only [MulAut.mul_apply]
    rw [QuotientGroup.congr_apply, QuotientGroup.congr_mk']

/-- Conjugation on `U` by elements of a subgroup `S ≤ N_G(U)`, as a monoid homomorphism
`↥S →* MulAut ↥U`. -/
noncomputable def conjAutH (U S : Subgroup G) (hnorm : S ≤ Subgroup.normalizer (U : Set G)) :
    ↥S →* MulAut ↥U where
  toFun s :=
    { toFun := fun x => ⟨(s : G) * (x : G) * (s : G)⁻¹,
        (Subgroup.mem_normalizer_iff.mp (hnorm s.2) (x : G)).mp x.2⟩
      invFun := fun x => ⟨(s : G)⁻¹ * (x : G) * (s : G), by
        have h : (s : G)⁻¹ ∈ Subgroup.normalizer (U : Set G) := inv_mem (hnorm s.2)
        simpa using (Subgroup.mem_normalizer_iff.mp h (x : G)).mp x.2⟩
      left_inv := fun x => Subtype.ext (by group)
      right_inv := fun x => Subtype.ext (by group)
      map_mul' := fun x y => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
  map_one' := MulEquiv.ext (fun x => Subtype.ext (by simp))
  map_mul' := fun s t => MulEquiv.ext (fun x => Subtype.ext (by simp; group))

theorem conjActionUab {G : Type} [Group G] (U S : Subgroup G) (hnorm : S ≤ Subgroup.normalizer (U : Set G)) : ∃ φ : ↥S →* MulAut (Uab U), ∀ (s : ↥S) (x : ↥U), φ s (UabMk U x) = UabMk U ⟨(s : G) * (x : G) * (s : G)⁻¹, (Subgroup.mem_normalizer_iff.mp (hnorm s.2) (x : G)).mp x.2⟩ := by
  refine ⟨(abAut U).comp (conjAutH U S hnorm), ?_⟩
  intro s x
  change abAut U (conjAutH U S hnorm s) (UabMk U x) = _
  change QuotientGroup.congr (derivedU U) (derivedU U) (conjAutH U S hnorm s)
      (map_derivedU U (conjAutH U S hnorm s)) (UabMk U x) = _
  rw [UabMk_apply, QuotientGroup.congr_mk']
  rfl

end Work.BG
