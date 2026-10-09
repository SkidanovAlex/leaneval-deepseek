import Mathlib
import Submission.NK.CFTLib.ArtinIdeal
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `arl_groupData`

Group-theoretic data attached to the "Route-B" pair of subgroups `Msub, Nsub ≤ Gal(Ω/K)`.

Let `Ω/K` be a finite Galois extension of number fields and let `Msub, Nsub` be normal subgroups
of `Gal(Ω/K)` whose fixed fields `Ω^{Msub}`, `Ω^{Nsub}` are linearly disjoint over `K` and
together generate `Ω/K`.  The Galois correspondence turns this into

* `Msub ⊔ Nsub = ⊤`  (from `fixedField Msub ⊓ fixedField Nsub = ⊥`), and
* `Msub ⊓ Nsub = ⊥`  (from `fixedField Msub ⊔ fixedField Nsub = ⊤`),

i.e. `Gal(Ω/K)` is the internal direct product of `Msub` and `Nsub`.  Consequently
`Nsub ≃* Gal(Ω/K) ⧸ Msub` and `Msub ≃* Gal(Ω/K) ⧸ Nsub`, so that cyclicity and the order of
either factor transfer from the corresponding quotient.

All of this is elementary: the only input is the order isomorphism
`IsGalois.intermediateFieldEquivSubgroup` given by the (finite) Galois correspondence.
-/

namespace NK.CFTLib.Existence

section GroupOrder

variable {G : Type*} [Group G]

/-- **The quotient by a direct factor.**  If `M, N ≤ G` are normal subgroups with `M ⊓ N = ⊥`
and `M ⊔ N = ⊤` (so that `G` is the internal direct product of `M` and `N`), then the quotient
projection `G → G ⧸ M` restricts to an isomorphism `N ≃* G ⧸ M`. -/
noncomputable def mulEquivQuotientOfDisjoint (M N : Subgroup G) [M.Normal] [N.Normal]
    (hsup : M ⊔ N = ⊤) (hinf : M ⊓ N = ⊥) : N ≃* G ⧸ M := by
  let f : N →* G ⧸ M := (QuotientGroup.mk' M).comp N.subtype
  have hker : f.ker = ⊥ := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_bot]
    constructor
    · intro hx
      have hxM : (x : G) ∈ M := by
        rw [← QuotientGroup.eq_one_iff (x : G)]
        simpa [f] using hx
      have hxMN : (x : G) ∈ M ⊓ N := ⟨hxM, x.2⟩
      rw [hinf] at hxMN
      exact Subtype.ext (by simpa using hxMN)
    · intro hx
      rw [hx]
      exact map_one f
  have hsurj : Function.Surjective f := by
    intro y
    obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective M y
    have hgmem : g ∈ M ⊔ N := by rw [hsup]; exact Subgroup.mem_top g
    obtain ⟨m, hm, n, hn, hmn⟩ :=
      (Subgroup.mem_sup_of_normal_left (s := M) (t := N)).mp hgmem
    refine ⟨⟨n, hn⟩, ?_⟩
    rw [← hg]
    show QuotientGroup.mk' M n = QuotientGroup.mk' M g
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, ← hmn, QuotientGroup.mk_mul,
      (QuotientGroup.eq_one_iff m).mpr hm, one_mul]
  exact (QuotientGroup.quotientBot.symm).trans
    ((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective f hsurj))

end GroupOrder

section FixedField

variable {F E : Type*} [Field F] [Field E] [Algebra F E]

/-- The fixed field of a supremum is the infimum of the fixed fields.  (One half of the
lattice anti-isomorphism `H ↦ Ω^H`; no finiteness is needed.) -/
theorem fixedField_sup_eq_inf (H K : Subgroup Gal(E/F)) :
    IntermediateField.fixedField (H ⊔ K) =
      IntermediateField.fixedField H ⊓ IntermediateField.fixedField K := by
  refine le_antisymm (le_inf (IntermediateField.fixedField_le le_sup_left)
    (IntermediateField.fixedField_le le_sup_right)) ?_
  refine (IntermediateField.le_iff_le (H ⊔ K)
    (IntermediateField.fixedField H ⊓ IntermediateField.fixedField K)).mpr (sup_le ?_ ?_)
  · exact le_trans ((IntermediateField.le_iff_le H (IntermediateField.fixedField H)).mp le_rfl)
      (IntermediateField.fixingSubgroup_le inf_le_left)
  · exact le_trans ((IntermediateField.le_iff_le K (IntermediateField.fixedField K)).mp le_rfl)
      (IntermediateField.fixingSubgroup_le inf_le_right)

/-- The fixed field of an infimum is the supremum of the fixed fields.  This is the other half of
the anti-isomorphism and uses that the Galois correspondence is bijective (finite Galois
extension). -/
theorem fixedField_inf_eq_sup [FiniteDimensional F E] [IsGalois F E]
    (H K : Subgroup Gal(E/F)) :
    IntermediateField.fixedField (H ⊓ K) =
      IntermediateField.fixedField H ⊔ IntermediateField.fixedField K := by
  have h : (IntermediateField.fixedField H ⊔ IntermediateField.fixedField K).fixingSubgroup
      = H ⊓ K := by
    rw [IntermediateField.fixingSubgroup_sup, IntermediateField.fixingSubgroup_fixedField,
      IntermediateField.fixingSubgroup_fixedField]
  rw [← h, IsGalois.fixedField_fixingSubgroup]

/-- `fixedField` is injective on subgroups of the Galois group of a finite Galois extension. -/
theorem fixedField_injective [FiniteDimensional F E] (H K : Subgroup Gal(E/F))
    (h : IntermediateField.fixedField H = IntermediateField.fixedField K) : H = K := by
  have h2 := congrArg (fun (M : IntermediateField F E) => M.fixingSubgroup) h
  rwa [IntermediateField.fixingSubgroup_fixedField,
    IntermediateField.fixingSubgroup_fixedField] at h2

end FixedField

theorem arl_groupData {K L Ω : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] [Field Ω] [NumberField Ω] [Algebra K Ω]
    [FiniteDimensional K Ω] [IsGalois K Ω]
    (Msub Nsub : Subgroup Gal(Ω/K)) [Msub.Normal] [Nsub.Normal]
    (hN : Nat.card (Gal(Ω/K) ⧸ Nsub) = Nat.card Gal(L/K))
    (hM : Nat.card (Gal(Ω/K) ⧸ Msub) = Nat.card Gal(L/K))
    (hcyc : IsCyclic (Gal(Ω/K) ⧸ Msub))
    (hdisj : IntermediateField.fixedField Msub ⊓ IntermediateField.fixedField Nsub = ⊥)
    (hsup : IntermediateField.fixedField Msub ⊔ IntermediateField.fixedField Nsub = ⊤) :
    (Msub ⊔ Nsub = ⊤) ∧ (Msub ⊓ Nsub = ⊥) ∧
      Nonempty (Nsub ≃* (Gal(Ω/K) ⧸ Msub)) ∧
      Nonempty (Msub ≃* (Gal(Ω/K) ⧸ Nsub)) ∧
      IsCyclic Nsub ∧
      Nat.card Nsub = Nat.card Gal(L/K) ∧ Nat.card Msub = Nat.card Gal(L/K) := by
  have hsupG : Msub ⊔ Nsub = ⊤ := by
    refine fixedField_injective (Msub ⊔ Nsub) ⊤ ?_
    rw [fixedField_sup_eq_inf, hdisj, ← IsGalois.fixedField_top]
  have hinfG : Msub ⊓ Nsub = ⊥ := by
    refine fixedField_injective (Msub ⊓ Nsub) ⊥ ?_
    rw [fixedField_inf_eq_sup, hsup, IntermediateField.fixedField_bot]
  have eN : Nsub ≃* (Gal(Ω/K) ⧸ Msub) :=
    mulEquivQuotientOfDisjoint Msub Nsub hsupG hinfG
  have eM : Msub ≃* (Gal(Ω/K) ⧸ Nsub) :=
    mulEquivQuotientOfDisjoint Nsub Msub (by rw [sup_comm]; exact hsupG)
      (by rw [inf_comm]; exact hinfG)
  refine ⟨hsupG, hinfG, ⟨eN⟩, ⟨eM⟩, (MulEquiv.isCyclic eN).mpr hcyc, ?_, ?_⟩
  · rw [Nat.card_congr eN.toEquiv]; exact hM
  · rw [Nat.card_congr eM.toEquiv]; exact hN

end NK.CFTLib.Existence
