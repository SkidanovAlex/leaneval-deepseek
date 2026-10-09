import Mathlib
import Submission.Work.SSGRoute.P2Core.defs
import Submission.Work.SSGRoute.ZDataMup.swCoreDefs
import Submission.Work.SSGRoute.place_basics
import Submission.Work.SSGRoute.H9.swHistKExists_proved
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The sibling places of the `p = 2` §4 recursion: splitting and separation

Two facts about `Work.SSGRoute.ZDataMup.siblingPlace K σ Q = galLift K σ • Q` that the recursion's
*datum* consumes:

* `siblingPlace_isSplitIn` — a sibling of a `Λ`-split place is `Λ`-split.  This is what makes the
  oracle's dichotomy `horth` available at every block of the recursion attached to an escape prime
  (the blocks attached to `S` carry the constant datum `0`);
* `siblingPlace_gesKConj_iff` — the `K`-classes of the siblings of the escape primes are pairwise
  distinct (different `σ` by `Work.SSGRoute.ZDataMup.siblingPlace_not_gesKConj`, different `l` by the
  `k`-level disjointness of the escape primes).  This is what makes the recursion's datum *well
  defined* when it is read off from an arbitrary attachment of a block to a pair `(l, σ)`.

See `ACTION_p2_recursion_datum_and_hKimag.md`; `P2Core/placeSetBookkeeping.lean` (`blockAttached`)
supplies the attachment itself.

The normality of a fixing subgroup is taken in the form `ker (restrictNormalHom ·) = fixingSubgroup`,
so that no `IsGalois k Ω` instance for the *algebraic closure* is needed.
-/

open scoped Pointwise

set_option linter.unusedVariables false

namespace Work.SSGRoute.P2Core

/-- The fixing subgroup of a normal subextension is normal, in the form that needs no `IsGalois`
instance for the ambient field. -/
theorem fixingSubgroup_normal {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]
    (N : IntermediateField k Ω) [Normal k N] : (N.fixingSubgroup).Normal := by
  rw [← IntermediateField.restrictNormalHom_ker N]
  exact MonoidHom.normal_ker _

/-- **A sibling of a `Λ`-split place is `Λ`-split.** -/
theorem siblingPlace_isSplitIn {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K Λ : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [FiniteDimensional k Λ] [IsGalois k Λ]
    (σ : K ≃ₐ[k] K) (Q : ValuationSubring Ω) (hQ : SSGRoute.IsSplitIn k Λ Q) :
    SSGRoute.IsSplitIn k Λ (Work.SSGRoute.ZDataMup.siblingPlace K σ Q) := by
  rw [Work.SSGRoute.ZDataMup.siblingPlace]
  exact (Work.SSGRoute.isSplitIn_conj Λ (fixingSubgroup_normal Λ) Q
    (Work.SSGRoute.ZDataMup.galLift K σ)).mpr hQ

/-- **The fixing subgroup of `K` is normal**, without an `IsGalois` instance for the ambient field. -/
theorem fixingSubgroup_normal_K {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]
    (K : IntermediateField k Ω) [Normal k K] : (K.fixingSubgroup).Normal :=
  fixingSubgroup_normal K

/-- **`gesKConj` is invariant under `G_k`-conjugation** (`G_K = ker (res)` is normal in `G_k`). -/
theorem gesKConj_smul {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [Normal k K]
    {A B : ValuationSubring Ω} (g : Ω ≃ₐ[k] Ω)
    (h : Work.SSGRoute.gesKConj K A B) :
    Work.SSGRoute.gesKConj K (g • A) (g • B) := by
  obtain ⟨τ, hτ, hτA⟩ := h
  have hτ1 : AlgEquiv.restrictNormalHom K τ = 1 := by
    have hmem : τ ∈ (AlgEquiv.restrictNormalHom K).ker := by
      rw [IntermediateField.restrictNormalHom_ker K]
      exact hτ
    exact MonoidHom.mem_ker.mp hmem
  refine ⟨g * τ * g⁻¹, ?_, ?_⟩
  · rw [← IntermediateField.restrictNormalHom_ker K, MonoidHom.mem_ker, map_mul, map_mul, map_inv,
      hτ1, mul_one, mul_inv_cancel]
  · show (g * τ * g⁻¹) • (g • A) = g • B
    rw [mul_smul, mul_smul, inv_smul_smul, hτA]

/-- **The siblings of the escape primes carry pairwise distinct `K`-classes.**  If the sibling of
`Q l` at `σ` and the sibling of `Q l'` at `σ'` are `K`-conjugate, then `l = l'` and `σ = σ'`. -/
theorem siblingPlace_gesKConj_iff {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] [IsAlgClosed Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] (m : ℕ) (Q : Fin m → ValuationSubring Ω)
    (hQsplitK : ∀ l, SSGRoute.IsSplitIn k K (Q l))
    (hQdisj : ∀ l l', SSGRoute.IsConjPlace k (Q l) (Q l') → l = l')
    (l l' : Fin m) (σ σ' : K ≃ₐ[k] K) :
    Work.SSGRoute.gesKConj K (Work.SSGRoute.ZDataMup.siblingPlace K σ (Q l))
      (Work.SSGRoute.ZDataMup.siblingPlace K σ' (Q l')) → l = l' ∧ σ = σ' := by
  intro h
  have hKnorm : (K.fixingSubgroup).Normal := fixingSubgroup_normal K
  -- ## step 1: conjugate the relation by `(galLift K σ)⁻¹`, giving `u • Q l = w • Q l'`
  obtain ⟨τ, hτ, hτA⟩ := h
  set u : Ω ≃ₐ[k] Ω :=
    (Work.SSGRoute.ZDataMup.galLift K σ)⁻¹ * τ * Work.SSGRoute.ZDataMup.galLift K σ with hu
  set w : Ω ≃ₐ[k] Ω :=
    (Work.SSGRoute.ZDataMup.galLift K σ)⁻¹ * Work.SSGRoute.ZDataMup.galLift K σ' with hw
  have huK : u ∈ K.fixingSubgroup := by
    rw [hu]
    exact hKnorm.conj_mem τ hτ (Work.SSGRoute.ZDataMup.galLift K σ)⁻¹
  have h2 : u • (Q l) = w • (Q l') := by
    have hcongr := congrArg (fun X => (Work.SSGRoute.ZDataMup.galLift K σ)⁻¹ • X) hτA
    rw [hu, hw]
    simp only [Work.SSGRoute.ZDataMup.siblingPlace, mul_smul] at hcongr ⊢
    exact hcongr
  -- ## step 2: `Q l` and `Q l'` are `k`-conjugate, hence `l = l'`
  have hconjl : SSGRoute.IsConjPlace k (Q l) (Q l') :=
    ⟨w⁻¹ * u, by rw [mul_smul, h2, inv_smul_smul]⟩
  obtain hll : l = l' := hQdisj l l' hconjl
  subst hll
  -- ## step 3: `Q l` is `K`-conjugate to the sibling of `Q l` at `σ⁻¹ σ'`
  have hwres : SSGRoute.res k K w = σ⁻¹ * σ' := by
    rw [hw, map_mul, map_inv, Work.SSGRoute.ZDataMup.galLift_spec,
      Work.SSGRoute.ZDataMup.galLift_spec]
  set v : Ω ≃ₐ[k] Ω := (Work.SSGRoute.ZDataMup.galLift K (σ⁻¹ * σ'))⁻¹ * w with hv
  have hvK : v ∈ K.fixingSubgroup := by
    rw [← IntermediateField.restrictNormalHom_ker K, MonoidHom.mem_ker, hv, map_mul, map_inv,
      Work.SSGRoute.ZDataMup.galLift_spec, hwres, inv_mul_cancel]
  have hkey : Work.SSGRoute.gesKConj K (Q l)
      (Work.SSGRoute.ZDataMup.siblingPlace K (σ⁻¹ * σ') (Q l)) := by
    have hwv : w = Work.SSGRoute.ZDataMup.galLift K (σ⁻¹ * σ') * v := by
      rw [hv]; group
    have h3 : u • (Q l) =
        Work.SSGRoute.ZDataMup.galLift K (σ⁻¹ * σ') • (v • (Q l)) := by
      rw [h2, hwv, mul_smul]
    have h4 : Work.SSGRoute.gesKConj K (Q l)
        (Work.SSGRoute.ZDataMup.galLift K (σ⁻¹ * σ') • (v • (Q l))) := ⟨u, huK, h3⟩
    have h5 : Work.SSGRoute.gesKConj K
        (Work.SSGRoute.ZDataMup.galLift K (σ⁻¹ * σ') • (v • (Q l)))
        (Work.SSGRoute.ZDataMup.siblingPlace K (σ⁻¹ * σ') (Q l)) := by
      have hv' : Work.SSGRoute.gesKConj K (v • (Q l)) (Q l) :=
        ⟨v⁻¹, K.fixingSubgroup.inv_mem hvK, by rw [inv_smul_smul]⟩
      have hsm := gesKConj_smul K (Work.SSGRoute.ZDataMup.galLift K (σ⁻¹ * σ')) hv'
      have hgoal : Work.SSGRoute.ZDataMup.siblingPlace K (σ⁻¹ * σ') (Q l) =
          Work.SSGRoute.ZDataMup.galLift K (σ⁻¹ * σ') • (Q l) := rfl
      rw [hgoal]
      exact hsm
    exact Work.SSGRoute.H9.swGesKConj_trans h4 h5
  -- ## step 4: the sibling of `Q l` at `σ⁻¹σ'` is `Q l` itself only for `σ⁻¹σ' = 1`
  by_cases hσ : σ⁻¹ * σ' = 1
  · refine ⟨rfl, ?_⟩
    have h1 : σ' = σ := by
      have h2' := congrArg (fun x : K ≃ₐ[k] K => σ * x) hσ
      simpa [mul_assoc] using h2'
    exact h1.symm
  · exact absurd hkey
      (Work.SSGRoute.ZDataMup.siblingPlace_not_gesKConj K hσ (hQsplitK l))

end Work.SSGRoute.P2Core
