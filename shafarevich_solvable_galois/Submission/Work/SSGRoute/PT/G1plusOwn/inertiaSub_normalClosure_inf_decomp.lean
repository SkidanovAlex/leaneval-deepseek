import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.InertiaDefs
import Submission.Work.SSGRoute.decomp_inertia_quotient_cyclic
import Submission.Work.SSGRoute.isInertia_of_fixes_rootsOfUnity_gen
import Submission.Work.SSGRoute.fixes_rootsOfUnity_of_isInertia
import Submission.Work.SSGRoute.charP_residueField_isFinPlace
import Submission.Work.SSGRoute.isUnit_natCast_of_not_dvd_resCharAt
import Submission.Work.SSGRoute.E7cC.exists_level_unramified_p_dvd_inertiaDeg
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.PT.G1plusOwn

open scoped Pointwise

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

/-- **The closure of the normal closure of the inertia lies in the fixing subgroup of any finite
Galois level fixed by the inertia.**

If `M ⊆ Ω` is a finite Galois level over `k` which is fixed pointwise by the inertia
`I_A = Work.SSGRoute.inertiaSub k Ω A`, then `M.fixingSubgroup` is an open — hence closed —
normal subgroup of `G_k = Ω ≃ₐ[k] Ω` containing `I_A`, so it contains the smallest such group,
namely the topological closure of the normal closure of `I_A`. -/
lemma topologicalClosure_normalClosure_inertiaSub_le_fixingSubgroup
    (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (A : ValuationSubring Ω) (M : IntermediateField k Ω) [FiniteDimensional k M] [IsGalois k M]
    (hI : Work.SSGRoute.inertiaSub k Ω A ≤ M.fixingSubgroup) :
    Subgroup.topologicalClosure (Subgroup.normalClosure (Work.SSGRoute.inertiaSub k Ω A)) ≤
      M.fixingSubgroup := by
  haveI : IsGalois k Ω := inferInstance
  refine Subgroup.topologicalClosure_minimal _ (Subgroup.normalClosure_le_normal hI) ?_
  exact IntermediateField.fixingSubgroup_isClosed M

/-- **The normal closure of the inertia meets the decomposition group in the inertia** (its
topological closure — the exact form consumed by the compactness step of clause (6)).

Let `k` be a number field, `Ω` an algebraic closure of `k`, `A` a finite place of `Ω` over `k`, and
`D_A = SSGRoute.decomp k A ≤ G_k = Ω ≃ₐ[k] Ω` its decomposition group.  Then the topological
closure of the normal closure of the inertia `I_A = Work.SSGRoute.inertiaSub k Ω A` meets `D_A`
exactly in `I_A`, i.e. for every `σ ∈ D_A` that is a limit of products of conjugates of inertia
elements, `σ ∈ I_A`.

Why: `⋂ {V ◁ G_k : IsOpen V, I_A ≤ V} = closure(normalClosure I_A) =: C` (the open normal subgroups
containing a closed subgroup intersect in the closure of the normal closure).  With `M := Ω^C` (the
maximal Galois extension of `k` inside `Ω` on which `C` acts trivially) one has `C = Gal(Ω/M)`,
`M/k` is unramified at the place `A` (since `I_A ≤ C`), and the restriction `D_A → D_A(M)` has kernel
`D_A ⊓ C` and image the decomposition group of the prime of `M` under `A`, which is isomorphic to
`Gal(κ_M / κ_k)`.  As `M` contains `k(ζ_ℓ)` for every prime `ℓ ≠ p`, and the inertia degree of
`k(ζ_ℓ)` at the prime below `A` is unbounded as `ℓ` varies (primitive prime divisors of `p^n − 1`),
the residue field `κ_M` is `𝔽̄_q`, so `D_A ⊓ C` sits in the kernel of the isomorphism
`D_A/I_A ≅ Gal(𝔽̄_q/𝔽_q) = Ẑ` with `D_A/(D_A ⊓ C) ≅ Ẑ`; a surjection of `Ẑ` onto `Ẑ` has trivial
kernel, so `D_A ⊓ C = I_A`.

WARNING (both reviewers): the pairwise statement "`I_{gA} ⊓ D_A = ⊥` for `g ∉ D_A` by rigidity of
places" does *not* suffice, because `closure(normalClosure I_A)` also contains *products* of such
conjugates, and pairwise triviality does not control the intersection of the generated group with
`D_A`.  Budget for a genuine product/normal-form argument (or the residue-field argument above),
not a two-liner.  This is the single remaining input of
`Work.SSGRoute.PT.G1plusOwn.exists_unramified_level_factors`: with it, the finite intersection
property over `𝒱 = {V ◁ G_k : IsOpen V, I_A ≤ V}` in the compact space `↥(decomp k A)` produces
`V ⊓ D_A ≤ Z` for any subgroup `Z ≤ D_A` with `I_A ≤ Z`. -/
theorem inertiaSub_normalClosure_inf_decomp
    (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) :
    Subgroup.topologicalClosure (Subgroup.normalClosure (Work.SSGRoute.inertiaSub k Ω A)) ⊓
        SSGRoute.decomp k A ≤
      Work.SSGRoute.inertiaSub k Ω A := by
  haveI hGalΩ : IsGalois k Ω := inferInstance
  haveI hSep : IsSepClosure k Ω := IsSepClosure.of_isAlgClosure_of_perfectField k Ω
  intro σ hσ
  obtain ⟨hσC, hσD⟩ := Subgroup.mem_inf.mp hσ
  rw [Work.SSGRoute.mem_inertiaSub]
  -- It suffices to show that `σ` fixes every root of unity of order prime to the residue
  -- characteristic `p`: this forces inertia.
  refine Work.SSGRoute.isInertia_of_fixes_rootsOfUnity_gen k Ω A hA
    (NK.TameStructureDeep.Tame.resCharAt (Submission.NeukirchUchida.primeOf A hA))
    (Work.SSGRoute.charP_residueField_isFinPlace k Ω A hA) σ hσD ?_
  intro n hn ζ hζ
  -- `ζ` is a primitive `n`-th root of unity of order prime to `p`, hence fixed by the inertia
  -- and therefore by the closed normal subgroup it generates: the level `M = k⟮ζ⟯` is finite
  -- Galois and `I_A ≤ M.fixingSubgroup`, so `C ≤ M.fixingSubgroup`.
  have hnpos : 0 < n := Nat.pos_of_ne_zero (fun h0 => hn (h0 ▸ dvd_zero _))
  haveI : NeZero n := ⟨hnpos.ne'⟩
  let M : IntermediateField k Ω := IntermediateField.adjoin k ({ζ} : Set Ω)
  haveI hcyc : IsCyclotomicExtension ({n} : Set ℕ) k ↥M :=
    Work.SSGRoute.E7cC.isCyclotomicExtension_adjoin_primitiveRoot (K := k) hζ
  haveI hMfd : FiniteDimensional k M := IsCyclotomicExtension.finiteDimensional {n} k ↥M
  haveI hMgal : IsGalois k M := IsCyclotomicExtension.isGalois {n} k ↥M
  have hIle : Work.SSGRoute.inertiaSub k Ω A ≤ M.fixingSubgroup := by
    refine (IntermediateField.le_iff_le (Work.SSGRoute.inertiaSub k Ω A) M).mp ?_
    rw [show M = IntermediateField.adjoin k ({ζ} : Set Ω) from rfl, IntermediateField.adjoin_le_iff]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    rw [hx]
    change ζ ∈ IntermediateField.fixedField (Work.SSGRoute.inertiaSub k Ω A)
    rw [IntermediateField.mem_fixedField_iff]
    intro τ hτ
    exact Work.SSGRoute.fixes_rootsOfUnity_of_isInertia ⟨A, hA⟩
      (fun m hm => (Work.SSGRoute.isUnit_natCast_iff_not_dvd_resCharAt k Ω A hA m).mpr hm)
      ⟨τ, ((Work.SSGRoute.mem_inertiaSub k Ω A τ).mp hτ).1⟩
      ((Work.SSGRoute.mem_inertiaSub k Ω A τ).mp hτ) n hn ζ hζ
  have hC := topologicalClosure_normalClosure_inertiaSub_le_fixingSubgroup k Ω A M hIle
  exact (IntermediateField.mem_fixingSubgroup_iff M σ).mp (hC hσC) ζ
    (IntermediateField.mem_adjoin_simple_self k ζ)

end Work.SSGRoute.PT.G1plusOwn
