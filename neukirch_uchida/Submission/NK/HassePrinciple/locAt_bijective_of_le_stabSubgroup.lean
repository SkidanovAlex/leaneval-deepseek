import Mathlib
import Submission.NK.HassePrinciple.RankInput
import Submission.NK.HassePrinciple.loc_injective_of_le_stabSubgroup

/-!
# The localisation at a place containing `U` in its decomposition group is **bijective**

Let `U ≤ Gal(K'/K)` be a subgroup and `A` a place of `K'` over a finite prime of `K` whose
decomposition group `D_A = stabSubgroup A.1` contains `U`.  The sibling module
`Submission/Work/HassePrinciple/loc_injective_of_le_stabSubgroup.lean` proves that the localisation

`locAt p U A : H²(U, Z/p) ⟶ LocalH2 p U A.1`

is *injective*; the mathematical content of that proof is that the local filtered system
`(U ⊓ D_A)/((U ⊓ D_A) ∩ Gal(K'/L))` and the global one `U/(U ∩ Gal(K'/L))` coincide, so that every
level-wise localisation `locLevel p U A L = H2.map (localInclHom U A L)` is induced by the
*bijective* group homomorphism `localInclHom U A L : (U ⊓ D_A)/(...) →* U/(...)`.

Here we record the other half of the same fact: because each `localInclHom U A L` is bijective, each
level-wise localisation is **surjective** as well, and hence so is `locAt p U A`.  The surjectivity
on the colimit `LocalH2 p U A.1` is checked level by level: every element of `LocalH2` is the class
of a finite level (`localH2_ofLevel_surjective`), and on a level `L` the map `locLevel p U A L` is
surjective because `H²(·, Z/p)` of a bijective group homomorphism is surjective
(`h2Map_surjective_of_bijective`).

Combined with the injectivity of the sibling module, the localisation at such an *inert* place is an
isomorphism of `Z/p`-modules: the local filtered system is not merely a quotient but a copy of the
global one.
-/

open CategoryTheory

universe u

namespace NK.HassePrinciple

open NK.BrauerHasse

/-! ## Surjectivity of `H²(·, Z/p)` on a bijective group homomorphism -/

section H2Map

variable {p : ℕ} {G H : Type u} [Group G] [Group H]

/-- **`H²(·, Z/p)` of a bijective group homomorphism is surjective.**  If `f : G →* H` is
bijective, the inverse `f⁻¹ : H ≃* G` exhibits `H2.map f` as a split epimorphism:
`H2.map f ≫ H2.map f⁻¹ = H2.map (f⁻¹ ∘ f) = 𝟙` on `H²(G, Z/p)`.  (The companion injectivity
statement, `h2Map_injective_of_bijective`, is the same computation in the other order.) -/
lemma h2Map_surjective_of_bijective (f : G →* H) (hf : Function.Bijective f) :
    Function.Surjective (fun x : H2 p H => (H2.map (p := p) f).hom x) := by
  intro y
  refine ⟨(H2.map (p := p) ((MulEquiv.ofBijective f hf).symm : H →* G)).hom y, ?_⟩
  have hcomp : H2.map (p := p) ((MulEquiv.ofBijective f hf).symm : H →* G) ≫ H2.map (p := p) f
      = 𝟙 (H2 p G) := by
    rw [← H2.map_comp]
    have h1 : ((MulEquiv.ofBijective f hf).symm : H →* G).comp f = MonoidHom.id G := by
      ext x
      exact MulEquiv.symm_apply_apply (MulEquiv.ofBijective f hf) x
    rw [h1, H2.map_id]
  exact congrArg (fun (k : H2 p G ⟶ H2 p G) => k.hom y) hcomp

end H2Map

/-! ## Surjectivity of the level-wise localisation -/

section Level

variable {K K' : Type u} [Field K] [Field K'] [Algebra K K'] [IsSepClosure K K']

/-- **Every element of `LocalH2 p U A` comes from a finite level.**  The local cohomology is a
quotient of the disjoint union of its finite levels (`LocalH2.ofLevel`), exactly as for the global
cohomology (`H2Profinite.ofLevel_surjective`). -/
lemma localH2_ofLevel_surjective (p : ℕ) (U : Subgroup Gal(K'/K)) (A : ValuationSubring K')
    (y : LocalH2 p U A) :
    ∃ (L : FiniteGaloisIntermediateField K K') (a : LocalLevelH2 p U A L),
      LocalH2.ofLevel p U A L a = y := by
  induction y using Quot.ind with
  | _ y => exact ⟨y.1, y.2, rfl⟩

/-- **If `U ≤ D_A`, the level-wise localisation is surjective**: it is the map on `H²(·, Z/p)`
induced by the bijective group homomorphism `localInclHom U A L`. -/
lemma locLevel_surjective_of_le_stabSubgroup (p : ℕ) {U : Subgroup Gal(K'/K)}
    (A : ValuationSubring K') (h : U ≤ stabSubgroup A)
    (L : FiniteGaloisIntermediateField K K') :
    Function.Surjective (locLevel p U A L) := by
  intro b
  obtain ⟨a, ha⟩ := h2Map_surjective_of_bijective (f := localInclHom U A L)
    (localInclHom_bijective_of_le_stabSubgroup A h L) b
  exact ⟨a, ha⟩

end Level

/-! ## The main statement -/

theorem locAt_bijective_of_le_stabSubgroup {K K' : Type u} [Field K] [NumberField K] [Field K'] [Algebra K K'] [IsSepClosure K K'] (p : ℕ) {U : Subgroup Gal(K'/K)} (A : NK.BrauerHasse.OverFinitePrime K K') (h : U ≤ NK.BrauerHasse.stabSubgroup A.1) : Function.Bijective (NK.HassePrinciple.locAt (K := K) (K' := K') p U A) := by
  refine ⟨?_, ?_⟩
  · -- injectivity: `NK.HassePrinciple.loc_injective_of_le_stabSubgroup`
    intro x y hxy
    exact loc_injective_of_le_stabSubgroup p A h hxy
  · -- surjectivity: level by level, using the bijectivity of `localInclHom`
    intro y
    obtain ⟨L, b, rfl⟩ := localH2_ofLevel_surjective p U A.1 y
    obtain ⟨a, ha⟩ := locLevel_surjective_of_le_stabSubgroup (p := p) A.1 h L b
    exact ⟨H2Profinite.ofLevel L a, by rw [locAt, H2Profinite.loc_ofLevel_apply, ha]⟩

end NK.HassePrinciple
