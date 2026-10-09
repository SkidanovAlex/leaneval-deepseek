import Submission.Work.SSGRoute.ZDataTwo.Mu2ArithDeps
import Submission.Work.SSGRoute.ZDataTwo.exists_kummerChar_of_additive_locConst_base
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Every locally constant character of a decomposition group is a global Kummer character

Let `k` be a number field, `Ω` an algebraic closure, `A` a finite place of `Ω` over `k`, and
`a : G_k → 𝔽₂` a cochain that is additive and locally constant on the decomposition group
`decomp k A`.  Then there is a *global* unit `b ∈ kˣ` whose Kummer character agrees with `a` on
`decomp k A`:

  `a σ = kummerChar b σ`  for all `σ ∈ decomp k A`.

This is the local Kummer surjectivity at a single place in the cochain language: the map
`kˣ → Hom(decomp k A, 𝔽₂)`, `b ↦ kummerChar b`, is onto.  The proof combines

* `Work.SSGRoute.grunwald_surjective_two` (Grünwald's theorem at `K = ⊥`): the local character `a`
  extends to a globally additive, locally constant cochain `z : G_k → 𝔽₂`; and
* `Work.SSGRoute.ZDataTwo.exists_kummerChar_of_additive_locConst_base`: every such `z` is the
  Kummer character of some `b ∈ kˣ`.

It is the surjectivity that lets the finite-place half of the `μ₂` local Tate pairing be defined on
the local cohomology: every local class is the class of a *global* Kummer character, so the local
Hilbert symbol of the corresponding global elements computes the pairing.
-/

namespace Work.SSGRoute.ZDataTwo

open scoped Classical

theorem exists_kummerChar_agreeing_on_decomp {k Ω : Type} [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω] (ζ : k) (hζ : IsPrimitiveRoot ζ 2)
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) (a : (Ω ≃ₐ[k] Ω) → ZMod 2)
    (ha : ∀ g ∈ SSGRoute.decomp k A, ∀ h ∈ SSGRoute.decomp k A, a (g * h) = a g + a h)
    (hlc : SSGRoute.IsLocConstOn (SSGRoute.decomp k A) a) :
    ∃ b : kˣ, ∀ σ ∈ SSGRoute.decomp k A,
      a σ = Work.SSGRoute.kummerChar (K := k) (Ω := Ω) ζ hζ b σ := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  -- the fixing subgroup of the bottom field is everything
  have hfix : (⊥ : IntermediateField k Ω).fixingSubgroup = ⊤ := by
    refine le_antisymm le_top ?_
    intro σ _
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    obtain ⟨c, rfl⟩ := IntermediateField.mem_bot.mp hx
    exact AlgEquiv.commutes σ c
  have ha1 : a 1 = 0 := by
    have h := ha 1 (Subgroup.one_mem _) 1 (Subgroup.one_mem _)
    rw [mul_one] at h
    exact add_left_cancel (show a 1 + a 1 = a 1 + 0 by rw [add_zero]; exact h.symm)
  let T : Finset (ValuationSubring Ω) := {A}
  have hTfin : ∀ P ∈ T, SSGRoute.IsFinPlace k P := by
    intro P hP
    rw [Finset.mem_singleton] at hP
    rw [hP]
    exact hA
  have hTdisj : ∀ P ∈ T, ∀ Q ∈ T, SSGRoute.IsConjPlace k P Q → P = Q := by
    intro P hP Q hQ _
    rw [Finset.mem_singleton] at hP hQ
    rw [hP, hQ]
  let H : ∀ P : {P // P ∈ T}, Subgroup (Ω ≃ₐ[k] Ω) :=
    fun P => SSGRoute.decomp k (P : ValuationSubring Ω) ⊓ (⊥ : IntermediateField k Ω).fixingSubgroup
  let f : ∀ P : {P // P ∈ T}, ↥(H P) → ZMod 2 := fun P δ => a (δ : Ω ≃ₐ[k] Ω)
  have hf : ∀ P : {P // P ∈ T}, ∀ x y : ↥(H P), f P (x * y) = f P x + f P y := by
    intro P x y
    have hP : P.1 = A := Finset.mem_singleton.mp P.2
    have hx : (x : Ω ≃ₐ[k] Ω) ∈ SSGRoute.decomp k A := by
      simpa [hP] using (Subgroup.mem_inf.mp x.2).1
    have hy : (y : Ω ≃ₐ[k] Ω) ∈ SSGRoute.decomp k A := by
      simpa [hP] using (Subgroup.mem_inf.mp y.2).1
    exact ha (x : Ω ≃ₐ[k] Ω) hx (y : Ω ≃ₐ[k] Ω) hy
  have hfcont : ∀ P : {P // P ∈ T},
      ∃ U : Subgroup ↥(H P), IsOpen (U : Set ↥(H P)) ∧ ∀ x ∈ U, f P x = 0 := by
    intro P
    obtain ⟨V, hVo, hV⟩ := hlc
    refine ⟨V.comap (Subgroup.subtype _), ?_, ?_⟩
    · rw [Subgroup.coe_comap]
      exact hVo.preimage continuous_subtype_val
    · intro x hx
      have hxV : (x : Ω ≃ₐ[k] Ω) ∈ V := hx
      have hmem : (x : Ω ≃ₐ[k] Ω) ∈ SSGRoute.decomp k A := by
        have hP : P.1 = A := Finset.mem_singleton.mp P.2
        simpa [hP] using (Subgroup.mem_inf.mp x.2).1
      have h := hV 1 (Subgroup.one_mem _) (x : Ω ≃ₐ[k] Ω) hxV hmem
      have h1 : a (x : Ω ≃ₐ[k] Ω) = a 1 := by simpa using h
      show a (x : Ω ≃ₐ[k] Ω) = 0
      rw [h1, ha1]
  have hζΩ : IsPrimitiveRoot (algebraMap k Ω ζ) 2 := by
    have h := IsPrimitiveRoot.coe_units_iff.mpr
      (isPrimitiveRoot_mappedRoot (E := Ω) (p := 2) hζ)
    simpa [mappedRoot, Units.coe_map, Work.Kummer.primRootUnit_coe] using h
  have hζmem : algebraMap k Ω ζ ∈ (⊥ : IntermediateField k Ω) :=
    IntermediateField.mem_bot.mpr ⟨ζ, rfl⟩
  obtain ⟨z, hzadd, hzlc, hzagree⟩ :=
    grunwald_surjective_two (p := 2) rfl k Ω (⊥ : IntermediateField k Ω) (algebraMap k Ω ζ)
      hζΩ hζmem T hTfin hTdisj f hf hfcont
  obtain ⟨b, hb⟩ := exists_kummerChar_of_additive_locConst_base (k := k) (Ω := Ω) ζ hζ z
    (fun g h => hzadd g (by rw [hfix]; exact Subgroup.mem_top g) h
      (by rw [hfix]; exact Subgroup.mem_top h)) (by rwa [hfix] at hzlc)
  refine ⟨b, ?_⟩
  intro σ hσ
  have h := hzagree ⟨A, Finset.mem_singleton_self A⟩
    ⟨σ, ⟨hσ, by rw [hfix]; exact Subgroup.mem_top σ⟩⟩
  exact h.symm.trans (hb σ)

end Work.SSGRoute.ZDataTwo
