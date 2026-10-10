import Mathlib.GroupTheory.Sylow
import Mathlib.Algebra.Torsor.Defs
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
import Mathlib.Topology.Algebra.RestrictedProduct.Basic
import Submission.NK.GlobalCFTdeep.H1All
import Submission.NK.GlobalCFTdeep.SecondInequalityFinal
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.GlobalCFTdeep


set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped NumberField RestrictedProduct IsMulCommutative
open NumberField IsDedekindDomain
open CategoryTheory CategoryTheory.Limits
open NK.GlobalCFT

noncomputable section

/-! ### Auxiliary lemmas -/

/-- **An abstract cardinality lemma for an extension of groups.**  Let `φ : B → C` and
`ψ : A → B` be maps with `φ b = 0 ↔ ∃ a, ψ a = b` (`ψ` has range the kernel of `φ`), with `φ`
additive.  If `A` and `C` are finite, then so is `B`, and `|B| ≤ |A| · |C|`: choosing a section of
`φ` on its range, `B` maps injectively into `{b | φ b = 0} × range φ`, the first factor is a
quotient of `A` and the second a subset of `C`. -/
theorem finite_card_le_of_ker_eq_range {A B C : Type*} [AddCommGroup A] [AddCommGroup B]
    [AddCommGroup C] (φ : B → C) (ψ : A → B) (hφ : ∀ x y : B, φ (x - y) = φ x - φ y)
    (h : ∀ b : B, φ b = 0 ↔ ∃ a : A, ψ a = b) (hA : Finite A) (hC : Finite C) :
    Finite B ∧ Nat.card B ≤ Nat.card A * Nat.card C := by
  classical
  have hsurj : Function.Surjective (fun a : A => (⟨ψ a, Set.mem_range_self a⟩ : Set.range ψ)) := by
    rintro ⟨b, a, ha⟩
    exact ⟨a, Subtype.ext ha⟩
  let eK : {b : B // φ b = 0} ≃ Set.range ψ :=
    { toFun := fun b => ⟨b.1, (h b.1).mp b.2⟩
      invFun := fun y => ⟨y.1, (h y.1).mpr y.2⟩
      left_inv := fun b => Subtype.ext rfl
      right_inv := fun y => Subtype.ext rfl }
  have hKfin : Finite {b : B // φ b = 0} :=
    (Equiv.finite_iff eK).mpr (Finite.of_surjective _ hsurj)
  have hKcard : Nat.card {b : B // φ b = 0} ≤ Nat.card A := by
    rw [Nat.card_congr eK]
    exact Nat.card_le_card_of_surjective _ hsurj
  have hRfin : Finite (Set.range φ) :=
    Finite.of_injective (fun x : Set.range φ => (x : C)) Subtype.coe_injective
  let σ : Set.range φ → B := fun y => Classical.choose y.2
  have hσ : ∀ y : Set.range φ, φ (σ y) = y.1 := fun y => Classical.choose_spec y.2
  let yφ : B → Set.range φ := fun b => ⟨φ b, Set.mem_range_self b⟩
  let Ψ : B → {b : B // φ b = 0} × Set.range φ := fun b =>
    (⟨b - σ (yφ b), by rw [hφ, hσ (yφ b)]; exact sub_self _⟩, yφ b)
  have hΨ : Function.Injective Ψ := by
    intro b₁ b₂ hb
    have h2 : yφ b₁ = yφ b₂ := congrArg Prod.snd hb
    have hσeq : σ (yφ b₁) = σ (yφ b₂) := congrArg σ h2
    have h1 : b₁ - σ (yφ b₁) = b₂ - σ (yφ b₂) := Subtype.ext_iff.mp (congrArg Prod.fst hb)
    rw [hσeq] at h1
    have h3 : b₁ - σ (yφ b₂) + σ (yφ b₂) = b₂ - σ (yφ b₂) + σ (yφ b₂) := by rw [h1]
    simpa using h3
  haveI := hKfin
  haveI := hRfin
  refine ⟨Finite.of_injective Ψ hΨ, ?_⟩
  have hle1 : Nat.card B ≤ Nat.card ({b : B // φ b = 0} × Set.range φ) :=
    Nat.card_le_card_of_injective Ψ hΨ
  have hcard : Nat.card ({b : B // φ b = 0} × Set.range φ)
      = Nat.card {b : B // φ b = 0} * Nat.card (Set.range φ) := Nat.card_prod _ _
  have hRcard : Nat.card (Set.range φ) ≤ Nat.card C :=
    Nat.card_le_card_of_injective (fun x : Set.range φ => (x : C)) Subtype.coe_injective
  calc Nat.card B ≤ Nat.card ({b : B // φ b = 0} × Set.range φ) := hle1
    _ = Nat.card {b : B // φ b = 0} * Nat.card (Set.range φ) := hcard
    _ ≤ Nat.card A * Nat.card C := Nat.mul_le_mul hKcard hRcard

/-- If `Nat.card X = n ≠ 0` then `X` is finite (because `Nat.card` of an infinite type is `0`). -/
theorem finite_of_natCard_eq {X : Type*} {n : ℕ} (h : Nat.card X = n) (hn : n ≠ 0) : Finite X := by
  rw [← not_infinite_iff_finite]
  intro hinf
  rw [Nat.card_eq_zero.mpr (Or.inr hinf)] at h
  exact hn h.symm

/-- **The cyclic case of prime degree.**  For a cyclic `L/K` of prime degree the class-formation
axioms at that level (Milne, *CFT*, Lemma 5.2, which this chapter proves unconditionally from the
Herbrand-quotient computation and the second inequality) compute `|H²(Gal(L/K), C_L)| = [L : K]`;
in particular `H²` is finite of order at most `[L : K]`. -/
theorem finite_card_le_of_isCyclic_prime_card {K L : Type} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [IsCyclic (L ≃ₐ[K] L)] [Fact (Nat.Prime (Nat.card (L ≃ₐ[K] L)))] :
    Finite (groupCohomology (IdeleClassGroup.rep K L) 2) ∧
      Nat.card (groupCohomology (IdeleClassGroup.rep K L) 2) ≤ Nat.card (L ≃ₐ[K] L) := by
  have h := cyclicPrimeAxioms.axioms_hold (K := K) (L := L)
  have h2 := h.h2_card ⊤
  rw [natCard_groupCohomology_top (IdeleClassGroup.rep K L), Subgroup.card_top] at h2
  have hne : Nat.card (L ≃ₐ[K] L) ≠ 0 :=
    Nat.card_ne_zero.mpr ⟨⟨1⟩, inferInstance⟩
  exact ⟨finite_of_natCard_eq h2 hne, le_of_eq h2⟩

/-- **The trivial case**: if `Gal(L/K)` is trivial then `H²(Gal(L/K), C_L) = 0`. -/
theorem finite_card_le_of_subsingleton {K L : Type} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Subsingleton (L ≃ₐ[K] L)] :
    Finite (groupCohomology (IdeleClassGroup.rep K L) 2) ∧
      Nat.card (groupCohomology (IdeleClassGroup.rep K L) 2) ≤ Nat.card (L ≃ₐ[K] L) := by
  have hz : IsZero (groupCohomology (IdeleClassGroup.rep K L) (1 + 1)) :=
    isZero_groupCohomology_succ_of_subsingleton _ 1
  have hsub : Subsingleton (groupCohomology (IdeleClassGroup.rep K L) 2) :=
    ModuleCat.isZero_iff_subsingleton.mp hz
  have hcard : Nat.card (groupCohomology (IdeleClassGroup.rep K L) 2) = 1 :=
    Nat.card_eq_one_iff_unique.mpr ⟨hsub, ⟨0⟩⟩
  have hG : Nat.card (L ≃ₐ[K] L) = 1 := Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, ⟨1⟩⟩
  exact ⟨finite_of_natCard_eq hcard one_ne_zero, by rw [hcard, hG]⟩

end


/-- **The `p`-group case of Milne 5.1(c)**, by strong induction on the order of the group.  For
`Γ = Gal(E/F)` a `p`-group, choose `N ◁ Γ` of index `p` (Milne 5.4), so that the
inflation–restriction sequence `0 → H²(Γ ⧸ N, C_E^N) → H²(Γ, C_E) → H²(N, C_E)` is exact because
`H¹(N, C_E) = 0`.  The middle group is then an extension of `H²(Γ ⧸ N, C_E^N) ≅ H²(Gal(E^N/F), C_{E^N})`
— of order `p` by the cyclic prime-degree case — by a quotient of `H²(N, C_E) ≅ H²(Gal(E/E^N), C_E)`,
which is bounded by `|N|` by the induction hypothesis.  Hence `|H²(Γ, C_E)| ≤ p·|N| = |Γ|`. -/
theorem finite_card_le_of_isPGroup {p : ℕ} [Fact p.Prime] {F E : Type} [Field F] [NumberField F]
    [Field E] [NumberField E] [Algebra F E] [FiniteDimensional F E] [IsGalois F E]
    (hG : IsPGroup p (E ≃ₐ[F] E)) :
    Finite (groupCohomology (IdeleClassGroup.rep F E) 2) ∧
      Nat.card (groupCohomology (IdeleClassGroup.rep F E) 2) ≤ Nat.card (E ≃ₐ[F] E) := by
  classical
  have key : ∀ n, ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
      [Algebra F E] [FiniteDimensional F E] [IsGalois F E],
      Nat.card (E ≃ₐ[F] E) = n → IsPGroup p (E ≃ₐ[F] E) →
      (Finite (groupCohomology (IdeleClassGroup.rep F E) 2) ∧
        Nat.card (groupCohomology (IdeleClassGroup.rep F E) 2) ≤ Nat.card (E ≃ₐ[F] E)) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro F E _ _ _ _ _ _ _ hcard hG
      rcases eq_or_ne n 1 with h1 | h1
      · -- the trivial group
        have hc1 : Nat.card (E ≃ₐ[F] E) = 1 := by rw [hcard]; exact h1
        haveI : Subsingleton (E ≃ₐ[F] E) := (Nat.card_eq_one_iff_unique.mp hc1).1
        exact finite_card_le_of_subsingleton
      · rcases eq_or_ne n p with h2 | h2
        · -- the cyclic case of prime degree
          have hcp : Nat.card (E ≃ₐ[F] E) = p := by rw [hcard]; exact h2
          haveI hcyc : IsCyclic (E ≃ₐ[F] E) := isCyclic_of_prime_card hcp
          haveI hfac : Fact (Nat.Prime (Nat.card (E ≃ₐ[F] E))) :=
            ⟨by rw [hcp]; exact Fact.out⟩
          exact finite_card_le_of_isCyclic_prime_card
        · -- the induction step
          haveI hnt : Nontrivial (E ≃ₐ[F] E) := by
            rw [← not_subsingleton_iff_nontrivial]
            intro hsub
            have hc1 : Nat.card (E ≃ₐ[F] E) = 1 := Nat.card_eq_one_iff_unique.mpr ⟨hsub, ⟨1⟩⟩
            rw [hcard] at hc1
            exact h1 hc1
          obtain ⟨N, hNnorm, hNindex⟩ :=
            NK.HassePrinciple.exists_normal_subgroup_index_eq_prime hG hnt
          haveI := hNnorm
          have hmul : Nat.card ↥N * N.index = Nat.card (E ≃ₐ[F] E) := N.card_mul_index
          have hNlt : Nat.card ↥N < n := by
            have hmul' : Nat.card ↥N * p = n := by rw [← hNindex, hmul, hcard]
            have hlt : Nat.card ↥N < Nat.card ↥N * p := by
              calc Nat.card ↥N = Nat.card ↥N * 1 := (mul_one _).symm
                _ < Nat.card ↥N * p :=
                    Nat.mul_lt_mul_of_pos_left (Fact.out : p.Prime).one_lt Nat.card_pos
            rwa [hmul'] at hlt
          set M : IntermediateField F E := IntermediateField.fixedField N with hM
          haveI : NumberField ↥M := inferInstance
          haveI : FiniteDimensional ↥M E := inferInstance
          haveI : IsGalois ↥M E := inferInstance
          have hMcard : Nat.card (E ≃ₐ[↥M] E) = Nat.card ↥N :=
            (Nat.card_congr (IntermediateField.subgroupEquivAlgEquiv N).toEquiv).symm
          -- the induction hypothesis at the sub-extension `E / M`
          have hMN := ih (Nat.card ↥N) hNlt (F := ↥M) (E := E) hMcard
            (IsPGroup.of_equiv (hG.to_subgroup N) (IntermediateField.subgroupEquivAlgEquiv N))
          -- `H²(N, C_E)`
          have hC : Finite (groupCohomology (Rep.res N.subtype (IdeleClassGroup.rep F E)) 2) ∧
              Nat.card (groupCohomology (Rep.res N.subtype (IdeleClassGroup.rep F E)) 2)
                ≤ Nat.card ↥N := by
            have hisoN : groupCohomology (Rep.res N.subtype (IdeleClassGroup.rep F E)) 2 ≅
                groupCohomology (IdeleClassGroup.rep ↥M E) 2 :=
              groupCohomology.mapIso (G := ↥N) (H := (E ≃ₐ[↥M] E))
                (A := IdeleClassGroup.rep ↥M E)
                (B := Rep.res N.subtype (IdeleClassGroup.rep F E))
                (IntermediateField.subgroupEquivAlgEquiv N) (LinearEquiv.refl ℤ _)
                (by intro g; rfl) 2
            refine ⟨(Equiv.finite_iff hisoN.toLinearEquiv.toEquiv).mpr hMN.1, ?_⟩
            calc Nat.card (groupCohomology (Rep.res N.subtype (IdeleClassGroup.rep F E)) 2)
                = Nat.card (groupCohomology (IdeleClassGroup.rep ↥M E) 2) :=
                  Nat.card_congr hisoN.toLinearEquiv.toEquiv
              _ ≤ Nat.card (E ≃ₐ[↥M] E) := hMN.2
              _ = Nat.card ↥N := hMcard
          -- `H²(Γ ⧸ N, C_E^N)`
          haveI : IsGalois F ↥M := IsGalois.of_fixedField_normal_subgroup N
          have hQcard : Nat.card ((E ≃ₐ[F] E) ⧸ N) = p := by
            rw [← Subgroup.index_eq_card]
            exact hNindex
          have hMcardQ : Nat.card (↥M ≃ₐ[F] ↥M) = p := by
            rw [← Nat.card_congr (IsGalois.normalAutEquivQuotient N).toEquiv, hQcard]
          haveI hcyc : IsCyclic (↥M ≃ₐ[F] ↥M) := isCyclic_of_prime_card hMcardQ
          haveI hfac : Fact (Nat.Prime (Nat.card (↥M ≃ₐ[F] ↥M))) :=
            ⟨by rw [hMcardQ]; exact Fact.out⟩
          have hbase := finite_card_le_of_isCyclic_prime_card (K := F) (L := ↥M)
          have hA : Finite (groupCohomology ((IdeleClassGroup.rep F E).quotientToInvariants N) 2) ∧
              Nat.card (groupCohomology ((IdeleClassGroup.rep F E).quotientToInvariants N) 2)
                ≤ p := by
            obtain ⟨hisoQ⟩ :=
              NK.HassePrinciple.repIso_quotientToInvariants_fixedField (K := F) (L := E) N
            have e1 : groupCohomology ((IdeleClassGroup.rep F E).quotientToInvariants N) 2 ≅
                groupCohomology
                  (Rep.res (IsGalois.normalAutEquivQuotient N).toMonoidHom
                    (IdeleClassGroup.rep F ↥M)) 2 :=
              (groupCohomology.functor ℤ ((E ≃ₐ[F] E) ⧸ N) 2).mapIso hisoQ
            have e2 : groupCohomology
                  (Rep.res (IsGalois.normalAutEquivQuotient N).toMonoidHom
                    (IdeleClassGroup.rep F ↥M)) 2 ≅
                groupCohomology (IdeleClassGroup.rep F ↥M) 2 :=
              groupCohomology.mapIso (G := (E ≃ₐ[F] E) ⧸ N) (H := (↥M ≃ₐ[F] ↥M))
                (A := IdeleClassGroup.rep F ↥M)
                (B := Rep.res (IsGalois.normalAutEquivQuotient N).toMonoidHom
                  (IdeleClassGroup.rep F ↥M))
                (IsGalois.normalAutEquivQuotient N) (LinearEquiv.refl ℤ _)
                (by intro g; rfl) 2
            have e : groupCohomology ((IdeleClassGroup.rep F E).quotientToInvariants N) 2 ≃
                groupCohomology (IdeleClassGroup.rep F ↥M) 2 :=
              e1.toLinearEquiv.toEquiv.trans e2.toLinearEquiv.toEquiv
            refine ⟨(Equiv.finite_iff e).mpr hbase.1, ?_⟩
            calc Nat.card (groupCohomology
                    ((IdeleClassGroup.rep F E).quotientToInvariants N) 2)
                = Nat.card (groupCohomology (IdeleClassGroup.rep F ↥M) 2) := Nat.card_congr e
              _ ≤ Nat.card (↥M ≃ₐ[F] ↥M) := hbase.2
              _ = p := hMcardQ
          -- the inflation–restriction exact sequence in degree two
          have h1sub : Subsingleton
              (groupCohomology (Rep.res N.subtype (IdeleClassGroup.rep F E)) 1) :=
            subsingleton_groupCohomology_one_res_ideleClassGroup N
          have hex :=
            Commons.RepresentationTheory.GroupCohomology.H2_inflation_restriction_exact_of_subsingleton_H1
              N (IdeleClassGroup.rep F E) h1sub
          let resL : groupCohomology (IdeleClassGroup.rep F E) 2 →ₗ[ℤ]
              groupCohomology (Rep.res N.subtype (IdeleClassGroup.rep F E)) 2 :=
            ModuleCat.Hom.hom ((groupCohomology.resNatTrans ℤ (G := ↥N) (H := E ≃ₐ[F] E)
              N.subtype 2).app (IdeleClassGroup.rep F E))
          let infL : groupCohomology ((IdeleClassGroup.rep F E).quotientToInvariants N) 2 →ₗ[ℤ]
              groupCohomology (IdeleClassGroup.rep F E) 2 :=
            ModuleCat.Hom.hom ((groupCohomology.infNatTrans ℤ N 2).app (IdeleClassGroup.rep F E))
          have hex' : LinearMap.range infL = LinearMap.ker resL := hex
          have hkey : ∀ b : groupCohomology (IdeleClassGroup.rep F E) 2,
              resL b = 0 ↔ ∃ a : groupCohomology
                ((IdeleClassGroup.rep F E).quotientToInvariants N) 2, infL a = b := by
            intro b
            have h1 : (resL b = 0) ↔ b ∈ LinearMap.ker resL :=
              (LinearMap.mem_ker (f := resL) (y := b)).symm
            have h2 : b ∈ LinearMap.ker resL ↔ b ∈ LinearMap.range infL := by rw [hex']
            have h3 : b ∈ LinearMap.range infL ↔ ∃ a, infL a = b :=
              LinearMap.mem_range (f := infL) (x := b)
            exact h1.trans (h2.trans h3)
          have hmain := finite_card_le_of_ker_eq_range
            (φ := fun b => resL b) (ψ := fun a => infL a)
            (fun x y => map_sub _ _ _) hkey hA.1 hC.1
          refine ⟨hmain.1, ?_⟩
          calc Nat.card (groupCohomology (IdeleClassGroup.rep F E) 2)
              ≤ Nat.card (groupCohomology ((IdeleClassGroup.rep F E).quotientToInvariants N) 2)
                * Nat.card (groupCohomology (Rep.res N.subtype (IdeleClassGroup.rep F E)) 2) :=
                hmain.2
            _ ≤ p * Nat.card ↥N := Nat.mul_le_mul hA.2 hC.2
            _ = Nat.card (E ≃ₐ[F] E) := by
                rw [mul_comm, ← hNindex]
                exact hmul
  exact key (Nat.card (E ≃ₐ[F] E)) rfl hG


/-- **Milne, *Class Field Theory*, Theorem 5.1(c): `H²(Gal(L/K), C_L)` is finite of order dividing
`[L : K]`.**

For every finite Galois extension of number fields, the second group cohomology of the idèle class
group is finite and its order is at most `[L : K]` (equivalently: divides it).  This is the first
half of the classical *fundamental-class* computation; together with the existence of a
fundamental class (an element of order `[L:K]`, the Brauer-group content `H² ≅ Br(L/K)`) it gives
`|H²(Gal(L/K), C_L)| = [L:K]` and hence `NK.GlobalCFTdeep.SecondInequality.HasseFundamentalClass`.

Proof plan (Milne 5.3–5.4, the same reduction as for `H¹ = 0`, which is already unconditional in
this chapter — `NK.GlobalCFTdeep.subsingleton_groupCohomology_one_ideleClassGroup`):

* **cyclic** `G`: for cyclic `G` the Tate cohomology is periodic, so `H²(G,C_L) ≅ Ĥ²(G,C_L) ≅
  Ĥ⁰(G,C_L)`, and the `H⁰`-computation (`NK.GlobalCFT.H0Computation.index_eq_natCard`) together
  with the (unconditional) index formula `index_eq_finrank_of_isCyclic` gives `|H²(G,C_L)| = [L:K]`
  (periodicity `Ĥ² ≅ Ĥ⁰` for cyclic `G` follows by the same dimension-shifting argument as in
  `NK.GlobalCFTdeep.subsingleton_tateCohomology_neg_one_of_subsingleton_groupCohomology_one_cyclic`);
* **`p`-groups**: strong induction on the group order.  For `N ◁ Γ` of index `p` and `M = E^N`, the
  inflation–restriction sequence in degree two,
  `0 → H²(Γ/N, C_M) → H²(Γ, C_E) → H²(N, C_E)`,
  is exact because `H¹(N, C_E) = 0` (unconditional), giving
  `|H²(Γ, C_E)| = |H²(Γ/N, C_M)| · |im(res)| ≤ p · |H²(N, C_E)| = p · |N| = |Γ|`;
* **general** `G`: restriction to a Sylow `p`-subgroup `S` is injective on `p`-primary parts
  (`cores ∘ res = [Γ : S]`; `NU.cor_resNatTrans_comp_apply` in degree two, which is exactly the
  degree where `NK.HassePrinciple/H2_map_injective_of_coprime_index.lean` works), so
  `|H²(Γ,C_E)|_p ≤ |H²(S,C_{E^S})|_p ≤ |S|_p` for every prime `p`; hence `|H²(Γ,C_E)| ≤ |Γ| = [E:F]`. -/
theorem natCard_groupCohomology_two_le_card {K L : Type} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L] :
    Finite (groupCohomology (NK.GlobalCFT.IdeleClassGroup.rep K L) 2) ∧
      Nat.card (groupCohomology (NK.GlobalCFT.IdeleClassGroup.rep K L) 2) ≤
        Nat.card (L ≃ₐ[K] L) := by
  classical
  by_cases h1 : Nat.card (L ≃ₐ[K] L) = 1
  · haveI : Subsingleton (L ≃ₐ[K] L) := (Nat.card_eq_one_iff_unique.mp h1).1
    exact finite_card_le_of_subsingleton
  · let n : ℕ := Nat.card (L ≃ₐ[K] L)
    have hn0 : n ≠ 0 := Nat.card_ne_zero.mpr ⟨⟨1⟩, inferInstance⟩
    let ι : Type := {p : ℕ // p ∈ n.primeFactors}
    haveI : Fintype ι := inferInstance
    have hSylow : ∀ p : ℕ, p.Prime → Nonempty (Sylow p (L ≃ₐ[K] L)) := by
      intro p hp
      haveI : Fact (Nat.Prime p) := ⟨hp⟩
      exact Sylow.nonempty
    let S : (i : ι) → Sylow i.1 (L ≃ₐ[K] L) := fun i =>
      Classical.choice (hSylow i.1 (Nat.prime_of_mem_primeFactors i.2))
    let T : ι → Subgroup (L ≃ₐ[K] L) := fun i => (S i : Subgroup (L ≃ₐ[K] L))
    haveI hfacti : ∀ i : ι, Fact (Nat.Prime i.1) :=
      fun i => ⟨Nat.prime_of_mem_primeFactors i.2⟩
    -- each Sylow subgroup gives a finite `H²` of order at most its own order
    have hfac : ∀ i : ι, Finite (groupCohomology
          (Rep.res (T i).subtype (IdeleClassGroup.rep K L)) 2) ∧
        Nat.card (groupCohomology
          (Rep.res (T i).subtype (IdeleClassGroup.rep K L)) 2) ≤ Nat.card ↥(T i) := by
      intro i
      let K' : IntermediateField K L := IntermediateField.fixedField (T i)
      haveI : NumberField ↥K' := inferInstance
      haveI : FiniteDimensional ↥K' L := inferInstance
      haveI : IsGalois ↥K' L := inferInstance
      have hpg : IsPGroup i.1 (L ≃ₐ[↥K'] L) :=
        IsPGroup.of_equiv (S i).isPGroup' (IntermediateField.subgroupEquivAlgEquiv (T i))
      have h := finite_card_le_of_isPGroup (p := i.1) hpg
      have hiso : groupCohomology (Rep.res (T i).subtype (IdeleClassGroup.rep K L)) 2 ≅
          groupCohomology (IdeleClassGroup.rep ↥K' L) 2 :=
        groupCohomology.mapIso (G := ↥(T i)) (H := (L ≃ₐ[↥K'] L))
          (A := IdeleClassGroup.rep ↥K' L)
          (B := Rep.res (T i).subtype (IdeleClassGroup.rep K L))
          (IntermediateField.subgroupEquivAlgEquiv (T i)) (LinearEquiv.refl ℤ _)
          (by intro g; rfl) 2
      refine ⟨(Equiv.finite_iff hiso.toLinearEquiv.toEquiv).mpr h.1, ?_⟩
      calc Nat.card (groupCohomology (Rep.res (T i).subtype (IdeleClassGroup.rep K L)) 2)
          = Nat.card (groupCohomology (IdeleClassGroup.rep ↥K' L) 2) :=
            Nat.card_congr hiso.toLinearEquiv.toEquiv
        _ ≤ Nat.card (L ≃ₐ[↥K'] L) := h.2
        _ = Nat.card ↥(T i) :=
            (Nat.card_congr (IntermediateField.subgroupEquivAlgEquiv (T i)).toEquiv).symm
    -- the product of the restrictions to the Sylow subgroups is injective
    let F : groupCohomology (IdeleClassGroup.rep K L) 2 →
        ((i : ι) → groupCohomology (Rep.res (T i).subtype (IdeleClassGroup.rep K L)) 2) :=
      fun x i => (ConcreteCategory.hom ((groupCohomology.resNatTrans ℤ (G := ↥(T i))
        (H := L ≃ₐ[K] L) (T i).subtype 2).app (IdeleClassGroup.rep K L))) x
    have hkey : ∀ z : groupCohomology (IdeleClassGroup.rep K L) 2,
        (∀ i, F z i = 0) → z = 0 := by
      intro z hz
      have hdvd_idx : ∀ i : ι, addOrderOf z ∣ (T i).index := by
        intro i
        have hc := NU.cor_resNatTrans_comp_apply (T i) (IdeleClassGroup.rep K L) 2 z
        have h2 : (NU.cor (T i) (IdeleClassGroup.rep K L) 2) (F z i) = (T i).index • z :=
          show (ConcreteCategory.hom ((groupCohomology.resNatTrans ℤ (G := ↥(T i))
              (H := L ≃ₐ[K] L) (T i).subtype 2).app (IdeleClassGroup.rep K L) ≫
              NU.cor (T i) (IdeleClassGroup.rep K L) 2)) z = (T i).index • z from hc
        rw [hz i, map_zero] at h2
        exact addOrderOf_dvd_iff_nsmul_eq_zero.mpr h2.symm
      have hdvd_n : addOrderOf z ∣ n := by
        have hz0 : n • z = 0 := by
          have h := Commons.RepresentationTheory.GroupCohomology.natCard_nsmul_groupCohomology_succ_eq_zero
            (G := L ≃ₐ[K] L) (IdeleClassGroup.rep K L) 1 z
          simpa only [n] using h
        exact addOrderOf_dvd_iff_nsmul_eq_zero.mpr hz0
      have hd1 : addOrderOf z = 1 := by
        by_contra hne
        obtain ⟨q, hqprime, hqdvd⟩ := Nat.exists_prime_and_dvd hne
        have hq_dvd_n : q ∣ n := hqdvd.trans hdvd_n
        have hmem : q ∈ n.primeFactors :=
          Nat.mem_primeFactors.mpr ⟨hqprime, hq_dvd_n, hn0⟩
        haveI : Fact (Nat.Prime q) := ⟨hqprime⟩
        exact Sylow.not_dvd_index (S ⟨q, hmem⟩)
          (hqdvd.trans (hdvd_idx ⟨q, hmem⟩))
      exact AddMonoid.addOrderOf_eq_one_iff.mp hd1
    have hFinj : Function.Injective F := by
      intro x y hxy
      have h0 : x - y = 0 := by
        refine hkey (x - y) (fun i => ?_)
        have h1 : F x i - F y i = 0 := sub_eq_zero.mpr (congrFun hxy i)
        rw [← h1]
        exact map_sub (ConcreteCategory.hom ((groupCohomology.resNatTrans ℤ (G := ↥(T i))
          (H := L ≃ₐ[K] L) (T i).subtype 2).app (IdeleClassGroup.rep K L))) x y
      exact sub_eq_zero.mp h0
    haveI : ∀ i : ι, Finite (groupCohomology
        (Rep.res (T i).subtype (IdeleClassGroup.rep K L)) 2) := fun i => (hfac i).1
    have hprod : (∏ i : ι, Nat.card ↥(T i)) = n := by
      have h1 : ∀ i : ι, Nat.card ↥(T i) = i.1 ^ n.factorization i.1 :=
        fun i => Sylow.card_eq_multiplicity (S i)
      calc (∏ i : ι, Nat.card ↥(T i))
          = ∏ i : ι, i.1 ^ n.factorization i.1 := Finset.prod_congr rfl (fun i _ => h1 i)
        _ = ∏ p ∈ n.primeFactors, p ^ n.factorization p := by
            have huniv : (Finset.univ : Finset ι) = n.primeFactors.attach := by
              ext x
              exact iff_of_true (Finset.mem_univ x) (Finset.mem_attach _ x)
            rw [show (∏ i : ι, i.1 ^ n.factorization i.1)
                = (Finset.univ : Finset ι).prod (fun i => i.1 ^ n.factorization i.1)
                from rfl, huniv]
            exact Finset.prod_attach n.primeFactors (fun p => p ^ n.factorization p)
        _ = n := by
            rw [← Nat.prod_factorization_eq_prod_primeFactors (fun p e => p ^ e)]
            exact Nat.prod_factorization_pow_eq_self hn0
    refine ⟨Finite.of_injective F hFinj, ?_⟩
    calc Nat.card (groupCohomology (IdeleClassGroup.rep K L) 2)
        ≤ Nat.card ((i : ι) → groupCohomology
            (Rep.res (T i).subtype (IdeleClassGroup.rep K L)) 2) :=
          Nat.card_le_card_of_injective F hFinj
      _ = ∏ i : ι, Nat.card (groupCohomology
            (Rep.res (T i).subtype (IdeleClassGroup.rep K L)) 2) := Nat.card_pi
      _ ≤ ∏ i : ι, Nat.card ↥(T i) := Finset.prod_le_prod' (fun i _ => (hfac i).2)
      _ = n := hprod
      _ = Nat.card (L ≃ₐ[K] L) := rfl

end NK.GlobalCFTdeep
