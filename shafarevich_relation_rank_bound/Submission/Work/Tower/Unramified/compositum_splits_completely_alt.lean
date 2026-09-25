import Mathlib
import Submission.Work.Tower.Unramified.Basic
import Submission.Work.Tower.Unramified.SplitsCompletelyNF
import Submission.Work.Tower.Unramified.SplitsCompletelyIn_descent
import Submission.Work.Tower.Unramified.splitsCompletelyIn_bot_iff_finrank
import Submission.Work.Tower.Unramified.splitsCompletelyIn_imp_NF
import Submission.Work.Tower.Unramified.splitsCompletelyIn_of_NF
import Submission.Work.Tower.Unramified.splitsCompletelyInNF_of_ramification_inertia
import Submission.Work.Tower.FrattiniLayer.splitsCompletelyIn_of_algHom

/-!
# Complete splitting ascends to the compositum of two intermediate fields

If a prime `𝔭` of `𝓞 F` splits completely in two finite extensions `E₁`, `E₂` of a number field
`F` (both lying in a common finite extension `L`), then it splits completely in the compositum
`E₁ ⊔ E₂`.

The proof reduces to the case that `L/F` is Galois, where complete splitting of `𝔭` in an
intermediate field `E` is equivalent to the assertion that for every prime `𝔮` of `𝓞 L` above
`𝔭` the stabilizer `st(𝔮) ≤ Gal(L/F)` is contained in the subgroup `Gal(L/E)` fixing `E`.
Indeed the ramification index and inertia degree of `𝔮 ∩ 𝓞 E` can be computed as
`e·f = [st(𝔮) : st(𝔮) ∩ Gal(L/E)]` (from `Ideal.card_stabilizer_eq` together with the tower
formulae for `e` and `f`), so it is `1` exactly when `st(𝔮) ⊆ Gal(L/E)`.  The stabilizers of
conjugate primes are conjugate, so the assertion for *all* primes above `𝔭` passes to the
intersection `Gal(L/E₁) ∩ Gal(L/E₂) = Gal(L/E₁E₂)`, giving complete splitting in `E₁ ⊔ E₂`.

An arbitrary finite extension `L/F` is handled by embedding it into the Galois extension
`normalClosure F L (AlgebraicClosure F)`; the property "every prime above `𝔭` has `e = f = 1`" is
transported along the resulting `F`-algebra isomorphism
(`splitsCompletelyIn_of_algHom`).

## Main result

* `Work.Tower.Unramified.compositum_splits_completely_alt`.
-/

open NumberField
open scoped Classical nonZeroDivisors Pointwise

namespace Work.Tower.Unramified

namespace CSCA

/-! ### The Galois case -/

section GaloisCase

variable {F M : Type*} [Field F] [Field M] [NumberField F] [NumberField M] [Algebra F M]
  [FiniteDimensional F M] [IsGalois F M]

/-- The `e·f` of the prime of `𝓞 E` below `𝔮` is the index of the stabilizer of `𝔮` in
`Gal(M/E)` inside the stabilizer of `𝔮` in `Gal(M/F)`. -/
lemma card_stab_eq_ef_mul {E : IntermediateField F M} [FiniteDimensional F E]
    {𝔭 : Ideal (𝓞 F)} [𝔭.IsPrime] {𝔮 : Ideal (𝓞 M)} [𝔮.IsPrime] [𝔮.LiesOver 𝔭] :
    Nat.card (MulAction.stabilizer Gal(M/F) 𝔮) =
      ((𝔮.under (𝓞 ↥E)).ramificationIdx (𝓞 F) * (𝔮.under (𝓞 ↥E)).inertiaDeg (𝓞 F)) *
        Nat.card (MulAction.stabilizer ↥(E.fixingSubgroup) 𝔮) := by
  haveI hGE : IsGaloisGroup ↥(E.fixingSubgroup) ↥E M :=
    IsGaloisGroup.intermediateField Gal(M/F) F M E
  haveI hGER : IsGaloisGroup ↥(E.fixingSubgroup) (𝓞 ↥E) (𝓞 M) :=
    IsGaloisGroup.of_isFractionRing ↥(E.fixingSubgroup) (𝓞 ↥E) (𝓞 M) ↥E M
  haveI hP : (𝔮.under (𝓞 ↥E)).IsPrime := inferInstance
  haveI hL : 𝔮.LiesOver (𝔮.under (𝓞 ↥E)) := ⟨rfl⟩
  have h1 : Nat.card (MulAction.stabilizer Gal(M/F) 𝔮) =
      𝔮.ramificationIdx (𝓞 F) * 𝔮.inertiaDeg (𝓞 F) := by
    rw [Ideal.card_stabilizer_eq 𝔭 𝔮, Ideal.ramificationIdxIn_eq_ramificationIdx 𝔭 𝔮 Gal(M/F),
      Ideal.inertiaDegIn_eq_inertiaDeg 𝔭 𝔮 Gal(M/F)]
  have h2 : Nat.card (MulAction.stabilizer ↥(E.fixingSubgroup) 𝔮) =
      𝔮.ramificationIdx (𝓞 ↥E) * 𝔮.inertiaDeg (𝓞 ↥E) := by
    have hh := Ideal.card_stabilizer_eq (G := ↥(E.fixingSubgroup)) (𝔮.under (𝓞 ↥E)) 𝔮
    rw [Ideal.ramificationIdxIn_eq_ramificationIdx (𝔮.under (𝓞 ↥E)) 𝔮 ↥(E.fixingSubgroup),
      Ideal.inertiaDegIn_eq_inertiaDeg (𝔮.under (𝓞 ↥E)) 𝔮 ↥(E.fixingSubgroup)] at hh
    exact hh
  have h3 : 𝔮.ramificationIdx (𝓞 F) =
      (𝔮.under (𝓞 ↥E)).ramificationIdx (𝓞 F) * 𝔮.ramificationIdx (𝓞 ↥E) :=
    Ideal.ramificationIdx_tower (𝔮.under (𝓞 ↥E)) 𝔮
  have h4 : 𝔮.inertiaDeg (𝓞 F) =
      (𝔮.under (𝓞 ↥E)).inertiaDeg (𝓞 F) * 𝔮.inertiaDeg (𝓞 ↥E) :=
    Ideal.inertiaDeg_tower (𝔮.under (𝓞 ↥E)) 𝔮
  rw [h1, h2, h3, h4]
  ring

lemma stabilizer_subgroupOf (E : IntermediateField F M) (𝔮 : Ideal (𝓞 M)) :
    MulAction.stabilizer ↥(E.fixingSubgroup) 𝔮 =
      (MulAction.stabilizer Gal(M/F) 𝔮).subgroupOf E.fixingSubgroup := by
  ext h
  simp only [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf]
  exact Iff.rfl

/-- The `e·f` formula in intersection form. -/
lemma card_stab_eq_ef_mul' {E : IntermediateField F M} [FiniteDimensional F E]
    {𝔭 : Ideal (𝓞 F)} [𝔭.IsPrime] {𝔮 : Ideal (𝓞 M)} [𝔮.IsPrime] [𝔮.LiesOver 𝔭] :
    Nat.card (MulAction.stabilizer Gal(M/F) 𝔮) =
      ((𝔮.under (𝓞 ↥E)).ramificationIdx (𝓞 F) * (𝔮.under (𝓞 ↥E)).inertiaDeg (𝓞 F)) *
        Nat.card ↥(MulAction.stabilizer Gal(M/F) 𝔮 ⊓ E.fixingSubgroup) := by
  rw [card_stab_eq_ef_mul (E := E) (𝔭 := 𝔭) (𝔮 := 𝔮)]
  congr 1
  rw [stabilizer_subgroupOf]
  have e1 : (MulAction.stabilizer Gal(M/F) 𝔮 ⊓ E.fixingSubgroup).subgroupOf E.fixingSubgroup
      = (MulAction.stabilizer Gal(M/F) 𝔮).subgroupOf E.fixingSubgroup := by
    ext x; simp
  rw [← e1]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right :
    MulAction.stabilizer Gal(M/F) 𝔮 ⊓ E.fixingSubgroup ≤ E.fixingSubgroup)).toEquiv

/-- **Complete splitting in the Galois case.**  For `M/F` finite Galois, if every prime of
`𝓞 Eᵢ` above `𝔭` has ramification index and inertia degree `1` over `𝓞 F`, then the same holds
for every prime of `𝓞 (E₁ ⊔ E₂)` above `𝔭`. -/
theorem galois
    {E₁ E₂ : IntermediateField F M} [FiniteDimensional F E₁] [FiniteDimensional F E₂]
    {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsPrime) (h𝔭0 : 𝔭 ≠ ⊥)
    (h₁ : ∀ P : 𝔭.primesOver (𝓞 ↥E₁),
      P.1.ramificationIdx (𝓞 F) = 1 ∧ P.1.inertiaDeg (𝓞 F) = 1)
    (h₂ : ∀ P : 𝔭.primesOver (𝓞 ↥E₂),
      P.1.ramificationIdx (𝓞 F) = 1 ∧ P.1.inertiaDeg (𝓞 F) = 1) :
    ∀ P : 𝔭.primesOver (𝓞 ↥(E₁ ⊔ E₂)),
      P.1.ramificationIdx (𝓞 F) = 1 ∧ P.1.inertiaDeg (𝓞 F) = 1 := by
  classical
  haveI : 𝔭.IsPrime := h𝔭
  haveI : 𝔭.IsMaximal := h𝔭.isMaximal h𝔭0
  haveI : Finite Gal(M/F) := inferInstance
  obtain ⟨𝔮, h𝔮mem⟩ := (inferInstance : Nonempty (𝔭.primesOver (𝓞 M)))
  haveI : 𝔮.IsPrime := h𝔮mem.1
  haveI : 𝔮.LiesOver 𝔭 := h𝔮mem.2
  have key : ∀ (E : IntermediateField F M) [FiniteDimensional F E],
      (∀ P : 𝔭.primesOver (𝓞 ↥E),
          P.1.ramificationIdx (𝓞 F) = 1 ∧ P.1.inertiaDeg (𝓞 F) = 1) ↔
      (∀ g : Gal(M/F), MulAction.stabilizer Gal(M/F) (g • 𝔮) ≤ E.fixingSubgroup) := by
    intro E _
    constructor
    · intro hE g
      haveI : (g • 𝔮).IsPrime := Ideal.IsPrime.smul g
      haveI : (g • 𝔮).LiesOver 𝔭 := Ideal.LiesOver.smul g
      haveI huu : (g • 𝔮).LiesOver ((g • 𝔮).under (𝓞 ↥E)) := ⟨rfl⟩
      obtain ⟨he, hf⟩ := hE ⟨(g • 𝔮).under (𝓞 ↥E),
        ⟨Ideal.IsPrime.under (𝓞 ↥E) (g • 𝔮), Ideal.LiesOver.tower_bot (g • 𝔮) _ 𝔭⟩⟩
      have hform := card_stab_eq_ef_mul' (F := F) (M := M) (E := E) (𝔭 := 𝔭) (𝔮 := g • 𝔮)
      rw [he, hf, mul_one, one_mul] at hform
      have hle : MulAction.stabilizer Gal(M/F) (g • 𝔮) ⊓ E.fixingSubgroup ≤
          MulAction.stabilizer Gal(M/F) (g • 𝔮) := inf_le_left
      have heq := Subgroup.eq_of_le_of_card_ge hle hform.le
      exact inf_eq_left.mp heq
    · intro hC P
      haveI : P.1.IsMaximal := Ideal.primesOver.isMaximal P
      obtain ⟨𝔮', h𝔮'max, h𝔮'lie⟩ :=
        Ideal.exists_maximal_ideal_liesOver_of_isIntegral (R := 𝓞 ↥E) (S := 𝓞 M) P.1
      haveI : 𝔮'.IsPrime := h𝔮'max.isPrime
      haveI : 𝔮'.LiesOver P.1 := h𝔮'lie
      haveI : 𝔮'.LiesOver 𝔭 := Ideal.LiesOver.trans 𝔮' P.1 𝔭
      obtain ⟨g, hg⟩ := Ideal.exists_smul_eq_of_isGaloisGroup 𝔭 𝔮 𝔮' Gal(M/F)
      have hsub : MulAction.stabilizer Gal(M/F) 𝔮' ≤ E.fixingSubgroup := by
        rw [← hg]; exact hC g
      have hform := card_stab_eq_ef_mul' (F := F) (M := M) (E := E) (𝔭 := 𝔭) (𝔮 := 𝔮')
      rw [← Ideal.over_def 𝔮' P.1, inf_eq_left.mpr hsub] at hform
      have hn : 0 < Nat.card (MulAction.stabilizer Gal(M/F) 𝔮') := Nat.card_pos
      have hmul : P.1.ramificationIdx (𝓞 F) * P.1.inertiaDeg (𝓞 F) = 1 :=
        Nat.mul_right_cancel hn (by rw [one_mul]; exact hform.symm)
      refine ⟨Nat.dvd_one.mp ⟨_, hmul.symm⟩, Nat.dvd_one.mp ⟨_, by rw [mul_comm]; exact hmul.symm⟩⟩
  refine (key (E₁ ⊔ E₂)).mpr ?_
  intro g
  rw [IntermediateField.fixingSubgroup_sup]
  exact le_inf ((key E₁).mp h₁ g) ((key E₂).mp h₂ g)

end GaloisCase

/-! ### Transporting complete splitting along an `F`-algebra isomorphism -/

/-- The `F`-algebra isomorphism `E ≃ₐ[F] E.map ψ` induced by an injective `F`-algebra map. -/
noncomputable def algEquiv_map {F L M : Type*} [Field F] [Field L] [Field M] [Algebra F L]
    [Algebra F M] (ψ : L →ₐ[F] M) (E : IntermediateField F L) : ↥E ≃ₐ[F] ↥(E.map ψ) :=
  (ψ.comp E.val).equivFieldRange.trans (IntermediateField.equivOfEq (by
    ext x
    rw [AlgHom.mem_fieldRange, IntermediateField.mem_map]
    exact ⟨fun ⟨y, hy⟩ => ⟨y, y.2, hy⟩, fun ⟨y, hy, h⟩ => ⟨⟨y, hy⟩, h⟩⟩))

theorem finiteDimensional_map {F L M : Type*} [Field F] [Field L] [Field M] [Algebra F L]
    [Algebra F M] (ψ : L →ₐ[F] M) (E : IntermediateField F L) [FiniteDimensional F ↥E] :
    FiniteDimensional F ↥(E.map ψ) :=
  LinearEquiv.finiteDimensional (algEquiv_map ψ E).toLinearEquiv

/-- Prime ideals above `𝔭` of an intermediate field and of its image under an `F`-embedding
correspond, with equal ramification index and inertia degree. -/
theorem ef_one_of_algHom {F L L' : Type*} [Field F] [NumberField F] [Field L] [NumberField L]
    [Field L'] [NumberField L'] [Algebra F L] [Algebra F L'] [FiniteDimensional F L]
    [FiniteDimensional F L'] {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsPrime) (h𝔭0 : 𝔭 ≠ ⊥)
    (φ : L' →ₐ[F] L)
    (h : ∀ P : 𝔭.primesOver (𝓞 L), P.1.ramificationIdx (𝓞 F) = 1 ∧ P.1.inertiaDeg (𝓞 F) = 1) :
    ∀ P : 𝔭.primesOver (𝓞 L'), P.1.ramificationIdx (𝓞 F) = 1 ∧ P.1.inertiaDeg (𝓞 F) = 1 := by
  haveI : 𝔭.IsPrime := h𝔭
  refine ef_eq_one_of_splitsCompletelyIn h𝔭0 ?_
  refine FrattiniLayer.splitsCompletelyIn_of_algHom 𝔭 φ ?_
  exact splitsCompletelyIn_of_NF h𝔭 h𝔭0 (splitsCompletelyInNF_of_ramification_inertia h𝔭 h)

/-- A prime splitting completely in a number field splits completely in any field carrying an
isomorphic `𝓞 F`-ring of integers via an `F`-algebra map.  (Consequence of the transfer
`ef_one_of_map` below.) -/
theorem ef_one_of_map {F L M : Type*} [Field F] [NumberField F] [Field L] [NumberField L]
    [Field M] [NumberField M] [Algebra F L] [Algebra F M] [FiniteDimensional F L]
    (ψ : L →ₐ[F] M) (E : IntermediateField F L) [FiniteDimensional F ↥E]
    {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsPrime) (h𝔭0 : 𝔭 ≠ ⊥) :
    (∀ P : 𝔭.primesOver (𝓞 ↥E), P.1.ramificationIdx (𝓞 F) = 1 ∧ P.1.inertiaDeg (𝓞 F) = 1) ↔
    (∀ P : 𝔭.primesOver (𝓞 ↥(E.map ψ)),
      P.1.ramificationIdx (𝓞 F) = 1 ∧ P.1.inertiaDeg (𝓞 F) = 1) := by
  haveI : FiniteDimensional F ↥(E.map ψ) := finiteDimensional_map ψ E
  haveI : NumberField ↥(E.map ψ) := NumberField.of_module_finite F _
  constructor
  · intro h P
    exact ef_one_of_algHom h𝔭 h𝔭0 (algEquiv_map ψ E).symm.toAlgHom h P
  · intro h P
    exact ef_one_of_algHom h𝔭 h𝔭0 (algEquiv_map ψ E).toAlgHom h P

end CSCA

/-! ### The compositum theorem -/

/-- **Complete splitting ascends to the compositum.**  If `𝔭` splits completely in `E₁` and in
`E₂`, then it splits completely in `E₁ ⊔ E₂`. -/
theorem compositum_splits_completely_alt {F L : Type*} [Field F] [Field L] [NumberField F]
    [NumberField L] [Algebra F L] [FiniteDimensional F L] {E₁ E₂ : IntermediateField F L}
    [FiniteDimensional F E₁] [FiniteDimensional F E₂]
    {𝔭 : Ideal (NumberField.RingOfIntegers F)}
    (h₁ : Work.Tower.SplitsCompletelyIn F ↥E₁ 𝔭)
    (h₂ : Work.Tower.SplitsCompletelyIn F ↥E₂ 𝔭) :
    Work.Tower.SplitsCompletelyIn F ↥(E₁ ⊔ E₂) 𝔭 := by
  classical
  haveI hn1 : NumberField ↥E₁ := NumberField.of_module_finite F ↥E₁
  haveI hn2 : NumberField ↥E₂ := NumberField.of_module_finite F ↥E₂
  haveI hn12 : NumberField ↥(E₁ ⊔ E₂) := NumberField.of_module_finite F ↥(E₁ ⊔ E₂)
  by_cases h𝔭0 : 𝔭 = ⊥
  · -- Degenerate case: complete splitting at `⊥` forces both degrees to be `1`.
    subst h𝔭0
    rw [splitsCompletelyIn_bot_iff_finrank (L := ↥(E₁ ⊔ E₂))]
    have hf1 : Module.finrank F ↥E₁ = 1 := (splitsCompletelyIn_bot_iff_finrank).mp h₁
    have hf2 : Module.finrank F ↥E₂ = 1 := (splitsCompletelyIn_bot_iff_finrank).mp h₂
    have hE1 : E₁ = ⊥ := IntermediateField.finrank_eq_one_iff.mp hf1
    have hE2 : E₂ = ⊥ := IntermediateField.finrank_eq_one_iff.mp hf2
    rw [hE1, hE2, sup_idem]
    exact IntermediateField.finrank_bot
  · -- Main case: reduce to the Galois case via a Galois closure of `L/F`.
    have h𝔭 : 𝔭.IsPrime := by
      obtain ⟨𝔔, hprime, hlies, -, -⟩ := h₁
      haveI : (𝔔 ⟨0, Module.finrank_pos⟩).IsPrime := hprime _
      haveI : (𝔔 ⟨0, Module.finrank_pos⟩).LiesOver 𝔭 := hlies _
      exact Ideal.isPrime_of_liesOver (𝔔 ⟨0, Module.finrank_pos⟩) 𝔭
    haveI : 𝔭.IsPrime := h𝔭
    -- A Galois extension of `F` containing `L`.
    let ψ : L →ₐ[F] AlgebraicClosure F := IsAlgClosed.lift
    let M : IntermediateField F (AlgebraicClosure F) :=
      IntermediateField.normalClosure F L (AlgebraicClosure F)
    haveI hMfin : FiniteDimensional F ↥M :=
      normalClosure.is_finiteDimensional F L (AlgebraicClosure F)
    haveI hMgal : IsGalois F ↥M := IsGalois.normalClosure F L (AlgebraicClosure F)
    haveI hMnf : NumberField ↥M := NumberField.of_module_finite F ↥M
    -- The induced `F`-embedding of `L` into the Galois closure.
    let ψ' : L →ₐ[F] ↥M :=
      ψ.codRestrict (IntermediateField.toSubalgebra M)
        (fun x => ψ.fieldRange_le_normalClosure ⟨x, rfl⟩)
    -- Transport the hypotheses to the images of `E₁`, `E₂` in `M`.
    haveI hf1 : FiniteDimensional F ↥(E₁.map ψ') := CSCA.finiteDimensional_map ψ' E₁
    haveI hf2 : FiniteDimensional F ↥(E₂.map ψ') := CSCA.finiteDimensional_map ψ' E₂
    haveI hf12 : FiniteDimensional F ↥((E₁ ⊔ E₂).map ψ') :=
      CSCA.finiteDimensional_map ψ' (E₁ ⊔ E₂)
    haveI hn1' : NumberField ↥(E₁.map ψ') := NumberField.of_module_finite F ↥(E₁.map ψ')
    haveI hn2' : NumberField ↥(E₂.map ψ') := NumberField.of_module_finite F ↥(E₂.map ψ')
    haveI hn12' : NumberField ↥((E₁ ⊔ E₂).map ψ') :=
      NumberField.of_module_finite F ↥((E₁ ⊔ E₂).map ψ')
    have hef1 : ∀ P : 𝔭.primesOver (𝓞 ↥(E₁.map ψ')),
        P.1.ramificationIdx (𝓞 F) = 1 ∧ P.1.inertiaDeg (𝓞 F) = 1 :=
      (CSCA.ef_one_of_map ψ' E₁ h𝔭 h𝔭0).mp
        (ef_eq_one_of_splitsCompletelyIn h𝔭0 h₁)
    have hef2 : ∀ P : 𝔭.primesOver (𝓞 ↥(E₂.map ψ')),
        P.1.ramificationIdx (𝓞 F) = 1 ∧ P.1.inertiaDeg (𝓞 F) = 1 :=
      (CSCA.ef_one_of_map ψ' E₂ h𝔭 h𝔭0).mp
        (ef_eq_one_of_splitsCompletelyIn h𝔭0 h₂)
    -- Apply the Galois case.
    have hgal := CSCA.galois (F := F) (M := ↥M) (E₁ := E₁.map ψ') (E₂ := E₂.map ψ')
      h𝔭 h𝔭0 hef1 hef2
    have key : ∀ P : 𝔭.primesOver (𝓞 ↥((E₁ ⊔ E₂).map ψ')),
        P.1.ramificationIdx (𝓞 F) = 1 ∧ P.1.inertiaDeg (𝓞 F) = 1 := by
      rw [IntermediateField.map_sup]
      exact hgal
    -- Convert back to `SplitsCompletelyIn` and descend to `E₁ ⊔ E₂`.
    have hsplit : Work.Tower.SplitsCompletelyIn F ↥((E₁ ⊔ E₂).map ψ') 𝔭 :=
      splitsCompletelyIn_of_NF h𝔭 h𝔭0 (splitsCompletelyInNF_of_ramification_inertia h𝔭 key)
    exact FrattiniLayer.splitsCompletelyIn_of_algHom 𝔭
      (CSCA.algEquiv_map ψ' (E₁ ⊔ E₂)).toAlgHom hsplit

end Work.Tower.Unramified
