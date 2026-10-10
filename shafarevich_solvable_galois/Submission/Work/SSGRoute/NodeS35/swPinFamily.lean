import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.SSGRoute.NodeS35.swPinBasic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The pinned Frobenius values of the §4 shoe box

For a `HistK` history `f` of the Schmidt--Wingberg recursion, every stage `m` and every
`σ ∈ Gal(K|k)` determine a *well-defined* value

  `pinValue m σ ∈ ZMod p`

— the value of the Kummer cochain `χ_{b_m}` at any element of `decomp k (galLift K σ • Q_m)` whose
restriction to the Kummer level `K((b_m)^{1/p})` is the Frobenius at the prime of `↥K` below the
sibling place.  Well-definedness is `chi_eq_of_restrictNormalHom_eq` (`swPinBasic`); the value is
*computed* by the descended Kummer character `hChar` at that Frobenius, so that no choice of
Frobenius element is needed anywhere in the shoe box.

The file also produces the pigeonhole selection `∃ i < j, ∀ σ, pinValue j σ = pinValue i σ`, which is
the shoe-box matching consumed by the §4(b) chain, and records the confinement `histK_killing` of the
history's classes at the sibling places.
-/

namespace Work.SSGRoute.NodeS35

open _root_.SSGRoute
open Work.SSGRoute.ZDataMup.LTRecFamHonest
open Work.SSGRoute.ZDataMup

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000

variable {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] [IsAlgClosed Ω]

section Family

variable {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
  [IsSepClosure ↥K Ω]

/-- **`IsSplitIn` descends along an inclusion of the levels.** -/
theorem isSplitIn_of_le {K N : IntermediateField k Ω} (hKN : K ≤ N) {A : ValuationSubring Ω}
    (h : SSGRoute.IsSplitIn k N A) : SSGRoute.IsSplitIn k K A := by
  intro σ hσ
  have h' : ∀ x ∈ N, σ x = x :=
    (IntermediateField.mem_fixingSubgroup_iff N σ).mp (h hσ)
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  exact h' x (hKN hx)

/-- **A pinned Frobenius at the Kummer level of `b_m`.**  Given a finite place `A` at which the
Kummer cochain of the `m`-th element of the history kills the inertia, there is
`ψ ∈ decomp k A ⊓ K.fixingSubgroup` whose restriction to `K((b_m)^{1/p})` is the Frobenius at the
prime of `↥K` below `A`. -/
theorem exists_pinned (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (f : ℕ → (ValuationSubring Ω × (↥K)ˣ)) (m : ℕ) (A : ValuationSubring Ω)
    (hA : SSGRoute.IsFinPlace k A)
    [FiniteDimensional ↥K ↥(hLevel (Ω := Ω) (K := K) (p := p) (f m).2)]
    [IsGalois ↥K ↥(hLevel (Ω := Ω) (K := K) (p := p) (f m).2)]
    [Normal ↥K ↥(hLevel (Ω := Ω) (K := K) (p := p) (f m).2)]
    [NumberField ↥(hLevel (Ω := Ω) (K := K) (p := p) (f m).2)]
    (hkill : ∀ u ∈ K.fixingSubgroup, SSGRoute.IsInertia k A u →
      Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ (f m).2 u = 0) :
    ∃ p' : {ψ : Ω ≃ₐ[k] Ω // ψ ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup},
      AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω)
        ↥(hLevel (Ω := Ω) (K := K) (p := p) (f m).2)
        ((IntermediateField.fixingSubgroupEquiv K) ⟨p'.1, (Subgroup.mem_inf.mp p'.2).2⟩) =
      NK.Chebotarev.frobAtPrime (K := ↥K)
        (L := ↥(hLevel (Ω := Ω) (K := K) (p := p) (f m).2))
        (Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K) A hA) := by
  have hζ' : IsPrimitiveRoot (⟨ζ, hζK⟩ : ↥K) p :=
    Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ
  have hunr : NK.HeckeL.IsUnramifiedIn (K := ↥K)
      (L := ↥(hLevel (Ω := Ω) (K := K) (p := p) (f m).2))
      (Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K) A hA) :=
    Work.SSGRoute.H9.swIsUnramifiedIn_hLevel_of_kills_inertia (K := K) (p := p) ζ hζ hζK
      (f m).2 A hA hkill
  obtain ⟨ψ, hψ, hmem, hpin⟩ := Work.SSGRoute.NodeS34.swFrobLift (K := K) (Ω := Ω)
    (hLevel (Ω := Ω) (K := K) (p := p) (f m).2)
    (hLevel_isMulCommutative (Ω := Ω) (K := K) (p := p) ⟨ζ, hζK⟩ hζ' (f m).2)
    A hA (Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K) A hA)
    (Work.SSGRoute.ZDataMup.OddForm.oddPrime_spec (K := K) (A := A) hA) hunr
  exact ⟨⟨ψ, Subgroup.mem_inf.mpr ⟨hmem, hψ⟩⟩, hpin⟩

/-- **The pinned Frobenius value of a stage.**  At the sibling `galLift K σ • Q_m`, the value of
`χ_{b_m}` at any pinned Frobenius is `pinValue m σ`; it is computed by the descended Kummer
character, so it is a definite element of `ZMod p`. -/
noncomputable def pinValue (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (f : ℕ → (ValuationSubring Ω × (↥K)ˣ)) (hfin : ∀ m, SSGRoute.IsFinPlace k ((f m).1))
    (m : ℕ) (σ : K ≃ₐ[k] K) : ZMod p := by
  by_cases h : σ = 1
  · exact 0
  · haveI hfd : FiniteDimensional ↥K ↥(hLevel (Ω := Ω) (K := K) (p := p) (f m).2) :=
      hLevel_finiteDimensional (Ω := Ω) (K := K) (p := p) ⟨ζ, hζK⟩
        (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ) (f m).2
    haveI hgal : IsGalois ↥K ↥(hLevel (Ω := Ω) (K := K) (p := p) (f m).2) :=
      hLevel_isGalois (Ω := Ω) (K := K) (p := p) ⟨ζ, hζK⟩
        (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ) (f m).2
    haveI hnf : NumberField ↥(hLevel (Ω := Ω) (K := K) (p := p) (f m).2) :=
      hLevel_numberField (Ω := Ω) (K := K) (p := p) ⟨ζ, hζK⟩
        (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ) (f m).2
    exact Multiplicative.ofAdd.symm
      (Work.SSGRoute.ZDataMup.OddForm.hChar (K := K) (p := p) (⟨ζ, hζK⟩ : ↥K)
        (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ) (f m).2 le_rfl
        (NK.Chebotarev.frobAtPrime (K := ↥K)
          (L := ↥(hLevel (Ω := Ω) (K := K) (p := p) (f m).2))
          (Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K)
            (Work.SSGRoute.ZDataMup.galLift K σ • (f m).1)
            ((Work.SSGRoute.isFinPlace_smul_iff (k := k) ((f m).1)
              (Work.SSGRoute.ZDataMup.galLift K σ)).mpr (hfin m)))))

/-- **The characteristic property of `pinValue`.**  Every element of `decomp k (galLift K σ • Q_m)`
that fixes `K` and whose restriction to `K((b_m)^{1/p})` is the Frobenius at the prime below the
sibling place has Kummer value `pinValue m σ`. -/
theorem pinValue_eq (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (f : ℕ → (ValuationSubring Ω × (↥K)ˣ)) (hfin : ∀ m, SSGRoute.IsFinPlace k ((f m).1))
    (m : ℕ) (σ : K ≃ₐ[k] K) (hσ : σ ≠ 1)
    [FiniteDimensional ↥K ↥(hLevel (Ω := Ω) (K := K) (p := p) (f m).2)]
    [IsGalois ↥K ↥(hLevel (Ω := Ω) (K := K) (p := p) (f m).2)]
    [Normal ↥K ↥(hLevel (Ω := Ω) (K := K) (p := p) (f m).2)]
    [NumberField ↥(hLevel (Ω := Ω) (K := K) (p := p) (f m).2)]
    (ψ : Ω ≃ₐ[k] Ω) (hψ : ψ ∈ SSGRoute.decomp k (Work.SSGRoute.ZDataMup.galLift K σ • (f m).1)
      ⊓ K.fixingSubgroup)
    (hpin : AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω)
        ↥(hLevel (Ω := Ω) (K := K) (p := p) (f m).2)
        ((IntermediateField.fixingSubgroupEquiv K) ⟨ψ, (Subgroup.mem_inf.mp hψ).2⟩) =
      NK.Chebotarev.frobAtPrime (K := ↥K)
        (L := ↥(hLevel (Ω := Ω) (K := K) (p := p) (f m).2))
        (Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K)
          (Work.SSGRoute.ZDataMup.galLift K σ • (f m).1)
          ((Work.SSGRoute.isFinPlace_smul_iff (k := k) ((f m).1)
            (Work.SSGRoute.ZDataMup.galLift K σ)).mpr (hfin m)))) :
    Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ (f m).2 ψ = pinValue (K := K) (p := p)
      ζ hζ hζK f hfin m σ := by
  classical
  haveI hfd : FiniteDimensional ↥K ↥(hLevel (Ω := Ω) (K := K) (p := p) (f m).2) :=
    hLevel_finiteDimensional (Ω := Ω) (K := K) (p := p) ⟨ζ, hζK⟩
      (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ) (f m).2
  haveI hgal : IsGalois ↥K ↥(hLevel (Ω := Ω) (K := K) (p := p) (f m).2) :=
    hLevel_isGalois (Ω := Ω) (K := K) (p := p) ⟨ζ, hζK⟩
      (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ) (f m).2
  haveI hnf : NumberField ↥(hLevel (Ω := Ω) (K := K) (p := p) (f m).2) :=
    hLevel_numberField (Ω := Ω) (K := K) (p := p) ⟨ζ, hζK⟩
      (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ) (f m).2
  have hkey := Work.SSGRoute.ZDataMup.OddForm.hChar_apply (K := K) (p := p)
    (⟨ζ, hζK⟩ : ↥K) (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ) (f m).2
    (M := hLevel (Ω := Ω) (K := K) (p := p) (f m).2) le_rfl
    ((IntermediateField.fixingSubgroupEquiv K) ⟨ψ, (Subgroup.mem_inf.mp hψ).2⟩)
  rw [Work.SSGRoute.ZSplit.nodeKummerCocharZMod_apply (K := K) (ζ := ζ) (hζK := hζK) (hζ := hζ)
    (β := (f m).2) (Subgroup.mem_inf.mp hψ).2]
  rw [pinValue, dif_neg hσ]
  rw [hpin] at hkey
  simpa using (congrArg Multiplicative.ofAdd.symm hkey).symm

/-- **The inertia-killing of the history's classes at the sibling places.** -/
theorem histK_killing {K N : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
    [FiniteDimensional k N] [IsGalois k N] [NumberField ↥K] [IsSepClosure ↥K Ω]
    (hp : p ≠ 2) (hKN : K ≤ N) (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (S : Finset (ValuationSubring Ω)) (y : (Ω ≃ₐ[k] Ω) → ZMod p)
    (hyT : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → y σ = 0)
    (f : ℕ → (ValuationSubring Ω × (↥K)ˣ))
    (hf : Work.SSGRoute.H9.HistK (p := p) K N ζ hζ hζK S y f) :
    ∀ m σ, σ ≠ 1 → ∀ u ∈ K.fixingSubgroup,
      SSGRoute.IsInertia k (Work.SSGRoute.ZDataMup.galLift K σ • (f m).1) u →
        Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ (f m).2 u = 0 := by
  intro m σ hσ u huK huI
  have hconf := Work.SSGRoute.H9.swHistChi_confinement_proved (K := K) (N := N) hp ζ hζ hζK S y
    hyT f hf m
  refine hconf _ ((Work.SSGRoute.isFinPlace_smul_iff (k := k) ((f m).1)
    (Work.SSGRoute.ZDataMup.galLift K σ)).mpr (hf.1 m)) ?_ u huK huI
  exact Work.SSGRoute.ZDataMup.siblingPlace_not_gesKConj (K := K) hσ
    (isSplitIn_of_le (K := K) (N := N) hKN (hf.2.1 m))

/-- **The shoe-box pigeonhole on the pinned Frobenius values.**  There are stages `i < j` whose
pinned-value vectors agree at every `σ`. -/
theorem pinValue_pigeonhole (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (f : ℕ → (ValuationSubring Ω × (↥K)ˣ)) (hfin : ∀ m, SSGRoute.IsFinPlace k ((f m).1))
    [Fintype (K ≃ₐ[k] K)] :
    ∃ i j : ℕ, i < j ∧ ∀ σ : K ≃ₐ[k] K,
      pinValue (K := K) (p := p) ζ hζ hζK f hfin j σ
        = pinValue (K := K) (p := p) ζ hζ hζK f hfin i σ := by
  classical
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  haveI : Fintype (ZMod p) := ZMod.fintype p
  obtain ⟨i, j, hij, heq⟩ := Work.SSGRoute.pigeonhole_two_eq
    (fun m : ℕ => fun σ : K ≃ₐ[k] K => pinValue (K := K) (p := p) ζ hζ hζK f hfin m σ)
  exact ⟨i, j, hij, fun σ => (congrFun heq σ).symm⟩

end Family

end Work.SSGRoute.NodeS35
