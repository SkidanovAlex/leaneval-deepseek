import Mathlib
import Submission.NK.Reconstruct.galToGamma
import Submission.NK.Reconstruct.frobElementAt
import Submission.NK.Chebotarev.Basic
import Submission.NeukirchUchida.Local.Restriction
import Submission.NK.Reconstruct.padicValNat_ramificationIdx_le

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 4000000

namespace NK.Reconstruct

open scoped Pointwise NumberField

/-!
# The ℓ-part of the inertia at a prime of residue characteristic `p ≠ ℓ`

This file proves `NK.Reconstruct.inertia_ellPart_pow_eq_one`, the input used by
`NK.Reconstruct.frobUniquenessAwayFromL`.

The proof reduces the statement about the abelianisation `Abelianization Gal(L/K)` of an arbitrary
finite Galois level to the case where the level is abelian of `ℓ`-power order: the kernel
`H` of the composite `Gal(L/K) →* Abelianization Gal(L/K) →* ` (its `ℓ`-primary part) defines the
subfield `A = L^H`, which is abelian over `K` with `Gal(A/K) ≅ (Abelianization Gal(L/K))_ℓ`, and
under this isomorphism the ℓ-primary part of the class of `h` corresponds to the restriction of `h`
to `A`.  Since `h` acts trivially on the residue field at `P`, its restriction to `A` lies in the
inertia subgroup at `P ∩ A`, whose order is the ramification index `e`; the ℓ-part of `e` divides
the ℓ-part of `q - 1` by `NK.Reconstruct.padicValNat_ramificationIdx_le` (proved from local class
field theory and the Hensel-`ℓ`-divisibility of the principal units,
`NK.Reconstruct.card_dvd_of_isPGroup_quotient_adicUnits`).
-/

section GroupAPI

variable {A : Type*} [CommGroup A] [Finite A]

noncomputable def ellCompHom (ℓ : ℕ) : A →* ellPart A ℓ where
  toFun x := ellComp ℓ x
  map_one' := ellComp_one ℓ
  map_mul' x y := ellComp_mul ℓ x y

theorem ellCompHom_apply (ℓ : ℕ) (x : A) : (ellCompHom ℓ x : A) = ellComp ℓ x := rfl

theorem ellCompHom_surjective (ℓ : ℕ) : Function.Surjective (ellCompHom (A := A) ℓ) := by
  intro y
  refine ⟨(y : A), ?_⟩
  apply Subtype.ext
  exact congrArg Subtype.val (ellComp_eq_self y)

theorem isPGroup_ellPart (ℓ : ℕ) : IsPGroup ℓ ↥(ellPart A ℓ) := by
  intro x
  obtain ⟨n, hn⟩ := (mem_ellPart_iff ℓ (x : A)).mp x.2
  exact ⟨n, Subtype.ext (by simpa using hn)⟩

end GroupAPI

section Abelianization

theorem abelianization_of_surjective {G : Type*} [Group G] :
    Function.Surjective (Abelianization.of : G → Abelianization G) := by
  intro x
  induction x using Quot.inductionOn with
  | _ a => exact ⟨a, (Abelianization.mk_eq_of a).symm⟩

end Abelianization

section PGroup

/-- In a finite group all of whose elements have `ℓ`-power order, every `orderOf` is a power of
`ℓ`. -/
theorem exists_pow_orderOf_eq_of_isPGroup {G : Type*} [Group G] {ℓ : ℕ} [Fact ℓ.Prime]
    (h : IsPGroup ℓ G) (x : G) : ∃ j : ℕ, orderOf x = ℓ ^ j :=
  (Nat.dvd_prime_pow (Fact.out : ℓ.Prime)).mp
    (orderOf_dvd_iff_pow_eq_one.mpr (h x).choose_spec) |>.imp fun _ h => h.2

end PGroup

section Lagrange

theorem orderOf_dvd_card_subgroup {G : Type*} [Group G] {H : Subgroup G} {x : G} (hx : x ∈ H) :
    orderOf x ∣ Nat.card H := by
  have h1 : orderOf (⟨x, hx⟩ : H) ∣ Nat.card H := by
    have h2 := Subgroup.card_subgroup_dvd_card
      (Subgroup.zpowers (⟨x, hx⟩ : H))
    rwa [Nat.card_zpowers] at h2
  rwa [← orderOf_injective H.subtype H.subtype_injective (⟨x, hx⟩ : H)] at h1

end Lagrange


/-- **The ℓ-part of the inertia at a prime of residue characteristic `p ≠ ℓ`, in the abelianisation of a finite Galois level, is annihilated by `ℓ ^ v_ℓ(q - 1)`.**

Let `L/K` be a finite Galois extension of number fields, `𝔮` a prime of `K` whose residue field `𝓞K ⧸ 𝔮` has cardinality `q` and characteristic `p`, `P` a prime of `L` above `𝔮`, and `ℓ ≠ p` a prime number.  If `h : Gal(L/K)` acts trivially on the residue field `𝓞L ⧸ P`, then the `ℓ`-primary component of the class of `h` in the abelianisation `Abelianization Gal(L/K)` has order dividing `ℓ ^ v_ℓ(q - 1)`.

Equivalently: for `p ≠ ℓ` the ℓ-part of the inertia subgroup at `𝔮` inside the ℓ-adic abelianisation `G_K^{ab,(ℓ)}` is finite of order dividing `ℓ^{v_ℓ(q-1)}`; this is what makes the Frobenius element `Frob_𝔮` well defined in the torsion-free quotient `Γ_K^{tf}` for every prime `𝔮 ∤ ℓ` (CoNF, Ch. X §10.3; Shimizu, arXiv:2009.10431, §4).

Route.  The image of the inertia in `Abelianization Gal(L/K)` is the inertia subgroup of the maximal abelian subextension `M = L^{[G,G]}` over `K` at the prime below `P`, so it suffices to treat the case of an abelian extension of number fields; passing to the completion `K_𝔮` and using the classical local structure of the tame inertia (an abelian tamely ramified extension of a `p`-adic field with residue field of size `q` has its ℓ-part of the inertia a quotient of `O^×/(O^×)^{ℓ^n} = μ_{q-1}/(μ_{q-1})^{ℓ^n}`, since `1 + 𝔪` is a pro-`p` group and `p ≠ ℓ`) gives the bound. -/
theorem inertia_ellPart_pow_eq_one {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (𝔮 : NK.Chebotarev.PrimeIdeal K) (P : NK.Chebotarev.PrimeIdeal L)
    (hP : P.asIdeal.LiesOver 𝔮.asIdeal) (ℓ p : ℕ) [Fact ℓ.Prime] [Fact p.Prime]
    (hres : CharP (NumberField.RingOfIntegers K ⧸ 𝔮.asIdeal) p) (hne : p ≠ ℓ)
    (h : Gal(L/K))
    (hh : ∀ x : NumberField.RingOfIntegers L,
      galRestrict (NumberField.RingOfIntegers K) K L (NumberField.RingOfIntegers L) h x - x ∈
        P.asIdeal) :
    (ellComp ℓ (Abelianization.of h)) ^
      (ℓ ^ padicValNat ℓ (Nat.card (NumberField.RingOfIntegers K ⧸ 𝔮.asIdeal) - 1)) = 1 := by
  classical
  letI hmulL : MulSemiringAction Gal(L/K) (𝓞 L) :=
    IsIntegralClosure.MulSemiringAction (𝓞 K) K L (𝓞 L)
  -- 1. `h` lies in the inertia subgroup at `P`
  have hmem : h ∈ Ideal.inertia (G := Gal(L/K)) P.asIdeal := by
    rw [Ideal.inertia, AddSubgroup.mem_inertia]
    intro x
    exact (Submodule.mem_toAddSubgroup _).mp (hh x)
  -- 2. the ℓ-primary projection `ψ`
  let ψ : Gal(L/K) →* ellPart (Abelianization (Gal(L/K))) ℓ :=
    (ellCompHom ℓ).comp (Abelianization.of)
  have hψ : Function.Surjective ψ := by
    intro y
    obtain ⟨x, hx⟩ := ellCompHom_surjective (A := Abelianization (Gal(L/K))) ℓ y
    obtain ⟨g, hg⟩ := abelianization_of_surjective (G := Gal(L/K)) x
    exact ⟨g, by show (ellCompHom ℓ) (Abelianization.of g) = y; rw [hg]; exact hx⟩
  let H : Subgroup Gal(L/K) := ψ.ker
  haveI hHn : H.Normal := ψ.normal_ker
  let A : IntermediateField K L := IntermediateField.fixedField H
  haveI hAgal : IsGalois K A := IsGalois.of_fixedField_normal_subgroup H
  -- 3. the isomorphism `e : Gal(A/K) ≃* the ℓ-part`
  let e₂ : Gal(L/K) ⧸ H ≃* ellPart (Abelianization (Gal(L/K))) ℓ :=
    QuotientGroup.quotientKerEquivOfSurjective ψ hψ
  let e : Gal(↥A/K) ≃* ellPart (Abelianization (Gal(L/K))) ℓ :=
    (IsGalois.normalAutEquivQuotient H).symm.trans e₂
  have hcompat : ∀ σ : Gal(L/K),
      e ((AlgEquiv.restrictNormalHom (F := K) (K₁ := L) A) σ) = ψ σ := by
    intro σ
    have h1 : (IsGalois.normalAutEquivQuotient H) (QuotientGroup.mk' H σ) =
        (AlgEquiv.restrictNormalHom (F := K) (K₁ := L) A) σ :=
      IsGalois.normalAutEquivQuotient_apply H σ
    have h2 : (IsGalois.normalAutEquivQuotient H).symm
        ((AlgEquiv.restrictNormalHom (F := K) (K₁ := L) A) σ) = QuotientGroup.mk' H σ := by
      rw [MulEquiv.symm_apply_eq]
      exact h1.symm
    show e₂ ((IsGalois.normalAutEquivQuotient H).symm
      ((AlgEquiv.restrictNormalHom (F := K) (K₁ := L) A) σ)) = ψ σ
    rw [h2]
    exact QuotientGroup.kerLift_mk ψ σ
  -- 4. the prime `Q = P ∩ A`
  let Q : NK.Chebotarev.PrimeIdeal ↥A := P.under (𝓞 ↥A)
  have hQlies : Q.asIdeal.LiesOver 𝔮.asIdeal := by
    show (P.asIdeal.under (𝓞 ↥A)).LiesOver 𝔮.asIdeal
    refine ⟨?_⟩
    rw [Ideal.under_under, hP.over]
  -- 5. the inertia membership transfers to `A`
  letI hmulA : MulSemiringAction Gal(↥A/K) (𝓞 ↥A) :=
    IsIntegralClosure.MulSemiringAction (𝓞 K) K ↥A (𝓞 ↥A)
  have hmemA : (AlgEquiv.restrictNormalHom (F := K) (K₁ := L) A) h ∈
      Ideal.inertia (G := Gal(↥A/K)) Q.asIdeal := by
    rw [Ideal.inertia, AddSubgroup.mem_inertia]
    intro x
    rw [show (AlgEquiv.restrictNormalHom (F := K) (K₁ := L) A h) • x =
      galRestrict (𝓞 K) K ↥A (𝓞 ↥A)
        (AlgEquiv.restrictNormalHom (F := K) (K₁ := L) A h) x from rfl]
    show galRestrict (𝓞 K) K ↥A (𝓞 ↥A)
        (AlgEquiv.restrictNormalHom (F := K) (K₁ := L) A h) x - x ∈
      P.asIdeal.under (𝓞 ↥A)
    rw [Ideal.under_def, Ideal.mem_comap, map_sub,
      Submission.NeukirchUchida.Local.galRestrict_restrictNormalHom (K := K) (M := L) A h x]
    exact hh (algebraMap (𝓞 ↥A) (𝓞 L) x)
  -- 6. `Gal(A/K)` is an `ℓ`-group
  have hpgA : IsPGroup ℓ (Gal(↥A/K)) :=
    IsPGroup.of_equiv (isPGroup_ellPart (A := Abelianization (Gal(L/K))) ℓ) e.symm
  have hcommA : ∀ a b : Gal(↥A/K), a * b = b * a := by
    intro a b
    refine e.injective ?_
    rw [map_mul, map_mul, mul_comm]
  -- 7. the order bound
  letI hGalA : IsGaloisGroup Gal(↥A/K) (𝓞 K) (𝓞 ↥A) :=
    IsGaloisGroup.of_isFractionRing Gal(↥A/K) (𝓞 K) (𝓞 ↥A) K ↥A
  have hcard : Nat.card ↥(Ideal.inertia (G := Gal(↥A/K)) Q.asIdeal) =
      Q.asIdeal.ramificationIdx (𝓞 K) := by
    rw [Ideal.card_inertia_eq_ramificationIdxIn 𝔮.asIdeal Q.asIdeal,
      Ideal.ramificationIdxIn_eq_ramificationIdx 𝔮.asIdeal Q.asIdeal (Gal(↥A/K))]
  have hP1 : padicValNat ℓ (Q.asIdeal.ramificationIdx (𝓞 K)) ≤
      padicValNat ℓ (Nat.card (𝓞 K ⧸ 𝔮.asIdeal) - 1) :=
    padicValNat_ramificationIdx_le 𝔮 Q hQlies hres hne hcommA
  have hord : orderOf ((AlgEquiv.restrictNormalHom (F := K) (K₁ := L) A) h) ∣
      ℓ ^ padicValNat ℓ (Nat.card (𝓞 K ⧸ 𝔮.asIdeal) - 1) := by
    obtain ⟨j, hj⟩ := exists_pow_orderOf_eq_of_isPGroup hpgA
      ((AlgEquiv.restrictNormalHom (F := K) (K₁ := L) A) h)
    have hdvd : orderOf ((AlgEquiv.restrictNormalHom (F := K) (K₁ := L) A) h) ∣
        Q.asIdeal.ramificationIdx (𝓞 K) := by
      rw [← hcard]
      exact orderOf_dvd_card_subgroup hmemA
    have he0 : Q.asIdeal.ramificationIdx (𝓞 K) ≠ 0 :=
      (Ideal.ramificationIdx_pos Q.asIdeal (𝓞 K)).ne'
    have h3 : j ≤ padicValNat ℓ (Q.asIdeal.ramificationIdx (𝓞 K)) := by
      refine (padicValNat_dvd_iff_le he0).mp ?_
      rw [← hj]
      exact hdvd
    rw [hj]
    exact Nat.pow_dvd_pow ℓ (le_trans h3 hP1)
  have hfinal : ((AlgEquiv.restrictNormalHom (F := K) (K₁ := L) A) h) ^
      (ℓ ^ padicValNat ℓ (Nat.card (𝓞 K ⧸ 𝔮.asIdeal) - 1)) = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp hord
  have hψpow : (ψ h) ^ (ℓ ^ padicValNat ℓ (Nat.card (𝓞 K ⧸ 𝔮.asIdeal) - 1)) = 1 := by
    rw [← hcompat h, ← map_pow, hfinal, map_one]
  simpa [ψ, ellCompHom] using hψpow


end NK.Reconstruct
