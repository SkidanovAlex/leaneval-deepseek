import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.RamificationInertia.Inertia
import Mathlib.RingTheory.RamificationInertia.Ramification
import Submission.Commons.NumberTheory.NumberField.Completion.exists_ringEquiv_adicCompletion_of_residue_ringEquiv
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

namespace Commons.NumberTheory.NumberField.Completion

open IsDedekindDomain.HeightOneSpectrum

/-- **The action of the local Galois group on the residue field.**

Let `L / K` be a finite Galois extension of number fields, `Q` a height one prime of `𝓞 K` and
`q` a height one prime of `𝓞 L` lying over `Q`.  Every `K_Q`-algebra automorphism `σ` of the
`q`-adic completion `L_q` preserves the ring of integers `q.adicCompletionIntegers L`, hence
induces a ring automorphism `ρ σ` of the residue field, and this assignment is a group
homomorphism `ρ`.

Its kernel consists exactly of the automorphisms acting trivially on the residue field, i.e. those
`σ` with `v(σ x - x) < 1` for every integer `x`; its range is exactly the group of ring
automorphisms of the residue field fixing the image of the natural map
`natResidueMap : k_Q → k_q` pointwise. -/
theorem residueActionHom_adicCompletion {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq : q.asIdeal.LiesOver Q.asIdeal) :
    letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
      RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
    ∃ ρ : (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L) →*
        (IsLocalRing.ResidueField (q.adicCompletionIntegers L) ≃+*
          IsLocalRing.ResidueField (q.adicCompletionIntegers L)),
      (∀ σ, σ ∈ ρ.ker ↔ ∀ x : q.adicCompletionIntegers L,
        Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ))
          (σ (x : q.adicCompletion L) - (x : q.adicCompletion L)) < 1) ∧
      ρ.range = Commons.NumberTheory.NumberField.Completion.fixSubgroup
        (Commons.NumberTheory.NumberField.Completion.natResidueMap Q q hq) := by
  classical
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
  let A := Q.adicCompletionIntegers K
  let B := q.adicCompletionIntegers L
  let KK := Q.adicCompletion K
  let LL := q.adicCompletion L
  let ResL := IsLocalRing.ResidueField B
  haveI hLfin : Finite ResL := finite_residueField_adicCompletion L q
  have hpres : ∀ (σ : LL ≃ₐ[KK] LL) (y : LL), σ y ∈ B ↔ y ∈ B :=
    algEquiv_mem_adicCompletionIntegers_iff_adicCompletion Q q hq
  let restr : (LL ≃ₐ[KK] LL) → B ≃+* B := fun σ =>
    { toFun := fun x => ⟨σ (x : LL), (hpres σ (x : LL)).mpr x.2⟩
      invFun := fun y => ⟨σ.symm (y : LL), (hpres σ.symm (y : LL)).mpr y.2⟩
      left_inv := fun x => Subtype.ext (by simp)
      right_inv := fun y => Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by simp)
      map_add' := fun x y => Subtype.ext (by simp) }
  have restr_coe : ∀ (σ : LL ≃ₐ[KK] LL) (x : B), ((restr σ x : B) : LL) = σ (x : LL) :=
    fun _ _ => rfl
  have restr_sub_coe : ∀ (σ : LL ≃ₐ[KK] LL) (x : B),
      ((restr σ x - x : B) : LL) = σ (x : LL) - (x : LL) := by
    intro σ x
    simp [restr_coe]
  have restr_one : restr 1 = 1 := by
    refine RingEquiv.ext fun x => Subtype.ext ?_
    rw [restr_coe]
    exact AlgEquiv.one_apply (x : LL)
  have restr_mul : ∀ σ σ' : LL ≃ₐ[KK] LL, restr (σ * σ') = restr σ * restr σ' := by
    intro σ σ'
    refine RingEquiv.ext fun x => Subtype.ext ?_
    change ((restr (σ * σ')) x : LL) = ((restr σ) ((restr σ') x) : LL)
    rw [restr_coe, restr_coe, restr_coe, AlgEquiv.mul_apply]
  let restrHom : (LL ≃ₐ[KK] LL) →* RingAut B :=
    { toFun := restr, map_one' := restr_one, map_mul' := restr_mul }
  let ρ : (LL ≃ₐ[KK] LL) →* RingAut ResL :=
    (IsLocalRing.ResidueField.mapAut : RingAut B →* RingAut ResL).comp restrHom
  have ρ_apply_residue : ∀ (σ : LL ≃ₐ[KK] LL) (x : B),
      ρ σ (IsLocalRing.residue B x) = IsLocalRing.residue B (restr σ x) := by
    intro σ x
    show IsLocalRing.ResidueField.mapAut (restrHom σ) (IsLocalRing.residue B x) =
      IsLocalRing.residue B (restr σ x)
    rw [IsLocalRing.ResidueField.mapAut_apply, IsLocalRing.ResidueField.mapEquiv_apply,
      IsLocalRing.ResidueField.map_residue]
    rfl
  -- the kernel is the inertia subgroup
  have hker : ∀ σ, σ ∈ ρ.ker ↔ ∀ x : B,
      Valued.v (R := LL) (Γ₀ := WithZero (Multiplicative ℤ))
        (σ (x : LL) - (x : LL)) < 1 := by
    intro σ
    rw [MonoidHom.mem_ker]
    constructor
    · intro h x
      have hx : IsLocalRing.residue B (restr σ x) = IsLocalRing.residue B x := by
        rw [← ρ_apply_residue σ x, h]; rfl
      have hzero : IsLocalRing.residue B (restr σ x - x) = 0 := by
        rw [map_sub, hx, sub_self]
      have hmem : restr σ x - x ∈ IsLocalRing.maximalIdeal B :=
        (IsLocalRing.residue_eq_zero_iff _).mp hzero
      have hval := (Commons.NumberTheory.NumberField.adicCompletionIntegers_mem_maximalIdeal_iff_valued_lt_one
        q (restr σ x - x)).mp hmem
      rwa [restr_sub_coe] at hval
    · intro h
      refine RingEquiv.ext fun r => ?_
      show ρ σ r = r
      obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective r
      rw [ρ_apply_residue σ x]
      have hzero : IsLocalRing.residue B (restr σ x - x) = 0 := by
        rw [map_sub]
        have hmem : restr σ x - x ∈ IsLocalRing.maximalIdeal B := by
          refine (Commons.NumberTheory.NumberField.adicCompletionIntegers_mem_maximalIdeal_iff_valued_lt_one
            q _).mpr ?_
          rw [restr_sub_coe]
          exact h x
        exact (IsLocalRing.residue_eq_zero_iff _).mpr hmem
      have hsub : IsLocalRing.residue B (restr σ x) - IsLocalRing.residue B x = 0 := by
        simpa using hzero
      exact sub_eq_zero.mp hsub
  -- the range is the subgroup fixing the image of the natural residue map
  let ψ := natResidueMap Q q hq
  have hle : ρ.range ≤ fixSubgroup ψ := by
    rintro α ⟨σ, rfl⟩ a
    obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective a
    rw [natResidueMap_residue, ρ_apply_residue]
    congr 1
    exact Subtype.ext (by rw [restr_coe, intCompletionMap_coe]; exact σ.commutes (x : KK))
  have hψinj : Function.Injective ψ := natResidueMap_injective Q q hq
  have hcardFix : Nat.card (fixSubgroup ψ) =
      q.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) := by
    have h := natCard_algEquiv_residueField_eq_inertiaDeg_of_injective Q q hq ψ hψinj
    rw [Nat.card_congr (fixSubgroupMulEquiv ψ).toEquiv]
    exact h
  obtain ⟨I, hI, hIcard⟩ := exists_inertiaSubgroup_adicCompletion_card_eq_ramificationIdx Q q hq
  have hkerI : ρ.ker = I := by
    ext σ
    rw [hker σ, hI σ]
  have hGcard : Nat.card (LL ≃ₐ[KK] LL) =
      q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) *
        q.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) :=
    natCard_algEquiv_adicCompletion_eq_ramificationIdx_mul_inertiaDeg Q q hq
  have hrange : Nat.card ρ.range = q.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) := by
    have h1 : Nat.card ((LL ≃ₐ[KK] LL) ⧸ ρ.ker) * Nat.card ρ.ker =
        Nat.card (LL ≃ₐ[KK] LL) := by
      simpa only [Subgroup.index_eq_card] using Subgroup.index_mul_card ρ.ker
    rw [hkerI, hIcard, hGcard] at h1
    have he : 0 < q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) :=
      Ideal.ramificationIdx_pos (NumberField.RingOfIntegers K) q.asIdeal
    have h2 : Nat.card ((LL ≃ₐ[KK] LL) ⧸ I) =
        q.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) := by
      rw [mul_comm (q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K))
        (q.asIdeal.inertiaDeg (NumberField.RingOfIntegers K))] at h1
      exact Nat.mul_right_cancel he h1
    have h3 : Nat.card ((LL ≃ₐ[KK] LL) ⧸ ρ.ker) = Nat.card ρ.range :=
      Nat.card_congr (QuotientGroup.quotientKerEquivRange ρ).toEquiv
    rw [← h3, hkerI, h2]
  have hfixeq : ρ.range = fixSubgroup ψ := by
    haveI : Finite (RingAut ResL) := by
      haveI : Finite (ResL → ResL) := inferInstance
      exact Finite.of_injective (fun f : RingAut ResL => (f : ResL → ResL))
        (fun f g h => by ext x; exact congrFun h x)
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [hrange, hcardFix])
  exact ⟨ρ, hker, hfixeq⟩

end Commons.NumberTheory.NumberField.Completion
