import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.RamificationInertia.Ramification
import Submission.Commons.NumberTheory.NumberField.Completion.adicCompletionIntegers_iInf_maximalIdeal_pow_eq_bot
import Submission.Commons.NumberTheory.NumberField.Completion.exists_inertiaSubgroup_adicCompletion_isNormal_card_quotient
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped NumberField

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

namespace Commons.NumberTheory.NumberField.Completion

/-! ## General preliminaries on ring automorphisms of local rings and of valued fields -/

/-- A ring automorphism of a local ring maps the maximal ideal to itself. -/
theorem map_maximalIdeal_eq_self_of_ringEquiv {R : Type*} [CommSemiring R] [IsLocalRing R]
    (e : R ≃+* R) :
    Ideal.map (e : R →+* R) (IsLocalRing.maximalIdeal R) = IsLocalRing.maximalIdeal R := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap]
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hx ⊢
    intro h
    exact hx (by simpa using (IsUnit.map (e.symm : R →+* R) h))
  · intro y hy
    have hpre : e.symm y ∈ IsLocalRing.maximalIdeal R := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hy ⊢
      intro h
      exact hy (by simpa using (IsUnit.map (e : R →+* R) h))
    have h1 := Ideal.mem_map_of_mem (f := (e : R →+* R)) hpre
    simpa using h1

/-- A ring automorphism of a field which fixes a valuation subring pointwise is the identity. -/
theorem ringEquiv_eq_one_of_forall_eq_on_valuationSubring {K : Type*} [Field K]
    (O : ValuationSubring K) (σ : K ≃+* K) (hσ : ∀ x : O, σ (x : K) = (x : K)) : σ = 1 := by
  ext x
  by_cases hx : x ∈ O
  · simpa using hσ ⟨x, hx⟩
  · have hinv : x⁻¹ ∈ O := (O.mem_or_inv_mem x).resolve_left hx
    have h1 : σ x⁻¹ = x⁻¹ := hσ ⟨x⁻¹, hinv⟩
    have h2 : σ x = x := by
      calc σ x = σ ((x⁻¹)⁻¹) := by rw [inv_inv]
        _ = (σ x⁻¹)⁻¹ := by rw [map_inv₀]
        _ = (x⁻¹)⁻¹ := by rw [h1]
        _ = x := by rw [inv_inv]
    simpa using h2

/-- An algebra automorphism of a field which fixes a valuation subring pointwise is the
identity. -/
theorem algEquiv_eq_one_of_forall_eq_on_valuationSubring {R K : Type*} [CommSemiring R] [Field K]
    [Algebra R K] (O : ValuationSubring K) (σ : K ≃ₐ[R] K)
    (hσ : ∀ x : O, σ (x : K) = (x : K)) : σ = 1 := by
  have h : (σ : K ≃+* K) = 1 :=
    ringEquiv_eq_one_of_forall_eq_on_valuationSubring O (σ : K ≃+* K) hσ
  ext x
  have h2 := RingEquiv.congr_fun h x
  simpa using h2

/-!
## The higher ramification subgroups of a local Galois group

Let `L / K` be a finite Galois extension of number fields, `Q` a height one prime of `𝓞 K` and
`q` a height one prime of `𝓞 L` lying over `Q`.  The `Q`-adic completion `K_Q` acts on the
`q`-adic completion `L_q` through `Commons.RingTheory.Henselian.adicCompletionMap`, and the
resulting local Galois group `Gal(L_q / K_Q)` carries a decreasing filtration by normal
subgroups, the *higher ramification subgroups in the lower numbering*.  The first of them is the
inertia subgroup, of order the ramification index; this is the local filtration used in
Neukirch–Schmidt–Wingberg, *Cohomology of Number Fields*, Theorem 12.2.1.
-/

/-- **The higher ramification subgroups of the local Galois group of an adic completion.**

With `L / K`, `Q`, `q` as above, there is a filtration `G : ℕ → Subgroup Gal(L_q / K_Q)` of the
local Galois group by normal subgroups, antitone in `n`, with trivial intersection, such that

`G ⁿ = { σ | ∀ x ∈ q.adicCompletionIntegers L, σ x ≡ x  (mod 𝔪^{n+1}) }`

(`𝔪` the maximal ideal of the ring of integers of `L_q`), and whose first member `G ⁰` — the
inertia subgroup — has order the ramification index `e(q|Q)`. -/
theorem exists_ramificationSubgroups_adicCompletion {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq : q.asIdeal.LiesOver Q.asIdeal) :
    letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
      RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
    ∃ (G : ℕ → Subgroup (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L)),
      (∀ n, (G n).Normal) ∧ Antitone G ∧ (⨅ n, G n) = ⊥ ∧
      Nat.card (G 0) = q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) ∧
      (∀ (n : ℕ) (σ : q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L),
        σ ∈ G n ↔ ∀ x : q.adicCompletionIntegers L,
          ∃ h : σ (x : q.adicCompletion L) ∈ q.adicCompletionIntegers L,
            Ideal.Quotient.mk (IsLocalRing.maximalIdeal (q.adicCompletionIntegers L) ^ (n + 1))
                ⟨σ (x : q.adicCompletion L), h⟩ =
              Ideal.Quotient.mk (IsLocalRing.maximalIdeal (q.adicCompletionIntegers L) ^ (n + 1)) x) := by
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
  -- every `K_Q`-algebra automorphism of `L_q` preserves the ring of integers
  have hpres : ∀ (σ : q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L)
      (x : q.adicCompletion L),
      σ x ∈ q.adicCompletionIntegers L ↔ x ∈ q.adicCompletionIntegers L :=
    algEquiv_mem_adicCompletionIntegers_iff_adicCompletion Q q hq
  -- the induced ring automorphism of the ring of integers
  let bar : (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L) →
      (q.adicCompletionIntegers L ≃+* q.adicCompletionIntegers L) := fun σ =>
    { toFun := fun x => ⟨σ x, (hpres σ x).mpr x.2⟩
      invFun := fun y => ⟨σ⁻¹ y, (hpres σ⁻¹ y).mpr y.2⟩
      left_inv := fun x => Subtype.ext (by simp)
      right_inv := fun y => Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by simp)
      map_add' := fun x y => Subtype.ext (by simp) }
  have bar_apply : ∀ (σ : q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L)
      (x : q.adicCompletionIntegers L),
      ((bar σ x : q.adicCompletionIntegers L) : q.adicCompletion L) =
        σ (x : q.adicCompletion L) := fun σ x => rfl
  -- `bar σ` preserves all powers of the maximal ideal
  have hmem_pow : ∀ (σ : q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L)
      (n : ℕ) (y : q.adicCompletionIntegers L),
      y ∈ IsLocalRing.maximalIdeal (q.adicCompletionIntegers L) ^ n →
      bar σ y ∈ IsLocalRing.maximalIdeal (q.adicCompletionIntegers L) ^ n := by
    intro σ n y hy
    have hmap : Ideal.map (bar σ : q.adicCompletionIntegers L →+* q.adicCompletionIntegers L)
        (IsLocalRing.maximalIdeal (q.adicCompletionIntegers L) ^ n) =
        IsLocalRing.maximalIdeal (q.adicCompletionIntegers L) ^ n := by
      rw [Ideal.map_pow, map_maximalIdeal_eq_self_of_ringEquiv]
    have h1 := Ideal.mem_map_of_mem
      (f := (bar σ : q.adicCompletionIntegers L →+* q.adicCompletionIntegers L)) hy
    rwa [hmap] at h1
  have bar_mul_apply : ∀ (σ τ : q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L)
      (x : q.adicCompletionIntegers L), bar (σ * τ) x = bar σ (bar τ x) := by
    intro σ τ x
    apply Subtype.ext
    simp [bar_apply, AlgEquiv.mul_apply]
  have bar_one_apply : ∀ x : q.adicCompletionIntegers L, bar 1 x = x := by
    intro x
    apply Subtype.ext
    simp [bar_apply]
  have bar_inv_apply : ∀ (σ : q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L)
      (x : q.adicCompletionIntegers L), bar σ (bar σ⁻¹ x) = x := by
    intro σ x
    have h1 := bar_mul_apply σ σ⁻¹ x
    rw [mul_inv_cancel, bar_one_apply] at h1
    exact h1.symm
  -- the candidate higher ramification subgroups
  let Gfun : ℕ → Subgroup (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L) := fun n =>
    { carrier := {σ | ∀ x : q.adicCompletionIntegers L,
        bar σ x - x ∈ IsLocalRing.maximalIdeal (q.adicCompletionIntegers L) ^ (n + 1)}
      mul_mem' := by
        intro σ τ hσ hτ x
        have h1 : bar τ x - x ∈
            IsLocalRing.maximalIdeal (q.adicCompletionIntegers L) ^ (n + 1) := hτ x
        have h2 : bar σ (bar τ x - x) ∈
            IsLocalRing.maximalIdeal (q.adicCompletionIntegers L) ^ (n + 1) :=
          hmem_pow σ (n + 1) _ h1
        have h3 : bar σ x - x ∈
            IsLocalRing.maximalIdeal (q.adicCompletionIntegers L) ^ (n + 1) := hσ x
        have heq : bar (σ * τ) x - x =
            bar σ (bar τ x - x) + (bar σ x - x) := by
          rw [bar_mul_apply σ τ x, map_sub]
          abel
        rw [heq]
        exact add_mem h2 h3
      one_mem' := by
        intro x
        rw [bar_one_apply x, sub_self]
        exact zero_mem _
      inv_mem' := by
        intro σ hσ x
        have h := hσ (bar σ⁻¹ x)
        rw [bar_inv_apply σ x] at h
        have h' := neg_mem h
        rwa [neg_sub] at h' }
  refine ⟨Gfun, ?_, ?_, ?_, ?_, ?_⟩
  · -- normality
    intro n
    refine ⟨fun σ hσ τ x => ?_⟩
    have h := hσ (bar τ⁻¹ x)
    have h2 : bar τ (bar σ (bar τ⁻¹ x) - bar τ⁻¹ x) ∈
        IsLocalRing.maximalIdeal (q.adicCompletionIntegers L) ^ (n + 1) :=
      hmem_pow τ (n + 1) _ h
    have heq : bar (τ * σ * τ⁻¹) x - x =
        bar τ (bar σ (bar τ⁻¹ x) - bar τ⁻¹ x) := by
      rw [bar_mul_apply (τ * σ) τ⁻¹ x, bar_mul_apply τ σ (bar τ⁻¹ x), map_sub,
        bar_inv_apply τ x]
    rw [heq]
    exact h2
  · -- antitonicity
    intro a b hab σ hσ x
    exact Ideal.pow_le_pow_right (Nat.succ_le_succ hab) (hσ x)
  · -- the intersection of all the ramification subgroups is trivial
    rw [Subgroup.eq_bot_iff_forall]
    intro σ hσ
    rw [Subgroup.mem_iInf] at hσ
    have hfix : ∀ y : q.adicCompletionIntegers L,
        σ (y : q.adicCompletion L) = (y : q.adicCompletion L) := by
      intro y
      have hzero : bar σ y - y = 0 := by
        have hmem : bar σ y - y ∈
            (⨅ n : ℕ, IsLocalRing.maximalIdeal (q.adicCompletionIntegers L) ^ n) := by
          rw [Submodule.mem_iInf]
          intro n
          cases n with
          | zero => simp
          | succ n => exact hσ n y
        rw [adicCompletionIntegers_iInf_maximalIdeal_pow_eq_bot L q] at hmem
        simpa using hmem
      calc σ (y : q.adicCompletion L) = (bar σ y : q.adicCompletion L) :=
            (bar_apply σ y).symm
        _ = (y : q.adicCompletion L) := by rw [sub_eq_zero.mp hzero]
    exact algEquiv_eq_one_of_forall_eq_on_valuationSubring (q.adicCompletionIntegers L) σ hfix
  · -- the order of the first ramification subgroup is the ramification index
    obtain ⟨I, hI, hcardI⟩ :=
      exists_inertiaSubgroup_adicCompletion_card_eq_ramificationIdx Q q hq
    have hG0 : Gfun 0 = I := by
      ext σ
      rw [hI]
      constructor
      · intro h x
        have hx : bar σ x - x ∈ IsLocalRing.maximalIdeal (q.adicCompletionIntegers L) := by
          simpa using h x
        rw [Commons.NumberTheory.NumberField.adicCompletionIntegers_mem_maximalIdeal_iff_valued_lt_one
          q (bar σ x - x)] at hx
        rwa [show ((bar σ x - x : q.adicCompletionIntegers L) : q.adicCompletion L) =
            σ (x : q.adicCompletion L) - (x : q.adicCompletion L) from by simp [bar_apply]] at hx
      · intro h x
        have hx := h x
        rw [← show ((bar σ x - x : q.adicCompletionIntegers L) : q.adicCompletion L) =
            σ (x : q.adicCompletion L) - (x : q.adicCompletion L) from by simp [bar_apply]] at hx
        have hx2 := (Commons.NumberTheory.NumberField.adicCompletionIntegers_mem_maximalIdeal_iff_valued_lt_one
          q (bar σ x - x)).mpr hx
        simpa using hx2
    rw [hG0, hcardI]
  · -- the defining congruence condition
    intro n σ
    change (∀ x : q.adicCompletionIntegers L,
        bar σ x - x ∈ IsLocalRing.maximalIdeal (q.adicCompletionIntegers L) ^ (n + 1)) ↔
      ∀ x : q.adicCompletionIntegers L,
        ∃ h : σ (x : q.adicCompletion L) ∈ q.adicCompletionIntegers L,
          Ideal.Quotient.mk (IsLocalRing.maximalIdeal (q.adicCompletionIntegers L) ^ (n + 1))
              (⟨σ (x : q.adicCompletion L), h⟩ : q.adicCompletionIntegers L) =
            Ideal.Quotient.mk (IsLocalRing.maximalIdeal (q.adicCompletionIntegers L) ^ (n + 1)) x
    refine forall_congr' fun x => ?_
    have h1 : (∃ h : σ (x : q.adicCompletion L) ∈ q.adicCompletionIntegers L,
        Ideal.Quotient.mk (IsLocalRing.maximalIdeal (q.adicCompletionIntegers L) ^ (n + 1))
            (⟨σ (x : q.adicCompletion L), h⟩ : q.adicCompletionIntegers L) =
          Ideal.Quotient.mk (IsLocalRing.maximalIdeal (q.adicCompletionIntegers L) ^ (n + 1)) x)
        ↔ (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (q.adicCompletionIntegers L) ^ (n + 1))
            (bar σ x) =
          Ideal.Quotient.mk (IsLocalRing.maximalIdeal (q.adicCompletionIntegers L) ^ (n + 1)) x) := by
      constructor
      · rintro ⟨h, hh⟩
        have h2 : (⟨σ (x : q.adicCompletion L), h⟩ : q.adicCompletionIntegers L) = bar σ x :=
          Subtype.ext rfl
        rwa [h2] at hh
      · intro hh
        refine ⟨(hpres σ (x : q.adicCompletion L)).mpr x.2, ?_⟩
        have h2 : (⟨σ (x : q.adicCompletion L),
            (hpres σ (x : q.adicCompletion L)).mpr x.2⟩ : q.adicCompletionIntegers L) =
            bar σ x := Subtype.ext rfl
        rwa [h2]
    rw [h1]
    exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem
      (I := IsLocalRing.maximalIdeal (q.adicCompletionIntegers L) ^ (n + 1)) (bar σ x) x).symm

end Commons.NumberTheory.NumberField.Completion
