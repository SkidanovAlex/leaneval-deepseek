import Mathlib.Data.Int.Star
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.Algebra.Order.Ring.Star
import Submission.Commons.NumberTheory.NumberField.exists_prime_splitsCompletely
import Submission.NK.Chebotarev.FrobeniusOne
import Submission.NK.FieldTheory.Galois.iSup_decompositionSubgroup_eq_top
import Submission.NK.Mine.CompletionAPI
import Submission.NK.Mine.FrobeniusGenerateTopUnramified
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Detection of an isomorphism of absolute Galois groups by its Frobenius action

Let `K` be a number field and `K'` a separable closure of `K`.  The main result of this file is
`NK.Mine.eq_of_preserves_frobenius`: **a homeomorphic isomorphism of absolute Galois groups which
preserves the Frobenius elements at the unramified primes of every finite Galois subextension is the
identity.**

The argument is the classical one, with the two arithmetic ingredients that are available
unconditionally in this workspace:

* for every finite Galois `L ⊆ K'`, *some* prime of `K` splits completely in `L`
  (`Commons.NumberTheory.NumberField.exists_prime_splitsCompletely`, Dedekind's density theorem
  for the completely split primes), so that the trivial element is a Frobenius at some unramified
  prime of `L`.  Consequently an automorphism preserving Frobenius elements preserves the subgroup
  `Gal(K'/L)` of elements fixing `L`;
* the Frobenius elements at the primes of `K` **unramified** in `L` generate `Gal(L/K)`
  (`NK.Mine.FrobeniusGenerateTopUnramified`).

Together they show that `σ` induces the identity on every finite quotient `Gal(L/K)`, hence is the
identity.  Applied to `σ = ϕ.trans ψ.symm` this yields
`NK.Mine.eq_of_preserves_decompositionGroup_and_frobenius`.
-/

namespace NK.Mine

open NK.Chebotarev

set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

/-- **Arithmetic helper.**  If every term of a finite sum of natural numbers is at least one and
the sum is the number of terms, then every term is one. -/
lemma eq_one_of_sum_eq_card {ι : Type*} [Fintype ι] (f : ι → ℕ) (h1 : ∀ i, 1 ≤ f i)
    (h2 : ∑ i, f i = Fintype.card ι) (i : ι) : f i = 1 := by
  have h3 : ∑ i : ι, ((f i : ℤ) - 1) = 0 := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    have h4 : ((∑ i : ι, f i : ℕ) : ℤ) = (Fintype.card ι : ℤ) := by rw [h2]
    rw [Nat.cast_sum] at h4
    linarith
  have h5 := (Finset.sum_eq_zero_iff_of_nonneg (s := Finset.univ)
    (f := fun i => (f i : ℤ) - 1) (fun i _ => by have := h1 i; omega)).mp h3 i
    (Finset.mem_univ i)
  omega

/-- **A prime of `L` unramified over `K` at which the Frobenius is trivial.**

Take a prime `p` of `K` splitting completely in `L`
(`Commons.NumberTheory.NumberField.exists_prime_splitsCompletely`), i.e. with
`#(primes over p) = [L : K]`.  The fundamental identity
`∑_{q | p} e(q) f(q) = [L : K]` then forces `e(q) = f(q) = 1` for every prime `q` above `p`: the sum
has `[L : K]` terms, each at least `1`.  For such a `q` the inertia degree of `q` is `1`, so the
trivial element is a Frobenius at `q`
(`NK.Chebotarev.IsFrobAt_eq_one_iff_inertiaDeg_eq_one`). -/
lemma exists_isFrobAt_one_and_unramified {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L] :
    ∃ (p : NK.Chebotarev.PrimeIdeal K) (P : NK.Chebotarev.PrimeIdeal L),
      P.asIdeal.LiesOver p.asIdeal ∧
        P.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1 ∧
        NK.Chebotarev.IsFrobAt (K := K) (L := L) P 1 := by
  classical
  obtain ⟨p, hp⟩ :=
    Commons.NumberTheory.NumberField.exists_prime_splitsCompletely (K := K) (L := L)
  haveI hp_prime : p.asIdeal.IsPrime := p.isPrime
  have hp0 : p.asIdeal ≠ ⊥ := p.ne_bot
  haveI hfin : (p.asIdeal.primesOver (NumberField.RingOfIntegers L)).Finite :=
    Commons.NumberTheory.NumberField.finite_primesOver (K := K) (L := L) p.asIdeal hp_prime hp0
  letI : Fintype (p.asIdeal.primesOver (NumberField.RingOfIntegers L)) := hfin.fintype
  have hsum : ∑ q : p.asIdeal.primesOver (NumberField.RingOfIntegers L),
      q.1.ramificationIdx (NumberField.RingOfIntegers K) *
        q.1.inertiaDeg (NumberField.RingOfIntegers K) =
      Module.finrank (NumberField.RingOfIntegers K) (NumberField.RingOfIntegers L) :=
    Ideal.sum_ramification_inertia_eq_finrank (R := NumberField.RingOfIntegers K)
      p.asIdeal (NumberField.RingOfIntegers L)
  have hcard : Fintype.card (p.asIdeal.primesOver (NumberField.RingOfIntegers L)) =
      Module.finrank K L := by
    rw [Set.fintypeCard_eq_ncard]; exact hp
  have hfr : Module.finrank (NumberField.RingOfIntegers K) (NumberField.RingOfIntegers L) =
      Module.finrank K L :=
    (IsFractionRing.finrank_eq (NumberField.RingOfIntegers K) K
      (NumberField.RingOfIntegers L) L).symm
  have hle : ∀ q : p.asIdeal.primesOver (NumberField.RingOfIntegers L),
      1 ≤ q.1.ramificationIdx (NumberField.RingOfIntegers K) *
        q.1.inertiaDeg (NumberField.RingOfIntegers K) := by
    intro q
    have h1 : 1 ≤ q.1.ramificationIdx (NumberField.RingOfIntegers K) :=
      q.1.ramificationIdx_pos (NumberField.RingOfIntegers K)
    have h2 : 1 ≤ q.1.inertiaDeg (NumberField.RingOfIntegers K) :=
      q.1.inertiaDeg_pos (NumberField.RingOfIntegers K)
    calc (1 : ℕ) = 1 * 1 := (mul_one 1).symm
      _ ≤ _ := Nat.mul_le_mul h1 h2
  obtain ⟨P⟩ := (inferInstance : Nonempty (p.asIdeal.primesOver (NumberField.RingOfIntegers L)))
  have hef : P.1.ramificationIdx (NumberField.RingOfIntegers K) *
      P.1.inertiaDeg (NumberField.RingOfIntegers K) = 1 :=
    eq_one_of_sum_eq_card (fun q : p.asIdeal.primesOver (NumberField.RingOfIntegers L) =>
      q.1.ramificationIdx (NumberField.RingOfIntegers K) *
        q.1.inertiaDeg (NumberField.RingOfIntegers K)) hle
      (by rw [hsum, hfr, ← hcard]) P
  obtain ⟨h1, h2⟩ := mul_eq_one.mp hef
  refine ⟨p, ⟨P.1, P.2.1, Ideal.ne_bot_of_mem_primesOver hp0 P.2⟩, P.2.2, h1, ?_⟩
  exact (NK.Chebotarev.IsFrobAt_eq_one_iff_inertiaDeg_eq_one P.2.2 h1).mpr h2

/-- **Frobenius detection.**  Let `K` be a number field, `K'` a separable closure of `K` and
`σ : Gal(K'/K) ≃* Gal(K'/K)` a group automorphism with the property that, for every finite Galois
`L ⊆ K'`, every prime `P` of `L` unramified over `K` and every `g : Gal(K'/K)` whose restriction to
`L` is a Frobenius at `P`, the restriction of `σ g` to `L` is *also* a Frobenius at `P`.  Then
`σ = 1`.

Since the Frobenius element at a fixed unramified prime is unique, this says that `σ` acts
trivially on the Frobenius elements of every finite Galois quotient `Gal(L/K)`; as these generate
(and fixing them fixes the whole subgroup `Gal(K'/L)`, by the completely split prime above), `σ`
acts trivially on every finite quotient of `Gal(K'/K)`. -/
lemma eq_of_preserves_frobenius {K K' : Type*} [Field K] [NumberField K] [Field K']
    [Algebra K K'] [IsSepClosure K K'] (σ : Gal(K'/K) ≃* Gal(K'/K))
    (hF : ∀ (L : IntermediateField K K') [FiniteDimensional K L] [IsGalois K L]
        (P : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥L))
        (g : Gal(K'/K)),
        P.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1 →
        NK.Chebotarev.IsFrobAt (K := K) (L := ↥L) P
          (AlgEquiv.restrictNormalHom (F := K) (K₁ := K') L g) →
        NK.Chebotarev.IsFrobAt (K := K) (L := ↥L) P
          (AlgEquiv.restrictNormalHom (F := K) (K₁ := K') L (σ g))) :
    σ = 1 := by
  -- `σ` acts trivially on every finite Galois quotient `Gal(L/K)`
  have key : ∀ (L : IntermediateField K K') [FiniteDimensional K L] [IsGalois K L],
      ∀ g : Gal(K'/K),
      AlgEquiv.restrictNormalHom (F := K) (K₁ := K') L (σ g) =
        AlgEquiv.restrictNormalHom (F := K) (K₁ := K') L g := by
    intro L _ _
    haveI : NumberField ↥L := Commons.NumberTheory.NumberField.numberField_of_intermediateField L
    let ρ : Gal(K'/K) →* Gal(↥L/K) := AlgEquiv.restrictNormalHom (F := K) (K₁ := K') L
    -- Step 1: `σ` preserves the kernel of the restriction (for a prime splitting completely in `L`)
    have hstep1 : ∀ g : Gal(K'/K), ρ g = 1 → ρ (σ g) = 1 := by
      intro g hg
      obtain ⟨p, P, hPover, he, hfrob1⟩ := exists_isFrobAt_one_and_unramified (K := K) (L := ↥L)
      have happ : NK.Chebotarev.IsFrobAt (K := K) (L := ↥L) P (ρ (σ g)) := by
        refine hF L P g he ?_
        show NK.Chebotarev.IsFrobAt (K := K) (L := ↥L) P (ρ g)
        rw [hg]
        exact hfrob1
      exact NK.Chebotarev.IsFrobAt.eq_of_isFrobAt (K := K) (L := ↥L) hPover he happ hfrob1
    -- Step 2: every element of `Gal(L/K)` which is a Frobenius at an unramified prime is fixed
    -- (in the twisted sense of the subgroup `hgen`) by `σ`
    set S : Set Gal(↥L/K) := {τ : Gal(↥L/K) | ∃ p : NK.Chebotarev.PrimeIdeal K,
        (∀ P : NK.Chebotarev.PrimeIdeal ↥L, P.asIdeal.LiesOver p.asIdeal →
          P.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1) ∧
        NK.Chebotarev.IsFrobAtPrime (K := K) (L := ↥L) p τ} with hS
    have hgen : ∀ τ ∈ Subgroup.closure S, ∀ g : Gal(K'/K), ρ g = τ → ρ (σ g) = τ := by
      intro τ hτ
      refine Subgroup.closure_induction (k := S) ?_ ?_ ?_ ?_ hτ
      · intro x hx g hg
        rw [hS] at hx
        obtain ⟨p, hunr, hf⟩ := hx
        rw [NK.Chebotarev.isFrobAtPrime_iff] at hf
        obtain ⟨P, hPover, hfrob⟩ := hf
        have happ : NK.Chebotarev.IsFrobAt (K := K) (L := ↥L) P (ρ (σ g)) := by
          refine hF L P g (hunr P hPover) ?_
          show NK.Chebotarev.IsFrobAt (K := K) (L := ↥L) P (ρ g)
          rw [hg]
          exact hfrob
        exact NK.Chebotarev.IsFrobAt.eq_of_isFrobAt (K := K) (L := ↥L) hPover
          (hunr P hPover) happ hfrob
      · intro g hg
        exact hstep1 g hg
      · intro x y hx hy ihx ihy g hg
        obtain ⟨g₁, hg₁⟩ :=
          AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := ↥L) (E := K') x
        obtain ⟨g₂, hg₂⟩ :=
          AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := ↥L) (E := K') y
        have hgg : ρ (g * (g₁ * g₂)⁻¹) = 1 := by
          rw [map_mul, map_inv, map_mul, hg, hg₁, hg₂, mul_inv_cancel]
        have hker := hstep1 (g * (g₁ * g₂)⁻¹) hgg
        simp only [map_mul, map_inv] at hker
        rw [ihx g₁ hg₁, ihy g₂ hg₂] at hker
        exact mul_inv_eq_one.mp hker
      · intro x hx ih g hg
        obtain ⟨h, hh⟩ :=
          AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := ↥L) (E := K') x
        have hgh : ρ (g * h) = 1 := by rw [map_mul, hg, hh, inv_mul_cancel]
        have hker := hstep1 (g * h) hgh
        simp only [map_mul] at hker
        rw [ih h hh] at hker
        exact eq_inv_of_mul_eq_one_left hker
    intro g
    have hclosure : Subgroup.closure S = ⊤ :=
      NK.Mine.FrobeniusGenerateTopUnramified (K := K) (L := ↥L)
    exact hgen (ρ g) (by rw [hclosure]; trivial) g rfl
  -- `σ` is therefore the identity: every element of `K'` lies in a finite Galois subextension
  refine MulEquiv.ext fun g => ?_
  refine AlgEquiv.ext fun x => ?_
  obtain ⟨L, hLfin, hLgal, hxL⟩ :=
    Commons.FieldTheory.Galois.exists_finite_galois_containing (k := K) (K := K') x
  haveI : FiniteDimensional K L := hLfin
  haveI : IsGalois K L := hLgal
  have h := congrArg (fun (e : Gal(↥L/K)) => ((e ⟨x, hxL⟩ : ↥L) : K')) (key L g)
  simp only [AlgEquiv.restrictNormalHom_apply] at h
  simpa using h

/-- **Two homeomorphic isomorphisms of absolute Galois groups of number fields which induce the
same decomposition groups and the same Frobenius elements are equal.**

The hypothesis `hF` already suffices: applied to `ϕ.trans ψ.symm` it says that this automorphism of
`Gal(K₁'/K₁)` preserves the Frobenius elements at the unramified primes of every finite Galois
extension of `K₁`, and `NK.Mine.eq_of_preserves_frobenius` then shows that it is the identity. -/
theorem eq_of_preserves_decompositionGroup_and_frobenius {K₁ K₂ K₁' K₂' : Type*}
    [Field K₁] [Field K₂] [Field K₁'] [Field K₂'] [NumberField K₁] [NumberField K₂]
    [Algebra K₁ K₁'] [Algebra K₂ K₂'] [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']
    (ϕ ψ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (hϕ : IsHomeomorph ϕ) (hψ : IsHomeomorph ψ)
    (hD : ∀ A : ValuationSubring K₁', A.comap (algebraMap K₁ K₁') ≠ ⊤ →
      (NK.Mine.decompositionGroupOf K₁ K₁' A).map (ϕ : Gal(K₁'/K₁) →* Gal(K₂'/K₂)) =
        (NK.Mine.decompositionGroupOf K₁ K₁' A).map (ψ : Gal(K₁'/K₁) →* Gal(K₂'/K₂)))
    (hF : ∀ (L : IntermediateField K₁ K₁') [FiniteDimensional K₁ L] [IsGalois K₁ L]
        (P : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥L))
        (g : Gal(K₁'/K₁)),
        P.asIdeal.ramificationIdx (NumberField.RingOfIntegers K₁) = 1 →
        NK.Chebotarev.IsFrobAt (K := K₁) (L := ↥L) P
          (AlgEquiv.restrictNormalHom (F := K₁) (K₁ := K₁') L g) →
        NK.Chebotarev.IsFrobAt (K := K₁) (L := ↥L) P
          (AlgEquiv.restrictNormalHom (F := K₁) (K₁ := K₁') L
            ((ϕ.trans ψ.symm : Gal(K₁'/K₁) ≃* Gal(K₁'/K₁)) g))) :
    ϕ = ψ := by
  have hσ1 : (ϕ.trans ψ.symm : Gal(K₁'/K₁) ≃* Gal(K₁'/K₁)) = 1 :=
    eq_of_preserves_frobenius (K := K₁) (K' := K₁') (ϕ.trans ψ.symm) hF
  refine MulEquiv.ext fun g => ?_
  have h1 : (ϕ.trans ψ.symm) g = g :=
    congrArg (fun e : Gal(K₁'/K₁) ≃* Gal(K₁'/K₁) => e g) hσ1
  have h2 : ψ.symm (ϕ g) = g := by simpa using h1
  calc ϕ g = ψ (ψ.symm (ϕ g)) := (ψ.apply_symm_apply (ϕ g)).symm
    _ = ψ g := by rw [h2]

end NK.Mine
