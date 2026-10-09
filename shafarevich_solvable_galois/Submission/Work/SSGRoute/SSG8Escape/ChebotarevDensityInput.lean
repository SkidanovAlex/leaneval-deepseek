import Mathlib
import Submission.Work.SSGRoute.ssg8Chebotarev
import Submission.NK.Chebotarev.ConjugacyOfFrobenius
import Submission.NK.Chebotarev.FrobeniusGenerateTop
import Submission.NK.Chebotarev.AbelianChebotarevOfLFunctions
import Submission.NK.Chebotarev.HasDirichletDensitySensitivity
import Submission.NK.NUV2.ChebAux.kernelLe_of_auxField
import Submission.NK.Reconstruct.denseChebotarev
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The Čebotarev density input of the escape theorem, over an arbitrary base

`Work.SSGRoute.chebotarev_density_general` (`Submission/Work/SSGRoute/ssg8Chebotarev.lean`, proved,
axiom-clean) is Čebotarev's density theorem over an arbitrary number-field base in the **element**
form: for a finite Galois `N/K` and `σ : Gal(N/K)`, the set
`frobSet σ = {p | IsFrobAtPrime p σ}` has Dirichlet density `1/|C_G(σ)|`.

The escape step `SSG8Escape.escape_prime_ssg8` consumes Čebotarev in the **conjugacy-class** form,
packaged as `NK.Reconstruct.ChebotarevDensityInput k Ω`: for every finite Galois level `L/k` and
every `τ : Gal(↥L/k)`, the set `{p | IsConj (frobAtPrime p) τ}` has density
`|{x // IsConj x τ}| / |Gal(↥L/k)|`.  This file bridges the two:

* `frobDensity_eq_card_conjClass` — orbit–stabiliser: `1/|C_G(σ)| = |cl(σ)|/|G|`;
* `isFrobAtPrime_of_isConj_frobAtPrime` — conjugates of the chosen Frobenius are Frobenius
  elements at the same prime (no unramifiedness needed);
* `isConj_frobAtPrime_of_isFrobAtPrime` — for an **unramified** prime, any Frobenius element is
  conjugate to the chosen one (`NK.Chebotarev.ConjugacyOfFrobenius` + uniqueness at an unramified
  prime);
* `chebotarevDensityInput_general` — the assembly, by
  `NK.Chebotarev.HasDirichletDensitySensitivity` (two sets differing only at the finitely many
  ramified primes have the same density).
-/

namespace Work.SSG8Escape

open NumberField IsDedekindDomain

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

/-- **Orbit–stabiliser for the Frobenius density.**  The predicted Čebotarev density
`1/|C_G(σ)|` equals `|cl(σ)|/|G|`. -/
theorem frobDensity_eq_card_conjClass (σ : Gal(L/K)) :
    NK.ChebotarevGeneral.frobDensity (K := K) (N := L) σ =
      (Nat.card {x : Gal(L/K) // IsConj x σ} : ℝ) / (Nat.card (Gal(L/K)) : ℝ) := by
  classical
  haveI : Fintype (Gal(L/K)) := Fintype.ofFinite _
  -- the conjugacy class is the orbit of the conjugation action
  have hcarrier : (ConjClasses.mk σ).carrier = {x : Gal(L/K) | IsConj x σ} := by
    ext x
    rw [ConjClasses.mem_carrier_iff_mk_eq, ConjClasses.mk_eq_mk_iff_isConj]
    exact Iff.rfl
  have horbit : (MulAction.orbit (ConjAct (Gal(L/K))) σ : Set (Gal(L/K))) =
      (ConjClasses.mk σ).carrier := ConjAct.orbit_eq_carrier_conjClasses (G := Gal(L/K)) σ
  -- orbit–stabiliser, and the identification of the stabiliser with the centraliser
  have hOS := MulAction.card_orbit_mul_card_stabilizer_eq_card_group
    (ConjAct (Gal(L/K))) σ
  have hstab : Fintype.card (Subgroup.centralizer ({σ} : Set (Gal(L/K)))) =
      Fintype.card (MulAction.stabilizer (ConjAct (Gal(L/K))) σ) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
    exact Subgroup.nat_card_centralizer_nat_card_stabilizer σ
  have hcl : Fintype.card {x : Gal(L/K) // IsConj x σ} =
      Fintype.card (MulAction.orbit (ConjAct (Gal(L/K))) σ) :=
    (Fintype.card_congr (Set.equivOfEq hcarrier)).symm.trans
      (Fintype.card_congr (Set.equivOfEq horbit.symm))
  -- the product identity
  have hcard : Nat.card {x : Gal(L/K) // IsConj x σ} *
      Nat.card (Subgroup.centralizer ({σ} : Set (Gal(L/K)))) = Nat.card (Gal(L/K)) := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
      hcl, hstab, hOS]
    exact (Fintype.card_congr (ConjAct.toConjAct (G := Gal(L/K)))).symm
  have hpos : 0 < Nat.card {x : Gal(L/K) // IsConj x σ} := by
    haveI : Nonempty {x : Gal(L/K) // IsConj x σ} := ⟨⟨σ, IsConj.refl σ⟩⟩
    exact Nat.card_pos
  have hCpos : 0 < Nat.card (Subgroup.centralizer ({σ} : Set (Gal(L/K)))) := by
    haveI : Nonempty (Subgroup.centralizer ({σ} : Set (Gal(L/K)))) := ⟨1, Subgroup.one_mem _⟩
    exact Nat.card_pos
  have hAne : (Nat.card {x : Gal(L/K) // IsConj x σ} : ℝ) ≠ 0 := by
    exact_mod_cast hpos.ne'
  have hCne : (Nat.card (Subgroup.centralizer ({σ} : Set (Gal(L/K)))) : ℝ) ≠ 0 := by
    exact_mod_cast hCpos.ne'
  rw [NK.ChebotarevGeneral.frobDensity, ← hcard, Nat.cast_mul]
  field_simp

/-- **Conjugates of the chosen Frobenius are Frobenius elements at the same prime.** -/
theorem isFrobAtPrime_of_isConj_frobAtPrime (p : NK.Chebotarev.PrimeIdeal K) (σ : Gal(L/K))
    (h : IsConj (NK.Chebotarev.frobAtPrime (K := K) (L := L) p) σ) :
    NK.Chebotarev.IsFrobAtPrime (K := K) (L := L) p σ := by
  obtain ⟨c, hc⟩ := isConj_iff.mp h
  rw [← hc]
  exact NK.ChebotarevGeneral.isFrobAtPrime_conj
    (σ := NK.Chebotarev.frobAtPrime (K := K) (L := L) p) (τ := c)
    (NK.NUV2.ChebAux.isFrobAtPrime_frobAtPrime' (K := K) (L := L) p)

/-- **At an unramified prime, every Frobenius element is conjugate to the chosen one.** -/
theorem isConj_frobAtPrime_of_isFrobAtPrime (p : NK.Chebotarev.PrimeIdeal K)
    (hunr : ∀ P : NK.Chebotarev.PrimeIdeal L, P.asIdeal.LiesOver p.asIdeal →
      P.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1)
    (σ : Gal(L/K)) (hσ : NK.Chebotarev.IsFrobAtPrime (K := K) (L := L) p σ) :
    IsConj (NK.Chebotarev.frobAtPrime (K := K) (L := L) p) σ := by
  obtain ⟨P, hP, hPσ⟩ := hσ
  obtain ⟨Q, hQ, hQF⟩ :=
    NK.NUV2.ChebAux.isFrobAtPrime_frobAtPrime' (K := K) (L := L) p
  obtain ⟨g, hg⟩ := NK.Chebotarev.ConjugacyOfFrobenius p Q P hQ hP hunr
    (NK.Chebotarev.frobAtPrime (K := K) (L := L) p) σ hQF hPσ
  exact isConj_iff.mpr ⟨g, hg.symm⟩

/-- **The Čebotarev density input `NK.Reconstruct.ChebotarevDensityInput`, over an arbitrary
number-field base.**  This is the Čebotarev input consumed by `SSG8Escape.escape_prime_ssg8`,
discharged from the proved general Čebotarev density theorem
`Work.SSGRoute.chebotarev_density_general` (element form) plus the two bridges above and
`NK.Chebotarev.HasDirichletDensitySensitivity` (density is insensitive to finite modifications). -/
theorem chebotarevDensityInput_general (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] : NK.Reconstruct.ChebotarevDensityInput k Ω := by
  intro L _ hnorm _ τ
  haveI : IsGalois k ↥L := Commons.FieldTheory.Galois.isGalois_of_normal_of_charZero
  have hbase := Work.SSGRoute.chebotarev_density_general k ↥L τ
  rw [Work.SSG8Escape.frobDensity_eq_card_conjClass (K := k) (L := ↥L) τ] at hbase
  refine NK.Chebotarev.HasDirichletDensitySensitivity ?_ hbase
  refine (NK.Chebotarev.finite_ramifiedPrimes (K := k) (L := ↥L)).subset ?_
  rintro p (hp | hp)
  · exact fun hunr => hp.2 (isConj_frobAtPrime_of_isFrobAtPrime p hunr τ
      (NK.ChebotarevGeneral.mem_frobSet.mp hp.1))
  · exact absurd (isFrobAtPrime_of_isConj_frobAtPrime p τ hp.1)
      (fun h => hp.2 (NK.ChebotarevGeneral.mem_frobSet.mpr h))

end Work.SSG8Escape
