import Mathlib.RingTheory.Henselian
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.ValuationSubring
import Submission.Work.SSGRoute.RamifiedPlacesAux
import Submission.Work.SSGRoute.TatePoitouRoute.FinitenessHM.exists_prime_val_lt_one_of_ne_top
import Submission.Work.SSGRoute.place_basics
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The rational primes below the places of `Ω` over a number field `k`

Supporting material for `Work.SSGRoute.TatePoitouRoute.FinitenessHM.exists_absDiscr_le_proved`
(the Hermite–Minkowski assembly step over a general number field `k`).  Nothing here is specific to
that statement: the file provides

* `kview k Ω`, the `ℚ`-view of `k` inside `Ω` (an `IntermediateField ℚ Ω` with carrier `k`), with
  `mem_kview_iff`, `kviewEquiv` (the `ℚ`-algebra isomorphism `k ≃ₐ[ℚ] kview`),
  `mem_kview_fixingSubgroup_iff` (`Gal(Ω/k) = kview.fixingSubgroup`) and `kview_base_ne_top` (a
  place finite over `ℚ` is finite over `k`);
* `pof k Ω A hA`, *the* rational prime below a finite place `A` of `Ω` over `k`, characterised by
  `pof_valuation_lt_one : A.valuation (pof k Ω A hA : Ω) < 1` and the uniqueness statement
  `eq_of_prime_valuation_lt_one` (two primes of value `< 1` at a place coincide, by Bézout);
* the transport of the condition `valuation (·) < 1` along the pointwise action on places
  (`smul_valuation_lt_one_iff`, `valuation_lt_one_of_isConjPlace`), and the descent of
  `IsRamifiedIn` from `ℚ` to `k` for a `k`-linear inertia element
  (`isRamifiedIn_base_of_isRamifiedIn_rat_fixing`).

The existence input `exists_prime_val_lt_one_of_ne_top` (a proper valuation subring of a number
field has a rational prime of value `< 1`) is proved in
`Submission/Work/SSGRoute/TatePoitouRoute/FinitenessHM/exists_prime_val_lt_one_of_ne_top.lean`.
-/

open scoped NumberField Pointwise
open SSGRoute

namespace Work.SSGRoute.TatePoitouRoute.FinitenessHM

set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false
set_option linter.style.haveILetI false

section Base

variable (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
  [CharZero Ω]

/-- The `ℚ`-view of the base field `k` inside `Ω`: the intermediate field with carrier `k`. -/
noncomputable def kview : IntermediateField ℚ Ω :=
  (⊤ : IntermediateField ℚ k).map (IsScalarTower.toAlgHom ℚ k Ω)

lemma mem_kview_iff (x : Ω) : x ∈ kview k Ω ↔ ∃ y : k, algebraMap k Ω y = x := by
  rw [kview, IntermediateField.mem_map]
  exact ⟨fun ⟨y, _, hy⟩ => ⟨y, hy⟩, fun ⟨y, hy⟩ => ⟨y, trivial, hy⟩⟩

/-- The fixing subgroup of the `ℚ`-view of `k` is the set of `ℚ`-automorphisms of `Ω` that are
`k`-linear. -/
lemma mem_kview_fixingSubgroup_iff (σ : Ω ≃ₐ[ℚ] Ω) :
    σ ∈ (kview k Ω).fixingSubgroup ↔ ∀ x : k, σ (algebraMap k Ω x) = algebraMap k Ω x := by
  rw [IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · intro h x
    exact h (algebraMap k Ω x) ((mem_kview_iff k Ω _).mpr ⟨x, rfl⟩)
  · intro h x hx
    obtain ⟨y, hy⟩ := (mem_kview_iff k Ω x).mp hx
    rw [← hy, h y]

/-- A place of `Ω` that is finite over `ℚ` is finite over the number field `k`. -/
lemma kview_base_ne_top (V : ValuationSubring Ω) (h : V.comap (algebraMap ℚ Ω) ≠ ⊤) :
    V.comap (algebraMap k Ω) ≠ ⊤ := by
  intro htop
  apply h
  rw [eq_top_iff]
  intro q _
  rw [ValuationSubring.mem_comap]
  rw [IsScalarTower.algebraMap_apply ℚ k Ω]
  exact (ValuationSubring.mem_comap).mp (by rw [htop]; exact Subring.mem_top _)

/-- The `ℚ`-view of `k`, as a `ℚ`-algebra isomorphic to `k`. -/
noncomputable def kviewEquiv : k ≃ₐ[ℚ] ↥(kview k Ω) :=
  (IntermediateField.topEquiv (F := ℚ) (E := k)).symm.trans
    (IntermediateField.equivMap (⊤ : IntermediateField ℚ k) (IsScalarTower.toAlgHom ℚ k Ω))

/-- The `ℚ`-view of `k` is a finite-dimensional `ℚ`-subfield of `Ω`. -/
lemma kview_finiteDimensional : FiniteDimensional ℚ ↥(kview k Ω) :=
  FiniteDimensional.of_surjective (kviewEquiv k Ω).toLinearEquiv.toLinearMap
    (kviewEquiv k Ω).surjective

/-- **The rational prime below a finite place of `Ω` over `k`**, chosen once and for all: the (by
`eq_of_prime_valuation_lt_one`, unique) prime `p` with `A.valuation (p : Ω) < 1`. -/
noncomputable def pof (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) : ℕ :=
  Classical.choose (exists_prime_val_lt_one_of_ne_top (A.comap (algebraMap k Ω)) hA)

lemma pof_prime (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) : (pof k Ω A hA).Prime :=
  (Classical.choose_spec (exists_prime_val_lt_one_of_ne_top (A.comap (algebraMap k Ω)) hA)).1

lemma pof_spec (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) :
    (A.comap (algebraMap k Ω)).valuation (pof k Ω A hA : k) < 1 :=
  (Classical.choose_spec (exists_prime_val_lt_one_of_ne_top (A.comap (algebraMap k Ω)) hA)).2

lemma pof_valuation_lt_one (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) :
    A.valuation (pof k Ω A hA : Ω) < 1 := by
  have h := (Work.SSGRoute.comap_valuation_lt_one_iff A (pof k Ω A hA : k)).mp (pof_spec k Ω A hA)
  rwa [map_natCast] at h

/-- Integer casts lie in a valuation subring. -/
lemma intCast_mem (A : ValuationSubring Ω) (n : ℤ) : (n : Ω) ∈ A := by
  have h := AddSubgroup.int_mul_mem (G := A.toSubring.toAddSubgroup) n (A.one_mem)
  simpa using h

/-- **Uniqueness of the rational prime of value `< 1` at a place of `Ω`.** -/
lemma eq_of_prime_valuation_lt_one (A : ValuationSubring Ω) {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpv : A.valuation (p : Ω) < 1) (hqv : A.valuation (q : Ω) < 1) : p = q := by
  by_contra hne
  have hcop : Nat.Coprime p q := (Nat.Prime.coprime_iff_not_dvd hp).mpr (fun hdvd =>
    hne ((Nat.prime_dvd_prime_iff_eq hp hq).mp hdvd))
  have hicI : IsCoprime (Ideal.span {(p : ℤ)}) (Ideal.span {(q : ℤ)}) :=
    (Ideal.isCoprime_span_singleton_iff (p : ℤ) (q : ℤ)).mpr hcop.isCoprime
  obtain ⟨i, hi, j, hj, hij⟩ := Ideal.isCoprime_iff_exists.mp hicI
  obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton.mp hi
  obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton.mp hj
  have hkey : (1 : Ω) = (a : Ω) * (p : Ω) + (b : Ω) * (q : Ω) := by
    have h2 := congrArg (fun z : ℤ => (z : Ω)) hij
    push_cast at h2
    rw [← h2]
    ring
  have hb_le : ∀ x : Ω, (0 : _) ≤ A.valuation x := fun x => bot_le
  have h1 : A.valuation (1 : Ω) < 1 := by
    rw [hkey]
    refine lt_of_le_of_lt (Valuation.map_add A.valuation _ _) (max_lt ?_ ?_)
    · calc A.valuation ((a : Ω) * (p : Ω))
          = A.valuation (a : Ω) * A.valuation (p : Ω) := Valuation.map_mul _ _ _
        _ ≤ 1 * A.valuation (p : Ω) := mul_le_mul_of_nonneg_right
            ((A.valuation_le_one_iff (a : Ω)).mpr (intCast_mem Ω A a)) (hb_le _)
        _ = A.valuation (p : Ω) := one_mul _
        _ < 1 := hpv
    · calc A.valuation ((b : Ω) * (q : Ω))
          = A.valuation (b : Ω) * A.valuation (q : Ω) := Valuation.map_mul _ _ _
        _ ≤ 1 * A.valuation (q : Ω) := mul_le_mul_of_nonneg_right
            ((A.valuation_le_one_iff (b : Ω)).mpr (intCast_mem Ω A b)) (hb_le _)
        _ = A.valuation (q : Ω) := one_mul _
        _ < 1 := hqv
  rw [Valuation.map_one] at h1
  exact lt_irrefl 1 h1

/-- `pof` is characterised by the valuation inequality. -/
lemma eq_pof_of_prime_valuation_lt_one (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    {q : ℕ} (hq : q.Prime) (hqv : A.valuation (q : Ω) < 1) : q = pof k Ω A hA :=
  eq_of_prime_valuation_lt_one Ω A hq (pof_prime k Ω A hA) hqv (pof_valuation_lt_one k Ω A hA)

/-- **The value `< 1` condition is transported by the pointwise action on places.** -/
lemma smul_valuation_lt_one_iff (g : Ω ≃ₐ[k] Ω) (A : ValuationSubring Ω) (y : Ω) :
    (g • A).valuation (g y) < 1 ↔ A.valuation y < 1 := by
  have hsub : (g • A).valuation.valuationSubring =
      (A.valuation.comap (g.symm : Ω →+* Ω)).valuationSubring := by
    ext x
    simp only [Valuation.mem_valuationSubring_iff,
      ValuationSubring.valuation_le_one_iff, Valuation.comap_apply]
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
    constructor
    · intro h
      rwa [AlgEquiv.smul_def] at h
    · intro h
      rw [AlgEquiv.smul_def]
      simpa using h
  have heq : (g • A).valuation.IsEquiv (A.valuation.comap (g.symm : Ω →+* Ω)) :=
    (Valuation.isEquiv_iff_valuationSubring _ _).mpr hsub
  rw [Valuation.IsEquiv.lt_one_iff_lt_one heq]
  show A.valuation ((g.symm : Ω →+* Ω) (g y)) < 1 ↔ A.valuation y < 1
  rw [show (g.symm : Ω →+* Ω) (g y) = g.symm (g y) from rfl, AlgEquiv.symm_apply_apply]

/-- **`k`-conjugate places have the same rational prime**: the conjugating automorphism fixes `ℚ`,
hence fixes the rational prime of the place. -/
lemma valuation_lt_one_of_isConjPlace {A B : ValuationSubring Ω}
    (h : SSGRoute.IsConjPlace k A B) {q : ℕ} (hq : A.valuation (q : Ω) < 1) :
    B.valuation (q : Ω) < 1 := by
  obtain ⟨σ, hσ⟩ := h
  have h1 := (smul_valuation_lt_one_iff k Ω σ A (q : Ω)).mpr hq
  rw [hσ, map_natCast] at h1
  exact h1

/-- **Descent of ramification from `ℚ` to `k`**: if a `ℚ`-inertia element at `B` preserves `k`
pointwise, then `B` is ramified in `L/k`. -/
lemma isRamifiedIn_base_of_isRamifiedIn_rat_fixing (L : IntermediateField k Ω)
    (B : ValuationSubring Ω) (σ : Ω ≃ₐ[ℚ] Ω) (hI : SSGRoute.IsInertia ℚ B σ)
    (hfix : ∀ x : k, σ (algebraMap k Ω x) = algebraMap k Ω x)
    (hne : σ ∉ (L.restrictScalars ℚ).fixingSubgroup) :
    SSGRoute.IsRamifiedIn k L B := by
  set σ' : Ω ≃ₐ[k] Ω := AlgEquiv.ofRingEquiv (f := σ.toRingEquiv) hfix with hσ'def
  have hσ'apply : ∀ x : Ω, σ' x = σ x := fun x => AlgEquiv.ofRingEquiv_apply hfix x
  have hsmul : (σ' : Ω ≃ₐ[k] Ω) • B = σ • B := by
    ext x
    simp only [ValuationSubring.mem_smul_pointwise_iff_exists, AlgEquiv.smul_def]
    constructor
    · rintro ⟨s, hs, hx⟩
      exact ⟨s, hs, by rw [← hx, hσ'apply]⟩
    · rintro ⟨s, hs, hx⟩
      exact ⟨s, hs, by rw [← hx, hσ'apply]⟩
  have hfixB : σ' ∈ SSGRoute.decomp k B := by
    rw [MulAction.mem_stabilizer_iff, hsmul, hI.1]
  refine ⟨σ', ⟨hfixB, fun x hx => ?_⟩, ?_⟩
  · have h := hI.2 x hx
    simpa only [hσ'apply] using h
  · intro hmem
    apply hne
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    have hxL : x ∈ L := (IntermediateField.mem_restrictScalars ℚ).mp hx
    have h2 := (IntermediateField.mem_fixingSubgroup_iff L σ').mp hmem x hxL
    rw [hσ'apply] at h2
    exact h2

end Base

end Work.SSGRoute.TatePoitouRoute.FinitenessHM
