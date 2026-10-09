import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.ZConstruction.localKummerDictionary
import Submission.Work.SSGRoute.kummerChar_eq_zero_of_isInertia_of_unit
import Submission.Work.SSGRoute.ZConstruction.kummerCharZMod_fixingSubgroup_mul_pow
import Submission.Work.SSGRoute.grunwald_kummer_idx
import Submission.Work.SSGRoute.place_basics
import Submission.NK.TameStructureDeep.Tame.InertiaFieldAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The Kummer character of a local unit kills the inertia

Let `k` be a number field, `Ω` an algebraic closure of `k`, `K/k` a finite Galois level, `p` a
prime, `ζ ∈ K` a primitive `p`-th root of unity.  For a finite place `A` of `Ω` at which `p` is a
*unit* (`¬ A.valuation (p : Ω) < 1`, together with the integrality of `p` at `A`) and an element
`a ∈ Kˣ` which is a `p`-th power times a unit at `A`, the global Kummer character
`Work.SSGRoute.kummerCharZMod p hζ a` vanishes on the inertia group of `A` over `K`.

This is the general-`p` form of `Work.SSGRoute.kummerChar_eq_zero_of_isInertia_of_unit` (the case
`p = 2`): a Kummer extension `K(a^{1/p})/K` with `p ∤ v_A(a)` is unramified at `A`.

## Proof

Writing `a = c ^ p · u` with `u` a unit at `A` and `γ = √[p]a` the chosen `p`-th root, the element
`δ = γ / c` satisfies `δ ^ p = u`, so `δ` is a unit at `A`.  For inertia `σ` set `r = σδ/δ`; then
`r ^ p = 1`, and `r ∈ A` with `r ≡ 1` modulo the maximal ideal of `A` (the inertia condition on
`δ`).  Since `(p : ↥A)` is a unit, reduction modulo the maximal ideal is injective on the `p`-torsion
of `↥A` (`NK.TameStructureDeep.Tame.eq_of_residue_eq_of_pow_eq_one`), so `r = 1`, i.e. `σδ = δ`, i.e.
`σγ = γ`, and `kummerIdx_eq_zero_of_apply_eq` gives the claim.
-/

namespace Work.SSGRoute

open scoped Pointwise

set_option linter.unusedVariables false

/-- A `p`-th power equal to `1` in the value group of a valuation subring forces the value to be
`1`. -/
private lemma val_eq_one_of_pow_eq_one {k : Type} [Field k] (A : ValuationSubring k)
    {x : k} {p : ℕ} (hp : p ≠ 0) (h : A.valuation x ^ p = 1) : A.valuation x = 1 := by
  have hle : A.valuation x ≤ 1 := by
    by_contra hlt
    rw [not_le] at hlt
    have h1 : 1 < A.valuation x ^ p := one_lt_pow₀ hlt hp
    rw [h] at h1
    exact lt_irrefl 1 h1
  have hge : 1 ≤ A.valuation x := by
    by_contra hlt
    rw [not_le] at hlt
    have h1 : A.valuation x ^ p < 1 :=
      pow_lt_one₀ (show 0 ≤ A.valuation x from zero_le) hlt hp
    rw [h] at h1
    exact lt_irrefl 1 h1
  exact le_antisymm hle hge

/-- Natural numbers are integral at a valuation subring. -/
private lemma natCast_mem (k : Type) [Field k] (A : ValuationSubring k) (n : ℕ) :
    (n : k) ∈ A := by
  induction n with
  | zero => simpa using A.zero_mem
  | succ n ih => simpa [Nat.cast_succ] using A.add_mem (n : k) 1 ih A.one_mem

/-- **The Kummer character of a local unit kills the inertia.**  If `p` is a unit at `A` and `u` is a
unit at `A`, then the Kummer character of `u` vanishes on the inertia group of `A` over `K`: the
Kummer extension `K(u^{1/p})/K` is unramified at `A`. -/
theorem kummerCharZMod_eq_zero_of_isInertia_of_unit
    (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    [IsAlgClosed Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (p : ℕ) [Fact p.Prime] (ζ : ↥K) (hζ : IsPrimitiveRoot ζ p)
    (A : ValuationSubring Ω) (hp : ¬ A.valuation (p : Ω) < 1)
    (u : (↥K)ˣ) (hu : A.valuation (algebraMap ↥K Ω (u : ↥K)) = 1)
    (σ : Ω ≃ₐ[↥K] Ω) (hσ : SSGRoute.IsInertia (k := ↥K) A σ) :
    Work.SSGRoute.kummerCharZMod (Ω := Ω) (K := ↥K) p (ζ := ζ) hζ u σ = 0 := by
  classical
  -- the chosen `p`-th root `γ` of the unit `u`, again a unit at `A`
  let γ : Ω := kummerSqrtZMod (Ω := Ω) (K := ↥K) p u
  have hγdef : γ = kummerSqrtZMod (Ω := Ω) (K := ↥K) p u := rfl
  have hγpow : γ ^ p = algebraMap ↥K Ω (u : ↥K) := by
    rw [hγdef, kummerSqrtZMod_pow]
  have hγne : γ ≠ 0 := by
    intro h0
    have h1 := hγpow
    rw [h0, zero_pow (Fact.out : p.Prime).ne_zero] at h1
    exact (map_ne_zero (algebraMap ↥K Ω)).mpr (Units.ne_zero u) h1.symm
  have hvalγ : A.valuation γ = 1 := by
    refine val_eq_one_of_pow_eq_one A (Fact.out : p.Prime).ne_zero ?_
    rw [← Valuation.map_pow, hγpow, hu]
  have hγmem : γ ∈ A := (ValuationSubring.valuation_le_one_iff A γ).mp (le_of_eq hvalγ)
  -- `σ` preserves `A`, so `σ γ` is a unit at `A` as well
  have hσA : σ • A = A := MulAction.mem_stabilizer_iff.mp hσ.1
  have hσγmem : σ γ ∈ A := by
    have h := ValuationSubring.smul_mem_pointwise_smul σ γ A hγmem
    rwa [hσA, AlgEquiv.smul_def] at h
  -- the Kummer ratio `r = σ γ / γ` is a `p`-th root of unity in `A`, congruent to `1` mod `m_A`
  let r : Ω := σ γ / γ
  have hrdef : r = σ γ / γ := rfl
  have hrpow : r ^ p = 1 := by
    have hσγpow : (σ γ) ^ p = γ ^ p := by
      rw [← map_pow, hγpow, AlgEquiv.commutes σ (u : ↥K)]
    rw [hrdef, div_pow, hσγpow, div_self (pow_ne_zero p hγne)]
  have hrmem : r ∈ A := by
    rw [← ValuationSubring.valuation_le_one_iff, hrdef, Valuation.map_div, hvalγ, div_one]
    exact ValuationSubring.valuation_le_one A ⟨σ γ, hσγmem⟩
  have hrsub : A.valuation (r - 1) < 1 := by
    have hlt : A.valuation (σ γ - γ) < 1 := hσ.2 γ hγmem
    have heq : (σ γ - γ) / γ = r - 1 := by
      rw [sub_div, hrdef, div_self hγne]
    rw [← heq, Valuation.map_div, hvalγ, div_one]
    exact hlt
  -- `(p : ↥A)` is a unit, so reduction is injective on the `p`-torsion
  have hpmem : (p : Ω) ∈ A := natCast_mem Ω A p
  have hpeq : IsUnit ((p : ℕ) : ↥A) := by
    have hunitA : IsUnit (⟨(p : Ω), hpmem⟩ : ↥A) := by
      by_contra h
      exact hp ((valuation_lt_one_iff_not_isUnit A ⟨(p : Ω), hpmem⟩).mpr h)
    have hcast : ((p : ℕ) : ↥A) = ⟨(p : Ω), hpmem⟩ := Subtype.ext (by simp)
    rw [hcast]
    exact hunitA
  have hres1 : IsLocalRing.residue ↥A (⟨r, hrmem⟩ : ↥A) = 1 := by
    have hmem : (⟨r, hrmem⟩ : ↥A) - 1 ∈ IsLocalRing.maximalIdeal ↥A := by
      rw [ValuationSubring.valuation_lt_one_iff]
      exact hrsub
    have h0 : IsLocalRing.residue ↥A ((⟨r, hrmem⟩ : ↥A) - 1) = 0 :=
      (IsLocalRing.residue_eq_zero_iff _).mpr hmem
    rw [map_sub, map_one, sub_eq_zero] at h0
    exact h0
  have hxpow : (⟨r, hrmem⟩ : ↥A) ^ p = 1 := by
    apply Subtype.ext
    show (r : Ω) ^ p = (1 : Ω)
    rw [hrpow]
  have hxy : (⟨r, hrmem⟩ : ↥A) = 1 :=
    NK.TameStructureDeep.Tame.eq_of_residue_eq_of_pow_eq_one hpeq hxpow (one_pow p)
      (by rw [hres1, map_one])
  have hr1 : r = 1 := by
    simpa using congrArg (fun z : ↥A => (z : Ω)) hxy
  have hσγ : σ γ = γ := by
    have h1 : σ γ / γ = 1 := by rw [← hrdef]; exact hr1
    exact (div_eq_one_iff_eq hγne).mp h1
  rw [kummerCharZMod_apply]
  refine kummerIdx_eq_zero_of_apply_eq p hζ u (kummerSqrtUnitZMod (Ω := Ω) p u)
    (kummerSqrtUnitZMod_pow (Ω := Ω) p u) σ ?_
  simpa [hγdef, kummerSqrtUnitZMod_coe] using hσγ

theorem kummerCharZ_eq_zero_of_isInertia_of_valuation_dvd
    (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (p : ℕ) [Fact p.Prime] (ζ : ↥K) (hζ : IsPrimitiveRoot ζ p)
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) (hp : ¬ A.valuation (p : Ω) < 1)
    (a : (↥K)ˣ)
    (ha : ∃ c : ↥K, ∃ u : (↥K)ˣ, a = c ^ p * u ∧
      A.valuation (algebraMap ↥K Ω (u : ↥K)) = 1)
    (σ : Ω ≃ₐ[↥K] Ω) (hσ : SSGRoute.IsInertia (k := ↥K) A σ) :
    Work.SSGRoute.kummerCharZMod (Ω := Ω) (K := ↥K) p (ζ := ζ) hζ a σ = 0 := by
  classical
  obtain ⟨c, u, hcu, hu⟩ := ha
  have hc : c ≠ 0 := by
    intro h0
    refine Units.ne_zero a ?_
    rw [hcu, h0, zero_pow (Fact.out : p.Prime).ne_zero, zero_mul]
  let w : (↥K)ˣ := Units.mk0 c hc
  have haw : a = u * w ^ p := by
    apply Units.ext
    show (a : ↥K) = (u : ↥K) * ((w : ↥K) ^ p)
    rw [hcu]
    show c ^ p * (u : ↥K) = (u : ↥K) * (c ^ p)
    ring
  have hred : Work.SSGRoute.kummerCharZMod (Ω := Ω) (K := ↥K) p (ζ := ζ) hζ a σ
      = Work.SSGRoute.kummerCharZMod (Ω := Ω) (K := ↥K) p (ζ := ζ) hζ u σ := by
    rw [kummerCharZMod_apply, kummerCharZMod_apply]
    exact kummerIdx_eq_of_mul_pow p hζ a u w haw
      (kummerSqrtUnitZMod (Ω := Ω) p a) (kummerSqrtUnitZMod (Ω := Ω) p u)
      (kummerSqrtUnitZMod_pow (Ω := Ω) p a) (kummerSqrtUnitZMod_pow (Ω := Ω) p u) σ
  rw [hred]
  exact kummerCharZMod_eq_zero_of_isInertia_of_unit k Ω K p ζ hζ A hp u hu σ hσ

end Work.SSGRoute
