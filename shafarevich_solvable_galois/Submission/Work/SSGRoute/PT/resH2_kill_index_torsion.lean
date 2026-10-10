import Mathlib.FieldTheory.KrullTopology
import Mathlib.RingTheory.Henselian
import Mathlib.Data.Int.Star
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Submission.Work.SSGRoute.PT.cardH2_units_openSubgroup_decomp
import Submission.Work.SSGRoute.PT.corH2_resH2_eq_index
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `resH2` kills the index-torsion

`Work.SSGRoute.PT.resH2_kill_index_torsion`: for a finite place `A` of `Ω` over a number field `k`,
an open subgroup `U ≤ D_A = decomp k A` of finite index `n`, and a class `e ∈ H²(D_A, Ωˣ)` with
`n • e = 0`, the restriction of `e` to `U` vanishes.

## Reduction (formalised below)

The corestriction–restriction identity `PT.corH2_resH2_eq_index` gives

  `corH2 U hU (Ωˣ) (resH2 U e) = n • e = 0`,

so the statement is the *injectivity of `corH2 U hU (Ωˣ)` on the `n`-torsion*.  By the Bézout
decomposition of an `n`-torsion element into its prime-power components
(`exists_add_decomposition_of_coprime_mul_zsmul_eq_zero` below), it is enough that
`corH2 U hU (Ωˣ)` be injective on the `p`-power torsion for every prime `p ∣ n`; this is the
content of `resH2_eq_zero_of_nsmul_eq_zero_of_primePower`, proved here by strong induction on the
exponent.

## The arithmetic input

The remaining statement — `corH2 U hU (Ωˣ)` injective on the `p`-power torsion for `p ∣ [D_A : U]`
— is Milne, *ADT*, (1.1b) at the open subgroup `U`: the compatibility of the local invariants,

  `inv_U ∘ corH2 = inv_{D_A}`   (equivalently `inv_U (resH2 α) = [D_A : U] · inv_{D_A} α`),

which under the isomorphisms `H²(·, Ωˣ) ≅ Br(ℚ/ℤ)` says that `corH2` is the invariant-preserving
identification while `resH2` is multiplication by the index `[D_A : U]` (in particular `corH2` is
injective, whereas `resH2` has the `[D_A : U]`-torsion as kernel).  It is stated below as
`corH2_injective_pPowerTorsion_of_dvd_index`; this is the node the whole file depends on.
-/

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 1000000
set_option linter.style.haveILetI false

namespace Work.SSGRoute.PT

open Work

noncomputable section

/-- **The two-factor Bézout decomposition of an `m · k`-torsion element** (for coprime `m`, `k`):
`e = e₁ + e₂` with `m • e₁ = 0` and `k • e₂ = 0`.

This is the elementary Chinese-remainder step: with `c·m + d·k = 1` (`Nat.gcd_eq_gcd_ab`), take
`e₁ := d·k • e` and `e₂ := c·m • e`. -/
theorem exists_add_decomposition_of_coprime_mul_zsmul_eq_zero {A : Type*} [AddCommGroup A]
    {m k : ℕ} (hcop : m.Coprime k) (e : A) (he : ((m * k : ℕ) : ℤ) • e = 0) :
    ∃ e₁ e₂ : A, e = e₁ + e₂ ∧ (m : ℤ) • e₁ = 0 ∧ (k : ℤ) • e₂ = 0 := by
  have hbez : (Nat.gcdB m k : ℤ) * (k : ℤ) + (Nat.gcdA m k : ℤ) * (m : ℤ) = 1 := by
    have h := Nat.gcd_eq_gcd_ab m k
    rw [hcop.gcd_eq_one, Nat.cast_one] at h
    linarith
  refine ⟨((Nat.gcdB m k : ℤ) * (k : ℤ)) • e, ((Nat.gcdA m k : ℤ) * (m : ℤ)) • e, ?_, ?_, ?_⟩
  · rw [← add_zsmul, hbez, one_zsmul]
  · have h1 : (m : ℤ) • ((Nat.gcdB m k : ℤ) * (k : ℤ)) • e
        = (Nat.gcdB m k : ℤ) • (((m * k : ℕ) : ℤ) • e) := by
      rw [← mul_smul, ← mul_smul]
      congr 1
      push_cast; ring
    rw [h1, he, smul_zero]
  · have h1 : (k : ℤ) • ((Nat.gcdA m k : ℤ) * (m : ℤ)) • e
        = (Nat.gcdA m k : ℤ) • (((m * k : ℕ) : ℤ) • e) := by
      rw [← mul_smul, ← mul_smul]
      congr 1
      push_cast; ring
    rw [h1, he, smul_zero]

/-- **The arithmetic input at the open subgroup `U`** (Milne, *ADT*, (1.1b), `p`-torsion form):
the corestriction `corH2 U hU (Ωˣ) : H²(U, Ωˣ) → H²(D_A, Ωˣ)` is injective on the `p`-torsion, for
every prime `p` dividing the index `[D_A : U]`.

Under the invariant isomorphisms `H²(·, Ωˣ) ≅ ℚ/ℤ` this is the statement `inv_{D_A} ∘ corH2 = inv_U`
(equivalently `inv_U (resH2 α) = [D_A : U] · inv_{D_A} α`); it is the class-formation axiom (1.1b)
for the local class formation `(D_A, Ωˣ)`, in the (weakest) `p`-torsion form.  Its `p`-primary
consequences are derived from it below. -/
theorem corH2_injective_ptorsion_of_dvd_index (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (A : ValuationSubring Ω)
    (hA : SSGRoute.IsFinPlace k A) (U : Subgroup ↥(SSGRoute.decomp k A))
    (hU : IsOpen (U : Set ↥(SSGRoute.decomp k A))) [U.FiniteIndex]
    [Fintype (↥(SSGRoute.decomp k A) ⧸ U)] (p : ℕ) [Fact p.Prime]
    (hp : p ∣ Nat.card (↥(SSGRoute.decomp k A) ⧸ U))
    (x : Work.AbsoluteKummer.H2 ↥U (Additive (Units Ω)))
    (hx : p • x = 0)
    (hcor : Work.SSGRoute.PT.corH2 U hU (Additive (Units Ω)) x = 0) :
    x = 0 := by sorry

/-- **`p`-power torsion from `p`-torsion.**  If the corestriction is injective on the `p`-torsion
of `H²(U, Ωˣ)`, then it is injective on the `p`-power torsion: for `p ^ (j+1) • x = 0` the element
`p ^ j • x` has order dividing `p`, so it vanishes; hence the order of `x` divides `p ^ j` and
induction on `j` applies. -/
theorem corH2_injective_pPowerTorsion_of_ptorsion
    (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (U : Subgroup ↥(SSGRoute.decomp k A)) (hU : IsOpen (U : Set ↥(SSGRoute.decomp k A)))
    [U.FiniteIndex] [Fintype (↥(SSGRoute.decomp k A) ⧸ U)]
    (hnode : ∀ (p : ℕ), Nat.Prime p → p ∣ Nat.card (↥(SSGRoute.decomp k A) ⧸ U) →
      ∀ x : Work.AbsoluteKummer.H2 ↥U (Additive (Units Ω)), p • x = 0 →
        corH2 U hU (Additive (Units Ω)) x = 0 → x = 0) :
    ∀ (p : ℕ), Nat.Prime p → p ∣ Nat.card (↥(SSGRoute.decomp k A) ⧸ U) →
      ∀ x : Work.AbsoluteKummer.H2 ↥U (Additive (Units Ω)), (∃ m : ℕ, p ^ m • x = 0) →
        corH2 U hU (Additive (Units Ω)) x = 0 → x = 0 := by
  intro p hpprime hpdvd x hx hcor
  obtain ⟨m, hm⟩ := hx
  induction m with
  | zero =>
    -- `p ^ 0 = 1`
    rw [pow_zero, one_nsmul] at hm
    exact hm
  | succ j ih =>
    -- `p ^ (j+1) • x = 0`: the element `p ^ j • x` is `p`-torsion
    have hpy : p • (p ^ j • x) = 0 := by
      rw [← mul_nsmul x (p ^ j) p, ← pow_succ p j]
      exact hm
    have hcory : corH2 U hU (Additive (Units Ω)) (p ^ j • x) = 0 := by
      rw [map_nsmul, hcor, smul_zero]
    have hy : p ^ j • x = 0 :=
      hnode p hpprime hpdvd _ hpy hcory
    exact ih hy

/-- **The reduction.**  If the corestriction is injective on the `p`-power torsion at `U` for every
prime `p` dividing the index, then `resH2 U` kills the index-torsion.

Strong induction on the exponent `m`: writing `m = p ^ a · k` with `k < m` coprime to `p`, the
Bézout decomposition splits `e = e₁ + e₂` with `p ^ a • e₁ = 0` and `k • e₂ = 0`.  The first
summand is handled by the hypothesis at `p`, applied to `resH2 U e₁` — whose corestriction is
`[D_A : U] • e₁ = 0` because `m • e₁ = 0` and `m ∣ [D_A : U]` — and the second by the induction
hypothesis at `k`. -/
theorem resH2_eq_zero_of_nsmul_eq_zero_of_primePower
    (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (U : Subgroup ↥(SSGRoute.decomp k A)) (hU : IsOpen (U : Set ↥(SSGRoute.decomp k A)))
    [U.FiniteIndex] [Fintype (↥(SSGRoute.decomp k A) ⧸ U)]
    (hnode : ∀ (p : ℕ), Nat.Prime p → p ∣ Nat.card (↥(SSGRoute.decomp k A) ⧸ U) →
      ∀ x : Work.AbsoluteKummer.H2 ↥U (Additive (Units Ω)), (∃ m : ℕ, p ^ m • x = 0) →
        corH2 U hU (Additive (Units Ω)) x = 0 → x = 0) :
    ∀ e : Work.AbsoluteKummer.H2 ↥(SSGRoute.decomp k A) (Additive (Units Ω)),
      Nat.card (↥(SSGRoute.decomp k A) ⧸ U) • e = 0 → resH2 U e = 0 := by
  classical
  set N := Nat.card (↥(SSGRoute.decomp k A) ⧸ U) with hN
  have hNpos : 0 < N := by
    rw [hN, Nat.card_eq_fintype_card]
    exact Fintype.card_pos_iff.mpr
      ⟨((1 : ↥(SSGRoute.decomp k A)) : ↥(SSGRoute.decomp k A) ⧸ U)⟩
  suffices H : ∀ m : ℕ, 0 < m → m ∣ N → ∀ e : Work.AbsoluteKummer.H2 ↥(SSGRoute.decomp k A)
      (Additive (Units Ω)), m • e = 0 → Work.SSGRoute.PT.resH2 U e = 0 by
    intro e he
    exact H N hNpos (dvd_refl N) e (by rwa [hN] at he)
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hmpos hmdvd e he
    rcases Nat.lt_or_ge 1 m with h1 | h1
    · obtain ⟨p, hpprime, hpm⟩ := Nat.exists_prime_and_dvd (by omega : m ≠ 1)
      haveI : Fact p.Prime := ⟨hpprime⟩
      set a := padicValNat p m with ha
      set kk := m / p ^ a with hk
      have hapos : 0 < a := by
        by_contra h
        rw [Nat.not_lt] at h
        have h0 : a = 0 := Nat.eq_zero_of_le_zero h
        rw [ha] at h0
        rcases (padicValNat.eq_zero_iff.mp h0) with h2 | h2 | h2
        · exact hpprime.ne_one h2
        · exact hmpos.ne' h2
        · exact h2 hpm
      have hsplit : m = p ^ a * kk := by
        rw [hk, ha]
        exact (Nat.mul_div_cancel' (pow_padicValNat_dvd (p := p) (n := m))).symm
      have hone : 1 < p ^ a := Nat.one_lt_pow hapos.ne' hpprime.one_lt
      have hkkpos : 0 < kk := by
        rw [hk]
        exact Nat.div_pos (Nat.le_of_dvd hmpos (pow_padicValNat_dvd (p := p) (n := m)))
          (pow_pos hpprime.pos a)
      have hkkm : kk < m := by
        rw [hk]
        exact Nat.div_lt_self hmpos hone
      have hkkdvd : kk ∣ N := dvd_trans (by rw [hsplit]; exact dvd_mul_left kk (p ^ a)) hmdvd
      have hcop : (p ^ a).Coprime kk := by
        rw [Nat.coprime_pow_left_iff hapos]
        refine (Nat.Prime.coprime_iff_not_dvd hpprime).mpr ?_
        intro hcon
        have h1' := padicValNat.div_pow (p := p) (a := a) (b := m)
          (by rw [ha]; exact pow_padicValNat_dvd (p := p) (n := m))
        rw [ha, Nat.sub_self, ← hk] at h1'
        rcases (padicValNat.eq_zero_iff.mp h1') with h2 | h2 | h2
        · exact hpprime.ne_one h2
        · exact hkkpos.ne' h2
        · exact h2 hcon
      obtain ⟨e₁, e₂, hsum, h1', h2'⟩ :=
        exists_add_decomposition_of_coprime_mul_zsmul_eq_zero hcop e
          (by rw [natCast_zsmul e (p ^ a * kk), ← hsplit]; exact he)
      have hpa0 : p ^ a • e₁ = 0 := by
        rw [← natCast_zsmul e₁ (p ^ a)]
        exact h1'
      have hkk0 : kk • e₂ = 0 := by
        rw [← natCast_zsmul e₂ kk]
        exact h2'
      have hm0 : m • e₁ = 0 := by
        rw [hsplit, mul_nsmul e₁ (p ^ a) kk, hpa0, smul_zero]
      have hres1 : Work.SSGRoute.PT.resH2 U e₁ = 0 := by
        refine hnode p hpprime (dvd_trans hpm hmdvd) _ ⟨a, ?_⟩ ?_
        · rw [← map_nsmul, hpa0, map_zero]
        · rw [Work.SSGRoute.PT.corH2_resH2_eq_index, Subgroup.index_eq_card U, ← hN]
          obtain ⟨t, ht⟩ := hmdvd
          rw [ht, mul_nsmul e₁ m t, hm0, smul_zero]
      have hres2 : Work.SSGRoute.PT.resH2 U e₂ = 0 :=
        ih kk hkkm hkkpos hkkdvd e₂ hkk0
      rw [hsum, map_add, hres1, hres2]
      exact add_zero (0 : Work.AbsoluteKummer.H2 ↥U (Additive (Units Ω)))
    · have hm1 : m = 1 := by omega
      have he0 : e = 0 := by rw [hm1, one_nsmul] at he; exact he
      rw [he0, map_zero]

theorem resH2_kill_index_torsion (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (A : ValuationSubring Ω)
    (hA : SSGRoute.IsFinPlace k A) (U : Subgroup ↥(SSGRoute.decomp k A))
    (hU : IsOpen (U : Set ↥(SSGRoute.decomp k A))) [U.FiniteIndex]
    [Fintype (↥(SSGRoute.decomp k A) ⧸ U)] :
    ∀ e : Work.AbsoluteKummer.H2 ↥(SSGRoute.decomp k A) (Additive (Units Ω)),
      Nat.card (↥(SSGRoute.decomp k A) ⧸ U) • e = 0 → Work.SSGRoute.PT.resH2 U e = 0 :=
  resH2_eq_zero_of_nsmul_eq_zero_of_primePower k Ω A hA U hU
    (corH2_injective_pPowerTorsion_of_ptorsion k Ω A hA U hU
      (fun p hp hpdvd x hx hcor => by
        haveI : Fact p.Prime := ⟨hp⟩
        exact corH2_injective_ptorsion_of_dvd_index (k := k) (Ω := Ω) (A := A) (hA := hA)
          (U := U) (hU := hU) (p := p) hpdvd x hx hcor))

end

end Work.SSGRoute.PT
