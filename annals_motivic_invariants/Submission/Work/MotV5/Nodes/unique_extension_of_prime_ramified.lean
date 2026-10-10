import Mathlib
import Submission.Work.MotV5.Nodes.UEPR.bridge
import Submission.Work.MotV5.Nodes.UEPR.countL
import Submission.Work.MotV5.Nodes.UEPR.ramificationIdx_ne_one
import Submission.Work.MotV5.Nodes.UEPR.residue_trivial

set_option linter.unusedVariables false -- v435-speed

set_option linter.style.haveILetI false

open scoped WithZero Pointwise
open IsLocalRing

namespace Work.MotV5.Nodes

theorem unique_extension_of_prime_ramified {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω]
    [FiniteDimensional F Ω] [IsGalois F Ω]
    (v : Valuation F (WithZero (Multiplicative ℤ))) {Γ₁ : Type*} [LinearOrderedCommGroupWithZero Γ₁]
    (f : WithZero (Multiplicative ℤ) →*₀ Γ₁) (hf : StrictMono f) (w : Valuation Ω Γ₁)
    (hw : ∀ x : F, w (algebraMap F Ω x) = f (v x))
    {p : ℕ} (hp : p.Prime) (hdeg : Module.finrank F Ω = p)
    (hram : ∃ y : Ω, y ≠ 0 ∧ ∀ x : F, x ≠ 0 → w y ≠ f (v x)) :
    (∀ y : Ω, w y ≤ 1 → ∃ x : F, v x ≤ 1 ∧ w (y - algebraMap F Ω x) < 1) ∧
      (∀ {Γ' : Type} [LinearOrderedCommGroupWithZero Γ'] (f' : WithZero (Multiplicative ℤ) →*₀ Γ')
        (hf' : StrictMono f') (w' : Valuation Ω Γ')
        (hw' : ∀ x : F, w' (algebraMap F Ω x) = f' (v x)),
        ∀ y : Ω, w' y ≤ 1 ↔ w y ≤ 1) := by
  classical
  -- ## 0. On the value group of `F`, `≤ 1` is detected by `v`
  have hf_le : ∀ a : WithZero (Multiplicative ℤ), f a ≤ 1 ↔ a ≤ 1 := by
    intro a
    rw [← map_one f, hf.le_iff_le]
  -- ## 1. `v` is nontrivial: otherwise `w` would be trivial and `hram` impossible
  have hvnt : v.IsNontrivial := by
    by_contra hnt
    have htriv : ∀ x : F, x ≠ 0 → v x = 1 := by
      intro x hx
      have h1 : ¬ (v x ≠ 0 ∧ v x ≠ 1) := fun h => hnt ⟨x, h.1, h.2⟩
      rcases not_and_or.mp h1 with h0 | h1
      · exact absurd ((Valuation.ne_zero_iff v).mpr hx) h0
      · exact not_not.mp h1
    haveI : Valuation.IsTrivialOn F w :=
      ⟨fun x hx => by rw [hw x, htriv x hx, map_one]⟩
    obtain ⟨y, hy0, hy⟩ := hram
    have hy1 : w y ≠ 1 := by
      intro h
      refine hy 1 one_ne_zero ?_
      rw [h, Valuation.map_one, map_one f]
    exact (Valuation.transcendental_of_ne_one F y hy0 hy1)
      (Algebra.IsAlgebraic.isAlgebraic y)
  -- ## 2. The integral closure `B` of the base valuation ring `A = v.valuationSubring`
  haveI hBfr : IsFractionRing ↥(integralClosure ↥(v.valuationSubring) Ω) Ω :=
    IsIntegralClosure.isFractionRing_of_finite_extension ↥(v.valuationSubring) F Ω _
  haveI hBfin : Module.Finite ↥(v.valuationSubring) ↥(integralClosure ↥(v.valuationSubring) Ω) :=
    IsIntegralClosure.finite ↥(v.valuationSubring) F Ω _
  -- ## 3. The bridge: the valuation ring of `w` is a localization of `B`
  have hsub : ∀ x : F, w (algebraMap F Ω x) ≤ 1 ↔ v x ≤ 1 := fun x => by rw [hw x, hf_le]
  obtain ⟨P, hPprime, hPlies, hPc, hbridge⟩ :=
    UEPR.bridge v hvnt w hsub
  haveI := hPprime
  haveI := hPlies
  -- ## 4. The ramification index of the extension is not `1`
  have he1 : P.ramificationIdx ↥(v.valuationSubring) ≠ 1 :=
    UEPR.ramificationIdx_ne_one v hvnt f hf w hw hram P hPc hbridge
  -- ## 5. The fundamental identity at `P`
  have hcount : ((IsLocalRing.maximalIdeal ↥(v.valuationSubring)).primesOver
        ↥(integralClosure ↥(v.valuationSubring) Ω)).ncard
      * (P.ramificationIdx ↥(v.valuationSubring) * P.inertiaDeg ↥(v.valuationSubring)) = p := by
    rw [UEPR.countL v hvnt P, hdeg]
  -- ## 6. Arithmetic: there is exactly one prime over `m_A`, and `e = p`, `f = 1`
  have hef2 : 2 ≤ P.ramificationIdx ↥(v.valuationSubring) * P.inertiaDeg ↥(v.valuationSubring) := by
    have h0 : 0 < P.ramificationIdx ↥(v.valuationSubring) := by
      rcases Nat.eq_zero_or_pos (P.ramificationIdx ↥(v.valuationSubring)) with h | h
      · rw [h, zero_mul, mul_zero] at hcount
        exact absurd hcount.symm hp.ne_zero
      · exact h
    have h1 : 0 < P.inertiaDeg ↥(v.valuationSubring) :=
      Ideal.inertiaDeg_pos P ↥(v.valuationSubring)
    have h2 : 2 ≤ P.ramificationIdx ↥(v.valuationSubring) := by omega
    have h3 : 1 ≤ P.inertiaDeg ↥(v.valuationSubring) := h1
    calc 2 = 2 * 1 := by norm_num
      _ ≤ P.ramificationIdx ↥(v.valuationSubring) * P.inertiaDeg ↥(v.valuationSubring) :=
          Nat.mul_le_mul h2 h3
  have hNdiv : ((IsLocalRing.maximalIdeal ↥(v.valuationSubring)).primesOver
      ↥(integralClosure ↥(v.valuationSubring) Ω)).ncard ∣ p :=
    ⟨_, hcount.symm⟩
  have hN1 : ((IsLocalRing.maximalIdeal ↥(v.valuationSubring)).primesOver
      ↥(integralClosure ↥(v.valuationSubring) Ω)).ncard = 1 := by
    rcases hp.eq_one_or_self_of_dvd _ hNdiv with h | h
    · exact h
    · exfalso
      rw [h] at hcount
      have hef1 : P.ramificationIdx ↥(v.valuationSubring) * P.inertiaDeg ↥(v.valuationSubring) = 1 :=
        Nat.mul_left_cancel hp.pos (hcount.trans (Nat.mul_one p).symm)
      omega
  have hef : P.ramificationIdx ↥(v.valuationSubring) * P.inertiaDeg ↥(v.valuationSubring) = p := by
    have h := hcount
    rw [hN1, one_mul] at h
    exact h
  have hep : P.ramificationIdx ↥(v.valuationSubring) = p := by
    rcases hp.eq_one_or_self_of_dvd _ ⟨_, hef.symm⟩ with h | h
    · exact absurd h he1
    · exact h
  have hfp : P.inertiaDeg ↥(v.valuationSubring) = 1 := by
    have h := hef
    rw [hep] at h
    exact Nat.mul_left_cancel hp.pos (h.trans (Nat.mul_one p).symm)
  refine ⟨UEPR.residue_trivial v hvnt w hsub P hPc hbridge hfp, ?_⟩
  -- ## 7. Uniqueness: every other extension has the same valuation ring
  intro Γ' _ f' hf' w' hw' y
  have hf'_le : ∀ a : WithZero (Multiplicative ℤ), f' a ≤ 1 ↔ a ≤ 1 := by
    intro a
    rw [← map_one f', hf'.le_iff_le]
  have hsub' : ∀ x : F, w' (algebraMap F Ω x) ≤ 1 ↔ v x ≤ 1 := fun x => by rw [hw' x, hf'_le]
  obtain ⟨P', hP'prime, hP'lies, hP'c, hbridge'⟩ := UEPR.bridge v hvnt w' hsub'
  -- `P` and `P'` are two primes over `m_A`, of which there is only one
  have hPmem : P ∈ (IsLocalRing.maximalIdeal ↥(v.valuationSubring)).primesOver
      ↥(integralClosure ↥(v.valuationSubring) Ω) := ⟨hPprime, hPlies⟩
  have hP'mem : P' ∈ (IsLocalRing.maximalIdeal ↥(v.valuationSubring)).primesOver
      ↥(integralClosure ↥(v.valuationSubring) Ω) := ⟨hP'prime, hP'lies⟩
  obtain ⟨Q, hQ⟩ := Set.ncard_eq_one.mp hN1
  have hPP : P' = P := by
    have h1 : P = Q := by
      have : P ∈ ({Q} : Set (Ideal ↥(integralClosure ↥(v.valuationSubring) Ω))) := hQ ▸ hPmem
      simpa using this
    have h2 : P' = Q := by
      have : P' ∈ ({Q} : Set (Ideal ↥(integralClosure ↥(v.valuationSubring) Ω))) := hQ ▸ hP'mem
      simpa using this
    rw [h2, h1]
  have hring : w'.valuationSubring = w.valuationSubring := by
    apply ValuationSubring.toSubring_injective
    subst hPP
    rw [hbridge', hbridge]
  rw [← Valuation.mem_valuationSubring_iff w' y, ← Valuation.mem_valuationSubring_iff w y, hring]

end Work.MotV5.Nodes
