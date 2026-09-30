import Mathlib
import Submission.Work.N8.step6v2_defs
import Submission.Work.N8.q0_arith_v2
import Submission.Work.N8.q0v2_defs
import Submission.Work.N8.IntegralOnDilIff
import Submission.Work.N8.denom_dvd_of_isDenom
import Submission.Work.N8.integral_coeff_denom
import Submission.Work.BMF.Defs
import Submission.Work.BMF.newton_series

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The per-vertex arithmetic core of Step 6 (`hq0arith`)

Given a polynomial `γ` of degree `≤ k` that is integral on `qℤ` and for which `q` is the
*minimal* positive modulus, we produce an exponent `m` and a modulus `qf` with

* `1 ≤ m ≤ k`, `1 ≤ qf`,
* `q^(1/k) / (k!)^2 ≤ qf`,
* every prime divisor of `qf` divides `k! · q`,
* `qf` divides `A^m - B^m` whenever `γ(A·) - γ(B·)` is integral on `ℤ`.

The construction: let `m0` maximise the least denominator `denom γ m` over `1 ≤ m ≤ k` and set
`qf = denom γ m0 / gcd (denom γ m0) k!`.  The lower bound comes from
`q ≤ ∏_{m=1}^{k} denom γ m ≤ (denom γ m0)^k` together with `gcd ≤ k!`; coprimality from
`denom γ m0 ∣ k! q^k` (`Work.N8.denom_dvd_of_isDenom`); divisibility from
`Work.N8.q0v2_denom_dvd`.
-/

namespace Work.N8

open Polynomial Finset

/-- Every prime divisor of the least denominator `denom γ m` divides `k! · q`, whenever `γ` has
degree `≤ k` and is integral on `qℤ` (`q ≥ 1`).  This is the prime-factor form of
`denom γ m ∣ k! q^k`, which itself follows from `Work.N8.denom_dvd_of_isDenom` and
`coeff_mul_denom_int`. -/
theorem prime_dvd_denom_imp {γ : Polynomial ℝ} {k q p m : ℕ}
    (hq : 1 ≤ q) (hdeg : γ.natDegree ≤ k) (hint : Work.BMF.IntegralOn (q : ℝ) γ)
    (hp : p.Prime) (h : p ∣ Work.N8.denom γ m) : p ∣ k.factorial ∨ p ∣ q := by
  have hIsDenom : IsDenom γ m (k.factorial * q ^ k) := by
    refine ⟨?_, coeff_mul_denom_int k q hdeg hint m⟩
    have : 0 < k.factorial * q ^ k :=
      Nat.mul_pos (Nat.factorial_pos k) (pow_pos (by omega) k)
    omega
  have hpk : p ∣ k.factorial * q ^ k :=
    dvd_trans h (denom_dvd_of_isDenom ⟨_, hIsDenom⟩ hIsDenom)
  rcases hp.dvd_mul.mp hpk with h1 | h2
  · exact Or.inl h1
  · exact Or.inr (hp.dvd_of_dvd_pow h2)

/-- Per-vertex arithmetic core: from a polynomial `γ` of degree `≤ k`, integral on `qℤ` with
`q` minimal, build `m` and `qf` with the properties listed above. -/
theorem exists_mF_qF (k : ℕ) (hk : 1 ≤ k) (γ : Polynomial ℝ) (q : ℕ) (hq : 1 ≤ q)
    (hdeg : γ.natDegree ≤ k) (hint : Work.BMF.IntegralOn (q : ℝ) γ)
    (hmin : ∀ r : ℕ, 1 ≤ r → Work.BMF.IntegralOn (r : ℝ) γ → q ≤ r) :
    ∃ m qf : ℕ,
      1 ≤ m ∧ m ≤ k ∧ 1 ≤ qf ∧
      (q : ℝ) ^ ((1 : ℝ) / (k : ℝ)) / ((k.factorial : ℝ)) ^ 2 ≤ (qf : ℝ) ∧
      (∀ p : ℕ, p.Prime → ¬ p ∣ k.factorial → ¬ p ∣ q → ¬ p ∣ qf) ∧
      (∀ A B : ℕ, Work.BMF.IntegralOn 1
        (Work.BMF.dil (A : ℝ) γ - Work.BMF.dil (B : ℝ) γ) →
        (qf : ℤ) ∣ ((A : ℤ) ^ m - (B : ℤ) ^ m)) := by
  classical
  have hqpos : 0 < q := by omega
  have hden : ∀ m : ℕ, m ≤ k → ∃ β : ℕ, IsDenom γ m β :=
    fun m hm => q0v2_denom_exists hqpos hdeg hm hint
  obtain ⟨m0, hm0mem, hm0eq⟩ :=
    Finset.exists_mem_eq_sup (Finset.Icc 1 k)
      ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hk⟩⟩ (fun m => denom γ m)
  have hm01 : 1 ≤ m0 := (Finset.mem_Icc.mp hm0mem).1
  have hm0k : m0 ≤ k := (Finset.mem_Icc.mp hm0mem).2
  have hβspec : IsDenom γ m0 (denom γ m0) := denom_spec (hden m0 hm0k)
  have hβ0 : 0 < denom γ m0 := by have := hβspec.1; omega
  -- product bound, then the supremum bound
  have hprod : q ≤ ∏ m ∈ Finset.Icc 1 k, denom γ m :=
    q0v2_le_prod_denom k q γ hdeg hden hint hmin
  have hcard : (Finset.Icc 1 k).card = k := by rw [Nat.card_Icc]; omega
  have hleM : (∏ m ∈ Finset.Icc 1 k, denom γ m) ≤ (denom γ m0) ^ k := by
    have h := Finset.prod_le_pow_card (Finset.Icc 1 k) (fun m => denom γ m)
      ((Finset.Icc 1 k).sup (fun m => denom γ m)) (fun m hm => Finset.le_sup hm)
    rw [hcard, hm0eq] at h
    exact h
  have hqM : q ≤ (denom γ m0) ^ k := le_trans hprod hleM
  have hβge : (q : ℝ) ^ ((1 : ℝ) / (k : ℝ)) / ((k.factorial : ℝ)) ≤ (denom γ m0 : ℝ) :=
    q0v2_root_le hk hqM
  -- the least denominator divides `k! · q^k`
  have hgcddvd : Nat.gcd (denom γ m0) k.factorial ∣ denom γ m0 := Nat.gcd_dvd_left _ _
  have hgcdpos : 0 < Nat.gcd (denom γ m0) k.factorial :=
    Nat.gcd_pos_of_pos_left _ hβ0
  have hgcdlefact : Nat.gcd (denom γ m0) k.factorial ≤ k.factorial :=
    Nat.gcd_le_right _ (Nat.factorial_pos k)
  have hfactRpos : (0 : ℝ) < (k.factorial : ℝ) := by positivity
  have hgcdRpos : (0 : ℝ) < (Nat.gcd (denom γ m0) k.factorial : ℝ) := by positivity
  refine ⟨m0, denom γ m0 / Nat.gcd (denom γ m0) k.factorial, hm01, hm0k, ?_, ?_, ?_, ?_⟩
  · rw [Nat.one_le_div_iff hgcdpos]
    exact Nat.gcd_le_left _ hβ0
  · have hcast : ((denom γ m0 / Nat.gcd (denom γ m0) k.factorial : ℕ) : ℝ)
        = (denom γ m0 : ℝ) / (Nat.gcd (denom γ m0) k.factorial : ℝ) :=
      Nat.cast_div hgcddvd (by positivity)
    rw [hcast]
    have hA : (q : ℝ) ^ ((1 : ℝ) / (k : ℝ)) / ((k.factorial : ℝ)) ^ 2
        ≤ (denom γ m0 : ℝ) / (k.factorial : ℝ) := by
      have heq : (q : ℝ) ^ ((1 : ℝ) / (k : ℝ)) / ((k.factorial : ℝ)) ^ 2
          = ((q : ℝ) ^ ((1 : ℝ) / (k : ℝ)) / (k.factorial : ℝ)) / (k.factorial : ℝ) := by
        rw [sq, div_div]
      rw [heq]
      exact div_le_div_of_nonneg_right hβge (le_of_lt hfactRpos)
    have hB : (denom γ m0 : ℝ) / (k.factorial : ℝ)
        ≤ (denom γ m0 : ℝ) / (Nat.gcd (denom γ m0) k.factorial : ℝ) :=
      div_le_div_of_nonneg_left (by positivity) hgcdRpos (by exact_mod_cast hgcdlefact)
    exact le_trans hA hB
  · intro p hp hpfac hpq hpdiv
    have hpβ : p ∣ denom γ m0 := by
      have hsplit : denom γ m0 = Nat.gcd (denom γ m0) k.factorial *
          (denom γ m0 / Nat.gcd (denom γ m0) k.factorial) :=
        (Nat.mul_div_cancel' hgcddvd).symm
      rw [hsplit]
      exact dvd_mul_of_dvd_right hpdiv _
    rcases prime_dvd_denom_imp hq hdeg hint hp hpβ with h1 | h2
    · exact hpfac h1
    · exact hpq h2
  · intro A B hdil
    have hδdeg : (Work.BMF.dil (A : ℝ) γ - Work.BMF.dil (B : ℝ) γ).natDegree ≤ k := by
      refine le_trans (Polynomial.natDegree_sub_le _ _) ?_
      rw [max_le_iff]
      exact ⟨le_trans (Work.BMF.natDegree_dil_le _ _) hdeg,
        le_trans (Work.BMF.natDegree_dil_le _ _) hdeg⟩
    obtain ⟨z, hz⟩ := q0v2_fact_coeff_int hdil hδdeg m0
    have hδcoeff : (Work.BMF.dil (A : ℝ) γ - Work.BMF.dil (B : ℝ) γ).coeff m0
        = γ.coeff m0 * ((A : ℝ) ^ m0 - (B : ℝ) ^ m0) := by
      rw [Polynomial.coeff_sub, Work.BMF.coeff_dil, Work.BMF.coeff_dil]
      ring
    have hz' : (z : ℝ) = (k.factorial : ℝ) *
        (((A : ℤ) ^ m0 - (B : ℤ) ^ m0 : ℤ) : ℝ) * γ.coeff m0 := by
      rw [← hz, hδcoeff]
      push_cast
      ring
    obtain ⟨b, hb⟩ := hβspec.2
    exact q0v2_denom_dvd (β := denom γ m0) (hβ := hβspec.1) (ha := hb)
      (hmin := fun β' hβ' ha' => denom_le (hden m0 hm0k) ⟨hβ', ha'⟩) (hz := hz')

theorem step6v2_hq0arith (k : ℕ) (hk : 1 ≤ k) {V : Type} [Fintype V]
    (T : Finset V) (γ : V → Polynomial ℝ) (q₀ : ℕ) (hq₀ : 1 ≤ q₀)
    (hdeg : ∀ v ∈ T, (γ v).natDegree ≤ k)
    (hint : ∀ v ∈ T, Work.BMF.IntegralOn (q₀ : ℝ) (γ v))
    (hmin : ∀ v ∈ T, ∀ r : ℕ, 1 ≤ r → Work.BMF.IntegralOn (r : ℝ) (γ v) → q₀ ≤ r) :
    ∃ (mF : V → ℕ) (qF : V → ℕ),
      (∀ v ∈ T, 1 ≤ mF v) ∧ (∀ v ∈ T, mF v ≤ k) ∧ (∀ v ∈ T, 1 ≤ qF v) ∧
      (∀ v ∈ T, (q₀ : ℝ) ^ ((1 : ℝ) / (k : ℝ)) / ((k.factorial : ℝ)) ^ 2 ≤ (qF v : ℝ)) ∧
      (∀ v ∈ T, ∀ p : ℕ, p.Prime → ¬ p ∣ k.factorial → ¬ p ∣ q₀ → ¬ p ∣ qF v) ∧
      (∀ v ∈ T, ∀ A B : ℕ, Work.BMF.IntegralOn 1
        (Work.BMF.dil (A : ℝ) (γ v) - Work.BMF.dil (B : ℝ) (γ v)) →
        (qF v : ℤ) ∣ ((A : ℤ) ^ (mF v) - (B : ℤ) ^ (mF v))) := by
  classical
  have hper : ∀ v ∈ T, ∃ p : ℕ × ℕ,
      1 ≤ p.1 ∧ p.1 ≤ k ∧ 1 ≤ p.2 ∧
      (q₀ : ℝ) ^ ((1 : ℝ) / (k : ℝ)) / ((k.factorial : ℝ)) ^ 2 ≤ (p.2 : ℝ) ∧
      (∀ r : ℕ, r.Prime → ¬ r ∣ k.factorial → ¬ r ∣ q₀ → ¬ r ∣ p.2) ∧
      (∀ A B : ℕ, Work.BMF.IntegralOn 1
        (Work.BMF.dil (A : ℝ) (γ v) - Work.BMF.dil (B : ℝ) (γ v)) →
        (p.2 : ℤ) ∣ ((A : ℤ) ^ (p.1) - (B : ℤ) ^ (p.1))) := by
    intro v hv
    obtain ⟨m, qf, h1, h2, h3, h4, h5, h6⟩ :=
      exists_mF_qF k hk (γ v) q₀ hq₀ (hdeg v hv) (hint v hv) (hmin v hv)
    exact ⟨(m, qf), h1, h2, h3, h4, h5, h6⟩
  refine ⟨(fun v => if hv : v ∈ T then (Classical.choose (hper v hv)).1 else 1),
    (fun v => if hv : v ∈ T then (Classical.choose (hper v hv)).2 else 1),
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro v hv
    simp only [dif_pos hv]
    exact (Classical.choose_spec (hper v hv)).1
  · intro v hv
    simp only [dif_pos hv]
    exact (Classical.choose_spec (hper v hv)).2.1
  · intro v hv
    simp only [dif_pos hv]
    exact (Classical.choose_spec (hper v hv)).2.2.1
  · intro v hv
    simp only [dif_pos hv]
    exact (Classical.choose_spec (hper v hv)).2.2.2.1
  · intro v hv p hp hpfac hpq
    simp only [dif_pos hv]
    exact (Classical.choose_spec (hper v hv)).2.2.2.2.1 p hp hpfac hpq
  · intro v hv A B hdil
    simp only [dif_pos hv]
    exact (Classical.choose_spec (hper v hv)).2.2.2.2.2 A B hdil

end Work.N8
