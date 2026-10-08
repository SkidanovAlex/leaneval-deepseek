/-
# Higman's Lemma 12: the `D` case

The last case of the case analysis of Higman's Lemma 12: both axes of the pinned squaring form
are non-abelian (`r, s ≠ 0`) and of different type (`r ≢ ± s`, i.e. `(r + s) % n ≠ 0` and
`(r + n - s) % n ≠ 0`).  Then `Work.Higman.Q3.L12.d_case_congruence` shows that the resonance
congruence (★) has solutions only when `5 * r ≡ 0 (mod n)`, `s ≡ 2 * r`, with support at
`(3 * r, r)` (or the mirror image with `r ↔ s`), which is exactly the `D(n, θ, ε)` shape of
Higman's table.

This file supplies, in the canonical coordinates of `Q3/L12/case_core.lean`, the implication
from the `D` shape to `Good n Q`, and performs the (elementary) bookkeeping that collapses the
double sum onto its single support point and dispatches the two branches of `d_case_congruence`.
-/

import Mathlib
import Submission.Work.Higman.Q3.L12.case_core

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace Work.Higman.Q3.L12

open Work.Higman

open scoped BigOperators

/-! ## Helper lemmas for the `D` case -/

/-- If `n ∣ 5 * r` (with `n > 0`) then `1 + 2 ^ (2 * r)` is coprime to `2 ^ n - 1`.

Indeed `n ∣ 5 * r` forces `n / n.gcd r` to be a divisor of `5`, hence odd; then
`Work.Higman.gcd_two_pow` with `2 * r` gives the claim (`n.gcd (2 * r) = n.gcd r` because
`n.gcd (2 * r) ∣ (2 * r).gcd (5 * r) = r`). -/
lemma caseD_coprime_two_mul {n r : ℕ} (hn : 0 < n) (hr : r ≠ 0) (h5 : n ∣ 5 * r) :
    Nat.Coprime (1 + 2 ^ (2 * r)) (2 ^ n - 1) := by
  have hgcd_eq : n.gcd (2 * r) = n.gcd r := by
    apply Nat.dvd_antisymm
    · have hs_n : n.gcd (2 * r) ∣ n := Nat.gcd_dvd_left _ _
      have hs_2r : n.gcd (2 * r) ∣ 2 * r := Nat.gcd_dvd_right _ _
      have hs_5r : n.gcd (2 * r) ∣ 5 * r := hs_n.trans h5
      have hs_r : n.gcd (2 * r) ∣ r := by
        have h := Nat.dvd_gcd hs_2r hs_5r
        rw [Nat.gcd_mul_right] at h
        norm_num at h
        simpa using h
      exact Nat.dvd_gcd hs_n hs_r
    · refine Nat.dvd_gcd (Nat.gcd_dvd_left n r) ?_
      exact (Nat.gcd_dvd_right n r).trans (dvd_mul_left r 2)
  have hpow5 : (frob n ^ r) ^ 5 = 1 := by
    rw [← pow_mul, show r * 5 = 5 * r by ring]
    exact frob_pow_eq_one_of_dvd (by omega) h5
  have hdiv : orderOf (frob n ^ r) ∣ 5 := orderOf_dvd_iff_pow_eq_one.mpr hpow5
  rw [orderOf_frobeniusEquiv_pow n r hn] at hdiv
  have hodd_r : Odd (n / n.gcd r) := by
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).mp hdiv with h | h
    · rw [h]; exact odd_one
    · rw [h]; exact ⟨2, by norm_num⟩
  have hodd : Odd (n / n.gcd (2 * r)) := by rw [hgcd_eq]; exact hodd_r
  have hg := (gcd_two_pow n (2 * r) hn).mpr hodd
  rw [Nat.Coprime, Nat.gcd_comm, Nat.add_comm 1 (2 ^ (2 * r))]
  exact hg

/-- If `θ ^ 5 = 1` and the `D`-squaring form `u ↦ dCocycle K θ ε u u` is anisotropic, then `ε`
is never one of the "bad" values `ρ⁻¹ + θ⁴ρ · θρ · ρ⁻¹`: for such `ε` the nonzero vector
`(1, θ⁴ρ)` would be isotropic. -/
lemma caseD_epsilon {K : Type*} [Field K] [CharP K 2]
    (θ : K ≃+* K) (hθ5 : θ ^ 5 = 1) (ε : K)
    (hani : ∀ u : K × K, u ≠ 0 → Work.Higman.dCocycle K θ ε u u ≠ 0) :
    ∀ ρ : K, ε ≠ ρ⁻¹ + θ (θ (θ (θ ρ))) * θ ρ * ρ⁻¹ := by
  have hθ5_apply : ∀ x, (θ ^ 5) x = x := by intro x; rw [hθ5]; rfl
  have hε : ε ≠ 0 := by
    intro h0
    have hcomp : Work.Higman.dCocycle K θ ε (1, 1) (1, 1) = ε := by
      simp only [Work.Higman.dCocycle, map_one, mul_one]
      rw [show (1 : K) + ε + 1 = (1 + 1) + ε by abel]
      rw [show (1 : K) + 1 = 0 from CharTwo.add_self_eq_zero 1, zero_add]
    exact hani (1, 1) (by simp) (by rw [hcomp, h0])
  intro ρ
  rcases eq_or_ne ρ 0 with hρ0 | hρne
  · subst hρ0
    intro h
    simp only [inv_zero, map_zero, mul_zero, add_zero] at h
    exact hε h
  · intro h
    have hconv : θ (θ (θ (θ ρ))) = (θ ^ 4) ρ := rfl
    rw [hconv] at h
    have hεmul : ε * ρ = 1 + (θ ^ 4) ρ * θ ρ := by
      rw [h, add_mul, inv_mul_cancel₀ hρne]
      rw [show (θ ^ 4) ρ * θ ρ * ρ⁻¹ * ρ = (θ ^ 4) ρ * θ ρ by
            rw [mul_assoc, inv_mul_cancel₀ hρne, mul_one]]
    have hX : θ ((θ ^ 4) ρ) = ρ := by
      have hh : (θ ^ 1) ((θ ^ 4) ρ) = (θ ^ (1 + 4)) ρ := by rw [pow_add]; rfl
      change (θ ^ 1) ((θ ^ 4) ρ) = ρ
      rw [hh]
      exact hθ5_apply ρ
    have hQ : Work.Higman.dCocycle K θ ε (1, (θ ^ 4) ρ) (1, (θ ^ 4) ρ) = 0 := by
      simp only [Work.Higman.dCocycle, map_one, mul_one, one_mul]
      rw [hX, hεmul]
      rw [show (1 : K) + (1 + (θ ^ 4) ρ * θ ρ) + (θ ^ 4) ρ * θ ρ
            = (1 + 1) + ((θ ^ 4) ρ * θ ρ + (θ ^ 4) ρ * θ ρ) by abel]
      rw [show (1 : K) + 1 = 0 from CharTwo.add_self_eq_zero 1,
          show (θ ^ 4) ρ * θ ρ + (θ ^ 4) ρ * θ ρ = 0 from CharTwo.add_self_eq_zero _,
          add_zero]
    exact hani (1, (θ ^ 4) ρ) (by simp) hQ

/-- The squaring form of `dCocycle` with `θ = frob ^ r`, in coordinates:
`v.1 ^ (1 + 2 ^ r) + ε * (v.1 ^ (2 ^ (3 * r)) * v.2 ^ (2 ^ r)) + v.2 ^ (1 + 2 ^ (2 * r))`. -/
lemma caseD_dCocycle_key {n r : ℕ} (v : GaloisField 2 n × GaloisField 2 n)
    (ε : GaloisField 2 n) :
    Work.Higman.dCocycle (GaloisField 2 n)
        (frob n ^ r : GaloisField 2 n ≃+* GaloisField 2 n) ε v v =
      v.1 ^ (1 + 2 ^ r) + ε * v.1 ^ (2 ^ (3 * r)) * v.2 ^ (2 ^ r) +
        v.2 ^ (1 + 2 ^ (2 * r)) := by
  have h3 : ∀ x : GaloisField 2 n, ((x ^ (2 ^ r)) ^ (2 ^ r)) ^ (2 ^ r) = x ^ (2 ^ (3 * r)) := by
    intro x
    rw [← pow_mul, ← pow_mul, ← pow_add, ← pow_add, show r + (r + r) = 3 * r by ring]
  have h2 : ∀ x : GaloisField 2 n, (x ^ (2 ^ r)) ^ (2 ^ r) = x ^ (2 ^ (2 * r)) := by
    intro x
    rw [← pow_mul, ← pow_add, show r + r = 2 * r by ring]
  simp only [Work.Higman.dCocycle, frob_pow_apply]
  rw [h3 v.1, h2 v.2, mul_pow_two_pow_eq v.1]
  rw [show v.2 * v.2 ^ (2 ^ (2 * r)) = v.2 ^ (1 + 2 ^ (2 * r)) by
        calc v.2 * v.2 ^ (2 ^ (2 * r)) = v.2 ^ 1 * v.2 ^ (2 ^ (2 * r)) := by rw [pow_one]
          _ = v.2 ^ (1 + 2 ^ (2 * r)) := by rw [← pow_add]]
  ring

/-- The two branches of `d_case_congruence` are mutually exclusive: `5r ≡ 0`, `s ≡ 2r` and
`r ≡ 2s` together force `n ∣ r`, hence `r = 0`. -/
lemma caseD_branch_excl {n r s : ℕ} (hr : r < n) (hr0 : r ≠ 0)
    (h1 : 5 * r ≡ 0 [MOD n]) (h2 : s ≡ 2 * r [MOD n]) (h4 : r ≡ 2 * s [MOD n]) : False := by
  have h5r : n ∣ 5 * r := by
    have h : (5 * r) % n = 0 := by simpa only [Nat.ModEq, Nat.zero_mod] using h1
    exact Nat.dvd_of_mod_eq_zero h
  have h2s : 2 * s ≡ 4 * r [MOD n] := by
    have h := h2.mul (Nat.ModEq.refl (n := n) 2)
    simpa [mul_comm, mul_assoc, mul_left_comm] using h
  have hr4r : r ≡ 4 * r [MOD n] := h4.trans h2s
  have h3r : n ∣ 3 * r := by
    have h := (Nat.modEq_iff_dvd' (by omega : r ≤ 4 * r)).mp hr4r
    have he : 4 * r - r = 3 * r := by omega
    rwa [he] at h
  have h2r : n ∣ 2 * r := by
    have h := Nat.dvd_sub h5r h3r
    have he : 5 * r - 3 * r = 2 * r := by omega
    rwa [he] at h
  have hnr : n ∣ r := by
    have h := Nat.dvd_sub h3r h2r
    have he : 3 * r - 2 * r = r := by omega
    rwa [he] at h
  exact hr0 (Nat.eq_zero_of_dvd_of_lt hnr hr)

/-- The swap of the two coordinates of `𝔽_{2ⁿ} × 𝔽_{2ⁿ}`, as an additive equivalence. -/
private def caseD_swap (n : ℕ) :
    GaloisField 2 n × GaloisField 2 n ≃+ GaloisField 2 n × GaloisField 2 n where
  toFun := fun w => (w.2, w.1)
  invFun := fun w => (w.2, w.1)
  left_inv := fun w => by cases w; rfl
  right_inv := fun w => by cases w; rfl
  map_add' := fun a b => by cases a; cases b; rfl

/-- **The canonical `D` shape is `Good`.**  If `5 * r % n = 0`, `0 < r < n`, `C, C' ≠ 0` and
`Q (α, β) = C α ^ (1 + 2 ^ r) + C' β ^ (1 + 2 ^ (2 * r)) + f α ^ (2 ^ (3 * r)) β ^ (2 ^ r)`, then
`Q` is (up to additive coordinate changes) the squaring form of `dCocycle 𝔽 (frob ^ r) ε`. -/
lemma caseD_good_canonical {n r : ℕ} (hn : 2 ≤ n) (hr0 : r ≠ 0) (hr : r < n)
    (h5 : 5 * r % n = 0)
    {C C' f : GaloisField 2 n} (hC : C ≠ 0) (hC' : C' ≠ 0)
    {Q : GaloisField 2 n × GaloisField 2 n → GaloisField 2 n}
    (hQ : ∀ α β : GaloisField 2 n, Q (α, β) = C * α ^ (1 + 2 ^ r) +
        C' * β ^ (1 + 2 ^ (2 * r)) + f * α ^ (2 ^ (3 * r)) * β ^ (2 ^ r))
    (hani : ∀ v : GaloisField 2 n × GaloisField 2 n, v ≠ 0 → Q v ≠ 0) :
    Good n Q := by
  have hn0 : 0 < n := by omega
  have hn1 : 1 ≤ n := by omega
  have hrpos : 0 < r := Nat.pos_of_ne_zero hr0
  have h5dvd : n ∣ 5 * r := Nat.dvd_of_mod_eq_zero h5
  -- the order of `frob ^ r` is `5`
  have hθord : orderOf (frob n ^ r) = 5 := by
    rw [orderOf_frobeniusEquiv_pow n r hn0]
    have hpow5 : (frob n ^ r) ^ 5 = 1 := by
      rw [← pow_mul, show r * 5 = 5 * r by ring]
      exact frob_pow_eq_one_of_dvd hn1 h5dvd
    have hdiv : n / n.gcd r ∣ 5 := by
      have h := orderOf_dvd_iff_pow_eq_one.mpr hpow5
      rwa [orderOf_frobeniusEquiv_pow n r hn0] at h
    have hgdvd : n.gcd r ∣ n := Nat.gcd_dvd_left n r
    have hmul : n.gcd r * (n / n.gcd r) = n := Nat.mul_div_cancel' hgdvd
    have hne1 : n / n.gcd r ≠ 1 := by
      intro h
      rw [h, mul_one] at hmul
      have : n ∣ r := by rw [← hmul]; exact Nat.gcd_dvd_right n r
      exact hr0 (Nat.eq_zero_of_dvd_of_lt this hr)
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).mp hdiv with h | h
    · exact absurd h hne1
    · exact h
  have hm5 : n / n.gcd r = 5 := by
    rw [← orderOf_frobeniusEquiv_pow n r hn0]; exact hθord
  -- the two coprimality hypotheses of `reduce_r_s`
  have hcop : Nat.Coprime (1 + 2 ^ r) (2 ^ n - 1) := by
    have hodd : Odd (n / n.gcd r) := by
      rw [hm5]; exact ⟨2, by norm_num⟩
    have hg := (gcd_two_pow n r hn0).mpr hodd
    rw [Nat.Coprime, Nat.gcd_comm, Nat.add_comm 1 (2 ^ r)]
    exact hg
  have hcop2 : Nat.Coprime (1 + 2 ^ (2 * r)) (2 ^ n - 1) :=
    caseD_coprime_two_mul hn0 hr0 h5dvd
  obtain ⟨Φ, Ψ, ε, hred⟩ := reduce_r_s hn1 hrpos hr hcop hcop2 h5 hC hC'
  -- the key identity: `Ψ (Q (Φ v))` is the `dCocycle` squaring form
  have hkey : ∀ v : GaloisField 2 n × GaloisField 2 n,
      Ψ (Q (Φ v)) = Work.Higman.dCocycle (GaloisField 2 n)
        (frob n ^ r : GaloisField 2 n ≃+* GaloisField 2 n) ε v v := by
    intro v
    rw [hQ (Φ v).1 (Φ v).2, hred v]
    exact (caseD_dCocycle_key (n := n) (r := r) v ε).symm
  have haniD : ∀ u : GaloisField 2 n × GaloisField 2 n, u ≠ 0 →
      Work.Higman.dCocycle (GaloisField 2 n)
        (frob n ^ r : GaloisField 2 n ≃+* GaloisField 2 n) ε u u ≠ 0 := by
    intro u hu h0
    have hΦu : Φ u ≠ 0 := fun h => hu (Φ.injective (by rw [h, map_zero]))
    exact hani (Φ u) hΦu (Ψ.injective (by rw [hkey u, h0, map_zero]))
  have hεcond : ∀ ρ : GaloisField 2 n,
      ε ≠ ρ⁻¹ + (frob n ^ r : GaloisField 2 n ≃+* GaloisField 2 n)
          ((frob n ^ r : GaloisField 2 n ≃+* GaloisField 2 n)
            ((frob n ^ r : GaloisField 2 n ≃+* GaloisField 2 n)
              ((frob n ^ r : GaloisField 2 n ≃+* GaloisField 2 n) ρ))) *
          (frob n ^ r : GaloisField 2 n ≃+* GaloisField 2 n) ρ * ρ⁻¹ :=
    caseD_epsilon (frob n ^ r : GaloisField 2 n ≃+* GaloisField 2 n)
      (by
        have h := pow_orderOf_eq_one (frob n ^ r : GaloisField 2 n ≃+* GaloisField 2 n)
        rwa [hθord] at h)
      ε haniD
  have hθ5 : (frob n ^ r : GaloisField 2 n ≃+* GaloisField 2 n) ^ 5 = 1 := by
    have h := pow_orderOf_eq_one (frob n ^ r : GaloisField 2 n ≃+* GaloisField 2 n)
    rwa [hθord] at h
  have hθne : (frob n ^ r : GaloisField 2 n ≃+* GaloisField 2 n) ≠
      RingEquiv.refl (GaloisField 2 n) := by
    intro h
    have h1 : orderOf (RingEquiv.refl (GaloisField 2 n)) = 1 := orderOf_one
    rw [h, h1] at hθord
    exact absurd hθord (by norm_num)
  have h5n : 5 ∣ n := by
    have hmul : n.gcd r * (n / n.gcd r) = n := Nat.mul_div_cancel' (Nat.gcd_dvd_left n r)
    exact ⟨n.gcd r, by rw [hm5, mul_comm] at hmul; exact hmul.symm⟩
  exact ⟨(frob n ^ r : GaloisField 2 n ≃+* GaloisField 2 n), ε, Φ, Ψ,
    by rw [hθord]; exact ⟨2, by norm_num⟩,
    Or.inr (Or.inr ⟨hθ5, hθne, h5n, hεcond, hkey⟩)⟩

/-! ## The `D` case -/

theorem case_D {n r s : ℕ} (hn : 2 ≤ n) (hr : r < n) (hs : s < n) (hr0 : r ≠ 0) (hs0 : s ≠ 0)
    (hrs : (r + s) % n ≠ 0) (hrms : (r + n - s) % n ≠ 0)
    (hcopr : Nat.Coprime (1 + 2 ^ r) (2 ^ n - 1)) (hcops : Nat.Coprime (1 + 2 ^ s) (2 ^ n - 1))
    {C C' : GaloisField 2 n} (hC : C ≠ 0) (hC' : C' ≠ 0)
    {g : ℕ → ℕ → GaloisField 2 n}
    (Q : GaloisField 2 n × GaloisField 2 n → GaloisField 2 n)
    (hQ : ∀ α β : GaloisField 2 n, Q (α, β) = C * α ^ (1 + 2 ^ r) + C' * β ^ (1 + 2 ^ s) +
        ∑ k ∈ Finset.range n, ∑ l ∈ Finset.range n, g k l * α ^ (2 ^ k) * β ^ (2 ^ l))
    (hani : ∀ v : GaloisField 2 n × GaloisField 2 n, v ≠ 0 → Q v ≠ 0)
    (hres : ∀ k l : ℕ, k < n → l < n → g k l ≠ 0 →
        (1 + 2 ^ s) * 2 ^ k + (1 + 2 ^ r) * 2 ^ l ≡ (1 + 2 ^ r) * (1 + 2 ^ s)
          [MOD 2 ^ n - 1])
    (hsupp : ∃ k l : ℕ, k < n ∧ l < n ∧ g k l ≠ 0) :
    Work.Higman.Q3.L12.Good n Q := by
  have hn0 : 0 < n := by omega
  have hn1 : 1 ≤ n := by omega
  obtain ⟨k₀, l₀, hk₀, hl₀, hg₀⟩ := hsupp
  -- the resonance congruence in the form required by `d_case_congruence`
  have hconv : ∀ k l : ℕ, k < n → l < n → g k l ≠ 0 →
      2 ^ k * (1 + 2 ^ s) + 2 ^ l * (1 + 2 ^ r) ≡ (1 + 2 ^ r) * (1 + 2 ^ s)
        [MOD 2 ^ n - 1] := by
    intro k l hk hl hg
    have h := hres k l hk hl hg
    rw [Nat.mul_comm ((1 : ℕ) + 2 ^ s) (2 ^ k),
      Nat.mul_comm ((1 : ℕ) + 2 ^ r) (2 ^ l)] at h
    exact h
  rcases d_case_congruence hn0 hr hs hk₀ hl₀ hr0 hs0 hrs hrms (hconv k₀ l₀ hk₀ hl₀ hg₀) with
    hA | hB
  · -- Branch A: `5r ≡ 0`, `s ≡ 2r`, support `(3r, r)`.
    rcases hA with ⟨hA5, hAsr, hAkr, hAlr⟩
    have h5 : 5 * r % n = 0 := by simpa only [Nat.ModEq, Nat.zero_mod] using hA5
    have hk₀eq : k₀ = 3 * r % n := by
      have h : k₀ % n = (3 * r) % n := hAkr
      rwa [Nat.mod_eq_of_lt hk₀] at h
    have hl₀eq : l₀ = r % n := by
      have h : l₀ % n = r % n := hAlr
      rwa [Nat.mod_eq_of_lt hl₀] at h
    have hseq : s = 2 * r % n := by
      have h : s % n = (2 * r) % n := hAsr
      rwa [Nat.mod_eq_of_lt hs] at h
    have hsup : ∀ k l : ℕ, k < n → l < n → g k l ≠ 0 → k = k₀ ∧ l = l₀ := by
      intro k l hk hl hg
      rcases d_case_congruence hn0 hr hs hk hl hr0 hs0 hrs hrms (hconv k l hk hl hg) with
        hA' | hB'
      · rcases hA' with ⟨_, _, hkk, hll⟩
        have h1 : k = 3 * r % n := by
          have h : k % n = (3 * r) % n := hkk
          rwa [Nat.mod_eq_of_lt hk] at h
        have h2 : l = r % n := by
          have h : l % n = r % n := hll
          rwa [Nat.mod_eq_of_lt hl] at h
        exact ⟨h1.trans hk₀eq.symm, h2.trans hl₀eq.symm⟩
      · exact (caseD_branch_excl hr hr0 hA5 hAsr hB'.2.1).elim
    have hQ' : ∀ α β : GaloisField 2 n, Q (α, β) = C * α ^ (1 + 2 ^ r) +
        C' * β ^ (1 + 2 ^ s) + g k₀ l₀ * α ^ (2 ^ k₀) * β ^ (2 ^ l₀) := by
      intro α β
      rw [hQ α β, sum_single hk₀ hl₀ hsup α β]
    have hQ'' : ∀ α β : GaloisField 2 n, Q (α, β) = C * α ^ (1 + 2 ^ r) +
        C' * β ^ (1 + 2 ^ (2 * r)) + g k₀ l₀ * α ^ (2 ^ (3 * r)) * β ^ (2 ^ r) := by
      intro α β
      rw [hQ' α β, hk₀eq, hl₀eq, hseq]
      rw [← pow_two_pow_mod hn1 α (3 * r), ← pow_two_pow_mod hn1 β r,
        show β ^ (1 + 2 ^ (2 * r % n)) = β ^ (1 + 2 ^ (2 * r)) by
          rw [pow_add, pow_add, pow_one, ← pow_two_pow_mod hn1 β (2 * r)]]
    exact caseD_good_canonical hn hr0 hr h5 hC hC' hQ'' hani
  · -- Branch B: `5s ≡ 0`, `r ≡ 2s`, support `(s, 3s)`; the `r ↔ s` mirror of branch A.
    rcases hB with ⟨hB5, hBrs, hBls, hBks⟩
    have hs0' : 0 < s := Nat.pos_of_ne_zero hs0
    have h5s : 5 * s % n = 0 := by simpa only [Nat.ModEq, Nat.zero_mod] using hB5
    have hk₀eq : k₀ = s % n := by
      have h : k₀ % n = s % n := hBks
      rwa [Nat.mod_eq_of_lt hk₀] at h
    have hl₀eq : l₀ = 3 * s % n := by
      have h : l₀ % n = (3 * s) % n := hBls
      rwa [Nat.mod_eq_of_lt hl₀] at h
    have hreq : r = 2 * s % n := by
      have h : r % n = (2 * s) % n := hBrs
      rwa [Nat.mod_eq_of_lt hr] at h
    have hsup : ∀ k l : ℕ, k < n → l < n → g k l ≠ 0 → k = k₀ ∧ l = l₀ := by
      intro k l hk hl hg
      rcases d_case_congruence hn0 hr hs hk hl hr0 hs0 hrs hrms (hconv k l hk hl hg) with
        hA' | hB'
      · exact (caseD_branch_excl hs hs0 hB5 hBrs hA'.2.1).elim
      · rcases hB' with ⟨_, _, hll, hkk⟩
        have h1 : k = s % n := by
          have h : k % n = s % n := hkk
          rwa [Nat.mod_eq_of_lt hk] at h
        have h2 : l = 3 * s % n := by
          have h : l % n = (3 * s) % n := hll
          rwa [Nat.mod_eq_of_lt hl] at h
        exact ⟨h1.trans hk₀eq.symm, h2.trans hl₀eq.symm⟩
    -- the mirrored form
    have hQswap : ∀ α β : GaloisField 2 n,
        (fun w : GaloisField 2 n × GaloisField 2 n => Q (w.2, w.1)) (α, β) =
          C' * α ^ (1 + 2 ^ s) + C * β ^ (1 + 2 ^ (2 * s)) +
            g k₀ l₀ * α ^ (2 ^ (3 * s)) * β ^ (2 ^ s) := by
      intro α β
      show Q (β, α) = _
      have hsum : (∑ k ∈ Finset.range n, ∑ l ∈ Finset.range n,
            g k l * β ^ (2 ^ k) * α ^ (2 ^ l)) = g k₀ l₀ * β ^ (2 ^ k₀) * α ^ (2 ^ l₀) :=
        sum_single hk₀ hl₀ hsup β α
      rw [hQ β α, hsum, hreq, hk₀eq, hl₀eq]
      rw [show β ^ (1 + 2 ^ (2 * s % n)) = β ^ (1 + 2 ^ (2 * s)) by
            rw [pow_add, pow_add, pow_one, ← pow_two_pow_mod hn1 β (2 * s)],
        ← pow_two_pow_mod hn1 β s, ← pow_two_pow_mod hn1 α (3 * s)]
      ring
    have haniSwap : ∀ v : GaloisField 2 n × GaloisField 2 n, v ≠ 0 →
        (fun w : GaloisField 2 n × GaloisField 2 n => Q (w.2, w.1)) v ≠ 0 := by
      intro v hv h0
      have hv' : (v.2, v.1) ≠ 0 := by
        intro h
        exact hv (by cases v with | mk a b => simp_all)
      exact hani (v.2, v.1) hv' h0
    obtain ⟨θ, ε, Φ₁, Ψ₁, hodd, hdisj⟩ :=
      caseD_good_canonical hn hs0 hs h5s hC' hC hQswap haniSwap
    refine ⟨θ, ε, Φ₁.trans (caseD_swap n), Ψ₁, hodd, ?_⟩
    exact hdisj

end Work.Higman.Q3.L12
