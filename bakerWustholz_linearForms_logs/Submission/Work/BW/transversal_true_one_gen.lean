import Mathlib
import Submission.Work.BW.multiplicity_engine

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

open scoped BigOperators

/-- **Transversal exclusion, `ε = true`, `ρ = 1`**: here the classes may collide, so only
`cardMod ≥ 1` is available; (E0) gives the contradiction. -/
lemma transversal_true_one_gen {N r : ℕ} (hNr : N < r)
    (δ : Fin (N + 1) → ℝ) (hδnn : ∀ i, 0 ≤ δ i) (hδ1 : ∀ i, 1 ≤ ⌊δ i⌋₊)
    (Sq Tq : ℕ → ℕ)
    (hE0 : ∀ j : Fin N, ((r : ℝ) + 1) * δ j.succ < (Tq 0 : ℝ) + 1)
    (θ : Fin N → ℂ) (M : Fin 1 → Fin N → ℤ) (m : ℕ)
    (hM : PrimSys M) (hm : m + 1 ≤ 1)
    (hcard : 1 ≤ cardMod true M θ (Sq m))
    (hineq : ∀ (J : Finset (Fin N)) (hJ : J.card = 1), minorJ M J hJ ≠ 0 →
      (((Tq m + 1).choose 1 : ℕ) : ℝ) * (cardMod true M θ (Sq m) : ℝ) *
        ((N + 1 - 1).factorial : ℝ) * |(minorJ M J hJ : ℝ)| *
        ((⌊δ 0⌋₊ : ℕ) : ℝ) * ∏ i ∈ Jᶜ, ((⌊δ i.succ⌋₊ : ℕ) : ℝ) ≤
        ((N + 1).factorial : ℝ) * ∏ i, ((⌊δ i⌋₊ : ℕ) : ℝ)) :
    False := by
  classical
  obtain ⟨J, hJ, hΔ⟩ := exists_minorJ_ne_zero M hM.1
  obtain ⟨j, rfl⟩ := Finset.card_eq_one.mp hJ
  have hm0 : m = 0 := by omega
  subst hm0
  have hze := hineq {j} rfl hΔ
  rw [show N + 1 - 1 = N from by omega] at hze
  simp only [Nat.choose_one_right, Nat.cast_add, Nat.cast_one] at hze
  have hΔ1 := one_le_abs_minorJ hΔ
  have hcard1 : (1 : ℝ) ≤ (cardMod true M θ (Sq 0) : ℝ) := by
    have h := one_le_cardMod true M θ (Sq 0)
    exact_mod_cast h
  have hNpos : (0 : ℝ) < ((N).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_pos N
  have hD0pos : (0 : ℝ) < ((⌊δ 0⌋₊ : ℕ) : ℝ) := by
    have h : 1 ≤ ⌊δ 0⌋₊ := hδ1 0
    exact_mod_cast (by omega : (0 : ℕ) < ⌊δ 0⌋₊)
  have hPCpos : (0 : ℝ) < ∏ i ∈ ({j} : Finset (Fin N))ᶜ, ((⌊δ i.succ⌋₊ : ℕ) : ℝ) := by
    apply Finset.prod_pos
    intro i _
    have h : 1 ≤ ⌊δ i.succ⌋₊ := hδ1 i.succ
    exact_mod_cast (by omega : (0 : ℕ) < ⌊δ i.succ⌋₊)
  have hprod : ∏ i : Fin (N + 1), ((⌊δ i⌋₊ : ℕ) : ℝ) =
      ((⌊δ 0⌋₊ : ℕ) : ℝ) * (∏ i ∈ ({j} : Finset (Fin N)), ((⌊δ i.succ⌋₊ : ℕ) : ℝ)) *
        (∏ i ∈ ({j} : Finset (Fin N))ᶜ, ((⌊δ i.succ⌋₊ : ℕ) : ℝ)) := by
    rw [Fin.prod_univ_succ, prod_split (fun i : Fin N => ((⌊δ i.succ⌋₊ : ℕ) : ℝ)) {j}]
    ring
  have hfact : ((N + 1).factorial : ℝ) = ((N).factorial : ℝ) * ((N : ℝ) + 1) := by
    rw [Nat.factorial_succ]
    push_cast
    ring
  have hprod1 : (∏ i ∈ ({j} : Finset (Fin N)), ((⌊δ i.succ⌋₊ : ℕ) : ℝ)) =
      ((⌊δ j.succ⌋₊ : ℕ) : ℝ) :=
      Finset.prod_singleton (fun i : Fin N => ((⌊δ i.succ⌋₊ : ℕ) : ℝ)) j
  rw [hprod, hprod1, hfact] at hze
  -- hze : (Tq 0 + 1) * cardMod * N! * |Δ| * Dd0 * PC ≤ (N! * (N+1)) * (Dd0 * Dd_{j+1} * PC)
  have hdiv : (0 : ℝ) < (N.factorial : ℝ) * ((⌊δ 0⌋₊ : ℕ) : ℝ) *
      (∏ i ∈ ({j} : Finset (Fin N))ᶜ, ((⌊δ i.succ⌋₊ : ℕ) : ℝ)) := by
    refine mul_pos (mul_pos (by exact_mod_cast Nat.factorial_pos N) ?_) hPCpos
    exact_mod_cast (by have h := hδ1 0; omega : (0 : ℕ) < ⌊δ 0⌋₊)
  have hmul : (Tq 0 : ℝ) + 1 ≤ ((Tq 0 : ℝ) + 1) *
      (cardMod true M θ (Sq 0) : ℝ) * |(minorJ M {j} rfl : ℝ)| := by
    have hCM1 : (1 : ℝ) ≤ (cardMod true M θ (Sq 0) : ℝ) := hcard1
    have hmul1 : (Tq 0 : ℝ) + 1 ≤ ((Tq 0 : ℝ) + 1) * (cardMod true M θ (Sq 0) : ℝ) := by
      have h := mul_le_mul_of_nonneg_leftℝ hCM1
        (show (0 : ℝ) ≤ (Tq 0 : ℝ) + 1 by positivity)
      simpa using h
    have hmul2 : ((Tq 0 : ℝ) + 1) * (cardMod true M θ (Sq 0) : ℝ) ≤
        ((Tq 0 : ℝ) + 1) * (cardMod true M θ (Sq 0) : ℝ) * |(minorJ M {j} rfl : ℝ)| := by
      have h := mul_le_mul_of_nonneg_leftℝ hΔ1
        (show (0 : ℝ) ≤ ((Tq 0 : ℝ) + 1) * (cardMod true M θ (Sq 0) : ℝ) by positivity)
      simpa [mul_assoc] using h
    exact le_trans hmul1 hmul2
  have hbig : ((Tq 0 : ℝ) + 1) * ((N.factorial : ℝ) * ((⌊δ 0⌋₊ : ℕ) : ℝ) *
        (∏ i ∈ ({j} : Finset (Fin N))ᶜ, ((⌊δ i.succ⌋₊ : ℕ) : ℝ))) ≤
      (((Tq 0 : ℝ) + 1) * (cardMod true M θ (Sq 0) : ℝ) *
        |(minorJ M {j} rfl : ℝ)|) * ((N.factorial : ℝ) * ((⌊δ 0⌋₊ : ℕ) : ℝ) *
        (∏ i ∈ ({j} : Finset (Fin N))ᶜ, ((⌊δ i.succ⌋₊ : ℕ) : ℝ))) :=
    mul_le_mul_of_nonneg_rightℝ hmul (le_of_lt hdiv)
  have h1 : (Tq 0 : ℝ) + 1 ≤ ((N : ℝ) + 1) * ((⌊δ j.succ⌋₊ : ℕ) : ℝ) := by
    refine le_of_mul_le_mul_right ?_ hdiv
    refine le_trans hbig ?_
    calc ((Tq 0 : ℝ) + 1) * (cardMod true M θ (Sq 0) : ℝ) *
          |(minorJ M {j} rfl : ℝ)| * ((N.factorial : ℝ) * ((⌊δ 0⌋₊ : ℕ) : ℝ) *
          (∏ i ∈ ({j} : Finset (Fin N))ᶜ, ((⌊δ i.succ⌋₊ : ℕ) : ℝ)))
        = ((Tq 0 : ℝ) + 1) * (cardMod true M θ (Sq 0) : ℝ) *
            (N.factorial : ℝ) * |(minorJ M {j} rfl : ℝ)| * ((⌊δ 0⌋₊ : ℕ) : ℝ) *
            (∏ i ∈ ({j} : Finset (Fin N))ᶜ, ((⌊δ i.succ⌋₊ : ℕ) : ℝ)) := by ring
      _ ≤ (N.factorial : ℝ) * ((N : ℝ) + 1) *
            (((⌊δ 0⌋₊ : ℕ) : ℝ) * ((⌊δ j.succ⌋₊ : ℕ) : ℝ) *
              (∏ i ∈ ({j} : Finset (Fin N))ᶜ, ((⌊δ i.succ⌋₊ : ℕ) : ℝ))) := by
          simpa only [mul_assoc] using hze
      _ = (((N : ℝ) + 1) * ((⌊δ j.succ⌋₊ : ℕ) : ℝ)) *
            ((N.factorial : ℝ) * ((⌊δ 0⌋₊ : ℕ) : ℝ) *
              (∏ i ∈ ({j} : Finset (Fin N))ᶜ, ((⌊δ i.succ⌋₊ : ℕ) : ℝ))) := by ring
  have h2 : ((N : ℝ) + 1) * ((⌊δ j.succ⌋₊ : ℕ) : ℝ) ≤
      ((r : ℝ) + 1) * ((⌊δ j.succ⌋₊ : ℕ) : ℝ) :=
    mul_le_mul_of_nonneg_rightℝ (by exact_mod_cast (by omega : N + 1 ≤ r + 1)) (by positivity)
  have h3 : ((r : ℝ) + 1) * ((⌊δ j.succ⌋₊ : ℕ) : ℝ) ≤ ((r : ℝ) + 1) * δ j.succ :=
    mul_le_mul_of_nonneg_leftℝ (Nat.floor_le (hδnn j.succ)) (by positivity)
  linarith [h1, h2, h3, hE0 j]

end Work.BW
