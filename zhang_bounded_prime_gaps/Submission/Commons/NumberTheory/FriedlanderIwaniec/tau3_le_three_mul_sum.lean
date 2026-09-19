import Mathlib

set_option linter.unusedVariables false

namespace Commons.NumberTheory.FriedlanderIwaniec

private abbrev Trip : Type := Sigma (fun _ : ℕ => ℕ × ℕ)

/-- `R n` is the finset of "triples" `⟨a, ⟨b, c⟩⟩` with `a ∣ n` and `b * c = n / a`.
Equivalently (for `n ≠ 0`) it is the set of triples of positive integers with product `n`. -/
private def R (n : ℕ) : Finset Trip :=
  n.divisors.sigma (fun a => (n / a).divisorsAntidiagonal)

private lemma mem_R {n : ℕ} {x : Trip} :
    x ∈ R n ↔ x.1 ∈ n.divisors ∧ x.2 ∈ (n / x.1).divisorsAntidiagonal := by
  rw [R, Finset.mem_sigma]

private lemma fst_dvd_of_mem_R {n : ℕ} {x : Trip} (hx : x ∈ R n) : x.1 ∣ n :=
  (Nat.mem_divisors.mp (mem_R.mp hx).1).1

private lemma snd_mul_of_mem_R {n : ℕ} {x : Trip} (hx : x ∈ R n) :
    x.2.1 * x.2.2 = n / x.1 :=
  (Nat.mem_divisorsAntidiagonal.mp (mem_R.mp hx).2).1

private lemma prod_of_mem_R {n : ℕ} {x : Trip} (hx : x ∈ R n) :
    x.1 * x.2.1 * x.2.2 = n := by
  calc x.1 * x.2.1 * x.2.2 = x.1 * (x.2.1 * x.2.2) := by ring
    _ = x.1 * (n / x.1) := by rw [snd_mul_of_mem_R hx]
    _ = n := Nat.mul_div_cancel' (fst_dvd_of_mem_R hx)

private def rot (x : Trip) : Trip := ⟨x.2.1, (x.2.2, x.1)⟩
private def rot2 (x : Trip) : Trip := ⟨x.2.2, (x.1, x.2.1)⟩

private lemma rot_rot2 (x : Trip) : rot (rot2 x) = x := by
  simp [rot, rot2]

private lemma rot2_rot (x : Trip) : rot2 (rot x) = x := by
  simp [rot, rot2]

private lemma rot_mem {n : ℕ} {x : Trip} (hx : x ∈ R n) : rot x ∈ R n := by
  obtain ⟨h1, h2⟩ := mem_R.mp hx
  obtain ⟨hdvd, hn0⟩ := Nat.mem_divisors.mp h1
  obtain ⟨hprod, hne⟩ := Nat.mem_divisorsAntidiagonal.mp h2
  have hx1pos : 0 < x.1 := Nat.pos_of_dvd_of_pos hdvd (Nat.pos_of_ne_zero hn0)
  have h21ne : x.2.1 ≠ 0 := by
    rintro hc; rw [hc, zero_mul] at hprod; exact hne hprod.symm
  have h22ne : x.2.2 ≠ 0 := by
    rintro hc; rw [hc, mul_zero] at hprod; exact hne hprod.symm
  have hN : n = x.2.1 * (x.1 * x.2.2) := by
    calc n = x.1 * (n / x.1) := (Nat.mul_div_cancel' hdvd).symm
      _ = x.1 * (x.2.1 * x.2.2) := by rw [hprod]
      _ = x.2.1 * (x.1 * x.2.2) := by ring
  rw [mem_R]
  constructor
  · rw [Nat.mem_divisors]
    exact ⟨dvd_trans (show x.2.1 ∣ n / x.1 from ⟨x.2.2, hprod.symm⟩) (Nat.div_dvd_of_dvd hdvd),
      hn0⟩
  · rw [Nat.mem_divisorsAntidiagonal]
    change x.2.2 * x.1 = n / x.2.1 ∧ n / x.2.1 ≠ 0
    constructor
    · rw [hN, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero h21ne)]
      ring
    · rw [hN, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero h21ne)]
      exact mul_ne_zero hx1pos.ne' h22ne

private lemma rot2_mem {n : ℕ} {x : Trip} (hx : x ∈ R n) : rot2 x ∈ R n := by
  rw [show rot2 x = rot (rot x) from by simp [rot, rot2]]
  exact rot_mem (rot_mem hx)

private def R0 (n : ℕ) : Finset Trip := (R n).filter (fun x => x.1^3 ≤ n)
private def R1 (n : ℕ) : Finset Trip := (R n).filter (fun x => x.2.1^3 ≤ n)
private def R2 (n : ℕ) : Finset Trip := (R n).filter (fun x => x.2.2^3 ≤ n)

private lemma mem_R0 {n : ℕ} {x : Trip} : x ∈ R0 n ↔ x ∈ R n ∧ x.1^3 ≤ n := by
  simp [R0]

private lemma mem_R1 {n : ℕ} {x : Trip} : x ∈ R1 n ↔ x ∈ R n ∧ x.2.1^3 ≤ n := by
  simp [R1]

private lemma mem_R2 {n : ℕ} {x : Trip} : x ∈ R2 n ↔ x ∈ R n ∧ x.2.2^3 ≤ n := by
  simp [R2]

private lemma rot_R1_R0 {n : ℕ} {x : Trip} (hx : x ∈ R1 n) : rot x ∈ R0 n := by
  rw [mem_R1] at hx
  rw [mem_R0]
  exact ⟨rot_mem hx.1, hx.2⟩

private lemma rot2_R0_R1 {n : ℕ} {x : Trip} (hx : x ∈ R0 n) : rot2 x ∈ R1 n := by
  rw [mem_R0] at hx
  rw [mem_R1]
  exact ⟨rot2_mem hx.1, hx.2⟩

private lemma rot_R2_R1 {n : ℕ} {x : Trip} (hx : x ∈ R2 n) : rot x ∈ R1 n := by
  rw [mem_R2] at hx
  rw [mem_R1]
  exact ⟨rot_mem hx.1, hx.2⟩

private lemma rot2_R1_R2 {n : ℕ} {x : Trip} (hx : x ∈ R1 n) : rot2 x ∈ R2 n := by
  rw [mem_R1] at hx
  rw [mem_R2]
  exact ⟨rot2_mem hx.1, hx.2⟩

private lemma rot_R0_R2 {n : ℕ} {x : Trip} (hx : x ∈ R0 n) : rot x ∈ R2 n := by
  rw [mem_R0] at hx
  rw [mem_R2]
  exact ⟨rot_mem hx.1, hx.2⟩

private lemma rot2_R2_R0 {n : ℕ} {x : Trip} (hx : x ∈ R2 n) : rot2 x ∈ R0 n := by
  rw [mem_R2] at hx
  rw [mem_R0]
  exact ⟨rot2_mem hx.1, hx.2⟩

private lemma cube_le_of_mul_eq {a b c n : ℕ} (h : a * b * c = n) :
    a^3 ≤ n ∨ b^3 ≤ n ∨ c^3 ≤ n := by
  by_contra hcon
  simp only [not_or, not_le] at hcon
  obtain ⟨ha, hb, hc⟩ := hcon
  have h1 : n * n < a^3 * b^3 := mul_lt_mul'' ha hb (Nat.zero_le _) (Nat.zero_le _)
  have h2 : n * n * n < a^3 * b^3 * c^3 := mul_lt_mul'' h1 hc (Nat.zero_le _) (Nat.zero_le _)
  have hpc : a^3 * b^3 * c^3 = (a * b * c)^3 := by ring
  rw [hpc, h, show n * n * n = n^3 from by ring] at h2
  exact absurd h2 (lt_irrefl _)

private lemma R_subset_union (n : ℕ) : R n ⊆ R0 n ∪ R1 n ∪ R2 n := by
  intro x hx
  have hcases := cube_le_of_mul_eq (prod_of_mem_R hx)
  rcases hcases with h0 | h1 | h2
  · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl (mem_R0.mpr ⟨hx, h0⟩))))
  · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr (mem_R1.mpr ⟨hx, h1⟩))))
  · exact Finset.mem_union.mpr (Or.inr (mem_R2.mpr ⟨hx, h2⟩))

private lemma card_divisorsAntidiagonal (m : ℕ) :
    (m.divisorsAntidiagonal).card = m.divisors.card := by
  have h := Nat.sum_divisorsAntidiagonal (fun _ _ => (1 : ℕ)) (n := m)
  simpa using h

private lemma card_R (n : ℕ) : (R n).card = ∑ d ∈ n.divisors, d.divisors.card := by
  rw [R, Finset.card_sigma]
  calc ∑ a ∈ n.divisors, ((n / a).divisorsAntidiagonal).card
      = ∑ a ∈ n.divisors, (n / a).divisors.card :=
        Finset.sum_congr rfl (fun a _ => card_divisorsAntidiagonal (n / a))
    _ = ∑ d ∈ n.divisors, d.divisors.card := Nat.sum_div_divisors n (fun d => d.divisors.card)

private lemma card_R0 (n : ℕ) :
    (R0 n).card = ∑ d ∈ n.divisors.filter (fun d => d^3 ≤ n), (n / d).divisors.card := by
  have hR0 : R0 n
      = (n.divisors.filter (fun d => d^3 ≤ n)).sigma (fun a => (n / a).divisorsAntidiagonal) := by
    ext x
    simp only [mem_R0, mem_R, Finset.mem_sigma, Finset.mem_filter]
    tauto
  rw [hR0, Finset.card_sigma]
  apply Finset.sum_congr rfl
  intro d _
  exact card_divisorsAntidiagonal (n / d)

private lemma card_R1 (n : ℕ) : (R1 n).card = (R0 n).card :=
  Finset.card_nbij' rot rot2 (fun _ hx => rot_R1_R0 hx) (fun _ hx => rot2_R0_R1 hx)
    (fun x _ => rot2_rot x) (fun x _ => rot_rot2 x)

private lemma card_R2 (n : ℕ) : (R2 n).card = (R0 n).card :=
  Finset.card_nbij' rot2 rot (fun _ hx => rot2_R2_R0 hx) (fun _ hx => rot_R0_R2 hx)
    (fun x _ => rot_rot2 x) (fun x _ => rot2_rot x)

private lemma card_le_three_mul (n : ℕ) : (R n).card ≤ 3 * (R0 n).card := by
  calc (R n).card
      ≤ (R0 n ∪ R1 n ∪ R2 n).card := Finset.card_le_card (R_subset_union n)
    _ ≤ (R0 n ∪ R1 n).card + (R2 n).card := Finset.card_union_le _ _
    _ ≤ ((R0 n).card + (R1 n).card) + (R2 n).card :=
        Nat.add_le_add_right (Finset.card_union_le _ _) _
    _ = 3 * (R0 n).card := by rw [card_R1 n, card_R2 n]; ring

theorem tau3_le_three_mul_sum {n : ℕ} (hn : 1 ≤ n) :
    ∑ d ∈ n.divisors, d.divisors.card ≤
      3 * ∑ d ∈ (n.divisors.filter fun d => d^3 ≤ n), (n / d).divisors.card := by
  calc ∑ d ∈ n.divisors, d.divisors.card
      = (R n).card := (card_R n).symm
    _ ≤ 3 * (R0 n).card := card_le_three_mul n
    _ = 3 * ∑ d ∈ n.divisors.filter (fun d => d^3 ≤ n), (n / d).divisors.card := by
        rw [card_R0 n]

end Commons.NumberTheory.FriedlanderIwaniec
