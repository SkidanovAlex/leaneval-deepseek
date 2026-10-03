/-
# `Xsum_eq_sum_Xf` — the Möbius inversion of the `Π`-coprimality condition

The chain consumes the `Π`-free window sum `Xsum atilc x m t (2t)`, while the companion's
Proposition 4.1 is stated for the `Π`-restricted inner sum `Xf x Pz c u`
(`(n, Π) = 1`, i.e. `PiCond Pz n`).  This file proves the identity that removes the
restriction:

`Xsum atilc x m t (2t) = ∑_{b₁ | Π} μ(b₁) · Xf x Pz (m·b₁) (t/b₁)`.

Combinatorially, the right-hand side sums `μ(b₁)·μ(n)` over pairs `(b₁, n)` with `b₁ | Π`,
`(n, Π) = 1` and `b₁ n` in the window `(t, 2t]`, `m b₁ n ≤ x`.  Writing `b = b₁ n`, the map
`(b₁, n) ↦ b` is injective on this set, and it hits exactly the *squarefree* window elements;
the remaining window elements contribute `μ(b) = 0`.  On the image the product
`μ(b₁) μ(n) = μ(b)` by multiplicativity of `μ` on the coprime pair `b₁, n`.

All statements below are definitions-free (no `sorry`, no `axiom`).
-/
import Mathlib
import Submission.Work.FIChain.BpWinDefs

namespace Work.FIChain

open Finset ArithmeticFunction

set_option maxHeartbeats 1000000

noncomputable section

/-! ## 1. `PiCond` is coprimality with the primorial `Π = ∏_{p ≤ Pz} p` -/

/-- `PiCond Pz n` (no prime `q ≤ Pz` divides `n`) is exactly `n.Coprime (ProdP Pz)`. -/
private lemma nat_coprime_prodP_iff (Pz n : ℕ) :
    n.Coprime (ProdP Pz) ↔ Work.FITop4.PiCond Pz n := by
  rw [ProdP, primorial_eq_prod_primesLE, Nat.coprime_prod_right_iff]
  constructor
  · intro h q hq hqPz
    exact (Nat.Prime.coprime_iff_not_dvd hq).mp ((h q (Nat.mem_primesLE.mpr ⟨hqPz, hq⟩)).symm)
  · intro h q hq
    rw [Nat.mem_primesLE] at hq
    exact ((Nat.Prime.coprime_iff_not_dvd hq.2).mpr (h q hq.2 hq.1)).symm

/-- A divisor of the squarefree primorial is coprime to any `n` satisfying `PiCond Pz n`. -/
private lemma coprime_of_dvd_prodP_of_piCond {Pz a n : ℕ}
    (ha : a ∣ ProdP Pz) (hn : Work.FITop4.PiCond Pz n) : a.Coprime n :=
  (Nat.Coprime.coprime_dvd_right ha ((nat_coprime_prodP_iff Pz n).mpr hn)).symm

/-! ## 2. Basic facts about `μ` over the integers and over `ℝ` -/

/-- Multiplicativity of `μ`, cast to `ℝ`, for a coprime product. -/
private lemma moebius_mul_cast {a b : ℕ} (h : a.Coprime b) :
    (ArithmeticFunction.moebius (a * b) : ℝ)
      = (ArithmeticFunction.moebius a : ℝ) * (ArithmeticFunction.moebius b : ℝ) := by
  have hh : ArithmeticFunction.moebius (a * b)
      = ArithmeticFunction.moebius a * ArithmeticFunction.moebius b :=
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime h
  rw [hh]; push_cast; ring

/-! ## 3. The decomposition `b = b₁·n` with `b₁ | Π` and `(n, Π) = 1` -/

/-- **Uniqueness.**  For `Q` squarefree, the representation `b = a·n` with `a | Q` and
`(n, Q) = 1` is unique. -/
private lemma sqfree_decomp_unique {Q a₁ n₁ a₂ n₂ : ℕ} (hQ : Squarefree Q) (hQ0 : Q ≠ 0)
    (ha₁ : a₁ ∣ Q) (ha₂ : a₂ ∣ Q) (hn₁ : n₁.Coprime Q) (hn₂ : n₂.Coprime Q)
    (h : a₁ * n₁ = a₂ * n₂) : a₁ = a₂ ∧ n₁ = n₂ := by
  have key : ∀ {a a' n n' : ℕ}, Squarefree a → a ∣ Q → a' ∣ Q → n'.Coprime Q →
      a * n = a' * n' → a ∣ a' := by
    intro a a' n n' hasq ha ha' hn' heq
    have ha'sq : Squarefree a' := hQ.squarefree_of_dvd ha'
    have ha'0 : a' ≠ 0 := ne_of_gt (Nat.pos_of_dvd_of_pos ha' (Nat.pos_of_ne_zero hQ0))
    rw [← Nat.prod_primeFactors_of_squarefree hasq,
        ← Nat.prod_primeFactors_of_squarefree ha'sq]
    refine Finset.prod_dvd_prod_of_subset _ _ id (fun p hp => ?_)
    rw [Nat.mem_primeFactors] at hp ⊢
    obtain ⟨hpp, hpa, _⟩ := hp
    refine ⟨hpp, ?_, ha'0⟩
    have hpQ : p ∣ Q := dvd_trans hpa ha
    have hdiv : p ∣ a' * n' := heq ▸ dvd_mul_of_dvd_left hpa n
    rcases hpp.dvd_mul.mp hdiv with h2 | h2
    · exact h2
    · exfalso
      have hg : n'.gcd Q = 1 := hn'
      have : p ∣ 1 := by
        have h3 : p ∣ n'.gcd Q := Nat.dvd_gcd h2 hpQ
        rwa [hg] at h3
      exact hpp.ne_one (Nat.eq_one_of_dvd_one this)
  have hdvd : a₁ ∣ a₂ := key (hQ.squarefree_of_dvd ha₁) ha₁ ha₂ hn₂ h
  have hdvd' : a₂ ∣ a₁ := key (hQ.squarefree_of_dvd ha₂) ha₂ ha₁ hn₁ h.symm
  have h12 : a₁ = a₂ := Nat.dvd_antisymm hdvd hdvd'
  refine ⟨h12, ?_⟩
  have ha₁pos : 0 < a₁ := Nat.pos_of_dvd_of_pos ha₁ (Nat.pos_of_ne_zero hQ0)
  rw [← h12] at h
  exact Nat.mul_left_cancel ha₁pos h

/-- **Existence.**  A squarefree `b` admits a representation `b = a·n` with `a | Q` and
`(n, Q) = 1` (here `a = b.gcd Q`, `n = b / (b.gcd Q)`). -/
private lemma exists_sqfree_decomp {Q b : ℕ} (hb : Squarefree b) (hQ0 : Q ≠ 0) :
    ∃ a n : ℕ, a ∣ Q ∧ b = a * n ∧ n.Coprime Q :=
  ⟨b.gcd Q, b / b.gcd Q, Nat.gcd_dvd_right _ _,
    (Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)).symm,
    Nat.coprime_div_gcd_of_squarefree hb hQ0⟩

/-! ## 4. The main identity -/

theorem Xsum_eq_sum_Xf (x Pz m : ℕ) (hm : 1 ≤ m) (t : ℝ) :
    Submission.ASP.Xsum Work.FIChain.atilc x m t (2 * t)
      = ∑ b₁ ∈ (Work.FIChain.ProdP Pz).divisors,
          (ArithmeticFunction.moebius b₁ : ℝ) * Work.FIChain.Xf x Pz (m * b₁) (t / b₁) := by
  classical
  set W : Finset ℕ := (Finset.Icc 1 x).filter
      (fun b => t < (b:ℝ) ∧ (b:ℝ) ≤ 2 * t ∧ b * m ≤ x) with hW
  set Sf : ℕ → Finset ℕ := fun b₁ => (Finset.Icc 1 x).filter
      (fun n => (m * b₁) * n ≤ x ∧ t / b₁ < (n:ℝ) ∧ (n:ℝ) ≤ 2 * (t / b₁)
        ∧ Work.FITop4.PiCond Pz n) with hSf
  set T : Finset (Σ _ : ℕ, ℕ) := (ProdP Pz).divisors.sigma Sf with hT
  have hSfeq : ∀ b₁, Sf b₁ = (Finset.Icc 1 x).filter
      (fun n => (m * b₁) * n ≤ x ∧ t / b₁ < (n:ℝ) ∧ (n:ℝ) ≤ 2 * (t / b₁)
        ∧ Work.FITop4.PiCond Pz n) := fun b₁ => by rw [hSf]
  have mem_Sf : ∀ b₁ n, n ∈ Sf b₁ ↔
      (n ∈ Finset.Icc 1 x ∧ (m * b₁) * n ≤ x ∧ t / b₁ < (n:ℝ)
        ∧ (n:ℝ) ≤ 2 * (t / b₁) ∧ Work.FITop4.PiCond Pz n) := by
    intro b₁ n; rw [hSfeq b₁, Finset.mem_filter]
  have mem_W : ∀ b, b ∈ W ↔
      (b ∈ Finset.Icc 1 x ∧ t < (b:ℝ) ∧ (b:ℝ) ≤ 2 * t ∧ b * m ≤ x) := by
    intro b; rw [hW, Finset.mem_filter]
  have mem_T : ∀ p : Σ _ : ℕ, ℕ, p ∈ T ↔ (p.1 ∈ (ProdP Pz).divisors ∧ p.2 ∈ Sf p.1) := by
    intro p; rw [hT, Finset.mem_sigma]
  -- The left-hand side is the window sum, with `b*m` rewritten to `m*b`.
  have hL : Submission.ASP.Xsum atilc x m t (2 * t)
      = ∑ b ∈ W, (ArithmeticFunction.moebius b : ℝ) * atilc (m * b) := by
    rw [Submission.ASP.Xsum, ← hW]
    apply Finset.sum_congr rfl
    intro b _
    rw [mul_comm b m]
  -- The right-hand side expands into a sum over the `sigma`-set `T`.
  have hR : (∑ b₁ ∈ (ProdP Pz).divisors,
        (ArithmeticFunction.moebius b₁ : ℝ) * Xf x Pz (m * b₁) (t / b₁))
      = ∑ p ∈ T, (ArithmeticFunction.moebius p.1 : ℝ)
          * ((ArithmeticFunction.moebius p.2 : ℝ) * atilc ((m * p.1) * p.2)) := by
    rw [hT, Finset.sum_sigma]
    apply Finset.sum_congr rfl
    intro b₁ _
    rw [Xf, ← hSfeq b₁, Finset.mul_sum]
  -- On `T` the product `μ(p.1)·μ(p.2)` is `μ(p.1·p.2)`.
  have hTterm : ∑ p ∈ T, (ArithmeticFunction.moebius p.1 : ℝ)
          * ((ArithmeticFunction.moebius p.2 : ℝ) * atilc ((m * p.1) * p.2))
      = ∑ p ∈ T, (ArithmeticFunction.moebius (p.1 * p.2) : ℝ) * atilc (m * (p.1 * p.2)) := by
    apply Finset.sum_congr rfl
    intro p hp
    rw [mem_T] at hp
    obtain ⟨hp1, hp2⟩ := hp
    have hp1d : p.1 ∣ ProdP Pz := (Nat.mem_divisors.mp hp1).1
    obtain ⟨-, -, -, -, hpi⟩ := (mem_Sf p.1 p.2).mp hp2
    have hcop : p.1.Coprime p.2 := coprime_of_dvd_prodP_of_piCond hp1d hpi
    have harg : (m * p.1) * p.2 = m * (p.1 * p.2) := mul_assoc m p.1 p.2
    rw [harg, moebius_mul_cast hcop, mul_assoc]
  -- `(b₁, n) ↦ b₁·n` is injective on `T`.
  have hInj : Set.InjOn (fun p : Σ _ : ℕ, ℕ => p.1 * p.2) ↑T := by
    rintro ⟨p1, p2⟩ hp ⟨q1, q2⟩ hq heq
    rw [Finset.mem_coe, mem_T] at hp hq
    simp only at heq
    have hp1d : p1 ∣ ProdP Pz := (Nat.mem_divisors.mp hp.1).1
    have hq1d : q1 ∣ ProdP Pz := (Nat.mem_divisors.mp hq.1).1
    obtain ⟨-, -, -, -, hpi⟩ := (mem_Sf p1 p2).mp hp.2
    obtain ⟨-, -, -, -, hqi⟩ := (mem_Sf q1 q2).mp hq.2
    have hp2c : p2.Coprime (ProdP Pz) := (nat_coprime_prodP_iff Pz p2).mpr hpi
    have hq2c : q2.Coprime (ProdP Pz) := (nat_coprime_prodP_iff Pz q2).mpr hqi
    have hdec := sqfree_decomp_unique (ProdP_squarefree Pz) (ProdP_pos Pz).ne'
      hp1d hq1d hp2c hq2c heq
    obtain ⟨h1, h2⟩ := hdec
    subst h1; subst h2; rfl
  -- The image of `T` lies in the window.
  have himage_sub : T.image (fun p : Σ _ : ℕ, ℕ => p.1 * p.2) ⊆ W := by
    intro b hb
    rw [Finset.mem_image] at hb
    obtain ⟨p, hp, rfl⟩ := hb
    rw [mem_W]
    rw [mem_T] at hp
    obtain ⟨hp1, hp2⟩ := hp
    have hp1d : p.1 ∣ ProdP Pz := (Nat.mem_divisors.mp hp1).1
    have hp1pos : 0 < p.1 := Nat.pos_of_dvd_of_pos hp1d (ProdP_pos Pz)
    have hp1R : (0:ℝ) < (p.1:ℝ) := by exact_mod_cast hp1pos
    obtain ⟨hnI, hle1, hlt, hle2, hpi⟩ := (mem_Sf p.1 p.2).mp hp2
    obtain ⟨hn1, hnx⟩ := Finset.mem_Icc.mp hnI
    refine ⟨Finset.mem_Icc.mpr ⟨?_, ?_⟩, ?_, ?_, ?_⟩
    · exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
    · calc p.1 * p.2 ≤ (m * p.1) * p.2 := Nat.mul_le_mul_right p.2 (by
              calc p.1 = 1 * p.1 := (one_mul p.1).symm
                _ ≤ m * p.1 := Nat.mul_le_mul_right p.1 hm)
        _ ≤ x := hle1
    · have hd := (div_lt_iff₀ hp1R).mp hlt
      calc t < (p.2:ℝ) * (p.1:ℝ) := hd
        _ = ((p.1 * p.2 : ℕ) : ℝ) := by push_cast; ring
    · have hd : (p.2:ℝ) ≤ (2 * t) / (p.1:ℝ) := by rw [mul_div_assoc]; exact hle2
      have hd2 := (le_div_iff₀ hp1R).mp hd
      calc ((p.1 * p.2 : ℕ) : ℝ) = (p.2:ℝ) * (p.1:ℝ) := by push_cast; ring
        _ ≤ 2 * t := hd2
    · have : (p.1 * p.2) * m = (m * p.1) * p.2 := by ring
      rw [this]; exact hle1
  -- Off the image, `μ b = 0`.
  have hzero : ∀ b ∈ W, b ∉ T.image (fun p : Σ _ : ℕ, ℕ => p.1 * p.2) →
      (ArithmeticFunction.moebius b : ℝ) * atilc (m * b) = 0 := by
    intro b hbW hbnot
    have hμ : (ArithmeticFunction.moebius b : ℝ) = 0 := by
      have hnsq : ¬ Squarefree b := by
        intro hbsq
        apply hbnot
        obtain ⟨hbIcc, hbt, hb2t, hbm⟩ := (mem_W b).mp hbW
        obtain ⟨hb1, hbx⟩ := Finset.mem_Icc.mp hbIcc
        obtain ⟨a, n, hadvd, hbeq, hnco⟩ := exists_sqfree_decomp hbsq (ProdP_pos Pz).ne'
        have hapos : 0 < a := Nat.pos_of_dvd_of_pos hadvd (ProdP_pos Pz)
        have haR : (0:ℝ) < (a:ℝ) := by exact_mod_cast hapos
        have han : (b:ℝ) = (a:ℝ) * (n:ℝ) := by rw [hbeq]; push_cast; ring
        have hn1 : 1 ≤ n := by
          rcases Nat.eq_zero_or_pos n with h | h
          · exfalso; rw [h, mul_zero] at hbeq; omega
          · omega
        have hnx : n ≤ x := by
          have h1 : n ≤ a * n := Nat.le_mul_of_pos_left n hapos
          rw [← hbeq] at h1
          exact le_trans h1 hbx
        have hmn : (m * a) * n ≤ x := by
          have : (m * a) * n = b * m := by rw [hbeq]; ring
          rw [this]; exact hbm
        have ht' : t / (a:ℝ) < (n:ℝ) := by
          rw [div_lt_iff₀ haR]
          calc t < (b:ℝ) := hbt
            _ = (n:ℝ) * (a:ℝ) := by rw [han]; ring
        have hn2t : (n:ℝ) ≤ 2 * (t / (a:ℝ)) := by
          rw [← mul_div_assoc, le_div_iff₀ haR]
          calc (n:ℝ) * (a:ℝ) = (b:ℝ) := by rw [han]; ring
            _ ≤ 2 * t := hb2t
        have hmem : (⟨a, n⟩ : Σ _ : ℕ, ℕ) ∈ T := by
          rw [mem_T]
          exact ⟨Nat.mem_divisors.mpr ⟨hadvd, (ProdP_pos Pz).ne'⟩,
            (mem_Sf a n).mpr ⟨Finset.mem_Icc.mpr ⟨hn1, hnx⟩, hmn, ht', hn2t,
              (nat_coprime_prodP_iff Pz n).mp hnco⟩⟩
        exact Finset.mem_image.mpr ⟨⟨a, n⟩, hmem, hbeq.symm⟩
      have : ArithmeticFunction.moebius b = 0 :=
        ArithmeticFunction.moebius_eq_zero_of_not_squarefree hnsq
      rw [this]; simp
    rw [hμ, zero_mul]
  have hkey : ∑ p ∈ T, (ArithmeticFunction.moebius (p.1 * p.2) : ℝ) * atilc (m * (p.1 * p.2))
      = ∑ b ∈ W, (ArithmeticFunction.moebius b : ℝ) * atilc (m * b) := by
    rw [← Finset.sum_image (s := T) (f := fun b => (ArithmeticFunction.moebius b : ℝ) * atilc (m * b))
      (g := fun p : Σ _ : ℕ, ℕ => p.1 * p.2) hInj]
    exact Finset.sum_subset himage_sub hzero
  rw [hL, hR, hTterm, hkey]

end

end Work.FIChain
