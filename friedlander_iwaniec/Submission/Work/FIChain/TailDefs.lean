/-
# `Submission.Work.FIChain.TailDefs` — vocabulary for the `(B′)`-window tail estimate

The tail `b₁ > Δπ` of the `Π`-removal of the companion paper's §10 (Theorem 3, estimate (10.4)
`W₁`) is estimated by Rankin's trick: every divisor `b₁ ∣ Π` with `b₁ > Δπ` has a divisor
`d ∣ b₁` with `Δπ < d ≤ Δπ·Pz` (`Work.FIChain.exists_dvd_ProdP_between`), and the `1/d`-saving
of the congruence sums then produces the factor `(log x)^{-κ}`.

This file defines the index set `Dsp` of those small divisors, and nothing else
(no `sorry`, no `axiom`).
-/
import Mathlib
import Submission.Work.FIChain.BpWinDefs

set_option autoImplicit false

namespace Work.FIChain

open Finset

attribute [local instance] Classical.propDecidable

noncomputable section

/-- The index set of the Rankin step: the divisors `d` of `Π(Pz)` with `D < d ≤ D·Pz`. -/
def Dsp (Pz D : ℕ) : Finset ℕ := ((ProdP Pz).divisors).filter (fun d => D < d ∧ d ≤ D * Pz)

lemma mem_Dsp {Pz D d : ℕ} :
    d ∈ Dsp Pz D ↔ d ∣ ProdP Pz ∧ D < d ∧ d ≤ D * Pz := by
  rw [Dsp, Finset.mem_filter, Nat.mem_divisors]
  constructor
  · rintro ⟨⟨hdvd, _⟩, h1, h2⟩; exact ⟨hdvd, h1, h2⟩
  · rintro ⟨hdvd, h1, h2⟩
    exact ⟨⟨hdvd, (ProdP_squarefree Pz).ne_zero⟩, h1, h2⟩

lemma Dsp_subset_divisors (Pz D : ℕ) : Dsp Pz D ⊆ (ProdP Pz).divisors :=
  fun _ hd => Nat.mem_divisors.mpr ⟨(mem_Dsp.mp hd).1, (ProdP_squarefree Pz).ne_zero⟩

lemma Dsp_pos {Pz D d : ℕ} (hd : d ∈ Dsp Pz D) : 0 < d :=
  lt_of_le_of_lt (Nat.zero_le D) (mem_Dsp.mp hd).2.1

/-! ## 2. Uniqueness of the `(b₁, n)` decomposition

The reindexing `(b₁, n) ↦ b₁ · n` of the `Π`-restricted tail is injective: for `b₁ ∣ Π` and
`(n, Π) = 1` the divisor `b₁` is exactly the `Π`-part of the product, hence determined by it.
-/

/-- For `b ∣ Π(Pz)` and `(n, Π) = 1` the `Π`-part of `b·n` is `b`: `gcd (b·n) Π = b`. -/
lemma gcd_mul_ProdP (Pz b n : ℕ) (hb : b ∣ ProdP Pz) (hn : Work.FITop4.PiCond Pz n) :
    Nat.gcd (b * n) (ProdP Pz) = b := by
  obtain ⟨M, hM⟩ := hb
  have hMeq : ProdP Pz = b * M := hM
  have hMnz : M ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hMeq
    exact (ProdP_squarefree Pz).ne_zero hMeq
  have hone : Nat.gcd n M = 1 := by
    by_contra h
    have hgnz : Nat.gcd n M ≠ 0 := fun h0 =>
      hMnz (Nat.eq_zero_of_zero_dvd (h0 ▸ Nat.gcd_dvd_right n M))
    have hpos : 0 < Nat.gcd n M := Nat.pos_of_ne_zero hgnz
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd (by omega : Nat.gcd n M ≠ 1)
    have hpn : p ∣ n := dvd_trans hpd (Nat.gcd_dvd_left n M)
    have hpM : p ∣ M := dvd_trans hpd (Nat.gcd_dvd_right n M)
    have hpP : p ∣ ProdP Pz := by rw [hMeq]; exact dvd_mul_of_dvd_right hpM b
    exact hn p hp ((hp.dvd_primorial_iff).mp hpP) hpn
  rw [hMeq, Nat.gcd_mul_left, hone, mul_one]

/-- **Injectivity of `(b₁, n) ↦ b₁ · n`** on the tail index set: if `b₁, b₁' ∣ Π(Pz)` and
`(n, Π) = (n', Π) = 1` with `b₁ n = b₁' n'` then `b₁ = b₁'` and `n = n'`. -/
lemma mul_inj_ProdP {Pz b₁ b₁' n n' : ℕ} (hb : b₁ ∣ ProdP Pz) (hb' : b₁' ∣ ProdP Pz)
    (hn : Work.FITop4.PiCond Pz n) (hn' : Work.FITop4.PiCond Pz n')
    (h : b₁ * n = b₁' * n') : b₁ = b₁' ∧ n = n' := by
  have hb0 : b₁ ≠ 0 := by
    intro h0
    have hz : ProdP Pz = 0 := by
      rw [h0] at hb
      exact Nat.eq_zero_of_zero_dvd hb
    exact (ProdP_squarefree Pz).ne_zero hz
  have h1 : b₁ = b₁' := by
    rw [← gcd_mul_ProdP Pz b₁ n hb hn, h, gcd_mul_ProdP Pz b₁' n' hb' hn']
  subst h1
  exact ⟨rfl, Nat.mul_left_cancel (Nat.pos_of_ne_zero hb0) h⟩


end

end Work.FIChain
