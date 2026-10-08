import Mathlib
import Submission.Work.BSLit.BenderFacts2.Facts2SzDefs
import Submission.Work.Models.Port.Sz.Borel
import Submission.Work.Models.Port.Sz.SuzukiCondition
import Submission.Work.Models.Port.Commons.GroupTheory.StronglyEmbedded.centralizer_eq_left_of_isStronglyEmbedded
import Submission.Work.Models.Port.Commons.Nat.coprime_one_add_two_pow_succ

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option maxHeartbeats 1600000

namespace Work.BSLit.BenderFacts2

open LeanEval.GroupTheory.Defs

/-! ## Two elementary inputs

The centralizer of an involution `u(0,c)` (`c ≠ 0`) of the Suzuki group `Sz(2^(2n+1))` is the
Suzuki `2`-group `U`.  The two model-specific facts that go into this are

* `u(0,c)` is central in `U` (`szUg_zero_mul_comm`), and
* the only torus element fixing `u(0,c)` is the identity
  (`szTS_eq_one_of_mem_centralizer_szUgS_zero`), a consequence of the conjugation formula
  `t(x)·u(0,c)·t(x)⁻¹ = u(0, x^(2^(n+1)+1)·c)` and the coprimality of `2^(n+1)+1` with
  `2^(2n+1) - 1 = |Fˣ|`.

Everything else is the general strongly-embedded argument
`centralizer_eq_left_of_isStronglyEmbedded`. -/

/-- `u(0,c)` is central in the Suzuki `2`-group. -/
lemma szUg_zero_mul_comm (n : ℕ) (c a b : Submission.Sz.SzField n) :
    Submission.Sz.szUg n 0 c * Submission.Sz.szUg n a b =
      Submission.Sz.szUg n a b * Submission.Sz.szUg n 0 c := by
  rw [Submission.Sz.szUg_mul, Submission.Sz.szUg_mul]
  congr 1
  · rw [zero_add, add_zero]
  · simp only [zero_mul, zero_pow (by positivity : 2 ^ (n + 1) ≠ 0), mul_zero, add_zero]
    exact add_comm c b

/-- The only element `x` of `Fˣ` with `x ^ (2^(n+1) + 1) = 1` is `1`: the exponent is coprime
to `|Fˣ| = 2^(2n+1) - 1`. -/
lemma szTg_pow_eq_one_iff (n : ℕ) (x : (Submission.Sz.SzField n)ˣ) :
    (x : Submission.Sz.SzField n) ^ (1 + 2 ^ (n + 1)) = 1 ↔ x = 1 := by
  constructor
  · intro hx
    have h4 : x ^ (1 + 2 ^ (n + 1)) = 1 := by
      apply Units.ext
      simpa using hx
    have h5 : orderOf x ∣ 1 + 2 ^ (n + 1) := orderOf_dvd_iff_pow_eq_one.mpr h4
    have h6 : orderOf x ∣ Nat.card (Submission.Sz.SzField n)ˣ := orderOf_dvd_natCard x
    have h7 : Nat.Coprime (1 + 2 ^ (n + 1)) (Nat.card (Submission.Sz.SzField n)ˣ) := by
      rw [Nat.card_units, Submission.Sz.card_szField]
      exact Commons.Nat.coprime_one_add_two_pow_succ n
    have h8 : orderOf x ∣ Nat.gcd (1 + 2 ^ (n + 1))
        (Nat.card (Submission.Sz.SzField n)ˣ) := Nat.dvd_gcd h5 h6
    rw [h7.gcd_eq_one] at h8
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h8)
  · rintro rfl
    simp

/-- A torus element `t` commuting with the involution `u(0,c)` (`c ≠ 0`) is trivial: write
`t = t(x)`, conjugate `u(0,c)` by `t(x)` and cancel `c`. -/
lemma szTS_eq_one_of_mem_centralizer_szUgS_zero (n : ℕ)
    {c : Submission.Sz.SzField n} (hc : c ≠ 0) {t : SzModel n}
    (ht : t ∈ Submission.Sz.szTS n)
    (hcomm : t ∈ Subgroup.centralizer ({szUgS n 0 c} : Set (SzModel n))) : t = 1 := by
  obtain ⟨x, hx⟩ := Subgroup.mem_subgroupOf.mp ht
  have hcomm' : (t : GL (Fin 4) (Submission.Sz.SzField n)) * Submission.Sz.szUg n 0 c =
      Submission.Sz.szUg n 0 c * (t : GL (Fin 4) (Submission.Sz.SzField n)) := by
    have h := (Subgroup.mem_centralizer_singleton_iff.mp hcomm)
    have h' := congrArg (fun z : SzModel n => (z : GL (Fin 4) (Submission.Sz.SzField n))) h
    simpa [szUgS_coe] using h'
  have htgl : (t : GL (Fin 4) (Submission.Sz.SzField n)) = Submission.Sz.szTg n x := by
    rw [← hx]; rfl
  have hconj : Submission.Sz.szTg n x * Submission.Sz.szUg n 0 c *
      (Submission.Sz.szTg n x)⁻¹ = Submission.Sz.szUg n 0 c := by
    have h2 := hcomm'
    rw [htgl] at h2
    rw [h2, mul_assoc, mul_inv_cancel, mul_one]
  rw [Submission.Sz.szTg_conj_szUg, mul_zero] at hconj
  have h1 : ((0 : Submission.Sz.SzField n),
      (x : Submission.Sz.SzField n) ^ (1 + 2 ^ (n + 1)) * c) =
      ((0 : Submission.Sz.SzField n), c) := Submission.Sz.szUg_injective n hconj
  have h2 : (x : Submission.Sz.SzField n) ^ (1 + 2 ^ (n + 1)) * c = c := (Prod.ext_iff.mp h1).2
  have h3 : (x : Submission.Sz.SzField n) ^ (1 + 2 ^ (n + 1)) = 1 :=
    mul_right_cancel₀ hc (by rw [h2, one_mul])
  have hx1 : x = 1 := (szTg_pow_eq_one_iff n x).mp h3
  apply Subtype.ext
  rw [htgl, hx1]
  show Submission.Sz.szTg n 1 = (1 : GL (Fin 4) (Submission.Sz.SzField n))
  exact Submission.Sz.szTg_one n

theorem sz_centralizer_involution_eq_U (n : ℕ) (hn : 1 ≤ n)
    {c : Submission.Sz.SzField n} (hc : c ≠ 0) :
    Subgroup.centralizer
      ({Work.BSLit.BenderFacts2.szUgS n 0 c} :
        Set (LeanEval.GroupTheory.Defs.SzModel n)) =
      Submission.Sz.szTwoGroupS n := by
  obtain ⟨hMtop, hEven, hOdd⟩ := Submission.Sz.szBorel_stronglyEmbedded n hn
  exact Commons.GroupTheory.StronglyEmbedded.centralizer_eq_left_of_isStronglyEmbedded
    (Submission.Sz.szBorelS n) (Submission.Sz.szTwoGroupS n) (Submission.Sz.szTS n)
    hMtop hEven hOdd
    (Submission.Sz.szBorelS_eq_sup n) (Submission.Sz.szTS_inf_szTwoGroupS n)
    (Submission.Sz.szTS_le_normalizer_szTwoGroupS n)
    (szUgS_mem_U n 0 c) (orderOf_szUgS_zero n hc)
    (by
      intro a ha
      obtain ⟨a', b', hab⟩ := Subgroup.mem_subgroupOf.mp ha
      apply Subtype.ext
      show (a : GL (Fin 4) (Submission.Sz.SzField n)) * Submission.Sz.szUg n 0 c =
        Submission.Sz.szUg n 0 c * (a : GL (Fin 4) (Submission.Sz.SzField n))
      rw [hab]
      exact (szUg_zero_mul_comm n c a' b').symm)
    (fun t ht hc' => szTS_eq_one_of_mem_centralizer_szUgS_zero n hc ht hc')

end Work.BSLit.BenderFacts2
