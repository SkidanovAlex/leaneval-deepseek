import Mathlib
import Submission.Work.FIArea1.Defs
import Submission.Work.FIArea1.boxZ_dvd_count_le
import Submission.Work.FIArea1.sum_divisors_card_le_two_sum_dvd
import Submission.Work.FIArea1.Nsol_prime_pow_le_aux
import Submission.Commons.NumberTheory.Divisors.sum_tau_pow_div_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
namespace Work.FIArea1

open Finset
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Conj1

/-- `p ↦ |p.1² + p.2²|`, the coordinate form of `gnorm` on `ℤ × ℤ`. -/
def Nsq (p : ℤ × ℤ) : ℕ := (p.1 ^ 2 + p.2 ^ 2).natAbs

lemma gnorm_mk (a b : ℤ) : Work.FIPlan.gnorm (⟨a, b⟩ : GaussianInt) = (a ^ 2 + b ^ 2).natAbs := by
  rw [Work.FIArea1.gnorm_coords]
  have key : ((a.natAbs ^ 2 + b.natAbs ^ 2 : ℕ) : ℤ) = ((a ^ 2 + b ^ 2).natAbs : ℤ) := by
    rw [Int.natAbs_of_nonneg (by positivity : (0 : ℤ) ≤ a ^ 2 + b ^ 2)]
    push_cast
    rw [sq_abs a, sq_abs b]
  exact_mod_cast key

lemma dvd_natAbs_iff (d : ℕ) (p : ℤ × ℤ) :
    (d : ℤ) ∣ p.1 ^ 2 + p.2 ^ 2 ↔ d ∣ (p.1 ^ 2 + p.2 ^ 2).natAbs := by
  rw [← Int.natAbs_of_nonneg (by positivity : (0 : ℤ) ≤ p.1 ^ 2 + p.2 ^ 2)]
  exact Int.natCast_dvd_natCast

lemma boxZ_mem (n : ℕ) {p : ℤ × ℤ} (hp : p ∈ boxZ n) :
    -(n : ℤ) ≤ p.1 ∧ p.1 ≤ n ∧ -(n : ℤ) ≤ p.2 ∧ p.2 ≤ n := by
  rw [boxZ] at hp
  obtain ⟨h1, h2⟩ := Finset.mem_product.mp hp
  rw [Finset.mem_Icc] at h1 h2
  exact ⟨h1.1, h1.2, h2.1, h2.2⟩

lemma natAbs_sq_sum_le (n : ℕ) {p : ℤ × ℤ} (hp : p ∈ boxZ n) :
    (p.1 ^ 2 + p.2 ^ 2).natAbs ≤ 2 * n * n := by
  obtain ⟨h1, h2, h3, h4⟩ := boxZ_mem n hp
  have e1 : p.1 ^ 2 ≤ (n : ℤ) ^ 2 := by nlinarith
  have e2 : p.2 ^ 2 ≤ (n : ℤ) ^ 2 := by nlinarith
  have key : (((p.1 ^ 2 + p.2 ^ 2).natAbs : ℕ) : ℤ) ≤ ((2 * n * n : ℕ) : ℤ) := by
    rw [Int.natAbs_of_nonneg (by positivity : (0 : ℤ) ≤ p.1 ^ 2 + p.2 ^ 2)]
    push_cast
    nlinarith
  exact_mod_cast key

/-! ### `Nsol d ≤ d * τ(d)`

The prime-power input `Nsol (p^e) ≤ (e+1)p^e` is the delegated lemma
`Work.FIArea1.Nsol_prime_pow_le_aux` (see below, `Nsol_prime_pow_le`). -/

theorem Nsol_prime_pow_le {p e : ℕ} (hp : p.Prime) :
    Work.FIArea1.Nsol (p ^ e) ≤ (e + 1) * p ^ e :=
  Work.FIArea1.Nsol_prime_pow_le_aux hp

lemma Nsol_one : Work.FIArea1.Nsol 1 = 1 := by
  rw [Nsol]
  have h : ({z : ZMod 1 × ZMod 1 | z.1 ^ 2 + z.2 ^ 2 = 0}) = Set.univ := by
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_univ]
    constructor
    · intro _; trivial
    · intro _
      have hz : z = (0, 0) := Subsingleton.elim z (0, 0)
      rw [hz]; simp
  rw [h, Set.ncard_univ]; simp

lemma Nsol_mul {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (hcop : Nat.Coprime m n) :
    Work.FIArea1.Nsol (m * n) = Work.FIArea1.Nsol m * Work.FIArea1.Nsol n := by
  have hmn : m * n ≠ 0 := by positivity
  let e : ZMod (m * n) ≃+* ZMod m × ZMod n := ZMod.chineseRemainder hcop
  let Φ : ZMod (m * n) × ZMod (m * n) → (ZMod m × ZMod m) × (ZMod n × ZMod n) :=
    fun z => (((e z.1).1, (e z.2).1), ((e z.1).2, (e z.2).2))
  have hΦinj : Function.Injective Φ := by
    intro z z' h
    simp only [Φ, Prod.mk.injEq] at h
    obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := h
    exact Prod.ext (e.injective (Prod.ext h1 h3)) (e.injective (Prod.ext h2 h4))
  have hΦset : Φ '' {z : ZMod (m * n) × ZMod (m * n) | z.1 ^ 2 + z.2 ^ 2 = 0} =
      ({a : ZMod m × ZMod m | a.1 ^ 2 + a.2 ^ 2 = 0} ×ˢ
        {b : ZMod n × ZMod n | b.1 ^ 2 + b.2 ^ 2 = 0}) := by
    ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      simp only [Set.mem_ofPred_eq] at hz ⊢
      have h0 : (e z.1) ^ 2 + (e z.2) ^ 2 = 0 := by
        have : e (z.1 ^ 2 + z.2 ^ 2) = (e z.1) ^ 2 + (e z.2) ^ 2 := by
          rw [map_add, map_pow, map_pow]
        rw [← this, hz, map_zero]
      refine ⟨?_, ?_⟩
      · have h1 := congrArg Prod.fst h0
        simpa [Φ] using h1
      · have h2 := congrArg Prod.snd h0
        simpa [Φ] using h2
    · rintro ⟨h1, h2⟩
      simp only [Set.mem_ofPred_eq] at h1 h2
      refine ⟨(e.symm (w.1.1, w.2.1), e.symm (w.1.2, w.2.2)), ?_, ?_⟩
      · simp only [Set.mem_ofPred_eq]
        apply e.injective
        rw [map_add, map_pow, map_pow, map_zero, e.apply_symm_apply, e.apply_symm_apply]
        ext
        · simpa [pow_two] using h1
        · simpa [pow_two] using h2
      · simp only [Φ]
        rw [e.apply_symm_apply, e.apply_symm_apply]
  rw [Nsol, ← Set.ncard_image_of_injective _ hΦinj, hΦset, Set.ncard_prod]
  rfl

lemma tau_prime_pow (p v : ℕ) (hp : p.Prime) : (p ^ v).divisors.card = v + 1 := by
  rw [Nat.divisors_prime_pow hp, Finset.card_map, Finset.card_range]

lemma Nsol_le_tau_mul : ∀ d, 1 ≤ d → Work.FIArea1.Nsol d ≤ d * d.divisors.card := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro hd
    rcases eq_or_lt_of_le hd with h1 | hgt
    · rw [← h1, Nsol_one]; simp
    · have hd0 : d ≠ 0 := by omega
      obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd (by omega : d ≠ 1)
      set v := d.factorization p with hv
      have hv1 : 1 ≤ v := (hp.dvd_iff_one_le_factorization hd0).mp hpd
      have hpdvd : p ^ v ∣ d := (hp.pow_dvd_iff_le_factorization hd0).mpr (le_of_eq hv)
      set m := d / p ^ v with hmdef
      have hd_eq : p ^ v * m = d := Nat.mul_div_cancel' hpdvd
      have hmpos : 0 < m := Nat.div_pos (Nat.le_of_dvd (by omega) hpdvd) (pow_pos hp.pos v)
      have hmlt : m < d := Nat.div_lt_self (by omega) (by
        have : 1 < p ^ v := by
          calc 1 < p := hp.one_lt
            _ ≤ p ^ v := Nat.le_self_pow (by omega) p
        exact this)
      have hpm : ¬ p ∣ m := by
        intro hpm
        obtain ⟨k, hk⟩ := hpm
        have hdvd : p ^ (v + 1) ∣ d := by
          refine ⟨k, ?_⟩
          rw [← hd_eq, hk, pow_succ']; ring
        have hle : v + 1 ≤ d.factorization p := (hp.pow_dvd_iff_le_factorization hd0).mp hdvd
        rw [hv] at hle; omega
      have hcop : Nat.Coprime (p ^ v) m := by
        rw [Nat.coprime_pow_left_iff (by omega : 0 < v)]
        exact (hp.coprime_iff_not_dvd).mpr hpm
      rw [← hd_eq, Nsol_mul (pow_pos hp.pos v) hmpos hcop]
      have hih := ih m hmlt (by omega)
      have hstep : Work.FIArea1.Nsol (p ^ v) * Work.FIArea1.Nsol m ≤
          ((v + 1) * p ^ v) * (m * m.divisors.card) :=
        Nat.mul_le_mul (Nsol_prime_pow_le hp) hih
      have heq : ((v + 1) * p ^ v) * (m * m.divisors.card) =
          p ^ v * m * (p ^ v * m).divisors.card := by
        have hτ : (p ^ v * m).divisors.card = (v + 1) * m.divisors.card := by
          rw [Nat.Coprime.card_divisors_mul hcop, tau_prime_pow p v hp]
        rw [hτ]; ring
      exact hstep.trans (le_of_eq heq)

end Conj1

open Conj1 in
theorem conj1_divisor_sum :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℤ, 0 ≤ R →
      (∑ z ∈ Work.FIPlan.gBox R, (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ))
        ≤ C * (((R.natAbs : ℝ) ^ 2 + 1) * (Real.log ((R.natAbs : ℝ) + 2)) ^ 2) := by
  obtain ⟨Cτ, hCτpos, hCτ⟩ := Commons.NumberTheory.Divisors.sum_tau_pow_div_le 1
  refine ⟨max (288 * Cτ) 1, lt_max_of_lt_left (by positivity), ?_⟩
  intro R hR
  set n : ℕ := R.natAbs with hn
  have hR_eq : (n : ℤ) = R := Int.natAbs_of_nonneg hR
  have hgBox : Work.FIPlan.gBox R = (boxZ n).image (fun p : ℤ × ℤ => (⟨p.1, p.2⟩ : GaussianInt)) := by
    rw [Work.FIPlan.gBox, boxZ, ← hR_eq]
  rw [hgBox, Finset.sum_image (Work.FIPlan.gaussMk_injective.injOn)]
  have hsum_eq : (∑ p ∈ boxZ n,
        (((Work.FIPlan.gnorm (⟨p.1, p.2⟩ : GaussianInt)).divisors.card : ℕ) : ℝ))
      = ∑ p ∈ boxZ n, (((Nsq p).divisors.card : ℕ) : ℝ) := by
    apply Finset.sum_congr rfl
    intro p _
    rw [gnorm_mk]
    rfl
  rw [hsum_eq]
  -- the divisor-splitting bound
  have hN : ∀ p ∈ boxZ n, Nsq p ≤ (2 * n) * (2 * n) := by
    intro p hp
    have h1 : Nsq p ≤ 2 * n * n := natAbs_sq_sum_le n hp
    have h2 : 2 * n * n ≤ (2 * n) * (2 * n) := by nlinarith
    linarith
  have hA : (∑ p ∈ boxZ n, (((Nsq p).divisors.card : ℕ) : ℝ))
      ≤ 2 * ∑ d ∈ Finset.Icc 1 (2 * n),
          ((((boxZ n).filter (fun p => d ∣ Nsq p)).card : ℕ) : ℝ) := by
    have h := sum_divisors_card_le_two_sum_dvd (boxZ n) (2 * n) Nsq hN
    calc (∑ p ∈ boxZ n, (((Nsq p).divisors.card : ℕ) : ℝ))
        = ((∑ p ∈ boxZ n, (Nsq p).divisors.card : ℕ) : ℝ) := by rw [Nat.cast_sum]
      _ ≤ ((2 * ∑ d ∈ Finset.Icc 1 (2 * n),
              ((boxZ n).filter (fun p => d ∣ Nsq p)).card : ℕ) : ℝ) := by exact_mod_cast h
      _ = 2 * ∑ d ∈ Finset.Icc 1 (2 * n),
              ((((boxZ n).filter (fun p => d ∣ Nsq p)).card : ℕ) : ℝ) := by
            push_cast; ring
  have hstep4 : (∑ d ∈ Finset.Icc 1 (2 * n),
        ((((boxZ n).filter (fun p => d ∣ Nsq p)).card : ℕ) : ℝ))
      ≤ ∑ d ∈ Finset.Icc 1 (2 * n), (Nsol d : ℝ) * ((2 * n / d + 2 : ℕ) : ℝ) ^ 2 := by
    apply Finset.sum_le_sum
    intro d hd
    rw [Finset.mem_Icc] at hd
    have hdpos : 0 < d := by omega
    have hle := boxZ_dvd_count_le n d hdpos
    have heq : ((boxZ n).filter (fun p => d ∣ Nsq p))
        = ((boxZ n).filter (fun p => (d : ℤ) ∣ p.1 ^ 2 + p.2 ^ 2)) := by
      apply Finset.filter_congr
      intro p _
      exact (dvd_natAbs_iff d p).symm
    rw [heq]
    have hle' : ((((boxZ n).filter (fun p => (d : ℤ) ∣ p.1 ^ 2 + p.2 ^ 2)).card : ℕ) : ℝ)
        ≤ ((Nsol d * (2 * n / d + 2) ^ 2 : ℕ) : ℝ) := by exact_mod_cast hle
    calc ((((boxZ n).filter (fun p => (d : ℤ) ∣ p.1 ^ 2 + p.2 ^ 2)).card : ℕ) : ℝ)
        ≤ ((Nsol d * (2 * n / d + 2) ^ 2 : ℕ) : ℝ) := hle'
      _ = (Nsol d : ℝ) * ((2 * n / d + 2 : ℕ) : ℝ) ^ 2 := by push_cast; ring
  have hstep5 : (∑ d ∈ Finset.Icc 1 (2 * n), (Nsol d : ℝ) * ((2 * n / d + 2 : ℕ) : ℝ) ^ 2)
      ≤ ∑ d ∈ Finset.Icc 1 (2 * n), (Nsol d : ℝ) * (36 * (n : ℝ) ^ 2 / (d : ℝ) ^ 2) := by
    apply Finset.sum_le_sum
    intro d hd
    rw [Finset.mem_Icc] at hd
    have hdle : d ≤ 2 * n := hd.2
    have hdpos : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
    have hnn : (0 : ℝ) ≤ (Nsol d : ℝ) := by positivity
    have hcast : (((2 * n / d + 2 : ℕ)) : ℝ) ≤ 2 * (n : ℝ) / (d : ℝ) + 2 := by
      push_cast
      have hcd := Nat.cast_div_le (α := ℝ) (m := 2 * n) (n := d)
      push_cast at hcd
      linarith
    have hbase : 2 * (n : ℝ) / (d : ℝ) + 2 ≤ 6 * (n : ℝ) / (d : ℝ) := by
      rw [div_add' _ _ _ (ne_of_gt hdpos)]
      rw [le_div_iff₀ hdpos]
      have hsimp : (2 * (n : ℝ) + 2 * (d : ℝ)) / (d : ℝ) * (d : ℝ) = 2 * (n : ℝ) + 2 * (d : ℝ) := by
        field_simp
      rw [hsimp]
      have hdle' : (d : ℝ) ≤ 2 * (n : ℝ) := by exact_mod_cast hdle
      nlinarith
    have hsquare : (2 * (n : ℝ) / (d : ℝ) + 2) ^ 2 ≤ 36 * (n : ℝ) ^ 2 / (d : ℝ) ^ 2 := by
      have h3 : (6 * (n : ℝ) / (d : ℝ)) ^ 2 = 36 * (n : ℝ) ^ 2 / (d : ℝ) ^ 2 := by rw [div_pow]; ring
      rw [← h3]
      apply sq_le_sq'
      · have h6 : (0 : ℝ) ≤ 6 * (n : ℝ) / (d : ℝ) := div_nonneg (by positivity) (le_of_lt hdpos)
        linarith [hbase, h6]
      · exact hbase
    calc (Nsol d : ℝ) * ((2 * n / d + 2 : ℕ) : ℝ) ^ 2
        ≤ (Nsol d : ℝ) * (2 * (n : ℝ) / (d : ℝ) + 2) ^ 2 := by
          apply mul_le_mul_of_nonneg_left _ hnn
          exact pow_le_pow_left₀ (by positivity) hcast 2
      _ ≤ (Nsol d : ℝ) * (36 * (n : ℝ) ^ 2 / (d : ℝ) ^ 2) := mul_le_mul_of_nonneg_left hsquare hnn
  have hstep6 : (∑ d ∈ Finset.Icc 1 (2 * n), (Nsol d : ℝ) * (36 * (n : ℝ) ^ 2 / (d : ℝ) ^ 2))
      = 36 * (n : ℝ) ^ 2 * ∑ d ∈ Finset.Icc 1 (2 * n), (Nsol d : ℝ) / (d : ℝ) ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d _
    ring
  have hstep7 : (∑ d ∈ Finset.Icc 1 (2 * n), (Nsol d : ℝ) / (d : ℝ) ^ 2)
      ≤ ∑ d ∈ Finset.Icc 1 (2 * n), ((d.divisors.card : ℕ) : ℝ) / (d : ℝ) := by
    apply Finset.sum_le_sum
    intro d hd
    rw [Finset.mem_Icc] at hd
    have hd1 : 1 ≤ d := hd.1
    have hdpos : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
    have hNl := Conj1.Nsol_le_tau_mul d hd1
    have hN' : (Nsol d : ℝ) ≤ (d : ℝ) * ((d.divisors.card : ℕ) : ℝ) := by exact_mod_cast hNl
    rw [div_le_iff₀ (pow_pos hdpos 2)]
    have hR : ((d.divisors.card : ℕ) : ℝ) / (d : ℝ) * (d : ℝ) ^ 2
        = ((d.divisors.card : ℕ) : ℝ) * (d : ℝ) := by
      field_simp
    rw [hR]
    nlinarith [hN']
  have hstep8 : (∑ d ∈ Finset.Icc 1 (2 * n), ((d.divisors.card : ℕ) : ℝ) / (d : ℝ))
      ≤ Cτ * (Real.log (2 * (n : ℝ) + 2)) ^ 2 := by
    rcases Nat.eq_zero_or_pos n with hn0 | hnpos
    · rw [hn0]
      have hempty : (Finset.Icc 1 (2 * 0) : Finset ℕ) = ∅ := Finset.Icc_eq_empty (by norm_num)
      rw [hempty, Finset.sum_empty]
      exact mul_nonneg hCτpos.le (sq_nonneg _)
    · have h2 := hCτ (2 * n) (by omega)
      have hcast : ((2 * n : ℕ) : ℝ) = 2 * (n : ℝ) := by push_cast; ring
      rw [hcast] at h2
      simpa [pow_one] using h2
  have hlog2 : Real.log (2 * (n : ℝ) + 2) ≤ 2 * Real.log ((n : ℝ) + 2) := by
    have h1 : Real.log (2 * (n : ℝ) + 2) = Real.log 2 + Real.log ((n : ℝ) + 1) := by
      rw [show 2 * (n : ℝ) + 2 = 2 * ((n : ℝ) + 1) by ring, Real.log_mul (by norm_num) (by positivity)]
    have h2 : Real.log ((n : ℝ) + 1) ≤ Real.log ((n : ℝ) + 2) :=
      Real.log_le_log (by positivity) (by linarith)
    have h3 : Real.log 2 ≤ Real.log ((n : ℝ) + 2) :=
      Real.log_le_log (by norm_num) (by linarith [show (0 : ℝ) ≤ (n : ℝ) by positivity])
    linarith
  have hsqlog : (Real.log (2 * (n : ℝ) + 2)) ^ 2 ≤ 4 * (Real.log ((n : ℝ) + 2)) ^ 2 := by
    have h0 : 0 ≤ Real.log (2 * (n : ℝ) + 2) :=
      Real.log_nonneg (by linarith [show (0 : ℝ) ≤ (n : ℝ) by positivity])
    calc (Real.log (2 * (n : ℝ) + 2)) ^ 2 ≤ (2 * Real.log ((n : ℝ) + 2)) ^ 2 :=
          pow_le_pow_left₀ h0 hlog2 2
      _ = 4 * (Real.log ((n : ℝ) + 2)) ^ 2 := by ring
  have hnnn : (0 : ℝ) ≤ (n : ℝ) ^ 2 := sq_nonneg _
  have hchain : (∑ p ∈ boxZ n, (((Nsq p).divisors.card : ℕ) : ℝ))
      ≤ 2 * (36 * (n : ℝ) ^ 2) * (Cτ * (4 * (Real.log ((n : ℝ) + 2)) ^ 2)) := by
    calc (∑ p ∈ boxZ n, (((Nsq p).divisors.card : ℕ) : ℝ))
        ≤ 2 * ∑ d ∈ Finset.Icc 1 (2 * n),
            ((((boxZ n).filter (fun p => d ∣ Nsq p)).card : ℕ) : ℝ) := hA
      _ ≤ 2 * ∑ d ∈ Finset.Icc 1 (2 * n), (Nsol d : ℝ) * ((2 * n / d + 2 : ℕ) : ℝ) ^ 2 :=
            mul_le_mul_of_nonneg_left hstep4 (by norm_num)
      _ ≤ 2 * ∑ d ∈ Finset.Icc 1 (2 * n), (Nsol d : ℝ) * (36 * (n : ℝ) ^ 2 / (d : ℝ) ^ 2) :=
            mul_le_mul_of_nonneg_left hstep5 (by norm_num)
      _ = 2 * (36 * (n : ℝ) ^ 2) * ∑ d ∈ Finset.Icc 1 (2 * n), (Nsol d : ℝ) / (d : ℝ) ^ 2 := by
            rw [hstep6]; ring
      _ ≤ 2 * (36 * (n : ℝ) ^ 2) * ∑ d ∈ Finset.Icc 1 (2 * n),
            ((d.divisors.card : ℕ) : ℝ) / (d : ℝ) :=
            mul_le_mul_of_nonneg_left hstep7 (by positivity)
      _ ≤ 2 * (36 * (n : ℝ) ^ 2) * (Cτ * (Real.log (2 * (n : ℝ) + 2)) ^ 2) :=
            mul_le_mul_of_nonneg_left hstep8 (by positivity)
      _ ≤ 2 * (36 * (n : ℝ) ^ 2) * (Cτ * (4 * (Real.log ((n : ℝ) + 2)) ^ 2)) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            apply mul_le_mul_of_nonneg_left _ hCτpos.le
            linarith [hsqlog]
  have hfinal : 2 * (36 * (n : ℝ) ^ 2) * (Cτ * (4 * (Real.log ((n : ℝ) + 2)) ^ 2))
      ≤ max (288 * Cτ) 1 * (((n : ℝ) ^ 2 + 1) * (Real.log ((n : ℝ) + 2)) ^ 2) := by
    have key2 : 2 * (36 * (n : ℝ) ^ 2) * (Cτ * (4 * (Real.log ((n : ℝ) + 2)) ^ 2))
        = 288 * Cτ * (n : ℝ) ^ 2 * (Real.log ((n : ℝ) + 2)) ^ 2 := by ring
    rw [key2]
    have hMnn : (0 : ℝ) ≤ max (288 * Cτ) 1 :=
      le_trans (by linarith [hCτpos.le] : (0 : ℝ) ≤ 288 * Cτ) (le_max_left _ _)
    have hL : (0 : ℝ) ≤ Real.log ((n : ℝ) + 2) ^ 2 := sq_nonneg _
    have hstep : (288 : ℝ) * Cτ * (n : ℝ) ^ 2 ≤ max (288 * Cτ) 1 * ((n : ℝ) ^ 2 + 1) :=
      mul_le_mul (le_max_left _ _) (by linarith) hnnn hMnn
    have := mul_le_mul_of_nonneg_right hstep hL
    linarith [this]
  exact le_trans hchain hfinal

end Work.FIArea1
