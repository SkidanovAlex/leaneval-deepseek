import Submission.Commons.NumberTheory.DirichletCharacter.exists_odd_character_mod_four
import Submission.Commons.NumberTheory.Diophantine.mertens_three_mod_four_prod_bound
import Submission.Commons.Analysis.Complex.Analytic.exists_analyticAt_log_of_ne_zero
import Submission.Commons.NumberTheory.LSeries.exists_zero_free_region_LFunction_chi4_all_t
import Submission.Commons.NumberTheory.DirichletCharacter.LFunction_zeroFree_region_awayFromAxis
import Submission.Commons.NumberTheory.DirichletCharacter.chi4_primeRecips_sub_const_powLog
import Submission.Commons.NumberTheory.LSeries.exists_zero_free_region_riemannZeta_log
import Submission.Commons.NumberTheory.LSeries.exists_zero_free_region_riemannZeta_all_t
import Submission.Commons.NumberTheory.LSeries.exists_bound_norm_riemannZeta_log_abs_t_ge_one
import Submission.Commons.NumberTheory.LSeries.exists_bound_norm_riemannZeta_fractional
import Submission.Commons.NumberTheory.LSeries.zero_free_region_LFunction_chi4
import Submission.Commons.NumberTheory.DirichletCharacter.LFunction_norm_le_two_of_two_le_re
import Submission.Commons.NumberTheory.LSeries.riemannZeta_norm_le_inv_sub_one
import Submission.Commons.NumberTheory.Zeta.vertical_line_identity_zeta
import Submission.Commons.NumberTheory.LSeries.exists_bound_LFunction_chi4_near_one
import Submission.Commons.NumberTheory.Zeta.inv_zeta_le_log_zeroFree
import Submission.Commons.NumberTheory.Diophantine.three_mod_four_lseries_half

set_option maxHeartbeats 1600000
open scoped BigOperators Topology
open Complex

namespace Commons.NumberTheory.Diophantine

open scoped BigOperators Topology

noncomputable def threeModFourSeries (s : ℂ) : ℂ :=
  ∑' n : ℕ, ((Set.indicator {n : ℕ | ∀ p : ℕ, p.Prime → p % 4 = 3 → ¬ p ∣ n} (fun _ => (1 : ℝ)) n : ℝ) : ℂ) * (n : ℂ) ^ (-s)

end Commons.NumberTheory.Diophantine

noncomputable section
namespace ETest

def Sset : Set ℕ := {n : ℕ | ∀ p : ℕ, p.Prime → p % 4 = 3 → ¬ p ∣ n}

noncomputable def aa (n : ℕ) : ℂ := ((Set.indicator Sset (fun _ => (1:ℝ)) n : ℝ) : ℂ)

lemma aa_of_mem {n : ℕ} (h : n ∈ Sset) : aa n = 1 := by
  rw [aa, Set.indicator_of_mem h]; norm_num

lemma aa_of_notMem {n : ℕ} (h : n ∉ Sset) : aa n = 0 := by
  rw [aa, Set.indicator_of_notMem h]; norm_num

lemma mem_Sset_mul {m n : ℕ} : m * n ∈ Sset ↔ m ∈ Sset ∧ n ∈ Sset := by
  constructor
  · intro h
    exact ⟨fun p hp hp4 hdvd => h p hp hp4 (dvd_mul_of_dvd_left hdvd n),
           fun p hp hp4 hdvd => h p hp hp4 (dvd_mul_of_dvd_right hdvd m)⟩
  · rintro ⟨hm, hn⟩ p hp hp4 hdvd
    rcases (Nat.Prime.dvd_mul hp).mp hdvd with h | h
    · exact hm p hp hp4 h
    · exact hn p hp hp4 h

lemma aa_mul (m n : ℕ) : aa (m * n) = aa m * aa n := by
  by_cases hm : m ∈ Sset
  · by_cases hn : n ∈ Sset
    · rw [aa_of_mem ((mem_Sset_mul).mpr ⟨hm, hn⟩), aa_of_mem hm, aa_of_mem hn]; ring
    · rw [aa_of_notMem (fun h => hn (mem_Sset_mul.mp h).2), aa_of_mem hm,
        aa_of_notMem hn]; ring
  · rw [aa_of_notMem (fun h => hm (mem_Sset_mul.mp h).1), aa_of_notMem hm]; ring

lemma aa_zero : aa 0 = 0 := by
  refine aa_of_notMem (fun h => ?_)
  exact h 3 (by norm_num) (by norm_num) (dvd_zero 3)

lemma aa_one : aa 1 = 1 := by
  refine aa_of_mem (fun p hp _ hdvd => ?_)
  exact hp.not_dvd_one hdvd

lemma aa_dichotomy (n : ℕ) : aa n = 0 ∨ aa n = 1 := by
  by_cases h : n ∈ Sset
  · exact Or.inr (aa_of_mem h)
  · exact Or.inl (aa_of_notMem h)

lemma norm_aa_le_one (n : ℕ) : ‖aa n‖ ≤ 1 := by
  rcases aa_dichotomy n with h | h <;> rw [h] <;> norm_num

noncomputable def Dser (s : ℂ) : ℂ := ∑' n : ℕ, aa n * (n : ℂ) ^ (-s)

noncomputable def fs (s : ℂ) : ℕ →*₀ ℂ where
  toFun n := aa n * (n : ℂ) ^ (-s)
  map_zero' := by simp [aa_zero]
  map_one' := by simp [aa_one]
  map_mul' m n := by
    have key : ((m:ℂ) * (n:ℂ)) ^ (-s) = (m:ℂ)^(-s) * (n:ℂ)^(-s) := by
      have h := Complex.mul_cpow_ofReal_nonneg
        (show (0:ℝ) ≤ (m:ℝ) by positivity) (show (0:ℝ) ≤ (n:ℝ) by positivity) (-s)
      simpa only [Complex.ofReal_natCast] using h
    rw [aa_mul, Nat.cast_mul, key]
    ring

lemma summable_norm_fs (s : ℂ) (hs : 1 < s.re) : Summable (fun n : ℕ => ‖fs s n‖) := by
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
    (Real.summable_nat_rpow.mpr (by linarith : -s.re < -1))
  show ‖aa n * (n : ℂ) ^ (-s)‖ ≤ (n : ℝ) ^ (-s.re)
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp only [aa_zero, zero_mul, norm_zero]
    positivity
  · rw [norm_mul, Complex.norm_natCast_cpow_of_pos hn]
    calc ‖aa n‖ * (n : ℝ) ^ (-s.re) ≤ 1 * (n : ℝ) ^ (-s.re) :=
          mul_le_mul_of_nonneg_right (norm_aa_le_one n) (Real.rpow_nonneg (Nat.cast_nonneg n) _)
      _ = _ := one_mul _

lemma euler_D (s : ℂ) (hs : 1 < s.re) :
    ∏' p : Nat.Primes, (1 - fs s p)⁻¹ = Dser s :=
  EulerProduct.eulerProduct_completely_multiplicative_tprod (summable_norm_fs s hs)

lemma hasProd_D (s : ℂ) (hs : 1 < s.re) :
    HasProd (fun p : Nat.Primes => (1 - fs s p)⁻¹) (Dser s) :=
  EulerProduct.eulerProduct_completely_multiplicative_hasProd (summable_norm_fs s hs)

end ETest

namespace ETest

open Commons.NumberTheory.DirichletCharacter

lemma norm_fs_le_one (s : ℂ) (hs : 1 < s.re) (n : ℕ) : ‖fs s n‖ ≤ 1 := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp
  · rw [show fs s n = aa n * (n:ℂ)^(-s) from rfl, norm_mul, Complex.norm_natCast_cpow_of_pos hn]
    calc ‖aa n‖ * (n:ℝ)^(-s.re) ≤ 1 * (n:ℝ)^(-s.re) :=
          mul_le_mul_of_nonneg_right (norm_aa_le_one n) (Real.rpow_nonneg (Nat.cast_nonneg n) _)
      _ = (n:ℝ)^(-s.re) := one_mul _
      _ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hn) (by linarith [hs])

noncomputable def fsq (s : ℂ) : ℕ →*₀ ℂ where
  toFun n := (fs s n)^2
  map_zero' := by simp
  map_one' := by simp
  map_mul' m n := by simp [map_mul, mul_pow]

lemma fsq_eq (s : ℂ) (n : ℕ) : fsq s n = aa n * (n:ℂ)^(-(2*s)) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    show (fs s 0)^2 = aa 0 * _
    rw [show fs s 0 = 0 from map_zero (fs s), aa_zero]; ring
  · show (fs s n)^2 = _
    show (aa n * (n:ℂ)^(-s))^2 = _
    rw [mul_pow]
    have h2 : ((n:ℂ)^(-s))^2 = (n:ℂ)^(-(2*s)) := by
      rw [← Complex.cpow_nat_mul]
      congr 1; ring
    have h3 : (aa n)^2 = aa n := by rcases aa_dichotomy n with h | h <;> rw [h] <;> norm_num
    rw [h2, h3]

lemma summable_norm_fsq (s : ℂ) (hs : 1 < s.re) : Summable (fun n : ℕ => ‖fsq s n‖) := by
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) (summable_norm_fs s hs)
  show ‖(fs s n)^2‖ ≤ ‖fs s n‖
  rw [norm_pow]
  have h1 := norm_fs_le_one s hs n
  have h0 : 0 ≤ ‖fs s n‖ := norm_nonneg _
  nlinarith [h0, h1, pow_nonneg h0 2]

lemma hasProd_D2 (s : ℂ) (hs : 1 < s.re) :
    HasProd (fun p : Nat.Primes => (1 - fsq s p)⁻¹) (Dser (2*s)) := by
  have := EulerProduct.eulerProduct_completely_multiplicative_hasProd (summable_norm_fsq s hs)
  -- value is ∑' n, fsq s n = Dser (2*s)
  rwa [show (∑' n : ℕ, fsq s n) = Dser (2*s) from ?_] at this
  rw [Dser]
  exact tsum_congr (fun n => fsq_eq s n)

end ETest

namespace ETest

open Commons.NumberTheory.DirichletCharacter

lemma chi4_prime_one {p : ℕ} (hp : p % 4 = 1) : chi4 (p : ZMod 4) = 1 := by
  have h : ((p : ℕ) : ZMod 4) = 1 := by rw [← ZMod.natCast_mod p 4, hp]; norm_num
  rw [h, chi4_apply]; simp

lemma chi4_prime_three {p : ℕ} (hp : p % 4 = 3) : chi4 (p : ZMod 4) = -1 := by
  have h : ((p : ℕ) : ZMod 4) = 3 := by rw [← ZMod.natCast_mod p 4, hp]; norm_num
  rw [h, chi4_apply]; simp

lemma chi4_prime_two : chi4 ((2 : ℕ) : ZMod 4) = 0 := by
  rw [chi4_apply]; simp

lemma mem_Sset_prime {p : ℕ} (hp : p.Prime) : p ∈ Sset ↔ p % 4 ≠ 3 := by
  constructor
  · intro h h3; exact h p hp h3 (dvd_refl p)
  · intro h q hq hq4 hdvd
    rcases (Nat.dvd_prime hp).mp hdvd with h1 | h1
    · exact hq.ne_one h1
    · rw [h1] at hq4; exact h hq4

end ETest

namespace ETest

open Commons.NumberTheory.DirichletCharacter

def pTwo : Nat.Primes := ⟨2, Nat.prime_two⟩

lemma cpow_neg_sq (x : ℂ) (s : ℂ) : (x^(-s))^2 = x^(-(2*s)) := by
  rw [← Complex.cpow_nat_mul x 2 (-s)]
  congr 1; ring

lemma two_rpow_ne_one (s : ℂ) (hs : 1 < s.re) : (2:ℂ)^(-s) ≠ 1 := by
  intro h
  have h1 : ‖(2:ℂ)^(-s)‖ = 1 := by rw [h]; simp
  rw [show ‖(2:ℂ)^(-s)‖ = (2:ℝ)^(-s.re) from by
    rw [show ((2:ℂ)) = ((2:ℝ):ℂ) by norm_num]
    exact Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num) (-s)] at h1
  have : (2:ℝ)^(-s.re) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  linarith

lemma aa_two : aa 2 = 1 := aa_of_mem ((mem_Sset_prime Nat.prime_two).mpr (by norm_num))

lemma Dser_sq_identity (s : ℂ) (hs : 1 < s.re) :
    Dser s ^ 2 * (1 - (2:ℂ)^(-s)) * riemannZeta (2*s)
      = riemannZeta s * DirichletCharacter.LFunction chi4 s * Dser (2*s) := by
  have hA : HasProd (fun p : Nat.Primes => ((1 - fs s p)⁻¹)^2) (Dser s ^ 2) := (hasProd_D s hs).pow 2
  have hB : HasProd (fun p : Nat.Primes => if p = pTwo then (1 - (2:ℂ)^(-s)) else 1)
      (1 - (2:ℂ)^(-s)) := by
    have h := hasProd_single pTwo (f := fun p : Nat.Primes => if p = pTwo then (1 - (2:ℂ)^(-s)) else 1)
      (by intro b hb; rw [if_neg hb])
    simpa using h
  have hC : HasProd (fun p : Nat.Primes => (1 - (p:ℂ)^(-(2*s)))⁻¹) (riemannZeta (2*s)) := by
    have h2re : (1 : ℝ) < ((2:ℂ)*s).re := by
      rw [Complex.mul_re]; simp; linarith
    have h := riemannZeta_eulerProduct_hasProd (s := (2:ℂ)*s) h2re
    simpa using h
  have hL := (hA.mul hB).mul hC
  have hA' : HasProd (fun p : Nat.Primes => (1 - (p:ℂ)^(-s))⁻¹) (riemannZeta s) :=
    riemannZeta_eulerProduct_hasProd hs
  have hB' : HasProd (fun p : Nat.Primes => (1 - chi4 (p : ZMod 4) * (p:ℂ)^(-s))⁻¹)
      (DirichletCharacter.LFunction chi4 s) := by
    have h := DirichletCharacter.LSeries_eulerProduct_hasProd chi4 hs
    rwa [← DirichletCharacter.LFunction_eq_LSeries chi4 hs] at h
  have hC' : HasProd (fun p : Nat.Primes => (1 - fsq s p)⁻¹) (Dser (2*s)) := hasProd_D2 s hs
  have hR := (hA'.mul hB').mul hC'
  rw [← hL.tprod_eq, ← hR.tprod_eq]
  refine tprod_congr (fun p => ?_)
  have hp : (p:ℕ).Prime := p.prop
  have hfsp : fs s p = aa (p:ℕ) * ((p:ℕ):ℂ)^(-s) := rfl
  rcases Commons.NumberTheory.Diophantine.prime_mod_four (p:ℕ) hp with h1 | h2 | h3
  · have haa : aa (p:ℕ) = 1 := aa_of_mem ((mem_Sset_prime hp).mpr (by omega))
    have hchi : chi4 (p : ZMod 4) = 1 := chi4_prime_one h1
    have hne : (p : Nat.Primes) ≠ pTwo := by
      intro h; have h2' : (p:ℕ) = 2 := congrArg Subtype.val h
      rw [h2'] at h1; norm_num at h1
    have hfs : fs s p = (p:ℂ)^(-s) := by rw [hfsp, haa, one_mul]
    have hfsq : fsq s p = (p:ℂ)^(-(2*s)) := by
      rw [show fsq s p = (fs s p)^2 from rfl, hfs, cpow_neg_sq]
    rw [if_neg hne, hfs, hchi, hfsq]
    ring
  · have hp2' : (p:ℕ) = 2 := by
      rcases hp.eq_two_or_odd with h | h
      · exact h
      · omega
    have hpq : (p : Nat.Primes) = pTwo := Subtype.ext (by rw [hp2']; rfl)
    have hfs : fs s p = (2:ℂ)^(-s) := by rw [hfsp, hp2', aa_two, one_mul]; norm_num
    have hchi : chi4 (p : ZMod 4) = 0 := by
      have hcast : (p : ZMod 4) = ((2:ℕ) : ZMod 4) := by rw [hp2']
      rw [hcast]; exact chi4_prime_two
    have hfsq : fsq s p = (2:ℂ)^(-(2*s)) := by
      rw [show fsq s p = (fs s p)^2 from rfl, hfs, cpow_neg_sq]
    rw [if_pos hpq, hfs, hchi, hfsq]
    have hc : (1 - (2:ℂ)^(-s)) ≠ 0 := sub_ne_zero.mpr (Ne.symm (two_rpow_ne_one s hs))
    have hkey : (1 - (2:ℂ)^(-s))⁻¹ * (1 - (2:ℂ)^(-s))⁻¹ * (1 - (2:ℂ)^(-s))
        = (1 - (2:ℂ)^(-s))⁻¹ := by
      rw [mul_assoc, inv_mul_cancel₀ hc, mul_one]
    rw [show ((1 - (2:ℂ)^(-s))⁻¹)^2 * (1 - (2:ℂ)^(-s))
          = (1 - (2:ℂ)^(-s))⁻¹ * (1 - (2:ℂ)^(-s))⁻¹ * (1 - (2:ℂ)^(-s)) from by ring, hkey]
    simp only [zero_mul, sub_zero, inv_one, mul_one]
    rw [hp2', Nat.cast_ofNat]
  · have haa : aa (p:ℕ) = 0 := aa_of_notMem (fun hm => (mem_Sset_prime hp).mp hm h3)
    have hchi : chi4 (p : ZMod 4) = -1 := chi4_prime_three h3
    have hne : (p : Nat.Primes) ≠ pTwo := by
      intro h; have h2' : (p:ℕ) = 2 := congrArg Subtype.val h
      rw [h2'] at h3; norm_num at h3
    have hfs : fs s p = 0 := by rw [hfsp, haa, zero_mul]
    have hfsq : fsq s p = 0 := by
      rw [show fsq s p = (fs s p)^2 from rfl, hfs]; ring
    rw [if_neg hne, hfs, hchi, hfsq]
    simp only [neg_one_mul, sub_zero, inv_one, one_pow, mul_one, sub_neg_eq_add]
    have hfac : (1 - (p:ℂ)^(-(2*s))) = (1 - (p:ℂ)^(-s)) * (1 + (p:ℂ)^(-s)) := by
      rw [← cpow_neg_sq]; ring
    rw [hfac, mul_inv, one_mul]

end ETest

namespace ETest

open Commons.NumberTheory.DirichletCharacter

lemma div_le_div_of_pos₀ {a b c d : ℝ} (hb : 0 < b) (hd : 0 < d) (h : a * d ≤ c * b) :
    a / b ≤ c / d := by
  rw [div_le_iff₀ hb, div_mul_eq_mul_div, le_div_iff₀ hd]
  linarith [h]

end ETest

namespace ETest

open Commons.NumberTheory.DirichletCharacter

lemma chi4_zero_free_region_log : ∃ c : ℝ, 0 < c ∧ ∀ σ t : ℝ,
    1 - c / Real.log (2 + |t|) ≤ σ →
    DirichletCharacter.LFunction chi4 ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
  obtain ⟨c1, hc1, h1⟩ := LFunction_zeroFree_region_awayFromAxis chi4 chi4_isPrimitive Commons.NumberTheory.LSeries.chi4_ne_one
  obtain ⟨c2, hc2, h2⟩ := Commons.NumberTheory.LSeries.exists_zero_free_region_LFunction_chi4_all_t
  have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  set c : ℝ := min (c1/2) (c2/(Real.log 4)^8) with hcdef
  have hcpos : 0 < c := lt_min (by linarith) (by positivity)
  refine ⟨c, hcpos, ?_⟩
  intro σ t hσ
  have hlogpos : 0 < Real.log (2 + |t|) := Real.log_pos (by linarith [abs_nonneg t])
  by_cases ht : 2 ≤ |t|
  · apply h1 σ t (by linarith)
    have hlog4t : 0 < Real.log (4 * (|t| + 2)) := Real.log_pos (by linarith [abs_nonneg t])
    have hc : c ≤ c1/2 := min_le_left _ _
    have hlogsplit : Real.log (4 * (|t| + 2)) = Real.log 4 + Real.log (2 + |t|) := by
      rw [Real.log_mul (by norm_num) (by linarith [abs_nonneg t])]; ring_nf
    have hkey : c * Real.log (4 * (|t| + 2)) ≤ c1 * Real.log (2 + |t|) := by
      rw [hlogsplit]
      calc c * (Real.log 4 + Real.log (2 + |t|))
          ≤ (c1/2) * (Real.log 4 + Real.log (2 + |t|)) :=
            mul_le_mul_of_nonneg_right hc (by positivity)
        _ ≤ (c1/2) * (Real.log (2 + |t|) + Real.log (2 + |t|)) := by
            apply mul_le_mul_of_nonneg_left _ (by linarith)
            have : Real.log 4 ≤ Real.log (2 + |t|) := Real.log_le_log (by norm_num) (by linarith)
            linarith
        _ = c1 * Real.log (2 + |t|) := by ring
    have hdiv : c / Real.log (2 + |t|) ≤ c1 / Real.log (4 * (|t| + 2)) :=
      div_le_div_of_pos₀ hlogpos hlog4t hkey
    linarith [hσ, hdiv]
  · apply h2 σ t
    rw [show (|t| + 2 : ℝ) = 2 + |t| by ring]
    have hlt : |t| < 2 := lt_of_not_ge ht
    have hc : c ≤ c2/(Real.log 4)^8 := min_le_right _ _
    have hlog9 : 0 < (Real.log (2 + |t|))^9 := by positivity
    have hloglt : Real.log (2 + |t|) ≤ Real.log 4 := Real.log_le_log (by linarith [abs_nonneg t]) (by linarith)
    have hratio : Real.log 4 ≠ 0 := ne_of_gt hlog4
    have hkey : c * (Real.log (2 + |t|))^9 ≤ c2 * Real.log (2 + |t|) := by
      have step1 : c * (Real.log (2 + |t|))^9 ≤ (c2/(Real.log 4)^8) * (Real.log (2 + |t|))^9 := by
        apply mul_le_mul_of_nonneg_right hc (by positivity)
      have step2 : (c2/(Real.log 4)^8) * (Real.log (2 + |t|))^9
          = c2 * Real.log (2 + |t|) * (Real.log (2 + |t|) / Real.log 4)^8 := by
        field_simp
      have hratio8 : (Real.log (2 + |t|) / Real.log 4)^8 ≤ 1 := by
        have h0 : 0 ≤ Real.log (2 + |t|) / Real.log 4 := div_nonneg hlogpos.le hlog4.le
        have h1' : Real.log (2 + |t|) / Real.log 4 ≤ 1 := by
          rw [div_le_one hlog4]; exact hloglt
        exact pow_le_one₀ h0 h1'
      have hc2pos : 0 ≤ c2 * Real.log (2 + |t|) := by positivity
      have step3 : c2 * Real.log (2 + |t|) * (Real.log (2 + |t|) / Real.log 4)^8
          ≤ c2 * Real.log (2 + |t|) := by
        simpa [mul_one] using mul_le_mul_of_nonneg_left hratio8 hc2pos
      linarith [step1, step2, step3]
    have hdiv : c / Real.log (2 + |t|) ≤ c2 / (Real.log (2 + |t|))^9 :=
      div_le_div_of_pos₀ hlogpos hlog9 hkey
    linarith [hσ, hdiv]

end ETest

namespace ETest

open Commons.NumberTheory.DirichletCharacter

lemma riemannZeta_zero_free_region_log_all_t : ∃ c : ℝ, 0 < c ∧ ∀ σ t : ℝ,
    1 - c / Real.log (2 + |t|) ≤ σ →
    riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
  obtain ⟨c1, hc1, h1⟩ := Commons.NumberTheory.LSeries.exists_zero_free_region_riemannZeta_log
  obtain ⟨c2, hc2, h2⟩ := Commons.NumberTheory.LSeries.exists_zero_free_region_riemannZeta_all_t
  have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  set c : ℝ := min (c1/2) (c2/(Real.log 4)^8) with hcdef
  have hcpos : 0 < c := lt_min (by linarith) (by positivity)
  refine ⟨c, hcpos, ?_⟩
  intro σ t hσ
  have hlogpos : 0 < Real.log (2 + |t|) := Real.log_pos (by linarith [abs_nonneg t])
  by_cases ht : 2 ≤ |t|
  · apply h1 σ t ht
    have hc : c ≤ c1 := by rw [hcdef]; linarith [min_le_left (c1/2) (c2/(Real.log 4)^8)]
    have hlogeq : Real.log (|t| + 2) = Real.log (2 + |t|) := by rw [add_comm]
    rw [hlogeq]
    have hdiv : c / Real.log (2 + |t|) ≤ c1 / Real.log (2 + |t|) :=
      div_le_div_of_nonneg_right hc hlogpos.le
    linarith [hσ, hdiv]
  · apply h2 σ t
    rw [show (|t| + 2 : ℝ) = 2 + |t| by ring]
    have hlt : |t| < 2 := lt_of_not_ge ht
    have hc : c ≤ c2/(Real.log 4)^8 := by rw [hcdef]; exact min_le_right _ _
    have hlog9 : 0 < (Real.log (2 + |t|))^9 := by positivity
    have hloglt : Real.log (2 + |t|) ≤ Real.log 4 := Real.log_le_log (by linarith [abs_nonneg t]) (by linarith)
    have hkey : c * (Real.log (2 + |t|))^9 ≤ c2 * Real.log (2 + |t|) := by
      have step1 : c * (Real.log (2 + |t|))^9 ≤ (c2/(Real.log 4)^8) * (Real.log (2 + |t|))^9 :=
        mul_le_mul_of_nonneg_right hc (by positivity)
      have step2 : (c2/(Real.log 4)^8) * (Real.log (2 + |t|))^9
          = c2 * Real.log (2 + |t|) * (Real.log (2 + |t|) / Real.log 4)^8 := by
        field_simp
      have hratio8 : (Real.log (2 + |t|) / Real.log 4)^8 ≤ 1 := by
        have h0 : 0 ≤ Real.log (2 + |t|) / Real.log 4 := div_nonneg hlogpos.le hlog4.le
        have h1' : Real.log (2 + |t|) / Real.log 4 ≤ 1 := by
          rw [div_le_one hlog4]; exact hloglt
        exact pow_le_one₀ h0 h1'
      have hc2pos : 0 ≤ c2 * Real.log (2 + |t|) := by positivity
      have step3 : c2 * Real.log (2 + |t|) * (Real.log (2 + |t|) / Real.log 4)^8
          ≤ c2 * Real.log (2 + |t|) := by
        simpa [mul_one] using mul_le_mul_of_nonneg_left hratio8 hc2pos
      linarith [step1, step2, step3]
    have hdiv : c / Real.log (2 + |t|) ≤ c2 / (Real.log (2 + |t|))^9 :=
      div_le_div_of_pos₀ hlogpos hlog9 hkey
    linarith [hσ, hdiv]

end ETest

namespace ETest

lemma riemannZeta_bound_log_region : ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ σ t : ℝ, 1 ≤ |t| →
    1 - c / Real.log (|t| + 2) ≤ σ →
    ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C * Real.log (|t| + 2) := by
  obtain ⟨C1, hC1, hb1⟩ := Commons.NumberTheory.LSeries.exists_bound_norm_riemannZeta_log_abs_t_ge_one
  obtain ⟨C2, hC2, hb2⟩ := Commons.NumberTheory.LSeries.exists_bound_norm_riemannZeta_fractional
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set c : ℝ := Real.log 2 / 2 with hcdef
  refine ⟨max C1 (C2 * Real.exp c), c, ?_, ?_, ?_⟩
  · exact lt_max_of_lt_left hC1
  · rw [hcdef]; positivity
  intro σ t ht hσ
  have hlogt : 0 < Real.log (|t| + 2) := Real.log_pos (by linarith [abs_nonneg t])
  have ht1 : (1:ℝ) ≤ |t| := by linarith
  have hlog2le : Real.log 2 ≤ Real.log (|t| + 2) :=
    Real.log_le_log (by norm_num) (by linarith [abs_nonneg t])
  have hσ12 : (1/2:ℝ) ≤ σ := by
    have h1σ : 1 - σ ≤ c / Real.log (|t| + 2) := by linarith [hσ]
    have : c / Real.log (|t| + 2) ≤ 1/2 := by
      rw [hcdef, div_le_iff₀ hlogt]; nlinarith [hlog2le, hlog2]
    linarith
  by_cases hσ1 : 1 ≤ σ
  · have hb := hb1 σ t hσ1 ht
    exact le_trans hb (mul_le_mul_of_nonneg_right (le_max_left _ _) hlogt.le)
  · have hσ1' : σ ≤ 1 := le_of_lt (lt_of_not_ge hσ1)
    have hb := hb2 σ t hσ12 hσ1' ht
    have hexp : |t| ^ (1 - σ) ≤ Real.exp c := by
      rw [Real.rpow_def_of_pos (by linarith : 0 < |t|)]
      apply Real.exp_le_exp.mpr
      rw [mul_comm (Real.log |t|) (1 - σ)]
      have h1σ : 1 - σ ≤ c / Real.log (|t| + 2) := by linarith [hσ]
      calc (1 - σ) * Real.log |t| ≤ (c / Real.log (|t|+2)) * Real.log |t| :=
            mul_le_mul_of_nonneg_right h1σ (Real.log_nonneg ht1)
        _ ≤ (c / Real.log (|t|+2)) * Real.log (|t| + 2) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact Real.log_le_log (by linarith) (by linarith)
        _ = c := by field_simp
    calc ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖
        ≤ C2 * |t| ^ (1 - σ) * Real.log (|t| + 2) := hb
      _ ≤ C2 * Real.exp c * Real.log (|t| + 2) := by
          apply mul_le_mul_of_nonneg_right _ hlogt.le
          exact mul_le_mul_of_nonneg_left hexp hC2.le
      _ = C2 * Real.log (|t| + 2) * Real.exp c := by ring
      _ = C2 * Real.exp c * Real.log (|t| + 2) := by ring
      _ ≤ max C1 (C2 * Real.exp c) * Real.log (|t| + 2) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) hlogt.le

end ETest


namespace ETest

noncomputable def oreg (δ : ℝ) : Set ℂ := {s : ℂ | 1 - δ / Real.log (2 + |s.im|) < s.re}

lemma isOpen_oreg (δ : ℝ) : IsOpen (oreg δ) := by
  have hlogc : Continuous (fun s : ℂ => Real.log (2 + |s.im|)) :=
    Continuous.log (by fun_prop) (fun s => ne_of_gt (by positivity : (0:ℝ) < 2 + |s.im|))
  have hcont : Continuous (fun s : ℂ => δ / Real.log (2 + |s.im|)) :=
    Continuous.div continuous_const hlogc
      (fun s => ne_of_gt (Real.log_pos (by linarith [abs_nonneg s.im] : (1:ℝ) < 2 + |s.im|)))
  have hcont2 : Continuous (fun s : ℂ => s.re - (1 - δ / Real.log (2 + |s.im|))) :=
    (continuous_re.sub (continuous_const.sub hcont))
  have : oreg δ = (fun s : ℂ => s.re - (1 - δ / Real.log (2 + |s.im|))) ⁻¹' (Set.Ioi 0) := by
    ext s; simp only [oreg, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_Ioi]; rw [sub_pos]
  rw [this]
  exact isOpen_Ioi.preimage hcont2

lemma im_smul_seg (y : ℂ) (t : ℝ) :
    (((1 - t : ℝ) • (2:ℂ) + t • y)).im = t * y.im := by
  rw [Complex.add_im, Complex.real_smul, Complex.real_smul]
  simp

lemma re_smul_seg (y : ℂ) (t : ℝ) :
    (((1 - t : ℝ) • (2:ℂ) + t • y)).re = (1 - t) * 2 + t * y.re := by
  rw [Complex.add_re, Complex.real_smul, Complex.real_smul]
  simp

lemma starConvex_oreg (δ : ℝ) (hδ : 0 < δ) : StarConvex ℝ (2 : ℂ) (oreg δ) := by
  rw [starConvex_iff_segment_subset]
  intro y hy
  rw [segment_eq_image]
  rintro _ ⟨t, ht, rfl⟩
  simp only [oreg, Set.mem_ofPred_eq] at hy ⊢
  rw [re_smul_seg, im_smul_seg]
  have ht0 : 0 ≤ t := ht.1
  have ht1 : t ≤ 1 := ht.2
  have hlogpos : 0 < Real.log (2 + |t * y.im|) := Real.log_pos (by
    have : (0:ℝ) ≤ |t * y.im| := abs_nonneg _
    linarith)
  have habs : |t * y.im| ≤ |y.im| := by
    rw [abs_mul, abs_of_nonneg ht0]; exact mul_le_of_le_one_left (abs_nonneg _) ht1
  have hlogle : Real.log (2 + |t * y.im|) ≤ Real.log (2 + |y.im|) :=
    Real.log_le_log (by linarith [abs_nonneg (t * y.im)]) (by linarith)
  by_cases hy2 : 2 ≤ y.re
  · have hlt1 : 1 - δ / Real.log (2 + |t * y.im|) < 1 := by
      have := div_pos hδ hlogpos
      linarith
    have hge2 : (1 - t) * 2 + t * y.re ≥ 2 := by nlinarith [hy2, ht0, ht1]
    linarith
  · have hy2' : y.re < 2 := lt_of_not_ge hy2
    have hygt : 1 - δ / Real.log (2 + |y.im|) < y.re := hy
    have hdl : δ / Real.log (2 + |y.im|) ≤ δ / Real.log (2 + |t * y.im|) :=
      div_le_div_of_nonneg_left hδ.le hlogpos hlogle
    have h2 : (1 - t) * 2 + t * y.re ≥ y.re := by nlinarith [hy2', ht0, ht1]
    linarith

end ETest

namespace ETest

lemma oreg_subset_half {δ : ℝ} (hδ2 : δ < Real.log 2 / 2) (hδ : 0 < δ) :
    oreg δ ⊆ {s : ℂ | 1/2 < s.re} := by
  intro s hs
  rw [oreg] at hs
  simp only [Set.mem_ofPred_eq] at hs ⊢
  have hlogpos : 0 < Real.log (2 + |s.im|) := Real.log_pos (by linarith [abs_nonneg s.im])
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogle : Real.log 2 ≤ Real.log (2 + |s.im|) :=
    Real.log_le_log (by norm_num) (by linarith [abs_nonneg s.im])
  have hdl : δ / Real.log (2 + |s.im|) ≤ δ / Real.log 2 :=
    div_le_div_of_nonneg_left hδ.le hlog2pos hlogle
  have h2 : δ / Real.log 2 < 1/2 := by
    rw [div_lt_iff₀ hlog2pos]; linarith
  linarith [hs, hdl, h2]

lemma mem_oreg_two (δ : ℝ) (hδ : 0 < δ) : (2:ℂ) ∈ oreg δ := by
  rw [oreg]
  simp only [Set.mem_ofPred_eq]
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hd : 0 < δ / Real.log 2 := div_pos hδ hlog2pos
  have him : (2:ℂ).im = 0 := by simp
  have hre : (2:ℂ).re = 2 := by simp
  rw [him, hre, abs_zero, add_zero]
  linarith

lemma isSimplyConnected_oreg (δ : ℝ) (hδ : 0 < δ) : IsSimplyConnected (oreg δ) := by
  have hsc := starConvex_oreg δ hδ
  have hcs : ContractibleSpace ↥(oreg δ) := hsc.contractibleSpace ⟨2, mem_oreg_two δ hδ⟩
  exact SimplyConnectedSpace.ofContractible ↥(oreg δ)

end ETest

namespace ETest

lemma norm_fs_le (w : ℂ) (p : Nat.Primes) : ‖fs w p‖ ≤ (p:ℝ)^(-w.re) := by
  show ‖aa (p:ℕ) * ((p:ℕ):ℂ)^(-w)‖ ≤ _
  rw [norm_mul, Complex.norm_natCast_cpow_of_pos p.prop.pos]
  calc ‖aa (p:ℕ)‖ * (p:ℝ)^(-w.re) ≤ 1 * (p:ℝ)^(-w.re) :=
        mul_le_mul_of_nonneg_right (norm_aa_le_one _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    _ = _ := one_mul _

lemma norm_fs_le_half (w : ℂ) (hw : 1 < w.re) (p : Nat.Primes) : ‖fs w p‖ ≤ 1/2 := by
  have hp2 : (2:ℝ) ≤ (p:ℝ) := by exact_mod_cast p.prop.two_le
  have h1 : (p:ℝ)^(-w.re) ≤ (2:ℝ)^(-w.re) := by
    rw [Real.rpow_neg (Nat.cast_nonneg _), Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
    exact inv_anti₀ (Real.rpow_pos_of_pos (by norm_num) _)
      (Real.rpow_le_rpow (by norm_num) hp2 (by linarith))
  have h2 : (2:ℝ)^(-w.re) ≤ 1/2 := by
    rw [show (1/2:ℝ) = (2:ℝ)^(-1:ℝ) by norm_num]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  linarith [norm_fs_le w p, h1, h2]

lemma norm_fs_ne_one (w : ℂ) (hw : 1 < w.re) (p : Nat.Primes) : fs w p ≠ 1 := by
  intro h
  have hle := norm_fs_le_half w hw p
  rw [h, norm_one] at hle
  norm_num at hle

lemma Dser_ne_zero (w : ℂ) (hw : 1 < w.re) : Dser w ≠ 0 := by
  rw [← euler_D w hw]
  have hpoint : ∀ p : Nat.Primes, (1 - fs w p)⁻¹ = 1 + ((1 - fs w p)⁻¹ - 1) := fun p => by ring
  rw [tprod_congr (fun p => hpoint p)]
  apply tprod_one_add_ne_zero_of_summable
  · intro p
    have : 1 + ((1 - fs w p)⁻¹ - 1) = (1 - fs w p)⁻¹ := by ring
    rw [this]; exact inv_ne_zero (sub_ne_zero.mpr (Ne.symm (norm_fs_ne_one w hw p)))
  · have hbase : Summable (fun p : Nat.Primes => ‖fs w p‖) :=
      (summable_norm_fs w hw).subtype (fun n => n.Prime)
    refine Summable.of_nonneg_of_le (fun p => norm_nonneg _) (fun p => ?_) (hbase.mul_left 2)
    have hfs_half := norm_fs_le_half w hw p
    have hfs_nonneg : 0 ≤ ‖fs w p‖ := norm_nonneg _
    have hsub : ‖(1 - fs w p)⁻¹ - 1‖ = ‖fs w p‖ / ‖1 - fs w p‖ := by
      have hc : (1 - fs w p) ≠ 0 := sub_ne_zero.mpr (Ne.symm (norm_fs_ne_one w hw p))
      rw [show (1 - fs w p)⁻¹ - 1 = fs w p / (1 - fs w p) by
        rw [eq_div_iff (b := 1 - fs w p) hc, sub_mul, inv_mul_cancel₀ hc, one_mul]; ring]
      rw [norm_div]
    rw [hsub]
    have hden : 1/2 ≤ ‖1 - fs w p‖ := by
      have h1 := abs_norm_sub_norm_le (1:ℂ) (fs w p)
      rw [norm_one] at h1
      have h2 := (abs_le.mp h1).2
      linarith
    calc ‖fs w p‖ / ‖1 - fs w p‖ ≤ ‖fs w p‖ / (1/2) :=
          div_le_div_of_nonneg_left hfs_nonneg (by norm_num) hden
      _ = 2 * ‖fs w p‖ := by ring

end ETest

namespace ETest

end ETest

namespace ETest

lemma oreg_re_bound {δ : ℝ} (hδ : 0 < δ) {s : ℂ} (hs : s ∈ oreg δ) :
    1 - δ / Real.log 2 < s.re := by
  rw [oreg] at hs
  simp only [Set.mem_ofPred_eq] at hs
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hle : Real.log 2 ≤ Real.log (2 + |s.im|) :=
    Real.log_le_log (by norm_num) (by linarith [abs_nonneg s.im])
  have hdl : δ / Real.log (2 + |s.im|) ≤ δ / Real.log 2 :=
    div_le_div_of_nonneg_left hδ.le hlog2 hle
  linarith

lemma diffOn_cpow_neg_two (n : ℕ) {U : Set ℂ} :
    DifferentiableOn ℂ (fun s : ℂ => aa n * (n:ℂ)^(-(2*s))) U := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    refine DifferentiableOn.congr (differentiableOn_const (c := (0:ℂ))) (fun s _ => ?_)
    simp [aa_zero]
  · have hnne : (n:ℂ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
    have heq : (fun s : ℂ => aa n * (n:ℂ)^(-(2*s)))
        = fun s => aa n * Complex.exp (Complex.log (n:ℂ) * (-(2*s))) := by
      funext s; rw [Complex.cpow_def_of_ne_zero hnne]
    rw [heq]; fun_prop

lemma analyticOnNhd_Dser_two {δ : ℝ} (hδ : 0 < δ) (hδ4 : δ ≤ Real.log 2 / 4) :
    AnalyticOnNhd ℂ (fun s => Dser (2*s)) (oreg δ) := by
  have ho := isOpen_oreg δ
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hδlog : δ / Real.log 2 ≤ 1/4 := by rw [div_le_iff₀ hlog2]; linarith
  have hE : 1 < 2 * (1 - δ / Real.log 2) := by linarith
  set E : ℝ := 2 * (1 - δ / Real.log 2) with hEdef
  have hsum : Summable (fun n : ℕ => (n:ℝ)^(-E)) :=
    Real.summable_nat_rpow.mpr (by rw [hEdef]; linarith)
  refine DifferentiableOn.analyticOnNhd ?_ ho
  have hconv : (fun s => Dser (2*s)) = fun s => ∑' n : ℕ, aa n * (n:ℂ)^(-(2*s)) := by
    funext s; rw [Dser]
  rw [hconv]
  apply Complex.differentiableOn_tsum_of_summable_norm (ι := ℕ) (U := oreg δ)
    (F := fun n s => aa n * (n:ℂ)^(-(2*s)))
    (u := fun n : ℕ => (n:ℝ)^(-E))
  · exact hsum
  · intro n; exact diffOn_cpow_neg_two n
  · exact ho
  · intro n s hs
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp only [aa_zero, norm_zero, zero_mul]; positivity
    · rw [norm_mul, Complex.norm_natCast_cpow_of_pos hn]
      have hsr := oreg_re_bound hδ hs
      have hExp : -(2*s).re ≤ -E := by
        rw [Complex.mul_re]; simp
        rw [hEdef]; linarith
      calc ‖aa n‖ * (n:ℝ)^(-(2*s).re) ≤ 1 * (n:ℝ)^(-(2*s).re) :=
            mul_le_mul_of_nonneg_right (norm_aa_le_one n) (Real.rpow_nonneg (Nat.cast_nonneg n) _)
        _ = (n:ℝ)^(-(2*s).re) := one_mul _
        _ ≤ (n:ℝ)^(-E) := Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) hExp

end ETest

namespace ETest

open Commons.NumberTheory.DirichletCharacter

noncomputable def Gfun (s : ℂ) : ℂ :=
  riemannZeta₁ s * DirichletCharacter.LFunction chi4 s * (1 - (2:ℂ)^(-s))⁻¹
    * Dser (2*s) * (riemannZeta (2*s))⁻¹

lemma analyticOnNhd_cpow_two {δ : ℝ} :
    AnalyticOnNhd ℂ (fun s : ℂ => (2:ℂ)^(-s)) (oreg δ) := by
  apply DifferentiableOn.analyticOnNhd _ (isOpen_oreg δ)
  exact (DifferentiableOn.neg differentiableOn_id).const_cpow (Or.inl (by norm_num))

lemma analyticOnNhd_zeta_two {δ : ℝ} (hδ : 0 < δ) (hδ4 : δ ≤ Real.log 2 / 4) :
    AnalyticOnNhd ℂ (fun s : ℂ => riemannZeta (2*s)) (oreg δ) := by
  apply DifferentiableOn.analyticOnNhd _ (isOpen_oreg δ)
  apply DifferentiableOn.comp differentiableOn_riemannZeta
    ((differentiableOn_const (c := (2:ℂ))).mul differentiableOn_id)
  intro s hs
  rw [Set.mem_compl_iff, Set.mem_singleton_iff]
  intro h
  have hre := congrArg Complex.re h
  simp only [Pi.mul_apply, id_eq] at hre
  rw [Complex.mul_re] at hre
  have h2re : (2:ℂ).re = 2 := by simp
  have h2im : (2:ℂ).im = 0 := by simp
  rw [h2re, h2im, Complex.one_re] at hre
  ring_nf at hre
  have hsr := oreg_re_bound hδ hs
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hδlog : δ / Real.log 2 ≤ 1/4 := by rw [div_le_iff₀ hlog2]; linarith
  nlinarith [hsr, hδlog]

end ETest

namespace ETest

open Commons.NumberTheory.DirichletCharacter

end ETest

namespace ETest

open Commons.NumberTheory.DirichletCharacter

lemma oreg_lt {δ : ℝ} {s : ℂ} (hs : s ∈ oreg δ) :
    1 - δ / Real.log (2 + |s.im|) < s.re := by
  rw [oreg] at hs; simpa using hs

lemma oreg_re_lt {δ : ℝ} (hδ : 0 < δ) {s : ℂ} (hs : s ∈ oreg δ) :
    1 - δ / Real.log 2 < s.re := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hle : Real.log 2 ≤ Real.log (2 + |s.im|) :=
    Real.log_le_log (by norm_num) (by linarith [abs_nonneg s.im])
  have hdl : δ / Real.log (2 + |s.im|) ≤ δ / Real.log 2 :=
    div_le_div_of_nonneg_left hδ.le hlog2 hle
  linarith [oreg_lt hs]

lemma oreg_re_pos {δ : ℝ} (hδ4 : δ ≤ Real.log 2 / 4) {s : ℂ} (hs : s ∈ oreg δ) :
    (1/2:ℝ) < s.re := by
  have hlogpos : 0 < Real.log (2 + |s.im|) := Real.log_pos (by linarith [abs_nonneg s.im])
  have hlt := oreg_lt hs
  by_cases hδ0 : δ ≤ 0
  · have : 0 ≤ -(δ / Real.log (2 + |s.im|)) := by
      apply neg_nonneg.mpr
      exact div_nonpos_of_nonpos_of_nonneg hδ0 hlogpos.le
    linarith
  · push_neg at hδ0
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hle : Real.log 2 ≤ Real.log (2 + |s.im|) :=
      Real.log_le_log (by norm_num) (by linarith [abs_nonneg s.im])
    have hdl : δ / Real.log (2 + |s.im|) ≤ δ / Real.log 2 :=
      div_le_div_of_nonneg_left hδ0.le hlog2 hle
    have hδlog : δ / Real.log 2 ≤ 1/4 := by rw [div_le_iff₀ hlog2]; linarith
    linarith

lemma two_mul_re (s : ℂ) : (2 * s).re = 2 * s.re := by rw [Complex.mul_re]; norm_num
lemma two_mul_im (s : ℂ) : (2 * s).im = 2 * s.im := by rw [Complex.mul_im]; norm_num

lemma two_cpow_ne_one_of_re_pos {s : ℂ} (hs : 0 < s.re) : (2:ℂ)^(-s) ≠ 1 := by
  intro h
  have h1 : ‖(2:ℂ)^(-s)‖ = 1 := by rw [h]; simp
  rw [show (2:ℂ) = ((2:ℝ):ℂ) by norm_num, Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0:ℝ) < 2) (-s), Complex.neg_re] at h1
  have h2 : (2:ℝ)^(-s.re) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  linarith

lemma analyticOnNhd_Gfun {δ : ℝ} (hδ : 0 < δ) (hδ4 : δ ≤ Real.log 2 / 4)
    (hzf : ∀ σ t : ℝ, 1 - δ / Real.log (2 + |t|) ≤ σ →
      riemannZeta ((σ:ℂ) + (t:ℂ) * Complex.I) ≠ 0)
    (hcf : ∀ σ t : ℝ, 1 - δ / Real.log (2 + |t|) ≤ σ →
      DirichletCharacter.LFunction chi4 ((σ:ℂ) + (t:ℂ) * Complex.I) ≠ 0) :
    AnalyticOnNhd ℂ Gfun (oreg δ) := by
  have ho := isOpen_oreg δ
  have h1 : AnalyticOnNhd ℂ riemannZeta₁ (oreg δ) :=
    differentiable_riemannZeta₁.differentiableOn.analyticOnNhd ho
  have h2 : AnalyticOnNhd ℂ (DirichletCharacter.LFunction chi4) (oreg δ) :=
    (DirichletCharacter.differentiable_LFunction Commons.NumberTheory.LSeries.chi4_ne_one).differentiableOn.analyticOnNhd ho
  have h3 : AnalyticOnNhd ℂ (fun s => (1 - (2:ℂ)^(-s))⁻¹) (oreg δ) := by
    apply AnalyticOnNhd.inv
    · exact analyticOnNhd_const.sub (analyticOnNhd_cpow_two (δ := δ))
    · intro s hs
      exact sub_ne_zero.mpr (Ne.symm (two_cpow_ne_one_of_re_pos (by linarith [oreg_re_pos hδ4 hs] : (0:ℝ) < s.re)))
  have h4 := analyticOnNhd_Dser_two hδ hδ4
  have h5 : AnalyticOnNhd ℂ (fun s => (riemannZeta (2*s))⁻¹) (oreg δ) := by
    apply AnalyticOnNhd.inv
    · exact analyticOnNhd_zeta_two hδ hδ4
    · intro s hs
      apply riemannZeta_ne_zero_of_one_lt_re
      rw [two_mul_re]
      have := oreg_re_pos hδ4 hs
      linarith
  have h := (((h1.mul h2).mul h3).mul h4).mul h5
  change AnalyticOnNhd ℂ (fun s => riemannZeta₁ s * DirichletCharacter.LFunction chi4 s * (1 - (2:ℂ)^(-s))⁻¹ * Dser (2*s) * (riemannZeta (2*s))⁻¹) (oreg δ) at h
  exact h

lemma Gfun_ne_zero {δ : ℝ} (hδ4 : δ ≤ Real.log 2 / 4)
    (hzf : ∀ σ t : ℝ, 1 - δ / Real.log (2 + |t|) ≤ σ →
      riemannZeta ((σ:ℂ) + (t:ℂ) * Complex.I) ≠ 0)
    (hcf : ∀ σ t : ℝ, 1 - δ / Real.log (2 + |t|) ≤ σ →
      DirichletCharacter.LFunction chi4 ((σ:ℂ) + (t:ℂ) * Complex.I) ≠ 0)
    {s : ℂ} (hs : s ∈ oreg δ) : Gfun s ≠ 0 := by
  have hlogpos : 0 < Real.log (2 + |s.im|) := Real.log_pos (by linarith [abs_nonneg s.im])
  have hσ : 1 - δ / Real.log (2 + |s.im|) ≤ s.re := le_of_lt (oreg_lt hs)
  have hζne : riemannZeta s ≠ 0 := by
    have := hzf s.re s.im hσ
    rwa [Complex.re_add_im] at this
  have hLne : DirichletCharacter.LFunction chi4 s ≠ 0 := by
    have := hcf s.re s.im hσ
    rwa [Complex.re_add_im] at this
  have hzeta1ne : riemannZeta₁ s ≠ 0 := by
    rcases eq_or_ne s 1 with h | h
    · rw [h, riemannZeta₁_one]; exact one_ne_zero
    · have hz : riemannZeta₁ s = (s - 1) * riemannZeta s := by
        rw [riemannZeta_eq_inv_sub_mul h, ← mul_assoc, mul_inv_cancel₀ (sub_ne_zero.mpr h), one_mul]
      rw [hz]; exact mul_ne_zero (sub_ne_zero.mpr h) hζne
  have hre := oreg_re_pos hδ4 hs
  rw [Gfun]
  refine mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hzeta1ne hLne) ?_) ?_) ?_
  · exact inv_ne_zero (sub_ne_zero.mpr (Ne.symm (two_cpow_ne_one_of_re_pos (by linarith [hre] : (0:ℝ) < s.re))))
  · apply Dser_ne_zero; rw [two_mul_re]; linarith
  · exact inv_ne_zero (riemannZeta_ne_zero_of_one_lt_re (by rw [two_mul_re]; linarith))

end ETest

namespace ETest

open Commons.NumberTheory.DirichletCharacter

lemma Gfun_eq (s : ℂ) (hs : 1 < s.re) : Gfun s = (s - 1) * Dser s ^ 2 := by
  have hsne : s ≠ 1 := fun h => by rw [h] at hs; norm_num at hs
  have h1 : (1 - (2:ℂ)^(-s)) ≠ 0 := sub_ne_zero.mpr (Ne.symm (two_rpow_ne_one s hs))
  have h2 : riemannZeta (2*s) ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re (by rw [two_mul_re]; linarith)
  have ha : (1 - (2:ℂ)^(-s)) * riemannZeta (2*s) ≠ 0 := mul_ne_zero h1 h2
  have hzeta1 : riemannZeta₁ s = (s - 1) * riemannZeta s := by
    rw [riemannZeta_eq_inv_sub_mul hsne, ← mul_assoc, mul_inv_cancel₀ (sub_ne_zero.mpr hsne), one_mul]
  have hmain := Dser_sq_identity s hs
  have key : Dser s ^ 2 = riemannZeta s * DirichletCharacter.LFunction chi4 s * Dser (2*s)
      * ((1 - (2:ℂ)^(-s)) * riemannZeta (2*s))⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq₀ ha, ← mul_assoc]
    exact hmain
  rw [Gfun, key, hzeta1, mul_inv]
  ring

end ETest

namespace ETest

end ETest

namespace ETest

open Commons.NumberTheory.DirichletCharacter

lemma exists_analytic_sqrt_Gfun {δ : ℝ} (hδ : 0 < δ) (hδ4 : δ ≤ Real.log 2 / 4)
    (hzf : ∀ σ t : ℝ, 1 - δ / Real.log (2 + |t|) ≤ σ →
      riemannZeta ((σ:ℂ) + (t:ℂ) * Complex.I) ≠ 0)
    (hcf : ∀ σ t : ℝ, 1 - δ / Real.log (2 + |t|) ≤ σ →
      DirichletCharacter.LFunction chi4 ((σ:ℂ) + (t:ℂ) * Complex.I) ≠ 0) :
    ∃ H : ℂ → ℂ, AnalyticOnNhd ℂ H (oreg δ) ∧ ∀ s, H s ^ 2 = Gfun s := by
  have ho := isOpen_oreg δ
  have hGan := analyticOnNhd_Gfun hδ hδ4 hzf hcf
  have hGc : ContinuousOn Gfun (oreg δ) := hGan.continuousOn
  have hG0 : 0 ∉ Gfun '' (oreg δ) := by
    rintro ⟨z, hz, hz0⟩; exact Gfun_ne_zero hδ4 hzf hcf hz hz0
  obtain ⟨f, hfc, hfsq⟩ := Complex.exists_continuousOn_pow_eq
    (isSimplyConnected_oreg δ hδ) ho hGc hG0 (by norm_num : (2:ℕ) ≠ 0)
  refine ⟨f, ?_, hfsq⟩
  change ∀ z ∈ oreg δ, AnalyticAt ℂ f z
  intro z hz
  have hGnz : Gfun z ≠ 0 := Gfun_ne_zero hδ4 hzf hcf hz
  obtain ⟨g, hgan, hgeq⟩ :=
    Commons.Analysis.Complex.Analytic.exists_analyticAt_log_of_ne_zero (hGan z hz) hGnz
  set h : ℂ → ℂ := fun w => Complex.exp (g w / 2) with hhdef
  have hh2 : h ^ 2 =ᶠ[𝓝 z] Gfun := by
    filter_upwards [hgeq] with w hw
    simp only [hhdef, Pi.pow_apply]
    rw [hw, ← Complex.exp_nat_mul]
    congr 1; ring
  have hhan : AnalyticAt ℂ h z := by rw [hhdef]; fun_prop
  have hhz : h z ≠ 0 := by rw [hhdef]; exact Complex.exp_ne_zero _
  have hfh : ∀ᶠ w in 𝓝 z, (f w - h w) * (f w + h w) = 0 := by
    filter_upwards [hh2] with w hw
    have h1 : f w ^ 2 = h w ^ 2 := by rw [hfsq w, ← hw, Pi.pow_apply]
    have h2 : (f w - h w) * (f w + h w) = f w ^ 2 - h w ^ 2 := by ring
    rw [h2, h1]; ring
  have hcase : f z = h z ∨ f z = -h z := by
    have hz0 := hfh.self_of_nhds
    rcases mul_eq_zero.mp hz0 with h' | h'
    · left; exact sub_eq_zero.mp h'
    · right; exact eq_neg_of_add_eq_zero_left h'
  rcases hcase with hcase | hcase
  · have hne : ∀ᶠ w in 𝓝 z, f w + h w ≠ 0 := by
      have hcf_cont : ContinuousAt f z := hfc.continuousAt (ho.mem_nhds hz)
      have hcont : ContinuousAt (fun w => f w + h w) z := hcf_cont.add hhan.continuousAt
      refine hcont.eventually_ne ?_
      rw [hcase]
      intro hcon
      exact hhz (by
        have h2 : (2:ℂ) * h z = 0 := by rwa [← two_mul] at hcon
        exact (mul_eq_zero.mp h2).resolve_left two_ne_zero)
    have hfeq : h =ᶠ[𝓝 z] f := by
      filter_upwards [hfh, hne] with w hw hne'
      have h' : f w - h w = 0 := by
        rcases mul_eq_zero.mp hw with h' | h'
        · exact h'
        · exact absurd h' hne'
      exact (sub_eq_zero.mp h').symm
    exact hhan.congr hfeq
  · have hne : ∀ᶠ w in 𝓝 z, f w - h w ≠ 0 := by
      have hcf_cont : ContinuousAt f z := hfc.continuousAt (ho.mem_nhds hz)
      have hcont : ContinuousAt (fun w => f w - h w) z := hcf_cont.sub hhan.continuousAt
      refine hcont.eventually_ne ?_
      rw [hcase]
      intro hcon
      apply hhz
      have h2 : (-h z) + (-h z) = 0 := by
        rw [show (-h z) + (-h z) = -h z - h z by ring]; exact hcon
      have h3 : (2:ℂ) * (-h z) = 0 := by rwa [two_mul]
      exact neg_eq_zero.mp ((mul_eq_zero.mp h3).resolve_left two_ne_zero)
    have hfeq : (-h) =ᶠ[𝓝 z] f := by
      filter_upwards [hfh, hne] with w hw hne'
      have h' : f w + h w = 0 := by
        rcases mul_eq_zero.mp hw with h' | h'
        · exact absurd h' hne'
        · exact h'
      simp only [Pi.neg_apply]; exact neg_eq_of_add_eq_zero_left h'
    exact hhan.neg.congr hfeq

end ETest

namespace ETest

open Commons.NumberTheory.DirichletCharacter

lemma diffOn_cpow_neg (n : ℕ) {U : Set ℂ} :
    DifferentiableOn ℂ (fun w : ℂ => aa n * (n:ℂ)^(-w)) U := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    refine DifferentiableOn.congr (differentiableOn_const (c := (0:ℂ))) (fun w _ => ?_)
    simp [aa_zero]
  · have hnne : (n:ℂ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
    have heq : (fun w : ℂ => aa n * (n:ℂ)^(-w))
        = fun w => aa n * Complex.exp (Complex.log (n:ℂ) * (-w)) := by
      funext w; rw [Complex.cpow_def_of_ne_zero hnne]
    rw [heq]; fun_prop

lemma analyticOnNhd_Dser_one : AnalyticOnNhd ℂ Dser {w : ℂ | 1 < w.re} := by
  intro z hz
  simp only [Set.mem_setOf_eq] at hz
  set σ0 : ℝ := (1 + z.re)/2 with hσ0
  have hσ0gt1 : 1 < σ0 := by rw [hσ0]; linarith
  have hεpos : 0 < σ0 - 1 := by linarith
  have hsum : Summable (fun n : ℕ => (n:ℝ)^(-σ0)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have hdiff : DifferentiableOn ℂ Dser (Metric.ball z (σ0 - 1)) := by
    apply Complex.differentiableOn_tsum_of_summable_norm (ι := ℕ) (U := Metric.ball z (σ0-1))
      (F := fun n w => aa n * (n:ℂ)^(-w)) (u := fun n => (n:ℝ)^(-σ0))
    · exact hsum
    · intro n; exact diffOn_cpow_neg n
    · exact Metric.isOpen_ball
    · intro n w hw
      rcases Nat.eq_zero_or_pos n with hn | hn
      · subst hn; simp only [aa_zero, zero_mul, norm_zero]; positivity
      · rw [norm_mul, Complex.norm_natCast_cpow_of_pos hn]
        have hwr : σ0 < w.re := by
          have hb : ‖w - z‖ < σ0 - 1 := by rwa [Metric.mem_ball, dist_eq_norm] at hw
          have h1 : -‖w - z‖ ≤ (w - z).re := (abs_le.mp (Complex.abs_re_le_norm (w - z))).1
          rw [Complex.sub_re] at h1; linarith
        calc ‖aa n‖ * (n:ℝ)^(-w.re) ≤ 1 * (n:ℝ)^(-w.re) :=
              mul_le_mul_of_nonneg_right (norm_aa_le_one n) (Real.rpow_nonneg (Nat.cast_nonneg n) _)
          _ = (n:ℝ)^(-w.re) := one_mul _
          _ ≤ (n:ℝ)^(-σ0) := Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) (by linarith)
  exact hdiff.analyticAt (Metric.ball_mem_nhds z hεpos)

end ETest

namespace ETest

open Commons.NumberTheory.DirichletCharacter

lemma isPreconnected_half : IsPreconnected {w : ℂ | 1 < w.re} := by
  apply Convex.isPreconnected
  intro x hx y hy a b ha hb hab
  simp only [Set.mem_setOf_eq] at hx hy ⊢
  have h1 : (a • x + b • y).re = a * x.re + b * y.re := by
    rw [Complex.add_re, Complex.smul_re, Complex.smul_re, smul_eq_mul, smul_eq_mul]
  rw [h1]
  rcases eq_or_lt_of_le ha with ha0 | hapos
  · rw [← ha0, zero_mul, zero_add]
    have hb1 : b = 1 := by linarith
    rw [hb1, one_mul]; exact hy
  · have hax : a * 1 < a * x.re := mul_lt_mul_of_pos_left hx hapos
    have hby : b * 1 ≤ b * y.re := mul_le_mul_of_nonneg_left (le_of_lt hy) hb
    nlinarith [hax, hby, hab]

lemma H0_identity {δ : ℝ} (hδ : 0 < δ) (hδ4 : δ ≤ Real.log 2 / 4)
    (hzf : ∀ σ t : ℝ, 1 - δ / Real.log (2 + |t|) ≤ σ →
      riemannZeta ((σ:ℂ) + (t:ℂ) * Complex.I) ≠ 0)
    (hcf : ∀ σ t : ℝ, 1 - δ / Real.log (2 + |t|) ≤ σ →
      DirichletCharacter.LFunction chi4 ((σ:ℂ) + (t:ℂ) * Complex.I) ≠ 0)
    (H0 : ℂ → ℂ) (hH0an : AnalyticOnNhd ℂ H0 (oreg δ)) (hH0sq : ∀ s, H0 s ^ 2 = Gfun s) :
    ∃ H : ℂ → ℂ, AnalyticOnNhd ℂ H (oreg δ) ∧ (∀ s, H s ^ 2 = Gfun s) ∧
      (∀ s : ℂ, 1 < s.re → H s * (s - 1) ^ (-(1/2 : ℂ)) = Dser s) := by
  set H : ℂ → ℂ := if H0 2 = Dser 2 then H0 else -H0 with hHdef
  have hHan : AnalyticOnNhd ℂ H (oreg δ) := by
    by_cases h : H0 2 = Dser 2
    · rw [hHdef]; simp only [h, if_true]; exact hH0an
    · rw [hHdef]; simp only [h, if_false]; exact hH0an.neg
  have hHsq : ∀ s, H s ^ 2 = Gfun s := by
    intro s
    by_cases h : H0 2 = Dser 2
    · rw [hHdef]; simp only [h, if_true]; exact hH0sq s
    · rw [hHdef]; simp only [h, if_false]
      show ((-H0) s) ^ 2 = Gfun s
      rw [Pi.neg_apply, neg_sq]; exact hH0sq s
  refine ⟨H, hHan, hHsq, ?_⟩
  intro s hs
  have hHan' : AnalyticOnNhd ℂ H {w : ℂ | 1 < w.re} := hHan.mono (fun w hw => by
    simp only [Set.mem_setOf_eq] at hw ⊢
    rw [oreg]; simp only [Set.mem_ofPred_eq]
    have hlogpos : 0 < Real.log (2 + |w.im|) := Real.log_pos (by linarith [abs_nonneg w.im])
    have hd : 0 < δ / Real.log (2 + |w.im|) := div_pos hδ hlogpos
    linarith)
  set K : ℂ → ℂ := fun w => (w - 1) ^ (1/2 : ℂ) * Dser w with hKdef
  have hKan : AnalyticOnNhd ℂ K {w : ℂ | 1 < w.re} := by
    rw [hKdef]
    apply AnalyticOnNhd.mul
    · apply AnalyticOnNhd.cpow
      · exact analyticOnNhd_id.sub analyticOnNhd_const
      · exact analyticOnNhd_const
      · intro w hw
        simp only [Set.mem_setOf_eq] at hw
        rw [Complex.mem_slitPlane_iff]; left
        simp only [Complex.sub_re, Complex.one_re]; linarith
    · exact analyticOnNhd_Dser_one
  have hK2 : K 2 = Dser 2 := by
    rw [hKdef]
    show (2 - 1) ^ (1/2:ℂ) * Dser 2 = Dser 2
    rw [show (2:ℂ) - 1 = 1 by norm_num, Complex.one_cpow, one_mul]
  have hH2 : H 2 = Dser 2 := by
    by_cases h : H0 2 = Dser 2
    · rw [hHdef]; simp only [h, if_true]
    · rw [hHdef]; simp only [h, if_false]
      show -H0 2 = Dser 2
      have hsq : H0 2 ^ 2 = Dser 2 ^ 2 := by
        rw [hH0sq 2, Gfun_eq 2 (by norm_num : (1:ℝ) < (2:ℂ).re)]; ring
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h' | h'
      · exact absurd h' h
      · rw [h']; ring
  have hnhds : {w : ℂ | 1 < w.re} ∈ 𝓝 (2:ℂ) :=
    IsOpen.mem_nhds (isOpen_lt continuous_const continuous_re) (by norm_num)
  have hev : H =ᶠ[𝓝 (2:ℂ)] K := by
    have hprod : ∀ᶠ w in 𝓝 (2:ℂ), (H w - K w) * (H w + K w) = 0 := by
      filter_upwards [hnhds] with w hw
      have hwk : H w ^ 2 = K w ^ 2 := by
        have hw1 : w - 1 ≠ 0 := fun h => by rw [sub_eq_zero] at h; rw [h] at hw; norm_num at hw
        have hsq1 : ((w - 1)^(1/2:ℂ))^2 = (w - 1) := by
          rw [sq, ← Complex.cpow_add _ _ hw1, show (1/2:ℂ)+(1/2:ℂ) = 1 by norm_num, Complex.cpow_one]
        rw [hHsq w, Gfun_eq w hw, hKdef, mul_pow, hsq1]
      have h2 : (H w - K w) * (H w + K w) = H w ^ 2 - K w ^ 2 := by ring
      rw [h2, hwk]; ring
    have hne : ∀ᶠ w in 𝓝 (2:ℂ), H w + K w ≠ 0 := by
      have hc : ContinuousAt (fun w => H w + K w) 2 :=
        (hHan' 2 (by norm_num)).continuousAt.add (hKan 2 (by norm_num)).continuousAt
      refine hc.eventually_ne ?_
      rw [hH2, hK2]
      have ht := mul_ne_zero two_ne_zero (Dser_ne_zero 2 (by norm_num))
      intro hcon
      exact ht (by rwa [← two_mul] at hcon)
    filter_upwards [hprod, hne] with w hp hn
    have h' : H w - K w = 0 := by
      rcases mul_eq_zero.mp hp with hh | hh
      · exact hh
      · exact absurd hh hn
    exact sub_eq_zero.mp h'
  have heq := AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq hHan' hKan isPreconnected_half
    (by norm_num : (2:ℂ) ∈ {w : ℂ | 1 < w.re}) hev
  have hHK : H s = K s := heq hs
  have hsne : s - 1 ≠ 0 := fun h => by rw [sub_eq_zero] at h; rw [h] at hs; norm_num at hs
  rw [hHK, hKdef]
  show (s - 1) ^ (1/2:ℂ) * Dser s * (s - 1) ^ (-(1/2:ℂ)) = Dser s
  rw [show (s - 1)^(1/2:ℂ) * Dser s * (s - 1)^(-(1/2:ℂ)) = ((s-1)^(1/2:ℂ) * (s-1)^(-(1/2:ℂ))) * Dser s from by ring,
    ← Complex.cpow_add _ _ hsne, show (1/2:ℂ) + -(1/2:ℂ) = 0 by ring, Complex.cpow_zero, one_mul]

end ETest

namespace ETest

lemma isCompact_strip (δ : ℝ) (hδ4 : δ ≤ Real.log 2 / 4) : IsCompact {s : ℂ | |s.im| ≤ 1 ∧ 1 - δ/Real.log 2 ≤ s.re ∧ s.re ≤ 3} := by
  have hclosed : IsClosed {s : ℂ | |s.im| ≤ 1 ∧ 1 - δ/Real.log 2 ≤ s.re ∧ s.re ≤ 3} := by
    rw [show {s : ℂ | |s.im| ≤ 1 ∧ 1 - δ/Real.log 2 ≤ s.re ∧ s.re ≤ 3}
        = (fun s : ℂ => |s.im|) ⁻¹' (Set.Iic 1) ∩ (fun s : ℂ => s.re) ⁻¹' (Set.Ici (1 - δ/Real.log 2))
          ∩ (fun s : ℂ => s.re) ⁻¹' (Set.Iic 3) by ext s; simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage, Set.mem_Iic, Set.mem_Ici]; tauto]
    exact ((isClosed_Iic.preimage (continuous_abs.comp continuous_im)).inter
      (isClosed_Ici.preimage continuous_re)).inter (isClosed_Iic.preimage continuous_re)
  refine (isCompact_closedBall (0:ℂ) 4).of_isClosed_subset hclosed ?_
  intro s hs
  simp only [Set.mem_ofPred_eq] at hs
  obtain ⟨h1, h2, h3⟩ := hs
  rw [Metric.mem_closedBall, dist_zero_right]
  have hδ0 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl : -(3:ℝ) ≤ 1 - δ / Real.log 2 := by
    have : δ / Real.log 2 ≤ 4 := by rw [div_le_iff₀ hδ0]; nlinarith
    linarith
  calc ‖s‖ ≤ |s.re| + |s.im| := Complex.norm_le_abs_re_add_abs_im s
    _ ≤ 3 + 1 := by
        have hre : |s.re| ≤ 3 := abs_le.mpr ⟨by linarith, h3⟩
        linarith
    _ = 4 := by norm_num

lemma zeta1_growth {δ czε Cζ : ℝ} (hδ : 0 < δ) (hδ4 : δ ≤ Real.log 2/4)
    (hδz : δ ≤ czε) (hCζ : 0 < Cζ)
    (hzb : ∀ σ t : ℝ, 1 ≤ |t| → 1 - czε / Real.log (|t| + 2) ≤ σ →
      ‖riemannZeta ((σ:ℂ) + (t:ℂ) * Complex.I)‖ ≤ Cζ * Real.log (|t| + 2)) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, s ∈ oreg δ →
      ‖riemannZeta₁ s‖ ≤ C * (2 + ‖s‖) * Real.log (2 + ‖s‖) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨M, hM⟩ := (isCompact_strip δ hδ4).exists_bound_of_continuousOn
    (differentiable_riemannZeta₁.continuous.continuousOn)
  set C : ℝ := max Cζ (max (M / (2*Real.log 2)) (2/Real.log 2)) + 1 with hCdef
  have hCpos : 0 < C := by rw [hCdef]; positivity
  refine ⟨C, hCpos, ?_⟩
  intro s hs
  have hsr := oreg_re_bound hδ hs
  have hsre := oreg_re_lt hδ hs
  have hRn : (2:ℝ) ≤ 2 + ‖s‖ := by linarith [norm_nonneg s]
  have hlogge : Real.log 2 ≤ Real.log (2 + ‖s‖) := Real.log_le_log (by norm_num) hRn
  have hA : Cζ ≤ C := by rw [hCdef]; linarith [le_max_left Cζ (max (M/(2*Real.log 2)) (2/Real.log 2))]
  have hB : M ≤ C * (2 + ‖s‖) * Real.log (2 + ‖s‖) := by
    have h2pos : 0 < 2 * Real.log 2 := by positivity
    have h1 : M / (2*Real.log 2) ≤ C := by
      rw [hCdef]; linarith [le_trans (le_max_left (M/(2*Real.log 2)) (2/Real.log 2)) (le_max_right Cζ _)]
    have h1' : M ≤ C * (2 * Real.log 2) := by
      have hh := mul_le_mul_of_nonneg_right h1 h2pos.le
      rwa [div_mul_cancel₀ M (ne_of_gt h2pos)] at hh
    have h3 : 2 * Real.log 2 ≤ (2 + ‖s‖) * Real.log (2 + ‖s‖) :=
      mul_le_mul hRn hlogge (Real.log_pos (by norm_num)).le (by linarith)
    nlinarith [h1', h3, hCpos]
  have hC2 : (3/2:ℝ) ≤ C * Real.log (2 + ‖s‖) := by
    have h1 : 2/Real.log 2 ≤ C := by
      rw [hCdef]; linarith [le_trans (le_max_right (M/(2*Real.log 2)) (2/Real.log 2)) (le_max_right Cζ _)]
    have h1' : (2:ℝ) ≤ C * Real.log 2 := by
      have hh := mul_le_mul_of_nonneg_right h1 hlog2.le
      rwa [div_mul_cancel₀ 2 (ne_of_gt hlog2)] at hh
    nlinarith [h1', hlogge, hCpos]
  by_cases him : 1 ≤ |s.im|
  · have hδz' : 1 - czε / Real.log (|s.im| + 2) ≤ s.re := by
      have h1 : 1 - δ / Real.log (2 + |s.im|) < s.re := oreg_lt hs
      have h2 : δ / Real.log (2 + |s.im|) ≤ czε / Real.log (|s.im| + 2) := by
        rw [show (2 + |s.im|) = (|s.im| + 2) by ring]
        exact div_le_div_of_nonneg_right hδz (Real.log_pos (by linarith [abs_nonneg s.im])).le
      linarith
    have hb := hzb s.re s.im him hδz'
    rw [Complex.re_add_im s] at hb
    have hsne : s ≠ 1 := by
      intro h; rw [h] at him; simp only [Complex.one_im, abs_zero] at him; linarith
    have hz1 : riemannZeta₁ s = (s - 1) * riemannZeta s := by
      rw [riemannZeta_eq_inv_sub_mul hsne, ← mul_assoc, mul_inv_cancel₀ (sub_ne_zero.mpr hsne), one_mul]
    rw [hz1, norm_mul]
    have h1 : ‖s - 1‖ ≤ 2 + ‖s‖ := by
      calc ‖s - 1‖ ≤ ‖s‖ + ‖(1:ℂ)‖ := norm_sub_le s 1
        _ = ‖s‖ + 1 := by rw [norm_one]
        _ ≤ 2 + ‖s‖ := by linarith
    have h2 : Real.log (|s.im| + 2) ≤ Real.log (2 + ‖s‖) := by
      apply Real.log_le_log (by linarith [abs_nonneg s.im])
      have := Complex.abs_im_le_norm s; linarith
    calc ‖s - 1‖ * ‖riemannZeta s‖
        ≤ (2 + ‖s‖) * (Cζ * Real.log (|s.im| + 2)) :=
          mul_le_mul h1 hb (by positivity) (by linarith [norm_nonneg s])
      _ ≤ (2 + ‖s‖) * (Cζ * Real.log (2 + ‖s‖)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 hCζ.le) (by linarith [norm_nonneg s])
      _ = Cζ * ((2 + ‖s‖) * Real.log (2 + ‖s‖)) := by ring
      _ ≤ C * ((2 + ‖s‖) * Real.log (2 + ‖s‖)) :=
          mul_le_mul_of_nonneg_right hA (mul_nonneg (by linarith [norm_nonneg s]) (Real.log_nonneg (by linarith [norm_nonneg s])))
      _ = C * (2 + ‖s‖) * Real.log (2 + ‖s‖) := by ring
  · push_neg at him
    by_cases hre : s.re ≤ 3
    · have hsK : s ∈ {s : ℂ | |s.im| ≤ 1 ∧ 1 - δ/Real.log 2 ≤ s.re ∧ s.re ≤ 3} :=
        ⟨le_of_lt him, le_of_lt hsre, hre⟩
      exact le_trans (hM s hsK) hB
    · push_neg at hre
      have hsne : s ≠ 1 := by intro h; rw [h] at hre; norm_num at hre
      have hz1 : riemannZeta₁ s = (s - 1) * riemannZeta s := by
        rw [riemannZeta_eq_inv_sub_mul hsne, ← mul_assoc, mul_inv_cancel₀ (sub_ne_zero.mpr hsne), one_mul]
      rw [hz1, norm_mul]
      have h1 : ‖s - 1‖ ≤ 2 + ‖s‖ := by
        calc ‖s - 1‖ ≤ ‖s‖ + ‖(1:ℂ)‖ := norm_sub_le s 1
          _ = ‖s‖ + 1 := by rw [norm_one]
          _ ≤ 2 + ‖s‖ := by linarith
      have hzbound : ‖riemannZeta s‖ ≤ 3/2 := by
        have h1 := Commons.NumberTheory.Zeta.norm_riemannZeta_le_tsum s (by linarith)
        have h2 := Commons.NumberTheory.LSeries.tsum_nat_rpow_neg_le_inv s.re (by linarith)
        have h3 : 1 / (s.re - 1) ≤ 1/2 := by rw [div_le_iff₀ (by linarith)]; linarith
        linarith [h1, h2, h3]
      calc ‖s - 1‖ * ‖riemannZeta s‖ ≤ (2 + ‖s‖) * (3/2) :=
            mul_le_mul h1 hzbound (norm_nonneg _) (by linarith [norm_nonneg s])
        _ = (3/2) * (2 + ‖s‖) := by ring
        _ ≤ (C * Real.log (2 + ‖s‖)) * (2 + ‖s‖) :=
            mul_le_mul_of_nonneg_right hC2 (by linarith [norm_nonneg s])
        _ = C * (2 + ‖s‖) * Real.log (2 + ‖s‖) := by ring

end ETest
namespace ETest

lemma tsum_shift_inv_sq : (∑' n : ℕ, ((n:ℝ)+2)^(-(2:ℝ))) = (∑' n : ℕ, ((n:ℝ)+1)^(-(2:ℝ))) - 1 := by
  have hsumm : Summable (fun n : ℕ => ((n:ℝ)+1)^(-(2:ℝ))) := by
    have h := (Real.summable_nat_rpow (p := (-2:ℝ))).mpr (by norm_num)
    have h2 := (summable_nat_add_iff (f := fun n : ℕ => (n:ℝ)^(-(2:ℝ))) 1).mpr h
    refine h2.congr (fun n => ?_); push_cast; ring_nf
  rw [Summable.tsum_eq_zero_add hsumm]
  have h0 : ((0:ℕ):ℝ) + 1 = 1 := by norm_num
  have : (∑' n : ℕ, (((n + 1 : ℕ):ℝ) + 1)^(-(2:ℝ))) = ∑' n : ℕ, ((n:ℝ)+2)^(-(2:ℝ)) := by
    apply tsum_congr; intro n; congr 1; push_cast; ring_nf
  rw [h0, this]; norm_num

lemma zeta_lower_bound_two : ∃ C : ℝ, 0 < C ∧ ∀ w : ℂ, 2 ≤ w.re → C ≤ ‖riemannZeta w‖ := by
  have hkey : (∑' n : ℕ, ((n:ℝ)+1)^(-(2:ℝ))) = (Real.pi)^2/6 := by
    have h := zeta_eq_tsum_one_div_nat_add_one_cpow (s := (2:ℂ)) (by norm_num)
    rw [riemannZeta_two] at h
    have hconv : (∑' n : ℕ, 1/((n:ℂ)+1)^(2:ℂ)) = ∑' n : ℕ, ((n:ℂ)+1)^(-(2:ℂ)) := by
      apply tsum_congr; intro n; rw [Complex.cpow_neg, one_div]
    have hreal : (∑' n : ℕ, ((n:ℂ)+1)^(-(2:ℂ)))
        = (((∑' n : ℕ, ((n:ℝ)+1)^(-(2:ℝ))) : ℝ) : ℂ) := by
      rw [Complex.ofReal_tsum]
      apply tsum_congr; intro n
      rw [show ((n:ℂ)+1) = ((((n:ℝ)+1) : ℝ) : ℂ) by push_cast; ring]
      rw [Complex.ofReal_cpow (by positivity) (-(2:ℝ))]; push_cast; ring
    rw [hconv, hreal] at h
    have hc : ((↑Real.pi : ℂ)^2/6) = (Real.pi^2/6 : ℂ) := by push_cast; ring
    have hre := congrArg Complex.re h
    rw [Complex.ofReal_re] at hre
    have hL : ((↑Real.pi:ℂ)^2/6).re = Real.pi^2/6 := by
      rw [← Complex.ofReal_pow, show (6:ℂ) = ↑(6:ℝ) by norm_num, ← Complex.ofReal_div, Complex.ofReal_re]
    rw [hL] at hre
    exact hre.symm
  have hle : (Real.pi)^2/6 - 1 ≤ 3/4 := by nlinarith [Real.pi_gt_three, Real.pi_lt_d4]
  refine ⟨1/4, by norm_num, ?_⟩
  intro w hw
  have h1 : (1:ℝ) < w.re := by linarith
  have hζ := zeta_eq_tsum_one_div_nat_add_one_cpow h1
  have hsumm : Summable (fun n : ℕ => 1/((n:ℂ)+1)^w) := by
    have h := (Complex.summable_one_div_nat_cpow (p := w)).mpr h1
    have h2 := (summable_nat_add_iff (f := fun n : ℕ => 1/((n:ℂ))^w) 1).mpr h
    refine h2.congr (fun n => by push_cast; ring)
  have hsplit : (∑' n : ℕ, 1/((n:ℂ)+1)^w) = 1 + ∑' n : ℕ, 1/((n:ℂ)+2)^w := by
    rw [Summable.tsum_eq_zero_add hsumm]
    congr 1
    · norm_num
    · apply tsum_congr; intro n; congr 1; push_cast; ring
  have hsumm2 : Summable (fun n : ℕ => 1/((n:ℂ)+2)^w) := by
    have h := (Complex.summable_one_div_nat_cpow (p := w)).mpr h1
    have h2 := (summable_nat_add_iff (f := fun n : ℕ => 1/((n:ℂ))^w) 2).mpr h
    refine h2.congr (fun n => by push_cast; ring)
  have hsumm3 : Summable (fun n : ℕ => ((n:ℝ)+2)^(-w.re)) := by
    have h := (Real.summable_nat_rpow (p := (-w.re))).mpr (by linarith)
    have h2 := (summable_nat_add_iff (f := fun n : ℕ => (n:ℝ)^(-w.re)) 2).mpr h
    exact h2.congr (fun n => by push_cast; ring)
  have htail : ‖∑' n : ℕ, 1/((n:ℂ)+2)^w‖ ≤ 3/4 := by
    calc ‖∑' n : ℕ, 1/((n:ℂ)+2)^w‖ ≤ ∑' n : ℕ, ‖1/((n:ℂ)+2)^w‖ :=
          norm_tsum_le_tsum_norm (hsumm2.norm)
      _ = ∑' n : ℕ, ((n:ℝ)+2)^(-w.re) := by
          apply tsum_congr; intro n
          rw [norm_div, norm_one, one_div,
            show ((↑n:ℂ)+2) = ((((n:ℝ)+2 : ℝ)):ℂ) by push_cast; ring,
            Complex.norm_cpow_eq_rpow_re_of_pos (by positivity : (0:ℝ) < (n:ℝ)+2),
            Real.rpow_neg (by positivity : (0:ℝ) ≤ (n:ℝ)+2)]
      _ ≤ ∑' n : ℕ, ((n:ℝ)+2)^(-(2:ℝ)) := by
          have hR : Summable (fun n : ℕ => ((n:ℝ)+2)^(-(2:ℝ))) := by
            have h := (Real.summable_nat_rpow (p := (-2:ℝ))).mpr (by norm_num)
            exact ((summable_nat_add_iff (f := fun n : ℕ => (n:ℝ)^(-(2:ℝ))) 2).mpr h).congr (fun n => by norm_num)
          apply Summable.tsum_le_tsum _ hsumm3 hR
          intro n
          gcongr
          linarith
      _ ≤ 3/4 := by rw [tsum_shift_inv_sq]; linarith [hkey, hle]
  rw [hζ, hsplit]
  have h5 : (1:ℝ) - ‖∑' n : ℕ, 1/((n:ℂ)+2)^w‖ ≤ ‖1 + ∑' n : ℕ, 1/((n:ℂ)+2)^w‖ := by
    have h := (abs_le.mp (abs_norm_sub_norm_le (1:ℂ) (-(∑' n : ℕ, 1/((n:ℂ)+2)^w)))).2
    rw [norm_one, norm_neg, sub_neg_eq_add] at h; linarith
  linarith [h5, htail]

end ETest
namespace ETest

open Commons.NumberTheory.DirichletCharacter

lemma L_growth {δ cL CL : ℝ} (hδ : 0 < δ) (hδ4 : δ ≤ Real.log 2/4) (hδL : δ ≤ cL) (hCL : 0 < CL)
    (hLb : ∀ σ t : ℝ, 1 ≤ |t| → 1 - cL / Real.log (|t| + 2) ≤ σ →
      ‖DirichletCharacter.LFunction chi4 ((σ:ℂ) + (t:ℂ) * Complex.I)‖ ≤ CL * Real.log (|t| + 2)) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, s ∈ oreg δ →
      ‖DirichletCharacter.LFunction chi4 s‖ ≤ C * Real.log (2 + ‖s‖) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨M, hM⟩ := (isCompact_strip δ hδ4).exists_bound_of_continuousOn
    ((DirichletCharacter.differentiable_LFunction Commons.NumberTheory.LSeries.chi4_ne_one).continuous.continuousOn)
  set C : ℝ := max (max (M/Real.log 2) (2/Real.log 2)) (max CL 1) + 1 with hCdef
  have hCpos : 0 < C := by rw [hCdef]; positivity
  refine ⟨C, hCpos, ?_⟩
  intro s hs
  have hsre := oreg_re_lt hδ hs
  have hlogpos : 0 < Real.log (2 + ‖s‖) := Real.log_pos (by linarith [norm_nonneg s])
  have hlogge : Real.log 2 ≤ Real.log (2 + ‖s‖) := Real.log_le_log (by norm_num) (by linarith [norm_nonneg s])
  have hMle : M ≤ C * Real.log (2 + ‖s‖) := by
    have h1 : M/Real.log 2 ≤ C := by
      rw [hCdef]; linarith [le_trans (le_max_left (M/Real.log 2) (2/Real.log 2)) (le_max_left (max (M/Real.log 2) (2/Real.log 2)) (max CL 1))]
    calc M = (M/Real.log 2) * Real.log 2 := (div_mul_cancel₀ M (ne_of_gt hlog2)).symm
      _ ≤ C * Real.log (2 + ‖s‖) := mul_le_mul h1 hlogge hlog2.le hCpos.le
  have h2le : (2:ℝ) ≤ C * Real.log (2 + ‖s‖) := by
    have h1 : 2/Real.log 2 ≤ C := by
      rw [hCdef]; linarith [le_trans (le_max_right (M/Real.log 2) (2/Real.log 2)) (le_max_left (max (M/Real.log 2) (2/Real.log 2)) (max CL 1))]
    calc (2:ℝ) = (2/Real.log 2) * Real.log 2 := (div_mul_cancel₀ 2 (ne_of_gt hlog2)).symm
      _ ≤ C * Real.log (2 + ‖s‖) := mul_le_mul h1 hlogge hlog2.le hCpos.le
  have hCLle : CL ≤ C := by
    rw [hCdef]; linarith [le_trans (le_max_left CL 1) (le_max_right (max (M/Real.log 2) (2/Real.log 2)) (max CL 1))]
  by_cases him : 1 ≤ |s.im|
  · have hδL' : 1 - cL / Real.log (|s.im| + 2) ≤ s.re := by
      rw [show (|s.im| + 2) = (2 + |s.im|) by ring]
      have h1 := oreg_lt hs
      have h2 : δ / Real.log (2 + |s.im|) ≤ cL / Real.log (2 + |s.im|) :=
        div_le_div_of_nonneg_right hδL (Real.log_pos (by linarith [abs_nonneg s.im])).le
      linarith
    have hb := hLb s.re s.im him hδL'
    rw [Complex.re_add_im s] at hb
    have hle : Real.log (|s.im| + 2) ≤ Real.log (2 + ‖s‖) := by
      apply Real.log_le_log (by linarith [abs_nonneg s.im])
      have := Complex.abs_im_le_norm s; linarith
    calc ‖DirichletCharacter.LFunction chi4 s‖ ≤ CL * Real.log (|s.im| + 2) := hb
      _ ≤ CL * Real.log (2 + ‖s‖) := mul_le_mul_of_nonneg_left hle hCL.le
      _ ≤ C * Real.log (2 + ‖s‖) := mul_le_mul_of_nonneg_right hCLle hlogpos.le
  · push_neg at him
    by_cases hre : s.re ≤ 2
    · have hsK : s ∈ {s : ℂ | |s.im| ≤ 1 ∧ 1 - δ/Real.log 2 ≤ s.re ∧ s.re ≤ 3} :=
        ⟨le_of_lt him, le_of_lt hsre, by linarith⟩
      exact le_trans (hM s hsK) hMle
    · push_neg at hre
      exact le_trans (LFunction_norm_le_two_of_two_le_re chi4 s (by linarith)) h2le

lemma inv_zeta_two_growth {δ cinv Cinv : ℝ} (hδ : 0 < δ) (hδ4 : δ ≤ Real.log 2/4)
    (hCinv : 0 < Cinv) (hcinv : 0 ≤ cinv)
    (hzinv : ∀ σ t : ℝ, 1 - cinv / Real.log (|t| + 2) ≤ σ → σ ≤ 2 →
      1 / ‖riemannZeta ((σ:ℂ) + (t:ℂ) * Complex.I)‖ ≤ Cinv * (Real.log (|t| + 2) + 1)) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, s ∈ oreg δ →
      ‖(riemannZeta (2*s))⁻¹‖ ≤ C * Real.log (2 + ‖s‖) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨C0, hC0pos, hC0⟩ := zeta_lower_bound_two
  set C : ℝ := max (max (1/(C0*Real.log 2)) (Cinv * (2 + 1/Real.log 2))) 1 + 1 with hCdef
  have hCpos : 0 < C := by rw [hCdef]; positivity
  have hC1 : 1/(C0*Real.log 2) ≤ C := by
    rw [hCdef]; linarith [le_trans (le_max_left (1/(C0*Real.log 2)) (Cinv*(2+1/Real.log 2))) (le_max_left (max (1/(C0*Real.log 2)) (Cinv*(2+1/Real.log 2))) 1)]
  have hC2 : Cinv * (2 + 1/Real.log 2) ≤ C := by
    rw [hCdef]; linarith [le_trans (le_max_right (1/(C0*Real.log 2)) (Cinv*(2+1/Real.log 2))) (le_max_left (max (1/(C0*Real.log 2)) (Cinv*(2+1/Real.log 2))) 1)]
  refine ⟨C, hCpos, fun s hs => ?_⟩
  have hlogpos : 0 < Real.log (2 + ‖s‖) := Real.log_pos (by linarith [norm_nonneg s])
  have hlogge : Real.log 2 ≤ Real.log (2 + ‖s‖) := Real.log_le_log (by norm_num) (by linarith [norm_nonneg s])
  rw [norm_inv, ← one_div]
  by_cases hre : s.re ≤ 1
  · have hσ : 1 - cinv / Real.log (|(2*s).im| + 2) ≤ (2*s).re := by
      rw [two_mul_re]
      have h1 : 1 - δ / Real.log (2 + |s.im|) < s.re := oreg_lt hs
      have h2 : 2 * (δ / Real.log (2 + |s.im|)) ≤ 1/2 := by
        have hlogp : 0 < Real.log (2 + |s.im|) := Real.log_pos (by linarith [abs_nonneg s.im])
        have hq : δ / Real.log (2 + |s.im|) ≤ 1/4 := by
          rw [div_le_iff₀ hlogp]
          have h3 := Real.log_le_log (by norm_num) (by linarith [abs_nonneg s.im] : (2:ℝ) ≤ 2 + |s.im|)
          linarith [h3, hlog2, hδ4]
        linarith
      have h4 : 1 - cinv / Real.log (|(2*s).im| + 2) ≤ 1 := by
        have hlog : 0 < Real.log (|(2*s).im| + 2) :=
          Real.log_pos (by linarith [abs_nonneg (2*s).im])
        have hnn := div_nonneg hcinv hlog.le
        linarith
      have h3 : (3:ℝ)/2 < 2 * s.re := by linarith
      linarith
    have hσ2 : (2*s).re ≤ 2 := by rw [two_mul_re]; linarith
    have hb := hzinv (2*s).re (2*s).im hσ hσ2
    rw [Complex.re_add_im] at hb
    have hle : Real.log (|(2*s).im| + 2) ≤ 2 * Real.log (2 + ‖s‖) := by
      have h1 : |(2*s).im| ≤ 2 * ‖s‖ := by
        rw [two_mul_im]
        calc |2 * s.im| = 2 * |s.im| := by rw [abs_mul]; norm_num
          _ ≤ 2 * ‖s‖ := by linarith [Complex.abs_im_le_norm s]
      have h2 : (|(2*s).im| + 2 : ℝ) ≤ 2 * (2 + ‖s‖) := by nlinarith [h1, norm_nonneg s]
      calc Real.log (|(2*s).im| + 2) ≤ Real.log (2 * (2 + ‖s‖)) := by
            apply Real.log_le_log (by linarith [abs_nonneg (2*s).im]); linarith
        _ = Real.log 2 + Real.log (2 + ‖s‖) := Real.log_mul (by norm_num) (by linarith [norm_nonneg s])
        _ ≤ 2 * Real.log (2 + ‖s‖) := by linarith [hlogge]
    calc 1 / ‖riemannZeta (2*s)‖ ≤ Cinv * (Real.log (|(2*s).im| + 2) + 1) := hb
      _ ≤ Cinv * (2 * Real.log (2 + ‖s‖) + 1) := by
          apply mul_le_mul_of_nonneg_left _ hCinv.le; linarith
      _ ≤ (Cinv * (2 + 1/Real.log 2)) * Real.log (2 + ‖s‖) := by
          have hL2 : Real.log (2 + ‖s‖) / Real.log 2 = (1/Real.log 2) * Real.log (2 + ‖s‖) := by ring
          have h3 : 2 * Real.log (2 + ‖s‖) + 1 ≤ 2 * Real.log (2 + ‖s‖) + (1/Real.log 2) * Real.log (2 + ‖s‖) := by
            rw [← hL2]
            have := div_le_div_of_nonneg_right hlogge hlog2.le
            rw [div_self (ne_of_gt hlog2)] at this
            linarith [this]
          rw [show (Cinv * (2 + 1/Real.log 2)) * Real.log (2 + ‖s‖) = Cinv * (2 * Real.log (2 + ‖s‖) + (1/Real.log 2) * Real.log (2 + ‖s‖)) by ring]
          exact mul_le_mul_of_nonneg_left h3 hCinv.le
      _ ≤ C * Real.log (2 + ‖s‖) := mul_le_mul_of_nonneg_right hC2 hlogpos.le
  · push_neg at hre
    have h2sre : 2 ≤ (2*s).re := by rw [two_mul_re]; linarith
    have hb := hC0 (2*s) h2sre
    have hb' : 1 / ‖riemannZeta (2*s)‖ ≤ 1/C0 :=
      one_div_le_one_div_of_le hC0pos hb
    calc 1 / ‖riemannZeta (2*s)‖ ≤ 1/C0 := hb'
      _ = (1/(C0*Real.log 2)) * Real.log 2 := by field_simp
      _ ≤ C * Real.log 2 := mul_le_mul_of_nonneg_right hC1 hlog2.le
      _ ≤ C * Real.log (2 + ‖s‖) := mul_le_mul_of_nonneg_left hlogge hCpos.le

end ETest


/-! ## Assembly of the main theorem -/

namespace Commons.NumberTheory.Diophantine

open ETest
open Commons.NumberTheory.DirichletCharacter
open scoped BigOperators Topology
open Filter

noncomputable section

/-- The real series underlying the `3`-mod-`4`-free Dirichlet series at real arguments. -/
noncomputable def realsum4 (σ : ℝ) : ℝ :=
  ∑' n : ℕ, (Set.indicator {n : ℕ | ∀ p : ℕ, p.Prime → p % 4 = 3 → ¬ p ∣ n}
    (fun _ => (1 : ℝ)) n) * (n : ℝ) ^ (-σ)

lemma threeModFourSeries_eq_Dser (s : ℂ) : threeModFourSeries s = ETest.Dser s := rfl

/-- `(1 - 2^{-s})⁻¹` is bounded on the region. -/
lemma inv_one_sub_two_cpow_bdd {δ : ℝ} (hδ : 0 < δ) (hδ4 : δ ≤ Real.log 2 / 4) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, s ∈ oreg δ → ‖(1 - (2 : ℂ) ^ (-s))⁻¹‖ ≤ C := by
  have hlt : (2 : ℝ) ^ (-(1 / 2 : ℝ)) < 1 := by
    have h := Real.rpow_lt_rpow_of_exponent_lt (show (1 : ℝ) < 2 by norm_num)
      (show (-(1 / 2 : ℝ)) < 0 by norm_num)
    rwa [Real.rpow_zero] at h
  refine ⟨(1 - (2 : ℝ) ^ (-(1 / 2 : ℝ)))⁻¹, inv_pos.mpr (by linarith), ?_⟩
  intro s hs
  have hre : (1 / 2 : ℝ) < s.re := oreg_re_pos hδ4 hs
  have hnorm : ‖(2 : ℂ) ^ (-s)‖ = (2 : ℝ) ^ (-s.re) := by
    have h := Complex.norm_cpow_eq_rpow_re_of_pos (x := 2) (by norm_num) (-s)
    rw [Complex.neg_re] at h
    simpa [Complex.ofReal_ofNat] using h
  have hlt2 : ‖(2 : ℂ) ^ (-s)‖ < (2 : ℝ) ^ (-(1 / 2 : ℝ)) := by
    rw [hnorm]
    exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith)
  have habs : 1 - (2 : ℝ) ^ (-(1 / 2 : ℝ)) ≤ ‖1 - (2 : ℂ) ^ (-s)‖ := by
    have h1 : ‖(1 : ℂ)‖ = 1 := norm_one
    have h2 := abs_norm_sub_norm_le (1 : ℂ) ((2 : ℂ) ^ (-s))
    rw [h1] at h2
    have h3 : (0 : ℝ) ≤ 1 - ‖(2 : ℂ) ^ (-s)‖ := by
      have : ‖(2 : ℂ) ^ (-s)‖ < 1 := lt_trans hlt2 hlt
      linarith
    rw [abs_of_nonneg h3] at h2
    linarith
  rw [norm_inv]
  exact inv_anti₀ (by linarith) habs

/-- `Dser (2s)` is bounded on the region. -/
lemma Dser_two_bdd {δ : ℝ} (hδ : 0 < δ) (hδ4 : δ ≤ Real.log 2 / 4) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, s ∈ oreg δ → ‖Dser (2 * s)‖ ≤ C := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hδlog : δ / Real.log 2 ≤ 1 / 4 := by
    rw [div_le_iff₀ hlog2]; linarith
  set σ0 : ℝ := 1 - δ / Real.log 2 with hσ0
  have hσ0ge : (3 : ℝ) / 4 ≤ σ0 := by rw [hσ0]; linarith
  have h2σ : (1 : ℝ) < 2 * σ0 := by linarith
  have hsumm0 : Summable (fun n : ℕ => (n : ℝ) ^ (-(2 * σ0))) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have htsum0 : 0 ≤ ∑' n : ℕ, (n : ℝ) ^ (-(2 * σ0)) :=
    tsum_nonneg (fun n : ℕ => Real.rpow_nonneg (Nat.cast_nonneg n) (-(2 * σ0)))
  refine ⟨1 + ∑' n : ℕ, (n : ℝ) ^ (-(2 * σ0)), by linarith, ?_⟩
  intro s hs
  have hsre : σ0 < s.re := by rw [hσ0]; exact oreg_re_lt hδ hs
  have hterm : ∀ n : ℕ, ‖aa n * (n : ℂ) ^ (-(2 * s))‖ ≤ (n : ℝ) ^ (-(2 * σ0)) := by
    intro n
    by_cases hn : n = 0
    · subst hn
      rw [aa_zero, zero_mul, norm_zero]
      exact Real.rpow_nonneg (Nat.cast_nonneg 0) _
    · have hnp : 0 < n := Nat.pos_of_ne_zero hn
      rw [norm_mul, Complex.norm_natCast_cpow_of_pos hnp, Complex.neg_re, two_mul_re]
      have h1 : ‖aa n‖ ≤ 1 := norm_aa_le_one n
      calc ‖aa n‖ * (n : ℝ) ^ (-(2 * s.re))
          ≤ 1 * (n : ℝ) ^ (-(2 * s.re)) :=
            mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg (Nat.cast_nonneg n) _)
        _ = (n : ℝ) ^ (-(2 * s.re)) := one_mul _
        _ ≤ (n : ℝ) ^ (-(2 * σ0)) :=
            Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hnp) (by linarith)
  have hf : Summable (fun n : ℕ => ‖aa n * (n : ℂ) ^ (-(2 * s))‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hterm hsumm0
  calc ‖Dser (2 * s)‖ = ‖∑' n : ℕ, aa n * (n : ℂ) ^ (-(2 * s))‖ := rfl
    _ ≤ ∑' n : ℕ, ‖aa n * (n : ℂ) ^ (-(2 * s))‖ := norm_tsum_le_tsum_norm hf
    _ ≤ ∑' n : ℕ, (n : ℝ) ^ (-(2 * σ0)) := Summable.tsum_le_tsum hterm hf hsumm0
    _ ≤ 1 + ∑' n : ℕ, (n : ℝ) ^ (-(2 * σ0)) := by linarith

/-- Bound for `Gfun` on the region. -/
lemma Gfun_growth {δ czε cL cinv Cζ CL Cinv : ℝ} (hδ : 0 < δ) (hδ4 : δ ≤ Real.log 2 / 4)
    (hδz : δ ≤ czε) (hδL : δ ≤ cL) (hδinv : δ ≤ cinv)
    (hCζ : 0 < Cζ) (hCL : 0 < CL) (hCinv : 0 < Cinv) (hcinv : 0 ≤ cinv)
    (hζb : ∀ σ t : ℝ, 1 ≤ |t| → 1 - czε / Real.log (|t| + 2) ≤ σ →
      ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ Cζ * Real.log (|t| + 2))
    (hLb : ∀ σ t : ℝ, 1 ≤ |t| → 1 - cL / Real.log (|t| + 2) ≤ σ →
      ‖DirichletCharacter.LFunction chi4 ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ CL * Real.log (|t| + 2))
    (hzinv : ∀ σ t : ℝ, 1 - cinv / Real.log (|t| + 2) ≤ σ → σ ≤ 2 →
      1 / ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ Cinv * (Real.log (|t| + 2) + 1)) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, s ∈ oreg δ →
      ‖Gfun s‖ ≤ C * (2 + ‖s‖) * (Real.log (2 + ‖s‖)) ^ 3 := by
  obtain ⟨C1, hC1, hb1⟩ := zeta1_growth hδ hδ4 hδz hCζ hζb
  obtain ⟨C2, hC2, hb2⟩ := L_growth hδ hδ4 hδL hCL hLb
  obtain ⟨C4, hC4, hb4⟩ := inv_zeta_two_growth hδ hδ4 hCinv hcinv hzinv
  obtain ⟨C3, hC3, hb3⟩ := inv_one_sub_two_cpow_bdd hδ hδ4
  obtain ⟨C5, hC5, hb5⟩ := Dser_two_bdd hδ hδ4
  refine ⟨C1 * C2 * C3 * C5 * C4, by positivity, ?_⟩
  intro s hs
  have hLp : 0 < Real.log (2 + ‖s‖) := Real.log_pos (by linarith [norm_nonneg s])
  have h2p : 0 < 2 + ‖s‖ := by linarith [norm_nonneg s]
  have e1 := hb1 s hs
  have e2 := hb2 s hs
  have e3 := hb3 s hs
  have e4 := hb4 s hs
  have e5 := hb5 s hs
  have hB1 : 0 ≤ C1 * (2 + ‖s‖) * Real.log (2 + ‖s‖) :=
    mul_nonneg (mul_nonneg hC1.le h2p.le) hLp.le
  have hB2 : 0 ≤ C2 * Real.log (2 + ‖s‖) := mul_nonneg hC2.le hLp.le
  have hB3 : 0 ≤ C3 := hC3.le
  have hB5 : 0 ≤ C5 := hC5.le
  have hnorm : ‖Gfun s‖
      = ‖riemannZeta₁ s‖ * ‖DirichletCharacter.LFunction chi4 s‖ * ‖(1 - (2 : ℂ) ^ (-s))⁻¹‖
        * ‖Dser (2 * s)‖ * ‖(riemannZeta (2 * s))⁻¹‖ := by
    rw [Gfun, norm_mul, norm_mul, norm_mul, norm_mul]
  rw [hnorm]
  calc ‖riemannZeta₁ s‖ * ‖DirichletCharacter.LFunction chi4 s‖
        * ‖(1 - (2 : ℂ) ^ (-s))⁻¹‖ * ‖Dser (2 * s)‖ * ‖(riemannZeta (2 * s))⁻¹‖
      ≤ (C1 * (2 + ‖s‖) * Real.log (2 + ‖s‖)) * (C2 * Real.log (2 + ‖s‖)) * C3 * C5
          * (C4 * Real.log (2 + ‖s‖)) := by
        refine mul_le_mul (mul_le_mul (mul_le_mul (mul_le_mul e1 e2 (norm_nonneg _) hB1)
          e3 (norm_nonneg _) (mul_nonneg hB1 hB2)) e5 (norm_nonneg _)
          (mul_nonneg (mul_nonneg hB1 hB2) hB3)) e4 (norm_nonneg _)
          (mul_nonneg (mul_nonneg (mul_nonneg hB1 hB2) hB3) hB5)
    _ = (C1 * C2 * C3 * C5 * C4) * (2 + ‖s‖) * (Real.log (2 + ‖s‖)) ^ 3 := by ring

/-- Growth bound for a square root `H` of `Gfun`. -/
lemma H_growth {δ czε cL cinv Cζ CL Cinv : ℝ} (hδ : 0 < δ) (hδ4 : δ ≤ Real.log 2 / 4)
    (hδz : δ ≤ czε) (hδL : δ ≤ cL) (hδinv : δ ≤ cinv)
    (hCζ : 0 < Cζ) (hCL : 0 < CL) (hCinv : 0 < Cinv) (hcinv : 0 ≤ cinv)
    (hζb : ∀ σ t : ℝ, 1 ≤ |t| → 1 - czε / Real.log (|t| + 2) ≤ σ →
      ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ Cζ * Real.log (|t| + 2))
    (hLb : ∀ σ t : ℝ, 1 ≤ |t| → 1 - cL / Real.log (|t| + 2) ≤ σ →
      ‖DirichletCharacter.LFunction chi4 ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ CL * Real.log (|t| + 2))
    (hzinv : ∀ σ t : ℝ, 1 - cinv / Real.log (|t| + 2) ≤ σ → σ ≤ 2 →
      1 / ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ Cinv * (Real.log (|t| + 2) + 1))
    (H : ℂ → ℂ) (hHsq : ∀ s, H s ^ 2 = Gfun s) :
    ∃ A K : ℝ, 0 < A ∧ ∀ s : ℂ, s ∈ oreg δ →
      ‖H s‖ ≤ A * (2 + ‖s‖) ^ (1 / 2 : ℝ) * (Real.log (2 + ‖s‖)) ^ K := by
  obtain ⟨C, hC, hb⟩ := Gfun_growth hδ hδ4 hδz hδL hδinv hCζ hCL hCinv hcinv hζb hLb hzinv
  refine ⟨Real.sqrt C, 3 / 2, Real.sqrt_pos.mpr hC, ?_⟩
  intro s hs
  have hLnn : 0 ≤ Real.log (2 + ‖s‖) := Real.log_nonneg (by linarith [norm_nonneg s])
  have h2nn : 0 ≤ 2 + ‖s‖ := by linarith [norm_nonneg s]
  have hnormsq : ‖H s‖ ^ 2 = ‖Gfun s‖ := by
    rw [← norm_pow (H s) 2, hHsq s]
  have hBnn : 0 ≤ Real.sqrt C * (2 + ‖s‖) ^ (1 / 2 : ℝ) * (Real.log (2 + ‖s‖)) ^ (3 / 2 : ℝ) :=
    mul_nonneg (mul_nonneg (Real.sqrt_nonneg C) (Real.rpow_nonneg h2nn _)) (Real.rpow_nonneg hLnn _)
  have hB2 : (Real.sqrt C * (2 + ‖s‖) ^ (1 / 2 : ℝ) * (Real.log (2 + ‖s‖)) ^ (3 / 2 : ℝ)) ^ 2
      = C * (2 + ‖s‖) * (Real.log (2 + ‖s‖)) ^ 3 := by
    have g1 : (Real.sqrt C) ^ 2 = C := Real.sq_sqrt hC.le
    have g2 : ((2 + ‖s‖) ^ (1 / 2 : ℝ)) ^ 2 = (2 + ‖s‖) := by
      rw [← Real.rpow_natCast ((2 + ‖s‖) ^ (1 / 2 : ℝ)) 2,
        ← Real.rpow_mul h2nn (1 / 2) ((2 : ℕ) : ℝ),
        show (1 / 2 : ℝ) * ((2 : ℕ) : ℝ) = 1 by norm_num, Real.rpow_one]
    have g3 : ((Real.log (2 + ‖s‖)) ^ (3 / 2 : ℝ)) ^ 2 = (Real.log (2 + ‖s‖)) ^ 3 := by
      rw [← Real.rpow_natCast ((Real.log (2 + ‖s‖)) ^ (3 / 2 : ℝ)) 2,
        ← Real.rpow_mul hLnn (3 / 2) ((2 : ℕ) : ℝ),
        show (3 / 2 : ℝ) * ((2 : ℕ) : ℝ) = ((3 : ℕ) : ℝ) by norm_num,
        Real.rpow_natCast]
    calc (Real.sqrt C * (2 + ‖s‖) ^ (1 / 2 : ℝ) * (Real.log (2 + ‖s‖)) ^ (3 / 2 : ℝ)) ^ 2
        = (Real.sqrt C) ^ 2 * ((2 + ‖s‖) ^ (1 / 2 : ℝ)) ^ 2
            * ((Real.log (2 + ‖s‖)) ^ (3 / 2 : ℝ)) ^ 2 := by ring
      _ = C * (2 + ‖s‖) * (Real.log (2 + ‖s‖)) ^ 3 := by rw [g1, g2, g3]
  have hle : ‖H s‖ ^ 2
      ≤ (Real.sqrt C * (2 + ‖s‖) ^ (1 / 2 : ℝ) * (Real.log (2 + ‖s‖)) ^ (3 / 2 : ℝ)) ^ 2 := by
    rw [hnormsq, hB2]
    exact hb s hs
  calc ‖H s‖ = Real.sqrt (‖H s‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt ((Real.sqrt C * (2 + ‖s‖) ^ (1 / 2 : ℝ)
          * (Real.log (2 + ‖s‖)) ^ (3 / 2 : ℝ)) ^ 2) := Real.sqrt_le_sqrt hle
    _ = Real.sqrt C * (2 + ‖s‖) ^ (1 / 2 : ℝ) * (Real.log (2 + ‖s‖)) ^ (3 / 2 : ℝ) :=
        Real.sqrt_sq hBnn

/-- The value at `1` of a square root of `Gfun` is the limit constant. -/
lemma H_one_eq_tendsto (H : ℂ → ℂ) (hcont : ContinuousAt H 1)
    (hIdent : ∀ s : ℂ, 1 < s.re → H s * (s - 1) ^ (-(1 / 2 : ℂ)) = Dser s)
    {c : ℝ} (hc : Tendsto (fun σ : ℝ => Real.sqrt (σ - 1) * realsum4 σ)
      (nhdsWithin (1 : ℝ) (Set.Ioi 1)) (nhds c)) :
    H 1 = (c : ℂ) := by
  have hHev : (fun σ : ℝ => H ((σ : ℂ))) =ᶠ[nhdsWithin (1 : ℝ) (Set.Ioi 1)]
      fun σ : ℝ => ((Real.sqrt (σ - 1) * realsum4 σ : ℝ) : ℂ) := by
    filter_upwards [self_mem_nhdsWithin] with σ hσ
    have hσ1 : (1 : ℝ) < σ := hσ
    have hs1 : (1 : ℝ) < ((σ : ℂ)).re := by
      rw [Complex.ofReal_re]; exact hσ1
    have hsne : ((σ : ℂ) - 1) ≠ 0 := by
      intro h
      have hre : ((σ : ℂ) - 1).re = 0 := by rw [h]; simp
      rw [Complex.sub_re, Complex.one_re, Complex.ofReal_re] at hre
      linarith
    have hH1 : H ((σ : ℂ)) = ((σ : ℂ) - 1) ^ (1 / 2 : ℂ) * Dser ((σ : ℂ)) := by
      have h := hIdent (σ : ℂ) hs1
      have h2 : ((σ : ℂ) - 1) ^ (-(1 / 2 : ℂ)) * ((σ : ℂ) - 1) ^ (1 / 2 : ℂ) = 1 := by
        rw [← Complex.cpow_add _ _ hsne, show (-(1 / 2 : ℂ)) + (1 / 2 : ℂ) = 0 by ring,
          Complex.cpow_zero]
      calc H ((σ : ℂ))
          = H ((σ : ℂ)) * (((σ : ℂ) - 1) ^ (-(1 / 2 : ℂ)) * ((σ : ℂ) - 1) ^ (1 / 2 : ℂ)) := by
            rw [h2, mul_one]
        _ = (H ((σ : ℂ)) * ((σ : ℂ) - 1) ^ (-(1 / 2 : ℂ))) * ((σ : ℂ) - 1) ^ (1 / 2 : ℂ) := by
            ring
        _ = Dser ((σ : ℂ)) * ((σ : ℂ) - 1) ^ (1 / 2 : ℂ) := by rw [h]
        _ = ((σ : ℂ) - 1) ^ (1 / 2 : ℂ) * Dser ((σ : ℂ)) := by ring
    have hDs : Dser ((σ : ℂ)) = ((realsum4 σ : ℝ) : ℂ) := by
      unfold Dser realsum4
      rw [Complex.ofReal_tsum (fun n : ℕ =>
        (Set.indicator {n : ℕ | ∀ p : ℕ, p.Prime → p % 4 = 3 → ¬ p ∣ n} (fun _ => (1 : ℝ)) n)
          * (n : ℝ) ^ (-σ))]
      apply tsum_congr
      intro n
      simp only [Complex.ofReal_mul, Complex.ofReal_cpow (Nat.cast_nonneg n), Complex.ofReal_neg,
        Complex.ofReal_natCast]
      rfl
    rw [hH1, hDs]
    have hcp : (σ : ℂ) - 1 = ((σ - 1 : ℝ) : ℂ) := by push_cast; ring
    have hcast : ((1 / 2 : ℝ) : ℂ) = (1 / 2 : ℂ) := by norm_num
    have hsqrt : ((σ : ℂ) - 1) ^ (1 / 2 : ℂ) = ((Real.sqrt (σ - 1) : ℝ) : ℂ) := by
      rw [hcp, ← hcast, ← Complex.ofReal_cpow (by linarith : (0 : ℝ) ≤ σ - 1) (1 / 2 : ℝ),
        Real.sqrt_eq_rpow]
    rw [hsqrt, ← Complex.ofReal_mul]
  have hcont1 : Tendsto (fun σ : ℝ => H ((σ : ℂ))) (nhdsWithin (1 : ℝ) (Set.Ioi 1)) (nhds (H 1)) :=
    hcont.tendsto.comp
      ((Complex.continuous_ofReal.continuousAt (x := (1 : ℝ))).tendsto.mono_left
        nhdsWithin_le_nhds)
  have htendc : Tendsto (fun σ : ℝ => ((Real.sqrt (σ - 1) * realsum4 σ : ℝ) : ℂ))
      (nhdsWithin (1 : ℝ) (Set.Ioi 1)) (nhds ((c : ℂ))) :=
    (Complex.continuous_ofReal.continuousAt (x := c)).tendsto.comp hc
  exact tendsto_nhds_unique hcont1 (Filter.Tendsto.congr' hHev.symm htendc)

theorem three_mod_four_lseries_continuation :
    ∃ c : ℝ, 0 < c ∧ ∃ H : ℂ → ℂ, ∃ δ : ℝ, 0 < δ ∧
      AnalyticOnNhd ℂ H {s : ℂ | 1 - δ / Real.log (2 + |s.im|) ≤ s.re} ∧
      (∃ A K : ℝ, 0 < A ∧ ∀ s : ℂ, 1 - δ / Real.log (2 + |s.im|) ≤ s.re →
        ‖H s‖ ≤ A * (2 + ‖s‖) ^ (1 / 2 : ℝ) * (Real.log (2 + ‖s‖)) ^ K) ∧
      H 1 = (c : ℂ) ∧
      (∀ s : ℂ, 1 < s.re → H s * (s - 1) ^ (-(1 / 2 : ℂ)) = threeModFourSeries s) := by
  obtain ⟨cζ, hcζ, hζ⟩ := riemannZeta_zero_free_region_log_all_t
  obtain ⟨cc, hcc, hcc4⟩ := chi4_zero_free_region_log
  obtain ⟨Cζ, czε, hCζ, hczε, hζb⟩ := riemannZeta_bound_log_region
  obtain ⟨CL, cL, hCL, hcL, hLb⟩ :=
    Commons.NumberTheory.LSeries.exists_bound_LFunction_chi4_near_one
  obtain ⟨cinv, Cinv, hcinv, hCinv, hzinv⟩ :=
    Commons.NumberTheory.Zeta.inv_zeta_le_log_zeroFree
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set δ : ℝ := min (Real.log 2 / 8) (min (min cζ cc) (min (min czε cL) cinv)) with hδdef
  have hδ : 0 < δ := by
    rw [hδdef]
    exact lt_min (by linarith) (lt_min (lt_min hcζ hcc) (lt_min (lt_min hczε hcL) hcinv))
  have hδ4 : δ ≤ Real.log 2 / 4 := by
    have := min_le_left (Real.log 2 / 8) (min (min cζ cc) (min (min czε cL) cinv))
    rw [hδdef]; linarith
  have hδcζ : δ ≤ cζ :=
    le_trans (le_trans (min_le_right _ _) (min_le_left _ _)) (min_le_left _ _)
  have hδcc : δ ≤ cc :=
    le_trans (le_trans (min_le_right _ _) (min_le_left _ _)) (min_le_right _ _)
  have hδczε : δ ≤ czε :=
    le_trans (le_trans (le_trans (min_le_right _ _) (min_le_right _ _)) (min_le_left _ _))
      (min_le_left _ _)
  have hδcL : δ ≤ cL :=
    le_trans (le_trans (le_trans (min_le_right _ _) (min_le_right _ _)) (min_le_left _ _))
      (min_le_right _ _)
  have hδcinv : δ ≤ cinv :=
    le_trans (le_trans (min_le_right _ _) (min_le_right _ _)) (min_le_right _ _)
  have hzf : ∀ σ t : ℝ, 1 - δ / Real.log (2 + |t|) ≤ σ →
      riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
    intro σ t hσ
    apply hζ σ t
    have hlogpos : 0 < Real.log (2 + |t|) := Real.log_pos (by linarith [abs_nonneg t])
    have hdiv : δ / Real.log (2 + |t|) ≤ cζ / Real.log (2 + |t|) :=
      div_le_div_of_nonneg_right hδcζ hlogpos.le
    linarith
  have hcf : ∀ σ t : ℝ, 1 - δ / Real.log (2 + |t|) ≤ σ →
      DirichletCharacter.LFunction chi4 ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
    intro σ t hσ
    apply hcc4 σ t
    have hlogpos : 0 < Real.log (2 + |t|) := Real.log_pos (by linarith [abs_nonneg t])
    have hdiv : δ / Real.log (2 + |t|) ≤ cc / Real.log (2 + |t|) :=
      div_le_div_of_nonneg_right hδcc hlogpos.le
    linarith
  obtain ⟨H0, hH0an, hH0sq⟩ := exists_analytic_sqrt_Gfun hδ hδ4 hzf hcf
  obtain ⟨H, hHan, hHsq, hIdent⟩ := H0_identity hδ hδ4 hzf hcf H0 hH0an hH0sq
  obtain ⟨c, hcpos, hctend⟩ := three_mod_four_lseries_half
  have h1mem : (1 : ℂ) ∈ oreg δ := by
    rw [oreg]
    simp only [Set.mem_ofPred_eq, Complex.one_re, Complex.one_im, abs_zero, add_zero]
    have : 0 < δ / Real.log 2 := div_pos hδ hlog2
    linarith
  have hH1 : H 1 = (c : ℂ) := H_one_eq_tendsto H (hHan 1 h1mem).continuousAt hIdent hctend
  obtain ⟨A, K, hA, hbound⟩ :=
    H_growth hδ hδ4 hδczε hδcL hδcinv hCζ hCL hCinv hcinv.le hζb hLb hzinv H hHsq
  refine ⟨c, hcpos, H, δ / 2, by linarith, ?_, ?_, hH1, ?_⟩
  · apply hHan.mono
    intro s hs
    simp only [Set.mem_ofPred_eq] at hs
    rw [oreg]
    have hlogpos : 0 < Real.log (2 + |s.im|) := Real.log_pos (by linarith [abs_nonneg s.im])
    have hd : δ / 2 / Real.log (2 + |s.im|) < δ / Real.log (2 + |s.im|) :=
      div_lt_div_of_pos_right (by linarith) hlogpos
    exact lt_of_lt_of_le (sub_lt_sub_left hd 1) hs
  · refine ⟨A, K, hA, ?_⟩
    intro s hs
    apply hbound s
    rw [oreg]
    have hlogpos : 0 < Real.log (2 + |s.im|) := Real.log_pos (by linarith [abs_nonneg s.im])
    have hd : δ / 2 / Real.log (2 + |s.im|) < δ / Real.log (2 + |s.im|) :=
      div_lt_div_of_pos_right (by linarith) hlogpos
    exact lt_of_lt_of_le (sub_lt_sub_left hd 1) hs
  · intro s hs
    rw [threeModFourSeries_eq_Dser]
    exact hIdent s hs

end

end Commons.NumberTheory.Diophantine
