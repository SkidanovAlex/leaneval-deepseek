import Mathlib
import Submission.Commons.NumberTheory.DirichletCharacter.burgess_prime_of_moment
import Submission.Commons.NumberTheory.Chebyshev.theta_le_log3_mul
import Submission.Commons.NumberTheory.Chebyshev.cumulativePrimePowerLeSqrt
import Submission.Commons.NumberTheory.Linnik.polyaVinogradov

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
set_option exponentiation.threshold 1024

open Finset

namespace Commons.NumberTheory.DirichletCharacter

/-!
# Burgess's short-character-sum bound for a general modulus, from the moment estimate

This file proves `burgess_charSum_uniform_of_moment`: from the Burgess (Davenport--Erdos) `2r`-th
moment estimate for characters of every modulus, the short character sum is
`≪ q^{(k+1)/(4k²)+ε} H^{1-1/k}` for `k = 2, 3`.

The prime-modulus case is `burgess_prime_of_moment`; here we adapt the same Burgess argument to an
arbitrary modulus `q`.  The only place where primality was used in the prime case is the splitting
`cSum χ N (N+H) = χ(ℓ) ∑_{a<ℓ} cSum χ ⌊(N-aq)/ℓ⌋ ⌊(N+H-aq)/ℓ⌋`, which requires `ℓ` coprime to the
modulus.  We therefore run the splitting only over the primes `ℓ ∈ (P,2P]` not dividing `q`, whose
number is `≫ P / log P ≫ P / q^ε` (a short-interval prime count), giving an extra factor
`log q = q^{o(1)}` that is absorbed into `q^ε`.
-/

variable {q : ℕ}




/-- Splitting a character sum along the residue classes modulo a `ℓ` coprime to the modulus `q`.

This is `cSum_ap_split` with the primality of the modulus replaced by the honest hypothesis
`IsUnit ((q : ZMod ℓ))` (equivalently `Nat.Coprime q ℓ`), which is what the argument actually uses. -/
theorem cSum_ap_split_gen {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {ℓ : ℕ}
    (hℓ0 : 0 < ℓ) (hunit : IsUnit ((q : ZMod ℓ))) (N : ℤ) (H : ℕ) :
    cSum χ N (N + H) = χ (ℓ : ZMod q) *
      ∑ a ∈ Finset.range ℓ,
        cSum χ ((N - (a:ℤ) * q) / (ℓ:ℤ)) (((N + (H:ℤ)) - (a:ℤ) * q) / (ℓ:ℤ)) := by
  haveI : NeZero ℓ := ⟨by omega⟩
  have hL : (0:ℤ) < (ℓ:ℤ) := by exact_mod_cast hℓ0
  have hq0 : ((q : ZMod q)) = 0 := by simp [ZMod.natCast_self]
  have hkey : ∀ a m : ℤ, ((a * q + (ℓ:ℤ) * m : ℤ) : ZMod q)
      = (ℓ : ZMod q) * (m : ZMod q) := by
    intro a m
    push_cast
    rw [show ((a:ZMod q) * (q:ZMod q)) = 0 by rw [hq0, mul_zero]]
    ring
  have hunit' : IsUnit ((q : ZMod ℓ)) := hunit
  obtain ⟨u, hu⟩ := hunit
  have hsigma : (∑ x ∈ (Finset.range ℓ).sigma (fun a =>
        Finset.Ioc ((N - (a:ℤ) * q) / (ℓ:ℤ)) (((N + (H:ℤ)) - (a:ℤ) * q) / (ℓ:ℤ))),
        χ (ℓ : ZMod q) * χ (x.2 : ZMod q))
      = ∑ a ∈ Finset.range ℓ,
          ∑ m ∈ Finset.Ioc ((N - (a:ℤ) * q) / (ℓ:ℤ)) (((N + (H:ℤ)) - (a:ℤ) * q) / (ℓ:ℤ)),
            χ (ℓ : ZMod q) * χ (m : ZMod q) := by
    rw [Finset.sum_sigma]
  simp only [cSum, Finset.mul_sum]
  rw [← hsigma]
  symm
  refine Finset.sum_bij (fun x _ => (x.1 : ℤ) * q + (ℓ:ℤ) * x.2) ?_ ?_ ?_ ?_
  · intro x hx
    rw [Finset.mem_sigma] at hx
    obtain ⟨ha, hm⟩ := hx
    rw [Finset.mem_range] at ha
    have hm' := (mem_Ioc_ediv_iff hL (N - (x.1:ℤ)*q) ((N + (H:ℤ)) - (x.1:ℤ)*q) x.2).mp hm
    rw [Finset.mem_Ioc]
    constructor <;> linarith only [hm'.1, hm'.2]
  · rintro ⟨x1, x2⟩ hx ⟨y1, y2⟩ hy hxy
    rw [Finset.mem_sigma] at hx hy
    obtain ⟨hxa, hxm⟩ := hx
    obtain ⟨hya, hym⟩ := hy
    rw [Finset.mem_range] at hxa hya
    have hmod : ((x1 : ZMod ℓ)) * (q : ZMod ℓ) = ((y1 : ZMod ℓ)) * (q : ZMod ℓ) := by
      have h := congrArg (fun t : ℤ => (t : ZMod ℓ)) hxy
      push_cast at h
      simpa using h
    have h3 : ∀ z : ZMod ℓ, z * (q : ZMod ℓ) * ↑(u⁻¹) = z := by
      intro z
      rw [← hu, mul_assoc, Units.mul_inv, mul_one]
    have h1 : (x1 : ZMod ℓ) = (y1 : ZMod ℓ) := by
      calc (x1 : ZMod ℓ) = (x1 : ZMod ℓ) * (q : ZMod ℓ) * ↑(u⁻¹) := (h3 _).symm
        _ = (y1 : ZMod ℓ) * (q : ZMod ℓ) * ↑(u⁻¹) := by rw [hmod]
        _ = (y1 : ZMod ℓ) := h3 _
    have haeq : x1 = y1 := by
      have h2 := congrArg ZMod.val h1
      rwa [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt hxa, Nat.mod_eq_of_lt hya] at h2
    have hmeq : x2 = y2 := by
      have hh := hxy
      rw [haeq] at hh
      have : (ℓ:ℤ) * x2 = (ℓ:ℤ) * y2 := by linarith only [hh]
      exact mul_left_cancel₀ (by omega : (ℓ:ℤ) ≠ 0) this
    rw [haeq, hmeq]
  · intro n hn
    rw [Finset.mem_Ioc] at hn
    obtain ⟨ha, huniq⟩ := zmod_mul_residue_unique hℓ0 hunit' n
    have hdvd : (ℓ:ℤ) ∣ (n - (ha:ℤ) * q) := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd (n - (ha:ℤ)*q) ℓ]
      push_cast
      rw [huniq.1.2]
      ring
    refine ⟨⟨ha, (n - (ha:ℤ) * q) / (ℓ:ℤ)⟩, ?_, ?_⟩
    · rw [Finset.mem_sigma]
      refine ⟨Finset.mem_range.mpr huniq.1.1, ?_⟩
      rw [mem_Ioc_ediv_iff hL]
      have h1 : ((n - (ha:ℤ)*q) / (ℓ:ℤ)) * (ℓ:ℤ) = n - (ha:ℤ)*q :=
        Int.ediv_mul_cancel hdvd
      constructor <;> linarith only [hn.1, hn.2, h1]
    · have h1 : ((n - (ha:ℤ)*q) / (ℓ:ℤ)) * (ℓ:ℤ) = n - (ha:ℤ)*q := Int.ediv_mul_cancel hdvd
      linarith only [h1]
  · intro x hx
    rw [hkey, map_mul]


lemma burgess_principle_gen {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (N : ℤ) (H P h : ℕ)
    (hP1 : 1 ≤ P) (h2P : 2*P < q)
    (hlo : ∀ x ∈ objFinset P, -(2*(q:ℤ)) ≤ oLo N q x.1 x.2 - (h:ℤ) ∧ oLo N q x.1 x.2 ≤ (q:ℤ))
    (hlen : ∀ x ∈ objFinset P, oHi N q H x.1 x.2 - oLo N q x.1 x.2 ≤ (h:ℤ)) :
    (h:ℝ) * (∑ x ∈ objFinset P, ‖cSum χ (oLo N q x.1 x.2) (oHi N q H x.1 x.2)‖)
      ≤ 2 * ∑ n ∈ Finset.Icc (-(2*(q:ℤ))) (q:ℤ), weightA N q h P n * supShift χ n (2*h) := by
  have hsub : ∀ x ∈ objFinset P,
      Finset.Ioc (oLo N q x.1 x.2 - (h:ℤ)) (oLo N q x.1 x.2) ⊆ Finset.Icc (-(2*(q:ℤ))) (q:ℤ) := by
    intro x hx n hn
    rw [Finset.mem_Ioc] at hn
    rw [Finset.mem_Icc]
    exact ⟨by linarith only [(hlo x hx).1, hn, hlo, hx], by linarith only [hn.2, (hlo x hx).2, hn, hlo, hx]⟩
  have hpt : ∀ x ∈ objFinset P, (h:ℝ) * ‖cSum χ (oLo N q x.1 x.2) (oHi N q H x.1 x.2)‖
      ≤ 2 * ∑ n ∈ Finset.Icc (-(2*(q:ℤ))) (q:ℤ),
          (if oLo N q x.1 x.2 - (h:ℤ) < n ∧ n ≤ oLo N q x.1 x.2 then (1:ℝ) else 0)
            * supShift χ n (2*h) := by
    intro x hx
    have hpx : 0 < x.1 := by
      have := (mem_objFinset.mp hx).1
      omega
    have hcard : ((Finset.Ioc (oLo N q x.1 x.2 - (h:ℤ)) (oLo N q x.1 x.2)).card : ℝ) = (h:ℝ) := by
      rw [Int.card_Ioc]
      have heq : oLo N q x.1 x.2 - (oLo N q x.1 x.2 - (h:ℤ)) = (h:ℤ) := by ring
      rw [heq]
      rw [show ((h:ℤ).toNat : ℝ) = (h:ℝ) by
        exact_mod_cast (Int.toNat_of_nonneg (by exact_mod_cast Nat.zero_le h : (0:ℤ) ≤ (h:ℤ)))]
    have hsum1 : (∑ _n ∈ Finset.Ioc (oLo N q x.1 x.2 - (h:ℤ)) (oLo N q x.1 x.2),
          ‖cSum χ (oLo N q x.1 x.2) (oHi N q H x.1 x.2)‖)
        = (h:ℝ) * ‖cSum χ (oLo N q x.1 x.2) (oHi N q H x.1 x.2)‖ := by
      rw [Finset.sum_const, nsmul_eq_mul, hcard]
    have h1 : ∑ n ∈ Finset.Ioc (oLo N q x.1 x.2 - (h:ℤ)) (oLo N q x.1 x.2),
        ‖cSum χ (oLo N q x.1 x.2) (oHi N q H x.1 x.2)‖
        ≤ ∑ n ∈ Finset.Ioc (oLo N q x.1 x.2 - (h:ℤ)) (oLo N q x.1 x.2),
          2 * supShift χ n (2*h) := by
      refine Finset.sum_le_sum (fun n hn => ?_)
      rw [Finset.mem_Ioc] at hn
      exact cSum_le_two_supShift' χ (oLo_le_oHi N q H x.1 x.2 hpx) hn.2 (hlen x hx) hn.1
    have h2 : ∑ n ∈ Finset.Ioc (oLo N q x.1 x.2 - (h:ℤ)) (oLo N q x.1 x.2),
        2 * supShift χ n (2*h)
        = 2 * ∑ n ∈ Finset.Ioc (oLo N q x.1 x.2 - (h:ℤ)) (oLo N q x.1 x.2), supShift χ n (2*h) :=
      (Finset.mul_sum ..).symm
    have hfilter : (Finset.Icc (-(2*(q:ℤ))) (q:ℤ)).filter
          (fun n => oLo N q x.1 x.2 - (h:ℤ) < n ∧ n ≤ oLo N q x.1 x.2)
        = Finset.Ioc (oLo N q x.1 x.2 - (h:ℤ)) (oLo N q x.1 x.2) := by
      ext n
      rw [Finset.mem_filter]
      constructor
      · rintro ⟨_, h1, h2⟩
        exact Finset.mem_Ioc.mpr ⟨h1, h2⟩
      · intro h
        obtain ⟨h1, h2⟩ := Finset.mem_Ioc.mp h
        exact ⟨hsub x hx (Finset.mem_Ioc.mpr ⟨h1, h2⟩), h1, h2⟩
    have h3 : (2 * ∑ n ∈ Finset.Ioc (oLo N q x.1 x.2 - (h:ℤ)) (oLo N q x.1 x.2), supShift χ n (2*h))
        = 2 * ∑ n ∈ Finset.Icc (-(2*(q:ℤ))) (q:ℤ),
            (if oLo N q x.1 x.2 - (h:ℤ) < n ∧ n ≤ oLo N q x.1 x.2 then (1:ℝ) else 0)
              * supShift χ n (2*h) := by
      congr 1
      have key1 : ∑ n ∈ Finset.Icc (-(2*(q:ℤ))) (q:ℤ),
          (if oLo N q x.1 x.2 - (h:ℤ) < n ∧ n ≤ oLo N q x.1 x.2 then (1:ℝ) else 0)
            * supShift χ n (2*h)
          = ∑ n ∈ Finset.Icc (-(2*(q:ℤ))) (q:ℤ),
              (if oLo N q x.1 x.2 - (h:ℤ) < n ∧ n ≤ oLo N q x.1 x.2
                then supShift χ n (2*h) else 0) := by
        refine Finset.sum_congr rfl (fun n hn => ?_)
        split <;> ring
      rw [key1, ← Finset.sum_filter, hfilter]
    calc (h:ℝ) * ‖cSum χ (oLo N q x.1 x.2) (oHi N q H x.1 x.2)‖
        = ∑ _n ∈ Finset.Ioc (oLo N q x.1 x.2 - (h:ℤ)) (oLo N q x.1 x.2),
            ‖cSum χ (oLo N q x.1 x.2) (oHi N q H x.1 x.2)‖ := hsum1.symm
      _ ≤ ∑ n ∈ Finset.Ioc (oLo N q x.1 x.2 - (h:ℤ)) (oLo N q x.1 x.2),
            2 * supShift χ n (2*h) := h1
      _ = 2 * ∑ n ∈ Finset.Ioc (oLo N q x.1 x.2 - (h:ℤ)) (oLo N q x.1 x.2), supShift χ n (2*h) := h2
      _ = 2 * ∑ n ∈ Finset.Icc (-(2*(q:ℤ))) (q:ℤ),
            (if oLo N q x.1 x.2 - (h:ℤ) < n ∧ n ≤ oLo N q x.1 x.2 then (1:ℝ) else 0)
              * supShift χ n (2*h) := h3

  calc (h:ℝ) * (∑ x ∈ objFinset P, ‖cSum χ (oLo N q x.1 x.2) (oHi N q H x.1 x.2)‖)
      = ∑ x ∈ objFinset P, (h:ℝ) * ‖cSum χ (oLo N q x.1 x.2) (oHi N q H x.1 x.2)‖ :=
        Finset.mul_sum ..
    _ ≤ ∑ x ∈ objFinset P, 2 * ∑ n ∈ Finset.Icc (-(2*(q:ℤ))) (q:ℤ),
          (if oLo N q x.1 x.2 - (h:ℤ) < n ∧ n ≤ oLo N q x.1 x.2 then (1:ℝ) else 0)
            * supShift χ n (2*h) := Finset.sum_le_sum hpt
    _ = 2 * ∑ x ∈ objFinset P, ∑ n ∈ Finset.Icc (-(2*(q:ℤ))) (q:ℤ),
          (if oLo N q x.1 x.2 - (h:ℤ) < n ∧ n ≤ oLo N q x.1 x.2 then (1:ℝ) else 0)
            * supShift χ n (2*h) := by rw [Finset.mul_sum]
    _ = 2 * ∑ n ∈ Finset.Icc (-(2*(q:ℤ))) (q:ℤ), ∑ x ∈ objFinset P,
          (if oLo N q x.1 x.2 - (h:ℤ) < n ∧ n ≤ oLo N q x.1 x.2 then (1:ℝ) else 0)
            * supShift χ n (2*h) := by
        rw [Finset.sum_comm]
    _ = 2 * ∑ n ∈ Finset.Icc (-(2*(q:ℤ))) (q:ℤ), weightA N q h P n * supShift χ n (2*h) := by
        congr 1
        refine Finset.sum_congr rfl (fun n hn => ?_)
        unfold weightA
        rw [← Finset.sum_mul]





lemma moment_W_le_gen {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (Cm : ℝ) (k : ℕ) (hk2 : 2 ≤ k)
    (hmom : ∀ L : ℕ, L ≤ q → ∑ m ∈ Finset.range q, ‖cSum χ (m:ℤ) ((m:ℤ) + L)‖^(2*k)
        ≤ Cm * ((q:ℝ) * (L:ℝ)^k + (L:ℝ)^(2*k) * Real.sqrt q))
    (h t K : ℕ) (ht : K = 2^t) (hK1 : 2*h ≤ K) (hKp : K ≤ q) :
    ∑ n ∈ Finset.Icc (-(2*(q:ℤ))) (q:ℤ), (supShift χ n (2*h))^(2*k)
      ≤ 4 * ((t+1:ℝ))^(2*k) *
          (4*Cm*((q:ℝ)*((2:ℝ)^t)^k + ((2:ℝ)^t)^(2*k)*Real.sqrt q)) := by
  have hB := supShift_window_le χ Cm k (by omega) hk2 hmom t (-(2*(q:ℤ))) (2*h)
    (by have h := hK1; rw [ht] at h; exact h) (by have h := hKp; rw [ht] at h; exact h)
  have hstep1 : ∑ n ∈ Finset.Icc (-(2*(q:ℤ))) (q:ℤ), (supShift χ n (2*h))^(2*k)
      ≤ ∑ n ∈ Finset.Icc (-(2*(q:ℤ))) (2*(q:ℤ)-1), (supShift χ n (2*h))^(2*k) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_
      (fun x hx hx' => pow_nonneg (supShift_nonneg χ x (2*h)) _)
    intro x hx
    rw [Finset.mem_Icc] at hx ⊢
    have hp2 : 1 ≤ q := (Nat.one_le_iff_ne_zero.mpr (NeZero.ne q))
    constructor <;> omega
  have hstep2 : ∑ n ∈ Finset.Icc (-(2*(q:ℤ))) (2*(q:ℤ)-1), (supShift χ n (2*h))^(2*k)
      = 4 * ∑ m ∈ Finset.range q, (supShift χ (-(2*(q:ℤ)) + (m:ℤ)) (2*h))^(2*k) := by
    have h4 : (2*(q:ℤ)-1) = -(2*(q:ℤ)) + ((4*q : ℕ):ℤ) - 1 := by push_cast; ring
    rw [h4, sum_Icc_eq_sum_range (fun x => (supShift χ x (2*h))^(2*k)) (-(2*(q:ℤ))) (4*q)]
    rw [sum_range_periodic_mul (p := q)
      (by have hp2 : 1 ≤ q := (Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)); omega)
      (fun m => (supShift χ (-(2*(q:ℤ)) + (m:ℤ)) (2*h))^(2*k)) ?_ 4]
    · ring
    · intro m
      rw [show -(2*(q:ℤ)) + (((q+m:ℕ)):ℤ) = (-(2*(q:ℤ)) + (m:ℤ)) + (q:ℤ) by push_cast; ring]
      rw [supShift_add_q]
  have hstep3 : ∑ m ∈ Finset.range q, (supShift χ (-(2*(q:ℤ)) + (m:ℤ)) (2*h))^(2*k)
      = ∑ x ∈ Finset.Icc (-(2*(q:ℤ))) (-(2*(q:ℤ)) + (q:ℤ) - 1),
          (supShift χ x (2*h))^(2*k) :=
    (sum_Icc_eq_sum_range (fun x => (supShift χ x (2*h))^(2*k)) (-(2*(q:ℤ))) q).symm
  calc ∑ n ∈ Finset.Icc (-(2*(q:ℤ))) (q:ℤ), (supShift χ n (2*h))^(2*k)
      ≤ ∑ n ∈ Finset.Icc (-(2*(q:ℤ))) (2*(q:ℤ)-1), (supShift χ n (2*h))^(2*k) := hstep1
    _ = 4 * ∑ m ∈ Finset.range q, (supShift χ (-(2*(q:ℤ)) + (m:ℤ)) (2*h))^(2*k) := hstep2
    _ = 4 * ∑ x ∈ Finset.Icc (-(2*(q:ℤ))) (-(2*(q:ℤ)) + (q:ℤ) - 1),
          (supShift χ x (2*h))^(2*k) := by rw [hstep3]
    _ ≤ 4 * (((t+1:ℝ))^(2*k) *
          (4*Cm*((q:ℝ)*((2:ℝ)^t)^k + ((2:ℝ)^t)^(2*k)*Real.sqrt q))) :=
        mul_le_mul_of_nonneg_left hB (by norm_num)
    _ = 4 * ((t+1:ℝ))^(2*k) *
          (4*Cm*((q:ℝ)*((2:ℝ)^t)^k + ((2:ℝ)^t)^(2*k)*Real.sqrt q)) := by ring




/-- Burgess's splitting, run over the primes `ℓ ∈ (P,2P]` coprime to the modulus `q`.

For every such `ℓ` the exact identity `cSum χ N (N+H) = χ(ℓ) ∑_{a<ℓ} cSum χ (oLo N q ℓ a) (oHi N q H ℓ a)`
holds, so summing over the `ℓ` and using `CL` as a bookkeeping constant for the (reciprocal of the)
density of the splitters gives the displayed bound. -/
lemma burgess_split_gen {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (N : ℤ) (H P : ℕ)
    (hP1 : 1 ≤ P) (CL : ℝ) (hCL : 0 ≤ CL)
    (hcard : (P:ℝ) ≤ CL *
      (((Finset.Icc (P+1) (2*P)).filter (fun ℓ : ℕ => Nat.Coprime ℓ q)).card : ℝ)) :
    (P:ℝ) * ‖cSum χ N (N + (H:ℤ))‖
      ≤ CL * ∑ x ∈ objFinset P, ‖cSum χ (oLo N q x.1 x.2) (oHi N q H x.1 x.2)‖ := by
  set S : Finset ℕ := (Finset.Icc (P+1) (2*P)).filter (fun ℓ : ℕ => Nat.Coprime ℓ q) with hSdef
  have hsingle : ∀ ℓ ∈ S, ‖cSum χ N (N + (H:ℤ))‖
      ≤ ∑ a ∈ Finset.range ℓ, ‖cSum χ (oLo N q ℓ a) (oHi N q H ℓ a)‖ := by
    intro ℓ hℓ
    rw [hSdef, Finset.mem_filter, Finset.mem_Icc] at hℓ
    obtain ⟨⟨hℓ1, hℓ2⟩, hcop⟩ := hℓ
    have hℓ0 : 0 < ℓ := by omega
    have hunit : IsUnit ((q : ZMod ℓ)) := (ZMod.isUnit_iff_coprime q ℓ).mpr hcop.symm
    have h1 := cSum_ap_split_gen χ hℓ0 hunit N H
    calc ‖cSum χ N (N + (H:ℤ))‖
        = ‖χ (ℓ : ZMod q) * ∑ a ∈ Finset.range ℓ, cSum χ (oLo N q ℓ a) (oHi N q H ℓ a)‖ := by
          rw [h1]; simp only [oLo, oHi]
      _ ≤ ‖χ (ℓ : ZMod q)‖ * ‖∑ a ∈ Finset.range ℓ, cSum χ (oLo N q ℓ a) (oHi N q H ℓ a)‖ :=
          norm_mul_le _ _
      _ ≤ 1 * ‖∑ a ∈ Finset.range ℓ, cSum χ (oLo N q ℓ a) (oHi N q H ℓ a)‖ :=
          mul_le_mul_of_nonneg_right (DirichletCharacter.norm_le_one χ _) (norm_nonneg _)
      _ = ‖∑ a ∈ Finset.range ℓ, cSum χ (oLo N q ℓ a) (oHi N q H ℓ a)‖ := one_mul _
      _ ≤ ∑ a ∈ Finset.range ℓ, ‖cSum χ (oLo N q ℓ a) (oHi N q H ℓ a)‖ := norm_sum_le _ _
  have hsum1 : (S.card : ℝ) * ‖cSum χ N (N + (H:ℤ))‖
      ≤ ∑ ℓ ∈ S, ∑ a ∈ Finset.range ℓ, ‖cSum χ (oLo N q ℓ a) (oHi N q H ℓ a)‖ := by
    calc (S.card : ℝ) * ‖cSum χ N (N + (H:ℤ))‖ = ∑ _ℓ ∈ S, ‖cSum χ N (N + (H:ℤ))‖ := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ ℓ ∈ S, ∑ a ∈ Finset.range ℓ, ‖cSum χ (oLo N q ℓ a) (oHi N q H ℓ a)‖ :=
          Finset.sum_le_sum hsingle
  have hsum2 : ∑ ℓ ∈ S, ∑ a ∈ Finset.range ℓ, ‖cSum χ (oLo N q ℓ a) (oHi N q H ℓ a)‖
      ≤ ∑ x ∈ objFinset P, ‖cSum χ (oLo N q x.1 x.2) (oHi N q H x.1 x.2)‖ := by
    rw [sum_obj P (fun l a => ‖cSum χ (oLo N q l a) (oHi N q H l a)‖)]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
    · intro ℓ hℓ
      rw [hSdef, Finset.mem_filter] at hℓ
      exact hℓ.1
    · intro ℓ hℓ hℓ'
      exact Finset.sum_nonneg (fun a _ => norm_nonneg _)
  calc (P:ℝ) * ‖cSum χ N (N + (H:ℤ))‖
      ≤ (CL * (S.card : ℝ)) * ‖cSum χ N (N + (H:ℤ))‖ :=
        mul_le_mul_of_nonneg_right hcard (norm_nonneg _)
    _ = CL * ((S.card : ℝ) * ‖cSum χ N (N + (H:ℤ))‖) := by ring
    _ ≤ CL * ∑ x ∈ objFinset P, ‖cSum χ (oLo N q x.1 x.2) (oHi N q H x.1 x.2)‖ :=
        mul_le_mul_of_nonneg_left (hsum1.trans hsum2) hCL

/-! ## A short-interval prime count (Chebyshev) and the window count

`#(primes in (P,2P]) > (7/64)P/log(2P)`, which is what the Burgess splitting over the primes `ℓ`
coprime to the modulus needs.  We use the elementary Chebyshev bounds already available:
`θ(2P) ≥ (2P-1)log2 - log(2P+2) - 2√(2P)log(2P)` (Mathlib `Chebyshev.theta_ge'`) and
`θ(P) ≤ log 3 · P` (commons `theta_le_log3_mul`).  The error term is dominated by `P/64` for
`P ≥ 2^64`, and from this we also deduce that the number of `ℓ ∈ (P,2P]` coprime to `q` is large
enough for the modulus `q ≤ P^8`.
-/

lemma burgess_two_log_two_sub_log_three_ge : (1:ℝ)/8 ≤ 2 * Real.log 2 - Real.log 3 := by
  have h2 : (0.6931:ℝ) ≤ Real.log 2 := by linarith only [Real.log_two_gt_d9]
  have h3 : Real.log 3 ≤ Real.log 2 + 1/2 := by
    have hm : Real.log 3 = Real.log 2 + Real.log ((3:ℝ)/2) := by
      have h := Real.log_mul (show (2:ℝ) ≠ 0 by norm_num) (show ((3:ℝ)/2) ≠ 0 by norm_num)
      rw [show (2:ℝ) * (3/2) = 3 by norm_num] at h
      linarith only [h]
    rw [hm]
    have h4 := Real.log_le_sub_one_of_pos (show (0:ℝ) < (3:ℝ)/2 by norm_num)
    linarith only [h4]
  linarith only [h2, h3]

lemma burgess_log_le_four_rpow_quarter (y : ℝ) (hy : 1 ≤ y) : Real.log y ≤ 4 * y^(1/4:ℝ) := by
  have h1 : (0:ℝ) < y := lt_of_lt_of_le one_pos hy
  have h := Real.log_le_rpow_div (x := y) (ε := (1/4:ℝ)) h1.le (by norm_num)
  have h2 : y^(1/4:ℝ) / (1/4:ℝ) = 4 * y^(1/4:ℝ) := by
    rw [div_eq_mul_inv, show (((1:ℝ)/4))⁻¹ = 4 by norm_num]
    ring
  rw [h2] at h; exact h

lemma burgess_rpow_quarter_ge {P : ℕ} (hP : 2^64 ≤ P) : (3392:ℝ) ≤ (P:ℝ)^(1/4:ℝ) := by
  have hcast : ((2:ℝ)^64) ≤ (P:ℝ) := by
    have h : ((2^64 : ℕ) : ℝ) ≤ (P:ℝ) := by exact_mod_cast hP
    rwa [Nat.cast_pow, Nat.cast_ofNat] at h
  have h1 : ((2:ℝ)^64)^(1/4:ℝ) ≤ (P:ℝ)^(1/4:ℝ) :=
    Real.rpow_le_rpow (by positivity) hcast (by norm_num)
  have h2 : ((2:ℝ)^64)^(1/4:ℝ) = (2:ℝ)^16 := by
    rw [← Real.rpow_natCast (x := (2:ℝ)) (n := 64), ← Real.rpow_mul (show (0:ℝ) ≤ 2 by norm_num)]
    norm_num
  have h3 : (3392:ℝ) ≤ (2:ℝ)^16 := by norm_num
  linarith only [h1, h2, h3]

lemma burgess_rpow_half_ge {P : ℕ} (hP : 2^64 ≤ P) : (10000:ℝ) ≤ (P:ℝ)^(1/2:ℝ) := by
  have hcast : ((2:ℝ)^64) ≤ (P:ℝ) := by
    have h : ((2^64 : ℕ) : ℝ) ≤ (P:ℝ) := by exact_mod_cast hP
    rwa [Nat.cast_pow, Nat.cast_ofNat] at h
  have h1 : ((2:ℝ)^64)^(1/2:ℝ) ≤ (P:ℝ)^(1/2:ℝ) :=
    Real.rpow_le_rpow (by positivity) hcast (by norm_num)
  have h2 : ((2:ℝ)^64)^(1/2:ℝ) = (2:ℝ)^32 := by
    rw [← Real.rpow_natCast (x := (2:ℝ)) (n := 64), ← Real.rpow_mul (show (0:ℝ) ≤ 2 by norm_num)]
    norm_num
  have h3 : (10000:ℝ) ≤ (2:ℝ)^32 := by norm_num
  linarith only [h1, h2, h3]

lemma burgess_one_le_P {P : ℕ} (hP : 2^64 ≤ P) : (1:ℝ) ≤ (P:ℝ) := by
  have : (1:ℕ) ≤ P := le_trans (by norm_num : 1 ≤ 2^64) hP
  exact_mod_cast this

lemma burgess_log_error_small {P : ℕ} (hP : 2^64 ≤ P) :
    Real.log 2 + Real.log (2*(P:ℝ)+2) + 2*Real.sqrt (2*(P:ℝ)) * Real.log (2*(P:ℝ))
      ≤ (1/64) * (P:ℝ) := by
  have hP1 : (1:ℝ) ≤ (P:ℝ) := burgess_one_le_P hP
  have hPpos : (0:ℝ) < (P:ℝ) := by linarith only [hP1]
  have hq : (3392:ℝ) ≤ (P:ℝ)^(1/4:ℝ) := burgess_rpow_quarter_ge hP
  have hqpos : (0:ℝ) < (P:ℝ)^(1/4:ℝ) := lt_of_lt_of_le (by norm_num) hq
  have hPone : (1:ℝ) ≤ (P:ℝ)^(1/4:ℝ) := Real.one_le_rpow hP1 (by norm_num)
  have ha : Real.log 2 ≤ (P:ℝ)^(1/4:ℝ) := by
    have h1 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num); linarith only [this]
    linarith only [hq, h1]
  have hlog4 : Real.log 4 ≤ 16 := by
    have h := burgess_log_le_four_rpow_quarter 4 (by norm_num)
    have h4 : (4:ℝ)^(1/4:ℝ) ≤ 4 := by
      have h' := Real.rpow_le_rpow_of_exponent_le (show (1:ℝ) ≤ 4 by norm_num)
        (show ((1:ℝ)/4) ≤ 1 by norm_num)
      simpa using h'
    linarith only [h, h4]
  have hlogP : Real.log (P:ℝ) ≤ 4 * (P:ℝ)^(1/4:ℝ) := burgess_log_le_four_rpow_quarter _ hP1
  have hb : Real.log (2*(P:ℝ)+2) ≤ 20 * (P:ℝ)^(1/4:ℝ) := by
    have hmono : Real.log (2*(P:ℝ)+2) ≤ Real.log (4*(P:ℝ)) := by
      apply Real.log_le_log (by positivity)
      linarith only [hP1]
    rw [Real.log_mul (by norm_num) (by linarith only [hP1])] at hmono
    linarith only [hq, hlog4, hlogP, hmono]
  have hc : 2*Real.sqrt (2*(P:ℝ)) * Real.log (2*(P:ℝ)) ≤ 32 * (P:ℝ)^(3/4:ℝ) := by
    have h2P : (0:ℝ) < 2*(P:ℝ) := by linarith only [hP1]
    have h2P1 : (1:ℝ) ≤ 2*(P:ℝ) := by linarith only [hP1]
    have hlog : Real.log (2*(P:ℝ)) ≤ 8 * (P:ℝ)^(1/4:ℝ) := by
      have h := burgess_log_le_four_rpow_quarter (2*(P:ℝ)) h2P1
      rw [Real.mul_rpow (by norm_num) hPpos.le] at h
      have h2q : (2:ℝ)^(1/4:ℝ) ≤ 2 := by
        have h' := Real.rpow_le_rpow_of_exponent_le (show (1:ℝ) ≤ 2 by norm_num)
          (show ((1:ℝ)/4) ≤ 1 by norm_num)
        simpa using h'
      nlinarith only [h, h2q, hqpos]
    have hsqrt : Real.sqrt (2*(P:ℝ)) = (2*(P:ℝ))^(1/2:ℝ) := Real.sqrt_eq_rpow _
    rw [hsqrt]
    have hsq : (2*(P:ℝ))^(1/2:ℝ) ≤ 2 * (P:ℝ)^(1/2:ℝ) := by
      rw [Real.mul_rpow (by norm_num) hPpos.le]
      have h2q : (2:ℝ)^(1/2:ℝ) ≤ 2 := by
        have h' := Real.rpow_le_rpow_of_exponent_le (show (1:ℝ) ≤ 2 by norm_num)
          (show ((1:ℝ)/2) ≤ 1 by norm_num)
        simpa using h'
      have hnn : (0:ℝ) ≤ (P:ℝ)^(1/2:ℝ) := Real.rpow_nonneg hPpos.le _
      nlinarith only [h2q, hnn]
    have hlog2Ppos : (0:ℝ) ≤ Real.log (2*(P:ℝ)) := Real.log_nonneg h2P1
    have hprod : (2*(P:ℝ))^(1/2:ℝ) * Real.log (2*(P:ℝ))
        ≤ (2 * (P:ℝ)^(1/2:ℝ)) * (8 * (P:ℝ)^(1/4:ℝ)) :=
      mul_le_mul hsq hlog hlog2Ppos (by positivity)
    have h3 : (P:ℝ)^(1/2:ℝ) * (P:ℝ)^(1/4:ℝ) = (P:ℝ)^(3/4:ℝ) := by
      rw [← Real.rpow_add hPpos, show ((1:ℝ)/2 + 1/4) = (3/4:ℝ) by norm_num]
    have hfin : 2 * ((2*(P:ℝ))^(1/2:ℝ) * Real.log (2*(P:ℝ)))
        ≤ 2 * ((2 * (P:ℝ)^(1/2:ℝ)) * (8 * (P:ℝ)^(1/4:ℝ))) := by linarith only [hprod]
    have heq : 2 * ((2 * (P:ℝ)^(1/2:ℝ)) * (8 * (P:ℝ)^(1/4:ℝ))) = 32 * (P:ℝ)^(3/4:ℝ) := by
      rw [← h3]; ring
    linarith only [hfin, heq.le]
  have hsum : Real.log 2 + Real.log (2*(P:ℝ)+2) + 2*Real.sqrt (2*(P:ℝ))*Real.log (2*(P:ℝ))
      ≤ 53 * (P:ℝ)^(3/4:ℝ) := by
    have hp13 : (P:ℝ)^(1/4:ℝ) ≤ (P:ℝ)^(3/4:ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hP1 (by norm_num)
    linarith only [ha, hb, hc, hp13]
  refine le_trans hsum ?_
  have hp34 : (P:ℝ)^(3/4:ℝ) = (P:ℝ)^(1:ℝ) * (P:ℝ)^(-(1/4):ℝ) := by
    rw [← Real.rpow_add hPpos]
    norm_num
  rw [hp34, Real.rpow_one]
  have hinv : (P:ℝ)^(-(1/4):ℝ) ≤ (3392:ℝ)⁻¹ := by
    rw [Real.rpow_neg hPpos.le]
    simpa [one_div] using one_div_le_one_div_of_le (show (0:ℝ) < 3392 by norm_num) hq
  have hfin : 53 * ((P:ℝ) * (P:ℝ)^(-(1/4):ℝ)) ≤ 53 * ((P:ℝ) * (3392:ℝ)⁻¹) := by
    have h1 : (P:ℝ) * (P:ℝ)^(-(1/4):ℝ) ≤ (P:ℝ) * (3392:ℝ)⁻¹ :=
      mul_le_mul_of_nonneg_left hinv hPpos.le
    linarith only [h1]
  have hone : (53:ℝ) * ((P:ℝ) * (3392:ℝ)⁻¹) = (1/64) * (P:ℝ) := by
    have h53 : (53:ℝ) * (3392:ℝ)⁻¹ = 1/64 := by norm_num
    linear_combination (P:ℝ) * h53
  linarith only [hfin, hone.ge]

lemma burgess_theta_interval_lower {P : ℕ} (hP : 2^64 ≤ P) :
    (7/64 : ℝ) * (P:ℝ) ≤ Chebyshev.theta (2*(P:ℝ)) - Chebyshev.theta (P:ℝ) := by
  have hP1 : (1:ℝ) ≤ (P:ℝ) := burgess_one_le_P hP
  have hlow := Chebyshev.theta_ge' (x := 2*(P:ℝ)) (by linarith only [hP1])
  have hup := Commons.NumberTheory.Chebyshev.theta_le_log3_mul P
  have herr := burgess_log_error_small hP
  have hc := burgess_two_log_two_sub_log_three_ge
  have hcP : (1/8) * (P:ℝ) ≤ (P:ℝ) * (2 * Real.log 2 - Real.log 3) := by
    nlinarith only [hc, hP1]
  linarith only [hlow, hup, herr, hcP]



lemma burgess_log_two_mul_le_eight {P : ℕ} (hP1 : (1:ℝ) ≤ (P:ℝ)) :
    Real.log (2*(P:ℝ)) ≤ 8 * (P:ℝ)^(1/4:ℝ) := by
  have hPpos : (0:ℝ) < (P:ℝ) := by linarith only [hP1]
  have h2P1 : (1:ℝ) ≤ 2*(P:ℝ) := by linarith only [hP1]
  have h := burgess_log_le_four_rpow_quarter (2*(P:ℝ)) h2P1
  rw [Real.mul_rpow (by norm_num) hPpos.le] at h
  have h2q : (2:ℝ)^(1/4:ℝ) ≤ 2 := by
    have h' := Real.rpow_le_rpow_of_exponent_le (show (1:ℝ) ≤ 2 by norm_num)
      (show ((1:ℝ)/4) ≤ 1 by norm_num)
    simpa using h'
  have hp : (0:ℝ) < (P:ℝ)^(1/4:ℝ) := Real.rpow_pos_of_pos hPpos _
  nlinarith only [h, h2q, hp]

lemma burgess_short_interval_prime_count_local (P : ℕ) (hP : 2^64 ≤ P) :
    (7/64 : ℝ) * (P:ℝ) / Real.log (2*(P:ℝ))
      ≤ (((Finset.Ioc P (2*P)).filter (fun p : ℕ => Nat.Prime p)).card : ℝ) := by
  have hP1 : (1:ℝ) ≤ (P:ℝ) := burgess_one_le_P hP
  have hPpos : (0:ℝ) < (P:ℝ) := by linarith only [hP1]
  have hlogpos : (0:ℝ) < Real.log (2*(P:ℝ)) := Real.log_pos (by linarith only [hP1])
  set S : Finset ℕ := (Finset.Ioc P (2*P)).filter (fun p : ℕ => Nat.Prime p) with hS
  have hSeq : S = (2*P).primesLE \ P.primesLE := by
    rw [hS]
    ext p
    simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_sdiff, Nat.mem_primesLE]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨⟨h2, h3⟩, fun h => absurd h.1 (not_le.mpr h1)⟩
    · rintro ⟨⟨h2, h3⟩, h4⟩
      exact ⟨⟨lt_of_not_ge (fun h => h4 ⟨h, h3⟩), h2⟩, h3⟩
  have ht2 : Chebyshev.theta (2*(P:ℝ)) = ∑ p ∈ (2*P).primesLE, Real.log (p:ℝ) := by
    rw [Chebyshev.theta_eq_sum_primesLE]
    congr 1
    rw [show 2*(P:ℝ) = ((2*P:ℕ):ℝ) by push_cast; ring, Nat.floor_natCast]
  have ht1 : Chebyshev.theta (P:ℝ) = ∑ p ∈ P.primesLE, Real.log (p:ℝ) := by
    rw [Chebyshev.theta_eq_sum_primesLE]
    congr 1
    rw [show (P:ℝ) = ((P:ℕ):ℝ) by push_cast; ring, Nat.floor_natCast]
  have hsub : P.primesLE ⊆ (2*P).primesLE := Nat.primesLE_mono (by omega)
  have hsplit := Finset.sum_sdiff hsub (f := fun p : ℕ => Real.log (p:ℝ))
  have hsum_eq : ∑ p ∈ S, Real.log (p:ℝ) = Chebyshev.theta (2*(P:ℝ)) - Chebyshev.theta (P:ℝ) := by
    rw [hSeq, ht2, ht1]
    linarith only [hsplit]
  have hcard : ∑ p ∈ S, Real.log (p:ℝ) ≤ (S.card : ℝ) * Real.log (2*(P:ℝ)) := by
    calc ∑ p ∈ S, Real.log (p:ℝ) ≤ ∑ p ∈ S, Real.log (2*(P:ℝ)) := by
          apply Finset.sum_le_sum
          intro p hp
          obtain ⟨hpIoc, hpprime⟩ := Finset.mem_filter.mp hp
          have h1 : (0:ℝ) < (p:ℝ) := by exact_mod_cast hpprime.pos
          have h2 : (p:ℝ) ≤ 2*(P:ℝ) := by
            have h := (Finset.mem_Ioc.mp hpIoc).2
            exact_mod_cast h
          exact Real.log_le_log h1 h2
      _ = (S.card : ℝ) * Real.log (2*(P:ℝ)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  rw [div_le_iff₀ hlogpos]
  linarith only [hsum_eq.le, hcard, burgess_theta_interval_lower hP, hsum_eq, hP]

lemma burgess_card_primeFactors_mul_log_two_le {q : ℕ} (hq : 0 < q) :
    (q.primeFactors.card : ℝ) * Real.log 2 ≤ Real.log (q:ℝ) := by
  have hqpos : (0:ℝ) < (q:ℝ) := by exact_mod_cast hq
  have hstep : ∑ p ∈ q.primeFactors, Real.log 2 ≤ ∑ p ∈ q.primeFactors, Real.log (p:ℝ) := by
    apply Finset.sum_le_sum
    intro p hp
    have hp2 : (2:ℝ) ≤ (p:ℝ) := by
      have h := (Nat.mem_primeFactors.mp hp).1.two_le
      exact_mod_cast h
    exact Real.log_le_log (by norm_num) hp2
  have hsum1 : ∑ p ∈ q.primeFactors, Real.log 2 = (q.primeFactors.card : ℝ) * Real.log 2 := by
    rw [Finset.sum_const, nsmul_eq_mul]
  have hne : ∀ p ∈ q.primeFactors, (p:ℝ) ≠ 0 := by
    intro p hp
    have h := (Nat.mem_primeFactors.mp hp).1.pos
    exact_mod_cast (ne_of_gt h)
  have hlogprod : ∑ p ∈ q.primeFactors, Real.log (p:ℝ)
      = Real.log (((q.primeFactors).prod (fun p => p) : ℕ) : ℝ) := by
    push_cast
    rw [Real.log_prod hne]
  have hdvd : ((q.primeFactors).prod (fun p => p)) ∣ q := Nat.prod_primeFactors_dvd q
  have hle : ((q.primeFactors).prod (fun p => p)) ≤ q := Nat.le_of_dvd hq hdvd
  have hposprod : (0:ℝ) < (((q.primeFactors).prod (fun p => p):ℕ):ℝ) := by
    have h : 0 < (q.primeFactors).prod (fun p => p) :=
      Finset.prod_pos (fun p hp => (Nat.mem_primeFactors.mp hp).1.pos)
    exact_mod_cast h
  have hlogprod2 : Real.log ((((q.primeFactors).prod (fun p => p):ℕ)):ℝ) ≤ Real.log (q:ℝ) :=
    Real.log_le_log hposprod (by exact_mod_cast hle)
  rw [← hlogprod] at hlogprod2
  rw [hsum1] at hstep
  linarith only [hstep, hlogprod2]

lemma burgess_omega_bound {q P : ℕ} (hq : 0 < q) (hP : 2^64 ≤ P) (hPq : q ≤ P^8) :
    (q.primeFactors.card : ℝ) * Real.log (2*(P:ℝ)) ≤ (7/128) * (P:ℝ) := by
  have hP1 : (1:ℝ) ≤ (P:ℝ) := burgess_one_le_P hP
  have hPpos : (0:ℝ) < (P:ℝ) := by linarith only [hP1]
  have hqpos : (0:ℝ) < (q:ℝ) := by exact_mod_cast hq
  have hL2 : (0.6931:ℝ) ≤ Real.log 2 := by linarith only [Real.log_two_gt_d9]
  have hcard2 : (q.primeFactors.card : ℝ) * Real.log 2 ≤ Real.log (q:ℝ) :=
    burgess_card_primeFactors_mul_log_two_le hq
  have hlogq : Real.log (q:ℝ) ≤ 8 * Real.log (P:ℝ) := by
    have hqP : (q:ℝ) ≤ (P:ℝ)^8 := by
      have h : (q:ℝ) ≤ ((P^8 : ℕ):ℝ) := by exact_mod_cast hPq
      rwa [Nat.cast_pow] at h
    have h1 : Real.log (q:ℝ) ≤ Real.log ((P:ℝ)^8) := Real.log_le_log hqpos hqP
    rw [Real.log_pow] at h1
    push_cast at h1
    linarith only [h1]
  have hlogP : Real.log (P:ℝ) ≤ 4 * (P:ℝ)^(1/4:ℝ) := burgess_log_le_four_rpow_quarter _ hP1
  have hlog2P : Real.log (2*(P:ℝ)) ≤ 8 * (P:ℝ)^(1/4:ℝ) := burgess_log_two_mul_le_eight hP1
  have hlog2Pnn : (0:ℝ) ≤ Real.log (2*(P:ℝ)) := Real.log_nonneg (by linarith only [hP1])
  have hq14 : (0:ℝ) < (P:ℝ)^(1/4:ℝ) := Real.rpow_pos_of_pos hPpos _
  have h1 : (q.primeFactors.card : ℝ) * Real.log 2 ≤ 8 * Real.log (P:ℝ) := le_trans hcard2 hlogq
  have hstep1 : (q.primeFactors.card : ℝ) * Real.log 2 * Real.log (2*(P:ℝ))
      ≤ 8 * Real.log (P:ℝ) * Real.log (2*(P:ℝ)) :=
    mul_le_mul_of_nonneg_right h1 hlog2Pnn
  have hstep2 : 8 * Real.log (P:ℝ) * Real.log (2*(P:ℝ)) ≤ 256 * (P:ℝ)^(1/2:ℝ) := by
    have h4 : 8 * Real.log (P:ℝ) ≤ 32 * (P:ℝ)^(1/4:ℝ) := by linarith only [hlogP]
    have h5 : 8 * Real.log (P:ℝ) * Real.log (2*(P:ℝ))
        ≤ (32 * (P:ℝ)^(1/4:ℝ)) * (8 * (P:ℝ)^(1/4:ℝ)) :=
      mul_le_mul h4 hlog2P hlog2Pnn (by linarith only [hq14])
    have h6 : (32 * (P:ℝ)^(1/4:ℝ)) * (8 * (P:ℝ)^(1/4:ℝ)) = 256 * (P:ℝ)^(1/2:ℝ) := by
      have hp : (P:ℝ)^(1/4:ℝ) * (P:ℝ)^(1/4:ℝ) = (P:ℝ)^(1/2:ℝ) := by
        rw [← Real.rpow_add hPpos, show ((1:ℝ)/4 + 1/4) = (1/2:ℝ) by norm_num]
      linear_combination (256:ℝ) * hp
    linarith only [h5, h6.le]
  have hmain : (q.primeFactors.card : ℝ) * Real.log (2*(P:ℝ)) * Real.log 2
      ≤ 256 * (P:ℝ)^(1/2:ℝ) := by nlinarith only [hstep1, hstep2]
  have hlarge : 256 * (P:ℝ)^(1/2:ℝ) ≤ (7/128) * (P:ℝ) * Real.log 2 := by
    have hx := burgess_rpow_half_ge hP
    have hxx : ((P:ℝ)^(1/2:ℝ))^2 = (P:ℝ) := by
      rw [← Real.sqrt_eq_rpow, Real.sq_sqrt hPpos.le]
    nlinarith only [hx, hL2, hxx]
  have hgoal : (q.primeFactors.card : ℝ) * Real.log (2*(P:ℝ)) * Real.log 2
      ≤ (7/128) * (P:ℝ) * Real.log 2 := le_trans hmain hlarge
  exact le_of_mul_le_mul_right hgoal (by linarith only [hL2] : (0:ℝ) < Real.log 2)

theorem burgess_coprime_window_count_le {q P : ℕ} (hq : 0 < q) (hP : 2^64 ≤ P) (hPq : q ≤ P^8) :
    (P:ℝ) ≤ (300 * Real.log (2*(P:ℝ))) *
      (((Finset.Icc (P+1) (2*P)).filter (fun ℓ : ℕ => Nat.Coprime ℓ q)).card : ℝ) := by
  have hP1 : (1:ℝ) ≤ (P:ℝ) := burgess_one_le_P hP
  have hPpos : (0:ℝ) < (P:ℝ) := by linarith only [hP1]
  have hlogpos : (0:ℝ) < Real.log (2*(P:ℝ)) := Real.log_pos (by linarith only [hP1])
  have hIcceq : Finset.Icc (P+1) (2*P) = Finset.Ioc P (2*P) := by
    ext x; simp only [Finset.mem_Ioc, Finset.mem_Icc]; omega
  set A : Finset ℕ := (Finset.Icc (P+1) (2*P)).filter (fun p : ℕ => Nat.Prime p) with hA
  set B : Finset ℕ := (Finset.Icc (P+1) (2*P)).filter (fun ℓ : ℕ => Nat.Coprime ℓ q) with hB
  have hAIoc : A.card = ((Finset.Ioc P (2*P)).filter (fun p : ℕ => Nat.Prime p)).card := by
    rw [hA, hIcceq]
  have hprime : (7/64 : ℝ) * (P:ℝ) / Real.log (2*(P:ℝ)) ≤ (A.card : ℝ) := by
    rw [hAIoc]
    exact burgess_short_interval_prime_count_local P hP
  have homega : (q.primeFactors.card : ℝ) * Real.log (2*(P:ℝ)) ≤ (7/128) * (P:ℝ) :=
    burgess_omega_bound hq hP hPq
  have hsubset : A ⊆ B ∪ q.primeFactors := by
    intro p hp
    have hpprime : Nat.Prime p := (Finset.mem_filter.mp hp).2
    have hpIcc := (Finset.mem_filter.mp hp).1
    by_cases hc : Nat.Coprime p q
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hpIcc, hc⟩)
    · refine Finset.mem_union_right _ ?_
      rw [Nat.mem_primeFactors]
      refine ⟨hpprime, ?_, hq.ne'⟩
      by_contra h
      exact hc ((hpprime.coprime_iff_not_dvd).mpr h)
  have hAcard : A.card ≤ B.card + (q.primeFactors).card :=
    le_trans (Finset.card_le_card hsubset) (Finset.card_union_le _ _)
  have h1 : (A.card : ℝ) ≤ (B.card : ℝ) + (q.primeFactors.card : ℝ) := by exact_mod_cast hAcard
  rw [div_le_iff₀ hlogpos] at hprime
  have hLnn : (0:ℝ) ≤ Real.log (2*(P:ℝ)) := le_of_lt hlogpos
  have h1L : (A.card : ℝ) * Real.log (2*(P:ℝ))
      ≤ ((B.card : ℝ) + (q.primeFactors.card : ℝ)) * Real.log (2*(P:ℝ)) :=
    mul_le_mul_of_nonneg_right h1 hLnn
  have hALB : (7/128) * (P:ℝ) ≤ (B.card : ℝ) * Real.log (2*(P:ℝ)) := by
    nlinarith only [hprime, h1L, homega]
  have hfin : (P:ℝ) ≤ 300 * Real.log (2*(P:ℝ)) * (B.card : ℝ) := by nlinarith only [hALB, hP1]
  rw [hB]
  exact hfin

private lemma burgess_core_gen_tail (Cm : ℝ) (hCm1 : 1 ≤ Cm) (k : ℕ) (hk2 : 2 ≤ k) {q : ℕ} (hp0 : (0:ℝ) < (q:ℝ))
    (H : ℕ) (hHqos : (0:ℝ) < (H:ℝ)) (hL1 : (1:ℝ) ≤ Real.log q) (CL : ℝ) (hCL0 : 0 ≤ CL)
    (X : ℝ) (hX : 0 ≤ X)
    (hpow : X^(2*k)
      ≤ CL^(2*k) * (2^68 * Cm * (H:ℝ)^(2*k-2) * (q:ℝ)^(((k:ℝ)+1)/(2*(k:ℝ))) * (Real.log q)^(10*k+17))) :
    X ≤ 2^70 * CL * Cm * (q:ℝ)^((k+1)/(4*k^2:ℝ)) * (H:ℝ)^(1 - 1/(k:ℝ)) * (Real.log q)^(10*k+20) := by
  have hk1 : 1 ≤ k := by omega
  have hkpos : (0:ℝ) < (k:ℝ) := by exact_mod_cast (show 0 < k by omega)
  -- ### extract the 2k-th root
  have hRHSnn : (0:ℝ) ≤ 2^70 * Cm * (q:ℝ)^((k+1)/(4*k^2:ℝ)) * (H:ℝ)^(1 - 1/(k:ℝ)) * (Real.log q)^(10*k+20) := by
    have h1 : (0:ℝ) ≤ (q:ℝ)^((k+1)/(4*k^2:ℝ)) := Real.rpow_nonneg hp0.le _
    have h2 : (0:ℝ) ≤ (H:ℝ)^(1 - 1/(k:ℝ)) := Real.rpow_nonneg hHqos.le _
    have h3 : (0:ℝ) ≤ (Real.log q)^(10*k+20) := by positivity
    positivity
  have hsq : 2^68 * Cm * (H:ℝ)^(2*k-2) * (q:ℝ)^(((k:ℝ)+1)/(2*(k:ℝ))) * (Real.log q)^(10*k+17)
      ≤ (2^70 * Cm * (q:ℝ)^((k+1)/(4*k^2:ℝ)) * (H:ℝ)^(1 - 1/(k:ℝ)) * (Real.log q)^(10*k+20))^(2*k) := by
    have hp2 : ((q:ℝ)^((k+1)/(4*k^2:ℝ)))^(2*k) = (q:ℝ)^(((k:ℝ)+1)/(2*(k:ℝ))) := by
      have hpe : ((k:ℝ)+1)/(4*(k:ℝ)^2) * ((2*k:ℕ):ℝ) = ((k:ℝ)+1)/(2*(k:ℝ)) := by
        have hkne : (k:ℝ) ≠ 0 := ne_of_gt hkpos
        push_cast
        field_simp
        ring
      rw [← Real.rpow_natCast (x := (q:ℝ)^((k+1)/(4*k^2:ℝ))) (n := 2*k), ← Real.rpow_mul hp0.le, hpe]
    have hH2' : ((H:ℝ)^(1 - 1/(k:ℝ)))^(2*k) = (H:ℝ)^(2*k-2) := by
      have hHe : (1 - 1/(k:ℝ)) * ((2*k:ℕ):ℝ) = ((2*k-2:ℕ):ℝ) := by
        have hkne : (k:ℝ) ≠ 0 := ne_of_gt hkpos
        have hcast : ((2*k-2:ℕ):ℝ) = 2*(k:ℝ) - 2 := by
          rw [Nat.cast_sub (by omega : 2 ≤ 2*k)]; push_cast; ring
        rw [hcast]
        push_cast
        field_simp
      rw [← Real.rpow_natCast (x := (H:ℝ)^(1 - 1/(k:ℝ))) (n := 2*k), ← Real.rpow_mul hHqos.le, hHe,
        Real.rpow_natCast]
    have hL2 : ((Real.log q)^(10*k+20))^(2*k) = (Real.log q)^((10*k+20)*(2*k)) :=
      (pow_mul (Real.log q) (10*k+20) (2*k)).symm
    have hB : (2^70 * Cm * (q:ℝ)^((k+1)/(4*k^2:ℝ)) * (H:ℝ)^(1 - 1/(k:ℝ)) * (Real.log q)^(10*k+20))^(2*k)
        = 2^(70*(2*k)) * Cm^(2*k) * (q:ℝ)^(((k:ℝ)+1)/(2*(k:ℝ))) * (H:ℝ)^(2*k-2)
          * (Real.log q)^((10*k+20)*(2*k)) := by
      rw [show 2^70 * Cm * (q:ℝ)^((k+1)/(4*k^2:ℝ)) * (H:ℝ)^(1 - 1/(k:ℝ)) * (Real.log q)^(10*k+20)
          = (2^70 * Cm) * ((q:ℝ)^((k+1)/(4*k^2:ℝ)) * ((H:ℝ)^(1 - 1/(k:ℝ)) * (Real.log q)^(10*k+20))) from by ring]
      simp only [mul_pow]
      rw [← pow_mul, hp2, hH2', hL2]
      ring
    rw [hB]
    have hc : (2:ℝ)^68 * Cm ≤ 2^(70*(2*k)) * Cm^(2*k) := by
      have h2 : (2:ℝ)^68 ≤ 2^(70*(2*k)) :=
        pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) (by omega : 68 ≤ 70*(2*k))
      have h3 : Cm ≤ Cm^(2*k) := by
        have := pow_le_pow_right₀ hCm1 (show 1 ≤ 2*k by omega)
        simpa using this
      exact mul_le_mul h2 h3 (le_trans zero_le_one hCm1) (by positivity)
    have hL : (Real.log q)^(10*k+17) ≤ (Real.log q)^((10*k+20)*(2*k)) :=
      pow_le_pow_right₀ hL1 (by nlinarith only [hk1])
    have h2 : (H:ℝ)^(2*k-2) * (q:ℝ)^(((k:ℝ)+1)/(2*(k:ℝ))) * (Real.log q)^(10*k+17)
        ≤ (H:ℝ)^(2*k-2) * (q:ℝ)^(((k:ℝ)+1)/(2*(k:ℝ))) * (Real.log q)^((10*k+20)*(2*k)) :=
      mul_le_mul_of_nonneg_left hL (by positivity)
    calc 2^68 * Cm * (H:ℝ)^(2*k-2) * (q:ℝ)^(((k:ℝ)+1)/(2*(k:ℝ))) * (Real.log q)^(10*k+17)
        = (2^68 * Cm) * ((H:ℝ)^(2*k-2) * (q:ℝ)^(((k:ℝ)+1)/(2*(k:ℝ))) * (Real.log q)^(10*k+17)) := by ring
      _ ≤ 2^(70*(2*k)) * Cm^(2*k) * ((H:ℝ)^(2*k-2) * (q:ℝ)^(((k:ℝ)+1)/(2*(k:ℝ))) * (Real.log q)^((10*k+20)*(2*k))) :=
            mul_le_mul hc h2 (by positivity) (by positivity)
      _ = 2^(70*(2*k)) * Cm^(2*k) * (q:ℝ)^(((k:ℝ)+1)/(2*(k:ℝ))) * (H:ℝ)^(2*k-2) * (Real.log q)^((10*k+20)*(2*k)) := by ring
  have hfin1 : X
      ≤ CL * (2^68 * Cm * (H:ℝ)^(2*k-2) * (q:ℝ)^(((k:ℝ)+1)/(2*(k:ℝ))) * (Real.log q)^(10*k+17))^(((2*k:ℕ):ℝ)⁻¹) := by
    have h2k : (0:ℝ) ≤ X^(2*k) := pow_nonneg hX _
    have hY0 : (0:ℝ) ≤ 2^68 * Cm * (H:ℝ)^(2*k-2) * (q:ℝ)^(((k:ℝ)+1)/(2*(k:ℝ))) * (Real.log q)^(10*k+17) := by positivity
    have h1 := Real.rpow_le_rpow h2k hpow (by positivity : (0:ℝ) ≤ ((2*k:ℕ):ℝ)⁻¹)
    rw [Real.pow_rpow_inv_natCast hX (by omega : 2*k ≠ 0)] at h1
    rw [Real.mul_rpow (by positivity : (0:ℝ) ≤ CL^(2*k)) hY0] at h1
    rw [Real.pow_rpow_inv_natCast hCL0 (by omega : 2*k ≠ 0)] at h1
    exact h1
  refine hfin1.trans ?_
  have hinner : (2^68 * Cm * (H:ℝ)^(2*k-2) * (q:ℝ)^(((k:ℝ)+1)/(2*(k:ℝ))) * (Real.log q)^(10*k+17))^(((2*k:ℕ):ℝ)⁻¹)
      ≤ 2^70 * Cm * (q:ℝ)^((k+1)/(4*k^2:ℝ)) * (H:ℝ)^(1 - 1/(k:ℝ)) * (Real.log q)^(10*k+20) := by
    calc (2^68 * Cm * (H:ℝ)^(2*k-2) * (q:ℝ)^(((k:ℝ)+1)/(2*(k:ℝ))) * (Real.log q)^(10*k+17))^(((2*k:ℕ):ℝ)⁻¹)
        ≤ ((2^70 * Cm * (q:ℝ)^((k+1)/(4*k^2:ℝ)) * (H:ℝ)^(1 - 1/(k:ℝ)) * (Real.log q)^(10*k+20))^(2*k))^(((2*k:ℕ):ℝ)⁻¹) :=
          Real.rpow_le_rpow (by positivity) hsq (by positivity)
      _ = 2^70 * Cm * (q:ℝ)^((k+1)/(4*k^2:ℝ)) * (H:ℝ)^(1 - 1/(k:ℝ)) * (Real.log q)^(10*k+20) :=
          Real.pow_rpow_inv_natCast hRHSnn (by omega : 2*k ≠ 0)
  calc CL * (2^68 * Cm * (H:ℝ)^(2*k-2) * (q:ℝ)^(((k:ℝ)+1)/(2*(k:ℝ))) * (Real.log q)^(10*k+17))^(((2*k:ℕ):ℝ)⁻¹)
      ≤ CL * (2^70 * Cm * (q:ℝ)^((k+1)/(4*k^2:ℝ)) * (H:ℝ)^(1 - 1/(k:ℝ)) * (Real.log q)^(10*k+20)) :=
        mul_le_mul_of_nonneg_left hinner hCL0
    _ = 2^70 * CL * Cm * (q:ℝ)^((k+1)/(4*k^2:ℝ)) * (H:ℝ)^(1 - 1/(k:ℝ)) * (Real.log q)^(10*k+20) := by ring

private lemma burgess_core_gen_aux (k : ℕ) (hk2 : 2 ≤ k) (hk3 : k ≤ 3) : (2:ℝ)^(2*k) * 2^(2*k-2) * 20000 * 4 * 2^(2*k) * 4 * 2 * 16^(2*k) * 2^(2*k) ≤ 2^68 := by
  have h1 : (2:ℝ)^(2*k) ≤ 2^6 := pow_le_pow_right₀ (by norm_num) (by omega)
  have h2 : (2:ℝ)^(2*k-2) ≤ 2^4 := pow_le_pow_right₀ (by norm_num) (by omega)
  have h3 : (16:ℝ)^(2*k) ≤ 2^24 := by
    rw [show (16:ℝ) = 2^4 by norm_num, ← pow_mul]
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  have h4 : (2:ℝ)^(2*k) ≤ 2^6 := h1
  have h5 : (2:ℝ)^(2*k) ≤ 2^6 := h1
  have h6 : (20000:ℝ) * 4 * 4 * 2 ≤ 2^20 := by norm_num
  calc (2:ℝ)^(2*k) * 2^(2*k-2) * 20000 * 4 * 2^(2*k) * 4 * 2 * 16^(2*k) * 2^(2*k)
      = ((2:ℝ)^(2*k) * 2^(2*k-2) * 2^(2*k) * 16^(2*k) * 2^(2*k)) * (20000 * 4 * 4 * 2) := by ring
    _ ≤ (2^6 * 2^4 * 2^6 * 2^24 * 2^6) * 2^20 := by gcongr
    _ ≤ 2^68 := by norm_num

lemma burgess_core_gen (Cm : ℝ) (hCm1 : 1 ≤ Cm) (k : ℕ) (hk2 : 2 ≤ k) (hk3 : k ≤ 3)
    {q : ℕ} [NeZero q] (hq60 : 2^60 ≤ q) (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (hmom : ∀ L : ℕ, L ≤ q →
      ∑ m ∈ Finset.range q, ‖cSum χ (m:ℤ) ((m:ℤ) + L)‖^(2*k)
        ≤ Cm * ((q:ℝ) * (L:ℝ)^k + (L:ℝ)^(2*k) * Real.sqrt q))
    (N : ℤ) (hN0 : 0 ≤ N) (hNq : N < (q:ℤ)) (H : ℕ) (hH1 : 1 ≤ H) (hHq : H ≤ q)
    (hHlo : (q:ℝ)^((k+1)/(4*k:ℝ)) ≤ (H:ℝ))
    (hHhi : (H:ℝ) ≤ (q:ℝ)^((2*k+1)/(4*k:ℝ)) * (Real.log q)^(4*k+8))
    (CL : ℝ) (hCL0 : 0 ≤ CL)
    (hsplit : (Nat.floor ((H:ℝ) * (q:ℝ)^(-(1/(2*(k:ℝ))))) + 1 : ℝ) * ‖cSum χ N (N + (H:ℤ))‖
      ≤ CL * ∑ x ∈ objFinset (Nat.floor ((H:ℝ) * (q:ℝ)^(-(1/(2*(k:ℝ))))) + 1),
          ‖cSum χ (oLo N q x.1 x.2) (oHi N q H x.1 x.2)‖) :
    ‖cSum χ N (N + (H:ℤ))‖ ≤ 2^70 * CL * Cm * (q:ℝ)^((k+1)/(4*k^2:ℝ)) * (H:ℝ)^(1 - 1/(k:ℝ))
      * (Real.log q)^(10*k+20) := by
  have hk1 : 1 ≤ k := by omega
  have hkpos : (0:ℝ) < (k:ℝ) := by exact_mod_cast (show 0 < k by omega)
  have hk3R : (k:ℝ) ≤ 3 := by exact_mod_cast hk3
  have hkR2 : (2:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk2
  have hp0 : (0:ℝ) < (q:ℝ) := by exact_mod_cast (show 0 < q by omega)
  have hp1 : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast (show 1 ≤ q by omega)
  have hp2 : 2 ≤ q := by omega
  have hpz : (0:ℤ) < (q:ℤ) := by exact_mod_cast (show 0 < q by omega)
  have hHqos : (0:ℝ) < (H:ℝ) := by exact_mod_cast hH1
  have hHnn : (0:ℝ) ≤ (H:ℝ) := le_of_lt hHqos
  have hp60r : ((2:ℝ)^60) ≤ (q:ℝ) := by
    have h : ((2^60 : ℕ) : ℝ) = (2:ℝ)^60 := by push_cast; ring
    rw [← h]; exact_mod_cast hq60
  have hL1 : (1:ℝ) ≤ Real.log q := by
    rw [← Real.log_exp 1]
    apply Real.log_le_log (Real.exp_pos 1)
    calc Real.exp 1 ≤ 4 := le_of_lt (lt_trans Real.exp_one_lt_three (by norm_num))
      _ ≤ (2:ℝ)^60 := by norm_num
      _ = ((2^60 : ℕ) : ℝ) := by norm_num
      _ ≤ (q:ℝ) := by exact_mod_cast hq60
  have hLpos : (0:ℝ) < Real.log q := lt_of_lt_of_le one_pos hL1
  -- ### rpow facts about q
  have h1024le : (1024:ℝ) ≤ (q:ℝ)^(1/(2*(k:ℝ))) := by
    have hexp_le : (1:ℝ)/6 ≤ 1/(2*(k:ℝ)) := by
      rw [div_le_div_iff₀ (by norm_num) (by positivity)]
      push_cast
      linarith only [hk3R]
    have h1 : (1024:ℝ) ≤ ((2:ℝ)^60)^((1:ℝ)/6) := by
      rw [← Real.rpow_natCast_mul (by norm_num : (0:ℝ) ≤ 2) 60 (1/6)]
      have he : (↑(60:ℕ) : ℝ) * ((1:ℝ)/6) = 10 := by norm_num
      rw [he]
      norm_num
    exact le_trans h1 (le_trans
      (Real.rpow_le_rpow (x := (2:ℝ)^60) (y := (q:ℝ)) (z := (1:ℝ)/6) (by positivity) hp60r (by norm_num))
      (Real.rpow_le_rpow_of_exponent_le hp1 hexp_le))
  have h8le : (8:ℝ) ≤ (q:ℝ)^(1/(2*(k:ℝ))) := le_trans (by norm_num) h1024le
  have h64le : (64:ℝ) ≤ (q:ℝ)^(1/(2*(k:ℝ))) := le_trans (by norm_num) h1024le
  have h2le : (2:ℝ) ≤ (q:ℝ)^(1/(2*(k:ℝ))) := le_trans (by norm_num) h1024le
  have hexp_le_half : 1/(2*(k:ℝ)) ≤ (1:ℝ)/2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    push_cast; linarith only [hkR2]
  have hpHalf : (q:ℝ)^(1/(2*(k:ℝ))) ≤ (q:ℝ)^((1:ℝ)/2) :=
    Real.rpow_le_rpow_of_exponent_le hp1 hexp_le_half
  have hp_sqrt_ge : (2:ℝ)^30 ≤ (q:ℝ)^((1:ℝ)/2) := by
    have h1 : (2:ℝ)^30 ≤ ((2:ℝ)^60)^((1:ℝ)/2) := by
      rw [← Real.rpow_natCast_mul (by norm_num : (0:ℝ) ≤ 2) 60 (1/2)]
      have he : (↑(60:ℕ) : ℝ) * ((1:ℝ)/2) = 30 := by norm_num
      rw [he]
      norm_num
    exact le_trans h1
      (Real.rpow_le_rpow (x := (2:ℝ)^60) (y := (q:ℝ)) (z := (1:ℝ)/2) (by positivity) hp60r (by norm_num))
  have h16sqrt : (16:ℝ) ≤ (q:ℝ)^((1:ℝ)/2) := le_trans (by norm_num) hp_sqrt_ge
  have h64sqrt : (64:ℝ) ≤ (q:ℝ)^((1:ℝ)/2) := le_trans (by norm_num) hp_sqrt_ge
  have h16p : (16:ℝ) * (q:ℝ)^(1/(2*(k:ℝ))) ≤ (q:ℝ) := by
    have h1 : (16:ℝ) * (q:ℝ)^(1/(2*(k:ℝ))) ≤ (q:ℝ)^((1:ℝ)/2) * (q:ℝ)^((1:ℝ)/2) :=
      mul_le_mul h16sqrt hpHalf (Real.rpow_nonneg hp0.le (1/(2*(k:ℝ)))) (Real.rpow_nonneg hp0.le ((1:ℝ)/2))
    have h2 : (q:ℝ)^((1:ℝ)/2) * (q:ℝ)^((1:ℝ)/2) = (q:ℝ) := by
      rw [← Real.rpow_add hp0]; norm_num
    linarith only [h1, h2]
  have h4p : (4:ℝ) * (q:ℝ)^(1 - 1/(2*(k:ℝ))) < (q:ℝ) := by
    have hsub : (q:ℝ)^(1 - 1/(2*(k:ℝ))) = (q:ℝ) / (q:ℝ)^(1/(2*(k:ℝ))) := by
      rw [Real.rpow_sub hp0, Real.rpow_one]
    have h1 : (q:ℝ) / (q:ℝ)^(1/(2*(k:ℝ))) ≤ (q:ℝ) / 8 :=
      div_le_div_of_nonneg_left hp0.le (by norm_num : (0:ℝ) < 8) h8le
    have h2 : (4:ℝ) * ((q:ℝ) / 8) = (q:ℝ) / 2 := by ring
    have h3 : (q:ℝ) / 2 < (q:ℝ) := by linarith only [hp60r]
    linarith only [hsub, h1, h2, h3]
  -- ### A and P
  set A : ℝ := (H:ℝ) * (q:ℝ)^(-(1/(2*(k:ℝ)))) with hAdef
  have hexp2 : 1/(2*(k:ℝ)) ≤ ((k:ℝ)+1)/(4*(k:ℝ)) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    push_cast; nlinarith only [hkR2]
  have hHlo' : (q:ℝ)^(1/(2*(k:ℝ))) ≤ (H:ℝ) :=
    le_trans (Real.rpow_le_rpow_of_exponent_le hp1 hexp2) hHlo
  have hA1 : 1 ≤ A := by
    have h := rpow_mul_inv_self hp0 (1/(2*(k:ℝ)))
    rw [hAdef]
    calc (1:ℝ) = (q:ℝ)^(1/(2*(k:ℝ))) * (q:ℝ)^(-(1/(2*(k:ℝ)))) := h.symm
      _ ≤ (H:ℝ) * (q:ℝ)^(-(1/(2*(k:ℝ)))) :=
          mul_le_mul_of_nonneg_right hHlo' (Real.rpow_nonneg hp0.le _)
  have hAnneg : (0:ℝ) ≤ A := le_trans zero_le_one hA1
  have hA2H : 2 * A ≤ (H:ℝ) := by
    have hpinv : (q:ℝ)^(-(1/(2*(k:ℝ)))) ≤ (1:ℝ)/2 := by
      rw [Real.rpow_neg hp0.le, inv_eq_one_div]
      exact le_trans (one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 8) h8le) (by norm_num)
    rw [hAdef]
    have h1 : (2:ℝ) * ((H:ℝ) * (q:ℝ)^(-(1/(2*(k:ℝ)))))
        = (H:ℝ) * (2 * (q:ℝ)^(-(1/(2*(k:ℝ))))) := by ring
    rw [h1]
    calc (H:ℝ) * (2 * (q:ℝ)^(-(1/(2*(k:ℝ))))) ≤ (H:ℝ) * 1 := by
          apply mul_le_mul_of_nonneg_left _ hHnn
          linarith only [hpinv]
      _ = (H:ℝ) := by ring
  set P : ℕ := Nat.floor A + 1 with hPdef
  have hP1 : 1 ≤ P := by rw [hPdef]; omega
  have hPpos : (0:ℝ) < (P:ℝ) := by exact_mod_cast hP1
  have hPlow : A ≤ (P:ℝ) := by
    rw [hPdef]; push_cast
    exact le_of_lt (Nat.lt_floor_add_one A)
  have hPhigh : (P:ℝ) ≤ 2 * A := by
    rw [hPdef]; push_cast
    have h := Nat.floor_le hAnneg
    linarith only [hA1, h]
  have hPleH : (P:ℝ) ≤ (H:ℝ) := by linarith only [hPhigh, hA2H]
  have hPx' : 2 * A = 2 * (H:ℝ) * (q:ℝ)^(-(1/(2*(k:ℝ)))) := by rw [hAdef]; ring
  have hPx : (P:ℝ) ≤ 2 * (H:ℝ) * (q:ℝ)^(-(1/(2*(k:ℝ)))) := by linarith only [hPhigh, hPx']
  have h2P : 2*P < q := by
    have h2 : (4:ℝ) * A < (q:ℝ) := by
      rw [hAdef]
      have h3 : (4:ℝ) * ((H:ℝ) * (q:ℝ)^(-(1/(2*(k:ℝ)))))
          ≤ 4 * ((q:ℝ) * (q:ℝ)^(-(1/(2*(k:ℝ))))) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 4)
        exact mul_le_mul_of_nonneg_right (show (H:ℝ) ≤ (q:ℝ) by exact_mod_cast hHq)
          (Real.rpow_nonneg hp0.le (-(1/(2*(k:ℝ)))))
      have h4 : (4:ℝ) * ((q:ℝ) * (q:ℝ)^(-(1/(2*(k:ℝ))))) = 4 * (q:ℝ)^(1 - 1/(2*(k:ℝ))) := by
        rw [show (q:ℝ)^(1 - 1/(2*(k:ℝ))) = (q:ℝ) * (q:ℝ)^(-(1/(2*(k:ℝ)))) by
          rw [Real.rpow_sub hp0, Real.rpow_one, div_eq_mul_inv, Real.rpow_neg hp0.le]]
      linarith only [h3, h4, h4p]
    have : (2:ℝ)*(P:ℝ) < (q:ℝ) := by linarith only [hPhigh, h2]
    exact_mod_cast this
  -- ### the parameter hh
  set hh : ℕ := Nat.ceil ((H:ℝ)/(P:ℝ)) + 1 with hhhdef
  have hhhpos : 1 ≤ hh := by rw [hhhdef]; omega
  have hhhposR : (0:ℝ) < (hh:ℝ) := by exact_mod_cast hhhpos
  have hhhge : (H:ℝ)/(P:ℝ) ≤ (hh:ℝ) := by
    rw [hhhdef]; push_cast
    have h := Nat.le_ceil ((H:ℝ)/(P:ℝ))
    linarith only [h]
  have hhhle : (hh:ℝ) ≤ (H:ℝ)/(P:ℝ) + 2 := by
    rw [hhhdef]; push_cast
    have h := Nat.ceil_lt_add_one (show (0:ℝ) ≤ (H:ℝ)/(P:ℝ) by positivity)
    linarith only [h]
  have hhdivP1 : (1:ℝ) ≤ (H:ℝ)/(P:ℝ) := by
    rw [le_div_iff₀ hPpos]; linarith only [hPleH]
  have hhlo : (H:ℝ)/(2*(P:ℝ)) ≤ (hh:ℝ) := by
    have h2 : (H:ℝ)/(2*(P:ℝ)) ≤ (H:ℝ)/(P:ℝ) :=
      div_le_div_of_nonneg_left hHnn (by linarith only [hPpos]) (by linarith only [hPpos])
    linarith only [hhhge, h2]
  have hhhle2 : (hh:ℝ) ≤ 4 * (q:ℝ)^(1/(2*(k:ℝ))) := by
    have h1 : (H:ℝ)/(P:ℝ) ≤ (q:ℝ)^(1/(2*(k:ℝ))) := by
      rw [div_le_iff₀ hPpos]
      have hmul : A * (q:ℝ)^(1/(2*(k:ℝ))) = (H:ℝ) := by
        rw [hAdef]; exact mul_rpow_neg_mul q H hp0 _
      rw [← hmul]
      calc A * (q:ℝ)^(1/(2*(k:ℝ))) ≤ (P:ℝ) * (q:ℝ)^(1/(2*(k:ℝ))) :=
            mul_le_mul_of_nonneg_right hPlow (Real.rpow_nonneg hp0.le _)
        _ = (q:ℝ)^(1/(2*(k:ℝ))) * (P:ℝ) := by ring
    have h3 : (1:ℝ) ≤ (q:ℝ)^(1/(2*(k:ℝ))) := le_trans (by norm_num) h2le
    linarith only [hhhle, h1, h3]
  have hhh_le_p : (hh:ℝ) ≤ (q:ℝ) := by linarith only [hhhle2, h16p]
  -- ### dyadic parameters
  set t : ℕ := Nat.log2 (2*hh) + 1 with htdef
  set K : ℕ := 2^t with hKdef
  have h2hhpos : 0 < 2*hh := by omega
  have hhhge1 : (H:ℝ)/(P:ℝ) + 1 ≤ (hh:ℝ) := by
    rw [hhhdef]; push_cast
    have h := Nat.le_ceil ((H:ℝ)/(P:ℝ))
    linarith only [h]
  have hKge : 2*hh ≤ K := by
    rw [hKdef, htdef, Nat.log2_eq_log_two]
    have h := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) (2*hh)
    simp only [Nat.succ_eq_add_one] at h
    exact le_of_lt h
  have hKle : K ≤ 4*hh := by
    rw [hKdef, htdef, Nat.log2_eq_log_two, pow_succ]
    have h := Nat.pow_log_le_self 2 (show 2*hh ≠ 0 by omega)
    calc 2 ^ Nat.log 2 (2 * hh) * 2 ≤ (2*hh) * 2 := Nat.mul_le_mul_right 2 h
      _ = 4*hh := by ring
  have hKp : K ≤ q := by
    have h1 : (K:ℝ) ≤ 4*(hh:ℝ) := by exact_mod_cast hKle
    have h2 : (4:ℝ)*(hh:ℝ) ≤ 4 * (4 * (q:ℝ)^(1/(2*(k:ℝ)))) :=
      mul_le_mul_of_nonneg_left hhhle2 (by norm_num : (0:ℝ) ≤ 4)
    have h3 : (4:ℝ) * (4 * (q:ℝ)^(1/(2*(k:ℝ)))) = 16 * (q:ℝ)^(1/(2*(k:ℝ))) := by ring
    have : (K:ℝ) ≤ (q:ℝ) := by linarith only [h1, h2, h3, h16p]
    exact_mod_cast this
  -- ### H squared
  have hH2 : (H:ℝ)^2 ≤ (q:ℝ)^((2*(k:ℝ)+1)/(2*(k:ℝ))) * (Real.log q)^(8*k+16) := by
    have h1 := pow_le_pow_left₀ hHnn hHhi 2
    refine h1.trans (le_of_eq ?_)
    have hh1 : (((q:ℝ)^((2*(k:ℝ)+1)/(4*(k:ℝ)))))^2 = (q:ℝ)^((2*(k:ℝ)+1)/(2*(k:ℝ))) := by
      rw [← Real.rpow_natCast (x := (q:ℝ)^((2*(k:ℝ)+1)/(4*(k:ℝ)))) (n := 2),
        ← Real.rpow_mul hp0.le]
      congr 1
      push_cast
      ring
    have hh2 : ((Real.log q)^(4*k+8))^2 = (Real.log q)^(8*k+16) := by
      rw [← pow_mul]
      congr 1
      ring
    rw [mul_pow, hh1, hh2]
  -- ### object bounds for the Burgess principle
  have hlo : ∀ x ∈ objFinset P, -(2*(q:ℤ)) ≤ oLo N q x.1 x.2 - (hh:ℤ) ∧ oLo N q x.1 x.2 ≤ (q:ℤ) := by
    intro x hx
    obtain ⟨hx1, hx2, hx3⟩ := mem_objFinset.mp hx
    have hl1 : 1 ≤ x.1 := by omega
    have hL : (0:ℤ) < (x.1:ℤ) := by exact_mod_cast hl1
    have ha : (x.2:ℤ) ≤ (x.1:ℤ) := by exact_mod_cast (le_of_lt hx3)
    have haz : (0:ℤ) ≤ (x.2:ℤ) := Nat.cast_nonneg x.2
    have hap : (x.2:ℤ) * (q:ℤ) ≤ (x.1:ℤ) * (q:ℤ) :=
      mul_le_mul_of_nonneg_right ha (le_of_lt hpz)
    constructor
    · have key : (hh:ℤ) - 2*(q:ℤ) ≤ (N - (x.2:ℤ)*(q:ℤ)) / (x.1:ℤ) := by
        rw [Int.le_ediv_iff_mul_le hL]
        have hh1 : (hh:ℤ) * (x.1:ℤ) ≤ (q:ℤ) * (x.1:ℤ) := by
          apply mul_le_mul_of_nonneg_right _ (le_of_lt hL)
          exact_mod_cast hhh_le_p
        nlinarith only [hh1, hap, hN0]
      simp only [oLo]
      linarith only [key]
    · have h1 : N - (x.2:ℤ)*(q:ℤ) ≤ N := by nlinarith only [haz, le_of_lt hpz]
      have h2 : (1:ℤ) ≤ (x.1:ℤ) := by exact_mod_cast hl1
      have h3 : (q:ℤ) + 1 ≤ (q:ℤ) * (x.1:ℤ) + (x.1:ℤ) := by nlinarith only [h2, le_of_lt hpz]
      simp only [oLo]
      rw [Int.ediv_le_iff_le_mul hL]
      linarith only [hNq, h1, h3]
  have hlen : ∀ x ∈ objFinset P, oHi N q H x.1 x.2 - oLo N q x.1 x.2 ≤ (hh:ℤ) := by
    intro x hx
    obtain ⟨hx1, hx2, hx3⟩ := mem_objFinset.mp hx
    have hl1 : 1 ≤ x.1 := by omega
    have hL : (0:ℤ) < (x.1:ℤ) := by exact_mod_cast hl1
    have hPl : P ≤ x.1 := by omega
    have hPposZ : (0:ℤ) < (P:ℤ) := by exact_mod_cast hP1
    have hHlt : (H:ℤ) < (hh:ℤ)*(P:ℤ) := by
      have h1 : ((H:ℝ)/(P:ℝ) + 1) * (P:ℝ) ≤ (hh:ℝ) * (P:ℝ) :=
        mul_le_mul_of_nonneg_right hhhge1 hPpos.le
      have h2 : ((H:ℝ)/(P:ℝ) + 1) * (P:ℝ) = (H:ℝ) + (P:ℝ) := by
        field_simp
      rw [h2] at h1
      have : (H:ℝ) < (hh:ℝ) * (P:ℝ) := by linarith only [hPpos, h1]
      exact_mod_cast this
    have h2 : (H:ℤ) / (x.1:ℤ) + 1 ≤ (hh:ℤ) := by
      have h3 : (H:ℤ) / (x.1:ℤ) ≤ (hh:ℤ) - 1 := by
        rw [Int.ediv_le_iff_le_mul hL]
        have heq : ((hh:ℤ) - 1) * (x.1:ℤ) + (x.1:ℤ) = (hh:ℤ) * (x.1:ℤ) := by ring
        rw [heq]
        have h4 : (hh:ℤ) * (P:ℤ) ≤ (hh:ℤ) * (x.1:ℤ) :=
          mul_le_mul_of_nonneg_left (show (P:ℤ) ≤ (x.1:ℤ) by exact_mod_cast hPl)
            (Nat.cast_nonneg hh)
        linarith only [hHlt, h4]
      linarith only [h3]
    have hkey : (N + (H:ℤ) - (x.2:ℤ)*(q:ℤ))/(x.1:ℤ) - (N - (x.2:ℤ)*(q:ℤ))/(x.1:ℤ)
        ≤ (H:ℤ)/(x.1:ℤ) + 1 := by
      have h := Commons.NumberTheory.Auxiliary.ediv_add_sub_ediv_le hL (N - (x.2:ℤ)*(q:ℤ)) (H:ℤ) (Nat.cast_nonneg H)
      rw [show N - (x.2:ℤ)*(q:ℤ) + (H:ℤ) = N + (H:ℤ) - (x.2:ℤ)*(q:ℤ) by ring] at h
      exact h
    simp only [oHi, oLo]
    exact hkey.trans h2

  -- ### the Burgess chain
  have hsplitP : (P:ℝ) * ‖cSum χ N (N + (H:ℤ))‖
      ≤ CL * ∑ x ∈ objFinset P, ‖cSum χ (oLo N q x.1 x.2) (oHi N q H x.1 x.2)‖ := by
    rw [show (P:ℝ) = ((⌊A⌋₊ : ℝ) + 1) from by rw [hPdef]; push_cast; ring]
    exact hsplit
  have hprinc : (hh:ℝ) * (∑ x ∈ objFinset P, ‖cSum χ (oLo N q x.1 x.2) (oHi N q H x.1 x.2)‖)
      ≤ 2 * ∑ n ∈ Finset.Icc (-(2*(q:ℤ))) (q:ℤ), weightA N q hh P n * supShift χ n (2*hh) :=
    burgess_principle_gen χ N H P hh hP1 h2P hlo hlen
  have hcollnn : (0:ℝ) ≤ collCount N q hh P := by
    unfold collCount
    exact Finset.sum_nonneg (fun x _ => Finset.sum_nonneg (fun y _ => by split <;> norm_num))
  have hPhhS : (P:ℝ) * (hh:ℝ) * ‖cSum χ N (N + (H:ℤ))‖
      ≤ 2 * CL * ∑ n ∈ Finset.Icc (-(2*(q:ℤ))) (q:ℤ), weightA N q hh P n * supShift χ n (2*hh) := by
    calc (P:ℝ) * (hh:ℝ) * ‖cSum χ N (N + (H:ℤ))‖
        = (hh:ℝ) * ((P:ℝ) * ‖cSum χ N (N + (H:ℤ))‖) := by ring
      _ ≤ (hh:ℝ) * (CL * ∑ x ∈ objFinset P, ‖cSum χ (oLo N q x.1 x.2) (oHi N q H x.1 x.2)‖) :=
          mul_le_mul_of_nonneg_left hsplitP hhhposR.le
      _ = CL * ((hh:ℝ) * (∑ x ∈ objFinset P, ‖cSum χ (oLo N q x.1 x.2) (oHi N q H x.1 x.2)‖)) := by ring
      _ ≤ CL * (2 * ∑ n ∈ Finset.Icc (-(2*(q:ℤ))) (q:ℤ), weightA N q hh P n * supShift χ n (2*hh)) :=
          mul_le_mul_of_nonneg_left hprinc hCL0
      _ = 2 * CL * ∑ n ∈ Finset.Icc (-(2*(q:ℤ))) (q:ℤ), weightA N q hh P n * supShift χ n (2*hh) := by ring
  -- ### the three moment-type bounds
  have hAnn : ∀ n ∈ Finset.Icc (-(2*(q:ℤ))) (q:ℤ), 0 ≤ weightA N q hh P n :=
    fun n _ => weightA_nonneg N q hh P n
  have hMnn : ∀ n ∈ Finset.Icc (-(2*(q:ℤ))) (q:ℤ), 0 ≤ supShift χ n (2*hh) :=
    fun n _ => supShift_nonneg χ n (2*hh)
  have hAsum : ∑ n ∈ Finset.Icc (-(2*(q:ℤ))) (q:ℤ), weightA N q hh P n
      ≤ 2 * (P:ℝ)^2 * (hh:ℝ) := weight_sum_le N q hh P hP1 hlo
  have hA2sum : ∑ n ∈ Finset.Icc (-(2*(q:ℤ))) (q:ℤ), (weightA N q hh P n)^2
      ≤ (hh:ℝ) * collCount N q hh P := weight_sq_le N q hh P hP1 hlo
  have hKcast : ((K:ℕ):ℝ) = (2:ℝ)^t := by rw [hKdef]; push_cast; ring
  have hRK : ((2:ℝ)^t) = (K:ℝ) := hKcast.symm
  have hMsum : ∑ n ∈ Finset.Icc (-(2*(q:ℤ))) (q:ℤ), (supShift χ n (2*hh))^(2*k)
      ≤ 4 * ((t:ℝ)+1)^(2*k) * (4*Cm*((q:ℝ)*((K:ℝ))^k + ((K:ℝ))^(2*k)*Real.sqrt (q:ℝ))) := by
    have h := moment_W_le_gen χ Cm k hk2 hmom hh t K hKdef.symm hKge hKp
    simpa only [hRK] using h
  -- ### Holder + Cauchy-Schwarz in 2k-th power form
  have hSMsq : (∑ n ∈ Finset.Icc (-(2*(q:ℤ))) (q:ℤ),
        weightA N q hh P n * (supShift χ n (2*hh))^k)^2
      ≤ (∑ n ∈ Finset.Icc (-(2*(q:ℤ))) (q:ℤ), (weightA N q hh P n)^2)
        * (∑ n ∈ Finset.Icc (-(2*(q:ℤ))) (q:ℤ), (supShift χ n (2*hh))^(2*k)) := by
    have h := Commons.Analysis.MeanInequalities.sum_mul_sq_le (Finset.Icc (-(2*(q:ℤ))) (q:ℤ))
      (fun n => weightA N q hh P n) (fun n => supShift χ n (2*hh)) hAnn hMnn k
    have h2 : ∀ n, ((supShift χ n (2*hh))^k)^2 = (supShift χ n (2*hh))^(2*k) := by
      intro n
      rw [← pow_mul]
      congr 1
      omega
    simpa only [h2] using h
  have hhold : (∑ n ∈ Finset.Icc (-(2*(q:ℤ))) (q:ℤ),
        weightA N q hh P n * supShift χ n (2*hh))^(2*k)
      ≤ (∑ n ∈ Finset.Icc (-(2*(q:ℤ))) (q:ℤ), weightA N q hh P n)^(2*k-2)
        * ((∑ n ∈ Finset.Icc (-(2*(q:ℤ))) (q:ℤ), (weightA N q hh P n)^2)
          * (∑ n ∈ Finset.Icc (-(2*(q:ℤ))) (q:ℤ), (supShift χ n (2*hh))^(2*k))) := by
    have h1 := Commons.Analysis.MeanInequalities.sum_mul_pow_le (Finset.Icc (-(2*(q:ℤ))) (q:ℤ))
      (fun n => weightA N q hh P n) (fun n => supShift χ n (2*hh)) hAnn hMnn k hk1
    have h2 := pow_le_pow_left₀
      (pow_nonneg (Finset.sum_nonneg (fun n hn => mul_nonneg (hAnn n hn) (hMnn n hn))) k) h1 2
    rw [mul_pow] at h2
    have he1 : ((∑ n ∈ Finset.Icc (-(2*(q:ℤ))) (q:ℤ), weightA N q hh P n * supShift χ n (2*hh))^k)^2
        = (∑ n ∈ Finset.Icc (-(2*(q:ℤ))) (q:ℤ), weightA N q hh P n * supShift χ n (2*hh))^(2*k) := by
      rw [← pow_mul]; congr 1; omega
    have he2 : ((∑ n ∈ Finset.Icc (-(2*(q:ℤ))) (q:ℤ), weightA N q hh P n)^(k-1))^2
        = (∑ n ∈ Finset.Icc (-(2*(q:ℤ))) (q:ℤ), weightA N q hh P n)^(2*k-2) := by
      rw [← pow_mul]; congr 1; omega
    rw [he1, he2] at h2
    exact h2.trans (mul_le_mul_of_nonneg_left hSMsq
      (pow_nonneg (Finset.sum_nonneg hAnn) _))
  have hbig : ((P:ℝ) * (hh:ℝ) * ‖cSum χ N (N + (H:ℤ))‖)^(2*k)
      ≤ CL^(2*k) * (2^(2*k) * (2 * (P:ℝ)^2 * (hh:ℝ))^(2*k-2) * ((hh:ℝ) * collCount N q hh P)
        * (4 * ((t:ℝ)+1)^(2*k)
            * (4*Cm*((q:ℝ)*((K:ℝ))^k + ((K:ℝ))^(2*k)*Real.sqrt (q:ℝ))))) := by
    have h1 := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ (P:ℝ) * (hh:ℝ) * ‖cSum χ N (N + (H:ℤ))‖) hPhhS (2*k)
    have h2 : (2 * CL * ∑ n ∈ Finset.Icc (-(2*(q:ℤ))) (q:ℤ), weightA N q hh P n * supShift χ n (2*hh))^(2*k)
        = CL^(2*k) * (2^(2*k) * (∑ n ∈ Finset.Icc (-(2*(q:ℤ))) (q:ℤ), weightA N q hh P n * supShift χ n (2*hh))^(2*k)) := by
      rw [mul_pow, mul_pow]; ring
    rw [h2] at h1
    have h3 : (∑ n ∈ Finset.Icc (-(2*(q:ℤ))) (q:ℤ), weightA N q hh P n * supShift χ n (2*hh))^(2*k)
        ≤ (2 * (P:ℝ)^2 * (hh:ℝ))^(2*k-2) * ((hh:ℝ) * collCount N q hh P)
          * (4 * ((t:ℝ)+1)^(2*k)
              * (4*Cm*((q:ℝ)*((K:ℝ))^k + ((K:ℝ))^(2*k)*Real.sqrt (q:ℝ)))) := by
      refine hhold.trans ?_
      have h5 : (∑ n ∈ Finset.Icc (-(2*(q:ℤ))) (q:ℤ), (weightA N q hh P n)^2)
            * (∑ n ∈ Finset.Icc (-(2*(q:ℤ))) (q:ℤ), (supShift χ n (2*hh))^(2*k))
          ≤ ((hh:ℝ) * collCount N q hh P)
            * (4 * ((t:ℝ)+1)^(2*k)
              * (4*Cm*((q:ℝ)*((K:ℝ))^k + ((K:ℝ))^(2*k)*Real.sqrt (q:ℝ)))) :=
        mul_le_mul hA2sum hMsum (Finset.sum_nonneg (fun n hn => pow_nonneg (hMnn n hn) _))
          (mul_nonneg (by positivity) hcollnn)
      refine (mul_le_mul_of_nonneg_left h5
        (pow_nonneg (Finset.sum_nonneg hAnn) (2*k-2))).trans ?_
      refine (mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (Finset.sum_nonneg hAnn) hAsum (2*k-2))
        (by positivity : (0:ℝ) ≤ (hh:ℝ) * collCount N q hh P * (4 * ((t:ℝ)+1)^(2*k)
          * (4*Cm*((q:ℝ)*((K:ℝ))^k + ((K:ℝ))^(2*k)*Real.sqrt (q:ℝ)))))).trans_eq ?_
      rw [← mul_assoc]
    have h3b : CL^(2*k) * (2^(2*k) * ((2 * (P:ℝ)^2 * (hh:ℝ))^(2*k-2) * ((hh:ℝ) * collCount N q hh P)
          * (4 * ((t:ℝ)+1)^(2*k)
              * (4*Cm*((q:ℝ)*((K:ℝ))^k + ((K:ℝ))^(2*k)*Real.sqrt (q:ℝ))))))
        = CL^(2*k) * (2^(2*k) * (2 * (P:ℝ)^2 * (hh:ℝ))^(2*k-2) * ((hh:ℝ) * collCount N q hh P)
          * (4 * ((t:ℝ)+1)^(2*k)
              * (4*Cm*((q:ℝ)*((K:ℝ))^k + ((K:ℝ))^(2*k)*Real.sqrt (q:ℝ))))) := by ring
    refine h1.trans ?_
    exact (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h3 (by positivity : (0:ℝ) ≤ 2^(2*k)))
      (by positivity : (0:ℝ) ≤ CL^(2*k))).trans_eq h3b
  -- ### collCount bound
  set κ : ℝ := (P:ℝ)^2 * ((hh:ℝ)+2) / (q:ℝ) with hκdef
  have hhh2' : (hh:ℝ) + 2 ≤ 8 * (q:ℝ)^(1/(2*(k:ℝ))) := by
    have h4 : (1:ℝ) ≤ (q:ℝ)^(1/(2*(k:ℝ))) := Real.one_le_rpow hp1 (by positivity)
    linarith only [hhhle2, h4]
  have hP2H : (P:ℝ)^2 ≤ 4 * (H:ℝ)^2 * (q:ℝ)^(-(1/(k:ℝ))) := by
    have h1 : (P:ℝ)^2 ≤ (2 * (H:ℝ) * (q:ℝ)^(-(1/(2*(k:ℝ)))))^2 :=
      pow_le_pow_left₀ (by positivity) hPx 2
    refine h1.trans (le_of_eq ?_)
    have hsq : ((q:ℝ)^(-(1/(2*(k:ℝ)))))^2 = (q:ℝ)^(-(1/(k:ℝ))) := by
      rw [← Real.rpow_natCast (x := (q:ℝ)^(-(1/(2*(k:ℝ))))) (n := 2), ← Real.rpow_mul hp0.le]
      congr 1
      push_cast
      ring
    rw [mul_pow, mul_pow, hsq]
    ring
  have hPsum : (P:ℝ)^2 * (hh:ℝ) ≤ 16 * (H:ℝ)^2 * (q:ℝ)^(-(1/(2*(k:ℝ)))) := by
    have h5 : (P:ℝ)^2 * (hh:ℝ)
        ≤ (4 * (H:ℝ)^2 * (q:ℝ)^(-(1/(k:ℝ)))) * (4 * (q:ℝ)^(1/(2*(k:ℝ)))) :=
      mul_le_mul hP2H hhhle2 (by positivity) (by positivity)
    refine h5.trans (le_of_eq ?_)
    rw [show 4 * (H:ℝ)^2 * (q:ℝ)^(-(1/(k:ℝ))) * (4 * (q:ℝ)^(1/(2*(k:ℝ))))
        = 16 * (H:ℝ)^2 * ((q:ℝ)^(-(1/(k:ℝ))) * (q:ℝ)^(1/(2*(k:ℝ)))) by ring]
    rw [← Real.rpow_add hp0]
    have he : -(1/(k:ℝ)) + 1/(2*(k:ℝ)) = -(1/(2*(k:ℝ))) := by ring
    rw [he]
  have hPsum1 : (1:ℝ) ≤ (P:ℝ)^2 * (hh:ℝ) := by
    have h1 : (1:ℝ) ≤ (P:ℝ)^2 := by
      have h2 : (1:ℝ) ≤ (P:ℝ) := by exact_mod_cast hP1
      calc (1:ℝ) = 1 * 1 := by ring
        _ ≤ (P:ℝ) * (P:ℝ) := mul_le_mul h2 h2 (by norm_num) (by norm_num)
        _ = (P:ℝ)^2 := (sq _).symm
    have h2 : (1:ℝ) ≤ (hh:ℝ) := by exact_mod_cast hhhpos
    calc (1:ℝ) = 1 * 1 := by ring
      _ ≤ (P:ℝ)^2 * (hh:ℝ) := mul_le_mul h1 h2 (by norm_num) (by positivity)
  have hn2k1 : 1 ≤ 2*k-1 := by omega
  have hH2k : (1:ℝ) ≤ (H:ℝ)^(2*k-2) * (q:ℝ)^(1/(2*(k:ℝ)) - 1) := by
    have h2 : ((q:ℝ)^(((k:ℝ)+1)/(4*(k:ℝ)))) ^ (2*k-2) ≤ (H:ℝ)^(2*k-2) :=
      pow_le_pow_left₀ (by positivity) hHlo (2*k-2)
    have h3 : ((q:ℝ)^(((k:ℝ)+1)/(4*(k:ℝ)))) ^ (2*k-2)
        = (q:ℝ)^(((k:ℝ)+1)/(4*(k:ℝ)) * ((2*k-2:ℕ):ℝ)) := by
      rw [← Real.rpow_natCast (x := (q:ℝ)^(((k:ℝ)+1)/(4*(k:ℝ)))) (n := 2*k-2),
        ← Real.rpow_mul hp0.le]
    have hexp : ((k:ℝ)+1)/(4*(k:ℝ)) * ((2*k-2:ℕ):ℝ) + (1/(2*(k:ℝ)) - 1) = (k:ℝ)/2 - 1 := by
      have h6a : ((2*k-2:ℕ):ℝ) = 2*(k:ℝ) - 2 := by
        rw [Nat.cast_sub (by omega : 2 ≤ 2*k)]; push_cast; ring
      rw [h6a]
      field_simp
      ring
    have h4 : (q:ℝ)^(((k:ℝ)+1)/(4*(k:ℝ)) * ((2*k-2:ℕ):ℝ)) * (q:ℝ)^(1/(2*(k:ℝ)) - 1)
        = (q:ℝ)^(((k:ℝ)+1)/(4*(k:ℝ)) * ((2*k-2:ℕ):ℝ) + (1/(2*(k:ℝ)) - 1)) :=
      (Real.rpow_add hp0 _ _).symm
    have h7 : (1:ℝ) ≤ (q:ℝ)^((k:ℝ)/2 - 1) := by
      have hexp0 : (0:ℝ) ≤ (k:ℝ)/2 - 1 := by linarith only [hkR2]
      calc (1:ℝ) = (q:ℝ)^(0:ℝ) := (Real.rpow_zero _).symm
        _ ≤ (q:ℝ)^((k:ℝ)/2 - 1) := Real.rpow_le_rpow_of_exponent_le hp1 hexp0
    calc (1:ℝ) ≤ (q:ℝ)^((k:ℝ)/2 - 1) := h7
      _ = (q:ℝ)^(((k:ℝ)+1)/(4*(k:ℝ)) * ((2*k-2:ℕ):ℝ) + (1/(2*(k:ℝ)) - 1)) := by rw [hexp]
      _ = (q:ℝ)^(((k:ℝ)+1)/(4*(k:ℝ)) * ((2*k-2:ℕ):ℝ)) * (q:ℝ)^(1/(2*(k:ℝ)) - 1) := h4.symm
      _ ≤ (H:ℝ)^(2*k-2) * (q:ℝ)^(1/(2*(k:ℝ)) - 1) := by
            have h2' : (q:ℝ)^(((k:ℝ)+1)/(4*(k:ℝ)) * ((2*k-2:ℕ):ℝ)) ≤ (H:ℝ)^(2*k-2) := by
              rw [← h3]; exact h2
            exact mul_le_mul_of_nonneg_right h2' (Real.rpow_nonneg hp0.le _)
  have hlog2P : Real.log (2 * (P:ℝ)) + 1 ≤ 2 * Real.log q := by
    have h1 : Real.log (2 * (P:ℝ)) ≤ Real.log q := by
      apply Real.log_le_log (by positivity)
      have : (2:ℝ)*(P:ℝ) < (q:ℝ) := by exact_mod_cast h2P
      linarith only [this]
    linarith only [hL1, h1]
  have hκle : κ ≤ 32 * (Real.log q)^(8*k+16) := by
    rw [hκdef, div_le_iff₀ hp0]
    have h2 : (P:ℝ)^2 * ((hh:ℝ)+2)
        ≤ (4 * (H:ℝ)^2 * (q:ℝ)^(-(1/(k:ℝ)))) * (8 * (q:ℝ)^(1/(2*(k:ℝ)))) :=
      mul_le_mul hP2H hhh2' (by positivity) (by positivity)
    refine h2.trans ?_
    have h4 : (H:ℝ)^2 ≤ (q:ℝ)^((2*(k:ℝ)+1)/(2*(k:ℝ))) * (Real.log q)^(8*k+16) := hH2
    have h5 : 4 * (H:ℝ)^2 * (q:ℝ)^(-(1/(k:ℝ))) * (8 * (q:ℝ)^(1/(2*(k:ℝ))))
        ≤ 4 * ((q:ℝ)^((2*(k:ℝ)+1)/(2*(k:ℝ))) * (Real.log q)^(8*k+16)) * (q:ℝ)^(-(1/(k:ℝ)))
          * (8 * (q:ℝ)^(1/(2*(k:ℝ)))) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact h4
    refine h5.trans (le_of_eq ?_)
    have hpe : (q:ℝ)^((2*(k:ℝ)+1)/(2*(k:ℝ))) * (q:ℝ)^(-(1/(k:ℝ))) * (q:ℝ)^(1/(2*(k:ℝ))) = (q:ℝ) := by
      have he : (2*(k:ℝ)+1)/(2*(k:ℝ)) + (-(1/(k:ℝ))) + (1/(2*(k:ℝ))) = 1 := by
        field_simp
        ring
      rw [← Real.rpow_add hp0, ← Real.rpow_add hp0, he, Real.rpow_one]
    rw [show 4 * ((q:ℝ)^((2*(k:ℝ)+1)/(2*(k:ℝ))) * (Real.log q)^(8*k+16)) * (q:ℝ)^(-(1/(k:ℝ)))
          * (8 * (q:ℝ)^(1/(2*(k:ℝ))))
        = 32 * (Real.log q)^(8*k+16) * ((q:ℝ)^((2*(k:ℝ)+1)/(2*(k:ℝ))) * (q:ℝ)^(-(1/(k:ℝ)))
            * (q:ℝ)^(1/(2*(k:ℝ)))) from by ring]
    rw [hpe]
  have hcoll : collCount N q hh P ≤ 20000 * (P:ℝ)^2 * (Real.log q)^(8*k+17) := by
    have h := collCount_le N q hh P (show 0 < q by omega) hP1
    have hRHS : collCount N q hh P
        ≤ 16 * κ * (P:ℝ) + 4 * (P:ℝ)^2
          + (8*κ + 4) * (16 * (P:ℝ)^2 * (Real.log (2*(P:ℝ)) + 1)) := by
      refine h.trans (le_of_eq ?_)
      rw [hκdef]
      ring
    have hpow : (Real.log q)^(8*k+16) ≤ (Real.log q)^(8*k+17) := pow_le_pow_right₀ hL1 (by omega)
    have hPleP2 : (P:ℝ) ≤ (P:ℝ)^2 := by
      have h2 : (1:ℝ) ≤ (P:ℝ) := by exact_mod_cast hP1
      calc (P:ℝ) = (P:ℝ) * 1 := by ring
        _ ≤ (P:ℝ) * (P:ℝ) := mul_le_mul_of_nonneg_left h2 hPpos.le
        _ = (P:ℝ)^2 := (sq _).symm
    have hb1 : 16 * κ * (P:ℝ) ≤ 512 * (P:ℝ)^2 * (Real.log q)^(8*k+16) := by
      have h1 : 16 * κ * (P:ℝ) ≤ 16 * (32 * (Real.log q)^(8*k+16)) * (P:ℝ) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_left hκle (by norm_num)
      have h2 : 16 * (32 * (Real.log q)^(8*k+16)) * (P:ℝ)
          ≤ 16 * (32 * (Real.log q)^(8*k+16)) * (P:ℝ)^2 :=
        mul_le_mul_of_nonneg_left hPleP2 (by positivity)
      calc 16 * κ * (P:ℝ) ≤ 16 * (32 * (Real.log q)^(8*k+16)) * (P:ℝ) := h1
        _ ≤ 16 * (32 * (Real.log q)^(8*k+16)) * (P:ℝ)^2 := h2
        _ = 512 * (P:ℝ)^2 * (Real.log q)^(8*k+16) := by ring
    have hb2 : 4 * (P:ℝ)^2 ≤ 4 * (P:ℝ)^2 * (Real.log q)^(8*k+17) := by
      have h1 : (1:ℝ) ≤ (Real.log q)^(8*k+17) := one_le_pow₀ hL1
      calc 4 * (P:ℝ)^2 = 4 * (P:ℝ)^2 * 1 := by ring
        _ ≤ 4 * (P:ℝ)^2 * (Real.log q)^(8*k+17) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
    have hb3 : (8*κ + 4) * (16 * (P:ℝ)^2 * (Real.log (2*(P:ℝ)) + 1))
        ≤ 13000 * (P:ℝ)^2 * (Real.log q)^(8*k+17) := by
      have h1 : 8*κ + 4 ≤ 12 * (32 * (Real.log q)^(8*k+16)) := by
        have h2 : (1:ℝ) ≤ (Real.log q)^(8*k+16) := one_le_pow₀ hL1
        have h3 := mul_le_mul_of_nonneg_left hκle (by norm_num : (0:ℝ) ≤ 8)
        linarith only [hκle, h2]
      have h2 : (16:ℝ) * (P:ℝ)^2 * (Real.log (2*(P:ℝ)) + 1)
          ≤ (16:ℝ) * (P:ℝ)^2 * (2 * Real.log q) :=
        mul_le_mul_of_nonneg_left (by linarith only [hlog2P]) (by positivity)
      have h3 : (8*κ+4) * (16 * (P:ℝ)^2 * (Real.log (2*(P:ℝ)) + 1))
          ≤ (12 * (32 * (Real.log q)^(8*k+16))) * (16 * (P:ℝ)^2 * (2*Real.log q)) :=
        mul_le_mul h1 h2 (mul_nonneg (by positivity)
          (add_nonneg (Real.log_nonneg (by linarith only [hPpos, hA1, hPlow])) (by norm_num))) (by positivity)
      refine h3.trans ?_
      have hLp : (Real.log q)^(8*k+16) * Real.log q = (Real.log q)^(8*k+17) := by
        rw [← pow_succ]
      calc (12 * (32 * (Real.log q)^(8*k+16))) * (16 * (P:ℝ)^2 * (2*Real.log q))
          = 12288 * (P:ℝ)^2 * ((Real.log q)^(8*k+16) * Real.log q) := by ring
        _ = 12288 * (P:ℝ)^2 * (Real.log q)^(8*k+17) := by rw [hLp]
        _ ≤ 13000 * (P:ℝ)^2 * (Real.log q)^(8*k+17) := by
            have h4 : (0:ℝ) ≤ (P:ℝ)^2 * (Real.log q)^(8*k+17) := by positivity
            linarith only [hPpos, hPleP2, hb2]
    calc collCount N q hh P
        ≤ 16 * κ * (P:ℝ) + 4 * (P:ℝ)^2
          + (8*κ+4) * (16*(P:ℝ)^2*(Real.log (2*(P:ℝ))+1)) := hRHS
      _ ≤ 512 * (P:ℝ)^2 * (Real.log q)^(8*k+16) + 4 * (P:ℝ)^2 * (Real.log q)^(8*k+17)
            + 13000 * (P:ℝ)^2 * (Real.log q)^(8*k+17) := add_le_add (add_le_add hb1 hb2) hb3
      _ ≤ 20000 * (P:ℝ)^2 * (Real.log q)^(8*k+17) := by
          have h4 : 512 * (P:ℝ)^2 * (Real.log q)^(8*k+16)
              ≤ 512 * (P:ℝ)^2 * (Real.log q)^(8*k+17) :=
            mul_le_mul_of_nonneg_left hpow (by positivity)
          linarith only [h4, hPpos, hPleP2, hb2]
  -- ### t bound
  have hL20 : (20:ℝ) ≤ Real.log q := by
    have h1 : Real.log ((2:ℝ)^60) ≤ Real.log q := Real.log_le_log (by positivity) hp60r
    have h2 : Real.log ((2:ℝ)^60) = 60 * Real.log 2 := by rw [Real.log_pow]; norm_num
    have h3 : (20:ℝ) ≤ 60 * Real.log 2 := by linarith only [Real.log_two_gt_d9]
    linarith only [h1, h2, h3]
  have htb : ((t:ℝ)+1)^(2*k) ≤ 2^(2*k) * (Real.log q)^(2*k) := by
    have hK64 : ((2:ℝ)^t) ≤ 64 * (q:ℝ)^(1/(2*(k:ℝ))) := by
      have h1 : (K:ℝ) ≤ 4*(hh:ℝ) := by exact_mod_cast hKle
      have h2 : (4:ℝ)*(hh:ℝ) ≤ 4*(4*(q:ℝ)^(1/(2*(k:ℝ)))) :=
        mul_le_mul_of_nonneg_left hhhle2 (by norm_num : (0:ℝ) ≤ 4)
      have h3 : (K:ℝ) ≤ 64*(q:ℝ)^(1/(2*(k:ℝ))) := by linarith only [h1024le, hhhle2, h1]
      rwa [hKcast] at h3
    have hlog2pos : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    have hlog2ge : (2:ℝ)/3 ≤ Real.log 2 := by linarith only [Real.log_two_gt_d9]
    have hlogineq : (t:ℝ) * Real.log 2 ≤ 6 * Real.log 2 + (1/(2*(k:ℝ))) * Real.log q := by
      have h0 : (0:ℝ) < (2:ℝ)^t := by positivity
      have h1 := Real.log_le_log h0 hK64
      rw [Real.log_pow] at h1
      rw [Real.log_mul (by norm_num : (64:ℝ) ≠ 0) (by positivity : (q:ℝ)^(1/(2*(k:ℝ))) ≠ (0:ℝ))] at h1
      rw [Real.log_rpow hp0 (1/(2*(k:ℝ)))] at h1
      have h2 : Real.log 64 = 6 * Real.log 2 := by
        rw [show (64:ℝ) = (2:ℝ)^6 by norm_num, Real.log_pow]
        norm_num
      rw [h2] at h1
      exact h1
    have h4 : (1:ℝ)/(2*(k:ℝ)) ≤ (1:ℝ)/4 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; push_cast; linarith only [hkR2]
    have ht1 : (t:ℝ) * Real.log 2 ≤ 6 * Real.log 2 + (Real.log q)/4 := by
      have h5 : (1/(2*(k:ℝ))) * Real.log q ≤ (Real.log q)/4 := by
        calc (1/(2*(k:ℝ))) * Real.log q ≤ ((1:ℝ)/4) * Real.log q :=
              mul_le_mul_of_nonneg_right h4 hLpos.le
          _ = (Real.log q)/4 := by ring
      linarith only [hlogineq, h5]
    have ht2 : (t:ℝ) ≤ 6 + (Real.log q)/(4 * Real.log 2) := by
      have h6 : (t:ℝ) * Real.log 2 / Real.log 2
          ≤ (6 * Real.log 2 + (Real.log q)/4) / Real.log 2 :=
        div_le_div_of_nonneg_right ht1 hlog2pos.le
      rw [mul_div_cancel_right₀ _ (ne_of_gt hlog2pos)] at h6
      have h7 : (6 * Real.log 2 + (Real.log q)/4) / Real.log 2
          = 6 + (Real.log q)/(4*Real.log 2) := by
        rw [add_div, mul_div_cancel_right₀ 6 (ne_of_gt hlog2pos), div_div]
      rw [h7] at h6
      exact h6
    have hinv : (1:ℝ)/(4 * Real.log 2) ≤ (3:ℝ)/8 := by
      rw [div_le_iff₀ (by positivity)]
      linarith only [hlog2ge]
    have ht4 : (t:ℝ) ≤ 6 + (3:ℝ)/8 * Real.log q := by
      have h8 : (Real.log q)/(4 * Real.log 2) = (Real.log q) * (1/(4 * Real.log 2)) := by ring
      rw [h8] at ht2
      have h9 := mul_le_mul_of_nonneg_left hinv hLpos.le
      linarith only [ht2, h9]
    have ht5 : (t:ℝ) + 1 ≤ 2 * Real.log q := by linarith only [ht4, hL20]
    have h10 := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ (t:ℝ)+1) ht5 (2*k)
    rwa [mul_pow] at h10
  -- ### moment bound
  have hK16 : (K:ℝ) ≤ 16 * (q:ℝ)^(1/(2*(k:ℝ))) := by
    have h1 : (K:ℝ) ≤ 4*(hh:ℝ) := by exact_mod_cast hKle
    have h2 : (4:ℝ)*(hh:ℝ) ≤ 4*(4*(q:ℝ)^(1/(2*(k:ℝ)))) :=
      mul_le_mul_of_nonneg_left hhhle2 (by norm_num : (0:ℝ) ≤ 4)
    linarith only [hhhle2, h1]
  have hmomB : (q:ℝ)*((K:ℝ))^k + ((K:ℝ))^(2*k)*Real.sqrt (q:ℝ)
      ≤ 2*16^(2*k)*(q:ℝ)^((3:ℝ)/2) := by
    have hsqrt : Real.sqrt (q:ℝ) = (q:ℝ)^((1:ℝ)/2) := Real.sqrt_eq_rpow _
    have hpa : ((q:ℝ)^(1/(2*(k:ℝ))))^k = (q:ℝ)^((1:ℝ)/2) := by
      rw [← Real.rpow_natCast (x := (q:ℝ)^(1/(2*(k:ℝ)))) (n := k), ← Real.rpow_mul hp0.le]
      have he : (1/(2*(k:ℝ))) * ((k:ℕ):ℝ) = (1:ℝ)/2 := by
        push_cast
        field_simp
      rw [he]
    have hpa2 : ((q:ℝ)^(1/(2*(k:ℝ))))^(2*k) = (q:ℝ) := by
      rw [← Real.rpow_natCast (x := (q:ℝ)^(1/(2*(k:ℝ)))) (n := 2*k), ← Real.rpow_mul hp0.le]
      have he : (1/(2*(k:ℝ))) * ((2*k:ℕ):ℝ) = 1 := by
        push_cast
        field_simp
      rw [he, Real.rpow_one]
    have hKk : (K:ℝ)^k ≤ 16^k * (q:ℝ)^((1:ℝ)/2) := by
      calc (K:ℝ)^k ≤ (16 * (q:ℝ)^(1/(2*(k:ℝ))))^k := pow_le_pow_left₀ (by positivity) hK16 k
        _ = 16^k * ((q:ℝ)^(1/(2*(k:ℝ))))^k := by rw [mul_pow]
        _ = 16^k * (q:ℝ)^((1:ℝ)/2) := by rw [hpa]
    have hK2k : (K:ℝ)^(2*k) ≤ 16^(2*k) * (q:ℝ) := by
      calc (K:ℝ)^(2*k) ≤ (16 * (q:ℝ)^(1/(2*(k:ℝ))))^(2*k) :=
            pow_le_pow_left₀ (by positivity) hK16 (2*k)
        _ = 16^(2*k) * ((q:ℝ)^(1/(2*(k:ℝ))))^(2*k) := by rw [mul_pow]
        _ = 16^(2*k) * (q:ℝ) := by rw [hpa2]
    have hpadd : (q:ℝ) * (q:ℝ)^((1:ℝ)/2) = (q:ℝ)^((3:ℝ)/2) := by
      have h := Real.rpow_add hp0 (1:ℝ) ((1:ℝ)/2)
      rw [Real.rpow_one] at h
      rw [← h]
      norm_num
    have ha : (q:ℝ) * (K:ℝ)^k ≤ 16^k * (q:ℝ)^((3:ℝ)/2) := by
      have h1 : (q:ℝ) * (K:ℝ)^k ≤ (q:ℝ) * (16^k * (q:ℝ)^((1:ℝ)/2)) :=
        mul_le_mul_of_nonneg_left hKk hp0.le
      have h2 : (q:ℝ) * (16^k * (q:ℝ)^((1:ℝ)/2)) = 16^k * (q:ℝ)^((3:ℝ)/2) := by
        rw [show (q:ℝ) * (16^k * (q:ℝ)^((1:ℝ)/2)) = 16^k * ((q:ℝ) * (q:ℝ)^((1:ℝ)/2)) by ring,
          hpadd]
      linarith only [h1, h2]
    have hb : (K:ℝ)^(2*k) * Real.sqrt (q:ℝ) ≤ 16^(2*k) * (q:ℝ)^((3:ℝ)/2) := by
      rw [hsqrt]
      have h1 : (K:ℝ)^(2*k) * (q:ℝ)^((1:ℝ)/2) ≤ (16^(2*k) * (q:ℝ)) * (q:ℝ)^((1:ℝ)/2) :=
        mul_le_mul_of_nonneg_right hK2k (by positivity)
      have h2 : (16^(2*k) * (q:ℝ)) * (q:ℝ)^((1:ℝ)/2) = 16^(2*k) * (q:ℝ)^((3:ℝ)/2) := by
        rw [show (16^(2*k) * (q:ℝ)) * (q:ℝ)^((1:ℝ)/2) = 16^(2*k) * ((q:ℝ) * (q:ℝ)^((1:ℝ)/2)) by ring,
          hpadd]
      linarith only [h1, h2]
    have h16k : (16:ℝ)^k ≤ 16^(2*k) :=
      pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 16) (by omega : k ≤ 2*k)
    have h16k2 : 16^k * (q:ℝ)^((3:ℝ)/2) ≤ 16^(2*k) * (q:ℝ)^((3:ℝ)/2) :=
      mul_le_mul_of_nonneg_right h16k (by positivity)
    linarith only [ha, hb, h16k2]
  have hPhh : (P:ℝ)^(2*k-2) * ((hh:ℝ))⁻¹
      ≤ 2^(2*k) * (H:ℝ)^(2*k-2) * (q:ℝ)^(1/(2*(k:ℝ)) - 1) := by
    have hinv : ((hh:ℝ))⁻¹ ≤ 2 * (P:ℝ) / (H:ℝ) := by
      rw [inv_le_comm₀ hhhposR (by positivity)]
      have he : (2 * (P:ℝ) / (H:ℝ))⁻¹ = (H:ℝ) / (2 * (P:ℝ)) := by rw [inv_div]
      rw [he]; exact hhlo
    have hPk : (P:ℝ)^(2*k-1) ≤ (2 * (H:ℝ) * (q:ℝ)^(-(1/(2*(k:ℝ)))))^(2*k-1) :=
      pow_le_pow_left₀ (by positivity) hPx (2*k-1)
    have hPk2 : (2 * (H:ℝ) * (q:ℝ)^(-(1/(2*(k:ℝ)))))^(2*k-1)
        = 2^(2*k-1) * (H:ℝ)^(2*k-1) * (q:ℝ)^(-(((2*k-1:ℕ):ℝ)/(2*(k:ℝ)))) := by
      have hp1 : ((q:ℝ)^(-(1/(2*(k:ℝ)))))^(2*k-1) = (q:ℝ)^(-(((2*k-1:ℕ):ℝ)/(2*(k:ℝ)))) := by
        rw [← Real.rpow_natCast (x := (q:ℝ)^(-(1/(2*(k:ℝ))))) (n := 2*k-1), ← Real.rpow_mul hp0.le]
        congr 1
        push_cast; ring
      rw [mul_pow, mul_pow, hp1]
    have key : (P:ℝ)^(2*k-2) * ((hh:ℝ))⁻¹
        ≤ 2^(2*k-1) * (H:ℝ)^(2*k-1) * (q:ℝ)^(-(((2*k-1:ℕ):ℝ)/(2*(k:ℝ)))) * (2 / (H:ℝ)) := by
      calc (P:ℝ)^(2*k-2) * ((hh:ℝ))⁻¹
          ≤ (P:ℝ)^(2*k-2) * (2 * (P:ℝ) / (H:ℝ)) := mul_le_mul_of_nonneg_left hinv (by positivity)
        _ = (P:ℝ)^(2*k-1) * (2 / (H:ℝ)) := by
              rw [show (P:ℝ)^(2*k-1) = (P:ℝ)^(2*k-2) * (P:ℝ) by
                rw [← pow_succ]; congr 1; omega]
              ring
        _ ≤ (2 * (H:ℝ) * (q:ℝ)^(-(1/(2*(k:ℝ)))))^(2*k-1) * (2 / (H:ℝ)) :=
              mul_le_mul_of_nonneg_right hPk (by positivity)
        _ = 2^(2*k-1) * (H:ℝ)^(2*k-1) * (q:ℝ)^(-(((2*k-1:ℕ):ℝ)/(2*(k:ℝ)))) * (2 / (H:ℝ)) := by
              rw [hPk2]
    refine key.trans (le_of_eq ?_)
    have he : -(((2*k-1:ℕ):ℝ)/(2*(k:ℝ))) = 1/(2*(k:ℝ)) - 1 := by
      have hea : ((2*k-1:ℕ):ℝ) = 2*(k:ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ 2*k)]; push_cast; ring
      rw [hea]; field_simp; ring
    have hHred : (H:ℝ)^(2*k-1) / (H:ℝ) = (H:ℝ)^(2*k-2) := by
      rw [div_eq_iff (ne_of_gt hHqos),
        show (H:ℝ)^(2*k-1) = (H:ℝ)^(2*k-2) * (H:ℝ) by
          rw [← pow_succ]; congr 1; omega]
    calc 2^(2*k-1) * (H:ℝ)^(2*k-1) * (q:ℝ)^(-(((2*k-1:ℕ):ℝ)/(2*(k:ℝ)))) * (2 / (H:ℝ))
        = 2^(2*k-1) * 2 * ((H:ℝ)^(2*k-1) / (H:ℝ)) * (q:ℝ)^(-(((2*k-1:ℕ):ℝ)/(2*(k:ℝ)))) := by ring
      _ = 2^(2*k-1) * 2 * (H:ℝ)^(2*k-2) * (q:ℝ)^(-(((2*k-1:ℕ):ℝ)/(2*(k:ℝ)))) := by rw [hHred]
      _ = 2^(2*k) * (H:ℝ)^(2*k-2) * (q:ℝ)^(1/(2*(k:ℝ)) - 1) := by
            rw [show (2:ℝ)^(2*k) = 2^(2*k-1) * 2 by rw [← pow_succ]; congr 1; omega, ← he]
  -- ### final monomial comparison
  have haux : (2:ℝ)^(2*k) * 2^(2*k-2) * 20000 * 4 * 2^(2*k) * 4 * 2 * 16^(2*k) * 2^(2*k) ≤ 2^68 :=
    burgess_core_gen_aux k hk2 hk3
  have hhhpow : (hh:ℝ)^(2*k-1) = (hh:ℝ)^(2*k) * ((hh:ℝ))⁻¹ := by
    have h1 : (hh:ℝ)^(2*k) = (hh:ℝ)^(2*k-1) * (hh:ℝ) := by
      rw [← pow_succ]; congr 1; omega
    rw [h1, mul_assoc, mul_inv_cancel₀ (ne_of_gt hhhposR), mul_one]
  have hAlg2 : (2 * (P:ℝ)^2 * (hh:ℝ))^(2*k-2) * (P:ℝ)^2 * (hh:ℝ)
      = 2^(2*k-2) * (P:ℝ)^(4*k-2) * (hh:ℝ)^(2*k-1) := by
    have hP : (P:ℝ)^(2*(2*k-2)) * (P:ℝ)^2 = (P:ℝ)^(4*k-2) := by
      rw [← pow_add]; congr 1; omega
    have hhh : (hh:ℝ)^(2*k-2) * (hh:ℝ) = (hh:ℝ)^(2*k-1) := by
      rw [← pow_succ]; congr 1; omega
    have h2 : (2 * (P:ℝ)^2 * (hh:ℝ))^(2*k-2)
        = 2^(2*k-2) * ((P:ℝ)^2)^(2*k-2) * (hh:ℝ)^(2*k-2) := by rw [mul_pow, mul_pow]
    have h3 : ((P:ℝ)^2)^(2*k-2) = (P:ℝ)^(2*(2*k-2)) := (pow_mul (P:ℝ) 2 (2*k-2)).symm
    rw [h2, h3]
    calc 2^(2*k-2) * (P:ℝ)^(2*(2*k-2)) * (hh:ℝ)^(2*k-2) * (P:ℝ)^2 * (hh:ℝ)
        = 2^(2*k-2) * ((P:ℝ)^(2*(2*k-2)) * (P:ℝ)^2) * ((hh:ℝ)^(2*k-2) * (hh:ℝ)) := by ring
      _ = 2^(2*k-2) * (P:ℝ)^(4*k-2) * (hh:ℝ)^(2*k-1) := by rw [hP, hhh]
  have hLp : (Real.log q)^(8*k+17) * (Real.log q)^(2*k) = (Real.log q)^(10*k+17) := by
    rw [← pow_add]; congr 1; omega
  have hstep : 2^(2*k) * (2 * (P:ℝ)^2 * (hh:ℝ))^(2*k-2) * ((hh:ℝ) * (20000 * (P:ℝ)^2 * (Real.log q)^(8*k+17)))
        * (4 * (2^(2*k) * (Real.log q)^(2*k)) * (4*Cm*(2*16^(2*k)*(q:ℝ)^((3:ℝ)/2))))
      ≤ 2^(2*k) * 2^(2*k-2) * 20000 * 4 * 2^(2*k) * 4 * 2 * 16^(2*k) * Cm
        * (P:ℝ)^(4*k-2) * (hh:ℝ)^(2*k-1) * (Real.log q)^(10*k+17) * (q:ℝ)^((3:ℝ)/2) := by
    have h1 : 2^(2*k) * (2 * (P:ℝ)^2 * (hh:ℝ))^(2*k-2) * ((hh:ℝ) * (20000 * (P:ℝ)^2 * (Real.log q)^(8*k+17)))
          * (4 * (2^(2*k) * (Real.log q)^(2*k)) * (4*Cm*(2*16^(2*k)*(q:ℝ)^((3:ℝ)/2))))
        = 2^(2*k) * 20000 * 4 * 2^(2*k) * 4 * 2 * 16^(2*k) * Cm
          * ((2 * (P:ℝ)^2 * (hh:ℝ))^(2*k-2) * (P:ℝ)^2 * (hh:ℝ))
          * ((Real.log q)^(8*k+17) * (Real.log q)^(2*k)) * (q:ℝ)^((3:ℝ)/2) := by ring
    rw [h1, hAlg2, hLp]
    exact le_of_eq (by ring)
  have hmono : 2^(2*k) * (2 * (P:ℝ)^2 * (hh:ℝ))^(2*k-2) * ((hh:ℝ) * collCount N q hh P)
        * (4 * ((t:ℝ)+1)^(2*k) * (4*Cm*((q:ℝ)*((K:ℝ))^k + ((K:ℝ))^(2*k)*Real.sqrt (q:ℝ))))
      ≤ ((P:ℝ)^(2*k) * (hh:ℝ)^(2*k))
        * (2^68 * Cm * (H:ℝ)^(2*k-2) * (q:ℝ)^(((k:ℝ)+1)/(2*(k:ℝ))) * (Real.log q)^(10*k+17)) := by
    have s1 : 2^(2*k) * (2 * (P:ℝ)^2 * (hh:ℝ))^(2*k-2) * ((hh:ℝ) * collCount N q hh P)
          * (4 * ((t:ℝ)+1)^(2*k) * (4*Cm*((q:ℝ)*((K:ℝ))^k + ((K:ℝ))^(2*k)*Real.sqrt (q:ℝ))))
        ≤ 2^(2*k) * (2 * (P:ℝ)^2 * (hh:ℝ))^(2*k-2) * ((hh:ℝ) * (20000 * (P:ℝ)^2 * (Real.log q)^(8*k+17)))
          * (4 * ((t:ℝ)+1)^(2*k) * (4*Cm*((q:ℝ)*((K:ℝ))^k + ((K:ℝ))^(2*k)*Real.sqrt (q:ℝ)))) := by
      apply mul_le_mul_of_nonneg_right _
        (by positivity : (0:ℝ) ≤ 4 * ((t:ℝ)+1)^(2*k)
          * (4*Cm*((q:ℝ)*((K:ℝ))^k + ((K:ℝ))^(2*k)*Real.sqrt (q:ℝ))))
      apply mul_le_mul_of_nonneg_left _
        (by positivity : (0:ℝ) ≤ 2^(2*k) * (2 * (P:ℝ)^2 * (hh:ℝ))^(2*k-2))
      exact mul_le_mul_of_nonneg_left hcoll hhhposR.le
    have s2 : 2^(2*k) * (2 * (P:ℝ)^2 * (hh:ℝ))^(2*k-2) * ((hh:ℝ) * (20000 * (P:ℝ)^2 * (Real.log q)^(8*k+17)))
          * (4 * ((t:ℝ)+1)^(2*k) * (4*Cm*((q:ℝ)*((K:ℝ))^k + ((K:ℝ))^(2*k)*Real.sqrt (q:ℝ))))
        ≤ 2^(2*k) * (2 * (P:ℝ)^2 * (hh:ℝ))^(2*k-2) * ((hh:ℝ) * (20000 * (P:ℝ)^2 * (Real.log q)^(8*k+17)))
          * (4 * (2^(2*k) * (Real.log q)^(2*k)) * (4*Cm*(2*16^(2*k)*(q:ℝ)^((3:ℝ)/2)))) := by
      apply mul_le_mul_of_nonneg_left _
        (by positivity : (0:ℝ) ≤ 2^(2*k) * (2 * (P:ℝ)^2 * (hh:ℝ))^(2*k-2)
          * ((hh:ℝ) * (20000 * (P:ℝ)^2 * (Real.log q)^(8*k+17))))
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left htb (by norm_num : (0:ℝ) ≤ 4)
      · exact mul_le_mul_of_nonneg_left hmomB (by positivity : (0:ℝ) ≤ 4*Cm)
      · positivity
      · positivity
    have s4 : 2^(2*k) * 2^(2*k-2) * 20000 * 4 * 2^(2*k) * 4 * 2 * 16^(2*k) * Cm
          * (P:ℝ)^(4*k-2) * (hh:ℝ)^(2*k-1) * (Real.log q)^(10*k+17) * (q:ℝ)^((3:ℝ)/2)
        ≤ ((P:ℝ)^(2*k) * (hh:ℝ)^(2*k))
          * (2^68 * Cm * (H:ℝ)^(2*k-2) * (q:ℝ)^(((k:ℝ)+1)/(2*(k:ℝ))) * (Real.log q)^(10*k+17)) := by
      have hpc : (2:ℝ)^(2*k) * 2^(2*k-2) * 20000 * 4 * 2^(2*k) * 4 * 2 * 16^(2*k) * 2^(2*k) ≤ 2^68 := haux
      have hkey : 2^(2*k) * 2^(2*k-2) * 20000 * 4 * 2^(2*k) * 4 * 2 * 16^(2*k)
            * (P:ℝ)^(4*k-2) * (hh:ℝ)^(2*k-1) * (q:ℝ)^((3:ℝ)/2)
          ≤ ((P:ℝ)^(2*k) * (hh:ℝ)^(2*k))
            * (2^68 * (H:ℝ)^(2*k-2) * (q:ℝ)^(((k:ℝ)+1)/(2*(k:ℝ)))) := by
        have hPe : (P:ℝ)^(4*k-2) = (P:ℝ)^(2*k) * (P:ℝ)^(2*k-2) := by
          rw [← pow_add]; congr 1; omega
        have h1 : 2^(2*k) * 2^(2*k-2) * 20000 * 4 * 2^(2*k) * 4 * 2 * 16^(2*k)
              * (P:ℝ)^(4*k-2) * (hh:ℝ)^(2*k-1) * (q:ℝ)^((3:ℝ)/2)
            = ((P:ℝ)^(2*k) * (hh:ℝ)^(2*k))
              * ((2^(2*k) * 2^(2*k-2) * 20000 * 4 * 2^(2*k) * 4 * 2 * 16^(2*k))
                * ((P:ℝ)^(2*k-2) * ((hh:ℝ))⁻¹ * (q:ℝ)^((3:ℝ)/2))) := by
          rw [hPe, hhhpow]; ring
        rw [h1]
        apply mul_le_mul_of_nonneg_left _ (by positivity : (0:ℝ) ≤ (P:ℝ)^(2*k) * (hh:ℝ)^(2*k))
        have h3 : (P:ℝ)^(2*k-2) * ((hh:ℝ))⁻¹ * (q:ℝ)^((3:ℝ)/2)
            ≤ 2^(2*k) * (H:ℝ)^(2*k-2) * (q:ℝ)^(((k:ℝ)+1)/(2*(k:ℝ))) := by
          have hpadd : (q:ℝ)^(1/(2*(k:ℝ)) - 1) * (q:ℝ)^((3:ℝ)/2) = (q:ℝ)^(((k:ℝ)+1)/(2*(k:ℝ))) := by
            rw [← Real.rpow_add hp0]
            congr 1
            field_simp
            ring
          have h4 : (P:ℝ)^(2*k-2) * ((hh:ℝ))⁻¹ * (q:ℝ)^((3:ℝ)/2)
              ≤ (2^(2*k) * (H:ℝ)^(2*k-2) * (q:ℝ)^(1/(2*(k:ℝ)) - 1)) * (q:ℝ)^((3:ℝ)/2) :=
            mul_le_mul_of_nonneg_right hPhh (by positivity)
          refine h4.trans (le_of_eq ?_)
          calc (2^(2*k) * (H:ℝ)^(2*k-2) * (q:ℝ)^(1/(2*(k:ℝ)) - 1)) * (q:ℝ)^((3:ℝ)/2)
              = 2^(2*k) * (H:ℝ)^(2*k-2) * ((q:ℝ)^(1/(2*(k:ℝ)) - 1) * (q:ℝ)^((3:ℝ)/2)) := by ring
            _ = 2^(2*k) * (H:ℝ)^(2*k-2) * (q:ℝ)^(((k:ℝ)+1)/(2*(k:ℝ))) := by rw [hpadd]
        calc (2^(2*k) * 2^(2*k-2) * 20000 * 4 * 2^(2*k) * 4 * 2 * 16^(2*k))
              * ((P:ℝ)^(2*k-2) * ((hh:ℝ))⁻¹ * (q:ℝ)^((3:ℝ)/2))
            ≤ (2^(2*k) * 2^(2*k-2) * 20000 * 4 * 2^(2*k) * 4 * 2 * 16^(2*k))
              * (2^(2*k) * (H:ℝ)^(2*k-2) * (q:ℝ)^(((k:ℝ)+1)/(2*(k:ℝ)))) :=
              mul_le_mul_of_nonneg_left h3 (by positivity)
          _ = ((2^(2*k) * 2^(2*k-2) * 20000 * 4 * 2^(2*k) * 4 * 2 * 16^(2*k)) * 2^(2*k))
              * ((H:ℝ)^(2*k-2) * (q:ℝ)^(((k:ℝ)+1)/(2*(k:ℝ)))) := by ring
          _ ≤ 2^68 * ((H:ℝ)^(2*k-2) * (q:ℝ)^(((k:ℝ)+1)/(2*(k:ℝ)))) :=
              mul_le_mul_of_nonneg_right hpc (by positivity)
          _ = 2^68 * (H:ℝ)^(2*k-2) * (q:ℝ)^(((k:ℝ)+1)/(2*(k:ℝ))) := by ring
      calc 2^(2*k) * 2^(2*k-2) * 20000 * 4 * 2^(2*k) * 4 * 2 * 16^(2*k) * Cm
            * (P:ℝ)^(4*k-2) * (hh:ℝ)^(2*k-1) * (Real.log q)^(10*k+17) * (q:ℝ)^((3:ℝ)/2)
          = Cm * (Real.log q)^(10*k+17) * (2^(2*k) * 2^(2*k-2) * 20000 * 4 * 2^(2*k) * 4 * 2 * 16^(2*k)
              * (P:ℝ)^(4*k-2) * (hh:ℝ)^(2*k-1) * (q:ℝ)^((3:ℝ)/2)) := by ring
        _ ≤ Cm * (Real.log q)^(10*k+17) * (((P:ℝ)^(2*k) * (hh:ℝ)^(2*k))
              * (2^68 * (H:ℝ)^(2*k-2) * (q:ℝ)^(((k:ℝ)+1)/(2*(k:ℝ))))) :=
              mul_le_mul_of_nonneg_left hkey (by positivity)
        _ = ((P:ℝ)^(2*k) * (hh:ℝ)^(2*k))
              * (2^68 * Cm * (H:ℝ)^(2*k-2) * (q:ℝ)^(((k:ℝ)+1)/(2*(k:ℝ))) * (Real.log q)^(10*k+17)) := by ring
    exact s1.trans (s2.trans (hstep.trans s4))
  have hscaled : ((P:ℝ)^(2*k) * (hh:ℝ)^(2*k)) * ‖cSum χ N (N + (H:ℤ))‖^(2*k)
      ≤ ((P:ℝ)^(2*k) * (hh:ℝ)^(2*k))
        * (CL^(2*k) * (2^68 * Cm * (H:ℝ)^(2*k-2) * (q:ℝ)^(((k:ℝ)+1)/(2*(k:ℝ))) * (Real.log q)^(10*k+17))) := by
    have h1 : ((P:ℝ) * (hh:ℝ) * ‖cSum χ N (N + (H:ℤ))‖)^(2*k)
        = ((P:ℝ)^(2*k) * (hh:ℝ)^(2*k)) * ‖cSum χ N (N + (H:ℤ))‖^(2*k) := by
      rw [mul_pow, mul_pow]
    rw [h1] at hbig
    refine (hbig.trans (mul_le_mul_of_nonneg_left hmono (by positivity : (0:ℝ) ≤ CL^(2*k)))).trans_eq ?_
    ring
  have hpow : ‖cSum χ N (N + (H:ℤ))‖^(2*k)
      ≤ CL^(2*k) * (2^68 * Cm * (H:ℝ)^(2*k-2) * (q:ℝ)^(((k:ℝ)+1)/(2*(k:ℝ))) * (Real.log q)^(10*k+17)) :=
    le_of_mul_le_mul_left hscaled (by positivity)
  exact burgess_core_gen_tail Cm hCm1 k hk2 hp0 H hHqos hL1 CL hCL0 _ (norm_nonneg _) hpow

theorem burgess_charSum_uniform_of_moment
    (hmom : ∀ r : ℕ, 0 < r → ∃ C : ℝ, 0 < C ∧
       ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive → χ ≠ 1 →
         ∀ H : ℕ, H ≤ q →
           ∑ m ∈ Finset.range q, ‖∑ h ∈ Finset.Ioc m (m + H), χ (h : ZMod q)‖ ^ (2 * r)
             ≤ C * ((q : ℝ) * (H : ℝ) ^ r + (H : ℝ) ^ (2 * r) * Real.sqrt (q : ℝ)))
    {ε : ℝ} (hε : 0 < ε) (k : ℕ) (hk : k = 2 ∨ k = 3) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive → χ ≠ 1 →
        ∀ {N H : ℕ}, 1 ≤ N → 1 ≤ H → H ≤ q →
          ‖∑ n ∈ Finset.Ioc N (N + H), χ (n : ZMod q)‖ ≤
            C * (q : ℝ) ^ ((k + 1 : ℝ) / (4 * k ^ 2) + ε) * (H : ℝ) ^ (1 - 1 / (k : ℝ)) := by
  have hk1 : 1 ≤ k := by omega
  have hk2 : 2 ≤ k := by omega
  have hk3 : k ≤ 3 := by omega
  have hkpos : 0 < k := by omega
  have hkposR : (0:ℝ) < (k:ℝ) := by exact_mod_cast hkpos
  have hk1R : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk1
  have hk2R : (2:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk2
  obtain ⟨Cm0, hCm0pos, hCm0⟩ := hmom k hkpos
  set Cm : ℝ := max Cm0 1 with hCmdef
  have hCm0le : Cm0 ≤ Cm := le_max_left _ _
  have hCm1 : 1 ≤ Cm := le_max_right _ _
  have hCmpos : 0 < Cm := lt_of_lt_of_le zero_lt_one hCm1
  have hCmC : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive → χ ≠ 1 →
      ∀ L : ℕ, L ≤ q →
      ∑ m ∈ Finset.range q, ‖cSum χ (m:ℤ) ((m:ℤ) + L)‖^(2*k)
        ≤ Cm * ((q:ℝ) * (L:ℝ)^k + (L:ℝ)^(2*k) * Real.sqrt q) := by
    intro q _ χ hprim hχ L hL
    have h0 := hCm0 χ hprim hχ L hL
    have hsum : ∑ m ∈ Finset.range q, ‖cSum χ (m:ℤ) ((m:ℤ) + L)‖^(2*k)
        = ∑ m ∈ Finset.range q, ‖∑ h ∈ Finset.Ioc m (m + L), χ (h : ZMod q)‖ ^ (2*k) := by
      refine Finset.sum_congr rfl (fun m hm => ?_)
      rw [cSum_natCast]
    rw [hsum]
    exact h0.trans (mul_le_mul_of_nonneg_right hCm0le (by positivity))
  obtain ⟨Ccs, hCcspos, hCcs⟩ := charSum_range_le_polyaVinogradov
  obtain ⟨C1, hC1pos, hC1⟩ := Commons.Analysis.Real.log_pow_le_mul_rpow
    (show (0:ℝ) < ε/2 by linarith only [hε]) (10*k+21)
  have h512nn : (0:ℝ) ≤ 2^512 := pow_nonneg (by norm_num : (0:ℝ) ≤ 2) 512
  have h512one : (1:ℝ) ≤ 2^512 := one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2)
  have hBigpos : (0:ℝ) < 2^512 + 2^70 * 600 * Cm * C1 + 2 * Ccs + 1 := by
    have h5 : (0:ℝ) < 2^70 * 600 * Cm * C1 := by positivity
    have h6 : (0:ℝ) < 2 * Ccs := by linarith only [hCcspos]
    linarith only [hCcspos, h5]
  refine ⟨2^512 + 2^70 * 600 * Cm * C1 + 2 * Ccs + 1, hBigpos, ?_⟩
  intro q _ χ hχprim hχne N H hN1 hH1 hHq
  have hqposN : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hq0 : (0:ℝ) < (q:ℝ) := by exact_mod_cast hqposN
  have hq1 : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast (show 1 ≤ q by omega)
  have hHpos : (0:ℝ) < (H:ℝ) := by exact_mod_cast hH1
  have hHnn : (0:ℝ) ≤ (H:ℝ) := hHpos.le
  have hHqR : (H:ℝ) ≤ (q:ℝ) := by exact_mod_cast hHq
  have hσpos : (0:ℝ) < (k + 1 : ℝ) / (4 * k ^ 2) + ε := by
    have h1 : (0:ℝ) < (k + 1 : ℝ) / (4 * k ^ 2) := by positivity
    linarith only [hε, h1]
  have htriv : ∀ (N' H' : ℕ), ‖∑ n ∈ Finset.Ioc N' (N' + H'), χ (n : ZMod q)‖ ≤ (H':ℝ) := by
    intro N' H'
    calc ‖∑ n ∈ Finset.Ioc N' (N' + H'), χ (n : ZMod q)‖
        ≤ ∑ n ∈ Finset.Ioc N' (N' + H'), ‖χ (n : ZMod q)‖ := norm_sum_le _ _
      _ ≤ ∑ _n ∈ Finset.Ioc N' (N' + H'), (1:ℝ) :=
          Finset.sum_le_sum (fun n _ => DirichletCharacter.norm_le_one χ _)
      _ = (H':ℝ) := by
          rw [Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul, mul_one,
            show N' + H' - N' = H' by omega]
  rcases lt_or_ge q (2^512) with hq512lt | hq512
  · -- ### case A: q < 2^512
    have hqexp : (q:ℝ)^((1:ℝ)/(k:ℝ) - ((k + 1 : ℝ) / (4 * k ^ 2) + ε)) ≤ 2^512 := by
      by_cases ha : (0:ℝ) ≤ (1:ℝ)/(k:ℝ) - ((k + 1 : ℝ) / (4 * k ^ 2) + ε)
      · have ha1 : (1:ℝ)/(k:ℝ) - ((k + 1 : ℝ) / (4 * k ^ 2) + ε) ≤ 1 := by
          have h1 : (1:ℝ)/(k:ℝ) ≤ 1 := by
            rw [div_le_one hkposR]; exact hk1R
          linarith only [hσpos, h1]
        calc (q:ℝ)^((1:ℝ)/(k:ℝ) - ((k + 1 : ℝ) / (4 * k ^ 2) + ε))
            ≤ (((2^512 : ℕ)):ℝ)^((1:ℝ)/(k:ℝ) - ((k + 1 : ℝ) / (4 * k ^ 2) + ε)) :=
              Real.rpow_le_rpow hq0.le (by exact_mod_cast (le_of_lt hq512lt)) ha
          _ ≤ (((2^512 : ℕ)):ℝ)^(1:ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast Nat.one_le_two_pow) ha1
          _ = 2^512 := by rw [Real.rpow_one, Nat.cast_pow, Nat.cast_ofNat]
      · push_neg at ha
        have hqa : (1:ℝ) ≤ (q:ℝ)^(-((1:ℝ)/(k:ℝ) - ((k + 1 : ℝ) / (4 * k ^ 2) + ε))) :=
          Real.one_le_rpow hq1 (by linarith only [ha])
        calc (q:ℝ)^((1:ℝ)/(k:ℝ) - ((k + 1 : ℝ) / (4 * k ^ 2) + ε))
            = ((q:ℝ)^(-((1:ℝ)/(k:ℝ) - ((k + 1 : ℝ) / (4 * k ^ 2) + ε))))⁻¹ := by
              rw [Real.rpow_neg hq0.le, inv_inv]
          _ ≤ 1 := inv_le_one_of_one_le₀ hqa
          _ ≤ 2^512 := h512one
    have hsplit : (H:ℝ) = (H:ℝ)^((1:ℝ)/(k:ℝ)) * (H:ℝ)^(1 - 1/(k:ℝ)) := by
      rw [← Real.rpow_add hHpos]
      have he : (1:ℝ)/(k:ℝ) + (1 - 1/(k:ℝ)) = 1 := by ring
      rw [he, Real.rpow_one]
    have hHk : (H:ℝ)^((1:ℝ)/(k:ℝ)) ≤ (q:ℝ)^((1:ℝ)/(k:ℝ)) :=
      Real.rpow_le_rpow hHnn hHqR (by positivity)
    have hqσ_eq : (q:ℝ)^((1:ℝ)/(k:ℝ))
        = (q:ℝ)^((1:ℝ)/(k:ℝ) - ((k + 1 : ℝ) / (4 * k ^ 2) + ε))
          * (q:ℝ)^((k + 1 : ℝ) / (4 * k ^ 2) + ε) := by
      rw [← Real.rpow_add hq0]
      congr 1
      ring
    calc ‖∑ n ∈ Finset.Ioc N (N + H), χ (n : ZMod q)‖ ≤ (H:ℝ) := htriv N H
      _ = (H:ℝ)^((1:ℝ)/(k:ℝ)) * (H:ℝ)^(1 - 1/(k:ℝ)) := hsplit
      _ ≤ (q:ℝ)^((1:ℝ)/(k:ℝ)) * (H:ℝ)^(1 - 1/(k:ℝ)) :=
          mul_le_mul_of_nonneg_right hHk (Real.rpow_nonneg hHnn _)
      _ = (q:ℝ)^((1:ℝ)/(k:ℝ) - ((k + 1 : ℝ) / (4 * k ^ 2) + ε))
            * (q:ℝ)^((k + 1 : ℝ) / (4 * k ^ 2) + ε) * (H:ℝ)^(1 - 1/(k:ℝ)) := by
          rw [hqσ_eq]
      _ ≤ 2^512 * (q:ℝ)^((k + 1 : ℝ) / (4 * k ^ 2) + ε) * (H:ℝ)^(1 - 1/(k:ℝ)) := by
          apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hHnn _)
          exact mul_le_mul_of_nonneg_right hqexp (by positivity)
      _ ≤ (2^512 + 2^70 * 600 * Cm * C1 + 2 * Ccs + 1)
            * (q:ℝ)^((k + 1 : ℝ) / (4 * k ^ 2) + ε) * (H:ℝ)^(1 - 1/(k:ℝ)) := by
          apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hHnn _)
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          have h5 : (0:ℝ) ≤ 2^70 * 600 * Cm * C1 := by positivity
          have h6 : (0:ℝ) ≤ 2 * Ccs := by linarith only [hCcspos]
          linarith only [hCcspos, h5]
  · -- q ≥ 2^512
    have hq60 : 2^60 ≤ q :=
      le_trans (by simpa using Nat.pow_le_pow_right (by norm_num : 0 < 2) (by norm_num : 60 ≤ 512)) hq512
    have hq2 : 2 ≤ q :=
      le_trans (by simpa using Nat.pow_le_pow_right (by norm_num : 0 < 2) (by norm_num : 1 ≤ 512)) hq512
    have hq2R : (2:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq2
    have hqlog : (0:ℝ) < Real.log q := Real.log_pos (by linarith only [hq2R])
    have hL20 : (20:ℝ) ≤ Real.log q := by
      have h1 : Real.log ((2:ℝ)^512) ≤ Real.log q :=
        Real.log_le_log (by positivity) (by exact_mod_cast hq512)
      have h2 : Real.log ((2:ℝ)^512) = 512 * Real.log 2 := by rw [Real.log_pow]; norm_num
      have h3 : (20:ℝ) ≤ 512 * Real.log 2 := by linarith only [Real.log_two_gt_d9]
      linarith only [h1, h2, h3]
    by_cases hB : (H:ℝ) ≤ (q:ℝ)^((k + 1 : ℝ) / (4 * k : ℝ))
    · -- ### case B: H ≤ q^((k+1)/(4k))
      have hHk : (H:ℝ)^((1:ℝ)/(k:ℝ)) ≤ (q:ℝ)^((k + 1 : ℝ) / (4 * k ^ 2)) := by
        calc (H:ℝ)^((1:ℝ)/(k:ℝ)) ≤ ((q:ℝ)^((k + 1 : ℝ) / (4 * k : ℝ)))^((1:ℝ)/(k:ℝ)) :=
              Real.rpow_le_rpow hHnn hB (by positivity)
          _ = (q:ℝ)^((k + 1 : ℝ) / (4 * k : ℝ) * ((1:ℝ)/(k:ℝ))) := by
              rw [← Real.rpow_mul hq0.le]
          _ = (q:ℝ)^((k + 1 : ℝ) / (4 * k ^ 2)) := by
              congr 1
              field_simp
      have hsplit : (H:ℝ) = (H:ℝ)^((1:ℝ)/(k:ℝ)) * (H:ℝ)^(1 - 1/(k:ℝ)) := by
        rw [← Real.rpow_add hHpos]
        have he : (1:ℝ)/(k:ℝ) + (1 - 1/(k:ℝ)) = 1 := by ring
        rw [he, Real.rpow_one]
      calc ‖∑ n ∈ Finset.Ioc N (N + H), χ (n : ZMod q)‖ ≤ (H:ℝ) := htriv N H
        _ = (H:ℝ)^((1:ℝ)/(k:ℝ)) * (H:ℝ)^(1 - 1/(k:ℝ)) := hsplit
        _ ≤ (q:ℝ)^((k + 1 : ℝ) / (4 * k ^ 2)) * (H:ℝ)^(1 - 1/(k:ℝ)) :=
            mul_le_mul_of_nonneg_right hHk (Real.rpow_nonneg hHnn _)
        _ ≤ (2^512 + 2^70 * 600 * Cm * C1 + 2 * Ccs + 1)
              * (q:ℝ)^((k + 1 : ℝ) / (4 * k ^ 2) + ε) * (H:ℝ)^(1 - 1/(k:ℝ)) := by
            have h5 : (q:ℝ)^((k + 1 : ℝ) / (4 * k ^ 2))
                ≤ (q:ℝ)^((k + 1 : ℝ) / (4 * k ^ 2) + ε) :=
              Real.rpow_le_rpow_of_exponent_le hq1 (by linarith only [hε])
            have h6 : (1:ℝ) ≤ 2^512 + 2^70 * 600 * Cm * C1 + 2 * Ccs + 1 := by
              have h7 : (0:ℝ) ≤ 2^70 * 600 * Cm * C1 := by positivity
              linarith only [hCcspos, h7, h512nn]
            calc (q:ℝ)^((k + 1 : ℝ) / (4 * k ^ 2)) * (H:ℝ)^(1 - 1/(k:ℝ))
                ≤ (q:ℝ)^((k + 1 : ℝ) / (4 * k ^ 2) + ε) * (H:ℝ)^(1 - 1/(k:ℝ)) :=
                  mul_le_mul_of_nonneg_right h5 (Real.rpow_nonneg hHnn _)
              _ ≤ (2^512 + 2^70 * 600 * Cm * C1 + 2 * Ccs + 1) * (q:ℝ)^((k + 1 : ℝ) / (4 * k ^ 2) + ε)
                    * (H:ℝ)^(1 - 1/(k:ℝ)) := by
                  rw [mul_assoc]
                  exact le_mul_of_one_le_left (by positivity) h6
    · push_neg at hB
      by_cases hC : (q:ℝ)^((2 * k + 1 : ℝ) / (4 * k : ℝ)) * (Real.log q)^(4*k+8) ≤ (H:ℝ)
      · -- ### case C: Polya-Vinogradov
        have hlog : Real.log (2*(q:ℝ) + 2) ≤ 2 * Real.log q := by
          calc Real.log (2*(q:ℝ) + 2) ≤ Real.log (4*(q:ℝ)) :=
                Real.log_le_log (by positivity) (by linarith only [hq2R])
            _ = Real.log 4 + Real.log (q:ℝ) :=
                Real.log_mul (by norm_num) (ne_of_gt hq0)
            _ = 2*Real.log 2 + Real.log q := by
                rw [show (4:ℝ) = (2:ℝ)^2 by norm_num, Real.log_pow]; norm_num
            _ ≤ 2 * Real.log q := by
                have h3 : (2:ℝ) * Real.log 2 ≤ 20 := by linarith only [Real.log_two_lt_d9]
                linarith only [hL20, h3]
        have hS : ‖∑ n ∈ Finset.Ioc N (N + H), χ (n : ZMod q)‖
            ≤ Ccs * Real.sqrt (q:ℝ) * Real.log (2*(q:ℝ) + 2) := by
          rw [Ioc_eq_Icc' hH1]
          exact hCcs q hq2 χ hχne (N+1) (N+H) (by omega)
        set Me : ℝ := ((4*k+8 : ℕ) : ℝ) * (1 - 1/(k:ℝ)) with hmdef
        have hm1 : (1:ℝ) ≤ Me := by
          have h7 : (1:ℝ)/(k:ℝ) ≤ (1:ℝ)/2 := by
            rw [div_le_div_iff₀ hkposR (by norm_num : (0:ℝ) < 2)]
            linarith only [hk2R]
          have h8 : (8:ℝ) ≤ ((4*k+8 : ℕ) : ℝ) := by push_cast; linarith only [hk1R]
          have h9 : (1:ℝ)/2 ≤ 1 - 1/(k:ℝ) := by linarith only [h7]
          rw [hmdef]
          nlinarith only [h8, h9]
        have hmnn : (0:ℝ) ≤ Me := le_trans zero_le_one hm1
        have hLpos' : (0:ℝ) ≤ Real.log q := by linarith only [hL20]
        have hL1' : (1:ℝ) ≤ Real.log q := by linarith only [hL20]
        have hHlower : (q:ℝ)^(((2*k+1:ℝ)/(4*k:ℝ)) * (1 - 1/(k:ℝ))) * (Real.log q)^Me
            ≤ (H:ℝ)^(1 - 1/(k:ℝ)) := by
          have hpow : ((q:ℝ)^((2*k+1:ℝ)/(4*k:ℝ)) * (Real.log q)^(4*k+8))^(1 - 1/(k:ℝ))
              = (q:ℝ)^(((2*k+1:ℝ)/(4*k:ℝ)) * (1 - 1/(k:ℝ))) * (Real.log q)^Me := by
            have h2 : ((Real.log q)^(4*k+8))^(1 - 1/(k:ℝ)) = (Real.log q)^Me := by
              rw [hmdef, ← Real.rpow_natCast (x := Real.log q) (n := 4*k+8),
                ← Real.rpow_mul hLpos']
            rw [Real.mul_rpow (Real.rpow_nonneg hq0.le _) (pow_nonneg hLpos' _),
              ← Real.rpow_mul hq0.le, h2]
          rw [← hpow]
          exact Real.rpow_le_rpow (by positivity : (0:ℝ) ≤ (q:ℝ)^((2*k+1:ℝ)/(4*k:ℝ)) * (Real.log q)^(4*k+8)) hC (by
            have h3 : (1:ℝ)/(k:ℝ) ≤ 1 := by rw [div_le_one hkposR]; exact hk1R
            linarith only [h3])
        have hterm : (2:ℝ)*Ccs * Real.log q ≤ (2^512 + 2^70 * 600 * Cm * C1 + 2 * Ccs + 1)
            * (q:ℝ)^ε * (Real.log q)^Me := by
          have h1 : Real.log q ≤ (Real.log q)^Me := by
            have h2 := Real.rpow_le_rpow_of_exponent_le hL1' hm1
            rwa [Real.rpow_one] at h2
          have h2 : (0:ℝ) ≤ (Real.log q)^Me := by positivity
          have h3 : (2:ℝ)*Ccs ≤ 2^512 + 2^70 * 600 * Cm * C1 + 2 * Ccs + 1 := by
            have h5 : (0:ℝ) ≤ 2^70 * 600 * Cm * C1 := by positivity
            linarith only [h5, h512nn]
          have h4 : (1:ℝ) ≤ (q:ℝ)^ε := Real.one_le_rpow hq1 hε.le
          calc (2:ℝ)*Ccs * Real.log q
              ≤ (2^512 + 2^70 * 600 * Cm * C1 + 2 * Ccs + 1) * (Real.log q)^Me := by
                calc (2:ℝ)*Ccs * Real.log q
                    ≤ (2^512 + 2^70 * 600 * Cm * C1 + 2 * Ccs + 1) * Real.log q :=
                      mul_le_mul_of_nonneg_right h3 hLpos'
                  _ ≤ (2^512 + 2^70 * 600 * Cm * C1 + 2 * Ccs + 1) * (Real.log q)^Me :=
                      mul_le_mul_of_nonneg_left h1 (by positivity)
            _ ≤ (2^512 + 2^70 * 600 * Cm * C1 + 2 * Ccs + 1) * (q:ℝ)^ε * (Real.log q)^Me := by
                have h6 : (Real.log q)^Me ≤ (q:ℝ)^ε * (Real.log q)^Me :=
                  le_mul_of_one_le_left h2 h4
                calc (2^512 + 2^70 * 600 * Cm * C1 + 2 * Ccs + 1) * (Real.log q)^Me
                    ≤ (2^512 + 2^70 * 600 * Cm * C1 + 2 * Ccs + 1) * ((q:ℝ)^ε * (Real.log q)^Me) :=
                      mul_le_mul_of_nonneg_left h6 (by positivity)
                  _ = (2^512 + 2^70 * 600 * Cm * C1 + 2 * Ccs + 1) * (q:ℝ)^ε * (Real.log q)^Me := by ring
        have hσa : (k + 1 : ℝ) / (4 * k ^ 2) + ε + ((2*k+1:ℝ)/(4*k:ℝ)) * (1 - 1/(k:ℝ))
            = (1:ℝ)/2 + ε := by
          have hkne : (k:ℝ) ≠ 0 := ne_of_gt hkposR
          field_simp
          ring
        have hmid : (q:ℝ)^((1:ℝ)/2 + ε) * (Real.log q)^Me
            ≤ (q:ℝ)^((k + 1 : ℝ) / (4 * k ^ 2) + ε) * (H:ℝ)^(1 - 1/(k:ℝ)) := by
          have h1 : (q:ℝ)^((k + 1 : ℝ) / (4 * k ^ 2) + ε
                + ((2*k+1:ℝ)/(4*k:ℝ)) * (1 - 1/(k:ℝ))) = (q:ℝ)^((1:ℝ)/2 + ε) := by
            rw [hσa]
          calc (q:ℝ)^((1:ℝ)/2 + ε) * (Real.log q)^Me
              = (q:ℝ)^((k + 1 : ℝ) / (4 * k ^ 2) + ε
                  + ((2*k+1:ℝ)/(4*k:ℝ)) * (1 - 1/(k:ℝ))) * (Real.log q)^Me := by rw [h1]
            _ = (q:ℝ)^((k + 1 : ℝ) / (4 * k ^ 2) + ε)
                  * (q:ℝ)^(((2*k+1:ℝ)/(4*k:ℝ)) * (1 - 1/(k:ℝ))) * (Real.log q)^Me := by
                rw [Real.rpow_add hq0]
            _ ≤ (q:ℝ)^((k + 1 : ℝ) / (4 * k ^ 2) + ε) * (H:ℝ)^(1 - 1/(k:ℝ)) := by
                calc (q:ℝ)^((k + 1 : ℝ) / (4 * k ^ 2) + ε)
                      * (q:ℝ)^(((2*k+1:ℝ)/(4*k:ℝ)) * (1 - 1/(k:ℝ))) * (Real.log q)^Me
                    = (q:ℝ)^((k + 1 : ℝ) / (4 * k ^ 2) + ε)
                      * ((q:ℝ)^(((2*k+1:ℝ)/(4*k:ℝ)) * (1 - 1/(k:ℝ))) * (Real.log q)^Me) := by ring
                  _ ≤ (q:ℝ)^((k + 1 : ℝ) / (4 * k ^ 2) + ε) * (H:ℝ)^(1 - 1/(k:ℝ)) :=
                      mul_le_mul_of_nonneg_left hHlower (by positivity)
        have hmain : (2:ℝ)*Ccs * (q:ℝ)^((1:ℝ)/2) * (Real.log q)
            ≤ (2^512 + 2^70 * 600 * Cm * C1 + 2 * Ccs + 1) * (q:ℝ)^((1:ℝ)/2 + ε)
              * (Real.log q)^Me := by
          have he : (q:ℝ)^ε * (q:ℝ)^((1:ℝ)/2) = (q:ℝ)^((1:ℝ)/2 + ε) := by
            rw [← Real.rpow_add hq0]
            congr 1
            ring
          have h : (2:ℝ)*Ccs * (Real.log q) ≤ (2^512 + 2^70 * 600 * Cm * C1 + 2 * Ccs + 1)
              * (q:ℝ)^ε * (Real.log q)^Me := hterm
          calc (2:ℝ)*Ccs * (q:ℝ)^((1:ℝ)/2) * (Real.log q)
              = ((2:ℝ)*Ccs * (Real.log q)) * (q:ℝ)^((1:ℝ)/2) := by ring
            _ ≤ ((2^512 + 2^70 * 600 * Cm * C1 + 2 * Ccs + 1) * (q:ℝ)^ε * (Real.log q)^Me)
                  * (q:ℝ)^((1:ℝ)/2) :=
                mul_le_mul_of_nonneg_right h (Real.rpow_nonneg hq0.le _)
            _ = (2^512 + 2^70 * 600 * Cm * C1 + 2 * Ccs + 1) * (q:ℝ)^((1:ℝ)/2 + ε)
                  * (Real.log q)^Me := by
                rw [show ((2^512 + 2^70 * 600 * Cm * C1 + 2 * Ccs + 1) * (q:ℝ)^ε * (Real.log q)^Me)
                      * (q:ℝ)^((1:ℝ)/2)
                    = (2^512 + 2^70 * 600 * Cm * C1 + 2 * Ccs + 1) * ((q:ℝ)^ε * (q:ℝ)^((1:ℝ)/2))
                      * (Real.log q)^Me from by ring]
                rw [he]
        calc ‖∑ n ∈ Finset.Ioc N (N + H), χ (n : ZMod q)‖
            ≤ Ccs * Real.sqrt (q:ℝ) * Real.log (2*(q:ℝ) + 2) := hS
          _ ≤ Ccs * Real.sqrt (q:ℝ) * (2 * Real.log q) :=
              mul_le_mul_of_nonneg_left hlog (by positivity)
          _ = (2:ℝ)*Ccs * (q:ℝ)^((1:ℝ)/2) * (Real.log q) := by
              rw [Real.sqrt_eq_rpow]; ring
          _ ≤ (2^512 + 2^70 * 600 * Cm * C1 + 2 * Ccs + 1) * (q:ℝ)^((1:ℝ)/2 + ε)
                * (Real.log q)^Me := hmain
          _ ≤ (2^512 + 2^70 * 600 * Cm * C1 + 2 * Ccs + 1)
                * (q:ℝ)^((k + 1 : ℝ) / (4 * k ^ 2) + ε) * (H:ℝ)^(1 - 1/(k:ℝ)) := by
              rw [show (2^512 + 2^70 * 600 * Cm * C1 + 2 * Ccs + 1) * (q:ℝ)^((1:ℝ)/2 + ε)
                    * (Real.log q)^Me
                  = (2^512 + 2^70 * 600 * Cm * C1 + 2 * Ccs + 1)
                    * ((q:ℝ)^((1:ℝ)/2 + ε) * (Real.log q)^Me) from by ring]
              refine (mul_le_mul_of_nonneg_left hmid
                (by positivity : (0:ℝ) ≤ 2^512 + 2^70 * 600 * Cm * C1 + 2 * Ccs + 1)).trans_eq ?_
              ring
      · -- ### case D: core
        push_neg at hC
        have hHhi : (H:ℝ) ≤ (q:ℝ)^((2 * k + 1 : ℝ) / (4 * k : ℝ)) * (Real.log q)^(4*k+8) :=
          le_of_lt hC
        have hHlo : (q:ℝ)^((k + 1 : ℝ) / (4 * k : ℝ)) ≤ (H:ℝ) := le_of_lt hB
        set A : ℝ := (H:ℝ) * (q:ℝ)^(-(1/(2*(k:ℝ)))) with hAdef
        have hA_nn : (0:ℝ) ≤ A := by
          rw [hAdef]; exact mul_nonneg hHnn (Real.rpow_nonneg hq0.le _)
        have hA_ge : (q:ℝ)^((1:ℝ)/8) ≤ A := by
          rw [hAdef]
          have h1 : (q:ℝ)^((k + 1 : ℝ) / (4 * k : ℝ)) * (q:ℝ)^(-(1/(2*(k:ℝ))))
              ≤ (H:ℝ) * (q:ℝ)^(-(1/(2*(k:ℝ)))) :=
            mul_le_mul_of_nonneg_right hHlo (Real.rpow_nonneg hq0.le _)
          have h2 : (q:ℝ)^((k + 1 : ℝ) / (4 * k : ℝ)) * (q:ℝ)^(-(1/(2*(k:ℝ))))
              = (q:ℝ)^(((k:ℝ) - 1) / (4 * k : ℝ)) := by
            rw [← Real.rpow_add hq0]
            congr 1
            field_simp
            ring
          have h3 : (1:ℝ)/8 ≤ ((k:ℝ) - 1) / (4 * k : ℝ) := by
            rw [div_le_div_iff₀ (by norm_num) (by positivity)]
            nlinarith only [hk2R]
          have h4 : (q:ℝ)^((1:ℝ)/8) ≤ (q:ℝ)^(((k:ℝ) - 1) / (4 * k : ℝ)) :=
            Real.rpow_le_rpow_of_exponent_le hq1 h3
          linarith only [h1, h2.ge, h4]
        have hP1 : 1 ≤ Nat.floor A + 1 := Nat.le_add_left 1 _
        have hq512R : (2:ℝ)^512 ≤ (q:ℝ) := by
          have h1 : ((2^512 : ℕ) : ℝ) ≤ (q:ℝ) := Nat.cast_le.mpr hq512
          rwa [Nat.cast_pow, Nat.cast_ofNat] at h1
        have hP64 : 2^64 ≤ Nat.floor A + 1 := by
          have hh : (2:ℝ)^64 ≤ (q:ℝ)^((1:ℝ)/8) := by
            have h := Real.rpow_le_rpow (pow_nonneg (by norm_num : (0:ℝ) ≤ 2) 512) hq512R
              (by norm_num : (0:ℝ) ≤ 1/8)
            have h2 : ((2:ℝ)^512)^((1:ℝ)/8) = (2:ℝ)^64 := by
              rw [← Real.rpow_natCast (x := (2:ℝ)) (n := 512), ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
              norm_num
            linarith only [h, h2.le]
          have hlt : (2:ℝ)^64 < ((Nat.floor A + 1 : ℕ) : ℝ) := by
            have hcast : ((Nat.floor A + 1 : ℕ) : ℝ) = (Nat.floor A : ℝ) + 1 := by
              push_cast; ring
            rw [hcast]
            exact lt_of_le_of_lt (le_trans hh hA_ge) (Nat.lt_floor_add_one A)
          exact_mod_cast hlt.le
        have hPq8 : q ≤ (Nat.floor A + 1)^8 := by
          have h4 : ((q:ℝ)^((1:ℝ)/8))^8 = (q:ℝ) := by
            rw [← Real.rpow_natCast (x := (q:ℝ)^((1:ℝ)/8)) (n := 8), ← Real.rpow_mul hq0.le,
              show ((1:ℝ)/8) * ((8:ℕ):ℝ) = 1 by norm_num, Real.rpow_one]
          have h2 : (q:ℝ) ≤ A^8 := by
            have h := Real.rpow_le_rpow (Real.rpow_nonneg hq0.le _) hA_ge
              (by norm_num : (0:ℝ) ≤ 8)
            have eq : ((q:ℝ)^((1:ℝ)/8))^(8:ℝ) = (q:ℝ) := by
              rw [show ((q:ℝ)^((1:ℝ)/8))^(8:ℝ) = ((q:ℝ)^((1:ℝ)/8))^8 by norm_num, h4]
            have eA : A^(8:ℝ) = A^8 := by norm_num
            rw [eq, eA] at h
            exact h
          have h3 : A^8 < ((Nat.floor A + 1 : ℕ) : ℝ)^8 := by
            have hcast : ((Nat.floor A + 1 : ℕ) : ℝ) = (Nat.floor A : ℝ) + 1 := by
              push_cast; ring
            rw [hcast]
            exact pow_lt_pow_left₀ (Nat.lt_floor_add_one A) hA_nn (by norm_num : 8 ≠ 0)
          have hq8' : (q:ℝ) < (((Nat.floor A + 1)^8 : ℕ) : ℝ) := by
            rw [Nat.cast_pow]
            exact lt_of_le_of_lt h2 h3
          exact_mod_cast hq8'.le
        have hcount := burgess_coprime_window_count_le (q := q) (P := Nat.floor A + 1) hqposN hP64 hPq8
        set CL : ℝ := 300 * Real.log (2 * ((Nat.floor A + 1 : ℕ) : ℝ)) with hCLdef
        have hP1R : (1:ℝ) ≤ ((Nat.floor A + 1 : ℕ) : ℝ) := by exact_mod_cast hP1
        have hCL0 : (0:ℝ) ≤ CL := by
          rw [hCLdef]
          exact mul_nonneg (by norm_num) (Real.log_nonneg (by linarith only [hP1R]))
        set N' : ℤ := ((N % q : ℕ) : ℤ) with hNdef
        have hN'0 : (0:ℤ) ≤ N' := by rw [hNdef]; exact_mod_cast Nat.zero_le _
        have hN'q : N' < (q:ℤ) := by
          rw [hNdef]; exact_mod_cast Nat.mod_lt N (by omega)
        have hsplitP : ((Nat.floor A + 1 : ℕ) : ℝ) * ‖cSum χ N' (N' + (H:ℤ))‖
            ≤ CL * ∑ x ∈ objFinset (Nat.floor A + 1),
                ‖cSum χ (oLo N' q x.1 x.2) (oHi N' q H x.1 x.2)‖ :=
          burgess_split_gen χ N' H (Nat.floor A + 1) hP1 CL hCL0 hcount
        have hsplit' : ((Nat.floor A : ℝ) + 1) * ‖cSum χ N' (N' + (H:ℤ))‖
            ≤ CL * ∑ x ∈ objFinset (Nat.floor A + 1),
                ‖cSum χ (oLo N' q x.1 x.2) (oHi N' q H x.1 x.2)‖ := by
          rw [Nat.cast_add, Nat.cast_one] at hsplitP
          exact hsplitP
        have hcore := burgess_core_gen Cm hCm1 k hk2 hk3 hq60 χ hχne
          (fun L hL => hCmC q χ hχprim hχne L hL) N' hN'0 hN'q H hH1 hHq hHlo hHhi CL hCL0 hsplit'
        have hmod : cSum χ (N:ℤ) ((N:ℤ) + (H:ℤ)) = cSum χ N' (N' + (H:ℤ)) := by
          have hN : (N:ℤ) = N' + (q:ℤ) * ((N / q : ℕ) : ℤ) := by
            rw [hNdef]
            have h := Nat.mod_add_div N q
            exact_mod_cast h.symm
          rw [hN]
          have key := cSum_add_q_mul χ N' (N' + (H:ℤ)) (N/q)
          rw [show N' + (q:ℤ) * ((N / q : ℕ) : ℤ) + (H:ℤ)
              = N' + (H:ℤ) + (q:ℤ) * ((N / q : ℕ) : ℤ) by ring]
          exact key
        -- CL ≤ 600 log q
        have hPle : ((Nat.floor A + 1 : ℕ) : ℝ) ≤ 2*(q:ℝ) := by
          have hA1 : A ≤ (H:ℝ) := by
            rw [hAdef]
            calc (H:ℝ) * (q:ℝ)^(-(1/(2*(k:ℝ)))) ≤ (H:ℝ) * 1 := by
                  apply mul_le_mul_of_nonneg_left _ hHnn
                  rw [Real.rpow_neg hq0.le]
                  exact inv_le_one_of_one_le₀ (Real.one_le_rpow hq1 (by positivity))
              _ = (H:ℝ) := mul_one _
          have hfl : ((Nat.floor A : ℕ) : ℝ) ≤ A := Nat.floor_le hA_nn
          push_cast
          linarith only [hHqR, hq512R, hA1, hfl]
        have hlog_bound : Real.log (2 * ((Nat.floor A + 1 : ℕ) : ℝ)) ≤ 2 * Real.log q := by
          have h1 : Real.log (2 * ((Nat.floor A + 1 : ℕ) : ℝ)) ≤ Real.log (2*(2*(q:ℝ))) :=
            Real.log_le_log (by positivity) (by linarith only [hPle])
          have h2 : Real.log (2*(2*(q:ℝ))) = Real.log 4 + Real.log q := by
            rw [show (2:ℝ)*(2*(q:ℝ)) = 4 * (q:ℝ) by ring,
              Real.log_mul (by norm_num) (ne_of_gt hq0)]
          have h3 : Real.log 4 ≤ Real.log q := by
            have h4' : Real.log 4 = 2 * Real.log 2 := by
              rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]; norm_num
            have h5' : 2 * Real.log 2 ≤ 20 := by linarith only [Real.log_two_lt_d9]
            linarith only [hL20, h4', h5']
          linarith only [h1, h2, h3]
        have hCLle : CL ≤ 600 * Real.log q := by rw [hCLdef]; linarith only [hlog_bound]
        have hLqnn : (0:ℝ) ≤ Real.log q := hqlog.le
        have hPw : (Real.log q)^(10*k+20) * Real.log q = (Real.log q)^(10*k+21) := by
          rw [← pow_succ]
        have hlogabs : (Real.log q)^(10*k+21) ≤ C1 * (q:ℝ)^(ε/2) := hC1 q hq1
        have hstep1 : 2^70 * CL * Cm * (q:ℝ)^((k+1)/(4*k^2:ℝ)) * (H:ℝ)^(1-1/(k:ℝ))
              * (Real.log q)^(10*k+20)
            ≤ 2^70 * 600 * Cm * (q:ℝ)^((k+1)/(4*k^2:ℝ)) * (H:ℝ)^(1-1/(k:ℝ))
              * (Real.log q)^(10*k+21) := by
          have hZ : (0:ℝ) ≤ 2^70 * Cm * (q:ℝ)^((k+1)/(4*k^2:ℝ)) * (H:ℝ)^(1-1/(k:ℝ))
              * (Real.log q)^(10*k+20) := by positivity
          have h := mul_le_mul_of_nonneg_right hCLle hZ
          have e2 : (600 * Real.log q) * (2^70 * Cm * (q:ℝ)^((k+1)/(4*k^2:ℝ))
                * (H:ℝ)^(1-1/(k:ℝ)) * (Real.log q)^(10*k+20))
              = 2^70 * 600 * Cm * (q:ℝ)^((k+1)/(4*k^2:ℝ)) * (H:ℝ)^(1-1/(k:ℝ))
                * (Real.log q)^(10*k+21) := by
            rw [show (600:ℝ) * Real.log q * (2^70 * Cm * (q:ℝ)^((k+1)/(4*k^2:ℝ))
                  * (H:ℝ)^(1-1/(k:ℝ)) * (Real.log q)^(10*k+20))
                = 2^70 * 600 * Cm * (q:ℝ)^((k+1)/(4*k^2:ℝ)) * (H:ℝ)^(1-1/(k:ℝ))
                  * ((Real.log q)^(10*k+20) * Real.log q) from by ring]
            rw [hPw]
          have e1 : CL * (2^70 * Cm * (q:ℝ)^((k+1)/(4*k^2:ℝ)) * (H:ℝ)^(1-1/(k:ℝ))
                * (Real.log q)^(10*k+20))
              = 2^70 * CL * Cm * (q:ℝ)^((k+1)/(4*k^2:ℝ)) * (H:ℝ)^(1-1/(k:ℝ))
                * (Real.log q)^(10*k+20) := by ring
          linarith only [h, e2.le, e1.le]
        have hstep2 : 2^70 * 600 * Cm * (q:ℝ)^((k+1)/(4*k^2:ℝ)) * (H:ℝ)^(1-1/(k:ℝ))
              * (Real.log q)^(10*k+21)
            ≤ 2^70 * 600 * Cm * C1 * (q:ℝ)^((k+1)/(4*k^2:ℝ) + ε/2) * (H:ℝ)^(1-1/(k:ℝ)) := by
          have h1 : 2^70 * 600 * Cm * (q:ℝ)^((k+1)/(4*k^2:ℝ)) * (H:ℝ)^(1-1/(k:ℝ))
                * (Real.log q)^(10*k+21)
              ≤ 2^70 * 600 * Cm * (q:ℝ)^((k+1)/(4*k^2:ℝ)) * (H:ℝ)^(1-1/(k:ℝ))
                * (C1 * (q:ℝ)^(ε/2)) :=
            mul_le_mul_of_nonneg_left hlogabs (by positivity)
          have e : 2^70 * 600 * Cm * (q:ℝ)^((k+1)/(4*k^2:ℝ)) * (H:ℝ)^(1-1/(k:ℝ))
                * (C1 * (q:ℝ)^(ε/2))
              = 2^70 * 600 * Cm * C1 * (q:ℝ)^((k+1)/(4*k^2:ℝ) + ε/2)
                * (H:ℝ)^(1-1/(k:ℝ)) := by
            rw [show 2^70 * 600 * Cm * (q:ℝ)^((k+1)/(4*k^2:ℝ)) * (H:ℝ)^(1-1/(k:ℝ))
                  * (C1 * (q:ℝ)^(ε/2))
                = (2^70 * 600 * Cm * C1) * ((q:ℝ)^((k+1)/(4*k^2:ℝ)) * (q:ℝ)^(ε/2))
                  * (H:ℝ)^(1-1/(k:ℝ)) from by ring,
              ← Real.rpow_add hq0]
          linarith only [h1, e.ge, e]
        have hstep3 : 2^70 * 600 * Cm * C1 * (q:ℝ)^((k+1)/(4*k^2:ℝ) + ε/2) * (H:ℝ)^(1-1/(k:ℝ))
            ≤ (2^512 + 2^70 * 600 * Cm * C1 + 2 * Ccs + 1) * (q:ℝ)^((k+1)/(4*k^2:ℝ) + ε)
              * (H:ℝ)^(1-1/(k:ℝ)) := by
          have h4 : (2^70 * 600 * Cm * C1) ≤ 2^512 + 2^70 * 600 * Cm * C1 + 2 * Ccs + 1 := by
            have h5 : (0:ℝ) ≤ 2 * Ccs := by linarith only [hCcspos]
            linarith only [h5, h512nn]
          have h5 : (q:ℝ)^((k+1)/(4*k^2:ℝ) + ε/2) ≤ (q:ℝ)^((k+1)/(4*k^2:ℝ) + ε) :=
            Real.rpow_le_rpow_of_exponent_le hq1 (by linarith only [hε])
          calc 2^70 * 600 * Cm * C1 * (q:ℝ)^((k+1)/(4*k^2:ℝ) + ε/2) * (H:ℝ)^(1-1/(k:ℝ))
              ≤ (2^512 + 2^70 * 600 * Cm * C1 + 2 * Ccs + 1)
                * (q:ℝ)^((k+1)/(4*k^2:ℝ) + ε/2) * (H:ℝ)^(1-1/(k:ℝ)) := by
                apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hHnn _)
                exact mul_le_mul_of_nonneg_right h4 (by positivity)
            _ ≤ (2^512 + 2^70 * 600 * Cm * C1 + 2 * Ccs + 1)
                * (q:ℝ)^((k+1)/(4*k^2:ℝ) + ε) * (H:ℝ)^(1-1/(k:ℝ)) := by
                apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hHnn _)
                exact mul_le_mul_of_nonneg_left h5 (by positivity)
        calc ‖∑ n ∈ Finset.Ioc N (N + H), χ (n : ZMod q)‖
            = ‖cSum χ (N:ℤ) ((N:ℤ) + (H:ℤ))‖ := by rw [cSum_natCast]
          _ = ‖cSum χ N' (N' + (H:ℤ))‖ := by rw [hmod]
          _ ≤ 2^70 * CL * Cm * (q:ℝ)^((k+1)/(4*k^2:ℝ)) * (H:ℝ)^(1-1/(k:ℝ))
                * (Real.log q)^(10*k+20) := hcore
          _ ≤ (2^512 + 2^70 * 600 * Cm * C1 + 2 * Ccs + 1)
                * (q:ℝ)^((k+1)/(4*k^2:ℝ) + ε) * (H:ℝ)^(1-1/(k:ℝ)) :=
              le_trans hstep1 (le_trans hstep2 hstep3)

end Commons.NumberTheory.DirichletCharacter
