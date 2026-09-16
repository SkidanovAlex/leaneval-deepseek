import Submission.ZagierHoffmanProof.AmbKEquiv
import Submission.ZagierHoffmanProof.OmUnit

/-!
# The valuations entering Step 3 of ND21 §5 (the `π̃`-divisibility)

Step 3 of the proof of Theorem B (Dac, §5.3) deduces, from the rationality statement
`f_𝔱(θ) ∈ K` of Step 2 and the bridge `𝓛(𝔰)(θ) = Γ_𝔰ζ_A(𝔰)/π̃^{w(𝔰)}`, that the weight
`m = w(𝔰)` of the relevant suffix is divisible by `q - 1`.

The arithmetic input is:

* `v (π̃) = exp q`, where `π̃ := 1/Ω(θ)` (`v_ambPiTilde`) — so that `v (π̃^m) = exp (q m)`;
* `v (K^×) ⊆ exp ((q-1)ℤ)` (`v_mem_ambK`) — so that `exp (q m) ∈ exp ((q-1)ℤ)`;
* hence `(q-1) | q m`, and `(q-1) | m` because `(q-1)` and `q` are coprime
  (`dvd_pred_of_piTilde_pow_mem_ambK`).

## Main results

* `v_eval₂_ambTheta`, `v_ambKPolyHom`, `v_ambKHom`, `v_ambKEquiv`, `v_mem_ambK`.
* `evalSeriesGen_ambOmega_eq`, `v_evalSeriesGen_ambOmega`, `v_ambPiTilde`, `v_ambPiTilde_pow`.
* ★★★ `dvd_pred_of_piTilde_pow_mem_ambK`.
-/

set_option autoImplicit false
open Polynomial
open scoped WithZero Topology

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F]

/-! ## §1. The valuation of a polynomial in `θ` -/

/-- The valuation of a single term `c·θ^i` of a polynomial in `θ` for `c ≠ 0`:
`exp ((q-1) i)` (the top-degree term dominates because `v θ = exp (q-1) > 1`). -/
lemma v_ambCoeff_mul_pow_ambTheta (c : F) (hc : c ≠ 0) (i : ℕ) :
    Valued.v ((algebraMap F (Ambient F)) c * (ambTheta F) ^ i)
      = WithZero.exp (((Nat.card F : ℚ) - 1) * (i : ℚ)) := by
  rw [algebraMap_ambient_eq, map_mul, v_ambCoeff F c hc, one_mul, map_pow, v_ambTheta,
    ← WithZero.exp_nsmul, nsmul_eq_mul, mul_comm]

lemma v_zero_mul_pow_ambTheta (i : ℕ) :
    Valued.v ((algebraMap F (Ambient F)) 0 * (ambTheta F) ^ i) = 0 := by
  rw [map_zero, zero_mul, map_zero]

/-- **The valuation of `p(θ)`**: `exp ((q-1)·deg p)` for a nonzero polynomial `p`.  The top-degree
term strictly dominates, by `Valuation.map_sum_eq_of_lt` and `v (c θ^i) = exp ((q-1) i)`. -/
lemma v_eval₂_ambTheta (p : Polynomial F) (hp : p ≠ 0) :
    Valued.v (p.eval₂ (algebraMap F (Ambient F)) (ambTheta F))
      = WithZero.exp (((Nat.card F : ℚ) - 1) * ((p.natDegree : ℕ) : ℚ)) := by
  rw [Polynomial.eval₂_eq_sum_range]
  have hdeg : p.coeff p.natDegree ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hp
  have hq1 : (0 : ℚ) < (Nat.card F : ℚ) - 1 := by
    have h2 : (2 : ℚ) ≤ (Nat.card F : ℚ) := by
      exact_mod_cast (show (2 : ℕ) ≤ Nat.card F from two_le_ambCard F)
    linarith
  have hkey : ∀ i ∈ Finset.range (p.natDegree + 1) \ {p.natDegree},
      Valued.v ((algebraMap F (Ambient F)) (p.coeff i) * (ambTheta F) ^ i)
        < Valued.v ((algebraMap F (Ambient F)) (p.coeff p.natDegree)
            * (ambTheta F) ^ p.natDegree) := by
    intro i hi
    rw [Finset.mem_sdiff, Finset.mem_range, Finset.mem_singleton] at hi
    obtain ⟨hlt, _⟩ := hi
    have hilt : i < p.natDegree := by omega
    by_cases hci : p.coeff i = 0
    · rw [hci, v_zero_mul_pow_ambTheta F i,
        v_ambCoeff_mul_pow_ambTheta F (p.coeff p.natDegree) hdeg p.natDegree]
      exact WithZero.exp_pos
    · rw [v_ambCoeff_mul_pow_ambTheta F (p.coeff i) hci i,
        v_ambCoeff_mul_pow_ambTheta F (p.coeff p.natDegree) hdeg p.natDegree,
        WithZero.exp_lt_exp]
      have hi' : (i : ℚ) < (p.natDegree : ℚ) := by exact_mod_cast hilt
      nlinarith
  rw [Valuation.map_sum_eq_of_lt (v := (Valued.v : Valuation (Ambient F) ℚᵐ⁰))
    (j := p.natDegree) (Finset.mem_range.mpr (Nat.lt_succ_self _)) hkey,
    v_ambCoeff_mul_pow_ambTheta F (p.coeff p.natDegree) hdeg p.natDegree]

/-! ## §2. The valuation of an element of `ambK F = F_q(θ)` -/

lemma v_ambKPolyHom (p : Polynomial F) (hp : p ≠ 0) :
    Valued.v ((ambKPolyHom F p : ↥(ambK F)) : Ambient F)
      = WithZero.exp (((Nat.card F : ℚ) - 1) * ((p.natDegree : ℕ) : ℚ)) := by
  rw [ambKPolyHom_apply]
  exact v_eval₂_ambTheta F p hp

lemma v_ambKHom_zero : Valued.v (((ambKHom F 0 : ↥(ambK F)) : Ambient F)) = 0 := by
  simp

/-- **The valuation of an element of `K = F_q(θ)`**, via `RatFunc.intDegree`: for a nonzero
rational function `x`, `v (x(θ)) = exp ((q-1)·intDegree x)`. -/
lemma v_ambKHom (x : RatFunc F) (hx : x ≠ 0) :
    Valued.v ((ambKHom F x : ↥(ambK F)) : Ambient F)
      = WithZero.exp (((Nat.card F : ℚ) - 1) * (x.intDegree : ℚ)) := by
  have hnum : RatFunc.num x ≠ 0 := RatFunc.num_ne_zero hx
  have hden : RatFunc.denom x ≠ 0 := RatFunc.denom_ne_zero x
  have hxdec : x = algebraMap (Polynomial F) (RatFunc F) (RatFunc.num x)
      / algebraMap (Polynomial F) (RatFunc F) (RatFunc.denom x) :=
    (RatFunc.num_div_denom x).symm
  have h1 : ((ambKHom F x : ↥(ambK F)) : Ambient F)
      = (((ambKPolyHom F (RatFunc.num x) : ↥(ambK F)) : Ambient F))
        / (((ambKPolyHom F (RatFunc.denom x) : ↥(ambK F)) : Ambient F)) := by
    conv_lhs => rw [hxdec]
    rw [map_div₀, ambKHom_algebraMap, ambKHom_algebraMap]
    push_cast
    ring
  rw [h1, map_div₀, v_ambKPolyHom F _ hnum, v_ambKPolyHom F _ hden, ← WithZero.exp_sub]
  congr 1
  rw [RatFunc.intDegree]
  push_cast
  ring

lemma v_ambKEquiv (x : RatFunc F) (hx : x ≠ 0) :
    Valued.v (((ambKEquiv F x : ↥(ambK F)) : Ambient F))
      = WithZero.exp (((Nat.card F : ℚ) - 1) * (x.intDegree : ℚ)) := by
  rw [show (ambKEquiv F x : ↥(ambK F)) = ambKHom F x from rfl]
  exact v_ambKHom F x hx

/-- ★★ **The valuation of a nonzero element of `K = F_q(θ)` is a `(q-1)`-st power**:
`v x ∈ exp ((q-1)ℤ)`. -/
theorem v_mem_ambK {x : Ambient F} (hx : x ∈ ambK F) (hx0 : x ≠ 0) :
    ∃ k : ℤ, Valued.v x = WithZero.exp (((Nat.card F : ℚ) - 1) * (k : ℚ)) := by
  set y : RatFunc F := (ambKEquiv F).symm ⟨x, hx⟩ with hy
  have hxy : ((ambKEquiv F y : ↥(ambK F)) : Ambient F) = x := by
    rw [hy]
    simp only [RingEquiv.apply_symm_apply]
  have hy0 : y ≠ 0 := by
    intro h
    rw [h, map_zero] at hxy
    simp only [Subfield.coe_zero] at hxy
    exact hx0 hxy.symm
  refine ⟨y.intDegree, ?_⟩
  rw [← hxy]
  exact v_ambKEquiv F y hy0

/-! ## §3. The period `π̃ = 1/Ω(θ)` -/

/-- The period `π̃ := 1/Ω(θ)` (Dac, §4.2). -/
noncomputable def ambPiTilde : Ambient F := (evalSeriesGen (ambOmega F) (ambTheta F))⁻¹

theorem evalSeriesGen_ambOmega_eq :
    evalSeriesGen (ambOmega F) (ambTheta F)
      = ambMu F * evalSeriesGen (atOmegaGen (Nat.card F) (ambTheta F)) (ambTheta F) := by
  rw [ambOmega, evalSeriesGen_C_mul]

theorem v_evalSeriesGen_ambOmega :
    Valued.v (evalSeriesGen (ambOmega F) (ambTheta F))
      = WithZero.exp (-(Nat.card F : ℚ)) := by
  rw [evalSeriesGen_ambOmega_eq, map_mul, v_ambMu, v_evalSeriesGen_atOmegaGen F 0, mul_one]

theorem evalSeriesGen_ambOmega_ne_zero : evalSeriesGen (ambOmega F) (ambTheta F) ≠ 0 := by
  intro h
  have h1 := v_evalSeriesGen_ambOmega F
  rw [h, map_zero] at h1
  exact absurd h1.symm (WithZero.exp_ne_zero)

/-- ★★★ **`v (π̃) = exp q`** (Dac §5.3 Step 3). -/
theorem v_ambPiTilde : Valued.v (ambPiTilde F) = WithZero.exp (Nat.card F : ℚ) := by
  rw [ambPiTilde, map_inv₀, v_evalSeriesGen_ambOmega, ← WithZero.exp_neg]
  congr 1
  ring

theorem ambPiTilde_ne_zero : ambPiTilde F ≠ 0 := by
  intro h
  have h1 := v_ambPiTilde F
  rw [h, map_zero] at h1
  exact absurd h1.symm (WithZero.exp_ne_zero)

/-- `v (π̃^m) = exp (q m)`. -/
theorem v_ambPiTilde_pow (m : ℕ) :
    Valued.v ((ambPiTilde F) ^ m) = WithZero.exp ((Nat.card F : ℚ) * m) := by
  rw [map_pow, v_ambPiTilde, ← WithZero.exp_nsmul]
  congr 1
  rw [nsmul_eq_mul, mul_comm]

/-! ## §4. The `π̃`-divisibility of Step 3 -/

/-- ★★★ **Step 3's arithmetic core**: if a power `π̃^m` lies in `K = F_q(θ)`, then `q - 1` divides
`m`.  Indeed `v (π̃^m) = exp (q m)` while `v (K^×) ⊆ exp ((q-1)ℤ)`. -/
theorem dvd_pred_of_piTilde_pow_mem_ambK {m : ℕ}
    (h : (ambPiTilde F) ^ m ∈ ambK F) : (Nat.card F - 1) ∣ m := by
  have hq2 : 2 ≤ Nat.card F := two_le_ambCard F
  have hq1 : 1 ≤ Nat.card F := by omega
  rcases Nat.eq_zero_or_pos m with hm | hm
  · rw [hm]; exact dvd_zero _
  · have hne : (ambPiTilde F) ^ m ≠ 0 := pow_ne_zero _ (ambPiTilde_ne_zero F)
    obtain ⟨k, hk⟩ := v_mem_ambK F h hne
    rw [v_ambPiTilde_pow] at hk
    have hexp : (Nat.card F : ℚ) * (m : ℚ) = ((Nat.card F : ℚ) - 1) * (k : ℚ) :=
      WithZero.exp_injective hk
    have hcast : (((Nat.card F - 1 : ℕ)) : ℚ) = (Nat.card F : ℚ) - 1 := by
      rw [Nat.cast_sub hq1, Nat.cast_one]
    have hZ : (((Nat.card F - 1 : ℕ)) : ℤ) * k = ((Nat.card F : ℕ) : ℤ) * ((m : ℕ) : ℤ) := by
      have h2 : ((((Nat.card F - 1 : ℕ)) : ℤ) * k : ℚ)
          = ((((Nat.card F : ℕ)) : ℤ) * ((m : ℕ) : ℤ) : ℚ) := by
        push_cast
        rw [hcast]
        exact hexp.symm
      exact_mod_cast h2
    have hdivZ : (((Nat.card F - 1 : ℕ)) : ℤ)
        ∣ ((((Nat.card F : ℕ)) : ℤ) * ((m : ℕ) : ℤ)) := ⟨k, hZ.symm⟩
    have hdivN : (Nat.card F - 1) ∣ (Nat.card F) * m := by
      have h3 : (((Nat.card F - 1 : ℕ)) : ℤ) ∣ ((((Nat.card F) * m : ℕ)) : ℤ) := by
        rw [Nat.cast_mul]
        exact hdivZ
      exact_mod_cast h3
    have hcop : Nat.Coprime (Nat.card F - 1) (Nat.card F) :=
      (Nat.coprime_self_sub_left hq1).mpr (Nat.coprime_one_left _)
    exact hcop.dvd_of_dvd_mul_left hdivN

end ZagierHoffmanPositiveChar
