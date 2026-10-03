import Mathlib
import Submission.Work.FIArea6.S16ErrTwo.ArithA
import Submission.Work.FIArea6.S16ErrTwo.Decomp
import Submission.Work.FIArea7.isBetaCoeff6_mass_caps
import Submission.Work.FIArea6.S16ErrTwo.s16_arith_endgame

set_option autoImplicit false
set_option maxHeartbeats 100000000

namespace Work.FIArea6.S16ErrTwo

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- `farMass` is the sum of the pointwise `farT`. -/
lemma farMass_eq_sum_farT (Pa : Work.FITop.Params) (X d : ℕ) (β : GaussianInt → ℂ) :
    (∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa, farT Pa X d β z1 z2)
      = farMass Pa X d β := by
  simp only [farT, farMass]

/-- Comparison tool: `L ^ a ≤ N ^ b` as soon as `4 a ≤ b √L`, for `L = log N ≥ 1`. -/
lemma logN_rpow_le_sqrt (Pa : Work.FITop.Params) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 < b)
    (hL : 1 ≤ Real.log Pa.N) (h : 4 * a ≤ b * Real.sqrt (Real.log Pa.N)) :
    (Real.log Pa.N) ^ a ≤ Pa.N ^ b := by
  have hN1 : (1:ℝ) ≤ Pa.N := Pa.hN1
  have hL0 : (0:ℝ) < Real.log Pa.N := lt_of_lt_of_le one_pos hL
  have hlog : Real.log (Real.log Pa.N) ≤ 2 * Real.sqrt (Real.log Pa.N) := by
    have h := Real.log_le_rpow_div hL0.le (show (0:ℝ) < 1/2 by norm_num)
    rw [Real.rpow_div_two_eq_sqrt 1 hL0.le, Real.rpow_one] at h
    linarith
  rw [Real.rpow_def_of_pos hL0, Real.rpow_def_of_pos (by linarith : (0:ℝ) < Pa.N)]
  apply Real.exp_le_exp.mpr
  have hs : (0:ℝ) ≤ Real.sqrt (Real.log Pa.N) := Real.sqrt_nonneg _
  have hsq : Real.sqrt (Real.log Pa.N) * Real.sqrt (Real.log Pa.N) = Real.log Pa.N :=
    Real.mul_self_sqrt hL0.le
  nlinarith [h, hlog, hs, hsq, ha]

/-- Monomial comparison `L ^ (a ν + b) ≤ N ^ c` for `0 ≤ a ≤ 3`, `0 ≤ b ≤ 8`, `c ≥ 1/2`. -/
lemma logN_rpow_mono (Pa : Work.FITop.Params) (hL : 1 ≤ Real.log Pa.N)
    (hs : 16 * (3 * Work.FITop4.nuU + 50) ≤ Real.sqrt (Real.log Pa.N))
    (a b c : ℝ) (ha : 0 ≤ a) (ha3 : a ≤ 3) (hb : 0 ≤ b) (hb8 : b ≤ 8) (hc : (1:ℝ)/2 ≤ c) :
    (Real.log Pa.N) ^ (a * Work.FITop4.nuU + b) ≤ Pa.N ^ c := by
  have hnu : (0:ℝ) ≤ Work.FITop4.nuU := Work.FIArea6.nuU_pos.le
  refine logN_rpow_le_sqrt Pa (a * Work.FITop4.nuU + b) c ?_ (by linarith) hL ?_
  · nlinarith
  · have h2 : 4 * (3 * Work.FITop4.nuU + 8) ≤ (1/2:ℝ) * Real.sqrt (Real.log Pa.N) := by
      nlinarith [hs, hnu]
    have h3 : (1/2:ℝ) * Real.sqrt (Real.log Pa.N) ≤ c * Real.sqrt (Real.log Pa.N) :=
      mul_le_mul_of_nonneg_right hc (Real.sqrt_nonneg _)
    nlinarith [h2, h3, hnu, ha3, hb8]

/-- `X ^ k ≤ L ^ (k ν)` for a coefficient with `X ≤ L ^ ν`. -/
lemma X_pow_le (Pa : Work.FITop.Params) (X : ℕ) (k : ℕ) (hL0 : 0 < Real.log Pa.N)
    (hXle : (X : ℝ) ≤ (Real.log Pa.N) ^ Work.FITop4.nuU) :
    (X : ℝ) ^ k ≤ (Real.log Pa.N) ^ (k * Work.FITop4.nuU) := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk; simp
  calc (X : ℝ) ^ k ≤ ((Real.log Pa.N) ^ Work.FITop4.nuU) ^ k :=
        pow_le_pow_left₀ (by positivity) hXle k
    _ = (Real.log Pa.N) ^ ((k : ℝ) * Work.FITop4.nuU) := by
        rw [← Real.rpow_natCast ((Real.log Pa.N) ^ Work.FITop4.nuU) k,
            ← Real.rpow_mul (le_of_lt hL0)]
        congr 1
        push_cast
        ring
/-- **The §16 error bound, conditional on the four mass estimates.**  Given the four mass bounds
(diagonal, near-diagonal, far, non-coprime — exactly the statements proved in
`S16ErrTwo/diagMass_le.lean`, `nearMass_le.lean`, `farMass_le.lean`, `ncMass_le.lean`), for
`x₀ ≤ Pa.x`, `1 ≤ X` and `X ≤ (log N)^nuU`,

`2 Σ_{d ≤ X} (φ(d)/d)·‖Vd d − MainSum X d‖ ≤ C·((Pz)⁻¹ + X⁻¹)·N²·log N`.

*Route.*  With `U := 1 + log(2+N)`, `θ := Pa.θ`, `Sq := Σ_{z ∈ boxN} ‖βz‖²`:

1. `Decomp.norm_Vd_sub_MainSum_le` gives, for each `1 ≤ d ≤ X` (its two extra hypotheses
   `4X ≤ Pz` and `X ≤ N` are derived from the threshold, cf. `Work.FIArea6.four_mul_le_Pz`),
   `‖Vd d − MainSum X d‖ ≤ 16U·(diagMass + nearMass d + ncMass d) + farMass d` (because
   `Bc Pa = 16U`), all four masses being sums over `boxN × boxN`.
2. Summing over `d ∈ Icc 1 X` with weights `φ(d)/d` and using the four hypotheses plus
   `Σ_{d ≤ X} φ(d)/d ≤ X` (`S16ErrTwo.totient_div_sum_le`) reduces the claim to
   `2·16U·(X·Cd·Sq + Cn·Sq·U·(X²+θ√NX+√N+θN/X) + Cc·N²U¹⁴X/Pz) + 2Cf·Sq·NU/X² ≤ C·T`
   with `T = (Pz⁻¹+X⁻¹)N²log N`, using `Sq ≤ Cs(θ²N+1)U⁴` from `S16ErrTwo.sq_mass_le`.
3. Numerically (`S16ErrTwo.threshold_facts` + `X ≤ (log N)^nuU`): with
   `x₀ = X0 = exp(exp(2ν+100)(1024(3ν+50)²+1))` one has `θ²X³U⁶ ≤ N`, `θ³X²U⁶ ≤ √N`,
   `X²U¹⁵ ≤ Pz`, `XU⁶ ≤ N`, `θ³U⁶ ≤ 1000`, `θ²U⁵ ≤ 1000`, `U⁶ ≤ N`, `N^{3/8} ≤ θ√N`, and each of
   the products above is of size `≤ K·N²log N·(X⁻¹ + Pz⁻¹)` for `K` an explicit constant
   combination of `Cd, Cn, Cc, Cf, Cs` (e.g. `10⁶·(Cd+Cn+Cc+Cf+Cs+1)⁴`). -/
theorem error_bound_of_pieces
    (hdiag : ∃ C : ℝ, 0 < C ∧
      ∀ (Pa : Work.FITop.Params) (φ : ℝ) (z0 : GaussianInt) (β : GaussianInt → ℂ),
        Work.FITop4.IsBetaCoeff6 Pa φ z0 β →
        Work.FIArea6.S16ErrTwo.diagMass Pa β ≤ C * (∑ z ∈ Work.FITop.boxN Pa, ‖β z‖ ^ (2 : ℕ)))
    (hnear : ∃ C : ℝ, 0 < C ∧
      ∀ (Pa : Work.FITop.Params) (X : ℕ) (φ : ℝ) (z0 : GaussianInt) (β : GaussianInt → ℂ),
        Work.FITop4.IsBetaCoeff6 Pa φ z0 β → 1 ≤ X → 4 * X ≤ Pa.Pz →
        (∑ d ∈ Finset.Icc 1 X, ((Nat.totient d : ℝ) / (d : ℝ)) * Work.FIArea6.S16ErrTwo.nearMass Pa X d β)
          ≤ C * (∑ z ∈ Work.FITop.boxN Pa, ‖β z‖ ^ (2 : ℕ)) * (1 + Real.log (2 + X))
              * ((X : ℝ) ^ (2 : ℕ) + Pa.θ * Real.sqrt Pa.N * X + Real.sqrt Pa.N + Pa.θ * Pa.N / X))
    (hfar : ∃ C : ℝ, 0 < C ∧
      ∀ (Pa : Work.FITop.Params) (X : ℕ) (φ : ℝ) (z0 : GaussianInt) (β : GaussianInt → ℂ),
        Work.FITop4.IsBetaCoeff6 Pa φ z0 β → 1 ≤ X → 4 * X ≤ Pa.Pz →
        (∑ d ∈ Finset.Icc 1 X, ((Nat.totient d : ℝ) / (d : ℝ)) * Work.FIArea6.S16ErrTwo.farMass Pa X d β)
          ≤ C * (∑ z ∈ Work.FITop.boxN Pa, ‖β z‖ ^ (2 : ℕ)) * Pa.N
              * (1 + Real.log (2 + Pa.N)) / (X : ℝ) ^ (2 : ℕ))
    (hnc : ∃ C : ℝ, 0 < C ∧
      ∀ (Pa : Work.FITop.Params) (X : ℕ) (φ : ℝ) (z0 : GaussianInt) (β : GaussianInt → ℂ),
        Work.FITop4.IsBetaCoeff6 Pa φ z0 β → 1 ≤ X → 4 * X ≤ Pa.Pz →
        (∑ d ∈ Finset.Icc 1 X, ((Nat.totient d : ℝ) / (d : ℝ)) * Work.FIArea6.S16ErrTwo.ncMass Pa d β)
          ≤ C * Pa.N ^ (2 : ℕ) * (1 + Real.log (2 + Pa.N)) ^ (14 : ℕ) * (X : ℝ) / (Pa.Pz : ℝ)) :
    ∃ C x0 : ℝ, 0 < C ∧ 0 < x0 ∧
    ∀ (Pa : Work.FITop.Params) (X : ℕ) (φ : ℝ) (z0 : GaussianInt) (β : GaussianInt → ℂ),
      x0 ≤ (Pa.x : ℝ) → Work.FITop4.IsBetaCoeff6 Pa φ z0 β → 1 ≤ X →
      (X : ℝ) ≤ (Real.log Pa.N) ^ Work.FITop4.nuU →
      2 * ∑ d ∈ Finset.Icc 1 X, ((Nat.totient d : ℝ) / (d : ℝ)) *
          ‖Work.FIArea6.Vd Pa d β - Work.FIArea6.MainSum Pa X d β‖
        ≤ C * ((Pa.Pz : ℝ)⁻¹ + (X : ℝ)⁻¹) * Pa.N ^ (2 : ℕ) * Real.log Pa.N := by
  obtain ⟨Cd, hCdpos, hdiag⟩ := hdiag
  obtain ⟨Cn, hCnpos, hnear⟩ := hnear
  obtain ⟨Cf, hCfpos, hfar⟩ := hfar
  obtain ⟨Cc, hCcpos, hnc⟩ := hnc
  have hSpos : (0:ℝ) < Cd + Cn + Cc + Cf + 1 := by linarith
  refine ⟨(10:ℝ)^(12:ℕ) * (Cd + Cn + Cc + Cf + 1)^(4:ℕ), X0,
    by positivity, X0_pos, ?_⟩
  intro Pa X φ z0 β hx hβ hX hXle
  have hx0 : X0 ≤ (Pa.x : ℝ) := hx
  have hx' : Real.exp (4 * Real.exp (Work.FITop4.nuU + 2)) ≤ (Pa.x : ℝ) := by
    have hν0' : (0:ℝ) ≤ Work.FITop4.nuU := Work.FIArea6.nuU_pos.le
    have hX0 : Real.exp (4 * Real.exp (Work.FITop4.nuU + 2)) ≤ X0 := by
      rw [X0]
      apply Real.exp_le_exp.mpr
      have h2 : (1:ℝ) ≤ 1024 * (3 * Work.FITop4.nuU + 50)^(2:ℕ) + 1 := by
        nlinarith [hν0', sq_nonneg (3*Work.FITop4.nuU + 50)]
      have h3 : (4:ℝ) * Real.exp (Work.FITop4.nuU + 2) ≤ Real.exp (2*Work.FITop4.nuU + 100) := by
        have h4 : (4:ℝ) = Real.exp (Real.log 4) := (Real.exp_log (by norm_num)).symm
        rw [h4, ← Real.exp_add]
        apply Real.exp_le_exp.mpr
        have hl4 : Real.log (4:ℝ) = 2 * Real.log 2 := by
          rw [show (4:ℝ) = 2^(2:ℕ) by norm_num, Real.log_pow]; norm_num
        rw [hl4]
        nlinarith [hν0', Real.log_two_lt_d9]
      calc (4:ℝ) * Real.exp (Work.FITop4.nuU + 2) ≤ Real.exp (2*Work.FITop4.nuU + 100) := h3
        _ ≤ Real.exp (2*Work.FITop4.nuU + 100) * (1024 * (3 * Work.FITop4.nuU + 50) ^ (2:ℕ) + 1) :=
            le_mul_of_one_le_right (Real.exp_pos _).le h2
    linarith [hx0]
  obtain ⟨hf1, hf2, hf3, hf4, hf5, hf6⟩ := threshold_facts Pa hx0
  have hν0 : (0:ℝ) ≤ Work.FITop4.nuU := Work.FIArea6.nuU_pos.le
  have hx3 : (3:ℝ) ≤ (Pa.x : ℝ) := by exact_mod_cast Pa.hx
  have hx1 : (1:ℝ) < (Pa.x : ℝ) := by linarith
  have hxpos : (0:ℝ) < (Pa.x : ℝ) := by linarith
  have hN1 : (1:ℝ) ≤ Pa.N := Pa.hN1
  have hNpos : (0:ℝ) < Pa.N := by linarith
  set L : ℝ := Real.log Pa.N with hLdef
  set U : ℝ := 1 + Real.log (2 + Pa.N) with hUdef
  have hlogNgt : ((1:ℝ)/4 + Pa.η) * Real.log (Pa.x : ℝ) < Real.log Pa.N := by
    have h := Real.log_lt_log (Real.rpow_pos_of_pos hxpos ((1:ℝ)/4 + Pa.η)) Pa.hNlo
    rwa [Real.log_rpow (by linarith)] at h
  have hL1 : (1:ℝ) ≤ L := by
    rw [hLdef]
    have h2 : (1:ℝ) ≤ ((1:ℝ)/4 + Pa.η) * Real.log (Pa.x : ℝ) := by
      nlinarith [hf4, Pa.hη, hν0]
    linarith
  have hL0 : (0:ℝ) < L := lt_of_lt_of_le one_pos hL1
  have hNx : Pa.N ≤ (Pa.x : ℝ) := by
    calc Pa.N ≤ (Pa.x : ℝ)^((1:ℝ)/2) * (Real.log (Pa.x : ℝ))^(-Pa.B) := le_of_lt Pa.hNhi
      _ ≤ (Pa.x : ℝ)^((1:ℝ)/2) * 1 := by
          apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (by linarith) _)
          exact Real.rpow_le_one_of_one_le_of_nonpos hf5 (by linarith [Pa.hB])
      _ = (Pa.x : ℝ)^((1:ℝ)/2) := by ring
      _ ≤ (Pa.x : ℝ)^((1:ℝ)) := Real.rpow_le_rpow_of_exponent_le (le_of_lt hx1) (by norm_num)
      _ = (Pa.x : ℝ) := Real.rpow_one _
  have hLt : L ≤ Real.log (Pa.x : ℝ) := by
    rw [hLdef]
    exact Real.log_le_log hNpos hNx
  have hsqrt : 16 * (3 * Work.FITop4.nuU + 50) ≤ Real.sqrt L := by
    rw [hLdef]
    have hLge : Real.log (Pa.x : ℝ) * ((1:ℝ)/4) ≤ Real.log Pa.N := by
      nlinarith [hlogNgt, Pa.hη]
    have hsq4 : Real.sqrt ((1:ℝ)/4) = 1/2 := by
      rw [show ((1:ℝ)/4) = (1/2)^2 by norm_num, Real.sqrt_sq (by norm_num)]
    have h1 : Real.sqrt (Real.log (Pa.x : ℝ)) * (1/2) ≤ Real.sqrt (Real.log Pa.N) := by
      calc Real.sqrt (Real.log (Pa.x : ℝ)) * (1/2)
          = Real.sqrt (Real.log (Pa.x : ℝ)) * Real.sqrt ((1:ℝ)/4) := by rw [hsq4]
        _ = Real.sqrt (Real.log (Pa.x : ℝ) * ((1:ℝ)/4)) :=
            (Real.sqrt_mul (by linarith [hf5]) ((1:ℝ)/4)).symm
        _ ≤ Real.sqrt (Real.log Pa.N) := Real.sqrt_le_sqrt hLge
    nlinarith [hf2, h1]
  have hL0' : (0:ℝ) < Real.log Pa.N := by rw [← hLdef]; exact hL0
  have hL1' : (1:ℝ) ≤ Real.log Pa.N := by rw [← hLdef]; exact hL1
  have hLt' : Real.log Pa.N ≤ Real.log (Pa.x : ℝ) := by rw [← hLdef]; exact hLt
  have hsqrt' : 16 * (3 * Work.FITop4.nuU + 50) ≤ Real.sqrt (Real.log Pa.N) := by
    rw [← hLdef]; exact hsqrt
  have hL100 : (100:ℝ) ≤ L := by
    rw [hLdef]
    have h2 : (100:ℝ) ≤ ((1:ℝ)/4 + Pa.η) * Real.log (Pa.x : ℝ) := by
      nlinarith [hf4, Pa.hη, hν0]
    linarith
  have hlog3le : Real.log 3 ≤ 1.4 := by
    have h : Real.log (3:ℝ) < Real.log 4 := Real.log_lt_log (by norm_num) (by norm_num)
    have h4 : Real.log (4:ℝ) < 1.4 := by
      have h2 : Real.log (4:ℝ) = 2 * Real.log 2 := by
        rw [show (4:ℝ) = 2^(2:ℕ) by norm_num, Real.log_pow]; norm_num
      nlinarith [Real.log_two_lt_d9]
    linarith
  have hU1 : (1:ℝ) ≤ U := by
    rw [hUdef]
    have h := Real.log_nonneg (by linarith : (1:ℝ) ≤ 2 + Pa.N)
    linarith
  have hUL : U ≤ 3 * L := by
    rw [hUdef, hLdef]
    have h1 : Real.log (2 + Pa.N) ≤ Real.log 3 + Real.log Pa.N := by
      calc Real.log (2 + Pa.N) ≤ Real.log (3 * Pa.N) :=
            Real.log_le_log (by linarith) (by linarith)
        _ = Real.log 3 + Real.log Pa.N := Real.log_mul (by norm_num) (by linarith)
    have hL100' : (100:ℝ) ≤ Real.log Pa.N := by rw [← hLdef]; exact hL100
    linarith
  have hULraw : (1:ℝ) + Real.log (2 + Pa.N) ≤ 3 * Real.log Pa.N := by
    have := hUL; rw [hUdef, hLdef] at this; exact this
  have hUnn : (0:ℝ) ≤ U := le_trans (by norm_num) hU1
  have hθ0 : (0:ℝ) ≤ Pa.θ := Pa.hθ0.le
  have hθ1 : Pa.θ ≤ 1 := by
    rw [Pa.hθ]
    have hA'0 : (0:ℝ) ≤ Pa.A' := by have h1 := Pa.hA'; have h2 := Pa.hA; linarith
    exact Real.rpow_le_one_of_one_le_of_nonpos (le_trans (by norm_num) hf5) (by linarith)
  have hθL4 : Pa.θ * L^(4:ℕ) ≤ 1 := by
    rw [hLdef]
    have hA'20 : (2:ℝ)^(20:ℕ) ≤ Pa.A' := by
      have h1 := Pa.hA'; have h2 := Pa.hA; linarith
    have hθle : Pa.θ ≤ (Real.log (Pa.x : ℝ))^(-((2:ℝ)^(20:ℕ))) := by
      rw [Pa.hθ]
      exact Real.rpow_le_rpow_of_exponent_le hf5 (by linarith)
    have hL4 : (Real.log Pa.N)^(4:ℕ) ≤ (Real.log (Pa.x : ℝ))^((2:ℝ)^(20:ℕ)) := by
      have h1 : (Real.log Pa.N)^(4:ℕ) ≤ (Real.log (Pa.x : ℝ))^((4:ℕ):ℝ) := by
        rw [Real.rpow_natCast]
        exact pow_le_pow_left₀ hL0'.le hLt' 4
      have h2 : (Real.log (Pa.x : ℝ))^((4:ℕ):ℝ) ≤ (Real.log (Pa.x : ℝ))^((2:ℝ)^(20:ℕ)) :=
        Real.rpow_le_rpow_of_exponent_le hf5 (by norm_num)
      linarith
    calc Pa.θ * (Real.log Pa.N)^(4:ℕ)
        ≤ (Real.log (Pa.x : ℝ))^(-((2:ℝ)^(20:ℕ))) * (Real.log (Pa.x : ℝ))^((2:ℝ)^(20:ℕ)) :=
          mul_le_mul hθle hL4 (by positivity) (by positivity)
      _ = 1 := by
          have hlogx0 : (0:ℝ) < Real.log (Pa.x : ℝ) := by linarith [hf5]
          rw [← Real.rpow_add hlogx0, show -((2:ℝ)^(20:ℕ)) + (2:ℝ)^(20:ℕ) = 0 by ring,
            Real.rpow_zero]
  have hXpos : (0:ℝ) < (X:ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hX)
  have hXN : (X:ℝ) ≤ Pa.N := by
    have h1 : (Real.log Pa.N)^Work.FITop4.nuU ≤ Pa.N^(1:ℝ) :=
      logN_rpow_le_sqrt Pa _ 1 hν0 (by norm_num) hL1'
        (by nlinarith [hsqrt', hν0])
    rw [Real.rpow_one] at h1
    exact le_trans hXle h1
  have hlogXle : Real.log (2 + (X:ℝ)) ≤ Real.log (2 + Pa.N) :=
    Real.log_le_log (by linarith) (by linarith)
  have hXLU : 1 + Real.log (2 + (X:ℝ)) ≤ U := by
    rw [hUdef]; linarith
  have hPz4 : 4 * X ≤ Pa.Pz := Work.FIArea6.four_mul_le_Pz Pa X hx' hXle
  have hPz2 : (2:ℝ) ≤ (Pa.Pz:ℝ) := by exact_mod_cast Pa.hP2
  have hPzpos : (0:ℝ) < (Pa.Pz:ℝ) := by linarith
  have hPzU : (X:ℝ)^(2:ℕ) * U^(15:ℕ) ≤ (Pa.Pz:ℝ) := by
    rw [hUdef]
    have hXUpos : (0:ℝ) < (X:ℝ)^(2:ℕ) * (1 + Real.log (2+Pa.N))^(15:ℕ) := by
      have h := Real.log_nonneg (by linarith : (1:ℝ) ≤ 2 + Pa.N)
      positivity
    rw [← Real.log_le_log_iff hXUpos hPzpos]
    have hlogX : Real.log (X:ℝ) ≤ Work.FITop4.nuU * Real.log (Real.log Pa.N) := by
      calc Real.log (X:ℝ) ≤ Real.log ((Real.log Pa.N)^Work.FITop4.nuU) :=
            Real.log_le_log (by positivity) hXle
        _ = Work.FITop4.nuU * Real.log (Real.log Pa.N) := Real.log_rpow hL0' _
    have hlogU : Real.log (1 + Real.log (2+Pa.N)) ≤ Real.log 3 + Real.log (Real.log Pa.N) := by
      have h2 : (0:ℝ) < 1 + Real.log (2+Pa.N) := by
        have h := Real.log_nonneg (by linarith : (1:ℝ) ≤ 2 + Pa.N); linarith
      have h3 : Real.log (1 + Real.log (2+Pa.N)) ≤ Real.log (3 * Real.log Pa.N) :=
        Real.log_le_log h2 hULraw
      rwa [Real.log_mul (by norm_num) (ne_of_gt hL0')] at h3
    have hlogL_u : Real.log (Real.log Pa.N) ≤ Real.log (Real.log (Pa.x:ℝ)) :=
      Real.log_le_log hL0' hLt'
    have hkey : Real.log ((X:ℝ)^(2:ℕ) * (1 + Real.log (2+Pa.N))^(15:ℕ))
        ≤ (Real.log (Real.log (Pa.x:ℝ)))^(2:ℕ) := by
      rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
      have hu : (0:ℝ) ≤ Real.log (Real.log (Pa.x:ℝ)) := by linarith [hf1, hν0]
      have hstep1 : 2 * Real.log (X:ℝ) ≤ 2 * (Work.FITop4.nuU * Real.log (Real.log Pa.N)) := by
        linarith [hlogX]
      have hstep2 : 15 * Real.log (1 + Real.log (2+Pa.N))
          ≤ 15 * (Real.log 3 + Real.log (Real.log Pa.N)) := by linarith [hlogU]
      have hstep3 : 2 * (Work.FITop4.nuU * Real.log (Real.log Pa.N))
            + 15 * (Real.log 3 + Real.log (Real.log Pa.N))
          ≤ (Real.log (Real.log (Pa.x:ℝ)))^(2:ℕ) := by
        have h1 : 2*Work.FITop4.nuU + 15 ≤ Real.log (Real.log (Pa.x:ℝ)) - 85 := by
          linarith [hf1]
        have h2 : 15 * Real.log 3 ≤ 85 * Real.log (Real.log (Pa.x:ℝ)) := by
          nlinarith [hlog3le, hu]
        nlinarith [h1, hu, h2, hlogL_u, hν0]
      have h12 : 2 * Real.log (X:ℝ) + 15 * Real.log (1 + Real.log (2+Pa.N))
          ≤ 2 * (Work.FITop4.nuU * Real.log (Real.log Pa.N))
            + 15 * (Real.log 3 + Real.log (Real.log Pa.N)) := add_le_add hstep1 hstep2
      exact le_trans h12 hstep3
    linarith [hkey, Pa.hPlo]
  set Sq : ℝ := ∑ z ∈ Work.FITop.boxN Pa, ‖β z‖ ^ (2:ℕ) with hSqdef
  set Wt : ℝ := (X:ℝ)^(2:ℕ) + Pa.θ * Real.sqrt Pa.N * (X:ℝ) + Real.sqrt Pa.N
    + Pa.θ * Pa.N / (X:ℝ) with hWdef
  have hSqnn : (0:ℝ) ≤ Sq := by rw [hSqdef]; positivity
  have hWnn : (0:ℝ) ≤ Wt := by
    rw [hWdef]
    have h1 : (0:ℝ) ≤ (X:ℝ)^(2:ℕ) := sq_nonneg _
    have h2 : (0:ℝ) ≤ Pa.θ * Real.sqrt Pa.N * (X:ℝ) := by positivity
    have h3 : (0:ℝ) ≤ Real.sqrt Pa.N := Real.sqrt_nonneg _
    have h4 : (0:ℝ) ≤ Pa.θ * Pa.N / (X:ℝ) := by positivity
    linarith
  have hSq_le : Sq ≤ 1000 * (Pa.θ * Pa.N + Real.sqrt Pa.N + 1) * U^(3:ℕ) := by
    have h := (Work.FIArea7.isBetaCoeff6_mass_caps hβ).2
    have hlogU : Real.log (2 + Pa.N) ≤ U := by rw [hUdef]; linarith
    have hlogU0 : (0:ℝ) ≤ Real.log (2 + Pa.N) := Real.log_nonneg (by linarith)
    calc Sq ≤ 1000 * (Pa.θ * Pa.N + Real.sqrt Pa.N + 1) * (Real.log (2 + Pa.N))^(3:ℕ) := by
          rw [hSqdef, Work.FITop.boxN]; exact h
      _ ≤ 1000 * (Pa.θ * Pa.N + Real.sqrt Pa.N + 1) * U^(3:ℕ) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact pow_le_pow_left₀ hlogU0 hlogU 3
  have hdiag' : diagMass Pa β ≤ Cd * Sq := by rw [hSqdef]; exact hdiag Pa φ z0 β hβ
  have hnear' : ∑ d ∈ Finset.Icc 1 X, ((Nat.totient d : ℝ) / (d : ℝ)) * nearMass Pa X d β
      ≤ Cn * Sq * (1 + Real.log (2 + (X:ℝ))) * Wt := by
    have h := hnear Pa X φ z0 β hβ hX hPz4
    rw [← hSqdef, ← hWdef] at h
    exact h
  have hfar' : ∑ d ∈ Finset.Icc 1 X, ((Nat.totient d : ℝ) / (d : ℝ)) * farMass Pa X d β
      ≤ Cf * Sq * Pa.N * (1 + Real.log (2 + Pa.N)) / (X:ℝ)^(2:ℕ) := by
    have h := hfar Pa X φ z0 β hβ hX hPz4
    rw [← hSqdef] at h
    exact h
  have hnc' : ∑ d ∈ Finset.Icc 1 X, ((Nat.totient d : ℝ) / (d : ℝ)) * ncMass Pa d β
      ≤ Cc * Pa.N^(2:ℕ) * (1 + Real.log (2 + Pa.N))^(14:ℕ) * (X:ℝ) / (Pa.Pz:ℝ) :=
    hnc Pa X φ z0 β hβ hX hPz4
  have hφnn : ∀ d ∈ Finset.Icc 1 X, (0:ℝ) ≤ (Nat.totient d : ℝ) / (d : ℝ) := by
    intro d _
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hpt : ∀ d ∈ Finset.Icc 1 X, ‖Work.FIArea6.Vd Pa d β - Work.FIArea6.MainSum Pa X d β‖
      ≤ Bc Pa * (diagMass Pa β + nearMass Pa X d β + ncMass Pa d β) + farMass Pa X d β := by
    intro d hd
    obtain ⟨hd1, hdX⟩ := Finset.mem_Icc.mp hd
    have h := norm_Vd_sub_MainSum_le hβ hd1 hdX hX hPz4 hXN
    rwa [farMass_eq_sum_farT] at h
  have hBc : Bc Pa = 16 * U := by rw [Bc, hUdef]; ring
  have hstep1 : ∑ d ∈ Finset.Icc 1 X, ((Nat.totient d : ℝ) / (d : ℝ)) *
        ‖Work.FIArea6.Vd Pa d β - Work.FIArea6.MainSum Pa X d β‖
      ≤ ∑ d ∈ Finset.Icc 1 X, ((Nat.totient d : ℝ) / (d : ℝ)) *
          (16 * U * (diagMass Pa β + nearMass Pa X d β + ncMass Pa d β) + farMass Pa X d β) := by
    refine Finset.sum_le_sum (fun d hd => ?_)
    have h := hpt d hd
    rw [hBc] at h
    exact mul_le_mul_of_nonneg_left h (hφnn d hd)
  have hdist : ∀ d : ℕ, ((Nat.totient d : ℝ) / (d : ℝ)) *
        (16 * U * (diagMass Pa β + nearMass Pa X d β + ncMass Pa d β) + farMass Pa X d β)
      = 16 * U * diagMass Pa β * ((Nat.totient d : ℝ) / (d : ℝ))
        + 16 * U * (((Nat.totient d : ℝ) / (d : ℝ)) * nearMass Pa X d β)
        + 16 * U * (((Nat.totient d : ℝ) / (d : ℝ)) * ncMass Pa d β)
        + ((Nat.totient d : ℝ) / (d : ℝ)) * farMass Pa X d β := by
    intro d
    ring
  have hstep2 : ∑ d ∈ Finset.Icc 1 X, ((Nat.totient d : ℝ) / (d : ℝ)) *
          (16 * U * (diagMass Pa β + nearMass Pa X d β + ncMass Pa d β) + farMass Pa X d β)
      = 16 * U * diagMass Pa β * (∑ d ∈ Finset.Icc 1 X, (Nat.totient d : ℝ) / (d : ℝ))
        + 16 * U * (∑ d ∈ Finset.Icc 1 X, ((Nat.totient d : ℝ) / (d : ℝ)) * nearMass Pa X d β)
        + 16 * U * (∑ d ∈ Finset.Icc 1 X, ((Nat.totient d : ℝ) / (d : ℝ)) * ncMass Pa d β)
        + ∑ d ∈ Finset.Icc 1 X, ((Nat.totient d : ℝ) / (d : ℝ)) * farMass Pa X d β := by
    rw [Finset.sum_congr rfl (fun d _ => hdist d)]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
    rw [← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
  have htot : (∑ d ∈ Finset.Icc 1 X, (Nat.totient d : ℝ) / (d : ℝ)) ≤ (X:ℝ) :=
    totient_div_sum_le X hX
  have hA : 16 * U * diagMass Pa β * (∑ d ∈ Finset.Icc 1 X, (Nat.totient d : ℝ) / (d : ℝ))
      ≤ 16 * U * ((X:ℝ) * Cd * Sq) := by
    have h1 : diagMass Pa β * (∑ d ∈ Finset.Icc 1 X, (Nat.totient d : ℝ) / (d : ℝ))
        ≤ (X:ℝ) * (Cd * Sq) := by
      calc diagMass Pa β * (∑ d ∈ Finset.Icc 1 X, (Nat.totient d : ℝ) / (d : ℝ))
          ≤ (Cd * Sq) * (X:ℝ) := mul_le_mul hdiag' htot (by positivity) (by positivity)
        _ = (X:ℝ) * (Cd * Sq) := by ring
    calc 16 * U * diagMass Pa β * (∑ d ∈ Finset.Icc 1 X, (Nat.totient d : ℝ) / (d : ℝ))
        = 16 * U * (diagMass Pa β * (∑ d ∈ Finset.Icc 1 X, (Nat.totient d : ℝ) / (d : ℝ))) := by
          ring
      _ ≤ 16 * U * ((X:ℝ) * (Cd * Sq)) :=
          mul_le_mul_of_nonneg_left h1 (mul_nonneg (by norm_num) hUnn)
      _ = 16 * U * ((X:ℝ) * Cd * Sq) := by ring
  have hB : 16 * U * (∑ d ∈ Finset.Icc 1 X, ((Nat.totient d : ℝ) / (d : ℝ)) * nearMass Pa X d β)
      ≤ 16 * U * (Cn * Sq * (1 + Real.log (2 + (X:ℝ))) * Wt) :=
    mul_le_mul_of_nonneg_left hnear' (mul_nonneg (by norm_num) hUnn)
  have hC : 16 * U * (∑ d ∈ Finset.Icc 1 X, ((Nat.totient d : ℝ) / (d : ℝ)) * ncMass Pa d β)
      ≤ 16 * U * (Cc * Pa.N^(2:ℕ) * (1 + Real.log (2 + Pa.N))^(14:ℕ) * (X:ℝ) / (Pa.Pz:ℝ)) :=
    mul_le_mul_of_nonneg_left hnc' (mul_nonneg (by norm_num) hUnn)
  have hD : (∑ d ∈ Finset.Icc 1 X, ((Nat.totient d : ℝ) / (d : ℝ)) * farMass Pa X d β)
      ≤ Cf * Sq * Pa.N * (1 + Real.log (2 + Pa.N)) / (X:ℝ)^(2:ℕ) := hfar'
  have hsum : ∑ d ∈ Finset.Icc 1 X, ((Nat.totient d : ℝ) / (d : ℝ)) *
        ‖Work.FIArea6.Vd Pa d β - Work.FIArea6.MainSum Pa X d β‖
      ≤ 16 * U * ((X:ℝ) * Cd * Sq) + 16 * U * (Cn * Sq * (1 + Real.log (2 + (X:ℝ))) * Wt)
        + 16 * U * (Cc * Pa.N^(2:ℕ) * (1 + Real.log (2 + Pa.N))^(14:ℕ) * (X:ℝ) / (Pa.Pz:ℝ))
        + Cf * Sq * Pa.N * (1 + Real.log (2 + Pa.N)) / (X:ℝ)^(2:ℕ) := by
    rw [hstep2] at hstep1
    linarith [hstep1, hA, hB, hC, hD]
  have hν' : (0:ℝ) ≤ Work.FITop4.nuU := hν0
  have hmon341 : L^(3*Work.FITop4.nuU+4) ≤ Pa.N := by
    rw [hLdef]
    simpa [Real.rpow_one] using logN_rpow_mono Pa hL1' hsqrt' 3 4 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hmon34h : L^(3*Work.FITop4.nuU+4) ≤ Real.sqrt Pa.N := by
    rw [hLdef]
    simpa [Real.sqrt_eq_rpow] using logN_rpow_mono Pa hL1' hsqrt' 3 4 ((1:ℝ)/2)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hmon24h : L^(2*Work.FITop4.nuU+4) ≤ Real.sqrt Pa.N := by
    rw [hLdef]
    simpa [Real.sqrt_eq_rpow] using logN_rpow_mono Pa hL1' hsqrt' 2 4 ((1:ℝ)/2)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hmon24o : L^(2*Work.FITop4.nuU+4) ≤ Pa.N := by
    rw [hLdef]
    simpa [Real.rpow_one] using logN_rpow_mono Pa hL1' hsqrt' 2 4 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hmon14h : L^(1*Work.FITop4.nuU+4) ≤ Real.sqrt Pa.N := by
    rw [hLdef]
    simpa [Real.sqrt_eq_rpow] using logN_rpow_mono Pa hL1' hsqrt' 1 4 ((1:ℝ)/2)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hmon03h : L^(0*Work.FITop4.nuU+3) ≤ Real.sqrt Pa.N := by
    rw [hLdef]
    simpa [Real.sqrt_eq_rpow] using logN_rpow_mono Pa hL1' hsqrt' 0 3 ((1:ℝ)/2)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hmon03o : L^(0*Work.FITop4.nuU+3) ≤ Pa.N := by
    rw [hLdef]
    simpa [Real.rpow_one] using logN_rpow_mono Pa hL1' hsqrt' 0 3 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hsqN : Real.sqrt Pa.N * Real.sqrt Pa.N = Pa.N := Real.mul_self_sqrt (le_of_lt hNpos)
  have hL3h : L^3 ≤ Real.sqrt Pa.N := by
    have h : L^(0*Work.FITop4.nuU+3) = L^3 := by
      rw [show (0:ℝ)*Work.FITop4.nuU+3 = 3 by ring]; norm_num
    rwa [h] at hmon03h
  have hL3o : L^3 ≤ Pa.N := by
    have h : L^(0*Work.FITop4.nuU+3) = L^3 := by
      rw [show (0:ℝ)*Work.FITop4.nuU+3 = 3 by ring]; norm_num
    rwa [h] at hmon03o
  have hθL3 : Pa.θ * L^3 ≤ 1 := by
    have h1 : L^3 ≤ L^4 := by
      have h2 : (0:ℝ) ≤ L^3 := by positivity
      calc L^3 = L^3 * 1 := by ring
        _ ≤ L^3 * L := mul_le_mul_of_nonneg_left hL1 h2
        _ = L^4 := by ring
    nlinarith [hθL4, hθ0, h1]
  have hX3L4 : (X:ℝ)^(3:ℕ) * L^4 ≤ L^(3*Work.FITop4.nuU+4) := by
    rw [hLdef]
    have h1 := X_pow_le Pa X 3 hL0' hXle
    have h2 : (X:ℝ)^(3:ℕ) * (Real.log Pa.N)^(4:ℕ)
        ≤ (Real.log Pa.N)^(3*Work.FITop4.nuU) * (Real.log Pa.N)^(4:ℕ) :=
      mul_le_mul_of_nonneg_right h1 (by positivity)
    have h3 : (Real.log Pa.N)^(3*Work.FITop4.nuU) * (Real.log Pa.N)^(4:ℕ)
        = (Real.log Pa.N)^(3*Work.FITop4.nuU+4) := by
      rw [← Real.rpow_natCast (Real.log Pa.N) 4, ← Real.rpow_add hL0',
        show ((4:ℕ):ℝ) = (4:ℝ) by norm_num]
    linarith [h2, h3.le, h3.ge]
  have hX2L4 : (X:ℝ)^(2:ℕ) * L^4 ≤ L^(2*Work.FITop4.nuU+4) := by
    rw [hLdef]
    have h1 := X_pow_le Pa X 2 hL0' hXle
    have h2 : (X:ℝ)^(2:ℕ) * (Real.log Pa.N)^(4:ℕ)
        ≤ (Real.log Pa.N)^(2*Work.FITop4.nuU) * (Real.log Pa.N)^(4:ℕ) :=
      mul_le_mul_of_nonneg_right h1 (by positivity)
    have h3 : (Real.log Pa.N)^(2*Work.FITop4.nuU) * (Real.log Pa.N)^(4:ℕ)
        = (Real.log Pa.N)^(2*Work.FITop4.nuU+4) := by
      rw [← Real.rpow_natCast (Real.log Pa.N) 4, ← Real.rpow_add hL0',
        show ((4:ℕ):ℝ) = (4:ℝ) by norm_num]
    linarith [h2, h3.le, h3.ge]
  have hXL4 : (X:ℝ) * L^4 ≤ L^(1*Work.FITop4.nuU+4) := by
    rw [hLdef]
    have h1 : (X:ℝ) * (Real.log Pa.N)^(4:ℕ) ≤ (Real.log Pa.N)^(Work.FITop4.nuU) * (Real.log Pa.N)^(4:ℕ) :=
      mul_le_mul_of_nonneg_right hXle (by positivity)
    have h3 : (Real.log Pa.N)^(Work.FITop4.nuU) * (Real.log Pa.N)^(4:ℕ)
        = (Real.log Pa.N)^(1*Work.FITop4.nuU+4) := by
      rw [← Real.rpow_natCast (Real.log Pa.N) 4, ← Real.rpow_add hL0',
        show ((4:ℕ):ℝ) = (4:ℝ) by norm_num,
        show (1:ℝ) * Work.FITop4.nuU = Work.FITop4.nuU by ring]
    linarith [h1, h3.le, h3.ge]
  have hW12 : L^4 * ((X:ℝ) * Wt) * (Pa.θ * Pa.N + Real.sqrt Pa.N + 1) ≤ 12 * Pa.N^(2:ℕ) := by
    have hXW : (X:ℝ) * Wt = (X:ℝ)^(3:ℕ) + Pa.θ * Real.sqrt Pa.N * (X:ℝ)^(2:ℕ)
        + Real.sqrt Pa.N * (X:ℝ) + Pa.θ * Pa.N := by
      rw [hWdef]
      field_simp
      try ring
    rw [hXW]
    have hexp : L^4 * ((X:ℝ)^(3:ℕ) + Pa.θ * Real.sqrt Pa.N * (X:ℝ)^(2:ℕ) + Real.sqrt Pa.N * (X:ℝ)
            + Pa.θ * Pa.N) * (Pa.θ * Pa.N + Real.sqrt Pa.N + 1)
        = L^4*(Pa.θ*Pa.N*(X:ℝ)^(3:ℕ)) + L^4*(Real.sqrt Pa.N*(X:ℝ)^(3:ℕ)) + L^4*((X:ℝ)^(3:ℕ))
          + L^4*(Pa.θ^(2:ℕ)*(Pa.N*Real.sqrt Pa.N)*(X:ℝ)^(2:ℕ))
          + L^4*(Pa.θ*((Real.sqrt Pa.N)*(Real.sqrt Pa.N))*(X:ℝ)^(2:ℕ))
          + L^4*(Pa.θ*Real.sqrt Pa.N*(X:ℝ)^(2:ℕ))
          + L^4*(Pa.θ*(Pa.N*Real.sqrt Pa.N)*(X:ℝ))
          + L^4*(((Real.sqrt Pa.N)*(Real.sqrt Pa.N))*(X:ℝ))
          + L^4*(Real.sqrt Pa.N*(X:ℝ))
          + L^4*(Pa.θ^(2:ℕ)*Pa.N^(2:ℕ)) + L^4*(Pa.θ*(Pa.N*Real.sqrt Pa.N))
          + L^4*(Pa.θ*Pa.N) := by ring
    rw [hexp]
    have ht1 : L^4*(Pa.θ*Pa.N*(X:ℝ)^(3:ℕ)) ≤ Pa.N^(2:ℕ) := by
      have h1 : Pa.θ * Pa.N * ((X:ℝ)^(3:ℕ) * L^4) ≤ Pa.θ * Pa.N * L^(3*Work.FITop4.nuU+4) :=
        mul_le_mul_of_nonneg_left hX3L4 (by positivity)
      have h2 : Pa.θ * Pa.N * L^(3*Work.FITop4.nuU+4) ≤ Pa.N * Pa.N := by
        have h3 : Pa.θ * Pa.N ≤ Pa.N := by nlinarith [hθ0, hθ1, hN1]
        exact mul_le_mul h3 hmon341 (by positivity) (by positivity)
      calc L^4*(Pa.θ*Pa.N*(X:ℝ)^(3:ℕ)) = Pa.θ * Pa.N * ((X:ℝ)^(3:ℕ) * L^4) := by ring
        _ ≤ Pa.θ * Pa.N * L^(3*Work.FITop4.nuU+4) := h1
        _ ≤ Pa.N * Pa.N := h2
        _ = Pa.N^(2:ℕ) := by ring
    have ht2 : L^4*(Real.sqrt Pa.N*(X:ℝ)^(3:ℕ)) ≤ Pa.N^(2:ℕ) := by
      have h1 : Real.sqrt Pa.N * ((X:ℝ)^(3:ℕ) * L^4) ≤ Real.sqrt Pa.N * L^(3*Work.FITop4.nuU+4) :=
        mul_le_mul_of_nonneg_left hX3L4 (Real.sqrt_nonneg _)
      have h2 : Real.sqrt Pa.N * L^(3*Work.FITop4.nuU+4) ≤ Real.sqrt Pa.N * Real.sqrt Pa.N :=
        mul_le_mul_of_nonneg_left hmon34h (Real.sqrt_nonneg _)
      calc L^4*(Real.sqrt Pa.N*(X:ℝ)^(3:ℕ)) = Real.sqrt Pa.N * ((X:ℝ)^(3:ℕ) * L^4) := by ring
        _ ≤ Real.sqrt Pa.N * L^(3*Work.FITop4.nuU+4) := h1
        _ ≤ Real.sqrt Pa.N * Real.sqrt Pa.N := h2
        _ = Pa.N := hsqN
        _ ≤ Pa.N^(2:ℕ) := by nlinarith [hN1]
    have ht3 : L^4*((X:ℝ)^(3:ℕ)) ≤ Pa.N^(2:ℕ) := by
      have h1 : (X:ℝ)^(3:ℕ) * L^4 ≤ L^(3*Work.FITop4.nuU+4) := hX3L4
      calc L^4*((X:ℝ)^(3:ℕ)) = (X:ℝ)^(3:ℕ) * L^4 := by ring
        _ ≤ L^(3*Work.FITop4.nuU+4) := h1
        _ ≤ Pa.N := hmon341
        _ ≤ Pa.N^(2:ℕ) := by nlinarith [hN1]
    have ht4 : L^4*(Pa.θ^(2:ℕ)*(Pa.N*Real.sqrt Pa.N)*(X:ℝ)^(2:ℕ)) ≤ Pa.N^(2:ℕ) := by
      have h1 : Pa.θ^(2:ℕ) * (Pa.N*Real.sqrt Pa.N) * ((X:ℝ)^(2:ℕ) * L^4)
          ≤ Pa.θ^(2:ℕ) * (Pa.N*Real.sqrt Pa.N) * Real.sqrt Pa.N := by
        have h2 : (X:ℝ)^(2:ℕ) * L^4 ≤ Real.sqrt Pa.N := hX2L4.trans hmon24h
        exact mul_le_mul_of_nonneg_left h2 (by positivity)
      have h3 : Pa.θ^(2:ℕ) * (Pa.N*Real.sqrt Pa.N) * Real.sqrt Pa.N ≤ Pa.N * Pa.N := by
        have h4 : Pa.θ^(2:ℕ) ≤ 1 := by nlinarith [hθ0, hθ1]
        have h5 : Pa.θ^(2:ℕ) * (Pa.N*Real.sqrt Pa.N) * Real.sqrt Pa.N
            ≤ 1 * (Pa.N*Real.sqrt Pa.N) * Real.sqrt Pa.N :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h4 (by positivity))
            (Real.sqrt_nonneg _)
        calc Pa.θ^(2:ℕ) * (Pa.N*Real.sqrt Pa.N) * Real.sqrt Pa.N
            ≤ 1 * (Pa.N*Real.sqrt Pa.N) * Real.sqrt Pa.N := h5
          _ = Pa.N * (Real.sqrt Pa.N * Real.sqrt Pa.N) := by ring
          _ = Pa.N * Pa.N := by rw [hsqN]
      calc L^4*(Pa.θ^(2:ℕ)*(Pa.N*Real.sqrt Pa.N)*(X:ℝ)^(2:ℕ))
          = Pa.θ^(2:ℕ) * (Pa.N*Real.sqrt Pa.N) * ((X:ℝ)^(2:ℕ) * L^4) := by ring
        _ ≤ Pa.θ^(2:ℕ) * (Pa.N*Real.sqrt Pa.N) * Real.sqrt Pa.N := h1
        _ ≤ Pa.N * Pa.N := h3
        _ = Pa.N^(2:ℕ) := by ring
    have ht5 : L^4*(Pa.θ*Pa.N*(X:ℝ)^(2:ℕ)) ≤ Pa.N^(2:ℕ) := by
      have h1 : Pa.θ * Pa.N * ((X:ℝ)^(2:ℕ) * L^4) ≤ Pa.θ * Pa.N * Real.sqrt Pa.N :=
        mul_le_mul_of_nonneg_left (hX2L4.trans hmon24h) (by positivity)
      have h2 : Pa.θ * Pa.N * Real.sqrt Pa.N ≤ Pa.N * Pa.N := by
        have h3 : Pa.θ * Pa.N ≤ Pa.N := by nlinarith [hθ0, hθ1, hN1]
        have h4 : Real.sqrt Pa.N ≤ Pa.N := by nlinarith [hsqN, hN1, Real.sqrt_nonneg Pa.N]
        exact mul_le_mul h3 h4 (Real.sqrt_nonneg _) (by positivity)
      calc L^4*(Pa.θ*Pa.N*(X:ℝ)^(2:ℕ)) = Pa.θ * Pa.N * ((X:ℝ)^(2:ℕ) * L^4) := by ring
        _ ≤ Pa.θ * Pa.N * Real.sqrt Pa.N := h1
        _ ≤ Pa.N * Pa.N := h2
        _ = Pa.N^(2:ℕ) := by ring
    have ht6 : L^4*(Pa.θ*Real.sqrt Pa.N*(X:ℝ)^(2:ℕ)) ≤ Pa.N^(2:ℕ) := by
      have h1 : Pa.θ * Real.sqrt Pa.N * ((X:ℝ)^(2:ℕ) * L^4) ≤ Pa.θ * Real.sqrt Pa.N * Real.sqrt Pa.N :=
        mul_le_mul_of_nonneg_left (hX2L4.trans hmon24h) (by positivity)
      calc L^4*(Pa.θ*Real.sqrt Pa.N*(X:ℝ)^(2:ℕ))
          = Pa.θ * Real.sqrt Pa.N * ((X:ℝ)^(2:ℕ) * L^4) := by ring
        _ ≤ Pa.θ * Real.sqrt Pa.N * Real.sqrt Pa.N := h1
        _ = Pa.θ * Pa.N := by rw [mul_assoc, hsqN]
        _ ≤ Pa.N^(2:ℕ) := by nlinarith [hθ0, hθ1, hN1]
    have ht7 : L^4*(Pa.θ*(Pa.N*Real.sqrt Pa.N)*(X:ℝ)) ≤ Pa.N^(2:ℕ) := by
      have h1 : Pa.θ * (Pa.N*Real.sqrt Pa.N) * ((X:ℝ) * L^4)
          ≤ Pa.θ * (Pa.N*Real.sqrt Pa.N) * Real.sqrt Pa.N :=
        mul_le_mul_of_nonneg_left (hXL4.trans hmon14h) (by positivity)
      have h2 : Pa.θ * (Pa.N*Real.sqrt Pa.N) * Real.sqrt Pa.N ≤ Pa.N * Pa.N := by
        have h5 : Pa.θ * (Pa.N*Real.sqrt Pa.N) * Real.sqrt Pa.N
            ≤ 1 * (Pa.N*Real.sqrt Pa.N) * Real.sqrt Pa.N :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hθ1 (by positivity))
            (Real.sqrt_nonneg _)
        calc Pa.θ * (Pa.N*Real.sqrt Pa.N) * Real.sqrt Pa.N
            ≤ 1 * (Pa.N*Real.sqrt Pa.N) * Real.sqrt Pa.N := h5
          _ = Pa.N * (Real.sqrt Pa.N * Real.sqrt Pa.N) := by ring
          _ = Pa.N * Pa.N := by rw [hsqN]
      calc L^4*(Pa.θ*(Pa.N*Real.sqrt Pa.N)*(X:ℝ))
          = Pa.θ * (Pa.N*Real.sqrt Pa.N) * ((X:ℝ) * L^4) := by ring
        _ ≤ Pa.θ * (Pa.N*Real.sqrt Pa.N) * Real.sqrt Pa.N := h1
        _ ≤ Pa.N * Pa.N := h2
        _ = Pa.N^(2:ℕ) := by ring
    have ht8 : L^4*(((Real.sqrt Pa.N)*(Real.sqrt Pa.N))*(X:ℝ)) ≤ Pa.N^(2:ℕ) := by
      rw [hsqN]
      have h1 : Pa.N * ((X:ℝ) * L^4) ≤ Pa.N * L^(1*Work.FITop4.nuU+4) :=
        mul_le_mul_of_nonneg_left hXL4 (le_of_lt hNpos)
      have h2 : Pa.N * L^(1*Work.FITop4.nuU+4) ≤ Pa.N * Real.sqrt Pa.N :=
        mul_le_mul_of_nonneg_left hmon14h (le_of_lt hNpos)
      calc L^4*(Pa.N*(X:ℝ)) = Pa.N * ((X:ℝ) * L^4) := by ring
        _ ≤ Pa.N * L^(1*Work.FITop4.nuU+4) := h1
        _ ≤ Pa.N * Real.sqrt Pa.N := h2
        _ ≤ Pa.N^(2:ℕ) := by nlinarith [hN1, Real.sqrt_nonneg Pa.N, hsqN]
    have ht9 : L^4*(Real.sqrt Pa.N*(X:ℝ)) ≤ Pa.N^(2:ℕ) := by
      have h1 : Real.sqrt Pa.N * ((X:ℝ) * L^4) ≤ Real.sqrt Pa.N * L^(1*Work.FITop4.nuU+4) :=
        mul_le_mul_of_nonneg_left hXL4 (Real.sqrt_nonneg _)
      have h2 : Real.sqrt Pa.N * L^(1*Work.FITop4.nuU+4) ≤ Real.sqrt Pa.N * Real.sqrt Pa.N :=
        mul_le_mul_of_nonneg_left hmon14h (Real.sqrt_nonneg _)
      calc L^4*(Real.sqrt Pa.N*(X:ℝ)) = Real.sqrt Pa.N * ((X:ℝ) * L^4) := by ring
        _ ≤ Real.sqrt Pa.N * L^(1*Work.FITop4.nuU+4) := h1
        _ ≤ Real.sqrt Pa.N * Real.sqrt Pa.N := h2
        _ = Pa.N := hsqN
        _ ≤ Pa.N^(2:ℕ) := by nlinarith [hN1]
    have ht10 : L^4*(Pa.θ^(2:ℕ)*Pa.N^(2:ℕ)) ≤ Pa.N^(2:ℕ) := by
      have h1 : Pa.θ^(2:ℕ) * L^4 ≤ 1 := by
        have h2 : Pa.θ^(2:ℕ) ≤ Pa.θ := by nlinarith [hθ0, hθ1]
        nlinarith [h2, hθL4]
      have h3 : (0:ℝ) ≤ Pa.N^(2:ℕ) := by positivity
      calc L^4*(Pa.θ^(2:ℕ)*Pa.N^(2:ℕ)) = (Pa.θ^(2:ℕ) * L^4) * Pa.N^(2:ℕ) := by ring
        _ ≤ 1 * Pa.N^(2:ℕ) := mul_le_mul_of_nonneg_right h1 h3
        _ = Pa.N^(2:ℕ) := by ring
    have ht11 : L^4*(Pa.θ*(Pa.N*Real.sqrt Pa.N)) ≤ Pa.N^(2:ℕ) := by
      have h1 : Pa.θ * L^4 ≤ 1 := hθL4
      have h2 : (Pa.θ * L^4) * (Pa.N*Real.sqrt Pa.N) ≤ 1 * (Pa.N * Pa.N) := by
        have h4 : Real.sqrt Pa.N ≤ Pa.N := by
          have hs1 : (1:ℝ) ≤ Real.sqrt Pa.N := by
            rw [← Real.sqrt_one]
            exact Real.sqrt_le_sqrt hN1
          calc Real.sqrt Pa.N = Real.sqrt Pa.N * 1 := by ring
            _ ≤ Real.sqrt Pa.N * Real.sqrt Pa.N := mul_le_mul_of_nonneg_left hs1 (Real.sqrt_nonneg _)
            _ = Pa.N := hsqN
        refine mul_le_mul h1 ?_ (by positivity) (by norm_num)
        exact mul_le_mul_of_nonneg_left h4 (le_of_lt hNpos)
      calc L^4*(Pa.θ*(Pa.N*Real.sqrt Pa.N)) = (Pa.θ * L^4) * (Pa.N*Real.sqrt Pa.N) := by ring
        _ ≤ 1 * (Pa.N * Pa.N) := h2
        _ = Pa.N^(2:ℕ) := by ring
    have ht12 : L^4*(Pa.θ*Pa.N) ≤ Pa.N^(2:ℕ) := by
      calc L^4*(Pa.θ*Pa.N) = (Pa.θ * L^4) * Pa.N := by ring
        _ ≤ 1 * Pa.N := mul_le_mul_of_nonneg_right hθL4 (le_of_lt hNpos)
        _ = Pa.N := by ring
        _ ≤ Pa.N^(2:ℕ) := by nlinarith [hN1]
    have ht5' : L^4*(Pa.θ*((Real.sqrt Pa.N)*(Real.sqrt Pa.N))*(X:ℝ)^(2:ℕ)) ≤ Pa.N^(2:ℕ) := by
      rw [hsqN]
      exact ht5
    linarith [ht1, ht2, ht3, ht4, ht5', ht6, ht7, ht8, ht9, ht10, ht11, ht12]
  set S1 : ℝ := 16 * U * ((X:ℝ) * Cd * Sq) with hS1def
  set S2 : ℝ := 16 * U * (Cn * Sq * (1 + Real.log (2 + (X:ℝ))) * Wt) with hS2def
  set S3 : ℝ := 16 * U * (Cc * Pa.N^(2:ℕ) * (1 + Real.log (2 + Pa.N))^(14:ℕ) * (X:ℝ) / (Pa.Pz:ℝ))
    with hS3def
  set S4 : ℝ := Cf * Sq * Pa.N * (1 + Real.log (2 + Pa.N)) / (X:ℝ)^(2:ℕ) with hS4def
  have hsum' : ∑ d ∈ Finset.Icc 1 X, ((Nat.totient d : ℝ) / (d : ℝ)) *
        ‖Work.FIArea6.Vd Pa d β - Work.FIArea6.MainSum Pa X d β‖ ≤ S1 + S2 + S3 + S4 := hsum
  have hSge1 : (1:ℝ) ≤ Cd + Cn + Cc + Cf + 1 := by linarith [hCdpos]
  have hSpow : Cd + Cn + Cc + Cf + 1 ≤ (Cd + Cn + Cc + Cf + 1)^(4:ℕ) := by
    have h4 : (1:ℝ) ≤ (Cd + Cn + Cc + Cf + 1)^(3:ℕ) := one_le_pow₀ hSge1
    calc Cd + Cn + Cc + Cf + 1 = (Cd + Cn + Cc + Cf + 1) * 1 := by ring
      _ ≤ (Cd + Cn + Cc + Cf + 1) * (Cd + Cn + Cc + Cf + 1)^(3:ℕ) :=
          mul_le_mul_of_nonneg_left h4 (by linarith)
      _ = (Cd + Cn + Cc + Cf + 1)^(4:ℕ) := by ring
  have hCd_le_S : Cd ≤ Cd + Cn + Cc + Cf + 1 := by linarith [hCnpos, hCcpos, hCfpos]
  have hCn_le_S : Cn ≤ Cd + Cn + Cc + Cf + 1 := by linarith [hCdpos, hCcpos, hCfpos]
  have hCc_le_S : Cc ≤ Cd + Cn + Cc + Cf + 1 := by linarith [hCdpos, hCnpos, hCfpos]
  have hCf_le_S : Cf ≤ Cd + Cn + Cc + Cf + 1 := by linarith [hCdpos, hCnpos, hCcpos]
  have hconst :
      ∀ K : ℝ, 0 ≤ K → K ≤ (10:ℝ)^(12:ℕ) →
        K * (Cd + Cn + Cc + Cf + 1) ≤ (10:ℝ)^(12:ℕ) * (Cd + Cn + Cc + Cf + 1)^(4:ℕ) := by
    intro K hK0 hK
    have h0 : (0:ℝ) ≤ Cd + Cn + Cc + Cf + 1 := by linarith
    calc K * (Cd + Cn + Cc + Cf + 1) ≤ (10:ℝ)^(12:ℕ) * (Cd + Cn + Cc + Cf + 1) :=
          mul_le_mul_of_nonneg_right hK h0
      _ ≤ (10:ℝ)^(12:ℕ) * (Cd + Cn + Cc + Cf + 1)^(4:ℕ) :=
          mul_le_mul_of_nonneg_left hSpow (by norm_num)
  have hconstCd : 124416000 * Cd ≤ (10:ℝ)^(12:ℕ) * (Cd + Cn + Cc + Cf + 1)^(4:ℕ) :=
    le_trans (mul_le_mul_of_nonneg_left hCd_le_S (by norm_num)) (hconst 124416000 (by norm_num) (by norm_num))
  have hconstCn : 186624000 * Cn ≤ (10:ℝ)^(12:ℕ) * (Cd + Cn + Cc + Cf + 1)^(4:ℕ) :=
    le_trans (mul_le_mul_of_nonneg_left hCn_le_S (by norm_num)) (hconst 186624000 (by norm_num) (by norm_num))
  have hconstCc : 8192 * Cc ≤ (10:ℝ)^(12:ℕ) * (Cd + Cn + Cc + Cf + 1)^(4:ℕ) :=
    le_trans (mul_le_mul_of_nonneg_left hCc_le_S (by norm_num)) (hconst 8192 (by norm_num) (by norm_num))
  have hconstCf : 124416000 * Cf ≤ (10:ℝ)^(12:ℕ) * (Cd + Cn + Cc + Cf + 1)^(4:ℕ) :=
    le_trans (mul_le_mul_of_nonneg_left hCf_le_S (by norm_num)) (hconst 124416000 (by norm_num) (by norm_num))
  have hXr : (1:ℝ) ≤ (X:ℝ) := by exact_mod_cast hX
  have hPz1 : (1:ℝ) ≤ (Pa.Pz:ℝ) := le_trans (by norm_num) hPz2
  have hmain : 2 * (16 * U * ((X:ℝ) * Cd * Sq)
        + 16 * U * (Cn * Sq * (1 + Real.log (2 + (X:ℝ)))
            * ((X:ℝ)^(2:ℕ) + Pa.θ * Real.sqrt Pa.N * (X:ℝ) + Real.sqrt Pa.N + Pa.θ * Pa.N / (X:ℝ)))
        + 16 * U * (Cc * Pa.N^(2:ℕ) * (1 + Real.log (2 + Pa.N))^(14:ℕ) * (X:ℝ) / (Pa.Pz:ℝ))
        + Cf * Sq * Pa.N * (1 + Real.log (2 + Pa.N)) / (X:ℝ)^(2:ℕ))
      ≤ (10:ℝ)^(12:ℕ) * (Cd + Cn + Cc + Cf + 1)^(4:ℕ)
        * ((Pa.Pz:ℝ)⁻¹ + (X:ℝ)⁻¹) * Pa.N^(2:ℕ) * L := by
    refine s16_arith_endgame Cd Cn Cc Cf Pa.N L (X:ℝ) U Pa.θ (Pa.Pz:ℝ) Sq Work.FITop4.nuU
      hCdpos.le hCnpos.le hCcpos.le hCfpos.le hθ0 hSqnn hN1 hL1 hXr hU1 hUL hUdef hθL3 hSq_le
      hPz1 hPzpos hPzU hXLU hν0 hmon24h hmon14h hL3h hL3o hW12 hconstCd hconstCn hconstCc hconstCf
  have hsum2 := hsum'
  rw [hS1def, hS2def, hS3def, hS4def, hWdef] at hsum2
  have hfin : 2 * ∑ d ∈ Finset.Icc 1 X, ((Nat.totient d : ℝ) / (d : ℝ)) *
        ‖Work.FIArea6.Vd Pa d β - Work.FIArea6.MainSum Pa X d β‖
      ≤ (10:ℝ)^(12:ℕ) * (Cd + Cn + Cc + Cf + 1)^(4:ℕ)
        * ((Pa.Pz:ℝ)⁻¹ + (X:ℝ)⁻¹) * Pa.N^(2:ℕ) * L := by
    have h1 : 2 * ∑ d ∈ Finset.Icc 1 X, ((Nat.totient d : ℝ) / (d : ℝ)) *
          ‖Work.FIArea6.Vd Pa d β - Work.FIArea6.MainSum Pa X d β‖
        ≤ 2 * (16 * U * ((X:ℝ) * Cd * Sq)
        + 16 * U * (Cn * Sq * (1 + Real.log (2 + (X:ℝ)))
            * ((X:ℝ)^(2:ℕ) + Pa.θ * Real.sqrt Pa.N * (X:ℝ) + Real.sqrt Pa.N + Pa.θ * Pa.N / (X:ℝ)))
        + 16 * U * (Cc * Pa.N^(2:ℕ) * (1 + Real.log (2 + Pa.N))^(14:ℕ) * (X:ℝ) / (Pa.Pz:ℝ))
        + Cf * Sq * Pa.N * (1 + Real.log (2 + Pa.N)) / (X:ℝ)^(2:ℕ)) :=
      mul_le_mul_of_nonneg_left hsum2 (by norm_num)
    exact le_trans h1 hmain
  rw [hLdef] at hfin
  exact hfin

end

end Work.FIArea6.S16ErrTwo
