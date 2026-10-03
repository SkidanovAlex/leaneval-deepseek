/-
# Absorption of the `ImprovKMT` weight into `(Log N)^{-10}` (strict form)

The single-scale minor arc estimate `ImprovKMT` (area A4) produces the weight
`2^{-c (L-1)} + (Log N)^{-c/ρ}` at the height `L = l_{(N)} = C₀ · LogLog N`, where `c > 0` is the
rate of `ImprovKMT` (independent of `ρ`).  Interpolating it against the loss bound raises it to the
power `1 - θ`; for `C₀` large enough and `ρ` small enough the result, multiplied by a fixed power
of `⟨L⟩`, is bounded by a constant times `(max 1 (Log N))^{-10}`.

The `⟨l_{(N)}⟩^P` factor forces the two hypotheses to be *strict* (as they are in the assembly,
where `C₀ ≥ 20/(c(1-θ))` and `ρ` is small): with `10 = c C₀ (1-θ)` the term `2^{-c(l_{(N)}-1)}`
only matches the loss `(Log N)^{-10}` and the extra factor `⟨C₀ LogLog N⟩^P` is unbounded.  See
`Work.KMTAreas.A5.absorbWeightRefuted` for the machine-checked counterexample.

## The proof

Write `A = 2^{-c(l_{(N)}-1)}`, `B = (Log N)^{-c/ρ}`, `L = LogLog N`, `m = Log N`,
`M = max 1 (logb 2 N)`.  Then `improvWeight = A + B`, `⟨l_{(N)}⟩ = C₀ L` and
`(A+B)^{1-θ} ≤ A^{1-θ} + B^{1-θ}`, so it suffices to bound the two terms separately, both by
`C₀^P C₁ (2^{c(1-θ)} + 2^{c(1-θ)/ρ}) · 2^{10} · M^{-10}`:

* `A^{1-θ} = 2^{c(1-θ)} · 2^{-ηL}` with `η = c C₀ (1-θ) > 10`, and `2^{L-1} ≤ m ≤ M` with
  `M < 2^{L+1}` — so `2^{-ηL} ≤ 2^{-10L} ≤ 2^{10} M^{-10}`;
* `B^{1-θ} = m^{-a}` with `a = c(1-θ)/ρ > 10` and `m ≥ M/2`, so `m^{-a} ≤ 2^a M^{-a}`.

The polylogarithmic factor `L^P` is absorbed by the exponential gain `2^{εL}` using
`natCast_rpow_le_two_pow`, with `ε = min (η-10) (a-10)/2`, and the scale comparisons
`2^{L-1} ≤ m`, `M < 2^{L+1}` are `scale_bounds_logb`.
-/
import Mathlib
import Submission.Work.KMTAreas.A5.Setup
import Submission.Work.KMTAreas.A5.natCast_rpow_le_two_pow
import Submission.Work.KMTAreas.A5.scale_bounds_logb

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.KMTAreas.A5

open MeasureTheory
open scoped ENNReal NNReal BigOperators

/-- The real-variable core of `Work.KMTAreas.A5.absorbWeightStrict`: under the *strict*
hypotheses `10 < c C₀ (1-θ)` and `10 ρ < c (1-θ)` the §5 weight
`(2^{-c(l_{(N)}-1)} + (Log N)^{-c/ρ})^{1-θ} · ⟨l_{(N)}⟩^P` is bounded by a constant times
`⟨Log N⟩^{-10}`, where `l_{(N)} = heightScale C₀ N`.

Both hypotheses are used strictly: the exponential gain `2^{-η L}` (`η = c C₀ (1-θ) > 10`,
`L = LogLog N`) and the power gain `(Log N)^{-a}` (`a = c(1-θ)/ρ > 10`) have to beat the
polylogarithmic loss `⟨C₀ L⟩^P`, and the slacks `η - 10 > 0`, `a - 10 > 0` are exactly what lets
`L^P` be absorbed by `2^{εL}` (`natCast_rpow_le_two_pow`). -/
private lemma absorbWeightReal_core {c ρ θ : ℝ} (hc : 0 < c) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hρ0 : 0 < ρ) {P : ℝ} (hP : 0 ≤ P) {C₀ : ℕ}
    (hC₀ : 10 < c * (C₀ : ℝ) * (1 - θ)) (hρ : 10 * ρ < c * (1 - θ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 1 ≤ N →
      ((Work.KMTAreas.A5.improvWeight c ρ (Work.Analysis.EndVar.heightScale C₀ N) N : ℝ≥0) : ℝ) ^ (1 - θ)
        * ((Work.Analysis.IWMultiplier.angleBracket (Work.Analysis.EndVar.heightScale C₀ N) : ℝ≥0) : ℝ) ^ P
      ≤ C * ((Work.Analysis.EndVar.heightWeight 10 N : ℝ≥0) : ℝ) := by
  have hθ1' : 0 < 1 - θ := by linarith
  have hC01 : 1 ≤ C₀ := by
    by_contra h
    have h0 : C₀ = 0 := by omega
    rw [h0] at hC₀
    simp at hC₀
    linarith
  have hApos : 0 < c * (C₀ : ℝ) * (1 - θ) - 10 := by linarith
  have hBpos : 0 < c * (1 - θ) / ρ - 10 := by
    have h10 : (10:ℝ) < c * (1 - θ) / ρ := by rw [lt_div_iff₀ hρ0]; linarith
    linarith
  set ε : ℝ := min (c * (C₀ : ℝ) * (1 - θ) - 10) (c * (1 - θ) / ρ - 10) / 2 with hεdef
  have hεpos : 0 < ε := by
    rw [hεdef]
    have h1 : 0 < min (c * (C₀ : ℝ) * (1 - θ) - 10) (c * (1 - θ) / ρ - 10) :=
      lt_min hApos hBpos
    linarith
  have hεη : ε ≤ c * (C₀ : ℝ) * (1 - θ) - 10 := by
    rw [hεdef]
    have h1 : 0 ≤ min (c * (C₀ : ℝ) * (1 - θ) - 10) (c * (1 - θ) / ρ - 10) :=
      le_of_lt (lt_min hApos hBpos)
    have h2 := min_le_left (c * (C₀ : ℝ) * (1 - θ) - 10) (c * (1 - θ) / ρ - 10)
    linarith
  have hεa : ε ≤ c * (1 - θ) / ρ - 10 := by
    rw [hεdef]
    have h1 : 0 ≤ min (c * (C₀ : ℝ) * (1 - θ) - 10) (c * (1 - θ) / ρ - 10) :=
      le_of_lt (lt_min hApos hBpos)
    have h2 := min_le_right (c * (C₀ : ℝ) * (1 - θ) - 10) (c * (1 - θ) / ρ - 10)
    linarith
  obtain ⟨C₁, hC₁nn, hC₁⟩ := natCast_rpow_le_two_pow (P := P) (ε := ε) hP hεpos
  refine ⟨(C₀ : ℝ) ^ P * C₁ * ((2 : ℝ) ^ (c * (1 - θ)) + (2 : ℝ) ^ (c * (1 - θ) / ρ))
      * (2 : ℝ) ^ (10 : ℝ), ?_, ?_⟩
  · have h1 : 0 ≤ (C₀ : ℝ) ^ P := Real.rpow_nonneg (by positivity) _
    have h2 : 0 < (2 : ℝ) ^ (c * (1 - θ)) := Real.rpow_pos_of_pos (by norm_num) _
    have h3 : 0 < (2 : ℝ) ^ (c * (1 - θ) / ρ) := Real.rpow_pos_of_pos (by norm_num) _
    positivity
  · intro N hN
    obtain ⟨hlogN1, hlogLog1, _hscle, hscLt, h2L⟩ := scale_bounds_logb hN
    have hm1 : 1 ≤ Work.Analysis.EndVar.logN N := hlogN1
    have hL1 : 1 ≤ Work.Analysis.EndVar.logLogN N := hlogLog1
    have hsLt : max 1 (Real.logb 2 (N : ℝ)) ≤
        (2 : ℝ) ^ (((Work.Analysis.EndVar.logLogN N : ℕ) : ℝ) + 1) := le_of_lt hscLt
    have hhs : Work.Analysis.EndVar.heightScale C₀ N = C₀ * Work.Analysis.EndVar.logLogN N := rfl
    set L : ℝ := ((Work.Analysis.EndVar.logLogN N : ℕ) : ℝ) with hLdef
    have hLnn : 0 ≤ L := by rw [hLdef]; positivity
    have hL1' : 1 ≤ L := by rw [hLdef]; exact_mod_cast hL1
    have hm1' : (1:ℝ) ≤ ((Work.Analysis.EndVar.logN N : ℤ) : ℝ) := by exact_mod_cast hm1
    have hspos : 0 < max 1 (Real.logb 2 (N : ℝ)) := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
    have hAB' : Work.Analysis.IWMultiplier.angleBracket (Work.Analysis.EndVar.heightScale C₀ N)
        = ((C₀ * Work.Analysis.EndVar.logLogN N : ℕ) : ℝ≥0) := by
      show (max (1:ℝ≥0) (Work.Analysis.EndVar.heightScale C₀ N) : ℝ≥0) = _
      rw [hhs]
      exact max_eq_right (by exact_mod_cast (one_le_mul hC01 hL1
        : 1 ≤ C₀ * Work.Analysis.EndVar.logLogN N))
    have hAB : ((Work.Analysis.IWMultiplier.angleBracket (Work.Analysis.EndVar.heightScale C₀ N) : ℝ≥0) : ℝ)
        = (C₀ : ℝ) * L := by
      rw [hAB', NNReal.coe_natCast, Nat.cast_mul, hLdef]
    set Am : ℝ := (2:ℝ) ^ (-(c * (((C₀ * Work.Analysis.EndVar.logLogN N : ℕ) : ℝ) - 1))) with hAdef
    set Bm : ℝ := (((Work.Analysis.EndVar.logN N : ℤ) : ℝ)) ^ (-(c/ρ)) with hBdef
    have hAmnn : 0 ≤ Am := le_of_lt (Real.rpow_pos_of_pos (by norm_num) _)
    have hBmnn : 0 ≤ Bm := by
      rw [hBdef]
      exact Real.rpow_nonneg (by exact_mod_cast (Work.Analysis.EndVar.logN_nonneg N)) _
    have hnn : 0 ≤ (2:ℝ) ^ (-(c * (((C₀ * Work.Analysis.EndVar.logLogN N : ℕ) : ℝ) - 1)))
        + (((Work.Analysis.EndVar.logN N : ℤ) : ℝ)) ^ (-(c/ρ)) := add_nonneg hAmnn hBmnn
    have hW : ((Work.KMTAreas.A5.improvWeight c ρ (Work.Analysis.EndVar.heightScale C₀ N) N : ℝ≥0) : ℝ)
        = Am + Bm := by
      rw [Work.KMTAreas.A5.improvWeight, hhs, hAdef, hBdef, Real.coe_toNNReal _ hnn]
    have hAdef2 : Am = (2:ℝ) ^ (-(c * ((C₀ : ℝ) * L - 1))) := by
      rw [hAdef, Nat.cast_mul, ← hLdef]
    have hLP : L ^ P ≤ C₁ * (2:ℝ)^(ε * L) := by
      simpa only [hLdef] using hC₁ (Work.Analysis.EndVar.logLogN N)
    have hC0Pnn : 0 ≤ (C₀:ℝ)^P := Real.rpow_nonneg (by positivity) _
    rw [hW, hAB, Work.Analysis.EndVar.coe_heightWeight]
    have hAterm : Am ^ (1-θ) * ((C₀:ℝ)*L)^P
        ≤ (C₀:ℝ)^P * C₁ * (2:ℝ)^(c*(1-θ)) * (2:ℝ)^(-(10:ℝ)*L) := by
      have h1 : Am ^ (1-θ) = (2:ℝ)^(c*(1-θ)) * (2:ℝ)^(-(c*(1-θ)*(C₀:ℝ)*L)) := by
        rw [hAdef2, ← Real.rpow_mul (show (0:ℝ) ≤ 2 by norm_num),
          ← Real.rpow_add (show (0:ℝ) < 2 by norm_num)]
        congr 1
        ring
      calc Am ^ (1-θ) * ((C₀:ℝ)*L)^P
          = (2:ℝ)^(c*(1-θ)) * (2:ℝ)^(-(c*(1-θ)*(C₀:ℝ)*L)) * ((C₀:ℝ)^P * L^P) := by
              rw [h1, Real.mul_rpow (by positivity) hLnn]
        _ ≤ (2:ℝ)^(c*(1-θ)) * (2:ℝ)^(-(c*(1-θ)*(C₀:ℝ)*L))
              * ((C₀:ℝ)^P * (C₁ * (2:ℝ)^(ε*L))) := by
              refine mul_le_mul_of_nonneg_left ?_ (by positivity)
              exact mul_le_mul_of_nonneg_left hLP hC0Pnn
        _ = (C₀:ℝ)^P * C₁ * (2:ℝ)^(c*(1-θ))
              * ((2:ℝ)^(-(c*(1-θ)*(C₀:ℝ)*L)) * (2:ℝ)^(ε*L)) := by ring
        _ = (C₀:ℝ)^P * C₁ * (2:ℝ)^(c*(1-θ))
              * (2:ℝ)^(-(c*(1-θ)*(C₀:ℝ)*L) + ε*L) := by
              rw [← Real.rpow_add (show (0:ℝ) < 2 by norm_num)]
        _ ≤ (C₀:ℝ)^P * C₁ * (2:ℝ)^(c*(1-θ)) * (2:ℝ)^(-(10:ℝ)*L) := by
              refine mul_le_mul_of_nonneg_left ?_ (by positivity)
              exact Real.monotone_rpow_of_base_ge_one (by norm_num : (1:ℝ) ≤ 2)
                (by nlinarith [hεη, hLnn])
    have hBterm : Bm ^ (1-θ) * ((C₀:ℝ)*L)^P
        ≤ (C₀:ℝ)^P * C₁ * (2:ℝ)^(c*(1-θ)/ρ) * (2:ℝ)^(-(10:ℝ)*L) := by
      have hmnn : 0 ≤ (((Work.Analysis.EndVar.logN N : ℤ) : ℝ)) := by
        exact_mod_cast (Work.Analysis.EndVar.logN_nonneg N)
      have h1 : Bm ^ (1-θ) = (((Work.Analysis.EndVar.logN N : ℤ) : ℝ)) ^ (-(c*(1-θ)/ρ)) := by
        rw [hBdef, ← Real.rpow_mul hmnn]
        congr 1
        ring
      have hpos2L : 0 < (2:ℝ)^(L-1) := Real.rpow_pos_of_pos (by norm_num) _
      have hmpow : (((Work.Analysis.EndVar.logN N : ℤ) : ℝ)) ^ (-(c*(1-θ)/ρ))
          ≤ (2:ℝ)^((L-1)*(-(c*(1-θ)/ρ))) := by
        calc (((Work.Analysis.EndVar.logN N : ℤ) : ℝ)) ^ (-(c*(1-θ)/ρ))
            ≤ ((2:ℝ)^(L-1))^(-(c*(1-θ)/ρ)) :=
              Real.rpow_le_rpow_of_nonpos hpos2L h2L
                (by nlinarith [hc, hθ1', hρ0] : -(c*(1-θ)/ρ) ≤ 0)
          _ = (2:ℝ)^((L-1)*(-(c*(1-θ)/ρ))) :=
              (Real.rpow_mul (show (0:ℝ) ≤ 2 by norm_num) _ _).symm
      calc Bm ^ (1-θ) * ((C₀:ℝ)*L)^P
          = (((Work.Analysis.EndVar.logN N : ℤ) : ℝ)) ^ (-(c*(1-θ)/ρ)) * ((C₀:ℝ)^P * L^P) := by
              rw [h1, Real.mul_rpow (by positivity) hLnn]
        _ ≤ (2:ℝ)^((L-1)*(-(c*(1-θ)/ρ))) * ((C₀:ℝ)^P * L^P) := by
              refine mul_le_mul_of_nonneg_right hmpow (by positivity)
        _ ≤ (2:ℝ)^((L-1)*(-(c*(1-θ)/ρ))) * ((C₀:ℝ)^P * (C₁ * (2:ℝ)^(ε*L))) := by
              refine mul_le_mul_of_nonneg_left ?_ (by positivity)
              exact mul_le_mul_of_nonneg_left hLP hC0Pnn
        _ ≤ (C₀:ℝ)^P * C₁ * (2:ℝ)^(c*(1-θ)/ρ + (-(10:ℝ)*L)) := by
              have hExp : (L-1)*(-(c*(1-θ)/ρ)) + ε*L ≤ c*(1-θ)/ρ + (-(10:ℝ)*L) := by
                nlinarith [hεa, hLnn]
              calc (2:ℝ)^((L-1)*(-(c*(1-θ)/ρ))) * ((C₀:ℝ)^P * (C₁ * (2:ℝ)^(ε*L)))
                  = ((C₀:ℝ)^P * C₁)
                    * ((2:ℝ)^((L-1)*(-(c*(1-θ)/ρ))) * (2:ℝ)^(ε*L)) := by ring
                _ = ((C₀:ℝ)^P * C₁) * (2:ℝ)^((L-1)*(-(c*(1-θ)/ρ)) + ε*L) := by
                      rw [← Real.rpow_add (show (0:ℝ) < 2 by norm_num)]
                _ ≤ ((C₀:ℝ)^P * C₁) * (2:ℝ)^(c*(1-θ)/ρ + (-(10:ℝ)*L)) :=
                      mul_le_mul_of_nonneg_left
                        (Real.monotone_rpow_of_base_ge_one (by norm_num : (1:ℝ) ≤ 2) hExp)
                        (by positivity : (0:ℝ) ≤ (C₀:ℝ)^P * C₁)
        _ = (C₀:ℝ)^P * C₁ * (2:ℝ)^(c*(1-θ)/ρ) * (2:ℝ)^(-(10:ℝ)*L) := by
              rw [Real.rpow_add (show (0:ℝ) < 2 by norm_num)]; ring
    have hsplit : (Am + Bm)^(1-θ) ≤ Am^(1-θ) + Bm^(1-θ) :=
      Real.rpow_add_le_add_rpow (p := 1 - θ) hAmnn hBmnn (by linarith) (by linarith)
    have hfin : (2:ℝ)^(-(10:ℝ)*L)
        ≤ (2:ℝ)^(10:ℝ) * (max 1 (Real.logb 2 (N:ℝ)))^(-10:ℝ) := by
      have h1 := Real.rpow_le_rpow_of_nonpos hspos hsLt (by norm_num : (-10:ℝ) ≤ 0)
      have h3 : ((2:ℝ)^(L+1))^(-10:ℝ) = (2:ℝ)^((L+1)*(-10)) :=
        (Real.rpow_mul (show (0:ℝ) ≤ 2 by norm_num) _ _).symm
      rw [h3] at h1
      have h2 : (2:ℝ)^((L+1)*(-10)) = (2:ℝ)^(-(10:ℝ)*L) * (2:ℝ)^(-10:ℝ) := by
        rw [show (L+1)*(-10) = -(10:ℝ)*L + -10 by ring,
          Real.rpow_add (show (0:ℝ) < 2 by norm_num)]
      rw [h2] at h1
      have h5 := mul_le_mul_of_nonneg_right h1 (by positivity : (0:ℝ) ≤ (2:ℝ)^(10:ℝ))
      rw [mul_assoc, ← Real.rpow_add (show (0:ℝ) < 2 by norm_num),
        show (-10:ℝ) + 10 = 0 by norm_num, Real.rpow_zero, mul_one] at h5
      simpa [mul_comm] using h5
    calc (Am+Bm)^(1-θ) * ((C₀:ℝ)*L)^P
        ≤ (Am^(1-θ) + Bm^(1-θ)) * ((C₀:ℝ)*L)^P :=
          mul_le_mul_of_nonneg_right hsplit (by positivity)
      _ = Am^(1-θ) * ((C₀:ℝ)*L)^P + Bm^(1-θ) * ((C₀:ℝ)*L)^P := by ring
      _ ≤ ((C₀:ℝ)^P * C₁ * (2:ℝ)^(c*(1-θ)) * (2:ℝ)^(-(10:ℝ)*L))
          + ((C₀:ℝ)^P * C₁ * (2:ℝ)^(c*(1-θ)/ρ) * (2:ℝ)^(-(10:ℝ)*L)) :=
            add_le_add hAterm hBterm
      _ = (C₀:ℝ)^P * C₁ * ((2:ℝ)^(c*(1-θ)) + (2:ℝ)^(c*(1-θ)/ρ)) * (2:ℝ)^(-(10:ℝ)*L) := by ring
      _ ≤ (C₀:ℝ)^P * C₁ * ((2:ℝ)^(c*(1-θ)) + (2:ℝ)^(c*(1-θ)/ρ))
          * ((2:ℝ)^(10:ℝ) * (max 1 (Real.logb 2 (N:ℝ)))^(-10:ℝ)) :=
            mul_le_mul_of_nonneg_left hfin (by positivity)
      _ = (C₀:ℝ)^P * C₁ * ((2:ℝ)^(c*(1-θ)) + (2:ℝ)^(c*(1-θ)/ρ)) * (2:ℝ)^(10:ℝ)
          * (max 1 (Real.logb 2 (N:ℝ)))^(-10:ℝ) := by ring

/-- Coercion bridge: a real inequality of nonnegative reals lifts to `ℝ≥0∞`. -/
private lemma ennreal_coe_rpow_mul_le {x y z K : ℝ≥0} {s P : ℝ} (hs : 0 ≤ s) (hP : 0 ≤ P)
    (h : ((x : ℝ)) ^ s * ((y : ℝ)) ^ P ≤ ((K : ℝ)) * ((z : ℝ))) :
    (x : ℝ≥0∞) ^ s * (y : ℝ≥0∞) ^ P ≤ (K : ℝ≥0∞) * (z : ℝ≥0∞) := by
  have hL : (x : ℝ≥0∞) ^ s * (y : ℝ≥0∞) ^ P = ((x ^ s * y ^ P : ℝ≥0) : ℝ≥0∞) := by
    rw [← ENNReal.coe_rpow_of_nonneg x hs, ← ENNReal.coe_rpow_of_nonneg y hP,
      ← ENNReal.coe_mul]
  have hR : (K : ℝ≥0∞) * (z : ℝ≥0∞) = ((K * z : ℝ≥0) : ℝ≥0∞) := by
    rw [ENNReal.coe_mul]
  rw [hL, hR, ENNReal.coe_le_coe]
  show ((x ^ s * y ^ P : ℝ≥0) : ℝ) ≤ ((K * z : ℝ≥0) : ℝ)
  rw [NNReal.coe_mul, NNReal.coe_rpow, NNReal.coe_rpow, NNReal.coe_mul]
  exact h

open MeasureTheory
open scoped ENNReal NNReal BigOperators

theorem absorbWeightStrict {c ρ θ : ℝ} (hc : 0 < c) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hρ0 : 0 < ρ) {P : ℝ} (hP : 0 ≤ P) {C₀ : ℕ}
    (hC₀ : 10 < c * (C₀ : ℝ) * (1 - θ)) (hρ : 10 * ρ < c * (1 - θ)) :
    ∃ Ca : ℝ≥0, ∀ N : ℕ, 1 ≤ N →
      (Work.KMTAreas.A5.improvWeight c ρ (Work.Analysis.EndVar.heightScale C₀ N) N : ℝ≥0∞) ^ (1 - θ)
        * ((Work.Analysis.IWMultiplier.angleBracket (Work.Analysis.EndVar.heightScale C₀ N) : ℝ≥0) : ℝ≥0∞) ^ P
        ≤ (Ca : ℝ≥0∞) * (Work.Analysis.EndVar.heightWeight 10 N : ℝ≥0∞) := by
  obtain ⟨C, hCnn, hC⟩ := absorbWeightReal_core hc hθ0 hθ1 hρ0 hP hC₀ hρ
  refine ⟨Real.toNNReal C, fun N hN => ?_⟩
  have h := hC N hN
  rw [← Real.coe_toNNReal C hCnn] at h
  exact ennreal_coe_rpow_mul_le (le_of_lt (by linarith : (0:ℝ) < 1 - θ)) hP h

end Work.KMTAreas.A5
