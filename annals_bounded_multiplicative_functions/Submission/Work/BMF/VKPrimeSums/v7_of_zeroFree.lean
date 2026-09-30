import Mathlib
import Submission.Work.BMF.Defs
import Submission.Work.BMF.v7chi_defs
import Submission.Work.BMF.v7chi_arith
import Submission.Work.BMF.v7chi_lowHeight_box
import Submission.Work.BMF.mangoldt_sum_not_coprime_le
import Submission.Work.BMF.v7_log_omega_bound
import Submission.Work.BMF.perron_twist_core
import Submission.Work.BMF.chiPerronTw_bound
import Submission.Work.BMF.VKPrimeSums.logDeriv_LVK_of_zeroFree

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
This is the V7 node (`Submission/Work/BMF/chi_prime_sum_twist.lean`) with the sibling node V3
(`Work.BMF.LFunction_zeroFree_VK`) replaced by the *hypothesis* `hzerofree`, so that it can be used
before the file `LFunction_zeroFree_VK.lean` builds (it imports the broken statement file
`L_growth_VK.lean`).  The theorem is renamed `chi_prime_sum_twist_of_zeroFree`.
-/

/-! # V7. Non-principal characters: the twisted von Mangoldt sum

`‖Σ_{n ≤ x} Λ(n) χ(n) n^{-iu}‖ ≤ C x exp(−c (log x)^{1/12})` for `χ ≠ 1` modulo
`q ≤ (log x)^A` and `|u| ≤ exp((log x)^{21/20})`.

Route (the lead's design, "Addendum: vk_prime_sums detail" §3 and "Addendum: V0 exponent"):

* reduce to the primitive character `χ*` inducing `χ` (error `≤ ω(q) log x`);
* truncated Perron formula (`chiPerronTw_sub_sum_uniform`) at `x' := ⌊x⌋ + 1/2`;
* contour shift (`chiPerronTw_bound`) with height `T = exp((log x)^{1/2})` and half-width
  `δ = v7chidelta c₄ c₅ (1/(20A)) N u T`;
* the box `[1-δ, 1+1/log x'] × [u-T, u+T]` is zero-free with `‖L'/L‖ ≤ B`, using the large-height
  input `logDeriv_LFunction_VK` (`|t| ≥ 4`) and the low-height input `v7chi_lowHeight_box`
  (`|t| ≤ 4`, Siegel-type region `1 - c N^{-ε}`);
* the elementary error arithmetic is `v7chi_arith` and is done inline below.

The zero-free/log-derivative statements and the primitive-character reduction are the only
non-elementary inputs.
-/

namespace Work.BMF

open Finset ArithmeticFunction
open MeasureTheory intervalIntegral Filter
open scoped BigOperators Topology

noncomputable section

/-! ## The primitive-character reduction -/

/-- **Reduction to the primitive character.**  For a non-principal character `χ` modulo `q`, the
twisted von Mangoldt sum for `χ` differs from that of `χ.primitiveCharacter` by at most
`(2/log 2) log(q+2) log(x+2)`.

For `n` coprime to `q` the two characters agree; the only `n ≤ ⌊x⌋` with `Λ n ≠ 0` and
`¬ n.Coprime q` are prime powers `p^k` with `p ∣ q`, and
`Work.BMF.mangoldt_sum_not_coprime_le` bounds their total von Mangoldt weight by
`ω(q) log ⌊x⌋ ≤ ω(q) log x`. -/
theorem v7chi_primitive_reduction :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x : ℝ) (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 → 2 ≤ x →
      ∀ u : ℝ,
        ‖(∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ n * (n : ℂ) ^ (-(Complex.I * u)))
          - (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ.primitiveCharacter n * (n : ℂ) ^ (-(Complex.I * u)))‖
        ≤ C * Real.log ((q : ℝ) + 2) * Real.log (x + 2) := by
  refine ⟨2 / Real.log 2, by positivity, ?_⟩
  intro x q _inst χ hχ hx u
  have hx0 : (0 : ℝ) ≤ x := by linarith
  have hM1 : 1 ≤ ⌊x⌋₊ := by
    have : (2 : ℕ) ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx)
    omega
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [← Finset.sum_sub_distrib]
  have hpoint : ∀ n ∈ Finset.Icc 1 ⌊x⌋₊,
      ‖((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ n * (n : ℂ) ^ (-(Complex.I * u)) -
        ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ.primitiveCharacter n *
          (n : ℂ) ^ (-(Complex.I * u))‖
      ≤ (if n.Coprime q then 0 else (ArithmeticFunction.vonMangoldt n : ℝ)) := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    have hn0 : 0 < n := by omega
    have hpow : ‖(n : ℂ) ^ (-(Complex.I * u))‖ = 1 := by
      rw [Complex.norm_natCast_cpow_of_pos hn0]; simp
    have hfac : ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ n * (n : ℂ) ^ (-(Complex.I * u)) -
          ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ.primitiveCharacter n *
            (n : ℂ) ^ (-(Complex.I * u))
        = (((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * (χ n - χ.primitiveCharacter n)) *
            (n : ℂ) ^ (-(Complex.I * u)) := by ring
    rw [hfac, norm_mul, hpow, mul_one]
    by_cases hc : n.Coprime q
    · have hdiff : χ n = χ.primitiveCharacter n := by
        have h := χ.primitiveCharacter_apply_of_isCoprime (a := (n : ℤ))
          (Nat.isCoprime_iff_coprime.mpr hc)
        simpa using h.symm
      rw [hdiff, sub_self, mul_zero, norm_zero, if_pos hc]
    · rw [if_neg hc]
      have hχn : χ (n : ZMod q) = 0 := by
        refine MulChar.map_nonunit _ ?_
        intro hunit
        exact hc ((ZMod.isUnit_iff_coprime n q).mp hunit)
      rw [hχn, zero_sub]
      calc ‖((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * (-(χ.primitiveCharacter n))‖
          = (ArithmeticFunction.vonMangoldt n : ℝ) * ‖χ.primitiveCharacter n‖ := by
            rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
              abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
        _ ≤ (ArithmeticFunction.vonMangoldt n : ℝ) * 1 := by
            gcongr; exact χ.primitiveCharacter.norm_le_one _
        _ = (ArithmeticFunction.vonMangoldt n : ℝ) := mul_one _
  calc ‖∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
        (((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ n * (n : ℂ) ^ (-(Complex.I * u)) -
          ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ.primitiveCharacter n *
            (n : ℂ) ^ (-(Complex.I * u)))‖
      ≤ ∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
          (if n.Coprime q then 0 else (ArithmeticFunction.vonMangoldt n : ℝ)) :=
        norm_sum_le _ _
          |>.trans (Finset.sum_le_sum hpoint)
    _ = ∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun n => ¬ n.Coprime q),
          (ArithmeticFunction.vonMangoldt n : ℝ) := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl (fun n _ => ?_)
        by_cases hc : n.Coprime q <;> simp [hc]
    _ ≤ (q.primeFactors.card : ℝ) * Real.log (⌊x⌋₊ : ℝ) :=
        mangoldt_sum_not_coprime_le (q := q) ⌊x⌋₊
    _ ≤ (1 / Real.log 2) * Real.log ((q : ℝ) + 2) * Real.log (x + 2) := by
        have hM2 : (1 : ℝ) ≤ (⌊x⌋₊ : ℝ) := by exact_mod_cast hM1
        have hMx : (⌊x⌋₊ : ℝ) ≤ x + 2 := by
          have : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx0
          linarith
        have h := v7_log_omega_bound q ⌊x⌋₊ x hM1 hMx
        have heq : (2 / Real.log 2) * Real.log ((q : ℝ) + 2) * Real.log (x + 2)
            = 2 * ((1 / Real.log 2) * Real.log ((q : ℝ) + 2) * Real.log (x + 2)) := by ring
        rw [heq] at h
        linarith [h]
    _ ≤ 2 / Real.log 2 * Real.log ((q : ℝ) + 2) * Real.log (x + 2) := by
        have h2 : 0 < Real.log ((q : ℝ) + 2) := by
          apply Real.log_pos
          have : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
          linarith
        have h3 : 0 < Real.log (x + 2) := Real.log_pos (by linarith)
        have h4 : (0 : ℝ) < 1 / Real.log 2 := by positivity
        have h5 : (1 : ℝ) / Real.log 2 ≤ 2 / Real.log 2 := by
          rw [div_le_div_iff_of_pos_right hlog2pos]; linarith
        calc (1 / Real.log 2) * Real.log ((q : ℝ) + 2) * Real.log (x + 2)
            ≤ (2 / Real.log 2) * Real.log ((q : ℝ) + 2) * Real.log (x + 2) := by
              apply mul_le_mul_of_nonneg_right _ h3.le
              exact mul_le_mul_of_nonneg_right h5 h2.le
          _ = 2 / Real.log 2 * Real.log ((q : ℝ) + 2) * Real.log (x + 2) := rfl


/-! ## The main theorem -/

set_option maxHeartbeats 4000000 in
theorem chi_prime_sum_twist_of_zeroFree (A : ℝ) (hA : 0 < A)
    (hzerofree : ∃ c : ℝ, 0 < c ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N),
      χ.IsPrimitive → χ ≠ 1 → ∀ σ t : ℝ, 3 ≤ |t| →
        1 - c / (Real.log (|t| + 3) ^ (6 / 7 : ℝ) *
          (Real.log ((N : ℝ) + 2) + Real.log (Real.log (|t| + 3)))) ≤ σ →
        DirichletCharacter.LFunction χ ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0) :
    ∃ c C : ℝ, 0 < c ∧ ∀ (x : ℝ), 2 ≤ x → ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ Real.log x ^ A →
      ∀ (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ (u : ℝ),
        |u| ≤ Real.exp (Real.log x ^ (21 / 20 : ℝ)) →
        ‖∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ n *
            (n : ℂ) ^ (-(Complex.I * u))‖
          ≤ C * x * Real.exp (-c * Real.log x ^ (1 / 12 : ℝ)) := by
  -- the analytic inputs
  -- the Vinogradov–Korobov zero-free region (node V3) and the log-derivative bound on it (V4)
  obtain ⟨C₄, c₄, hC₄pos, hc₄pos, hV4⟩ :=
    VKPrimeSums.logDeriv_LVK_of_zeroFree hzerofree
  obtain ⟨c₅, C₅, hc₅pos, hC₅pos, hV5⟩ := v7chi_lowHeight_box (1 / (20 * A)) (by positivity)
  obtain ⟨C_red, hC_red, hRed⟩ := v7chi_primitive_reduction
  obtain ⟨C_p, hC_ppos, hTrunc⟩ := chiPerronTw_sub_sum_uniform
  have hC_p_nn : 0 ≤ C_p := le_of_lt hC_ppos
  -- the constant `c`
  set c : ℝ := 1 / 8 with hcdef
  have hcpos : 0 < c := by rw [hcdef]; norm_num
  -- the arithmetic core
  obtain ⟨X₀, hX₀⟩ := Filter.eventually_atTop.mp
    (v7chi_arith A c c₄ c₅ C₄ C₅ C_red C_p hA hcpos hc₄pos hc₅pos hC₄pos hC₅pos hC_red hC_p_nn)
  set X₁ : ℝ := max X₀ 6 with hX₁def
  set C_fin : ℝ := max 2 (Real.log X₁ * Real.exp (c * Real.log X₁ ^ (1 / 12 : ℝ)) + 1)
    with hCfindef
  refine ⟨c, C_fin, hcpos, ?_⟩
  intro x hx2 q _inst hq χ hχ u hu
  by_cases hxbig : X₁ ≤ x
  · -- ===== main case: `x ≥ X₁` =====
    have hX₀le : X₀ ≤ x := le_trans (le_max_left _ _) hxbig
    have hx6 : 6 ≤ x := le_trans (le_max_right _ _) hxbig
    have hx1 : (1 : ℝ) ≤ x := by linarith
    have hx0 : (0 : ℝ) < x := by linarith
    -- the primitive character inducing `χ`
    set N : ℕ := χ.conductor with hNdef
    have hNne : N ≠ 0 := by rw [hNdef]; exact χ.conductor_ne_zero
    haveI hNNe : NeZero N := ⟨hNne⟩
    have hNle : N ≤ q := by
      rw [hNdef]
      exact Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) χ.conductor_dvd_level
    have hNq : (N : ℝ) ≤ Real.log x ^ A := le_trans (Nat.cast_le.mpr hNle) hq
    have hcond1 : χ.conductor ≠ 1 := by
      intro h1
      exact hχ ((DirichletCharacter.eq_one_iff_conductor_eq_one).mpr h1)
    have hN2 : 2 ≤ N := by
      have h : N ≠ 1 := by rw [hNdef]; exact hcond1
      omega
    set χs : DirichletCharacter ℂ N := χ.primitiveCharacter with hχsdef
    have hχsprim : χs.IsPrimitive := χ.primitiveCharacter_isPrimitive
    have hχsne : χs ≠ 1 := by
      intro h1
      have hc1 : χs.conductor = 1 := (DirichletCharacter.eq_one_iff_conductor_eq_one).mp h1
      have hcN : χs.conductor = N := (DirichletCharacter.isPrimitive_def χs).mp hχsprim
      omega
    -- the contour data
    set x' : ℝ := (⌊x⌋₊ : ℝ) + 1 / 2 with hx'def
    set δ : ℝ := v7chidelta c₄ c₅ (1 / (20 * A)) N u (v7chiT x) with hδdef
    set σ₁ : ℝ := 1 - δ with hσ₁def
    set B : ℝ := v7chiB C₄ C₅ (1 / (20 * A)) N u (v7chiT x) with hBdef
    have hTpos : 0 < v7chiT x := v7chiT_pos x
    have hδD : δ ≤ c₄ / (2 * v7chiD N u (v7chiT x)) := by
      rw [hδdef]
      exact v7chidelta_le_D c₄ c₅ (1 / (20 * A)) N u (v7chiT x)
    have hδsieg : δ ≤ c₅ * (N : ℝ) ^ (-(1 / (20 * A))) / 2 := by
      rw [hδdef]
      exact v7chidelta_le_sieg c₄ c₅ (1 / (20 * A)) N u (v7chiT x)
    -- the arithmetic bullets
    have harith := hX₀ x hX₀le N hN2 hNq u hu
    obtain ⟨hT2, hδposR, hδ4R, hx2R, h1000, hconj5, hconj6, hconj7, hconj8, hconj9, hconj10,
      hconj11, hconj12⟩ := harith
    rw [← hδdef] at hδposR hδ4R hconj5
    rw [← hBdef] at hconj6 hconj7
    rw [← hδdef] at hconj6
    rw [← hσ₁def] at hconj6
    rw [← hx'def] at hconj11 hconj12
    have hδpos : 0 < δ := hδposR
    have hδ4 : δ ≤ 1 / 4 := hδ4R
    have hσ₁pos : 0 < σ₁ := by rw [hσ₁def]; linarith
    have hσ₁ge : 3 / 4 ≤ σ₁ := by rw [hσ₁def]; linarith
    have hx'log1 : 1 ≤ Real.log x' := by rw [hx'def]; exact v7chiX_log_ge_one hx6
    have hx'le : x' ≤ 2 * x := hconj11
    have hx'log : Real.log x' ≤ Real.log x + 1 := hconj12
    have hx'3 : 3 ≤ x' := by
      have h3 : (6 : ℕ) ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx6)
      have : (6 : ℝ) ≤ (⌊x⌋₊ : ℝ) := by exact_mod_cast h3
      rw [hx'def]; linarith
    have hx'1 : 1 < x' := by linarith
    have hx'pos : 0 < x' := by linarith
    have hx'notnat : ∀ n : ℕ, (n : ℝ) ≠ x' := by
      intro n
      rw [hx'def]
      exact v7chiX_not_natCast x n
    have hx'2 : x ≤ 2 * x' := by
      rw [hx'def]
      exact v7chiX_ge hx1
    have hσ₁lt : σ₁ < 1 + 1 / Real.log x' := by
      have h1 : 0 < 1 / Real.log x' := one_div_pos.mpr (by linarith)
      rw [hσ₁def]; linarith
    -- the box is zero-free
    have hbox : ∀ s : ℂ, s.re ∈ Set.Icc σ₁ (1 + 1 / Real.log x') → |s.im - u| ≤ v7chiT x →
        DirichletCharacter.LFunction χs s ≠ 0 := by
      intro s hs hs2
      have hU : |s.im| + 3 ≤ v7chiU u (v7chiT x) := by
        have h2 : |s.im| ≤ |s.im - u| + |u| := by
          calc |s.im| = |(s.im - u) + u| := by congr 1; ring
            _ ≤ |s.im - u| + |u| := abs_add_le _ _
        have h1 : |s.im| ≤ v7chiT x + |u| := by linarith [hs2, h2]
        simp only [v7chiU]; linarith
      have hσ2 : s.re ≤ 2 := by
        have h1 : 1 / Real.log x' ≤ 1 := by
          rw [div_le_one (by linarith [hx'log1])]; exact hx'log1
        linarith [hs.2]
      have hδle : δ ≤ c₄ / (Real.log (|s.im| + 3) ^ (6 / 7 : ℝ) *
          (Real.log ((N : ℝ) + 2) + Real.log (Real.log (|s.im| + 3)))) := by
        have h1 := v7chi_denom_le hc₄pos.le N hN2 (le_of_lt hTpos) (y := |s.im| + 3)
          (by linarith [abs_nonneg s.im]) hU
        linarith [hδD, h1]
      by_cases h4 : 4 ≤ |s.im|
      · have hσ : 1 - c₄ / (Real.log (|s.im| + 3) ^ (6 / 7 : ℝ) *
            (Real.log ((N : ℝ) + 2) + Real.log (Real.log (|s.im| + 3)))) ≤ s.re := by
          rw [hσ₁def] at hs; linarith [hs.1, hδle]
        have hz := (hV4 N χs hχsprim hχsne s.re s.im h4 hσ hσ2).1
        rwa [Complex.re_add_im] at hz
      · push_neg at h4
        have hδle2 : δ ≤ c₅ * (N : ℝ) ^ (-(1 / (20 * A))) := by
          have h5 : 0 ≤ (N : ℝ) ^ (-(1 / (20 * A))) := Real.rpow_nonneg (Nat.cast_nonneg _) _
          linarith [hδsieg]
        have hσ : 1 - c₅ * (N : ℝ) ^ (-(1 / (20 * A))) ≤ s.re := by
          rw [hσ₁def] at hs; linarith [hs.1, hδle2]
        have hz := (hV5 N χs hχsprim hχsne s.re s.im (le_of_lt h4) hσ hσ2).1
        rwa [Complex.re_add_im] at hz
    -- the log-derivative bound
    have hBbox : ∀ σ t : ℝ, σ ∈ Set.Icc σ₁ (1 + 1 / Real.log x') → |t - u| ≤ v7chiT x →
        ‖logDeriv (DirichletCharacter.LFunction χs) ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ B := by
      intro σ t hs hs2
      have hU : |t| + 3 ≤ v7chiU u (v7chiT x) := by
        have h2 : |t| ≤ |t - u| + |u| := by
          calc |t| = |(t - u) + u| := by congr 1; ring
            _ ≤ |t - u| + |u| := abs_add_le _ _
        have h1 : |t| ≤ v7chiT x + |u| := by linarith [hs2, h2]
        simp only [v7chiU]; linarith
      have hσ2 : σ ≤ 2 := by
        have h1 : 1 / Real.log x' ≤ 1 := by
          rw [div_le_one (by linarith [hx'log1])]; exact hx'log1
        linarith [hs.2]
      have hδle : δ ≤ c₄ / (Real.log (|t| + 3) ^ (6 / 7 : ℝ) *
          (Real.log ((N : ℝ) + 2) + Real.log (Real.log (|t| + 3)))) := by
        have h1 := v7chi_denom_le hc₄pos.le N hN2 (le_of_lt hTpos) (y := |t| + 3)
          (by linarith [abs_nonneg t]) hU
        linarith [hδD, h1]
      by_cases h4 : 4 ≤ |t|
      · have hσ : 1 - c₄ / (Real.log (|t| + 3) ^ (6 / 7 : ℝ) *
            (Real.log ((N : ℝ) + 2) + Real.log (Real.log (|t| + 3)))) ≤ σ := by
          rw [hσ₁def] at hs; linarith [hs.1, hδle]
        have hb := (hV4 N χs hχsprim hχsne σ t h4 hσ hσ2).2
        refine le_trans hb ?_
        rw [hBdef, v7chiB]
        have htpos : (0 : ℝ) < |t| + 3 := by positivity
        have hNnn : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg _
        have hlt : Real.log ((N : ℝ) * (|t| + 3)) ≤ Real.log ((N : ℝ) * v7chiU u (v7chiT x)) := by
          apply Real.log_le_log (by positivity)
          exact mul_le_mul_of_nonneg_left hU hNnn
        have hlog0 : 0 ≤ Real.log ((N : ℝ) * (|t| + 3)) := by
          apply Real.log_nonneg
          have hN2' : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN2
          nlinarith [abs_nonneg t, hN2']
        have h5 : Real.log ((N : ℝ) * (|t| + 3)) ^ 4 ≤
            Real.log ((N : ℝ) * v7chiU u (v7chiT x)) ^ 4 :=
          pow_le_pow_left₀ hlog0 hlt 4
        have h6 : 0 ≤ C₅ * ((N : ℝ) ^ (1 / (20 * A)) +
            Real.log ((N : ℝ) + 2) ^ 2) := by
          have h7 : 0 ≤ (N : ℝ) ^ (1 / (20 * A)) := Real.rpow_nonneg hNnn _
          have h8 : 0 ≤ Real.log ((N : ℝ) + 2) ^ 2 := sq_nonneg _
          nlinarith [hC₅pos]
        nlinarith [hC₄pos]
      · push_neg at h4
        have hδle2 : δ ≤ c₅ * (N : ℝ) ^ (-(1 / (20 * A))) := by
          have h5 : 0 ≤ (N : ℝ) ^ (-(1 / (20 * A))) := Real.rpow_nonneg (Nat.cast_nonneg _) _
          linarith [hδsieg]
        have hσ : 1 - c₅ * (N : ℝ) ^ (-(1 / (20 * A))) ≤ σ := by
          rw [hσ₁def] at hs; linarith [hs.1, hδle2]
        have hb := (hV5 N χs hχsprim hχsne σ t (le_of_lt h4) hσ hσ2).2
        refine le_trans hb ?_
        rw [hBdef, v7chiB]
        have h7 : 0 ≤ C₄ * Real.log ((N : ℝ) * v7chiU u (v7chiT x)) ^ 4 := by
          have h8 : 0 ≤ Real.log ((N : ℝ) * v7chiU u (v7chiT x)) ^ 4 := by positivity
          nlinarith [hC₄pos]
        linarith
    -- the Perron bound
    have hperr := chiPerronTw_bound χs hχsne (u := u) (x := x') (T := v7chiT x) (σ₁ := σ₁)
      (B := B) hx'1 hTpos hσ₁pos hσ₁lt hbox hBbox
    -- the truncation error
    have htrunc := hTrunc χs hχsne u x' (v7chiT x) hx'3 hx'notnat hT2
    -- the sum identification
    have hsumid : (∑ n ∈ Finset.Icc 1 ⌊x'⌋₊, chiLambdaTwist χs u n)
        = ∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
            ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χs n * (n : ℂ) ^ (-(Complex.I * u)) := by
      have hfloor : ⌊x'⌋₊ = ⌊x⌋₊ := by rw [hx'def]; exact v7chiX_floor x
      rw [hfloor]
      refine Finset.sum_congr rfl fun n _ => ?_
      simp only [chiLambdaTwist]
      ring
    -- the four error estimates
    have hLpos : 0 < Real.log x := by linarith
    have hTexp : v7chiT x * Real.exp (-c * Real.log x ^ (1 / 12 : ℝ)) =
        Real.exp (Real.log x ^ (1 / 2 : ℝ) - c * Real.log x ^ (1 / 12 : ℝ)) := by
      rw [v7chiT, ← Real.exp_add]
      congr 1
      ring
    have hexpL : Real.exp (Real.log x - c * Real.log x ^ (1 / 12 : ℝ)) =
        x * Real.exp (-c * Real.log x ^ (1 / 12 : ℝ)) := by
      calc Real.exp (Real.log x - c * Real.log x ^ (1 / 12 : ℝ))
          = Real.exp (Real.log x) * Real.exp (-c * Real.log x ^ (1 / 12 : ℝ)) := by
            rw [← Real.exp_add]
            congr 1
            ring
        _ = x * Real.exp (-c * Real.log x ^ (1 / 12 : ℝ)) := by
            rw [Real.exp_log hx0]
    have hx0' : (0 : ℝ) ≤ x := by linarith
    have hXnn : 0 ≤ x * Real.exp (-c * Real.log x ^ (1 / 12 : ℝ)) := by positivity
    have hBnn : 0 ≤ B := by
      rw [hBdef, v7chiB]
      have h5 : 0 ≤ C₄ * Real.log ((N : ℝ) * v7chiU u (v7chiT x)) ^ 4 := by
        have h6 : 0 ≤ Real.log ((N : ℝ) * v7chiU u (v7chiT x)) ^ 4 := by positivity
        nlinarith [hC₄pos]
      have h6 : 0 ≤ C₅ * ((N : ℝ) ^ (1 / (20 * A)) + Real.log ((N : ℝ) + 2) ^ 2) := by
        have h7 : 0 ≤ (N : ℝ) ^ (1 / (20 * A)) := Real.rpow_nonneg (Nat.cast_nonneg N) _
        have h8 : 0 ≤ Real.log ((N : ℝ) + 2) ^ 2 := sq_nonneg _
        nlinarith [hC₅pos]
      linarith
    -- first Perron term
    have hterm1 : B * x' ^ (1 + 1 / Real.log x') / v7chiT x * (1 + 1 / Real.log x' - σ₁) ≤
        (1 / 4) * (x * Real.exp (-c * Real.log x ^ (1 / 12 : ℝ))) := by
      have hrpow : x' ^ (1 + 1 / Real.log x') = Real.exp 1 * x' := by
        have hne : Real.log x' ≠ 0 := by linarith [hx'log1]
        rw [Real.rpow_add hx'pos 1 (1 / Real.log x'), Real.rpow_one]
        have h2 : x' ^ (1 / Real.log x') = Real.exp 1 := by
          rw [Real.rpow_def_of_pos hx'pos, mul_one_div, div_self hne]
        rw [h2, mul_comm]
      have hfac : (1 + 1 / Real.log x' - σ₁) ≤ 5 / 4 := by
        have h3 : 1 / Real.log x' ≤ 1 := by
          rw [div_le_one (by linarith [hx'log1])]; exact hx'log1
        linarith [hσ₁ge]
      have hfac0 : (0 : ℝ) ≤ 1 + 1 / Real.log x' - σ₁ := by
        have h3 : 1 / Real.log x' ≤ 1 := by
          rw [div_le_one (by linarith [hx'log1])]; exact hx'log1
        linarith [hσ₁pos]
      have hbound : B * Real.exp 1 / v7chiT x
          ≤ (1 / 16) * Real.exp (-c * Real.log x ^ (1 / 12 : ℝ)) := by
        rw [← hTexp] at hconj7
        rw [div_le_iff₀ hTpos]
        linarith [hconj7]
      have hA1 : B * (Real.exp 1 * x') / v7chiT x ≤ B * (Real.exp 1 * (2 * x)) / v7chiT x := by
        have h2 : Real.exp 1 * x' ≤ Real.exp 1 * (2 * x) :=
          mul_le_mul_of_nonneg_left hx'le (Real.exp_pos 1).le
        exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h2 hBnn) hTpos.le
      have hA2 : (0 : ℝ) ≤ B * (Real.exp 1 * (2 * x)) / v7chiT x := by positivity
      have hstep : B * x' ^ (1 + 1 / Real.log x') / v7chiT x * (1 + 1 / Real.log x' - σ₁)
          ≤ B * (Real.exp 1 * (2 * x)) / v7chiT x * (5 / 4) := by
        rw [hrpow]
        exact mul_le_mul hA1 hfac hfac0 hA2
      have hstep2 : B * (Real.exp 1 * (2 * x)) / v7chiT x * (5 / 4)
          ≤ (5 / 32) * (x * Real.exp (-c * Real.log x ^ (1 / 12 : ℝ))) := by
        have h6 : B * (Real.exp 1 * (2 * x)) / v7chiT x * (5 / 4)
            = (5 / 2) * (B * Real.exp 1 / v7chiT x) * x := by ring
        rw [h6]
        calc (5 / 2) * (B * Real.exp 1 / v7chiT x) * x
            ≤ (5 / 2) * ((1 / 16) * Real.exp (-c * Real.log x ^ (1 / 12 : ℝ))) * x := by
              have h7 : (0 : ℝ) ≤ 5 / 2 := by norm_num
              exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hbound h7) hx0'
          _ = (5 / 32) * (x * Real.exp (-c * Real.log x ^ (1 / 12 : ℝ))) := by ring
      linarith [hstep, hstep2]
    -- second Perron term
    have hterm2 : B * x' ^ σ₁ * (3 + 3 * Real.log (2 + v7chiT x / σ₁)) ≤
        (1 / 4) * (x * Real.exp (-c * Real.log x ^ (1 / 12 : ℝ))) := by
      have hpow : x' ^ σ₁ ≤ 4 * x * Real.exp (-(δ * Real.log x)) := by
        have hδ1 : δ ≤ 1 := by linarith [hδ4]
        have hlogx' : Real.log x' ≥ Real.log x - Real.log 2 := by
          have h4 : Real.log x ≤ Real.log (2 * x') := Real.log_le_log (by positivity) hx'2
          rw [Real.log_mul (by norm_num) (by linarith)] at h4
          linarith
        have h2 : x' ^ (-(δ)) ≤ 2 * Real.exp (-(δ * Real.log x)) := by
          have h3 : Real.exp (-(δ * Real.log x')) ≤ 2 * Real.exp (-(δ * Real.log x)) := by
            have h4 : Real.exp (-(δ * Real.log x')) ≤
                Real.exp (-(δ * Real.log x) + δ * Real.log 2) := by
              apply Real.exp_le_exp.mpr
              nlinarith [hlogx', hδpos]
            have h5 : Real.exp (-(δ * Real.log x) + δ * Real.log 2)
                = Real.exp (-(δ * Real.log x)) * 2 ^ δ := by
              rw [Real.exp_add, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
              congr 1
              ring
            rw [h5] at h4
            have h6 : (2 : ℝ) ^ δ ≤ 2 := by
              calc (2 : ℝ) ^ δ ≤ (2 : ℝ) ^ (1 : ℝ) :=
                    Real.rpow_le_rpow_of_exponent_le (by norm_num) hδ1
                _ = 2 := Real.rpow_one 2
            have h7 : (0 : ℝ) < Real.exp (-(δ * Real.log x)) := Real.exp_pos _
            nlinarith [h4, h6, h7]
          calc x' ^ (-(δ)) = Real.exp (-(δ * Real.log x')) := by
                rw [Real.rpow_def_of_pos hx'pos]
                congr 1; ring
            _ ≤ 2 * Real.exp (-(δ * Real.log x)) := h3
        have h7 : x' ^ σ₁ = x' ^ (1 : ℝ) * x' ^ (-(δ)) := by
          rw [hσ₁def, show (1 : ℝ) - δ = 1 + (-(δ)) by ring, Real.rpow_add hx'pos 1 (-(δ))]
        rw [h7, Real.rpow_one]
        have h8 : x' * x' ^ (-(δ)) ≤ (2 * x) * (2 * Real.exp (-(δ * Real.log x))) :=
          mul_le_mul hx'le h2 (Real.rpow_nonneg hx'pos.le _) (by positivity)
        linarith [h8]
      have h11 : B * x' ^ σ₁ * (3 + 3 * Real.log (2 + v7chiT x / σ₁))
          ≤ (1 / 16) * (Real.log x + 2) ^ 20 * (4 * x * Real.exp (-(δ * Real.log x))) := by
        have h12 : B * (3 + 3 * Real.log (2 + v7chiT x / σ₁)) * x' ^ σ₁
            ≤ (1 / 16) * (Real.log x + 2) ^ 20 * (4 * x * Real.exp (-(δ * Real.log x))) :=
          mul_le_mul hconj6 hpow (Real.rpow_nonneg hx'pos.le _) (by positivity)
        calc B * x' ^ σ₁ * (3 + 3 * Real.log (2 + v7chiT x / σ₁))
            = B * (3 + 3 * Real.log (2 + v7chiT x / σ₁)) * x' ^ σ₁ := by ring
          _ ≤ _ := h12
      have h15 : (Real.log x + 2) ^ 20 * Real.exp (-(δ * Real.log x)) ≤
          Real.exp (-c * Real.log x ^ (1 / 12 : ℝ)) := by
        have h14 : (0 : ℝ) < (Real.log x + 2) ^ 20 := by positivity
        have h17 : (Real.log x + 2) ^ 20 * Real.exp (-(δ * Real.log x)) ≤
            Real.exp (-(c * Real.log x ^ (1 / 12 : ℝ))) := by
          calc (Real.log x + 2) ^ 20 * Real.exp (-(δ * Real.log x))
              ≤ (Real.log x + 2) ^ 20 *
                  (Real.exp (-(c * Real.log x ^ (1 / 12 : ℝ))) / (Real.log x + 2) ^ 20) :=
                mul_le_mul_of_nonneg_left hconj5 h14.le
            _ = Real.exp (-(c * Real.log x ^ (1 / 12 : ℝ))) := by field_simp
        simpa only [neg_mul] using h17
      have h16 : (1 / 16) * (Real.log x + 2) ^ 20 * (4 * x * Real.exp (-(δ * Real.log x)))
          ≤ (1 / 4) * (x * Real.exp (-c * Real.log x ^ (1 / 12 : ℝ))) := by
        rw [show (1 / 16) * (Real.log x + 2) ^ 20 * (4 * x * Real.exp (-(δ * Real.log x)))
            = (1 / 4) * (x * ((Real.log x + 2) ^ 20 * Real.exp (-(δ * Real.log x)))) by ring]
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h15 hx0') (by norm_num)
      linarith [h11, h16]
    -- the truncation error
    have htrunc_le : C_p * (x' * (Real.log x') ^ 2 / v7chiT x + Real.log x') ≤
        (1 / 4) * (x * Real.exp (-c * Real.log x ^ (1 / 12 : ℝ))) := by
      have ha : C_p * (x' * (Real.log x') ^ 2 / v7chiT x)
          ≤ (1 / 8) * (x * Real.exp (-c * Real.log x ^ (1 / 12 : ℝ))) := by
        have h2 : 16 * C_p * (Real.log x + 1) ^ 2 ≤
            v7chiT x * Real.exp (-c * Real.log x ^ (1 / 12 : ℝ)) := by
          rw [hTexp]
          exact hconj8
        have h3 : x' * (Real.log x') ^ 2 / v7chiT x
            ≤ 2 * x * (Real.log x + 1) ^ 2 / v7chiT x := by
          have hlogx'0 : 0 ≤ Real.log x' := by linarith [hx'log1]
          have h4 : (Real.log x') ^ 2 ≤ (Real.log x + 1) ^ 2 :=
            pow_le_pow_left₀ hlogx'0 hx'log 2
          have h5 : 0 ≤ (Real.log x') ^ 2 := sq_nonneg _
          have h6 : 0 < v7chiT x := hTpos
          gcongr
        have h4 : C_p * (x' * (Real.log x') ^ 2 / v7chiT x)
            ≤ C_p * (2 * x * (Real.log x + 1) ^ 2 / v7chiT x) :=
          mul_le_mul_of_nonneg_left h3 hC_p_nn
        have h5 : C_p * (2 * x * (Real.log x + 1) ^ 2 / v7chiT x)
            ≤ (1 / 8) * (x * Real.exp (-c * Real.log x ^ (1 / 12 : ℝ))) := by
          have h7 : C_p * (Real.log x + 1) ^ 2 / v7chiT x
              ≤ (1 / 16) * Real.exp (-c * Real.log x ^ (1 / 12 : ℝ)) := by
            rw [div_le_iff₀ hTpos]
            linarith [h2]
          calc C_p * (2 * x * (Real.log x + 1) ^ 2 / v7chiT x)
              = (2 * x) * (C_p * (Real.log x + 1) ^ 2 / v7chiT x) := by ring
            _ ≤ (2 * x) * ((1 / 16) * Real.exp (-c * Real.log x ^ (1 / 12 : ℝ))) :=
                mul_le_mul_of_nonneg_left h7 (by positivity)
            _ = (1 / 8) * (x * Real.exp (-c * Real.log x ^ (1 / 12 : ℝ))) := by ring
        linarith [h4, h5]
      have hb : C_p * Real.log x' ≤ (1 / 8) * (x * Real.exp (-c * Real.log x ^ (1 / 12 : ℝ))) := by
        have h2 : 8 * C_p * (Real.log x + 1) ≤
            x * Real.exp (-c * Real.log x ^ (1 / 12 : ℝ)) := by
          have h3 := hconj9
          rw [hexpL] at h3
          exact h3
        have h4 : C_p * Real.log x' ≤ C_p * (Real.log x + 1) :=
          mul_le_mul_of_nonneg_left hx'log hC_p_nn
        linarith [h4, h2]
      linarith [ha, hb]
    -- the reduction error
    have hred_le : C_red * Real.log ((q : ℝ) + 2) * Real.log (x + 2) ≤
        (1 / 2) * (x * Real.exp (-c * Real.log x ^ (1 / 12 : ℝ))) := by
      have h1 : Real.log ((q : ℝ) + 2) ≤ 2 * (A * Real.log (Real.log x + 2) + Real.log 2) := by
        by_cases hcase : Real.log x ^ A ≤ 2
        · have h2 : (q : ℝ) + 2 ≤ 4 := by linarith
          have h3 : Real.log ((q : ℝ) + 2) ≤ Real.log 4 := Real.log_le_log (by linarith) h2
          have h4 : Real.log 4 = 2 * Real.log 2 := by
            rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
            push_cast
            ring
          rw [h4] at h3
          have h5 : 0 ≤ A * Real.log (Real.log x + 2) :=
            mul_nonneg hA.le (Real.log_nonneg (by linarith))
          linarith
        · push_neg at hcase
          have h2 : (q : ℝ) + 2 ≤ 2 * Real.log x ^ A := by linarith
          have h3 : Real.log ((q : ℝ) + 2) ≤ Real.log (2 * Real.log x ^ A) :=
            Real.log_le_log (by linarith) h2
          rw [Real.log_mul (by norm_num) (by positivity), Real.log_rpow hLpos] at h3
          have h5 : A * Real.log (Real.log x) ≤ A * Real.log (Real.log x + 2) :=
            mul_le_mul_of_nonneg_left (Real.log_le_log hLpos (by linarith)) hA.le
          have h6 : Real.log 2 ≤ A * Real.log (Real.log x + 2) := by
            have h7 : Real.log 2 ≤ Real.log (Real.log x ^ A) := by
              apply Real.log_le_log (by norm_num)
              linarith
            rw [Real.log_rpow hLpos] at h7
            exact le_trans h7 h5
          have h8 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
          linarith [h3, h5, h6, h8]
      have h2 : Real.log (x + 2) ≤ Real.log x + 2 := by
        have h3 : Real.log (x + 2) ≤ Real.log (2 * x) :=
          Real.log_le_log (by linarith) (by linarith)
        rw [Real.log_mul (by norm_num) (ne_of_gt hx0)] at h3
        linarith [Real.log_two_lt_d9]
      have h4 : 4 * C_red * (A * Real.log (Real.log x + 2) + Real.log 2) * (Real.log x + 2) ≤
          x * Real.exp (-c * Real.log x ^ (1 / 12 : ℝ)) := by
        have h5 := hconj10
        rw [hexpL] at h5
        exact h5
      have h6 : 0 ≤ Real.log (x + 2) := Real.log_nonneg (by linarith)
      have h8 : C_red * Real.log ((q : ℝ) + 2) * Real.log (x + 2)
          ≤ C_red * (2 * (A * Real.log (Real.log x + 2) + Real.log 2)) * (Real.log x + 2) := by
        have h9 : C_red * Real.log ((q : ℝ) + 2) ≤
            C_red * (2 * (A * Real.log (Real.log x + 2) + Real.log 2)) :=
          mul_le_mul_of_nonneg_left h1 hC_red
        have h5 : (0 : ℝ) ≤ C_red * (2 * (A * Real.log (Real.log x + 2) + Real.log 2)) := by
          refine mul_nonneg hC_red ?_
          have h6' : 0 ≤ A * Real.log (Real.log x + 2) :=
            mul_nonneg hA.le (Real.log_nonneg (by linarith))
          have h7' : 0 < Real.log 2 := Real.log_pos (by norm_num)
          linarith
        exact mul_le_mul h9 h2 h6 h5
      have h9 : C_red * (2 * (A * Real.log (Real.log x + 2) + Real.log 2)) * (Real.log x + 2)
          = (1 / 2) * (4 * C_red * (A * Real.log (Real.log x + 2) + Real.log 2) *
              (Real.log x + 2)) := by
        ring
      rw [h9] at h8
      linarith [h8, h4]
    -- assemble
    have hXnn : 0 ≤ x * Real.exp (-c * Real.log x ^ (1 / 12 : ℝ)) := by positivity
    have htrunc3 : ‖(∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
          ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χs n * (n : ℂ) ^ (-(Complex.I * u)))‖
        ≤ ‖chiPerronTw χs u x' (v7chiT x)‖ +
          C_p * (x' * (Real.log x') ^ 2 / v7chiT x + Real.log x') := by
      have hsub : ‖(∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
            ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χs n * (n : ℂ) ^ (-(Complex.I * u))) -
            chiPerronTw χs u x' (v7chiT x)‖
          ≤ C_p * (x' * (Real.log x') ^ 2 / v7chiT x + Real.log x') := by
        rw [norm_sub_rev, ← hsumid]
        exact htrunc
      have h := norm_add_le
        ((∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
          ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χs n * (n : ℂ) ^ (-(Complex.I * u))) -
          chiPerronTw χs u x' (v7chiT x))
        (chiPerronTw χs u x' (v7chiT x))
      have hid : ((∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
              ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χs n * (n : ℂ) ^ (-(Complex.I * u))) -
            chiPerronTw χs u x' (v7chiT x)) + chiPerronTw χs u x' (v7chiT x)
          = ∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
              ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χs n * (n : ℂ) ^ (-(Complex.I * u)) := by
        ring
      rw [hid] at h
      linarith [h, hsub]
    have hred := hRed x q χ hχ hx2 u
    have hperr2 : ‖chiPerronTw χs u x' (v7chiT x)‖
        ≤ (1 / 2) * (x * Real.exp (-c * Real.log x ^ (1 / 12 : ℝ))) := by
      linarith [hperr, hterm1, hterm2]
    have htri : ‖(∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
          ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ n * (n : ℂ) ^ (-(Complex.I * u)))‖
        ≤ C_red * Real.log ((q : ℝ) + 2) * Real.log (x + 2) +
          (‖chiPerronTw χs u x' (v7chiT x)‖ +
            C_p * (x' * (Real.log x') ^ 2 / v7chiT x + Real.log x')) := by
      have h := norm_add_le
        ((∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
            ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ n * (n : ℂ) ^ (-(Complex.I * u))) -
          ∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
            ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χs n * (n : ℂ) ^ (-(Complex.I * u)))
        (∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
          ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χs n * (n : ℂ) ^ (-(Complex.I * u)))
      have hid : ((∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
              ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ n * (n : ℂ) ^ (-(Complex.I * u))) -
            ∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
              ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χs n * (n : ℂ) ^ (-(Complex.I * u))) +
            ∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
              ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χs n * (n : ℂ) ^ (-(Complex.I * u))
          = ∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
              ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ n * (n : ℂ) ^ (-(Complex.I * u)) := by
        ring
      rw [hid] at h
      linarith [h, hred, htrunc3]
    have hCfin_ge : (2 : ℝ) ≤ C_fin := by
      rw [hCfindef]
      exact le_max_left _ _
    have htotal : ‖(∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
          ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ n * (n : ℂ) ^ (-(Complex.I * u)))‖
        ≤ (5 / 4) * (x * Real.exp (-c * Real.log x ^ (1 / 12 : ℝ))) := by
      linarith [htri, hred_le, htrunc_le, hperr2]
    calc ‖(∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
          ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ n * (n : ℂ) ^ (-(Complex.I * u)))‖
        ≤ (5 / 4) * (x * Real.exp (-c * Real.log x ^ (1 / 12 : ℝ))) := htotal
      _ ≤ C_fin * (x * Real.exp (-c * Real.log x ^ (1 / 12 : ℝ))) := by
          nlinarith [hCfin_ge, hXnn]
      _ = C_fin * x * Real.exp (-c * Real.log x ^ (1 / 12 : ℝ)) := by ring
  · -- ===== small case: `x < X₁` =====
    push_neg at hxbig
    have hx_le : x ≤ X₁ := le_of_lt hxbig
    have hX₁pos : 0 < X₁ := by
      have h : (6 : ℝ) ≤ X₁ := le_max_right _ _
      linarith
    have hlogx_le : Real.log x ≤ Real.log X₁ := Real.log_le_log (by linarith) hx_le
    have hCfin_ge : Real.log X₁ * Real.exp (c * Real.log X₁ ^ (1 / 12 : ℝ)) ≤ C_fin := by
      have h1 := le_max_right (2 : ℝ)
        (Real.log X₁ * Real.exp (c * Real.log X₁ ^ (1 / 12 : ℝ)) + 1)
      rw [hCfindef]
      linarith
    have hsum_le : ‖(∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
          ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ n * (n : ℂ) ^ (-(Complex.I * u)))‖
        ≤ x * Real.log x := by
      have hx0 : (0 : ℝ) ≤ x := by linarith
      have h1 : ∀ n ∈ Finset.Icc 1 ⌊x⌋₊,
          ‖((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ n * (n : ℂ) ^ (-(Complex.I * u))‖
            ≤ Real.log x := by
        intro n hn
        rw [Finset.mem_Icc] at hn
        have hn0 : (0 : ℕ) < n := by omega
        have hχn : ‖χ n‖ ≤ 1 := DirichletCharacter.norm_le_one χ _
        have hpow : ‖(n : ℂ) ^ (-(Complex.I * u))‖ = 1 := by
          rw [Complex.norm_natCast_cpow_of_pos hn0]; simp
        have hnle : (n : ℝ) ≤ x := le_trans (by exact_mod_cast hn.2) (Nat.floor_le hx0)
        calc ‖((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ n * (n : ℂ) ^ (-(Complex.I * u))‖
            = (ArithmeticFunction.vonMangoldt n : ℝ) * ‖χ n‖ := by
              rw [norm_mul, norm_mul, hpow, mul_one, Complex.norm_real]
              rw [Real.norm_eq_abs, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
          _ ≤ (ArithmeticFunction.vonMangoldt n : ℝ) := by
              have h2 : (0 : ℝ) ≤ (ArithmeticFunction.vonMangoldt n : ℝ) :=
                ArithmeticFunction.vonMangoldt_nonneg
              nlinarith [hχn]
          _ ≤ Real.log n := ArithmeticFunction.vonMangoldt_le_log
          _ ≤ Real.log x := Real.log_le_log (by positivity) hnle
      calc ‖(∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
            ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ n * (n : ℂ) ^ (-(Complex.I * u)))‖
          ≤ ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, Real.log x :=
            le_trans (norm_sum_le _ _) (Finset.sum_le_sum h1)
        _ = (⌊x⌋₊ : ℝ) * Real.log x := by
            rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
        _ ≤ x * Real.log x := by
            have hlogx0 : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
            have h2 : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx0
            nlinarith
    have hexp_ge : Real.exp (-c * Real.log X₁ ^ (1 / 12 : ℝ))
        ≤ Real.exp (-c * Real.log x ^ (1 / 12 : ℝ)) := by
      apply Real.exp_le_exp.mpr
      have h1 : Real.log x ^ (1 / 12 : ℝ) ≤ Real.log X₁ ^ (1 / 12 : ℝ) :=
        Real.rpow_le_rpow (Real.log_nonneg (by linarith)) hlogx_le (by norm_num)
      nlinarith [hcpos]
    have hmain : x * Real.log x ≤ C_fin * x * Real.exp (-c * Real.log x ^ (1 / 12 : ℝ)) := by
      have h2 : Real.log X₁ ≤ C_fin * Real.exp (-c * Real.log X₁ ^ (1 / 12 : ℝ)) := by
        have h3 : Real.exp (c * Real.log X₁ ^ (1 / 12 : ℝ)) *
            Real.exp (-c * Real.log X₁ ^ (1 / 12 : ℝ)) = 1 := by
          rw [← Real.exp_add]
          simp
        have h4 : Real.log X₁ * (Real.exp (c * Real.log X₁ ^ (1 / 12 : ℝ)) *
            Real.exp (-c * Real.log X₁ ^ (1 / 12 : ℝ))) ≤
            C_fin * Real.exp (-c * Real.log X₁ ^ (1 / 12 : ℝ)) := by
          have h5 : Real.log X₁ * (Real.exp (c * Real.log X₁ ^ (1 / 12 : ℝ)) *
              Real.exp (-c * Real.log X₁ ^ (1 / 12 : ℝ))) =
              (Real.log X₁ * Real.exp (c * Real.log X₁ ^ (1 / 12 : ℝ))) *
              Real.exp (-c * Real.log X₁ ^ (1 / 12 : ℝ)) := by ring
          rw [h5]
          exact mul_le_mul_of_nonneg_right hCfin_ge (Real.exp_pos _).le
        rwa [h3, mul_one] at h4
      have hx0 : 0 ≤ x := by linarith
      have h5 : x * Real.log x ≤ x * Real.log X₁ := mul_le_mul_of_nonneg_left hlogx_le hx0
      have h6 : x * Real.log X₁ ≤ x * (C_fin * Real.exp (-c * Real.log X₁ ^ (1 / 12 : ℝ))) :=
        mul_le_mul_of_nonneg_left h2 hx0
      have h7 : x * (C_fin * Real.exp (-c * Real.log X₁ ^ (1 / 12 : ℝ))) ≤
          x * (C_fin * Real.exp (-c * Real.log x ^ (1 / 12 : ℝ))) := by
        apply mul_le_mul_of_nonneg_left _ hx0
        exact mul_le_mul_of_nonneg_left hexp_ge (by positivity)
      linarith [h5, h6, h7]
    linarith [hsum_le, hmain]

end

end Work.BMF
