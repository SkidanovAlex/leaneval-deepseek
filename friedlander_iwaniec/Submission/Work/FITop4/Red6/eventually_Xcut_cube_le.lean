import Mathlib
import Submission.Work.FITop4.Red5.Vocab
import Submission.Work.FITop4.Numeric4.log_dominance

namespace Work.FITop4.Red6

open Filter

/-- **The real-analysis core of the (16.41) proviso.**  `log` is little-`o` of `y^{1/2}`, so
eventually the fixed constant `K = 9σ+10` (where `σ = sigmaChoice Asave`) satisfies
`K·log y ≤ √y`.  The constant is irrelevant; only its fixedness matters. -/
private lemma eventually_const_mul_log_le_sqrt :
    ∀ᶠ y : ℝ in Filter.atTop,
      (9 * sigmaChoice Asave + 10) * Real.log y ≤ Real.sqrt y := by
  have hKpos : (0:ℝ) < 9 * sigmaChoice Asave + 10 := by
    unfold sigmaChoice Asave Aprime; norm_num
  have hlog : (fun y : ℝ => Real.log y) =o[Filter.atTop] (fun y : ℝ => y ^ ((1:ℝ)/2)) :=
    isLittleO_log_rpow_atTop (by norm_num)
  rw [Asymptotics.isLittleO_iff] at hlog
  filter_upwards [hlog (show (0:ℝ) < 1/(4*(9 * sigmaChoice Asave + 10)) by positivity),
      eventually_ge_atTop (1:ℝ)] with y hy hy1
  rw [Real.norm_of_nonneg (Real.log_nonneg hy1)] at hy
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (by linarith : (0:ℝ) ≤ y) _)] at hy
  rw [Real.sqrt_eq_rpow]
  have hK : (9 * sigmaChoice Asave + 10) * Real.log y
      ≤ (9 * sigmaChoice Asave + 10)
        * ((1/(4*(9 * sigmaChoice Asave + 10))) * y^((1:ℝ)/2)) :=
    mul_le_mul_of_nonneg_left hy hKpos.le
  have hsimp : (9 * sigmaChoice Asave + 10)
        * ((1/(4*(9 * sigmaChoice Asave + 10))) * y^((1:ℝ)/2))
      = (1/4) * y^((1:ℝ)/2) := by field_simp
  rw [hsimp] at hK
  have hnn : (0:ℝ) ≤ y^((1:ℝ)/2) := Real.rpow_nonneg (by linarith) _
  linarith

/-- **`X³ ≤ exp(√y)` eventually**, as a statement about the real variable `y = log N`: the cut
`X = ⌈y^{3σ+3}⌉₊` has cube bounded by `exp(√y)` for all large `y`.  The proof crushes
`⌈y^{a}⌉₊ ≤ 2 y^{a}` (`a = 3σ+3`), turns the cube into `8 y^{9σ+9} ≤ y^{9σ+10}`, and then applies
`eventually_const_mul_log_le_sqrt`. -/
private lemma eventually_Xcut_cube_le_core :
    ∀ᶠ y : ℝ in Filter.atTop,
      ((⌈y ^ (3 * sigmaChoice Asave + 3)⌉₊ : ℝ)) ^ 3 ≤ Real.exp (Real.sqrt y) := by
  filter_upwards [eventually_ge_atTop (8:ℝ), eventually_const_mul_log_le_sqrt] with y hy8 hkey
  set a : ℝ := 3 * sigmaChoice Asave + 3 with hadef
  have hypos : 0 < y := by linarith
  have hanneg : 0 ≤ a := by
    rw [hadef]; unfold sigmaChoice Asave Aprime; norm_num
  have hpowge1 : 1 ≤ y ^ a := Real.one_le_rpow (by linarith) hanneg
  have hceil_lt : (⌈y ^ a⌉₊ : ℝ) < y ^ a + 1 := Nat.ceil_lt_add_one (Real.rpow_nonneg hypos.le a)
  have hceil : (⌈y ^ a⌉₊ : ℝ) ≤ 2 * y ^ a := by linarith
  have hstep1 : ((⌈y ^ a⌉₊ : ℝ)) ^ 3 ≤ (2 * y ^ a) ^ 3 :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) hceil 3
  have h3a : a * 3 = 9 * sigmaChoice Asave + 9 := by rw [hadef]; ring
  have hpow3 : (y ^ a) ^ 3 = y ^ (a * 3) := by
    calc (y ^ a) ^ 3 = (y ^ a) ^ (3:ℝ) := by norm_num [Real.rpow_natCast]
      _ = y ^ (a * 3) := by rw [Real.rpow_mul hypos.le]
  calc ((⌈y ^ a⌉₊ : ℝ)) ^ 3 ≤ (2 * y ^ a) ^ 3 := hstep1
    _ = 8 * y ^ (a*3) := by rw [mul_pow, hpow3]; norm_num
    _ ≤ y * y ^ (a*3) := by
        apply mul_le_mul_of_nonneg_right hy8 (Real.rpow_nonneg hypos.le _)
    _ = y ^ (a*3+1) := by rw [Real.rpow_add hypos, Real.rpow_one, mul_comm]
    _ = y ^ (9 * sigmaChoice Asave + 10) := by rw [h3a]; ring_nf
    _ = Real.exp ((9 * sigmaChoice Asave + 10) * Real.log y) := by
        rw [Real.rpow_def_of_pos hypos, mul_comm]
    _ ≤ Real.exp (Real.sqrt y) := Real.exp_le_exp.mpr hkey

/-- **The (16.41) proviso, supplied by the composition's threshold.**  For `x` large, the cut
`X = Xcut Pa (sigmaChoice Asave) = ⌈(log N)^{3σ+3}⌉₊` of Proposition 10.2 satisfies `X³ ≤ exp(√log N)`
(equivalently `(9σ+9)·loglog N ≤ √(log N)`, since `σ = sigmaChoice Asave` is a fixed constant); this
is the side condition *FI* §16 imposes on (16.41) (the Fourier cut-off `K = X³ ≤ exp(√log N)`), and
it is carried explicitly by `Defs6`-era `Areas6.Area6_6`.  `Pa.hNlo : x^{1/4+η} < N` makes `log N`
grow with `Pa.x`, so the threshold can be taken as a function of the fixed `σ` alone.  The bound is
*not* among the conjuncts of `Numeric4.log_dominance` (those give `exp((loglog x)²)` etc., which are
larger than `exp(√log x)` for large `x`); the prover should establish `K·loglog N ≤ √(log N)` for
`N ≥ N₀(K)` directly (e.g. `Real.log_le_rpow`/`Real.log_lt_rpow` after substituting `u = √log N`,
or `Real.log_le_sub_one_of_pos` iterated), then transport through `Pa.hNlo`. -/
theorem eventually_Xcut_cube_le :
    ∃ x₀ : ℕ, ∀ (Pa : Work.FITop.Params), x₀ ≤ Pa.x →
      (((Work.FITop4.Xcut Pa (Work.FITop4.sigmaChoice Work.FITop4.Asave) : ℕ)) : ℝ) ^ 3
        ≤ Real.exp (Real.sqrt (Real.log ((Pa.N : ℝ)))) := by
  obtain ⟨L, hL⟩ := Filter.eventually_atTop.mp eventually_Xcut_cube_le_core
  refine ⟨⌈Real.exp (4 * L)⌉₊, fun Pa hx => ?_⟩
  -- `x₀ ≤ Pa.x` gives `4L ≤ log x`
  have hxpos : (0:ℝ) < (Pa.x : ℝ) := by
    have h : (0:ℕ) < Pa.x := by have := Pa.hx; omega
    exact_mod_cast h
  have hx1 : (1:ℝ) ≤ (Pa.x : ℝ) := by
    have h : (1:ℕ) ≤ Pa.x := by have := Pa.hx; omega
    exact_mod_cast h
  have hexp_le : Real.exp (4*L) ≤ (Pa.x : ℝ) := by
    have h1 : Real.exp (4*L) ≤ (⌈Real.exp (4*L)⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (⌈Real.exp (4*L)⌉₊ : ℝ) ≤ (Pa.x : ℝ) := by exact_mod_cast hx
    linarith
  have hlogx_ge : 4*L ≤ Real.log (Pa.x : ℝ) := by
    have h := Real.log_le_log (Real.exp_pos (4*L)) hexp_le
    rwa [Real.log_exp] at h
  -- `Pa.hNlo` gives `log N ≥ L`
  have hlogNge : L ≤ Real.log ((Pa.N : ℝ)) := by
    have hxpowpos : (0:ℝ) < (Pa.x : ℝ) ^ ((1:ℝ)/4 + Pa.η) := Real.rpow_pos_of_pos hxpos _
    have hlt := Real.log_lt_log hxpowpos Pa.hNlo
    rw [Real.log_rpow hxpos] at hlt
    have hlogxnn : 0 ≤ Real.log (Pa.x : ℝ) := Real.log_nonneg hx1
    have hstep : (1/4 : ℝ) * Real.log (Pa.x:ℝ) ≤ ((1:ℝ)/4 + Pa.η) * Real.log (Pa.x:ℝ) :=
      mul_le_mul_of_nonneg_right (by linarith [Pa.hη]) hlogxnn
    have hL4 : L ≤ (1/4 : ℝ) * Real.log (Pa.x:ℝ) := by linarith
    linarith
  exact hL (Real.log ((Pa.N : ℝ))) hlogNge

end Work.FITop4.Red6
