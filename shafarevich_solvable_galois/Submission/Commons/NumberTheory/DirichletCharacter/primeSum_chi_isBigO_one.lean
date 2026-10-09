import Mathlib.NumberTheory.LSeries.Nonvanishing
import Submission.Commons.NumberTheory.DirichletCharacter.LFunction_logDeriv_eq_neg_LSeries_vonMangoldt
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open Complex LSeries ArithmeticFunction
open scoped LSeries.notation
open Filter Topology

namespace Commons.NumberTheory.DirichletCharacter

/-!
# Boundedness of the prime sum `∑_p χ(p) p^{-s}` near `s = 1⁺`

For a non-principal Dirichlet character `χ` modulo `q`, the prime sum
`∑_p χ(p) p^{-s}` stays bounded as `s → 1⁺` (it converges to `∑_p χ(p)/p`).

The proof compares the prime sum with the logarithm of the Euler product,
`-log(1 - χ(p) p^{-s}) = χ(p) p^{-s} + R_p(s)`, where the correction `R_p(s)` is
bounded by `2 p^{-2s}`, and uses that
`∑_p -log(1 - χ(p) p^{-s}) = log L(s, χ)` evaluated through the `L`-series, whose
log-derivative `L'/L` is continuous at `s = 1` because `L(1, χ) ≠ 0`.
-/

noncomputable section

/-- The Dirichlet series coefficients `χ n · Λ n / log n`, whose `L`-series is the logarithm
of the Euler product of `L(·, χ)`. -/
private def chiLamLog (q : ℕ) (χ : DirichletCharacter ℂ q) : ℕ → ℂ :=
  fun n : ℕ => (χ (n : ZMod q)) * ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)
    / ((Real.log (n : ℝ)) : ℂ)

/-- The individual summand `χ(p) p^{-s}` of the prime sum, over `p : Nat.Primes`. -/
private def chiZ (q : ℕ) (χ : DirichletCharacter ℂ q) (u : ℝ) (p : Nat.Primes) : ℂ :=
  χ ((p : ℕ) : ZMod q) * (((p : ℕ) : ℂ) ^ (-(u : ℂ)))

/-- The prime sum `∑_p χ(p) p^{-u}` (target of the theorem). -/
private def primeChiSum (q : ℕ) (χ : DirichletCharacter ℂ q) (u : ℝ) : ℂ :=
  ∑' p : Nat.Primes, χ ((p : ℕ) : ZMod q) * ((((p : ℕ) : ℝ) ^ (-u) : ℝ) : ℂ)

/-- The logarithm of the Euler product, `∑_p -log (1 - χ(p) p^{-u})`. -/
private def primeLogSum (q : ℕ) (χ : DirichletCharacter ℂ q) (u : ℝ) : ℂ :=
  ∑' p : Nat.Primes, -Complex.log (1 - chiZ q χ u p)

/-- The correction series `∑_p (-log (1 - χ(p) p^{-u}) - χ(p) p^{-u})`. -/
private def primeCorrSum (q : ℕ) (χ : DirichletCharacter ℂ q) (u : ℝ) : ℂ :=
  ∑' p : Nat.Primes, (-Complex.log (1 - chiZ q χ u p) - chiZ q χ u p)

/-! ## Elementary estimates -/

/-- Pointwise bound on the Taylor remainder of `-log (1 - z)`. -/
private lemma norm_neg_log_one_sub_sub_le {z : ℂ} (hz : ‖z‖ ≤ 1/2) :
    ‖-Complex.log (1 - z) - z‖ ≤ 2 * ‖z‖^2 := by
  have hz1 : ‖z‖ < 1 := by linarith
  have hzR : ‖(‖z‖ : ℝ)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg z)]; exact hz1
  have hgsummR : Summable (fun n : ℕ => ‖z‖^n) := summable_geometric_of_norm_lt_one hzR
  set g : ℕ → ℂ := fun n => z^(n+1)/((n:ℂ)+1) with hg
  have h1 : HasSum g (-Complex.log (1-z)) := by
    have := hasSum_taylorSeries_neg_log' hz1
    simpa [hg] using this
  have hs : Summable g := h1.summable
  have heq : -Complex.log (1-z) - z = ∑' n : ℕ, g (n+1) := by
    rw [← h1.tsum_eq, hs.tsum_eq_zero_add]
    have hg0 : g 0 = z := by simp [g]
    rw [hg0]; ring
  rw [heq]
  have hnormsumm : Summable (fun n : ℕ => ‖g (n+1)‖) := (summable_nat_add_iff 1).mpr hs.norm
  have hstep : ∀ n : ℕ, ‖g (n+1)‖ = ‖z‖^n * ‖z‖^2 / ((n:ℝ)+2) := by
    intro n
    simp only [g]
    rw [norm_div, norm_pow,
      show ((↑(n+1) : ℂ) + 1) = (((n:ℝ)+2 : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    rw [show n+1+1 = n+2 from by omega, pow_add]
  calc ‖∑' n : ℕ, g (n+1)‖
      ≤ ∑' n : ℕ, ‖g (n+1)‖ := norm_tsum_le_tsum_norm hnormsumm
    _ ≤ ∑' n : ℕ, ‖z‖^2 * ‖z‖^n := by
        apply Summable.tsum_le_tsum _ hnormsumm (hgsummR.mul_left (‖z‖^2))
        intro n
        rw [hstep n]
        calc ‖z‖^n * ‖z‖^2 / ((n:ℝ)+2) ≤ ‖z‖^n * ‖z‖^2 :=
              div_le_self (by positivity) (by have : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n; linarith)
          _ = ‖z‖^2 * ‖z‖^n := by ring
    _ = ‖z‖^2 * ∑' n : ℕ, ‖z‖^n := tsum_mul_left
    _ = ‖z‖^2 * (1 - ‖z‖)⁻¹ := by
        rw [tsum_geometric_of_norm_lt_one (ξ := ‖z‖) hzR]
    _ ≤ 2 * ‖z‖^2 := by
        have hpos : 0 < 1 - ‖z‖ := by linarith
        have hle : (1 - ‖z‖)⁻¹ ≤ 2 := by
          rw [inv_le_comm₀ hpos (by norm_num : (0:ℝ) < 2)]
          linarith
        calc ‖z‖^2 * (1 - ‖z‖)⁻¹ ≤ ‖z‖^2 * 2 := mul_le_mul_of_nonneg_left hle (sq_nonneg ‖z‖)
          _ = 2 * ‖z‖^2 := by ring

/-- Norm of `χ(p) p^{-s}` is at most `p^{-s}`. -/
private lemma norm_chiZ_le {q : ℕ} (χ : DirichletCharacter ℂ q) (u : ℝ) (p : Nat.Primes) :
    ‖chiZ q χ u p‖ ≤ ((p : ℕ) : ℝ) ^ (-u) := by
  rw [chiZ, norm_mul]
  have h1 : ‖χ ((p : ℕ) : ZMod q)‖ ≤ 1 := χ.norm_le_one _
  have h2 : ‖(((p : ℕ) : ℂ)) ^ (-(u : ℂ))‖ = ((p : ℕ) : ℝ) ^ (-u) := by
    rw [norm_natCast_cpow_of_pos (n := (p : ℕ)) p.prop.pos]
    simp
  rw [h2]
  calc ‖χ ((p : ℕ) : ZMod q)‖ * ((p : ℕ) : ℝ) ^ (-u)
      ≤ 1 * ((p : ℕ) : ℝ) ^ (-u) :=
        mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    _ = ((p : ℕ) : ℝ) ^ (-u) := one_mul _

/-- Pointwise bound on the correction summand. -/
private lemma norm_corrTerm_le {q : ℕ} (χ : DirichletCharacter ℂ q) {u : ℝ} (hu : 1 ≤ u)
    (p : Nat.Primes) :
    ‖-Complex.log (1 - chiZ q χ u p) - chiZ q χ u p‖ ≤ 2 * ((p : ℕ) : ℝ) ^ (-2 : ℝ) := by
  have hp2 : (2 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast p.prop.two_le
  have hp1 : (1 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast p.prop.one_le
  have hzub := norm_chiZ_le χ u p
  have hzle : ‖chiZ q χ u p‖ ≤ 1/2 := by
    refine hzub.trans ?_
    calc ((p : ℕ) : ℝ) ^ (-u) ≤ (2 : ℝ) ^ (-u) :=
          Real.rpow_le_rpow_of_nonpos (by norm_num) hp2 (by linarith)
      _ ≤ (2 : ℝ) ^ (-1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 1/2 := by rw [Real.rpow_neg_one]; norm_num
  have hz2 : ‖chiZ q χ u p‖ ^ 2 ≤ ((p : ℕ) : ℝ) ^ (-2 : ℝ) := by
    refine (pow_le_pow_left₀ (norm_nonneg _) hzub 2).trans ?_
    have hpos : (0:ℝ) < ((p : ℕ) : ℝ) := by positivity
    rw [pow_two, ← Real.rpow_add hpos]
    apply Real.rpow_le_rpow_of_exponent_le hp1
    linarith
  calc ‖-Complex.log (1 - chiZ q χ u p) - chiZ q χ u p‖ ≤ 2 * ‖chiZ q χ u p‖ ^ 2 :=
        norm_neg_log_one_sub_sub_le hzle
    _ ≤ 2 * ((p : ℕ) : ℝ) ^ (-2 : ℝ) := mul_le_mul_of_nonneg_left hz2 (by norm_num)

/-! ## The Euler-product identity and differentiability of the logarithm -/

private lemma abscissa_chiLamLog_le {q : ℕ} (χ : DirichletCharacter ℂ q) :
    abscissaOfAbsConv (chiLamLog q χ) ≤ 1 := by
  apply LSeries.abscissaOfAbsConv_le_of_le_const
  refine ⟨1, fun n hn => ?_⟩
  rcases eq_or_ne n 1 with rfl | hn1
  · simp [chiLamLog]
  · have hn2 : 2 ≤ n := by omega
    have hlogpos : 0 < Real.log (n:ℝ) := Real.log_pos (by exact_mod_cast hn2)
    have hΛnonneg : 0 ≤ (ArithmeticFunction.vonMangoldt n : ℝ) := ArithmeticFunction.vonMangoldt_nonneg
    have hΛle : (ArithmeticFunction.vonMangoldt n : ℝ) ≤ Real.log (n:ℝ) := ArithmeticFunction.vonMangoldt_le_log
    have hchin : ‖χ (n : ZMod q)‖ ≤ 1 := χ.norm_le_one (n : ZMod q)
    rw [chiLamLog]
    rw [norm_div, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg hΛnonneg, abs_of_pos hlogpos]
    rw [div_le_one hlogpos]
    calc ‖χ (n : ZMod q)‖ * ArithmeticFunction.vonMangoldt n
        ≤ 1 * ArithmeticFunction.vonMangoldt n :=
          mul_le_mul_of_nonneg_right hchin hΛnonneg
      _ = ArithmeticFunction.vonMangoldt n := one_mul _
      _ ≤ Real.log (n:ℝ) := hΛle

/-- The logarithm of the Euler product is the `L`-series of `chiLamLog`. -/
private lemma eulerLogEq {q : ℕ} (χ : DirichletCharacter ℂ q) {u : ℝ} (hu : 1 < u) :
    primeLogSum q χ u = L (chiLamLog q χ) (u:ℂ) := by
  have h := DirichletCharacter.eulerProduct_log_eq_LSeries χ (s := (u:ℂ)) (by simpa using hu)
  have key : chiLamLog q χ = fun n : ℕ => χ (n : ZMod q) * ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) / ((Real.log (n:ℝ)) : ℂ) := rfl
  rw [key]
  simpa [primeLogSum, chiZ] using h

/-- The pointwise product `log · chiLamLog` coincides (for `n ≠ 0`) with `χ n · Λ n`. -/
private lemma logMul_chiLamLog_eq_LSeries {q : ℕ} (χ : DirichletCharacter ℂ q) (s : ℂ) :
    L (LSeries.logMul (chiLamLog q χ)) s
      = L (fun n : ℕ => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ (n : ZMod q)) s := by
  apply LSeries_congr
  intro n hn
  rcases eq_or_ne n 1 with rfl | hn1
  · simp [LSeries.logMul, chiLamLog]
  · have hn2 : 2 ≤ n := by omega
    have hlog : Complex.log (n : ℂ) = ((Real.log (n:ℝ)) : ℂ) :=
      (Complex.ofReal_log (x := (n:ℝ)) (Nat.cast_nonneg n)).symm
    simp only [LSeries.logMul, chiLamLog]
    rw [hlog]
    have hlogne : ((Real.log (n:ℝ)) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.log_pos (by exact_mod_cast hn2)))
    field_simp

/-- `primeLogSum` is differentiable on `(1, ∞)` with derivative `L'/L`. -/
private lemma HasDerivAt_primeLogSum {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {u : ℝ}
    (hu : 1 < u) :
    HasDerivAt (primeLogSum q χ) (logDeriv (DirichletCharacter.LFunction χ) (u:ℂ)) u := by
  have habs : abscissaOfAbsConv (chiLamLog q χ) < (↑u : ℂ).re := by
    rw [Complex.ofReal_re]
    exact lt_of_le_of_lt (abscissa_chiLamLog_le χ) (by exact_mod_cast hu)
  have hderiv : HasDerivAt (fun y : ℝ => L (chiLamLog q χ) (y:ℂ))
      (-L (LSeries.logMul (chiLamLog q χ)) (u:ℂ)) u :=
    (LSeries_hasDerivAt habs).comp_ofReal
  have hident : -L (LSeries.logMul (chiLamLog q χ)) (u:ℂ)
      = logDeriv (DirichletCharacter.LFunction χ) (u:ℂ) := by
    rw [logMul_chiLamLog_eq_LSeries χ (u:ℂ)]
    rw [Commons.NumberTheory.DirichletCharacter.LFunction_logDeriv_eq_neg_LSeries_vonMangoldt χ
      (s := (u:ℂ)) (by simpa using hu)]
  rw [hident] at hderiv
  refine hderiv.congr_of_eventuallyEq ?_
  filter_upwards [isOpen_Ioi.mem_nhds hu] with y hy
  exact eulerLogEq χ hy

/-! ## Bounds -/

/-- `L'/L` is bounded on `[1, 3/2]`. -/
private lemma exists_bound_logDeriv {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    ∃ M : ℝ, ∀ u ∈ Set.Icc (1:ℝ) (3/2), ‖logDeriv (DirichletCharacter.LFunction χ) (u:ℂ)‖ ≤ M := by
  have hdiff : Differentiable ℂ (DirichletCharacter.LFunction χ) :=
    DirichletCharacter.differentiable_LFunction hχ
  have hcont : ContinuousOn (fun z : ℂ => logDeriv (DirichletCharacter.LFunction χ) z)
      {z : ℂ | 1 ≤ z.re} := by
    have hd : ContinuousOn (deriv (DirichletCharacter.LFunction χ)) {z : ℂ | 1 ≤ z.re} :=
      (hdiff.deriv.continuous).continuousOn
    have hF : ContinuousOn (DirichletCharacter.LFunction χ) {z : ℂ | 1 ≤ z.re} :=
      hdiff.continuous.continuousOn
    have hne : ∀ z ∈ {z : ℂ | 1 ≤ z.re}, DirichletCharacter.LFunction χ z ≠ 0 :=
      fun z hz => DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) hz
    have hdiv := ContinuousOn.div hd hF hne
    have hfun : (deriv (DirichletCharacter.LFunction χ) / DirichletCharacter.LFunction χ)
        = fun z => logDeriv (DirichletCharacter.LFunction χ) z := by
      funext z; rfl
    rwa [hfun] at hdiv
  have hcomp : ContinuousOn
      (fun u : ℝ => logDeriv (DirichletCharacter.LFunction χ) (u:ℂ)) (Set.Icc 1 (3/2)) :=
    hcont.comp continuous_ofReal.continuousOn (fun u hu => by
      simp only [Set.mem_ofPred_eq, Complex.ofReal_re]; exact hu.1)
  obtain ⟨M, hM⟩ := IsCompact.exists_bound_of_continuousOn isCompact_Icc hcomp
  exact ⟨M, hM⟩

/-- Summability of `chiZ`. -/
private lemma summable_chiZ {q : ℕ} (χ : DirichletCharacter ℂ q) {u : ℝ} (hu : 1 < u) :
    Summable (chiZ q χ u) := by
  have hbase : Summable (fun p : Nat.Primes => ((p : ℕ) : ℝ) ^ (-u)) :=
    (Nat.Primes.summable_rpow (r := -u)).mpr (by linarith)
  exact Summable.of_norm_bounded hbase (fun p => norm_chiZ_le χ u p)

/-- Summability of the correction series. -/
private lemma summable_corrTerm {q : ℕ} (χ : DirichletCharacter ℂ q) {u : ℝ} (hu : 1 ≤ u) :
    Summable (fun p : Nat.Primes => -Complex.log (1 - chiZ q χ u p) - chiZ q χ u p) := by
  have hbase : Summable (fun p : Nat.Primes => 2 * ((p : ℕ) : ℝ) ^ (-2 : ℝ)) :=
    ((Nat.Primes.summable_rpow (r := (-2:ℝ))).mpr (by norm_num)).mul_left 2
  exact Summable.of_norm_bounded hbase (fun p => norm_corrTerm_le χ hu p)

/-- Uniform bound on the correction series. -/
private lemma norm_primeCorrSum_le {q : ℕ} (χ : DirichletCharacter ℂ q) {u : ℝ} (hu : 1 ≤ u) :
    ‖primeCorrSum q χ u‖ ≤ ∑' p : Nat.Primes, 2 * ((p : ℕ) : ℝ) ^ (-2 : ℝ) := by
  have hbase : Summable (fun p : Nat.Primes => 2 * ((p : ℕ) : ℝ) ^ (-2 : ℝ)) :=
    ((Nat.Primes.summable_rpow (r := (-2:ℝ))).mpr (by norm_num)).mul_left 2
  have hsumm := (summable_corrTerm χ hu).norm
  calc ‖primeCorrSum q χ u‖
      = ‖∑' p : Nat.Primes, (-Complex.log (1 - chiZ q χ u p) - chiZ q χ u p)‖ := rfl
    _ ≤ ∑' p : Nat.Primes, ‖-Complex.log (1 - chiZ q χ u p) - chiZ q χ u p‖ :=
        norm_tsum_le_tsum_norm hsumm
    _ ≤ ∑' p : Nat.Primes, 2 * ((p : ℕ) : ℝ) ^ (-2 : ℝ) :=
        Summable.tsum_le_tsum (fun p => norm_corrTerm_le χ hu p) hsumm hbase

/-- The prime sum splits as the logarithm of the Euler product minus the correction series. -/
private lemma primeChiSum_eq {q : ℕ} (χ : DirichletCharacter ℂ q) {u : ℝ} (hu : 1 < u) :
    primeChiSum q χ u = primeLogSum q χ u - primeCorrSum q χ u := by
  have hsummZ := summable_chiZ χ hu
  have hsummR := summable_corrTerm χ (le_of_lt hu)
  have hpt : ∀ p : Nat.Primes, χ ((p : ℕ) : ZMod q) * ((((p : ℕ) : ℝ) ^ (-u) : ℝ) : ℂ)
      = chiZ q χ u p := by
    intro p
    rw [chiZ]
    congr 1
    rw [Complex.ofReal_cpow (Nat.cast_nonneg (p : ℕ)) (-u), Complex.ofReal_neg,
        Complex.ofReal_natCast]
  have hS : primeChiSum q χ u = ∑' p : Nat.Primes, chiZ q χ u p := by
    rw [primeChiSum]
    exact tsum_congr hpt
  have hT : primeLogSum q χ u
      = ∑' p : Nat.Primes, chiZ q χ u p + primeCorrSum q χ u := by
    rw [primeLogSum, primeCorrSum, ← Summable.tsum_add hsummZ hsummR]
    apply tsum_congr
    intro p
    ring
  rw [hS, hT]
  ring

/-! ## The main theorem -/

theorem primeSum_chi_isBigO_one {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    Asymptotics.IsBigO (nhdsWithin (1 : ℝ) (Set.Ioi 1))
      (fun s : ℝ => ∑' p : Nat.Primes, χ ((p.1 : ℕ) : ZMod q) * ((((p.1 : ℕ) : ℝ) ^ (-s) : ℝ) : ℂ))
      (fun _ : ℝ => (1 : ℝ)) := by
  obtain ⟨M, hM⟩ := exists_bound_logDeriv χ hχ
  have hM0 : 0 ≤ M :=
    (norm_nonneg (logDeriv (DirichletCharacter.LFunction χ) ((1:ℝ):ℂ))).trans (hM 1 (by norm_num))
  -- bound on the logarithm of the Euler product near `1`
  have hlog : ∀ u : ℝ, 1 < u → u < 3/2 →
      ‖primeLogSum q χ u‖ ≤ ‖primeLogSum q χ (3/2)‖ + M * (3/2 - u) := by
    intro u hu hu32
    have hs : Convex ℝ (Set.Icc u (3/2)) := convex_Icc _ _
    have hx1 : ∀ x ∈ Set.Icc u (3/2), (1:ℝ) < x := fun x hx => by have := hx.1; linarith
    have hdiffAt : ∀ x ∈ Set.Icc u (3/2), DifferentiableAt ℝ (primeLogSum q χ) x := fun x hx =>
      (HasDerivAt_primeLogSum χ (hx1 x hx)).differentiableAt
    have hbound : ∀ x ∈ Set.Icc u (3/2), ‖deriv (primeLogSum q χ) x‖ ≤ M := fun x hx => by
      rw [(HasDerivAt_primeLogSum χ (hx1 x hx)).deriv]
      exact hM x ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have hmvt := hs.norm_image_sub_le_of_norm_deriv_le hdiffAt hbound
      (Set.left_mem_Icc.mpr (by linarith)) (Set.right_mem_Icc.mpr (by linarith))
    have hnorm : ‖(3/2 : ℝ) - u‖ = 3/2 - u := by
      rw [Real.norm_eq_abs, abs_of_pos (by linarith)]
    rw [hnorm] at hmvt
    calc ‖primeLogSum q χ u‖
        = ‖primeLogSum q χ u - primeLogSum q χ (3/2) + primeLogSum q χ (3/2)‖ := by ring_nf
      _ ≤ ‖primeLogSum q χ u - primeLogSum q χ (3/2)‖ + ‖primeLogSum q χ (3/2)‖ :=
          norm_add_le _ _
      _ = ‖primeLogSum q χ (3/2) - primeLogSum q χ u‖ + ‖primeLogSum q χ (3/2)‖ := by
          rw [norm_sub_rev]
      _ ≤ M * (3/2 - u) + ‖primeLogSum q χ (3/2)‖ := by linarith [hmvt]
      _ = ‖primeLogSum q χ (3/2)‖ + M * (3/2 - u) := by ring
  -- bound on the prime sum near `1`
  have hS : ∀ u : ℝ, 1 < u → u < 3/2 →
      ‖primeChiSum q χ u‖ ≤ ‖primeLogSum q χ (3/2)‖ + M * (1/2)
        + (∑' p : Nat.Primes, 2 * ((p : ℕ) : ℝ) ^ (-2 : ℝ)) := by
    intro u hu hu32
    rw [primeChiSum_eq χ hu]
    calc ‖primeLogSum q χ u - primeCorrSum q χ u‖
        ≤ ‖primeLogSum q χ u‖ + ‖primeCorrSum q χ u‖ := norm_sub_le _ _
      _ ≤ (‖primeLogSum q χ (3/2)‖ + M * (3/2 - u))
            + (∑' p : Nat.Primes, 2 * ((p : ℕ) : ℝ) ^ (-2 : ℝ)) :=
          add_le_add (hlog u hu hu32) (norm_primeCorrSum_le χ hu.le)
      _ ≤ ‖primeLogSum q χ (3/2)‖ + M * (1/2)
            + (∑' p : Nat.Primes, 2 * ((p : ℕ) : ℝ) ^ (-2 : ℝ)) := by
          have : M * (3/2 - u) ≤ M * (1/2) := mul_le_mul_of_nonneg_left (by linarith) hM0
          linarith
  refine Asymptotics.IsBigO.of_bound
    (‖primeLogSum q χ (3/2)‖ + M * (1/2) + (∑' p : Nat.Primes, 2 * ((p : ℕ) : ℝ) ^ (-2 : ℝ))) ?_
  rw [eventually_nhdsWithin_iff]
  filter_upwards [Iio_mem_nhds (by norm_num : (1:ℝ) < 3/2)] with u hu2 hu1
  simpa [primeChiSum] using hS u hu1 hu2

end

end Commons.NumberTheory.DirichletCharacter