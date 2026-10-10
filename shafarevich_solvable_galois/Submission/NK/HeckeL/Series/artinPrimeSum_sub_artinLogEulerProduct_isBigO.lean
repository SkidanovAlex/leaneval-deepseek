import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.NumberTheory.EulerProduct.ExpLog
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Submission.NK.HeckeL.Zeta
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open NumberField IsDedekindDomain
open scoped BigOperators Classical
open Filter Topology

namespace NK.HeckeL.Series

/-- Quadratic bound for the remainder of the principal logarithm: for `‖z‖ < 1`,
`‖z + log (1 - z)‖ ≤ ‖z‖ ^ 2 * (1 - ‖z‖)⁻¹ / 2`.

This is `Complex.norm_log_one_sub_inv_sub_self_le` together with the identity
`log (1 - z)⁻¹ = - log (1 - z)`. -/
lemma norm_add_log_one_sub_le {z : ℂ} (hz : ‖z‖ < 1) :
    ‖z + Complex.log (1 - z)‖ ≤ ‖z‖ ^ 2 * (1 - ‖z‖)⁻¹ / 2 := by
  have hslit : (1 - z) ∈ Complex.slitPlane := by
    have h := Complex.mem_slitPlane_of_norm_lt_one (z := -z) (by simpa using hz)
    simpa [sub_eq_add_neg] using h
  have hlog : Complex.log (1 - z)⁻¹ = -Complex.log (1 - z) :=
    Complex.log_inv (1 - z) (Complex.slitPlane_arg_ne_pi hslit)
  have h := Complex.norm_log_one_sub_inv_sub_self_le hz
  rw [hlog] at h
  have heq : -Complex.log (1 - z) - z = -(z + Complex.log (1 - z)) := by ring
  rw [heq, norm_neg] at h
  exact h

/-- Summed form of the quadratic bound.  If `f` is summable and `‖f i‖ ≤ 1/2` for every `i`, then
`∑ᵢ (f i + log (1 - f i))` is summable and its norm is bounded by `∑ᵢ ‖f i‖ ^ 2`. -/
lemma norm_tsum_add_log_one_sub_le {ι : Type*} (f : ι → ℂ) (hf : Summable f)
    (h1 : ∀ i, ‖f i‖ ≤ 1 / 2) :
    ‖∑' i, (f i + Complex.log (1 - f i))‖ ≤ ∑' i, ‖f i‖ ^ 2 := by
  have hpt : ∀ i, ‖f i + Complex.log (1 - f i)‖ ≤ ‖f i‖ ^ 2 := by
    intro i
    refine (norm_add_log_one_sub_le (lt_of_le_of_lt (h1 i) one_half_lt_one)).trans ?_
    have hinv : (1 - ‖f i‖)⁻¹ ≤ 2 := by
      have h2 : (1 / 2 : ℝ) ≤ 1 - ‖f i‖ := by linarith [h1 i]
      calc (1 - ‖f i‖)⁻¹ ≤ (1 / 2 : ℝ)⁻¹ := inv_anti₀ (by norm_num) h2
        _ = 2 := by norm_num
    calc ‖f i‖ ^ 2 * (1 - ‖f i‖)⁻¹ / 2 ≤ ‖f i‖ ^ 2 * 2 / 2 := by gcongr
      _ = ‖f i‖ ^ 2 := by ring
  have hsq : Summable (fun i => ‖f i‖ ^ 2) := by
    refine Summable.of_nonneg_of_le (fun i => sq_nonneg _) (fun i => ?_)
      (hf.norm.mul_left (1 / 2))
    nlinarith [norm_nonneg (f i), h1 i]
  have hsumnorm : Summable (fun i => ‖f i + Complex.log (1 - f i)‖) :=
    Summable.of_nonneg_of_le (fun i => norm_nonneg _) hpt hsq
  exact (norm_tsum_le_tsum_norm hsumnorm).trans (Summable.tsum_le_tsum hpt hsumnorm hsq)

theorem artinPrimeSum_sub_artinLogEulerProduct_isBigO {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (S : Finset (NK.HeckeL.PrimeIdeal K)) (χ : Gal(L/K) →* ℂˣ) :
    (fun s : ℝ => NK.HeckeL.artinPrimeSum K L S χ s -
      NK.HeckeL.artinLogEulerProduct K L S χ s)
      =O[nhdsWithin (1 : ℝ) (Set.Ioi 1)] (fun _ : ℝ => (1 : ℂ)) := by
  classical
  have hchar : ∀ g : Gal(L/K), ‖(χ g : ℂ)‖ = 1 := fun g =>
    NK.Chebotarev.norm_monoidHom_units_apply_eq_one χ g
  -- the majorant `C = ∑_𝔭 N𝔭^{-2}` (over the primes outside `S`)
  set C : ℝ := ∑' 𝔭 : {𝔭 : NK.HeckeL.PrimeIdeal K // 𝔭 ∉ S},
      (Ideal.absNorm 𝔭.1.asIdeal : ℝ) ^ (-2 : ℝ) with hCdef
  have hCsum : Summable (fun 𝔭 : {𝔭 : NK.HeckeL.PrimeIdeal K // 𝔭 ∉ S} =>
      (Ideal.absNorm 𝔭.1.asIdeal : ℝ) ^ (-2 : ℝ)) :=
    (Commons.NumberTheory.NumberField.Set.summable_primeIdealZetaSum (K := K)
      (by norm_num : (1 : ℝ) < 2)).subtype (fun 𝔭 : NK.HeckeL.PrimeIdeal K => 𝔭 ∉ S)
  -- uniform bound along `(1, ∞)`
  have hbound : ∀ s : ℝ, 1 < s →
      ‖NK.HeckeL.artinPrimeSum K L S χ s -
        NK.HeckeL.artinLogEulerProduct K L S χ s‖ ≤ C := by
    intro s hs
    let e : {𝔭 : NK.HeckeL.PrimeIdeal K // 𝔭 ∉ S} → ℂ := fun 𝔭 =>
      (χ (NK.Chebotarev.frobAtPrime (K := K) (L := L) 𝔭.1) : ℂ) *
        (((Ideal.absNorm 𝔭.1.asIdeal : ℝ) ^ (-s) : ℝ) : ℂ)
    have hznorm : ∀ 𝔭 : {𝔭 : NK.HeckeL.PrimeIdeal K // 𝔭 ∉ S},
        ‖e 𝔭‖ = (Ideal.absNorm 𝔭.1.asIdeal : ℝ) ^ (-s) := by
      intro 𝔭
      simp only [e, norm_mul, hchar (NK.Chebotarev.frobAtPrime (K := K) (L := L) 𝔭.1), one_mul,
        Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg (Ideal.absNorm 𝔭.1.asIdeal)) (-s))]
    have hhalf : ∀ 𝔭 : {𝔭 : NK.HeckeL.PrimeIdeal K // 𝔭 ∉ S}, ‖e 𝔭‖ ≤ 1 / 2 := by
      intro 𝔭
      rw [hznorm 𝔭]
      have h2 : (2 : ℝ) ≤ (Ideal.absNorm 𝔭.1.asIdeal : ℝ) :=
        Commons.NumberTheory.NumberField.DedekindZeta.two_le_absNorm_primeIdeal 𝔭.1
      have h1 : (Ideal.absNorm 𝔭.1.asIdeal : ℝ) ^ (-s) ≤ (2 : ℝ) ^ (-s) :=
        Real.rpow_le_rpow_of_nonpos (by norm_num) h2 (by linarith)
      have h2' : (2 : ℝ) ^ (-s) ≤ (2 : ℝ) ^ (-1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      have h3 : (2 : ℝ) ^ (-1 : ℝ) = 1 / 2 := by rw [Real.rpow_neg_one]; norm_num
      calc (Ideal.absNorm 𝔭.1.asIdeal : ℝ) ^ (-s) ≤ (2 : ℝ) ^ (-s) := h1
        _ ≤ (2 : ℝ) ^ (-1 : ℝ) := h2'
        _ = 1 / 2 := h3
    have hf : Summable e := by
      have hbase : Summable (fun 𝔭 : {𝔭 : NK.HeckeL.PrimeIdeal K // 𝔭 ∉ S} =>
          (Ideal.absNorm 𝔭.1.asIdeal : ℝ) ^ (-s)) :=
        (Commons.NumberTheory.NumberField.Set.summable_primeIdealZetaSum (K := K) hs).subtype
          (fun 𝔭 : NK.HeckeL.PrimeIdeal K => 𝔭 ∉ S)
      refine Summable.of_norm_bounded hbase (fun 𝔭 => ?_)
      rw [hznorm 𝔭]
    have hlogsum : Summable (fun 𝔭 : {𝔭 : NK.HeckeL.PrimeIdeal K // 𝔭 ∉ S} =>
        -Complex.log (1 - e 𝔭)) := hf.clog_one_sub.neg
    have hprime : NK.HeckeL.artinPrimeSum K L S χ s =
        ∑' 𝔭 : {𝔭 : NK.HeckeL.PrimeIdeal K // 𝔭 ∉ S}, e 𝔭 := rfl
    have hlog : NK.HeckeL.artinLogEulerProduct K L S χ s =
        ∑' 𝔭 : {𝔭 : NK.HeckeL.PrimeIdeal K // 𝔭 ∉ S}, -Complex.log (1 - e 𝔭) := rfl
    have hsub : NK.HeckeL.artinPrimeSum K L S χ s -
        NK.HeckeL.artinLogEulerProduct K L S χ s =
        ∑' 𝔭 : {𝔭 : NK.HeckeL.PrimeIdeal K // 𝔭 ∉ S},
          (e 𝔭 + Complex.log (1 - e 𝔭)) := by
      rw [hprime, hlog, tsum_neg, sub_neg_eq_add]
      exact (hf.tsum_add hf.clog_one_sub).symm
    have hwsum : Summable (fun 𝔭 : {𝔭 : NK.HeckeL.PrimeIdeal K // 𝔭 ∉ S} =>
        (Ideal.absNorm 𝔭.1.asIdeal : ℝ) ^ (-(2 * s))) := by
      refine Summable.of_nonneg_of_le (fun 𝔭 => Real.rpow_nonneg (Nat.cast_nonneg _) _)
        (fun 𝔭 => ?_) hCsum
      have hbase : (1 : ℝ) ≤ (Ideal.absNorm 𝔭.1.asIdeal : ℝ) :=
        le_trans (by norm_num)
          (Commons.NumberTheory.NumberField.DedekindZeta.two_le_absNorm_primeIdeal 𝔭.1)
      exact Real.rpow_le_rpow_of_exponent_le hbase (by linarith)
    rw [hsub]
    calc ‖∑' 𝔭 : {𝔭 : NK.HeckeL.PrimeIdeal K // 𝔭 ∉ S},
            (e 𝔭 + Complex.log (1 - e 𝔭))‖
        ≤ ∑' 𝔭 : {𝔭 : NK.HeckeL.PrimeIdeal K // 𝔭 ∉ S}, ‖e 𝔭‖ ^ 2 :=
          norm_tsum_add_log_one_sub_le e hf hhalf
      _ = ∑' 𝔭 : {𝔭 : NK.HeckeL.PrimeIdeal K // 𝔭 ∉ S},
            (Ideal.absNorm 𝔭.1.asIdeal : ℝ) ^ (-(2 * s)) := by
          refine tsum_congr (fun 𝔭 => ?_)
          rw [hznorm 𝔭, ← Real.rpow_mul_natCast
            (le_of_lt (Commons.NumberTheory.NumberField.DedekindZeta.absNorm_primeIdeal_pos
              𝔭.1)) (-s) 2]
          congr 1
          ring
      _ ≤ ∑' 𝔭 : {𝔭 : NK.HeckeL.PrimeIdeal K // 𝔭 ∉ S},
            (Ideal.absNorm 𝔭.1.asIdeal : ℝ) ^ (-2 : ℝ) := by
          refine Summable.tsum_le_tsum (fun 𝔭 => ?_) hwsum hCsum
          have hbase : (1 : ℝ) ≤ (Ideal.absNorm 𝔭.1.asIdeal : ℝ) :=
            le_trans (by norm_num)
              (Commons.NumberTheory.NumberField.DedekindZeta.two_le_absNorm_primeIdeal 𝔭.1)
          exact Real.rpow_le_rpow_of_exponent_le hbase (by linarith)
      _ = C := hCdef.symm
  refine Asymptotics.IsBigO.of_bound (C + 1) ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs1 : 1 < s := Set.mem_Ioi.mp hs
  rw [norm_one, mul_one]
  exact (hbound s hs1).trans (le_add_of_nonneg_right zero_le_one)

end NK.HeckeL.Series
