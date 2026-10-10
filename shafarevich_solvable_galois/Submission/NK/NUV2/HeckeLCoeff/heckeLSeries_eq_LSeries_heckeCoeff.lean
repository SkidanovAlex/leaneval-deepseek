import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.NumberTheory.LSeries.Basic
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.Topology.GDelta.MetrizableSpace
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Submission.NK.HeckeL.Series.heckeLSeries_eq_heckeEulerProduct
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open NumberField IsDedekindDomain
open Filter Finset
open scoped Topology BigOperators Classical

namespace NK.NUV2.HeckeLCoeff

/-- The nonzero ideals of `𝓞 K` coprime to every prime of `S`: the index type of the Hecke
`L`-series. -/
abbrev HIdx (K : Type) [Field K] [NumberField K] (S : Finset (NK.HeckeL.PrimeIdeal K)) : Type _ :=
  {𝔞 : Ideal (𝓞 K) // 𝔞 ≠ 0 ∧ ∀ 𝔭 ∈ S, ¬ 𝔭.asIdeal ∣ 𝔞}

/-- The fibre of the absolute norm over `n` inside the index type of the Hecke `L`-series is the
index type of the coefficient `heckeCoeff n`. -/
def fiberEquiv (K : Type) [Field K] [NumberField K] (S : Finset (NK.HeckeL.PrimeIdeal K)) (n : ℕ) :
    {𝔞 : HIdx K S // Ideal.absNorm 𝔞.1 = n} ≃
      {𝔞 : Ideal (𝓞 K) // 𝔞 ≠ 0 ∧ (∀ 𝔭 ∈ S, ¬ 𝔭.asIdeal ∣ 𝔞) ∧ Ideal.absNorm 𝔞 = n} where
  toFun x := ⟨x.1.1, x.1.2.1, x.1.2.2, x.2⟩
  invFun y := ⟨⟨y.1, y.2.1, y.2.2.1⟩, y.2.2.2⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

/-- For `s > 1`, the Hecke `L`-series `heckeLSeries K U S χ s = ∑'_𝔞 χ([𝔞]) N𝔞^{-s}`, an absolutely
convergent sum over the nonzero ideals coprime to `S`, agrees with the `L`-series of the norm-indexed
coefficient sequence `heckeCoeff K U S χ`.  This is a reindexing of an absolutely convergent sum
along the fibres of the absolute norm. -/
theorem heckeLSeries_eq_LSeries_heckeCoeff (K : Type) [Field K] [NumberField K]
    (U : Subgroup (NK.GlobalCFT.Idele K))
    [Finite (NK.GlobalCFT.IdeleClassGroup.rayClassGroup K U)]
    (S : Finset (NK.HeckeL.PrimeIdeal K)) (χ : NK.HeckeL.RayChar K U) {s : ℝ} (hs : 1 < s) :
    NK.HeckeL.heckeLSeries K U S χ s = LSeries (NK.HeckeL.heckeCoeff K U S χ) (s : ℂ) := by
  -- The Hecke series converges absolutely; transport the summability proved for the Euler-product
  -- presentation of the series along the exponent-vector bijection.
  have hsumm : Summable (fun 𝔞 : HIdx K S => NK.HeckeL.Series.gCoeff χ S s 𝔞) := by
    rw [← Equiv.summable_iff (NK.HeckeL.Series.coeffEquiv (K := K) S)
      (f := fun 𝔞 : HIdx K S => NK.HeckeL.Series.gCoeff χ S s 𝔞)]
    exact (NK.HeckeL.Series.summable_hCoeff (K := K) χ S hs).congr
      (fun c => (NK.HeckeL.Series.gCoeff_coeffEquiv χ S s c).symm)
  -- Regroup the sum according to the absolute norm: this is a bijection onto the disjoint union of
  -- the norm fibres.
  have hsigsumm : Summable (fun p : (Σ n : ℕ, {𝔞 : HIdx K S // Ideal.absNorm 𝔞.1 = n}) =>
      NK.HeckeL.Series.gCoeff χ S s p.2.1) :=
    (Equiv.summable_iff (Equiv.sigmaFiberEquiv (fun 𝔞 : HIdx K S => Ideal.absNorm 𝔞.1))
      (f := fun 𝔞 : HIdx K S => NK.HeckeL.Series.gCoeff χ S s 𝔞)).mpr hsumm
  have hsig : (∑' p : (Σ n : ℕ, {𝔞 : HIdx K S // Ideal.absNorm 𝔞.1 = n}),
        NK.HeckeL.Series.gCoeff χ S s p.2.1)
      = ∑' n : ℕ, ∑' 𝔞 : {𝔞 : HIdx K S // Ideal.absNorm 𝔞.1 = n},
          NK.HeckeL.Series.gCoeff χ S s 𝔞 := by
    refine (Summable.tsum_sigma' (γ := fun n => {𝔞 : HIdx K S // Ideal.absNorm 𝔞.1 = n})
        (f := fun p : (Σ n : ℕ, {𝔞 : HIdx K S // Ideal.absNorm 𝔞.1 = n}) =>
          NK.HeckeL.Series.gCoeff χ S s p.2.1)
        (fun n => hsigsumm.sigma_factor n) hsigsumm).trans ?_
    exact tsum_congr (fun n => tsum_congr (fun 𝔞 => rfl))
  -- The coefficient at `n` is exactly the sum over the norm-`n` ideals, times `n^{-s}`.
  have hterm : ∀ n : ℕ, LSeries.term (NK.HeckeL.heckeCoeff K U S χ) (s : ℂ) n
      = ∑' 𝔞 : {𝔞 : HIdx K S // Ideal.absNorm 𝔞.1 = n}, NK.HeckeL.Series.gCoeff χ S s 𝔞 := by
    intro n
    rcases eq_or_ne n 0 with h0 | hn
    · -- there is no nonzero ideal of norm `0`
      subst h0
      haveI : IsEmpty {𝔞 : HIdx K S // Ideal.absNorm 𝔞.1 = 0} :=
        ⟨fun x => x.1.2.1 (Ideal.absNorm_eq_zero_iff.mp x.2)⟩
      rw [LSeries.term_zero, tsum_empty]
    · rw [LSeries.term_of_ne_zero hn, div_eq_mul_inv]
      have hpow : ((n : ℂ) ^ ((s : ℝ) : ℂ))⁻¹ = (((n : ℝ) ^ (-s) : ℝ) : ℂ) := by
        rw [← Complex.ofReal_natCast n, ← Complex.ofReal_cpow (Nat.cast_nonneg n) s,
          ← Complex.ofReal_inv, ← Real.rpow_neg (Nat.cast_nonneg n) s]
      rw [hpow]
      have hcoeff : NK.HeckeL.heckeCoeff K U S χ n
          = ∑' 𝔞 : {𝔞 : HIdx K S // Ideal.absNorm 𝔞.1 = n}, χ.atIdeal (𝔞 : Ideal (𝓞 K)) := by
        rw [show NK.HeckeL.heckeCoeff K U S χ n
            = ∑' 𝔞 : {𝔞 : Ideal (𝓞 K) // 𝔞 ≠ 0 ∧ (∀ 𝔭 ∈ S, ¬ 𝔭.asIdeal ∣ 𝔞) ∧ Ideal.absNorm 𝔞 = n},
                χ.atIdeal (𝔞 : Ideal (𝓞 K)) from rfl]
        rw [← Equiv.tsum_eq (fiberEquiv K S n)
          (fun 𝔞 : {𝔞 : Ideal (𝓞 K) // 𝔞 ≠ 0 ∧ (∀ 𝔭 ∈ S, ¬ 𝔭.asIdeal ∣ 𝔞) ∧ Ideal.absNorm 𝔞 = n} =>
            χ.atIdeal (𝔞 : Ideal (𝓞 K)))]
        exact tsum_congr (fun 𝔞 => rfl)
      rw [hcoeff, ← tsum_mul_right]
      exact tsum_congr (fun 𝔞 => by
        simp only [NK.HeckeL.Series.gCoeff]
        rw [𝔞.2])
  have e1 : (∑' 𝔞 : HIdx K S, NK.HeckeL.Series.gCoeff χ S s 𝔞)
      = ∑' p : (Σ n : ℕ, {𝔞 : HIdx K S // Ideal.absNorm 𝔞.1 = n}),
          NK.HeckeL.Series.gCoeff χ S s p.2.1 := by
    rw [← Equiv.tsum_eq (Equiv.sigmaFiberEquiv (fun 𝔞 : HIdx K S => Ideal.absNorm 𝔞.1))
      (fun 𝔞 : HIdx K S => NK.HeckeL.Series.gCoeff χ S s 𝔞)]
    exact tsum_congr (fun p => rfl)
  calc NK.HeckeL.heckeLSeries K U S χ s
      = ∑' 𝔞 : HIdx K S, NK.HeckeL.Series.gCoeff χ S s 𝔞 := rfl
    _ = ∑' p : (Σ n : ℕ, {𝔞 : HIdx K S // Ideal.absNorm 𝔞.1 = n}),
          NK.HeckeL.Series.gCoeff χ S s p.2.1 := e1
    _ = ∑' n : ℕ, ∑' 𝔞 : {𝔞 : HIdx K S // Ideal.absNorm 𝔞.1 = n},
          NK.HeckeL.Series.gCoeff χ S s 𝔞 := hsig
    _ = ∑' n : ℕ, LSeries.term (NK.HeckeL.heckeCoeff K U S χ) (s : ℂ) n :=
          tsum_congr (fun n => (hterm n).symm)
    _ = LSeries (NK.HeckeL.heckeCoeff K U S χ) (s : ℂ) := rfl

end NK.NUV2.HeckeLCoeff
