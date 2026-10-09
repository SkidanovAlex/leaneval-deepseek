/-
Work of the Neukirch–Uchida team: the analytic input of Čebotarev's theorem.

Continuity of the Artin `L`-series of a character of `Gal(L/K)` on the half-plane `Re s > 1`.

The Artin `L`-series is the Euler product `∏_{𝔭 ∉ S} (1 - χ(Frob_𝔭) N𝔭^{-s})⁻¹`.  Each factor is
continuous in `s`, and on every compact subset of `{s : ℝ | 1 < s}` the factors are dominated by
`2 · N𝔭^{-s₀}` (where `s₀ > 1` is the minimum of the compact set), which is summable since
`s₀ > 1`.  Weierstrass' theorem on locally uniformly convergent products
(`Summable.hasProdLocallyUniformlyOn_one_add`) then gives continuity of the product.
-/
import Mathlib
import Submission.NK.HeckeL.Zeta
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open NumberField IsDedekindDomain
open scoped BigOperators Topology
open Filter

noncomputable section

namespace NK.HeckeL.Series

open Commons.NumberTheory.NumberField.DedekindZeta

/-! ## Elementary estimates for the Euler factors -/

/-- If `‖w‖ = r ≤ 1/2` then `(1 - w)⁻¹` differs from `1` by at most `2 r`.  This is the standard
estimate `(1 - w)⁻¹ - 1 = w (1 - w)⁻¹` together with `‖(1 - w)⁻¹‖ ≤ 2`. -/
lemma norm_inv_one_sub_sub_one_le (w : ℂ) (r : ℝ) (hw : ‖w‖ = r) (hrhalf : r ≤ 1/2) :
    ‖(1 - w)⁻¹ - 1‖ ≤ 2 * r := by
  have hwlt : ‖w‖ < 1 := by rw [hw]; linarith
  have h1wne : 1 - w ≠ 0 := by
    intro h
    have : w = 1 := (sub_eq_zero.mp h).symm
    rw [this, norm_one] at hwlt
    linarith
  have hkey : (1 - w)⁻¹ - 1 = (1 - w)⁻¹ * w := by
    have h := calc (1 - w)⁻¹ * w = (1 - w)⁻¹ * (1 - (1 - w)) := by ring
      _ = (1 - w)⁻¹ * 1 - (1 - w)⁻¹ * (1 - w) := by rw [mul_sub]
      _ = (1 - w)⁻¹ - 1 := by rw [mul_one, inv_mul_cancel₀ h1wne]
    exact h.symm
  have hnorm1w : (1:ℝ)/2 ≤ ‖1 - w‖ := by
    have h := abs_norm_sub_norm_le (1:ℂ) w
    rw [norm_one] at h
    have h2 : |1 - ‖w‖| = 1 - ‖w‖ := abs_of_nonneg (by linarith)
    rw [h2] at h
    rw [hw] at h
    linarith
  have hinv : ‖(1 - w)⁻¹‖ ≤ 2 := by
    rw [norm_inv]
    have hpos : 0 < ‖1 - w‖ := by linarith
    have hh := (inv_le_inv₀ hpos (by norm_num : (0:ℝ) < 1/2)).mpr hnorm1w
    norm_num at hh
    linarith
  calc ‖(1 - w)⁻¹ - 1‖ = ‖(1 - w)⁻¹ * w‖ := by rw [hkey]
    _ = ‖(1 - w)⁻¹‖ * ‖w‖ := by rw [norm_mul]
    _ ≤ 2 * ‖w‖ := by nlinarith [norm_nonneg w]
    _ = 2 * r := by rw [hw]

/-- **The basic estimate on the Artin Euler factors.**  For `1 < s₀ ≤ s` and a prime ideal `𝔭`,

`‖(1 - χ(Frob_𝔭) N𝔭^{-s})⁻¹ - 1‖ ≤ 2 · N𝔭^{-s₀}`.

The left-hand side equals `N𝔭^{-s} / ‖1 - χ(Frob_𝔭) N𝔭^{-s}‖`, and `‖χ(Frob_𝔭)‖ = 1` because
`Gal(L/K)` is finite (`‖χ(g)‖ = 1` for a character of a finite group), while `N𝔭 ≥ 2` makes
`N𝔭^{-s} ≤ 2^{-s₀} < 1/2`. -/
lemma norm_artinEulerFactor_sub_one_le {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] (χ : Gal(L/K) →* ℂˣ) {s s₀ : ℝ}
    (h1 : 1 < s₀) (hle : s₀ ≤ s) (𝔭 : PrimeIdeal K) :
    ‖artinEulerFactor (K:=K) (L:=L) χ s 𝔭 - 1‖ ≤
      2 * (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s₀) := by
  have hNpos : 0 < (Ideal.absNorm 𝔭.asIdeal : ℝ) := absNorm_primeIdeal_pos 𝔭
  have hN2 : 2 ≤ (Ideal.absNorm 𝔭.asIdeal : ℝ) := two_le_absNorm_primeIdeal 𝔭
  have hz : ‖(((χ (NK.Chebotarev.frobAtPrime (K:=K) (L:=L) 𝔭) : ℂˣ) : ℂ))‖ = 1 :=
    NK.Chebotarev.norm_monoidHom_units_apply_eq_one χ _
  have hr : ‖(((Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s) : ℝ) : ℂ)‖ =
      (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hNpos.le _)]
  have hwr : ‖(((χ (NK.Chebotarev.frobAtPrime (K:=K) (L:=L) 𝔭) : ℂˣ) : ℂ)) *
      ((((Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s) : ℝ)) : ℂ)‖ =
      (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s) := by
    rw [norm_mul, hz, hr, one_mul]
  have hrle : (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s) ≤ 1/2 := by
    have hNsle : (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s) ≤ (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s₀) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith : (1:ℝ) ≤ (Ideal.absNorm 𝔭.asIdeal : ℝ))
        (by linarith)
    have hN2le : (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s₀) ≤ (2:ℝ) ^ (-s₀) :=
      Real.rpow_le_rpow_of_nonpos (by norm_num) hN2 (by linarith)
    have h2 : (2:ℝ) ^ (-s₀) < 1/2 := by
      have h := Real.rpow_lt_rpow_of_exponent_lt (show (1:ℝ) < 2 by norm_num)
        (by linarith : -s₀ < -1)
      rw [Real.rpow_neg_one, inv_eq_one_div] at h
      norm_num at h
      exact h
    linarith
  have hboth : (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s) ≤ (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s₀) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith : (1:ℝ) ≤ (Ideal.absNorm 𝔭.asIdeal : ℝ))
      (by linarith)
  have key := norm_inv_one_sub_sub_one_le
    (((χ (NK.Chebotarev.frobAtPrime (K:=K) (L:=L) 𝔭) : ℂˣ) : ℂ) *
      ((((Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s) : ℝ)) : ℂ))
    ((Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s)) hwr hrle
  have heq : artinEulerFactor (K:=K) (L:=L) χ s 𝔭 - 1 =
      (1 - (((χ (NK.Chebotarev.frobAtPrime (K:=K) (L:=L) 𝔭) : ℂˣ) : ℂ) *
        ((((Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s) : ℝ)) : ℂ)))⁻¹ - 1 := rfl
  rw [heq]
  calc ‖(1 - (((χ (NK.Chebotarev.frobAtPrime (K:=K) (L:=L) 𝔭) : ℂˣ) : ℂ) *
        ((((Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s) : ℝ)) : ℂ)))⁻¹ - 1‖
      ≤ 2 * (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s) := key
    _ ≤ 2 * (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s₀) := by linarith

/-- Each Artin Euler factor is continuous on `{s : ℝ | 0 < s}`: the denominator
`1 - χ(Frob_𝔭) N𝔭^{-s}` does not vanish there because `|χ(Frob_𝔭) N𝔭^{-s}| = N𝔭^{-s} < 1`. -/
lemma continuousOn_artinEulerFactor {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] (χ : Gal(L/K) →* ℂˣ)
    (𝔭 : PrimeIdeal K) :
    ContinuousOn (fun s : ℝ => artinEulerFactor (K:=K) (L:=L) χ s 𝔭) (Set.Ioi 0) := by
  have hNpos : 0 < (Ideal.absNorm 𝔭.asIdeal : ℝ) := absNorm_primeIdeal_pos 𝔭
  unfold artinEulerFactor
  refine ContinuousOn.inv₀ ?_ ?_
  · refine ContinuousOn.sub continuousOn_const ?_
    refine ContinuousOn.mul continuousOn_const ?_
    exact (Complex.continuous_ofReal.comp
      ((Real.continuous_const_rpow (ne_of_gt hNpos)).comp continuous_neg)).continuousOn
  · intro s hs h
    have hw1 : (((χ (NK.Chebotarev.frobAtPrime (K:=K) (L:=L) 𝔭) : ℂˣ) : ℂ)) *
        ((((Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s) : ℝ)) : ℂ) = 1 := (sub_eq_zero.mp h).symm
    have hz : ‖(((χ (NK.Chebotarev.frobAtPrime (K:=K) (L:=L) 𝔭) : ℂˣ) : ℂ))‖ = 1 :=
      NK.Chebotarev.norm_monoidHom_units_apply_eq_one χ _
    have hr : ‖(((Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s) : ℝ) : ℂ)‖ =
        (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s) := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hNpos.le _)]
    have hnorm : ‖(((χ (NK.Chebotarev.frobAtPrime (K:=K) (L:=L) 𝔭) : ℂˣ) : ℂ)) *
        ((((Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s) : ℝ)) : ℂ)‖ =
        (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s) := by
      rw [norm_mul, hz, hr, one_mul]
    have hlt : (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s) < 1 :=
      rpow_neg_absNorm_primeIdeal_lt_one hs 𝔭
    rw [hw1, norm_one] at hnorm
    linarith

/-! ## Continuity of the Artin `L`-series -/

theorem continuousOn_artinLSeries {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] (S : Finset (NK.HeckeL.PrimeIdeal K))
    (χ : Gal(L/K) →* ℂˣ) :
    ContinuousOn (fun s : ℝ => NK.HeckeL.artinLSeries K L S χ s) (Set.Ioi 1) := by
  have hmain : HasProdLocallyUniformlyOn
      (fun (𝔭 : {𝔭 : NK.HeckeL.PrimeIdeal K // 𝔭 ∉ S}) (s : ℝ) =>
        NK.HeckeL.artinEulerFactor (K:=K) (L:=L) χ s 𝔭.1)
      (fun s : ℝ => ∏' (𝔭 : {𝔭 : NK.HeckeL.PrimeIdeal K // 𝔭 ∉ S}),
        NK.HeckeL.artinEulerFactor (K:=K) (L:=L) χ s 𝔭.1)
      (Set.Ioi 1) := by
    refine hasProdLocallyUniformlyOn_of_forall_compact isOpen_Ioi ?_
    intro C hCsub hC
    by_cases hne : C.Nonempty
    · obtain ⟨s₀, hs₀mem, hs₀min⟩ := hC.exists_isMinOn hne continuousOn_id
      have hs₀ : 1 < s₀ := hCsub hs₀mem
      have hle : ∀ s ∈ C, s₀ ≤ s := fun s hs => hs₀min hs
      have hu : Summable (fun 𝔭 : {𝔭 : NK.HeckeL.PrimeIdeal K // 𝔭 ∉ S} =>
          2 * (Ideal.absNorm 𝔭.1.asIdeal : ℝ) ^ (-s₀)) :=
        ((Commons.NumberTheory.NumberField.Set.summable_primeIdealNorm K hs₀).mul_left 2).subtype
          (fun 𝔭 => 𝔭 ∉ S)
      have hbd : ∀ᶠ (𝔭 : {𝔭 : NK.HeckeL.PrimeIdeal K // 𝔭 ∉ S}) in cofinite,
          ∀ s ∈ C, ‖NK.HeckeL.artinEulerFactor (K:=K) (L:=L) χ s 𝔭.1 - 1‖ ≤
            2 * (Ideal.absNorm 𝔭.1.asIdeal : ℝ) ^ (-s₀) :=
        Filter.Eventually.of_forall fun 𝔭 s hs =>
          norm_artinEulerFactor_sub_one_le χ hs₀ (hle s hs) 𝔭.1
      have hcts : ∀ 𝔭 : {𝔭 : NK.HeckeL.PrimeIdeal K // 𝔭 ∉ S},
          ContinuousOn (fun s : ℝ => NK.HeckeL.artinEulerFactor (K:=K) (L:=L) χ s 𝔭.1 - 1)
            C :=
        fun 𝔭 => ContinuousOn.sub
          ((continuousOn_artinEulerFactor χ 𝔭.1).mono
            (fun s hs => Set.mem_Ioi.mpr (lt_trans zero_lt_one (hCsub hs))))
          continuousOn_const
      have hprod := Summable.hasProdUniformlyOn_one_add hC hu hbd hcts
      refine (hprod.congr ?_).congr_right ?_
      · filter_upwards with n s hs
        exact Finset.prod_congr rfl (fun 𝔭 _ => by ring)
      · intro s hs
        exact tprod_congr (fun 𝔭 => by ring)
    · rw [Set.not_nonempty_iff_eq_empty.mp hne, hasProdUniformlyOn_iff_tendstoUniformlyOn]
      exact tendstoUniformlyOn_empty
  have hfreq : ∃ᶠ (n : Finset {𝔭 : NK.HeckeL.PrimeIdeal K // 𝔭 ∉ S}) in atTop,
      ContinuousOn (fun s : ℝ => ∏ 𝔭 ∈ n,
        NK.HeckeL.artinEulerFactor (K:=K) (L:=L) χ s 𝔭.1) (Set.Ioi 1) :=
    Filter.Frequently.of_forall fun n =>
      continuousOn_finsetProd n
        (fun 𝔭 _ => (continuousOn_artinEulerFactor χ 𝔭.1).mono
          (fun s hs => Set.mem_Ioi.mpr (lt_trans zero_lt_one hs)))
  exact hmain.continuousOn hfreq

end NK.HeckeL.Series
