import Mathlib
import Submission.NK.HeckeL.Zeta
import Submission.NK.HeckeL.Dictionary
import Submission.NK.HeckeL.heckeEulerProduct_eq_artinLSeries
import Submission.NK.HeckeL.Series.heckeLSeries_eq_heckeEulerProduct
import Submission.NK.HeckeL.Series.exp_artinLogEulerProduct
import Submission.NK.HeckeL.Series.artinPrimeSum_sub_artinLogEulerProduct_isBigO
import Submission.NK.HeckeL.Nonvanishing.artinLSeries_value_ne_zero
import Submission.NK.HeckeL.primeSum_eq_artinPrimeSum
import Submission.Commons.NumberTheory.NumberField.Set.summable_primeIdealZetaSum
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open NumberField IsDedekindDomain Filter Asymptotics
open scoped BigOperators Classical nonZeroDivisors Topology

open NK.GlobalCFT (Idele IdeleClassGroup)

noncomputable section

namespace NK.HeckeL.Consequences

/-!
# Consequences of the Hecke/Artin dictionary: boundedness of the character-twisted prime sum

This file proves `primeSum_isBigO`: for a non-trivial character `χ` of the ray class group, the
Hecke prime sum `∑_{𝔭 ∉ S} χ(𝔭) N𝔭^{-s}` stays bounded as `s → 1⁺`.

The proof transfers the Hecke regularity hypothesis to the Galois side along Artin reciprocity
(`artinLSeries_eq_heckeLSeries`), and then applies the Artin-side argument: `artinLogEulerProduct`
is a continuous branch of the logarithm of the Artin `L`-series, whose limit at `1⁺` is non-zero by
the non-vanishing input `NK.HeckeL.Nonvanishing.artinLSeries_value_ne_zero`; hence
`artinLogEulerProduct` is bounded, and it differs from the Artin prime sum by an `O(1)` term.

The analytic continuity of `artinLogEulerProduct` and the "continuous branch of the logarithm"
lemma are reproduced here so that this module does not import
`NK.HeckeL.Series.continuousOn_artinLogEulerProduct`; the latter and
`NK.HeckeL.Series.heckeLSeries_eq_heckeEulerProduct` declare a common auxiliary lemma under the
same name, so no module may import both.
-/

/-! ## Continuity of the logarithmic Euler product -/

/-! ## Preparatory estimates -/

/-- A nonzero prime ideal of the ring of integers of a number field has absolute norm at least
`2`. -/
lemma absNorm_primeIdeal_ge_two {K : Type*} [Field K] [NumberField K]
    (𝔭 : NK.HeckeL.PrimeIdeal K) : 2 ≤ Ideal.absNorm 𝔭.asIdeal := by
  have h0 : Ideal.absNorm 𝔭.asIdeal ≠ 0 := fun h =>
    𝔭.ne_bot (Ideal.absNorm_eq_zero_iff.mp h)
  have h1 : Ideal.absNorm 𝔭.asIdeal ≠ 1 := fun h =>
    𝔭.isPrime.ne_top (Ideal.absNorm_eq_one_iff.mp h)
  omega

/-- The modulus of a character value times a prime power: `‖χ(𝔭) N𝔭^{-s}‖ ≤ N𝔭^{-c}` for
`1 < c ≤ s`, `N𝔭 ≥ 2` and `‖χ(𝔭)‖ ≤ 1`. -/
lemma norm_mul_rpow_le {n : ℝ} (hn : 2 ≤ n) (a : ℂ) (ha : ‖a‖ ≤ 1) {c s : ℝ}
    (hc : 1 < c) (hcs : c ≤ s) : ‖a * ((n ^ (-s) : ℝ) : ℂ)‖ ≤ n ^ (-c) := by
  have hn0 : (0 : ℝ) ≤ n := by linarith
  have hn1 : (1 : ℝ) ≤ n := by linarith
  have hnorm : ‖a * ((n ^ (-s) : ℝ) : ℂ)‖ = ‖a‖ * n ^ (-s) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg hn0 _)]
  rw [hnorm]
  calc ‖a‖ * n ^ (-s) ≤ 1 * n ^ (-s) := by gcongr
    _ = n ^ (-s) := one_mul _
    _ ≤ n ^ (-c) := Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)

/-- The same bound, strict, for `s > c > 1`. -/
lemma norm_mul_rpow_lt_half {n : ℝ} (hn : 2 ≤ n) (a : ℂ) (ha : ‖a‖ ≤ 1) {c s : ℝ}
    (hc : 1 < c) (hcs : c < s) : ‖a * ((n ^ (-s) : ℝ) : ℂ)‖ < 1 / 2 := by
  refine lt_of_le_of_lt (norm_mul_rpow_le hn a ha hc hcs.le) ?_
  have h1 : n ^ (-c) ≤ (2 : ℝ) ^ (-c) :=
    Real.rpow_le_rpow_of_nonpos (by norm_num) hn (by linarith)
  have h2 : (2 : ℝ) ^ (-c) < 1 / 2 := by
    have h3 := (Real.rpow_lt_rpow_left_iff (x := (2 : ℝ)) (by norm_num)).mpr
      (show (-c : ℝ) < (-1 : ℝ) by linarith)
    rw [Real.rpow_neg_one] at h3
    have h4 : (2 : ℝ)⁻¹ = 1 / 2 := by norm_num
    linarith
  linarith

/-- The logarithmic Euler factor at a single prime is bounded by `(3/2) * N𝔭^{-c}` on
`(c, ∞)`, for `c > 1`. -/
lemma norm_neg_log_one_sub_le {n : ℝ} (hn : 2 ≤ n) (a : ℂ) (ha : ‖a‖ ≤ 1) {c s : ℝ}
    (hc : 1 < c) (hcs : c < s) :
    ‖-Complex.log (1 - a * ((n ^ (-s) : ℝ) : ℂ))‖ ≤ (3 / 2) * n ^ (-c) := by
  have hnorm : ‖a * ((n ^ (-s) : ℝ) : ℂ)‖ ≤ 1 / 2 :=
    (norm_mul_rpow_lt_half hn a ha hc hcs).le
  have hlog : ‖Complex.log (1 - a * ((n ^ (-s) : ℝ) : ℂ))‖ ≤
      (3 / 2) * ‖a * ((n ^ (-s) : ℝ) : ℂ)‖ := by
    have h1 := Complex.norm_log_one_add_half_le_self
      (z := -(a * ((n ^ (-s) : ℝ) : ℂ))) (by rw [norm_neg]; exact hnorm)
    rwa [← sub_eq_add_neg, norm_neg] at h1
  calc ‖-Complex.log (1 - a * ((n ^ (-s) : ℝ) : ℂ))‖
      = ‖Complex.log (1 - a * ((n ^ (-s) : ℝ) : ℂ))‖ := norm_neg _
    _ ≤ (3 / 2) * ‖a * ((n ^ (-s) : ℝ) : ℂ)‖ := hlog
    _ ≤ (3 / 2) * n ^ (-c) := by
        gcongr
        exact norm_mul_rpow_le hn a ha hc hcs.le

/-- Continuity of a single logarithmic Euler factor on `(s₀, ∞)` for `s₀ > 1`. -/
lemma continuousOn_logEulerTerm (n : ℝ) (hn : 2 ≤ n) (a : ℂ) (ha : ‖a‖ ≤ 1) {s₀ : ℝ}
    (hs₀ : 1 < s₀) :
    ContinuousOn (fun s : ℝ => -Complex.log (1 - a * ((n ^ (-s) : ℝ) : ℂ))) (Set.Ioi s₀) := by
  have hnpos : n ≠ 0 := by linarith
  have hcont : ContinuousOn (fun s : ℝ => 1 - a * ((n ^ (-s) : ℝ) : ℂ)) (Set.Ioi s₀) :=
    (continuous_const.sub (continuous_const.mul <|
      Complex.continuous_ofReal.comp <|
        (Real.continuous_const_rpow hnpos).comp continuous_neg)).continuousOn
  refine (hcont.clog fun s hs => ?_).neg
  have hlt : ‖-(a * ((n ^ (-s) : ℝ) : ℂ))‖ < 1 := by
    rw [norm_neg]
    exact lt_of_lt_of_le (norm_mul_rpow_lt_half hn a ha hs₀ hs) (by norm_num)
  have := Complex.mem_slitPlane_of_norm_lt_one hlt
  simpa [sub_eq_add_neg] using this

/-! ## Continuity of the logarithmic Euler product -/

theorem continuousOn_artinLogEulerProduct {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (S : Finset (NK.HeckeL.PrimeIdeal K)) (χ : Gal(L/K) →* ℂˣ) :
    ContinuousOn (fun s : ℝ => NK.HeckeL.artinLogEulerProduct K L S χ s) (Set.Ioi 1) := by
  haveI : Fintype Gal(L/K) := AlgEquiv.fintype K L
  have hnorm_one : ∀ g : Gal(L/K), ‖(χ g : ℂ)‖ = 1 := fun g =>
    NK.Chebotarev.norm_monoidHom_units_apply_eq_one χ g
  have key : ∀ c : ℝ, 1 < c →
      ContinuousOn (fun s : ℝ => NK.HeckeL.artinLogEulerProduct K L S χ s) (Set.Ioi c) := by
    intro c hc
    simp only [NK.HeckeL.artinLogEulerProduct]
    refine continuousOn_tsum
      (u := fun 𝔭 : {𝔭 : NK.HeckeL.PrimeIdeal K // 𝔭 ∉ S} =>
        (3 / 2) * (Ideal.absNorm 𝔭.1.asIdeal : ℝ) ^ (-c)) ?_ ?_ ?_
    · intro 𝔭
      refine continuousOn_logEulerTerm (Ideal.absNorm 𝔭.1.asIdeal : ℝ)
        (by exact_mod_cast absNorm_primeIdeal_ge_two 𝔭.1)
        (χ (NK.Chebotarev.frobAtPrime (K := K) (L := L) 𝔭.1) : ℂ)
        (le_of_eq (hnorm_one (NK.Chebotarev.frobAtPrime (K := K) (L := L) 𝔭.1))) hc
    · have hsum : Summable (fun 𝔭 : NK.HeckeL.PrimeIdeal K =>
          (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-c)) :=
        Commons.NumberTheory.NumberField.Set.summable_primeIdealZetaSum (K := K) hc
      exact (hsum.mul_left (3 / 2)).subtype (fun 𝔭 => 𝔭 ∉ S)
    · intro 𝔭 s hs
      exact norm_neg_log_one_sub_le (by exact_mod_cast absNorm_primeIdeal_ge_two 𝔭.1)
        (χ (NK.Chebotarev.frobAtPrime (K := K) (L := L) 𝔭.1) : ℂ)
        (le_of_eq (hnorm_one (NK.Chebotarev.frobAtPrime (K := K) (L := L) 𝔭.1))) hc hs
  refine continuousOn_of_locally_continuousOn fun x hx => ?_
  obtain ⟨c, h1c, hcx⟩ := exists_between (show (1 : ℝ) < x from hx)
  exact ⟨Set.Ioi c, isOpen_Ioi, hcx, by
    rw [Set.Ioi_inter_Ioi, max_eq_right h1c.le]
    exact key c h1c⟩
/-! ## A continuous branch of the logarithm tending to a non-zero limit is bounded -/

/-- **A continuous branch of the logarithm of a function tending to a non-zero limit is bounded.**

If `f` is continuous on `(1, ∞)` and `exp ∘ f` tends to a non-zero limit `w` as `s → 1⁺`, then `f`
is `O(1)` near `1⁺`.

Indeed `exp (f s) / w → 1`, so on a small interval `(1, 1+ε)` the auxiliary function
`g s = log (exp (f s) / w) + log w` is a continuous branch of the logarithm of `exp ∘ f`, hence
`f - g` is continuous there with values in the discrete subgroup `2πiℤ`; being defined on a
connected set it is constant, so `f` differs from the bounded function `g` by a constant. -/
lemma isBigO_of_tendsto_exp_ne_zero {f : ℝ → ℂ} {w : ℂ}
    (hf : ContinuousOn f (Set.Ioi 1))
    (ht : Tendsto (fun s => Complex.exp (f s)) (nhdsWithin (1 : ℝ) (Set.Ioi 1)) (𝓝 w))
    (hw : w ≠ 0) :
    f =O[nhdsWithin (1 : ℝ) (Set.Ioi 1)] (fun _ : ℝ => (1 : ℂ)) := by
  have hL' : Tendsto (fun s : ℝ => Complex.exp (f s) / w)
      (nhdsWithin (1 : ℝ) (Set.Ioi 1)) (𝓝 1) := by
    simpa [div_self hw] using ht.div_const w
  -- On a small interval to the right of `1` the quotient `exp (f s) / w` stays in the right
  -- half-plane, hence in the slit plane.
  have hU : {y : ℂ | (1 : ℝ) / 2 < y.re} ∈ 𝓝 (1 : ℂ) :=
    (isOpen_Ioi.preimage Complex.continuous_re).mem_nhds (by norm_num)
  have hev : ∀ᶠ s in nhdsWithin (1 : ℝ) (Set.Ioi 1),
      (1 : ℝ) / 2 < (Complex.exp (f s) / w).re := hL'.eventually hU
  obtain ⟨e, he, hesub⟩ := Metric.mem_nhdsWithin_iff.mp hev
  set ε : ℝ := min e 1 / 2 with hεdef
  have hε : 0 < ε := by
    have : 0 < min e 1 := lt_min he one_pos
    linarith
  have hεe : ε < e := by
    have hle : ε ≤ e / 2 := by
      rw [hεdef]
      exact div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
    linarith [lt_min he one_pos]
  have hε1 : ε < 1 := by
    have hle : ε ≤ 1 / 2 := by
      rw [hεdef]
      exact div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
    linarith
  have hfε : ContinuousOn f (Set.Ioo (1 : ℝ) (1 + ε)) := hf.mono (fun s hs => hs.1)
  have hmemε : ∀ s ∈ Set.Ioo (1 : ℝ) (1 + ε),
      (1 : ℝ) / 2 < (Complex.exp (f s) / w).re := by
    intro s hs
    apply hesub
    refine ⟨?_, hs.1⟩
    rw [Metric.mem_ball, Real.dist_eq]
    have h1 : (1 : ℝ) < s := hs.1
    have h2 : s < 1 + ε := hs.2
    rw [abs_of_pos (by linarith : (0 : ℝ) < s - 1)]
    linarith
  set g : ℝ → ℂ := fun s => Complex.log (Complex.exp (f s) / w) + Complex.log w with hgdef
  have hgcont : ContinuousOn g (Set.Ioo (1 : ℝ) (1 + ε)) := by
    have h1 : ContinuousOn (fun s : ℝ => Complex.exp (f s) / w) (Set.Ioo (1 : ℝ) (1 + ε)) :=
      (hfε.cexp).div_const w
    have h2 : ContinuousOn (fun s : ℝ => Complex.log (Complex.exp (f s) / w))
        (Set.Ioo (1 : ℝ) (1 + ε)) :=
      h1.clog (fun s hs => Complex.mem_slitPlane_iff.mpr
        (Or.inl (by linarith [hmemε s hs] : (0 : ℝ) < (Complex.exp (f s) / w).re)))
    simpa [hgdef] using h2.add_const (Complex.log w)
  have hexp : ∀ s ∈ Set.Ioo (1 : ℝ) (1 + ε), Complex.exp (f s) = Complex.exp (g s) := by
    intro s _hs
    have hz : Complex.exp (f s) / w ≠ 0 := div_ne_zero (Complex.exp_ne_zero _) hw
    simp only [hgdef]
    rw [Complex.exp_add, Complex.exp_log hz, Complex.exp_log hw, div_mul_cancel₀ _ hw]
  have hgl : Tendsto g (nhdsWithin (1 : ℝ) (Set.Ioi 1)) (𝓝 (Complex.log w)) := by
    have h1 : Tendsto (fun s : ℝ => Complex.log (Complex.exp (f s) / w))
        (nhdsWithin (1 : ℝ) (Set.Ioi 1)) (𝓝 (Complex.log 1)) :=
      hL'.clog (by simp [Complex.mem_slitPlane_iff])
    have := h1.add_const (Complex.log w)
    simpa [hgdef, Complex.log_one] using this
  have hgO : g =O[nhdsWithin (1 : ℝ) (Set.Ioi 1)] (fun _ : ℝ => (1 : ℂ)) :=
    hgl.isBigO_one ℂ
  -- The connectedness argument: `f - g` is continuous and `2πiℤ`-valued on `(1, 1+ε)`.
  have hS : IsPreconnected (Set.Ioo (1 : ℝ) (1 + ε)) := isPreconnected_Ioo
  have hFcont : ContinuousOn (fun s : ℝ => f s - g s) (Set.Ioo (1 : ℝ) (1 + ε)) :=
    hfε.sub hgcont
  have hT : IsDiscrete
      (((AddSubgroup.zmultiples (2 * ↑Real.pi * Complex.I) : AddSubgroup ℂ)) : Set ℂ) := by
    rw [isDiscrete_iff_discreteTopology]
    exact NormedSpace.discreteTopology_zmultiples _
  have hmap : Set.MapsTo (fun s : ℝ => f s - g s) (Set.Ioo (1 : ℝ) (1 + ε))
      (((AddSubgroup.zmultiples (2 * ↑Real.pi * Complex.I) : AddSubgroup ℂ)) : Set ℂ) := by
    intro s hs
    have hexps : Complex.exp (f s - g s) = 1 := by
      rw [Complex.exp_sub, hexp s hs, div_self (Complex.exp_ne_zero (g s))]
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp hexps
    change f s - g s ∈ AddSubgroup.zmultiples (2 * ↑Real.pi * Complex.I)
    rw [AddSubgroup.mem_zmultiples_iff]
    refine ⟨n, ?_⟩
    rw [zsmul_eq_mul]
    exact hn.symm
  have hconst : ∀ x ∈ Set.Ioo (1 : ℝ) (1 + ε), ∀ y ∈ Set.Ioo (1 : ℝ) (1 + ε),
      f x - g x = f y - g y :=
    fun x hx y hy => hS.constant_of_mapsTo hT hFcont hmap hx hy
  have hmem : (1 + ε / 2) ∈ Set.Ioo (1 : ℝ) (1 + ε) := by
    refine ⟨?_, ?_⟩ <;> linarith
  have hnb : Set.Ioo (1 : ℝ) (1 + ε) ∈ nhdsWithin (1 : ℝ) (Set.Ioi 1) := by
    rw [Metric.mem_nhdsWithin_iff]
    refine ⟨ε, hε, ?_⟩
    intro s hs
    obtain ⟨hsb, hsi⟩ := hs
    have hs1 : (1 : ℝ) < s := hsi
    have h1 : |s - 1| < ε := by simpa [Real.dist_eq] using (Metric.mem_ball.mp hsb)
    rw [abs_of_pos (by linarith : (0 : ℝ) < s - 1)] at h1
    exact ⟨hs1, by linarith⟩
  have heq : (fun s : ℝ => f s) =ᶠ[nhdsWithin (1 : ℝ) (Set.Ioi 1)]
      (fun s : ℝ => g s + (f (1 + ε / 2) - g (1 + ε / 2))) := by
    rw [Filter.eventuallyEq_iff_exists_mem]
    refine ⟨Set.Ioo (1 : ℝ) (1 + ε), hnb, ?_⟩
    intro s hs
    exact sub_eq_iff_eq_add'.mp (hconst s hs _ hmem)
  have hb : (fun s : ℝ => g s + (f (1 + ε / 2) - g (1 + ε / 2)))
      =O[nhdsWithin (1 : ℝ) (Set.Ioi 1)] (fun _ : ℝ => (1 : ℂ)) :=
    hgO.add (isBigO_const_one ℂ (f (1 + ε / 2) - g (1 + ε / 2)) _)
  exact hb.congr' heq.symm Filter.EventuallyEq.rfl
theorem artinPrimeSum_isBigO' {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (S : Finset (NK.HeckeL.PrimeIdeal K)) (hcomm : ∀ a b : Gal(L/K), a * b = b * a)
    (hS : ∀ 𝔭 : NK.HeckeL.PrimeIdeal K, ¬ NK.HeckeL.IsUnramifiedIn (K := K) (L := L) 𝔭 → 𝔭 ∈ S)
    (h : ∀ ψ : Gal(L/K) →* ℂˣ, ψ ≠ 1 → NK.HeckeL.ArtinLRegularAtOne K L S ψ)
    (χ : Gal(L/K) →* ℂˣ) (hχ : χ ≠ 1) :
    (fun s : ℝ => NK.HeckeL.artinPrimeSum K L S χ s)
      =O[nhdsWithin (1 : ℝ) (Set.Ioi 1)] (fun _ : ℝ => (1 : ℂ)) := by
  -- the value of the `L`-series at `1` is non-zero (non-vanishing input)
  have hv : (h χ hχ).value ≠ 0 := NK.HeckeL.Nonvanishing.artinLSeries_value_ne_zero S hcomm hS h χ hχ
  -- `artinLogEulerProduct` is a continuous branch of `log (artinLSeries ·)`, whence bounded.
  have hteq : (fun s : ℝ => Complex.exp (NK.HeckeL.artinLogEulerProduct K L S χ s))
      =ᶠ[nhdsWithin (1 : ℝ) (Set.Ioi 1)] (fun s : ℝ => NK.HeckeL.artinLSeries K L S χ s) := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact NK.HeckeL.Series.exp_artinLogEulerProduct S χ hs
  have ht : Tendsto (fun s : ℝ => Complex.exp (NK.HeckeL.artinLogEulerProduct K L S χ s))
      (nhdsWithin (1 : ℝ) (Set.Ioi 1)) (𝓝 (h χ hχ).value) :=
    Filter.Tendsto.congr' hteq.symm (h χ hχ).tendsto
  have hfO : (fun s : ℝ => NK.HeckeL.artinLogEulerProduct K L S χ s)
      =O[nhdsWithin (1 : ℝ) (Set.Ioi 1)] (fun _ : ℝ => (1 : ℂ)) :=
    isBigO_of_tendsto_exp_ne_zero
      (continuousOn_artinLogEulerProduct S χ) ht hv
  -- `artinPrimeSum` differs from `artinLogEulerProduct` by an `O(1)` term.
  have hsub : (fun s : ℝ => NK.HeckeL.artinPrimeSum K L S χ s -
        NK.HeckeL.artinLogEulerProduct K L S χ s)
      =O[nhdsWithin (1 : ℝ) (Set.Ioi 1)] (fun _ : ℝ => (1 : ℂ)) :=
    NK.HeckeL.Series.artinPrimeSum_sub_artinLogEulerProduct_isBigO S χ
  have hdecomp : (fun s : ℝ => NK.HeckeL.artinPrimeSum K L S χ s)
      = (fun s : ℝ => NK.HeckeL.artinPrimeSum K L S χ s -
            NK.HeckeL.artinLogEulerProduct K L S χ s)
        + (fun s : ℝ => NK.HeckeL.artinLogEulerProduct K L S χ s) := by
    ext s
    simp only [Pi.add_apply, sub_add_cancel]
  rw [hdecomp]
  exact hsub.add hfO
/-! ## Transfer of the regularity input to the Galois side -/

/-- On the half-plane `s > 1` the Hecke `L`-series of a ray class character equals the Artin
`L`-series of the corresponding Galois character: the Dirichlet series is the Euler product
(`NK.HeckeL.Series.heckeLSeries_eq_heckeEulerProduct`) and the Euler factors agree under Artin
reciprocity (`NK.HeckeL.heckeEulerProduct_eq_artinLSeries`). -/
theorem heckeLSeries_eq_artinLSeries {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] {U : Subgroup (NK.GlobalCFT.Idele K)}
    [Finite (NK.GlobalCFT.IdeleClassGroup.rayClassGroup K U)]
    (h : NK.GlobalCFT.ArtinReciprocity K L)
    (e : NK.GlobalCFT.IdeleClassGroup.rayClassGroup K U ≃*
      (NK.GlobalCFT.IdeleClassGroup K ⧸ NK.GlobalCFT.Idele.normClassSubgroup K L))
    (S : Finset (NK.HeckeL.PrimeIdeal K))
    (hFrob : NK.HeckeL.FrobeniusCompatibility K L U h e S)
    (χ : NK.HeckeL.RayChar K U) {s : ℝ} (hs : 1 < s) :
    NK.HeckeL.heckeLSeries K U S χ s =
      NK.HeckeL.artinLSeries K L S (NK.HeckeL.rayCharEquivGalois h e χ) s := by
  rw [NK.HeckeL.Series.heckeLSeries_eq_heckeEulerProduct U S χ hs,
    NK.HeckeL.heckeEulerProduct_eq_artinLSeries h e S hFrob χ s]

/-- Transfer of the named regularity input from the Hecke side to the Artin side along the
Artin-reciprocity dictionary of characters: a non-trivial Galois character `ψ` is the image of a
non-trivial ray class character `χ`, and `L`-series regularity is preserved. -/
def artinLRegular_of_heckeLRegular {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] {U : Subgroup (NK.GlobalCFT.Idele K)}
    [Finite (NK.GlobalCFT.IdeleClassGroup.rayClassGroup K U)]
    (h : NK.GlobalCFT.ArtinReciprocity K L)
    (e : NK.GlobalCFT.IdeleClassGroup.rayClassGroup K U ≃*
      (NK.GlobalCFT.IdeleClassGroup K ⧸ NK.GlobalCFT.Idele.normClassSubgroup K L))
    (S : Finset (NK.HeckeL.PrimeIdeal K))
    (hFrob : NK.HeckeL.FrobeniusCompatibility K L U h e S)
    (hH : ∀ χ : NK.HeckeL.RayChar K U, χ ≠ 1 → NK.HeckeL.HeckeLRegularAtOne K U S χ) :
    ∀ ψ : Gal(L/K) →* ℂˣ, ψ ≠ 1 → NK.HeckeL.ArtinLRegularAtOne K L S ψ := by
  intro ψ hψ
  have hχ : (NK.HeckeL.rayCharEquivGalois h e).symm ψ ≠ 1 := by
    intro h1
    apply hψ
    have h2 := congrArg (NK.HeckeL.rayCharEquivGalois h e) h1
    simpa using h2
  refine ⟨(hH _ hχ).value, ?_⟩
  refine (hH _ hχ).tendsto.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hmem : (NK.HeckeL.rayCharEquivGalois h e) ((NK.HeckeL.rayCharEquivGalois h e).symm ψ) = ψ :=
    MulEquiv.apply_symm_apply _ _
  rw [heckeLSeries_eq_artinLSeries h e S hFrob ((NK.HeckeL.rayCharEquivGalois h e).symm ψ) hs, hmem]


/-! ## The main theorem -/

theorem primeSum_isBigO {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    {U : Subgroup (NK.GlobalCFT.Idele K)}
    [Finite (NK.GlobalCFT.IdeleClassGroup.rayClassGroup K U)]
    (h : NK.GlobalCFT.ArtinReciprocity K L)
    (e : NK.GlobalCFT.IdeleClassGroup.rayClassGroup K U ≃*
      (NK.GlobalCFT.IdeleClassGroup K ⧸ NK.GlobalCFT.Idele.normClassSubgroup K L))
    (S : Finset (NK.HeckeL.PrimeIdeal K)) (hcomm : ∀ a b : Gal(L/K), a * b = b * a)
    (hS : ∀ 𝔭 : NK.HeckeL.PrimeIdeal K, ¬ NK.HeckeL.IsUnramifiedIn (K := K) (L := L) 𝔭 → 𝔭 ∈ S)
    (hFrob : NK.HeckeL.FrobeniusCompatibility K L U h e S)
    (hH : ∀ χ : NK.HeckeL.RayChar K U, χ ≠ 1 → NK.HeckeL.HeckeLRegularAtOne K U S χ)
    (χ : NK.HeckeL.RayChar K U) (hχ : χ ≠ 1) :
    (fun s : ℝ => NK.HeckeL.primeSum K U S χ s)
      =O[nhdsWithin (1 : ℝ) (Set.Ioi 1)] (fun _ : ℝ => (1 : ℂ)) := by
  have hArtin : ∀ ψ : Gal(L/K) →* ℂˣ, ψ ≠ 1 → NK.HeckeL.ArtinLRegularAtOne K L S ψ :=
    artinLRegular_of_heckeLRegular h e S hFrob hH
  have hχ' : NK.HeckeL.rayCharEquivGalois h e χ ≠ 1 :=
    fun h1 => hχ ((NK.HeckeL.rayCharEquivGalois_eq_one_iff h e).mp h1)
  have hb := artinPrimeSum_isBigO' (K := K) (L := L) S hcomm hS hArtin
    (NK.HeckeL.rayCharEquivGalois h e χ) hχ'
  have heq : (fun s : ℝ => NK.HeckeL.primeSum K U S χ s)
      = fun s : ℝ =>
          NK.HeckeL.artinPrimeSum K L S (NK.HeckeL.rayCharEquivGalois h e χ) s := by
    funext s
    exact NK.HeckeL.primeSum_eq_artinPrimeSum h e S hFrob χ s
  rw [heq]
  exact hb

end NK.HeckeL.Consequences
