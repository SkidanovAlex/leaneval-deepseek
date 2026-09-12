import Mathlib
import Submission.ModelStarChebyshev
import Submission.ModelStarLevelSet
import Submission.ModelStarHarmMeasure
import Submission.ModelStarHpot
import Submission.FeketeLim
import Submission.Commons.MeasureTheory.lintegral_log_kernel_empirical_sum_injective
import Submission.Commons.MeasureTheory.log_kernel_lintegral_ge_of_potential_eq
import Submission.Commons.MeasureTheory.atomless_of_tendsto_lintegral_le
import Submission.Commons.Analysis.Potential.lintegral_log_kernel_liminf_of_tendsto
import Submission.Commons.MeasureTheory.lintegral_log_kernel_empK
import Submission.Commons.Data.Fin.prod_Iio_eq_prod_range

/-!
# ModelStarN1 -- the Fekete root limsup of the model star is at most `1`

STATUS: research isolate (NOT imported by `Submission.lean`).

`M = F '' unitCircle` is the model star of the model map `F = modelF z₀ r`
(`F(z)/z → 1`), whose harmonic measure `μ₀ = F_*(dθ/2π)` has vanishing
logarithmic potential on `M ∖ {0}` (PROVED, `Submission.ModelStarHpot`) and is
atomless (PROVED, `Submission.ModelStarLevelSet`).  The Fekete numbers of `M`
are bounded below by `1` (PROVED, `Submission.ModelStarChebyshev`).

This module runs the classical energy/polarization argument:

  * `(N1)`  `limsup_N (feketeNumber M N)^(2/(N(N-1))) ≤ 1`.

The two analytic inputs are the polarisation lemma
`Commons.MeasureTheory.log_kernel_lintegral_ge_of_potential_eq` and the Fekete
bookkeeping (`Commons.MeasureTheory.lintegral_log_kernel_empirical_sum_injective`,
`Commons.Analysis.Potential.lintegral_log_kernel_liminf_of_tendsto`,
`Commons.MeasureTheory.atomless_of_tendsto_lintegral_le`).
-/

noncomputable section

open scoped Real BigOperators Topology ENNReal
open Filter Set Complex MeasureTheory

namespace Submission.ModelStarN1

open Submission.ModelStarMap
open Submission.FeketeLim

variable {s : ℕ} {z₀ : Fin s → ℂ} {r φ : Fin s → ℝ}

/-- The model star `M = F '' unitCircle`. -/
abbrev star (z₀ : Fin s → ℂ) (r : Fin s → ℝ) : Set ℂ := Submission.ModelStarExterior.modelStarImage z₀ r

/-- Push a probability measure on the (compact) model star into `ℂ`. -/
noncomputable def push {K : Set ℂ} (ν : MeasureTheory.ProbabilityMeasure ↥K) : MeasureTheory.Measure ℂ :=
  (ν : MeasureTheory.Measure ↥K).map (Subtype.val)

lemma isProbabilityMeasure_push {K : Set ℂ} (ν : MeasureTheory.ProbabilityMeasure ↥K) :
    MeasureTheory.IsProbabilityMeasure (push ν) :=
  MeasureTheory.Measure.isProbabilityMeasure_map (measurable_subtype_coe.aemeasurable)

/-- Transfer of a double integral from the star to `ℂ`. -/
lemma lintegral_push_prod {K : Set ℂ} (ν : MeasureTheory.ProbabilityMeasure ↥K)
    {g : ℂ × ℂ → ENNReal} (hg : Measurable g) :
    ∫⁻ w, g w ∂((push ν).prod (push ν))
      = ∫⁻ z, g (z.1.1, z.2.1) ∂((ν : MeasureTheory.Measure ↥K).prod
          (ν : MeasureTheory.Measure ↥K)) := by
  have hmap : (push ν).prod (push ν)
      = ((ν : MeasureTheory.Measure ↥K).prod (ν : MeasureTheory.Measure ↥K)).map
          (fun z : ↥K × ↥K => ((z.1 : ℂ), (z.2 : ℂ))) := by
    rw [push, MeasureTheory.Measure.map_prod_map (ν : MeasureTheory.Measure ↥K)
      (ν : MeasureTheory.Measure ↥K) measurable_subtype_coe measurable_subtype_coe]
    rfl
  rw [hmap, MeasureTheory.lintegral_map hg (by fun_prop)]


/-! ## §2  The empirical measure of a tuple in `K` -/

/-- The empirical probability measure of an (injective) tuple in `K`. -/
noncomputable def empK {K : Set ℂ} {N : ℕ} (hN : 0 < N) (x : Fin N → K) :
    MeasureTheory.ProbabilityMeasure K :=
  ⟨(N : ENNReal)⁻¹ • ∑ i : Fin N, MeasureTheory.Measure.dirac (x i), by
    constructor
    rw [MeasureTheory.Measure.smul_apply, MeasureTheory.Measure.finsetSum_apply]
    simp only [MeasureTheory.Measure.dirac_apply, Set.indicator_of_mem, Set.mem_univ,
      Pi.one_apply, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    rw [smul_eq_mul]
    exact ENNReal.inv_mul_cancel (by simp [hN.ne']) (by simp)⟩

lemma empK_coe {K : Set ℂ} {N : ℕ} (hN : 0 < N) (x : Fin N → K) :
    ((empK hN x : MeasureTheory.ProbabilityMeasure K) : MeasureTheory.Measure K)
      = (N : ENNReal)⁻¹ • ∑ i : Fin N, MeasureTheory.Measure.dirac (x i) := rfl

/-- The atoms of the empirical measure of an injective tuple are at most `1/N`. -/
lemma empK_singleton_le {K : Set ℂ} {N : ℕ} (hN : 0 < N) {x : Fin N → K}
    (hx : Function.Injective x) (a : K) :
    ((empK hN x : MeasureTheory.ProbabilityMeasure K) : MeasureTheory.Measure K) {a}
      ≤ (N : ENNReal)⁻¹ := by
  rw [empK_coe, MeasureTheory.Measure.smul_apply, MeasureTheory.Measure.finsetSum_apply]
  have hterm : ∀ i : Fin N, MeasureTheory.Measure.dirac (x i) {a} = if x i = a then 1 else 0 := by
    intro i
    by_cases h : x i = a <;> simp [h]
  simp only [hterm]
  have hsum : (∑ i : Fin N, (if x i = a then (1 : ENNReal) else 0))
      = ((Finset.univ.filter (fun i : Fin N => x i = a)).card : ENNReal) := by
    rw [← Finset.sum_filter]
    simp
  rw [hsum]
  have hcard : (Finset.univ.filter (fun i : Fin N => x i = a)).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro i hi j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
    exact hx (hi.trans hj.symm)
  calc (N : ENNReal)⁻¹ • ((Finset.univ.filter (fun i : Fin N => x i = a)).card : ENNReal)
      ≤ (N : ENNReal)⁻¹ • (1 : ENNReal) := by
        gcongr
        exact_mod_cast hcard
    _ = (N : ENNReal)⁻¹ := by simp


/-- The model star is nonempty. -/
lemma star_nonempty (hs : 0 < s) (hunit : ∀ k, ‖z₀ k‖ = 1) (hr : ∀ k, 0 < r k) :
    (star z₀ r).Nonempty :=
  ⟨0, ⟨z₀ ⟨0, hs⟩, Submission.ModelStarExterior.mem_circle.mpr (hunit _),
    Submission.ModelStarExterior.modelF_junction_eq_zero z₀ r hunit hr ⟨0, hs⟩⟩⟩

/-- A near-Fekete configuration of `N ≥ 1` points in the model star, with the
`Fin`-indexed Vandermonde product. -/
lemma exists_approx_config (hs : 0 < s) (hunit : ∀ k, ‖z₀ k‖ = 1) (hr : ∀ k, 0 < r k)
    (N : ℕ) (hN : 1 ≤ N) :
    ∃ x : Fin N → ↥(star z₀ r), Function.Injective x ∧
      (1 / 2) * feketeNumber (star z₀ r) N
        ≤ ∏ i : Fin N, ∏ j ∈ Finset.Iio i,
            ‖((x j : ↥(star z₀ r)) : ℂ) - ((x i : ↥(star z₀ r)) : ℂ)‖ := by
  have hK : IsCompact (star z₀ r) :=
    Submission.ModelStarExterior.isCompact_modelStarImage z₀ r hunit hr
  have hKne := star_nonempty (z₀ := z₀) (r := r) hs hunit hr
  have hm : 1 ≤ feketeNumber (star z₀ r) N := Submission.ModelStarChebyshev.one_le_feketeNumber_modelStar hunit hr hs N hN
  obtain ⟨y, hyK, hyvdm⟩ := exists_fekete_approx hKne hK.isBounded (n := N - 1)
    (δ := feketeNumber (star z₀ r) N / 2) (by linarith)
  have hNm : N - 1 + 1 = N := by omega
  have hyK' : ∀ i : Fin N, y i.1 ∈ star z₀ r := fun i => hyK i.1 (by omega)
  have hvpos : 0 < vdm y N := by rw [hNm] at hyvdm; linarith
  refine ⟨fun i => ⟨y i.1, hyK' i⟩, ?_, ?_⟩
  · intro i j hij
    have hyij : y i.1 = y j.1 := by
      simpa using congrArg (fun t : ↥(star z₀ r) => (t : ℂ)) hij
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact absurd hvpos (by
        rw [vdm_eq_zero_of_lt hlt (by omega) hyij]; exact lt_irrefl 0)
    · exact absurd hvpos (by
        rw [vdm_eq_zero_of_lt hgt (by omega) hyij.symm]; exact lt_irrefl 0)
  · show (1 / 2) * feketeNumber (star z₀ r) N
        ≤ ∏ i : Fin N, ∏ j ∈ Finset.Iio i, ‖y j.1 - y i.1‖
    have hconv : (∏ i : Fin N, ∏ j ∈ Finset.Iio i, ‖y j.1 - y i.1‖) = vdm y N := by
      rw [Commons.Data.Fin.prod_Iio_eq_prod_range]
      rfl
    rw [hconv]
    rw [hNm] at hyvdm
    linarith


open Submission.ModelStarHpot (hpot)
open Submission.ModelStarHarmMeasure (harmMeasure harmMeasure_compl_eq_zero)
open Submission.ModelStarLevelSet (nullSingletonClass_harmMeasure)

/-- The sequence `(2/N²) log m_N` is eventually at most any prescribed `c > 0`; this is the quantitative form of the energy bound. -/
theorem eventually_log_le (hs : 0 < s)
    (hz₀e : ∀ k, z₀ k = Submission.ModelStarBoundary2.eAngle (φ k))
    (hunit : ∀ k, ‖z₀ k‖ = 1) (hr : ∀ k, 0 < r k) (hsum : (∑ k : Fin s, r k) = 1)
    (hmono : Monotone φ) (hφinj : Function.Injective φ)
    (hφlo : ∀ k, 0 ≤ φ k) (hφhi : ∀ k, φ k < 2 * Real.pi) {c : ℝ} (hcpos : 0 < c) :
    ∀ᶠ N : ℕ in Filter.atTop,
      (2 / (N : ℝ) ^ 2) * Real.log (feketeNumber (star z₀ r) N) ≤ c := by
  classical
  have hK : IsCompact (star z₀ r) :=
    Submission.ModelStarExterior.isCompact_modelStarImage z₀ r hunit hr
  have hKne : (star z₀ r).Nonempty := star_nonempty (z₀ := z₀) (r := r) hs hunit hr
  rcases hK.isBounded.exists_pos_norm_le with ⟨R, hRpos, hR⟩
  set D : ℝ := 2 * R + 2 with hDdef
  have hDpos : 0 < D := by rw [hDdef]; linarith
  have hD1 : 1 < D := by rw [hDdef]; linarith
  have hDlog : 0 < Real.log D := Real.log_pos hD1
  have hDiam : ∀ x ∈ star z₀ r, ∀ y ∈ star z₀ r, ‖x - y‖ ≤ D := by
    intro x hx y hy
    rw [hDdef]
    calc ‖x - y‖ ≤ ‖x‖ + ‖y‖ := norm_sub_le x y
      _ ≤ R + R := add_le_add (hR x hx) (hR y hy)
      _ = 2 * R := by ring
      _ ≤ 2 * R + 2 := by linarith
  haveI hμ₀atom : MeasureTheory.NullSingletonClass (harmMeasure z₀ r) :=
    nullSingletonClass_harmMeasure hs hz₀e hunit hr hsum hmono hφinj hφlo hφhi
  have hμ₀K : (harmMeasure z₀ r) (star z₀ r)ᶜ = 0 :=
    harmMeasure_compl_eq_zero (z₀ := z₀) (r := r) hunit hr
  by_contra hcon
  rw [Filter.not_eventually] at hcon
  have hfreq : ∃ᶠ N : ℕ in Filter.atTop,
      c < (2 / (N : ℝ) ^ 2) * Real.log (feketeNumber (star z₀ r) N) :=
    hcon.mono (fun N hN => by have := not_le.mp hN; linarith)
  obtain ⟨nseq, hnmono, hnP⟩ := Nat.exists_strictMono_subsequence
    (P := fun n => c < (2 / (n : ℝ) ^ 2) * Real.log (feketeNumber (star z₀ r) n))
    (fun N => by
      obtain ⟨n, hn, hPn⟩ := (Filter.frequently_atTop.mp hfreq) (N + 1)
      exact ⟨n, Nat.lt_of_succ_le hn, hPn⟩)
  have hnge : ∀ k, 1 ≤ nseq k := by
    intro k
    rcases Nat.eq_zero_or_pos (nseq k) with h | h
    · exfalso
      have hP := hnP k
      rw [h] at hP
      simp only [Nat.cast_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
        div_zero, zero_mul] at hP
      linarith
    · exact h
  choose xk hxkinj hxkvdm using fun k => exists_approx_config hs hunit hr (nseq k) (hnge k)
  set ν : ℕ → MeasureTheory.ProbabilityMeasure ↥(star z₀ r) :=
    fun k => empK (lt_of_lt_of_le Nat.zero_lt_one (hnge k)) (xk k) with hν
  haveI : CompactSpace ↥(star z₀ r) := isCompact_iff_compactSpace.mp hK
  obtain ⟨μ, ψ, hψmono, hψlim⟩ := SeqCompactSpace.tendsto_subseq ν
  set ν' : ℕ → MeasureTheory.ProbabilityMeasure ↥(star z₀ r) := fun j => ν (ψ (2 * j + 2)) with hν'
  have hν'lim : Filter.Tendsto ν' Filter.atTop (nhds μ) :=
    hψlim.comp (strictMono_nat_of_lt_succ (fun n => by show 2 * n + 2 < 2 * (n + 1) + 2; omega)).tendsto_atTop
  -- atoms of the re-indexed empirical measures
  have hsmall : ∀ j (a : ↥(star z₀ r)), ν' j {a} ≤ ((j : ENNReal) + 1)⁻¹ := by
    intro j a
    have h1 := empK_singleton_le (N := nseq (ψ (2 * j + 2)))
      (lt_of_lt_of_le Nat.zero_lt_one (hnge (ψ (2 * j + 2)))) (hxkinj (ψ (2 * j + 2))) a
    have h2 : (nseq (ψ (2 * j + 2)) : ENNReal)⁻¹ ≤ ((j : ENNReal) + 1)⁻¹ := by
      rw [ENNReal.inv_le_inv]
      exact_mod_cast (Nat.succ_le_of_lt (lt_of_lt_of_le (by omega : j < 2 * j + 2)
        (le_trans (hψmono.id_le (2 * j + 2)) (hnmono.id_le (ψ (2 * j + 2))))) : j + 1 ≤ nseq (ψ (2 * j + 2)))
    rw [show ν' j {a} = ↑(((ν' j : MeasureTheory.Measure _) {a}).toNNReal) from rfl,
      ENNReal.coe_toNNReal (MeasureTheory.measure_ne_top _ _)]
    exact le_trans h1 h2
  set c₀ : ℝ := Real.log D + 2 * Real.log 2 with hc₀
  -- the upper bound on the empirical energies
  have henergy : ∀ j, MeasureTheory.lintegral ((ν' j : MeasureTheory.ProbabilityMeasure _).prod (ν' j))
      (fun z : ↥(star z₀ r) × ↥(star z₀ r) =>
        ENNReal.ofReal (Real.log (D / ‖((z.1 : ↥(star z₀ r)) : ℂ) - ((z.2 : ↥(star z₀ r)) : ℂ)‖)))
      ≤ ENNReal.ofReal c₀ := by
    intro j
    simp only [MeasureTheory.ProbabilityMeasure.toMeasure_prod]
    rw [Commons.MeasureTheory.lintegral_log_kernel_empK (hnge (ψ (2 * j + 2))) (xk (ψ (2 * j + 2))) (hxkinj (ψ (2 * j + 2)))
      hDpos (fun i j' => hDiam _ (xk (ψ (2 * j + 2)) i).2 _ (xk (ψ (2 * j + 2)) j').2) (ν' j) rfl]
    refine ENNReal.ofReal_le_ofReal ?_
    have hm1 : 1 ≤ feketeNumber (star z₀ r) (nseq (ψ (2 * j + 2))) :=
      Submission.ModelStarChebyshev.one_le_feketeNumber_modelStar hunit hr hs (nseq (ψ (2 * j + 2))) (hnge (ψ (2 * j + 2)))
    have hV : (1 : ℝ) / 2 ≤ ∏ i : Fin (nseq (ψ (2 * j + 2))), ∏ i' ∈ Finset.Iio i,
        ‖((xk (ψ (2 * j + 2)) i' : ↥(star z₀ r)) : ℂ) - ((xk (ψ (2 * j + 2)) i : ↥(star z₀ r)) : ℂ)‖ := by
      have := hxkvdm (ψ (2 * j + 2)); linarith
    have hlogV : -Real.log 2 ≤ Real.log (∏ i : Fin (nseq (ψ (2 * j + 2))), ∏ i' ∈ Finset.Iio i,
        ‖((xk (ψ (2 * j + 2)) i' : ↥(star z₀ r)) : ℂ) - ((xk (ψ (2 * j + 2)) i : ↥(star z₀ r)) : ℂ)‖) := by
      have h := Real.log_le_log (by norm_num : (0:ℝ) < 1/2) hV
      rwa [Real.log_div one_ne_zero (by norm_num : (2:ℝ) ≠ 0), Real.log_one, zero_sub] at h
    set M : ℝ := (nseq (ψ (2 * j + 2)) : ℝ) with hM
    have hM1 : 1 ≤ M := by rw [hM]; exact_mod_cast hnge (ψ (2 * j + 2))
    have hfac : ((M - 1) / M) ≤ 1 := by
      rw [div_le_one (by linarith)]
      linarith
    have h1 : ((M - 1) / M) * Real.log D ≤ Real.log D := by
      calc ((M - 1) / M) * Real.log D ≤ 1 * Real.log D :=
            mul_le_mul_of_nonneg_right hfac hDlog.le
        _ = Real.log D := one_mul _
    have h2 : (2 / M ^ 2) * Real.log 2 ≤ 2 * Real.log 2 := by
      have hdiv : 2 / M ^ 2 ≤ 2 := by
        rw [div_le_iff₀ (by positivity : (0:ℝ) < M ^ 2)]
        nlinarith
      exact mul_le_mul_of_nonneg_right hdiv (Real.log_nonneg (by norm_num))
    have h3 : -((2 / M ^ 2) * Real.log (∏ i : Fin (nseq (ψ (2 * j + 2))), ∏ i' ∈ Finset.Iio i,
        ‖((xk (ψ (2 * j + 2)) i' : ↥(star z₀ r)) : ℂ) - ((xk (ψ (2 * j + 2)) i : ↥(star z₀ r)) : ℂ)‖))
        ≤ (2 / M ^ 2) * Real.log 2 := by
      have hpos : 0 ≤ 2 / M ^ 2 := by positivity
      nlinarith [hlogV, hpos]
    have hcf : ((nseq (ψ (2 * j + 2)) : ℝ) - 1) / (nseq (ψ (2 * j + 2)) : ℝ) * Real.log D
        - 2 / (nseq (ψ (2 * j + 2)) : ℝ) ^ 2 * Real.log (∏ i : Fin (nseq (ψ (2 * j + 2))), ∏ i' ∈ Finset.Iio i,
            ‖((xk (ψ (2 * j + 2)) i' : ↥(star z₀ r)) : ℂ) - ((xk (ψ (2 * j + 2)) i : ↥(star z₀ r)) : ℂ)‖)
        ≤ c₀ := by
      rw [hc₀]
      rw [hM] at h1 h2 h3
      linarith
    linarith [hcf]
  -- atomlessness of the weak limit
  have hμatNN : ∀ a : ↥(star z₀ r), μ {a} = 0 :=
    Commons.MeasureTheory.atomless_of_tendsto_lintegral_le hK hDpos hDiam μ ν' hν'lim hsmall henergy
  have hμat : ∀ a : ↥(star z₀ r), (μ : MeasureTheory.Measure ↥(star z₀ r)) {a} = 0 := by
    intro a
    have h := hμatNN a
    have htop : (μ : MeasureTheory.Measure ↥(star z₀ r)) {a} ≠ ⊤ := MeasureTheory.measure_ne_top _ _
    rw [← ENNReal.coe_toNNReal htop]
    simpa using h
  haveI hμatom : MeasureTheory.NullSingletonClass (μ : MeasureTheory.Measure ↥(star z₀ r)) := ⟨hμat⟩
  -- the liminf bound (Fatou)
  have hlinf := Commons.Analysis.Potential.lintegral_log_kernel_liminf_of_tendsto hK hDpos hDiam μ ν'
    hν'lim hsmall
  -- the pushed-forward measure and the polarisation identity
  haveI hpushprob : MeasureTheory.IsProbabilityMeasure (push μ) := isProbabilityMeasure_push μ
  have hμℂK : (push μ) (star z₀ r)ᶜ = 0 := by
    rw [push, MeasureTheory.Measure.map_apply measurable_subtype_coe hK.isClosed.measurableSet.compl]
    have hempty : Subtype.val ⁻¹' (star z₀ r)ᶜ = (∅ : Set ↥(star z₀ r)) := by
      ext b
      simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_empty_iff_false, iff_false]
      exact fun hb => hb b.2
    rw [hempty]; simp
  have hμℂatom : MeasureTheory.NullSingletonClass (push μ) := by
    refine MeasureTheory.NullSingletonClass.mk (fun y => ?_)
    rw [push, MeasureTheory.Measure.map_apply measurable_subtype_coe (measurableSet_singleton y)]
    by_cases h : ∃ a : ↥(star z₀ r), (a : ℂ) = y
    · obtain ⟨a, ha⟩ := h
      have hpre : (Subtype.val : ↥(star z₀ r) → ℂ) ⁻¹' {y} = {a} := by
        ext b
        simp only [Set.mem_preimage, Set.mem_singleton_iff]
        exact ⟨fun hb => Subtype.ext (hb.trans ha.symm), fun hb => by rw [hb]; exact ha⟩
      rw [hpre]; exact hμat a
    · have hpre : (Subtype.val : ↥(star z₀ r) → ℂ) ⁻¹' {y} = (∅ : Set ↥(star z₀ r)) := by
        ext b
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
        exact fun hb => h ⟨b, hb⟩
      rw [hpre]; simp
  have hpotμ : ∀ᵐ x ∂(push μ), ∫⁻ y, ENNReal.ofReal (Real.log (D / ‖x - y‖)) ∂(harmMeasure z₀ r)
      = ENNReal.ofReal (Real.log D) := by
    have hKae : ∀ᵐ x ∂(push μ), x ∈ star z₀ r := by
      rw [MeasureTheory.ae_iff]
      have : {x : ℂ | ¬x ∈ star z₀ r} = (star z₀ r)ᶜ := rfl
      rw [this]; exact hμℂK
    have hne0 : ∀ᵐ x ∂(push μ), x ≠ 0 := by
      rw [MeasureTheory.ae_iff]
      have : {x : ℂ | ¬(x ≠ 0)} = {0} := by ext x; simp
      rw [this]; exact hμℂatom.measure_singleton 0
    filter_upwards [hKae, hne0] with x hxK hx0
    exact hpot hs hz₀e hunit hr hsum hmono hφinj hφlo hφhi hxK hx0 hDpos hDiam
  have hpotμ₀ : ∀ᵐ x ∂(harmMeasure z₀ r),
      ∫⁻ y, ENNReal.ofReal (Real.log (D / ‖x - y‖)) ∂(harmMeasure z₀ r)
        = ENNReal.ofReal (Real.log D) := by
    have hKae : ∀ᵐ x ∂(harmMeasure z₀ r), x ∈ star z₀ r := by
      rw [MeasureTheory.ae_iff]
      have : {x : ℂ | ¬x ∈ star z₀ r} = (star z₀ r)ᶜ := rfl
      rw [this]; exact hμ₀K
    have hne0 : ∀ᵐ x ∂(harmMeasure z₀ r), x ≠ 0 := by
      rw [MeasureTheory.ae_iff]
      have : {x : ℂ | ¬(x ≠ 0)} = {0} := by ext x; simp
      rw [this]; exact hμ₀atom.measure_singleton 0
    filter_upwards [hKae, hne0] with x hxK hx0
    exact hpot hs hz₀e hunit hr hsum hmono hφinj hφlo hφhi hxK hx0 hDpos hDiam
  have hge := Commons.MeasureTheory.log_kernel_lintegral_ge_of_potential_eq hK hDpos hDiam
    (push μ) (harmMeasure z₀ r) hμℂK hμ₀K hpotμ hpotμ₀
  have hconv2 : ∫⁻ z, ENNReal.ofReal (Real.log (D / ‖z.1 - z.2‖)) ∂((push μ).prod (push μ))
      = ∫⁻ z, ENNReal.ofReal (Real.log (D / ‖((z.1 : ↥(star z₀ r)) : ℂ)
          - ((z.2 : ↥(star z₀ r)) : ℂ)‖))
        ∂((μ : MeasureTheory.Measure ↥(star z₀ r)).prod (μ : MeasureTheory.Measure ↥(star z₀ r))) :=
    lintegral_push_prod μ (by fun_prop)
  -- the eventual upper bound on the empirical energies
  have hMtop : Filter.Tendsto (fun j => (nseq (ψ (2 * j + 2)) : ℝ)) Filter.atTop Filter.atTop := by
    refine Filter.tendsto_atTop_mono (fun j => ?_) tendsto_natCast_atTop_atTop
    have h3 := hnmono.id_le (ψ (2 * j + 2))
    have h4 := hψmono.id_le (2 * j + 2)
    exact_mod_cast (le_trans (by omega : j ≤ 2 * j + 2) (le_trans h4 h3))
  have hlim1 : Filter.Tendsto (fun j => ((nseq (ψ (2 * j + 2)) : ℝ) - 1) / (nseq (ψ (2 * j + 2)) : ℝ))
      Filter.atTop (nhds 1) := by
    have h1 : Filter.Tendsto (fun j => (1 : ℝ) / (nseq (ψ (2 * j + 2)) : ℝ)) Filter.atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop hMtop
    have h2 : (fun j => ((nseq (ψ (2 * j + 2)) : ℝ) - 1) / (nseq (ψ (2 * j + 2)) : ℝ))
        =ᶠ[Filter.atTop] fun j => 1 - 1 / (nseq (ψ (2 * j + 2)) : ℝ) := by
      filter_upwards with j
      have hpos : (0 : ℝ) < (nseq (ψ (2 * j + 2)) : ℝ) :=
        lt_of_lt_of_le one_pos (by exact_mod_cast hnge (ψ (2 * j + 2)))
      field_simp
    have hc1 : Filter.Tendsto (fun _ : ℕ => (1 : ℝ)) Filter.atTop (nhds 1) := tendsto_const_nhds
    have hsub : Filter.Tendsto (fun j => 1 - 1 / (nseq (ψ (2 * j + 2)) : ℝ)) Filter.atTop (nhds 1) := by
      simpa using hc1.sub h1
    exact hsub.congr' h2.symm
  have hlim2 : Filter.Tendsto (fun j => (2 : ℝ) / (nseq (ψ (2 * j + 2)) : ℝ) * Real.log 2)
      Filter.atTop (nhds 0) := by
    have h := ((tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => (2 : ℝ)) Filter.atTop
      (nhds 2)).div_atTop hMtop).mul (tendsto_const_nhds :
        Filter.Tendsto (fun _ : ℕ => Real.log 2) Filter.atTop (nhds (Real.log 2)))
    simpa using h
  have hev : ∀ᶠ j in Filter.atTop, ((nseq (ψ (2 * j + 2)) : ℝ) - 1) / (nseq (ψ (2 * j + 2)) : ℝ) * Real.log D
      - c + (2 : ℝ) / (nseq (ψ (2 * j + 2)) : ℝ) * Real.log 2 ≤ Real.log D - c / 2 := by
    have hsum : Filter.Tendsto (fun j => ((nseq (ψ (2 * j + 2)) : ℝ) - 1) / (nseq (ψ (2 * j + 2)) : ℝ) * Real.log D
        - c + (2 : ℝ) / (nseq (ψ (2 * j + 2)) : ℝ) * Real.log 2) Filter.atTop
        (nhds (Real.log D - c)) := by
      have hcD : Filter.Tendsto (fun _ : ℕ => Real.log D) Filter.atTop (nhds (Real.log D)) :=
        tendsto_const_nhds
      have hcc : Filter.Tendsto (fun _ : ℕ => c) Filter.atTop (nhds c) := tendsto_const_nhds
      have := ((hlim1.mul hcD).sub hcc).add hlim2
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, mul_comm] using this
    have hlt : Real.log D - c < Real.log D - c / 2 := by linarith [hcpos]
    exact (hsum.eventually (Iio_mem_nhds hlt)).mono (fun j hj => le_of_lt hj)
  have hLjval : ∀ j, MeasureTheory.lintegral ((ν' j : MeasureTheory.ProbabilityMeasure _).prod (ν' j))
      (fun z : ↥(star z₀ r) × ↥(star z₀ r) =>
        ENNReal.ofReal (Real.log (D / ‖((z.1 : ↥(star z₀ r)) : ℂ) - ((z.2 : ↥(star z₀ r)) : ℂ)‖)))
      = ENNReal.ofReal (((nseq (ψ (2 * j + 2)) : ℝ) - 1) / (nseq (ψ (2 * j + 2)) : ℝ) * Real.log D
          - 2 / (nseq (ψ (2 * j + 2)) : ℝ) ^ 2 * Real.log (∏ i : Fin (nseq (ψ (2 * j + 2))), ∏ i' ∈ Finset.Iio i,
              ‖((xk (ψ (2 * j + 2)) i' : ↥(star z₀ r)) : ℂ) - ((xk (ψ (2 * j + 2)) i : ↥(star z₀ r)) : ℂ)‖)) := by
    intro j
    simp only [MeasureTheory.ProbabilityMeasure.toMeasure_prod]
    rw [Commons.MeasureTheory.lintegral_log_kernel_empK (hnge (ψ (2 * j + 2))) (xk (ψ (2 * j + 2))) (hxkinj (ψ (2 * j + 2)))
      hDpos (fun i j' => hDiam _ (xk (ψ (2 * j + 2)) i).2 _ (xk (ψ (2 * j + 2)) j').2) (ν' j) rfl]
  have hEtop : ∀ᶠ j in Filter.atTop,
      ENNReal.ofReal (((nseq (ψ (2 * j + 2)) : ℝ) - 1) / (nseq (ψ (2 * j + 2)) : ℝ) * Real.log D
          - 2 / (nseq (ψ (2 * j + 2)) : ℝ) ^ 2 * Real.log (∏ i : Fin (nseq (ψ (2 * j + 2))), ∏ i' ∈ Finset.Iio i,
              ‖((xk (ψ (2 * j + 2)) i' : ↥(star z₀ r)) : ℂ) - ((xk (ψ (2 * j + 2)) i : ↥(star z₀ r)) : ℂ)‖))
        ≤ ENNReal.ofReal (Real.log D - c / 2) := by
    filter_upwards [hev] with j hj
    refine ENNReal.ofReal_le_ofReal ?_
    have hM1 : 1 ≤ (nseq (ψ (2 * j + 2)) : ℝ) := by
      exact_mod_cast hnge (ψ (2 * j + 2))
    have hMpos : (0 : ℝ) < (nseq (ψ (2 * j + 2)) : ℝ) := lt_of_lt_of_le one_pos hM1
    have hm1 : 1 ≤ feketeNumber (star z₀ r) (nseq (ψ (2 * j + 2))) :=
      Submission.ModelStarChebyshev.one_le_feketeNumber_modelStar hunit hr hs
        (nseq (ψ (2 * j + 2))) (hnge (ψ (2 * j + 2)))
    have hmpos : 0 < feketeNumber (star z₀ r) (nseq (ψ (2 * j + 2))) :=
      lt_of_lt_of_le one_pos hm1
    have hVge : (1 / 2) * feketeNumber (star z₀ r) (nseq (ψ (2 * j + 2)))
        ≤ ∏ i : Fin (nseq (ψ (2 * j + 2))), ∏ i' ∈ Finset.Iio i,
            ‖((xk (ψ (2 * j + 2)) i' : ↥(star z₀ r)) : ℂ)
              - ((xk (ψ (2 * j + 2)) i : ↥(star z₀ r)) : ℂ)‖ := hxkvdm (ψ (2 * j + 2))
    have hlogV : Real.log ((1 / 2) * feketeNumber (star z₀ r) (nseq (ψ (2 * j + 2))))
        ≤ Real.log (∏ i : Fin (nseq (ψ (2 * j + 2))), ∏ i' ∈ Finset.Iio i,
            ‖((xk (ψ (2 * j + 2)) i' : ↥(star z₀ r)) : ℂ)
              - ((xk (ψ (2 * j + 2)) i : ↥(star z₀ r)) : ℂ)‖) :=
      Real.log_le_log (by positivity) hVge
    have hsplit : Real.log ((1 / 2) * feketeNumber (star z₀ r) (nseq (ψ (2 * j + 2))))
        = Real.log ((1 : ℝ) / 2) + Real.log (feketeNumber (star z₀ r) (nseq (ψ (2 * j + 2)))) :=
      Real.log_mul (by norm_num) (ne_of_gt hmpos)
    have hloghalf : Real.log ((1 : ℝ) / 2) = -Real.log 2 := by
      rw [Real.log_div one_ne_zero (by norm_num : (2 : ℝ) ≠ 0), Real.log_one, zero_sub]
    have hcfe : c < 2 / (nseq (ψ (2 * j + 2)) : ℝ) ^ 2
        * Real.log (feketeNumber (star z₀ r) (nseq (ψ (2 * j + 2)))) := hnP (ψ (2 * j + 2))
    have hkey : -(2 / (nseq (ψ (2 * j + 2)) : ℝ) ^ 2
        * Real.log (∏ i : Fin (nseq (ψ (2 * j + 2))), ∏ i' ∈ Finset.Iio i,
            ‖((xk (ψ (2 * j + 2)) i' : ↥(star z₀ r)) : ℂ)
              - ((xk (ψ (2 * j + 2)) i : ↥(star z₀ r)) : ℂ)‖))
        ≤ 2 / (nseq (ψ (2 * j + 2)) : ℝ) ^ 2 * Real.log 2 - c := by
      have hpos : 0 ≤ 2 / (nseq (ψ (2 * j + 2)) : ℝ) ^ 2 := by positivity
      nlinarith [hlogV, hsplit, hloghalf, hcfe, hpos]
    have hfac : ((nseq (ψ (2 * j + 2)) : ℝ) - 1) / (nseq (ψ (2 * j + 2)) : ℝ) * Real.log D
        ≤ Real.log D := by
      calc ((nseq (ψ (2 * j + 2)) : ℝ) - 1) / (nseq (ψ (2 * j + 2)) : ℝ) * Real.log D
          ≤ 1 * Real.log D := mul_le_mul_of_nonneg_right (by
              rw [div_le_one hMpos]; linarith) hDlog.le
        _ = Real.log D := one_mul _
    have hb : 2 / (nseq (ψ (2 * j + 2)) : ℝ) ^ 2 * Real.log 2
        ≤ 2 / (nseq (ψ (2 * j + 2)) : ℝ) * Real.log 2 := by
      have hle : 2 / (nseq (ψ (2 * j + 2)) : ℝ) ^ 2 ≤ 2 / (nseq (ψ (2 * j + 2)) : ℝ) := by
        rw [div_le_div_iff₀ (by positivity) hMpos]
        nlinarith
      exact mul_le_mul_of_nonneg_right hle (Real.log_nonneg (by norm_num))
    linarith

  -- the upper bound on the limsup
  have hlimsup_le : Filter.limsup (fun j => MeasureTheory.lintegral
      ((ν' j : MeasureTheory.ProbabilityMeasure _).prod (ν' j))
      (fun z : ↥(star z₀ r) × ↥(star z₀ r) =>
        ENNReal.ofReal (Real.log (D / ‖((z.1 : ↥(star z₀ r)) : ℂ) - ((z.2 : ↥(star z₀ r)) : ℂ)‖))))
      Filter.atTop ≤ ENNReal.ofReal (Real.log D - c / 2) := by
    refine Filter.limsup_le_of_le (a := ENNReal.ofReal (Real.log D - c / 2)) ?_ ?_
    · refine ⟨0, fun a _ => show (0 : ENNReal) ≤ a from zero_le⟩
    · filter_upwards [hEtop] with j hj
      rw [hLjval j]
      exact hj
  -- final chain
  have hchain : ENNReal.ofReal (Real.log D) ≤ ENNReal.ofReal (Real.log D - c / 2) :=
    le_trans hge (le_trans (le_of_eq hconv2) (le_trans hlinf
      (le_trans (Filter.liminf_le_limsup (u := fun j => MeasureTheory.lintegral
          ((ν' j : MeasureTheory.ProbabilityMeasure _).prod (ν' j))
          (fun z : ↥(star z₀ r) × ↥(star z₀ r) => ENNReal.ofReal
            (Real.log (D / ‖((z.1 : ↥(star z₀ r)) : ℂ) - ((z.2 : ↥(star z₀ r)) : ℂ)‖))))
        ⟨ENNReal.ofReal c₀, Filter.eventually_atTop.2 ⟨0, fun j _ => henergy j⟩⟩
        ⟨0, Filter.eventually_atTop.2 ⟨0, fun j _ => show (0 : ENNReal) ≤ _ from zero_le⟩⟩)
      hlimsup_le)))
  have hlt : ENNReal.ofReal (Real.log D - c / 2) < ENNReal.ofReal (Real.log D) := by
    rw [ENNReal.ofReal_lt_ofReal_iff hDlog]
    linarith
  exact absurd hchain (not_le.mpr hlt)

/-- **The main energy bound**: `limsup_N (2/N²) log m_N ≤ 0` for the model star. -/
theorem limsup_log_le_zero (hs : 0 < s) (hz₀e : ∀ k, z₀ k = Submission.ModelStarBoundary2.eAngle (φ k))
    (hunit : ∀ k, ‖z₀ k‖ = 1) (hr : ∀ k, 0 < r k) (hsum : (∑ k : Fin s, r k) = 1)
    (hmono : Monotone φ) (hφinj : Function.Injective φ)
    (hφlo : ∀ k, 0 ≤ φ k) (hφhi : ∀ k, φ k < 2 * Real.pi) :
    Filter.limsup (fun N : ℕ => (2 / (N : ℝ) ^ 2) * Real.log (feketeNumber (star z₀ r) N))
      Filter.atTop ≤ 0 := by
  classical
  have hK : IsCompact (star z₀ r) :=
    Submission.ModelStarExterior.isCompact_modelStarImage z₀ r hunit hr
  have hKne : (star z₀ r).Nonempty := star_nonempty (z₀ := z₀) (r := r) hs hunit hr
  rcases hK.isBounded.exists_pos_norm_le with ⟨R, hRpos, hR⟩
  set D : ℝ := 2 * R + 2 with hDdef
  have hDpos : 0 < D := by rw [hDdef]; linarith
  have hD1 : 1 < D := by rw [hDdef]; linarith
  have hDlog : 0 < Real.log D := Real.log_pos hD1
  have hDiam : ∀ x ∈ star z₀ r, ∀ y ∈ star z₀ r, ‖x - y‖ ≤ D := by
    intro x hx y hy
    rw [hDdef]
    calc ‖x - y‖ ≤ ‖x‖ + ‖y‖ := norm_sub_le x y
      _ ≤ R + R := add_le_add (hR x hx) (hR y hy)
      _ = 2 * R := by ring
      _ ≤ 2 * R + 2 := by linarith
  haveI hμ₀atom : MeasureTheory.NullSingletonClass (harmMeasure z₀ r) :=
    nullSingletonClass_harmMeasure hs hz₀e hunit hr hsum hmono hφinj hφlo hφhi
  have hμ₀K : (harmMeasure z₀ r) (star z₀ r)ᶜ = 0 :=
    harmMeasure_compl_eq_zero (z₀ := z₀) (r := r) hunit hr
  -- the main claim, proved by contradiction
  refine le_of_forall_pos_le_add (fun c hcpos => ?_)
  refine Filter.limsup_le_of_le (a := 0 + c) ?_ ?_
  · refine ⟨0, fun a ha => ?_⟩
    obtain ⟨N, hN⟩ := (Filter.eventually_map.mp ha).exists
    rcases Nat.eq_zero_or_pos N with h0 | hNpos
    · rw [h0] at hN; simpa using hN
    · refine le_trans (mul_nonneg (div_nonneg (by norm_num) (by positivity)) ?_) hN
      exact Real.log_nonneg (Submission.ModelStarChebyshev.one_le_feketeNumber_modelStar
        hunit hr hs N hNpos)
  · simpa using eventually_log_le hs hz₀e hunit hr hsum hmono hφinj hφlo hφhi hcpos

/-- **(N1)**: the Fekete root limsup of the model star is at most `1`. -/
theorem fekete_rootLimsup_modelStar_le_one (hs : 0 < s)
    (hz₀e : ∀ k, z₀ k = Submission.ModelStarBoundary2.eAngle (φ k))
    (hunit : ∀ k, ‖z₀ k‖ = 1) (hr : ∀ k, 0 < r k) (hsum : (∑ k : Fin s, r k) = 1)
    (hmono : Monotone φ) (hφinj : Function.Injective φ)
    (hφlo : ∀ k, 0 ≤ φ k) (hφhi : ∀ k, φ k < 2 * Real.pi) :
    Filter.limsup (fun N : ℕ =>
        (feketeNumber (star z₀ r) N) ^ (2 / ((N : ℝ) * ((N : ℝ) - 1)))) Filter.atTop ≤ 1 := by
  have hmain := limsup_log_le_zero hs hz₀e hunit hr hsum hmono hφinj hφlo hφhi
  have hbound : ∀ y : ℝ, 1 < y → ∀ᶠ N : ℕ in Filter.atTop,
      (feketeNumber (star z₀ r) N) ^ (2 / ((N : ℝ) * ((N : ℝ) - 1))) ≤ y := by
    intro y hy
    have hlogy : 0 < Real.log y := Real.log_pos hy
    have hev : ∀ᶠ N : ℕ in Filter.atTop,
        (2 / (N : ℝ) ^ 2) * Real.log (feketeNumber (star z₀ r) N) ≤ Real.log y / 2 :=
      eventually_log_le hs hz₀e hunit hr hsum hmono hφinj hφlo hφhi (by positivity : 0 < Real.log y / 2)
    filter_upwards [hev, Filter.eventually_ge_atTop 2] with N hN hN2
    have hpos : 0 < feketeNumber (star z₀ r) N :=
      lt_of_lt_of_le one_pos
        (Submission.ModelStarChebyshev.one_le_feketeNumber_modelStar hunit hr hs N (by omega))
    have hyexp : y = Real.exp (Real.log y) := (Real.exp_log (by linarith : 0 < y)).symm
    rw [Real.rpow_def_of_pos hpos, hyexp]
    refine Real.exp_le_exp.mpr ?_
    have hNpos : (0 : ℝ) < (N : ℝ) := by positivity
    have hNm1 : (0 : ℝ) < (N : ℝ) - 1 := by
      have : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN2
      linarith
    have hlogN : Real.log (feketeNumber (star z₀ r) N) ≤ (N : ℝ) ^ 2 * Real.log y / 4 := by
      have h2 : (0 : ℝ) < (N : ℝ) ^ 2 := by positivity
      have hle := mul_le_mul_of_nonneg_left hN (by positivity : (0 : ℝ) ≤ (N : ℝ) ^ 2 / 2)
      have hcancel : (N : ℝ) ^ 2 / 2 * (2 / (N : ℝ) ^ 2 * Real.log (feketeNumber (star z₀ r) N))
          = Real.log (feketeNumber (star z₀ r) N) := by
        field_simp
      rw [hcancel] at hle
      nlinarith [hle]
    calc Real.log (feketeNumber (star z₀ r) N) * (2 / ((N : ℝ) * ((N : ℝ) - 1)))
        ≤ ((N : ℝ) ^ 2 * Real.log y / 4) * (2 / ((N : ℝ) * ((N : ℝ) - 1))) := by
          refine mul_le_mul_of_nonneg_right hlogN ?_
          positivity
      _ = (N : ℝ) / (2 * ((N : ℝ) - 1)) * Real.log y := by
          field_simp; ring
      _ ≤ Real.log y := by
          have hN2' : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN2
          have hle : (N : ℝ) / (2 * ((N : ℝ) - 1)) ≤ 1 := by
            rw [div_le_one (by positivity)]
            linarith
          exact mul_le_of_le_one_left hlogy.le hle
  refine le_of_forall_pos_le_add (fun ε hε => ?_)
  refine Filter.limsup_le_of_le (a := 1 + ε) ?_ ?_
  · refine ⟨0, fun a ha => ?_⟩
    obtain ⟨N, hN⟩ := (Filter.eventually_map.mp ha).exists
    exact le_trans (Real.rpow_nonneg (Submission.FeketeLim.feketeNumber_nonneg
      (star_nonempty (z₀ := z₀) (r := r) hs hunit hr)
      (Submission.ModelStarExterior.isCompact_modelStarImage z₀ r hunit hr).isBounded N) _) hN
  · filter_upwards [hbound (1 + ε) (by linarith)] with N hN
    linarith

end Submission.ModelStarN1
