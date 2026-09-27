import Mathlib
import Submission.Work.Mostow.BaryBase

/-!
# Uniform gap for atomless probability measures on the boundary sphere

Let `ν` be a probability measure on `E n = EuclideanSpace ℝ (Fin n)` carried by the unit sphere
`Sph n` and without atoms.  Then there is a *uniform* `δ > 0` such that for every `ŷ ∈ Sph n`
the "cap" `{ξ | 1 - inner ℝ ŷ ξ < δ}` around `ŷ` has `ν`-measure at most `1/4`, i.e. its
complement `{ξ | δ ≤ 1 - inner ℝ ŷ ξ}` has measure at least `3/4`.

This is the analytic input (BCG, "natural map" construction) that turns the absence of atoms of a
boundary measure into a *quantitative* bound, uniform over the sphere.

Why it is true.  The caps `C(ŷ, δ) = {ξ | 1 - inner ℝ ŷ ξ < δ}` shrink to the single point `ŷ`
as `δ → 0`.  Suppose no `δ` worked: then there were `δ_k → 0` and `ŷ_k ∈ Sph n` with
`ν (C(ŷ_k, δ_k)) > 1/4`.  The sphere is compact, so along a subsequence `ŷ_k → p ∈ Sph n`.  For
`ν`-almost every `x` (namely for `x ∈ Sph n`, `x ≠ p`) one has `1 - inner ℝ p x > 0` by strict
Cauchy–Schwarz on the sphere, hence eventually `δ_k < 1 - inner ℝ ŷ_k x`, i.e. `x ∉ C(ŷ_k, δ_k)`.
Thus the indicators of the `C(ŷ_k, δ_k)` converge `ν`-a.e. to the indicator of the null set `{p}`,
and `MeasureTheory.tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure` gives
`ν (C(ŷ_k, δ_k)) → ν {p} = 0`, contradicting `> 1/4`.
-/

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory Filter
open scoped Topology

namespace Work.Mostow

set_option linter.style.haveILetI false

noncomputable section

variable {n : ℕ}

/-- Strict Cauchy–Schwarz on the unit sphere: two distinct unit vectors have inner product `< 1`.
Indeed `1 - inner ℝ p x = ‖p - x‖² / 2`. -/
theorem inner_lt_one_of_mem_sphere {p x : E n} (hp : p ∈ Sph n) (hx : x ∈ Sph n) (hne : x ≠ p) :
    inner ℝ p x < 1 := by
  have hpn : ‖p‖ = 1 := (mem_Sph_iff p).mp hp
  have hxn : ‖x‖ = 1 := (mem_Sph_iff x).mp hx
  have hsq := norm_sub_sq_real p x
  rw [hpn, hxn] at hsq
  have hlt : 0 < ‖p - x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hne))
  nlinarith [hsq, hlt]

/-- If a cap `{ξ | 1 - inner ℝ ŷ ξ < δ}` has measure at most `1/4`, then its complement
`{ξ | δ ≤ 1 - inner ℝ ŷ ξ}` has measure at least `3/4`. -/
theorem capComplement_gap {ν : Measure (E n)} [IsProbabilityMeasure ν] {ŷ : E n} {δ : ℝ}
    (hcap : ν {ξ : E n | 1 - inner ℝ ŷ ξ < δ} ≤ ENNReal.ofReal (1/4)) :
    (3/4 : ℝ) ≤ (ν {ξ : E n | δ ≤ 1 - inner ℝ ŷ ξ}).toReal := by
  have hCmble : MeasurableSet {ξ : E n | 1 - inner ℝ ŷ ξ < δ} :=
    (isOpen_lt (by fun_prop) continuous_const).measurableSet
  have hset : {ξ : E n | δ ≤ 1 - inner ℝ ŷ ξ} = {ξ : E n | 1 - inner ℝ ŷ ξ < δ}ᶜ := by
    ext ξ; simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, not_lt]
  rw [hset]
  have hsum : ν {ξ : E n | 1 - inner ℝ ŷ ξ < δ} + ν {ξ : E n | 1 - inner ℝ ŷ ξ < δ}ᶜ = 1 := by
    rw [measure_add_measure_compl hCmble, measure_univ]
  have hCle : ν {ξ : E n | 1 - inner ℝ ŷ ξ < δ} ≤ 1 := by
    rw [← measure_univ (μ := ν)]; exact measure_mono (Set.subset_univ _)
  have hCcle : ν {ξ : E n | 1 - inner ℝ ŷ ξ < δ}ᶜ ≤ 1 := by
    rw [← measure_univ (μ := ν)]; exact measure_mono (Set.subset_univ _)
  have htR : (ν {ξ : E n | 1 - inner ℝ ŷ ξ < δ}).toReal
      + (ν {ξ : E n | 1 - inner ℝ ŷ ξ < δ}ᶜ).toReal = 1 := by
    rw [← ENNReal.toReal_add (ne_top_of_le_ne_top (by norm_num) hCle)
      (ne_top_of_le_ne_top (by norm_num) hCcle), hsum, ENNReal.toReal_one]
  have hCleR : (ν {ξ : E n | 1 - inner ℝ ŷ ξ < δ}).toReal ≤ 1/4 := by
    have h := ENNReal.toReal_mono (a := ν {ξ : E n | 1 - inner ℝ ŷ ξ < δ})
      (b := ENNReal.ofReal (1/4)) ENNReal.ofReal_ne_top hcap
    rwa [ENNReal.toReal_ofReal (by norm_num)] at h
  linarith

theorem UniformGap (n : ℕ) (ν : MeasureTheory.Measure (Submission.Mostow.E n))
    (hν : MeasureTheory.IsProbabilityMeasure ν) (hsupp : ν (Submission.Mostow.Sph n)ᶜ = 0)
    (hatom : ∀ ξ : Submission.Mostow.E n, ν {ξ} = 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ŷ ∈ Submission.Mostow.Sph n,
      (3/4 : ℝ) ≤ (ν {ξ : Submission.Mostow.E n | δ ≤ 1 - inner ℝ ŷ ξ}).toReal := by
  haveI : IsProbabilityMeasure ν := hν
  -- Step 1: a uniform `δ` for which every cap has measure at most `1/4`.
  have key : ∃ δ : ℝ, 0 < δ ∧ ∀ ŷ ∈ Sph n,
      ν {ξ : E n | 1 - inner ℝ ŷ ξ < δ} ≤ ENNReal.ofReal (1/4) := by
    by_contra h
    push Not at h
    have hδpos : ∀ k : ℕ, 0 < 1/(((k : ℕ) : ℝ) + 1) := fun k => by positivity
    choose ŷ hŷSph hŷbig using fun k => h (1/(((k : ℕ) : ℝ) + 1)) (hδpos k)
    -- compactness of the sphere: extract a convergent subsequence
    have hcomp : IsCompact (Sph n : Set (E n)) := by
      simpa [Sph] using isCompact_sphere (0 : E n) 1
    obtain ⟨p, hpSph, φ, hφmono, hφtend⟩ := hcomp.tendsto_subseq hŷSph
    have hy : Tendsto (fun k => ŷ (φ k)) atTop (𝓝 p) := hφtend
    have hδtend : Tendsto (fun k => 1/(((φ k : ℕ) : ℝ) + 1)) atTop (𝓝 0) :=
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp hφmono.tendsto_atTop
    -- the exceptional set (`Sph nᶜ` and `{p}`) is `ν`-null
    have hsupp_ae : ∀ᵐ x ∂ν, x ∈ Sph n := by rw [ae_iff]; exact hsupp
    have hne_ae : ∀ᵐ x ∂ν, x ≠ p := by
      rw [ae_iff]
      have hset : {x : E n | ¬ x ≠ p} = {p} := by ext x; simp
      rw [hset]; exact hatom p
    -- `ν`-a.e. the indicators of the caps converge to that of `{p}`
    have h_lim : ∀ᵐ x ∂ν, ∀ᶠ k in atTop,
        x ∈ {ξ : E n | 1 - inner ℝ (ŷ (φ k)) ξ < 1/(((φ k : ℕ) : ℝ) + 1)}
          ↔ x ∈ ({p} : Set (E n)) := by
      filter_upwards [hsupp_ae, hne_ae] with x hxSph hxne
      have hxpos : 0 < 1 - inner ℝ p x := by
        linarith [inner_lt_one_of_mem_sphere hpSph hxSph hxne]
      have hinner : Tendsto (fun k => inner ℝ (ŷ (φ k)) x) atTop (𝓝 (inner ℝ p x)) :=
        hy.inner tendsto_const_nhds
      have h1 : Tendsto (fun k => 1 - inner ℝ (ŷ (φ k)) x) atTop (𝓝 (1 - inner ℝ p x)) :=
        tendsto_const_nhds.sub hinner
      refine (hδtend.eventually_lt h1 hxpos).mono ?_
      intro k hk
      simp only [Set.mem_singleton_iff]
      exact ⟨fun hh => absurd hh (not_lt.mpr (le_of_lt hk)), fun hh => absurd hh hxne⟩
    have hAsmble : ∀ k, MeasurableSet
        {ξ : E n | 1 - inner ℝ (ŷ (φ k)) ξ < 1/(((φ k : ℕ) : ℝ) + 1)} :=
      fun k => (isOpen_lt (by fun_prop) continuous_const).measurableSet
    have hlim : Tendsto
        (fun k => ν {ξ : E n | 1 - inner ℝ (ŷ (φ k)) ξ < 1/(((φ k : ℕ) : ℝ) + 1)})
        atTop (𝓝 (ν {p})) :=
      tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure atTop
        (measurableSet_singleton p) hAsmble h_lim
    have hlim0 : Tendsto
        (fun k => ν {ξ : E n | 1 - inner ℝ (ŷ (φ k)) ξ < 1/(((φ k : ℕ) : ℝ) + 1)})
        atTop (𝓝 0) := by simpa [hatom p] using hlim
    have hlt : ∀ᶠ k in atTop,
        ν {ξ : E n | 1 - inner ℝ (ŷ (φ k)) ξ < 1/(((φ k : ℕ) : ℝ) + 1)}
          < ENNReal.ofReal (1/4) :=
      hlim0.eventually_lt tendsto_const_nhds (by rw [ENNReal.ofReal_pos]; norm_num)
    obtain ⟨k, hk⟩ := hlt.exists
    exact absurd (lt_trans (hŷbig (φ k)) hk) (lt_irrefl _)
  -- Step 2: complement the cap bound.
  obtain ⟨δ, hδ, hcap⟩ := key
  exact ⟨δ, hδ, fun ŷ hŷ => capComplement_gap (hcap ŷ hŷ)⟩

end

end Work.Mostow
