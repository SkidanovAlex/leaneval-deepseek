import Mathlib
import Submission.Work.ParamRaysCrit.CritDomain
import Submission.Work.ParamRays.greenSeq_tendsto_greenFun

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Filter
open scoped Real Topology ComplexConjugate

/-!
# The modulus of a critical Böttcher coordinate

`Work.ParamRays.IsCritBottcher c φ` is the parameter-plane Böttcher coordinate of
`T_c(z) = z̄² + c`, defined on the critical domain `critDomain c = {G_c > G_c 0}`.  This file
proves that its modulus is the exponential of the Green function,

`‖φ z‖ = exp (G_c z)`  for `z ∈ critDomain c`,

the parameter-plane analogue of `Work.ParamRays.IsDynBottcher_modulus`.  The whole argument is
the dynamical one with `Escaping c z` replaced by `z ∈ critDomain c` (the critical domain is
`T_c`-invariant and contained in the escaping set) and `IsDynBottcher` by `IsCritBottcher`:

* `IsCritBottcher.functional_iterate` : `φ (T_c^[2n] z) = φ z ^ (4^n)`,
* `IsCritBottcher_norm_div` : `‖φ (T_c^n z)‖ / ‖T_c^n z‖ → 1`,
* `IsCritBottcher.ne_zero` : `φ z ≠ 0`,
* `IsCritBottcher_modulus` : the main statement.
-/

namespace Work.ParamRays

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-- **Iterated Böttcher equation on the critical domain.**  Along the even iterates the
Böttcher relation `φ (T_c w) = conj (φ w)^2` gives `φ (T_c^{2n} z) = φ z ^ (4^n)`.  The orbit of
`z ∈ critDomain c` stays in `critDomain c` (`orbit_mem_critDomain`), so the equation may be
applied at every step. -/
theorem IsCritBottcher.functional_iterate {c : ℂ} {φ : ℂ → ℂ} (h : IsCritBottcher c φ)
    {z : ℂ} (hz : z ∈ critDomain c) (n : ℕ) :
    φ (orbit c z (2 * n)) = φ z ^ (4 ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hw : orbit c z (2 * n) ∈ critDomain c := orbit_mem_critDomain hz (2 * n)
    have hw1 : orbit c z (2 * n + 1) ∈ critDomain c := orbit_mem_critDomain hz (2 * n + 1)
    have e1 : orbit c z (2 * n + 1) = Tantibar c (orbit c z (2 * n)) := orbit_succ c z (2 * n)
    have e2 : orbit c z (2 * (n + 1)) = Tantibar c (orbit c z (2 * n + 1)) := by
      rw [show 2 * (n + 1) = 2 * n + 1 + 1 from by ring]
      exact orbit_succ c z (2 * n + 1)
    rw [e2, h.2.1 _ hw1, e1, h.2.1 _ hw, ih, conj_sq_sq, ← pow_mul, pow_succ]

/-- **A critical Böttcher coordinate is asymptotic to the identity along a critical orbit.**
If `φ` is a critical Böttcher coordinate and `z ∈ critDomain c`, then the orbit of `z` leaves
every compact set (since `critDomain c ⊆ escapingSet c`), so the third clause of
`IsCritBottcher` applies to the orbit points and the ratios `‖φ w‖ / ‖w‖` tend to `1`. -/
theorem IsCritBottcher_norm_div {c : ℂ} {φ : ℂ → ℂ} (h : IsCritBottcher c φ)
    {z : ℂ} (hz : z ∈ critDomain c) :
    Filter.Tendsto (fun n : ℕ => ‖φ (orbit c z n)‖ / ‖orbit c z n‖)
      Filter.atTop (nhds 1) := by
  have hzE : Escaping c z := critDomain_subset_escapingSet c hz
  have hz' : Filter.Tendsto (fun n : ℕ => ‖orbit c z n‖) Filter.atTop Filter.atTop := hzE
  -- an escaping orbit leaves every compact set
  have hcoc : Filter.Tendsto (fun n : ℕ => orbit c z n) Filter.atTop
      (Filter.cocompact ℂ) :=
    tendsto_cocompact_of_tendsto_dist_comp_atTop 0 (by simpa [dist_zero_right] using hz')
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hε2 : 0 < ε / 2 := by linarith
  -- the asymptotic clause of the Böttcher coordinate, evaluated along the orbit
  have hP : ∀ᶠ w : ℂ in Filter.cocompact ℂ, ‖φ w - w‖ ≤ ε / 2 * ‖w‖ := h.2.2 (ε / 2) hε2
  have hev : ∀ᶠ n : ℕ in Filter.atTop,
      ‖φ (orbit c z n) - orbit c z n‖ ≤ ε / 2 * ‖orbit c z n‖ := hcoc.eventually hP
  -- eventually the orbit point is far from the origin, so we may divide by its norm
  have hbig : ∀ᶠ n : ℕ in Filter.atTop, (1 : ℝ) ≤ ‖orbit c z n‖ :=
    hz'.eventually_ge_atTop 1
  filter_upwards [hev, hbig] with n hn hb
  have hbpos : 0 < ‖orbit c z n‖ := lt_of_lt_of_le zero_lt_one hb
  have hdiff : |‖φ (orbit c z n)‖ - ‖orbit c z n‖| ≤ ε / 2 * ‖orbit c z n‖ :=
    le_trans (abs_norm_sub_norm_le _ _) hn
  rw [Real.dist_eq, div_sub_one (ne_of_gt hbpos), abs_div, abs_of_pos hbpos,
    div_lt_iff₀ hbpos]
  nlinarith [hdiff, hbpos, hε]

/-- **A critical Böttcher coordinate does not vanish.**  If `ψ z = 0` for some `z ∈ critDomain c`
then the Böttcher equation forces `ψ` to be identically `0` along the whole orbit of `z`, which
however leaves every compact set and on which `‖ψ w - w‖ ≤ (1/2)‖w‖`; that forces `ψ (T_c^n z)`
to be nonzero. -/
theorem IsCritBottcher.ne_zero {c : ℂ} {ψ : ℂ → ℂ} (hψ : IsCritBottcher c ψ) {z : ℂ}
    (hz : z ∈ critDomain c) : ψ z ≠ 0 := by
  intro hz0
  have hzero : ∀ n : ℕ, ψ (orbit c z n) = 0 := by
    intro n
    induction n with
    | zero => simpa using hz0
    | succ n ih =>
      rw [orbit_succ, hψ.2.1 (orbit c z n) (orbit_mem_critDomain hz n), ih]
      simp
  have hzE : Escaping c z := critDomain_subset_escapingSet c hz
  have hcoc : Tendsto (fun n : ℕ => orbit c z n) atTop (cocompact ℂ) :=
    tendsto_cocompact_of_tendsto_dist_comp_atTop 0 (by
      show Tendsto (fun n : ℕ => dist (orbit c z n) 0) atTop atTop
      rw [show (fun n : ℕ => dist (orbit c z n) 0) = fun n : ℕ => ‖orbit c z n‖ from by
        funext n; rw [dist_zero_right]]
      exact hzE)
  have h2 : ∀ᶠ w : ℂ in cocompact ℂ, ‖ψ w - w‖ ≤ (1 / 2) * ‖w‖ := hψ.2.2 (1 / 2) (by norm_num)
  have h3 : ∀ᶠ n : ℕ in atTop, ‖ψ (orbit c z n) - orbit c z n‖ ≤ (1 / 2) * ‖orbit c z n‖ :=
    hcoc.eventually h2
  have h4 : ∀ᶠ n : ℕ in atTop, 0 < ‖orbit c z n‖ := Escaping.eventually_gt hzE 0
  obtain ⟨n, hn1, hn2⟩ := (h3.and h4).exists
  have hineq : ‖orbit c z n‖ ≤ ‖ψ (orbit c z n)‖ + (1 / 2) * ‖orbit c z n‖ := by
    have hsum : ψ (orbit c z n) + (orbit c z n - ψ (orbit c z n)) = orbit c z n := by ring
    calc ‖orbit c z n‖ = ‖ψ (orbit c z n) + (orbit c z n - ψ (orbit c z n))‖ := by rw [hsum]
      _ ≤ ‖ψ (orbit c z n)‖ + ‖orbit c z n - ψ (orbit c z n)‖ := norm_add_le _ _
      _ = ‖ψ (orbit c z n)‖ + ‖ψ (orbit c z n) - orbit c z n‖ := by rw [norm_sub_rev]
      _ ≤ ‖ψ (orbit c z n)‖ + (1 / 2) * ‖orbit c z n‖ := by linarith
  have hpos : 0 < ‖ψ (orbit c z n)‖ := by linarith
  rw [hzero n] at hpos
  simp at hpos

end Work.ParamRays

namespace Work.ParamRaysCrit.CritBottcher

/-- The modulus of a critical Böttcher coordinate is the exponential of the Green function. This is the parameter-plane analogue of `Work.ParamRays.IsDynBottcher_modulus`: copy that proof (and the proofs of `IsDynBottcher.functional_iterate`, `IsDynBottcher_norm_div`, `IsDynBottcher.ne_zero` in `Submission/Work/ParamRays/`), replacing `Escaping c z` by `z ∈ critDomain c` (`Work.ParamRays.critDomain_subset_escapingSet`, `Work.ParamRays.orbit_mem_critDomain`) and `IsDynBottcher` by `IsCritBottcher`. -/
theorem IsCritBottcher_modulus {c : ℂ} {φ : ℂ → ℂ} (h : Work.ParamRays.IsCritBottcher c φ)
    {z : ℂ} (hz : z ∈ Work.ParamRays.critDomain c) :
    ‖φ z‖ = Real.exp (Work.ParamRays.greenFun c z) := by
  have hzE : Work.ParamRays.Escaping c z := Work.ParamRays.critDomain_subset_escapingSet c hz
  -- the even-indexed orbit points, and the ratio of the `φ`-image to the point
  have h2n : Tendsto (fun n : ℕ => 2 * n) atTop atTop :=
    tendsto_atTop_atTop.mpr (fun b =>
      ⟨b, fun a ha => le_trans ha (Nat.le_mul_of_pos_left a (by norm_num))⟩)
  -- the whole sequence converges to the Green function
  have hconv := Work.ParamRays.greenSeq_tendsto_greenFun c z hzE
  -- `‖φ (T_c^[2n] z)‖ / ‖T_c^[2n] z‖ → 1`
  have hratio : Tendsto (fun n : ℕ =>
      ‖φ (Work.ParamRays.orbit c z (2*n))‖ / ‖Work.ParamRays.orbit c z (2*n)‖)
      atTop (nhds 1) := (Work.ParamRays.IsCritBottcher_norm_div h hz).comp h2n
  have hlogr : Tendsto (fun n : ℕ =>
      Real.log (‖φ (Work.ParamRays.orbit c z (2*n))‖ / ‖Work.ParamRays.orbit c z (2*n)‖))
      atTop (nhds 0) := by
    have h1 := hratio.log (by norm_num : (1 : ℝ) ≠ 0)
    simpa using h1
  have hinv4 : Tendsto (fun n : ℕ => ((4 : ℝ) ^ n)⁻¹) atTop (nhds 0) :=
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 4)).inv_tendsto_atTop
  have hprod : Tendsto (fun n : ℕ =>
      ((4 : ℝ) ^ n)⁻¹ * Real.log (‖φ (Work.ParamRays.orbit c z (2*n))‖ /
        ‖Work.ParamRays.orbit c z (2*n)‖))
      atTop (nhds 0) := by
    simpa using hinv4.mul hlogr
  -- large orbits and positive `φ`-images
  have hden : ∀ᶠ n : ℕ in atTop, (1 : ℝ) ≤ ‖Work.ParamRays.orbit c z (2*n)‖ := by
    have h := h2n.eventually (hzE.eventually_gt 1)
    filter_upwards [h] with n hn using le_of_lt hn
  have hrat1 : ∀ᶠ n : ℕ in atTop,
      (1/2 : ℝ) ≤ ‖φ (Work.ParamRays.orbit c z (2*n))‖ / ‖Work.ParamRays.orbit c z (2*n)‖ :=
    hratio.eventually (eventually_ge_nhds (by norm_num : (1/2 : ℝ) < 1))
  have hnum : ∀ᶠ n : ℕ in atTop, 0 < ‖φ (Work.ParamRays.orbit c z (2*n))‖ := by
    filter_upwards [hrat1, hden] with n hn hd
    have hdpos : 0 < ‖Work.ParamRays.orbit c z (2*n)‖ := by linarith
    have h3 : 0 < (‖φ (Work.ParamRays.orbit c z (2*n))‖ / ‖Work.ParamRays.orbit c z (2*n)‖) *
        ‖Work.ParamRays.orbit c z (2*n)‖ :=
      mul_pos (by linarith) hdpos
    rwa [div_mul_cancel₀ _ (ne_of_gt hdpos)] at h3
  -- the key asymptotic identity for the even subsequence of `greenSeq`
  have hkey : ∀ᶠ n : ℕ in atTop, Work.ParamRays.greenSeq c z (2*n) =
      Real.log ‖φ z‖ -
        ((4 : ℝ) ^ n)⁻¹ * Real.log (‖φ (Work.ParamRays.orbit c z (2*n))‖ /
          ‖Work.ParamRays.orbit c z (2*n)‖) := by
    filter_upwards [hden, hnum] with n hdenn hnumn
    have hdne : ‖Work.ParamRays.orbit c z (2*n)‖ ≠ 0 := by
      have : (0 : ℝ) < ‖Work.ParamRays.orbit c z (2*n)‖ := by linarith
      exact ne_of_gt this
    have hnumne : ‖φ (Work.ParamRays.orbit c z (2*n))‖ ≠ 0 := ne_of_gt hnumn
    have hfun : ‖φ (Work.ParamRays.orbit c z (2*n))‖ = ‖φ z‖ ^ (4^n) := by
      rw [Work.ParamRays.IsCritBottcher.functional_iterate h hz n, norm_pow]
    have hlognum : Real.log ‖φ (Work.ParamRays.orbit c z (2*n))‖ =
        (4 : ℝ)^n * Real.log ‖φ z‖ := by
      rw [hfun, Real.log_pow, Nat.cast_pow]
      norm_num
    have hlogden : Real.log ‖Work.ParamRays.orbit c z (2*n)‖ =
        Real.log ‖φ (Work.ParamRays.orbit c z (2*n))‖ -
        Real.log (‖φ (Work.ParamRays.orbit c z (2*n))‖ /
          ‖Work.ParamRays.orbit c z (2*n)‖) := by
      have h := Real.log_div hnumne hdne
      linarith
    have hpow : ((2 : ℝ) ^ (2*n))⁻¹ = ((4 : ℝ) ^ n)⁻¹ := by
      rw [pow_mul]; norm_num
    rw [Work.ParamRays.greenSeq, hpow,
      Real.posLog_eq_log (by rw [abs_of_nonneg (norm_nonneg _)]; exact hdenn),
      hlogden, hlognum]
    field_simp
  have heven : Tendsto (fun n : ℕ => Work.ParamRays.greenSeq c z (2*n)) atTop
      (nhds (Real.log ‖φ z‖)) := by
    have h1 : Tendsto (fun n : ℕ => Real.log ‖φ z‖ -
        ((4 : ℝ) ^ n)⁻¹ * Real.log (‖φ (Work.ParamRays.orbit c z (2*n))‖ /
          ‖Work.ParamRays.orbit c z (2*n)‖))
        atTop (nhds (Real.log ‖φ z‖ - 0)) := tendsto_const_nhds.sub hprod
    simpa using h1.congr' (Filter.EventuallyEq.symm hkey)
  have hsub : Tendsto (fun n : ℕ => Work.ParamRays.greenSeq c z (2*n)) atTop
      (nhds (Work.ParamRays.greenFun c z)) := hconv.comp h2n
  -- the Green function is `log ‖φ z‖`
  have hEq : Work.ParamRays.greenFun c z = Real.log ‖φ z‖ := tendsto_nhds_unique hsub heven
  have hpos : 0 < ‖φ z‖ := by
    obtain ⟨n, hn⟩ := hnum.exists
    have hfun0 : ‖φ (Work.ParamRays.orbit c z (2*n))‖ = ‖φ z‖ ^ (4^n) := by
      rw [Work.ParamRays.IsCritBottcher.functional_iterate h hz n, norm_pow]
    have h1 : 0 < ‖φ z‖ ^ (4^n) := by rwa [hfun0] at hn
    have hx0 : ‖φ z‖ ≠ 0 := by
      intro hzero
      rw [hzero, zero_pow (by positivity : 4^n ≠ 0)] at h1
      exact absurd h1 (lt_irrefl 0)
    exact lt_of_le_of_ne (norm_nonneg _) (Ne.symm hx0)
  rw [hEq, Real.exp_log hpos]

end Work.ParamRaysCrit.CritBottcher
