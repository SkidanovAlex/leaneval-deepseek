import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Local monotonicity of `t ↦ ‖u t - u t₀‖` at a point with nonvanishing derivative

`Work.ELRig.Mono.local_mono_norm`: if `u : ℝ → ℂ` has `deriv u t₀ = a ≠ 0`, is differentiable
near `t₀`, and `deriv u` is continuous at `t₀`, then on a one-sided neighbourhood of `t₀` the
function `t ↦ ‖u t - u t₀‖` is strictly increasing on `[t₀, t₀+δ]` and strictly decreasing on
`[t₀-δ, t₀]`.

The proof is the honest mean-value / first-order argument, with no analyticity needed:

* `first_order_bound` extracts the expansion `‖u t - u t₀ - a (t - t₀)‖ ≤ η |t - t₀|` from
  differentiability of `u` at `t₀` (via `hasDerivAt_iff_isLittleO_nhds_zero`);
* `deriv_close` records the continuity of `deriv u` at `t₀` in the form `‖deriv u t - a‖ ≤ η`;
* `normSq_deriv_sign` turns the two estimates into the sign of the derivative of
  `t ↦ ‖u t - u t₀‖²` on the two sides of `t₀`, via `HasDerivAt.norm_sq`;
* `strictMonoOn_of_deriv_pos` / `strictAntiOn_of_deriv_neg` upgrade this to the monotonicity of
  the squared norm, and `Real.sqrt_lt_sqrt` (with `‖·‖ ≥ 0`) transfers it to the norm itself.

Note that the hypothesis `hne : ∀ᶠ t in 𝓝[{t₀}ᶜ] t₀, u t ≠ u t₀` of the statement is not needed:
it follows from the conclusion (`‖u t - u t₀‖ > ‖u t₀ - u t₀‖ = 0` for `t > t₀` close to `t₀`).
-/

namespace Work.ELRig.Mono

open Filter Topology

/-- The norm on `ℂ` of a real number. -/
private lemma norm_ofReal (r : ℝ) : ‖(r : ℂ)‖ = |r| := by
  rw [← Real.norm_eq_abs, ← Complex.ofRealLI.norm_map r]; rfl

/-- A radius on which `u` is differentiable at every point, from differentiability near `t₀`. -/
private lemma diff_near {u : ℝ → ℂ} {t₀ : ℝ}
    (hdiff : ∀ᶠ t in nhds t₀, DifferentiableAt ℝ u t) :
    ∃ δ > 0, ∀ t, |t - t₀| < δ → DifferentiableAt ℝ u t := by
  rw [Metric.eventually_nhds_iff] at hdiff
  obtain ⟨δ, hδ, hh⟩ := hdiff
  exact ⟨δ, hδ, fun t ht => hh (by rwa [Real.dist_eq])⟩

/-- First order expansion of `u` at `t₀` (centred form), from `u` differentiable at `t₀`. -/
private lemma first_order_bound {u : ℝ → ℂ} {t₀ : ℝ} {a : ℂ}
    (hdiff : ∀ᶠ t in nhds t₀, DifferentiableAt ℝ u t) (hd : deriv u t₀ = a)
    (η : ℝ) (hη : 0 < η) :
    ∃ δ > 0, ∀ t : ℝ, |t - t₀| < δ →
      ‖u t - u t₀ - a * ((t - t₀ : ℝ) : ℂ)‖ ≤ η * |t - t₀| := by
  have hdt₀ : DifferentiableAt ℝ u t₀ := hdiff.self_of_nhds
  have hderiv : HasDerivAt u a t₀ := by rw [← hd]; exact hdt₀.hasDerivAt
  rw [hasDerivAt_iff_isLittleO_nhds_zero] at hderiv
  rw [Asymptotics.isLittleO_iff] at hderiv
  have h := hderiv hη
  rw [Metric.eventually_nhds_iff] at h
  obtain ⟨δ, hδ, hh⟩ := h
  refine ⟨δ, hδ, fun t ht => ?_⟩
  have hh' := hh (show dist (t - t₀) 0 < δ by rw [Real.dist_eq, sub_zero]; exact ht)
  have hsl : (t - t₀) • a = a * ((t - t₀ : ℝ) : ℂ) := by
    rw [Complex.real_smul, mul_comm]
  have harg : t₀ + (t - t₀) = t := by ring
  rw [Real.norm_eq_abs, harg, hsl] at hh'
  exact hh'

/-- Continuity of `deriv u` at `t₀` with value `a`, in quantitative form. -/
private lemma deriv_close {u : ℝ → ℂ} {t₀ : ℝ} {a : ℂ}
    (hcont : ContinuousAt (deriv u) t₀) (hd : deriv u t₀ = a) (η : ℝ) (hη : 0 < η) :
    ∃ δ > 0, ∀ t : ℝ, |t - t₀| < δ → ‖deriv u t - a‖ ≤ η := by
  have h := Metric.tendsto_nhds.mp hcont η hη
  rw [Metric.eventually_nhds_iff] at h
  obtain ⟨δ, hδ, hh⟩ := h
  refine ⟨δ, hδ, fun t ht => ?_⟩
  have hh' := hh (show dist t t₀ < δ by rwa [Real.dist_eq])
  rw [dist_eq_norm, hd] at hh'
  exact le_of_lt hh'

/-- The core sign computation: from the first order estimates around the nonvanishing value `a`,
the derivative of `t ↦ ‖u t - u t₀‖²` is positive on `(t₀, t₀+δ)` and negative on
`(t₀-δ, t₀)`. -/
private lemma normSq_deriv_sign {u : ℝ → ℂ} {t₀ : ℝ} {a : ℂ} {δ η : ℝ}
    (hη : 0 < η) (hineq : 2 * ‖a‖ * η + η ^ 2 < ‖a‖ ^ 2)
    (hdiff : ∀ t : ℝ, |t - t₀| < δ → DifferentiableAt ℝ u t)
    (h1 : ∀ t : ℝ, |t - t₀| < δ → ‖u t - u t₀ - a * ((t - t₀ : ℝ) : ℂ)‖ ≤ η * |t - t₀|)
    (h2 : ∀ t : ℝ, |t - t₀| < δ → ‖deriv u t - a‖ ≤ η) :
    (∀ t ∈ Set.Ioo t₀ (t₀ + δ), 0 < deriv (fun s : ℝ => ‖u s - u t₀‖ ^ 2) t) ∧
    (∀ t ∈ Set.Ioo (t₀ - δ) t₀, deriv (fun s : ℝ => ‖u s - u t₀‖ ^ 2) t < 0) := by
  have hderiv : ∀ t, |t - t₀| < δ →
      deriv (fun s : ℝ => ‖u s - u t₀‖ ^ 2) t = 2 * inner ℝ (u t - u t₀) (deriv u t) := by
    intro t ht
    exact (((hdiff t ht).hasDerivAt.sub_const (u t₀)).norm_sq).deriv
  have hcore : ∀ t, |t - t₀| < δ →
      |inner ℝ (u t - u t₀) (deriv u t) - (t - t₀) * ‖a‖ ^ 2|
        ≤ (2 * ‖a‖ * η + η ^ 2) * |t - t₀| := by
    intro t ht
    set E : ℂ := u t - u t₀ - a * ((t - t₀ : ℝ) : ℂ) with hE
    set e : ℂ := deriv u t - a with he
    have hft : u t - u t₀ = a * ((t - t₀ : ℝ) : ℂ) + E := by rw [hE]; ring
    have hdt : deriv u t = a + e := by rw [he]; ring
    have hEbound : ‖E‖ ≤ η * |t - t₀| := by rw [hE]; exact h1 t ht
    have hebound : ‖e‖ ≤ η := by rw [he]; exact h2 t ht
    have hsmul : a * ((t - t₀ : ℝ) : ℂ) = (t - t₀) • a := by
      rw [Complex.real_smul, mul_comm]
    have hkey : inner ℝ (u t - u t₀) (deriv u t)
        = (t - t₀) * ‖a‖ ^ 2 + inner ℝ (a * ((t - t₀ : ℝ) : ℂ)) e
          + inner ℝ E a + inner ℝ E e := by
      have hself : inner ℝ (a * ((t - t₀ : ℝ) : ℂ)) a = (t - t₀) * ‖a‖ ^ 2 := by
        rw [hsmul, real_inner_smul_left, real_inner_self_eq_norm_sq]
      rw [hft, hdt, inner_add_left, inner_add_right, inner_add_right, hself]
      ring
    have hAB : |inner ℝ (a * ((t - t₀ : ℝ) : ℂ)) e| ≤ ‖a‖ * |t - t₀| * η := by
      have h1' : ‖a * ((t - t₀ : ℝ) : ℂ)‖ = ‖a‖ * |t - t₀| := by
        rw [norm_mul, norm_ofReal]
      calc |inner ℝ (a * ((t - t₀ : ℝ) : ℂ)) e|
            ≤ ‖a * ((t - t₀ : ℝ) : ℂ)‖ * ‖e‖ := abs_real_inner_le_norm _ _
        _ = ‖a‖ * |t - t₀| * ‖e‖ := by rw [h1']
        _ ≤ ‖a‖ * |t - t₀| * η := mul_le_mul_of_nonneg_left hebound (by positivity)
    have hB : |inner ℝ E a| ≤ η * |t - t₀| * ‖a‖ := by
      calc |inner ℝ E a| ≤ ‖E‖ * ‖a‖ := abs_real_inner_le_norm _ _
        _ ≤ η * |t - t₀| * ‖a‖ := mul_le_mul_of_nonneg_right hEbound (norm_nonneg a)
    have hC : |inner ℝ E e| ≤ η * |t - t₀| * η := by
      calc |inner ℝ E e| ≤ ‖E‖ * ‖e‖ := abs_real_inner_le_norm _ _
        _ ≤ η * |t - t₀| * η := mul_le_mul hEbound hebound (norm_nonneg _) (by positivity)
    have hsum : |inner ℝ (a * ((t - t₀ : ℝ) : ℂ)) e + inner ℝ E a + inner ℝ E e|
        ≤ (2 * ‖a‖ * η + η ^ 2) * |t - t₀| := by
      refine (abs_add_three _ _ _).trans ?_
      have hthis : ‖a‖ * |t - t₀| * η + η * |t - t₀| * ‖a‖ + η * |t - t₀| * η
          = (2 * ‖a‖ * η + η ^ 2) * |t - t₀| := by ring
      linarith [hAB, hB, hC, hthis.le, hthis.ge]
    have hfin : inner ℝ (u t - u t₀) (deriv u t) - (t - t₀) * ‖a‖ ^ 2
        = inner ℝ (a * ((t - t₀ : ℝ) : ℂ)) e + inner ℝ E a + inner ℝ E e := by
      rw [hkey]; ring
    rw [hfin]; exact hsum
  constructor
  · intro t ht
    have htabs : |t - t₀| < δ := by
      rw [abs_of_pos (by linarith [ht.1] : (0 : ℝ) < t - t₀)]; linarith [ht.2]
    rw [hderiv t htabs]
    have hlow := (abs_le.mp (hcore t htabs)).1
    have hpos : 0 < inner ℝ (u t - u t₀) (deriv u t) := by
      rw [abs_of_pos (by linarith [ht.1] : (0 : ℝ) < t - t₀)] at hlow
      nlinarith [hineq, (by linarith [ht.1] : (0 : ℝ) < t - t₀), hlow]
    linarith
  · intro t ht
    have htabs : |t - t₀| < δ := by
      rw [abs_of_neg (by linarith [ht.2] : t - t₀ < 0)]; linarith [ht.1]
    rw [hderiv t htabs]
    have hup := (abs_le.mp (hcore t htabs)).2
    have hneg : inner ℝ (u t - u t₀) (deriv u t) < 0 := by
      rw [abs_of_neg (by linarith [ht.2] : t - t₀ < 0)] at hup
      nlinarith [hineq, (by linarith [ht.2] : t - t₀ < 0), hup]
    linarith

theorem local_mono_norm {u : ℝ → ℂ} {t₀ : ℝ} {a : ℂ} (ha : a ≠ 0)
    (hd : deriv u t₀ = a) (hdiff : ∀ᶠ t in nhds t₀, DifferentiableAt ℝ u t)
    (hcont : ContinuousAt (deriv u) t₀)
    (hne : ∀ᶠ t in nhdsWithin t₀ {t₀}ᶜ, u t ≠ u t₀) :
    ∃ δ > 0, StrictMonoOn (fun t : ℝ => ‖u t - u t₀‖) (Set.Icc t₀ (t₀ + δ)) ∧
      StrictAntiOn (fun t : ℝ => ‖u t - u t₀‖) (Set.Icc (t₀ - δ) t₀) := by
  have hapos : 0 < ‖a‖ := norm_pos_iff.mpr ha
  set η : ℝ := ‖a‖ / 8 with hηdef
  have hη : 0 < η := by rw [hηdef]; linarith
  have hineq : 2 * ‖a‖ * η + η ^ 2 < ‖a‖ ^ 2 := by rw [hηdef]; nlinarith [hapos]
  obtain ⟨δ₁, hδ₁, hd1⟩ := diff_near hdiff
  obtain ⟨δ₂, hδ₂, h2⟩ := deriv_close hcont hd η hη
  obtain ⟨δ₃, hδ₃, h1⟩ := first_order_bound hdiff hd η hη
  set δ : ℝ := min (min (δ₁ / 2) δ₂) δ₃ with hδdef
  have hδ : 0 < δ := by rw [hδdef]; exact lt_min (lt_min (by linarith) hδ₂) hδ₃
  have hδ1 : δ ≤ δ₁ / 2 := by rw [hδdef]; exact le_trans (min_le_left _ _) (min_le_left _ _)
  have hδ2 : δ ≤ δ₂ := by rw [hδdef]; exact le_trans (min_le_left _ _) (min_le_right _ _)
  have hδ3 : δ ≤ δ₃ := by rw [hδdef]; exact min_le_right _ _
  have hδδ1 : δ < δ₁ := by linarith [hδ1, hδ₁]
  have hdiffδ : ∀ t, |t - t₀| < δ → DifferentiableAt ℝ u t :=
    fun t ht => hd1 t (lt_of_lt_of_le ht hδδ1.le)
  have h1δ : ∀ t, |t - t₀| < δ →
      ‖u t - u t₀ - a * ((t - t₀ : ℝ) : ℂ)‖ ≤ η * |t - t₀| :=
    fun t ht => h1 t (lt_of_lt_of_le ht hδ3)
  have h2δ : ∀ t, |t - t₀| < δ → ‖deriv u t - a‖ ≤ η :=
    fun t ht => h2 t (lt_of_lt_of_le ht hδ2)
  obtain ⟨hposd, hnegd⟩ := normSq_deriv_sign hη hineq hdiffδ h1δ h2δ
  have hcont_u : ContinuousOn (fun t : ℝ => u t - u t₀) (Set.Icc (t₀ - δ) (t₀ + δ)) := by
    intro x hx
    have hxabs : |x - t₀| < δ₁ := by
      have h1 : |x - t₀| ≤ δ := abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩
      linarith [hδδ1]
    exact ((hd1 x hxabs).continuousAt.sub continuousAt_const).continuousWithinAt
  have hcont_g : ContinuousOn (fun t : ℝ => ‖u t - u t₀‖ ^ 2) (Set.Icc (t₀ - δ) (t₀ + δ)) :=
    hcont_u.norm.pow 2
  have hmonoSq : StrictMonoOn (fun t : ℝ => ‖u t - u t₀‖ ^ 2) (Set.Icc t₀ (t₀ + δ)) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc t₀ (t₀ + δ))
    · exact hcont_g.mono (Set.Icc_subset_Icc (by linarith) le_rfl)
    · intro x hx
      rw [interior_Icc] at hx
      exact hposd x hx
  have hantiSq : StrictAntiOn (fun t : ℝ => ‖u t - u t₀‖ ^ 2) (Set.Icc (t₀ - δ) t₀) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc (t₀ - δ) t₀)
    · exact hcont_g.mono (Set.Icc_subset_Icc le_rfl (by linarith))
    · intro x hx
      rw [interior_Icc] at hx
      exact hnegd x hx
  refine ⟨δ, hδ, ?_, ?_⟩
  · intro x hx y hy hxy
    change ‖u x - u t₀‖ < ‖u y - u t₀‖
    have hsq : ‖u x - u t₀‖ ^ 2 < ‖u y - u t₀‖ ^ 2 := hmonoSq hx hy hxy
    rw [← Real.sqrt_sq (norm_nonneg (u x - u t₀)), ← Real.sqrt_sq (norm_nonneg (u y - u t₀))]
    exact Real.sqrt_lt_sqrt (by positivity) hsq
  · intro x hx y hy hxy
    change ‖u y - u t₀‖ < ‖u x - u t₀‖
    have hsq : ‖u y - u t₀‖ ^ 2 < ‖u x - u t₀‖ ^ 2 := hantiSq hx hy hxy
    rw [← Real.sqrt_sq (norm_nonneg (u y - u t₀)), ← Real.sqrt_sq (norm_nonneg (u x - u t₀))]
    exact Real.sqrt_lt_sqrt (by positivity) hsq

end Work.ELRig.Mono
