import Mathlib
import Submission.Work.OddRadon.Chapter
import Submission.Work.OddCurve.Inv.radonProfile_radonInvData
import Submission.Work.OddRadon.abelTrans_hasDerivAt_direct

/-!
# The right-inverse half of the odd-dimensional Abel inversion, for the Radon datum

Target: `Work.OddRadon.abelTrans_radonInverse_eq_abelDatum`.

`radonInverse n F = abelInvert (abelReduceIter ((n:ℝ)-3/2) (n-1) (abelDatum n F))`, and
`abelDatum n F c = (2 |S^{2n-2}|)⁻¹ c^{2n-2} F c` vanishes to order `2(n-1)` at `0`.  Writing
`k = n-1`, `α = k - 1/2`, `K = abelDatum n F`, `Φ = R^k K` (the `k`-fold exponent reduction) and
`γ = abelInvert Φ`, the target is

  `T_α γ c = K c`   for `c ∈ (0,1)`.

The proof has three ingredients.

* **The base case at exponent `-1/2`** (`RI.abelTrans_neg_half_abelInvert`, namespace `RI` below):
  for a globally smooth `Ψ`, `T_{-1/2} (abelInvert Ψ) = Ψ` on `(0,1)`.  This is the classical Abel
  inversion.  The copy in `RI` is a verbatim adaptation of the proof of
  `Submission.Work.OddRadon.radonProfile_radonInverse` (which cannot be imported here: that file
  also declares the present target, with a `sorry`), with the regularity hypothesis weakened from
  `C^∞` to `C²` so that it can be fed the finitely-smooth extension of the datum.
* **The reduced datum of an extension.**  `K` extends to a globally smooth `Kx` by replacing `F`
  with a global `C^M` extension; the iterated reductions `R^j Kx` are then the explicit
  `c^{2(k-j)}` multiples of a smooth coefficient (`redCoef`), which gives both a global smooth
  representative `Ψ0` of `Φ` and the bounds `R^j K = O(c^{2(k-j)})`.
* **The comparison.**  `T_{-1/2} γ = Φ` (`R^k` of both sides agree), and the reductions of
  `T_α γ` and of `K` are `O(c^{2(k-j)})` with the *same* vanishing order; a downward induction on
  `j` shows `R^j (T_α γ) = R^j K` on `(0,1)`, using only that a function whose derivative vanishes
  and which is `O(c^{2(k-j)})` at `0` must be the zero constant.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped Interval Topology ContDiff

namespace Work.OddRadon

/-! ## The classical Abel inversion (base case `α = -1/2`) -/

namespace RI


/-- A simultaneous bound for `Ψ` and `deriv Ψ` on `(0,1)`. -/
lemma exists_bound_deriv {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ 1 Ψ) :
    ∃ C : ℝ, ∀ x ∈ Set.Ioo (0:ℝ) 1, ‖Ψ x‖ ≤ C ∧ ‖deriv Ψ x‖ ≤ C := by
  have h1 : ContinuousOn Ψ (Set.Icc (0:ℝ) 1) := hΨ.continuous.continuousOn
  have h2 : ContinuousOn (deriv Ψ) (Set.Icc (0:ℝ) 1) :=
    (hΨ.continuous_deriv le_rfl).continuousOn
  obtain ⟨C₁, hC₁⟩ := isCompact_Icc.exists_bound_of_continuousOn h1
  obtain ⟨C₂, hC₂⟩ := isCompact_Icc.exists_bound_of_continuousOn h2
  refine ⟨max C₁ C₂, fun x hx => ⟨?_, ?_⟩⟩
  · exact (hC₁ x ⟨hx.1.le, hx.2.le⟩).trans (le_max_left _ _)
  · exact (hC₂ x ⟨hx.1.le, hx.2.le⟩).trans (le_max_right _ _)

/-- **The trigonometric form of the derivative of the inner Abel integral.**
For smooth `Ψ` and `u ∈ (0,1)`,

`d/du ∫_0^u c Ψ c / √(u²-c²) dc = ∫_0^{π/2} sin θ (Ψ (u sin θ) + u sin θ Ψ' (u sin θ)) dθ`. -/
lemma deriv_abelIntegral {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ 1 Ψ) {u : ℝ}
    (hu : u ∈ Set.Ioo (0:ℝ) 1) :
    deriv (fun v : ℝ => ∫ c in (0:ℝ)..v, c * Ψ c / Real.sqrt (v ^ 2 - c ^ 2)) u
      = ∫ θ in (0:ℝ)..(Real.pi / 2),
          Real.sin θ * (Ψ (u * Real.sin θ) + u * Real.sin θ * deriv Ψ (u * Real.sin θ)) := by
  obtain ⟨C, hC⟩ := exists_bound_deriv hΨ
  have hΨc : Continuous Ψ := hΨ.continuous
  have hdΨc : Continuous (deriv Ψ) := hΨ.continuous_deriv le_rfl
  -- the integrand of the trigonometric form and its parameter derivative
  set F : ℝ → ℝ → ℝ := fun v θ => v * Real.sin θ * Ψ (v * Real.sin θ) with hF
  set F' : ℝ → ℝ → ℝ := fun v θ =>
    Real.sin θ * (Ψ (v * Real.sin θ) + v * Real.sin θ * deriv Ψ (v * Real.sin θ)) with hF'
  -- derivative of the parametrised integral
  have htrig : HasDerivAt (fun v : ℝ => ∫ θ in (0:ℝ)..(Real.pi / 2), F v θ)
      (∫ θ in (0:ℝ)..(Real.pi / 2), F' u θ) u := by
    have hcontF : ∀ v : ℝ, Continuous fun θ : ℝ => F v θ := by
      intro v
      have h1 : Continuous fun θ : ℝ => v * Real.sin θ := by fun_prop
      exact h1.mul (hΨc.comp h1)
    have hcontF' : Continuous fun θ : ℝ => F' u θ := by
      have h1 : Continuous fun θ : ℝ => u * Real.sin θ := by fun_prop
      exact (Real.continuous_sin.mul ((hΨc.comp h1).add (h1.mul (hdΨc.comp h1))))
    refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := volume) (a := (0:ℝ)) (b := Real.pi / 2) (bound := fun _ => C + C)
      (F := F) (F' := F') (x₀ := u) (s := Set.Ioo (0:ℝ) 1)
      (isOpen_Ioo.mem_nhds hu) ?_ ?_ ?_ ?_ intervalIntegrable_const ?_).2
    · filter_upwards with v
      exact (hcontF v).aestronglyMeasurable
    · exact (hcontF u).continuousOn.intervalIntegrable
    · exact hcontF'.aestronglyMeasurable
    · filter_upwards with θ hθ v hv
      have hθ' : θ ∈ Set.Ioo (0:ℝ) Real.pi := by
        rw [Set.uIoc_of_le (by positivity : (0:ℝ) ≤ Real.pi / 2)] at hθ
        exact ⟨hθ.1, by linarith [Real.pi_pos, hθ.2]⟩
      have hsinpos : 0 < Real.sin θ := Real.sin_pos_of_mem_Ioo hθ'
      have hvsin : v * Real.sin θ ∈ Set.Ioo (0:ℝ) 1 := by
        refine ⟨mul_pos hv.1 hsinpos, ?_⟩
        nlinarith [Real.sin_le_one θ, hv.1.le, hv.2]
      obtain ⟨hC1, hC2⟩ := hC _ hvsin
      have h1 : |v * Real.sin θ| ≤ 1 := by
        rw [abs_of_pos (mul_pos hv.1 hsinpos)]
        exact le_of_lt hvsin.2
      have h2 : |deriv Ψ (v * Real.sin θ)| ≤ C := by
        simpa only [Real.norm_eq_abs] using hC2
      have h3 : |Ψ (v * Real.sin θ)| ≤ C := by
        simpa only [Real.norm_eq_abs] using hC1
      have h4 : |Ψ (v * Real.sin θ) + v * Real.sin θ * deriv Ψ (v * Real.sin θ)| ≤ C + C := by
        calc |Ψ (v * Real.sin θ) + v * Real.sin θ * deriv Ψ (v * Real.sin θ)|
            ≤ |Ψ (v * Real.sin θ)| + |v * Real.sin θ * deriv Ψ (v * Real.sin θ)| := abs_add_le _ _
          _ = |Ψ (v * Real.sin θ)| + |v * Real.sin θ| * |deriv Ψ (v * Real.sin θ)| := by
                rw [abs_mul]
          _ ≤ C + 1 * C := add_le_add h3 (mul_le_mul h1 h2 (abs_nonneg _) zero_le_one)
          _ = C + C := by ring
      simp only [hF, hF']
      calc ‖Real.sin θ * (Ψ (v * Real.sin θ) + v * Real.sin θ * deriv Ψ (v * Real.sin θ))‖
          = |Real.sin θ| * |Ψ (v * Real.sin θ) + v * Real.sin θ * deriv Ψ (v * Real.sin θ)| := by
              rw [Real.norm_eq_abs, abs_mul]
        _ ≤ 1 * (C + C) := mul_le_mul (Real.abs_sin_le_one θ) h4 (abs_nonneg _) (by norm_num)
        _ = C + C := one_mul _
    · filter_upwards with θ hθ v hv
      simp only [hF, hF']
      have h1 : HasDerivAt (fun v : ℝ => v * Real.sin θ) (Real.sin θ) v := by
        simpa using (hasDerivAt_id v).mul_const (Real.sin θ)
      have h2 : HasDerivAt (fun v : ℝ => Ψ (v * Real.sin θ))
          (deriv Ψ (v * Real.sin θ) * Real.sin θ) v :=
        (((hΨ.differentiable (by norm_num)).differentiableAt).hasDerivAt.comp v h1).congr_deriv
          (by ring)
      have h3 : HasDerivAt (fun v : ℝ => v * Real.sin θ * Ψ (v * Real.sin θ))
          (Real.sin θ * Ψ (v * Real.sin θ)
            + (v * Real.sin θ) * (deriv Ψ (v * Real.sin θ) * Real.sin θ)) v :=
        (h1.mul h2).congr_of_eventuallyEq (by filter_upwards with y; rfl)
      exact h3.congr_deriv (by ring)
  -- the inner Abel integral agrees with the trigonometric form on `(0,1)`
  have hcontΨ : ContinuousOn Ψ (Set.Ioo (0:ℝ) 1) := hΨc.continuousOn
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hΨc.continuousOn
  have hbdd : ∀ c ∈ Set.Ioo (0:ℝ) 1, ‖Ψ c‖ ≤ M := fun c hc => hM c ⟨hc.1.le, hc.2.le⟩
  have hEq : Set.EqOn (fun v : ℝ => ∫ c in (0:ℝ)..v, c * Ψ c / Real.sqrt (v ^ 2 - c ^ 2))
      (fun v : ℝ => ∫ θ in (0:ℝ)..(Real.pi / 2), F v θ) (Set.Ioo (0:ℝ) 1) := by
    intro v hv
    simpa only [hF] using abel_integral_trig_substitution hv.1 hv.2 hcontΨ hbdd
  rw [(hEq.deriv isOpen_Ioo) hu, htrig.deriv]

/-- The trigonometric representative of `abelInvert Ψ`: the derivative of the trigonometric
form of the inner Abel integral. -/
def abelInvertTrig (Ψ : ℝ → ℝ) (u : ℝ) : ℝ :=
  (2 / Real.pi) * ∫ θ in (0 : ℝ)..(Real.pi / 2),
    Real.sin θ * (Ψ (u * Real.sin θ) + u * Real.sin θ * deriv Ψ (u * Real.sin θ))

/-- The trigonometric form `∫_0^{π/2} G (c sin θ) dθ` of the half-Abel transform
`∫_0^c G s / √(c²-s²) ds`. -/
def trigAbel (G : ℝ → ℝ) (c : ℝ) : ℝ :=
  ∫ θ in (0 : ℝ)..(Real.pi / 2), G (c * Real.sin θ)

/-- `abelInvert Ψ` in trigonometric form on `(0,1)`. -/
theorem abelInvert_eq_abelInvertTrig {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ 1 Ψ) {u : ℝ}
    (hu : u ∈ Set.Ioo (0:ℝ) 1) : abelInvert Ψ u = abelInvertTrig Ψ u := by
  unfold abelInvert abelInvertTrig
  rw [deriv_abelIntegral hΨ hu]

/-- Smoothness of the trigonometric representative, at the regularity actually needed. -/
lemma contDiff_abelInvertTrig {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ 2 Ψ) :
    ContDiff ℝ 1 (abelInvertTrig Ψ) := by
  unfold abelInvertTrig
  refine contDiff_const.mul ?_
  refine Work.Analysis.Calculus.contDiff_intervalIntegral_fixed 1 ?_
  have hd : ContDiff ℝ 1 (deriv Ψ) := hΨ.deriv'
  have h1 : ContDiff ℝ 1 (fun p : ℝ × ℝ => p.1 * Real.sin p.2) := by fun_prop
  have hsin : ContDiff ℝ 1 (fun p : ℝ × ℝ => Real.sin p.2) := by fun_prop
  have h2 : ContDiff ℝ 1 (fun p : ℝ × ℝ => Ψ (p.1 * Real.sin p.2)) :=
    (hΨ.of_le (by norm_num)).comp h1
  have h3 : ContDiff ℝ 1 (fun p : ℝ × ℝ => deriv Ψ (p.1 * Real.sin p.2)) :=
    hd.comp h1
  exact hsin.mul (h2.add (h1.mul h3))

/-- Smoothness of `trigAbel G`, at the regularity actually needed. -/
lemma contDiff_trigAbel {G : ℝ → ℝ} (hG : ContDiff ℝ 1 G) :
    ContDiff ℝ 1 (trigAbel G) := by
  unfold trigAbel
  refine Work.Analysis.Calculus.contDiff_intervalIntegral_fixed 1 ?_
  have h1 : ContDiff ℝ 1 (fun p : ℝ × ℝ => p.1 * Real.sin p.2) := by fun_prop
  exact hG.comp h1

/-- The half-Abel transform in trigonometric form. -/
lemma abelTrans_neg_half_eq_trigAbel {G : ℝ → ℝ} {c : ℝ} (hc : 0 < c) :
    abelTrans (-(1 / 2)) G c = trigAbel G c := by
  rw [abelTrans_neg_half_eq hc.le]
  have hpi2 : (0:ℝ) < Real.pi / 2 := by positivity
  have hc' : ContinuousOn (fun θ : ℝ => c * Real.sin θ) (Set.uIcc (0:ℝ) (Real.pi / 2)) :=
    (continuous_const.mul Real.continuous_sin).continuousOn
  have hd : ∀ x ∈ Set.Ioo (min (0:ℝ) (Real.pi / 2)) (max (0:ℝ) (Real.pi / 2)),
      HasDerivAt (fun θ : ℝ => c * Real.sin θ) (c * Real.cos x) x := by
    intro x _
    exact (Real.hasDerivAt_sin x).const_mul c
  have hn : ∀ x ∈ Set.Ioo (min (0:ℝ) (Real.pi / 2)) (max (0:ℝ) (Real.pi / 2)),
      0 ≤ c * Real.cos x := by
    intro x hx
    rw [min_eq_left hpi2.le, max_eq_right hpi2.le] at hx
    exact mul_nonneg hc.le (Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos, hx.1],
      by linarith [Real.pi_pos, hx.2]⟩)
  have hsub := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (f := fun θ : ℝ => c * Real.sin θ) (f' := fun θ : ℝ => c * Real.cos θ)
    (g := fun s : ℝ => G s / Real.sqrt (c ^ 2 - s ^ 2)) (a := (0:ℝ)) (b := Real.pi / 2)
    hc' hd hn
  simp only [Function.comp_apply, Real.sin_zero, mul_zero, Real.sin_pi_div_two, mul_one] at hsub
  rw [← hsub]
  unfold trigAbel
  apply intervalIntegral.integral_congr_ae
  have hcompl : ∀ᵐ x ∂(volume : Measure ℝ), x ∉ ({Real.pi / 2} : Set ℝ) := by
    have hfin : ({Real.pi / 2} : Set ℝ).Finite := Set.finite_singleton _
    exact MeasureTheory.compl_mem_ae_iff.mpr (hfin.measure_zero volume)
  filter_upwards [hcompl] with θ hθ hθm
  rw [Set.uIoc_of_le hpi2.le] at hθm
  simp only [Set.mem_singleton_iff] at hθ
  have hθ0 : 0 < θ := hθm.1
  have hθlt : θ < Real.pi / 2 := lt_of_le_of_ne hθm.2 hθ
  have hcos : 0 < Real.cos θ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hθ0], by linarith [Real.pi_pos, hθlt]⟩
  have hsq : c ^ 2 - (c * Real.sin θ) ^ 2 = (c * Real.cos θ) ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq θ]
  have hsqrt : Real.sqrt (c ^ 2 - (c * Real.sin θ) ^ 2) = c * Real.cos θ := by
    rw [hsq, Real.sqrt_sq (by positivity)]
  rw [hsqrt]
  have hne : c * Real.cos θ ≠ 0 := by positivity
  field_simp

/-- The parameterised derivative of the trigonometric form of the inner Abel integral. -/
lemma hasDerivAt_trigInner {h : ℝ → ℝ} (hh : ContDiff ℝ 1 h) {u : ℝ}
    (hu : u ∈ Set.Ioo (0:ℝ) 1) :
    HasDerivAt (fun u : ℝ => ∫ θ in (0:ℝ)..(Real.pi / 2), u * Real.sin θ * h (u * Real.sin θ))
      (∫ θ in (0:ℝ)..(Real.pi / 2),
        Real.sin θ * (h (u * Real.sin θ) + u * Real.sin θ * deriv h (u * Real.sin θ))) u := by
  have hhc : Continuous h := hh.continuous
  have hdc : Continuous (deriv h) := hh.continuous_deriv le_rfl
  obtain ⟨C₁, hC₁⟩ := isCompact_Icc.exists_bound_of_continuousOn hhc.continuousOn
  obtain ⟨C₂, hC₂⟩ := isCompact_Icc.exists_bound_of_continuousOn hdc.continuousOn
  set F : ℝ → ℝ → ℝ := fun v θ => v * Real.sin θ * h (v * Real.sin θ) with hF
  set F' : ℝ → ℝ → ℝ := fun v θ =>
    Real.sin θ * (h (v * Real.sin θ) + v * Real.sin θ * deriv h (v * Real.sin θ)) with hF''
  have hcontF : ∀ v : ℝ, Continuous fun θ : ℝ => F v θ := by
    intro v
    have h1 : Continuous fun θ : ℝ => v * Real.sin θ := by fun_prop
    exact h1.mul (hhc.comp h1)
  have hcontF' : Continuous fun θ : ℝ => F' u θ := by
    have h1 : Continuous fun θ : ℝ => u * Real.sin θ := by fun_prop
    exact Real.continuous_sin.mul ((hhc.comp h1).add (h1.mul (hdc.comp h1)))
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (a := (0:ℝ)) (b := Real.pi / 2) (bound := fun _ => C₁ + C₂)
    (F := F) (F' := F') (x₀ := u) (s := Set.Ioo (-1:ℝ) 1)
    (isOpen_Ioo.mem_nhds ⟨by linarith [hu.1], by linarith [hu.2]⟩) ?_ ?_ ?_ ?_
    intervalIntegrable_const ?_).2
  · filter_upwards with v
    exact (hcontF v).aestronglyMeasurable
  · exact (hcontF u).continuousOn.intervalIntegrable
  · exact hcontF'.aestronglyMeasurable
  · filter_upwards with θ hθ v hv
    have hsin1 : |Real.sin θ| ≤ 1 := Real.abs_sin_le_one θ
    have hv1 : |v| ≤ 1 := by rw [abs_le]; exact ⟨hv.1.le, hv.2.le⟩
    have hmem : v * Real.sin θ ∈ Set.Icc (-2:ℝ) 2 := by
      rw [Set.mem_Icc, ← abs_le, abs_mul]
      nlinarith [hv1, Real.abs_sin_le_one θ, abs_nonneg v, abs_nonneg (Real.sin θ)]
    have h1 : |h (v * Real.sin θ)| ≤ C₁ := by
      simpa only [Real.norm_eq_abs] using hC₁ _ hmem
    have h2 : |deriv h (v * Real.sin θ)| ≤ C₂ := by
      simpa only [Real.norm_eq_abs] using hC₂ _ hmem
    have h3 : |v * Real.sin θ| ≤ 1 := by
      rw [abs_mul]
      calc |v| * |Real.sin θ| ≤ 1 * 1 :=
            mul_le_mul hv1 hsin1 (abs_nonneg _) (by norm_num)
        _ = 1 := by ring
    simp only [hF, hF'']
    rw [Real.norm_eq_abs, abs_mul]
    calc |Real.sin θ| * |h (v * Real.sin θ) + v * Real.sin θ * deriv h (v * Real.sin θ)|
        ≤ 1 * (C₁ + C₂) := by
          refine mul_le_mul hsin1 ?_ (abs_nonneg _) (by norm_num)
          calc |h (v * Real.sin θ) + v * Real.sin θ * deriv h (v * Real.sin θ)|
              ≤ |h (v * Real.sin θ)| + |v * Real.sin θ * deriv h (v * Real.sin θ)| :=
                abs_add_le _ _
            _ = |h (v * Real.sin θ)| + |v * Real.sin θ| * |deriv h (v * Real.sin θ)| := by
                rw [abs_mul]
            _ ≤ C₁ + 1 * C₂ := add_le_add h1 (mul_le_mul h3 h2 (abs_nonneg _) zero_le_one)
            _ = C₁ + C₂ := by ring
      _ = C₁ + C₂ := one_mul _
      _ = C₁ + C₂ := by ring
  · filter_upwards with θ hθ v hv
    simp only [hF, hF'']
    have h1 : HasDerivAt (fun v : ℝ => v * Real.sin θ) (Real.sin θ) v := by
      simpa using (hasDerivAt_id v).mul_const (Real.sin θ)
    have h2 : HasDerivAt (fun v : ℝ => h (v * Real.sin θ))
        (deriv h (v * Real.sin θ) * Real.sin θ) v :=
      (((hh.differentiable (by norm_num)).differentiableAt).hasDerivAt.comp v h1).congr_deriv
        (by ring)
    have h3 : HasDerivAt (fun v : ℝ => v * Real.sin θ * h (v * Real.sin θ))
        (Real.sin θ * h (v * Real.sin θ)
          + (v * Real.sin θ) * (deriv h (v * Real.sin θ) * Real.sin θ)) v :=
      (h1.mul h2).congr_of_eventuallyEq (by filter_upwards with y; rfl)
    exact h3.congr_deriv (by ring)

/-- **Injectivity of the Abel inversion on smooth functions.**  If `abelInvert h` vanishes on
`(0,1)` and `h` is `C¹` with an `L^∞` bound, then `h` vanishes on `(0,1)`. -/
lemma abelInvert_eq_zero_imp {h : ℝ → ℝ} (hh : ContDiff ℝ 1 h)
    (hzero : ∀ u ∈ Set.Ioo (0:ℝ) 1, abelInvert h u = 0) :
    ∀ c ∈ Set.Ioo (0:ℝ) 1, h c = 0 := by
  have hhc : Continuous h := hh.continuous
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hhc.continuousOn
  set ψ : ℝ → ℝ := fun u => ∫ θ in (0:ℝ)..(Real.pi / 2), u * Real.sin θ * h (u * Real.sin θ)
    with hψ
  -- ψ and the weighted inner Abel integral agree on (0,1)
  have hEqOn : Set.EqOn ψ (fun v : ℝ => ∫ c in (0:ℝ)..v, c * h c / Real.sqrt (v ^ 2 - c ^ 2))
      (Set.Ioo (0:ℝ) 1) := by
    intro v hv
    show (∫ θ in (0:ℝ)..(Real.pi / 2), v * Real.sin θ * h (v * Real.sin θ))
      = ∫ c in (0:ℝ)..v, c * h c / Real.sqrt (v ^ 2 - c ^ 2)
    exact (abel_integral_trig_substitution hv.1 hv.2 hhc.continuousOn
      (fun c hc => hM c ⟨hc.1.le, hc.2.le⟩)).symm
  -- the derivative of ψ vanishes on (0,1)
  have hderiv0 : ∀ u ∈ Set.Ioo (0:ℝ) 1, deriv ψ u = 0 := by
    intro u hu
    have h1 : deriv ψ u
        = deriv (fun v : ℝ => ∫ c in (0:ℝ)..v, c * h c / Real.sqrt (v ^ 2 - c ^ 2)) u :=
      (hEqOn.deriv isOpen_Ioo) hu
    rw [h1]
    have h2 := hzero u hu
    unfold abelInvert at h2
    have hne : (2 / Real.pi : ℝ) ≠ 0 := by positivity
    exact (mul_eq_zero.mp h2).resolve_left hne
  -- ψ differentiable on (0,1)
  have hdiff : DifferentiableOn ℝ ψ (Set.Ioo (0:ℝ) 1) := by
    intro u hu
    exact (hasDerivAt_trigInner hh hu).differentiableAt.differentiableWithinAt
  -- hence ψ is constant on (0,1)
  have hconst : ∀ a b, a ∈ Set.Ioo (0:ℝ) 1 → b ∈ Set.Ioo (0:ℝ) 1 → ψ a = ψ b := by
    have key : ∀ x y, x ∈ Set.Ioo (0:ℝ) 1 → y ∈ Set.Ioo (0:ℝ) 1 → x < y → ψ x = ψ y := by
      intro x y hx hy hxy
      obtain ⟨ξ, hξ, hξeq⟩ := exists_deriv_eq_slope ψ hxy
        (hdiff.continuousOn.mono (Set.Icc_subset_Ioo hx.1 hy.2))
        (hdiff.mono (Set.Ioo_subset_Ioo hx.1.le hy.2.le))
      rw [hderiv0 ξ ⟨lt_trans hx.1 hξ.1, lt_trans hξ.2 hy.2⟩] at hξeq
      have hyn : y - x ≠ 0 := ne_of_gt (sub_pos.mpr hxy)
      have hz : ψ x - ψ y = 0 := by
        field_simp at hξeq
        linarith
      exact sub_eq_zero.mp hz
    intro a b ha hb
    by_cases hab : a ≤ b
    · rcases eq_or_lt_of_le hab with h | h
      · rw [← h]
      · exact key a b ha hb h
    · rcases eq_or_lt_of_le (le_of_lt (lt_of_not_ge hab)) with h | h
      · rw [h]
      · exact (key b a hb ha h).symm
  -- ψ vanishes on `(0,1)`
  have hψbound : ∀ u ∈ Set.Ioo (0:ℝ) 1, |ψ u| ≤ M * u := by
    intro u hu
    rw [hψ]
    have h1 : |∫ θ in (0:ℝ)..(Real.pi / 2), u * Real.sin θ * h (u * Real.sin θ)|
        ≤ ∫ θ in (0:ℝ)..(Real.pi / 2), |u * Real.sin θ * h (u * Real.sin θ)| :=
      intervalIntegral.abs_integral_le_integral_abs (by positivity)
    have h2 : (∫ θ in (0:ℝ)..(Real.pi / 2), |u * Real.sin θ * h (u * Real.sin θ)|)
        ≤ ∫ θ in (0:ℝ)..(Real.pi / 2), u * Real.sin θ * M := by
      apply intervalIntegral.integral_mono_on (by positivity)
      · exact (((continuous_const.mul Real.continuous_sin).mul
          (hhc.comp (continuous_const.mul Real.continuous_sin))).abs).continuousOn.intervalIntegrable
      · exact (((continuous_const.mul Real.continuous_sin).mul
          continuous_const)).continuousOn.intervalIntegrable
      · intro θ hθ
        have hsin : 0 ≤ Real.sin θ := Real.sin_nonneg_of_mem_Icc
          ⟨hθ.1, by linarith [Real.pi_pos, hθ.2]⟩
        have hmem : u * Real.sin θ ∈ Set.Icc (0:ℝ) 1 := by
          refine ⟨mul_nonneg hu.1.le hsin, ?_⟩
          nlinarith [Real.sin_le_one θ, hu.1.le, hu.2]
        have hb := hM _ hmem
        rw [Real.norm_eq_abs] at hb
        rw [abs_mul, abs_of_nonneg (mul_nonneg hu.1.le hsin)]
        exact mul_le_mul_of_nonneg_left hb (mul_nonneg hu.1.le hsin)
    have h3 : (∫ θ in (0:ℝ)..(Real.pi / 2), u * Real.sin θ * M) = M * u := by
      rw [show (fun θ : ℝ => u * Real.sin θ * M) = (fun θ : ℝ => (M * u) * Real.sin θ) by
        funext θ; ring]
      rw [intervalIntegral.integral_const_mul, integral_sin]
      simp [Real.cos_pi_div_two, Real.cos_zero]
    rw [h3] at h2
    exact le_trans h1 h2
  have hψzero : ∀ u ∈ Set.Ioo (0:ℝ) 1, ψ u = 0 := by
    intro u hu
    by_contra hne
    have hpos : 0 < |ψ u| := abs_pos.mpr hne
    have hMnn : 0 ≤ M := le_trans (abs_nonneg _) (hM 0 ⟨le_rfl, zero_le_one⟩)
    by_cases hM0 : M = 0
    · have hle : |ψ u| ≤ 0 := by
        have := hψbound u hu
        rwa [hM0, zero_mul] at this
      exact hne (abs_eq_zero.mp (le_antisymm hle (abs_nonneg _)))
    · have hMpos : 0 < M := lt_of_le_of_ne hMnn (Ne.symm hM0)
      set u₀ : ℝ := min (u / 2) (|ψ u| / (2 * M)) with hu₀def
      have hu₀pos : 0 < u₀ := lt_min (by linarith [hu.1]) (by positivity)
      have hu₀lt : u₀ < 1 := lt_of_le_of_lt (min_le_left _ _) (by linarith [hu.2])
      have hu₀ : u₀ ∈ Set.Ioo (0:ℝ) 1 := ⟨hu₀pos, hu₀lt⟩
      have h1 : |ψ u| ≤ M * u₀ := by
        rw [hconst u u₀ hu hu₀]
        exact hψbound u₀ hu₀
      have h2 : M * u₀ ≤ |ψ u| / 2 := by
        calc M * u₀ ≤ M * (|ψ u| / (2 * M)) :=
              mul_le_mul_of_nonneg_left (min_le_right _ _) hMpos.le
          _ = |ψ u| / 2 := by field_simp
      linarith
  -- the weighted function `c ↦ c * h c` is continuous, and its Abel transform vanishes
  have hMcont : ContinuousOn (fun c : ℝ => c * h c) (Set.Icc (0:ℝ) 1) :=
    (continuousOn_id.mul hhc.continuousOn)
  have hinner : Set.EqOn (fun c : ℝ => ∫ s in (0:ℝ)..c, (s * h s) / Real.sqrt (c ^ 2 - s ^ 2))
      (0 : ℝ → ℝ) (Set.Ioo (0:ℝ) 1) := by
    intro c hc
    rw [Pi.zero_apply]
    show (∫ s in (0:ℝ)..c, (s * h s) / Real.sqrt (c ^ 2 - s ^ 2)) = 0
    have h1 : (∫ s in (0:ℝ)..c, (s * h s) / Real.sqrt (c ^ 2 - s ^ 2)) = ψ c := (hEqOn hc).symm
    rw [h1, hψzero c hc]
  intro c hc
  have hleft := Commons.Analysis.Radon.abel_inversion_hemisphere_final (G := fun c : ℝ => c * h c)
    hMcont hc
  have hz : abelInvert (0 : ℝ → ℝ) c = 0 := by
    unfold abelInvert
    simp
  have hf : c * h c = 0 := by
    have h2 : (2 / Real.pi) * deriv (fun u => ∫ c' in (0:ℝ)..u,
          c' * (∫ s in (0:ℝ)..c', s * h s / Real.sqrt (c' ^ 2 - s ^ 2)) /
            Real.sqrt (u ^ 2 - c' ^ 2)) c
        = abelInvert (fun c' : ℝ => ∫ s in (0:ℝ)..c',
            s * h s / Real.sqrt (c' ^ 2 - s ^ 2)) c := rfl
    rw [hleft, h2, abelInvert_congr_of_eqOn hc.1 hc.2 hinner, hz]
  exact (mul_eq_zero.mp hf).resolve_left (ne_of_gt hc.1)

/-- Linearity of the Abel inversion on smooth functions. -/
lemma abelInvert_sub {f g : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) {u : ℝ}
    (hu : u ∈ Set.Ioo (0:ℝ) 1) :
    abelInvert (f - g) u = abelInvert f u - abelInvert g u := by
  have hfg : ContDiff ℝ 1 (f - g) := hf.sub hg
  rw [abelInvert_eq_abelInvertTrig hfg hu, abelInvert_eq_abelInvertTrig hf hu,
    abelInvert_eq_abelInvertTrig hg hu]
  unfold abelInvertTrig
  rw [← mul_sub]
  congr 1
  rw [← intervalIntegral.integral_sub]
  · apply intervalIntegral.integral_congr
    intro θ _
    have hderivfun : deriv (f - g) = fun x => deriv f x - deriv g x := by
      funext x
      exact deriv_sub ((hf.differentiable (by norm_num)).differentiableAt)
        ((hg.differentiable (by norm_num)).differentiableAt)
    rw [hderivfun]
    simp only [Pi.sub_apply]
    ring
  · have h1 : Continuous fun θ : ℝ => u * Real.sin θ := by fun_prop
    have h2 : Continuous fun θ : ℝ =>
        Real.sin θ * (f (u * Real.sin θ) + u * Real.sin θ * deriv f (u * Real.sin θ)) :=
      Real.continuous_sin.mul ((hf.continuous.comp h1).add
        (h1.mul ((hf.continuous_deriv le_rfl).comp h1)))
    exact h2.intervalIntegrable (0:ℝ) (Real.pi / 2)
  · have h1 : Continuous fun θ : ℝ => u * Real.sin θ := by fun_prop
    have h2 : Continuous fun θ : ℝ =>
        Real.sin θ * (g (u * Real.sin θ) + u * Real.sin θ * deriv g (u * Real.sin θ)) :=
      Real.continuous_sin.mul ((hg.continuous.comp h1).add
        (h1.mul ((hg.continuous_deriv le_rfl).comp h1)))
    exact h2.intervalIntegrable (0:ℝ) (Real.pi / 2)

/-- **The right-inverse (surjectivity) half of the half-Abel transform**, for smooth data:
`∫_0^c (abelInvert Ψ) s / √(c²-s²) ds = Ψ c` on `(0,1)`. -/
theorem abelTrans_neg_half_abelInvert {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ 2 Ψ) {c : ℝ}
    (hc : c ∈ Set.Ioo (0:ℝ) 1) :
    abelTrans (-(1 / 2)) (abelInvert Ψ) c = Ψ c := by
  set Bc : ℝ → ℝ := abelInvertTrig Ψ with hBc
  set T₂ : ℝ → ℝ := trigAbel Bc with hT₂
  have hBcinf : ContDiff ℝ 1 Bc := contDiff_abelInvertTrig hΨ
  have hBccont : ContinuousOn Bc (Set.Icc (0:ℝ) 1) := hBcinf.continuous.continuousOn
  have hT₂sm : ContDiff ℝ 1 T₂ := contDiff_trigAbel hBcinf
  have hΨ1 : ContDiff ℝ 1 Ψ := hΨ.of_le (by norm_num)
  -- `T₂` is the half-Abel transform of `Bc`
  have hT₂abel : ∀ u ∈ Set.Ioo (0:ℝ) 1, abelTrans (-(1 / 2)) Bc u = T₂ u := by
    intro u hu
    rw [abelTrans_neg_half_eq_trigAbel hu.1]
  -- the left inverse of the half-Abel transform, applied to `Bc`
  have hleft : ∀ u ∈ Set.Ioo (0:ℝ) 1, abelInvert T₂ u = Bc u := by
    intro u hu
    have hinner : Set.EqOn (fun c : ℝ => ∫ s in (0:ℝ)..c, Bc s / Real.sqrt (c ^ 2 - s ^ 2))
        T₂ (Set.Ioo (0:ℝ) 1) := by
      intro c hc'
      show (∫ s in (0:ℝ)..c, Bc s / Real.sqrt (c ^ 2 - s ^ 2)) = T₂ c
      rw [← abelTrans_neg_half_eq hc'.1.le, hT₂abel c hc']
    have h := Commons.Analysis.Radon.abel_inversion_hemisphere_final (G := Bc) hBccont hu
    calc abelInvert T₂ u
        = abelInvert (fun c : ℝ => ∫ s in (0:ℝ)..c, Bc s / Real.sqrt (c ^ 2 - s ^ 2)) u :=
          (abelInvert_congr_of_eqOn hu.1 hu.2 hinner).symm
      _ = (2 / Real.pi) * deriv (fun u' : ℝ => ∫ c in (0:ℝ)..u',
            c * (∫ s in (0:ℝ)..c, Bc s / Real.sqrt (c ^ 2 - s ^ 2)) /
              Real.sqrt (u' ^ 2 - c ^ 2)) u := rfl
      _ = Bc u := h.symm
  -- hence `abelInvert (T₂ - Ψ)` vanishes
  have hzero : ∀ u ∈ Set.Ioo (0:ℝ) 1, abelInvert (T₂ - Ψ) u = 0 := by
    intro u hu
    rw [abelInvert_sub hT₂sm hΨ1 hu, hleft u hu,
      abelInvert_eq_abelInvertTrig hΨ1 hu]
    ring
  have hT₂Ψ : ∀ u ∈ Set.Ioo (0:ℝ) 1, (T₂ - Ψ) u = 0 :=
    abelInvert_eq_zero_imp (hT₂sm.sub hΨ1) hzero
  -- conclude
  have h1 : trigAbel (abelInvert Ψ) c = T₂ c := by
    show (∫ θ in (0:ℝ)..(Real.pi / 2), (abelInvert Ψ) (c * Real.sin θ))
      = (∫ θ in (0:ℝ)..(Real.pi / 2), Bc (c * Real.sin θ))
    apply intervalIntegral.integral_congr_ae
    filter_upwards with θ hθm
    rw [Set.uIoc_of_le (by positivity : (0:ℝ) ≤ Real.pi / 2)] at hθm
    have hsinpos : 0 < Real.sin θ :=
      Real.sin_pos_of_mem_Ioo ⟨hθm.1, by linarith [Real.pi_pos, hθm.2]⟩
    have hmem : c * Real.sin θ ∈ Set.Ioo (0:ℝ) 1 := by
      refine ⟨mul_pos hc.1 hsinpos, ?_⟩
      nlinarith [Real.sin_le_one θ, hc.1.le, hc.2]
    rw [abelInvert_eq_abelInvertTrig hΨ1 hmem]
  rw [abelTrans_neg_half_eq_trigAbel hc.1, h1]
  exact sub_eq_zero.mp (hT₂Ψ c hc)

/-! ## The exponent-raising recursion in integrated form -/

/-- `abelTrans a G c` depends on `G` only on `(0,c)`. -/
lemma abelTrans_congr {a : ℝ} {f g : ℝ → ℝ} {c : ℝ} (hc : 0 < c)
    (h : Set.EqOn f g (Set.Ioo (0:ℝ) c)) : abelTrans a f c = abelTrans a g c := by
  unfold abelTrans
  apply intervalIntegral.integral_congr_ae
  have hcompl : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ c := by
    rw [MeasureTheory.ae_iff]; simp [measure_singleton]
  filter_upwards [hcompl] with x hxc hx
  rw [Set.uIoc_of_le hc.le] at hx
  rw [h ⟨hx.1, lt_of_le_of_ne hx.2 hxc⟩]


/-- **Pointwise bound on the Abel transform.**  For `a > -1`, a function `G` bounded by `M` on
`(0,1)` and `s ∈ (0,1)`,
`‖abelTrans a G s‖ ≤ M · (∫_0^1 (1-v²)^a dv) · s^{2a+1}`. -/
lemma abelTrans_le_mul {a : ℝ} (ha : -1 < a) {G : ℝ → ℝ} {M : ℝ}
    (hM : ∀ x ∈ Set.Ioo (0:ℝ) 1, ‖G x‖ ≤ M) {s : ℝ} (hs : s ∈ Set.Ioo (0:ℝ) 1) :
    ‖abelTrans a G s‖ ≤ M * (∫ v in (0:ℝ)..1, (1 - v^2)^a) * s ^ (2*a + 1) := by
  have htrig : abelTrans a G s
      = s ^ (2*a + 1) * ∫ v in (0:ℝ)..1, G (s*v) * (1 - v^2)^a :=
    AbelDirect.abelTrans_eq_integral_comp_mul a G hs.1
  have hmain : ‖∫ v in (0:ℝ)..1, G (s*v) * (1 - v^2)^a‖
      ≤ ∫ v in (0:ℝ)..1, M * (1 - v^2)^a := by
    refine intervalIntegral.norm_integral_le_of_norm_le (by norm_num) ?_ ?_
    · filter_upwards with v hv
      rw [Set.mem_Ioc] at hv
      have hv0 : 0 < v := hv.1
      have hv1 : v ≤ 1 := hv.2
      have hnn : 0 ≤ (1 - v^2)^a := Real.rpow_nonneg (by nlinarith [hv0, hv1]) a
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hnn]
      exact mul_le_mul_of_nonneg_right
        (hM _ ⟨mul_pos hs.1 hv0, by nlinarith [hs.2, hv0, hv1]⟩) hnn
    · exact (AbelDirect.intervalIntegrable_one_sub_sq_rpow ha).const_mul M
  have hconst : (∫ v in (0:ℝ)..1, M * (1 - v^2)^a) = M * (∫ v in (0:ℝ)..1, (1 - v^2)^a) :=
    intervalIntegral.integral_const_mul M _
  rw [htrig, norm_mul, Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos hs.1 (2*a+1))]
  calc s ^ (2*a+1) * ‖∫ v in (0:ℝ)..1, G (s*v) * (1 - v^2)^a‖
      ≤ s ^ (2*a+1) * (∫ v in (0:ℝ)..1, M * (1 - v^2)^a) :=
        mul_le_mul_of_nonneg_left hmain (Real.rpow_nonneg hs.1.le _)
    _ = s ^ (2*a+1) * (M * (∫ v in (0:ℝ)..1, (1 - v^2)^a)) := by rw [hconst]
    _ = M * (∫ v in (0:ℝ)..1, (1 - v^2)^a) * s ^ (2*a+1) := by ring

end RI

/-! ## The iterated reduction of `c^{2m} H`

The `j`-fold exponent reduction of `c^{2m} H` is again `c^{2(m-j)}` times a globally smooth
coefficient.  This gives both a smooth representative of the reduced datum and the bounds
`R^j K = O(c^{2(k-j)})` used in the comparison at the end. -/

/-- The iterated reduction peels off from the outside: the `j`-th exponent used is `α - j`. -/
lemma abelReduceIter_succ' (α : ℝ) (j : ℕ) (F : ℝ → ℝ) :
    abelReduceIter α (j + 1) F = abelReduce (α - (j : ℝ)) (abelReduceIter α j F) := by
  induction j generalizing α F with
  | zero => simp [abelReduceIter_succ, abelReduceIter_zero]
  | succ j ih =>
    have h1 : abelReduceIter α (j + 1 + 1) F
        = abelReduceIter (α - 1) (j + 1) (abelReduce α F) := abelReduceIter_succ α (j + 1) F
    rw [h1, ih (α := α - 1) (F := abelReduce α F)]
    rw [show abelReduceIter (α - 1) j (abelReduce α F) = abelReduceIter α (j + 1) F from
      (abelReduceIter_succ α j F).symm]
    refine congrArg (fun e : ℝ => abelReduce e (abelReduceIter α (j + 1) F)) ?_
    push_cast
    ring

/-- `abelReduce` depends only on the germ of its argument. -/
lemma abelReduce_congr_eventuallyEq {α : ℝ} {f g : ℝ → ℝ} {c : ℝ}
    (h : f =ᶠ[𝓝 c] g) : abelReduce α f c = abelReduce α g c := by
  simp only [abelReduce]
  rw [h.deriv_eq]

/-- **One reduction step of `c^{2m} F`.**  For `m ≥ 1`, `F` differentiable, `α ≠ 0` and `c ≠ 0`,

`abelReduce α (c ↦ c^{2m} F c) c = c^{2(m-1)} · ((m F c + c F' c / 2) / α)`. -/
lemma abelReduce_pow_mul {m : ℕ} (hm : 1 ≤ m) {α : ℝ} (hα : α ≠ 0) {F : ℝ → ℝ}
    (hF : Differentiable ℝ F) {c : ℝ} (hc : c ≠ 0) :
    abelReduce α (fun x : ℝ => x ^ (2 * m) * F x) c
      = c ^ (2 * m - 2) * (((m : ℝ) * F c + c * deriv F c / 2) / α) := by
  have hder : deriv (fun x : ℝ => x ^ (2 * m) * F x) c
      = (2 * m : ℝ) * c ^ (2 * m - 1) * F c + c ^ (2 * m) * deriv F c := by
    have h1 : HasDerivAt (fun x : ℝ => x ^ (2 * m)) ((2 * m : ℕ) * c ^ (2 * m - 1)) c :=
      hasDerivAt_pow (2 * m) c
    have h2 : HasDerivAt F (deriv F c) c := hF.differentiableAt.hasDerivAt
    have h3 : HasDerivAt (fun x : ℝ => x ^ (2 * m) * F x)
        ((2 * m : ℕ) * c ^ (2 * m - 1) * F c + c ^ (2 * m) * deriv F c) c := h1.mul h2
    have h4 := h3.deriv
    simpa using h4
  have hpow : c ^ (2 * m) = c ^ (2 * m - 2) * c ^ 2 := by
    rw [← pow_add]; congr 1; omega
  have hpow1 : c ^ (2 * m - 1) = c ^ (2 * m - 2) * c ^ 1 := by
    rw [← pow_add]; congr 1; omega
  rw [abelReduce, hder, hpow, hpow1, pow_one]
  field_simp
  try ring

/-- The algebra of one coefficient step (the arithmetical content of `redCoef_succ`). -/
lemma redCoef_step_algebra {m j : ℕ} (hj : j + 1 ≤ m) {α : ℝ} {F : ℝ → ℝ} {c : ℝ} :
    c ^ (2 * (m - (j + 1))) * ((((m : ℝ) - j) * F c + c * deriv F c / 2) / (α - j))
      = c ^ (2 * (m - j) - 2) * (((((m - j : ℕ)) : ℝ) * F c + c * deriv F c / 2) / (α - j)) := by
  have h1 : 2 * (m - (j + 1)) = 2 * (m - j) - 2 := by omega
  have h2 : (((m - j : ℕ)) : ℝ) = (m : ℝ) - j := by
    rw [Nat.cast_sub (by omega : j ≤ m)]
  rw [h1, h2]

/-- The coefficient sequence of the `j`-fold reduction of `c^{2m} H`. -/
noncomputable def redCoef (m : ℕ) (α : ℝ) (H : ℝ → ℝ) : ℕ → ℝ → ℝ
  | 0 => H
  | (j + 1) => fun c => (((m : ℝ) - j) * redCoef m α H j c
      + c * deriv (redCoef m α H j) c / 2) / (α - j)

@[simp] lemma redCoef_zero (m : ℕ) (α : ℝ) (H : ℝ → ℝ) : redCoef m α H 0 = H := rfl

lemma redCoef_succ (m : ℕ) (α : ℝ) (H : ℝ → ℝ) (j : ℕ) :
    redCoef m α H (j + 1) = fun c => (((m : ℝ) - j) * redCoef m α H j c
      + c * deriv (redCoef m α H j) c / 2) / (α - j) := rfl

/-- Arithmetic of the exponent shift, at the level of the `ContDiff` exponent type. -/
lemma cast_sub_succ_add_one (N j : ℕ) (hj : j + 1 ≤ N) :
    ((N - (j + 1) : ℕ) : WithTop ℕ∞) + 1 = ((N - j : ℕ) : WithTop ℕ∞) := by
  rw [show ((N - (j + 1) : ℕ) : WithTop ℕ∞) + 1 = ((N - (j + 1) + 1 : ℕ) : WithTop ℕ∞) by
    push_cast; ring]
  congr 1
  omega

/-- **Smoothness of the reduction coefficients**: `redCoef` loses exactly one derivative per
step. -/
lemma contDiff_redCoef (m : ℕ) (α : ℝ) {H : ℝ → ℝ} {N : ℕ} (hH : ContDiff ℝ N H) :
    ∀ j ≤ N, (∀ i < j, α - (i : ℝ) ≠ 0) → ContDiff ℝ ((N - j : ℕ) : WithTop ℕ∞) (redCoef m α H j) := by
  intro j
  induction j with
  | zero => intro _ _; simpa using hH
  | succ j ih =>
    intro hj hα
    have hj' : j ≤ N := by omega
    have hα' : ∀ i < j, α - (i : ℝ) ≠ 0 := fun i hi => hα i (lt_trans hi (Nat.lt_succ_self j))
    have hFj : ContDiff ℝ (((N - (j + 1) : ℕ) : WithTop ℕ∞) + 1) (redCoef m α H j) := by
      rw [cast_sub_succ_add_one N j hj]
      exact ih hj' hα'
    have hFj' : ContDiff ℝ ((N - (j + 1) : ℕ) : WithTop ℕ∞) (deriv (redCoef m α H j)) := by
      simpa using hFj.deriv'
    have hc1 : ContDiff ℝ ((N - (j + 1) : ℕ) : WithTop ℕ∞)
        (fun c : ℝ => ((m : ℝ) - j) * redCoef m α H j c) :=
      contDiff_const.mul (hFj.of_le (by simp))
    have hc2 : ContDiff ℝ ((N - (j + 1) : ℕ) : WithTop ℕ∞)
        (fun c : ℝ => c * deriv (redCoef m α H j) c / 2) :=
      (contDiff_id.mul hFj').div_const 2
    rw [redCoef_succ]
    exact (hc1.add hc2).div_const _

/-- **The reduced datum of `c^{2m} H` in closed form.** -/
lemma eqOn_redCoef (m : ℕ) (α : ℝ) {H : ℝ → ℝ} {N : ℕ} (hH : ContDiff ℝ N H) :
    ∀ j, j + 1 ≤ N → j ≤ m → (∀ i < j, α - (i : ℝ) ≠ 0) →
      Set.EqOn (fun c : ℝ => c ^ (2 * (m - j)) * redCoef m α H j c)
        (abelReduceIter α j (fun c : ℝ => c ^ (2 * m) * H c)) (Set.Ioo (0 : ℝ) 1) := by
  intro j
  induction j with
  | zero => intro _ _ _ c _; simp
  | succ j ih =>
    intro hN hj hα c hc
    have hj' : j ≤ m := by omega
    have hNj : j ≤ N := by omega
    have hα' : ∀ i < j, α - (i : ℝ) ≠ 0 := fun i hi => hα i (lt_trans hi (Nat.lt_succ_self j))
    have hmj : 1 ≤ m - j := by omega
    have hαne : α - (j : ℝ) ≠ 0 := hα j (Nat.lt_succ_self j)
    have hFd : Differentiable ℝ (redCoef m α H j) :=
      (contDiff_redCoef m α hH j (by omega) hα').differentiable (by
        exact_mod_cast (by omega : N - j ≠ 0))
    rw [abelReduceIter_succ', redCoef_succ]
    rw [abelReduce_congr_eventuallyEq (α := α - (j : ℝ)) (c := c)
      ((ih (by omega) hj' hα').eventuallyEq_of_mem (isOpen_Ioo.mem_nhds hc)).symm]
    rw [abelReduce_pow_mul hmj hαne hFd (ne_of_gt hc.1)]
    exact redCoef_step_algebra hj

/-- **The right-inverse half of the odd-dimensional Abel inversion, for the Radon datum.** -/
theorem abelTrans_radonInverse_eq_abelDatum (n : ℕ) (hn : 1 ≤ n) {F : ℝ → ℝ}
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) F (Set.Icc (0 : ℝ) 1)) :
    ∀ c : ℝ, c ∈ Set.Ioo (0 : ℝ) 1 →
      abelTrans ((n : ℝ) - 3 / 2) (radonInverse n F) c = abelDatum n F c := by
  set k : ℕ := n - 1 with hk
  set α : ℝ := (n : ℝ) - 3 / 2 with hαdef
  have hαk : α = (k : ℝ) - 1 / 2 := by
    have hcast : ((k : ℕ) : ℝ) = (n : ℝ) - 1 := by
      rw [hk, Nat.cast_sub hn]
      norm_num
    rw [hαdef, hcast]
    ring
  have h2k : 2 * n - 2 = 2 * k := by omega
  have hαne : ∀ i < k, α - (i : ℝ) ≠ 0 := by
    intro i hi
    have hi' : (i : ℝ) + 1 ≤ (k : ℝ) := by
      exact_mod_cast (by omega : i + 1 ≤ k)
    have hpos : (0 : ℝ) < α - (i : ℝ) := by
      rw [hαk]
      linarith
    exact ne_of_gt hpos
  -- a globally smooth extension of the datum `F`
  have hFsm : ContDiffOn ℝ (k + 4) F (Set.Icc (0 : ℝ) 1) :=
    (contDiffOn_infty.mp hF) (k + 4)
  set Gext : ℝ → ℝ := Commons.Analysis.Calculus.taylorExtend F (k + 4) 0 1 with hGext
  have hGext_sm : ContDiff ℝ (k + 4) Gext := by
    rw [hGext]
    exact Commons.Analysis.Calculus.contDiff_taylorExtend (k + 4) (by norm_num) hFsm
  have hGext_eq : Set.EqOn Gext F (Set.Icc (0 : ℝ) 1) := by
    rw [hGext]
    exact Commons.Analysis.Calculus.taylorExtend_eqOn_Icc
  set Hc : ℝ → ℝ := fun c => (2 * sphereArea (2 * n - 2))⁻¹ * Gext c with hHc
  have hHc_sm : ContDiff ℝ (k + 4) Hc := by
    rw [hHc]
    exact contDiff_const.mul hGext_sm
  set Kx : ℝ → ℝ := fun c => c ^ (2 * k) * Hc c with hKx
  set Ψ0 : ℝ → ℝ := redCoef k α Hc k with hΨ0
  have hK_eq : Set.EqOn (abelDatum n F) Kx (Set.Ioo (0 : ℝ) 1) := by
    intro c hc
    have hc1 : c ∈ Set.Icc (0 : ℝ) 1 := ⟨hc.1.le, hc.2.le⟩
    have h2c : c ^ (2 * n - 2) = c ^ (2 * k) := by rw [h2k]
    simp only [abelDatum, hKx, hHc]
    rw [h2c, hGext_eq hc1]
    ring
  have hΨ0_eq : Set.EqOn Ψ0 (abelReduceIter α k Kx) (Set.Ioo (0 : ℝ) 1) := by
    have h := eqOn_redCoef (m := k) (α := α) (H := Hc) (N := k + 4) hHc_sm k (by omega) (by omega) hαne
    simpa [hΨ0, hKx] using h
  have hΨ0_sm4 : ContDiff ℝ 4 Ψ0 := by
    have h := contDiff_redCoef (m := k) (α := α) (H := Hc) (N := k + 4) hHc_sm k (by omega) hαne
    have h4 : ((k + 4) - k : ℕ) = 4 := by omega
    rw [h4] at h
    simpa [hΨ0] using h
  have hΨ0_sm2 : ContDiff ℝ 2 Ψ0 := hΨ0_sm4.of_le (by norm_num)
  have hΨ0_sm1 : ContDiff ℝ 1 Ψ0 := hΨ0_sm4.of_le (by norm_num)
  have hΦ : Set.EqOn (abelReduceIter α (n - 1) (abelDatum n F)) Ψ0 (Set.Ioo (0 : ℝ) 1) := by
    have h1 : Set.EqOn (abelReduceIter α (n - 1) (abelDatum n F))
        (abelReduceIter α (n - 1) Kx) (Set.Ioo (0 : ℝ) 1) :=
      abelReduceIter_congr hK_eq α (n - 1)
    have h2 : n - 1 = k := hk
    rw [h2] at h1
    exact h1.trans hΨ0_eq.symm
  have hγ_eq : ∀ u ∈ Set.Ioo (0 : ℝ) 1, radonInverse n F u = abelInvert Ψ0 u := by
    intro u hu
    have hdef : radonInverse n F u
        = abelInvert (abelReduceIter α (n - 1) (abelDatum n F)) u := rfl
    rw [hdef]
    exact abelInvert_congr_of_eqOn hu.1 hu.2 hΦ
  -- the trigonometric representative of `abelInvert Ψ0`, which is globally `C¹`
  set γext : ℝ → ℝ := RI.abelInvertTrig Ψ0 with hγext
  have hγext_sm1 : ContDiff ℝ 1 γext := by
    rw [hγext]
    exact RI.contDiff_abelInvertTrig hΨ0_sm2
  have hγext_eq : ∀ u ∈ Set.Ioo (0 : ℝ) 1, γext u = abelInvert Ψ0 u := by
    intro u hu
    rw [hγext]
    exact (RI.abelInvert_eq_abelInvertTrig hΨ0_sm1 hu).symm
  have hγext_eq_γ : ∀ u ∈ Set.Ioo (0 : ℝ) 1, γext u = radonInverse n F u := by
    intro u hu
    rw [hγext_eq u hu, ← hγ_eq u hu]
  -- the base case at exponent `-1/2`
  have hbase : ∀ x ∈ Set.Ioo (0 : ℝ) 1, abelTrans (-(1 / 2)) γext x = Ψ0 x := by
    intro x hx
    have h1 : abelTrans (-(1 / 2)) γext x = abelTrans (-(1 / 2)) (abelInvert Ψ0) x :=
      RI.abelTrans_congr hx.1 (fun y hy => hγext_eq y ⟨hy.1, lt_trans hy.2 hx.2⟩)
    rw [h1]
    exact RI.abelTrans_neg_half_abelInvert hΨ0_sm2 hx
  -- the reduction of the Abel transform of `γext`
  have hγext_ci1 : ContDiffOn ℝ 1 γext (Set.Ioo (-1 : ℝ) 1) := hγext_sm1.contDiffOn
  have hαlt : ((k : ℕ) : ℝ) - 1 < α := by
    rw [hαk]; norm_num
  have hsum : α - ((k : ℕ) : ℝ) = -(1 / 2) := by
    rw [hαk]; ring
  have hchain : Set.EqOn (abelReduceIter α k (abelTrans α γext)) (abelTrans (-(1 / 2)) γext)
      (Set.Ioo (0 : ℝ) 1) := by
    have h := Work.OddCurve.Inv.abelReduceIter_abelTrans_local (G := γext) hγext_ci1
      (k := k) (α := α) hαlt
    rw [hsum] at h
    exact h
  have hchainj : ∀ j ≤ k, Set.EqOn (abelReduceIter α j (abelTrans α γext))
      (abelTrans (α - (j : ℝ)) γext) (Set.Ioo (0 : ℝ) 1) := by
    intro j hj
    have hj' : (j : ℝ) ≤ (k : ℝ) := by exact_mod_cast hj
    exact Work.OddCurve.Inv.abelReduceIter_abelTrans_local (G := γext) hγext_ci1
      (k := j) (α := α) (by rw [hαk]; linarith)
  have hU : Set.EqOn (abelReduceIter α k (abelTrans α γext)) Ψ0 (Set.Ioo (0 : ℝ) 1) :=
    hchain.trans hbase
  have hUk : Set.EqOn (abelReduceIter α k (abelTrans α γext)) (abelReduceIter α k Kx)
      (Set.Ioo (0 : ℝ) 1) := hU.trans hΨ0_eq
  -- bounds
  obtain ⟨S, hS⟩ := isCompact_Icc.exists_bound_of_continuousOn (f := γext)
    hγext_sm1.continuous.continuousOn
  have hSat : ∀ x ∈ Set.Ioo (0 : ℝ) 1, ‖γext x‖ ≤ S := fun x hx => hS x ⟨hx.1.le, hx.2.le⟩
  have hbound_f : ∀ m, m + 1 ≤ k → ∃ C : ℝ, ∀ c ∈ Set.Ioo (0 : ℝ) 1,
      ‖abelReduceIter α m (abelTrans α γext) c‖ ≤ C * c ^ (2 * (k - m)) := by
    intro m hm
    have hpos : 0 < α - (m : ℝ) := by
      have hm' : (m : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast hm
      rw [hαk]; linarith
    refine ⟨S * (∫ v in (0:ℝ)..1, (1 - v ^ 2) ^ (α - (m : ℝ))), ?_⟩
    intro c hc
    have h1 : abelReduceIter α m (abelTrans α γext) c = abelTrans (α - (m : ℝ)) γext c :=
      hchainj m (by omega) hc
    rw [h1]
    have hb := RI.abelTrans_le_mul (a := α - (m : ℝ)) (G := γext) (M := S)
      (by linarith) hSat hc
    have hexp : 2 * (α - (m : ℝ)) + 1 = ((2 * (k - m) : ℕ) : ℝ) := by
      have h1 : ((2 * (k - m) : ℕ) : ℝ) = 2 * ((k : ℝ) - m) := by
        rw [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sub (by omega : m ≤ k)]
      rw [hαk, h1]; ring
    rw [hexp, Real.rpow_natCast] at hb
    exact hb
  have hbound_g : ∀ m ≤ k, ∃ C : ℝ, ∀ c ∈ Set.Ioo (0 : ℝ) 1,
      ‖abelReduceIter α m Kx c‖ ≤ C * c ^ (2 * (k - m)) := by
    intro m hm
    have hαne' : ∀ i < m, α - (i : ℝ) ≠ 0 := fun i hi => hαne i (lt_of_lt_of_le hi hm)
    have hsm := contDiff_redCoef (m := k) (α := α) (H := Hc) (N := k + 4) hHc_sm m (by omega) hαne'
    obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
      (f := redCoef k α Hc m) hsm.continuous.continuousOn
    refine ⟨C, ?_⟩
    intro c hc
    have h1 : abelReduceIter α m Kx c = c ^ (2 * (k - m)) * redCoef k α Hc m c :=
      (eqOn_redCoef (m := k) (α := α) (H := Hc) (N := k + 4) hHc_sm m (by omega) hm hαne' hc).symm
    rw [h1, norm_mul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hc.1.le _)]
    calc c ^ (2 * (k - m)) * ‖redCoef k α Hc m c‖ ≤ c ^ (2 * (k - m)) * C :=
          mul_le_mul_of_nonneg_left (hC c ⟨hc.1.le, hc.2.le⟩) (pow_nonneg hc.1.le _)
      _ = C * c ^ (2 * (k - m)) := by ring
  -- differentiability of the two chains
  have hdiff_f : ∀ m, m + 1 ≤ k → ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      DifferentiableAt ℝ (abelReduceIter α m (abelTrans α γext)) x := by
    intro m hm x hx
    have hpos : 0 < α - (m : ℝ) := by
      have hm' : (m : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast hm
      rw [hαk]; linarith
    have hd : DifferentiableAt ℝ (abelTrans (α - (m : ℝ)) γext) x :=
      (AbelDirect.hasDerivAt_abelTrans_direct hpos hγext_sm1.contDiffOn hx).differentiableAt
    exact hd.congr_of_eventuallyEq
      ((hchainj m (by omega)).eventuallyEq_of_mem (isOpen_Ioo.mem_nhds hx))
  have hdiff_g : ∀ m ≤ k, ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      DifferentiableAt ℝ (abelReduceIter α m Kx) x := by
    intro m hm x hx
    have hαne' : ∀ i < m, α - (i : ℝ) ≠ 0 := fun i hi => hαne i (lt_of_lt_of_le hi hm)
    have hsm := contDiff_redCoef (m := k) (α := α) (H := Hc) (N := k + 4) hHc_sm m (by omega) hαne'
    have hne : (((k + 4) - m : ℕ) : WithTop ℕ∞) ≠ 0 := by
      exact_mod_cast (by omega : (k + 4) - m ≠ 0)
    have hd : DifferentiableAt ℝ (fun c : ℝ => c ^ (2 * (k - m)) * redCoef k α Hc m c) x :=
      ((contDiff_id.pow _).mul (hsm.of_le (by simp))).differentiable hne |>.differentiableAt
    exact hd.congr_of_eventuallyEq
      (((eqOn_redCoef (m := k) (α := α) (H := Hc) (N := k + 4) hHc_sm m (by omega) hm hαne').eventuallyEq_of_mem
        (isOpen_Ioo.mem_nhds hx)).symm)
  -- the downward induction
  have hfg : Set.EqOn (abelTrans α γext) Kx (Set.Ioo (0 : ℝ) 1) := by
    have key : ∀ i ≤ k, Set.EqOn (abelReduceIter α (k - i) (abelTrans α γext))
        (abelReduceIter α (k - i) Kx) (Set.Ioo (0 : ℝ) 1) := by
      intro i
      induction i with
      | zero =>
        intro _
        simpa using hUk
      | succ i ih =>
        intro hi
        have hik : i ≤ k := by omega
        set m : ℕ := k - i - 1 with hm
        have hmk : m + 1 ≤ k := by omega
        have hIH : Set.EqOn (abelReduceIter α (m + 1) (abelTrans α γext))
            (abelReduceIter α (m + 1) Kx) (Set.Ioo (0 : ℝ) 1) := by
          have h := ih hik
          have hki : k - i = m + 1 := by omega
          rwa [hki] at h
        have hgoal : k - (i + 1) = m := by omega
        rw [hgoal]
        have hder_all : Set.EqOn (deriv (abelReduceIter α m (abelTrans α γext)))
            (deriv (abelReduceIter α m Kx)) (Set.Ioo (0 : ℝ) 1) := by
          intro y hy
          have hred : abelReduce (α - (m : ℝ)) (abelReduceIter α m (abelTrans α γext)) y
              = abelReduce (α - (m : ℝ)) (abelReduceIter α m Kx) y := by
            have h := hIH hy
            rw [abelReduceIter_succ' α m (abelTrans α γext), abelReduceIter_succ' α m Kx] at h
            exact h
          simp only [abelReduce] at hred
          have hb : (2 * (α - (m : ℝ)) * y) ≠ 0 := by
            have hpos : 0 < α - (m : ℝ) := by
              have hm' : (m : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast hmk
              rw [hαk]; linarith
            exact mul_ne_zero (mul_ne_zero (by norm_num) (ne_of_gt hpos)) (ne_of_gt hy.1)
          have h2 := congrArg (fun z : ℝ => z * (2 * (α - (m : ℝ)) * y)) hred
          rwa [div_mul_cancel₀ _ hb, div_mul_cancel₀ _ hb] at h2
        have hd0 : Set.EqOn (deriv ((abelReduceIter α m (abelTrans α γext)) - (abelReduceIter α m Kx)))
            0 (Set.Ioo (0 : ℝ) 1) := by
          intro y hy
          rw [deriv_sub (hdiff_f m hmk y hy) (hdiff_g m (by omega) y hy), hder_all hy, sub_self]
          rfl
        have hconst : ∀ x y, x ∈ Set.Ioo (0 : ℝ) 1 → y ∈ Set.Ioo (0 : ℝ) 1 →
            abelReduceIter α m (abelTrans α γext) x - abelReduceIter α m Kx x
              = abelReduceIter α m (abelTrans α γext) y - abelReduceIter α m Kx y :=
          fun x y hx hy => isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
            (fun z hz => ((hdiff_f m hmk z hz).sub (hdiff_g m (by omega) z hz)).differentiableWithinAt)
            hd0 hx hy
        intro x hx
        obtain ⟨Cf, hCf⟩ := hbound_f m hmk
        obtain ⟨Cg, hCg⟩ := hbound_g m (by omega)
        have hbnd : ∀ y ∈ Set.Ioo (0 : ℝ) 1,
            |abelReduceIter α m (abelTrans α γext) x - abelReduceIter α m Kx x|
              ≤ (Cf + Cg) * y ^ (2 * (k - m)) := by
          intro y hy
          have hxy := hconst x y hx hy
          calc |abelReduceIter α m (abelTrans α γext) x - abelReduceIter α m Kx x|
              = |abelReduceIter α m (abelTrans α γext) y - abelReduceIter α m Kx y| := by rw [hxy]
            _ ≤ ‖abelReduceIter α m (abelTrans α γext) y‖ + ‖abelReduceIter α m Kx y‖ := by
                rw [← Real.norm_eq_abs]
                exact norm_sub_le _ _
            _ ≤ Cf * y ^ (2 * (k - m)) + Cg * y ^ (2 * (k - m)) := add_le_add (hCf y hy) (hCg y hy)
            _ = (Cf + Cg) * y ^ (2 * (k - m)) := by ring
        have htend : Filter.Tendsto (fun y : ℝ => (Cf + Cg) * y ^ (2 * (k - m)))
            (𝓝[>] (0 : ℝ)) (𝓝 0) := by
          have h0 : Filter.Tendsto (fun y : ℝ => (Cf + Cg) * y ^ (2 * (k - m))) (𝓝 (0 : ℝ))
              (𝓝 ((Cf + Cg) * (0 : ℝ) ^ (2 * (k - m)))) :=
            (continuousAt_const.mul (continuousAt_id.pow _)).tendsto
          have hz : (Cf + Cg) * (0 : ℝ) ^ (2 * (k - m)) = 0 := by
            rw [zero_pow (by omega : 2 * (k - m) ≠ 0), mul_zero]
          rw [hz] at h0
          exact h0.mono_left nhdsWithin_le_nhds
        have hmem : ∀ᶠ y in 𝓝[>] (0 : ℝ), y ∈ Set.Ioo (0 : ℝ) 1 :=
          Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)
        have hev : ∀ᶠ y in 𝓝[>] (0 : ℝ),
            |abelReduceIter α m (abelTrans α γext) x - abelReduceIter α m Kx x|
              ≤ (Cf + Cg) * y ^ (2 * (k - m)) := hmem.mono hbnd
        have hle : |abelReduceIter α m (abelTrans α γext) x - abelReduceIter α m Kx x| ≤ 0 :=
          ge_of_tendsto htend hev
        exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hle (abs_nonneg _)))
    intro c hc
    have h := key k le_rfl
    simpa using h hc
  -- conclusion
  intro c hc
  have h1 : abelTrans α (radonInverse n F) c = abelTrans α γext c :=
    RI.abelTrans_congr hc.1 (fun y hy => (hγext_eq_γ y ⟨hy.1, lt_trans hy.2 hc.2⟩).symm)
  rw [h1, hfg hc]
  exact (hK_eq hc).symm

end Work.OddRadon

end
