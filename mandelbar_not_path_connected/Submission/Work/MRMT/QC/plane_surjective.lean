import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# A continuous map of `ℂ` that is asymptotically the identity is onto ("degree one at infinity")

Mathlib has no planar degree theory, so the *argument change* of a plane loop is set up here from
scratch.  Everything rests on the explicit argument function
`t ↦ Real.arcsin ((γ t / ‖γ t‖).im)` of a loop with values in the right half plane.

Main result: `Work.MRMT.QC.surjective_of_tendsto_sub_id` — if `f : ℂ → ℂ` is continuous and
`f z - z → 0` as `z → ∞`, then `f` is surjective.

This is used to upgrade the principal normalisation `φ z = z + O(1/z)` of a quasiconformal map to
a homeomorphism of `ℂ` *without* invoking the Reshetnyak/Stoilow openness theorem (which is still
unproved in this workspace).  The whole file is axiom-clean and depends on Mathlib only.
-/

noncomputable section

open MeasureTheory Filter Complex
open scoped Topology

namespace Work.MRMT.QC

/-- The positively oriented circle of radius `R`, as a `1`-periodic loop. -/
def circLoop (R : ℝ) (t : ℝ) : ℂ :=
  (R : ℂ) * Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I)

theorem continuous_circLoop (R : ℝ) : Continuous (circLoop R) := by
  unfold circLoop; fun_prop

theorem circLoop_zero (R : ℝ) : circLoop R 0 = (R : ℂ) := by simp [circLoop]

theorem circLoop_one (R : ℝ) : circLoop R 1 = (R : ℂ) := by
  have h1 : ((2 * Real.pi * 1 : ℝ) : ℂ) * Complex.I = 2 * (Real.pi : ℂ) * Complex.I := by
    push_cast; ring
  rw [circLoop, h1, Complex.exp_two_pi_mul_I, mul_one]

theorem norm_circLoop {R : ℝ} (hR : 0 ≤ R) (t : ℝ) : ‖circLoop R t‖ = R := by
  have hre : (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I).re = 0 := by
    simp [Complex.mul_re]
  rw [circLoop, norm_mul, Complex.norm_exp, hre, Real.exp_zero, mul_one, Complex.norm_real,
    Real.norm_of_nonneg hR]

/-- `Θ` is a continuous argument function of the loop `γ` on `[0,1]`. -/
def IsArgFunOn (γ : ℝ → ℂ) (Θ : ℝ → ℝ) : Prop :=
  ContinuousOn Θ (Set.Icc 0 1) ∧
    ∀ t ∈ Set.Icc (0 : ℝ) 1, γ t = (‖γ t‖ : ℂ) * Complex.exp ((Θ t : ℂ) * Complex.I)

/-- `γ` has *argument change* `2πk`. -/
def HasArgChange (γ : ℝ → ℂ) (k : ℤ) : Prop :=
  ∃ Θ : ℝ → ℝ, IsArgFunOn γ Θ ∧ Θ 1 - Θ 0 = 2 * Real.pi * k

theorem norm_mul_exp_arcsin_mul_I (z : ℂ) (hz : 0 < z.re) :
    (‖z‖ : ℂ) * Complex.exp (((Real.arcsin ((z / (‖z‖ : ℂ)).im)) : ℂ) * Complex.I) = z := by
  have hzne : z ≠ 0 := fun h => by rw [h] at hz; simp at hz
  have hρ : (0 : ℝ) < ‖z‖ := norm_pos_iff.mpr hzne
  set c : ℂ := z / (‖z‖ : ℂ) with hc
  have hc_eq : c = ((‖z‖ : ℝ)⁻¹ : ℂ) * z := by rw [hc, div_eq_inv_mul]
  have hcre : c.re = z.re / ‖z‖ := by
    rw [hc_eq, Complex.mul_re, ← Complex.ofReal_inv, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero]
    rw [inv_mul_eq_div]
  have hcnorm : ‖c‖ = 1 := by
    rw [hc, norm_div, Complex.norm_real, Real.norm_of_nonneg hρ.le, div_self (ne_of_gt hρ)]
  have hcrepos : 0 < c.re := by rw [hcre]; exact div_pos hz hρ
  have hcsq : c.re ^ 2 + c.im ^ 2 = 1 := by
    have h := Complex.normSq_apply c
    rw [Complex.normSq_eq_norm_sq, hcnorm] at h
    norm_num at h
    nlinarith [h]
  have hcim_le : -1 ≤ c.im ∧ c.im ≤ 1 := by
    have h := Complex.abs_im_le_norm c
    rw [hcnorm] at h
    exact abs_le.mp h
  have hcre_sqrt : c.re = Real.sqrt (1 - c.im ^ 2) := by
    have h1 : (1 : ℝ) - c.im ^ 2 = c.re ^ 2 := by linarith [hcsq]
    rw [h1, Real.sqrt_sq (le_of_lt hcrepos)]
  have hexp : Complex.exp (((Real.arcsin c.im) : ℂ) * Complex.I) = c := by
    refine Complex.ext ?_ ?_
    · rw [Complex.exp_ofReal_mul_I_re, Real.cos_arcsin, hcre_sqrt]
    · rw [Complex.exp_ofReal_mul_I_im, Real.sin_arcsin hcim_le.1 hcim_le.2]
  rw [hexp, hc]
  exact mul_div_cancel₀ z (by simpa using (ne_of_gt hρ))

theorem isArgFunOn_arcsin {r : ℝ → ℂ} (hc : ContinuousOn r (Set.Icc 0 1))
    (hpos : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 < (r t).re) :
    IsArgFunOn r (fun t => Real.arcsin ((r t / (‖r t‖ : ℂ)).im)) := by
  refine ⟨?_, fun t ht => (norm_mul_exp_arcsin_mul_I (r t) (hpos t ht)).symm⟩
  refine Real.continuous_arcsin.comp_continuousOn ?_
  refine Complex.continuous_im.comp_continuousOn ?_
  refine ContinuousOn.div hc ?_ ?_
  · exact Complex.continuous_ofReal.comp_continuousOn (continuous_norm.comp_continuousOn hc)
  · intro t ht
    have h := hpos t ht
    have hr : r t ≠ 0 := fun h0 => by rw [h0] at h; simp at h
    exact Complex.ofReal_ne_zero.mpr (ne_of_gt (norm_pos_iff.mpr hr))

theorem IsArgFunOn.congr {γ γ' : ℝ → ℂ} {Θ : ℝ → ℝ} (h : IsArgFunOn γ Θ)
    (heq : ∀ t ∈ Set.Icc (0 : ℝ) 1, γ t = γ' t) : IsArgFunOn γ' Θ :=
  ⟨h.1, fun t ht => by
    have h2 := h.2 t ht
    simpa only [heq t ht] using h2⟩

theorem isArgFunOn_mul {γ₁ γ₂ : ℝ → ℂ} {Θ₁ Θ₂ : ℝ → ℝ} (h₁ : IsArgFunOn γ₁ Θ₁)
    (h₂ : IsArgFunOn γ₂ Θ₂) :
    IsArgFunOn (fun t => γ₁ t * γ₂ t) (fun t => Θ₁ t + Θ₂ t) := by
  refine ⟨h₁.1.add h₂.1, fun t ht => ?_⟩
  have hnorm : (‖γ₁ t * γ₂ t‖ : ℂ) = (‖γ₁ t‖ : ℂ) * (‖γ₂ t‖ : ℂ) := by
    rw [norm_mul]; push_cast; ring
  have hexp : Complex.exp ((Θ₁ t : ℂ) * Complex.I) * Complex.exp ((Θ₂ t : ℂ) * Complex.I)
      = Complex.exp (((Θ₁ t + Θ₂ t : ℝ)) * Complex.I) := by
    rw [← Complex.exp_add]; push_cast; ring_nf
  have hL : (‖γ₁ t‖ : ℂ) * Complex.exp ((Θ₁ t : ℂ) * Complex.I)
        * ((‖γ₂ t‖ : ℂ) * Complex.exp ((Θ₂ t : ℂ) * Complex.I))
      = ((‖γ₁ t‖ : ℂ) * (‖γ₂ t‖ : ℂ))
        * (Complex.exp ((Θ₁ t : ℂ) * Complex.I) * Complex.exp ((Θ₂ t : ℂ) * Complex.I)) := by
    ring
  simp only []
  conv_lhs => rw [h₁.2 t ht, h₂.2 t ht]
  rw [hL, hexp, hnorm]

theorem isArgFunOn_mul_of_re_pos {γ r : ℝ → ℂ} {Θ : ℝ → ℝ} (h : IsArgFunOn γ Θ)
    (hr : ContinuousOn r (Set.Icc 0 1)) (hpos : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 < (r t).re) :
    IsArgFunOn (fun t => γ t * r t)
      (fun t => Θ t + Real.arcsin ((r t / (‖r t‖ : ℂ)).im)) :=
  isArgFunOn_mul h (isArgFunOn_arcsin hr hpos)

theorem hasArgChange_congr {γ γ' : ℝ → ℂ} {k : ℤ} (h : HasArgChange γ k)
    (heq : ∀ t, γ t = γ' t) : HasArgChange γ' k := by
  obtain ⟨Θ, hA, hΔ⟩ := h
  exact ⟨Θ, hA.congr fun t _ => heq t, hΔ⟩

theorem hasArgChange_mul {γ₁ γ₂ : ℝ → ℂ} {k₁ k₂ : ℤ} (h₁ : HasArgChange γ₁ k₁)
    (h₂ : HasArgChange γ₂ k₂) :
    HasArgChange (fun t => γ₁ t * γ₂ t) (k₁ + k₂) := by
  obtain ⟨Θ₁, hA₁, hΔ₁⟩ := h₁
  obtain ⟨Θ₂, hA₂, hΔ₂⟩ := h₂
  refine ⟨fun t => Θ₁ t + Θ₂ t, isArgFunOn_mul hA₁ hA₂, ?_⟩
  have h1' : Θ₁ 1 - Θ₁ 0 = 2 * Real.pi * (k₁ : ℝ) := hΔ₁
  have h2' : Θ₂ 1 - Θ₂ 0 = 2 * Real.pi * (k₂ : ℝ) := hΔ₂
  have hgoal : 2 * Real.pi * ((k₁ + k₂ : ℤ) : ℝ)
      = 2 * Real.pi * (k₁ : ℝ) + 2 * Real.pi * (k₂ : ℝ) := by
    push_cast; ring
  rw [hgoal]
  linarith

theorem hasArgChange_const (c : ℂ) (hc : c ≠ 0) : HasArgChange (fun _ : ℝ => c) 0 :=
  ⟨fun _ => Complex.arg c, ⟨continuousOn_const, fun t _ => (Complex.norm_mul_exp_arg_mul_I c).symm⟩,
    by simp⟩

theorem hasArgChange_of_close {γ γ' : ℝ → ℂ} {k : ℤ} (h : HasArgChange γ k)
    (hloop : γ 1 = γ 0) (hloop' : γ' 1 = γ' 0) (hγ : ContinuousOn γ (Set.Icc 0 1))
    (hγ' : ContinuousOn γ' (Set.Icc 0 1))
    (hclose : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖γ' t - γ t‖ < ‖γ t‖) :
    HasArgChange γ' k := by
  obtain ⟨Θ, hA, hΔ⟩ := h
  have hne : ∀ t ∈ Set.Icc (0 : ℝ) 1, γ t ≠ 0 := by
    intro t ht h0
    have h := hclose t ht
    rw [h0, norm_zero, sub_zero] at h
    linarith [norm_nonneg (γ' t)]
  have hpos : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 < ((γ' / γ) t).re := by
    intro t ht
    have hlt : ‖(γ' / γ) t - 1‖ < 1 := by
      have hγne : γ t ≠ 0 := hne t ht
      have h1 : (γ' / γ) t - 1 = (γ' t - γ t) / γ t := by
        simp only [Pi.div_apply]
        field_simp
      rw [h1, norm_div, div_lt_one (norm_pos_iff.mpr hγne)]
      exact hclose t ht
    have h2 : -1 < ((γ' / γ) t - 1).re := by
      have h3 : |((γ' / γ) t - 1).re| ≤ ‖(γ' / γ) t - 1‖ := Complex.abs_re_le_norm _
      have h4 : -|((γ' / γ) t - 1).re| ≤ ((γ' / γ) t - 1).re := neg_abs_le _
      linarith
    have h5 : ((γ' / γ) t).re = ((γ' / γ) t - 1).re + 1 := by simp
    linarith
  have hloopr : (γ' / γ) 1 = (γ' / γ) 0 := by
    simp only [Pi.div_apply]; rw [hloop', hloop]
  have hcont : ContinuousOn (γ' / γ) (Set.Icc 0 1) :=
    hγ'.div hγ fun t ht => hne t ht
  have hsplit : ∀ t ∈ Set.Icc (0 : ℝ) 1, γ t * (γ' / γ) t = γ' t := by
    intro t ht
    have hγne : γ t ≠ 0 := hne t ht
    simp only [Pi.div_apply]
    field_simp
  refine ⟨fun t => Θ t + Real.arcsin (((γ' / γ) t / (‖(γ' / γ) t‖ : ℂ)).im),
    (isArgFunOn_mul_of_re_pos hA hcont hpos).congr hsplit, ?_⟩
  have hψ : Real.arcsin (((γ' / γ) 1 / (‖(γ' / γ) 1‖ : ℂ)).im)
      - Real.arcsin (((γ' / γ) 0 / (‖(γ' / γ) 0‖ : ℂ)).im) = 0 := by rw [hloopr]; ring
  have h4 : (Θ 1 + Real.arcsin (((γ' / γ) 1 / (‖(γ' / γ) 1‖ : ℂ)).im))
      - (Θ 0 + Real.arcsin (((γ' / γ) 0 / (‖(γ' / γ) 0‖ : ℂ)).im)) = 2 * Real.pi * k := by
    linarith [hΔ, hψ]
  simpa using h4

theorem argFun_diff_mem_multiples {γ : ℝ → ℂ} {Θ₁ Θ₀ : ℝ → ℝ} (h₁ : IsArgFunOn γ Θ₁)
    (h₀ : IsArgFunOn γ Θ₀) (hne : ∀ t ∈ Set.Icc (0 : ℝ) 1, γ t ≠ 0) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, ∃ m : ℤ, Θ₁ t - Θ₀ t = 2 * Real.pi * m := by
  intro t ht
  have hnorm : (‖γ t‖ : ℂ) ≠ 0 := by
    have h := hne t ht
    exact Complex.ofReal_ne_zero.mpr (ne_of_gt (norm_pos_iff.mpr h))
  have hprod : (‖γ t‖ : ℂ) * Complex.exp ((Θ₁ t : ℂ) * Complex.I)
      = (‖γ t‖ : ℂ) * Complex.exp ((Θ₀ t : ℂ) * Complex.I) := by
    rw [← h₁.2 t ht, ← h₀.2 t ht]
  have heq : Complex.exp ((Θ₁ t : ℂ) * Complex.I) = Complex.exp ((Θ₀ t : ℂ) * Complex.I) :=
    mul_left_cancel₀ hnorm hprod
  have hone : Complex.exp (((Θ₁ t : ℂ) * Complex.I) - ((Θ₀ t : ℂ) * Complex.I)) = 1 := by
    rw [Complex.exp_sub, heq, div_self (Complex.exp_ne_zero _)]
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp hone
  refine ⟨n, ?_⟩
  have hI : ((Θ₁ t - Θ₀ t : ℝ) : ℂ) * Complex.I = ((n : ℂ) * (2 * Real.pi)) * Complex.I := by
    push_cast
    linear_combination hn
  have hfinal : ((Θ₁ t - Θ₀ t : ℝ) : ℂ) = (n : ℂ) * (2 * Real.pi) := by
    have h2 := congrArg (fun z : ℂ => z / Complex.I) hI
    rw [mul_div_cancel_right₀ _ Complex.I_ne_zero] at h2
    simpa using h2
  have hreal : (Θ₁ t - Θ₀ t : ℝ) = (n : ℝ) * (2 * Real.pi) := by
    exact_mod_cast hfinal
  rw [hreal]; ring

theorem eq_endpoints_of_multiples {Θ : ℝ → ℝ} (hcont : ContinuousOn Θ (Set.Icc 0 1))
    (hval : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∃ m : ℤ, Θ t = 2 * Real.pi * m) : Θ 1 = Θ 0 := by
  by_contra hne
  obtain ⟨m, hm⟩ := hval 0 (by norm_num)
  obtain ⟨n, hn⟩ := hval 1 (by norm_num)
  have hmn : n ≠ m := by
    intro h
    exact hne (by rw [hm, hn, h])
  rcases lt_or_gt_of_ne hmn with hlt | hgt
  · -- Θ 1 < Θ 0
    have hstep' : (1 : ℝ) ≤ (m : ℝ) - (n : ℝ) := by
      have h1 : (1 : ℝ) ≤ ((m - n : ℤ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ m - n)
      simpa using h1
    have hmem : Θ 0 - Real.pi ∈ Set.Icc (Θ 1) (Θ 0) := by
      refine ⟨?_, by linarith [Real.pi_pos]⟩
      have h2 : Real.pi ≤ 2 * Real.pi * (m : ℝ) - 2 * Real.pi * (n : ℝ) := by
        nlinarith [hstep', Real.pi_pos]
      rw [hm, hn]; push_cast
      linarith
    obtain ⟨t, ht, htval⟩ := intermediate_value_Icc' zero_le_one hcont hmem
    obtain ⟨k, hk⟩ := hval t ht
    have hk' : 2 * Real.pi * (k : ℝ) = 2 * Real.pi * (m : ℝ) - Real.pi := by
      rw [← hk, htval, hm]
    have hgoal : 2 * Real.pi * (((k - m : ℤ)) : ℝ) = -Real.pi := by
      have h5 : (((k - m : ℤ)) : ℝ) = (k : ℝ) - (m : ℝ) := by simp only [Int.cast_sub]
      rw [h5]; linarith
    have h3 : (2 * (((k - m : ℤ)) : ℝ) + 1) * Real.pi = 0 := by linarith [hgoal]
    rcases mul_eq_zero.mp h3 with h4 | h4
    · have h6 : (2 * (((k - m : ℤ)) : ℝ) + 1 : ℝ) = 0 := by linarith [h4]
      have h5 : (2 * (k - m) + 1 : ℤ) = 0 := by exact_mod_cast h6
      omega
    · exact Real.pi_ne_zero h4
  · -- Θ 0 < Θ 1
    have hstep' : (1 : ℝ) ≤ (n : ℝ) - (m : ℝ) := by
      have h1 : (1 : ℝ) ≤ ((n - m : ℤ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ n - m)
      simpa using h1
    have hmem : Θ 0 + Real.pi ∈ Set.Icc (Θ 0) (Θ 1) := by
      refine ⟨by linarith [Real.pi_pos], ?_⟩
      have h2 : Real.pi ≤ 2 * Real.pi * (n : ℝ) - 2 * Real.pi * (m : ℝ) := by
        nlinarith [hstep', Real.pi_pos]
      rw [hm, hn]; push_cast
      linarith
    obtain ⟨t, ht, htval⟩ := intermediate_value_Icc zero_le_one hcont hmem
    obtain ⟨k, hk⟩ := hval t ht
    have hk' : 2 * Real.pi * (k : ℝ) = 2 * Real.pi * (m : ℝ) + Real.pi := by
      rw [← hk, htval, hm]
    have hgoal : 2 * Real.pi * (((k - m : ℤ)) : ℝ) = Real.pi := by
      have h5 : (((k - m : ℤ)) : ℝ) = (k : ℝ) - (m : ℝ) := by simp only [Int.cast_sub]
      rw [h5]; linarith
    have h3 : (2 * (((k - m : ℤ)) : ℝ) - 1) * Real.pi = 0 := by linarith [hgoal]
    rcases mul_eq_zero.mp h3 with h4 | h4
    · have h6 : (2 * (((k - m : ℤ)) : ℝ) - 1 : ℝ) = 0 := by linarith [h4]
      have h5 : (2 * (k - m) - 1 : ℤ) = 0 := by exact_mod_cast h6
      omega
    · exact Real.pi_ne_zero h4

theorem surjective_of_tendsto_sub_id {f : ℂ → ℂ} (hf : Continuous f)
    (h : Filter.Tendsto (fun z : ℂ => f z - z) (Filter.cocompact ℂ) (nhds 0)) :
    Function.Surjective f := by
  intro w
  have hbound : ∃ R₀ : ℝ, ∀ z : ℂ, R₀ ≤ ‖z‖ → ‖f z - z‖ < 1 / 2 := by
    have h1 : ∀ᶠ z : ℂ in Filter.cocompact ℂ, ‖f z - z‖ < 1 / 2 := by
      have := (Metric.tendsto_nhds.mp h) (1 / 2) (by norm_num)
      simpa [dist_eq_norm] using this
    rw [Filter.eventually_iff, Filter.mem_cocompact] at h1
    obtain ⟨K, hK, hKu⟩ := h1
    obtain ⟨C, hC⟩ := hK.isBounded.exists_norm_le
    refine ⟨C + 1, fun z hz => hKu (fun hzK => ?_)⟩
    linarith [hC z hzK]
  obtain ⟨R₀, hR₀⟩ := hbound
  by_contra hw
  set R : ℝ := max R₀ (‖w‖ + 2) with hRdef
  have hR₀' : R₀ ≤ R := le_max_left _ _
  have hRw : ‖w‖ + 2 ≤ R := le_max_right _ _
  have hRpos : 0 < R := by linarith [norm_nonneg w]
  have hmem_closed : ∀ z ∈ Metric.closedBall (0 : ℂ) R, f z ≠ w := by
    intro z hz hzw
    exact hw ⟨z, hzw⟩
  set γ : ℝ → ℂ := fun t => f (circLoop R t) - w with hγdef
  have hγcont : Continuous γ := (hf.comp (continuous_circLoop R)).sub continuous_const
  have hγne : ∀ t ∈ Set.Icc (0 : ℝ) 1, γ t ≠ 0 := by
    intro t ht
    have hnorm : ‖circLoop R t‖ = R := norm_circLoop hRpos.le t
    have hmem : circLoop R t ∈ Metric.closedBall (0 : ℂ) R := by
      simp only [Metric.mem_closedBall, dist_zero_right, hnorm]; exact le_rfl
    exact sub_ne_zero.mpr (hmem_closed _ hmem)
  set v : ℝ → ℂ := fun t => 1 - w / circLoop R t with hvdef
  set u : ℝ → ℂ := fun t => (f (circLoop R t) - w) / (circLoop R t - w) with hudef
  have hvpos : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 < (v t).re := by
    intro t ht
    have hz : ‖circLoop R t‖ = R := norm_circLoop hRpos.le t
    have hq : ‖w / circLoop R t‖ < 1 := by
      rw [norm_div, hz, div_lt_one hRpos]
      linarith
    have hv : v t = 1 - w / circLoop R t := rfl
    rw [hv]
    have hre : (w / circLoop R t).re ≤ ‖w / circLoop R t‖ := Complex.re_le_norm _
    simp only [sub_re, one_re]
    linarith
  have hupos : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 < (u t).re := by
    intro t ht
    have hz : ‖circLoop R t‖ = R := norm_circLoop hRpos.le t
    have hdec : ‖f (circLoop R t) - circLoop R t‖ < 1 / 2 := hR₀ _ (by rw [hz]; exact hR₀')
    have hden : R - ‖w‖ ≤ ‖circLoop R t - w‖ := by
      have h := abs_norm_sub_norm_le (circLoop R t) w
      have h2 : ‖circLoop R t‖ - ‖w‖ ≤ |‖circLoop R t‖ - ‖w‖| := le_abs_self _
      rw [hz] at h h2
      linarith
    have hdenpos : 0 < ‖circLoop R t - w‖ := by linarith [hRw]
    have hratio : ‖(f (circLoop R t) - circLoop R t) / (circLoop R t - w)‖ < 1 := by
      rw [norm_div, div_lt_one hdenpos]
      linarith [hden, hdec]
    have hu : u t = 1 + (f (circLoop R t) - circLoop R t) / (circLoop R t - w) := by
      rw [hudef]
      simp only []
      have h1 : f (circLoop R t) - w
          = (circLoop R t - w) + (f (circLoop R t) - circLoop R t) := by ring
      have hzw : circLoop R t - w ≠ 0 := norm_pos_iff.mp hdenpos
      rw [h1, add_div, div_self hzw]
    rw [hu]
    have hre2 : -‖(f (circLoop R t) - circLoop R t) / (circLoop R t - w)‖
        ≤ ((f (circLoop R t) - circLoop R t) / (circLoop R t - w)).re := by
      have h3 := Complex.abs_re_le_norm ((f (circLoop R t) - circLoop R t) / (circLoop R t - w))
      have h4 : -|((f (circLoop R t) - circLoop R t) / (circLoop R t - w)).re|
          ≤ ((f (circLoop R t) - circLoop R t) / (circLoop R t - w)).re := neg_abs_le _
      have h5 : |((f (circLoop R t) - circLoop R t) / (circLoop R t - w)).re|
          ≤ ‖(f (circLoop R t) - circLoop R t) / (circLoop R t - w)‖ := Complex.abs_re_le_norm _
      linarith
    simp only [add_re, one_re]
    linarith
  have hvloop : v 1 = v 0 := by rw [hvdef]; simp [circLoop_one, circLoop_zero]
  have huloop : u 1 = u 0 := by rw [hudef]; simp [circLoop_one, circLoop_zero]
  have hvcont : ContinuousOn v (Set.Icc 0 1) := by
    rw [hvdef]
    refine ContinuousOn.sub continuousOn_const ?_
    refine ContinuousOn.div continuousOn_const (continuous_circLoop R).continuousOn ?_
    intro t ht h0
    have h := norm_circLoop hRpos.le t
    rw [h0, norm_zero] at h
    linarith [hRpos]
  have hucont : ContinuousOn u (Set.Icc 0 1) := by
    rw [hudef]
    refine ContinuousOn.div ?_ ?_ ?_
    · exact ((hf.comp (continuous_circLoop R)).sub continuous_const).continuousOn
    · exact ((continuous_circLoop R).sub continuous_const).continuousOn
    · intro t ht h0
      have h1 : circLoop R t = w := sub_eq_zero.mp h0
      have h2 := norm_circLoop hRpos.le t
      rw [h1] at h2
      linarith [hRw]
  have hcirc : HasArgChange (fun t => circLoop R t) 1 := by
    refine ⟨fun t => 2 * Real.pi * t, ⟨by fun_prop, fun t _ => ?_⟩, by norm_num⟩
    simp only []
    rw [norm_circLoop hRpos.le t]
    rfl
  have hv : HasArgChange v 0 := by
    refine ⟨fun t => Real.arcsin ((v t / (‖v t‖ : ℂ)).im),
      isArgFunOn_arcsin hvcont hvpos, ?_⟩
    have h1 : Real.arcsin ((v 1 / (‖v 1‖ : ℂ)).im)
        = Real.arcsin ((v 0 / (‖v 0‖ : ℂ)).im) := by rw [hvloop]
    simp only []
    rw [h1]
    ring
  have hu : HasArgChange u 0 := by
    refine ⟨fun t => Real.arcsin ((u t / (‖u t‖ : ℂ)).im),
      isArgFunOn_arcsin hucont hupos, ?_⟩
    have h1 : Real.arcsin ((u 1 / (‖u 1‖ : ℂ)).im)
        = Real.arcsin ((u 0 / (‖u 0‖ : ℂ)).im) := by rw [huloop]
    simp only []
    rw [h1]
    ring
  have hprod : HasArgChange (fun t => circLoop R t * (v t * u t)) 1 := by
    have h1 := hasArgChange_mul hcirc (hasArgChange_mul hv hu)
    simpa using h1
  have hγ_eq : ∀ t, circLoop R t * (v t * u t) = γ t := by
    intro t
    rw [hvdef, hudef, hγdef]
    simp only []
    have hz : circLoop R t ≠ 0 := fun h0 => by
      have := norm_circLoop hRpos.le t; rw [h0, norm_zero] at this; linarith
    have hzw : circLoop R t - w ≠ 0 := by
      intro h0
      have h1 : circLoop R t = w := sub_eq_zero.mp h0
      have h2 := norm_circLoop hRpos.le t
      rw [h1] at h2
      linarith [hRw]
    field_simp
  have hA : HasArgChange γ 1 := hasArgChange_congr hprod hγ_eq
  set hfam : ℝ → ℝ → ℂ := fun s t => f ((s : ℂ) * circLoop R t) - w with hfamdef
  have hfam_ne : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1, hfam s t ≠ 0 := by
    intro s hs t ht
    have hnorm : ‖(s : ℂ) * circLoop R t‖ ≤ R := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hs.1, norm_circLoop hRpos.le]
      nlinarith [hs.2]
    have hmem : (s : ℂ) * circLoop R t ∈ Metric.closedBall (0 : ℂ) R := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hnorm
    exact sub_ne_zero.mpr (hmem_closed _ hmem)
  have hfam_cont : Continuous hfam := by rw [hfamdef]; fun_prop
  have hfam_contOn : ∀ s : ℝ, ContinuousOn (hfam s) (Set.Icc 0 1) := by
    intro s
    rw [hfamdef]
    exact ((hf.comp (continuous_const.mul (continuous_circLoop R))).sub
      continuous_const).continuousOn
  have hfam_loop : ∀ s : ℝ, hfam s 1 = hfam s 0 := by
    intro s; simp [hfamdef, circLoop_one, circLoop_zero]
  have huc : UniformContinuousOn (fun p : ℝ × ℝ => hfam p.1 p.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) := by
    have hcont : Continuous (fun p : ℝ × ℝ => hfam p.1 p.2) := by
      rw [hfamdef]
      simp only []
      exact (hf.comp ((Complex.continuous_ofReal.comp continuous_fst).mul
        ((continuous_circLoop R).comp continuous_snd))).sub continuous_const
    exact (isCompact_Icc.prod isCompact_Icc).uniformContinuousOn_of_continuous hcont.continuousOn
  have hloc : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∃ η > 0, ∀ s' ∈ Set.Icc (0 : ℝ) 1, |s' - s| < η →
      (HasArgChange (hfam s') 0 ↔ HasArgChange (hfam s) 0) := by
    intro s hs
    obtain ⟨t₀, ht₀, hmin⟩ := isCompact_Icc.exists_isMinOn ⟨0, by norm_num⟩
      ((hfam_contOn s).norm)
    set δ : ℝ := ‖hfam s t₀‖ with hδ
    have hδpos : 0 < δ := norm_pos_iff.mpr (hfam_ne s hs t₀ ht₀)
    obtain ⟨η, hη, hη'⟩ := Metric.uniformContinuousOn_iff.mp huc (δ / 2) (by linarith)
    refine ⟨η, hη, fun s' hs' hdist => ⟨fun h' => ?_, fun h' => ?_⟩⟩
    · refine hasArgChange_of_close h' (hfam_loop s') (hfam_loop s) (hfam_contOn s')
        (hfam_contOn s) ?_
      intro t ht
      have hd : dist (s', t) (s, t) < η := by
        rw [Prod.dist_eq, dist_eq_norm, dist_eq_norm, Real.norm_eq_abs, Real.norm_eq_abs,
          sub_self, abs_zero, max_eq_left (abs_nonneg _)]
        exact hdist
      have h1 : ‖hfam s' t - hfam s t‖ < δ / 2 := by
        have h2 := hη' (s', t) ⟨hs', ht⟩ (s, t) ⟨hs, ht⟩ hd
        rwa [dist_eq_norm] at h2
      have h3 : δ ≤ ‖hfam s t‖ := hmin ht
      have h4 : δ / 2 ≤ ‖hfam s' t‖ := by
        have h5 : ‖hfam s t‖ - ‖hfam s' t‖ ≤ ‖hfam s t - hfam s' t‖ := by
          have h6 := abs_norm_sub_norm_le (hfam s t) (hfam s' t)
          have h7 : ‖hfam s t‖ - ‖hfam s' t‖ ≤ |‖hfam s t‖ - ‖hfam s' t‖| := le_abs_self _
          linarith
        have h8 : ‖hfam s t - hfam s' t‖ = ‖hfam s' t - hfam s t‖ := norm_sub_rev _ _
        linarith
      have h9 : ‖hfam s t - hfam s' t‖ = ‖hfam s' t - hfam s t‖ := norm_sub_rev _ _
      linarith
    · refine hasArgChange_of_close h' (hfam_loop s) (hfam_loop s') (hfam_contOn s)
        (hfam_contOn s') ?_
      intro t ht
      have hd : dist (s, t) (s', t) < η := by
        rw [Prod.dist_eq, dist_eq_norm, dist_eq_norm, Real.norm_eq_abs, Real.norm_eq_abs,
          sub_self, abs_zero, max_eq_left (abs_nonneg _)]
        rwa [abs_sub_comm]
      have h1 : ‖hfam s t - hfam s' t‖ < δ / 2 := by
        have h2 := hη' (s, t) ⟨hs, ht⟩ (s', t) ⟨hs', ht⟩ hd
        rwa [dist_eq_norm] at h2
      have h3 : δ ≤ ‖hfam s t‖ := hmin ht
      have h9 : ‖hfam s' t - hfam s t‖ = ‖hfam s t - hfam s' t‖ := norm_sub_rev _ _
      linarith
  set S : Set ℝ := {s : ℝ | s ∈ Set.Icc (0 : ℝ) 1 ∧ HasArgChange (hfam s) 0} with hSdef
  have hS0 : (0 : ℝ) ∈ S := by
    refine ⟨⟨le_rfl, zero_le_one⟩, ?_⟩
    have h0 : hfam 0 = fun _ : ℝ => f 0 - w := by
      funext t; simp [hfamdef]
    rw [h0]
    refine hasArgChange_const (f 0 - w) (sub_ne_zero.mpr ?_)
    refine hmem_closed 0 ?_
    simp only [Metric.mem_closedBall, dist_zero_right, norm_zero]
    linarith [hRpos]
  have hbdd : BddAbove S := ⟨1, fun x hx => hx.1.2⟩
  have hSclosed : IsClosed S := by
    rw [← isOpen_compl_iff]
    rw [isOpen_iff_mem_nhds]
    intro x hx
    by_cases hxI : x ∈ Set.Icc (0 : ℝ) 1
    · obtain ⟨η, hη, hiff⟩ := hloc x hxI
      refine Filter.mem_of_superset (Metric.ball_mem_nhds x (show (0 : ℝ) < η / 2 by linarith)) ?_
      intro y hy hyS
      have hyI : y ∈ Set.Icc (0 : ℝ) 1 := hyS.1
      have hdist : |y - x| < η := by
        rw [Metric.mem_ball, dist_eq_norm, Real.norm_eq_abs] at hy
        linarith
      exact hx ⟨hxI, (hiff y hyI hdist).mp hyS.2⟩
    · have hopen := (isClosed_Icc (a := (0 : ℝ)) (b := 1)).isOpen_compl.mem_nhds hxI
      obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.mp hopen
      exact Filter.mem_of_superset (Metric.ball_mem_nhds x hε) fun y hy hyS => hsub hy hyS.1
  have hsSup_mem : sSup S ∈ S := IsClosed.csSup_mem hSclosed ⟨0, hS0⟩ hbdd
  have hsSup_le : sSup S ≤ 1 := csSup_le ⟨0, hS0⟩ (fun b hb => hb.1.2)
  have hsSup_eq : sSup S = 1 := by
    rcases lt_or_eq_of_le hsSup_le with hlt | heq
    · exfalso
      obtain ⟨η, hη, hiff⟩ := hloc (sSup S) hsSup_mem.1
      set ρ : ℝ := min (η / 2) ((1 - sSup S) / 2) with hρ
      have hρpos : 0 < ρ := lt_min (by linarith) (by linarith)
      have hs' : sSup S + ρ ∈ S := by
        refine ⟨⟨by linarith [hsSup_mem.1.1], by
          have h1 : ρ ≤ (1 - sSup S) / 2 := min_le_right _ _
          linarith⟩, ?_⟩
        refine (hiff _ ?_ ?_).mpr hsSup_mem.2
        · refine ⟨by linarith [hsSup_mem.1.1], by
            have h1 : ρ ≤ (1 - sSup S) / 2 := min_le_right _ _
            linarith⟩
        · have h2 : |sSup S + ρ - sSup S| < η := by
            rw [add_sub_cancel_left, abs_of_pos hρpos]
            have h1 : ρ ≤ η / 2 := min_le_left _ _
            linarith
          exact h2
      have hle := le_csSup hbdd hs'
      linarith
    · exact heq
  have hB : HasArgChange (hfam 1) 0 := (hsSup_eq ▸ hsSup_mem).2
  have hB' : HasArgChange γ 0 := by
    refine hasArgChange_congr hB (fun t => ?_)
    simp [hfamdef, hγdef]
  obtain ⟨Θ₁, hA₁, hΔ₁⟩ := hA
  obtain ⟨Θ₀, hA₀, hΔ₀⟩ := hB'
  have hmultiples := argFun_diff_mem_multiples hA₁ hA₀ hγne
  have hcont : ContinuousOn (fun t => Θ₁ t - Θ₀ t) (Set.Icc 0 1) := hA₁.1.sub hA₀.1
  have hend := eq_endpoints_of_multiples hcont hmultiples
  have hfin : 2 * Real.pi = 0 := by
    have h1 : Θ₁ 1 - Θ₁ 0 = 2 * Real.pi := by simpa using hΔ₁
    have h0 : Θ₀ 1 - Θ₀ 0 = 2 * Real.pi * (0 : ℝ) := by simpa using hΔ₀
    have h2 : Θ₁ 1 - Θ₁ 0 = Θ₀ 1 - Θ₀ 0 := by linarith [hend]
    rw [h1] at h2
    rw [h0, mul_zero] at h2
    linarith
  exact Real.pi_ne_zero (by linarith [hfin])


end Work.MRMT.QC
