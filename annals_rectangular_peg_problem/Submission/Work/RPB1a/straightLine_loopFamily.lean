import Mathlib
import Submission.Work.RPB1a.Defs
import Submission.Work.RPB1a.biLipschitz_loop
import Submission.Work.RPA3.periodic_mem_Icc
import Submission.Work.RPB.B5.periodic_norm_min_pos

/-!
# RPB1a N2: the straight-line isotopy between `C¹`-close loops

Every smooth loop `u` has a `C¹`-neighbourhood (in the uniform norm on the derivative) consisting
of loops: for `v` with `‖deriv v − deriv u‖ < ε`, the straight-line interpolant
`(s,t) ↦ u t + s (v t − u t)` is a `IsLoopFamily`.

The analytic content is
* `biLipschitz_loop` (delegated, file `biLipschitz_loop.lean`): the uniform local lower bound
  `c |h| ≤ ‖u (t+h) − u t‖` for `|h| ≤ π`, from which the injectivity of every interpolant follows;
* `min_deriv_pos`: a positive lower bound for `‖deriv u‖`, from which the immersion of every
  interpolant follows.

Everything else is the mean value inequality for the perturbation `v − u`.
-/

set_option autoImplicit false

open Complex Set Metric
open scoped ContDiff Real
open Work.RPB1a

noncomputable section

namespace Work.RPB1a

/-- `‖(s : ℂ)‖ = |s|`. -/
private lemma norm_ofReal' (s : ℝ) : ‖(s : ℂ)‖ = |s| := by
  rw [Complex.norm_def, Complex.normSq_ofReal, ← sq, Real.sqrt_sq_eq_abs]

/-- `deriv u` is `2π`-periodic when `u` is. -/
private lemma deriv_periodic {u : ℝ → ℂ} (hu : ∀ t, u (t + 2 * π) = u t) :
    ∀ t, deriv u (t + 2 * π) = deriv u t := by
  intro t
  have h1 : deriv (fun s : ℝ => u (2 * π + s)) t = deriv u (2 * π + t) :=
    deriv_comp_const_add u (2 * π) t
  have h2 : (fun s : ℝ => u (2 * π + s)) = u := by
    funext s
    rw [add_comm, hu s]
  rw [h2] at h1
  have h3 : (2 * π + t) = t + 2 * π := by ring
  rw [h3] at h1
  exact h1.symm

/-- A positive lower bound for `‖deriv u‖` on a smooth loop. -/
private lemma min_deriv_pos {u : ℝ → ℂ} (hu : IsSmoothLoop u) :
    ∃ c > 0, ∀ t, c ≤ ‖deriv u t‖ := by
  have hcont : Continuous (deriv u) := hu.1.continuous_deriv (by simp)
  have hper : ∀ t, deriv u (t + 2 * π) = deriv u t := deriv_periodic hu.2.1
  obtain ⟨m, hmpos, hmle⟩ := Work.RPB.B5.periodic_norm_min_pos (fun (_ : ℝ) (t : ℝ) => deriv u t)
    (hcont.comp continuous_snd) (fun τ t => hper t) (fun τ hτ t => hu.2.2.2 t)
  exact ⟨m, hmpos, fun t => hmle 0 (by norm_num) t⟩

/-- Mean value bound: a global derivative bound gives a Lipschitz bound. -/
private lemma mvt_bound {w : ℝ → ℂ} (hw : ∀ t, DifferentiableAt ℝ w t) {ε : ℝ}
    (hb : ∀ t, ‖deriv w t‖ ≤ ε) : ∀ t h : ℝ, ‖w (t + h) - w t‖ ≤ ε * |h| := by
  intro t h
  have h := Convex.norm_image_sub_le_of_norm_deriv_le (𝕜 := ℝ) (f := w) (s := Set.univ)
    (C := ε) (fun x _ => hw x) (fun x _ => hb x) convex_univ (Set.mem_univ t)
    (Set.mem_univ (t + h))
  rw [Real.norm_eq_abs, add_sub_cancel_left] at h
  exact h

/-- Derivative of the straight-line interpolant. -/
private lemma deriv_straightLine {u v : ℝ → ℂ} (hu : Differentiable ℝ u) (hv : Differentiable ℝ v)
    (s : ℝ) (t : ℝ) :
    deriv (fun t => u t + (s : ℂ) * (v t - u t)) t
      = deriv u t + (s : ℂ) * (deriv v t - deriv u t) := by
  have hu1 : HasDerivAt u (deriv u t) t := hu.differentiableAt.hasDerivAt
  have hv1 : HasDerivAt v (deriv v t) t := hv.differentiableAt.hasDerivAt
  have hsub : HasDerivAt (fun t => v t - u t) (deriv v t - deriv u t) t := hv1.sub hu1
  have hmul : HasDerivAt (fun t => (s : ℂ) * (v t - u t))
      ((s : ℂ) * (deriv v t - deriv u t)) t := hsub.const_mul (s : ℂ)
  have hadd : HasDerivAt (fun t => u t + (s : ℂ) * (v t - u t))
      (deriv u t + (s : ℂ) * (deriv v t - deriv u t)) t := hu1.add hmul
  exact hadd.deriv

/-- Reverse-triangle lower bound for a sum with a controlled perturbation. -/
private lemma norm_add_lower {A X : ℂ} {a b : ℝ} (hA : a ≤ ‖A‖) (hX : ‖X‖ ≤ b) (h : b < a) :
    0 < ‖A + X‖ := by
  have htri : ‖A‖ - ‖X‖ ≤ ‖A + X‖ := by
    have hh := norm_add_le (A + X) (-X)
    simp only [add_neg_cancel_right, norm_neg] at hh
    linarith
  linarith

theorem straightLine_loopFamily (u : ℝ → ℂ) (hu : IsSmoothLoop u) :
    ∃ ε > 0, ∀ v : ℝ → ℂ, ContDiff ℝ ∞ v → (∀ t, v (t + 2 * π) = v t) →
      (∀ t, ‖deriv v t - deriv u t‖ < ε) →
      IsLoopFamily (fun s t => u t + (s : ℂ) * (v t - u t)) := by
  obtain ⟨c₁, hc₁pos, hc₁⟩ := biLipschitz_loop u hu
  obtain ⟨c₂, hc₂pos, hc₂⟩ := min_deriv_pos hu
  set c : ℝ := min c₁ c₂ with hcdef
  have hcpos : 0 < c := by rw [hcdef]; exact lt_min hc₁pos hc₂pos
  have hcc₁ : c ≤ c₁ := by rw [hcdef]; exact min_le_left _ _
  have hcc₂ : c ≤ c₂ := by rw [hcdef]; exact min_le_right _ _
  refine ⟨c / 2, by linarith, ?_⟩
  intro v hv hvper hvclose
  have hu_diff : Differentiable ℝ u := hu.1.differentiable (by simp)
  have hv_diff : Differentiable ℝ v := hv.differentiable (by simp)
  -- integer periodicity
  have hu_int : ∀ (x : ℝ) (k : ℤ), u (x + 2 * π * (k : ℝ)) = u x := by
    intro x k
    have hpd : Function.Periodic u (2 * π) := hu.2.1
    have h := (hpd.int_mul k) x
    rwa [show x + (k : ℝ) * (2 * π) = x + 2 * π * (k : ℝ) by ring] at h
  have hv_int : ∀ (x : ℝ) (k : ℤ), v (x + 2 * π * (k : ℝ)) = v x := by
    intro x k
    have hpd : Function.Periodic v (2 * π) := hvper
    have h := (hpd.int_mul k) x
    rwa [show x + (k : ℝ) * (2 * π) = x + 2 * π * (k : ℝ) by ring] at h
  -- the perturbation `v - u` and its mean value bound
  have hw_diff : ∀ t, DifferentiableAt ℝ (fun t => v t - u t) t :=
    fun t => (hv_diff.differentiableAt).sub (hu_diff.differentiableAt)
  have hderivwu : ∀ t, deriv (fun t => v t - u t) t = deriv v t - deriv u t :=
    fun t => deriv_sub (hv_diff.differentiableAt) (hu_diff.differentiableAt)
  have hw_lip : ∀ t h : ℝ, ‖(v (t + h) - u (t + h)) - (v t - u t)‖ ≤ (c / 2) * |h| :=
    mvt_bound hw_diff (fun t => by
      rw [hderivwu t]
      exact le_of_lt (hvclose t))
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- joint smoothness
    have h1 : ContDiff ℝ ∞ (fun z : ℝ × ℝ => u z.2) := hu.1.comp contDiff_snd
    have h2 : ContDiff ℝ ∞ (fun z : ℝ × ℝ => v z.2) := hv.comp contDiff_snd
    have h3 : ContDiff ℝ ∞ (fun z : ℝ × ℝ => (z.1 : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp contDiff_fst
    exact h1.add (h3.mul (h2.sub h1))
  · -- periodicity in `t`
    intro s t
    change u (t + 2 * π) + (s : ℂ) * (v (t + 2 * π) - u (t + 2 * π))
        = u t + (s : ℂ) * (v t - u t)
    rw [hu.2.1 t, hvper t]
  · -- injectivity modulo `2π`
    intro s hs t t' heq
    change u t + (s : ℂ) * (v t - u t) = u t' + (s : ℂ) * (v t' - u t') at heq
    set hh : ℝ := t' - t with hhdef
    set m : ℤ := ⌊hh / (2 * π)⌋ with hmdef
    set δ : ℝ := hh - 2 * π * (m : ℝ) with hδdef
    have hδeq : δ = (t' - t) - 2 * π * (⌊(t' - t) / (2 * π)⌋ : ℝ) := by
      rw [hδdef, hmdef, hhdef]
    have h2p : (0 : ℝ) < 2 * π := by positivity
    have hδ0 : 0 ≤ δ := by
      rw [hδeq]
      have hfl : ((⌊(t' - t) / (2 * π)⌋ : ℤ) : ℝ) ≤ (t' - t) / (2 * π) := Int.floor_le _
      have hmul := mul_le_mul_of_nonneg_right hfl (le_of_lt h2p)
      rw [div_mul_cancel₀ (t' - t) h2p.ne'] at hmul
      nlinarith [hmul]
    have hδ2 : δ < 2 * π := by
      rw [hδeq]
      have hfl : (t' - t) / (2 * π) < ((⌊(t' - t) / (2 * π)⌋ : ℤ) : ℝ) + 1 :=
        Int.lt_floor_add_one _
      have hmul := mul_lt_mul_of_pos_right hfl h2p
      rw [div_mul_cancel₀ (t' - t) h2p.ne'] at hmul
      nlinarith [hmul]
    have ht' : t' = t + δ + 2 * π * (m : ℝ) := by
      have h1 : t' - t = δ + 2 * π * (m : ℝ) := by rw [← hhdef, hδdef]; ring
      linarith
    have heq' : u t + (s : ℂ) * (v t - u t) = u (t + δ) + (s : ℂ) * (v (t + δ) - u (t + δ)) := by
      have h1 : u t' = u (t + δ) := by rw [ht']; exact hu_int (t + δ) m
      have h2 : v t' = v (t + δ) := by rw [ht']; exact hv_int (t + δ) m
      rw [h1, h2] at heq
      exact heq
    by_cases hδ : δ = 0
    · exact ⟨m, by rw [ht', hδ]; ring⟩
    · exfalso
      have hδpos : 0 < δ := lt_of_le_of_ne hδ0 (Ne.symm hδ)
      have hident : u (t + δ) + (s : ℂ) * (v (t + δ) - u (t + δ))
          - (u t + (s : ℂ) * (v t - u t))
          = (u (t + δ) - u t) + (s : ℂ) * ((v (t + δ) - u (t + δ)) - (v t - u t)) := by
        ring
      have key : 0 < ‖u (t + δ) + (s : ℂ) * (v (t + δ) - u (t + δ))
          - (u t + (s : ℂ) * (v t - u t))‖ := by
        rw [hident]
        by_cases hle : δ ≤ π
        · -- δ ≤ π
          have hA : c₁ * δ ≤ ‖u (t + δ) - u t‖ := by
            have h := hc₁ t δ (by rwa [abs_of_pos hδpos])
            rwa [abs_of_pos hδpos] at h
          have hB : ‖(s : ℂ) * ((v (t + δ) - u (t + δ)) - (v t - u t))‖ ≤ (c / 2) * δ := by
            rw [norm_mul, norm_ofReal']
            have hs1 : |s| ≤ 1 := by rw [abs_of_nonneg hs.1]; exact hs.2
            have hBw : ‖(v (t + δ) - u (t + δ)) - (v t - u t)‖ ≤ (c / 2) * δ := by
              have h := hw_lip t δ
              rwa [abs_of_pos hδpos] at h
            calc |s| * ‖(v (t + δ) - u (t + δ)) - (v t - u t)‖ ≤ 1 * ((c / 2) * δ) :=
                  mul_le_mul hs1 hBw (norm_nonneg _) (by norm_num)
              _ = (c / 2) * δ := one_mul _
          have hlt' : (c / 2) * δ < c₁ * δ := by nlinarith [hδpos, hcc₁]
          exact norm_add_lower hA hB hlt'
        · -- π < δ < 2π
          have hlt : π < δ := not_le.mp hle
          have hneg : δ - 2 * π < 0 := by linarith
          have habs : |δ - 2 * π| = 2 * π - δ := by rw [abs_of_neg hneg]; ring
          have hπ' : |δ - 2 * π| ≤ π := by rw [habs]; linarith
          have hup : u (t + δ) = u (t + (δ - 2 * π)) := by
            have h := hu.2.1 (t + (δ - 2 * π))
            rw [show t + (δ - 2 * π) + 2 * π = t + δ by ring] at h
            exact h
          have hvp : v (t + δ) = v (t + (δ - 2 * π)) := by
            have h := hvper (t + (δ - 2 * π))
            rw [show t + (δ - 2 * π) + 2 * π = t + δ by ring] at h
            exact h
          have hA : c₁ * (2 * π - δ) ≤ ‖u (t + δ) - u t‖ := by
            have h := hc₁ t (δ - 2 * π) hπ'
            rw [habs, ← hup] at h
            exact h
          have hB : ‖(s : ℂ) * ((v (t + δ) - u (t + δ)) - (v t - u t))‖ ≤ (c / 2) * (2 * π - δ) := by
            rw [norm_mul, norm_ofReal']
            have hs1 : |s| ≤ 1 := by rw [abs_of_nonneg hs.1]; exact hs.2
            have hBw : ‖(v (t + δ) - u (t + δ)) - (v t - u t)‖ ≤ (c / 2) * (2 * π - δ) := by
              have h := hw_lip t (δ - 2 * π)
              rw [habs] at h
              rw [show (v (t + (δ - 2 * π)) - u (t + (δ - 2 * π))) - (v t - u t)
                    = (v (t + δ) - u (t + δ)) - (v t - u t) by rw [← hup, ← hvp]] at h
              exact h
            calc |s| * ‖(v (t + δ) - u (t + δ)) - (v t - u t)‖ ≤ 1 * ((c / 2) * (2 * π - δ)) :=
                  mul_le_mul hs1 hBw (norm_nonneg _) (by norm_num)
              _ = (c / 2) * (2 * π - δ) := one_mul _
          have hlt' : (c / 2) * (2 * π - δ) < c₁ * (2 * π - δ) := by
            have hpos : 0 < 2 * π - δ := by linarith
            nlinarith [hpos, hcc₁]
          exact norm_add_lower hA hB hlt'
      have hzero : u (t + δ) + (s : ℂ) * (v (t + δ) - u (t + δ)) - (u t + (s : ℂ) * (v t - u t)) = 0 := by
        rw [heq'.symm]; ring
      rw [hzero, norm_zero] at key
      exact lt_irrefl 0 key
  · -- immersed
    intro s hs t
    change deriv (fun t => u t + (s : ℂ) * (v t - u t)) t ≠ 0
    rw [deriv_straightLine hu_diff hv_diff s t]
    intro hzero
    have hbound : ‖(s : ℂ) * (deriv v t - deriv u t)‖ ≤ c / 2 := by
      rw [norm_mul, norm_ofReal']
      have hs1 : |s| ≤ 1 := by rw [abs_of_nonneg hs.1]; exact hs.2
      calc |s| * ‖deriv v t - deriv u t‖ ≤ 1 * (c / 2) :=
            mul_le_mul hs1 (le_of_lt (hvclose t)) (norm_nonneg _) (by norm_num)
        _ = c / 2 := one_mul _
    have hc₂' : c ≤ ‖deriv u t‖ := le_trans hcc₂ (hc₂ t)
    have : 0 < ‖deriv u t + (s : ℂ) * (deriv v t - deriv u t)‖ :=
      norm_add_lower (A := deriv u t) (X := (s : ℂ) * (deriv v t - deriv u t))
        (a := c) (b := c / 2) hc₂' hbound (by linarith [hcpos])
    rw [hzero, norm_zero] at this
    exact lt_irrefl 0 this

end Work.RPB1a
