import Mathlib

namespace Work.NN.Final.ChartComp

open Metric

/-- The norm function on `ℂ` is smooth away from the origin. -/
private lemma norm_contDiffOn :
    ContDiffOn ℝ ⊤ (fun z : ℂ => ‖z‖) {z : ℂ | z ≠ 0} := by
  intro z hz
  rw [contDiffWithinAt_iff_contDiffAt (isOpen_ne (x := (0:ℂ)) |>.mem_nhds hz)]
  exact contDiffAt_norm ℝ hz

/-- Scaling key lemma: for a function `f` on `ℂ` which is smooth off the origin and
positively homogeneous of degree one, the norm of the `m`-th Fréchet derivative scales.
Namely `t ^ m * ‖D^m f (t • x)‖ = t * ‖D^m f x‖` for `t > 0` and `x ≠ 0`.

This is the analytic content of the statement `D^m f` is homogeneous of degree `1 - m`. -/
private lemma scaling_aux (f : ℂ → ℝ) (hhom : ∀ (t : ℝ) (y : ℂ), 0 < t → f (t • y) = t * f y)
    (hcd : ContDiffOn ℝ ⊤ f {z : ℂ | z ≠ 0})
    (m : ℕ) (t : ℝ) (ht : 0 < t) (x : ℂ) (hx : x ≠ 0) :
    t ^ m * ‖iteratedFDeriv ℝ m f (t • x)‖ = t * ‖iteratedFDeriv ℝ m f x‖ := by
  have hs : IsOpen {z : ℂ | z ≠ 0} := isOpen_ne (x := (0:ℂ))
  set T : ℂ →L[ℝ] ℂ := t • (1 : ℂ →L[ℝ] ℂ) with hT
  have hTa : ∀ y : ℂ, T y = t • y := fun y => by simp [hT]
  have hxT : T x ∈ {z : ℂ | z ≠ 0} := by
    show T x ≠ 0
    rw [hTa]; exact smul_ne_zero ht.ne' hx
  have hpre : T ⁻¹' {z : ℂ | z ≠ 0} = {z : ℂ | z ≠ 0} := by
    ext y; rw [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_ofPred_eq, hTa, smul_ne_zero_iff]
    exact ⟨fun h => h.2, fun h => ⟨ht.ne', h⟩⟩
  -- differentiating the identity `f (t • ·) = t • (f ·)` at `x`
  have h1 : iteratedFDeriv ℝ m (f ∘ ⇑T) x
      = (iteratedFDeriv ℝ m f (T x)).compContinuousLinearMap (fun _ => T) := by
    have key := ContinuousLinearMap.iteratedFDerivWithin_comp_right (𝕜 := ℝ) (g := T) (f := f)
      (s := {z : ℂ | z ≠ 0}) hcd hs.uniqueDiffOn (by rw [hpre]; exact hs.uniqueDiffOn) hxT
      (i := m) le_top
    rw [hpre] at key
    rw [← (iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (s := {z : ℂ | z ≠ 0}) (f := f) m hs) hxT,
      ← key,
      ← (iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (s := {z : ℂ | z ≠ 0})
        (f := f ∘ ⇑T) m hs) hx]
  have h2 : iteratedFDeriv ℝ m ((t • (1 : ℝ →L[ℝ] ℝ)) ∘ f) x
      = (t • (1 : ℝ →L[ℝ] ℝ)).compContinuousMultilinearMap (iteratedFDeriv ℝ m f x) :=
    ContinuousLinearMap.iteratedFDeriv_comp_left (𝕜 := ℝ) (g := t • (1 : ℝ →L[ℝ] ℝ))
      (hcd.contDiffAt (hs.mem_nhds hx)) (i := m) le_top
  have h3 : (f ∘ ⇑T) = ((t • (1 : ℝ →L[ℝ] ℝ)) ∘ f) := by
    funext y
    rw [Function.comp_apply, Function.comp_apply, hTa, hhom t y ht]
    simp
  have hkey : (iteratedFDeriv ℝ m f (T x)).compContinuousLinearMap (fun _ => T)
      = (t • (1 : ℝ →L[ℝ] ℝ)).compContinuousMultilinearMap (iteratedFDeriv ℝ m f x) := by
    rw [← h1, h3, h2]
  have hL : (iteratedFDeriv ℝ m f (T x)).compContinuousLinearMap (fun _ => T)
      = t ^ m • (iteratedFDeriv ℝ m f (T x)) := by
    ext v
    simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply, hTa,
      ContinuousMultilinearMap.map_smul_univ, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul, ContinuousMultilinearMap.smul_apply]
  have hR : (t • (1 : ℝ →L[ℝ] ℝ)).compContinuousMultilinearMap (iteratedFDeriv ℝ m f x)
      = t • (iteratedFDeriv ℝ m f x) := by
    ext v
    simp only [ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply, smul_eq_mul]
  have hkey2 : t ^ m • (iteratedFDeriv ℝ m f (T x)) = t • (iteratedFDeriv ℝ m f x) :=
    hL.symm.trans (hkey.trans hR)
  have hnorm : t ^ m * ‖iteratedFDeriv ℝ m f (T x)‖ = t * ‖iteratedFDeriv ℝ m f x‖ := by
    calc t ^ m * ‖iteratedFDeriv ℝ m f (T x)‖
        = ‖t ^ m • (iteratedFDeriv ℝ m f (T x))‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos (pow_pos ht m)]
      _ = ‖t • (iteratedFDeriv ℝ m f x)‖ := by rw [hkey2]
      _ = t * ‖iteratedFDeriv ℝ m f x‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht]
  simpa [hTa] using hnorm

/-- The above scaling statement specialised to `f = ‖·‖` on `ℂ`. -/
private lemma norm_scaling (m : ℕ) (t : ℝ) (ht : 0 < t) (x : ℂ) (hx : x ≠ 0) :
    t ^ m * ‖iteratedFDeriv ℝ m (fun z : ℂ => ‖z‖) (t • x)‖
      = t * ‖iteratedFDeriv ℝ m (fun z : ℂ => ‖z‖) x‖ :=
  scaling_aux (fun z : ℂ => ‖z‖) (fun t y ht => by
      simp only [norm_smul, Real.norm_eq_abs, abs_of_pos ht]) norm_contDiffOn m t ht x hx

theorem exists_bound_iteratedFDeriv_norm :
    ∃ C : ℕ → ℝ, (∀ m, 0 < C m) ∧ ∀ (m : ℕ), 1 ≤ m → ∀ (w : ℂ),
      w ≠ 0 → ‖iteratedFDeriv ℝ m (fun w : ℂ => ‖w‖) w‖ ≤ C m * (1 / ‖w‖) ^ (m - 1) := by
  have hs : IsOpen {z : ℂ | z ≠ 0} := isOpen_ne (x := (0:ℂ))
  -- the `m`-th derivative is bounded on the unit sphere by compactness
  have hbound : ∀ m : ℕ, 1 ≤ m → ∃ C : ℝ, ∀ y : ℂ, y ∈ sphere (0:ℂ) 1 →
      ‖iteratedFDeriv ℝ m (fun z : ℂ => ‖z‖) y‖ ≤ C := by
    intro m _
    have hcont : ContinuousOn (fun y : ℂ => iteratedFDeriv ℝ m (fun z : ℂ => ‖z‖) y)
        (sphere (0:ℂ) 1) :=
      (ContinuousOn.continuousOn_iteratedFDeriv norm_contDiffOn hs le_top).mono (by
        intro y hy
        simp only [Set.mem_ofPred_eq]
        intro h0
        rw [h0] at hy
        simp at hy)
    obtain ⟨C, hC⟩ := (isCompact_sphere (0:ℂ) 1).exists_bound_of_continuousOn hcont
    exact ⟨C, hC⟩
  -- for each `m` produce a positive constant, vacuously for `m = 0`
  have hex : ∀ m : ℕ, ∃ C : ℝ, (0 < C) ∧ (1 ≤ m → ∀ w : ℂ, w ≠ 0 →
      ‖iteratedFDeriv ℝ m (fun z : ℂ => ‖z‖) w‖ ≤ C * (1 / ‖w‖) ^ (m - 1)) := by
    intro m
    by_cases hm : 1 ≤ m
    · obtain ⟨D, hD⟩ := hbound m hm
      refine ⟨max 1 D, ?_, ?_⟩
      · exact lt_of_lt_of_le one_pos (le_max_left 1 D)
      · intro _ w hw
        -- reduce `w` to the unit vector `w / ‖w‖`, using the scaling lemma
        have hrpos : 0 < ‖w‖ := norm_pos_iff.mpr hw
        have hrnz : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw
        have hxnorm : ‖(‖w‖⁻¹ • w : ℂ)‖ = 1 := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hrpos), inv_mul_cancel₀ hrnz]
        have hxnz : (‖w‖⁻¹ • w : ℂ) ≠ 0 := by
          intro hh; rw [hh] at hxnorm; simp at hxnorm
        have hsphere : (‖w‖⁻¹ • w : ℂ) ∈ sphere (0:ℂ) 1 := by
          rw [mem_sphere, dist_eq_norm, sub_zero]; exact hxnorm
        have hsw : (‖w‖) • (‖w‖⁻¹ • w) = w := smul_inv_smul₀ hrnz w
        have hsc := norm_scaling m ‖w‖ hrpos (‖w‖⁻¹ • w) hxnz
        rw [hsw] at hsc
        have hsc' : ‖w‖ ^ (m - 1) * ‖iteratedFDeriv ℝ m (fun z : ℂ => ‖z‖) w‖
            = ‖iteratedFDeriv ℝ m (fun z : ℂ => ‖z‖) (‖w‖⁻¹ • w)‖ := by
          have hh : ‖w‖ ^ m = ‖w‖ * ‖w‖ ^ (m - 1) := by
            rw [← pow_succ', Nat.sub_add_cancel hm]
          rw [hh, mul_assoc] at hsc
          exact mul_left_cancel₀ hrnz hsc
        have h1 : ‖w‖ ^ (m - 1) * ‖iteratedFDeriv ℝ m (fun z : ℂ => ‖z‖) w‖ ≤ max 1 D :=
          hsc'.le.trans ((hD _ hsphere).trans (le_max_right 1 D))
        have h2 : ‖iteratedFDeriv ℝ m (fun z : ℂ => ‖z‖) w‖ * ‖w‖ ^ (m - 1) ≤ max 1 D := by
          rw [mul_comm]; exact h1
        calc ‖iteratedFDeriv ℝ m (fun z : ℂ => ‖z‖) w‖
            ≤ max 1 D / ‖w‖ ^ (m - 1) := (le_div_iff₀ (pow_pos hrpos (m - 1))).2 h2
          _ = max 1 D * (1 / ‖w‖) ^ (m - 1) := by rw [one_div_pow, div_eq_mul_inv, one_div]
    · exact ⟨1, one_pos, fun h => absurd h hm⟩
  choose C hC using hex
  exact ⟨C, fun m => (hC m).1, fun m hm w hw => (hC m).2 hm w hw⟩

end Work.NN.Final.ChartComp
