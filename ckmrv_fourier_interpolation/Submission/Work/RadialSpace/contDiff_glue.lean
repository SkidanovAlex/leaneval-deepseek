import Mathlib
import Submission.Work.RadialSpace.Basic

/-!
# Gluing a function smooth on a half-line to a smooth function

Let `F : ℝ → ℂ` be smooth on `(0, ∞)` and let `W : ℝ → ℂ` be smooth everywhere.
If moreover all the one-sided derivatives of `F` at `0` converge to the corresponding
derivatives of `W` at `0` (`m`-th jet matching), then the function

`glue F W = fun s ↦ if 0 < s then F s else W s`

is smooth (i.e. `C^∞`) on all of `ℝ`.

The proof reduces to the case `W = 0` (`glue F W = glue (F - W) 0 + W`) and then
proceeds by induction on the order `n`: `C^{n+1}` is equivalent to differentiability
together with `C^n` of the derivative, and the derivative of the glue is the glue of
the derivatives.  The one non-trivial point is differentiability of `glue F 0` at `0`,
where `F t = o(t)`: this follows from the mean value inequality once one knows that
`F` and all its one-sided derivatives vanish at `0+`.

## Main result

* `Work.RadialSpace.contDiff_glue`
-/

namespace Work.RadialSpace

open Filter Topology Set
open scoped ContDiff

/-- The function which is equal to `F` on `(0, ∞)` and to `W` on `(-∞, 0]`. -/
noncomputable def glue (F W : ℝ → ℂ) : ℝ → ℂ := fun s => if 0 < s then F s else W s

lemma glue_of_pos {F W : ℝ → ℂ} {s : ℝ} (h : 0 < s) : glue F W s = F s := if_pos h

lemma glue_of_nonpos {F W : ℝ → ℂ} {s : ℝ} (h : ¬ 0 < s) : glue F W s = W s := if_neg h

lemma glue_zero_eq {F : ℝ → ℂ} : glue F 0 0 = (0 : ℂ) := by simp [glue]

lemma glue_zero_of_pos {F : ℝ → ℂ} {s : ℝ} (h : 0 < s) : glue F 0 s = F s := if_pos h

lemma glue_zero_of_nonpos {F : ℝ → ℂ} {s : ℝ} (h : ¬ 0 < s) : glue F 0 s = (0 : ℂ) := by
  simp [glue, h]

/-- `Flat F` means: `F` is smooth on `(0, ∞)` and all its one-sided derivatives at `0`
vanish. -/
def Flat (F : ℝ → ℂ) : Prop :=
  ContDiffOn ℝ Smooth F (Ioi 0) ∧
    ∀ m : ℕ, Tendsto (iteratedDeriv m F) (𝓝[>] (0 : ℝ)) (𝓝 0)

lemma Flat.contDiffOn {F : ℝ → ℂ} (h : Flat F) : ContDiffOn ℝ Smooth F (Ioi 0) := h.1

lemma Flat.tendsto_iteratedDeriv {F : ℝ → ℂ} (h : Flat F) (m : ℕ) :
    Tendsto (iteratedDeriv m F) (𝓝[>] (0 : ℝ)) (𝓝 0) := h.2 m

lemma natCast_le_smooth (m : ℕ) : ((m : ℕ) : ℕ∞ω) ≤ Smooth := by
  show ((m : ℕ) : ℕ∞ω) ≤ ∞
  exact_mod_cast le_top

lemma natCast_ne_omega (n : ℕ) : ((n : ℕ) : ℕ∞ω) ≠ ω := by
  rw [show (ω : ℕ∞ω) = (⊤ : ℕ∞ω) from rfl]
  exact_mod_cast (WithTop.coe_lt_top (n : ℕ∞)).ne

/-! ### Continuity of the glue -/

lemma eventuallyEq_glue_of_pos {F : ℝ → ℂ} {x : ℝ} (hx : 0 < x) :
    glue F 0 =ᶠ[𝓝 x] F := by
  filter_upwards [isOpen_Ioi.mem_nhds hx] with y hy
  exact glue_of_pos hy

lemma eventuallyEq_glue_nhdsGT (F : ℝ → ℂ) :
    glue F 0 =ᶠ[𝓝[>] (0 : ℝ)] F := by
  filter_upwards [self_mem_nhdsWithin] with y hy
  exact glue_of_pos (mem_Ioi.mp hy)

/-- Along `0+` the glue `glue F 0` tends to `0`. -/
lemma tendsto_glue_nhdsGT {F : ℝ → ℂ} (hF : Flat F) :
    Tendsto (glue F 0) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
  Tendsto.congr' (eventuallyEq_glue_nhdsGT F).symm (by simpa using hF.2 0)

/-- The glue `glue F 0` is continuous at `0`. -/
lemma continuousAt_glue_zero {F : ℝ → ℂ} (hF : Flat F) :
    ContinuousAt (glue F 0) 0 := by
  change Tendsto (glue F 0) (𝓝 (0 : ℝ)) (𝓝 (glue F 0 0))
  rw [glue_zero_eq]
  rw [← nhdsLE_sup_nhdsGT (0 : ℝ), tendsto_sup]
  refine ⟨?_, ?_⟩
  · refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [self_mem_nhdsWithin] with y hy
    have hy' : ¬ (0 : ℝ) < y := not_lt.mpr (mem_Iic.mp hy)
    simp [glue, hy']
  · refine Tendsto.congr' ?_ (tendsto_glue_nhdsGT hF)
    filter_upwards [self_mem_nhdsWithin] with y hy
    have hy' : (0 : ℝ) < y := mem_Ioi.mp hy
    simp [glue, hy']

/-- The glue `glue F 0` is continuous on all of `ℝ`. -/
lemma continuous_glue_zero {F : ℝ → ℂ} (hF : Flat F) : Continuous (glue F 0) := by
  rw [continuous_iff_continuousAt]
  intro x
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · have hc : ContinuousAt (fun _ : ℝ => (0 : ℂ)) x := continuousAt_const
    refine hc.congr ?_
    filter_upwards [isOpen_Iio.mem_nhds hx] with y hy
    exact (glue_zero_of_nonpos (not_lt.mpr hy.le)).symm
  · exact continuousAt_glue_zero hF
  · exact (hF.1.contDiffAt (isOpen_Ioi.mem_nhds hx)).continuousAt.congr
      (eventuallyEq_glue_of_pos hx).symm

/-! ### Differentiability at `0` -/

lemma differentiableAt_glue_zero_of_pos {F : ℝ → ℂ} (hF : Flat F) {x : ℝ} (hx : 0 < x) :
    DifferentiableAt ℝ (glue F 0) x :=
  ((hF.1.contDiffAt (isOpen_Ioi.mem_nhds hx)).differentiableAt (by simp)).congr_of_eventuallyEq
    (eventuallyEq_glue_of_pos hx)

lemma deriv_glue_zero_of_pos {F : ℝ → ℂ} {x : ℝ} (hx : 0 < x) :
    deriv (glue F 0) x = deriv F x :=
  (eventuallyEq_glue_of_pos hx).deriv_eq

/-- Near `0` from the right, `glue F 0 t = o(t)`: the mean value inequality applied to
`glue F 0`, whose derivative is the one-sided derivative of `F`. -/
lemma tendsto_inv_smul_glue_zero {F : ℝ → ℂ} (hF : Flat F) :
    Tendsto (fun t : ℝ => t⁻¹ • glue F 0 t) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hε2 : (0 : ℝ) < ε / 2 := by linarith
  have hS : {s : ℝ | ‖deriv F s‖ < ε / 2} ∈ 𝓝[>] (0 : ℝ) := by
    have h1 : Tendsto (fun s : ℝ => ‖deriv F s‖) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
      simpa using (hF.2 1).norm
    have h2 : ∀ᶠ s in 𝓝[>] (0 : ℝ), ‖deriv F s‖ < ε / 2 := by
      have h := (Metric.tendsto_nhds.mp h1) (ε / 2) hε2
      simpa [dist_eq_norm, Real.norm_eq_abs] using h
    exact h2
  obtain ⟨δ, hδ, hδS⟩ :=
    (mem_nhdsGT_iff_exists_Ioo_subset' (show (0 : ℝ) < 1 by norm_num)).mp hS
  have hI : Ioo (0 : ℝ) δ ∈ 𝓝[>] (0 : ℝ) := (nhdsGT_basis 0).mem_of_mem hδ
  filter_upwards [hI] with t ht
  obtain ⟨ht0, htd⟩ := mem_Ioo.mp ht
  have hbd : ‖glue F 0 t‖ ≤ (ε / 2) * t := by
    have hlim : Tendsto (fun t' : ℝ => ‖glue F 0 t - glue F 0 t'‖)
        (𝓝[>] (0 : ℝ)) (𝓝 ‖glue F 0 t‖) := by
      have h3 : Tendsto (fun t' : ℝ => glue F 0 t - glue F 0 t') (𝓝[>] (0 : ℝ))
          (𝓝 (glue F 0 t - 0)) := tendsto_const_nhds.sub (tendsto_glue_nhdsGT hF)
      simpa using h3.norm
    have hlim2 : Tendsto (fun t' : ℝ => (ε / 2) * (t - t')) (𝓝[>] (0 : ℝ))
        (𝓝 ((ε / 2) * t)) := by
      have htend : Tendsto (fun t' : ℝ => t') (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
        tendsto_id.mono_right nhdsWithin_le_nhds
      have hsub : Tendsto (fun t' : ℝ => t - t') (𝓝[>] (0 : ℝ)) (𝓝 (t - 0)) :=
        (tendsto_const_nhds : Tendsto (fun _ : ℝ => t) (𝓝[>] (0 : ℝ)) (𝓝 t)).sub htend
      have := (tendsto_const_nhds : Tendsto (fun _ : ℝ => ε / 2) (𝓝[>] (0 : ℝ))
        (𝓝 (ε / 2))).mul hsub
      simpa using this
    refine le_of_tendsto_of_tendsto hlim hlim2 ?_
    filter_upwards [(nhdsGT_basis (0 : ℝ)).mem_of_mem ht0] with t' ht'
    obtain ⟨ht'0, ht't⟩ := mem_Ioo.mp ht'
    have ht's : t' ∈ Ioo (0 : ℝ) δ := ⟨ht'0, lt_trans ht't htd⟩
    have hts : t ∈ Ioo (0 : ℝ) δ := ⟨ht0, htd⟩
    have h := Convex.norm_image_sub_le_of_norm_deriv_le
      (f := glue F 0) (s := Ioo (0 : ℝ) δ) (x := t') (y := t) (C := ε / 2)
      (fun x hx => differentiableAt_glue_zero_of_pos hF (mem_Ioo.mp hx).1)
      (fun x hx => by
        obtain ⟨hx0, hxd⟩ := mem_Ioo.mp hx
        rw [deriv_glue_zero_of_pos hx0]
        exact le_of_lt (show ‖deriv F x‖ < ε / 2 from hδS ⟨hx0, hxd⟩))
      (convex_Ioo (0 : ℝ) δ) ht's hts
    have hnorm : ‖t - t'‖ = t - t' := by
      rw [Real.norm_eq_abs, abs_of_pos (sub_pos.mpr ht't)]
    rwa [hnorm] at h
  rw [dist_eq_norm, sub_zero]
  calc ‖t⁻¹ • glue F 0 t‖ = t⁻¹ * ‖glue F 0 t‖ := by
        rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr ht0.le)]
    _ ≤ t⁻¹ * ((ε / 2) * t) := mul_le_mul_of_nonneg_left hbd (inv_nonneg.mpr ht0.le)
    _ = ε / 2 := by field_simp
    _ < ε := by linarith

/-- The glue `glue F 0` is differentiable, and its derivative is the glue of the
derivatives. -/
lemma deriv_glue_zero {F : ℝ → ℂ} (hF : Flat F) :
    Differentiable ℝ (glue F 0) ∧ deriv (glue F 0) = glue (deriv F) 0 := by
  have hd0 : HasDerivAt (glue F 0) 0 0 := by
    rw [hasDerivAt_iff_tendsto_slope_left_right]
    refine ⟨?_, ?_⟩
    · refine Tendsto.congr' ?_ tendsto_const_nhds
      filter_upwards [self_mem_nhdsWithin] with y hy
      have hy' : ¬ (0 : ℝ) < y := not_lt.mpr (mem_Iio.mp hy).le
      simp [slope_def_module, glue, hy']
    · refine Tendsto.congr' ?_ (tendsto_inv_smul_glue_zero hF)
      filter_upwards [self_mem_nhdsWithin] with y hy
      have hy' : (0 : ℝ) < y := mem_Ioi.mp hy
      simp [slope_def_module, glue, hy']
  refine ⟨?_, ?_⟩
  · intro x
    rcases lt_trichotomy x 0 with hx | rfl | hx
    · have hc : DifferentiableAt ℝ (fun _ : ℝ => (0 : ℂ)) x := differentiableAt_const _
      refine hc.congr_of_eventuallyEq ?_
      filter_upwards [isOpen_Iio.mem_nhds hx] with y hy
      exact glue_zero_of_nonpos (not_lt.mpr hy.le)
    · exact hd0.differentiableAt
    · exact differentiableAt_glue_zero_of_pos hF hx
  · funext x
    rcases lt_trichotomy x 0 with hx | rfl | hx
    · have he : glue F 0 =ᶠ[𝓝 x] (fun _ => (0 : ℂ)) := by
        filter_upwards [isOpen_Iio.mem_nhds hx] with y hy
        exact glue_zero_of_nonpos (not_lt.mpr hy.le)
      rw [he.deriv_eq, deriv_const, glue_zero_of_nonpos (not_lt.mpr hx.le)]
    · rw [hd0.deriv, glue_zero_eq]
    · rw [(eventuallyEq_glue_of_pos hx).deriv_eq, glue_zero_of_pos hx]

/-- The hypotheses are stable under taking derivatives. -/
lemma Flat.deriv {F : ℝ → ℂ} (hF : Flat F) : Flat (deriv F) := by
  refine ⟨?_, ?_⟩
  · exact (contDiffOn_infty_iff_deriv_of_isOpen isOpen_Ioi).1 hF.1 |>.2
  · intro m
    rw [← iteratedDeriv_succ']
    exact hF.2 (m + 1)

/-- The reduced statement: if `F` is smooth on `(0, ∞)` and flat at `0+`, then
`glue F 0` is `C^n` for every `n`. -/
theorem contDiff_glue_zero_aux :
    ∀ n : ℕ, ∀ F : ℝ → ℂ, Flat F → ContDiff ℝ ((n : ℕ) : ℕ∞ω) (glue F 0)
  | 0, F, hF => by
      rw [Nat.cast_zero, contDiff_zero]
      exact continuous_glue_zero hF
  | n + 1, F, hF => by
      rw [Nat.cast_succ, contDiff_succ_iff_deriv]
      refine ⟨(deriv_glue_zero hF).1, fun h => absurd h (natCast_ne_omega n), ?_⟩
      rw [(deriv_glue_zero hF).2]
      exact contDiff_glue_zero_aux n (deriv F) hF.deriv

/-- If `F` is smooth on `(0, ∞)` and flat at `0+`, then `glue F 0` is smooth. -/
theorem contDiff_glue_zero {F : ℝ → ℂ} (hF : Flat F) : ContDiff ℝ Smooth (glue F 0) := by
  rw [contDiff_infty]
  intro n
  exact contDiff_glue_zero_aux n F hF

/-! ### The general case -/

theorem contDiff_glue {F W : ℝ → ℂ} (hF : ContDiffOn ℝ Work.RadialSpace.Smooth F (Set.Ioi 0))
    (hW : ContDiff ℝ Work.RadialSpace.Smooth W)
    (hjet : ∀ m : ℕ, Filter.Tendsto (iteratedDeriv m F) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (iteratedDeriv m W 0))) :
    ContDiff ℝ Work.RadialSpace.Smooth fun s : ℝ => if 0 < s then F s else W s := by
  have hflat : Flat (F - W) := by
    refine ⟨hF.sub hW.contDiffOn, ?_⟩
    intro m
    have heq : (fun s : ℝ => iteratedDeriv m F s - iteratedDeriv m W s) =ᶠ[𝓝[>] (0 : ℝ)]
        iteratedDeriv m (F - W) := by
      filter_upwards [self_mem_nhdsWithin] with s hs
      have hs' : (0 : ℝ) < s := mem_Ioi.mp hs
      have hFs : ContDiffAt ℝ ((m : ℕ) : ℕ∞ω) F s :=
        (hF.contDiffAt (isOpen_Ioi.mem_nhds hs')).of_le (natCast_le_smooth m)
      have hWs : ContDiffAt ℝ ((m : ℕ) : ℕ∞ω) W s :=
        hW.contDiffAt.of_le (natCast_le_smooth m)
      exact (iteratedDeriv_sub hFs hWs).symm
    refine Tendsto.congr' heq ?_
    have hWt : Tendsto (iteratedDeriv m W) (𝓝[>] (0 : ℝ)) (𝓝 (iteratedDeriv m W 0)) :=
      (hW.continuous_iteratedDeriv m (natCast_le_smooth m)).tendsto 0 |>.mono_left
        nhdsWithin_le_nhds
    simpa using (hjet m).sub hWt
  have hsum : ContDiff ℝ Smooth (glue (F - W) 0 + W) := (contDiff_glue_zero hflat).add hW
  rw [show (fun s : ℝ => if 0 < s then F s else W s) = glue (F - W) 0 + W from ?_]
  · exact hsum
  · funext s
    by_cases h : 0 < s
    · simp [glue, h]
    · simp [glue, h]

end Work.RadialSpace
