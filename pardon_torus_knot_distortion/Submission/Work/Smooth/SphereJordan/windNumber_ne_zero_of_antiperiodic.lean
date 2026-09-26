import Mathlib
import Submission.Work.Smooth.SphereJordan.planeIndex
import Submission.Work.Smooth.SphereJordan.planeIndexGeom

/-!
# The winding number of an antiperiodic closed curve is nonzero

If `γ : ℝ → ℂ` is continuous, `2 * π`-periodic and antiperiodic under the half-period shift
`t ↦ t + π` (`γ (t + π) = -γ t`), and nowhere vanishing, then its winding number about `0` is
nonzero.

The proof passes to the loop `c t = γ (2π t)` on `[0,1]`, takes a continuous logarithm lift `Λ`
of `c` (`argChangeLift`), and compares the increments of `Λ` over the two halves of the loop.  The
function `t ↦ Λ (t + 1/2) - Λ t - π I` takes values in `2πi ℤ` on `[0,1/2]`; being continuous on a
preconnected set it is constant (`IsCoveringMap.constOn_of_comp`), so
`Λ 1 - Λ 0 = 2 (Λ (1/2) - Λ 0)`.  Since `exp (Λ (1/2) - Λ 0) = c (1/2) / c 0 = -1`, the half
increment `Λ (1/2) - Λ 0` is nonzero; a zero winding number would force it to vanish, whence the
contradiction `1 = -1`.
-/

noncomputable section

open Set

namespace Work.Smooth.SphereJordan

/-- **A nowhere vanishing continuous `2π`-periodic plane curve which is antiperiodic under a
half-period shift has nonzero winding number about the origin.** -/
theorem windNumber_ne_zero_of_antiperiodic {γ : ℝ → ℂ} (hγ : Continuous γ)
    (hper : Function.Periodic γ (2 * Real.pi)) (hanti : ∀ t : ℝ, γ (t + Real.pi) = -γ t)
    (hne : ∀ t : ℝ, γ t ≠ 0) : windNumber γ hγ 0 ≠ 0 := by
  set c : C(unitInterval, ℂ) := curveLoop γ hγ with hcdef
  have hc_apply : ∀ t : unitInterval, c t = γ (2 * Real.pi * (t : ℝ)) := fun t => rfl
  have hc0 : ∀ t : unitInterval, c t ≠ 0 := by
    intro t; rw [hc_apply]; exact hne _
  have hloop : c 0 = c 1 := by
    rw [hc_apply, hc_apply]
    have h0 : 2 * Real.pi * ((0 : unitInterval) : ℝ) = 0 := by simp
    have h1 : 2 * Real.pi * ((1 : unitInterval) : ℝ) = 2 * Real.pi := by simp
    rw [h0, h1]
    simpa using (hper 0).symm
  have hwind : windNumber γ hγ 0 = loopIndex c := by
    rw [hcdef]
    unfold windNumber
    refine loopIndex_congr (fun t => ?_) (fun t => ?_) (fun t => ?_) ?_ ?_
    · show γ (2 * Real.pi * (t : ℝ)) - 0 = γ (2 * Real.pi * (t : ℝ))
      rw [sub_zero]
    · show γ (2 * Real.pi * (t : ℝ)) - 0 ≠ 0
      rw [sub_zero]; exact hne _
    · show γ (2 * Real.pi * (t : ℝ)) ≠ 0
      exact hne _
    · show γ (2 * Real.pi * ((0 : unitInterval) : ℝ)) - 0 = γ (2 * Real.pi * ((1 : unitInterval) : ℝ)) - 0
      have h0 : 2 * Real.pi * ((0 : unitInterval) : ℝ) = 0 := by simp
      have h1 : 2 * Real.pi * ((1 : unitInterval) : ℝ) = 2 * Real.pi := by simp
      rw [h0, h1, sub_zero, sub_zero]
      simpa using (hper 0).symm
    · show γ (2 * Real.pi * ((0 : unitInterval) : ℝ)) = γ (2 * Real.pi * ((1 : unitInterval) : ℝ))
      have h0 : 2 * Real.pi * ((0 : unitInterval) : ℝ) = 0 := by simp
      have h1 : 2 * Real.pi * ((1 : unitInterval) : ℝ) = 2 * Real.pi := by simp
      rw [h0, h1]
      simpa using (hper 0).symm
  rw [hwind]
  -- now show loopIndex c ≠ 0
  obtain ⟨Λ, hΛ, hΛne, huniq⟩ := argChangeLift c hc0
  set half : unitInterval := ⟨1/2, by norm_num⟩ with hhalfdef
  -- clamp function
  have hmem : ∀ s : ℝ, min (max s 0) 1 ∈ Set.Icc (0:ℝ) 1 := by
    intro s
    exact ⟨le_min (le_max_right _ _) zero_le_one, min_le_right _ _⟩
  let clamp : ℝ → unitInterval := fun s => ⟨min (max s 0) 1, hmem s⟩
  have hclamp_cont : Continuous clamp :=
    (by fun_prop : Continuous fun s : ℝ => min (max s 0) 1).subtype_mk hmem
  let g : ℝ → ℂ := fun s => Λ (clamp (s + 1/2)) - Λ (clamp s) - (↑Real.pi * Complex.I)
  have hga : Continuous fun s : ℝ => Λ (clamp (s + 1/2)) :=
    Λ.continuous.comp (hclamp_cont.comp (continuous_id.add continuous_const))
  have hgb : Continuous fun s : ℝ => Λ (clamp s) := Λ.continuous.comp hclamp_cont
  have hg_cont : Continuous g := by
    unfold g
    exact (hga.sub hgb).sub continuous_const
  -- key: exp(g s) = 1 on [0,1/2]
  have hlemmas : ∀ s ∈ Set.Icc (0:ℝ) (1/2), Complex.exp (g s) = 1 := by
    intro s hs
    obtain ⟨hs0, hs1⟩ := hs
    have hs_mem : s ∈ Set.Icc (0:ℝ) 1 := ⟨hs0, by linarith⟩
    have hsp_mem : s + 1/2 ∈ Set.Icc (0:ℝ) 1 := ⟨by linarith, by linarith⟩
    have hσ : clamp (s + 1/2) = (⟨s + 1/2, hsp_mem⟩ : unitInterval) := by
      apply Subtype.ext
      show min (max (s + 1/2) 0) 1 = s + 1/2
      rw [max_eq_left (by linarith), min_eq_left (by linarith)]
    have hτ : clamp s = (⟨s, hs_mem⟩ : unitInterval) := by
      apply Subtype.ext
      show min (max s 0) 1 = s
      rw [max_eq_left (by linarith), min_eq_left (by linarith)]
    have hcs : c (clamp (s + 1/2)) = - c (clamp s) := by
      rw [hσ, hτ, hc_apply, hc_apply]
      have h1 : 2 * Real.pi * (s + 1/2) = 2 * Real.pi * s + Real.pi := by ring
      rw [h1]
      exact hanti (2 * Real.pi * s)
    unfold g
    rw [Complex.exp_sub, Complex.exp_sub, hΛ, hΛ, Complex.exp_pi_mul_I, hcs,
      neg_div, div_self (hc0 (clamp s))]
    norm_num
  have hge : ∀ a ∈ Set.Icc (0:ℝ) (1/2), ∀ a' ∈ Set.Icc (0:ℝ) (1/2),
      (fun z : ℂ => (⟨Complex.exp z, Complex.exp_ne_zero z⟩ : {z : ℂ // z ≠ 0})) (g a)
        = (fun z : ℂ => (⟨Complex.exp z, Complex.exp_ne_zero z⟩ : {z : ℂ // z ≠ 0})) (g a') := by
    intro a ha a' ha'
    apply Subtype.ext
    show Complex.exp (g a) = Complex.exp (g a')
    rw [hlemmas a ha, hlemmas a' ha']
  have hconst : g 0 = g (1/2) := by
    apply Complex.isCoveringMap_exp.constOn_of_comp (s := Set.Icc (0:ℝ) (1/2))
      (isPreconnected_Icc : IsPreconnected (Set.Icc (0:ℝ) (1/2))) hg_cont.continuousOn hge
    · exact ⟨le_refl 0, by norm_num⟩
    · exact ⟨by norm_num, le_refl (1/2)⟩
  -- compute g 0 and g (1/2)
  have hσ0 : clamp (0 + 1/2) = half := by
    apply Subtype.ext
    show min (max (0 + 1/2) 0) 1 = (half : ℝ)
    rw [hhalfdef]
    show min (max (0 + 1/2) 0) 1 = 1/2
    rw [max_eq_left (by norm_num), min_eq_left (by norm_num)]
    norm_num
  have hτ0 : clamp 0 = (0 : unitInterval) := by
    apply Subtype.ext
    show min (max (0:ℝ) 0) 1 = ((0 : unitInterval) : ℝ)
    rw [max_self, min_eq_left (by norm_num)]
    rfl
  have hσh : clamp (1/2 + 1/2) = (1 : unitInterval) := by
    apply Subtype.ext
    show min (max ((1/2:ℝ) + 1/2) 0) 1 = ((1 : unitInterval) : ℝ)
    rw [show ((1/2:ℝ) + 1/2) = 1 by norm_num, max_eq_left (by norm_num), min_self]
    rfl
  have hτh : clamp (1/2) = half := by
    apply Subtype.ext
    show min (max (1/2:ℝ) 0) 1 = (half : ℝ)
    rw [hhalfdef]
    show min (max (1/2:ℝ) 0) 1 = 1/2
    rw [max_eq_left (by norm_num), min_eq_left (by norm_num)]
  have hg0 : g 0 = Λ half - Λ 0 - (↑Real.pi * Complex.I) := by
    unfold g; rw [hσ0, hτ0]
  have hgh : g (1/2) = Λ 1 - Λ half - (↑Real.pi * Complex.I) := by
    unfold g; rw [hσh, hτh]
  have hrel : Λ half - Λ 0 = Λ 1 - Λ half := by
    have h := hconst
    rw [hg0, hgh] at h
    have h2 := congrArg (fun z => z + (↑Real.pi * Complex.I)) h
    simpa using h2
  have hM : Λ 1 - Λ 0 = 2 * (Λ half - Λ 0) := by
    have h2 : Λ half + (Λ half - Λ 0) = Λ 1 := by rw [hrel]; ring
    rw [← h2]; ring
  have hspec := loopIndex_spec c hc0 hloop Λ hΛ
  have hexpS : Complex.exp (Λ half - Λ 0) = -1 := by
    rw [Complex.exp_sub, hΛ half, hΛ 0, hc_apply half, hc_apply 0]
    have hhalf : ((half : unitInterval) : ℝ) = 1/2 := rfl
    have h0v : (((0 : unitInterval)) : ℝ) = 0 := rfl
    rw [hhalf, h0v]
    have hpi : 2 * Real.pi * (1/2) = Real.pi := by ring
    rw [hpi, mul_zero]
    rw [show γ Real.pi = -γ 0 by simpa using hanti 0]
    rw [neg_div, div_self (hne 0)]
  intro hk
  have hM0 : Λ 1 - Λ 0 = 0 := by rw [hspec, hk]; ring
  have hS0 : Λ half - Λ 0 = 0 := by
    have hmul : (2:ℂ) * (Λ half - Λ 0) = 0 := by rw [← hM]; exact hM0
    exact (mul_eq_zero.mp hmul).resolve_left (by norm_num)
  have h1 : (1:ℂ) = -1 := by rw [← hexpS, hS0, Complex.exp_zero]
  exact absurd h1 (by norm_num)


end Work.Smooth.SphereJordan
