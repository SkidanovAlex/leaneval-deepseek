import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.Spaces.Defs
import Submission.Work.Construction.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real

namespace Work.FTS.StrongEps.E5Aux2

/-! ## The model profile `δ` and its derivatives -/

/-- The model profile `δ(z,θ) = sin(2θ)/(2(1+z))` (the singular part `Theta α (Fstar α)` of
the stream function of the reference profile). -/
private noncomputable def delta (z θ : ℝ) : ℝ := Real.sin (2 * θ) / (2 * (1 + z))

lemma hasDerivAt_delta_z (θ z : ℝ) (hz : (0 : ℝ) < 1 + z) :
    HasDerivAt (fun z' : ℝ => delta z' θ) (- Real.sin (2 * θ) / (2 * (1 + z) ^ 2)) z := by
  have h2 : HasDerivAt (fun z' : ℝ => 2 * (1 + z')) 2 z := by
    simpa using ((hasDerivAt_id z).const_add 1).const_mul 2
  have h1 : HasDerivAt (fun z' : ℝ => (2 * (1 + z'))⁻¹) (-2 / (2 * (1 + z)) ^ 2) z :=
    h2.inv (by positivity)
  have h3 := h1.const_mul (Real.sin (2 * θ))
  have hfun : (fun z' : ℝ => Real.sin (2 * θ) * (2 * (1 + z'))⁻¹)
      = fun z' : ℝ => delta z' θ := by
    funext z'; simp only [delta]; ring
  rw [hfun] at h3
  have hval : Real.sin (2 * θ) * (-2 / (2 * (1 + z)) ^ 2)
      = - Real.sin (2 * θ) / (2 * (1 + z) ^ 2) := by
    field_simp
  rwa [hval] at h3

lemma hasDerivAt_delta_th (z θ : ℝ) (hz : (0 : ℝ) < 1 + z) :
    HasDerivAt (fun θ' : ℝ => delta z θ') (Real.cos (2 * θ) / (1 + z)) θ := by
  have h2 : HasDerivAt (fun θ' : ℝ => 2 * θ') 2 θ := by
    simpa using (hasDerivAt_id θ).const_mul 2
  have h1 : HasDerivAt (fun θ' : ℝ => Real.sin (2 * θ')) (Real.cos (2 * θ) * 2) θ :=
    (Real.hasDerivAt_sin (2 * θ)).comp θ h2
  have h3 := h1.div_const (2 * (1 + z))
  have hfun : (fun θ' : ℝ => Real.sin (2 * θ') / (2 * (1 + z)))
      = fun θ' : ℝ => delta z θ' := by
    funext θ'; simp only [delta]
  rw [hfun] at h3
  have hval : Real.cos (2 * θ) * 2 / (2 * (1 + z)) = Real.cos (2 * θ) / (1 + z) := by
    field_simp
  rwa [hval] at h3

/-- The totalised derivative is bounded in terms of the derivative of the subtracted
profile: quantitatively, "`deriv (f - g) x - deriv f x` is either `-deriv g x` or `0`". -/
lemma abs_deriv_sub_sub_le {f g : ℝ → ℝ} {x : ℝ} (hg : DifferentiableAt ℝ g x) :
    |deriv (f - g) x - deriv f x| ≤ |deriv g x| := by
  by_cases hf : DifferentiableAt ℝ f x
  · have hfg : DifferentiableAt ℝ (f - g) x := hf.sub hg
    rw [deriv_sub hf hg]
    have : deriv f x - deriv g x - deriv f x = -deriv g x := by ring
    rw [this, abs_neg]
  · have hnm : ¬ DifferentiableAt ℝ (f - g) x := by
      intro h
      have h' : DifferentiableAt ℝ (fun y => (f y - g y) + g y) x := h.add hg
      have heq : (fun y => (f y - g y) + g y) = f := by funext y; ring
      exact hf (heq ▸ h')
    rw [deriv_zero_of_not_differentiableAt hnm, deriv_zero_of_not_differentiableAt hf]
    simp

/-- The `pz`-form of `abs_deriv_sub_sub_le`. -/
lemma abs_pz_sub_le {F G : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hG : DifferentiableAt ℝ (fun z' => G z' θ) z) :
    |Work.Spaces.pz (F - G) z θ - Work.Spaces.pz F z θ| ≤ |Work.Spaces.pz G z θ| := by
  have h := abs_deriv_sub_sub_le (f := fun z' : ℝ => F z' θ)
    (g := fun z' : ℝ => G z' θ) hG
  have key : (fun z' : ℝ => (F - G) z' θ)
      = ((fun z' : ℝ => F z' θ) - fun z' : ℝ => G z' θ) := by
    funext z'; rfl
  have h1 : Work.Spaces.pz (F - G) z θ
      = deriv ((fun z' : ℝ => F z' θ) - fun z' : ℝ => G z' θ) z := by
    simp only [Work.Spaces.pz, key]
  have h2 : Work.Spaces.pz F z θ = deriv (fun z' : ℝ => F z' θ) z := rfl
  have h3 : Work.Spaces.pz G z θ = deriv (fun z' : ℝ => G z' θ) z := rfl
  rw [h1, h2, h3]
  exact h

/-- The `pth`-form of `abs_deriv_sub_sub_le`. -/
lemma abs_pth_sub_le {F G : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hG : DifferentiableAt ℝ (fun θ' => G z θ') θ) :
    |Work.Spaces.pth (F - G) z θ - Work.Spaces.pth F z θ| ≤ |Work.Spaces.pth G z θ| := by
  have h := abs_deriv_sub_sub_le (f := fun θ' : ℝ => F z θ')
    (g := fun θ' : ℝ => G z θ') hG
  have key : (fun θ' : ℝ => (F - G) z θ')
      = ((fun θ' : ℝ => F z θ') - fun θ' : ℝ => G z θ') := by
    funext θ'; rfl
  have h1 : Work.Spaces.pth (F - G) z θ
      = deriv ((fun θ' : ℝ => F z θ') - fun θ' : ℝ => G z θ') θ := by
    simp only [Work.Spaces.pth, key]
  have h2 : Work.Spaces.pth F z θ = deriv (fun θ' : ℝ => F z θ') θ := rfl
  have h3 : Work.Spaces.pth G z θ = deriv (fun θ' : ℝ => G z θ') θ := rfl
  rw [h1, h2, h3]
  exact h

/-- The `z`-error for the model profile `δ`. -/
lemma abs_pz_sub_le_delta {F : ℝ → ℝ → ℝ} {z θ : ℝ} (h1z : (0 : ℝ) < 1 + z)
    (hs2nn : 0 ≤ Real.sin (2 * θ)) :
    |Work.Spaces.pz (F - delta) z θ - Work.Spaces.pz F z θ|
      ≤ Real.sin (2 * θ) / (2 * (1 + z) ^ 2) := by
  have hG : DifferentiableAt ℝ (fun z' : ℝ => delta z' θ) z :=
    (hasDerivAt_delta_z θ z h1z).differentiableAt
  have h := abs_pz_sub_le (F := F) (G := delta) hG
  have hd : Work.Spaces.pz delta z θ = - Real.sin (2 * θ) / (2 * (1 + z) ^ 2) := by
    simp only [Work.Spaces.pz]
    exact (hasDerivAt_delta_z θ z h1z).deriv
  rw [hd] at h
  rw [abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * (1 + z) ^ 2), abs_neg,
    abs_of_nonneg hs2nn] at h
  exact h

/-- The `θ`-error for the model profile `δ`. -/
lemma abs_pth_sub_le_delta {F : ℝ → ℝ → ℝ} {z θ : ℝ} (h1z : (0 : ℝ) < 1 + z) :
    |Work.Spaces.pth (F - delta) z θ - Work.Spaces.pth F z θ|
      ≤ |Real.cos (2 * θ)| / (1 + z) := by
  have hG : DifferentiableAt ℝ (fun θ' : ℝ => delta z θ') θ :=
    (hasDerivAt_delta_th z θ h1z).differentiableAt
  have h := abs_pth_sub_le (F := F) (G := delta) hG
  have hd : Work.Spaces.pth delta z θ = Real.cos (2 * θ) / (1 + z) := by
    simp only [Work.Spaces.pth]
    exact (hasDerivAt_delta_th z θ h1z).deriv
  rw [hd] at h
  rwa [abs_div, abs_of_nonneg h1z.le] at h

/-! ## The exact algebraic relation between the slots at `F - δ` and at `F` -/

lemma Rop_sub_eq (F G : ℝ → ℝ → ℝ) (α z θ : ℝ) :
    Work.Construction.Rop α (F - G) z θ = Work.Construction.Rop α F z θ
      + (-(2 * Real.sin θ * G z θ)
          + α * Real.sin θ * z * (Work.Spaces.pz (F - G) z θ - Work.Spaces.pz F z θ)
          + Real.cos θ * (Work.Spaces.pth (F - G) z θ - Work.Spaces.pth F z θ))
        / Real.cos θ := by
  simp only [Work.Construction.Rop, Pi.sub_apply]
  rw [← add_div]
  congr 1
  ring

lemma Uop_sub_eq (F G : ℝ → ℝ → ℝ) (α z θ : ℝ) :
    Work.Construction.Uop α (F - G) z θ = Work.Construction.Uop α F z θ
      + (3 * G z θ - α * z * (Work.Spaces.pz (F - G) z θ - Work.Spaces.pz F z θ)) := by
  simp only [Work.Construction.Uop, Pi.sub_apply]
  ring

lemma Vop_sub_eq (F G : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Construction.Vop (F - G) z θ = Work.Construction.Vop F z θ
      + ((Work.Spaces.pth (F - G) z θ - Work.Spaces.pth F z θ) + Real.tan θ * G z θ) := by
  simp only [Work.Construction.Vop, Pi.sub_apply]
  ring

/-- `z/(1+z)² ≤ 1/4` for `z > 0`. -/
lemma div_sq_le_quarter {z : ℝ} (hz : 0 < z) : z / (1 + z) ^ 2 ≤ 1 / 4 := by
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < (1 + z) ^ 2)]
  nlinarith [sq_nonneg (1 - z)]

/-! ## The three slot bounds -/

lemma Rop_delta_bd {α z θ : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hz : 0 < z)
    (hθ1 : 0 < θ) (hθ2 : θ < π / 2) (F : ℝ → ℝ → ℝ) :
    |Work.Construction.Rop α (F - delta) z θ| ≤ |Work.Construction.Rop α F z θ| + 10 := by
  have h1z : (0 : ℝ) < 1 + z := by linarith
  have hcos : 0 < Real.cos θ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hcosne : Real.cos θ ≠ 0 := ne_of_gt hcos
  have hsin : 0 < Real.sin θ :=
    Real.sin_pos_of_pos_of_lt_pi hθ1 (by linarith [hθ2, Real.pi_pos])
  have hs2nn : 0 ≤ Real.sin (2 * θ) := by
    rw [Real.sin_two_mul]
    exact mul_nonneg (mul_nonneg (by norm_num) hsin.le) hcos.le
  have hez := abs_pz_sub_le_delta (F := F) h1z hs2nn
  have heth := abs_pth_sub_le_delta (F := F) (z := z) (θ := θ) h1z
  rw [Rop_sub_eq (F := F) (G := delta)]
  set ez : ℝ := Work.Spaces.pz (F - delta) z θ - Work.Spaces.pz F z θ with hezdef
  set eth : ℝ := Work.Spaces.pth (F - delta) z θ - Work.Spaces.pth F z θ with hethdef
  have hez' : |ez| ≤ Real.sin (2 * θ) / (2 * (1 + z) ^ 2) := by rw [hezdef]; exact hez
  have heth' : |eth| ≤ |Real.cos (2 * θ)| / (1 + z) := by rw [hethdef]; exact heth
  rw [show delta z θ = Real.sin (2 * θ) / (2 * (1 + z)) from rfl]
  have hE : |(-(2 * Real.sin θ * (Real.sin (2 * θ) / (2 * (1 + z))))
        + α * Real.sin θ * z * ez + Real.cos θ * eth) / Real.cos θ| ≤ 3 + α / 4 := by
    have hN : |-(2 * Real.sin θ * (Real.sin (2 * θ) / (2 * (1 + z))))
          + α * Real.sin θ * z * ez + Real.cos θ * eth|
        ≤ 2 * Real.sin θ * |Real.sin (2 * θ) / (2 * (1 + z))|
          + α * Real.sin θ * z * |ez| + Real.cos θ * |eth| := by
      have h2 : |-(2 * Real.sin θ * (Real.sin (2 * θ) / (2 * (1 + z))))
            + α * Real.sin θ * z * ez|
          ≤ |-(2 * Real.sin θ * (Real.sin (2 * θ) / (2 * (1 + z))))|
            + |α * Real.sin θ * z * ez| := abs_add_le _ _
      have h3 : |-(2 * Real.sin θ * (Real.sin (2 * θ) / (2 * (1 + z))))
            + α * Real.sin θ * z * ez + Real.cos θ * eth|
          ≤ |-(2 * Real.sin θ * (Real.sin (2 * θ) / (2 * (1 + z))))
              + α * Real.sin θ * z * ez| + |Real.cos θ * eth| := abs_add_le _ _
      have h4 : |-(2 * Real.sin θ * (Real.sin (2 * θ) / (2 * (1 + z))))|
          = 2 * Real.sin θ * |Real.sin (2 * θ) / (2 * (1 + z))| := by
        rw [abs_neg, abs_mul, abs_mul,
          abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), abs_of_nonneg hsin.le]
      have h5 : |α * Real.sin θ * z * ez| = α * Real.sin θ * z * |ez| := by
        rw [abs_mul, abs_mul, abs_mul,
          abs_of_nonneg hα0, abs_of_nonneg hsin.le, abs_of_nonneg hz.le]
      have h6 : |Real.cos θ * eth| = Real.cos θ * |eth| := by
        rw [abs_mul, abs_of_nonneg hcos.le]
      linarith
    have hstep : |(-(2 * Real.sin θ * (Real.sin (2 * θ) / (2 * (1 + z))))
          + α * Real.sin θ * z * ez + Real.cos θ * eth) / Real.cos θ|
        ≤ (2 * Real.sin θ * |Real.sin (2 * θ) / (2 * (1 + z))|
            + α * Real.sin θ * z * |ez| + Real.cos θ * |eth|) / Real.cos θ := by
      rw [abs_div, abs_of_nonneg hcos.le]
      exact div_le_div_of_nonneg_right hN hcos.le
    have hsplit : (2 * Real.sin θ * |Real.sin (2 * θ) / (2 * (1 + z))|
          + α * Real.sin θ * z * |ez| + Real.cos θ * |eth|) / Real.cos θ
        = 2 * Real.sin θ * |Real.sin (2 * θ) / (2 * (1 + z))| / Real.cos θ
          + α * Real.sin θ * z * |ez| / Real.cos θ + |eth| := by
      field_simp
    rw [hsplit] at hstep
    have hA : 2 * Real.sin θ * |Real.sin (2 * θ) / (2 * (1 + z))| / Real.cos θ ≤ 2 := by
      have hkey : 2 * Real.sin θ * |Real.sin (2 * θ) / (2 * (1 + z))| / Real.cos θ
          = 2 * Real.sin θ ^ 2 / (1 + z) := by
        rw [abs_of_nonneg (div_nonneg hs2nn (by positivity)), Real.sin_two_mul]
        field_simp
      rw [hkey, div_le_iff₀ h1z]
      nlinarith [Real.sin_sq_le_one θ, hz]
    have hB : α * Real.sin θ * z * |ez| / Real.cos θ ≤ α / 4 := by
      have hkey : α * Real.sin θ * z * |ez| / Real.cos θ
          ≤ α * Real.sin θ * z * (Real.sin (2 * θ) / (2 * (1 + z) ^ 2)) / Real.cos θ := by
        apply div_le_div_of_nonneg_right _ hcos.le
        exact mul_le_mul_of_nonneg_left hez' (by positivity)
      refine le_trans hkey ?_
      have hkey2 : α * Real.sin θ * z * (Real.sin (2 * θ) / (2 * (1 + z) ^ 2)) / Real.cos θ
          = α * (z / (1 + z) ^ 2) * Real.sin θ ^ 2 := by
        rw [Real.sin_two_mul]
        field_simp
      rw [hkey2]
      have h1 : α * (z / (1 + z) ^ 2) ≤ α * (1 / 4) :=
        mul_le_mul_of_nonneg_left (div_sq_le_quarter hz) hα0
      have h2 : (0 : ℝ) ≤ Real.sin θ ^ 2 := sq_nonneg _
      have h3 : (0 : ℝ) ≤ α * (1 / 4) := by positivity
      have h4 := mul_le_mul h1 (Real.sin_sq_le_one θ) h2 h3
      linarith
    have hC : |eth| ≤ 1 := by
      have h1 : |Real.cos (2 * θ)| / (1 + z) ≤ 1 / (1 + z) :=
        div_le_div_of_nonneg_right (Real.abs_cos_le_one (2 * θ)) h1z.le
      have h2 : (1 : ℝ) / (1 + z) ≤ 1 := by
        rw [div_le_one h1z]; linarith
      linarith
    linarith
  linarith [abs_add_le (Work.Construction.Rop α F z θ)
    ((-(2 * Real.sin θ * (Real.sin (2 * θ) / (2 * (1 + z))))
      + α * Real.sin θ * z * ez + Real.cos θ * eth) / Real.cos θ), hE, hα1]

lemma Uop_div_s2_delta_bd {α z θ : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hz : 0 < z)
    (hθ1 : 0 < θ) (hθ2 : θ < π / 2) (F : ℝ → ℝ → ℝ) :
    |Work.Construction.Uop α (F - delta) z θ / Work.Construction.s2 θ|
      ≤ |Work.Construction.Uop α F z θ / Work.Construction.s2 θ| + 10 := by
  have h1z : (0 : ℝ) < 1 + z := by linarith
  have hcos : 0 < Real.cos θ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hsin : 0 < Real.sin θ :=
    Real.sin_pos_of_pos_of_lt_pi hθ1 (by linarith [hθ2, Real.pi_pos])
  have hs2pos : 0 < Real.sin (2 * θ) := by
    rw [Real.sin_two_mul]
    exact mul_pos (mul_pos (by norm_num) hsin) hcos
  have hs2ne : Real.sin (2 * θ) ≠ 0 := ne_of_gt hs2pos
  have hez := abs_pz_sub_le_delta (F := F) h1z hs2pos.le
  simp only [Work.Construction.s2]
  rw [Uop_sub_eq (F := F) (G := delta), add_div]
  set ez : ℝ := Work.Spaces.pz (F - delta) z θ - Work.Spaces.pz F z θ with hezdef
  have hez' : |ez| ≤ Real.sin (2 * θ) / (2 * (1 + z) ^ 2) := by rw [hezdef]; exact hez
  rw [show delta z θ = Real.sin (2 * θ) / (2 * (1 + z)) from rfl]
  have hE : |(3 * (Real.sin (2 * θ) / (2 * (1 + z))) - α * z * ez) / Real.sin (2 * θ)|
      ≤ 3 / 2 + α / 8 := by
    have hN : |3 * (Real.sin (2 * θ) / (2 * (1 + z))) - α * z * ez|
        ≤ 3 * |Real.sin (2 * θ) / (2 * (1 + z))| + α * z * |ez| := by
      have h2 : |3 * (Real.sin (2 * θ) / (2 * (1 + z))) - α * z * ez|
          ≤ |3 * (Real.sin (2 * θ) / (2 * (1 + z)))| + |α * z * ez| := by
        calc |3 * (Real.sin (2 * θ) / (2 * (1 + z))) - α * z * ez|
            = |3 * (Real.sin (2 * θ) / (2 * (1 + z))) + (-(α * z * ez))| := by rw [sub_eq_add_neg]
          _ ≤ |3 * (Real.sin (2 * θ) / (2 * (1 + z)))| + |-(α * z * ez)| := abs_add_le _ _
          _ = |3 * (Real.sin (2 * θ) / (2 * (1 + z)))| + |α * z * ez| := by rw [abs_neg]
      have h3 : |3 * (Real.sin (2 * θ) / (2 * (1 + z)))| = 3 * |Real.sin (2 * θ) / (2 * (1 + z))| := by
        rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)]
      have h4 : |α * z * ez| = α * z * |ez| := by
        rw [abs_mul, abs_mul, abs_of_nonneg hα0, abs_of_nonneg hz.le]
      linarith
    have hstep : |(3 * (Real.sin (2 * θ) / (2 * (1 + z))) - α * z * ez) / Real.sin (2 * θ)|
        ≤ (3 * |Real.sin (2 * θ) / (2 * (1 + z))| + α * z * |ez|) / Real.sin (2 * θ) := by
      rw [abs_div, abs_of_nonneg hs2pos.le]
      exact div_le_div_of_nonneg_right hN hs2pos.le
    have hsplit : (3 * |Real.sin (2 * θ) / (2 * (1 + z))| + α * z * |ez|) / Real.sin (2 * θ)
        = 3 * |Real.sin (2 * θ) / (2 * (1 + z))| / Real.sin (2 * θ)
          + α * z * |ez| / Real.sin (2 * θ) := by
      rw [add_div]
    rw [hsplit] at hstep
    have hA : 3 * |Real.sin (2 * θ) / (2 * (1 + z))| / Real.sin (2 * θ) ≤ 3 / 2 := by
      have hkey : 3 * |Real.sin (2 * θ) / (2 * (1 + z))| / Real.sin (2 * θ)
          = 3 / (2 * (1 + z)) := by
        rw [abs_of_nonneg (div_nonneg hs2pos.le (by positivity))]
        field_simp
      rw [hkey, div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (1 + z))]
      linarith
    have hB : α * z * |ez| / Real.sin (2 * θ) ≤ α / 8 := by
      have hkey : α * z * |ez| / Real.sin (2 * θ)
          ≤ α * z * (Real.sin (2 * θ) / (2 * (1 + z) ^ 2)) / Real.sin (2 * θ) := by
        apply div_le_div_of_nonneg_right _ hs2pos.le
        exact mul_le_mul_of_nonneg_left hez' (by positivity)
      refine le_trans hkey ?_
      have hkey2 : α * z * (Real.sin (2 * θ) / (2 * (1 + z) ^ 2)) / Real.sin (2 * θ)
          = α * z / (2 * (1 + z) ^ 2) := by
        field_simp
      rw [hkey2]
      have hz4 : z / (1 + z) ^ 2 ≤ 1 / 4 := div_sq_le_quarter hz
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (1 + z) ^ 2)]
      have hz4' : z ≤ (1 + z) ^ 2 / 4 := by
        rw [div_le_iff₀ (by positivity : (0 : ℝ) < (1 + z) ^ 2)] at hz4
        linarith
      have h6 : α * z ≤ α * ((1 + z) ^ 2 / 4) := mul_le_mul_of_nonneg_left hz4' hα0
      have h7 : α / 8 * (2 * (1 + z) ^ 2) = α * ((1 + z) ^ 2 / 4) := by ring
      linarith
    linarith
  linarith [abs_add_le (Work.Construction.Uop α F z θ / Real.sin (2 * θ))
    ((3 * (Real.sin (2 * θ) / (2 * (1 + z))) - α * z * ez) / Real.sin (2 * θ)), hE, hα1]

lemma Vop_delta_bd {z θ : ℝ} (hz : 0 < z) (hθ1 : 0 < θ) (hθ2 : θ < π / 2)
    (F : ℝ → ℝ → ℝ) :
    |Work.Construction.Vop (F - delta) z θ| ≤ |Work.Construction.Vop F z θ| + 10 := by
  have h1z : (0 : ℝ) < 1 + z := by linarith
  have hcos : 0 < Real.cos θ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hsin : 0 < Real.sin θ :=
    Real.sin_pos_of_pos_of_lt_pi hθ1 (by linarith [hθ2, Real.pi_pos])
  have hs2nn : 0 ≤ Real.sin (2 * θ) := by
    rw [Real.sin_two_mul]
    exact mul_nonneg (mul_nonneg (by norm_num) hsin.le) hcos.le
  have heth := abs_pth_sub_le_delta (F := F) (z := z) (θ := θ) h1z
  rw [Vop_sub_eq (F := F) (G := delta)]
  set eth : ℝ := Work.Spaces.pth (F - delta) z θ - Work.Spaces.pth F z θ with hethdef
  have heth' : |eth| ≤ |Real.cos (2 * θ)| / (1 + z) := by rw [hethdef]; exact heth
  rw [show delta z θ = Real.sin (2 * θ) / (2 * (1 + z)) from rfl]
  have hE : |eth + Real.tan θ * (Real.sin (2 * θ) / (2 * (1 + z)))| ≤ 2 := by
    have htanval : Real.tan θ * (Real.sin (2 * θ) / (2 * (1 + z)))
        = Real.sin θ ^ 2 / (1 + z) := by
      rw [Real.tan_eq_sin_div_cos, Real.sin_two_mul]
      field_simp
    have htanabs : |Real.tan θ * (Real.sin (2 * θ) / (2 * (1 + z)))|
        = Real.sin θ ^ 2 / (1 + z) := by
      rw [htanval, abs_of_nonneg (div_nonneg (sq_nonneg _) (by positivity))]
    have h1 : |eth + Real.tan θ * (Real.sin (2 * θ) / (2 * (1 + z)))|
        ≤ |eth| + |Real.tan θ * (Real.sin (2 * θ) / (2 * (1 + z)))| := abs_add_le _ _
    rw [htanabs] at h1
    have h2 : |eth| ≤ 1 / (1 + z) := by
      refine le_trans heth' ?_
      exact div_le_div_of_nonneg_right (Real.abs_cos_le_one (2 * θ)) h1z.le
    have h3 : Real.sin θ ^ 2 / (1 + z) ≤ 1 / (1 + z) :=
      div_le_div_of_nonneg_right (Real.sin_sq_le_one θ) h1z.le
    have h4 : (1 : ℝ) / (1 + z) ≤ 1 := by
      rw [div_le_one h1z]; linarith
    linarith
  linarith [abs_add_le (Work.Construction.Vop F z θ)
    (eth + Real.tan θ * (Real.sin (2 * θ) / (2 * (1 + z)))), hE]

/-- Auxiliary fact for `N0_N_Transport_pt_le`: subtracting the explicit profile
`δ(z,θ) = sin(2θ)/(2(1+z))` (which is `Theta α (Fstar α)`, the singular part of the
stream function of the reference profile) changes each of the three slots `Rop`, `Uop/s2`,
`Vop` by at most `10`.

Hint for the proof.  `Rop α Ψ z θ = (2 sinθ·Ψ + α sinθ·z·pz Ψ + cosθ·pth Ψ)/cosθ`,
`Uop α Ψ z θ = -3Ψ - α z·pz Ψ`, `Vop Ψ z θ = pth Ψ - tanθ·Ψ`; `δ` is smooth for `z ≠ -1`,
with `pz δ z θ = -sin(2θ)/(2(1+z)^2)` and `pth δ z θ = cos(2θ)/(1+z)`.  The obstruction is
that `pz`/`pth` are totalised `deriv`s and are *not* additive in general: if
`f := fun z' => Ψ1 z' θ` is not `DifferentiableAt ℝ · z` then neither is `f - δ`, and both
differentials are `0` (`deriv_zero_of_not_differentiableAt`); if it is differentiable then
`deriv_sub` applies.  In both cases the signed error
`deriv (f - δ) z - deriv f z + deriv δ z` is bounded in absolute value by `|deriv δ z|`
(and likewise in `θ`), which gives the claim with the three explicit bounds
`|Rop α δ| ≤ 2 + α/4 + 1`, `|Uop α δ / s2 θ| ≤ 3/2 + α/8`, `|Vop δ| ≤ 2` (using
`Real.sin_two_mul`, `Real.tan_eq_sin_div_cos`, `0 < cos θ`, `sin(2θ) ≠ 0`). -/
theorem Psivar0_slots_sub : ∀ {α z θ : ℝ}, α ∈ Set.Ioc 0 1 → z ∈ Set.Ioi (0 : ℝ) →
    θ ∈ Set.Ioo (0 : ℝ) (π / 2) → ∀ {Ψ1 : ℝ → ℝ → ℝ},
      |Work.Construction.Rop α (fun z θ => Ψ1 z θ - Real.sin (2 * θ) / (2 * (1 + z))) z θ|
          ≤ |Work.Construction.Rop α Ψ1 z θ| + 10 ∧
      |Work.Construction.Uop α (fun z θ => Ψ1 z θ - Real.sin (2 * θ) / (2 * (1 + z))) z θ
          / Work.Construction.s2 θ|
          ≤ |Work.Construction.Uop α Ψ1 z θ / Work.Construction.s2 θ| + 10 ∧
      |Work.Construction.Vop (fun z θ => Ψ1 z θ - Real.sin (2 * θ) / (2 * (1 + z))) z θ|
          ≤ |Work.Construction.Vop Ψ1 z θ| + 10 := by
  intro α z θ hα hz hθ Ψ1
  obtain ⟨hα0, hα1⟩ := hα
  refine ⟨?_, ?_, ?_⟩
  · exact Rop_delta_bd hα0.le hα1 hz hθ.1 hθ.2 Ψ1
  · exact Uop_div_s2_delta_bd hα0.le hα1 hz hθ.1 hθ.2 Ψ1
  · exact Vop_delta_bd hz hθ.1 hθ.2 Ψ1

end Work.FTS.StrongEps.E5Aux2
