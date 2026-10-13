/-
# The fundamental model: core API

First instalment of the API of `Submission/Work/FM/Defs.lean` (the paper's
`L₁₂^K`, the profile `F_*`, the self-similar family and the model equation).
Self-contained apart from the definitions.
-/

import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Submission.Work.FM.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace Work.FM

/-! ## The angular density: elementary rewrites -/

/-- Pulling the factor `1/s` out of the angular integral defining `L12dens`. -/
theorem L12dens_eq {K : ℝ → ℝ} {f : ℝ → ℝ → ℝ} {s : ℝ} (hs : s ≠ 0) :
    L12dens K f s = (∫ θ in Icc 0 (Real.pi / 2), K θ * f s θ) / s := by
  rw [L12dens, integral_div]

/-- The density of a separable function `(s,θ) ↦ g s * Γ θ` factors. -/
theorem L12dens_separable {K Γ : ℝ → ℝ} {g : ℝ → ℝ} {s : ℝ}
    (hΓ : IntegrableOn (fun θ => K θ * Γ θ) (Icc 0 (Real.pi / 2))) :
    L12dens K (fun s θ => g s * Γ θ) s
      = (∫ θ in Icc 0 (Real.pi / 2), K θ * Γ θ) * (g s / s) := by
  rw [L12dens]
  have hpoint : (fun θ => K θ * (g s * Γ θ) / s)
      = fun θ => (K θ * Γ θ) * (g s / s) := by
    funext θ; ring
  rw [hpoint, integral_mul_const]

/-- `L₁₂^K` of a separable function of the form `(s,θ) ↦ g s * Γ θ`: this is the
form in which the operator is computed for the self-similar family. -/
theorem L12_separable {K Γ : ℝ → ℝ} {g : ℝ → ℝ} {ρ : ℝ}
    (hΓ : IntegrableOn (fun θ => K θ * Γ θ) (Icc 0 (Real.pi / 2)))
    (hg : IntegrableOn (fun s => g s / s) (Ioi ρ)) :
    L12 K (fun s θ => g s * Γ θ) ρ
      = (∫ θ in Icc 0 (Real.pi / 2), K θ * Γ θ) * (∫ s in Ioi ρ, g s / s) := by
  rw [L12]
  have hpoint : (fun s => L12dens K (fun s θ => g s * Γ θ) s)
      = fun s => (∫ θ in Icc 0 (Real.pi / 2), K θ * Γ θ) * (g s / s) := by
    funext s; exact L12dens_separable hΓ
  rw [hpoint, integral_const_mul]

/-- `L₁₂^K` is additive in the profile. -/
theorem L12_add {K : ℝ → ℝ} {f g : ℝ → ℝ → ℝ} {ρ : ℝ}
    (hf : ∀ s, IntegrableOn (fun θ => K θ * f s θ / s) (Icc 0 (Real.pi / 2)))
    (hg : ∀ s, IntegrableOn (fun θ => K θ * g s θ / s) (Icc 0 (Real.pi / 2)))
    (hF : IntegrableOn (L12dens K f) (Ioi ρ)) (hG : IntegrableOn (L12dens K g) (Ioi ρ)) :
    L12 K (fun s θ => f s θ + g s θ) ρ = L12 K f ρ + L12 K g ρ := by
  rw [L12]
  have hpoint : ∀ s, L12dens K (fun s θ => f s θ + g s θ) s
      = L12dens K f s + L12dens K g s := by
    intro s
    rw [L12dens, L12dens, L12dens, ← integral_add (hf s) (hg s)]
    congr 1 with θ
    ring
  simp only [hpoint]
  exact integral_add hF hG

/-- `L₁₂^K` is homogeneous in the profile (no integrability needed: the Bochner
integral is total). -/
theorem L12_const_mul {K : ℝ → ℝ} {f : ℝ → ℝ → ℝ} {ρ c : ℝ} :
    L12 K (fun s θ => c * f s θ) ρ = c * L12 K f ρ := by
  rw [L12]
  have hpoint : ∀ s, L12dens K (fun s θ => c * f s θ) s = c * L12dens K f s := by
    intro s
    rw [L12dens, L12dens, ← integral_const_mul]
    congr 1 with θ
    ring
  simp only [hpoint]
  exact integral_const_mul c _

/-! ## Calculus of the profile -/

theorem hasDerivAt_add_const (c z : ℝ) : HasDerivAt (fun t : ℝ => c + t) 1 z := by
  simpa using (hasDerivAt_id' (𝕜 := ℝ) z).const_add c

theorem hasDerivAt_one_add_sq (z : ℝ) :
    HasDerivAt (fun t : ℝ => (1 + t) ^ 2) (2 * (1 + z)) z := by
  have h := hasDerivAt_add_const 1 z
  convert h.pow 2 using 1 <;> (first | (funext x; simp) | ring_nf)

theorem hasDerivAt_two_mul (z : ℝ) : HasDerivAt (fun t : ℝ => 2 * t) 2 z := by
  simpa using (hasDerivAt_id' (𝕜 := ℝ) z).const_mul 2

theorem hasDerivAt_inv_add_const (c x : ℝ) (h : c + x ≠ 0) :
    HasDerivAt (fun t : ℝ => (c + t)⁻¹) (-1 / (c + x) ^ 2) x := by
  have h1 := hasDerivAt_add_const c x
  convert h1.inv h using 1 <;> (first | (funext t; simp [Pi.inv_apply]) | ring_nf)

/-- `d/dt (a/(c+t)) = -a/(c+t)²`. -/
theorem hasDerivAt_div_add_const (a c x : ℝ) (h : c + x ≠ 0) :
    HasDerivAt (fun t : ℝ => a / (c + t)) (-a / (c + x) ^ 2) x := by
  have h2 := hasDerivAt_inv_add_const c x h
  convert h2.const_mul a using 1 <;>
    (first | (funext t; simp [Pi.inv_apply, div_eq_mul_inv]) | ring_nf)

theorem hasDerivAt_Fstar (z : ℝ) (hz : -1 < z) :
    HasDerivAt Fstar (2 * (1 - z) / (1 + z) ^ 3) z := by
  have hz1 : (1 + z) ^ 2 ≠ 0 := by
    have h : (0 : ℝ) < 1 + z := by linarith
    positivity
  have h := (hasDerivAt_two_mul z).div (hasDerivAt_one_add_sq z) hz1
  have hfun : ((fun t : ℝ => 2 * t) / fun t => (1 + t) ^ 2) = Fstar := by
    funext t; unfold Fstar; rfl
  rw [hfun] at h
  convert h using 1 <;>
    (first | (funext t; simp [Pi.div_apply]) | (field_simp; ring) | ring_nf)

theorem hasDerivAt_Fstarp (z : ℝ) (hz : -1 < z) :
    HasDerivAt Fstarp ((1 - z) / (1 + z) ^ 3) z := by
  have hz1 : (1 + z) ^ 2 ≠ 0 := by
    have h : (0 : ℝ) < 1 + z := by linarith
    positivity
  have hid : HasDerivAt (fun t : ℝ => t) 1 z := hasDerivAt_id' (𝕜 := ℝ) z
  have h := hid.div (hasDerivAt_one_add_sq z) hz1
  have hfun : ((fun t : ℝ => t) / fun t => (1 + t) ^ 2) = Fstarp := by
    funext t; unfold Fstarp; rfl
  rw [hfun] at h
  convert h using 1 <;>
    (first | (funext t; simp [Pi.div_apply]) | (field_simp; ring) | ring_nf)

theorem deriv_Fstar (z : ℝ) (hz : -1 < z) : deriv Fstar z = 2 * (1 - z) / (1 + z) ^ 3 :=
  (hasDerivAt_Fstar z hz).deriv

theorem deriv_Fstarp (z : ℝ) (hz : -1 < z) : deriv Fstarp z = (1 - z) / (1 + z) ^ 3 :=
  (hasDerivAt_Fstarp z hz).deriv

/-! ## The two improper integrals of the profile -/

theorem integral_Ioi_Fstar_div (z : ℝ) (hz : 0 ≤ z) :
    ∫ s in Ioi z, Fstar s / s = 2 / (1 + z) := by
  have hcongr : EqOn (fun s => Fstar s / s) (fun s => 2 / (1 + s) ^ 2) (Ioi z) := by
    intro s hs
    have hs0 : s ≠ 0 := by have := hs.out; linarith
    unfold Fstar
    first | (field_simp; ring) | (field_simp) | ring_nf
  rw [setIntegral_congr_fun measurableSet_Ioi hcongr]
  have key := integral_Ioi_of_hasDerivAt_of_nonneg'
    (g := fun t : ℝ => -2 / (1 + t)) (g' := fun t : ℝ => 2 / (1 + t) ^ 2) (a := z) (l := 0)
    ?_ ?_ ?_
  · rw [key]
    ring
  · intro x hx
    have hx1 : (1 : ℝ) + x ≠ 0 := by have := hx.out; linarith
    have h := hasDerivAt_div_add_const (-2) 1 x hx1
    convert h using 1 <;> (first | ring | (funext t; simp) | (field_simp; ring))
  · intro x hx
    have hx0 : (0 : ℝ) < 1 + x := by have := hx.out; linarith
    positivity
  · have h1 : Tendsto (fun t : ℝ => (1 : ℝ) + t) atTop atTop :=
      tendsto_atTop_add_const_left atTop (1 : ℝ) tendsto_id
    have h2 : Tendsto (fun t : ℝ => ((1 : ℝ) + t)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp h1
    have h3 := h2.const_mul (-2 : ℝ)
    simpa [div_eq_mul_inv] using h3

theorem integral_Ioi_Fstarp_div (z : ℝ) (hz : 0 ≤ z) :
    ∫ s in Ioi z, Fstarp s / s = 1 / (1 + z) := by
  have hcongr : EqOn (fun s => Fstarp s / s) (fun s => 1 / (1 + s) ^ 2) (Ioi z) := by
    intro s hs
    have hs0 : s ≠ 0 := by have := hs.out; linarith
    unfold Fstarp
    first | (field_simp; ring) | (field_simp) | ring_nf
  rw [setIntegral_congr_fun measurableSet_Ioi hcongr]
  have key := integral_Ioi_of_hasDerivAt_of_nonneg'
    (g := fun t : ℝ => -1 / (1 + t)) (g' := fun t : ℝ => 1 / (1 + t) ^ 2) (a := z) (l := 0)
    ?_ ?_ ?_
  · rw [key]
    ring
  · intro x hx
    have hx1 : (1 : ℝ) + x ≠ 0 := by have := hx.out; linarith
    have h := hasDerivAt_div_add_const (-1) 1 x hx1
    convert h using 1 <;> (first | ring | (funext t; simp) | (field_simp; ring))
  · intro x hx
    have hx0 : (0 : ℝ) < 1 + x := by have := hx.out; linarith
    positivity
  · have h1 : Tendsto (fun t : ℝ => (1 : ℝ) + t) atTop atTop :=
      tendsto_atTop_add_const_left atTop (1 : ℝ) tendsto_id
    have h2 : Tendsto (fun t : ℝ => ((1 : ℝ) + t)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp h1
    have h3 := h2.const_mul (-1 : ℝ)
    simpa [div_eq_mul_inv] using h3

/-- The paper's profile identity (line 467) for `F_*(z) = 2z/(1+z)²`. -/
theorem Fstar_profile (z : ℝ) (hz : 0 ≤ z) :
    Fstar z + z * deriv Fstar z = Fstar z * ∫ s in Ioi z, Fstar s / s := by
  rw [deriv_Fstar z (by linarith), integral_Ioi_Fstar_div z hz]
  unfold Fstar
  first | (field_simp; ring) | (field_simp) | ring_nf

/-- The profile identity in the normalization of Lemma `FMSelfSimilar`,
`F_{*,rad}(z) = z/(1+z)²`; the factor `2` on the right is a consequence of
`F_* = 2 F_{*,rad}`. -/
theorem Fstarp_profile (z : ℝ) (hz : 0 ≤ z) :
    Fstarp z + z * deriv Fstarp z = 2 * Fstarp z * ∫ s in Ioi z, Fstarp s / s := by
  rw [deriv_Fstarp z (by linarith), integral_Ioi_Fstarp_div z hz]
  unfold Fstarp
  first | (field_simp; ring) | (field_simp) | ring_nf

/-! ## The Riccati solution and the blow-up rate -/

/-- The explicit solution of the scalar Riccati equation `v' = v²/2`:
if `v(t) = V₀/(1 - t V₀/2)` then `v' = v²/2`. -/
theorem hasDerivAt_riccati {V₀ : ℝ → ℝ} {ρ t : ℝ} (h0 : 1 - t * V₀ ρ / 2 ≠ 0) :
    HasDerivAt (fun t => V₀ ρ / (1 - t * V₀ ρ / 2))
      ((V₀ ρ / (1 - t * V₀ ρ / 2)) ^ 2 / 2) t := by
  have hne : 1 - t * (V₀ ρ / 2) ≠ 0 := by
    intro hc
    refine h0 ?_
    have h1 : t * V₀ ρ / 2 = t * (V₀ ρ / 2) := by ring
    rw [h1]; exact hc
  have hden : HasDerivAt (fun y : ℝ => 1 - y * (V₀ ρ / 2)) (-(V₀ ρ / 2)) t := by
    have h2 : HasDerivAt (fun y : ℝ => y * (V₀ ρ / 2)) (V₀ ρ / 2) t := by
      simpa using (hasDerivAt_id' (𝕜 := ℝ) t).mul_const (V₀ ρ / 2)
    have hc : HasDerivAt (fun _ : ℝ => (1 : ℝ)) 0 t := hasDerivAt_const t 1
    have h := hc.sub h2
    convert h using 1 <;> (first | (funext y; simp) | ring_nf)
  have hinv : HasDerivAt (fun y : ℝ => (1 - y * (V₀ ρ / 2))⁻¹)
      (-(-(V₀ ρ / 2)) / (1 - t * (V₀ ρ / 2)) ^ 2) t := by
    convert hden.inv hne using 1 <;> (first | (funext y; simp [Pi.inv_apply]) | ring_nf)
  have h3 : HasDerivAt (fun y : ℝ => V₀ ρ * (1 - y * (V₀ ρ / 2))⁻¹)
      (V₀ ρ * (-(-(V₀ ρ / 2)) / (1 - t * (V₀ ρ / 2)) ^ 2)) t := hinv.const_mul (V₀ ρ)
  have hfun : (fun y : ℝ => V₀ ρ * (1 - y * (V₀ ρ / 2))⁻¹)
      = fun y => V₀ ρ / (1 - y * V₀ ρ / 2) := by
    funext y
    rw [div_eq_mul_inv]
    congr 1
    ring
  rw [hfun] at h3
  have hval : V₀ ρ * (-(-(V₀ ρ / 2)) / (1 - t * (V₀ ρ / 2)) ^ 2)
      = (V₀ ρ / (1 - t * V₀ ρ / 2)) ^ 2 / 2 := by
    first | (field_simp; ring) | field_simp | ring_nf
  rw [hval] at h3
  exact h3

/-- `t ↦ 2/(1-t)` blows up as `t → 1⁻`. -/
theorem tendsto_two_div_one_sub :
    Tendsto (fun t : ℝ => 2 / (1 - t)) (nhdsWithin 1 (Iio 1)) atTop := by
  have h0 : Tendsto (fun t : ℝ => (1 : ℝ) - t) (nhdsWithin 1 (Iio 1)) (𝓝 0) := by
    have hid : Tendsto (fun t : ℝ => t) (nhdsWithin 1 (Iio 1)) (𝓝 (1 : ℝ)) :=
      tendsto_id.mono_right inf_le_left
    have hc : Tendsto (fun _ : ℝ => (1 : ℝ)) (nhdsWithin 1 (Iio 1)) (𝓝 (1 : ℝ)) :=
      tendsto_const_nhds
    have h : Tendsto (fun t : ℝ => (1 : ℝ) - t) (nhdsWithin 1 (Iio 1)) (𝓝 (1 - 1)) := by
      simpa using hc.sub hid
    simpa using h
  have h1 : Tendsto (fun t : ℝ => (1 : ℝ) - t) (nhdsWithin 1 (Iio 1)) (nhdsWithin 0 (Ioi 0)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨h0, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact sub_pos.mpr (show t < 1 from ht)
  have h2 : Tendsto (fun t : ℝ => ((1 : ℝ) - t)⁻¹) (nhdsWithin 1 (Iio 1)) atTop :=
    tendsto_inv_nhdsGT_zero.comp h1
  have h3 := h2.const_mul_atTop (show (0 : ℝ) < 2 by norm_num)
  simpa [div_eq_mul_inv] using h3

/-! ## The self-similar family -/

/-- The self-similar family at time `0`, i.e. the profile of §Modulation. -/
theorem selfSim_zero (K Γ : ℝ → ℝ) (α ρ θ : ℝ) :
    selfSim K Γ α ρ θ 0 = 2 * α * (Γ θ / cK K Γ) * Fstarp (ρ ^ α) := by
  simp [selfSim]

/-- The angular density of the self-similar family. -/
theorem L12dens_selfSim {K Γ : ℝ → ℝ} {α : ℝ} {s t : ℝ}
    (hc : cK K Γ ≠ 0)
    (hΓ : IntegrableOn (fun θ => K θ * Γ θ) (Icc 0 (Real.pi / 2))) (ht : t ≠ 1) :
    L12dens K (fun s θ => selfSim K Γ α s θ t) s
      = (2 * α / (1 - t)) * (Fstarp (s ^ α / (1 - t)) / s) := by
  have hpoint : ∀ θ, K θ * selfSim K Γ α s θ t / s
      = (K θ * Γ θ / cK K Γ)
          * ((2 * α / (1 - t)) * (Fstarp (s ^ α / (1 - t)) / s)) := by
    intro θ
    simp only [selfSim, div_eq_mul_inv]
    ring
  rw [L12dens]
  simp only [hpoint]
  rw [integral_mul_const, integral_div]
  rw [cK] at hc ⊢
  rw [div_self hc, one_mul]

end Work.FM
