/-
# `Work.FTS_RegExport.RXR5L.ProdDefs` — the objects of `EllProd_C1JetFull`

The three product slots of the `R5` assembly at the sanitised family

  `G := gS α (tauExt g)`,  `Φ := psiR α Φs E (tauExt g)`,  `Φ̃_τ := PhiTil (pExp α) (F_τ) (slice Φ τ)`

with `F_τ := Ftau (pExp α) G τ`:

* `P1 = Rop (pExp α) Φ̃_τ · F_τ`,
* `P2 = (Uop (pExp α) Φ̃_τ / sin 2θ) · (D_θ F_τ)`,
* `P3 = Vop Φ̃_τ · (D_z F_τ)`.

`P2` is written with the split `Uop Φ̃ = (Uop Φ̃ / sin 2θ) · sin 2θ` (which is what the
`vanish0` slot bounds of `RXT.velVanish2` control); the two forms agree on the *whole* box
`z ≥ 0, θ ∈ Iθ, τ ∈ [0,S]`.

This file fixes the abbreviations and the elementary endpoint facts about the angular profile
`Γ(θ) = (sinθ cos²θ)^α` at the profile exponent (`Gmp α = Work.FTS.Regularity.Gamma α`, which
is `Work.Spaces.Gam (pExp α)` definitionally).
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS_RegExport.RXT.velVanish2Aux
import Submission.Work.FTS_RegExport.RXT.weighted_system
import Submission.Work.FTS_RegExport.RXR5L.Ftau_C1Jet
import Submission.Work.FTS_RegExport.RXR5L.DthFtau_C1Jet
import Submission.Work.FTS_RegExport.RXR5L.DzFtau_C1Jet

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open Set Filter MeasureTheory

namespace Work.FTS_RegExport.RXR5L

open Work.FTS.Galerkin (Fn Fam slice)
open Work.FTS.Regularity (pExp gSlice)

set_option autoImplicit false

/-! ## §1 The angular profile and the endpoint distance -/

/-- The angular weight `Γ(θ) = (sinθ cos²θ)^α` at the **profile** exponent, i.e.
`Work.Spaces.Gam (pExp α)`.  It is `Work.FTS.Regularity.Gamma α` definitionally. -/
abbrev Gmp (α : ℝ) : ℝ → ℝ := fun θ => Work.FTS.Regularity.Gamma α θ

/-- The distance to the nearer angular endpoint. -/
def dang (θ : ℝ) : ℝ := min θ (π / 2 - θ)

theorem Gmp_eq_Gam (α θ : ℝ) : Gmp α θ = Work.Spaces.Gam (pExp α) θ :=
  Work.FTS.Regularity.Gamma_eq_Gam α θ

theorem Gmp_nonneg {α θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Gmp α θ :=
  Work.ConstructionInstance.Gamma_nonneg hθ

theorem Gmp_le_one {α θ : ℝ} (hα : 0 ≤ α) (hθ : θ ∈ Work.Spaces.Iθ) : Gmp α θ ≤ 1 :=
  Work.ConstructionInstance.Gamma_le_one hα hθ

/-! ## §2 The modulated residual, the three coefficients and the three factors -/

/-- The modulated residual `Φ̃_τ = PhiTil (pExp α) (F_τ) (slice Φ τ)`. -/
abbrev PhiT (α : ℝ) (Φs : Fn) (E : Fn →ₗ[ℝ] Fn) (g : Fam) (τ : ℝ) : Fn :=
  Work.FTS_RegExport.RXT.v2_PhiT α Φs E g τ

/-- The `R`-coefficient `Rop (pExp α) Φ̃_τ`. -/
abbrev CoefR (α : ℝ) (Φs : Fn) (E : Fn →ₗ[ℝ] Fn) (g : Fam) (τ : ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => Work.Construction.Rop (pExp α) (PhiT α Φs E g τ) z θ

/-- The `V`-coefficient `Vop Φ̃_τ`. -/
abbrev CoefV (α : ℝ) (Φs : Fn) (E : Fn →ₗ[ℝ] Fn) (g : Fam) (τ : ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => Work.Construction.Vop (PhiT α Φs E g τ) z θ

/-- The `U`-coefficient `Uop (pExp α) Φ̃_τ / sin 2θ`. -/
abbrev CoefU (α : ℝ) (Φs : Fn) (E : Fn →ₗ[ℝ] Fn) (g : Fam) (τ : ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => Work.Construction.Uop (pExp α) (PhiT α Φs E g τ) z θ / Real.sin (2 * θ)

/-- The full profile `F_τ = Ftau (pExp α) (gS α (tauExt g)) τ`. -/
abbrev Fp (α : ℝ) (g : Fam) (τ : ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => Work.Construction.Ftau (pExp α)
    (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g)) τ z θ

/-- `D_θ F_τ = sin 2θ · ∂_θF_τ`. -/
abbrev FpDth (α : ℝ) (g : Fam) (τ : ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => Work.Spaces.Dth (Fp α g τ) z θ

/-- `D_z F_τ = z ∂_zF_τ`. -/
abbrev FpDz (α : ℝ) (g : Fam) (τ : ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => Work.Spaces.Dz (Fp α g τ) z θ

/-! ## §3 The three products, in the exact shape consumed by the assembly -/

/-- The first product slot `P₁ = Rop Φ̃_τ · F_τ`. -/
abbrev P1 (α : ℝ) (Φs : Fn) (E : Fn →ₗ[ℝ] Fn) (g : Fam) : ℝ → ℝ → ℝ → ℝ :=
  fun z θ τ => CoefR α Φs E g τ z θ * Fp α g τ z θ

/-- The second product slot `P₂ = (Uop Φ̃_τ / sin 2θ)·D_θF_τ`. -/
abbrev P2 (α : ℝ) (Φs : Fn) (E : Fn →ₗ[ℝ] Fn) (g : Fam) : ℝ → ℝ → ℝ → ℝ :=
  fun z θ τ => CoefU α Φs E g τ z θ * FpDth α g τ z θ

/-- The third product slot `P₃ = Vop Φ̃_τ · D_zF_τ`. -/
abbrev P3 (α : ℝ) (Φs : Fn) (E : Fn →ₗ[ℝ] Fn) (g : Fam) : ℝ → ℝ → ℝ → ℝ :=
  fun z θ τ => CoefV α Φs E g τ z θ * FpDz α g τ z θ

/-! ## §4 The endpoint values of the residual and of the coefficients

`Φ̃_τ(z,·,τ)` vanishes identically at the two angular endpoints **as a function of `z`** (the
`psiR`-junk value at the endpoints is `0`, and the `Theta`-part carries `sin 2θ = 0`), hence so
does `pz Φ̃_τ` there; consequently `Uop Φ̃_τ (z,0,τ) = Uop Φ̃_τ (z,π/2,τ) = 0`.  This is what
makes the two forms of the second product slot agree on the whole closed box. -/

theorem Theta_apply_zero (α : ℝ) (F : ℝ → ℝ → ℝ) (z : ℝ) :
    Work.Construction.Theta α F z 0 = 0 := by
  simp only [Work.Construction.Theta, Work.Construction.s2]
  norm_num

theorem Theta_apply_pi_div_two (α : ℝ) (F : ℝ → ℝ → ℝ) (z : ℝ) :
    Work.Construction.Theta α F z (π / 2) = 0 := by
  simp only [Work.Construction.Theta, Work.Construction.s2]
  rw [show 2 * (π / 2) = π from by ring, Real.sin_pi]
  ring

theorem psiR_apply_zero (α : ℝ) (Φs : Fn) (E : Fn →ₗ[ℝ] Fn) (g : Fam) (z τ : ℝ) :
    Work.FTS.RegExportIface.psiR α Φs E (Work.FTS.FinalV2.tauExt g) z 0 τ = 0 := by
  by_cases hz : 0 < z
  · rw [Work.FTS.RegExportIface.psiR, if_pos hz, Work.FTS.RegExportIface.psiQ,
      if_neg (by rintro ⟨h1, h2⟩; linarith [Real.pi_pos] : ¬ (0 < (0 : ℝ) ∧ (0 : ℝ) < π / 2)),
      if_neg (by rintro ⟨h1, h2⟩; linarith [Real.pi_pos] : ¬ (π / 2 < (0 : ℝ) ∧ (0 : ℝ) < π)),
      if_neg (by rintro ⟨h1, h2⟩; linarith [Real.pi_pos] : ¬ (-(π / 2) < (0 : ℝ) ∧ (0 : ℝ) < 0))]
  · rw [Work.FTS.RegExportIface.psiR, if_neg hz]
    exact Theta_apply_zero _ _ _

theorem psiR_apply_pi_div_two (α : ℝ) (Φs : Fn) (E : Fn →ₗ[ℝ] Fn) (g : Fam) (z τ : ℝ) :
    Work.FTS.RegExportIface.psiR α Φs E (Work.FTS.FinalV2.tauExt g) z (π / 2) τ = 0 := by
  by_cases hz : 0 < z
  · rw [Work.FTS.RegExportIface.psiR, if_pos hz, Work.FTS.RegExportIface.psiQ,
      if_neg (by rintro ⟨h1, h2⟩; linarith [Real.pi_pos] : ¬ (0 < π / 2 ∧ π / 2 < π / 2)),
      if_neg (by rintro ⟨h1, h2⟩; linarith [Real.pi_pos] : ¬ (π / 2 < π / 2 ∧ π / 2 < π)),
      if_neg (by rintro ⟨h1, h2⟩; linarith [Real.pi_pos] : ¬ (-(π / 2) < π / 2 ∧ π / 2 < 0))]
  · rw [Work.FTS.RegExportIface.psiR, if_neg hz]
    exact Theta_apply_pi_div_two _ _ _

theorem PhiT_apply_zero (α : ℝ) (Φs : Fn) (E : Fn →ₗ[ℝ] Fn) (g : Fam) (τ z : ℝ) :
    PhiT α Φs E g τ z 0 = 0 := by
  show Work.Construction.PhiTil (pExp α)
      (Work.Construction.Ftau (pExp α) (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g)) τ)
      (Work.FTS.Regularity.gSlice (Work.FTS_RegExport.RXR5.SΨ α Φs E g) τ) z 0 = 0
  simp only [Work.Construction.PhiTil]
  rw [show Work.FTS.Regularity.gSlice (Work.FTS_RegExport.RXR5.SΨ α Φs E g) τ z 0 = 0 from
      psiR_apply_zero α Φs E g z τ,
    Theta_apply_zero]
  ring

theorem PhiT_apply_pi_div_two (α : ℝ) (Φs : Fn) (E : Fn →ₗ[ℝ] Fn) (g : Fam) (τ z : ℝ) :
    PhiT α Φs E g τ z (π / 2) = 0 := by
  show Work.Construction.PhiTil (pExp α)
      (Work.Construction.Ftau (pExp α) (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g)) τ)
      (Work.FTS.Regularity.gSlice (Work.FTS_RegExport.RXR5.SΨ α Φs E g) τ) z (π / 2) = 0
  simp only [Work.Construction.PhiTil]
  rw [show Work.FTS.Regularity.gSlice (Work.FTS_RegExport.RXR5.SΨ α Φs E g) τ z (π / 2) = 0 from
      psiR_apply_pi_div_two α Φs E g z τ,
    Theta_apply_pi_div_two]
  ring

theorem pz_PhiT_zero (α : ℝ) (Φs : Fn) (E : Fn →ₗ[ℝ] Fn) (g : Fam) (τ z : ℝ) :
    Work.Spaces.pz (PhiT α Φs E g τ) z 0 = 0 := by
  have h : (fun z' => PhiT α Φs E g τ z' 0) = fun _ => (0 : ℝ) :=
    funext fun z' => PhiT_apply_zero α Φs E g τ z'
  simp only [Work.Spaces.pz, h, deriv_const]

theorem pz_PhiT_pi_div_two (α : ℝ) (Φs : Fn) (E : Fn →ₗ[ℝ] Fn) (g : Fam) (τ z : ℝ) :
    Work.Spaces.pz (PhiT α Φs E g τ) z (π / 2) = 0 := by
  have h : (fun z' => PhiT α Φs E g τ z' (π / 2)) = fun _ => (0 : ℝ) :=
    funext fun z' => PhiT_apply_pi_div_two α Φs E g τ z'
  simp only [Work.Spaces.pz, h, deriv_const]

/-- `Uop Φ̃_τ` vanishes at both angular endpoints. -/
theorem Uop_PhiT_endpoint {α : ℝ} {Φs : Fn} {E : Fn →ₗ[ℝ] Fn} {g : Fam} {τ z θ : ℝ}
    (hθ : θ = 0 ∨ θ = π / 2) :
    Work.Construction.Uop (pExp α) (PhiT α Φs E g τ) z θ = 0 := by
  rcases hθ with rfl | rfl
  · simp [Work.Construction.Uop, PhiT_apply_zero, pz_PhiT_zero]
  · simp [Work.Construction.Uop, PhiT_apply_pi_div_two, pz_PhiT_pi_div_two]

end Work.FTS_RegExport.RXR5L
