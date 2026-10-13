import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.RegExportIface.RXT.Leaves
import Submission.Work.FTS_RegExport.RXT.velVanish2Aux
import Submission.Work.FTS_RegExport.RXT.Sys.GdotCore
import Submission.Work.FTS_RegExport.RXT.Sys.CoeffCore

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXT.Sys.CoeffBounds` — the order-`≤ 2` jet bounds of the coefficients

For a fixed fake time `τ` the three transport coefficients are written as explicit sums of a
constant, a radial `L₁₂`/`FK`-piece and a slot `Vop Φ̃`, `Uop Φ̃/sin 2θ`, `Rop Φ̃` of the residual
(plus the explicit `Θ`-parts).  Each of the four bounds (the three coefficient families and
`∂_θVz7`) is reduced here to the corresponding bound of the *slots* (`Sys.velVanish2`), of the
explicit pieces (`Sys.explicit_pieces_coeff`), of the `|μ| ≤ 1/2` clock bound and of the
`C²`-regularity of the pieces (`Sys.CoeffSmooth`), which are supplied as hypotheses.
-/

noncomputable section
open scoped Real Topology
open Set Filter

namespace Work.FTS_RegExport.RXT.Sys

open Work.FTS.Galerkin (Fn Fam slice)
open Work.FTS.RegExportIface (Vz7 Vθ7 cs7)
open Work.FTS.RegExportIface.RXT (GR ΦR μR)
open Work.FTS_RegExport.RXT (v2_PhiT v2_SlotR v2_SlotV v2_SlotU)
open Work.FTS.Regularity (pExp)
open Work.Construction (L12 FK Ftau Theta Uop Vop Rop c2m Fstar)

set_option autoImplicit false

variable {α Ce Cs : ℝ} {Φs : Fn} {E : Fn →ₗ[ℝ] Fn}

/-- The clock bound gives `|1 ∓ μ| ≤ 3/2`. -/
theorem one_sub_abs_le {μ : ℝ} (h : |μ| ≤ 1 / 2) : |1 - μ| ≤ 3 / 2 := by
  have := abs_le.mp h
  rw [abs_le]
  constructor <;> linarith

/-- The clock bound gives `|1 + μ| ≤ 3/2`. -/
theorem one_add_abs_le {μ : ℝ} (h : |μ| ≤ 1 / 2) : |1 + μ| ≤ 3 / 2 := by
  have := abs_le.mp h
  rw [abs_le]
  constructor <;> linarith

/-- **`Vz7`'s order-`≤ 2` jets.** -/
theorem Vz7_jets_le {g : Fam} {τ Mslot Cexp : ℝ}
    (hαG : 0 < pExp α)
    (hsmA : ContDiffOn ℝ 2 (Function.uncurry (fun z θ => (1 - μR α Φs E g τ)
        + L12 (Ftau (pExp α) (GR α g) τ) z * c2m θ)) Q0)
    (hsmB : ContDiffOn ℝ 2 (Function.uncurry (fun z θ => 2 * pExp α
        * Vop (v2_PhiT α Φs E g τ) z θ)) Q0)
    (hsmP1 : ContDiffOn ℝ 2 (Function.uncurry (fun z θ =>
        L12 (Ftau (pExp α) (GR α g) τ) z * c2m θ)) Q0)
    (hμbd : |μR α Φs E g τ| ≤ 1 / 2)
    (hslotV : ∀ j i : ℕ, j + i ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.mixed j i (v2_SlotV α (v2_PhiT α Φs E g τ)) z θ| ≤ Mslot)
    (hexp1 : ∀ j i : ℕ, j + i ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.mixed j i (fun z θ =>
        L12 (Ftau (pExp α) (GR α g) τ) z * c2m θ) z θ| ≤ Cexp) :
    ∀ j i : ℕ, j + i ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.mixed j i (fun z θ => Vz7 (pExp α) (μR α Φs E g) (GR α g)
        (ΦR α Φs E g) z θ τ) z θ| ≤ 3 / 2 + Cexp + 2 * pExp α * Mslot := by
  intro j i hji z θ hz hθ hθ2
  have hzθ : (z, θ) ∈ Q0 := ⟨hz, hθ, hθ2⟩
  have hEq : EqOn (Function.uncurry (fun z θ => Vz7 (pExp α) (μR α Φs E g) (GR α g)
      (ΦR α Φs E g) z θ τ))
      (Function.uncurry (fun z θ => ((1 - μR α Φs E g τ)
        + L12 (Ftau (pExp α) (GR α g) τ) z * c2m θ)
        + 2 * pExp α * Vop (v2_PhiT α Φs E g τ) z θ)) Q0 := by
    intro p hp
    simp only [Function.uncurry, Vz7, v2_PhiT, Work.FTS.RegExportIface.phiTil,
      Work.Construction.PhiTil]
  rw [mixed_congr_of_isOpen (V := Q0) Work.FTS.EllipticEst.isOpen_Q0 hEq j i z θ hzθ,
    mixed_add_lam hsmA hsmB hji hzθ]
  have h1 : |Work.Spaces.mixed j i (fun z θ => (1 - μR α Φs E g τ)
        + L12 (Ftau (pExp α) (GR α g) τ) z * c2m θ) z θ|
      ≤ |1 - μR α Φs E g τ| + Cexp := by
    rw [mixed_add_lam (contDiffOn_const) hsmP1 hji hzθ]
    exact le_trans (abs_add_le _ _)
      (add_le_add (abs_mixed_const_le _ j i z θ) (hexp1 j i hji z θ hz hθ hθ2))
  have h2 : |Work.Spaces.mixed j i (fun z θ => 2 * pExp α
        * Vop (v2_PhiT α Φs E g τ) z θ) z θ| ≤ 2 * pExp α * Mslot := by
    rw [coeff_mixed_const_mul]
    rw [abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 2 * pExp α)]
    exact mul_le_mul_of_nonneg_left (hslotV j i hji z θ hz hθ hθ2) (by linarith)
  have hsum := abs_add_le (Work.Spaces.mixed j i (fun z θ => (1 - μR α Φs E g τ)
      + L12 (Ftau (pExp α) (GR α g) τ) z * c2m θ) z θ)
    (Work.Spaces.mixed j i (fun z θ => 2 * pExp α
      * Vop (v2_PhiT α Φs E g τ) z θ) z θ)
  have hm := one_sub_abs_le hμbd
  linarith

/-- **`Vθ7/sin 2θ`'s order-`≤ 2` jets.** -/
theorem Vth_jets_le {g : Fam} {τ Mslot Cexp : ℝ}
    (hαG : 0 < pExp α)
    (hsmU1 : ContDiffOn ℝ 2 (Function.uncurry (fun z θ => 2 * Uop (pExp α)
        (v2_PhiT α Φs E g τ) z θ / Real.sin (2 * θ))) Q0)
    (hsmU2 : ContDiffOn ℝ 2 (Function.uncurry (fun z θ => 2 * Uop (pExp α)
        (Theta (pExp α) (Ftau (pExp α) (GR α g) τ)) z θ / Real.sin (2 * θ))) Q0)
    (hsmPsi : ContDiffOn ℝ 3 (Function.uncurry (v2_PhiT α Φs E g τ)) Q0)
    (hsmTheta : ContDiffOn ℝ 3 (Function.uncurry (Theta (pExp α) (Ftau (pExp α) (GR α g) τ))) Q0)
    (hslotU : ∀ j i : ℕ, j + i ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.mixed j i (v2_SlotU α (v2_PhiT α Φs E g τ)) z θ| ≤ Mslot)
    (hexp4 : ∀ j i : ℕ, j + i ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.mixed j i (fun z θ => Uop (pExp α)
        (Theta (pExp α) (Ftau (pExp α) (GR α g) τ)) z θ / Real.sin (2 * θ)) z θ| ≤ Cexp) :
    ∀ j i : ℕ, j + i ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.mixed j i (fun z θ => Vθ7 (pExp α) (ΦR α Φs E g) z θ τ
        / Real.sin (2 * θ)) z θ| ≤ 2 * Mslot + 2 * Cexp := by
  intro j i hji z θ hz hθ hθ2
  have hzθ : (z, θ) ∈ Q0 := ⟨hz, hθ, hθ2⟩
  have hEq : EqOn (Function.uncurry (fun z θ => Vθ7 (pExp α) (ΦR α Φs E g) z θ τ
      / Real.sin (2 * θ)))
      (Function.uncurry (fun z θ => 2 * Uop (pExp α)
          (v2_PhiT α Φs E g τ) z θ / Real.sin (2 * θ)
        + 2 * Uop (pExp α) (Theta (pExp α) (Ftau (pExp α) (GR α g) τ)) z θ
            / Real.sin (2 * θ))) Q0 := by
    intro p hp
    obtain ⟨z', θ'⟩ := p
    obtain ⟨hz', hθ', hθ2'⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    simp only [Function.uncurry, Vθ7, Work.FTS.Galerkin.slice]
    rw [uop_split_theta (Φs := Φs) (E := E) (g := g) ⟨hz', hθ', hθ2'⟩ hsmPsi hsmTheta]
    ring
  rw [mixed_congr_of_isOpen (V := Q0) Work.FTS.EllipticEst.isOpen_Q0 hEq j i z θ hzθ,
    mixed_add_lam hsmU1 hsmU2 hji hzθ]
  have h1 : |Work.Spaces.mixed j i (fun z θ => 2 * Uop (pExp α)
        (v2_PhiT α Φs E g τ) z θ / Real.sin (2 * θ)) z θ| ≤ 2 * Mslot := by
    have hcongr : EqOn (Function.uncurry (fun z θ => 2 * Uop (pExp α)
        (v2_PhiT α Φs E g τ) z θ / Real.sin (2 * θ)))
        (Function.uncurry (fun z θ => 2 * (Uop (pExp α)
          (v2_PhiT α Φs E g τ) z θ / Real.sin (2 * θ)))) Q0 := by
      intro p hp
      simp only [Function.uncurry]
      ring
    rw [mixed_congr_of_isOpen (V := Q0) Work.FTS.EllipticEst.isOpen_Q0 hcongr j i z θ hzθ,
      coeff_mixed_const_mul]
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    have hU : |Work.Spaces.mixed j i (fun z θ => Uop (pExp α)
        (v2_PhiT α Φs E g τ) z θ / Real.sin (2 * θ)) z θ| ≤ Mslot := by
      change |Work.Spaces.mixed j i (v2_SlotU α
        (v2_PhiT α Φs E g τ)) z θ| ≤ Mslot
      exact hslotU j i hji z θ hz hθ hθ2
    exact mul_le_mul_of_nonneg_left hU (by norm_num)
  have h2 : |Work.Spaces.mixed j i (fun z θ => 2 * Uop (pExp α)
        (Theta (pExp α) (Ftau (pExp α) (GR α g) τ)) z θ / Real.sin (2 * θ)) z θ|
      ≤ 2 * Cexp := by
    have hcongr : EqOn (Function.uncurry (fun z θ => 2 * Uop (pExp α)
        (Theta (pExp α) (Ftau (pExp α) (GR α g) τ)) z θ / Real.sin (2 * θ)))
        (Function.uncurry (fun z θ => 2 * (Uop (pExp α)
          (Theta (pExp α) (Ftau (pExp α) (GR α g) τ)) z θ / Real.sin (2 * θ)))) Q0 := by
      intro p hp
      simp only [Function.uncurry]
      ring
    rw [mixed_congr_of_isOpen (V := Q0) Work.FTS.EllipticEst.isOpen_Q0 hcongr j i z θ hzθ,
      coeff_mixed_const_mul]
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    exact mul_le_mul_of_nonneg_left (hexp4 j i hji z θ hz hθ hθ2) (by norm_num)
  have hsum := abs_add_le (Work.Spaces.mixed j i (fun z θ => 2 * Uop (pExp α)
      (v2_PhiT α Φs E g τ) z θ / Real.sin (2 * θ)) z θ)
    (Work.Spaces.mixed j i (fun z θ => 2 * Uop (pExp α)
      (Theta (pExp α) (Ftau (pExp α) (GR α g) τ)) z θ / Real.sin (2 * θ)) z θ)
  linarith

/-- **`cs7`'s order-`≤ 2` jets.** -/
theorem Cs_jets_le {g : Fam} {τ Mslot Cexp : ℝ}
    (hαG : 0 < pExp α)
    (hsmA' : ContDiffOn ℝ 2 (Function.uncurry (fun z θ => (1 + μR α Φs E g τ)
        - L12 (Ftau (pExp α) (GR α g) τ) z / pExp α)) Q0)
    (hsmB' : ContDiffOn ℝ 2 (Function.uncurry (fun z θ => (Real.sin θ) ^ 2
        * FK (Ftau (pExp α) (GR α g) τ) z)) Q0)
    (hsmA'B' : ContDiffOn ℝ 2 (Function.uncurry (fun z θ => ((1 + μR α Φs E g τ)
        - L12 (Ftau (pExp α) (GR α g) τ) z / pExp α)
        + (Real.sin θ) ^ 2 * FK (Ftau (pExp α) (GR α g) τ) z)) Q0)
    (hsmC' : ContDiffOn ℝ 2 (Function.uncurry (fun z θ => 2 * Rop (pExp α)
        (v2_PhiT α Φs E g τ) z θ)) Q0)
    (hsmLdiv : ContDiffOn ℝ 2 (Function.uncurry (fun z θ =>
        L12 (Ftau (pExp α) (GR α g) τ) z / pExp α)) Q0)
    (hμbd : |μR α Φs E g τ| ≤ 1 / 2)
    (hslotR : ∀ j i : ℕ, j + i ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.mixed j i (v2_SlotR α (v2_PhiT α Φs E g τ)) z θ| ≤ Mslot)
    (hexp2 : ∀ j i : ℕ, j + i ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.mixed j i (fun z θ =>
        L12 (Ftau (pExp α) (GR α g) τ) z) z θ| ≤ Cexp)
    (hexp3 : ∀ j i : ℕ, j + i ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.mixed j i (fun z θ => (Real.sin θ) ^ 2 * FK
        (Ftau (pExp α) (GR α g) τ) z) z θ| ≤ Cexp) :
    ∀ j i : ℕ, j + i ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.mixed j i (fun z θ => cs7 (pExp α) (μR α Φs E g) (GR α g)
        (ΦR α Φs E g) z θ τ) z θ| ≤ 3 / 2 + Cexp / pExp α + Cexp + 2 * Mslot := by
  intro j i hji z θ hz hθ hθ2
  have hzθ : (z, θ) ∈ Q0 := ⟨hz, hθ, hθ2⟩
  -- the field as a sum of the three pieces
  have hEq : EqOn (Function.uncurry (fun z θ => cs7 (pExp α) (μR α Φs E g) (GR α g)
      (ΦR α Φs E g) z θ τ))
      (Function.uncurry (fun z θ => (((1 + μR α Φs E g τ)
          - L12 (Ftau (pExp α) (GR α g) τ) z / pExp α)
        + (Real.sin θ) ^ 2 * FK (Ftau (pExp α) (GR α g) τ) z)
        + (-1) * (2 * Rop (pExp α) (v2_PhiT α Φs E g τ) z θ))) Q0 := by
    intro p hp
    simp only [Function.uncurry, cs7, v2_PhiT, Work.FTS.RegExportIface.phiTil,
      Work.Construction.PhiTil]
    ring
  rw [mixed_congr_of_isOpen (V := Q0) Work.FTS.EllipticEst.isOpen_Q0 hEq j i z θ hzθ,
    mixed_add_lam hsmA'B' (contDiffOn_const.mul hsmC') hji hzθ]
  -- the `Rop`-piece
  have h3 : |Work.Spaces.mixed j i (fun z θ => (-1) * (2 * Rop (pExp α)
        (v2_PhiT α Φs E g τ) z θ)) z θ| ≤ 2 * Mslot := by
    have hR0 : |Work.Spaces.mixed j i (Rop (pExp α) (v2_PhiT α Φs E g τ)) z θ| ≤ Mslot := by
      change |Work.Spaces.mixed j i (v2_SlotR α
        (v2_PhiT α Φs E g τ)) z θ| ≤ Mslot
      exact hslotR j i hji z θ hz hθ hθ2
    have hR : |Work.Spaces.mixed j i (fun z θ => 2 * Rop (pExp α)
        (v2_PhiT α Φs E g τ) z θ) z θ| ≤ 2 * Mslot :=
      abs_mixed_const_mul_le (c := (2 : ℝ)) (by norm_num)
        (f := Rop (pExp α) (v2_PhiT α Φs E g τ)) hR0
    have h2 := abs_mixed_const_mul_le' (c := (-1 : ℝ))
      (f := fun z θ => 2 * Rop (pExp α) (v2_PhiT α Φs E g τ) z θ) hR
    simpa using h2
  -- the explicit pieces
  have h1 : |Work.Spaces.mixed j i (fun z θ => ((1 + μR α Φs E g τ)
        - L12 (Ftau (pExp α) (GR α g) τ) z / pExp α)
        + (Real.sin θ) ^ 2 * FK (Ftau (pExp α) (GR α g) τ) z) z θ|
      ≤ 3 / 2 + Cexp / pExp α + Cexp := by
    rw [mixed_add_lam hsmA' hsmB' hji hzθ]
    have hA' : |Work.Spaces.mixed j i (fun z θ => (1 + μR α Φs E g τ)
          - L12 (Ftau (pExp α) (GR α g) τ) z / pExp α) z θ|
        ≤ 3 / 2 + Cexp / pExp α := by
      have hcongr : EqOn (Function.uncurry (fun z θ => (1 + μR α Φs E g τ)
          - L12 (Ftau (pExp α) (GR α g) τ) z / pExp α))
          (Function.uncurry (fun z θ => (1 + μR α Φs E g τ)
            + (-1) * (L12 (Ftau (pExp α) (GR α g) τ) z / pExp α))) Q0 := by
        intro p hp
        simp only [Function.uncurry]
        ring
      rw [mixed_congr_of_isOpen (V := Q0) Work.FTS.EllipticEst.isOpen_Q0 hcongr j i z θ hzθ,
        mixed_add_lam contDiffOn_const (contDiffOn_const.mul hsmLdiv) hji hzθ]
      have hLdiv' : |Work.Spaces.mixed j i (fun z θ => L12 (Ftau (pExp α) (GR α g) τ) z
            / pExp α) z θ| ≤ Cexp / pExp α := by
        have hcongr2 : EqOn (Function.uncurry (fun z θ => L12 (Ftau (pExp α) (GR α g) τ) z
            / pExp α))
            (Function.uncurry (fun z θ => (pExp α)⁻¹
              * L12 (Ftau (pExp α) (GR α g) τ) z)) Q0 := by
          intro p hp
          simp only [Function.uncurry]
          ring
        rw [mixed_congr_of_isOpen (V := Q0) Work.FTS.EllipticEst.isOpen_Q0 hcongr2 j i z θ hzθ,
          coeff_mixed_const_mul]
        rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr hαG.le)]
        calc (pExp α)⁻¹ * |Work.Spaces.mixed j i (fun z θ =>
              L12 (Ftau (pExp α) (GR α g) τ) z) z θ|
            ≤ (pExp α)⁻¹ * Cexp :=
              mul_le_mul_of_nonneg_left (hexp2 j i hji z θ hz hθ hθ2)
                (inv_nonneg.mpr hαG.le)
          _ = Cexp / pExp α := by rw [inv_mul_eq_div]
      have hneg : |Work.Spaces.mixed j i (fun z θ => (-1)
            * (L12 (Ftau (pExp α) (GR α g) τ) z / pExp α)) z θ| ≤ Cexp / pExp α := by
        have h := abs_mixed_const_mul_le' (c := (-1 : ℝ))
          (f := fun z θ => L12 (Ftau (pExp α) (GR α g) τ) z / pExp α) hLdiv'
        simpa using h
      have hsum2 := abs_add_le (Work.Spaces.mixed j i (fun _ _ : ℝ =>
          (1 + μR α Φs E g τ)) z θ)
        (Work.Spaces.mixed j i (fun z θ => (-1)
          * (L12 (Ftau (pExp α) (GR α g) τ) z / pExp α)) z θ)
      have hm := one_add_abs_le hμbd
      have hc := abs_mixed_const_le (1 + μR α Φs E g τ) j i z θ
      linarith
    have hsum2 := abs_add_le (Work.Spaces.mixed j i (fun z θ => (1 + μR α Φs E g τ)
        - L12 (Ftau (pExp α) (GR α g) τ) z / pExp α) z θ)
      (Work.Spaces.mixed j i (fun z θ => (Real.sin θ) ^ 2 * FK
        (Ftau (pExp α) (GR α g) τ) z) z θ)
    have hb := hexp3 j i hji z θ hz hθ hθ2
    linarith
  have hsum := abs_add_le (Work.Spaces.mixed j i (fun z θ => ((1 + μR α Φs E g τ)
      - L12 (Ftau (pExp α) (GR α g) τ) z / pExp α)
      + (Real.sin θ) ^ 2 * FK (Ftau (pExp α) (GR α g) τ) z) z θ)
    (Work.Spaces.mixed j i (fun z θ => (-1) * (2 * Rop (pExp α)
      (v2_PhiT α Φs E g τ) z θ)) z θ)
  linarith

/-- **`∂_θVz7`'s bound.** -/
theorem Vz7_pth_le {g : Fam} {τ CF Mpth : ℝ}
    (hαG : 0 < pExp α)
    (hsmA : ContDiffOn ℝ 2 (Function.uncurry (fun z θ => (1 - μR α Φs E g τ)
        + L12 (Ftau (pExp α) (GR α g) τ) z * c2m θ)) Q0)
    (hsmB : ContDiffOn ℝ 2 (Function.uncurry (fun z θ => 2 * pExp α
        * Vop (v2_PhiT α Φs E g τ) z θ)) Q0)
    (hMpth : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.pth (fun z θ => Vop (v2_PhiT α Φs E g τ) z θ) z θ| ≤ Mpth)
    (hCF0 : 0 ≤ CF)
    (hL12bd : ∀ z : ℝ, 0 < z → |L12 (Ftau (pExp α) (GR α g) τ) z| ≤ CF) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.pth (fun z θ => Vz7 (pExp α) (μR α Φs E g) (GR α g)
        (ΦR α Φs E g) z θ τ) z θ| ≤ CF * 4 + 2 * pExp α * Mpth := by
  intro z θ hz hθ hθ2
  have hzθ : (z, θ) ∈ Q0 := ⟨hz, hθ, hθ2⟩
  have hMpth : |Work.Spaces.pth (fun z θ => Vop (v2_PhiT α Φs E g τ) z θ) z θ| ≤ Mpth :=
    hMpth z θ hz hθ hθ2
  have hL12bd' : |L12 (Ftau (pExp α) (GR α g) τ) z| ≤ CF := hL12bd z hz
  have hEq : EqOn (Function.uncurry (fun z θ => Vz7 (pExp α) (μR α Φs E g) (GR α g)
      (ΦR α Φs E g) z θ τ))
      (Function.uncurry (fun z θ => ((1 - μR α Φs E g τ)
        + L12 (Ftau (pExp α) (GR α g) τ) z * c2m θ)
        + 2 * pExp α * Vop (v2_PhiT α Φs E g τ) z θ)) Q0 := by
    intro p hp
    simp only [Function.uncurry, Vz7, v2_PhiT, Work.FTS.RegExportIface.phiTil,
      Work.Construction.PhiTil]
  have hDthSplit : Work.Spaces.Dth (fun z θ => Vz7 (pExp α) (μR α Φs E g) (GR α g)
      (ΦR α Φs E g) z θ τ) z θ
      = Work.Spaces.Dth (fun z θ => (1 - μR α Φs E g τ)
          + L12 (Ftau (pExp α) (GR α g) τ) z * c2m θ) z θ
        + Work.Spaces.Dth (fun z θ => 2 * pExp α
          * Vop (v2_PhiT α Φs E g τ) z θ) z θ := by
    rw [Dth_congr_of_isOpen (V := Q0) Work.FTS.EllipticEst.isOpen_Q0 hEq hzθ]
    exact Dth_split_of_eqOn hsmA hsmB hEq z θ hzθ
  have hsin : Real.sin (2 * θ) ≠ 0 := ne_of_gt (Work.FTS_RegExport.RXT.sin_two_pos_Q0 hzθ)
  have hD1 : Work.Spaces.Dth (fun z θ => (1 - μR α Φs E g τ)
      + L12 (Ftau (pExp α) (GR α g) τ) z * c2m θ) z θ
      = Real.sin (2 * θ) * (L12 (Ftau (pExp α) (GR α g) τ) z * deriv c2m θ) := by
    have hd1 : DifferentiableAt ℝ (fun _ : ℝ => (1 - μR α Φs E g τ)) θ :=
      differentiableAt_const _
    have hd2 : DifferentiableAt ℝ (fun θ' => L12 (Ftau (pExp α) (GR α g) τ) z
        * c2m θ') θ := by
      have hc := Work.FTS_RegExport.RXT.contDiffOn_c2m.differentiableOn (by norm_num) θ
        ⟨hθ, hθ2⟩
      exact (differentiableAt_const _).mul (hc.differentiableAt (isOpen_Ioo.mem_nhds ⟨hθ, hθ2⟩))
    simp only [Work.Spaces.Dth, Work.Spaces.pth]
    rw [show (fun θ' : ℝ => (1 - μR α Φs E g τ) + L12 (Ftau (pExp α) (GR α g) τ) z
          * c2m θ') = ((fun _ : ℝ => (1 - μR α Φs E g τ))
          + (fun θ' => L12 (Ftau (pExp α) (GR α g) τ) z * c2m θ')) from rfl,
      deriv_add hd1 hd2, deriv_const, Work.Construction.deriv_const_mul_fun]
    ring
  have hD2 : Work.Spaces.Dth (fun z θ => 2 * pExp α
      * Vop (v2_PhiT α Φs E g τ) z θ) z θ
      = 2 * pExp α * Work.Spaces.Dth (Vop (v2_PhiT α Φs E g τ)) z θ := by
    rw [Work.FTS.StrongEps.Dth_const_mul (2 * pExp α) (Vop (v2_PhiT α Φs E g τ))]
  have hpthEq : Work.Spaces.pth (fun z θ => Vz7 (pExp α) (μR α Φs E g) (GR α g)
      (ΦR α Φs E g) z θ τ) z θ
      = L12 (Ftau (pExp α) (GR α g) τ) z * deriv c2m θ
        + 2 * pExp α * Work.Spaces.pth (Vop (v2_PhiT α Φs E g τ)) z θ := by
    have hDth : Work.Spaces.Dth (fun z θ => Vz7 (pExp α) (μR α Φs E g) (GR α g)
        (ΦR α Φs E g) z θ τ) z θ
        = Real.sin (2 * θ) * ((L12 (Ftau (pExp α) (GR α g) τ) z * deriv c2m θ)
          + 2 * pExp α * Work.Spaces.pth (Vop (v2_PhiT α Φs E g τ)) z θ) := by
      rw [hDthSplit, hD1, hD2, Work.Spaces.Dth]
      ring
    have hDthDef : Work.Spaces.Dth (fun z θ => Vz7 (pExp α) (μR α Φs E g) (GR α g)
        (ΦR α Φs E g) z θ τ) z θ
        = Real.sin (2 * θ) * Work.Spaces.pth (fun z θ => Vz7 (pExp α) (μR α Φs E g)
          (GR α g) (ΦR α Φs E g) z θ τ) z θ := rfl
    rw [hDthDef] at hDth
    exact mul_left_cancel₀ hsin hDth
  rw [hpthEq]
  have hmul : |L12 (Ftau (pExp α) (GR α g) τ) z * deriv c2m θ| ≤ CF * 4 := by
    rw [abs_mul]
    exact mul_le_mul hL12bd' (abs_deriv_c2m_le θ) (abs_nonneg _) hCF0
  have hmul2 : |2 * pExp α * Work.Spaces.pth (Vop (v2_PhiT α Φs E g τ)) z θ|
      ≤ 2 * pExp α * Mpth := by
    rw [abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 2 * pExp α)]
    exact mul_le_mul_of_nonneg_left hMpth (by linarith)
  have hsum := abs_add_le (L12 (Ftau (pExp α) (GR α g) τ) z * deriv c2m θ)
    (2 * pExp α * Work.Spaces.pth (Vop (v2_PhiT α Φs E g τ)) z θ)
  linarith

end Work.FTS_RegExport.RXT.Sys
