/-
Copyright: work module for the Elgindi finite-time singularity project.

# `PTblocks` — the three pointwise block bounds feeding `N0_N_Transport_pt_le`

For a projected slice `W = slice (JfamP ρ ε g) τ` whose slots are dominated by `1`
(`pt_EpsDecay_slots`), whose `L₁₂`-mode is bounded by `CL · C₀ α²` and whose angular moment by
`C7 · B`, the three blocks of the right-hand side of the `ε`-scheme are bounded pointwise by

* `|N₀ α (F_*+W) W| ≤ 1000 (CL+1) (1+C₀) (1+B) / sin 2θ` (`pt_N0_le`),
* `|N α (F_*+W) Φg| ≤ (30000 + 200 C7) (1+C₀) (1+B) / sin 2θ` (`pt_N_le`),
* `|Transport W| ≤ 3 (1+C₀) (1+B) / sin 2θ` (`pt_Transport_le`).

Every term is estimated with the explicit profile data `pt_Fstar_pt_data`, the slot data
`pt_F_slots` and the residual-slot data `pt_Xi_slots`; the factors `1/sin 2θ` are supplied once
at the end of each block by `sin 2θ ≤ 1`.

Axioms: `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.FM.Defs
import Submission.Work.Construction.Defs
import Submission.Work.Coercivity.Defs
import Submission.Work.FTS.StrongEps.E5Aux2.PTgadgets

set_option synthInstance.maxHeartbeats 400000 -- v435-synth

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E5Aux2

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-- **The `N₀`-block.** -/
theorem pt_N0_le {α C₀ B CL : ℝ} (hαι : α ∈ Set.Ioc 0 1) (hC₀ : 0 ≤ C₀) (hB : 0 ≤ B)
    (hCL : 0 < CL) {W F : ℝ → ℝ → ℝ}
    (hWS : Work.FTS.EllipticEst.SmoothOpen W)
    (hFeq : F = fun z θ => Work.Construction.Fstar α z θ + W z θ)
    (hWval : ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ : ℝ, |W z θ| ≤ 1)
    (hWDz : ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ : ℝ, |Work.Spaces.Dz W z θ| ≤ 1)
    (hWDth : ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ : ℝ, |Work.Spaces.Dth W z θ| ≤ 1)
    (hL12W : ∀ z ∈ Set.Ioi (0 : ℝ),
      |Work.Construction.L12 W z| ≤ CL * (C₀ * α ^ 2)) :
    ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      |Work.Construction.N0 α F W z θ|
        ≤ (1000 * (CL + 1)) * (1 + C₀) * (1 + B) / Real.sin (2 * θ) := by
  have hα0 : 0 < α := hαι.1
  have hα1 : α ≤ 1 := hαι.2
  intro z hz θ hθ
  have hs2pos : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2])
  have hs2le1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  obtain ⟨hFval, hs2pthF, hDzF⟩ := pt_F_slots hα0 hα1 hWS hFeq hWval hWDz hWDth z hz θ hθ
  obtain ⟨-, hDzFstar, hDthFstar, hL12Fstar, -⟩ := pt_Fstar_pt_data hα0 hα1 hz hθ
  have hFstarsharp : |Work.Construction.L12 (Work.Construction.Fstar α) z| ≤ 2 * α :=
    hL12Fstar
  have hWv : |W z θ| ≤ 1 := hWval z hz θ
  have hWz : |Work.Spaces.Dz W z θ| ≤ 1 := hWDz z hz θ
  have hc2m : |Work.Construction.c2m θ| ≤ 2 := pt_abs_c2m_le_two θ
  have hL12Wz : |Work.Construction.L12 W z| ≤ CL * (C₀ * α ^ 2) := hL12W z hz
  have hL12Wnn : 0 ≤ CL * (C₀ * α ^ 2) :=
    mul_nonneg hCL.le (mul_nonneg hC₀ (sq_nonneg α))
  -- the six summands of `N₀`
  have hkey1 : |Work.Construction.s2 θ * Work.Spaces.pth (Work.Construction.Fstar α) z θ|
      ≤ 100 * α := by
    have h := hDthFstar
    rw [Work.Spaces.Dth, abs_mul] at h
    first
    | (rw [abs_mul]; exact h)
    | (simpa [Work.Construction.s2, abs_mul] using h)
    | (rw [abs_mul]; unfold Work.Construction.s2; exact h)
  have hCC : 0 ≤ CL * C₀ := mul_nonneg hCL.le hC₀
  have hα2 : α ^ 2 ≤ 1 := by nlinarith [hα0, hα1]
  have ht1 : |(3 / (2 * α)) * Work.Construction.s2 θ
      * Work.Construction.L12 (Work.Construction.Fstar α) z
      * Work.Spaces.pth (Work.Construction.Fstar α) z θ| ≤ 300 := by
    have hre : (3 / (2 * α)) * Work.Construction.s2 θ
        * Work.Construction.L12 (Work.Construction.Fstar α) z
        * Work.Spaces.pth (Work.Construction.Fstar α) z θ
        = (3 / (2 * α)) * Work.Construction.L12 (Work.Construction.Fstar α) z
          * (Work.Construction.s2 θ * Work.Spaces.pth (Work.Construction.Fstar α) z θ) := by
      ring
    rw [hre, abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 3 / (2 * α))]
    have h1 : 3 / (2 * α) * |Work.Construction.L12 (Work.Construction.Fstar α) z| ≤ 3 := by
      calc 3 / (2 * α) * |Work.Construction.L12 (Work.Construction.Fstar α) z|
          ≤ 3 / (2 * α) * (2 * α) :=
            mul_le_mul_of_nonneg_left hFstarsharp (by positivity)
        _ = 3 := by rw [div_mul_cancel₀ 3 (by positivity : (2 : ℝ) * α ≠ 0)]
    calc 3 / (2 * α) * |Work.Construction.L12 (Work.Construction.Fstar α) z|
          * |Work.Construction.s2 θ * Work.Spaces.pth (Work.Construction.Fstar α) z θ|
        ≤ 3 * (100 * α) := mul_le_mul h1 hkey1 (abs_nonneg _) (by norm_num)
      _ ≤ 300 := by nlinarith [hα0]
  have ht2 : |Work.Construction.c2m θ * Work.Construction.L12 (Work.Construction.Fstar α) z
      * Work.Spaces.Dz (Work.Construction.Fstar α) z θ| ≤ 400 := by
    rw [abs_mul, abs_mul]
    have h1 : |Work.Construction.c2m θ| * |Work.Construction.L12 (Work.Construction.Fstar α) z|
        ≤ 2 * (2 * α) := mul_le_mul hc2m hFstarsharp (abs_nonneg _) (by norm_num)
    calc |Work.Construction.c2m θ| * |Work.Construction.L12 (Work.Construction.Fstar α) z|
          * |Work.Spaces.Dz (Work.Construction.Fstar α) z θ|
        ≤ (2 * (2 * α)) * (100 * α) := mul_le_mul h1 hDzFstar (abs_nonneg _) (by positivity)
      _ ≤ 400 := by nlinarith [hα0, hα2]
  have ht3 : |(1 / α) * Work.Construction.L12 W z * W z θ| ≤ CL * C₀ := by
    rw [abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / α)]
    have h1 : 1 / α * |Work.Construction.L12 W z| ≤ CL * C₀ * α := by
      calc 1 / α * |Work.Construction.L12 W z| ≤ 1 / α * (CL * (C₀ * α ^ 2)) :=
            mul_le_mul_of_nonneg_left hL12Wz (by positivity)
        _ = CL * C₀ * α := by field_simp
    calc 1 / α * |Work.Construction.L12 W z| * |W z θ| ≤ (CL * C₀ * α) * 1 :=
          mul_le_mul h1 hWv (abs_nonneg _) (by positivity)
      _ ≤ CL * C₀ := by nlinarith [hCC, hα0, hα1]
  have ht4 : |(3 / (2 * α)) * Work.Construction.s2 θ * Work.Construction.L12 W z
      * Work.Spaces.pth F z θ| ≤ 152 * CL * C₀ := by
    have hre : (3 / (2 * α)) * Work.Construction.s2 θ * Work.Construction.L12 W z
        * Work.Spaces.pth F z θ
        = (3 / (2 * α)) * Work.Construction.L12 W z
          * (Work.Construction.s2 θ * Work.Spaces.pth F z θ) := by ring
    rw [hre, abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 3 / (2 * α))]
    have h1 : 3 / (2 * α) * |Work.Construction.L12 W z| ≤ 3 / 2 * CL * C₀ * α := by
      calc 3 / (2 * α) * |Work.Construction.L12 W z| ≤ 3 / (2 * α) * (CL * (C₀ * α ^ 2)) :=
            mul_le_mul_of_nonneg_left hL12Wz (by positivity)
        _ = 3 / 2 * CL * C₀ * α := by field_simp
    calc 3 / (2 * α) * |Work.Construction.L12 W z|
          * |Work.Construction.s2 θ * Work.Spaces.pth F z θ|
        ≤ (3 / 2 * CL * C₀ * α) * 101 :=
          mul_le_mul h1 hs2pthF (abs_nonneg _) (by positivity)
      _ ≤ 152 * CL * C₀ := by nlinarith [hCC, hα0, hα1]
  have ht5 : |Work.Construction.c2m θ * Work.Construction.L12 W z
      * Work.Spaces.Dz F z θ| ≤ 202 * CL * C₀ := by
    rw [abs_mul, abs_mul]
    have h1 : |Work.Construction.c2m θ| * |Work.Construction.L12 W z|
        ≤ 2 * (CL * (C₀ * α ^ 2)) := mul_le_mul hc2m hL12Wz (abs_nonneg _) (by positivity)
    calc |Work.Construction.c2m θ| * |Work.Construction.L12 W z| * |Work.Spaces.Dz F z θ|
        ≤ (2 * (CL * (C₀ * α ^ 2))) * 101 :=
          mul_le_mul h1 hDzF (abs_nonneg _) (by positivity)
      _ ≤ 202 * CL * C₀ := by
          calc (2 * (CL * (C₀ * α ^ 2))) * 101 = 202 * (CL * C₀) * α ^ 2 := by ring
            _ ≤ 202 * (CL * C₀) * 1 := mul_le_mul_of_nonneg_left hα2 (by positivity)
            _ = 202 * CL * C₀ := by ring
  have ht6 : |Work.Construction.c2m θ * Work.Construction.L12 (Work.Construction.Fstar α) z
      * Work.Spaces.Dz W z θ| ≤ 4 := by
    rw [abs_mul, abs_mul]
    have h1 : |Work.Construction.c2m θ| * |Work.Construction.L12 (Work.Construction.Fstar α) z|
        ≤ 2 * (2 * α) := mul_le_mul hc2m hFstarsharp (abs_nonneg _) (by norm_num)
    calc |Work.Construction.c2m θ| * |Work.Construction.L12 (Work.Construction.Fstar α) z|
          * |Work.Spaces.Dz W z θ|
        ≤ (2 * (2 * α)) * 1 := mul_le_mul h1 hWz (abs_nonneg _) (by positivity)
      _ ≤ 4 := by nlinarith [hα0, hα1]
  have htri : |Work.Construction.N0 α F W z θ|
      ≤ |(3 / (2 * α)) * Work.Construction.s2 θ
            * Work.Construction.L12 (Work.Construction.Fstar α) z
            * Work.Spaces.pth (Work.Construction.Fstar α) z θ|
          + |Work.Construction.c2m θ * Work.Construction.L12 (Work.Construction.Fstar α) z
            * Work.Spaces.Dz (Work.Construction.Fstar α) z θ|
          + |(1 / α) * Work.Construction.L12 W z * W z θ|
          + |(3 / (2 * α)) * Work.Construction.s2 θ * Work.Construction.L12 W z
            * Work.Spaces.pth F z θ|
          + |Work.Construction.c2m θ * Work.Construction.L12 W z * Work.Spaces.Dz F z θ|
          + |Work.Construction.c2m θ * Work.Construction.L12 (Work.Construction.Fstar α) z
            * Work.Spaces.Dz W z θ| := by
    rw [Work.Construction.N0]
    exact pt_abs_six_le _ _ _ _ _ _
  have hN0 : |Work.Construction.N0 α F W z θ| ≤ (1000 * (CL + 1)) * (1 + C₀) * (1 + B) := by
    have hB1 : (1 : ℝ) ≤ 1 + B := by linarith
    have hsum : |Work.Construction.N0 α F W z θ| ≤ 704 + 355 * (CL * C₀) := by
      linarith [htri, ht1, ht2, ht3, ht4, ht5, ht6, hCC]
    have h2 : 704 + 355 * (CL * C₀) ≤ (1000 * (CL + 1)) * (1 + C₀) := by
      nlinarith [hCL.le, hC₀, hCC]
    have h3 : (1000 * (CL + 1)) * (1 + C₀) ≤ (1000 * (CL + 1)) * (1 + C₀) * (1 + B) := by
      have h := mul_le_mul_of_nonneg_left hB1 (by positivity : (0 : ℝ) ≤ 1000 * (CL + 1) * (1 + C₀))
      calc (1000 * (CL + 1)) * (1 + C₀) = (1000 * (CL + 1)) * (1 + C₀) * 1 := by ring
        _ ≤ (1000 * (CL + 1)) * (1 + C₀) * (1 + B) := h
    linarith [hsum, h2, h3]
  refine le_trans hN0 ?_
  rw [le_div_iff₀ hs2pos]
  exact mul_le_of_le_one_right (by positivity) hs2le1

/-- **The `N`-block.** -/
theorem pt_N_le {α C₀ B C7 : ℝ} (hαι : α ∈ Set.Ioc 0 1) (hC₀ : 0 ≤ C₀) (hB : 0 ≤ B)
    (hC7nn : 0 ≤ C7) {W F Φg : ℝ → ℝ → ℝ}
    (hWS : Work.FTS.EllipticEst.SmoothOpen W)
    (hWC4 : Work.Spaces.HkMem α 4 W)
    (hFeq : F = fun z θ => Work.Construction.Fstar α z θ + W z θ)
    (hWval : ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ : ℝ, |W z θ| ≤ 1)
    (hWDz : ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ : ℝ, |Work.Spaces.Dz W z θ| ≤ 1)
    (hWDth : ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ : ℝ, |Work.Spaces.Dth W z θ| ≤ 1)
    (hFKW : ∀ z ∈ Set.Ioi (0 : ℝ), |Work.Construction.FK W z| ≤ C7 * B)
    (hΞ : ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      |Work.Construction.Rop α (Work.Construction.PhiTil α
          (fun z θ => Work.Construction.Fstar α z θ + W z θ) Φg) z θ| ≤ 13 ∧
        |Work.Construction.Uop α (Work.Construction.PhiTil α
          (fun z θ => Work.Construction.Fstar α z θ + W z θ) Φg) z θ
          / Work.Construction.s2 θ| ≤ 13 ∧
        |Work.Construction.Vop (Work.Construction.PhiTil α
          (fun z θ => Work.Construction.Fstar α z θ + W z θ) Φg) z θ| ≤ 13) :
    ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      |Work.Construction.N α F Φg z θ|
        ≤ (30000 + 200 * C7) * (1 + C₀) * (1 + B) / Real.sin (2 * θ) := by
  have hα0 : 0 < α := hαι.1
  have hα1 : α ≤ 1 := hαι.2
  have hFKF := pt_FK_le hα0 hα1 hWS hWC4 hFeq hC7nn hB hFKW
  intro z hz θ hθ
  have hs2pos : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2])
  have hs2le1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hs2ne : Work.Construction.s2 θ ≠ 0 := by
    simp only [Work.Construction.s2]
    exact ne_of_gt hs2pos
  obtain ⟨hFval, hs2pthF, hDzF⟩ := pt_F_slots hα0 hα1 hWS hFeq hWval hWDz hWDth z hz θ hθ
  obtain ⟨hΞR', hΞU', hΞV'⟩ := hΞ z hz θ hθ
  -- pass from the slots of `PhiTil α (F_* + W) Φg` to those of `PhiTil α F Φg`
  have hpt : ∀ z' θ' : ℝ, 0 < z' → 0 < θ' → θ' < π / 2 →
      Work.Construction.PhiTil α F Φg z' θ'
        = Work.Construction.PhiTil α
            (fun z θ => Work.Construction.Fstar α z θ + W z θ) Φg z' θ' := by
    intro z' θ' _ _ _
    rw [hFeq]
  have hΞR : |Work.Construction.Rop α (Work.Construction.PhiTil α F Φg) z θ| ≤ 13 := by
    rw [Work.FTS.GalFields.RHS.Sharp.Rop_congr_Q0 hpt z θ hz hθ.1 hθ.2]
    exact hΞR'
  have hΞU : |Work.Construction.Uop α (Work.Construction.PhiTil α F Φg) z θ
      / Work.Construction.s2 θ| ≤ 13 := by
    rw [Work.FTS.GalFields.RHS.Sharp.Uop_congr_Q0 hpt z θ hz hθ.1 hθ.2]
    exact hΞU'
  have hΞV : |Work.Construction.Vop (Work.Construction.PhiTil α F Φg) z θ| ≤ 13 := by
    rw [Work.FTS.GalFields.RHS.Sharp.Vop_congr_Q0 hpt z θ hz hθ.1 hθ.2]
    exact hΞV'
  have hFKFz : |Work.Construction.FK F z| ≤ (100 + C7) * (1 + B) := hFKF z hz
  have hKB : 0 ≤ (100 + C7) * (1 + B) := by
    have : 0 ≤ 100 + C7 := by linarith
    positivity
  -- the five summands of `N`
  have hA : |2 * Work.Construction.Rop α (Work.Construction.PhiTil α F Φg) z θ * F z θ|
      ≤ 2626 := by
    rw [abs_mul, abs_mul, show |(2 : ℝ)| = 2 from by norm_num]
    calc 2 * |Work.Construction.Rop α (Work.Construction.PhiTil α F Φg) z θ| * |F z θ|
        ≤ 2 * 13 * 101 :=
          mul_le_mul (mul_le_mul_of_nonneg_left hΞR (by norm_num)) hFval (abs_nonneg _)
            (by norm_num)
      _ = 2626 := by norm_num
  have hB' : |2 * Work.Construction.Uop α (Work.Construction.PhiTil α F Φg) z θ
      * Work.Spaces.pth F z θ| ≤ 2626 := by
    have hre : 2 * Work.Construction.Uop α (Work.Construction.PhiTil α F Φg) z θ
        * Work.Spaces.pth F z θ
        = 2 * (Work.Construction.Uop α (Work.Construction.PhiTil α F Φg) z θ
            / Work.Construction.s2 θ)
          * (Work.Construction.s2 θ * Work.Spaces.pth F z θ) := by
      field_simp
    rw [hre, abs_mul, abs_mul, show |(2 : ℝ)| = 2 from by norm_num]
    calc 2 * |Work.Construction.Uop α (Work.Construction.PhiTil α F Φg) z θ
            / Work.Construction.s2 θ| * |Work.Construction.s2 θ * Work.Spaces.pth F z θ|
        ≤ 2 * 13 * 101 :=
          mul_le_mul (mul_le_mul_of_nonneg_left hΞU (by norm_num)) hs2pthF (abs_nonneg _)
            (by norm_num)
      _ = 2626 := by norm_num
  have hC' : |2 * α * Work.Construction.Vop (Work.Construction.PhiTil α F Φg) z θ
      * Work.Spaces.Dz F z θ| ≤ 2626 := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hα0.le,
      show |(2 : ℝ)| = 2 from by norm_num]
    calc 2 * α * |Work.Construction.Vop (Work.Construction.PhiTil α F Φg) z θ|
          * |Work.Spaces.Dz F z θ|
        ≤ 2 * α * 13 * 101 :=
          mul_le_mul (mul_le_mul_of_nonneg_left hΞV (by positivity)) hDzF (abs_nonneg _)
            (by positivity)
      _ ≤ 2626 := by nlinarith [hα0, hα1]
  have hD' : |(1 / 2) * Work.Construction.s2 θ * Work.Construction.FK F z
      * Work.Spaces.pth F z θ| ≤ 51 * ((100 + C7) * (1 + B)) := by
    have hre : (1 / 2) * Work.Construction.s2 θ * Work.Construction.FK F z
        * Work.Spaces.pth F z θ
        = (1 / 2) * Work.Construction.FK F z
          * (Work.Construction.s2 θ * Work.Spaces.pth F z θ) := by ring
    rw [hre, abs_mul, abs_mul, show |(1 : ℝ) / 2| = 1 / 2 from by norm_num]
    calc 1 / 2 * |Work.Construction.FK F z| * |Work.Construction.s2 θ * Work.Spaces.pth F z θ|
        ≤ 1 / 2 * ((100 + C7) * (1 + B)) * 101 :=
          mul_le_mul (mul_le_mul_of_nonneg_left hFKFz (by norm_num)) hs2pthF (abs_nonneg _)
            (by positivity)
      _ ≤ 51 * ((100 + C7) * (1 + B)) := by nlinarith [hKB]
  have hE' : |Real.sin θ ^ 2 * Work.Construction.FK F z * F z θ|
      ≤ 101 * ((100 + C7) * (1 + B)) := by
    rw [abs_mul, abs_mul]
    have hsin : |Real.sin θ ^ 2| ≤ 1 := by
      rw [abs_of_nonneg (sq_nonneg _)]
      exact Real.sin_sq_le_one θ
    calc |Real.sin θ ^ 2| * |Work.Construction.FK F z| * |F z θ|
        ≤ 1 * ((100 + C7) * (1 + B)) * 101 :=
          mul_le_mul (mul_le_mul hsin hFKFz (abs_nonneg _) (by positivity)) hFval
            (abs_nonneg _) (by positivity)
      _ = 101 * ((100 + C7) * (1 + B)) := by ring
  have htri : |Work.Construction.N α F Φg z θ|
      ≤ |2 * Work.Construction.Rop α (Work.Construction.PhiTil α F Φg) z θ * F z θ|
        + |2 * Work.Construction.Uop α (Work.Construction.PhiTil α F Φg) z θ
            * Work.Spaces.pth F z θ|
        + |2 * α * Work.Construction.Vop (Work.Construction.PhiTil α F Φg) z θ
            * Work.Spaces.Dz F z θ|
        + |(1 / 2) * Work.Construction.s2 θ * Work.Construction.FK F z
            * Work.Spaces.pth F z θ|
        + |Real.sin θ ^ 2 * Work.Construction.FK F z * F z θ| := by
    rw [Work.Construction.N]
    exact pt_abs_five_le _ _ _ _ _
  have hN : |Work.Construction.N α F Φg z θ|
      ≤ (30000 + 200 * C7) * (1 + C₀) * (1 + B) := by
    have hKBp : 0 ≤ (100 + C7) * (1 + B) := hKB
    have hsum : |Work.Construction.N α F Φg z θ| ≤ 7878 + 152 * ((100 + C7) * (1 + B)) := by
      linarith [htri, hA, hB', hC', hD', hE']
    have h2 : 7878 + 152 * ((100 + C7) * (1 + B)) ≤ (30000 + 200 * C7) * (1 + B) := by
      have h1 : (1 : ℝ) ≤ 1 + B := by linarith
      have h3 : 0 ≤ C7 * (1 + B) := mul_nonneg hC7nn (by linarith)
      have h4 : 0 ≤ 1 + B := by linarith
      nlinarith [h1, h3, h4, hC7nn]
    have h3 : (30000 + 200 * C7) * (1 + B) ≤ (30000 + 200 * C7) * (1 + C₀) * (1 + B) := by
      have h4 : 0 ≤ 30000 + 200 * C7 := by linarith
      have h5 : (1 : ℝ) ≤ 1 + C₀ := by linarith
      have h6 : 0 ≤ 1 + B := by linarith
      calc (30000 + 200 * C7) * (1 + B) = (30000 + 200 * C7) * 1 * (1 + B) := by ring
        _ ≤ (30000 + 200 * C7) * (1 + C₀) * (1 + B) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h5 h4) h6
    linarith [hsum, h2, h3]
  refine le_trans hN ?_
  rw [le_div_iff₀ hs2pos]
  exact mul_le_of_le_one_right (by positivity) hs2le1

/-- **The `Transport`-block.** -/
theorem pt_Transport_le {C₀ B : ℝ} (hC₀ : 0 ≤ C₀) (hB : 0 ≤ B) {W : ℝ → ℝ → ℝ}
    (hWDth : ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ : ℝ, |Work.Spaces.Dth W z θ| ≤ 1) :
    ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      |Work.Coercivity.Transport W z θ| ≤ 3 * (1 + C₀) * (1 + B) / Real.sin (2 * θ) := by
  intro z hz θ hθ
  have hz' : (0 : ℝ) < z := hz
  have hs2pos : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2])
  have hs2le1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have h1 : (0 : ℝ) < 1 + z := by linarith
  have hDth : |Work.Spaces.Dth W z θ| ≤ 1 := hWDth z hz θ
  have h3 : |Work.Coercivity.Transport W z θ| ≤ 3 := by
    have h2 : Work.Coercivity.Transport W z θ = 3 * Work.Spaces.Dth W z θ / (1 + z) := rfl
    rw [h2, abs_div, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3), abs_of_pos h1,
      div_le_iff₀ h1]
    nlinarith [hDth, h1]
  have h4 : (3 : ℝ) ≤ 3 * (1 + C₀) * (1 + B) := by nlinarith [hC₀, hB]
  refine le_trans h3 (le_trans h4 ?_)
  rw [le_div_iff₀ hs2pos]
  exact mul_le_of_le_one_right (by positivity) hs2le1

end Work.FTS.StrongEps.E5Aux2
