/-
Copyright: work module for the Elgindi finite-time singularity project.

# `EllPkgClsSlots` — the slot identities and the degenerate `α = 0` case

* `slot_identities`: if the function `A` equals `P₁ - P₂` on the open quadrant and both the `z`- and
  the `θ`-derivatives split there, then `Rop`, `Uop` and `Vop` are additive on `(A, P₁, P₂)`.
* `HQo_sub_of_slot`: `HQo α k` transfers from `X₁`, `X₂` to any `A` agreeing with `X₁ - X₂` on the
  open quadrant (via `smoothOpen_sub_bsl`, `HkMem_sub_of_HkMem` and the open-quadrant congruence
  `Cert.GbarSin.HkMem_congr_Q0`).
* `L12_sub_of_Theta`: `Theta`-additivity on the half-line is `L₁₂`-additivity there, for `α ≠ 0`.
* `EllPkgCls_sub_zero`: the closure of `EllPkgCls` under differences in the degenerate case
  `α = 0`, where `Theta 0 F = 0` and hence `PhiTil 0 F Ψ = Ψ` (up to `sub_zero`).
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.StrongEps.EComparison.EllPkgClsVop
import Submission.Work.FTS.EllipticEst.bslOp_sub
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.assembly_core
import Submission.Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EComparison

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-- **The slot identities**: if `A = P₁ - P₂` as functions on the open quadrant and both the
`z`- and the `θ`-derivatives split there, then `Rop`, `Uop` and `Vop` are additive on
`(A, P₁, P₂)`. -/
theorem slot_identities {α : ℝ} {A P₁ P₂ : Fn}
    (hval : ∀ z θ, 0 < z → 0 < θ → θ < π / 2 → A z θ = P₁ z θ - P₂ z θ)
    (hpz : ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
      Work.Spaces.pz A z θ = Work.Spaces.pz P₁ z θ - Work.Spaces.pz P₂ z θ)
    (hpth : ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
      Work.Spaces.pth A z θ = Work.Spaces.pth P₁ z θ - Work.Spaces.pth P₂ z θ) :
    (∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
        Work.Construction.Rop α A z θ
          = Work.Construction.Rop α P₁ z θ - Work.Construction.Rop α P₂ z θ)
      ∧ (∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
        Work.Construction.Uop α A z θ
          = Work.Construction.Uop α P₁ z θ - Work.Construction.Uop α P₂ z θ)
      ∧ (∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
        Work.Construction.Vop A z θ
          = Work.Construction.Vop P₁ z θ - Work.Construction.Vop P₂ z θ) := by
  refine ⟨?_, ?_, ?_⟩
  · intro z θ hz h0 h1
    simp only [Work.Construction.Rop]
    rw [hval z θ hz h0 h1, hpz z θ hz h0 h1, hpth z θ hz h0 h1]
    ring
  · intro z θ hz h0 h1
    simp only [Work.Construction.Uop]
    rw [hval z θ hz h0 h1, hpz z θ hz h0 h1]
    ring
  · intro z θ hz h0 h1
    simp only [Work.Construction.Vop]
    rw [hval z θ hz h0 h1, hpth z θ hz h0 h1]
    ring

/-- **The `HQo`-slot of a difference**: if `X₁`, `X₂` are of class `HQo α k` and the function
`X₁ - X₂` agrees with `A` on the open quadrant, then `A` is of class `HQo α k`. -/
theorem HQo_sub_of_slot {α : ℝ} (k : ℕ) {X₁ X₂ A : Fn}
    (h₁ : Work.FTS.VocabO.HQo α k X₁) (h₂ : Work.FTS.VocabO.HQo α k X₂)
    (h : ∀ z θ, 0 < z → 0 < θ → θ < π / 2 → X₁ z θ - X₂ z θ = A z θ) :
    Work.FTS.VocabO.HQo α k A := by
  refine ⟨?_, ?_⟩
  · refine Work.FTS.EllipticEst.Cert.smoothOpen_congr_bsl
      (Work.FTS.EllipticEst.Cert.smoothOpen_sub_bsl h₁.1 h₂.1) ?_
    intro z θ hz h0 h1
    exact h z θ hz h0 h1
  · exact Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α k
      (Work.FTS.StrongPersist.H6Pair6Aux.HkMem_sub_of_HkMem α k h₁.1 h₂.1 h₁.2 h₂.2)
      (fun z hz θ hθ => h z θ hz hθ.1 hθ.2)

/-- **`L₁₂`-additivity on the half-line, from the additivity of `Theta`.** -/
theorem L12_sub_of_Theta {α : ℝ} (hα : α ≠ 0) {F₁ F₂ : Fn}
    (hΘ : ∀ z ∈ Work.Spaces.Iz, ∀ θ : ℝ,
      Work.Construction.Theta α (fun z θ => F₁ z θ - F₂ z θ) z θ
        = Work.Construction.Theta α F₁ z θ - Work.Construction.Theta α F₂ z θ) :
    ∀ z ∈ Set.Ioi (0 : ℝ),
      Work.Construction.L12 (fun z θ => F₁ z θ - F₂ z θ) z
        = Work.Construction.L12 F₁ z - Work.Construction.L12 F₂ z := by
  intro z hz
  have hzIz : z ∈ Work.Spaces.Iz := by
    have hle : (0 : ℝ) ≤ z := le_of_lt (show (0 : ℝ) < z from hz)
    simpa only [Work.Spaces.Iz, Set.mem_Ici] using hle
  have h := hΘ z hzIz (π / 4)
  simp only [Work.Construction.Theta, Work.Construction.s2] at h
  have hsin : Real.sin (2 * (π / 4)) = 1 := by
    rw [show 2 * (π / 4) = π / 2 from by ring, Real.sin_pi_div_two]
  rw [hsin, mul_one] at h
  have hc : (1 / (4 * α)) ≠ 0 := by
    have h4 : (4 * α : ℝ) ≠ 0 := mul_ne_zero (by norm_num) hα
    simpa using inv_ne_zero h4
  have h'' : (1 / (4 * α)) * (Work.Construction.L12 (fun z θ => F₁ z θ - F₂ z θ) z
      - (Work.Construction.L12 F₁ z - Work.Construction.L12 F₂ z)) = 0 := by linarith
  rcases mul_eq_zero.mp h'' with h1 | h2
  · exact absurd h1 hc
  · linarith [sub_eq_zero.mp h2]

/-- **The `α = 0` case.**  Here `Theta 0 F = 0`, so `PhiTil 0 F Ψ = Ψ` for every `F` and the
`V`-slot machinery is not needed: only the splits of the two stream functions themselves enter. -/
theorem EllPkgCls_sub_zero {Ce : ℝ} {F₁ F₂ Ψ₁ Ψ₂ : Fn}
    (h₁ : EllPkgCls 0 Ce F₁ Ψ₁) (h₂ : EllPkgCls 0 Ce F₂ Ψ₂) :
    EllPkgCls 0 Ce (fun z θ => F₁ z θ - F₂ z θ) (fun z θ => Ψ₁ z θ - Ψ₂ z θ) := by
  have hPhi : ∀ F Ψ : Fn, Work.Construction.PhiTil 0 F Ψ = Ψ := by
    intro F Ψ
    funext z θ
    simp only [Work.Construction.PhiTil, Work.Construction.Theta, Work.Construction.s2]
    norm_num
  have hR₁ : Work.FTS.VocabO.HQo 0 6 (Work.Construction.Rop 0 Ψ₁) := by
    rw [← hPhi F₁ Ψ₁]; exact h₁.2.2.1
  have hR₂ : Work.FTS.VocabO.HQo 0 6 (Work.Construction.Rop 0 Ψ₂) := by
    rw [← hPhi F₂ Ψ₂]; exact h₂.2.2.1
  have hU₁ : Work.FTS.VocabO.HQo 0 6
      (fun z θ => Work.Construction.Uop 0 Ψ₁ z θ / Work.Construction.s2 θ) := by
    rw [← hPhi F₁ Ψ₁]; exact h₁.2.2.2.1
  have hU₂ : Work.FTS.VocabO.HQo 0 6
      (fun z θ => Work.Construction.Uop 0 Ψ₂ z θ / Work.Construction.s2 θ) := by
    rw [← hPhi F₂ Ψ₂]; exact h₂.2.2.2.1
  have hV₁ : Work.FTS.VocabO.HQo 0 6 (Work.Construction.Vop Ψ₁) := by
    rw [← hPhi F₁ Ψ₁]; exact h₁.2.2.2.2
  have hV₂ : Work.FTS.VocabO.HQo 0 6 (Work.Construction.Vop Ψ₂) := by
    rw [← hPhi F₂ Ψ₂]; exact h₂.2.2.2.2
  have hval : ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
      (fun z θ => Ψ₁ z θ - Ψ₂ z θ) z θ = Ψ₁ z θ - Ψ₂ z θ := fun _ _ _ _ _ => rfl
  have hpz : ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
      Work.Spaces.pz (fun z θ => Ψ₁ z θ - Ψ₂ z θ) z θ
        = Work.Spaces.pz Ψ₁ z θ - Work.Spaces.pz Ψ₂ z θ :=
    fun z θ hz h0 h1 => pz_sub h₁.1 h₂.1 hz h0 h1
  have hpth : ∀ z θ, 0 < z → 0 < θ → θ < π / 2 →
      Work.Spaces.pth (fun z θ => Ψ₁ z θ - Ψ₂ z θ) z θ
        = Work.Spaces.pth Ψ₁ z θ - Work.Spaces.pth Ψ₂ z θ :=
    fun z θ hz h0 h1 => pth_sub h₁.1 h₂.1 hz h0 h1
  obtain ⟨hsR, hsU, hsV⟩ := slot_identities (α := 0)
    (A := fun z θ => Ψ₁ z θ - Ψ₂ z θ) (P₁ := Ψ₁) (P₂ := Ψ₂) hval hpz hpth
  have hgoal : Work.Construction.PhiTil 0 (fun z θ => F₁ z θ - F₂ z θ)
      (fun z θ => Ψ₁ z θ - Ψ₂ z θ) = fun z θ => Ψ₁ z θ - Ψ₂ z θ :=
    hPhi (fun z θ => F₁ z θ - F₂ z θ) (fun z θ => Ψ₁ z θ - Ψ₂ z θ)
  refine ⟨Work.FTS.StrongPersist.H6Pair6Aux.smoothOpen_sub' h₁.1 h₂.1, ?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_⟩
    · intro z hz θ h0 h1
      have hc : Real.cos θ ≠ 0 :=
        ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], h1⟩)
      have hC2₁ : ContDiffAt ℝ 2 (Function.uncurry Ψ₁) (z, θ) :=
        (h₁.1.forall 2).contDiffAt (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds ⟨hz, h0, h1⟩)
      have hC2₂ : ContDiffAt ℝ 2 (Function.uncurry Ψ₂) (z, θ) :=
        (h₂.1.forall 2).contDiffAt (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds ⟨hz, h0, h1⟩)
      rw [Work.FTS.EllipticEst.bslOp_sub 0 Ψ₁ Ψ₂ z θ hc hC2₁ hC2₂,
        h₁.2.1.1 z hz θ h0 h1, h₂.2.1.1 z hz θ h0 h1]
    · intro z
      show Ψ₁ z 0 - Ψ₂ z 0 = 0
      rw [h₁.2.1.2.1 z, h₂.2.1.2.1 z]
      ring
    · intro z
      show Ψ₁ z (π / 2) - Ψ₂ z (π / 2) = 0
      rw [h₁.2.1.2.2.1 z, h₂.2.1.2.2.1 z]
      ring
    · intro θ hθ
      simpa using (h₁.2.1.2.2.2 θ hθ).sub (h₂.2.1.2.2.2 θ hθ)
  · rw [hgoal]
    exact HQo_sub_of_slot 6 hR₁ hR₂ (fun z θ hz h0 h1 => (hsR z θ hz h0 h1).symm)
  · rw [hgoal]
    refine HQo_sub_of_slot 6 hU₁ hU₂ (fun z θ hz h0 h1 => ?_)
    rw [← sub_div, ← hsU z θ hz h0 h1]
  · rw [hgoal]
    exact HQo_sub_of_slot 6 hV₁ hV₂ (fun z θ hz h0 h1 => (hsV z θ hz h0 h1).symm)

end Work.FTS.StrongEps.EComparison
