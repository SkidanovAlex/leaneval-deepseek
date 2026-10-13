/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/EpsEngine/UopSlot.lean` — the `Uop/sin 2θ` slot of `EpsDecay`

Per the lead's ruling (2026-10-11), the `EpsDecay` clause is to be stated with `Maj ≤ C` for an
explicit `C` (`≥ 3`), because the explicit `Theta α F_*` pieces of the `Uop/sin 2θ` and `Vop` slots
do **not** vanish at `z = 0`:

    Uop α (Theta α F_*)/sin 2θ = −3/(2(1+z)) + α z/(2(1+z)²)  →  −3/2,
    Vop (Theta α F_*)          =  c2m θ/(1+z)                 →  c2m θ  (down to −2).

This module assembles the `Uop/sin 2θ` slot with `C = 3`:

* `Uop_div_decomp` — the decomposition into the three pieces (additivity of `Uop`,
  `Rop_Uop_Vop_add`, plus the affineness of `PhiTil`);
* `ell_Uop_le` — the `EllPkgGo` piece, from `EllPkgGo.U` and the pointwise extraction `hpt`
  (instantiated by `Work.FTS_RegExport.RXT.hkMem_pointwise_min`);
* `uop_slot_abs_le_three` — the assembly: the three pieces are `≤ P`, `≤ Cs α` and `≤ 3/2` in
  absolute value, and `P + Cs α ≤ 1` gives `|·| ≤ 5/2 < 3`.

Everything here is `sorry`-free.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.Galerkin.Defs
import Submission.Work.FTS.VocabO
import Submission.Work.FTS.ClassC.Defs
import Submission.Work.FTS.EpsEngine.Theta_Fstar_ops
import Submission.Work.FTS.EpsEngine.Rop_Uop_Vop_add

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology ENNReal
open MeasureTheory Set Filter
open Work.FTS.Galerkin (Fn Fam slice)

namespace Work.FTS.EpsEngine

set_option autoImplicit false

/-! ## The decomposition of the `Uop/sin 2θ` slot -/

/-- **The `Uop/sin 2θ` slot's decomposition into its three pieces.** -/
theorem Uop_div_decomp {α : ℝ} {f Φs : ℝ → ℝ → ℝ} {E : (ℝ → ℝ → ℝ) → ℝ → ℝ → ℝ} {z θ : ℝ}
    (hz₁ : DifferentiableAt ℝ (fun z' => Work.Construction.PhiTil α f (E f) z' θ) z)
    (hz₂ : DifferentiableAt ℝ (fun z' => Φs z' θ) z)
    (hz₃ : DifferentiableAt ℝ (fun z' => Work.Construction.PhiTil α (Work.Construction.Fstar α)
      Φs z' θ) z)
    (hz₄ : DifferentiableAt ℝ (fun z' => Work.Construction.Theta α (Work.Construction.Fstar α)
      z' θ) z)
    (hθ₁ : DifferentiableAt ℝ (fun θ' => Work.Construction.PhiTil α f (E f) z θ') θ)
    (hθ₂ : DifferentiableAt ℝ (fun θ' => Φs z θ') θ)
    (hθ₃ : DifferentiableAt ℝ (fun θ' => Work.Construction.PhiTil α (Work.Construction.Fstar α)
      Φs z θ') θ)
    (hθ₄ : DifferentiableAt ℝ (fun θ' => Work.Construction.Theta α (Work.Construction.Fstar α)
      z θ') θ) :
    Work.Construction.Uop α (Work.Construction.PhiTil α f (fun z θ => Φs z θ + E f z θ)) z θ
        / Work.Construction.s2 θ
      = Work.Construction.Uop α (Work.Construction.PhiTil α f (E f)) z θ
          / Work.Construction.s2 θ
        + Work.Construction.Uop α (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ
          / Work.Construction.s2 θ
        + Work.Construction.Uop α (Work.Construction.Theta α (Work.Construction.Fstar α)) z θ
          / Work.Construction.s2 θ := by
  have hfun₁ : Work.Construction.PhiTil α f (fun z θ => Φs z θ + E f z θ)
      = fun z θ => Work.Construction.PhiTil α f (E f) z θ + Φs z θ := by
    funext z θ
    simp only [Work.Construction.PhiTil, Work.Construction.Theta]
    ring
  have hfun₂ : Φs = fun z θ => Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs z θ
      + Work.Construction.Theta α (Work.Construction.Fstar α) z θ := by
    funext z θ
    simp only [Work.Construction.PhiTil, Work.Construction.Theta]
    ring
  rw [hfun₁]
  have h₁ := (Work.FTS.EpsEngine.Rop_Uop_Vop_add (α := α) (z := z) (θ := θ)
    (Ψ₁ := Work.Construction.PhiTil α f (E f)) (Ψ₂ := Φs) hz₁ hz₂ hθ₁ hθ₂).2.1
  rw [h₁]
  have h₂ := (Work.FTS.EpsEngine.Rop_Uop_Vop_add (α := α) (z := z) (θ := θ)
    (Ψ₁ := Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs)
    (Ψ₂ := Work.Construction.Theta α (Work.Construction.Fstar α)) hz₃ hz₄ hθ₃ hθ₄).2.1
  have hUΦ : Work.Construction.Uop α Φs z θ
      = Work.Construction.Uop α (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ
        + Work.Construction.Uop α (Work.Construction.Theta α (Work.Construction.Fstar α)) z θ := by
    conv_lhs => rw [hfun₂]
    exact h₂
  rw [hUΦ, add_div]
  ring

/-! ## The `EllPkgGo` piece -/

/-- **The `EllPkgGo` piece of the `Uop/sin 2θ` slot.** -/
theorem ell_Uop_le {α Ce Cpt : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hCpt : 0 ≤ Cpt)
    (hpt : ∀ g : Fn, ContDiffOn ℝ 4 (Function.uncurry g) Work.FTS.EllipticEst.Q0 →
      Work.Spaces.HkMem α 4 g → ∀ b a : ℕ, a + b ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ →
        θ < Real.pi / 2 →
        |Work.Spaces.mixed b a g z θ| ≤ Cpt * min z 1 * Work.Spaces.HkNorm α 4 g)
    {f : Fn} {E : Fn → Fn} (hf : Work.FTS.ClassC.ClassC α f)
    (hEll : ∀ u : Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    |Work.Construction.Uop α (Work.Construction.PhiTil α f (E f)) z θ / Work.Construction.s2 θ|
      ≤ Cpt * (Ce * Work.FTS.Nonlin.Xn α f) * min z 1 := by
  have hU : Work.FTS.VocabO.HQo α 4
      (fun z θ => Work.Construction.Uop α (Work.Construction.PhiTil α f (E f)) z θ
        / Work.Construction.s2 θ) := (hEll f hf).1.U.1
  have hsm : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Work.Construction.Uop α (Work.Construction.PhiTil α f (E f)) z θ
        / Work.Construction.s2 θ) := hU.1
  have hmem : Work.Spaces.HkMem α 4
      (fun z θ => Work.Construction.Uop α (Work.Construction.PhiTil α f (E f)) z θ
        / Work.Construction.s2 θ) := hU.2
  have h4 : ContDiffOn ℝ 4
      (Function.uncurry (fun z θ => Work.Construction.Uop α (Work.Construction.PhiTil α f (E f))
        z θ / Work.Construction.s2 θ)) Work.FTS.EllipticEst.Q0 :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp hsm 4
  have h := hpt _ h4 hmem 0 0 (by norm_num) z θ hz hθ.1 hθ.2
  simp only [Work.Spaces.mixed_zero_left, Work.Spaces.mixed_zero_right, Work.Spaces.DthIter_zero,
    Work.Spaces.DzIter_zero] at h
  refine h.trans ?_
  have hXn : Work.FTS.Nonlin.Xn α
      (fun z θ => Work.Construction.Uop α (Work.Construction.PhiTil α f (E f)) z θ
        / Work.Construction.s2 θ) ≤ Ce * Work.FTS.Nonlin.Xn α f := (hEll f hf).1.U.2
  calc Cpt * min z 1 * Work.Spaces.HkNorm α 4
        (fun z θ => Work.Construction.Uop α (Work.Construction.PhiTil α f (E f)) z θ
          / Work.Construction.s2 θ)
      = Cpt * min z 1 * Work.FTS.Nonlin.Xn α
          (fun z θ => Work.Construction.Uop α (Work.Construction.PhiTil α f (E f)) z θ
            / Work.Construction.s2 θ) := by
        rw [Work.FTS.Nonlin.Xn]
    _ ≤ Cpt * min z 1 * (Ce * Work.FTS.Nonlin.Xn α f) := by
        refine mul_le_mul_of_nonneg_left hXn (by positivity)
    _ = Cpt * (Ce * Work.FTS.Nonlin.Xn α f) * min z 1 := by ring

/-! ## The assembly -/

/-- **The `Uop/sin 2θ` slot of `EpsDecay`, with `C = 3`.**  With the decomposition
`Uop_div_decomp` and the two piece bounds, the block is `≤ P + Cs α + 3/2` in absolute value, where
`P = Cpt · Ce · C₀α²` bounds the `EllPkgGo` piece; the smallness `P + Cs α ≤ 1` gives `≤ 5/2 < 3`.

The star piece is `≤ Cs α` by `Work.FTS.EpsEngine.star_Uop_div_le` (extraction of
`StarPkgo2.UsW`) and the explicit piece is `∈ [−3/2, 0]` by
`Work.FTS.EpsEngine.Theta_Fstar_ops`. -/
theorem uop_slot_abs_le_three {α Cpt Ce Cs C₀ : ℝ} {f Φs : Fn} {E : Fn → Fn} {z θ : ℝ}
    (hα : 0 < α) (hα1 : α ≤ 1) (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2))
    (hCpt : 0 ≤ Cpt) (hCe : 0 ≤ Ce) (hCs : 0 ≤ Cs) (hC₀ : 0 ≤ C₀)
    (hsmall : Cpt * (Ce * (C₀ * α ^ 2)) + Cs * α ≤ 1)
    (hdec : Work.Construction.Uop α (Work.Construction.PhiTil α f
          (fun z θ => Φs z θ + E f z θ)) z θ / Work.Construction.s2 θ
        = Work.Construction.Uop α (Work.Construction.PhiTil α f (E f)) z θ
            / Work.Construction.s2 θ
          + Work.Construction.Uop α (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs)
              z θ / Work.Construction.s2 θ
          + Work.Construction.Uop α (Work.Construction.Theta α (Work.Construction.Fstar α))
              z θ / Work.Construction.s2 θ)
    (hE : |Work.Construction.Uop α (Work.Construction.PhiTil α f (E f)) z θ
        / Work.Construction.s2 θ| ≤ Cpt * (Ce * (C₀ * α ^ 2)) * min z 1)
    (hS : |Work.Construction.Uop α (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ
        / Work.Construction.s2 θ| ≤ Cs * α) :
    |Work.Construction.Uop α (Work.Construction.PhiTil α f
        (fun z θ => Φs z θ + E f z θ)) z θ / Work.Construction.s2 θ| ≤ 3 := by
  have hΘ := (Work.FTS.EpsEngine.Theta_Fstar_ops (α := α) hα hα1).2.2 z θ hz hθ.1 hθ.2
  -- the explicit piece lies in `[-3/2, 0]`
  have hnum : 0 ≤ 3 * (1 + z) - α * z := by nlinarith [hα.le, hz.le]
  have hden : 0 < 2 * (1 + z) ^ 2 := by positivity
  have hkey : 0 ≤ 3 / (2 * (1 + z)) - α * z / (2 * (1 + z) ^ 2) := by
    have heq : 3 / (2 * (1 + z)) - α * z / (2 * (1 + z) ^ 2)
        = (3 * (1 + z) - α * z) / (2 * (1 + z) ^ 2) := by
      field_simp
      try ring
    rw [heq]
    exact div_nonneg hnum hden.le
  have hle32 : 3 / (2 * (1 + z)) ≤ 3 / 2 := by
    have heq : 3 / 2 - 3 / (2 * (1 + z)) = (3 * (2 * (1 + z)) - 3 * 2) / (2 * (2 * (1 + z))) := by
      field_simp
      try ring
    have hpos : 0 < 2 * (2 * (1 + z)) := by positivity
    have hnonneg : 0 ≤ 3 / 2 - 3 / (2 * (1 + z)) := by
      rw [heq]
      exact div_nonneg (by nlinarith [hz.le]) hpos.le
    linarith
  have hpiece : |Work.Construction.Uop α (Work.Construction.Theta α (Work.Construction.Fstar α))
      z θ / Work.Construction.s2 θ| ≤ 3 / 2 := by
    rw [hΘ]
    have hval : -(3 / (2 * (1 + z))) + α * z / (2 * (1 + z) ^ 2)
        = -(3 / (2 * (1 + z)) - α * z / (2 * (1 + z) ^ 2)) := by ring
    rw [hval, abs_neg, abs_of_nonneg hkey]
    have hb : (0 : ℝ) ≤ α * z / (2 * (1 + z) ^ 2) := by positivity
    linarith [hle32, hb]
  rw [hdec]
  have hP : Cpt * (Ce * (C₀ * α ^ 2)) * min z 1 ≤ Cpt * (Ce * (C₀ * α ^ 2)) := by
    have h1 : min z 1 ≤ 1 := min_le_right _ _
    have h2 : 0 ≤ Cpt * (Ce * (C₀ * α ^ 2)) := by positivity
    calc Cpt * (Ce * (C₀ * α ^ 2)) * min z 1 ≤ Cpt * (Ce * (C₀ * α ^ 2)) * 1 :=
          mul_le_mul_of_nonneg_left h1 h2
      _ = Cpt * (Ce * (C₀ * α ^ 2)) := mul_one _
  calc |Work.Construction.Uop α (Work.Construction.PhiTil α f (E f)) z θ
          / Work.Construction.s2 θ
        + Work.Construction.Uop α (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ
          / Work.Construction.s2 θ
        + Work.Construction.Uop α (Work.Construction.Theta α (Work.Construction.Fstar α)) z θ
          / Work.Construction.s2 θ|
      ≤ |Work.Construction.Uop α (Work.Construction.PhiTil α f (E f)) z θ
            / Work.Construction.s2 θ|
        + |Work.Construction.Uop α (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs)
            z θ / Work.Construction.s2 θ|
        + |Work.Construction.Uop α (Work.Construction.Theta α (Work.Construction.Fstar α)) z θ
            / Work.Construction.s2 θ| := by
        refine (abs_add_le _ _).trans ?_
        exact add_le_add_left (abs_add_le _ _) _
    _ ≤ 3 := by
        linarith [hE.trans hP, hS, hpiece, hsmall]

end Work.FTS.EpsEngine
