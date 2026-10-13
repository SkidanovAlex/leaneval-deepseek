/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/EpsEngine/VopSlot.lean` — the `Vop` slot of `EpsDecay`

The third block slot, in the relaxed form `Maj ≤ C` (`C = 3`) forced by the explicit piece
`Vop (Theta α F_*) = c2m θ/(1+z)`, whose value at `z = 0` ranges down to `−2` as `θ → π/2`
(`Work.FTS.EpsEngine.Theta_Fstar_ops`).

* `Vop_decomp` — the decomposition into the three pieces (additivity of `Vop`, `Rop_Uop_Vop_add`);
* `ell_Vop_le` — the `EllPkgGo` piece, from `EllPkgGo.V` and the pointwise extraction `hpt`;
* `star_Vop_le` — the star piece, from `StarPkgo2.V` (`WDp 4 (Vop (PhiTil α F_* Φs)) ≤ Cs α`) via
  `Work.FTS.OpenPkg.WDMem_of_WDp_le`;
* `vop_slot_abs_le_three` — the assembly (`P + Cs α ≤ 1` gives `|·| ≤ 3`).

Everything here is `sorry`-free.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.Galerkin.Defs
import Submission.Work.FTS.VocabO
import Submission.Work.FTS.VocabO2
import Submission.Work.FTS.OpenPkg.Basic
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

/-! ## The decomposition -/

/-- **The `Vop` slot's decomposition into its three pieces.** -/
theorem Vop_decomp {α : ℝ} {f Φs : ℝ → ℝ → ℝ} {E : (ℝ → ℝ → ℝ) → ℝ → ℝ → ℝ} {z θ : ℝ}
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
    Work.Construction.Vop (Work.Construction.PhiTil α f (fun z θ => Φs z θ + E f z θ)) z θ
      = Work.Construction.Vop (Work.Construction.PhiTil α f (E f)) z θ
        + Work.Construction.Vop (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ
        + Work.Construction.Vop (Work.Construction.Theta α (Work.Construction.Fstar α)) z θ := by
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
    (Ψ₁ := Work.Construction.PhiTil α f (E f)) (Ψ₂ := Φs) hz₁ hz₂ hθ₁ hθ₂).2.2
  rw [h₁]
  have h₂ := (Work.FTS.EpsEngine.Rop_Uop_Vop_add (α := α) (z := z) (θ := θ)
    (Ψ₁ := Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs)
    (Ψ₂ := Work.Construction.Theta α (Work.Construction.Fstar α)) hz₃ hz₄ hθ₃ hθ₄).2.2
  have hVΦ : Work.Construction.Vop Φs z θ
      = Work.Construction.Vop (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ
        + Work.Construction.Vop (Work.Construction.Theta α (Work.Construction.Fstar α)) z θ := by
    conv_lhs => rw [hfun₂]
    exact h₂
  rw [hVΦ]
  ring

/-! ## The two pieces' bounds -/

/-- **The `EllPkgGo` piece of the `Vop` slot.** -/
theorem ell_Vop_le {α Ce Cpt : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hCpt : 0 ≤ Cpt)
    (hpt : ∀ g : Fn, ContDiffOn ℝ 4 (Function.uncurry g) Work.FTS.EllipticEst.Q0 →
      Work.Spaces.HkMem α 4 g → ∀ b a : ℕ, a + b ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ →
        θ < Real.pi / 2 →
        |Work.Spaces.mixed b a g z θ| ≤ Cpt * min z 1 * Work.Spaces.HkNorm α 4 g)
    {f : Fn} {E : Fn → Fn} (hf : Work.FTS.ClassC.ClassC α f)
    (hEll : ∀ u : Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    |Work.Construction.Vop (Work.Construction.PhiTil α f (E f)) z θ|
      ≤ Cpt * (Ce * Work.FTS.Nonlin.Xn α f) * min z 1 := by
  have hU : Work.FTS.VocabO.HQo α 4
      (Work.Construction.Vop (Work.Construction.PhiTil α f (E f))) := (hEll f hf).1.V.1
  have hsm : Work.FTS.EllipticEst.SmoothOpen
      (Work.Construction.Vop (Work.Construction.PhiTil α f (E f))) := hU.1
  have hmem : Work.Spaces.HkMem α 4 (Work.Construction.Vop (Work.Construction.PhiTil α f (E f))) :=
    hU.2
  have h4 : ContDiffOn ℝ 4 (Function.uncurry
      (Work.Construction.Vop (Work.Construction.PhiTil α f (E f))))
      Work.FTS.EllipticEst.Q0 :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp hsm 4
  have h := hpt _ h4 hmem 0 0 (by norm_num) z θ hz hθ.1 hθ.2
  simp only [Work.Spaces.mixed_zero_left, Work.Spaces.mixed_zero_right, Work.Spaces.DthIter_zero,
    Work.Spaces.DzIter_zero] at h
  refine h.trans ?_
  have hXn : Work.FTS.Nonlin.Xn α (Work.Construction.Vop (Work.Construction.PhiTil α f (E f)))
      ≤ Ce * Work.FTS.Nonlin.Xn α f := (hEll f hf).1.V.2
  calc Cpt * min z 1 * Work.Spaces.HkNorm α 4
        (Work.Construction.Vop (Work.Construction.PhiTil α f (E f)))
      = Cpt * min z 1 * Work.FTS.Nonlin.Xn α
          (Work.Construction.Vop (Work.Construction.PhiTil α f (E f))) := by
        rw [Work.FTS.Nonlin.Xn]
    _ ≤ Cpt * min z 1 * (Ce * Work.FTS.Nonlin.Xn α f) := by
        refine mul_le_mul_of_nonneg_left hXn (by positivity)
    _ = Cpt * (Ce * Work.FTS.Nonlin.Xn α f) * min z 1 := by ring

/-- **The star piece of the `Vop` slot**, from the `V` field of `StarPkgo2`
(`WDp 4 (Vop (PhiTil α F_* Φs)) ≤ Cs α`) through `Work.FTS.OpenPkg.WDMem_of_WDp_le`. -/
theorem star_Vop_le {α Cs : ℝ} {Φs : ℝ → ℝ → ℝ}
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Construction.Vop (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ|
        ≤ Cs * α := by
  intro z θ hz hθ0 hθ1
  exact Work.FTS.OpenPkg.WDMem_of_WDp_le hstar.V.1 hstar.V.2 0 0 (by norm_num) z θ hz hθ0 hθ1

/-! ## The assembly -/

/-- **The `Vop` slot of `EpsDecay`, with `C = 3`.** -/
theorem vop_slot_abs_le_three {α Cpt Ce Cs C₀ : ℝ} {f Φs : Fn} {E : Fn → Fn} {z θ : ℝ}
    (hα : 0 < α) (hα1 : α ≤ 1) (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2))
    (hCpt : 0 ≤ Cpt) (hCe : 0 ≤ Ce) (hCs : 0 ≤ Cs) (hC₀ : 0 ≤ C₀)
    (hsmall : Cpt * (Ce * (C₀ * α ^ 2)) + Cs * α ≤ 1)
    (hdec : Work.Construction.Vop (Work.Construction.PhiTil α f
          (fun z θ => Φs z θ + E f z θ)) z θ
        = Work.Construction.Vop (Work.Construction.PhiTil α f (E f)) z θ
          + Work.Construction.Vop (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ
          + Work.Construction.Vop (Work.Construction.Theta α (Work.Construction.Fstar α)) z θ)
    (hE : |Work.Construction.Vop (Work.Construction.PhiTil α f (E f)) z θ|
        ≤ Cpt * (Ce * (C₀ * α ^ 2)) * min z 1)
    (hS : |Work.Construction.Vop (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ|
        ≤ Cs * α) :
    |Work.Construction.Vop (Work.Construction.PhiTil α f (fun z θ => Φs z θ + E f z θ)) z θ|
      ≤ 3 := by
  have hΘ := (Work.FTS.EpsEngine.Theta_Fstar_ops (α := α) hα hα1).2.1 z θ hz hθ.1 hθ.2
  -- the explicit piece is `c2m θ/(1+z)`, of absolute value `≤ 2`
  have hc2m : |Work.Construction.c2m θ| ≤ 2 := by
    have h1 : |Real.cos (2 * θ)| ≤ 1 := Real.abs_cos_le_one _
    have h2 : Real.sin θ ^ 2 ≤ 1 := Real.sin_sq_le_one θ
    have h3 : |Real.cos (2 * θ) - Real.sin θ ^ 2| ≤ |Real.cos (2 * θ)| + Real.sin θ ^ 2 := by
      have h := abs_sub_le (Real.cos (2 * θ)) 0 (Real.sin θ ^ 2)
      rw [sub_zero, zero_sub, abs_neg, abs_of_nonneg (sq_nonneg (Real.sin θ))] at h
      exact h
    simp only [Work.Construction.c2m]
    linarith
  have hdiv : |Work.Construction.c2m θ / (1 + z)| ≤ 2 := by
    rw [abs_div, abs_of_pos (by linarith : (0 : ℝ) < 1 + z), div_le_iff₀ (by linarith)]
    nlinarith [abs_nonneg (Work.Construction.c2m θ), hc2m]
  have hpiece : |Work.Construction.Vop (Work.Construction.Theta α (Work.Construction.Fstar α))
      z θ| ≤ 2 := by
    rw [hΘ]
    exact hdiv
  have hP : Cpt * (Ce * (C₀ * α ^ 2)) * min z 1 ≤ Cpt * (Ce * (C₀ * α ^ 2)) := by
    have h1 : min z 1 ≤ 1 := min_le_right _ _
    have h2 : 0 ≤ Cpt * (Ce * (C₀ * α ^ 2)) := by positivity
    calc Cpt * (Ce * (C₀ * α ^ 2)) * min z 1 ≤ Cpt * (Ce * (C₀ * α ^ 2)) * 1 :=
          mul_le_mul_of_nonneg_left h1 h2
      _ = Cpt * (Ce * (C₀ * α ^ 2)) := mul_one _
  rw [hdec]
  calc |Work.Construction.Vop (Work.Construction.PhiTil α f (E f)) z θ
        + Work.Construction.Vop (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ
        + Work.Construction.Vop (Work.Construction.Theta α (Work.Construction.Fstar α)) z θ|
      ≤ |Work.Construction.Vop (Work.Construction.PhiTil α f (E f)) z θ|
        + |Work.Construction.Vop (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs) z θ|
        + |Work.Construction.Vop (Work.Construction.Theta α (Work.Construction.Fstar α)) z θ| := by
        refine (abs_add_le _ _).trans ?_
        exact add_le_add_left (abs_add_le _ _) _
    _ ≤ 3 := by linarith [hE.trans hP, hS, hpiece, hsmall]

end Work.FTS.EpsEngine
