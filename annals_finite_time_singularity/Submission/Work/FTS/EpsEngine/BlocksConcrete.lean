/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/EpsEngine/BlocksConcrete.lean` — the three `EpsDecay` block slots, with the
# pointwise extraction **instantiated**

The three slot assemblies (`EpsEngine/Rop_block_abs_le_one`, `EpsEngine/uop_slot_abs_le_three`,
`EpsEngine/vop_slot_abs_le_three`) take two kinds of inputs:

* the pointwise extraction `hpt` of the `HQo α 4` data (`|D_z^bD_θ^a g z θ| ≤ Cpt·min z 1·HkNorm α 4 g`
  for `a + b ≤ 2`) — now **instantiated** here from the proved
  `Work.FTS_RegExport.RXT.hkMem_pointwise_min` (no boundary traces needed);
* the two piece bounds — now produced here from `EllPkgGo` (fields `R`, `U`, `V`) and `StarPkgo2`
  (fields `R`, `UsW`, `V`) through `star_Rop_le`, `star_Uop_div_le`, `star_Vop_le`.

The result is one theorem per slot of the form `∃ K ≥ 0, <smallness in K> → |slot| ≤ C`, with the
constant `K` that of `hkMem_pointwise_min`; the smallness is a threshold in `(α, C₀, Ce, Cs)` that
the restated target's `α₄` absorbs.

Everything here is `sorry`-free.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS_RegExport.RXT.hkMem_pointwise_min
import Submission.Work.FTS.EpsEngine.Rop_block_abs_le_one
import Submission.Work.FTS.EpsEngine.EllRopLe
import Submission.Work.FTS.EpsEngine.StarRopLe
import Submission.Work.FTS.EpsEngine.star_Uop_div_le
import Submission.Work.FTS.EpsEngine.UopSlot
import Submission.Work.FTS.EpsEngine.VopSlot

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

/-- **The pointwise extraction `hpt`, instantiated** from the proved
`Work.FTS_RegExport.RXT.hkMem_pointwise_min`
(`|D_z^bD_θ^a g z θ| ≤ C·min z 1·HkNorm α 4 g` for `a + b ≤ 2`, from `ContDiffOn ℝ 4` on the open
quadrant and `ℋ⁴`-honesty alone — in particular with **no** boundary-trace hypothesis). -/
theorem hpt_of_hkMem_pointwise_min {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    ∃ Cpt : ℝ, 0 ≤ Cpt ∧ ∀ g : Fn,
      ContDiffOn ℝ 4 (Function.uncurry g) Work.FTS.EllipticEst.Q0 →
      Work.Spaces.HkMem α 4 g → ∀ b a : ℕ, a + b ≤ 2 → ∀ z θ : ℝ, 0 < z → 0 < θ →
        θ < Real.pi / 2 →
        |Work.Spaces.mixed b a g z θ| ≤ Cpt * min z 1 * Work.Spaces.HkNorm α 4 g := by
  obtain ⟨C, hC0, hC⟩ := Work.FTS_RegExport.RXT.hkMem_pointwise_min (α := α) hα hα1
  exact ⟨C, hC0, fun g h4 hmem b a hab z θ hz hθ0 hθ1 =>
    hC g h4 hmem b a hab z θ hz hθ0 hθ1⟩

/-- **The `Rop` slot of `EpsDecay`, with everything instantiated.** -/
theorem Rop_slot_concrete {α Ce Cs : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hCe : 0 ≤ Ce) (hCs : 0 ≤ Cs) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (C₀ : ℝ), 0 ≤ C₀ → ∀ {f Φs : Fn} {E : Fn → Fn} {z θ : ℝ},
      0 < z → θ ∈ Set.Ioo 0 (Real.pi / 2) → K * (Ce * (C₀ * α ^ 2)) + Cs * α ≤ 1 / 4 →
      Work.FTS.ClassC.ClassC α f → Work.FTS.Nonlin.Xn α f ≤ C₀ * α ^ 2 →
      (∀ u : Fn, Work.FTS.ClassC.ClassC α u →
        Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u)) →
      Work.FTS.VocabO2.StarPkgo2 α Cs Φs →
      (Work.Construction.Rop α (Work.Construction.PhiTil α f
          (fun z θ => Φs z θ + E f z θ)) z θ
        = Work.Construction.Rop α (Work.Construction.PhiTil α f (E f)) z θ
          + Work.Construction.Rop α (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs)
              z θ
          + Work.Construction.Rop α (Work.Construction.Theta α (Work.Construction.Fstar α)) z θ) →
      |Work.Construction.Rop α (Work.Construction.PhiTil α f
        (fun z θ => Φs z θ + E f z θ)) z θ| ≤ 1 := by
  obtain ⟨Cpt, hCpt0, hpt⟩ := hpt_of_hkMem_pointwise_min (α := α) hα hα1
  refine ⟨Cpt, hCpt0, fun C₀ hC₀ f Φs E z θ hz hθ hsmall hf hball hEll hstar hdec => ?_⟩
  have hE := ell_Rop_le (α := α) (Ce := Ce) (Cpt := Cpt) hα hα1 hCpt0 hpt hf hEll hz hθ
  have hE' : |Work.Construction.Rop α (Work.Construction.PhiTil α f (E f)) z θ|
      ≤ Cpt * (Ce * (C₀ * α ^ 2)) * min z 1 := by
    refine hE.trans ?_
    have h1 : Ce * Work.FTS.Nonlin.Xn α f ≤ Ce * (C₀ * α ^ 2) :=
      mul_le_mul_of_nonneg_left hball hCe
    have h2 : 0 ≤ Cpt * min z 1 := by positivity
    have h3 : Cpt * (Ce * Work.FTS.Nonlin.Xn α f) * min z 1
        ≤ Cpt * (Ce * (C₀ * α ^ 2)) * min z 1 := by
      refine mul_le_mul_of_nonneg_right ?_ (le_min hz.le zero_le_one)
      exact mul_le_mul_of_nonneg_left h1 hCpt0
    linarith
  exact Rop_block_abs_le_one (α := α) (Cpt := Cpt) (Ce := Ce) (Cs := Cs) (C₀ := C₀)
    hα hα1 hz hθ hCpt0 hCe hCs hC₀ hsmall hdec hE'
    (star_Rop_le (α := α) (Cs := Cs) hstar z θ hz hθ.1 hθ.2)

/-- **The `Uop/sin 2θ` slot of `EpsDecay`, with everything instantiated.** -/
theorem Uop_slot_concrete {α Ce Cs : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hCe : 0 ≤ Ce) (hCs : 0 ≤ Cs) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (C₀ : ℝ), 0 ≤ C₀ → ∀ {f Φs : Fn} {E : Fn → Fn} {z θ : ℝ},
      0 < z → θ ∈ Set.Ioo 0 (Real.pi / 2) → K * (Ce * (C₀ * α ^ 2)) + Cs * α ≤ 1 →
      Work.FTS.ClassC.ClassC α f → Work.FTS.Nonlin.Xn α f ≤ C₀ * α ^ 2 →
      (∀ u : Fn, Work.FTS.ClassC.ClassC α u →
        Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u)) →
      Work.FTS.VocabO2.StarPkgo2 α Cs Φs →
      (Work.Construction.Uop α (Work.Construction.PhiTil α f
          (fun z θ => Φs z θ + E f z θ)) z θ / Work.Construction.s2 θ
        = Work.Construction.Uop α (Work.Construction.PhiTil α f (E f)) z θ
            / Work.Construction.s2 θ
          + Work.Construction.Uop α (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs)
              z θ / Work.Construction.s2 θ
          + Work.Construction.Uop α (Work.Construction.Theta α (Work.Construction.Fstar α))
              z θ / Work.Construction.s2 θ) →
      |Work.Construction.Uop α (Work.Construction.PhiTil α f
        (fun z θ => Φs z θ + E f z θ)) z θ / Work.Construction.s2 θ| ≤ 3 := by
  obtain ⟨Cpt, hCpt0, hpt⟩ := hpt_of_hkMem_pointwise_min (α := α) hα hα1
  refine ⟨Cpt, hCpt0, fun C₀ hC₀ f Φs E z θ hz hθ hsmall hf hball hEll hstar hdec => ?_⟩
  have hE := ell_Uop_le (α := α) (Ce := Ce) (Cpt := Cpt) hα hα1 hCpt0 hpt hf hEll hz hθ
  have hE' : |Work.Construction.Uop α (Work.Construction.PhiTil α f (E f)) z θ
      / Work.Construction.s2 θ| ≤ Cpt * (Ce * (C₀ * α ^ 2)) * min z 1 := by
    refine hE.trans ?_
    have h1 : Ce * Work.FTS.Nonlin.Xn α f ≤ Ce * (C₀ * α ^ 2) :=
      mul_le_mul_of_nonneg_left hball hCe
    have h3 : Cpt * (Ce * Work.FTS.Nonlin.Xn α f) * min z 1
        ≤ Cpt * (Ce * (C₀ * α ^ 2)) * min z 1 := by
      refine mul_le_mul_of_nonneg_right ?_ (le_min hz.le zero_le_one)
      exact mul_le_mul_of_nonneg_left h1 hCpt0
    linarith
  exact uop_slot_abs_le_three (α := α) (Cpt := Cpt) (Ce := Ce) (Cs := Cs) (C₀ := C₀)
    hα hα1 hz hθ hCpt0 hCe hCs hC₀ hsmall hdec hE'
    (star_Uop_div_le (α := α) (Cs := Cs) hα hCs hstar z θ hz hθ.1 hθ.2)

/-- **The `Vop` slot of `EpsDecay`, with everything instantiated.** -/
theorem Vop_slot_concrete {α Ce Cs : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hCe : 0 ≤ Ce) (hCs : 0 ≤ Cs) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (C₀ : ℝ), 0 ≤ C₀ → ∀ {f Φs : Fn} {E : Fn → Fn} {z θ : ℝ},
      0 < z → θ ∈ Set.Ioo 0 (Real.pi / 2) → K * (Ce * (C₀ * α ^ 2)) + Cs * α ≤ 1 →
      Work.FTS.ClassC.ClassC α f → Work.FTS.Nonlin.Xn α f ≤ C₀ * α ^ 2 →
      (∀ u : Fn, Work.FTS.ClassC.ClassC α u →
        Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u)) →
      Work.FTS.VocabO2.StarPkgo2 α Cs Φs →
      (Work.Construction.Vop (Work.Construction.PhiTil α f
          (fun z θ => Φs z θ + E f z θ)) z θ
        = Work.Construction.Vop (Work.Construction.PhiTil α f (E f)) z θ
          + Work.Construction.Vop (Work.Construction.PhiTil α (Work.Construction.Fstar α) Φs)
              z θ
          + Work.Construction.Vop (Work.Construction.Theta α (Work.Construction.Fstar α)) z θ) →
      |Work.Construction.Vop (Work.Construction.PhiTil α f
        (fun z θ => Φs z θ + E f z θ)) z θ| ≤ 3 := by
  obtain ⟨Cpt, hCpt0, hpt⟩ := hpt_of_hkMem_pointwise_min (α := α) hα hα1
  refine ⟨Cpt, hCpt0, fun C₀ hC₀ f Φs E z θ hz hθ hsmall hf hball hEll hstar hdec => ?_⟩
  have hE := ell_Vop_le (α := α) (Ce := Ce) (Cpt := Cpt) hα hα1 hCpt0 hpt hf hEll hz hθ
  have hE' : |Work.Construction.Vop (Work.Construction.PhiTil α f (E f)) z θ|
      ≤ Cpt * (Ce * (C₀ * α ^ 2)) * min z 1 := by
    refine hE.trans ?_
    have h1 : Ce * Work.FTS.Nonlin.Xn α f ≤ Ce * (C₀ * α ^ 2) :=
      mul_le_mul_of_nonneg_left hball hCe
    have h3 : Cpt * (Ce * Work.FTS.Nonlin.Xn α f) * min z 1
        ≤ Cpt * (Ce * (C₀ * α ^ 2)) * min z 1 := by
      refine mul_le_mul_of_nonneg_right ?_ (le_min hz.le zero_le_one)
      exact mul_le_mul_of_nonneg_left h1 hCpt0
    linarith
  exact vop_slot_abs_le_three (α := α) (Cpt := Cpt) (Ce := Ce) (Cs := Cs) (C₀ := C₀)
    hα hα1 hz hθ hCpt0 hCe hCs hC₀ hsmall hdec hE'
    (star_Vop_le (α := α) (Cs := Cs) hstar z θ hz hθ.1 hθ.2)

end Work.FTS.EpsEngine
