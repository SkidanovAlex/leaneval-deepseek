/-
  WilG4a / CD / `oneDim_Cj_locus_mem`.

  For a function `g : ℝ → ℝ` whose graph is `Ω F0 D 2`-definable in a sharply o-minimal
  structure `S` with sharp derivatives, the `C^j`-locus of `g` is `Ω`-definable, with format
  depending only on `F0` and degree a polynomial in `D` and `j`.

  The point is that `ContDiffAt ℝ j g ·` is an *open* condition, so the `C^j`-locus of `g`
  coincides with its interior — and that interior is `smoothLocus` of the (constant) one-parameter
  family `fun _ x => g x`, which `SharpDeriv` exhibits as an `Ω`-set (`smoothLocus_mem` with
  `p = 0`).
-/
import Mathlib
import Submission.Work.Wilkies.Defs
import Submission.Work.WilG1.OneDim.Defs
import Submission.Work.WilG4a.Cells

set_option autoImplicit false
noncomputable section
open Classical
open scoped ContDiff

namespace Work.WilG4a.CD

open WilkiesDesign WilkiesConjecture
open Work.WilG1

/-! ## The `C^j` locus is open, and `ContDiffAt` is stable under the identification
`Fin 1 → ℝ ≃ ℝ` -/

/-- The set of points at which `g` is `C^j` is open: `C^j`-ness is a local condition. -/
theorem isOpen_contDiffAt_locus (g : ℝ → ℝ) (j : ℕ) :
    IsOpen {x : ℝ | ContDiffAt ℝ j g x} := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  have hx' : ContDiffAt ℝ j g x := hx
  exact hx'.eventually (by simp)

/-- `ContDiffAt` is unaffected by reading a one-variable function as a function on the
one-point space `Fin 1 → ℝ` (coordinates `z ↦ z 0`): the two spaces are linearly
homeomorphic, so smoothness at a point is the same. -/
theorem contDiffAt_fin1_comp (g : ℝ → ℝ) (j : ℕ) (z : Fin 1 → ℝ) :
    ContDiffAt ℝ j (fun z : Fin 1 → ℝ => g (z 0)) z ↔ ContDiffAt ℝ j g (z 0) := by
  let e : (Fin 1 → ℝ) ≃L[ℝ] ℝ := ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ
  have he : ⇑e = fun w : Fin 1 → ℝ => w 0 := by
    simp only [e]
    rw [ContinuousLinearEquiv.coe_funUnique]
    funext w
    simp
  have hz : e z = z 0 := by rw [he]
  have h := ContinuousLinearEquiv.contDiffAt_comp_iff (e := e) (f := g) (n := (j : ℕ∞ω))
    (x := z 0)
  rw [show e.symm (z 0) = z by rw [← hz, ContinuousLinearEquiv.symm_apply_apply]] at h
  rwa [show (g ∘ ⇑e) = fun z : Fin 1 → ℝ => g (z 0) by
    funext w
    rw [Function.comp_apply, he]] at h

/-- The `C^j`-locus of `g`, read in `Fin 1 → ℝ`, is the pointwise `C^j`-locus of `z ↦ g (z 0)`. -/
theorem liftR_contDiffAt_eq (g : ℝ → ℝ) (j : ℕ) :
    liftR {x : ℝ | ContDiffAt ℝ j g x}
      = {z : Fin 1 → ℝ | ContDiffAt ℝ j (fun z : Fin 1 → ℝ => g (z 0)) z} := by
  ext z
  simp only [liftR, Set.mem_ofPred_eq]
  exact (contDiffAt_fin1_comp g j z).symm

/-- The `C^j`-locus of `g` is open, hence equal to the interior of its reading in `Fin 1 → ℝ`. -/
theorem liftR_contDiffAt_interior (g : ℝ → ℝ) (j : ℕ) :
    liftR {x : ℝ | ContDiffAt ℝ j g x}
      = interior {z : Fin 1 → ℝ | ContDiffAt ℝ j (fun z : Fin 1 → ℝ => g (z 0)) z} := by
  have hopen : IsOpen (liftR {x : ℝ | ContDiffAt ℝ j g x}) := by
    have hpre : liftR {x : ℝ | ContDiffAt ℝ j g x}
        = (fun z : Fin 1 → ℝ => z 0) ⁻¹' {x : ℝ | ContDiffAt ℝ j g x} := rfl
    rw [hpre]
    exact IsOpen.preimage (continuous_apply 0) (isOpen_contDiffAt_locus g j)
  have h2 : IsOpen {z : Fin 1 → ℝ | ContDiffAt ℝ j (fun z : Fin 1 → ℝ => g (z 0)) z} := by
    rw [← liftR_contDiffAt_eq]
    exact hopen
  rw [liftR_contDiffAt_eq]
  exact h2.interior_eq.symm

/-! ## The main statement -/

theorem oneDim_Cj_locus_mem (S : WilkiesDesign.SOMin) (hder : S.SharpDeriv) (F0 : ℕ) :
    ∃ (a : ℕ) (b : MvPolynomial (Fin 2) ℕ),
      ∀ (D j : ℕ) (g : ℝ → ℝ),
        WilkiesDesign.graphOf (fun x : Fin 1 → ℝ => g (x 0)) ∈ S.Ω F0 D 2 →
        Work.WilG1.liftR {x : ℝ | ContDiffAt ℝ j g x} ∈
          S.Ω a (MvPolynomial.eval ![D, j] b) 1 := by
  obtain ⟨a, b, hb⟩ := Work.WilG4a.smoothLocus_mem S hder 0 F0
  refine ⟨a, b, ?_⟩
  intro D j g hg
  set f : (Fin 0 → ℝ) → ℝ → ℝ := fun _ x => g x with hf
  have hfam : famFun f = fun z : Fin 1 → ℝ => g (z 0) := by
    funext z
    simp only [famFun, hf]
    rw [show Fin.last 0 = (0 : Fin 1) from Fin.ext rfl]
  have hgraph : graphFam f ∈ S.Ω F0 D 2 := by
    rw [show graphFam f = graphOf (fun z : Fin 1 → ℝ => g (z 0)) from by
      rw [← graphOf_famFun f, hfam]]
    exact hg
  have h := hb D j hgraph
  have hset : smoothLocus f j = liftR {x : ℝ | ContDiffAt ℝ j g x} := by
    have h2 : IsOpen {z : Fin 1 → ℝ | ContDiffAt ℝ j (fun z : Fin 1 → ℝ => g (z 0)) z} := by
      rw [← liftR_contDiffAt_eq]
      exact IsOpen.preimage (continuous_apply 0) (isOpen_contDiffAt_locus g j)
    unfold smoothLocus
    rw [hfam]
    rw [liftR_contDiffAt_eq]
    exact h2.interior_eq
  rw [hset] at h
  exact h

end Work.WilG4a.CD
