import Mathlib
import Submission.Work.WilG4a.Sset_explicit
import Submission.Work.WilG1.Plumb.SsetMem
import Submission.Work.WilG1.Plumb.junkPartial_mem

set_option autoImplicit false
set_option linter.unusedSimpArgs false

noncomputable section
open Classical

namespace Work.WilG4a

open WilkiesDesign

/-!
# `derivGraph_mem`

For a one-variable function `g` whose graph is `Ω F D 2`-definable, both the differentiability
locus of `g` and the graph of `deriv g` are `Ω`-definable, with a format and a degree polynomial
that are uniform in `D` (they depend only on `F`).

The differentiability locus is the projection of the `ε`-`δ` derivative set
`Work.WilG1.Plumb.Sset 1 0 f` (the set of pairs `(x,c)` with `HasDerivAt (· ↦ g ·) c x`), and the
graph of `deriv g` is the graph of the "junk partial" `Work.WilG1.junkPartial 0 f`, i.e. the union
of that derivative set with the degenerate piece `¬ differentiable × {0}` where Mathlib's `deriv`
vanishes.

The `Ω`-bookkeeping only uses `Work.WilG1.Plumb.Sset_explicit` (uniform constants for the `ε`-`δ`
derivative set) and the elementary closure lemmas of `Work.WilG1.Omega`.
-/

/-! ## 1. The derivative set in the one-variable language -/

/-- `Sset` at `N = 1`, `i = 0` and `f = (x ↦ g (x 0))` is the `ε`-`δ` derivative set of `g`. -/
lemma Sset_one_eq_epsDeriv (g : ℝ → ℝ) :
    Work.WilG1.Plumb.Sset 1 (0 : Fin 1) (fun x : Fin 1 → ℝ => g (x 0))
      = {v : Fin 2 → ℝ | Work.WilG1.Plumb.epsDeriv g (v 0) (v 1)} := by
  rw [Work.WilG1.Plumb.Sset_char]
  ext v
  show Work.WilG1.Plumb.epsDeriv
      (fun t : ℝ => (fun x : Fin 1 → ℝ => g (x 0))
        (Fin.insertNth (0 : Fin 1) t (Fin.removeNth (0 : Fin 1) (Fin.init v))))
      (Fin.init v 0) (v (Fin.last (0 + 1)))
      ↔ Work.WilG1.Plumb.epsDeriv g (v 0) (v 1)
  rw [show (fun t : ℝ => (fun x : Fin 1 → ℝ => g (x 0))
        (Fin.insertNth (0 : Fin 1) t (Fin.removeNth (0 : Fin 1) (Fin.init v)))) = g from by
    funext t
    show g ((Fin.insertNth (0 : Fin 1) t (Fin.removeNth (0 : Fin 1) (Fin.init v)) :
      Fin 1 → ℝ) 0) = g t
    rw [show (Fin.insertNth (0 : Fin 1) t (Fin.removeNth (0 : Fin 1) (Fin.init v)) :
      Fin 1 → ℝ) 0 = t from Fin.insertNth_apply_same _ _ _]]
  have h1 : (Fin.init v) 0 = v 0 := rfl
  have h2 : (Fin.last (0 + 1) : Fin 2) = 1 := rfl
  rw [h1, h2]

/-- Projecting the derivative set onto `x` gives the differentiability locus of `g`. -/
lemma projLast_epsDeriv_eq_liftR (g : ℝ → ℝ) :
    projLast {v : Fin 2 → ℝ | Work.WilG1.Plumb.epsDeriv g (v 0) (v 1)}
      = Work.WilG1.liftR {x : ℝ | DifferentiableAt ℝ g x} := by
  ext x
  rw [WilkiesDesign.projLast, Work.WilG1.liftR]
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨t, ht⟩
    have h1 : (Fin.snoc x t : Fin 2 → ℝ) 1 = t := rfl
    have h0 : (Fin.snoc x t : Fin 2 → ℝ) 0 = x 0 := rfl
    rw [h0, h1] at ht
    exact Work.WilG1.Plumb.exists_hasDerivAt_iff.mp
      ⟨t, Work.WilG1.Plumb.hasDerivAt_iff_epsDeriv.mpr ht⟩
  · intro hd
    obtain ⟨c, hc⟩ := Work.WilG1.Plumb.exists_hasDerivAt_iff.mpr hd
    refine ⟨c, ?_⟩
    show Work.WilG1.Plumb.epsDeriv g ((Fin.snoc x c : Fin 2 → ℝ) 0)
      ((Fin.snoc x c : Fin 2 → ℝ) 1)
    rw [show (Fin.snoc x c : Fin 2 → ℝ) 0 = x 0 from rfl,
      show (Fin.snoc x c : Fin 2 → ℝ) 1 = c from rfl]
    exact Work.WilG1.Plumb.hasDerivAt_iff_epsDeriv.mp hc

/-! ## 2. The junk partial of a one-variable graph is `deriv` -/

/-- In one variable (and only the last coordinate is differentiated), the junk partial is
Mathlib's `deriv`. -/
lemma junkPartial_one_apply (g : ℝ → ℝ) (z : Fin 1 → ℝ) :
    Work.WilG1.junkPartial (0 : Fin 1) (fun x : Fin 1 → ℝ => g (x 0)) z = deriv g (z 0) := by
  simp only [Work.WilG1.junkPartial]
  congr 1

/-- The graph of `deriv g` is the graph of the junk partial. -/
lemma graphOf_deriv_eq_graphOf_junkPartial (g : ℝ → ℝ) :
    WilkiesDesign.graphOf (fun x : Fin 1 → ℝ => deriv g (x 0))
      = WilkiesDesign.graphOf
          (Work.WilG1.junkPartial (0 : Fin 1) (fun x : Fin 1 → ℝ => g (x 0))) := by
  have h : (fun x : Fin 1 → ℝ => deriv g (x 0))
      = Work.WilG1.junkPartial (0 : Fin 1) (fun x : Fin 1 → ℝ => g (x 0)) := by
    funext z
    exact (junkPartial_one_apply g z).symm
  rw [h]

/-! ## 3. Uniform `Ω`-bounds -/

/-- Uniform `Ω`-bounds for the `ε`-`δ` derivative set of a one-variable definable graph. -/
theorem Sset_one_uniform (S : WilkiesDesign.SOMin) (F : ℕ) :
    ∃ (a : ℕ) (b : Polynomial ℕ), ∀ (D : ℕ) (g : ℝ → ℝ),
      WilkiesDesign.graphOf (fun x : Fin 1 → ℝ => g (x 0)) ∈ S.Ω F D 2 →
      Work.WilG1.Plumb.Sset 1 (0 : Fin 1) (fun x : Fin 1 → ℝ => g (x 0))
        ∈ S.Ω a (b.eval D) 2 :=
  ⟨Work.WilG1.Plumb.AFR 1 F + 1,
    Polynomial.C 2 * Polynomial.X + Polynomial.C (2 * Work.WilG1.Plumb.KK 1 + 1 * 4 + 80),
    fun D g hg => Sset_explicit (S := S) (N := 1) (F := F) (D := D)
      (f := fun x : Fin 1 → ℝ => g (x 0)) 0 hg⟩

/-- Uniform `Ω`-bounds for the differentiability locus of a one-variable definable graph. -/
theorem liftR_diffLocus_uniform (S : WilkiesDesign.SOMin) (F : ℕ) :
    ∃ (a : ℕ) (b : Polynomial ℕ), ∀ (D : ℕ) (g : ℝ → ℝ),
      WilkiesDesign.graphOf (fun x : Fin 1 → ℝ => g (x 0)) ∈ S.Ω F D 2 →
      Work.WilG1.liftR {x : ℝ | DifferentiableAt ℝ g x} ∈ S.Ω a (b.eval D) 1 := by
  obtain ⟨aS, bS, hSset⟩ := Sset_one_uniform S F
  refine ⟨aS + 1, bS, ?_⟩
  intro D g hg
  have hproj : projLast (Work.WilG1.Plumb.Sset 1 (0 : Fin 1) (fun x : Fin 1 → ℝ => g (x 0)))
      ∈ S.Ω (aS + 1) (bS.eval D) 1 := S.proj (hSset D g hg)
  rw [Sset_one_eq_epsDeriv g, projLast_epsDeriv_eq_liftR g] at hproj
  exact hproj

/-- Uniform `Ω`-bounds for the graph of the junk partial of a one-variable definable graph. -/
theorem junkGraph_uniform (S : WilkiesDesign.SOMin) (F : ℕ) :
    ∃ (a : ℕ) (b : Polynomial ℕ), ∀ (D : ℕ) (g : ℝ → ℝ),
      WilkiesDesign.graphOf (fun x : Fin 1 → ℝ => g (x 0)) ∈ S.Ω F D 2 →
      WilkiesDesign.graphOf
          (Work.WilG1.junkPartial (0 : Fin 1) (fun x : Fin 1 → ℝ => g (x 0)))
        ∈ S.Ω a (b.eval D) 2 := by
  obtain ⟨aS, bS, hSset⟩ := Sset_one_uniform S F
  refine ⟨max aS (max (aS + 3) 2 + 1), bS + (bS + Polynomial.C 1), ?_⟩
  intro D g hg
  have hS := hSset D g hg
  have hproj : projLast (Work.WilG1.Plumb.Sset 1 (0 : Fin 1) (fun x : Fin 1 → ℝ => g (x 0)))
      ∈ S.Ω (aS + 1) (bS.eval D) 1 := S.proj hS
  have hnot := S.compl hproj
  have hlift : {z : Fin 2 → ℝ | Fin.init z ∈
        (projLast (Work.WilG1.Plumb.Sset 1 (0 : Fin 1)
          (fun x : Fin 1 → ℝ => g (x 0))))ᶜ}
      ∈ S.Ω (aS + 3) (bS.eval D) 2 := by
    simpa using S.prod_right hnot
  have hzero : {v : Fin 2 → ℝ | v (Fin.last 1) = 0}
      ∈ S.Ω 2 ((Polynomial.C 1 : Polynomial ℕ).eval D) 2 := by
    have h := S.hyp 2 (MvPolynomial.X (Fin.last 1) : MvPolynomial (Fin 2) ℝ)
    rw [MvPolynomial.totalDegree_X] at h
    simpa using h
  have hunion := Work.WilG1.Omega.union₂ hS (Work.WilG1.Omega.inter₂ hlift hzero)
  rw [Work.WilG1.Plumb.graph_eq (0 : Fin 1) (fun x : Fin 1 → ℝ => g (x 0))]
  exact hunion

/-! ## 4. The target -/

theorem derivGraph_mem (S : WilkiesDesign.SOMin) (F : ℕ) :
    ∃ (a : ℕ) (b : Polynomial ℕ), ∀ (D : ℕ) (g : ℝ → ℝ),
      WilkiesDesign.graphOf (fun x : Fin 1 → ℝ => g (x 0)) ∈ S.Ω F D 2 →
      (Work.WilG1.liftR {x : ℝ | DifferentiableAt ℝ g x} ∈ S.Ω a (b.eval D) 1) ∧
      (WilkiesDesign.graphOf (fun x : Fin 1 → ℝ => deriv g (x 0)) ∈ S.Ω a (b.eval D) 2) := by
  obtain ⟨aL, bL, hL⟩ := liftR_diffLocus_uniform S F
  obtain ⟨aJ, bJ, hJ⟩ := junkGraph_uniform S F
  refine ⟨max aL aJ, bL + bJ, fun D g hg => ⟨?_, ?_⟩⟩
  · refine Work.WilG1.Omega.mono (hL D g hg) (le_max_left _ _) ?_
    rw [Polynomial.eval_add]
    omega
  · rw [graphOf_deriv_eq_graphOf_junkPartial g]
    refine Work.WilG1.Omega.mono (hJ D g hg) (le_max_right _ _) ?_
    rw [Polynomial.eval_add]
    omega

end Work.WilG4a
