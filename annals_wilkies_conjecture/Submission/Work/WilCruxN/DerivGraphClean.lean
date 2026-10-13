/-
  WilCruxN / `DerivGraphClean` — the order-one derivative graph is `Ω`-definable
  *without* `S.SharpDeriv`.

  `Work.WilG4b.derivGraph_mem` (`Submission/Work/WilG4b/ESet_mem.lean`) derives the
  `Ω`-definability of `derivGraph f i = {z | Fin.init z ∈ c1Loc f ∧ z (last) = dDir f i (init z)}`
  from the structure axiom `S.SharpDeriv`.  At order one that axiom is not needed: on the `C¹`
  locus the *junk* partial

  `junkP f i u = deriv (fun t => f (Function.update u i t)) (u i)`

  is the genuine directional derivative `dDir f i u` (`junkP_eq_dDir_of_contDiffAt`), and the
  junk partial is `Ω`-definable from `SharpCD` alone (`Work.WilG1.Plumb.junkPartial_mem`).
  Since the `C¹` locus is open it coincides with its interior, hence is `Ω`-definable by
  `Work.WilG4c.famContDiffAt_mem`, and intersecting the two `Ω`-sets gives the derivative graph.

  This is the *only* order-one input that the `WilCrux` node files (N4b, N4c, N4d) take from
  `SharpDeriv`; replacing their calls of `derivGraph_mem S hder` by `derivGraph_mem_clean S hcd`
  therefore removes the `hder` hypothesis from the whole flat-sheet chain.
-/
import Mathlib
import Submission.Work.WilG4b.Basic
import Submission.Work.WilG4c.JointC1LocMem
import Submission.Work.WilG1.Cell.smooth_k_cover
import Submission.Work.WilG1.Cell.JunkDefs
import Submission.Work.WilG4c.BadLocusThin

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilCruxN

open WilkiesDesign

/-! ## 0. The `C¹` locus is the `ContDiffAt` set -/

/-- `c1Loc f` is the set of points at which `f` is `C¹` (its defining `interior` is redundant,
the `C¹` locus being open). -/
theorem c1Loc_eq_contDiffAt_set {n : ℕ} (f : (Fin n → ℝ) → ℝ) :
    Work.WilG4b.c1Loc f = {z : Fin n → ℝ | ContDiffAt ℝ 1 f z} := by
  have hopen : IsOpen {z : Fin n → ℝ | ContDiffAt ℝ 1 f z} :=
    Work.WilkG4c.isOpen_contDiffAt_set (k := 1) f
  rw [Work.WilG4b.c1Loc, hopen.interior_eq]

/-! ## 1. The junk partial is the directional derivative on the `C¹` locus -/

/-- The curve `t ↦ Function.update u i t` has derivative `Pi.single i 1` at `t = u i`. -/
theorem hasDerivAt_update {m : ℕ} (u : Fin m → ℝ) (i : Fin m) :
    HasDerivAt (fun t : ℝ => Function.update u i t) (Pi.single i (1 : ℝ) : Fin m → ℝ)
      (u i) := by
  have hfun : (fun t : ℝ => Function.update u i t)
      = fun t : ℝ => u + (t - u i) • (Pi.single i (1 : ℝ) : Fin m → ℝ) := by
    funext t
    funext k
    rcases eq_or_ne k i with rfl | hk
    · rw [Function.update_self, Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul,
        mul_one]
      ring
    · rw [Function.update_of_ne hk, Pi.add_apply, Pi.smul_apply, Pi.single_eq_of_ne hk,
        smul_eq_mul, mul_zero, add_zero]
  rw [hfun]
  have h := ((hasDerivAt_id (u i)).sub_const (u i)).smul_const
    (Pi.single i (1 : ℝ) : Fin m → ℝ)
  simpa using h.const_add u

/-- **On the `C¹` locus the junk partial is the genuine directional derivative.** -/
theorem junkP_eq_dDir_of_contDiffAt {m : ℕ} (f : (Fin m → ℝ) → ℝ) (i : Fin m)
    {u : Fin m → ℝ} (hu : ContDiffAt ℝ 1 f u) :
    Work.WilG1.Cell.junkP f i u = Work.WilG4b.dDir f i u := by
  have hd : DifferentiableAt ℝ f u := hu.differentiableAt (by simp)
  have hcurve := hasDerivAt_update u i
  have hpt : (fun t : ℝ => Function.update u i t) (u i) = u := by
    simp [Function.update_eq_self]
  have hcomp : HasDerivAt (f ∘ fun t : ℝ => Function.update u i t)
      (fderiv ℝ f u (Pi.single i (1 : ℝ))) (u i) := by
    have hf' : HasFDerivAt f (fderiv ℝ f u) ((fun t : ℝ => Function.update u i t) (u i)) := by
      rw [hpt]
      exact hd.hasFDerivAt
    exact hf'.comp_hasDerivAt (u i) hcurve
  change deriv (fun t : ℝ => f (Function.update u i t)) (u i) = fderiv ℝ f u (Pi.single i 1)
  simpa [Function.comp_def] using hcomp.deriv

/-! ## 2. The order-one derivative graph is `Ω`-definable from `SharpCD` alone -/

/-- **`derivGraph` is `Ω`-definable without `SharpDeriv`.**  For a function `f : ℝ^m → ℝ` with
`Ω`-definable graph in format `F0` and degree `D`, the graph of the directional derivative
`∂ᵢ f`, taken over the `C¹` locus, is `Ω`-definable with a format independent of `D` and a
degree bounded by `b.eval D`.

Compare `Work.WilG4b.derivGraph_mem`, which derives the same conclusion from the structure
axiom `SharpDeriv`; here only `SharpCD` is used, through the junk partial
`Work.WilG1.Plumb.junkPartial_mem`. -/
theorem derivGraph_mem_clean (S : WilkiesDesign.SOMin) (hcd : S.SharpCD) {m F0 D : ℕ}
    (f : (Fin m → ℝ) → ℝ) (i : Fin m)
    (hf : WilkiesDesign.graphOf f ∈ S.Ω F0 D (m + 1)) :
    ∃ (a : ℕ) (b : Polynomial ℕ),
      Work.WilG4b.derivGraph f i ∈ S.Ω a (b.eval D) (m + 1) := by
  rcases m with _ | n
  · exact i.elim0
  · -- `m = n + 1`
    obtain ⟨a₁, b₁, hL⟩ := Work.WilG4c.famContDiffAt_mem S hcd (n + 1) F0
    have hloc : {z : Fin (n + 1) → ℝ | ContDiffAt ℝ 1 f z} ∈ S.Ω a₁ (b₁.eval D) (n + 1) :=
      hL D f (by simpa using hf)
    have hlift : {z : Fin ((n + 1) + 1) → ℝ | Fin.init z ∈
        {z : Fin (n + 1) → ℝ | ContDiffAt ℝ 1 f z}} ∈ S.Ω (a₁ + 1) (b₁.eval D) ((n + 1) + 1) :=
      S.prod_right hloc
    -- the junk partial is `Ω`-definable
    obtain ⟨aj, bj, hj⟩ :=
      Work.WilG1.Plumb.junkPartial_mem (S := S) (n := n) (F := F0) (D := D) i f
        (by simpa using hf)
    have hjp : WilkiesDesign.graphOf (Work.WilG1.Cell.junkP f i) ∈
        S.Ω aj (bj.eval D) ((n + 1) + 1) := by
      rw [Work.WilG1.Cell.junkP_eq_junkPartial]
      exact hj
    -- the intersection
    have hinter := Work.WilG1.Omega.inter₂
      (Y := WilkiesDesign.graphOf (Work.WilG1.Cell.junkP f i)) hlift hjp
    refine ⟨max (a₁ + 1) aj + 1, b₁ + bj, ?_⟩
    have hset : Work.WilG4b.derivGraph f i =
        ({z : Fin ((n + 1) + 1) → ℝ | Fin.init z ∈
            {z : Fin (n + 1) → ℝ | ContDiffAt ℝ 1 f z}} ∩
          WilkiesDesign.graphOf (Work.WilG1.Cell.junkP f i)) := by
      ext z
      constructor
      · intro hz
        rw [Work.WilG4b.derivGraph] at hz
        obtain ⟨hz1, hz2⟩ := hz
        have hc : Fin.init z ∈ {z : Fin (n + 1) → ℝ | ContDiffAt ℝ 1 f z} := by
          rwa [c1Loc_eq_contDiffAt_set f] at hz1
        refine ⟨hc, ?_⟩
        rw [WilkiesDesign.graphOf]
        exact hz2.trans (junkP_eq_dDir_of_contDiffAt f i hc).symm
      · intro hz
        have hc : ContDiffAt ℝ 1 f (Fin.init z) := hz.1
        have hg : z (Fin.last (n + 1)) = Work.WilG1.Cell.junkP f i (Fin.init z) := hz.2
        rw [Work.WilG4b.derivGraph]
        refine ⟨?_, ?_⟩
        · rw [c1Loc_eq_contDiffAt_set f]
          exact hc
        · exact hg.trans (junkP_eq_dDir_of_contDiffAt f i hc)
    rw [hset]
    exact hinter

end Work.WilCruxN
