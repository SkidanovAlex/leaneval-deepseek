/-
  Area G4b: finiteness of the non-`C¹` locus of an `Ω`-definable function of one variable.

  This is the input `nondiff_finite` consumed by `Submission/Work/WilG4bF/Asm.lean`.  The
  argument is:

  * the non-`C¹` locus is `Ω`-definable (`NondiffAux.badMem`, from `SharpDeriv`);
  * the non-differentiability locus is `Ω`-definable (from the derivative relation
    `derivRel_mem`, by projecting `DRset G`), has empty interior (`oneDim_thin`) and is
    therefore *finite* (`finite_of_interior_empty`);
  * the discontinuity locus of `deriv G` is finite (its graph is `Ω`-definable by
    `derivGraph_mem`, its points are the boundaries of the level sets of `deriv G`, which are
    finite by `SOMin.comps` and `Thin.level_mem`);
  * suppose the non-`C¹` locus contained an interval `(c,d)`.  Removing the finite union above
    leaves an interval on which `G` is differentiable everywhere and `deriv G` is continuous
    everywhere; there `G` is `C¹` (`contDiffOn_succ_iff_deriv_of_isOpen`), a contradiction.
-/
import Mathlib
import Submission.Work.Wilkies.Defs
import Submission.Work.WilG1.Basic
import Submission.Work.WilG1.Calc.finite_of_interior_empty
import Submission.Work.WilG1.OneDim.thin_assemble
import Submission.Work.WilG4b.Basic
import Submission.Work.WilG4b.nd_cont_off_finite
import Submission.Work.WilG4b.NondiffAuxAux
import Submission.Work.WilG4b.oneDim_thinAux
import Submission.Work.WilG4b.derivRel_memAux

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

open Classical
open scoped Topology

namespace Work.WilG4bF

open WilkiesDesign WilkiesDesign.CG
open Work.WilG1 Work.WilG1.OneDim

/-! ## Transport between `ℝ` and `ℝ¹ = Fin 1 → ℝ` -/

/-- The canonical homeomorphism `(Fin 1 → ℝ) ≃ₜ ℝ` (evaluation at the unique coordinate). -/
def e1 : (Fin 1 → ℝ) ≃ₜ ℝ := Homeomorph.funUnique (Fin 1) ℝ

lemma e1_apply (z : Fin 1 → ℝ) : e1 z = z 0 := by
  rw [show e1 = Homeomorph.funUnique (Fin 1) ℝ from rfl, Homeomorph.funUnique_apply]
  exact congrArg z (Subsingleton.elim default 0)

lemma liftR_eq_preimage (A : Set ℝ) : Work.WilG1.liftR A = e1 ⁻¹' A := by
  ext z
  rw [Set.mem_preimage, Work.WilG1.liftR, Set.mem_setOf_eq, e1_apply]

lemma interior_liftR_empty_iff (A : Set ℝ) :
    interior (Work.WilG1.liftR A) = ∅ ↔ interior A = ∅ := by
  rw [liftR_eq_preimage, ← Homeomorph.preimage_interior]
  constructor
  · intro h
    have himg : e1 '' (e1 ⁻¹' interior A) = interior A :=
      Set.image_preimage_eq _ e1.surjective
    rw [← himg, h, Set.image_empty]
  · intro h
    rw [h, Set.preimage_empty]

lemma finite_liftR_iff (A : Set ℝ) : (Work.WilG1.liftR A).Finite ↔ A.Finite := by
  constructor
  · intro h
    have himg : e1 '' (Work.WilG1.liftR A) = A := by
      rw [liftR_eq_preimage, Set.image_preimage_eq _ e1.surjective]
    rw [← himg]
    exact h.image _
  · intro h
    rw [liftR_eq_preimage]
    exact h.preimage (Set.injOn_of_injective e1.injective)

/-- `¬ ContDiffAt` transfers between `G` and its `ℝ¹`-model. -/
lemma not_contDiffAt_fin1_iff {G : ℝ → ℝ} {z : Fin 1 → ℝ} :
    ¬ ContDiffAt ℝ 1 (fin1 G) z ↔ ¬ ContDiffAt ℝ 1 G (z 0) :=
  not_congr (Work.WilG4b.thrContDiffAt_dinG_iff G z)

/-! ## Finiteness of the non-`C¹` locus -/

theorem nondiff_finite (S : WilkiesDesign.SOMin) (hcd : S.SharpCD) (hder : S.SharpDeriv)
    {F D : ℕ} (G : ℝ → ℝ)
    (hG : graphOf (fun x : Fin 1 → ℝ => G (x 0)) ∈ S.Ω F D 2) :
    ({t : ℝ | ¬ ContDiffAt ℝ 1 G t}).Finite := by
  classical
  -- (1) the non-`C¹` locus is `Ω`-definable
  obtain ⟨a₁, b₁, hbadMem⟩ := badMem S hder G hG
  have hA1 : Work.WilG1.liftR {x : ℝ | ¬ ContDiffAt ℝ 1 G x} ∈ S.Ω a₁ (b₁.eval D) 1 := by
    have hset : {z : Fin 1 → ℝ | ¬ ContDiffAt ℝ 1 (fin1 G) z}
        = Work.WilG1.liftR {x : ℝ | ¬ ContDiffAt ℝ 1 G x} := by
      ext z
      simp only [Set.mem_setOf_eq, Work.WilG1.liftR]
      exact not_contDiffAt_fin1_iff
    rwa [hset] at hbadMem
  -- (2) the derivative relation, and the graph of `deriv G`
  obtain ⟨K, p, hDR⟩ := derivRel_mem S G hG
  obtain ⟨K₂, p₂, hderivGraph⟩ := derivGraph_mem (S := S) hDR
  -- (3) finiteness of the discontinuity locus of `deriv G`
  have hdisc : ({x : ℝ | ¬ ContinuousAt (deriv G) x} : Set ℝ).Finite :=
    Work.WilG4b.nd_cont_off_finite S hcd (deriv G) hderivGraph
  -- (4) finiteness of the non-differentiability locus of `G`
  have hND : ({x : ℝ | ¬ DifferentiableAt ℝ G x} : Set ℝ).Finite := by
    have hproj : projLast (DRset G) ∈ S.Ω (F + K + 1) (p.eval D) 1 := S.proj hDR
    have hset : projLast (DRset G) = {z : Fin 1 → ℝ | DifferentiableAt ℝ G (z 0)} := by
      ext z
      exact mem_projLast_DRset_iff
    have hmem : Work.WilG1.liftR {x : ℝ | ¬ DifferentiableAt ℝ G x}
        ∈ S.Ω (F + K + 1 + 1) (p.eval D) 1 := by
      have hc := S.compl hproj
      rw [hset] at hc
      have hset2 : Work.WilG1.liftR {x : ℝ | ¬ DifferentiableAt ℝ G x}
          = {z : Fin 1 → ℝ | DifferentiableAt ℝ G (z 0)}ᶜ := by
        ext z
        simp [Work.WilG1.liftR]
      rw [hset2]
      exact hc
    have hthin : interior (Work.WilG1.liftR {x : ℝ | ¬ DifferentiableAt ℝ G x}) = ∅ :=
      (interior_liftR_empty_iff _).mpr (oneDim_thin (S := S) (F := F) (D := D) hcd G hG)
    exact (finite_liftR_iff _).mp (Work.WilG1.Calc.finite_of_interior_empty hmem hthin)
  -- (5) the bad locus
  set Bad : Set ℝ := {x : ℝ | ¬ DifferentiableAt ℝ G x} ∪ {x : ℝ | ¬ ContinuousAt (deriv G) x}
    with hBad
  have hfinBad : Bad.Finite := by
    rw [hBad]
    exact hND.union hdisc
  -- (6) the non-`C¹` locus has empty interior
  have hempty : interior (Work.WilG1.liftR {x : ℝ | ¬ ContDiffAt ℝ 1 G x}) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    intro z hz
    -- a ball of non-`C¹` points around the real point `e1 z`
    have hz' : e1 z ∈ interior {x : ℝ | ¬ ContDiffAt ℝ 1 G x} := by
      have h := hz
      rw [liftR_eq_preimage, ← Homeomorph.preimage_interior, Set.mem_preimage] at h
      exact h
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior _ hz'
    set c : ℝ := e1 z - ε / 2 with hc
    set d : ℝ := e1 z + ε / 2 with hd
    have hcd : c < d := by rw [hc, hd]; linarith
    have hsub : ∀ x ∈ Set.Ioo c d, ¬ ContDiffAt ℝ 1 G x := by
      intro x hx
      refine interior_subset (hball ?_)
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      rw [hc] at hx
      rw [hd] at hx
      constructor <;> linarith [hx.1, hx.2]
    -- a point of `(c,d)` outside the finite bad locus
    have hex : ∃ t ∈ Set.Ioo c d, t ∉ Bad := by
      by_contra hcon
      push_neg at hcon
      have hsub' : Set.Ioo c d ⊆ Bad := hcon
      exact not_countable_Ioo hcd (hfinBad.countable.mono hsub')
    obtain ⟨t, ht, htBad⟩ := hex
    have htBad' : t ∈ Badᶜ := htBad
    -- a neighbourhood of `t` on which `G` is differentiable and `deriv G` interactive
    obtain ⟨ρ, hρ, hρsub⟩ := Metric.isOpen_iff.mp hfinBad.isClosed.isOpen_compl t htBad'
    have htI : t ∈ Set.Ioo (t - ρ / 2) (t + ρ / 2) := ⟨by linarith, by linarith⟩
    have hballρ : ∀ x ∈ Set.Ioo (t - ρ / 2) (t + ρ / 2), x ∈ Metric.ball t ρ := by
      intro x hx
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      constructor <;> linarith [hx.1, hx.2]
    have hgood : ∀ x ∈ Set.Ioo (t - ρ / 2) (t + ρ / 2),
        DifferentiableAt ℝ G x ∧ ContinuousAt (deriv G) x := by
      intro x hx
      have hx' : x ∉ Bad := hρsub (hballρ x hx)
      simp only [hBad, Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hx'
      exact hx'
    have hdiffOn : DifferentiableOn ℝ G (Set.Ioo (t - ρ / 2) (t + ρ / 2)) :=
      fun x hx => ((hgood x hx).1).differentiableWithinAt
    have hcontOn : ContinuousOn (deriv G) (Set.Ioo (t - ρ / 2) (t + ρ / 2)) :=
      fun x hx => ((hgood x hx).2).continuousWithinAt
    have hcontDiffOn : ContDiffOn ℝ 1 G (Set.Ioo (t - ρ / 2) (t + ρ / 2)) := by
      rw [show (1 : WithTop ℕ∞) = 0 + 1 from rfl, contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioo]
      refine ⟨hdiffOn, ?_, ?_⟩
      · intro h
        exact absurd h (by simp)
      · rwa [contDiffOn_zero]
    exact hsub t ht (hcontDiffOn.contDiffAt (isOpen_Ioo.mem_nhds htI))
  -- (7) finiteness
  exact (finite_liftR_iff _).mp (Work.WilG1.Calc.finite_of_interior_empty hA1 hempty)

end Work.WilG4bF
