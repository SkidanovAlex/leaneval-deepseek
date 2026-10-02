import Submission.Work.ThomBordism.assembly
import Submission.Work.ThomBordism.smooth8Fundamental
import Submission.Work.ThomBordism.boundarySigmaWiring
import Submission.Work.ThomBordism.degenerateFamily

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The assembly of `Work.Drive.ThomRational` from the *connected*-family transversality core

Project lead's decision on the connectivity gap (probe round 14): carry connectedness.  The local
degree of TUBULAR (`Work.Tubular.exists_localDegree_at_collapseRelK8_of_connected`) needs
`[ConnectedSpace V.pt]`, so the producers of the tubular data carry the hypothesis
`(∀ i, ConnectedSpace (F i).pt)`; the chapter's transversality core must therefore be consumed in the
restricted form

  `Work.ThomBordism.TransversalityCoreFamilyConn`
    `∀ ι F, (∀ i, ConnectedSpace (F i).pt) → (∑ p₁² = 0) → (∑ p₂ = 0) → ∃ N > 0, Nonempty (NullBordismFamily (Fin N × ι) F)`

(`Interface.lean`).

This file proves that the restricted form **suffices** for the target, i.e.

  `Work.ThomBordism.thomRational_of_transversalityCoreConn :
     TransversalityCoreFamilyConn → BoundarySigma → Smooth8Fundamental → Work.Drive.ThomRational`

and the convenience form `thomRational_of_conn` with the two proved inputs
(`boundarySigma_of_maximalIsotropic boundaryMaximalIsotropic`, `smooth8Fundamental`) instantiated.

The point of the proof is the *discharge of the connectivity hypothesis* at the one place where
`Work.Drive.Smooth8` members become `Man8`s.  The assembly of `assembly.lean` replaced a degenerate
`Smooth8` (one whose class vanishes) by `Man8.empty`, which is *not* connected, so it cannot be used
here: instead the degenerate indices are **dropped** from the family.  That is harmless because such
a manifold has vanishing numbers (`Work.ThomBordism.Smooth8_sigma_eq_zero_of_c_eq_zero` and friends),
so the two sums are unchanged (`sum_drop_degenerate` below, on top of
`Work.ThomBordism.Finset.sum_subtype_eq_sum_of_eq_zero`).  The remaining members are the manifolds
`M i` themselves (`c ≠ 0`), which are connected because `Work.Drive.Smooth8` carries
`ConnectedSpace`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

attribute [local instance] Classical.propDecidable

open CategoryTheory AlgebraicTopology
open scoped Manifold ContDiff

namespace Work.ThomBordism

noncomputable section

/-- **The connectivity of a non-degenerate `Smooth8`-as-`Man8`**: for `M : Work.Drive.Smooth8` with
`M.c ≠ 0`, the manifold `Man8.ofSmooth8 M …` *is* `M`, hence connected.  (Contrapositively,
`M.c = 0` is exactly the degenerate case that the assembly below drops; `Man8.empty` is not
connected, which is why the dropping is necessary.) -/
theorem connectedSpace_ofSmooth8 (hfund : Smooth8Fundamental) (M : Work.Drive.Smooth8)
    (h : M.c ≠ 0) : ConnectedSpace (Man8.ofSmooth8 M (hfund M h)).pt :=
  (inferInstance : ConnectedSpace M.pt)

/-- **Connectivity of an `if`-conditional oriented manifold.**

The `if` cannot be rewritten *inside* the goal `ConnectedSpace (if c then A else B).pt`: the
topology instance `(if c then A else B).topologicalSpace` depends on the conditional, so `rw`/`simp`
report "motive is not type correct" / "made no progress".  Transport along the equality of the
manifolds instead (`Eq.mpr` of `congrArg …`).  (`Man8.neg` needs no such transport: its point type is
the same by `rfl`.) -/
theorem connectedSpace_ite {c : Prop} [Decidable c] {A B : Man8}
    (hA : ConnectedSpace A.pt) (hB : ConnectedSpace B.pt) :
    ConnectedSpace (if c then A else B).pt := by
  by_cases h : c
  · exact Eq.mpr (congrArg (fun M : Man8 => ConnectedSpace M.pt) (if_pos h)) hA
  · exact Eq.mpr (congrArg (fun M : Man8 => ConnectedSpace M.pt) (if_neg h)) hB

/-- **Dropping the degenerate members of a `Smooth8`-family does not change a weighted sum**: the
terms with vanishing class vanish. -/
theorem sum_drop_degenerate {n : ℕ} (M : Fin n → Work.Drive.Smooth8) (w : Fin n → ℤ)
    (f : Work.Drive.Smooth8 → ℤ) (hf : ∀ M, M.c = 0 → f M = 0) :
    (∑ i : {i : Fin n // (M i).c ≠ 0}, w i.1 * f (M i.1)) = ∑ i, w i * f (M i) := by
  rw [Finset.sum_subtype_eq_sum_of_eq_zero (fun i => (M i).c ≠ 0)
    (fun i => w i * f (M i))]
  intro i hi
  rw [hf (M i) (not_not.mp hi), mul_zero]

/-- **The target from the connected-family transversality core.**

Given `TransversalityCoreFamilyConn`, the proved `BoundarySigma` and the proved
`Smooth8Fundamental`, `Work.Drive.ThomRational` follows.  The argument is the arithmetic of
`assembly.lean` with the family of signed copies built from the *non-degenerate* indices only, so
that all its members are connected (`smooth8ToMan8`-connectivity). -/
theorem thomRational_of_transversalityCoreConn (hT : TransversalityCoreFamilyConn)
    (hσ : BoundarySigma) (hfund : Smooth8Fundamental) : Work.Drive.ThomRational := by
  intro n M w h1 h2
  classical
  -- the family of signed copies of the non-degenerate members, indexed by the manifold itself
  set F : (Σ i : {i : Fin n // (M i).c ≠ 0}, Fin (w i.1).natAbs) → Man8 :=
    fun j => (if 0 < w j.1.1 then Man8.ofSmooth8 (M j.1.1) (hfund (M j.1.1) j.1.2)
      else (Man8.ofSmooth8 (M j.1.1) (hfund (M j.1.1) j.1.2)).neg) with hFdef
  have hconn : ∀ j, ConnectedSpace (F j).pt := by
    intro j
    have hFj : F j = (if 0 < w j.1.1 then Man8.ofSmooth8 (M j.1.1) (hfund (M j.1.1) j.1.2)
        else (Man8.ofSmooth8 (M j.1.1) (hfund (M j.1.1) j.1.2)).neg) := rfl
    refine Eq.mpr (congrArg (fun M : Man8 => ConnectedSpace M.pt) hFj) ?_
    exact connectedSpace_ite (connectedSpace_ofSmooth8 hfund (M j.1.1) j.1.2)
      (connectedSpace_ofSmooth8 hfund (M j.1.1) j.1.2)
  have hsum1 : (∑ j, (F j).p1Sq) = ∑ i : {i : Fin n // (M i).c ≠ 0},
      w i.1 * (M i.1).p1Sq := by
    rw [Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hFdef]
    exact sum_signedCopies (fun W => W.p1Sq) (fun W => W.neg_p1Sq)
      (Man8.ofSmooth8 (M i.1) (hfund (M i.1) i.2)) (w i.1)
  have hsum2 : (∑ j, (F j).p2Num) = ∑ i : {i : Fin n // (M i).c ≠ 0},
      w i.1 * (M i.1).p2Num := by
    rw [Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hFdef]
    exact sum_signedCopies (fun W => W.p2Num) (fun W => W.neg_p2Num)
      (Man8.ofSmooth8 (M i.1) (hfund (M i.1) i.2)) (w i.1)
  have hp1 : (∑ j, (F j).p1Sq) = 0 := by
    rw [hsum1, sum_drop_degenerate M w (fun M => M.p1Sq)
      (fun M hM => Smooth8_p1Sq_eq_zero_of_c_eq_zero M hM)]
    exact h1
  have hp2 : (∑ j, (F j).p2Num) = 0 := by
    rw [hsum2, sum_drop_degenerate M w (fun M => M.p2Num)
      (fun M hM => Smooth8_p2Num_eq_zero_of_c_eq_zero M hM)]
    exact h2
  obtain ⟨N, hN, ⟨W⟩⟩ := hT _ F hconn hp1 hp2
  -- bordism invariance of σ for the reduced family
  have h0 := hσ (Fin N × (Σ i : {i : Fin n // (M i).c ≠ 0}, Fin (w i.1).natAbs))
    (fun k => F k.2) W
  have h0' : (N : ℤ) * (∑ j, (F j).sigma) = 0 := by
    rw [← sum_prod_family N (Σ i : {i : Fin n // (M i).c ≠ 0}, Fin (w i.1).natAbs)
      (fun j => (F j).sigma)]
    exact h0
  have hN' : (N : ℤ) ≠ 0 := by exact_mod_cast hN.ne'
  have hfam : (∑ j, (F j).sigma) = 0 := (mul_eq_zero.mp h0').resolve_left hN'
  have hsum3 : (∑ j, (F j).sigma) = ∑ i : {i : Fin n // (M i).c ≠ 0},
      w i.1 * (M i.1).sigma := by
    rw [Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hFdef]
    exact sum_signedCopies (fun W => W.sigma) (fun W => W.neg_sigma)
      (Man8.ofSmooth8 (M i.1) (hfund (M i.1) i.2)) (w i.1)
  rw [hsum3] at hfam
  rw [sum_drop_degenerate M w (fun M => M.sigma)
    (fun M hM => Smooth8_sigma_eq_zero_of_c_eq_zero M hM)] at hfam
  exact hfam

/-- **`Work.Drive.ThomRational` from the connected-family transversality core alone** (the two
proved inputs — bordism invariance of the signature and the local-generator lemma — instantiated).
This is the consumer-facing form of the chapter: a producer supplies
`Work.ThomBordism.TransversalityCoreFamilyConn`, which is what the tubular data with the
`(∀ i, ConnectedSpace (F i).pt)` hypothesis gives. -/
theorem thomRational_of_conn (hT : TransversalityCoreFamilyConn) : Work.Drive.ThomRational :=
  thomRational_of_transversalityCoreConn hT
    (boundarySigma_of_maximalIsotropic boundaryMaximalIsotropic) smooth8Fundamental

end

end Work.ThomBordism
