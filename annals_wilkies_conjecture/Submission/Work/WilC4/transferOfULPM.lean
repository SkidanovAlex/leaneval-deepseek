/-
  WilC4/transferOfULPM : H2 of the lead's C4 route: the *uniform log-piecewise-monomiality*
  statement of `WilC4/ULPMDefs.lean` transfers from `ℝ` to every model of `TR`.

  The mathematical content is that ULPM is a first-order schema: for a parameter-free `LRc`
  formula `φ` defining the family and fixed meta-data `N, Nq, qs, ψ`, the conclusion is the
  `LRc`-*sentence* `ulpmSent k N Nq φ ψ qs` (`WilC4/ULPMSyntax.lean`), whose semantic content is
  `ULPMGood` (`ulpmSent_realize`, `WilC4/ULPMRealize.lean`).  Completeness of `TR` then transfers
  it, exactly as in `transferOfPB`.

  The extraction of the data from the hypothesis `ModelULPM ℝ` (the `ℝ`-side input H1) is the
  lemma `realULPMGood`.
-/
import Mathlib
import Submission.Work.WilC4.ULPMSyntax
import Submission.Work.WilC4.ULPMRealize
import Submission.Work.WilC4.realULPMGood

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

noncomputable section
open Classical FirstOrder FirstOrder.Language
namespace Work.WilC4

open WilkiesDesign WilkiesDesign.CG
open Work.WilC2 (model_exists_sq real_exists_sq)

theorem transferOfULPM (h : Work.WilC4.Route.ModelULPM ℝ) : ∀ (M : Type) [Field M] [LinearOrder M] [IsStrictOrderedRing M] [FirstOrder.Ring.CompatibleRing M] [WilkiesDesign.CG.rexpL.Structure M] [(FirstOrder.Language.constantsOn ℝ).Structure M], M ⊨ WilkiesDesign.CG.TR → Work.WilC4.Route.ModelULPM M := by
  intro M _ _ _ _ _ _ hM k Y hYd hgraph
  obtain ⟨φ, hYeq⟩ := Set.empty_definable_iff.mp hYd
  obtain ⟨N, Nq, qs, ψ, hNpos, hgoodℝ⟩ := realULPMGood h φ
  have hsqM : ∀ x : M, 0 ≤ x → ∃ z : M, x = z * z := model_exists_sq hM
  have hsqℝ : ∀ x : ℝ, 0 ≤ x → ∃ z : ℝ, x = z * z := real_exists_sq
  haveI : M ⊨ LRc.completeTheory ℝ := hM
  have hSentℝ : ℝ ⊨ ulpmSent k N Nq φ ψ qs :=
    (ulpmSent_realize hsqℝ k N Nq φ ψ qs).mpr hgoodℝ
  have hSentM : M ⊨ ulpmSent k N Nq φ ψ qs :=
    (realize_iff_of_model_completeTheory (L := LRc) (M := ℝ) (N := M)
      (ulpmSent k N Nq φ ψ qs)).mpr hSentℝ
  have hgoodM : ULPMGood k N Nq φ ψ qs M :=
    (ulpmSent_realize hsqM k N Nq φ ψ qs).mp hSentM
  have hgraphM : ∀ (c : Fin k → M) (x y y' : M), uphiVal k φ M c x y →
      uphiVal k φ M c x y' → y = y' := by
    intro c x y y' h1 h2
    refine hgraph c x y y' ?_ ?_
    · rw [hYeq]; exact h1
    · rw [hYeq]; exact h2
  have hbodyM := hgoodM hgraphM
  refine ⟨N, hNpos, Finset.univ.image qs, {z : Fin (k + 1) → M | ψ.Realize z}, ?_, ?_⟩
  · exact Set.empty_definable_iff.mpr ⟨ψ, rfl⟩
  · intro c
    refine ⟨(hbodyM c).1, ?_⟩
    intro x₁ x₂ hx1 hx2 hss
    have hss' : ∀ b : M, (Fin.cons b c ∈ {z : Fin (k + 1) → M | ψ.Realize z}) →
        (((N : M) * b < x₁ ∧ (N : M) * b < x₂) ∨
         ((N : M) * x₁ < b ∧ (N : M) * x₂ < b)) := fun b hb => hss b hb
    obtain ⟨hd, ha⟩ := (hbodyM c).2 x₁ x₂ hx1 hx2 hss'
    · refine ⟨?_, ?_⟩
      · rw [hYeq]
        simp only [Set.mem_ofPred_eq]
        exact hd
      · intro y₁ y₂ hy1 hy2
        rw [hYeq] at hy1 hy2
        simp only [Set.mem_ofPred_eq] at hy1 hy2
        obtain ⟨i, t₁, t₂, h1, h2, h3, h4⟩ := ha y₁ y₂ hy1 hy2
        exact ⟨qs i, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩, t₁, t₂, h1, h2, h3, h4⟩

end Work.WilC4
