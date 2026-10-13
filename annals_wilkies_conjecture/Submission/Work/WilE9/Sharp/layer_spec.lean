import Mathlib
import Submission.Work.WilE9.Sharp.layer_aux2

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace Work.WilE9.Sharp
open WilkiesDesign WilkiesDesign.E

/-- The hypotheses of the layer specification, assembled. -/
theorem layer_spec {n : ℕ} {f : (Fin n → ℝ) → ℝ} {Z : Set (Fin (n + 1) → ℝ)}
    (S : List (AEStratum n))
    (hZ : WilkiesDesign.graphOf f = WilkiesDesign.E.psiV ⁻¹' Z)
    (hGood : ∀ A ∈ S, A.E.Good)
    (hπ : ∀ A ∈ S, ∀ w ∈ A.comp, Work.WilE9.Sharp.stratProj w ∈ Z)
    (hcov : ∃ N : Set (Fin n → ℝ), MeasureTheory.volume N = 0 ∧
      ∀ y ∈ Z, Fin.init y ∉ N → (∀ j : Fin n, |Fin.init y j| < 1) →
        y ∈ ⋃ A ∈ S, Work.WilE9.Sharp.stratProj '' A.comp)
    (hbase : ∀ A ∈ S, ∀ (L : List (Fin n)) (y : Fin n → ℝ) (σ : ℝ),
      (∃ z ∈ Work.WilE9.Sharp.exComp n A.1 A.E A.q L,
        Work.WilE9.Sharp.exOut z = Fin.snoc y σ) →
      ∃ w ∈ A.comp, Work.WilE9.Sharp.stratProj w =
        Fin.snoc (WilkiesDesign.E.psiV (Work.WilE9.Sharp.psiInvV y))
          (WilkiesDesign.E.psi (f (Work.WilE9.Sharp.psiInvV y))))
    (hfst : ∀ A ∈ S, ∀ (L : List (Fin n)) (x : Fin n → ℝ) (w : Fin (n + (1 + A.1)) → ℝ),
      w ∈ A.comp →
      Work.WilE9.Sharp.stratProj w =
        Fin.snoc (WilkiesDesign.E.psiV x) (WilkiesDesign.E.psi (f x)) →
      ∃ z ∈ Work.WilE9.Sharp.exComp n A.1 A.E A.q L,
        Work.WilE9.Sharp.exOut z =
          Fin.snoc (WilkiesDesign.E.psiV x) (WilkiesDesign.E.psi (Work.WilE9.glDeriv L f x)))
    (hsnd : ∀ A ∈ S, ∀ (L : List (Fin n)) (y : Fin n → ℝ) (σ : ℝ),
      (∃ z ∈ Work.WilE9.Sharp.exComp n A.1 A.E A.q L,
        Work.WilE9.Sharp.exOut z = Fin.snoc y σ) →
      (∀ i : Fin n, |y i| < 1) ∧ |σ| < 1 ∧
        σ = WilkiesDesign.E.psi (Work.WilE9.glDeriv L f (Work.WilE9.Sharp.psiInvV y)))
    (hsndC : ∀ A ∈ S, ∀ (L : List (Fin n)) (y : Fin n → ℝ) (σ : ℝ),
      (∃ z ∈ Work.WilE9.Sharp.exComp n A.1 A.E A.q L,
        Work.WilE9.Sharp.exOut z = Fin.snoc y σ) →
      ContDiffAt ℝ ⊤ f (Work.WilE9.Sharp.psiInvV y))
    (hglperm : ∀ (y : Fin n → ℝ), ContDiffAt ℝ ⊤ f y →
      ∀ (L L' : List (Fin n)), List.Perm L L' →
        Work.WilE9.glDeriv L f y = Work.WilE9.glDeriv L' f y) :
    (∀ k : ℕ, Work.WilE9.Sharp.SecSpec n k S f ∧ Work.WilE9.Sharp.LimSpec n k S f) ∧
      (∀ L L' : List (Fin n), List.Perm L L' →
        Work.WilE9.Sharp.Eset n S L = Work.WilE9.Sharp.Eset n S L') := by
  have H : Work.WilE9.Sharp.LayerHyp n f Z S :=
    ⟨hZ, hGood, hπ, hcov, hbase, hfst, hsnd, hsndC, hglperm⟩
  exact ⟨fun k => ⟨secSpec_of H, limSpec_of H⟩, fun L L' hperm => Eset_perm H hperm⟩

end Work.WilE9.Sharp
