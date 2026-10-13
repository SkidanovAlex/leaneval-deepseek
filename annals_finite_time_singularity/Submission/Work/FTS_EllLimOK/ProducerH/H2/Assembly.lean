import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS_EllLimOK.RulingELF
import Submission.Work.FTS_EllLimOK.ProducerH.H2.Basic
import Submission.Work.FTS_EllLimOK.ProducerH.H2.Data

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_EllLimOK.ProducerH

open scoped Real Topology
open MeasureTheory Set Filter

open Work.FTS.Galerkin (Fn)

/-- **The assembly of `PkgBoxH` from the box data and the three clauses.**

The three clauses of `RulingELF.PkgBoxH` are taken as hypotheses (they are produced by the H2
chapter from the endpooint data `H2.BoxData`); the content of this lemma is the box quantifier
bookkeeping: the non-degenerate box `a < b` is handled by the clauses, while the degenerate box
`a = b = {a} × [0,π/2]` carries only the `ContDiffOn` clause, which is obtained by monotonicity
from the non-degenerate box `cbox a (a+1) ⊇ cbox a a`. -/
theorem pkgBoxH_of_data {α Ce : ℝ} {E : Fn →ₗ[ℝ] Fn}
    (hboxdata : ∀ a b : ℝ, 0 < a → a ≤ b → H2.BoxData α Ce E a b)
    (hclause1 : ∀ a b : ℝ, 0 < a → a < b → H2.BoxData α Ce E a b →
      ∀ g : Fn, Work.FTS.ClassC.ClassC α g →
        ContDiffOn ℝ 2 (Function.uncurry (E g)) (Work.FTS_EllLimOK.cbox a b))
    (hclause2 : ∀ a b : ℝ, 0 < a → a < b → H2.BoxData α Ce E a b →
      (∀ g : Fn, Work.FTS.ClassC.ClassC α g →
        ContDiffOn ℝ 2 (Function.uncurry (E g)) (Work.FTS_EllLimOK.cbox a b)) →
      ∃ K : ℝ, 0 < K ∧ ∀ g : Fn, Work.FTS.ClassC.ClassC α g →
        ∀ k : ℕ, k ≤ 2 → ∀ p ∈ Work.FTS_EllLimOK.cbox a b,
          ‖iteratedFDerivWithin ℝ k (Function.uncurry (E g))
            (Work.FTS_EllLimOK.cbox a b) p‖
            ≤ K * Work.FTS.StrongGlobal.Xn6 α g)
    (hclause3 : ∀ a b : ℝ, 0 < a → a < b → H2.BoxData α Ce E a b →
      (∀ g : Fn, Work.FTS.ClassC.ClassC α g →
        ContDiffOn ℝ 2 (Function.uncurry (E g)) (Work.FTS_EllLimOK.cbox a b)) →
      ∃ K : ℝ, 0 < K ∧ ∃ β : ℝ, 0 < β ∧ ∀ g : Fn, Work.FTS.ClassC.ClassC α g →
        ∀ p ∈ Work.FTS_EllLimOK.cbox a b, ∀ q ∈ Work.FTS_EllLimOK.cbox a b,
          ‖iteratedFDerivWithin ℝ 2 (Function.uncurry (E g))
              (Work.FTS_EllLimOK.cbox a b) p
            - iteratedFDerivWithin ℝ 2 (Function.uncurry (E g))
              (Work.FTS_EllLimOK.cbox a b) q‖
            ≤ K * Work.FTS.StrongGlobal.Xn6 α g * ‖p - q‖ ^ β) :
    Work.FTS_EllLimOK.RulingELF.PkgBoxH α E := by
  intro a b ha hab
  by_cases hab' : a < b
  · -- ## the non-degenerate box: the three clauses
    obtain ⟨hdata, hc1, hc2, hc3⟩ :
        H2.BoxData α Ce E a b ∧
        (∀ g : Fn, Work.FTS.ClassC.ClassC α g →
          ContDiffOn ℝ 2 (Function.uncurry (E g)) (Work.FTS_EllLimOK.cbox a b)) ∧
        (∃ K : ℝ, 0 < K ∧ ∀ g : Fn, Work.FTS.ClassC.ClassC α g →
          ∀ k : ℕ, k ≤ 2 → ∀ p ∈ Work.FTS_EllLimOK.cbox a b,
            ‖iteratedFDerivWithin ℝ k (Function.uncurry (E g))
              (Work.FTS_EllLimOK.cbox a b) p‖
              ≤ K * Work.FTS.StrongGlobal.Xn6 α g) ∧
        (∃ K : ℝ, 0 < K ∧ ∃ β : ℝ, 0 < β ∧ ∀ g : Fn, Work.FTS.ClassC.ClassC α g →
          ∀ p ∈ Work.FTS_EllLimOK.cbox a b, ∀ q ∈ Work.FTS_EllLimOK.cbox a b,
            ‖iteratedFDerivWithin ℝ 2 (Function.uncurry (E g))
                (Work.FTS_EllLimOK.cbox a b) p
              - iteratedFDerivWithin ℝ 2 (Function.uncurry (E g))
                (Work.FTS_EllLimOK.cbox a b) q‖
              ≤ K * Work.FTS.StrongGlobal.Xn6 α g * ‖p - q‖ ^ β) :=
      ⟨hboxdata a b ha hab, hclause1 a b ha hab' (hboxdata a b ha hab),
        hclause2 a b ha hab' (hboxdata a b ha hab)
          (hclause1 a b ha hab' (hboxdata a b ha hab)),
        hclause3 a b ha hab' (hboxdata a b ha hab)
          (hclause1 a b ha hab' (hboxdata a b ha hab))⟩
    obtain ⟨K₂, hK₂, hc2'⟩ := hc2
    obtain ⟨K₃, hK₃, β₃, hβ₃, hc3'⟩ := hc3
    refine ⟨max K₂ K₃ + 1, β₃, by positivity, hβ₃, ?_⟩
    intro g hg
    refine ⟨hc1 g hg, fun _ => ?_, fun _ => ?_⟩
    · intro k hk p hp
      have h := hc2' g hg k hk p hp
      have hX : (0 : ℝ) ≤ Work.FTS.StrongGlobal.Xn6 α g := H2.Xn6_nonneg α g
      calc ‖iteratedFDerivWithin ℝ k (Function.uncurry (E g))
            (Work.FTS_EllLimOK.cbox a b) p‖
          ≤ K₂ * Work.FTS.StrongGlobal.Xn6 α g := h
        _ ≤ (max K₂ K₃ + 1) * Work.FTS.StrongGlobal.Xn6 α g :=
            mul_le_mul_of_nonneg_right (by linarith [le_max_left K₂ K₃]) hX
    · intro p hp q hq
      have h := hc3' g hg p hp q hq
      have hX : (0 : ℝ) ≤ Work.FTS.StrongGlobal.Xn6 α g := H2.Xn6_nonneg α g
      have hr : (0 : ℝ) ≤ ‖p - q‖ ^ β₃ := Real.rpow_nonneg (norm_nonneg _) _
      calc ‖iteratedFDerivWithin ℝ 2 (Function.uncurry (E g))
              (Work.FTS_EllLimOK.cbox a b) p
            - iteratedFDerivWithin ℝ 2 (Function.uncurry (E g))
              (Work.FTS_EllLimOK.cbox a b) q‖
          ≤ K₃ * Work.FTS.StrongGlobal.Xn6 α g * ‖p - q‖ ^ β₃ := h
        _ ≤ (max K₂ K₃ + 1) * Work.FTS.StrongGlobal.Xn6 α g * ‖p - q‖ ^ β₃ :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right (by linarith [le_max_right K₂ K₃]) hX) hr
  · -- ## the degenerate box `a = b`: only the first clause is asked for, and the box sits
    -- inside the non-degenerate box `cbox a (a+1)`
    have hba : b = a := le_antisymm (not_lt.mp hab') hab
    rw [hba]
    have hdata : H2.BoxData α Ce E a (a + 1) := hboxdata a (a + 1) ha (by linarith)
    have hc1 : ∀ g : Fn, Work.FTS.ClassC.ClassC α g →
        ContDiffOn ℝ 2 (Function.uncurry (E g)) (Work.FTS_EllLimOK.cbox a (a + 1)) :=
      hclause1 a (a + 1) ha (by linarith) hdata
    refine ⟨1, 1, one_pos, one_pos, ?_⟩
    intro g hg
    refine ⟨?_, ?_, ?_⟩
    · exact (hc1 g hg).mono (fun p hp => by
        rw [Work.FTS_EllLimOK.mem_cbox] at hp ⊢
        exact ⟨⟨hp.1.1, by linarith [hp.1.2]⟩, hp.2⟩)
    · intro hcon
      exact absurd hcon (by linarith)
    · intro hcon
      exact absurd hcon (by linarith)

end Work.FTS_EllLimOK.ProducerH
