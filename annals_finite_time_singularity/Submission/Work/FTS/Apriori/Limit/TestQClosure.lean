/-
# `Work.FTS.Apriori.Limit.TestQClosure` — closures of the class of test functions

`TestQ ψ` is the class of functions that are `C^∞` on the open quadrant `Qd = (0,∞) × (0,π/2)`
and have compact support contained in it.  This module proves that the class is closed under
multiplication by functions that are `C^∞` on the quadrant, and under the adjoints
`adjMixed (j,i) = (D_z^j D_θ^i)^*` of the slot operators.
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.Apriori.Limit.Defs
import Submission.Work.FTS.Apriori.Limit.SlotCalc

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.Apriori.Limit

set_option autoImplicit false

open Work.FTS.LocData (SmoothQuad)

theorem isOpen_Qd : IsOpen Qd := isOpen_Ioi.prod isOpen_Ioo

/-! ## Supports of the partial derivatives -/

/-- The support of the partial `z`-derivative is contained in the closed support of the
function. -/
theorem isClosed_slice_tsupport (ψ : ℝ → ℝ → ℝ) (θ : ℝ) :
    IsClosed {z : ℝ | (z, θ) ∈ tsupport (Function.uncurry ψ)} :=
  (isClosed_tsupport (Function.uncurry ψ)).preimage (continuous_id.prodMk continuous_const)

theorem isClosed_slice_tsupport' (ψ : ℝ → ℝ → ℝ) (z : ℝ) :
    IsClosed {θ : ℝ | (z, θ) ∈ tsupport (Function.uncurry ψ)} :=
  (isClosed_tsupport (Function.uncurry ψ)).preimage (continuous_const.prodMk continuous_id)

theorem support_pz_subset_tsupport (ψ : ℝ → ℝ → ℝ) :
    Function.support (fun p : ℝ × ℝ => Work.Spaces.pz ψ p.1 p.2)
      ⊆ tsupport (Function.uncurry ψ) := by
  intro p hp
  have hp1 : p.1 ∈ tsupport (fun z : ℝ => deriv (fun z' => ψ z' p.2) z) :=
    subset_tsupport _ (by simpa [Function.mem_support, Work.Spaces.pz] using hp)
  have h1 : tsupport (fun z : ℝ => deriv (fun z' => ψ z' p.2) z)
      ⊆ tsupport (fun z : ℝ => ψ z p.2) := tsupport_deriv_subset
  have h2 : tsupport (fun z : ℝ => ψ z p.2)
      ⊆ {z : ℝ | (z, p.2) ∈ tsupport (Function.uncurry ψ)} := by
    refine closure_minimal ?_ (isClosed_slice_tsupport ψ p.2)
    intro z hz
    exact subset_tsupport (Function.uncurry ψ) (by simpa using hz)
  exact h2 (h1 hp1)

/-- The support of the partial `θ`-derivative is contained in the closed support of the
function. -/
theorem support_pth_subset_tsupport (ψ : ℝ → ℝ → ℝ) :
    Function.support (fun p : ℝ × ℝ => Work.Spaces.pth ψ p.1 p.2)
      ⊆ tsupport (Function.uncurry ψ) := by
  intro p hp
  have hp2 : p.2 ∈ tsupport (fun θ : ℝ => deriv (fun θ' => ψ p.1 θ') θ) :=
    subset_tsupport _ (by simpa [Function.mem_support, Work.Spaces.pth] using hp)
  have h1 : tsupport (fun θ : ℝ => deriv (fun θ' => ψ p.1 θ') θ)
      ⊆ tsupport (fun θ : ℝ => ψ p.1 θ) := tsupport_deriv_subset
  have h2 : tsupport (fun θ : ℝ => ψ p.1 θ)
      ⊆ {θ : ℝ | (p.1, θ) ∈ tsupport (Function.uncurry ψ)} := by
    refine closure_minimal ?_ (isClosed_slice_tsupport' ψ p.1)
    intro θ hθ
    exact subset_tsupport (Function.uncurry ψ) (by simpa using hθ)
  exact h2 (h1 hp2)

/-! ## Supports of the adjoints -/

theorem support_adjZ_subset (ψ : ℝ → ℝ → ℝ) :
    Function.support (Function.uncurry (adjZ ψ)) ⊆ tsupport (Function.uncurry ψ) := by
  have hneg : Function.support (fun p : ℝ × ℝ =>
      -(Function.uncurry (Work.Spaces.pz (fun z θ => z * ψ z θ)) p))
      = Function.support (fun p : ℝ × ℝ =>
          Function.uncurry (Work.Spaces.pz (fun z θ => z * ψ z θ)) p) := by
    ext p
    simp only [Function.mem_support, neg_ne_zero]
  have hG : Function.uncurry (adjZ ψ)
      = fun p : ℝ × ℝ =>
          -(Function.uncurry (Work.Spaces.pz (fun z θ => z * ψ z θ)) p) := rfl
  rw [hG, hneg]
  refine (support_pz_subset_tsupport (fun z θ => z * ψ z θ)).trans ?_
  exact closure_mono (Function.support_mul_subset_right _ _)

theorem support_adjTh_subset (ψ : ℝ → ℝ → ℝ) :
    Function.support (Function.uncurry (adjTh ψ)) ⊆ tsupport (Function.uncurry ψ) := by
  have hneg : Function.support (fun p : ℝ × ℝ =>
      -(Function.uncurry (Work.Spaces.pth (fun z θ => Real.sin (2 * θ) * ψ z θ)) p))
      = Function.support (fun p : ℝ × ℝ =>
          Function.uncurry (Work.Spaces.pth (fun z θ => Real.sin (2 * θ) * ψ z θ)) p) := by
    ext p
    simp only [Function.mem_support, neg_ne_zero]
  have hG : Function.uncurry (adjTh ψ)
      = fun p : ℝ × ℝ =>
          -(Function.uncurry (Work.Spaces.pth (fun z θ => Real.sin (2 * θ) * ψ z θ)) p) := rfl
  rw [hG, hneg]
  refine (support_pth_subset_tsupport (fun z θ => Real.sin (2 * θ) * ψ z θ)).trans ?_
  exact closure_mono (Function.support_mul_subset_right _ _)

/-! ## The elementary adjoints preserve `TestQ` -/

theorem TestQ_adjZ {ψ : ℝ → ℝ → ℝ} (h : TestQ ψ) : TestQ (adjZ ψ) := by
  obtain ⟨hsm, hcomp, hsub⟩ := h
  have hG : ContDiffOn ℝ Work.Stability.smoothOrder
      (Function.uncurry (fun z θ => z * ψ z θ)) Qd := by
    have h1 : ContDiffOn ℝ Work.Stability.smoothOrder
        (fun p : ℝ × ℝ => p.1 * Function.uncurry ψ p) Qd :=
      (contDiffOn_fst (s := Qd)).mul hsm
    exact h1.congr (fun p _ => rfl)
  have hsupp : tsupport (Function.uncurry (adjZ ψ)) ⊆ tsupport (Function.uncurry ψ) :=
    closure_minimal (support_adjZ_subset ψ) (isClosed_tsupport (Function.uncurry ψ))
  exact ⟨(Work.FTS.LocData.contDiffOn_pz isOpen_Qd hG).neg,
    IsCompact.of_isClosed_subset hcomp (isClosed_tsupport (Function.uncurry (adjZ ψ))) hsupp,
    hsupp.trans hsub⟩

theorem TestQ_adjTh {ψ : ℝ → ℝ → ℝ} (h : TestQ ψ) : TestQ (adjTh ψ) := by
  obtain ⟨hsm, hcomp, hsub⟩ := h
  have hG : ContDiffOn ℝ Work.Stability.smoothOrder
      (Function.uncurry (fun z θ => Real.sin (2 * θ) * ψ z θ)) Qd := by
    have hsin : ContDiffOn ℝ Work.Stability.smoothOrder
        (fun p : ℝ × ℝ => Real.sin (2 * p.2)) Qd :=
      (Real.contDiff_sin.comp (contDiff_const.mul contDiff_snd)).contDiffOn
    have h1 : ContDiffOn ℝ Work.Stability.smoothOrder
        (fun p : ℝ × ℝ => Real.sin (2 * p.2) * Function.uncurry ψ p) Qd := hsin.mul hsm
    exact h1.congr (fun p _ => rfl)
  have hsupp : tsupport (Function.uncurry (adjTh ψ)) ⊆ tsupport (Function.uncurry ψ) :=
    closure_minimal (support_adjTh_subset ψ) (isClosed_tsupport (Function.uncurry ψ))
  exact ⟨(Work.FTS.LocData.contDiffOn_pth isOpen_Qd hG).neg,
    IsCompact.of_isClosed_subset hcomp (isClosed_tsupport (Function.uncurry (adjTh ψ))) hsupp,
    hsupp.trans hsub⟩

theorem TestQ_adjDzIter (j : ℕ) {ψ : ℝ → ℝ → ℝ} (h : TestQ ψ) :
    TestQ (adjDzIter j ψ) := by
  induction j generalizing ψ with
  | zero => exact h
  | succ j ih => exact ih (TestQ_adjZ h)

theorem TestQ_adjDthIter (i : ℕ) {ψ : ℝ → ℝ → ℝ} (h : TestQ ψ) :
    TestQ (adjDthIter i ψ) := by
  induction i generalizing ψ with
  | zero => exact h
  | succ i ih => exact ih (TestQ_adjTh h)

/-- `TestQ` is closed under multiplication by functions that are `C^∞` on the open quadrant,
and under the adjoints of the slot operators. -/
theorem TestQ_mul_adjMixed {ψ : ℝ → ℝ → ℝ} (hψ : TestQ ψ) :
    (∀ (g : ℝ → ℝ → ℝ),
        ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry g) Qd →
        TestQ (fun z θ => g z θ * ψ z θ)) ∧
      (∀ j i : ℕ, TestQ (adjMixed (j, i) ψ)) := by
  constructor
  · intro g hg
    have hsupp : Function.support (Function.uncurry (fun z θ => g z θ * ψ z θ))
        ⊆ tsupport (Function.uncurry ψ) :=
      (Function.support_mul_subset_right _ _).trans (subset_tsupport _)
    refine ⟨hg.mul hψ.1, ?_, ?_⟩
    · exact IsCompact.of_isClosed_subset hψ.2.1
        (isClosed_tsupport (Function.uncurry (fun z θ => g z θ * ψ z θ)))
        (closure_minimal hsupp (isClosed_tsupport (Function.uncurry ψ)))
    · exact (closure_minimal hsupp (isClosed_tsupport (Function.uncurry ψ))).trans hψ.2.2
  · intro j i
    exact TestQ_adjDthIter i (TestQ_adjDzIter j hψ)

end Work.FTS.Apriori.Limit
