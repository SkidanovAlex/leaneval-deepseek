import Mathlib
import Submission.Work.Diff.STE.B3.VarCoef.varLapStarDef
import Submission.Work.Diff.STE.B3.VarCoef.mulOp_isOrd
import Submission.Work.Diff.STE.B3.VarCoef.pdOp_isOrd

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `varLapStar A B` is an operator of order `2`

The formal adjoint `varLapStar A B h = -(Σ_{ab} ∂_a∂_b (A_{ab} h) + Σ_a ∂_a (B_a h))` is built out
of the two primitive operators of the order calculus `VarCoef/OpOrder.lean`:

* the multipliers `M_{A a b}` and `M_{B a}`, of order `0` (`mulOp_isOrd`), and
* the partial derivatives `∂_a = pdOp a`, of order `1` (`pdOp_isOrd`),

in the compositions `∂_a (∂_b (M_{A a b} ·))` (order `1 + (1 + 0) = 2`) and `∂_a (M_{B a} ·)`
(order `1 + 0 = 1`, lifted to `2` by monotonicity in the order).  Finite sums and the outer
negation preserve the order (`IsOrd.sum`, `IsOrd.add`, `IsOrd.neg`), so `varLapStar A B` has order
`2`; the one thing to check is that the pointwise description `varLapStar` coincides with the
operator built from these compositions (`varLapStar_eq_ops`).
-/

noncomputable section

open scoped BigOperators

namespace Work.Diff.STE.B3.VarCoef

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The pointwise identity expressing `varLapStar A B` as a finite sum of compositions of partial
derivatives and multipliers, in the operator notation of `VarCoef/OpOrder.lean`. -/
theorem varLapStar_eq_ops (A : ι → ι → (ι → ℝ) → ℝ) (B : ι → (ι → ℝ) → ℝ)
    (f : (ι → ℝ) → ℂ) :
    varLapStar A B f
      = -(((∑ a, ∑ b, compOp (pdOp a) (compOp (pdOp b) (mulOp (A a b)))) f)
        + ((∑ a, compOp (pdOp a) (mulOp (B a))) f)) := by
  funext x
  simp only [varLapStar, Pi.neg_apply, Pi.add_apply, Finset.sum_apply,
    compOp_apply, pdOp]
  rfl

/-- `∂_a ∂_b (M_{A a b} ·)` is an operator of order `2`. -/
theorem isOrd_two_pd_pd_mulOp (a b : ι) (A : ι → ι → (ι → ℝ) → ℝ)
    (hA : ContDiff ℝ (⊤ : ℕ∞) (A a b)) (hAp : Work.Diff.STE.Periodic1 (A a b)) :
    ∃ C : ℤ → ℝ, IsOrd 2 C (compOp (pdOp a) (compOp (pdOp b) (mulOp (A a b)))) := by
  obtain ⟨Cb, hCb⟩ := mulOp_isOrd (A a b) hA hAp
  obtain ⟨Cd, hCd⟩ := pdOp_isOrd a
  obtain ⟨Ce, hCe⟩ := pdOp_isOrd b
  have h := IsOrd.comp (T := pdOp a) (U := compOp (pdOp b) (mulOp (A a b))) hCd
    (IsOrd.comp (T := pdOp b) (U := mulOp (A a b)) hCe hCb)
  exact ⟨_, IsOrd.mono_d h (by omega)⟩

/-- `∂_a (M_{B a} ·)` is an operator of order `2` (its true order is `1`). -/
theorem isOrd_two_pd_mulOp (a : ι) (B : ι → (ι → ℝ) → ℝ)
    (hB : ContDiff ℝ (⊤ : ℕ∞) (B a)) (hBp : Work.Diff.STE.Periodic1 (B a)) :
    ∃ C : ℤ → ℝ, IsOrd 2 C (compOp (pdOp a) (mulOp (B a))) := by
  obtain ⟨Cb, hCb⟩ := mulOp_isOrd (B a) hB hBp
  obtain ⟨Cd, hCd⟩ := pdOp_isOrd a
  exact ⟨_, IsOrd.mono_d (IsOrd.comp (T := pdOp a) (U := mulOp (B a)) hCd hCb) (by omega)⟩

/-- The operator built from the compositions has order `2`. -/
theorem varLapStar_collapse_isOrd (A : ι → ι → (ι → ℝ) → ℝ) (B : ι → (ι → ℝ) → ℝ)
    (hA : ∀ a b, ContDiff ℝ (⊤ : ℕ∞) (A a b)) (hAp : ∀ a b, Work.Diff.STE.Periodic1 (A a b))
    (hB : ∀ a, ContDiff ℝ (⊤ : ℕ∞) (B a)) (hBp : ∀ a, Work.Diff.STE.Periodic1 (B a)) :
    ∃ C : ℤ → ℝ, IsOrd 2 C
      (-((∑ a, ∑ b, compOp (pdOp a) (compOp (pdOp b) (mulOp (A a b))))
        + (∑ a, compOp (pdOp a) (mulOp (B a))))) := by
  classical
  -- ### the second-order part `Σ_{ab} ∂_a ∂_b M_{A a b}`
  have hT1 : ∃ C : ℤ → ℝ, IsOrd 2 C
      (∑ a, ∑ b, compOp (pdOp a) (compOp (pdOp b) (mulOp (A a b)))) := by
    have hinner : ∀ a : ι, ∃ C : ℤ → ℝ, IsOrd 2 C
        (∑ b, compOp (pdOp a) (compOp (pdOp b) (mulOp (A a b)))) := by
      intro a
      choose C hC using fun b : ι => isOrd_two_pd_pd_mulOp a b A (hA a b) (hAp a b)
      exact ⟨fun t => (Fintype.card ι : ℝ) * ∑ b, C b t,
        IsOrd.sum Finset.univ
          (fun b => compOp (pdOp a) (compOp (pdOp b) (mulOp (A a b)))) C
          (fun b _ => hC b)⟩
    choose C hC using hinner
    exact ⟨fun t => (Fintype.card ι : ℝ) * ∑ a, C a t,
      IsOrd.sum Finset.univ
        (fun a => ∑ b, compOp (pdOp a) (compOp (pdOp b) (mulOp (A a b)))) C
        (fun a _ => hC a)⟩
  -- ### the first-order part `Σ_a ∂_a M_{B a}`, lifted to order `2`
  have hT2 : ∃ C : ℤ → ℝ, IsOrd 2 C (∑ a, compOp (pdOp a) (mulOp (B a))) := by
    choose C hC using fun a : ι => isOrd_two_pd_mulOp a B (hB a) (hBp a)
    exact ⟨fun t => (Fintype.card ι : ℝ) * ∑ a, C a t,
      IsOrd.sum Finset.univ (fun a => compOp (pdOp a) (mulOp (B a))) C (fun a _ => hC a)⟩
  obtain ⟨C₁, h₁⟩ := hT1
  obtain ⟨C₂, h₂⟩ := hT2
  exact ⟨fun t => 2 * (C₁ t + C₂ t), IsOrd.neg (IsOrd.add h₁ h₂)⟩

theorem varLapStarOp_isOrd {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ι → ι → (ι → ℝ) → ℝ) (B : ι → (ι → ℝ) → ℝ)
    (hA : ∀ a b, ContDiff ℝ (⊤ : ℕ∞) (A a b)) (hAp : ∀ a b, Work.Diff.STE.Periodic1 (A a b))
    (hB : ∀ a, ContDiff ℝ (⊤ : ℕ∞) (B a)) (hBp : ∀ a, Work.Diff.STE.Periodic1 (B a)) :
    ∃ C : ℤ → ℝ, Work.Diff.STE.B3.VarCoef.IsOrd 2 C
      (Work.Diff.STE.B3.VarCoef.varLapStarOp A B) := by
  classical
  obtain ⟨C, hC⟩ := varLapStar_collapse_isOrd A B hA hAp hB hBp
  refine ⟨C, IsOrd.congr hC (fun f _ => ?_)⟩
  show (-((∑ a, ∑ b, compOp (pdOp a) (compOp (pdOp b) (mulOp (A a b))))
      + (∑ a, compOp (pdOp a) (mulOp (B a))))) f = varLapStar A B f
  exact (varLapStar_eq_ops A B f).symm

end Work.Diff.STE.B3.VarCoef
