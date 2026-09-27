import Mathlib
import Submission.Work.Mostow.orthSmallCommuteDefs
import Submission.Work.Mostow.Margulis.engel_frobenius_orthogonal

namespace Work.Mostow.osc

open Submission.Mostow

/-- One step of the Engel descent: if `B_{i+2} = 1` for the Engel sequence
`B₀ = b`, `B_{k+1} = [a, B_k]` inside a subgroup `A ≤ O(m)`, and both `a` and `B_i` are within
operator norm `1/2` of the identity, then `a` commutes with `[a, B_i] = B_{i+1}`, so
Engel–Frobenius gives `a B_i = B_i a`, i.e. `B_{i+1} = 1`. -/
lemma engelSeq_step {m : ℕ} (A : Subgroup (Submission.Mostow.E m ≃ₗᵢ[ℝ] Submission.Mostow.E m))
    (a b : A)
    (ha : Work.Mostow.mOf (a : Submission.Mostow.E m ≃ₗᵢ[ℝ] Submission.Mostow.E m) ≤ 1 / 4)
    (hbound : ∀ i : ℕ, Work.Mostow.mOf (Work.Mostow.engelSeq A a b i : Submission.Mostow.E m ≃ₗᵢ[ℝ] Submission.Mostow.E m) ≤ 1 / 2)
    (i : ℕ) (h : Work.Mostow.engelSeq A a b (i + 2) = 1) :
    Work.Mostow.engelSeq A a b (i + 1) = 1 := by
  have ha' : ‖Work.Mostow.opOf (a : Submission.Mostow.E m ≃ₗᵢ[ℝ] Submission.Mostow.E m) - 1‖ ≤ 1/2 := by
    have h1 := ha; unfold Work.Mostow.mOf at h1; linarith
  have hbound_i : ‖Work.Mostow.opOf (Work.Mostow.engelSeq A a b i : Submission.Mostow.E m ≃ₗᵢ[ℝ] Submission.Mostow.E m) - 1‖ ≤ 1/2 := by
    have h1 := hbound i; unfold Work.Mostow.mOf at h1; exact h1
  set c : Submission.Mostow.E m ≃ₗᵢ[ℝ] Submission.Mostow.E m :=
      (a : Submission.Mostow.E m ≃ₗᵢ[ℝ] Submission.Mostow.E m)
        * (Work.Mostow.engelSeq A a b i : Submission.Mostow.E m ≃ₗᵢ[ℝ] Submission.Mostow.E m)
        * (a : Submission.Mostow.E m ≃ₗᵢ[ℝ] Submission.Mostow.E m)⁻¹
        * (Work.Mostow.engelSeq A a b i : Submission.Mostow.E m ≃ₗᵢ[ℝ] Submission.Mostow.E m)⁻¹ with hc
  have hstep_i' : (Work.Mostow.engelSeq A a b (i+1) : Submission.Mostow.E m ≃ₗᵢ[ℝ] Submission.Mostow.E m) = c := by
    rw [Work.Mostow.engelSeq_succ, hc]
  -- `B_{i+2} = [a, B_{i+1}] = 1`, i.e. `a` commutes with `B_{i+1} = c`.
  have hrel : (a : Submission.Mostow.E m ≃ₗᵢ[ℝ] Submission.Mostow.E m) * c
      * (a : Submission.Mostow.E m ≃ₗᵢ[ℝ] Submission.Mostow.E m)⁻¹ * c⁻¹ = 1 := by
    rw [← hstep_i', ← Work.Mostow.engelSeq_succ A a b (i+1)]
    rw [h]
    rfl
  have hcomm : (a : Submission.Mostow.E m ≃ₗᵢ[ℝ] Submission.Mostow.E m) * c
      = c * (a : Submission.Mostow.E m ≃ₗᵢ[ℝ] Submission.Mostow.E m) := by
    have h2 : (a : Submission.Mostow.E m ≃ₗᵢ[ℝ] Submission.Mostow.E m) * c
        * (a : Submission.Mostow.E m ≃ₗᵢ[ℝ] Submission.Mostow.E m)⁻¹ = c := by
      have := congrArg (fun x => x * c) hrel
      simpa using this
    calc (a : Submission.Mostow.E m ≃ₗᵢ[ℝ] Submission.Mostow.E m) * c
        = (a : Submission.Mostow.E m ≃ₗᵢ[ℝ] Submission.Mostow.E m) * c
          * (a : Submission.Mostow.E m ≃ₗᵢ[ℝ] Submission.Mostow.E m)⁻¹
          * (a : Submission.Mostow.E m ≃ₗᵢ[ℝ] Submission.Mostow.E m) := by group
      _ = c * (a : Submission.Mostow.E m ≃ₗᵢ[ℝ] Submission.Mostow.E m) := by rw [h2]
  -- Engel–Frobenius: `a` commuting with `[a, B_i] = c` forces `a B_i = B_i a`.
  have hAB : (a : Submission.Mostow.E m ≃ₗᵢ[ℝ] Submission.Mostow.E m)
        * (Work.Mostow.engelSeq A a b i : Submission.Mostow.E m ≃ₗᵢ[ℝ] Submission.Mostow.E m)
      = (Work.Mostow.engelSeq A a b i : Submission.Mostow.E m ≃ₗᵢ[ℝ] Submission.Mostow.E m)
        * (a : Submission.Mostow.E m ≃ₗᵢ[ℝ] Submission.Mostow.E m) :=
    Work.Mostow.Margulis.engel_frobenius_orthogonal
      (a : Submission.Mostow.E m ≃ₗᵢ[ℝ] Submission.Mostow.E m)
      (Work.Mostow.engelSeq A a b i : Submission.Mostow.E m ≃ₗᵢ[ℝ] Submission.Mostow.E m)
      ha' hbound_i hcomm
  have hgoal : (Work.Mostow.engelSeq A a b (i+1) : Submission.Mostow.E m ≃ₗᵢ[ℝ] Submission.Mostow.E m) = 1 := by
    rw [hstep_i', hc]
    calc (a : Submission.Mostow.E m ≃ₗᵢ[ℝ] Submission.Mostow.E m)
          * (Work.Mostow.engelSeq A a b i : Submission.Mostow.E m ≃ₗᵢ[ℝ] Submission.Mostow.E m)
          * (a : Submission.Mostow.E m ≃ₗᵢ[ℝ] Submission.Mostow.E m)⁻¹
          * (Work.Mostow.engelSeq A a b i : Submission.Mostow.E m ≃ₗᵢ[ℝ] Submission.Mostow.E m)⁻¹
        = ((Work.Mostow.engelSeq A a b i : Submission.Mostow.E m ≃ₗᵢ[ℝ] Submission.Mostow.E m)
            * (a : Submission.Mostow.E m ≃ₗᵢ[ℝ] Submission.Mostow.E m))
          * (a : Submission.Mostow.E m ≃ₗᵢ[ℝ] Submission.Mostow.E m)⁻¹
          * (Work.Mostow.engelSeq A a b i : Submission.Mostow.E m ≃ₗᵢ[ℝ] Submission.Mostow.E m)⁻¹ := by rw [hAB]
      _ = 1 := by group
  exact Subtype.ext hgoal

end Work.Mostow.osc
