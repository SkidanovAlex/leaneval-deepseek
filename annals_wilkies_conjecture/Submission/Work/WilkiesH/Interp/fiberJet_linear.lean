import Mathlib
import Submission.Work.WilkiesH.Defs

namespace Work.WilkiesH.Interp

/-- Linearity of `iteratedFDeriv` for a finite linear combination: the `n`-th iterated
derivative of `∑ i, c i • f i` is `∑ i, c i • iteratedFDeriv … (f i)`, pointwise at a
vector `v`. -/
lemma iteratedFDeriv_sum_smul_apply {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {ι : Type*} [Fintype ι]
    (c : ι → ℝ) (f : ι → E → F) (n : ℕ) (x : E) (v : Fin n → E)
    (h : ∀ i, ContDiffAt ℝ (n : ℕ) (f i) x) :
    (iteratedFDeriv ℝ n (fun z => ∑ i, c i • f i z) x) v
      = ∑ i, c i • (iteratedFDeriv ℝ n (f i) x) v := by
  rw [iteratedFDeriv_fun_sum_apply (u := Finset.univ) (fun i _ => (h i).const_smul (c i))]
  rw [sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [iteratedFDeriv_const_smul_apply' (f := f i) (x := x) (a := c i) (h i)]
  rw [smul_apply]

theorem fiberJet_linear {μ k d n : ℕ} (α : Fin μ → ℕ) (hα : (∑ i, α i) = n) (s₀ : Fin μ → ℝ)
    (Ψ : (Fin μ → ℝ) → (Fin k → ℝ))
    (hsm : ∀ α' : Work.WilkiesH.ExpVec k d,
      ContDiffAt ℝ n (fun t => Work.WilkiesH.ExpVec.eval α' (Ψ t)) s₀)
    (c : Work.WilkiesH.ExpVec k d → ℝ) :
    (∑ g : {g : Fin n → Fin μ // ∀ i, Fintype.card {l : Fin n // g l = i} = α i},
        (iteratedFDeriv ℝ n
          (fun t => ∑ α' : Work.WilkiesH.ExpVec k d, c α' * Work.WilkiesH.ExpVec.eval α' (Ψ t))
          s₀) (fun i => Pi.single (g.1 i) (1 : ℝ)))
      = ∑ α' : Work.WilkiesH.ExpVec k d, c α' *
        (∑ g : {g : Fin n → Fin μ // ∀ i, Fintype.card {l : Fin n // g l = i} = α i},
          (iteratedFDeriv ℝ n (fun t => Work.WilkiesH.ExpVec.eval α' (Ψ t)) s₀)
            (fun i => Pi.single (g.1 i) (1 : ℝ))) := by
  -- The derivative of the finite linear combination is the finite linear combination of the
  -- derivatives; then exchange the two finite sums and pull out the constant coefficients.
  have key : ∀ g : {g : Fin n → Fin μ // ∀ i, Fintype.card {l : Fin n // g l = i} = α i},
      (iteratedFDeriv ℝ n
          (fun t => ∑ α' : Work.WilkiesH.ExpVec k d, c α' * Work.WilkiesH.ExpVec.eval α' (Ψ t))
          s₀) (fun i => Pi.single (g.1 i) (1 : ℝ))
      = ∑ α' : Work.WilkiesH.ExpVec k d, c α' *
          (iteratedFDeriv ℝ n (fun t => Work.WilkiesH.ExpVec.eval α' (Ψ t)) s₀)
            (fun i => Pi.single (g.1 i) (1 : ℝ)) := by
    intro g
    have h := iteratedFDeriv_sum_smul_apply (E := Fin μ → ℝ) (F := ℝ) c
      (fun α' t => Work.WilkiesH.ExpVec.eval α' (Ψ t)) n s₀
      (fun i => Pi.single (g.1 i) (1 : ℝ)) (fun α' => hsm α')
    simpa [smul_eq_mul] using h
  rw [Finset.sum_congr rfl (fun g _ => key g)]
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum]

end Work.WilkiesH.Interp
