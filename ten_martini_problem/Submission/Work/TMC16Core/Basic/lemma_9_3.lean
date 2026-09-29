import Mathlib
import Submission.Work.TMC16Core.Defs
import Submission.Work.TMC16Core.Basic.lagrange_eval
import Submission.Work.TMC16Core.Basic.exp_arith

namespace Work.TMC16Core.Basic

/-- AJ §9, Lemma `nongen` (non-generation of uniform families): a family of `k+1` phases
which all lie in `A_{k,L-ε}` cannot be `ε₁`-uniform, provided the gap-condition
`4(k+1)e^{L-ε} < e^{k(ε-ε₁)}` holds.  The proof is the Lagrange interpolation argument
of the paper: writing `Q_k` in the Lagrange form at the nodes `cos 2π z j` and evaluating
at `cos 2π θ₀`, the size of `Q_k` at the nodes (from `A_{k,L-ε}`) fights the size of the
Lagrange kernels (from `ε₁`-uniformity). -/
theorem lemma_9_3 {ι : Type*} [Fintype ι] [DecidableEq ι] {α lam : ℝ} {E : ℂ} {k : ℕ}
    {L ε ε₁ : ℝ} {Q : Polynomial ℂ} {z : ι → ℝ}
    (hQ : ∀ x : ℝ, Q.eval (((Real.cos (2 * Real.pi * x) : ℝ)) : ℂ) =
        Work.TMC16Core.pd α lam (x - (((k : ℝ) - 1) / 2) * α) E (k + 1))
    (hdeg : Q.natDegree ≤ k) (hcard : Fintype.card ι = k + 1)
    (hA : ∀ j : ι, z j ∈ Work.TMC16Core.AkSet α lam E k (L - ε))
    (θ₀ : ℝ) (h0 : Real.exp ((k : ℝ) * L) / 4 ≤
        ‖Work.TMC16Core.pd α lam (θ₀ - (((k : ℝ) - 1) / 2) * α) E (k + 1)‖)
    (hε : ε₁ < ε)
    (hk : 4 * ((k : ℝ) + 1) * Real.exp (L - ε) < Real.exp ((k : ℝ) * (ε - ε₁))) :
    ¬ Work.TMC16Core.Uniform ε₁ z := by
  intro hU
  -- The nodes are the cosine values of the phases, viewed as complex numbers.
  set u : ι → ℝ := fun i => Real.cos (2 * Real.pi * z i) with hu
  set v : ι → ℂ := fun i => ((u i : ℝ) : ℂ) with hv
  -- The evaluation point associated with θ₀.
  set w : ℝ := Real.cos (2 * Real.pi * θ₀) with hw
  have norm_real : ∀ r : ℝ, ‖((r : ℝ) : ℂ)‖ = |r| := fun r => by
    rw [Complex.norm_def, Complex.normSq_ofReal, ← sq, Real.sqrt_sq_eq_abs]
  -- The nodes are pairwise distinct, since `Uniform` demands distinct cosines.
  have hinj : Function.Injective v := by
    intro a b hab
    have hab' : ((u a : ℝ) : ℂ) = ((u b : ℝ) : ℂ) := hab
    have h1 : u a = u b := Complex.ofReal_injective hab'
    by_contra hne
    exact hU.1 a b hne h1
  have hdeg' : Q.natDegree < Fintype.card ι := by rw [hcard]; omega
  have hwmem : w ∈ Set.Icc (-1 : ℝ) 1 := by
    rw [hw]; exact ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
  -- Value of `Q` at the point associated with `θ₀`.
  have hQw : Q.eval ((w : ℝ) : ℂ) =
      Work.TMC16Core.pd α lam (θ₀ - (((k : ℝ) - 1) / 2) * α) E (k + 1) := by
    rw [hw]; exact hQ θ₀
  have hQw_ge : Real.exp ((k : ℝ) * L) / 4 ≤ ‖Q.eval ((w : ℝ) : ℂ)‖ := by
    rw [hQw]; exact h0
  -- Values of `Q` at the nodes, bounded using `A_{k,L-ε}`.
  have hQi : ∀ i : ι, ‖Q.eval (v i)‖ ≤ Real.exp (((k : ℝ) + 1) * (L - ε)) := by
    intro i
    have hAi := hA i
    simp only [Work.TMC16Core.AkSet, Set.mem_ofPred_eq] at hAi
    have hvi : Q.eval (v i) =
        Work.TMC16Core.pd α lam (z i - (((k : ℝ) - 1) / 2) * α) E (k + 1) :=
      hQ (z i)
    rw [hvi]; exact hAi
  -- Lagrange kernels bounded using `ε₁`-uniformity.
  have hPb : ∀ i : ι, |∏ j ∈ (Finset.univ : Finset ι).erase i, (w - u j) / (u i - u j)| ≤
      Real.exp ((k : ℝ) * ε₁) := by
    intro i
    have hUi := hU.2 i w hwmem
    have hcardR : ((Fintype.card ι : ℝ) - 1) * ε₁ = (k : ℝ) * ε₁ := by
      have hc : (Fintype.card ι : ℝ) = (k : ℝ) + 1 := by rw [hcard]; push_cast; ring
      rw [hc]; ring
    rw [hcardR] at hUi
    exact le_of_lt hUi
  -- Lagrange interpolation identity at `w`.
  have hLagr : Q.eval ((w : ℝ) : ℂ) =
      ∑ i : ι, (Q.eval (v i) / ∏ j ∈ (Finset.univ : Finset ι).erase i, (v i - v j)) *
        ∏ j ∈ (Finset.univ : Finset ι).erase i, (((w : ℝ) : ℂ) - v j) :=
    lagrange_eval Q v ((w : ℝ) : ℂ) hinj hdeg'
  -- Norms of the two products appearing in each Lagrange term.
  have hDnorm : ∀ i : ι, ‖∏ j ∈ (Finset.univ : Finset ι).erase i, (v i - v j)‖ =
      ∏ j ∈ (Finset.univ : Finset ι).erase i, |u i - u j| := by
    intro i
    rw [norm_prod]
    apply Finset.prod_congr rfl
    intro j hj
    have hsub : v i - v j = ((u i - u j : ℝ) : ℂ) := by
      simp only [hv]
      exact (Complex.ofReal_sub (u i) (u j)).symm
    rw [hsub, norm_real]
  have hNnorm : ∀ i : ι, ‖∏ j ∈ (Finset.univ : Finset ι).erase i, (((w : ℝ) : ℂ) - v j)‖ =
      ∏ j ∈ (Finset.univ : Finset ι).erase i, |w - u j| := by
    intro i
    rw [norm_prod]
    apply Finset.prod_congr rfl
    intro j hj
    have hsub : ((w : ℝ) : ℂ) - v j = ((w - u j : ℝ) : ℂ) := by
      simp only [hv]
      exact (Complex.ofReal_sub w (u j)).symm
    rw [hsub, norm_real]
  -- Quotient of the two norms equals the modulus of the Lagrange kernel.
  have hratio : ∀ i : ι, ‖∏ j ∈ (Finset.univ : Finset ι).erase i, (((w : ℝ) : ℂ) - v j)‖ /
      ‖∏ j ∈ (Finset.univ : Finset ι).erase i, (v i - v j)‖ =
      |∏ j ∈ (Finset.univ : Finset ι).erase i, (w - u j) / (u i - u j)| := by
    intro i
    rw [hNnorm i, hDnorm i]
    rw [Finset.abs_prod]
    rw [show (∏ j ∈ (Finset.univ : Finset ι).erase i, |(w - u j) / (u i - u j)|)
        = ∏ j ∈ (Finset.univ : Finset ι).erase i, |w - u j| / |u i - u j| from
        Finset.prod_congr rfl (fun j hj => by rw [abs_div])]
    rw [Finset.prod_div_distrib]
  -- Bound on the modulus of each Lagrange term.
  have hterm : ∀ i : ι, ‖(Q.eval (v i) / ∏ j ∈ (Finset.univ : Finset ι).erase i, (v i - v j)) *
        ∏ j ∈ (Finset.univ : Finset ι).erase i, (((w : ℝ) : ℂ) - v j)‖ ≤
      Real.exp (((k : ℝ) + 1) * (L - ε)) * Real.exp ((k : ℝ) * ε₁) := by
    intro i
    have hrw : ‖(Q.eval (v i) / ∏ j ∈ (Finset.univ : Finset ι).erase i, (v i - v j)) *
        ∏ j ∈ (Finset.univ : Finset ι).erase i, (((w : ℝ) : ℂ) - v j)‖ =
        ‖Q.eval (v i)‖ * |∏ j ∈ (Finset.univ : Finset ι).erase i, (w - u j) / (u i - u j)| := by
      rw [norm_mul, norm_div]
      rw [show (‖Q.eval (v i)‖ / ‖∏ j ∈ (Finset.univ : Finset ι).erase i, (v i - v j)‖) *
            ‖∏ j ∈ (Finset.univ : Finset ι).erase i, (((w : ℝ) : ℂ) - v j)‖
          = ‖Q.eval (v i)‖ * (‖∏ j ∈ (Finset.univ : Finset ι).erase i, (((w : ℝ) : ℂ) - v j)‖ /
            ‖∏ j ∈ (Finset.univ : Finset ι).erase i, (v i - v j)‖) from by ring]
      rw [hratio i]
    rw [hrw]
    exact mul_le_mul (hQi i) (hPb i) (abs_nonneg _) (Real.exp_pos _).le
  -- Summing the term bounds.
  have hsum : ‖Q.eval ((w : ℝ) : ℂ)‖ ≤ (Fintype.card ι : ℝ) *
      (Real.exp (((k : ℝ) + 1) * (L - ε)) * Real.exp ((k : ℝ) * ε₁)) := by
    rw [hLagr]
    calc ‖∑ i : ι, (Q.eval (v i) / ∏ j ∈ (Finset.univ : Finset ι).erase i, (v i - v j)) *
            ∏ j ∈ (Finset.univ : Finset ι).erase i, (((w : ℝ) : ℂ) - v j)‖
        ≤ ∑ i : ι, ‖(Q.eval (v i) / ∏ j ∈ (Finset.univ : Finset ι).erase i, (v i - v j)) *
            ∏ j ∈ (Finset.univ : Finset ι).erase i, (((w : ℝ) : ℂ) - v j)‖ := norm_sum_le _ _
      _ ≤ ∑ i : ι, Real.exp (((k : ℝ) + 1) * (L - ε)) * Real.exp ((k : ℝ) * ε₁) :=
            Finset.sum_le_sum (fun i _ => hterm i)
      _ = (Fintype.card ι : ℝ) *
            (Real.exp (((k : ℝ) + 1) * (L - ε)) * Real.exp ((k : ℝ) * ε₁)) := by
            simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  -- The hypothesis `hk` converts into the strict upper bound.
  have hfinal : (Fintype.card ι : ℝ) *
      (Real.exp (((k : ℝ) + 1) * (L - ε)) * Real.exp ((k : ℝ) * ε₁)) <
      Real.exp ((k : ℝ) * L) / 4 := by
    have hc : (Fintype.card ι : ℝ) = (k : ℝ) + 1 := by rw [hcard]; push_cast; ring
    rw [hc]
    exact exp_arith hk
  linarith

end Work.TMC16Core.Basic
