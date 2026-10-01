import Mathlib
import Submission.Work.LinnikAreas.BGTZ.GEstimateDefs
import Submission.Work.LinnikAreas.BGTZSetup
import Submission.Work.LinnikAreas.BGTZ.SieveLocalBound
import Submission.Work.LinnikAreas.BGTZ.SieveGsumTermLe

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.LinnikAreas.BGTZ

/-- **The trivial half of BGTZ Lemma 4.3**: on the critical line the sieve function `G(s,χ)` is
dominated by the double sum `gpairsum χ₁ R = Σ_{d,e ≤ R} f([d,e])[d,e]^{-1/2}`.

The proof is the triangle inequality together with the local bound `‖sieveLocal‖ ≤ gwt`: for
`s.re = 1/2`,

`‖sieveG‖ = ‖Σ_{d,e ≤ R} θ_d θ_e ∏_{p | [d,e]} sieveLocal‖ ≤ Σ_{d,e ≤ R} ‖θ_d θ_e ∏_{p | [d,e]} sieveLocal‖`,

and each summand is at most `gw χ₁ [d,e]` (`Work.LinnikAreas.BGTZ.SieveGsumTermLe`, which combines
`SieveLocalBound` prime by prime with `|θ_d|, |θ_e| ≤ 1` and `IsSieveWeight`'s vanishing on
non-squarefree indices).  Summing gives `Σ_{d,e ≤ R} gw χ₁ [d,e] = gpairsum χ₁ R`. -/
theorem SieveGLePairsum {q : ℕ} [NeZero q] (χ₁ χ : DirichletCharacter ℂ q) (hχ₁ : χ₁ ^ 2 = 1)
    {R : ℕ} {θw : ℕ → ℝ} (hθ : Work.LinnikAreas.BGTZ.IsSieveWeight R θw) (t : ℝ) :
    ‖Work.LinnikAreas.BGTZ.sieveG χ₁ R θw (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) χ‖
      ≤ Work.LinnikAreas.BGTZ.gpairsum χ₁ R := by
  have hs : (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I).re = 1 / 2 := by simp
  have hpair : ∀ d ∈ Finset.Icc 1 R, ∀ e ∈ Finset.Icc 1 R,
      ‖(θw d : ℂ) * (θw e : ℂ)
          * ∏ p ∈ (Nat.lcm d e).primeFactors,
              sieveLocal χ₁ χ (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) p‖
        ≤ gw χ₁ (Nat.lcm d e) :=
    fun d _ e _ => SieveGsumTermLe χ₁ χ hθ hs d e
  calc ‖sieveG χ₁ R θw (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) χ‖
      = ‖∑ d ∈ Finset.Icc 1 R, ∑ e ∈ Finset.Icc 1 R,
            (θw d : ℂ) * (θw e : ℂ)
              * ∏ p ∈ (Nat.lcm d e).primeFactors,
                  sieveLocal χ₁ χ (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) p‖ := rfl
    _ ≤ ∑ d ∈ Finset.Icc 1 R, ‖∑ e ∈ Finset.Icc 1 R,
            (θw d : ℂ) * (θw e : ℂ)
              * ∏ p ∈ (Nat.lcm d e).primeFactors,
                  sieveLocal χ₁ χ (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) p‖ :=
          norm_sum_le _ _
    _ ≤ ∑ d ∈ Finset.Icc 1 R, ∑ e ∈ Finset.Icc 1 R,
            ‖(θw d : ℂ) * (θw e : ℂ)
              * ∏ p ∈ (Nat.lcm d e).primeFactors,
                  sieveLocal χ₁ χ (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) p‖ :=
          Finset.sum_le_sum (fun d _ => norm_sum_le _ _)
    _ ≤ ∑ d ∈ Finset.Icc 1 R, ∑ e ∈ Finset.Icc 1 R, gw χ₁ (Nat.lcm d e) :=
          Finset.sum_le_sum (fun d hd => Finset.sum_le_sum (fun e he => hpair d hd e he))
    _ = gpairsum χ₁ R := rfl

end Work.LinnikAreas.BGTZ
