import Mathlib
import Submission.Work.CLift.defs

namespace Work.CLift

/-- `A21`, `A22` and `c2` are rational functions of `x` (with coefficients depending on
`m, n, r_a, r_b, r_ab`) whose denominators are all multiples of `R2p`.  Hence their
pull-backs along any differentiable `Φ` are differentiable wherever `R2p (Φ z) ≠ 0`. -/
theorem entry_diff (m n : ℕ) (ra rb rab : ℤ) (Φ : ℂ → ℂ) {s : Set ℂ}
    (hΦ : DifferentiableOn ℂ Φ s)
    (hR2 : ∀ z ∈ s, Work.CLift.R2p m n (Φ z) ≠ 0) :
    DifferentiableOn ℂ (fun z => Work.CLift.A21 m n (Φ z)) s ∧
    DifferentiableOn ℂ (fun z => Work.CLift.A22 m n (Φ z)) s ∧
    DifferentiableOn ℂ (fun z => Work.CLift.c2 m n ra rb rab (Φ z)) s := by
  -- the numerator/denominator polynomials are differentiable everywhere on `ℂ`
  have hMu : Differentiable ℂ (fun x : ℂ => Muqp m n x) := by simp only [Muqp]; fun_prop
  have hR2d : Differentiable ℂ (fun x : ℂ => R2p m n x) := by simp only [R2p]; fun_prop
  have hNq : Differentiable ℂ (fun x : ℂ => Nqp m n x) := by simp only [Nqp]; fun_prop
  have hMc : Differentiable ℂ (fun x : ℂ => Mcqp m n ra rb rab x) := by
    simp only [Mcqp]; fun_prop
  -- and so are their compositions with `Φ`
  have hMuΦ : DifferentiableOn ℂ (fun z => Muqp m n (Φ z)) s :=
    hMu.differentiableOn.comp hΦ (t := Set.univ) (fun x _ => Set.mem_univ _)
  have hR2Φ : DifferentiableOn ℂ (fun z => R2p m n (Φ z)) s :=
    hR2d.differentiableOn.comp hΦ (t := Set.univ) (fun x _ => Set.mem_univ _)
  have hNqΦ : DifferentiableOn ℂ (fun z => Nqp m n (Φ z)) s :=
    hNq.differentiableOn.comp hΦ (t := Set.univ) (fun x _ => Set.mem_univ _)
  have hMcΦ : DifferentiableOn ℂ (fun z => Mcqp m n ra rb rab (Φ z)) s :=
    hMc.differentiableOn.comp hΦ (t := Set.univ) (fun x _ => Set.mem_univ _)
  -- a pointwise-quotient wrapper, to keep the elaborated function forms in sync
  have hdiv : ∀ (f g : ℂ → ℂ), DifferentiableOn ℂ f s → DifferentiableOn ℂ g s →
      (∀ z ∈ s, g z ≠ 0) → DifferentiableOn ℂ (fun z => f z / g z) s :=
    fun f g hf hg h => DifferentiableOn.div hf hg h
  refine ⟨?_, ?_, ?_⟩
  · simp only [A21]
    exact hdiv _ _ hMuΦ hR2Φ (fun z hz => hR2 z hz)
  · simp only [A22]
    refine (hdiv _ _ hNqΦ hR2Φ (fun z hz => hR2 z hz)).sub_const (1 / 2)
  · -- `c2 = Mcqp / ((2(a+b)) · R2p)`, rewrite as `(Mcqp / (2(a+b))) / R2p`
    have hfun : (fun z => c2 m n ra rb rab (Φ z))
        = fun z => (Mcqp m n ra rb rab (Φ z) / (2 * ((aa m : ℂ) + (bb n : ℂ))))
            / R2p m n (Φ z) := by
      funext z; simp only [c2]; rw [div_mul_eq_div_div]
    rw [hfun]
    exact hdiv _ _ (hMcΦ.div_const (2 * ((aa m : ℂ) + (bb n : ℂ)))) hR2Φ (fun z hz => hR2 z hz)

end Work.CLift
