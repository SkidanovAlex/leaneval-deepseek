import Mathlib
import Submission.Work.RPB.Defs
import Submission.Work.RPB.B5.evenHadamardSplit
import Submission.Work.RPB.B5.sqrtPowSmooth
import Submission.Work.RPB.B5.halfChordSmooth
import Submission.Work.RPB.B3.existsRadiusOpen
import Submission.Work.RPB.B5.phaseDeriv_eq
import Submission.Work.RPB.B5.regularizedPhaseIntegrand
import Submission.Work.RPA3.contDiff_param_intervalIntegral

/-!
# B5: the `ρ`-chart of the chord annulus near the blown-up diagonal

The chord surface `(τ,t,r) ↦ chordSurf c a τ t r` is a smooth *even* function of `r`, so it is a
smooth function of `ρ = r²`; this file makes that explicit: it produces `W : ℝ → ℝ → ℝ → PS`,
`C⁸` in `(τ,t,ρ)` on `Icc 0 1 × univ × Ioo (-ρ₀) ρ₀` for some `ρ₀ > 0`, with

`W τ t (r^2) = chordSurf c a τ t r` for `0 < r < ρ₀`.

The chord data is built from

* the (even, smooth) chord sum `(c τ (t+r) + c τ (t-r))/√2` and squared-chord datum
  `(‖c τ (t+r)‖² + ‖c τ (t-r)‖²)/2 - 1`, made into `ρ`-charts by the even factorisation
  `evenFactorFromSplit` ("even `C^∞` functions of `r` are `C^k` functions of `r²`", obtained here
  from the Hadamard/Taylor splitting `evenHadamardSplit` together with the piecewise square-root
  smoothness `sqrtPowSmooth`), and
* the (even, smooth near `r = 0`) chord phase `a`, made into a `ρ`-chart by `chordPhaseFactor`
  (which uses the smooth even representative of the half chord).

Indeed `chordPS` only sees the *sum* `c τ (t+r) + c τ (t-r)`, the two moduli and the phase lift,
all of which are even in `r`.
-/

open RectangularPegProblem
open Manifold Complex Real

set_option autoImplicit false

noncomputable section

namespace Work.RPB.B5

/-! ## Reassociation maps and the even factorisation `r ↦ r²`

In this section we record the (continuous-linear) changes of variables between the bracketing
`(τ, (t, ρ))` used by the statements below and `((τ, t), ρ)` used by the piecewise
square-root lemma, and then assemble the even factorisation
`f(τ,t,r) = g(τ,t,r²)` from

* `Work.RPB.B5.evenHadamardSplit`: the Hadamard/Taylor splitting
  `f τ t r = Σ_{j<k} r^{2j} c_j(τ,t) + r^{2k} R(τ,t,r)` of an even smooth `f`, and
* `Work.RPB.B5.sqrtPowSmooth`: `ρ ↦ ρ^k • R (x, √ρ)` (two branches) is `C^k`.
-/

/-- `(τ, (t, r)) ↦ (τ, t)` is smooth. -/
lemma rhoChartPair_contDiff : ContDiff ℝ (((⊤ : ℕ∞) : WithTop ℕ∞))
    (fun z : ℝ × (ℝ × ℝ) => (z.1, z.2.1)) := by
  have h1 : ContDiff ℝ (((⊤ : ℕ∞) : WithTop ℕ∞))
      (fun z : ℝ × (ℝ × ℝ) => z.1) := contDiff_fst
  have h2 : ContDiff ℝ (((⊤ : ℕ∞) : WithTop ℕ∞))
      (fun z : ℝ × (ℝ × ℝ) => z.2.1) :=
    (contDiff_fst : ContDiff ℝ (((⊤ : ℕ∞) : WithTop ℕ∞))
      (fun z : ℝ × ℝ => z.1)).comp contDiff_snd
  exact h1.prodMk h2

/-- `((τ, t), r) ↦ (τ, (t, r))` is smooth. -/
lemma rhoChartUnassoc_contDiff : ContDiff ℝ (((⊤ : ℕ∞) : WithTop ℕ∞))
    (fun z : (ℝ × ℝ) × ℝ => (z.1.1, (z.1.2, z.2))) := by
  have h1 : ContDiff ℝ (((⊤ : ℕ∞) : WithTop ℕ∞))
      (fun z : (ℝ × ℝ) × ℝ => z.1.1) :=
    (contDiff_fst : ContDiff ℝ (((⊤ : ℕ∞) : WithTop ℕ∞))
      (fun z : ℝ × ℝ => z.1)).comp contDiff_fst
  have h2 : ContDiff ℝ (((⊤ : ℕ∞) : WithTop ℕ∞))
      (fun z : (ℝ × ℝ) × ℝ => z.1.2) :=
    (contDiff_snd : ContDiff ℝ (((⊤ : ℕ∞) : WithTop ℕ∞))
      (fun z : ℝ × ℝ => z.2)).comp contDiff_fst
  have h3 : ContDiff ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) (fun z : (ℝ × ℝ) × ℝ => z.2) := contDiff_snd
  exact h1.prodMk (h2.prodMk h3)

/-- `(τ, (t, ρ)) ↦ ((τ, t), ρ)` is smooth. -/
lemma rhoChartAssoc_contDiff : ContDiff ℝ (((⊤ : ℕ∞) : WithTop ℕ∞))
    (fun z : ℝ × (ℝ × ℝ) => ((z.1, z.2.1), z.2.2)) := by
  have h1 : ContDiff ℝ (((⊤ : ℕ∞) : WithTop ℕ∞))
      (fun z : ℝ × (ℝ × ℝ) => z.1) := contDiff_fst
  have h2 : ContDiff ℝ (((⊤ : ℕ∞) : WithTop ℕ∞))
      (fun z : ℝ × (ℝ × ℝ) => z.2.1) :=
    (contDiff_fst : ContDiff ℝ (((⊤ : ℕ∞) : WithTop ℕ∞))
      (fun z : ℝ × ℝ => z.1)).comp contDiff_snd
  have h3 : ContDiff ℝ (((⊤ : ℕ∞) : WithTop ℕ∞))
      (fun z : ℝ × (ℝ × ℝ) => z.2.2) :=
    (contDiff_snd : ContDiff ℝ (((⊤ : ℕ∞) : WithTop ℕ∞))
      (fun z : ℝ × ℝ => z.2)).comp contDiff_snd
  exact (h1.prodMk h2).prodMk h3

/-- **Even factorisation.**  An even `C^∞` function of `r` (jointly in the parameters `τ,t`) is a
`C^k` function of `ρ = r²`. -/
theorem evenFactorFromSplit {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E]
    (f : ℝ → ℝ → ℝ → E) (k : ℕ)
    (hf : ContDiff ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) (fun z : ℝ × (ℝ × ℝ) => f z.1 z.2.1 z.2.2))
    (heven : ∀ τ t r, f τ t (-r) = f τ t r) :
    ∃ g : ℝ → ℝ → ℝ → E,
      ContDiff ℝ k (fun z : ℝ × (ℝ × ℝ) => g z.1 z.2.1 z.2.2) ∧
      ∀ τ t ρ, 0 ≤ ρ → g τ t ρ = f τ t (Real.sqrt ρ) := by
  obtain ⟨c, R, hc, hR, hsplit⟩ := evenHadamardSplit f k hf heven
  refine ⟨fun τ t ρ => (∑ j : Fin k, ρ ^ (j : ℕ) • c j τ t) +
    (if 0 ≤ ρ then ρ ^ k • R τ t (Real.sqrt ρ) else ρ ^ k • R τ t (Real.sqrt (-ρ))), ?_, ?_⟩
  · have hsum : ContDiff ℝ k
        (fun z : ℝ × (ℝ × ℝ) => ∑ j : Fin k, z.2.2 ^ (j : ℕ) • c j z.1 z.2.1) := by
      refine ContDiff.sum (fun j _ => ?_)
      have hcj : ContDiff ℝ k (fun z : ℝ × (ℝ × ℝ) => c j z.1 z.2.1) := by
        have h0 : ContDiff ℝ (((⊤ : ℕ∞) : WithTop ℕ∞))
            ((fun x : ℝ × ℝ => c j x.1 x.2) ∘ (fun z : ℝ × (ℝ × ℝ) => (z.1, z.2.1))) :=
          (hc j).comp rhoChartPair_contDiff
        exact h0.of_le (by exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤))
      exact ((contDiff_snd.comp contDiff_snd).pow _).smul hcj
    have hR' : ContDiff ℝ (((⊤ : ℕ∞) : WithTop ℕ∞))
        (fun z : (ℝ × ℝ) × ℝ => R z.1.1 z.1.2 z.2) := hR.comp rhoChartUnassoc_contDiff
    have hPW := sqrtPowSmooth (X := ℝ × ℝ) (fun x : ℝ × ℝ => fun r : ℝ => R x.1 x.2 r) k hR'
    have hcomp : ContDiff ℝ k
        (fun z : ℝ × (ℝ × ℝ) =>
          if 0 ≤ z.2.2 then z.2.2 ^ k • R z.1 z.2.1 (Real.sqrt z.2.2)
          else z.2.2 ^ k • R z.1 z.2.1 (Real.sqrt (-z.2.2))) :=
      hPW.comp (rhoChartAssoc_contDiff.of_le (by exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤)))
    exact hsum.add hcomp
  · intro τ t ρ hρ
    simp only [if_pos hρ]
    show (∑ j : Fin k, ρ ^ (j : ℕ) • c j τ t) + ρ ^ k • R τ t (Real.sqrt ρ)
      = f τ t (Real.sqrt ρ)
    rw [hsplit τ t (Real.sqrt ρ)]
    congr 1
    · refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [pow_mul, Real.sq_sqrt hρ]
    · rw [pow_mul, Real.sq_sqrt hρ]


/-- The chord sum `(c τ (t+r) + c τ (t-r))/√2`: the reduced coordinate of the chord `(c τ (t+r),
c τ (t-r))` up to the phase factor.  It is an even `C^∞` function of `r`. -/
def chordSumChart (c : ℝ → ℝ → ℂ) (τ t r : ℝ) : ℂ :=
  (c τ (t + r) + c τ (t - r)) / (Real.sqrt 2 : ℂ)

/-- The squared chord datum `(‖c τ (t+r)‖² + ‖c τ (t-r)‖²)/2 - 1`, the `p₂`-component of
`chordPS (c τ (t+r)) (c τ (t-r)) a`.  It is an even `C^∞` function of `r`. -/
def chordModChart (c : ℝ → ℝ → ℂ) (τ t r : ℝ) : ℝ :=
  (‖c τ (t + r)‖ ^ 2 + ‖c τ (t - r)‖ ^ 2) / 2 - 1

lemma chordSumChart_even (c : ℝ → ℝ → ℂ) :
    ∀ τ t r, chordSumChart c τ t (-r) = chordSumChart c τ t r := by
  intro τ t r
  unfold chordSumChart
  have h1 : t + -r = t - r := by ring
  have h2 : t - -r = t + r := by ring
  rw [h1, h2, add_comm]

lemma chordModChart_even (c : ℝ → ℝ → ℂ) :
    ∀ τ t r, chordModChart c τ t (-r) = chordModChart c τ t r := by
  intro τ t r
  unfold chordModChart
  have h1 : t + -r = t - r := by ring
  have h2 : t - -r = t + r := by ring
  rw [h1, h2, add_comm]

lemma chordSumChart_contDiff (c : ℝ → ℝ → ℂ)
    (hcs : ContDiff ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) (fun z : ℝ × ℝ => c z.1 z.2)) :
    ContDiff ℝ (((⊤ : ℕ∞) : WithTop ℕ∞))
      (fun z : ℝ × (ℝ × ℝ) => chordSumChart c z.1 z.2.1 z.2.2) := by
  have h1 : ContDiff ℝ (((⊤ : ℕ∞) : WithTop ℕ∞))
      (fun z : ℝ × (ℝ × ℝ) => c z.1 (z.2.1 + z.2.2)) := by
    have hg : ContDiff ℝ (((⊤ : ℕ∞) : WithTop ℕ∞))
        (fun z : ℝ × (ℝ × ℝ) => (z.1, z.2.1 + z.2.2)) :=
      (contDiff_fst : ContDiff ℝ (((⊤ : ℕ∞) : WithTop ℕ∞))
          (fun z : ℝ × (ℝ × ℝ) => z.1)).prodMk
        (((contDiff_fst : ContDiff ℝ (((⊤ : ℕ∞) : WithTop ℕ∞))
            (fun z : ℝ × ℝ => z.1)).comp
          (contDiff_snd : ContDiff ℝ (((⊤ : ℕ∞) : WithTop ℕ∞))
            (fun z : ℝ × (ℝ × ℝ) => z.2))).add
        ((contDiff_snd : ContDiff ℝ (((⊤ : ℕ∞) : WithTop ℕ∞))
            (fun z : ℝ × ℝ => z.2)).comp
          (contDiff_snd : ContDiff ℝ (((⊤ : ℕ∞) : WithTop ℕ∞))
            (fun z : ℝ × (ℝ × ℝ) => z.2))))
    exact hcs.comp hg
  have h2 : ContDiff ℝ (((⊤ : ℕ∞) : WithTop ℕ∞))
      (fun z : ℝ × (ℝ × ℝ) => c z.1 (z.2.1 - z.2.2)) := by
    have hg : ContDiff ℝ (((⊤ : ℕ∞) : WithTop ℕ∞))
        (fun z : ℝ × (ℝ × ℝ) => (z.1, z.2.1 - z.2.2)) :=
      (contDiff_fst : ContDiff ℝ (((⊤ : ℕ∞) : WithTop ℕ∞))
          (fun z : ℝ × (ℝ × ℝ) => z.1)).prodMk
        (((contDiff_fst : ContDiff ℝ (((⊤ : ℕ∞) : WithTop ℕ∞))
            (fun z : ℝ × ℝ => z.1)).comp
          (contDiff_snd : ContDiff ℝ (((⊤ : ℕ∞) : WithTop ℕ∞))
            (fun z : ℝ × (ℝ × ℝ) => z.2))).sub
        ((contDiff_snd : ContDiff ℝ (((⊤ : ℕ∞) : WithTop ℕ∞))
            (fun z : ℝ × ℝ => z.2)).comp
          (contDiff_snd : ContDiff ℝ (((⊤ : ℕ∞) : WithTop ℕ∞))
            (fun z : ℝ × (ℝ × ℝ) => z.2))))
    exact hcs.comp hg
  have h3 : ContDiff ℝ (((⊤ : ℕ∞) : WithTop ℕ∞))
      (fun z : ℝ × (ℝ × ℝ) => c z.1 (z.2.1 + z.2.2) + c z.1 (z.2.1 - z.2.2)) := h1.add h2
  have h4 := h3.div_const (Real.sqrt 2 : ℂ)
  exact contDiffOn_univ.mp ((h4.contDiffOn).congr (fun z _ => rfl))

lemma chordModChart_contDiff (c : ℝ → ℝ → ℂ)
    (hcs : ContDiff ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) (fun z : ℝ × ℝ => c z.1 z.2)) :
    ContDiff ℝ (((⊤ : ℕ∞) : WithTop ℕ∞))
      (fun z : ℝ × (ℝ × ℝ) => chordModChart c z.1 z.2.1 z.2.2) := by
  have key : ∀ w : ℂ, ‖w‖ ^ 2 = w.re * w.re + w.im * w.im := by
    intro w; rw [Complex.sq_norm, Complex.normSq_apply]
  have hplus : ContDiff ℝ (((⊤ : ℕ∞) : WithTop ℕ∞))
      (fun z : ℝ × (ℝ × ℝ) => c z.1 (z.2.1 + z.2.2)) := by
    have hg : ContDiff ℝ (((⊤ : ℕ∞) : WithTop ℕ∞))
        (fun z : ℝ × (ℝ × ℝ) => (z.1, z.2.1 + z.2.2)) :=
      (contDiff_fst : ContDiff ℝ (((⊤ : ℕ∞) : WithTop ℕ∞))
          (fun z : ℝ × (ℝ × ℝ) => z.1)).prodMk
        (((contDiff_fst : ContDiff ℝ (((⊤ : ℕ∞) : WithTop ℕ∞))
            (fun z : ℝ × ℝ => z.1)).comp
          (contDiff_snd : ContDiff ℝ (((⊤ : ℕ∞) : WithTop ℕ∞))
            (fun z : ℝ × (ℝ × ℝ) => z.2))).add
        ((contDiff_snd : ContDiff ℝ (((⊤ : ℕ∞) : WithTop ℕ∞))
            (fun z : ℝ × ℝ => z.2)).comp
          (contDiff_snd : ContDiff ℝ (((⊤ : ℕ∞) : WithTop ℕ∞))
            (fun z : ℝ × (ℝ × ℝ) => z.2))))
    exact hcs.comp hg
  have hminus : ContDiff ℝ (((⊤ : ℕ∞) : WithTop ℕ∞))
      (fun z : ℝ × (ℝ × ℝ) => c z.1 (z.2.1 - z.2.2)) := by
    have hg : ContDiff ℝ (((⊤ : ℕ∞) : WithTop ℕ∞))
        (fun z : ℝ × (ℝ × ℝ) => (z.1, z.2.1 - z.2.2)) :=
      (contDiff_fst : ContDiff ℝ (((⊤ : ℕ∞) : WithTop ℕ∞))
          (fun z : ℝ × (ℝ × ℝ) => z.1)).prodMk
        (((contDiff_fst : ContDiff ℝ (((⊤ : ℕ∞) : WithTop ℕ∞))
            (fun z : ℝ × ℝ => z.1)).comp
          (contDiff_snd : ContDiff ℝ (((⊤ : ℕ∞) : WithTop ℕ∞))
            (fun z : ℝ × (ℝ × ℝ) => z.2))).sub
        ((contDiff_snd : ContDiff ℝ (((⊤ : ℕ∞) : WithTop ℕ∞))
            (fun z : ℝ × ℝ => z.2)).comp
          (contDiff_snd : ContDiff ℝ (((⊤ : ℕ∞) : WithTop ℕ∞))
            (fun z : ℝ × (ℝ × ℝ) => z.2))))
    exact hcs.comp hg
  have h1 : ContDiff ℝ (((⊤ : ℕ∞) : WithTop ℕ∞))
      (fun z : ℝ × (ℝ × ℝ) => (c z.1 (z.2.1 + z.2.2)).re * (c z.1 (z.2.1 + z.2.2)).re
        + (c z.1 (z.2.1 + z.2.2)).im * (c z.1 (z.2.1 + z.2.2)).im) :=
    ((Complex.reCLM.contDiff.comp hplus).mul (Complex.reCLM.contDiff.comp hplus)).add
      ((Complex.imCLM.contDiff.comp hplus).mul (Complex.imCLM.contDiff.comp hplus))
  have h2 : ContDiff ℝ (((⊤ : ℕ∞) : WithTop ℕ∞))
      (fun z : ℝ × (ℝ × ℝ) => (c z.1 (z.2.1 - z.2.2)).re * (c z.1 (z.2.1 - z.2.2)).re
        + (c z.1 (z.2.1 - z.2.2)).im * (c z.1 (z.2.1 - z.2.2)).im) :=
    ((Complex.reCLM.contDiff.comp hminus).mul (Complex.reCLM.contDiff.comp hminus)).add
      ((Complex.imCLM.contDiff.comp hminus).mul (Complex.imCLM.contDiff.comp hminus))
  have h3 : ContDiff ℝ (((⊤ : ℕ∞) : WithTop ℕ∞))
      (fun z : ℝ × (ℝ × ℝ) =>
        ((c z.1 (z.2.1 + z.2.2)).re * (c z.1 (z.2.1 + z.2.2)).re
          + (c z.1 (z.2.1 + z.2.2)).im * (c z.1 (z.2.1 + z.2.2)).im
          + ((c z.1 (z.2.1 - z.2.2)).re * (c z.1 (z.2.1 - z.2.2)).re
            + (c z.1 (z.2.1 - z.2.2)).im * (c z.1 (z.2.1 - z.2.2)).im)) / 2 - 1) :=
    ((h1.add h2).div_const 2).sub contDiff_const
  exact contDiffOn_univ.mp
    ((h3.contDiffOn).congr (fun z _ => by simp only [chordModChart, key]))

end Work.RPB.B5
