/-
# `Work.LinnikAreas.ownRepelNW.turanPowerStepWeyl`

The Turán power step of the Deuring–Heilbronn repulsion argument with the *Weyl-type `kMult` input
discharged*.

The Turán step (`Work.LinnikAreas.DhExplicit.turanPowerStepConst`, following
Kadiri–Ng–Wong arXiv:1902.08640 §2) takes two analytic inputs about the zeros of
`ζ_K = ζ · L(·,χ)`:

* `hweyl` -- the inverse-square ("Weyl") zero-sum bound
  `∑'_v kMult χ v · (1/‖c-v‖² + 1/‖c+iγ'-v‖²) ≤ Cw · log N` for `2 ≤ c ≤ 10`, `|γ'| ≤ 1`
  (the *norm-square / Weyl-shift* input, KNW Lemma 2.6 with the shifted centre);
* `hdiff` -- the differentiated explicit formula (KNW (2.5)–(2.6)) in "exceptional zero removed"
  form.

Here `hweyl` is *proved*, not assumed: `Work.LinnikAreas.ownRepelNW.kMultWeylBound` supplies it
with an absolute constant and a threshold `q₀`.  Instantiating the Turán step at that constant
turns the power inequality into an unconditional statement in its Weyl input: there is an absolute
`C > 0` such that, for all large `N` and every quadratic primitive non-trivial `χ mod N`, the Turán
power `j` of the pair `(ρ₀, ρ)` satisfies `j ≤ 10000 · C · log N`.

This is the step that lets the chain drop the hypothesis
`Work.LinnikAreas.DhExplicit.MassBound` (which `DhExplicit/turanPowerIneq.lean` uses *only* to
manufacture a Weyl bound): `MassBound` is in fact the already-proved statement
`Work.LinnikAreas.DhExplicit.zeroSumKMultBound` written out, so the Weyl input of the Turán route
is available outright.

The remaining hypothesis `hdiff` is the target of `ownRepelNW/diffExplicitIneq.lean` (the sibling
delegation), so it is kept as a hypothesis here.
-/
import Mathlib
import Submission.Work.LinnikAreas.P3Rect.Work_LinnikAreas_DhK_Defs
import Submission.Work.LinnikAreas.P3Rect.Work_LinnikAreas_ownRepelNW_kMultWeylBound
import Submission.Work.LinnikAreas.P3Rect.Work_LinnikAreas_DhExplicit_turanPowerStepConst

open scoped Classical BigOperators
noncomputable section

namespace Work.LinnikAreas.ownRepelNW

/-- **The Turán power step with the Weyl-type `kMult` input discharged.**

There is an absolute constant `C > 0` and a threshold `N₀` such that for every `N ≥ N₀` and every
quadratic, primitive, non-trivial Dirichlet character `χ mod N`, any pair of zeros `ρ₀` (real,
with `1 - Re ρ₀ ≤ 1/100`) and `ρ` (with `|Im ρ| ≤ 1`, `ρ ≠ ρ₀`, `1 - Re ρ ≤ 1/3`) of `Λ(·,χ)`
satisfies: given the differentiated explicit formula `hdiff`, there is a Turán power
`1 ≤ j` with `j ≤ 10000 · C · log N` and
`(1/36)/(5 - Re ρ)^{2j} ≤ 4j(1 - Re ρ₀)/4^{2j+1}`.

The constant and the threshold come from `kMultWeylBound`; the power inequality itself is
`Work.LinnikAreas.DhExplicit.turanPowerStepConst` at that constant. -/
theorem turanPowerStepWeyl :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ [NeZero N]
      (χ : DirichletCharacter ℂ N) (ρ₀ ρ : ℂ),
      χ ≠ 1 → χ.IsPrimitive → χ ^ 2 = 1 → ρ₀.im = 0 →
      analyticOrderNatAt (DirichletCharacter.completedLFunction χ) ρ₀ ≠ 0 →
      analyticOrderNatAt (DirichletCharacter.completedLFunction χ) ρ ≠ 0 →
      |ρ.im| ≤ 1 → ρ ≠ ρ₀ → 1 - ρ₀.re ≤ 1 / 100 → 1 - ρ.re ≤ 1 / 3 →
      (∀ (j : ℕ), 1 ≤ j → ∀ {c γ' : ℝ}, 5 ≤ c →
        Summable (fun v : ℂ => (Work.LinnikAreas.DhK.kMult χ v : ℝ) *
          ((1 / ((c : ℂ) - v) ^ (2 * j)).re
            + (1 / ((c : ℂ) + Complex.I * (γ' : ℂ) - v) ^ (2 * j)).re)) ∧
        4 * (j : ℝ) * (1 - ρ₀.re) / (c - 1) ^ (2 * j + 1) ≥
          ∑' v : ℂ, (if v = ρ₀ then 0 else (Work.LinnikAreas.DhK.kMult χ v : ℝ)) *
            ((1 / ((c : ℂ) - v) ^ (2 * j)).re
              + (1 / ((c : ℂ) + Complex.I * (γ' : ℂ) - v) ^ (2 * j)).re)) →
      ∃ j : ℕ, 1 ≤ j ∧ (j : ℝ) ≤ 10000 * C * Real.log (N : ℝ) ∧
        (1 / 36) / (5 - ρ.re) ^ (2 * j)
          ≤ 4 * (j : ℝ) * (1 - ρ₀.re) / (4 : ℝ) ^ (2 * j + 1) := by
  obtain ⟨C, hCpos, q₀, hC⟩ := kMultWeylBound
  refine ⟨C, hCpos, max q₀ 3, ?_⟩
  intro N hN _inst χ ρ₀ ρ hχ hχprim hχ2 hρ₀im hzρ₀ hzρ himρ hne hρ₀le hρle hdiff
  have hq₀ : q₀ ≤ N := le_trans (le_max_left q₀ 3) hN
  have hN3 : 3 ≤ N := le_trans (le_max_right q₀ 3) hN
  exact Work.LinnikAreas.DhExplicit.turanPowerStepConst (N := N) (Cw := C) χ ρ₀ ρ hN3
    hχ hχprim hχ2 hρ₀im hzρ₀ hzρ himρ hne hρ₀le hρle hCpos
    (fun {c γ'} hc hc10 hγ' => hC N hq₀ χ hχ hχprim hχ2 hc hc10 hγ') hdiff


/-- **The `DhExplicit` input `MassBound` is already proved.**

`Work.LinnikAreas.DhExplicit.MassBound` (declared in `DhExplicit/Inputs.lean` as "the
inverse-square zero-sum bound (KNW Lemma 2.6)") is definitionally the statement of the proved
`Work.LinnikAreas.DhExplicit.zeroSumKMultBound`, so it holds outright.  This matters because
`DhExplicit/turanPowerIneq.lean` uses `MassBound` *only* to manufacture the Weyl input `hweyl`
of the Turán step; with this lemma that route carries no unproved analytic hypothesis for the Weyl
input. -/
theorem massBound_of_zeroSumKMultBound : Work.LinnikAreas.DhExplicit.MassBound :=
  Work.LinnikAreas.DhExplicit.zeroSumKMultBound

end Work.LinnikAreas.ownRepelNW
