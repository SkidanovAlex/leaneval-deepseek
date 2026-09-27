import Mathlib
import Submission.Work.EQ.DefsCore
import Submission.Work.EQ.charValDefs
import Submission.Work.EQ.charVal_aux
import Submission.Work.EQ.charVal_main

/-! Guidance from the project lead (the requester):

ROUTE: read Submission/Work/EQ/DESIGN.md and DESIGN_CORE.md (orchestrator designs; your lemma is one node). Defs: Submission/Work/EQ/Defs.lean + DefsCore.lean (namespace Work.EQ; do NOT edit). The proved UNIFORMIZATION library is in this workspace (Submission.UnifMain etc.; see DESIGN_CORE 'Library use'). NOTE: importing UnifMain makes `open Topology` resolve to Work.Topology — write `open _root_.Topology`.

# charVal_props: the characteristic semigroup (Rychlik Lemma 13, (110)) (1–2k)

**Claim.** For a word returning to `A₁`, `μ = charVal` is real in `(0,1]`. `μ = 1` only for the
principal leaf. `{μ ≥ η}` is finite.

**Numerically**: `μ(TF) = 0.4406`, `μ(TFTF) = 0.1941`, `μ(TTFF) = 0.1179` (a = 3/10).

**Route.**
* At an axis centre `x'`, the backward step multiplies `w` by `(x'-b)/(x'+b)` (the inverse of
  `w' = w(x'+b)/(x'-b)`); this is `1/λ` at `A₁`. The derivative matrix is diagonal on the axis, so
  `charVal ε = ∏ over the steps of λ·(x'-b)/(x'+b)` (Rychlik (110)).
* The factor depends only on the centre `x'` of the point being inverted, not on the branch. Steps
  out of `A₁` contribute `1`, whichever branch is taken. A step out of a centre `x' = -1/2+2k`, `k ≠ 0`, contributes
  `r(x') = λ|(x'-b)/(x'+b)|`. Checked by hand: `r(x') ≤ ϑ := max(r(3/2), r(-5/2)) < 1`. For
  `x' < 0`, `(|x'|+b)/(|x'|-b)` decreases in `|x'|` and equals `1/λ` at `|x'| = 1/2`. For `x' > 0`
  the factor is `< 1`. All factors are positive, since no centre lies in `(-b, b)`.
* So `μ ≥ η` bounds the number of visits by `log η / log ϑ`. Each visit has `r(x') ≥ η`, which
  bounds `|x'|`. This leaves finitely many products.
* `μ = 1` forces zero visits. Then every step is the branch fixing `A₁`, i.e. the principal one.
  By `germC_facts`, `fan ε = germC`.

**Check.** `TF` (a = 3/10): centres `A₁ → 3/2 → A₁`, `μ = λ·(3/2-b)/(3/2+b) = 0.4406`, which matches
the numerics.
-/

namespace Work.EQ

/-- **The characteristic semigroup (Rychlik Lemma 13, end of Thm 7).** Characteristic values
of fan maps returning to `A₁` are real in `(0, 1]`, equal `1` only for the principal leaf, and
only finitely many exceed any positive bound. -/
theorem charVal_props {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) :
    ∃ δ : ℝ, 0 < δ ∧
      (∀ ε : List Bool, fan a h ε 0 = ((-1 / 2 : ℂ), (0 : ℂ)) →
        (charVal a h ε).im = 0 ∧ 0 < (charVal a h ε).re ∧ (charVal a h ε).re ≤ 1 ∧
        (charVal a h ε = 1 → Set.EqOn (fan a h ε) (germC a h) (Metric.ball 0 δ))) ∧
      ∀ η : ℝ, 0 < η →
        {μ : ℂ | ∃ ε : List Bool, fan a h ε 0 = ((-1 / 2 : ℂ), (0 : ℂ)) ∧
          charVal a h ε = μ ∧ η ≤ ‖μ‖}.Finite := by
  obtain ⟨-, -, -, δ₀, hδ₀, hinv⟩ := germC_diff_at_zero ha0 ha1 hh
  refine ⟨δ₀, hδ₀, ?_, ?_⟩
  · intro ε hε
    obtain ⟨w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15⟩ :=
      walk_bounds (a := a) ha0 ha1
    have hcv := charVal_of_closed ha0 ha1 hh hε
    have hclosed := stAux_eq_zero_of_closed ha0 ha1 hh hε
    have hpos := w10 ε.reverse 0
    have hbound := w12 ε.reverse hclosed
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hcv]; simp
    · rw [hcv]; simpa using hpos
    · rw [hcv]; simpa using hbound
    · intro h1
      have hwt : wtAux a ε.reverse 0 = 1 := by
        have h2 : ((wtAux a ε.reverse 0 : ℝ) : ℂ) = 1 := by rw [← hcv]; exact h1
        exact_mod_cast h2
      have hall : ∀ c ∈ ε.reverse, c = true := w13 ε.reverse hclosed hwt
      refine fan_eq_germC_of_all_true ha0 ha1 hh hinv ε ?_
      intro c hc
      exact hall c (List.mem_reverse.mpr hc)
  · intro η hη
    exact finite_charVal_set ha0 ha1 hh η hη

end Work.EQ
