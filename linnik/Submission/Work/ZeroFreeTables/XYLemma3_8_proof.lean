/-
# ZeroFreeTables — `XYLemma3_8_proof`

**[X] Lemma 3.8** (Xylouris, arXiv:0906.2749) in the order-2 case, i.e. the input
`Work.ZeroFreeTables.XYLemma3_8` of AREA 3: for a *real* character `χ₁` (`χ₁² = 1`) whose
zero `ρ₁` is non-real and realises the minimal `λ` among all non-principal zeros with
`|Im| ≤ 10`, one has `λ₁ = (1 - Re ρ₁)·log q ≥ 0.628`.

The proof is the order-2 (`ord χ₁ = 2`) slice of Xylouris's `λ₁`-estimates (his Table 11,
`ord χ₁ = 2` row), in three steps:

* **(a) `λ₁ ≥ 0.518`** — HB Lemma 9.5 (`XY.Lam1Lower`, the `P₃` engine at `h = 2`);
* **(b) `λ' ≥ 1` for the other zeros of `χ₁` in the strip `|Im| ≤ 4`** — Xylouris's
  `λ₀`-estimate (`XY.LamPrimeLowerV`), proved from the order-2 *Nebenfall* inequality
  `XY.NebenfallOrd2V` (his (4.14) at `k = 1`, an eight-term `K`-sum positivity combined
  with HB Lemmas 5.2/5.3), the supremum bounds `XY.LamPrimeSup`
  (`sup G, sup H ≤ 1/25`) and the test-function values `XY.LamPrimeFVal`; the arithmetic
  closes with `-697/5400 < 0`.
* **(c) the `F`-method inequality** `0 ≤ xyMain λ₁ + 240` (`XY.FMethodOrd2`, HB (9.16) at
  `λ* = 1`) together with the numerical core `xyMain λ₁ + 240 < 0` for `λ₁ ≤ 0.628`
  (`XY.xyMainLt`).

(a)–(c) are contradictory, so `λ₁ > 0.628`.

**Height bookkeeping.**  The Nebenfall of (b) evaluates the eight `K`-sums at the heights
`0, γ', γ₁, γ₁ ∓ γ', 2γ₁, 2γ₁ ∓ γ'` (`γ' = Im u`, `γ₁ = Im ρ₁`) and HB Lemma 5.2 windows have
radius `δ < 1`, so every *window* zero lies in `|Im| ≤ 2 + 5 + δ < 10`: the frozen minimality
`IsMin1WideAt 10` therefore applies to every window zero, which is exactly what the retention
lemma `XY.KsumWindowKeepFinsetV` (HB Lemma 5.2 with a retained nilpotent-free `Finset` of
zeros on the left of `s`, and its order hypothesis weakened to the retained zeros *outside*
the window) needs.  The sibling statements with `|Im u| ≤ 10` (`XY.NebenfallOrd2`,
`XY.LamPrimeNebenfall`, `XY/LamPrimeLower.lean`) are FALSE for this reason — their windows
reach `12 + δ > 10` — and are not used here.

The F-method inequality of (c) only needs the `λ'`-bound of (b) for the window zeros of the
points `β₁ + iγ₁`, `β₁ + 3iγ₁` (`|γ₁| ≤ 1`), i.e. at heights `≤ 3 + δ < 4`, which is why
`|Im u| ≤ 4` is the form in which (b) is consumed.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.HBProps
import Submission.Work.ZeroFreeTables.XYDefs
import Submission.Work.ZeroFreeTables.XY.Lam1Lower
import Submission.Work.ZeroFreeTables.XY.LamPrimeLowerV
import Submission.Work.ZeroFreeTables.XY.FMethodOrd2
import Submission.Work.ZeroFreeTables.XY.xyMainLt

namespace Work.ZeroFreeTables

open DirichletCharacter Complex
open Work.LinnikContract
open Work.ZeroFreeTables.XY

theorem XYLemma3_8_proof : Work.ZeroFreeTables.XYLemma3_8 := by
  obtain ⟨qA, hA⟩ := Lam1Lower
  obtain ⟨qB, hB⟩ := LamPrimeLowerV
  obtain ⟨qC, hC⟩ := FMethodOrd2
  refine ⟨max (max qA qB) qC, ?_⟩
  intro q hq hqne χ₁ ρ₁ hm hsq him
  haveI : NeZero q := hqne
  have hqA : qA ≤ q := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hq)
  have hqB : qB ≤ q := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hq)
  have hqC : qC ≤ q := le_trans (le_max_right _ _) hq
  by_contra hcon
  push_neg at hcon
  have hle : lamOf q ρ₁ ≤ 628/1000 := le_of_lt hcon
  have h518 : 518/1000 ≤ lamOf q ρ₁ := hA q hqA χ₁ ρ₁ hm hsq him
  have hprime : ∀ u : ℂ, zeroMult χ₁ u ≠ 0 → |u.im| ≤ 4 → u ≠ ρ₁ →
      u ≠ starRingEnd ℂ ρ₁ → 1 ≤ lamOf q u := by
    intro u hzu hu hu1 hu2
    exact hB q hqB χ₁ ρ₁ hm hsq him hle u hzu (le_trans hu (by norm_num)) hu1 hu2
  have hmeth : 0 ≤ xyMain (lamOf q ρ₁) + 240 :=
    hC q hqC χ₁ ρ₁ hm hsq him hle h518 hprime
  have hneg : xyMain (lamOf q ρ₁) + 240 < 0 := xyMainLt (lamOf q ρ₁) hle
  linarith

end Work.ZeroFreeTables
