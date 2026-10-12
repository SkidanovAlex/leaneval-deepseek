import ChallengeDeps
import Submission.Work.MGroupInput.mGroupWindowCapped_of_perStateBound
import Submission.Work.MGroupInput.perState_of_simpleA2Two7b
import Submission.Work.MGroupInput.perState_zeroCond
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.MGroupInput.FinalWiring` — the `m`-arm at its usable window

This closes the chapter's chain: the two PROVED per-state branches

* `Work.MGroupInput.perState_of_simpleA2Two` (`0 < cS1`, needs `SimpleA2Two`,
  the `cgap`-absorption `hab`, the `CorrWord` bound `hcorr`, `μs³ ≥ 20` and
  `8μ + E₁ ≤ u`),
* `Work.MGroupInput.perState_zeroCond` (`cS1 = 0`, needs the diluteness `hgap`
  and `6μ ≤ u`),

together with the PROVED per-state-to-infimum reduction
`Work.MGroupInput.mGroupWindowCapped_of_perStateBound`, give the capped
windowed `m`-arm bound

    `MGroupWindowCapped (8 + E₁/μ) 9 s μ v h c₀ cgap`.

Fed to `Work.MGroupInput.mGroupLinearCapped_of_mGroupWindowCapped` and the
PROVED capped two-arm assembly
`Work.MGroupInput.d4_dl_bound_of_groups_windowCapped`, this is what replaces
the (false) `Work.DLRepoint.MGroupInput` in the DL re-point.

**The one remaining window-arithmetic gap** (recorded honestly): the assembly
applies the `m`-arm at the split's group count `n′ = ⌈Cnμβ⌉` and needs BOTH
`n′/s³ ≥ 8μ + E₁` (the `m`-arm) and `n″ < n′ ≤ 9μβ` (the corpus's block window
`u ≤ 9μ`, `hblk`).  With `Cn := 8 + E₁/μ` the first holds, and the second needs
`(9 + E₁/μ)μ` — an `E₁/μ`-wide overhang past `9μ`.  Since `E₁` can be taken
`≤ 1/s³ ≤ μ/20` (using `SimpleA2Small`'s arbitrary `ε`), the overhang is
`≤ 5\%`, so the corpus's `9μ` constant needs widening by a few percent
(or the m-arm's window lowered, which costs `μs³`).  Everything else in the
chain is proved.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.MGroupInput

open Submission BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **The `m`-arm on its usable capped window** (from the two proved per-state
branches). -/
theorem mGroupWindowCapped_of_simpleA2Two {s μ c₀ cgap E₁ E₂ : ℝ} {v : ℝ³ → ℝ} {R : ℝ}
    (hR : 0 < R) (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) (hv_memL1 : MemLp v 1)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRs : R ≤ s * chiR0) (hav : 0 < a v) (hs : 0 < s) (hμ : 0 < μ)
    (hμs : 20 ≤ μ * s ^ 3) (hcgap : 1 / (36 * s ^ 2) ≤ cgap)
    (hE₁ : 0 ≤ E₁) (hE₁μ : E₁ ≤ μ)
    (hA2 : SimpleA2Two E₁ E₂ s c₀ v h)
    (hab : ∀ P : ℕ, 1 ≤ P → (P : ℝ) / s ^ 3 ≤ 9 * μ →
      Work.SmallBoxA0.totNCoeff s μ v + E₂ * (a v) * (((P : ℝ) + 1) / s ^ 3) ≤ cgap)
    (hgap : (μ * (a v) * s ^ 2) * (1600 + 1850 * chiSup ^ 2) ≤ 1)
    (hcorr : ∀ (P : ℕ) (Φ : X P → ℝ), 1 ≤ P → ContDiff ℝ ∞ Φ →
      (∫ x in abox P s, (Φ x) ^ 2) = 1 → (P : ℝ) / s ^ 3 ≤ 9 * μ → 0 < cS1 s Φ →
      2 * (s ^ 3)⁻¹ * Work.SmallBoxA0.CorrWord s h Φ
        ≤ (1 / (72 * s ^ 2)) * cnPlus s Φ + 36 * π * (a v) * μ) :
    MGroupWindowCapped (8 + E₁ / μ) 9 s μ v h c₀ cgap := by
  have hμpos : (0 : ℝ) < μ := hμ
  have hs3 : (0 : ℝ) < s ^ 3 := by positivity
  have hcgap0 : (0 : ℝ) ≤ cgap :=
    le_trans (by positivity : (0:ℝ) ≤ 1 / (36 * s ^ 2)) hcgap
  have hD : g0w0Mass (v := v) h ≤ 8 * Real.pi * (a v) := by
    have hb := (chosen_gomega_integral_bounds (v := v) (R := R) hR hv_nonneg hvrad hv_supp h).2
    simpa [g0w0Mass, g0] using hb
  refine mGroupWindowCapped_of_perStateBound (Cn := 8 + E₁ / μ) (Cn' := 9) (s := s) (μ := μ)
    (v := v) (h := h) (c₀ := c₀) (cgap := cgap) hs ?_
  intro P hP hCn hCn'
  -- density forms
  have hwin : (P : ℝ) / s ^ 3 ≤ 9 * μ := by
    rw [div_le_iff₀ hs3]
    linarith [hCn']
  have hCn'8 : (8 + E₁ / μ) * μ ≤ (P : ℝ) / s ^ 3 := by
    rw [le_div_iff₀ hs3]
    linarith [hCn]
  have hdiv : (8 + E₁ / μ) * μ = 8 * μ + E₁ := by
    rw [add_mul, div_mul_cancel₀ _ (ne_of_gt hμpos)]
  have hCn8 : 8 * μ + E₁ ≤ (P : ℝ) / s ^ 3 := by linarith [hCn'8, hdiv]
  have h6 : 6 * μ ≤ (P : ℝ) / s ^ 3 := by linarith [hCn8, hE₁]
  intro Φ hΦc hnorm
  rcases lt_or_ge (0 : ℝ) (cS1 s Φ) with hpos | hnonpos
  · exact perState_of_simpleA2Two (P := P) (s := s) (μ := μ) (c₀ := c₀) (cgap := cgap)
      (E₁ := E₁) (E₂ := E₂) (v := v) (R := R) hR hv_nonneg hvrad hv_memL1 hv_supp h hRs
      hav hs hμ hμs hcgap0 hD hE₁ hP hwin hCn8 hA2 (hab P hP hwin) Φ hΦc hnorm hpos
      (hcorr P Φ hP hΦc hnorm hwin hpos)
  · have hz : cS1 s Φ = 0 := le_antisymm hnonpos (cS1_nonneg)
    exact perState_zeroCond (P := P) (s := s) (μ := μ) (c₀ := c₀) (cgap := cgap) (v := v)
      (R := R) hR hv_nonneg hvrad hv_memL1 hv_supp h hRs hav hs hμ hcgap hgap hP hwin h6
      Φ hΦc hnorm hz

/-- **The `m`-arm with a window constant `Cn ≤ 8`** — the form the capped
two-arm assembly consumes.  Same proof as `mGroupWindowCapped_of_simpleA2Two`
but on the `7μ` per-state base (`perState_of_simpleA2Two7b`, `μs³ ≥ 10`), so that
`Cn = 7 + E₁/μ ≤ 8` whenever `E₁ ≤ μ` — which is exactly the assembly's
requirement `Cn + 1 ≤ Cn' = 9`. -/
theorem mGroupWindowCapped8_of_simpleA2Two {s μ c₀ cgap E₁ E₂ : ℝ} {v : ℝ³ → ℝ} {R : ℝ}
    (hR : 0 < R) (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) (hv_memL1 : MemLp v 1)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRs : R ≤ s * chiR0) (hav : 0 < a v) (hs : 0 < s) (hμ : 0 < μ)
    (hμs : 10 ≤ μ * s ^ 3) (hcgap : 1 / (36 * s ^ 2) ≤ cgap)
    (hE₁ : 0 ≤ E₁) (hE₁μ : E₁ ≤ μ)
    (hA2 : SimpleA2Two E₁ E₂ s c₀ v h)
    (hab : ∀ P : ℕ, 1 ≤ P → (P : ℝ) / s ^ 3 ≤ 9 * μ →
      Work.SmallBoxA0.totNCoeff s μ v + E₂ * (a v) * (((P : ℝ) + 1) / s ^ 3) ≤ cgap)
    (hgap : (μ * (a v) * s ^ 2) * (1600 + 1850 * chiSup ^ 2) ≤ 1)
    (hcorr : ∀ (P : ℕ) (Φ : X P → ℝ), 1 ≤ P → ContDiff ℝ ∞ Φ →
      (∫ x in abox P s, (Φ x) ^ 2) = 1 → (P : ℝ) / s ^ 3 ≤ 9 * μ → 0 < cS1 s Φ →
      2 * (s ^ 3)⁻¹ * Work.SmallBoxA0.CorrWord s h Φ
        ≤ (1 / (72 * s ^ 2)) * cnPlus s Φ + 36 * π * (a v) * μ) :
    MGroupWindowCapped (7 + E₁ / μ) 9 s μ v h c₀ cgap := by
  have hμpos : (0 : ℝ) < μ := hμ
  have hs3 : (0 : ℝ) < s ^ 3 := by positivity
  have hcgap0 : (0 : ℝ) ≤ cgap :=
    le_trans (by positivity : (0:ℝ) ≤ 1 / (36 * s ^ 2)) hcgap
  have hD : g0w0Mass (v := v) h ≤ 8 * Real.pi * (a v) := by
    have hb := (chosen_gomega_integral_bounds (v := v) (R := R) hR hv_nonneg hvrad hv_supp h).2
    simpa [g0w0Mass, g0] using hb
  refine mGroupWindowCapped_of_perStateBound (Cn := 7 + E₁ / μ) (Cn' := 9) (s := s) (μ := μ)
    (v := v) (h := h) (c₀ := c₀) (cgap := cgap) hs ?_
  intro P hP hCn hCn'
  have hwin : (P : ℝ) / s ^ 3 ≤ 9 * μ := by
    rw [div_le_iff₀ hs3]
    linarith [hCn']
  have hCn'7 : (7 + E₁ / μ) * μ ≤ (P : ℝ) / s ^ 3 := by
    rw [le_div_iff₀ hs3]
    linarith [hCn]
  have hdiv : (7 + E₁ / μ) * μ = 7 * μ + E₁ := by
    rw [add_mul, div_mul_cancel₀ _ (ne_of_gt hμpos)]
  have hCn7 : 7 * μ + E₁ ≤ (P : ℝ) / s ^ 3 := by linarith [hCn'7, hdiv]
  have h6 : 6 * μ ≤ (P : ℝ) / s ^ 3 := by linarith [hCn7, hE₁]
  intro Φ hΦc hnorm
  rcases lt_or_ge (0 : ℝ) (cS1 s Φ) with hpos | hnonpos
  · exact perState_of_simpleA2Two7b (P := P) (s := s) (μ := μ) (c₀ := c₀) (cgap := cgap)
      (E₁ := E₁) (E₂ := E₂) (v := v) (R := R) hR hv_nonneg hvrad hv_memL1 hv_supp h hRs
      hav hs hμ hμs hcgap0 hD hE₁ hP hwin hCn7 hA2 (hab P hP hwin) Φ hΦc hnorm hpos
      (hcorr P Φ hP hΦc hnorm hwin hpos)
  · have hz : cS1 s Φ = 0 := le_antisymm hnonpos (cS1_nonneg)
    exact perState_zeroCond (P := P) (s := s) (μ := μ) (c₀ := c₀) (cgap := cgap) (v := v)
      (R := R) hR hv_nonneg hvrad hv_memL1 hv_supp h hRs hav hs hμ hcgap hgap hP hwin h6
      Φ hΦc hnorm hz

end Work.MGroupInput
