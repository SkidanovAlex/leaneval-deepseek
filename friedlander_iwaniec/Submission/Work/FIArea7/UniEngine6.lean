/-
# `Submission.Work.FIArea7.UniEngine6` — the (17.10) engine of area 7, assembled

This file assembles, in one place, the *identities* and the two *errors* that reduce the uniform
(paper's `W`) cut `Work.FIArea7.WUni6` to the character-expanded main term
`Work.FIArea7.WUniOmega6Pull6Char` of (17.10):

  `WUni6 Pa X β = WUniOmega6Pull6 Pa X β`                        (`UniAssembled6`, proved)
  `WUniOmega6Pull6Moll Pa X β K = uniModeSum Pa X β K ε`         (`WUniOmega6Pull6Moll_eq_uniModeSum`, here)
  `uniModeSumFree Pa X β K ε = WUniOmega6Pull6Char Pa X β K ε`   (`UniCharFree6`, proved)
  `‖WUniOmega6Pull6 − WUniOmega6Pull6Moll‖ ≤ C(N³/K+N)(log N)⁶`  (child, proved)
  `‖uniModeSum − uniModeSumFree‖ ≤ Eguard`                       (child, in flight; taken as a hypothesis)

so that

  `‖WUni6 − WUniOmega6Pull6Char‖ ≤ C(N³/K+N)(log N)⁶ + Eguard`.

The point of the file is that it fixes the *interface* of the two errors: with the §53.1 choice
`K = X³(log N)²⁰` the first error is `≪ N²/X`, and the second is the coprimality-guard removal
(`NOTES.md` §55), whose shape must be `(Pz⁻¹+X⁻¹)N²·log¹` — see `NOTES.md` §57.6: an error carrying
an extra `(Pz⁻¹+X⁻¹)N²(log N)^{1+ε}` is **not** absorbable by the contract's fixed constant.
-/
import Mathlib
import Submission.Work.FIArea7.UniAssembled6
import Submission.Work.FIArea7.WUniOmega6Pull6Moll_eq_modes
import Submission.Work.FIArea7.uniModePair_eq_uniModeChar
import Submission.Work.FIArea7.WUniOmega6Pull6_sub_Moll_le
import Submission.Work.FIArea7.UniCharFree6

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.FIArea7

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## 1. The mollified pull-out sum is the mode sum -/

/-- The per-`(b,e)` summand of the mode expansion, stated as its own lemma so that the
`(b,e)`-level rewriting is fully type-annotated. -/
private lemma charTerm_eq {Pa : Work.FITop.Params} {φ : ℝ} {z0 : GaussianInt}
    {β : GaussianInt → ℂ} (hβ : Work.FITop4.IsBetaCoeff6 Pa φ z0 β) {ε : GaussianInt → ℤ}
    (hε : ∀ z1 z2 : GaussianInt, Work.FITop3.InPolarBox Pa φ z1 →
      Work.FITop3.InPolarBox Pa φ z2 → reflSign z1 z2 = ε z1 * ε z2)
    (b e : ℕ) (hb : 1 ≤ b) (he : 1 ≤ e) (K : ℕ) :
    (((2 * Real.log 2 + Real.log 4 : ℝ)) : ℂ) * uniModePair Pa b e β 0
        + ∑ k ∈ evenFreq K, (1 / (|k| : ℝ) : ℂ) * uniModePair Pa b e β k
      = (((2 * Real.log 2 + Real.log 4 : ℝ)) : ℂ) * uniModeChar Pa b e β 0 ε
        + ∑ k ∈ evenFreq K, (1 / (|k| : ℝ) : ℂ) * uniModeChar Pa b e β k ε := by
  have hne : 4 * b * e ≠ 0 := four_mul_ne_zero_of_pos hb he
  have key : ∀ k : ℤ, uniModePair Pa b e β k = uniModeChar Pa b e β k ε :=
    fun k => @uniModePair_eq_uniModeChar Pa φ z0 β hβ b e k ⟨hne⟩ ε hε
  rw [key 0]
  have hsum : (∑ k ∈ evenFreq K, (1 / (|k| : ℝ) : ℂ) * uniModePair Pa b e β k)
      = (∑ k ∈ evenFreq K, (1 / (|k| : ℝ) : ℂ) * uniModeChar Pa b e β k ε) :=
    Finset.sum_congr rfl (fun k _ => by rw [key k])
  rw [hsum]

/-- **`WUniOmega6Pull6Moll = uniModeSum`.**  `Work.FIArea7.WUniOmega6Pull6Moll_eq_modes` expands the
mollified pull-out sum into its Fourier modes at the *pair* object `uniModePair`, and
`Work.FIArea7.uniModePair_eq_uniModeChar` identifies each pair object with the `unitInd`/`ω`-form
`uniModeChar` that `uniModeSum` is built from. -/
theorem WUniOmega6Pull6Moll_eq_uniModeSum {Pa : Work.FITop.Params} {φ : ℝ} {z0 : GaussianInt}
    {β : GaussianInt → ℂ} (hβ : Work.FITop4.IsBetaCoeff6 Pa φ z0 β) {ε : GaussianInt → ℤ}
    (hε : ∀ z1 z2 : GaussianInt, Work.FITop3.InPolarBox Pa φ z1 →
      Work.FITop3.InPolarBox Pa φ z2 → reflSign z1 z2 = ε z1 * ε z2)
    (X : ℕ) (K : ℕ) :
    WUniOmega6Pull6Moll Pa X β K = uniModeSum Pa X β K ε := by
  rw [Work.FIArea7.WUniOmega6Pull6Moll_eq_modes, uniModeSum]
  refine congrArg (fun t : ℂ => 2 * t) ?_
  refine Finset.sum_congr rfl (fun b hb => ?_)
  refine Finset.sum_congr rfl (fun e he => ?_)
  obtain ⟨hb1, _⟩ := Finset.mem_Icc.mp hb
  obtain ⟨he1, _⟩ := Finset.mem_Icc.mp he
  rw [charTerm_eq hβ hε b e hb1 he1 K]

/-! ## 2. The engine: `WUni6` against the (17.10) main term -/

/-! ## 3. The engine in the `|Δ|`-cut route (the shapes the assembly actually needs)

The mollifier error of §2 (`WUniOmega6Pull6_sub_Moll_le`, `(N³/K+N)log⁶`) is **too large** to close
the contract's target `X⁻¹N²log N` for any admissible `K` — see `NOTES.md` §58.3.  The engine must
therefore be run through the `|Δ|`-cut `WUniOmega6Pull6Cut` (where the Fourier-series error of
`logFac6` is *uniform*, `4(1+θ)N/(KM)`, `UniMollify6.abs_logFac6_sub_series_le`), i.e.

  `‖WUni6 − Char‖ ≤ Ecut + End + Eguard`,

with `Ecut = ‖WUniOmega6Pull6 − Cut‖` (the child `WUniOmega6Pull6_sub_Cut_le`),
`End = ‖Cut − WUniOmega6Pull6Moll‖` (the near-diagonal difference, the child
`WUniOmega6Pull6Cut_sub_Moll_le`) and `Eguard` the guard removal. -/

/-- **The (17.10) engine, cut route.**  `WUni6` is `WUniOmega6Pull6` (proved), which is `Cut` plus
`Ecut`, which is `Moll` plus `End`; `Moll = uniModeSum` and `uniModeSumFree = Char` (both proved), so
the difference `WUni6 − Char` is `(Pull6 − Cut) + (Cut − Moll) + (uniModeSum − uniModeSumFree)` and
the triangle inequality gives the stated bound. -/
theorem WUni6_sub_Char_le_cut {Pa : Work.FITop.Params} {X : ℕ} {φ : ℝ} {z0 : GaussianInt}
    {β : GaussianInt → ℂ} {ε : GaussianInt → ℤ}
    (hβ : Work.FITop4.IsBetaCoeff6 Pa φ z0 β) (hX : 1 ≤ X)
    (hε : ∀ z1 z2 : GaussianInt, Work.FITop3.InPolarBox Pa φ z1 →
      Work.FITop3.InPolarBox Pa φ z2 → reflSign z1 z2 = ε z1 * ε z2)
    (K M : ℕ) {Eguard Ecut End : ℝ}
    (hG : ‖uniModeSum Pa X β K ε - uniModeSumFree Pa X β K ε‖ ≤ Eguard)
    (hC : ‖WUniOmega6Pull6 Pa X β - WUniOmega6Pull6Cut Pa X β K M‖ ≤ Ecut)
    (hN : ‖WUniOmega6Pull6Cut Pa X β K M - WUniOmega6Pull6Moll Pa X β K‖ ≤ End) :
    ‖WUni6 Pa X β - WUniOmega6Pull6Char Pa X β K ε‖ ≤ Ecut + End + Eguard := by
  have hMoll : WUniOmega6Pull6Moll Pa X β K = uniModeSum Pa X β K ε :=
    WUniOmega6Pull6Moll_eq_uniModeSum hβ hε X K
  have hFree : uniModeSumFree Pa X β K ε = WUniOmega6Pull6Char Pa X β K ε :=
    uniModeSumFree_eq_WUniOmega6Pull6Char Pa X β K ε
  have hsplit : WUni6 Pa X β - WUniOmega6Pull6Char Pa X β K ε
      = (WUniOmega6Pull6 Pa X β - WUniOmega6Pull6Cut Pa X β K M)
        + ((WUniOmega6Pull6Cut Pa X β K M - WUniOmega6Pull6Moll Pa X β K)
          + (uniModeSum Pa X β K ε - uniModeSumFree Pa X β K ε)) := by
    rw [WUni6_eq_WUniOmega6Pull6 Pa X φ z0 β hβ hX, hMoll, hFree]
    ring
  have h2 : ‖(WUniOmega6Pull6Cut Pa X β K M - WUniOmega6Pull6Moll Pa X β K)
        + (uniModeSum Pa X β K ε - uniModeSumFree Pa X β K ε)‖ ≤ End + Eguard :=
    le_trans (norm_add_le _ _) (add_le_add hN hG)
  have h1 : ‖(WUniOmega6Pull6 Pa X β - WUniOmega6Pull6Cut Pa X β K M)
        + ((WUniOmega6Pull6Cut Pa X β K M - WUniOmega6Pull6Moll Pa X β K)
          + (uniModeSum Pa X β K ε - uniModeSumFree Pa X β K ε))‖ ≤ Ecut + (End + Eguard) :=
    le_trans (norm_add_le _ _) (add_le_add hC h2)
  rw [hsplit]
  linarith [h1]

end

end Work.FIArea7
