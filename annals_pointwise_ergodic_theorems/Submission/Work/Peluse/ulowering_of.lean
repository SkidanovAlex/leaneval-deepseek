import Mathlib
import Submission.Work.Peluse.Ulower.ss_nongap
import Submission.Work.Peluse.Ulower.ss_gap_full

/-!
# `Work.Peluse.ulowering_of`

Peluse's chapter (iii), in the normalisation used by `PeluseCrux`: `U^s`-control of the dual
function `F₂ = dualFn N P f₀ f₁` at the shift set `c[D]` forces a long progression average of
`f₁`.  The proof is the paper's §§7-9 (degree lowering `U^s → U²`, the `U²`-inverse theorem
`h1`, the major-arc statement `h2`, and the §9 argument), of which the workspace now has two
independent, sorry-free chapters:

* `Work.Peluse.Ulower.ss_nongap` — the *non-gap* regime `¬ (2 N^d < N₀ ∧ N < 2 N₀)`, i.e. the
  declared support range `N₀` and the polynomial scale `N^d` comparable, so that the balanced
  chapters `ss_degree_lowering` + `ss_u2_level` + `ss_transfer` + `ss_conversion` apply.  It
  covers the whole shift range `D ≤ N^d`.
* `Work.Peluse.Ulower.ss_gap_case_full` — the *gap* regime `2 N^d < N₀ ∧ N < 2 N₀` (support much
  larger than the polynomial scale), where the balanced chapters cannot be applied at all; here
  the argument is the localisation + the `D`-lossy balanced core + the transfer.  This is the
  copy of `Ulower/ss_gap_case` with the shift bound relaxed from `D ≤ N^d/2` to `D ≤ N^d` (in
  that proof the bound is used only to deduce `D ≤ N^d`).

The two chapters produce the display with their own constants; the assembly below takes the
pointwise maxima (`ss_mono` for the monotonicity of the display in `(C, K)`) and splits on the
gap condition.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

open scoped BigOperators
open Polynomial

namespace Work.Peluse

noncomputable section

/-- **Peluse's chapter (iii)**: `U^s`-control of the dual function implies a long progression on
which `f₁` has large average (Lemma 3.9 iterated, Lemma 2.4, Lemma 3.10 and §9). -/
theorem ulowering_of {P : Polynomial ℤ} (hd : 2 ≤ P.natDegree)
    (h1 : Work.Peluse.PeluseU2Inverse) (h2 : Work.Peluse.PeluseMajorArc P) :
    Work.Peluse.PeluseULowering P := by
  intro s hs A' hA'
  obtain ⟨Cg, Kg, hCg1, hKg1, hgap⟩ :=
    Work.Peluse.Ulower.ss_gap_case_full (P := P) hd h1 h2 s hs
  obtain ⟨Cn, Kn, hCn1, hKn1, hnongap⟩ :=
    Work.Peluse.Ulower.ss_nongap (P := P) hd h1 h2 s hs
  refine ⟨max Cg Cn, max Kg Kn, le_trans hCg1 (le_max_left _ _),
    le_trans hKg1 (le_max_left _ _), ?_⟩
  intro N N₀ D f₀ f₁ δ hd2 hN hN₀ hsc1 hsc2 hδ0 hδ1 hD1 hDle hf0 hf1 hb0 hb1 hhyp
  have hDM : (D : ℝ) ≤ ((N ^ P.natDegree : ℕ) : ℝ) := by rw [Nat.cast_pow]; exact hDle
  change Work.Peluse.Ulower.Display P (max Cg Cn) (max Kg Kn) A' N N₀ D f₁ δ
  rw [Work.Peluse.Ulower.display_iff_displayAt]
  by_cases hgapc : 2 * (N : ℝ) ^ P.natDegree < (N₀ : ℝ) ∧ (N : ℝ) < 2 * (N₀ : ℝ)
  · have hg : Work.Peluse.Ulower.Display P Cg Kg A' N N₀ D f₁ δ :=
      hgap A' N N₀ D f₀ f₁ δ hd2 hA' hN hN₀ hsc1 hsc2 hgapc.1 hgapc.2 hδ0 hδ1 hD1 hDle
        hf0 hf1 hb0 hb1 hhyp
    rw [Work.Peluse.Ulower.display_iff_displayAt] at hg
    exact Work.Peluse.Ulower.ss_mono (le_max_left _ _) (le_max_left _ _) A' (N ^ P.natDegree)
      N N₀ D f₁ δ hA' hδ0 hδ1 hN hD1 hDM hg
  · have hn : Work.Peluse.Ulower.Display P Cn Kn A' N N₀ D f₁ δ :=
      hnongap A' N N₀ D f₀ f₁ δ hd2 hA' hN hN₀ hsc1 hsc2 hδ0 hδ1 hD1 hDle hgapc
        hf0 hf1 hb0 hb1 hhyp
    rw [Work.Peluse.Ulower.display_iff_displayAt] at hn
    exact Work.Peluse.Ulower.ss_mono (le_max_right _ _) (le_max_right _ _) A' (N ^ P.natDegree)
      N N₀ D f₁ δ hA' hδ0 hδ1 hN hD1 hDM hn

end

end Work.Peluse
