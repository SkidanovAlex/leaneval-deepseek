import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Pert.Ksub2.Setup
import Submission.Work.Pert.pert2v2.shadow_walk_local
import Submission.Work.Pert.pert2v2.walk_Qreg_const
import Submission.Work.Pert.pert2v2.Qp_norm_lower
import Submission.Work.Pert.pert2v2.HsegRow

/-!
# `Work.Pert.pert2v2.ShadowBand` — the `(SHADOW)` row of the two-piece R-block

`Submission/Work/Pert/NOTES_pert2v2_session39.md` §2.  The overlap identity `hcross` of the
`pert2v2` two-piece R-block reduces to the *single-point* statement

  `(SHADOW)`   `‖F^[m] ς - τ₀ (f₀^[m] (d.φ w))‖ < 4`,

where `F = liftF u σ α`, `ς` is the gate point of `w` in the **datum** gate `Qm Ξabs α ∩ Qp Ξabs α`
and `m` is the crux's landing time: `Qp' = ⋃_{w' ∈ Kb} ball (τ₀ (f₀^[m] (d.φ w')), 4)` contains the
ball around the centre, `τ (F^[m] ς) = f^[m] (φ w) = τ ζ_w`, and `τ` is injective on `Qp'`, so
`F^[m] ς = ζ_w` — which is exactly what `Rlow_eq_retOf_level0` (re-run with the walk in the datum
gate) needs.

This file contains the *assembly* of `(SHADOW)`:

* `F0f_iterate` — the model orbit identity `(F0f f₀)^[m] w = τ₀ (f₀^[m] (τ₀ w))` (unconditional:
  `τ₀` is an involution);
* `shadow_of_walks` — `(SHADOW)` from `shadow_walk_local` (the shadowing estimate, with the *local*
  Lipschitz form that `Ksub2.F0f_far_translation` supplies) plus `tau0_Xc'`;
* `F0f_walk_Qp_18` — the model walk in the gate from `F0f_far_translation`'s `≤ 1/8` bound and
  `Qp_norm_lower`;
* `room_sub` — the `b`-margin (the walk room) is `2`-Lipschitz in the point, the input needed to
  transport the waist room of `ς` to `Xc d w`.
-/

namespace Work.Pert.pert2v2

open _root_.MandelDim Complex Set Metric

noncomputable section

/-- The key identity of `F0f f₀ = τ₀ ∘ f₀ ∘ τ₀`: precomposing with the involution `τ₀` turns it
into `τ₀ ∘ f₀`. -/
theorem F0f_tau0 (f₀ : ℂ → ℂ) (u : ℂ) :
    Work.Pert.F0f f₀ (MandelDim.tau0 u) = MandelDim.tau0 (f₀ u) := by
  simp only [Work.Pert.F0f, Work.Pert.tau0_tau0]

/-- **The model orbit identity.**  `F0f f₀ = τ₀ ∘ f₀ ∘ τ₀`, so its `m`-th iterate is
`τ₀ ∘ f₀^[m] ∘ τ₀` — unconditionally, because `MandelDim.tau0` is an involution (`tau0_tau0`, with
no non-vanishing side condition: `τ₀ 0 = 0` by the junk value `1/0 = 0`). -/
theorem F0f_iterate (f₀ : ℂ → ℂ) (m : ℕ) (w : ℂ) :
    (Work.Pert.F0f f₀)^[m] w = MandelDim.tau0 (f₀^[m] (MandelDim.tau0 w)) := by
  induction m with
  | zero => exact (Work.Pert.tau0_tau0 w).symm
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply', F0f_tau0]

/-- **`(SHADOW)`, assembled.**  With the two walk confinements in the gate `Qp Ξ α`, a local
Lipschitz bound for `F0f` at distances `≤ B`, the comparison `‖F - F0f‖ ≤ δ` on the gate, the start
closeness `‖ς - Xc d w‖ ≤ η`, the scale condition `K^m(η + mδ) ≤ B` and the arithmetic
`K^m(η + mδ) < 4`, the perturbed walk from `ς` lands within `4` of the crux's centre
`τ₀ (f₀^[m] (d.φ w))`. -/
theorem shadow_of_walks {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀)
    {Ξ : ℝ} {α : ℂ} {u : ℂ → ℂ} {σ : ℂ} {w ς : ℂ} {m : ℕ} {K η δ B : ℝ}
    (hK : 1 ≤ K) (hη : 0 ≤ η) (hδ : 0 ≤ δ)
    (hstay : ∀ j : ℕ, j ≤ m → (Work.Pert.liftF u σ α)^[j] ς ∈ Work.Pert.Qp Ξ α)
    (hstay₀ : ∀ j : ℕ, j ≤ m → (Work.Pert.F0f f₀)^[j] (Work.Pert.Xc d w) ∈ Work.Pert.Qp Ξ α)
    (hlip : ∀ a ∈ Work.Pert.Qp Ξ α, ∀ b ∈ Work.Pert.Qp Ξ α, ‖a - b‖ ≤ B →
      ‖Work.Pert.F0f f₀ a - Work.Pert.F0f f₀ b‖ ≤ K * ‖a - b‖)
    (hclose : ∀ a ∈ Work.Pert.Qp Ξ α,
      ‖Work.Pert.liftF u σ α a - Work.Pert.F0f f₀ a‖ ≤ δ)
    (hηc : ‖ς - Work.Pert.Xc d w‖ ≤ η)
    (hB : K ^ m * (η + (m : ℝ) * δ) ≤ B)
    (harith : K ^ m * (η + (m : ℝ) * δ) < 4) :
    ‖(Work.Pert.liftF u σ α)^[m] ς - MandelDim.tau0 (f₀^[m] (d.φ w))‖ < 4 := by
  have hsh := shadow_walk_local (F := Work.Pert.liftF u σ α) (F₀ := Work.Pert.F0f f₀)
    (Q := Work.Pert.Qp Ξ α) hK hη hδ hlip hclose hstay hstay₀ hηc hB
  have hmod : (Work.Pert.F0f f₀)^[m] (Work.Pert.Xc d w)
      = MandelDim.tau0 (f₀^[m] (d.φ w)) := by
    rw [F0f_iterate, tau0_Xc']
  rw [hmod] at hsh
  exact lt_of_le_of_lt hsh harith

/-- **The model walk in the gate.**  `F0f f₀` is a `≤ 1/8` near-translation for `‖w‖ ≥ Rf`
(`Ksub2.F0f_far_translation`), and `Qp Ξ α ⊆ {Ξ/2 ≤ ‖·‖}` (`Qp_norm_lower`); hence the walk of
`F0f f₀` from any point of `Qp Ξ α` with enough `b`-margin stays in `Qp Ξ α`.  The room constant is
`1 + 2·(1/8) = 5/4`. -/
theorem F0f_walk_Qp_18 {f₀ : ℂ → ℂ} {Ξ Rf : ℝ} {z : ℂ} {m : ℕ} {α : ℂ}
    (hΞ : 0 < Ξ) (h2R : 2 * Rf ≤ Ξ)
    (hfar : ∀ w : ℂ, Rf ≤ ‖w‖ → ‖Work.Pert.F0f f₀ w - (w + 1)‖ ≤ 1 / 8)
    (hz : z ∈ Work.Pert.Qp Ξ α)
    (hroom : (5 / 4 : ℝ) * (m : ℝ) + 1 ≤
      |(z - (-(Ξ : ℂ) + 1 / α)).im| - (z - (-(Ξ : ℂ) + 1 / α)).re) :
    ∀ j : ℕ, j ≤ m → (Work.Pert.F0f f₀)^[j] z ∈ Work.Pert.Qp Ξ α := by
  have hstep : ∀ w ∈ MandelDim.Qreg (some (Ξ : ℂ)) (some (-(Ξ : ℂ) + 1 / α)),
      ‖Work.Pert.F0f f₀ w - (w + 1)‖ ≤ 1 / 8 := by
    intro w hw
    refine hfar w ?_
    have hwQ : w ∈ Work.Pert.Qp Ξ α := hw
    have h1 := Qp_norm_lower hΞ hwQ
    linarith
  have hroom' : (1 + 2 * (1 / 8 : ℝ)) * (m : ℝ) + 1 ≤
      |(z - (-(Ξ : ℂ) + 1 / α)).im| - (z - (-(Ξ : ℂ) + 1 / α)).re := by
    have hc : (1 + 2 * (1 / 8 : ℝ)) = (5 / 4 : ℝ) := by norm_num
    rw [hc]
    exact hroom
  exact walk_Qreg_const (a := (Ξ : ℂ)) (b := (-(Ξ : ℂ) + 1 / α)) (F := Work.Pert.F0f f₀)
    (by norm_num) (by norm_num) hstep hz hroom'

/-- **The walk room is `2`-Lipschitz in the point.**  The `b`-margin
`z ↦ |(z - b).im| - (z - b).re` decreases by at most `2‖z - z'‖` when the point is moved:
both its terms are `1`-Lipschitz.  This transports the waist room of `ς` to a nearby point
(`Xc d w`, which satisfies `‖Xc d w - ς‖ ≤ C εp` by the modulus of injectivity of the coordinate). -/
theorem room_sub {b z z' : ℂ} :
    |(z - b).im| - (z - b).re ≥ (|(z' - b).im| - (z' - b).re) - 2 * ‖z - z'‖ := by
  have h1 : |(z - b).im| ≥ |(z' - b).im| - ‖z - z'‖ := by
    have h := abs_add_le ((z - b).im) ((z' - b).im - (z - b).im)
    have h2 : (z - b).im + ((z' - b).im - (z - b).im) = (z' - b).im := by ring
    rw [h2] at h
    have h3 : |(z' - b).im - (z - b).im| ≤ ‖z - z'‖ := by
      have h4 : (z' - b).im - (z - b).im = -((z - z').im) := by
        simp only [Complex.sub_im, Complex.neg_im]; ring
      rw [h4, abs_neg]
      exact Complex.abs_im_le_norm _
    have h5 : ‖z - z'‖ = ‖z' - z‖ := norm_sub_rev _ _
    linarith
  have h2 : (z - b).re ≤ (z' - b).re + ‖z - z'‖ := by
    have h3 : (z - b).re - (z' - b).re = (z - z').re := by
      simp only [Complex.sub_re]; ring
    have h4 : (z - z').re ≤ ‖z - z'‖ :=
      le_trans (le_abs_self _) (Complex.abs_re_le_norm _)
    linarith
  linarith

/-- **Transport of the walk room from the waist point `ς` to the nearby point `Xc d w`.**  If the
`b`-margin at `ς` is `≥ (5/4) m + 1 + 2η` and `z` is within `η` of `ς`, then the `b`-margin at `z`
is `≥ (5/4) m + 1` — the room the *model* walk `F0f_walk_Qp_18` needs (defect `1/8` instead of
`1/32`, hence the slightly larger constant `5/4`).  The hypothesis on `ς` is the horizontal room
`Re(1/α) - Im(1/α)` plus the waist slack, hence a `δ₀`-condition. -/
theorem room_transfer {b ς z : ℂ} {m : ℕ} {η : ℝ}
    (hς : (5 / 4 : ℝ) * (m : ℝ) + 1 + 2 * η ≤ |(ς - b).im| - (ς - b).re)
    (hclose : ‖z - ς‖ ≤ η) :
    (5 / 4 : ℝ) * (m : ℝ) + 1 ≤ |(z - b).im| - (z - b).re := by
  have h₁ : (|(ς - b).im| - (ς - b).re) - 2 * ‖z - ς‖ ≤ |(z - b).im| - (z - b).re := by
    have h := room_sub (b := b) (z := z) (z' := ς)
    linarith
  have h₂ : 2 * ‖z - ς‖ ≤ 2 * η := mul_le_mul_of_nonneg_left hclose (by norm_num)
  linarith

end

end Work.Pert.pert2v2
