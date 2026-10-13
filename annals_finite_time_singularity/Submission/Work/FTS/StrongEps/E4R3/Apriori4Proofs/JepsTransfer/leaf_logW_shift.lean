import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Defs
import Submission.Work.FTS.StrongEps.wtE_shift_le
import Submission.Work.FTS.StrongEps.wtG_shift_le
import Submission.Work.FTS.StrongEps.sinTwo_thShift_bounds
import Submission.Work.FTS.StrongEps.HkSqAux.logJac_shift_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer

set_option autoImplicit false
set_option maxHeartbeats 800000

/-!
# `leaf_logW_shift` — the log-coordinate shift estimate for the leaf weights

The three leaf weights of the `IP4`-unfolding are

  `leafEta = w² sin(2θ)^{-η}`,  `leafOne = w²`,  `leafGam α = w² sin(2θ)^{-γ α}`,

with `w z = (1+z)²/z²`, `η = 99/100`, `γ α = 1 + α/10`.  In the log coordinates
`(s,ζ) = (log z, log tan θ)` the weight `logW w` is the product of the Jacobian `logJac` of the
substitution and `w ∘ Ψ`, and the shift `y ↦ y + p` on the plane corresponds to
`z ↦ z e^{p.1}`, `tan θ ↦ tan θ · e^{p.2}`.  The present file proves that this shift changes
`logW w` by at most `e^{C(|p.1|+|p.2|)}`, in both directions — the hypothesis needed by
`logPair_conv_transfer`.

Everything is elementary and assembled from the shift bounds of the individual factors:

* `logJac_add_le` — `logJac (s+p₁) (ζ+p₂) ≤ e^{4(|p₁|+|p₂|)} logJac s ζ`, from
  `HkSqAux.kappa_shift_core`;
* `wtZ_exp_add_le` — the radial factor `wtZ = w²`, from `wtZ_zShift_le`;
* `sEtaW_thShift_le` / `sGamW_shift_le_sharp` — the angular factors
  `sin(2θ)^{-q}` for `q = η` resp. `q = γ α`, the second one being the sharp
  `e^{(γ α)|p|}`-version of `wtG_shift_le`'s `sGamW_shift_le` (which assumes `α ≤ 1`); it is
  obtained from the two-sided bound `sinTwo_thShift_bounds` by `rpow_shift_le`.

-/

/-! ## Elementary identifications of the shifted arguments -/

/-- The angle `arctan (e^ζ)` always lies in the open quadrant. -/
theorem arctan_exp_mem (ζ : ℝ) :
    Real.arctan (Real.exp ζ) ∈ Set.Ioo 0 (π / 2) :=
  ⟨Real.arctan_pos.mpr (Real.exp_pos ζ), Real.arctan_lt_pi_div_two _⟩

/-- `ζ ↦ ζ + p` is the `θ`-shift `thShift · (-p)` after the identification `θ = arctan (e^ζ)`. -/
theorem arctan_exp_add (ζ p : ℝ) :
    Real.arctan (Real.exp (ζ + p))
      = Work.FTS.StrongEps.thShift (Real.arctan (Real.exp ζ)) (-p) := by
  rw [Work.FTS.StrongEps.thShift, Real.tan_arctan, neg_neg, ← Real.exp_add]

/-- `ζ ↦ ζ + p` is the `z`-shift `zShift · (-p)` after the identification `z = e^ζ`. -/
theorem exp_add_eq_zShift (ζ p : ℝ) :
    Real.exp (ζ + p) = Work.FTS.StrongEps.zShift (Real.exp ζ) (-p) := by
  rw [Work.FTS.StrongEps.zShift, neg_neg, ← Real.exp_add]

/-! ## The Jacobian factor -/

/-- **The Jacobian factor shifts forwards by `e^{4(|p₁|+|p₂|)}`.**  This is
`HkSqAux.kappa_shift_core` (`kappa (ζ+p₂) ≤ e^{2|p₂|+p₂} kappa ζ`) combined with
`Real.exp (s+p₁) = e^s e^{p₁} ≤ e^s e^{|p₁|}`. -/
theorem logJac_add_le (s ζ p₁ p₂ : ℝ) :
    Work.FTS.StrongEps.HkSqAux.logJac (s + p₁) (ζ + p₂)
      ≤ Real.exp (4 * (|p₁| + |p₂|)) * Work.FTS.StrongEps.HkSqAux.logJac s ζ := by
  have hk : Work.FTS.StrongEps.HkSqAux.kappa (ζ + p₂)
      ≤ Real.exp (2 * |p₂| + p₂) * Work.FTS.StrongEps.HkSqAux.kappa ζ := by
    have h := Work.FTS.StrongEps.HkSqAux.kappa_shift_core (ζ + p₂) p₂
    rwa [show ζ + p₂ - p₂ = ζ from by ring] at h
  have he : Real.exp (s + p₁) ≤ Real.exp |p₁| * Real.exp s := by
    rw [Real.exp_add, mul_comm (Real.exp s)]
    exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (le_abs_self p₁))
      (Real.exp_pos s).le
  have hE : Real.exp |p₁| * Real.exp (2 * |p₂| + p₂)
      ≤ Real.exp (4 * (|p₁| + |p₂|)) := by
    rw [show Real.exp |p₁| * Real.exp (2 * |p₂| + p₂)
        = Real.exp (|p₁| + (2 * |p₂| + p₂)) from
      (Real.exp_add |p₁| (2 * |p₂| + p₂)).symm]
    exact Real.exp_le_exp.mpr
      (by nlinarith [abs_nonneg p₁, abs_nonneg p₂, le_abs_self p₂])
  rw [Work.FTS.StrongEps.HkSqAux.logJac, Work.FTS.StrongEps.HkSqAux.logJac]
  calc Real.exp (s + p₁) * Work.FTS.StrongEps.HkSqAux.kappa (ζ + p₂)
      ≤ (Real.exp |p₁| * Real.exp s)
        * (Real.exp (2 * |p₂| + p₂) * Work.FTS.StrongEps.HkSqAux.kappa ζ) :=
        mul_le_mul he hk (Work.FTS.StrongEps.HkSqAux.kappa_nonneg _)
          (mul_nonneg (Real.exp_pos _).le (Real.exp_pos s).le)
    _ = (Real.exp |p₁| * Real.exp (2 * |p₂| + p₂))
        * (Real.exp s * Work.FTS.StrongEps.HkSqAux.kappa ζ) := by ring
    _ ≤ Real.exp (4 * (|p₁| + |p₂|))
        * (Real.exp s * Work.FTS.StrongEps.HkSqAux.kappa ζ) :=
        mul_le_mul_of_nonneg_right hE
          (mul_nonneg (Real.exp_pos s).le (Work.FTS.StrongEps.HkSqAux.kappa_nonneg ζ))

/-! ## The radial factor `wtZ = w²` -/

/-- **The radial weight shifts forwards by `e^{4|p|}`**: `wtZ (e^{s+p}) ≤ e^{4|p|} wtZ (e^s)`.
This is `wtZ_zShift_le` at the point `z = e^s` with parameter `-p`. -/
theorem wtZ_exp_add_le (s p : ℝ) :
    Work.FTS.StrongEps.wtZ (Real.exp (s + p))
      ≤ Real.exp (4 * |p|) * Work.FTS.StrongEps.wtZ (Real.exp s) := by
  have h := Work.FTS.StrongEps.wtZ_zShift_le (Real.exp s) (-p) (Real.exp_pos s)
  rw [← exp_add_eq_zShift s p, abs_neg] at h
  exact h

/-! ## The angular factor `sin(2θ)^{-γ α}` with the sharp exponent -/

/-- **The angular weight `sin(2θ)^{-γ α}` is shifted by at most `e^{(γ α)|p|}`** for every
`α > 0` (no upper bound on `α`).  This is the sharp version of `sGamW_shift_le`: from the lower
bound `e^{-|p|} sin(2θ) ≤ sin(2·thShift θ p)` one raises to the negative power `-γ α` using
`rpow_shift_le`. -/
theorem sGamW_shift_le_sharp {α : ℝ} (hα : 0 < α) {θ p : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    Work.FTS.StrongEps.sGamW α (Work.FTS.StrongEps.thShift θ p)
      ≤ Real.exp (Work.Spaces.gam α * |p|) * Work.FTS.StrongEps.sGamW α θ := by
  have hlo : Real.exp (-|p|) * Real.sin (2 * θ)
      ≤ Real.sin (2 * Work.FTS.StrongEps.thShift θ p) :=
    (Work.FTS.StrongEps.sinTwo_thShift_bounds hθ).1
  have hs : 0 < Real.sin (2 * θ) := Work.FTS.StrongEps.sin_two_pos hθ
  have hγ : 0 ≤ Work.Spaces.gam α := by rw [Work.Spaces.gam]; linarith
  have h := Work.FTS.StrongEps.rpow_shift_le (s := Real.sin (2 * θ))
    (s' := Real.sin (2 * Work.FTS.StrongEps.thShift θ p)) (c := |p|)
    (γ := Work.Spaces.gam α) hs hγ hlo
  simpa only [Work.FTS.StrongEps.sGamW] using h

/-! ## The general one-sided shift bound -/

/-- **One-sided shift bound for `logJac · (wtZ ∘ exp) · Θ`**, where `Θ` is an arbitrary angular
factor which is positive and shifted by at most `e^{κ|p|}`.  The constant is `8 + κ`
(`4` for the Jacobian, `4` for the radial weight, `κ` for `Θ`). -/
theorem logW_shift_aux {Θ : ℝ → ℝ} (hΘpos : ∀ ζ : ℝ, 0 < Θ ζ) {κ : ℝ} (hκ : 0 ≤ κ)
    (hΘ : ∀ ζ p : ℝ, Θ (ζ + p) ≤ Real.exp (κ * |p|) * Θ ζ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y p : ℝ × ℝ,
      Work.FTS.StrongEps.HkSqAux.logJac (y + p).1 (y + p).2
          * (Work.FTS.StrongEps.wtZ (Real.exp (y + p).1) * Θ (y + p).2)
        ≤ Real.exp (C * (|p.1| + |p.2|))
          * (Work.FTS.StrongEps.HkSqAux.logJac y.1 y.2
              * (Work.FTS.StrongEps.wtZ (Real.exp y.1) * Θ y.2)) := by
  refine ⟨8 + κ, by linarith, fun y p => ?_⟩
  have hJ : Work.FTS.StrongEps.HkSqAux.logJac (y + p).1 (y + p).2
      ≤ Real.exp (4 * (|p.1| + |p.2|)) * Work.FTS.StrongEps.HkSqAux.logJac y.1 y.2 := by
    simpa only [Prod.fst_add, Prod.snd_add] using logJac_add_le y.1 y.2 p.1 p.2
  have hZ : Work.FTS.StrongEps.wtZ (Real.exp (y + p).1)
      ≤ Real.exp (4 * |p.1|) * Work.FTS.StrongEps.wtZ (Real.exp y.1) := by
    simpa only [Prod.fst_add] using wtZ_exp_add_le y.1 p.1
  have hT : Θ (y + p).2 ≤ Real.exp (κ * |p.2|) * Θ y.2 := by
    simpa only [Prod.snd_add] using hΘ y.2 p.2
  have hinner : Work.FTS.StrongEps.wtZ (Real.exp (y + p).1) * Θ (y + p).2
      ≤ (Real.exp (4 * |p.1|) * Work.FTS.StrongEps.wtZ (Real.exp y.1))
        * (Real.exp (κ * |p.2|) * Θ y.2) :=
    mul_le_mul hZ hT (le_of_lt (hΘpos _))
      (mul_nonneg (Real.exp_pos _).le (Work.FTS.StrongEps.wtZ_nonneg _))
  have hmain := mul_le_mul hJ hinner
    (mul_nonneg (Work.FTS.StrongEps.wtZ_nonneg _) (le_of_lt (hΘpos _)))
    (mul_nonneg (Real.exp_pos _).le (Work.FTS.StrongEps.HkSqAux.logJac_pos _ _).le)
  refine hmain.trans ?_
  have heq : (Real.exp (4 * (|p.1| + |p.2|)) * Work.FTS.StrongEps.HkSqAux.logJac y.1 y.2)
        * ((Real.exp (4 * |p.1|) * Work.FTS.StrongEps.wtZ (Real.exp y.1))
            * (Real.exp (κ * |p.2|) * Θ y.2))
      = Real.exp (4 * (|p.1| + |p.2|) + 4 * |p.1| + κ * |p.2|)
        * (Work.FTS.StrongEps.HkSqAux.logJac y.1 y.2
            * (Work.FTS.StrongEps.wtZ (Real.exp y.1) * Θ y.2)) := by
    rw [Real.exp_add (4 * (|p.1| + |p.2|) + 4 * |p.1|) (κ * |p.2|)]
    rw [Real.exp_add (4 * (|p.1| + |p.2|)) (4 * |p.1|)]
    ring
  rw [heq]
  apply mul_le_mul_of_nonneg_right
  · apply Real.exp_le_exp.mpr
    nlinarith [abs_nonneg p.1, abs_nonneg p.2, hκ]
  · exact le_of_lt (mul_pos (Work.FTS.StrongEps.HkSqAux.logJac_pos _ _)
      (mul_pos (Work.FTS.StrongEps.wtZ_pos (Real.exp_pos _)) (hΘpos _)))

/-! ## The target -/

theorem leaf_logW_shift {w : ℝ → ℝ → ℝ} {α : ℝ} (hα : 0 < α)
    (hw : w = Work.FTS.TransportS.leafEta ∨ w = Work.FTS.TransportS.leafOne
      ∨ w = Work.FTS.TransportS.leafGam α) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y p : ℝ × ℝ,
      (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w (y + p)
          ≤ Real.exp (C * (|p.1| + |p.2|)) * Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w y)
      ∧ (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w y
          ≤ Real.exp (C * (|p.1| + |p.2|)) * Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w (y + p)) := by
  rcases hw with hw | hw | hw
  · -- the `η`-leaf `w² sin(2θ)^{-η}`
    subst hw
    have hΘpos : ∀ ζ : ℝ, 0 < Work.FTS.StrongEps.sEtaW (Real.arctan (Real.exp ζ)) :=
      fun ζ => Work.FTS.StrongEps.sEtaW_pos (arctan_exp_mem ζ)
    have hΘ : ∀ ζ p : ℝ, Work.FTS.StrongEps.sEtaW (Real.arctan (Real.exp (ζ + p)))
        ≤ Real.exp (1 * |p|) * Work.FTS.StrongEps.sEtaW (Real.arctan (Real.exp ζ)) := by
      intro ζ p
      have h := Work.FTS.StrongEps.sEtaW_thShift_le (θ := Real.arctan (Real.exp ζ))
        (p := -p) (arctan_exp_mem ζ)
      rw [← arctan_exp_add ζ p, abs_neg] at h
      rw [one_mul]
      exact h
    obtain ⟨C, hC0, hC⟩ := logW_shift_aux hΘpos (by norm_num : (0 : ℝ) ≤ 1) hΘ
    refine ⟨C, hC0, fun y p => ⟨?_, ?_⟩⟩
    · have h := hC y p
      simpa only [logW_apply, Work.FTS.TransportS.leafEta, Work.FTS.StrongEps.wtZ,
        Work.FTS.StrongEps.sEtaW] using h
    · have h := hC (y + p) (-p)
      simpa only [logW_apply, Work.FTS.TransportS.leafEta, Work.FTS.StrongEps.wtZ,
        Work.FTS.StrongEps.sEtaW, Prod.fst_add, Prod.snd_add, Prod.fst_neg, Prod.snd_neg,
        abs_neg, add_neg_cancel_right] using h
  · -- the `w²`-leaf
    subst hw
    have hΘpos : ∀ ζ : ℝ, 0 < (fun _ : ℝ => (1 : ℝ)) ζ := fun _ => one_pos
    have hΘ : ∀ ζ p : ℝ, (fun _ : ℝ => (1 : ℝ)) (ζ + p)
        ≤ Real.exp (0 * |p|) * (fun _ : ℝ => (1 : ℝ)) ζ := by
      intro ζ p; simp
    obtain ⟨C, hC0, hC⟩ := logW_shift_aux (Θ := fun _ : ℝ => (1 : ℝ)) hΘpos
      (le_refl (0 : ℝ)) hΘ
    refine ⟨C, hC0, fun y p => ⟨?_, ?_⟩⟩
    · have h := hC y p
      simpa only [logW_apply, Work.FTS.TransportS.leafOne, Work.FTS.StrongEps.wtZ,
        mul_one] using h
    · have h := hC (y + p) (-p)
      simpa only [logW_apply, Work.FTS.TransportS.leafOne, Work.FTS.StrongEps.wtZ,
        mul_one, Prod.fst_add, Prod.snd_add, Prod.fst_neg, Prod.snd_neg,
        abs_neg, add_neg_cancel_right] using h
  · -- the `γ`-leaf `w² sin(2θ)^{-γ α}`
    subst hw
    have hgam : 0 ≤ Work.Spaces.gam α := by rw [Work.Spaces.gam]; linarith
    have hΘpos : ∀ ζ : ℝ, 0 < Work.FTS.StrongEps.sGamW α (Real.arctan (Real.exp ζ)) :=
      fun ζ => Work.FTS.StrongEps.sGamW_pos (arctan_exp_mem ζ)
    have hΘ : ∀ ζ p : ℝ, Work.FTS.StrongEps.sGamW α (Real.arctan (Real.exp (ζ + p)))
        ≤ Real.exp (Work.Spaces.gam α * |p|)
          * Work.FTS.StrongEps.sGamW α (Real.arctan (Real.exp ζ)) := by
      intro ζ p
      have h := sGamW_shift_le_sharp hα (θ := Real.arctan (Real.exp ζ))
        (p := -p) (arctan_exp_mem ζ)
      rwa [← arctan_exp_add ζ p, abs_neg] at h
    obtain ⟨C, hC0, hC⟩ := logW_shift_aux hΘpos hgam hΘ
    refine ⟨C, hC0, fun y p => ⟨?_, ?_⟩⟩
    · have h := hC y p
      simpa only [logW_apply, Work.FTS.TransportS.leafGam, Work.FTS.StrongEps.wtZ,
        Work.FTS.StrongEps.sGamW] using h
    · have h := hC (y + p) (-p)
      simpa only [logW_apply, Work.FTS.TransportS.leafGam, Work.FTS.StrongEps.wtZ,
        Work.FTS.StrongEps.sGamW, Prod.fst_add, Prod.snd_add, Prod.fst_neg, Prod.snd_neg,
        abs_neg, add_neg_cancel_right] using h

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer
