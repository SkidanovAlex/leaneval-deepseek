import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.Defs
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer.leaf_logW_shift

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer

set_option autoImplicit false
set_option maxHeartbeats 800000

open scoped Real Topology
open MeasureTheory Set Filter

/-!
# `leaf_logW_shift_uniform` — a *single* shift constant for all three leaf weights

`leaf_logW_shift` proves, for each fixed `α > 0` and each of the three leaf weights
`w²sin(2θ)^{-η}`, `w²`, `w²sin(2θ)^{-γ α}`, the existence of a constant `C` with

`logW w (y+p) ≤ e^{C(|p.1|+|p.2|)} logW w y`

(and the reverse).  The exponent produced there is `8 + κ`, where `κ` is the angular constant:
`κ = 1` for the `η`-leaf, `κ = 0` for the `w²`-leaf and `κ = γ α = 1 + α/10` for the `γ`-leaf.
Since `α ≤ 1` forces `γ α ≤ 11/10` and `η = 99/100 ≤ 11/10`, all three leaves satisfy the angular
bound with the **same** constant `κ = 11/10`, hence all of them — uniformly in `α ∈ (0,1]` — are
controlled with the single constant

  `C = 8 + 11/10`.

The two ingredients of `8` are the Jacobian factor (`logJac_add_le`, giving `e^{4(|p.1|+|p.2|)}`)
and the radial factor (`wtZ_exp_add_le`, giving `e^{4|p.1|}`); they combine exactly as in
`logW_shift_aux`, whose proof we re-run with the constant exposed (`logW_shift_uniform_aux`) so
that a common `κ` can be fed to all three leaves.
-/

/-! ## The angular factors, with the common exponent `11/10` -/

/-- **The `η`-factor with the uniform exponent**: `sin(2θ)^{-η}` at `θ = arctan (e^ζ)` shifts by
at most `e^{(11/10)|p|}`.  (`sEtaW_thShift_le` gives `e^{|p|}`, and `1 ≤ 11/10`.) -/
theorem sEtaW_arctan_exp_shift (ζ p : ℝ) :
    Work.FTS.StrongEps.sEtaW (Real.arctan (Real.exp (ζ + p)))
      ≤ Real.exp ((11 / 10 : ℝ) * |p|)
        * Work.FTS.StrongEps.sEtaW (Real.arctan (Real.exp ζ)) := by
  have h := Work.FTS.StrongEps.sEtaW_thShift_le (θ := Real.arctan (Real.exp ζ)) (p := -p)
    (arctan_exp_mem ζ)
  rw [← arctan_exp_add ζ p, abs_neg] at h
  have hexp : Real.exp |p| ≤ Real.exp ((11 / 10 : ℝ) * |p|) :=
    Real.exp_le_exp.mpr (by nlinarith [abs_nonneg p])
  exact h.trans (mul_le_mul_of_nonneg_right hexp
    (le_of_lt (Work.FTS.StrongEps.sEtaW_pos (arctan_exp_mem ζ))))

/-- **The `γ`-factor with the uniform exponent**: for `α ∈ (0,1]`, `sin(2θ)^{-γ α}` at
`θ = arctan (e^ζ)` shifts by at most `e^{(11/10)|p|}`.  This is `sGamW_shift_le_sharp`
(`e^{γ α |p|}`) together with `γ α = 1 + α/10 ≤ 11/10`. -/
theorem sGamW_arctan_exp_shift {α : ℝ} (hα : α ∈ Set.Ioc (0 : ℝ) 1) (ζ p : ℝ) :
    Work.FTS.StrongEps.sGamW α (Real.arctan (Real.exp (ζ + p)))
      ≤ Real.exp ((11 / 10 : ℝ) * |p|)
        * Work.FTS.StrongEps.sGamW α (Real.arctan (Real.exp ζ)) := by
  have h := sGamW_shift_le_sharp (α := α) hα.1 (θ := Real.arctan (Real.exp ζ)) (p := -p)
    (arctan_exp_mem ζ)
  rw [← arctan_exp_add ζ p, abs_neg] at h
  have hgam : Work.Spaces.gam α ≤ 11 / 10 := by
    rw [Work.Spaces.gam]; linarith [hα.2]
  have hexp : Real.exp (Work.Spaces.gam α * |p|) ≤ Real.exp ((11 / 10 : ℝ) * |p|) :=
    Real.exp_le_exp.mpr (by nlinarith [abs_nonneg p, hgam])
  exact h.trans (mul_le_mul_of_nonneg_right hexp
    (le_of_lt (Work.FTS.StrongEps.sGamW_pos (α := α) (arctan_exp_mem ζ))))

/-! ## The two-sided shift bound with an exposed constant -/

/-- **Two-sided shift bound for `logW`, with the constant `8 + κ` exposed.**  If `Θ` is a positive
angular factor which shifts by at most `e^{κ|p|}` and `w`, evaluated at `Ψ y = (e^{y.1},
arctan (e^{y.2}))`, is `wtZ (e^{y.1}) · Θ y.2`, then `logW w` shifts by at most
`e^{(8+κ)(|p.1|+|p.2|)}` in both directions.  The forward direction is the proof of
`logW_shift_aux` with `∃C` replaced by the explicit `8 + κ`; the reverse is the forward bound
applied at `(y + p, -p)`. -/
theorem logW_shift_uniform_aux {Θ : ℝ → ℝ} (hΘpos : ∀ ζ : ℝ, 0 < Θ ζ) {κ : ℝ} (hκ : 0 ≤ κ)
    (hΘ : ∀ ζ p : ℝ, Θ (ζ + p) ≤ Real.exp (κ * |p|) * Θ ζ) (w : ℝ → ℝ → ℝ)
    (hw : ∀ y : ℝ × ℝ, w (Real.exp y.1) (Real.arctan (Real.exp y.2))
      = Work.FTS.StrongEps.wtZ (Real.exp y.1) * Θ y.2) :
    ∀ y p : ℝ × ℝ,
      (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w (y + p)
          ≤ Real.exp ((8 + κ) * (|p.1| + |p.2|))
            * Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w y)
      ∧ (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w y
          ≤ Real.exp ((8 + κ) * (|p.1| + |p.2|))
            * Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w (y + p)) := by
  -- fold `logW w` into the `logJac · (wtZ · Θ)` form
  have hpi : ∀ y : ℝ × ℝ, Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w y
      = Work.FTS.StrongEps.HkSqAux.logJac y.1 y.2
        * (Work.FTS.StrongEps.wtZ (Real.exp y.1) * Θ y.2) := by
    intro y
    rw [Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW_apply, hw y]
  have hfwd : ∀ y p : ℝ × ℝ,
      Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w (y + p)
        ≤ Real.exp ((8 + κ) * (|p.1| + |p.2|))
          * Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w y := by
    intro y p
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
    have heq : (Real.exp (4 * (|p.1| + |p.2|)) * Work.FTS.StrongEps.HkSqAux.logJac y.1 y.2)
          * ((Real.exp (4 * |p.1|) * Work.FTS.StrongEps.wtZ (Real.exp y.1))
              * (Real.exp (κ * |p.2|) * Θ y.2))
        = Real.exp (4 * (|p.1| + |p.2|) + 4 * |p.1| + κ * |p.2|)
          * (Work.FTS.StrongEps.HkSqAux.logJac y.1 y.2
              * (Work.FTS.StrongEps.wtZ (Real.exp y.1) * Θ y.2)) := by
      rw [Real.exp_add (4 * (|p.1| + |p.2|) + 4 * |p.1|) (κ * |p.2|)]
      rw [Real.exp_add (4 * (|p.1| + |p.2|)) (4 * |p.1|)]
      ring
    have hstep : Work.FTS.StrongEps.HkSqAux.logJac (y + p).1 (y + p).2
          * (Work.FTS.StrongEps.wtZ (Real.exp (y + p).1) * Θ (y + p).2)
        ≤ Real.exp ((8 + κ) * (|p.1| + |p.2|))
          * (Work.FTS.StrongEps.HkSqAux.logJac y.1 y.2
              * (Work.FTS.StrongEps.wtZ (Real.exp y.1) * Θ y.2)) := by
      refine hmain.trans ?_
      rw [heq]
      apply mul_le_mul_of_nonneg_right
      · exact Real.exp_le_exp.mpr (by nlinarith [abs_nonneg p.1, abs_nonneg p.2, hκ])
      · exact le_of_lt (mul_pos (Work.FTS.StrongEps.HkSqAux.logJac_pos _ _)
          (mul_pos (Work.FTS.StrongEps.wtZ_pos (Real.exp_pos _)) (hΘpos _)))
    rw [hpi (y + p), hpi y]
    exact hstep
  intro y p
  refine ⟨hfwd y p, ?_⟩
  have h := hfwd (y + p) (-p)
  simpa only [Prod.fst_add, Prod.snd_add, Prod.fst_neg, Prod.snd_neg, abs_neg,
    add_neg_cancel_right] using h

/-! ## The uniform statement -/

theorem leaf_logW_shift_uniform :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ α ∈ Set.Ioc (0 : ℝ) 1, ∀ w : ℝ → ℝ → ℝ,
      (w = Work.FTS.TransportS.leafEta ∨ w = Work.FTS.TransportS.leafOne
        ∨ w = Work.FTS.TransportS.leafGam α) →
      ∀ y p : ℝ × ℝ,
        (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w (y + p)
            ≤ Real.exp (C * (|p.1| + |p.2|))
              * Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w y)
        ∧ (Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w y
            ≤ Real.exp (C * (|p.1| + |p.2|))
              * Work.FTS.StrongEps.E4R3.Apriori4Proofs.logW w (y + p)) := by
  refine ⟨8 + 11 / 10, by norm_num, ?_⟩
  intro α hα w hw y p
  have hκ : (0 : ℝ) ≤ 11 / 10 := by norm_num
  rcases hw with hw | hw | hw
  · -- the `η`-leaf
    subst hw
    have hΘpos : ∀ ζ : ℝ, 0 < Work.FTS.StrongEps.sEtaW (Real.arctan (Real.exp ζ)) :=
      fun ζ => Work.FTS.StrongEps.sEtaW_pos (arctan_exp_mem ζ)
    have hΘ : ∀ ζ p : ℝ, Work.FTS.StrongEps.sEtaW (Real.arctan (Real.exp (ζ + p)))
        ≤ Real.exp ((11 / 10 : ℝ) * |p|)
          * Work.FTS.StrongEps.sEtaW (Real.arctan (Real.exp ζ)) :=
      fun ζ p => sEtaW_arctan_exp_shift ζ p
    have hw' : ∀ y : ℝ × ℝ,
        Work.FTS.TransportS.leafEta (Real.exp y.1) (Real.arctan (Real.exp y.2))
          = Work.FTS.StrongEps.wtZ (Real.exp y.1)
            * Work.FTS.StrongEps.sEtaW (Real.arctan (Real.exp y.2)) := by
      intro y
      simp only [Work.FTS.TransportS.leafEta, Work.FTS.StrongEps.wtZ,
        Work.FTS.StrongEps.sEtaW]
    exact logW_shift_uniform_aux
      (Θ := fun ζ => Work.FTS.StrongEps.sEtaW (Real.arctan (Real.exp ζ)))
      (κ := 11 / 10) hΘpos hκ hΘ Work.FTS.TransportS.leafEta hw' y p
  · -- the `w²`-leaf
    subst hw
    have hΘpos : ∀ ζ : ℝ, 0 < (fun _ : ℝ => (1 : ℝ)) ζ := fun _ => one_pos
    have hΘ : ∀ ζ p : ℝ, (fun _ : ℝ => (1 : ℝ)) (ζ + p)
        ≤ Real.exp ((11 / 10 : ℝ) * |p|) * (fun _ : ℝ => (1 : ℝ)) ζ := by
      intro ζ p
      have h0 : (0 : ℝ) ≤ (11 / 10 : ℝ) * |p| :=
        mul_nonneg (by norm_num) (abs_nonneg p)
      simpa only [Pi.one_apply, mul_one] using Real.one_le_exp h0
    have hw' : ∀ y : ℝ × ℝ,
        Work.FTS.TransportS.leafOne (Real.exp y.1) (Real.arctan (Real.exp y.2))
          = Work.FTS.StrongEps.wtZ (Real.exp y.1) * (fun _ : ℝ => (1 : ℝ)) y.2 := by
      intro y
      simp only [Work.FTS.TransportS.leafOne, Work.FTS.StrongEps.wtZ, mul_one]
    exact logW_shift_uniform_aux (Θ := fun _ : ℝ => (1 : ℝ)) (κ := 11 / 10) hΘpos hκ hΘ
      Work.FTS.TransportS.leafOne hw' y p
  · -- the `γ`-leaf
    subst hw
    have hΘpos : ∀ ζ : ℝ, 0 < Work.FTS.StrongEps.sGamW α (Real.arctan (Real.exp ζ)) :=
      fun ζ => Work.FTS.StrongEps.sGamW_pos (α := α) (arctan_exp_mem ζ)
    have hΘ : ∀ ζ p : ℝ, Work.FTS.StrongEps.sGamW α (Real.arctan (Real.exp (ζ + p)))
        ≤ Real.exp ((11 / 10 : ℝ) * |p|)
          * Work.FTS.StrongEps.sGamW α (Real.arctan (Real.exp ζ)) :=
      fun ζ p => sGamW_arctan_exp_shift hα ζ p
    have hw' : ∀ y : ℝ × ℝ,
        Work.FTS.TransportS.leafGam α (Real.exp y.1) (Real.arctan (Real.exp y.2))
          = Work.FTS.StrongEps.wtZ (Real.exp y.1)
            * Work.FTS.StrongEps.sGamW α (Real.arctan (Real.exp y.2)) := by
      intro y
      simp only [Work.FTS.TransportS.leafGam, Work.FTS.StrongEps.wtZ,
        Work.FTS.StrongEps.sGamW]
    exact logW_shift_uniform_aux
      (Θ := fun ζ => Work.FTS.StrongEps.sGamW α (Real.arctan (Real.exp ζ)))
      (κ := 11 / 10) hΘpos hκ hΘ (Work.FTS.TransportS.leafGam α) hw' y p

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.JepsTransfer
