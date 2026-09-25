import Mathlib
import Submission.Work.BourgainPlan.Maximal.mst_major_defs
import Submission.Work.BourgainPlan.Maximal.mst_level_defs
import Submission.Work.BourgainPlan.Maximal.memLp_mst_symbols
import Submission.Work.BourgainPlan.Maximal.level_l2_mst_large_n_aux_defs
import Submission.Work.BourgainPlan.Maximal.mstFreezeDefs

/-!
# The vocabulary of the *large-scale* `ℓʳ` level estimate (`mst_level_lr_large`)

The target `Work.Maximal.mst_level_lr_large` bounds the `ℓʳ` (`1 < r < 2`) maximal function, over
the *dyadic scales* `k ≥ 2^{κ_s}` (`κ_s = mstKappa P s`), of the level-`s` model

`mstNuS P l d χ η k s = Σ_{β ∈ 𝒰(s+1) ∖ 𝒰(s)} star (G β) · (star (Φ_{2^k}) · η_s) (· - β)`.

The reduction performed in `Submission/Work/Maximal/mst_level_lr_large.lean` splits this into

* the **single-symbol** family `k ↦ mstPiSym P d χ η k s` (the conjugated profile-times-bump
  `star (Φ_{2^k}) · η_s`, no arcs, no weights) — whose maximal bound is the `ℓʳ` analogue of
  `Maximal.mstMaximal_single` (`Submission/Work/BourgainPlan/Maximal/mstMaximal_single.lean`),
  proved by the same sampling/freezing route as MST Proposition 4;
* the arc/weight bookkeeping, which is algebra: linearity of `opMul` in the symbol, the *modulation*
  identity `opMul (arcTranslate β Φ) g = (character) • opMul Φ (modSeq g β)`, and the Gauss-sum
  bound `Σ_{β ∈ 𝒰(s+1) ∖ 𝒰(s)} ‖G β‖ ≤ C` (uniform in `s`).

This file fixes the two symbols, their `L^∞(𝕋)`-classes and the interface lemmas used by the
reduction.
-/

open MeasureTheory Finset
open scoped BigOperators ENNReal

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.Maximal

open Work.BourgainPlan.IonescuWainger

noncomputable section

local notation "haarT" => (AddCircle.haarAddCircle (T := 1))
local notation "Circ" => Work.BourgainPlan.IonescuWainger.Circle

/-! ## The level bump `η_s` and its class -/

/-- The level-`s` bump `η_s` is a.e. bounded (a continuous circle function). -/
lemma memLp_mstEta (d : ℕ) (χ : ℝ) (η : ℝ → ℂ) (hηc : ContDiff ℝ 2 η) (s : ℕ) :
    MeasureTheory.MemLp (Work.BourgainPlan.Maximal.mstEta d χ η s) ⊤ haarT := by
  have h := (Work.BourgainPlan.Maximal.memLp_mst_symbols (0 : Polynomial ℤ) 0
    ((2 : ℝ) ^ ((s : ℝ) * ((d : ℝ) - χ))) η hηc.continuous).2.2
  have hfun : (fun ξ : Circ =>
        η ((2 : ℝ) ^ ((s : ℝ) * ((d : ℝ) - χ)) * Work.BourgainPlan.Maximal.iwRep ξ))
      = Work.BourgainPlan.Maximal.mstEta d χ η s := by
    funext ξ; rw [Work.BourgainPlan.Maximal.mstEta_apply]
  rwa [hfun] at h

/-- The `L^∞(𝕋)`-class of the level-`s` bump. -/
def mstEtaCls (d : ℕ) (χ : ℝ) (η : ℝ → ℂ) (hηc : ContDiff ℝ 2 η) (s : ℕ) :
    Lp ℂ ⊤ haarT :=
  (memLp_mstEta d χ η hηc s).toLp (Work.BourgainPlan.Maximal.mstEta d χ η s)

lemma mstEtaCls_coeFn (d : ℕ) (χ : ℝ) (η : ℝ → ℂ) (hηc : ContDiff ℝ 2 η) (s : ℕ) :
    (mstEtaCls d χ η hηc s : Circ → ℂ)
      =ᵐ[haarT] Work.BourgainPlan.Maximal.mstEta d χ η s :=
  MemLp.coeFn_toLp _

/-! ## The single level-`s` model symbol `star (Φ_{2^k}) · η_s` -/

/-- The **conjugated profile-times-bump symbol** `ξ ↦ star (Φ_{2^k}(ξ)) · η_s(ξ)`: the single
multiplier symbol of the level-`s` model at the dyadic scale `2^k`, without the arc weights. -/
def mstPiSym (P : Polynomial ℤ) (d : ℕ) (χ : ℝ) (η : ℝ → ℂ) (k s : ℕ) : Circ → ℂ :=
  fun ξ => star (Work.BourgainPlan.Maximal.mstProf P (2 ^ k) ξ)
    * Work.BourgainPlan.Maximal.mstEta d χ η s ξ

@[simp] lemma mstPiSym_apply (P : Polynomial ℤ) (d : ℕ) (χ : ℝ) (η : ℝ → ℂ) (k s : ℕ)
    (ξ : Circ) :
    mstPiSym P d χ η k s ξ
      = star (Work.BourgainPlan.Maximal.mstProf P (2 ^ k) ξ)
        * Work.BourgainPlan.Maximal.mstEta d χ η s ξ := rfl

/-- The conjugate profile is a.e. bounded. -/
lemma memLp_mstStarProf (P : Polynomial ℤ) (N : ℕ) :
    MeasureTheory.MemLp (fun ζ : Circ => star (Work.BourgainPlan.Maximal.mstProf P N ζ)) ⊤
      haarT :=
  ((Work.BourgainPlan.Maximal.memLp_mst_symbols P N 1 (fun _ : ℝ => (0 : ℂ))
    continuous_const).2.1).star

lemma memLp_mstPiSym (P : Polynomial ℤ) (d : ℕ) (χ : ℝ) (η : ℝ → ℂ)
    (hηc : ContDiff ℝ 2 η) (k s : ℕ) :
    MeasureTheory.MemLp (mstPiSym P d χ η k s) ⊤ haarT :=
  MemLp.mul (f := Work.BourgainPlan.Maximal.mstEta d χ η s)
    (φ := fun ζ : Circ => star (Work.BourgainPlan.Maximal.mstProf P (2 ^ k) ζ))
    (p := ⊤) (q := ⊤) (r := ⊤)
    (memLp_mstStarProf P (2 ^ k)) (memLp_mstEta d χ η hηc s)

/-- The `L^∞(𝕋)`-class of the single level-`s` model symbol at scale `2^k`. -/
def mstPiSymLp (P : Polynomial ℤ) (d : ℕ) (χ : ℝ) (η : ℝ → ℂ) (hηc : ContDiff ℝ 2 η)
    (k s : ℕ) : Lp ℂ ⊤ haarT :=
  (memLp_mstPiSym P d χ η hηc k s).toLp (mstPiSym P d χ η k s)

lemma mstPiSymLp_coeFn (P : Polynomial ℤ) (d : ℕ) (χ : ℝ) (η : ℝ → ℂ)
    (hηc : ContDiff ℝ 2 η) (k s : ℕ) :
    (mstPiSymLp P d χ η hηc k s : Circ → ℂ) =ᵐ[haarT] mstPiSym P d χ η k s :=
  MemLp.coeFn_toLp _

end

end Work.Maximal
