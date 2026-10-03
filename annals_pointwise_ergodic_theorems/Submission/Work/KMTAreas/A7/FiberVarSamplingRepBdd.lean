/-
# The `f`-side fibre variational sampling estimate at the repaired window `uRep`, bounded input

This is the `uRep`-analogue of `Work.KMTAreas.A7.fiberVarSampling` (the §8 fibre estimate of
Krause--Mirek--Tao for the fibre `fiberOp ρ l₁ (mStarF U) n₀`), in the form needed by the
assembly `Work.KMTAreas.A7.ModelLargeHiRep`:

* the input function `f` is **bounded** (`∃ Bf, ∀ y, ‖f y‖ ≤ Bf`), which is exactly what the
  assembly has in hand (a finite `ℓᵖ`-norm forces boundedness on `ℤ` with the counting measure);
* the scale family is **lacunary** (`a : ℕ → ℝ≥0`, `1 < Λ`, `Lacunary Λ a`, `∀ n, 1 ≤ a n`) and
  enters only through `N n = ⌊a n⌋`, with an arbitrary clip `S : ℕ → Prop` on which the two scale
  conditions are imposed;
* the window is the *repaired* one `uRep ρ l₁ l₂ k₁ k₂ = max (uScale ρ L) (max l₁ l₂ + 3)`
  (`L = max (max l₁ l₂) (max k₁ k₂)`).

## The proof (two regimes, as in the sibling `g`-side `A7Rescue.fiberVarSamplingGRep_bdd`)

* **Bounded scale** `L ≤ B ρ`: the proved `A7.rep_smallL` (crude Young/kernel bound, valid for
  *every* family) gives the estimate at the window `uRep` itself, with no `lossWeight`.
* **Large scale** `L > B ρ`: `A7.farey_and_strict_of_large_L` gives the quantitative Farey
  condition `8·2^{k₁}·arithQ ρ (max l₁ l₂) ≤ N` and the strict main-regime condition at the
  *`uScale`* window, and `A7.exists_nonAliasing_uScale` gives non-aliasing of the arithmetic
  frequencies at the `uScale` scale.  The **proved** `uScale`-version of the estimate
  (`A7.fiberVarSamplingLargeLoss_bdd`), which needs exactly those three hypotheses, then applies —
  but with the window `mStarF (uScale ρ L)` rather than `mStarF (uRep ρ l₁ l₂ k₁ k₂)`.

  The two windows are compared by the **clip identity** `A7.fiberOp_mStarF_Sclip`: for a bump
  `φ` whose spectrum lies in the plateau half-ball `2^{-2U-1}` and arithmetic frequencies
  non-aliasing at the scale `-2U`,

    `fiberOp ρ l₁ (mStarF U) n₀ (1_S · Tex ρ l₁ φ f) = 1_S · fiberOp ρ l₁ φ n₀ f`,

  whose right-hand side is *independent of `U`*.  Since `uScale ρ L ≤ uRep ρ l₁ l₂ k₁ k₂`, the
  strict-condition and support hypotheses hold at both windows (the `uRep` plateau is the
  narrower one), and non-aliasing at `uRep` follows from non-aliasing at `uScale` by
  `nonAliasing_mono_scale`.  Hence the two fibres agree and the `uScale` estimate transfers
  verbatim.  (Off the clip `S` both sides are `0` for trivial reasons.)

## Relation to the tree

`Work.KMTAreas.A7.ModelLargeHiRep` (and its `uScale` sibling `Work.KMTAreas.A7.ModelLargeHi`)
consume this estimate in the `f`-side slot of the §8 model-tuple bound.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.FiberVarSamplingRep
import Submission.Work.KMTAreas.A7Hi.NonAliasingMono

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.KMTAreas.A7

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.Analysis.IonescuWainger Work.Analysis.EndVar

/-- **The `f`-side fibre variational sampling estimate at the repaired window `uRep`, bounded
input.**  See the module docstring for the route. -/
theorem FiberVarSamplingRepBdd (r : NNReal) (hr : 2 < r) :
    ∃ A : ℝ, 0 ≤ A ∧ ∃ ρ₀ : ℝ, 0 < ρ₀ ∧
      ∀ (p : ENNReal) (hp : 1 < p) (hptop : p < ⊤),
      ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ →
      ∃ C : ℝ, 0 < C ∧
        ∀ (a : ℕ → NNReal) (Λ : NNReal), 1 < Λ →
          PointwiseErgodicTheorems.Lacunary Λ a → (∀ n : ℕ, 1 ≤ a n) →
        ∀ (l₁ l₂ k₁ k₂ : ℕ) (t : ℝ) (f : ℤ → ℂ) (S : ℕ → Prop) [DecidablePred S],
          (∃ Bf : ℝ, ∀ y : ℤ, ‖f y‖ ≤ Bf) →
          t ∈ Set.Icc (1/2 : ℝ) 1 →
          (∀ n : ℕ, S n → k₁ + 1 + 2 * uRep ρ l₁ l₂ k₁ k₂
              ≤ (logN (Nat.floor (a n))).toNat) →
          (∀ n : ℕ, S n → splitCut ρ (max (max l₁ l₂) (max k₁ k₂))
              < Nat.floor (a n)) →
          MeasureTheory.eLpNorm (fun x : ℤ =>
              residueLp p.toReal (arithQ ρ (max l₁ l₂))
                (fun y n₀ => variationalNorm r
                  (fun n : ℕ => fiberOp ρ l₁
                    (mStarF (uRep ρ l₁ l₂ k₁ k₂)) n₀
                    (if S n then Tex ρ l₁
                      (varphiNt (Nat.floor (a n)) k₁ t) f else 0) y)) x) p
              MeasureTheory.Measure.count
            ≤ ENNReal.ofReal (C * lossWeight A ρ l₁ l₂ k₁ k₂) *
                MeasureTheory.eLpNorm (fun x : ℤ => variationalNorm r
                  (fun n : ℕ => (if S n then Tex ρ l₁
                    (varphiNt (Nat.floor (a n)) k₁ t) f else 0) x)) p
                  MeasureTheory.Measure.count := by
  classical
  refine ⟨0, le_rfl, 1, one_pos, ?_⟩
  intro p hp hptop ρ hρ hρ1
  obtain ⟨Bfas, hBfas⟩ := farey_and_strict_of_large_L ρ hρ hρ1
  obtain ⟨Bna, hBna⟩ := exists_nonAliasing_uScale ρ hρ hρ1
  obtain ⟨C₁, hC₁pos, hC₁⟩ := rep_smallL r hr ρ hρ hρ1 p hp hptop (fun _ => max Bfas Bna + 1)
  obtain ⟨C₂, hC₂pos, hC₂⟩ := fiberVarSamplingLargeLoss_bdd ρ hρ hρ1 p hp hptop r hr
  refine ⟨max C₁ C₂, lt_max_of_lt_left hC₁pos, ?_⟩
  intro a Λ hΛ hlac ha l₁ l₂ k₁ k₂ t f S hdec hBf ht hband hsplit
  by_cases hsmall : Lnat l₁ l₂ k₁ k₂ ≤ max Bfas Bna + 1
  · -- bounded scale: the crude estimate at the `uRep` window, uniformly in the family
    have hb := hC₁ l₁ l₂ k₁ k₂ hsmall
      (fun n => if S n then Tex ρ l₁ (varphiNt (Nat.floor (a n)) k₁ t) f else 0)
    refine hb.trans ?_
    refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
    rw [show lossWeight 0 ρ l₁ l₂ k₁ k₂ = 1 by simp [lossWeight], mul_one]
    exact le_max_left C₁ C₂
  · -- large scale
    push_neg at hsmall
    obtain ⟨Bf, hBf⟩ := hBf
    have hLdef : Lnat l₁ l₂ k₁ k₂ = max (max l₁ l₂) (max k₁ k₂) := rfl
    have hBfasLt : Bfas < max (max l₁ l₂) (max k₁ k₂) := by rw [hLdef] at hsmall; omega
    have hBnaLe : Bna ≤ max (max l₁ l₂) (max k₁ k₂) := by rw [hLdef] at hsmall; omega
    have hl₁L : l₁ ≤ max (max l₁ l₂) (max k₁ k₂) := by omega
    have hUscl : uScale ρ (max (max l₁ l₂) (max k₁ k₂)) ≤ uRep ρ l₁ l₂ k₁ k₂ := by
      rw [uRep]; exact le_max_left _ _
    have hnaScale : NonAliasing (-(2 * (uScale ρ (max (max l₁ l₂) (max k₁ k₂)) : ℤ)))
        (iwArithFreqs ρ l₁) := hBna l₁ _ hl₁L hBnaLe
    have hnaRep : NonAliasing (-(2 * (uRep ρ l₁ l₂ k₁ k₂ : ℤ))) (iwArithFreqs ρ l₁) := by
      refine A7Hi.nonAliasing_mono_scale ?_ hnaScale
      have h : ((uScale ρ (max (max l₁ l₂) (max k₁ k₂)) : ℕ) : ℤ)
          ≤ ((uRep ρ l₁ l₂ k₁ k₂ : ℕ) : ℤ) := by exact_mod_cast hUscl
      linarith
    -- the auxiliary scale sequence: the target's family on the clip, a huge constant off it
    set N' : ℕ → ℕ := fun n => if S n then Nat.floor (a n)
      else 2 ^ (k₁ + 2 * uRep ρ l₁ l₂ k₁ k₂ + 4) * (arithQ ρ (max l₁ l₂) + 1) with hN'
    have hstrictRep : ∀ n : ℕ, k₁ + 2 * uRep ρ l₁ l₂ k₁ k₂ + 1 ≤ (logN (N' n)).toNat := by
      intro n
      by_cases hn : S n
      · rw [hN']; simp only [hn, if_true]
        have h := hband n hn
        omega
      · rw [hN']; simp only [hn, if_false]
        set K : ℕ := 2 ^ (k₁ + 2 * uRep ρ l₁ l₂ k₁ k₂ + 4)
          * (arithQ ρ (max l₁ l₂) + 1) with hK
        have hle : 2 ^ (k₁ + 2 * uRep ρ l₁ l₂ k₁ k₂ + 4) ≤ max K 2 := by
          rw [hK]
          refine le_trans ?_ (le_max_left _ _)
          exact Nat.le_mul_of_pos_right _
            (by omega : 0 < arithQ ρ (max l₁ l₂) + 1)
        have hlog := Nat.le_log_of_pow_le (by norm_num : 1 < 2) hle
        have hlogN : (logN K).toNat = Nat.log 2 (max K 2) := by
          rw [logN, Int.toNat_natCast]
        rw [hlogN]
        omega
    have hstrictScale : ∀ n : ℕ, k₁ + 2 * uScale ρ (max (max l₁ l₂) (max k₁ k₂)) + 1
        ≤ (logN (N' n)).toNat := by
      intro n
      have h := hstrictRep n
      omega
    have hfarey' : ∀ n : ℕ, (2 : ℝ) ^ k₁ * (arithQ ρ (max l₁ l₂) : ℝ) * 8 ≤ (N' n : ℝ) := by
      intro n
      by_cases hn : S n
      · rw [hN']; simp only [hn, if_true]
        exact (hBfas l₁ l₂ k₁ k₂ (Nat.floor (a n)) (hsplit n hn) hBfasLt).1
      · rw [hN']; simp only [hn, if_false]
        have h8 : (8 : ℝ) ≤ (2 : ℝ) ^ (2 * uRep ρ l₁ l₂ k₁ k₂ + 4) := by
          have h : (8 : ℕ) ≤ 2 ^ (2 * uRep ρ l₁ l₂ k₁ k₂ + 4) := by
            calc (8 : ℕ) = 2 ^ 3 := by norm_num
              _ ≤ 2 ^ (2 * uRep ρ l₁ l₂ k₁ k₂ + 4) :=
                  Nat.pow_le_pow_right (by norm_num) (by omega)
          exact_mod_cast h
        have hcast : (((2 ^ (k₁ + 2 * uRep ρ l₁ l₂ k₁ k₂ + 4)
            * (arithQ ρ (max l₁ l₂) + 1) : ℕ) : ℝ))
            = (2 : ℝ) ^ (k₁ + 2 * uRep ρ l₁ l₂ k₁ k₂ + 4)
              * ((arithQ ρ (max l₁ l₂) : ℝ) + 1) := by
          push_cast
          ring
        rw [hcast]
        have hpow : (2 : ℝ) ^ (k₁ + 2 * uRep ρ l₁ l₂ k₁ k₂ + 4)
            = (2 : ℝ) ^ k₁ * (2 : ℝ) ^ (2 * uRep ρ l₁ l₂ k₁ k₂ + 4) := by
          rw [← pow_add]; ring_nf
        rw [hpow]
        have hk₁nn : (0 : ℝ) ≤ (2 : ℝ) ^ k₁ := by positivity
        have hq1 : (0 : ℝ) ≤ (arithQ ρ (max l₁ l₂) : ℝ) + 1 := by positivity
        calc (2 : ℝ) ^ k₁ * (arithQ ρ (max l₁ l₂) : ℝ) * 8
            = (2 : ℝ) ^ k₁ * ((arithQ ρ (max l₁ l₂) : ℝ) * 8) := by ring
          _ ≤ (2 : ℝ) ^ k₁
                * (((arithQ ρ (max l₁ l₂) : ℝ) + 1)
                  * (2 : ℝ) ^ (2 * uRep ρ l₁ l₂ k₁ k₂ + 4)) := by
              refine mul_le_mul_of_nonneg_left ?_ hk₁nn
              calc (arithQ ρ (max l₁ l₂) : ℝ) * 8
                  ≤ ((arithQ ρ (max l₁ l₂) : ℝ) + 1) * 8 := by nlinarith
                _ ≤ ((arithQ ρ (max l₁ l₂) : ℝ) + 1)
                      * (2 : ℝ) ^ (2 * uRep ρ l₁ l₂ k₁ k₂ + 4) :=
                    mul_le_mul_of_nonneg_left h8 hq1
          _ = (2 : ℝ) ^ k₁ * (2 : ℝ) ^ (2 * uRep ρ l₁ l₂ k₁ k₂ + 4)
                * ((arithQ ρ (max l₁ l₂) : ℝ) + 1) := by ring
    -- the `uScale`-window estimate (the proved `uScale` version of the §8 fibre estimate)
    have hkey := hC₂ l₁ l₂ k₁ k₂ t f Bf hBf N' S ht hfarey' hstrictScale hnaScale
    have hφint : ∀ n : ℕ, Integrable (varphiNt (N' n) k₁ t) :=
      fun n => lacBump_integrable_varphiNt (N' n) k₁ t
    have hφsum : ∀ n : ℕ, Summable (fun j : ℤ => ‖cw (varphiNt (N' n) k₁ t) j‖) :=
      fun n => cw_varphiNt_summable (N' n) k₁ t
    have hU1rep : 1 ≤ uRep ρ l₁ l₂ k₁ k₂ := by
      rw [uRep]
      exact le_trans (by omega : 1 ≤ max l₁ l₂ + 3) (le_max_right _ _)
    have hU1scl : 1 ≤ uScale ρ (max (max l₁ l₂) (max k₁ k₂)) := one_le_uScale_bdd hρ.le _
    have hnaNewRep : NonAliasing (-(2 * (uRep ρ l₁ l₂ k₁ k₂ : ℤ))) (iwArithFreqsNew ρ l₁) :=
      nonAliasing_subset hnaRep (fun α hα => mem_iwArithFreqsNew_le hα)
    have hnaNewScl : NonAliasing (-(2 * (uScale ρ (max (max l₁ l₂) (max k₁ k₂)) : ℤ)))
        (iwArithFreqsNew ρ l₁) :=
      nonAliasing_subset hnaScale (fun α hα => mem_iwArithFreqsNew_le hα)
    have hwfn : ∀ n : ℕ, (if S n then Tex ρ l₁ (varphiNt (N' n) k₁ t) f else 0)
        = (if S n then Tex ρ l₁ (varphiNt (Nat.floor (a n)) k₁ t) f else 0) := by
      intro n
      by_cases hn : S n
      · rw [hN']; simp only [hn, if_true]
      · simp only [hn, if_false]
    -- the clip identity: both fibres are the window-free fibre, hence equal
    have hbridgeN : ∀ n₀ : ℤ, (fun n : ℕ => fiberOp ρ l₁ (mStarF (uRep ρ l₁ l₂ k₁ k₂)) n₀
          (if S n then Tex ρ l₁ (varphiNt (N' n) k₁ t) f else 0))
        = (fun n : ℕ => fiberOp ρ l₁
            (mStarF (uScale ρ (max (max l₁ l₂) (max k₁ k₂)))) n₀
          (if S n then Tex ρ l₁ (varphiNt (N' n) k₁ t) f else 0)) := by
      intro n₀
      funext n
      rw [fiberOp_mStarF_Sclip ρ hρ hρ1 l₁ (uRep ρ l₁ l₂ k₁ k₂) hU1rep hnaNewRep
            (varphiNt (N' n) k₁ t) (hφint n) (hφsum n)
            (fun ξ hξ => varphiNt_support_strict (N' n) k₁ t (uRep ρ l₁ l₂ k₁ k₂)
              (hstrictRep n) ξ hξ) f Bf hBf (S n) n₀,
          fiberOp_mStarF_Sclip ρ hρ hρ1 l₁ (uScale ρ (max (max l₁ l₂) (max k₁ k₂))) hU1scl
            hnaNewScl (varphiNt (N' n) k₁ t) (hφint n) (hφsum n)
            (fun ξ hξ => varphiNt_support_strict (N' n) k₁ t
              (uScale ρ (max (max l₁ l₂) (max k₁ k₂))) (hstrictScale n) ξ hξ) f Bf hBf
            (S n) n₀]
    have hbridge : ∀ n₀ : ℤ, (fun n : ℕ => fiberOp ρ l₁ (mStarF (uRep ρ l₁ l₂ k₁ k₂)) n₀
          (if S n then Tex ρ l₁ (varphiNt (Nat.floor (a n)) k₁ t) f else 0))
        = (fun n : ℕ => fiberOp ρ l₁
            (mStarF (uScale ρ (max (max l₁ l₂) (max k₁ k₂)))) n₀
          (if S n then Tex ρ l₁ (varphiNt (N' n) k₁ t) f else 0)) := by
      intro n₀
      have h1 : (fun n : ℕ => fiberOp ρ l₁ (mStarF (uRep ρ l₁ l₂ k₁ k₂)) n₀
            (if S n then Tex ρ l₁ (varphiNt (Nat.floor (a n)) k₁ t) f else 0))
          = (fun n : ℕ => fiberOp ρ l₁ (mStarF (uRep ρ l₁ l₂ k₁ k₂)) n₀
            (if S n then Tex ρ l₁ (varphiNt (N' n) k₁ t) f else 0)) := by
        funext n
        rw [← hwfn n]
      exact h1.trans (hbridgeN n₀)
    have hinner : (fun y (n₀ : ℕ) => variationalNorm r
          (fun n : ℕ => fiberOp ρ l₁ (mStarF (uRep ρ l₁ l₂ k₁ k₂)) n₀
            (if S n then Tex ρ l₁ (varphiNt (Nat.floor (a n)) k₁ t) f else 0) y))
        = (fun y (n₀ : ℕ) => variationalNorm r
          (fun n : ℕ => fiberOp ρ l₁ (mStarF (uScale ρ (max (max l₁ l₂) (max k₁ k₂)))) n₀
            (if S n then Tex ρ l₁ (varphiNt (N' n) k₁ t) f else 0) y)) := by
      funext y n₀
      exact congrArg (fun (F : ℕ → ℤ → ℂ) => variationalNorm r (fun n : ℕ => F n y))
        (hbridge (n₀ : ℤ))
    have hRHS : (fun x : ℤ => variationalNorm r (fun n : ℕ => (if S n then Tex ρ l₁
            (varphiNt (Nat.floor (a n)) k₁ t) f else 0) x))
        = (fun x : ℤ => variationalNorm r (fun n : ℕ => (if S n then Tex ρ l₁
            (varphiNt (N' n) k₁ t) f else 0) x)) :=
      congrArg (fun (F : ℕ → ℤ → ℂ) => fun x : ℤ => variationalNorm r (fun n : ℕ => F n x))
        (funext fun n => (hwfn n).symm)
    rw [hinner, hRHS]
    refine hkey.trans ?_
    rw [show lossWeight 0 ρ l₁ l₂ k₁ k₂ = 1 by simp [lossWeight], mul_one]
    exact mul_le_mul' (ENNReal.ofReal_le_ofReal (le_max_right C₁ C₂)) le_rfl

end Work.KMTAreas.A7
