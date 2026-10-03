/-
# The defect case of the low-case model approximation (area A6)

This module contains the *arithmetic* half of the target
`Work.KMTPlan.A6.LowModApproxNoAliasingCase`, and the reduction of that target to the two analytic
bounds on the two operators that occur in it.

## The two branches of the hypothesis

The hypothesis of the target is the disjunction

* `¬ NonAliasing (-(2 * uScale ρ (lcL l₁ l₂ k₁ k₂))) (iwArithFreqs ρ l₁ ∪ iwArithFreqs ρ l₂)`
  (the two arithmetic frequency sets are *not* separated at the model's window
  `2 ^ (-(2 * uScale ρ L))`), or
* there is an admissible large scale `N = ⌊a n⌋` in the main regime at which the *strict plateau*
  condition `max k₁ k₂ + 2 * uScale ρ L + 1 ≤ logN N` fails.

**Both branches force the height `L = lcL l₁ l₂ k₁ k₂` to be bounded by a constant depending only
on `ρ`.**  For the first branch this is the proved
`Work.KMTPlan.A6.lcL_le_of_not_nonAliasing` (the non-aliasing theorem `thm:iw` gives non-aliasing as
soon as the window is smaller than the separation `2 ^ (-Cρ * 2 ^ (ρ * max l₁ l₂))`, and the window
`2 ^ (-(2 * uScale ρ L))` is smaller than that as soon as `L` exceeds `⌈logb 2 Cρ / ρ⌉₊ + 1`).
For the second branch it is the elementary estimate `lcL_le_of_plateauFail` proved below:
`N > splitCut ρ L = 2 ^ (2 ^ u)`, `u = uScale ρ L`, gives `2 ^ u ≤ logN N`, while the failure of
the plateau gives `logN N < max k₁ k₂ + 2 * u + 1 ≤ L + 2 * u + 1`; since `u = ⌊2 ^ (2ρL)⌋ ≥ L`
and `2 ^ u ≥ 3 * u + 1` for `u ≥ 4` (`two_pow_uScale_ge_add`), a large `L` would give
`2 ^ u ≥ L + 2u + 1 > logN N ≥ 2 ^ u`, a contradiction.

## The reduction

With `L ≤ B(ρ)` for a `ρ`-dependent `B(ρ)`, the target follows from the two *bounded-height*
variational bounds

* `MainPieceBoundedH` for the concrete column `Work.KMTAreas.A7.mainPartTuple` (the halved average
  of the §5 pieces), and
* `ModelPieceBoundedH` for the §6 model operator `Work.KMTPlan.A6.mdlPart`,

together with the pointwise identity `modApproxErr = mainPartTuple − mdlPart` and the
subadditivity of the variational norm; the weight `lcWeight 1 l₁ l₂ k₁ k₂ = 2 ^ (-L)` is bounded
below by `2 ^ (-B(ρ))` on the bounded range of heights and is absorbed into the constant `K(Λ)`.
This is `lowModApproxNoAliasingCase_of_boundedH` below.
-/
import Mathlib
import Submission.Work.KMTPlan.A6.lowSmallModelVar
import Submission.Work.KMTAreas.A7.ExceptionalBound
import Submission.Port.Aesm

set_option maxHeartbeats 1000000

namespace Work.KMTPlan.A6

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems
open Submission.PointwiseErgodicTheorems
open Work.Analysis.EndVar
open Work.KMTContract
open Work.KMTAreas.A7
open Work.Analysis.IonescuWainger

/-! ## The arithmetic of the second branch: a failing strict plateau forces a bounded height -/

/-- `2 ^ u ≥ 3u + 1` for `u ≥ 4`. -/
theorem three_mul_add_one_le_two_pow : ∀ u : ℕ, 4 ≤ u → 3 * u + 1 ≤ 2 ^ u :=
  Nat.le_induction (m := 4) (by norm_num) (fun u _hu ih => by
    have h2 : 2 * (3 * u + 1) ≤ 2 * 2 ^ u := Nat.mul_le_mul_left 2 ih
    calc 3 * (u + 1) + 1 ≤ 2 * (3 * u + 1) := by omega
      _ ≤ 2 * 2 ^ u := h2
      _ = 2 ^ (u + 1) := by ring)

/-- **The window scale dominates `L` and `2 ^ u ≥ L + 2u + 1`.**  Beyond a `ρ`-dependent threshold
the window scale `u = uScale ρ L = ⌊2 ^ (2ρL)⌋` satisfies `2 ^ u ≥ L + 2u + 1`.  (The two inputs
are `u ≥ L`, which is `Work.KMTPlan.A6.uScale_window_arith`, and `u ≥ 4`, whence
`2 ^ u ≥ 3u + 1 ≥ L + 2u + 1`.) -/
theorem two_pow_uScale_ge_add (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ B : ℕ, ∀ L : ℕ, B ≤ L → L + 2 * uScale ρ L + 1 ≤ 2 ^ uScale ρ L := by
  obtain ⟨B₁, hB₁⟩ := uScale_window_arith ρ hρ
  refine ⟨max B₁ (max (Nat.ceil (2 / ρ) + 1) 4), fun L hL => ?_⟩
  obtain ⟨hLe, hpow⟩ := hB₁ L (le_trans (le_max_left _ _) hL)
  have hceil : Nat.ceil (2 / ρ) + 1 ≤ L :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hL
  have hu4 : 4 ≤ uScale ρ L := by
    have h1 : (2 : ℝ) / ρ ≤ (L : ℝ) := by
      have h2 : ((Nat.ceil (2 / ρ) : ℕ) : ℝ) ≤ (L : ℝ) := by
        have h22 : Nat.ceil (2 / ρ) ≤ L := by omega
        exact_mod_cast h22
      exact le_trans (Nat.le_ceil _) h2
    have h3 : (2 : ℝ) ≤ ρ * (L : ℝ) := by
      rw [div_le_iff₀ hρ] at h1
      linarith
    have h4 : (4 : ℝ) ≤ (2 : ℝ) ^ (ρ * (L : ℝ)) := by
      calc (4 : ℝ) = (2 : ℝ) ^ (2 : ℝ) := by norm_num
        _ ≤ (2 : ℝ) ^ (ρ * (L : ℝ)) := Real.rpow_le_rpow_of_exponent_le (by norm_num) h3
    have h5 : (4 : ℝ) ≤ (uScale ρ L : ℝ) := le_trans h4 hpow
    exact_mod_cast h5
  have hkey : 3 * uScale ρ L + 1 ≤ 2 ^ uScale ρ L := three_mul_add_one_le_two_pow _ hu4
  have h3u : L ≤ uScale ρ L := by exact_mod_cast hLe
  omega

/-- **A failing strict plateau forces a bounded height.**  If `N = ⌊a n⌋` is above the scale split
`splitCut ρ L = 2 ^ (2 ^ u)` (`u = uScale ρ L`) and the strict plateau condition
`max k₁ k₂ + 2u + 1 ≤ logN N` fails, then `L = lcL l₁ l₂ k₁ k₂` is bounded by a constant depending
only on `ρ`.

Indeed `N > 2 ^ (2 ^ u)` gives `2 ^ u ≤ Nat.log 2 N = logN N`, while the failure gives
`logN N < max k₁ k₂ + 2u + 1 ≤ L + 2u + 1`, and `L + 2u + 1 ≤ 2 ^ u` for `L` large. -/
theorem lcL_le_of_plateauFail (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ B : ℕ, ∀ (C₀ : ℕ) (a : ℕ → NNReal) (l₁ l₂ k₁ k₂ n : ℕ),
      splitCut ρ (lcL l₁ l₂ k₁ k₂) < Nat.floor (a n) →
      ¬ (max k₁ k₂ + 2 * uScale ρ (lcL l₁ l₂ k₁ k₂) + 1
          ≤ (logN (Nat.floor (a n))).toNat) →
      lcL l₁ l₂ k₁ k₂ ≤ B := by
  obtain ⟨B, hB⟩ := two_pow_uScale_ge_add ρ hρ
  refine ⟨B, fun C₀ a l₁ l₂ k₁ k₂ n hcut hfail => ?_⟩
  by_contra hnot
  rw [not_le] at hnot
  set L : ℕ := lcL l₁ l₂ k₁ k₂ with hL
  set N : ℕ := Nat.floor (a n) with hN
  set u : ℕ := uScale ρ L with hu
  have hsc : splitCut ρ L = 2 ^ (2 ^ u) := rfl
  have hcut' : 2 ^ (2 ^ u) < N := by rw [← hsc]; exact hcut
  have hN2 : 2 ≤ N := by
    have h1 : (2 : ℕ) ≤ 2 ^ (2 ^ u) := by
      have hone : 1 ≤ 2 ^ u := Nat.one_le_two_pow
      calc (2 : ℕ) = 2 ^ 1 := (pow_one 2).symm
        _ ≤ 2 ^ (2 ^ u) := Nat.pow_le_pow_right (by norm_num) hone
    omega
  have hlog : 2 ^ u ≤ Nat.log 2 N := by
    have h1 : Nat.log 2 (2 ^ (2 ^ u)) ≤ Nat.log 2 N := Nat.log_mono_right (le_of_lt hcut')
    rwa [Nat.log_pow (by norm_num : 1 < 2)] at h1
  have hlogN : logN N = (Nat.log 2 N : ℤ) := by
    rw [logN, max_eq_left hN2]
  have htoNat : (logN N).toNat = Nat.log 2 N := by
    rw [hlogN]; exact Int.toNat_natCast _
  have hlt : Nat.log 2 N < max k₁ k₂ + 2 * u + 1 := by
    have h := hfail
    rw [htoNat] at h
    omega
  have hcle : max k₁ k₂ ≤ L := by rw [hL]; exact le_max_right _ _
  have hkey : L + 2 * u + 1 ≤ 2 ^ u := by
    have h := hB L (le_of_lt hnot)
    rwa [← hu] at h
  omega

/-! ## The two operators of the model approximation -/

/-- **The bounded-height variational bound for the concrete column family.**  For every `ρ > 0`
and every bound `B` on the height `L = lcL l₁ l₂ k₁ k₂`, the `ℓ¹(ℤ;V^r)`-norm of the concrete §5
column `mainPartTuple` (the halved average of the pieces) is bounded by `K(Λ) ‖f‖₂ ‖g‖₂`, uniformly
in the lacunary sequence and in the functions.

This is the large-scale (§6--§8) analysis of Krause--Mirek--Tao at the exponents `(2,2,1)`, at
*intermediately many* arithmetic heights; the constant may depend on `ρ` and `B`. -/
def MainPieceBoundedH (P : Polynomial ℤ) (r : NNReal) (C₀ : ℕ) (ρ : ℝ) (B : ℕ) : Prop :=
  ∃ K : NNReal → NNReal,
    ∀ (a : ℕ → NNReal) (Λ : NNReal) (l₁ l₂ k₁ k₂ : ℕ) (f g : ℤ → ℂ),
      1 < Λ → Lacunary Λ a → (∀ m, 1 ≤ a m) →
      lcL l₁ l₂ k₁ k₂ ≤ B → (k₁ = 0 ∨ k₂ = 0) →
      eLpNorm (fun x : ℤ => variationalNorm r
          (fun n : ℕ => mainPartTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x))
        1 Measure.count
        ≤ (K Λ : ENNReal) * eLpNorm f 2 Measure.count * eLpNorm g 2 Measure.count

/-- **The bounded-height variational bound for the §6 model operator.**  Same statement with the
model `mdlPart` (the twisted bilinear multiplier applied to the exact-height shells) in place of
the concrete column. -/
def ModelPieceBoundedH (P : Polynomial ℤ) (r : NNReal) (C₀ : ℕ) (ρ : ℝ) (B : ℕ) : Prop :=
  ∃ K : NNReal → NNReal,
    ∀ (a : ℕ → NNReal) (Λ : NNReal) (l₁ l₂ k₁ k₂ : ℕ) (f g : ℤ → ℂ),
      1 < Λ → Lacunary Λ a → (∀ m, 1 ≤ a m) →
      lcL l₁ l₂ k₁ k₂ ≤ B → (k₁ = 0 ∨ k₂ = 0) →
      eLpNorm (fun x : ℤ => variationalNorm r
          (fun n : ℕ => mdlPart ρ P C₀ a f g l₁ l₂ k₁ k₂ n x))
        1 Measure.count
        ≤ (K Λ : ENNReal) * eLpNorm f 2 Measure.count * eLpNorm g 2 Measure.count

/-- **The bounded-height variational bound for the concrete §5 column family** (the clamped
`varpCol` of the §6--§8 analysis, i.e. `Work.KMTAreas.A7.colTuple` restricted to the large scales).
This is the A6/A7 large-scale estimate at `(2,2,1)` at bounded heights, without the gain; the
constant may depend on `ρ` and `B`.  By `mainPieceBoundedH_of_colPieceBoundedH` it implies
`MainPieceBoundedH` (`mainPartTuple = colTuple − exceptionalPart`, and the exceptional part is
bounded unconditionally by the proved `Work.KMTAreas.A7.ExceptionalBound`). -/
def ColPieceBoundedH (P : Polynomial ℤ) (r : NNReal) (C₀ : ℕ) (ρ : ℝ) (B : ℕ) : Prop :=
  ∃ K : NNReal → NNReal,
    ∀ (a : ℕ → NNReal) (Λ : NNReal) (l₁ l₂ k₁ k₂ : ℕ) (f g : ℤ → ℂ),
      1 < Λ → Lacunary Λ a → (∀ m, 1 ≤ a m) →
      lcL l₁ l₂ k₁ k₂ ≤ B → (k₁ = 0 ∨ k₂ = 0) →
      eLpNorm (fun x : ℤ => variationalNorm r
          (fun n : ℕ => Work.KMTAreas.A7.colTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x))
        1 Measure.count
        ≤ (K Λ : ENNReal) * eLpNorm f 2 Measure.count * eLpNorm g 2 Measure.count

/-! ## Elementary bookkeeping for the weight -/

/-- The variational norm of a difference is at most the sum of the variational norms. -/
theorem variationalNorm_sub_le' {r : NNReal} (hr : 1 ≤ r) (a b : ℕ → ℂ) :
    variationalNorm r (a - b) ≤ variationalNorm r a + variationalNorm r b := by
  have h : a - b = a + (-1 : ℂ) • b := by
    funext n
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [h]
  refine (variationalNorm_add_le hr a ((-1 : ℂ) • b)).trans ?_
  rw [variationalNorm_smul hr]
  simp

/-- **The concrete side follows from the column bound.**  `mainPartTuple = colTuple − exceptionalPart`
pointwise, and the exceptional part is bounded *unconditionally* at `(2,2,1)` by the proved
`Work.KMTAreas.A7.ExceptionalBound` (no `AreaA1`/`improv` hypotheses); the variational norm and the
`ℒ¹` seminorm are subadditive. -/
theorem mainPieceBoundedH_of_colPieceBoundedH (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree)
    (r : NNReal) (hr : 2 < r) (C₀ : ℕ) (hC₀ : 1 ≤ C₀) (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (B : ℕ) (h : ColPieceBoundedH P r C₀ ρ B) : MainPieceBoundedH P r C₀ ρ B := by
  have hr1 : (1 : NNReal) ≤ r := le_of_lt (lt_trans (by norm_num) hr)
  obtain ⟨Kc, hKc⟩ := h
  obtain ⟨Kexc, hKexc⟩ := Work.KMTAreas.A7.ExceptionalBound P 2 2 hd (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by rw [ENNReal.inv_two_add_inv_two]) C₀ r hC₀ hr
  refine ⟨fun Λ => Kc Λ + Kexc Λ, ?_⟩
  intro a Λ l₁ l₂ k₁ k₂ f g hΛ ha ha1 hLB hQ
  have e₁ := hKc a Λ l₁ l₂ k₁ k₂ f g hΛ ha ha1 hLB hQ
  have e₂ := hKexc ρ a Λ l₁ l₂ k₁ k₂ f g hρ hρ1 hΛ ha ha1
  simp only [ENNReal.inv_two_add_inv_two, inv_one] at e₂
  set Fm : ℤ → ENNReal := fun x : ℤ =>
    variationalNorm r (fun n : ℕ => mainPartTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x) with hFm
  set Fc : ℤ → ENNReal := fun x : ℤ =>
    variationalNorm r (fun n : ℕ => Work.KMTAreas.A7.colTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x)
    with hFc
  set Fe : ℤ → ENNReal := fun x : ℤ => variationalNorm r
    (fun n : ℕ => Work.KMTAreas.A7.exceptionalPart ρ P C₀ a f g l₁ l₂ k₁ k₂ n x) with hFe
  have hpoint : ∀ x : ℤ, Fm x ≤ Fc x + Fe x := by
    intro x
    have hsub : (fun n : ℕ => mainPartTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x)
        = (fun n : ℕ => Work.KMTAreas.A7.colTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x)
          - (fun n : ℕ => Work.KMTAreas.A7.exceptionalPart ρ P C₀ a f g l₁ l₂ k₁ k₂ n x) := by
      funext n
      simp only [Work.KMTAreas.A7.exceptionalPart, Pi.sub_apply]
      ring
    simp only [hFm, hFc, hFe]
    rw [hsub]
    exact variationalNorm_sub_le' hr1 _ _
  calc eLpNorm (fun x : ℤ => Fm x) 1 Measure.count
      ≤ eLpNorm (fun x : ℤ => Fc x + Fe x) 1 Measure.count :=
        eLpNorm_mono_enorm (hf := by pw_aesm) (fun x => by simpa only [enorm_eq_self] using hpoint x)
    _ ≤ eLpNorm Fc 1 Measure.count + eLpNorm Fe 1 Measure.count :=
        eLpNorm_add_le le_rfl
    _ ≤ (Kc Λ : ENNReal) * eLpNorm f 2 Measure.count * eLpNorm g 2 Measure.count
        + (Kexc Λ : ENNReal) * eLpNorm f 2 Measure.count * eLpNorm g 2 Measure.count :=
        add_le_add (by simpa only [hFc] using e₁) (by simpa only [hFe] using e₂)
    _ = ((Kc Λ + Kexc Λ : NNReal) : ENNReal)
          * eLpNorm f 2 Measure.count * eLpNorm g 2 Measure.count := by
        push_cast
        ring

/-- `lcWeight 1 l₁ l₂ k₁ k₂ = 2 ^ (-L)`, `L = lcL l₁ l₂ k₁ k₂`. -/
theorem lcWeight_one_eq_lcL (l₁ l₂ k₁ k₂ : ℕ) :
    lcWeight 1 l₁ l₂ k₁ k₂ = (2 : ℝ) ^ (-(lcL l₁ l₂ k₁ k₂ : ℝ)) := by
  rw [lcWeight, ← lcL_eq, Int.cast_natCast]
  ring_nf

/-- `1 ≤ 2 ^ B · 2 ^ (-L)` for `L ≤ B`. -/
theorem one_le_two_pow_mul (B L : ℕ) (h : L ≤ B) :
    (1 : ℝ) ≤ (2 : ℝ) ^ (B : ℝ) * (2 : ℝ) ^ (-(L : ℝ)) := by
  rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  have h1 : (B : ℝ) + -(L : ℝ) = ((B - L : ℕ) : ℝ) := by
    push_cast [Nat.cast_sub h]
    ring
  rw [h1, Real.rpow_natCast]
  exact one_le_pow₀ (by norm_num)

/-! ## The reduction of the target to the two bounded-height bounds -/

/-- **The target follows from the two bounded-height variational bounds.**  Both branches of the
defect hypothesis force `L ≤ B(ρ)` (the first via `lcL_le_of_not_nonAliasing`, the second via
`lcL_le_of_plateauFail`); the two bounded-height bounds applied at `B(ρ)` control the two operators,
and `modApproxErr = mainPartTuple − mdlPart` with the subadditivity of the variational norm
finishes, the weight `2 ^ (-L)` being absorbed into `K(Λ)` on the bounded range of heights. -/
theorem lowModApproxNoAliasingCase_of_boundedH (P : Polynomial ℤ) (r : NNReal) (hr : 2 < r)
    (C₀ : ℕ)
    (hmain : ∀ ρ : ℝ, 0 < ρ → ∀ B : ℕ, MainPieceBoundedH P r C₀ ρ B)
    (hmdl : ∀ ρ : ℝ, 0 < ρ → ∀ B : ℕ, ModelPieceBoundedH P r C₀ ρ B) :
    ∃ c : ℝ, 0 < c ∧ ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ →
      ∃ K : NNReal → NNReal,
      ∀ (a : ℕ → NNReal) (Λ : NNReal) (l₁ l₂ k₁ k₂ : ℕ) (f g : ℤ → ℂ),
        1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ m, 1 ≤ a m) →
        (k₁ = 0 ∨ k₂ = 0) →
        (¬ (Work.Analysis.IonescuWainger.NonAliasing
              (-(2 * (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) : ℤ)))
              (Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁
                ∪ Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂))
          ∨ ∃ n : ℕ,
              Work.Analysis.EndVar.inIndexSet C₀ (max (l₁ : ℤ) (l₂ : ℤ)) (k₁ : ℤ) (k₂ : ℤ)
                  (Nat.floor (a n)) ∧
              Work.KMTAreas.A7.splitCut ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) < Nat.floor (a n) ∧
              Work.KMTAreas.A7.mainRegime ρ k₁ k₂ (Nat.floor (a n)) ∧
              ¬ (max k₁ k₂ + 2 * Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) + 1
                  ≤ (Work.Analysis.EndVar.logN (Nat.floor (a n))).toNat)) →
        MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => Work.KMTPlan.A6.modApproxErr ρ P C₀ a f g l₁ l₂ k₁ k₂ n x))
          1 MeasureTheory.Measure.count
          ≤ (K Λ : ENNReal) * ENNReal.ofReal (Work.KMTPlan.A6.lcWeight c l₁ l₂ k₁ k₂)
              * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count
              * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count := by
  have hr1 : (1 : NNReal) ≤ r := le_of_lt (lt_trans (by norm_num) hr)
  refine ⟨1, one_pos, 1, one_pos, ?_⟩
  intro ρ hρ hρ1
  obtain ⟨Cna, hCnaps, hna0⟩ := exists_goodMajorArcs_nonAliasing hρ
  have hsize : ∀ (l : ℕ) (K : ℤ),
      (K : ℝ) + Cna * (2 : ℝ) ^ (ρ * (l : ℝ)) < 0 → NonAliasing K (iwArithFreqs ρ l) := by
    intro l K hK
    refine hna0 l K ?_
    show (K : ℝ) ≤ -Cna * (2 : ℝ) ^ (ρ * (l : ℝ))
    linarith
  obtain ⟨B₂, hB₂⟩ := lcL_le_of_plateauFail ρ hρ
  set B : ℕ := max (⌈Real.logb 2 Cna / ρ⌉₊ + 1) B₂ with hBdef
  obtain ⟨K₁, hK₁⟩ := hmain ρ hρ B
  obtain ⟨K₂, hK₂⟩ := hmdl ρ hρ B
  refine ⟨fun Λ => (K₁ Λ + K₂ Λ) * (2 : NNReal) ^ B, ?_⟩
  intro a Λ l₁ l₂ k₁ k₂ f g hΛ ha ha1 hQ hdef
  have hLB : lcL l₁ l₂ k₁ k₂ ≤ B := by
    rcases hdef with hna | ⟨n, _hidx, hcut, _hreg, hfail⟩
    · refine le_trans (lcL_le_of_not_nonAliasing ρ hρ hρ1 Cna hCnaps hsize l₁ l₂ k₁ k₂ hna) ?_
      rw [hBdef]; exact le_max_left _ _
    · refine le_trans (hB₂ C₀ a l₁ l₂ k₁ k₂ n hcut hfail) ?_
      rw [hBdef]; exact le_max_right _ _
  have e₁ := hK₁ a Λ l₁ l₂ k₁ k₂ f g hΛ ha ha1 hLB hQ
  have e₂ := hK₂ a Λ l₁ l₂ k₁ k₂ f g hΛ ha ha1 hLB hQ
  set Fm : ℤ → ENNReal := fun x : ℤ =>
    variationalNorm r (fun n : ℕ => mainPartTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x) with hFm
  set Fd : ℤ → ENNReal := fun x : ℤ =>
    variationalNorm r (fun n : ℕ => mdlPart ρ P C₀ a f g l₁ l₂ k₁ k₂ n x) with hFd
  set Fe : ℤ → ENNReal := fun x : ℤ =>
    variationalNorm r (fun n : ℕ => modApproxErr ρ P C₀ a f g l₁ l₂ k₁ k₂ n x) with hFe
  have hpt : ∀ x : ℤ, Fe x ≤ Fm x + Fd x := by
    intro x
    have hsub : (fun n : ℕ => modApproxErr ρ P C₀ a f g l₁ l₂ k₁ k₂ n x)
        = (fun n : ℕ => mainPartTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x)
          - (fun n : ℕ => mdlPart ρ P C₀ a f g l₁ l₂ k₁ k₂ n x) := by
      funext n
      rfl
    simp only [hFe, hFm, hFd]
    rw [hsub]
    exact variationalNorm_sub_le' hr1 _ _
  have hmono : eLpNorm (fun x : ℤ => Fe x) 1 Measure.count
      ≤ eLpNorm (fun x : ℤ => Fm x + Fd x) 1 Measure.count :=
    eLpNorm_mono_enorm (hf := by pw_aesm) (fun x => by simpa only [enorm_eq_self] using hpt x)
  have hadd : eLpNorm (fun x : ℤ => Fm x + Fd x) 1 Measure.count
      ≤ eLpNorm Fm 1 Measure.count + eLpNorm Fd 1 Measure.count :=
    eLpNorm_add_le le_rfl
  have hgain : (1 : ENNReal) ≤ ENNReal.ofReal ((2 : ℝ) ^ (B : ℝ))
      * ENNReal.ofReal (lcWeight 1 l₁ l₂ k₁ k₂) := by
    rw [lcWeight_one_eq_lcL, ← ENNReal.ofReal_one, ← ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.ofReal_le_ofReal (one_le_two_pow_mul B (lcL l₁ l₂ k₁ k₂) hLB)
  have h2B : (((2 : NNReal) ^ B : NNReal) : ENNReal) = ENNReal.ofReal ((2 : ℝ) ^ (B : ℝ)) := by
    rw [← ENNReal.ofReal_coe_nnreal]
    congr 1
    push_cast
    rw [Real.rpow_natCast]
  have hcoef : ((K₁ Λ + K₂ Λ : NNReal) : ENNReal)
      ≤ (((K₁ Λ + K₂ Λ) * (2 : NNReal) ^ B : NNReal) : ENNReal)
          * ENNReal.ofReal (lcWeight 1 l₁ l₂ k₁ k₂) := by
    rw [ENNReal.coe_mul, h2B, mul_assoc]
    calc ((K₁ Λ + K₂ Λ : NNReal) : ENNReal)
        = ((K₁ Λ + K₂ Λ : NNReal) : ENNReal) * 1 := (mul_one _).symm
      _ ≤ ((K₁ Λ + K₂ Λ : NNReal) : ENNReal)
            * (ENNReal.ofReal ((2 : ℝ) ^ (B : ℝ))
              * ENNReal.ofReal (lcWeight 1 l₁ l₂ k₁ k₂)) := mul_le_mul' le_rfl hgain
      _ = ((K₁ Λ + K₂ Λ : NNReal) : ENNReal)
            * (ENNReal.ofReal ((2 : ℝ) ^ (B : ℝ))
              * ENNReal.ofReal (lcWeight 1 l₁ l₂ k₁ k₂)) := by ring
  calc eLpNorm (fun x : ℤ => Fe x) 1 Measure.count
      ≤ eLpNorm (fun x : ℤ => Fm x + Fd x) 1 Measure.count := hmono
    _ ≤ eLpNorm Fm 1 Measure.count + eLpNorm Fd 1 Measure.count := hadd
    _ ≤ (K₁ Λ : ENNReal) * eLpNorm f 2 Measure.count * eLpNorm g 2 Measure.count
        + (K₂ Λ : ENNReal) * eLpNorm f 2 Measure.count * eLpNorm g 2 Measure.count :=
        add_le_add (by simpa only [hFm] using e₁) (by simpa only [hFd] using e₂)
    _ = ((K₁ Λ + K₂ Λ : NNReal) : ENNReal)
          * eLpNorm f 2 Measure.count * eLpNorm g 2 Measure.count := by
        push_cast
        ring
    _ ≤ ((((K₁ Λ + K₂ Λ) * (2 : NNReal) ^ B : NNReal)) : ENNReal)
          * ENNReal.ofReal (lcWeight 1 l₁ l₂ k₁ k₂)
          * eLpNorm f 2 Measure.count * eLpNorm g 2 Measure.count := by
        exact mul_le_mul' (mul_le_mul' hcoef le_rfl) le_rfl

/-- **The defect case of the low-case model approximation.**  See the module docstring. -/
theorem LowModApproxNoAliasingCase (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (r : NNReal) (hr : 2 < r)
    (C₀ : ℕ) (hC₀ : 1 ≤ C₀) (hA1 : Work.KMTContract.AreaA1) :
    ∃ c : ℝ, 0 < c ∧ ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ →
      ∃ K : NNReal → NNReal,
      ∀ (a : ℕ → NNReal) (Λ : NNReal) (l₁ l₂ k₁ k₂ : ℕ) (f g : ℤ → ℂ),
        1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ m, 1 ≤ a m) →
        (k₁ = 0 ∨ k₂ = 0) →
        (¬ (Work.Analysis.IonescuWainger.NonAliasing
              (-(2 * (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) : ℤ)))
              (Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁
                ∪ Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂))
          ∨ ∃ n : ℕ,
              Work.Analysis.EndVar.inIndexSet C₀ (max (l₁ : ℤ) (l₂ : ℤ)) (k₁ : ℤ) (k₂ : ℤ)
                  (Nat.floor (a n)) ∧
              Work.KMTAreas.A7.splitCut ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) < Nat.floor (a n) ∧
              Work.KMTAreas.A7.mainRegime ρ k₁ k₂ (Nat.floor (a n)) ∧
              ¬ (max k₁ k₂ + 2 * Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) + 1
                  ≤ (Work.Analysis.EndVar.logN (Nat.floor (a n))).toNat)) →
        MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => Work.KMTPlan.A6.modApproxErr ρ P C₀ a f g l₁ l₂ k₁ k₂ n x))
          1 MeasureTheory.Measure.count
          ≤ (K Λ : ENNReal) * ENNReal.ofReal (Work.KMTPlan.A6.lcWeight c l₁ l₂ k₁ k₂)
              * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count
              * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count := by sorry

end

end Work.KMTPlan.A6
