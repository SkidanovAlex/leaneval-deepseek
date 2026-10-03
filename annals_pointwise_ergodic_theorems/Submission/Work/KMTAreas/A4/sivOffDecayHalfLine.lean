/-
# Lemma `iw-prop`(i): the off-diagonal decay in half-line form

Krause--Mirek--Tao, Ann. of Math. 195 (2022), Lemma `iw-prop`(i), second half, is stated for
the `ℓ^q`-norm of the projection `Π_{≤l,≤k}` over a *window* `[c,d]` placed to the right of the
support `[a,b]` of the input (with `b < c`), the gain being the negative power
`max (2^k (c - b)) 1 ^ (-M)` of the distance from the support to the window.
(`Work.KMTAreas.A4.OffDecayClaim ρ`, proved in `A4/offDecayKMT`, is exactly that statement,
for every `1 < q < ∞` and every order `M`.)

This module derives from it the two **half-line** forms actually consumed by §5.1: for `q = 2`
the window may be the whole half-line `[c,∞)` (equivalently, by reflection, `(-∞,c]`):

* `‖1_{[c,∞)} Π_{≤l,≤k} f‖_{ℓ²} ≤ C ⟨l⟩ ⟨2^k (c-b)⟩^{-M} ‖f‖_{ℓ²}` for `b < c`;
* `‖1_{(-∞,c]} Π_{≤l,≤k} f‖_{ℓ²} ≤ C ⟨l⟩ ⟨2^k (a-c)⟩^{-M} ‖f‖_{ℓ²}` for `c < a`,

where `f` is supported in `[a,b]`.  The half-line form is the one in which the off-diagonal part
of the second dual function of §5.1 is estimated (the off-diagonal region there is a half-line,
not a bounded window).

## The two steps

* **The right half-line.**  The truncations `1_{[c,d]} u` increase monotonically to `1_{[c,∞)} u`,
  so monotone convergence in the form `Commons.Analysis.MeasureTheory.eLpNorm_iSup_of_monotone`
  (which is `(⨆ f)^{1/2} = ⨆ f^{1/2}` on top of `lintegral_iSup`) gives
  `‖1_{[c,∞)} u‖_{ℓ²} = ⨆_{d} ‖1_{[c,d]} u‖_{ℓ²}`.  Every interval bound carries the *same*
  constant — `c - b` does not depend on `d` — so the supremum of the interval bounds is the
  half-line bound.
* **The left half-line.**  Reflection `x ↦ -x` of the ambient group `ℤ` is a measure-preserving
  bijection of the counting measure (`eLpNorm_neg_count`), and the kernel of the Ionescu--Wainger
  projection is even (`kmtProj_reflect`), so `Π_{≤l,≤k}` commutes with reflection.  Applying the
  right half-line bound to the reflected input `x ↦ f (-x)` — whose support is `[-b,-a]`, at
  distance `(-c) - (-a) = a - c` from the half-line `(-∞,c]`, written as `x ≥ -c` — gives the
  left half-line bound with the other distance.
-/
import Mathlib
import Submission.Work.KMTAreas.A4.ImprovOneClaims
import Submission.Work.KMTAreas.A4.kmtProj_reflect
import Submission.Commons.Analysis.MeasureTheory.eLpNorm_iSup_of_monotone
import Submission.Port.Aesm

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

open MeasureTheory Classical
open scoped ENNReal NNReal BigOperators

namespace Work.KMTAreas.A4

open Work.Analysis.IonescuWainger (GoodMajorArcs)

noncomputable section

/-! ## Reflection -/

/-- Negation on `ℤ` preserves counting measure. -/
private lemma measurePreserving_neg_count :
    MeasurePreserving (fun x : ℤ => -x) (Measure.count : Measure ℤ)
      (Measure.count : Measure ℤ) := by
  refine MeasurePreserving.mk measurable_neg ?_
  ext s hs
  rw [Measure.map_apply measurable_neg hs]
  have hpre : (fun x : ℤ => -x) ⁻¹' s = Neg.neg '' s := by
    ext y; simp
  rw [hpre]
  exact Measure.count_injective_image neg_injective s

/-- Reflection of the argument preserves the `ℒᵖ`-seminorm against the counting measure on `ℤ`. -/
private lemma eLpNorm_neg_count (u : ℤ → ℂ) (p : ENNReal) :
    eLpNorm (fun n : ℤ => u (-n)) p (Measure.count : Measure ℤ)
      = eLpNorm u p (Measure.count : Measure ℤ) := by
  rw [show (fun n : ℤ => u (-n)) = u ∘ (fun n : ℤ => -n) from rfl,
    eLpNorm_comp_measurePreserving _ measurePreserving_neg_count]
  exact (measurable_of_countable u).aestronglyMeasurable

/-- The `ℒ²`-norm of the left half-line `(-∞,c]` of a reflected function is the `ℒ²`-norm of the
left half-line `(-∞,c]` of the function: the substitution `x ↦ -x` (a measure-preserving
bijection for the counting measure) turns the condition `-c ≤ x` into `x ≤ c`. -/
private lemma eLpNorm_halfRight_neg (g : ℤ → ℂ) (c : ℤ) :
    eLpNorm (fun x : ℤ => if -c ≤ x then g (-x) else 0) (2 : ENNReal) (Measure.count : Measure ℤ)
      = eLpNorm (fun x : ℤ => if x ≤ c then g x else 0) (2 : ENNReal)
          (Measure.count : Measure ℤ) := by
  have h1 : (fun x : ℤ => if -c ≤ x then g (-x) else 0)
      = ((fun x : ℤ => if x ≤ c then g x else 0) ∘ (fun x : ℤ => -x)) := by
    funext x
    simp only [Function.comp_apply]
    by_cases hx : -c ≤ x
    · have hx' : -x ≤ c := by omega
      rw [if_pos hx, if_pos hx']
    · have hx' : ¬ (-x ≤ c) := by omega
      rw [if_neg hx, if_neg hx']
  rw [h1, eLpNorm_comp_measurePreserving _ measurePreserving_neg_count]
  exact (measurable_of_countable _).aestronglyMeasurable

/-! ## The right half-line as the supremum of its windows -/

/-- Pointwise exhaustion of the right half-line `[c,∞)` by the windows `[c,d]`. -/
private lemma enorm_halfLineRight_eq_iSup (g : ℤ → ℂ) (c : ℤ) (x : ℤ) :
    ‖(if c ≤ x then g x else 0 : ℂ)‖ₑ
      = ⨆ d : ℕ, ‖(if c ≤ x ∧ x ≤ (d : ℤ) then g x else 0 : ℂ)‖ₑ := by
  by_cases hx : c ≤ x
  · refine le_antisymm ?_ (iSup_le fun d => ?_)
    · have hmem : c ≤ x ∧ x ≤ (x.natAbs : ℤ) := ⟨hx, Int.le_natAbs⟩
      rw [if_pos hx]
      simpa only [if_pos hmem] using
        le_iSup (fun d : ℕ => ‖(if c ≤ x ∧ x ≤ (d : ℤ) then g x else 0 : ℂ)‖ₑ) x.natAbs
    · by_cases hd : x ≤ (d : ℤ)
      · rw [if_pos ⟨hx, hd⟩, if_pos hx]
      · rw [if_neg (fun h => hd h.2)]
        simp
  · have h : ∀ d : ℕ, ‖(if c ≤ x ∧ x ≤ (d : ℤ) then g x else 0 : ℂ)‖ₑ = 0 := by
      intro d
      rw [if_neg (fun hh => hx hh.1)]
      simp
    have hsup : (⨆ d : ℕ, ‖(if c ≤ x ∧ x ≤ (d : ℤ) then g x else 0 : ℂ)‖ₑ) = 0 := by
      rw [show (⨆ d : ℕ, ‖(if c ≤ x ∧ x ≤ (d : ℤ) then g x else 0 : ℂ)‖ₑ)
            = ⨆ _ : ℕ, (0 : ENNReal) from iSup_congr h]
      exact iSup_const
    rw [if_neg hx, hsup]
    simp

/-- **The `ℒ²`-norm of the right half-line is the supremum of the `ℒ²`-norms of its windows**
(monotone convergence). -/
private lemma eLpNorm_halfLineRight_eq_iSup (g : ℤ → ℂ) (c : ℤ) :
    eLpNorm (fun x : ℤ => if c ≤ x then g x else 0) (2 : ENNReal) (Measure.count : Measure ℤ)
      = ⨆ d : ℕ, eLpNorm (fun x : ℤ => if c ≤ x ∧ x ≤ (d : ℤ) then g x else 0)
          (2 : ENNReal) (Measure.count : Measure ℤ) := by
  have hmono : Monotone fun d : ℕ => fun x : ℤ =>
      ‖(if c ≤ x ∧ x ≤ (d : ℤ) then g x else 0 : ℂ)‖ₑ := by
    intro d d' hdd' x
    show ‖(if c ≤ x ∧ x ≤ (d : ℤ) then g x else 0 : ℂ)‖ₑ
      ≤ ‖(if c ≤ x ∧ x ≤ (d' : ℤ) then g x else 0 : ℂ)‖ₑ
    by_cases hx : c ≤ x
    · by_cases hd : x ≤ (d : ℤ)
      · have hd' : x ≤ (d' : ℤ) := hd.trans (Int.ofNat_le.mpr hdd')
        rw [if_pos ⟨hx, hd⟩, if_pos ⟨hx, hd'⟩]
      · rw [if_neg (fun h => hd h.2)]
        simp
    · rw [if_neg (fun h => hx h.1)]
      simp
  calc eLpNorm (fun x : ℤ => if c ≤ x then g x else 0) (2 : ENNReal) (Measure.count : Measure ℤ)
      = eLpNorm (fun x : ℤ => ‖(if c ≤ x then g x else 0 : ℂ)‖ₑ) (2 : ENNReal)
          (Measure.count : Measure ℤ) :=
        eLpNorm_congr_enorm_ae (hf := by pw_aesm) (hg := by pw_aesm) (Filter.Eventually.of_forall fun x => by simp)
    _ = eLpNorm (fun x : ℤ => ⨆ d : ℕ, ‖(if c ≤ x ∧ x ≤ (d : ℤ) then g x else 0 : ℂ)‖ₑ)
          (2 : ENNReal) (Measure.count : Measure ℤ) :=
        eLpNorm_congr_enorm_ae (hf := by pw_aesm) (hg := by pw_aesm)
          (Filter.Eventually.of_forall fun x => by simpa using enorm_halfLineRight_eq_iSup g c x)
    _ = ⨆ d : ℕ, eLpNorm (fun x : ℤ => ‖(if c ≤ x ∧ x ≤ (d : ℤ) then g x else 0 : ℂ)‖ₑ)
          (2 : ENNReal) (Measure.count : Measure ℤ) :=
        Commons.Analysis.MeasureTheory.eLpNorm_iSup_of_monotone (μ := (Measure.count : Measure ℤ))
          (p := (2 : ENNReal))
          (u := fun d : ℕ => fun x : ℤ =>
            ‖(if c ≤ x ∧ x ≤ (d : ℤ) then g x else 0 : ℂ)‖ₑ)
          (by norm_num) (by norm_num) (fun d => measurable_of_countable _) hmono
    _ = ⨆ d : ℕ, eLpNorm (fun x : ℤ => if c ≤ x ∧ x ≤ (d : ℤ) then g x else 0)
          (2 : ENNReal) (Measure.count : Measure ℤ) := by
        refine iSup_congr fun d => ?_
        exact eLpNorm_congr_enorm_ae (hf := by pw_aesm) (hg := by pw_aesm) (Filter.Eventually.of_forall fun x => by simp)

/-! ## The window form implies the half-line form -/

/-- **The right half-line.**  If the interval (window) form of the off-diagonal decay at `q = 2`
holds with a constant independent of the window, then so does the right half-line form. -/
private lemma halfLineRight_of_interval (ρ : ℝ) (Cρ : ℝ) (C : NNReal) (M : ℕ)
    (h : ∀ (l : ℕ) (k : ℤ), GoodMajorArcs ρ Cρ l k → ∀ (a b c d : ℤ) (f : ℤ → ℂ), b < c →
      (∀ x : ℤ, x < a ∨ b < x → f x = 0) →
      eLpNorm (fun x : ℤ => if c ≤ x ∧ x ≤ d then Work.KMTContract.kmtProj ρ l k f x else 0)
          (2 : ENNReal) (Measure.count : Measure ℤ)
        ≤ (C : ENNReal) * ENNReal.ofReal (max ((l : ℝ)) 1 *
              (max ((2 : ℝ) ^ k * ((c - b : ℤ) : ℝ)) 1) ^ (-(M : ℝ))) *
          eLpNorm f (2 : ENNReal) (Measure.count : Measure ℤ)) :
    ∀ (l : ℕ) (k : ℤ), GoodMajorArcs ρ Cρ l k → ∀ (a b c : ℤ) (f : ℤ → ℂ), b < c →
      (∀ x : ℤ, x < a ∨ b < x → f x = 0) →
      eLpNorm (fun x : ℤ => if c ≤ x then Work.KMTContract.kmtProj ρ l k f x else 0)
          (2 : ENNReal) (Measure.count : Measure ℤ)
        ≤ (C : ENNReal) * ENNReal.ofReal (max ((l : ℝ)) 1 *
              (max ((2 : ℝ) ^ k * ((c - b : ℤ) : ℝ)) 1) ^ (-(M : ℝ))) *
          eLpNorm f (2 : ENNReal) (Measure.count : Measure ℤ) := by
  intro l k hGA a b c f hbc hsupp
  refine le_trans (le_of_eq ?_) (iSup_le fun d : ℕ => h l k hGA a b c (d : ℤ) f hbc hsupp)
  exact eLpNorm_halfLineRight_eq_iSup (Work.KMTContract.kmtProj ρ l k f) c

/-- **The left half-line.**  The reflected form of `halfLineRight_of_interval`: for `f` supported
in `[a,b]` with `c < a`, the `ℒ²`-norm of the left half-line `(-∞,c]` of `Π_{≤l,≤k} f` decays
like the negative `M`-th power of the distance `a - c`. -/
private lemma halfLineLeft_of_interval (ρ : ℝ) (Cρ : ℝ) (C : NNReal) (M : ℕ)
    (h : ∀ (l : ℕ) (k : ℤ), GoodMajorArcs ρ Cρ l k → ∀ (a b c : ℤ) (f : ℤ → ℂ), b < c →
      (∀ x : ℤ, x < a ∨ b < x → f x = 0) →
      eLpNorm (fun x : ℤ => if c ≤ x then Work.KMTContract.kmtProj ρ l k f x else 0)
          (2 : ENNReal) (Measure.count : Measure ℤ)
        ≤ (C : ENNReal) * ENNReal.ofReal (max ((l : ℝ)) 1 *
              (max ((2 : ℝ) ^ k * ((c - b : ℤ) : ℝ)) 1) ^ (-(M : ℝ))) *
          eLpNorm f (2 : ENNReal) (Measure.count : Measure ℤ)) :
    ∀ (l : ℕ) (k : ℤ), GoodMajorArcs ρ Cρ l k → ∀ (a b c : ℤ) (f : ℤ → ℂ), c < a →
      (∀ x : ℤ, x < a ∨ b < x → f x = 0) → MemLp f (2 : ENNReal) (Measure.count : Measure ℤ) →
      eLpNorm (fun x : ℤ => if x ≤ c then Work.KMTContract.kmtProj ρ l k f x else 0)
          (2 : ENNReal) (Measure.count : Measure ℤ)
        ≤ (C : ENNReal) * ENNReal.ofReal (max ((l : ℝ)) 1 *
              (max ((2 : ℝ) ^ k * ((a - c : ℤ) : ℝ)) 1) ^ (-(M : ℝ))) *
          eLpNorm f (2 : ENNReal) (Measure.count : Measure ℤ) := by
  intro l k hGA a b c f hca hsupp hmem
  -- the reflected input lives on `[-b,-a]`, at distance `(-c) - (-a) = a - c` from `x ≥ -c`
  have hsupp' : ∀ x : ℤ, x < -b ∨ -a < x → (fun x : ℤ => f (-x)) x = 0 := by
    intro x hx
    rcases hx with hx | hx
    · exact hsupp (-x) (Or.inr (by omega))
    · exact hsupp (-x) (Or.inl (by omega))
  have hb := h l k hGA (-b) (-a) (-c) (fun x : ℤ => f (-x)) (by omega) hsupp'
  have hL : eLpNorm (fun x : ℤ => if -c ≤ x then
        Work.KMTContract.kmtProj ρ l k (fun y : ℤ => f (-y)) x else 0)
        (2 : ENNReal) (Measure.count : Measure ℤ)
      = eLpNorm (fun x : ℤ => if x ≤ c then Work.KMTContract.kmtProj ρ l k f x else 0)
          (2 : ENNReal) (Measure.count : Measure ℤ) := by
    rw [kmtProj_reflect ρ l k f hmem]
    exact eLpNorm_halfRight_neg (Work.KMTContract.kmtProj ρ l k f) c
  have hR : eLpNorm (fun x : ℤ => f (-x)) (2 : ENNReal) (Measure.count : Measure ℤ)
      = eLpNorm f (2 : ENNReal) (Measure.count : Measure ℤ) :=
    eLpNorm_neg_count f (2 : ENNReal)
  have hfac : (((-c : ℤ) - (-a : ℤ) : ℤ) : ℝ) = ((a - c : ℤ) : ℝ) := by push_cast; ring
  rw [hfac] at hb
  rw [hL, hR] at hb
  exact hb

/-! ## The main result -/

theorem sivOffDecayHalfLine (ρ : ℝ) (M : ℕ) (hOff : Work.KMTAreas.A4.OffDecayClaim ρ) :
    ∃ Cρ : ℝ, 0 < Cρ ∧ ∃ C : NNReal, 0 < C ∧
      (∀ (l : ℕ) (k : ℤ), Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l k →
        ∀ (a b c : ℤ) (f : ℤ → ℂ), b < c →
        (∀ x : ℤ, x < a ∨ b < x → f x = 0) →
        MeasureTheory.eLpNorm (fun x : ℤ => if c ≤ x then Work.KMTContract.kmtProj ρ l k f x else 0)
            (2 : ENNReal) MeasureTheory.Measure.count
          ≤ (C : ENNReal) * ENNReal.ofReal (max ((l : ℝ)) 1 *
                (max ((2 : ℝ) ^ k * ((c - b : ℤ) : ℝ)) 1) ^ (-(M : ℝ))) *
              MeasureTheory.eLpNorm f (2 : ENNReal) MeasureTheory.Measure.count) ∧
      (∀ (l : ℕ) (k : ℤ), Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l k →
        ∀ (a b c : ℤ) (f : ℤ → ℂ), c < a →
        (∀ x : ℤ, x < a ∨ b < x → f x = 0) →
        MeasureTheory.MemLp f (2 : ENNReal) MeasureTheory.Measure.count →
        MeasureTheory.eLpNorm (fun x : ℤ => if x ≤ c then Work.KMTContract.kmtProj ρ l k f x else 0)
            (2 : ENNReal) MeasureTheory.Measure.count
          ≤ (C : ENNReal) * ENNReal.ofReal (max ((l : ℝ)) 1 *
                (max ((2 : ℝ) ^ k * ((a - c : ℤ) : ℝ)) 1) ^ (-(M : ℝ))) *
              MeasureTheory.eLpNorm f (2 : ENNReal) MeasureTheory.Measure.count) := by
  obtain ⟨Cρ, hCρ, C, hC, hbound⟩ := hOff 2 (by norm_num) M
  simp_rw [show ENNReal.ofReal (2 : ℝ) = (2 : ENNReal) from by norm_num] at hbound
  refine ⟨Cρ, hCρ, C, hC, ?_, ?_⟩
  · exact halfLineRight_of_interval ρ Cρ C M hbound
  · exact halfLineLeft_of_interval ρ Cρ C M (halfLineRight_of_interval ρ Cρ C M hbound)

end

end Work.KMTAreas.A4
