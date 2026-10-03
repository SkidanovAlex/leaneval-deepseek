/-
# The algebraic clauses of the §8 adelic packet construction

`Work.KMTPlan.A6.AdelicPacketsProp` (the packet half of the adelic form `AdelicFormPropRange`, and
hence of `Work.KMTPlan.A6.AdelicRealizeBounded`) asks for two packet families
`u, v : ℕ → ℝ → ZMod Q → ℂ` and a lift `F` with

1. the band `HasRealFreqSupport (F n · ρ') (Icc (-1/(8Q)) (1/(8Q)))`,
2. the **diagonal identity** `F n (x:ℝ) (x % Q) = 1_{goodScale}·mdlSliceJ ⋯ n x`,
3. the **presentation** `F n X ρ' = zmodAvg (negReflect P) Q (u n X) (v n X) ρ'`,
4. the measurability of `X ↦ u n X θ` and of `X ↦ v n X θ`.

This module proves clauses 2, 3 and 4 for the canonical construction in which the packets are the
character combinations of the *band-limited lifts* `W α` of the window pieces of the two model
packets `mdlSliceF`, `mdlSliceG`,

  `u n X θ = 1_{goodScale Q L ⌊a n⌋} · Σ_{α ∈ iwArithFreqs ρ l₁} e(-θ.val·α)·W₁ α X`,   (and the
  `g`-side twin), and `F n X ρ' := zmodAvg (negReflect P) Q (u n X) (v n X) ((ρ' : ℤ) : ZMod Q)`,

so that clause 3 holds by definition (`rfl`).  The diagonal identity is the **proved**
`Work.KMTPlan.A6Clean.zmodAvgWindowPacketsNegReflect` (`form-1`/`form-2`: the fibre factorisation
`Btwist_eq_fiberSum` + the window-piece decomposition of a fibre) applied to the samples of the
lifts (`W α x = winConvR m (winModR (-α) h) x` for integer `x`; such `W` are produced by
`Work.KMTAreas.A7Rep.envelopeBandExtend`), together with `mdlSliceJ_eq_Btwist`.

The remaining analytic input (the `VrLiftDataP`/`Ku` bounds, clauses (5)–(8) of the adelic form) is
*not* addressed here.

-/
import Mathlib
import Submission.Work.KMTPlan.A6Clean.zmodAvgWindowPacketsNegReflect
import Submission.Work.KMTPlan.A6.MdlAdelicLiftPackets

-- v4.35 port: restore the v4.34 instance-unification behaviour (respectTransparency) in this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- (2026-10-03) Repointed from `Submission.Work.KMTPlan.A6.MdlSliceCoreGainBig` (which now
-- re-exports the copied §8 chain of `Submission/Work/A6Big/`, whose declarations carry the same
-- names as the ones this file's import tree provides) to the new home of the definitions
-- `mdlSliceF/G` / `MdlSliceCoreGainMemLp`: `Submission.Work.A6Big.Defs`.

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Work.KMTPlan.A6Clean

open MeasureTheory Polynomial Finset
open scoped BigOperators
open Work.KMTAreas.A7
open Work.KMTPlan.A6

local notation "Circ" => Work.Analysis.IonescuWainger.Circle

/-- **The diagonal identity of the packet construction** (clause (2) of
`Work.KMTPlan.A6.AdelicPacketsProp`): for the packet profiles whose `θ`-th Fourier coefficient is
the band-limited lift `W α` of the window piece of the model packet, evaluated at the integer `x`,
the `zmodAvg (negReflect P)`-average equals the frozen slice `mdlSliceJ` at `x`. -/
theorem zmodAvg_packets_eq_slice (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (P : ℤ[X]) (C₀ : ℕ)
    (a : ℕ → NNReal) (f g : ℤ → ℂ) (l₁ l₂ k₁ k₂ : ℕ) (j₁ j₂ : ℤ) (t : ℝ) (n : ℕ) (x : ℤ)
    (hj₁ : j₁ ∈ ({-1, 0, 1} : Finset ℤ)) (hj₂ : j₂ ∈ ({-1, 0, 1} : Finset ℤ))
    (hk₁ : k₁ = 0 → j₁ ≠ -1) (hk₂ : k₂ = 0 → j₂ ≠ -1)
    (W₁ W₂ : Circ → ℝ → ℂ)
    (hW₁ : ∀ α ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁,
      W₁ α (x : ℝ) = winConvR (mStarF (uScale ρ (lcL l₁ l₂ k₁ k₂)))
        (winModR (-α) (mdlSliceF ρ C₀ a l₁ l₂ k₁ k₂ j₁ t f n)) x)
    (hW₂ : ∀ β ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂,
      W₂ β (x : ℝ) = winConvR (mStargF P.natDegree (uScale ρ (lcL l₁ l₂ k₁ k₂)))
        (winModR (-β) (mdlSliceG ρ P C₀ a l₁ l₂ k₁ k₂ j₂ t g n)) x)
    (hsum₁ : ∀ z : ℤ, Summable (fun j : ℤ =>
      cw (mStarF (uScale ρ (lcL l₁ l₂ k₁ k₂))) j *
        mdlSliceF ρ C₀ a l₁ l₂ k₁ k₂ j₁ t f n (z - j)))
    (hsum₂ : ∀ z : ℤ, Summable (fun j : ℤ =>
      cw (mStargF P.natDegree (uScale ρ (lcL l₁ l₂ k₁ k₂))) j *
        mdlSliceG ρ P C₀ a l₁ l₂ k₁ k₂ j₂ t g n (z - j))) :
    Work.KMTPlan.A6.zmodAvg (Work.KMTPlan.A6.negReflect P) (arithQ ρ (max l₁ l₂))
      (fun θ : ZMod (arithQ ρ (max l₁ l₂)) =>
        ∑ α ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁,
          fourier (T := 1) (-(θ.val : ℤ)) α * W₁ α (x : ℝ))
      (fun θ : ZMod (arithQ ρ (max l₁ l₂)) =>
        ∑ β ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂,
          fourier (T := 1) (-(θ.val : ℤ)) β * W₂ β (x : ℝ))
      ((x : ℤ) : ZMod (arithQ ρ (max l₁ l₂)))
    = mdlSliceJ ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ t n x := by
  have hL : (fun θ : ZMod (arithQ ρ (max l₁ l₂)) =>
        ∑ α ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁,
          fourier (T := 1) (-(θ.val : ℤ)) α * W₁ α (x : ℝ))
      = (fun θ : ZMod (arithQ ρ (max l₁ l₂)) =>
        ∑ α ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁,
          fourier (T := 1) (-(θ.val : ℤ)) α *
            winConvR (mStarF (uScale ρ (lcL l₁ l₂ k₁ k₂)))
              (winModR (-α) (mdlSliceF ρ C₀ a l₁ l₂ k₁ k₂ j₁ t f n)) x) := by
    funext θ
    exact Finset.sum_congr rfl (fun α hα => by rw [hW₁ α hα])
  have hR : (fun θ : ZMod (arithQ ρ (max l₁ l₂)) =>
        ∑ β ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂,
          fourier (T := 1) (-(θ.val : ℤ)) β * W₂ β (x : ℝ))
      = (fun θ : ZMod (arithQ ρ (max l₁ l₂)) =>
        ∑ β ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂,
          fourier (T := 1) (-(θ.val : ℤ)) β *
            winConvR (mStargF P.natDegree (uScale ρ (lcL l₁ l₂ k₁ k₂)))
              (winModR (-β) (mdlSliceG ρ P C₀ a l₁ l₂ k₁ k₂ j₂ t g n)) x) := by
    funext θ
    exact Finset.sum_congr rfl (fun β hβ => by rw [hW₂ β hβ])
  rw [hL, hR, zmodAvgWindowPacketsNegReflect ρ hρ hρ1 P l₁ l₂ _ _ _ _ x
    (hsum₁ x) (hsum₂ x)]
  rw [Work.KMTPlan.A6.mdlSliceJ_eq_Btwist]
  simp only [lcL]

/-- The residue `x % Q` and the integer `x` have the same image in `ZMod Q`. -/
theorem intCast_emod_eq (Q : ℕ) (x : ℤ) :
    (((x % (Q : ℤ) : ℤ)) : ZMod Q) = ((x : ℤ) : ZMod Q) := by
  have h : (x % (Q : ℤ)) + (x / (Q : ℤ)) * (Q : ℤ) = x := by
    have h0 := Int.emod_add_mul_ediv x (Q : ℤ)
    rw [mul_comm] at h0
    exact h0
  rw [← h]
  push_cast
  rw [ZMod.natCast_self]

/-- **The gated diagonal identity** (the shape of clause (2) of `AdelicPacketsProp`): with the
packets switched off off the good scales, the `zmodAvg` at the diagonal is the good-scaled slice. -/
theorem zmodAvg_gated_packets_eq_slice (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (P : ℤ[X]) (C₀ : ℕ)
    (a : ℕ → NNReal) (f g : ℤ → ℂ) (l₁ l₂ k₁ k₂ : ℕ) (j₁ j₂ : ℤ) (t : ℝ) (n : ℕ) (x : ℤ)
    (hj₁ : j₁ ∈ ({-1, 0, 1} : Finset ℤ)) (hj₂ : j₂ ∈ ({-1, 0, 1} : Finset ℤ))
    (hk₁ : k₁ = 0 → j₁ ≠ -1) (hk₂ : k₂ = 0 → j₂ ≠ -1)
    (W₁ W₂ : Circ → ℝ → ℂ)
    (hW₁ : ∀ α ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁,
      W₁ α (x : ℝ) = winConvR (mStarF (uScale ρ (lcL l₁ l₂ k₁ k₂)))
        (winModR (-α) (mdlSliceF ρ C₀ a l₁ l₂ k₁ k₂ j₁ t f n)) x)
    (hW₂ : ∀ β ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂,
      W₂ β (x : ℝ) = winConvR (mStargF P.natDegree (uScale ρ (lcL l₁ l₂ k₁ k₂)))
        (winModR (-β) (mdlSliceG ρ P C₀ a l₁ l₂ k₁ k₂ j₂ t g n)) x)
    (hsum₁ : ∀ z : ℤ, Summable (fun j : ℤ =>
      cw (mStarF (uScale ρ (lcL l₁ l₂ k₁ k₂))) j *
        mdlSliceF ρ C₀ a l₁ l₂ k₁ k₂ j₁ t f n (z - j)))
    (hsum₂ : ∀ z : ℤ, Summable (fun j : ℤ =>
      cw (mStargF P.natDegree (uScale ρ (lcL l₁ l₂ k₁ k₂))) j *
        mdlSliceG ρ P C₀ a l₁ l₂ k₁ k₂ j₂ t g n (z - j))) :
    Work.KMTPlan.A6.zmodAvg (Work.KMTPlan.A6.negReflect P) (arithQ ρ (max l₁ l₂))
      (fun θ : ZMod (arithQ ρ (max l₁ l₂)) =>
        if goodScale (arithQ ρ (max l₁ l₂)) (lcL l₁ l₂ k₁ k₂) (Nat.floor (a n)) then
          ∑ α ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁,
            fourier (T := 1) (-(θ.val : ℤ)) α * W₁ α (x : ℝ) else 0)
      (fun θ : ZMod (arithQ ρ (max l₁ l₂)) =>
        if goodScale (arithQ ρ (max l₁ l₂)) (lcL l₁ l₂ k₁ k₂) (Nat.floor (a n)) then
          ∑ β ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂,
            fourier (T := 1) (-(θ.val : ℤ)) β * W₂ β (x : ℝ) else 0)
      ((x : ℤ) : ZMod (arithQ ρ (max l₁ l₂)))
    = (if goodScale (arithQ ρ (max l₁ l₂)) (lcL l₁ l₂ k₁ k₂) (Nat.floor (a n)) then
        mdlSliceJ ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ t n x else 0) := by
  by_cases hg : goodScale (arithQ ρ (max l₁ l₂)) (lcL l₁ l₂ k₁ k₂) (Nat.floor (a n))
  · simp only [hg, if_true]
    exact zmodAvg_packets_eq_slice ρ hρ hρ1 P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ t n x
      hj₁ hj₂ hk₁ hk₂ W₁ W₂ hW₁ hW₂ hsum₁ hsum₂
  · simp only [hg, if_false]
    simp [Work.KMTPlan.A6.zmodAvg]

/-- **The `Q`-periodicity of the packet `zmodAvg`** (clause (3) of `AdelicPacketsProp`). -/
theorem zmodAvg_packet_periodic (P : ℤ[X]) (Q : ℕ) (u v : ZMod Q → ℂ) (ρ' : ℤ) :
    Work.KMTPlan.A6.zmodAvg (Work.KMTPlan.A6.negReflect P) Q u v
        (((ρ' + (Q : ℤ)) : ℤ) : ZMod Q)
      = Work.KMTPlan.A6.zmodAvg (Work.KMTPlan.A6.negReflect P) Q u v ((ρ' : ℤ) : ZMod Q) := by
  have h : (((ρ' + (Q : ℤ)) : ℤ) : ZMod Q) = ((ρ' : ℤ) : ZMod Q) := by
    push_cast
    rw [ZMod.natCast_self]
    ring
  rw [h]

/-- **The measurability of a packet profile** (clause (9) of `AdelicPacketsProp`): a finite
character combination of measurable amplitudes is `AEMeasurable` in `X`. -/
theorem aemeasurable_packetProfile (ρ : ℝ) (C₀ : ℕ) (a : ℕ → NNReal) (L₁ L₂ k₁ k₂ : ℕ) (l : ℕ)
    (W : Circ → ℝ → ℂ) (hW : ∀ α, Measurable (W α)) (n : ℕ)
    (θ : ZMod (arithQ ρ (max L₁ L₂))) :
    AEMeasurable (fun X : ℝ =>
      if goodScale (arithQ ρ (max L₁ L₂)) (lcL L₁ L₂ k₁ k₂) (Nat.floor (a n)) then
        ∑ α ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l,
          fourier (T := 1) (-(θ.val : ℤ)) α * W α X
      else 0) := by
  by_cases hg : goodScale (arithQ ρ (max L₁ L₂)) (lcL L₁ L₂ k₁ k₂) (Nat.floor (a n))
  · simp only [hg, if_true]
    refine (Finset.measurable_sum _ (fun α _ => ?_)).aemeasurable
    exact (hW α).const_mul _
  · simp only [hg, if_false]
    exact aemeasurable_const

/-- The zero function is band limited (with any band). -/
theorem hasRealFreqSupport_zero (S : Set ℝ) :
    Work.KMTAreas.A7Rep.HasRealFreqSupport (fun _ : ℝ => (0 : ℂ)) S :=
  ⟨0, MeasureTheory.integrable_zero ℝ ℂ volume, fun ξ _ => rfl, fun t => by
    rw [Real.fourierInv_eq']
    simp⟩

/-- **The gated packet profile is band limited** (clause (1)'s core): a finite character combination
of amplitudes each band limited to `Icc (-δ) δ`, gated by `goodScale`, is band limited to
`Icc (-δ) δ`.  `l` is the height of the arithmetic frequencies entering the profile. -/
theorem hasRealFreqSupport_gatedProfile (ρ : ℝ) (C₀ : ℕ) (a : ℕ → NNReal) (L₁ L₂ k₁ k₂ : ℕ)
    (l : ℕ) (W : Circ → ℝ → ℂ) {δ : ℝ}
    (hW : ∀ α, Work.KMTAreas.A7Rep.HasRealFreqSupport (W α) (Set.Icc (-δ) δ))
    (n : ℕ) (θ : ZMod (arithQ ρ (max L₁ L₂))) :
    Work.KMTAreas.A7Rep.HasRealFreqSupport (fun X : ℝ =>
      if goodScale (arithQ ρ (max L₁ L₂)) (lcL L₁ L₂ k₁ k₂) (Nat.floor (a n)) then
        ∑ α ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l,
          fourier (T := 1) (-(θ.val : ℤ)) α * W α X else 0)
      (Set.Icc (-δ) δ) := by
  by_cases hg : goodScale (arithQ ρ (max L₁ L₂)) (lcL L₁ L₂ k₁ k₂) (Nat.floor (a n))
  · simp only [hg, if_true]
    exact Work.KMTPlan.A6.hasRealFreqSupport_finset_sum
      (s := Work.Analysis.IonescuWainger.iwArithFreqs ρ l)
      (c := fun α => fourier (T := 1) (-(θ.val : ℤ)) α)
      (ψ := fun α => W α)
      (fun α _ => hW α)
  · simp only [hg, if_false]
    exact hasRealFreqSupport_zero _

/-- **The band of the packet `zmodAvg`** (clause (1) of `AdelicPacketsProp`): if the two packet
families are band limited to `Icc (-βu) βu` resp. `Icc (-βv) βv`, slice by slice, with
`βu + βv ≤ β`, then the `zmodAvg`-lift of them is band limited to `Icc (-β) β`. -/
theorem hasRealFreqSupport_zmodAvg_packets (P : ℤ[X]) (Q : ℕ) (u v : ZMod Q → ℝ → ℂ)
    {βu βv β : ℝ}
    (hu : ∀ θ : ZMod Q, Work.KMTAreas.A7Rep.HasRealFreqSupport (u θ) (Set.Icc (-βu) βu))
    (hv : ∀ θ : ZMod Q, Work.KMTAreas.A7Rep.HasRealFreqSupport (v θ) (Set.Icc (-βv) βv))
    (hβ : βu + βv ≤ β) (ρ' : ZMod Q) :
    Work.KMTAreas.A7Rep.HasRealFreqSupport
      (fun X : ℝ => Work.KMTPlan.A6.zmodAvg (Work.KMTPlan.A6.negReflect P) Q
        (fun θ => u θ X) (fun θ => v θ X) ρ')
      (Set.Icc (-β) β) := by
  have hterm : ∀ y ∈ Finset.range Q,
      Work.KMTAreas.A7Rep.HasRealFreqSupport
        (fun X : ℝ => u (ρ' + (y : ZMod Q)) X *
          v (ρ' + (((Work.KMTPlan.A6.negReflect P).eval (y : ℤ) : ℤ) : ZMod Q)) X)
        (Set.Icc (-β) β) := by
    intro y hy
    refine Work.KMTPlan.A6.hasRealFreqSupport_mul (hu _) (hv _) ?_
    intro η hη ζ hζ
    simp only [Set.mem_Icc] at hη hζ ⊢
    constructor <;> linarith [hη.1, hη.2, hζ.1, hζ.2, hβ]
  have hsum := Work.KMTPlan.A6.hasRealFreqSupport_finset_sum (Finset.range Q)
    (fun _ => (1 : ℂ)) hterm
  have hfin := Work.KMTPlan.A6.hasRealFreqSupport_const_mul ((Q : ℂ)⁻¹)
    (S := Set.Icc (-β) β) (ψ := fun X : ℝ => ∑ y ∈ Finset.range Q, 1 *
      (u (ρ' + (y : ZMod Q)) X *
        v (ρ' + (((Work.KMTPlan.A6.negReflect P).eval (y : ℤ) : ℤ) : ZMod Q)) X)) hsum
  convert hfin using 3 with X
  rw [Work.KMTPlan.A6.zmodAvg]
  simp only [one_mul]

end Work.KMTPlan.A6Clean
