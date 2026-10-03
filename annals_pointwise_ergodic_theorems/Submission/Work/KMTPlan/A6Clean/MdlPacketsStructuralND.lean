/-
# The structural clauses of the §8 adelic form, with **scale-dependent** packet bands

`A6Clean/AdelicPacketsAssembly.lean` (`adelicPackets_of_windowPieceLifts`) and
`A6Clean/AdelicPacketFam.lean` (`packets_structuralClauses`) assemble clauses (1), (2), (3), (9),
(10) of the adelic form from lift families whose bands `β₁`, `β₂` are *fixed* with `β₁ + β₂ ≤ β`.

That uniformity is **not** available: the `f`-side packet at scale `n` has band `γ₁ n` and the
`g`-side packet has band `γ₂ n`, and what the data give
(`Work.KMTPlan.A6.goodScale_two_pow_bands_le`) is the *inequality*

  `γ₁ n + γ₂ n ≤ 1/(8Q)`,   `Q = arithQ ρ (max l₁ l₂)`,

n-uniformly, but with `γᵢ n` genuinely depending on `n` (`γ₁ n = 2^{k₁ - logN ⌊a n⌋}`).  Taking
`β₁ = β₂ = 1/(16Q)` is impossible (see `NOTES_MdlWindowLift_CORRECTED_BAND.md`).  This file
therefore redoes the (mechanical) assembly with `n`-dependent bands, using the *proved*
`Work.KMTPlan.A6Clean.hasRealFreqSupport_zmodAvg_packets` (which is already stated slice by slice,
hence also applies with `n`-dependent bands) and a `n`-indexed copy of
`hasRealFreqSupport_gatedProfile`.
-/
import Mathlib
import Submission.Work.KMTPlan.A6Clean.AdelicPacketFam

-- v4.35 port: restore the v4.34 instance-unification behaviour (respectTransparency) in this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.KMTPlan.A6Clean

open MeasureTheory Polynomial Finset
open scoped BigOperators ENNReal NNReal
open Work.KMTAreas.A7
open Work.KMTPlan.A6

local notation "Circ" => Work.Analysis.IonescuWainger.Circle

/-- **The gated packet profile is band limited, with the band indexed by the scale.**  The
`n`-indexed version of `hasRealFreqSupport_gatedProfile`. -/
theorem hasRealFreqSupport_gatedProfile_nd (ρ : ℝ) (C₀ : ℕ) (a : ℕ → NNReal)
    (L₁ L₂ k₁ k₂ l : ℕ) (W : ℕ → Circ → ℝ → ℂ) {δ : ℕ → ℝ}
    (hW : ∀ (n : ℕ) (α : Circ),
      Work.KMTAreas.A7Rep.HasRealFreqSupport (W n α) (Set.Icc (-(δ n)) (δ n)))
    (n : ℕ) (θ : ZMod (arithQ ρ (max L₁ L₂))) :
    Work.KMTAreas.A7Rep.HasRealFreqSupport (fun X : ℝ =>
      if goodScale (arithQ ρ (max L₁ L₂)) (lcL L₁ L₂ k₁ k₂) (Nat.floor (a n)) then
        ∑ α ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l,
          fourier (T := 1) (-(θ.val : ℤ)) α * W n α X else 0)
      (Set.Icc (-(δ n)) (δ n)) := by
  by_cases hg : goodScale (arithQ ρ (max L₁ L₂)) (lcL L₁ L₂ k₁ k₂) (Nat.floor (a n))
  · simp only [hg, if_true]
    exact Work.KMTPlan.A6.hasRealFreqSupport_finset_sum
      (s := Work.Analysis.IonescuWainger.iwArithFreqs ρ l)
      (c := fun α => fourier (T := 1) (-(θ.val : ℤ)) α)
      (ψ := fun α => W n α)
      (fun α _ => hW n α)
  · simp only [hg, if_false]
    exact hasRealFreqSupport_zero _

/-- **The measurability of the gated packet profile** (`n`-indexed version of
`aemeasurable_packetProfile`). -/
theorem aemeasurable_packetProfile_nd (ρ : ℝ) (C₀ : ℕ) (a : ℕ → NNReal)
    (L₁ L₂ k₁ k₂ l : ℕ) (W : ℕ → Circ → ℝ → ℂ)
    (hW : ∀ (n : ℕ) (α : Circ), Measurable (W n α))
    (n : ℕ) (θ : ZMod (arithQ ρ (max L₁ L₂))) :
    AEMeasurable (fun X : ℝ =>
      if goodScale (arithQ ρ (max L₁ L₂)) (lcL L₁ L₂ k₁ k₂) (Nat.floor (a n)) then
        ∑ α ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l,
          fourier (T := 1) (-(θ.val : ℤ)) α * W n α X else 0) volume := by
  by_cases hg : goodScale (arithQ ρ (max L₁ L₂)) (lcL L₁ L₂ k₁ k₂) (Nat.floor (a n))
  · simp only [hg, if_true]
    exact (Finset.measurable_sum _ (fun α _ => measurable_const.mul (hW n α))).aemeasurable
  · simp only [hg, if_false]
    exact aemeasurable_const

/-- **Clauses (1), (2), (3), (9), (10) of the §8 adelic form, with scale-dependent packet
bands.**  The packets are the gated character combinations of the lift families `W₁ n`, `W₂ n`, the
lift `F` is their `zmodAvg`, so the presentation clause holds for every `X`, `ρ'`. -/
theorem packets_structuralClauses_nd (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (P : Polynomial ℤ)
    (C₀ : ℕ) (a : ℕ → NNReal) (f g : ℤ → ℂ) (l₁ l₂ k₁ k₂ : ℕ) (j₁ j₂ : ℤ) (t : ℝ)
    (hj₁ : j₁ ∈ ({-1, 0, 1} : Finset ℤ)) (hj₂ : j₂ ∈ ({-1, 0, 1} : Finset ℤ))
    (hk₁ : k₁ = 0 → j₁ ≠ -1) (hk₂ : k₂ = 0 → j₂ ≠ -1)
    (W₁ W₂ : ℕ → Circ → ℝ → ℂ) (δ₁ δ₂ : ℕ → ℝ) (β : ℝ)
    (hβ : ∀ n, δ₁ n + δ₂ n ≤ β)
    (hW₁b : ∀ (n : ℕ) (α : Circ),
      Work.KMTAreas.A7Rep.HasRealFreqSupport (W₁ n α) (Set.Icc (-(δ₁ n)) (δ₁ n)))
    (hW₂b : ∀ (n : ℕ) (α : Circ),
      Work.KMTAreas.A7Rep.HasRealFreqSupport (W₂ n α) (Set.Icc (-(δ₂ n)) (δ₂ n)))
    (hW₁c : ∀ (n : ℕ) (α : Circ), Measurable (W₁ n α))
    (hW₂c : ∀ (n : ℕ) (α : Circ), Measurable (W₂ n α))
    (hW₁s : ∀ (n : ℕ) (α : Circ),
      α ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁ → ∀ x : ℤ,
        W₁ n α (x : ℝ) = winConvR (mStarF (uScale ρ (lcL l₁ l₂ k₁ k₂)))
          (winModR (-α) (mdlSliceF ρ C₀ a l₁ l₂ k₁ k₂ j₁ t f n)) x)
    (hW₂s : ∀ (n : ℕ) (β₂ : Circ),
      β₂ ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂ → ∀ x : ℤ,
        W₂ n β₂ (x : ℝ) = winConvR (mStargF P.natDegree (uScale ρ (lcL l₁ l₂ k₁ k₂)))
          (winModR (-β₂) (mdlSliceG ρ P C₀ a l₁ l₂ k₁ k₂ j₂ t g n)) x)
    (hsum₁ : ∀ (n : ℕ) (z : ℤ), Summable (fun j : ℤ =>
      cw (mStarF (uScale ρ (lcL l₁ l₂ k₁ k₂))) j *
        mdlSliceF ρ C₀ a l₁ l₂ k₁ k₂ j₁ t f n (z - j)))
    (hsum₂ : ∀ (n : ℕ) (z : ℤ), Summable (fun j : ℤ =>
      cw (mStargF P.natDegree (uScale ρ (lcL l₁ l₂ k₁ k₂))) j *
        mdlSliceG ρ P C₀ a l₁ l₂ k₁ k₂ j₂ t g n (z - j))) :
    ∃ (F : ℕ → ℝ → ℤ → ℂ) (u v : ℕ → ℝ → ZMod (arithQ ρ (max l₁ l₂)) → ℂ),
      (∀ (n : ℕ) (ρ' : ℤ), Work.KMTAreas.A7Rep.HasRealFreqSupport (fun X : ℝ => F n X ρ')
        (Set.Icc (-β) β)) ∧
      (∀ (n : ℕ) (x : ℤ), F n (x : ℝ) (x % ((arithQ ρ (max l₁ l₂) : ℕ) : ℤ))
        = (if goodScale (arithQ ρ (max l₁ l₂)) (lcL l₁ l₂ k₁ k₂) (Nat.floor (a n)) then
            mdlSliceJ ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ t n x else 0)) ∧
      (∀ (n : ℕ) (X : ℝ) (ρ' : ℤ), F n X ρ'
        = zmodAvg (negReflect P) (arithQ ρ (max l₁ l₂)) (u n X) (v n X)
            ((ρ' : ℤ) : ZMod (arithQ ρ (max l₁ l₂)))) ∧
      (∀ (n : ℕ) (θ : ZMod (arithQ ρ (max l₁ l₂))), AEMeasurable (fun X : ℝ => u n X θ)) ∧
      (∀ (n : ℕ) (θ : ZMod (arithQ ρ (max l₁ l₂))), AEMeasurable (fun X : ℝ => v n X θ)) := by
  classical
  set Q : ℕ := arithQ ρ (max l₁ l₂) with hQdef
  set U : ℕ := uScale ρ (lcL l₁ l₂ k₁ k₂) with hUdef
  let u : ℕ → ℝ → ZMod Q → ℂ := fun n X θ =>
    if goodScale (arithQ ρ (max l₁ l₂)) (lcL l₁ l₂ k₁ k₂) (Nat.floor (a n)) then
      ∑ α ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁,
        fourier (T := 1) (-(θ.val : ℤ)) α * W₁ n α X else 0
  let v : ℕ → ℝ → ZMod Q → ℂ := fun n X θ =>
    if goodScale (arithQ ρ (max l₁ l₂)) (lcL l₁ l₂ k₁ k₂) (Nat.floor (a n)) then
      ∑ β ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂,
        fourier (T := 1) (-(θ.val : ℤ)) β * W₂ n β X else 0
  refine ⟨fun n X ρ' => zmodAvg (negReflect P) Q (u n X) (v n X) (((ρ' : ℤ)) : ZMod Q),
    u, v, ?_, ?_, ?_, ?_, ?_⟩
  · intro n ρ'
    have hb₁ : ∀ θ : ZMod Q, Work.KMTAreas.A7Rep.HasRealFreqSupport (fun X : ℝ => u n X θ)
        (Set.Icc (-(δ₁ n)) (δ₁ n)) :=
      fun θ => hasRealFreqSupport_gatedProfile_nd ρ C₀ a l₁ l₂ k₁ k₂ l₁ W₁ hW₁b n θ
    have hb₂ : ∀ θ : ZMod Q, Work.KMTAreas.A7Rep.HasRealFreqSupport (fun X : ℝ => v n X θ)
        (Set.Icc (-(δ₂ n)) (δ₂ n)) :=
      fun θ => hasRealFreqSupport_gatedProfile_nd ρ C₀ a l₁ l₂ k₁ k₂ l₂ W₂ hW₂b n θ
    exact Work.KMTPlan.A6Clean.hasRealFreqSupport_zmodAvg_packets P Q (fun θ X => u n X θ)
      (fun θ X => v n X θ) hb₁ hb₂ (hβ n) ρ'
  · intro n x
    have hsm₁ : ∀ z : ℤ, Summable (fun j : ℤ =>
        cw (mStarF (uScale ρ (lcL l₁ l₂ k₁ k₂))) j *
          mdlSliceF ρ C₀ a l₁ l₂ k₁ k₂ j₁ t f n (z - j)) := hsum₁ n
    have hsm₂ : ∀ z : ℤ, Summable (fun j : ℤ =>
        cw (mStargF P.natDegree (uScale ρ (lcL l₁ l₂ k₁ k₂))) j *
          mdlSliceG ρ P C₀ a l₁ l₂ k₁ k₂ j₂ t g n (z - j)) := hsum₂ n
    have h := zmodAvg_gated_packets_eq_slice ρ hρ hρ1 P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ t n x
      hj₁ hj₂ hk₁ hk₂ (W₁ n) (W₂ n)
      (fun α hα => hW₁s n α hα x) (fun β hβ' => hW₂s n β hβ' x) hsm₁ hsm₂
    simpa only [intCast_emod_eq] using h
  · intro n X ρ'
    rfl
  · intro n θ
    exact (aemeasurable_packetProfile_nd ρ C₀ a l₁ l₂ k₁ k₂ l₁ W₁ hW₁c n θ)
  · intro n θ
    exact (aemeasurable_packetProfile_nd ρ C₀ a l₁ l₂ k₁ k₂ l₂ W₂ hW₂c n θ)

end Work.KMTPlan.A6Clean
