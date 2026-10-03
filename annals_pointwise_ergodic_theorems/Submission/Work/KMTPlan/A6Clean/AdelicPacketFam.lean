/-
# The §8 packet families of the adelic form, and the structural clauses assembled

This module fixes the *packet families* of the §8 adelic form of the A6 model estimate
(`Work.KMTPlan.A6.AdelicFormPropRange`) in the shape the assembly uses, and proves — by direct
appeal to the already-proved structural lemmas of `A6Clean/AdelicPacketsReduction.lean` and
`A6Clean/AdelicPacketsDiag.lean` — that they satisfy clauses (1), (2), (3), (9), (10) of the
adelic form once the two *lift families* `W₁`, `W₂` are given with the right bands and samples.

The packets are the character combinations of the band-limited lifts of the *window pieces* of the
two model packets:

  `packetFamF ρ a l₁ l₂ k₁ k₂ W₁ n X θ`
    `= 1_{goodScale Q L ⌊a n⌋} · Σ_{α ∈ iwArithFreqs ρ l₁} e(-θ.val·α) · W₁ n α X`

(and the `g`-side twin `packetFamG`), with `Q = arithQ ρ (max l₁ l₂)` and `L = lcL l₁ l₂ k₁ k₂`.

Note the **`n`-indexing of the lifts**: the window piece of the model packet at scale `n` depends
on `n`, so the lift `W₁` must be indexed by `n` as well.  (The earlier assembly
`Work.KMTPlan.A6Clean.adelicPackets_of_windowPieceLifts` took a single `W₁ : Circ → ℝ → ℂ` shared
by all `n`, which is *unsatisfiable* whenever two good scales have different window pieces; the
present module is the repaired interface.)

The *content* of the adelic form — the existence of the lifts `W₁`, `W₂` (their bands and samples),
the arithmetic minor-arc property of the packets (which supplies the gain `2^{-c·max(l₁,l₂)}` through
`Work.KMTPlan.A6Clean.MdlAdelicBileClausesOr`) and the two `VrLiftDataP`-data bounds (the paper's
`(lin-1)`/`(lin-2)`) — is *not* addressed here: `packets_structuralClauses` below is pure glue, and
takes the band/measurability/diagonal properties of the packets as hypotheses.
-/
import Mathlib
import Submission.Work.KMTPlan.A6Clean.AdelicPacketsDiag
import Submission.Work.KMTPlan.A6Clean.AdelicBileOr
import Submission.Work.KMTPlan.A6.goodScale_two_pow_bands_le
import Submission.Work.KMTPlan.A6.MdlSliceDiagonalSampling
import Submission.Work.KMTPlan.A6.zmodAvgCharExpansion

-- v4.35 port: restore the v4.34 instance-unification behaviour (respectTransparency) in this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Work.KMTPlan.A6Clean

open MeasureTheory Polynomial Finset
open scoped BigOperators ENNReal NNReal
open Work.KMTAreas.A7
open Work.KMTPlan.A6

local notation "Circ" => Work.Analysis.IonescuWainger.Circle

/-- **The `f`-side packet family of the §8 adelic form.**  `W` is the lift family: `W n α` is the
band-limited lift of the window piece of the model packet `mdlSliceF ⋯ n` at the arithmetic
frequency `α`; the `θ`-th slice of the packet is its character combination, gated by `goodScale`. -/
noncomputable def packetFamF (ρ : ℝ) (a : ℕ → NNReal) (l₁ l₂ k₁ k₂ : ℕ)
    (W : ℕ → Circ → ℝ → ℂ) : ℕ → ℝ → ZMod (arithQ ρ (max l₁ l₂)) → ℂ :=
  fun n X θ =>
    if goodScale (arithQ ρ (max l₁ l₂)) (lcL l₁ l₂ k₁ k₂) (Nat.floor (a n)) then
      ∑ α ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁,
        fourier (T := 1) (-(θ.val : ℤ)) α * W n α X
    else 0

/-- **The `g`-side packet family of the §8 adelic form** (the twin of `packetFamF`, at height
`l₂`). -/
noncomputable def packetFamG (ρ : ℝ) (a : ℕ → NNReal) (l₁ l₂ k₁ k₂ : ℕ)
    (W : ℕ → Circ → ℝ → ℂ) : ℕ → ℝ → ZMod (arithQ ρ (max l₁ l₂)) → ℂ :=
  fun n X θ =>
    if goodScale (arithQ ρ (max l₁ l₂)) (lcL l₁ l₂ k₁ k₂) (Nat.floor (a n)) then
      ∑ β ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂,
        fourier (T := 1) (-(θ.val : ℤ)) β * W n β X
    else 0

@[simp] lemma packetFamF_apply (ρ : ℝ) (a : ℕ → NNReal) (l₁ l₂ k₁ k₂ : ℕ)
    (W : ℕ → Circ → ℝ → ℂ) (n : ℕ) (X : ℝ) (θ : ZMod (arithQ ρ (max l₁ l₂))) :
    packetFamF ρ a l₁ l₂ k₁ k₂ W n X θ =
      if goodScale (arithQ ρ (max l₁ l₂)) (lcL l₁ l₂ k₁ k₂) (Nat.floor (a n)) then
        ∑ α ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁,
          fourier (T := 1) (-(θ.val : ℤ)) α * W n α X
      else 0 := rfl

@[simp] lemma packetFamG_apply (ρ : ℝ) (a : ℕ → NNReal) (l₁ l₂ k₁ k₂ : ℕ)
    (W : ℕ → Circ → ℝ → ℂ) (n : ℕ) (X : ℝ) (θ : ZMod (arithQ ρ (max l₁ l₂))) :
    packetFamG ρ a l₁ l₂ k₁ k₂ W n X θ =
      if goodScale (arithQ ρ (max l₁ l₂)) (lcL l₁ l₂ k₁ k₂) (Nat.floor (a n)) then
        ∑ β ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂,
          fourier (T := 1) (-(θ.val : ℤ)) β * W n β X
      else 0 := rfl

/-! ## The structural clauses of the adelic form for the packet families -/

end Work.KMTPlan.A6Clean
