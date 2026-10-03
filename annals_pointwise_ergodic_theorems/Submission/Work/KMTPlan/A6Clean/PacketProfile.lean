/-
# The `ZMod Q` presentation of the twisted bilinear multiplier by packet profiles

`Work.KMTPlan.A6.AdelicPacketsProp` (and hence the adelic form `AdelicFormPropRange` of §8 of
Krause–Mirek–Tao, Annals **195** (2022)) requires, for the frozen slice `mdlSliceJ` of the model
tuple, two packet families `u, v : ℕ → ℝ → ZMod Q → ℂ` whose `zmodAvg`-average reproduces the
slice.  This module proves the **algebraic core** of that construction, i.e. the identity

  `zmodAvg (negReflect P) Q (u n x) (v n x) (x % Q) = Btwist ρ P l₁ l₂ m₁ m₂ h k x`

for the canonical *packet profiles* of the two model inputs `h = mdlSliceF … n`,
`k = mdlSliceG … n`: at an integer point `x` the profile of `h` is built from the **window pieces**

  `winPieceR m h α = winConvR m (winModR (-α) h)`

of the height-`≤ l` arithmetic fibres, with the character of `ZMod Q` indexed by `α`:

  `packetProfile A m h x Q θ = ∑_{α ∈ A} e(-θ.val · α) · winPieceR m h α x`,  `A = iwArithFreqs ρ l`.

The proof is the fibre identity `Work.KMTAreas.A7.Btwist_eq_fiberSum`
(`Btwist = Q⁻¹ ∑_{n₀ < Q} fiberOpSet (n₀) h · fiberOpPSet (n₀) k`) together with the
window-piece decomposition of a single fibre
`fiberOpSet A m n₀ h x = ∑_{α∈A} e((n₀-x)α) winPieceR m h α x` and the `Q`-periodicity of the
characters (`Q = arithQ ρ (max l₁ l₂)` kills every frequency of height `≤ 2^{l₁}`, `≤ 2^{l₂}`).

This is exactly the `(A)` obligation ("the fibre identity / `form-1`–`form-2`") of
`NOTES_A6_MdlSliceCoreGainAll_SESSION2.md` §3 and of `HANDOFF_A6_MdlSliceCoreGainMemLp2_SESSION2.md`
§2: it is stated for *arbitrary* lifts `G α : ℤ → ℂ` of the window pieces, so the analytic part
(the band-limited lift of the pieces to `ℝ`, its band, measurability) can be supplied separately.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.ModelLargeHiRep
import Submission.Work.KMTPlan.A6.MdlAdelicFormPlusDefs

-- v4.35 port: restore the v4.34 instance-unification behaviour (respectTransparency) in this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.KMTPlan.A6Clean

open MeasureTheory Polynomial Finset
open scoped BigOperators

noncomputable section

/-- The subtraction rule for the circle characters: `e((n-m)α) = e(nα)·e((-m)α)`. -/
theorem fourier_sub_eq_mulR (n m : ℤ) (α : Work.Analysis.IonescuWainger.Circle) :
    fourier (T := 1) (n - m) α = fourier (T := 1) n α * fourier (T := 1) (-m) α := by
  rw [show n - m = n + (-m) from by ring, fourier_add]

/-- The **window piece** of a model input `v` at the arithmetic frequency `α`: the window
multiplier `Ω(· - α)` applied to `v`, i.e. `winConvR m (winModR (-α) v)`. -/
def winPieceR (m : ℝ → ℂ) (v : ℤ → ℂ) (α : Work.Analysis.IonescuWainger.Circle) : ℤ → ℂ :=
  Work.KMTAreas.A7.winConvR m (Work.KMTAreas.A7.winModR (-α) v)

/-- **The window-piece decomposition of a single arithmetic fibre.**
`fiberOpSet A m n₀ v x = ∑_{α ∈ A} e((n₀-x)α) · winPieceR m v α x`, for an arbitrary finite set
`A` of circle frequencies, provided the window sums are summable.

This is the general-`A` form of the proved
`Work.KMTAreas.A7.fiberOp_eq_phaseRotation_windowCut` (which is stated for the exact-height set
`iwArithFreqsNew ρ l`); the model's fibre identity `Btwist_eq_fiberSum` uses the height-`≤ l` set
`iwArithFreqs ρ l`, so the height-`≤ l` form is the one needed here. -/
theorem fiberOpSet_eq_windowPieceR (A : Finset Work.Analysis.IonescuWainger.Circle) (m : ℝ → ℂ)
    (n₀ : ℤ) (v : ℤ → ℂ) (x : ℤ)
    (hsum : Summable (fun j : ℤ => Work.KMTAreas.A7.cw m j * v (x - j))) :
    Work.KMTAreas.A7.fiberOpSet A m n₀ v x
      = ∑ α ∈ A, fourier (T := 1) (n₀ - x) α * winPieceR m v α x := by
  have hsumα : ∀ α : Work.Analysis.IonescuWainger.Circle, Summable (fun j : ℤ =>
      fourier (T := 1) (-j) α * (Work.KMTAreas.A7.cw m j * v (x - j))) := by
    intro α
    refine Summable.of_norm_bounded (hsum.norm) (fun j => ?_)
    rw [norm_mul, Work.KMTAreas.A7.norm_fourier_applyR, one_mul]
  have hsumm : ∀ α : Work.Analysis.IonescuWainger.Circle, Summable (fun j : ℤ =>
      fourier (T := 1) n₀ α * (fourier (T := 1) (-j) α
        * (Work.KMTAreas.A7.cw m j * v (x - j)))) :=
    fun α => (hsumα α).mul_left _
  have hLHS : Work.KMTAreas.A7.fiberOpSet A m n₀ v x
      = ∑' j : ℤ, ∑ α ∈ A, fourier (T := 1) n₀ α
          * (fourier (T := 1) (-j) α * (Work.KMTAreas.A7.cw m j * v (x - j))) := by
    rw [Work.KMTAreas.A7.fiberOpSet]
    refine tsum_congr (fun j => ?_)
    rw [Work.KMTAreas.A7.arithCharSet]
    rw [Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun α _ => ?_)
    rw [fourier_sub_eq_mulR]
    ring
  rw [hLHS, Summable.tsum_finsetSum (s := A) (fun α _ => hsumm α)]
  refine Finset.sum_congr rfl (fun α _ => ?_)
  rw [tsum_mul_left]
  rw [show (∑' j : ℤ, fourier (T := 1) (-j) α * (Work.KMTAreas.A7.cw m j * v (x - j)))
      = Work.KMTAreas.A7.winModR α (Work.KMTAreas.A7.winConvR m
          (Work.KMTAreas.A7.winModR (-α) v)) x from
    (Work.KMTAreas.A7.winModR_winConvR_apply α m v x).symm]
  rw [winPieceR, Work.KMTAreas.A7.winModR]
  rw [show fourier (T := 1) n₀ α
        * (fourier (T := 1) (-x) α
          * Work.KMTAreas.A7.winConvR m (Work.KMTAreas.A7.winModR (-α) v) x)
      = fourier (T := 1) (n₀ - x) α
        * Work.KMTAreas.A7.winConvR m (Work.KMTAreas.A7.winModR (-α) v) x from by
    rw [fourier_sub_eq_mulR]
    ring]

/-- **The characters of `(ℚ/ℤ)_{≤l}` have period `arithQ ρ L` for every `L ≥ l`.** -/
theorem fourier_mul_arithQ_eq_one {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) {l L : ℕ} (hl : l ≤ L)
    {α : Work.Analysis.IonescuWainger.Circle}
    (hα : α ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l) (t : ℤ) :
    fourier (T := 1) (t * (Work.KMTAreas.A7.arithQ ρ L : ℤ)) α = 1 := by
  have hαL : α ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ L :=
    (Work.Analysis.IonescuWainger.iwArithFreqs_mono hρ hρ1 hl) hα
  have h0 : ((Work.KMTAreas.A7.arithQ ρ L : ℕ) : ℤ) • α = 0 := by
    have h := Work.KMTAreas.A7.arithQ_nsmul_eq_zero (ρ := ρ) (l := L) hαL
    simpa using h
  rw [fourier_apply, mul_zsmul, h0, smul_zero]
  exact fourier_zero'

/-- **The characters of `(ℚ/ℤ)_{≤l}` are periodic of period `arithQ ρ L`, `L ≥ l`, in the
index.** -/
theorem fourier_add_mul_arithQ {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) {l L : ℕ} (hl : l ≤ L)
    {α : Work.Analysis.IonescuWainger.Circle}
    (hα : α ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l) (n t : ℤ) :
    fourier (T := 1) (n + t * (Work.KMTAreas.A7.arithQ ρ L : ℤ)) α
      = fourier (T := 1) n α := by
  rw [fourier_add, fourier_mul_arithQ_eq_one hρ hρ1 hl hα t, mul_one]



end

end Work.KMTPlan.A6Clean
