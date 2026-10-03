/-
# The two precisely-stated remaining gaps of `Work.KMTPlan.A6.MdlSlicePktLinF`

This module only *defines* the statements (no proofs are postulated).  It serves two purposes:

* it fixes the decomposition of the paper's `(lin-1)` for the `f`-side packet family of §8 of
  Krause--Mirek--Tao (Annals 195 (2022)) — in the A6 carrier `mdlCore`/`Tle`/`mdlF`/`varphiNtj` —
  into

  1. `MdlPktVanishingCase` (`Submission/Work/KMTPlan/A6/MdlPktVanishingCase.lean`, **proved,
     axiom-clean**): the cases where the signed sums of the modified bumps are pointwise bounded,
     i.e. `k₁ ≥ 1` (any `j₁`) and `(k₁,j₁) = (0,1)`; and
  2. `MdlPktZeroZero` below: the remaining case `(k₁,j₁) = (0,0)`,

  so that `MdlSlicePktLinF` is their conjunction (see
  `MdlSlicePktLinF_of_zeroZero_vanishing`);

* it records the *analysis* of `MdlPktZeroZero`: at `(k₁,j₁) = (0,0)` the bump is the unmodulated
  `varphiNt N 0 t = φ_N e(Nt·)`, the pointwise (uniform-in-signs) bound fails at the frequency
  origin, and the functional calculus `Tle_mdlF_eq_Tm` identifies the clipped A6 family with the
  A7 `Hcl` family (`HclEstimate2`, which is the `p = 2` instance of
  `Work.KMTAreas.A7.lacunaryBumpVarEstimate`, itself assembled from the narrow/Farey, bad-scale
  and low-pass pieces).  The A7 assembly is complete and axiom-clean *except* for the low-pass
  input, which is the `p = 2` instance of the workspace's registered crux
  `Work.KMTAreas.A7HiRep.chainPartSqFun` — stated below as `CruxP2`, and the only genuinely missing
  input of the whole reduction.
-/
import Mathlib
import Submission.Work.KMTPlan.A6.MdlDefs
import Submission.Work.KMTAreas.A7Hi.LowpassDefs

set_option autoImplicit false

namespace Work.KMTPlan.A6

open MeasureTheory
open scoped ENNReal NNReal BigOperators
open Work.KMTAreas.A7Hi Work.KMTAreas.A7

/-- **The `p = 2` instance of the registered crux `Work.KMTAreas.A7HiRep.chainPartSqFun`**: the
chain part of the `r`-variational norm of the low-pass Ionescu--Wainger walk
`m ↦ lpf ρ l₁ m₀ m f = kmtProj ρ l₁ (-(m₀+m)) f` is dominated in `ℓ²(ℤ)` by the band square
function of its increments, with a constant free of the arithmetic height `l₁` and of the base
level `m₀` (on the good major arcs).

This is Lépingle's inequality plus the standard square function argument (Jones--Seeger--Wright,
`jsw`), i.e. exactly the step that Krause--Mirek--Tao cite for the low-frequency case
`s = -u`, `j = 0` of `(lin-1)`.  It is *strictly weaker* than the registered crux (which is stated
for all `p ∈ (1,∞)` and with the `Hyp`-hypothesis rather than `GoodMajorArcs`). -/
def CruxP2 (ρ : ℝ) (R : NNReal) : Prop :=
  ∃ Cρ : ℝ, 0 < Cρ ∧ ∃ C : ℝ, 0 < C ∧ ∀ (l₁ m₀ : ℕ),
    Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l₁ (-(m₀ : ℤ)) → ∀ f : ℤ → ℂ,
    MeasureTheory.eLpNorm (fun x : ℤ => Work.KMTAreas.A7Hi.chainPart R
        (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ m f x))
      2 MeasureTheory.Measure.count
      ≤ ENNReal.ofReal C *
          MeasureTheory.eLpNorm (Work.KMTAreas.A7Hi.sqFun ρ l₁ m₀ f) 2 MeasureTheory.Measure.count

/-- **The `ℓ²` low-pass variational estimate for the Ionescu--Wainger walk** — the `p = 2` instance
of `Work.KMTAreas.A7.LowpassVarDyadic`, i.e. the full `V^R = supPart + chainPart` conclusion at
`p = 2`.  It follows from `CruxP2` for the chain part (by definition) and from
`Work.KMTAreas.A7JSW.maximalFromCrux` for the values supremum, with the band square function
`Work.KMTAreas.A7Lpd.bandSquareUnif` supplying the `sqFun`-budget. -/
def LowpassVar2 (ρ : ℝ) (R : NNReal) : Prop :=
  ∃ Cρ : ℝ, 0 < Cρ ∧ ∃ C : ℝ, 0 < C ∧ ∀ (l₁ m₀ : ℕ),
    Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l₁ (-(m₀ : ℤ)) → ∀ f : ℤ → ℂ,
    MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm R
        (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ m f x))
      2 MeasureTheory.Measure.count
      ≤ ENNReal.ofReal (C * (1 + (l₁ : ℝ)) ^ 2) *
          MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count

/-- **The `p = 2` case of the A7 `(lin-1)` estimate in the carrier `Hcl`**, at the bottom height
`k₁ = 0` (the only case that the `(k₁,j₁) = (0,0)` instance of `MdlSlicePktLinF` needs): for the
modulated bump `varphiNt N 0 t = φ_N e(Nt·)`, the clipped exact-height family
`n ↦ 1_{core}·Tex ρ l₁ (varphiNt ⌊a n⌋ 0 t) f` obeys the `ℓ²`-variational estimate with the weight
`lossWeight A ρ l₁ l₂ 0 k₂`.

This is the `k₁ = 0` case of `Work.KMTAreas.A7.lacunaryBumpVarEstimate`; the A7 assembly
(`Work.KMTAreas.A7.lacunaryBumpVarEstimate_assembly`, axiom-clean, with the four inputs as
hypotheses) reduces it to the low-pass estimate `LowpassVar2` (through
`Work.KMTAreas.A7.lacunaryIUProjLowpassVar`-style monotone reindexing) together with the *proved*
narrow/Farey, clip and bad-scale pieces. -/
def HclEstimate2 (C₀ : ℕ) (R : NNReal) : Prop :=
  ∃ A : ℝ, 0 ≤ A ∧ ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → ∃ K : NNReal → NNReal,
    ∀ (a : ℕ → NNReal) (Λ : NNReal) (l₁ l₂ k₂ : ℕ) (t : ℝ) (f : ℤ → ℂ),
      1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ n : ℕ, 1 ≤ a n) →
      t ∈ Set.Icc (1 / 2 : ℝ) 1 →
      MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm R
          (fun n : ℕ => Work.KMTAreas.A7.Hcl ρ C₀ a l₁ l₂ 0 k₂ t f n x))
        2 MeasureTheory.Measure.count
        ≤ (K Λ : ENNReal) * ENNReal.ofReal (Work.KMTAreas.A7.lossWeight A ρ l₁ l₂ 0 k₂) *
            MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count

/-- **The `(k₁,j₁) = (0,0)` case of `Work.KMTPlan.A6.MdlSlicePktLinF`**, isolated: the paper's
`(lin-1)` for the `f`-side packet family at the bottom height and the zero twist.  This is the
half of the target that is *not* covered by `Work.KMTPlan.A6.MdlPktVanishingCase`. -/
def MdlPktZeroZero (C₀ : ℕ) (R : NNReal) : Prop :=
  ∃ A : ℝ, 0 ≤ A ∧ ∃ ρ₀ : ℝ, 0 < ρ₀ ∧
    ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → ∃ K : NNReal → NNReal,
      ∀ (a : ℕ → NNReal) (Λ : NNReal) (l₁ l₂ k₂ : ℕ) (t : ℝ) (f : ℤ → ℂ),
        1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ n : ℕ, 1 ≤ a n) →
        t ∈ Set.Icc (1 / 2 : ℝ) 1 →
        MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm R
            (fun n : ℕ =>
              if Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ l₂ 0 k₂ n then
                Work.KMTAreas.A7.Tle ρ l₁ (Work.KMTPlan.A6.varphiNtj (Nat.floor (a n)) 0 0 t)
                  (Work.KMTPlan.A6.mdlF ρ (Work.KMTAreas.A7.uScale ρ
                    (max (max l₁ l₂) (max 0 k₂))) l₁ f) x
              else 0))
          2 MeasureTheory.Measure.count
          ≤ (K Λ : ENNReal) *
              ENNReal.ofReal (Work.KMTAreas.A7.lossWeight A ρ l₁ l₂ 0 k₂) *
              MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count

/-- **The registered crux in its *existential, positive* form, at every exponent** — i.e. the
correct shape of the pipeline `Work.KMTAreas.A7HiRep.chainPartSqFun` / `…chainPartSqFunLeTwo`, whose
consumers (`A7.LowpassVarDyadic`, `A7.lacunaryIWProjLowpassVar`, and hence the whole A7 `(lin-1)`
assembly) instantiate it at a *positive* major-arc constant.  See the header of
`Submission/Work/KMTPlan/A6/MdlPktLinFRoad.lean` for why the registered free-constant form is
suspicious. -/
def CruxAll (ρ : ℝ) : Prop :=
  ∀ (r : NNReal) (hr : 2 < r) (p : ENNReal) (hp : 1 < p) (hptop : p < ⊤),
    ∃ Cρ : ℝ, 0 < Cρ ∧ ∃ C : ℝ, 0 < C ∧ ∀ (l₁ m₀ : ℕ),
      Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l₁ (-(m₀ : ℤ)) → ∀ f : ℤ → ℂ,
      MeasureTheory.eLpNorm (fun x : ℤ => Work.KMTAreas.A7Hi.chainPart r
          (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ m f x))
        p MeasureTheory.Measure.count
        ≤ ENNReal.ofReal C *
            MeasureTheory.eLpNorm (Work.KMTAreas.A7Hi.sqFun ρ l₁ m₀ f) p MeasureTheory.Measure.count

/-- **The `ℓᵖ` low-pass variational estimate for the Ionescu--Wainger walk, at every exponent** —
the existential-positive form of `Work.KMTAreas.A7.LowpassVarDyadic` (which is the `r`, `p`
parameterised family of statements below). -/
def LowpassVarAll (ρ : ℝ) : Prop :=
  ∀ (r : NNReal) (hr : 2 < r) (p : ENNReal) (hp : 1 < p) (hptop : p < ⊤),
    ∃ Cρ : ℝ, 0 < Cρ ∧ ∃ C : ℝ, 0 < C ∧ ∀ (l₁ m₀ : ℕ) (f : ℤ → ℂ),
      Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l₁ (-(m₀ : ℤ)) →
      MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ m f x))
        p MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (C * (1 + (l₁ : ℝ)) ^ 2) *
            MeasureTheory.eLpNorm f p MeasureTheory.Measure.count

/-- **The height-`0` instance of `MdlPktZeroZero`.**  Here the exact-height carrier `Tex ρ 0` is
identically zero (`Work.KMTAreas.A7.Tex_zero_level`), so this case is *not* covered by
`HclEstimate2`; it is the genuine bottom-height low-pass walk
`n ↦ Tle ρ 0 (varphiNt ⌊a n⌋ 0 t) (mdlF ρ (uScale ρ L) 0 f) = kmtProj ρ 0 (-(logN ⌊a n⌋))` of `f`,
i.e. a plain lacunary dilation family — the case covered by the *clean* height-`0` linear estimate
(`Work.KMTAreas.A7.LoLinVar`, `Work.KMTAreas.A7Hi.kmtProj_zero_varBound`). -/
def MdlPktZeroZeroAtZero (C₀ : ℕ) (R : NNReal) : Prop :=
  ∃ A : ℝ, 0 ≤ A ∧ ∃ ρ₀ : ℝ, 0 < ρ₀ ∧
    ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → ∃ K : NNReal → NNReal,
      ∀ (a : ℕ → NNReal) (Λ : NNReal) (l₂ k₂ : ℕ) (t : ℝ) (f : ℤ → ℂ),
        1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ n : ℕ, 1 ≤ a n) →
        t ∈ Set.Icc (1 / 2 : ℝ) 1 →
        MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm R
            (fun n : ℕ =>
              if Work.KMTPlan.A6.mdlCore ρ C₀ a 0 l₂ 0 k₂ n then
                Work.KMTAreas.A7.Tle ρ 0 (Work.KMTPlan.A6.varphiNtj (Nat.floor (a n)) 0 0 t)
                  (Work.KMTPlan.A6.mdlF ρ (Work.KMTAreas.A7.uScale ρ
                    (max (max 0 l₂) (max 0 k₂))) 0 f) x
              else 0))
          2 MeasureTheory.Measure.count
          ≤ (K Λ : ENNReal) *
              ENNReal.ofReal (Work.KMTAreas.A7.lossWeight A ρ 0 l₂ 0 k₂) *
              MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count

/-- **The positive-height instance `l₁ ≥ 1` of `MdlPktZeroZero`** — the case in which the composite
is identified with the A7 `Hcl` family by
`Work.KMTPlan.A6.Tle_mdlF_eq_Tm_local`, and hence follows from `HclEstimate2`. -/
def MdlPktZeroZeroPos (C₀ : ℕ) (R : NNReal) : Prop :=
  ∃ A : ℝ, 0 ≤ A ∧ ∃ ρ₀ : ℝ, 0 < ρ₀ ∧
    ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → ∃ K : NNReal → NNReal,
      ∀ (a : ℕ → NNReal) (Λ : NNReal) (l₁ l₂ k₂ : ℕ) (t : ℝ) (f : ℤ → ℂ),
        1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ n : ℕ, 1 ≤ a n) →
        t ∈ Set.Icc (1 / 2 : ℝ) 1 → 1 ≤ l₁ →
        MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm R
            (fun n : ℕ =>
              if Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ l₂ 0 k₂ n then
                Work.KMTAreas.A7.Tle ρ l₁ (Work.KMTPlan.A6.varphiNtj (Nat.floor (a n)) 0 0 t)
                  (Work.KMTPlan.A6.mdlF ρ (Work.KMTAreas.A7.uScale ρ
                    (max (max l₁ l₂) (max 0 k₂))) l₁ f) x
              else 0))
          2 MeasureTheory.Measure.count
          ≤ (K Λ : ENNReal) *
              ENNReal.ofReal (Work.KMTAreas.A7.lossWeight A ρ l₁ l₂ 0 k₂) *
              MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count

end Work.KMTPlan.A6
