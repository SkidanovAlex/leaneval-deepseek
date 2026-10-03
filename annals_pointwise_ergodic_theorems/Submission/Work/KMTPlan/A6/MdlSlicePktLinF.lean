import Mathlib
import Submission.Work.KMTPlan.A6.MdlPktLinFAssembly
import Submission.Work.KMTPlan.A6.MdlPktZeroZeroAtZero
import Submission.Work.KMTPlan.A6.MdlPktZeroZeroPos_of_hclEstimate2
import Submission.Work.KMTPlan.A6.LowpassLoss
import Submission.Work.KMTPlan.A6.shallowChainLe
import Submission.Work.KMTPlan.A6.deepChainLe
import Submission.Work.KMTAreas.A7.lacunaryBumpBadPartBound
import Submission.Work.KMTAreas.A7.lacunaryBumpLowpassClipBoundGen

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.KMTPlan.A6

open MeasureTheory
open scoped ENNReal NNReal BigOperators

/-- **`HclEstimate2` from the low-pass estimate with a polynomial loss.**

Verbatim the proof of `hclEstimate2_of_cruxAll` (`Submission/Work/KMTPlan/A6/MdlPktLinFHcl.lean`),
with the `hLowpass` input of `Work.KMTAreas.A7.lacunaryBumpVarEstimate_assembly` supplied directly
instead of through the `l₁`-free crux: the other two inputs are the proved
`lacunaryBumpLowpassClipBoundGen` and `lacunaryBumpBadPartBound`. -/
theorem hclEstimate2_of_lowpassVar (C₀ : ℕ) (hC₀ : 1 ≤ C₀) (R : NNReal) (hR : 2 < R)
    (hLowpass : ∀ (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (r : NNReal) (hr : 2 < r)
      (p : ENNReal) (hp : 1 < p) (hptop : p < ⊤) (Λ : NNReal) (hΛ : 1 < Λ),
      ∃ Cρ : ℝ, 0 < Cρ ∧ ∃ C : ℝ, 0 < C ∧
        ∀ (k : ℤ) (l₁ : ℕ) (a : ℕ → NNReal)
          (ha : PointwiseErgodicTheorems.Lacunary Λ a) (ha1 : ∀ n, 1 ≤ a n) (f : ℤ → ℂ),
          Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l₁ k →
          (∀ n : ℕ, -(Work.Analysis.EndVar.logN (Nat.floor (a n))) ≤ k) →
          MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
              (fun n : ℕ => Work.KMTAreas.A7.Tle ρ l₁
                (Work.KMTAreas.A7.varphiN (Nat.floor (a n)) 0) f x))
            p MeasureTheory.Measure.count
            ≤ ENNReal.ofReal (C * (1 + (l₁ : ℝ)) ^ 2) *
                MeasureTheory.eLpNorm f p MeasureTheory.Measure.count) :
    HclEstimate2 C₀ R := by
  classical
  obtain ⟨A, hA, ρ₀, hρ0, hgen⟩ :=
    Work.KMTAreas.A7.lacunaryBumpVarEstimate_assembly
      (fun ρ hρ hρ1 r hr p hp hptop Λ hΛ => hLowpass ρ hρ hρ1 r hr p hp hptop Λ hΛ)
      (fun ρ hρ hρ1 C₀ Cρc Cρ hCρpos hCρc Λ hΛ r hr p hp hptop C hCpos =>
        Work.KMTAreas.A7.lacunaryBumpLowpassClipBoundGen ρ hρ hρ1 C₀ Cρc Cρ hCρpos hCρc
          Λ hΛ r hr p hp hptop C hCpos)
      (fun ρ hρ hρ1 C₀ hC₀ hρC Cρc hCρc Λ hΛ r hr p hp hptop =>
        Work.KMTAreas.A7.lacunaryBumpBadPartBound ρ hρ hρ1 C₀ hC₀ hρC Cρc hCρc Λ hΛ r hr p hp hptop)
      C₀ hC₀ R hR
  refine ⟨A, hA, ρ₀, hρ0, ?_⟩
  intro ρ hρ hρ0'
  obtain ⟨K, hK⟩ := hgen ρ hρ hρ0' 2 (by norm_num) (by norm_num)
  exact ⟨K, fun a Λ l₁ l₂ k₂ t f hΛ ha ha1 ht => hK a Λ l₁ l₂ 0 k₂ t f hΛ ha ha1 ht⟩

/-- Do NOT prove this from `Work.KMTPlan.A6.MdlSliceLinF`, `MdlSliceLinG`, `MdlSliceCoreGainBig`,
`MdlSliceCoreGainEstimate` or any other declaration that is proved by `sorry` (a proof using them
would contain `sorryAx` and be rejected).  This is the paper's `(lin-1)` for the `f`-side packet
family `n ↦ T^{l₁}_{φ_{⌊a n⌋,k₁,t,j₁}} (Π_{l₁,≤-u}f)` of §8 of Krause--Mirek--Tao, Annals 195
(2022), in the carrier used by the A6 model tuple `Work.KMTPlan.A6.mdlPart`.  Useful existing
material: `Work.KMTAreas.A7.lacunaryBumpVarEstimate` (PROVED, the same estimate for the `Tex`
carrier with the unmodified bump `varphiNt`), `Work.KMTPlan.A6.Tle_mdlF_eq_Tm` (PROVED, the
functional calculus `Tle ρ l (varphiNt N k t) (mdlF ρ u l f) = Tm ρ l (varphiNt N k t) f`),
`Work.KMTPlan.A6.Tle_mdlF_eq_iwConv`, `Work.KMTAreas.A7.ModelOps` (`Tm`, `diffFreqs`),
`Work.Analysis.IonescuWainger.MajorArcs` (`iwArithFreqsNew`), and the A7 files
`lacunaryBumpAux`, `lacunaryBumpGlue`, `lacunaryBumpExponent`, `lacunaryBumpFinal`,
`lacunaryBump_mult_bound_k1pos`, `lacunaryBump_mult_bound_k0_diff`,
`varEst_of_narrow_symbols_twoEndpoints`, `opArc_iwArithFreqs_endpoint`.

## Where the proof comes from

Everything except the low-pass input of the A7 assembly is proved, and the whole reduction is

  `Work.KMTAreas.A7.lacunaryBumpVarEstimate_assembly`   (the A7 §8 assembly, PROVED)
    with its four inputs supplied by
      * `Work.KMTAreas.A7.lacunaryBumpLowpassClipBoundGen`  (PROVED),
      * `Work.KMTAreas.A7.lacunaryBumpBadPartBound`         (PROVED),
      * the *low-pass* input `Work.KMTPlan.A6.lowpassVar_of_parts` (PROVED here), assembled from
          - `Work.KMTPlan.A6.shallowChainLe` (the frozen/dyadic shallow half, PROVED),
          - `Work.KMTPlan.A6.deepChainLe` (the decimated deep half, PROVED),
          - the glue `Work.KMTPlan.A6.chainLe_dyadic_of_parts`,
            `Work.KMTPlan.A6.dyadicVarLe_of_chain` and `Work.KMTPlan.A6.lacLowpassVar_of_dyadic`;
    ⟹ `HclEstimate2`                             (`hclEstimate2_of_lowpassVar`, PROVED here)
    ⟹ `MdlPktZeroZeroPos`                         (`MdlPktZeroZeroPos_of_hclEstimate2`, PROVED)
    ⟹ `MdlPktZeroZero`                            (`MdlPktLinFAssembly.MdlPktZeroZero_of_split`, PROVED,
                                                   with `MdlPktZeroZeroAtZero`, PROVED)
    ⟹ the target                                  (`MdlPktLinFAssembly.MdlSlicePktLinF_of_zeroZero`,
                                                   PROVED, which also uses the PROVED vanishing case
                                                   `MdlPktVanishingCase` for `(k₁,j₁) ≠ (0,0)`).

So the target no longer depends on the workspace's canonical crux
`Work.KMTAreas.A7HiRep.chainPartSqFunPos`: the low-pass estimate is obtained *with* a polynomial
loss `(1+l₁)²` in the arithmetic height, which the target's weight
`Work.KMTAreas.A7.lossWeight A ρ l₁ l₂ k₁ k₂` absorbs (the assembly's own bookkeeping uses
`lossWeight 4`).  The `l₁`-free form of the crux would need the *uniform* vector-valued
Ionescu--Wainger multiplier theorem of T. Tao (Remark (iii) after Theorem `thm:iw` of the paper),
which is not available in this workspace; the lossy route above avoids it entirely. -/
theorem MdlSlicePktLinF (C₀ : ℕ) (hC₀ : 1 ≤ C₀) (R : NNReal) (hR : 2 < R)
    (j₁ : ℤ) (hj₁ : j₁ ∈ ({-1, 0, 1} : Finset ℤ)) :
    ∃ A : ℝ, 0 ≤ A ∧ ∃ ρ₀ : ℝ, 0 < ρ₀ ∧
      ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → ∃ K : NNReal → NNReal,
        ∀ (a : ℕ → NNReal) (Λ : NNReal) (l₁ l₂ k₁ k₂ : ℕ) (t : ℝ) (f : ℤ → ℂ),
          1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ n : ℕ, 1 ≤ a n) →
          t ∈ Set.Icc (1 / 2 : ℝ) 1 → (k₁ = 0 → j₁ ≠ -1) →
          MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm R
              (fun n : ℕ =>
                if Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n then
                  Work.KMTAreas.A7.Tle ρ l₁ (Work.KMTPlan.A6.varphiNtj (Nat.floor (a n)) k₁ j₁ t)
                    (Work.KMTPlan.A6.mdlF ρ (Work.KMTAreas.A7.uScale ρ
                      (max (max l₁ l₂) (max k₁ k₂))) l₁ f) x
                else 0)) 2 MeasureTheory.Measure.count
            ≤ (K Λ : ENNReal) *
                ENNReal.ofReal (Work.KMTAreas.A7.lossWeight A ρ l₁ l₂ k₁ k₂) *
                MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count := by
  exact MdlSlicePktLinF_of_zeroZero C₀ hC₀ R hR j₁ hj₁
    (MdlPktZeroZero_of_split C₀ R (mdlPktZeroZeroAtZero C₀ hC₀ R hR)
      (MdlPktZeroZeroPos_of_hclEstimate2 C₀ hC₀ R hR
        (hclEstimate2_of_lowpassVar C₀ hC₀ R hR
          (lowpassVar_of_parts shallowChainLe deepChainLe))))

end Work.KMTPlan.A6
