/-
# Area A4Z: the free-window fine inverse theorem `LipL1FineA` (Proposition `lip`, fine support)

`Work.KMTAreas.A4.lipL1Fine` proves the *pinned* fine inverse theorem `LipL1Fine P`, in which the
support window of the three input functions is `N₀ ∈ [N^d/2, 2 N^d]` and the returned dual function
`F` has Fourier support in the union of the `q` arcs of radius `2^k` around the `q`-torsion
frequencies of the frequency circle, with `q ≲ δ^{-O(1)}` and `2^k ≲ δ^{-O(1)}/N`.

The §5.2 chain of Krause--Mirek--Tao needs this statement with a **free** window
`N₀ ∈ [N^d/A, A N^d]`, the constants being allowed to depend on `A` but not on `ρ`
(see `NOTES_A4_window_pin_GAP.md`: the pinned form is vacuous for `P = 100 X²`).  That is exactly
`Work.KMTAreas.A4.LipL1FineA P`.

The proof is the usual split along the Peluse dichotomy (Krause--Mirek--Tao §5.1):

* `Work.KMTAreas.A4Z.lipL1FineA_caseA` (file `A4Z/lipL1FineACore.lean`) -- the branch
  `N ≤ C δ^{-K}`, in which the transposed dual function `Ã_N^*(h,g)` (normalised by `C/(2A+5)`)
  is a witness, with the single arc `{0}` of radius `1` (the whole frequency circle);
* `Work.KMTAreas.A4Z.lipL1FineACaseB` (file `A4Z/lipL1FineACaseB.lean`) -- the branch
  `C δ^{-K} < N`, the §5.1 smoothing construction `F = λ • smoothOp (lipWeight ψ ε N') G q`, whose
  Fourier transform is supported in the torsion arcs (`A4.lipWeightFourierSupportFine`).

The two branches are then merged below with the usual monotonicity of `C δ^{-K}` and of each clause
of the conclusion in the pair `(C, K)` (note that the correlation clause `δ^K N^d ≤ ‖⟨f,F⟩‖`
*weakens* in `K`, which is the direction needed).  This is the same architecture as
`A4/peluseLipL1TailA.lean` for Proposition `lip`.
-/
import Mathlib
import Submission.Work.KMTAreas.A4Z.lipL1FineACaseB

set_option autoImplicit false
set_option maxHeartbeats 4000000

open scoped BigOperators FourierTransform
open MeasureTheory

namespace Work.KMTAreas.A4Z

open Work.KMTAreas.A4 Work.Analysis.InverseTheory

theorem lipL1FineA (P : Polynomial ℤ) (hP : 2 ≤ P.natDegree) (hPel : Work.KMTContract.PeluseInverseKMT P) : Work.KMTAreas.A4.LipL1FineA P := by
  intro Aw hAw
  obtain ⟨CB, KB, hCBpos, hKBpos, hB⟩ := lipL1FineACaseB P hP hPel Aw hAw
  set K : ℝ := max 1 KB with hKdef
  set C : ℝ := max (2 * Aw + 5) CB with hCdef
  have hK1 : 1 ≤ K := by rw [hKdef]; exact le_max_left _ _
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK1
  have hCw : 2 * Aw + 5 ≤ C := by rw [hCdef]; exact le_max_left _ _
  have hCB : CB ≤ C := by rw [hCdef]; exact le_max_right _ _
  have hKB : KB ≤ K := by rw [hKdef]; exact le_max_right _ _
  have hCpos : 0 < C := lt_of_lt_of_le (by linarith : (0 : ℝ) < 2 * Aw + 5) hCw
  refine ⟨C, K, hCpos, hKpos, ?_⟩
  intro ρ hρpos hρle N N₀ δ f g h hN hδpos hδle hN₀lo hN₀hi hfs hgs hhs hfb hgb hhb hcorr
  have hD1 : 1 ≤ δ⁻¹ := (one_le_inv₀ hδpos).mpr hδle
  have hDmono : δ⁻¹ ^ KB ≤ δ⁻¹ ^ K := Real.rpow_le_rpow_of_exponent_le hD1 hKB
  have hCmono : CB * δ⁻¹ ^ KB ≤ C * δ⁻¹ ^ K :=
    mul_le_mul hCB hDmono (Real.rpow_nonneg (le_trans zero_le_one hD1) KB) hCpos.le
  by_cases hlarge : CB * δ⁻¹ ^ KB < (N : ℝ)
  · -- #### the large-`N` branch: the smoothing construction of §5.1
    obtain ⟨F, k, 𝔸, h1, h2, h3, h4, h5, h6, h7⟩ :=
      hB ρ hρpos hρle N N₀ δ f g h hN hδpos hδle hN₀lo hN₀hi hfs hgs hhs hfb hgb hhb hcorr
        hlarge
    refine ⟨F, k, 𝔸, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro x
      exact le_trans (h1 x) hCmono
    · exact h2
    · exact le_trans h3 (mul_le_mul_of_nonneg_right hCmono (by positivity))
    · exact h4
    · exact le_trans h5 hCmono
    · have hNnn : (0 : ℝ) ≤ (N : ℝ) := by positivity
      exact le_trans h6 (div_le_div_of_nonneg_right hCmono hNnn)
    · calc δ ^ K * (N : ℝ) ^ P.natDegree
          ≤ δ ^ KB * (N : ℝ) ^ P.natDegree :=
            mul_le_mul_of_nonneg_right
              (Real.rpow_le_rpow_of_exponent_ge hδpos hδle hKB) (by positivity)
        _ ≤ ‖bilinPair f F‖ := h7
  · -- #### the small-`N` branch: the transposed dual function
    have hNle : (N : ℝ) ≤ C * δ⁻¹ ^ K := le_trans (not_lt.mp hlarge) hCmono
    exact lipL1FineA_caseA P hP Aw C K hAw hCw hK1 ρ hρpos hρle N N₀ δ f g h hN hδpos hδle
      hN₀lo hN₀hi hfs hgs hhs hfb hgb hhb hcorr hNle

end Work.KMTAreas.A4Z
