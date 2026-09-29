import Mathlib
import Submission.HvdH.Interfaces
import Submission.Work.Main.mainStepOf
import Submission.Work.MainP.mainParams
import Submission.Work.MainP.prop52
import Submission.Work.MainP.prop53
import Submission.Work.MainP.crtWord

/-! Guidance from the project lead (the requester):

AREA OWNER: Main (paper Props 5.2–5.4, REFS/nlogn.txt lines 2130–2267). You prove
`KernelLib → IntLib → LayoutLib → FxLib → DFTMathProp → TransformProp → ResampleProp → ParamsProp → MainStepProp`.
Read HANDOFF.md and Interfaces.lean completely (MainStepProp, mainCost, MulBelow, the chapter Props you assume).
The step: for n := max(size x, size y) with n₁ ≤ n ≤ N (you choose n₁ huge), given MulBelow main N Cm, output
x·y with cost ≤ mainCost K Cm n = 12(T/r)·Cm(3rp) + K·T·(√p+1)·α·Cm(K·p) + K·n·size n.
ALGORITHM (paper Prop 5.4 with b, p, α, T, r, tᵢ, sᵢ from ParamsProp; S = ∏sᵢ > T/2, γ = 2Dα²):
1. Chunks: N' = ⌈n/b⌉; F_j, G_j < 2^b (IntLib.chunk). H = F·G has deg < 2N'−1 < S, coefficients < 2^{3b}.
2. CRT reindex (Agarwal–Cooley): position m < S ↦ multi-index (m mod s₁, …, m mod s_D) ↦ flat lexicographic index
   (undigits). Pad to length S with zeros, label, LayoutLib.sortByKey. Labels computed INCREMENTALLY while m runs
   (all residues increase by 1 with rare wraps; the flat index changes by a fixed W minus Σ over wrapped digits;
   O(size S) per element). Math: under this bijection the product mod x^S − 1 is the multidimensional cyclic
   convolution (s_i pairwise coprime; Nat.chineseRemainder), so H'' = S·convC ss F'' G'' (DFTMathProp's convC is
   normalised by 1/S).
3. u := 2^{−b}F'', v := 2^{−b}G'' exactly as fixed point: (F·2^{p−b}, 0).
4. Prop 5.2: F̃_s := FxLib.scale(c = 2^γ) ∘ B̃ ∘ F̃_t ∘ Ã (TransformProp on ts, ResampleProp's progA/progB);
   error < 2^{γ+5}T log₂T. F̃*_s(u) := conj(F̃_s(conj u)) (conjugation is exact on fixed point).
5. Prop 5.3: w̃ = scale(c = S, F̃*_s(F̃_s u · F̃_s v)) (pointwise FxLib.mulS), error < 2^{γ+8}T² log₂T; uses
   DFTMathProp (norm ≤ 1, linearity, convolution formula) and the linear contractions A, B.
6. Recover H'' = round(2^{2b}·S·w̃) exactly (error < ¼ needs γ < b − 13 and T log₂T < 2^{b+3}: true for n ≥ n₁).
7. Inverse reindex (label with m, sort), take 2N'−1 coefficients, IntLib.evalPoly at 2^b (all H_j < 2^{3b}).
COSTS: three TransformProp calls give exactly 12(T/r)·Cm(3r p) (lmax ts = r, ts.prod = T); six ResampleProp calls
give ≤ K·T(√p+1)α·Cm(K p) + O(T p²) (Cm monotone, merge constants); everything else must be ≤ K·n·size n for
n ≥ n₁: T·p² ≤ 288·n·b, table terms Σtᵢ·(p+1)^K ≤ D·r·(6b+1)^K = o(n), sorts O(S·p·log S). Side conditions to
discharge for n ≥ n₁: PowTwoParams, ResParams (θᵢ ≥ 1/(4D) and α⁴ ≥ 12D²b give α⁴θᵢ ≥ 3Db ≥ p), 3rp < n,
K_R·p < n, 2^γ ≤ 2^p, S ≤ 2^p. Split the work: (a) exact algebra (CRT, convolution, rounding), (b) numerical
error chain, (c) the program and its cost, (d) parameter inequalities for large n. Delegate these in parallel.
NOT needed: base case / small n (Assembly does it), the recursion inequality (Recursion does it).
-/

namespace Work.Main

/-- Paper Propositions 5.2, 5.3, 5.4: one recursive step of the multiplication algorithm. -/
theorem mainStep : HvdH.KernelLib → HvdH.IntLib → HvdH.LayoutLib → HvdH.FxLib → HvdH.DFTMathProp →
    HvdH.TransformProp → HvdH.ResampleProp → HvdH.ParamsProp → HvdH.MainStepProp := by
  intro hKer hInt hLay hFx hDFT hTr hRe hP
  exact mainStep_of hKer hInt hLay hFx hDFT hP Work.MainP.mainParams
    (Work.MainP.prop53 hKer hInt hLay hFx hDFT
      (Work.MainP.prop52 hKer hInt hLay hFx hDFT hTr hRe))
    (Work.MainP.crtWord hKer hInt hLay)

end Work.Main
