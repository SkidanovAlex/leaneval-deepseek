import Mathlib
import Submission.HvdH.Interfaces
import Submission.Work.Resample.defs
import Submission.Work.Resample.specs
import Submission.Work.Resample.core
import Submission.Work.Resample.sliceAu
import Submission.Work.Resample.sliceBu

/-! Guidance from the project lead (the requester):

AREA OWNER: Resample (paper Lemmas 4.8–4.12, proof of Thm 4.1, REFS/nlogn.txt lines 1604–1889). You prove
`KernelLib → IntLib → LayoutLib → FxLib → DFTMathProp → ResMath1DProp → ResampleProp`. Read HANDOFF.md and
Interfaces.lean (ResMath1DProp and its matrices, ResampleProp, ResParams, resCost, LayoutLib.applyAlong,
FxLib.mulF/expNeg/expPos). ResMath1DProp (assumed) gives the 1-D identity and all norm facts.
MATH:
M1. Define A := tensor of the 1-D `resA sᵢ tᵢ α` and B := tensor of `resB sᵢ tᵢ α` as linear maps on flat
    lexicographic arrays: successive application along axis i = 1..D (A: shape t₁..t_{i−1}, sᵢ→tᵢ, s_{i+1}..s_D),
    in exactly the `slices`/`unslices` layout of LayoutLib.applyAlong. Norm ≤ product of 1-D norms ≤ 1.
M2. Tensor factorisation of dftMulti: dftMulti ts (−1) = successive 1-D `dftMat tᵢ` along the axes (the phase is
    a sum over coordinates). With the 1-D identities F_{sᵢ} = 2^{2α²} Bᵢ F_{tᵢ} Aᵢ and mixed-product rules this gives
    dftMulti ss (−1) u = 2^{2Dα²} B(dftMulti ts (−1) (A u)).
M3. Error of a tensor of approximations ≤ Σᵢ ε(Ãᵢ) (Lemma 2.11 + Cor 2.8): D·p² once each 1-D error < p².
1-D APPROXIMATIONS (Lemmas 4.8–4.12), m := ⌈√p⌉·α:
- Ã₁ = S̃' (Lemma 4.9): (S'u)_k ≈ Σ_{|j − sk/t| < m} ½α⁻¹ e^{−πα⁻²(j−sk/t)²} u_{j mod s}; the tail is < 2^{−p};
  weights via FxLib.expNeg with (numerator, denominator) = ((jt − sk)², α²t²) and ½α⁻¹ exactly rounded; each
  weight×u product by FxLib.mulF (self). Error < 14m + 1 < 16p < p².
- Ẽ (Lemma 4.11) with m' = ⌈√p/(2α)⌉ terms; J̃' (Lemma 4.12): v⁽⁰⁾ = ρ(u/2), v⁽ʲ⁾ = Ẽv⁽ʲ⁻¹⁾, J̃'u = Σ(−1)ʲv⁽ʲ⁾,
  n = ⌈p/(α²θ)⌉ ≤ α² + 1 rounds; D̃' (Lemma 4.8) via FxLib.expPos (k_ℓ = s²β_ℓ² integer numerator over s²);
  C̃, P̃_t, P̃_s⁻¹ are pure data moves (label + LayoutLib.sortByKey; t⁻¹ mod s by any method, s is small).
- Tables per dimension (weights for all (k, j) pairs: tᵢ·2m entries, poly(p) each) are computed once and passed
  below the array so that the 1-D word q sees them in `rest` under applyAlong; the window of u_j's for output k
  is contiguous except near the wrap-around (Remark 4.10).
Costs: products by `self` need K·p < N (MulBelow with sizes ≤ p+2). Target resCost: K·T·(√p+1)·α·(Cm(Kp)+p)
+ K·T·p² + K·Σtᵢ·(p+1)^K. Never compute an exponential per array entry — only per table entry.
-/

namespace Work.Resample

/-!
## Status of `Work.Resample.resample` (Resample area, session report)

**Note on v1 of the interface.** In `Interfaces.lean` v1 the `loop` field of `HvdH.KernelLib` had the cost
bound `m * (c + K) + K`, which is unsatisfiable at `m = 0` (formally refuted by
`Work.Kernel.loopField_false` in `Submission/Work/Kernel/loopRefute.lean`), so `KernelLib` was
uninhabited and this statement was *vacuous*.  The lead's v2 fixes the bound to
`(m + 1) * (c + K) + K`; nothing may ever be discharged from `KernelLib` by contradiction.

**What the area has established** (all `sorry`-free, v2):

* `Submission.Work.Resample.defs` — `unb`, `dE`, `rA`, `rB`, `digitProd`, `tensorFun`/`tensorLin`,
  and the tensors `resAop = ⊗ᵢ resA sᵢ tᵢ α`, `resBop = ⊗ᵢ resB sᵢ tᵢ α`, `dftOp = ⊗ᵢ dftMat tᵢ`.
* `digitsFacts` — the mixed-radix bijection for `HvdH.digits`/`undigits`.
* `dftTensor` — `dftMulti ts (-1) u = dftOp ts u` (tensor factorisation of the multidimensional DFT).
* `tensorComp`, `tensorSmul` — mixed-product and scalar rules for the tensor.
* `tensorNorm` — `‖⊗ᵢ Mᵢ‖ ≤ ∏ᵢ ‖Mᵢ‖` in the sup norm.
* `resAopNorm`, `resBopNorm` — `‖resAop u‖ ≤ ‖u‖`, `‖resBop v‖ ≤ ‖v‖` (M1, from `ResMath1DProp`).
* `resampleIdentity` — **M2**: `dftMulti ss (-1) u = 2^{2Dα²} • resBop (dftMulti ts (-1) (resAop u))`.
* `axis.lean`, `fx.lean` — the flat-array machinery for the programs: `axisApply1Gen`,
  `fxTensorRec`, `tensorMapRec`, `matFam` (the `applyAlong`/`slices` layout).
* `tensorMapLin` — `tensorMapRec ss ts (matFam ss ts f) = tensorFun ss ts f`.
* `tensorMapErr`, `fxTensorErr` — tensoring of approximations (paper Lemma 2.11 / Cor 2.8), in
  ℂ-vector and fixed-point form: `ε(⊗Ãᵢ) ≤ Σᵢ ε(Ãᵢ)`.

**What is left** (the word-level part, `ResampleProp` (ii)): the one-dimensional words of Lemmas
4.8–4.12 — `S̃'` (4.9), `D̃'` (4.8), `Ẽ` (4.11), `J̃'` (4.12), `C̃`, `P̃_t`, `P̃_s⁻¹` — together with
their tables, the `applyAlong` chain over the `D` axes, and the final cost arithmetic.  The two
child statements that package the 1-D words are `Resample/sliceA1` and `Resample/sliceB1`; each
takes the library Props `KernelLib, IntLib, LayoutLib, FxLib, ResMath1DProp` as hypotheses (the
library words come from `hF.mulF`, `hF.mulS`, `hF.expNeg`, …).
-/

/-- The uniform one-dimensional slice words of `sliceAu` package `SliceSpecA`. -/
theorem sliceSpecA_of (KL : HvdH.KernelLib) (IL : HvdH.IntLib) (LL : HvdH.LayoutLib)
    (FL : HvdH.FxLib) (RM : HvdH.ResMath1DProp) : SliceSpecA KL IL LL FL RM :=
  sliceAu KL IL LL FL RM

/-- The uniform one-dimensional slice words of `sliceBu` package `SliceSpecB`. -/
theorem sliceSpecB_of (KL : HvdH.KernelLib) (IL : HvdH.IntLib) (LL : HvdH.LayoutLib)
    (FL : HvdH.FxLib) (RM : HvdH.ResMath1DProp) : SliceSpecB KL IL LL FL RM :=
  sliceBu KL IL LL FL RM

/-- Paper Thm 4.1 (Lem. 4.8-4.12 and tensoring): Gaussian resampling maps and their approximations. -/
theorem resample : HvdH.KernelLib → HvdH.IntLib → HvdH.LayoutLib → HvdH.FxLib → HvdH.DFTMathProp →
    HvdH.ResMath1DProp → HvdH.ResampleProp :=
  fun KL IL LL FL DFT RM =>
    resampleCore KL IL LL FL DFT RM (sliceSpecA_of KL IL LL FL RM) (sliceSpecB_of KL IL LL FL RM)

end Work.Resample
