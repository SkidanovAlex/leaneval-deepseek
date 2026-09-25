import Mathlib
import Submission.Work.NN.Core.bmPotentialHolderContinuous
import Submission.Work.CR.Flat.Holder
import Submission.Work.CR.Flat.Cauchy.bmCZDefs
import Submission.Work.CR.Flat.Cauchy.bmPotential_iter_bound
import Submission.Work.CR.Flat.Cauchy.bmPotential_top_bound
import Submission.Work.CR.Flat.Cauchy.bmPotential_iteratedFDeriv
import Submission.Work.NN.Core.bmPot_riesz_Ck

namespace Work.NN.Core

/-- **The Bochner–Martinelli Schauder estimate in the `C^{k,α}` scale with data of class `C^k`**
(one derivative gain, the data hypothesis at level `k` rather than `k+1`), with a strictly smaller
conclusion polydisc.

For every `k` there is `C > 0` such that every family `f` of class `C^k` whose components vanish
off the open polydisc `polydisc c s` (more precisely: `f_j z = 0` whenever `s i ≤ ‖z i - c i‖` for
some `i`) satisfies, on every strictly smaller polydisc `polydisc c t < polydisc c s`,

`‖bmPotential f‖_{C^{k+1,α}(polydisc c t)} ≤ C Σ_j ‖f_j‖_{C^{k,α}(ℂⁿ)}`.

(The strict gap `t < s` is the usual bookkeeping: the data `D^m f · v` used in the induction are
supported off `polydisc c (2s)`, and the `k = 0` estimate applies to *those*.)

**Route.**  The case `k = 0` is
`Work.NN.Core.bmPotential_holder_one_of_holderNorm` (`NN/Core/bmPotentialHolderContinuous.lean`,
proved), which also supplies the *differentiability* of `bmPotential h` for every continuous,
bounded, `α`-Hölder, compactly supported datum `h` — this is what replaces the `C^{k+1}`
hypothesis of the existing `bmPotential_iter_bound` / `bmPotential_top_bound`.

For `k ≥ 1` fix `m ≤ k` and a tuple `v : Fin m → (Fin n → ℂ)` and put
`h_v := fun j y => iteratedFDeriv ℝ m (f j) y v`.  Then `h_v` is continuous, vanishes off
`polydisc c (2s)` (`bmIter_vanishing` applied with `r := 2s`) and
`∑_j holderNorm 0 α (h_v j) univ ≤ ofReal (∏ i, ‖v i‖) * ∑_j holderNorm k α (f j) univ`
(`bmIter_holderNorm_zero_le`).  The commutation identity `bmPotential_iteratedFDeriv` (valid for
`f` of class `C^m`, hence for `m ≤ k`) gives, *globally*,
`(iteratedFDeriv ℝ m (bmPotential f) y) v = bmPotential (h_v) y`.  Hence the `k = 0` estimate for
`h_v` bounds all the tuple values and their `α`-differences, and
`ofReal_opNorm_le_of_bound_prod` converts this into bounds for `iterDerivNorm m` and
`holderSeminorm m α` on `polydisc c t` for every `m ≤ k`.

For the top order `k+1`: the function `y ↦ iteratedFDeriv ℝ k (bmPotential f) y` is
multilinear-map-valued and one proves that it is *differentiable* at every point of
`polydisc c t` by the componentwise criterion: each scalar function
`y ↦ (iteratedFDeriv ℝ k (bmPotential f) y) v` equals `bmPotential (h_v)` globally, hence is
differentiable with `fderiv`-norm and `α`-Hölder bounds from the `k = 0` estimate; the candidate
derivative `L h := the multilinear map v ↦ fderiv ℝ (bmPotential (h_v)) z h` is multilinear in
`v` (using the multilinearity of `v ↦ h_v` and the additivity/homogeneity of
`h ↦ fderiv ℝ (bmPotential h) z`), and `HasFDerivAt` follows from
`hasFDerivAt_iff_isLittleO_nhds_zero`, the tuple-wise Taylor estimate
`‖bmPotential (h_v) (z + h) - bmPotential (h_v) z - fderiv ℝ (bmPotential (h_v)) z h‖
 ≤ C (∏ i, ‖v i‖) ‖h‖ ^ (1+α)`
(mean value inequality along the segment, as in `Work.NN.Core.taylor_le`) and
`ContinuousMultilinearMap.opNorm_le_iff`.  With that differentiability,
`norm_iteratedFDeriv_succ_le_of_bound` and `norm_iteratedFDeriv_succ_sub_le_of_holder`
(`CR/Flat/Cauchy/bmPotential_top_bound.lean`, proved) transfer the scalar bounds to
`iterDerivNorm (k+1)` and `holderSeminorm (k+1) α`.

A caveat on the last two lemmas: they ask for *global* differentiability of the
multilinear-valued function, while the componentwise argument gives it on `polydisc c (2s)`.
Either run the bookkeeping with the `Within` versions, or reprove the operator-norm bound from
the tuple-wise bounds on the polydisc using `ContinuousMultilinearMap.opNorm_le_iff` directly
(this is all that is needed, since the whole statement is about the *within*-norm on
`polydisc c t`). -/
theorem bmPotentialHolderNormLeCk {n : ℕ} (hn : 0 < n) {c : Fin n → ℂ} {s t : Fin n → ℝ}
    {α : ℝ} (hα : 0 < α) (hα1 : α < 1) (ht : ∀ j, 0 < t j) (hts : ∀ j, t j < s j) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : Fin n → (Fin n → ℂ) → ℂ, (∀ j, ContDiff ℝ k (f j)) →
      (∀ j z, (∃ i, s i ≤ ‖z i - c i‖) → f j z = 0) →
      Work.CR.Flat.holderNorm (k + 1) α (Work.CR.Flat.Cauchy.bmPotential f)
          (Work.CR.Flat.polydisc c t)
        ≤ ENNReal.ofReal C * ∑ j, Work.CR.Flat.holderNorm k α (f j) Set.univ := by
  classical
  -- The `C^{k,α}` Schauder estimate in the half-polydisc form: the datum vanishes off
  -- `polydisc c (2s)` and the conclusion holds on `polydisc c (2s / 2) = polydisc c s`.
  obtain ⟨C, hCpos, hC⟩ :=
    Work.NN.Core.bmPot_riesz_Ck (n := n) hn (c := c) (r := fun j => 2 * s j)
      hα hα1 (fun j => by linarith [ht j, hts j]) k
  refine ⟨C, hCpos, fun f hf hfsupp => ?_⟩
  by_cases hS : (∑ j, Work.CR.Flat.holderNorm k α (f j) Set.univ) = ⊤
  · -- the trivial case: the right-hand side is `⊤`
    have hne0 : ENNReal.ofReal C ≠ 0 := (ENNReal.ofReal_pos.mpr hCpos).ne'
    rw [hS, ENNReal.mul_top hne0]
    exact le_top
  · -- every component has finite `C^{k,α}` norm
    have hfin : ∀ j, Work.CR.Flat.holderNorm k α (f j) Set.univ < ⊤ := by
      intro j
      refine lt_top_iff_ne_top.mpr fun hj => hS ?_
      exact top_le_iff.mp (hj ▸ Finset.single_le_sum
        (f := fun i => Work.CR.Flat.holderNorm k α (f i) Set.univ)
        (fun i _ => bot_le) (Finset.mem_univ j))
    have hmain := hC f hf hfin (fun j z hz => by
      obtain ⟨i, hi⟩ := hz
      rw [show (2 * s i) / 2 = s i from by ring] at hi
      exact hfsupp j z ⟨i, hi⟩)
    -- shrink the conclusion polydisc from `polydisc c s` to `polydisc c t`
    have hsubset : Work.CR.Flat.polydisc c t
        ⊆ Work.CR.Flat.polydisc c (fun j => (2 * s j) / 2) :=
      Work.CR.Flat.polydisc_mono fun j => by
        rw [show (2 * s j) / 2 = s j from by ring]
        exact (hts j).le
    exact (Work.CR.Flat.holderNorm_mono_set (Ω := Work.CR.Flat.polydisc c (fun j => (2 * s j) / 2))
      (Ω' := Work.CR.Flat.polydisc c t) (Work.CR.Flat.isOpen_polydisc c _)
      (Work.CR.Flat.isOpen_polydisc c _) hsubset (k + 1) α
      (Work.CR.Flat.Cauchy.bmPotential f)).trans hmain

end Work.NN.Core
