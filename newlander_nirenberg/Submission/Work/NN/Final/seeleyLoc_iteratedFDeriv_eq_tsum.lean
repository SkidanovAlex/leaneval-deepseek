import Mathlib
import Submission.Work.NN.Final.SeeleyLoc

noncomputable section

open scoped NNReal ENNReal ContDiff Topology BigOperators
open Set Filter

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Work.NN.Final

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ## Supporting lemmas

On the open lower slab `seLw W δ = W × (-δ,0)` the Seeley extension `seeleyExt a b g` coincides
with the Seeley sum `seeleySum a b g`, and the latter is locally a finite sum of the terms
`seeleyTerm a b g m`: near a point `x` with `x.2 < 0`, every term with `b m * |x.2| ≥ 4` vanishes
on the neighbourhood `{q | q.2 < x.2 / 2}` of `x`. Hence the iterated derivative of the extension
is the (finite, then `tsum`-) sum of the iterated derivatives of the terms. -/

/-- If `b m * |x.2| ≥ 4` with `x.2 < 0`, then the `m`-th Seeley term vanishes on the half space
`{q | q.2 < x.2 / 2}` (where the argument of the cutoff is `> 2` in absolute value). -/
lemma seeleyLoc_seeleyTerm_eq_zero_of_abs {a b : ℕ → ℝ} {g : E × ℝ → ℂ} {x q : E × ℝ} {m : ℕ}
    (hbm : 0 < b m) (hm : 4 ≤ b m * |x.2|) (hx : x.2 < 0) (hq : q.2 < x.2 / 2) :
    seeleyTerm a b g m q = 0 := by
  have hxabs : |x.2| = -x.2 := abs_of_neg hx
  have hqneg : q.2 < 0 := by linarith
  have hqabs : |q.2| = -q.2 := abs_of_neg hqneg
  have h2 : 2 ≤ |-(b m) * q.2| := by
    rw [abs_neg_mul, abs_of_nonneg hbm.le, hqabs]
    nlinarith only [hm, hxabs, hq, hbm]
  simp only [seeleyTerm, seeleyCut_eq_zero h2, zero_smul, smul_zero]

/-- The `m`-th Seeley term is `C^i` at `x` whenever `g` is `C^i` on the closed upper half space
and the point `(x.1, -(b m) * x.2)` (at which the term evaluates `g`) lies in the open upper half
space. -/
lemma seeleyLoc_contDiffAt_seeleyTerm {a b : ℕ → ℝ} {n i : ℕ} {W : Set E} (hW : IsOpen W)
    {g : E × ℝ → ℂ} (hg : ContDiffOn ℝ (i : WithTop ENat) g (seHp W)) {x : E × ℝ}
    (hx : (x.1, -(b n) * x.2) ∈ seUp W) :
    ContDiffAt ℝ (i : WithTop ENat) (seeleyTerm a b g n) x := by
  have hmem : seUp W ∈ 𝓝 ((x.1, -(b n) * x.2)) := (isOpen_seUp hW).mem_nhds hx
  have hgAt : ContDiffAt ℝ (i : WithTop ENat) g ((x.1, -(b n) * x.2)) :=
    hg.contDiffAt (Filter.mem_of_superset hmem seUp_subset_seHp)
  have hcomp : ContDiffAt ℝ (i : WithTop ENat) (fun q : E × ℝ => g (q.1, -(b n) * q.2)) x := by
    have hlin : ContDiffAt ℝ (i : WithTop ENat) (fun q : E × ℝ => (q.1, -(b n) * q.2)) x := by
      have h1 : (fun q : E × ℝ => (q.1, -(b n) * q.2))
          = ⇑((ContinuousLinearMap.fst ℝ E ℝ).prod
                ((-(b n)) • ContinuousLinearMap.snd ℝ E ℝ)) := by
        funext q; simp
      rw [h1]
      exact (ContinuousLinearMap.contDiff _).contDiffAt
    exact hgAt.comp x hlin
  have hcut : ContDiffAt ℝ (i : WithTop ENat) (fun q : E × ℝ => seeleyCut (-(b n) * q.2)) x := by
    have h2 : (fun q : E × ℝ => -(b n) * q.2)
        = ⇑(((-(b n)) : ℝ) • ContinuousLinearMap.snd ℝ E ℝ) := by funext q; simp
    have h3 : ContDiffAt ℝ (i : WithTop ENat) (fun q : E × ℝ => -(b n) * q.2) x := by
      rw [h2]; exact (ContinuousLinearMap.contDiff _).contDiffAt
    exact ContDiffAt.comp x
      ((seeleyCut_contDiff.of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt) h3
  exact (hcut.smul hcomp).const_smul (a n)

/-- The iterated derivative at a point only depends on the germ of the function. -/
lemma seeleyLoc_iteratedFDeriv_congr_of_eventuallyEq {f h : E × ℝ → ℂ} {x : E × ℝ}
    (hfe : f =ᶠ[𝓝 x] h) (k : ℕ) :
    iteratedFDeriv ℝ k f x = iteratedFDeriv ℝ k h x := by
  have h' : f =ᶠ[𝓝[Set.univ] x] h := by rwa [nhdsWithin_univ]
  have := Filter.EventuallyEq.iteratedFDerivWithin_eq (𝕜 := ℝ) h' hfe.eq_of_nhds k
  simpa only [iteratedFDerivWithin_univ] using this

/-- The `i`-th iterated derivative of the Seeley extension on the open lower slab equals the termwise series of the derivatives of the Seeley terms, whenever the terms with index at least `N` vanish on a neighbourhood of the point. -/
theorem seeleyLoc_iteratedFDeriv_eq_tsum {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a b : ℕ → ℝ} (hb : ∀ m, 2 ≤ b m)
    (hbT : Filter.Tendsto b Filter.atTop Filter.atTop) {W : Set E} (hW : IsOpen W)
    {δ : ℝ} {i : ℕ} {g : E × ℝ → ℂ} (hg : ContDiffOn ℝ (i : WithTop ENat) g (seHp W))
    {x : E × ℝ} (hx : x ∈ seLw W δ) {N : ℕ} (hN : ∀ m ≥ N, 4 ≤ b m * |x.2|) :
    iteratedFDeriv ℝ i (seeleyExt a b g) x
      = ∑' n, iteratedFDeriv ℝ i (seeleyTerm a b g n) x := by
  have hx2 : x.2 < 0 := hx.2.2
  have hxW : x.1 ∈ W := hx.1
  have hneigh : {q : E × ℝ | q.2 < x.2 / 2} ∈ 𝓝 x :=
    (isOpen_lt continuous_snd continuous_const).mem_nhds
      (by simp only [Set.mem_ofPred_eq]; linarith)
  -- the extension agrees, near `x`, with the finite sum of the terms of index `< N`
  have hev : seeleyExt a b g =ᶠ[𝓝 x]
      (fun q => ∑ m ∈ Finset.range N, seeleyTerm a b g m q) := by
    filter_upwards [hneigh] with q hq
    have hqneg : q.2 < 0 := by linarith
    rw [seeleyExt_of_neg a b g hqneg, seeleySum]
    exact tsum_eq_sum (s := Finset.range N) (f := fun m => seeleyTerm a b g m q) (fun m hm => by
      simp only [Finset.mem_range, not_lt] at hm
      exact seeleyLoc_seeleyTerm_eq_zero_of_abs (by linarith [hb m]) (hN m hm) hx2 hq)
  -- the derivative of the finite sum is the sum of the derivatives
  have h2 : iteratedFDeriv ℝ i (fun q => ∑ m ∈ Finset.range N, seeleyTerm a b g m q) x
      = ∑ m ∈ Finset.range N, iteratedFDeriv ℝ i (seeleyTerm a b g m) x :=
    iteratedFDeriv_fun_sum_apply (fun m _ =>
      seeleyLoc_contDiffAt_seeleyTerm hW hg (mem_seUp.mpr ⟨hxW, by nlinarith [hb m, hx2]⟩))
  -- the series of derivatives is the same finite sum: the terms of index `≥ N` vanish
  have h3 : ∑ m ∈ Finset.range N, iteratedFDeriv ℝ i (seeleyTerm a b g m) x
      = ∑' n, iteratedFDeriv ℝ i (seeleyTerm a b g n) x := by
    refine (tsum_eq_sum (s := Finset.range N)
      (f := fun n => iteratedFDeriv ℝ i (seeleyTerm a b g n) x) ?_).symm
    intro n hn
    have hnN : N ≤ n := by simpa [Finset.mem_range, not_lt] using hn
    have hz : seeleyTerm a b g n =ᶠ[𝓝 x] (0 : E × ℝ → ℂ) := by
      filter_upwards [hneigh] with q hq
      exact seeleyLoc_seeleyTerm_eq_zero_of_abs (by linarith [hb n]) (hN n hnN) hx2 hq
    rw [seeleyLoc_iteratedFDeriv_congr_of_eventuallyEq hz i]
    simp
  rw [seeleyLoc_iteratedFDeriv_congr_of_eventuallyEq hev i, h2, h3]

end Work.NN.Final
