/-
# `FTS/ClassCHon/Lop_good` — the iterate of `Lzero1` preserves the class `Good`

`Lop g k` is the `k`-fold iterate of the angular operator
`Lzero1 u = -u'' + ∂_θ(tan θ · u) - 6u` (`Work.FTS.EllipticEst.Lzero1`), and
`Good a b g` says that `g` is `C^∞` (`Work.Stability.smoothOrder`, the *honest* smooth
order `∞ = ↑⊤ : ℕ∞ω`, not the analytic order `ω = ⊤`) and vanishes off the closed interval
`[a,b]`.

Here we show that `Good a b` is stable under `Lzero1`, hence under every iterate:
if `0 < a`, `b < π/2` and `Good a b g` then `Good a b (Lop g k)` for every `k`.

The two ingredients are

* the support: `Lzero1` is built from `deriv`'s of `u`, so the support is preserved
  because `u` vanishes *on an open set* around every point outside `[a,b]`
  (`Lzero1_eq_zero_of_not_mem`);
* the smoothness: `deriv` preserves `C^∞` (`contDiff_infty_iff_deriv`), and
  `θ ↦ tan θ · u θ` is `C^∞` because `u` vanishes in a neighbourhood of the singularities
  of `tan`: on `[a,b] ⊂ (0,π/2)` the tangent is smooth, and off `[a,b]` the product is
  locally `0` (`contDiff_tan_mul_of_support`).
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Submission.Work.FTS.ClassCHon.CmodeDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Topology

namespace Work.FTS.ClassCHon

/-- A function which is eventually `0` at `θ` has derivative `0` there. -/
private lemma deriv_eq_zero_of_eventuallyEq_zero {u : ℝ → ℝ} {θ : ℝ} (hu : u =ᶠ[𝓝 θ] 0) :
    deriv u θ = 0 := by
  rw [Filter.EventuallyEq.deriv_eq hu]
  simp

/-- `Lzero1 u` vanishes away from the support of `u`: at a point `θ ∉ [a,b]` the function
`u` — and hence `deriv u` and `θ' ↦ tan θ' * u θ'` — is eventually zero. -/
lemma Lzero1_eq_zero_of_not_mem {u : ℝ → ℝ} {a b : ℝ}
    (hu : ∀ θ : ℝ, θ ∉ Set.Icc a b → u θ = 0) {θ : ℝ} (hθ : θ ∉ Set.Icc a b) :
    Work.FTS.EllipticEst.Lzero1 u θ = 0 := by
  have hopen : (Set.Icc a b)ᶜ ∈ 𝓝 θ :=
    IsOpen.mem_nhds isClosed_Icc.isOpen_compl hθ
  have hdu : deriv u =ᶠ[𝓝 θ] 0 := by
    filter_upwards [hopen] with t ht
    refine deriv_eq_zero_of_eventuallyEq_zero ?_
    filter_upwards [IsOpen.mem_nhds isClosed_Icc.isOpen_compl ht] with s hs using hu s hs
  have htanu : (fun t : ℝ => Real.tan t * u t) =ᶠ[𝓝 θ] 0 := by
    filter_upwards [hopen] with t ht
    simp [hu t ht]
  simp only [Work.FTS.EllipticEst.Lzero1]
  rw [deriv_eq_zero_of_eventuallyEq_zero hdu, deriv_eq_zero_of_eventuallyEq_zero htanu,
    hu θ hθ]
  ring

/-- If `u` is `C^∞` and supported in `[a,b]` with `0 < a`, `b < π/2`, then
`θ ↦ tan θ * u θ` is `C^∞`: on `[a,b]` (which lies inside `(-π/2, π/2)`) the tangent is
smooth, and off `[a,b]` the product vanishes in a neighbourhood. -/
lemma contDiff_tan_mul_of_support {u : ℝ → ℝ} {a b : ℝ} (ha : 0 < a)
    (hb : b < Real.pi / 2) (hu : ContDiff ℝ Work.Stability.smoothOrder u)
    (hsup : ∀ θ : ℝ, θ ∉ Set.Icc a b → u θ = 0) :
    ContDiff ℝ Work.Stability.smoothOrder (fun θ : ℝ => Real.tan θ * u θ) := by
  rw [contDiff_iff_contDiffAt]
  intro θ
  by_cases hθ : θ ∈ Set.Icc a b
  · have hpos : 0 < θ := lt_of_lt_of_le ha hθ.1
    have hlt : θ < Real.pi / 2 := lt_of_le_of_lt hθ.2 hb
    have hcos : Real.cos θ ≠ 0 := by
      refine ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨?_, hlt⟩)
      linarith [Real.pi_pos, hpos]
    exact (Real.contDiffAt_tan.2 hcos).mul ((contDiff_iff_contDiffAt.mp hu) θ)
  · have hnhds : (Set.Icc a b)ᶜ ∈ 𝓝 θ := IsOpen.mem_nhds isClosed_Icc.isOpen_compl hθ
    refine ContDiffAt.congr_of_eventuallyEq (contDiffAt_const (c := (0 : ℝ))) ?_
    filter_upwards [hnhds] with t ht
    simp [hsup t ht]

/-- `Lzero1` preserves the class `Good a b` (for `0 < a`, `b < π/2`). -/
lemma good_Lzero1 {g : ℝ → ℝ} {a b : ℝ} (ha : 0 < a) (hb : b < Real.pi / 2)
    (hg : Work.FTS.ClassCHon.Good a b g) :
    Work.FTS.ClassCHon.Good a b (Work.FTS.EllipticEst.Lzero1 g) := by
  refine ⟨?_, fun θ hθ => Lzero1_eq_zero_of_not_mem hg.2 hθ⟩
  have hu := hg.1
  have hdu : ContDiff ℝ Work.Stability.smoothOrder (deriv g) :=
    (contDiff_infty_iff_deriv.mp hu).2
  have hddu : ContDiff ℝ Work.Stability.smoothOrder (deriv (deriv g)) :=
    (contDiff_infty_iff_deriv.mp hdu).2
  have hw : ContDiff ℝ Work.Stability.smoothOrder (fun θ : ℝ => Real.tan θ * g θ) :=
    contDiff_tan_mul_of_support ha hb hu hg.2
  have hdw : ContDiff ℝ Work.Stability.smoothOrder
      (deriv (fun θ : ℝ => Real.tan θ * g θ)) :=
    (contDiff_infty_iff_deriv.mp hw).2
  have hsum : ContDiff ℝ Work.Stability.smoothOrder
      (fun θ : ℝ => -(deriv (deriv g) θ) + deriv (fun t : ℝ => Real.tan t * g t) θ
        - 6 * g θ) :=
    (hddu.neg.add hdw).sub (contDiff_const.mul hu)
  exact hsum

theorem Lop_good {g : ℝ → ℝ} {a b : ℝ} (ha : 0 < a) (hb : b < Real.pi / 2)
    (hg : Work.FTS.ClassCHon.Good a b g) :
    ∀ k : ℕ, Work.FTS.ClassCHon.Good a b (Work.FTS.ClassCHon.Lop g k) := by
  intro k
  induction k with
  | zero => simpa using hg
  | succ k ih =>
      rw [Work.FTS.ClassCHon.Lop_succ]
      exact good_Lzero1 ha hb ih

end Work.FTS.ClassCHon
