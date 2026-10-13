import Mathlib
import Submission.Work.WilG4c.YPullback
import Submission.Work.WilG4c.LipOnCubeOfBound

namespace Work.WilkG4c

/-- The open cube of `ℝ^N` is open.  (Local copy of `Work.WilG4c.isOpen_openCube`, to avoid
importing the covering step of the per-cell engine just for this one line.) -/
private lemma isOpen_openCube_local (N : ℕ) : IsOpen (WilkiesDesign.openCube N) := by
  have h : WilkiesDesign.openCube N
      = Set.pi Set.univ (fun _ : Fin N => Set.Ioo (0 : ℝ) 1) := by
    ext t
    simp [WilkiesDesign.openCube]
  rw [h]
  exact isOpen_set_pi Set.finite_univ (fun _ _ => isOpen_Ioo)

set_option linter.unusedVariables false in
theorem YPullbackBound {k p n r : ℕ} (F : Work.WilkG4c.Family k p (n+1))
    (φ : Work.WilkG4c.ChartTuple (p+1) n) (Λ : Set (Fin p → ℝ)) (hr : 1 ≤ r)
    (hcube : ∀ l ∈ Λ, ∀ s ∈ Work.WilkG4c.I, ∀ t ∈ WilkiesDesign.openCube n,
      (fun j => φ j (Fin.snoc l s) t) ∈ WilkiesDesign.openCube n)
    (hsmooth : ∀ i, ∀ l ∈ Λ, ∀ s ∈ Work.WilkG4c.I,
      ContDiffOn ℝ r (fun t => F i l (Fin.cons s (fun j => φ j (Fin.snoc l s) t)))
        (WilkiesDesign.openCube n))
    (hnorm : ∀ i, ∀ l ∈ Λ, ∀ s ∈ Work.WilkG4c.I, ∀ m, m ≤ r → ∀ t ∈ WilkiesDesign.openCube n,
      ‖iteratedFDeriv ℝ m (fun t => F i l (Fin.cons s (fun j => φ j (Fin.snoc l s) t))) t‖ ≤ 1) :
    (∀ i, ∀ l ∈ Λ, ∀ x ∈ Work.WilkG4c.I, ∀ m, m ≤ r → ∀ y ∈ WilkiesDesign.openCube n,
        ‖iteratedFDeriv ℝ m (Work.WilkG4c.slice (Work.WilkG4c.yPullback F φ i l) x) y‖ ≤ 1) ∧
      (∀ i, ∀ l ∈ Λ, ∀ s ∈ Work.WilkG4c.I, ∀ u ∈ WilkiesDesign.openCube n,
        ∀ u' ∈ WilkiesDesign.openCube n,
        |Work.WilkG4c.yPullback F φ i l (Fin.cons s u) -
          Work.WilkG4c.yPullback F φ i l (Fin.cons s u')| ≤ dist u u') := by
  constructor
  · -- Part 1: the `y`-slices of the pullback are the `s`-fibre slices of `F` composed with the
    -- chart `φ`; the hypothesis `hnorm` is exactly the desired bound, transferred by
    -- `slice_yPullback`.
    intro i l hl x hx m hm y hy
    rw [Work.WilkG4c.slice_yPullback]
    exact hnorm i l hl x hx m hm y hy
  · -- Part 2: fix `s ∈ I` and read the `s`-fibre of the pullback as the single function
    -- `g w = F i l (s, φ(...)(w))` on `ℝⁿ`, which is `C¹` on the open cube with
    -- `‖fderiv g‖ ≤ 1` there; the mean value inequality on the convex cube gives the bound.
    intro i l hl s hs u hu u' hu'
    rw [Work.WilkG4c.yPullback_cons F φ i l s u, Work.WilkG4c.yPullback_cons F φ i l s u']
    set g : (Fin n → ℝ) → ℝ :=
      fun w => F i l (Fin.cons s (fun j => φ j (Fin.snoc l s) w)) with hg
    change |g u - g u'| ≤ dist u u'
    have hCD1 : ContDiffOn ℝ (1 : ℕ) g (WilkiesDesign.openCube n) :=
      (hsmooth i l hl s hs).of_le (by exact_mod_cast hr)
    have hdiff : ∀ w ∈ WilkiesDesign.openCube n, DifferentiableAt ℝ g w := by
      intro w hw
      exact (hCD1.contDiffAt ((isOpen_openCube_local n).mem_nhds hw)).differentiableAt
        (by norm_num)
    have hbound : ∀ w ∈ WilkiesDesign.openCube n, ‖fderiv ℝ g w‖ ≤ 1 := by
      intro w hw
      rw [← norm_iteratedFDeriv_one g]
      exact hnorm i l hl s hs 1 hr w hw
    have hmvt := Convex.norm_image_sub_le_of_norm_fderiv_le hdiff hbound
      (Work.WilG4c.convex_openCube n) hu' hu
    simpa [dist_eq_norm, Real.norm_eq_abs] using hmvt

end Work.WilkG4c
