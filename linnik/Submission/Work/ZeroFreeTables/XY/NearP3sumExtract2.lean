/-
# ZeroFreeTables/XY/NearP3sumExtract2

The single-zero extraction for the near-zero sum `P9.nearP3sum`, in the *window* form of the
minimality hypothesis: every zero `u'` of the `δ`-window already satisfies
`lam ≤ (1 - u'.re) * L`, and `0 < a + lam`.  Under those hypotheses the `P₃`-term at every
window zero is non-negative (`P3Bounds.1`), the argument at a zero outside the window is
multiplied by `nearInd = 0`, and the term at a `zeroMult = 0` point vanishes.  Hence every
summand of `nearP3sum` is non-negative, and the summand at the given window zero `u` -- which
*is* the left-hand side -- is dominated by the whole sum: `nearP3sum` is a `tsum` of a family
supported in the compact box `1 - δ ≤ Re ≤ 1`, `|Im| ≤ |s.im| + δ`, which is finite by
`boxMaxZeroAux.finite_zeroMult_box`.

The proof uses two reusable facts, proved in parallel and imported here:
* `P9.NearP3summandMemBoxGen` -- the support of the summand lies in that box;
* `P9.NearP3summandNonnegWindow` -- the summand is non-negative under window-minimality.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.P3.DefsL
import Submission.Work.ZeroFreeTables.P9.Defs
import Submission.Work.ZeroFreeTables.P3Pos
import Submission.Work.ZeroFreeTables.P9.NearSummandDefs
import Submission.Work.ZeroFreeTables.P9.NearP3summandMemBoxGen
import Submission.Work.ZeroFreeTables.P9.NearP3summandNonnegWindow
import Submission.Work.LinnikAreas.boxMaxZero

namespace Work.ZeroFreeTables.XY

theorem NearP3sumExtract2 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {L a lam δ : ℝ} (hL : 0 < L) (ha : 0 < a) (hδ : 0 < δ) (hα : 0 < a + lam)
    {s u : ℂ} (hmin : ∀ u' : ℂ, Work.LinnikContract.zeroMult χ u' ≠ 0 →
      ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u'‖ ≤ δ → lam ≤ (1 - u'.re) * L)
    (hs : s.re = 1 + a / L) (hu : Work.LinnikContract.zeroMult χ u ≠ 0)
    (hnear : ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ) :
    (Work.LinnikContract.zeroMult χ u : ℝ)
        * (Work.ZeroFreeTables.P3 (((a + lam : ℝ) : ℂ) / ((s - u) * (L : ℂ)))).re
      ≤ Work.ZeroFreeTables.P9.nearP3sum q L χ s a lam δ := by
  classical
  -- `ha` and `hδ` are not needed: the window form of the minimality hypothesis together with
  -- `0 < a + lam` already forces non-negativity of every summand.  (They remain in the
  -- statement, unchanged, as requested.)
  have _ : 0 < a := ha
  have _ : 0 < δ := hδ
  set F : ℂ → ℝ := fun u' => Work.ZeroFreeTables.P9.nearP3summand q L χ s a lam δ u' with hF
  -- 1. every summand is non-negative (window-minimality; `P3Bounds.1`)
  have hnn : ∀ u' : ℂ, 0 ≤ F u' := fun u' =>
    Work.ZeroFreeTables.P9.NearP3summandNonnegWindow χ hL hα hs hmin u'
  -- 2. the support of the summand is contained in a finite box
  set S : Finset ℂ := (Work.LinnikAreas.boxMaxZeroAux.finite_zeroMult_box χ (1 - δ)
    (|s.im| + δ)).toFinset with hS
  have hmemS : ∀ u' : ℂ, u' ∈ S ↔ Work.LinnikContract.zeroMult χ u' ≠ 0 ∧ 1 - δ ≤ u'.re
      ∧ u'.re ≤ 1 ∧ |u'.im| ≤ |s.im| + δ := by
    intro u'
    rw [hS, Set.Finite.mem_toFinset]
    rfl
  have hsupp : ∀ u' : ℂ, u' ∉ S → F u' = 0 := by
    intro u' hu'
    by_contra hne
    rw [hF] at hne
    exact hu' ((hmemS u').mpr (Work.ZeroFreeTables.P9.NearP3summandMemBoxGen χ hne))
  -- 3. `nearP3sum` is the (finitely supported) sum of `F`
  have htsum : Work.ZeroFreeTables.P9.nearP3sum q L χ s a lam δ = ∑' i : ℂ, F i := by
    rw [Work.ZeroFreeTables.P9.nearP3sum_eq_tsum]
  rw [htsum, tsum_eq_sum (s := S) hsupp]
  -- 4. the summand at `u` is the left-hand side, and `u` lies in the box
  have hFu : F u = (Work.LinnikContract.zeroMult χ u : ℝ)
      * (Work.ZeroFreeTables.P3 (((a + lam : ℝ) : ℂ) / ((s - u) * (L : ℂ)))).re := by
    simp only [hF]
    rw [Work.ZeroFreeTables.P9.nearP3summand_eq_P3]
    have hind : Work.ZeroFreeTables.P9.nearInd s δ u = 1 := by
      rw [Work.ZeroFreeTables.P9.nearInd_eq_ite, if_pos hnear]
    rw [hind, mul_one]
    simp only [Complex.ofReal_add]
  rw [← hFu]
  have huS : u ∈ S := by
    rw [hmemS u]
    refine ⟨hu, ?_, ?_, ?_⟩
    · have h1 : |((1 : ℂ) + (s.im : ℂ) * Complex.I - u).re| ≤ δ :=
        le_trans (Complex.abs_re_le_norm _) hnear
      have hre : ((1 : ℂ) + (s.im : ℂ) * Complex.I - u).re = 1 - u.re := by simp
      rw [hre, abs_le] at h1
      linarith [h1.1]
    · exact le_of_lt (Work.LinnikAreas.boxMaxZeroAux.zeroMult_re_lt_one χ hu)
    · have h1 : |((1 : ℂ) + (s.im : ℂ) * Complex.I - u).im| ≤ δ :=
        le_trans (Complex.abs_im_le_norm _) hnear
      have him : ((1 : ℂ) + (s.im : ℂ) * Complex.I - u).im = s.im - u.im := by simp
      rw [him] at h1
      have h3 : |u.im| ≤ |s.im| + |s.im - u.im| := by
        calc |u.im| = |s.im - (s.im - u.im)| := by congr 1; ring
          _ ≤ |s.im| + |s.im - u.im| := abs_sub _ _
      linarith
  -- 5. a single summand is at most the whole (non-negative) sum
  have hle : ∑ u' ∈ ({u} : Finset ℂ), F u' ≤ ∑ u' ∈ S, F u' :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.singleton_subset_iff.mpr huS)
      (fun x _ _ => hnn x)
  simpa using hle

end Work.ZeroFreeTables.XY
