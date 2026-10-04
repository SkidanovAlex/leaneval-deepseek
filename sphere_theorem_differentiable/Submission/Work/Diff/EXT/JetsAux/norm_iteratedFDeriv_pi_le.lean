import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.EXT.JetsAux

open Set

/-- **The iterated Fréchet derivative of a Pi-valued function is the Pi of the iterated Fréchet
derivatives of its components.**

This is proved by writing the (local) Taylor series of each component; on the common open
neighbourhood `U` of `x` on which all components are `C^n` the Taylor series of the Pi-valued
function is the Pi of the componentwise Taylor series (`hasFTaylorSeriesUpToOn_pi`), and
evaluating at `x` gives the claim, since `U` and the componentwise neighbourhoods are open
(so `iteratedFDerivWithin` agrees with `iteratedFDeriv`). -/
theorem iteratedFDeriv_pi_eq
    {ι : Type*} [Fintype ι] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {J : Type*} [NormedAddCommGroup J] [NormedSpace ℝ J]
    (w : ι → E → J) (x : E) (n : ℕ) (hw : ∀ i, ContDiffAt ℝ (⊤ : ℕ∞) (w i) x) :
    iteratedFDeriv ℝ n (fun y : E => fun i => w i y) x
      = ContinuousMultilinearMap.pi (fun i => iteratedFDeriv ℝ n (w i) x) := by
  classical
  -- each component is `C^n` on an open neighbourhood of `x`
  have hloc : ∀ i, ∃ u : Set E, IsOpen u ∧ x ∈ u ∧ ContDiffOn ℝ (n : ℕ∞) (w i) u := by
    intro i
    obtain ⟨u, huo, hxu, hu⟩ :=
      (hw i).contDiffOn' (m := (n : ℕ∞)) (by simp) (by intro h; simp at h)
    exact ⟨u, huo, hxu, by simpa using hu⟩
  choose u huo hxu hu using hloc
  set U : Set E := ⋂ i, u i
  have hUopen : IsOpen U := isOpen_iInter_of_finite huo
  have hxU : x ∈ U := mem_iInter.2 hxu
  -- the Taylor series of the Pi-valued function, on the common neighbourhood `U`
  have hFt : HasFTaylorSeriesUpToOn (n : ℕ∞) (fun y : E => fun i => w i y)
      (fun y m => ContinuousMultilinearMap.pi fun i => iteratedFDerivWithin ℝ m (w i) (u i) y)
      U := by
    refine (hasFTaylorSeriesUpToOn_pi).2 fun i => ?_
    refine ((hu i).ftaylorSeriesWithin (huo i).uniqueDiffOn).mono ?_
    intro y hy
    exact mem_iInter.1 hy i
  have h1 : ContinuousMultilinearMap.pi (fun i => iteratedFDerivWithin ℝ n (w i) (u i) x)
      = iteratedFDerivWithin ℝ n (fun y : E => fun i => w i y) U x :=
    hFt.eq_iteratedFDerivWithin_of_uniqueDiffOn (m := n) le_rfl hUopen.uniqueDiffOn hxU
  have h2 : iteratedFDerivWithin ℝ n (fun y : E => fun i => w i y) U x
      = iteratedFDeriv ℝ n (fun y : E => fun i => w i y) x :=
    iteratedFDerivWithin_of_isOpen n hUopen hxU
  have h3 : ∀ i, iteratedFDerivWithin ℝ n (w i) (u i) x = iteratedFDeriv ℝ n (w i) x :=
    fun i => iteratedFDerivWithin_of_isOpen n (huo i) (hxu i)
  have hfun : (fun i => iteratedFDerivWithin ℝ n (w i) (u i) x)
      = (fun i => iteratedFDeriv ℝ n (w i) x) := funext h3
  calc iteratedFDeriv ℝ n (fun y : E => fun i => w i y) x
      = iteratedFDerivWithin ℝ n (fun y : E => fun i => w i y) U x := h2.symm
    _ = ContinuousMultilinearMap.pi (fun i => iteratedFDerivWithin ℝ n (w i) (u i) x) := h1.symm
    _ = ContinuousMultilinearMap.pi (fun i => iteratedFDeriv ℝ n (w i) x) := by rw [hfun]

/-- **Jet bound for a family of functions into a Pi-type.**  If every component `w i` is `C^∞` at
`x` and its `n`-th iterated Fréchet derivative is bounded by `C`, then the same is true of the
Pi-valued function `y ↦ (fun i => w i y)`, with `C` replaced by `max C 0`. -/
theorem norm_iteratedFDeriv_pi_le
    {ι : Type*} [Fintype ι] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {J : Type*} [NormedAddCommGroup J] [NormedSpace ℝ J]
    (w : ι → E → J) (x : E) (n : ℕ) (hw : ∀ i, ContDiffAt ℝ (⊤ : ℕ∞) (w i) x) {C : ℝ}
    (hC : ∀ i, ‖iteratedFDeriv ℝ n (w i) x‖ ≤ C) :
    ‖iteratedFDeriv ℝ n (fun y : E => fun i => w i y) x‖ ≤ max C 0 := by
  rw [iteratedFDeriv_pi_eq w x n hw, ContinuousMultilinearMap.opNorm_pi]
  exact (pi_norm_le_iff_of_nonneg (le_max_right C 0)).2 fun i => (hC i).trans (le_max_left C 0)

end Work.Diff.EXT.JetsAux
