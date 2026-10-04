/-
# The chart-transfer estimate for a `T` which is only smooth on an open set

`Work.Diff.STE.B3.CSq_period_comp_arg_le_uniform` controls

  `CSq s (fourierCoeff (periodisation of z ↦ f z * u (T z)))`

by `C (1 + CSq s (fourierCoeff u))`, uniformly in the smooth `1`-periodic `u`, but only for a
*globally* smooth `T`.  In the applications (chart transitions of a manifold) one only knows that
`T` is `C^∞` on an open set `U` containing the support of `f` — off `U` its values are junk.

The two ingredients of the present file:

* `exists_bump_open_nhds` — the strengthening of `Work.Diff.STE.D.bump_smul_smooth` which also
  records an *open* set `V` with `K ⊆ V ⊆ U` on which the bump is identically `1`.  (The proof of
  `bump_smul_smooth` produces the bump as `1 - ∏ (1 - φᵢ)` over a cover of `K` by open balls
  `ball xᵢ (r xᵢ/2)`; the bump is `1` on the union `V` of those open balls.)  The open set is
  needed because the injectivity and the invertibility of the Jacobian of `T` — which are
  hypotheses of the transfer estimate — must be transferred to the regularised `x ↦ χ x • T x`.
* `CSq_period_comp_arg_le_of_isOpen` — the estimate itself: the periodisation only ever evaluates
  `T` at points of `Function.support f ⊆ tsupport f ⊆ V`, where the regularised map agrees with
  `T`, so the two periodisations coincide term by term.
-/
import Mathlib
import Submission.Work.Diff.STE.B3.CSq_period_comp_arg_le
import Submission.Work.Diff.STE.B3.CSq_period_comp_arg_le_uniform
import Submission.Work.Diff.STE.D.bump_smul_smooth
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.periodization_contDiff_periodic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open scoped Topology

namespace Work.Diff.STE.B3

/-- **A smooth bump equal to `1` on an open neighbourhood of a compact set.**

For a compact `K` contained in an open set `U` of `ι → ℝ` (`ι` finite) and a function `g` which is
`C^∞` *on* `U`, there are a `C^∞` function `φ` and an *open* set `V` with

* `K ⊆ V ⊆ U`, `φ ≡ 1` on `V`,
* `tsupport φ ⊆ U`,
* the product `x ↦ φ x • g x` is `C^∞` on all of `ι → ℝ`.

This is the version of `Work.Diff.STE.D.bump_smul_smooth` needed to transfer properties of `g`
(the injectivity and the invertibility of the Jacobian, hypotheses of the chart-transfer estimate)
to the regularised product: on the open set `V` the product equals `g` (smoothness and Jacobian
agree there), while the product is globally smooth and vanishes off `U`. -/
theorem exists_bump_open_nhds {ι : Type*} [Fintype ι] [DecidableEq ι]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (K U : Set (ι → ℝ)) (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (g : (ι → ℝ) → F) (hg : ContDiffOn ℝ (⊤ : ℕ∞) g U) :
    ∃ φ : (ι → ℝ) → ℝ, ∃ V : Set (ι → ℝ),
      ContDiff ℝ (⊤ : ℕ∞) φ ∧ IsOpen V ∧ K ⊆ V ∧ V ⊆ U ∧ (∀ x ∈ V, φ x = 1) ∧
      tsupport φ ⊆ U ∧ ContDiff ℝ (⊤ : ℕ∞) (fun x => φ x • g x) := by
  classical
  -- For each point `x` we pick a radius `r x > 0` with `closedBall x (r x) ⊆ U` at points of `K`
  -- (possible since `U` is a neighbourhood of every point of `K ⊆ U`); off `K` the choice is
  -- arbitrary but still positive.
  have hex : ∀ x : ι → ℝ, ∃ r : ℝ, 0 < r ∧ (x ∈ K → Metric.closedBall x r ⊆ U) := by
    intro x
    by_cases hx : x ∈ K
    · obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds (hKU hx))
      refine ⟨ε / 2, half_pos hε, fun _ y hy => hεU ?_⟩
      rw [Metric.mem_ball]
      have h1 := Metric.mem_closedBall.mp hy
      linarith
    · exact ⟨1, one_pos, fun h => absurd h hx⟩
  let r : (ι → ℝ) → ℝ := fun x => Classical.choose (hex x)
  have hr_pos : ∀ x, 0 < r x := fun x => (Classical.choose_spec (hex x)).1
  have hr_tsub : ∀ x ∈ K, Metric.closedBall x (r x) ⊆ U :=
    fun x hx => (Classical.choose_spec (hex x)).2 hx
  -- Cover the compact set `K` by the open balls `ball x (r x / 2)`, `x` ranging over a finite
  -- set `t ⊆ K`.
  have hnhds : ∀ x ∈ K, Metric.ball x (r x / 2) ∈ 𝓝 x :=
    fun x _ => Metric.ball_mem_nhds x (half_pos (hr_pos x))
  obtain ⟨t, htK, hcov⟩ := hK.elim_nhds_subcover (fun x => Metric.ball x (r x / 2)) hnhds
  -- The individual bumps: equal to `1` on `closedBall x (r x / 2)`, supported in
  -- `closedBall x (r x) ⊆ U`.
  let φb : (x : ι → ℝ) → ContDiffBump x :=
    fun x => ⟨r x / 2, r x, half_pos (hr_pos x), by linarith [hr_pos x]⟩
  let φ : (ι → ℝ) → ℝ := fun y => 1 - ∏ x ∈ t, (1 - φb x y)
  have hφ : ContDiff ℝ (⊤ : ℕ∞) φ := by
    show ContDiff ℝ (⊤ : ℕ∞) (fun y => 1 - ∏ x ∈ t, (1 - φb x y))
    refine ContDiff.sub contDiff_const ?_
    refine contDiff_prod (fun x _ => ?_)
    exact ContDiff.sub contDiff_const ((φb x).contDiff (n := ⊤))
  -- The open set on which `φ` is `1`: the union of the (open) inner balls of the cover.
  have hVopen : IsOpen (⋃ x ∈ t, Metric.ball x (r x / 2)) :=
    isOpen_biUnion fun x _ => Metric.isOpen_ball
  have hKV : K ⊆ ⋃ x ∈ t, Metric.ball x (r x / 2) := fun y hy => hcov hy
  have hVU : (⋃ x ∈ t, Metric.ball x (r x / 2)) ⊆ U := by
    intro y hy
    obtain ⟨x, hxt, hyb⟩ : ∃ x ∈ t, y ∈ Metric.ball x (r x / 2) := by
      simpa only [Set.mem_iUnion, exists_prop] using hy
    have hyc : y ∈ Metric.closedBall x (r x) :=
      Metric.mem_closedBall.mpr (by
        have h2 := Metric.mem_ball.mp hyb
        linarith [hr_pos x])
    exact hr_tsub x (htK x hxt) hyc
  have hφone : ∀ y ∈ (⋃ x ∈ t, Metric.ball x (r x / 2)), φ y = 1 := by
    intro y hy
    obtain ⟨x, hxt, hyb⟩ : ∃ x ∈ t, y ∈ Metric.ball x (r x / 2) := by
      simpa only [Set.mem_iUnion, exists_prop] using hy
    have h1 : φb x y = 1 :=
      (φb x).one_of_mem_closedBall (Metric.ball_subset_closedBall hyb)
    show 1 - ∏ x ∈ t, (1 - φb x y) = 1
    rw [Finset.prod_eq_zero hxt (by rw [h1]; ring)]
    ring
  -- The support of `φ` is contained in the union of the topological supports of the bumps:
  -- if none of the factors `1 - φb x` vanishes then the product equals `1`, so `φ = 0`.
  have hsupp : Function.support φ ⊆ ⋃ x ∈ t, tsupport (φb x) := by
    intro y hy
    by_contra hcon
    have hzero : ∀ x ∈ t, φb x y = 0 := by
      intro x hx
      refine image_eq_zero_of_notMem_tsupport ?_
      intro hmem
      exact hcon (by simp only [Set.mem_iUnion, exists_prop]; exact ⟨x, hx, hmem⟩)
    apply hy
    show 1 - ∏ x ∈ t, (1 - φb x y) = 0
    rw [Finset.prod_eq_one (fun x hx => by rw [hzero x hx]; ring)]
    ring
  have hcl : IsClosed (⋃ x ∈ t, tsupport (φb x)) :=
    Set.Finite.isClosed_biUnion t.finite_toSet (fun x _ => isClosed_tsupport _)
  have htsub1 : tsupport φ ⊆ ⋃ x ∈ t, tsupport (φb x) := by
    rw [tsupport]
    exact hcl.closure_subset_iff.mpr hsupp
  have htsub2 : (⋃ x ∈ t, tsupport (φb x)) ⊆ U := by
    intro y hy
    simp only [Set.mem_iUnion, exists_prop] at hy
    obtain ⟨x, hx, hyx⟩ := hy
    have hyx' : y ∈ Metric.closedBall x (r x) := by
      rwa [(φb x).tsupport_eq] at hyx
    exact hr_tsub x (htK x hx) hyx'
  refine ⟨φ, ⋃ x ∈ t, Metric.ball x (r x / 2), hφ, hVopen, hKV, hVU, hφone,
    htsub1.trans htsub2, ?_⟩
  -- Smoothness of `φ • g`: on `U` both factors are smooth at the point, off `U` the product
  -- vanishes on a neighbourhood.
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hy : y ∈ U
  · exact (hφ.contDiffAt).smul (hg.contDiffAt (hU.mem_nhds hy))
  · have hny : y ∉ tsupport φ := fun h => hy (htsub1.trans htsub2 h)
    have hev : φ =ᶠ[𝓝 y] 0 := notMem_tsupport_iff_eventuallyEq.mp hny
    have hev2 : (fun z => φ z • g z) =ᶠ[𝓝 y] (fun _ => (0 : F)) :=
      hev.mono (fun z hz => by simp [hz])
    exact (contDiffAt_const (c := (0 : F))).congr_of_eventuallyEq hev2

theorem CSq_period_comp_arg_le_of_isOpen {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : ℕ) (hs : Fintype.card ι < 2 * s)
    (T : (ι → ℝ) → (ι → ℝ))
    (f : (ι → ℝ) → ℂ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hfsupp : Function.support f ⊆
      Set.pi Set.univ (fun _ : ι => Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)))
    (hK : IsCompact (tsupport f))
    (U : Set (ι → ℝ)) (hU : IsOpen U) (hUf : tsupport f ⊆ U)
    (hT : ∀ z ∈ U, ContDiffAt ℝ (⊤ : ℕ∞) T z)
    (hinj : Set.InjOn T U)
    (hdet : ∀ z ∈ U, (fderiv ℝ T z).det ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : (ι → ℝ) → ℂ),
      ContDiff ℝ (⊤ : ℕ∞) u → Work.Diff.STE.Periodic1 u →
      Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff (fun z => ∑' m : ι → ℤ,
        f (z + Work.Diff.STE.iVec m) * u (T (z + Work.Diff.STE.iVec m))))
        ≤ C * (1 + Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff u)) := by
  classical
  -- `T` is `C^∞` on the whole open set `U` (the hypothesis is pointwise)
  have hTon : ContDiffOn ℝ (⊤ : ℕ∞) T U := fun z hz => (hT z hz).contDiffWithinAt
  -- a bump `φ`, equal to `1` on an open neighbourhood `V` of `tsupport f` contained in `U`,
  -- which regularises `T` to a globally smooth `x ↦ φ x • T x`
  obtain ⟨φ, V, hφsm, hVopen, hKV, hVU, hφone, hφsupp, hφTsm⟩ :=
    exists_bump_open_nhds (tsupport f) U hK hU hUf T hTon
  -- on the *open* set `V` the regularised map agrees with `T`, so it inherits injectivity
  have hinj' : Set.InjOn (fun z => φ z • T z) V := by
    intro x hx y hy hxy
    refine hinj (hVU hx) (hVU hy) ?_
    have h1 : φ x • T x = φ y • T y := hxy
    simpa only [hφone x hx, hφone y hy, one_smul] using h1
  -- and the invertibility of the Jacobian
  have hdet' : ∀ z ∈ V, (fderiv ℝ (fun z => φ z • T z) z).det ≠ 0 := by
    intro z hz
    have hev : (fun w => φ w • T w) =ᶠ[𝓝 z] T := by
      filter_upwards [hVopen.mem_nhds hz] with w hw
      rw [hφone w hw, one_smul]
    rw [hev.fderiv_eq]
    exact hdet z (hVU hz)
  obtain ⟨C, hCnn, hCb⟩ :=
    CSq_period_comp_arg_le_uniform (ι := ι) s hs (fun z => φ z • T z) hφTsm f hf hfsupp
      V hVopen hKV hinj' hdet'
  refine ⟨C, hCnn, fun u hu hup => ?_⟩
  -- the two periodisations agree term by term, because `f (z + m) ≠ 0` forces
  -- `z + m ∈ Function.support f ⊆ tsupport f ⊆ V`, where `T` and `φ • T` coincide
  have hfun : (fun z : ι → ℝ => ∑' m : ι → ℤ,
        f (z + Work.Diff.STE.iVec m) * u (T (z + Work.Diff.STE.iVec m)))
      = (fun z : ι → ℝ => ∑' m : ι → ℤ,
        f (z + Work.Diff.STE.iVec m)
          * u (φ (z + Work.Diff.STE.iVec m) • T (z + Work.Diff.STE.iVec m))) := by
    funext z
    refine tsum_congr fun m => ?_
    by_cases hfm : f (z + Work.Diff.STE.iVec m) = 0
    · rw [hfm, zero_mul, zero_mul]
    · have hmem : z + Work.Diff.STE.iVec m ∈ tsupport f :=
        subset_tsupport f (Function.mem_support.mpr hfm)
      rw [show φ (z + Work.Diff.STE.iVec m) = 1 from hφone _ (hKV hmem), one_smul]
  rw [hfun]
  exact hCb u hu hup

end Work.Diff.STE.B3
