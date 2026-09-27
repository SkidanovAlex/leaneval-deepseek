import Mathlib
import Submission.Work.SimplyConnected.ABS.RegularPieceDefs
import Submission.Work.SimplyConnected.ABS.exists_sector_subset_of_open_convexCone

/-!
# The sector (cone) condition is independent of the atlas chart

`Work.SimplyConnected.ABS.HasSectorBoundary U p` is stated by exhibiting *one* atlas chart `c` around
the frontier point `p` in which `U` avoids a sector (cone) through `c p`.  This module proves that the
condition can be re-established in **any** other atlas chart `d` around `p`:

`Work.Topology.Surface.hasSectorBoundary_transfer_chart`.

This is what makes the sector half of the ABS engulfing usable for a region presented as a finite
union of chart balls *in different charts*: at a frontier point where two balls from two charts meet,
the analysis can be carried out in either chart.

## Why it is true, and why the naive statement fails

The chart transition `nu = c o d^-1` is a local biholomorphism, so it maps directions at `d p`
conformally (i.e. by the invertible real-linear map `b = D nu (d p)`) to directions at `c p`.  The
subtlety is that the hypothesis only says that `U` avoids the **open** cone `C`; points of `U` may
approach `p` along the *boundary rays* of `C`.  Indeed the naive conclusion -- "avoid the cone
`b^-1 C`" -- is **false**: for a transition with a non-trivial second-order term, points of `U`
approaching `p` above a boundary ray of `C` (with the right quadratic correction) have image
directions strictly inside `C`.  What survives is the **strictly smaller** cone

  `C_eta = {h : eta * ‖h‖ < L1 h and eta * ‖h‖ < L2 h}`  (`eta > 0`),

and this is all we need: a cone of positive angle is exactly what the barrier construction consumes.
`C_eta` is open, convex (`‖a x + b y‖ <= a ‖x‖ + b ‖y‖`) and closed under positive scalings, so the
verified `exists_sector_subset_of_open_convexCone` produces the two functionals describing it, and the
little-`o` estimate for `nu` then beats the margin `eta`.

## Contents

* `exists_hasFDerivAt_transition_ne_zero` -- the transition is differentiable at `d p` with a non-zero
  (hence invertible) complex-linear derivative;
* `complexLinear_apply_one_mul` -- an explicit description `b z = z * b 1` of a `ℂ`-linear map;
* `exists_wedge_margin_of_pair` -- a sector strictly inside the cone of a pair of functionals;
* `hasSectorBoundary_transfer_chart` -- the transfer.
-/

open Set Manifold
open scoped Manifold Topology ContDiff

namespace Work.Topology.Surface

/-! ## The transition's derivative -/

/-- **An explicit description of a `ℂ`-linear endomorphism of `ℂ`**: it is multiplication by
`b 1`. -/
theorem complexLinear_apply_one_mul (b : ℂ →L[ℂ] ℂ) (z : ℂ) : b z = z * b 1 := by
  have hI : b Complex.I = Complex.I * b 1 := by
    have h := b.map_smul Complex.I (1 : ℂ)
    simpa using h
  have hz : z = (z.re : ℂ) • (1 : ℂ) + (z.im : ℂ) • (Complex.I : ℂ) := by
    rw [smul_eq_mul, smul_eq_mul, mul_one]
    exact (Complex.re_add_im z).symm
  rw [hz, map_add, map_smul, map_smul, hI, smul_eq_mul, smul_eq_mul]
  rw [← Complex.re_add_im z]
  ring

/-- **The transition `c ∘ d⁻¹` is differentiable at `d p` with a non-zero complex-linear
derivative.**  Both atlas charts are biholomorphic coordinate systems, so the transition is
holomorphic; its derivative is non-zero because the two-sided composite with the inverse transition
is the identity. -/
theorem exists_hasFDerivAt_transition_ne_zero {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    {c d : OpenPartialHomeomorph X ℂ} (hc : c ∈ atlas ℂ X) (hd : d ∈ atlas ℂ X) {p : X}
    (hpc : p ∈ c.source) (hpd : p ∈ d.source) :
    ∃ b : ℂ →L[ℂ] ℂ, b ≠ 0 ∧ HasFDerivAt (fun ζ : ℂ => c (d.symm ζ)) b (d p) := by
  -- both transitions are members of the holomorphic groupoid
  have hG : (d.symm ≫ₕ c) ∈ contDiffGroupoid 1 (modelWithCornersSelf ℂ ℂ) :=
    StructureGroupoid.compatible _ hd hc
  have hG' : (c.symm ≫ₕ d) ∈ contDiffGroupoid 1 (modelWithCornersSelf ℂ ℂ) :=
    StructureGroupoid.compatible _ hc hd
  rw [contDiffGroupoid, mem_groupoid_of_pregroupoid] at hG hG'
  have hcd1 : ContDiffOn ℂ 1 (↑(d.symm ≫ₕ c)) (d.symm ≫ₕ c).source := by
    simpa [contDiffPregroupoid, contMDiffOn_iff_contDiffOn] using hG.1
  have hcd2 : ContDiffOn ℂ 1 (↑(c.symm ≫ₕ d)) (c.symm ≫ₕ d).source := by
    simpa [contDiffPregroupoid, contMDiffOn_iff_contDiffOn] using hG'.1
  have hcd1' : ContDiffOn ℂ 1 (fun ζ : ℂ => c (d.symm ζ)) (d.symm ≫ₕ c).source := by
    refine hcd1.congr ?_
    intro ζ _
    rw [OpenPartialHomeomorph.trans_apply]
  have hcd2' : ContDiffOn ℂ 1 (fun w : ℂ => d (c.symm w)) (c.symm ≫ₕ d).source := by
    refine hcd2.congr ?_
    intro w _
    rw [OpenPartialHomeomorph.trans_apply]
  have hsrc : d p ∈ (d.symm ≫ₕ c).source := by
    rw [OpenPartialHomeomorph.trans_source]
    refine ⟨?_, ?_⟩
    · rw [OpenPartialHomeomorph.symm_source]
      exact d.map_source hpd
    · show d.symm (d p) ∈ c.source
      rw [d.left_inv hpd]
      exact hpc
  have hsrc' : c p ∈ (c.symm ≫ₕ d).source := by
    rw [OpenPartialHomeomorph.trans_source]
    refine ⟨?_, ?_⟩
    · rw [OpenPartialHomeomorph.symm_source]
      exact c.map_source hpc
    · show c.symm (c p) ∈ d.source
      rw [c.left_inv hpc]
      exact hpd
  have h1 : HasFDerivAt (fun ζ : ℂ => c (d.symm ζ))
      (fderiv ℂ (fun ζ : ℂ => c (d.symm ζ)) (d p)) (d p) :=
    (hcd1'.contDiffAt ((d.symm ≫ₕ c).open_source.mem_nhds hsrc)).differentiableAt
      (by norm_num) |>.hasFDerivAt
  have h2 : HasFDerivAt (fun w : ℂ => d (c.symm w))
      (fderiv ℂ (fun w : ℂ => d (c.symm w)) (c p)) (c p) :=
    (hcd2'.contDiffAt ((c.symm ≫ₕ d).open_source.mem_nhds hsrc')).differentiableAt
      (by norm_num) |>.hasFDerivAt
  have hval : (fun ζ : ℂ => c (d.symm ζ)) (d p) = c p := by
    show c (d.symm (d p)) = c p
    rw [d.left_inv hpd]
  have h2' : HasFDerivAt (fun w : ℂ => d (c.symm w))
      (fderiv ℂ (fun w : ℂ => d (c.symm w)) (c p)) ((fun ζ : ℂ => c (d.symm ζ)) (d p)) := by
    rw [hval]; exact h2
  have hcomp : HasFDerivAt
      ((fun w : ℂ => d (c.symm w)) ∘ (fun ζ : ℂ => c (d.symm ζ)))
      ((fderiv ℂ (fun w : ℂ => d (c.symm w)) (c p)).comp
        (fderiv ℂ (fun ζ : ℂ => c (d.symm ζ)) (d p))) (d p) :=
    h2'.comp (d p) h1
  have hid : (fun ζ : ℂ => ζ) =ᶠ[nhds (d p)]
      ((fun w : ℂ => d (c.symm w)) ∘ (fun ζ : ℂ => c (d.symm ζ))) := by
    filter_upwards [((d.symm ≫ₕ c).open_source).mem_nhds hsrc] with ζ hζ
    have h1 : d.symm ζ ∈ c.source := hζ.2
    have h2 : ζ ∈ d.target := by
      rw [← OpenPartialHomeomorph.symm_source]
      exact hζ.1
    simp only [Function.comp_apply]
    rw [c.left_inv h1]
    exact (d.right_inv h2).symm
  have huniq : ((fderiv ℂ (fun w : ℂ => d (c.symm w)) (c p)).comp
        (fderiv ℂ (fun ζ : ℂ => c (d.symm ζ)) (d p))) = ContinuousLinearMap.id ℂ ℂ :=
    HasFDerivAt.unique (HasFDerivAt.congr_of_eventuallyEq hcomp hid)
      (hasFDerivAt_id (d p))
  refine ⟨fderiv ℂ (fun ζ : ℂ => c (d.symm ζ)) (d p), ?_, h1⟩
  intro hb
  have hzero : ((fderiv ℂ (fun w : ℂ => d (c.symm w)) (c p)).comp
        (fderiv ℂ (fun ζ : ℂ => c (d.symm ζ)) (d p))) = 0 := by
    rw [hb, ContinuousLinearMap.comp_zero]
  rw [huniq] at hzero
  have h1' : (ContinuousLinearMap.id ℂ ℂ) (1 : ℂ) = (0 : ℂ →L[ℂ] ℂ) 1 := by rw [hzero]
  rw [ContinuousLinearMap.id_apply, ContinuousLinearMap.zero_apply] at h1'
  exact one_ne_zero h1'

/-! ## A sector strictly inside the cone of a pair of functionals -/

/-- **A sector strictly inside the cone of a pair of functionals.**

Let `A₁ A₂` be non-zero real-linear functionals on `ℂ` whose cones `{A₁ > 0}` and `{A₂ > 0}` meet.
Then there are non-zero functionals `P, Q` spanning a non-empty sector which is *strictly* inside the
cone of `A₁, A₂`, in the quantitative sense that on it both `A₁` and `A₂` dominate `η ‖·‖`:

`0 < P h → 0 < Q h → η ‖h‖ < A₁ h and η ‖h‖ < A₂ h`.

The proof does not need any case distinction: the set `{h : η ‖h‖ < A₁ h and η ‖h‖ < A₂ h}` is an
open convex cone for small `η > 0` (convexity is the triangle inequality), and
`exists_sector_subset_of_open_convexCone` linearises it. -/
theorem exists_wedge_margin_of_pair {A₁ A₂ : ℂ →L[ℝ] ℝ} (_h₁ : A₁ ≠ 0) (_h₂ : A₂ ≠ 0)
    (hw : ∃ w : ℂ, 0 < A₁ w ∧ 0 < A₂ w) :
    ∃ (P Q : ℂ →L[ℝ] ℝ) (η : ℝ), 0 < η ∧ P ≠ 0 ∧ Q ≠ 0 ∧ (∃ w : ℂ, 0 < P w ∧ 0 < Q w) ∧
      ∀ h : ℂ, 0 < P h → 0 < Q h → η * ‖h‖ < A₁ h ∧ η * ‖h‖ < A₂ h := by
  obtain ⟨w₀, hw₁, hw₂⟩ := hw
  have hmin : 0 < min (A₁ w₀) (A₂ w₀) := lt_min hw₁ hw₂
  set η : ℝ := min (A₁ w₀) (A₂ w₀) / (2 * (‖w₀‖ + 1)) with hη
  have hηpos : 0 < η := by rw [hη]; positivity
  have hηw : η * ‖w₀‖ < min (A₁ w₀) (A₂ w₀) := by
    have hfac : ‖w₀‖ / (2 * (‖w₀‖ + 1)) < 1 := by
      rw [div_lt_one (by positivity)]
      linarith [norm_nonneg w₀]
    calc η * ‖w₀‖ = min (A₁ w₀) (A₂ w₀) * (‖w₀‖ / (2 * (‖w₀‖ + 1))) := by
          rw [hη]; ring
      _ < min (A₁ w₀) (A₂ w₀) * 1 := mul_lt_mul_of_pos_left hfac hmin
      _ = min (A₁ w₀) (A₂ w₀) := mul_one _
  have hwitC : η * ‖w₀‖ < A₁ w₀ ∧ η * ‖w₀‖ < A₂ w₀ :=
    ⟨lt_of_lt_of_le hηw (min_le_left _ _), lt_of_lt_of_le hηw (min_le_right _ _)⟩
  set C : Set ℂ := {h : ℂ | η * ‖h‖ < A₁ h ∧ η * ‖h‖ < A₂ h} with hC
  have hopen : IsOpen C := by
    rw [hC]
    exact (isOpen_lt (continuous_const.mul continuous_norm) A₁.continuous).inter
      (isOpen_lt (continuous_const.mul continuous_norm) A₂.continuous)
  have hconv : Convex ℝ C := by
    intro x hx y hy a b ha hb hab
    rw [hC] at hx hy ⊢
    simp only [Set.mem_ofPred_eq] at hx hy ⊢
    rcases eq_or_lt_of_le ha with ha0 | hapos
    · have hb1 : b = 1 := by linarith
      rw [← ha0, zero_smul, zero_add, hb1, one_smul]
      exact hy
    rcases eq_or_lt_of_le hb with hb0 | hbpos
    · have ha1 : a = 1 := by linarith
      rw [← hb0, zero_smul, add_zero, ha1, one_smul]
      exact hx
    have hnorm : ‖a • x + b • y‖ ≤ a * ‖x‖ + b * ‖y‖ := by
      have h1 : ‖a • x + b • y‖ ≤ ‖a • x‖ + ‖b • y‖ := norm_add_le _ _
      rwa [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb] at h1
    have hsum₁ : A₁ (a • x + b • y) = a * A₁ x + b * A₁ y := by
      rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    have hsum₂ : A₂ (a • x + b • y) = a * A₂ x + b * A₂ y := by
      rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    constructor
    · rw [hsum₁]
      have h2 : η * (a * ‖x‖ + b * ‖y‖) < a * A₁ x + b * A₁ y := by
        have h3 : η * (a * ‖x‖ + b * ‖y‖) = a * (η * ‖x‖) + b * (η * ‖y‖) := by ring
        rw [h3]
        exact add_lt_add (mul_lt_mul_of_pos_left hx.1 hapos) (mul_lt_mul_of_pos_left hy.1 hbpos)
      exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hnorm (le_of_lt hηpos)) h2
    · rw [hsum₂]
      have h2 : η * (a * ‖x‖ + b * ‖y‖) < a * A₂ x + b * A₂ y := by
        have h3 : η * (a * ‖x‖ + b * ‖y‖) = a * (η * ‖x‖) + b * (η * ‖y‖) := by ring
        rw [h3]
        exact add_lt_add (mul_lt_mul_of_pos_left hx.2 hapos) (mul_lt_mul_of_pos_left hy.2 hbpos)
      exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hnorm (le_of_lt hηpos)) h2
  have hcone : ∀ w ∈ C, ∀ t : ℝ, 0 < t → t • w ∈ C := by
    intro w hw t ht
    rw [hC] at hw ⊢
    simp only [Set.mem_ofPred_eq] at hw ⊢
    have hnorm : ‖t • w‖ = t * ‖w‖ := by rw [norm_smul, Real.norm_of_nonneg ht.le]
    have hA₁ : A₁ (t • w) = t * A₁ w := by rw [map_smul, smul_eq_mul]
    have hA₂ : A₂ (t • w) = t * A₂ w := by rw [map_smul, smul_eq_mul]
    constructor
    · rw [hA₁, hnorm]
      nlinarith [hw.1, ht]
    · rw [hA₂, hnorm]
      nlinarith [hw.2, ht]
  have hCne : C.Nonempty := ⟨w₀, by rw [hC]; exact hwitC⟩
  obtain ⟨P, Q, hP, hQ, hPQ, hsub⟩ :=
    Work.SimplyConnected.ABS.exists_sector_subset_of_open_convexCone C hopen hconv hcone hCne
  exact ⟨P, Q, η, hηpos, hP, hQ, hPQ, fun h hp hq => hsub h hp hq⟩

/-! ## The transfer -/

/-- **The sector condition transfers to any atlas chart through the frontier point.**

If `U` satisfies the sector condition at `p` in the sense of
`Work.SimplyConnected.ABS.HasSectorBoundary` (i.e. in *some* atlas chart), then it does so in *any*
atlas chart `d` containing `p`: there is a neighbourhood `V ⊆ d.source` of `p`, together with two
non-zero functionals `L₁ L₂ : ℂ →L[ℝ] ℝ` spanning a non-empty sector, such that no point of `U ∩ V`
is mapped by `d` into that sector (measured from `d p`). -/
theorem hasSectorBoundary_transfer_chart {X : Type*} [TopologicalSpace X] [T2Space X]
    [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] {U : Set X} {p : X}
    (h : Work.SimplyConnected.ABS.HasSectorBoundary U p)
    (d : OpenPartialHomeomorph X ℂ) (hd : d ∈ atlas ℂ X) (hpd : p ∈ d.source) :
    ∃ (V : Set X) (L₁ L₂ : ℂ →L[ℝ] ℝ), IsOpen V ∧ p ∈ V ∧ V ⊆ d.source ∧
      L₁ ≠ 0 ∧ L₂ ≠ 0 ∧ (∃ w : ℂ, 0 < L₁ w ∧ 0 < L₂ w) ∧
      ∀ x ∈ U ∩ V, ¬ (0 < L₁ (d x - d p) ∧ 0 < L₂ (d x - d p)) := by
  obtain ⟨c, V₀, A₁, A₂, hc, hV₀o, hpV₀, hV₀sub, hpc, hA₁, hA₂, hwit, havoid⟩ := h
  obtain ⟨b, hbne, hb⟩ := exists_hasFDerivAt_transition_ne_zero hc hd hpc hpd
  -- `b` is multiplication by `b 1 ≠ 0`
  have hb1 : b 1 ≠ 0 := by
    intro h0
    refine hbne (ContinuousLinearMap.ext fun z => ?_)
    rw [complexLinear_apply_one_mul b z, h0, mul_zero]
    simp
  have hbsurj : Function.Surjective b := fun w => ⟨w * (b 1)⁻¹, by
    rw [complexLinear_apply_one_mul b, mul_assoc, inv_mul_cancel₀ hb1, mul_one]⟩
  -- the transported pair of functionals `z ↦ A_i (b z)`
  let M₁ : ℂ →L[ℝ] ℝ := A₁.comp (b.restrictScalars ℝ)
  let M₂ : ℂ →L[ℝ] ℝ := A₂.comp (b.restrictScalars ℝ)
  have hM₁ : M₁ ≠ 0 := by
    intro h0
    refine hA₁ (ContinuousLinearMap.ext fun w => ?_)
    obtain ⟨z, rfl⟩ := hbsurj w
    have hz : M₁ z = 0 := by rw [h0]; simp
    exact hz
  have hM₂ : M₂ ≠ 0 := by
    intro h0
    refine hA₂ (ContinuousLinearMap.ext fun w => ?_)
    obtain ⟨z, rfl⟩ := hbsurj w
    have hz : M₂ z = 0 := by rw [h0]; simp
    exact hz
  obtain ⟨w₀, hw₁, hw₂⟩ := hwit
  obtain ⟨z₀, hz₀⟩ : ∃ z, b z = w₀ := hbsurj w₀
  have hMwit : ∃ z : ℂ, 0 < M₁ z ∧ 0 < M₂ z := by
    refine ⟨z₀, ?_, ?_⟩
    · show 0 < A₁ (b z₀)
      rw [hz₀]; exact hw₁
    · show 0 < A₂ (b z₀)
      rw [hz₀]; exact hw₂
  obtain ⟨P, Q, η, hηpos, hP, hQ, hPQwit, hmargin⟩ :=
    exists_wedge_margin_of_pair hM₁ hM₂ hMwit
  -- the error threshold
  set δ : ℝ := η / (2 * (‖A₁‖ + ‖A₂‖ + 1)) with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; positivity
  have hbd₁ : ‖A₁‖ * δ < η := by
    rw [hδdef, mul_div_assoc']
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * (‖A₁‖ + ‖A₂‖ + 1))]
    nlinarith [norm_nonneg A₁, norm_nonneg A₂, hηpos]
  have hbd₂ : ‖A₂‖ * δ < η := by
    rw [hδdef, mul_div_assoc']
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * (‖A₁‖ + ‖A₂‖ + 1))]
    nlinarith [norm_nonneg A₁, norm_nonneg A₂, hηpos]
  -- the little-`o` estimate for the transition
  have hev : ∀ᶠ ζ in 𝓝 (d p),
      ‖c (d.symm ζ) - c (d.symm (d p)) - b (ζ - d p)‖ ≤ δ * ‖ζ - d p‖ :=
    Asymptotics.isLittleO_iff.mp hb.isLittleO hδpos
  rw [Metric.eventually_nhds_iff] at hev
  obtain ⟨r, hr, hball⟩ := hev
  refine ⟨(d.source ∩ d ⁻¹' Metric.ball (d p) r) ∩ V₀, P, Q, ?_, ?_, ?_, hP, hQ, hPQwit, ?_⟩
  · exact (d.continuousOn.isOpen_inter_preimage d.open_source Metric.isOpen_ball).inter hV₀o
  · refine ⟨⟨hpd, ?_⟩, hpV₀⟩
    show d p ∈ Metric.ball (d p) r
    rw [Metric.mem_ball, dist_self]
    exact hr
  · intro x hx
    exact hx.1.1
  · rintro x ⟨hxU, hxV⟩ ⟨hPz, hQz⟩
    obtain ⟨⟨hxsrc, hxball⟩, hxV₀⟩ := hxV
    have hzd : dist (d x) (d p) < r := Metric.mem_ball.mp hxball
    have herr := hball (y := d x) hzd
    have hdx : d.symm (d x) = x := d.left_inv hxsrc
    have hdp : d.symm (d p) = p := d.left_inv hpd
    set z : ℂ := d x - d p with hzdef
    set e : ℂ := c (d.symm (d x)) - c (d.symm (d p)) - b (d x - d p) with hedef
    have hcx : c x - c p = b z + e := by
      rw [hedef, hdx, hdp, hzdef]; ring
    have hen : ‖e‖ ≤ δ * ‖z‖ := by
      rw [hzdef]; exact herr
    have hmargin' := hmargin z hPz hQz
    have hmem₁ : η * ‖z‖ < A₁ (b z) := hmargin'.1
    have hmem₂ : η * ‖z‖ < A₂ (b z) := hmargin'.2
    have hzne : z ≠ 0 := by
      intro hz0
      rw [hz0, norm_zero, mul_zero] at hmem₁
      simp only [map_zero] at hmem₁
      exact lt_irrefl (0 : ℝ) hmem₁
    have hznorm : 0 < ‖z‖ := norm_pos_iff.mpr hzne
    refine havoid x ⟨hxU, hxV₀⟩ ⟨?_, ?_⟩
    · have hsplit : A₁ (c x - c p) = A₁ (b z) + A₁ e := by rw [hcx, map_add]
      have hbnd : ‖A₁ e‖ ≤ ‖A₁‖ * ‖e‖ := ContinuousLinearMap.le_opNorm A₁ e
      have hbnd' : |A₁ e| ≤ ‖A₁‖ * (δ * ‖z‖) :=
        le_trans (by simpa [Real.norm_eq_abs] using hbnd)
          (mul_le_mul_of_nonneg_left hen (norm_nonneg A₁))
      have hup : A₁ e ≤ ‖A₁‖ * (δ * ‖z‖) := le_trans (le_abs_self _) hbnd'
      have hkey : ‖A₁‖ * (δ * ‖z‖) < η * ‖z‖ := by
        rw [← mul_assoc]
        exact mul_lt_mul_of_pos_right hbd₁ hznorm
      have hlow : -(‖A₁‖ * (δ * ‖z‖)) ≤ A₁ e := neg_le_of_abs_le hbnd'
      rw [hsplit]; linarith
    · have hsplit : A₂ (c x - c p) = A₂ (b z) + A₂ e := by rw [hcx, map_add]
      have hbnd : ‖A₂ e‖ ≤ ‖A₂‖ * ‖e‖ := ContinuousLinearMap.le_opNorm A₂ e
      have hbnd' : |A₂ e| ≤ ‖A₂‖ * (δ * ‖z‖) :=
        le_trans (by simpa [Real.norm_eq_abs] using hbnd)
          (mul_le_mul_of_nonneg_left hen (norm_nonneg A₂))
      have hup : A₂ e ≤ ‖A₂‖ * (δ * ‖z‖) := le_trans (le_abs_self _) hbnd'
      have hkey : ‖A₂‖ * (δ * ‖z‖) < η * ‖z‖ := by
        rw [← mul_assoc]
        exact mul_lt_mul_of_pos_right hbd₂ hznorm
      have hlow : -(‖A₂‖ * (δ * ‖z‖)) ≤ A₂ e := neg_le_of_abs_le hbnd'
      rw [hsplit]; linarith

/-! ## A chart ball read in another chart

The chart ball `chartBall c a ρ` is the sub-level set `{x | u x < 0}` of
`u x = ‖c x - a‖ ^ 2 - ρ ^ 2`.  Read in another atlas chart `d`, its defining function is the
composite of `u` with the transition, and the following lemma records that this composite still has a
*non-zero* derivative at a boundary point of the ball.  This is exactly the input that
`Work.Topology.Surface.hasSectorBoundary_union_of_two_sublevel` consumes, so that a union of chart
balls taken in *different* charts can be analysed in a single chart. -/

/-- **The explicit form of the derivative of a chart ball's defining function, read in another
chart.**  If `b` is the derivative of the transition `c ∘ d⁻¹` at `d p`, then the defining function
`ζ ↦ ‖c (d.symm ζ) - a‖ ^ 2 - ρ ^ 2` of the chart ball has derivative
`2 • ((innerSL ℝ (c p - a)) ∘SL b)` at `d p`. -/
theorem hasFDerivAt_chartBall_sq_sub {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    {c d : OpenPartialHomeomorph X ℂ} {a : ℂ} {ρ : ℝ} {p : X} {b : ℂ →L[ℂ] ℂ}
    (hpd : p ∈ d.source) (hb : HasFDerivAt (fun ζ : ℂ => c (d.symm ζ)) b (d p)) :
    HasFDerivAt (fun ζ : ℂ => ‖c (d.symm ζ) - a‖ ^ 2 - ρ ^ 2)
      ((2 : ℕ) • ((innerSL ℝ) (c p - a) ∘SL (b.restrictScalars ℝ))) (d p) := by
  have hbℝ : HasFDerivAt (fun ζ : ℂ => c (d.symm ζ)) (b.restrictScalars ℝ) (d p) :=
    HasFDerivAt.restrictScalars ℝ hb
  have hTp : (fun ζ : ℂ => c (d.symm ζ)) (d p) = c p := by
    show c (d.symm (d p)) = c p
    rw [d.left_inv hpd]
  have hmain : HasFDerivAt (fun ζ : ℂ => ‖(fun ζ : ℂ => c (d.symm ζ)) ζ - a‖ ^ 2)
      ((2 : ℕ) • ((innerSL ℝ) ((fun ζ : ℂ => c (d.symm ζ)) (d p) - a) ∘SL
        (b.restrictScalars ℝ))) (d p) := (hbℝ.sub_const a).norm_sq
  rw [hTp] at hmain
  exact hmain.sub_const (ρ ^ 2)

/-- **A chart ball read in another chart has a non-zero derivative at a boundary point.**

If `p` lies on the boundary of the chart ball of `c` around `a` of radius `ρ` (i.e. `‖c p - a‖ = ρ`),
then the function `ζ ↦ ‖c (d.symm ζ) - a‖ ^ 2 - ρ ^ 2` (whose sub-level set `{< 0}` is the chart
ball, read in the chart `d`) has a non-zero derivative at `d p`. -/
theorem exists_hasFDerivAt_chartBall_sq_sub {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    {c d : OpenPartialHomeomorph X ℂ} (hc : c ∈ atlas ℂ X) (hd : d ∈ atlas ℂ X)
    {a : ℂ} {ρ : ℝ} (hρ : 0 < ρ) {p : X} (hpc : p ∈ c.source) (hpd : p ∈ d.source)
    (hbd : ‖c p - a‖ = ρ) :
    ∃ L : ℂ →L[ℝ] ℝ, L ≠ 0 ∧
      HasFDerivAt (fun ζ : ℂ => ‖c (d.symm ζ) - a‖ ^ 2 - ρ ^ 2) L (d p) := by
  obtain ⟨b, hbne, hb⟩ := exists_hasFDerivAt_transition_ne_zero hc hd hpc hpd
  have hb1 : b 1 ≠ 0 := by
    intro h0
    refine hbne (ContinuousLinearMap.ext fun z => ?_)
    rw [complexLinear_apply_one_mul b z, h0, mul_zero]
    simp
  have hbsurj : Function.Surjective b := fun w => ⟨w * (b 1)⁻¹, by
    rw [complexLinear_apply_one_mul b, mul_assoc, inv_mul_cancel₀ hb1, mul_one]⟩
  refine ⟨_, ?_, hasFDerivAt_chartBall_sq_sub hpd hb⟩
  intro h0
  obtain ⟨z, hz⟩ : ∃ z : ℂ, b z = c p - a := hbsurj (c p - a)
  have hz' : ((2 : ℕ) • ((innerSL ℝ) (c p - a) ∘SL (b.restrictScalars ℝ))) z = 0 := by
    rw [h0]; simp
  have hz'' : (2 : ℝ) * inner ℝ (c p - a) (b z) = 0 := by
    have := hz'
    rw [smul_apply, ContinuousLinearMap.comp_apply, innerSL_apply_apply,
      nsmul_eq_mul] at this
    simpa using this
  rw [hz, real_inner_self_eq_norm_sq] at hz''
  have hnormpos : 0 < ‖c p - a‖ := by rw [hbd]; exact hρ
  nlinarith [hz'']

end Work.Topology.Surface
