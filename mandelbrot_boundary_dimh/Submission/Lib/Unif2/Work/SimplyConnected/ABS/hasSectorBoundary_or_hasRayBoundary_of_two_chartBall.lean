import Mathlib
import Submission.Lib.Unif2.Work.SimplyConnected.ABS.RegularPieceDefs
import Submission.Lib.Unif2.Work.SimplyConnected.ABS.ray_boundary_barrier

/-!
# The sector/ray alternative at a frontier point of a union of two chart balls

This module proves `Work.SimplyConnected.ABS.hasSectorBoundary_or_hasRayBoundary_of_two_chartBall`:
if `φ` is a chart of a Riemann surface `X` and `c₁ c₂ : ℂ`, `ρ₁ ρ₂ > 0` are such that the closed
balls `closedBall cᵢ ρᵢ` lie in the target of `φ`, then every frontier point of
`U = φ.symm '' ball c₁ ρ₁ ∪ φ.symm '' ball c₂ ρ₂` either satisfies the *sector* condition
`HasSectorBoundary U p` or the *ray* condition `HasRayBoundary U p`.

## The mathematics

Write `A = ball c₁ ρ₁`, `B = ball c₂ ρ₂`.  The chart `φ` identifies `U` with `A ∪ B` near any of
its frontier points `p`, and `x₀ = φ p` lies in `(cl A ∪ cl B) ∖ (A ∪ B)`.

* If `x₀ ∉ cl B` (or symmetrically `x₀ ∉ cl A`), then near `x₀` the region is a disc through `x₀`,
  which lies in the half plane `{z : Re (conj u (z - x₀)) < 0}`, `u = (x₀ - c₁)/ρ₁` the outward
  unit normal.  Hence the *half plane* condition holds, which is the sector condition with
  `L₁ = L₂`.
* If `x₀ ∈ ∂A ∩ ∂B`, put `u = (x₀ - c₁)/ρ₁`, `v = (x₀ - c₂)/ρ₂`, both unit vectors, so that
  `A ⊆ {Re (conj u (z - x₀)) < 0}` and `B ⊆ {Re (conj v (z - x₀)) < 0}`.  If `u ≠ ±v` the two open
  half planes have a common open wedge, which `U` avoids (sector condition, `L₁ = Re (conj u ·)`,
  `L₂ = Re (conj v ·)`).  If `u = v` both discs lie in one half plane, and if `u = -v` the two
  boundary circles are tangent to each other, the union leaves the *ray* through `x₀` perpendicular
  to the line of centres free, giving the ray condition with `d = i u`.
-/

namespace Work.SimplyConnected.ABS

open Set Metric
open scoped Topology ComplexConjugate

set_option linter.unusedSectionVars false

noncomputable section

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- The norm of a real number seen in `ℂ`. -/
private lemma norm_ofReal_complex (r : ℝ) : ‖(r:ℂ)‖ = |r| := RCLike.norm_ofReal r

/-! ### The linear functionals `z ↦ Re (conj u * z)` -/

/-- The real-linear functional `z ↦ Re (conj u * z)` (the scalar product with `u`). -/
private def reConjCLM (u : ℂ) : ℂ →L[ℝ] ℝ :=
  Complex.reCLM.comp (ContinuousLinearMap.mul ℝ ℂ (conj u))

@[simp] private lemma reConjCLM_apply (u z : ℂ) : reConjCLM u z = (conj u * z).re := rfl

private lemma reConjCLM_ne_zero {u : ℂ} (hu : ‖u‖ = 1) : reConjCLM u ≠ 0 := by
  intro h
  have h1 : reConjCLM u u = 1 := by
    rw [reConjCLM_apply, Complex.conj_mul', hu]
    norm_num
  rw [h] at h1
  simp at h1

private lemma reConjCLM_self_pos {u : ℂ} (hu : ‖u‖ = 1) : 0 < reConjCLM u u := by
  rw [reConjCLM_apply, Complex.conj_mul', hu]
  norm_num

/-! ### Plane lemmas: a disc through `x₀` lies in a half plane; two tangent discs leave a ray free -/

/-- **A disc through `x₀` lies in a half plane.**  If `x₀` is on the boundary of the disc
`ball c ρ`, then with `u = (x₀ - c)/ρ` the whole disc lies in `{z : Re (conj u (z - x₀)) < 0}`. -/
private lemma disc_re_neg {c x₀ : ℂ} {ρ : ℝ} (hρ : 0 < ρ) (hd : dist x₀ c = ρ) :
    ∀ z ∈ Metric.ball c ρ, (conj ((ρ:ℂ)⁻¹ * (x₀ - c)) * (z - x₀)).re < 0 := by
  intro z hz
  have hz' : ‖z - c‖ < ρ := by
    have h := Metric.mem_ball.mp hz
    rwa [Complex.dist_eq] at h
  have hw : ‖x₀ - c‖ = ρ := by rw [← Complex.dist_eq]; exact hd
  have hquad : (conj (x₀ - c) * (z - x₀)).re
      = (conj (x₀ - c) * (z - c)).re - ρ^2 := by
    have h1 : z - x₀ = (z - c) - (x₀ - c) := by ring
    rw [h1, mul_sub, Complex.sub_re, sub_right_inj]
    rw [Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re, hw]
  have hbound : (conj (x₀ - c) * (z - c)).re ≤ ρ * ‖z - c‖ := by
    calc (conj (x₀ - c) * (z - c)).re
        ≤ ‖conj (x₀ - c) * (z - c)‖ := Complex.re_le_norm _
      _ = ‖x₀ - c‖ * ‖z - c‖ := by rw [Complex.norm_mul, Complex.norm_conj]
      _ = ρ * ‖z - c‖ := by rw [hw]
  have hmain : (conj (x₀ - c) * (z - x₀)).re < 0 := by
    rw [hquad]; nlinarith
  have hconj : conj ((ρ:ℂ)⁻¹ * (x₀ - c))
      = ((ρ⁻¹ : ℝ) : ℂ) * conj (x₀ - c) := by
    rw [map_mul, ← Complex.ofReal_inv, Complex.conj_ofReal]
  rw [hconj, mul_assoc, Complex.re_ofReal_mul]
  exact mul_neg_of_pos_of_neg (inv_pos.mpr hρ) hmain

private lemma abs_le_norm_add_mul_I (a t : ℝ) : |a| ≤ ‖(a:ℂ) + (t:ℂ)*Complex.I‖ := by
  have hsq : ‖(a:ℂ) + (t:ℂ)*Complex.I‖^2 = a^2 + t^2 := by
    rw [Complex.sq_norm, Complex.normSq_add_mul_I]
  have h1 : ‖(a:ℂ) + (t:ℂ)*Complex.I‖ = Real.sqrt (a^2 + t^2) := by
    rw [← hsq, Real.sqrt_sq (norm_nonneg _)]
  rw [h1, ← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg t])

private lemma self_le_norm_sub_mul_I {a t : ℝ} (ha : 0 ≤ a) : a ≤ ‖(t:ℂ) * Complex.I - (a:ℂ)‖ := by
  have h : (t:ℂ) * Complex.I - (a:ℂ) = ((-a : ℝ) : ℂ) + (t:ℂ) * Complex.I := by
    push_cast; ring
  rw [h]
  have := abs_le_norm_add_mul_I (-a) t
  rwa [abs_neg, abs_of_nonneg ha] at this

/-- **Two discs tangent at `x₀` leave the perpendicular ray free.**  If `x₀` is on both boundary
circles and lies on opposite sides of the two centres (`x₀ - c₁ = ρ₁ u`, `x₀ - c₂ = -ρ₂ u` with
`‖u‖ = 1`), then the ray through `x₀` in the direction `i u` misses both discs. -/
private lemma ray_notMem {c₁ c₂ x₀ u : ℂ} {ρ₁ ρ₂ : ℝ} (h₂ : 0 < ρ₂)
    (hu : ‖u‖ = 1) (hc₁ : x₀ - c₁ = (ρ₁ : ℂ) * u) (hc₂ : x₀ - c₂ = -((ρ₂ : ℂ) * u)) :
    ∀ t : ℝ, 0 ≤ t → x₀ + t • (Complex.I * u) ∉ Metric.ball c₁ ρ₁ ∧
      x₀ + t • (Complex.I * u) ∉ Metric.ball c₂ ρ₂ := by
  intro t _ht
  have hsm : x₀ + t • (Complex.I * u) = x₀ + (t:ℂ) * (Complex.I * u) := by
    rw [Complex.real_smul]
  constructor
  · intro hmem
    have hlt : ‖x₀ + t • (Complex.I * u) - c₁‖ < ρ₁ := by
      simpa [Complex.dist_eq] using Metric.mem_ball.mp hmem
    have heq : x₀ + t • (Complex.I * u) - c₁ = ((ρ₁:ℂ) + (t:ℂ) * Complex.I) * u := by
      rw [hsm]; linear_combination hc₁
    have hge : ρ₁ ≤ ‖x₀ + t • (Complex.I * u) - c₁‖ := by
      rw [heq, Complex.norm_mul, hu, mul_one]
      exact le_trans (le_abs_self ρ₁) (abs_le_norm_add_mul_I ρ₁ t)
    linarith
  · intro hmem
    have hlt : ‖x₀ + t • (Complex.I * u) - c₂‖ < ρ₂ := by
      simpa [Complex.dist_eq] using Metric.mem_ball.mp hmem
    have heq : x₀ + t • (Complex.I * u) - c₂ = ((t:ℂ) * Complex.I - (ρ₂:ℂ)) * u := by
      rw [hsm]; linear_combination hc₂
    have hge : ρ₂ ≤ ‖x₀ + t • (Complex.I * u) - c₂‖ := by
      rw [heq, Complex.norm_mul, hu, mul_one]
      exact self_le_norm_sub_mul_I (le_of_lt h₂)
    linarith

/-- If a unit complex number is not `-1`, then `1 + Re z > 0`. -/
private lemma one_add_re_pos {z : ℂ} (hz : ‖z‖ = 1) (hne : z ≠ -1) : 0 < 1 + z.re := by
  have hsq : z.re ^ 2 + z.im ^ 2 = 1 := by
    have h : Complex.normSq z = (1:ℝ)^2 := by rw [Complex.normSq_eq_norm_sq, hz]
    rw [Complex.normSq_apply] at h
    linarith
  by_contra hcon
  push Not at hcon
  have hre : z.re = -1 := by nlinarith
  have him : z.im = 0 := by
    have h2 : z.im ^ 2 = 0 := by rw [hre] at hsq; nlinarith
    exact sq_eq_zero_iff.mp h2
  exact hne (Complex.ext hre (by simpa using him))

/-- **Two distinct half planes through the origin have a common open wedge**: if `u ≠ -v` are unit
vectors, the open set `{w : 0 < Re (conj u w) ∧ 0 < Re (conj v w)}` is non-empty. -/
private lemma exists_wedge_witness {u v : ℂ} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : u ≠ -v) :
    ∃ w : ℂ, 0 < (conj u * w).re ∧ 0 < (conj v * w).re := by
  have hne : conj u * v ≠ -1 := by
    intro h
    apply huv
    have hconj : u * conj v = -1 := by
      simpa [map_mul] using congrArg conj h
    have hmm : u * conj v * v = -1 * v := by rw [hconj]
    have hvv : conj v * v = 1 := by rw [Complex.conj_mul', hv]; norm_num
    rw [mul_assoc, hvv, mul_one] at hmm
    simpa using hmm
  have hnorm : ‖conj u * v‖ = 1 := by rw [Complex.norm_mul, Complex.norm_conj, hu, hv, one_mul]
  refine ⟨u + v, ?_, ?_⟩
  · have h : (conj u * (u + v)).re = 1 + (conj u * v).re := by
      rw [mul_add, Complex.add_re, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re, hu]
      norm_num
    rw [h]
    exact one_add_re_pos hnorm hne
  · have h : (conj v * (u + v)).re = 1 + (conj u * v).re := by
      have hsym : conj v * u = conj (conj u * v) := by rw [map_mul, Complex.conj_conj, mul_comm]
      rw [mul_add, Complex.add_re, hsym, Complex.conj_re, Complex.conj_mul', ← Complex.ofReal_pow,
        Complex.ofReal_re, hv]
      norm_num
      ring
    rw [h]
    exact one_add_re_pos hnorm hne

/-! ### Chart bookkeeping -/

/-- Membership in `φ.symm '' W` in terms of the chart coordinates, for `W` inside the target. -/
private lemma symm_image_mem {φ : OpenPartialHomeomorph X ℂ} {W : Set ℂ} (hW : W ⊆ φ.target) {x : X} :
    x ∈ φ.symm '' W ↔ x ∈ φ.source ∧ φ x ∈ W := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨φ.symm.map_source (hW hy), by rw [φ.right_inv (hW hy)]; exact hy⟩
  · rintro ⟨hxs, hxW⟩
    exact ⟨φ x, hxW, φ.left_inv hxs⟩

/-- The closure of the image of a disc of radius `ρ` whose closure lies in the target is contained in
the image of the closed disc. -/
private lemma closure_symm_image_ball {φ : OpenPartialHomeomorph X ℂ} {c : ℂ} {ρ : ℝ}
    (hsub : Metric.closedBall c ρ ⊆ φ.target) :
    closure (φ.symm '' Metric.ball c ρ) ⊆ φ.symm '' Metric.closedBall c ρ := by
  have himg : IsCompact (φ.symm '' Metric.closedBall c ρ) :=
    IsCompact.image_of_continuousOn (isCompact_closedBall c ρ) (φ.continuousOn_symm.mono hsub)
  exact closure_minimal (Set.image_mono Metric.ball_subset_closedBall) himg.isClosed

/-! ### The local alternatives -/

/-- **One disc, one far disc**: if `x₀` is on the boundary of `ball c ρ` and is not in
`closedBall c' ρ'`, then the union of the two chart discs satisfies the sector condition at
`φ.symm x₀` (witnessed by the half plane through `x₀` containing the first disc). -/
private lemma sector_of_one_ball {φ : OpenPartialHomeomorph X ℂ} (hφ : φ ∈ atlas ℂ X) {c c' : ℂ}
    {ρ ρ' : ℝ} (hρ : 0 < ρ) (hT : Metric.closedBall c ρ ⊆ φ.target)
    (hT' : Metric.closedBall c' ρ' ⊆ φ.target) {x₀ : ℂ} (hx₀ : x₀ ∈ Metric.sphere c ρ)
    (hfar : x₀ ∉ Metric.closedBall c' ρ') :
    HasSectorBoundary ((φ.symm '' Metric.ball c ρ) ∪ (φ.symm '' Metric.ball c' ρ'))
      (φ.symm x₀) := by
  have hx₀T : x₀ ∈ φ.target := hT (Metric.sphere_subset_closedBall hx₀)
  have hd : dist x₀ c = ρ := Metric.mem_sphere.mp hx₀
  have hdist : ρ' < dist x₀ c' := lt_of_not_ge fun h => hfar (Metric.mem_closedBall.mpr h)
  obtain ⟨r₁, hr₁, hr₁T⟩ := Metric.isOpen_iff.mp φ.open_target x₀ hx₀T
  obtain ⟨r, hr, hrT, hrfar⟩ : ∃ r > 0, Metric.ball x₀ r ⊆ φ.target ∧
      ∀ z ∈ Metric.ball x₀ r, z ∉ Metric.closedBall c' ρ' := by
    refine ⟨min (dist x₀ c' - ρ') r₁, lt_min (by linarith) hr₁, ?_, ?_⟩
    · exact (Metric.ball_subset_ball (min_le_right _ _)).trans hr₁T
    · intro z hz hz'
      have h1 : dist x₀ z < min (dist x₀ c' - ρ') r₁ := by
        have := Metric.mem_ball.mp hz
        rwa [dist_comm] at this
      have h2 : dist z c' ≤ ρ' := Metric.mem_closedBall.mp hz'
      have h3 : dist x₀ c' ≤ dist x₀ z + dist z c' := dist_triangle _ _ _
      have h4 : min (dist x₀ c' - ρ') r₁ ≤ dist x₀ c' - ρ' := min_le_left _ _
      linarith
  have hnorm : ‖x₀ - c‖ = ρ := by rw [← Complex.dist_eq]; exact hd
  set u : ℂ := (ρ:ℂ)⁻¹ * (x₀ - c) with hu_def
  have hu : ‖u‖ = 1 := by
    rw [hu_def, norm_mul, norm_inv, norm_ofReal_complex, abs_of_pos hρ, hnorm,
      inv_mul_cancel₀ (ne_of_gt hρ)]
  refine ⟨φ, φ.symm '' Metric.ball x₀ r, reConjCLM u, reConjCLM u, hφ,
    φ.isOpen_image_symm_of_subset_target Metric.isOpen_ball hrT,
    ⟨x₀, Metric.mem_ball_self hr, rfl⟩, ?_, ?_, reConjCLM_ne_zero hu, reConjCLM_ne_zero hu,
    ⟨u, reConjCLM_self_pos hu, reConjCLM_self_pos hu⟩, ?_⟩
  · rintro y ⟨z, hz, rfl⟩
    exact φ.symm.map_source (hrT (Metric.mem_ball.mp hz))
  · exact φ.symm.map_source hx₀T
  · rintro x ⟨hxU, hxV⟩
    obtain ⟨-, hxball⟩ := (symm_image_mem hrT).mp hxV
    have hxφ : φ x ∈ Metric.ball c ρ := by
      rcases hxU with h | h
      · exact ((symm_image_mem (Metric.ball_subset_closedBall.trans hT)).mp h).2
      · exact absurd (Metric.ball_subset_closedBall
          ((symm_image_mem (Metric.ball_subset_closedBall.trans hT')).mp h).2)
          (hrfar (φ x) hxball)
    have hneg : reConjCLM u (φ x - x₀) < 0 := by
      rw [reConjCLM_apply]
      exact disc_re_neg hρ hd (φ x) hxφ
    rw [φ.right_inv hx₀T]
    intro hcon
    exact absurd hcon.1 (not_lt.mpr (le_of_lt hneg))

/-- **Two discs through `x₀`**: if `x₀` lies on the boundary circles of both `ball c₁ ρ₁` and
`ball c₂ ρ₂`, then the union of the two chart discs satisfies the sector condition or the ray
condition at `φ.symm x₀`. -/
private lemma sector_or_ray_of_two_balls {φ : OpenPartialHomeomorph X ℂ} (hφ : φ ∈ atlas ℂ X)
    {c₁ c₂ : ℂ} {ρ₁ ρ₂ : ℝ} (h₁ : 0 < ρ₁) (h₂ : 0 < ρ₂)
    (hT₁ : Metric.closedBall c₁ ρ₁ ⊆ φ.target) (hT₂ : Metric.closedBall c₂ ρ₂ ⊆ φ.target)
    {x₀ : ℂ} (hx₁ : x₀ ∈ Metric.sphere c₁ ρ₁) (hx₂ : x₀ ∈ Metric.sphere c₂ ρ₂) :
    HasSectorBoundary ((φ.symm '' Metric.ball c₁ ρ₁) ∪ (φ.symm '' Metric.ball c₂ ρ₂))
        (φ.symm x₀) ∨
      HasRayBoundary ((φ.symm '' Metric.ball c₁ ρ₁) ∪ (φ.symm '' Metric.ball c₂ ρ₂))
        (φ.symm x₀) := by
  have hx₁T : x₀ ∈ φ.target := hT₁ (Metric.sphere_subset_closedBall hx₁)
  have hd₁ : dist x₀ c₁ = ρ₁ := Metric.mem_sphere.mp hx₁
  have hd₂ : dist x₀ c₂ = ρ₂ := Metric.mem_sphere.mp hx₂
  have hnc₁ : ‖x₀ - c₁‖ = ρ₁ := by rw [← Complex.dist_eq]; exact hd₁
  have hnc₂ : ‖x₀ - c₂‖ = ρ₂ := by rw [← Complex.dist_eq]; exact hd₂
  set u : ℂ := (ρ₁:ℂ)⁻¹ * (x₀ - c₁) with hu_def
  set v : ℂ := (ρ₂:ℂ)⁻¹ * (x₀ - c₂) with hv_def
  have hu : ‖u‖ = 1 := by
    rw [hu_def, norm_mul, norm_inv, norm_ofReal_complex, abs_of_pos h₁, hnc₁,
      inv_mul_cancel₀ (ne_of_gt h₁)]
  have hv : ‖v‖ = 1 := by
    rw [hv_def, norm_mul, norm_inv, norm_ofReal_complex, abs_of_pos h₂, hnc₂,
      inv_mul_cancel₀ (ne_of_gt h₂)]
  have hρ₁0 : (ρ₁:ℂ) ≠ 0 := by exact_mod_cast ne_of_gt h₁
  have hρ₂0 : (ρ₂:ℂ) ≠ 0 := by exact_mod_cast ne_of_gt h₂
  have hcu : (ρ₁:ℂ) * u = x₀ - c₁ := by
    rw [hu_def, ← mul_assoc, mul_inv_cancel₀ hρ₁0, one_mul]
  have hcv : (ρ₂:ℂ) * v = x₀ - c₂ := by
    rw [hv_def, ← mul_assoc, mul_inv_cancel₀ hρ₂0, one_mul]
  have hsrc : φ.symm x₀ ∈ φ.source := φ.symm.map_source hx₁T
  have hφp : φ (φ.symm x₀) = x₀ := φ.right_inv hx₁T
  have hmem₁ : ∀ {x : X}, x ∈ φ.symm '' Metric.ball c₁ ρ₁ ↔
      x ∈ φ.source ∧ φ x ∈ Metric.ball c₁ ρ₁ :=
    fun {x} => symm_image_mem (Metric.ball_subset_closedBall.trans hT₁)
  have hmem₂ : ∀ {x : X}, x ∈ φ.symm '' Metric.ball c₂ ρ₂ ↔
      x ∈ φ.source ∧ φ x ∈ Metric.ball c₂ ρ₂ :=
    fun {x} => symm_image_mem (Metric.ball_subset_closedBall.trans hT₂)
  by_cases huv : u = v
  · left
    refine ⟨φ, φ.source, reConjCLM u, reConjCLM u, hφ, φ.open_source, hsrc, ?_, hsrc,
      reConjCLM_ne_zero hu, reConjCLM_ne_zero hu,
      ⟨u, reConjCLM_self_pos hu, reConjCLM_self_pos hu⟩, ?_⟩
    · intro y hy; exact hy
    · rintro x ⟨hxU, -⟩
      rw [hφp]
      have hneg : reConjCLM u (φ x - x₀) < 0 := by
        rcases hxU with h | h
        · rw [reConjCLM_apply]
          exact disc_re_neg h₁ hd₁ (φ x) (hmem₁.mp h).2
        · rw [reConjCLM_apply]
          have hu' : u = (ρ₂:ℂ)⁻¹ * (x₀ - c₂) := by rw [← hv_def]; exact huv
          rw [hu']
          exact disc_re_neg h₂ hd₂ (φ x) (hmem₂.mp h).2
      intro hcon
      exact absurd hcon.1 (not_lt.mpr (le_of_lt hneg))
  · by_cases huv₂ : u = -v
    · right
      have hIu : Complex.I * u ≠ 0 := by
        refine mul_ne_zero Complex.I_ne_zero ?_
        rintro h
        rw [h] at hu
        norm_num at hu
      refine ⟨φ, φ.source, Complex.I * u, hφ, φ.open_source, hsrc, ?_, hsrc, hIu, ?_⟩
      · intro y hy; exact hy
      · rintro x ⟨hxU, -⟩ t ht heq
        rw [hφp] at heq
        have hc₁ : x₀ - c₁ = (ρ₁:ℂ) * u := hcu.symm
        have hc₂ : x₀ - c₂ = -((ρ₂:ℂ) * u) := by
          have h : (ρ₂:ℂ) * v = -((ρ₂:ℂ) * u) := by rw [huv₂]; ring
          rw [← hcv, h]
        have hnot := ray_notMem h₂ hu hc₁ hc₂ t ht
        have hxeq : φ x = x₀ + t • (Complex.I * u) := by
          rw [← heq]; ring
        rcases hxU with h | h
        · have hxφ : φ x ∈ Metric.ball c₁ ρ₁ := (hmem₁.mp h).2
          rw [hxeq] at hxφ
          exact hnot.1 hxφ
        · have hxφ : φ x ∈ Metric.ball c₂ ρ₂ := (hmem₂.mp h).2
          rw [hxeq] at hxφ
          exact hnot.2 hxφ
    · left
      refine ⟨φ, φ.source, reConjCLM u, reConjCLM v, hφ, φ.open_source, hsrc, ?_, hsrc,
        reConjCLM_ne_zero hu, reConjCLM_ne_zero hv,
        exists_wedge_witness hu hv huv₂, ?_⟩
      · intro y hy; exact hy
      · rintro x ⟨hxU, -⟩
        rw [hφp]
        have hneg : reConjCLM u (φ x - x₀) < 0 ∨ reConjCLM v (φ x - x₀) < 0 := by
          rcases hxU with h | h
          · left; rw [reConjCLM_apply]
            exact disc_re_neg h₁ hd₁ (φ x) (hmem₁.mp h).2
          · right; rw [reConjCLM_apply]
            exact disc_re_neg h₂ hd₂ (φ x) (hmem₂.mp h).2
        rintro ⟨h1, h2⟩
        rcases hneg with h | h
        · exact absurd h1 (not_lt.mpr (le_of_lt h))
        · exact absurd h2 (not_lt.mpr (le_of_lt h))

/-! ### The main statement -/

theorem hasSectorBoundary_or_hasRayBoundary_of_two_chartBall {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] (φ : OpenPartialHomeomorph X ℂ) (hφ : φ ∈ atlas ℂ X) {c₁ c₂ : ℂ} {ρ₁ ρ₂ : ℝ} (h₁ : 0 < ρ₁) (h₂ : 0 < ρ₂) (hs₁ : Metric.closedBall c₁ ρ₁ ⊆ φ.target) (hs₂ : Metric.closedBall c₂ ρ₂ ⊆ φ.target) : ∀ p ∈ frontier ((φ.symm '' Metric.ball c₁ ρ₁) ∪ (φ.symm '' Metric.ball c₂ ρ₂)), Work.SimplyConnected.ABS.HasSectorBoundary ((φ.symm '' Metric.ball c₁ ρ₁) ∪ (φ.symm '' Metric.ball c₂ ρ₂)) p ∨ Work.SimplyConnected.ABS.HasRayBoundary ((φ.symm '' Metric.ball c₁ ρ₁) ∪ (φ.symm '' Metric.ball c₂ ρ₂)) p := by
  intro p hp
  set U : Set X := (φ.symm '' Metric.ball c₁ ρ₁) ∪ (φ.symm '' Metric.ball c₂ ρ₂) with hU
  have hUo : IsOpen U := by
    rw [hU]
    exact (φ.isOpen_image_symm_of_subset_target Metric.isOpen_ball
        (Metric.ball_subset_closedBall.trans hs₁)).union
      (φ.isOpen_image_symm_of_subset_target Metric.isOpen_ball
        (Metric.ball_subset_closedBall.trans hs₂))
  rw [frontier] at hp
  obtain ⟨hpcl, hpint⟩ := hp
  have hpU : p ∉ U := by rwa [IsOpen.interior_eq hUo] at hpint
  have hmem : p ∈ φ.symm '' Metric.closedBall c₁ ρ₁ ∪ φ.symm '' Metric.closedBall c₂ ρ₂ := by
    rw [hU, closure_union] at hpcl
    rcases hpcl with h | h
    · exact Or.inl (closure_symm_image_ball hs₁ h)
    · exact Or.inr (closure_symm_image_ball hs₂ h)
  have hsrc : p ∈ φ.source := by
    rcases hmem with h | h
    · exact ((symm_image_mem hs₁).mp h).1
    · exact ((symm_image_mem hs₂).mp h).1
  have hxcl : φ p ∈ Metric.closedBall c₁ ρ₁ ∨ φ p ∈ Metric.closedBall c₂ ρ₂ := by
    rcases hmem with h | h
    · exact Or.inl ((symm_image_mem hs₁).mp h).2
    · exact Or.inr ((symm_image_mem hs₂).mp h).2
  have hxball : ¬ (φ p ∈ Metric.ball c₁ ρ₁ ∨ φ p ∈ Metric.ball c₂ ρ₂) := by
    rintro (h | h)
    · refine hpU ?_
      rw [hU]
      exact Or.inl ((symm_image_mem (Metric.ball_subset_closedBall.trans hs₁)).mpr ⟨hsrc, h⟩)
    · refine hpU ?_
      rw [hU]
      exact Or.inr ((symm_image_mem (Metric.ball_subset_closedBall.trans hs₂)).mpr ⟨hsrc, h⟩)
  have hp_eq : p = φ.symm (φ p) := (φ.left_inv hsrc).symm
  rcases hxcl with hx₁ | hx₂
  · by_cases h2 : φ p ∈ Metric.closedBall c₂ ρ₂
    · have hs1 : φ p ∈ Metric.sphere c₁ ρ₁ :=
        Metric.mem_sphere.mpr (le_antisymm (Metric.mem_closedBall.mp hx₁)
          (not_lt.mp fun hh => hxball (Or.inl (Metric.mem_ball.mpr hh))))
      have hs2 : φ p ∈ Metric.sphere c₂ ρ₂ :=
        Metric.mem_sphere.mpr (le_antisymm (Metric.mem_closedBall.mp h2)
          (not_lt.mp fun hh => hxball (Or.inr (Metric.mem_ball.mpr hh))))
      have hres := sector_or_ray_of_two_balls hφ h₁ h₂ hs₁ hs₂ hs1 hs2
      rw [← hp_eq] at hres
      exact hres
    · have hs1 : φ p ∈ Metric.sphere c₁ ρ₁ :=
        Metric.mem_sphere.mpr (le_antisymm (Metric.mem_closedBall.mp hx₁)
          (not_lt.mp fun hh => hxball (Or.inl (Metric.mem_ball.mpr hh))))
      have hres := sector_of_one_ball hφ h₁ hs₁ hs₂ hs1 h2
      rw [← hp_eq] at hres
      exact Or.inl hres
  · by_cases h1' : φ p ∈ Metric.closedBall c₁ ρ₁
    · have hs1 : φ p ∈ Metric.sphere c₁ ρ₁ :=
        Metric.mem_sphere.mpr (le_antisymm (Metric.mem_closedBall.mp h1')
          (not_lt.mp fun hh => hxball (Or.inl (Metric.mem_ball.mpr hh))))
      have hs2 : φ p ∈ Metric.sphere c₂ ρ₂ :=
        Metric.mem_sphere.mpr (le_antisymm (Metric.mem_closedBall.mp hx₂)
          (not_lt.mp fun hh => hxball (Or.inr (Metric.mem_ball.mpr hh))))
      have hres := sector_or_ray_of_two_balls hφ h₁ h₂ hs₁ hs₂ hs1 hs2
      rw [← hp_eq] at hres
      exact hres
    · have hs2 : φ p ∈ Metric.sphere c₂ ρ₂ :=
        Metric.mem_sphere.mpr (le_antisymm (Metric.mem_closedBall.mp hx₂)
          (not_lt.mp fun hh => hxball (Or.inr (Metric.mem_ball.mpr hh))))
      have hres := sector_of_one_ball hφ h₂ hs₂ hs₁ hs2 h1'
      rw [← hp_eq] at hres
      have hres' : HasSectorBoundary U p := by
        rw [hU, Set.union_comm]
        exact hres
      exact Or.inl hres'

end

end Work.SimplyConnected.ABS
