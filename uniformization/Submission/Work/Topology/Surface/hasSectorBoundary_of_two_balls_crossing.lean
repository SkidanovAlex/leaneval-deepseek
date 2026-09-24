import Mathlib
import Submission.Work.SimplyConnected.ABS.RegularPieceDefs

/-!
# The sector condition at a crossing point of two chart balls

Let `φ` be a chart of a Riemann surface `X`, let `c₁ c₂ : ℂ` and `ρ₁ ρ₂ > 0` be such that the closed
balls `closedBall cᵢ ρᵢ` lie in `φ.target`, and let

`U = φ.symm '' ball c₁ ρ₁ ∪ φ.symm '' ball c₂ ρ₂`.

Let `p` be a frontier point of `U` whose image `x₀ = φ p` lies in **both** closed balls
`closedBall c₁ ρ₁`, `closedBall c₂ ρ₂` and which is *not* an internal tangency point, i.e.

`(x₀ - c₁)/ρ₁ ≠ -((x₀ - c₂)/ρ₂)`.

Then `U` satisfies the sector (cone) condition `Work.SimplyConnected.ABS.HasSectorBoundary U p` at
`p`.

## The mathematics

As `p` is a frontier point of `U` and `U` is open, `p ∉ U`; hence `x₀ = φ p` lies on neither open
ball `ball cᵢ ρᵢ`, and from the hypotheses `x₀ ∈ closedBall cᵢ ρᵢ` we get `x₀ ∈ sphere cᵢ ρᵢ`.  So
both discs pass through `x₀`, with outward unit normals

`u = (x₀ - c₁)/ρ₁`,  `v = (x₀ - c₂)/ρ₂`  (`‖u‖ = ‖v‖ = 1`).

The half plane through `x₀` with outward normal `u` contains `ball c₁ ρ₁`, i.e.

`0 < Re (conj u (z - x₀))` fails for every `z ∈ ball c₁ ρ₁` (indeed the expression is `< 0`), and
similarly for `ball c₂ ρ₂` with `v`.  The hypothesis `u ≠ -v` says exactly that the two closed half
planes have an open wedge in common: `w = u + v` satisfies `0 < Re (conj u w)` and
`0 < Re (conj v w)` because `Re (conj u v) > -1`.  Hence the two real-linear functionals

`L₁ z = Re (conj u z)`, `L₂ z = Re (conj v z)`

are nonzero, span a nondegenerate sector, and `U` avoids that sector near `p`: this is precisely
`HasSectorBoundary U p`.
-/

namespace Work.Topology.Surface

open Set Metric
open scoped ComplexConjugate

set_option linter.unusedSectionVars false

noncomputable section

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-! ## Plane lemmas: the two discs through `x₀` leave a sector free -/

private lemma norm_ofReal_complex (r : ℝ) : ‖(r:ℂ)‖ = |r| := RCLike.norm_ofReal r

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

/-- **A disc through `x₀` lies in a half plane.**  If `x₀` is on the boundary of the disc
`ball c ρ`, then with `u = (ρ)⁻¹ (x₀ - c)` the whole disc lies in `{z : Re (conj u (z - x₀)) < 0}`. -/
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
vectors, the set `{w : 0 < Re (conj u w) ∧ 0 < Re (conj v w)}` is non-empty. -/
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

/-- **The sector functionals of two discs crossing at `x₀`.**  If `x₀` lies on both boundary
circles `sphere cᵢ ρᵢ` and the outward normals are not opposite
(`(x₀ - c₁)/ρ₁ ≠ -((x₀ - c₂)/ρ₂)`), then the two *open* discs avoid a common nondegenerate open
sector with apex `x₀`: there are nonzero real-linear functionals `L₁ L₂` with a common positive
witness `w` such that `U` never has both `L₁ (· - x₀)` and `L₂ (· - x₀)` positive. -/
private lemma twoBalls_sectorFunctionals {c₁ c₂ : ℂ} {ρ₁ ρ₂ : ℝ} (h₁ : 0 < ρ₁) (h₂ : 0 < ρ₂)
    {x₀ : ℂ} (hx₁ : x₀ ∈ Metric.sphere c₁ ρ₁) (hx₂ : x₀ ∈ Metric.sphere c₂ ρ₂)
    (hcross : (x₀ - c₁) / ρ₁ ≠ -((x₀ - c₂) / ρ₂)) :
    ∃ L₁ L₂ : ℂ →L[ℝ] ℝ, L₁ ≠ 0 ∧ L₂ ≠ 0 ∧ (∃ w : ℂ, 0 < L₁ w ∧ 0 < L₂ w) ∧
      ∀ z ∈ Metric.ball c₁ ρ₁ ∪ Metric.ball c₂ ρ₂,
        ¬ (0 < L₁ (z - x₀) ∧ 0 < L₂ (z - x₀)) := by
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
  have hcross' : u ≠ -v := by
    intro h
    refine hcross ?_
    rw [div_eq_inv_mul, div_eq_inv_mul, ← hu_def, ← hv_def]
    exact h
  refine ⟨reConjCLM u, reConjCLM v, reConjCLM_ne_zero hu, reConjCLM_ne_zero hv,
    exists_wedge_witness hu hv hcross', ?_⟩
  rintro z (hz | hz) hcon
  · have hneg : reConjCLM u (z - x₀) < 0 := by
      rw [reConjCLM_apply]
      exact disc_re_neg h₁ hd₁ z hz
    exact absurd hcon.1 (not_lt.mpr (le_of_lt hneg))
  · have hneg : reConjCLM v (z - x₀) < 0 := by
      rw [reConjCLM_apply]
      exact disc_re_neg h₂ hd₂ z hz
    exact absurd hcon.2 (not_lt.mpr (le_of_lt hneg))

/-! ## Chart bookkeeping -/

/-- Membership in `φ.symm '' W` in terms of the chart coordinates, for `W` inside the target. -/
private lemma symm_image_mem {φ : OpenPartialHomeomorph X ℂ} {W : Set ℂ} (hW : W ⊆ φ.target)
    {x : X} : x ∈ φ.symm '' W ↔ x ∈ φ.source ∧ φ x ∈ W := by
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

/-- The sector condition at a point of `φ.source` whose image lies on both boundary spheres. -/
private lemma hasSectorBoundary_of_two_balls_sphere {φ : OpenPartialHomeomorph X ℂ}
    (hφ : φ ∈ atlas ℂ X) {c₁ c₂ : ℂ} {ρ₁ ρ₂ : ℝ} (h₁ : 0 < ρ₁) (h₂ : 0 < ρ₂)
    (hT₁ : Metric.closedBall c₁ ρ₁ ⊆ φ.target) (hT₂ : Metric.closedBall c₂ ρ₂ ⊆ φ.target)
    {p : X} (hpsrc : p ∈ φ.source) (hsp₁ : φ p ∈ Metric.sphere c₁ ρ₁)
    (hsp₂ : φ p ∈ Metric.sphere c₂ ρ₂)
    (hcross : (φ p - c₁) / ρ₁ ≠ -((φ p - c₂) / ρ₂)) :
    Work.SimplyConnected.ABS.HasSectorBoundary
      ((φ.symm '' Metric.ball c₁ ρ₁) ∪ (φ.symm '' Metric.ball c₂ ρ₂)) p := by
  obtain ⟨L₁, L₂, hL₁, hL₂, hw, hsec⟩ := twoBalls_sectorFunctionals h₁ h₂ hsp₁ hsp₂ hcross
  refine ⟨φ, φ.source, L₁, L₂, hφ, φ.open_source, hpsrc, subset_rfl, hpsrc, hL₁, hL₂, hw, ?_⟩
  rintro x ⟨hxU, -⟩
  rcases hxU with hx | hx
  · exact hsec (φ x) (Or.inl ((symm_image_mem (Metric.ball_subset_closedBall.trans hT₁)).mp hx).2)
  · exact hsec (φ x) (Or.inr ((symm_image_mem (Metric.ball_subset_closedBall.trans hT₂)).mp hx).2)

/-! ## The main statement -/

theorem hasSectorBoundary_of_two_balls_crossing {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] (φ : OpenPartialHomeomorph X ℂ) (hφ : φ ∈ atlas ℂ X) {c₁ c₂ : ℂ} {ρ₁ ρ₂ : ℝ} (h₁ : 0 < ρ₁) (h₂ : 0 < ρ₂) (hs₁ : Metric.closedBall c₁ ρ₁ ⊆ φ.target) (hs₂ : Metric.closedBall c₂ ρ₂ ⊆ φ.target) {p : X} (hp : p ∈ frontier ((φ.symm '' Metric.ball c₁ ρ₁) ∪ (φ.symm '' Metric.ball c₂ ρ₂))) (hm₁ : φ p ∈ Metric.closedBall c₁ ρ₁) (hm₂ : φ p ∈ Metric.closedBall c₂ ρ₂) (hcross : (φ p - c₁) / ρ₁ ≠ -((φ p - c₂) / ρ₂)) : Work.SimplyConnected.ABS.HasSectorBoundary ((φ.symm '' Metric.ball c₁ ρ₁) ∪ (φ.symm '' Metric.ball c₂ ρ₂)) p := by
  have hUo : IsOpen ((φ.symm '' Metric.ball c₁ ρ₁) ∪ (φ.symm '' Metric.ball c₂ ρ₂)) :=
    (φ.isOpen_image_symm_of_subset_target Metric.isOpen_ball
        (Metric.ball_subset_closedBall.trans hs₁)).union
      (φ.isOpen_image_symm_of_subset_target Metric.isOpen_ball
        (Metric.ball_subset_closedBall.trans hs₂))
  have hpcl : p ∈ closure ((φ.symm '' Metric.ball c₁ ρ₁) ∪ (φ.symm '' Metric.ball c₂ ρ₂)) := by
    have h := hp
    rw [frontier, Set.mem_sdiff] at h
    exact h.1
  have hpU : p ∉ ((φ.symm '' Metric.ball c₁ ρ₁) ∪ (φ.symm '' Metric.ball c₂ ρ₂)) := by
    have h := hp
    rw [frontier, Set.mem_sdiff, IsOpen.interior_eq hUo] at h
    exact h.2
  have hmemcl : p ∈ φ.symm '' Metric.closedBall c₁ ρ₁ ∪ φ.symm '' Metric.closedBall c₂ ρ₂ := by
    rw [closure_union] at hpcl
    rcases hpcl with h | h
    · exact Or.inl (closure_symm_image_ball hs₁ h)
    · exact Or.inr (closure_symm_image_ball hs₂ h)
  have hpsrc : p ∈ φ.source := by
    rcases hmemcl with h | h
    · exact ((symm_image_mem hs₁).mp h).1
    · exact ((symm_image_mem hs₂).mp h).1
  have hsp₁ : φ p ∈ Metric.sphere c₁ ρ₁ := by
    rw [Metric.mem_sphere]
    refine le_antisymm (Metric.mem_closedBall.mp hm₁) (not_lt.mp fun hlt => ?_)
    exact hpU (Or.inl ((symm_image_mem (Metric.ball_subset_closedBall.trans hs₁)).mpr
      ⟨hpsrc, Metric.mem_ball.mpr hlt⟩))
  have hsp₂ : φ p ∈ Metric.sphere c₂ ρ₂ := by
    rw [Metric.mem_sphere]
    refine le_antisymm (Metric.mem_closedBall.mp hm₂) (not_lt.mp fun hlt => ?_)
    exact hpU (Or.inr ((symm_image_mem (Metric.ball_subset_closedBall.trans hs₂)).mpr
      ⟨hpsrc, Metric.mem_ball.mpr hlt⟩))
  exact hasSectorBoundary_of_two_balls_sphere hφ h₁ h₂ hs₁ hs₂ hpsrc hsp₁ hsp₂ hcross

end

end Work.Topology.Surface
