import Mathlib
import ChallengeDeps
import Submission.Voronoi
import Submission.VoronoiMeasure
import Submission.QuotientLattice
import Submission.SubLattice
import Submission.Determinant
import Submission.LatticeBasics

open Module MeasureTheory Metric Set
open scoped Real BigOperators InnerProductSpace RealInnerProductSpace ENNReal NNReal Pointwise
set_option autoImplicit false

/-! # The closest-vector map (CVP)

The [C]-block (`monotone_Voronoi_wins`: the Voronoi cell maximizes the integral of a
radial non-increasing function among fundamental bodies of the lattice) is built on
the closest-vector map

  ψ(x) := x − cvp(x),

where `cvp(x)` is a lattice point closest to `x` (arbitrary tie-breaking).  The two
facts used everywhere are that `ψ(x)` lies in the Voronoi cell and that
`‖ψ(x)‖ ≤ ‖x‖` (since `0 ∈ ℒ`).  This module records those facts together with the
injectivity of `ψ` on the interior of any set `K` whose translates `K + y` do not
overlap `Int K` for `y ≠ 0` (a "fundamental body").
-/

namespace Submission.Cvp

variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "VC" => Submission.Voronoi.voronoi

/-- A closest lattice point to `x` (arbitrary tie-breaking). -/
noncomputable def cvp {ℒ : Submodule ℤ E} [DiscreteTopology ℒ]
    (hℒ : IsZLattice ℝ ℒ) (x : E) : ℒ :=
  Classical.choose (Submission.VoronoiMeasure.exists_nearest_lattice_point (ℒ := ℒ) hℒ x)

/-- `cvp hℒ x` is indeed closest to `x` among all lattice points. -/
lemma cvp_spec {ℒ : Submodule ℤ E} [DiscreteTopology ℒ] (hℒ : IsZLattice ℝ ℒ) (x : E) :
    ∀ z : ℒ, ‖x - (z : E)‖ ≥ ‖x - ((cvp hℒ x : ℒ) : E)‖ :=
  Classical.choose_spec (Submission.VoronoiMeasure.exists_nearest_lattice_point (ℒ := ℒ) hℒ x)

/-- The closest-vector map `ψ(x) := x − cvp(x)`. -/
noncomputable def psi {ℒ : Submodule ℤ E} [DiscreteTopology ℒ]
    (hℒ : IsZLattice ℝ ℒ) (x : E) : E :=
  x - ((cvp hℒ x : ℒ) : E)

/-- `ψ(x)` lies in the Voronoi cell. -/
lemma psi_mem_voronoi {ℒ : Submodule ℤ E} [DiscreteTopology ℒ]
    (hℒ : IsZLattice ℝ ℒ) (x : E) : psi hℒ x ∈ VC ℒ := by
  have h := Submission.VoronoiMeasure.vadd_mem_of_nearest (ℒ := ℒ) (cvp hℒ x) x (cvp_spec hℒ x)
  simpa [psi, add_comm, sub_eq_add_neg] using h

/-- The distance from `x` to its closest lattice point is `‖ψ(x)‖`. -/
lemma dist_cvp_eq {ℒ : Submodule ℤ E} [DiscreteTopology ℒ]
    (hℒ : IsZLattice ℝ ℒ) (x : E) : ‖x - ((cvp hℒ x : ℒ) : E)‖ = ‖psi hℒ x‖ := by
  rfl

/-- `ψ` shrinks the norm: `‖ψ(x)‖ ≤ ‖x‖` (because `0 ∈ ℒ`). -/
lemma norm_psi_le {ℒ : Submodule ℤ E} [DiscreteTopology ℒ]
    (hℒ : IsZLattice ℝ ℒ) (x : E) : ‖psi hℒ x‖ ≤ ‖x‖ := by
  have h0 := cvp_spec hℒ x 0
  rw [dist_cvp_eq] at h0
  simpa using h0

/-- If `ψ(x) = ψ(x')` then `x − x'` is the difference of the two closest lattice
points (hence a lattice point). -/
lemma cvp_diff_of_psi_eq {ℒ : Submodule ℤ E} [DiscreteTopology ℒ]
    (hℒ : IsZLattice ℝ ℒ) (x x' : E) :
    psi hℒ x = psi hℒ x' →
      x - x' = ((cvp hℒ x : ℒ) : E) - ((cvp hℒ x' : ℒ) : E) := by
  intro h
  have h' : x - ((cvp hℒ x : ℒ) : E) = x' - ((cvp hℒ x' : ℒ) : E) := by
    simpa [psi] using h
  calc
    x - x' = (x - ((cvp hℒ x : ℒ) : E)) - (x' - ((cvp hℒ x' : ℒ) : E))
        + (((cvp hℒ x : ℒ) : E) - ((cvp hℒ x' : ℒ) : E)) := by abel
    _ = 0 + (((cvp hℒ x : ℒ) : E) - ((cvp hℒ x' : ℒ) : E)) := by
      rw [h']
      abel
    _ = ((cvp hℒ x : ℒ) : E) - ((cvp hℒ x' : ℒ) : E) := by abel

/-- `ψ` is injective on the interior of any set whose distinct translates do not
overlap its interior (the "fundamental body" disjointness). -/
lemma psi_injective_on_interior {ℒ : Submodule ℤ E} [DiscreteTopology ℒ]
    (hℒ : IsZLattice ℝ ℒ) (K : Set E)
    (hK : ∀ y : ℒ, y ≠ 0 → Disjoint (interior K) (((y : E) +ᵥ K))) :
    Set.InjOn (psi hℒ) (interior K) := by
  intro x hx x' hx' hpsi
  have hy_eq : x - x' = ((cvp hℒ x : ℒ) : E) - ((cvp hℒ x' : ℒ) : E) :=
    cvp_diff_of_psi_eq hℒ x x' hpsi
  let y : ℒ := cvp hℒ x - cvp hℒ x'
  have hy : (y : E) = x - x' := by
    dsimp [y]
    exact hy_eq.symm
  by_cases hy0 : y = 0
  · have hy0' : cvp hℒ x - cvp hℒ x' = 0 := by
      change y = 0
      exact hy0
    have hcvpeq : cvp hℒ x = cvp hℒ x' := sub_eq_zero.mp hy0'
    have hceq : ((cvp hℒ x : ℒ) : E) = ((cvp hℒ x' : ℒ) : E) := by rw [hcvpeq]
    have hxx' : x - x' = 0 := by rw [hy_eq, hceq, sub_self]
    exact sub_eq_zero.mp hxx'
  · have hxmem : x ∈ ((y : E) +ᵥ K) := by
      rw [Set.mem_vadd_set]
      use x', interior_subset hx'
      change (y : E) + x' = x
      rw [hy]
      abel
    exfalso
    exact (hK y hy0).ne_of_mem hx hxmem rfl





/-- Lattice points in a closed ball form a finite set. -/
lemma finite_lattice_points_in_ball {ℒ : Submodule ℤ E} [DiscreteTopology ℒ] (c : E) (R : ℝ) :
    {y : ℒ | ‖(y : E) - c‖ ≤ R}.Finite := by
  classical
  have hclosed : IsClosed (ℒ.toAddSubgroup : Set E) :=
    AddSubgroup.isClosed_of_discrete (G := E) (H := ℒ.toAddSubgroup)
  have hdisc : IsDiscrete (ℒ.toAddSubgroup : Set E) := DiscreteTopology.isDiscrete
  have himg : (fun y : ℒ => (y : E)) '' {y : ℒ | ‖(y : E) - c‖ ≤ R} ⊆
      Metric.closedBall c R ∩ (ℒ.toAddSubgroup : Set E) := by
    rintro v ⟨y, hy, rfl⟩
    refine ⟨?_, (Submodule.mem_toAddSubgroup (p := ℒ)).mpr y.2⟩
    rw [Metric.mem_closedBall, dist_eq_norm]
    exact hy
  have hinj : Set.InjOn (fun y : ℒ => (y : E)) {y : ℒ | ‖(y : E) - c‖ ≤ R} :=
    (Subtype.coe_injective).injOn
  exact ((Metric.finite_isBounded_inter_isClosed hdisc Metric.isBounded_closedBall hclosed).subset himg).of_finite_image hinj

/-- Direction (⇒) of the open-cell characterization: an interior point satisfies
every constraint strictly. -/
lemma strict_of_interior_voronoi {ℒ : Submodule ℤ E} [DiscreteTopology ℒ]
    {x : E} (hx : x ∈ interior (VC ℒ)) :
    ∀ y : ℒ, y ≠ 0 → ⟪x, (y : E)⟫_ℝ < ‖(y : E)‖ ^ 2 / 2 := by
  intro y hy0
  have hmem := (Submission.Voronoi.mem_voronoi.mp (interior_subset hx)) y
  have hle : ⟪x, (y : E)⟫_ℝ ≤ ‖(y : E)‖ ^ 2 / 2 := hmem
  have hne0 : ‖(y : E)‖ ≠ 0 := by
    intro hn
    exact hy0 (Subtype.ext (norm_eq_zero.mp hn))
  by_contra hlt
  have heq : ⟪x, (y : E)⟫_ℝ = ‖(y : E)‖ ^ 2 / 2 := le_antisymm hle (le_of_not_gt hlt)
  rcases (Metric.isOpen_iff.mp isOpen_interior) x hx with ⟨r, hr, hball⟩
  let δ : ℝ := r / (2 * ‖(y : E)‖)
  have hypos : 0 < ‖(y : E)‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne0)
  have hδpos : 0 < δ := by
    dsimp [δ]
    exact div_pos hr (mul_pos two_pos hypos)
  have hδy : ‖δ • (y : E)‖ < r := by
    rw [norm_smul]
    rw [Real.norm_eq_abs, abs_of_pos hδpos]
    dsimp [δ]
    calc
      (r / (2 * ‖(y : E)‖)) * ‖(y : E)‖ = r / 2 := by
        field_simp [hne0]
      _ < r := by linarith [hr]
  have hballmem : x + δ • (y : E) ∈ Metric.ball x r := by
    rw [Metric.mem_ball, dist_eq_norm]
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, smul_eq_mul] using hδy
  have hviol : ‖(y : E)‖ ^ 2 / 2 < ⟪x + δ • (y : E), (y : E)⟫_ℝ := by
    have hinner : ⟪δ • (y : E), (y : E)⟫_ℝ = δ * ‖(y : E)‖ ^ 2 := by
      rw [real_inner_smul_left, real_inner_self_eq_norm_sq]
    have hδpos2 : 0 < δ * ‖(y : E)‖ ^ 2 := mul_pos hδpos (sq_pos_of_ne_zero hne0)
    rw [inner_add_left, hinner]
    nlinarith [heq, hδpos2]
  have hvc := hball hballmem
  exact (not_le_of_gt hviol) ((Submission.Voronoi.mem_voronoi.mp (interior_subset hvc)) y)

/-- Direction (⇐) of the open-cell characterization: strictly satisfying every
constraint puts `x` in the interior of the Voronoi cell.

Proof: only finitely many lattice points lie in the ball of radius `R = 2‖x‖+1`.
For those the slack `δ_y := ‖y‖²/2 − ⟨x,y⟩` is strictly positive, so a small
`ε > 0` (half the minimum of `δ_y/‖y‖` over the finite set) fits inside each;
for the infinitely many `y` with `‖y‖ ≥ R` the slack is at least `‖y‖/2`
(Cauchy–Schwarz), so any `ε ≤ 1/2` works.  Then `⟨x+z, y⟩ ≤ ⟨x,y⟩ + ε‖y‖ ≤ ‖y‖²/2`
for every `z` with `‖z‖ ≤ ε`. -/
lemma interior_voronoi_of_strict {ℒ : Submodule ℤ E} [DiscreteTopology ℒ] (x : E)
    (h : ∀ y : ℒ, y ≠ 0 → ⟪x, (y : E)⟫_ℝ < ‖(y : E)‖ ^ 2 / 2) :
    x ∈ interior (VC ℒ) := by
  classical
  let R : ℝ := 2 * ‖x‖ + 1
  -- finite set of lattice points within the ball of radius R
  have hFin : {y : ℒ | y ≠ 0 ∧ ‖(y : E)‖ ≤ R}.Finite := by
    refine (finite_lattice_points_in_ball (ℒ := ℒ) (0 : E) R).subset ?_
    rintro y ⟨_hy0, hyR⟩
    simpa using hyR
  let F : Finset ℒ := hFin.toFinset
  have hFmem : ∀ y : ℒ, y ∈ F ↔ y ≠ 0 ∧ ‖(y : E)‖ ≤ R := by
    intro y
    exact hFin.mem_toFinset
  -- slack δ_y and normalized slack f_y on nonzero lattice points
  let δ : ℒ → ℝ := fun y => ‖(y : E)‖ ^ 2 / 2 - ⟪x, (y : E)⟫_ℝ
  let f : ℒ → ℝ := fun y => δ y / ‖(y : E)‖
  have hδpos (y : ℒ) (hy0 : y ≠ 0) : 0 < δ y := by
    dsimp [δ]
    linarith [h y hy0]
  have hfpos (y : ℒ) (hyF : y ∈ F) : 0 < f y := by
    have hyS := (hFmem y).mp hyF
    have hypos : 0 < ‖(y : E)‖ := by
      have hne : ‖(y : E)‖ ≠ 0 := by
        intro hn
        exact hyS.1 (Subtype.ext (norm_eq_zero.mp hn))
      exact lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)
    dsimp [f, δ]
    exact div_pos (hδpos y hyS.1) hypos
  -- tail estimate: for ‖y‖ ≥ R the slack covers ε·‖y‖ for any ε ≤ 1/2
  have htail (ε : ℝ) (hε : ε ≤ (1 : ℝ) / 2) (y : ℒ) (hy0 : y ≠ 0)
      (hybig : R < ‖(y : E)‖) :
      ε * ‖(y : E)‖ ≤ ‖(y : E)‖ ^ 2 / 2 - ⟪x, (y : E)⟫_ℝ := by
    have hypos : 0 < ‖(y : E)‖ := by
      have hne : ‖(y : E)‖ ≠ 0 := by
        intro hn
        exact hy0 (Subtype.ext (norm_eq_zero.mp hn))
      exact lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)
    have hy0' : 0 ≤ ‖(y : E)‖ := norm_nonneg _
    have hcs : ⟪x, (y : E)⟫_ℝ ≤ ‖x‖ * ‖(y : E)‖ := real_inner_le_norm x (y : E)
    have hlin : 2 * ‖x‖ + 1 ≤ ‖(y : E)‖ := by
      dsimp [R] at hybig
      exact le_of_lt hybig
    have hsq : (2 * ‖x‖ + 1) * ‖(y : E)‖ ≤ ‖(y : E)‖ ^ 2 := by
      rw [pow_two]
      exact mul_le_mul_of_nonneg_right hlin hy0'
    have hhalf : (1 : ℝ) / 2 * ‖(y : E)‖ ≤ ‖(y : E)‖ ^ 2 / 2 - ⟪x, (y : E)⟫_ℝ := by
      nlinarith [hcs, hsq, hy0']
    have hεy : ε * ‖(y : E)‖ ≤ (1 : ℝ) / 2 * ‖(y : E)‖ :=
      mul_le_mul_of_nonneg_right hε hy0'
    linarith
  by_cases hF : F = ∅
  · -- no nonzero lattice point has norm ≤ R : ε := 1/4 works for all
    have hclosed : Metric.closedBall x (1 / 4) ⊆ VC ℒ := by
      intro z hz
      rw [Submission.Voronoi.mem_voronoi]
      intro y
      by_cases hy0 : y = 0
      · subst y
        simp
      · have hybig : R < ‖(y : E)‖ := by
          by_contra hle
          have hyS : y ≠ 0 ∧ ‖(y : E)‖ ≤ R := ⟨hy0, le_of_not_gt hle⟩
          have hyF : y ∈ F := (hFmem y).mpr hyS
          rw [hF] at hyF
          simp at hyF
        have hεy := htail (1 / 4) (by norm_num) y hy0 hybig
        have hzle : ‖z - x‖ ≤ (1 : ℝ) / 4 := by
          simpa [dist_eq_norm] using (Metric.mem_closedBall.mp hz)
        have hin : ⟪x + (z - x), (y : E)⟫_ℝ ≤ ⟪x, (y : E)⟫_ℝ + ‖z - x‖ * ‖(y : E)‖ := by
          calc
            ⟪x + (z - x), (y : E)⟫_ℝ = ⟪x, (y : E)⟫_ℝ + ⟪z - x, (y : E)⟫_ℝ := by rw [inner_add_left]
            _ ≤ ⟪x, (y : E)⟫_ℝ + ‖z - x‖ * ‖(y : E)‖ := by
              exact add_le_add_right (real_inner_le_norm (z - x) (y : E)) ⟪x, (y : E)⟫_ℝ
        have hzmem : ⟪z, (y : E)⟫_ℝ ≤ ‖(y : E)‖ ^ 2 / 2 := by
          calc
            ⟪z, (y : E)⟫_ℝ = ⟪x + (z - x), (y : E)⟫_ℝ := by congr 1; abel
            _ ≤ ⟪x, (y : E)⟫_ℝ + ‖z - x‖ * ‖(y : E)‖ := hin
            _ ≤ ⟪x, (y : E)⟫_ℝ + (1 : ℝ) / 4 * ‖(y : E)‖ := by
              exact add_le_add_right (mul_le_mul_of_nonneg_right hzle (norm_nonneg (y : E))) ⟪x, (y : E)⟫_ℝ
            _ ≤ ‖(y : E)‖ ^ 2 / 2 := by linarith [hεy]
        exact hzmem
    have hball : Metric.ball x (1 / 4) ⊆ VC ℒ := by
      intro z hz
      exact hclosed (Metric.ball_subset_closedBall hz)
    have hsub : Metric.ball x (1 / 4) ⊆ interior (VC ℒ) := interior_maximal hball isOpen_ball
    have hx : x ∈ Metric.ball x (1 / 4) := by
      rw [Metric.mem_ball, dist_self]
      norm_num
    exact hsub hx
  · -- F nonempty: ε := min (1/2) (m/2) with m := min of f over F
    have hFne : F.Nonempty := Finset.nonempty_iff_ne_empty.mpr hF
    rcases Finset.exists_min_image F f hFne with ⟨y₀, hy₀F, hmin⟩
    let m : ℝ := f y₀
    have hmpos : 0 < m := hfpos y₀ hy₀F
    let ε : ℝ := min (1 / 2) (m / 2)
    have hεpos : 0 < ε := by
      dsimp [ε]
      exact lt_min (by norm_num) (div_pos hmpos (by norm_num))
    have hεhalf : ε ≤ (1 : ℝ) / 2 := by
      dsimp [ε]
      exact min_le_left _ _
    have hεm (y : ℒ) (hyF : y ∈ F) : ε ≤ f y := by
      dsimp [ε]
      have hmle : m ≤ f y := hmin y hyF
      have hm2le : m / 2 ≤ f y := by linarith
      exact le_trans (min_le_right _ _) hm2le
    have hclosed : Metric.closedBall x ε ⊆ VC ℒ := by
      intro z hz
      rw [Submission.Voronoi.mem_voronoi]
      intro y
      by_cases hy0 : y = 0
      · subst y
        simp
      · have hypos : 0 < ‖(y : E)‖ := by
          have hne : ‖(y : E)‖ ≠ 0 := by
            intro hn
            exact hy0 (Subtype.ext (norm_eq_zero.mp hn))
          exact lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)
        have hεy : ε * ‖(y : E)‖ ≤ ‖(y : E)‖ ^ 2 / 2 - ⟪x, (y : E)⟫_ℝ := by
          by_cases hyR : ‖(y : E)‖ ≤ R
          · have hyF : y ∈ F := (hFmem y).mpr ⟨hy0, hyR⟩
            have hεf : ε ≤ δ y / ‖(y : E)‖ := by
              simpa [f, δ] using (hεm y hyF)
            have hle' := (le_div_iff₀ hypos).mp hεf
            simpa [δ, mul_comm] using hle'
          · have hybig : R < ‖(y : E)‖ := lt_of_not_ge hyR
            exact htail ε hεhalf y hy0 hybig
        have hzle : ‖z - x‖ ≤ ε := by
          simpa [dist_eq_norm] using (Metric.mem_closedBall.mp hz)
        have hin : ⟪x + (z - x), (y : E)⟫_ℝ ≤ ⟪x, (y : E)⟫_ℝ + ‖z - x‖ * ‖(y : E)‖ := by
          calc
            ⟪x + (z - x), (y : E)⟫_ℝ = ⟪x, (y : E)⟫_ℝ + ⟪z - x, (y : E)⟫_ℝ := by rw [inner_add_left]
            _ ≤ ⟪x, (y : E)⟫_ℝ + ‖z - x‖ * ‖(y : E)‖ := by
              exact add_le_add_right (real_inner_le_norm (z - x) (y : E)) ⟪x, (y : E)⟫_ℝ
        have hzmem : ⟪z, (y : E)⟫_ℝ ≤ ‖(y : E)‖ ^ 2 / 2 := by
          calc
            ⟪z, (y : E)⟫_ℝ = ⟪x + (z - x), (y : E)⟫_ℝ := by congr 1; abel
            _ ≤ ⟪x, (y : E)⟫_ℝ + ‖z - x‖ * ‖(y : E)‖ := hin
            _ ≤ ⟪x, (y : E)⟫_ℝ + ε * ‖(y : E)‖ := by
              exact add_le_add_right (mul_le_mul_of_nonneg_right hzle (norm_nonneg (y : E))) ⟪x, (y : E)⟫_ℝ
            _ ≤ ‖(y : E)‖ ^ 2 / 2 := by linarith [hεy]
        exact hzmem
    have hball : Metric.ball x ε ⊆ VC ℒ := by
      intro z hz
      exact hclosed (Metric.ball_subset_closedBall hz)
    have hsub : Metric.ball x ε ⊆ interior (VC ℒ) := interior_maximal hball isOpen_ball
    have hx : x ∈ Metric.ball x ε := by
      rw [Metric.mem_ball, dist_self]
      exact hεpos
    exact hsub hx

/-- The open-cell characterization of the Voronoi interior: `x` is an interior
point iff it strictly satisfies every constraint. -/
theorem mem_interior_voronoi_iff {ℒ : Submodule ℤ E} [DiscreteTopology ℒ] (x : E) :
    x ∈ interior (VC ℒ) ↔ ∀ y : ℒ, y ≠ 0 → ⟪x, (y : E)⟫_ℝ < ‖(y : E)‖ ^ 2 / 2 := by
  constructor
  · intro hx y hy0
    exact strict_of_interior_voronoi hx y hy0
  · intro h
    exact interior_voronoi_of_strict x h


/-- A Voronoi-cell point outside the interior satisfies some constraint with equality. -/
lemma exists_tight_of_voronoi_not_interior {ℒ : Submodule ℤ E} [DiscreteTopology ℒ]
    {x : E} (hxV : x ∈ VC ℒ) (hxn : x ∉ interior (VC ℒ)) :
    ∃ y : ℒ, y ≠ 0 ∧ ⟪x, (y : E)⟫_ℝ = ‖(y : E)‖ ^ 2 / 2 := by
  classical
  have hnot : ¬ ∀ y : ℒ, y ≠ 0 → ⟪x, (y : E)⟫_ℝ < ‖(y : E)‖ ^ 2 / 2 := by
    intro hall
    exact hxn (interior_voronoi_of_strict x hall)
  push Not at hnot
  rcases hnot with ⟨y, hy0, hnotlt⟩
  have hle : ⟪x, (y : E)⟫_ℝ ≤ ‖(y : E)‖ ^ 2 / 2 := (Submission.Voronoi.mem_voronoi.mp hxV) y
  exact ⟨y, hy0, le_antisymm hle hnotlt⟩

/-- The relative boundary of the Voronoi cell (points of the closed cell outside its
interior) has Lebesgue measure zero: each such point lies on one of the countably
many affine hyperplanes `{x | ⟨x, y⟩ = ‖y‖²/2}`, `y ≠ 0`. -/
lemma volume_voronoi_boundary_zero {ℒ : Submodule ℤ E} [DiscreteTopology ℒ] [Countable ℒ] :
    volume ((VC ℒ : Set E) \ interior (VC ℒ)) = 0 := by
  classical
  let S : Set E := {x : E | ∃ y : {y : ℒ // y ≠ 0},
      ⟪x, (y.1 : E)⟫_ℝ = ‖(y.1 : E)‖ ^ 2 / 2}
  have hsub : (VC ℒ : Set E) \ interior (VC ℒ) ⊆ S := by
    intro x hx
    rcases exists_tight_of_voronoi_not_interior (ℒ := ℒ) hx.1 hx.2 with ⟨y, hy0, ht⟩
    refine ⟨⟨y, hy0⟩, ?_⟩
    simpa using ht
  have hnull : volume S = 0 := by
    have hS : S = ⋃ y : {y : ℒ // y ≠ 0},
        {x : E | ⟪x, (y.1 : E)⟫_ℝ = ‖(y.1 : E)‖ ^ 2 / 2} := by
      ext x
      simp [S]
    rw [hS]
    rw [measure_iUnion_null]
    intro y
    have hz : volume {x : E | ⟪x - (0 : E), (y.1 : E)⟫_ℝ = ‖(y.1 : E)‖ ^ 2 / 2} = 0 :=
      Submission.VoronoiMeasure.hyperplane_measure_zero (p := (0 : E)) (h := (y.1 : E))
        (by
          intro hz
          exact y.2 (Subtype.ext hz))
    simpa using hz
  exact measure_mono_null hsub hnull



/-- If `x − y` lies in the interior of the Voronoi cell then `y` is the unique
closest lattice point to `x`, so `ψ(x) = x − y`. -/
lemma psi_eq_of_voronoi_interior {ℒ : Submodule ℤ E} [DiscreteTopology ℒ]
    (hℒ : IsZLattice ℝ ℒ) (y : ℒ) (x : E)
    (h : x - (y : E) ∈ interior (VC ℒ)) : psi hℒ x = x - (y : E) := by
  classical
  have hcvp : cvp hℒ x = y := by
    by_contra hne
    let z : ℒ := cvp hℒ x
    let u : E := x - (y : E)
    let w : ℒ := z - y
    have hw0 : w ≠ 0 := by
      dsimp [w, z]
      exact sub_ne_zero.mpr hne
    have hstrict := (mem_interior_voronoi_iff (ℒ := ℒ) u).mp h w hw0
    have hyV : x - (y : E) ∈ VC ℒ := interior_subset h
    have hz_spec := cvp_spec hℒ x y
    have hu_eq : ‖u - (w : E)‖ ^ 2 = ‖u‖ ^ 2 + ‖(w : E)‖ ^ 2 - 2 * ⟪u, (w : E)⟫_ℝ := by
      rw [norm_sub_sq_real]
      ring
    have hgt : ‖u‖ ^ 2 < ‖u - (w : E)‖ ^ 2 := by
      rw [hu_eq]
      nlinarith [hstrict]
    have hdist : ‖x - ((cvp hℒ x : ℒ) : E)‖ ≤ ‖x - (y : E)‖ := hz_spec
    have hrewrite : ‖x - ((cvp hℒ x : ℒ) : E)‖ = ‖u - (w : E)‖ := by
      have hargs : x - ((cvp hℒ x : ℒ) : E) = u - (w : E) := by
        dsimp [u, w, z]
        abel
      exact congrArg (fun t : E => ‖t‖) hargs
    have hle_pow : ‖u - (w : E)‖ ^ 2 ≤ ‖u‖ ^ 2 := by
      rw [hrewrite] at hdist
      dsimp [u] at hdist
      exact pow_le_pow_left₀ (norm_nonneg _) hdist 2
    exact (not_lt_of_ge hle_pow) hgt
  simpa [psi, hcvp]



/-- The open translates of the Voronoi interior cover space almost everywhere: the
closed Voronoi translates tile (`isAddFundamentalDomain_voronoi`), and the relative
boundary of each translate is null. -/
lemma voronoi_interior_translates_cover_ae {ℒ : Submodule ℤ E} [DiscreteTopology ℒ]
    [Countable ℒ] (hℒ : IsZLattice ℝ ℒ) :
    volume ((univ : Set E) \ ⋃ y : ℒ, ((y : E) +ᵥ interior (VC ℒ))) = 0 := by
  classical
  let Ucl : Set E := ⋃ y : ℒ, ((y : E) +ᵥ (VC ℒ : Set E))
  let Uop : Set E := ⋃ y : ℒ, ((y : E) +ᵥ interior (VC ℒ))
  let Bnd : Set E := ⋃ y : ℒ, ((y : E) +ᵥ ((VC ℒ : Set E) \ interior (VC ℒ)))
  -- closed translates cover a.e. (they are a fundamental-domain tiling):
  let C : Set E := {x | ∃ y : ℒ, (y : ℒ) +ᵥ x ∈ (VC ℒ : Set E)}
  have hCnull : volume ((univ : Set E) \ C) = 0 := by
    have fund := Submission.VoronoiMeasure.isAddFundamentalDomain_voronoi (ℒ := ℒ) hℒ
    have hCae : (∀ᵐ x ∂(volume : Measure E), x ∈ C) := by
      filter_upwards [fund.ae_covers] with x hx
      rcases hx with ⟨g, hg⟩
      exact ⟨g, hg⟩
    have hset : {a : E | a ∉ C} = (univ : Set E) \ C := by
      ext a
      simp
    rw [← hset]
    exact ae_iff.mp hCae
  have hCsub : C ⊆ Ucl := by
    intro x hx
    rcases hx with ⟨y, hy⟩
    rw [Set.mem_iUnion]
    refine ⟨-y, ?_⟩
    rw [Set.mem_vadd_set]
    refine ⟨(y : ℒ) +ᵥ x, ?_, ?_⟩
    · simpa using hy
    · change (-(y : E)) + (((y : ℒ) +ᵥ x)) = x
      rw [Submission.VoronoiMeasure.lattice_vadd_apply]
      abel
  have hcv : volume ((univ : Set E) \ Ucl) = 0 := by
    refine measure_mono_null ?_ hCnull
    intro x hx
    exact ⟨hx.1, fun hxC => hx.2 (hCsub hxC)⟩
  -- boundary translates are null:
  have hbd : volume Bnd = 0 := by
    dsimp [Bnd]
    rw [measure_iUnion_null]
    intro y
    have hb0 : volume (((VC ℒ : Set E) \ interior (VC ℒ))) = 0 :=
      volume_voronoi_boundary_zero (ℒ := ℒ)
    simpa using (MeasureTheory.measure_vadd (μ := (volume : Measure E)) (c := (y : E))
      (((VC ℒ : Set E) \ interior (VC ℒ)))).trans hb0
  -- main inclusion:
  have hsub : (univ : Set E) \ Uop ⊆ ((univ : Set E) \ Ucl) ∪ Bnd := by
    intro x hx
    by_cases hxU : x ∈ Ucl
    · -- x ∈ Ucl but x ∉ Uop : x lies in some boundary translate
      rw [Set.mem_iUnion] at hxU
      rcases hxU with ⟨y, hy⟩
      rw [Set.mem_vadd_set] at hy
      rcases hy with ⟨v, hvV, hxeq⟩
      have hvnot : v ∉ interior (VC ℒ) := by
        intro hvInt
        apply hx.2
        rw [Set.mem_iUnion]
        refine ⟨y, ?_⟩
        rw [Set.mem_vadd_set]
        exact ⟨v, hvInt, hxeq⟩
      right
      rw [Set.mem_iUnion]
      refine ⟨y, ?_⟩
      rw [Set.mem_vadd_set]
      exact ⟨v, ⟨hvV, hvnot⟩, hxeq⟩
    · left
      exact ⟨hx.1, hxU⟩
  have hA0 : volume ((univ : Set E) \ Ucl) = 0 := hcv
  have hB0 : volume Bnd = 0 := hbd
  have hle : volume ((univ : Set E) \ Uop) ≤ volume ((univ : Set E) \ Ucl) + volume Bnd := by
    calc
      volume ((univ : Set E) \ Uop) ≤ volume (((univ : Set E) \ Ucl) ∪ Bnd) := measure_mono hsub
      _ ≤ volume ((univ : Set E) \ Ucl) + volume Bnd := measure_union_le _ _
  have hle0 : volume ((univ : Set E) \ Uop) ≤ 0 := by
    rw [hA0, hB0] at hle
    simpa using hle
  have h0 : volume ((univ : Set E) \ Uop) = 0 := le_antisymm hle0 zero_le
  simpa [Uop] using h0

/-- The open pieces `{x ∈ interior K | x − y ∈ interior (VC ℒ)}` (`y : ℒ`) of the
interior of any set `K` tile it up to a null set (the interiors of the Voronoi
translates cover space a.e.). -/
lemma pieces_cover_interior_ae {ℒ : Submodule ℤ E} [DiscreteTopology ℒ] [Countable ℒ]
    (hℒ : IsZLattice ℝ ℒ) (K : Set E) :
    volume (interior K \ ⋃ y : ℒ, (interior K ∩ {x : E | x - (y : E) ∈ interior (VC ℒ)})) = 0 := by
  classical
  have hcov := voronoi_interior_translates_cover_ae (ℒ := ℒ) hℒ
  have hsub : interior K \ ⋃ y : ℒ, (interior K ∩ {x : E | x - (y : E) ∈ interior (VC ℒ)}) ⊆
      (univ : Set E) \ ⋃ y : ℒ, ((y : E) +ᵥ interior (VC ℒ)) := by
    intro x hx
    rcases hx with ⟨hxin, hxnot⟩
    refine ⟨trivial, ?_⟩
    intro hxU
    rw [Set.mem_iUnion] at hxU
    rcases hxU with ⟨y, hyU⟩
    have hP : x ∈ interior K ∩ {x : E | x - (y : E) ∈ interior (VC ℒ)} := by
      refine ⟨hxin, ?_⟩
      rw [Set.mem_vadd_set] at hyU
      rcases hyU with ⟨v, hv, hxeq⟩
      have hxeq' : (y : E) + v = x := by
        simpa [vadd_eq_add] using hxeq
      have hv' : x - (y : E) = v := by
        rw [← hxeq']
        abel
      simpa [hv'] using hv
    rw [Set.mem_iUnion] at hxnot
    exact hxnot ⟨y, hP⟩
  exact measure_mono_null hsub hcov



/-- The open cell of the lattice point `y` (points whose difference with `y` lies in the
interior of the Voronoi cell): the open `y`-translate of `Int V`. -/
def openCell {ℒ : Submodule ℤ E} (y : ℒ) : Set E := {x : E | x - (y : E) ∈ interior (VC ℒ)}

/-- The `y`-piece of the interior of `K` (a "fundamental body" candidate). -/
def piece {ℒ : Submodule ℤ E} (K : Set E) (y : ℒ) : Set E := interior K ∩ openCell y

/-- The open cell is open. -/
lemma openCell_isOpen {ℒ : Submodule ℤ E} (y : ℒ) : IsOpen (openCell y) := by
  dsimp [openCell]
  exact isOpen_interior.preimage (continuous_id.sub continuous_const)

/-- The open cell is measurable. -/
lemma openCell_measurableSet {ℒ : Submodule ℤ E} (y : ℒ) : MeasurableSet (openCell y) :=
  (openCell_isOpen y).measurableSet

/-- `piece K y` is open (hence measurable). -/
lemma piece_isOpen {ℒ : Submodule ℤ E} (K : Set E) (y : ℒ) : IsOpen (piece K y) := by
  dsimp [piece]
  exact isOpen_interior.inter (openCell_isOpen y)

/-- `piece K y` is measurable. -/
lemma piece_measurableSet {ℒ : Submodule ℤ E} (K : Set E) (y : ℒ) :
    MeasurableSet (piece K y) :=
  (piece_isOpen K y).measurableSet

/-- The open cells of distinct lattice points are disjoint. -/
lemma openCell_disjoint {ℒ : Submodule ℤ E} [DiscreteTopology ℒ] (y z : ℒ) (hyz : y ≠ z) :
    Disjoint (openCell y) (openCell z) := by
  rw [Set.disjoint_left]
  intro x hxy hxz
  let u : E := x - (y : E)
  let w : ℒ := z - y
  have hw0 : w ≠ 0 := sub_ne_zero.mpr hyz.symm
  have hu : u ∈ interior (VC ℒ) := by
    dsimp [openCell] at hxy
    simpa [u] using hxy
  have hstrict := (mem_interior_voronoi_iff (ℒ := ℒ) u).mp hu w hw0
  have huz : u - (w : E) ∈ (VC ℒ : Set E) := by
    have hEq : u - (w : E) = x - (z : E) := by
      dsimp [u, w]
      abel
    rw [hEq]
    dsimp [openCell] at hxz
    exact interior_subset hxz
  have hlen_le : ‖u - (w : E)‖ ≤ ‖u‖ := by
    have hmem := (Submission.VoronoiMeasure.mem_voronoi_iff_norm (ℒ := ℒ) (u - (w : E))).mp huz (-w)
    calc
      ‖u - (w : E)‖ ≤ ‖(u - (w : E)) - ((-w : ℒ) : E)‖ := by
        exact le_of_sq_le_sq hmem (norm_nonneg _)
      _ = ‖u‖ := by
        congr 1
        simp only [Submodule.coe_neg]
        abel
  have hsq_gt : ‖u‖ ^ 2 < ‖u - (w : E)‖ ^ 2 := by
    have hu_eq : ‖u - (w : E)‖ ^ 2 = ‖u‖ ^ 2 + ‖(w : E)‖ ^ 2 - 2 * ⟪u, (w : E)⟫_ℝ := by
      rw [norm_sub_sq_real]
      ring
    rw [hu_eq]
    nlinarith [hstrict]
  exact (not_le_of_gt hsq_gt) (pow_le_pow_left₀ (norm_nonneg (u - (w : E))) hlen_le 2)

/-- Membership in a piece. -/
lemma mem_piece_iff {ℒ : Submodule ℤ E} (K : Set E) (y : ℒ) (x : E) :
    x ∈ piece K y ↔ x ∈ interior K ∧ x - (y : E) ∈ interior (VC ℒ) := by
  rfl

/-- On the `y`-piece the closest-vector map is the translation by `y`. -/
lemma psi_eq_on_piece {ℒ : Submodule ℤ E} [DiscreteTopology ℒ]
    (hℒ : IsZLattice ℝ ℒ) (K : Set E) (y : ℒ) {x : E} (hx : x ∈ piece K y) :
    psi hℒ x = x - (y : E) := by
  exact psi_eq_of_voronoi_interior hℒ y x ((mem_piece_iff K y x).mp hx).2



noncomputable def psiCan {ℒ : Submodule ℤ E} [DiscreteTopology ℒ]
    (hℒ : IsZLattice ℝ ℒ) (x : E) : E := by
  classical
  exact if h : ∃ y : ℒ, x ∈ openCell y then x - ((Classical.choose h : ℒ) : E) else x

/-- On the open cell of `y`, `psiCan` is the translation by `y` (and agrees with `psi`). -/
lemma psiCan_eq_translate_of_mem_openCell {ℒ : Submodule ℤ E} [DiscreteTopology ℒ]
    (hℒ : IsZLattice ℝ ℒ) {y : ℒ} {x : E} (hx : x ∈ openCell y) :
    psiCan hℒ x = x - (y : E) := by
  classical
  have h : ∃ y : ℒ, x ∈ openCell y := ⟨y, hx⟩
  let y₀ : ℒ := Classical.choose h
  have hy₀ : x ∈ openCell y₀ := Classical.choose_spec h
  have hy₀y : y₀ = y := by
    by_contra hne
    have hd := openCell_disjoint y₀ y hne
    exact (Set.disjoint_left.mp hd) hy₀ hx
  unfold psiCan
  rw [dif_pos h]
  congr 1
  dsimp [y₀] at hy₀y
  rw [hy₀y]

/-- On the complement of the union of the open cells, `psiCan` is the identity. -/
lemma psiCan_eq_self {ℒ : Submodule ℤ E} [DiscreteTopology ℒ]
    (hℒ : IsZLattice ℝ ℒ) {x : E} (hx : x ∉ ⋃ y : ℒ, openCell y) :
    psiCan hℒ x = x := by
  classical
  have hnot : ¬ ∃ y : ℒ, x ∈ openCell y := by
    intro h
    exact hx (by
      rw [Set.mem_iUnion]
      exact ⟨Classical.choose h, Classical.choose_spec h⟩)
  unfold psiCan
  rw [dif_neg hnot]

/-- `psiCan` agrees with `psi` wherever `psi` is canonical (in particular on `Int K` a.e.). -/
lemma psiCan_eq_psi {ℒ : Submodule ℤ E} [DiscreteTopology ℒ]
    (hℒ : IsZLattice ℝ ℒ) {y : ℒ} {x : E} (hx : x ∈ openCell y) :
    psiCan hℒ x = psi hℒ x := by
  rw [psiCan_eq_translate_of_mem_openCell hℒ hx]
  exact (psi_eq_of_voronoi_interior hℒ y x (by
    dsimp [openCell] at hx
    exact hx)).symm

/-- `psiCan` shrinks the norm. -/
lemma norm_psiCan_le {ℒ : Submodule ℤ E} [DiscreteTopology ℒ]
    (hℒ : IsZLattice ℝ ℒ) (x : E) : ‖psiCan hℒ x‖ ≤ ‖x‖ := by
  classical
  by_cases h : ∃ y : ℒ, x ∈ openCell y
  · rcases h with ⟨y, hy⟩
    rw [psiCan_eq_translate_of_mem_openCell hℒ hy]
    have hpsi : psi hℒ x = x - (y : E) := psi_eq_of_voronoi_interior hℒ y x hy
    rw [← hpsi]
    exact norm_psi_le hℒ x
  · have hx : x ∉ ⋃ y : ℒ, openCell y := by
      intro hxmem
      rw [Set.mem_iUnion] at hxmem
      exact h hxmem
    rw [psiCan_eq_self hℒ hx]

/-- The image of a piece under `psiCan` is the translate of the piece. -/
lemma psiCan_image_piece_eq {ℒ : Submodule ℤ E} [DiscreteTopology ℒ]
    (hℒ : IsZLattice ℝ ℒ) (K : Set E) (A : Set E) (y : ℒ) :
    psiCan hℒ '' (A ∩ piece K y) = (fun x : E => x - (y : E)) '' (A ∩ piece K y) := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hxy : x ∈ openCell y := (mem_piece_iff K y x).mp hx.2 |>.2
    refine ⟨x, hx, ?_⟩
    exact (psiCan_eq_translate_of_mem_openCell hℒ hxy).symm
  · rintro ⟨x, hx, rfl⟩
    have hxy : x ∈ openCell y := (mem_piece_iff K y x).mp hx.2 |>.2
    refine ⟨x, hx, ?_⟩
    exact psiCan_eq_translate_of_mem_openCell hℒ hxy

/-- The image of a piece has the same volume as the piece (it is a translate). -/
lemma volume_psiCan_image_piece {ℒ : Submodule ℤ E} [DiscreteTopology ℒ]
    (hℒ : IsZLattice ℝ ℒ) (K A : Set E) (y : ℒ) :
    volume (psiCan hℒ '' (A ∩ piece K y)) = volume (A ∩ piece K y) := by
  rw [psiCan_image_piece_eq hℒ K A y]
  have htrans : (fun x : E => x - (y : E)) '' (A ∩ piece K y) =
      ((-(y : E)) +ᵥ (A ∩ piece K y)) := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [Set.mem_vadd_set]
      refine ⟨x, hx, ?_⟩
      change (-(y : E)) + x = x - (y : E)
      abel
    · rw [Set.mem_vadd_set]
      rintro ⟨x, hx, hz⟩
      refine ⟨x, hx, ?_⟩
      change x - (y : E) = z
      have hz' : -(y : E) + x = z := by simpa [vadd_eq_add] using hz
      rw [← hz']
      abel
  rw [htrans]
  exact MeasureTheory.measure_vadd (μ := (volume : Measure E)) (-(y : E)) (A ∩ piece K y)




/-- Distinct pieces have disjoint images under `psiCan` (injectivity of `psi` on
`interior K` + disjointness of the open cells). -/
lemma psiCan_image_piece_disjoint {ℒ : Submodule ℤ E} [DiscreteTopology ℒ]
    (hℒ : IsZLattice ℝ ℒ) (K : Set E)
    (hK : ∀ y : ℒ, y ≠ 0 → Disjoint (interior K) (((y : E) +ᵥ K)))
    (A : Set E) (hA : A ⊆ interior K) (y z : ℒ) (hyz : y ≠ z) :
    Disjoint (psiCan hℒ '' (A ∩ piece K y)) (psiCan hℒ '' (A ∩ piece K z)) := by
  rw [Set.disjoint_left]
  intro w hwy hwz
  rcases hwy with ⟨a, ha, hwa⟩
  rcases hwz with ⟨b, hb, hwb⟩
  have hya : a ∈ interior K := hA ha.1
  have hyb : b ∈ interior K := hA hb.1
  have hpsia : psiCan hℒ a = psi hℒ a := by
    exact psiCan_eq_psi hℒ ((mem_piece_iff K y a).mp ha.2 |>.2)
  have hpsib : psiCan hℒ b = psi hℒ b := by
    exact psiCan_eq_psi hℒ ((mem_piece_iff K z b).mp hb.2 |>.2)
  have hpeq : psi hℒ a = psi hℒ b := by
    have hcan : psiCan hℒ a = psiCan hℒ b := hwa.trans hwb.symm
    rw [hpsia, hpsib] at hcan
    exact hcan
  have hab : a = b := psi_injective_on_interior hℒ K hK hya hyb hpeq
  have hza : a ∈ openCell z := by
    have hbz : b ∈ openCell z := (mem_piece_iff K z b).mp hb.2 |>.2
    simpa [hab] using hbz
  have hya' : a ∈ openCell y := (mem_piece_iff K y a).mp ha.2 |>.2
  exact (Set.disjoint_left.mp (openCell_disjoint y z hyz)) hya' hza

/-- Measurability of the `psiCan`-image of a piece (it is a translate). -/
lemma measurableSet_psiCan_image_piece {ℒ : Submodule ℤ E} [DiscreteTopology ℒ]
    (hℒ : IsZLattice ℝ ℒ) (K A : Set E) (y : ℒ) (hAm : MeasurableSet A) :
    MeasurableSet (psiCan hℒ '' (A ∩ piece K y)) := by
  have htrans : psiCan hℒ '' (A ∩ piece K y) = ((-(y : E)) +ᵥ (A ∩ piece K y)) := by
    rw [psiCan_image_piece_eq hℒ K A y]
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [Set.mem_vadd_set]
      exact ⟨x, hx, by
        change (-(y : E)) + x = x - (y : E)
        abel⟩
    · rw [Set.mem_vadd_set]
      rintro ⟨x, hx, hz⟩
      refine ⟨x, hx, ?_⟩
      change x - (y : E) = z
      have hz' : -(y : E) + x = z := by simpa [vadd_eq_add] using hz
      rw [← hz']
      abel
  rw [htrans]
  exact MeasurableSet.const_vadd (hAm.inter (piece_measurableSet K y)) (-(y : E))

/-- Volume of the image of a piece under `psiCan` (a translate). -/
lemma volume_psiCan_image_piece' {ℒ : Submodule ℤ E} [DiscreteTopology ℒ]
    (hℒ : IsZLattice ℝ ℒ) (K A : Set E) (y : ℒ) :
    volume (psiCan hℒ '' (A ∩ piece K y)) = volume (A ∩ piece K y) :=
  volume_psiCan_image_piece hℒ K A y


/-- The image under `psiCan` of the union of the pieces has volume equal to the sum
of the image-piece volumes. -/
lemma volume_psiCan_image_tsum_pieces {ℒ : Submodule ℤ E} [DiscreteTopology ℒ]
    [Countable ℒ] (hℒ : IsZLattice ℝ ℒ) (K A : Set E)
    (hK : ∀ y : ℒ, y ≠ 0 → Disjoint (interior K) (((y : E) +ᵥ K)))
    (hA : A ⊆ interior K) (hAm : MeasurableSet A) :
    volume (psiCan hℒ '' (⋃ y : ℒ, (A ∩ piece K y))) =
      ∑' y : ℒ, volume (psiCan hℒ '' (A ∩ piece K y)) := by
  classical
  have himage_union : psiCan hℒ '' (⋃ y : ℒ, (A ∩ piece K y)) =
      ⋃ y : ℒ, (psiCan hℒ '' (A ∩ piece K y)) := by
    rw [Set.image_iUnion]
  rw [himage_union]
  exact measure_iUnion
    (by
      intro y z hyz
      exact psiCan_image_piece_disjoint hℒ K hK A hA y z hyz)
    (fun y => measurableSet_psiCan_image_piece hℒ K A y hAm)

/-- The canonical closest-vector map preserves the volume of measurable subsets of
the interior of a fundamental body: `vol (ψ₀''A) = vol A`. -/
theorem volume_psiCan_image {ℒ : Submodule ℤ E} [DiscreteTopology ℒ] [Countable ℒ]
    (hℒ : IsZLattice ℝ ℒ) (K A : Set E)
    (hK : ∀ y : ℒ, y ≠ 0 → Disjoint (interior K) (((y : E) +ᵥ K)))
    (hA : A ⊆ interior K) (hAm : MeasurableSet A) :
    volume (psiCan hℒ '' A) = volume A := by
  classical
  let P : ℒ → Set E := fun y => piece K y
  have hPmeas (y : ℒ) : MeasurableSet (P y) := by
    dsimp [P]
    exact piece_measurableSet K y
  have hPdisj : Pairwise (Function.onFun Disjoint P) := by
    intro y z hyz
    change Disjoint (P y) (P z)
    rw [Set.disjoint_left]
    intro x hxy hxz
    exact (Set.disjoint_left.mp (openCell_disjoint y z hyz)) hxy.2 hxz.2
  have hleft : volume ((interior K) \ ⋃ y : ℒ, P y) = 0 := by
    dsimp [P]
    simpa [piece, openCell] using (pieces_cover_interior_ae (ℒ := ℒ) hℒ K)
  let U : Set E := ⋃ y : ℒ, (A ∩ P y)
  have hAmem (y : ℒ) : MeasurableSet (A ∩ P y) := hAm.inter (hPmeas y)
  have hUmeas : MeasurableSet U := MeasurableSet.iUnion hAmem
  have hUA : U ⊆ A := by
    intro x hx
    rw [Set.mem_iUnion] at hx
    rcases hx with ⟨y, hxy⟩
    exact hxy.1
  have hAeqU : A = U ∪ (A \ U) := by
    ext x
    constructor
    · intro hxA
      by_cases hxU : x ∈ U
      · exact Or.inl hxU
      · exact Or.inr ⟨hxA, hxU⟩
    · intro hx
      rcases hx with hxU | hxAU
      · exact hUA hxU
      · exact hxAU.1
  have hnullAU : volume (A \ U) = 0 := by
    refine measure_mono_null ?_ hleft
    intro x hx
    rcases hx with ⟨hxA, hxU⟩
    refine ⟨hA hxA, ?_⟩
    intro hxP
    rw [Set.mem_iUnion] at hxP
    rcases hxP with ⟨y, hxy⟩
    exact hxU (by
      rw [Set.mem_iUnion]
      exact ⟨y, ⟨hxA, hxy⟩⟩)
  have hUvol : volume U = ∑' y : ℒ, volume (A ∩ P y) := by
    dsimp [U]
    exact measure_iUnion
      (by
        intro y z hyz
        change Disjoint (A ∩ P y) (A ∩ P z)
        rw [Set.disjoint_left]
        intro x hxy hxz
        exact (Set.disjoint_left.mp (hPdisj hyz)) hxy.2 hxz.2)
      hAmem
  have hvolA : volume A = ∑' y : ℒ, volume (A ∩ P y) := by
    calc
      volume A = volume (U ∪ (A \ U)) := by rw [← hAeqU]
      _ = volume U + volume (A \ U) := by
        exact measure_union (by
          rw [Set.disjoint_left]
          intro x hxU hxAU
          exact hxAU.2 hxU) (hAm.diff hUmeas)
      _ = volume U := by rw [hnullAU, add_zero]
      _ = ∑' y : ℒ, volume (A ∩ P y) := hUvol
  have hvolim : volume (psiCan hℒ '' U) = ∑' y : ℒ, volume (A ∩ P y) := by
    calc
      volume (psiCan hℒ '' U)
          = ∑' y : ℒ, volume (psiCan hℒ '' (A ∩ P y)) := by
            dsimp [U]
            exact volume_psiCan_image_tsum_pieces hℒ K A hK hA hAm
      _ = ∑' y : ℒ, volume (A ∩ P y) := by
        apply tsum_congr
        intro y
        exact volume_psiCan_image_piece' hℒ K A y
  have hnullim : volume (psiCan hℒ '' (A \ U)) = 0 := by
    have hid : psiCan hℒ '' (A \ U) = A \ U := by
      ext x
      constructor
      · rintro ⟨z, hz, rfl⟩
        have hznot : z ∉ ⋃ w : ℒ, openCell w := by
          intro hzw
          rw [Set.mem_iUnion] at hzw
          rcases hzw with ⟨w, hzw⟩
          exact hz.2 (by
            rw [Set.mem_iUnion]
            exact ⟨w, ⟨hz.1, ⟨hA hz.1, hzw⟩⟩⟩)
        have hzid : psiCan hℒ z = z := psiCan_eq_self hℒ hznot
        rw [hzid]
        exact hz
      · intro hx
        have hxnot : x ∉ ⋃ w : ℒ, openCell w := by
          intro hxw
          rw [Set.mem_iUnion] at hxw
          rcases hxw with ⟨w, hxw⟩
          exact hx.2 (by
            rw [Set.mem_iUnion]
            exact ⟨w, ⟨hx.1, ⟨hA hx.1, hxw⟩⟩⟩)
        have hxid : psiCan hℒ x = x := psiCan_eq_self hℒ hxnot
        rw [← hxid]
        exact ⟨x, hx, rfl⟩
    rw [hid]
    exact hnullAU
  have himU : psiCan hℒ '' A = (psiCan hℒ '' U) ∪ (psiCan hℒ '' (A \ U)) := by
    ext x
    constructor
    · rintro ⟨a, ha, rfl⟩
      by_cases haU : a ∈ U
      · exact Or.inl ⟨a, haU, rfl⟩
      · exact Or.inr ⟨a, ⟨ha, haU⟩, rfl⟩
    · intro hx
      rcases hx with hx | hx
      · rcases hx with ⟨a, haU, hxeq⟩
        exact ⟨a, hUA haU, hxeq⟩
      · rcases hx with ⟨a, haAU, hxeq⟩
        exact ⟨a, haAU.1, hxeq⟩
  calc
    volume (psiCan hℒ '' A) = volume ((psiCan hℒ '' U) ∪ (psiCan hℒ '' (A \ U))) := by
      rw [himU]
    _ = volume (psiCan hℒ '' U) := by
      apply le_antisymm
      · calc
          volume ((psiCan hℒ '' U) ∪ (psiCan hℒ '' (A \ U)))
              ≤ volume (psiCan hℒ '' U) + volume (psiCan hℒ '' (A \ U)) := measure_union_le _ _
          _ = volume (psiCan hℒ '' U) := by rw [hnullim, add_zero]
      · exact measure_mono (by intro x hx; exact Or.inl hx)
    _ = volume A := by rw [hvolim, hvolA]



/-- The interiors of two measurable fundamental domains have the same volume; in
particular `vol (interior K) = vol V` for a fundamental body `K` whose boundary is
null. -/
lemma volume_interior_eq_volume_voronoi {ℒ : Submodule ℤ E} [DiscreteTopology ℒ]
    [Countable ℒ] (hℒ : IsZLattice ℝ ℒ) (K : Set E) (hKmeas : MeasurableSet K)
    (hKfund : IsAddFundamentalDomain ℒ K)
    (hKboundary : volume (K \ interior K) = 0) :
    volume (interior K) = volume (VC ℒ : Set E) := by
  classical
  haveI : MeasurableConstVAdd ℒ E := ⟨fun g => by
    change Measurable (fun x : E => (g : E) + x)
    exact (continuous_const.add continuous_id).measurable⟩
  haveI : VAddInvariantMeasure ℒ E volume := ⟨fun g s hs => by
    simpa using (measurePreserving_add_left (μ := (volume : Measure E)) (g : E) s hs)⟩
  have hV : IsAddFundamentalDomain ℒ (VC ℒ : Set E) :=
    Submission.VoronoiMeasure.isAddFundamentalDomain_voronoi (ℒ := ℒ) hℒ
  have hKV : volume K = volume (VC ℒ : Set E) := IsAddFundamentalDomain.measure_eq hKfund hV
  have hKmeasInt : MeasurableSet (interior K) := isOpen_interior.measurableSet
  have hsplit : K = interior K ∪ (K \ interior K) := by
    ext x
    constructor
    · intro hx
      by_cases h : x ∈ interior K
      · exact Or.inl h
      · exact Or.inr ⟨hx, h⟩
    · intro hx
      rcases hx with hx | hx
      · exact interior_subset hx
      · exact hx.1
  have hvolsplit : volume K = volume (interior K) + volume (K \ interior K) := by
    calc
      volume K = volume (interior K ∪ (K \ interior K)) := congrArg volume hsplit
      _ = volume (interior K) + volume (K \ interior K) := by
        exact measure_union (by
          rw [Set.disjoint_left]
          intro x hxInt hxOut
          exact hxOut.2 hxInt) (hKmeas.diff hKmeasInt)
  have hKvol : volume (interior K) = volume K := by
    rw [hvolsplit, hKboundary, add_zero]
  calc
    volume (interior K) = volume K := hKvol
    _ = volume (VC ℒ : Set E) := hKV



/-- Per-piece substitution identity: on the `y`-piece `psiCan` is the translation
`x ↦ x − y`, so its integral over the piece equals the integral over its image. -/
lemma setIntegral_psiCan_piece {ℒ : Submodule ℤ E} [DiscreteTopology ℒ]
    (hℒ : IsZLattice ℝ ℒ) (K : Set E) (y : ℒ) (F : E → ℝ) :
    (∫ x in (psiCan hℒ '' (piece K y)), F x) = ∫ x in (piece K y), F (psiCan hℒ x) := by
  let T : E → E := fun x => -(y : E) + x
  have hTmp : MeasurePreserving T volume volume := by
    dsimp [T]
    exact measurePreserving_add_left (μ := (volume : Measure E)) (-(y : E))
  have hTemb : MeasurableEmbedding T := by
    dsimp [T]
    simpa [vadd_eq_add] using (measurableEmbedding_const_vadd (G := E) (α := E) (c := (-(y : E))))
  have hTimage : T '' (piece K y) = psiCan hℒ '' (piece K y) := by
    have heq := psiCan_image_piece_eq hℒ K (Set.univ : Set E) y
    simp at heq
    rw [heq]
    congr 1
    funext x
    dsimp [T]
    abel
  calc
    (∫ x in (psiCan hℒ '' (piece K y)), F x) = ∫ x in (T '' (piece K y)), F x := by
      rw [hTimage.symm]
    _ = ∫ x in (piece K y), F (T x) := by
      exact hTmp.setIntegral_image_emb hTemb F (piece K y)
    _ = ∫ x in (piece K y), F (psiCan hℒ x) := by
      refine setIntegral_congr_fun (piece_measurableSet K y) ?_
      intro x hx
      have hTψ : T x = psiCan hℒ x := by
        have hxy : x ∈ openCell y := (mem_piece_iff K y x).mp hx |>.2
        have hψ : psiCan hℒ x = x - (y : E) := psiCan_eq_translate_of_mem_openCell hℒ hxy
        rw [hψ]
        dsimp [T]
        abel
      exact congrArg F hTψ



/-- Step (i) of `monotone_Voronoi_wins`: if the boundary of `K` (relative to its
interior) is null, then integrals over `K` and over `interior K` agree. -/
lemma setIntegral_eq_interior_of_null_boundary (K : Set E)
    (hKboundary : volume (K \ interior K) = 0) (F : E → ℝ) :
    (∫ x in K, F x) = ∫ x in (interior K), F x := by
  have hsub : interior K ⊆ K := interior_subset
  have hnull2 : volume (interior K \ K) = 0 := by
    have hdiff : interior K \ K = ∅ := Set.sdiff_eq_empty.mpr hsub
    rw [hdiff]
    simp
  have hset : K =ᵐ[volume] interior K := by
    rw [ae_eq_set]
    exact ⟨hKboundary, hnull2⟩
  exact setIntegral_congr_set hset



/-- The pieces of the interior of `K` give a decomposition of the restricted volume. -/
lemma restrict_eq_sum_restrict_piece {ℒ : Submodule ℤ E} [DiscreteTopology ℒ]
    [Countable ℒ] (hℒ : IsZLattice ℝ ℒ) (K : Set E) :
    volume.restrict (interior K) = Measure.sum (fun y : ℒ => volume.restrict (piece K y)) := by
  classical
  have hleft : volume ((interior K) \ ⋃ y : ℒ, piece K y) = 0 := by
    simpa [piece, openCell] using (pieces_cover_interior_ae (ℒ := ℒ) hℒ K)
  have hsubU : (⋃ y : ℒ, piece K y) ⊆ interior K := by
    intro x hx
    rw [Set.mem_iUnion] at hx
    rcases hx with ⟨y, hy⟩
    exact (mem_piece_iff K y x).mp hy |>.1
  have hnull2 : volume ((⋃ y : ℒ, piece K y) \ interior K) = 0 := by
    have hdiff : (⋃ y : ℒ, piece K y) \ interior K = ∅ := Set.sdiff_eq_empty.mpr hsubU
    rw [hdiff]
    simp
  have hset : interior K =ᵐ[volume] ⋃ y : ℒ, piece K y := by
    rw [ae_eq_set]
    exact ⟨hleft, hnull2⟩
  calc
    volume.restrict (interior K) = volume.restrict (⋃ y : ℒ, piece K y) :=
      Measure.restrict_congr_set hset
    _ = Measure.sum (fun y : ℒ => volume.restrict (piece K y)) := by
      refine Measure.ext ?_
      intro T hTmeas
      rw [Measure.sum_apply (fun y : ℒ => volume.restrict (piece K y)) hTmeas]
      rw [Measure.restrict_apply hTmeas]
      rw [Set.inter_iUnion]
      rw [measure_iUnion (by
        intro y z hyz
        change Disjoint (T ∩ piece K y) (T ∩ piece K z)
        rw [Set.disjoint_left]
        intro x hxy hxz
        exact (Set.disjoint_left.mp (openCell_disjoint y z hyz)) hxy.2.2 hxz.2.2)
        (by
          intro i
          exact hTmeas.inter (piece_measurableSet K i))]
      apply tsum_congr
      intro y
      rw [Measure.restrict_apply hTmeas]

/-- Step (ii): integrals over the interior of `K` decompose over the pieces. -/
lemma setIntegral_eq_tsum_pieces {ℒ : Submodule ℤ E} [DiscreteTopology ℒ]
    [Countable ℒ] (hℒ : IsZLattice ℝ ℒ) (K : Set E) (H : E → ℝ)
    (hH : IntegrableOn H (interior K)) :
    (∫ x in (interior K), H x) = ∑' y : ℒ, ∫ x in (piece K y), H x := by
  have hrest := restrict_eq_sum_restrict_piece (ℒ := ℒ) hℒ K
  have hHsum : Integrable H (Measure.sum (fun y : ℒ => volume.restrict (piece K y))) := by
    rw [← hrest]
    exact hH
  calc
    (∫ x in (interior K), H x) = ∫ x, H x ∂(volume.restrict (interior K)) := by rfl
    _ = ∫ x, H x ∂(Measure.sum (fun y : ℒ => volume.restrict (piece K y))) := by rw [hrest]
    _ = ∑' y : ℒ, ∫ x, H x ∂(volume.restrict (piece K y)) := integral_sum_measure hHsum
    _ = ∑' y : ℒ, ∫ x in (piece K y), H x := by
      apply tsum_congr
      intro y
      rfl



/-- Pointwise radial monotonicity against `psiCan`: since `‖ψ₀x‖ ≤ ‖x‖`, a function
`F` that is non-increasing along the radial direction satisfies `F x ≤ F (ψ₀ x)`. -/
lemma F_le_psiCan {ℒ : Submodule ℤ E} [DiscreteTopology ℒ]
    (hℒ : IsZLattice ℝ ℒ) (F : E → ℝ)
    (hFmono : ∀ a b, ‖a‖ ≤ ‖b‖ → F b ≤ F a) (x : E) :
    F x ≤ F (psiCan hℒ x) := by
  exact hFmono (psiCan hℒ x) x (norm_psiCan_le hℒ x)

/-- Step (iii) of `monotone_Voronoi_wins`: the interior integral of `F` is at most the
interior integral of `F ∘ psiCan`. -/
lemma setIntegral_le_psiCan {ℒ : Submodule ℤ E} [DiscreteTopology ℒ]
    (hℒ : IsZLattice ℝ ℒ) (K : Set E) (F : E → ℝ)
    (hFmono : ∀ a b, ‖a‖ ≤ ‖b‖ → F b ≤ F a)
    (hFint : IntegrableOn F (interior K))
    (hFψint : IntegrableOn (fun x => F (psiCan hℒ x)) (interior K)) :
    (∫ x in (interior K), F x) ≤ ∫ x in (interior K), F (psiCan hℒ x) := by
  exact setIntegral_mono hFint hFψint (fun x => F_le_psiCan hℒ F hFmono x)



/-- Restriction over a disjoint measurable family: the restriction to the union is the
sum of the restrictions to the pieces. -/
lemma restrict_eq_sum_restrict_iUnion {ι : Type*} [Countable ι] {s : ι → Set E}
    (hmeas : ∀ i : ι, MeasurableSet (s i))
    (hdisj : Pairwise (Function.onFun Disjoint s)) :
    volume.restrict (⋃ i, s i) = Measure.sum (fun i : ι => volume.restrict (s i)) := by
  refine Measure.ext ?_
  intro T hTmeas
  rw [Measure.sum_apply (fun i : ι => volume.restrict (s i)) hTmeas]
  rw [Measure.restrict_apply hTmeas]
  rw [Set.inter_iUnion]
  rw [measure_iUnion (by
    intro i j hij
    change Disjoint (T ∩ s i) (T ∩ s j)
    rw [Set.disjoint_left]
    intro x hxi hxj
    exact (Set.disjoint_left.mp (hdisj hij)) hxi.2 hxj.2)
    (by
      intro i
      exact hTmeas.inter (hmeas i))]
  apply tsum_congr
  intro i
  rw [Measure.restrict_apply hTmeas]

/-- The restriction to the union of the `psiCan`-images of the pieces is the sum of the
restrictions to the individual images. -/
lemma restrict_eq_sum_restrict_image_piece {ℒ : Submodule ℤ E} [DiscreteTopology ℒ]
    [Countable ℒ] (hℒ : IsZLattice ℝ ℒ) (K : Set E)
    (hK : ∀ y : ℒ, y ≠ 0 → Disjoint (interior K) (((y : E) +ᵥ K))) :
    volume.restrict (⋃ y : ℒ, (psiCan hℒ '' (piece K y))) =
      Measure.sum (fun y : ℒ => volume.restrict (psiCan hℒ '' (piece K y))) := by
  classical
  let Q : ℒ → Set E := fun y => psiCan hℒ '' (piece K y)
  have hQmeas (y : ℒ) : MeasurableSet (Q y) := by
    dsimp [Q]
    have hm := measurableSet_psiCan_image_piece hℒ K (Set.univ : Set E) y
      (MeasurableSet.univ : MeasurableSet (Set.univ : Set E))
    -- hm : MeasurableSet (psiCan hℒ '' (univ ∩ piece K y))
    simpa using hm
  have hsub (w : ℒ) : piece K w ⊆ interior K := by
    intro x hx
    exact (mem_piece_iff K w x).mp hx |>.1
  have hQdisj : Pairwise (Function.onFun Disjoint Q) := by
    intro y z hyz
    change Disjoint (psiCan hℒ '' (piece K y)) (psiCan hℒ '' (piece K z))
    have hd := psiCan_image_piece_disjoint hℒ K hK (interior K) (fun x hx => hx) y z hyz
    have heq₁ : psiCan hℒ '' (interior K ∩ piece K y) = psiCan hℒ '' (piece K y) := by
      congr 1
      exact Set.inter_eq_right.mpr (hsub y)
    have heq₂ : psiCan hℒ '' (interior K ∩ piece K z) = psiCan hℒ '' (piece K z) := by
      congr 1
      exact Set.inter_eq_right.mpr (hsub z)
    rw [heq₁, heq₂] at hd
    exact hd
  simpa [Q] using restrict_eq_sum_restrict_iUnion hQmeas hQdisj



/-- The radial Gaussian integrand of the `γ_{1/t}`-mass: `F(x) = tⁿ·e^{−π(t‖x‖)²}`. -/
noncomputable def gaussianF (t : ℝ) : E → ℝ :=
  fun x => (t : ℝ) ^ n * rexp (-Real.pi * (t * ‖x‖) ^ 2)

/-- `gaussianF t` is nonnegative (for `t ≥ 0`). -/
lemma gaussianF_nonneg (t : ℝ) (ht : 0 ≤ t) (x : E) :
    0 ≤ gaussianF t x := by
  dsimp [gaussianF]
  exact mul_nonneg (pow_nonneg ht n) (le_of_lt (Real.exp_pos _))

/-- `gaussianF t` is (radially) non-increasing: `‖a‖ ≤ ‖b‖ ⟹ F b ≤ F a`. -/
lemma gaussianF_mono (t : ℝ) (ht : 0 ≤ t) {a b : E} (hab : ‖a‖ ≤ ‖b‖) :
    gaussianF t b ≤ gaussianF t a := by
  dsimp [gaussianF]
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg ht n)
  have hsq : (t * ‖a‖) ^ 2 ≤ (t * ‖b‖) ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg a) hab 2) (sq_nonneg t)]
  exact Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos.le, hsq])

/-- `gaussianF t` is integrable on the whole space (for `t > 0`). -/
lemma gaussianF_integrable (t : ℝ) (ht : 0 < t) :
    Integrable (fun x : E => gaussianF t x) := by
  have hs : 0 < (1 : ℝ) / t := one_div_pos.mpr ht
  have hg : Integrable (fun x : E => rexp (-Real.pi * ‖x‖ ^ 2 / (1 / t) ^ 2)) :=
    Submission.VoronoiMeasure.gaussian_integrable (1 / t) hs
  have hEq : (fun x : E => gaussianF t x) =
      fun x : E => (t : ℝ) ^ n * rexp (-Real.pi * ‖x‖ ^ 2 / (1 / t) ^ 2) := by
    funext x
    dsimp [gaussianF]
    have hsq : (t * ‖x‖) ^ 2 = ‖x‖ ^ 2 / (1 / t) ^ 2 := by
      field_simp [ht.ne']
    rw [hsq]
    congr 1
    ring
  rw [hEq]
  exact hg.const_mul ((t : ℝ) ^ n)



/-- The images of the pieces under `psiCan` lie in the Voronoi cell. -/
lemma image_piece_subset_voronoi {ℒ : Submodule ℤ E} [DiscreteTopology ℒ]
    (hℒ : IsZLattice ℝ ℒ) (K : Set E) :
    (⋃ y : ℒ, (psiCan hℒ '' (piece K y))) ⊆ (VC ℒ : Set E) := by
  intro x hx
  rw [Set.mem_iUnion] at hx
  rcases hx with ⟨y, hy⟩
  rcases hy with ⟨a, ha, rfl⟩
  -- a ∈ piece K y: psiCan a = a − y ∈ interior (VC ℒ) ⊆ VC
  have hxy : a ∈ openCell y := (mem_piece_iff K y a).mp ha |>.2
  have hψ : psiCan hℒ a = a - (y : E) := psiCan_eq_translate_of_mem_openCell hℒ hxy
  rw [hψ]
  exact interior_subset hxy

/-- The union of the piece images is a.e. the whole Voronoi cell. -/
lemma image_pieces_ae_voronoi {ℒ : Submodule ℤ E} [DiscreteTopology ℒ]
    [Countable ℒ] (hℒ : IsZLattice ℝ ℒ) (K : Set E) (hKmeas : MeasurableSet K)
    (hKfund : IsAddFundamentalDomain ℒ K)
    (hKdisj : ∀ y : ℒ, y ≠ 0 → Disjoint (interior K) (((y : E) +ᵥ K)))
    (hKboundary : volume (K \ interior K) = 0)
    (hVfin : volume (VC ℒ : Set E) ≠ ⊤) :
    (⋃ y : ℒ, (psiCan hℒ '' (piece K y))) =ᵐ[volume] (VC ℒ : Set E) := by
  classical
  let Q : ℒ → Set E := fun y => psiCan hℒ '' (piece K y)
  have hsub (y : ℒ) : piece K y ⊆ interior K := by
    intro x hx
    exact (mem_piece_iff K y x).mp hx |>.1
  have hQmeas (y : ℒ) : MeasurableSet (Q y) := by
    dsimp [Q]
    have hm := measurableSet_psiCan_image_piece hℒ K (Set.univ : Set E) y
      (MeasurableSet.univ : MeasurableSet (Set.univ : Set E))
    simpa using hm
  have hQdisj : Pairwise (Function.onFun Disjoint Q) := by
    intro y z hyz
    change Disjoint (psiCan hℒ '' (piece K y)) (psiCan hℒ '' (piece K z))
    have hd := psiCan_image_piece_disjoint hℒ K hKdisj (interior K) (fun x hx => hx) y z hyz
    have heq₁ : psiCan hℒ '' (interior K ∩ piece K y) = psiCan hℒ '' (piece K y) := by
      congr 1
      exact Set.inter_eq_right.mpr (hsub y)
    have heq₂ : psiCan hℒ '' (interior K ∩ piece K z) = psiCan hℒ '' (piece K z) := by
      congr 1
      exact Set.inter_eq_right.mpr (hsub z)
    rw [heq₁, heq₂] at hd
    exact hd
  have hvolQ : volume (⋃ y : ℒ, Q y) = ∑' y : ℒ, volume (Q y) := by
    dsimp [Q]
    exact measure_iUnion hQdisj hQmeas
  have hvolQpieces : (∑' y : ℒ, volume (Q y)) = ∑' y : ℒ, volume (piece K y) := by
    apply tsum_congr
    intro y
    dsimp [Q]
    simpa using volume_psiCan_image_piece hℒ K (Set.univ : Set E) y
  have hvolInt : (∑' y : ℒ, volume (piece K y)) = volume (interior K) := by
    -- from restrict_eq_sum_restrict_piece applied to univ
    have hrest := restrict_eq_sum_restrict_piece (ℒ := ℒ) hℒ K
    -- (restrict IntK) univ = vol IntK; Measure.sum side = Σ vol piece
    have hleft : volume.restrict (interior K) (Set.univ : Set E) = volume (interior K) := by
      rw [Measure.restrict_apply (MeasurableSet.univ : MeasurableSet (Set.univ : Set E))]
      simp
    have hright : (Measure.sum (fun y : ℒ => volume.restrict (piece K y))) (Set.univ : Set E) =
        ∑' y : ℒ, volume (piece K y) := by
      rw [Measure.sum_apply (fun y : ℒ => volume.restrict (piece K y))
        (MeasurableSet.univ : MeasurableSet (Set.univ : Set E))]
      apply tsum_congr
      intro y
      rw [Measure.restrict_apply (MeasurableSet.univ : MeasurableSet (Set.univ : Set E))]
      simp
    have heq := congrArg (fun m : Measure E => m (Set.univ : Set E)) hrest
    rw [hleft, hright] at heq
    exact heq.symm
  have hvolV : volume (interior K) = volume (VC ℒ : Set E) :=
    volume_interior_eq_volume_voronoi (ℒ := ℒ) hℒ K hKmeas hKfund hKboundary
  -- assemble vol (⋃Q) = vol V
  have hvol : volume (⋃ y : ℒ, Q y) = volume (VC ℒ : Set E) := by
    calc
      volume (⋃ y : ℒ, Q y) = ∑' y : ℒ, volume (Q y) := hvolQ
      _ = ∑' y : ℒ, volume (piece K y) := hvolQpieces
      _ = volume (interior K) := hvolInt
      _ = volume (VC ℒ : Set E) := hvolV
  -- ae_eq: ⋃Q =ᵐ V
  have hsubV : (⋃ y : ℒ, Q y) ⊆ (VC ℒ : Set E) := by
    simpa [Q] using image_piece_subset_voronoi hℒ K
  have hnull2 : volume (((⋃ y : ℒ, Q y)) \ (VC ℒ : Set E)) = 0 := by
    have hd : (⋃ y : ℒ, Q y) \ (VC ℒ : Set E) = ∅ := Set.sdiff_eq_empty.mpr hsubV
    rw [hd]
    simp
  have hVmeas : MeasurableSet (VC ℒ : Set E) := Submission.Voronoi.voronoi_measurable ℒ
  have hUmeas : MeasurableSet (⋃ y : ℒ, Q y) := MeasurableSet.iUnion hQmeas
  have hnull1 : volume ((VC ℒ : Set E) \ ⋃ y : ℒ, Q y) = 0 := by
    -- vol V = vol U + vol(V∖U) (V = U ∪ (V∖U)); vol U = vol V so difference = 0
    have hsplit : (VC ℒ : Set E) = (⋃ y : ℒ, Q y) ∪ ((VC ℒ : Set E) \ ⋃ y : ℒ, Q y) := by
      ext x
      constructor
      · intro hx
        by_cases hxU : x ∈ ⋃ y : ℒ, Q y
        · exact Or.inl hxU
        · exact Or.inr ⟨hx, hxU⟩
      · intro hx
        rcases hx with hxU | hxAU
        · exact hsubV hxU
        · exact hxAU.1
    have hvolsplit : volume (VC ℒ : Set E) =
        volume (⋃ y : ℒ, Q y) + volume ((VC ℒ : Set E) \ ⋃ y : ℒ, Q y) := by
      calc
        volume (VC ℒ : Set E)
            = volume ((⋃ y : ℒ, Q y) ∪ ((VC ℒ : Set E) \ ⋃ y : ℒ, Q y)) := congrArg volume hsplit
        _ = volume (⋃ y : ℒ, Q y) + volume ((VC ℒ : Set E) \ ⋃ y : ℒ, Q y) := by
          exact measure_union (by
            rw [Set.disjoint_left]
            intro x hxU hxAU
            exact hxAU.2 hxU) (hVmeas.diff hUmeas)
    have hUfin : volume (⋃ y : ℒ, Q y) ≠ ⊤ := by
      rw [hvol]
      exact hVfin
    have hres : volume ((VC ℒ : Set E) \ ⋃ y : ℒ, Q y) = volume (VC ℒ : Set E) - volume (⋃ y : ℒ, Q y) :=
      measure_sdiff hsubV hUmeas.nullMeasurableSet hUfin
    rw [hres, hvol]
    simp
  rw [ae_eq_set]
  exact ⟨hnull2, hnull1⟩

/-- **`monotone_Voronoi_wins`** — the Voronoi cell maximizes the integral of a radial
non-increasing function among fundamental bodies. -/
theorem monotone_voronoi_wins {ℒ : Submodule ℤ E} [DiscreteTopology ℒ] [Countable ℒ]
    (hℒ : IsZLattice ℝ ℒ) (K : Set E) (hKmeas : MeasurableSet K)
    (hKfund : IsAddFundamentalDomain ℒ K)
    (hKdisj : ∀ y : ℒ, y ≠ 0 → Disjoint (interior K) (((y : E) +ᵥ K)))
    (hKboundary : volume (K \ interior K) = 0)
    (F : E → ℝ) (hFmono : ∀ a b, ‖a‖ ≤ ‖b‖ → F b ≤ F a)
    (hFintInt : IntegrableOn F (interior K))
    (hFψint : IntegrableOn (fun x => F (psiCan hℒ x)) (interior K))
    (hFV : IntegrableOn F (VC ℒ : Set E)) (hVfin : volume (VC ℒ : Set E) ≠ ⊤) :
    (∫ x in K, F x) ≤ ∫ x in (VC ℒ : Set E), F x := by
  classical
  have h1 : (∫ x in K, F x) = ∫ x in (interior K), F x :=
    setIntegral_eq_interior_of_null_boundary K hKboundary F
  have h2 : (∫ x in (interior K), F x) ≤ ∫ x in (interior K), F (psiCan hℒ x) :=
    setIntegral_le_psiCan hℒ K F hFmono hFintInt hFψint
  have h3 : (∫ x in (interior K), F (psiCan hℒ x)) =
      ∑' y : ℒ, ∫ x in (piece K y), F (psiCan hℒ x) :=
    setIntegral_eq_tsum_pieces hℒ K (fun x => F (psiCan hℒ x)) hFψint
  have h4 : (∑' y : ℒ, ∫ x in (piece K y), F (psiCan hℒ x)) =
      ∑' y : ℒ, ∫ x in (psiCan hℒ '' (piece K y)), F x := by
    apply tsum_congr
    intro y
    exact (setIntegral_psiCan_piece hℒ K y F).symm
  have hrest := restrict_eq_sum_restrict_image_piece hℒ K hKdisj
  have hsubU : (⋃ y : ℒ, (psiCan hℒ '' (piece K y))) ⊆ (VC ℒ : Set E) :=
    image_piece_subset_voronoi hℒ K
  have hFU : IntegrableOn F (⋃ y : ℒ, (psiCan hℒ '' (piece K y))) := hFV.mono_set hsubU
  have hsumint : Integrable F (Measure.sum (fun y : ℒ => volume.restrict
      (psiCan hℒ '' (piece K y)))) := by
    rw [← hrest]
    exact hFU
  have h5 : (∑' y : ℒ, ∫ x in (psiCan hℒ '' (piece K y)), F x) =
      ∫ x in (⋃ y : ℒ, (psiCan hℒ '' (piece K y))), F x := by
    calc
      (∑' y : ℒ, ∫ x in (psiCan hℒ '' (piece K y)), F x)
          = ∑' y : ℒ, ∫ x, F x ∂(volume.restrict (psiCan hℒ '' (piece K y))) := by rfl
      _ = ∫ x, F x ∂(Measure.sum (fun y : ℒ => volume.restrict
            (psiCan hℒ '' (piece K y)))) := (integral_sum_measure hsumint).symm
      _ = ∫ x, F x ∂(volume.restrict (⋃ y : ℒ, (psiCan hℒ '' (piece K y)))) := by
        rw [hrest]
      _ = ∫ x in (⋃ y : ℒ, (psiCan hℒ '' (piece K y))), F x := by rfl
  have hae := image_pieces_ae_voronoi (ℒ := ℒ) hℒ K hKmeas hKfund hKdisj hKboundary hVfin
  have h6 : (∫ x in (⋃ y : ℒ, (psiCan hℒ '' (piece K y))), F x) =
      ∫ x in (VC ℒ : Set E), F x :=
    setIntegral_congr_set hae
  calc
    (∫ x in K, F x) ≤ ∫ x in (VC ℒ : Set E), F x := by
      rw [h1]
      calc
        (∫ x in (interior K), F x) ≤ ∫ x in (interior K), F (psiCan hℒ x) := h2
        _ = ∫ x in (VC ℒ : Set E), F x := by
          rw [h3, h4, h5, h6]



/-- The direct-sum body `V(Q) + V(ℒ')` (Minkowski sum) of the Voronoi cells of two
lattices living in complementary orthogonal subspaces — the product body used by
`fundamental_product`. -/
noncomputable def productBody (Q ℒ' : Submodule ℤ E) : Set E :=
  (VC Q : Set E) + (VC ℒ' : Set E)

/-- Membership in the Minkowski-sum body. -/
lemma mem_productBody_iff (Q ℒ' : Submodule ℤ E) (x : E) :
    x ∈ productBody Q ℒ' ↔
      ∃ a ∈ (VC Q : Set E), ∃ b ∈ (VC ℒ' : Set E), a + b = x := by
  dsimp [productBody]
  exact Set.mem_add


/-- The sum of a `Q`-cell point and an `ℒ'`-cell point lies in the product body. -/
lemma productBody_add_mem (Q ℒ' : Submodule ℤ E) {a b : E}
    (ha : a ∈ (VC Q : Set E)) (hb : b ∈ (VC ℒ' : Set E)) :
    a + b ∈ productBody Q ℒ' := by
  dsimp [productBody]
  exact Set.add_mem_add ha hb



/-- The quotient lattice `ℒ/S` lies in the orthogonal complement of `S`. -/
lemma quotLattice_subset_orthogonal {ℒ : Submodule ℤ E} (S : Submodule ℝ E) :
    ((Submission.QuotientLattice.quotLattice ℒ S : Submodule ℤ E) : Set E) ⊆ (Sᗮ : Set E) := by
  intro x hx
  unfold Submission.QuotientLattice.quotLattice at hx
  change x ∈ Submodule.map ((Sᗮ.starProjection : E →ₗ[ℝ] E).restrictScalars ℤ) ℒ at hx
  rcases (Submodule.mem_map.mp hx) with ⟨y, hy, hxy⟩
  have hx' : x = Sᗮ.starProjection y := hxy.symm
  rw [hx']
  exact Submodule.starProjection_apply_mem Sᗮ y



/-- Rank-one determinant-quotient: for a primitive rank-one sublattice `ℤ·v` of `ℒ`,
`det(ℒ/(ℤ·v)) = det ℒ / ‖v‖`. -/
lemma det_quot_rank_one (ℒ : Submodule ℤ E) [DiscreteTopology ℒ]
    (v : E) (hvL : v ∈ ℒ) (hv : v ≠ 0)
    (hprim : Submission.QuotientLattice.Primitive (Submodule.span ℤ ({v} : Set E)) ℒ)
    [DiscreteTopology (Submission.QuotientLattice.quotLattice ℒ
      (Submission.QuotientLattice.realSpan (Submodule.span ℤ ({v} : Set E))))] :
    ReverseMinkowski.determinant
        (Submission.QuotientLattice.quotLattice ℒ
          (Submission.QuotientLattice.realSpan (Submodule.span ℤ ({v} : Set E)))) =
      ReverseMinkowski.determinant ℒ / ‖v‖ := by
  classical
  let ℒ' : Submodule ℤ E := Submodule.span ℤ ({v} : Set E)
  haveI : DiscreteTopology ℒ' := by
    dsimp [ℒ']
    have hle : Submodule.span ℤ ({v} : Set E) ≤ ℒ := by
      exact Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hvL)
    exact Submission.LatticeBasics.discreteTopology_of_le (ℒ := ℒ) (ℒ' := Submodule.span ℤ ({v} : Set E)) hle
  have hdetL' : ReverseMinkowski.determinant ℒ' = ‖v‖ := by
    dsimp [ℒ']
    exact Submission.Determinant.det_eq_norm_of_generator (Submodule.span ℤ ({v} : Set E))
      (Submodule.subset_span (by simp)) (fun hz => hv hz) rfl
  have hmain : ReverseMinkowski.determinant
        (Submission.QuotientLattice.quotLattice ℒ (Submission.QuotientLattice.realSpan ℒ')) =
      ReverseMinkowski.determinant ℒ / ReverseMinkowski.determinant ℒ' := by
    exact Submission.SubLattice.determinant_quot_generic (ℒ' := ℒ') (ℒ := ℒ)
      (S := Submission.QuotientLattice.realSpan ℒ') rfl hprim
  rw [hdetL'] at hmain
  dsimp [ℒ'] at hmain ⊢
  exact hmain


end Submission.Cvp
