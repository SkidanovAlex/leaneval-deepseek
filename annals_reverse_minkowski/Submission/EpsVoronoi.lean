import Mathlib
import Submission.Voronoi
import Submission.ShapeDeriv
import Submission.StableLattices
import Submission.CoveringRadius
import Submission.Commons.Analysis.Convex.smul_add_ball_subset_smul

open Module Real MeasureTheory Matrix
open MeasureTheory MeasureTheory.Measure
open scoped Real BigOperators Pointwise InnerProductSpace RealInnerProductSpace
set_option autoImplicit false
set_option maxHeartbeats 800000

/-!
# [C2] eps-Voronoi inclusions (paper `clm:eps_voronoi`, first half)

For a lattice `ℒ ≤ E` whose Voronoi cell `V := voronoi ℒ` contains the ball of radius `r`
(`λ₁/2` in the paper) and is contained in the ball of radius `R` (a covering-radius-type
bound), any linear map `A` that moves every point by at most `ε‖x‖` (`A := I + M` with
`ε := ‖M‖` in the application) satisfies the smooth-image inclusions of
`clm:eps_voronoi`:

* `A '' V ⊆ (1 + εR/r) • V` (`image_cell_subset_scale`) — points of the image cell are
  within `εR` of `V`, and `V + ball(0, εR) ⊆ (1 + εR/r)·V` since `V` is convex,
  contains `0`, and contains `ball(0, r)` (`Commons...smul_add_ball_subset_smul`);
* `V ⊆ A '' V +ᵥ ball(0, εR)` (`cell_subset_image_add_ball`) — the reverse inclusion at
  the Minkowski-sum level (a perturbed point `x = Ax + (x−Ax)`, `‖x−Ax‖ ≤ εR`).

Together with the analogous inclusions for `V(A·ℒ)` (whose half-space bounds shift by the
same `ε` — the remaining part of `clm:eps_voronoi`) these give the Hausdorff-`O(ε)`
proximity of the three cells `V`, `A·V`, `V(A·ℒ)` that `thm:same_grad_VL` needs to
identify the cell-side and smooth-side derivatives.  Placeholder of the eventual glue: all
statements are parameterized by concrete `r`, `R`, `ε` and the pointwise map bound, so any
lattice (stable ⇒ `r = 1/2`, covering-radius ⇒ `R`) instantiates them directly.
-/

namespace Submission.EpsVoronoi

variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "VC" => Submission.Voronoi.voronoi

/-- The origin lies in the Voronoi cell. -/
lemma zero_mem_voronoi (ℒ : Submodule ℤ E) : (0 : E) ∈ VC ℒ := by
  rw [Submission.Voronoi.mem_voronoi]
  intro y
  simp only [inner_zero_left]
  exact div_nonneg (sq_nonneg ‖(y : E)‖) (by norm_num)

/-- `x ∈ K +ᵥ ball(0,ε)` once some `v ∈ K` is `ε`-close to `x`. -/
lemma mem_vadd_ball (K : Set E) {v x : E} {ε : ℝ} (hv : v ∈ K) (h : ‖x - v‖ ≤ ε) :
    x ∈ K +ᵥ Metric.closedBall (0 : E) ε := by
  refine ⟨v, hv, x - v, ?_, ?_⟩
  · rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
    exact h
  · abel

/-- **Forward eps-cell inclusion (image side).**  With `ball r ⊆ V ⊆ ball R` and
`A` moving points by at most `ε‖x‖`, the image cell lies in the `(1 + εR/r)`-scaled cell. -/
theorem image_cell_subset_scale {ℒ : Submodule ℤ E} (r R : ℝ) (hr : 0 < r) (hR : 0 ≤ R)
    (hball : Metric.closedBall (0 : E) r ⊆ VC ℒ)
    (hcell : VC ℒ ⊆ Metric.closedBall (0 : E) R)
    (A : E →ₗ[ℝ] E) (ε : ℝ) (hε0 : 0 ≤ ε) (hA : ∀ x, ‖A x - x‖ ≤ ε * ‖x‖) :
    A '' VC ℒ ⊆ (1 + ε * R / r) • VC ℒ := by
  intro x hx
  rw [Set.mem_image] at hx
  rcases hx with ⟨v, hv, hxeq⟩
  have hvR : ‖v‖ ≤ R := by
    have hb := Metric.mem_closedBall.mp (hcell hv)
    simpa [dist_eq_norm] using hb
  have hAv : ‖A v - v‖ ≤ ε * R := by
    calc
      ‖A v - v‖ ≤ ε * ‖v‖ := hA v
      _ ≤ ε * R := mul_le_mul_of_nonneg_left hvR hε0
  let t : ℝ := ε * R / r
  have htr : t * r = ε * R := by
    dsimp [t]
    field_simp [ne_of_gt hr]
  have hsum : x ∈ VC ℒ +ᵥ Metric.closedBall (0 : E) (t * r) := by
    rw [← hxeq]
    exact mem_vadd_ball (VC ℒ) (v := v) (x := A v) (ε := t * r) hv (by simpa [htr] using hAv)
  have hinc : VC ℒ +ᵥ Metric.closedBall (0 : E) (t * r) ⊆ (1 + t) • VC ℒ := by
    have ht0 : 0 ≤ t := by
      dsimp [t]
      exact div_nonneg (mul_nonneg hε0 hR) (le_of_lt hr)
    have hcm := Commons.Analysis.Convex.smul_add_ball_subset_smul (n := n) (C := VC ℒ)
      (t₁ := 1) (t₂ := 1 + t)
      (Submission.Voronoi.voronoi_convex ℒ) (zero_mem_voronoi ℒ)
      (hr := le_of_lt hr) (ht₁ := by norm_num) (ht := by linarith [ht0]) hball
    have hrad : (1 + t - 1) * r = t * r := by ring
    simpa [hrad] using hcm
  exact hinc hsum

/-- **Reverse eps-cell inclusion (image side, Minkowski form).**  With `V ⊆ ball R` and
`A` moving points by at most `ε‖x‖`, `V ⊆ A·V + ball(0, εR)`. -/
theorem cell_subset_image_add_ball {ℒ : Submodule ℤ E} (R : ℝ)
    (hcell : VC ℒ ⊆ Metric.closedBall (0 : E) R)
    (A : E →ₗ[ℝ] E) (ε : ℝ) (hε0 : 0 ≤ ε) (hA : ∀ x, ‖A x - x‖ ≤ ε * ‖x‖) :
    VC ℒ ⊆ A '' VC ℒ +ᵥ Metric.closedBall (0 : E) (ε * R) := by
  intro x hx
  have hxR : ‖x‖ ≤ R := by
    have hb := Metric.mem_closedBall.mp (hcell hx)
    simpa [dist_eq_norm] using hb
  have hAx : ‖A x - x‖ ≤ ε * R := by
    calc
      ‖A x - x‖ ≤ ε * ‖x‖ := hA x
      _ ≤ ε * R := mul_le_mul_of_nonneg_left hxR hε0
  refine ⟨A x, ?_, x - A x, ?_, ?_⟩
  · refine ⟨x, hx, rfl⟩
  · rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, norm_sub_rev]
    exact hAx
  · abel


/-! ## Matrix instantiation of the eps-cell inclusion (stable lattices)

Concretely: a STABLE full-rank lattice `ℒ` has Voronoi cell containing `ball(0, 1/2)`
(`half_ball_subset_voronoi_of_stable`, inradius `λ₁/2 ≥ 1/2`), and contained in the
`closedBall 0 R(b)` for any `ℤ`-basis `b` (`CoveringRadius.voronoi_subset_closedBall_basis`).
For any perturbation matrix `M` there is a Lipschitz constant `L` for `x ↦ mvec M x`
(`ShapeDeriv.mvec_bound`), and `mvec (1 + M) x = x + mvec M x` (`ShapeDeriv.path_eq`), so
`‖mvec (1+M) x − x‖ ≤ L‖x‖`; the eps-inclusion `image_cell_subset_scale` applies with
`r = 1/2`, `R = R(b)`, `ε = L`.  This is the matrix-position form of the forward
`clm:eps_voronoi` inclusion (paper Eq. (Voronoi_claimed_inclusion_1)) used to compare the
cell-side and smooth-side functionals over det-one perturbations of a stable minimizer. -/

/-- For a stable full-rank lattice and a perturbation matrix `M`, the image of the Voronoi
cell under `mvec (1 + M)` lies in the `(1 + L·R(b)/(1/2))`-scaled cell for some `L > 0`. -/
theorem stable_image_cell_eps {ℒ : Submodule ℤ E} [DiscreteTopology ℒ]
    (hℒ : IsZLattice ℝ ℒ) (hSt : Submission.StableLattices.Stable ℒ)
    (b : Module.Basis (Fin n) ℤ ℒ) (M : Matrix (Fin n) (Fin n) ℝ) :
    ∃ L : ℝ, 0 < L ∧
      (Submission.ShapeDeriv.mvec ((1 : Matrix (Fin n) (Fin n) ℝ) + M)) '' VC ℒ
        ⊆ (1 + L * (∑ i : Fin n, ‖((b i : ℒ) : E)‖) / (1 / 2)) • VC ℒ := by
  rcases Submission.ShapeDeriv.mvec_bound M with ⟨L, hLpos, hLip⟩
  refine ⟨L, hLpos, ?_⟩
  let R : ℝ := ∑ i : Fin n, ‖((b i : ℒ) : E)‖
  have hball : Metric.closedBall (0 : E) (1 / 2) ⊆ VC ℒ :=
    Submission.StableLattices.half_ball_subset_voronoi_of_stable hSt
  have hcell : VC ℒ ⊆ Metric.closedBall (0 : E) R := by
    simpa [R] using (Submission.CoveringRadius.voronoi_subset_closedBall_basis ℒ hℒ b)
  have hR : 0 ≤ R := by
    dsimp [R]
    positivity
  have hA : ∀ x : E, ‖Submission.ShapeDeriv.mvec ((1 : Matrix (Fin n) (Fin n) ℝ) + M) x - x‖ ≤ L * ‖x‖ := by
    intro x
    have hp : Submission.ShapeDeriv.mvec ((1 : Matrix (Fin n) (Fin n) ℝ) + M) x = x + Submission.ShapeDeriv.mvec M x := by
      simpa using (Submission.ShapeDeriv.path_eq (M := M) (t := 1) x)
    rw [hp]
    have hcancel : (x + Submission.ShapeDeriv.mvec M x) - x = Submission.ShapeDeriv.mvec M x := by
      abel
    rw [hcancel]
    exact hLip x
  have hmain := image_cell_subset_scale (ℒ := ℒ) (r := 1 / 2) (R := R)
    (hr := by norm_num) (hR := hR) (hball := hball) (hcell := hcell)
    (A := Submission.ShapeDeriv.mvec ((1 : Matrix (Fin n) (Fin n) ℝ) + M))
    (ε := L) (hε0 := le_of_lt hLpos) (hA := hA)
  simpa [R] using hmain



/-! ## [C2b] The `V(A·ℒ)`-side scaled inclusion (paper `clm:eps_voronoi`, second half)

For `A` moving every point by at most `ε‖x‖` (`ε ≤ 1/2`), the Voronoi cell `V(A·ℒ)` of the
image lattice (here the set `voronoiImage A ℒ := {x | ∀ z ∈ ℒ, ⟨x, Az⟩ ≤ ‖Az‖²/2}`, which
agrees with `voronoi` of the image submodule once glued) satisfies the paper's left
containment of Eq. (Voronoi_claimed_inclusion_2):

`( (1−ε)² / (1 + 2εR/r) ) · V(ℒ) ⊆ V(A·ℒ)`

where `ball r ⊆ V(ℒ)` (λ₁/2), `V(ℒ) ⊆ ball R` (covering radius) and `λ₁ ≥ r`.  The engine
is the α-homothety half-space estimate `halfspace_perturbed`: for `x ∈ V(ℒ)`,
`‖x‖ ≤ R`, `0 ≠ z ∈ ℒ`,
`⟨Az, x⟩ ≤ (‖Az‖²/2) · (1 + 2εR/r)/(1−ε)²`
(⟨z,x⟩ ≤ ‖z‖²/2 from `x ∈ V(ℒ)`, deviation `⟨Az−z,x⟩ ≤ ε‖z‖‖x‖`, and
`‖Az‖ ≥ (1−ε)‖z‖`); rescaling by `s := (1−ε)²/(1+2εR/r)` (`s·β = 1`) gives the
membership lemma `scale_mem_voronoiImage` and the inclusion.
-/

/-- the Voronoi cell of the `A`-image of `ℒ` (paper `V(A·Λ)`) -/
def voronoiImage (A : E →ₗ[ℝ] E) (ℒ : Submodule ℤ E) : Set E :=
  {x | ∀ z : ℒ, ⟪x, A (z : E)⟫_ℝ ≤ ‖A (z : E)‖ ^ 2 / 2}

/-- membership in the Voronoi cell of the image lattice -/
lemma mem_voronoiImage {A : E →ₗ[ℝ] E} {ℒ : Submodule ℤ E} {x : E} :
    x ∈ voronoiImage A ℒ ↔ ∀ z : ℒ, ⟪x, A (z : E)⟫_ℝ ≤ ‖A (z : E)‖ ^ 2 / 2 := by
  rfl

/-- ‖A z‖ ≥ (1−ε)‖z‖ from ‖A z − z‖ ≤ ε‖z‖. -/
lemma norm_lower_image (ε : ℝ) (hε0 : 0 ≤ ε)
    {A : E →ₗ[ℝ] E} (hA : ∀ w : E, ‖A w - w‖ ≤ ε * ‖w‖) (z : E) :
    (1 - ε) * ‖z‖ ≤ ‖A z‖ := by
  have htri : ‖z‖ ≤ ‖A z‖ + ‖A z - z‖ := by
    calc
      ‖z‖ = ‖A z + (z - A z)‖ := by
        congr 1
        abel
      _ ≤ ‖A z‖ + ‖z - A z‖ := norm_add_le _ _
      _ = ‖A z‖ + ‖A z - z‖ := by rw [norm_sub_rev]
  have hb : ‖A z - z‖ ≤ ε * ‖z‖ := hA z
  linarith

/-- inner-product deviation bound: `⟨A z − z, x⟩ ≤ ε·‖z‖·‖x‖`. -/
lemma inner_dev_le (ε : ℝ) (hε0 : 0 ≤ ε)
    {A : E →ₗ[ℝ] E} (hA : ∀ w : E, ‖A w - w‖ ≤ ε * ‖w‖) (z x : E) :
    ⟪A z - z, x⟫_ℝ ≤ ε * ‖z‖ * ‖x‖ := by
  calc
    ⟪A z - z, x⟫_ℝ ≤ |⟪A z - z, x⟫_ℝ| := le_abs_self _
    _ ≤ ‖A z - z‖ * ‖x‖ := abs_real_inner_le_norm (A z - z) x
    _ ≤ (ε * ‖z‖) * ‖x‖ := mul_le_mul_of_nonneg_right (hA z) (norm_nonneg x)
    _ = ε * ‖z‖ * ‖x‖ := by ring

/-- **The α-homothety half-space estimate.**  For `x ∈ V(ℒ)` with `‖x‖ ≤ R`, `λ₁ ≥ r`,
`ε ≤ 1/2`, and `0 ≠ z ∈ ℒ`:
`⟨A z, x⟩ ≤ (‖A z‖²/2)·(1 + 2εR/r)/(1−ε)²`. -/
lemma halfspace_perturbed (r R ε : ℝ) (hr : 0 < r) (hR0 : 0 ≤ R) (hε1 : ε ≤ 1 / 2)
    (hε0 : 0 ≤ ε)
    {ℒ : Submodule ℤ E} {A : E →ₗ[ℝ] E}
    (hlam : ∀ z : ℒ, z ≠ 0 → r ≤ ‖(z : E)‖)
    (hA : ∀ w : E, ‖A w - w‖ ≤ ε * ‖w‖)
    {x : E} (hx : x ∈ VC ℒ) (hxR : ‖x‖ ≤ R) {z : ℒ} (hz : z ≠ 0) :
    ⟪A (z : E), x⟫_ℝ ≤ ‖A (z : E)‖ ^ 2 / 2 * ((1 + 2 * ε * R / r) / (1 - ε) ^ 2) := by
  let w : ℝ := ‖(z : E)‖
  have hwr : r ≤ w := by
    dsimp [w]
    exact hlam z hz
  have hwpos : 0 < w := lt_of_lt_of_le hr hwr
  have h1em : 0 < 1 - ε := by linarith
  have hβ : 0 ≤ (1 + 2 * ε * R / r) / (1 - ε) ^ 2 := by
    have hnum : 0 ≤ 1 + 2 * ε * R / r := by
      have hn : 0 ≤ 2 * ε * R / r := by
        exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hε0) hR0) (le_of_lt hr)
      linarith
    exact div_nonneg hnum (sq_nonneg (1 - ε))
  have hcell := (Submission.Voronoi.mem_voronoi (ℒ := ℒ)).mp hx
  have hzx : ⟪(z : E), x⟫_ℝ ≤ w ^ 2 / 2 := by
    rw [real_inner_comm]
    have hc := hcell z
    simpa [w] using hc
  have hdev : ⟪A (z : E) - (z : E), x⟫_ℝ ≤ ε * w * R := by
    have h1 := inner_dev_le ε hε0 hA (z : E) x
    calc
      ⟪A (z : E) - (z : E), x⟫_ℝ ≤ ε * ‖(z : E)‖ * ‖x‖ := h1
      _ = ε * w * ‖x‖ := by dsimp [w]
      _ ≤ ε * w * R := by
        exact mul_le_mul_of_nonneg_left hxR (mul_nonneg hε0 (by positivity : 0 ≤ w))
  have hmain : ⟪A (z : E), x⟫_ℝ ≤ w ^ 2 / 2 + ε * w * R := by
    have hdec : ⟪A (z : E), x⟫_ℝ = ⟪(z : E), x⟫_ℝ + ⟪A (z : E) - (z : E), x⟫_ℝ := by
      rw [show A (z : E) = (z : E) + (A (z : E) - (z : E)) by abel]
      rw [inner_add_left]
      simp
    rw [hdec]
    nlinarith [hzx, hdev]
  have hl := norm_lower_image ε hε0 hA (z : E)
  have hsq : (1 - ε) ^ 2 * w ^ 2 ≤ ‖A (z : E)‖ ^ 2 := by
    have h1n : 0 ≤ (1 - ε) * w := mul_nonneg (le_of_lt h1em) (le_of_lt hwpos)
    have habs : |(1 - ε) * w| ≤ |‖A (z : E)‖| := by
      rw [abs_of_nonneg h1n, abs_of_nonneg (norm_nonneg _)]
      dsimp [w] at hl ⊢
      exact hl
    have hs := sq_le_sq.mpr habs
    have h : ((1 - ε) * w) ^ 2 = (1 - ε) ^ 2 * w ^ 2 := by ring
    rwa [h] at hs
  have hrec : w⁻¹ ≤ r⁻¹ := by
    simpa using (one_div_le_one_div_of_le hr hwr)
  have hmain2 : w ^ 2 / 2 + ε * w * R ≤ w ^ 2 / 2 * (1 + 2 * ε * R / r) := by
    calc
      w ^ 2 / 2 + ε * w * R = w ^ 2 / 2 * (1 + (2 * ε * R / w)) := by
        field_simp [hwpos.ne']
      _ ≤ w ^ 2 / 2 * (1 + 2 * ε * R / r) := by
        have h2 : (2 * ε * R) / w ≤ (2 * ε * R) / r := by
          have h2' : (2 * ε * R) * w⁻¹ ≤ (2 * ε * R) * r⁻¹ :=
            mul_le_mul_of_nonneg_left hrec (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hε0) hR0)
          simpa [div_eq_mul_inv] using h2'
        have h12 : 1 + 2 * ε * R / w ≤ 1 + 2 * ε * R / r := add_le_add (le_rfl : (1 : ℝ) ≤ 1) h2
        exact mul_le_mul_of_nonneg_left h12 (by positivity)
  have hfin : w ^ 2 / 2 * (1 + 2 * ε * R / r) ≤ ‖A (z : E)‖ ^ 2 / 2 * ((1 + 2 * ε * R / r) / (1 - ε) ^ 2) := by
    calc
      w ^ 2 / 2 * (1 + 2 * ε * R / r)
          = ((1 - ε) ^ 2 * w ^ 2) / 2 * ((1 + 2 * ε * R / r) / (1 - ε) ^ 2) := by
            field_simp [ne_of_gt h1em]
      _ ≤ ‖A (z : E)‖ ^ 2 / 2 * ((1 + 2 * ε * R / r) / (1 - ε) ^ 2) := by
            have hh : ((1 - ε) ^ 2 * w ^ 2) / 2 ≤ ‖A (z : E)‖ ^ 2 / 2 := by nlinarith [hsq]
            exact mul_le_mul_of_nonneg_right hh hβ
  nlinarith [hmain, hmain2, hfin]

/-- scaled cell vectors lie in the Voronoi cell of the A-image lattice -/
lemma scale_mem_voronoiImage (r R ε : ℝ) (hr : 0 < r) (hR0 : 0 ≤ R) (hε1 : ε ≤ 1 / 2)
    (hε0 : 0 ≤ ε)
    {ℒ : Submodule ℤ E} {A : E →ₗ[ℝ] E}
    (hlam : ∀ z : ℒ, z ≠ 0 → r ≤ ‖(z : E)‖)
    (hA : ∀ w : E, ‖A w - w‖ ≤ ε * ‖w‖)
    {x : E} (hx : x ∈ VC ℒ) (hxR : ‖x‖ ≤ R) :
    (((1 - ε) ^ 2 / (1 + 2 * ε * R / r)) • x) ∈ voronoiImage A ℒ := by
  rw [mem_voronoiImage]
  intro z
  by_cases hz : z = 0
  · subst z
    simp
  · have hp := halfspace_perturbed r R ε hr hR0 hε1 hε0 hlam hA hx hxR hz
    have hdenpos : 0 < 1 + 2 * ε * R / r := by
      have hn : 0 ≤ 2 * ε * R / r := div_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hε0) hR0) (le_of_lt hr)
      linarith
    have hs0 : 0 ≤ (1 - ε) ^ 2 / (1 + 2 * ε * R / r) := div_nonneg (sq_nonneg (1 - ε)) (le_of_lt hdenpos)
    have hcom : ⟪(((1 - ε) ^ 2 / (1 + 2 * ε * R / r)) • x), A (z : E)⟫_ℝ
        = ((1 - ε) ^ 2 / (1 + 2 * ε * R / r)) * ⟪x, A (z : E)⟫_ℝ := by
      rw [real_inner_smul_left]
    calc
      ⟪(((1 - ε) ^ 2 / (1 + 2 * ε * R / r)) • x), A (z : E)⟫_ℝ
          = ((1 - ε) ^ 2 / (1 + 2 * ε * R / r)) * ⟪x, A (z : E)⟫_ℝ := hcom
      _ ≤ ((1 - ε) ^ 2 / (1 + 2 * ε * R / r)) *
            (‖A (z : E)‖ ^ 2 / 2 * ((1 + 2 * ε * R / r) / (1 - ε) ^ 2)) := by
            have hcom2 : ⟪x, A (z : E)⟫_ℝ = ⟪A (z : E), x⟫_ℝ := (real_inner_comm x (A (z : E))).symm
            rw [hcom2]
            exact mul_le_mul_of_nonneg_left hp hs0
      _ = ‖A (z : E)‖ ^ 2 / 2 := by
            have hden1 : (1 - ε) ^ 2 ≠ 0 := by
              have h1n : 1 - ε ≠ 0 := by linarith
              exact pow_ne_zero 2 h1n
            have hden2 : 1 + 2 * ε * R / r ≠ 0 := ne_of_gt hdenpos
            have hrp : 0 < r + 2 * ε * R := by
              have h2εR : 0 ≤ 2 * ε * R := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hε0) hR0
              nlinarith
            have h1ε : 1 - ε ≠ 0 := by linarith
            have hsb : ((1 - ε) ^ 2 / (1 + 2 * ε * R / r)) * ((1 + 2 * ε * R / r) / (1 - ε) ^ 2) = 1 := by
              field_simp [h1ε, hden2, ne_of_gt hr, ne_of_gt hrp]
            calc
              ((1 - ε) ^ 2 / (1 + 2 * ε * R / r)) * (‖A (z : E)‖ ^ 2 / 2 * ((1 + 2 * ε * R / r) / (1 - ε) ^ 2))
                  = (((1 - ε) ^ 2 / (1 + 2 * ε * R / r)) * ((1 + 2 * ε * R / r) / (1 - ε) ^ 2)) * (‖A (z : E)‖ ^ 2 / 2) := by ring
              _ = 1 * (‖A (z : E)‖ ^ 2 / 2) := by rw [hsb]
              _ = ‖A (z : E)‖ ^ 2 / 2 := by ring

/-- **V(A·ℒ)-side scaled inclusion** (paper Eq. (Voronoi_claimed_inclusion_2), left part).
`( (1−ε)²/(1+2εR/r) ) · V(ℒ) ⊆ V(A·ℒ)`. -/
theorem scaled_cell_subset_voronoiImage (r R ε : ℝ) (hr : 0 < r) (hR0 : 0 ≤ R)
    (hε1 : ε ≤ 1 / 2) (hε0 : 0 ≤ ε)
    {ℒ : Submodule ℤ E} {A : E →ₗ[ℝ] E}
    (hlam : ∀ z : ℒ, z ≠ 0 → r ≤ ‖(z : E)‖)
    (hA : ∀ w : E, ‖A w - w‖ ≤ ε * ‖w‖)
    (hcell : VC ℒ ⊆ Metric.closedBall (0 : E) R) :
    (((1 - ε) ^ 2 / (1 + 2 * ε * R / r)) • VC ℒ) ⊆ voronoiImage A ℒ := by
  intro x hx
  rw [Set.mem_smul_set] at hx
  rcases hx with ⟨w, hw, hxeq⟩
  rw [← hxeq]
  have hwR : ‖w‖ ≤ R := by
    have hb := Metric.mem_closedBall.mp (hcell hw)
    simpa [dist_eq_norm] using hb
  exact scale_mem_voronoiImage r R ε hr hR0 hε1 hε0 hlam hA (hx := hw) (hxR := hwR)



lemma norm_upper_image (ε : ℝ) (hε0 : 0 ≤ ε)
    {A : E →ₗ[ℝ] E} (hA : ∀ w : E, ‖A w - w‖ ≤ ε * ‖w‖) (z : E) :
    ‖A z‖ ≤ (1 + ε) * ‖z‖ := by
  calc
    ‖A z‖ = ‖z + (A z - z)‖ := by
      congr 1
      abel
    _ ≤ ‖z‖ + ‖A z - z‖ := norm_add_le _ _
    _ ≤ ‖z‖ + ε * ‖z‖ := by
      exact add_le_add (le_rfl : ‖z‖ ≤ ‖z‖) (hA z)
    _ = (1 + ε) * ‖z‖ := by ring


lemma inner_dev_abs_le (ε : ℝ) (hε0 : 0 ≤ ε)
    {A : E →ₗ[ℝ] E} (hA : ∀ w : E, ‖A w - w‖ ≤ ε * ‖w‖) (z x : E) :
    -(⟪A z - z, x⟫_ℝ) ≤ ε * ‖z‖ * ‖x‖ := by
  have h1 := abs_real_inner_le_norm (A z - z) x
  calc
    -(⟪A z - z, x⟫_ℝ) ≤ |⟪A z - z, x⟫_ℝ| := neg_le_abs _
    _ ≤ ‖A z - z‖ * ‖x‖ := h1
    _ ≤ (ε * ‖z‖) * ‖x‖ := mul_le_mul_of_nonneg_right (hA z) (norm_nonneg x)
    _ = ε * ‖z‖ * ‖x‖ := by ring


lemma halfspace_for_cell (r R ε : ℝ) (hr : 0 < r) (hR0 : 0 ≤ R) (hε1 : ε ≤ 1 / 2)
    (hε0 : 0 ≤ ε)
    {ℒ : Submodule ℤ E} {A : E →ₗ[ℝ] E}
    (hlam : ∀ z : ℒ, z ≠ 0 → r ≤ ‖(z : E)‖)
    (hA : ∀ w : E, ‖A w - w‖ ≤ ε * ‖w‖)
    {x : E} (hx : x ∈ voronoiImage A ℒ) (hxR : ‖x‖ ≤ R) {z : ℒ} (hz : z ≠ 0) :
    ⟪(z : E), x⟫_ℝ ≤ ‖(z : E)‖ ^ 2 / 2 * ((1 + ε) ^ 2 + 2 * ε * R / r) := by
  let w : ℝ := ‖(z : E)‖
  have hwr : r ≤ w := by
    dsimp [w]
    exact hlam z hz
  have hwpos : 0 < w := lt_of_lt_of_le hr hwr
  have hm : ⟪A (z : E), x⟫_ℝ ≤ ‖A (z : E)‖ ^ 2 / 2 := by
    have hmem := (mem_voronoiImage.mp hx) z
    simpa [real_inner_comm] using hmem
  have h1ε : 0 ≤ 1 + ε := by linarith
  -- ⟨Az, x⟩ ≤ ‖Az‖²/2 ≤ w²/2(1+ε)²
  have hmain : ⟪A (z : E), x⟫_ℝ ≤ w ^ 2 / 2 * (1 + ε) ^ 2 := by
    have hu := norm_upper_image ε hε0 hA (z : E)
    have hsq : ‖A (z : E)‖ ^ 2 ≤ (1 + ε) ^ 2 * w ^ 2 := by
      -- sq from ‖Az‖ ≤ (1+ε)w
      have h1n : 0 ≤ ‖A (z : E)‖ := norm_nonneg _
      have h2n : 0 ≤ (1 + ε) * w := mul_nonneg h1ε (le_of_lt hwpos)
      have habs : |‖A (z : E)‖| ≤ |(1 + ε) * w| := by
        rw [abs_of_nonneg h1n, abs_of_nonneg h2n]
        dsimp [w] at hu ⊢
        exact hu
      have hs := sq_le_sq.mpr habs
      have h : ((1 + ε) * w) ^ 2 = (1 + ε) ^ 2 * w ^ 2 := by ring
      rwa [h] at hs
    calc
      ⟪A (z : E), x⟫_ℝ ≤ ‖A (z : E)‖ ^ 2 / 2 := hm
      _ ≤ w ^ 2 / 2 * (1 + ε) ^ 2 := by
        nlinarith [hsq]
  -- ⟨y,x⟩ = ⟨Ay,x⟩ − ⟨Ay−y,x⟩ ≤ ⟨Ay,x⟩ + εw‖x‖ ≤ ⟨Ay,x⟩ + εwR
  have hminus : ⟪(z : E), x⟫_ℝ = ⟪A (z : E), x⟫_ℝ - ⟪A (z : E) - (z : E), x⟫_ℝ := by
    have hc : ⟪(z : E), x⟫_ℝ + ⟪A (z : E) - (z : E), x⟫_ℝ = ⟪A (z : E), x⟫_ℝ := by
      rw [show A (z : E) = (z : E) + (A (z : E) - (z : E)) by abel]
      rw [inner_add_left]
      simp
    linarith
  have hdev : -(⟪A (z : E) - (z : E), x⟫_ℝ) ≤ ε * w * R := by
    have h1 := inner_dev_abs_le ε hε0 hA (z : E) x
    calc
      -(⟪A (z : E) - (z : E), x⟫_ℝ) ≤ ε * ‖(z : E)‖ * ‖x‖ := h1
      _ = ε * w * ‖x‖ := by dsimp [w]
      _ ≤ ε * w * R := by
        exact mul_le_mul_of_nonneg_left hxR (mul_nonneg hε0 (by positivity : 0 ≤ w))
  have hsum : ⟪(z : E), x⟫_ℝ ≤ ⟪A (z : E), x⟫_ℝ + ε * w * R := by
    rw [hminus]
    linarith
  have hsecond : ε * w * R ≤ w ^ 2 / 2 * (2 * ε * R / r) := by
    -- εwR = w²/2·(2εR/w) ≤ w²/2·(2εR/r)
    have hrec : w⁻¹ ≤ r⁻¹ := by
      simpa using (one_div_le_one_div_of_le hr hwr)
    have h2' : (2 * ε * R) * w⁻¹ ≤ (2 * ε * R) * r⁻¹ :=
      mul_le_mul_of_nonneg_left hrec (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hε0) hR0)
    have h2 : (2 * ε * R) / w ≤ (2 * ε * R) / r := by
      simpa [div_eq_mul_inv] using h2'
    calc
      ε * w * R = w ^ 2 / 2 * ((2 * ε * R) / w) := by
        field_simp [hwpos.ne']
      _ ≤ w ^ 2 / 2 * ((2 * ε * R) / r) := by
        exact mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = w ^ 2 / 2 * (2 * ε * R / r) := rfl
  calc
    ⟪(z : E), x⟫_ℝ ≤ ⟪A (z : E), x⟫_ℝ + ε * w * R := hsum
    _ ≤ w ^ 2 / 2 * (1 + ε) ^ 2 + ε * w * R := by
        exact add_le_add hmain (le_rfl : ε * w * R ≤ ε * w * R)
    _ ≤ w ^ 2 / 2 * (1 + ε) ^ 2 + w ^ 2 / 2 * (2 * ε * R / r) := by
        exact add_le_add (le_rfl : w ^ 2 / 2 * (1 + ε) ^ 2 ≤ w ^ 2 / 2 * (1 + ε) ^ 2) hsecond
    _ = w ^ 2 / 2 * ((1 + ε) ^ 2 + 2 * ε * R / r) := by ring


lemma scale_mem_voronoi_cell (r R ε : ℝ) (hr : 0 < r) (hR0 : 0 ≤ R) (hε1 : ε ≤ 1 / 2)
    (hε0 : 0 ≤ ε)
    {ℒ : Submodule ℤ E} {A : E →ₗ[ℝ] E}
    (hlam : ∀ z : ℒ, z ≠ 0 → r ≤ ‖(z : E)‖)
    (hA : ∀ w : E, ‖A w - w‖ ≤ ε * ‖w‖)
    {x : E} (hx : x ∈ voronoiImage A ℒ) (hxR : ‖x‖ ≤ R) :
    (((1 : ℝ) / ((1 + ε) ^ 2 + 2 * ε * R / r)) • x) ∈ VC ℒ := by
  rw [Submission.Voronoi.mem_voronoi]
  intro z
  by_cases hz : z = 0
  · subst z
    simp
  · have hp := halfspace_for_cell r R ε hr hR0 hε1 hε0 hlam hA hx hxR hz
    have hdenpos : 0 < (1 + ε) ^ 2 + 2 * ε * R / r := by
      have h1p : 0 < (1 + ε) ^ 2 := sq_pos_of_ne_zero (by linarith : 1 + ε ≠ 0)
      have hn : 0 ≤ 2 * ε * R / r := div_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hε0) hR0) (le_of_lt hr)
      nlinarith
    have hs0 : 0 ≤ (1 : ℝ) / ((1 + ε) ^ 2 + 2 * ε * R / r) := div_nonneg (by norm_num) (le_of_lt hdenpos)
    have hcom : ⟪(((1 : ℝ) / ((1 + ε) ^ 2 + 2 * ε * R / r)) • x), (z : E)⟫_ℝ
        = ((1 : ℝ) / ((1 + ε) ^ 2 + 2 * ε * R / r)) * ⟪(z : E), x⟫_ℝ := by
      rw [real_inner_smul_left]
      rw [real_inner_comm (z : E) x]
    calc
      ⟪(((1 : ℝ) / ((1 + ε) ^ 2 + 2 * ε * R / r)) • x), (z : E)⟫_ℝ
          = ((1 : ℝ) / ((1 + ε) ^ 2 + 2 * ε * R / r)) * ⟪(z : E), x⟫_ℝ := hcom
      _ ≤ ((1 : ℝ) / ((1 + ε) ^ 2 + 2 * ε * R / r)) *
            (‖(z : E)‖ ^ 2 / 2 * ((1 + ε) ^ 2 + 2 * ε * R / r)) := by
            exact mul_le_mul_of_nonneg_left hp hs0
      _ = ‖(z : E)‖ ^ 2 / 2 := by
            have hden : (1 + ε) ^ 2 + 2 * ε * R / r ≠ 0 := ne_of_gt hdenpos
            have hsb : ((1 : ℝ) / ((1 + ε) ^ 2 + 2 * ε * R / r)) * ((1 + ε) ^ 2 + 2 * ε * R / r) = 1 := by
              field_simp [hden]
            calc
              ((1 : ℝ) / ((1 + ε) ^ 2 + 2 * ε * R / r)) * (‖(z : E)‖ ^ 2 / 2 * ((1 + ε) ^ 2 + 2 * ε * R / r))
                  = (((1 : ℝ) / ((1 + ε) ^ 2 + 2 * ε * R / r)) * ((1 + ε) ^ 2 + 2 * ε * R / r)) * (‖(z : E)‖ ^ 2 / 2) := by ring
              _ = 1 * (‖(z : E)‖ ^ 2 / 2) := by rw [hsb]
              _ = ‖(z : E)‖ ^ 2 / 2 := by ring


theorem voronoiImage_subset_scale (r R ε : ℝ) (hr : 0 < r) (hR0 : 0 ≤ R)
    (hε1 : ε ≤ 1 / 2) (hε0 : 0 ≤ ε)
    {ℒ : Submodule ℤ E} {A : E →ₗ[ℝ] E}
    (hlam : ∀ z : ℒ, z ≠ 0 → r ≤ ‖(z : E)‖)
    (hA : ∀ w : E, ‖A w - w‖ ≤ ε * ‖w‖)
    (hcell : voronoiImage A ℒ ⊆ Metric.closedBall (0 : E) R) :
    voronoiImage A ℒ ⊆ ((1 + ε) ^ 2 + 2 * ε * R / r) • VC ℒ := by
  intro x hx
  have hxR : ‖x‖ ≤ R := by
    have hb := Metric.mem_closedBall.mp (hcell hx)
    simpa [dist_eq_norm] using hb
  refine ⟨((1 : ℝ) / ((1 + ε) ^ 2 + 2 * ε * R / r)) • x, ?_, ?_⟩
  · exact scale_mem_voronoi_cell r R ε hr hR0 hε1 hε0 hlam hA hx hxR
  · have hden : (1 + ε) ^ 2 + 2 * ε * R / r ≠ 0 := by
      have h1p : 0 < (1 + ε) ^ 2 := sq_pos_of_ne_zero (by linarith : 1 + ε ≠ 0)
      have hn : 0 ≤ 2 * ε * R / r := div_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hε0) hR0) (le_of_lt hr)
      have hd : 0 < (1 + ε) ^ 2 + 2 * ε * R / r := by nlinarith
      exact ne_of_gt hd
    have hnn : ((1 + ε) ^ 2 + 2 * ε * R / r) * ((1 : ℝ) / ((1 + ε) ^ 2 + 2 * ε * R / r)) = 1 := by
      field_simp [hden]
    have h1 : x = (((1 + ε) ^ 2 + 2 * ε * R / r) * ((1 : ℝ) / ((1 + ε) ^ 2 + 2 * ε * R / r))) • x := by
      rw [hnn, one_smul]
    have h2 : (((1 + ε) ^ 2 + 2 * ε * R / r) * ((1 : ℝ) / ((1 + ε) ^ 2 + 2 * ε * R / r))) • x
        = ((1 + ε) ^ 2 + 2 * ε * R / r) • (((1 : ℝ) / ((1 + ε) ^ 2 + 2 * ε * R / r)) • x) := by
      exact (smul_smul ((1 + ε) ^ 2 + 2 * ε * R / r) ((1 : ℝ) / ((1 + ε) ^ 2 + 2 * ε * R / r)) x).symm
    exact (h1.trans h2).symm

lemma scale_left_ge (r R ε : ℝ) (hr : 0 < r) (hR0 : 0 ≤ R) (hε0 : 0 ≤ ε)
    (hε1 : ε ≤ 1 / 2) :
    1 - (4 + 4 * (R / r)) * ε ≤ (1 - ε) ^ 2 / (1 + 2 * ε * R / r) := by
  let t : ℝ := R / r
  let ν : ℝ := 4 + 4 * t
  have ht0 : 0 ≤ t := by
    dsimp [t]
    exact div_nonneg hR0 (le_of_lt hr)
  have hd : 0 < 1 + 2 * ε * t := by
    have h1 : 0 ≤ 2 * ε * t := mul_nonneg (mul_nonneg (by norm_num) hε0) ht0
    nlinarith
  have hν0 : 0 ≤ ν := by
    dsimp [ν]
    nlinarith
  have h1m : 1 - ν * ε ≤ 1 := by nlinarith [hε0, hν0]
  have h2t0 : 0 ≤ 2 * ε * t := mul_nonneg (mul_nonneg (by norm_num) hε0) ht0
  have hsplit : (1 - ν * ε) * (1 + 2 * ε * t) ≤ (1 - ν * ε) + 2 * ε * t := by
    calc
      (1 - ν * ε) * (1 + 2 * ε * t) = (1 - ν * ε) + (1 - ν * ε) * (2 * ε * t) := by ring
      _ ≤ (1 - ν * ε) + 2 * ε * t := by
        exact add_le_add (le_rfl : (1 - ν * ε) ≤ (1 - ν * ε))
          (by simpa using mul_le_mul_of_nonneg_right h1m h2t0)
  have htail : (1 - ν * ε) + 2 * ε * t ≤ 1 - 2 * ε + ε ^ 2 := by
    dsimp [ν]
    nlinarith [sq_nonneg ε, hε0, ht0]
  have hsqeq : 1 - 2 * ε + ε ^ 2 = (1 - ε) ^ 2 := by ring
  have hmain : (1 - ν * ε) * (1 + 2 * ε * t) ≤ (1 - ε) ^ 2 := by
    have h1 := le_trans hsplit htail
    rwa [hsqeq] at h1
  have hdiv : 1 - ν * ε ≤ (1 - ε) ^ 2 / (1 + 2 * ε * t) := by
    exact (le_div_iff₀ hd).2 hmain
  have hden_eq : 1 + 2 * ε * R / r = 1 + 2 * ε * (R / r) := by
    field_simp [ne_of_gt hr]
  have hgoal : 1 - (4 + 4 * (R / r)) * ε ≤ (1 - ε) ^ 2 / (1 + 2 * ε * (R / r)) := by
    simpa [ν, t] using hdiv
  rwa [hden_eq.symm] at hgoal


lemma scale_two_le (r R ε : ℝ) (hr : 0 < r) (hR0 : 0 ≤ R) (hε0 : 0 ≤ ε)
    (hε1 : ε ≤ 1 / 2) :
    (1 + ε) ^ 2 + 2 * ε * R / r ≤ 1 + (4 + 4 * (R / r)) * ε := by
  let c : ℝ := R / r
  have hc0 : 0 ≤ c := by
    dsimp [c]
    exact div_nonneg hR0 (le_of_lt hr)
  have hde : 2 * ε * R / r = 2 * ε * c := by
    dsimp [c]
    field_simp [ne_of_gt hr]
  rw [hde]
  have hmain : (1 + ε) ^ 2 + 2 * ε * c ≤ 1 + (4 + 4 * c) * ε := by
    nlinarith [sq_nonneg ε, hε0, hε1, hc0]
  simpa [c] using hmain


lemma smul_subset_smul_of_le {V : Set E} (hC : Convex ℝ V) (h0 : (0 : E) ∈ V)
    {a b : ℝ} (ha0 : 0 ≤ a) (hab : a ≤ b) : a • V ⊆ b • V := by
  intro x hx
  rw [Set.mem_smul_set] at hx ⊢
  rcases hx with ⟨v, hv, hxeq⟩
  by_cases hb : b = 0
  · subst b
    have ha0' : a = 0 := by nlinarith
    subst a
    refine ⟨v, hv, ?_⟩
    exact hxeq
  · have hbpos : 0 < b := by
      have : b ≤ 0 ∨ 0 ≤ b := le_total b 0
      rcases this with hle | hge
      · have : b = 0 := by nlinarith [hle, hab, ha0]
        exact (hb this).elim
      · exact lt_of_le_of_ne hge (Ne.symm hb)
    have hc : (a / b) • v ∈ V := by
      have hc0 : 0 ≤ a / b := div_nonneg ha0 (le_of_lt hbpos)
      have hc1 : a / b ≤ 1 := by
        rw [div_le_one hbpos]
        exact hab
      have hm := hC h0 hv (by linarith : 0 ≤ 1 - a / b) hc0 (by linarith : (1 - a / b) + a / b = 1)
      simpa using hm
    refine ⟨(a / b) • v, hc, ?_⟩
    calc
      b • ((a / b) • v) = a • v := by
        have hs : b * (a / b) = a := by field_simp [hb]
        rw [smul_smul]
        rw [hs]
      _ = x := hxeq


/-- paper `(1−ν·ε)·V ⊆ V(A·ℒ) ⊆ (1+ν·ε)·V` with `ν := 4 + 4R/r`, `ε` the perturbation
bound (`‖M‖`), `r := λ₁/2`, `R` the cell radius. -/
theorem voronoiImage_sandwich (r R ε : ℝ) (hr : 0 < r) (hR0 : 0 ≤ R) (hε0 : 0 ≤ ε)
    (hε1 : ε ≤ 1 / 2) (hνe : (4 + 4 * (R / r)) * ε ≤ 1)
    {ℒ : Submodule ℤ E} {A : E →ₗ[ℝ] E}
    (hlam : ∀ z : ℒ, z ≠ 0 → r ≤ ‖(z : E)‖)
    (hA : ∀ w : E, ‖A w - w‖ ≤ ε * ‖w‖)
    (hcellL : VC ℒ ⊆ Metric.closedBall (0 : E) R)
    (hcellR : voronoiImage A ℒ ⊆ Metric.closedBall (0 : E) R) :
    (1 - (4 + 4 * (R / r)) * ε) • VC ℒ ⊆ voronoiImage A ℒ ∧
      voronoiImage A ℒ ⊆ (1 + (4 + 4 * (R / r)) * ε) • VC ℒ := by
  let ν : ℝ := 4 + 4 * (R / r)
  have hleft_s : (1 - ν * ε) ≤ (1 - ε) ^ 2 / (1 + 2 * ε * R / r) := by
    dsimp [ν]
    exact scale_left_ge r R ε hr hR0 hε0 hε1
  have hleft0 : 0 ≤ 1 - ν * ε := by
    dsimp [ν]
    exact sub_nonneg.mpr hνe
  have hVc : Convex ℝ (VC ℒ) := Submission.Voronoi.voronoi_convex ℒ
  have hV0 : (0 : E) ∈ VC ℒ := zero_mem_voronoi ℒ
  have hinc1 : (1 - ν * ε) • VC ℒ ⊆ ((1 - ε) ^ 2 / (1 + 2 * ε * R / r)) • VC ℒ := by
    exact smul_subset_smul_of_le hVc hV0 hleft0 hleft_s
  have hinc2 : ((1 - ε) ^ 2 / (1 + 2 * ε * R / r)) • VC ℒ ⊆ voronoiImage A ℒ := by
    exact scaled_cell_subset_voronoiImage r R ε hr hR0 hε1 hε0 hlam hA hcellL
  have hleft : (1 - ν * ε) • VC ℒ ⊆ voronoiImage A ℒ := (hinc1.trans hinc2)
  have hright1 : voronoiImage A ℒ ⊆ ((1 + ε) ^ 2 + 2 * ε * R / r) • VC ℒ := by
    exact voronoiImage_subset_scale r R ε hr hR0 hε1 hε0 hlam hA hcellR
  have hright2 : ((1 + ε) ^ 2 + 2 * ε * R / r) • VC ℒ ⊆ (1 + ν * ε) • VC ℒ := by
    have hb2 : (1 + ε) ^ 2 + 2 * ε * R / r ≤ 1 + ν * ε := by
      dsimp [ν]
      exact scale_two_le r R ε hr hR0 hε0 hε1
    have hb0 : 0 ≤ (1 + ε) ^ 2 + 2 * ε * R / r := by
      have h1 : 0 ≤ (1 + ε) ^ 2 := sq_nonneg (1 + ε)
      have h2 : 0 ≤ 2 * ε * R / r := div_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hε0) hR0) (le_of_lt hr)
      nlinarith
    exact smul_subset_smul_of_le hVc hV0 hb0 hb2
  exact ⟨hleft, (hright1.trans hright2)⟩

/-! ## [C2c] Glue: `voronoiImage A ℒ = voronoi (image submodule)`

`voronoiImage A ℒ` was defined as the paper's `V(A·Λ)`-cell directly over lattice vectors
`z ∈ ℒ` with `⟨x, Az⟩ ≤ ‖Az‖²/2`.  The actual image lattice is the `ℤ`-submodule
`ℒ.map (A.restrictScalars ℤ)` (the same ambient set of points `{A z : z ∈ ℒ}`), whose
`voronoi` cell iterates over the image elements; the glue below identifies the two cells as
sets, so all of `clm:eps_voronoi` (sandwich) statements transfer to the image submodule.
-/

/-- **Glue**: the Voronoi cell of the `A`-image submodule equals `voronoiImage A ℒ`. -/
lemma voronoi_map_lattice (A : E →ₗ[ℝ] E) (ℒ : Submodule ℤ E) :
    VC (ℒ.map (A.restrictScalars ℤ)) = voronoiImage A ℒ := by
  ext x
  rw [Submission.Voronoi.mem_voronoi]
  rw [mem_voronoiImage]
  constructor
  · intro hx z
    have hw : (A.restrictScalars ℤ) (z : E) ∈ ℒ.map (A.restrictScalars ℤ) := by
      rw [Submodule.mem_map]
      refine ⟨(z : E), z.2, rfl⟩
    have h := hx ⟨(A.restrictScalars ℤ) (z : E), hw⟩
    simpa using h
  · intro hx w
    have hw2 : (w : E) ∈ ℒ.map (A.restrictScalars ℤ) := w.2
    rw [Submodule.mem_map] at hw2
    rcases hw2 with ⟨y, hy, hyw⟩
    have h := hx ⟨y, hy⟩
    have hval : (w : E) = A y := by
      simpa using hyw.symm
    rw [hval]
    exact h



/-! ## [C2d] Measure scaling of the transformed cell (`thm:same_grad_VL` input)

`λ(A·V) = |det A|·λ(V)`: volume is an additive Haar measure on `E`
(`IsAddHaarMeasure volume`), and `addHaar_image_linearMap` gives the image-scaling law for
any (not necessarily invertible) real-linear map `A` in terms of `|LinearMap.det A|`.
The real-valued `measureReal_map_cell` version is what the Gaussian-integral-difference
estimate consumes (set-integral of `1` over `A·V` = `|det|·` measure of `V`).
-/

/-- measure scaling under a linear map: `λ(A·V) = |det A|·λ(V)` (any `V`, any `A`). -/
theorem measure_map_cell (A : E →ₗ[ℝ] E) (V : Set E) :
    (volume : Measure E) (A '' V) = ENNReal.ofReal |LinearMap.det A| * (volume : Measure E) V := by
  exact addHaar_image_linearMap (μ := (volume : Measure E)) (f := A) V

/-- real-measure version: `λ(A·V) = |det A|·λ(V)`. -/
theorem measureReal_map_cell (A : E →ₗ[ℝ] E) (V : Set E) :
    (volume : Measure E).real (A '' V) = |LinearMap.det A| * (volume : Measure E).real V := by
  have htr := congrArg ENNReal.toReal (measure_map_cell A V)
  have hR : ((volume : Measure E) (A '' V)).toReal = (volume : Measure E).real (A '' V) := rfl
  have hL : (ENNReal.ofReal |LinearMap.det A| * (volume : Measure E) V).toReal =
      |LinearMap.det A| * (volume : Measure E).real V := by
    rw [ENNReal.toReal_mul]
    rw [ENNReal.toReal_ofReal]
    · rfl
    · exact abs_nonneg _
  rwa [hR, hL] at htr


lemma ball_subset_image_ball (r ε : ℝ) (hr : 0 < r) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / 2)
    {A : E →ₗ[ℝ] E} (hdetA : LinearMap.det A ≠ 0) (hA : ∀ w : E, ‖A w - w‖ ≤ ε * ‖w‖) :
    Metric.closedBall (0 : E) ((1 - ε) * r) ⊆ A '' Metric.closedBall (0 : E) r := by
  have h1e : 0 < 1 - ε := by linarith
  let g : E ≃ₗ[ℝ] E := A.equivOfDetNeZero hdetA
  have hgfun : ∀ z : E, A z = g z := by intro z; rfl
  intro x hx
  rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hx
  have hAy : A (g.symm x) = x := by
    rw [hgfun (g.symm x)]
    exact (g.apply_symm_apply x)
  have hy : ‖g.symm x‖ ≤ r := by
    have hl := norm_lower_image ε hε0 hA (g.symm x)
    rw [hAy] at hl
    calc
      ‖g.symm x‖ ≤ ‖x‖ / (1 - ε) := (le_div_iff₀ h1e).2 (by simpa [mul_comm] using hl)
      _ ≤ r := by
        exact (div_le_iff₀ h1e).2 (by simpa [mul_comm] using hx)
  refine ⟨g.symm x, ?_, ?_⟩
  · rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
    exact hy
  · exact hAy


lemma cell_subset_image_scale (r R ε : ℝ) (hr : 0 < r) (hR0 : 0 ≤ R) (hε0 : 0 ≤ ε)
    (hε1 : ε ≤ 1 / 2)
    {ℒ : Submodule ℤ E} {A : E →ₗ[ℝ] E}
    (hdetA : LinearMap.det A ≠ 0)
    (hball : Metric.closedBall (0 : E) r ⊆ VC ℒ)
    (hcell : VC ℒ ⊆ Metric.closedBall (0 : E) R)
    (hA : ∀ w : E, ‖A w - w‖ ≤ ε * ‖w‖) :
    VC ℒ ⊆ (1 + ε * R / ((1 - ε) * r)) • (A '' VC ℒ) := by
  have h1e : 0 < 1 - ε := by linarith
  have hr' : 0 < (1 - ε) * r := mul_pos h1e hr
  let W : Set E := A '' VC ℒ
  have hWcvx : Convex ℝ W := by
    dsimp [W]
    exact (Submission.Voronoi.voronoi_convex ℒ).linear_image (A : E →ₗ[ℝ] E)
  have hW0 : (0 : E) ∈ W := by
    refine ⟨(0 : E), zero_mem_voronoi ℒ, ?_⟩
    simp
  have hWball : Metric.closedBall (0 : E) ((1 - ε) * r) ⊆ W := by
    intro z hz
    have hb := ball_subset_image_ball r ε hr hε0 hε1 hdetA hA
    have hz' : z ∈ A '' Metric.closedBall (0 : E) r := hb hz
    rw [Set.mem_image] at hz'
    rcases hz' with ⟨y, hyb, hzy⟩
    refine ⟨y, hball hyb, hzy⟩
  have hVadd : VC ℒ ⊆ W +ᵥ Metric.closedBall (0 : E) (ε * R) := by
    intro x hx
    have hxadd := cell_subset_image_add_ball R hcell A ε hε0 hA
    simpa [W] using hxadd hx
  have hnum : 0 ≤ ε * R / ((1 - ε) * r) := div_nonneg (mul_nonneg hε0 hR0) (le_of_lt hr')
  have hcm := Commons.Analysis.Convex.smul_add_ball_subset_smul (n := n) (C := W)
    (t₁ := 1) (t₂ := 1 + ε * R / ((1 - ε) * r))
    hWcvx hW0 (hr := le_of_lt hr') (ht₁ := by norm_num) (ht := by linarith) hWball
  have hrad : ((1 + ε * R / ((1 - ε) * r)) - 1) * ((1 - ε) * r) = ε * R := by
    field_simp [ne_of_gt hr']
    ring
  have hone : (1 : ℝ) • W = W := by
    ext x
    rw [Set.mem_smul_set]
    constructor
    · rintro ⟨w, hw, hxeq⟩
      have hxw : w = x := by simpa using hxeq
      rwa [← hxw]
    · intro hx
      refine ⟨x, hx, by simp⟩
  have hinc : W +ᵥ Metric.closedBall (0 : E) (ε * R) ⊆ (1 + ε * R / ((1 - ε) * r)) • W := by
    rw [hrad] at hcm
    rw [hone] at hcm
    exact hcm
  intro x hx
  exact (hinc (hVadd hx))


/-- **Volume-side of the Gaussian-integral estimate**: the measure of the transformed-lattice
cell is sandwiched between the measures of the `(1∓νε)`-scaled cells.  With the measure of
`(c•V)` equal to `c^n·vol V` and `|det A| = 1+O(ε)` (the two remaining scaling sub-lemmas),
this turns the integrand-difference into `O(ε)` for any bounded integrand. -/
theorem measure_cell_sandwich (r R ε : ℝ) (hr : 0 < r) (hR0 : 0 ≤ R) (hε0 : 0 ≤ ε)
    (hε1 : ε ≤ 1 / 2) (hνe : (4 + 4 * (R / r)) * ε ≤ 1)
    {ℒ : Submodule ℤ E} {A : E →ₗ[ℝ] E}
    (hlam : ∀ z : ℒ, z ≠ 0 → r ≤ ‖(z : E)‖)
    (hA : ∀ w : E, ‖A w - w‖ ≤ ε * ‖w‖)
    (hcellL : VC ℒ ⊆ Metric.closedBall (0 : E) R)
    (hcellR : voronoiImage A ℒ ⊆ Metric.closedBall (0 : E) R) :
    (volume : Measure E) ((1 - (4 + 4 * (R / r)) * ε) • VC ℒ) ≤ volume (voronoiImage A ℒ) ∧
      volume (voronoiImage A ℒ) ≤ volume ((1 + (4 + 4 * (R / r)) * ε) • VC ℒ) := by
  have hs := voronoiImage_sandwich r R ε hr hR0 hε0 hε1 hνe hlam hA hcellL hcellR
  exact ⟨measure_mono hs.1, measure_mono hs.2⟩


theorem measure_smul (c : ℝ) (V : Set E) :
    (volume : Measure E) (c • V) = ENNReal.ofReal |c ^ Module.finrank ℝ E| * (volume : Measure E) V := by
  have h := addHaar_image_linearMap (μ := (volume : Measure E))
    (f := (c • LinearMap.id : E →ₗ[ℝ] E)) V
  have hdet : LinearMap.det ((c • LinearMap.id) : E →ₗ[ℝ] E) = c ^ Module.finrank ℝ E := by
    rw [LinearMap.det_smul, LinearMap.det_id]
    simp
  have him : ((c • LinearMap.id : E →ₗ[ℝ] E) '' V) = c • V := by
    ext x
    simp [Set.mem_image, Set.mem_smul_set]
  rw [hdet] at h
  rwa [him] at h


theorem measureReal_smul (c : ℝ) (hc : 0 ≤ c) (V : Set E) :
    (volume : Measure E).real (c • V) = c ^ Module.finrank ℝ E * (volume : Measure E).real V := by
  have htr := congrArg ENNReal.toReal (measure_smul c V)
  have hR : ((volume : Measure E) (c • V)).toReal = (volume : Measure E).real (c • V) := rfl
  have hdet0 : 0 ≤ c ^ Module.finrank ℝ E := pow_nonneg hc _
  have hL : (ENNReal.ofReal |c ^ Module.finrank ℝ E| * (volume : Measure E) V).toReal =
      c ^ Module.finrank ℝ E * (volume : Measure E).real V := by
    rw [ENNReal.toReal_mul]
    rw [ENNReal.toReal_ofReal]
    · congr 1
      exact abs_of_nonneg hdet0
    · exact abs_nonneg _
  rwa [hR, hL] at htr

/-! ## [C2e] matrix entries bounded by the `mvec`-Lipschitz constant (det-close input)

For a perturbation matrix `M` whose action `x ↦ mvec M x` is bounded by `ε·‖x‖`, each entry
is bounded by `ε`: apply the bound to the standard basis vector `e_j` (unit norm) and take
the `i`-th coordinate (|coordinate| ≤ norm).  This is the entry bound that the
first-principles det-close lemma (`|det(1+M) − 1| ≤ n!·2ⁿ·ε`, Leibniz/`det_apply`
expansion — in progress) needs; it is also the bridge from the eps-voronoi `ε`-data to
matrix-norm statements.
-/

/-- standard basis vector `e_j` as an element of `E`. -/
noncomputable def e_j (j : Fin n) : E :=
  WithLp.toLp 2 (fun r : Fin n => if r = j then 1 else 0)

/-- `‖e_j‖ = 1`. -/
lemma norm_e_j (j : Fin n) : ‖e_j j‖ = 1 := by
  have hsq : ‖e_j j‖ ^ 2 = 1 := by
    dsimp [e_j]
    simp only [PiLp.norm_sq_eq_of_L2]
    rw [Finset.sum_eq_single j]
    · simp
    · intro b hb hbj
      simp [hbj]
    · intro h
      exact (h (Finset.mem_univ j)).elim
  have hn : 0 ≤ ‖e_j j‖ := norm_nonneg _
  nlinarith [hsq]

/-- coordinate of the standard basis vector: `(e_j)_r = 1` iff `r = j`. -/
lemma coord_e_j (j r : Fin n) : (e_j j) r = if r = j then 1 else 0 := by
  rfl

/-- **Entry bound**: `‖mvec M x‖ ≤ ε‖x‖` for all `x` ⟹ `|M i j| ≤ ε`. -/
lemma mvec_entry_le (M : Matrix (Fin n) (Fin n) ℝ) (ε : ℝ)
    (hM : ∀ x : E, ‖Submission.ShapeDeriv.mvec M x‖ ≤ ε * ‖x‖) (i j : Fin n) :
    |M i j| ≤ ε := by
  have hc : (Submission.ShapeDeriv.mvec M (e_j j)) i = M i j := by
    have hcm := Submission.ShapeDeriv.co_mvec M (e_j j)
    have hci : (Submission.ShapeDeriv.mvec M (e_j j)) i = (M *ᵥ Submission.ShapeDeriv.co (e_j j)) i := by
      have := congrFun hcm i
      simpa [Submission.ShapeDeriv.co, Submission.ShapeDeriv.coord_apply] using this
    rw [hci]
    have hz : ∀ r : Fin n, Submission.ShapeDeriv.co (e_j j) r = (if r = j then 1 else 0) := by
      intro r
      simpa [Submission.ShapeDeriv.co] using (coord_e_j j r)
    calc
      (M *ᵥ Submission.ShapeDeriv.co (e_j j)) i = ∑ r : Fin n, M i r * Submission.ShapeDeriv.co (e_j j) r := by
        simp [Matrix.mulVec, dotProduct]
      _ = ∑ r : Fin n, M i r * (if r = j then 1 else 0) := by
        apply Finset.sum_congr rfl
        intro r hr
        rw [hz r]
      _ = M i j := by
        rw [Finset.sum_eq_single j]
        · simp
        · intro b hb hbj
          simp [hbj]
        · intro h
          exact (h (Finset.mem_univ j)).elim
  have hb : |(Submission.ShapeDeriv.mvec M (e_j j)) i| ≤ ‖Submission.ShapeDeriv.mvec M (e_j j)‖ := by
    have := PiLp.norm_apply_le (p := 2) (β := fun _ : Fin n => ℝ) (Submission.ShapeDeriv.mvec M (e_j j)) i
    simpa [Real.norm_eq_abs] using this
  calc
    |M i j| = |(Submission.ShapeDeriv.mvec M (e_j j)) i| := by rw [hc]
    _ ≤ ‖Submission.ShapeDeriv.mvec M (e_j j)‖ := hb
    _ ≤ ε * ‖e_j j‖ := hM (e_j j)
    _ = ε := by
      rw [norm_e_j]
      ring

lemma diag_prod_sandwich (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (ε : ℝ)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (hM : ∀ i : Fin n, |M i i| ≤ ε) :
    (1 - ε) ^ n ≤ (∏ i : Fin n, (1 + M i i)) ∧
      (∏ i : Fin n, (1 + M i i)) ≤ (1 + ε) ^ n := by
  have hfac (i : Fin n) : 1 - ε ≤ 1 + M i i ∧ 1 + M i i ≤ 1 + ε := by
    have habs := hM i
    have h1 : -ε ≤ M i i := (abs_le.mp habs).1
    have h2 : M i i ≤ ε := (abs_le.mp habs).2
    constructor <;> linarith
  have hnonneg (i : Fin n) : 0 ≤ 1 + M i i := by
    have : 1 - ε ≤ 1 + M i i := (hfac i).1
    linarith
  have hnonneg_lo (i : Fin n) : 0 ≤ 1 - ε := by linarith
  have hnonneg_up (i : Fin n) : 0 ≤ 1 + ε := by linarith
  constructor
  · -- (1−ε)ⁿ ≤ ∏(1+Mᵢᵢ)
    calc
      (1 - ε) ^ n = ∏ i : Fin n, (1 - ε) := by simp
      _ ≤ ∏ i : Fin n, (1 + M i i) := by
        exact Finset.prod_le_prod (s := (Finset.univ : Finset (Fin n)))
          (f := fun _ : Fin n => 1 - ε) (g := fun i : Fin n => 1 + M i i)
          ((by intro i hi; exact hnonneg_lo i)) ((by intro i hi; exact (hfac i).1))
  · -- ∏(1+Mᵢᵢ) ≤ (1+ε)ⁿ
    calc
      ∏ i : Fin n, (1 + M i i) ≤ ∏ i : Fin n, (1 + ε) := by
        exact Finset.prod_le_prod (s := (Finset.univ : Finset (Fin n)))
          (f := fun i : Fin n => 1 + M i i) (g := fun _ : Fin n => 1 + ε)
          ((by intro i hi; exact hnonneg i)) ((by intro i hi; exact (hfac i).2))
      _ = (1 + ε) ^ n := by simp
lemma bernoulli_lower (n : ℕ) (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    1 - (n : ℝ) * ε ≤ (1 - ε) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      have h1e0 : 0 ≤ 1 - ε := by linarith
      have hn0 : 0 ≤ (n : ℝ) := by exact_mod_cast (Nat.zero_le n)
      calc
        1 - ((n + 1 : ℕ) : ℝ) * ε ≤ (1 - (n : ℝ) * ε) * (1 - ε) := by
          have hc : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by norm_num
          rw [hc]
          have hprod : (1 - (n : ℝ) * ε) * (1 - ε) = 1 - ε - (n : ℝ) * ε + (n : ℝ) * ε ^ 2 := by ring
          rw [hprod]
          nlinarith [mul_nonneg hn0 (sq_nonneg ε)]
        _ ≤ (1 - ε) ^ (n + 1) := by
          calc
            (1 - (n : ℝ) * ε) * (1 - ε) ≤ (1 - ε) ^ n * (1 - ε) :=
              mul_le_mul_of_nonneg_right ih h1e0
            _ = (1 - ε) ^ (n + 1) := by rw [pow_succ]


lemma diag_prod_one_close (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (ε : ℝ)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (hM : ∀ i : Fin n, |M i i| ≤ ε) :
    |(∏ i : Fin n, (1 + M i i)) - 1| ≤ (n : ℝ) * 2 ^ n * ε := by
  let hs := Submission.EpsVoronoi.diag_prod_sandwich n M ε hε0 hε1 hM
  -- ∏ ≤ (1+ε)ⁿ ⟹ ∏ − 1 ≤ (1+ε)ⁿ − 1
  have hup1 : (∏ i : Fin n, (1 + M i i)) - 1 ≤ (1 + ε) ^ n - 1 := by
    linarith [hs.2]
  -- (1+ε)ⁿ − 1 ≤ n·2ⁿ·ε
  have hsum_le : (∑ k ∈ Finset.range n, (1 + ε) ^ k) ≤ (n : ℝ) * 2 ^ n := by
    calc
      (∑ k ∈ Finset.range n, (1 + ε) ^ k) ≤ ∑ k ∈ Finset.range n, (2 : ℝ) ^ k := by
        exact Finset.sum_le_sum (by
          intro k hk
          exact pow_le_pow_left₀ (by linarith : 0 ≤ 1 + ε) (by linarith : 1 + ε ≤ 2) k)
      _ ≤ ∑ k ∈ Finset.range n, (2 : ℝ) ^ n := by
        exact Finset.sum_le_sum (by
          intro k hk
          have hkn : k ≤ n := le_of_lt (Finset.mem_range.mp hk)
          exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hkn)
      _ = (n : ℝ) * 2 ^ n := by simp
  have hgeom : (1 + ε) ^ n - 1 ≤ (n : ℝ) * 2 ^ n * ε := by
    have hgm := geom_sum_mul (1 + ε) n
    -- (Σ (1+ε)^k)·((1+ε)−1) = (1+ε)^n − 1; (1+ε)−1 = ε
    have hgm' : (1 + ε) ^ n - 1 = (∑ k ∈ Finset.range n, (1 + ε) ^ k) * ε := by
      rw [show (1 + ε) - 1 = ε by ring] at hgm
      exact hgm.symm
    rw [hgm']
    exact mul_le_mul_of_nonneg_right hsum_le hε0
  have hup : (∏ i : Fin n, (1 + M i i)) - 1 ≤ (n : ℝ) * 2 ^ n * ε :=
    le_trans hup1 hgeom
  -- lower: ∏ ≥ (1−ε)ⁿ ≥ 1−nε ⟹ 1 − ∏ ≤ nε ≤ n·2ⁿ·ε
  have hbern := bernoulli_lower n ε hε0 hε1
  have hlo1 : 1 - (∏ i : Fin n, (1 + M i i)) ≤ (n : ℝ) * ε := by
    linarith [hs.1, hbern]
  have h2n : (1 : ℝ) ≤ 2 ^ n := by
    have := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (Nat.zero_le n)
    simpa using this
  have hlo : 1 - (∏ i : Fin n, (1 + M i i)) ≤ (n : ℝ) * 2 ^ n * ε := by
    nlinarith [hlo1, h2n, hε0]
  exact (abs_le.mpr ⟨by linarith [hlo], hup⟩)


lemma perm_term_bound (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (ε : ℝ)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (hM : ∀ i j : Fin n, |M i j| ≤ ε)
    {σ : Equiv.Perm (Fin n)} (hσ : σ ≠ 1) :
    (∏ i : Fin n, |(1 + M) (σ i) i|) ≤ ε * 2 ^ (n - 1) := by
  classical
  have hfac2 (i : Fin n) : |(1 + M) (σ i) i| ≤ 2 := by
    by_cases h : σ i = i
    · have hm : |M (σ i) i| = |M i i| := by rw [h]
      have hent : (1 + M) (σ i) i = (1 : ℝ) + M (σ i) i := by
        rw [h]
        simp
      calc
        |(1 + M) (σ i) i| ≤ 1 + |M (σ i) i| := by
          rw [hent]
          simpa using (abs_add_le (1 : ℝ) (M (σ i) i))
        _ ≤ 1 + ε := by
          rw [hm]
          exact add_le_add le_rfl (hM i i)
        _ ≤ 2 := by linarith
    · have hm : |(1 + M) (σ i) i| = |M (σ i) i| := by
        simp [h]
      calc
        |(1 + M) (σ i) i| = |M (σ i) i| := hm
        _ ≤ ε := hM (σ i) i
        _ ≤ 2 := by linarith
  have hne : ∃ i : Fin n, σ i ≠ i := by
    by_contra h
    have hall : σ = 1 := by
      apply Equiv.ext
      intro i
      by_contra hi
      exact h ⟨i, hi⟩
    exact hσ hall
  let i₀ : Fin n := Classical.choose hne
  have hi₀ : σ i₀ ≠ i₀ := Classical.choose_spec hne
  have h0 : |(1 + M) (σ i₀) i₀| ≤ ε := by
    have hm : |(1 + M) (σ i₀) i₀| = |M (σ i₀) i₀| := by
      simp [hi₀]
    rw [hm]
    exact hM (σ i₀) i₀
  let s : Finset (Fin n) := Finset.univ.erase i₀
  have hcard : s.card = n - 1 := by
    dsimp [s]
    rw [Finset.card_erase_of_mem (Finset.mem_univ i₀)]
    simp
  have hnon0 : 0 ≤ (∏ i ∈ s, |(1 + M) (σ i) i|) := by
    exact Finset.prod_nonneg (by intro i hi; exact abs_nonneg _)
  have hnonE : 0 ≤ ε := hε0
  calc
    (∏ i : Fin n, |(1 + M) (σ i) i|)
        = |(1 + M) (σ i₀) i₀| * (∏ i ∈ s, |(1 + M) (σ i) i|) := by
          dsimp [s]
          exact (Finset.mul_prod_erase (Finset.univ : Finset (Fin n))
            (fun i => |(1 + M) (σ i) i|) (Finset.mem_univ i₀)).symm
    _ ≤ ε * (∏ i ∈ s, |(1 + M) (σ i) i|) := by
      exact mul_le_mul_of_nonneg_right h0 hnon0
    _ ≤ ε * (∏ i ∈ s, (2 : ℝ)) := by
      exact mul_le_mul_of_nonneg_left (Finset.prod_le_prod (f := fun i : Fin n => |(1 + M) (σ i) i|)
        (g := fun _ : Fin n => (2 : ℝ)) (s := s)
        ((by intro i hi; exact abs_nonneg _)) ((by intro i hi; exact hfac2 i))) hε0
    _ = ε * 2 ^ (n - 1) := by
      rw [Finset.prod_const]
      rw [hcard]

lemma sign_smul_abs (u : ℤˣ) (q : ℝ) : |u • q| = |q| := by
  rcases Int.units_eq_one_or u with h | h
  · rw [h]; norm_num
  · rw [h]; norm_num

/-- `|(1+M).det − 1| ≤ (n! + n)·2ⁿ·ε` from entry bounds `|M i j| ≤ ε`, `0 ≤ ε ≤ 1`. -/
lemma det_one_add_close (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (ε : ℝ)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (hM : ∀ i j : Fin n, |M i j| ≤ ε) :
    |(1 + M).det - 1| ≤ (((n.factorial : ℝ) + n) * 2 ^ n) * ε := by
  classical
  let T : Equiv.Perm (Fin n) → ℝ := fun σ => Equiv.Perm.sign σ • (∏ i : Fin n, (1 + M) (σ i) i)
  let Er : Finset (Equiv.Perm (Fin n)) := Finset.univ.erase (1 : Equiv.Perm (Fin n))
  have hT1 : T 1 = ∏ i : Fin n, ((1 : ℝ) + M i i) := by
    dsimp [T]
    simp [Matrix.one_apply]
  have hdia : |T 1 - 1| ≤ (n : ℝ) * 2 ^ n * ε := by
    rw [hT1]
    exact diag_prod_one_close n M ε hε0 hε1 (by intro i; exact hM i i)
  have hT (σ : Equiv.Perm (Fin n)) (hσ : σ ≠ 1) : |T σ| ≤ ε * 2 ^ (n - 1) := by
    dsimp [T]
    rw [sign_smul_abs]
    have h1 : |∏ i : Fin n, (1 + M) (σ i) i| ≤ ∏ i : Fin n, |(1 + M) (σ i) i| := by
      rw [Finset.abs_prod]
    exact le_trans h1 (perm_term_bound n M ε hε0 hε1 hM hσ)
  have hdet : (1 + M).det = ∑ σ : Equiv.Perm (Fin n), T σ := by
    rw [Matrix.det_apply]
  have hsplit : (1 + M).det = T 1 + ∑ σ ∈ Er, T σ := by
    rw [hdet]
    have hs := Finset.sum_erase_add (Finset.univ : Finset (Equiv.Perm (Fin n))) T
      (Finset.mem_univ (1 : Equiv.Perm (Fin n)))
    have hc : (∑ σ ∈ (Finset.univ : Finset (Equiv.Perm (Fin n))), T σ)
        = T 1 + ∑ σ ∈ Er, T σ := by
      simpa [Er, add_comm, add_left_comm, add_assoc] using hs.symm
    simpa using hc
  have hcardN : (Er.card : ℝ) ≤ (n.factorial : ℝ) := by
    dsimp [Er]
    have hc0 : (Finset.univ.erase (1 : Equiv.Perm (Fin n))).card ≤ (Finset.univ : Finset (Equiv.Perm (Fin n))).card :=
      Finset.card_le_card (Finset.erase_subset _ _)
    have hc1 : (Finset.univ : Finset (Equiv.Perm (Fin n))).card = n.factorial := by
      simpa [Fintype.card_perm]
    rw [hc1] at hc0
    exact_mod_cast hc0
  have hsumT : |∑ σ ∈ Er, T σ| ≤ ((n.factorial : ℝ)) * ε * 2 ^ (n - 1) := by
    calc
      |∑ σ ∈ Er, T σ| ≤ ∑ σ ∈ Er, |T σ| := Finset.abs_sum_le_sum_abs T Er
      _ ≤ ∑ σ ∈ Er, ε * 2 ^ (n - 1) := by
            exact Finset.sum_le_sum (by
              intro σ hσ
              have hne : σ ≠ 1 := (Finset.mem_erase.mp hσ).1
              exact hT σ hne)
      _ = (Er.card : ℝ) * (ε * 2 ^ (n - 1)) := by
            rw [Finset.sum_const]
            simp
      _ ≤ ((n.factorial : ℝ)) * ε * 2 ^ (n - 1) := by
            have hnε : 0 ≤ ε * 2 ^ (n - 1) := mul_nonneg hε0 (pow_nonneg (by norm_num) _)
            nlinarith [hcardN, hnε]
  have hcomb : |(T 1 - 1) + ∑ σ ∈ Er, T σ| ≤ (n : ℝ) * 2 ^ n * ε + (n.factorial : ℝ) * ε * 2 ^ (n - 1) := by
    have h1 := abs_add_le (T 1 - 1) (∑ σ ∈ Er, T σ)
    nlinarith [hdia, hsumT]
  have hdd : |(1 + M).det - 1| = |(T 1 - 1) + ∑ σ ∈ Er, T σ| := by
    rw [hsplit]
    dsimp [Er]
    congr 1
    ring
  have hbig : (n : ℝ) * 2 ^ n * ε + (n.factorial : ℝ) * ε * 2 ^ (n - 1) ≤ (((n.factorial : ℝ) + n) * 2 ^ n) * ε := by
    have hp : (2 : ℝ) ^ (n - 1) ≤ (2 : ℝ) ^ n := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (Nat.sub_le n 1)
    have hnn : 0 ≤ (n.factorial : ℝ) := by positivity
    have h2a : (n.factorial : ℝ) * ε * 2 ^ (n - 1) ≤ (n.factorial : ℝ) * ε * 2 ^ n := by
      exact mul_le_mul_of_nonneg_left hp (mul_nonneg hnn hε0)
    nlinarith [h2a, hε0]
  rw [hdd]
  exact le_trans hcomb hbig

/-! ## Scalar-shell volume difference (same_grad-VL volume bound input)

For a convex set `V` containing `0` and `0 ≤ a < 1`, the two scaled sets
`(1+a)·V` and `(1−a)·V` are nested (`smul_subset_smul_of_le`), so the real volume of
the shell `(1+a)·V ∖ (1−a)·V` equals `((1+a)^m − (1−a)^m)·vol V` exactly via
`measureReal_inter_add_sdiff₀` + `measureReal_smul`.  This is the `vol(V̂) ≤
C·‖M‖·vol V` volume estimate of `thm:same_grad_VL` (with `a := ν‖M‖`), bounded
arithmetically by `≤ 2^{m+1}·a·vol V` for `a ≤ 1/2` at the use site.
`smul_measurableSet_of_measurableSet` (image of a measurable set under nonzero real
scalar multiplication is measurable, via the measurable equivalence of the scalar
linear map) is the measurability transport used throughout. -/

/-- linear equiv for scalar multiplication by nonzero c -/
noncomputable def smulLinEquiv (c : ℝ) (hc : c ≠ 0) : E ≃ₗ[ℝ] E where
  toFun := fun x => c • x
  invFun := fun x => c⁻¹ • x
  map_add' := by intro x y; simp [smul_add]
  map_smul' := by intro a x; simp [smul_smul, mul_comm]
  left_inv := by
    intro x
    dsimp
    rw [smul_smul]
    field_simp [hc]
    simp
  right_inv := by
    intro x
    dsimp
    rw [smul_smul]
    field_simp [hc]
    simp

lemma smul_measurableSet_of_measurableSet {c : ℝ} (hc : c ≠ 0) {V : Set E}
    (hV : MeasurableSet V) : MeasurableSet (c • V) := by
  let L : E ≃ₗ[ℝ] E := smulLinEquiv c hc
  let e : E ≃ᵐ E := L.toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv
  have hfun : ∀ x : E, e x = c • x := by
    intro x
    rfl
  have himg : e '' V = c • V := by
    ext y
    constructor
    · intro hy
      rcases hy with ⟨x, hx, hxy⟩
      rw [← hxy]
      rw [hfun]
      exact Set.mem_smul_set.mpr ⟨x, hx, rfl⟩
    · intro hy
      rcases (Set.mem_smul_set.mp hy) with ⟨x, hx, hxy⟩
      refine ⟨x, hx, ?_⟩
      rw [hfun]
      exact hxy
  rw [← himg]
  exact (MeasurableEquiv.measurableSet_image e).mpr hV

/-- real-measure difference bound for a scalar shell `(1+a)V ∖ (1−a)V`, `0 ≤ a < 1`. -/
lemma measureReal_shell_le (a : ℝ) (V : Set E) (hC : Convex ℝ V) (h0 : (0 : E) ∈ V)
    (hVmeas : MeasurableSet V) (hVfin : (volume : Measure E) V ≠ ⊤) (ha0 : 0 ≤ a) (ha1 : a < 1) :
    (volume : Measure E).real (((1 + a) • V) \ ((1 - a) • V)) ≤
      (((1 + a) ^ (Module.finrank ℝ E)) - ((1 - a) ^ (Module.finrank ℝ E))) *
        (volume : Measure E).real V := by
  let s : Set E := (1 + a) • V
  let t : Set E := (1 - a) • V
  have hc1 : 0 ≤ 1 + a := by linarith
  have hc2pos : 0 < 1 - a := by linarith
  have hc2ne : 1 - a ≠ 0 := ne_of_gt hc2pos
  have hc20 : 0 ≤ 1 - a := le_of_lt hc2pos
  have hc21 : 1 - a ≤ 1 + a := by linarith
  have hsub : t ⊆ s := by
    dsimp [s, t]
    exact smul_subset_smul_of_le (V := V) hC h0 hc20 hc21
  have hst : s ∩ t = t := by
    ext x
    constructor
    · intro hx; exact hx.2
    · intro hx; exact ⟨hsub hx, hx⟩
  have htNull : NullMeasurableSet t (volume : Measure E) := by
    dsimp [t]
    exact (smul_measurableSet_of_measurableSet hc2ne hVmeas).nullMeasurableSet
  have hms := measure_smul (1 + a) V
  have hfin_s : (volume : Measure E) s ≠ ⊤ := by
    dsimp [s]
    rw [hms]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hVfin
  have hadd := measureReal_inter_add_sdiff₀ (μ := (volume : Measure E)) (s := s) (t := t) htNull
    (h := hfin_s)
  have hsr : (volume : Measure E).real s = (volume : Measure E).real t +
      (volume : Measure E).real (s \ t) := by
    rw [hst] at hadd
    simpa [add_comm, add_left_comm, add_assoc] using hadd.symm
  have hs : (volume : Measure E).real s =
      (1 + a) ^ (Module.finrank ℝ E) * (volume : Measure E).real V := by
    dsimp [s]
    exact measureReal_smul (1 + a) hc1 V
  have ht : (volume : Measure E).real t =
      (1 - a) ^ (Module.finrank ℝ E) * (volume : Measure E).real V := by
    dsimp [t]
    exact measureReal_smul (1 - a) hc20 V
  have hdiff : (volume : Measure E).real (s \ t) =
      (((1 + a) ^ (Module.finrank ℝ E)) - ((1 - a) ^ (Module.finrank ℝ E))) *
        (volume : Measure E).real V := by
    have hsub2 : (volume : Measure E).real s - (volume : Measure E).real t =
        (volume : Measure E).real (s \ t) := by linarith
    rw [← hsub2]
    rw [hs, ht]
    ring
  rw [hdiff]

/-- **Image-cell upper shell**: `A·V ⊆ (1+νε)·V` (image side of `clm:eps_voronoi` with the
common `ν := 4 + 4R/r`), from `image_cell_subset_scale` + `εR/r ≤ νε`. -/
lemma image_cell_upper_shell (r R ε : ℝ) (hr : 0 < r) (hR0 : 0 ≤ R) (hε0 : 0 ≤ ε)
    {ℒ : Submodule ℤ E} (hball : Metric.closedBall (0 : E) r ⊆ VC ℒ)
    (hcell : VC ℒ ⊆ Metric.closedBall (0 : E) R)
    (A : E →ₗ[ℝ] E) (hA : ∀ w : E, ‖A w - w‖ ≤ ε * ‖w‖) :
    A '' VC ℒ ⊆ (1 + (4 + 4 * (R / r)) * ε) • VC ℒ := by
  have hsub := image_cell_subset_scale (ℒ := ℒ) r R hr hR0 hball hcell A ε hε0 hA
  have hq0 : 0 ≤ R / r := div_nonneg hR0 (le_of_lt hr)
  have hRr : ε * R / r = ε * (R / r) := by
    field_simp [ne_of_gt hr]
  have hle0 : R / r ≤ 4 + 4 * (R / r) := by nlinarith
  have hle : ε * (R / r) ≤ (4 + 4 * (R / r)) * ε := by
    have hm := mul_le_mul_of_nonneg_left hle0 hε0
    -- hm : ε*(R/r) ≤ ε*(4 + 4*(R/r)); goal commuted
    nlinarith [hm]
  have hfac : 1 + ε * R / r ≤ 1 + (4 + 4 * (R / r)) * ε := by
    nlinarith [hRr, hle]
  have hc10 : 0 ≤ 1 + ε * R / r := by
    have hpos : 0 ≤ ε * (R / r) := mul_nonneg hε0 hq0
    nlinarith [hRr, hpos]
  have hVc : Convex ℝ (VC ℒ) := Submission.Voronoi.voronoi_convex ℒ
  have hV0 : (0 : E) ∈ VC ℒ := zero_mem_voronoi ℒ
  exact hsub.trans (smul_subset_smul_of_le hVc hV0 hc10 hfac)

/-- **Lattice-cell lower shell**: `(1−νε)·V ⊆ V(A·ℒ)` (left part of `clm:eps_voronoi` for
the transformed-lattice cell, i.e. `voronoiImage A ℒ`), WITHOUT the `hcellR` bound on the
image cell that the full `voronoiImage_sandwich` requires. -/
lemma voronoiImage_left_shell (r R ε : ℝ) (hr : 0 < r) (hR0 : 0 ≤ R) (hε0 : 0 ≤ ε)
    (hε1 : ε ≤ 1 / 2) (hνe : (4 + 4 * (R / r)) * ε ≤ 1)
    {ℒ : Submodule ℤ E} {A : E →ₗ[ℝ] E}
    (hlam : ∀ z : ℒ, z ≠ 0 → r ≤ ‖(z : E)‖)
    (hA : ∀ w : E, ‖A w - w‖ ≤ ε * ‖w‖)
    (hcell : VC ℒ ⊆ Metric.closedBall (0 : E) R) :
    (1 - (4 + 4 * (R / r)) * ε) • VC ℒ ⊆ voronoiImage A ℒ := by
  let ν : ℝ := 4 + 4 * (R / r)
  have hleft_s : (1 - ν * ε) ≤ (1 - ε) ^ 2 / (1 + 2 * ε * R / r) := by
    dsimp [ν]
    exact scale_left_ge r R ε hr hR0 hε0 hε1
  have hleft0 : 0 ≤ 1 - ν * ε := by
    dsimp [ν]
    exact sub_nonneg.mpr hνe
  have hVc : Convex ℝ (VC ℒ) := Submission.Voronoi.voronoi_convex ℒ
  have hV0 : (0 : E) ∈ VC ℒ := zero_mem_voronoi ℒ
  have hinc1 : (1 - ν * ε) • VC ℒ ⊆ ((1 - ε) ^ 2 / (1 + 2 * ε * R / r)) • VC ℒ := by
    exact smul_subset_smul_of_le hVc hV0 hleft0 hleft_s
  have hinc2 : ((1 - ε) ^ 2 / (1 + 2 * ε * R / r)) • VC ℒ ⊆ voronoiImage A ℒ := by
    exact scaled_cell_subset_voronoiImage r R ε hr hR0 hε1 hε0 hlam hA hcell
  exact hinc1.trans hinc2

/-- **Shell linearization**: for `0 ≤ x ≤ 1`, `(1+x)^m − (1−x)^m ≤ m·2^m·x`.  (Companion of
`measureReal_shell_le`: turns the exact shell difference into an `O(ε)` bound.) -/
lemma shell_pow_lin (m : ℕ) (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    (1 + x) ^ m - (1 - x) ^ m ≤ (m : ℝ) * (2 : ℝ) ^ m * x := by
  induction m with
  | zero => simp
  | succ m ih =>
      have h1x0 : 0 ≤ 1 + x := by linarith
      have h1mx0 : 0 ≤ 1 - x := by linarith
      have h1mx1 : 1 - x ≤ 1 := by linarith
      have h2x0 : 0 ≤ 2 * x := by nlinarith
      have hpow1 : (1 - x) ^ m ≤ 1 := by
        have h := pow_le_pow_left₀ h1mx0 h1mx1 m
        simpa using h
      have hF : (1 + x) ^ m * (1 + x) - (1 - x) ^ m * (1 - x) =
          ((1 + x) ^ m - (1 - x) ^ m) * (1 + x) + (1 - x) ^ m * (2 * x) := by
        ring
      have hterm1 : ((1 + x) ^ m - (1 - x) ^ m) * (1 + x) ≤
          ((m : ℝ) * (2 : ℝ) ^ m * x) * (1 + x) :=
        mul_le_mul_of_nonneg_right ih h1x0
      have hterm2 : (1 - x) ^ m * (2 * x) ≤ 2 * x := by
        exact (mul_le_mul_of_nonneg_right hpow1 h2x0).trans_eq (by ring)
      have hcomb : ((1 + x) ^ m - (1 - x) ^ m) * (1 + x) + (1 - x) ^ m * (2 * x) ≤
          ((m : ℝ) * (2 : ℝ) ^ m * x) * (1 + x) + 2 * x :=
        add_le_add hterm1 hterm2
      have hih0 : 0 ≤ (m : ℝ) * (2 : ℝ) ^ m * x := by
        exact mul_nonneg (mul_nonneg (by positivity : 0 ≤ (m : ℝ)) (pow_nonneg (by norm_num) m)) hx0
      have hb1 : ((m : ℝ) * (2 : ℝ) ^ m * x) * (1 + x) ≤ (m : ℝ) * (2 : ℝ) ^ m * x * 2 := by
        have h1x : 1 + x ≤ 2 := by linarith
        nlinarith [hih0, h1x]
      have hpm : (1 : ℝ) ≤ (2 : ℝ) ^ m := by
        have h := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ (2 : ℝ)) (Nat.zero_le m)
        simpa using h
      have hmul2 := mul_le_mul_of_nonneg_right hpm h2x0
      have hmcast : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by norm_num
      calc
        (1 + x) ^ (m + 1) - (1 - x) ^ (m + 1)
            ≤ ((m : ℝ) * (2 : ℝ) ^ m * x) * (1 + x) + 2 * x := by
              simp only [pow_succ]
              rw [hF]
              exact hcomb
        _ ≤ (m : ℝ) * (2 : ℝ) ^ m * x * 2 + 2 * x := by
              nlinarith [hb1]
        _ ≤ ((m + 1 : ℕ) : ℝ) * (2 : ℝ) ^ (m + 1) * x := by
              rw [hmcast]
              simp only [pow_succ']
              nlinarith [hmul2]
end Submission.EpsVoronoi