import Submission.FUP.HSHoles
import Submission.FUP.BoxPorosity

open FractalUncertainty MeasureTheory FourierTransform Metric Filter Set Pointwise
open scoped ENNReal BigOperators Topology ContDiff

set_option autoImplicit false
variable {d : ℕ}
local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)

/-!
# Han–Schlag's §5: the `L`-adic grid with integer indices, and the corrected hole set

`Submission/FUP/ROADMAP.md`, Session 52: Han–Schlag's Corollary 4.2 (`cor:UPY`) places one square
of side `2c₁` in **every** cell of the grid and concludes `‖f‖ ≤ C_*‖f·1_S‖`.  The §5 induction
therefore has to use the localisation set on *all* cells of the rescaled `L`-adic grid, and the
hole set `U_{mT+1}` = half-cubes of **all** empty cells of generation `mT+1` (which contains a
cube of side `L^{-1}` in every gen-`mT` cell: by porosity in the cells meeting `X`, trivially in
the others).

The `ℕ`-indexed grid of `Submission.FUP.BoxPorosity` only covers `[-1,1]^d`; this module provides
the `ℤ`-indexed refinement covering all of `ℝ^d`.
-/

namespace Submission.FUP

/-! ## The grid with integer indices -/

/-- The `L`-adic grid cell at depth `n` with integer multi-index `k`. -/
def gridBoxZ (L n : ℕ) (k : Fin d → ℤ) : Set ℝᵈ :=
  box (fun i => -1 + 2 * (k i : ℝ) * hss L n)
      (fun i => -1 + 2 * ((k i : ℝ) + 1) * hss L n)

lemma measurableSet_gridBoxZ (L n : ℕ) (k : Fin d → ℤ) : MeasurableSet (gridBoxZ L n k) :=
  measurableSet_box _ _

lemma gridBoxZ_natCast (L n : ℕ) (k : Fin d → ℕ) :
    gridBoxZ L n (fun i => (k i : ℤ)) = gridBox L n k := by
  unfold gridBoxZ gridBox
  congr 1 <;> · funext i; norm_num

/-- Index of a child cell (integer version). -/
def childIndexZ (L : ℕ) (k : Fin d → ℤ) (j : Fin d → Fin L) : Fin d → ℤ :=
  fun i => L * k i + (j i : ℤ)

lemma childIndexZ_natCast (L : ℕ) (k : Fin d → ℕ) (j : Fin d → Fin L) :
    childIndexZ L (fun i => (k i : ℤ)) j = fun i => (childIndex L k j i : ℤ) := by
  funext i
  simp only [childIndexZ, childIndex]
  push_cast
  ring

lemma gridBoxZ_child_subset {L n : ℕ} (hL : 0 < L) (k : Fin d → ℤ) (j : Fin d → Fin L) :
    gridBoxZ L (n + 1) (childIndexZ L k j) ⊆ gridBoxZ L n k := by
  refine box_subset_box ?_ ?_ <;> intro i
  · have hs : hss L (n+1) = hss L n / L := hss_succ hL n
    have hLr : (0:ℝ) < L := by exact_mod_cast hL
    have hh : 0 < hss L n := hss_pos hL n
    rw [hs]
    show -1 + 2 * (k i : ℝ) * hss L n
      ≤ -1 + 2 * (childIndexZ L k j i : ℝ) * (hss L n / L)
    have hK : (childIndexZ L k j i : ℝ) = (L:ℝ) * (k i : ℝ) + (j i : ℝ) := by
      simp only [childIndexZ]; push_cast; ring
    rw [hK]
    have hkn : (k i : ℝ) * (L:ℝ) ≤ (L:ℝ) * (k i : ℝ) + (j i : ℝ) := by
      have : (0:ℝ) ≤ (j i : ℝ) := by positivity
      nlinarith
    have hle : 2 * (k i : ℝ) * hss L n
        ≤ 2 * ((L:ℝ) * (k i:ℝ) + (j i:ℝ)) * (hss L n / L) := by
      rw [← mul_div_assoc]
      rw [le_div_iff₀ hLr]
      have hm := mul_le_mul_of_nonneg_right hkn (by positivity : (0:ℝ) ≤ 2 * hss L n)
      nlinarith [hm]
    linarith
  · have hs : hss L (n+1) = hss L n / L := hss_succ hL n
    have hLr : (0:ℝ) < L := by exact_mod_cast hL
    have hh : 0 < hss L n := hss_pos hL n
    rw [hs]
    show -1 + 2 * ((childIndexZ L k j i : ℝ) + 1) * (hss L n / L)
        ≤ -1 + 2 * ((k i : ℝ) + 1) * hss L n
    have hK : (childIndexZ L k j i : ℝ) = (L:ℝ) * (k i : ℝ) + (j i : ℝ) := by
      simp only [childIndexZ]; push_cast; ring
    rw [hK]
    have hj : (j i : ℝ) + 1 ≤ (L:ℝ) := by
      have h2 : ((j i : ℕ) + 1 : ℕ) ≤ L := Nat.succ_le_iff.mpr (j i).isLt
      exact_mod_cast h2
    have hle : 2 * ((L:ℝ) * (k i:ℝ) + (j i:ℝ) + 1) * (hss L n / L)
        ≤ 2 * ((k i : ℝ) + 1) * hss L n := by
      rw [← mul_div_assoc]
      rw [div_le_iff₀ hLr]
      have h1 : (2 * ((L:ℝ) * (k i:ℝ) + (j i:ℝ) + 1)) * hss L n
          ≤ (2 * ((L:ℝ) * ((k i:ℝ) + 1))) * hss L n := by
        apply mul_le_mul_of_nonneg_right _ (le_of_lt hh)
        nlinarith [hj]
      calc (2 * ((L:ℝ) * (k i:ℝ) + (j i:ℝ) + 1)) * hss L n
          ≤ (2 * ((L:ℝ) * ((k i:ℝ) + 1))) * hss L n := h1
        _ = (2 * ((k i:ℝ) + 1) * hss L n) * L := by ring
    linarith

/-- The concentric half-cube of a cell (integer version). -/
noncomputable def halfCubeZ (L n : ℕ) (k : Fin d → ℤ) : Set ℝᵈ :=
  box (fun i => -1 + 2 * (k i : ℝ) * hss L n + hss L n / 2)
      (fun i => -1 + 2 * ((k i : ℝ) + 1) * hss L n - hss L n / 2)

lemma halfCubeZ_natCast (L n : ℕ) (k : Fin d → ℕ) :
    halfCubeZ L n (fun i => (k i : ℤ)) = halfCube L n k := by
  unfold halfCubeZ halfCube
  congr 1 <;> · funext i; norm_num

lemma halfCubeZ_subset_gridBoxZ (L n : ℕ) (k : Fin d → ℤ) :
    halfCubeZ L n k ⊆ gridBoxZ L n k := by
  refine box_subset_box ?_ ?_ <;> intro i
  · show -1 + 2 * (k i : ℝ) * hss L n ≤ -1 + 2 * (k i : ℝ) * hss L n + hss L n / 2
    have := hss_nonneg L n; linarith
  · show -1 + 2 * ((k i : ℝ) + 1) * hss L n - hss L n / 2
      ≤ -1 + 2 * ((k i : ℝ) + 1) * hss L n
    have := hss_nonneg L n; linarith

lemma smul_halfCubeZ {L n : ℕ} (k : Fin d → ℤ) {s : ℝ} (hs : 0 < s) :
    s • halfCubeZ L n k
      = box (fun i => s * (-1 + 2 * (k i : ℝ) * hss L n + hss L n / 2))
            (fun i => s * (-1 + 2 * ((k i : ℝ) + 1) * hss L n - hss L n / 2)) := by
  rw [halfCubeZ, smul_box hs]

/-- A point of a half-cube of a cell has a coordinate at distance at least half the side length
from any point of any other cell at the same depth (integer indices). -/
lemma exists_coord_hss_half_le_of_mem_halfCubeZ_of_mem_gridBoxZ {L n : ℕ} (hL : 0 < L)
    {k k' : Fin d → ℤ} (hne : k' ≠ k) {z s : ℝᵈ} (hz : z ∈ halfCubeZ L n k)
    (hs : s ∈ gridBoxZ L n k') : ∃ i : Fin d, hss L n / 2 ≤ |z i - s i| := by
  have hLn0 : (0:ℝ) < hss L n := hss_pos hL n
  obtain ⟨i, hi⟩ : ∃ i, k' i ≠ k i := by
    by_contra h
    push Not at h
    exact hne (funext h)
  refine ⟨i, ?_⟩
  rw [halfCubeZ, mem_box] at hz
  rw [gridBoxZ, mem_box] at hs
  rcases lt_or_gt_of_ne hi with hlt | hgt
  · have hki : (k' i : ℝ) + 1 ≤ (k i : ℝ) := by
      have hZ : k' i + 1 ≤ k i := by omega
      exact_mod_cast hZ
    have hsle : s i ≤ -1 + 2 * (k i : ℝ) * hss L n := by
      have h := (hs i).2
      nlinarith [hLn0, hki, h]
    have hzge : -1 + 2 * (k i : ℝ) * hss L n + hss L n / 2 ≤ z i := (hz i).1
    rw [abs_of_nonneg (by linarith)]
    linarith
  · have hki : (k i : ℝ) + 1 ≤ (k' i : ℝ) := by
      have hZ : k i + 1 ≤ k' i := by omega
      exact_mod_cast hZ
    have hsge : -1 + 2 * (k i : ℝ) * hss L n + 2 * hss L n ≤ s i := by
      have h := (hs i).1
      nlinarith [hLn0, hki, h]
    have hzle : z i ≤ -1 + 2 * ((k i : ℝ) + 1) * hss L n - hss L n / 2 := (hz i).2
    rw [abs_of_nonpos (by linarith)]
    linarith


/-! ## The corrected hole set `U_{n+1}`: the half-cubes of *all* empty cells -/

/-- Han–Schlag's hole set `U_{n+1}`, corrected (Session 52): the union of the half-cubes of **all**
depth-`(n+1)` cells that miss `X`.  This set contains a cube of side `L^{-(n+1)}` in *every*
depth-`n` cell — by porosity for the cells meeting `X`, and trivially for the others — so it is a
valid localisation set for Corollary 4.2. -/
noncomputable def UstarZ (L : ℕ) (X : Set ℝᵈ) (n : ℕ) : Set ℝᵈ :=
  {z : ℝᵈ | ∃ k : Fin d → ℤ, X ∩ gridBoxZ L (n+1) k = ∅ ∧ z ∈ halfCubeZ L (n+1) k}

lemma mem_UstarZ {L n : ℕ} {X : Set ℝᵈ} {z : ℝᵈ} :
    z ∈ UstarZ L X n ↔ ∃ k : Fin d → ℤ, X ∩ gridBoxZ L (n+1) k = ∅ ∧
      z ∈ halfCubeZ L (n+1) k := Iff.rfl

lemma measurableSet_UstarZ (L : ℕ) (X : Set ℝᵈ) (n : ℕ) : MeasurableSet (UstarZ L X n) := by
  have h : UstarZ L X n = ⋃ k : Fin d → ℤ, ⋃ (_ : X ∩ gridBoxZ L (n+1) k = ∅),
      halfCubeZ L (n+1) k := by
    ext z
    simp only [mem_UstarZ, Set.mem_iUnion, exists_prop]
  rw [h]
  exact MeasurableSet.iUnion fun k => MeasurableSet.iUnion fun _ => measurableSet_box _ _

/-- **Upper bound on `Ψ_n` at points of the corrected holes `U_{n+1}`** (Han–Schlag (5-5)). -/
theorem Psi_upperZ {L T n : ℕ} (hL : 1 ≤ L) (Φ : FupCutoff d) {X : Set ℝᵈ}
    {x : ℝᵈ} (hx : x ∈ UstarZ L X n) :
    Psi Φ L T X n x ≤
      ∫ w in {w : ℝᵈ | (L : ℝ) ^ (n + T) * (2 * hss L (n+1) / 5) ≤ ‖w‖}, Φ.reFun w := by
  classical
  have hLpos : 0 < L := lt_of_lt_of_le one_pos hL
  have hLr : (0:ℝ) < (L:ℝ) := by exact_mod_cast hLpos
  have hc : (0:ℝ) < (L : ℝ) ^ (n + T) := pow_pos hLr _
  have hLn0 : (0:ℝ) < hss L (n+1) := hss_pos hLpos (n+1)
  obtain ⟨Q, hQ, hxc⟩ := hx
  -- a point within `ℓ^∞`-distance `L^{-(n+1)}/10` of a cell meeting `X` is far from every hole
  have hfar : ∀ z : ℝᵈ, x - z ∈ StarS L X (n+1) → 2 * hss L (n+1) / 5 ≤ ‖z‖ := by
    intro z hz
    obtain ⟨k, hkne, hzk⟩ := hz
    rw [fattenBox, mem_box] at hzk
    have hQne : (fun i => (k i : ℤ)) ≠ Q := by
      intro h
      have h2 : X ∩ gridBoxZ L (n+1) (fun i => (k i : ℤ)) = ∅ := by rw [h]; exact hQ
      rw [gridBoxZ_natCast] at h2
      exact (Set.Nonempty.ne_empty hkne) h2
    obtain ⟨i, hi⟩ : ∃ i, Q i ≠ (k i : ℤ) := by
      by_contra h
      push Not at h
      exact hQne (funext fun i => (h i).symm)
    rw [halfCubeZ, mem_box] at hxc
    have hcoord : 2 * hss L (n+1) / 5 ≤ |z i| := by
      rcases lt_or_gt_of_ne hi with hlt | hgt
      · have hki : (Q i : ℝ) + 1 ≤ (k i : ℝ) := by
          have hZ : Q i + 1 ≤ (k i : ℤ) := by omega
          exact_mod_cast hZ
        have hlo : -1 + 2 * (k i : ℝ) * hss L (n+1) - hss L (n+1) / 10 ≤ (x - z) i := (hzk i).1
        have hxu : x i ≤ -1 + 2 * ((Q i : ℝ) + 1) * hss L (n+1) - hss L (n+1) / 2 := (hxc i).2
        have hzsub : z i = x i - (x - z) i := by rw [sub_apply']; ring
        have hzle : z i ≤ -(2 * hss L (n+1) / 5) := by
          rw [hzsub]; nlinarith [hLn0, hlo, hxu, hki]
        rw [abs_of_nonpos (by linarith), hzsub]
        linarith
      · have hki : (k i : ℝ) + 1 ≤ (Q i : ℝ) := by
          have hZ : (k i : ℤ) + 1 ≤ Q i := by omega
          exact_mod_cast hZ
        have hhi : (x - z) i ≤ -1 + 2 * (Q i : ℝ) * hss L (n+1) + hss L (n+1) / 10 := by
          have h := (hzk i).2
          nlinarith [hLn0, hki, h]
        have hxl : -1 + 2 * (Q i : ℝ) * hss L (n+1) + hss L (n+1) / 2 ≤ x i := (hxc i).1
        have hzsub : z i = x i - (x - z) i := by rw [sub_apply']; ring
        have hzge : 2 * hss L (n+1) / 5 ≤ z i := by
          rw [hzsub]; nlinarith [hhi, hxl]
        rw [abs_of_nonneg (by linarith), hzsub]
        linarith
    calc 2 * hss L (n+1) / 5 ≤ |z i| := hcoord
      _ = ‖z i‖ := by rw [Real.norm_eq_abs]
      _ ≤ ‖z‖ := PiLp.norm_apply_le z i
  have hmono : ∀ z : ℝᵈ, scaleFun Φ.reFun ((L : ℝ) ^ (n + T)) z *
        (StarS L X (n+1)).indicator (fun _ => (1 : ℝ)) (x - z)
      ≤ scaleFun Φ.reFun ((L : ℝ) ^ (n + T)) z *
        ({w : ℝᵈ | 2 * hss L (n+1) / 5 ≤ ‖w‖}).indicator (fun _ => (1 : ℝ)) z := by
    intro z
    have h2 : 0 ≤ scaleFun Φ.reFun ((L : ℝ) ^ (n + T)) z :=
      scaleFun_nonneg Φ.reFun_nonneg hc.le z
    by_cases hz : z ∈ ({w : ℝᵈ | 2 * hss L (n+1) / 5 ≤ ‖w‖} : Set ℝᵈ)
    · have hz1 : ({w : ℝᵈ | 2 * hss L (n+1) / 5 ≤ ‖w‖} : Set ℝᵈ).indicator
          (fun _ => (1 : ℝ)) z = 1 := Set.indicator_of_mem (f := fun _ => (1 : ℝ)) hz
      rw [hz1]
      exact mul_le_mul_of_nonneg_left (indicator_one_le_one _ _) h2
    · have hz0 : ({w : ℝᵈ | 2 * hss L (n+1) / 5 ≤ ‖w‖} : Set ℝᵈ).indicator
          (fun _ => (1 : ℝ)) z = 0 := Set.indicator_of_notMem (f := fun _ => (1 : ℝ)) hz
      have hzind : (StarS L X (n+1)).indicator (fun _ => (1 : ℝ)) (x - z) = 0 :=
        Set.indicator_of_notMem (f := fun _ => (1 : ℝ)) (fun hmem => hz (hfar z hmem))
      rw [hzind, hz0]
  have hstep : Psi Φ L T X n x ≤ ∫ z, scaleFun Φ.reFun ((L : ℝ) ^ (n + T)) z *
        ({w : ℝᵈ | 2 * hss L (n+1) / 5 ≤ ‖w‖}).indicator (fun _ => (1 : ℝ)) z :=
    integral_mono (integrable_Psi_integrand hL Φ T n X x)
      (integrable_scaleFun_indicator Φ hc (measurableSet_le measurable_const measurable_norm)) hmono
  have hchange := integral_scaleFun_indicator Φ hc
    (S := {w : ℝᵈ | 2 * hss L (n+1) / 5 ≤ ‖w‖}) (measurableSet_le measurable_const measurable_norm)
  have hset : (L : ℝ) ^ (n + T) • {w : ℝᵈ | 2 * hss L (n+1) / 5 ≤ ‖w‖}
      = {w : ℝᵈ | (L : ℝ) ^ (n + T) * (2 * hss L (n+1) / 5) ≤ ‖w‖} := by
    ext w
    simp only [Set.mem_smul_set, Set.mem_setOf_eq]
    constructor
    · rintro ⟨z, hz, rfl⟩
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc]
      exact mul_le_mul_of_nonneg_left hz hc.le
    · intro hw
      refine ⟨((L:ℝ)^(n+T))⁻¹ • w, ?_, by rw [smul_inv_smul₀ hc.ne']⟩
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hc)]
      have h2 : ((L:ℝ)^(n+T))⁻¹ * ((L:ℝ)^(n+T) * (2 * hss L (n+1) / 5))
          = 2 * hss L (n+1) / 5 := by
        rw [← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul]
      calc 2 * hss L (n+1) / 5 = ((L:ℝ)^(n+T))⁻¹ * ((L:ℝ)^(n+T) * (2*hss L (n+1)/5)) := h2.symm
        _ ≤ ((L:ℝ)^(n+T))⁻¹ * ‖w‖ := mul_le_mul_of_nonneg_left hw (by positivity)
  rw [hset] at hchange
  linarith [hstep, hchange]


/-! ## The localisation set over *all* cells of the rescaled grid -/

/-- The rescaled half-cube of a child of a (integer-indexed) gen-`(mT)` cell is the cube
`holeCube`. -/
lemma holeCube_eq_smul_halfCubeZ {L : ℕ} (hL : 0 < L) (T m : ℕ) (k : Fin d → ℤ)
    (j : Fin d → Fin L) :
    rescaleFactor L T m • halfCubeZ L (m * T + 1) (childIndexZ L k j) = holeCube L T m k j := by
  rw [smul_halfCubeZ (childIndexZ L k j) (rescaleFactor_pos hL T m), holeCube]
  have h : rescaleFactor L T m * hss L (m * T + 1) = (L : ℝ)⁻¹ :=
    rescaleFactor_mul_hss_succ hL T m
  have hstep : ∀ i : Fin d,
      rescaleFactor L T m *
          (-1 + 2 * (childIndexZ L k j i : ℝ) * hss L (m * T + 1) + hss L (m * T + 1) / 2)
        = holeLower L T m k j i := by
    intro i
    have hc : (childIndexZ L k j i : ℝ) = (L:ℝ) * (k i : ℝ) + (j i : ℝ) := by
      simp only [childIndexZ]; push_cast; ring
    rw [hc, holeLower]
    have hexp : rescaleFactor L T m *
          (-1 + 2 * ((L:ℝ) * (k i : ℝ) + (j i : ℝ)) * hss L (m * T + 1)
            + hss L (m * T + 1) / 2)
        = -rescaleFactor L T m
          + 2 * ((L:ℝ) * (k i : ℝ) + (j i : ℝ)) * (rescaleFactor L T m * hss L (m * T + 1))
          + (rescaleFactor L T m * hss L (m * T + 1)) / 2 := by ring
    rw [hexp, h]
    field_simp
    ring
  have hstep' : ∀ i : Fin d,
      rescaleFactor L T m *
          (-1 + 2 * (((childIndexZ L k j i : ℤ) : ℝ) + 1) * hss L (m * T + 1)
            - hss L (m * T + 1) / 2)
        = holeLower L T m k j i + locSide L := by
    intro i
    have hc : (childIndexZ L k j i : ℝ) = (L:ℝ) * (k i : ℝ) + (j i : ℝ) := by
      simp only [childIndexZ]; push_cast; ring
    rw [hc, holeLower, locSide]
    have hexp : rescaleFactor L T m *
          (-1 + 2 * (((L:ℝ) * (k i : ℝ) + (j i : ℝ)) + 1) * hss L (m * T + 1)
            - hss L (m * T + 1) / 2)
        = -rescaleFactor L T m
          + 2 * (((L:ℝ) * (k i : ℝ) + (j i : ℝ)) + 1) * (rescaleFactor L T m * hss L (m * T + 1))
          - (rescaleFactor L T m * hss L (m * T + 1)) / 2 := by ring
    rw [hexp, h]
    field_simp
    ring
  congr 1
  · funext i; exact hstep i
  · funext i; exact hstep' i

/-- The (classical) choice of a missing child of a cell, from box porosity. -/
noncomputable def holeSel {L T m : ℕ} (hL : 0 < L) (X : Set ℝᵈ)
    (hpor : BoxPorous L (m * T + 1) X) : (Fin d → ℤ) → Fin d → Fin L := by
  classical
  exact fun n => if h : (X ∩ gridBox L (m * T) (fun i => (n i).toNat)).Nonempty then
      Classical.choose (hpor (m * T) (by omega) (fun i => (n i).toNat) h)
    else fun _ => ⟨0, hL⟩

lemma holeSel_spec {L T m : ℕ} (hL : 0 < L) {X : Set ℝᵈ} (hpor : BoxPorous L (m * T + 1) X)
    {n : Fin d → ℤ} (hn : (∀ i : Fin d, 0 ≤ n i) ∧
      (X ∩ gridBox L (m * T) (fun i => (n i).toNat)).Nonempty) :
    X ∩ gridBox L (m * T + 1)
      (childIndex L (fun i => (n i).toNat) (holeSel hL X hpor n)) = ∅ := by
  classical
  have hne : (X ∩ gridBox L (m * T) (fun i => (n i).toNat)).Nonempty := hn.2
  rw [holeSel, dif_pos hne, Set.inter_comm]
  exact Classical.choose_spec (hpor (m * T) (by omega) (fun i => (n i).toNat) hne)

/-- A choice of a missing child for **every** integer-indexed gen-`(mT)` cell: for the cells
meeting `X` (and inside `[-1,1]^d`) the porosity child exists; for the cells inside `[-1,1]^d`
that miss `X` every child misses `X`; and for the cells outside `[-1,1]^d` the first child lies
outside `[-1,1]^d` (in a negative coordinate) and hence misses `X ⊆ [-1,1]^d`. -/
noncomputable def holeSelZ {L T m : ℕ} (hL : 0 < L) (X : Set ℝᵈ)
    (hpor : BoxPorous L (m * T + 1) X) : (Fin d → ℤ) → Fin d → Fin L := by
  classical
  exact fun n => if h : (∀ i : Fin d, 0 ≤ n i) ∧
      (X ∩ gridBox L (m * T) (fun i => (n i).toNat)).Nonempty
    then holeSel hL X hpor n
    else fun _ => ⟨0, hL⟩

lemma holeSelZ_empty {L T m : ℕ} (hL : 0 < L) (hL2 : 2 ≤ L) {X : Set ℝᵈ}
    (hX : X ⊆ cube (-1) 1) (hpor : BoxPorous L (m * T + 1) X) (n : Fin d → ℤ) :
    X ∩ gridBoxZ L (m * T + 1) (childIndexZ L n (holeSelZ hL X hpor n)) = ∅ := by
  classical
  by_cases hn : (∀ i : Fin d, 0 ≤ n i) ∧
      (X ∩ gridBox L (m * T) (fun i => (n i).toNat)).Nonempty
  · have hsel : holeSelZ hL X hpor n = holeSel hL X hpor n := by
      unfold holeSelZ; rw [dif_pos hn]
    rw [hsel]
    have hn_eq : n = fun i => ((n i).toNat : ℤ) := by
      funext i; exact (Int.toNat_of_nonneg (hn.1 i)).symm
    have hchild : childIndexZ L n (holeSel hL X hpor n)
        = fun i => (childIndex L (fun i => (n i).toNat) (holeSel hL X hpor n) i : ℤ) := by
      rw [hn_eq]
      exact childIndexZ_natCast L (fun i => (n i).toNat) (holeSel hL X hpor n)
    rw [hchild, gridBoxZ_natCast]
    exact holeSel_spec (L := L) (T := T) (m := m) hL (X := X) hpor hn
  · have hsel : holeSelZ hL X hpor n = fun _ => ⟨0, hL⟩ := by
      unfold holeSelZ; rw [dif_neg hn]
    rw [hsel]
    by_cases hnn : ∀ i : Fin d, 0 ≤ n i
    · have hcell : X ∩ gridBox L (m * T) (fun i => (n i).toNat) = ∅ :=
        Set.not_nonempty_iff_eq_empty.mp (fun h => hn ⟨hnn, h⟩)
      have hn_eq : n = fun i => ((n i).toNat : ℤ) := by
        funext i; exact (Int.toNat_of_nonneg (hnn i)).symm
      have hchild : childIndexZ L n (fun _ => ⟨0, hL⟩)
          = fun i => (childIndex L (fun i => (n i).toNat) (fun _ => ⟨0, hL⟩) i : ℤ) := by
        rw [hn_eq]
        exact childIndexZ_natCast L (fun i => (n i).toNat) (fun _ => ⟨0, hL⟩)
      rw [hchild, gridBoxZ_natCast, Set.eq_empty_iff_forall_notMem]
      intro x hx
      have hmem : x ∈ X ∩ gridBox L (m * T) (fun i => (n i).toNat) :=
        ⟨hx.1, gridBox_child_subset hL (n := m * T) (fun i => (n i).toNat)
          (fun _ => ⟨0, hL⟩) hx.2⟩
      rw [hcell] at hmem
      exact hmem
    · push Not at hnn
      obtain ⟨i, hi⟩ := hnn
      have hLpos : 0 < L := hL
      have hhspos : 0 < hss L (m * T) := hss_pos hLpos (m * T)
      have hLr : (1:ℝ) < L := by exact_mod_cast (by omega : 1 < L)
      rw [Set.eq_empty_iff_forall_notMem]
      intro x hx
      have hlt : x i < -1 := by
        have hx2 := hx.2
        rw [gridBoxZ, mem_box] at hx2
        have hyu := (hx2 i).2
        have hci : (childIndexZ L n (fun _ => ⟨0, hL⟩) i : ℝ) = (L:ℝ) * (n i : ℝ) := by
          simp only [childIndexZ]; push_cast; ring
        rw [hci] at hyu
        have hniZ : n i ≤ -1 := by omega
        have hni : (n i : ℝ) ≤ -1 := by exact_mod_cast hniZ
        have hexp : 2 * ((L:ℝ) * (n i : ℝ) + 1) * hss L (m * T + 1)
            = 2 * (n i : ℝ) * hss L (m * T) + 2 * hss L (m * T + 1) := by
          have hmul : (L:ℝ) * hss L (m * T + 1) = hss L (m * T) := by
            rw [hss_succ hLpos]; field_simp
          nlinarith [hmul]
        rw [hexp] at hyu
        have hinv : (L:ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hLr
        have hhs2 : hss L (m * T + 1) = hss L (m * T) * (L:ℝ)⁻¹ := by
          rw [hss_succ hLpos, div_eq_mul_inv]
        rw [hhs2] at hyu
        have hprod : 0 < hss L (m * T) * (L:ℝ)⁻¹ := by positivity
        nlinarith [hhspos, hni, hinv, hprod]
      have hXi := hX hx.1
      rw [mem_cube] at hXi
      linarith [(hXi i).1]

/-- The localisation set of the `m`-th step, corrected (Session 52): one cube of side `L^{-1}`
in **every** cell of the rescaled `L`-adic grid. -/
noncomputable def locSetZ (L T m : ℕ) (X : Set ℝᵈ) (j : (Fin d → ℤ) → Fin d → Fin L) :
    Set ℝᵈ :=
  ⋃ n : Fin d → ℤ, holeCube L T m n (j n)

lemma measurableSet_locSetZ (L T m : ℕ) (X : Set ℝᵈ) (j : (Fin d → ℤ) → Fin d → Fin L) :
    MeasurableSet (locSetZ L T m X j) := by
  rw [locSetZ]
  exact MeasurableSet.iUnion fun n => measurableSet_box _ _

/-- **The corrected localisation set is contained in the rescaled hole set.**  Every cube of
`locSetZ` is the rescaled half-cube of a missing child, hence a point of `resc ⋅ U_{mT+1}`. -/
theorem locSetZ_subset_smul_UstarZ {L T m : ℕ} (hL : 0 < L) {X : Set ℝᵈ}
    {j : (Fin d → ℤ) → Fin d → Fin L}
    (hj : ∀ n : Fin d → ℤ, X ∩ gridBoxZ L (m * T + 1) (childIndexZ L n (j n)) = ∅) :
    locSetZ L T m X j ⊆ rescaleFactor L T m • UstarZ L X (m * T) := by
  intro z hz
  rw [locSetZ, Set.mem_iUnion] at hz
  obtain ⟨n, hzn⟩ := hz
  rw [← holeCube_eq_smul_halfCubeZ hL T m n (j n)] at hzn
  obtain ⟨y, hy, hyz⟩ := Set.mem_smul_set.mp hzn
  exact Set.mem_smul_set.mpr ⟨y, ⟨childIndexZ L n (j n), hj n, hy⟩, hyz⟩

end Submission.FUP
