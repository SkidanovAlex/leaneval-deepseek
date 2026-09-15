import Submission.FUP.HSSets

open FractalUncertainty MeasureTheory FourierTransform Metric Filter Set Pointwise
open scoped ENNReal BigOperators Topology ContDiff

set_option autoImplicit false
variable {d : ℕ}
local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)

/-!
# Han–Schlag's §5, step 3: the rescaled holes of the induction on scales

This module contains the *geometric* layer of the induction on scales of Han–Schlag's §5
(`Submission/FUP/ROADMAP.md`, Session 49): the holes `U_{mT+1}` of
`Submission/FUP/HSSets.lean`, rescaled by the factor `L^{mT}` of the `m`-th step, are a union of
one cube of side `L^{-1}` per cell of the rescaled `L`-adic grid meeting `X` — i.e. they are a
localisation set of the shape required by `Submission.FUP.LocalizationStatement`.

Contents:

* `rescaleFactor L T m = L^{mT}`, with `rescaleFactor * hss L (mT) = 1`;
* `smul_box`, `smul_gridBox`, `smul_halfCube` — how a positive dilation acts on the boxes of the
  `L`-adic grid;
* `smul_gridBox_rescale` — the rescaled depth-`(mT)` cells are the cells `box (2k - L^{mT})
  (2k + 2 - L^{mT})` of the (`-L^{mT}`-shifted) `2ℤ`-grid;
* `holeLower`, `holeCube` — the rescaled concentric half-cube of a child, as a cube of side
  `L^{-1}`;
* `holeLower_constraint` — each of these cubes sits inside its cell, as required by
  `LocalizationStatement`;
* `holeChoice` / `locSet` — the union of one such cube per active cell, and its inclusion into
  the rescaled hole set `rescaleFactor L T m • Ustar L X (mT)`.
-/

namespace Submission.FUP

/-- The rescaling factor `L^{mT}` of the `m`-th step of the induction on scales. -/
noncomputable def rescaleFactor (L T m : ℕ) : ℝ := (L : ℝ) ^ (m * T)

lemma rescaleFactor_pos {L : ℕ} (hL : 0 < L) (T m : ℕ) : 0 < rescaleFactor L T m :=
  pow_pos (by exact_mod_cast hL) _

lemma rescaleFactor_ne_zero {L : ℕ} (hL : 0 < L) (T m : ℕ) : rescaleFactor L T m ≠ 0 :=
  ne_of_gt (rescaleFactor_pos hL T m)

lemma rescaleFactor_mul_hss {L : ℕ} (hL : 0 < L) (T m : ℕ) :
    rescaleFactor L T m * hss L (m * T) = 1 := by
  rw [rescaleFactor, hss, mul_inv_cancel₀ (pow_ne_zero _ (Nat.cast_ne_zero.mpr hL.ne'))]

lemma rescaleFactor_mul_hss_succ {L : ℕ} (hL : 0 < L) (T m : ℕ) :
    rescaleFactor L T m * hss L (m * T + 1) = (L : ℝ)⁻¹ := by
  have hLr : (L : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hL.ne'
  rw [rescaleFactor, hss, pow_succ, mul_inv]
  field_simp

/-- The side length of the rescaled holes: `L^{-1} = 2c₁` with `c₁ = (2L)^{-1}`. -/
noncomputable def locSide (L : ℕ) : ℝ := (L : ℝ)⁻¹

lemma two_mul_half_locSide (L : ℕ) : 2 * (2 * (L : ℝ))⁻¹ = locSide L := by
  rw [locSide, mul_inv]; ring

/-- The damping parameter of the localisation statement: with the half-side `c₁ = (2L)^{-1}` of
the localisation squares, the statement asks for the damping function at band radius `c₁/2`. -/
lemma two_mul_inv_div_two (L : ℕ) : (2 * (L : ℝ))⁻¹ / 2 = (4 * (L : ℝ))⁻¹ := by
  have h : (2 * (L : ℝ)) * 2 = 4 * (L : ℝ) := by ring
  rw [div_eq_mul_inv, ← mul_inv, h]

lemma locSide_pos {L : ℕ} (hL : 0 < L) : 0 < locSide L := by
  rw [locSide]; positivity

/-! ## Dilating the boxes of the `L`-adic grid -/

lemma smul_box {s : ℝ} (hs : 0 < s) (a b : Fin d → ℝ) :
    s • box a b = box (fun i => s * a i) (fun i => s * b i) := by
  ext x
  rw [Set.mem_smul_set]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [mem_box] at hy ⊢
    exact fun i => ⟨mul_le_mul_of_nonneg_left (hy i).1 hs.le,
      mul_le_mul_of_nonneg_left (hy i).2 hs.le⟩
  · intro hx
    rw [mem_box] at hx
    refine ⟨s⁻¹ • x, ?_, by rw [smul_inv_smul₀ hs.ne']⟩
    rw [mem_box]
    intro i
    refine ⟨?_, ?_⟩
    · rw [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, le_inv_mul_iff₀ hs]
      exact (hx i).1
    · rw [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, inv_mul_le_iff₀ hs]
      exact (hx i).2

lemma smul_gridBox {L n : ℕ} (k : Fin d → ℕ) {s : ℝ} (hs : 0 < s) :
    s • gridBox L n k
      = box (fun i => s * (-1 + 2 * (k i : ℝ) * hss L n))
            (fun i => s * (-1 + 2 * ((k i : ℝ) + 1) * hss L n)) := by
  rw [gridBox, smul_box hs]

lemma smul_halfCube {L n : ℕ} (k : Fin d → ℕ) {s : ℝ} (hs : 0 < s) :
    s • halfCube L n k
      = box (fun i => s * (-1 + 2 * (k i : ℝ) * hss L n + hss L n / 2))
            (fun i => s * (-1 + 2 * ((k i : ℝ) + 1) * hss L n - hss L n / 2)) := by
  rw [halfCube, smul_box hs]

/-- **The rescaled depth-`(mT)` cells** are the cells of the `(-L^{mT})`-shifted `2ℤ`-grid. -/
lemma smul_gridBox_rescale {L : ℕ} (hL : 0 < L) (T m : ℕ) (k : Fin d → ℕ) :
    rescaleFactor L T m • gridBox L (m * T) k
      = box (fun i => 2 * (k i : ℝ) + (-rescaleFactor L T m))
            (fun i => 2 * (k i : ℝ) + (-rescaleFactor L T m) + 2) := by
  rw [smul_gridBox k (rescaleFactor_pos hL T m)]
  have h : rescaleFactor L T m * hss L (m * T) = 1 := rescaleFactor_mul_hss hL T m
  congr 1
  · funext i; nlinarith [h]
  · funext i; nlinarith [h]

/-! ## The rescaled concentric half-cubes of the missing children -/

/-- The lower corner of the rescaled concentric half-cube of the child of the cell `k` with
offset `j`: the rescaled half-cube `L^{mT} • halfCube L (mT+1) (childIndex L k j)` is
`box (holeLower L T m k j) (holeLower L T m k j + L^{-1})`. -/
noncomputable def holeLower (L T m : ℕ) (k : Fin d → ℤ) (j : Fin d → Fin L) : Fin d → ℝ :=
  fun i => 2 * (k i : ℝ) + (-rescaleFactor L T m) + (2 * (j i : ℝ) + 1 / 2) / (L : ℝ)

/-- The rescaled hole of the induction: a cube of side `L^{-1} = 2c₁` with `c₁ = (2L)^{-1}`. -/
noncomputable def holeCube (L T m : ℕ) (k : Fin d → ℤ) (j : Fin d → Fin L) : Set ℝᵈ :=
  box (holeLower L T m k j) (fun i => holeLower L T m k j i + locSide L)

lemma holeCube_eq_smul_halfCube {L : ℕ} (hL : 0 < L) (T m : ℕ) (k : Fin d → ℕ)
    (j : Fin d → Fin L) :
    rescaleFactor L T m • halfCube L (m * T + 1) (childIndex L k j)
      = holeCube L T m (fun i => (k i : ℤ)) j := by
  rw [smul_halfCube (childIndex L k j) (rescaleFactor_pos hL T m), holeCube]
  have h : rescaleFactor L T m * hss L (m * T + 1) = (L : ℝ)⁻¹ :=
    rescaleFactor_mul_hss_succ hL T m
  have hstep : ∀ i : Fin d,
      rescaleFactor L T m *
          (-1 + 2 * ((childIndex L k j i : ℕ) : ℝ) * hss L (m * T + 1)
            + hss L (m * T + 1) / 2)
        = holeLower L T m (fun i => (k i : ℤ)) j i := by
    intro i
    have hc : ((childIndex L k j i : ℕ) : ℝ) = (L:ℝ) * (k i : ℝ) + (j i : ℝ) := by
      rw [childIndex]; push_cast; ring
    rw [hc, holeLower]
    simp only [Int.cast_natCast]
    have hexp : rescaleFactor L T m *
          (-1 + 2 * ((L:ℝ) * (k i : ℝ) + (j i : ℝ)) * hss L (m * T + 1)
            + hss L (m * T + 1) / 2)
        = -rescaleFactor L T m
          + 2 * ((L:ℝ) * (k i : ℝ) + (j i : ℝ))
              * (rescaleFactor L T m * hss L (m * T + 1))
          + (rescaleFactor L T m * hss L (m * T + 1)) / 2 := by ring
    rw [hexp, h]
    field_simp
    ring
  have hstep' : ∀ i : Fin d,
      rescaleFactor L T m *
          (-1 + 2 * (((childIndex L k j i : ℕ) : ℝ) + 1) * hss L (m * T + 1)
            - hss L (m * T + 1) / 2)
        = holeLower L T m (fun i => (k i : ℤ)) j i + locSide L := by
    intro i
    have hc : ((childIndex L k j i : ℕ) : ℝ) = (L:ℝ) * (k i : ℝ) + (j i : ℝ) := by
      rw [childIndex]; push_cast; ring
    rw [hc, holeLower, locSide]
    simp only [Int.cast_natCast]
    have hexp : rescaleFactor L T m *
          (-1 + 2 * (((L:ℝ) * (k i : ℝ) + (j i : ℝ)) + 1) * hss L (m * T + 1)
            - hss L (m * T + 1) / 2)
        = -rescaleFactor L T m
          + 2 * (((L:ℝ) * (k i : ℝ) + (j i : ℝ)) + 1)
              * (rescaleFactor L T m * hss L (m * T + 1))
          - (rescaleFactor L T m * hss L (m * T + 1)) / 2 := by ring
    rw [hexp, h]
    field_simp
    ring
  congr 1
  · funext i; exact hstep i
  · funext i; exact hstep' i

/-- Each rescaled hole is a cube of side `2c₁` (`c₁ = (2L)^{-1}`) inside the cell
`box (2k + γ) (2k + γ + 2)` of the shifted `2ℤ`-grid, as required by `LocalizationStatement`. -/
lemma holeLower_constraint {L : ℕ} (hL : 0 < L) (T m : ℕ) (k : Fin d → ℤ)
    (j : Fin d → Fin L) (i : Fin d) :
    2 * (k i : ℝ) + (-rescaleFactor L T m) ≤ holeLower L T m k j i ∧
      holeLower L T m k j i + 2 * (2 * (L : ℝ))⁻¹
        ≤ 2 * (k i : ℝ) + (-rescaleFactor L T m) + 2 := by
  have hLr : (0:ℝ) < L := by exact_mod_cast hL
  have hj : (j i : ℝ) + 1 ≤ (L : ℝ) := by
    have h := (j i).isLt
    exact_mod_cast Nat.succ_le_of_lt h
  constructor
  · have hnn : 0 ≤ (2 * (j i : ℝ) + 1 / 2) / (L : ℝ) :=
      div_nonneg (by positivity) hLr.le
    rw [holeLower]; linarith
  · have h2 : 2 * (2 * (L : ℝ))⁻¹ = locSide L := two_mul_half_locSide L
    rw [h2]
    have hkey : (2 * (j i : ℝ) + 1 / 2) / (L : ℝ) + (L : ℝ)⁻¹ ≤ 2 := by
      rw [inv_eq_one_div, ← add_div]
      rw [div_le_iff₀ hLr]
      linarith
    rw [holeLower, locSide]
    linarith [hkey]

/-! ## The localisation set of the `m`-th step -/

/-- The active cells of the `m`-th step: the depth-`(mT)` cells of the `L`-adic grid meeting `X`,
indexed (for `LocalizationStatement`) by nonnegative integer vectors. -/
def activeCells (L T m : ℕ) (X : Set ℝᵈ) : Set (Fin d → ℤ) :=
  {n | (∀ i : Fin d, 0 ≤ n i) ∧ (X ∩ gridBox L (m * T) (fun i => (n i).toNat)).Nonempty}

/-- The lower corners of the chosen holes: one missing child per active cell. -/
noncomputable def holeChoice (L T m : ℕ) (j : (Fin d → ℤ) → Fin d → Fin L) :
    (Fin d → ℤ) → (Fin d → ℝ) :=
  fun n => holeLower L T m n (j n)

/-- The localisation set of the `m`-th step of the induction: one cube of side `L^{-1}` per
active cell. -/
noncomputable def locSet (L T m : ℕ) (X : Set ℝᵈ) (j : (Fin d → ℤ) → Fin d → Fin L) : Set ℝᵈ :=
  ⋃ n ∈ activeCells L T m X,
    box (holeChoice L T m j n) (fun i => holeChoice L T m j n i + locSide L)

/-- **The localisation set is contained in the rescaled hole set.**  If for each active cell `n`
the child `j n` misses `X`, then the corresponding cube lies in `L^{mT} • U_{mT+1}` — the set on
which the cut-off `Ψ_{mT}` is small. -/
theorem locSet_subset_smul_Ustar {L : ℕ} (hL : 0 < L) {T m : ℕ} {X : Set ℝᵈ}
    {j : (Fin d → ℤ) → Fin d → Fin L}
    (hj : ∀ n ∈ activeCells L T m X,
      X ∩ gridBox L (m * T + 1) (childIndex L (fun i => (n i).toNat) (j n)) = ∅) :
    locSet L T m X j ⊆ rescaleFactor L T m • Ustar L X (m * T) := by
  intro z hz
  rw [locSet, Set.mem_iUnion] at hz
  obtain ⟨n, hz2⟩ := hz
  rw [Set.mem_iUnion] at hz2
  obtain ⟨hnS, hzn⟩ := hz2
  simp only [activeCells, Set.mem_ofPred_eq] at hnS
  obtain ⟨hnn, hnact⟩ := hnS
  have hmem : z ∈ holeCube L T m n (j n) := hzn
  have hlow : holeLower L T m n (j n) = holeLower L T m (fun i => (n i).toNat) (j n) := by
    funext i
    unfold holeLower
    simp only [Int.toNat_of_nonneg (hnn i)]
  have hk : holeCube L T m n (j n)
      = holeCube L T m (fun i => (n i).toNat) (j n) := by
    unfold holeCube
    rw [hlow]
  rw [hk, ← holeCube_eq_smul_halfCube (L := L) hL T m (fun i => (n i).toNat) (j n)] at hmem
  obtain ⟨y, hy, hyz⟩ := Set.mem_smul_set.mp hmem
  refine Set.mem_smul_set.mpr ⟨y, ?_, hyz⟩
  exact mem_Ustar.mpr ⟨fun i => (n i).toNat, hnact, j n,
    hj n (show n ∈ activeCells L T m X from ⟨hnn, hnact⟩), hy⟩

end Submission.FUP
