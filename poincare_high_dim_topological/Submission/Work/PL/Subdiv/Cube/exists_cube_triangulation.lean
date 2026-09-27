import Submission.Work.PL.Subdiv.Cube.Inter
import Submission.Work.PL.Subdiv.Cube.affineIndependent_unitVerts
import Submission.Work.PL.Subdiv.Cube.convexHull_unitVerts
import Submission.Work.PL.Subdiv.Cube.mem_unitVerts_iff
import Submission.Work.PL.Subdiv.Cube.exists_cx_of_maximal

/-!
# Mesh-`δ` triangulations of a cube (the Kuhn/Freudenthal grid)

The complex is the Kuhn (Freudenthal) triangulation of the grid `[0,m]^n` rescaled onto
`closedCube β` by the affine map `x ↦ (2β/m) x - β`.

* `phiPt`/`phiEquiv`: the rescaling.
* `cellVerts`/`pcellVerts`: the vertex set of a grid simplex, before and after the rescaling.
* `kuhnCx`: the resulting simplicial complex.
* `exists_cube_triangulation`: its existence for a sufficiently fine grid.
-/

open Set Metric
open scoped BigOperators
open PL

namespace Work.PL.Subdiv.Cube

noncomputable section

variable {n : ℕ}

/-! ### The affine rescaling `x ↦ (2β/m) x - β` -/

/-- The coordinate formula of the rescaling. -/
def phiPt (β : ℝ) (m : ℕ) (x : PL.E n) : PL.E n :=
  WithLp.toLp 2 (fun i => (2 * β / (m : ℝ)) * x i - β)

/-- The rescaling as an affine equivalence (for `β > 0`, `m > 0`). -/
noncomputable def phiEquiv (β : ℝ) (m : ℕ) (hβ : 0 < β) (hm : 0 < m) : PL.E n ≃ᵃ[ℝ] PL.E n :=
  (LinearEquiv.toAffineEquiv
      (LinearEquiv.smulOfNeZero ℝ (PL.E n) (2 * β / (m : ℝ)) (by positivity))).trans
    (AffineEquiv.constVAdd ℝ (PL.E n) (WithLp.toLp 2 (fun _ : Fin n => -β)))

lemma phiEquiv_apply (β : ℝ) (m : ℕ) (hβ : 0 < β) (hm : 0 < m) (x : PL.E n) :
    phiEquiv β m hβ hm x = phiPt β m x := by
  ext i
  simp only [phiEquiv, phiPt, AffineEquiv.trans_apply, LinearEquiv.coe_toAffineEquiv,
    LinearEquiv.smulOfNeZero_apply, AffineEquiv.constVAdd_apply, vadd_eq_add, WithLp.ofLp_add,
    WithLp.ofLp_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

lemma phiPt_sub (β : ℝ) (m : ℕ) (a b : PL.E n) :
    phiPt β m a - phiPt β m b = (2 * β / (m : ℝ)) • (a - b) := by
  ext i
  simp only [phiPt, WithLp.ofLp_sub, WithLp.ofLp_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-! ### The vertex sets of grid simplices and their rescalings -/

/-- The vertex set of the grid simplex of the cell `c` and the order `π`, rescaled onto
`closedCube β`. -/
def pcellVerts (β : ℝ) (m : ℕ) (c : Fin n → ℕ) (π : Equiv.Perm (Fin n)) : Finset (PL.E n) :=
  (cellVerts c π).image (phiPt β m)

lemma affineIndependent_cellVerts (c : Fin n → ℕ) (π : Equiv.Perm (Fin n)) :
    AffineIndependent ℝ ((↑) : ↥(cellVerts c π) → PL.E n) := by
  have hconst : (⇑(AffineEquiv.constVAdd ℝ (PL.E n) (cellPt c))) = (fun v => cellPt c + v) := by
    funext x; rw [AffineEquiv.constVAdd_apply, vadd_eq_add]
  have hcoe : (↑(cellVerts c π) : Set (PL.E n)) =
      (AffineEquiv.constVAdd ℝ (PL.E n) (cellPt c) : PL.E n → PL.E n) ''
        (↑(unitVerts π) : Set (PL.E n)) := by
    rw [hconst, cellVerts, Finset.coe_image]
  change AffineIndependent ℝ ((↑) : ↥(↑(cellVerts c π) : Set (PL.E n)) → PL.E n)
  rw [hcoe]
  exact (AffineEquiv.affineIndependent_set_of_eq_iff
    (AffineEquiv.constVAdd ℝ (PL.E n) (cellPt c))).mpr (affineIndependent_unitVerts n π)

lemma affineIndependent_pcellVerts (β : ℝ) (m : ℕ) (hβ : 0 < β) (hm : 0 < m)
    (c : Fin n → ℕ) (π : Equiv.Perm (Fin n)) :
    AffineIndependent ℝ ((↑) : ↥(pcellVerts β m c π) → PL.E n) := by
  have hcoe : (↑(pcellVerts β m c π) : Set (PL.E n)) =
      (phiEquiv β m hβ hm : PL.E n → PL.E n) '' (↑(cellVerts c π) : Set (PL.E n)) := by
    rw [pcellVerts, Finset.coe_image]
    congr 1
    funext x
    exact (phiEquiv_apply β m hβ hm x).symm
  change AffineIndependent ℝ ((↑) : ↥((↑(pcellVerts β m c π) : Set (PL.E n))) → PL.E n)
  rw [hcoe]
  exact (AffineEquiv.affineIndependent_set_of_eq_iff (phiEquiv β m hβ hm)).mpr
    (affineIndependent_cellVerts c π)

lemma convexHull_pcellVerts (β : ℝ) (m : ℕ) (hβ : 0 < β) (hm : 0 < m)
    (c : Fin n → ℕ) (π : Equiv.Perm (Fin n)) :
    convexHull ℝ ((pcellVerts β m c π) : Set (PL.E n)) =
      (phiEquiv β m hβ hm : PL.E n → PL.E n) ''
        convexHull ℝ ((cellVerts c π) : Set (PL.E n)) := by
  have hcoe : (↑(pcellVerts β m c π) : Set (PL.E n)) =
      (phiEquiv β m hβ hm : PL.E n → PL.E n) '' (↑(cellVerts c π) : Set (PL.E n)) := by
    rw [pcellVerts, Finset.coe_image]
    congr 1
    funext x
    exact (phiEquiv_apply β m hβ hm x).symm
  rw [hcoe]
  have := (phiEquiv β m hβ hm).toAffineMap.image_convexHull ((↑(cellVerts c π)) : Set (PL.E n))
  simpa using this.symm

/-- Pushing forward by the affine equivalence preserves the "glue nicely" condition. -/
lemma convexHull_inter_pcellVerts (β : ℝ) (m : ℕ) (hβ : 0 < β) (hm : 0 < m)
    (c c' : Fin n → ℕ) (π π' : Equiv.Perm (Fin n)) :
    convexHull ℝ ((pcellVerts β m c π ∩ pcellVerts β m c' π' : Finset (PL.E n)) :
        Set (PL.E n)) =
      convexHull ℝ (pcellVerts β m c π : Set (PL.E n)) ∩
      convexHull ℝ (pcellVerts β m c' π' : Set (PL.E n)) := by
  have hphi : ∀ (s : Set (PL.E n)),
      convexHull ℝ ((phiEquiv β m hβ hm : PL.E n → PL.E n) '' s) =
        (phiEquiv β m hβ hm : PL.E n → PL.E n) '' convexHull ℝ s := by
    intro s
    have := (phiEquiv β m hβ hm).toAffineMap.image_convexHull s
    simpa using this.symm
  have hA : (↑(pcellVerts β m c π) : Set (PL.E n)) =
      (phiEquiv β m hβ hm : PL.E n → PL.E n) '' (↑(cellVerts c π) : Set (PL.E n)) := by
    rw [pcellVerts, Finset.coe_image]; congr 1; funext x; exact (phiEquiv_apply β m hβ hm x).symm
  have hB : (↑(pcellVerts β m c' π') : Set (PL.E n)) =
      (phiEquiv β m hβ hm : PL.E n → PL.E n) '' (↑(cellVerts c' π') : Set (PL.E n)) := by
    rw [pcellVerts, Finset.coe_image]; congr 1; funext x; exact (phiEquiv_apply β m hβ hm x).symm
  have hAB : (↑(pcellVerts β m c π ∩ pcellVerts β m c' π') : Set (PL.E n)) =
      (phiEquiv β m hβ hm : PL.E n → PL.E n) ''
        (↑(cellVerts c π ∩ cellVerts c' π') : Set (PL.E n)) := by
    rw [Finset.coe_inter, hA, hB, ← Set.image_inter (phiEquiv β m hβ hm).injective,
      ← Finset.coe_inter]
  rw [hAB, hA, hB, hphi, hphi, hphi, ← Set.image_inter (phiEquiv β m hβ hm).injective,
    ← convexHull_inter_cellVerts]


/-! ### Metric bounds for grid simplices -/

/-- Vertices of one grid simplex are at distance at most `√n`. -/
lemma dist_cellVerts_le (c : Fin n → ℕ) (π : Equiv.Perm (Fin n)) {a b : PL.E n}
    (ha : a ∈ cellVerts c π) (hb : b ∈ cellVerts c π) : dist a b ≤ Real.sqrt n := by
  rw [cellVerts_eq] at ha hb
  obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hb
  have hsub : (cellPt c + wvec π k) - (cellPt c + wvec π j) = wvec π k - wvec π j := by abel
  rw [dist_eq_norm, hsub, EuclideanSpace.norm_eq]
  have hcard : (∑ _i : Fin n, (1 : ℝ)) = (n : ℝ) := by simp
  rw [← hcard]
  refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ => ?_)
  have h : ‖(wvec π k - wvec π j) i‖ ^ 2 ≤ 1 := by
    rw [WithLp.ofLp_sub, Pi.sub_apply, wvec_apply, wvec_apply, Real.norm_eq_abs, sq_abs]
    split <;> split <;> norm_num
  exact h

lemma dist_phiPt (β : ℝ) (m : ℕ) (hβ : 0 < β) (hm : 0 < m) (a b : PL.E n) :
    dist (phiPt β m a) (phiPt β m b) = (2 * β / (m : ℝ)) * dist a b := by
  have hpos : (0:ℝ) ≤ 2 * β / (m : ℝ) := by positivity
  rw [dist_eq_norm, phiPt_sub, norm_smul, Real.norm_of_nonneg hpos, dist_eq_norm]

/-! ### Every point of the grid cube lies in a grid simplex -/

/-- For any point `y` there is an order `π` along which `y` is non-decreasing. -/
lemma exists_perm_mono (y : PL.E n) :
    ∃ π : Equiv.Perm (Fin n), ∀ a b : Fin n, a ≤ b → y (π a) ≤ y (π b) :=
  ⟨Tuple.sort (fun i => y i), fun a b hab => Tuple.monotone_sort (fun i => y i) hab⟩

/-- The chosen grid cell of a point of `[0,m]^n`. -/
def cellOf (m : ℕ) (x : PL.E n) : Fin n → ℕ :=
  fun i => if x i = (m : ℝ) then m - 1 else Nat.floor (x i)

lemma cellOf_lt (m : ℕ) (hm : 0 < m) {x : PL.E n} (hx : ∀ i, 0 ≤ x i ∧ x i ≤ (m : ℝ)) :
    ∀ i, cellOf m x i < m := by
  intro i
  have hx1 := (hx i).1
  have hx2 := (hx i).2
  simp only [cellOf]
  by_cases h : x i = (m : ℝ)
  · rw [if_pos h]; omega
  · rw [if_neg h]
    have hfloor : (Nat.floor (x i) : ℝ) ≤ x i := Nat.floor_le hx1
    have hlt : x i < (m : ℝ) := lt_of_le_of_ne hx2 h
    by_contra hcon
    have : (m : ℝ) ≤ (Nat.floor (x i) : ℝ) := by exact_mod_cast Nat.le_of_not_lt hcon
    linarith

lemma cellOf_le (m : ℕ) {x : PL.E n} (hx : ∀ i, 0 ≤ x i ∧ x i ≤ (m : ℝ)) (i : Fin n) :
    (cellOf m x i : ℝ) ≤ x i := by
  have hx1 := (hx i).1
  have hx2 := (hx i).2
  simp only [cellOf]
  by_cases h : x i = (m : ℝ)
  · rw [if_pos h]
    have hle : ((m - 1 : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast Nat.sub_le m 1
    rw [h]; exact hle
  · rw [if_neg h]
    exact Nat.floor_le hx1

lemma le_cellOf_add_one (m : ℕ) (hm : 0 < m) {x : PL.E n}
    (hx : ∀ i, 0 ≤ x i ∧ x i ≤ (m : ℝ)) (i : Fin n) : x i ≤ (cellOf m x i : ℝ) + 1 := by
  have hx2 := (hx i).2
  simp only [cellOf]
  by_cases h : x i = (m : ℝ)
  · rw [if_pos h]
    have hcast : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
      rw [Nat.cast_sub (show 1 ≤ m by omega)]; norm_num
    rw [hcast, h]; linarith
  · rw [if_neg h]
    have := Nat.lt_floor_add_one (x i)
    linarith

/-- **Coverage.**  The unit Freudenthal simplices of all grid cells and orders cover the cube
`[0,m]^n`. -/
lemma iUnion_cover (m : ℕ) (hm : 0 < m) :
    (⋃ p : (Fin n → Fin m) × Equiv.Perm (Fin n),
        (fun y => cellPt (fun j => (p.1 j : ℕ)) + y) '' unitSimp p.2) =
      {x : PL.E n | ∀ i, 0 ≤ x i ∧ x i ≤ (m : ℝ)} := by
  refine Set.Subset.antisymm ?_ ?_
  · intro x hx
    rw [Set.mem_iUnion] at hx
    obtain ⟨p, hx⟩ := hx
    obtain ⟨y, hy, rfl⟩ := hx
    intro i
    have h1 := (hy.1 i).1
    have h2 := (hy.1 i).2
    have h3 : ((p.1 i : ℕ) : ℝ) + 1 ≤ (m : ℝ) := by
      have hlt := (p.1 i).isLt
      have : (p.1 i : ℕ) + 1 ≤ m := hlt
      exact_mod_cast this
    have h4 : (0:ℝ) ≤ (p.1 i : ℕ) := Nat.cast_nonneg _
    simp only [WithLp.ofLp_add, Pi.add_apply, cellPt_apply]
    constructor <;> linarith
  · intro x hx
    set c : Fin n → ℕ := cellOf m x with hc
    have hclt : ∀ i, c i < m := cellOf_lt m hm hx
    set y : PL.E n := x - cellPt c with hydef
    have hy0 : ∀ i, 0 ≤ y i ∧ y i ≤ 1 := by
      intro i
      have h1 : (c i : ℝ) ≤ x i := cellOf_le m hx i
      have h2 : x i ≤ (c i : ℝ) + 1 := le_cellOf_add_one m hm hx i
      have hyi : y i = x i - (c i : ℝ) := by
        rw [hydef, WithLp.ofLp_sub, Pi.sub_apply, cellPt_apply]
      rw [hyi]; constructor <;> linarith
    obtain ⟨π, hπ⟩ := exists_perm_mono y
    refine Set.mem_iUnion.mpr ⟨(fun i => ⟨c i, hclt i⟩, π), ?_⟩
    exact ⟨y, ⟨hy0, hπ⟩, by rw [hydef]; abel⟩

/-- The image of the grid cube `[0,m]^n` under the rescaling is `closedCube β`. -/
lemma phiEquiv_image_cube (β : ℝ) (m : ℕ) (hβ : 0 < β) (hm : 0 < m) :
    (phiEquiv β m hβ hm : PL.E n → PL.E n) ''
        {x : PL.E n | ∀ i, 0 ≤ x i ∧ x i ≤ (m : ℝ)} = closedCube (n := n) β := by
  have hm' : (0:ℝ) < m := by exact_mod_cast hm
  have hpos : (0:ℝ) < 2 * β / (m : ℝ) := by positivity
  have hfun : (phiEquiv β m hβ hm : PL.E n → PL.E n) = phiPt β m := by
    funext x; exact phiEquiv_apply β m hβ hm x
  rw [hfun]
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    intro i
    have h1 := (hx i).1
    have h2 := (hx i).2
    have hcoord : phiPt β m x i = (2 * β / (m : ℝ)) * x i - β := by
      simp only [phiPt, WithLp.ofLp_toLp]
    rw [hcoord, abs_le]
    constructor
    · nlinarith [h1, hpos]
    · have hmul : 2 * β / (m : ℝ) * x i ≤ 2 * β / (m : ℝ) * (m : ℝ) :=
        mul_le_mul_of_nonneg_left h2 (le_of_lt hpos)
      have hmul2 : 2 * β / (m : ℝ) * (m : ℝ) = 2 * β := by field_simp
      linarith
  · intro hy
    refine ⟨WithLp.toLp 2 (fun i => (y i + β) * (m : ℝ) / (2 * β)), ?_, ?_⟩
    · intro i
      have hyi : |y i| ≤ β := hy i
      rw [abs_le] at hyi
      have h1' : 0 ≤ y i + β := by linarith [hyi.1]
      have h2' : y i + β ≤ 2 * β := by linarith [hyi.2]
      simp only [WithLp.ofLp_toLp]
      have hm0 : (0:ℝ) ≤ m := Nat.cast_nonneg m
      constructor
      · exact div_nonneg (mul_nonneg h1' hm0) (by positivity)
      · rw [div_le_iff₀ (by positivity : (0:ℝ) < 2 * β)]
        nlinarith [h2', hm0, hβ]
    · ext i
      simp only [phiPt, WithLp.ofLp_toLp]
      field_simp
      ring

/-! ### The Kuhn complex of the grid -/

/-- The vertex set of the grid simplex indexed by `p`. -/
def kuhnV (β : ℝ) (m : ℕ) : (Fin n → Fin m) × Equiv.Perm (Fin n) → Finset (PL.E n) :=
  fun p => pcellVerts β m (fun j => (p.1 j : ℕ)) p.2

lemma kuhnV_affineIndependent (β : ℝ) (m : ℕ) (hβ : 0 < β) (hm : 0 < m)
    (i : (Fin n → Fin m) × Equiv.Perm (Fin n)) :
    AffineIndependent ℝ ((↑) : ↥(kuhnV β m i) → PL.E n) :=
  affineIndependent_pcellVerts β m hβ hm _ _

lemma kuhnV_hinter (β : ℝ) (m : ℕ) (hβ : 0 < β) (hm : 0 < m)
    (i j : (Fin n → Fin m) × Equiv.Perm (Fin n)) :
    convexHull ℝ ((kuhnV β m i ∩ kuhnV β m j : Finset (PL.E n)) : Set (PL.E n)) =
      convexHull ℝ (kuhnV β m i : Set (PL.E n)) ∩
      convexHull ℝ (kuhnV β m j : Set (PL.E n)) :=
  convexHull_inter_pcellVerts β m hβ hm _ _ _ _

/-- The Kuhn (Freudenthal) triangulation of the grid `[0,m]^n`, rescaled onto `closedCube β`. -/
noncomputable def kuhnCx (β : ℝ) (m : ℕ) (hβ : 0 < β) (hm : 0 < m) : PL.Cx n :=
  Classical.choose (exists_cx_of_maximal (kuhnV β m) (kuhnV_affineIndependent β m hβ hm)
    (kuhnV_hinter β m hβ hm))

lemma kuhnCx_faces (β : ℝ) (m : ℕ) (hβ : 0 < β) (hm : 0 < m) :
    (kuhnCx (n := n) β m hβ hm).faces =
      {s : Finset (PL.E n) | s.Nonempty ∧ ∃ i, s ⊆ kuhnV β m i} := by
  unfold kuhnCx
  exact Classical.choose_spec (exists_cx_of_maximal (kuhnV β m)
    (kuhnV_affineIndependent β m hβ hm) (kuhnV_hinter β m hβ hm))

lemma kuhnV_nonempty (β : ℝ) (m : ℕ) (i : (Fin n → Fin m) × Equiv.Perm (Fin n)) :
    (kuhnV β m i).Nonempty := by
  refine ⟨phiPt β m (cellPt (fun j => (i.1 j : ℕ)) + wvec i.2 0), ?_⟩
  rw [kuhnV, pcellVerts]
  exact Finset.mem_image.mpr ⟨_, mem_cellVerts (Nat.zero_le n), rfl⟩

lemma kuhnCx_finite (β : ℝ) (m : ℕ) (hβ : 0 < β) (hm : 0 < m) :
    (kuhnCx (n := n) β m hβ hm).faces.Finite := by
  rw [kuhnCx_faces]
  refine Set.Finite.subset
    (Finset.finite_toSet ((Finset.univ : Finset ((Fin n → Fin m) × Equiv.Perm (Fin n))).biUnion
      (fun i => (kuhnV β m i).powerset))) ?_
  rintro s ⟨-, i, hsi⟩
  exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, Finset.mem_powerset.mpr hsi⟩

lemma kuhnCx_space (β : ℝ) (m : ℕ) (hβ : 0 < β) (hm : 0 < m) :
    (kuhnCx (n := n) β m hβ hm).space = closedCube (n := n) β := by
  have hspace : (kuhnCx (n := n) β m hβ hm).space =
      ⋃ i : (Fin n → Fin m) × Equiv.Perm (Fin n),
        convexHull ℝ ((kuhnV β m i) : Set (PL.E n)) := by
    refine Set.Subset.antisymm ?_ ?_
    · intro z hz
      rw [Geometry.SimplicialComplex.mem_space_iff] at hz
      obtain ⟨s, hs, hzs⟩ := hz
      rw [kuhnCx_faces] at hs
      obtain ⟨-, i, hsi⟩ := hs
      exact Set.mem_iUnion.mpr ⟨i, convexHull_mono (by simpa using hsi) hzs⟩
    · intro z hz
      rw [Geometry.SimplicialComplex.mem_space_iff]
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hz
      exact ⟨kuhnV β m i, by rw [kuhnCx_faces]; exact ⟨kuhnV_nonempty β m i, i, subset_rfl⟩, hi⟩
  have hcov : (⋃ i : (Fin n → Fin m) × Equiv.Perm (Fin n),
        convexHull ℝ ((kuhnV β m i) : Set (PL.E n))) =
      (phiEquiv β m hβ hm : PL.E n → PL.E n) ''
        {x : PL.E n | ∀ i, 0 ≤ x i ∧ x i ≤ (m : ℝ)} := by
    rw [← iUnion_cover (n := n) m hm, Set.image_iUnion]
    refine iUnion_congr (fun i => ?_)
    obtain ⟨p, π⟩ := i
    rw [kuhnV, convexHull_pcellVerts β m hβ hm (fun j => (p j : ℕ)) π, convexHull_cellVerts]
  rw [hspace, hcov, phiEquiv_image_cube]

lemma kuhnCx_meshLT (β : ℝ) (m : ℕ) (hβ : 0 < β) (hm : 0 < m) (δ : ℝ)
    (hmesh : 2 * β * Real.sqrt (n : ℝ) < (m : ℝ) * δ) : PL.MeshLT (kuhnCx (n := n) β m hβ hm) δ := by
  intro s hs x hx y hy
  rw [kuhnCx_faces] at hs
  obtain ⟨-, i, hsi⟩ := hs
  obtain ⟨p, π⟩ := i
  rw [kuhnV, pcellVerts] at hsi
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp (hsi hx)
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp (hsi hy)
  have hm' : (0:ℝ) < m := by exact_mod_cast hm
  rw [dist_phiPt β m hβ hm]
  have h1 : dist a b ≤ Real.sqrt n := dist_cellVerts_le _ π ha hb
  have h2 : 2 * β / (m : ℝ) * dist a b ≤ 2 * β / (m : ℝ) * Real.sqrt n :=
    mul_le_mul_of_nonneg_left h1 (by positivity)
  have h3 : 2 * β / (m : ℝ) * Real.sqrt n < δ := by
    have heq : 2 * β / (m : ℝ) * Real.sqrt n = 2 * β * Real.sqrt n / (m : ℝ) := by ring
    rw [heq, div_lt_iff₀ hm']
    linarith
  linarith

/-- **A mesh-`δ` triangulation of the cube `closedCube β`.** -/
theorem exists_cube_triangulation (n : ℕ) (β δ : ℝ) (hβ : 0 < β) (hδ : 0 < δ) :
    ∃ P : PL.Cx n, P.faces.Finite ∧ P.space = PL.closedCube (n := n) β ∧ PL.MeshLT P δ := by
  set m : ℕ := Nat.floor (2 * β * Real.sqrt (n : ℝ) / δ) + 1 with hmdef
  have hm : 0 < m := Nat.succ_pos _
  have hmesh : 2 * β * Real.sqrt (n : ℝ) < (m : ℝ) * δ := by
    have h1 : 2 * β * Real.sqrt (n : ℝ) / δ < (m : ℝ) := by
      rw [hmdef]
      push_cast
      exact Nat.lt_floor_add_one _
    rwa [div_lt_iff₀ hδ] at h1
  exact ⟨kuhnCx (n := n) β m hβ hm, kuhnCx_finite (n := n) β m hβ hm, kuhnCx_space (n := n) β m hβ hm,
    kuhnCx_meshLT (n := n) β m hβ hm δ hmesh⟩

end

end Work.PL.Subdiv.Cube