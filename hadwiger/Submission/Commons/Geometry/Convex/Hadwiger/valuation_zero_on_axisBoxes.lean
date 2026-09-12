import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Commons.Geometry.Convex.Hadwiger.dissection_additivity

open Set
open scoped BigOperators

namespace Commons.Geometry.Convex.Hadwiger

noncomputable section

abbrev EucV (n : ℕ) := EuclideanSpace ℝ (Fin n)
abbrev EucE (n : ℕ) : EucV n ≃L[ℝ] (Fin n → ℝ) := EuclideanSpace.equiv (Fin n) ℝ

def boxSet (n : ℕ) (l u : Fin n → ℝ) : Set (EucV n) :=
  {x : EucV n | ∀ i : Fin n, x i ∈ Set.Icc (l i) (u i)}

def vecOfFun (n : ℕ) (f : Fin n → ℝ) : EucV n := (EucE n).symm f

@[simp] theorem vecOfFun_apply (n : ℕ) (f : Fin n → ℝ) (i : Fin n) : (vecOfFun n f) i = f i := by
  simp [vecOfFun]

def basisVec (n : ℕ) (i : Fin n) : EucV n := PiLp.single 2 i (1 : ℝ)

@[simp] theorem basisVec_apply (n : ℕ) (i j : Fin n) : (basisVec n i) j = if j = i then (1 : ℝ) else 0 := by
  simp [basisVec]

@[simp] theorem norm_basisVec (n : ℕ) (i : Fin n) : ‖basisVec n i‖ = 1 := by
  simp [basisVec]

theorem boxSet_eq_image (n : ℕ) (l u : Fin n → ℝ) :
    boxSet n l u = (EucE n).symm '' (Set.pi Set.univ (fun i : Fin n => Set.Icc (l i) (u i))) := by
  ext x
  constructor
  · intro hx
    refine ⟨EucE n x, ?_, ?_⟩
    · intro i hi
      simpa using hx i
    · simp [EucE]
  · rintro ⟨f, hf, rfl⟩
    intro i
    simpa using hf i (Set.mem_univ i)

theorem mem_boxSet_iff (n : ℕ) (l u : Fin n → ℝ) (x : EucV n) :
    x ∈ boxSet n l u ↔ ∀ i : Fin n, l i ≤ x i ∧ x i ≤ u i := by
  simp [boxSet, Set.mem_Icc]

theorem boxSet_translate (n : ℕ) (l u : Fin n → ℝ) :
    boxSet n l u = (fun x : EucV n => x + vecOfFun n l) '' boxSet n 0 (u - l) := by
  ext x
  constructor
  · intro hx
    refine ⟨x - vecOfFun n l, ?_, ?_⟩
    · rw [mem_boxSet_iff] at hx ⊢
      intro i
      have hlo : l i ≤ x i := (hx i).1
      have hhi : x i ≤ u i := (hx i).2
      constructor
      · have : (x - vecOfFun n l) i = x i - l i := by simp
        rw [this]
        change (0 : ℝ) ≤ x i - l i
        linarith
      · have : (x - vecOfFun n l) i = x i - l i := by simp
        rw [this]
        change x i - l i ≤ u i - l i
        linarith
    · ext i <;> simp
  · rintro ⟨y, hy, rfl⟩
    rw [mem_boxSet_iff] at hy ⊢
    intro i
    have h1 : (0 : ℝ) ≤ y i := by simpa using (hy i).1
    have h2 : y i ≤ u i - l i := by simpa using (hy i).2
    constructor
    · have : (y + vecOfFun n l) i = y i + l i := by simp
      rw [this]
      change l i ≤ y i + l i
      linarith
    · have : (y + vecOfFun n l) i = y i + l i := by simp
      rw [this]
      change y i + l i ≤ u i
      linarith

theorem boxSet_translate_origin (n : ℕ) (l u : Fin n → ℝ) :
    boxSet n 0 (u - l) = (fun x : EucV n => x + (-vecOfFun n l)) '' boxSet n l u := by
  ext x
  constructor
  · intro hx
    refine ⟨x + vecOfFun n l, ?_, ?_⟩
    · rw [mem_boxSet_iff] at hx ⊢
      intro i
      have h1 : (0 : ℝ) ≤ x i := by simpa using (hx i).1
      have h2 : x i ≤ u i - l i := by simpa using (hx i).2
      constructor
      · have : (x + vecOfFun n l) i = x i + l i := by simp
        rw [this]
        change l i ≤ x i + l i
        linarith
      · have : (x + vecOfFun n l) i = x i + l i := by simp
        rw [this]
        change x i + l i ≤ u i
        linarith
    · ext i
      simp [PiLp.add_apply, PiLp.neg_apply]
  · rintro ⟨y, hy, rfl⟩
    rw [mem_boxSet_iff] at hy ⊢
    intro i
    have hlo : l i ≤ y i := (hy i).1
    have hhi : y i ≤ u i := (hy i).2
    constructor
    · have : (y + (-vecOfFun n l)) i = y i + (-l i) := by
        simp [PiLp.add_apply, PiLp.neg_apply]
      rw [this]
      change (0 : ℝ) ≤ y i + -l i
      linarith
    · have : (y + (-vecOfFun n l)) i = y i + (-l i) := by
        simp [PiLp.add_apply, PiLp.neg_apply]
      rw [this]
      change y i + -l i ≤ u i - l i
      linarith

theorem convex_boxSet (n : ℕ) (l u : Fin n → ℝ) : Convex ℝ (boxSet n l u) := by
  rw [boxSet_eq_image]
  exact Convex.linear_image (convex_pi (fun i hi => convex_Icc (l i) (u i)))
    ((EucE n).symm : (Fin n → ℝ) →ₗ[ℝ] EucV n)

theorem isCompact_boxSet (n : ℕ) (l u : Fin n → ℝ) : IsCompact (boxSet n l u) := by
  rw [boxSet_eq_image]
  exact (isCompact_univ_pi (fun i => isCompact_Icc)).image
    (by fun_prop : Continuous ((EucE n).symm : (Fin n → ℝ) → EucV n))

theorem boxSet_nonempty_of_le (n : ℕ) {l u : Fin n → ℝ} (hlu : ∀ i, l i ≤ u i) :
    (boxSet n l u).Nonempty := by
  refine ⟨vecOfFun n l, ?_⟩
  rw [mem_boxSet_iff]
  intro i
  exact ⟨le_rfl, hlu i⟩

noncomputable def coordBody (n : ℕ) (l u : Fin n → ℝ) (hlu : ∀ i, l i ≤ u i) :
    ConvexBody (EucV n) :=
  ⟨boxSet n l u, convex_boxSet n l u, isCompact_boxSet n l u, boxSet_nonempty_of_le n hlu⟩

@[simp] theorem coe_coordBody (n : ℕ) (l u : Fin n → ℝ) (hlu : ∀ i, l i ≤ u i) :
    ((coordBody n l u hlu : ConvexBody (EucV n)) : Set (EucV n)) = boxSet n l u :=
  rfl

theorem coordBody_translate_set (n : ℕ) (l u : Fin n → ℝ) (hlu : ∀ i, l i ≤ u i)
    (h0 : ∀ i, (0 : ℝ) ≤ u i - l i) :
    ((coordBody n 0 (u - l) h0 : ConvexBody (EucV n)) : Set (EucV n)) =
      (fun x : EucV n => x + (-vecOfFun n l)) '' (coordBody n l u hlu : Set (EucV n)) := by
  rw [coe_coordBody, coe_coordBody]
  exact boxSet_translate_origin n l u

theorem interior_coord_eq_empty (n : ℕ) (i : Fin n) (c : ℝ) :
    interior ({x : EucV n | x i = c} : Set (EucV n)) = ∅ := by
  apply subset_empty_iff.mp
  intro x hx
  have hxH : x i = c := by
    have hxmem : x ∈ ({x : EucV n | x i = c} : Set (EucV n)) := interior_subset hx
    exact hxmem
  rcases (Metric.isOpen_iff.mp isOpen_interior x) hx with ⟨ε, hε, hball⟩
  let δ := ε / 2
  have hδ : 0 < δ := half_pos hε
  let y : EucV n := x + δ • basisVec n i
  have hdy : dist y x < ε := by
    rw [dist_eq_norm]
    have hyx : y - x = δ • basisVec n i := by
      simp [y]
    calc
      ‖y - x‖ = ‖δ • basisVec n i‖ := by rw [hyx]
      _ = δ := by
        rw [norm_smul, norm_basisVec, mul_one]
        exact abs_of_nonneg hδ.le
      _ < ε := by dsimp [δ]; linarith
  have hyball : y ∈ Metric.ball x ε := Metric.mem_ball.mpr hdy
  have hyH : y ∈ ({x : EucV n | x i = c} : Set (EucV n)) := interior_subset (hball hyball)
  have hyi : y i = x i + δ := by
    simp [y, PiLp.add_apply, PiLp.smul_apply]
  have : c = c + δ := by
    calc
      c = y i := hyH.symm
      _ = x i + δ := hyi
      _ = c + δ := by rw [hxH]
  have hδ0 : δ = 0 := by linarith
  exact (ne_of_gt hδ) hδ0

theorem interior_box_inter_empty (n : ℕ) {l u l' u' : Fin n → ℝ} (i₀ : Fin n)
    (h : u i₀ ≤ l' i₀) :
    interior (((boxSet n l u : Set (EucV n)) ∩ (boxSet n l' u') : Set (EucV n))) = ∅ := by
  apply subset_empty_iff.mp
  have hsub : (boxSet n l u : Set (EucV n)) ∩ boxSet n l' u' ⊆
      ({x : EucV n | x i₀ = u i₀} : Set (EucV n)) := by
    intro x hx
    have hx1 := (mem_boxSet_iff n l u x).mp hx.1 i₀
    have hx2 := (mem_boxSet_iff n l' u' x).mp hx.2 i₀
    exact le_antisymm hx1.2 (le_trans h hx2.1)
  have hinter : interior (((boxSet n l u : Set (EucV n)) ∩ (boxSet n l' u')) : Set (EucV n)) ⊆
      interior ({x : EucV n | x i₀ = u i₀} : Set (EucV n)) := interior_mono hsub
  intro x hx
  have hxH : x ∈ interior ({x : EucV n | x i₀ = u i₀} : Set (EucV n)) := hinter hx
  rw [interior_coord_eq_empty n i₀ (u i₀)] at hxH
  exact hxH

end

/-! ## Grid subdivisions of boxes -/

noncomputable def gridL (n : ℕ) (K : ℕ) {m : Fin n → ℕ} (j : ∀ i : Fin n, Fin (m i)) : Fin n → ℝ :=
  fun i => ((j i : ℕ) : ℝ) / (K : ℝ)

noncomputable def gridU (n : ℕ) (K : ℕ) {m : Fin n → ℕ} (j : ∀ i : Fin n, Fin (m i)) : Fin n → ℝ :=
  fun i => (((j i : ℕ) + 1) : ℝ) / (K : ℝ)

theorem gridL_le_gridU (n K : ℕ) (hK : 0 < K) {m : Fin n → ℕ}
    (j : ∀ i : Fin n, Fin (m i)) : ∀ i, gridL n K j i ≤ gridU n K j i := by
  intro i
  have hK0 : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
  dsimp [gridL, gridU]
  exact div_le_div_of_nonneg_right (by exact_mod_cast Nat.le_succ (j i : ℕ)) (le_of_lt hK0)

noncomputable def gridCube (n K : ℕ) (hK : 0 < K) {m : Fin n → ℕ}
    (j : ∀ i : Fin n, Fin (m i)) : ConvexBody (EucV n) :=
  coordBody n (gridL n K j) (gridU n K j) (gridL_le_gridU n K hK j)

theorem exists_Fin_Icc_div {K : ℕ} (hK : 0 < K) {m : ℕ} (hm : 0 < m) {x : ℝ}
    (hx0 : 0 ≤ x) (hx : x ≤ (m : ℝ) / (K : ℝ)) :
    ∃ j : Fin m, x ∈ Set.Icc (((j : ℕ) : ℝ) / (K : ℝ)) ((((j : ℕ) : ℝ) + 1) / (K : ℝ)) := by
  have hK0 : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
  by_cases hxeq : x = (m : ℝ) / (K : ℝ)
  · refine ⟨⟨m - 1, by omega⟩, ?_⟩
    dsimp
    constructor
    · have hleN : (m - 1 : ℕ) ≤ m := Nat.sub_le m 1
      have hdiv : ((m - 1 : ℕ) : ℝ) / (K : ℝ) ≤ (m : ℝ) / (K : ℝ) :=
        div_le_div_of_nonneg_right (by exact_mod_cast hleN) (le_of_lt hK0)
      rwa [hxeq]
    · rw [hxeq]
      have hsub : ((m - 1 : ℕ) : ℝ) + 1 = (m : ℝ) := by
        have hle1 : 1 ≤ m := Nat.succ_le_of_lt hm
        have hnat : (m - 1) + 1 = m := Nat.sub_add_cancel hle1
        exact_mod_cast hnat
      rw [← hsub]
  · have hxlt : x < (m : ℝ) / (K : ℝ) := lt_of_le_of_ne hx hxeq
    have hKx : (K : ℝ) * x < (m : ℝ) := by
      have h1 := mul_lt_mul_of_pos_right hxlt hK0
      rw [div_mul_cancel₀ (m : ℝ) (ne_of_gt hK0)] at h1
      rwa [mul_comm] at h1
    let j : ℕ := Nat.floor ((K : ℝ) * x)
    have hjm : j < m := by
      dsimp [j]
      rw [Nat.floor_lt (mul_nonneg (le_of_lt hK0) hx0)]
      exact hKx
    refine ⟨⟨j, hjm⟩, ?_⟩
    dsimp
    constructor
    · have hle : ((j : ℕ) : ℝ) ≤ (K : ℝ) * x := Nat.floor_le (mul_nonneg (le_of_lt hK0) hx0)
      exact (div_le_iff₀ hK0).2 (by rwa [mul_comm] at hle)
    · have hlt : (K : ℝ) * x < ((j : ℕ) : ℝ) + 1 := by
        dsimp [j]
        have := Nat.lt_floor_add_one ((K : ℝ) * x)
        simpa using this
      have hlt' : x * (K : ℝ) < ((j : ℕ) : ℝ) + 1 := by rwa [mul_comm] at hlt
      exact (le_div_iff₀ hK0).2 (le_of_lt hlt')

theorem boxSet_zero_eq_union_grid (n K : ℕ) (hK : 0 < K) {m : Fin n → ℕ}
    (hm : ∀ i, 0 < m i) :
    boxSet n (fun _ => (0 : ℝ)) (fun i => (m i : ℝ) / (K : ℝ)) =
      ⋃ j : (∀ i : Fin n, Fin (m i)),
        boxSet n (gridL n K j) (gridU n K j) := by
  classical
  have hK0 : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
  ext x
  constructor
  · intro hx
    rw [Set.mem_iUnion]
    have hxmem := (mem_boxSet_iff n (fun _ => (0 : ℝ)) (fun i => (m i : ℝ) / (K : ℝ)) x).mp hx
    choose j hj using fun i => exists_Fin_Icc_div (K := K) hK (hm i) (hxmem i).1 (hxmem i).2
    refine ⟨j, ?_⟩
    rw [mem_boxSet_iff]
    intro i
    exact (Set.mem_Icc.mp (hj i))
  · intro hx
    rw [Set.mem_iUnion] at hx
    rcases hx with ⟨j, hx⟩
    rw [mem_boxSet_iff] at hx ⊢
    intro i
    have hji := Set.mem_Icc.mp (hx i)
    have hlow : (0 : ℝ) ≤ x i := le_trans (by
      dsimp [gridL]
      exact div_nonneg (Nat.cast_nonneg _) (le_of_lt hK0)) hji.1
    have hhigh : x i ≤ (m i : ℝ) / (K : ℝ) := by
      have hsucc : (j i : ℕ) + 1 ≤ m i := Nat.succ_le_of_lt (j i).isLt
      have hle : (((j i : ℕ) : ℝ) + 1) / (K : ℝ) ≤ (m i : ℝ) / (K : ℝ) :=
        div_le_div_of_nonneg_right (by exact_mod_cast hsucc) (le_of_lt hK0)
      exact le_trans hji.2 hle
    exact ⟨hlow, hhigh⟩

theorem interior_gridCube_inter_empty (n K : ℕ) (hK : 0 < K) {m : Fin n → ℕ}
    {j j' : ∀ i : Fin n, Fin (m i)} (hjj : j ≠ j') :
    interior (((boxSet n (gridL n K j) (gridU n K j) : Set (EucV n)) ∩
        boxSet n (gridL n K j') (gridU n K j')) : Set (EucV n)) = ∅ := by
  have hne : ∃ i, j i ≠ j' i := by
    by_contra h
    apply hjj
    funext i
    by_contra hnei
    exact h ⟨i, hnei⟩
  rcases hne with ⟨i, hnei⟩
  rcases lt_or_gt_of_ne hnei with hlt | hgt
  · have hle : gridU n K j i ≤ gridL n K j' i := by
      have hsucc : (j i : ℕ) + 1 ≤ (j' i : ℕ) := Nat.succ_le_of_lt (by exact_mod_cast hlt)
      dsimp [gridU, gridL]
      exact div_le_div_of_nonneg_right (by exact_mod_cast hsucc) (le_of_lt (by exact_mod_cast hK))
    exact interior_box_inter_empty n i hle
  · have hle : gridU n K j' i ≤ gridL n K j i := by
      have hsucc : (j' i : ℕ) + 1 ≤ (j i : ℕ) := Nat.succ_le_of_lt (by exact_mod_cast hgt)
      dsimp [gridU, gridL]
      exact div_le_div_of_nonneg_right (by exact_mod_cast hsucc) (le_of_lt (by exact_mod_cast hK))
    have h := interior_box_inter_empty n i (l := gridL n K j') (u := gridU n K j')
      (l' := gridL n K j) (u' := gridU n K j) hle
    rw [Set.inter_comm]
    exact h

/-! ## Valuations on rational grid boxes -/

/-- The cube `[0, 1/K]ⁿ` anchored at the origin. -/
noncomputable def cubeCorner (n K : ℕ) (hK : 0 < K) : ConvexBody (EucV n) :=
  coordBody n (fun _ : Fin n => (0 : ℝ)) (fun _ : Fin n => (1 : ℝ) / (K : ℝ))
    (fun _ => div_nonneg zero_le_one (le_of_lt (by exact_mod_cast hK)))

theorem gridU_sub_gridL (n K : ℕ) (hK : 0 < K) {m : Fin n → ℕ} (j : ∀ i : Fin n, Fin (m i)) :
    (gridU n K j - gridL n K j) = fun _ : Fin n => (1 : ℝ) / (K : ℝ) := by
  have hKreal : (K : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hK)
  funext i
  simp [Pi.sub_apply]
  dsimp [gridU, gridL]
  field_simp [hKreal]
  ring

theorem boxSet_grid_shift (n K : ℕ) (hK : 0 < K) {m : Fin n → ℕ}
    (j : ∀ i : Fin n, Fin (m i)) :
    boxSet n (gridL n K j) (gridU n K j) =
      (fun x : EucV n => x + vecOfFun n (gridL n K j)) ''
        boxSet n (fun _ : Fin n => (0 : ℝ)) (fun _ : Fin n => (1 : ℝ) / (K : ℝ)) := by
  rw [boxSet_translate]
  rw [gridU_sub_gridL n K hK j]
  rfl

theorem gridCube_corner_image (n K : ℕ) (hK : 0 < K) {m : Fin n → ℕ}
    (j : ∀ i : Fin n, Fin (m i)) :
    (gridCube n K hK j : Set (EucV n)) =
      (fun x : EucV n => x + vecOfFun n (gridL n K j)) '' (cubeCorner n K hK : Set (EucV n)) := by
  change boxSet n (gridL n K j) (gridU n K j) =
    (fun x : EucV n => x + vecOfFun n (gridL n K j)) ''
      boxSet n (fun _ : Fin n => (0 : ℝ)) (fun _ : Fin n => (1 : ℝ) / (K : ℝ))
  exact boxSet_grid_shift n K hK j

/-- The unit coordinate cube as a convex body. -/
noncomputable def unitBody (n : ℕ) : ConvexBody (EucV n) :=
  coordBody n (fun _ : Fin n => (0 : ℝ)) (fun _ : Fin n => (1 : ℝ)) (fun _ => by norm_num)

/-- The collection of hypotheses of the main theorem, bundled. -/
structure AxisValuation (n : ℕ) where
  φ : ConvexBody (EucV n) → ℝ
  hcont : Continuous φ
  hadd : ∀ A B C D : ConvexBody (EucV n),
      (A : Set (EucV n)) = (C : Set (EucV n)) ∪ (D : Set (EucV n)) →
      (B : Set (EucV n)) = (C : Set (EucV n)) ∩ (D : Set (EucV n)) → φ A + φ B = φ C + φ D
  htrans : ∀ A B : ConvexBody (EucV n), ∀ t : EucV n,
      (B : Set (EucV n)) = (fun x : EucV n => x + t) '' (A : Set (EucV n)) → φ A = φ B
  hsimple : ∀ K : ConvexBody (EucV n), interior (K : Set (EucV n)) = ∅ → φ K = 0
  hcube : ∀ Q : ConvexBody (EucV n),
      (Q : Set (EucV n)) = (EucE n).symm '' (Set.pi Set.univ (fun _ : Fin n => Set.Icc (0 : ℝ) 1)) → φ Q = 0

namespace AxisValuation

variable {n : ℕ}

/-- The value at the unit cube is zero (this is the hypothesis). -/
lemma unit_body_zero (μ : AxisValuation n) : μ.φ (unitBody n) = 0 := by
  apply μ.hcube
  change (boxSet n (fun _ : Fin n => (0 : ℝ)) (fun _ : Fin n => (1 : ℝ))) =
      (EucE n).symm '' (Set.pi Set.univ (fun _ : Fin n => Set.Icc (0 : ℝ) 1))
  exact boxSet_eq_image n (fun _ : Fin n => (0 : ℝ)) (fun _ : Fin n => (1 : ℝ))

lemma corner_cube_zero (μ : AxisValuation n) (K : ℕ) (hK : 0 < K) :
    μ.φ (cubeCorner n K hK) = 0 := by
  classical
  let φ := μ.φ
  let j₀ : Fin n → Fin K := fun _ => ⟨0, hK⟩
  let B : (Fin n → Fin K) → ConvexBody (EucV n) := fun j => gridCube n K hK (m := fun _ => K) j
  let U : ConvexBody (EucV n) := unitBody n
  have hU : φ U = 0 := by
    dsimp [φ]
    exact unit_body_zero μ
  have hKreal : (K : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hK)
  have hUset : (U : Set (EucV n)) = boxSet n (fun _ : Fin n => (0 : ℝ)) (fun i : Fin n => (K : ℝ) / (K : ℝ)) := by
    dsimp [U]
    simp [unitBody]
    congr 1
    funext i
    field_simp [hKreal]
  have hcov : (U : Set (EucV n)) = ⋃ j : (Fin n → Fin K), (B j : Set (EucV n)) := by
    rw [hUset]
    have hgrid := boxSet_zero_eq_union_grid n K hK (m := fun _ : Fin n => K) (hm := fun _ => hK)
    simpa [B, gridCube] using hgrid
  have hpair : ∀ j j' : Fin n → Fin K, j ≠ j' →
      interior (((B j : Set (EucV n)) ∩ (B j' : Set (EucV n))) : Set (EucV n)) = ∅ := by
    intro j j' hjj
    have h := interior_gridCube_inter_empty n K hK (m := fun _ : Fin n => K) (j := j) (j' := j') hjj
    simpa [B, gridCube] using h
  have hsum : φ U = ∑ j : Fin n → Fin K, φ (B j) := by
    dsimp [φ]
    exact dissection_additivity (V := EucV n) μ.φ μ.hcont μ.hadd μ.hsimple (P := U) (A := B) hcov hpair
  have hcornerB : (gridCube n K hK (m := fun _ => K) j₀ : ConvexBody (EucV n)) = cubeCorner n K hK := by
    apply ConvexBody.ext
    change boxSet n (gridL n K j₀) (gridU n K j₀) =
      boxSet n (fun _ : Fin n => (0 : ℝ)) (fun _ : Fin n => (1 : ℝ) / (K : ℝ))
    rw [show gridL n K j₀ = fun _ : Fin n => (0 : ℝ) by
      funext i; dsimp [gridL, j₀]; simp]
    rw [show gridU n K j₀ = fun _ : Fin n => (1 : ℝ) / (K : ℝ) by
      funext i; dsimp [gridU, j₀]; simp]
  have hBval : ∀ j : Fin n → Fin K, φ (B j) = φ (B j₀) := by
    intro j
    have hc : (gridCube n K hK (m := fun _ => K) j : Set (EucV n)) =
        (fun x : EucV n => x + vecOfFun n (gridL n K j)) ''
          (gridCube n K hK (m := fun _ => K) j₀ : Set (EucV n)) := by
      have h1 := gridCube_corner_image n K hK (m := fun _ => K) j
      have h2 : (cubeCorner n K hK : Set (EucV n)) = (gridCube n K hK (m := fun _ => K) j₀ : Set (EucV n)) := by
        exact congrArg (fun (B : ConvexBody (EucV n)) => (B : Set (EucV n))) hcornerB.symm
      rw [h2] at h1
      exact h1
    have hφj₀ : φ (gridCube n K hK (m := fun _ => K) j₀) = φ (gridCube n K hK (m := fun _ => K) j) := by
      dsimp [φ]
      exact μ.htrans (gridCube n K hK (m := fun _ => K) j₀) (gridCube n K hK (m := fun _ => K) j)
        (vecOfFun n (gridL n K j)) hc
    dsimp [B]
    exact hφj₀.symm
  have hsum1 : (∑ j : Fin n → Fin K, φ (B j)) =
      (Fintype.card (Fin n → Fin K) : ℝ) * φ (cubeCorner n K hK) := by
    calc
      (∑ j : Fin n → Fin K, φ (B j)) = ∑ j : Fin n → Fin K, φ (B j₀) :=
        Finset.sum_congr rfl (fun j hj => hBval j)
      _ = (Fintype.card (Fin n → Fin K) : ℝ) * φ (B j₀) := by simp
      _ = (Fintype.card (Fin n → Fin K) : ℝ) * φ (cubeCorner n K hK) := by
        dsimp [B]
        rw [hcornerB]
  have hcard : (Fintype.card (Fin n → Fin K) : ℝ) = ((K : ℕ) ^ n : ℝ) := by
    rw [Fintype.card_fun]
    simp
  have hleft : φ U = ((K : ℕ) ^ n : ℝ) * φ (cubeCorner n K hK) := by
    rw [hsum, hsum1, hcard]
  have hprod : ((K : ℕ) ^ n : ℝ) * φ (cubeCorner n K hK) = 0 := by
    rw [← hleft, hU]
  have hpow_ne : ((K : ℕ) ^ n : ℝ) ≠ 0 := by
    exact_mod_cast pow_ne_zero n (ne_of_gt hK)
  exact (mul_eq_zero.mp hprod).resolve_left hpow_ne

lemma gridCube_zero (μ : AxisValuation n) (K : ℕ) (hK : 0 < K) {m : Fin n → ℕ}
    (j : ∀ i : Fin n, Fin (m i)) : μ.φ (gridCube n K hK j) = 0 := by
  have hset := gridCube_corner_image n K hK (m := m) j
  have hφ : μ.φ (cubeCorner n K hK) = μ.φ (gridCube n K hK j) :=
    μ.htrans (cubeCorner n K hK) (gridCube n K hK j) (vecOfFun n (gridL n K j)) hset
  rw [← hφ]
  exact corner_cube_zero μ K hK

lemma box_grid_zero (μ : AxisValuation n) (K : ℕ) (hK : 0 < K) (m : Fin n → ℕ) (hm : ∀ i, 0 < m i) :
    μ.φ (coordBody n (fun _ : Fin n => (0 : ℝ)) (fun i : Fin n => (m i : ℝ) / (K : ℝ))
        (fun i => div_nonneg (Nat.cast_nonneg (m i)) (le_of_lt (by exact_mod_cast hK)))) = 0 := by
  classical
  let φ := μ.φ
  let B : ConvexBody (EucV n) :=
    coordBody n (fun _ : Fin n => (0 : ℝ)) (fun i : Fin n => (m i : ℝ) / (K : ℝ))
      (fun i => div_nonneg (Nat.cast_nonneg (m i)) (le_of_lt (by exact_mod_cast hK)))
  let F : (∀ i : Fin n, Fin (m i)) → ConvexBody (EucV n) := fun j => gridCube n K hK j
  have hcov : (B : Set (EucV n)) = ⋃ j : (∀ i : Fin n, Fin (m i)), (F j : Set (EucV n)) := by
    dsimp [B]
    have hgrid := boxSet_zero_eq_union_grid n K hK (m := m) (hm := hm)
    simpa [F, gridCube] using hgrid
  have hpair : ∀ j j' : (∀ i : Fin n, Fin (m i)), j ≠ j' →
      interior (((F j : Set (EucV n)) ∩ (F j' : Set (EucV n))) : Set (EucV n)) = ∅ := by
    intro j j' hjj
    have h := interior_gridCube_inter_empty n K hK (m := m) (j := j) (j' := j') hjj
    simpa [F, gridCube] using h
  have hsum : φ B = ∑ j : (∀ i : Fin n, Fin (m i)), φ (F j) := by
    dsimp [φ]
    exact dissection_additivity (V := EucV n) μ.φ μ.hcont μ.hadd μ.hsimple (P := B) (A := F) hcov hpair
  have hpieces : ∀ j : (∀ i : Fin n, Fin (m i)), φ (F j) = 0 := by
    intro j
    dsimp [F, φ]
    exact gridCube_zero μ K hK j
  calc
    φ B = ∑ j : (∀ i : Fin n, Fin (m i)), φ (F j) := hsum
    _ = ∑ j : (∀ i : Fin n, Fin (m i)), 0 := Finset.sum_congr rfl (fun j hj => hpieces j)
    _ = 0 := by simp

end AxisValuation



/-! ## Hausdorff estimates and degenerate anchored boxes -/

/-- `(Σ tᵢ)² ≥ Σ tᵢ²` for nonnegative `t`. -/
lemma sum_sq_le_sq_sum {ι : Type*} [Fintype ι] (t : ι → ℝ) (ht : ∀ i, 0 ≤ t i) :
    (∑ i, t i ^ 2) ≤ (∑ i, t i) ^ 2 := by
  have htS : ∀ i, t i ≤ ∑ j, t j := fun i => Finset.single_le_sum (fun j hj => ht j) (Finset.mem_univ i)
  have hle : ∀ i, t i ^ 2 ≤ (t i) * (∑ j, t j) := by
    intro i
    have ht0 : 0 ≤ t i := ht i
    have h := mul_le_mul_of_nonneg_left (htS i) ht0
    simpa [pow_two] using h
  calc
    (∑ i, t i ^ 2) ≤ ∑ i, (t i) * (∑ j, t j) := by
      apply Finset.sum_le_sum
      intro i hi
      exact hle i
    _ = (∑ i, t i) * (∑ j, t j) := by rw [Finset.sum_mul]
    _ = (∑ i, t i) ^ 2 := by ring

/-- The Euclidean norm is bounded by the sum of the absolute coordinates. -/
lemma norm_le_sum_abs (n : ℕ) (z : EucV n) : ‖z‖ ≤ ∑ i : Fin n, |z i| := by
  let S : ℝ := ∑ i : Fin n, |z i|
  have hS : 0 ≤ S := Finset.sum_nonneg (fun i hi => abs_nonneg _)
  have hs : (∑ i : Fin n, |z i| ^ 2) ≤ S ^ 2 := by
    dsimp [S]
    exact sum_sq_le_sq_sum (fun i : Fin n => |z i|) (fun i => abs_nonneg _)
  calc
    ‖z‖ = √(∑ i : Fin n, |z i| ^ 2) := by
      rw [EuclideanSpace.norm_eq]
      congr 1
    _ ≤ √(S ^ 2) := Real.sqrt_le_sqrt hs
    _ = S := by rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hS]

/-- Clamping a point of an anchored box into another anchored box moves it by
at most `|a i - b i|` in coordinate `i`. -/
lemma abs_coord_clamp_le (n : ℕ) (a b : Fin n → ℝ) (x y : EucV n)
    (hy : ∀ i, y i = min (x i) (b i)) (hx : ∀ i, 0 ≤ x i ∧ x i ≤ a i) :
    ∀ i, |x i - y i| ≤ |a i - b i| := by
  intro i
  by_cases hxb : x i ≤ b i
  · have hyi : y i = x i := by rw [hy i, min_eq_left hxb]
    rw [hyi]
    simp
  · have hbx : b i < x i := lt_of_not_ge hxb
    have hyi : y i = b i := by rw [hy i, min_eq_right (le_of_lt hbx)]
    rw [hyi]
    have hxle : x i ≤ a i := (hx i).2
    have hab : b i ≤ a i := le_trans (le_of_lt hbx) hxle
    have h1 : |x i - b i| = x i - b i := abs_of_nonneg (sub_nonneg.mpr (le_of_lt hbx))
    have h2 : |a i - b i| = a i - b i := abs_of_nonneg (sub_nonneg.mpr hab)
    rw [h1, h2]
    linarith

/-- Hausdorff distance between anchored boxes is bounded by the sum of the
coordinate differences of their upper corners. -/
lemma hausdorffDist_anchored_le_sum (n : ℕ) (a b : Fin n → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) :
    Metric.hausdorffDist (boxSet n (fun _ : Fin n => (0 : ℝ)) a : Set (EucV n))
      (boxSet n (fun _ : Fin n => (0 : ℝ)) b) ≤ ∑ i : Fin n, |a i - b i| := by
  let r : ℝ := ∑ i : Fin n, |a i - b i|
  have hr : 0 ≤ r := Finset.sum_nonneg (fun i hi => abs_nonneg _)
  apply Metric.hausdorffDist_le_of_mem_dist hr
  · intro x hx
    have hxmem : ∀ i, 0 ≤ x i ∧ x i ≤ a i := (mem_boxSet_iff n (fun _ : Fin n => (0 : ℝ)) a x).mp hx
    let y : EucV n := vecOfFun n (fun i => min (x i) (b i))
    refine ⟨y, ?_, ?_⟩
    · rw [mem_boxSet_iff]
      intro i
      have hyi : y i = min (x i) (b i) := by simp [y]
      constructor
      · rw [hyi]
        exact le_min (hxmem i).1 (hb i)
      · rw [hyi]
        exact min_le_right _ _
    · have hdist : dist x y ≤ ∑ i : Fin n, |x i - y i| := by
        simpa [dist_eq_norm] using norm_le_sum_abs n (x - y)
      refine le_trans hdist ?_
      apply Finset.sum_le_sum
      intro i hi
      exact abs_coord_clamp_le n a b x y (fun i => by simp [y]) hxmem i
  · intro y hy
    have hymem : ∀ i, 0 ≤ y i ∧ y i ≤ b i := (mem_boxSet_iff n (fun _ : Fin n => (0 : ℝ)) b y).mp hy
    let x : EucV n := vecOfFun n (fun i => min (y i) (a i))
    refine ⟨x, ?_, ?_⟩
    · rw [mem_boxSet_iff]
      intro i
      have hxi : x i = min (y i) (a i) := by simp [x]
      constructor
      · rw [hxi]
        exact le_min (hymem i).1 (ha i)
      · rw [hxi]
        exact min_le_right _ _
    · have hdist : dist y x ≤ ∑ i : Fin n, |y i - x i| := by
        simpa [dist_eq_norm] using norm_le_sum_abs n (y - x)
      have hclamp : ∀ i, |y i - x i| ≤ |b i - a i| := by
        intro i
        exact abs_coord_clamp_le n b a y x (fun i => by simp [x]) hymem i
      refine le_trans hdist ?_
      apply Finset.sum_le_sum
      intro i hi
      calc
        |y i - x i| ≤ |b i - a i| := hclamp i
        _ = |a i - b i| := abs_sub_comm _ _

/-- Distance between anchored boxes as convex bodies. -/
lemma dist_coordBody_anchored_le_sum (n : ℕ) (a b : Fin n → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) :
    dist (coordBody n (fun _ : Fin n => (0 : ℝ)) a ha)
      (coordBody n (fun _ : Fin n => (0 : ℝ)) b hb) ≤ ∑ i : Fin n, |a i - b i| := by
  rw [← ConvexBody.hausdorffDist_coe]
  rw [coe_coordBody, coe_coordBody]
  exact hausdorffDist_anchored_le_sum n a b ha hb

/-- An anchored box with a zero-length side has empty interior. -/
lemma interior_anchored_box_empty (n : ℕ) {a : Fin n → ℝ} (i : Fin n) (hai : a i = 0) :
    interior (boxSet n (fun _ : Fin n => (0 : ℝ)) a : Set (EucV n)) = ∅ := by
  apply subset_empty_iff.mp
  have hsub : boxSet n (fun _ : Fin n => (0 : ℝ)) a ⊆ ({x : EucV n | x i = 0} : Set (EucV n)) := by
    intro x hx
    have hxi := (mem_boxSet_iff n (fun _ : Fin n => (0 : ℝ)) a x).mp hx i
    exact le_antisymm (by simpa [hai] using hxi.2) hxi.1
  have hinter : interior (boxSet n (fun _ : Fin n => (0 : ℝ)) a : Set (EucV n)) ⊆
      interior ({x : EucV n | x i = 0} : Set (EucV n)) := interior_mono hsub
  intro x hx
  have hxH : x ∈ interior ({x : EucV n | x i = 0} : Set (EucV n)) := hinter hx
  rw [interior_coord_eq_empty n i 0] at hxH
  exact hxH



lemma rat_coord_common (n : ℕ) (q : Fin n → ℚ) (hq : ∀ i, 0 < (q i : ℝ)) :
    ∃ (m : Fin n → ℕ) (K : ℕ), 0 < K ∧ (∀ i, 0 < m i) ∧
      (∀ i, (q i : ℝ) = ((m i : ℕ) : ℝ) / ((K : ℕ) : ℝ)) := by
  classical
  let K : ℕ := ∏ i : Fin n, (q i).den
  have hK : 0 < K := by
    dsimp [K]
    exact Finset.prod_pos (fun i hi => (q i).den_pos)
  let m : Fin n → ℕ := fun i => (q i).num.toNat * (∏ j ∈ (Finset.univ.erase i), (q j).den)
  refine ⟨m, K, hK, ?_, ?_⟩
  · intro i
    have hqQ : 0 < q i := by exact_mod_cast hq i
    have hnum : 0 < (q i).num := (Rat.num_pos).2 hqQ
    have hnz : 0 < (q i).num.toNat := by
      have hnzI : (0 : ℤ) < ((q i).num.toNat : ℤ) := by
        rw [Int.toNat_of_nonneg (le_of_lt hnum)]
        exact hnum
      exact_mod_cast hnzI
    have hrest : 0 < (∏ j ∈ (Finset.univ.erase i), (q j).den) :=
      Finset.prod_pos (fun j hj => (q j).den_pos)
    dsimp [m]
    exact Nat.mul_pos hnz hrest
  · intro i
    let rest : ℕ := ∏ j ∈ (Finset.univ.erase i), (q j).den
    have hnum0 : 0 ≤ (q i).num := by
      have hqQ : 0 < q i := by exact_mod_cast hq i
      exact le_of_lt ((Rat.num_pos).2 hqQ)
    have hKden : K = (q i).den * rest := by
      dsimp [K, rest]
      rw [Finset.mul_prod_erase (s := Finset.univ) (f := fun j => (q j).den) (a := i) (Finset.mem_univ i)]
    calc
      (q i : ℝ) = ((q i).num : ℝ) / ((q i).den : ℝ) := by
        calc
          (q i : ℝ) = ((Rat.divInt (q i).num ((q i).den : ℤ)) : ℝ) := by rw [(q i).num_divInt_den]
          _ = ((q i).num : ℝ) / (((q i).den : ℤ) : ℝ) := by rw [Rat.cast_divInt]
          _ = ((q i).num : ℝ) / ((q i).den : ℝ) := by norm_num
      _ = ((((q i).num.toNat : ℕ) * rest : ℕ) : ℝ) / (((q i).den * rest : ℕ) : ℝ) := by
        have hnumcast : (((q i).num.toNat : ℕ) : ℝ) = ((q i).num : ℝ) := by
          have hz : (((q i).num.toNat : ℕ) : ℤ) = (q i).num := Int.toNat_of_nonneg hnum0
          calc
            (((q i).num.toNat : ℕ) : ℝ) = ((((q i).num.toNat : ℕ) : ℤ) : ℝ) := by rfl
            _ = ((q i).num : ℝ) := by rw [hz]
        have hrest0 : (0 : ℝ) < (rest : ℝ) := by
          exact_mod_cast (Finset.prod_pos (fun j hj => (q j).den_pos))
        have hden0 : (0 : ℝ) < ((q i).den : ℝ) := by exact_mod_cast (q i).den_pos
        have hL : ((q i).num : ℝ) / ((q i).den : ℝ) =
            (((q i).num.toNat : ℕ) : ℝ) / (((q i).den : ℕ) : ℝ) := by
          rw [← hnumcast]
        have hnummul : ((((q i).num.toNat * rest : ℕ) : ℝ)) =
            (((q i).num.toNat : ℕ) : ℝ) * (rest : ℝ) := by
          norm_num [Nat.cast_mul]
        have hdenmul : ((((q i).den * rest : ℕ) : ℝ)) =
            (((q i).den : ℕ) : ℝ) * (rest : ℝ) := by
          norm_num [Nat.cast_mul]
        rw [hL, hnummul, hdenmul]
        field_simp [ne_of_gt hrest0, ne_of_gt hden0]
      _ = (((m i : ℕ) : ℝ)) / (((K : ℕ) : ℝ)) := by
        have hm : (((m i : ℕ) : ℝ)) = (((q i).num.toNat * rest : ℕ) : ℝ) := by dsimp [m, rest]
        have hKc : (((q i).den * rest : ℕ) : ℝ) = (((K : ℕ) : ℝ)) := by
          rw [hKden.symm]
        rw [hm, hKc]


namespace AxisValuation

variable {n : ℕ}

/-- A coordinate box with positive rational side lengths has value zero. -/
lemma box_rat_pos_zero (μ : AxisValuation n) (q : Fin n → ℚ) (hq : ∀ i, 0 < (q i : ℝ)) :
    μ.φ (coordBody n (fun _ : Fin n => (0 : ℝ)) (fun i : Fin n => (q i : ℝ))
      (fun i => le_of_lt (hq i))) = 0 := by
  classical
  rcases rat_coord_common n q hq with ⟨m, K, hK, hm, hcast⟩
  have hz : μ.φ (coordBody n (fun _ : Fin n => (0 : ℝ))
      (fun i : Fin n => ((m i : ℕ) : ℝ) / ((K : ℕ) : ℝ))
      (fun i => div_nonneg (Nat.cast_nonneg (m i)) (le_of_lt (by exact_mod_cast hK)))) = 0 :=
    box_grid_zero μ K hK m hm
  have hfun : (fun i : Fin n => (q i : ℝ)) = fun i : Fin n => ((m i : ℕ) : ℝ) / ((K : ℕ) : ℝ) := by
    funext i
    exact (hcast i)
  have hB : (coordBody n (fun _ : Fin n => (0 : ℝ)) (fun i : Fin n => (q i : ℝ))
      (fun i => le_of_lt (hq i)) : ConvexBody (EucV n)) =
      coordBody n (fun _ : Fin n => (0 : ℝ))
        (fun i : Fin n => ((m i : ℕ) : ℝ) / ((K : ℕ) : ℝ))
        (fun i => div_nonneg (Nat.cast_nonneg (m i)) (le_of_lt (by exact_mod_cast hK))) := by
    apply ConvexBody.ext
    change boxSet n (fun _ : Fin n => (0 : ℝ)) (fun i : Fin n => (q i : ℝ)) =
      boxSet n (fun _ : Fin n => (0 : ℝ)) (fun i : Fin n => ((m i : ℕ) : ℝ) / ((K : ℕ) : ℝ))
    rw [hfun]
  rw [hB]
  exact hz

/-- An anchored box with strictly positive real side lengths has value zero. -/
lemma anchored_pos_zero (μ : AxisValuation n) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) :
    μ.φ (coordBody n (fun _ : Fin n => (0 : ℝ)) a (fun i => le_of_lt (ha i))) = 0 := by
  classical
  let φ := μ.φ
  let A : ConvexBody (EucV n) :=
    coordBody n (fun _ : Fin n => (0 : ℝ)) a (fun i => le_of_lt (ha i))
  by_contra hne
  have hε : 0 < |φ A| / 2 := half_pos (abs_pos.mpr hne)
  obtain ⟨δ, hδ, hclose⟩ := (Metric.continuousAt_iff.mp μ.hcont.continuousAt) (|φ A| / 2) hε
  let θ : ℝ := δ / ((n : ℝ) + 1)
  have hθ : 0 < θ := div_pos hδ (by positivity)
  have hexists : ∀ i, ∃ q : ℚ, max (a i - θ) 0 < (q : ℝ) ∧ (q : ℝ) < a i := by
    intro i
    have hlo : max (a i - θ) 0 < a i := by
      rw [max_lt_iff]
      exact ⟨by linarith, ha i⟩
    exact exists_rat_btwn hlo
  choose q hq using hexists
  have hqpos : ∀ i, 0 < (q i : ℝ) := by
    intro i
    exact lt_of_le_of_lt (le_max_right (a i - θ) 0) (hq i).1
  have hclose_q : ∀ i, |(q i : ℝ) - a i| < θ := by
    intro i
    have hsub : a i - (q i : ℝ) < θ := by
      have h1 : a i - θ < (q i : ℝ) := lt_of_le_of_lt (le_max_left (a i - θ) 0) (hq i).1
      linarith
    have hpos : 0 < a i - (q i : ℝ) := sub_pos.mpr (hq i).2
    rw [abs_sub_comm, abs_of_pos hpos]
    exact hsub
  let Q : ConvexBody (EucV n) := coordBody n (fun _ : Fin n => (0 : ℝ))
    (fun i : Fin n => (q i : ℝ)) (fun i => le_of_lt (hqpos i))
  have hQzero : φ Q = 0 := by
    dsimp [φ, Q]
    exact box_rat_pos_zero μ q hqpos
  have hdist_le : dist Q A ≤ ∑ i : Fin n, |(q i : ℝ) - a i| := by
    dsimp [Q, A]
    exact dist_coordBody_anchored_le_sum n (fun i : Fin n => (q i : ℝ)) a
      (fun i => le_of_lt (hqpos i)) (fun i => le_of_lt (ha i))
  have hsum_lt : (∑ i : Fin n, |(q i : ℝ) - a i|) < δ := by
    have hle_term : ∀ i, |(q i : ℝ) - a i| ≤ θ := fun i => le_of_lt (hclose_q i)
    have hsum_θ : (∑ i : Fin n, |(q i : ℝ) - a i|) ≤ (n : ℝ) * θ := by
      have h1 : (∑ i : Fin n, |(q i : ℝ) - a i|) ≤ ∑ _i : Fin n, θ :=
        Finset.sum_le_sum (fun i hi => hle_term i)
      rwa [show (∑ _i : Fin n, θ) = (n : ℝ) * θ by simp] at h1
    have hmain : (n : ℝ) * θ < δ := by
      dsimp [θ]
      field_simp [show ((n : ℝ) + 1) ≠ 0 by positivity]
      nlinarith
    exact lt_of_le_of_lt hsum_θ hmain
  have hdist_lt : dist Q A < δ := lt_of_le_of_lt hdist_le hsum_lt
  have hφclose : |φ Q - φ A| < |φ A| / 2 := hclose hdist_lt
  have h : |φ A| < |φ A| / 2 := by
    have hc : |0 - φ A| < |φ A| / 2 := by
      simpa [hQzero] using hφclose
    simpa using hc
  nlinarith [abs_nonneg (φ A)]

/-- An anchored box with nonnegative real side lengths has value zero. -/
lemma anchored_zero (μ : AxisValuation n) (a : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i) :
    μ.φ (coordBody n (fun _ : Fin n => (0 : ℝ)) a ha) = 0 := by
  classical
  by_cases hall : ∀ i, 0 < a i
  · have hz := anchored_pos_zero μ a hall
    have hB : (coordBody n (fun _ : Fin n => (0 : ℝ)) a (fun i => le_of_lt (hall i))) =
        coordBody n (fun _ : Fin n => (0 : ℝ)) a ha := by
      apply ConvexBody.ext
      rfl
    rw [← hB]
    exact hz
  · push_neg at hall
    rcases hall with ⟨i, hnot⟩
    have hai : a i = 0 := le_antisymm hnot (ha i)
    apply μ.hsimple
    rw [coe_coordBody]
    exact interior_anchored_box_empty n i hai

/-- Any axis-parallel box (real side lengths) has value zero. -/
lemma any_box_zero (μ : AxisValuation n) (l u : Fin n → ℝ) (hlu : ∀ i, l i ≤ u i) :
    μ.φ (coordBody n l u hlu) = 0 := by
  have h0 : ∀ i, (0 : ℝ) ≤ u i - l i := fun i => sub_nonneg.mpr (hlu i)
  have htrans : μ.φ (coordBody n l u hlu) = μ.φ (coordBody n (fun _ : Fin n => (0 : ℝ)) (u - l) h0) := by
    exact μ.htrans (coordBody n l u hlu) (coordBody n (fun _ : Fin n => (0 : ℝ)) (u - l) h0)
      (-vecOfFun n l) (coordBody_translate_set n l u hlu h0)
  have hz := anchored_zero μ (u - l) h0
  rw [htrans]
  exact hz

end AxisValuation


/-- Klain box-vanishing, axis-parallel part: a continuous, quadruple-additive,
translation-invariant, *simple* valuation on `EuclideanSpace ℝ (Fin n)` that
vanishes on the unit coordinate cube vanishes on **every** axis-parallel box
`∏ᵢ [l i, u i]` (real side lengths).  Proof route: split the unit cube into
`kⁿ` congruent subcubes of side `1/k` (convex dissection; use the commons
`Commons.Geometry.Convex.Hadwiger.dissection_additivity`) to get
`φ = 0` on cubes of side `1/k`; tile any rational-sided box at the origin by
such cubes (dissection_additivity again); pass to real side lengths by
continuity (boxes converge in the Hausdorff metric as side lengths converge);
translate to remove the lower corner. -/
theorem valuation_zero_on_axisBoxes (n : ℕ) :
    ∀ (φ : ConvexBody (EuclideanSpace ℝ (Fin n)) → ℝ),
      Continuous φ →
      (∀ A B C D : ConvexBody (EuclideanSpace ℝ (Fin n)),
          (A : Set (EuclideanSpace ℝ (Fin n))) = (C : Set (EuclideanSpace ℝ (Fin n))) ∪ (D : Set (EuclideanSpace ℝ (Fin n))) →
          (B : Set (EuclideanSpace ℝ (Fin n))) = (C : Set (EuclideanSpace ℝ (Fin n))) ∩ (D : Set (EuclideanSpace ℝ (Fin n))) →
          φ A + φ B = φ C + φ D) →
      (∀ A B : ConvexBody (EuclideanSpace ℝ (Fin n)), ∀ t : EuclideanSpace ℝ (Fin n),
          (B : Set (EuclideanSpace ℝ (Fin n))) = (fun x : EuclideanSpace ℝ (Fin n) => x + t) '' (A : Set (EuclideanSpace ℝ (Fin n))) →
          φ A = φ B) →
      (∀ K : ConvexBody (EuclideanSpace ℝ (Fin n)), interior (K : Set (EuclideanSpace ℝ (Fin n))) = ∅ → φ K = 0) →
      (∀ Q : ConvexBody (EuclideanSpace ℝ (Fin n)),
          (Q : Set (EuclideanSpace ℝ (Fin n))) =
            (EuclideanSpace.equiv (Fin n) ℝ).symm '' (Set.pi Set.univ (fun _ : Fin n => Set.Icc (0 : ℝ) 1)) →
          φ Q = 0) →
      ∀ (l u : Fin n → ℝ), (∀ i : Fin n, l i ≤ u i) →
        ∀ (Q : ConvexBody (EuclideanSpace ℝ (Fin n))),
          (Q : Set (EuclideanSpace ℝ (Fin n))) =
            (EuclideanSpace.equiv (Fin n) ℝ).symm '' (Set.pi Set.univ (fun i : Fin n => Set.Icc (l i) (u i))) →
          φ Q = 0 := by
  classical
  intro φ hcont hadd htrans hsimple hcube l u hlu Q hQ
  let μ : AxisValuation n := ⟨φ, hcont, hadd, htrans, hsimple, hcube⟩
  have hz : μ.φ (coordBody n l u hlu) = 0 := AxisValuation.any_box_zero μ l u hlu
  have hQbox : (Q : Set (EucV n)) = boxSet n l u := by
    exact hQ.trans (boxSet_eq_image n l u).symm
  have hφQ : φ Q = μ.φ (coordBody n l u hlu) := by
    have hsets : (Q : Set (EucV n)) = ((coordBody n l u hlu : ConvexBody (EucV n)) : Set (EucV n)) := by
      rw [coe_coordBody]
      exact hQbox
    exact val_eq_of_set_eq (V := EucV n) φ hadd (A := Q) (B := coordBody n l u hlu) hsets
  rw [hφQ]
  exact hz

end Commons.Geometry.Convex.Hadwiger