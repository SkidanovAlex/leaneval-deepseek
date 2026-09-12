import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Commons.Geometry.Convex.Hadwiger.dissection_additivity
import Submission.Commons.Geometry.Convex.Hadwiger.simple_valuation_binary_union
import Submission.Commons.Geometry.Convex.Hadwiger.valuation_inclusionExclusion
import Submission.Commons.Geometry.Convex.Hadwiger.exists_lie_unit_to_unit

open Set Filter Metric
open scoped Pointwise Topology BigOperators

namespace Commons.Geometry.Convex.Hadwiger

noncomputable section

namespace ObliquePrismZero

abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- Drop the last coordinate. -/
def dropLast (n : ℕ) (y : E (n + 1)) : E n :=
  (EuclideanSpace.equiv (Fin n) ℝ).symm (fun j : Fin n => y (Fin.castSucc j))

/-- The last coordinate. -/
def lastCoord (n : ℕ) (y : E (n + 1)) : ℝ := y (Fin.last n)

/-- Embed `E n` into `E (n+1)` by putting `0` in the last coordinate. -/
def emb (n : ℕ) (x : E n) : E (n + 1) :=
  (EuclideanSpace.equiv (Fin (n + 1)) ℝ).symm
    (fun i : Fin (n + 1) =>
      if h : i = Fin.last n then 0 else x (Fin.castLT i (Fin.val_lt_last h)))

/-- The last-coordinate unit vector. -/
def eLast (n : ℕ) : E (n + 1) :=
  (EuclideanSpace.equiv (Fin (n + 1)) ℝ).symm
    (fun i : Fin (n + 1) => if i = Fin.last n then 1 else 0)

@[simp] theorem emb_zero (n : ℕ) : emb n (0 : E n) = 0 := by ext i; simp [emb]
@[simp] theorem emb_add (n : ℕ) (x y : E n) : emb n (x + y) = emb n x + emb n y := by
  ext i; dsimp [emb]; by_cases h : i = Fin.last n <;> simp [h]
@[simp] theorem emb_smul (n : ℕ) (a : ℝ) (x : E n) : emb n (a • x) = a • emb n x := by
  ext i; dsimp [emb]; by_cases h : i = Fin.last n <;> simp [h]
@[simp] theorem dropLast_emb (n : ℕ) (x : E n) : dropLast n (emb n x) = x := by
  ext j; simp [dropLast, emb]
@[simp] theorem lastCoord_emb (n : ℕ) (x : E n) : lastCoord n (emb n x) = 0 := by
  simp [lastCoord, emb]
@[simp] theorem dropLast_eLast (n : ℕ) : dropLast n (eLast n) = 0 := by
  ext j; simp [dropLast, eLast]
@[simp] theorem lastCoord_eLast (n : ℕ) : lastCoord n (eLast n) = 1 := by
  simp [lastCoord, eLast]

theorem emb_dropLast_add_last (n : ℕ) (y : E (n + 1)) :
    emb n (dropLast n y) + lastCoord n y • eLast n = y := by
  apply (EuclideanSpace.equiv (Fin (n + 1)) ℝ).injective
  funext i
  by_cases h : i = Fin.last n
  · simp [emb, eLast, lastCoord, h]
  · have hlt := Fin.val_lt_last h
    have hi : Fin.castSucc (Fin.castLT i hlt) = i := by ext; simp [Fin.castLT]
    simp [emb, eLast, lastCoord, dropLast, h, hi]

@[simp] theorem dropLast_add (n : ℕ) (x y : E (n + 1)) : dropLast n (x + y) = dropLast n x + dropLast n y := by ext j; rfl
@[simp] theorem dropLast_smul (n : ℕ) (a : ℝ) (x : E (n + 1)) : dropLast n (a • x) = a • dropLast n x := by ext j; rfl
@[simp] theorem lastCoord_add (n : ℕ) (x y : E (n + 1)) : lastCoord n (x + y) = lastCoord n x + lastCoord n y := by rfl
@[simp] theorem lastCoord_smul (n : ℕ) (a : ℝ) (x : E (n + 1)) : lastCoord n (a • x) = a * lastCoord n x := by rfl
@[simp] theorem dropLast_neg (n : ℕ) (y : E (n + 1)) : dropLast n (-y) = - dropLast n y := by ext j; rfl
@[simp] theorem lastCoord_neg (n : ℕ) (y : E (n + 1)) : lastCoord n (-y) = - lastCoord n y := by rfl

@[simp] theorem emb_neg (n : ℕ) (x : E n) : emb n (-x) = -emb n x := by
  ext i; dsimp [emb]; by_cases h : i = Fin.last n <;> simp [h]
@[simp] theorem emb_sub (n : ℕ) (x y : E n) : emb n (x - y) = emb n x - emb n y := by
  rw [sub_eq_add_neg, sub_eq_add_neg, emb_add, emb_neg]

@[simp] theorem norm_emb (n : ℕ) (x : E n) : ‖emb n x‖ = ‖x‖ := by
  have hsq : ‖emb n x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    rw [Fin.sum_univ_castSucc]
    simp [emb]
  exact (sq_eq_sq_iff_eq_or_eq_neg.mp hsq)
    |>.elim (fun h => h) (fun h => by linarith [norm_nonneg (emb n x), norm_nonneg x])

theorem norm_dropLast_le (n : ℕ) (y : E (n + 1)) : ‖dropLast n y‖ ≤ ‖y‖ := by
  have hsq : ‖dropLast n y‖ ^ 2 ≤ ‖y‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    rw [Fin.sum_univ_castSucc]
    simp [dropLast]
    exact sq_nonneg (y (Fin.last n))
  have habs := sq_le_sq.mp hsq
  have h1 : |‖dropLast n y‖| = ‖dropLast n y‖ := abs_of_nonneg (norm_nonneg _)
  have h2 : |‖y‖| = ‖y‖ := abs_of_nonneg (norm_nonneg _)
  linarith

theorem abs_lastCoord_le_norm (n : ℕ) (y : E (n + 1)) : |lastCoord n y| ≤ ‖y‖ := by
  have h := PiLp.norm_apply_le (p := (2 : ENNReal)) (β := fun _ : Fin (n + 1) => ℝ) y (Fin.last n)
  simpa [lastCoord] using h

@[simp] theorem norm_eLast (n : ℕ) : ‖eLast n‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  rw [Fin.sum_univ_castSucc]
  simp [eLast]

/-- inner product with the last-coordinate basis vector equals the last coordinate -/
theorem inner_eLast (n : ℕ) (y : E (n + 1)) : inner ℝ (eLast n) y = lastCoord n y := by
  have h1 : inner ℝ (eLast n) y = y (Fin.last n) := by
    rw [PiLp.inner_apply]
    rw [Fin.sum_univ_castSucc]
    simp [eLast]
  simpa [lastCoord] using h1

@[simp] theorem inner_eLast_comm (n : ℕ) (y : E (n + 1)) : inner ℝ y (eLast n) = lastCoord n y := by
  rw [real_inner_comm, inner_eLast]

/-- The last coordinate of `ρ⁻¹ y` (for `ρ` sending `eLast` to a unit vector `u`) is the
inner product `⟪y, u⟫`. -/
theorem lastCoord_of_lie (n : ℕ) (ρ : E (n + 1) ≃ₗᵢ[ℝ] E (n + 1)) (u : E (n + 1))
    (hu : ρ (eLast n) = u) (y : E (n + 1)) : lastCoord n (ρ.symm y) = inner ℝ y u := by
  calc
    lastCoord n (ρ.symm y) = inner ℝ (eLast n) (ρ.symm y) := by rw [inner_eLast]
    _ = inner ℝ y (ρ (eLast n)) := by
      have h := (ρ.inner_map_map (ρ.symm y) (eLast n))
      have h' : inner ℝ y (ρ (eLast n)) = inner ℝ (ρ.symm y) (eLast n) := by simpa using h
      rw [real_inner_comm]
      exact h'.symm
    _ = inner ℝ y u := by rw [hu]

/-- the orthogonal projection to the base hyperplane (dropping last coordinate): a point in the
hyperplane `{last = 0}` is exactly `emb (dropLast ·)` of itself. -/
theorem emb_dropLast_eq_self_of_lastCoord_zero {n : ℕ} {y : E (n + 1)}
    (hy : lastCoord n y = 0) : emb n (dropLast n y) = y := by
  calc
    emb n (dropLast n y) = emb n (dropLast n y) + lastCoord n y • eLast n := by simp [hy]
    _ = y := emb_dropLast_add_last n y


/-! ## The prism sets and bodies -/

/-- Prism over base `K` (in the coordinate hyperplane) in direction `w`, generator
parameter running over the interval `[lo,hi]`. -/
def segPrismSet (m : ℕ) (K : ConvexBody (E m)) (w : E (m + 1)) (lo hi : ℝ) : Set (E (m + 1)) :=
  {y : E (m + 1) | ∃ x : E m, x ∈ (K : Set (E m)) ∧
      ∃ t : ℝ, t ∈ Set.Icc lo hi ∧ y = emb m x + t • w}

/-- The unit prism `K + [0,1]·w` (the carrier of the statement). -/
def prismSet (m : ℕ) (K : ConvexBody (E m)) (w : E (m + 1)) : Set (E (m + 1)) :=
  segPrismSet m K w 0 1

/-- The `N`-fold tall prism `K + [0,N]·w`. -/
def bigPrismSet (m : ℕ) (K : ConvexBody (E m)) (w : E (m + 1)) (N : ℕ) : Set (E (m + 1)) :=
  segPrismSet m K w 0 (N : ℝ)

/-- The `j`-th slab `K + [j,j+1]·w` of the tall prism. -/
def slabSet (m : ℕ) (K : ConvexBody (E m)) (w : E (m + 1)) (j : ℕ) : Set (E (m + 1)) :=
  segPrismSet m K w (j : ℝ) ((j : ℝ) + 1)

theorem segPrismSet_convex (m : ℕ) (K : ConvexBody (E m)) (w : E (m + 1)) (lo hi : ℝ) :
    Convex ℝ (segPrismSet m K w lo hi) := by
  rintro y ⟨x1, hx1, t1, ht1, rfl⟩ z ⟨x2, hx2, t2, ht2, rfl⟩ a b ha hb hab
  refine ⟨a • x1 + b • x2, ?_, a • t1 + b • t2, ?_, ?_⟩
  · exact K.convex hx1 hx2 ha hb hab
  · exact (convex_Icc lo hi) ht1 ht2 ha hb hab
  · calc
      a • (emb m x1 + t1 • w) + b • (emb m x2 + t2 • w)
          = (a • emb m x1 + a • (t1 • w)) + (b • emb m x2 + b • (t2 • w)) := by simp [smul_add]
      _ = (a • emb m x1 + b • emb m x2) + (a • (t1 • w) + b • (t2 • w)) := by abel
      _ = emb m (a • x1 + b • x2) + ((a • t1 + b • t2) • w) := by
            rw [← emb_smul m, ← emb_smul m, ← emb_add m]
            rw [smul_smul, smul_smul]
            simp only [smul_eq_mul]
            rw [← add_smul]

theorem segPrismSet_nonempty (m : ℕ) (K : ConvexBody (E m)) (w : E (m + 1))
    (lo hi : ℝ) (h : lo ≤ hi) : (segPrismSet m K w lo hi).Nonempty := by
  rcases K.nonempty with ⟨x, hx⟩
  refine ⟨emb m x + lo • w, ⟨x, hx, lo, ?_, by simp⟩⟩
  exact left_mem_Icc.mpr h

/-- Compactness via the image of `K × Icc lo hi`. -/
theorem segPrismSet_compact (m : ℕ) (K : ConvexBody (E m)) (w : E (m + 1))
    (lo hi : ℝ) : IsCompact (segPrismSet m K w lo hi) := by
  let f : E m × ℝ → E (m + 1) := fun p => emb m p.1 + p.2 • w
  have hf : Continuous f := by
    have h1 : Continuous (fun p : E m × ℝ => emb m p.1) :=
      (LinearMap.continuous_of_finiteDimensional
        { toFun := fun x : E m => emb m x, map_add' := by intro x y; exact emb_add m x y,
          map_smul' := by intro a x; exact emb_smul m a x }).comp continuous_fst
    have h2 : Continuous (fun p : E m × ℝ => p.2 • w) := Continuous.smul continuous_snd continuous_const
    exact h1.add h2
  have himage : segPrismSet m K w lo hi = f '' ((K : Set (E m)) ×ˢ Set.Icc lo hi) := by
    ext y
    constructor
    · rintro ⟨x, hx, t, ht, rfl⟩
      refine ⟨(x, t), ?_, rfl⟩
      exact ⟨hx, ht⟩
    · rintro ⟨p, hp, rfl⟩
      exact ⟨p.1, hp.1, p.2, hp.2, rfl⟩
  rw [himage]
  exact IsCompact.image (K.isCompact.prod isCompact_Icc) hf

theorem segPrismSet_closed (m : ℕ) (K : ConvexBody (E m)) (w : E (m + 1))
    (lo hi : ℝ) : IsClosed (segPrismSet m K w lo hi) :=
  (segPrismSet_compact m K w lo hi).isClosed

theorem segPrismSet_bounded (m : ℕ) (K : ConvexBody (E m)) (w : E (m + 1))
    (lo hi : ℝ) : Bornology.IsBounded (segPrismSet m K w lo hi) :=
  (segPrismSet_compact m K w lo hi).isBounded

/-- The prism over `K` in direction `w` (generator `[0,1]`) as a convex body. -/
def prismBody (m : ℕ) (K : ConvexBody (E m)) (w : E (m + 1)) : ConvexBody (E (m + 1)) :=
  ⟨prismSet m K w, segPrismSet_convex m K w 0 1,
    Metric.isCompact_iff_isClosed_bounded.mpr ⟨segPrismSet_closed m K w 0 1, segPrismSet_bounded m K w 0 1⟩,
    segPrismSet_nonempty m K w 0 1 zero_le_one⟩

@[simp] theorem prismBody_coe (m : ℕ) (K : ConvexBody (E m)) (w : E (m + 1)) :
    (prismBody m K w : Set (E (m + 1))) = prismSet m K w := rfl

/-- The tall prism `K + [0,N]·w` as a convex body. -/
def bigPrismBody (m : ℕ) (K : ConvexBody (E m)) (w : E (m + 1)) (N : ℕ) : ConvexBody (E (m + 1)) :=
  ⟨bigPrismSet m K w N, segPrismSet_convex m K w 0 (N : ℝ),
    Metric.isCompact_iff_isClosed_bounded.mpr ⟨segPrismSet_closed m K w 0 (N : ℝ), segPrismSet_bounded m K w 0 (N : ℝ)⟩,
    segPrismSet_nonempty m K w 0 (N : ℝ) (by exact_mod_cast Nat.zero_le N)⟩

@[simp] theorem bigPrismBody_coe (m : ℕ) (K : ConvexBody (E m)) (w : E (m + 1)) (N : ℕ) :
    (bigPrismBody m K w N : Set (E (m + 1))) = bigPrismSet m K w N := rfl

/-- The `j`-th slab as a convex body. -/
def slabBody (m : ℕ) (K : ConvexBody (E m)) (w : E (m + 1)) (j : ℕ) : ConvexBody (E (m + 1)) :=
  ⟨slabSet m K w j, segPrismSet_convex m K w (j : ℝ) ((j : ℝ) + 1),
    Metric.isCompact_iff_isClosed_bounded.mpr
      ⟨segPrismSet_closed m K w (j : ℝ) ((j : ℝ) + 1), segPrismSet_bounded m K w (j : ℝ) ((j : ℝ) + 1)⟩,
    segPrismSet_nonempty m K w (j : ℝ) ((j : ℝ) + 1) (by simp)⟩

@[simp] theorem slabBody_coe (m : ℕ) (K : ConvexBody (E m)) (w : E (m + 1)) (j : ℕ) :
    (slabBody m K w j : Set (E (m + 1))) = slabSet m K w j := rfl

/-! Membership in the prism sets in generator coordinates. -/

/-- Every point of a prism over `K` (direction `w`, `lastCoord w ≠ 0`) has a unique
representation `emb x + t • w`. -/
theorem segPrism_unique (m : ℕ) (K : ConvexBody (E m)) {w : E (m + 1)}
    (hw : w (Fin.last m) ≠ 0) {y : E (m + 1)}
    {x x' : E m} {t t' : ℝ} (hy₁ : y = emb m x + t • w) (hy₂ : y = emb m x' + t' • w) :
    t = t' ∧ x = x' := by
  have hlast : lastCoord m y = t * w (Fin.last m) := by
    rw [hy₁]
    rw [lastCoord_add, lastCoord_smul, lastCoord_emb]
    simp [lastCoord]
  have hlast' : lastCoord m y = t' * w (Fin.last m) := by
    rw [hy₂]
    rw [lastCoord_add, lastCoord_smul, lastCoord_emb]
    simp [lastCoord]
  have ht : t = t' := by
    have hw1 : w (Fin.last m) * t = w (Fin.last m) * t' := by
      have : t * w (Fin.last m) = t' * w (Fin.last m) := by linarith
      simpa [mul_comm] using this
    exact mul_left_cancel₀ hw hw1
  constructor
  · exact ht
  · have hemb : emb m x = emb m x' := by
      calc
        emb m x = y - t • w := by rw [hy₁]; simp
        _ = emb m x' := by rw [hy₂, ht]; simp
    apply (EuclideanSpace.equiv (Fin m) ℝ).injective
    -- show coordinate-wise equality via dropLast
    have : dropLast m (emb m x) = dropLast m (emb m x') := by rw [hemb]
    simpa using this

/-- A point of the tall prism lies in one of its unit slabs. -/
lemma exists_fin_of_mem_Icc {N : ℕ} (hN : 0 < N) {t : ℝ}
    (ht0 : 0 ≤ t) (htN : t ≤ (N : ℝ)) : ∃ j : Fin N, t ∈ Set.Icc (j : ℝ) ((j : ℝ) + 1) := by
  by_cases htN' : t < (N : ℝ)
  · -- j := floor of t, but bounded by N-1
    let j0 : ℕ := Nat.floor t
    have hf0 : (0 : ℝ) ≤ (j0 : ℝ) := by exact_mod_cast Nat.zero_le j0
    have hf1 : (j0 : ℝ) ≤ t := Nat.floor_le (by positivity : 0 ≤ t)
    have hf2 : t < (j0 : ℝ) + 1 := Nat.lt_floor_add_one t
    have hj0 : j0 < N := by
      by_contra h
      have : (N : ℝ) ≤ (j0 : ℝ) := by exact_mod_cast (Nat.le_of_not_gt h)
      linarith
    refine ⟨⟨j0, hj0⟩, ?_⟩
    exact ⟨hf1, le_of_lt hf2⟩
  · -- t = N (since t ≤ N): use j := N-1
    have ht_eq : t = (N : ℝ) := le_antisymm htN (le_of_not_gt htN')
    have hN1 : N - 1 < N := Nat.pred_lt (Nat.ne_of_gt hN)
    refine ⟨⟨N - 1, hN1⟩, ?_⟩
    rw [ht_eq]
    have hcast : ((N - 1 : ℕ) : ℝ) + 1 = (N : ℝ) := by
      exact_mod_cast (Nat.sub_add_cancel (Nat.succ_le_of_lt hN) : (N - 1 : ℕ) + 1 = N)
    constructor
    · exact_mod_cast Nat.pred_le N
    · rw [hcast]

/-! ## The tall prism as a dissection into unit slabs -/

/-- The `j`-th slab is a translate of the unit prism. -/
theorem slabSet_eq_translate_prismSet (m : ℕ) (K : ConvexBody (E m)) (w : E (m + 1)) (j : ℕ) :
    slabSet m K w j = (fun z : E (m + 1) => z + (j : ℝ) • w) '' prismSet m K w := by
  ext y
  constructor
  · rintro ⟨x, hx, t, ht, rfl⟩
    refine ⟨emb m x + (t - (j : ℝ)) • w, ?_, ?_⟩
    · refine ⟨x, hx, t - (j : ℝ), ?_, rfl⟩
      constructor
      · have : (j : ℝ) ≤ t := ht.1
        linarith
      · have : t ≤ (j : ℝ) + 1 := ht.2
        linarith
    · simp [sub_eq_add_neg, add_smul, smul_add, add_assoc]
  · rintro ⟨z, hz, rfl⟩
    rcases hz with ⟨x, hx, u, hu, rfl⟩
    refine ⟨x, hx, u + (j : ℝ), ?_, ?_⟩
    · constructor <;> linarith [hu.1, hu.2]
    · simp [add_smul, add_assoc]

/-- The tall prism is the union of its `N` unit slabs (for `0 < N`). -/
theorem bigPrismSet_eq_iUnion_slab (m : ℕ) (K : ConvexBody (E m)) (w : E (m + 1))
    (N : ℕ) (hN : 0 < N) :
    bigPrismSet m K w N = ⋃ j : Fin N, slabSet m K w (j : ℕ) := by
  ext y
  constructor
  · intro hy
    rcases hy with ⟨x, hx, t, ht, hy⟩
    rcases exists_fin_of_mem_Icc hN ht.1 ht.2 with ⟨j, hj⟩
    rw [Set.mem_iUnion]
    refine ⟨j, ?_⟩
    exact ⟨x, hx, t, hj, hy⟩
  · intro hy
    rw [Set.mem_iUnion] at hy
    rcases hy with ⟨j, hyj⟩
    rcases hyj with ⟨x, hx, t, ht, hy⟩
    refine ⟨x, hx, t, ?_, hy⟩
    have hj1 : (j : ℕ) + 1 ≤ N := Nat.succ_le_of_lt j.2
    exact ⟨le_trans (by exact_mod_cast (Nat.zero_le (j : ℕ))) ht.1, le_trans ht.2 (by exact_mod_cast hj1)⟩

/-- Two distinct unit intervals `[i,i+1]`, `[j,j+1]` intersect in at most one point. -/
lemma inter_unit_int_singleton {i j : ℕ} (hij : i ≠ j) :
    ∃ t₀ : ℝ, ∀ t : ℝ, t ∈ Set.Icc (i : ℝ) ((i : ℝ) + 1) →
      t ∈ Set.Icc (j : ℝ) ((j : ℝ) + 1) → t = t₀ := by
  have hlt : i < j ∨ j < i := Nat.lt_or_gt_of_ne hij
  rcases hlt with hlt | hlt
  · by_cases hsucc : (i : ℕ) + 1 = j
    · refine ⟨(j : ℝ), ?_⟩
      intro t hti htj
      have ht1 : t ≤ (i : ℝ) + 1 := hti.2
      have ht2 : (j : ℝ) ≤ t := htj.1
      have hcast : (i : ℝ) + 1 = (j : ℝ) := by
        exact_mod_cast hsucc
      have ht3 : t ≤ (j : ℝ) := by
        rw [← hcast]
        exact ht1
      linarith
    · have hj2 : (i : ℕ) + 2 ≤ j := by omega
      refine ⟨(0 : ℝ), ?_⟩
      intro t hti htj
      exfalso
      have ht1 : t ≤ (i : ℝ) + 1 := hti.2
      have ht2 : (j : ℝ) ≤ t := htj.1
      have hjbig_nat : (i : ℕ) + 1 < j := by omega
      have hjbig : (i : ℝ) + 1 < (j : ℝ) := by exact_mod_cast hjbig_nat
      linarith
  · by_cases hsucc : (j : ℕ) + 1 = i
    · refine ⟨(i : ℝ), ?_⟩
      intro t hti htj
      have ht1 : t ≤ (j : ℝ) + 1 := htj.2
      have ht2 : (i : ℝ) ≤ t := hti.1
      have hcast : (j : ℝ) + 1 = (i : ℝ) := by
        exact_mod_cast hsucc
      have ht3 : t ≤ (i : ℝ) := by
        rw [← hcast]
        exact ht1
      linarith
    · have hi2 : (j : ℕ) + 2 ≤ i := by omega
      refine ⟨(0 : ℝ), ?_⟩
      intro t hti htj
      exfalso
      have ht1 : t ≤ (j : ℝ) + 1 := htj.2
      have ht2 : (i : ℝ) ≤ t := hti.1
      have hibig_nat : (j : ℕ) + 1 < i := by omega
      have hibig : (j : ℝ) + 1 < (i : ℝ) := by exact_mod_cast hibig_nat
      linarith

/-- Interior of a level set of the last coordinate is empty. -/
lemma interior_lastCoord_level_empty (m : ℕ) (s : ℝ) :
    interior {y : E (m + 1) | lastCoord m y = s} = ∅ := by
  have hset : {y : E (m + 1) | lastCoord m y = s} =
      {y : E (m + 1) | inner ℝ (eLast m) y = s} := by
    ext x
    change lastCoord m x = s ↔ inner ℝ (eLast m) x = s
    rw [inner_eLast]
  rw [hset]
  have heLast_ne : eLast m ≠ (0 : E (m + 1)) := by
    intro hz
    have h := congrArg (norm : E (m + 1) → ℝ) hz
    rw [norm_eLast, norm_zero] at h
    norm_num at h
  exact interior_hpPlane_empty (eLast m) heLast_ne s

/-- The pairwise intersections of unit slabs of the tall prism have empty interior. -/
theorem slab_interior_inter_empty (m : ℕ) (K : ConvexBody (E m)) {w : E (m + 1)}
    (hw : w (Fin.last m) ≠ 0) {i j : ℕ} (hij : i ≠ j) :
    interior ((slabSet m K w i : Set (E (m + 1))) ∩ (slabSet m K w j : Set (E (m + 1)))) = ∅ := by
  rcases inter_unit_int_singleton hij with ⟨t₀, ht₀⟩
  let L : Set (E (m + 1)) := {y | lastCoord m y = t₀ * w (Fin.last m)}
  have hsub : (slabSet m K w i : Set (E (m + 1))) ∩ (slabSet m K w j : Set (E (m + 1))) ⊆ L := by
    intro y hy
    rcases hy.1 with ⟨x, hx, t, ht, rfl⟩
    rcases hy.2 with ⟨x', hx', t', ht', hy'⟩
    rcases segPrism_unique (m := m) (K := K) hw rfl hy'.symm with ⟨ht_eq, hx_eq⟩
    have ht_j : t ∈ Set.Icc (j : ℝ) ((j : ℝ) + 1) := by
      simpa [ht_eq] using ht'
    have ht0 : t = t₀ := ht₀ t ht ht_j
    have hlast : lastCoord m (emb m x + t • w) = t * w (Fin.last m) := by
      rw [lastCoord_add, lastCoord_smul, lastCoord_emb]
      simp [lastCoord]
    change lastCoord m (emb m x + t • w) = t₀ * w (Fin.last m)
    rw [hlast, ht0]
  have hLempty : interior L = ∅ := interior_lastCoord_level_empty m (t₀ * w (Fin.last m))
  apply subset_antisymm
  · exact (interior_mono hsub).trans (by simpa [hLempty])
  · exact empty_subset _

/-- Value of the tall prism: `μ (K + [0,N]·w) = N · μ (K + [0,1]·w)`. -/
theorem mu_bigPrism (m : ℕ) (μ : ConvexBody (E (m + 1)) → ℝ)
    (hcont : Continuous μ)
    (hadd : ∀ A B C D : ConvexBody (E (m + 1)),
        (A : Set (E (m + 1))) = (C : Set (E (m + 1))) ∪ (D : Set (E (m + 1))) →
        (B : Set (E (m + 1))) = (C : Set (E (m + 1))) ∩ (D : Set (E (m + 1))) →
        μ A + μ B = μ C + μ D)
    (htrans : ∀ A B : ConvexBody (E (m + 1)), ∀ t : E (m + 1),
        (B : Set (E (m + 1))) = (fun x : E (m + 1) => x + t) '' (A : Set (E (m + 1))) → μ A = μ B)
    (hsimple : ∀ K : ConvexBody (E (m + 1)), interior (K : Set (E (m + 1))) = ∅ → μ K = 0)
    (K : ConvexBody (E m)) {w : E (m + 1)} (hw : w (Fin.last m) ≠ 0)
    (N : ℕ) (hN : 0 < N) :
    μ (bigPrismBody m K w N) = (N : ℝ) • μ (prismBody m K w) := by
  let A : Fin N → ConvexBody (E (m + 1)) := fun j => slabBody m K w (j : ℕ)
  have hcover : ((bigPrismBody m K w N : ConvexBody (E (m + 1))) : Set (E (m + 1))) =
      ⋃ j : Fin N, (A j : Set (E (m + 1))) := by
    change bigPrismSet m K w N = ⋃ j : Fin N, slabSet m K w (j : ℕ)
    exact bigPrismSet_eq_iUnion_slab m K w N hN
  have hpair : ∀ i j : Fin N, i ≠ j →
      interior ((A i : Set (E (m + 1))) ∩ (A j : Set (E (m + 1)))) = ∅ := by
    intro i j hij
    have hnat : (i : ℕ) ≠ (j : ℕ) := by
      intro h
      apply hij
      exact Fin.ext h
    change interior ((slabSet m K w (i : ℕ)) ∩ (slabSet m K w (j : ℕ))) = ∅
    exact slab_interior_inter_empty m K hw hnat
  have hmain := dissection_additivity (V := E (m + 1)) μ hcont hadd hsimple
    (bigPrismBody m K w N) A hcover hpair
  rw [hmain]
  calc
    (∑ j : Fin N, μ (A j)) = ∑ j : Fin N, μ (prismBody m K w) := by
      refine Finset.sum_congr rfl ?_
      intro j hj
      have htr : ((A j : ConvexBody (E (m + 1))) : Set (E (m + 1))) =
          (fun x : E (m + 1) => x + (j : ℝ) • w) '' (prismBody m K w : Set (E (m + 1))) := by
        change slabSet m K w (j : ℕ) = (fun x : E (m + 1) => x + (j : ℝ) • w) '' prismSet m K w
        exact slabSet_eq_translate_prismSet m K w (j : ℕ)
      exact (htrans (prismBody m K w) (A j) ((j : ℝ) • w) htr).symm
    _ = (N : ℝ) • μ (prismBody m K w) := by
      simp [Finset.sum_const]

/-! ## Halfspace cuts of a convex body -/

/-- Translate a convex body by a vector. -/
def transBody {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (K : ConvexBody V) (t : V) : ConvexBody V :=
  ⟨(fun x : V => x + t) '' (K : Set V),
    by simpa [add_comm] using K.convex.translate t,
    by simpa using K.isCompact.image (by fun_prop : Continuous (fun x : V => x + t)),
    by simpa using K.nonempty.image (fun x : V => x + t)⟩

@[simp] theorem transBody_coe {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (K : ConvexBody V) (t : V) :
    (transBody K t : Set V) = (fun x : V => x + t) '' (K : Set V) := rfl

/-- `P ∩ {⟨u,·⟩ ≤ c}` as a convex body (given nonempty). -/
def cutLeBody (m : ℕ) (P : ConvexBody (E (m + 1))) (w : E (m + 1)) (c : ℝ)
    (hne : ((P : Set (E (m + 1))) ∩ {y | inner ℝ w y ≤ c}).Nonempty) :
    ConvexBody (E (m + 1)) :=
  ⟨(P : Set (E (m + 1))) ∩ {y | inner ℝ w y ≤ c},
    P.convex.inter (convex_hpLower w c),
    (by
      apply Metric.isCompact_iff_isClosed_bounded.mpr
      constructor
      · exact P.isCompact.isClosed.inter (isClosed_hpLower w c)
      · exact P.isCompact.isBounded.subset (by intro y hy; exact hy.1)),
    hne⟩

@[simp] theorem cutLeBody_coe (m : ℕ) (P : ConvexBody (E (m + 1))) (w : E (m + 1)) (c : ℝ)
    (hne : ((P : Set (E (m + 1))) ∩ {y | inner ℝ w y ≤ c}).Nonempty) :
    ((cutLeBody m P w c hne : ConvexBody (E (m + 1))) : Set (E (m + 1))) =
      (P : Set (E (m + 1))) ∩ {y | inner ℝ w y ≤ c} := rfl

/-- `P ∩ {⟨u,·⟩ ≥ c}` as a convex body (given nonempty). -/
def cutGeBody (m : ℕ) (P : ConvexBody (E (m + 1))) (w : E (m + 1)) (c : ℝ)
    (hne : ((P : Set (E (m + 1))) ∩ {y | c ≤ inner ℝ w y}).Nonempty) :
    ConvexBody (E (m + 1)) :=
  ⟨(P : Set (E (m + 1))) ∩ {y | c ≤ inner ℝ w y},
    P.convex.inter (convex_hpUpper w c),
    (by
      apply Metric.isCompact_iff_isClosed_bounded.mpr
      constructor
      · exact P.isCompact.isClosed.inter (isClosed_hpUpper w c)
      · exact P.isCompact.isBounded.subset (by intro y hy; exact hy.1)),
    hne⟩

@[simp] theorem cutGeBody_coe (m : ℕ) (P : ConvexBody (E (m + 1))) (w : E (m + 1)) (c : ℝ)
    (hne : ((P : Set (E (m + 1))) ∩ {y | c ≤ inner ℝ w y}).Nonempty) :
    ((cutGeBody m P w c hne : ConvexBody (E (m + 1))) : Set (E (m + 1))) =
      (P : Set (E (m + 1))) ∩ {y | c ≤ inner ℝ w y} := rfl

/-- `P ∩ {⟨u,·⟩ = c}` as a convex body (given nonempty). -/
def cutEqBody (m : ℕ) (P : ConvexBody (E (m + 1))) (w : E (m + 1)) (c : ℝ)
    (hne : ((P : Set (E (m + 1))) ∩ {y | inner ℝ w y = c}).Nonempty) :
    ConvexBody (E (m + 1)) :=
  ⟨(P : Set (E (m + 1))) ∩ {y | inner ℝ w y = c},
    P.convex.inter (convex_hpPlane w c),
    (by
      apply Metric.isCompact_iff_isClosed_bounded.mpr
      constructor
      · exact P.isCompact.isClosed.inter (isClosed_hpPlane w c)
      · exact P.isCompact.isBounded.subset (by intro y hy; exact hy.1)),
    hne⟩

@[simp] theorem cutEqBody_coe (m : ℕ) (P : ConvexBody (E (m + 1))) (w : E (m + 1)) (c : ℝ)
    (hne : ((P : Set (E (m + 1))) ∩ {y | inner ℝ w y = c}).Nonempty) :
    ((cutEqBody m P w c hne : ConvexBody (E (m + 1))) : Set (E (m + 1))) =
      (P : Set (E (m + 1))) ∩ {y | inner ℝ w y = c} := rfl

/-- A convex body is the union of its `≤ c` and `≥ c` cuts, with flat intersection. -/
theorem body_split_le_ge (m : ℕ) (P : ConvexBody (E (m + 1))) (w : E (m + 1)) (c : ℝ)
    (hneLe : ((P : Set (E (m + 1))) ∩ {y | inner ℝ w y ≤ c}).Nonempty)
    (hneGe : ((P : Set (E (m + 1))) ∩ {y | c ≤ inner ℝ w y}).Nonempty) :
    (P : Set (E (m + 1))) =
      ((cutLeBody m P w c hneLe : Set (E (m + 1))) ∪ (cutGeBody m P w c hneGe : Set (E (m + 1)))) := by
  ext y
  constructor
  · intro hy
    by_cases h : inner ℝ w y ≤ c
    · exact Or.inl ⟨hy, h⟩
    · exact Or.inr ⟨hy, le_of_not_ge h⟩
  · intro hy
    rcases hy with h | h
    · exact h.1
    · exact h.1

theorem body_inter_le_ge (m : ℕ) (P : ConvexBody (E (m + 1))) (w : E (m + 1)) (c : ℝ)
    (hneLe : ((P : Set (E (m + 1))) ∩ {y | inner ℝ w y ≤ c}).Nonempty)
    (hneGe : ((P : Set (E (m + 1))) ∩ {y | c ≤ inner ℝ w y}).Nonempty) :
    ((cutLeBody m P w c hneLe : Set (E (m + 1))) ∩ (cutGeBody m P w c hneGe : Set (E (m + 1)))) =
      ((P : Set (E (m + 1))) ∩ {y | inner ℝ w y = c}) := by
  ext y
  constructor
  · rintro ⟨hy1, hy2⟩
    exact ⟨hy1.1, le_antisymm hy1.2 hy2.2⟩
  · intro hy
    exact ⟨⟨hy.1, le_of_eq hy.2⟩, ⟨hy.1, ge_of_eq hy.2⟩⟩

/-- Interior of `P ∩ {⟨u,·⟩ = c}` is empty (hyperplane inside `P`). -/
theorem interior_cutEq_empty (m : ℕ) (P : ConvexBody (E (m + 1))) {w : E (m + 1)}
    (hw : w ≠ 0) (c : ℝ)
    (hne : ((P : Set (E (m + 1))) ∩ {y | inner ℝ w y = c}).Nonempty) :
    interior ((cutEqBody m P w c hne : Set (E (m + 1)))) = ∅ := by
  have hsub : ((cutEqBody m P w c hne : Set (E (m + 1)))) ⊆ {y | inner ℝ w y = c} := by
    intro y hy
    exact hy.2
  have hPlane : interior {y : E (m + 1) | inner ℝ w y = c} = ∅ := interior_hpPlane_empty w hw c
  apply subset_antisymm
  · exact (interior_mono hsub).trans (by simpa [hPlane])
  · exact empty_subset _


/-! ## The mid-cut identity (raw sets) -/

/-- `w ≠ 0` follows from a nonzero last coordinate. -/
theorem w_ne_zero_of_last (m : ℕ) {w : E (m + 1)} (hw : w (Fin.last m) ≠ 0) : w ≠ 0 := by
  intro h
  apply hw
  rw [h]
  simp

/-- `‖w‖² > 0`. -/
lemma norm_sq_pos_of_last (m : ℕ) {w : E (m + 1)} (hw : w (Fin.last m) ≠ 0) : 0 < ‖w‖ ^ 2 := by
  exact sq_pos_of_ne_zero (norm_ne_zero_iff.mpr (w_ne_zero_of_last m hw))

/-- Inner product of `w` with a generator point. -/
theorem inner_w_gen (m : ℕ) (x : E m) (w : E (m + 1)) (t : ℝ) :
    inner ℝ w (emb m x + t • w) = inner ℝ w (emb m x) + t * ‖w‖ ^ 2 := by
  rw [inner_add_right, inner_smul_right, real_inner_self_eq_norm_sq]

/-- `{b + u•w | b ∈ B, u ∈ [0,N]}`. -/
def cylFromSet (m : ℕ) (B : Set (E (m + 1))) (w : E (m + 1)) (N : ℕ) : Set (E (m + 1)) :=
  (fun p : E (m + 1) × ℝ => p.1 + p.2 • w) '' (B ×ˢ Set.Icc (0 : ℝ) (N : ℝ))

/-- The mid-slice `K + [0,N]·w` at level `⟨w,·⟩ = c`. -/
def midSliceSet (m : ℕ) (K : ConvexBody (E m)) (w : E (m + 1)) (c : ℝ) (N : ℕ) : Set (E (m + 1)) :=
  bigPrismSet m K w N ∩ {y | inner ℝ w y = c}

/-- The reassembly: lower part slid up by `N·w`, glued to the upper part. -/
def slideUnion (m : ℕ) (K : ConvexBody (E m)) (w : E (m + 1)) (c : ℝ) (N : ℕ) : Set (E (m + 1)) :=
  ((fun z : E (m + 1) => z + (N : ℝ) • w) ''
    (bigPrismSet m K w N ∩ {y | inner ℝ w y ≤ c})) ∪
  (bigPrismSet m K w N ∩ {y | c ≤ inner ℝ w y})

/-- Membership in the tall prism. -/
theorem mem_bigPrismSet (m : ℕ) (K : ConvexBody (E m)) (w : E (m + 1)) (N : ℕ) (y : E (m + 1)) :
    y ∈ bigPrismSet m K w N ↔
      ∃ x : E m, x ∈ (K : Set (E m)) ∧ ∃ t : ℝ, t ∈ Set.Icc (0 : ℝ) (N : ℝ) ∧ y = emb m x + t • w := by
  constructor <;> intro h <;> exact h

/-- Membership in the cylinder-from-set. -/
theorem mem_cylFromSet (m : ℕ) (B : Set (E (m + 1))) (w : E (m + 1)) (N : ℕ) (y : E (m + 1)) :
    y ∈ cylFromSet m B w N ↔ ∃ b : E (m + 1), b ∈ B ∧ ∃ u : ℝ, u ∈ Set.Icc (0 : ℝ) (N : ℝ) ∧ y = b + u • w := by
  constructor
  · intro hy
    rcases hy with ⟨p, hp, hpf⟩
    exact ⟨p.1, hp.1, p.2, hp.2, hpf.symm⟩
  · rintro ⟨b, hb, u, hu, hy⟩
    refine ⟨(b, u), ⟨hb, hu⟩, hy.symm⟩

/-- Membership in the slide union. -/
theorem mem_slideUnion (m : ℕ) (K : ConvexBody (E m)) (w : E (m + 1)) (c : ℝ) (N : ℕ) (y : E (m + 1)) :
    y ∈ slideUnion m K w c N ↔
      (∃ z : E (m + 1), z ∈ bigPrismSet m K w N ∧ inner ℝ w z ≤ c ∧ y = z + (N : ℝ) • w) ∨
      (y ∈ bigPrismSet m K w N ∧ c ≤ inner ℝ w y) := by
  constructor
  · intro hy
    rcases hy with hy | hy
    · left
      rcases hy with ⟨z, hz, hyz⟩
      exact ⟨z, hz.1, hz.2, hyz.symm⟩
    · right
      exact hy
  · intro hy
    rcases hy with ⟨z, hz1, hz2, hyz⟩ | hy
    · left
      exact ⟨z, ⟨hz1, hz2⟩, hyz.symm⟩
    · right
      exact hy

/-- The mid-point parameter `t0 = (c - ⟨w,emb x⟩)/‖w‖²` on the generator over `x`. -/
def t0of (m : ℕ) (w : E (m + 1)) (c : ℝ) (x : E m) : ℝ :=
  (c - inner ℝ w (emb m x)) / ‖w‖ ^ 2

theorem inner_w_gen_t0 (m : ℕ) {w : E (m + 1)} (hw : w (Fin.last m) ≠ 0)
    (c : ℝ) (x : E m) : inner ℝ w (emb m x + t0of m w c x • w) = c := by
  dsimp [t0of]
  rw [inner_w_gen]
  have hnorm : ‖w‖ ^ 2 ≠ 0 := ne_of_gt (norm_sq_pos_of_last m hw)
  have hwnz : ‖w‖ ≠ 0 := (norm_ne_zero_iff.mpr (w_ne_zero_of_last m hw))
  field_simp [hnorm, hwnz]
  ring_nf

/-! ### arithmetic around the mid parameter `t0of` -/


theorem inner_le_t0of_iff (m : ℕ) {w : E (m + 1)} (hw : w (Fin.last m) ≠ 0)
    (x : E m) (t : ℝ) (c : ℝ) : inner ℝ w (emb m x + t • w) ≤ c ↔ t ≤ t0of m w c x := by
  rw [inner_w_gen]
  dsimp [t0of]
  have hnorm : 0 < ‖w‖ ^ 2 := norm_sq_pos_of_last m hw
  constructor
  · intro h
    exact (le_div_iff₀ hnorm).2 (by nlinarith)
  · intro h
    have h' : t * ‖w‖ ^ 2 ≤ c - inner ℝ w (emb m x) := (le_div_iff₀ hnorm).1 h
    nlinarith

theorem le_inner_t0of_iff (m : ℕ) {w : E (m + 1)} (hw : w (Fin.last m) ≠ 0)
    (x : E m) (t : ℝ) (c : ℝ) : c ≤ inner ℝ w (emb m x + t • w) ↔ t0of m w c x ≤ t := by
  rw [inner_w_gen]
  dsimp [t0of]
  have hnorm : 0 < ‖w‖ ^ 2 := norm_sq_pos_of_last m hw
  constructor
  · intro h
    exact (div_le_iff₀ hnorm).2 (by nlinarith)
  · intro h
    have h' : (c - inner ℝ w (emb m x)) ≤ t * ‖w‖ ^ 2 := (div_le_iff₀ hnorm).1 h
    nlinarith

/-- `0 ≤ t0` from `inner (emb x) ≤ c`. -/
theorem t0of_nonneg_of_le (m : ℕ) {w : E (m + 1)} (hw : w (Fin.last m) ≠ 0)
    (x : E m) (c : ℝ) (hle : inner ℝ w (emb m x) ≤ c) : 0 ≤ t0of m w c x := by
  dsimp [t0of]
  have hnorm : 0 < ‖w‖ ^ 2 := norm_sq_pos_of_last m hw
  rw [div_nonneg_iff]
  left
  exact ⟨sub_nonneg.mpr hle, le_of_lt hnorm⟩

/-- `t0 ≤ N` when `inner (emb x) + N‖w‖² ≥ c`. -/
theorem t0of_le_of_ge (m : ℕ) {w : E (m + 1)} (hw : w (Fin.last m) ≠ 0)
    (x : E m) (c : ℝ) (N : ℕ) (hge : c ≤ inner ℝ w (emb m x + (N : ℝ) • w)) :
    t0of m w c x ≤ (N : ℝ) := by
  exact (le_inner_t0of_iff m hw x (N : ℝ) c).mp hge

/-- `t0 = (c - ⟨w,emb x⟩)/‖w‖²` lies in `[0,N]` when the bottom point of the
generator lies at or below level `c` and the top point at or above level `c`. -/
theorem t0of_mem_of_le_ge (m : ℕ) {w : E (m + 1)} (hw : w (Fin.last m) ≠ 0)
    (x : E m) (c : ℝ) (N : ℕ)
    (hlo : inner ℝ w (emb m x) ≤ c)
    (hhi : c ≤ inner ℝ w (emb m x + (N : ℝ) • w)) :
    t0of m w c x ∈ Set.Icc (0 : ℝ) (N : ℝ) := by
  constructor
  · exact t0of_nonneg_of_le m hw x c hlo
  · exact t0of_le_of_ge m hw x c N hhi

/-! ### The slide-union equals the cylinder over the mid-slice -/



theorem slideUnion_subset_cyl (m : ℕ) (K : ConvexBody (E m)) {w : E (m + 1)}
    (hw : w (Fin.last m) ≠ 0) (c : ℝ) (N : ℕ)
    (hKlo : ∀ x : E m, x ∈ (K : Set (E m)) → inner ℝ w (emb m x) ≤ c)
    (hKhi : ∀ x : E m, x ∈ (K : Set (E m)) → c ≤ inner ℝ w (emb m x + (N : ℝ) • w)) :
    slideUnion m K w c N ⊆ cylFromSet m (midSliceSet m K w c N) w N := by
  intro y hy
  rw [slideUnion] at hy
  rcases hy with hy | hy
  · rcases hy with ⟨z, hz, hyz⟩
    rcases hz with ⟨hzP, hzle⟩
    rcases (mem_bigPrismSet m K w N z).mp hzP with ⟨x, hx, t, ht, hzt⟩
    let t0 : ℝ := t0of m w c x
    have ht0 : t0 ∈ Set.Icc (0 : ℝ) (N : ℝ) := t0of_mem_of_le_ge m hw x c N (hKlo x hx) (hKhi x hx)
    have hz_in : inner ℝ w (emb m x + t • w) = inner ℝ w z := by rw [← hzt]
    have ht_le_t0 : t ≤ t0 := by
      have : inner ℝ w (emb m x + t • w) ≤ c := by simpa [hz_in] using hzle
      exact (inner_le_t0of_iff m hw x t c).mp this
    let u : ℝ := t + (N : ℝ) - t0
    have hu0 : 0 ≤ u := by dsimp [u]; nlinarith [ht.1, ht0.2]
    have huN : u ≤ (N : ℝ) := by dsimp [u]; nlinarith [ht_le_t0]
    change y ∈ (fun p : E (m + 1) × ℝ => p.1 + p.2 • w) '' (midSliceSet m K w c N ×ˢ Set.Icc (0 : ℝ) (N : ℝ))
    refine ⟨(emb m x + t0 • w, u), ?_, ?_⟩
    · constructor
      · rw [midSliceSet]
        constructor
        · exact (mem_bigPrismSet m K w N (emb m x + t0 • w)).mpr ⟨x, hx, t0, ht0, rfl⟩
        · exact inner_w_gen_t0 m hw c x
      · exact ⟨hu0, huN⟩
    · dsimp
      calc
        (emb m x + t0 • w) + u • w = emb m x + (t0 + u) • w := by simp [add_smul, add_assoc]
        _ = emb m x + (t + (N : ℝ)) • w := by
          congr 1
          dsimp [u]
          ring
        _ = (emb m x + t • w) + (N : ℝ) • w := by simp [add_smul, add_assoc]
        _ = z + (N : ℝ) • w := by rw [hzt]
        _ = y := hyz
  · rcases hy with ⟨hyP, hyge⟩
    rcases (mem_bigPrismSet m K w N y).mp hyP with ⟨x, hx, t, ht, hyt⟩
    let t0 : ℝ := t0of m w c x
    have ht0 : t0 ∈ Set.Icc (0 : ℝ) (N : ℝ) := t0of_mem_of_le_ge m hw x c N (hKlo x hx) (hKhi x hx)
    have hy_in : inner ℝ w (emb m x + t • w) = inner ℝ w y := by rw [← hyt]
    have ht0_le_t : t0 ≤ t := by
      have : c ≤ inner ℝ w (emb m x + t • w) := by simpa [hy_in] using hyge
      exact (le_inner_t0of_iff m hw x t c).mp this
    let u : ℝ := t - t0
    have hu0 : 0 ≤ u := by dsimp [u]; linarith
    have huN : u ≤ (N : ℝ) := by dsimp [u]; linarith [ht.2, ht0.1]
    change y ∈ (fun p : E (m + 1) × ℝ => p.1 + p.2 • w) '' (midSliceSet m K w c N ×ˢ Set.Icc (0 : ℝ) (N : ℝ))
    refine ⟨(emb m x + t0 • w, u), ?_, ?_⟩
    · constructor
      · rw [midSliceSet]
        constructor
        · exact (mem_bigPrismSet m K w N (emb m x + t0 • w)).mpr ⟨x, hx, t0, ht0, rfl⟩
        · exact inner_w_gen_t0 m hw c x
      · exact ⟨hu0, huN⟩
    · dsimp
      calc
        (emb m x + t0 • w) + u • w = emb m x + (t0 + u) • w := by simp [add_smul, add_assoc]
        _ = emb m x + t • w := by
          congr 1
          dsimp [u]
          ring
        _ = y := hyt.symm

theorem cyl_subset_slideUnion (m : ℕ) (K : ConvexBody (E m)) {w : E (m + 1)}
    (hw : w (Fin.last m) ≠ 0) (c : ℝ) (N : ℕ) :
    cylFromSet m (midSliceSet m K w c N) w N ⊆ slideUnion m K w c N := by
  intro y hy
  rw [cylFromSet] at hy
  rcases hy with ⟨p, hp, hyp⟩
  rcases hp with ⟨hb, hu⟩
  let b : E (m + 1) := p.1
  have hbP : b ∈ bigPrismSet m K w N := (mem_bigPrismSet m K w N b).mpr ?hbmem
  · rcases (mem_bigPrismSet m K w N b).mp hbP with ⟨x, hx, s, hs, hbs⟩
    -- inner w b = c
    have hbinner : inner ℝ w b = c := by
      -- from hp : p.1 ∈ midSliceSet
      rw [midSliceSet] at hb
      exact hb.2
    let t0 : ℝ := t0of m w c x
    have hs_eq : s = t0 := by
      have h1 : s ≤ t0 := by
        have this_eq : inner ℝ w (emb m x + s • w) = c := by
          calc
            inner ℝ w (emb m x + s • w) = inner ℝ w b := by rw [← hbs]
            _ = c := hbinner
        exact (inner_le_t0of_iff m hw x s c).mp (le_of_eq this_eq)
      have h2 : t0 ≤ s := by
        have this_eq : inner ℝ w (emb m x + s • w) = c := by
          calc
            inner ℝ w (emb m x + s • w) = inner ℝ w b := by rw [← hbs]
            _ = c := hbinner
        have hge : c ≤ inner ℝ w (emb m x + s • w) := ge_of_eq this_eq
        exact (le_inner_t0of_iff m hw x s c).mp hge
      exact le_antisymm h1 h2
    let u : ℝ := p.2
    have hy_gen : y = emb m x + (s + u) • w := by
      calc
        y = p.1 + p.2 • w := hyp.symm
        _ = b + u • w := by simp [b, u]
        _ = (emb m x + s • w) + u • w := by rw [hbs]
        _ = emb m x + (s + u) • w := by simp [add_smul, add_assoc]
    rw [slideUnion]
    by_cases hsplit : s + u ≤ (N : ℝ)
    · right
      constructor
      · exact (mem_bigPrismSet m K w N y).mpr ⟨x, hx, s + u, ⟨by nlinarith [hs.1, hu.1], hsplit⟩, hy_gen⟩
      · have hy_in : inner ℝ w (emb m x + (s + u) • w) = inner ℝ w y := by rw [← hy_gen]
        change c ≤ inner ℝ w y
        rw [← hy_in]
        rw [inner_w_gen, hs_eq]
        have hinner_c : inner ℝ w (emb m x) + t0 * ‖w‖ ^ 2 = c := by
          have h := inner_w_gen_t0 m hw c x
          rw [inner_w_gen] at h
          exact h
        have hterm : 0 ≤ u * ‖w‖ ^ 2 := mul_nonneg hu.1 (sq_nonneg ‖w‖)
        nlinarith
    · have hN_le : (N : ℝ) ≤ s + u := le_of_not_ge hsplit
      let v : ℝ := s + u - (N : ℝ)
      have hv0 : 0 ≤ v := by dsimp [v]; nlinarith
      have hvN : v ≤ (N : ℝ) := by dsimp [v]; nlinarith [hs.2, hu.2]
      left
      refine ⟨emb m x + v • w, ?_, ?_⟩
      · constructor
        · exact (mem_bigPrismSet m K w N (emb m x + v • w)).mpr ⟨x, hx, v, ⟨hv0, hvN⟩, rfl⟩
        · have hin : inner ℝ w (emb m x + v • w) =
              inner ℝ w (emb m x) + (s + u - (N : ℝ)) * ‖w‖ ^ 2 := by
            dsimp [v]
            exact inner_w_gen m x w (s + u - (N : ℝ))
          change inner ℝ w (emb m x + v • w) ≤ c
          rw [hin, hs_eq]
          have hinner_c : inner ℝ w (emb m x) + t0 * ‖w‖ ^ 2 = c := by
            have h := inner_w_gen_t0 m hw c x
            rw [inner_w_gen] at h
            exact h
          have hterm : (u - (N : ℝ)) * ‖w‖ ^ 2 ≤ 0 :=
            mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hu.2) (sq_nonneg ‖w‖)
          nlinarith
      · calc
          (emb m x + v • w) + (N : ℝ) • w = (emb m x + (s + u - (N : ℝ)) • w) + (N : ℝ) • w := by rfl
          _ = emb m x + (s + u) • w := by
            rw [sub_eq_add_neg]
            simp [add_smul, add_assoc]
          _ = y := hy_gen.symm
  · -- hbmem proof (b ∈ bigPrism from hp.1 ∈ midSlice)
    rw [midSliceSet] at hb
    exact hb.1

/-! ## μ-level mid-cut machinery -/

/-- `μ P = μ (P∩{≤c}) + μ (P∩{≥c})` when `w ≠ 0`. -/
theorem mu_split_le_ge (m : ℕ) (μ : ConvexBody (E (m + 1)) → ℝ)
    (hadd : ∀ A B C D : ConvexBody (E (m + 1)),
        (A : Set (E (m + 1))) = (C : Set (E (m + 1))) ∪ (D : Set (E (m + 1))) →
        (B : Set (E (m + 1))) = (C : Set (E (m + 1))) ∩ (D : Set (E (m + 1))) →
        μ A + μ B = μ C + μ D)
    (hsimple : ∀ K : ConvexBody (E (m + 1)), interior (K : Set (E (m + 1))) = ∅ → μ K = 0)
    (P : ConvexBody (E (m + 1))) {w : E (m + 1)} (hw : w ≠ 0) (c : ℝ)
    (hneLe : ((P : Set (E (m + 1))) ∩ {y | inner ℝ w y ≤ c}).Nonempty)
    (hneGe : ((P : Set (E (m + 1))) ∩ {y | c ≤ inner ℝ w y}).Nonempty)
    (hneEq : ((P : Set (E (m + 1))) ∩ {y | inner ℝ w y = c}).Nonempty) :
    μ P = μ (cutLeBody m P w c hneLe) + μ (cutGeBody m P w c hneGe) := by
  have hU : (P : Set (E (m + 1))) =
      ((cutLeBody m P w c hneLe : Set (E (m + 1))) ∪ (cutGeBody m P w c hneGe : Set (E (m + 1)))) :=
    body_split_le_ge m P w c hneLe hneGe
  have hI : ((cutEqBody m P w c hneEq : Set (E (m + 1)))) =
      ((cutLeBody m P w c hneLe : Set (E (m + 1))) ∩ (cutGeBody m P w c hneGe : Set (E (m + 1)))) := by
    rw [cutEqBody_coe]
    exact (body_inter_le_ge m P w c hneLe hneGe).symm
  have hie : μ P + μ (cutEqBody m P w c hneEq) =
      μ (cutLeBody m P w c hneLe) + μ (cutGeBody m P w c hneGe) :=
    hadd P (cutEqBody m P w c hneEq) (cutLeBody m P w c hneLe) (cutGeBody m P w c hneGe) hU hI
  have hB : interior ((cutEqBody m P w c hneEq : Set (E (m + 1)))) = ∅ :=
    interior_cutEq_empty m P hw c hneEq
  have hB0 : μ (cutEqBody m P w c hneEq) = 0 := hsimple _ hB
  linarith

/-- The interior of the top face `K + N·w` is empty. -/
theorem interior_top_face_empty (m : ℕ) (K : ConvexBody (E m)) {w : E (m + 1)}
    (hw : w (Fin.last m) ≠ 0) (N : ℕ) :
    interior ((fun x : E m => emb m x + (N : ℝ) • w) '' (K : Set (E m))) = ∅ := by
  have hsub : (fun x : E m => emb m x + (N : ℝ) • w) '' (K : Set (E m)) ⊆
      {y : E (m + 1) | lastCoord m y = (N : ℝ) * w (Fin.last m)} := by
    rintro y ⟨x, hx, hy⟩
    rw [← hy]
    change lastCoord m (emb m x + (N : ℝ) • w) = (N : ℝ) * w (Fin.last m)
    rw [lastCoord_add, lastCoord_smul, lastCoord_emb]
    change 0 + (N : ℝ) * w (Fin.last m) = (N : ℝ) * w (Fin.last m)
    simp
  have hL : interior {y : E (m + 1) | lastCoord m y = (N : ℝ) * w (Fin.last m)} = ∅ :=
    interior_lastCoord_level_empty m ((N : ℝ) * w (Fin.last m))
  apply subset_antisymm
  · exact (interior_mono hsub).trans (by simpa [hL])
  · exact empty_subset _

/-- The intersection of the slid-lower and upper pieces lies in the flat top face. -/
theorem slid_lower_inter_upper_subset_top (m : ℕ) (K : ConvexBody (E m)) {w : E (m + 1)}
    (hw : w (Fin.last m) ≠ 0) (c : ℝ) (N : ℕ) :
    (((fun z : E (m + 1) => z + (N : ℝ) • w) ''
      (bigPrismSet m K w N ∩ {y | inner ℝ w y ≤ c})) ∩
     (bigPrismSet m K w N ∩ {y | c ≤ inner ℝ w y})) ⊆
      (fun x : E m => emb m x + (N : ℝ) • w) '' (K : Set (E m)) := by
  intro y hy
  rcases hy.1 with ⟨z, hz, hyz⟩
  rcases hz.1 with ⟨x, hx, t, ht, hzt⟩
  rcases hy.2 with ⟨hyP, hyge⟩
  -- y = z + N w = emb x + (t+N) w; also y ∈ bigPrism
  have hy_gen : y = emb m x + (t + (N : ℝ)) • w := by
    calc
      y = z + (N : ℝ) • w := hyz.symm
      _ = (emb m x + t • w) + (N : ℝ) • w := by rw [hzt]
      _ = emb m x + (t + (N : ℝ)) • w := by simp [add_smul, add_assoc]
  rcases (mem_bigPrismSet m K w N y).mp hyP with ⟨x', hx', t', ht', hy_gen'⟩
  have hunique := segPrism_unique (m := m) (K := K) hw hy_gen hy_gen'
  -- t + N = t' ≤ N forces t = 0
  have ht0 : t = 0 := by
    have htN : t + (N : ℝ) = t' := hunique.1
    have ht' : t' ≤ (N : ℝ) := ht'.2
    nlinarith [ht.1]
  refine ⟨x, hx, ?_⟩
  change emb m x + (N : ℝ) • w = y
  rw [hy_gen, ht0]
  simp


/-- `slideUnion = cylFromSet (midSliceSet)`: the slide identity (both inclusions). -/
theorem slideUnion_eq_cyl (m : ℕ) (K : ConvexBody (E m)) {w : E (m + 1)}
    (hw : w (Fin.last m) ≠ 0) (c : ℝ) (N : ℕ)
    (hKlo : ∀ x : E m, x ∈ (K : Set (E m)) → inner ℝ w (emb m x) ≤ c)
    (hKhi : ∀ x : E m, x ∈ (K : Set (E m)) → c ≤ inner ℝ w (emb m x + (N : ℝ) • w)) :
    slideUnion m K w c N = cylFromSet m (midSliceSet m K w c N) w N :=
  subset_antisymm (slideUnion_subset_cyl m K hw c N hKlo hKhi)
    (cyl_subset_slideUnion m K hw c N)

/-- The bottom `≤ c` cut of the tall prism is nonempty. -/
theorem cutLe_nonempty (m : ℕ) (K : ConvexBody (E m)) (w : E (m + 1)) (c : ℝ) (N : ℕ)
    (hKlo : ∀ x : E m, x ∈ (K : Set (E m)) → inner ℝ w (emb m x) ≤ c) :
    ((bigPrismBody m K w N : Set (E (m + 1))) ∩ {y | inner ℝ w y ≤ c}).Nonempty := by
  rcases K.nonempty with ⟨x0, hx0⟩
  refine ⟨emb m x0, ?_, hKlo x0 hx0⟩
  rw [bigPrismBody_coe]
  exact (mem_bigPrismSet m K w N (emb m x0)).mpr
    ⟨x0, hx0, 0, ⟨le_rfl, by exact_mod_cast (Nat.zero_le N)⟩, by simp⟩

/-- The top `≥ c` cut of the tall prism is nonempty. -/
theorem cutGe_nonempty (m : ℕ) (K : ConvexBody (E m)) (w : E (m + 1)) (c : ℝ) (N : ℕ)
    (hKhi : ∀ x : E m, x ∈ (K : Set (E m)) → c ≤ inner ℝ w (emb m x + (N : ℝ) • w)) :
    ((bigPrismBody m K w N : Set (E (m + 1))) ∩ {y | c ≤ inner ℝ w y}).Nonempty := by
  rcases K.nonempty with ⟨x0, hx0⟩
  refine ⟨emb m x0 + (N : ℝ) • w, ?_, hKhi x0 hx0⟩
  rw [bigPrismBody_coe]
  exact (mem_bigPrismSet m K w N (emb m x0 + (N : ℝ) • w)).mpr
    ⟨x0, hx0, (N : ℝ), ⟨by exact_mod_cast (Nat.zero_le N), le_rfl⟩, rfl⟩

/-- The mid-slice `P ∩ {⟨w,·⟩ = c}` of the tall prism is nonempty (given the level
bracketing `hKlo`/`hKhi`). -/
theorem cutEq_nonempty (m : ℕ) (K : ConvexBody (E m)) {w : E (m + 1)}
    (hw : w (Fin.last m) ≠ 0) (c : ℝ) (N : ℕ)
    (hKlo : ∀ x : E m, x ∈ (K : Set (E m)) → inner ℝ w (emb m x) ≤ c)
    (hKhi : ∀ x : E m, x ∈ (K : Set (E m)) → c ≤ inner ℝ w (emb m x + (N : ℝ) • w)) :
    ((bigPrismBody m K w N : Set (E (m + 1))) ∩ {y | inner ℝ w y = c}).Nonempty := by
  rcases K.nonempty with ⟨x0, hx0⟩
  let t0 := t0of m w c x0
  have ht0 : t0 ∈ Set.Icc (0 : ℝ) (N : ℝ) :=
    t0of_mem_of_le_ge m hw x0 c N (hKlo x0 hx0) (hKhi x0 hx0)
  refine ⟨emb m x0 + t0 • w, ?_, ?_⟩
  · rw [bigPrismBody_coe]
    exact (mem_bigPrismSet m K w N (emb m x0 + t0 • w)).mpr ⟨x0, hx0, t0, ht0, rfl⟩
  · exact inner_w_gen_t0 m hw c x0

/-- The mid-slice set is nonempty. -/
theorem midSlice_nonempty (m : ℕ) (K : ConvexBody (E m)) {w : E (m + 1)}
    (hw : w (Fin.last m) ≠ 0) (c : ℝ) (N : ℕ)
    (hKlo : ∀ x : E m, x ∈ (K : Set (E m)) → inner ℝ w (emb m x) ≤ c)
    (hKhi : ∀ x : E m, x ∈ (K : Set (E m)) → c ≤ inner ℝ w (emb m x + (N : ℝ) • w)) :
    (midSliceSet m K w c N).Nonempty := by
  rcases K.nonempty with ⟨x0, hx0⟩
  let t0 := t0of m w c x0
  have ht0 : t0 ∈ Set.Icc (0 : ℝ) (N : ℝ) :=
    t0of_mem_of_le_ge m hw x0 c N (hKlo x0 hx0) (hKhi x0 hx0)
  refine ⟨emb m x0 + t0 • w, ?_⟩
  rw [midSliceSet]
  constructor
  · exact (mem_bigPrismSet m K w N (emb m x0 + t0 • w)).mpr ⟨x0, hx0, t0, ht0, rfl⟩
  · exact inner_w_gen_t0 m hw c x0

/-- The mid-slice is convex. -/
theorem midSlice_convex (m : ℕ) (K : ConvexBody (E m)) (w : E (m + 1)) (c : ℝ) (N : ℕ) :
    Convex ℝ (midSliceSet m K w c N) := by
  unfold midSliceSet bigPrismSet
  exact (segPrismSet_convex m K w 0 (N : ℝ)).inter (convex_hpPlane w c)

/-- The mid-slice is compact. -/
theorem midSlice_compact (m : ℕ) (K : ConvexBody (E m)) (w : E (m + 1)) (c : ℝ) (N : ℕ) :
    IsCompact (midSliceSet m K w c N) := by
  unfold midSliceSet bigPrismSet
  exact (segPrismSet_compact m K w 0 (N : ℝ)).inter_right (isClosed_hpPlane w c)

/-- The cylinder-from-set is convex when the base set is. -/
theorem cylFromSet_convex (m : ℕ) {B : Set (E (m + 1))} (hB : Convex ℝ B)
    (w : E (m + 1)) (N : ℕ) : Convex ℝ (cylFromSet m B w N) := by
  intro y hy z hz a b ha hb hab
  rw [mem_cylFromSet] at hy hz
  rcases hy with ⟨b1, hb1, u1, hu1, rfl⟩
  rcases hz with ⟨b2, hb2, u2, hu2, rfl⟩
  rw [mem_cylFromSet]
  refine ⟨a • b1 + b • b2, hB hb1 hb2 ha hb hab, a • u1 + b • u2,
    (convex_Icc (0 : ℝ) (N : ℝ)) hu1 hu2 ha hb hab, ?_⟩
  calc
    a • (b1 + u1 • w) + b • (b2 + u2 • w)
        = (a • b1 + b • b2) + (a • (u1 • w) + b • (u2 • w)) := by
          rw [smul_add, smul_add]
          abel
    _ = (a • b1 + b • b2) + (a • u1 + b • u2) • w := by
          rw [smul_smul, smul_smul]
          simp only [smul_eq_mul]
          rw [← add_smul]

/-- The cylinder-from-set is compact when the base is. -/
theorem cylFromSet_compact (m : ℕ) (B : Set (E (m + 1))) (hB : IsCompact B)
    (w : E (m + 1)) (N : ℕ) : IsCompact (cylFromSet m B w N) := by
  have hf : Continuous (fun p : E (m + 1) × ℝ => p.1 + p.2 • w) := by
    have h1 : Continuous (fun p : E (m + 1) × ℝ => p.1) := continuous_fst
    have h2 : Continuous (fun p : E (m + 1) × ℝ => p.2 • w) :=
      Continuous.smul continuous_snd continuous_const
    exact h1.add h2
  simpa [cylFromSet] using (hB.prod isCompact_Icc).image hf

/-- The cylinder-from-set is nonempty when the base is. -/
theorem cylFromSet_nonempty (m : ℕ) (B : Set (E (m + 1))) (hB : B.Nonempty)
    (w : E (m + 1)) (N : ℕ) : (cylFromSet m B w N).Nonempty := by
  rcases hB with ⟨b, hb⟩
  refine ⟨b + 0 • w, ?_⟩
  rw [mem_cylFromSet]
  refine ⟨b, hb, 0, ⟨le_rfl, by exact_mod_cast (Nat.zero_le N)⟩, by simp⟩

/-- The reassembled body: the cylinder over the mid-slice `B₀ = P ∩ {⟨w,·⟩ = c}`
in direction `w` of height `N`. -/
def midCylBody (m : ℕ) (K : ConvexBody (E m)) {w : E (m + 1)}
    (hw : w (Fin.last m) ≠ 0) (c : ℝ) (N : ℕ)
    (hKlo : ∀ x : E m, x ∈ (K : Set (E m)) → inner ℝ w (emb m x) ≤ c)
    (hKhi : ∀ x : E m, x ∈ (K : Set (E m)) → c ≤ inner ℝ w (emb m x + (N : ℝ) • w)) :
    ConvexBody (E (m + 1)) :=
  ⟨cylFromSet m (midSliceSet m K w c N) w N,
    cylFromSet_convex m (midSlice_convex m K w c N) w N,
    cylFromSet_compact m (midSliceSet m K w c N) (midSlice_compact m K w c N) w N,
    cylFromSet_nonempty m (midSliceSet m K w c N)
      (midSlice_nonempty m K hw c N hKlo hKhi) w N⟩

@[simp] theorem midCylBody_coe (m : ℕ) (K : ConvexBody (E m)) {w : E (m + 1)}
    (hw : w (Fin.last m) ≠ 0) (c : ℝ) (N : ℕ)
    (hKlo : ∀ x : E m, x ∈ (K : Set (E m)) → inner ℝ w (emb m x) ≤ c)
    (hKhi : ∀ x : E m, x ∈ (K : Set (E m)) → c ≤ inner ℝ w (emb m x + (N : ℝ) • w)) :
    (midCylBody m K hw c N hKlo hKhi : Set (E (m + 1))) =
      cylFromSet m (midSliceSet m K w c N) w N := rfl


/-- The intersection of the slid lower piece with the upper piece (as ConvexBody carriers)
is a subset of the flat top face, hence has empty interior. -/
theorem slidPieces_interior_empty (m : ℕ) (K : ConvexBody (E m)) {w : E (m + 1)}
    (hw : w (Fin.last m) ≠ 0) (c : ℝ) (N : ℕ)
    (hneLe : ((bigPrismBody m K w N : Set (E (m + 1))) ∩ {y | inner ℝ w y ≤ c}).Nonempty)
    (hneGe : ((bigPrismBody m K w N : Set (E (m + 1))) ∩ {y | c ≤ inner ℝ w y}).Nonempty) :
    interior ((transBody (cutLeBody m (bigPrismBody m K w N) w c hneLe) ((N : ℝ) • w) :
        Set (E (m + 1))) ∩
      (cutGeBody m (bigPrismBody m K w N) w c hneGe : Set (E (m + 1)))) = ∅ := by
  have hsub :
      ((transBody (cutLeBody m (bigPrismBody m K w N) w c hneLe) ((N : ℝ) • w) :
          Set (E (m + 1))) ∩
        (cutGeBody m (bigPrismBody m K w N) w c hneGe : Set (E (m + 1)))) ⊆
        (fun x : E m => emb m x + (N : ℝ) • w) '' (K : Set (E m)) := by
    rw [transBody_coe, cutLeBody_coe, cutGeBody_coe, bigPrismBody_coe]
    exact slid_lower_inter_upper_subset_top m K hw c N
  have htop : interior ((fun x : E m => emb m x + (N : ℝ) • w) '' (K : Set (E m))) = ∅ :=
    interior_top_face_empty m K hw N
  apply subset_antisymm
  · exact (interior_mono hsub).trans (by simpa [htop])
  · exact empty_subset _


theorem bigPrism_mu_zero_of_midcyl
    (m : ℕ) (μ : ConvexBody (E (m + 1)) → ℝ)
    (hcont : Continuous μ)
    (hadd : ∀ A B C D : ConvexBody (E (m + 1)),
        (A : Set (E (m + 1))) = (C : Set (E (m + 1))) ∪ (D : Set (E (m + 1))) →
        (B : Set (E (m + 1))) = (C : Set (E (m + 1))) ∩ (D : Set (E (m + 1))) →
        μ A + μ B = μ C + μ D)
    (htrans : ∀ A B : ConvexBody (E (m + 1)), ∀ t : E (m + 1),
        (B : Set (E (m + 1))) = (fun x : E (m + 1) => x + t) '' (A : Set (E (m + 1))) → μ A = μ B)
    (hsimple : ∀ K : ConvexBody (E (m + 1)), interior (K : Set (E (m + 1))) = ∅ → μ K = 0)
    (K : ConvexBody (E m)) {w : E (m + 1)} (hw : w (Fin.last m) ≠ 0)
    (c : ℝ) (N : ℕ) (hN : 0 < N)
    (hKlo : ∀ x : E m, x ∈ (K : Set (E m)) → inner ℝ w (emb m x) ≤ c)
    (hKhi : ∀ x : E m, x ∈ (K : Set (E m)) → c ≤ inner ℝ w (emb m x + (N : ℝ) • w))
    (hcylC : μ (midCylBody m K hw c N hKlo hKhi) = 0) :
    μ (prismBody m K w) = 0 := by
  have hneLe : ((bigPrismBody m K w N : Set (E (m + 1))) ∩ {y | inner ℝ w y ≤ c}).Nonempty :=
    cutLe_nonempty m K w c N hKlo
  have hneGe : ((bigPrismBody m K w N : Set (E (m + 1))) ∩ {y | c ≤ inner ℝ w y}).Nonempty :=
    cutGe_nonempty m K w c N hKhi
  have hneEq : ((bigPrismBody m K w N : Set (E (m + 1))) ∩ {y | inner ℝ w y = c}).Nonempty :=
    cutEq_nonempty m K hw c N hKlo hKhi
  let ZLe : ConvexBody (E (m + 1)) := cutLeBody m (bigPrismBody m K w N) w c hneLe
  let ZGe : ConvexBody (E (m + 1)) := cutGeBody m (bigPrismBody m K w N) w c hneGe
  let Cbody : ConvexBody (E (m + 1)) := midCylBody m K hw c N hKlo hKhi
  have hmuZ : μ (bigPrismBody m K w N) = μ ZLe + μ ZGe := by
    have h0 := mu_split_le_ge m μ hadd hsimple (bigPrismBody m K w N) (w := w)
      (w_ne_zero_of_last m hw) c hneLe hneGe hneEq
    simpa [ZLe, ZGe] using h0
  have hmuTrans : μ ZLe = μ (transBody ZLe ((N : ℝ) • w)) := by
    exact htrans ZLe (transBody ZLe ((N : ℝ) • w)) ((N : ℝ) • w) (by simp)
  let transZLe : ConvexBody (E (m + 1)) := transBody ZLe ((N : ℝ) • w)
  have hcov01 : (Cbody : Set (E (m + 1))) =
      (transZLe : Set (E (m + 1))) ∪ (ZGe : Set (E (m + 1))) := by
    dsimp [Cbody, transZLe, ZLe, ZGe]
    change cylFromSet m (midSliceSet m K w c N) w N =
      (transBody (cutLeBody m (bigPrismBody m K w N) w c hneLe) ((N : ℝ) • w) :
          Set (E (m + 1))) ∪
      (cutGeBody m (bigPrismBody m K w N) w c hneGe : Set (E (m + 1)))
    rw [← slideUnion_eq_cyl m K hw c N hKlo hKhi]
    unfold slideUnion
    rw [transBody_coe, cutLeBody_coe, cutGeBody_coe, bigPrismBody_coe]
  let A : Bool → ConvexBody (E (m + 1)) := fun b =>
    match b with | false => transZLe | true => ZGe
  have hcov : (Cbody : Set (E (m + 1))) = ⋃ b : Bool, (A b : Set (E (m + 1))) := by
    rw [hcov01]
    ext y
    simp [A, Bool.exists_bool]
  have hpair : ∀ b c : Bool, b ≠ c →
      interior (((A b : Set (E (m + 1)))) ∩ ((A c : Set (E (m + 1))))) = ∅ := by
    intro b c hbc
    cases b <;> cases c
    · exfalso
      exact hbc rfl
    · have hAf : (A false : Set (E (m + 1))) = (transZLe : Set (E (m + 1))) := by simp [A]
      have hAt : (A true : Set (E (m + 1))) = (ZGe : Set (E (m + 1))) := by simp [A]
      rw [hAf, hAt]
      dsimp [transZLe, ZLe, ZGe]
      exact slidPieces_interior_empty m K hw c N hneLe hneGe
    · have hAf : (A false : Set (E (m + 1))) = (transZLe : Set (E (m + 1))) := by simp [A]
      have hAt : (A true : Set (E (m + 1))) = (ZGe : Set (E (m + 1))) := by simp [A]
      rw [hAt, hAf]
      rw [inter_comm]
      dsimp [transZLe, ZLe, ZGe]
      exact slidPieces_interior_empty m K hw c N hneLe hneGe
    · exfalso
      exact hbc rfl
  have hdiss := dissection_additivity (V := E (m + 1)) μ hcont hadd hsimple Cbody A hcov hpair
  have hsum : (∑ b : Bool, μ (A b)) = μ ZGe + μ transZLe := by
    simp [A]
  have hmuC : μ Cbody = μ ZGe + μ transZLe := by
    rw [hsum] at hdiss
    exact hdiss
  have hmuZ0 : μ (bigPrismBody m K w N) = 0 := by
    calc
      μ (bigPrismBody m K w N) = μ ZLe + μ ZGe := hmuZ
      _ = μ (transBody ZLe ((N : ℝ) • w)) + μ ZGe := by rw [hmuTrans]
      _ = μ ZGe + μ (transBody ZLe ((N : ℝ) • w)) := by rw [add_comm]
      _ = μ Cbody := by
        rw [← hmuC]
      _ = 0 := hcylC
  have hbig : μ (bigPrismBody m K w N) = (N : ℝ) • μ (prismBody m K w) :=
    mu_bigPrism m μ hcont hadd htrans hsimple K hw N hN
  have hprod : (N : ℝ) * μ (prismBody m K w) = 0 := by
    rw [hbig] at hmuZ0
    simpa [smul_eq_mul] using hmuZ0
  have hNne : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  rcases mul_eq_zero.mp hprod with h | h
  · exact False.elim (hNne h)
  · exact h



/-- Points of the mid-slice lie at level `c`. -/
lemma midSlice_mem_level (m : ℕ) (K : ConvexBody (E m)) (w : E (m + 1)) (c : ℝ) (N : ℕ)
    {y : E (m + 1)} (hy : y ∈ midSliceSet m K w c N) : inner ℝ w y = c := by
  rw [midSliceSet] at hy
  exact hy.2

/-- `ρ.symm` kills the difference of two points on the level hyperplane `{inner w = c}`:
its last coordinate is zero (that difference lies in the linear hyperplane `wᗮ`). -/
lemma lastCoord_symm_sub (m : ℕ) {w : E (m + 1)}
    (ρ : E (m + 1) ≃ₗᵢ[ℝ] E (m + 1)) (u : E (m + 1))
    (hρu : ρ (eLast m) = u) (hu : u = ‖w‖⁻¹ • w)
    {c : ℝ} {x y : E (m + 1)} (hx : inner ℝ w x = c) (hy : inner ℝ w y = c) :
    lastCoord m (ρ.symm (x - y)) = 0 := by
  have hinner : inner ℝ w (x - y) = 0 := by
    rw [inner_sub_right, hx, hy]
    ring
  have hin : inner ℝ u (x - y) = 0 := by
    rw [hu]
    rw [real_inner_smul_left]
    rw [hinner]
    ring
  have hlc := lastCoord_of_lie m ρ u hρu (x - y)
  rw [hlc]
  rw [real_inner_comm]
  exact hin

/-- The translated reassembled cylinder equals the `hcyl`-right-cylinder in the frame `ρ`
over the base `K0` (a translate of the mid-slice viewed through `ρ`). -/
lemma transMidCyl_carrier_eq
    (m : ℕ) (K : ConvexBody (E m)) {w : E (m + 1)} (hw : w (Fin.last m) ≠ 0)
    (c : ℝ) (N : ℕ)
    (hKlo : ∀ x : E m, x ∈ (K : Set (E m)) → inner ℝ w (emb m x) ≤ c)
    (hKhi : ∀ x : E m, x ∈ (K : Set (E m)) → c ≤ inner ℝ w (emb m x + (N : ℝ) • w))
    (ρ : E (m + 1) ≃ₗᵢ[ℝ] E (m + 1)) (u : E (m + 1))
    (hρu : ρ (eLast m) = u) (hu : u = ‖w‖⁻¹ • w)
    (p0 : E (m + 1)) (hp0 : p0 ∈ midSliceSet m K w c N)
    (B : Set (E (m + 1)))
    (hB : B = (fun b : E (m + 1) => b - p0) '' midSliceSet m K w c N)
    (K0 : ConvexBody (E m))
    (hK0 : (K0 : Set (E m)) = (fun b : E (m + 1) => dropLast m (ρ.symm b)) '' B) :
    (transBody (midCylBody m K hw c N hKlo hKhi) (-p0) : Set (E (m + 1))) =
      {y : E (m + 1) | dropLast m (ρ.symm y) ∈ (K0 : Set (E m)) ∧
        lastCoord m (ρ.symm y) ∈ Set.Icc (0 : ℝ) ((N : ℝ) * ‖w‖)} := by
  have hwnz : w ≠ 0 := w_ne_zero_of_last m hw
  have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hwnz
  have hw_eq : w = ‖w‖ • u := by
    rw [hu]
    rw [smul_smul]
    rw [mul_inv_cancel₀ (ne_of_gt hwpos)]
    simp
  have hsymmu : ρ.symm u = eLast m := by
    have h' := congrArg ρ.symm hρu
    simpa using h'.symm
  have hρw : ρ.symm w = ‖w‖ • eLast m := by
    conv_lhs => rw [hw_eq]
    simp [hsymmu]
  ext y
  constructor
  · intro hy
    rw [transBody_coe] at hy
    rcases hy with ⟨x, hx, hyx⟩
    change x ∈ cylFromSet m (midSliceSet m K w c N) w N at hx
    rw [mem_cylFromSet] at hx
    rcases hx with ⟨b0, hb0, t, ht, hx_eq⟩
    have hy_form : y = (b0 - p0) + t • w := by
      calc
        y = x + (-p0) := hyx.symm
        _ = (b0 + t • w) + (-p0) := by rw [hx_eq]
        _ = (b0 - p0) + t • w := by abel
    have hlc0 : lastCoord m (ρ.symm (b0 - p0)) = 0 := by
      exact lastCoord_symm_sub m ρ u hρu hu (midSlice_mem_level m K w c N hb0)
        (midSlice_mem_level m K w c N hp0)
    have hsymm : ρ.symm y = ρ.symm (b0 - p0) + (t * ‖w‖) • eLast m := by
      calc
        ρ.symm y = ρ.symm ((b0 - p0) + t • w) := by rw [hy_form]
        _ = ρ.symm (b0 - p0) + ρ.symm (t • w) := by simp
        _ = ρ.symm (b0 - p0) + t • ρ.symm w := by simp
        _ = ρ.symm (b0 - p0) + t • (‖w‖ • eLast m) := by rw [hρw]
        _ = ρ.symm (b0 - p0) + (t * ‖w‖) • eLast m := by rw [smul_smul]
    have hdrop : dropLast m (ρ.symm y) = dropLast m (ρ.symm (b0 - p0)) := by
      rw [hsymm]
      simp
    constructor
    · rw [hK0]
      refine ⟨b0 - p0, ?_, hdrop.symm⟩
      rw [hB]
      exact ⟨b0, hb0, rfl⟩
    · rw [hsymm]
      rw [lastCoord_add, lastCoord_smul]
      rw [hlc0, lastCoord_eLast]
      simp
      constructor
      · exact mul_nonneg ht.1 (norm_nonneg w)
      · exact mul_le_mul_of_nonneg_right ht.2 (norm_nonneg w)
  · intro hy
    rw [hK0] at hy
    rcases hy with ⟨hd, hs⟩
    rcases hd with ⟨b, hb, hd_eq⟩
    rw [hB] at hb
    rcases hb with ⟨b0, hb0, hb_eq⟩
    let s : ℝ := lastCoord m (ρ.symm y)
    let t : ℝ := s / ‖w‖
    have ht0 : 0 ≤ t := by
      dsimp [t]
      exact div_nonneg hs.1 (le_of_lt hwpos)
    have htN : t ≤ (N : ℝ) := by
      dsimp [t]
      exact (div_le_iff₀ hwpos).mpr (by simpa [s] using hs.2)
    have hb_eq' : b0 - p0 = b := by simpa using hb_eq
    have hlc_b : lastCoord m (ρ.symm b) = 0 := by
      rw [← hb_eq']
      exact lastCoord_symm_sub m ρ u hρu hu (midSlice_mem_level m K w c N hb0)
        (midSlice_mem_level m K w c N hp0)
    have hd_eq' : dropLast m (ρ.symm b) = dropLast m (ρ.symm y) := by simpa using hd_eq
    have hb_emb : ρ.symm b = emb m (dropLast m (ρ.symm y)) := by
      calc
        ρ.symm b = emb m (dropLast m (ρ.symm b)) :=
          (emb_dropLast_eq_self_of_lastCoord_zero hlc_b).symm
        _ = emb m (dropLast m (ρ.symm y)) := by rw [hd_eq']
    have hsymm : ρ.symm y = ρ.symm b + s • eLast m := by
      calc
        ρ.symm y = emb m (dropLast m (ρ.symm y)) + s • eLast m :=
          (emb_dropLast_add_last m (ρ.symm y)).symm
        _ = ρ.symm b + s • eLast m := by rw [← hb_emb]
    have hc := congrArg ρ hsymm
    have hc' : y = b + s • u := by
      simpa [hρu] using hc
    have hsmu : s • u = (s / ‖w‖) • w := by
      rw [hu]
      rw [smul_smul]
      rw [div_eq_mul_inv]
    have hmain : y = b + (s / ‖w‖) • w := by
      calc
        y = b + s • u := hc'
        _ = b + (s / ‖w‖) • w := by rw [hsmu]
    rw [transBody_coe]
    refine ⟨b0 + t • w, ?_, ?_⟩
    · change b0 + t • w ∈ cylFromSet m (midSliceSet m K w c N) w N
      rw [mem_cylFromSet]
      exact ⟨b0, hb0, t, ⟨ht0, htN⟩, rfl⟩
    · calc
        (b0 + t • w) + (-p0) = (b0 - p0) + t • w := by abel
        _ = b + t • w := by rw [hb_eq']
        _ = y := by simpa [t] using hmain.symm



/-- The `ρ`-frame right cylinder vanishes: the reassembled cylinder `midCylBody` has value zero. -/
theorem mu_midCyl_zero
    (m : ℕ) (μ : ConvexBody (E (m + 1)) → ℝ)
    (hcont : Continuous μ)
    (hadd : ∀ A B C D : ConvexBody (E (m + 1)),
        (A : Set (E (m + 1))) = (C : Set (E (m + 1))) ∪ (D : Set (E (m + 1))) →
        (B : Set (E (m + 1))) = (C : Set (E (m + 1))) ∩ (D : Set (E (m + 1))) →
        μ A + μ B = μ C + μ D)
    (htrans : ∀ A B : ConvexBody (E (m + 1)), ∀ t : E (m + 1),
        (B : Set (E (m + 1))) = (fun x : E (m + 1) => x + t) '' (A : Set (E (m + 1))) → μ A = μ B)
    (hsimple : ∀ K : ConvexBody (E (m + 1)), interior (K : Set (E (m + 1))) = ∅ → μ K = 0)
    (hcyl : ∀ (ρ : E (m + 1) ≃ₗᵢ[ℝ] E (m + 1)) (K0 : ConvexBody (E m)) (h : ℝ), 0 ≤ h →
        ∀ Q : ConvexBody (E (m + 1)),
          (Q : Set (E (m + 1))) = {y : E (m + 1) |
            dropLast m (ρ.symm y) ∈ (K0 : Set (E m)) ∧
              lastCoord m (ρ.symm y) ∈ Set.Icc (0 : ℝ) h} → μ Q = 0)
    (K : ConvexBody (E m)) {w : E (m + 1)} (hw : w (Fin.last m) ≠ 0)
    (c : ℝ) (N : ℕ)
    (hKlo : ∀ x : E m, x ∈ (K : Set (E m)) → inner ℝ w (emb m x) ≤ c)
    (hKhi : ∀ x : E m, x ∈ (K : Set (E m)) → c ≤ inner ℝ w (emb m x + (N : ℝ) • w)) :
    μ (midCylBody m K hw c N hKlo hKhi) = 0 := by
  have hwnz : w ≠ 0 := w_ne_zero_of_last m hw
  have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hwnz
  rcases midSlice_nonempty m K hw c N hKlo hKhi with ⟨p0, hp0⟩
  let u : E (m + 1) := ‖w‖⁻¹ • w
  rcases exists_lie_unit_to_unit (V := E (m + 1)) (eLast m) (norm_eLast m) w hwnz with ⟨ρ, hρ⟩
  have hρu : ρ (eLast m) = u := by simpa [u] using hρ
  let B : Set (E (m + 1)) := (fun b : E (m + 1) => b - p0) '' midSliceSet m K w c N
  have hBconv : Convex ℝ B := by
    dsimp [B]
    intro y hy z hz a d ha hd had
    rcases hy with ⟨b, hb, hy_eq⟩
    rcases hz with ⟨c0, hc0, hz_eq⟩
    dsimp at hy_eq hz_eq
    rw [← hy_eq, ← hz_eq]
    refine ⟨a • b + d • c0, midSlice_convex m K w c N hb hc0 ha hd had, ?_⟩
    calc
      (a • b + d • c0) - p0 = (a • b + d • c0) + (a + d) • (-p0) := by
        have hpm : (a + d) • (-p0) = -p0 := by
          rw [had]
          simp
        rw [sub_eq_add_neg]
        rw [hpm]
      _ = (a • b + d • c0) + (a • (-p0) + d • (-p0)) := by rw [add_smul]
      _ = (a • b + a • (-p0)) + (d • c0 + d • (-p0)) := by abel
      _ = a • (b + (-p0)) + d • (c0 + (-p0)) := by
        rw [smul_add, smul_add]
      _ = a • (b - p0) + d • (c0 - p0) := by
        rw [sub_eq_add_neg, sub_eq_add_neg]
  have hBcpt : IsCompact B := by
    dsimp [B]
    exact IsCompact.image (midSlice_compact m K w c N) (by fun_prop)
  have hBne : B.Nonempty := by
    refine ⟨p0 - p0, ?_⟩
    dsimp [B]
    exact ⟨p0, hp0, rfl⟩
  let K0car : Set (E m) := (fun b : E (m + 1) => dropLast m (ρ.symm b)) '' B
  have hK0conv : Convex ℝ K0car := by
    let f : E (m + 1) →ₗ[ℝ] E m :=
      { toFun := fun b => dropLast m (ρ.symm b)
        map_add' := by intro x y; simp
        map_smul' := by intro a x; simp }
    change Convex ℝ (f '' B)
    exact hBconv.linear_image f
  have hK0cpt : IsCompact K0car := by
    change IsCompact ((fun b : E (m + 1) => dropLast m (ρ.symm b)) '' B)
    let L : E (m + 1) →ₗ[ℝ] E m :=
      { toFun := dropLast m
        map_add' := by intro x y; simp
        map_smul' := by intro a x; simp }
    have hL : Continuous (fun x : E (m + 1) => L x) := L.continuous_of_finiteDimensional
    have hρcont : Continuous (fun b : E (m + 1) => ρ.symm b) := by fun_prop
    have hf : Continuous (fun b : E (m + 1) => dropLast m (ρ.symm b)) := by
      exact hL.comp hρcont
    exact IsCompact.image hBcpt hf
  have hK0ne : K0car.Nonempty := by
    rcases hBne with ⟨b, hb⟩
    refine ⟨dropLast m (ρ.symm b), ?_⟩
    exact ⟨b, hb, rfl⟩
  let K0 : ConvexBody (E m) := ⟨K0car, hK0conv, hK0cpt, hK0ne⟩
  have hh : 0 ≤ (N : ℝ) * ‖w‖ := mul_nonneg (by exact_mod_cast (Nat.zero_le N)) (norm_nonneg w)
  have hcar : (transBody (midCylBody m K hw c N hKlo hKhi) (-p0) : Set (E (m + 1))) =
      {y : E (m + 1) | dropLast m (ρ.symm y) ∈ (K0 : Set (E m)) ∧
        lastCoord m (ρ.symm y) ∈ Set.Icc (0 : ℝ) ((N : ℝ) * ‖w‖)} := by
    change (transBody (midCylBody m K hw c N hKlo hKhi) (-p0) : Set (E (m + 1))) =
      {y : E (m + 1) | dropLast m (ρ.symm y) ∈ K0car ∧
        lastCoord m (ρ.symm y) ∈ Set.Icc (0 : ℝ) ((N : ℝ) * ‖w‖)}
    exact transMidCyl_carrier_eq m K hw c N hKlo hKhi ρ u hρu (by rfl) p0 hp0 B (by rfl) K0 (by rfl)
  have hcyl0 := hcyl ρ K0 ((N : ℝ) * ‖w‖) hh (transBody (midCylBody m K hw c N hKlo hKhi) (-p0)) hcar
  have htr : μ (midCylBody m K hw c N hKlo hKhi) =
      μ (transBody (midCylBody m K hw c N hKlo hKhi) (-p0)) := by
    exact htrans (midCylBody m K hw c N hKlo hKhi)
      (transBody (midCylBody m K hw c N hKlo hKhi) (-p0)) (-p0) (by simp)
  exact htr.trans hcyl0


theorem oblique_prism_zero_inner
    (m : ℕ) (μ : ConvexBody (E (m + 1)) → ℝ)
    (hcont : Continuous μ)
    (hadd : ∀ A B C D : ConvexBody (E (m + 1)),
        (A : Set (E (m + 1))) = (C : Set (E (m + 1))) ∪ (D : Set (E (m + 1))) →
        (B : Set (E (m + 1))) = (C : Set (E (m + 1))) ∩ (D : Set (E (m + 1))) →
        μ A + μ B = μ C + μ D)
    (htrans : ∀ A B : ConvexBody (E (m + 1)), ∀ t : E (m + 1),
        (B : Set (E (m + 1))) = (fun x : E (m + 1) => x + t) '' (A : Set (E (m + 1))) → μ A = μ B)
    (hsimple : ∀ K : ConvexBody (E (m + 1)), interior (K : Set (E (m + 1))) = ∅ → μ K = 0)
    (hcyl : ∀ (ρ : E (m + 1) ≃ₗᵢ[ℝ] E (m + 1)) (K0 : ConvexBody (E m)) (h : ℝ), 0 ≤ h →
        ∀ Q : ConvexBody (E (m + 1)),
          (Q : Set (E (m + 1))) = {y : E (m + 1) |
            dropLast m (ρ.symm y) ∈ (K0 : Set (E m)) ∧
              lastCoord m (ρ.symm y) ∈ Set.Icc (0 : ℝ) h} → μ Q = 0) :
    ∀ (K : ConvexBody (E m)) (w : E (m + 1)), w (Fin.last m) ≠ 0 → μ (prismBody m K w) = 0 := by
  intro K w hw
  have hwnz : w ≠ 0 := w_ne_zero_of_last m hw
  have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hwnz
  let f : E m → ℝ := fun x => ‖x‖
  have hcontOn : ContinuousOn f (K : Set (E m)) := by
    dsimp [f]
    fun_prop
  obtain ⟨xM, hxMK, hBeq, hmax⟩ := K.isCompact.exists_sSup_image_eq_and_ge K.nonempty hcontOn
  let r : ℝ := ‖xM‖
  have hr0 : 0 ≤ r := by
    dsimp [r]
    exact norm_nonneg xM
  have hnorm_le : ∀ x : E m, x ∈ (K : Set (E m)) → ‖x‖ ≤ r := by
    intro x hx
    simpa [f, r] using hmax x hx
  let c : ℝ := r * ‖w‖
  have hKlo : ∀ x : E m, x ∈ (K : Set (E m)) → inner ℝ w (emb m x) ≤ c := by
    intro x hx
    have habs : |inner ℝ w (emb m x)| ≤ ‖w‖ * r := by
      calc
        |inner ℝ w (emb m x)| ≤ ‖w‖ * ‖emb m x‖ := by
          simpa using (norm_inner_le_norm (𝕜 := ℝ) w (emb m x))
        _ = ‖w‖ * ‖x‖ := by rw [norm_emb]
        _ ≤ ‖w‖ * r := mul_le_mul_of_nonneg_left (hnorm_le x hx) (norm_nonneg w)
    calc
      inner ℝ w (emb m x) ≤ |inner ℝ w (emb m x)| := le_abs_self _
      _ ≤ ‖w‖ * r := habs
      _ = c := by
        dsimp [c]
        ring
  have h2r0 : 0 ≤ 2 * r / ‖w‖ := div_nonneg (mul_nonneg (by norm_num) hr0) (le_of_lt hwpos)
  obtain ⟨N, hNgt⟩ := exists_nat_gt (2 * r / ‖w‖)
  have hN : 0 < N := by
    have : (0 : ℝ) < (N : ℝ) := lt_of_le_of_lt h2r0 hNgt
    exact_mod_cast this
  have hNw : 2 * r < (N : ℝ) * ‖w‖ := by
    exact (div_lt_iff₀ hwpos).mp hNgt
  have hKhi : ∀ x : E m, x ∈ (K : Set (E m)) → c ≤ inner ℝ w (emb m x + (N : ℝ) • w) := by
    intro x hx
    have habs : |inner ℝ w (emb m x)| ≤ ‖w‖ * r := by
      calc
        |inner ℝ w (emb m x)| ≤ ‖w‖ * ‖emb m x‖ := by
          simpa using (norm_inner_le_norm (𝕜 := ℝ) w (emb m x))
        _ = ‖w‖ * ‖x‖ := by rw [norm_emb]
        _ ≤ ‖w‖ * r := mul_le_mul_of_nonneg_left (hnorm_le x hx) (norm_nonneg w)
    have hin_lo : -(‖w‖ * r) ≤ inner ℝ w (emb m x) := by
      exact le_trans (neg_le_neg habs) (neg_abs_le _)
    rw [inner_w_gen]
    have h2 : 2 * r * ‖w‖ < (N : ℝ) * ‖w‖ ^ 2 := by
      have h := mul_lt_mul_of_pos_right hNw hwpos
      -- h : 2 * r * ‖w‖ < (N:ℝ) * ‖w‖ * ‖w‖
      simpa [pow_two, mul_assoc, mul_comm, mul_left_comm] using h
    have hneed : r * ‖w‖ - inner ℝ w (emb m x) < (N : ℝ) * ‖w‖ ^ 2 := by
      nlinarith [h2, hin_lo]
    dsimp [c]
    nlinarith
  have hmid0 : μ (midCylBody m K hw c N hKlo hKhi) = 0 :=
    mu_midCyl_zero m μ hcont hadd htrans hsimple hcyl K hw c N hKlo hKhi
  exact bigPrism_mu_zero_of_midcyl m μ hcont hadd htrans hsimple K hw c N hN hKlo hKhi hmid0

end ObliquePrismZero

/-!
# `oblique_prism_zero` — Klain 1995 Fig. 2 ("cut a prism into a right cylinder")

This is step 1 of the in-dimension chain of Theorem 3.3 of
D. A. Klain, *A short proof of Hadwiger's characterization theorem*,
Mathematika 42 (1995) 329–339 (see p. 335, Fig. 2; also reproduced as Figure 4
of César–Johnson–Lamberty, *Valuations on convex bodies: the classical basic
facts*, freely readable; and described in `PROOF_PLAN.md`/`klain333_step.lean`
in this workspace).

## Mathematical content

`μ` is a continuous, quadruple-additive, translation-invariant, *simple*
(empty interior ⇒ 0) valuation on `W = EuclideanSpace ℝ (Fin (m+1))`, which
vanishes on every *right cylinder* `ρ(K × [0,h])` (hypothesis `hcyl`):
`K` is a convex body of `V = EuclideanSpace ℝ (Fin m)` sitting in the coordinate
hyperplane `{last coordinate = 0}`, `h ≥ 0` the height along the last coordinate
axis, and `ρ` any linear isometry of `W` (so the cylinder may sit over any
hyperplane, in any frame).  Conclusion: `μ` vanishes on every *oblique prism*
`K + [0,1]·w` over such a base `K` whose direction `w` has nonzero component
along the normal (`w (Fin.last m) ≠ 0`); if that last coordinate is 0 the prism
lies in a hyperplane and vanishes by simplicity, so the ≠ 0 hypothesis is the
essential case.

## Strategy (Klain Fig. 2)

1. From `hcyl` + translation invariance derive `μ = 0` on every right cylinder
   over every convex base in every (affine) hyperplane at every height ≥ 0
   (translate bases into the coordinate hyperplane; intervals `[a,b]` are
   translates of `[0,b-a]`).
2. Scissors lemma: an oblique prism `M = B + [0,1]·w` (base `B` a convex body of
   an affine hyperplane, `w` with nonzero normal component) can be cut into
   pieces and re-pasted *using translations only* into a right cylinder `C`
   over (a translate of) `B`.  Then `μ(M) = μ(C) = 0` via dissection additivity
   on the two dissections (both `M` and `C` are convex) plus translation
   invariance of `μ` piecewise.  When the base is too "fat" for a single clean
   cut, first subdivide the base into small convex pieces (each sub-prism is a
   dissection piece of `M`; apply the two-piece scissors to each small prism and
   reassemble).  [The 2D prototype: shear a parallelogram by sliding the two
   halves obtained by a vertical cut through the base; slanted edges glue
   internally and the cut faces become the vertical outer faces of the
   rectangle.]
3. Assemble: `μ` is zero on every oblique prism over every hyperplane body.

## Available Commons support (import in your proof file; all in namespace
`Commons.Geometry.Convex.Hadwiger`):
- `dissection_additivity` (Groemer): for continuous simple valuations,
  `φ P = ∑ φ (A i)` whenever the convex body `P` is a dissection
  `P = ⋃ᵢ Aᵢ` with pairwise empty-interior intersections — this is the engine
  for every cut-and-paste step.
- `val_eq_of_set_eq`, `simple_valuation_binary_union`, `valuation_inclusionExclusion`.
- Coordinate plumbing of `EuclideanSpace ℝ (Fin k)`/`Fin (k+1)` (first-`k`
  coordinates, last coordinate, embedding with last coordinate 0) can be
  re-developed locally in your file (see the parent module
  `Submission/Work/Geometry/Convex/Hadwiger/klain333_from_cylinders.lean` for
  the patterns: `dropLast`, `lastCoord`, `emb`, `eLast`, `cylSetStd`).
-/
theorem oblique_prism_zero
    (m : ℕ)
    (μ : ConvexBody (EuclideanSpace ℝ (Fin (m + 1))) → ℝ)
    (hcont : Continuous μ)
    (hadd : ∀ A B C D : ConvexBody (EuclideanSpace ℝ (Fin (m + 1))),
        (A : Set (EuclideanSpace ℝ (Fin (m + 1)))) =
          (C : Set (EuclideanSpace ℝ (Fin (m + 1)))) ∪ (D : Set (EuclideanSpace ℝ (Fin (m + 1)))) →
        (B : Set (EuclideanSpace ℝ (Fin (m + 1)))) =
          (C : Set (EuclideanSpace ℝ (Fin (m + 1)))) ∩ (D : Set (EuclideanSpace ℝ (Fin (m + 1)))) →
        μ A + μ B = μ C + μ D)
    (htrans : ∀ A B : ConvexBody (EuclideanSpace ℝ (Fin (m + 1))),
        ∀ t : EuclideanSpace ℝ (Fin (m + 1)),
          (B : Set (EuclideanSpace ℝ (Fin (m + 1)))) =
            (fun x : EuclideanSpace ℝ (Fin (m + 1)) => x + t) '' (A : Set (EuclideanSpace ℝ (Fin (m + 1)))) →
          μ A = μ B)
    (hsimple : ∀ K : ConvexBody (EuclideanSpace ℝ (Fin (m + 1))),
        interior (K : Set (EuclideanSpace ℝ (Fin (m + 1)))) = ∅ → μ K = 0)
    (hcyl : ∀ (ρ : EuclideanSpace ℝ (Fin (m + 1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (m + 1)))
        (K : ConvexBody (EuclideanSpace ℝ (Fin m))) (h : ℝ), 0 ≤ h →
        ∀ Q : ConvexBody (EuclideanSpace ℝ (Fin (m + 1))),
          (Q : Set (EuclideanSpace ℝ (Fin (m + 1)))) =
            {y : EuclideanSpace ℝ (Fin (m + 1)) |
              (EuclideanSpace.equiv (Fin m) ℝ).symm (fun i : Fin m => (ρ.symm y) (Fin.castSucc i)) ∈
                (K : Set (EuclideanSpace ℝ (Fin m))) ∧
              (ρ.symm y) (Fin.last m) ∈ Set.Icc (0 : ℝ) h} →
          μ Q = 0) :
    ∀ (K : ConvexBody (EuclideanSpace ℝ (Fin m))) (w : EuclideanSpace ℝ (Fin (m + 1))),
      w (Fin.last m) ≠ 0 →
      ∀ Q : ConvexBody (EuclideanSpace ℝ (Fin (m + 1))),
        (Q : Set (EuclideanSpace ℝ (Fin (m + 1)))) =
          {y : EuclideanSpace ℝ (Fin (m + 1)) |
            ∃ x : EuclideanSpace ℝ (Fin m),
              x ∈ (K : Set (EuclideanSpace ℝ (Fin m))) ∧
              ∃ t : ℝ,
                t ∈ Set.Icc (0 : ℝ) 1 ∧
                y = (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
                      (fun j : Fin (m + 1) => if h : j = Fin.last m then (0 : ℝ) else x (Fin.castLT j (Fin.val_lt_last h))) + t • w} →
        μ Q = 0 := by
  have hcyl' :
      ∀ (ρ : ObliquePrismZero.E (m + 1) ≃ₗᵢ[ℝ] ObliquePrismZero.E (m + 1))
        (K0 : ConvexBody (ObliquePrismZero.E m)) (h : ℝ), 0 ≤ h →
        ∀ Q : ConvexBody (ObliquePrismZero.E (m + 1)),
          (Q : Set (ObliquePrismZero.E (m + 1))) =
            {y : ObliquePrismZero.E (m + 1) |
              ObliquePrismZero.dropLast m (ρ.symm y) ∈ (K0 : Set (ObliquePrismZero.E m)) ∧
                ObliquePrismZero.lastCoord m (ρ.symm y) ∈ Set.Icc (0 : ℝ) h} → μ Q = 0 := by
    intro ρ K0 h hh Q hQ
    exact hcyl ρ K0 h hh Q hQ
  intro K w hw Q hQ
  have hz : μ (ObliquePrismZero.prismBody m K w) = 0 :=
    ObliquePrismZero.oblique_prism_zero_inner m μ hcont hadd htrans hsimple hcyl' K w hw
  have hQeq : (Q : Set (EuclideanSpace ℝ (Fin (m + 1)))) =
      (ObliquePrismZero.prismBody m K w : Set (EuclideanSpace ℝ (Fin (m + 1)))) := by
    change (Q : Set (EuclideanSpace ℝ (Fin (m + 1)))) =
      ObliquePrismZero.segPrismSet m K w 0 1
    exact hQ
  have hμ : μ Q = μ (ObliquePrismZero.prismBody m K w) := val_eq_of_set_eq μ hadd hQeq
  rw [hμ]
  exact hz

end