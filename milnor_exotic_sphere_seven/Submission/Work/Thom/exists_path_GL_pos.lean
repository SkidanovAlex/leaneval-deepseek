import Mathlib
import Submission.Work.Thom.even_card_neg_of_prod_pos

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The positive-determinant general linear group over `ℝ` is path connected

This file proves `Work.Thom.exists_path_GL_pos`: for a real `n × n` matrix `M` with `det M > 0`
there is a continuous path of matrices from `M` to `1` along which the determinant never vanishes.

The route is the classical one.  We write `M = L · D · L'` where `D` is diagonal and `L`, `L'` are
products of transvections (`Matrix.Pivot.exists_list_transvec_mul_diagonal_mul_list_transvec`), and
connect each of the three factors to `1`:

* a transvection `T` is connected to `1` by `s ↦ transvection i j ((1-s) * c)`,
* a diagonal matrix with positive determinant is connected to `1`; reducing the entries to their
  signs by a linear interpolation of the diagonal entries, one is left with the diagonal matrix
  `negDiag s` with `-1` on a set `s` of even cardinality, and such a matrix is connected to `1` by
  pairing up the elements of `s` and rotating the corresponding `2 × 2` block; here the rotation of
  angle `π` in the coordinates `a`, `b` is written explicitly as the square
  `(T_{a b}(1) · T_{b a}(-2))^2`, a product of four transvections, so that every matrix along the
  path is visibly a product of transvections.
-/

namespace Work.Thom

open Matrix

/-- `Conn A B` : `A` and `B` are joined by a continuous path of matrices whose determinant is a
unit (i.e. non-zero) at every time. -/
def Conn {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∃ γ : Path A B, ∀ t : unitInterval, IsUnit (γ t).det

lemma Conn.refl {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (h : IsUnit A.det) : Conn A A :=
  ⟨Path.refl A, fun t => by rw [Path.refl_apply]; exact h⟩

lemma Conn.symm {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℝ} (h : Conn A B) : Conn B A := by
  obtain ⟨γ, hγ⟩ := h
  exact ⟨γ.symm, fun t => by rw [Path.symm_apply]; exact hγ _⟩

lemma Conn.trans {n : ℕ} {A B C : Matrix (Fin n) (Fin n) ℝ} (h₁ : Conn A B) (h₂ : Conn B C) :
    Conn A C := by
  obtain ⟨γ, hγ⟩ := h₁
  obtain ⟨δ, hδ⟩ := h₂
  refine ⟨γ.trans δ, fun t => ?_⟩
  rw [Path.trans_apply]
  split_ifs with h
  · exact hγ _
  · exact hδ _

lemma Conn.mul {n : ℕ} {A B C D : Matrix (Fin n) (Fin n) ℝ} (h₁ : Conn A B) (h₂ : Conn C D) :
    Conn (A * C) (B * D) := by
  obtain ⟨γ, hγ⟩ := h₁
  obtain ⟨δ, hδ⟩ := h₂
  have hcont : Continuous fun t : unitInterval => γ t * δ t := γ.continuous.mul δ.continuous
  have hsrc : (fun t : unitInterval => γ t * δ t) 0 = A * C := by
    show γ 0 * δ 0 = A * C
    rw [Path.source γ, Path.source δ]
  have htgt : (fun t : unitInterval => γ t * δ t) 1 = B * D := by
    show γ 1 * δ 1 = B * D
    rw [Path.target γ, Path.target δ]
  refine ⟨⟨⟨fun t => γ t * δ t, hcont⟩, hsrc, htgt⟩, ?_⟩
  intro t
  show IsUnit ((γ t * δ t).det)
  rw [Matrix.det_mul]
  exact (hγ t).mul (hδ t)

/-- The product of two paths to the identity. -/
lemma Conn.mulToId {n : ℕ} {A C : Matrix (Fin n) (Fin n) ℝ} (h₁ : Conn A 1) (h₂ : Conn C 1) :
    Conn (A * C) 1 := by
  obtain ⟨γ, hγ⟩ := h₁
  obtain ⟨δ, hδ⟩ := h₂
  have hcont : Continuous fun t : unitInterval => γ t * δ t := γ.continuous.mul δ.continuous
  have hsrc : (fun t : unitInterval => γ t * δ t) 0 = A * C := by
    show γ 0 * δ 0 = A * C
    rw [Path.source γ, Path.source δ]
  have htgt : (fun t : unitInterval => γ t * δ t) 1 = 1 := by
    show γ 1 * δ 1 = 1
    rw [Path.target γ, Path.target δ, mul_one]
  refine ⟨⟨⟨fun t => γ t * δ t, hcont⟩, hsrc, htgt⟩, ?_⟩
  intro t
  show IsUnit ((γ t * δ t).det)
  rw [Matrix.det_mul]
  exact (hγ t).mul (hδ t)

/-! ## Continuity helpers -/

lemma continuous_transvection {n : ℕ} {X : Type*} [TopologicalSpace X] (i j : Fin n)
    {f : X → ℝ} (hf : Continuous f) : Continuous fun x => Matrix.transvection i j (f x) := by
  have h : ∀ c : ℝ, Matrix.transvection i j c =
      1 + c • Matrix.single i j (1 : ℝ) := by
    intro c
    unfold Matrix.transvection
    rw [Matrix.smul_single]
    simp
  simp only [h]
  exact continuous_const.add (hf.smul continuous_const)

/-! ## Transvections -/

/-- A transvection is connected to the identity by `s ↦ transvection i j ((1 - s) * c)`; along this
path the determinant is identically `1`. -/
lemma conn_transvection {n : ℕ} (i j : Fin n) (hij : i ≠ j) (c : ℝ) :
    Conn (Matrix.transvection i j c) 1 := by
  refine ⟨⟨⟨fun t : unitInterval => Matrix.transvection i j ((1 - (t : ℝ)) * c), ?_⟩, ?_, ?_⟩, ?_⟩
  · exact continuous_transvection i j ((continuous_const.sub continuous_subtype_val).mul
      continuous_const)
  · show Matrix.transvection i j ((1 - ((0 : unitInterval) : ℝ)) * c) = Matrix.transvection i j c
    norm_num
  · show Matrix.transvection i j ((1 - ((1 : unitInterval) : ℝ)) * c) = 1
    rw [show (1 : ℝ) - ((1 : unitInterval) : ℝ) = 0 by norm_num, zero_mul,
      Matrix.transvection_zero]
  · intro t
    show IsUnit (Matrix.transvection i j ((1 - (t : ℝ)) * c)).det
    rw [Matrix.det_transvection_of_ne i j hij]
    exact isUnit_one

/-! ## Flipping the entries on an even set of coordinates -/

/-- The diagonal matrix with `-1` on `s` and `1` elsewhere. -/
def negDiag {n : ℕ} (s : Finset (Fin n)) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.diagonal fun i => if i ∈ s then (-1 : ℝ) else 1

lemma negDiag_empty {n : ℕ} : negDiag (∅ : Finset (Fin n)) = (1 : Matrix (Fin n) (Fin n) ℝ) := by
  ext i j
  simp [negDiag, Matrix.diagonal_apply, Matrix.one_apply]

lemma negDiag_pair {n : ℕ} {a b : Fin n} (hab : a ≠ b) :
    negDiag ({a, b} : Finset (Fin n)) = 1 - 2 • (Matrix.single a a (1 : ℝ) + Matrix.single b b 1) := by
  rw [negDiag, ← Matrix.diagonal_single, ← Matrix.diagonal_single, ← Matrix.diagonal_one,
    Matrix.diagonal_add, ← Matrix.diagonal_smul, Matrix.diagonal_sub]
  congr 1
  funext i
  by_cases h : i = a <;> by_cases h' : i = b <;>
    simp_all [Pi.single_apply, Finset.mem_insert, Finset.mem_singleton]
  all_goals norm_num

lemma negDiag_insert_insert {n : ℕ} {s : Finset (Fin n)} {a b : Fin n}
    (ha : a ∉ s) (hb : b ∉ s) (hab : a ≠ b) :
    negDiag (insert a (insert b s)) = negDiag ({a, b} : Finset (Fin n)) * negDiag s := by
  rw [negDiag, negDiag, negDiag, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  by_cases h : i = a
  · subst h; simp [ha, hab]
  · by_cases h' : i = b
    · subst h'; simp [hb]
    · simp [h, h', Finset.mem_insert]

/-- The product of two transvections in the coordinate directions `(a, b)` and `(b, a)`. -/
lemma transvection_pair_prod {n : ℕ} (a b : Fin n) (u v : ℝ) :
    Matrix.transvection a b u * Matrix.transvection b a v
      = 1 + Matrix.single a b u + Matrix.single b a v + Matrix.single a a (u * v) := by
  unfold Matrix.transvection
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.one_mul, Matrix.mul_one]
  repeat rw [Matrix.single_mul_single_same]
  abel

/-- The square of `T_{a b}(1) · T_{b a}(-2)` is the diagonal matrix with `-1` at `a` and `b`.
This is the rotation by `π` in the coordinates `a`, `b`, written as a product of four
transvections. -/
lemma transvection_pair_sq {n : ℕ} (a b : Fin n) (hab : a ≠ b) :
    (Matrix.transvection a b (1 : ℝ) * Matrix.transvection b a (-2 : ℝ)) *
      (Matrix.transvection a b (1 : ℝ) * Matrix.transvection b a (-2 : ℝ))
      = negDiag ({a, b} : Finset (Fin n)) := by
  rw [negDiag_pair hab]
  have h1 : Matrix.transvection a b (1 : ℝ) * Matrix.transvection b a (-2 : ℝ)
      = 1 + Matrix.single a b (1 : ℝ) + Matrix.single b a (-2 : ℝ) +
          Matrix.single a a (-2 : ℝ) := by
    simpa using transvection_pair_prod a b (1 : ℝ) (-2 : ℝ)
  rw [h1]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.one_mul, Matrix.mul_one]
  repeat rw [Matrix.single_mul_single_same]
  repeat rw [Matrix.single_mul_single_of_ne _ _ _ _ hab]
  repeat rw [Matrix.single_mul_single_of_ne _ _ _ _ hab.symm]
  ext i j
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.add_apply, Matrix.zero_apply,
    Matrix.one_apply, Matrix.single_apply]
  split_ifs <;> norm_num

/-- The matrix `T_{a b}(u) · T_{b a}(-2u)`; at `u = 0` it is the identity, and at `u = 1` its
square is the reflection in the coordinates `a`, `b`. -/
def qmat {n : ℕ} (a b : Fin n) (u : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.transvection a b u * Matrix.transvection b a (-2 * u)

lemma continuous_qmat {n : ℕ} (a b : Fin n) : Continuous (qmat a b) := by
  unfold qmat
  exact (continuous_transvection a b continuous_id).mul
    (continuous_transvection b a (continuous_const.mul continuous_id))

lemma qmat_det {n : ℕ} (a b : Fin n) (hab : a ≠ b) (u : ℝ) : (qmat a b u).det = 1 := by
  unfold qmat
  rw [Matrix.det_mul, Matrix.det_transvection_of_ne _ _ hab,
    Matrix.det_transvection_of_ne _ _ hab.symm, one_mul]

lemma qmat_zero {n : ℕ} (a b : Fin n) : qmat a b 0 = 1 := by
  unfold qmat
  rw [mul_zero, Matrix.transvection_zero, Matrix.transvection_zero, one_mul]

lemma qmat_one_sq {n : ℕ} (a b : Fin n) (hab : a ≠ b) :
    qmat a b 1 * qmat a b 1 = negDiag ({a, b} : Finset (Fin n)) := by
  have h : qmat a b 1 = Matrix.transvection a b (1 : ℝ) * Matrix.transvection b a (-2 : ℝ) := by
    unfold qmat
    rw [mul_one]
  rw [h, transvection_pair_sq a b hab]

/-- **A `2 × 2` sign flip is contractible.** The diagonal matrix with `-1` in the two coordinates
`a`, `b` is connected to the identity through matrices with non-zero determinant. -/
lemma conn_negDiag_pair {n : ℕ} (a b : Fin n) (hab : a ≠ b) :
    Conn (negDiag ({a, b} : Finset (Fin n))) 1 := by
  have hcont : Continuous fun t : unitInterval =>
      qmat a b (1 - (t : ℝ)) * qmat a b (1 - (t : ℝ)) :=
    ((continuous_qmat a b).comp (continuous_const.sub continuous_subtype_val)).mul
      ((continuous_qmat a b).comp (continuous_const.sub continuous_subtype_val))
  refine ⟨⟨⟨fun t : unitInterval => qmat a b (1 - (t : ℝ)) * qmat a b (1 - (t : ℝ)), hcont⟩,
    ?_, ?_⟩, ?_⟩
  · show qmat a b (1 - ((0 : unitInterval) : ℝ)) * qmat a b (1 - ((0 : unitInterval) : ℝ))
      = negDiag ({a, b} : Finset (Fin n))
    rw [show (1 : ℝ) - ((0 : unitInterval) : ℝ) = 1 by norm_num]
    exact qmat_one_sq a b hab
  · show qmat a b (1 - ((1 : unitInterval) : ℝ)) * qmat a b (1 - ((1 : unitInterval) : ℝ)) = 1
    rw [show (1 : ℝ) - ((1 : unitInterval) : ℝ) = 0 by norm_num, qmat_zero, one_mul]
  · intro t
    show IsUnit ((qmat a b (1 - (t : ℝ)) * qmat a b (1 - (t : ℝ))).det)
    rw [Matrix.det_mul, qmat_det a b hab, mul_one]
    exact isUnit_one

/-- The reflection in an even set of coordinates is connected to the identity. -/
lemma conn_negDiag_of_even {n : ℕ} (s : Finset (Fin n)) (hs : Even s.card) :
    Conn (negDiag s) 1 := by
  induction s using Finset.strongInductionOn with
  | _ s ih =>
    rcases Finset.eq_empty_or_nonempty s with h | ⟨a, ha⟩
    · subst h
      rw [negDiag_empty]
      exact Conn.refl 1 (by rw [Matrix.det_one]; exact isUnit_one)
    · have hcard : 0 < s.card := Finset.card_pos.mpr ⟨a, ha⟩
      have h2 : 2 ≤ s.card := by
        obtain ⟨k, hk⟩ := hs
        omega
      have hnonempty : (s.erase a).Nonempty := by
        rw [← Finset.card_pos, Finset.card_erase_of_mem ha]
        omega
      obtain ⟨b, hb⟩ := hnonempty
      rw [Finset.mem_erase] at hb
      obtain ⟨hba, hbs⟩ := hb
      have hbs' : b ∈ s.erase a := Finset.mem_erase.mpr ⟨hba, hbs⟩
      set s' : Finset (Fin n) := (s.erase a).erase b with hs'def
      have ha' : a ∉ s' := by
        rw [hs'def]
        exact fun h => (Finset.notMem_erase a s) (Finset.mem_of_mem_erase h)
      have hb' : b ∉ s' := by rw [hs'def]; exact Finset.notMem_erase b (s.erase a)
      have hsub : s' ⊆ s := by
        rw [hs'def]
        exact Finset.Subset.trans (Finset.erase_subset _ _) (Finset.erase_subset _ _)
      have hs'_ne : s' ≠ s := by
        intro h
        exact ha' (h ▸ ha)
      have hssub : s' ⊂ s := Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hs'_ne⟩
      have heven' : Even s'.card := by
        have hc : s'.card = s.card - 2 := by
          rw [hs'def, Finset.card_erase_of_mem hbs', Finset.card_erase_of_mem ha]
          omega
        obtain ⟨k, hk⟩ := hs
        exact ⟨k - 1, by omega⟩
      have ih' : Conn (negDiag s') 1 := ih s' hssub heven'
      have hins : insert a (insert b s') = s := by
        rw [hs'def, Finset.insert_erase hbs', Finset.insert_erase ha]
      rw [← hins, negDiag_insert_insert ha' hb' hba.symm]
      exact Conn.mulToId (conn_negDiag_pair a b hba.symm) ih'

/-! ## Diagonal matrices -/

/-- A diagonal matrix with positive determinant is connected to the identity. -/
lemma conn_diagonal {n : ℕ} (D : Fin n → ℝ) (hdet : 0 < (Matrix.diagonal D).det) :
    Conn (Matrix.diagonal D) 1 := by
  have hprod : 0 < ∏ i, D i := by rwa [Matrix.det_diagonal] at hdet
  have hne : ∀ i, D i ≠ 0 := fun i =>
    (Finset.prod_ne_zero_iff.mp (ne_of_gt hprod)) i (Finset.mem_univ i)
  -- the interpolation path, from `diagonal D` to the sign matrix of `D`
  have hcont : Continuous fun t : unitInterval =>
      (1 - (t : ℝ)) • Matrix.diagonal D +
        (t : ℝ) • Matrix.diagonal (fun i => if 0 < D i then (1 : ℝ) else -1) :=
    ((continuous_const.sub continuous_subtype_val).smul continuous_const).add
      (continuous_subtype_val.smul continuous_const)
  have hsrc : (fun t : unitInterval =>
      (1 - (t : ℝ)) • Matrix.diagonal D +
        (t : ℝ) • Matrix.diagonal (fun i => if 0 < D i then (1 : ℝ) else -1)) 0
      = Matrix.diagonal D := by
    show (1 - ((0 : unitInterval) : ℝ)) • Matrix.diagonal D +
      ((0 : unitInterval) : ℝ) • Matrix.diagonal (fun i => if 0 < D i then (1 : ℝ) else -1)
      = Matrix.diagonal D
    rw [show (1 : ℝ) - ((0 : unitInterval) : ℝ) = 1 by norm_num,
      show ((0 : unitInterval) : ℝ) = 0 by norm_num, zero_smul, add_zero, one_smul]
  have htgt : (fun t : unitInterval =>
      (1 - (t : ℝ)) • Matrix.diagonal D +
        (t : ℝ) • Matrix.diagonal (fun i => if 0 < D i then (1 : ℝ) else -1)) 1
      = Matrix.diagonal (fun i => if 0 < D i then (1 : ℝ) else -1) := by
    show (1 - ((1 : unitInterval) : ℝ)) • Matrix.diagonal D +
      ((1 : unitInterval) : ℝ) •
        Matrix.diagonal (fun i => if 0 < D i then (1 : ℝ) else -1)
      = Matrix.diagonal (fun i => if 0 < D i then (1 : ℝ) else -1)
    rw [show (1 : ℝ) - ((1 : unitInterval) : ℝ) = 0 by norm_num,
      show ((1 : unitInterval) : ℝ) = 1 by norm_num, zero_smul, zero_add, one_smul]
  have hdet1 : ∀ t : unitInterval,
      IsUnit ((fun t : unitInterval =>
        (1 - (t : ℝ)) • Matrix.diagonal D +
          (t : ℝ) • Matrix.diagonal (fun i => if 0 < D i then (1 : ℝ) else -1)) t).det := by
    intro t
    show IsUnit (((1 - (t : ℝ)) • Matrix.diagonal D +
      (t : ℝ) • Matrix.diagonal (fun i => if 0 < D i then (1 : ℝ) else -1)).det)
    rw [← Matrix.diagonal_smul, ← Matrix.diagonal_smul, Matrix.diagonal_add,
      Matrix.det_diagonal, isUnit_iff_ne_zero, Finset.prod_ne_zero_iff]
    intro i _
    simp only [Pi.smul_apply, smul_eq_mul]
    by_cases hi : 0 < D i
    · rw [if_pos hi]
      have hpos : 0 < (1 - (t : ℝ)) * D i + (t : ℝ) * 1 := by
        nlinarith [mul_nonneg (by linarith [t.2.2] : (0 : ℝ) ≤ 1 - (t : ℝ)) (le_of_lt hi),
          (t.2.1 : (0 : ℝ) ≤ (t : ℝ)), hi]
      linarith
    · have hneg : D i < 0 := lt_of_le_of_ne (le_of_not_gt hi) (hne i)
      rw [if_neg hi]
      have hneg' : (1 - (t : ℝ)) * D i + (t : ℝ) * (-1) < 0 := by
        nlinarith [mul_nonpos_of_nonneg_of_nonpos
            (by linarith [t.2.2] : (0 : ℝ) ≤ 1 - (t : ℝ)) (le_of_lt hneg),
          (t.2.1 : (0 : ℝ) ≤ (t : ℝ)), hneg]
      linarith
  have h1 : Conn (Matrix.diagonal D)
      (Matrix.diagonal (fun i => if 0 < D i then (1 : ℝ) else -1)) :=
    ⟨⟨⟨_, hcont⟩, hsrc, htgt⟩, hdet1⟩
  -- the sign matrix is the reflection in the set of negative coordinates
  have hsign : Matrix.diagonal (fun i => if 0 < D i then (1 : ℝ) else -1)
      = negDiag (Finset.univ.filter fun i => D i < 0) := by
    rw [negDiag]
    congr 1
    funext i
    by_cases hi : D i < 0
    · have h1' : ¬ (0 < D i) := not_lt.mpr (le_of_lt hi)
      simp [hi, h1']
    · have h1' : 0 < D i := lt_of_le_of_ne (le_of_not_gt hi) (Ne.symm (hne i))
      simp [hi, h1']
  have heven : Even (Finset.univ.filter fun i => D i < 0).card :=
    even_card_neg_of_prod_pos D hne hprod
  rw [hsign] at h1
  exact Conn.trans h1 (conn_negDiag_of_even _ heven)

/-! ## Products of transvections -/

lemma conn_toMatrix {n : ℕ} (t : Matrix.TransvectionStruct (Fin n) ℝ) : Conn t.toMatrix 1 := by
  cases t with
  | mk i j hij c =>
    rw [Matrix.TransvectionStruct.toMatrix_mk]
    exact conn_transvection i j hij c

lemma conn_list_prod {n : ℕ} (L : List (Matrix.TransvectionStruct (Fin n) ℝ)) :
    Conn (L.map Matrix.TransvectionStruct.toMatrix).prod 1 := by
  induction L with
  | nil =>
    rw [List.map_nil, List.prod_nil]
    exact Conn.refl 1 (by rw [Matrix.det_one]; exact isUnit_one)
  | cons t L ih =>
    rw [List.map_cons, List.prod_cons]
    exact Conn.mulToId (conn_toMatrix t) ih

/-! ## The theorem -/

/-- **The positive-determinant general linear group over `ℝ` is path connected** (pointwise form).

For a real `n × n` matrix `M` with `det M > 0` there is a continuous path of matrices from `M` to `1`
along which the determinant never vanishes.  (For `n = 0` the matrix type is a subsingleton and the
statement is trivial.)

Suggested route: `Matrix.diagonal_transvection_induction` reduces to (a) transvections, which are
connected to `1` by `s ↦ transvection i j (s * c)`, and (b) diagonal matrices of determinant `> 0`;
for (b) reduce by a path to the case of diagonal entries `±1` with an even number of `-1`s, and for
that case pair up the negative positions (`Finset` induction on the set of negative positions,
picking two elements at a time, possible because its cardinality is even) and connect the block
`diag (-1, -1)` on a pair of coordinates to the identity by the rotation path
`[[cos θ, -sin θ], [sin θ, cos θ]]`, `θ` from `π` to `0`.

Here the route followed is the same, with the rotation by `π` written as the product of four
transvections `(T_{a b}(1) · T_{b a}(-2))^2` so that every matrix appearing along the path is
visibly a product of transvections.-/
theorem exists_path_GL_pos (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (hM : 0 < M.det) :
    ∃ γ : C(unitInterval, Matrix (Fin n) (Fin n) ℝ),
      γ 0 = M ∧ γ 1 = 1 ∧ ∀ t : unitInterval, IsUnit (γ t).det := by
  obtain ⟨L, L', D, hD⟩ := Matrix.Pivot.exists_list_transvec_mul_diagonal_mul_list_transvec M
  have hdetD : 0 < (Matrix.diagonal D).det := by
    have h1 : M.det = (Matrix.diagonal D).det := by
      rw [hD, Matrix.det_mul, Matrix.det_mul, Matrix.TransvectionStruct.det_toMatrix_prod,
        Matrix.TransvectionStruct.det_toMatrix_prod, one_mul, mul_one]
    rwa [h1] at hM
  have h := Conn.mulToId (Conn.mulToId (conn_list_prod L) (conn_diagonal D hdetD))
    (conn_list_prod L')
  rw [← hD] at h
  obtain ⟨γ, hγ⟩ := h
  exact ⟨γ, γ.source, γ.target, hγ⟩

end Work.Thom
