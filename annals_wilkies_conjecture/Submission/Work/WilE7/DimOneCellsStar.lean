/-
  Area E7, dimension-one case of BV Proposition 9: every cell of the decomposition `cuts U`
  of the line is a `*`-set of format `1` and degree `4`, and a restricted sub-Pfaffian set.

  The cells of `cuts U` are the singletons `{t}` (`t ∈ U`) and the open intervals `(a,b)`
  between consecutive points of `U`.  Each of them is realised by an explicit `*`-piece:

  * `pointPiece t`  — the piece with a single `*`-coordinate (`m = 0`), the semi-Pfaffian set
    `{x ∈ cubeC 1 | x 0 = t}` and the point `pt1 t`;
  * `ivlPiece a b`  — the piece with the semi-Pfaffian set `{x ∈ cubeC 1 | a < x 0 < b}` and
    the midpoint `pt1 ((a+b)/2)`.

  The set of such a piece is the projection to the first `1` coordinates of the connected
  component of its semi-Pfaffian set through the chosen point.  Since the semi-Pfaffian set
  is exactly the cell (`set_ptSemiPf`, `set_ivlSemiPf`) and the cell is preconnected (a
  singleton, resp. an interval), that component is the whole cell, and since the fibre
  dimension is `m = 0` the projection is the identity (`image_projFirst_one_zero`).

  The format bound `1` is `1 + 0` (ambient dimension plus chain length); the degree bound
  `4` comes from the fact that each of the two defining linear atoms has total degree `≤ 1`,
  hence `atomDeg ≤ 2` and the degree sum is `≤ 4`.  The same witnesses give `SubPf 1` with
  the trivial fibration `m = 0`.
-/
import Mathlib
import Submission.Work.WilE7.DimOneCells

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilE7
open WilkiesConjecture WilkiesDesign WilkiesDesign.E

/-! ## The identity `ℝ^{1+0} → ℝ¹` -/

/-- The projection `projFirst 1 0` is the identity (the types `Fin (1+0)` and `Fin 1` agree
definitionally). -/
theorem projFirst_one_zero (x : Fin (1 + 0) → ℝ) : projFirst 1 0 x = x := by
  funext i
  show x (Fin.castAdd 0 i) = x i
  congr 1

/-- The image of a set of `ℝ¹` under `projFirst 1 0` is the set itself. -/
theorem image_projFirst_one_zero (S : Set (Fin 1 → ℝ)) : projFirst 1 0 '' S = S := by
  have h : projFirst 1 0 = id := by
    funext x i
    show x (Fin.castAdd 0 i) = x i
    congr 1
  rw [h, Set.image_id]

/-- The map `pt1 : ℝ → ℝ¹` is continuous. -/
theorem continuous_pt1 : Continuous pt1 := continuous_pi fun _ => continuous_id

/-! ## The two cell shapes -/

/-- Membership in the semi-Pfaffian set of `pointPiece`. -/
theorem mem_ptSemiPf (t : ℝ) (x : Fin 1 → ℝ) :
    x ∈ (ptSemiPf t).set ↔ x 0 = t ∧ x ∈ cubeC 1 := by
  unfold ptSemiPf WilkiesDesign.E.SemiPf.set
  simp [WilkiesDesign.E.Basic.holds, eaEval, EAChain.nil, sub_eq_zero]
  tauto

/-- Membership in the semi-Pfaffian set of `ivlPiece`. -/
theorem mem_ivlSemiPf (a b : ℝ) (x : Fin 1 → ℝ) :
    x ∈ (ivlSemiPf a b).set ↔ a < x 0 ∧ x 0 < b ∧ x ∈ cubeC 1 := by
  unfold ivlSemiPf WilkiesDesign.E.SemiPf.set
  simp [WilkiesDesign.E.Basic.holds, eaEval, EAChain.nil]
  tauto

/-- For `|t| ≤ 1` the semi-Pfaffian set `{x ∈ cubeC 1 | x 0 = t}` is the singleton cell. -/
theorem set_ptSemiPf (t : ℝ) (ht : |t| ≤ 1) : (ptSemiPf t).set = cellPt t := by
  ext x
  rw [mem_ptSemiPf, mem_cellPt, pt1_eq_iff]
  constructor
  · rintro ⟨h, -⟩; exact h
  · intro h
    refine ⟨h, ?_⟩
    intro i
    rw [Fin.eq_zero i, h]
    exact ht

/-- For `-1 ≤ a` and `b ≤ 1` the semi-Pfaffian set `{x ∈ cubeC 1 | a < x 0 < b}` is the
open interval cell. -/
theorem set_ivlSemiPf (a b : ℝ) (ha : -1 ≤ a) (hb : b ≤ 1) :
    (ivlSemiPf a b).set = cellIoo a b := by
  ext x
  rw [mem_ivlSemiPf, mem_cellIoo]
  constructor
  · rintro ⟨h1, h2, -⟩; exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨h1, h2, ?_⟩
    intro i
    rw [Fin.eq_zero i]
    exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- The open interval cell is preconnected: it is the image of `Set.Ioo a b ⊆ ℝ` under the
continuous map `pt1`. -/
theorem isPreconnected_cellIoo (a b : ℝ) : IsPreconnected (cellIoo a b) := by
  have h : cellIoo a b = pt1 '' Set.Ioo a b := by
    ext x
    rw [mem_cellIoo, Set.mem_image]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨x 0, ⟨h1, h2⟩, (pt1_eq_iff (t := x 0)).mpr rfl |>.symm⟩
    · rintro ⟨y, hy, rfl⟩; simpa using hy
  rw [h]
  exact isPreconnected_Ioo.image _ continuous_pt1.continuousOn

/-! ## The point sets of the two pieces -/

/-- The `*`-piece `pointPiece t` realises the singleton cell `{t}`. -/
theorem pointPiece_set (t : ℝ) (ht : |t| ≤ 1) : (pointPiece t).set = cellPt t := by
  show projFirst 1 0 '' connectedComponentIn (ptSemiPf t).set (pt1 t) = cellPt t
  have hset := set_ptSemiPf t ht
  have hcell : IsPreconnected (cellPt t) := by
    rw [cellPt]; exact isPreconnected_singleton
  have hpre : IsPreconnected (ptSemiPf t).set := hset ▸ hcell
  have hx : pt1 t ∈ (ptSemiPf t).set := by rw [hset]; exact rfl
  rw [hpre.connectedComponentIn hx, hset, image_projFirst_one_zero]

/-- The `*`-piece `ivlPiece a b` realises the open interval cell `(a,b)`. -/
theorem ivlPiece_set (a b : ℝ) (ha : -1 ≤ a) (hb : b ≤ 1) (hab : a < b) :
    (ivlPiece a b).set = cellIoo a b := by
  show projFirst 1 0 '' connectedComponentIn (ivlSemiPf a b).set (pt1 ((a + b) / 2))
      = cellIoo a b
  have hset := set_ivlSemiPf a b ha hb
  have hpre : IsPreconnected (ivlSemiPf a b).set := hset ▸ isPreconnected_cellIoo a b
  have hx : pt1 ((a + b) / 2) ∈ (ivlSemiPf a b).set := by
    rw [hset, mem_cellIoo, pt1_apply]
    exact ⟨by linarith, by linarith⟩
  rw [hpre.connectedComponentIn hx, hset, image_projFirst_one_zero]

/-! ## Format and degree of the two pieces -/

/-- The format of `pointPiece t` is `1 + 0 = 1`. -/
theorem pointPiece_fmt (t : ℝ) : (pointPiece t).X.fmt ≤ 1 := by
  show (ptSemiPf t).fmt ≤ 1
  simp [ptSemiPf, WilkiesDesign.E.SemiPf.fmt]

/-- The format of `ivlPiece a b` is `1 + 0 = 1`. -/
theorem ivlPiece_fmt (a b : ℝ) : (ivlPiece a b).X.fmt ≤ 1 := by
  show (ivlSemiPf a b).fmt ≤ 1
  simp [ivlSemiPf, WilkiesDesign.E.SemiPf.fmt]

/-- The atom `X 0 - C t` has total degree at most `1`. -/
theorem totalDegree_X_sub_C (t : ℝ) :
    (MvPolynomial.X (Sum.inl (0 : Fin 1)) - MvPolynomial.C t : EAPoly 1 0).totalDegree
      ≤ 1 := by
  calc _ ≤ (MvPolynomial.X (Sum.inl (0 : Fin 1)) : EAPoly 1 0).totalDegree :=
        MvPolynomial.totalDegree_sub_C_le _ _
    _ = 1 := MvPolynomial.totalDegree_X _

/-- The atom `C b - X 0` has total degree at most `1`. -/
theorem totalDegree_C_sub_X (b : ℝ) :
    (MvPolynomial.C b - MvPolynomial.X (Sum.inl (0 : Fin 1)) : EAPoly 1 0).totalDegree
      ≤ 1 := by
  rw [show (MvPolynomial.C b - MvPolynomial.X (Sum.inl (0 : Fin 1)) : EAPoly 1 0)
      = -(MvPolynomial.X (Sum.inl (0 : Fin 1)) - MvPolynomial.C b) by ring]
  rw [MvPolynomial.totalDegree_neg]
  exact totalDegree_X_sub_C b

/-- The degree of `pointPiece t` is `atomDeg (X 0 - C t) ≤ 2 ≤ 4`. -/
theorem pointPiece_deg (t : ℝ) : (pointPiece t).X.deg ≤ 4 := by
  show (ptSemiPf t).deg ≤ 4
  have h := totalDegree_X_sub_C t
  simp only [ptSemiPf, WilkiesDesign.E.SemiPf.deg, WilkiesDesign.E.Basic.deg,
    WilkiesDesign.E.atomDeg, List.map_cons, List.map_nil, List.append_nil, List.sum_cons,
    List.sum_nil, add_zero]
  omega

/-- The degree of `ivlPiece a b` is the sum of the two atom degrees, each `≤ 2`. -/
theorem ivlPiece_deg (a b : ℝ) : (ivlPiece a b).X.deg ≤ 4 := by
  show (ivlSemiPf a b).deg ≤ 4
  have h1 := totalDegree_X_sub_C a
  have h2 := totalDegree_C_sub_X b
  simp only [ivlSemiPf, WilkiesDesign.E.SemiPf.deg, WilkiesDesign.E.Basic.deg,
    WilkiesDesign.E.atomDeg, List.nil_append, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, add_zero]
  omega

/-! ## The cells are `*`-sets of format `1` and degree `4`, and sub-Pfaffian -/

/-- A singleton cell `{t}`, `|t| ≤ 1`, is a `*`-set of format `1` and degree `4`. -/
theorem pointPiece_star (t : ℝ) (ht : |t| ≤ 1) : Star 1 4 1 (cellPt t) := by
  refine ⟨[pointPiece t], ?_, ?_, ?_⟩
  · ext x
    simp [pointPiece_set t ht]
  · intro P hP
    rw [List.mem_singleton] at hP
    subst hP
    exact pointPiece_fmt t
  · simpa using pointPiece_deg t

/-- An interval cell `(a,b)` with `-1 ≤ a < b ≤ 1` is a `*`-set of format `1` and degree `4`. -/
theorem ivlPiece_star (a b : ℝ) (ha : -1 ≤ a) (hb : b ≤ 1) (hab : a < b) :
    Star 1 4 1 (cellIoo a b) := by
  refine ⟨[ivlPiece a b], ?_, ?_, ?_⟩
  · ext x
    simp [ivlPiece_set a b ha hb hab]
  · intro P hP
    rw [List.mem_singleton] at hP
    subst hP
    exact ivlPiece_fmt a b
  · simpa using ivlPiece_deg a b

/-- A singleton cell `{t}`, `|t| ≤ 1`, is a restricted sub-Pfaffian set (trivial fibration). -/
theorem pointPiece_subPf (t : ℝ) (ht : |t| ≤ 1) : SubPf 1 (cellPt t) := by
  refine ⟨0, ptSemiPf t, ?_⟩
  rw [set_ptSemiPf t ht, image_projFirst_one_zero]

/-- An interval cell `(a,b)` with `-1 ≤ a`, `b ≤ 1` is a restricted sub-Pfaffian set. -/
theorem ivlPiece_subPf (a b : ℝ) (ha : -1 ≤ a) (hb : b ≤ 1) : SubPf 1 (cellIoo a b) := by
  refine ⟨0, ivlSemiPf a b, ?_⟩
  rw [set_ivlSemiPf a b ha hb, image_projFirst_one_zero]

/-- **Dimension one cells are `*`-sets of format `1` and degree `4`, and sub-Pfaffian.**
Every cell cut out by a finite set of cut points of `[-1,1]` is a `*`-set of format `1` and
degree `4`, and a restricted sub-Pfaffian set. -/
theorem DimOneCellsStar (U : Finset ℝ) (hU : ∀ t ∈ U, |t| ≤ 1) :
    ∀ κ ∈ Work.WilE7.cuts U,
      WilkiesDesign.E.Star 1 4 1 κ ∧ WilkiesDesign.E.SubPf 1 κ := by
  intro κ hκ
  rcases mem_cuts.mp hκ with ⟨t, ht, rfl⟩ | ⟨a, ha, b, hb, hab, -, rfl⟩
  · exact ⟨pointPiece_star t (hU t ht), pointPiece_subPf t (hU t ht)⟩
  · have ha' : -1 ≤ a := (abs_le.mp (hU a ha)).1
    have hb' : b ≤ 1 := (abs_le.mp (hU b hb)).2
    exact ⟨ivlPiece_star a b ha' hb' hab, ivlPiece_subPf a b ha' hb'⟩

end Work.WilE7
