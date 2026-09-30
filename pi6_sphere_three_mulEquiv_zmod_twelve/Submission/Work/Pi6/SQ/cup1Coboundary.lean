import Mathlib
import Submission.Work.Pi6.SQ.Defs
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Pi6.SQ

noncomputable section

open Work.Cohomology (Cochain genEval cochainDiff cup cup1 Fface Gface Amap Qmap Wmap Ymap Delmap
  shmap frontIncl backIncl frontFace backFace genEval_cup1 genEval_cochainDiff sum_range_eq_fin
  face_F_le face_G_le face_F_mid face_G_mid face_F_gt face_G_gt
  Wcomp_zero Wcomp_top Wcomp_zero_of Wcomp_top_of Qcomp_zero Qcomp_top Qcomp_Y Qcomp_Y'
  Qcomp_zero_of Qcomp_top_of Amap_zero_eq_frontIncl mop
  cup_apply' cup_apply genEval_ext genEval_add genEval_cast frontIncl_comp_shmap backIncl_comp_shmap
  delta_comp_shmap)

/-! ## Casting helpers

Transport lemmas for cochains along equalities of degrees.  These are used to move between the
several degree expressions (`n+m-1+1`, `n+m`, `(n+1)+m-1`, ...) that occur in the statement. -/

lemma cup1Rec_irrel {α : ℕ → Type*} {p q : ℕ} (h h' : p = q) (x : α p) : h ▸ x = h' ▸ x := by
  cases h'; cases h; rfl

lemma cup1Rec_self {α : ℕ → Type*} {a : ℕ} (h : a = a) (x : α a) : h ▸ x = x := by
  cases h; rfl

lemma cup1Rec_trans {α : ℕ → Type*} {a b c : ℕ} (h₁ : a = b) (h₂ : b = c) (x : α a) :
    h₂ ▸ (h₁ ▸ x) = (h₁.trans h₂) ▸ x := by cases h₁; cases h₂; rfl

lemma cup1Rec_add {α : ℕ → Type*} [∀ k, Add (α k)] {p q : ℕ} (h : p = q) (x y : α p) :
    h ▸ (x + y) = h ▸ x + h ▸ y := by cases h; rfl

lemma cup1CochainDiff_cast {X : SSet} {p q : ℕ} (h : p = q) (c : Cochain F2 X p) :
    cochainDiff F2 X (h ▸ c) = (congrArg (fun k => k + 1) h) ▸ (cochainDiff F2 X c) := by
  cases h; rfl

/-! ## The interval maps of the shifted degrees -/

/-- `Fface`/`Gface` in degrees `(n+1, m)`, composed with the degree identification
`(n+1)+m-1 = n+m`, are the interval maps `Wmap`/`Ymap`. -/
theorem cup1ShmapFface (n m s : ℕ) (hs : s < m) (h : (n+1)+m-1 = n+m) :
    (CategoryTheory.CategoryStruct.comp (Work.Cohomology.Fface (n+1) m s (by omega))
        (Work.Cohomology.shmap ((n+1)+m-1) (n+m) h)
        = Work.Cohomology.Wmap n m s (by omega))
    ∧ (CategoryTheory.CategoryStruct.comp (Work.Cohomology.Gface (n+1) m s (by omega))
        (Work.Cohomology.shmap ((n+1)+m-1) (n+m) h)
        = Work.Cohomology.Ymap n m s (by omega)) := by
  constructor
  · refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
    apply Fin.ext
    rw [CategoryTheory.comp_apply]
    simp only [Work.Cohomology.shmap_val, Work.Cohomology.Fface_val, Work.Cohomology.Wmap_val]
  · refine ConcreteCategory.hom_ext _ _ (fun j => ?_)
    apply Fin.ext
    rw [CategoryTheory.comp_apply]
    simp only [Work.Cohomology.shmap_val, Work.Cohomology.Gface_apply]
    rw [Work.Cohomology.Gfun_val_if, Work.Cohomology.Ymap_val_if]
    split_ifs <;> omega

/-- `Fface`/`Gface` in degrees `(n, m+1)`, composed with the degree identification
`n+(m+1)-1 = n+m`, are the interval maps `Amap`/`Qmap`. -/
theorem cup1ShmapFfaceAmap (n m s : ℕ) (hs : s ≤ m) (h : n+(m+1)-1 = n+m) :
    (CategoryTheory.CategoryStruct.comp (Work.Cohomology.Fface n (m+1) s (by omega))
        (Work.Cohomology.shmap (n+(m+1)-1) (n+m) h)
        = Work.Cohomology.Amap n m s (by omega))
    ∧ (CategoryTheory.CategoryStruct.comp (Work.Cohomology.Gface n (m+1) s (by omega))
        (Work.Cohomology.shmap (n+(m+1)-1) (n+m) h)
        = Work.Cohomology.Qmap n m s (by omega)) := by
  constructor
  · refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
    apply Fin.ext
    rw [CategoryTheory.comp_apply]
    simp only [Work.Cohomology.shmap_val, Work.Cohomology.Fface_val, Work.Cohomology.Amap_val]
  · refine ConcreteCategory.hom_ext _ _ (fun j => ?_)
    apply Fin.ext
    rw [CategoryTheory.comp_apply]
    simp only [Work.Cohomology.shmap_val, Work.Cohomology.Gface_apply]
    rw [Work.Cohomology.Gfun_val_if, Work.Cohomology.Qmap_val_if]



/-! ## The combinatorial core

For a simplex `σ` of dimension `n+m`, `δ(u ∪₁ v)(σ)` expands as a double sum over the faces `k` of
`σ` and the cut points `s`; splitting the `k`-sum into the three regimes `k ≤ s`, `s < k ≤ s+n`,
`s+n < k` and applying the coboundary relations for `u` and `v` produces the four terms of the
coboundary formula. -/

open scoped CharTwo

lemma cup1GenEval_cochainDiff {X : SSet} {k : ℕ} (γ : Cochain F2 X k) (τ : X _⦋k+1⦌) :
    genEval F2 X (cochainDiff F2 X γ) τ = ∑ i : Fin (k+2), genEval F2 X γ (X.δ i τ) := by
  rw [genEval_cochainDiff]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp

lemma cup1GenEval_cup1 {X : SSet} (n m : ℕ) (α : Cochain F2 X n) (β : Cochain F2 X m)
    (τ : X _⦋n+m-1⦌) :
    genEval F2 X (cup1 F2 X n m α β) τ
      = ∑ s : Fin m, genEval F2 X α (X.map (Fface n m s.val (by have := s.isLt; omega)).op τ)
          * genEval F2 X β (X.map (Gface n m s.val (by have := s.isLt; omega)).op τ) := by
  rw [genEval_cup1]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp

lemma cup1F2_solve_add {a b c d : F2} (h : a + b + c = d) : b = d + a + c := by
  rw [← h]
  have h1 : a + b + c + a + c = a + a + (c + c + b) := by abel
  rw [h1, CharTwo.add_self_eq_zero a, CharTwo.add_self_eq_zero c]
  simp

lemma cup1F2_solve_add' {a b c : F2} (h : a + b = c) : a = c + b := by
  rw [← h, add_assoc, CharTwo.add_self_eq_zero, add_zero]

lemma cup1Rec_congr {α : ℕ → Type*} {p q : ℕ} (h : p = q) {x y : α p} (e : x = y) :
    h ▸ x = h ▸ y := by
  cases h
  exact e

theorem cup1SimplexCore (X : SSet) (n m : ℕ) (α : Cochain F2 X n) (β : Cochain F2 X m)
    (hn : 1 ≤ n) (hm : 1 ≤ m) (σ : X _⦋n+m⦌) :
    (∑ k : Fin (n+m+1), ∑ s : Fin m,
        genEval F2 X α (X.map (Fface n m s.val (by have := s.isLt; omega)).op
              (X.map (Delmap n m k.val (by omega)).op σ))
        * genEval F2 X β (X.map (Gface n m s.val (by have := s.isLt; omega)).op
              (X.map (Delmap n m k.val (by omega)).op σ)))
      = (∑ s : Fin m, genEval F2 X (cochainDiff F2 X α)
            (X.map (Wmap n m s.val (by have := s.isLt; omega)).op σ)
            * genEval F2 X β (X.map (Ymap n m s.val (by have := s.isLt; omega)).op σ))
        + (∑ t : Fin (m+1), genEval F2 X α (X.map (Amap n m t.val (by have := t.isLt; omega)).op σ)
            * genEval F2 X (cochainDiff F2 X β)
                (X.map (Qmap n m t.val (by have := t.isLt; omega)).op σ))
        + genEval F2 X α (X.map (frontIncl n (n+m) (by omega)).op σ)
          * genEval F2 X β (X.map (backIncl n m).op σ)
        + genEval F2 X β (X.map (frontIncl m (n+m) (by omega)).op σ)
          * genEval F2 X α (X.map (Amap n m m (by omega)).op σ) := by
  -- abbreviations
  let Df : ℕ → X _⦋n+m-1⦌ := fun k =>
    if _ : k ≤ n+m then X.map (Delmap n m k (by omega)).op σ
      else X.map (Delmap n m 0 (by omega)).op σ
  let TFf : ℕ → Fin m → F2 := fun k s =>
    genEval F2 X α (X.map (Fface n m s.val (by have := s.isLt; omega)).op (Df k)) *
      genEval F2 X β (X.map (Gface n m s.val (by have := s.isLt; omega)).op (Df k))
  let AQ : ℕ → X _⦋n⦌ := fun t => if _ : t ≤ m then X.map (Amap n m t (by omega)).op σ
    else X.map (Amap n m 0 (by omega)).op σ
  let QQ : ℕ → ℕ → X _⦋m⦌ := fun t p => if _ : t ≤ m then
      (if _ : p ≤ m+1 then
        X.map ((SimplexCategory.δ (⟨p, by omega⟩ : Fin (m+2))) ≫ Qmap n m t (by omega)).op σ
        else X.map (backIncl n m).op σ)
    else X.map (backIncl n m).op σ
  let WQ : ℕ → ℕ → X _⦋n⦌ := fun s j => if _ : s < m then
      (if _ : j ≤ n+1 then
        X.map ((SimplexCategory.δ (⟨j, by omega⟩ : Fin (n+2))) ≫ Wmap n m s (by omega)).op σ
        else X.map (frontIncl n (n+m) (by omega)).op σ)
    else X.map (frontIncl n (n+m) (by omega)).op σ
  let YQ : ℕ → X _⦋m⦌ := fun s => if _ : s < m then X.map (Ymap n m s (by omega)).op σ
    else X.map (backIncl n m).op σ
  have hLHS : (∑ k : Fin (n+m+1), ∑ s : Fin m, TFf k.val s)
      = (∑ k : Fin (n+m+1), ∑ s : Fin m,
          genEval F2 X α (X.map (Fface n m s.val (by have := s.isLt; omega)).op
                (X.map (Delmap n m k.val (by omega)).op σ))
          * genEval F2 X β (X.map (Gface n m s.val (by have := s.isLt; omega)).op
                (X.map (Delmap n m k.val (by omega)).op σ))) := by
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun s _ => ?_
    simp only [TFf, Df, dif_pos (by have := k.isLt; omega : k.val ≤ n+m)]
  rw [← hLHS]
  -- the three regimes
  let P1 : Fin m → F2 := fun s => ∑ k ∈ Finset.range (s.val+1),
      genEval F2 X α (AQ (s.val+1)) * genEval F2 X β (QQ (s.val+1) k)
  let P2 : Fin m → F2 := fun s => (∑ j ∈ Finset.range n,
      genEval F2 X α (WQ s.val (j+1))) * genEval F2 X β (YQ s.val)
  let P3 : Fin m → F2 := fun s => ∑ i ∈ Finset.range (m - s.val),
      genEval F2 X α (AQ s.val) * genEval F2 X β (QQ s.val (s.val+2+i))
  have hsplit : ∀ s : Fin m, (∑ k : Fin (n+m+1), TFf k.val s) = P1 s + P2 s + P3 s := by
    intro s
    rw [← sum_range_eq_fin (n+m+1) (fun k => TFf k s)]
    have h2 : (∑ k ∈ Finset.range (n+m+1), TFf k s)
        = (∑ k ∈ Finset.range (s.val+1), TFf k s)
          + ∑ j ∈ Finset.range (n+m-s.val), TFf (s.val+1+j) s := by
      rw [show n+m+1 = (s.val+1)+(n+m-s.val) by omega]
      exact Finset.sum_range_add (fun k => TFf k s) (s.val+1) (n+m-s.val)
    have h3 : (∑ j ∈ Finset.range (n+m-s.val), TFf (s.val+1+j) s)
        = (∑ j ∈ Finset.range n, TFf (s.val+1+j) s)
          + ∑ i ∈ Finset.range (m-s.val), TFf (s.val+1+(n+i)) s := by
      rw [show n+m-s.val = n + (m-s.val) by omega]
      exact Finset.sum_range_add (fun j => TFf (s.val+1+j) s) n (m-s.val)
    have e1 : (∑ k ∈ Finset.range (s.val+1), TFf k s) = P1 s := by
      simp only [P1]
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [Finset.mem_range] at hk
      simp only [TFf, Df, AQ, QQ, dif_pos (by omega : k ≤ n+m), dif_pos (by omega : s.val+1 ≤ m),
        dif_pos (by omega : k ≤ m+1)]
      rw [face_F_le σ k s.val (by omega) s.isLt, face_G_le σ k s.val (by omega) s.isLt]
      try ring
    have e2 : (∑ j ∈ Finset.range n, TFf (s.val+1+j) s) = P2 s := by
      simp only [P2, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [Finset.mem_range] at hj
      simp only [TFf, Df, WQ, YQ, dif_pos (by omega : s.val+1+j ≤ n+m), dif_pos s.isLt,
        dif_pos (by omega : j+1 ≤ n+1)]
      rw [face_F_mid σ (s.val+1+j) s.val (by omega) (by omega) s.isLt,
          face_G_mid σ (s.val+1+j) s.val (by omega) (by omega) s.isLt]
      rw [show (⟨(s.val+1+j) - s.val, by omega⟩ : Fin (n+2)) = ⟨j+1, by omega⟩ from
            Fin.ext (by simp only [Fin.val_mk]; omega)]
      try ring
    have e3 : (∑ i ∈ Finset.range (m-s.val), TFf (s.val+1+(n+i)) s) = P3 s := by
      simp only [P3]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [Finset.mem_range] at hi
      simp only [TFf, Df, AQ, QQ, dif_pos (by omega : s.val+1+(n+i) ≤ n+m),
        dif_pos (by omega : s.val ≤ m), dif_pos (by omega : s.val+2+i ≤ m+1)]
      rw [face_F_gt σ (s.val+1+(n+i)) s.val (by omega) s.isLt,
          face_G_gt σ (s.val+1+(n+i)) s.val (by omega) (by omega) s.isLt]
      rw [show (⟨(s.val+1+(n+i)) - n + 1, by omega⟩ : Fin (m+2)) = ⟨s.val+2+i, by omega⟩ from
            Fin.ext (by simp only [Fin.val_mk]; omega)]
      try ring
    rw [h2, h3, e1, e2, e3]
    ring
  -- the `α`-coboundary relation on the middle `(n+1)`-simplex
  have hmid : ∀ s : Fin m,
      (∑ j ∈ Finset.range n, genEval F2 X α (WQ s.val (j+1)))
        = genEval F2 X (cochainDiff F2 X α)
            (X.map (Wmap n m s.val (by have := s.isLt; omega)).op σ)
          + genEval F2 X α (AQ (s.val+1)) + genEval F2 X α (AQ s.val) := by
    intro s
    have hrel : (∑ j ∈ Finset.range (n+2), genEval F2 X α (WQ s.val j))
        = genEval F2 X (cochainDiff F2 X α)
            (X.map (Wmap n m s.val (by have := s.isLt; omega)).op σ) := by
      have hh : (∑ j : Fin (n+2),
            genEval F2 X α (X.δ j (X.map (Wmap n m s.val (by have := s.isLt; omega)).op σ)))
          = ∑ j : Fin (n+2), genEval F2 X α (WQ s.val (j:ℕ)) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [show X.δ j (X.map (Wmap n m s.val (by have := s.isLt; omega)).op σ) = WQ s.val (j:ℕ) from by
          rw [SimplicialObject.δ_def, mop]
          simp only [WQ, dif_pos s.isLt, dif_pos (by omega : (j:ℕ) ≤ n+1)]]
      rw [cup1GenEval_cochainDiff, hh, sum_range_eq_fin (n+2) (fun j => genEval F2 X α (WQ s.val j))]
    have hsplitW : (∑ j ∈ Finset.range (n+2), genEval F2 X α (WQ s.val j))
        = genEval F2 X α (WQ s.val 0)
          + (∑ j ∈ Finset.range n, genEval F2 X α (WQ s.val (j+1)))
          + genEval F2 X α (WQ s.val (n+1)) := by
      rw [show n+2 = (n+1)+1 by omega, Finset.sum_range_succ, Finset.sum_range_succ']
      ring
    rw [hsplitW] at hrel
    rw [show WQ s.val 0 = AQ (s.val+1) from by
        dsimp only [WQ, AQ]
        rw [dif_pos s.isLt, dif_pos (by omega : (0:ℕ) ≤ n+1), dif_pos (by omega : s.val+1 ≤ m)]
        exact Wcomp_zero_of σ s.val s.isLt (⟨0, by omega⟩ : Fin (n+2)) rfl] at hrel
    rw [show WQ s.val (n+1) = AQ s.val from by
        dsimp only [WQ, AQ]
        rw [dif_pos s.isLt, dif_pos (by omega : n+1 ≤ n+1), dif_pos (by omega : s.val ≤ m)]
        exact Wcomp_top_of σ s.val s.isLt (⟨n+1, by omega⟩ : Fin (n+2)) rfl] at hrel
    exact cup1F2_solve_add hrel
  have hP2 : ∀ s : Fin m, P2 s
      = genEval F2 X (cochainDiff F2 X α)
            (X.map (Wmap n m s.val (by have := s.isLt; omega)).op σ) * genEval F2 X β (YQ s.val)
        + genEval F2 X α (AQ (s.val+1)) * genEval F2 X β (YQ s.val)
        + genEval F2 X α (AQ s.val) * genEval F2 X β (YQ s.val) := by
    intro s
    simp only [P2]
    rw [hmid s, add_mul, add_mul]
  -- the `Q1`, `Q3` blocks
  let Q1 : Fin m → F2 := fun s => genEval F2 X α (AQ (s.val+1)) *
      ∑ k ∈ Finset.range (s.val+2), genEval F2 X β (QQ (s.val+1) k)
  let Q3 : Fin m → F2 := fun s => genEval F2 X α (AQ s.val) *
      ∑ i ∈ Finset.range (m+1-s.val), genEval F2 X β (QQ s.val (s.val+1+i))
  have ha : ∀ s : Fin m,
      P1 s + genEval F2 X α (AQ (s.val+1)) * genEval F2 X β (YQ s.val) = Q1 s := by
    intro s
    simp only [P1, Q1]
    rw [show YQ s.val = QQ (s.val+1) (s.val+1) from by
      dsimp only [YQ, QQ]
      rw [dif_pos s.isLt, dif_pos (by omega : s.val+1 ≤ m), dif_pos (by omega : s.val+1 ≤ m+1)]
      exact (Qcomp_Y' σ s.val s.isLt).symm]
    rw [Finset.sum_range_succ (fun k => genEval F2 X β (QQ (s.val+1) k)) (s.val+1), mul_add,
      Finset.mul_sum]
  have hb : ∀ s : Fin m,
      P3 s + genEval F2 X α (AQ s.val) * genEval F2 X β (YQ s.val) = Q3 s := by
    intro s
    simp only [P3, Q3]
    rw [show YQ s.val = QQ s.val (s.val+1) from by
      dsimp only [YQ, QQ]
      rw [dif_pos s.isLt, dif_pos (by omega : s.val ≤ m), dif_pos (by omega : s.val+1 ≤ m+1)]
      exact (Qcomp_Y σ s.val s.isLt).symm]
    rw [show (∑ i ∈ Finset.range (m+1-s.val), genEval F2 X β (QQ s.val (s.val+1+i)))
        = (∑ i ∈ Finset.range (m-s.val), genEval F2 X β (QQ s.val (s.val+1+(i+1))))
          + genEval F2 X β (QQ s.val (s.val+1)) from by
      rw [show m+1-s.val = (m-s.val)+1 by omega]
      rw [Finset.sum_range_succ']]
    rw [show (∑ i ∈ Finset.range (m-s.val), genEval F2 X β (QQ s.val (s.val+1+(i+1))))
        = (∑ i ∈ Finset.range (m-s.val), genEval F2 X β (QQ s.val (s.val+2+i))) from by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [show s.val+1+(i+1) = s.val+2+i by omega]]
    rw [mul_add, Finset.mul_sum]
  have hrelB : ∀ (t : ℕ) (ht : t ≤ m),
      (∑ p ∈ Finset.range (m+2), genEval F2 X β (QQ t p))
        = genEval F2 X (cochainDiff F2 X β) (X.map (Qmap n m t ht).op σ) := by
    intro t ht
    have hh : (∑ p : Fin (m+2), genEval F2 X β (X.δ p (X.map (Qmap n m t ht).op σ)))
        = ∑ p : Fin (m+2), genEval F2 X β (QQ t (p:ℕ)) := by
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [show X.δ p (X.map (Qmap n m t ht).op σ) = QQ t (p:ℕ) from by
        rw [SimplicialObject.δ_def, mop]
        simp only [QQ, dif_pos ht, dif_pos (by omega : (p:ℕ) ≤ m+1)]]
    rw [cup1GenEval_cochainDiff, hh, sum_range_eq_fin (m+2) (fun p => genEval F2 X β (QQ t p))]
  have hsplitQ : ∀ (t : ℕ) (ht : t ≤ m),
      (∑ p ∈ Finset.range (m+2), genEval F2 X β (QQ t p))
        = (∑ k ∈ Finset.range (t+1), genEval F2 X β (QQ t k))
          + (∑ i ∈ Finset.range (m+1-t), genEval F2 X β (QQ t (t+1+i))) := by
    intro t ht
    rw [show m+2 = (t+1) + (m+1-t) by omega]
    exact Finset.sum_range_add (fun p => genEval F2 X β (QQ t p)) (t+1) (m+1-t)
  have hbeta : ∀ (t : ℕ) (ht : t ≤ m),
      (∑ k ∈ Finset.range (t+1), genEval F2 X β (QQ t k))
        + (∑ i ∈ Finset.range (m+1-t), genEval F2 X β (QQ t (t+1+i)))
      = genEval F2 X (cochainDiff F2 X β) (X.map (Qmap n m t ht).op σ) := by
    intro t ht
    rw [← hsplitQ t ht, hrelB t ht]
  let B1 : ℕ → F2 := fun t => genEval F2 X α (AQ t) *
      ∑ k ∈ Finset.range (t+1), genEval F2 X β (QQ t k)
  let B2 : ℕ → F2 := fun t => genEval F2 X α (AQ t) *
      ∑ i ∈ Finset.range (m+1-t), genEval F2 X β (QQ t (t+1+i))
  have hcancel : ∀ (t : ℕ) (ht : t ≤ m), B1 t + B2 t
      = genEval F2 X α (AQ t)
        * genEval F2 X (cochainDiff F2 X β) (X.map (Qmap n m t ht).op σ) := by
    intro t ht
    simp only [B1, B2]
    rw [← mul_add, hbeta t ht]
  have hcancelQ : ∀ (t : ℕ) (ht : t ≤ m), B1 t + B2 t
      = genEval F2 X α (AQ t) * ∑ p ∈ Finset.range (m+2), genEval F2 X β (QQ t p) := by
    intro t ht
    simp only [B1, B2]
    rw [← mul_add, hsplitQ t ht]
  have hB10 : B1 0 = genEval F2 X α (AQ 0)
      * genEval F2 X β (X.map (backIncl n m).op σ) := by
    simp only [B1, Finset.range_one, Finset.sum_singleton, Nat.zero_add]
    rw [show QQ 0 0 = X.map (backIncl n m).op σ from by
      dsimp only [QQ]
      rw [dif_pos (by omega : (0:ℕ) ≤ m), dif_pos (by omega : (0:ℕ) ≤ m+1)]
      exact Qcomp_zero σ]
  have hB2m : B2 m = genEval F2 X α (AQ m)
      * genEval F2 X β (X.map (frontIncl m (n+m) (by omega)).op σ) := by
    simp only [B2]
    rw [show m+1-m = 1 by omega, Finset.range_one, Finset.sum_singleton]
    rw [show QQ m (m+1) = X.map (frontIncl m (n+m) (by omega)).op σ from by
      dsimp only [QQ]
      rw [dif_pos (by omega : m ≤ m), dif_pos (by omega : m+1 ≤ m+1)]
      exact Qcomp_top σ]
  have hQ1step : ∀ s : Fin m, Q1 s = B1 (s.val+1) := by
    intro s
    simp only [Q1, B1]
  have hQ3step : ∀ s : Fin m, Q3 s = B2 s.val := by
    intro s
    simp only [Q3, B2]
  have hQ1sum : (∑ s : Fin m, Q1 s) + B1 0 = ∑ t ∈ Finset.range (m+1), B1 t := by
    have h1 : (∑ s : Fin m, Q1 s) = ∑ t ∈ Finset.range m, B1 (t+1) := by
      rw [sum_range_eq_fin m (fun t => B1 (t+1))]
    rw [h1, ← Finset.sum_range_succ' B1 m]
  have hQ3sum : (∑ s : Fin m, Q3 s) + B2 m = ∑ t ∈ Finset.range (m+1), B2 t := by
    have h1 : (∑ s : Fin m, Q3 s) = ∑ t ∈ Finset.range m, B2 t := by
      rw [sum_range_eq_fin m (fun t => B2 t)]
    rw [h1, Finset.sum_range_succ]
  have hBM : (∑ s : Fin m, Q1 s) + (∑ s : Fin m, Q3 s)
      = (∑ t ∈ Finset.range (m+1), genEval F2 X α (AQ t)
          * ∑ p ∈ Finset.range (m+2), genEval F2 X β (QQ t p))
        + B1 0 + B2 m := by
    have e1 : (∑ s : Fin m, Q1 s) = (∑ t ∈ Finset.range (m+1), B1 t) + B1 0 :=
      cup1F2_solve_add' hQ1sum
    have e2 : (∑ s : Fin m, Q3 s) = (∑ t ∈ Finset.range (m+1), B2 t) + B2 m :=
      cup1F2_solve_add' hQ3sum
    rw [e1, e2]
    rw [show (∑ t ∈ Finset.range (m+1), B1 t) + B1 0
          + ((∑ t ∈ Finset.range (m+1), B2 t) + B2 m)
        = ((∑ t ∈ Finset.range (m+1), B1 t) + (∑ t ∈ Finset.range (m+1), B2 t))
          + B1 0 + B2 m from by ring]
    rw [← Finset.sum_add_distrib]
    have hc : (∑ t ∈ Finset.range (m+1), (B1 t + B2 t))
        = ∑ t ∈ Finset.range (m+1), genEval F2 X α (AQ t)
            * ∑ p ∈ Finset.range (m+2), genEval F2 X β (QQ t p) := by
      refine Finset.sum_congr rfl fun t ht => ?_
      rw [Finset.mem_range] at ht
      exact hcancelQ t (by omega)
    rw [hc]
  -- identifications of the blocks with the four terms of the formula
  have hG : (∑ s : Fin m, genEval F2 X (cochainDiff F2 X α)
        (X.map (Wmap n m s.val (by have := s.isLt; omega)).op σ) * genEval F2 X β (YQ s.val))
      = (∑ s : Fin m, genEval F2 X (cochainDiff F2 X α)
          (X.map (Wmap n m s.val (by have := s.isLt; omega)).op σ)
          * genEval F2 X β (X.map (Ymap n m s.val (by have := s.isLt; omega)).op σ)) := by
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [show YQ s.val = X.map (Ymap n m s.val (by have := s.isLt; omega)).op σ from by
      dsimp only [YQ]
      rw [dif_pos s.isLt]]
  have hQs : (∑ t ∈ Finset.range (m+1), genEval F2 X α (AQ t)
        * ∑ p ∈ Finset.range (m+2), genEval F2 X β (QQ t p))
      = (∑ t : Fin (m+1), genEval F2 X α (X.map (Amap n m t.val (by have := t.isLt; omega)).op σ)
          * genEval F2 X (cochainDiff F2 X β)
              (X.map (Qmap n m t.val (by have := t.isLt; omega)).op σ)) := by
    rw [sum_range_eq_fin (m+1) (fun t => genEval F2 X α (AQ t)
      * ∑ p ∈ Finset.range (m+2), genEval F2 X β (QQ t p))]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [hrelB t.val (by have := t.isLt; omega)]
    rw [show AQ t.val = X.map (Amap n m t.val (by have := t.isLt; omega)).op σ from by
      dsimp only [AQ]
      rw [dif_pos (by have := t.isLt; omega : t.val ≤ m)]]
  have hE1 : AQ 0 = X.map (frontIncl n (n+m) (by omega)).op σ := by
    dsimp only [AQ]
    rw [dif_pos (by omega : (0:ℕ) ≤ m), Amap_zero_eq_frontIncl]
  have hE2 : AQ m = X.map (Amap n m m (by omega)).op σ := by
    dsimp only [AQ]
    rw [dif_pos (by omega : m ≤ m)]
  -- assembly
  have h1 : ∀ s : Fin m, P1 s + P2 s + P3 s
      = genEval F2 X (cochainDiff F2 X α)
            (X.map (Wmap n m s.val (by have := s.isLt; omega)).op σ) * genEval F2 X β (YQ s.val)
          + Q1 s + Q3 s := by
    intro s
    rw [hP2 s]
    rw [show P1 s + (genEval F2 X (cochainDiff F2 X α)
            (X.map (Wmap n m s.val (by have := s.isLt; omega)).op σ) * genEval F2 X β (YQ s.val)
          + genEval F2 X α (AQ (s.val+1)) * genEval F2 X β (YQ s.val)
          + genEval F2 X α (AQ s.val) * genEval F2 X β (YQ s.val)) + P3 s
        = genEval F2 X (cochainDiff F2 X α)
            (X.map (Wmap n m s.val (by have := s.isLt; omega)).op σ) * genEval F2 X β (YQ s.val)
          + (P1 s + genEval F2 X α (AQ (s.val+1)) * genEval F2 X β (YQ s.val))
          + (P3 s + genEval F2 X α (AQ s.val) * genEval F2 X β (YQ s.val)) from by ring]
    rw [ha s, hb s]
  have hPsum : (∑ s : Fin m, (P1 s + P2 s + P3 s))
      = (∑ s : Fin m, genEval F2 X (cochainDiff F2 X α)
            (X.map (Wmap n m s.val (by have := s.isLt; omega)).op σ) * genEval F2 X β (YQ s.val))
        + (∑ s : Fin m, Q1 s) + (∑ s : Fin m, Q3 s) := by
    rw [Finset.sum_congr rfl (fun s _ => h1 s), Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [Finset.sum_comm, Finset.sum_congr rfl (fun s _ => hsplit s), hPsum]
  rw [show (∑ s : Fin m, genEval F2 X (cochainDiff F2 X α)
          (X.map (Wmap n m s.val (by have := s.isLt; omega)).op σ) * genEval F2 X β (YQ s.val))
        + (∑ s : Fin m, Q1 s) + (∑ s : Fin m, Q3 s)
      = (∑ s : Fin m, genEval F2 X (cochainDiff F2 X α)
          (X.map (Wmap n m s.val (by have := s.isLt; omega)).op σ) * genEval F2 X β (YQ s.val))
        + ((∑ s : Fin m, Q1 s) + (∑ s : Fin m, Q3 s)) from by ring]
  rw [hBM, hB10, hB2m, hG, hQs, hE1, hE2]
  ring

/-! ## Unfolding the four terms on a simplex -/

lemma cup1ShiftedLeft (X : SSet) (n m : ℕ) (α : Cochain F2 X n) (β : Cochain F2 X m)
    (h1 : (n+1)+m-1 = n+m) (σ : X _⦋n+m⦌) :
    genEval F2 X (cup1 F2 X (n+1) m (cochainDiff F2 X α) β)
        (X.map (shmap ((n+1)+m-1) (n+m) h1).op σ)
      = ∑ s : Fin m, genEval F2 X (cochainDiff F2 X α)
            (X.map (Wmap n m s.val (by have := s.isLt; omega)).op σ)
          * genEval F2 X β (X.map (Ymap n m s.val (by have := s.isLt; omega)).op σ) := by
  rw [cup1GenEval_cup1]
  refine Finset.sum_congr rfl fun s _ => ?_
  obtain ⟨hf, hg⟩ := cup1ShmapFface n m s.val s.isLt h1
  rw [mop (shmap ((n+1)+m-1) (n+m) h1)
        (Fface (n+1) m s.val (by have := s.isLt; omega)) σ, hf,
      mop (shmap ((n+1)+m-1) (n+m) h1)
        (Gface (n+1) m s.val (by have := s.isLt; omega)) σ, hg]

lemma cup1ShiftedRight (X : SSet) (n m : ℕ) (α : Cochain F2 X n) (β : Cochain F2 X m)
    (h2 : n+(m+1)-1 = n+m) (σ : X _⦋n+m⦌) :
    genEval F2 X (cup1 F2 X n (m+1) α (cochainDiff F2 X β))
        (X.map (shmap (n+(m+1)-1) (n+m) h2).op σ)
      = ∑ t : Fin (m+1), genEval F2 X α
            (X.map (Amap n m t.val (by have := t.isLt; omega)).op σ)
          * genEval F2 X (cochainDiff F2 X β)
              (X.map (Qmap n m t.val (by have := t.isLt; omega)).op σ) := by
  rw [cup1GenEval_cup1]
  refine Finset.sum_congr rfl fun t _ => ?_
  obtain ⟨hf, hg⟩ := cup1ShmapFfaceAmap n m t.val (by have := t.isLt; omega) h2
  rw [mop (shmap (n+(m+1)-1) (n+m) h2)
        (Fface n (m+1) t.val (by have := t.isLt; omega)) σ, hf,
      mop (shmap (n+(m+1)-1) (n+m) h2)
        (Gface n (m+1) t.val (by have := t.isLt; omega)) σ, hg]

lemma cup1CupAlphaBetaUnfold (X : SSet) (n m : ℕ) (α : Cochain F2 X n) (β : Cochain F2 X m)
    (σ : X _⦋n+m⦌) :
    genEval F2 X (cup F2 X α β) σ
      = genEval F2 X α (X.map (frontIncl n (n+m) (by omega)).op σ)
        * genEval F2 X β (X.map (backIncl n m).op σ) := by
  rw [cup_apply']
  simp only [frontFace, backFace]

lemma cup1Shmap_congr {p q : ℕ} (h h' : p = q) : shmap p q h = shmap p q h' := by
  simp only [shmap]

lemma cupBetaAlphaUnfoldF2 (X : SSet) (n m : ℕ) (α : Cochain F2 X n) (β : Cochain F2 X m)
    (h3 : m+n = n+m) (σ : X _⦋n+m⦌) :
    genEval F2 X (cup F2 X β α) (X.map (shmap (m+n) (n+m) h3).op σ)
      = genEval F2 X β (X.map (frontIncl m (n+m) (by omega)).op σ)
        * genEval F2 X α (X.map (Amap n m m (by omega)).op σ) := by
  rw [cup_apply']
  simp only [frontFace, backFace]
  rw [show shmap (m+n) (n+m) h3 = shmap (m+n) (n+m) (Nat.add_comm m n) from cup1Shmap_congr h3 _]
  rw [mop (shmap (m+n) (n+m) (Nat.add_comm m n)) (frontIncl m (m+n) (by omega)) σ,
      mop (shmap (m+n) (n+m) (Nat.add_comm m n)) (backIncl m n) σ]
  rw [frontIncl_comp_shmap, backIncl_comp_shmap]

/-- The casted form of `cup1ShiftedLeft`. -/
lemma cup1ShiftedLeftCast (X : SSet) (n m : ℕ) (α : Cochain F2 X n) (β : Cochain F2 X m)
    (h1 : (n+1)+m-1 = n+m) (σ : X _⦋n+m⦌) :
    genEval F2 X (h1 ▸ cup1 F2 X (n+1) m (cochainDiff F2 X α) β) σ
      = ∑ s : Fin m, genEval F2 X (cochainDiff F2 X α)
            (X.map (Wmap n m s.val (by have := s.isLt; omega)).op σ)
          * genEval F2 X β (X.map (Ymap n m s.val (by have := s.isLt; omega)).op σ) := by
  have h := genEval_cast (R := F2) (X := X) (p := (n+1)+m-1) (q := n+m) h1
    (cup1 F2 X (n+1) m (cochainDiff F2 X α) β) σ
  rw [h]
  exact cup1ShiftedLeft X n m α β h1 σ

/-- The casted form of `cup1ShiftedRight`. -/
lemma cup1ShiftedRightCast (X : SSet) (n m : ℕ) (α : Cochain F2 X n) (β : Cochain F2 X m)
    (h2 : n+(m+1)-1 = n+m) (σ : X _⦋n+m⦌) :
    genEval F2 X (h2 ▸ cup1 F2 X n (m+1) α (cochainDiff F2 X β)) σ
      = ∑ t : Fin (m+1), genEval F2 X α
            (X.map (Amap n m t.val (by have := t.isLt; omega)).op σ)
          * genEval F2 X (cochainDiff F2 X β)
              (X.map (Qmap n m t.val (by have := t.isLt; omega)).op σ) := by
  have h := genEval_cast (R := F2) (X := X) (p := n+(m+1)-1) (q := n+m) h2
    (cup1 F2 X n (m+1) α (cochainDiff F2 X β)) σ
  rw [h]
  exact cup1ShiftedRight X n m α β h2 σ

/-- The casted form of `cupBetaAlphaUnfoldF2`. -/
lemma cup1CupBetaAlphaCast (X : SSet) (n m : ℕ) (α : Cochain F2 X n) (β : Cochain F2 X m)
    (h3 : m+n = n+m) (σ : X _⦋n+m⦌) :
    genEval F2 X (h3 ▸ cup F2 X β α) σ
      = genEval F2 X β (X.map (frontIncl m (n+m) (by omega)).op σ)
        * genEval F2 X α (X.map (Amap n m m (by omega)).op σ) := by
  have h := genEval_cast (R := F2) (X := X) (p := m+n) (q := n+m) h3 (cup F2 X β α) σ
  rw [h]
  exact cupBetaAlphaUnfoldF2 X n m α β h3 σ


/-! ## Expansion of the coboundary of `u ∪₁ v` on a simplex -/

lemma cup1DeltaExpandF2 (X : SSet) (n m : ℕ) (α : Cochain F2 X n) (β : Cochain F2 X m)
    (hn : 1 ≤ n) (hm : 1 ≤ m) (hcast : n+m-1+1 = n+m) (σ : X _⦋n+m⦌) :
    genEval F2 X (cochainDiff F2 X (cup1 F2 X n m α β))
        (X.map (shmap (n+m-1+1) (n+m) hcast).op σ)
      = ∑ k : Fin (n+m+1), ∑ s : Fin m,
          genEval F2 X α (X.map (Fface n m s.val (by have := s.isLt; omega)).op
                (X.map (Delmap n m k.val (by omega)).op σ))
          * genEval F2 X β (X.map (Gface n m s.val (by have := s.isLt; omega)).op
                (X.map (Delmap n m k.val (by omega)).op σ)) := by
  let Df : ℕ → X _⦋n+m-1⦌ := fun k =>
    if _ : k ≤ n+m then X.map (Delmap n m k (by omega)).op σ
      else X.map (Delmap n m 0 (by omega)).op σ
  rw [cup1GenEval_cochainDiff]
  have h2 : (∑ i : Fin ((n+m-1)+2), genEval F2 X (cup1 F2 X n m α β)
        (X.δ i (X.map (shmap (n+m-1+1) (n+m) hcast).op σ)))
      = ∑ i : Fin ((n+m-1)+2), genEval F2 X (cup1 F2 X n m α β) (Df (i:ℕ)) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    have hi : (i:ℕ) ≤ n+m := by have := i.isLt; omega
    rw [show Df (i:ℕ) = X.map (Delmap n m (i:ℕ) (by omega)).op σ from by
      simp only [Df, dif_pos hi]]
    rw [SimplicialObject.δ_def, mop, delta_comp_shmap]
  rw [h2, Fin.sum_univ_eq_sum_range (fun i => genEval F2 X (cup1 F2 X n m α β) (Df i))
    ((n+m-1)+2)]
  rw [show (n+m-1)+2 = n+m+1 by omega]
  rw [← sum_range_eq_fin (n+m+1) (fun k => ∑ s : Fin m,
      genEval F2 X α (X.map (Fface n m s.val (by have := s.isLt; omega)).op
            (X.map (Delmap n m k (by omega)).op σ))
      * genEval F2 X β (X.map (Gface n m s.val (by have := s.isLt; omega)).op
            (X.map (Delmap n m k (by omega)).op σ)))]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.mem_range] at hk
  rw [cup1GenEval_cup1]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [show Df k = X.map (Delmap n m k (by omega)).op σ from by
    simp only [Df, dif_pos (by omega : k ≤ n+m)]]

/-! ## The mod-2 cup-1 coboundary formula for the library product -/

theorem cup1_library_gen (X : SSet) (n m : ℕ) (α : Cochain F2 X n) (β : Cochain F2 X m)
    (hn : 1 ≤ n) (hm : 1 ≤ m)
    (hcast : n+m-1+1 = n+m) (h1 : (n+1)+m-1 = n+m) (h2 : n+(m+1)-1 = n+m)
    (h3 : m+n = n+m) :
    hcast ▸ cochainDiff F2 X (cup1 F2 X n m α β)
      = h1 ▸ cup1 F2 X (n+1) m (cochainDiff F2 X α) β
        + h2 ▸ cup1 F2 X n (m+1) α (cochainDiff F2 X β)
        + cup F2 X α β + h3 ▸ cup F2 X β α := by
  apply genEval_ext
  intro σ
  have hL : genEval F2 X (hcast ▸ cochainDiff F2 X (cup1 F2 X n m α β)) σ
      = genEval F2 X (cochainDiff F2 X (cup1 F2 X n m α β))
          (X.map (shmap (n+m-1+1) (n+m) hcast).op σ) := genEval_cast hcast _ σ
  rw [hL, cup1DeltaExpandF2 X n m α β hn hm hcast σ, genEval_add, genEval_add, genEval_add,
    cup1ShiftedLeftCast X n m α β h1 σ, cup1ShiftedRightCast X n m α β h2 σ,
    cup1CupAlphaBetaUnfold X n m α β σ, cup1CupBetaAlphaCast X n m α β h3 σ]
  exact cup1SimplexCore X n m α β hn hm σ

/-! ## The coboundary formula for `cup1m` -/

/-- The coboundary formula for `cup1m`, with the degree identifications as explicit hypotheses. -/
lemma cup1mCoboundaryGen (X : SSet) (n m : ℕ) (u : Cochain F2 X n) (v : Cochain F2 X m)
    (hn : 1 ≤ n) (hm : 1 ≤ m)
    (hA : (n+m-1)+1 = n+m) (hvu : m+n = n+m) (h3 : (n+1)+m-1 = n+m)
    (h4 : n+(m+1)-1 = n+m) :
    hA ▸ cochainDiff F2 X (cup1m X n m u v)
      = cup F2 X u v + hvu ▸ cup F2 X v u
        + h3 ▸ cup1m X (n+1) m (cochainDiff F2 X u) v
        + h4 ▸ cup1m X n (m+1) u (cochainDiff F2 X v) := by
  have hS : m+n-1 = n+m-1 := congrArg (fun k => k - 1) (Nat.add_comm m n)
  have hS1 : m+(n+1)-1 = (n+1)+m-1 := congrArg (fun k => k - 1) (Nat.add_comm m (n+1))
  have hS2 : (m+1)+n-1 = n+(m+1)-1 := congrArg (fun k => k - 1) (Nat.add_comm (m+1) n)
  have hB : (m+n-1)+1 = m+n := by omega
  have h1' : (m+1)+n-1 = m+n := by omega
  have h2' : m+(n+1)-1 = m+n := by omega
  have h3' : n+m = m+n := by omega
  have hc : m+n = n+m := Nat.add_comm m n
  have hgen := cup1_library_gen X m n v u hm hn hB h1' h2' h3'
  have hunf : cup1m X n m u v = hS ▸ cup1 F2 X m n v u := rfl
  have hunf1 : cup1m X (n+1) m (cochainDiff F2 X u) v
      = hS1 ▸ cup1 F2 X m (n+1) v (cochainDiff F2 X u) := rfl
  have hunf2 : cup1m X n (m+1) u (cochainDiff F2 X v)
      = hS2 ▸ cup1 F2 X (m+1) n (cochainDiff F2 X v) u := rfl
  rw [hunf, hunf1, hunf2]
  have hA1 : hA ▸ cochainDiff F2 X (hS ▸ cup1 F2 X m n v u)
      = hA ▸ ((congrArg (fun k => k + 1) hS) ▸ cochainDiff F2 X (cup1 F2 X m n v u)) :=
    cup1Rec_congr (α := fun k => Cochain F2 X k) hA (cup1CochainDiff_cast hS _)
  have hA2 : hA ▸ ((congrArg (fun k => k + 1) hS) ▸ cochainDiff F2 X (cup1 F2 X m n v u))
      = ((congrArg (fun k => k + 1) hS).trans hA) ▸ cochainDiff F2 X (cup1 F2 X m n v u) :=
    cup1Rec_trans (α := fun k => Cochain F2 X k) _ _ _
  have hA3 : ((congrArg (fun k => k + 1) hS).trans hA) ▸ cochainDiff F2 X (cup1 F2 X m n v u)
      = (hB.trans hc) ▸ cochainDiff F2 X (cup1 F2 X m n v u) :=
    cup1Rec_irrel (α := fun k => Cochain F2 X k) _ _ _
  have hA4 : (hB.trans hc) ▸ cochainDiff F2 X (cup1 F2 X m n v u)
      = hc ▸ (hB ▸ cochainDiff F2 X (cup1 F2 X m n v u)) :=
    (cup1Rec_trans (α := fun k => Cochain F2 X k) hB hc _).symm
  have hLHS : hA ▸ cochainDiff F2 X (hS ▸ cup1 F2 X m n v u)
      = hc ▸ (hB ▸ cochainDiff F2 X (cup1 F2 X m n v u)) :=
    hA1.trans (hA2.trans (hA3.trans hA4))
  have hgen' : hc ▸ (hB ▸ cochainDiff F2 X (cup1 F2 X m n v u))
      = hc ▸ (h1' ▸ cup1 F2 X (m+1) n (cochainDiff F2 X v) u
              + h2' ▸ cup1 F2 X m (n+1) v (cochainDiff F2 X u) + cup F2 X v u
              + h3' ▸ cup F2 X u v) :=
    congrArg (fun x : Cochain F2 X (m+n) => hc ▸ x) hgen
  have hR1 : hc ▸ (h1' ▸ cup1 F2 X (m+1) n (cochainDiff F2 X v) u
          + h2' ▸ cup1 F2 X m (n+1) v (cochainDiff F2 X u) + cup F2 X v u
          + h3' ▸ cup F2 X u v)
      = (hc ▸ (h1' ▸ cup1 F2 X (m+1) n (cochainDiff F2 X v) u)
          + hc ▸ (h2' ▸ cup1 F2 X m (n+1) v (cochainDiff F2 X u))
          + hc ▸ cup F2 X v u) + hc ▸ (h3' ▸ cup F2 X u v) := by
    rw [cup1Rec_add (α := fun k => Cochain F2 X k) hc
        (h1' ▸ cup1 F2 X (m+1) n (cochainDiff F2 X v) u
          + h2' ▸ cup1 F2 X m (n+1) v (cochainDiff F2 X u) + cup F2 X v u)
        (h3' ▸ cup F2 X u v)]
    rw [cup1Rec_add (α := fun k => Cochain F2 X k) hc
        (h1' ▸ cup1 F2 X (m+1) n (cochainDiff F2 X v) u
          + h2' ▸ cup1 F2 X m (n+1) v (cochainDiff F2 X u)) (cup F2 X v u)]
    rw [cup1Rec_add (α := fun k => Cochain F2 X k) hc
        (h1' ▸ cup1 F2 X (m+1) n (cochainDiff F2 X v) u)
        (h2' ▸ cup1 F2 X m (n+1) v (cochainDiff F2 X u))]
  have ht1 : hc ▸ (h1' ▸ cup1 F2 X (m+1) n (cochainDiff F2 X v) u)
      = h4 ▸ (hS2 ▸ cup1 F2 X (m+1) n (cochainDiff F2 X v) u) :=
    (cup1Rec_trans (α := fun k => Cochain F2 X k) h1' hc _).trans
      ((cup1Rec_irrel (α := fun k => Cochain F2 X k) (h1'.trans hc) (hS2.trans h4) _).trans
        (cup1Rec_trans (α := fun k => Cochain F2 X k) hS2 h4 _).symm)
  have ht2 : hc ▸ (h2' ▸ cup1 F2 X m (n+1) v (cochainDiff F2 X u))
      = h3 ▸ (hS1 ▸ cup1 F2 X m (n+1) v (cochainDiff F2 X u)) :=
    (cup1Rec_trans (α := fun k => Cochain F2 X k) h2' hc _).trans
      ((cup1Rec_irrel (α := fun k => Cochain F2 X k) (h2'.trans hc) (hS1.trans h3) _).trans
        (cup1Rec_trans (α := fun k => Cochain F2 X k) hS1 h3 _).symm)
  have ht3 : hc ▸ cup F2 X v u = hvu ▸ cup F2 X v u :=
    cup1Rec_irrel (α := fun k => Cochain F2 X k) hc hvu _
  have ht4 : hc ▸ (h3' ▸ cup F2 X u v) = cup F2 X u v :=
    (cup1Rec_trans (α := fun k => Cochain F2 X k) h3' hc _).trans
      (cup1Rec_self (α := fun k => Cochain F2 X k) (h3'.trans hc) _)
  have hR2 : (hc ▸ (h1' ▸ cup1 F2 X (m+1) n (cochainDiff F2 X v) u)
          + hc ▸ (h2' ▸ cup1 F2 X m (n+1) v (cochainDiff F2 X u))
          + hc ▸ cup F2 X v u) + hc ▸ (h3' ▸ cup F2 X u v)
      = cup F2 X u v + hvu ▸ cup F2 X v u
        + h3 ▸ (hS1 ▸ cup1 F2 X m (n+1) v (cochainDiff F2 X u))
        + h4 ▸ (hS2 ▸ cup1 F2 X (m+1) n (cochainDiff F2 X v) u) := by
    rw [ht1, ht2, ht3, ht4]
    abel
  exact hLHS.trans (hgen'.trans (hR1.trans hR2))

/-- Mod-2 coboundary formula for the cup-1 product `Work.Pi6.SQ.cup1m` (Steenrod's interval convention as in `REFS/pi6_cupi_check.py`, `i = 1`): for cochains `u`, `v` of degrees `n`, `m`, `δ(u ∪₁ v) = u ∪ v + v ∪ u + δu ∪₁ v + u ∪₁ δv`. -/
theorem cup1Coboundary (X : SSet) (n m : ℕ) (u : Work.Cohomology.Cochain Work.Pi6.SQ.F2 X n) (v : Work.Cohomology.Cochain Work.Pi6.SQ.F2 X m) (hn : 1 ≤ n) (hm : 1 ≤ m) : (by omega : (n + m - 1) + 1 = n + m) ▸ (Work.Cohomology.cochainDiff Work.Pi6.SQ.F2 X (Work.Pi6.SQ.cup1m X n m u v)) = Work.Cohomology.cup Work.Pi6.SQ.F2 X u v + (by omega : m + n = n + m) ▸ Work.Cohomology.cup Work.Pi6.SQ.F2 X v u + (by omega : (n + 1) + m - 1 = n + m) ▸ Work.Pi6.SQ.cup1m X (n + 1) m (Work.Cohomology.cochainDiff Work.Pi6.SQ.F2 X u) v + (by omega : n + (m + 1) - 1 = n + m) ▸ Work.Pi6.SQ.cup1m X n (m + 1) u (Work.Cohomology.cochainDiff Work.Pi6.SQ.F2 X v) :=
  cup1mCoboundaryGen X n m u v hn hm (by omega) (by omega) (by omega) (by omega)

end

end Work.Pi6.SQ
