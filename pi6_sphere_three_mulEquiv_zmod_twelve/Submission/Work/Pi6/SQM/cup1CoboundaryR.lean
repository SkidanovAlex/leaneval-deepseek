import Mathlib
import Submission.Work.Pi6.SQM.Defs
import Submission.Work.Pi6.SQM.cup1ShiftedLeftR
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# The integral cup-1 coboundary formula (`Cup1CobR`)

`δ(α ∪₁ β) = α ⌣ β − (−1)^{nm} β ⌣ α − δα ∪₁ β + (−1)^{n+1} α ∪₁ δβ`

for the library cup-1 product `Work.Cohomology.cup1` over any commutative ring `R` and **arbitrary**
cochains.  The library's `Work.Cohomology.cup1Identity` treats the cocycle case only.  Route: the
telescoping computation of `cup1Identity`, keeping the two families of terms that the cocycle
hypotheses killed — the faces of the `α`-arguments give `δα ∪₁ β`, the faces of the `β`-arguments
give `α ∪₁ δβ`.
-/

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Pi6.SQM

noncomputable section

open Work.Cohomology (Cochain genEval cochainDiff cup cup1 Fface Gface Amap Qmap Wmap Ymap Delmap
  shmap frontIncl backIncl frontFace backFace genEval_cup1 genEval_cochainDiff genEval_cast
  genEval_add genEval_smul genEval_ext sum_range_eq_fin mop delta_comp_shmap map_op_comp cup_apply'
  frontIncl_comp_shmap backIncl_comp_shmap
  face_F_le face_G_le face_F_mid face_G_mid face_F_gt face_G_gt
  Wcomp_zero Wcomp_top Wcomp_zero_of Wcomp_top_of Qcomp_zero Qcomp_top Qcomp_Y Qcomp_Y'
  Qcomp_Y_of Qcomp_Y'_of
  Qcomp_zero_of Qcomp_top_of Amap_zero_eq_frontIncl)

variable {R : Type} [CommRing R] {X : SSet}

/-- Evaluation of a difference of cochains. -/
lemma genEval_sub' {k : ℕ} (f g : Cochain R X k) (σ : X _⦋k⦌) :
    genEval R X (f - g) σ = genEval R X f σ - genEval R X g σ := by
  simp only [genEval, LinearMap.sub_apply]

/-- `(−1)^{2k} = 1`. -/
lemma negOnePowTwoMul (k : ℕ) : (-1:R)^(2*k) = 1 := by
  rw [pow_mul, neg_one_sq, one_pow]

/-- `(−1)^{a+2k} = (−1)^a`. -/
lemma negOnePowAddTwoMul (a k : ℕ) : (-1:R)^(a + 2*k) = (-1:R)^a := by
  rw [pow_add, negOnePowTwoMul, mul_one]

/-! ## The shifted `∪₁` product (right shift) -/

/-- `Fface`/`Gface` in degrees `(n, m+1)`, composed with the degree identification
`n+(m+1)-1 = n+m`, are the interval maps `Amap`/`Qmap`. -/
theorem shmapFfaceAmapR (n m s : ℕ) (hs : s ≤ m) (h : n+(m+1)-1 = n+m) :
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

/-- The `α ∪₁ δβ` term, evaluated at the degree-transported simplex. -/
theorem cup1ShiftedRightR (R : Type) [CommRing R] (X : SSet) (n m : ℕ)
    (α : Work.Cohomology.Cochain R X n) (β : Work.Cohomology.Cochain R X m)
    (h2 : n+(m+1)-1 = n+m) (σ : X.obj (Opposite.op (SimplexCategory.mk (n+m)))) :
    Work.Cohomology.genEval R X
        (Work.Cohomology.cup1 R X n (m+1) α (Work.Cohomology.cochainDiff R X β))
        (X.map (Work.Cohomology.shmap (n+(m+1)-1) (n+m) h2).op σ)
      = ∑ t : Fin (m+1), ((-1:R)^(t.val*(n+1)+n)) *
          Work.Cohomology.genEval R X α
            (X.map (Work.Cohomology.Amap n m t.val (by have := t.isLt; omega)).op σ) *
          Work.Cohomology.genEval R X (Work.Cohomology.cochainDiff R X β)
            (X.map (Work.Cohomology.Qmap n m t.val (by have := t.isLt; omega)).op σ) := by
  rw [Work.Cohomology.genEval_cup1]
  refine Finset.sum_congr rfl fun s _ => ?_
  obtain ⟨hf, hg⟩ := shmapFfaceAmapR n m s.val (by have := s.isLt; omega) h2
  rw [Work.Cohomology.mop (Work.Cohomology.shmap (n+(m+1)-1) (n+m) h2)
        (Work.Cohomology.Fface n (m+1) s.val (by have := s.isLt; omega)) σ, hf,
      Work.Cohomology.mop (Work.Cohomology.shmap (n+(m+1)-1) (n+m) h2)
        (Work.Cohomology.Gface n (m+1) s.val (by have := s.isLt; omega)) σ, hg]

/-! ## A sign reindexing identity -/

/-- The `δβ`-block of the telescoping computation, reindexed against the `t`-th coefficient
`(−1)^{t(n+1)+n}` of the shifted product `α ∪₁ δβ`. -/
theorem powSignReindex (R : Type) [CommRing R] (n m : ℕ) (hm : 1 ≤ m) (Y : ℕ → R) :
    (∑ u ∈ Finset.range (m - 1), ((-1:R)^(u*(n+1)+n)) * Y (u+1))
      + ((-1:R)^((m-1)*(n+1)+n)) * Y m - Y 0
    = ((-1:R)^(n+1)) * (∑ t ∈ Finset.range (m+1), ((-1:R)^(t*(n+1)+n)) * Y t) := by
  -- the two blocks of the left-hand side merge into the sum over `range m`
  have hL : (∑ u ∈ Finset.range (m - 1), ((-1:R)^(u*(n+1)+n)) * Y (u+1))
      + ((-1:R)^((m-1)*(n+1)+n)) * Y m
      = ∑ t ∈ Finset.range m, ((-1:R)^(t*(n+1)+n)) * Y (t+1) := by
    have hrange : Finset.range m = Finset.range ((m-1)+1) := by
      congr 1
      omega
    rw [hrange, Finset.sum_range_succ]
    rw [Nat.sub_add_cancel hm]
  rw [hL]
  -- push the coefficient `(-1)^{n+1}` inside the right-hand sum
  rw [Finset.mul_sum]
  rw [show (∑ t ∈ Finset.range (m+1), ((-1:R)^(n+1)) * (((-1:R)^(t*(n+1)+n)) * Y t))
      = (∑ t ∈ Finset.range (m+1), (((-1:R)^(n+1)) * ((-1:R)^(t*(n+1)+n))) * Y t) from by
    refine Finset.sum_congr rfl fun t _ => ?_
    ring]
  rw [Finset.sum_range_succ' (fun t => (((-1:R)^(n+1)) * ((-1:R)^(t*(n+1)+n))) * Y t) m]
  have h0 : (((-1:R)^(n+1)) * ((-1:R)^((0:ℕ)*(n+1)+n))) * Y 0 = - Y 0 := by
    rw [show (0:ℕ)*(n+1)+n = n by omega]
    rw [← pow_add]
    rw [show n+1+n = 2*n+1 by omega]
    rw [pow_add, pow_one, negOnePowTwoMul]
    ring
  rw [h0]
  rw [show (∑ t ∈ Finset.range m, (((-1:R)^(n+1)) * ((-1:R)^((t+1)*(n+1)+n))) * Y (t+1))
      = ∑ t ∈ Finset.range m, ((-1:R)^(t*(n+1)+n)) * Y (t+1) from by
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [← pow_add]
    rw [show n+1 + ((t+1)*(n+1)+n) = (t*(n+1)+n) + 2*(n+1) by
      have h : (t+1)*(n+1) = t*(n+1) + (n+1) := by ring
      omega]
    rw [negOnePowAddTwoMul]]
  ring
/-- **The integral cup-1 coboundary formula** for arbitrary cochains: `Cup1CobR`. -/
theorem cup1CoboundaryGen (R : Type) [CommRing R] (X : SSet) (n m : ℕ)
    (α : Cochain R X n) (β : Cochain R X m) (hn : 1 ≤ n) (hm : 1 ≤ m)
    (hcast : n + m - 1 + 1 = n + m) (h1 : (n + 1) + m - 1 = n + m)
    (h2 : n + (m + 1) - 1 = n + m) :
    hcast ▸ (cochainDiff R X (cup1 R X n m α β)) =
      Work.Cohomology.cup R X α β - ((-1 : R) ^ (n * m)) • ((Nat.add_comm m n) ▸ Work.Cohomology.cup R X β α) -
      h1 ▸ cup1 R X (n + 1) m (cochainDiff R X α) β +
      ((-1 : R) ^ (n + 1)) • (h2 ▸ cup1 R X n (m + 1) α (cochainDiff R X β)) := by
  apply genEval_ext
  intro σ
  simp only [genEval_sub', genEval_add, genEval_smul, smul_eq_mul]
  -- the `k`-th face of `σ`
  let Df : ℕ → X _⦋n+m-1⦌ := fun k =>
    if _ : k ≤ n+m then X.map (Delmap n m k (by omega)).op σ
      else X.map (Delmap n m 0 (by omega)).op σ
  -- the master term of the double sum
  let TFf : ℕ → Fin m → R := fun k s => ((-1:R)^k) * ((-1:R)^(s.val*(n+1)+n) *
      (genEval R X α (X.map (Fface n m s.val (by have := s.isLt; omega)).op (Df k)) *
       genEval R X β (X.map (Gface n m s.val (by have := s.isLt; omega)).op (Df k))))
  have hL : genEval R X (hcast ▸ cochainDiff R X (cup1 R X n m α β)) σ
      = ∑ k ∈ Finset.range (n+m+1), ∑ s : Fin m, TFf k s := by
    rw [genEval_cast, genEval_cochainDiff]
    trans ∑ i : Fin ((n+m-1+1)+1),
        ((-1:R)^(i:ℕ)) * genEval R X (cup1 R X n m α β) (Df (i:ℕ))
    · refine Finset.sum_congr rfl fun i _ => ?_
      have h : X.δ i (X.map (shmap (n+m-1+1) (n+m) hcast).op σ) = Df (i:ℕ) := by
        rw [show Df (i:ℕ) = X.map (Delmap n m (i:ℕ) (by omega)).op σ from by
          simp only [Df, dif_pos (by omega : (i:ℕ) ≤ n + m)]]
        rw [SimplicialObject.δ_def, map_op_comp, delta_comp_shmap]
      rw [h]
    · rw [Fin.sum_univ_eq_sum_range
        (fun k => ((-1:R)^k) * genEval R X (cup1 R X n m α β) (Df k)) ((n+m-1+1)+1)]
      rw [show (n+m-1+1)+1 = n+m+1 by omega]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [genEval_cup1, Finset.mul_sum]
      refine Finset.sum_congr rfl fun s _ => ?_
      simp only [TFf]
      ring
  rw [hL, Finset.sum_comm]
  -- abbreviations
  let sg : ℕ → R := fun s => (-1:R)^(s*(n+1)+n)
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
  let DBQ : ℕ → R := fun t => if _ : t ≤ m then
      genEval R X (cochainDiff R X β) (X.map (Qmap n m t (by omega)).op σ) else 0
  let DBS : ℕ → R := fun t => genEval R X α (AQ t) * DBQ t
  let DW : Fin m → R := fun s => (sg s.val * ((-1:R)^(s.val+1))) *
      (genEval R X (cochainDiff R X α) (X.map (Wmap n m s.val (by have := s.isLt; omega)).op σ) *
       genEval R X β (YQ s.val))
  let P1 : Fin m → R := fun s => ∑ r ∈ Finset.range (s.val+1),
      ((-1:R)^r) * (sg s.val * (genEval R X α (AQ (s.val+1)) * genEval R X β (QQ (s.val+1) r)))
  let P2 : Fin m → R := fun s => ∑ j ∈ Finset.range n,
      ((-1:R)^(s.val+1+j)) * (sg s.val * (genEval R X α (WQ s.val (j+1)) * genEval R X β (YQ s.val)))
  let P3 : Fin m → R := fun s => ∑ i ∈ Finset.range (m - s.val),
      ((-1:R)^(s.val+1+(n+i))) * (sg s.val * (genEval R X α (AQ s.val) * genEval R X β (QQ s.val (s.val+2+i))))
  have hsplit : ∀ s : Fin m, (∑ k ∈ Finset.range (n+m+1), TFf k s) = P1 s + P2 s + P3 s := by
    intro s
    have h1 : (∑ k ∈ Finset.range (n+m+1), TFf k s)
        = (∑ k ∈ Finset.range (s.val+1), TFf k s)
          + ∑ j ∈ Finset.range (n+m-s.val), TFf (s.val+1+j) s := by
      rw [show n+m+1 = (s.val+1)+(n+m-s.val) by omega]
      exact Finset.sum_range_add (fun k => TFf k s) (s.val+1) (n+m-s.val)
    have h2 : (∑ j ∈ Finset.range (n+m-s.val), TFf (s.val+1+j) s)
        = (∑ j ∈ Finset.range n, TFf (s.val+1+j) s)
          + ∑ i ∈ Finset.range (m-s.val), TFf (s.val+1+(n+i)) s := by
      rw [show n+m-s.val = n + (m-s.val) by omega]
      exact Finset.sum_range_add (fun j => TFf (s.val+1+j) s) n (m-s.val)
    rw [h1, h2]
    dsimp only [P1, P2, P3, sg]
    rw [← add_assoc]
    congr 1
    · congr 1
      · refine Finset.sum_congr rfl fun r hr => ?_
        rw [Finset.mem_range] at hr
        simp only [TFf, Df, AQ, QQ, dif_pos s.isLt, dif_pos (by omega : r ≤ n + m),
          dif_pos (by omega : s.val + 1 ≤ m), dif_pos (by omega : r ≤ m + 1)]
        rw [face_F_le σ r s.val (by omega) s.isLt, face_G_le σ r s.val (by omega) s.isLt]
        try ring
      · refine Finset.sum_congr rfl fun j hj => ?_
        rw [Finset.mem_range] at hj
        simp only [TFf, Df, WQ, YQ, dif_pos s.isLt, dif_pos (by omega : s.val + 1 + j ≤ n + m),
          dif_pos (by omega : j + 1 ≤ n + 1)]
        rw [face_F_mid σ (s.val+1+j) s.val (by omega) (by omega) s.isLt,
            face_G_mid σ (s.val+1+j) s.val (by omega) (by omega) s.isLt]
        rw [show (⟨(s.val+1+j) - s.val, by omega⟩ : Fin (n+2)) = ⟨j+1, by omega⟩ from
              Fin.ext (by simp only [Fin.val_mk]; omega)]
        try ring
    · refine Finset.sum_congr rfl fun i hi => ?_
      rw [Finset.mem_range] at hi
      simp only [TFf, Df, AQ, QQ, dif_pos s.isLt,
        dif_pos (by omega : s.val + 1 + (n + i) ≤ n + m),
        dif_pos (by omega : s.val ≤ m),
        dif_pos (by omega : s.val + 2 + i ≤ m + 1)]
      rw [face_F_gt σ (s.val+1+(n+i)) s.val (by omega) s.isLt,
          face_G_gt σ (s.val+1+(n+i)) s.val (by omega) (by omega) s.isLt]
      rw [show (⟨(s.val+1+(n+i)) - n + 1, by omega⟩ : Fin (m+2)) = ⟨s.val+2+i, by omega⟩ from
            Fin.ext (by simp only [Fin.val_mk]; omega)]
      try ring
  rw [Finset.sum_congr rfl (fun s _ => hsplit s)]
  -- the two "end terms" contributed by the `α`-cocycle relation on `[s,s+n+1]`
  let X1 : Fin m → R := fun s => sg s.val * ((-1:R)^(s.val+1)) *
      (genEval R X α (AQ (s.val+1)) * genEval R X β (YQ s.val))
  let X3 : Fin m → R := fun s => sg s.val * ((-1:R)^(s.val+n)) *
      (genEval R X α (AQ s.val) * genEval R X β (YQ s.val))
  let Q1 : Fin m → R := fun s => sg s.val * (genEval R X α (AQ (s.val+1)) *
      ∑ r ∈ Finset.range (s.val+2), ((-1:R)^r) * genEval R X β (QQ (s.val+1) r))
  let Q3 : Fin m → R := fun s => sg s.val * (genEval R X α (AQ s.val) *
      ∑ i ∈ Finset.range (m+1-s.val), ((-1:R)^(s.val+n+i)) * genEval R X β (QQ s.val (s.val+1+i)))
  -- the `δα`-coboundary relation on `[s,s+n+1]`
  have hrelW : ∀ s : Fin m,
      (∑ j ∈ Finset.range (n+2), ((-1:R)^j) * genEval R X α (WQ s.val j))
        = genEval R X (cochainDiff R X α)
            (X.map (Wmap n m s.val (by have := s.isLt; omega)).op σ) := by
    intro s
    rw [sum_range_eq_fin]
    trans ∑ j : Fin (n+2),
        ((-1:R)^(j:ℕ)) * genEval R X α (X.δ j (X.map (Wmap n m s.val (by have := s.isLt; omega)).op σ))
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [show X.δ j (X.map (Wmap n m s.val (by have := s.isLt; omega)).op σ) = WQ s.val (j:ℕ) from by
        rw [SimplicialObject.δ_def, map_op_comp]
        simp only [WQ, dif_pos s.isLt, dif_pos (by omega : (j:ℕ) ≤ n + 1)]]
    · exact (genEval_cochainDiff α
        (X.map (Wmap n m s.val (by have := s.isLt; omega)).op σ)).symm
  -- telescoping the `α`-coboundary over the faces of `[s,s+n+1]`
  have hmid : ∀ s : Fin m,
      (∑ j ∈ Finset.range n, ((-1:R)^j) * genEval R X α (WQ s.val (j+1)))
        = - genEval R X (cochainDiff R X α)
              (X.map (Wmap n m s.val (by have := s.isLt; omega)).op σ)
          + genEval R X α (WQ s.val 0) + ((-1:R)^(n+1)) * genEval R X α (WQ s.val (n+1)) := by
    intro s
    have h0 := hrelW s
    have h1 : (∑ j ∈ Finset.range (n+2), ((-1:R)^j) * genEval R X α (WQ s.val j))
        = (∑ j ∈ Finset.range (n+1), ((-1:R)^(j+1)) * genEval R X α (WQ s.val (j+1)))
          + genEval R X α (WQ s.val 0) := by
      rw [show n+2 = (n+1)+1 by omega, Finset.sum_range_succ']
      simp only [pow_zero, one_mul]
    have h2 : (∑ j ∈ Finset.range (n+1), ((-1:R)^(j+1)) * genEval R X α (WQ s.val (j+1)))
        = (∑ j ∈ Finset.range n, ((-1:R)^(j+1)) * genEval R X α (WQ s.val (j+1)))
          + ((-1:R)^(n+1)) * genEval R X α (WQ s.val (n+1)) := by
      rw [Finset.sum_range_succ]
    have h3 : (∑ j ∈ Finset.range n, ((-1:R)^(j+1)) * genEval R X α (WQ s.val (j+1)))
        = - (∑ j ∈ Finset.range n, ((-1:R)^j) * genEval R X α (WQ s.val (j+1))) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [pow_succ]; ring
    rw [h1, h2, h3] at h0
    linear_combination -h0
  have hP2 : ∀ s : Fin m, P2 s
      = X1 s + sg s.val * (((-1:R)^(s.val+1)) * ((-1:R)^(n+1))) *
          (genEval R X α (AQ s.val) * genEval R X β (YQ s.val)) - DW s := by
    intro s
    dsimp only [P2, X1, sg, DW]
    rw [show (∑ j ∈ Finset.range n, ((-1:R)^(s.val+1+j)) *
          (((-1:R)^(s.val*(n+1)+n)) * (genEval R X α (WQ s.val (j+1)) * genEval R X β (YQ s.val))))
        = (((-1:R)^(s.val*(n+1)+n)) * ((-1:R)^(s.val+1))) *
            ((∑ j ∈ Finset.range n, ((-1:R)^j) * genEval R X α (WQ s.val (j+1))) *
              genEval R X β (YQ s.val)) from by
      rw [Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← pow_add]
      ring]
    rw [hmid s]
    rw [show WQ s.val 0 = AQ (s.val+1) from by
      dsimp only [WQ, AQ]
      rw [dif_pos s.isLt, dif_pos (by omega : (0:ℕ) ≤ n+1), dif_pos (by omega : s.val+1 ≤ m)]
      exact Wcomp_zero_of σ s.val s.isLt (⟨0, by omega⟩ : Fin (n+2)) rfl]
    rw [show WQ s.val (n+1) = AQ s.val from by
      dsimp only [WQ, AQ]
      rw [dif_pos s.isLt, dif_pos (by omega : n+1 ≤ n+1), dif_pos (by omega : s.val ≤ m)]
      exact Wcomp_top_of σ s.val s.isLt (⟨n+1, by omega⟩ : Fin (n+2)) rfl]
    ring
  have ha : ∀ s : Fin m, P1 s + X1 s = Q1 s := by
    intro s
    dsimp only [P1, Q1, X1, sg]
    rw [show s.val + 2 = (s.val+1) + 1 by omega,
        Finset.sum_range_succ (fun r => ((-1:R)^r) * genEval R X β (QQ (s.val+1) r)) (s.val+1)]
    rw [show QQ (s.val+1) (s.val+1) = YQ s.val from by
      dsimp only [QQ, YQ]
      rw [dif_pos (by omega : s.val+1 ≤ m), dif_pos (by omega : s.val+1 ≤ m+1), dif_pos s.isLt]
      exact Qcomp_Y'_of σ s.val s.isLt (⟨s.val+1, by omega⟩ : Fin (m+2)) rfl]
    rw [show (∑ r ∈ Finset.range (s.val+1), ((-1:R)^r) *
          (sg s.val * (genEval R X α (AQ (s.val+1)) * genEval R X β (QQ (s.val+1) r))))
        = (sg s.val * genEval R X α (AQ (s.val+1))) *
            (∑ r ∈ Finset.range (s.val+1), ((-1:R)^r) * genEval R X β (QQ (s.val+1) r)) from by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun r _ => ?_
      ring]
    ring
  have hb : ∀ s : Fin m, P3 s + X3 s = Q3 s := by
    intro s
    dsimp only [P3, Q3, X3, sg]
    -- factor out `sg * α` from the `P3` sum
    rw [show (∑ i ∈ Finset.range (m - s.val), ((-1:R)^(s.val+1+(n+i))) *
          (sg s.val * (genEval R X α (AQ s.val) * genEval R X β (QQ s.val (s.val+2+i)))))
        = (sg s.val * genEval R X α (AQ s.val)) *
            (∑ i ∈ Finset.range (m - s.val), ((-1:R)^(s.val+1+(n+i))) *
              genEval R X β (QQ s.val (s.val+2+i))) from by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring]
    -- split off the first term of the `Q3` sum
    rw [show m+1-s.val = (m-s.val)+1 by omega,
        Finset.sum_range_succ' (fun i => ((-1:R)^(s.val+n+i)) * genEval R X β (QQ s.val (s.val+1+i))) (m-s.val)]
    -- identify the first term
    rw [show QQ s.val (s.val+1) = YQ s.val from by
      dsimp only [QQ, YQ]
      rw [dif_pos (by omega : s.val ≤ m), dif_pos (by omega : s.val+1 ≤ m+1), dif_pos s.isLt]
      exact Qcomp_Y_of σ s.val s.isLt (⟨s.val+1, by omega⟩ : Fin (m+2)) rfl]
    -- normalise the exponents
    rw [show (∑ k ∈ Finset.range (m-s.val), ((-1:R)^(s.val+n+(k+1))) * genEval R X β (QQ s.val (s.val+1+(k+1))))
        = ∑ k ∈ Finset.range (m-s.val), ((-1:R)^(s.val+1+(n+k))) * genEval R X β (QQ s.val (s.val+2+k)) from by
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [show s.val+n+(k+1) = s.val+1+(n+k) by omega]
      rw [show s.val+1+(k+1) = s.val+2+k by omega]]
    ring
  have hd : ∀ s : Fin m, sg s.val * (((-1:R)^(s.val+1)) * ((-1:R)^(n+1))) *
        (genEval R X α (AQ s.val) * genEval R X β (YQ s.val)) = X3 s := by
    intro s
    dsimp only [X3, sg]
    rw [show ((-1:R)^(s.val+1)) * ((-1:R)^(n+1)) = (-1:R)^(s.val+n) from by
      rw [← pow_add]
      rw [show s.val+1+(n+1) = (s.val+n) + 2*1 by omega]
      rw [negOnePowAddTwoMul]]
  have hS2 : (∑ s : Fin m, (P1 s + P2 s + P3 s))
      = (∑ s : Fin m, (Q1 s + Q3 s)) - ∑ s : Fin m, DW s := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [hP2 s, hd s]
    rw [show P1 s + (X1 s + X3 s - DW s) + P3 s = (P1 s + X1 s) + (P3 s + X3 s) - DW s from by ring]
    rw [ha s, hb s]
  rw [hS2]
  -- the two families of "blocks"
  let B1 : ℕ → R := fun t => if t = 0 then 0 else sg (t-1) * (genEval R X α (AQ t) *
      ∑ r ∈ Finset.range (t+1), ((-1:R)^r) * genEval R X β (QQ t r))
  let B2 : ℕ → R := fun t => if t = m then 0 else sg t * (genEval R X α (AQ t) *
      ∑ i ∈ Finset.range (m+1-t), ((-1:R)^(t+n+i)) * genEval R X β (QQ t (t+1+i)))
  have hQ1step : ∀ s : Fin m, Q1 s = B1 (s.val+1) := by
    intro s
    dsimp only [Q1, B1, sg]
    rw [if_neg (by omega : ¬ s.val + 1 = 0)]
    rw [show s.val+1-1 = s.val by omega]
  have hQ3step : ∀ s : Fin m, Q3 s = B2 s.val := by
    intro s
    dsimp only [Q3, B2]
    rw [if_neg (by omega : ¬ s.val = m)]
  have hB1zero : B1 0 = 0 := by
    dsimp only [B1]
    rw [if_pos rfl]
  have hQ1sum : (∑ s : Fin m, Q1 s) = ∑ t ∈ Finset.range (m+1), B1 t := by
    rw [show (∑ s : Fin m, Q1 s) = ∑ s ∈ Finset.range m, B1 (s+1) from by
      rw [Finset.sum_fin_eq_sum_range]
      refine Finset.sum_congr rfl fun s hs => ?_
      rw [dif_pos (Finset.mem_range.mp hs), hQ1step ⟨s, Finset.mem_range.mp hs⟩]]
    rw [Finset.sum_range_succ' B1 m, hB1zero, add_zero]
  have hQ3sum : (∑ s : Fin m, Q3 s) = ∑ t ∈ Finset.range m, B2 t := by
    rw [Finset.sum_fin_eq_sum_range]
    refine Finset.sum_congr rfl fun s hs => ?_
    rw [dif_pos (Finset.mem_range.mp hs), hQ3step ⟨s, Finset.mem_range.mp hs⟩]
  rw [Finset.sum_add_distrib, hQ1sum, hQ3sum]
  -- the `δβ`-coboundary relation on `[0,t] ∪ [t+n, n+m]`
  have hrelQ : ∀ t : Fin (m+1),
      (∑ p ∈ Finset.range (m+2), ((-1:R)^p) * genEval R X β (QQ t.val p))
        = genEval R X (cochainDiff R X β)
            (X.map (Qmap n m t.val (by have := t.isLt; omega)).op σ) := by
    intro t
    rw [sum_range_eq_fin]
    trans ∑ p : Fin (m+2),
        ((-1:R)^(p:ℕ)) * genEval R X β (X.δ p (X.map (Qmap n m t.val (by have := t.isLt; omega)).op σ))
    · refine Finset.sum_congr rfl fun p _ => ?_
      rw [show X.δ p (X.map (Qmap n m t.val (by have := t.isLt; omega)).op σ) = QQ t.val (p:ℕ) from by
        rw [SimplicialObject.δ_def, map_op_comp]
        simp only [QQ, dif_pos (by omega : t.val ≤ m), dif_pos (by omega : (p:ℕ) ≤ m+1)]]
    · exact (genEval_cochainDiff β
        (X.map (Qmap n m t.val (by have := t.isLt; omega)).op σ)).symm
  -- the interior blocks: the `δβ` relation on `[0,u] ∪ [u+n, n+m]`
  have hcancel : ∀ u : ℕ, 1 ≤ u → u ≤ m - 1 → B1 u + B2 u
      = ((-1:R)^((u-1)*(n+1)+n)) * (genEval R X α (AQ u) * DBQ u) := by
    intro u hu1 hu2
    have hu : u ≤ m := by omega
    dsimp only [B1, B2, sg]
    rw [if_neg (by omega : ¬ u = 0), if_neg (by omega : ¬ u = m)]
    -- coefficient identity: `(-1)^{u(n+1)+n}(-1)^{u+n+i} = (-1)^{(u-1)(n+1)+n}(-1)^{u+1+i}`
    have hcoef : ∀ i : ℕ,
        ((-1:R)^(u*(n+1)+n)) * (((-1:R)^(u+n+i)) * genEval R X β (QQ u (u+1+i)))
          = ((-1:R)^((u-1)*(n+1)+n)) * (((-1:R)^(u+1+i)) * genEval R X β (QQ u (u+1+i))) := by
      intro i
      rw [show ((-1:R)^(u*(n+1)+n)) * (((-1:R)^(u+n+i)) * genEval R X β (QQ u (u+1+i)))
          = (((-1:R)^(u*(n+1)+n)) * ((-1:R)^(u+n+i))) * genEval R X β (QQ u (u+1+i)) from by ring]
      rw [show ((-1:R)^((u-1)*(n+1)+n)) * (((-1:R)^(u+1+i)) * genEval R X β (QQ u (u+1+i)))
          = (((-1:R)^((u-1)*(n+1)+n)) * ((-1:R)^(u+1+i))) * genEval R X β (QQ u (u+1+i)) from by ring]
      rw [show ((-1:R)^(u*(n+1)+n)) * ((-1:R)^(u+n+i))
          = ((-1:R)^((u-1)*(n+1)+n)) * ((-1:R)^(u+1+i)) from by
        rw [← pow_add, ← pow_add]
        rw [show u*(n+1)+n + (u+n+i) = ((u-1)*(n+1)+n + (u+1+i)) + 2*n by
          have h1 : u*(n+1) = (u-1)*(n+1) + (n+1) := by
            nth_rw 1 [← Nat.sub_add_cancel hu1]
            rw [add_mul, one_mul]
          omega]
        rw [negOnePowAddTwoMul]]
    -- the second summand, with the coefficient of the first summand
    have h2 : ((-1:R)^(u*(n+1)+n)) * (genEval R X α (AQ u) *
          ∑ i ∈ Finset.range (m+1-u), ((-1:R)^(u+n+i)) * genEval R X β (QQ u (u+1+i)))
        = ((-1:R)^((u-1)*(n+1)+n)) * (genEval R X α (AQ u) *
          ∑ i ∈ Finset.range (m+1-u), ((-1:R)^(u+1+i)) * genEval R X β (QQ u (u+1+i))) := by
      have e1 : ((-1:R)^(u*(n+1)+n)) * (genEval R X α (AQ u) *
            ∑ i ∈ Finset.range (m+1-u), ((-1:R)^(u+n+i)) * genEval R X β (QQ u (u+1+i)))
          = ∑ i ∈ Finset.range (m+1-u), ((-1:R)^(u*(n+1)+n)) * (genEval R X α (AQ u) *
              (((-1:R)^(u+n+i)) * genEval R X β (QQ u (u+1+i)))) := by
        rw [show ((-1:R)^(u*(n+1)+n)) * (genEval R X α (AQ u) *
              ∑ i ∈ Finset.range (m+1-u), ((-1:R)^(u+n+i)) * genEval R X β (QQ u (u+1+i)))
            = (((-1:R)^(u*(n+1)+n)) * genEval R X α (AQ u)) *
              (∑ i ∈ Finset.range (m+1-u), ((-1:R)^(u+n+i)) * genEval R X β (QQ u (u+1+i))) from by
          ring]
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        ring
      rw [e1]
      have e2 : (∑ i ∈ Finset.range (m+1-u), ((-1:R)^(u*(n+1)+n)) * (genEval R X α (AQ u) *
              (((-1:R)^(u+n+i)) * genEval R X β (QQ u (u+1+i)))))
          = ∑ i ∈ Finset.range (m+1-u), ((-1:R)^((u-1)*(n+1)+n)) * (genEval R X α (AQ u) *
              (((-1:R)^(u+1+i)) * genEval R X β (QQ u (u+1+i)))) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [show ((-1:R)^(u*(n+1)+n)) * (genEval R X α (AQ u) * (((-1:R)^(u+n+i)) * genEval R X β (QQ u (u+1+i))))
            = genEval R X α (AQ u) * (((-1:R)^(u*(n+1)+n)) * (((-1:R)^(u+n+i)) * genEval R X β (QQ u (u+1+i)))) from by ring]
        rw [hcoef i]
        ring
      rw [e2]
      rw [show (∑ i ∈ Finset.range (m+1-u), ((-1:R)^((u-1)*(n+1)+n)) * (genEval R X α (AQ u) *
              (((-1:R)^(u+1+i)) * genEval R X β (QQ u (u+1+i)))))
          = ((-1:R)^((u-1)*(n+1)+n)) * (genEval R X α (AQ u) *
              ∑ i ∈ Finset.range (m+1-u), ((-1:R)^(u+1+i)) * genEval R X β (QQ u (u+1+i))) from by
        rw [show ((-1:R)^((u-1)*(n+1)+n)) * (genEval R X α (AQ u) *
              ∑ i ∈ Finset.range (m+1-u), ((-1:R)^(u+1+i)) * genEval R X β (QQ u (u+1+i)))
            = (((-1:R)^((u-1)*(n+1)+n)) * genEval R X α (AQ u)) *
              (∑ i ∈ Finset.range (m+1-u), ((-1:R)^(u+1+i)) * genEval R X β (QQ u (u+1+i))) from by
          ring]
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        ring]
    rw [h2]
    -- combine the two partial sums with the full one
    have hcomb : (∑ r ∈ Finset.range (u+1), ((-1:R)^r) * genEval R X β (QQ u r))
          + (∑ i ∈ Finset.range (m+1-u), ((-1:R)^(u+1+i)) * genEval R X β (QQ u (u+1+i)))
        = ∑ p ∈ Finset.range (m+2), ((-1:R)^p) * genEval R X β (QQ u p) := by
      rw [show m+2 = (u+1) + (m+1-u) by omega]
      exact (Finset.sum_range_add (fun p => ((-1:R)^p) * genEval R X β (QQ u p)) (u+1) (m+1-u)).symm
    have hzero : (∑ p ∈ Finset.range (m+2), ((-1:R)^p) * genEval R X β (QQ u p))
        = genEval R X (cochainDiff R X β) (X.map (Qmap n m u (by omega)).op σ) := hrelQ ⟨u, by omega⟩
    have hST : (∑ r ∈ Finset.range (u+1), ((-1:R)^r) * genEval R X β (QQ u r))
          + (∑ i ∈ Finset.range (m+1-u), ((-1:R)^(u+1+i)) * genEval R X β (QQ u (u+1+i)))
        = genEval R X (cochainDiff R X β) (X.map (Qmap n m u (by omega)).op σ) := by
      rw [hcomb, hzero]
    rw [show (∑ r ∈ Finset.range (u+1), ((-1:R)^r) * genEval R X β (QQ u r))
          = genEval R X (cochainDiff R X β) (X.map (Qmap n m u (by omega)).op σ)
            - (∑ i ∈ Finset.range (m+1-u), ((-1:R)^(u+1+i)) * genEval R X β (QQ u (u+1+i))) from
        eq_sub_of_add_eq hST]
    rw [show DBQ u = genEval R X (cochainDiff R X β) (X.map (Qmap n m u (by omega)).op σ) from by
      dsimp only [DBQ]
      rw [dif_pos hu]]
    ring
  -- peel off the two end blocks
  have hpeel : (∑ t ∈ Finset.range (m+1), B1 t) + (∑ t ∈ Finset.range m, B2 t)
      = B1 m + B2 0 + ∑ u ∈ Finset.range (m-1), (B1 (u+1) + B2 (u+1)) := by
    have hB2split : (∑ t ∈ Finset.range m, B2 t) = B2 0 + ∑ t ∈ Finset.range (m-1), B2 (t+1) := by
      have h := Finset.sum_range_succ' B2 (m-1)
      rw [show (∑ t ∈ Finset.range m, B2 t) = ∑ t ∈ Finset.range ((m-1)+1), B2 t from by
        congr 1
        rw [show (m-1)+1 = m by omega]]
      rw [h]
      ring
    have hB1split : (∑ t ∈ Finset.range m, B1 t) = B1 0 + ∑ t ∈ Finset.range (m-1), B1 (t+1) := by
      have h := Finset.sum_range_succ' B1 (m-1)
      rw [show (∑ t ∈ Finset.range m, B1 t) = ∑ t ∈ Finset.range ((m-1)+1), B1 t from by
        congr 1
        rw [show (m-1)+1 = m by omega]]
      rw [h]
      ring
    rw [Finset.sum_range_succ B1 m, hB2split, hB1split, hB1zero, zero_add]
    rw [show (∑ t ∈ Finset.range (m-1), B1 (t+1)) + B1 m + (B2 0 + ∑ t ∈ Finset.range (m-1), B2 (t+1))
        = B1 m + B2 0 + ((∑ t ∈ Finset.range (m-1), B1 (t+1)) + (∑ t ∈ Finset.range (m-1), B2 (t+1))) from by
      ring]
    rw [Finset.sum_add_distrib]
  rw [hpeel]
  have hB1m : B1 m = - ((-1:R)^(n*m)) * (genEval R X α (AQ m) * genEval R X β (QQ m (m+1)))
      + ((-1:R)^((m-1)*(n+1)+n)) * (genEval R X α (AQ m) * DBQ m) := by
    dsimp only [B1, sg]
    rw [if_neg (by omega : ¬ m = 0)]
    have hrel : (∑ p ∈ Finset.range (m+2), ((-1:R)^p) * genEval R X β (QQ m p))
        = genEval R X (cochainDiff R X β) (X.map (Qmap n m m (by omega)).op σ) := hrelQ ⟨m, by omega⟩
    have hsplit : (∑ p ∈ Finset.range (m+2), ((-1:R)^p) * genEval R X β (QQ m p))
        = (∑ r ∈ Finset.range (m+1), ((-1:R)^r) * genEval R X β (QQ m r))
          + ((-1:R)^(m+1)) * genEval R X β (QQ m (m+1)) := by
      rw [show m+2 = (m+1)+1 by omega]
      exact Finset.sum_range_succ (fun p => ((-1:R)^p) * genEval R X β (QQ m p)) (m+1)
    have hpre : (∑ r ∈ Finset.range (m+1), ((-1:R)^r) * genEval R X β (QQ m r))
        = genEval R X (cochainDiff R X β) (X.map (Qmap n m m (by omega)).op σ)
          - (((-1:R)^(m+1)) * genEval R X β (QQ m (m+1))) := by
      rw [hsplit] at hrel
      exact eq_sub_of_add_eq hrel
    rw [hpre]
    rw [show DBQ m = genEval R X (cochainDiff R X β) (X.map (Qmap n m m (by omega)).op σ) from by
      dsimp only [DBQ]
      rw [dif_pos (by omega : m ≤ m)]]
    rw [show ((-1:R)^((m-1)*(n+1)+n)) * (genEval R X α (AQ m) *
          (genEval R X (cochainDiff R X β) (X.map (Qmap n m m (by omega)).op σ)
            - (((-1:R)^(m+1)) * genEval R X β (QQ m (m+1)))))
        = - (((-1:R)^((m-1)*(n+1)+n)) * ((-1:R)^(m+1))) *
              (genEval R X α (AQ m) * genEval R X β (QQ m (m+1)))
          + ((-1:R)^((m-1)*(n+1)+n)) *
              (genEval R X α (AQ m) * genEval R X (cochainDiff R X β) (X.map (Qmap n m m (by omega)).op σ)) from by
      ring]
    rw [show ((-1:R)^((m-1)*(n+1)+n)) * ((-1:R)^(m+1)) = ((-1:R)^(n*m)) from by
      rw [← pow_add]
      rw [show (m-1)*(n+1)+n + (m+1) = n*m + 2*m by
        have h1 : (m-1)*(n+1) = (m-1)*n + (m-1) := by rw [Nat.mul_add, mul_one]
        have h2 : m*n = (m-1)*n + n := by
          calc m*n = ((m-1)+1)*n := by rw [Nat.sub_add_cancel hm]
            _ = (m-1)*n + 1*n := by rw [add_mul]
            _ = (m-1)*n + n := by rw [one_mul]
        have h3 : n*m = m*n := Nat.mul_comm n m
        omega]
      rw [negOnePowAddTwoMul]]
  have hB2zero : B2 0 = genEval R X α (AQ 0) * genEval R X β (QQ 0 0)
      - genEval R X α (AQ 0) * DBQ 0 := by
    dsimp only [B2, sg]
    rw [if_neg (by omega : ¬ (0:ℕ) = m)]
    simp only [Nat.zero_mul, Nat.mul_zero, zero_add, Nat.sub_zero]
    have hrel : (∑ p ∈ Finset.range (m+2), ((-1:R)^p) * genEval R X β (QQ 0 p))
        = genEval R X (cochainDiff R X β) (X.map (Qmap n m 0 (by omega)).op σ) := hrelQ ⟨0, by omega⟩
    have hsplit : (∑ p ∈ Finset.range (m+2), ((-1:R)^p) * genEval R X β (QQ 0 p))
        = (∑ i ∈ Finset.range (m+1), ((-1:R)^(i+1)) * genEval R X β (QQ 0 (i+1)))
          + genEval R X β (QQ 0 0) := by
      rw [show m+2 = (m+1)+1 by omega]
      rw [Finset.sum_range_succ' (fun p => ((-1:R)^p) * genEval R X β (QQ 0 p)) (m+1)]
      simp only [pow_zero, one_mul]
    have htail : (∑ i ∈ Finset.range (m+1), ((-1:R)^(i+1)) * genEval R X β (QQ 0 (i+1)))
        = genEval R X (cochainDiff R X β) (X.map (Qmap n m 0 (by omega)).op σ)
          - genEval R X β (QQ 0 0) := by
      rw [hsplit] at hrel
      exact eq_sub_of_add_eq hrel
    rw [show (∑ i ∈ Finset.range (m+1), ((-1:R)^(n+i)) * genEval R X β (QQ 0 (1+i)))
        = ((-1:R)^(n-1)) *
            (∑ i ∈ Finset.range (m+1), ((-1:R)^(i+1)) * genEval R X β (QQ 0 (i+1))) from by
      rw [show (∑ i ∈ Finset.range (m+1), ((-1:R)^(n+i)) * genEval R X β (QQ 0 (1+i)))
          = ∑ i ∈ Finset.range (m+1), ((-1:R)^(n+i)) * genEval R X β (QQ 0 (i+1)) from by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [show 1+i = i+1 by omega]]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [show (-1:R)^(n-1) * (((-1:R)^(i+1)) * genEval R X β (QQ 0 (i+1)))
          = (((-1:R)^(n-1)) * ((-1:R)^(i+1))) * genEval R X β (QQ 0 (i+1)) from by ring]
      rw [← pow_add]
      rw [show n-1+(i+1) = n+i by omega]]
    rw [htail]
    rw [show DBQ 0 = genEval R X (cochainDiff R X β) (X.map (Qmap n m 0 (by omega)).op σ) from by
      dsimp only [DBQ]
      rw [dif_pos (by omega : (0:ℕ) ≤ m)]]
    rw [show ((-1:R)^n) * (genEval R X α (AQ 0) * (((-1:R)^(n-1)) *
          (genEval R X (cochainDiff R X β) (X.map (Qmap n m 0 (by omega)).op σ) - genEval R X β (QQ 0 0))))
        = (((-1:R)^n) * ((-1:R)^(n-1))) * (genEval R X α (AQ 0) *
            (genEval R X (cochainDiff R X β) (X.map (Qmap n m 0 (by omega)).op σ) - genEval R X β (QQ 0 0))) from by
      ring]
    rw [show ((-1:R)^n) * ((-1:R)^(n-1)) = -1 from by
      rw [← pow_add]
      rw [show n + (n-1) = 2*(n-1) + 1 by omega]
      rw [pow_add, pow_one, negOnePowTwoMul]
      ring]
    ring
  rw [hB1m, hB2zero]
  -- the interior blocks, in the form of the `δβ`-block of the shifted product
  rw [show (∑ u ∈ Finset.range (m-1), (B1 (u+1) + B2 (u+1)))
      = (∑ u ∈ Finset.range (m-1), ((-1:R)^(u*(n+1)+n)) * DBS (u+1)) from by
    refine Finset.sum_congr rfl fun u hu => ?_
    rw [Finset.mem_range] at hu
    rw [hcancel (u+1) (by omega) (by omega)]
    rw [show u+1-1 = u by omega]]
  -- the two terms contributed by `δα` and by `δβ`
  have hDWsum : (∑ s : Fin m, DW s) = genEval R X
      (h1 ▸ cup1 R X (n+1) m (cochainDiff R X α) β) σ := by
    rw [show genEval R X (h1 ▸ cup1 R X (n+1) m (cochainDiff R X α) β) σ
        = genEval R X (cup1 R X (n+1) m (cochainDiff R X α) β)
            (X.map (shmap ((n+1)+m-1) (n+m) h1).op σ) from
      genEval_cast h1 (cup1 R X (n+1) m (cochainDiff R X α) β) σ]
    rw [cup1ShiftedLeftR]
    refine Finset.sum_congr rfl fun s _ => ?_
    dsimp only [DW, sg]
    rw [show YQ s.val = X.map (Ymap n m s.val (by have := s.isLt; omega)).op σ from by
      dsimp only [YQ]
      rw [dif_pos s.isLt]]
    rw [← pow_add]
    rw [show s.val*(n+1)+n + (s.val+1) = s.val*((n+1)+1) + ((n+1)) by
      have h : s.val*((n+1)+1) = s.val*(n+1) + s.val := by ring
      omega]
    ring
  have hDBsum :
      (∑ u ∈ Finset.range (m-1), ((-1:R)^(u*(n+1)+n)) * DBS (u+1))
        + ((-1:R)^((m-1)*(n+1)+n)) * DBS m - DBS 0
      = ((-1:R)^(n+1)) * genEval R X
          (h2 ▸ cup1 R X n (m+1) α (cochainDiff R X β)) σ := by
    rw [show genEval R X (h2 ▸ cup1 R X n (m+1) α (cochainDiff R X β)) σ
        = genEval R X (cup1 R X n (m+1) α (cochainDiff R X β))
            (X.map (shmap (n+(m+1)-1) (n+m) h2).op σ) from
      genEval_cast h2 (cup1 R X n (m+1) α (cochainDiff R X β)) σ]
    rw [cup1ShiftedRightR]
    rw [show (∑ t : Fin (m+1), ((-1:R)^(t.val*(n+1)+n)) *
          genEval R X α (X.map (Amap n m t.val (by have := t.isLt; omega)).op σ) *
          genEval R X (cochainDiff R X β) (X.map (Qmap n m t.val (by have := t.isLt; omega)).op σ))
        = (∑ t : Fin (m+1), ((-1:R)^(t.val*(n+1)+n)) * DBS t.val) from by
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [show DBS t.val = (genEval R X α (X.map (Amap n m t.val (by have := t.isLt; omega)).op σ) *
           genEval R X (cochainDiff R X β) (X.map (Qmap n m t.val (by have := t.isLt; omega)).op σ)) from by
        dsimp only [DBS, DBQ, AQ]
        rw [dif_pos (by have := t.isLt; omega : t.val ≤ m),
            dif_pos (by have := t.isLt; omega : t.val ≤ m)]]
      ring]
    rw [show (∑ t : Fin (m+1), ((-1:R)^(t.val*(n+1)+n)) * DBS t.val)
        = (∑ t ∈ Finset.range (m+1), ((-1:R)^(t*(n+1)+n)) * DBS t) from by
      rw [sum_range_eq_fin]]
    rw [← powSignReindex R n m hm DBS]
  -- the two cup terms of the formula
  have hR : genEval R X (Work.Cohomology.cup R X α β) σ
        - ((-1:R)^(n*m)) * genEval R X ((Nat.add_comm m n) ▸ Work.Cohomology.cup R X β α) σ
      = genEval R X α (X.map (frontIncl n (n+m) (by omega)).op σ) * genEval R X β (X.map (backIncl n m).op σ)
        - ((-1:R)^(n*m)) * (genEval R X β (X.map (frontIncl m (n+m) (by omega)).op σ) *
            genEval R X α (X.map (Amap n m m (by omega)).op σ)) := by
    rw [show genEval R X (Work.Cohomology.cup R X α β) σ
        = genEval R X α (X.map (frontIncl n (n+m) (by omega)).op σ) * genEval R X β (X.map (backIncl n m).op σ) from by
      exact cup_apply' α β σ]
    rw [show genEval R X ((Nat.add_comm m n) ▸ Work.Cohomology.cup R X β α) σ
        = genEval R X β (X.map (frontIncl m (n+m) (by omega)).op σ) *
            genEval R X α (X.map (Amap n m m (by omega)).op σ) from by
      rw [show genEval R X ((Nat.add_comm m n) ▸ Work.Cohomology.cup R X β α) σ
          = genEval R X (Work.Cohomology.cup R X β α)
              (X.map (shmap (m+n) (n+m) (Nat.add_comm m n)).op σ) from
        genEval_cast (Nat.add_comm m n) (Work.Cohomology.cup R X β α) σ]
      rw [show genEval R X (Work.Cohomology.cup R X β α) (X.map (shmap (m+n) (n+m) (Nat.add_comm m n)).op σ)
          = genEval R X β (frontFace X m (m+n) (by omega) (X.map (shmap (m+n) (n+m) (Nat.add_comm m n)).op σ)) *
            genEval R X α (backFace X m n (X.map (shmap (m+n) (n+m) (Nat.add_comm m n)).op σ)) from
        cup_apply' β α (X.map (shmap (m+n) (n+m) (Nat.add_comm m n)).op σ)]
      congr 1
      · rw [show frontFace X m (m+n) (by omega) (X.map (shmap (m+n) (n+m) (Nat.add_comm m n)).op σ)
            = X.map (frontIncl m (n+m) (by omega)).op σ from by
          rw [frontFace, map_op_comp, frontIncl_comp_shmap]]
      · rw [show backFace X m n (X.map (shmap (m+n) (n+m) (Nat.add_comm m n)).op σ)
            = X.map (Amap n m m (by omega)).op σ from by
          rw [backFace, map_op_comp, backIncl_comp_shmap]]]
  rw [hR, ← hDWsum, ← hDBsum]
  dsimp only [DBS]
  -- identify the four faces
  -- identify the four faces
  rw [show AQ 0 = X.map (frontIncl n (n+m) (by omega)).op σ from by
    dsimp only [AQ]
    rw [dif_pos (by omega : (0:ℕ) ≤ m), Amap_zero_eq_frontIncl]]
  rw [show QQ 0 0 = X.map (backIncl n m).op σ from by
    dsimp only [QQ]
    rw [dif_pos (by omega : (0:ℕ) ≤ m), dif_pos (by omega : (0:ℕ) ≤ m+1)]
    exact Qcomp_zero_of σ (⟨0, by omega⟩ : Fin (m+2)) rfl]
  rw [show AQ m = X.map (Amap n m m (by omega)).op σ from by
    dsimp only [AQ]
    rw [dif_pos (by omega : m ≤ m)]]
  rw [show QQ m (m+1) = X.map (frontIncl m (n+m) (by omega)).op σ from by
    dsimp only [QQ]
    rw [dif_pos (by omega : m ≤ m), dif_pos (by omega : m+1 ≤ m+1)]
    exact Qcomp_top_of σ (⟨m+1, by omega⟩ : Fin (m+2)) rfl]
  ring

/-- The requested statement: the integral cup-1 coboundary formula for arbitrary cochains. -/
theorem cup1CoboundaryR : Work.Pi6.SQM.Cup1CobR := by
  intro R _ X n m α β hn hm
  exact cup1CoboundaryGen R X n m α β hn hm (by omega) (by omega) (by omega)

end

end Work.Pi6.SQM
