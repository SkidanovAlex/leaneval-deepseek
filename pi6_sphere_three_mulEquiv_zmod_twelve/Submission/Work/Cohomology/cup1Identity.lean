import Mathlib
import Submission.Work.Cohomology.cup1defs
import Submission.Work.Cohomology.cup1Aux
import Submission.Work.Cohomology.cup1Shuffle
import Submission.Work.Cohomology.cup1Faces
import Submission.Work.Cohomology.cup1Cast

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 4000000

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Cohomology

noncomputable section

variable {R : Type} [CommRing R] {X : SSet}

lemma genEval_sub {k : ℕ} (f g : Cochain R X k) (σ : X _⦋k⦌) :
    genEval R X (f - g) σ = genEval R X f σ - genEval R X g σ := by
  simp only [genEval, LinearMap.sub_apply]

/-- The cocycle relation in "position" form: the alternating sum of a cocycle over the faces of a
simplex vanishes. -/
lemma cocycle_sum {k : ℕ} (γ : Cochain R X k) (hγ : cochainDiff R X γ = 0)
    (τ : X _⦋k+1⦌) :
    ∑ i : Fin (k+2), ((-1:R)^(i:ℕ)) * genEval R X γ (X.δ i τ) = 0 := by
  have h1 : genEval R X (cochainDiff R X γ) τ = 0 := by
    rw [hγ]
    simp only [genEval, LinearMap.zero_apply]
  rwa [genEval_cochainDiff] at h1

lemma neg_one_pow_two_mul (k : ℕ) : (-1:R)^(2*k) = 1 := by
  rw [pow_mul, neg_one_sq, one_pow]

lemma neg_one_pow_add_two_mul (a k : ℕ) : (-1:R)^(a + 2*k) = (-1:R)^a := by
  rw [pow_add, neg_one_pow_two_mul, mul_one]

theorem cup1Identity (R : Type) [CommRing R] (X : SSet) (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m)
    (α : Cochain R X n) (β : Cochain R X m)
    (hα : cochainDiff R X α = 0) (hβ : cochainDiff R X β = 0) :
    (Nat.sub_add_cancel (by omega : 1 ≤ n + m)) ▸ (cochainDiff R X (cup1 R X n m α β)) =
      cup R X α β - ((-1 : R) ^ (n * m)) • ((Nat.add_comm m n) ▸ cup R X β α) := by
  apply genEval_ext
  intro σ
  rw [genEval_sub, genEval_smul, smul_eq_mul]
  set hcast : n + m - 1 + 1 = n + m := Nat.sub_add_cancel (by omega : 1 ≤ n + m) with hhcast
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
  -- the `α`-cocycle relation on `[s,s+n+1]`
  have hcocW : ∀ s : Fin m,
      (∑ j ∈ Finset.range (n+2), ((-1:R)^j) * genEval R X α (WQ s.val j)) = 0 := by
    intro s
    rw [sum_range_eq_fin]
    trans ∑ j : Fin (n+2),
        ((-1:R)^(j:ℕ)) * genEval R X α (X.δ j (X.map (Wmap n m s.val (by have := s.isLt; omega)).op σ))
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [show X.δ j (X.map (Wmap n m s.val (by have := s.isLt; omega)).op σ) = WQ s.val (j:ℕ) from by
        rw [SimplicialObject.δ_def, map_op_comp]
        simp only [WQ, dif_pos s.isLt, dif_pos (by omega : (j:ℕ) ≤ n + 1)]]
    · exact cocycle_sum α hα _
  have hmid : ∀ s : Fin m,
      (∑ j ∈ Finset.range n, ((-1:R)^j) * genEval R X α (WQ s.val (j+1)))
        = genEval R X α (WQ s.val 0) + ((-1:R)^(n+1)) * genEval R X α (WQ s.val (n+1)) := by
    intro s
    have h0 := hcocW s
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
          (genEval R X α (AQ s.val) * genEval R X β (YQ s.val)) := by
    intro s
    dsimp only [P2, X1, sg]
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
      rw [neg_one_pow_add_two_mul]]
  have hS2 : (∑ s : Fin m, (P1 s + P2 s + P3 s)) = ∑ s : Fin m, (Q1 s + Q3 s) := by
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [hP2 s, hd s]
    rw [show P1 s + (X1 s + X3 s) + P3 s = (P1 s + X1 s) + (P3 s + X3 s) from by ring]
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
  -- the `β`-cocycle relation on `[0,t] ∪ [t+n, n+m]`
  have hcocQ : ∀ t : Fin (m+1),
      (∑ p ∈ Finset.range (m+2), ((-1:R)^p) * genEval R X β (QQ t.val p)) = 0 := by
    intro t
    rw [sum_range_eq_fin]
    trans ∑ p : Fin (m+2),
        ((-1:R)^(p:ℕ)) * genEval R X β (X.δ p (X.map (Qmap n m t.val (by have := t.isLt; omega)).op σ))
    · refine Finset.sum_congr rfl fun p _ => ?_
      rw [show X.δ p (X.map (Qmap n m t.val (by have := t.isLt; omega)).op σ) = QQ t.val (p:ℕ) from by
        rw [SimplicialObject.δ_def, map_op_comp]
        simp only [QQ, dif_pos (by omega : t.val ≤ m), dif_pos (by omega : (p:ℕ) ≤ m+1)]]
    · exact cocycle_sum β hβ _
  -- cancellation of the interior blocks
  have hcancel : ∀ u : ℕ, 1 ≤ u → u ≤ m - 1 → B1 u + B2 u = 0 := by
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
        rw [neg_one_pow_add_two_mul]]
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
    have hzero : (∑ p ∈ Finset.range (m+2), ((-1:R)^p) * genEval R X β (QQ u p)) = 0 :=
      hcocQ ⟨u, by omega⟩
    have hST : (∑ r ∈ Finset.range (u+1), ((-1:R)^r) * genEval R X β (QQ u r))
          + (∑ i ∈ Finset.range (m+1-u), ((-1:R)^(u+1+i)) * genEval R X β (QQ u (u+1+i))) = 0 := by
      rw [hcomb, hzero]
    rw [show (∑ r ∈ Finset.range (u+1), ((-1:R)^r) * genEval R X β (QQ u r))
          = - (∑ i ∈ Finset.range (m+1-u), ((-1:R)^(u+1+i)) * genEval R X β (QQ u (u+1+i))) from
        eq_neg_of_add_eq_zero_left hST]
    ring
  -- peel off the two end blocks
  have hpeel : (∑ t ∈ Finset.range (m+1), B1 t) + (∑ t ∈ Finset.range m, B2 t) = B1 m + B2 0 := by
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
    rw [show (∑ t ∈ Finset.range (m-1), B1 (t+1)) + (∑ t ∈ Finset.range (m-1), B2 (t+1)) = 0 from by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_eq_zero
      intro t ht
      rw [Finset.mem_range] at ht
      exact hcancel (t+1) (by omega) (by omega)]
    ring
  rw [hpeel]
  -- the two end blocks
  have hB1m : B1 m = - ((-1:R)^(n*m)) * (genEval R X α (AQ m) * genEval R X β (QQ m (m+1))) := by
    dsimp only [B1, sg]
    rw [if_neg (by omega : ¬ m = 0)]
    have hcoc : (∑ p ∈ Finset.range (m+2), ((-1:R)^p) * genEval R X β (QQ m p)) = 0 := hcocQ ⟨m, by omega⟩
    have hsplit : (∑ p ∈ Finset.range (m+2), ((-1:R)^p) * genEval R X β (QQ m p))
        = (∑ r ∈ Finset.range (m+1), ((-1:R)^r) * genEval R X β (QQ m r))
          + ((-1:R)^(m+1)) * genEval R X β (QQ m (m+1)) := by
      rw [show m+2 = (m+1)+1 by omega]
      exact Finset.sum_range_succ (fun p => ((-1:R)^p) * genEval R X β (QQ m p)) (m+1)
    have hpre : (∑ r ∈ Finset.range (m+1), ((-1:R)^r) * genEval R X β (QQ m r))
        = - (((-1:R)^(m+1)) * genEval R X β (QQ m (m+1))) := by
      rw [hsplit] at hcoc
      exact eq_neg_iff_add_eq_zero.mpr hcoc
    rw [hpre]
    rw [show ((-1:R)^((m-1)*(n+1)+n)) * (genEval R X α (AQ m) *
          (- (((-1:R)^(m+1)) * genEval R X β (QQ m (m+1)))))
        = - ((-1:R)^(n*m)) * (genEval R X α (AQ m) * genEval R X β (QQ m (m+1))) from by
      rw [show ((-1:R)^((m-1)*(n+1)+n)) * (genEval R X α (AQ m) *
            (- (((-1:R)^(m+1)) * genEval R X β (QQ m (m+1)))))
          = - ((((-1:R)^((m-1)*(n+1)+n)) * ((-1:R)^(m+1)) *
              (genEval R X α (AQ m) * genEval R X β (QQ m (m+1))))) from by ring]
      rw [← pow_add]
      rw [show (m-1)*(n+1)+n + (m+1) = n*m + 2*m by
        have h1 : (m-1)*(n+1) = (m-1)*n + (m-1) := by rw [Nat.mul_add, mul_one]
        have h2 : m*n = (m-1)*n + n := by
          calc m*n = ((m-1)+1)*n := by rw [Nat.sub_add_cancel hm]
            _ = (m-1)*n + 1*n := by rw [add_mul]
            _ = (m-1)*n + n := by rw [one_mul]
        have h3 : n*m = m*n := Nat.mul_comm n m
        omega]
      rw [neg_one_pow_add_two_mul]
      ring]
  have hB2zero : B2 0 = genEval R X α (AQ 0) * genEval R X β (QQ 0 0) := by
    dsimp only [B2, sg]
    rw [if_neg (by omega : ¬ (0:ℕ) = m)]
    simp only [Nat.zero_mul, Nat.mul_zero, zero_add, Nat.sub_zero]
    have hcoc : (∑ p ∈ Finset.range (m+2), ((-1:R)^p) * genEval R X β (QQ 0 p)) = 0 := hcocQ ⟨0, by omega⟩
    have hsplit : (∑ p ∈ Finset.range (m+2), ((-1:R)^p) * genEval R X β (QQ 0 p))
        = (∑ i ∈ Finset.range (m+1), ((-1:R)^(i+1)) * genEval R X β (QQ 0 (i+1)))
          + genEval R X β (QQ 0 0) := by
      rw [show m+2 = (m+1)+1 by omega]
      rw [Finset.sum_range_succ' (fun p => ((-1:R)^p) * genEval R X β (QQ 0 p)) (m+1)]
      simp only [pow_zero, one_mul]
    have htail : (∑ i ∈ Finset.range (m+1), ((-1:R)^(i+1)) * genEval R X β (QQ 0 (i+1)))
        = - genEval R X β (QQ 0 0) := by
      rw [hsplit] at hcoc
      exact eq_neg_iff_add_eq_zero.mpr hcoc
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
    rw [show ((-1:R)^n) * (genEval R X α (AQ 0) * (((-1:R)^(n-1)) * (- genEval R X β (QQ 0 0))))
        = genEval R X α (AQ 0) * genEval R X β (QQ 0 0) from by
      rw [show ((-1:R)^n) * (genEval R X α (AQ 0) * (((-1:R)^(n-1)) * (- genEval R X β (QQ 0 0))))
          = (((-1:R)^n) * ((-1:R)^(n-1)) * (-1)) *
              (genEval R X α (AQ 0) * genEval R X β (QQ 0 0)) from by ring]
      rw [← pow_add]
      rw [show n + (n-1) = 2*(n-1) + 1 by omega]
      rw [pow_add, pow_one, neg_one_pow_two_mul, one_mul]
      ring]
  rw [hB1m, hB2zero]
  -- the right hand side
  have hR : genEval R X (cup R X α β) σ
        - ((-1:R)^(n*m)) * genEval R X ((Nat.add_comm m n) ▸ cup R X β α) σ
      = genEval R X α (X.map (frontIncl n (n+m) (by omega)).op σ) * genEval R X β (X.map (backIncl n m).op σ)
        - ((-1:R)^(n*m)) * (genEval R X β (X.map (frontIncl m (n+m) (by omega)).op σ) *
            genEval R X α (X.map (Amap n m m (by omega)).op σ)) := by
    rw [show genEval R X (cup R X α β) σ
        = genEval R X α (X.map (frontIncl n (n+m) (by omega)).op σ) * genEval R X β (X.map (backIncl n m).op σ) from by
      exact cup_apply' α β σ]
    rw [show genEval R X ((Nat.add_comm m n) ▸ cup R X β α) σ
        = genEval R X β (X.map (frontIncl m (n+m) (by omega)).op σ) *
            genEval R X α (X.map (Amap n m m (by omega)).op σ) from by
      rw [genEval_cast]
      rw [show genEval R X (cup R X β α) (X.map (shmap (m+n) (n+m) (Nat.add_comm m n)).op σ)
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
  rw [hR]
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
