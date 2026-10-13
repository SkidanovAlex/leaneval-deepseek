/-
  `Work.CoreStep.RankSliceDefs` — definitions and basic lemmas for `Work.CoreStep.rankSlice_projRank`.

  The rank slice
  `{z ∈ X.set | finrank ((LinearMap.ker (jac S z)).map (basePrLin n m)) = r}`
  is a `SemiPf` set over the *same* chain as `X`: by the matrix identity
  `rank ([jac ; basePrLin]) = rank (jac) + finrank ((ker jac).map basePrLin)`
  it is a Boolean combination of minors of the matrices `jacP` and `[jacP ; P]`.

  The disjunction "some `k×k` minor is nonzero" is realised by the sum of the *squares* of all
  `k × k` minors (`sqSum`), so each format level `s ∈ [0, F]` contributes exactly one `Basic`
  per `Basic` of `X`.  The equations are `sqSum (jacP) (s+1) = 0` and `sqSum (stackP) (s+r+1) = 0`
  (i.e. `rank ≤ s` and `rank ≤ s + r`) and the strict inequalities are `sqSum (jacP) s > 0` and
  `sqSum (stackP) (s+r) > 0` (i.e. `rank ≥ s` and `rank ≥ s + r`).
-/
import Mathlib
import Submission.Work.Wilkies.E.Spec
import Submission.Work.WilE5.Basic
import Submission.Work.WilE2.Lift
import Submission.Work.WilE2.Ebc.Poly
import Submission.Work.WilE7.MainDesignDefs
import Submission.Work.WilE7.FiberCutDefs

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.CoreStep.RankSlice

open WilkiesDesign WilkiesDesign.E

variable {N j n r k m : ℕ}

/-! ## 1. The symbolic matrices and the sum of squares of the minors -/

/-- The symbolic Jacobian matrix of the equation family `h` over the chain `c`. -/
def jacP (c : EAChain N r) (h : Fin j → EAPoly N r) : Matrix (Fin j) (Fin N) (EAPoly N r) :=
  Matrix.of fun a l => eaD c l (h a)

@[simp] theorem jacP_apply (c : EAChain N r) (h : Fin j → EAPoly N r) (a : Fin j) (l : Fin N) :
    jacP c h a l = eaD c l (h a) := rfl

/-- The Jacobian rows stacked with the rows of a constant real matrix `P`. -/
def stackP (c : EAChain N r) (h : Fin j → EAPoly N r) (P : Matrix (Fin n) (Fin N) ℝ) :
    Matrix (Fin j ⊕ Fin n) (Fin N) (EAPoly N r) :=
  Matrix.of (Sum.elim (fun a l => eaD c l (h a)) (fun i l => MvPolynomial.C (P i l)))

@[simp] theorem stackP_inl (c : EAChain N r) (h : Fin j → EAPoly N r)
    (P : Matrix (Fin n) (Fin N) ℝ) (a : Fin j) (l : Fin N) :
    stackP c h P (Sum.inl a) l = eaD c l (h a) := rfl

@[simp] theorem stackP_inr (c : EAChain N r) (h : Fin j → EAPoly N r)
    (P : Matrix (Fin n) (Fin N) ℝ) (i : Fin n) (l : Fin N) :
    stackP c h P (Sum.inr i) l = MvPolynomial.C (P i l) := rfl

/-- The sum of the squares of all `k × k` minors of `M`. -/
def sqSum {ι : Type*} [Fintype ι] [DecidableEq ι] {N r : ℕ}
    (M : Matrix ι (Fin N) (EAPoly N r)) (k : ℕ) : EAPoly N r :=
  ∑ p : (Fin k ↪ ι) × (Fin k ↪ Fin N), ((M.submatrix p.1 p.2).det) ^ 2

/-- Evaluation at `z` as a ring homomorphism `EAPoly N r →+* ℝ`. -/
def evalHom (c : EAChain N r) (z : Fin N → ℝ) : EAPoly N r →+* ℝ :=
  MvPolynomial.eval (Sum.elim z fun j => Real.exp (c.ell j z))

theorem evalHom_apply (c : EAChain N r) (z : Fin N → ℝ) (Q : EAPoly N r) :
    evalHom c z Q = eaEval c Q z := rfl

@[simp] theorem evalHom_C (c : EAChain N r) (z : Fin N → ℝ) (a : ℝ) :
    evalHom c z (MvPolynomial.C a) = a := by
  rw [evalHom, MvPolynomial.eval_C]

theorem evalHom_det (c : EAChain N r) (M : Matrix (Fin m) (Fin m) (EAPoly N r)) (z : Fin N → ℝ) :
    evalHom c z M.det = (M.map (evalHom c z)).det := by
  rw [RingHom.map_det, RingHom.mapMatrix_apply]

/-- The evaluation of the symbolic minors is the determinant of the evaluated matrix. -/
theorem eaEval_sqSum {ι : Type*} [Fintype ι] [DecidableEq ι] (c : EAChain N r)
    (M : Matrix ι (Fin N) (EAPoly N r)) (z : Fin N → ℝ) :
    eaEval c (sqSum M k) z =
      ∑ p : (Fin k ↪ ι) × (Fin k ↪ Fin N),
        (((M.map (evalHom c z)).submatrix p.1 p.2).det) ^ 2 := by
  have h : eaEval c (sqSum M k) z = evalHom c z (sqSum M k) := evalHom_apply c z _
  rw [h, sqSum, map_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  conv_lhs => rw [map_pow]
  rw [evalHom_det, ← Matrix.submatrix_map]

/-- The evaluated symbolic Jacobian matrix. -/
def jacEval (c : EAChain N r) (h : Fin j → EAPoly N r) (z : Fin N → ℝ) :
    Matrix (Fin j) (Fin N) ℝ :=
  (jacP c h).map (evalHom c z)

@[simp] theorem jacEval_apply (c : EAChain N r) (h : Fin j → EAPoly N r) (z : Fin N → ℝ)
    (a : Fin j) (l : Fin N) : jacEval c h z a l = eaEval c (eaD c l (h a)) z := by
  simp [jacEval, evalHom_apply]

/-- The evaluated stacked matrix. -/
def stackEval (c : EAChain N r) (h : Fin j → EAPoly N r) (P : Matrix (Fin n) (Fin N) ℝ)
    (z : Fin N → ℝ) : Matrix (Fin j ⊕ Fin n) (Fin N) ℝ :=
  (stackP c h P).map (evalHom c z)

theorem stackEval_eq (c : EAChain N r) (h : Fin j → EAPoly N r) (P : Matrix (Fin n) (Fin N) ℝ)
    (z : Fin N → ℝ) : stackEval c h P z = Matrix.of (Sum.elim (jacEval c h z) P) := by
  ext x l
  rcases x with a | i
  · rfl
  · have hL : stackEval c h P z (Sum.inr i) l = P i l := by
      change evalHom c z (stackP c h P (Sum.inr i) l) = P i l
      rw [stackP_inr, evalHom_C]
    have hR : (Matrix.of (Sum.elim (jacEval c h z) P) (Sum.inr i)) l = P i l :=
      congrFun (Sum.elim_inr (jacEval c h z) P i) l
    rw [hL, hR]

/-! ## 2. Sums of squares of reals -/

theorem sum_sq_eq_zero_iff {ι : Type*} [Fintype ι] (f : ι → ℝ) :
    (∑ i, (f i) ^ 2) = 0 ↔ ∀ i, f i = 0 := by
  constructor
  · intro h i
    by_contra hi
    have h1 : (0:ℝ) < (f i) ^ 2 := sq_pos_of_ne_zero hi
    have h2 : (f i) ^ 2 ≤ ∑ t, (f t) ^ 2 :=
      Finset.single_le_sum (fun t _ => sq_nonneg (f t)) (Finset.mem_univ i)
    rw [h] at h2
    exact absurd h2 (not_le.mpr h1)
  · intro h
    exact Finset.sum_eq_zero fun i _ => by rw [h i]; ring

theorem sum_sq_pos_iff {ι : Type*} [Fintype ι] (f : ι → ℝ) :
    0 < (∑ i, (f i) ^ 2) ↔ ∃ i, f i ≠ 0 := by
  constructor
  · intro h
    by_contra hcon
    push Not at hcon
    rw [Finset.sum_eq_zero (fun i _ => by rw [hcon i]; ring)] at h
    exact lt_irrefl _ h
  · rintro ⟨i, hi⟩
    have h1 : (0:ℝ) < (f i) ^ 2 := sq_pos_of_ne_zero hi
    exact lt_of_lt_of_le h1
      (Finset.single_le_sum (fun t _ => sq_nonneg (f t)) (Finset.mem_univ i))

theorem eaEval_sqSum_eq_zero_iff {ι : Type*} [Fintype ι] [DecidableEq ι] (c : EAChain N r)
    (M : Matrix ι (Fin N) (EAPoly N r)) (z : Fin N → ℝ) :
    eaEval c (sqSum M k) z = 0 ↔
      ∀ (σ : Fin k ↪ ι) (τ : Fin k ↪ Fin N),
        ((M.map (evalHom c z)).submatrix σ τ).det = 0 := by
  rw [eaEval_sqSum, sum_sq_eq_zero_iff]
  exact ⟨fun h σ τ => h (σ, τ), fun h p => h p.1 p.2⟩

theorem eaEval_sqSum_pos_iff {ι : Type*} [Fintype ι] [DecidableEq ι] (c : EAChain N r)
    (M : Matrix ι (Fin N) (EAPoly N r)) (z : Fin N → ℝ) :
    0 < eaEval c (sqSum M k) z ↔
      ∃ (σ : Fin k ↪ ι) (τ : Fin k ↪ Fin N),
        ((M.map (evalHom c z)).submatrix σ τ).det ≠ 0 := by
  rw [eaEval_sqSum, sum_sq_pos_iff]
  constructor
  · rintro ⟨p, hp⟩
    exact ⟨p.1, p.2, hp⟩
  · rintro ⟨σ, τ, h⟩
    exact ⟨(σ, τ), h⟩

/-! ## 3. Degree bounds for the sums of squares -/

/-- `det` of a `k × k` submatrix, in terms of the entry degree bound `D`. -/
theorem totalDegree_det_submatrix_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι (Fin N) (EAPoly N r)) {D : ℕ} (hM : ∀ i l, (M i l).totalDegree ≤ D)
    (σ : Fin k ↪ ι) (τ : Fin k ↪ Fin N) :
    ((M.submatrix σ τ).det).totalDegree ≤ k * D := by
  have h := Work.WilE2.Matrix.det_totalDegree_le (M.submatrix σ τ) (fun _ : Fin k => D)
    (fun i l => hM _ _)
  simpa [Finset.sum_const, Fintype.card_fin, nsmul_eq_mul] using h

/-- The `sqSum` of the `k × k` minors has total degree at most `2 * (min k N) * D`. -/
theorem totalDegree_sqSum_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι (Fin N) (EAPoly N r)) {D : ℕ} (hM : ∀ i l, (M i l).totalDegree ≤ D) :
    (sqSum M k).totalDegree ≤ 2 * (min k N * D) := by
  rw [sqSum]
  refine MvPolynomial.totalDegree_finsetSum_le ?_
  intro p _
  have hk : k ≤ N := by
    have h := Fintype.card_le_of_injective (fun i : Fin k => (p.2 i : Fin N)) p.2.injective
    simpa using h
  rw [min_eq_left hk]
  refine (MvPolynomial.totalDegree_pow _ 2).trans ?_
  exact Nat.mul_le_mul_left 2 (totalDegree_det_submatrix_le M hM p.1 p.2)

theorem atomDeg_sqSum_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι (Fin N) (EAPoly N r)) {D : ℕ} (hM : ∀ i l, (M i l).totalDegree ≤ D) :
    atomDeg (sqSum M k) ≤ 2 * (min k N * D) + 1 := by
  have h := totalDegree_sqSum_le (k := k) M hM
  simp only [atomDeg]
  omega

theorem atomDeg_sqSum_le_of_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι (Fin N) (EAPoly N r)) {D F : ℕ} (hM : ∀ i l, (M i l).totalDegree ≤ D)
    (hN : N ≤ F) : atomDeg (sqSum M k) ≤ 2 * (F * D) + 1 := by
  refine (atomDeg_sqSum_le (k := k) M hM).trans ?_
  have h1 : min k N ≤ F := le_trans (min_le_right _ _) hN
  have h2 : min k N * D ≤ F * D := Nat.mul_le_mul_right _ h1
  omega

/-! ## 4. Canonicalisation of the basic list -/

theorem Basic.eq_nil_nil_of_deg_eq_zero {B : Basic N r} (h : B.deg = 0) :
    B = (⟨[], []⟩ : Basic N r) := by
  cases B with
  | mk eqs pos =>
    simp only [Basic.deg, List.map_append, List.sum_append] at h
    have heqs : eqs = [] := by
      by_contra hne
      obtain ⟨f, hf⟩ := List.exists_mem_of_ne_nil _ hne
      have hf1 : atomDeg f ≤ (eqs.map atomDeg).sum := List.le_sum_of_mem (List.mem_map_of_mem hf)
      have h3 : 1 ≤ atomDeg f := by simp [atomDeg]
      omega
    have hpos : pos = [] := by
      by_contra hne
      obtain ⟨f, hf⟩ := List.exists_mem_of_ne_nil _ hne
      have hf1 : atomDeg f ≤ (pos.map atomDeg).sum := List.le_sum_of_mem (List.mem_map_of_mem hf)
      have h3 : 1 ≤ atomDeg f := by simp [atomDeg]
      omega
    subst heqs; subst hpos; rfl

/-- Keep at most one basic of degree `0` (they are all the same basic) and all the others. -/
def keepBasics (l : List (Basic N r)) : List (Basic N r) :=
  (l.filter (fun B => decide (B.deg = 0))).take 1 ++ l.filter (fun B => decide (B.deg ≠ 0))

theorem mem_keepBasics {l : List (Basic N r)} {B : Basic N r} :
    B ∈ keepBasics l ↔ B ∈ l := by
  constructor
  · intro h
    rcases List.mem_append.mp h with h | h
    · exact List.filter_sublist.subset (List.take_sublist 1 _ |>.subset h)
    · exact List.filter_sublist.subset h
  · intro h
    by_cases hd : B.deg = 0
    · refine List.mem_append.mpr (Or.inl ?_)
      have hmem : B ∈ l.filter (fun B => decide (B.deg = 0)) := by
        rw [List.mem_filter]; exact ⟨h, by simp [hd]⟩
      obtain ⟨C, t, ht⟩ := List.exists_cons_of_ne_nil (List.ne_nil_of_mem hmem)
      have hCmem : C ∈ l.filter (fun B => decide (B.deg = 0)) := by
        rw [ht]; exact List.mem_cons_self ..
      have hCd : C.deg = 0 := by
        have h2 := (List.mem_filter.mp hCmem).2
        simpa using h2
      have hCB : C = B := by
        rw [Basic.eq_nil_nil_of_deg_eq_zero hCd, Basic.eq_nil_nil_of_deg_eq_zero hd]
      rw [ht, show List.take 1 (C :: t) = [C] from rfl, List.mem_singleton]
      exact hCB.symm
    · refine List.mem_append.mpr (Or.inr ?_)
      rw [List.mem_filter]; exact ⟨h, by simp [hd]⟩

theorem length_le_sum_of_one_le {l : List ℕ} (h : ∀ x ∈ l, 1 ≤ x) : l.length ≤ l.sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
    have ha : 1 ≤ a := h a (by simp)
    have ht : ∀ x ∈ t, 1 ≤ x := fun x hx => h x (by simp [hx])
    have := ih ht
    simp only [List.length_cons, List.sum_cons]
    omega

theorem length_keepBasics_le (l : List (Basic N r)) :
    (keepBasics l).length ≤ (l.map Basic.deg).sum + 1 := by
  have h1 : (keepBasics l).length ≤ 1 + (l.filter (fun B => decide (B.deg ≠ 0))).length := by
    rw [keepBasics, List.length_append]
    have h2 : (List.take 1 (l.filter fun B => decide (B.deg = 0))).length ≤ 1 := by
      rw [List.length_take]; omega
    omega
  have h2 : (l.filter (fun B => decide (B.deg ≠ 0))).length ≤
      ((l.filter (fun B => decide (B.deg ≠ 0))).map Basic.deg).sum := by
    rw [← List.length_map (f := Basic.deg)]
    refine length_le_sum_of_one_le ?_
    intro x hx
    obtain ⟨B, hB, rfl⟩ := List.mem_map.mp hx
    have hBd := (List.mem_filter.mp hB).2
    have hBd' : B.deg ≠ 0 := by simpa using hBd
    omega
  have h3 : ((l.filter (fun B => decide (B.deg ≠ 0))).map Basic.deg).sum ≤
      (l.map Basic.deg).sum := by
    refine List.Sublist.sum_le_sum ?_ (fun a _ => Nat.zero_le _)
    exact List.filter_sublist.map Basic.deg
  omega

/-! ## 5. The rank slice as a `SemiPf` set -/

/-- One `Basic` of the rank slice: the equations say `rank (jacP) ≤ s` and
`rank (stackP) ≤ s + rt`, the inequalities `rank (jacP) ≥ s` and `rank (stackP) ≥ s + rt`. -/
def rankBasic (c : EAChain N r) (h : Fin j → EAPoly N r) (P : Matrix (Fin n) (Fin N) ℝ)
    (rt s : ℕ) (B : Basic N r) : Basic N r :=
  { eqs := B.eqs ++ [sqSum (jacP c h) (s + 1), sqSum (stackP c h P) (s + rt + 1)],
    pos := B.pos ++ [sqSum (jacP c h) s, sqSum (stackP c h P) (s + rt)] }

theorem rankBasic_holds (c : EAChain N r) (h : Fin j → EAPoly N r)
    (P : Matrix (Fin n) (Fin N) ℝ) (rt s : ℕ) (B : Basic N r) (z : Fin N → ℝ) :
    (rankBasic c h P rt s B).holds c z ↔
      (B.holds c z ∧ eaEval c (sqSum (jacP c h) (s + 1)) z = 0 ∧
        eaEval c (sqSum (stackP c h P) (s + rt + 1)) z = 0 ∧
        0 < eaEval c (sqSum (jacP c h) s) z ∧
        0 < eaEval c (sqSum (stackP c h P) (s + rt)) z) := by
  have h1 : (rankBasic c h P rt s B).eqs
      = B.eqs ++ [sqSum (jacP c h) (s + 1), sqSum (stackP c h P) (s + rt + 1)] := rfl
  have h2 : (rankBasic c h P rt s B).pos
      = B.pos ++ [sqSum (jacP c h) s, sqSum (stackP c h P) (s + rt)] := rfl
  simp only [Basic.holds, h1, h2]
  constructor
  · intro hh
    exact ⟨⟨fun f hf => hh.1 f (List.mem_append.mpr (Or.inl hf)),
        fun g hg => hh.2 g (List.mem_append.mpr (Or.inl hg))⟩,
      hh.1 _ (by simp), hh.1 _ (by simp), hh.2 _ (by simp), hh.2 _ (by simp)⟩
  · rintro ⟨⟨heqs, hpos⟩, h3, h4, h5, h6⟩
    refine ⟨fun f hf => ?_, fun g hg => ?_⟩
    · rcases List.mem_append.mp hf with hf | hf
      · exact heqs f hf
      · rcases List.mem_cons.mp hf with hf | hf
        · rw [hf]; exact h3
        · rw [List.mem_singleton.mp hf]; exact h4
    · rcases List.mem_append.mp hg with hg | hg
      · exact hpos g hg
      · rcases List.mem_cons.mp hg with hg | hg
        · rw [hg]; exact h5
        · rw [List.mem_singleton.mp hg]; exact h6

theorem rankBasic_deg (c : EAChain N r) (h : Fin j → EAPoly N r)
    (P : Matrix (Fin n) (Fin N) ℝ) (rt s : ℕ) (B : Basic N r) :
    (rankBasic c h P rt s B).deg = B.deg + atomDeg (sqSum (jacP c h) (s + 1)) +
      atomDeg (sqSum (stackP c h P) (s + rt + 1)) + atomDeg (sqSum (jacP c h) s) +
      atomDeg (sqSum (stackP c h P) (s + rt)) := by
  simp only [Basic.deg, rankBasic, List.map_append, List.sum_append, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, add_zero]
  ring

/-- The list of basics of the rank slice: one branch per (`canonicalised`) basic of `X` and per
format level `s ≤ F`. -/
def rankBasics (c : EAChain N r) (h : Fin j → EAPoly N r) (P : Matrix (Fin n) (Fin N) ℝ)
    (F rt : ℕ) (l : List (Basic N r)) : List (Basic N r) :=
  (keepBasics l).flatMap fun B => (List.range (F + 1)).map fun s => rankBasic c h P rt s B

/-- The rank slice, as a `SemiPf` set over the chain of `X`. -/
def rankSemiPf (X : SemiPf N) (h : Fin j → EAPoly N X.r) (P : Matrix (Fin n) (Fin N) ℝ)
    (F rt : ℕ) : SemiPf N :=
  ⟨X.r, X.c, rankBasics X.c h P F rt X.basics⟩

@[simp] theorem rankSemiPf_r (X : SemiPf N) (h : Fin j → EAPoly N X.r)
    (P : Matrix (Fin n) (Fin N) ℝ) (F rt : ℕ) : (rankSemiPf X h P F rt).r = X.r := rfl

@[simp] theorem rankSemiPf_c (X : SemiPf N) (h : Fin j → EAPoly N X.r)
    (P : Matrix (Fin n) (Fin N) ℝ) (F rt : ℕ) : (rankSemiPf X h P F rt).c = X.c := rfl

@[simp] theorem rankSemiPf_basics (X : SemiPf N) (h : Fin j → EAPoly N X.r)
    (P : Matrix (Fin n) (Fin N) ℝ) (F rt : ℕ) :
    (rankSemiPf X h P F rt).basics = rankBasics X.c h P F rt X.basics := rfl

theorem rankSemiPf_fmt (X : SemiPf N) (h : Fin j → EAPoly N X.r)
    (P : Matrix (Fin n) (Fin N) ℝ) (F rt : ℕ) : (rankSemiPf X h P F rt).fmt = X.fmt := rfl

/-- Membership in the rank slice: the level `s ≤ F` is the rank of `jacP` and `s + rt` the rank
of `stackP`. -/
theorem mem_rankSemiPf_set_iff (X : SemiPf N) (h : Fin j → EAPoly N X.r)
    (P : Matrix (Fin n) (Fin N) ℝ) (F rt : ℕ) (z : Fin N → ℝ) :
    z ∈ (rankSemiPf X h P F rt).set ↔
      z ∈ X.set ∧ ∃ s ≤ F,
        (eaEval X.c (sqSum (jacP X.c h) (s + 1)) z = 0 ∧
          eaEval X.c (sqSum (stackP X.c h P) (s + rt + 1)) z = 0 ∧
          0 < eaEval X.c (sqSum (jacP X.c h) s) z ∧
          0 < eaEval X.c (sqSum (stackP X.c h P) (s + rt)) z) := by
  show (z ∈ cubeC N ∧ ∃ β ∈ rankBasics X.c h P F rt X.basics, β.holds X.c z) ↔
      z ∈ X.set ∧ ∃ s ≤ F,
        (eaEval X.c (sqSum (jacP X.c h) (s + 1)) z = 0 ∧
          eaEval X.c (sqSum (stackP X.c h P) (s + rt + 1)) z = 0 ∧
          0 < eaEval X.c (sqSum (jacP X.c h) s) z ∧
          0 < eaEval X.c (sqSum (stackP X.c h P) (s + rt)) z)
  constructor
  · rintro ⟨hc, β, hβ, hβh⟩
    obtain ⟨B, hB, hs⟩ := List.mem_flatMap.mp hβ
    obtain ⟨s, hs', heq⟩ := List.mem_map.mp hs
    rw [← heq] at hβh
    have hBl : B ∈ X.basics := mem_keepBasics.mp hB
    have hF' : s ≤ F := by
      have := List.mem_range.mp hs'
      omega
    obtain ⟨hbb, h1, h2, h3, h4⟩ := (rankBasic_holds X.c h P rt s B z).mp hβh
    exact ⟨⟨hc, B, hBl, hbb⟩, s, hF', h1, h2, h3, h4⟩
  · rintro ⟨⟨hc, B, hB, hBh⟩, s, hF', h1, h2, h3, h4⟩
    refine ⟨hc, rankBasic X.c h P rt s B, ?_, ?_⟩
    · exact List.mem_flatMap.mpr ⟨B, mem_keepBasics.mpr hB,
        List.mem_map.mpr ⟨s, List.mem_range.mpr (by omega), rfl⟩⟩
    · exact (rankBasic_holds X.c h P rt s B z).mpr ⟨hBh, h1, h2, h3, h4⟩

/-- The degree bound for the rank slice. -/
theorem rankSemiPf_deg_le (X : SemiPf N) (h : Fin j → EAPoly N X.r)
    (P : Matrix (Fin n) (Fin N) ℝ) (F rt D : ℕ)
    (hX : ∀ B ∈ X.basics, B.deg ≤ D)
    (hjac : ∀ i l, (jacP X.c h i l).totalDegree ≤ D)
    (hstack : ∀ i l, (stackP X.c h P i l).totalDegree ≤ D)
    (hN : N ≤ F) :
    (rankSemiPf X h P F rt).deg ≤
      ((X.basics.map Basic.deg).sum + 1) * (F + 1) * (D + 4 * (2 * (F * D) + 1)) := by
  have hmem : ∀ B ∈ rankBasics X.c h P F rt X.basics,
      B.deg ≤ D + 4 * (2 * (F * D) + 1) := by
    intro Bc hBc
    obtain ⟨B', hB', hs⟩ := List.mem_flatMap.mp hBc
    obtain ⟨s, -, heq⟩ := List.mem_map.mp hs
    have hB'X : B' ∈ X.basics := mem_keepBasics.mp hB'
    rw [← heq, rankBasic_deg]
    have h1 := hX B' hB'X
    have h2 := atomDeg_sqSum_le_of_le (jacP X.c h) hjac hN (k := s + 1)
    have h3 := atomDeg_sqSum_le_of_le (stackP X.c h P) hstack hN (k := s + rt + 1)
    have h4 := atomDeg_sqSum_le_of_le (jacP X.c h) hjac hN (k := s)
    have h5 := atomDeg_sqSum_le_of_le (stackP X.c h P) hstack hN (k := s + rt)
    omega
  have hmem2 : ∀ x ∈ (rankBasics X.c h P F rt X.basics).map Basic.deg,
      x ≤ D + 4 * (2 * (F * D) + 1) := by
    intro x hx
    obtain ⟨B, hB, rfl⟩ := List.mem_map.mp hx
    exact hmem B hB
  have h1 : (rankSemiPf X h P F rt).deg ≤
      (rankBasics X.c h P F rt X.basics).length • (D + 4 * (2 * (F * D) + 1)) := by
    rw [SemiPf.deg, rankSemiPf_basics]
    have h := List.sum_le_length_nsmul
      (List.map Basic.deg (rankBasics X.c h P F rt X.basics))
      (D + 4 * (2 * (F * D) + 1)) hmem2
    rwa [List.length_map] at h
  have h2 : (rankBasics X.c h P F rt X.basics).length =
      (keepBasics X.basics).length * (F + 1) := by
    rw [rankBasics, List.length_flatMap]
    simp [List.length_map, List.length_range]
  have h3 : (keepBasics X.basics).length ≤ (X.basics.map Basic.deg).sum + 1 :=
    length_keepBasics_le _
  rw [h2, nsmul_eq_mul] at h1
  have h4 : (keepBasics X.basics).length * (F + 1) ≤
      ((X.basics.map Basic.deg).sum + 1) * (F + 1) :=
    Nat.mul_le_mul_right _ h3
  calc (rankSemiPf X h P F rt).deg
      ≤ (keepBasics X.basics).length * (F + 1) * (D + 4 * (2 * (F * D) + 1)) := h1
    _ ≤ ((X.basics.map Basic.deg).sum + 1) * (F + 1) * (D + 4 * (2 * (F * D) + 1)) := by
        exact Nat.mul_le_mul_right _ h4

end Work.CoreStep.RankSlice
