import Mathlib
import Submission.Work.Wilkies.E.Spec
import Submission.Work.WilE7.prod_semiPf
import Submission.Work.WilE7.ProdDefs
import Submission.Work.WilE7.prodSet
import Submission.Work.WilE7.prodDeg

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilE7
open WilkiesConjecture WilkiesDesign WilkiesDesign.E

/-! ## Elementary list facts -/

/-- Sum of `f a + c` over a list. -/
theorem List.sum_map_add_const {α : Type*} (l : List α) (f : α → ℕ) (c : ℕ) :
    (l.map (fun a => f a + c)).sum = (l.map f).sum + l.length * c := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    rw [ih]; ring

/-- Equal maps have equal sums. -/
theorem List.sum_map_congr {α : Type*} (l : List α) (f g : α → ℕ)
    (h : ∀ a ∈ l, f a = g a) : (l.map f).sum = (l.map g).sum := by
  rw [List.map_congr_left h]

/-- Length of `List.product`. -/
theorem List.length_product_list {α β : Type*} (l : List α) (l' : List β) :
    (l.product l').length = l.length * l'.length := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [product_cons_left, List.length_append, List.length_map, ih, List.length_cons]
    ring

/-- Semantics of a branch with extra equations. -/
theorem Basic.holds_appendEqs {k r : ℕ} (c : EAChain k r) (B : Basic k r)
    (E : List (EAPoly k r)) (z : Fin k → ℝ) :
    (⟨B.eqs ++ E, B.pos⟩ : Basic k r).holds c z ↔ B.holds c z ∧ ∀ f ∈ E, eaEval c f z = 0 := by
  simp only [Basic.holds, List.forall_mem_append]
  tauto

/-- Degree of a branch with extra equations. -/
theorem Basic.deg_appendEqs {k r : ℕ} (B : Basic k r) (E : List (EAPoly k r)) :
    (⟨B.eqs ++ E, B.pos⟩ : Basic k r).deg = B.deg + (E.map atomDeg).sum := by
  simp only [Basic.deg, List.map_append, List.sum_append]
  ring

/-! ## The diagonal equations `z_{A i} = z_{B i}` -/

/-- First copy of coordinate `i` (inside the first block of the fibre product). -/
def diagIdxA (p q : ℕ) (i : Fin p) : Fin ((p + q) + (p + q)) :=
  Fin.castAdd (p + q) (Fin.castAdd q i)

/-- Second copy of coordinate `i` (inside the second block of the fibre product). -/
def diagIdxB (p q : ℕ) (i : Fin p) : Fin ((p + q) + (p + q)) :=
  Fin.natAdd (p + q) (Fin.castAdd q i)

/-- The diagonal equation `z_{A i} - z_{B i} = 0` as an `EA`-polynomial. -/
def diagEq (p q r r' : ℕ) (i : Fin p) : EAPoly ((p + q) + (p + q)) (r + r') :=
  MvPolynomial.X (Sum.inl (diagIdxA p q i)) - MvPolynomial.X (Sum.inl (diagIdxB p q i))

/-- The list of diagonal equations. -/
def diagEqs (p q r r' : ℕ) : List (EAPoly ((p + q) + (p + q)) (r + r')) :=
  (List.finRange p).map (diagEq p q r r')

/-- Evaluation of a diagonal equation. -/
theorem eaEval_diagEq {p q r r' : ℕ} (c : EAChain ((p + q) + (p + q)) (r + r'))
    (i : Fin p) (z : Fin ((p + q) + (p + q)) → ℝ) :
    eaEval c (diagEq p q r r' i) z = z (diagIdxA p q i) - z (diagIdxB p q i) := by
  simp [diagEq, eaEval]

/-- The diagonal equations hold exactly when the two `p`-blocks agree. -/
theorem diagEqs_forall {p q r r' : ℕ} (c : EAChain ((p + q) + (p + q)) (r + r'))
    (z : Fin ((p + q) + (p + q)) → ℝ) :
    (∀ f ∈ diagEqs p q r r', eaEval c f z = 0) ↔
      projFirst p q (projFirst (p + q) (p + q) z) =
        projFirst p q (projSnd (p + q) (p + q) z) := by
  rw [diagEqs, List.forall_mem_map]
  constructor
  · intro h
    funext i
    have h0 := h i (List.mem_finRange i)
    rw [eaEval_diagEq] at h0
    exact sub_eq_zero.mp h0
  · intro h i _
    rw [eaEval_diagEq, sub_eq_zero]
    exact congrFun h i

/-! ## The fibre product -/

/-- The product of `X` and `X'` cut by the diagonal equations `z_{A i} = z_{B i}`.
Its ambient dimension is `(p+q)+(p+q)` and its chain is `EAChain.prod X.c X'.c`. -/
def fiberProdZ {p q : ℕ} (X X' : SemiPf (p + q)) : SemiPf ((p + q) + (p + q)) :=
  ⟨X.r + X'.r, EAChain.prod X.c X'.c,
   ((redBasics X).product (redBasics X')).map (fun b =>
     (⟨(Basic.prod b.1 b.2).eqs ++ diagEqs p q X.r X'.r, (Basic.prod b.1 b.2).pos⟩ :
       Basic ((p + q) + (p + q)) (X.r + X'.r)))⟩

theorem fiberProdZ_fmt {p q F : ℕ} (X X' : SemiPf (p + q))
    (hX : X.fmt ≤ F) (hX' : X'.fmt ≤ F) : (fiberProdZ X X').fmt ≤ 2 * F := by
  simp only [SemiPf.fmt, fiberProdZ] at hX hX' ⊢
  omega

theorem fiberProdZ_set {p q : ℕ} (X X' : SemiPf (p + q)) :
    (fiberProdZ X X').set = {z : Fin ((p + q) + (p + q)) → ℝ |
      projFirst (p + q) (p + q) z ∈ X.set ∧ projSnd (p + q) (p + q) z ∈ X'.set ∧
      projFirst p q (projFirst (p + q) (p + q) z) =
        projFirst p q (projSnd (p + q) (p + q) z)} := by
  ext z
  change (z ∈ cubeC ((p + q) + (p + q)) ∧ ∃ B ∈ ((redBasics X).product (redBasics X')).map
      (fun b => (⟨(Basic.prod b.1 b.2).eqs ++ diagEqs p q X.r X'.r,
        (Basic.prod b.1 b.2).pos⟩ : Basic ((p + q) + (p + q)) (X.r + X'.r))),
      B.holds (EAChain.prod X.c X'.c) z) ↔
    ((projFirst (p + q) (p + q) z ∈ cubeC (p + q) ∧
        ∃ B ∈ X.basics, B.holds X.c (projFirst (p + q) (p + q) z)) ∧
      (projSnd (p + q) (p + q) z ∈ cubeC (p + q) ∧
        ∃ B ∈ X'.basics, B.holds X'.c (projSnd (p + q) (p + q) z)) ∧
      projFirst p q (projFirst (p + q) (p + q) z) =
        projFirst p q (projSnd (p + q) (p + q) z))
  rw [cubeC_add z]
  have hkey : (∃ B ∈ ((redBasics X).product (redBasics X')).map
        (fun b => (⟨(Basic.prod b.1 b.2).eqs ++ diagEqs p q X.r X'.r,
          (Basic.prod b.1 b.2).pos⟩ : Basic ((p + q) + (p + q)) (X.r + X'.r))),
        B.holds (EAChain.prod X.c X'.c) z) ↔
      (∃ B ∈ redBasics X, B.holds X.c (projFirst (p + q) (p + q) z)) ∧
      (∃ B ∈ redBasics X', B.holds X'.c (projSnd (p + q) (p + q) z)) ∧
      (∀ f ∈ diagEqs p q X.r X'.r, eaEval (EAChain.prod X.c X'.c) f z = 0) := by
    rw [exists_mem_product_map]
    constructor
    · rintro ⟨a, ha, b, hb, hh⟩
      have hh2 : (⟨(Basic.prod a b).eqs ++ diagEqs p q X.r X'.r, (Basic.prod a b).pos⟩ :
          Basic ((p + q) + (p + q)) (X.r + X'.r)).holds (EAChain.prod X.c X'.c) z := hh
      obtain ⟨hh', hd⟩ := (Basic.holds_appendEqs (EAChain.prod X.c X'.c) (Basic.prod a b)
        (diagEqs p q X.r X'.r) z).mp hh2
      obtain ⟨h1, h2⟩ := (Basic.holds_prod X.c X'.c a b z).mp hh'
      exact ⟨⟨a, ha, h1⟩, ⟨b, hb, h2⟩, hd⟩
    · rintro ⟨⟨a, ha, h1⟩, ⟨b, hb, h2⟩, hd⟩
      refine ⟨a, ha, b, hb, ?_⟩
      exact (Basic.holds_appendEqs (EAChain.prod X.c X'.c) (Basic.prod a b)
        (diagEqs p q X.r X'.r) z).mpr
        ⟨(Basic.holds_prod X.c X'.c a b z).mpr ⟨h1, h2⟩, hd⟩
  rw [hkey, exists_holds_redBasics X (projFirst (p + q) (p + q) z),
    exists_holds_redBasics X' (projSnd (p + q) (p + q) z), diagEqs_forall]
  tauto

theorem fiberProdZ_deg {p q F : ℕ} (X X' : SemiPf (p + q)) (hX : X.fmt ≤ F) :
    (fiberProdZ X X').deg ≤ 2 * (1 + F) * (1 + (X.deg + X'.deg)) ^ 2 := by
  have hsum : (((redBasics X).product (redBasics X')).map
      (fun b => (Basic.prod b.1 b.2).deg)).sum ≤ 2 * (1 + (X.deg + X'.deg)) ^ 2 := by
    have h1 : (((redBasics X).product (redBasics X')).map
        (fun b => (Basic.prod b.1 b.2).deg)).sum
        ≤ (((redBasics X).product (redBasics X')).map
            (fun b => b.1.deg + b.2.deg)).sum :=
      sum_map_le_of_pointwise _ _ _ (fun b _ => Basic.prod_deg_le b.1 b.2)
    rw [sumProduct] at h1
    exact le_trans h1 (deg_bound_arith X.deg X'.deg (redBasics X).length (redBasics X').length
      ((redBasics X).map Basic.deg).sum ((redBasics X').map Basic.deg).sum
      (redBasics_length_le X) (redBasics_length_le X')
      (redBasics_deg_le X) (redBasics_deg_le X'))
  have hdeg : (fiberProdZ X X').deg
      = (((redBasics X).product (redBasics X')).map
          (fun b => (Basic.prod b.1 b.2).deg)).sum
        + ((redBasics X).product (redBasics X')).length
          * ((diagEqs p q X.r X'.r).map atomDeg).sum := by
    rw [show (fiberProdZ X X').deg
        = (((redBasics X).product (redBasics X')).map
            (fun b => (Basic.prod b.1 b.2).deg
              + ((diagEqs p q X.r X'.r).map atomDeg).sum)).sum from ?_]
    · rw [List.sum_map_add_const]
    · simp only [SemiPf.deg, fiberProdZ, List.map_map]
      apply List.sum_map_congr
      intro B _
      exact Basic.deg_appendEqs (Basic.prod B.1 B.2) (diagEqs p q X.r X'.r)
  have hlen : ((redBasics X).product (redBasics X')).length ≤ (1 + (X.deg + X'.deg)) ^ 2 := by
    rw [List.length_product_list]
    calc (redBasics X).length * (redBasics X').length
        ≤ (1 + X.deg) * (1 + X'.deg) :=
          Nat.mul_le_mul (le_trans (redBasics_length_le X) (by omega))
            (le_trans (redBasics_length_le X') (by omega))
      _ ≤ (1 + (X.deg + X'.deg)) ^ 2 := by
          have h1 : 1 + X.deg ≤ 1 + (X.deg + X'.deg) := by omega
          have h2 : 1 + X'.deg ≤ 1 + (X.deg + X'.deg) := by omega
          calc (1 + X.deg) * (1 + X'.deg)
              ≤ (1 + (X.deg + X'.deg)) * (1 + (X.deg + X'.deg)) := Nat.mul_le_mul h1 h2
            _ = (1 + (X.deg + X'.deg)) ^ 2 := by ring
  have hpF : p ≤ F := by
    have h := hX; simp only [SemiPf.fmt] at h; omega
  have hb : ∀ i : Fin p, atomDeg (diagEq p q X.r X'.r i) ≤ 2 := by
    intro i
    have h := MvPolynomial.totalDegree_sub
      (MvPolynomial.X (Sum.inl (diagIdxA p q i)) : EAPoly ((p + q) + (p + q)) (X.r + X'.r))
      (MvPolynomial.X (Sum.inl (diagIdxB p q i)) : EAPoly ((p + q) + (p + q)) (X.r + X'.r))
    rw [MvPolynomial.totalDegree_X, MvPolynomial.totalDegree_X] at h
    simp only [atomDeg, diagEq]
    omega
  have hE : ((diagEqs p q X.r X'.r).map atomDeg).sum ≤ 2 * F := by
    rw [diagEqs, List.map_map]
    calc ((List.finRange p).map (atomDeg ∘ diagEq p q X.r X'.r)).sum
        ≤ ((List.finRange p).map (fun _ => 2)).sum :=
          sum_map_le_of_pointwise _ _ _ (fun i _ => hb i)
      _ = (List.finRange p).length * 2 := sum_map_const_nat _ _
      _ = p * 2 := by rw [List.length_finRange]
      _ ≤ 2 * F := by omega
  calc (fiberProdZ X X').deg
      = (((redBasics X).product (redBasics X')).map
          (fun b => (Basic.prod b.1 b.2).deg)).sum
        + ((redBasics X).product (redBasics X')).length
          * ((diagEqs p q X.r X'.r).map atomDeg).sum := hdeg
    _ ≤ 2 * (1 + (X.deg + X'.deg)) ^ 2 + (1 + (X.deg + X'.deg)) ^ 2 * (2 * F) :=
        Nat.add_le_add hsum (Nat.mul_le_mul hlen hE)
    _ = 2 * (1 + F) * (1 + (X.deg + X'.deg)) ^ 2 := by ring

/-! ## The fibre product -/

/-- **Fibre product of restricted semi-Pfaffian sets.** Two copies of `ℝ^{p+q}` with the
first `p` coordinates glued together: the product of `X` and `X'` cut by the diagonal
equations `z_{i} = z_{p+q+i}` for `i < p`. -/
theorem fiberProduct_semiPf (F : ℕ) :
    ∃ (a : ℕ) (b : Polynomial ℕ), ∀ (p q : ℕ) (X X' : WilkiesDesign.E.SemiPf (p + q)),
      X.fmt ≤ F → X'.fmt ≤ F →
      ∃ Z : WilkiesDesign.E.SemiPf ((p + q) + (p + q)),
        Z.fmt ≤ a ∧ Z.deg ≤ b.eval (X.deg + X'.deg) ∧
        Z.set = {z : Fin ((p + q) + (p + q)) → ℝ |
          WilkiesDesign.E.projFirst (p + q) (p + q) z ∈ X.set ∧
          WilkiesDesign.E.projSnd (p + q) (p + q) z ∈ X'.set ∧
          WilkiesDesign.E.projFirst p q (WilkiesDesign.E.projFirst (p + q) (p + q) z) =
            WilkiesDesign.E.projFirst p q (WilkiesDesign.E.projSnd (p + q) (p + q) z)} := by
  refine ⟨2 * F, Polynomial.C (2 * (1 + F)) * (1 + Polynomial.X) ^ 2, ?_⟩
  intro p q X X' hX hX'
  refine ⟨fiberProdZ X X', fiberProdZ_fmt X X' hX hX', ?_, fiberProdZ_set X X'⟩
  have hev : (Polynomial.C (2 * (1 + F)) * (1 + Polynomial.X) ^ 2 : Polynomial ℕ).eval
      (X.deg + X'.deg) = 2 * (1 + F) * (1 + (X.deg + X'.deg)) ^ 2 := by simp
  rw [hev]
  exact fiberProdZ_deg X X' hX

end Work.WilE7
