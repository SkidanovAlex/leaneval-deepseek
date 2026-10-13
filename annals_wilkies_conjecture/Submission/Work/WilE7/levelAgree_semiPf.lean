import Mathlib
import Submission.Work.WilE7.fiberProduct_semiPf
import Submission.Work.WilE7.FaceAux.InsertCoord

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilE7
open WilkiesConjecture WilkiesDesign WilkiesDesign.E

/-! ## Gluing the *last* coordinate of the two blocks

`fiberProduct_semiPf` glues the *first* `p` coordinates of the two copies of `ℝ^{p+q}`.
Here we additionally want to glue the last coordinate — index `M` of the second block, when the
block size is `q = M+1`.  This is one extra diagonal equation `z_A = z_B` on top of the fibre
product; we build the whole restricted semi-Pfaffian set `levelGlue` directly (rather than via
`FaceAux.addEq`) so that all the basic sets carry the *correct* chain size syntactically. -/

/-- The index of the glued coordinate inside the *first* block of the fibre product. -/
def glueIdxA (n M : ℕ) : Fin ((n + (M + 1)) + (n + (M + 1))) :=
  Fin.castAdd (n + (M + 1)) (Fin.natAdd n ⟨M, by omega⟩)

/-- The index of the glued coordinate inside the *second* block of the fibre product. -/
def glueIdxB (n M : ℕ) : Fin ((n + (M + 1)) + (n + (M + 1))) :=
  Fin.natAdd (n + (M + 1)) (Fin.natAdd n ⟨M, by omega⟩)

/-- The diagonal equation `z_A - z_B = 0` gluing the last coordinate of the two blocks. -/
def glueEq (n M r r' : ℕ) : EAPoly ((n + (M + 1)) + (n + (M + 1))) (r + r') :=
  MvPolynomial.X (Sum.inl (glueIdxA n M)) - MvPolynomial.X (Sum.inl (glueIdxB n M))

/-- Evaluation of the gluing equation. -/
theorem eaEval_glueEq {n M r r' : ℕ} (c : EAChain ((n + (M + 1)) + (n + (M + 1))) (r + r'))
    (z : Fin ((n + (M + 1)) + (n + (M + 1))) → ℝ) :
    eaEval c (glueEq n M r r') z = z (glueIdxA n M) - z (glueIdxB n M) := by
  simp [glueEq, eaEval]

/-- `z (glueIdxA n M)` is the last coordinate of the second block of the first copy. -/
theorem glueIdxA_apply (n M : ℕ) (z : Fin ((n + (M + 1)) + (n + (M + 1))) → ℝ) :
    z (glueIdxA n M) =
      (projSnd n (M + 1) (projFirst (n + (M + 1)) (n + (M + 1)) z)) ⟨M, by omega⟩ := rfl

/-- `z (glueIdxB n M)` is the last coordinate of the second block of the second copy. -/
theorem glueIdxB_apply (n M : ℕ) (z : Fin ((n + (M + 1)) + (n + (M + 1))) → ℝ) :
    z (glueIdxB n M) =
      (projSnd n (M + 1) (projSnd (n + (M + 1)) (n + (M + 1)) z)) ⟨M, by omega⟩ := rfl

/-- The gluing equation vanishes exactly when the two last coordinates agree. -/
theorem glueEq_zero_iff {n M r r' : ℕ} (c : EAChain ((n + (M + 1)) + (n + (M + 1))) (r + r'))
    (z : Fin ((n + (M + 1)) + (n + (M + 1))) → ℝ) :
    eaEval c (glueEq n M r r') z = 0 ↔
      (projSnd n (M + 1) (projFirst (n + (M + 1)) (n + (M + 1)) z)) ⟨M, by omega⟩ =
        (projSnd n (M + 1) (projSnd (n + (M + 1)) (n + (M + 1)) z)) ⟨M, by omega⟩ := by
  rw [eaEval_glueEq, sub_eq_zero]
  constructor
  · intro h
    rwa [glueIdxA_apply n M z, glueIdxB_apply n M z] at h
  · intro h
    rwa [glueIdxA_apply n M z, glueIdxB_apply n M z]

/-- The gluing equation has atom degree at most `2`. -/
theorem atomDeg_glueEq (n M r r' : ℕ) : atomDeg (glueEq n M r r') ≤ 2 := by
  have h := MvPolynomial.totalDegree_sub
    (MvPolynomial.X (Sum.inl (glueIdxA n M)) : EAPoly ((n + (M + 1)) + (n + (M + 1))) (r + r'))
    (MvPolynomial.X (Sum.inl (glueIdxB n M)) : EAPoly ((n + (M + 1)) + (n + (M + 1))) (r + r'))
  rw [MvPolynomial.totalDegree_X, MvPolynomial.totalDegree_X] at h
  rw [glueEq]
  simp only [atomDeg]
  omega

/-! ## The construction -/

/-- **The level-agreeing fibre product**: the product of `P` and `P'` cut by the diagonal
equations `z_{A i} = z_{B i}` for the first `n` coordinates *and* the gluing of the last
coordinate (index `M` of the second block). -/
def levelGlue {n M : ℕ} (P P' : SemiPf (n + (M + 1))) :
    SemiPf ((n + (M + 1)) + (n + (M + 1))) where
  r := P.r + P'.r
  c := EAChain.prod P.c P'.c
  basics := ((redBasics P).product (redBasics P')).map (fun b =>
    (⟨(Basic.prod b.1 b.2).eqs ++ (diagEqs n (M + 1) P.r P'.r ++ [glueEq n M P.r P'.r]),
      (Basic.prod b.1 b.2).pos⟩ : Basic ((n + (M + 1)) + (n + (M + 1))) (P.r + P'.r)))

/-- The point set of the level-agreeing fibre product. -/
theorem levelGlue_set {n M : ℕ} (P P' : SemiPf (n + (M + 1))) :
    (levelGlue P P').set =
      {z : Fin ((n + (M + 1)) + (n + (M + 1))) → ℝ |
        projFirst (n + (M + 1)) (n + (M + 1)) z ∈ P.set ∧
        projSnd (n + (M + 1)) (n + (M + 1)) z ∈ P'.set ∧
        projFirst n (M + 1) (projFirst (n + (M + 1)) (n + (M + 1)) z) =
          projFirst n (M + 1) (projSnd (n + (M + 1)) (n + (M + 1)) z) ∧
        (projSnd n (M + 1) (projFirst (n + (M + 1)) (n + (M + 1)) z)) ⟨M, by omega⟩ =
          (projSnd n (M + 1) (projSnd (n + (M + 1)) (n + (M + 1)) z)) ⟨M, by omega⟩} := by
  ext z
  change (z ∈ cubeC ((n + (M + 1)) + (n + (M + 1))) ∧
      ∃ B ∈ ((redBasics P).product (redBasics P')).map
        (fun b => (⟨(Basic.prod b.1 b.2).eqs
            ++ (diagEqs n (M + 1) P.r P'.r ++ [glueEq n M P.r P'.r]),
          (Basic.prod b.1 b.2).pos⟩ :
            Basic ((n + (M + 1)) + (n + (M + 1))) (P.r + P'.r))),
      B.holds (EAChain.prod P.c P'.c) z) ↔
    ((projFirst (n + (M + 1)) (n + (M + 1)) z ∈ cubeC (n + (M + 1)) ∧
        ∃ B ∈ P.basics, B.holds P.c (projFirst (n + (M + 1)) (n + (M + 1)) z)) ∧
      (projSnd (n + (M + 1)) (n + (M + 1)) z ∈ cubeC (n + (M + 1)) ∧
        ∃ B ∈ P'.basics, B.holds P'.c (projSnd (n + (M + 1)) (n + (M + 1)) z)) ∧
      projFirst n (M + 1) (projFirst (n + (M + 1)) (n + (M + 1)) z) =
        projFirst n (M + 1) (projSnd (n + (M + 1)) (n + (M + 1)) z) ∧
      (projSnd n (M + 1) (projFirst (n + (M + 1)) (n + (M + 1)) z)) ⟨M, by omega⟩ =
        (projSnd n (M + 1) (projSnd (n + (M + 1)) (n + (M + 1)) z)) ⟨M, by omega⟩)
  have hkey : (∃ B ∈ ((redBasics P).product (redBasics P')).map
        (fun b => (⟨(Basic.prod b.1 b.2).eqs
            ++ (diagEqs n (M + 1) P.r P'.r ++ [glueEq n M P.r P'.r]),
          (Basic.prod b.1 b.2).pos⟩ :
            Basic ((n + (M + 1)) + (n + (M + 1))) (P.r + P'.r))),
        B.holds (EAChain.prod P.c P'.c) z) ↔
      (∃ B ∈ redBasics P, B.holds P.c (projFirst (n + (M + 1)) (n + (M + 1)) z)) ∧
      (∃ B ∈ redBasics P', B.holds P'.c (projSnd (n + (M + 1)) (n + (M + 1)) z)) ∧
      (∀ f ∈ diagEqs n (M + 1) P.r P'.r, eaEval (EAChain.prod P.c P'.c) f z = 0) ∧
      eaEval (EAChain.prod P.c P'.c) (glueEq n M P.r P'.r) z = 0 := by
    rw [exists_mem_product_map]
    constructor
    · rintro ⟨a, ha, b, hb, hh⟩
      have hh2 : (⟨(Basic.prod a b).eqs
          ++ (diagEqs n (M + 1) P.r P'.r ++ [glueEq n M P.r P'.r]),
          (Basic.prod a b).pos⟩ :
            Basic ((n + (M + 1)) + (n + (M + 1))) (P.r + P'.r)).holds
          (EAChain.prod P.c P'.c) z := hh
      obtain ⟨hh', hd⟩ := (Basic.holds_appendEqs (EAChain.prod P.c P'.c) (Basic.prod a b)
        (diagEqs n (M + 1) P.r P'.r ++ [glueEq n M P.r P'.r]) z).mp hh2
      obtain ⟨hd1, hd2⟩ := List.forall_mem_append.mp hd
      obtain ⟨h1, h2⟩ := (Basic.holds_prod P.c P'.c a b z).mp hh'
      exact ⟨⟨a, ha, h1⟩, ⟨b, hb, h2⟩, hd1,
        hd2 (glueEq n M P.r P'.r) (List.mem_singleton_self _)⟩
    · rintro ⟨⟨a, ha, h1⟩, ⟨b, hb, h2⟩, hd1, hd2⟩
      refine ⟨a, ha, b, hb, ?_⟩
      exact (Basic.holds_appendEqs (EAChain.prod P.c P'.c) (Basic.prod a b)
        (diagEqs n (M + 1) P.r P'.r ++ [glueEq n M P.r P'.r]) z).mpr
        ⟨(Basic.holds_prod P.c P'.c a b z).mpr ⟨h1, h2⟩,
          List.forall_mem_append.mpr
            ⟨hd1, fun x hx => by rw [List.mem_singleton] at hx; rw [hx]; exact hd2⟩⟩
  rw [hkey, cubeC_add z,
    exists_holds_redBasics P (projFirst (n + (M + 1)) (n + (M + 1)) z),
    exists_holds_redBasics P' (projSnd (n + (M + 1)) (n + (M + 1)) z),
    diagEqs_forall (p := n) (q := M + 1) (r := P.r) (r' := P'.r) (EAChain.prod P.c P'.c) z,
    glueEq_zero_iff (c := EAChain.prod P.c P'.c) z]
  tauto

/-- The format of the level-agreeing fibre product. -/
theorem levelGlue_fmt {n M F : ℕ} (P P' : SemiPf (n + (M + 1)))
    (hP : P.fmt ≤ F) (hP' : P'.fmt ≤ F) : (levelGlue P P').fmt ≤ 2 * F := by
  simp only [SemiPf.fmt, levelGlue] at hP hP' ⊢
  omega

/-- The degree of the level-agreeing fibre product, with the glued equation accounted for. -/
theorem levelGlue_deg_le {n M : ℕ} (P P' : SemiPf (n + (M + 1))) :
    (levelGlue P P').deg ≤
      (((redBasics P).product (redBasics P')).map
          (fun b => (Basic.prod b.1 b.2).deg)).sum
        + ((redBasics P).product (redBasics P')).length
          * (((diagEqs n (M + 1) P.r P'.r).map atomDeg).sum
              + atomDeg (glueEq n M P.r P'.r)) := by
  have hS : (((diagEqs n (M + 1) P.r P'.r ++ [glueEq n M P.r P'.r]).map atomDeg)).sum
      = ((diagEqs n (M + 1) P.r P'.r).map atomDeg).sum + atomDeg (glueEq n M P.r P'.r) := by
    rw [List.map_append, List.sum_append, List.map_singleton, List.sum_singleton]
  have hdeg : (levelGlue P P').deg
      = (((redBasics P).product (redBasics P')).map
          (fun b => (Basic.prod b.1 b.2).deg
            + ((diagEqs n (M + 1) P.r P'.r ++ [glueEq n M P.r P'.r]).map atomDeg).sum)).sum := by
    simp only [SemiPf.deg, levelGlue, List.map_map]
    apply List.sum_map_congr
    intro B _
    exact Basic.deg_appendEqs (Basic.prod B.1 B.2)
      (diagEqs n (M + 1) P.r P'.r ++ [glueEq n M P.r P'.r])
  rw [hdeg, List.sum_map_add_const, hS]

/-- The degree bound for the level-agreeing fibre product. -/
theorem levelGlue_deg {n M F : ℕ} (P P' : SemiPf (n + (M + 1))) (hP : P.fmt ≤ F) :
    (levelGlue P P').deg ≤ 2 * (F + 2) * (1 + (P.deg + P'.deg)) ^ 2 := by
  have hsum : (((redBasics P).product (redBasics P')).map
      (fun b => (Basic.prod b.1 b.2).deg)).sum ≤ 2 * (1 + (P.deg + P'.deg)) ^ 2 := by
    have h1 : (((redBasics P).product (redBasics P')).map
        (fun b => (Basic.prod b.1 b.2).deg)).sum
        ≤ (((redBasics P).product (redBasics P')).map
            (fun b => b.1.deg + b.2.deg)).sum :=
      sum_map_le_of_pointwise _ _ _ (fun b _ => Basic.prod_deg_le b.1 b.2)
    rw [sumProduct] at h1
    exact le_trans h1 (deg_bound_arith P.deg P'.deg (redBasics P).length (redBasics P').length
      ((redBasics P).map Basic.deg).sum ((redBasics P').map Basic.deg).sum
      (redBasics_length_le P) (redBasics_length_le P')
      (redBasics_deg_le P) (redBasics_deg_le P'))
  have hlen : ((redBasics P).product (redBasics P')).length
      ≤ (1 + (P.deg + P'.deg)) ^ 2 := by
    rw [Work.WilE7.List.length_product_list]
    have hX : (redBasics P).length ≤ 1 + P.deg := by
      have := redBasics_length_le P; omega
    have hX' : (redBasics P').length ≤ 1 + P'.deg := by
      have := redBasics_length_le P'; omega
    calc (redBasics P).length * (redBasics P').length
        ≤ (1 + P.deg) * (1 + P'.deg) := Nat.mul_le_mul hX hX'
      _ ≤ (1 + (P.deg + P'.deg)) ^ 2 := by
          have e1 : 1 + P.deg ≤ 1 + (P.deg + P'.deg) := by omega
          have e2 : 1 + P'.deg ≤ 1 + (P.deg + P'.deg) := by omega
          calc (1 + P.deg) * (1 + P'.deg)
              ≤ (1 + (P.deg + P'.deg)) * (1 + (P.deg + P'.deg)) := Nat.mul_le_mul e1 e2
            _ = (1 + (P.deg + P'.deg)) ^ 2 := by ring
  have hpF : n ≤ F := by
    have h := hP; simp only [SemiPf.fmt] at h; omega
  have hb : ∀ i : Fin n, atomDeg (diagEq n (M + 1) P.r P'.r i) ≤ 2 := by
    intro i
    have h := MvPolynomial.totalDegree_sub
      (MvPolynomial.X (Sum.inl (diagIdxA n (M + 1) i)) :
        EAPoly ((n + (M + 1)) + (n + (M + 1))) (P.r + P'.r))
      (MvPolynomial.X (Sum.inl (diagIdxB n (M + 1) i)) :
        EAPoly ((n + (M + 1)) + (n + (M + 1))) (P.r + P'.r))
    rw [MvPolynomial.totalDegree_X, MvPolynomial.totalDegree_X] at h
    simp only [atomDeg, diagEq]
    omega
  have hE : ((diagEqs n (M + 1) P.r P'.r).map atomDeg).sum ≤ 2 * F := by
    rw [diagEqs, List.map_map]
    calc ((List.finRange n).map (atomDeg ∘ diagEq n (M + 1) P.r P'.r)).sum
        ≤ ((List.finRange n).map (fun _ => 2)).sum :=
          sum_map_le_of_pointwise _ _ _ (fun i _ => hb i)
      _ = (List.finRange n).length * 2 := sum_map_const_nat _ _
      _ = n * 2 := by rw [List.length_finRange]
      _ ≤ 2 * F := by omega
  have hglue : atomDeg (glueEq n M P.r P'.r) ≤ 2 := atomDeg_glueEq n M P.r P'.r
  have hd := levelGlue_deg_le P P'
  calc (levelGlue P P').deg
      ≤ (((redBasics P).product (redBasics P')).map
          (fun b => (Basic.prod b.1 b.2).deg)).sum
        + ((redBasics P).product (redBasics P')).length
          * (((diagEqs n (M + 1) P.r P'.r).map atomDeg).sum
              + atomDeg (glueEq n M P.r P'.r)) := hd
    _ ≤ 2 * (1 + (P.deg + P'.deg)) ^ 2
        + (1 + (P.deg + P'.deg)) ^ 2 * (2 * F + 2) :=
        Nat.add_le_add hsum (Nat.mul_le_mul hlen (Nat.add_le_add hE hglue))
    _ = 2 * (F + 2) * (1 + (P.deg + P'.deg)) ^ 2 := by ring

/-! ## Auxiliary degree counting (kept for reuse) -/

/-- Adjoining an equation to every basic set increases the degree by the atom degree of the
equation, once per basic set. -/
theorem addEq_deg_le {k : ℕ} (X : SemiPf k) (Q : EAPoly k X.r) :
    (Work.WilE7.FaceAux.addEq X Q).deg ≤ X.deg + X.basics.length * atomDeg Q := by
  simp only [SemiPf.deg, Work.WilE7.FaceAux.addEq]
  rw [List.map_map]
  have hcongr : (X.basics.map (Basic.deg ∘ fun B => (⟨B.eqs ++ [Q], B.pos⟩ : Basic k X.r)))
      = X.basics.map (fun B => B.deg + atomDeg Q) := by
    apply List.map_congr_left
    intro B _
    simp only [Function.comp_apply]
    rw [Work.WilE7.Basic.deg_appendEqs, List.map_singleton, List.sum_singleton]
  rw [hcongr, List.sum_map_add_const]

/-- The number of basic sets of the fibre product. -/
theorem fiberProdZ_basics_length_le {p q : ℕ} (X X' : SemiPf (p + q)) :
    (fiberProdZ X X').basics.length ≤ (1 + (X.deg + X'.deg)) ^ 2 := by
  have hX : (redBasics X).length ≤ 1 + X.deg := by
    have := redBasics_length_le X; omega
  have hX' : (redBasics X').length ≤ 1 + X'.deg := by
    have := redBasics_length_le X'; omega
  have hlen : (fiberProdZ X X').basics.length
      = (redBasics X).length * (redBasics X').length := by
    simp only [fiberProdZ]
    rw [List.length_map, Work.WilE7.List.length_product_list]
  rw [hlen]
  calc (redBasics X).length * (redBasics X').length
      ≤ (1 + X.deg) * (1 + X'.deg) := Nat.mul_le_mul hX hX'
    _ ≤ (1 + (X.deg + X'.deg)) ^ 2 := by
        have e1 : 1 + X.deg ≤ 1 + (X.deg + X'.deg) := by omega
        have e2 : 1 + X'.deg ≤ 1 + (X.deg + X'.deg) := by omega
        calc (1 + X.deg) * (1 + X'.deg)
            ≤ (1 + (X.deg + X'.deg)) * (1 + (X.deg + X'.deg)) := Nat.mul_le_mul e1 e2
          _ = (1 + (X.deg + X'.deg)) ^ 2 := by ring

/-! ## The main theorem -/

theorem levelAgree_semiPf (F : ℕ) :
    ∃ (A : ℕ) (Cb : Polynomial ℕ), ∀ (n M : ℕ) (P P' : WilkiesDesign.E.SemiPf (n + (M + 1))),
      P.fmt ≤ F → P'.fmt ≤ F →
      ∃ W : WilkiesDesign.E.SemiPf ((n + (M + 1)) + (n + (M + 1))),
        W.fmt ≤ A ∧ W.deg ≤ Cb.eval (P.deg + P'.deg) ∧
        W.set = {z : Fin ((n + (M + 1)) + (n + (M + 1))) → ℝ |
          WilkiesDesign.E.projFirst (n + (M + 1)) (n + (M + 1)) z ∈ P.set ∧
          WilkiesDesign.E.projSnd (n + (M + 1)) (n + (M + 1)) z ∈ P'.set ∧
          WilkiesDesign.E.projFirst n (M + 1)
            (WilkiesDesign.E.projFirst (n + (M + 1)) (n + (M + 1)) z) =
          WilkiesDesign.E.projFirst n (M + 1)
            (WilkiesDesign.E.projSnd (n + (M + 1)) (n + (M + 1)) z) ∧
          (WilkiesDesign.E.projSnd n (M + 1)
            (WilkiesDesign.E.projFirst (n + (M + 1)) (n + (M + 1)) z)) ⟨M, by omega⟩ =
          (WilkiesDesign.E.projSnd n (M + 1)
            (WilkiesDesign.E.projSnd (n + (M + 1)) (n + (M + 1)) z)) ⟨M, by omega⟩} := by
  refine ⟨2 * F, Polynomial.C (2 * (F + 2)) * (1 + Polynomial.X) ^ 2, ?_⟩
  intro n M P P' hP hP'
  refine ⟨levelGlue P P', levelGlue_fmt P P' hP hP', ?_, levelGlue_set P P'⟩
  rw [show (Polynomial.C (2 * (F + 2)) * (1 + Polynomial.X) ^ 2 : Polynomial ℕ).eval
      (P.deg + P'.deg) = 2 * (F + 2) * (1 + (P.deg + P'.deg)) ^ 2 from by simp]
  exact levelGlue_deg P P' hP

end Work.WilE7
