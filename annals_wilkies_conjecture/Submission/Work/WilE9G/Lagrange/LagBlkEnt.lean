import Submission.Work.WilE9G.Lagrange.LagBlkAux

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilE9G.Lagrange.LagBlk
open WilkiesDesign WilkiesDesign.E Work.WilE9G Work.WilE9G.Lagrange

/-! ## the nine entry computations -/

theorem pEntLyt {n m : ℕ} (S : AmbStratum (n + (1 + m)))
    (Phi : EAPoly (n + (1 + m)) S.X.r) (c : Fin (1 + m) → ℝ)
    (z : Fin (n + (1 + m)) → ℝ) (mu : Fin S.j → ℝ) (mu0 : ℝ)
    (a l : Fin (1 + (m + S.j + 1))) (ha : a.val < 1 + m) (hl : l.val < 1 + m) :
    eaEval (lagChain S) (eaD (lagChain S) (Fin.natAdd n l) (lagEqs S Phi c a))
        (lagPoint z mu mu0)
      = mu0 * (eaEval S.X.c (eaD S.X.c (Fin.natAdd n ⟨l.val, hl⟩)
                  (eaD S.X.c (Fin.natAdd n ⟨a.val, ha⟩) Phi)) z
              + eaEval S.X.c (eaD S.X.c (Fin.natAdd n ⟨l.val, hl⟩) Phi) z * c ⟨a.val, ha⟩)
        - ∑ a' : Fin S.j, mu a' * eaEval S.X.c
            (eaD S.X.c (Fin.natAdd n ⟨l.val, hl⟩)
              (eaD S.X.c (Fin.natAdd n ⟨a.val, ha⟩) (S.h a'))) z := by
  rw [pLagEqs_lt S Phi c a ha, pLagNatAdd_castLE S l hl]
  simp only [lagL, lagChain, pEaD_sub, pEaD_add, pEaD_mul, pEaD_C, pEaD_sum,
    Work.WilE9G.Lagrange.eaD_pad, pEaD_mu0Var_castLE, pEaD_muVar_castLE,
    zero_mul, mul_zero, zero_add, add_zero]
  simp only [lagEval_add, lagEval_sub, lagEval_mul, lagEval_sum, lagEval_one, lagEval_C,
    pEval_pad, pEval_muVar, pEval_mu0Var, pEval_neg, pEval_zero]
  ring

theorem pEntLmu {n m : ℕ} (S : AmbStratum (n + (1 + m)))
    (Phi : EAPoly (n + (1 + m)) S.X.r) (c : Fin (1 + m) → ℝ)
    (z : Fin (n + (1 + m)) → ℝ) (mu : Fin S.j → ℝ) (mu0 : ℝ)
    (a l : Fin (1 + (m + S.j + 1))) (ha : a.val < 1 + m)
    (h1 : 1 + m ≤ l.val) (h2 : l.val < 1 + m + S.j) :
    eaEval (lagChain S) (eaD (lagChain S) (Fin.natAdd n l) (lagEqs S Phi c a))
        (lagPoint z mu mu0)
      = - eaEval S.X.c
          (eaD S.X.c (Fin.natAdd n ⟨a.val, ha⟩) (S.h ⟨l.val - (1 + m), by omega⟩)) z := by
  rw [pLagEqs_lt S Phi c a ha, pLagNatAdd_muIdx S l h1 h2]
  simp only [lagL, lagChain, pEaD_sub, pEaD_add, pEaD_mul, pEaD_C, pEaD_sum,
    pEaD_padZero_muIdx, pEaD_mu0Var_muIdx, pEaD_muVar_muIdx, pSum_ite_one_mul,
    zero_mul, mul_zero, zero_add, add_zero, sub_zero]
  simp only [lagEval_add, lagEval_sub, lagEval_mul, lagEval_sum, lagEval_one, lagEval_C,
    pEval_pad, pEval_muVar, pEval_mu0Var, pEval_neg, pEval_zero]
  ring

theorem pEntLmu0 {n m : ℕ} (S : AmbStratum (n + (1 + m)))
    (Phi : EAPoly (n + (1 + m)) S.X.r) (c : Fin (1 + m) → ℝ)
    (z : Fin (n + (1 + m)) → ℝ) (mu : Fin S.j → ℝ) (mu0 : ℝ)
    (a l : Fin (1 + (m + S.j + 1))) (ha : a.val < 1 + m) (h : l.val = 1 + m + S.j) :
    eaEval (lagChain S) (eaD (lagChain S) (Fin.natAdd n l) (lagEqs S Phi c a))
        (lagPoint z mu mu0)
      = eaEval S.X.c (eaD S.X.c (Fin.natAdd n ⟨a.val, ha⟩) Phi) z
        + eaEval S.X.c Phi z * c ⟨a.val, ha⟩ := by
  rw [pLagEqs_lt S Phi c a ha, pLagNatAdd_mu0Idx S l h]
  simp only [lagL, lagChain, pEaD_sub, pEaD_add, pEaD_mul, pEaD_C, pEaD_sum,
    pEaD_padZero_mu0, pEaD_mu0Var_self, pEaD_muVar_mu0, Finset.sum_const_zero,
    zero_mul, mul_zero, one_mul, zero_add, add_zero, sub_zero]
  simp only [lagEval_add, lagEval_sub, lagEval_mul, lagEval_sum, lagEval_one, lagEval_C,
    pEval_pad, pEval_muVar, pEval_mu0Var, pEval_neg, pEval_zero]
  ring

theorem pEntHyt {n m : ℕ} (S : AmbStratum (n + (1 + m)))
    (Phi : EAPoly (n + (1 + m)) S.X.r) (c : Fin (1 + m) → ℝ)
    (z : Fin (n + (1 + m)) → ℝ) (mu : Fin S.j → ℝ) (mu0 : ℝ)
    (a l : Fin (1 + (m + S.j + 1)))
    (ha : 1 + m ≤ a.val) (ha2 : a.val < 1 + m + S.j) (hl : l.val < 1 + m) :
    eaEval (lagChain S) (eaD (lagChain S) (Fin.natAdd n l) (lagEqs S Phi c a))
        (lagPoint z mu mu0)
      = eaEval S.X.c
          (eaD S.X.c (Fin.natAdd n ⟨l.val, hl⟩) (S.h ⟨a.val - (1 + m), by omega⟩)) z := by
  rw [pLagEqs_mid S Phi c a ha ha2, pLagNatAdd_castLE S l hl]
  simp only [lagH, lagChain, Work.WilE9G.Lagrange.eaD_pad]
  simp only [lagEval_add, lagEval_sub, lagEval_mul, lagEval_sum, lagEval_one, lagEval_C,
    pEval_pad, pEval_muVar, pEval_mu0Var, pEval_neg, pEval_zero]

theorem pEntHmu {n m : ℕ} (S : AmbStratum (n + (1 + m)))
    (Phi : EAPoly (n + (1 + m)) S.X.r) (c : Fin (1 + m) → ℝ)
    (z : Fin (n + (1 + m)) → ℝ) (mu : Fin S.j → ℝ) (mu0 : ℝ)
    (a l : Fin (1 + (m + S.j + 1)))
    (ha : 1 + m ≤ a.val) (ha2 : a.val < 1 + m + S.j)
    (h1 : 1 + m ≤ l.val) (h2 : l.val < 1 + m + S.j) :
    eaEval (lagChain S) (eaD (lagChain S) (Fin.natAdd n l) (lagEqs S Phi c a))
        (lagPoint z mu mu0) = 0 := by
  rw [pLagEqs_mid S Phi c a ha ha2, pLagNatAdd_muIdx S l h1 h2]
  simp only [lagH, lagChain, pEaD_padZero_muIdx, pEval_zero]

theorem pEntHmu0 {n m : ℕ} (S : AmbStratum (n + (1 + m)))
    (Phi : EAPoly (n + (1 + m)) S.X.r) (c : Fin (1 + m) → ℝ)
    (z : Fin (n + (1 + m)) → ℝ) (mu : Fin S.j → ℝ) (mu0 : ℝ)
    (a l : Fin (1 + (m + S.j + 1)))
    (ha : 1 + m ≤ a.val) (ha2 : a.val < 1 + m + S.j) (h : l.val = 1 + m + S.j) :
    eaEval (lagChain S) (eaD (lagChain S) (Fin.natAdd n l) (lagEqs S Phi c a))
        (lagPoint z mu mu0) = 0 := by
  rw [pLagEqs_mid S Phi c a ha ha2, pLagNatAdd_mu0Idx S l h]
  simp only [lagH, lagChain, pEaD_padZero_mu0, pEval_zero]

theorem pEntNyt {n m : ℕ} (S : AmbStratum (n + (1 + m)))
    (Phi : EAPoly (n + (1 + m)) S.X.r) (c : Fin (1 + m) → ℝ)
    (z : Fin (n + (1 + m)) → ℝ) (mu : Fin S.j → ℝ) (mu0 : ℝ)
    (a l : Fin (1 + (m + S.j + 1))) (ha : a.val = 1 + m + S.j) (hl : l.val < 1 + m) :
    eaEval (lagChain S) (eaD (lagChain S) (Fin.natAdd n l) (lagEqs S Phi c a))
        (lagPoint z mu mu0) = 0 := by
  rw [pLagEqs_last S Phi c a ha, pLagNatAdd_castLE S l hl]
  simp only [lagN, lagChain, pEaD_sub, pEaD_add, pEaD_mul, pEaD_sq, pEaD_one, pEaD_sum,
    pEaD_mu0Var_castLE, pEaD_muVar_castLE, Finset.sum_const_zero,
    zero_mul, mul_zero, zero_add, add_zero, sub_zero]
  simp only [pEval_zero]

theorem pEntNmu {n m : ℕ} (S : AmbStratum (n + (1 + m)))
    (Phi : EAPoly (n + (1 + m)) S.X.r) (c : Fin (1 + m) → ℝ)
    (z : Fin (n + (1 + m)) → ℝ) (mu : Fin S.j → ℝ) (mu0 : ℝ)
    (a l : Fin (1 + (m + S.j + 1))) (ha : a.val = 1 + m + S.j)
    (h1 : 1 + m ≤ l.val) (h2 : l.val < 1 + m + S.j) :
    eaEval (lagChain S) (eaD (lagChain S) (Fin.natAdd n l) (lagEqs S Phi c a))
        (lagPoint z mu mu0) = 2 * mu ⟨l.val - (1 + m), by omega⟩ := by
  rw [pLagEqs_last S Phi c a ha, pLagNatAdd_muIdx S l h1 h2]
  simp only [lagN, lagChain, pEaD_sub, pEaD_add, pEaD_mul, pEaD_sq, pEaD_one, pEaD_sum,
    pEaD_mu0Var_muIdx, pEaD_muVar_muIdx, Finset.sum_add_distrib, pSum_ite_one_mul, pSum_mul_ite_one,
    zero_mul, mul_zero, zero_add, add_zero, sub_zero]
  simp only [lagEval_add, lagEval_sub, lagEval_mul, lagEval_sum, lagEval_one, lagEval_C,
    pEval_muVar, pEval_mu0Var, pEval_zero, pEval_neg]
  ring

theorem pEntNmu0 {n m : ℕ} (S : AmbStratum (n + (1 + m)))
    (Phi : EAPoly (n + (1 + m)) S.X.r) (c : Fin (1 + m) → ℝ)
    (z : Fin (n + (1 + m)) → ℝ) (mu : Fin S.j → ℝ) (mu0 : ℝ)
    (a l : Fin (1 + (m + S.j + 1))) (ha : a.val = 1 + m + S.j) (h : l.val = 1 + m + S.j) :
    eaEval (lagChain S) (eaD (lagChain S) (Fin.natAdd n l) (lagEqs S Phi c a))
        (lagPoint z mu mu0) = 2 * mu0 := by
  rw [pLagEqs_last S Phi c a ha, pLagNatAdd_mu0Idx S l h]
  simp only [lagN, lagChain, pEaD_sub, pEaD_add, pEaD_mul, pEaD_sq, pEaD_one, pEaD_sum,
    pEaD_mu0Var_self, pEaD_muVar_mu0, Finset.sum_const_zero,
    zero_mul, mul_zero, one_mul, zero_add, add_zero, sub_zero]
  simp only [lagEval_add, lagEval_sub, lagEval_mul, lagEval_sum, lagEval_one, lagEval_C,
    pEval_muVar, pEval_mu0Var, pEval_zero, pEval_neg]
  ring

/-! ## the nine entries of `lagJacTrue`, in the same explicit form -/

theorem pJac_Lyt {n m : ℕ} (S : AmbStratum (n + (1 + m)))
    (Phi : EAPoly (n + (1 + m)) S.X.r) (c : Fin (1 + m) → ℝ)
    (z : Fin (n + (1 + m)) → ℝ) (mu : Fin S.j → ℝ) (mu0 : ℝ)
    (a l : Fin (1 + (m + S.j + 1))) (ha : a.val < 1 + m) (hl : l.val < 1 + m) :
    lagJacTrue S Phi c z mu mu0 (lagEquiv m S.j a) (lagEquiv m S.j l)
      = mu0 * (eaEval S.X.c (eaD S.X.c (Fin.natAdd n ⟨l.val, hl⟩)
                  (eaD S.X.c (Fin.natAdd n ⟨a.val, ha⟩) Phi)) z
              + eaEval S.X.c (eaD S.X.c (Fin.natAdd n ⟨l.val, hl⟩) Phi) z * c ⟨a.val, ha⟩)
        - ∑ a' : Fin S.j, mu a' * eaEval S.X.c
            (eaD S.X.c (Fin.natAdd n ⟨l.val, hl⟩)
              (eaD S.X.c (Fin.natAdd n ⟨a.val, ha⟩) (S.h a'))) z := by
  rw [lagJacTrue]
  simp only [Matrix.of_apply]
  rw [show lagEquiv m S.j l = Fin.castAdd (S.j + 1) (⟨l.val, hl⟩ : Fin (1 + m))
      from Fin.ext (by simp), Fin.addCases_left]
  rw [show lagEquiv m S.j a = Fin.castAdd (S.j + 1) (⟨a.val, ha⟩ : Fin (1 + m))
      from Fin.ext (by simp), Fin.addCases_left]

theorem pJac_Lmu {n m : ℕ} (S : AmbStratum (n + (1 + m)))
    (Phi : EAPoly (n + (1 + m)) S.X.r) (c : Fin (1 + m) → ℝ)
    (z : Fin (n + (1 + m)) → ℝ) (mu : Fin S.j → ℝ) (mu0 : ℝ)
    (a l : Fin (1 + (m + S.j + 1))) (ha : a.val < 1 + m)
    (h1 : 1 + m ≤ l.val) (h2 : l.val < 1 + m + S.j) :
    lagJacTrue S Phi c z mu mu0 (lagEquiv m S.j a) (lagEquiv m S.j l)
      = - eaEval S.X.c
          (eaD S.X.c (Fin.natAdd n ⟨a.val, ha⟩) (S.h ⟨l.val - (1 + m), by omega⟩)) z := by
  rw [lagJacTrue]
  simp only [Matrix.of_apply]
  rw [show lagEquiv m S.j l
        = Fin.natAdd (1 + m) (Fin.castAdd 1 (⟨l.val - (1 + m), by omega⟩ : Fin S.j))
      from Fin.ext (by
        simp only [lagEquiv_apply_val, Fin.val_natAdd, Fin.val_castAdd]; omega),
    Fin.addCases_right, Fin.addCases_left]
  rw [show lagEquiv m S.j a = Fin.castAdd (S.j + 1) (⟨a.val, ha⟩ : Fin (1 + m))
      from Fin.ext (by simp), Fin.addCases_left]

theorem pJac_Lmu0 {n m : ℕ} (S : AmbStratum (n + (1 + m)))
    (Phi : EAPoly (n + (1 + m)) S.X.r) (c : Fin (1 + m) → ℝ)
    (z : Fin (n + (1 + m)) → ℝ) (mu : Fin S.j → ℝ) (mu0 : ℝ)
    (a l : Fin (1 + (m + S.j + 1))) (ha : a.val < 1 + m) (h : l.val = 1 + m + S.j) :
    lagJacTrue S Phi c z mu mu0 (lagEquiv m S.j a) (lagEquiv m S.j l)
      = eaEval S.X.c (eaD S.X.c (Fin.natAdd n ⟨a.val, ha⟩) Phi) z
        + eaEval S.X.c Phi z * c ⟨a.val, ha⟩ := by
  rw [lagJacTrue]
  simp only [Matrix.of_apply]
  rw [show lagEquiv m S.j l = Fin.natAdd (1 + m) (Fin.last S.j)
      from Fin.ext (by
        simp only [lagEquiv_apply_val, Fin.val_natAdd, Fin.val_last]; omega),
    Fin.addCases_right]
  rw [show (Fin.last S.j : Fin (S.j + 1)) = Fin.natAdd S.j (0 : Fin 1)
      from Fin.ext (by simp), Fin.addCases_right]
  rw [show lagEquiv m S.j a = Fin.castAdd (S.j + 1) (⟨a.val, ha⟩ : Fin (1 + m))
      from Fin.ext (by simp), Fin.addCases_left]

theorem pJac_Hyt {n m : ℕ} (S : AmbStratum (n + (1 + m)))
    (Phi : EAPoly (n + (1 + m)) S.X.r) (c : Fin (1 + m) → ℝ)
    (z : Fin (n + (1 + m)) → ℝ) (mu : Fin S.j → ℝ) (mu0 : ℝ)
    (a l : Fin (1 + (m + S.j + 1)))
    (ha : 1 + m ≤ a.val) (ha2 : a.val < 1 + m + S.j) (hl : l.val < 1 + m) :
    lagJacTrue S Phi c z mu mu0 (lagEquiv m S.j a) (lagEquiv m S.j l)
      = eaEval S.X.c
          (eaD S.X.c (Fin.natAdd n ⟨l.val, hl⟩) (S.h ⟨a.val - (1 + m), by omega⟩)) z := by
  rw [lagJacTrue]
  simp only [Matrix.of_apply]
  rw [show lagEquiv m S.j l = Fin.castAdd (S.j + 1) (⟨l.val, hl⟩ : Fin (1 + m))
      from Fin.ext (by simp), Fin.addCases_left]
  rw [show lagEquiv m S.j a
        = Fin.natAdd (1 + m) (Fin.castAdd 1 (⟨a.val - (1 + m), by omega⟩ : Fin S.j))
      from Fin.ext (by
        simp only [lagEquiv_apply_val, Fin.val_natAdd, Fin.val_castAdd]; omega),
    Fin.addCases_right, Fin.addCases_left]

theorem pJac_Hmu {n m : ℕ} (S : AmbStratum (n + (1 + m)))
    (Phi : EAPoly (n + (1 + m)) S.X.r) (c : Fin (1 + m) → ℝ)
    (z : Fin (n + (1 + m)) → ℝ) (mu : Fin S.j → ℝ) (mu0 : ℝ)
    (a l : Fin (1 + (m + S.j + 1)))
    (ha : 1 + m ≤ a.val) (ha2 : a.val < 1 + m + S.j)
    (h1 : 1 + m ≤ l.val) (h2 : l.val < 1 + m + S.j) :
    lagJacTrue S Phi c z mu mu0 (lagEquiv m S.j a) (lagEquiv m S.j l) = 0 := by
  rw [lagJacTrue]
  simp only [Matrix.of_apply]
  rw [show lagEquiv m S.j l
        = Fin.natAdd (1 + m) (Fin.castAdd 1 (⟨l.val - (1 + m), by omega⟩ : Fin S.j))
      from Fin.ext (by
        simp only [lagEquiv_apply_val, Fin.val_natAdd, Fin.val_castAdd]; omega),
    Fin.addCases_right, Fin.addCases_left]
  rw [show lagEquiv m S.j a
        = Fin.natAdd (1 + m) (Fin.castAdd 1 (⟨a.val - (1 + m), by omega⟩ : Fin S.j))
      from Fin.ext (by
        simp only [lagEquiv_apply_val, Fin.val_natAdd, Fin.val_castAdd]; omega),
    Fin.addCases_right, Fin.addCases_left]

theorem pJac_Hmu0 {n m : ℕ} (S : AmbStratum (n + (1 + m)))
    (Phi : EAPoly (n + (1 + m)) S.X.r) (c : Fin (1 + m) → ℝ)
    (z : Fin (n + (1 + m)) → ℝ) (mu : Fin S.j → ℝ) (mu0 : ℝ)
    (a l : Fin (1 + (m + S.j + 1)))
    (ha : 1 + m ≤ a.val) (ha2 : a.val < 1 + m + S.j) (h : l.val = 1 + m + S.j) :
    lagJacTrue S Phi c z mu mu0 (lagEquiv m S.j a) (lagEquiv m S.j l) = 0 := by
  rw [lagJacTrue]
  simp only [Matrix.of_apply]
  rw [show lagEquiv m S.j l = Fin.natAdd (1 + m) (Fin.last S.j)
      from Fin.ext (by
        simp only [lagEquiv_apply_val, Fin.val_natAdd, Fin.val_last]; omega),
    Fin.addCases_right]
  rw [show (Fin.last S.j : Fin (S.j + 1)) = Fin.natAdd S.j (0 : Fin 1)
      from Fin.ext (by simp), Fin.addCases_right]
  rw [show lagEquiv m S.j a
        = Fin.natAdd (1 + m) (Fin.castAdd 1 (⟨a.val - (1 + m), by omega⟩ : Fin S.j))
      from Fin.ext (by
        simp only [lagEquiv_apply_val, Fin.val_natAdd, Fin.val_castAdd]; omega),
    Fin.addCases_right, Fin.addCases_left]

theorem pJac_Nyt {n m : ℕ} (S : AmbStratum (n + (1 + m)))
    (Phi : EAPoly (n + (1 + m)) S.X.r) (c : Fin (1 + m) → ℝ)
    (z : Fin (n + (1 + m)) → ℝ) (mu : Fin S.j → ℝ) (mu0 : ℝ)
    (a l : Fin (1 + (m + S.j + 1))) (ha : a.val = 1 + m + S.j) (hl : l.val < 1 + m) :
    lagJacTrue S Phi c z mu mu0 (lagEquiv m S.j a) (lagEquiv m S.j l) = 0 := by
  rw [lagJacTrue]
  simp only [Matrix.of_apply]
  rw [show lagEquiv m S.j l = Fin.castAdd (S.j + 1) (⟨l.val, hl⟩ : Fin (1 + m))
      from Fin.ext (by simp), Fin.addCases_left]
  rw [show lagEquiv m S.j a = Fin.natAdd (1 + m) (Fin.last S.j)
      from Fin.ext (by
        simp only [lagEquiv_apply_val, Fin.val_natAdd, Fin.val_last]; omega),
    Fin.addCases_right]
  rw [show (Fin.last S.j : Fin (S.j + 1)) = Fin.natAdd S.j (0 : Fin 1)
      from Fin.ext (by simp), Fin.addCases_right]

theorem pJac_Nmu {n m : ℕ} (S : AmbStratum (n + (1 + m)))
    (Phi : EAPoly (n + (1 + m)) S.X.r) (c : Fin (1 + m) → ℝ)
    (z : Fin (n + (1 + m)) → ℝ) (mu : Fin S.j → ℝ) (mu0 : ℝ)
    (a l : Fin (1 + (m + S.j + 1))) (ha : a.val = 1 + m + S.j)
    (h1 : 1 + m ≤ l.val) (h2 : l.val < 1 + m + S.j) :
    lagJacTrue S Phi c z mu mu0 (lagEquiv m S.j a) (lagEquiv m S.j l)
      = 2 * mu ⟨l.val - (1 + m), by omega⟩ := by
  rw [lagJacTrue]
  simp only [Matrix.of_apply]
  rw [show lagEquiv m S.j l
        = Fin.natAdd (1 + m) (Fin.castAdd 1 (⟨l.val - (1 + m), by omega⟩ : Fin S.j))
      from Fin.ext (by
        simp only [lagEquiv_apply_val, Fin.val_natAdd, Fin.val_castAdd]; omega),
    Fin.addCases_right, Fin.addCases_left]
  rw [show lagEquiv m S.j a = Fin.natAdd (1 + m) (Fin.last S.j)
      from Fin.ext (by
        simp only [lagEquiv_apply_val, Fin.val_natAdd, Fin.val_last]; omega),
    Fin.addCases_right]
  rw [show (Fin.last S.j : Fin (S.j + 1)) = Fin.natAdd S.j (0 : Fin 1)
      from Fin.ext (by simp), Fin.addCases_right]

theorem pJac_Nmu0 {n m : ℕ} (S : AmbStratum (n + (1 + m)))
    (Phi : EAPoly (n + (1 + m)) S.X.r) (c : Fin (1 + m) → ℝ)
    (z : Fin (n + (1 + m)) → ℝ) (mu : Fin S.j → ℝ) (mu0 : ℝ)
    (a l : Fin (1 + (m + S.j + 1))) (ha : a.val = 1 + m + S.j) (h : l.val = 1 + m + S.j) :
    lagJacTrue S Phi c z mu mu0 (lagEquiv m S.j a) (lagEquiv m S.j l) = 2 * mu0 := by
  rw [lagJacTrue]
  simp only [Matrix.of_apply]
  rw [show lagEquiv m S.j l = Fin.natAdd (1 + m) (Fin.last S.j)
      from Fin.ext (by
        simp only [lagEquiv_apply_val, Fin.val_natAdd, Fin.val_last]; omega),
    Fin.addCases_right]
  rw [show (Fin.last S.j : Fin (S.j + 1)) = Fin.natAdd S.j (0 : Fin 1)
      from Fin.ext (by simp), Fin.addCases_right]
  rw [show lagEquiv m S.j a = Fin.natAdd (1 + m) (Fin.last S.j)
      from Fin.ext (by
        simp only [lagEquiv_apply_val, Fin.val_natAdd, Fin.val_last]; omega),
    Fin.addCases_right]
  rw [show (Fin.last S.j : Fin (S.j + 1)) = Fin.natAdd S.j (0 : Fin 1)
      from Fin.ext (by simp), Fin.addCases_right]

end Work.WilE9G.Lagrange.LagBlk
