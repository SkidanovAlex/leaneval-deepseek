import Submission.Work.WilE9G.Lagrange.lagEqs_eval
import Submission.Work.WilE3.API.eaD_commute

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilE9G.Lagrange.LagBlk
open WilkiesDesign WilkiesDesign.E Work.WilE9G Work.WilE9G.Lagrange

/-! ## the `eaD` calculus on EA polynomials -/
theorem pEaD_add {k r : ℕ} (c : EAChain k r) (i : Fin k) (Q R : EAPoly k r) :
    eaD c i (Q + R) = eaD c i Q + eaD c i R := (Work.WilE3.API.eaD_derivation c i).1 Q R
theorem pEaD_sub {k r : ℕ} (c : EAChain k r) (i : Fin k) (Q R : EAPoly k r) :
    eaD c i (Q - R) = eaD c i Q - eaD c i R := by
  have h := (Work.WilE3.API.eaD_derivation c i).1 (Q - R) R
  rw [sub_add_cancel] at h
  rw [h]; ring
theorem pEaD_mul {k r : ℕ} (c : EAChain k r) (i : Fin k) (Q R : EAPoly k r) :
    eaD c i (Q * R) = eaD c i Q * R + Q * eaD c i R := (Work.WilE3.API.eaD_derivation c i).2.2.1 Q R
theorem pEaD_C {k r : ℕ} (c : EAChain k r) (i : Fin k) (a : ℝ) :
    eaD c i (MvPolynomial.C a) = 0 := (Work.WilE3.API.eaD_derivation c i).2.2.2 a
theorem pEaD_X_inl {k r : ℕ} (c : EAChain k r) (i l : Fin k) :
    eaD c i (MvPolynomial.X (Sum.inl l)) = if i = l then 1 else 0 :=
  Work.WilE3.API.eaDer_X_inl c i l
theorem pEaD_X_inr {k r : ℕ} (c : EAChain k r) (i : Fin k) (l : Fin r) :
    eaD c i (MvPolynomial.X (Sum.inr l)) = MvPolynomial.C (c.a l i) * MvPolynomial.X (Sum.inr l) :=
  Work.WilE3.API.eaDer_X_inr c i l
theorem pEaD_sum {k r : ℕ} {ι : Type*} (c : EAChain k r) (i : Fin k) (s : Finset ι)
    (f : ι → EAPoly k r) :
    eaD c i (s.sum f) = s.sum (fun j => eaD c i (f j)) :=
  map_sum (Work.WilE3.API.eaDer c i) f s
theorem pEaD_sq {k r : ℕ} (c : EAChain k r) (i : Fin k) (Q : EAPoly k r) :
    eaD c i (Q ^ 2) = eaD c i Q * Q + Q * eaD c i Q := by rw [pow_two, pEaD_mul]
theorem pEaD_one {k r : ℕ} (c : EAChain k r) (i : Fin k) :
    eaD c i (1 : EAPoly k r) = 0 := by
  have h : (1 : EAPoly k r) = MvPolynomial.C 1 := by rw [MvPolynomial.C_1]
  rw [h, pEaD_C]

/-! ## padding -/
theorem pPad_C {k K r : ℕ} (hm : k ≤ K) (a : ℝ) :
    Work.WilE7.EAPoly.pad hm (MvPolynomial.C a : EAPoly k r) = (MvPolynomial.C a : EAPoly K r) := by
  simp only [Work.WilE7.EAPoly.pad, MvPolynomial.rename_C]
theorem pPad_mul {k K r : ℕ} (hm : k ≤ K) (p q : EAPoly k r) :
    Work.WilE7.EAPoly.pad hm (p * q) = Work.WilE7.EAPoly.pad hm p * Work.WilE7.EAPoly.pad hm q := by
  simp only [Work.WilE7.EAPoly.pad, map_mul]
theorem pPad_X {k K r : ℕ} (hm : k ≤ K) (n : Fin k ⊕ Fin r) :
    Work.WilE7.EAPoly.pad hm (MvPolynomial.X n)
      = MvPolynomial.X (Sum.map (Fin.castLE hm) id n) := by
  simp only [Work.WilE7.EAPoly.pad, MvPolynomial.rename_X]
theorem pPad_add {k K r : ℕ} (hm : k ≤ K) (p q : EAPoly k r) :
    Work.WilE7.EAPoly.pad hm (p + q) = Work.WilE7.EAPoly.pad hm p + Work.WilE7.EAPoly.pad hm q := by
  simp only [Work.WilE7.EAPoly.pad, map_add]
theorem pPad_eaD_zero {k K r : ℕ} (hm : k ≤ K) (c : EAChain k r) (i : Fin K) (hi : k ≤ i.val) :
    ∀ Q : EAPoly k r, eaD (Work.WilE7.EAChain.pad hm c) i (Work.WilE7.EAPoly.pad hm Q) = 0 := by
  intro Q
  induction Q using MvPolynomial.induction_on with
  | C a => rw [pPad_C, pEaD_C]
  | add p q hp hq => rw [pPad_add, pEaD_add, hp, hq, add_zero]
  | mul_X p n hp =>
      rw [pPad_mul, pPad_X, pEaD_mul, hp, zero_mul]
      have hX : eaD (Work.WilE7.EAChain.pad hm c) i
          (MvPolynomial.X (Sum.map (Fin.castLE hm) id n)) = 0 := by
        rcases n with l' | j
        · simp only [Sum.map_inl]
          rw [pEaD_X_inl, ite_eq_right]
          intro hcon
          have h2 := congrArg Fin.val hcon
          simp only [Fin.val_castLE] at h2
          omega
        · simp only [Sum.map_inr, id_eq]
          rw [pEaD_X_inr]
          have hcoef : (Work.WilE7.EAChain.pad hm c).a j i = 0 := by
            show (if h : i.val < k then c.a j ⟨i.val, h⟩ else 0) = 0
            rw [dite_eq_right (by omega)]
          rw [hcoef, MvPolynomial.C_0, zero_mul]
      rw [hX, mul_zero, add_zero]

/-! ## the case split of `lagEqs` -/
theorem pLagEqs_apply {n m : ℕ} (S : AmbStratum (n + (1 + m)))
    (Phi : EAPoly (n + (1 + m)) S.X.r) (c : Fin (1 + m) → ℝ)
    (a : Fin (1 + (m + S.j + 1))) :
    lagEqs S Phi c a
      = Fin.addCases (fun l : Fin (1 + m) => lagL S Phi c l)
          (fun s : Fin (S.j + 1) =>
            Fin.addCases (fun b : Fin S.j => lagH S b) (fun _ : Fin 1 => lagN S) s)
          (lagEquiv m S.j a) := rfl

theorem pLagEqs_lt {n m : ℕ} (S : AmbStratum (n + (1 + m)))
    (Phi : EAPoly (n + (1 + m)) S.X.r) (c : Fin (1 + m) → ℝ)
    (a : Fin (1 + (m + S.j + 1))) (ha : a.val < 1 + m) :
    lagEqs S Phi c a = lagL S Phi c ⟨a.val, ha⟩ := by
  rw [pLagEqs_apply]
  have h : lagEquiv m S.j a = Fin.castAdd (S.j + 1) (⟨a.val, ha⟩ : Fin (1 + m)) := by
    apply Fin.ext; simp
  rw [h, Fin.addCases_left]

theorem pLagEqs_mid {n m : ℕ} (S : AmbStratum (n + (1 + m)))
    (Phi : EAPoly (n + (1 + m)) S.X.r) (c : Fin (1 + m) → ℝ)
    (a : Fin (1 + (m + S.j + 1))) (ha : 1 + m ≤ a.val) (ha2 : a.val < 1 + m + S.j) :
    lagEqs S Phi c a = lagH S ⟨a.val - (1 + m), by omega⟩ := by
  rw [pLagEqs_apply]
  have h : lagEquiv m S.j a
      = Fin.natAdd (1 + m) (Fin.castAdd 1 (⟨a.val - (1 + m), by omega⟩ : Fin S.j)) := by
    apply Fin.ext
    simp only [lagEquiv_apply_val, Fin.val_natAdd, Fin.val_castAdd]
    omega
  rw [h, Fin.addCases_right, Fin.addCases_left]

theorem pLagEqs_last {n m : ℕ} (S : AmbStratum (n + (1 + m)))
    (Phi : EAPoly (n + (1 + m)) S.X.r) (c : Fin (1 + m) → ℝ)
    (a : Fin (1 + (m + S.j + 1))) (ha : a.val = 1 + m + S.j) :
    lagEqs S Phi c a = lagN S := by
  rw [pLagEqs_apply]
  have h : lagEquiv m S.j a = Fin.natAdd (1 + m) (Fin.last S.j) := by
    apply Fin.ext
    simp only [lagEquiv_apply_val, Fin.val_natAdd, Fin.val_last]
    omega
  rw [h, Fin.addCases_right]
  rw [show (Fin.last S.j : Fin (S.j + 1)) = Fin.natAdd S.j (0 : Fin 1) from Fin.ext (by simp)]
  rw [Fin.addCases_right]

/-! ## the ambient indices of the columns -/
theorem pLagNatAdd_castLE {n m : ℕ} (S : AmbStratum (n + (1 + m)))
    (l : Fin (1 + (m + S.j + 1))) (hl : l.val < 1 + m) :
    Fin.natAdd n l
      = Fin.castLE (by omega : n + (1 + m) ≤ n + (1 + (m + S.j + 1)))
          (Fin.natAdd n (⟨l.val, hl⟩ : Fin (1 + m))) := by
  apply Fin.ext
  simp [Fin.natAdd]

theorem pLagNatAdd_muIdx {n m : ℕ} (S : AmbStratum (n + (1 + m)))
    (l : Fin (1 + (m + S.j + 1))) (h1 : 1 + m ≤ l.val) (h2 : l.val < 1 + m + S.j) :
    Fin.natAdd n l = muIdx n m (⟨l.val - (1 + m), by omega⟩ : Fin S.j) := by
  apply Fin.ext
  simp only [Fin.val_natAdd, muIdx_val]
  omega

theorem pLagNatAdd_mu0Idx {n m : ℕ} (S : AmbStratum (n + (1 + m)))
    (l : Fin (1 + (m + S.j + 1))) (h : l.val = 1 + m + S.j) :
    Fin.natAdd n l = mu0Idx n m S.j := by
  apply Fin.ext
  simp only [Fin.val_natAdd, mu0Idx_val]
  omega

/-! ## derivative of the multiplier variables, per column type -/
theorem pMuIdx_inj {n m j : ℕ} {a b : Fin j} (h : muIdx n m a = muIdx n m b) : a = b := by
  apply Fin.ext
  have hh := congrArg Fin.val h
  simp only [muIdx_val] at hh
  omega

theorem pEaD_mu0Var_castLE {n m : ℕ} (S : AmbStratum (n + (1 + m)))
    (hm : n + (1 + m) ≤ n + (1 + (m + S.j + 1))) (lam : Fin (1 + m)) :
    eaD (Work.WilE7.EAChain.pad hm S.X.c) (Fin.castLE hm (Fin.natAdd n lam)) (mu0Var S) = 0 := by
  show eaD (Work.WilE7.EAChain.pad hm S.X.c) (Fin.castLE hm (Fin.natAdd n lam))
    (MvPolynomial.X (Sum.inl (mu0Idx n m S.j))) = 0
  rw [pEaD_X_inl, ite_eq_right]
  intro h
  have hh := congrArg Fin.val h
  simp only [Fin.val_castLE, Fin.val_natAdd, mu0Idx_val] at hh
  omega

theorem pEaD_muVar_castLE {n m : ℕ} (S : AmbStratum (n + (1 + m)))
    (hm : n + (1 + m) ≤ n + (1 + (m + S.j + 1))) (lam : Fin (1 + m)) (x : Fin S.j) :
    eaD (Work.WilE7.EAChain.pad hm S.X.c) (Fin.castLE hm (Fin.natAdd n lam)) (muVar S x) = 0 := by
  show eaD (Work.WilE7.EAChain.pad hm S.X.c) (Fin.castLE hm (Fin.natAdd n lam))
    (MvPolynomial.X (Sum.inl (muIdx n m x))) = 0
  rw [pEaD_X_inl, ite_eq_right]
  intro h
  have hh := congrArg Fin.val h
  simp only [Fin.val_castLE, Fin.val_natAdd, muIdx_val] at hh
  omega

theorem pEaD_mu0Var_muIdx {n m : ℕ} (S : AmbStratum (n + (1 + m)))
    (hm : n + (1 + m) ≤ n + (1 + (m + S.j + 1))) (b : Fin S.j) :
    eaD (Work.WilE7.EAChain.pad hm S.X.c) (muIdx n m b) (mu0Var S) = 0 := by
  show eaD (Work.WilE7.EAChain.pad hm S.X.c) (muIdx n m b)
    (MvPolynomial.X (Sum.inl (mu0Idx n m S.j))) = 0
  rw [pEaD_X_inl, ite_eq_right]
  intro h
  have hh := congrArg Fin.val h
  simp only [muIdx_val, mu0Idx_val] at hh
  omega

theorem pEaD_muVar_muIdx {n m : ℕ} (S : AmbStratum (n + (1 + m)))
    (hm : n + (1 + m) ≤ n + (1 + (m + S.j + 1))) (b x : Fin S.j) :
    eaD (Work.WilE7.EAChain.pad hm S.X.c) (muIdx n m b) (muVar S x)
      = (if b = x then (1 : EAPoly (n + (1 + (m + S.j + 1))) S.X.r) else 0) := by
  show eaD (Work.WilE7.EAChain.pad hm S.X.c) (muIdx n m b)
    (MvPolynomial.X (Sum.inl (muIdx n m x))) = _
  rw [pEaD_X_inl]
  by_cases h : b = x
  · subst h; rw [ite_eq_left rfl, ite_eq_left rfl]
  · rw [ite_eq_right (fun hh => h (pMuIdx_inj hh)), ite_eq_right h]

theorem pEaD_mu0Var_self {n m : ℕ} (S : AmbStratum (n + (1 + m)))
    (hm : n + (1 + m) ≤ n + (1 + (m + S.j + 1))) :
    eaD (Work.WilE7.EAChain.pad hm S.X.c) (mu0Idx n m S.j) (mu0Var S) = 1 := by
  show eaD (Work.WilE7.EAChain.pad hm S.X.c) (mu0Idx n m S.j)
    (MvPolynomial.X (Sum.inl (mu0Idx n m S.j))) = 1
  rw [pEaD_X_inl, ite_eq_left rfl]

theorem pEaD_muVar_mu0 {n m : ℕ} (S : AmbStratum (n + (1 + m)))
    (hm : n + (1 + m) ≤ n + (1 + (m + S.j + 1))) (x : Fin S.j) :
    eaD (Work.WilE7.EAChain.pad hm S.X.c) (mu0Idx n m S.j) (muVar S x) = 0 := by
  show eaD (Work.WilE7.EAChain.pad hm S.X.c) (mu0Idx n m S.j)
    (MvPolynomial.X (Sum.inl (muIdx n m x))) = 0
  rw [pEaD_X_inl, ite_eq_right]
  intro h
  have hh := congrArg Fin.val h
  simp only [muIdx_val, mu0Idx_val] at hh
  omega

/-! ## derivative of the padded polynomials at a multiplier index -/
theorem pEaD_padZero_muIdx {n m : ℕ} (S : AmbStratum (n + (1 + m))) (b : Fin S.j)
    (hm : n + (1 + m) ≤ n + (1 + (m + S.j + 1))) (Q : EAPoly (n + (1 + m)) S.X.r) :
    eaD (Work.WilE7.EAChain.pad hm S.X.c) (muIdx n m b) (Work.WilE7.EAPoly.pad hm Q) = 0 := by
  apply pPad_eaD_zero hm S.X.c (muIdx n m b) _ Q
  simp only [muIdx_val]; omega

theorem pEaD_padZero_mu0 {n m : ℕ} (S : AmbStratum (n + (1 + m)))
    (hm : n + (1 + m) ≤ n + (1 + (m + S.j + 1))) (Q : EAPoly (n + (1 + m)) S.X.r) :
    eaD (Work.WilE7.EAChain.pad hm S.X.c) (mu0Idx n m S.j) (Work.WilE7.EAPoly.pad hm Q) = 0 := by
  apply pPad_eaD_zero hm S.X.c (mu0Idx n m S.j) _ Q
  simp only [mu0Idx_val]; omega

/-! ## sums against the Kronecker delta -/
theorem pSum_ite_one_mul {ι M : Type*} [Semiring M] [Fintype ι] [DecidableEq ι]
    (b : ι) (A : ι → M) :
    (∑ x, (if b = x then (1 : M) else 0) * A x) = A b := by
  rw [show (∑ x, (if b = x then (1 : M) else 0) * A x)
      = ∑ x, (if b = x then A x else 0) from
      Finset.sum_congr rfl (fun x _ => by by_cases h : b = x <;> simp [h])]
  rw [Finset.sum_ite_eq]
  simp

theorem pSum_mul_ite_one {ι M : Type*} [CommSemiring M] [Fintype ι] [DecidableEq ι]
    (b : ι) (A : ι → M) :
    (∑ x, A x * (if b = x then (1 : M) else 0)) = A b := by
  rw [show (∑ x, A x * (if b = x then (1 : M) else 0))
      = ∑ x, (if b = x then A x else 0) from
      Finset.sum_congr rfl (fun x _ => by by_cases h : b = x <;> simp [h])]
  rw [Finset.sum_ite_eq]
  simp

/-! ## evaluation at `lagPoint` -/
theorem pEval_muIdx {n m : ℕ} (S : AmbStratum (n + (1 + m)))
    (hm : n + (1 + m) ≤ n + (1 + (m + S.j + 1)))
    (z : Fin (n + (1 + m)) → ℝ) (mu : Fin S.j → ℝ) (mu0 : ℝ) (a : Fin S.j) :
    eaEval (Work.WilE7.EAChain.pad hm S.X.c) (MvPolynomial.X (Sum.inl (muIdx n m a)))
      (lagPoint z mu mu0) = mu a := by
  simp only [eaEval, MvPolynomial.eval_X, Sum.elim_inl]
  exact lagEval_lagPoint_muIdx z mu mu0 a

theorem pEval_mu0Idx {n m : ℕ} (S : AmbStratum (n + (1 + m)))
    (hm : n + (1 + m) ≤ n + (1 + (m + S.j + 1)))
    (z : Fin (n + (1 + m)) → ℝ) (mu : Fin S.j → ℝ) (mu0 : ℝ) :
    eaEval (Work.WilE7.EAChain.pad hm S.X.c) (MvPolynomial.X (Sum.inl (mu0Idx n m S.j)))
      (lagPoint z mu mu0) = mu0 := by
  simp only [eaEval, MvPolynomial.eval_X, Sum.elim_inl]
  exact lagEval_lagPoint_mu0Idx z mu mu0

theorem pEval_muVar {n m : ℕ} (S : AmbStratum (n + (1 + m)))
    (hm : n + (1 + m) ≤ n + (1 + (m + S.j + 1)))
    (z : Fin (n + (1 + m)) → ℝ) (mu : Fin S.j → ℝ) (mu0 : ℝ) (a : Fin S.j) :
    eaEval (Work.WilE7.EAChain.pad hm S.X.c) (muVar S a) (lagPoint z mu mu0) = mu a := by
  simp only [muVar, eaEval, MvPolynomial.eval_X, Sum.elim_inl]
  exact lagEval_lagPoint_muIdx z mu mu0 a

theorem pEval_mu0Var {n m : ℕ} (S : AmbStratum (n + (1 + m)))
    (hm : n + (1 + m) ≤ n + (1 + (m + S.j + 1)))
    (z : Fin (n + (1 + m)) → ℝ) (mu : Fin S.j → ℝ) (mu0 : ℝ) :
    eaEval (Work.WilE7.EAChain.pad hm S.X.c) (mu0Var S) (lagPoint z mu mu0) = mu0 := by
  simp only [mu0Var, eaEval, MvPolynomial.eval_X, Sum.elim_inl]
  exact lagEval_lagPoint_mu0Idx z mu mu0

theorem pEval_zero {k r : ℕ} (c : EAChain k r) (x : Fin k → ℝ) :
    eaEval c (0 : EAPoly k r) x = 0 := by simp [eaEval]

theorem pEval_neg {k r : ℕ} (c : EAChain k r) (Q : EAPoly k r) (x : Fin k → ℝ) :
    eaEval c (-Q) x = - eaEval c Q x := by simp [eaEval]

theorem pEval_pad {n m : ℕ} (S : AmbStratum (n + (1 + m)))
    (hm : n + (1 + m) ≤ n + (1 + (m + S.j + 1))) (Q : EAPoly (n + (1 + m)) S.X.r)
    (z : Fin (n + (1 + m)) → ℝ) (mu : Fin S.j → ℝ) (mu0 : ℝ) :
    eaEval (Work.WilE7.EAChain.pad hm S.X.c) (Work.WilE7.EAPoly.pad hm Q) (lagPoint z mu mu0)
      = eaEval S.X.c Q z := by
  rw [Work.WilE7.padAux.eaEval_pad hm S.X.c Q (lagPoint z mu mu0),
    lagEval_takeZ_lagPoint z mu mu0 hm]

end Work.WilE9G.Lagrange.LagBlk
