/-
  WilE9 / Sharp / PbDet — the four "algebraic" rows of the pulled-back fibre Jacobian.

  The rows of `Mmat` at the fibre indices `fS` (`τ - s u`), `fY i` (`y i - x i * w i`),
  `fW i` (`y i ^ 2 + w i ^ 2 - 1`) and `fT` (`τ ^ 2 + u ^ 2 - 1`) are computed explicitly: the
  corresponding polynomials contain no exponential atom, so `eaD` is `pderiv` in the ambient
  direction (`eaD_eq_pderiv_of_inr_free`), and the two shapes are handled by
  `eval_eaD_sub_mul` and `eval_eaD_pow2`.  The transport of the ambient `if`-conditions
  (`pbS n m = ambIdx n m l` etc.) to the fibre index `l` is `ite_pbS`/`ite_pbT`/`ite_pbU`/
  `ite_pbY`/`ite_pbW`.
-/
import Submission.Work.WilE9.Sharp.PbDetDefs

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace Work.WilE9.Sharp
open WilkiesDesign WilkiesDesign.E

/-! ## The derivative of the two polynomial shapes -/

section General

variable {k r : ℕ}

theorem eaD_eq_pderiv_of_inr_free (c : EAChain k r) (Q : EAPoly k r)
    (hQ : ∀ j : Fin r, MvPolynomial.pderiv (Sum.inr j) Q = 0) (d : Fin k) :
    eaD c d Q = MvPolynomial.pderiv (Sum.inl d) Q := by
  rw [eaD]
  rw [Finset.sum_eq_zero (fun j _ => by rw [hQ j]; ring)]
  simp

theorem eaD_sub_mul_poly (c : EAChain k r) (a b cc d : Fin k) :
    eaD c d ((MvPolynomial.X (Sum.inl a) : EAPoly k r)
        - MvPolynomial.X (Sum.inl b) * MvPolynomial.X (Sum.inl cc))
      = (if a = d then 1 else 0) - (if b = d then 1 else 0) * MvPolynomial.X (Sum.inl cc)
        - MvPolynomial.X (Sum.inl b) * (if cc = d then 1 else 0) := by
  rw [eaD_eq_pderiv_of_inr_free _ _ ?_ d]
  · simp only [Derivation.map_sub, MvPolynomial.pderiv_mul, MvPolynomial.pderiv_X]
    simp only [Pi.single_apply, Sum.inl.injEq]
    ring
  · intro j
    simp

theorem eaD_pow2_poly (c : EAChain k r) (a b d : Fin k) :
    eaD c d (((MvPolynomial.X (Sum.inl a) : EAPoly k r)) ^ 2
        + (MvPolynomial.X (Sum.inl b)) ^ 2 - 1)
      = 2 * MvPolynomial.X (Sum.inl a) * (if a = d then 1 else 0)
        + 2 * MvPolynomial.X (Sum.inl b) * (if b = d then 1 else 0) := by
  rw [eaD_eq_pderiv_of_inr_free _ _ ?_ d]
  · simp only [Derivation.map_sub, Derivation.map_add, MvPolynomial.pderiv_pow,
      MvPolynomial.pderiv_X, MvPolynomial.pderiv_one]
    simp only [Pi.single_apply, Sum.inl.injEq, Nat.reduceSub, pow_one, Nat.cast_ofNat]
    ring
  · intro j
    simp

theorem eval_eaD_sub_mul (c : EAChain k r) (a b cc d : Fin k) (z : Fin k → ℝ) :
    eaEval c
        (eaD c d ((MvPolynomial.X (Sum.inl a) : EAPoly k r)
          - MvPolynomial.X (Sum.inl b) * MvPolynomial.X (Sum.inl cc))) z
      = (if a = d then 1 else 0) - (if b = d then 1 else 0) * z cc
        - z b * (if cc = d then 1 else 0) := by
  rw [eaD_sub_mul_poly]
  split_ifs <;> simp [eaEval]

theorem eval_eaD_pow2 (c : EAChain k r) (a b d : Fin k) (z : Fin k → ℝ) :
    eaEval c
        (eaD c d (((MvPolynomial.X (Sum.inl a) : EAPoly k r)) ^ 2
          + (MvPolynomial.X (Sum.inl b)) ^ 2 - 1)) z
      = 2 * z a * (if a = d then 1 else 0) + 2 * z b * (if b = d then 1 else 0) := by
  rw [eaD_pow2_poly]
  split_ifs <;> simp [eaEval] <;> ring

end General

/-! ## Index arithmetic and the transports of the `if`-conditions -/

section Index

variable {n m : ℕ}

theorem fS_ne_fT : fS n m ≠ fT n m := by
  intro hh; have h := congrArg Fin.val hh; simp [fS, fT] at h
theorem fS_ne_fU : fS n m ≠ fU n m := by
  intro hh; have h := congrArg Fin.val hh; simp [fS, fU] at h
theorem fT_ne_fU : fT n m ≠ fU n m := by
  intro hh; have h := congrArg Fin.val hh; simp [fT, fU] at h
theorem fT_ne_fS : fT n m ≠ fS n m := (fS_ne_fT (n := n) (m := m)).symm
theorem fU_ne_fS : fU n m ≠ fS n m := (fS_ne_fU (n := n) (m := m)).symm
theorem fU_ne_fT : fU n m ≠ fT n m := (fT_ne_fU (n := n) (m := m)).symm
theorem fY_ne_fW (i : Fin n) : fY n m i ≠ fW n m i := by
  intro hh; have h := congrArg Fin.val hh; simp only [fY, fW] at h; omega
theorem fW_ne_fY (i : Fin n) : fW n m i ≠ fY n m i := (fY_ne_fW (n := n) (m := m) i).symm

theorem val_fS : ((fS n m : Fin (qpb n m)) : ℕ) = 0 := rfl
theorem val_fT : ((fT n m : Fin (qpb n m)) : ℕ) = 2 * n + 1 := rfl
theorem val_fU : ((fU n m : Fin (qpb n m)) : ℕ) = 2 * n + 2 := rfl
theorem val_fY (i : Fin n) : ((fY n m i : Fin (qpb n m)) : ℕ) = 1 + (i : ℕ) := rfl
theorem val_fW (i : Fin n) : ((fW n m i : Fin (qpb n m)) : ℕ) = n + 1 + (i : ℕ) := rfl

theorem natAdd_fS_val : (Fin.natAdd n (fS n m) : Fin (Npb n m)) = pbS n m := by
  apply Fin.ext; simp only [Fin.natAdd, fS, pbS]; omega
theorem natAdd_fT_val : (Fin.natAdd n (fT n m) : Fin (Npb n m)) = pbT n m := by
  apply Fin.ext; simp only [Fin.natAdd, fT, pbT]; omega
theorem natAdd_fU_val : (Fin.natAdd n (fU n m) : Fin (Npb n m)) = pbU n m := by
  apply Fin.ext; simp only [Fin.natAdd, fU, pbU]; omega
theorem natAdd_fY_val (i : Fin n) :
    (Fin.natAdd n (fY n m i) : Fin (Npb n m)) = pbY n m i := by
  apply Fin.ext; simp only [Fin.natAdd, fY, pbY]; omega
theorem natAdd_fW_val (i : Fin n) :
    (Fin.natAdd n (fW n m i) : Fin (Npb n m)) = pbW n m i := by
  apply Fin.ext; simp only [Fin.natAdd, fW, pbW]; omega
theorem natAdd_fA_val (b : Fin m) :
    (Fin.natAdd n (fA n m b) : Fin (Npb n m)) = pbA n m b := by
  apply Fin.ext; simp only [Fin.natAdd, fA, pbA]; omega

theorem ite_pbS (l : Fin (qpb n m)) (x : ℝ) :
    (if pbS n m = ambIdx n m l then x else 0) = (if l = fS n m then x else 0) := by
  by_cases h : l = fS n m
  · subst h; rw [if_pos (by rw [ambIdx]; exact (natAdd_fS_val (n := n) (m := m)).symm), if_pos rfl]
  · rw [if_neg h]; exact if_neg (fun hh => h (by
      have hh2 := congrArg Fin.val hh
      simp only [ambIdx, Fin.natAdd, pbS, fS, Fin.val_mk] at hh2
      exact Fin.ext (by simp only [fS, Fin.val_mk]; omega)))

theorem ite_pbT (l : Fin (qpb n m)) (x : ℝ) :
    (if pbT n m = ambIdx n m l then x else 0) = (if l = fT n m then x else 0) := by
  by_cases h : l = fT n m
  · subst h; rw [if_pos (by rw [ambIdx]; exact (natAdd_fT_val (n := n) (m := m)).symm), if_pos rfl]
  · rw [if_neg h]; exact if_neg (fun hh => h (by
      have hh2 := congrArg Fin.val hh
      simp only [ambIdx, Fin.natAdd, pbT, fT, Fin.val_mk] at hh2
      exact Fin.ext (by simp only [fT, Fin.val_mk]; omega)))

theorem ite_pbU (l : Fin (qpb n m)) (x : ℝ) :
    (if pbU n m = ambIdx n m l then x else 0) = (if l = fU n m then x else 0) := by
  by_cases h : l = fU n m
  · subst h; rw [if_pos (by rw [ambIdx]; exact (natAdd_fU_val (n := n) (m := m)).symm), if_pos rfl]
  · rw [if_neg h]; exact if_neg (fun hh => h (by
      have hh2 := congrArg Fin.val hh
      simp only [ambIdx, Fin.natAdd, pbU, fU, Fin.val_mk] at hh2
      exact Fin.ext (by simp only [fU, Fin.val_mk]; omega)))

theorem ite_pbY (i : Fin n) (l : Fin (qpb n m)) (x : ℝ) :
    (if pbY n m i = ambIdx n m l then x else 0) = (if l = fY n m i then x else 0) := by
  by_cases h : l = fY n m i
  · subst h
    rw [if_pos (by rw [ambIdx]; exact (natAdd_fY_val (n := n) (m := m) i).symm), if_pos rfl]
  · rw [if_neg h]; exact if_neg (fun hh => h (by
      have hh2 := congrArg Fin.val hh
      simp only [ambIdx, Fin.natAdd, pbY, fY, Fin.val_mk] at hh2
      exact Fin.ext (by simp only [fY, Fin.val_mk]; omega)))

theorem ite_pbW (i : Fin n) (l : Fin (qpb n m)) (x : ℝ) :
    (if pbW n m i = ambIdx n m l then x else 0) = (if l = fW n m i then x else 0) := by
  by_cases h : l = fW n m i
  · subst h
    rw [if_pos (by rw [ambIdx]; exact (natAdd_fW_val (n := n) (m := m) i).symm), if_pos rfl]
  · rw [if_neg h]; exact if_neg (fun hh => h (by
      have hh2 := congrArg Fin.val hh
      simp only [ambIdx, Fin.natAdd, pbW, fW, Fin.val_mk] at hh2
      exact Fin.ext (by simp only [fW, Fin.val_mk]; omega)))

theorem pbX_ne_ambIdx (i : Fin n) (l : Fin (qpb n m)) : pbX n m i ≠ ambIdx n m l := by
  intro hh
  have h1 := congrArg Fin.val hh
  simp only [ambIdx, Fin.natAdd, pbX, Fin.val_mk] at h1
  have := i.isLt
  omega

end Index

/-! ## The four algebraic rows -/

section Rows

variable {n m r : ℕ}

theorem Mmat_row_fS (c : EAChain (n + (1 + m)) r) (h : Fin (1 + m) → EAPoly (n + (1 + m)) r)
    (z : Fin (Npb n m) → ℝ) (l : Fin (qpb n m)) :
    Mmat n m r c h z (fS n m) l =
      (if l = fS n m then -z (pbU n m)
        else if l = fT n m then 1 else if l = fU n m then -z (pbS n m) else 0) := by
  rw [Mmat_apply]
  have hb : pbF n m r h (fS n m) =
      ((MvPolynomial.X (Sum.inl (pbT n m)) : EAPoly (Npb n m) r)
        - MvPolynomial.X (Sum.inl (pbS n m)) * MvPolynomial.X (Sum.inl (pbU n m))) := by
    rw [pbF]; rw [dif_pos (show ((fS n m : Fin (qpb n m)) : ℕ) = 0 from rfl)]
  change eaEval (pbChain c) (eaD (pbChain c) (ambIdx n m l) _) z =
    (if l = fS n m then -z (pbU n m)
      else if l = fT n m then 1 else if l = fU n m then -z (pbS n m) else 0)
  rw [hb, eval_eaD_sub_mul (pbChain c) (pbT n m) (pbS n m) (pbU n m) (ambIdx n m l) z,
    ite_pbT l 1, ite_pbS l 1, ite_pbU l 1]
  by_cases h1 : l = fS n m <;> by_cases h2 : l = fT n m <;> by_cases h3 : l = fU n m <;>
    simp_all [fS_ne_fT, fS_ne_fU, fT_ne_fU, fT_ne_fS, fU_ne_fS, fU_ne_fT] <;> ring

theorem Mmat_row_fY (c : EAChain (n + (1 + m)) r) (h : Fin (1 + m) → EAPoly (n + (1 + m)) r)
    (z : Fin (Npb n m) → ℝ) (i : Fin n) (l : Fin (qpb n m)) :
    Mmat n m r c h z (fY n m i) l =
      (if l = fY n m i then 1 else if l = fW n m i then -z (pbX n m i) else 0) := by
  rw [Mmat_apply]
  have hb : pbF n m r h (fY n m i) =
      ((MvPolynomial.X (Sum.inl (pbY n m i)) : EAPoly (Npb n m) r)
        - MvPolynomial.X (Sum.inl (pbX n m i)) * MvPolynomial.X (Sum.inl (pbW n m i))) := by
    rw [pbF]
    rw [dif_neg (by rw [val_fY]; omega), dif_pos (by rw [val_fY]; omega)]
    refine congrArg (fun i' : Fin n => (MvPolynomial.X (Sum.inl (pbY n m i')) : EAPoly (Npb n m) r)
      - MvPolynomial.X (Sum.inl (pbX n m i')) * MvPolynomial.X (Sum.inl (pbW n m i'))) ?_
    apply Fin.ext
    simp only [val_fY, Fin.val_mk]
    omega
  change eaEval (pbChain c) (eaD (pbChain c) (ambIdx n m l) _) z =
    (if l = fY n m i then 1 else if l = fW n m i then -z (pbX n m i) else 0)
  rw [hb, eval_eaD_sub_mul (pbChain c) (pbY n m i) (pbX n m i) (pbW n m i) (ambIdx n m l) z,
    ite_pbY i l 1, ite_pbW i l 1,
    show (if pbX n m i = ambIdx n m l then (1 : ℝ) else 0) = 0 from
      if_neg (pbX_ne_ambIdx i l)]
  by_cases h1 : l = fY n m i <;> by_cases h2 : l = fW n m i <;>
    simp_all [fY_ne_fW, fW_ne_fY] <;> ring

theorem Mmat_row_fW (c : EAChain (n + (1 + m)) r) (h : Fin (1 + m) → EAPoly (n + (1 + m)) r)
    (z : Fin (Npb n m) → ℝ) (i : Fin n) (l : Fin (qpb n m)) :
    Mmat n m r c h z (fW n m i) l =
      (if l = fY n m i then 2 * z (pbY n m i)
        else if l = fW n m i then 2 * z (pbW n m i) else 0) := by
  rw [Mmat_apply]
  have hb : pbF n m r h (fW n m i) =
      (((MvPolynomial.X (Sum.inl (pbY n m i)) : EAPoly (Npb n m) r)) ^ 2
        + (MvPolynomial.X (Sum.inl (pbW n m i))) ^ 2 - 1) := by
    rw [pbF]
    rw [dif_neg (by rw [val_fW]; omega), dif_neg (by rw [val_fW]; omega),
      dif_pos (by rw [val_fW]; omega)]
    refine congrArg (fun i' : Fin n =>
      ((MvPolynomial.X (Sum.inl (pbY n m i')) : EAPoly (Npb n m) r)) ^ 2
      + (MvPolynomial.X (Sum.inl (pbW n m i'))) ^ 2 - 1) ?_
    apply Fin.ext
    simp only [val_fW, Fin.val_mk]
    omega
  change eaEval (pbChain c) (eaD (pbChain c) (ambIdx n m l) _) z =
    (if l = fY n m i then 2 * z (pbY n m i) else if l = fW n m i then 2 * z (pbW n m i) else 0)
  rw [hb, eval_eaD_pow2 (pbChain c) (pbY n m i) (pbW n m i) (ambIdx n m l) z,
    ite_pbY i l 1, ite_pbW i l 1]
  by_cases h1 : l = fY n m i <;> by_cases h2 : l = fW n m i <;>
    simp_all [fY_ne_fW, fW_ne_fY] <;> ring

theorem Mmat_row_fT (c : EAChain (n + (1 + m)) r) (h : Fin (1 + m) → EAPoly (n + (1 + m)) r)
    (z : Fin (Npb n m) → ℝ) (l : Fin (qpb n m)) :
    Mmat n m r c h z (fT n m) l =
      (if l = fT n m then 2 * z (pbT n m) else if l = fU n m then 2 * z (pbU n m) else 0) := by
  rw [Mmat_apply]
  have hb : pbF n m r h (fT n m) =
      (((MvPolynomial.X (Sum.inl (pbT n m)) : EAPoly (Npb n m) r)) ^ 2
        + (MvPolynomial.X (Sum.inl (pbU n m))) ^ 2 - 1) := by
    rw [pbF]
    rw [dif_neg (by rw [val_fT]; omega), dif_neg (by rw [val_fT]; omega),
      dif_neg (by rw [val_fT]; omega), dif_pos (by rw [val_fT])]
  change eaEval (pbChain c) (eaD (pbChain c) (ambIdx n m l) _) z =
    (if l = fT n m then 2 * z (pbT n m) else if l = fU n m then 2 * z (pbU n m) else 0)
  rw [hb, eval_eaD_pow2 (pbChain c) (pbT n m) (pbU n m) (ambIdx n m l) z,
    ite_pbT l 1, ite_pbU l 1]
  by_cases h1 : l = fT n m <;> by_cases h2 : l = fU n m <;>
    simp_all [fT_ne_fU, fU_ne_fT] <;> ring

end Rows

end Work.WilE9.Sharp
