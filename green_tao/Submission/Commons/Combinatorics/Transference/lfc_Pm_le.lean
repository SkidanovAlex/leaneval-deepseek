import Mathlib
import Submission.Commons.NumberTheory.Sieve.KPseudorandom_mean
import Submission.Commons.Combinatorics.Additive.Gowers.gvn_weighted

open Finset
open scoped BigOperators
open Commons.NumberTheory.Sieve

namespace Commons.Combinatorics.Transference


variable {p : ℕ} [Fact p.Prime]

/-! ## Elementary `qmod` facts -/

lemma lfc_qmod_intDiv (a : ℤ) (b : ℕ) (hb : b ≠ 0) (hb' : (b : ZMod p) ≠ 0) :
    qmod p ((a : ℚ) / (b : ℚ)) = (a : ZMod p) * (b : ZMod p)⁻¹ := by
  set q : ℚ := Rat.divInt a (b : ℤ) with hq
  have hqz : q = (a : ℚ) / (b : ℚ) := by
    rw [hq, Rat.divInt_eq_div]; push_cast; ring
  have hden : (q.den : ℤ) ∣ (b : ℤ) := by
    rw [hq]; exact Rat.den_dvd a (b : ℤ)
  have hdne : (q.den : ZMod p) ≠ 0 := by
    intro h0
    have hdvd : (p : ℤ) ∣ (q.den : ℤ) :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd (q.den : ℤ) p).mp (by simpa using h0)
    have hbdvd : (p : ℤ) ∣ (b : ℤ) := dvd_trans hdvd hden
    have hpbdvd : p ∣ b := by exact_mod_cast hbdvd
    exact hb' ((CharP.cast_eq_zero_iff (ZMod p) p b).mpr hpbdvd)
  have hnum : (q.num : ℤ) * (b : ℤ) = a * q.den := by
    have h1 : (q.num : ℚ) / (q.den : ℚ) = (a : ℚ) / (b : ℚ) := by
      rw [Rat.num_div_den q, hqz]
    rw [div_eq_div_iff (by exact_mod_cast Rat.den_ne_zero q) (by exact_mod_cast hb)] at h1
    exact_mod_cast h1
  have hnumZ : (q.num : ZMod p) * (b : ZMod p) = (a : ZMod p) * (q.den : ZMod p) := by
    have := congrArg (fun z : ℤ => (z : ZMod p)) hnum
    push_cast at this
    exact this
  have key : (q.num : ZMod p) * (q.den : ZMod p)⁻¹ = (a : ZMod p) * (b : ZMod p)⁻¹ := by
    rw [← div_eq_mul_inv, ← div_eq_mul_inv, div_eq_div_iff hdne hb', hnumZ]
  rw [show ((a : ℚ) / (b : ℚ)) = q from hqz.symm]
  show (q.num : ZMod p) / (q.den : ZMod p) = (a : ZMod p) * (b : ZMod p)⁻¹
  rw [div_eq_mul_inv]
  exact key

lemma lfc_qmod_one : qmod p (1 : ℚ) = 1 := by simp [qmod]
lemma lfc_qmod_zero : qmod p (0 : ℚ) = 0 := by simp [qmod]

/-! ## The coefficient family -/

/-- The rational coefficient of the `i`-th `u`-variable. -/
noncomputable def lfc_rho (m : ℕ) (i : Fin m) : ℚ :=
  if (((i.val + 1 : ℕ)) : ZMod p) = 0 then 1
  else ((i.val : ℚ) - (m : ℚ)) / ((i.val + 1 : ℕ) : ℚ)

/-- The rational coefficient of the `j`-th `w`-variable. -/
noncomputable def lfc_sig (m n : ℕ) (j : Fin n) : ℚ :=
  if (((m + 2 + j.val : ℕ)) : ZMod p) = 0 then 1
  else ((j.val + 1 : ℚ)) / (((m + 2 + j.val : ℕ)) : ℚ)

/-- The constant term (the Green–Tao shift `b`). -/
noncomputable def lfc_C (m : ℕ) (z0 : ZMod p) : ZMod p :=
  if (((m + 1 : ℕ)) : ZMod p) = 0 then z0 else 0

/-- The linear forms controlling the `m`-th `P`-weight. -/
noncomputable def lfc_L (m n : ℕ) (ω : Fin n → Bool) : Fin (m + (n + n)) → ℚ :=
  Fin.append (lfc_rho (p:=p) m)
    (Fin.append (fun j : Fin n => if ω j then 0 else lfc_sig (p:=p) m n j)
      (fun j : Fin n => if ω j then lfc_sig (p:=p) m n j else 0))

/-- The variable vector: `u`-block, `a`-block, `b`-block. -/
noncomputable def lfc_Y (m n : ℕ) (u : Fin m → ZMod p) (a b : Fin n → ZMod p) :
    Fin (m + (n + n)) → ZMod p :=
  Fin.append u (Fin.append a b)

lemma qmod_lfcRho (m : ℕ) (i : Fin m) :
    qmod p (lfc_rho (p:=p) m i)
      = 1 - (((m + 1 : ℕ)) : ZMod p) * (((i.val + 1 : ℕ)) : ZMod p)⁻¹ := by
  unfold lfc_rho
  split_ifs with h
  · rw [lfc_qmod_one, h, inv_zero, mul_zero, sub_zero]
  · rw [show ((i.val : ℚ) - (m : ℚ)) = (((i.val : ℤ) - (m : ℤ) : ℤ) : ℚ) from by push_cast; ring]
    rw [lfc_qmod_intDiv (p:=p) ((i.val : ℤ) - (m : ℤ)) (i.val + 1) (by omega) h]
    have hc1 : (((i.val + 1 : ℕ)) : ZMod p) = (i.val : ZMod p) + 1 := by push_cast; ring
    have hc2 : (((m + 1 : ℕ)) : ZMod p) = (m : ZMod p) + 1 := by push_cast; ring
    rw [hc1, hc2]
    push_cast
    have hne : ((i.val : ZMod p)) + 1 ≠ 0 := by rw [← hc1]; exact h
    field_simp
    ring

lemma qmod_lfcSig (m n : ℕ) (j : Fin n) :
    qmod p (lfc_sig (p:=p) m n j)
      = 1 - (((m + 1 : ℕ)) : ZMod p) * ((((m + 2 + j.val : ℕ))) : ZMod p)⁻¹ := by
  unfold lfc_sig
  split_ifs with h
  · rw [lfc_qmod_one, h, inv_zero, mul_zero, sub_zero]
  · rw [show ((j.val : ℚ) + 1) = ((((j.val : ℤ) + 1 : ℤ)) : ℚ) from by push_cast; ring]
    rw [lfc_qmod_intDiv (p:=p) ((j.val : ℤ) + 1) (m + 2 + j.val) (by omega) h]
    have hc2 : (((m + 2 + j.val : ℕ)) : ZMod p) = (m : ZMod p) + 2 + (j.val : ZMod p) := by
      push_cast; ring
    have hc3 : (((m + 1 : ℕ)) : ZMod p) = (m : ZMod p) + 1 := by push_cast; ring
    rw [hc2, hc3]
    push_cast
    have hne : ((m : ZMod p) + 2 + (j.val : ZMod p)) ≠ 0 := by rw [← hc2]; exact h
    field_simp
    ring

lemma lfc_C_eq (m : ℕ) (z0 : ZMod p) :
    z0 * (1 - (((m + 1 : ℕ)) : ZMod p) * (((m + 1 : ℕ)) : ZMod p)⁻¹) = lfc_C (p:=p) m z0 := by
  unfold lfc_C
  split_ifs with h
  · rw [h, zero_mul, sub_zero, mul_one]
  · rw [mul_inv_cancel₀ h, sub_self, mul_zero]

/-! ## The algebraic kernel -/

/-- `app` is `Fin.append` up to a cast. -/
lemma lfc_app_eq_append {k m : ℕ} (hm : m + 2 ≤ k) {X : Type*}
    (U : Fin (m+1) → X) (W : Fin (k-1-(m+1)) → X)
    (t : Fin ((m+1) + (k-1-(m+1)))) :
    GVNgen.app k (m+1) (by omega) U W (Fin.cast (by omega : (m+1) + (k-1-(m+1)) = k-1) t)
      = Fin.append U W t := by
  revert t
  refine fun t => Fin.addCases (motive := fun t => GVNgen.app k (m+1) (by omega) U W
      (Fin.cast (by omega : (m+1) + (k-1-(m+1)) = k-1) t) = Fin.append U W t) ?_ ?_ t
  · intro i
    rw [Fin.append_left, GVNgen.app_apply]
    rw [dif_pos (by simp; omega)]
    congr 1
  · intro j
    rw [Fin.append_right, GVNgen.app_apply]
    rw [dif_neg (by simp; omega)]
    congr 1
    apply Fin.ext
    simp

/-- `phiZ` is a linear form in `y`. -/
lemma lfc_phiZ_sum (k : ℕ) (j : Fin k) (y : Fin (k-1) → ZMod p) :
    GVNgen.phiZ (p:=p) k j y
      = ∑ t : Fin (k-1), y t * (1 - (((j:ℕ)) : ZMod p) * ((((t:ℕ) : ZMod p)) + 1)⁻¹) := by
  rw [GVNgen.phiZ_apply, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl; intro t _
  rw [div_eq_mul_inv]; ring

/-- **Key pointwise identity**: the weighted vertex of `Pm` at stage `m` is one of the
linear-form-condition forms. -/
lemma lfc_pointwise {k m : ℕ} (hm : m + 2 ≤ k) (u : Fin m → ZMod p) (z0 : ZMod p)
    (a b : Fin (k-1-(m+1)) → ZMod p) (ω : Fin (k-1-(m+1)) → Bool) :
    GVNgen.phiZ (p:=p) k ⟨m+1, by omega⟩
        (GVNgen.app k (m+1) (by omega) (Fin.snoc u z0) (fun j => if ω j then b j else a j))
      = linForm p (lfc_L (p:=p) m (k-1-(m+1)) ω) (lfc_C (p:=p) m z0)
          (lfc_Y (p:=p) m (k-1-(m+1)) u a b) := by
  let N := k - 1 - (m + 1)
  set W : Fin N → ZMod p := fun j => if ω j then b j else a j with hW
  set dd2 : Fin ((m+1) + N) → ZMod p :=
    fun t => 1 - (((m+1:ℕ)) : ZMod p) * (((t.val : ZMod p)) + 1)⁻¹ with hdd2
  have h1 : GVNgen.phiZ (p:=p) k ⟨m+1, by omega⟩
      (GVNgen.app k (m+1) (by omega) (Fin.snoc u z0) W)
      = (∑ t : Fin ((m+1) + N), (Fin.append (Fin.snoc u z0) W) t * dd2 t) := by
    rw [lfc_phiZ_sum (p:=p) k ⟨m+1, by omega⟩
      (GVNgen.app k (m+1) (by omega) (Fin.snoc u z0) W)]
    rw [← Equiv.sum_comp (finCongr (by omega : (m+1) + N = k-1))
      (fun t : Fin (k-1) => (GVNgen.app k (m+1) (by omega) (Fin.snoc u z0) W) t
        * (1 - (((m+1:ℕ)) : ZMod p) * ((((t:ℕ):ZMod p)) + 1)⁻¹))]
    apply Finset.sum_congr rfl
    intro t _
    rw [finCongr_apply, lfc_app_eq_append (by omega) (Fin.snoc u z0) W t]
    rw [hdd2, Fin.val_cast]
  have h3 : (∑ t : Fin ((m+1) + N), (Fin.append (Fin.snoc u z0) W) t * dd2 t)
      = (∑ i : Fin m, u i * (1 - (((m+1:ℕ)) : ZMod p) * (((i.val : ZMod p)) + 1)⁻¹))
        + z0 * (1 - (((m+1:ℕ)) : ZMod p) * ((((m+1:ℕ)) : ZMod p))⁻¹)
        + ∑ j : Fin N, W j * (1 - (((m+1:ℕ)) : ZMod p) * ((((m+2+j.val:ℕ)) : ZMod p))⁻¹) := by
    rw [Fin.sum_univ_add (a := m+1) (b := N)]
    rw [Fin.sum_univ_add (a := m) (b := 1)]
    rw [Fin.sum_univ_one]
    have e1 : ∀ i : Fin m, ((Fin.snoc u z0 : Fin (m+1) → ZMod p)) (Fin.castAdd 1 i)
        * dd2 (Fin.castAdd N (Fin.castAdd 1 i))
        = u i * (1 - (((m+1:ℕ)) : ZMod p) * (((i.val : ZMod p)) + 1)⁻¹) := by
      intro i
      have hci : Fin.castAdd 1 i = (Fin.castSucc i : Fin (m+1)) := Fin.ext rfl
      rw [hci, Fin.snoc_castSucc]
      simp only [hdd2, Fin.val_castAdd, Fin.val_castSucc]
    have e2 : ((Fin.snoc u z0 : Fin (m+1) → ZMod p)) (Fin.natAdd m 0)
        * dd2 (Fin.castAdd N (Fin.natAdd m 0))
        = z0 * (1 - (((m+1:ℕ)) : ZMod p) * ((((m+1:ℕ)) : ZMod p))⁻¹) := by
      have hz : Fin.natAdd m (0 : Fin 1) = Fin.last m := Fin.ext (by simp)
      rw [hz, Fin.snoc_last]
      simp only [hdd2, Fin.val_castAdd, Fin.val_natAdd]
      norm_num
    have e3 : ∀ j : Fin N, W j * dd2 (Fin.natAdd (m+1) j)
        = W j * (1 - (((m+1:ℕ)) : ZMod p) * ((((m+2+j.val:ℕ)) : ZMod p))⁻¹) := by
      intro j
      simp only [hdd2, Fin.val_natAdd]
      congr 2
      push_cast
      ring
    simp only [Fin.append_left, Fin.append_right]
    rw [Finset.sum_congr rfl (fun i _ => e1 i),
        Finset.sum_congr rfl (fun j _ => e3 j), e2]
  have h4 : linForm p (lfc_L (p:=p) m N ω) (lfc_C (p:=p) m z0) (lfc_Y (p:=p) m N u a b)
      = (∑ i : Fin m, qmod p (lfc_rho (p:=p) m i) * u i)
        + (∑ j : Fin N, (if ω j then 0 else qmod p (lfc_sig (p:=p) m N j)) * a j)
        + (∑ j : Fin N, (if ω j then qmod p (lfc_sig (p:=p) m N j) else 0) * b j)
        + lfc_C (p:=p) m z0 := by
    rw [linForm]
    rw [Fin.sum_univ_add (a := m) (b := N + N)]
    rw [Fin.sum_univ_add (a := N) (b := N)]
    have e1 : ∀ i : Fin m, qmod p (lfc_L (p:=p) m N ω (Fin.castAdd (N+N) i))
        * lfc_Y (p:=p) m N u a b (Fin.castAdd (N+N) i)
        = qmod p (lfc_rho (p:=p) m i) * u i := by
      intro i
      rw [lfc_L, lfc_Y, Fin.append_left, Fin.append_left]
    have e2 : ∀ j : Fin N, qmod p (lfc_L (p:=p) m N ω (Fin.natAdd m (Fin.castAdd N j)))
        * lfc_Y (p:=p) m N u a b (Fin.natAdd m (Fin.castAdd N j))
        = (if ω j then 0 else qmod p (lfc_sig (p:=p) m N j)) * a j := by
      intro j
      rw [lfc_L, lfc_Y, Fin.append_right, Fin.append_right, Fin.append_left, Fin.append_left]
      by_cases h : ω j
      · rw [if_pos h, if_pos h, lfc_qmod_zero]
      · rw [if_neg h, if_neg h]
    have e3 : ∀ j : Fin N, qmod p (lfc_L (p:=p) m N ω (Fin.natAdd m (Fin.natAdd N j)))
        * lfc_Y (p:=p) m N u a b (Fin.natAdd m (Fin.natAdd N j))
        = (if ω j then qmod p (lfc_sig (p:=p) m N j) else 0) * b j := by
      intro j
      rw [lfc_L, lfc_Y, Fin.append_right, Fin.append_right, Fin.append_right, Fin.append_right]
      by_cases h : ω j
      · rw [if_pos h, if_pos h]
      · rw [if_neg h, if_neg h, lfc_qmod_zero]
    rw [Finset.sum_congr rfl (fun i _ => e1 i),
        Finset.sum_congr rfl (fun j _ => e2 j),
        Finset.sum_congr rfl (fun j _ => e3 j)]
    ring_nf
  rw [h1, h3, h4]
  have eRho : ∀ i : Fin m, (1 - (((m+1:ℕ)) : ZMod p) * (((i.val : ZMod p)) + 1)⁻¹)
      = qmod p (lfc_rho (p:=p) m i) := by
    intro i
    rw [qmod_lfcRho]
    congr 2
    push_cast; ring
  have eSig : ∀ j : Fin N, (1 - (((m+1:ℕ)) : ZMod p) * ((((m+2+j.val:ℕ)) : ZMod p))⁻¹)
      = qmod p (lfc_sig (p:=p) m N j) := by
    intro j
    rw [qmod_lfcSig]
  have eA : (∑ i : Fin m, u i * (1 - (((m+1:ℕ)) : ZMod p) * (((i.val : ZMod p)) + 1)⁻¹))
      = (∑ i : Fin m, qmod p (lfc_rho (p:=p) m i) * u i) := by
    apply Finset.sum_congr rfl; intro i _
    rw [eRho i, mul_comm]
  have eB : (∑ j : Fin N, W j * (1 - (((m+1:ℕ)) : ZMod p) * ((((m+2+j.val:ℕ)) : ZMod p))⁻¹))
      = (∑ j : Fin N, (if ω j then 0 else qmod p (lfc_sig (p:=p) m N j)) * a j)
        + (∑ j : Fin N, (if ω j then qmod p (lfc_sig (p:=p) m N j) else 0) * b j) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro j _
    rw [eSig j]
    simp only [hW]
    by_cases h : ω j <;> simp [h, mul_comm]
  have eC : z0 * (1 - (((m+1:ℕ)) : ZMod p) * ((((m+1:ℕ)) : ZMod p))⁻¹) = lfc_C (p:=p) m z0 :=
    lfc_C_eq m z0
  rw [eA, eB, eC]
  ring



variable {p : ℕ} [Fact p.Prime]

/-! ## `IsSmallRat` and `NonzeroTuple` for the coefficient family -/

lemma lfc_isSmallRat_one {L : ℕ} (hL : 1 ≤ L) : IsSmallRat L (1 : ℚ) := by
  constructor <;> simp [IsSmallRat, hL]

lemma lfc_isSmallRat_zero {L : ℕ} (hL : 1 ≤ L) : IsSmallRat L (0 : ℚ) := by
  constructor <;> simp [IsSmallRat, hL]

lemma lfc_isSmallRat_div (a : ℤ) (b : ℕ) (L : ℕ) (hb : b ≠ 0)
    (ha : a.natAbs ≤ L) (hbL : b ≤ L) : IsSmallRat L ((a : ℚ) / (b : ℚ)) := by
  set q : ℚ := Rat.divInt a (b : ℤ) with hq
  have hqz : q = (a : ℚ) / (b : ℚ) := by rw [hq, Rat.divInt_eq_div]; push_cast; ring
  have hden : (q.den : ℤ) ∣ (b : ℤ) := by rw [hq]; exact Rat.den_dvd a (b : ℤ)
  have hdenle : q.den ≤ b := by
    have h := Int.le_of_dvd (by exact_mod_cast Nat.pos_of_ne_zero hb) hden
    exact_mod_cast h
  have hnum : (q.num : ℤ) * (b : ℤ) = a * q.den := by
    have h1 : (q.num : ℚ) / (q.den : ℚ) = (a : ℚ) / (b : ℚ) := by
      rw [Rat.num_div_den q, hqz]
    rw [div_eq_div_iff (by exact_mod_cast Rat.den_ne_zero q) (by exact_mod_cast hb)] at h1
    exact_mod_cast h1
  have hnum2 : q.num.natAbs * b = a.natAbs * q.den := by
    simpa only [Int.natAbs_mul, Int.natAbs_natCast] using congrArg Int.natAbs hnum
  rw [← hqz]
  unfold IsSmallRat
  refine ⟨?_, ?_⟩
  · have hle : q.num.natAbs * b ≤ L * b := by
      rw [hnum2]; exact Nat.mul_le_mul ha hdenle
    exact Nat.le_of_mul_le_mul_right hle (Nat.pos_of_ne_zero hb)
  · exact le_trans hdenle hbL

lemma lfc_isSmallRat_rho {k m : ℕ} (hm : m ≤ k) (i : Fin m) :
    IsSmallRat k (lfc_rho (p:=p) m i) := by
  unfold lfc_rho
  split_ifs with h
  · exact lfc_isSmallRat_one (L := k) (by have := i.isLt; omega)
  · rw [show ((i.val : ℚ) - (m : ℚ)) = ((((i.val : ℤ) - (m : ℤ)) : ℤ) : ℚ) from by push_cast; ring]
    refine lfc_isSmallRat_div (a := (i.val : ℤ) - (m : ℤ)) (b := i.val + 1) (L := k)
      (Nat.succ_ne_zero _) ?_ (by omega)
    have h2 : (((i.val : ℤ) - (m : ℤ))).natAbs = m - i.val := by
      rw [show ((i.val : ℤ) - (m : ℤ)) = -(((m - i.val : ℕ)) : ℤ) from by
            rw [Nat.cast_sub (le_of_lt i.isLt)]; ring, Int.natAbs_neg, Int.natAbs_natCast]
    omega

lemma lfc_isSmallRat_sig {k m : ℕ} (hm : m + 2 ≤ k) (j : Fin (k-1-(m+1))) :
    IsSmallRat k (lfc_sig (p:=p) m (k-1-(m+1)) j) := by
  unfold lfc_sig
  split_ifs with h
  · exact lfc_isSmallRat_one (L := k) (by omega)
  · rw [show ((j.val : ℚ) + 1) = ((((j.val : ℤ) + 1 : ℤ)) : ℚ) from by push_cast; ring]
    refine lfc_isSmallRat_div (a := ((j.val : ℤ) + 1)) (b := m + 2 + j.val) (L := k)
      (by omega) ?_ (by omega)
    have h2 : (((j.val : ℤ) + 1)).natAbs = j.val + 1 := by
      rw [show ((j.val : ℤ) + 1) = (((j.val + 1 : ℕ)) : ℤ) from by push_cast; ring,
        Int.natAbs_natCast]
    omega

lemma lfc_isSmallRat_L {k m : ℕ} (hm : m + 2 ≤ k) (ω : Fin (k-1-(m+1)) → Bool) :
    ∀ q : Fin (m + ((k-1-(m+1)) + (k-1-(m+1)))),
      IsSmallRat k (lfc_L (p:=p) m (k-1-(m+1)) ω q) := by
  intro q
  revert q
  refine fun q => Fin.addCases
    (motive := fun q => IsSmallRat k (lfc_L (p:=p) m (k-1-(m+1)) ω q)) ?_ ?_ q
  · intro i
    rw [lfc_L, Fin.append_left]
    exact lfc_isSmallRat_rho (p:=p) (by omega) i
  · intro q
    revert q
    refine fun q => Fin.addCases
      (motive := fun q => IsSmallRat k (lfc_L (p:=p) m (k-1-(m+1)) ω (Fin.natAdd m q))) ?_ ?_ q
    · intro j
      rw [lfc_L, Fin.append_right, Fin.append_left]
      by_cases h : ω j
      · rw [if_pos h]; exact lfc_isSmallRat_zero (L := k) (by omega)
      · rw [if_neg h]; exact lfc_isSmallRat_sig (p:=p) hm j
    · intro j
      rw [lfc_L, Fin.append_right, Fin.append_right]
      by_cases h : ω j
      · rw [if_pos h]; exact lfc_isSmallRat_sig (p:=p) hm j
      · rw [if_neg h]; exact lfc_isSmallRat_zero (L := k) (by omega)

lemma lfcRho_ne_zero {m : ℕ} (i : Fin m) : lfc_rho (p:=p) m i ≠ 0 := by
  unfold lfc_rho
  split_ifs with h
  · norm_num
  · apply div_ne_zero
    · have hlt : (i.val : ℚ) < (m : ℚ) := by exact_mod_cast i.isLt
      exact sub_ne_zero.mpr (by intro hc; linarith)
    · positivity

lemma lfcSig_ne_zero {m n : ℕ} (j : Fin n) : lfc_sig (p:=p) m n j ≠ 0 := by
  unfold lfc_sig
  split_ifs with h
  · norm_num
  · apply div_ne_zero
    · positivity
    · positivity

lemma nonzeroTuple_lfcL {k m : ℕ} (hk : 3 ≤ k) (hm : m + 2 ≤ k)
    (ω : Fin (k-1-(m+1)) → Bool) :
    NonzeroTuple (lfc_L (p:=p) m (k-1-(m+1)) ω) := by
  by_cases hN : k - 1 - (m + 1) = 0
  · -- then m ≥ 1, use the `u`-index
    have hm1 : 1 ≤ m := by
      have h1 : k - 1 ≤ m + 1 := Nat.le_of_sub_eq_zero hN
      have h2 : 2 ≤ k - 1 := by omega
      omega
    refine ⟨Fin.castAdd ((k-1-(m+1)) + (k-1-(m+1))) ⟨0, hm1⟩, ?_⟩
    rw [lfc_L, Fin.append_left]
    exact lfcRho_ne_zero (p:=p) _
  · have hNpos : 0 < k - 1 - (m + 1) := Nat.pos_of_ne_zero hN
    let j : Fin (k-1-(m+1)) := ⟨0, hNpos⟩
    by_cases h : ω j
    · refine ⟨Fin.natAdd m (Fin.natAdd (k-1-(m+1)) j), ?_⟩
      rw [lfc_L, Fin.append_right, Fin.append_right, if_pos h]
      exact lfcSig_ne_zero (p:=p) j
    · refine ⟨Fin.natAdd m (Fin.castAdd (k-1-(m+1)) j), ?_⟩
      rw [lfc_L, Fin.append_right, Fin.append_left, if_neg h]
      exact lfcSig_ne_zero (p:=p) j

lemma notProp_lfcL {k m : ℕ} (hm : m + 2 ≤ k) {ω ω' : Fin (k-1-(m+1)) → Bool}
    (h : ω ≠ ω') :
    NotProp (lfc_L (p:=p) m (k-1-(m+1)) ω) (lfc_L (p:=p) m (k-1-(m+1)) ω') := by
  rintro ⟨lam, hlam⟩
  have hj : ∃ j, ω j ≠ ω' j := by
    by_contra hc
    push_neg at hc
    exact h (funext hc)
  obtain ⟨j, hj⟩ := hj
  have ha := hlam (Fin.natAdd m (Fin.castAdd (k-1-(m+1)) j))
  have hb := hlam (Fin.natAdd m (Fin.natAdd (k-1-(m+1)) j))
  rw [lfc_L, lfc_L, Fin.append_right, Fin.append_right, Fin.append_left, Fin.append_left] at ha
  rw [lfc_L, lfc_L, Fin.append_right, Fin.append_right, Fin.append_right, Fin.append_right] at hb
  have hsig := lfcSig_ne_zero (p:=p) (m:=m) (n:=k-1-(m+1)) j
  cases hjω : ω j <;> cases hjω' : ω' j <;> simp_all



variable {p : ℕ} [Fact p.Prime]

/-- The variable vector of `Pm` as a function on `Fin (m + (N+N))`. -/
noncomputable def lfc_epEquiv (m N : ℕ) :
    ((Fin m → ZMod p) × ((Fin N → ZMod p) × (Fin N → ZMod p)))
      ≃ (Fin (m + (N + N)) → ZMod p) where
  toFun r := Fin.append r.1 (Fin.append r.2.1 r.2.2)
  invFun x := (fun i => x (Fin.castAdd (N+N) i),
               (fun j => x (Fin.natAdd m (Fin.castAdd N j)),
                fun j => x (Fin.natAdd m (Fin.natAdd N j))))
  left_inv r := by
    obtain ⟨u, a, b⟩ := r
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · funext i; simp only [Fin.append_left]
    · funext j; simp only [Fin.append_left, Fin.append_right]
    · funext j; simp only [Fin.append_right]
  right_inv x := by
    funext t
    show (Fin.append (fun i => x (Fin.castAdd (N+N) i))
        (Fin.append (fun j : Fin N => x (Fin.natAdd m (Fin.castAdd N j)))
          (fun j : Fin N => x (Fin.natAdd m (Fin.natAdd N j))))) t = x t
    have hBC : (Fin.append (fun j : Fin N => x (Fin.natAdd m (Fin.castAdd N j)))
        (fun j : Fin N => x (Fin.natAdd m (Fin.natAdd N j))))
        = fun q : Fin (N+N) => x (Fin.natAdd m q) :=
      Fin.append_castAdd_natAdd (f := fun q : Fin (N+N) => x (Fin.natAdd m q))
    have hA : (Fin.append (fun i : Fin m => x (Fin.castAdd (N+N) i))
        (fun q : Fin (N+N) => x (Fin.natAdd m q))) = x :=
      Fin.append_castAdd_natAdd (f := x)
    rw [hBC, hA]

theorem lfc_Pm_le {p : ℕ} [Fact p.Prime] {k : ℕ} (hk : 3 ≤ k) {ν : ZMod p → ℝ} {ε : ℝ}
    (hLFC : Commons.NumberTheory.Sieve.LinFormsCond p ν (2 ^ (k - 1)) (2 * k) k ε) :
    ∀ i ∈ Finset.range (k - 1),
      GVNW.Pm (ZMod p) k (GVNgen.phiZ (p := p) k) ν i ≤ 1 + ε := by
  intro i hi
  rw [Finset.mem_range] at hi
  have hik : i + 1 < k := by omega
  have hm2 : i + 2 ≤ k := by omega
  rw [GVNW.Pm, dif_pos hik, GVNgen.av]
  set z0 : ZMod p := Classical.arbitrary (ZMod p) with hz0
  let N := k - 1 - (i + 1)
  let t := i + (N + N)
  have hNz : N = k - 1 - (i + 1) := rfl
  have htz : t = i + (N + N) := rfl
  have hcardℕ : Fintype.card ((Fin i → ZMod p) × ((Fin N → ZMod p) × (Fin N → ZMod p)))
      = Fintype.card (Fin t → ZMod p) := Fintype.card_congr (lfc_epEquiv (p:=p) i N)
  have hcard : (Fintype.card ((Fin i → ZMod p) × ((Fin N → ZMod p) × (Fin N → ZMod p))) : ℝ)
      = (Fintype.card (Fin t → ZMod p) : ℝ) := by rw [hcardℕ]
  have hG : ∀ r : (Fin i → ZMod p) × ((Fin N → ZMod p) × (Fin N → ZMod p)),
      (∏ ω : Fin N → Bool, ν (GVNgen.phiZ (p:=p) k ⟨i+1, hik⟩
        (GVNgen.app k (i+1) (by omega) (Fin.snoc r.1 z0)
          (fun j => if ω j then r.2.2 j else r.2.1 j))))
      = ∏ ω : Fin N → Bool, ν (linForm p (lfc_L (p:=p) i N ω) (lfc_C (p:=p) i z0)
          (lfc_epEquiv (p:=p) i N r)) := by
    intro r
    obtain ⟨u, a, b⟩ := r
    apply Finset.prod_congr rfl
    intro ω _
    congr 1
    exact lfc_pointwise (p:=p) hm2 u z0 a b ω
  have hsum : (∑ r : (Fin i → ZMod p) × ((Fin N → ZMod p) × (Fin N → ZMod p)),
      ∏ ω : Fin N → Bool, ν (GVNgen.phiZ (p:=p) k ⟨i+1, hik⟩
        (GVNgen.app k (i+1) (by omega) (Fin.snoc r.1 z0)
          (fun j => if ω j then r.2.2 j else r.2.1 j))))
      = ∑ x : Fin t → ZMod p, ∏ ω : Fin N → Bool,
          ν (linForm p (lfc_L (p:=p) i N ω) (lfc_C (p:=p) i z0) x) := by
    rw [Finset.sum_congr rfl (fun r _ => hG r)]
    exact Equiv.sum_comp (lfc_epEquiv (p:=p) i N)
      (fun x : Fin t → ZMod p => ∏ ω : Fin N → Bool,
        ν (linForm p (lfc_L (p:=p) i N ω) (lfc_C (p:=p) i z0) x))
  rw [hcard, hsum]
  have hcard1 : 1 ≤ Fintype.card (Fin N → Bool) := by
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]
    exact Nat.one_le_two_pow
  have hcard2 : Fintype.card (Fin N → Bool) ≤ 2 ^ (k - 1) := by
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]
    have hNle : N ≤ k - 1 := by rw [hNz]; exact Nat.sub_le _ _
    exact Nat.pow_le_pow_right (by norm_num) hNle
  have ht1 : 1 ≤ t := by rw [htz, hNz]; omega
  have ht2 : t ≤ 2 * k := by rw [htz, hNz]; omega
  have hmain := hLFC (Fin N → Bool) hcard1 hcard2 t ht1 ht2 (lfc_L (p:=p) i N)
    (fun ω q => lfc_isSmallRat_L (p:=p) hm2 ω q)
    (fun ω => nonzeroTuple_lfcL (p:=p) hk hm2 ω)
    (fun ω ω' hne => notProp_lfcL (p:=p) hm2 hne)
    (fun _ => lfc_C (p:=p) i z0)
  have hfin := (abs_le.mp hmain).2
  linarith [hfin]

end Commons.Combinatorics.Transference
