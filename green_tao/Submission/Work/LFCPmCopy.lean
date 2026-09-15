import Mathlib
import Submission.Commons.NumberTheory.Sieve.KPseudorandom_mean
import Submission.Commons.Combinatorics.Additive.Gowers.gvn_weighted
import Submission.Commons.Combinatorics.Transference.lfc_Pm_le

open Finset
open scoped BigOperators
open Commons.NumberTheory.Sieve
open Commons.Combinatorics.Transference

namespace LFCPmCopy


variable {p : ℕ} [Fact p.Prime]
variable {k : ℕ}

/-! ## Elementary arithmetic for the general ratio coefficient -/

/-- The rational number `(D - C)/D`, whose reduction mod `p` is `1 - C·D⁻¹`
(with value `1` when `D ≡ 0`). -/
noncomputable def gBr (D C : ℤ) : ℚ :=
  if (D : ZMod p) = 0 then 1 else ((D - C : ℤ) : ℚ) / ((D : ℚ))

lemma qmod_divInt (a b : ℤ) (hb : (b : ZMod p) ≠ 0) :
    qmod p ((a : ℚ) / (b : ℚ)) = (a : ZMod p) * (b : ZMod p)⁻¹ := by
  have hbne : b ≠ 0 := by rintro h; exact hb (by rw [h]; simp)
  set q : ℚ := Rat.divInt a b with hq
  have hqz : q = (a : ℚ) / (b : ℚ) := by rw [hq, Rat.divInt_eq_div]
  have hden : (q.den : ℤ) ∣ b := by rw [hq]; exact Rat.den_dvd a b
  have hdne : (q.den : ZMod p) ≠ 0 := by
    intro h0
    have hdvd : (p : ℤ) ∣ (q.den : ℤ) :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd (q.den : ℤ) p).mp (by simpa using h0)
    exact hb ((ZMod.intCast_zmod_eq_zero_iff_dvd b p).mpr (dvd_trans hdvd hden))
  have hnum : (q.num : ℤ) * b = a * q.den := by
    have h1 : (q.num : ℚ) / (q.den : ℚ) = (a : ℚ) / (b : ℚ) := by
      rw [Rat.num_div_den q, hqz]
    rw [div_eq_div_iff (by exact_mod_cast Rat.den_ne_zero q) (by exact_mod_cast hbne)] at h1
    exact_mod_cast h1
  have hnumZ : (q.num : ZMod p) * (b : ZMod p) = (a : ZMod p) * (q.den : ZMod p) := by
    have := congrArg (fun z : ℤ => (z : ZMod p)) hnum
    push_cast at this
    exact this
  have key : (q.num : ZMod p) * (q.den : ZMod p)⁻¹ = (a : ZMod p) * (b : ZMod p)⁻¹ := by
    rw [← div_eq_mul_inv, ← div_eq_mul_inv, div_eq_div_iff hdne hb, hnumZ]
  rw [show ((a : ℚ) / (b : ℚ)) = q from hqz.symm]
  show (q.num : ZMod p) / (q.den : ZMod p) = (a : ZMod p) * (b : ZMod p)⁻¹
  rw [div_eq_mul_inv]
  exact key

lemma isSmallRat_divInt {a b : ℤ} {L₀ : ℕ} (hb : b ≠ 0)
    (ha : a.natAbs ≤ L₀) (hbL : b.natAbs ≤ L₀) : IsSmallRat L₀ ((a : ℚ) / (b : ℚ)) := by
  set q : ℚ := Rat.divInt a b with hq
  have hqz : q = (a : ℚ) / (b : ℚ) := by rw [hq, Rat.divInt_eq_div]
  have hden : (q.den : ℤ) ∣ b := by rw [hq]; exact Rat.den_dvd a b
  have hden2 : (q.den : ℤ) ∣ (b.natAbs : ℤ) := Int.dvd_natAbs.mpr hden
  have hdenle : q.den ≤ b.natAbs := by
    have h := Int.le_of_dvd
      (show (0:ℤ) < (b.natAbs:ℤ) from by exact_mod_cast Int.natAbs_pos.mpr hb) hden2
    exact_mod_cast h
  have hnum : (q.num : ℤ) * b = a * q.den := by
    have h1 : (q.num : ℚ) / (q.den : ℚ) = (a : ℚ) / (b : ℚ) := by
      rw [Rat.num_div_den q, hqz]
    rw [div_eq_div_iff (by exact_mod_cast Rat.den_ne_zero q) (by exact_mod_cast hb)] at h1
    exact_mod_cast h1
  have hnum2 : q.num.natAbs * b.natAbs = a.natAbs * q.den := by
    simpa only [Int.natAbs_mul, Int.natAbs_natCast] using congrArg Int.natAbs hnum
  rw [← hqz]
  unfold IsSmallRat
  refine ⟨?_, ?_⟩
  · have hle : q.num.natAbs * b.natAbs ≤ L₀ * b.natAbs := by
      rw [hnum2]; exact Nat.mul_le_mul ha hdenle
    exact Nat.le_of_mul_le_mul_right hle (Int.natAbs_pos.mpr hb)
  · exact le_trans hdenle hbL

lemma qmod_gBr (D C : ℤ) :
    qmod p (gBr (p:=p) D C) = 1 - (C : ZMod p) * (D : ZMod p)⁻¹ := by
  unfold gBr
  split_ifs with h
  · rw [lfc_qmod_one, h, inv_zero, mul_zero, sub_zero]
  · rw [qmod_divInt (p:=p) (D - C) D h]
    push_cast
    rw [sub_mul, mul_inv_cancel₀ h]

lemma gBr_ne_zero {D C : ℤ} (hDC : D ≠ C) : gBr (p:=p) D C ≠ 0 := by
  unfold gBr
  split_ifs with h
  · norm_num
  · apply div_ne_zero
    · have hsub : D - C ≠ 0 := sub_ne_zero.mpr hDC
      intro h0
      exact hsub (by exact_mod_cast h0)
    · intro h0
      apply h
      rw [show D = 0 from by exact_mod_cast h0]
      simp

lemma isSmallRat_gBr {D C : ℤ} {K L₀ : ℕ} (hD : D.natAbs ≤ K) (hC : C.natAbs ≤ K)
    (hK : 2 * K ≤ L₀) (h1 : 1 ≤ L₀) : IsSmallRat L₀ (gBr (p:=p) D C) := by
  unfold gBr
  split_ifs with h
  · exact lfc_isSmallRat_one h1
  · have hsub : (D - C).natAbs ≤ 2 * K := by
      calc (D - C).natAbs ≤ D.natAbs + C.natAbs := Int.natAbs_sub_le D C
        _ ≤ K + K := Nat.add_le_add hD hC
        _ = 2 * K := by ring
    have hDne : D ≠ 0 := by
      intro h0; apply h; rw [h0]; simp
    exact isSmallRat_divInt (L₀ := L₀) hDne (le_trans hsub hK) (le_trans hD (by omega))

/-! ## The coefficient family attached to a value vector `c` -/

/-- The integer attached to the variable of index `t` in the reparametrisation. -/
noncomputable def gD (c : Fin k → ℤ) (t : Fin (k - 1)) : ℤ :=
  c ⟨t.val + 1, by have := t.isLt; omega⟩

/-- The coefficient of the variable `t` at the vertex `jj`. -/
noncomputable def gCoeff (c : Fin k → ℤ) (jj : Fin k) (t : Fin (k - 1)) : ZMod p :=
  1 - (c jj : ZMod p) * ((gD c t : ℤ) : ZMod p)⁻¹

/-- The rational coefficient of the `i`-th `u`-variable at stage `m`. -/
noncomputable def gRho (c : Fin k → ℤ) (m : ℕ) (hm : m + 2 ≤ k) (i : Fin m) : ℚ :=
  gBr (p:=p) (c ⟨i.val + 1, by omega⟩) (c ⟨m + 1, by omega⟩)

/-- The rational coefficient of the `j`-th `a`/`b`-variable at stage `m`. -/
noncomputable def gSig (c : Fin k → ℤ) (m : ℕ) (hm : m + 2 ≤ k)
    (j : Fin (k - 1 - (m + 1))) : ℚ :=
  gBr (p:=p) (c ⟨m + 2 + j.val, by omega⟩) (c ⟨m + 1, by omega⟩)

/-- The constant term at stage `m`. -/
noncomputable def gCp (c : Fin k → ℤ) (m : ℕ) (hm : m + 2 ≤ k) (z0 : ZMod p) : ZMod p :=
  if (c ⟨m + 1, by omega⟩ : ZMod p) = 0 then z0 else 0

/-- The linear forms controlling the `m`-th `P`-weight for the value vector `c`. -/
noncomputable def gL (c : Fin k → ℤ) (m : ℕ) (hm : m + 2 ≤ k)
    (ω : Fin (k - 1 - (m + 1)) → Bool) :
    Fin (m + ((k - 1 - (m + 1)) + (k - 1 - (m + 1)))) → ℚ :=
  Fin.append (gRho (p:=p) c m hm)
    (Fin.append (fun j => if ω j then 0 else gSig (p:=p) c m hm j)
      (fun j => if ω j then gSig (p:=p) c m hm j else 0))

/-- The general Green–Tao reparametrised vertex attached to `c`. -/
noncomputable def gphi (c : Fin k → ℤ) (jj : Fin k) : (Fin (k - 1) → ZMod p) → ZMod p :=
  fun y => ∑ t : Fin (k - 1), gCoeff (p:=p) c jj t * y t

/-! ## `qmod` and smallness of the coefficient family -/

lemma qmod_gRho (c : Fin k → ℤ) (m : ℕ) (hm : m + 2 ≤ k) (i : Fin m) :
    qmod p (gRho (p:=p) c m hm i)
      = 1 - (c ⟨m + 1, by omega⟩ : ZMod p)
          * ((c ⟨i.val + 1, by omega⟩ : ℤ) : ZMod p)⁻¹ := by
  unfold gRho
  exact qmod_gBr (p:=p) _ _

lemma qmod_gSig (c : Fin k → ℤ) (m : ℕ) (hm : m + 2 ≤ k) (j : Fin (k - 1 - (m + 1))) :
    qmod p (gSig (p:=p) c m hm j)
      = 1 - (c ⟨m + 1, by omega⟩ : ZMod p)
          * ((c ⟨m + 2 + j.val, by omega⟩ : ℤ) : ZMod p)⁻¹ := by
  unfold gSig
  exact qmod_gBr (p:=p) _ _

lemma gCoeff_eq_gRho (c : Fin k → ℤ) (m : ℕ) (hm : m + 2 ≤ k) (i : Fin m) :
    gCoeff (p:=p) c ⟨m + 1, by omega⟩ (⟨i.val, by omega⟩ : Fin (k - 1))
      = qmod p (gRho (p:=p) c m hm i) := by
  have hg : gD c (⟨i.val, by omega⟩ : Fin (k - 1)) = c ⟨i.val + 1, by omega⟩ := rfl
  rw [qmod_gRho]
  unfold gCoeff
  rw [hg]

lemma gCoeff_eq_gSig (c : Fin k → ℤ) (m : ℕ) (hm : m + 2 ≤ k) (j : Fin (k - 1 - (m + 1))) :
    gCoeff (p:=p) c ⟨m + 1, by omega⟩ (⟨m + 1 + j.val, by omega⟩ : Fin (k - 1))
      = qmod p (gSig (p:=p) c m hm j) := by
  have hg : gD c (⟨m + 1 + j.val, by omega⟩ : Fin (k - 1))
      = c ⟨m + 2 + j.val, by omega⟩ := by
    unfold gD
    congr 1
    apply Fin.ext
    ring
  rw [qmod_gSig]
  unfold gCoeff
  rw [hg]

lemma gC_eq (c : Fin k → ℤ) (m : ℕ) (hm : m + 2 ≤ k) (z0 : ZMod p) :
    z0 * (1 - (c ⟨m + 1, by omega⟩ : ZMod p) * (c ⟨m + 1, by omega⟩ : ZMod p)⁻¹)
      = gCp (p:=p) c m hm z0 := by
  unfold gCp
  by_cases h : (c ⟨m + 1, by omega⟩ : ZMod p) = 0
  · rw [h]; simp
  · rw [mul_inv_cancel₀ h, sub_self, mul_zero, if_neg h]

lemma gCoeff_eq_gC (c : Fin k → ℤ) (m : ℕ) (hm : m + 2 ≤ k) (z0 : ZMod p) :
    z0 * gCoeff (p:=p) c ⟨m + 1, by omega⟩ (⟨m, by omega⟩ : Fin (k - 1))
      = gCp (p:=p) c m hm z0 := by
  have hg : gD c (⟨m, by omega⟩ : Fin (k - 1)) = c ⟨m + 1, by omega⟩ := rfl
  unfold gCoeff
  rw [hg]
  exact gC_eq (p:=p) c m hm z0

lemma gRho_ne_zero (c : Fin k → ℤ) (hinj : ∀ a b : Fin k, a ≠ b → c a ≠ c b)
    (m : ℕ) (hm : m + 2 ≤ k) (i : Fin m) : gRho (p:=p) c m hm i ≠ 0 := by
  unfold gRho
  refine gBr_ne_zero (p:=p) (hinj _ _ ?_)
  intro h
  have hv := congrArg Fin.val h
  simp only [Fin.val_mk] at hv
  omega

lemma gSig_ne_zero (c : Fin k → ℤ) (hinj : ∀ a b : Fin k, a ≠ b → c a ≠ c b)
    (m : ℕ) (hm : m + 2 ≤ k) (j : Fin (k - 1 - (m + 1))) :
    gSig (p:=p) c m hm j ≠ 0 := by
  unfold gSig
  refine gBr_ne_zero (p:=p) (hinj _ _ ?_)
  intro h
  have hv := congrArg Fin.val h
  simp only [Fin.val_mk] at hv
  omega

lemma isSmallRat_gRho {c : Fin k → ℤ} {K L₀ : ℕ} (hcb : ∀ n, (c n).natAbs ≤ K)
    (hK : 2 * K ≤ L₀) (h1 : 1 ≤ L₀) (m : ℕ) (hm : m + 2 ≤ k) (i : Fin m) :
    IsSmallRat L₀ (gRho (p:=p) c m hm i) := by
  unfold gRho
  exact isSmallRat_gBr (p:=p) (hcb _) (hcb _) hK h1

lemma isSmallRat_gSig {c : Fin k → ℤ} {K L₀ : ℕ} (hcb : ∀ n, (c n).natAbs ≤ K)
    (hK : 2 * K ≤ L₀) (h1 : 1 ≤ L₀) (m : ℕ) (hm : m + 2 ≤ k)
    (j : Fin (k - 1 - (m + 1))) : IsSmallRat L₀ (gSig (p:=p) c m hm j) := by
  unfold gSig
  exact isSmallRat_gBr (p:=p) (hcb _) (hcb _) hK h1

lemma isSmallRat_gL {c : Fin k → ℤ} {K L₀ : ℕ} (hcb : ∀ n, (c n).natAbs ≤ K)
    (hK : 2 * K ≤ L₀) (h1 : 1 ≤ L₀) (m : ℕ) (hm : m + 2 ≤ k)
    (ω : Fin (k - 1 - (m + 1)) → Bool) :
    ∀ q : Fin (m + ((k - 1 - (m + 1)) + (k - 1 - (m + 1)))),
      IsSmallRat L₀ (gL (p:=p) c m hm ω q) := by
  intro q
  revert q
  refine fun q => Fin.addCases
    (motive := fun q => IsSmallRat L₀ (gL (p:=p) c m hm ω q)) ?_ ?_ q
  · intro i
    rw [gL, Fin.append_left]
    exact isSmallRat_gRho (p:=p) hcb hK h1 m hm i
  · intro q
    revert q
    refine fun q => Fin.addCases
      (motive := fun q => IsSmallRat L₀ (gL (p:=p) c m hm ω (Fin.natAdd m q))) ?_ ?_ q
    · intro j
      rw [gL, Fin.append_right, Fin.append_left]
      by_cases h : ω j
      · rw [if_pos h]; exact lfc_isSmallRat_zero h1
      · rw [if_neg h]; exact isSmallRat_gSig (p:=p) hcb hK h1 m hm j
    · intro j
      rw [gL, Fin.append_right, Fin.append_right]
      by_cases h : ω j
      · rw [if_pos h]; exact isSmallRat_gSig (p:=p) hcb hK h1 m hm j
      · rw [if_neg h]; exact lfc_isSmallRat_zero h1

lemma nonzeroTuple_gL {c : Fin k → ℤ} (hk : 3 ≤ k)
    (hinj : ∀ a b : Fin k, a ≠ b → c a ≠ c b)
    (m : ℕ) (hm : m + 2 ≤ k) (ω : Fin (k - 1 - (m + 1)) → Bool) :
    NonzeroTuple (gL (p:=p) c m hm ω) := by
  by_cases hN : k - 1 - (m + 1) = 0
  · have hm1 : 1 ≤ m := by
      have h1 : k - 1 ≤ m + 1 := Nat.le_of_sub_eq_zero hN
      have h2 : 2 ≤ k - 1 := by omega
      omega
    refine ⟨Fin.castAdd ((k - 1 - (m + 1)) + (k - 1 - (m + 1))) ⟨0, hm1⟩, ?_⟩
    rw [gL, Fin.append_left]
    exact gRho_ne_zero (p:=p) c hinj m hm _
  · have hNpos : 0 < k - 1 - (m + 1) := Nat.pos_of_ne_zero hN
    let j : Fin (k - 1 - (m + 1)) := ⟨0, hNpos⟩
    by_cases h : ω j
    · refine ⟨Fin.natAdd m (Fin.natAdd (k - 1 - (m + 1)) j), ?_⟩
      rw [gL, Fin.append_right, Fin.append_right, if_pos h]
      exact gSig_ne_zero (p:=p) c hinj m hm j
    · refine ⟨Fin.natAdd m (Fin.castAdd (k - 1 - (m + 1)) j), ?_⟩
      rw [gL, Fin.append_right, Fin.append_left, if_neg h]
      exact gSig_ne_zero (p:=p) c hinj m hm j

lemma notProp_gL {c : Fin k → ℤ} (hinj : ∀ a b : Fin k, a ≠ b → c a ≠ c b)
    (m : ℕ) (hm : m + 2 ≤ k) {ω ω' : Fin (k - 1 - (m + 1)) → Bool} (h : ω ≠ ω') :
    NotProp (gL (p:=p) c m hm ω) (gL (p:=p) c m hm ω') := by
  rintro ⟨lam, hlam⟩
  have hj : ∃ j, ω j ≠ ω' j := by
    by_contra hc
    push Not at hc
    exact h (funext hc)
  obtain ⟨j, hj⟩ := hj
  have ha := hlam (Fin.natAdd m (Fin.castAdd (k - 1 - (m + 1)) j))
  have hb := hlam (Fin.natAdd m (Fin.natAdd (k - 1 - (m + 1)) j))
  rw [gL, gL, Fin.append_right, Fin.append_right, Fin.append_left, Fin.append_left] at ha
  rw [gL, gL, Fin.append_right, Fin.append_right, Fin.append_right, Fin.append_right] at hb
  have hsig := gSig_ne_zero (p:=p) c hinj m hm j
  cases hjω : ω j <;> cases hjω' : ω' j <;> simp_all

/-! ## The pointwise identity -/

lemma g_pointwise {c : Fin k → ℤ} {m : ℕ} (hm : m + 2 ≤ k) (u : Fin m → ZMod p)
    (z0 : ZMod p) (a b : Fin (k - 1 - (m + 1)) → ZMod p)
    (ω : Fin (k - 1 - (m + 1)) → Bool) :
    gphi (p:=p) c ⟨m + 1, by omega⟩
        (GVNgen.app k (m + 1) (by omega) (Fin.snoc u z0) (fun j => if ω j then b j else a j))
      = linForm p (gL (p:=p) c m hm ω) (gCp (p:=p) c m hm z0)
          (Fin.append u (Fin.append a b)) := by
  let N := k - 1 - (m + 1)
  set W : Fin N → ZMod p := fun j => if ω j then b j else a j with hW
  have hkN : (m + 1) + N = k - 1 := by simp only [N]; omega
  simp only [gphi]
  have h1 : (∑ t : Fin (k - 1), gCoeff (p:=p) c ⟨m + 1, by omega⟩ t
        * (GVNgen.app k (m + 1) (by omega) (Fin.snoc u z0) W) t)
      = ∑ t : Fin ((m + 1) + N), (Fin.append (Fin.snoc u z0) W) t
            * gCoeff (p:=p) c ⟨m + 1, by omega⟩ (Fin.cast hkN t) := by
    rw [← Equiv.sum_comp (finCongr hkN)
      (fun t : Fin (k - 1) => gCoeff (p:=p) c ⟨m + 1, by omega⟩ t
        * (GVNgen.app k (m + 1) (by omega) (Fin.snoc u z0) W) t)]
    apply Finset.sum_congr rfl
    intro t _
    rw [finCongr_apply, lfc_app_eq_append (m := m) (by omega) (Fin.snoc u z0) W t]
    ring
  have h3 : (∑ t : Fin ((m + 1) + N), (Fin.append (Fin.snoc u z0) W) t
        * gCoeff (p:=p) c ⟨m + 1, by omega⟩ (Fin.cast hkN t))
      = (∑ i : Fin m, u i
            * gCoeff (p:=p) c ⟨m + 1, by omega⟩ (⟨i.val, by omega⟩ : Fin (k - 1)))
        + z0 * gCoeff (p:=p) c ⟨m + 1, by omega⟩ (⟨m, by omega⟩ : Fin (k - 1))
        + ∑ j : Fin N, W j
            * gCoeff (p:=p) c ⟨m + 1, by omega⟩ (⟨m + 1 + j.val, by omega⟩ : Fin (k - 1)) := by
    rw [Fin.sum_univ_add (a := m + 1) (b := N)]
    rw [Fin.sum_univ_add (a := m) (b := 1)]
    rw [Fin.sum_univ_one]
    have e1 : ∀ i : Fin m,
        (Fin.snoc u z0 : Fin (m + 1) → ZMod p) (Fin.castAdd 1 i)
          * gCoeff (p:=p) c ⟨m + 1, by omega⟩
              (Fin.cast hkN (Fin.castAdd N (Fin.castAdd 1 i)))
        = u i * gCoeff (p:=p) c ⟨m + 1, by omega⟩ (⟨i.val, by omega⟩ : Fin (k - 1)) := by
      intro i
      have hidx : Fin.cast hkN (Fin.castAdd N (Fin.castAdd 1 i)) = (⟨i.val, by omega⟩ : Fin (k - 1)) :=
        Fin.ext rfl
      have hci : (Fin.castAdd 1 i : Fin (m + 1)) = Fin.castSucc i := Fin.ext rfl
      rw [hidx, hci, Fin.snoc_castSucc]
    have e2 : (Fin.snoc u z0 : Fin (m + 1) → ZMod p) (Fin.natAdd m (0 : Fin 1))
          * gCoeff (p:=p) c ⟨m + 1, by omega⟩
              (Fin.cast hkN (Fin.castAdd N (Fin.natAdd m (0 : Fin 1))))
        = z0 * gCoeff (p:=p) c ⟨m + 1, by omega⟩ (⟨m, by omega⟩ : Fin (k - 1)) := by
      have hidx : Fin.cast hkN (Fin.castAdd N (Fin.natAdd m (0 : Fin 1))) = (⟨m, by omega⟩ : Fin (k - 1)) :=
        Fin.ext rfl
      have hlast : (Fin.natAdd m (0 : Fin 1) : Fin (m + 1)) = Fin.last m := Fin.ext (by simp)
      rw [hidx, hlast, Fin.snoc_last]
    have e3 : ∀ j : Fin N, W j
          * gCoeff (p:=p) c ⟨m + 1, by omega⟩ (Fin.cast hkN (Fin.natAdd (m + 1) j))
        = W j * gCoeff (p:=p) c ⟨m + 1, by omega⟩ (⟨m + 1 + j.val, by omega⟩ : Fin (k - 1)) := by
      intro j
      have hidx : Fin.cast hkN (Fin.natAdd (m + 1) j) = (⟨m + 1 + j.val, by omega⟩ : Fin (k - 1)) :=
        Fin.ext rfl
      rw [hidx]
    simp only [Fin.append_left, Fin.append_right]
    rw [Finset.sum_congr rfl (fun i _ => e1 i),
        Finset.sum_congr rfl (fun j _ => e3 j), e2]
  have h4 : linForm p (gL (p:=p) c m hm ω) (gCp (p:=p) c m hm z0)
        (Fin.append u (Fin.append a b))
      = (∑ i : Fin m, qmod p (gRho (p:=p) c m hm i) * u i)
        + (∑ j : Fin N, (if ω j then 0 else qmod p (gSig (p:=p) c m hm j)) * a j)
        + (∑ j : Fin N, (if ω j then qmod p (gSig (p:=p) c m hm j) else 0) * b j)
        + gCp (p:=p) c m hm z0 := by
    rw [linForm]
    rw [Fin.sum_univ_add (a := m) (b := N + N)]
    rw [Fin.sum_univ_add (a := N) (b := N)]
    have e1 : ∀ i : Fin m, qmod p (gL (p:=p) c m hm ω (Fin.castAdd (N + N) i))
        * (Fin.append u (Fin.append a b)) (Fin.castAdd (N + N) i)
        = qmod p (gRho (p:=p) c m hm i) * u i := by
      intro i
      rw [gL, Fin.append_left, Fin.append_left]
    have e2 : ∀ j : Fin N,
        qmod p (gL (p:=p) c m hm ω (Fin.natAdd m (Fin.castAdd N j)))
          * (Fin.append u (Fin.append a b)) (Fin.natAdd m (Fin.castAdd N j))
        = (if ω j then 0 else qmod p (gSig (p:=p) c m hm j)) * a j := by
      intro j
      rw [gL, Fin.append_right, Fin.append_right, Fin.append_left, Fin.append_left]
      by_cases h : ω j
      · rw [if_pos h, if_pos h, lfc_qmod_zero]
      · rw [if_neg h, if_neg h]
    have e3 : ∀ j : Fin N,
        qmod p (gL (p:=p) c m hm ω (Fin.natAdd m (Fin.natAdd N j)))
          * (Fin.append u (Fin.append a b)) (Fin.natAdd m (Fin.natAdd N j))
        = (if ω j then qmod p (gSig (p:=p) c m hm j) else 0) * b j := by
      intro j
      rw [gL, Fin.append_right, Fin.append_right, Fin.append_right, Fin.append_right]
      by_cases h : ω j
      · rw [if_pos h, if_pos h]
      · rw [if_neg h, if_neg h, lfc_qmod_zero]
    rw [Finset.sum_congr rfl (fun i _ => e1 i),
        Finset.sum_congr rfl (fun j _ => e2 j),
        Finset.sum_congr rfl (fun j _ => e3 j)]
    ring_nf
  rw [h1, h3, h4]
  have hA : (∑ i : Fin m, u i
        * gCoeff (p:=p) c ⟨m + 1, by omega⟩ (⟨i.val, by omega⟩ : Fin (k - 1)))
      = (∑ i : Fin m, qmod p (gRho (p:=p) c m hm i) * u i) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [gCoeff_eq_gRho (p:=p) c m hm i]
    ring
  have hB : (∑ j : Fin N, W j
        * gCoeff (p:=p) c ⟨m + 1, by omega⟩ (⟨m + 1 + j.val, by omega⟩ : Fin (k - 1)))
      = (∑ j : Fin N, (if ω j then 0 else qmod p (gSig (p:=p) c m hm j)) * a j)
        + (∑ j : Fin N, (if ω j then qmod p (gSig (p:=p) c m hm j) else 0) * b j) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [gCoeff_eq_gSig (p:=p) c m hm j]
    simp only [hW]
    by_cases h : ω j <;> simp [h, mul_comm]
  rw [hA, hB, gCoeff_eq_gC (p:=p) c m hm z0]
  ring

theorem lfc_Pm_le_inj {p : ℕ} [Fact p.Prime] {k : ℕ} (hk : 3 ≤ k) {ν : ZMod p → ℝ} {ε : ℝ}
    (c : Fin k → ℤ) (K : ℕ) (hcb : ∀ m, (c m).natAbs ≤ K)
    (hinj : Function.Injective (fun m : Fin k => ((c m : ℤ) : ZMod p)))
    (hcne : ∀ m : Fin k, 1 ≤ m.val → c m ≠ 0)
    (hLFC : Commons.NumberTheory.Sieve.LinFormsCond p ν (2 ^ (k-1)) (2 * k - 4) (2 * K * K + 2) ε) :
    ∀ i ∈ Finset.range (k-1),
      GVNW.Pm (ZMod p) k (fun ii y => ∑ t : Fin (k-1),
          (1 - ((c ii : ℤ) : ZMod p)
            * (((c ⟨t.val+1, by have := t.isLt; omega⟩ : ℤ) : ZMod p))⁻¹) * y t) ν i
        ≤ 1 + ε := by
  intro i hi
  rw [Finset.mem_range] at hi
  have hik : i + 1 < k := by omega
  have hm2 : i + 2 ≤ k := by omega
  have hinjZ : ∀ a b : Fin k, a ≠ b → c a ≠ c b := by
    intro a b hab hcab
    exact hab (hinj (by show ((c a : ℤ) : ZMod p) = ((c b : ℤ) : ZMod p); rw [hcab]))
  rw [GVNW.Pm, dif_pos hik, GVNgen.av]
  let N := k - 1 - (i + 1)
  let t := i + (N + N)
  have hNz : N = k - 1 - (i + 1) := rfl
  have htz : t = i + (N + N) := rfl
  set z0 : ZMod p := Classical.arbitrary (ZMod p) with hz0
  change ((Fintype.card ((Fin i → ZMod p) × ((Fin N → ZMod p) × (Fin N → ZMod p)))) : ℝ)⁻¹
      * (∑ r : (Fin i → ZMod p) × ((Fin N → ZMod p) × (Fin N → ZMod p)),
          ∏ ω : Fin N → Bool, ν (gphi (p:=p) c ⟨i + 1, hik⟩
            (GVNgen.app k (i + 1) (by omega) (Fin.snoc r.1 z0)
              (fun j => if ω j then r.2.2 j else r.2.1 j)))) ≤ 1 + ε
  have hcardℕ : Fintype.card ((Fin i → ZMod p) × ((Fin N → ZMod p) × (Fin N → ZMod p)))
      = Fintype.card (Fin t → ZMod p) := Fintype.card_congr (lfc_epEquiv (p:=p) i N)
  have hcard : (Fintype.card ((Fin i → ZMod p) × ((Fin N → ZMod p) × (Fin N → ZMod p))) : ℝ)
      = (Fintype.card (Fin t → ZMod p) : ℝ) := by rw [hcardℕ]
  have hG : ∀ r : (Fin i → ZMod p) × ((Fin N → ZMod p) × (Fin N → ZMod p)),
      (∏ ω : Fin N → Bool, ν (gphi (p:=p) c ⟨i + 1, hik⟩
        (GVNgen.app k (i+1) (by omega) (Fin.snoc r.1 z0)
          (fun j => if ω j then r.2.2 j else r.2.1 j))))
      = ∏ ω : Fin N → Bool, ν (linForm p (gL (p:=p) c i hm2 ω) (gCp (p:=p) c i hm2 z0)
          (lfc_epEquiv (p:=p) i N r)) := by
    intro r
    obtain ⟨u, a, b⟩ := r
    apply Finset.prod_congr rfl
    intro ω _
    congr 1
    exact g_pointwise (p:=p) (c:=c) (m:=i) hm2 u z0 a b ω
  have hsum : (∑ r : (Fin i → ZMod p) × ((Fin N → ZMod p) × (Fin N → ZMod p)),
      ∏ ω : Fin N → Bool, ν (gphi (p:=p) c ⟨i + 1, hik⟩
        (GVNgen.app k (i+1) (by omega) (Fin.snoc r.1 z0)
          (fun j => if ω j then r.2.2 j else r.2.1 j))))
      = ∑ x : Fin t → ZMod p, ∏ ω : Fin N → Bool,
          ν (linForm p (gL (p:=p) c i hm2 ω) (gCp (p:=p) c i hm2 z0) x) := by
    rw [Finset.sum_congr rfl (fun r _ => hG r)]
    exact Equiv.sum_comp (lfc_epEquiv (p:=p) i N)
      (fun x : Fin t → ZMod p => ∏ ω : Fin N → Bool,
        ν (linForm p (gL (p:=p) c i hm2 ω) (gCp (p:=p) c i hm2 z0) x))
  rw [hcard, hsum]
  have hcard1 : 1 ≤ Fintype.card (Fin N → Bool) := by
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]
    exact Nat.one_le_two_pow
  have hcard2 : Fintype.card (Fin N → Bool) ≤ 2 ^ (k - 1) := by
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]
    have hNle : N ≤ k - 1 := by rw [hNz]; exact Nat.sub_le _ _
    exact Nat.pow_le_pow_right (by norm_num) hNle
  have ht1 : 1 ≤ t := by rw [htz, hNz]; omega
  have ht2 : t ≤ 2 * k - 4 := by rw [htz, hNz]; omega
  have hK : 2 * K ≤ 2 * K * K + 2 := by
    rcases Nat.eq_zero_or_pos K with h | h
    · subst h; omega
    · have hle : 2 * K ≤ 2 * K * K := by
        calc 2 * K = 2 * K * 1 := by ring
          _ ≤ 2 * K * K := Nat.mul_le_mul_left _ h
      omega
  have hone : 1 ≤ 2 * K * K + 2 := by omega
  have hmain := hLFC (Fin N → Bool) hcard1 hcard2 t ht1 ht2 (gL (p:=p) c i hm2)
    (fun ω q => isSmallRat_gL (p:=p) hcb hK hone i hm2 ω q)
    (fun ω => nonzeroTuple_gL (p:=p) hk hinjZ i hm2 ω)
    (fun ω ω' hne => notProp_gL (p:=p) hinjZ i hm2 hne)
    (fun _ => gCp (p:=p) c i hm2 z0)
  have hfin := (abs_le.mp hmain).2
  linarith [hfin]



variable {p : ℕ} [Fact p.Prime]
variable {k : ℕ}

/-! ## Smallness of the coefficient family with the tight constant `K`

The coefficients of the shifted cube systems are `gBr D C = (D - C)/D` where `D`, `C` are values
of the shift family `c`.  Their reduced numerator/denominator are bounded by
`max(|D - C|, |D|)`, so the *diameter* bound `|c m - c m'| ≤ K` (together with `|c m| ≤ K`)
gives `IsSmallRat K` — exactly the parameter of Green–Tao's `k`-pseudorandomness. -/

/-- From `|a - b| ≤ K` (as integers) to the `natAbs` bound. -/
lemma natAbs_sub_le_of_abs_le {a b : ℤ} {K : ℕ} (h : |a - b| ≤ (K : ℤ)) :
    (a - b).natAbs ≤ K := by
  have h2 : (((a - b).natAbs : ℤ)) ≤ (K : ℤ) := by
    rw [Int.natCast_natAbs]; exact h
  exact_mod_cast h2

/-- `gBr D C` is `IsSmallRat K` when `|D| ≤ K` and `|D - C| ≤ K`. -/
lemma isSmallRat_gBr_diam {D C : ℤ} {K : ℕ} (hD : D.natAbs ≤ K)
    (hDC : (D - C).natAbs ≤ K) (h1 : 1 ≤ K) : IsSmallRat K (gBr (p:=p) D C) := by
  unfold gBr
  split_ifs with h
  · exact lfc_isSmallRat_one h1
  · have hDne : D ≠ 0 := by
      intro h0; apply h; rw [h0]; simp
    exact isSmallRat_divInt (L₀ := K) hDne hDC hD

lemma isSmallRat_gRho_diam {c : Fin k → ℤ} {K : ℕ}
    (hcb : ∀ n, (c n).natAbs ≤ K) (hdiam : ∀ m m', |c m - c m'| ≤ (K : ℤ)) (h1 : 1 ≤ K)
    (m : ℕ) (hm : m + 2 ≤ k) (i : Fin m) :
    IsSmallRat K (gRho (p:=p) c m hm i) := by
  unfold gRho
  refine isSmallRat_gBr_diam (p:=p) (hcb _) ?_ h1
  exact natAbs_sub_le_of_abs_le (hdiam _ _)

lemma isSmallRat_gSig_diam {c : Fin k → ℤ} {K : ℕ}
    (hcb : ∀ n, (c n).natAbs ≤ K) (hdiam : ∀ m m', |c m - c m'| ≤ (K : ℤ)) (h1 : 1 ≤ K)
    (m : ℕ) (hm : m + 2 ≤ k) (j : Fin (k - 1 - (m + 1))) :
    IsSmallRat K (gSig (p:=p) c m hm j) := by
  unfold gSig
  refine isSmallRat_gBr_diam (p:=p) (hcb _) ?_ h1
  exact natAbs_sub_le_of_abs_le (hdiam _ _)

lemma isSmallRat_gL_diam {c : Fin k → ℤ} {K : ℕ}
    (hcb : ∀ n, (c n).natAbs ≤ K) (hdiam : ∀ m m', |c m - c m'| ≤ (K : ℤ)) (h1 : 1 ≤ K)
    (m : ℕ) (hm : m + 2 ≤ k) (ω : Fin (k - 1 - (m + 1)) → Bool) :
    ∀ q : Fin (m + ((k - 1 - (m + 1)) + (k - 1 - (m + 1)))),
      IsSmallRat K (gL (p:=p) c m hm ω q) := by
  intro q
  revert q
  refine fun q => Fin.addCases
    (motive := fun q => IsSmallRat K (gL (p:=p) c m hm ω q)) ?_ ?_ q
  · intro i
    rw [gL, Fin.append_left]
    exact isSmallRat_gRho_diam (p:=p) hcb hdiam h1 m hm i
  · intro q
    revert q
    refine fun q => Fin.addCases
      (motive := fun q => IsSmallRat K (gL (p:=p) c m hm ω (Fin.natAdd m q))) ?_ ?_ q
    · intro j
      rw [gL, Fin.append_right, Fin.append_left]
      by_cases h : ω j
      · rw [if_pos h]; exact lfc_isSmallRat_zero h1
      · rw [if_neg h]; exact isSmallRat_gSig_diam (p:=p) hcb hdiam h1 m hm j
    · intro j
      rw [gL, Fin.append_right, Fin.append_right]
      by_cases h : ω j
      · rw [if_pos h]; exact isSmallRat_gSig_diam (p:=p) hcb hdiam h1 m hm j
      · rw [if_neg h]; exact lfc_isSmallRat_zero h1

/-- `K ≥ 1` follows from injectivity of the shift family when `k ≥ 2`. -/
lemma one_le_of_shift_inj {c : Fin k → ℤ} {K : ℕ} (hk : 2 ≤ k)
    (hcb : ∀ m, (c m).natAbs ≤ K)
    (hinj : Function.Injective (fun m : Fin k => ((c m : ℤ) : ZMod p))) : 1 ≤ K := by
  by_contra h
  have hK0 : K = 0 := by omega
  have hzero : ∀ m : Fin k, c m = 0 := by
    intro m
    have hh : (c m).natAbs ≤ 0 := by simpa [hK0] using hcb m
    exact Int.natAbs_eq_zero.mp (Nat.le_zero.mp hh)
  have hlt1 : 1 < k := by omega
  have hne : (⟨0, by omega⟩ : Fin k) ≠ (⟨1, hlt1⟩ : Fin k) := by
    intro hc; have := congrArg Fin.val hc; simp at this
  exact hne (hinj (by simp [hzero]))

theorem lfc_Pm_le_shift2 {p : ℕ} [Fact p.Prime] {k : ℕ} (hk : 3 ≤ k) {ν : ZMod p → ℝ} {ε : ℝ}
    (c : Fin k → ℤ) (K : ℕ) (hcb : ∀ m, (c m).natAbs ≤ K)
    (hdiam : ∀ m m', |c m - c m'| ≤ K)
    (hinj : Function.Injective (fun m : Fin k => ((c m : ℤ) : ZMod p)))
    (hcne : ∀ m : Fin k, 1 ≤ m.val → c m ≠ 0)
    (hLFC : Commons.NumberTheory.Sieve.LinFormsCond p ν (2 ^ (k-1)) (2 * k - 4) K ε) :
    ∀ i ∈ Finset.range (k-1),
      GVNW.Pm (ZMod p) k (fun ii y => ∑ t : Fin (k-1),
          (1 - ((c ii : ℤ) : ZMod p)
            * (((c ⟨t.val+1, by have := t.isLt; omega⟩ : ℤ) : ZMod p))⁻¹) * y t) ν i
        ≤ 1 + ε := by
  have hK1 : 1 ≤ K := one_le_of_shift_inj (p:=p) (c:=c) (by omega) hcb hinj
  intro i hi
  rw [Finset.mem_range] at hi
  have hik : i + 1 < k := by omega
  have hm2 : i + 2 ≤ k := by omega
  have hinjZ : ∀ a b : Fin k, a ≠ b → c a ≠ c b := by
    intro a b hab hcab
    exact hab (hinj (by show ((c a : ℤ) : ZMod p) = ((c b : ℤ) : ZMod p); rw [hcab]))
  rw [GVNW.Pm, dif_pos hik, GVNgen.av]
  let N := k - 1 - (i + 1)
  let t := i + (N + N)
  have hNz : N = k - 1 - (i + 1) := rfl
  have htz : t = i + (N + N) := rfl
  set z0 : ZMod p := Classical.arbitrary (ZMod p) with hz0
  change ((Fintype.card ((Fin i → ZMod p) × ((Fin N → ZMod p) × (Fin N → ZMod p)))) : ℝ)⁻¹
      * (∑ r : (Fin i → ZMod p) × ((Fin N → ZMod p) × (Fin N → ZMod p)),
          ∏ ω : Fin N → Bool, ν (gphi (p:=p) c ⟨i + 1, hik⟩
            (GVNgen.app k (i + 1) (by omega) (Fin.snoc r.1 z0)
              (fun j => if ω j then r.2.2 j else r.2.1 j)))) ≤ 1 + ε
  have hcardℕ : Fintype.card ((Fin i → ZMod p) × ((Fin N → ZMod p) × (Fin N → ZMod p)))
      = Fintype.card (Fin t → ZMod p) := Fintype.card_congr (lfc_epEquiv (p:=p) i N)
  have hcard : (Fintype.card ((Fin i → ZMod p) × ((Fin N → ZMod p) × (Fin N → ZMod p))) : ℝ)
      = (Fintype.card (Fin t → ZMod p) : ℝ) := by rw [hcardℕ]
  have hG : ∀ r : (Fin i → ZMod p) × ((Fin N → ZMod p) × (Fin N → ZMod p)),
      (∏ ω : Fin N → Bool, ν (gphi (p:=p) c ⟨i + 1, hik⟩
        (GVNgen.app k (i+1) (by omega) (Fin.snoc r.1 z0)
          (fun j => if ω j then r.2.2 j else r.2.1 j))))
      = ∏ ω : Fin N → Bool, ν (linForm p (gL (p:=p) c i hm2 ω) (gCp (p:=p) c i hm2 z0)
          (lfc_epEquiv (p:=p) i N r)) := by
    intro r
    obtain ⟨u, a, b⟩ := r
    apply Finset.prod_congr rfl
    intro ω _
    congr 1
    exact g_pointwise (p:=p) (c:=c) (m:=i) hm2 u z0 a b ω
  have hsum : (∑ r : (Fin i → ZMod p) × ((Fin N → ZMod p) × (Fin N → ZMod p)),
      ∏ ω : Fin N → Bool, ν (gphi (p:=p) c ⟨i + 1, hik⟩
        (GVNgen.app k (i+1) (by omega) (Fin.snoc r.1 z0)
          (fun j => if ω j then r.2.2 j else r.2.1 j))))
      = ∑ x : Fin t → ZMod p, ∏ ω : Fin N → Bool,
          ν (linForm p (gL (p:=p) c i hm2 ω) (gCp (p:=p) c i hm2 z0) x) := by
    rw [Finset.sum_congr rfl (fun r _ => hG r)]
    exact Equiv.sum_comp (lfc_epEquiv (p:=p) i N)
      (fun x : Fin t → ZMod p => ∏ ω : Fin N → Bool,
        ν (linForm p (gL (p:=p) c i hm2 ω) (gCp (p:=p) c i hm2 z0) x))
  rw [hcard, hsum]
  have hcard1 : 1 ≤ Fintype.card (Fin N → Bool) := by
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]
    exact Nat.one_le_two_pow
  have hcard2 : Fintype.card (Fin N → Bool) ≤ 2 ^ (k - 1) := by
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]
    have hNle : N ≤ k - 1 := by rw [hNz]; exact Nat.sub_le _ _
    exact Nat.pow_le_pow_right (by norm_num) hNle
  have ht1 : 1 ≤ t := by rw [htz, hNz]; omega
  have ht2 : t ≤ 2 * k - 4 := by rw [htz, hNz]; omega
  have hmain := hLFC (Fin N → Bool) hcard1 hcard2 t ht1 ht2 (gL (p:=p) c i hm2)
    (fun ω q => isSmallRat_gL_diam (p:=p) hcb hdiam hK1 i hm2 ω q)
    (fun ω => nonzeroTuple_gL (p:=p) hk hinjZ i hm2 ω)
    (fun ω ω' hne => notProp_gL (p:=p) hinjZ i hm2 hne)
    (fun _ => gCp (p:=p) c i hm2 z0)
  have hfin := (abs_le.mp hmain).2
  linarith [hfin]


end LFCPmCopy
