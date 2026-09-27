-- Verbatim copy of `Submission.Work.Mostow.margulisPigeonhole` (proved by a colleague of the
-- `margulisCusp` team), kept in a private namespace and with the single import
-- `Submission.Work.Mostow.poTransitive` removed: that module pulls in `visualDefs`, which
-- declares `Work.Mostow.wvec`, a name that clashes with the `wvec` of `QIDefs` (needed here for
-- `finite_nearStab`).  The removed import is not used by the proof.
import Mathlib
import Submission.Work.Mostow.margulisCuspDefs
import Submission.Work.Mostow.Margulis.exists_pair_dist_le_bdd
import Submission.Work.Mostow.Margulis.exists_pow_near_fix_zero
import Submission.Work.Mostow.Margulis.near1_conj_pow
import Submission.Work.Mostow.Margulis.exists_boost_near
import Submission.Work.Mostow.BoostTransitive

/-!
# The Margulis pigeonhole for `PO(n,1)`

For every tolerance `η > 0` there is a bound `N` and a radius `ε₀ > 0` such that every
isometry `g` of `ℍⁿ` which moves the base point `0` by less than `ε₀` has a power `g ^ m`,
`0 < m ≤ N`, whose sheet-preserving lift `ToO (g ^ m)` is entrywise within `η` of the
identity matrix.

The proof decomposes `g = b * k`, where `b` is the boost along the geodesic from `0` to
`g • 0` (so `k` fixes `0`), uses the compact-stabiliser pigeonhole
`Margulis.exists_pow_near_fix_zero` to find a bounded power of `k` close to the identity,
and controls the remaining product of `m` small boosts by the entrywise near-identity
estimates of `margulisPair`/`near1_conj_pow`.
-/

namespace Work.Mostow.CuspPig

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory Matrix

noncomputable section

variable {n : ℕ}

/-! ## Elementary `Near1` estimates -/

theorem near1_mono {A : O1 n} {s t : ℝ} (h : Near1 A s) (hst : s ≤ t) : Near1 A t :=
  fun i j => le_trans (h i j) hst

/-- A recursive finite product in a monoid. -/
def prodR {M : Type*} [Monoid M] (F : ℕ → M) : ℕ → M
  | 0 => 1
  | (m + 1) => prodR F m * F m

@[simp] lemma prodR_zero {M : Type*} [Monoid M] (F : ℕ → M) : prodR F 0 = 1 := rfl

@[simp] lemma prodR_succ {M : Type*} [Monoid M] (F : ℕ → M) (m : ℕ) :
    prodR F (m + 1) = prodR F m * F m := rfl

/-- A product of `m` matrices, each within `q` of the identity, is within
`(1 + msz n * q) ^ m - 1` of the identity. -/
lemma near1_prodR (F : ℕ → O1 n) (q : ℝ) (hq : 0 ≤ q) (hF : ∀ j, Near1 (F j) q) :
    ∀ m : ℕ, Near1 (prodR F m) ((1 + msz n * q) ^ m - 1) := by
  intro m
  induction m with
  | zero => simpa using near1_one
  | succ m ih =>
      rw [prodR_succ]
      have hstep := near1_mul' ih (hF m)
      have hc : q ≤ msz n * q := by nlinarith [hq, one_le_msz (n := n)]
      have heq : (1 + msz n * q) ^ (m + 1) - 1
          = msz n * ((1 + msz n * q) ^ m - 1) * q + ((1 + msz n * q) ^ m - 1)
            + (msz n * q) := by
        rw [pow_succ]; ring
      refine fun i j => le_trans (hstep i j) ?_
      rw [heq]
      linarith [hc]

/-- The binomial-type bound `(1 + y) ^ m ≤ 1 + (2 ^ m - 1) * y` for `0 ≤ y ≤ 1`. -/
lemma pow_le_one_add (m : ℕ) {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    (1 + y) ^ m ≤ 1 + ((2 : ℝ) ^ m - 1) * y := by
  induction m with
  | zero => norm_num
  | succ k ih =>
      have hz : (1 : ℝ) ≤ (2 : ℝ) ^ k := one_le_pow₀ (by norm_num)
      have h2 : (0 : ℝ) ≤ (2 : ℝ) ^ k - 1 := by linarith
      have hy2 : y * y ≤ y := by nlinarith
      have hexp : (1 + ((2 : ℝ) ^ k - 1) * y) * (1 + y)
          = 1 + ((2 : ℝ) ^ k) * y + ((2 : ℝ) ^ k - 1) * (y * y) := by ring
      have h2k : (2 : ℝ) ^ (k + 1) = 2 * (2 : ℝ) ^ k := by rw [pow_succ]; ring
      rw [pow_succ]
      calc (1 + y) ^ k * (1 + y)
          ≤ (1 + ((2 : ℝ) ^ k - 1) * y) * (1 + y) :=
            mul_le_mul_of_nonneg_right ih (by linarith)
        _ = 1 + ((2 : ℝ) ^ k) * y + ((2 : ℝ) ^ k - 1) * (y * y) := hexp
        _ ≤ 1 + ((2 : ℝ) ^ k) * y + ((2 : ℝ) ^ k - 1) * y := by
            have := mul_le_mul_of_nonneg_left hy2 h2; linarith
        _ = 1 + ((2 : ℝ) ^ (k + 1) - 1) * y := by rw [h2k]; ring

/-- The geometric-series identity `(b * k) ^ m = (∏_{j<m} k^j b k^{-j}) * k^m`. -/
def cprod {G : Type*} [Group G] (b k : G) : ℕ → G
  | 0 => 1
  | (m + 1) => cprod b k m * (k ^ m * b * (k ^ m)⁻¹)

@[simp] lemma cprod_zero {G : Type*} [Group G] (b k : G) : cprod b k 0 = 1 := rfl

@[simp] lemma cprod_succ {G : Type*} [Group G] (b k : G) (m : ℕ) :
    cprod b k (m + 1) = cprod b k m * (k ^ m * b * (k ^ m)⁻¹) := rfl

lemma pow_eq_cprod {G : Type*} [Group G] (b k : G) (m : ℕ) :
    (b * k) ^ m = cprod b k m * k ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [pow_succ, ih, cprod_succ, pow_succ]
      group

/-! ## The sheet-preserving lift `ToO` -/

/-- `ToO` is multiplicative on powers. -/
lemma ToO_pow (hA : POActionProp n) (g : PO n 1) (m : ℕ) : ToO (g ^ m) = (ToO g) ^ m := by
  induction m with
  | zero => simpa using ToO_one hA
  | succ m ih => rw [pow_succ, ToO_mul hA, ih, pow_succ]

/-- If `k` fixes the base point then so does its sheet-preserving lift. -/
lemma actO_ToO_fix (hA : POActionProp n) {k : PO n 1} (hk : k • (0 : E n) = 0) :
    actO (ToO k) (0 : E n) = 0 := by
  rw [actO, mat_ToO]
  have hts : tsign (ToO k) = 1 := by
    rw [tsign_eq_one_iff, mat_ToO, LambdaMat, Matrix.smul_apply, smul_eq_mul,
      tsign_mul_time_entry]
    exact abs_pos.mpr (O1_tt_ne_zero (Quotient.out k))
  have hh : Matrix.mulVec (LambdaMat k) (hlift (0 : E n)) = hlift (0 : E n) := by
    rw [← hlift_LambdaMat hA k 0, hk]
  simp only [hts, one_mul, hh]
  ext i
  simp [hlift_zero]

/-- The sheet-preserving lift of the class of a matrix with positive time-time entry is that
matrix. -/
lemma ToO_of_rep_pos (hA : POActionProp n) {A : O1 n}
    (hApos : 0 < mat A (Sum.inr 0) (Sum.inr 0)) : ToO ((A : PO n 1)) = A := by
  apply O1.mat_injective
  rw [mat_ToO]
  set o : O1 n := Quotient.out ((A : PO n 1)) with ho
  have hcoe : ((o : O1 n) : PO n 1) = ((A : O1 n) : PO n 1) := by
    rw [ho]; exact Quotient.out_eq' _
  have hmem : o⁻¹ * A ∈ Subgroup.center (O1 n) := QuotientGroup.eq.mp hcoe
  rw [LambdaMat, ← ho]
  rcases (hA.1 _).mp hmem with h1 | h1
  · have hout : o = A := by
      have h2 : o * (o⁻¹ * A) = o * 1 := by rw [h1]
      rw [mul_inv_cancel_left, mul_one] at h2
      exact h2.symm
    rw [hout, show tsign A = 1 from (tsign_eq_one_iff A).mpr hApos, one_smul]
  · have hout : o = -A := by
      have h2 : o * (o⁻¹ * A) = o * (-1) := by rw [h1]
      rw [mul_inv_cancel_left, O1_mul_neg_one] at h2
      rw [h2, neg_neg]
    rw [hout]
    have htsneg : tsign (-A : O1 n) = -1 := by
      rw [tsign]
      rw [if_neg]
      rw [mat_neg, Matrix.neg_apply]
      linarith
    rw [htsneg, neg_one_smul, mat_neg, neg_neg]

/-- The lift of the telescoping product `cprod`. -/
lemma ToO_cprod (hA : POActionProp n) (b k : PO n 1) (m : ℕ) :
    ToO (cprod b k m)
      = prodR (fun j => (ToO k) ^ j * ToO b * ((ToO k) ^ j)⁻¹) m := by
  induction m with
  | zero => simp [cprod, ToO_one hA]
  | succ m ih =>
      have h1 : ToO (k ^ m * b * (k ^ m)⁻¹)
          = (ToO k) ^ m * ToO b * ((ToO k) ^ m)⁻¹ := by
        rw [ToO_mul hA, ToO_mul hA, ToO_inv hA, ToO_pow hA]
      rw [cprod_succ, prodR_succ, ToO_mul hA, h1, ih]

/-! ## The main theorem -/

theorem margulisPigeonhole (n : ℕ) (hA : Submission.Mostow.POActionProp n)
    (hI : Submission.Mostow.HypIsometryProp n) :
    ∀ η : ℝ, 0 < η → ∃ N : ℕ, 0 < N ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ g : LeanEval.Geometry.MostowRigidity.PO n 1,
        Submission.Mostow.hdist (0 : Submission.Mostow.E n) (g • (0 : Submission.Mostow.E n)) < ε₀ →
        ∃ m : ℕ, 0 < m ∧ m ≤ N ∧ Work.Mostow.Near1 (Work.Mostow.ToO (g ^ m)) η := by
  intro η hη
  have hmsz : 0 < msz n := lt_of_lt_of_le zero_lt_one (one_le_msz n)
  -- the near-identity tolerance used both for the rotation part and for the boost product
  set T : ℝ := min (η / 4) (1 / (4 * msz n)) with hTdef
  have hTpos : 0 < T := by
    rw [hTdef]; exact lt_min (by linarith) (by positivity)
  have hTeta : T ≤ η / 4 := by rw [hTdef]; exact min_le_left _ _
  have hTinv : T ≤ 1 / (4 * msz n) := by rw [hTdef]; exact min_le_right _ _
  have hT4 : T ≤ 1 / 4 := by
    refine le_trans hTinv ?_
    have h44 : (4 : ℝ) ≤ 4 * msz n := by linarith [one_le_msz (n := n)]
    simpa using one_div_le_one_div_of_le (show (0 : ℝ) < 4 by norm_num) h44
  -- the compact-stabiliser pigeonhole
  obtain ⟨N₁, hN₁, hEPZ⟩ := Margulis.exists_pow_near_fix_zero n T hTpos
  -- a bound for the (conjugated) boost factors
  set C : ℝ := 3 * (msz n) ^ 2 with hCdef
  have hCpos : 0 < C := by rw [hCdef]; positivity
  have hLpos : 0 < msz n * C := mul_pos hmsz hCpos
  -- choose the radius so that `N₁` boost factors of that size remain within `T`
  obtain ⟨δ, hδpos, hδle⟩ : ∃ δ : ℝ, 0 < δ ∧ (1 + msz n * C * δ) ^ N₁ - 1 ≤ T := by
    have h2N : (0 : ℝ) < (2 : ℝ) ^ N₁ - 1 := by
      have h : (2 : ℝ) ^ 1 ≤ (2 : ℝ) ^ N₁ := pow_le_pow_right₀ (by norm_num) hN₁
      norm_num at h ⊢
      linarith
    refine ⟨T / (((2 : ℝ) ^ N₁ - 1) * (msz n * C)), ?_, ?_⟩
    · exact div_pos hTpos (mul_pos h2N hLpos)
    · have hval : msz n * C * (T / (((2 : ℝ) ^ N₁ - 1) * (msz n * C)))
          = T / ((2 : ℝ) ^ N₁ - 1) := by
        field_simp
      rw [hval]
      have hy0 : 0 ≤ T / ((2 : ℝ) ^ N₁ - 1) := le_of_lt (div_pos hTpos h2N)
      have h2N1 : (1 : ℝ) ≤ (2 : ℝ) ^ N₁ - 1 := by
        have h : (2 : ℝ) ^ 1 ≤ (2 : ℝ) ^ N₁ := pow_le_pow_right₀ (by norm_num) hN₁
        norm_num at h ⊢
        linarith
      have hy1 : T / ((2 : ℝ) ^ N₁ - 1) ≤ 1 := by
        rw [div_le_one (by linarith)]
        linarith [hT4, h2N1]
      have hpow := pow_le_one_add N₁ hy0 hy1
      have hmul : ((2 : ℝ) ^ N₁ - 1) * (T / ((2 : ℝ) ^ N₁ - 1)) = T := by field_simp
      linarith [hpow]
  set ε₀ : ℝ := min (1 / 3) δ with hεdef
  have hεpos : 0 < ε₀ := by rw [hεdef]; exact lt_min (by norm_num) hδpos
  have hεδ : ε₀ ≤ δ := by rw [hεdef]; exact min_le_right _ _
  have hε3 : ε₀ ≤ 1 / 3 := by rw [hεdef]; exact min_le_left _ _
  refine ⟨N₁, hN₁, ε₀, hεpos, ?_⟩
  intro g hg
  set d : ℝ := hdist (0 : E n) (g • (0 : E n)) with hd
  have hdε : d < ε₀ := hg
  have hd1 : d ≤ 1 := by linarith [hε3]
  -- boost through the displacement point
  obtain ⟨B, hB0, hBnear⟩ :=
    Margulis.exists_boost_near n (g • (0 : E n)) (by rw [← hd]; linarith)
  have hBtpos : 0 < mat B (Sum.inr 0) (Sum.inr 0) := by
    have h := hBnear (Sum.inr 0) (Sum.inr 0)
    rw [dE_self] at h
    have h3 : (3 : ℝ) * d < 1 := by linarith [hdε, hε3]
    have := (abs_le.mp h).1
    linarith
  set b : PO n 1 := (B : PO n 1) with hb
  have hTob : ToO b = B := by rw [hb]; exact ToO_of_rep_pos hA hBtpos
  have hBb : Near1 (ToO b) (3 * d) := by
    rw [hTob, hd]; exact hBnear
  have hb0 : b • (0 : E n) = g • (0 : E n) := by
    rw [hb, hA.2.1 B 0]; exact hB0
  -- the rotation part
  set k : PO n 1 := b⁻¹ * g with hk
  have hk0 : k • (0 : E n) = 0 := by
    rw [hk]
    have h1 : (b⁻¹ * g) • (0 : E n) = b⁻¹ • (g • (0 : E n)) := hA.2.2.2.2.1 b⁻¹ g 0
    rw [h1, ← hb0]
    have h2 : b⁻¹ • (b • (0 : E n)) = (b⁻¹ * b) • (0 : E n) :=
      (hA.2.2.2.2.1 b⁻¹ b 0).symm
    rw [h2, inv_mul_cancel, hA.2.2.2.1]
  have hTOk : actO (ToO k) (0 : E n) = 0 := actO_ToO_fix hA hk0
  obtain ⟨m, hmpos, hmle, hmnear⟩ := hEPZ (ToO k) hTOk
  refine ⟨m, hmpos, hmle, ?_⟩
  -- `g ^ m = (∏_{j<m} k^j b k^{-j}) * k^m`
  have hbk : b * k = g := by rw [hk, mul_inv_cancel_left]
  have hgpow : g ^ m = cprod b k m * k ^ m := by
    rw [← hbk]; exact pow_eq_cprod b k m
  have hToOg : ToO (g ^ m) = ToO (cprod b k m) * ToO (k ^ m) := by
    rw [hgpow, ToO_mul hA]
  have hknear : Near1 ((ToO k) ^ m) T := hmnear
  -- the boost product
  have hfactor : ∀ j : ℕ, Near1 ((ToO k) ^ j * ToO b * ((ToO k) ^ j)⁻¹) (C * ε₀) := by
    intro j
    have hj := Margulis.near1_conj_pow n (ToO k) (ToO b) (3 * d) j hTOk hBb
    refine near1_mono hj ?_
    have hm2 : (0 : ℝ) ≤ (msz n) ^ 2 := sq_nonneg _
    rw [hCdef]
    nlinarith [hdε, hm2]
  have hprod : Near1 (ToO (cprod b k m)) T := by
    rw [ToO_cprod hA b k m]
    have hq : 0 ≤ C * ε₀ := le_of_lt (mul_pos hCpos hεpos)
    have h := near1_prodR (fun j => (ToO k) ^ j * ToO b * ((ToO k) ^ j)⁻¹) (C * ε₀) hq hfactor m
    refine near1_mono h ?_
    have hbase : 0 ≤ 1 + msz n * (C * ε₀) := by positivity
    have hmono : 1 + msz n * (C * ε₀) ≤ 1 + msz n * C * δ := by
      have hCδ : 0 ≤ C * δ := le_of_lt (mul_pos hCpos hδpos)
      nlinarith [hεδ, hCδ, hmsz]
    have h1 : (1 : ℝ) ≤ 1 + msz n * C * δ := by
      have : 0 ≤ msz n * C * δ := le_of_lt (mul_pos hLpos hδpos)
      linarith
    calc (1 + msz n * (C * ε₀)) ^ m - 1
        ≤ (1 + msz n * C * δ) ^ m - 1 := by
          have h2 := pow_le_pow_left₀ hbase hmono m; linarith
      _ ≤ (1 + msz n * C * δ) ^ N₁ - 1 := by
          have h3 := pow_le_pow_right₀ h1 hmle; linarith
      _ ≤ T := hδle
  -- assembly
  have hfinal : Near1 (ToO (g ^ m)) (msz n * T * T + T + T) := by
    rw [hToOg, ToO_pow hA]
    exact near1_mul' hprod hknear
  refine near1_mono hfinal ?_
  have h1 : msz n * T ≤ 1 / 4 := by
    calc msz n * T ≤ msz n * (1 / (4 * msz n)) := mul_le_mul_of_nonneg_left hTinv (le_of_lt hmsz)
      _ = 1 / 4 := by field_simp
  have h2 : msz n * T * T ≤ (1 / 4) * T := by nlinarith [h1, hTpos]
  have h3 : (1 / 4) * T ≤ η / 16 := by nlinarith [hTeta]
  linarith [h2, h3, hTeta, hη]

end

end Work.Mostow.CuspPig
