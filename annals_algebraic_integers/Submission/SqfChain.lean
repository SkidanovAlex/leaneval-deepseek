import Mathlib
import Submission.GcdInt

/-!
# Canonical prefix gcd chain for a family of integer polynomials

Given a family `Q : Fin (n+1) → Polynomial ℤ` of nonzero members, and an
index `j ≤ n`, let `G_j` be the gcd of the first `j+1` members
(`Q (emb j hj i)`, `i : Fin (j+1)`), `S_j i` the (unique) quotient
`Q(emb i) = G_j · S_j i` in `ℤ[X]`, and `m_j` the maximal degree of the
quotients `S_j i`.  This module records all the facts needed by the
squarefree assembly (Theorem squarefree): `G_j ≠ 0`, quotients without
common complex roots, `j ≤ m_j ≤ n` (from ℚ-linear independence of `Q` and
degree bounds), monotonicity `m_j ≤ m_{j+1}`, and the degree-of-`G_j` bound
`deg G_j + m_j ≤ n`.
-/

noncomputable section
open Polynomial
open scoped BigOperators

namespace Submission.SqfChain

open Submission.GcdInt

/-- The natural embedding of `Fin (j+1)` into `Fin (n+1)` for `j ≤ n`. -/
def emb {n j : ℕ} (hj : j ≤ n) : Fin (j + 1) → Fin (n + 1) := fun i => ⟨i.val, by omega⟩

/-- The gcd of the first `j+1` members. -/
noncomputable def gJ {n j : ℕ} (Q : Fin (n + 1) → Polynomial ℤ) (hj : j ≤ n) : Polynomial ℤ :=
  (Finset.univ : Finset (Fin (j + 1))).gcd (fun i => Q (emb hj i))

lemma gJ_dvd_emb {n j : ℕ} (Q : Fin (n + 1) → Polynomial ℤ) (hj : j ≤ n) (i : Fin (j + 1)) :
    gJ Q hj ∣ Q (emb hj i) := by
  unfold gJ
  exact Finset.gcd_dvd (s := (Finset.univ : Finset (Fin (j + 1)))) (b := i) (by simp)

/-- The quotient `Q(emb i) / G_j` in `ℤ[X]`. -/
noncomputable def sJ {n j : ℕ} (Q : Fin (n + 1) → Polynomial ℤ) (hj : j ≤ n)
    (i : Fin (j + 1)) : Polynomial ℤ :=
  Classical.choose (gJ_dvd_emb Q hj i)

/-- `Q(emb i) = G_j · S_j i`. -/
lemma sJ_div {n j : ℕ} (Q : Fin (n + 1) → Polynomial ℤ) (hj : j ≤ n) (i : Fin (j + 1)) :
    Q (emb hj i) = gJ Q hj * sJ Q hj i := by
  unfold sJ
  exact Classical.choose_spec (gJ_dvd_emb Q hj i)

/-- `G_j ≠ 0` when some member is nonzero. -/
lemma gJ_ne_zero {n j : ℕ} (Q : Fin (n + 1) → Polynomial ℤ) (hj : j ≤ n)
    (hQnz : ∀ i : Fin (n + 1), Q i ≠ 0) : gJ Q hj ≠ 0 := by
  unfold gJ
  rw [Finset.gcd_ne_zero_iff]
  refine ⟨(0 : Fin (j + 1)), by simp, ?_⟩
  simpa using hQnz (emb hj (0 : Fin (j + 1)))

/-- Every quotient is nonzero. -/
lemma sJ_ne_zero {n j : ℕ} (Q : Fin (n + 1) → Polynomial ℤ) (hj : j ≤ n)
    (hQnz : ∀ i : Fin (n + 1), Q i ≠ 0) (i : Fin (j + 1)) : sJ Q hj i ≠ 0 := by
  intro hz
  have hQi : Q (emb hj i) ≠ 0 := hQnz (emb hj i)
  have : Q (emb hj i) = 0 := by
    rw [sJ_div Q hj i, hz]
    simp
  exact hQi this

/-- `G_j` is the gcd over `ℤ`: any common ℤ-divisor divides it. -/
lemma gJ_max {n j : ℕ} (Q : Fin (n + 1) → Polynomial ℤ) (hj : j ≤ n)
    (H : Polynomial ℤ) (hH : ∀ i : Fin (j + 1), H ∣ Q (emb hj i)) : H ∣ gJ Q hj := by
  unfold gJ
  exact Finset.dvd_gcd (s := (Finset.univ : Finset (Fin (j + 1)))) (f := fun i => Q (emb hj i))
    (by intro i hi; exact hH i)

/-- The quotients `S_j i` have no common complex root. -/
lemma sJ_no_common_root {n j : ℕ} (Q : Fin (n + 1) → Polynomial ℤ) (hj : j ≤ n)
    (hQnz : ∀ i : Fin (n + 1), Q i ≠ 0) :
    ∀ z : ℂ, ¬ (∀ i : Fin (j + 1), Polynomial.aeval z (sJ Q hj i) = 0) := by
  classical
  intro z hz
  have hS0ne : sJ Q hj (0 : Fin (j + 1)) ≠ 0 := sJ_ne_zero Q hj hQnz (0 : Fin (j + 1))
  have hSmap_ne : (sJ Q hj (0 : Fin (j + 1))).map (algebraMap ℤ ℚ) ≠ 0 := by
    intro hm
    exact hS0ne (map_int_poly_injective (by simpa using hm))
  have hz0q : Polynomial.aeval z ((sJ Q hj (0 : Fin (j + 1))).map (algebraMap ℤ ℚ)) = 0 := by
    rw [aeval_int_map_aeval]
    exact hz 0
  have hzalg : IsAlgebraic ℚ z := ⟨(sJ Q hj (0 : Fin (j + 1))).map (algebraMap ℤ ℚ), hSmap_ne, hz0q⟩
  have hzint : IsIntegral ℚ z := IsAlgebraic.isIntegral hzalg
  let m : Polynomial ℚ := minpoly ℚ z
  have hm_ne : m ≠ 0 := minpoly.ne_zero hzint
  have hGmap_ne : (gJ Q hj).map (algebraMap ℤ ℚ) ≠ 0 := by
    intro hg
    exact gJ_ne_zero Q hj hQnz (map_int_poly_injective (by simpa using hg))
  have hm_dvd : ∀ i : Fin (j + 1), m ∣ (sJ Q hj i).map (algebraMap ℤ ℚ) := fun i => by
    refine minpoly.dvd ℚ z ?_
    rw [aeval_int_map_aeval]
    exact hz i
  let Hq : Polynomial ℚ := (gJ Q hj).map (algebraMap ℤ ℚ) * m
  have hHqne : Hq ≠ 0 := mul_ne_zero hGmap_ne hm_ne
  have hHqdiv : ∀ i : Fin (j + 1), Hq ∣ (Q (emb hj i)).map (algebraMap ℤ ℚ) := fun i => by
    rcases hm_dvd i with ⟨v, hv⟩
    refine ⟨v, ?_⟩
    calc
      (Q (emb hj i)).map (algebraMap ℤ ℚ) = ((gJ Q hj) * sJ Q hj i).map (algebraMap ℤ ℚ) := by
        rw [sJ_div Q hj i]
      _ = (gJ Q hj).map (algebraMap ℤ ℚ) * (sJ Q hj i).map (algebraMap ℤ ℚ) := by
        rw [Polynomial.map_mul]
      _ = (gJ Q hj).map (algebraMap ℤ ℚ) * (m * v) := by rw [hv]
      _ = ((gJ Q hj).map (algebraMap ℤ ℚ) * m) * v := by rw [mul_assoc]
  have hfinal : Hq ∣ (gJ Q hj).map (algebraMap ℤ ℚ) :=
    rat_common_divisor_dvd_int_gcd (Q := fun i : Fin (j + 1) => Q (emb hj i))
      (G := gJ Q hj) (0 : Fin (j + 1))
      (hQnz (emb hj (0 : Fin (j + 1)))) (gJ_max Q hj) Hq hHqdiv
  rcases hfinal with ⟨c, hc⟩
  have hmul1 : m * c = 1 := by
    apply mul_left_cancel₀ hGmap_ne
    calc
      (gJ Q hj).map (algebraMap ℤ ℚ) * (m * c) =
          ((gJ Q hj).map (algebraMap ℤ ℚ) * m) * c := by rw [mul_assoc]
      _ = (gJ Q hj).map (algebraMap ℤ ℚ) := hc.symm
      _ = (gJ Q hj).map (algebraMap ℤ ℚ) * 1 := by rw [mul_one]
  have hm_unit : IsUnit m := by
    exact isUnit_iff_exists_inv.mpr ⟨c, hmul1⟩
  exact (minpoly.not_isUnit ℚ z) (by simpa [m] using hm_unit)

/-- The maximal degree of the quotients `S_j i` (`i : Fin (j+1)`). -/
noncomputable def mJ {n j : ℕ} (Q : Fin (n + 1) → Polynomial ℤ) (hj : j ≤ n) : ℕ :=
  (Finset.univ : Finset (Fin (j + 1))).sup (fun i => (sJ Q hj i).natDegree)

/-- every quotient degree is at most `m_j`. -/
lemma sJ_deg_le_mJ {n j : ℕ} (Q : Fin (n + 1) → Polynomial ℤ) (hj : j ≤ n)
    (i : Fin (j + 1)) : (sJ Q hj i).natDegree ≤ mJ Q hj := by
  unfold mJ
  exact Finset.le_sup (s := (Finset.univ : Finset (Fin (j + 1))))
    (f := fun i => (sJ Q hj i).natDegree) (b := i) (by simp)

/-- The maximum is attained. -/
lemma mJ_deg_att {n j : ℕ} (Q : Fin (n + 1) → Polynomial ℤ) (hj : j ≤ n) :
    ∃ i : Fin (j + 1), (sJ Q hj i).natDegree = mJ Q hj := by
  classical
  rcases Finset.exists_mem_eq_sup (Finset.univ : Finset (Fin (j + 1))) (by simp)
    (fun i => (sJ Q hj i).natDegree) with ⟨i, _hi, h⟩
  exact ⟨i, h.symm⟩

/-- `G_j · S_j i` and `Q(emb i)` share the degree: `deg Q = deg G_j + deg S_j i`. -/
lemma deg_quot_add {n j : ℕ} (Q : Fin (n + 1) → Polynomial ℤ) (hj : j ≤ n)
    (hQnz : ∀ i : Fin (n + 1), Q i ≠ 0) (i : Fin (j + 1)) :
    (Q (emb hj i)).natDegree = (gJ Q hj).natDegree + (sJ Q hj i).natDegree := by
  have hQi : Q (emb hj i) ≠ 0 := hQnz (emb hj i)
  have hs : sJ Q hj i ≠ 0 := sJ_ne_zero Q hj hQnz i
  have hg : gJ Q hj ≠ 0 := gJ_ne_zero Q hj hQnz
  rw [sJ_div Q hj i]
  exact Polynomial.natDegree_mul hg hs

/-- `m_j ≤ n` when all members have degree `≤ n`. -/
lemma mJ_le_n {n j : ℕ} (Q : Fin (n + 1) → Polynomial ℤ) (hj : j ≤ n)
    (hQnz : ∀ i : Fin (n + 1), Q i ≠ 0)
    (hdeg : ∀ i : Fin (n + 1), (Q i).natDegree ≤ n) : mJ Q hj ≤ n := by
  classical
  rcases mJ_deg_att Q hj with ⟨i, hi⟩
  have hdegQ : (Q (emb hj i)).natDegree ≤ n := hdeg (emb hj i)
  have hdegadd := deg_quot_add Q hj hQnz i
  omega

/-- `deg G_j ≤ n − m_j` (from the degree-`n` bound on members). -/
lemma gJ_deg_le {n j : ℕ} (Q : Fin (n + 1) → Polynomial ℤ) (hj : j ≤ n)
    (hQnz : ∀ i : Fin (n + 1), Q i ≠ 0)
    (hdeg : ∀ i : Fin (n + 1), (Q i).natDegree ≤ n) :
    (gJ Q hj).natDegree ≤ n - mJ Q hj := by
  classical
  rcases mJ_deg_att Q hj with ⟨i, hi⟩
  have hdegadd := deg_quot_add Q hj hQnz i
  have hdegQ : (Q (emb hj i)).natDegree ≤ n := hdeg (emb hj i)
  omega

/-- Monotonicity: `m_j ≤ m_{j+1}`. -/
lemma mJ_mono {n j : ℕ} (Q : Fin (n + 1) → Polynomial ℤ)
    (hQnz : ∀ i : Fin (n + 1), Q i ≠ 0) (hj1 : j ≤ n) (hj2 : j + 1 ≤ n) :
    mJ Q hj1 ≤ mJ Q hj2 := by
  classical
  -- G_{j+1} divides G_j
  have hdiv : gJ Q hj2 ∣ gJ Q hj1 := by
    apply gJ_max Q hj1 (gJ Q hj2)
    intro i
    let i' : Fin (j + 2) := ⟨i.val, by omega⟩
    have hsame : emb hj1 i = emb hj2 i' := by
      ext
      simp [emb, i']
    have hGdvd : gJ Q hj2 ∣ Q (emb hj2 i') := gJ_dvd_emb Q hj2 i'
    simpa [hsame] using hGdvd
  rcases hdiv with ⟨T, hT⟩
  have hTne : T ≠ 0 := by
    intro hTz
    apply gJ_ne_zero Q hj1 hQnz
    rw [hT, hTz]
    simp
  -- for each i : Fin (j+1), S_{j+1} i' = T · S_j i
  have hsrel : ∀ i : Fin (j + 1), sJ Q hj2 (⟨i.val, by omega⟩ : Fin (j + 2)) = T * sJ Q hj1 i := by
    intro i
    let i' : Fin (j + 2) := ⟨i.val, by omega⟩
    have hQi1 : Q (emb hj1 i) = gJ Q hj1 * sJ Q hj1 i := sJ_div Q hj1 i
    have hQi2 : Q (emb hj2 i') = gJ Q hj2 * sJ Q hj2 i' := sJ_div Q hj2 i'
    have hsame : emb hj1 i = emb hj2 i' := by
      ext
      simp [emb, i']
    have hg2ne : gJ Q hj2 ≠ 0 := gJ_ne_zero Q hj2 hQnz
    apply mul_left_cancel₀ hg2ne
    calc
      gJ Q hj2 * (sJ Q hj2 i') = Q (emb hj2 i') := hQi2.symm
      _ = Q (emb hj1 i) := by rw [← hsame]
      _ = gJ Q hj1 * sJ Q hj1 i := hQi1
      _ = (gJ Q hj2 * T) * sJ Q hj1 i := by rw [hT]
      _ = gJ Q hj2 * (T * sJ Q hj1 i) := by rw [mul_assoc]
  -- degrees: deg(S_{j+1} i') ≥ deg(S_j i)
  have hle_i : ∀ i : Fin (j + 1),
      (sJ Q hj1 i).natDegree ≤ (sJ Q hj2 (⟨i.val, by omega⟩ : Fin (j + 2))).natDegree := by
    intro i
    have hs1ne : sJ Q hj1 i ≠ 0 := sJ_ne_zero Q hj1 hQnz i
    calc
      (sJ Q hj1 i).natDegree ≤ T.natDegree + (sJ Q hj1 i).natDegree := by omega
      _ = (T * sJ Q hj1 i).natDegree := (Polynomial.natDegree_mul hTne hs1ne).symm
      _ = (sJ Q hj2 (⟨i.val, by omega⟩ : Fin (j + 2))).natDegree := by rw [hsrel i]
  -- sup over the smaller family ≤ sup over the larger
  unfold mJ
  apply Finset.sup_le (s := (Finset.univ : Finset (Fin (j + 1))))
  intro i hi
  calc
    (sJ Q hj1 i).natDegree ≤
        (sJ Q hj2 (⟨i.val, by omega⟩ : Fin (j + 2))).natDegree := hle_i i
    _ ≤ (Finset.univ : Finset (Fin (j + 2))).sup (fun i => (sJ Q hj2 i).natDegree) := by
        exact Finset.le_sup (s := (Finset.univ : Finset (Fin (j + 2))))
          (f := fun i => (sJ Q hj2 i).natDegree) (b := (⟨i.val, by omega⟩ : Fin (j + 2))) (by simp)

/-- Monotonicity iterated: `j₁ ≤ j₂` implies `m_{j₁} ≤ m_{j₂}`. -/
lemma mJ_mono_le {n : ℕ} (Q : Fin (n + 1) → Polynomial ℤ)
    (hQnz : ∀ i : Fin (n + 1), Q i ≠ 0) {j1 j2 : ℕ} (hj1 : j1 ≤ n) (hj2 : j2 ≤ n)
    (hle : j1 ≤ j2) : mJ Q hj1 ≤ mJ Q hj2 := by
  induction j2, hle using Nat.le_induction with
  | base => rfl
  | succ j hlt ih =>
      have hj2' : j + 1 ≤ n := by omega
      exact le_trans (ih (by omega)) (mJ_mono Q hQnz (by omega) hj2')

/-- polynomial ℚ-independence plus degree bound ⇒ the length-`M+1` coefficient
vectors are ℚ-independent. -/
lemma fullPoly_indep_to_vec {ι : Type*} [Fintype ι] {M : ℕ} (P : ι → Polynomial ℤ)
    (hP : LinearIndependent ℚ (fun i => (P i).map (algebraMap ℤ ℚ)))
    (hdeg : ∀ i, (P i).natDegree ≤ M) :
    LinearIndependent ℚ (fun i : ι => (fun t : Fin (M + 1) => ((P i).coeff t.val : ℚ))) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hrel
  have hcoeff : ∀ t : ℕ, (∑ i : ι, g i * ((P i).coeff t : ℚ)) = 0 := by
    intro t
    by_cases ht : t ≤ M
    · have ht1 : t < M + 1 := by omega
      have hrel' := congrFun hrel ⟨t, ht1⟩
      simpa [mul_comm, mul_left_comm, mul_assoc] using hrel'
    · have htbig : M < t := by omega
      calc
        (∑ i : ι, g i * ((P i).coeff t : ℚ)) = ∑ i : ι, g i * (0 : ℚ) := by
          apply Finset.sum_congr rfl
          intro i hi
          congr 1
          exact_mod_cast (Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (hdeg i) htbig))
        _ = 0 := by simp
  have hpoly : (∑ i : ι, g i • (P i).map (algebraMap ℤ ℚ)) = 0 := by
    ext t
    calc
      ((∑ i : ι, g i • (P i).map (algebraMap ℤ ℚ)).coeff t)
          = ∑ i : ι, g i * ((P i).coeff t : ℚ) := by
              simp [Polynomial.coeff_map]
      _ = 0 := hcoeff t
  exact (Fintype.linearIndependent_iff.mp hP) g hpoly

/-- `j ≤ m_j` when the first `j+1` members are ℚ-independent. -/
lemma mJ_ge_j {n j : ℕ} (Q : Fin (n + 1) → Polynomial ℤ) (hj : j ≤ n)
    (hQnz : ∀ i : Fin (n + 1), Q i ≠ 0)
    (hQlin : LinearIndependent ℚ (fun i : Fin (j + 1) =>
      (Q (emb hj i)).map (algebraMap ℤ ℚ))) : j ≤ mJ Q hj := by
  classical
  -- S_j family is ℚ-independent as polynomials
  have hSlin : LinearIndependent ℚ (fun i : Fin (j + 1) =>
      (sJ Q hj i).map (algebraMap ℤ ℚ)) := by
    rw [Fintype.linearIndependent_iff]
    intro g hrel
    have hGmap_ne : (gJ Q hj).map (algebraMap ℤ ℚ) ≠ 0 := by
      intro hm
      exact gJ_ne_zero Q hj hQnz (map_int_poly_injective (by simpa using hm))
    have hQrel : (∑ i : Fin (j + 1), g i • (Q (emb hj i)).map (algebraMap ℤ ℚ)) = 0 := by
      calc
        (∑ i : Fin (j + 1), g i • (Q (emb hj i)).map (algebraMap ℤ ℚ))
            = ∑ i : Fin (j + 1),
                (gJ Q hj).map (algebraMap ℤ ℚ) * (g i • (sJ Q hj i).map (algebraMap ℤ ℚ)) := by
                apply Finset.sum_congr rfl
                intro i hi
                rw [sJ_div Q hj i, Polynomial.map_mul, Polynomial.smul_eq_C_mul,
                  Polynomial.smul_eq_C_mul]
                ring
        _ = (gJ Q hj).map (algebraMap ℤ ℚ) *
            (∑ i : Fin (j + 1), g i • (sJ Q hj i).map (algebraMap ℤ ℚ)) := by
                rw [← Finset.mul_sum]
        _ = 0 := by
            rw [hrel]
            simp
    exact (Fintype.linearIndependent_iff.mp hQlin) g hQrel
  -- truncated coefficient vectors of length mJ+1 are independent
  have hSvec : LinearIndependent ℚ (fun i : Fin (j + 1) =>
      (fun t : Fin (mJ Q hj + 1) => ((sJ Q hj i).coeff t.val : ℚ))) := by
    exact fullPoly_indep_to_vec (P := sJ Q hj) hSlin (fun i => sJ_deg_le_mJ Q hj i)
  have hcard : Fintype.card (Fin (j + 1)) ≤ mJ Q hj + 1 := by
    have h := LinearIndependent.fintype_card_le_finrank hSvec
    simpa using h
  have hcard' : j + 1 ≤ mJ Q hj + 1 := by
    simpa [Fintype.card_fin] using hcard
  omega

end Submission.SqfChain
