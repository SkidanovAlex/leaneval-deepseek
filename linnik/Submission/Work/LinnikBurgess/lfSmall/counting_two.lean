import Mathlib
import Submission.Work.LinnikBurgess.lfSmall.two_defs
import Submission.Work.LinnikBurgess.lfSmall.two_transfer_d1
import Submission.Work.LinnikBurgess.lfSmall.two_transfer_d2
import Submission.Work.LinnikBurgess.lfSmall.lvlSet2_card_le
import Submission.Work.LinnikBurgess.lfSmall.content_dvd_critN
import Submission.Work.LinnikBurgess.lfSmall.dlp_of_supp
import Submission.Work.LinnikBurgess.lfSmall.nv_le_vcapD2
import Submission.Work.LinnikBurgess.lfSmall.capSet2_card_le
import Submission.Work.LinnikBurgess.lfSmall.cap_term_le
import Submission.Work.LinnikBurgess.lfSmall.localFactor_lower

/-!
# The `p = 2` counting lemma

`gaussTwoRHS2 e (cubeLevel 2 e) a b ≤ localFactor 2 e a b` for `e ≥ 13` and a singleton pair.

The proof is assembled here from the transfer lemmas (`two_transfer_d1`, `two_transfer_d2`,
`nv_le_vcapD2`, `dlp_of_supp`), the two counting lemmas (`lvlSet2_card_le`, `capSet2_card_le`),
the content lemma (`content_dvd_critN`) and the menu lemma (`localFactor_lower`), all in sibling
modules of `lfSmall/`.  Those are kept as section variables so that the assembly can be checked
independently of their proofs.
-/

open scoped BigOperators
open Classical

namespace Work.LinnikBurgess.lfSmall

section Arith

lemma cubeLevel_ge_two {e : ℕ} (he : 13 ≤ e) : 2 ≤ cubeLevel 2 e := by
  simp only [cubeLevel, if_true]
  omega

lemma two_mul_cubeLevel_le {e : ℕ} (he : 13 ≤ e) : 2 * cubeLevel 2 e ≤ e := by
  simp only [cubeLevel, if_true]
  omega

lemma three_mul_cubeLevel_ge {e : ℕ} : e + 1 ≤ 3 * cubeLevel 2 e := by
  simp only [cubeLevel, if_true]
  have h := Nat.div_add_mod (e + 3) 3
  have h' := Nat.mod_lt (e + 3) (by norm_num : 0 < 3)
  omega

lemma capLevel_le_self (e : ℕ) : capLevel 2 e ≤ e := by
  rw [capLevel]; exact Nat.sub_le _ _

lemma le_cubeLevel_add_capLevel {e : ℕ} (he : 13 ≤ e) :
    cubeLevel 2 e + capLevel 2 e - 1 ≤ e := by
  rw [capLevel]
  have h := two_mul_cubeLevel_le he
  have h2 := cubeLevel_ge_two he
  omega

lemma capLevel_lt_cubeLevel {e : ℕ} (he : 13 ≤ e) : capLevel 2 e < cubeLevel 2 e := by
  rw [capLevel]
  have h := three_mul_cubeLevel_ge (e := e)
  omega

lemma one_le_cubeLevel {e : ℕ} (he : 13 ≤ e) : 1 ≤ cubeLevel 2 e := by
  have := cubeLevel_ge_two he; omega

end Arith

/-- Divisibility of an integer by a natural number, from divisibility of its `natAbs`. -/
lemma int_dvd_of_natAbs_dvd {m : ℕ} {z : ℤ} (h : m ∣ z.natAbs) : (m : ℤ) ∣ z := by
  obtain ⟨k, hk⟩ := h
  have h2 : z = (((k * m : ℕ)) : ℤ) ∨ z = -(((k * m : ℕ)) : ℤ) := by
    have := Int.natAbs_eq z
    rw [hk] at this
    simpa [mul_comm] using this
  rcases h2 with h2 | h2
  · exact ⟨(k : ℤ), by rw [h2]; push_cast; ring⟩
  · exact ⟨-(k : ℤ), by rw [h2]; push_cast; ring⟩

/-- Elements of the support with `nv = s < T` lie in `lvlSet2 e s`. -/
lemma mem_lvlSet2_of_mem_suppSet2 {e s : ℕ} (he : 13 ≤ e) (a b : Fin 3 → ℕ) {y : ℕ}
    (hy : y ∈ suppSet2 e a b) (hnv : nv e a b y = s) (hs : s < capLevel 2 e) :
    y ∈ lvlSet2 e s a b := by
  classical
  obtain ⟨hy1, hy2, hN⟩ := Finset.mem_filter.1 hy
  have hyrange := Finset.mem_range.1 hy1
  have hNe : (critN a b).derivative.eval (y : ℤ) ≠ 0 := by
    intro hzero
    have : nv e a b y = capLevel 2 e := by
      simp only [nv, hzero, Int.natAbs_zero]
      simp [vcap]
    omega
  have hNe' : (((critN a b).derivative.eval (y : ℤ)).natAbs) ≠ 0 := by
    simpa [Int.natAbs_eq_zero] using hNe
  have hpad : padicValNat 2 (((critN a b).derivative.eval (y : ℤ)).natAbs) = s := by
    have h1 : nv e a b y = min (padicValNat 2 (((critN a b).derivative.eval (y : ℤ)).natAbs))
        (capLevel 2 e) := by
      simp only [nv, vcap, if_neg hNe']
    rw [hnv] at h1
    have hpT : padicValNat 2 (((critN a b).derivative.eval (y : ℤ)).natAbs) ≤ capLevel 2 e := by
      by_contra hcon
      push Not at hcon
      rw [min_eq_right (le_of_lt hcon)] at h1
      omega
    have hm : min (padicValNat 2 (((critN a b).derivative.eval (y : ℤ)).natAbs)) (capLevel 2 e)
        = padicValNat 2 (((critN a b).derivative.eval (y : ℤ)).natAbs) := min_eq_left hpT
    omega
  rw [lvlSet2, Finset.mem_filter]
  refine ⟨Finset.mem_range.2 hyrange, hy2, ?_, hNe, hpad⟩
  rw [hnv] at hN
  exact hN

/-- Elements of the support with `nv = T` lie in the cap set. -/
lemma mem_capSet2_of_mem_suppSet2 {e : ℕ} (he : 13 ≤ e) (a b : Fin 3 → ℕ) {y : ℕ}
    (hy : y ∈ suppSet2 e a b) (hnv : nv e a b y = capLevel 2 e) :
    y ∈ capSet2 e a b := by
  classical
  obtain ⟨hy1, hy2, hN⟩ := Finset.mem_filter.1 hy
  have hyrange := Finset.mem_range.1 hy1
  have hT : (2 : ℕ) ^ capLevel 2 e ∣ (((critN a b).derivative.eval (y : ℤ)).natAbs) := by
    rw [padicValNat_dvd_iff]
    by_cases hzero : (((critN a b).derivative.eval (y : ℤ)).natAbs) = 0
    · exact Or.inl hzero
    · right
      have hmin : nv e a b y
          = min (padicValNat 2 (((critN a b).derivative.eval (y : ℤ)).natAbs)) (capLevel 2 e) := by
        simp only [nv, vcap, if_neg hzero]
      rw [hnv] at hmin
      omega
  rw [capSet2, Finset.mem_filter]
  refine ⟨Finset.mem_range.2 hyrange, hy2, ?_, ?_⟩
  · have hL : Lvl e = cubeLevel 2 e + capLevel 2 e - 1 := rfl
    rw [hL, ← hnv]
    exact hN
  · exact int_dvd_of_natAbs_dvd hT

section Assembly

variable (h_d1 : ∀ {e k : ℕ}, 1 ≤ e → k ≤ e → ∀ (a b : Fin 3 → ℕ) {y : ℕ}, UnitAt 2 y a b →
    ((2 ^ k ∣ (defect1 2 e a b y).val) ↔ ((2 ^ k : ℕ) : ℤ) ∣ (critN a b).eval (y : ℤ)))
variable (h_d2 : ∀ {e : ℕ}, 13 ≤ e → ∀ (a b : Fin 3 → ℕ) {y : ℕ}, UnitAt 2 y a b →
    ((2 ^ (cubeLevel 2 e + nv e a b y - 1) : ℕ) : ℤ) ∣ (critN a b).eval (y : ℤ) →
    vcap 2 (capLevel 2 e) (defect2 2 e a b y).val = nv e a b y)
variable (h_nvle : ∀ {e : ℕ}, 13 ≤ e → ∀ (a b : Fin 3 → ℕ) {y : ℕ}, UnitAt 2 y a b →
    ((2 ^ (cubeLevel 2 e + vcap 2 (capLevel 2 e) (defect2 2 e a b y).val - 1) : ℕ) : ℤ)
      ∣ (critN a b).eval (y : ℤ) →
    nv e a b y ≤ vcap 2 (capLevel 2 e) (defect2 2 e a b y).val)
variable (h_lvl : ∀ {e s : ℕ}, 13 ≤ e → s < capLevel 2 e → ∀ (a b : Fin 3 → ℕ),
    (lvlSet2 e s a b).card ≤ 8)
variable (h_cap : ∀ {e J : ℕ}, 13 ≤ e → ∀ (a b : Fin 3 → ℕ) (i : Fin 6),
    padicValNat 2 (contAB a b) = J → (∀ n, ((2 ^ J : ℕ) : ℤ) ∣ (critN a b).coeff n) →
    (∀ j : Fin 6, j ≠ i → shift a b i ≠ shift a b j) →
    ((capSet2 e a b).card : ℝ) ≤ (10 : ℝ) ^ 4
      * (2 : ℝ) ^ (((cubeLevel 2 e : ℝ) - (capLevel 2 e : ℝ) + 2 + (J : ℝ)) / 2))
variable (h_cont : ∀ {J : ℕ} (a b : Fin 3 → ℕ), 2 ^ J ∣ contAB a b →
    ∀ n, ((2 ^ J : ℕ) : ℤ) ∣ (critN a b).coeff n)
variable (h_dlp : ∀ {e : ℕ}, 13 ≤ e → ∀ (a b : Fin 3 → ℕ) {y : ℕ}, UnitAt 2 y a b →
    ((2 ^ (cubeLevel 2 e + nv e a b y - 1) : ℕ) : ℤ) ∣ (critN a b).eval (y : ℤ) →
    DLp 2 (nv e a b y) a b)
variable (h_lf : ∀ {e J : ℕ}, 13 ≤ e → ∀ (a b : Fin 3 → ℕ), padicValNat 2 (contAB a b) = J →
    (10 : ℝ) ^ 6 * ((Finset.range (capLevel 2 e + 1)).sum
        (fun s => ind (DLp 2 s a b) * (2 : ℝ) ^ ((s : ℝ) / 2)))
      + (10 : ℝ) ^ 6 * ((2 : ℝ) ^ (((cubeLevel 2 e : ℝ) + ((min J e : ℕ) : ℝ)) / 2)
          * ind (DLp 2 (max (capLevel 2 e) (min J e)) a b))
    ≤ localFactor 2 e a b)

include h_d1 h_d2 h_nvle h_lvl h_cap h_cont h_dlp h_lf

/-- Coefficient-wise divisibility of `critN a b` gives `DLp` witnesses at the content level. -/
lemma dlp_of_coeff {J : ℕ} (a b : Fin 3 → ℕ) {y : ℕ} (hy : UnitAt 2 y a b)
    (hcoeff : ∀ n, ((2 ^ J : ℕ) : ℤ) ∣ (critN a b).coeff n) : DLp 2 J a b := by
  classical
  have hev : ∀ {P : Polynomial ℤ}, (∀ n, ((2 ^ J : ℕ) : ℤ) ∣ P.coeff n) →
      ((2 ^ J : ℕ) : ℤ) ∣ P.eval ((y : ℤ)) := by
    intro P hP
    rw [Polynomial.eval_eq_sum_range]
    refine Finset.dvd_sum (fun i hi => ?_)
    exact dvd_mul_of_dvd_left (hP i) _
  have hd : ∀ n, ((2 ^ J : ℕ) : ℤ) ∣ (Polynomial.derivative (critN a b)).coeff n := by
    intro n
    rw [Polynomial.coeff_derivative]
    exact dvd_mul_of_dvd_left (hcoeff (n + 1)) _
  exact ⟨y, hy, hev hcoeff, hev hd⟩

/-- The summand of `gaussTwoRHS2` at `y < 2^m`, re-expressed through `critN`. -/
lemma summand_eq {e : ℕ} (he : 13 ≤ e) (a b : Fin 3 → ℕ) {y : ℕ} (hy' : y < 2 ^ cubeLevel 2 e) :
    (if UnitAt 2 y a b
        ∧ (2 ^ (cubeLevel 2 e + vcap 2 (capLevel 2 e) (defect2 2 e a b y).val - 1))
            ∣ (defect1 2 e a b y).val
      then (2 : ℝ) ^ (((vcap 2 (capLevel 2 e) (defect2 2 e a b y).val : ℕ) : ℝ) / 2)
      else 0)
      = (if y ∈ suppSet2 e a b then (2 : ℝ) ^ ((nv e a b y : ℝ) / 2) else 0) := by
  classical
  have hk : cubeLevel 2 e + vcap 2 (capLevel 2 e) (defect2 2 e a b y).val - 1 ≤ e := by
    have hBle : vcap 2 (capLevel 2 e) (defect2 2 e a b y).val ≤ capLevel 2 e := by
      rw [vcap]; split <;> simp
    have := le_cubeLevel_add_capLevel he
    omega
  by_cases hy : UnitAt 2 y a b
  · by_cases hd : (2 ^ (cubeLevel 2 e + vcap 2 (capLevel 2 e) (defect2 2 e a b y).val - 1))
        ∣ (defect1 2 e a b y).val
    · have hN : ((2 ^ (cubeLevel 2 e + vcap 2 (capLevel 2 e) (defect2 2 e a b y).val - 1) : ℕ) : ℤ)
          ∣ (critN a b).eval (y : ℤ) :=
        (h_d1 (le_trans (by norm_num) he) hk a b hy).1 hd
      have hnvle := h_nvle he a b hy hN
      have hmono : (2 ^ (cubeLevel 2 e + nv e a b y - 1) : ℕ)
          ∣ (2 ^ (cubeLevel 2 e + vcap 2 (capLevel 2 e) (defect2 2 e a b y).val - 1) : ℕ) :=
        Nat.pow_dvd_pow 2 (by omega)
      have hNnv : ((2 ^ (cubeLevel 2 e + nv e a b y - 1) : ℕ) : ℤ) ∣ (critN a b).eval (y : ℤ) :=
        dvd_trans (by exact_mod_cast hmono) hN
      have h2 := h_d2 he a b hy hNnv
      have hmem : y ∈ suppSet2 e a b := by
        rw [suppSet2, Finset.mem_filter]
        exact ⟨Finset.mem_range.2 hy', hy, hNnv⟩
      rw [if_pos ⟨hy, hd⟩, if_pos hmem, h2]
    · have hmem : y ∉ suppSet2 e a b := by
        intro hmem
        obtain ⟨-, hyU, hNnv⟩ := Finset.mem_filter.1 hmem
        have h2 := h_d2 he a b hy hNnv
        have hN : ((2 ^ (cubeLevel 2 e + vcap 2 (capLevel 2 e) (defect2 2 e a b y).val - 1) : ℕ) : ℤ)
            ∣ (critN a b).eval (y : ℤ) := by
          rw [← h2] at hNnv
          exact hNnv
        exact hd ((h_d1 (le_trans (by norm_num) he) hk a b hy).2 hN)
      rw [if_neg (by tauto), if_neg hmem]
  · have hmem : y ∉ suppSet2 e a b := by
      intro hmem
      exact hy (Finset.mem_filter.1 hmem).2.1
    rw [if_neg (by tauto), if_neg hmem]

/-- The right–hand side of Lemma A₂ as a sum over `suppSet2` with the weights `2 ^ (nv/2)`. -/
lemma gaussTwoRHS2_eq_sum {e : ℕ} (he : 13 ≤ e) (a b : Fin 3 → ℕ) :
    gaussTwoRHS2 e (cubeLevel 2 e) a b
      = ∑ y ∈ suppSet2 e a b, (2 : ℝ) ^ ((nv e a b y : ℝ) / 2) := by
  classical
  simp only [gaussTwoRHS2]
  refine (Finset.sum_congr rfl (fun y hy =>
      summand_eq h_d1 h_d2 h_nvle h_lvl h_cap h_cont h_dlp h_lf he a b
        (Finset.mem_range.1 hy))).trans ?_
  rw [← Finset.sum_filter]
  congr 1
  ext y
  simp only [Finset.mem_filter, Finset.mem_range, suppSet2]
  tauto

/-- Cardinality of the fibre at level `s < T` is at most `8`. -/
lemma fiber_card_le_eight {e s : ℕ} (he : 13 ≤ e) (a b : Fin 3 → ℕ) (hs : s < capLevel 2 e) :
    ((suppSet2 e a b).filter (fun y => nv e a b y = s)).card ≤ 8 :=
  le_trans (Finset.card_le_card (fun y hy => by
    rw [Finset.mem_filter] at hy
    exact mem_lvlSet2_of_mem_suppSet2 he a b hy.1 hy.2 hs)) (h_lvl he hs a b)

/-- The fibre at level `T` is contained in the cap set. -/
lemma fiber_card_le_cap {e : ℕ} (he : 13 ≤ e) (a b : Fin 3 → ℕ) :
    ((suppSet2 e a b).filter (fun y => nv e a b y = capLevel 2 e)).card ≤ (capSet2 e a b).card :=
  Finset.card_le_card (fun y hy => by
    rw [Finset.mem_filter] at hy
    exact mem_capSet2_of_mem_suppSet2 he a b hy.1 hy.2)

/-- The fibre at a nonempty level `s < T` witnesses `DLp 2 s a b`. -/
lemma dlp_of_fiber {e s : ℕ} (he : 13 ≤ e) (a b : Fin 3 → ℕ) (hs : s < capLevel 2 e)
    (hne : ((suppSet2 e a b).filter (fun y => nv e a b y = s)).Nonempty) : DLp 2 s a b := by
  classical
  obtain ⟨y, hy⟩ := hne
  rw [Finset.mem_filter] at hy
  obtain ⟨hysupp, hnv'⟩ := hy
  obtain ⟨hy1, hyU, hN⟩ := Finset.mem_filter.1 hysupp
  obtain ⟨-, -, hN2, hNe, hpad⟩ := Finset.mem_filter.1
    (mem_lvlSet2_of_mem_suppSet2 he a b hysupp hnv' hs)
  refine ⟨y, hyU, ?_, ?_⟩
  · have hle : s ≤ cubeLevel 2 e + s - 1 := by have := one_le_cubeLevel he; omega
    have hdvd : (2 ^ s : ℕ) ∣ (2 ^ (cubeLevel 2 e + s - 1) : ℕ) := Nat.pow_dvd_pow 2 hle
    exact dvd_trans (by exact_mod_cast hdvd) hN2
  · have hdvd : (2 ^ s : ℕ) ∣ (((critN a b).derivative.eval (y : ℤ)).natAbs) := by
      rw [padicValNat_dvd_iff]
      right
      omega
    exact int_dvd_of_natAbs_dvd hdvd

/-- The fibre at level `T`, when nonempty, witnesses `DLp 2 T a b`. -/
lemma dlp_of_capfiber {e : ℕ} (he : 13 ≤ e) (a b : Fin 3 → ℕ)
    (hne : ((suppSet2 e a b).filter (fun y => nv e a b y = capLevel 2 e)).Nonempty) :
    DLp 2 (capLevel 2 e) a b := by
  classical
  obtain ⟨y, hy⟩ := hne
  rw [Finset.mem_filter] at hy
  obtain ⟨hysupp, hnv'⟩ := hy
  obtain ⟨hy1, hyU, hN⟩ := Finset.mem_filter.1 hysupp
  obtain ⟨hy1', hyU', hL, hT'⟩ := Finset.mem_filter.1
    (mem_capSet2_of_mem_suppSet2 he a b hysupp hnv')
  refine ⟨y, hyU', ?_, hT'⟩
  have hle : capLevel 2 e ≤ Lvl e := by
    have hL' : Lvl e = cubeLevel 2 e + capLevel 2 e - 1 := rfl
    rw [hL']; have := one_le_cubeLevel he; omega
  have hdvd : (2 ^ capLevel 2 e : ℕ) ∣ (2 ^ Lvl e : ℕ) := Nat.pow_dvd_pow 2 hle
  exact dvd_trans (by exact_mod_cast hdvd) hL

/-- The support sum is bounded by the level sum and the cap term. -/
lemma fiber_sum_le {e : ℕ} (he : 13 ≤ e) (a b : Fin 3 → ℕ) :
    ∑ y ∈ suppSet2 e a b, (2 : ℝ) ^ ((nv e a b y : ℝ) / 2)
      ≤ 8 * (∑ s ∈ Finset.range (capLevel 2 e + 1),
            ind (DLp 2 s a b) * (2 : ℝ) ^ ((s : ℝ) / 2))
        + (capSet2 e a b).card * (2 : ℝ) ^ ((capLevel 2 e : ℝ) / 2) := by
  classical
  set T := capLevel 2 e with hTdef
  set W : ℕ → ℝ := fun s => (2 : ℝ) ^ ((s : ℝ) / 2) with hWdef
  have hWnn : ∀ s, 0 ≤ W s := fun s => by rw [hWdef]; positivity
  have hnvle : ∀ y, nv e a b y ≤ T := fun y => by
    rw [hTdef]; simp only [nv, vcap]; split <;> simp
  have hfib : ∑ y ∈ suppSet2 e a b, W (nv e a b y)
      = ∑ s ∈ Finset.range (T + 1),
          ∑ y ∈ (suppSet2 e a b).filter (fun y => nv e a b y = s), W (nv e a b y) :=
    (Finset.sum_fiberwise_of_maps_to (s := suppSet2 e a b) (t := Finset.range (T + 1))
      (fun y _ => by rw [Finset.mem_range]; exact Nat.lt_succ_of_le (hnvle y))
      (fun y => W (nv e a b y))).symm
  have hinner : ∀ s ∈ Finset.range (T + 1),
      ∑ y ∈ (suppSet2 e a b).filter (fun y => nv e a b y = s), W (nv e a b y)
        = ((suppSet2 e a b).filter (fun y => nv e a b y = s)).card * W s := by
    intro s hs
    rw [Finset.sum_congr rfl (fun y hy => ?_), Finset.sum_const, nsmul_eq_mul]
    rw [Finset.mem_filter] at hy
    rw [hy.2]
  rw [hfib, Finset.sum_congr rfl hinner]
  have hstep : ∀ s ∈ Finset.range (T + 1),
      ((suppSet2 e a b).filter (fun y => nv e a b y = s)).card * W s
        ≤ 8 * (ind (DLp 2 s a b) * W s)
          + (if s = T then (capSet2 e a b).card * W T else 0) := by
    intro s hs
    have hsle : s ≤ T := by rw [Finset.mem_range] at hs; omega
    by_cases hsT : s < T
    · have hcard : ((suppSet2 e a b).filter (fun y => nv e a b y = s)).card ≤ 8 :=
        fiber_card_le_eight h_d1 h_d2 h_nvle h_lvl h_cap h_cont h_dlp h_lf he a b
          (by rw [hTdef] at hsT; exact hsT)
      by_cases hne : ((suppSet2 e a b).filter (fun y => nv e a b y = s)).Nonempty
      · have hdlp : DLp 2 s a b :=
          dlp_of_fiber h_d1 h_d2 h_nvle h_lvl h_cap h_cont h_dlp h_lf he a b
            (by rw [hTdef] at hsT; exact hsT) hne
        rw [ind_eq_one_of _ hdlp, if_neg (by omega), one_mul]
        have hcard' : ((((suppSet2 e a b).filter (fun y => nv e a b y = s)).card : ℕ) : ℝ) ≤ 8 := by
          exact_mod_cast hcard
        nlinarith [hcard', hWnn s]
      · rw [Finset.not_nonempty_iff_eq_empty] at hne
        rw [hne, Finset.card_empty, Nat.cast_zero, zero_mul, if_neg (by omega)]
        have h1 := ind_nonneg (DLp 2 s a b)
        have h2 := hWnn s
        positivity
    · have hsT' : s = T := by omega
      subst hsT'
      rw [if_pos rfl]
      have hcard : ((suppSet2 e a b).filter (fun y => nv e a b y = T)).card
          ≤ (capSet2 e a b).card :=
        fiber_card_le_cap h_d1 h_d2 h_nvle h_lvl h_cap h_cont h_dlp h_lf he a b
      have h1 : (0 : ℝ) ≤ 8 * (ind (DLp 2 T a b) * W T) := by
        have := ind_nonneg (DLp 2 T a b); positivity
      have hcard' : ((((suppSet2 e a b).filter (fun y => nv e a b y = T)).card : ℕ) : ℝ)
          ≤ ((capSet2 e a b).card : ℝ) := by exact_mod_cast hcard
      nlinarith [hcard', hWnn T, h1]
  refine le_trans (Finset.sum_le_sum hstep) ?_
  rw [Finset.sum_add_distrib, Finset.mul_sum]
  have hsec : (∑ s ∈ Finset.range (T + 1),
      (if s = T then (capSet2 e a b).card * W T else 0)) ≤ (capSet2 e a b).card * W T := by
    rw [Finset.sum_ite_eq']
    rw [if_pos (by rw [Finset.mem_range]; omega)]
  linarith [hsec]


variable (h_ct : ∀ {e J : ℕ}, 13 ≤ e → ∀ (a b : Fin 3 → ℕ) (i : Fin 6),
    padicValNat 2 (contAB a b) = J → (∀ n, ((2 ^ J : ℕ) : ℤ) ∣ (critN a b).coeff n) →
    (∀ j : Fin 6, j ≠ i → shift a b i ≠ shift a b j) →
    ((capSet2 e a b).card ≠ 0 → DLp 2 (capLevel 2 e) a b) →
    ((capSet2 e a b).card ≠ 0 → J ≤ e → DLp 2 J a b) →
    (2 ^ J : ℕ) ∣ contAB a b →
    ((capSet2 e a b).card : ℝ) * (2 : ℝ) ^ ((capLevel 2 e : ℝ) / 2)
      ≤ (10 : ℝ) ^ 6 * ((2 : ℝ) ^ (((cubeLevel 2 e : ℝ) + ((min J e : ℕ) : ℝ)) / 2)
          * ind (DLp 2 (max (capLevel 2 e) (min J e)) a b)))

include h_ct

/-- The counting lemma, modulo the sibling modules (all kept as section variables). -/
theorem counting_two_aux {e : ℕ} (he : 13 ≤ e) (a b : Fin 3 → ℕ) (i : Fin 6)
    (hi : ∀ j : Fin 6, j ≠ i → shift a b i ≠ shift a b j) :
    gaussTwoRHS2 e (cubeLevel 2 e) a b ≤ localFactor 2 e a b := by
  classical
  set J := padicValNat 2 (contAB a b) with hJdef
  have hJdvd : (2 ^ J : ℕ) ∣ contAB a b := by
    rw [hJdef, padicValNat_dvd_iff]
    exact Or.inr le_rfl
  have hcoeff : ∀ n, ((2 ^ J : ℕ) : ℤ) ∣ (critN a b).coeff n := h_cont a b hJdvd
  have hlf := h_lf he a b (J := J) hJdef.symm
  rw [gaussTwoRHS2_eq_sum h_d1 h_d2 h_nvle h_lvl h_cap h_cont h_dlp h_lf he a b]
  refine le_trans (fiber_sum_le h_d1 h_d2 h_nvle h_lvl h_cap h_cont h_dlp h_lf he a b) ?_
  set S : ℝ := ∑ s ∈ Finset.range (capLevel 2 e + 1),
    ind (DLp 2 s a b) * (2 : ℝ) ^ ((s : ℝ) / 2) with hSdef
  have hSnn : 0 ≤ S := by
    rw [hSdef]
    exact Finset.sum_nonneg (fun s _ => by
      have := ind_nonneg (DLp 2 s a b); positivity)
  have h8 : 8 * S ≤ (10 : ℝ) ^ 6 * S := by nlinarith
  have hcapT : (capSet2 e a b).card ≠ 0 → DLp 2 (capLevel 2 e) a b := by
    intro h0
    obtain ⟨y, hy⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero h0)
    obtain ⟨-, hyU, hL, hTd⟩ := Finset.mem_filter.1 hy
    refine ⟨y, hyU, ?_, hTd⟩
    have hle : capLevel 2 e ≤ Lvl e := by
      have hL' : Lvl e = cubeLevel 2 e + capLevel 2 e - 1 := rfl
      rw [hL']; have := one_le_cubeLevel he; omega
    exact dvd_trans (by exact_mod_cast Nat.pow_dvd_pow 2 hle) hL
  have hcapJ : (capSet2 e a b).card ≠ 0 → J ≤ e → DLp 2 J a b := by
    intro h0 _
    obtain ⟨y, hy⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero h0)
    obtain ⟨-, hyU, -, -⟩ := Finset.mem_filter.1 hy
    exact dlp_of_coeff h_d1 h_d2 h_nvle h_lvl h_cap h_cont h_dlp h_lf a b hyU hcoeff
  have hct := h_ct he a b i hJdef.symm hcoeff hi hcapT hcapJ hJdvd
  linarith [hlf, h8, hct]


/-- **The `p = 2` counting lemma**: the right–hand side of Lemma A₂ at `m = cubeLevel 2 e`
is dominated by the `2`-adic local factor, for `e ≥ 13` and a singleton pair. -/
theorem counting_two {e : ℕ} (he : 13 ≤ e) (a b : Fin 3 → ℕ) (i : Fin 6)
    (hi : ∀ j : Fin 6, j ≠ i → shift a b i ≠ shift a b j) :
    gaussTwoRHS2 e (cubeLevel 2 e) a b ≤ localFactor 2 e a b :=
  counting_two_aux two_transfer_d1 two_transfer_d2 nv_le_vcapD2 lvlSet2_card_le
    capSet2_card_le content_dvd_critN dlp_of_supp localFactor_lower cap_term_le he a b i hi

end Assembly

end Work.LinnikBurgess.lfSmall
