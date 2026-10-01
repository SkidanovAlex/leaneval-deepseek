/-
# Lemma A_2 (`p = 2`) in the `gaussSum` bubble

The `p = 2` "two-digit" (Postnikov) bound for the cubic character correlation:
`||sum_x chi (f_a x) * conj (chi (f_b x))|| <= 2^(e/2) * gaussTwoRHS2 e m a b` for `e + 1 <= 3m`,
`2m <= e`.  This is the statement of `Work.LinnikBurgess.corr6_twoPow_gaussTwo_le`, re-proved in the
`gaussSum` bubble (`...gaussSum_normSq_eq_conductor`, not `...charCorrelation_twoPow`), because the
caller also needs the `lfSmall` counting chain at `p = 2` and those two `Commons` clusters cannot be
imported together.  Used here: `Work.ZeroFreeTables.P9F.twoPow_innerSum_factor_aux` (the peel,
re-proving `thetaTwo_core.lean` + `twoPow_innerSum_factor.lean`),
`Work.ZeroFreeTables.P9F.sum_range_mul_pow_two`, and Mathlib's `DirichletCharacter.norm_le_one` in
place of the `Commons` copy; `twoPow_quadGaussSum` and `twoPow_innerSum_vanishing` are already in the
`gaussSum` bubble.
-/
import Mathlib
import Submission.Work.LinnikBurgess.burgess_lead_defs
import Submission.Work.LinnikBurgess.corr6_twoPow_defs
import Submission.Work.LinnikBurgess.twoPow_quadGaussSum
import Submission.Work.LinnikBurgess.twoPow_innerSum_vanishing
import Submission.Work.ZeroFreeTables.P9F.twoPow_api
import Submission.Work.ZeroFreeTables.P9F.twoPow_innerSum_factor_aux

set_option linter.style.haveILetI false
open scoped BigOperators

namespace Work.ZeroFreeTables.P9F.TwoPowB

open Work.LinnikBurgess
lemma sum_zmod_eq_sum_range' {n : ℕ} [NeZero n] {M : Type*} [AddCommMonoid M]
    (f : ZMod n → M) : ∑ x : ZMod n, f x = ∑ i ∈ Finset.range n, f (i : ZMod n) := by
  refine Finset.sum_bij (fun (x : ZMod n) _ => x.val) ?_ ?_ ?_ ?_
  · intro a _; exact Finset.mem_range.mpr (ZMod.val_lt a)
  · intro a _ b _ h; exact ZMod.val_injective n h
  · intro b hb
    refine ⟨(b : ZMod n), Finset.mem_univ _, ?_⟩
    rw [ZMod.val_natCast]
    exact Nat.mod_eq_of_lt (Finset.mem_range.mp hb)
  · intro a _
    rw [ZMod.natCast_zmod_val]

lemma sum_reindex_twoPow {e m : ℕ} (hm : 1 ≤ m) (h2 : 2 * m ≤ e) (F : ZMod (2 ^ e) → ℂ) :
    (∑ x : ZMod (2 ^ e), F x)
      = ∑ y ∈ Finset.range (2 ^ m), ∑ w : ZMod (2 ^ (e - m)),
          F (((y : ℕ) : ZMod (2 ^ e)) + ((2 ^ m * w.val : ℕ) : ZMod (2 ^ e))) := by
  have hsum : m + (e - m) = e := by omega
  have hmle : m ≤ e := by omega
  haveI : NeZero (2 ^ e) := ⟨pow_ne_zero e (by norm_num)⟩
  haveI : NeZero (2 ^ m) := ⟨pow_ne_zero m (by norm_num)⟩
  haveI : NeZero (2 ^ (e - m)) := ⟨pow_ne_zero (e - m) (by norm_num)⟩
  -- convert the inner `ZMod` sum into a `range` sum
  have hinner : ∀ y : ℕ,
      (∑ w : ZMod (2 ^ (e - m)),
          F (((y : ℕ) : ZMod (2 ^ e)) + ((2 ^ m * w.val : ℕ) : ZMod (2 ^ e))))
        = ∑ t ∈ Finset.range (2 ^ (e - m)),
            F (((y : ℕ) : ZMod (2 ^ e)) + ((2 ^ m * t : ℕ) : ZMod (2 ^ e))) := by
    intro y
    rw [sum_zmod_eq_sum_range' (f := fun w : ZMod (2 ^ (e - m)) =>
        F (((y : ℕ) : ZMod (2 ^ e)) + ((2 ^ m * w.val : ℕ) : ZMod (2 ^ e))))]
    refine Finset.sum_congr rfl (fun t ht => ?_)
    congr 1
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (Finset.mem_range.mp ht)]
  rw [sum_zmod_eq_sum_range']
  simp only [hinner]
  have key := Work.ZeroFreeTables.P9F.sum_range_mul_pow_two
    (j := m) (m := e - m) (G := fun X : ℕ => F ((X : ℕ) : ZMod (2 ^ e)))
  rw [hsum] at key
  rw [key]
  refine Finset.sum_congr rfl (fun y hy => Finset.sum_congr rfl (fun t ht => ?_))
  congr 1
  push_cast
  ring

-- vcap lemmas
lemma vcap_eq_of_ne_zero {K x : ℕ} (hx : x ≠ 0) : vcap 2 K x = min (padicValNat 2 x) K := by
  unfold vcap
  rw [if_neg hx]

lemma vcap_eq_of_zero (K : ℕ) : vcap 2 K 0 = K := by
  unfold vcap
  rw [if_pos rfl]

lemma vcap_two_zero (x : ℕ) : vcap 2 0 x = 0 := by
  rcases eq_or_ne x 0 with h | h
  · subst h; exact vcap_eq_of_zero 0
  · rw [vcap_eq_of_ne_zero h]
    exact Nat.min_eq_right (Nat.zero_le _)

lemma padicValNat_two_mod {M t : ℕ} (ht : t % 2 ^ M ≠ 0) :
    padicValNat 2 (t % 2 ^ M) = padicValNat 2 t := by
  have ht0 : t ≠ 0 := fun h => ht (by rw [h, Nat.zero_mod])
  have hdiv : ∀ n ≤ M, (2 ^ n ∣ t % 2 ^ M ↔ 2 ^ n ∣ t) := by
    intro n hn
    have hndvd : 2 ^ n ∣ 2 ^ M := pow_dvd_pow 2 hn
    have hsub : t - t / 2 ^ M * 2 ^ M = t % 2 ^ M := by
      refine Nat.sub_eq_of_eq_add ?_
      have h := (Nat.div_add_mod t (2 ^ M)).symm
      rw [mul_comm (2 ^ M) (t / 2 ^ M), add_comm] at h
      exact h
    constructor
    · intro h
      have hd := Nat.div_add_mod t (2 ^ M)
      rw [← hd]
      exact Nat.dvd_add (dvd_mul_of_dvd_left hndvd (t / 2 ^ M)) h
    · intro h
      have h2 : 2 ^ n ∣ t - t / 2 ^ M * 2 ^ M :=
        Nat.dvd_sub h (dvd_mul_of_dvd_right hndvd (t / 2 ^ M))
      rwa [hsub] at h2
  have hM1 : 1 ≤ M := by
    by_contra h
    have h0 : M = 0 := by omega
    rw [h0, pow_zero, Nat.mod_one] at ht
    exact ht rfl
  have hlt : padicValNat 2 t < M := by
    by_contra hcon
    push Not at hcon
    exact ht (Nat.mod_eq_zero_of_dvd ((padicValNat_dvd_iff_le ht0).mpr hcon))
  refine le_antisymm ?_ ?_
  · by_contra hcon
    push Not at hcon
    have h1 : 2 ^ (padicValNat 2 t + 1) ∣ t % 2 ^ M :=
      (padicValNat_dvd_iff_le ht).mpr (by omega)
    have h2 : 2 ^ (padicValNat 2 t + 1) ∣ t := (hdiv (padicValNat 2 t + 1) (by omega)).mp h1
    exact pow_succ_padicValNat_not_dvd ht0 h2
  · have h1 : 2 ^ padicValNat 2 t ∣ t := (padicValNat_dvd_iff_le ht0).mpr le_rfl
    have h2 : 2 ^ padicValNat 2 t ∣ t % 2 ^ M := (hdiv _ hlt.le).mpr h1
    exact (padicValNat_dvd_iff_le ht).mp h2

lemma vcap_mod_two_pow {K M t : ℕ} (hK : K ≤ M) : vcap 2 K (t % 2 ^ M) = vcap 2 K t := by
  rcases eq_or_ne t 0 with h | ht
  · subst h; simp
  by_cases hC : t % 2 ^ M = 0
  · rw [hC, vcap_eq_of_zero, vcap_eq_of_ne_zero ht]
    refine (Nat.min_eq_right ?_).symm
    exact (padicValNat_dvd_iff_le ht).mp
      (dvd_trans (pow_dvd_pow 2 hK) (Nat.dvd_of_mod_eq_zero hC))
  · rw [vcap_eq_of_ne_zero hC, vcap_eq_of_ne_zero ht, padicValNat_two_mod hC]

lemma castHom_val_twoPow {N M : ℕ} (hM : M ≤ N) (c : ZMod (2 ^ N)) :
    ((ZMod.castHom (pow_dvd_pow 2 hM) (ZMod (2 ^ M))) c).val = c.val % 2 ^ M := by
  haveI : NeZero (2 ^ N) := ⟨pow_ne_zero N (by norm_num)⟩
  rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.val_natCast]

lemma vcap_castHom_eq {N M K : ℕ} (hM : M ≤ N) (hK : K ≤ M) (c : ZMod (2 ^ N)) :
    vcap 2 K ((ZMod.castHom (pow_dvd_pow 2 hM) (ZMod (2 ^ M))) c).val = vcap 2 K c.val := by
  rw [castHom_val_twoPow hM c]
  exact vcap_mod_two_pow hK

lemma dvd_castHom_val {N M k : ℕ} (hM : M ≤ N) (hk : k ≤ M) (c : ZMod (2 ^ N)) :
    2 ^ k ∣ ((ZMod.castHom (pow_dvd_pow 2 hM) (ZMod (2 ^ M))) c).val ↔ 2 ^ k ∣ c.val := by
  rw [castHom_val_twoPow hM c]
  constructor
  · intro h
    have hd := Nat.div_add_mod c.val (2 ^ M)
    rw [← hd]
    exact Nat.dvd_add (dvd_mul_of_dvd_left (pow_dvd_pow 2 hk) (c.val / 2 ^ M)) h
  · intro h
    have hsub : c.val - c.val / 2 ^ M * 2 ^ M = c.val % 2 ^ M := by
      refine Nat.sub_eq_of_eq_add ?_
      have h := (Nat.div_add_mod c.val (2 ^ M)).symm
      rw [mul_comm (2 ^ M) (c.val / 2 ^ M), add_comm] at h
      exact h
    have h2 : 2 ^ k ∣ c.val - c.val / 2 ^ M * 2 ^ M :=
      Nat.dvd_sub h (dvd_mul_of_dvd_right (pow_dvd_pow 2 hk) (c.val / 2 ^ M))
    rwa [hsub] at h2



lemma vcap_le (p K x : ℕ) : vcap p K x ≤ K := by
  unfold vcap
  split
  · exact le_rfl
  · exact Nat.min_le_right _ _

lemma summand_form_congr {e m : ℕ} (χ : DirichletCharacter ℂ (2 ^ e)) (a b : Fin 3 → ℕ)
    (y : ℕ) (w : ZMod (2 ^ (e - m))) :
    χ (∏ l : Fin 3, (((y : ℕ) : ZMod (2 ^ e)) + ((2 ^ m * w.val : ℕ) : ZMod (2 ^ e)) + (a l : ZMod (2 ^ e))))
        * (starRingEnd ℂ) (χ (∏ l : Fin 3, (((y : ℕ) : ZMod (2 ^ e)) + ((2 ^ m * w.val : ℕ) : ZMod (2 ^ e)) + (b l : ZMod (2 ^ e)))))
      = χ (∏ l : Fin 3, (((y : ℕ) : ZMod (2 ^ e)) + ((2 ^ m : ℕ) : ZMod (2 ^ e)) * ((w.val : ℕ) : ZMod (2 ^ e)) + (a l : ℕ)))
        * (starRingEnd ℂ) (χ (∏ l : Fin 3, (((y : ℕ) : ZMod (2 ^ e)) + ((2 ^ m : ℕ) : ZMod (2 ^ e)) * ((w.val : ℕ) : ZMod (2 ^ e)) + (b l : ℕ)))) := by
  have h1 : (∏ l : Fin 3, (((y : ℕ) : ZMod (2 ^ e)) + ((2 ^ m * w.val : ℕ) : ZMod (2 ^ e)) + (a l : ZMod (2 ^ e))))
      = ∏ l : Fin 3, (((y : ℕ) : ZMod (2 ^ e)) + ((2 ^ m : ℕ) : ZMod (2 ^ e)) * ((w.val : ℕ) : ZMod (2 ^ e)) + (a l : ℕ)) := by
    refine Finset.prod_congr rfl (fun l _ => ?_)
    push_cast
    ring
  have h2 : (∏ l : Fin 3, (((y : ℕ) : ZMod (2 ^ e)) + ((2 ^ m * w.val : ℕ) : ZMod (2 ^ e)) + (b l : ZMod (2 ^ e))))
      = ∏ l : Fin 3, (((y : ℕ) : ZMod (2 ^ e)) + ((2 ^ m : ℕ) : ZMod (2 ^ e)) * ((w.val : ℕ) : ZMod (2 ^ e)) + (b l : ℕ)) := by
    refine Finset.prod_congr rfl (fun l _ => ?_)
    push_cast
    ring
  rw [h1, h2]



/-- Per-`y` bound, positive case: when all six shifts are odd and the criticality condition
holds, the inner sum over the last `e - m` binary digits is bounded by the Gauss-sum weight. -/
lemma inner_bound_pos {e m : ℕ} (hm : 1 ≤ m) (h3 : e + 1 ≤ 3 * m) (h2 : 2 * m ≤ e)
    (χ : DirichletCharacter ℂ (2 ^ e)) (hχ : χ.IsPrimitive) (a b : Fin 3 → ℕ) (y : ℕ)
    (hU : UnitAt 2 y a b)
    (hdiv : 2 ^ (m + vcap 2 (e - 2 * m) (defect2 2 e a b y).val - 1) ∣ (defect1 2 e a b y).val) :
    ‖∑ w : ZMod (2 ^ (e - m)),
        χ (∏ l : Fin 3, (((y : ℕ) : ZMod (2 ^ e)) + ((2 ^ m : ℕ) : ZMod (2 ^ e)) * ((w.val : ℕ) : ZMod (2 ^ e)) + (a l : ℕ)))
        * (starRingEnd ℂ) (χ (∏ l : Fin 3, (((y : ℕ) : ZMod (2 ^ e)) + ((2 ^ m : ℕ) : ZMod (2 ^ e)) * ((w.val : ℕ) : ZMod (2 ^ e)) + (b l : ℕ))))‖
      ≤ (2 : ℝ) ^ ((e : ℝ) / 2) * (2 : ℝ) ^ ((vcap 2 (e - 2 * m) (defect2 2 e a b y).val : ℝ) / 2) := by
  classical
  by_cases he3 : 3 ≤ e
  · -- main case: the two-digit peel plus the 2-adic quadratic Gauss sum
    obtain ⟨hprim, hfac⟩ := Work.ZeroFreeTables.P9F.twoPow_innerSum_factor_aux hm he3 h3 h2 χ hχ a b y hU
    have hK : 1 ≤ e - m := by omega
    have hmK : m ≤ e - m := by omega
    have hg := twoPow_quadGaussSum (K := e - m) (m := m) hK hm hmK hprim
      ((ZMod.castHom (pow_dvd_pow 2 (by omega : e - m ≤ e)) (ZMod (2 ^ (e - m)))) (defect1 2 e a b y))
      ((ZMod.castHom (pow_dvd_pow 2 (by omega : e - m ≤ e)) (ZMod (2 ^ (e - m)))) (defect2 2 e a b y))
    have hC : ‖χ (∏ l : Fin 3, (((y : ℕ) : ZMod (2 ^ e)) + (a l : ℕ)))
        * (starRingEnd ℂ) (χ (∏ l : Fin 3, (((y : ℕ) : ZMod (2 ^ e)) + (b l : ℕ))))‖ ≤ 1 := by
      rw [starRingEnd_apply, norm_mul, norm_star]
      have h1 := DirichletCharacter.norm_le_one χ
        (∏ l : Fin 3, (((y : ℕ) : ZMod (2 ^ e)) + (a l : ℕ)))
      have h2 := DirichletCharacter.norm_le_one χ
        (∏ l : Fin 3, (((y : ℕ) : ZMod (2 ^ e)) + (b l : ℕ)))
      have h1' := norm_nonneg (χ (∏ l : Fin 3, (((y : ℕ) : ZMod (2 ^ e)) + (a l : ℕ))))
      have h2' := norm_nonneg (χ (∏ l : Fin 3, (((y : ℕ) : ZMod (2 ^ e)) + (b l : ℕ))))
      nlinarith [h1, h2, h1', h2']
    have hb : vcap 2 ((e - m) - m)
          ((ZMod.castHom (pow_dvd_pow 2 (by omega : e - m ≤ e)) (ZMod (2 ^ (e - m)))) (defect2 2 e a b y)).val
        = vcap 2 (e - 2 * m) (defect2 2 e a b y).val := by
      have h1 : (e - m) - m = e - 2 * m := by omega
      rw [h1]
      exact vcap_castHom_eq (by omega) (by omega) (defect2 2 e a b y)
    have hdiv' : 2 ^ (m + vcap 2 ((e - m) - m)
          ((ZMod.castHom (pow_dvd_pow 2 (by omega : e - m ≤ e)) (ZMod (2 ^ (e - m)))) (defect2 2 e a b y)).val - 1)
        ∣ ((ZMod.castHom (pow_dvd_pow 2 (by omega : e - m ≤ e)) (ZMod (2 ^ (e - m)))) (defect1 2 e a b y)).val := by
      rw [hb]
      exact (dvd_castHom_val (by omega) (by
        have hv := vcap_le 2 (e - 2 * m) (defect2 2 e a b y).val
        omega) (defect1 2 e a b y)).mpr hdiv
    have hexp : ((((e - m) + (m + vcap 2 ((e - m) - m)
            ((ZMod.castHom (pow_dvd_pow 2 (by omega : e - m ≤ e)) (ZMod (2 ^ (e - m)))) (defect2 2 e a b y)).val) : ℕ) : ℝ) / 2)
        = (e : ℝ) / 2 + ((vcap 2 (e - 2 * m) (defect2 2 e a b y).val : ℝ) / 2) := by
      have h1 : (e - m) + (m + vcap 2 ((e - m) - m)
            ((ZMod.castHom (pow_dvd_pow 2 (by omega : e - m ≤ e)) (ZMod (2 ^ (e - m)))) (defect2 2 e a b y)).val)
          = e + vcap 2 (e - 2 * m) (defect2 2 e a b y).val := by
        rw [hb]
        omega
      rw [h1]
      push_cast
      ring
    rw [hfac, norm_mul]
    have hsum_eq : (∑ w : ZMod (2 ^ (e - m)),
          (χ (thetaTwo e m 1)) ^ (((ZMod.castHom (pow_dvd_pow 2 (by omega : e - m ≤ e)) (ZMod (2 ^ (e - m)))) (defect1 2 e a b y) * w
            - ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ (e - m)))
              * ((ZMod.castHom (pow_dvd_pow 2 (by omega : e - m ≤ e)) (ZMod (2 ^ (e - m)))) (defect2 2 e a b y) * w ^ 2)).val))
        = ∑ w : ZMod (2 ^ (e - m)),
          (χ (thetaTwo e m 1)) ^ (((ZMod.castHom (pow_dvd_pow 2 (by omega : e - m ≤ e)) (ZMod (2 ^ (e - m)))) (defect1 2 e a b y) * w
            - ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ (e - m)))
              * (ZMod.castHom (pow_dvd_pow 2 (by omega : e - m ≤ e)) (ZMod (2 ^ (e - m)))) (defect2 2 e a b y) * w ^ 2).val) := by
      refine Finset.sum_congr rfl (fun w _ => ?_)
      congr 1
      congr 1
      ring
    rw [hsum_eq]
    refine (mul_le_mul hC le_rfl (norm_nonneg _) (by positivity)).trans ?_
    calc (1 : ℝ) * ‖∑ w : ZMod (2 ^ (e - m)),
            (χ (thetaTwo e m 1)) ^ (((ZMod.castHom (pow_dvd_pow 2 (by omega : e - m ≤ e)) (ZMod (2 ^ (e - m)))) (defect1 2 e a b y) * w
              - ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ (e - m)))
                * (ZMod.castHom (pow_dvd_pow 2 (by omega : e - m ≤ e)) (ZMod (2 ^ (e - m)))) (defect2 2 e a b y) * w ^ 2).val)‖
        ≤ 1 * ((2 : ℝ) ^ ((((e - m) + (m + vcap 2 ((e - m) - m)
              ((ZMod.castHom (pow_dvd_pow 2 (by omega : e - m ≤ e)) (ZMod (2 ^ (e - m)))) (defect2 2 e a b y)).val) : ℕ) : ℝ) / 2)
            * (if 2 ^ (m + vcap 2 ((e - m) - m)
                  ((ZMod.castHom (pow_dvd_pow 2 (by omega : e - m ≤ e)) (ZMod (2 ^ (e - m)))) (defect2 2 e a b y)).val - 1)
                ∣ ((ZMod.castHom (pow_dvd_pow 2 (by omega : e - m ≤ e)) (ZMod (2 ^ (e - m)))) (defect1 2 e a b y)).val
              then 1 else 0)) := by
          exact mul_le_mul_of_nonneg_left hg (by norm_num)
      _ = (2 : ℝ) ^ ((e : ℝ) / 2) * (2 : ℝ) ^ ((vcap 2 (e - 2 * m) (defect2 2 e a b y).val : ℝ) / 2) := by
          rw [one_mul, hexp, Real.rpow_add (by norm_num), if_pos hdiv', mul_one]


  · -- degenerate case `e < 3`: here `e = 2`, `m = 1`, and the trivial bound suffices
    have he2 : e = 2 := by omega
    have hm1 : m = 1 := by omega
    subst he2
    subst hm1
    have hb0 : vcap 2 (2 - 2 * 1) (defect2 2 2 a b y).val = 0 := by
      rw [show (2 : ℕ) - 2 * 1 = 0 by norm_num]
      exact vcap_two_zero _
    have hgoal : (2 : ℝ) ^ (((2 : ℕ) : ℝ) / 2)
        * (2 : ℝ) ^ ((vcap 2 (2 - 2 * 1) (defect2 2 2 a b y).val : ℝ) / 2) = 2 := by
      rw [hb0]
      have hnum1 : (2 : ℝ) ^ (((2 : ℕ) : ℝ) / 2) = 2 := by
        have h : (((2 : ℕ) : ℝ) / 2) = ((1 : ℕ) : ℝ) := by norm_num
        rw [h, Real.rpow_natCast]
        norm_num
      have hnum2 : (2 : ℝ) ^ (((0 : ℕ) : ℝ) / 2) = 1 := by
        have h : (((0 : ℕ) : ℝ) / 2) = ((0 : ℕ) : ℝ) := by norm_num
        rw [h, Real.rpow_natCast]
        norm_num
      rw [hnum1, hnum2, mul_one]
    rw [hgoal]
    have hstep : (∑ w : ZMod (2 ^ (2 - 1)),
          ‖χ (∏ l : Fin 3, (((y : ℕ) : ZMod (2 ^ 2)) + ((2 ^ 1 : ℕ) : ZMod (2 ^ 2)) * ((w.val : ℕ) : ZMod (2 ^ 2)) + (a l : ℕ)))
            * (starRingEnd ℂ) (χ (∏ l : Fin 3, (((y : ℕ) : ZMod (2 ^ 2)) + ((2 ^ 1 : ℕ) : ZMod (2 ^ 2)) * ((w.val : ℕ) : ZMod (2 ^ 2)) + (b l : ℕ))))‖)
        ≤ ∑ _w : ZMod (2 ^ (2 - 1)), (1 : ℝ) := by
      refine Finset.sum_le_sum (fun w _ => ?_)
      rw [starRingEnd_apply, norm_mul, norm_star]
      have h1 := DirichletCharacter.norm_le_one χ
        (∏ l : Fin 3, (((y : ℕ) : ZMod (2 ^ 2)) + ((2 ^ 1 : ℕ) : ZMod (2 ^ 2)) * ((w.val : ℕ) : ZMod (2 ^ 2)) + (a l : ℕ)))
      have h2 := DirichletCharacter.norm_le_one χ
        (∏ l : Fin 3, (((y : ℕ) : ZMod (2 ^ 2)) + ((2 ^ 1 : ℕ) : ZMod (2 ^ 2)) * ((w.val : ℕ) : ZMod (2 ^ 2)) + (b l : ℕ)))
      have h1' := norm_nonneg (χ (∏ l : Fin 3, (((y : ℕ) : ZMod (2 ^ 2)) + ((2 ^ 1 : ℕ) : ZMod (2 ^ 2)) * ((w.val : ℕ) : ZMod (2 ^ 2)) + (a l : ℕ))))
      have h2' := norm_nonneg (χ (∏ l : Fin 3, (((y : ℕ) : ZMod (2 ^ 2)) + ((2 ^ 1 : ℕ) : ZMod (2 ^ 2)) * ((w.val : ℕ) : ZMod (2 ^ 2)) + (b l : ℕ))))
      nlinarith [h1, h2, h1', h2']
    refine (norm_sum_le _ _).trans (hstep.trans (le_of_eq ?_))
    rw [Finset.sum_const, Finset.card_univ, ZMod.card]
    norm_num

/-- Per-`y` bound, vanishing case: if some shift is even, or the criticality condition fails,
the whole inner sum vanishes. -/
lemma inner_bound_zero {e m : ℕ} (hm : 1 ≤ m) (h3 : e + 1 ≤ 3 * m) (h2 : 2 * m ≤ e)
    (χ : DirichletCharacter ℂ (2 ^ e)) (hχ : χ.IsPrimitive) (a b : Fin 3 → ℕ) (y : ℕ)
    (h : ¬ (UnitAt 2 y a b ∧
      2 ^ (m + vcap 2 (e - 2 * m) (defect2 2 e a b y).val - 1) ∣ (defect1 2 e a b y).val)) :
    (∑ w : ZMod (2 ^ (e - m)),
        χ (∏ l : Fin 3, (((y : ℕ) : ZMod (2 ^ e)) + ((2 ^ m : ℕ) : ZMod (2 ^ e)) * ((w.val : ℕ) : ZMod (2 ^ e)) + (a l : ℕ)))
        * (starRingEnd ℂ) (χ (∏ l : Fin 3, (((y : ℕ) : ZMod (2 ^ e)) + ((2 ^ m : ℕ) : ZMod (2 ^ e)) * ((w.val : ℕ) : ZMod (2 ^ e)) + (b l : ℕ))))) = 0 := by
  classical
  by_cases hU : UnitAt 2 y a b
  · by_cases he3 : 3 ≤ e
    · obtain ⟨hprim, hfac⟩ := Work.ZeroFreeTables.P9F.twoPow_innerSum_factor_aux hm he3 h3 h2 χ hχ a b y hU
      have hndiv : ¬ (2 ^ (m + vcap 2 (e - 2 * m) (defect2 2 e a b y).val - 1)
          ∣ (defect1 2 e a b y).val) := fun hh => h ⟨hU, hh⟩
      have hg := twoPow_quadGaussSum (K := e - m) (m := m) (by omega) hm (by omega) hprim
        ((ZMod.castHom (pow_dvd_pow 2 (by omega : e - m ≤ e)) (ZMod (2 ^ (e - m)))) (defect1 2 e a b y))
        ((ZMod.castHom (pow_dvd_pow 2 (by omega : e - m ≤ e)) (ZMod (2 ^ (e - m)))) (defect2 2 e a b y))
      have hb : vcap 2 ((e - m) - m)
            ((ZMod.castHom (pow_dvd_pow 2 (by omega : e - m ≤ e)) (ZMod (2 ^ (e - m)))) (defect2 2 e a b y)).val
          = vcap 2 (e - 2 * m) (defect2 2 e a b y).val := by
        have h1 : (e - m) - m = e - 2 * m := by omega
        rw [h1]
        exact vcap_castHom_eq (by omega) (by omega) (defect2 2 e a b y)
      have hndiv' : ¬ (2 ^ (m + vcap 2 ((e - m) - m)
            ((ZMod.castHom (pow_dvd_pow 2 (by omega : e - m ≤ e)) (ZMod (2 ^ (e - m)))) (defect2 2 e a b y)).val - 1)
          ∣ ((ZMod.castHom (pow_dvd_pow 2 (by omega : e - m ≤ e)) (ZMod (2 ^ (e - m)))) (defect1 2 e a b y)).val) := by
        rw [hb]
        exact fun hh => hndiv ((dvd_castHom_val (by omega) (by
          have hv := vcap_le 2 (e - 2 * m) (defect2 2 e a b y).val
          omega) (defect1 2 e a b y)).mp hh)
      have hG : (∑ w : ZMod (2 ^ (e - m)),
            (χ (thetaTwo e m 1)) ^ (((ZMod.castHom (pow_dvd_pow 2 (by omega : e - m ≤ e)) (ZMod (2 ^ (e - m)))) (defect1 2 e a b y) * w
              - ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ (e - m)))
                * (ZMod.castHom (pow_dvd_pow 2 (by omega : e - m ≤ e)) (ZMod (2 ^ (e - m)))) (defect2 2 e a b y) * w ^ 2).val)) = 0 := by
        have hnorm : ‖∑ w : ZMod (2 ^ (e - m)),
              (χ (thetaTwo e m 1)) ^ (((ZMod.castHom (pow_dvd_pow 2 (by omega : e - m ≤ e)) (ZMod (2 ^ (e - m)))) (defect1 2 e a b y) * w
                - ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ (e - m)))
                  * (ZMod.castHom (pow_dvd_pow 2 (by omega : e - m ≤ e)) (ZMod (2 ^ (e - m)))) (defect2 2 e a b y) * w ^ 2).val)‖ = 0 := by
          refine le_antisymm ?_ (norm_nonneg _)
          refine hg.trans (le_of_eq ?_)
          rw [if_neg hndiv', mul_zero]
        exact norm_eq_zero.mp hnorm
      have hsum_eq : (∑ w : ZMod (2 ^ (e - m)),
            (χ (thetaTwo e m 1)) ^ (((ZMod.castHom (pow_dvd_pow 2 (by omega : e - m ≤ e)) (ZMod (2 ^ (e - m)))) (defect1 2 e a b y) * w
              - ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ (e - m)))
                * ((ZMod.castHom (pow_dvd_pow 2 (by omega : e - m ≤ e)) (ZMod (2 ^ (e - m)))) (defect2 2 e a b y) * w ^ 2)).val))
          = ∑ w : ZMod (2 ^ (e - m)),
            (χ (thetaTwo e m 1)) ^ (((ZMod.castHom (pow_dvd_pow 2 (by omega : e - m ≤ e)) (ZMod (2 ^ (e - m)))) (defect1 2 e a b y) * w
              - ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ (e - m)))
                * (ZMod.castHom (pow_dvd_pow 2 (by omega : e - m ≤ e)) (ZMod (2 ^ (e - m)))) (defect2 2 e a b y) * w ^ 2).val) := by
        refine Finset.sum_congr rfl (fun w _ => ?_)
        congr 1
        congr 1
        ring
      rw [hfac, hsum_eq, hG, mul_zero]
    · have he2 : e = 2 := by omega
      have hm1 : m = 1 := by omega
      subst he2
      subst hm1
      have hb0 : vcap 2 (2 - 2 * 1) (defect2 2 2 a b y).val = 0 := by
        rw [show (2 : ℕ) - 2 * 1 = 0 by norm_num]
        exact vcap_two_zero _
      have hone : (2 : ℕ) ^ (1 + vcap 2 (2 - 2 * 1) (defect2 2 2 a b y).val - 1) = 1 := by
        rw [hb0]
        norm_num
      exact absurd ⟨hU, by rw [hone]; exact one_dvd _⟩ h
  · rw [Finset.sum_eq_zero (fun w _ => twoPow_innerSum_vanishing hm h2 χ a b y hU w)]



/-- Assembly: reindex `x = y + 2^m w`, apply the per-`y` bound, factor out `2^(e/2)`. -/
theorem corr6_twoPow_gaussTwo_le_aux {e m : ℕ} (hm : 1 ≤ m) (h3 : e + 1 ≤ 3 * m) (h2 : 2 * m ≤ e)
    (χ : DirichletCharacter ℂ (2 ^ e)) (hχ : χ.IsPrimitive) (a b : Fin 3 → ℕ) :
    ‖∑ x : ZMod (2 ^ e), χ (∏ l : Fin 3, (x + (a l : ZMod (2 ^ e))))
        * (starRingEnd ℂ) (χ (∏ l : Fin 3, (x + (b l : ZMod (2 ^ e)))))‖
      ≤ (2 : ℝ) ^ ((e : ℝ) / 2) * gaussTwoRHS2 e m a b := by
  classical
  have hreindex := sum_reindex_twoPow hm h2 (fun x : ZMod (2 ^ e) =>
      χ (∏ l : Fin 3, (x + (a l : ZMod (2 ^ e))))
        * (starRingEnd ℂ) (χ (∏ l : Fin 3, (x + (b l : ZMod (2 ^ e))))))
  have key : ‖∑ x : ZMod (2 ^ e), χ (∏ l : Fin 3, (x + (a l : ZMod (2 ^ e))))
        * (starRingEnd ℂ) (χ (∏ l : Fin 3, (x + (b l : ZMod (2 ^ e)))))‖
      ≤ (2 : ℝ) ^ ((e : ℝ) / 2) * ∑ y ∈ Finset.range (2 ^ m),
          (if UnitAt 2 y a b ∧ 2 ^ (m + vcap 2 (e - 2 * m) (defect2 2 e a b y).val - 1)
                ∣ (defect1 2 e a b y).val
           then (2 : ℝ) ^ ((vcap 2 (e - 2 * m) (defect2 2 e a b y).val : ℝ) / 2) else 0) := by
    rw [hreindex]
    have hstep : (∑ y ∈ Finset.range (2 ^ m),
          ‖∑ w : ZMod (2 ^ (e - m)),
            χ (∏ l : Fin 3, (((y : ℕ) : ZMod (2 ^ e)) + ((2 ^ m * w.val : ℕ) : ZMod (2 ^ e)) + (a l : ZMod (2 ^ e))))
            * (starRingEnd ℂ) (χ (∏ l : Fin 3, (((y : ℕ) : ZMod (2 ^ e))
                + ((2 ^ m * w.val : ℕ) : ZMod (2 ^ e)) + (b l : ZMod (2 ^ e)))))‖)
        ≤ ∑ y ∈ Finset.range (2 ^ m), ((2 : ℝ) ^ ((e : ℝ) / 2)
            * (if UnitAt 2 y a b ∧ 2 ^ (m + vcap 2 (e - 2 * m) (defect2 2 e a b y).val - 1)
                  ∣ (defect1 2 e a b y).val
               then (2 : ℝ) ^ ((vcap 2 (e - 2 * m) (defect2 2 e a b y).val : ℝ) / 2) else 0)) := by
      refine Finset.sum_le_sum (fun y hy => ?_)
      by_cases hc : UnitAt 2 y a b ∧
          2 ^ (m + vcap 2 (e - 2 * m) (defect2 2 e a b y).val - 1) ∣ (defect1 2 e a b y).val
      · rw [if_pos hc]
        rw [Finset.sum_congr rfl (fun w _ => summand_form_congr χ a b y w)]
        exact inner_bound_pos hm h3 h2 χ hχ a b y hc.1 hc.2
      · rw [if_neg hc,
          Finset.sum_congr rfl (fun w _ => summand_form_congr χ a b y w),
          inner_bound_zero hm h3 h2 χ hχ a b y hc]
        simp
    exact (norm_sum_le _ _).trans (hstep.trans (le_of_eq (Finset.mul_sum _ _ _).symm))
  exact key


end Work.ZeroFreeTables.P9F.TwoPowB

namespace Work.ZeroFreeTables.P9F

open Work.LinnikBurgess

/-- Lemma A_2 at `p = 2`, in the `gaussSum` bubble. -/
theorem corr6_twoPow_gaussTwo_le_aux {e m : ℕ} (hm : 1 ≤ m) (h3 : e + 1 ≤ 3 * m) (h2 : 2 * m ≤ e)
    (χ : DirichletCharacter ℂ (2 ^ e)) (hχ : χ.IsPrimitive) (a b : Fin 3 → ℕ) :
    ‖∑ x : ZMod (2 ^ e), χ (∏ l : Fin 3, (x + (a l : ZMod (2 ^ e))))
        * (starRingEnd ℂ) (χ (∏ l : Fin 3, (x + (b l : ZMod (2 ^ e)))))‖
      ≤ (2 : ℝ) ^ ((e : ℝ) / 2) * gaussTwoRHS2 e m a b :=
  TwoPowB.corr6_twoPow_gaussTwo_le_aux hm h3 h2 χ hχ a b

end Work.ZeroFreeTables.P9F
