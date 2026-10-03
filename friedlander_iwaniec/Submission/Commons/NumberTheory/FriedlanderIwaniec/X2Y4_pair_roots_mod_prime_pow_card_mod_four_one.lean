import Mathlib
import Submission.Commons.NumberTheory.FriedlanderIwaniec.sq_sum_sq_root_count_prime_pow
import Submission.Commons.NumberTheory.FriedlanderIwaniec.sq_roots_neg_one_mod_prime_pow_eq_two
import Submission.Commons.Data.Nat.padicValNat_factorization
import Submission.Commons.Data.ZMod.range_card_eq_subtype
import Submission.Commons.GroupTheory.Cardinality.card_eq_sum_card_fiber

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.style.haveILetI false

namespace Commons.NumberTheory.FriedlanderIwaniec

open Finset

/-- `p`-adic valuation of an element of `ZMod (p ^ e)`, defined to be `e` at `0`. -/
def X2Y4_valZ (p e : ℕ) (y : ZMod (p ^ e)) : ℕ := if y = 0 then e else padicValNat p y.val

lemma X2Y4_valZ_le {p e : ℕ} (hp : p.Prime) (y : ZMod (p ^ e)) :
    X2Y4_valZ p e y ≤ e := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [X2Y4_valZ]
  split_ifs with hy
  · rfl
  · by_contra h
    have hge : e + 1 ≤ padicValNat p y.val := by omega
    have hval : y.val ≠ 0 := fun h0 => hy (by rw [← ZMod.natCast_zmod_val y, h0]; simp)
    have hdvd : p ^ (e + 1) ∣ y.val := (padicValNat_dvd_iff_le hval).mpr hge
    have hdvd' : p ^ e ∣ y.val := dvd_trans (Nat.pow_dvd_pow p (by omega)) hdvd
    exact hval (Nat.eq_zero_of_dvd_of_lt hdvd' (ZMod.val_lt y))

/-- The number of square-zero elements of `ZMod (p ^ e)`. -/
lemma X2Y4_ncard_sq_zero_prime_pow {p e : ℕ} (hp : p.Prime) (he : 1 ≤ e) :
    ({α : ZMod (p ^ e) | α ^ 2 = 0}).ncard = p ^ (e / 2) := by
  haveI : NeZero (p ^ e) := ⟨pow_ne_zero e hp.ne_zero⟩
  rw [ncard_zmod_eq_range (n := p ^ e) (ψ := fun α : ZMod (p ^ e) => α ^ 2 = 0)]
  have h2 : ((Finset.range (p ^ e)).filter (fun r : ℕ => (r : ZMod (p ^ e)) ^ 2 = 0))
      = ((Finset.range (p ^ e)).filter (fun r : ℕ => p ^ e ∣ r ^ 2)) := by
    apply Finset.filter_congr
    intro r _
    rw [← Nat.cast_pow, ZMod.natCast_eq_zero_iff]
  rw [h2]
  exact card_filter_range_sq_dvd_prime_pow p e hp he

/-- The number of `x` with `x ^ 2 + y ^ 4 = 0` in `ZMod (p ^ e)` depends only on the
`p`-adic valuation of `y`. -/
lemma X2Y4_fiber_ncard {p e : ℕ} (hp : p.Prime) (hp1 : p % 4 = 1) (he : 1 ≤ e)
    (y : ZMod (p ^ e)) :
    ({x : ZMod (p ^ e) | x ^ 2 + y ^ 4 = 0}).ncard =
      (if 4 * X2Y4_valZ p e y < e then 2 * p ^ (2 * X2Y4_valZ p e y) else p ^ (e / 2)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  by_cases hy : y = 0
  · subst hy
    have hval : X2Y4_valZ p e 0 = e := by simp [X2Y4_valZ]
    rw [hval, if_neg (by omega)]
    have hset : ({x : ZMod (p ^ e) | x ^ 2 + (0 : ZMod (p ^ e)) ^ 4 = 0} : Set (ZMod (p ^ e)))
        = {x : ZMod (p ^ e) | x ^ 2 = 0} := by
      ext x; simp
    rw [hset]
    exact X2Y4_ncard_sq_zero_prime_pow hp he
  · obtain ⟨hfac, hunit⟩ :=
      Commons.Data.Nat.padicValNat_factorization (p := p) (d := y.val)
        (fun h0 => hy (by rw [← ZMod.natCast_zmod_val y, h0]; simp))
    set v := padicValNat p y.val with hv
    set u := y.val / p ^ v with hu
    have hval : X2Y4_valZ p e y = v := by simp [X2Y4_valZ, hy, hv]
    rw [hval]
    have hy2 : y = ((p ^ v * u : ℕ) : ZMod (p ^ e)) := by
      rw [← ZMod.natCast_zmod_val y, hfac, hu]
    have hy4 : y ^ 4 = (((p ^ (2 * v) * u ^ 2 : ℕ)) : ZMod (p ^ e)) ^ 2 := by
      rw [hy2, ← Nat.cast_pow, ← Nat.cast_pow]
      congr 1
      ring
    by_cases h4v : 4 * v < e
    · rw [if_pos h4v]
      have h2c : 2 * (2 * v) < e := by omega
      have hu2 : ¬ p ∣ u ^ 2 := fun h => hunit (hp.dvd_of_dvd_pow h)
      have hred := ncard_sq_add_sq_prime_pow_reduction (p := p) (e := e) (c := 2 * v) (u := u ^ 2)
        hp he hu2 h2c
      rw [← hy4] at hred
      rw [hred]
      have hroot : ({γ : ZMod (p ^ (e - 2 * (2 * v))) | γ ^ 2 = -1}).ncard = 2 :=
        sq_roots_neg_one_mod_prime_pow_eq_two hp hp1 (by omega)
      rw [hroot, mul_comm]
    · rw [if_neg h4v]
      have hy40 : y ^ 4 = 0 := by
        rw [hy4, ← Nat.cast_pow, ZMod.natCast_eq_zero_iff]
        refine ⟨p ^ (4 * v - e) * u ^ 4, ?_⟩
        have h1 : (p ^ (2 * v) * u ^ 2) ^ 2 = p ^ (4 * v) * u ^ 4 := by
          rw [mul_pow, ← pow_mul, ← pow_mul]
          rw [show 2 * v * 2 = 4 * v by ring, show 2 * 2 = 4 by norm_num]
        rw [h1]
        have h2 : p ^ (4 * v) = p ^ e * p ^ (4 * v - e) := by
          rw [← pow_add, Nat.add_sub_of_le (by omega)]
        rw [h2]
        ring
      have hset : ({x : ZMod (p ^ e) | x ^ 2 + y ^ 4 = 0} : Set (ZMod (p ^ e)))
          = {x : ZMod (p ^ e) | x ^ 2 = 0} := by
        ext x; simp [hy40]
      rw [hset]
      exact X2Y4_ncard_sq_zero_prime_pow hp he


/-- Membership criterion for a prescribed valuation, valid when the modulus is `p ^ e`
with `r < p ^ e` and the target valuation is `< e`. -/
lemma X2Y4_valZ_eq_iff {p e a r : ℕ} (hp : p.Prime) (hr : r < p ^ e) (ha : a < e) :
    ((if r = 0 then e else padicValNat p r) = a) ↔ (p ^ a ∣ r ∧ ¬ p ^ (a + 1) ∣ r) := by
  haveI : Fact p.Prime := ⟨hp⟩
  rcases eq_or_ne r 0 with h0 | hr0
  · subst h0
    constructor
    · intro h
      rw [if_pos rfl] at h
      exact absurd h.symm ha.ne
    · rintro ⟨-, h2⟩
      exact absurd (dvd_zero _) h2
  · have hne : (if r = 0 then e else padicValNat p r) = padicValNat p r := if_neg hr0
    rw [hne]
    constructor
    · intro h
      refine ⟨(padicValNat_dvd_iff_le hr0).mpr (le_of_eq h.symm), ?_⟩
      intro hd
      have := (padicValNat_dvd_iff_le hr0).mp hd
      omega
    · rintro ⟨h1, h2⟩
      have hge : a ≤ padicValNat p r := (padicValNat_dvd_iff_le hr0).mp h1
      have hlt : padicValNat p r < a + 1 := by
        by_contra hcon
        exact h2 ((padicValNat_dvd_iff_le hr0).mpr (by omega))
      omega

/-- The number of elements of `ZMod (p ^ e)` with a prescribed `p`-adic valuation. -/
lemma X2Y4_card_valZ_stratum {p e a : ℕ} (hp : p.Prime) (ha : a ≤ e) :
    ({y : ZMod (p ^ e) | X2Y4_valZ p e y = a}).ncard
      = if a < e then p ^ (e - a - 1) * (p - 1) else 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero (p ^ e) := ⟨pow_ne_zero e hp.ne_zero⟩
  rw [ncard_zmod_eq_range (n := p ^ e) (ψ := fun y : ZMod (p ^ e) => X2Y4_valZ p e y = a)]
  have hcongr : ∀ r ∈ Finset.range (p ^ e),
      (X2Y4_valZ p e (r : ZMod (p ^ e)) = a) ↔ ((if r = 0 then e else padicValNat p r) = a) := by
    intro r hr
    rw [Finset.mem_range] at hr
    simp only [X2Y4_valZ]
    by_cases hr0 : r = 0
    · subst hr0; simp
    · have hne : ¬ ((r : ZMod (p ^ e)) = 0) := by
        rw [ZMod.natCast_eq_zero_iff]
        intro hd; exact hr0 (Nat.eq_zero_of_dvd_of_lt hd hr)
      rw [if_neg hne, if_neg hr0, ZMod.val_cast_of_lt hr]
  rw [Finset.filter_congr hcongr]
  by_cases hae : a < e
  · rw [if_pos hae]
    have hiff : ∀ r ∈ Finset.range (p ^ e),
        (((if r = 0 then e else padicValNat p r) = a) ↔ (p ^ a ∣ r ∧ ¬ p ^ (a + 1) ∣ r)) :=
      fun r hr => X2Y4_valZ_eq_iff hp (Finset.mem_range.mp hr) hae
    rw [Finset.filter_congr hiff]
    have hset : ((Finset.range (p ^ e)).filter (fun r => p ^ a ∣ r ∧ ¬ p ^ (a + 1) ∣ r))
        = ((Finset.range (p ^ e)).filter (fun r => p ^ a ∣ r)) \
          ((Finset.range (p ^ e)).filter (fun r => p ^ (a + 1) ∣ r)) := by
      ext r
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_sdiff]
      tauto
    rw [hset, Finset.card_sdiff]
    have hsub : ((Finset.range (p ^ e)).filter (fun r => p ^ (a + 1) ∣ r))
        ⊆ ((Finset.range (p ^ e)).filter (fun r => p ^ a ∣ r)) := by
      intro r hr
      simp only [Finset.mem_filter, Finset.mem_range] at hr ⊢
      exact ⟨hr.1, dvd_trans (Nat.pow_dvd_pow p (by omega)) hr.2⟩
    rw [Finset.inter_eq_left.mpr hsub]
    rw [card_filter_range_dvd (p ^ e) (p ^ a) (pow_pos hp.pos a) (Nat.pow_dvd_pow p ha),
        card_filter_range_dvd (p ^ e) (p ^ (a + 1)) (pow_pos hp.pos (a + 1))
          (Nat.pow_dvd_pow p (by omega)),
        Nat.pow_div ha hp.pos, Nat.pow_div (by omega : a + 1 ≤ e) hp.pos,
        show e - (a + 1) = e - a - 1 by omega]
    have h1 : p ^ (e - a) = p ^ (e - a - 1) * p := by
      rw [← pow_succ, show e - a - 1 + 1 = e - a by omega]
    rw [h1, Nat.mul_sub_left_distrib, mul_one]
  · rw [if_neg hae]
    have hae' : a = e := by omega
    rw [hae']
    have hset : ((Finset.range (p ^ e)).filter (fun r => ((if r = 0 then e else padicValNat p r) = e)))
        = {0} := by
      ext r
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
      constructor
      · rintro ⟨hr, hre⟩
        by_contra hr0
        rw [if_neg hr0] at hre
        have hlt : padicValNat p r < e := by
          by_contra hcon
          have hd : p ^ e ∣ r := (padicValNat_dvd_iff_le hr0).mpr (by omega)
          exact hr0 (Nat.eq_zero_of_dvd_of_lt hd hr)
        omega
      · rintro rfl
        refine ⟨pow_pos hp.pos e, ?_⟩
        rw [if_pos rfl]
    rw [hset, Finset.card_singleton]


/-- Splitting the solution set according to the second coordinate. -/
lemma X2Y4_ncard_eq_sum_fiber {p e : ℕ} [NeZero (p ^ e)] :
    ({z : ZMod (p ^ e) × ZMod (p ^ e) | z.1 ^ 2 + z.2 ^ 4 = 0}).ncard =
      ∑ y : ZMod (p ^ e), ({x : ZMod (p ^ e) | x ^ 2 + y ^ 4 = 0}).ncard := by
  classical
  set S : Set (ZMod (p ^ e) × ZMod (p ^ e)) := {z | z.1 ^ 2 + z.2 ^ 4 = 0} with hS
  have h1 : S.ncard = Fintype.card {z : ZMod (p ^ e) × ZMod (p ^ e) // z ∈ S} :=
    (Set.fintypeCard_eq_ncard S).symm
  rw [h1]
  rw [Commons.GroupTheory.Cardinality.card_eq_sum_card_fiber
        (fun z : {z : ZMod (p ^ e) × ZMod (p ^ e) // z ∈ S} => z.1.2)]
  apply Finset.sum_congr rfl
  intro y _
  rw [← (Set.fintypeCard_eq_ncard ({x : ZMod (p ^ e) | x ^ 2 + y ^ 4 = 0}))]
  refine Fintype.card_congr ?_
  refine ⟨fun w => ⟨w.1.1.1, ?_⟩, fun x => ⟨⟨(x.1, y), ?_⟩, rfl⟩, ?_, ?_⟩
  · have h := w.1.2
    change w.1.1.1 ^ 2 + w.1.1.2 ^ 4 = 0 at h
    rw [w.2] at h
    exact h
  · change x.1 ^ 2 + y ^ 4 = 0
    exact x.2
  · intro w
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext rfl w.2.symm
  · intro x
    rfl


/-- `(p - 1) * (1 + p + ... + p ^ (n-1)) = p ^ n - 1`. -/
lemma X2Y4_mul_geom_sum (p n : ℕ) (hp : 1 ≤ p) :
    (p - 1) * (∑ i ∈ Finset.range n, p ^ i) = p ^ n - 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    have h2 : (p - 1) * p ^ n = p ^ (n + 1) - p ^ n := by
      rw [mul_comm, Nat.mul_sub_left_distrib, mul_one, pow_succ]
    rw [h2]
    have h1 : 1 ≤ p ^ n := Nat.one_le_pow n p (by omega)
    have h3 : p ^ n ≤ p ^ (n + 1) := pow_le_pow_right₀ hp (Nat.le_succ n)
    omega


/-- `∑_{a < m} f a = f 0 + ∑_{j = 1}^{m-1} f j` for `m ≥ 1`. -/
lemma X2Y4_sum_range_eq_head_add_sum_Icc {M : Type*} [AddCommMonoid M] (f : ℕ → M) {m : ℕ}
    (hm : 1 ≤ m) :
    (∑ a ∈ Finset.range m, f a) = f 0 + ∑ j ∈ Finset.Icc 1 (m - 1), f j := by
  conv_lhs => rw [show m = (m - 1) + 1 by omega]
  rw [Finset.sum_range_succ']
  conv_lhs => rw [add_comm]
  congr 1
  trans ∑ k ∈ Finset.range (m - 1), f (1 + k)
  · apply Finset.sum_congr rfl
    intro k _
    rw [Nat.add_comm]
  · rw [← Finset.sum_Ico_eq_sum_range f 1 m]
    have hIco : Finset.Ico 1 m = Finset.Icc 1 (m - 1) := by
      ext x
      simp only [Finset.mem_Ico, Finset.mem_Icc]
      omega
    rw [hIco]

/-- Evaluation of the closed-form sum obtained after grouping by the `p`-adic
valuation of the second coordinate. -/
lemma X2Y4_sum_closed {p e : ℕ} (hp : p.Prime) (he : 1 ≤ e) :
    (∑ a ∈ Finset.range (e + 1),
        (if a < e then p ^ (e - a - 1) * (p - 1) else 1) *
          (if 4 * a < e then 2 * p ^ (2 * a) else p ^ (e / 2)))
      = 2 * p ^ (e - 1) * (p - 1) +
          (∑ j ∈ Finset.Icc 1 ((e + 3) / 4 - 1), 2 * p ^ (e + j - 1) * (p - 1)) +
          p ^ (e / 2 + e - (e + 3) / 4) := by
  have hp1 : 1 ≤ p := by have := hp.two_le; omega
  set m : ℕ := (e + 3) / 4 with hm
  have hm1 : 1 ≤ m := by omega
  have hmle : m ≤ e := by omega
  have hstep1 : (∑ a ∈ Finset.range (e + 1),
        (if a < e then p ^ (e - a - 1) * (p - 1) else 1) *
          (if 4 * a < e then 2 * p ^ (2 * a) else p ^ (e / 2)))
      = (∑ a ∈ Finset.range e,
        (if a < e then p ^ (e - a - 1) * (p - 1) else 1) *
          (if 4 * a < e then 2 * p ^ (2 * a) else p ^ (e / 2))) + p ^ (e / 2) := by
    rw [Finset.sum_range_succ, if_neg (show ¬ e < e by omega),
      if_neg (show ¬ 4 * e < e by omega), one_mul]
  have hsum_e : (∑ a ∈ Finset.range e,
        (if a < e then p ^ (e - a - 1) * (p - 1) else 1) *
          (if 4 * a < e then 2 * p ^ (2 * a) else p ^ (e / 2)))
      = (∑ a ∈ Finset.range m, 2 * p ^ (e + a - 1) * (p - 1)) +
          p ^ (e / 2) * (p ^ (e - m) - 1) := by
    trans ∑ a ∈ Finset.range e,
        p ^ (e - a - 1) * (p - 1) * (if 4 * a < e then 2 * p ^ (2 * a) else p ^ (e / 2))
    · apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.mem_range] at ha
      rw [if_pos ha]
    · rw [← Finset.sum_range_add_sum_Ico
        (fun a => p ^ (e - a - 1) * (p - 1) *
          (if 4 * a < e then 2 * p ^ (2 * a) else p ^ (e / 2))) hmle]
      congr 1
      · apply Finset.sum_congr rfl
        intro a ha
        rw [Finset.mem_range] at ha
        rw [if_pos (show 4 * a < e by omega)]
        have hpow : p ^ (e - a - 1) * p ^ (2 * a) = p ^ (e + a - 1) := by
          rw [← pow_add, show e - a - 1 + 2 * a = e + a - 1 by omega]
        calc p ^ (e - a - 1) * (p - 1) * (2 * p ^ (2 * a))
            = 2 * (p ^ (e - a - 1) * p ^ (2 * a)) * (p - 1) := by ring
          _ = 2 * p ^ (e + a - 1) * (p - 1) := by rw [hpow]
      · trans p ^ (e / 2) * (∑ a ∈ Finset.Ico m e, p ^ (e - a - 1) * (p - 1))
        · rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro a ha
          rw [Finset.mem_Ico] at ha
          rw [if_neg (show ¬ 4 * a < e by omega)]
          ring
        · congr 1
          have hgeom : (∑ a ∈ Finset.Ico m e, p ^ (e - a - 1) * (p - 1))
              = (p - 1) * (∑ j ∈ Finset.range (e - m), p ^ j) := by
            calc (∑ a ∈ Finset.Ico m e, p ^ (e - a - 1) * (p - 1))
                = ∑ k ∈ Finset.range (e - m), p ^ (e - (m + k) - 1) * (p - 1) := by
                  rw [Finset.sum_Ico_eq_sum_range
                    (fun a => p ^ (e - a - 1) * (p - 1)) m e]
              _ = ∑ k ∈ Finset.range (e - m), p ^ ((e - m) - 1 - k) * (p - 1) := by
                  apply Finset.sum_congr rfl
                  intro k hk
                  rw [Finset.mem_range] at hk
                  rw [show e - (m + k) - 1 = (e - m) - 1 - k by omega]
              _ = (∑ k ∈ Finset.range (e - m), p ^ ((e - m) - 1 - k)) * (p - 1) :=
                  (Finset.sum_mul (Finset.range (e - m))
                    (fun k => p ^ ((e - m) - 1 - k)) (p - 1)).symm
              _ = (∑ j ∈ Finset.range (e - m), p ^ j) * (p - 1) := by
                  rw [Finset.sum_range_reflect (fun j => p ^ j) (e - m)]
              _ = (p - 1) * (∑ j ∈ Finset.range (e - m), p ^ j) :=
                  mul_comm _ _
          rw [hgeom, X2Y4_mul_geom_sum p (e - m) hp1]
  have hsum_m : (∑ a ∈ Finset.range m, 2 * p ^ (e + a - 1) * (p - 1))
      = 2 * p ^ (e - 1) * (p - 1) +
          ∑ j ∈ Finset.Icc 1 (m - 1), 2 * p ^ (e + j - 1) * (p - 1) := by
    rw [X2Y4_sum_range_eq_head_add_sum_Icc (fun a => 2 * p ^ (e + a - 1) * (p - 1)) hm1]
    congr 1
  have hb : p ^ (e / 2) * (p ^ (e - m) - 1) + p ^ (e / 2) = p ^ (e / 2 + e - m) := by
    rw [Nat.mul_sub_left_distrib, mul_one]
    rw [Nat.sub_add_cancel (Nat.le_mul_of_pos_right _ (pow_pos hp.pos _))]
    rw [← pow_add, show e / 2 + (e - m) = e / 2 + e - m by omega]
  calc (∑ a ∈ Finset.range (e + 1),
        (if a < e then p ^ (e - a - 1) * (p - 1) else 1) *
          (if 4 * a < e then 2 * p ^ (2 * a) else p ^ (e / 2)))
      = (∑ a ∈ Finset.range e,
        (if a < e then p ^ (e - a - 1) * (p - 1) else 1) *
          (if 4 * a < e then 2 * p ^ (2 * a) else p ^ (e / 2))) + p ^ (e / 2) := hstep1
    _ = ((∑ a ∈ Finset.range m, 2 * p ^ (e + a - 1) * (p - 1)) +
          p ^ (e / 2) * (p ^ (e - m) - 1)) + p ^ (e / 2) := by rw [hsum_e]
    _ = (∑ a ∈ Finset.range m, 2 * p ^ (e + a - 1) * (p - 1)) + p ^ (e / 2 + e - m) := by
          rw [Nat.add_assoc, hb]
    _ = (2 * p ^ (e - 1) * (p - 1) +
          ∑ j ∈ Finset.Icc 1 (m - 1), 2 * p ^ (e + j - 1) * (p - 1)) +
          p ^ (e / 2 + e - m) := by rw [hsum_m]
    _ = 2 * p ^ (e - 1) * (p - 1) +
          (∑ j ∈ Finset.Icc 1 ((e + 3) / 4 - 1), 2 * p ^ (e + j - 1) * (p - 1)) +
          p ^ (e / 2 + e - (e + 3) / 4) := by rw [hm]


theorem X2Y4_pair_roots_mod_prime_pow_card_mod_four_one
    {p e : ℕ} (hp : p.Prime) (hp1 : p % 4 = 1) (he : 1 ≤ e) :
    ({(x : ZMod (p ^ e) × ZMod (p ^ e)) | x.1 ^ 2 + x.2 ^ 4 = 0}).ncard =
      2 * p ^ (e - 1) * (p - 1) +
        (∑ j ∈ Finset.Icc 1 ((e + 3) / 4 - 1), 2 * p ^ (e + j - 1) * (p - 1)) +
        p ^ (e / 2 + e - (e + 3) / 4) := by
  haveI : NeZero (p ^ e) := ⟨pow_ne_zero e hp.ne_zero⟩
  rw [X2Y4_ncard_eq_sum_fiber]
  simp only [X2Y4_fiber_ncard hp hp1 he]
  rw [← Finset.sum_fiberwise_of_maps_to (s := (Finset.univ : Finset (ZMod (p ^ e))))
        (t := Finset.range (e + 1)) (g := fun y : ZMod (p ^ e) => X2Y4_valZ p e y)
        (f := fun y : ZMod (p ^ e) =>
          if 4 * X2Y4_valZ p e y < e then 2 * p ^ (2 * X2Y4_valZ p e y) else p ^ (e / 2))
        (fun y _ => Finset.mem_range.mpr (Nat.lt_succ_of_le (X2Y4_valZ_le hp y)))]
  have hsummand : ∀ a ∈ Finset.range (e + 1),
      (∑ y ∈ Finset.univ.filter (fun y : ZMod (p ^ e) => X2Y4_valZ p e y = a),
        (if 4 * X2Y4_valZ p e y < e then 2 * p ^ (2 * X2Y4_valZ p e y) else p ^ (e / 2)))
        = (if a < e then p ^ (e - a - 1) * (p - 1) else 1) *
            (if 4 * a < e then 2 * p ^ (2 * a) else p ^ (e / 2)) := by
    intro a ha
    rw [Finset.mem_range] at ha
    have hconst : ∀ y ∈ Finset.univ.filter (fun y : ZMod (p ^ e) => X2Y4_valZ p e y = a),
        (if 4 * X2Y4_valZ p e y < e then 2 * p ^ (2 * X2Y4_valZ p e y) else p ^ (e / 2))
          = (if 4 * a < e then 2 * p ^ (2 * a) else p ^ (e / 2)) := by
      intro y hy
      rw [Finset.mem_filter] at hy
      rw [hy.2]
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, smul_eq_mul]
    congr 1
    rw [← Fintype.card_subtype (fun y : ZMod (p ^ e) => X2Y4_valZ p e y = a)]
    rw [show Fintype.card {y : ZMod (p ^ e) // X2Y4_valZ p e y = a}
        = Fintype.card (↥{y : ZMod (p ^ e) | X2Y4_valZ p e y = a}) from rfl,
      Set.fintypeCard_eq_ncard]
    exact X2Y4_card_valZ_stratum hp (by omega)
  rw [Finset.sum_congr rfl hsummand]
  exact X2Y4_sum_closed hp he

end Commons.NumberTheory.FriedlanderIwaniec
