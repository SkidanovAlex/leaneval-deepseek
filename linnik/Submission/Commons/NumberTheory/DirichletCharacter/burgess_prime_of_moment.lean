import Mathlib
import Submission.Commons.NumberTheory.CharacterSum.dyadic_interval_decomposition
import Submission.Commons.NumberTheory.CharacterSum.card_floor_close_offdiag
import Submission.Commons.NumberTheory.CharacterSum.card_floor_close_diag
import Submission.Commons.NumberTheory.DivisorSum.gcd_sum_square_bound
import Submission.Commons.Analysis.MeanInequalities.sum_mul_pow_le
import Submission.Commons.Analysis.MeanInequalities.sum_mul_sq_le
import Submission.Commons.NumberTheory.Auxiliary.ediv_add_sub_ediv_le
import Submission.Commons.NumberTheory.DirichletCharacter.charSum_range_le_polyaVinogradov
import Submission.Commons.Analysis.Real.log_pow_le_mul_rpow

set_option maxHeartbeats 8000000

open Finset

namespace Commons.NumberTheory.DirichletCharacter
/-! ## Interval character sums over integers -/

variable {q : ℕ}

/-- Sum of `χ` over the integer interval `(a, b]`. -/
noncomputable def cSum (χ : DirichletCharacter ℂ q) (a b : ℤ) : ℂ :=
  ∑ m ∈ Finset.Ioc a b, χ (m : ZMod q)

lemma cSum_add_q (χ : DirichletCharacter ℂ q) (a b : ℤ) :
    cSum χ (a + q) (b + q) = cSum χ a b := by
  unfold cSum
  refine Finset.sum_bij (fun m _ => m - (q:ℤ)) ?_ ?_ ?_ ?_
  · intro m hm; rw [Finset.mem_Ioc] at hm ⊢; constructor <;> omega
  · intro m1 hm1 m2 hm2 h; omega
  · intro m hm
    rw [Finset.mem_Ioc] at hm
    refine ⟨m + (q:ℤ), ?_, by omega⟩
    rw [Finset.mem_Ioc]; constructor <;> omega
  · intro m hm; congr 1; simp

lemma cSum_split (χ : DirichletCharacter ℂ q) {a b c : ℤ} (hab : a ≤ b) (hbc : b ≤ c) :
    cSum χ a c = cSum χ a b + cSum χ b c := by
  have hunion : Finset.Ioc a b ∪ Finset.Ioc b c = Finset.Ioc a c :=
    Finset.Ioc_union_Ioc_eq_Ioc hab hbc
  have hdisj : Disjoint (Finset.Ioc a b) (Finset.Ioc b c) :=
    Finset.Ioc_disjoint_Ioc_of_le (c := b) (d := c) le_rfl
  unfold cSum
  rw [← hunion, Finset.sum_union hdisj]

lemma norm_cSum_le_card (χ : DirichletCharacter ℂ q) (a b : ℤ) :
    ‖cSum χ a b‖ ≤ ((Finset.Ioc a b).card : ℝ) := by
  unfold cSum
  calc ‖∑ m ∈ Finset.Ioc a b, χ (m : ZMod q)‖ ≤ ∑ m ∈ Finset.Ioc a b, ‖χ (m : ZMod q)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _m ∈ Finset.Ioc a b, (1:ℝ) :=
        Finset.sum_le_sum (fun m _ => DirichletCharacter.norm_le_one χ _)
    _ = ((Finset.Ioc a b).card : ℝ) := by simp

lemma norm_cSum_le (χ : DirichletCharacter ℂ q) {a b : ℤ} (hab : a ≤ b) :
    ‖cSum χ a b‖ ≤ ((b - a : ℤ) : ℝ) := by
  have hcard : (Finset.Ioc a b).card = (b - a).toNat := Int.card_Ioc a b
  calc ‖cSum χ a b‖ ≤ ((Finset.Ioc a b).card : ℝ) := norm_cSum_le_card χ a b
    _ = ((b - a).toNat : ℝ) := by rw [hcard]
    _ = ((b - a : ℤ) : ℝ) := by
        rw [show ((b - a).toNat : ℝ) = (((b - a).toNat : ℤ) : ℝ) by push_cast; ring]
        rw [Int.toNat_of_nonneg (by omega)]

/-- Shift-invariance of a sum over a complete residue system. -/
lemma sum_Icc_periodic {p : ℕ} (hp : 0 < p) (G : ℤ → ℝ) (hper : ∀ x, G (x + p) = G x)
    (a : ℤ) :
    ∑ x ∈ Finset.Icc a (a + p - 1), G x = ∑ r ∈ Finset.range p, G (r : ℤ) := by
  have hper' : Function.Periodic G (p:ℤ) := fun x => by have := hper x; simpa using this
  have key : ∀ x : ℤ, G x = G (x % (p:ℤ)) := by
    intro x
    have hx : x = (x % (p:ℤ)) + (x / (p:ℤ)) * (p:ℤ) := by
      have := Int.mul_ediv_add_emod x (p:ℤ); linarith [this]
    conv_lhs => rw [hx]
    have := hper'.int_mul (x / (p:ℤ)) (x % (p:ℤ))
    simpa using this
  have hpz : (0:ℤ) < (p:ℤ) := by exact_mod_cast hp
  have hltp : (p:ℤ) ≠ 0 := by omega
  refine Finset.sum_bij (fun x _ => (x % (p:ℤ)).toNat) ?_ ?_ ?_ ?_
  · intro x hx
    rw [Finset.mem_Icc] at hx
    rw [Finset.mem_range]
    exact (Int.toNat_lt (Int.emod_nonneg x hltp)).mpr (Int.emod_lt_of_pos x hpz)
  · intro x hx y hy hxy
    rw [Finset.mem_Icc] at hx hy
    have h1 : 0 ≤ x % (p:ℤ) := Int.emod_nonneg x hltp
    have h2 : 0 ≤ y % (p:ℤ) := Int.emod_nonneg y hltp
    have heq : x % (p:ℤ) = y % (p:ℤ) := by
      have := congrArg (fun n : ℕ => (n:ℤ)) hxy
      simpa [Int.toNat_of_nonneg h1, Int.toNat_of_nonneg h2] using this
    have hmod : (x - y) % (p:ℤ) = 0 :=
      (Int.emod_eq_emod_iff_emod_sub_eq_zero (m := x) (n := p) (k := y)).mp heq
    obtain ⟨c, hc⟩ : (p:ℤ) ∣ (x - y) := by rw [Int.dvd_iff_emod_eq_zero]; exact hmod
    have habs : |x - y| < (p:ℤ) := by rw [abs_lt]; constructor <;> omega
    rw [hc, abs_mul, abs_of_pos hpz] at habs
    have hc0 : c = 0 := by
      by_contra hcne
      have hc1 : (1:ℤ) ≤ |c| := by have : (0:ℤ) < |c| := abs_pos.mpr hcne; omega
      nlinarith
    rw [hc0, mul_zero] at hc; omega
  · intro r hr
    rw [Finset.mem_range] at hr
    refine ⟨a + (((r:ℤ) - a) % (p:ℤ)), ?_, ?_⟩
    · rw [Finset.mem_Icc]
      have h1 : 0 ≤ ((r:ℤ) - a) % (p:ℤ) := Int.emod_nonneg _ (by omega)
      have h2 : ((r:ℤ) - a) % (p:ℤ) < (p:ℤ) := Int.emod_lt_of_pos _ hpz
      constructor <;> omega
    · have hsub : (a + ((r:ℤ) - a) % (p:ℤ)) - (r:ℤ)
            = -((p:ℤ) * (((r:ℤ) - a) / (p:ℤ))) := by
        have := Int.mul_ediv_add_emod ((r:ℤ) - a) (p:ℤ); linarith [this]
      have hmod0 : (a + ((r:ℤ) - a) % (p:ℤ)) % (p:ℤ) = (r:ℤ) % (p:ℤ) := by
        refine (Int.emod_eq_emod_iff_emod_sub_eq_zero (m := a + ((r:ℤ)-a) % (p:ℤ))
          (n := p) (k := r)).mpr ?_
        rw [hsub]
        exact Int.emod_eq_zero_of_dvd ⟨-(((r:ℤ)-a)/(p:ℤ)), by ring⟩
      have hrr : (r:ℤ) % (p:ℤ) = (r:ℤ) :=
        Int.emod_eq_of_lt (Int.natCast_nonneg r) (by exact_mod_cast hr)
      rw [hmod0, hrr]
      exact Nat.cast_injective (Int.toNat_of_nonneg (Int.natCast_nonneg r))
  · intro x hx
    have h1 : 0 ≤ x % (p:ℤ) := Int.emod_nonneg x hltp
    rw [Int.toNat_of_nonneg h1]
    exact key x

/-! ## The dyadic decomposition of an interval sum -/

/-- Dyadic index family: `(d,v)` with `d ≤ t` and `v < 2^(d+1)`. -/
def famIdx (t : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (t + 1)).biUnion fun d =>
    (Finset.range (2 ^ (d + 1))).image fun v => (d, v)

lemma mem_famIdx {t d v : ℕ} : (d, v) ∈ famIdx t ↔ d ≤ t ∧ v < 2 ^ (d + 1) := by
  rw [famIdx, Finset.mem_biUnion]
  constructor
  · rintro ⟨d', hd', hmem⟩
    rw [Finset.mem_image] at hmem
    obtain ⟨v', hv', heq⟩ := hmem
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    have hd'' : d' < t+1 := Finset.mem_range.mp hd'
    exact ⟨by omega, Finset.mem_range.mp hv'⟩
  · rintro ⟨hd, hv⟩
    exact ⟨d, Finset.mem_range.mpr (by omega), by
      rw [Finset.mem_image]; exact ⟨v, Finset.mem_range.mpr hv, rfl⟩⟩

/-- The value attached to a dyadic index. -/
noncomputable def famVal (f : ℤ → ℂ) (t : ℕ) (a : ℤ) (p : ℕ × ℕ) : ℝ :=
  ‖∑ m ∈ Finset.Ioc (a + (p.2 : ℤ) * (2:ℤ)^(t - p.1))
      (a + (p.2 : ℤ) * (2:ℤ)^(t - p.1) + (2:ℤ)^(t - p.1)), f m‖

lemma famVal_nonneg (f : ℤ → ℂ) (t : ℕ) (a : ℤ) (p : ℕ × ℕ) : 0 ≤ famVal f t a p :=
  norm_nonneg _

lemma famVal_succ_low (f : ℤ → ℂ) (t : ℕ) (a : ℤ) (d v : ℕ) :
    famVal f (t+1) a (d+1, v) = famVal f t a (d, v) := by
  simp only [famVal]
  have h1 : (t + 1) - (d+1) = t - d := by omega
  rw [h1]

lemma famVal_succ_high (f : ℤ → ℂ) (t : ℕ) (a : ℤ) (d v : ℕ) (hd : d ≤ t) :
    famVal f (t+1) a (d+1, v + 2^d) = famVal f t (a + 2^t) (d, v) := by
  have h1 : (t + 1) - (d+1) = t - d := by omega
  simp only [famVal]
  rw [h1]
  have e1 : a + ((v + 2^d : ℕ) : ℤ) * (2:ℤ)^(t-d) = (a + (2:ℤ)^t) + (v:ℤ)*(2:ℤ)^(t-d) := by
    push_cast
    rw [add_mul, ← pow_add, Nat.add_sub_cancel' hd]
    ring
  rw [e1]

lemma famVal_one_zero (f : ℤ → ℂ) (t : ℕ) (a : ℤ) :
    famVal f (t+1) a (1,0) = ‖∑ m ∈ Finset.Ioc a (a + 2^t), f m‖ := by
  simp only [famVal]
  norm_num

/-- Dyadic decomposition of an interval sum. -/
lemma exists_dyadic_decomp (f : ℤ → ℂ) :
    ∀ (t : ℕ) (a : ℤ) (k : ℕ), k ≤ 2^t → ∃ S : Finset (ℕ × ℕ), S ⊆ famIdx t ∧ S.card ≤ t + 1 ∧
      ‖∑ m ∈ Finset.Ioc a (a + k), f m‖ ≤ ∑ p ∈ S, famVal f t a p := by
  intro t
  induction t with
  | zero =>
    intro a k hk
    have hk' : k ≤ 1 := by simpa using hk
    interval_cases k
    · exact ⟨∅, by simp, by simp, by simp⟩
    · refine ⟨{(0,0)}, ?_, ?_, ?_⟩
      · intro p hp
        rw [Finset.mem_singleton] at hp; subst hp
        rw [mem_famIdx]; constructor <;> norm_num
      · simp
      · rw [Finset.sum_singleton]
        have hs1 : Finset.Ioc a (a + (1:ℤ)) = {(a+1)} := by
          ext x; rw [Finset.mem_Ioc, Finset.mem_singleton]; constructor <;> intro hx <;> omega
        have hs2 : Finset.Ioc a (a + (1:ℕ)) = {(a+1)} := by
          ext x; rw [Finset.mem_Ioc, Finset.mem_singleton]; constructor <;> intro hx <;> omega
        have h2 : famVal f 0 a (0,0) = ‖f (a+1)‖ := by
          simp only [famVal]
          norm_num
          rw [hs1, Finset.sum_singleton]
        rw [h2]
        have h : (∑ m ∈ Finset.Ioc a (a + (1:ℕ)), f m) = f (a+1) := by
          rw [hs2, Finset.sum_singleton]
        rw [h]
  | succ t ih =>
    intro a k hk
    by_cases hcase : k ≤ 2^t
    · obtain ⟨S, hS, hcard, hbound⟩ := ih a k hcase
      refine ⟨S.image (fun p => (p.1+1, p.2)), ?_, ?_, ?_⟩
      · intro q hq
        rw [Finset.mem_image] at hq
        obtain ⟨p, hp, rfl⟩ := hq
        have hp' := hS hp
        rw [mem_famIdx] at hp' ⊢
        obtain ⟨h1, h2⟩ := hp'
        exact ⟨by omega, by
          calc p.2 < 2^(p.1+1) := h2
            _ ≤ 2^(p.1+1+1) := Nat.pow_le_pow_right (by norm_num) (by omega)⟩
      · rw [Finset.card_image_of_injOn (by
          intro p hp q hq hpq
          simp only [Prod.mk.injEq] at hpq
          exact Prod.ext (by omega) hpq.2)]
        omega
      · refine hbound.trans (le_of_eq ?_)
        rw [Finset.sum_image (by
          intro p hp q hq hpq
          simp only [Prod.mk.injEq] at hpq
          exact Prod.ext (by omega) hpq.2)]
        refine Finset.sum_congr rfl (fun p hp => ?_)
        exact (famVal_succ_low f t a p.1 p.2).symm
    · rw [not_le] at hcase
      obtain ⟨k₁, rfl⟩ : ∃ k₁, k = 2^t + k₁ := ⟨k - 2^t, by omega⟩
      have hk₁ : k₁ ≤ 2^t := by omega
      obtain ⟨S, hS, hcard, hbound⟩ := ih (a + 2^t) k₁ hk₁
      set emb : ℕ × ℕ → ℕ × ℕ := fun p => (p.1+1, p.2 + 2^(p.1)) with hemb
      have hemb_inj : ∀ p ∈ S, ∀ q ∈ S, emb p = emb q → p = q := by
        intro p hp q hq hpq
        simp only [hemb, Prod.mk.injEq] at hpq
        have h1 : p.1 = q.1 := by omega
        have h2 : p.2 = q.2 := by
          have := hpq.2
          rw [h1] at this
          omega
        exact Prod.ext h1 h2
      have hone : (1,0) ∉ S.image emb := by
        intro hmem
        rw [Finset.mem_image] at hmem
        obtain ⟨p, hp, heq⟩ := hmem
        simp only [hemb, Prod.mk.injEq] at heq
        have hpos : 0 < 2^(p.1) := Nat.two_pow_pos _
        omega
      have hJsub : insert (1,0) (S.image emb) ⊆ famIdx (t+1) := by
        intro q hq
        rw [Finset.mem_insert] at hq
        rcases hq with rfl | hq
        · rw [mem_famIdx]; constructor <;> norm_num
        · rw [Finset.mem_image] at hq
          obtain ⟨p, hp, rfl⟩ := hq
          have hp' := hS hp
          rw [mem_famIdx] at hp' ⊢
          obtain ⟨h1, h2⟩ := hp'
          constructor
          · omega
          · have h3 : 2^(p.1) < 2^(p.1+1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
            calc p.2 + 2^(p.1) < 2^(p.1+1) + 2^(p.1+1) := by omega
              _ = 2^(p.1+1+1) := by ring
      have hJcard : (insert (1,0) (S.image emb)).card ≤ t + 1 + 1 := by
        calc (insert (1,0) (S.image emb)).card ≤ (S.image emb).card + 1 := Finset.card_insert_le _ _
          _ ≤ S.card + 1 := by
              have := Finset.card_image_le (f := emb) (s := S)
              omega
          _ ≤ (t + 1) + 1 := by omega
      refine ⟨insert (1,0) (S.image emb), hJsub, hJcard, ?_⟩
      have hdisj : Disjoint (Finset.Ioc a (a + 2^t) : Finset ℤ)
          (Finset.Ioc (a + 2^t) (a + 2^t + k₁)) :=
        Finset.Ioc_disjoint_Ioc_of_le le_rfl
      have hIoc : (Finset.Ioc a ((a + 2^t) + (k₁:ℤ)) : Finset ℤ)
          = Finset.Ioc a (a + 2^t) ∪ Finset.Ioc (a + 2^t) (a + 2^t + k₁) :=
        (Finset.Ioc_union_Ioc_eq_Ioc (le_add_of_nonneg_right (show (0:ℤ) ≤ (2^t : ℤ) by positivity))
          (le_add_of_nonneg_right (show (0:ℤ) ≤ (k₁ : ℤ) by positivity))).symm
      have hsplit : (∑ m ∈ Finset.Ioc a (a + ((2^t + k₁ : ℕ) : ℤ)), f m)
          = (∑ m ∈ Finset.Ioc a (a + 2^t), f m)
            + (∑ m ∈ Finset.Ioc (a + 2^t) (a + 2^t + k₁), f m) := by
        have h1 : a + ((2^t + k₁ : ℕ) : ℤ) = (a + 2^t) + k₁ := by push_cast; ring
        rw [h1, hIoc, Finset.sum_union hdisj]
      have hterm2 : ∀ p ∈ S, famVal f (t+1) a (emb p) = famVal f t (a + 2^t) p := by
        intro p hp
        have hp' := hS hp
        rw [mem_famIdx] at hp'
        exact famVal_succ_high f t a p.1 p.2 hp'.1
      have hsum : (∑ p ∈ S, famVal f (t+1) a (emb p)) = ∑ p ∈ S, famVal f t (a + 2^t) p :=
        Finset.sum_congr rfl hterm2
      rw [Finset.sum_insert hone, Finset.sum_image hemb_inj]
      rw [hsplit]
      refine (norm_add_le _ _).trans ?_
      refine add_le_add ?_ ?_
      · rw [famVal_one_zero]
      · rw [hsum]; exact hbound


/-- `supShift χ n K` is the maximum of `‖cSum χ n (n+j)‖` for `j ≤ K`. -/
noncomputable def supShift (χ : DirichletCharacter ℂ q) (n : ℤ) (K : ℕ) : ℝ :=
  (Finset.range (K+1)).sup' ⟨0, by simp⟩ (fun j => ‖cSum χ n (n + j)‖)

lemma le_supShift (χ : DirichletCharacter ℂ q) (n : ℤ) (K : ℕ) {j : ℕ} (hj : j ≤ K) :
    ‖cSum χ n (n + j)‖ ≤ supShift χ n K := by
  unfold supShift
  exact Finset.le_sup' (s := Finset.range (K+1)) (f := fun j => ‖cSum χ n (n + j)‖)
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))

lemma supShift_nonneg (χ : DirichletCharacter ℂ q) (n : ℤ) (K : ℕ) : 0 ≤ supShift χ n K :=
  le_trans (norm_nonneg _) (le_supShift χ n K (j := 0) (by omega))

/-- The ℕ-indexed interval sum equals the ℤ-indexed one. -/
lemma cSum_natCast (χ : DirichletCharacter ℂ q) (N H : ℕ) :
    cSum χ (N:ℤ) ((N:ℤ) + H) = ∑ n ∈ Finset.Ioc N (N+H), χ (n : ZMod q) := by
  have hset : Finset.Ioc ((N:ℤ)) ((N:ℤ) + H)
      = (Finset.Ioc N (N+H)).image (fun n : ℕ => (n:ℤ)) := by
    ext m
    constructor
    · intro hm
      rw [Finset.mem_Ioc] at hm
      rw [Finset.mem_image]
      refine ⟨m.toNat, ?_, ?_⟩
      · rw [Finset.mem_Ioc]
        constructor
        · have : (N:ℤ) < m := hm.1
          omega
        · have : m ≤ (N:ℤ) + H := hm.2
          omega
      · exact Int.toNat_of_nonneg (by omega)
    · intro hm
      rw [Finset.mem_image] at hm
      obtain ⟨n, hn, rfl⟩ := hm
      rw [Finset.mem_Ioc] at hn ⊢
      constructor
      · exact_mod_cast hn.1
      · push_cast; exact_mod_cast hn.2
  unfold cSum
  rw [hset, Finset.sum_image (by
    intro a ha b hb hab
    exact Nat.cast_injective hab)]
  simp

/-- The "principle": a sum over an interval starting at `lo` is controlled by the maximal
short sum based at a nearby point `n`. -/
lemma cSum_le_two_supShift (χ : DirichletCharacter ℂ q) {n lo : ℤ} {len h : ℕ} (hn : n ≤ lo)
    (hlen : len ≤ h) (hnh : lo - h < n) :
    ‖cSum χ lo (lo + len)‖ ≤ 2 * supShift χ n (2*h) := by
  have hsplit := cSum_split χ hn (show lo ≤ lo + (len:ℤ) by
    have := (show (0:ℤ) ≤ (len:ℤ) by exact_mod_cast Nat.zero_le len); linarith)
  have hdiff : cSum χ lo (lo + len) = cSum χ n (lo + len) - cSum χ n lo := by
    rw [hsplit]; ring
  have h1 : (lo - n).toNat ≤ 2*h := by
    have h0 : (0:ℤ) ≤ lo - n := by omega
    have : lo - n < (h:ℤ) := by omega
    omega
  have h2 : ((lo + len) - n).toNat ≤ 2*h := by
    have h0 : (0:ℤ) ≤ (lo + len) - n := by omega
    have : (lo + len) - n < 2 * (h:ℤ) := by
      have : (len:ℤ) ≤ h := by exact_mod_cast hlen
      omega
    omega
  have hb1 : ‖cSum χ n (lo + len)‖ = ‖cSum χ n (n + (((lo + len) - n).toNat : ℤ))‖ := by
    congr 1
    rw [Int.toNat_of_nonneg (by omega : (0:ℤ) ≤ (lo+len) - n)]; ring
  have hb2 : ‖cSum χ n lo‖ = ‖cSum χ n (n + ((lo - n).toNat : ℤ))‖ := by
    congr 1
    rw [Int.toNat_of_nonneg (by omega : (0:ℤ) ≤ lo - n)]; ring
  rw [hdiff]
  refine (norm_sub_le _ _).trans ?_
  rw [hb1, hb2, two_mul]
  exact add_le_add (le_supShift χ n (2*h) h2) (le_supShift χ n (2*h) h1)

/-- Power-mean inequality for a finite sum of nonnegative reals. -/
lemma sum_pow_le_card_pow_mul_sum_pow {ι : Type*} (s : Finset ι) (a : ι → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i) (n : ℕ) (hn : 1 ≤ n) :
    (∑ i ∈ s, a i) ^ n ≤ ((s.card : ℝ)) ^ n * ∑ i ∈ s, (a i) ^ n := by
  rcases s.eq_empty_or_nonempty with rfl | hne
  · rw [Finset.sum_empty, zero_pow (by omega)]; simp
  set M : ℝ := ∑ i ∈ s, (a i) ^ n with hM
  have hMnn : 0 ≤ M := by
    rw [hM]; exact Finset.sum_nonneg (fun i hi => pow_nonneg (ha i hi) n)
  have hn0 : n ≠ 0 := by omega
  have hle : ∀ i ∈ s, a i ≤ M ^ ((n:ℝ)⁻¹) := by
    intro i hi
    have h1 : (a i)^n ≤ M := by
      rw [hM]; exact Finset.single_le_sum (fun j hj => pow_nonneg (ha j hj) n) hi
    have h2 : (M ^ ((n:ℝ)⁻¹)) ^ n = M := Real.rpow_inv_natCast_pow hMnn hn0
    rw [← h2] at h1
    exact (pow_le_pow_iff_left₀ (ha i hi) (Real.rpow_nonneg hMnn _) hn0).mp h1
  have h3 : (∑ i ∈ s, a i) ≤ (s.card : ℝ) * M ^ ((n:ℝ)⁻¹) := by
    calc (∑ i ∈ s, a i) ≤ ∑ _i ∈ s, M ^ ((n:ℝ)⁻¹) := Finset.sum_le_sum hle
      _ = s.card • (M ^ ((n:ℝ)⁻¹)) := Finset.sum_const _
      _ = (s.card : ℝ) * M ^ ((n:ℝ)⁻¹) := by simp
  calc (∑ i ∈ s, a i) ^ n ≤ ((s.card : ℝ) * M ^ ((n:ℝ)⁻¹)) ^ n :=
        pow_le_pow_left₀ (Finset.sum_nonneg ha) h3 n
    _ = (s.card : ℝ) ^ n * M := by
        rw [mul_pow, Real.rpow_inv_natCast_pow hMnn hn0]
    _ = (s.card : ℝ) ^ n * ∑ i ∈ s, (a i) ^ n := by rw [hM]




/-! ## Maximal moment bounds from the plain moment bounds -/

/-- Power bound for a single interval sum, from the dyadic decomposition. -/
lemma norm_pow_le_famSum (f : ℤ → ℂ) (t : ℕ) (n : ℤ) (k : ℕ) (hk : k ≤ 2^t) (r : ℕ)
    (hr : 1 ≤ r) :
    ‖∑ m ∈ Finset.Ioc n (n + k), f m‖ ^ (2*r) ≤ ((t+1:ℝ)) ^ (2*r) *
      ∑ p ∈ famIdx t, (famVal f t n p) ^ (2*r) := by
  obtain ⟨S, hS, hcard, hbound⟩ := exists_dyadic_decomp f t n k hk
  have h1 : ‖∑ m ∈ Finset.Ioc n (n + k), f m‖ ^ (2*r)
      ≤ (∑ p ∈ S, famVal f t n p) ^ (2*r) :=
    pow_le_pow_left₀ (norm_nonneg _) hbound _
  have h2 : (∑ p ∈ S, famVal f t n p) ^ (2*r)
      ≤ ((S.card : ℝ)) ^ (2*r) * ∑ p ∈ S, (famVal f t n p) ^ (2*r) :=
    sum_pow_le_card_pow_mul_sum_pow S _ (fun p _ => famVal_nonneg ..) (2*r) (by omega)
  have h3 : ((S.card : ℝ)) ^ (2*r) * ∑ p ∈ S, (famVal f t n p) ^ (2*r)
      ≤ ((t+1:ℝ)) ^ (2*r) * ∑ p ∈ famIdx t, (famVal f t n p) ^ (2*r) := by
    refine mul_le_mul (pow_le_pow_left₀ (by positivity) (by exact_mod_cast hcard) (2*r)) ?_ ?_ ?_
    · exact Finset.sum_le_sum_of_subset_of_nonneg hS (fun i hi _ => pow_nonneg (famVal_nonneg ..) _)
    · exact Finset.sum_nonneg (fun i hi => pow_nonneg (famVal_nonneg ..) _)
    · exact pow_nonneg (by positivity) _
  linarith

lemma supShift_pow_le_fam (χ : DirichletCharacter ℂ q) (t : ℕ) (n : ℤ) (K : ℕ)
    (hK : K ≤ 2^t) (r : ℕ) (hr : 1 ≤ r) :
    (supShift χ n K) ^ (2*r) ≤ ((t+1:ℝ)) ^ (2*r) *
      ∑ p ∈ famIdx t, (famVal (fun m : ℤ => χ (m : ZMod q)) t n p) ^ (2*r) := by
  set D : ℝ := ((t+1:ℝ)) ^ (2*r) *
      ∑ p ∈ famIdx t, (famVal (fun m : ℤ => χ (m : ZMod q)) t n p) ^ (2*r) with hD
  have hDnn : 0 ≤ D := by
    rw [hD]
    refine mul_nonneg (by positivity) ?_
    exact Finset.sum_nonneg (fun p _ => pow_nonneg (famVal_nonneg ..) _)
  have key : supShift χ n K ≤ D ^ (((2*r : ℕ) : ℝ))⁻¹ := by
    unfold supShift
    refine Finset.sup'_le _ _ (fun j hj => ?_)
    rw [Finset.mem_range] at hj
    have hj' : j ≤ K := by omega
    have h := norm_pow_le_famSum (fun m : ℤ => χ (m : ZMod q)) t n j (le_trans hj' hK) r hr
    rw [← hD] at h
    have h2 : (D ^ (((2*r : ℕ) : ℝ))⁻¹) ^ (2*r) = D :=
      Real.rpow_inv_natCast_pow (x := D) (n := 2*r) hDnn (by omega)
    rw [← h2] at h
    exact (pow_le_pow_iff_left₀ (n := 2*r) (norm_nonneg _) (Real.rpow_nonneg hDnn _)
      (by omega : 2*r ≠ 0)).mp h
  calc (supShift χ n K) ^ (2*r) ≤ (D ^ (((2*r : ℕ) : ℝ))⁻¹) ^ (2*r) :=
        pow_le_pow_left₀ (supShift_nonneg ..) key _
    _ = D := Real.rpow_inv_natCast_pow (x := D) (n := 2*r) hDnn (by omega)

/-- Periodicity of the windowed moment sums. -/
lemma windowMom_eq_rangeSum (χ : DirichletCharacter ℂ q) (r L : ℕ) (a : ℤ) :
    ∑ x ∈ Finset.Icc a (a + q - 1), ‖cSum χ x (x + L)‖ ^ (2*r)
      = ∑ m ∈ Finset.range q, ‖cSum χ (m:ℤ) ((m:ℤ) + L)‖ ^ (2*r) := by
  have hper : ∀ x : ℤ, (fun y : ℤ => ‖cSum χ y (y + L)‖ ^ (2*r)) (x + q)
      = (fun y : ℤ => ‖cSum χ y (y + L)‖ ^ (2*r)) x := by
    intro x
    have h1 : x + (q:ℤ) + (L:ℤ) = (x + (L:ℤ)) + q := by ring
    have := cSum_add_q χ x (x + (L:ℤ))
    simp only [h1]
    rw [this]
  rcases Nat.eq_zero_or_pos q with hq | hq
  · subst hq
    simp
  · exact sum_Icc_periodic hq _ hper a


/-! ## Sums over the dyadic family, geometric bounds -/

lemma sum_famIdx {t : ℕ} (f : ℕ × ℕ → ℝ) :
    ∑ p ∈ famIdx t, f p = ∑ d ∈ Finset.range (t+1), ∑ v ∈ Finset.range (2^(d+1)), f (d, v) := by
  rw [famIdx, Finset.sum_biUnion]
  · refine Finset.sum_congr rfl (fun d hd => ?_)
    rw [Finset.sum_image]
    intro a ha b hb hab
    simpa using hab
  · intro d hd d' hd' hne
    rw [Function.onFun, Finset.disjoint_left]
    intro x hx hx'
    rw [Finset.mem_image] at hx hx'
    obtain ⟨v, hv, hvx⟩ := hx
    obtain ⟨v', hv', hvx'⟩ := hx'
    have h1 : d = d' := by
      have := congrArg Prod.fst (hvx.trans hvx'.symm)
      simpa using this
    exact hne h1

lemma geom_pow_sum_le (r : ℕ) (hr : 2 ≤ r) (t : ℕ) :
    ∑ d ∈ Finset.range (t+1), (2:ℝ)^(d+1) * ((2:ℝ)^(t-d))^r ≤ 4 * ((2:ℝ)^t)^r := by
  induction t with
  | zero => norm_num
  | succ t ih =>
    rw [Finset.sum_range_succ']
    have hstep : ∀ d : ℕ, (2:ℝ)^(d+1+1) * ((2:ℝ)^(t+1-(d+1)))^r
        = 2 * ((2:ℝ)^(d+1) * ((2:ℝ)^(t-d))^r) := by
      intro d
      have h1 : t+1-(d+1) = t-d := by omega
      rw [h1, pow_succ]
      ring
    rw [Finset.sum_congr rfl (fun d _ => hstep d), ← Finset.mul_sum]
    have h0 : (2:ℝ)^(0+1) * ((2:ℝ)^(t+1-0))^r = 2 * ((2:ℝ)^(t+1))^r := by norm_num
    rw [h0]
    have h2r : ((2:ℝ)^(t+1))^r = (2:ℝ)^r * ((2:ℝ)^t)^r := by
      rw [pow_succ', mul_pow]
    have h8 : (8:ℝ) ≤ (2:ℝ)^r * 2 := by
      calc (8:ℝ) = 2^3 := by norm_num
        _ ≤ 2^(r+1) := by
            apply pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2)
            omega
        _ = 2^r * 2 := by rw [pow_succ]
    have hkey : 2 * (4 * ((2:ℝ)^t)^r) + 2 * ((2:ℝ)^r * ((2:ℝ)^t)^r) ≤ 4 * ((2:ℝ)^(t+1))^r := by
      rw [h2r]
      have hnn : (0:ℝ) ≤ ((2:ℝ)^t)^r := pow_nonneg (by norm_num) _
      have hpos : (0:ℝ) < (2:ℝ)^r := pow_pos (by norm_num) _
      nlinarith [h8, hnn, hpos]
    calc 2 * (∑ d ∈ Finset.range (t+1), (2:ℝ)^(d+1) * ((2:ℝ)^(t-d))^r)
          + 2 * ((2:ℝ)^(t+1))^r
        ≤ 2 * (4 * ((2:ℝ)^t)^r) + 2 * ((2:ℝ)^r * ((2:ℝ)^t)^r) := by
          rw [h2r]
          linarith [ih]
      _ ≤ 4 * ((2:ℝ)^(t+1))^r := hkey


/-! ## The maximal moment bound over a residue system -/

lemma sum_fam_double (t : ℕ) (Cm : ℝ) (A : ℕ → ℝ) :
    ∑ d ∈ Finset.range (t+1), ∑ v ∈ Finset.range (2^(d+1)), Cm * A d
      = Cm * ∑ d ∈ Finset.range (t+1), (2:ℝ)^(d+1) * A d := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun d hd => ?_)
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_pow]
  push_cast
  ring

lemma sum_fam_split (t : ℕ) (q s : ℝ) (f g : ℕ → ℝ) :
    ∑ d ∈ Finset.range (t+1), (2:ℝ)^(d+1) * (q * f d + g d * s)
      = q * ∑ d ∈ Finset.range (t+1), (2:ℝ)^(d+1) * f d
        + s * ∑ d ∈ Finset.range (t+1), (2:ℝ)^(d+1) * g d := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun d hd => ?_)
  ring

lemma supShift_window_le (χ : DirichletCharacter ℂ q) (Cm : ℝ) (r : ℕ) (hr1 : 1 ≤ r) (hr2 : 2 ≤ r)
    (hmom : ∀ L : ℕ, L ≤ q → ∑ m ∈ Finset.range q, ‖cSum χ (m:ℤ) ((m:ℤ) + L)‖ ^ (2*r)
      ≤ Cm * ((q:ℝ) * (L:ℝ)^r + (L:ℝ)^(2*r) * Real.sqrt q))
    (t : ℕ) (a : ℤ) (K : ℕ) (hK : K ≤ 2^t) (h2t : 2^t ≤ q) :
    ∑ x ∈ Finset.Icc a (a + q - 1), (supShift χ x K) ^ (2*r)
      ≤ ((t+1:ℝ))^(2*r) * (4 * Cm *
          ((q:ℝ) * ((2:ℝ)^t)^r + ((2:ℝ)^t)^(2*r) * Real.sqrt q)) := by
  have hstep : ∑ x ∈ Finset.Icc a (a + q - 1), (supShift χ x K)^(2*r)
      ≤ ((t+1:ℝ))^(2*r) * ∑ x ∈ Finset.Icc a (a + q - 1),
          ∑ p ∈ famIdx t, (famVal (fun m : ℤ => χ (m : ZMod q)) t x p)^(2*r) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun x hx => supShift_pow_le_fam χ t x K hK r hr1)
  refine hstep.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  rw [Finset.sum_comm, sum_famIdx]
  have hpoint : ∀ d ∈ Finset.range (t+1), ∀ v ∈ Finset.range (2^(d+1)),
      ∑ x ∈ Finset.Icc a (a + q - 1), (famVal (fun m : ℤ => χ (m : ZMod q)) t x (d,v))^(2*r)
        ≤ Cm * ((q:ℝ) * ((2:ℝ)^(t-d))^r + ((2:ℝ)^(t-d))^(2*r) * Real.sqrt q) := by
    intro d hd v hv
    have hterm : ∀ x : ℤ, (famVal (fun m : ℤ => χ (m : ZMod q)) t x (d,v))^(2*r)
        = ‖cSum χ (x + (v:ℤ) * (2:ℤ)^(t-d)) ((x + (v:ℤ) * (2:ℤ)^(t-d)) + 2^(t-d))‖^(2*r) := by
      intro x
      simp only [famVal, cSum, Nat.cast_pow]
    have hshift : ∑ x ∈ Finset.Icc a (a + q - 1),
          ‖cSum χ (x + (v:ℤ) * (2:ℤ)^(t-d)) ((x + (v:ℤ) * (2:ℤ)^(t-d)) + 2^(t-d))‖^(2*r)
        = ∑ y ∈ Finset.Icc (a + (v:ℤ) * (2:ℤ)^(t-d))
              (a + (v:ℤ) * (2:ℤ)^(t-d) + q - 1),
              ‖cSum χ y (y + 2^(t-d))‖^(2*r) := by
      refine Finset.sum_bij (fun x _ => x + (v:ℤ) * (2:ℤ)^(t-d)) ?_ ?_ ?_ ?_
      · intro x hx
        rw [Finset.mem_Icc] at hx ⊢
        constructor <;> linarith [hx.1, hx.2]
      · intro x hx y hy hxy
        linarith
      · intro y hy
        refine ⟨y - (v:ℤ) * (2:ℤ)^(t-d), ?_, by ring⟩
        rw [Finset.mem_Icc] at hy ⊢
        constructor <;> linarith [hy.1, hy.2]
      · intro x hx
        rfl
    rw [Finset.sum_congr rfl (fun x _ => hterm x), hshift]
    have hL := hmom (2^(t-d)) (by
      calc 2^(t-d) ≤ 2^t := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ ≤ q := h2t)
    have hcast : ((2^(t-d) : ℕ) : ℝ) = (2:ℝ)^(t-d) := by push_cast; ring
    rw [hcast] at hL
    exact (windowMom_eq_rangeSum χ r (2^(t-d)) (a + (v:ℤ) * (2:ℤ)^(t-d))).le.trans hL
  have h1 : ∑ d ∈ Finset.range (t+1), ∑ v ∈ Finset.range (2^(d+1)),
        ∑ x ∈ Finset.Icc a (a + q - 1),
          (famVal (fun m : ℤ => χ (m : ZMod q)) t x (d,v))^(2*r)
      ≤ ∑ d ∈ Finset.range (t+1), ∑ v ∈ Finset.range (2^(d+1)),
          Cm * ((q:ℝ) * ((2:ℝ)^(t-d))^r + ((2:ℝ)^(t-d))^(2*r) * Real.sqrt q) :=
    Finset.sum_le_sum (fun d hd => Finset.sum_le_sum (fun v hv => hpoint d hd v hv))
  refine h1.trans ?_
  rw [sum_fam_double t Cm (fun d => (q:ℝ) * ((2:ℝ)^(t-d))^r + ((2:ℝ)^(t-d))^(2*r) * Real.sqrt q)]
  rw [sum_fam_split t (q:ℝ) (Real.sqrt (q:ℝ))
      (fun d => ((2:ℝ)^(t-d))^r) (fun d => ((2:ℝ)^(t-d))^(2*r))]
  have h6 := geom_pow_sum_le r hr2 t
  have h7 := geom_pow_sum_le (2*r) (by omega) t
  have hsq : (0:ℝ) ≤ Real.sqrt (q:ℝ) := Real.sqrt_nonneg _
  have hq : (0:ℝ) ≤ (q:ℝ) := by positivity
  have hC : 0 ≤ Cm := by
    have hq1 : 1 ≤ q := le_trans (Nat.one_le_two_pow) h2t
    have h := hmom 1 hq1
    have h0 : (0:ℝ) ≤ ∑ m ∈ Finset.range q, ‖cSum χ (m:ℤ) ((m:ℤ) + ((1:ℕ):ℤ))‖ ^ (2*r) :=
      Finset.sum_nonneg (fun m _ => pow_nonneg (norm_nonneg _) _)
    have h1' : (0:ℝ) ≤ Cm * ((q:ℝ) * ((1:ℕ):ℝ)^r + ((1:ℕ):ℝ)^(2*r) * Real.sqrt q) := h0.trans h
    have h2' : (0:ℝ) < (q:ℝ) * ((1:ℕ):ℝ)^r + ((1:ℕ):ℝ)^(2*r) * Real.sqrt q := by
      simp only [Nat.cast_one, one_pow, mul_one, one_mul]
      have hq' : (0:ℝ) < (q:ℝ) := by exact_mod_cast hq1
      have := Real.sqrt_nonneg (q:ℝ)
      linarith
    exact (nonneg_of_mul_nonneg_left h1' h2')
  have hinner : (q:ℝ) * (∑ d ∈ Finset.range (t+1), ((2:ℝ)^(d+1) * ((2:ℝ)^(t-d))^r))
        + Real.sqrt (q:ℝ) * ∑ d ∈ Finset.range (t+1),
            ((2:ℝ)^(d+1) * ((2:ℝ)^(t-d))^(2*r))
      ≤ 4 * ((q:ℝ) * ((2:ℝ)^t)^r + ((2:ℝ)^t)^(2*r) * Real.sqrt q) := by
    calc (q:ℝ) * (∑ d ∈ Finset.range (t+1), ((2:ℝ)^(d+1) * ((2:ℝ)^(t-d))^r))
          + Real.sqrt (q:ℝ) * ∑ d ∈ Finset.range (t+1),
              ((2:ℝ)^(d+1) * ((2:ℝ)^(t-d))^(2*r))
        ≤ (q:ℝ) * (4 * ((2:ℝ)^t)^r) + Real.sqrt (q:ℝ) * (4 * ((2:ℝ)^t)^(2*r)) :=
          add_le_add (mul_le_mul_of_nonneg_left h6 hq) (mul_le_mul_of_nonneg_left h7 hsq)
      _ = 4 * ((q:ℝ) * ((2:ℝ)^t)^r + ((2:ℝ)^t)^(2*r) * Real.sqrt q) := by ring
  calc Cm * ((q:ℝ) * (∑ d ∈ Finset.range (t+1), ((2:ℝ)^(d+1) * ((2:ℝ)^(t-d))^r))
          + Real.sqrt (q:ℝ) * ∑ d ∈ Finset.range (t+1),
              ((2:ℝ)^(d+1) * ((2:ℝ)^(t-d))^(2*r)))
      ≤ Cm * (4 * ((q:ℝ) * ((2:ℝ)^t)^r + ((2:ℝ)^t)^(2*r) * Real.sqrt q)) :=
        mul_le_mul_of_nonneg_left hinner hC
    _ = 4 * Cm * ((q:ℝ) * ((2:ℝ)^t)^r + ((2:ℝ)^t)^(2*r) * Real.sqrt q) := by ring


/-! ## Polylog absorption -/

lemma log_pow_le_mul_rpow {ε : ℝ} (hε : 0 < ε) (A : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 1 ≤ x → (Real.log x) ^ A ≤ C * x ^ ε := by
  rcases Nat.eq_zero_or_pos A with hA | hA
  · refine ⟨1, one_pos, fun x hx => ?_⟩
    rw [hA, pow_zero, one_mul]
    exact Real.one_le_rpow hx hε.le
  · have hApos : (0:ℝ) < (A:ℝ) := by exact_mod_cast hA
    refine ⟨(A / ε)^A, by positivity, fun x hx => ?_⟩
    have hδpos : 0 < ε / (A:ℝ) := by positivity
    have hlog : Real.log x ≤ x^(ε/(A:ℝ)) / (ε/(A:ℝ)) := Real.log_le_rpow_div (by linarith) hδpos
    have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx
    have h1 : (Real.log x)^A ≤ (x^(ε/(A:ℝ)) / (ε/(A:ℝ)))^A := pow_le_pow_left₀ hlog0 hlog A
    have h2 : (x^(ε/(A:ℝ)) / (ε/(A:ℝ)))^A = x^ε / (ε/(A:ℝ))^A := by
      rw [div_pow, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith : (0:ℝ) ≤ x)]
      congr 2
      rw [mul_comm]
      field_simp
    refine h1.trans ?_
    rw [h2, div_eq_mul_inv, ← inv_pow, inv_div]
    exact le_of_eq (by ring)


lemma mem_Ioc_ediv_iff {L : ℤ} (hL : 0 < L) (X Y m : ℤ) :
    m ∈ Finset.Ioc (X / L) (Y / L) ↔ X < L * m ∧ L * m ≤ Y := by
  rw [Finset.mem_Ioc, Int.ediv_lt_iff_lt_mul hL, Int.le_ediv_iff_mul_le hL]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
  · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩

lemma zmod_mul_residue_unique {ℓ : ℕ} (hℓ0 : 0 < ℓ) {p : ℕ}
    (h : IsUnit ((p : ZMod ℓ))) (n : ℤ) :
    ∃! a : ℕ, a < ℓ ∧ ((a : ZMod ℓ)) * (p : ZMod ℓ) = (n : ZMod ℓ) := by
  haveI : NeZero ℓ := ⟨by omega⟩
  obtain ⟨u, hu⟩ := h
  refine ⟨(((n : ZMod ℓ)) * ↑(u⁻¹)).val, ⟨ZMod.val_lt _, ?_⟩, ?_⟩
  · rw [ZMod.natCast_zmod_val, ← hu, mul_assoc, Units.inv_mul, mul_one]
  · intro b hb
    obtain ⟨hb1, hb2⟩ := hb
    have hb2' : (b : ZMod ℓ) = (n : ZMod ℓ) * ↑(u⁻¹) := by
      have h1 : (b : ZMod ℓ) * (↑u : ZMod ℓ) = (n : ZMod ℓ) := by rw [← hb2, hu]
      calc (b : ZMod ℓ) = (b : ZMod ℓ) * ↑u * ↑(u⁻¹) := by
              rw [mul_assoc, Units.mul_inv, mul_one]
        _ = (n : ZMod ℓ) * ↑(u⁻¹) := by rw [h1]
    have hbv : b = (((n : ZMod ℓ)) * ↑(u⁻¹)).val := by
      have := congrArg ZMod.val hb2'
      rwa [ZMod.val_natCast, Nat.mod_eq_of_lt hb1] at this
    exact hbv

theorem cSum_ap_split {p : ℕ} [Fact p.Prime] (χ : DirichletCharacter ℂ p) {ℓ : ℕ}
    (hℓ0 : 0 < ℓ) (hℓp : ℓ < p) (N : ℤ) (H : ℕ) :
    cSum χ N (N + H) = χ (ℓ : ZMod p) *
      ∑ a ∈ Finset.range ℓ,
        cSum χ ((N - (a:ℤ) * p) / (ℓ:ℤ)) (((N + (H:ℤ)) - (a:ℤ) * p) / (ℓ:ℤ)) := by
  haveI : NeZero ℓ := ⟨by omega⟩
  have hp : p.Prime := Fact.out
  have hcop : Nat.Coprime p ℓ := (hp.coprime_iff_not_dvd (n := ℓ)).mpr (by
    intro hd
    have := Nat.le_of_dvd hℓ0 hd
    omega)
  have hunit : IsUnit ((p : ZMod ℓ)) := (ZMod.isUnit_iff_coprime p ℓ).mpr hcop
  have hL : (0:ℤ) < (ℓ:ℤ) := by exact_mod_cast hℓ0
  have hpz : ((p:ℤ)) ≠ 0 := by
    have : 0 < p := hp.pos
    exact_mod_cast (by omega : p ≠ 0)
  have hp0 : ((p : ZMod p)) = 0 := by
    simp [ZMod.natCast_self]
  have hkey : ∀ a m : ℤ, ((a * p + (ℓ:ℤ) * m : ℤ) : ZMod p)
      = (ℓ : ZMod p) * (m : ZMod p) := by
    intro a m
    push_cast
    rw [show ((a:ZMod p) * (p:ZMod p)) = 0 by rw [hp0, mul_zero]]
    ring
  have hlen : ∀ a : ℕ, (a:ℤ) * p < (a+1) * p := by
    intro a
    have : (0:ℤ) < p := by exact_mod_cast hp.pos
    nlinarith
  obtain ⟨u, hu⟩ := hunit
  have hsigma : (∑ x ∈ (Finset.range ℓ).sigma (fun a =>
        Finset.Ioc ((N - (a:ℤ) * p) / (ℓ:ℤ)) (((N + (H:ℤ)) - (a:ℤ) * p) / (ℓ:ℤ))),
        χ (ℓ : ZMod p) * χ (x.2 : ZMod p))
      = ∑ a ∈ Finset.range ℓ,
          ∑ m ∈ Finset.Ioc ((N - (a:ℤ) * p) / (ℓ:ℤ)) (((N + (H:ℤ)) - (a:ℤ) * p) / (ℓ:ℤ)),
            χ (ℓ : ZMod p) * χ (m : ZMod p) := by
    rw [Finset.sum_sigma]
  simp only [cSum, Finset.mul_sum]
  rw [← hsigma]
  symm
  refine Finset.sum_bij (fun x _ => (x.1 : ℤ) * p + (ℓ:ℤ) * x.2) ?_ ?_ ?_ ?_
  · -- maps into Ioc N (N+H)
    intro x hx
    rw [Finset.mem_sigma] at hx
    obtain ⟨ha, hm⟩ := hx
    rw [Finset.mem_range] at ha
    have hm' := (mem_Ioc_ediv_iff hL (N - (x.1:ℤ)*p) ((N + (H:ℤ)) - (x.1:ℤ)*p) x.2).mp hm
    rw [Finset.mem_Ioc]
    constructor <;> linarith [hm'.1, hm'.2]
  · -- injective
    rintro ⟨x1, x2⟩ hx ⟨y1, y2⟩ hy hxy
    rw [Finset.mem_sigma] at hx hy
    obtain ⟨hxa, hxm⟩ := hx
    obtain ⟨hya, hym⟩ := hy
    rw [Finset.mem_range] at hxa hya
    have hmod : ((x1 : ZMod ℓ)) * (p : ZMod ℓ) = ((y1 : ZMod ℓ)) * (p : ZMod ℓ) := by
      have h := congrArg (fun t : ℤ => (t : ZMod ℓ)) hxy
      push_cast at h
      simpa using h
    have h3 : ∀ z : ZMod ℓ, z * (p : ZMod ℓ) * ↑(u⁻¹) = z := by
      intro z
      rw [← hu, mul_assoc, Units.mul_inv, mul_one]
    have h1 : (x1 : ZMod ℓ) = (y1 : ZMod ℓ) := by
      calc (x1 : ZMod ℓ) = (x1 : ZMod ℓ) * (p : ZMod ℓ) * ↑(u⁻¹) := (h3 _).symm
        _ = (y1 : ZMod ℓ) * (p : ZMod ℓ) * ↑(u⁻¹) := by rw [hmod]
        _ = (y1 : ZMod ℓ) := h3 _
    have haeq : x1 = y1 := by
      have h2 := congrArg ZMod.val h1
      rwa [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt hxa, Nat.mod_eq_of_lt hya] at h2
    have hmeq : x2 = y2 := by
      have hh := hxy
      rw [haeq] at hh
      have : (ℓ:ℤ) * x2 = (ℓ:ℤ) * y2 := by linarith [hh]
      exact mul_left_cancel₀ (by omega : (ℓ:ℤ) ≠ 0) this
    rw [haeq, hmeq]
  · -- surjective
    intro n hn
    rw [Finset.mem_Ioc] at hn
    obtain ⟨ha, hq⟩ := zmod_mul_residue_unique hℓ0
      (show IsUnit ((p : ZMod ℓ)) from (ZMod.isUnit_iff_coprime p ℓ).mpr hcop) n
    have hdvd : (ℓ:ℤ) ∣ (n - (ha:ℤ) * p) := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd (n - (ha:ℤ)*p) ℓ]
      push_cast
      rw [hq.1.2]
      ring
    refine ⟨⟨ha, (n - (ha:ℤ) * p) / (ℓ:ℤ)⟩, ?_, ?_⟩
    · rw [Finset.mem_sigma]
      refine ⟨Finset.mem_range.mpr hq.1.1, ?_⟩
      rw [mem_Ioc_ediv_iff hL]
      have h1 : ((n - (ha:ℤ)*p) / (ℓ:ℤ)) * (ℓ:ℤ) = n - (ha:ℤ)*p :=
        Int.ediv_mul_cancel hdvd
      constructor <;> linarith [hn.1, hn.2, h1]
    · have h1 : ((n - (ha:ℤ)*p) / (ℓ:ℤ)) * (ℓ:ℤ) = n - (ha:ℤ)*p := Int.ediv_mul_cancel hdvd
      linarith [h1]
  · -- the value identity
    intro x hx
    rw [hkey, map_mul]



/-! ## The Burgess method: splitting and the maximal principle -/

/-- Left endpoint of the interval of `m` such that `ap + lm ∈ (N, N+H]`. -/
noncomputable def oLo (N : ℤ) (p : ℕ) (l a : ℕ) : ℤ :=
  (N - (a:ℤ) * (p:ℤ)) / (l:ℤ)

/-- Right endpoint of the interval of `m` such that `ap + lm ∈ (N, N+H]`. -/
noncomputable def oHi (N : ℤ) (p : ℕ) (H l a : ℕ) : ℤ :=
  ((N + (H:ℤ)) - (a:ℤ) * (p:ℤ)) / (l:ℤ)

lemma oLo_le_oHi (N : ℤ) (p H l a : ℕ) (hl : 0 < l) : oLo N p l a ≤ oHi N p H l a := by
  unfold oLo oHi
  refine Int.ediv_le_ediv (by exact_mod_cast hl) ?_
  have : (0:ℤ) ≤ (H:ℤ) := by exact_mod_cast Nat.zero_le H
  linarith

lemma cSum_le_two_supShift' (χ : DirichletCharacter ℂ q) {n lo hi : ℤ} (hlo : lo ≤ hi)
    (hn : n ≤ lo) {h : ℕ} (hlen : hi - lo ≤ (h:ℤ)) (hnh : lo - h < n) :
    ‖cSum χ lo hi‖ ≤ 2 * supShift χ n (2*h) := by
  have hsplit := cSum_split χ hn hlo
  have hdiff : cSum χ lo hi = cSum χ n hi - cSum χ n lo := by rw [hsplit]; ring
  have h1 : (lo - n).toNat ≤ 2*h := by
    have h0 : (0:ℤ) ≤ lo - n := by omega
    have : lo - n < (h:ℤ) := by omega
    omega
  have h2 : (hi - n).toNat ≤ 2*h := by
    have h0 : (0:ℤ) ≤ hi - n := by omega
    have : hi - n ≤ 2 * (h:ℤ) := by linarith
    omega
  have hb1 : ‖cSum χ n hi‖ = ‖cSum χ n (n + ((hi - n).toNat : ℤ))‖ := by
    congr 1
    rw [Int.toNat_of_nonneg (by omega : (0:ℤ) ≤ hi - n)]; ring
  have hb2 : ‖cSum χ n lo‖ = ‖cSum χ n (n + ((lo - n).toNat : ℤ))‖ := by
    congr 1
    rw [Int.toNat_of_nonneg (by omega : (0:ℤ) ≤ lo - n)]; ring
  rw [hdiff]
  refine (norm_sub_le _ _).trans ?_
  rw [hb1, hb2, two_mul]
  exact add_le_add (le_supShift χ n (2*h) h2) (le_supShift χ n (2*h) h1)

/-- Splitting the character sum along the residue classes modulo `l`. -/
lemma burgess_split {p : ℕ} [Fact p.Prime] (χ : DirichletCharacter ℂ p) (N : ℤ) (H P : ℕ)
    (hP1 : 1 ≤ P) (h2P : 2*P < p) :
    (P:ℝ) * ‖cSum χ N (N + (H:ℤ))‖ ≤
      ∑ l ∈ Finset.Icc (P+1) (2*P), ∑ a ∈ Finset.range l,
        ‖cSum χ (oLo N p l a) (oHi N p H l a)‖ := by
  have hsingle : ∀ l ∈ Finset.Icc (P+1) (2*P),
      ‖cSum χ N (N + (H:ℤ))‖ ≤ ∑ a ∈ Finset.range l, ‖cSum χ (oLo N p l a) (oHi N p H l a)‖ := by
    intro l hl
    rw [Finset.mem_Icc] at hl
    have h1 := cSum_ap_split χ (ℓ := l) (by omega) (by omega) N H
    have hnorm : ‖χ (l : ZMod p)‖ ≤ 1 := DirichletCharacter.norm_le_one χ _
    rw [h1]
    calc ‖χ (l : ZMod p) * ∑ a ∈ Finset.range l, cSum χ (oLo N p l a) (oHi N p H l a)‖
        ≤ ‖χ (l : ZMod p)‖ * ‖∑ a ∈ Finset.range l, cSum χ (oLo N p l a) (oHi N p H l a)‖ :=
          norm_mul_le _ _
      _ ≤ 1 * ‖∑ a ∈ Finset.range l, cSum χ (oLo N p l a) (oHi N p H l a)‖ :=
          mul_le_mul_of_nonneg_right hnorm (norm_nonneg _)
      _ = ‖∑ a ∈ Finset.range l, cSum χ (oLo N p l a) (oHi N p H l a)‖ := one_mul _
      _ ≤ ∑ a ∈ Finset.range l, ‖cSum χ (oLo N p l a) (oHi N p H l a)‖ := norm_sum_le _ _
  have hcard : (Finset.Icc (P+1) (2*P)).card = P := by
    rw [Nat.card_Icc]
    omega
  calc (P:ℝ) * ‖cSum χ N (N + (H:ℤ))‖
      = ∑ _l ∈ Finset.Icc (P+1) (2*P), ‖cSum χ N (N + (H:ℤ))‖ := by
        rw [Finset.sum_const, hcard, nsmul_eq_mul]
    _ ≤ ∑ l ∈ Finset.Icc (P+1) (2*P), ∑ a ∈ Finset.range l,
          ‖cSum χ (oLo N p l a) (oHi N p H l a)‖ :=
        Finset.sum_le_sum hsingle


/-! ## The object set and the weighted collision sum -/

/-- The set of pairs `(l,a)` with `l ∈ [P+1,2P]` and `a < l`. -/
def objFinset (P : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Icc (P+1) (2*P)) ×ˢ (Finset.range (2*P+1))).filter (fun x => x.2 < x.1)

lemma mem_objFinset {P : ℕ} {x : ℕ × ℕ} :
    x ∈ objFinset P ↔ P + 1 ≤ x.1 ∧ x.1 ≤ 2*P ∧ x.2 < x.1 := by
  constructor
  · intro h
    rw [objFinset, Finset.mem_filter] at h
    obtain ⟨h1, h2⟩ := h
    rw [Finset.mem_product, Finset.mem_Icc, Finset.mem_range] at h1
    exact ⟨h1.1.1, h1.1.2, h2⟩
  · intro h
    obtain ⟨h1, h2, h3⟩ := h
    rw [objFinset, Finset.mem_filter]
    exact ⟨by
      rw [Finset.mem_product, Finset.mem_Icc, Finset.mem_range]
      exact ⟨⟨h1, h2⟩, by omega⟩, h3⟩

lemma sum_obj {M : Type*} [AddCommMonoid M] (P : ℕ) (f : ℕ → ℕ → M) :
    ∑ x ∈ objFinset P, f x.1 x.2 = ∑ l ∈ Finset.Icc (P+1) (2*P), ∑ a ∈ Finset.range l, f l a := by
  rw [objFinset, Finset.sum_filter, Finset.sum_product]
  refine Finset.sum_congr rfl (fun l hl => ?_)
  rw [Finset.mem_Icc] at hl
  rw [← Finset.sum_filter]
  refine Finset.sum_congr ?_ (fun a ha => rfl)
  ext a
  rw [Finset.mem_filter, Finset.mem_range, Finset.mem_range]
  constructor
  · rintro ⟨h1, h2⟩; omega
  · intro h; exact ⟨by omega, h⟩

/-- The "A-weight": number of objects whose window contains `n`. -/
noncomputable def weightA (N : ℤ) (p h P : ℕ) (n : ℤ) : ℝ :=
  ∑ x ∈ objFinset P,
    (if oLo N p x.1 x.2 - (h:ℤ) < n ∧ n ≤ oLo N p x.1 x.2 then (1:ℝ) else 0)

lemma weightA_nonneg (N : ℤ) (p h P : ℕ) (n : ℤ) : 0 ≤ weightA N p h P n := by
  unfold weightA
  exact Finset.sum_nonneg (fun x _ => by split <;> norm_num)

/-- `weightA` in nested-sum form. -/
lemma weightA_eq_nested (N : ℤ) (p h P : ℕ) (n : ℤ) :
    weightA N p h P n = ∑ l ∈ Finset.Icc (P+1) (2*P), ∑ a ∈ Finset.range l,
      (if oLo N p l a - (h:ℤ) < n ∧ n ≤ oLo N p l a then (1:ℝ) else 0) := by
  unfold weightA
  exact sum_obj P (fun l a => (if oLo N p l a - (h:ℤ) < n ∧ n ≤ oLo N p l a then (1:ℝ) else 0))

/-- The "collision count". -/
noncomputable def collCount (N : ℤ) (p h P : ℕ) : ℝ :=
  ∑ x ∈ objFinset P, ∑ y ∈ objFinset P,
    (if |oLo N p x.1 x.2 - oLo N p y.1 y.2| ≤ (h:ℤ) then (1:ℝ) else 0)

lemma collCount_eq_nested (N : ℤ) (p h P : ℕ) :
    collCount N p h P =
      ∑ l ∈ Finset.Icc (P+1) (2*P), ∑ a ∈ Finset.range l,
        ∑ l' ∈ Finset.Icc (P+1) (2*P), ∑ a' ∈ Finset.range l',
          (if |(N - (a:ℤ)*(p:ℤ))/(l:ℤ) - (N - (a':ℤ)*(p:ℤ))/(l':ℤ)| ≤ (h:ℤ) then (1:ℝ) else 0) := by
  unfold collCount
  rw [sum_obj P (fun l a => ∑ y ∈ objFinset P,
    (if |oLo N p l a - oLo N p y.1 y.2| ≤ (h:ℤ) then (1:ℝ) else 0))]
  refine Finset.sum_congr rfl (fun l hl => Finset.sum_congr rfl (fun a ha => ?_))
  rw [sum_obj P (fun l' a' => (if |oLo N p l a - oLo N p l' a'| ≤ (h:ℤ) then (1:ℝ) else 0))]
  rfl


/-- The maximal principle applied to every object, summed. -/
lemma burgess_principle {p : ℕ} [Fact p.Prime] (χ : DirichletCharacter ℂ p) (N : ℤ) (H P h : ℕ)
    (hP1 : 1 ≤ P) (h2P : 2*P < p)
    (hlo : ∀ x ∈ objFinset P, -(2*(p:ℤ)) ≤ oLo N p x.1 x.2 - (h:ℤ) ∧ oLo N p x.1 x.2 ≤ (p:ℤ))
    (hlen : ∀ x ∈ objFinset P, oHi N p H x.1 x.2 - oLo N p x.1 x.2 ≤ (h:ℤ)) :
    (h:ℝ) * (∑ x ∈ objFinset P, ‖cSum χ (oLo N p x.1 x.2) (oHi N p H x.1 x.2)‖)
      ≤ 2 * ∑ n ∈ Finset.Icc (-(2*(p:ℤ))) (p:ℤ), weightA N p h P n * supShift χ n (2*h) := by
  have hsub : ∀ x ∈ objFinset P,
      Finset.Ioc (oLo N p x.1 x.2 - (h:ℤ)) (oLo N p x.1 x.2) ⊆ Finset.Icc (-(2*(p:ℤ))) (p:ℤ) := by
    intro x hx n hn
    rw [Finset.mem_Ioc] at hn
    rw [Finset.mem_Icc]
    exact ⟨by linarith [(hlo x hx).1], by linarith [hn.2, (hlo x hx).2]⟩
  have hpt : ∀ x ∈ objFinset P, (h:ℝ) * ‖cSum χ (oLo N p x.1 x.2) (oHi N p H x.1 x.2)‖
      ≤ 2 * ∑ n ∈ Finset.Icc (-(2*(p:ℤ))) (p:ℤ),
          (if oLo N p x.1 x.2 - (h:ℤ) < n ∧ n ≤ oLo N p x.1 x.2 then (1:ℝ) else 0)
            * supShift χ n (2*h) := by
    intro x hx
    have hpx : 0 < x.1 := by
      have := (mem_objFinset.mp hx).1
      omega
    have hcard : ((Finset.Ioc (oLo N p x.1 x.2 - (h:ℤ)) (oLo N p x.1 x.2)).card : ℝ) = (h:ℝ) := by
      rw [Int.card_Ioc]
      have heq : oLo N p x.1 x.2 - (oLo N p x.1 x.2 - (h:ℤ)) = (h:ℤ) := by ring
      rw [heq]
      rw [show ((h:ℤ).toNat : ℝ) = (h:ℝ) by
        exact_mod_cast (Int.toNat_of_nonneg (by exact_mod_cast Nat.zero_le h : (0:ℤ) ≤ (h:ℤ)))]
    have hsum1 : (∑ _n ∈ Finset.Ioc (oLo N p x.1 x.2 - (h:ℤ)) (oLo N p x.1 x.2),
          ‖cSum χ (oLo N p x.1 x.2) (oHi N p H x.1 x.2)‖)
        = (h:ℝ) * ‖cSum χ (oLo N p x.1 x.2) (oHi N p H x.1 x.2)‖ := by
      rw [Finset.sum_const, nsmul_eq_mul, hcard]
    have h1 : ∑ n ∈ Finset.Ioc (oLo N p x.1 x.2 - (h:ℤ)) (oLo N p x.1 x.2),
        ‖cSum χ (oLo N p x.1 x.2) (oHi N p H x.1 x.2)‖
        ≤ ∑ n ∈ Finset.Ioc (oLo N p x.1 x.2 - (h:ℤ)) (oLo N p x.1 x.2),
          2 * supShift χ n (2*h) := by
      refine Finset.sum_le_sum (fun n hn => ?_)
      rw [Finset.mem_Ioc] at hn
      exact cSum_le_two_supShift' χ (oLo_le_oHi N p H x.1 x.2 hpx) hn.2 (hlen x hx) hn.1
    have h2 : ∑ n ∈ Finset.Ioc (oLo N p x.1 x.2 - (h:ℤ)) (oLo N p x.1 x.2),
        2 * supShift χ n (2*h)
        = 2 * ∑ n ∈ Finset.Ioc (oLo N p x.1 x.2 - (h:ℤ)) (oLo N p x.1 x.2), supShift χ n (2*h) :=
      (Finset.mul_sum ..).symm
    have hfilter : (Finset.Icc (-(2*(p:ℤ))) (p:ℤ)).filter
          (fun n => oLo N p x.1 x.2 - (h:ℤ) < n ∧ n ≤ oLo N p x.1 x.2)
        = Finset.Ioc (oLo N p x.1 x.2 - (h:ℤ)) (oLo N p x.1 x.2) := by
      ext n
      rw [Finset.mem_filter]
      constructor
      · rintro ⟨_, h1, h2⟩
        exact Finset.mem_Ioc.mpr ⟨h1, h2⟩
      · intro h
        obtain ⟨h1, h2⟩ := Finset.mem_Ioc.mp h
        exact ⟨hsub x hx (Finset.mem_Ioc.mpr ⟨h1, h2⟩), h1, h2⟩
    have h3 : (2 * ∑ n ∈ Finset.Ioc (oLo N p x.1 x.2 - (h:ℤ)) (oLo N p x.1 x.2), supShift χ n (2*h))
        = 2 * ∑ n ∈ Finset.Icc (-(2*(p:ℤ))) (p:ℤ),
            (if oLo N p x.1 x.2 - (h:ℤ) < n ∧ n ≤ oLo N p x.1 x.2 then (1:ℝ) else 0)
              * supShift χ n (2*h) := by
      congr 1
      have key1 : ∑ n ∈ Finset.Icc (-(2*(p:ℤ))) (p:ℤ),
          (if oLo N p x.1 x.2 - (h:ℤ) < n ∧ n ≤ oLo N p x.1 x.2 then (1:ℝ) else 0)
            * supShift χ n (2*h)
          = ∑ n ∈ Finset.Icc (-(2*(p:ℤ))) (p:ℤ),
              (if oLo N p x.1 x.2 - (h:ℤ) < n ∧ n ≤ oLo N p x.1 x.2
                then supShift χ n (2*h) else 0) := by
        refine Finset.sum_congr rfl (fun n hn => ?_)
        split <;> ring
      rw [key1, ← Finset.sum_filter, hfilter]
    calc (h:ℝ) * ‖cSum χ (oLo N p x.1 x.2) (oHi N p H x.1 x.2)‖
        = ∑ _n ∈ Finset.Ioc (oLo N p x.1 x.2 - (h:ℤ)) (oLo N p x.1 x.2),
            ‖cSum χ (oLo N p x.1 x.2) (oHi N p H x.1 x.2)‖ := hsum1.symm
      _ ≤ ∑ n ∈ Finset.Ioc (oLo N p x.1 x.2 - (h:ℤ)) (oLo N p x.1 x.2),
            2 * supShift χ n (2*h) := h1
      _ = 2 * ∑ n ∈ Finset.Ioc (oLo N p x.1 x.2 - (h:ℤ)) (oLo N p x.1 x.2), supShift χ n (2*h) := h2
      _ = 2 * ∑ n ∈ Finset.Icc (-(2*(p:ℤ))) (p:ℤ),
            (if oLo N p x.1 x.2 - (h:ℤ) < n ∧ n ≤ oLo N p x.1 x.2 then (1:ℝ) else 0)
              * supShift χ n (2*h) := h3

  calc (h:ℝ) * (∑ x ∈ objFinset P, ‖cSum χ (oLo N p x.1 x.2) (oHi N p H x.1 x.2)‖)
      = ∑ x ∈ objFinset P, (h:ℝ) * ‖cSum χ (oLo N p x.1 x.2) (oHi N p H x.1 x.2)‖ :=
        Finset.mul_sum ..
    _ ≤ ∑ x ∈ objFinset P, 2 * ∑ n ∈ Finset.Icc (-(2*(p:ℤ))) (p:ℤ),
          (if oLo N p x.1 x.2 - (h:ℤ) < n ∧ n ≤ oLo N p x.1 x.2 then (1:ℝ) else 0)
            * supShift χ n (2*h) := Finset.sum_le_sum hpt
    _ = 2 * ∑ x ∈ objFinset P, ∑ n ∈ Finset.Icc (-(2*(p:ℤ))) (p:ℤ),
          (if oLo N p x.1 x.2 - (h:ℤ) < n ∧ n ≤ oLo N p x.1 x.2 then (1:ℝ) else 0)
            * supShift χ n (2*h) := by rw [Finset.mul_sum]
    _ = 2 * ∑ n ∈ Finset.Icc (-(2*(p:ℤ))) (p:ℤ), ∑ x ∈ objFinset P,
          (if oLo N p x.1 x.2 - (h:ℤ) < n ∧ n ≤ oLo N p x.1 x.2 then (1:ℝ) else 0)
            * supShift χ n (2*h) := by
        rw [Finset.sum_comm]
    _ = 2 * ∑ n ∈ Finset.Icc (-(2*(p:ℤ))) (p:ℤ), weightA N p h P n * supShift χ n (2*h) := by
        congr 1
        refine Finset.sum_congr rfl (fun n hn => ?_)
        unfold weightA
        rw [← Finset.sum_mul]




/-- Converting an integer interval sum to a `range` sum. -/
lemma sum_Icc_eq_sum_range (G : ℤ → ℝ) (a : ℤ) (n : ℕ) :
    ∑ x ∈ Finset.Icc a (a + n - 1), G x = ∑ m ∈ Finset.range n, G (a + m) := by
  refine Finset.sum_bij (fun x _ => (x - a).toNat) ?_ ?_ ?_ ?_
  · intro x hx
    rw [Finset.mem_Icc] at hx
    rw [Finset.mem_range]
    have h0 : 0 ≤ x - a := by omega
    have h1 : x - a < ((n:ℕ):ℤ) := by
      have : x ≤ a + (n:ℤ) - 1 := hx.2
      omega
    omega
  · intro x hx y hy hxy
    rw [Finset.mem_Icc] at hx hy
    have h1 : 0 ≤ x - a := by omega
    have h2 : 0 ≤ y - a := by omega
    have h3 := congrArg (fun t : ℕ => (t:ℤ)) hxy
    simp only [Int.toNat_of_nonneg h1, Int.toNat_of_nonneg h2] at h3
    omega
  · intro m hm
    rw [Finset.mem_range] at hm
    refine ⟨a + (m:ℤ), ?_, ?_⟩
    · rw [Finset.mem_Icc]
      constructor <;> push_cast <;> omega
    · have h1 : a + (m:ℤ) - a = (m:ℤ) := by ring
      rw [h1, Int.toNat_natCast]
  · intro x hx
    rw [Finset.mem_Icc] at hx
    have h1 : 0 ≤ x - a := by omega
    rw [Int.toNat_of_nonneg h1]
    ring

/-- Sum over `j` full periods. -/
lemma sum_range_periodic_mul {p : ℕ} (hp : 0 < p) (G : ℕ → ℝ) (hper : ∀ m, G (p + m) = G m)
    (j : ℕ) :
    ∑ m ∈ Finset.range (j*p), G m = j * ∑ m ∈ Finset.range p, G m := by
  induction j with
  | zero => simp
  | succ j ih =>
    have h1 : (j+1)*p = j*p + p := by ring
    have hshift : ∀ k m : ℕ, G (k*p + m) = G m := by
      intro k
      induction k with
      | zero => intro m; simp
      | succ k ih =>
        intro m
        have h1 : (k+1)*p + m = p + (k*p + m) := by ring
        rw [h1, hper, ih]
    rw [h1, Finset.sum_range_add, ih,
      show ∑ x ∈ Finset.range p, G (j*p + x) = ∑ x ∈ Finset.range p, G x from
        Finset.sum_congr rfl (fun m hm => hshift j m)]
    push_cast
    ring

/-- The number of window points inside `W`. -/
lemma weight_pointwise_count {N : ℤ} {p h P : ℕ} {x : ℕ × ℕ} (hx : x ∈ objFinset P)
    (hlo : -(2*(p:ℤ)) ≤ oLo N p x.1 x.2 - (h:ℤ) ∧ oLo N p x.1 x.2 ≤ (p:ℤ)) :
    ∑ n ∈ Finset.Icc (-(2*(p:ℤ))) (p:ℤ),
        (if oLo N p x.1 x.2 - (h:ℤ) < n ∧ n ≤ oLo N p x.1 x.2 then (1:ℝ) else 0)
      = (h:ℝ) := by
  have hfilter : (Finset.Icc (-(2*(p:ℤ))) (p:ℤ)).filter
        (fun n => oLo N p x.1 x.2 - (h:ℤ) < n ∧ n ≤ oLo N p x.1 x.2)
      = Finset.Ioc (oLo N p x.1 x.2 - (h:ℤ)) (oLo N p x.1 x.2) := by
    ext n
    rw [Finset.mem_filter]
    constructor
    · rintro ⟨_, h1, h2⟩
      exact Finset.mem_Ioc.mpr ⟨h1, h2⟩
    · intro hn
      obtain ⟨h1, h2⟩ := Finset.mem_Ioc.mp hn
      exact ⟨Finset.mem_Icc.mpr ⟨by linarith [hlo.1], by linarith [hlo.2]⟩, h1, h2⟩
  rw [← Finset.sum_filter, hfilter]
  rw [Finset.sum_const, Int.card_Ioc]
  have heq : oLo N p x.1 x.2 - (oLo N p x.1 x.2 - (h:ℤ)) = (h:ℤ) := by ring
  rw [heq]
  rw [nsmul_eq_mul]
  rw [show ((h:ℤ).toNat : ℝ) = (h:ℝ) by
    exact_mod_cast (Int.toNat_of_nonneg (by exact_mod_cast Nat.zero_le h : (0:ℤ) ≤ (h:ℤ)))]
  ring

/-- The total weight. -/
lemma weight_sum_le (N : ℤ) (p h P : ℕ) (hP : 1 ≤ P)
    (hlo : ∀ x ∈ objFinset P, -(2*(p:ℤ)) ≤ oLo N p x.1 x.2 - (h:ℤ) ∧ oLo N p x.1 x.2 ≤ (p:ℤ)) :
    ∑ n ∈ Finset.Icc (-(2*(p:ℤ))) (p:ℤ), weightA N p h P n ≤ 2 * (P:ℝ)^2 * (h:ℝ) := by
  have hswap : ∑ n ∈ Finset.Icc (-(2*(p:ℤ))) (p:ℤ), weightA N p h P n
      = ∑ x ∈ objFinset P, ∑ n ∈ Finset.Icc (-(2*(p:ℤ))) (p:ℤ),
          (if oLo N p x.1 x.2 - (h:ℤ) < n ∧ n ≤ oLo N p x.1 x.2 then (1:ℝ) else 0) := by
    unfold weightA
    rw [Finset.sum_comm]
  rw [hswap]
  have h1 : ∑ x ∈ objFinset P, ∑ n ∈ Finset.Icc (-(2*(p:ℤ))) (p:ℤ),
        (if oLo N p x.1 x.2 - (h:ℤ) < n ∧ n ≤ oLo N p x.1 x.2 then (1:ℝ) else 0)
      = ∑ x ∈ objFinset P, (h:ℝ) :=
    Finset.sum_congr rfl (fun x hx => weight_pointwise_count hx (hlo x hx))
  rw [h1, Finset.sum_const, nsmul_eq_mul]
  have hcard : ((objFinset P).card : ℝ) ≤ 2*(P:ℝ)^2 := by
    have hcard' : (objFinset P).card = ∑ l ∈ Finset.Icc (P+1) (2*P), l := by
      rw [show (objFinset P).card = ∑ x ∈ objFinset P, (1:ℕ) by simp]
      rw [sum_obj P (fun _ _ => (1:ℕ))]
      refine Finset.sum_congr rfl (fun l hl => ?_)
      simp
    rw [hcard']
    have h2 : ∑ l ∈ Finset.Icc (P+1) (2*P), l ≤ P * (2*P) := by
      calc ∑ l ∈ Finset.Icc (P+1) (2*P), l
          ≤ ∑ _l ∈ Finset.Icc (P+1) (2*P), (2*P) :=
            Finset.sum_le_sum (fun l hl => by rw [Finset.mem_Icc] at hl; omega)
        _ = P * (2*P) := by
            rw [Finset.sum_const, Nat.card_Icc, smul_eq_mul]
            congr 1
            omega
    calc ((∑ l ∈ Finset.Icc (P+1) (2*P), l : ℕ) : ℝ) ≤ ((P * (2*P) : ℕ) : ℝ) := by
          exact_mod_cast h2
      _ = 2*(P:ℝ)^2 := by push_cast; ring
  calc ((objFinset P).card : ℝ) * (h:ℝ) ≤ (2*(P:ℝ)^2) * (h:ℝ) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = 2 * (P:ℝ)^2 * (h:ℝ) := by ring


lemma supShift_add_q (χ : DirichletCharacter ℂ q) (n : ℤ) (K : ℕ) :
    supShift χ (n + q) K = supShift χ n K := by
  have hfun : (fun j : ℕ => ‖cSum χ (n + q) ((n + q) + j)‖)
      = (fun j : ℕ => ‖cSum χ n (n + j)‖) := by
    funext j
    have h1 : n + (q:ℤ) + (j:ℤ) = (n + (j:ℤ)) + (q:ℤ) := by ring
    rw [h1, cSum_add_q]
  unfold supShift
  rw [hfun]


/-- Moment bound for the maximal sums over the window `Icc (-2p) p`. -/
lemma moment_W_le {p : ℕ} [Fact p.Prime] (χ : DirichletCharacter ℂ p) (Cm : ℝ) (k : ℕ) (hk2 : 2 ≤ k)
    (hmom : ∀ L : ℕ, L ≤ p → ∑ m ∈ Finset.range p, ‖cSum χ (m:ℤ) ((m:ℤ) + L)‖^(2*k)
        ≤ Cm * ((p:ℝ) * (L:ℝ)^k + (L:ℝ)^(2*k) * Real.sqrt p))
    (h t K : ℕ) (ht : K = 2^t) (hK1 : 2*h ≤ K) (hKp : K ≤ p) :
    ∑ n ∈ Finset.Icc (-(2*(p:ℤ))) (p:ℤ), (supShift χ n (2*h))^(2*k)
      ≤ 4 * ((t+1:ℝ))^(2*k) *
          (4*Cm*((p:ℝ)*((2:ℝ)^t)^k + ((2:ℝ)^t)^(2*k)*Real.sqrt p)) := by
  have hB := supShift_window_le χ Cm k (by omega) hk2 hmom t (-(2*(p:ℤ))) (2*h)
    (by have h := hK1; rw [ht] at h; exact h) (by have h := hKp; rw [ht] at h; exact h)
  have hstep1 : ∑ n ∈ Finset.Icc (-(2*(p:ℤ))) (p:ℤ), (supShift χ n (2*h))^(2*k)
      ≤ ∑ n ∈ Finset.Icc (-(2*(p:ℤ))) (2*(p:ℤ)-1), (supShift χ n (2*h))^(2*k) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_
      (fun x hx hx' => pow_nonneg (supShift_nonneg χ x (2*h)) _)
    intro x hx
    rw [Finset.mem_Icc] at hx ⊢
    have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
    constructor <;> omega
  have hstep2 : ∑ n ∈ Finset.Icc (-(2*(p:ℤ))) (2*(p:ℤ)-1), (supShift χ n (2*h))^(2*k)
      = 4 * ∑ m ∈ Finset.range p, (supShift χ (-(2*(p:ℤ)) + (m:ℤ)) (2*h))^(2*k) := by
    have h4 : (2*(p:ℤ)-1) = -(2*(p:ℤ)) + ((4*p : ℕ):ℤ) - 1 := by push_cast; ring
    rw [h4, sum_Icc_eq_sum_range (fun x => (supShift χ x (2*h))^(2*k)) (-(2*(p:ℤ))) (4*p)]
    rw [sum_range_periodic_mul (p := p)
      (by have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le; omega)
      (fun m => (supShift χ (-(2*(p:ℤ)) + (m:ℤ)) (2*h))^(2*k)) ?_ 4]
    · ring
    · intro m
      rw [show -(2*(p:ℤ)) + (((p+m:ℕ)):ℤ) = (-(2*(p:ℤ)) + (m:ℤ)) + (p:ℤ) by push_cast; ring]
      rw [supShift_add_q]
  have hstep3 : ∑ m ∈ Finset.range p, (supShift χ (-(2*(p:ℤ)) + (m:ℤ)) (2*h))^(2*k)
      = ∑ x ∈ Finset.Icc (-(2*(p:ℤ))) (-(2*(p:ℤ)) + (p:ℤ) - 1),
          (supShift χ x (2*h))^(2*k) :=
    (sum_Icc_eq_sum_range (fun x => (supShift χ x (2*h))^(2*k)) (-(2*(p:ℤ))) p).symm
  calc ∑ n ∈ Finset.Icc (-(2*(p:ℤ))) (p:ℤ), (supShift χ n (2*h))^(2*k)
      ≤ ∑ n ∈ Finset.Icc (-(2*(p:ℤ))) (2*(p:ℤ)-1), (supShift χ n (2*h))^(2*k) := hstep1
    _ = 4 * ∑ m ∈ Finset.range p, (supShift χ (-(2*(p:ℤ)) + (m:ℤ)) (2*h))^(2*k) := hstep2
    _ = 4 * ∑ x ∈ Finset.Icc (-(2*(p:ℤ))) (-(2*(p:ℤ)) + (p:ℤ) - 1),
          (supShift χ x (2*h))^(2*k) := by rw [hstep3]
    _ ≤ 4 * (((t+1:ℝ))^(2*k) *
          (4*Cm*((p:ℝ)*((2:ℝ)^t)^k + ((2:ℝ)^t)^(2*k)*Real.sqrt p))) :=
        mul_le_mul_of_nonneg_left hB (by norm_num)
    _ = 4 * ((t+1:ℝ))^(2*k) *
          (4*Cm*((p:ℝ)*((2:ℝ)^t)^k + ((2:ℝ)^t)^(2*k)*Real.sqrt p)) := by ring


/-- Indicator of the window of an object. -/
noncomputable def winInd (N : ℤ) (p h : ℕ) (x : ℕ × ℕ) (n : ℤ) : ℝ :=
  if oLo N p x.1 x.2 - (h:ℤ) < n ∧ n ≤ oLo N p x.1 x.2 then 1 else 0

lemma winInd_nonneg (N : ℤ) (p h : ℕ) (x : ℕ × ℕ) (n : ℤ) : 0 ≤ winInd N p h x n := by
  unfold winInd; split <;> norm_num

lemma weightA_eq_sum_winInd (N : ℤ) (p h P : ℕ) (n : ℤ) :
    weightA N p h P n = ∑ x ∈ objFinset P, winInd N p h x n := by
  unfold weightA winInd
  rfl

lemma winInd_le_one (N : ℤ) (p h : ℕ) (x : ℕ × ℕ) (n : ℤ) : winInd N p h x n ≤ 1 := by
  unfold winInd; split <;> norm_num

lemma winInd_ne_zero_iff {N : ℤ} {p h : ℕ} {x : ℕ × ℕ} {n : ℤ} :
    winInd N p h x n ≠ 0 ↔ (oLo N p x.1 x.2 - (h:ℤ) < n ∧ n ≤ oLo N p x.1 x.2) := by
  unfold winInd
  constructor
  · intro hne
    by_contra hc
    exact hne (if_neg hc)
  · intro hc
    rw [if_pos hc]
    norm_num

/-- The sum of squares of the weights is bounded by `h` times the collision count. -/
lemma weight_sq_le (N : ℤ) (p h P : ℕ) (hP : 1 ≤ P)
    (hlo : ∀ x ∈ objFinset P, -(2*(p:ℤ)) ≤ oLo N p x.1 x.2 - (h:ℤ) ∧ oLo N p x.1 x.2 ≤ (p:ℤ)) :
    ∑ n ∈ Finset.Icc (-(2*(p:ℤ))) (p:ℤ), (weightA N p h P n)^2
      ≤ (h:ℝ) * collCount N p h P := by
  have hpoint : ∀ x ∈ objFinset P, ∀ y ∈ objFinset P,
      ∑ n ∈ Finset.Icc (-(2*(p:ℤ))) (p:ℤ), winInd N p h x n * winInd N p h y n
        ≤ (h:ℝ) * (if |oLo N p x.1 x.2 - oLo N p y.1 y.2| ≤ (h:ℤ) then (1:ℝ) else 0) := by
    intro x hx y hy
    by_cases hc : |oLo N p x.1 x.2 - oLo N p y.1 y.2| ≤ (h:ℤ)
    · rw [if_pos hc, mul_one]
      calc ∑ n ∈ Finset.Icc (-(2*(p:ℤ))) (p:ℤ), winInd N p h x n * winInd N p h y n
          ≤ ∑ n ∈ Finset.Icc (-(2*(p:ℤ))) (p:ℤ), winInd N p h x n := by
            refine Finset.sum_le_sum (fun n hn => ?_)
            calc winInd N p h x n * winInd N p h y n ≤ winInd N p h x n * 1 :=
                  mul_le_mul_of_nonneg_left (winInd_le_one N p h y n) (winInd_nonneg N p h x n)
              _ = winInd N p h x n := mul_one _
        _ = (h:ℝ) := weight_pointwise_count hx (hlo x hx)
    · rw [if_neg hc, mul_zero]
      refine le_of_eq (Finset.sum_eq_zero (fun n hn => ?_))
      by_contra hne
      rw [mul_eq_zero] at hne
      push_neg at hne
      obtain ⟨hxe, hye⟩ := hne
      obtain ⟨hxc1, hxc2⟩ := winInd_ne_zero_iff.mp hxe
      obtain ⟨hyc1, hyc2⟩ := winInd_ne_zero_iff.mp hye
      exact hc (by rw [abs_le]; constructor <;> linarith)
  have hexp : ∀ n, (weightA N p h P n)^2
      = ∑ x ∈ objFinset P, ∑ y ∈ objFinset P, winInd N p h x n * winInd N p h y n := by
    intro n
    rw [weightA_eq_sum_winInd, sq, Finset.sum_mul_sum]
  calc ∑ n ∈ Finset.Icc (-(2*(p:ℤ))) (p:ℤ), (weightA N p h P n)^2
      = ∑ n ∈ Finset.Icc (-(2*(p:ℤ))) (p:ℤ), ∑ x ∈ objFinset P, ∑ y ∈ objFinset P,
          winInd N p h x n * winInd N p h y n := Finset.sum_congr rfl (fun n _ => hexp n)
    _ = ∑ x ∈ objFinset P, ∑ n ∈ Finset.Icc (-(2*(p:ℤ))) (p:ℤ), ∑ y ∈ objFinset P,
          winInd N p h x n * winInd N p h y n := Finset.sum_comm
    _ = ∑ x ∈ objFinset P, ∑ y ∈ objFinset P, ∑ n ∈ Finset.Icc (-(2*(p:ℤ))) (p:ℤ),
          winInd N p h x n * winInd N p h y n := by
        refine Finset.sum_congr rfl (fun x hx => ?_)
        exact Finset.sum_comm
    _ ≤ ∑ x ∈ objFinset P, ∑ y ∈ objFinset P,
          (h:ℝ) * (if |oLo N p x.1 x.2 - oLo N p y.1 y.2| ≤ (h:ℤ) then (1:ℝ) else 0) :=
        Finset.sum_le_sum (fun x hx => Finset.sum_le_sum (fun y hy => hpoint x hx y hy))
    _ = (h:ℝ) * collCount N p h P := by
        unfold collCount
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun x hx => ?_)
        rw [Finset.mul_sum]



/-- The collision count is bounded by the diagonal plus the off-diagonal count. -/
lemma collCount_le (N : ℤ) (p h P : ℕ) (hp : 0 < p) (hP : 1 ≤ P) :
    collCount N p h P
      ≤ ((2*((h:ℝ)+2)/(p:ℝ)) * (2*(P:ℝ))^3 + (2*(P:ℝ))^2)
        + ((8*(P:ℝ)^2*((h:ℝ)+2)/(p:ℝ) + 4) * (4*(2*(P:ℝ))^2*(Real.log (2*(P:ℝ))+1))) := by
  rw [collCount_eq_nested]
  have hsplit : ∀ l a l' a' : ℕ,
      (if |(N - (a:ℤ)*(p:ℤ))/(l:ℤ) - (N - (a':ℤ)*(p:ℤ))/(l':ℤ)| ≤ (h:ℤ) then (1:ℝ) else 0)
      = (if l = l' ∧ |(N - (a:ℤ)*(p:ℤ))/(l:ℤ) - (N - (a':ℤ)*(p:ℤ))/(l':ℤ)| ≤ (h:ℤ)
          then (1:ℝ) else 0)
        + (if l ≠ l' ∧ |(N - (a:ℤ)*(p:ℤ))/(l:ℤ) - (N - (a':ℤ)*(p:ℤ))/(l':ℤ)| ≤ (h:ℤ)
          then (1:ℝ) else 0) := by
    intro l a l' a'
    by_cases hl : l = l' <;> by_cases hc : |(N - (a:ℤ)*(p:ℤ))/(l:ℤ) - (N - (a':ℤ)*(p:ℤ))/(l':ℤ)| ≤ (h:ℤ) <;>
      simp [hl, hc]
  have hdiag : (∑ l ∈ Finset.Icc (P+1) (2*P), ∑ a ∈ Finset.range l,
        ∑ l' ∈ Finset.Icc (P+1) (2*P), ∑ a' ∈ Finset.range l',
          (if l = l' ∧ |(N - (a:ℤ)*(p:ℤ))/(l:ℤ) - (N - (a':ℤ)*(p:ℤ))/(l':ℤ)| ≤ (h:ℤ)
            then (1:ℝ) else 0))
      ≤ (2*((h:ℝ)+2)/(p:ℝ)) * (2*(P:ℝ))^3 + (2*(P:ℝ))^2 := by
    have h1 : (∑ l ∈ Finset.Icc (P+1) (2*P), ∑ a ∈ Finset.range l,
        ∑ l' ∈ Finset.Icc (P+1) (2*P), ∑ a' ∈ Finset.range l',
          (if l = l' ∧ |(N - (a:ℤ)*(p:ℤ))/(l:ℤ) - (N - (a':ℤ)*(p:ℤ))/(l':ℤ)| ≤ (h:ℤ)
            then (1:ℝ) else 0))
        = (∑ l ∈ Finset.Icc (P+1) (2*P), ∑ a ∈ Finset.range l, ∑ a' ∈ Finset.range l,
          (if |(N - (a:ℤ)*(p:ℤ))/(l:ℤ) - (N - (a':ℤ)*(p:ℤ))/(l:ℤ)| ≤ (h:ℤ) then (1:ℝ) else 0)) := by
      refine Finset.sum_congr rfl (fun l hl => Finset.sum_congr rfl (fun a ha => ?_))
      rw [Finset.sum_eq_single l]
      · refine Finset.sum_congr rfl (fun a' ha' => ?_)
        simp only [true_and]
      · intro l' hl' hne
        refine Finset.sum_eq_zero (fun a' ha' => ?_)
        rw [if_neg]
        intro hcon
        exact hne hcon.1.symm
      · intro hnot
        exact absurd hl hnot
    rw [h1]
    exact Commons.NumberTheory.CharacterSum.card_floor_close_diag P p N h hp
  have hoff : (∑ l ∈ Finset.Icc (P+1) (2*P), ∑ a ∈ Finset.range l,
        ∑ l' ∈ Finset.Icc (P+1) (2*P), ∑ a' ∈ Finset.range l',
          (if l ≠ l' ∧ |(N - (a:ℤ)*(p:ℤ))/(l:ℤ) - (N - (a':ℤ)*(p:ℤ))/(l':ℤ)| ≤ (h:ℤ)
            then (1:ℝ) else 0))
      ≤ (8*(P:ℝ)^2*((h:ℝ)+2)/(p:ℝ) + 4) * (4*(2*(P:ℝ))^2*(Real.log (2*(P:ℝ))+1)) :=
    Commons.NumberTheory.CharacterSum.card_floor_close_offdiag P p N h hp hP
  have hsplitSum : (∑ l ∈ Finset.Icc (P+1) (2*P), ∑ a ∈ Finset.range l,
        ∑ l' ∈ Finset.Icc (P+1) (2*P), ∑ a' ∈ Finset.range l',
          (if |(N - (a:ℤ)*(p:ℤ))/(l:ℤ) - (N - (a':ℤ)*(p:ℤ))/(l':ℤ)| ≤ (h:ℤ)
            then (1:ℝ) else 0))
      = (∑ l ∈ Finset.Icc (P+1) (2*P), ∑ a ∈ Finset.range l,
        ∑ l' ∈ Finset.Icc (P+1) (2*P), ∑ a' ∈ Finset.range l',
          ((if l = l' ∧ |(N - (a:ℤ)*(p:ℤ))/(l:ℤ) - (N - (a':ℤ)*(p:ℤ))/(l':ℤ)| ≤ (h:ℤ)
            then (1:ℝ) else 0)
           + (if l ≠ l' ∧ |(N - (a:ℤ)*(p:ℤ))/(l:ℤ) - (N - (a':ℤ)*(p:ℤ))/(l':ℤ)| ≤ (h:ℤ)
            then (1:ℝ) else 0))) := by
    refine Finset.sum_congr rfl (fun l hl => Finset.sum_congr rfl (fun a ha =>
      Finset.sum_congr rfl (fun l' hl' => ?_)))
    refine (Finset.sum_congr rfl (fun a' ha' => hsplit l a l' a')).trans ?_
    rw [Finset.sum_add_distrib]
  rw [hsplitSum]
  simp only [Finset.sum_add_distrib]
  exact add_le_add hdiag hoff


/-- `p^a * p^(-a) = 1` for `p > 0`. -/
lemma rpow_mul_inv_self {p : ℝ} (hp : 0 < p) (a : ℝ) : p^a * p^(-a) = 1 := by
  rw [← Real.rpow_add hp]; ring_nf; rw [Real.rpow_zero]

/-- Squaring a product of `rpow`s. -/
lemma sq_rpow (p L : ℝ) (hp : 0 ≤ p) (a : ℝ) (m : ℕ) :
    (p^a * L^m)^2 = p^(a*2) * L^(m*2) := by
  rw [mul_pow]
  have h1 : (p^a)^2 = p^(a*2) := by
    rw [← Real.rpow_natCast (x := p^a) (n := 2)]
    exact (Real.rpow_mul hp a 2).symm
  have h2 : (L^m)^2 = L^(m*2) := (pow_mul L m 2).symm
  rw [h1, h2]

/-- `(H * p^(-a)) * p^a = H`. -/
lemma mul_rpow_neg_mul (p H : ℝ) (hp : 0 < p) (a : ℝ) : (H * p^(-a)) * p^a = H := by
  rw [mul_assoc, ← Real.rpow_add hp]; ring_nf; rw [Real.rpow_zero, mul_one]

lemma burgess_core (Cm : ℝ) (hCm1 : 1 ≤ Cm) (k : ℕ) (hk2 : 2 ≤ k) (hk3 : k ≤ 3)
    (hmom : ∀ (p : ℕ) [Fact p.Prime] (χ : DirichletCharacter ℂ p), χ ≠ 1 → ∀ L : ℕ, L ≤ p →
      ∑ m ∈ Finset.range p, ‖cSum χ (m:ℤ) ((m:ℤ) + L)‖^(2*k)
        ≤ Cm * ((p:ℝ) * (L:ℝ)^k + (L:ℝ)^(2*k) * Real.sqrt p))
    {p : ℕ} [Fact p.Prime] (hp : 2^60 ≤ p) (χ : DirichletCharacter ℂ p) (hχ : χ ≠ 1)
    (N : ℤ) (hN0 : 0 ≤ N) (hNp : N < (p:ℤ)) (H : ℕ) (hH1 : 1 ≤ H) (hHp : H ≤ p)
    (hHlo : (p:ℝ)^((k+1)/(4*k:ℝ)) ≤ (H:ℝ))
    (hHhi : (H:ℝ) ≤ (p:ℝ)^((2*k+1)/(4*k:ℝ)) * (Real.log p)^(4*k+8)) :
    ‖cSum χ N (N + (H:ℤ))‖ ≤ 2^70 * Cm * (p:ℝ)^((k+1)/(4*k^2:ℝ)) * (H:ℝ)^(1 - 1/(k:ℝ))
      * (Real.log p)^(10*k+20) := by
  have hk1 : 1 ≤ k := by omega
  have hkpos : (0:ℝ) < (k:ℝ) := by exact_mod_cast (show 0 < k by omega)
  have hk3R : (k:ℝ) ≤ 3 := by exact_mod_cast hk3
  have hkR2 : (2:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk2
  have hp0 : (0:ℝ) < (p:ℝ) := by exact_mod_cast (Fact.out : p.Prime).pos
  have hp1 : (1:ℝ) ≤ (p:ℝ) := by exact_mod_cast (show 1 ≤ p by omega)
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hpz : (0:ℤ) < (p:ℤ) := by exact_mod_cast (Fact.out : p.Prime).pos
  have hHpos : (0:ℝ) < (H:ℝ) := by exact_mod_cast hH1
  have hHnn : (0:ℝ) ≤ (H:ℝ) := le_of_lt hHpos
  have hp60r : ((2:ℝ)^60) ≤ (p:ℝ) := by
    have h : ((2^60 : ℕ) : ℝ) = (2:ℝ)^60 := by push_cast; ring
    rw [← h]; exact_mod_cast hp
  have hL1 : (1:ℝ) ≤ Real.log p := by
    rw [← Real.log_exp 1]
    apply Real.log_le_log (Real.exp_pos 1)
    calc Real.exp 1 ≤ 4 := le_of_lt (lt_trans Real.exp_one_lt_three (by norm_num))
      _ ≤ (2:ℝ)^60 := by norm_num
      _ = ((2^60 : ℕ) : ℝ) := by norm_num
      _ ≤ (p:ℝ) := by exact_mod_cast hp
  have hLpos : (0:ℝ) < Real.log p := lt_of_lt_of_le one_pos hL1
  -- ### rpow facts about p
  have h1024le : (1024:ℝ) ≤ (p:ℝ)^(1/(2*(k:ℝ))) := by
    have hexp_le : (1:ℝ)/6 ≤ 1/(2*(k:ℝ)) := by
      rw [div_le_div_iff₀ (by norm_num) (by positivity)]
      push_cast
      linarith [hk3R]
    have h1 : (1024:ℝ) ≤ ((2:ℝ)^60)^((1:ℝ)/6) := by
      rw [← Real.rpow_natCast_mul (by norm_num : (0:ℝ) ≤ 2) 60 (1/6)]
      have he : (↑(60:ℕ) : ℝ) * ((1:ℝ)/6) = 10 := by norm_num
      rw [he]
      norm_num
    exact le_trans h1 (le_trans
      (Real.rpow_le_rpow (x := (2:ℝ)^60) (y := (p:ℝ)) (z := (1:ℝ)/6) (by positivity) hp60r (by norm_num))
      (Real.rpow_le_rpow_of_exponent_le hp1 hexp_le))
  have h8le : (8:ℝ) ≤ (p:ℝ)^(1/(2*(k:ℝ))) := le_trans (by norm_num) h1024le
  have h64le : (64:ℝ) ≤ (p:ℝ)^(1/(2*(k:ℝ))) := le_trans (by norm_num) h1024le
  have h2le : (2:ℝ) ≤ (p:ℝ)^(1/(2*(k:ℝ))) := le_trans (by norm_num) h1024le
  have hexp_le_half : 1/(2*(k:ℝ)) ≤ (1:ℝ)/2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    push_cast; linarith [hkR2]
  have hpHalf : (p:ℝ)^(1/(2*(k:ℝ))) ≤ (p:ℝ)^((1:ℝ)/2) :=
    Real.rpow_le_rpow_of_exponent_le hp1 hexp_le_half
  have hp_sqrt_ge : (2:ℝ)^30 ≤ (p:ℝ)^((1:ℝ)/2) := by
    have h1 : (2:ℝ)^30 ≤ ((2:ℝ)^60)^((1:ℝ)/2) := by
      rw [← Real.rpow_natCast_mul (by norm_num : (0:ℝ) ≤ 2) 60 (1/2)]
      have he : (↑(60:ℕ) : ℝ) * ((1:ℝ)/2) = 30 := by norm_num
      rw [he]
      norm_num
    exact le_trans h1
      (Real.rpow_le_rpow (x := (2:ℝ)^60) (y := (p:ℝ)) (z := (1:ℝ)/2) (by positivity) hp60r (by norm_num))
  have h16sqrt : (16:ℝ) ≤ (p:ℝ)^((1:ℝ)/2) := le_trans (by norm_num) hp_sqrt_ge
  have h64sqrt : (64:ℝ) ≤ (p:ℝ)^((1:ℝ)/2) := le_trans (by norm_num) hp_sqrt_ge
  have h16p : (16:ℝ) * (p:ℝ)^(1/(2*(k:ℝ))) ≤ (p:ℝ) := by
    have h1 : (16:ℝ) * (p:ℝ)^(1/(2*(k:ℝ))) ≤ (p:ℝ)^((1:ℝ)/2) * (p:ℝ)^((1:ℝ)/2) :=
      mul_le_mul h16sqrt hpHalf (Real.rpow_nonneg hp0.le (1/(2*(k:ℝ)))) (Real.rpow_nonneg hp0.le ((1:ℝ)/2))
    have h2 : (p:ℝ)^((1:ℝ)/2) * (p:ℝ)^((1:ℝ)/2) = (p:ℝ) := by
      rw [← Real.rpow_add hp0]; norm_num
    linarith
  have h4p : (4:ℝ) * (p:ℝ)^(1 - 1/(2*(k:ℝ))) < (p:ℝ) := by
    have hsub : (p:ℝ)^(1 - 1/(2*(k:ℝ))) = (p:ℝ) / (p:ℝ)^(1/(2*(k:ℝ))) := by
      rw [Real.rpow_sub hp0, Real.rpow_one]
    have h1 : (p:ℝ) / (p:ℝ)^(1/(2*(k:ℝ))) ≤ (p:ℝ) / 8 :=
      div_le_div_of_nonneg_left hp0.le (by norm_num : (0:ℝ) < 8) h8le
    have h2 : (4:ℝ) * ((p:ℝ) / 8) = (p:ℝ) / 2 := by ring
    have h3 : (p:ℝ) / 2 < (p:ℝ) := by linarith
    linarith [hsub, h1, h2, h3]
  -- ### A and P
  set A : ℝ := (H:ℝ) * (p:ℝ)^(-(1/(2*(k:ℝ)))) with hAdef
  have hexp2 : 1/(2*(k:ℝ)) ≤ ((k:ℝ)+1)/(4*(k:ℝ)) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    push_cast; nlinarith [hk1]
  have hHlo' : (p:ℝ)^(1/(2*(k:ℝ))) ≤ (H:ℝ) :=
    le_trans (Real.rpow_le_rpow_of_exponent_le hp1 hexp2) hHlo
  have hA1 : 1 ≤ A := by
    have h := rpow_mul_inv_self hp0 (1/(2*(k:ℝ)))
    rw [hAdef]
    calc (1:ℝ) = (p:ℝ)^(1/(2*(k:ℝ))) * (p:ℝ)^(-(1/(2*(k:ℝ)))) := h.symm
      _ ≤ (H:ℝ) * (p:ℝ)^(-(1/(2*(k:ℝ)))) :=
          mul_le_mul_of_nonneg_right hHlo' (Real.rpow_nonneg hp0.le _)
  have hAnneg : (0:ℝ) ≤ A := le_trans zero_le_one hA1
  have hA2H : 2 * A ≤ (H:ℝ) := by
    have hpinv : (p:ℝ)^(-(1/(2*(k:ℝ)))) ≤ (1:ℝ)/2 := by
      rw [Real.rpow_neg hp0.le, inv_eq_one_div]
      exact le_trans (one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 8) h8le) (by norm_num)
    rw [hAdef]
    have h1 : (2:ℝ) * ((H:ℝ) * (p:ℝ)^(-(1/(2*(k:ℝ)))))
        = (H:ℝ) * (2 * (p:ℝ)^(-(1/(2*(k:ℝ))))) := by ring
    rw [h1]
    calc (H:ℝ) * (2 * (p:ℝ)^(-(1/(2*(k:ℝ))))) ≤ (H:ℝ) * 1 := by
          apply mul_le_mul_of_nonneg_left _ hHnn
          linarith
      _ = (H:ℝ) := by ring
  set P : ℕ := Nat.floor A + 1 with hPdef
  have hP1 : 1 ≤ P := by rw [hPdef]; omega
  have hPpos : (0:ℝ) < (P:ℝ) := by exact_mod_cast hP1
  have hPlow : A ≤ (P:ℝ) := by
    rw [hPdef]; push_cast
    exact le_of_lt (Nat.lt_floor_add_one A)
  have hPhigh : (P:ℝ) ≤ 2 * A := by
    rw [hPdef]; push_cast
    have h := Nat.floor_le hAnneg
    linarith
  have hPleH : (P:ℝ) ≤ (H:ℝ) := by linarith [hPhigh, hA2H]
  have hPx' : 2 * A = 2 * (H:ℝ) * (p:ℝ)^(-(1/(2*(k:ℝ)))) := by rw [hAdef]; ring
  have hPx : (P:ℝ) ≤ 2 * (H:ℝ) * (p:ℝ)^(-(1/(2*(k:ℝ)))) := by linarith [hPhigh, hPx']
  have h2P : 2*P < p := by
    have h2 : (4:ℝ) * A < (p:ℝ) := by
      rw [hAdef]
      have h3 : (4:ℝ) * ((H:ℝ) * (p:ℝ)^(-(1/(2*(k:ℝ)))))
          ≤ 4 * ((p:ℝ) * (p:ℝ)^(-(1/(2*(k:ℝ))))) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 4)
        exact mul_le_mul_of_nonneg_right (show (H:ℝ) ≤ (p:ℝ) by exact_mod_cast hHp)
          (Real.rpow_nonneg hp0.le (-(1/(2*(k:ℝ)))))
      have h4 : (4:ℝ) * ((p:ℝ) * (p:ℝ)^(-(1/(2*(k:ℝ))))) = 4 * (p:ℝ)^(1 - 1/(2*(k:ℝ))) := by
        rw [show (p:ℝ)^(1 - 1/(2*(k:ℝ))) = (p:ℝ) * (p:ℝ)^(-(1/(2*(k:ℝ)))) by
          rw [Real.rpow_sub hp0, Real.rpow_one, div_eq_mul_inv, Real.rpow_neg hp0.le]]
      linarith [h3, h4, h4p]
    have : (2:ℝ)*(P:ℝ) < (p:ℝ) := by linarith [hPhigh, h2]
    exact_mod_cast this
  -- ### the parameter hh
  set hh : ℕ := Nat.ceil ((H:ℝ)/(P:ℝ)) + 1 with hhhdef
  have hhhpos : 1 ≤ hh := by rw [hhhdef]; omega
  have hhhposR : (0:ℝ) < (hh:ℝ) := by exact_mod_cast hhhpos
  have hhhge : (H:ℝ)/(P:ℝ) ≤ (hh:ℝ) := by
    rw [hhhdef]; push_cast
    have h := Nat.le_ceil ((H:ℝ)/(P:ℝ))
    linarith
  have hhhle : (hh:ℝ) ≤ (H:ℝ)/(P:ℝ) + 2 := by
    rw [hhhdef]; push_cast
    have h := Nat.ceil_lt_add_one (show (0:ℝ) ≤ (H:ℝ)/(P:ℝ) by positivity)
    linarith
  have hhdivP1 : (1:ℝ) ≤ (H:ℝ)/(P:ℝ) := by
    rw [le_div_iff₀ hPpos]; linarith [hPleH]
  have hhlo : (H:ℝ)/(2*(P:ℝ)) ≤ (hh:ℝ) := by
    have h2 : (H:ℝ)/(2*(P:ℝ)) ≤ (H:ℝ)/(P:ℝ) :=
      div_le_div_of_nonneg_left hHnn (by linarith) (by linarith)
    linarith [hhhge, h2]
  have hhhle2 : (hh:ℝ) ≤ 4 * (p:ℝ)^(1/(2*(k:ℝ))) := by
    have h1 : (H:ℝ)/(P:ℝ) ≤ (p:ℝ)^(1/(2*(k:ℝ))) := by
      rw [div_le_iff₀ hPpos]
      have hmul : A * (p:ℝ)^(1/(2*(k:ℝ))) = (H:ℝ) := by
        rw [hAdef]; exact mul_rpow_neg_mul p H hp0 _
      rw [← hmul]
      calc A * (p:ℝ)^(1/(2*(k:ℝ))) ≤ (P:ℝ) * (p:ℝ)^(1/(2*(k:ℝ))) :=
            mul_le_mul_of_nonneg_right hPlow (Real.rpow_nonneg hp0.le _)
        _ = (p:ℝ)^(1/(2*(k:ℝ))) * (P:ℝ) := by ring
    have h3 : (1:ℝ) ≤ (p:ℝ)^(1/(2*(k:ℝ))) := le_trans (by norm_num) h2le
    linarith [hhhle, h1, h3]
  have hhh_le_p : (hh:ℝ) ≤ (p:ℝ) := by linarith [hhhle2, h16p]
  -- ### dyadic parameters
  set t : ℕ := Nat.log2 (2*hh) + 1 with htdef
  set K : ℕ := 2^t with hKdef
  have h2hhpos : 0 < 2*hh := by omega
  have hhhge1 : (H:ℝ)/(P:ℝ) + 1 ≤ (hh:ℝ) := by
    rw [hhhdef]; push_cast
    have h := Nat.le_ceil ((H:ℝ)/(P:ℝ))
    linarith
  have hKge : 2*hh ≤ K := by
    rw [hKdef, htdef, Nat.log2_eq_log_two]
    have h := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) (2*hh)
    simp only [Nat.succ_eq_add_one] at h
    exact le_of_lt h
  have hKle : K ≤ 4*hh := by
    rw [hKdef, htdef, Nat.log2_eq_log_two, pow_succ]
    have h := Nat.pow_log_le_self 2 (show 2*hh ≠ 0 by omega)
    calc 2 ^ Nat.log 2 (2 * hh) * 2 ≤ (2*hh) * 2 := Nat.mul_le_mul_right 2 h
      _ = 4*hh := by ring
  have hKp : K ≤ p := by
    have h1 : (K:ℝ) ≤ 4*(hh:ℝ) := by exact_mod_cast hKle
    have h2 : (4:ℝ)*(hh:ℝ) ≤ 4 * (4 * (p:ℝ)^(1/(2*(k:ℝ)))) :=
      mul_le_mul_of_nonneg_left hhhle2 (by norm_num : (0:ℝ) ≤ 4)
    have h3 : (4:ℝ) * (4 * (p:ℝ)^(1/(2*(k:ℝ)))) = 16 * (p:ℝ)^(1/(2*(k:ℝ))) := by ring
    have : (K:ℝ) ≤ (p:ℝ) := by linarith [h1, h2, h3, h16p]
    exact_mod_cast this
  -- ### H squared
  have hH2 : (H:ℝ)^2 ≤ (p:ℝ)^((2*(k:ℝ)+1)/(2*(k:ℝ))) * (Real.log p)^(8*k+16) := by
    have h1 := pow_le_pow_left₀ hHnn hHhi 2
    refine h1.trans (le_of_eq ?_)
    have hh1 : (((p:ℝ)^((2*(k:ℝ)+1)/(4*(k:ℝ)))))^2 = (p:ℝ)^((2*(k:ℝ)+1)/(2*(k:ℝ))) := by
      rw [← Real.rpow_natCast (x := (p:ℝ)^((2*(k:ℝ)+1)/(4*(k:ℝ)))) (n := 2),
        ← Real.rpow_mul hp0.le]
      congr 1
      push_cast
      ring
    have hh2 : ((Real.log p)^(4*k+8))^2 = (Real.log p)^(8*k+16) := by
      rw [← pow_mul]
      congr 1
      ring
    rw [mul_pow, hh1, hh2]
  -- ### object bounds for the Burgess principle
  have hlo : ∀ x ∈ objFinset P, -(2*(p:ℤ)) ≤ oLo N p x.1 x.2 - (hh:ℤ) ∧ oLo N p x.1 x.2 ≤ (p:ℤ) := by
    intro x hx
    obtain ⟨hx1, hx2, hx3⟩ := mem_objFinset.mp hx
    have hl1 : 1 ≤ x.1 := by omega
    have hL : (0:ℤ) < (x.1:ℤ) := by exact_mod_cast hl1
    have ha : (x.2:ℤ) ≤ (x.1:ℤ) := by exact_mod_cast (le_of_lt hx3)
    have haz : (0:ℤ) ≤ (x.2:ℤ) := Nat.cast_nonneg x.2
    have hap : (x.2:ℤ) * (p:ℤ) ≤ (x.1:ℤ) * (p:ℤ) :=
      mul_le_mul_of_nonneg_right ha (le_of_lt hpz)
    constructor
    · have key : (hh:ℤ) - 2*(p:ℤ) ≤ (N - (x.2:ℤ)*(p:ℤ)) / (x.1:ℤ) := by
        rw [Int.le_ediv_iff_mul_le hL]
        have hh1 : (hh:ℤ) * (x.1:ℤ) ≤ (p:ℤ) * (x.1:ℤ) := by
          apply mul_le_mul_of_nonneg_right _ (le_of_lt hL)
          exact_mod_cast hhh_le_p
        nlinarith [hh1, hap, hN0]
      simp only [oLo]
      linarith
    · have h1 : N - (x.2:ℤ)*(p:ℤ) ≤ N := by nlinarith [haz, le_of_lt hpz]
      have h2 : (1:ℤ) ≤ (x.1:ℤ) := by exact_mod_cast hl1
      have h3 : (p:ℤ) + 1 ≤ (p:ℤ) * (x.1:ℤ) + (x.1:ℤ) := by nlinarith [h2, le_of_lt hpz]
      simp only [oLo]
      rw [Int.ediv_le_iff_le_mul hL]
      linarith
  have hlen : ∀ x ∈ objFinset P, oHi N p H x.1 x.2 - oLo N p x.1 x.2 ≤ (hh:ℤ) := by
    intro x hx
    obtain ⟨hx1, hx2, hx3⟩ := mem_objFinset.mp hx
    have hl1 : 1 ≤ x.1 := by omega
    have hL : (0:ℤ) < (x.1:ℤ) := by exact_mod_cast hl1
    have hPl : P ≤ x.1 := by omega
    have hPposZ : (0:ℤ) < (P:ℤ) := by exact_mod_cast hP1
    have hHlt : (H:ℤ) < (hh:ℤ)*(P:ℤ) := by
      have h1 : ((H:ℝ)/(P:ℝ) + 1) * (P:ℝ) ≤ (hh:ℝ) * (P:ℝ) :=
        mul_le_mul_of_nonneg_right hhhge1 hPpos.le
      have h2 : ((H:ℝ)/(P:ℝ) + 1) * (P:ℝ) = (H:ℝ) + (P:ℝ) := by
        field_simp
      rw [h2] at h1
      have : (H:ℝ) < (hh:ℝ) * (P:ℝ) := by linarith
      exact_mod_cast this
    have h2 : (H:ℤ) / (x.1:ℤ) + 1 ≤ (hh:ℤ) := by
      have h3 : (H:ℤ) / (x.1:ℤ) ≤ (hh:ℤ) - 1 := by
        rw [Int.ediv_le_iff_le_mul hL]
        have heq : ((hh:ℤ) - 1) * (x.1:ℤ) + (x.1:ℤ) = (hh:ℤ) * (x.1:ℤ) := by ring
        rw [heq]
        have h4 : (hh:ℤ) * (P:ℤ) ≤ (hh:ℤ) * (x.1:ℤ) :=
          mul_le_mul_of_nonneg_left (show (P:ℤ) ≤ (x.1:ℤ) by exact_mod_cast hPl)
            (Nat.cast_nonneg hh)
        linarith
      linarith
    have hkey : (N + (H:ℤ) - (x.2:ℤ)*(p:ℤ))/(x.1:ℤ) - (N - (x.2:ℤ)*(p:ℤ))/(x.1:ℤ)
        ≤ (H:ℤ)/(x.1:ℤ) + 1 := by
      have h := Commons.NumberTheory.Auxiliary.ediv_add_sub_ediv_le hL (N - (x.2:ℤ)*(p:ℤ)) (H:ℤ) (Nat.cast_nonneg H)
      rw [show N - (x.2:ℤ)*(p:ℤ) + (H:ℤ) = N + (H:ℤ) - (x.2:ℤ)*(p:ℤ) by ring] at h
      exact h
    simp only [oHi, oLo]
    exact hkey.trans h2

  -- ### the Burgess chain
  have hsplitP : (P:ℝ) * ‖cSum χ N (N + (H:ℤ))‖
      ≤ ∑ x ∈ objFinset P, ‖cSum χ (oLo N p x.1 x.2) (oHi N p H x.1 x.2)‖ := by
    rw [sum_obj P (fun l a => ‖cSum χ (oLo N p l a) (oHi N p H l a)‖)]
    exact burgess_split χ N H P hP1 h2P
  have hprinc : (hh:ℝ) * (∑ x ∈ objFinset P, ‖cSum χ (oLo N p x.1 x.2) (oHi N p H x.1 x.2)‖)
      ≤ 2 * ∑ n ∈ Finset.Icc (-(2*(p:ℤ))) (p:ℤ), weightA N p hh P n * supShift χ n (2*hh) :=
    burgess_principle χ N H P hh hP1 h2P hlo hlen
  have hcollnn : (0:ℝ) ≤ collCount N p hh P := by
    unfold collCount
    exact Finset.sum_nonneg (fun x _ => Finset.sum_nonneg (fun y _ => by split <;> norm_num))
  have hPhhS : (P:ℝ) * (hh:ℝ) * ‖cSum χ N (N + (H:ℤ))‖
      ≤ 2 * ∑ n ∈ Finset.Icc (-(2*(p:ℤ))) (p:ℤ), weightA N p hh P n * supShift χ n (2*hh) := by
    calc (P:ℝ) * (hh:ℝ) * ‖cSum χ N (N + (H:ℤ))‖
        = (hh:ℝ) * ((P:ℝ) * ‖cSum χ N (N + (H:ℤ))‖) := by ring
      _ ≤ (hh:ℝ) * (∑ x ∈ objFinset P, ‖cSum χ (oLo N p x.1 x.2) (oHi N p H x.1 x.2)‖) :=
          mul_le_mul_of_nonneg_left hsplitP hhhposR.le
      _ ≤ 2 * ∑ n ∈ Finset.Icc (-(2*(p:ℤ))) (p:ℤ), weightA N p hh P n * supShift χ n (2*hh) := hprinc
  -- ### the three moment-type bounds
  have hAnn : ∀ n ∈ Finset.Icc (-(2*(p:ℤ))) (p:ℤ), 0 ≤ weightA N p hh P n :=
    fun n _ => weightA_nonneg N p hh P n
  have hMnn : ∀ n ∈ Finset.Icc (-(2*(p:ℤ))) (p:ℤ), 0 ≤ supShift χ n (2*hh) :=
    fun n _ => supShift_nonneg χ n (2*hh)
  have hAsum : ∑ n ∈ Finset.Icc (-(2*(p:ℤ))) (p:ℤ), weightA N p hh P n
      ≤ 2 * (P:ℝ)^2 * (hh:ℝ) := weight_sum_le N p hh P hP1 hlo
  have hA2sum : ∑ n ∈ Finset.Icc (-(2*(p:ℤ))) (p:ℤ), (weightA N p hh P n)^2
      ≤ (hh:ℝ) * collCount N p hh P := weight_sq_le N p hh P hP1 hlo
  have hKcast : ((K:ℕ):ℝ) = (2:ℝ)^t := by rw [hKdef]; push_cast; ring
  have hRK : ((2:ℝ)^t) = (K:ℝ) := hKcast.symm
  have hMsum : ∑ n ∈ Finset.Icc (-(2*(p:ℤ))) (p:ℤ), (supShift χ n (2*hh))^(2*k)
      ≤ 4 * ((t:ℝ)+1)^(2*k) * (4*Cm*((p:ℝ)*((K:ℝ))^k + ((K:ℝ))^(2*k)*Real.sqrt (p:ℝ))) := by
    have h := moment_W_le χ Cm k hk2 (fun L hL => hmom p χ hχ L hL) hh t K hKdef.symm hKge hKp
    simpa only [hRK] using h
  -- ### Holder + Cauchy-Schwarz in 2k-th power form
  have hSMsq : (∑ n ∈ Finset.Icc (-(2*(p:ℤ))) (p:ℤ),
        weightA N p hh P n * (supShift χ n (2*hh))^k)^2
      ≤ (∑ n ∈ Finset.Icc (-(2*(p:ℤ))) (p:ℤ), (weightA N p hh P n)^2)
        * (∑ n ∈ Finset.Icc (-(2*(p:ℤ))) (p:ℤ), (supShift χ n (2*hh))^(2*k)) := by
    have h := Commons.Analysis.MeanInequalities.sum_mul_sq_le (Finset.Icc (-(2*(p:ℤ))) (p:ℤ))
      (fun n => weightA N p hh P n) (fun n => supShift χ n (2*hh)) hAnn hMnn k
    have h2 : ∀ n, ((supShift χ n (2*hh))^k)^2 = (supShift χ n (2*hh))^(2*k) := by
      intro n
      rw [← pow_mul]
      congr 1
      omega
    simpa only [h2] using h
  have hhold : (∑ n ∈ Finset.Icc (-(2*(p:ℤ))) (p:ℤ),
        weightA N p hh P n * supShift χ n (2*hh))^(2*k)
      ≤ (∑ n ∈ Finset.Icc (-(2*(p:ℤ))) (p:ℤ), weightA N p hh P n)^(2*k-2)
        * ((∑ n ∈ Finset.Icc (-(2*(p:ℤ))) (p:ℤ), (weightA N p hh P n)^2)
          * (∑ n ∈ Finset.Icc (-(2*(p:ℤ))) (p:ℤ), (supShift χ n (2*hh))^(2*k))) := by
    have h1 := Commons.Analysis.MeanInequalities.sum_mul_pow_le (Finset.Icc (-(2*(p:ℤ))) (p:ℤ))
      (fun n => weightA N p hh P n) (fun n => supShift χ n (2*hh)) hAnn hMnn k hk1
    have h2 := pow_le_pow_left₀
      (pow_nonneg (Finset.sum_nonneg (fun n hn => mul_nonneg (hAnn n hn) (hMnn n hn))) k) h1 2
    rw [mul_pow] at h2
    have he1 : ((∑ n ∈ Finset.Icc (-(2*(p:ℤ))) (p:ℤ), weightA N p hh P n * supShift χ n (2*hh))^k)^2
        = (∑ n ∈ Finset.Icc (-(2*(p:ℤ))) (p:ℤ), weightA N p hh P n * supShift χ n (2*hh))^(2*k) := by
      rw [← pow_mul]; congr 1; omega
    have he2 : ((∑ n ∈ Finset.Icc (-(2*(p:ℤ))) (p:ℤ), weightA N p hh P n)^(k-1))^2
        = (∑ n ∈ Finset.Icc (-(2*(p:ℤ))) (p:ℤ), weightA N p hh P n)^(2*k-2) := by
      rw [← pow_mul]; congr 1; omega
    rw [he1, he2] at h2
    exact h2.trans (mul_le_mul_of_nonneg_left hSMsq
      (pow_nonneg (Finset.sum_nonneg hAnn) _))
  have hbig : ((P:ℝ) * (hh:ℝ) * ‖cSum χ N (N + (H:ℤ))‖)^(2*k)
      ≤ 2^(2*k) * (2 * (P:ℝ)^2 * (hh:ℝ))^(2*k-2) * ((hh:ℝ) * collCount N p hh P)
        * (4 * ((t:ℝ)+1)^(2*k)
            * (4*Cm*((p:ℝ)*((K:ℝ))^k + ((K:ℝ))^(2*k)*Real.sqrt (p:ℝ)))) := by
    have h1 := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ (P:ℝ) * (hh:ℝ) * ‖cSum χ N (N + (H:ℤ))‖) hPhhS (2*k)
    have h2 : (2 * ∑ n ∈ Finset.Icc (-(2*(p:ℤ))) (p:ℤ), weightA N p hh P n * supShift χ n (2*hh))^(2*k)
        = 2^(2*k) * (∑ n ∈ Finset.Icc (-(2*(p:ℤ))) (p:ℤ), weightA N p hh P n * supShift χ n (2*hh))^(2*k) :=
      mul_pow 2 _ (2*k)
    rw [h2] at h1
    have h3 : (∑ n ∈ Finset.Icc (-(2*(p:ℤ))) (p:ℤ), weightA N p hh P n * supShift χ n (2*hh))^(2*k)
        ≤ (2 * (P:ℝ)^2 * (hh:ℝ))^(2*k-2) * ((hh:ℝ) * collCount N p hh P)
          * (4 * ((t:ℝ)+1)^(2*k)
              * (4*Cm*((p:ℝ)*((K:ℝ))^k + ((K:ℝ))^(2*k)*Real.sqrt (p:ℝ)))) := by
      refine hhold.trans ?_
      have h5 : (∑ n ∈ Finset.Icc (-(2*(p:ℤ))) (p:ℤ), (weightA N p hh P n)^2)
            * (∑ n ∈ Finset.Icc (-(2*(p:ℤ))) (p:ℤ), (supShift χ n (2*hh))^(2*k))
          ≤ ((hh:ℝ) * collCount N p hh P)
            * (4 * ((t:ℝ)+1)^(2*k)
              * (4*Cm*((p:ℝ)*((K:ℝ))^k + ((K:ℝ))^(2*k)*Real.sqrt (p:ℝ)))) :=
        mul_le_mul hA2sum hMsum (Finset.sum_nonneg (fun n hn => pow_nonneg (hMnn n hn) _))
          (mul_nonneg (by positivity) hcollnn)
      refine (mul_le_mul_of_nonneg_left h5
        (pow_nonneg (Finset.sum_nonneg hAnn) (2*k-2))).trans ?_
      refine (mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (Finset.sum_nonneg hAnn) hAsum (2*k-2))
        (by positivity : (0:ℝ) ≤ (hh:ℝ) * collCount N p hh P * (4 * ((t:ℝ)+1)^(2*k)
          * (4*Cm*((p:ℝ)*((K:ℝ))^k + ((K:ℝ))^(2*k)*Real.sqrt (p:ℝ)))))).trans_eq ?_
      rw [← mul_assoc]
    have h3b : 2^(2*k) * ((2 * (P:ℝ)^2 * (hh:ℝ))^(2*k-2) * ((hh:ℝ) * collCount N p hh P)
          * (4 * ((t:ℝ)+1)^(2*k)
              * (4*Cm*((p:ℝ)*((K:ℝ))^k + ((K:ℝ))^(2*k)*Real.sqrt (p:ℝ)))))
        = 2^(2*k) * (2 * (P:ℝ)^2 * (hh:ℝ))^(2*k-2) * ((hh:ℝ) * collCount N p hh P)
          * (4 * ((t:ℝ)+1)^(2*k)
              * (4*Cm*((p:ℝ)*((K:ℝ))^k + ((K:ℝ))^(2*k)*Real.sqrt (p:ℝ)))) := by ring
    exact h1.trans ((mul_le_mul_of_nonneg_left h3 (by positivity : (0:ℝ) ≤ 2^(2*k))).trans_eq h3b)
  -- ### collCount bound
  set κ : ℝ := (P:ℝ)^2 * ((hh:ℝ)+2) / (p:ℝ) with hκdef
  have hhh2' : (hh:ℝ) + 2 ≤ 8 * (p:ℝ)^(1/(2*(k:ℝ))) := by
    have h4 : (1:ℝ) ≤ (p:ℝ)^(1/(2*(k:ℝ))) := Real.one_le_rpow hp1 (by positivity)
    linarith [hhhle2, h4]
  have hP2H : (P:ℝ)^2 ≤ 4 * (H:ℝ)^2 * (p:ℝ)^(-(1/(k:ℝ))) := by
    have h1 : (P:ℝ)^2 ≤ (2 * (H:ℝ) * (p:ℝ)^(-(1/(2*(k:ℝ)))))^2 :=
      pow_le_pow_left₀ (by positivity) hPx 2
    refine h1.trans (le_of_eq ?_)
    have hsq : ((p:ℝ)^(-(1/(2*(k:ℝ)))))^2 = (p:ℝ)^(-(1/(k:ℝ))) := by
      rw [← Real.rpow_natCast (x := (p:ℝ)^(-(1/(2*(k:ℝ))))) (n := 2), ← Real.rpow_mul hp0.le]
      congr 1
      push_cast
      ring
    rw [mul_pow, mul_pow, hsq]
    ring
  have hPsum : (P:ℝ)^2 * (hh:ℝ) ≤ 16 * (H:ℝ)^2 * (p:ℝ)^(-(1/(2*(k:ℝ)))) := by
    have h5 : (P:ℝ)^2 * (hh:ℝ)
        ≤ (4 * (H:ℝ)^2 * (p:ℝ)^(-(1/(k:ℝ)))) * (4 * (p:ℝ)^(1/(2*(k:ℝ)))) :=
      mul_le_mul hP2H hhhle2 (by positivity) (by positivity)
    refine h5.trans (le_of_eq ?_)
    rw [show 4 * (H:ℝ)^2 * (p:ℝ)^(-(1/(k:ℝ))) * (4 * (p:ℝ)^(1/(2*(k:ℝ))))
        = 16 * (H:ℝ)^2 * ((p:ℝ)^(-(1/(k:ℝ))) * (p:ℝ)^(1/(2*(k:ℝ)))) by ring]
    rw [← Real.rpow_add hp0]
    have he : -(1/(k:ℝ)) + 1/(2*(k:ℝ)) = -(1/(2*(k:ℝ))) := by ring
    rw [he]
  have hPsum1 : (1:ℝ) ≤ (P:ℝ)^2 * (hh:ℝ) := by
    have h1 : (1:ℝ) ≤ (P:ℝ)^2 := by
      have h2 : (1:ℝ) ≤ (P:ℝ) := by exact_mod_cast hP1
      calc (1:ℝ) = 1 * 1 := by ring
        _ ≤ (P:ℝ) * (P:ℝ) := mul_le_mul h2 h2 (by norm_num) (by norm_num)
        _ = (P:ℝ)^2 := (sq _).symm
    have h2 : (1:ℝ) ≤ (hh:ℝ) := by exact_mod_cast hhhpos
    calc (1:ℝ) = 1 * 1 := by ring
      _ ≤ (P:ℝ)^2 * (hh:ℝ) := mul_le_mul h1 h2 (by norm_num) (by positivity)
  have hn2k1 : 1 ≤ 2*k-1 := by omega
  have hH2k : (1:ℝ) ≤ (H:ℝ)^(2*k-2) * (p:ℝ)^(1/(2*(k:ℝ)) - 1) := by
    have h2 : ((p:ℝ)^(((k:ℝ)+1)/(4*(k:ℝ)))) ^ (2*k-2) ≤ (H:ℝ)^(2*k-2) :=
      pow_le_pow_left₀ (by positivity) hHlo (2*k-2)
    have h3 : ((p:ℝ)^(((k:ℝ)+1)/(4*(k:ℝ)))) ^ (2*k-2)
        = (p:ℝ)^(((k:ℝ)+1)/(4*(k:ℝ)) * ((2*k-2:ℕ):ℝ)) := by
      rw [← Real.rpow_natCast (x := (p:ℝ)^(((k:ℝ)+1)/(4*(k:ℝ)))) (n := 2*k-2),
        ← Real.rpow_mul hp0.le]
    have hexp : ((k:ℝ)+1)/(4*(k:ℝ)) * ((2*k-2:ℕ):ℝ) + (1/(2*(k:ℝ)) - 1) = (k:ℝ)/2 - 1 := by
      have h6a : ((2*k-2:ℕ):ℝ) = 2*(k:ℝ) - 2 := by
        rw [Nat.cast_sub (by omega : 2 ≤ 2*k)]; push_cast; ring
      rw [h6a]
      field_simp
      ring
    have h4 : (p:ℝ)^(((k:ℝ)+1)/(4*(k:ℝ)) * ((2*k-2:ℕ):ℝ)) * (p:ℝ)^(1/(2*(k:ℝ)) - 1)
        = (p:ℝ)^(((k:ℝ)+1)/(4*(k:ℝ)) * ((2*k-2:ℕ):ℝ) + (1/(2*(k:ℝ)) - 1)) :=
      (Real.rpow_add hp0 _ _).symm
    have h7 : (1:ℝ) ≤ (p:ℝ)^((k:ℝ)/2 - 1) := by
      have hexp0 : (0:ℝ) ≤ (k:ℝ)/2 - 1 := by linarith only [hkR2]
      calc (1:ℝ) = (p:ℝ)^(0:ℝ) := (Real.rpow_zero _).symm
        _ ≤ (p:ℝ)^((k:ℝ)/2 - 1) := Real.rpow_le_rpow_of_exponent_le hp1 hexp0
    calc (1:ℝ) ≤ (p:ℝ)^((k:ℝ)/2 - 1) := h7
      _ = (p:ℝ)^(((k:ℝ)+1)/(4*(k:ℝ)) * ((2*k-2:ℕ):ℝ) + (1/(2*(k:ℝ)) - 1)) := by rw [hexp]
      _ = (p:ℝ)^(((k:ℝ)+1)/(4*(k:ℝ)) * ((2*k-2:ℕ):ℝ)) * (p:ℝ)^(1/(2*(k:ℝ)) - 1) := h4.symm
      _ ≤ (H:ℝ)^(2*k-2) * (p:ℝ)^(1/(2*(k:ℝ)) - 1) := by
            have h2' : (p:ℝ)^(((k:ℝ)+1)/(4*(k:ℝ)) * ((2*k-2:ℕ):ℝ)) ≤ (H:ℝ)^(2*k-2) := by
              rw [← h3]; exact h2
            exact mul_le_mul_of_nonneg_right h2' (Real.rpow_nonneg hp0.le _)
  have hlog2P : Real.log (2 * (P:ℝ)) + 1 ≤ 2 * Real.log p := by
    have h1 : Real.log (2 * (P:ℝ)) ≤ Real.log p := by
      apply Real.log_le_log (by positivity)
      have : (2:ℝ)*(P:ℝ) < (p:ℝ) := by exact_mod_cast h2P
      linarith
    linarith [hL1]
  have hκle : κ ≤ 32 * (Real.log p)^(8*k+16) := by
    rw [hκdef, div_le_iff₀ hp0]
    have h2 : (P:ℝ)^2 * ((hh:ℝ)+2)
        ≤ (4 * (H:ℝ)^2 * (p:ℝ)^(-(1/(k:ℝ)))) * (8 * (p:ℝ)^(1/(2*(k:ℝ)))) :=
      mul_le_mul hP2H hhh2' (by positivity) (by positivity)
    refine h2.trans ?_
    have h4 : (H:ℝ)^2 ≤ (p:ℝ)^((2*(k:ℝ)+1)/(2*(k:ℝ))) * (Real.log p)^(8*k+16) := hH2
    have h5 : 4 * (H:ℝ)^2 * (p:ℝ)^(-(1/(k:ℝ))) * (8 * (p:ℝ)^(1/(2*(k:ℝ))))
        ≤ 4 * ((p:ℝ)^((2*(k:ℝ)+1)/(2*(k:ℝ))) * (Real.log p)^(8*k+16)) * (p:ℝ)^(-(1/(k:ℝ)))
          * (8 * (p:ℝ)^(1/(2*(k:ℝ)))) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact h4
    refine h5.trans (le_of_eq ?_)
    have hpe : (p:ℝ)^((2*(k:ℝ)+1)/(2*(k:ℝ))) * (p:ℝ)^(-(1/(k:ℝ))) * (p:ℝ)^(1/(2*(k:ℝ))) = (p:ℝ) := by
      have he : (2*(k:ℝ)+1)/(2*(k:ℝ)) + (-(1/(k:ℝ))) + (1/(2*(k:ℝ))) = 1 := by
        field_simp
        ring
      rw [← Real.rpow_add hp0, ← Real.rpow_add hp0, he, Real.rpow_one]
    rw [show 4 * ((p:ℝ)^((2*(k:ℝ)+1)/(2*(k:ℝ))) * (Real.log p)^(8*k+16)) * (p:ℝ)^(-(1/(k:ℝ)))
          * (8 * (p:ℝ)^(1/(2*(k:ℝ))))
        = 32 * (Real.log p)^(8*k+16) * ((p:ℝ)^((2*(k:ℝ)+1)/(2*(k:ℝ))) * (p:ℝ)^(-(1/(k:ℝ)))
            * (p:ℝ)^(1/(2*(k:ℝ)))) from by ring]
    rw [hpe]
  have hcoll : collCount N p hh P ≤ 20000 * (P:ℝ)^2 * (Real.log p)^(8*k+17) := by
    have h := collCount_le N p hh P (show 0 < p by omega) hP1
    have hRHS : collCount N p hh P
        ≤ 16 * κ * (P:ℝ) + 4 * (P:ℝ)^2
          + (8*κ + 4) * (16 * (P:ℝ)^2 * (Real.log (2*(P:ℝ)) + 1)) := by
      refine h.trans (le_of_eq ?_)
      rw [hκdef]
      ring
    have hpow : (Real.log p)^(8*k+16) ≤ (Real.log p)^(8*k+17) := pow_le_pow_right₀ hL1 (by omega)
    have hPleP2 : (P:ℝ) ≤ (P:ℝ)^2 := by
      have h2 : (1:ℝ) ≤ (P:ℝ) := by exact_mod_cast hP1
      calc (P:ℝ) = (P:ℝ) * 1 := by ring
        _ ≤ (P:ℝ) * (P:ℝ) := mul_le_mul_of_nonneg_left h2 hPpos.le
        _ = (P:ℝ)^2 := (sq _).symm
    have hb1 : 16 * κ * (P:ℝ) ≤ 512 * (P:ℝ)^2 * (Real.log p)^(8*k+16) := by
      have h1 : 16 * κ * (P:ℝ) ≤ 16 * (32 * (Real.log p)^(8*k+16)) * (P:ℝ) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_left hκle (by norm_num)
      have h2 : 16 * (32 * (Real.log p)^(8*k+16)) * (P:ℝ)
          ≤ 16 * (32 * (Real.log p)^(8*k+16)) * (P:ℝ)^2 :=
        mul_le_mul_of_nonneg_left hPleP2 (by positivity)
      calc 16 * κ * (P:ℝ) ≤ 16 * (32 * (Real.log p)^(8*k+16)) * (P:ℝ) := h1
        _ ≤ 16 * (32 * (Real.log p)^(8*k+16)) * (P:ℝ)^2 := h2
        _ = 512 * (P:ℝ)^2 * (Real.log p)^(8*k+16) := by ring
    have hb2 : 4 * (P:ℝ)^2 ≤ 4 * (P:ℝ)^2 * (Real.log p)^(8*k+17) := by
      have h1 : (1:ℝ) ≤ (Real.log p)^(8*k+17) := one_le_pow₀ hL1
      calc 4 * (P:ℝ)^2 = 4 * (P:ℝ)^2 * 1 := by ring
        _ ≤ 4 * (P:ℝ)^2 * (Real.log p)^(8*k+17) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
    have hb3 : (8*κ + 4) * (16 * (P:ℝ)^2 * (Real.log (2*(P:ℝ)) + 1))
        ≤ 13000 * (P:ℝ)^2 * (Real.log p)^(8*k+17) := by
      have h1 : 8*κ + 4 ≤ 12 * (32 * (Real.log p)^(8*k+16)) := by
        have h2 : (1:ℝ) ≤ (Real.log p)^(8*k+16) := one_le_pow₀ hL1
        have h3 := mul_le_mul_of_nonneg_left hκle (by norm_num : (0:ℝ) ≤ 8)
        linarith
      have h2 : (16:ℝ) * (P:ℝ)^2 * (Real.log (2*(P:ℝ)) + 1)
          ≤ (16:ℝ) * (P:ℝ)^2 * (2 * Real.log p) :=
        mul_le_mul_of_nonneg_left (by linarith [hlog2P]) (by positivity)
      have h3 : (8*κ+4) * (16 * (P:ℝ)^2 * (Real.log (2*(P:ℝ)) + 1))
          ≤ (12 * (32 * (Real.log p)^(8*k+16))) * (16 * (P:ℝ)^2 * (2*Real.log p)) :=
        mul_le_mul h1 h2 (mul_nonneg (by positivity)
          (add_nonneg (Real.log_nonneg (by linarith [hPpos])) (by norm_num))) (by positivity)
      refine h3.trans ?_
      have hLp : (Real.log p)^(8*k+16) * Real.log p = (Real.log p)^(8*k+17) := by
        rw [← pow_succ]
      calc (12 * (32 * (Real.log p)^(8*k+16))) * (16 * (P:ℝ)^2 * (2*Real.log p))
          = 12288 * (P:ℝ)^2 * ((Real.log p)^(8*k+16) * Real.log p) := by ring
        _ = 12288 * (P:ℝ)^2 * (Real.log p)^(8*k+17) := by rw [hLp]
        _ ≤ 13000 * (P:ℝ)^2 * (Real.log p)^(8*k+17) := by
            have h4 : (0:ℝ) ≤ (P:ℝ)^2 * (Real.log p)^(8*k+17) := by positivity
            linarith
    calc collCount N p hh P
        ≤ 16 * κ * (P:ℝ) + 4 * (P:ℝ)^2
          + (8*κ+4) * (16*(P:ℝ)^2*(Real.log (2*(P:ℝ))+1)) := hRHS
      _ ≤ 512 * (P:ℝ)^2 * (Real.log p)^(8*k+16) + 4 * (P:ℝ)^2 * (Real.log p)^(8*k+17)
            + 13000 * (P:ℝ)^2 * (Real.log p)^(8*k+17) := add_le_add (add_le_add hb1 hb2) hb3
      _ ≤ 20000 * (P:ℝ)^2 * (Real.log p)^(8*k+17) := by
          have h4 : 512 * (P:ℝ)^2 * (Real.log p)^(8*k+16)
              ≤ 512 * (P:ℝ)^2 * (Real.log p)^(8*k+17) :=
            mul_le_mul_of_nonneg_left hpow (by positivity)
          linarith [h4]
  -- ### t bound
  have hL20 : (20:ℝ) ≤ Real.log p := by
    have h1 : Real.log ((2:ℝ)^60) ≤ Real.log p := Real.log_le_log (by positivity) hp60r
    have h2 : Real.log ((2:ℝ)^60) = 60 * Real.log 2 := by rw [Real.log_pow]; norm_num
    have h3 : (20:ℝ) ≤ 60 * Real.log 2 := by linarith [Real.log_two_gt_d9]
    linarith
  have htb : ((t:ℝ)+1)^(2*k) ≤ 2^(2*k) * (Real.log p)^(2*k) := by
    have hK64 : ((2:ℝ)^t) ≤ 64 * (p:ℝ)^(1/(2*(k:ℝ))) := by
      have h1 : (K:ℝ) ≤ 4*(hh:ℝ) := by exact_mod_cast hKle
      have h2 : (4:ℝ)*(hh:ℝ) ≤ 4*(4*(p:ℝ)^(1/(2*(k:ℝ)))) :=
        mul_le_mul_of_nonneg_left hhhle2 (by norm_num : (0:ℝ) ≤ 4)
      have h3 : (K:ℝ) ≤ 64*(p:ℝ)^(1/(2*(k:ℝ))) := by linarith
      rwa [hKcast] at h3
    have hlog2pos : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    have hlog2ge : (2:ℝ)/3 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
    have hlogineq : (t:ℝ) * Real.log 2 ≤ 6 * Real.log 2 + (1/(2*(k:ℝ))) * Real.log p := by
      have h0 : (0:ℝ) < (2:ℝ)^t := by positivity
      have h1 := Real.log_le_log h0 hK64
      rw [Real.log_pow] at h1
      rw [Real.log_mul (by norm_num : (64:ℝ) ≠ 0) (by positivity : (p:ℝ)^(1/(2*(k:ℝ))) ≠ (0:ℝ))] at h1
      rw [Real.log_rpow hp0 (1/(2*(k:ℝ)))] at h1
      have h2 : Real.log 64 = 6 * Real.log 2 := by
        rw [show (64:ℝ) = (2:ℝ)^6 by norm_num, Real.log_pow]
        norm_num
      rw [h2] at h1
      exact h1
    have h4 : (1:ℝ)/(2*(k:ℝ)) ≤ (1:ℝ)/4 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; push_cast; linarith [hkR2]
    have ht1 : (t:ℝ) * Real.log 2 ≤ 6 * Real.log 2 + (Real.log p)/4 := by
      have h5 : (1/(2*(k:ℝ))) * Real.log p ≤ (Real.log p)/4 := by
        calc (1/(2*(k:ℝ))) * Real.log p ≤ ((1:ℝ)/4) * Real.log p :=
              mul_le_mul_of_nonneg_right h4 hLpos.le
          _ = (Real.log p)/4 := by ring
      linarith
    have ht2 : (t:ℝ) ≤ 6 + (Real.log p)/(4 * Real.log 2) := by
      have h6 : (t:ℝ) * Real.log 2 / Real.log 2
          ≤ (6 * Real.log 2 + (Real.log p)/4) / Real.log 2 :=
        div_le_div_of_nonneg_right ht1 hlog2pos.le
      rw [mul_div_cancel_right₀ _ (ne_of_gt hlog2pos)] at h6
      have h7 : (6 * Real.log 2 + (Real.log p)/4) / Real.log 2
          = 6 + (Real.log p)/(4*Real.log 2) := by
        rw [add_div, mul_div_cancel_right₀ 6 (ne_of_gt hlog2pos), div_div]
      rw [h7] at h6
      exact h6
    have hinv : (1:ℝ)/(4 * Real.log 2) ≤ (3:ℝ)/8 := by
      rw [div_le_iff₀ (by positivity)]
      linarith [hlog2ge]
    have ht4 : (t:ℝ) ≤ 6 + (3:ℝ)/8 * Real.log p := by
      have h8 : (Real.log p)/(4 * Real.log 2) = (Real.log p) * (1/(4 * Real.log 2)) := by ring
      rw [h8] at ht2
      have h9 := mul_le_mul_of_nonneg_left hinv hLpos.le
      linarith [ht2, h9]
    have ht5 : (t:ℝ) + 1 ≤ 2 * Real.log p := by linarith [ht4, hL20]
    have h10 := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ (t:ℝ)+1) ht5 (2*k)
    rwa [mul_pow] at h10
  -- ### moment bound
  have hK16 : (K:ℝ) ≤ 16 * (p:ℝ)^(1/(2*(k:ℝ))) := by
    have h1 : (K:ℝ) ≤ 4*(hh:ℝ) := by exact_mod_cast hKle
    have h2 : (4:ℝ)*(hh:ℝ) ≤ 4*(4*(p:ℝ)^(1/(2*(k:ℝ)))) :=
      mul_le_mul_of_nonneg_left hhhle2 (by norm_num : (0:ℝ) ≤ 4)
    linarith
  have hmomB : (p:ℝ)*((K:ℝ))^k + ((K:ℝ))^(2*k)*Real.sqrt (p:ℝ)
      ≤ 2*16^(2*k)*(p:ℝ)^((3:ℝ)/2) := by
    have hsqrt : Real.sqrt (p:ℝ) = (p:ℝ)^((1:ℝ)/2) := Real.sqrt_eq_rpow _
    have hpa : ((p:ℝ)^(1/(2*(k:ℝ))))^k = (p:ℝ)^((1:ℝ)/2) := by
      rw [← Real.rpow_natCast (x := (p:ℝ)^(1/(2*(k:ℝ)))) (n := k), ← Real.rpow_mul hp0.le]
      have he : (1/(2*(k:ℝ))) * ((k:ℕ):ℝ) = (1:ℝ)/2 := by
        push_cast
        field_simp
      rw [he]
    have hpa2 : ((p:ℝ)^(1/(2*(k:ℝ))))^(2*k) = (p:ℝ) := by
      rw [← Real.rpow_natCast (x := (p:ℝ)^(1/(2*(k:ℝ)))) (n := 2*k), ← Real.rpow_mul hp0.le]
      have he : (1/(2*(k:ℝ))) * ((2*k:ℕ):ℝ) = 1 := by
        push_cast
        field_simp
      rw [he, Real.rpow_one]
    have hKk : (K:ℝ)^k ≤ 16^k * (p:ℝ)^((1:ℝ)/2) := by
      calc (K:ℝ)^k ≤ (16 * (p:ℝ)^(1/(2*(k:ℝ))))^k := pow_le_pow_left₀ (by positivity) hK16 k
        _ = 16^k * ((p:ℝ)^(1/(2*(k:ℝ))))^k := by rw [mul_pow]
        _ = 16^k * (p:ℝ)^((1:ℝ)/2) := by rw [hpa]
    have hK2k : (K:ℝ)^(2*k) ≤ 16^(2*k) * (p:ℝ) := by
      calc (K:ℝ)^(2*k) ≤ (16 * (p:ℝ)^(1/(2*(k:ℝ))))^(2*k) :=
            pow_le_pow_left₀ (by positivity) hK16 (2*k)
        _ = 16^(2*k) * ((p:ℝ)^(1/(2*(k:ℝ))))^(2*k) := by rw [mul_pow]
        _ = 16^(2*k) * (p:ℝ) := by rw [hpa2]
    have hpadd : (p:ℝ) * (p:ℝ)^((1:ℝ)/2) = (p:ℝ)^((3:ℝ)/2) := by
      have h := Real.rpow_add hp0 (1:ℝ) ((1:ℝ)/2)
      rw [Real.rpow_one] at h
      rw [← h]
      norm_num
    have ha : (p:ℝ) * (K:ℝ)^k ≤ 16^k * (p:ℝ)^((3:ℝ)/2) := by
      have h1 : (p:ℝ) * (K:ℝ)^k ≤ (p:ℝ) * (16^k * (p:ℝ)^((1:ℝ)/2)) :=
        mul_le_mul_of_nonneg_left hKk hp0.le
      have h2 : (p:ℝ) * (16^k * (p:ℝ)^((1:ℝ)/2)) = 16^k * (p:ℝ)^((3:ℝ)/2) := by
        rw [show (p:ℝ) * (16^k * (p:ℝ)^((1:ℝ)/2)) = 16^k * ((p:ℝ) * (p:ℝ)^((1:ℝ)/2)) by ring,
          hpadd]
      linarith [h1, h2]
    have hb : (K:ℝ)^(2*k) * Real.sqrt (p:ℝ) ≤ 16^(2*k) * (p:ℝ)^((3:ℝ)/2) := by
      rw [hsqrt]
      have h1 : (K:ℝ)^(2*k) * (p:ℝ)^((1:ℝ)/2) ≤ (16^(2*k) * (p:ℝ)) * (p:ℝ)^((1:ℝ)/2) :=
        mul_le_mul_of_nonneg_right hK2k (by positivity)
      have h2 : (16^(2*k) * (p:ℝ)) * (p:ℝ)^((1:ℝ)/2) = 16^(2*k) * (p:ℝ)^((3:ℝ)/2) := by
        rw [show (16^(2*k) * (p:ℝ)) * (p:ℝ)^((1:ℝ)/2) = 16^(2*k) * ((p:ℝ) * (p:ℝ)^((1:ℝ)/2)) by ring,
          hpadd]
      linarith [h1, h2]
    have h16k : (16:ℝ)^k ≤ 16^(2*k) :=
      pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 16) (by omega : k ≤ 2*k)
    have h16k2 : 16^k * (p:ℝ)^((3:ℝ)/2) ≤ 16^(2*k) * (p:ℝ)^((3:ℝ)/2) :=
      mul_le_mul_of_nonneg_right h16k (by positivity)
    linarith [ha, hb, h16k2]
  have hPhh : (P:ℝ)^(2*k-2) * ((hh:ℝ))⁻¹
      ≤ 2^(2*k) * (H:ℝ)^(2*k-2) * (p:ℝ)^(1/(2*(k:ℝ)) - 1) := by
    have hinv : ((hh:ℝ))⁻¹ ≤ 2 * (P:ℝ) / (H:ℝ) := by
      rw [inv_le_comm₀ hhhposR (by positivity)]
      have he : (2 * (P:ℝ) / (H:ℝ))⁻¹ = (H:ℝ) / (2 * (P:ℝ)) := by rw [inv_div]
      rw [he]; exact hhlo
    have hPk : (P:ℝ)^(2*k-1) ≤ (2 * (H:ℝ) * (p:ℝ)^(-(1/(2*(k:ℝ)))))^(2*k-1) :=
      pow_le_pow_left₀ (by positivity) hPx (2*k-1)
    have hPk2 : (2 * (H:ℝ) * (p:ℝ)^(-(1/(2*(k:ℝ)))))^(2*k-1)
        = 2^(2*k-1) * (H:ℝ)^(2*k-1) * (p:ℝ)^(-(((2*k-1:ℕ):ℝ)/(2*(k:ℝ)))) := by
      have hp1 : ((p:ℝ)^(-(1/(2*(k:ℝ)))))^(2*k-1) = (p:ℝ)^(-(((2*k-1:ℕ):ℝ)/(2*(k:ℝ)))) := by
        rw [← Real.rpow_natCast (x := (p:ℝ)^(-(1/(2*(k:ℝ))))) (n := 2*k-1), ← Real.rpow_mul hp0.le]
        congr 1
        push_cast; ring
      rw [mul_pow, mul_pow, hp1]
    have key : (P:ℝ)^(2*k-2) * ((hh:ℝ))⁻¹
        ≤ 2^(2*k-1) * (H:ℝ)^(2*k-1) * (p:ℝ)^(-(((2*k-1:ℕ):ℝ)/(2*(k:ℝ)))) * (2 / (H:ℝ)) := by
      calc (P:ℝ)^(2*k-2) * ((hh:ℝ))⁻¹
          ≤ (P:ℝ)^(2*k-2) * (2 * (P:ℝ) / (H:ℝ)) := mul_le_mul_of_nonneg_left hinv (by positivity)
        _ = (P:ℝ)^(2*k-1) * (2 / (H:ℝ)) := by
              rw [show (P:ℝ)^(2*k-1) = (P:ℝ)^(2*k-2) * (P:ℝ) by
                rw [← pow_succ]; congr 1; omega]
              ring
        _ ≤ (2 * (H:ℝ) * (p:ℝ)^(-(1/(2*(k:ℝ)))))^(2*k-1) * (2 / (H:ℝ)) :=
              mul_le_mul_of_nonneg_right hPk (by positivity)
        _ = 2^(2*k-1) * (H:ℝ)^(2*k-1) * (p:ℝ)^(-(((2*k-1:ℕ):ℝ)/(2*(k:ℝ)))) * (2 / (H:ℝ)) := by
              rw [hPk2]
    refine key.trans (le_of_eq ?_)
    have he : -(((2*k-1:ℕ):ℝ)/(2*(k:ℝ))) = 1/(2*(k:ℝ)) - 1 := by
      have hea : ((2*k-1:ℕ):ℝ) = 2*(k:ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ 2*k)]; push_cast; ring
      rw [hea]; field_simp; ring
    have hHred : (H:ℝ)^(2*k-1) / (H:ℝ) = (H:ℝ)^(2*k-2) := by
      rw [div_eq_iff (ne_of_gt hHpos),
        show (H:ℝ)^(2*k-1) = (H:ℝ)^(2*k-2) * (H:ℝ) by
          rw [← pow_succ]; congr 1; omega]
    calc 2^(2*k-1) * (H:ℝ)^(2*k-1) * (p:ℝ)^(-(((2*k-1:ℕ):ℝ)/(2*(k:ℝ)))) * (2 / (H:ℝ))
        = 2^(2*k-1) * 2 * ((H:ℝ)^(2*k-1) / (H:ℝ)) * (p:ℝ)^(-(((2*k-1:ℕ):ℝ)/(2*(k:ℝ)))) := by ring
      _ = 2^(2*k-1) * 2 * (H:ℝ)^(2*k-2) * (p:ℝ)^(-(((2*k-1:ℕ):ℝ)/(2*(k:ℝ)))) := by rw [hHred]
      _ = 2^(2*k) * (H:ℝ)^(2*k-2) * (p:ℝ)^(1/(2*(k:ℝ)) - 1) := by
            rw [show (2:ℝ)^(2*k) = 2^(2*k-1) * 2 by rw [← pow_succ]; congr 1; omega, ← he]
  -- ### final monomial comparison
  have haux : (2:ℝ)^(2*k) * 2^(2*k-2) * 20000 * 4 * 2^(2*k) * 4 * 2 * 16^(2*k) * 2^(2*k) ≤ 2^68 := by
    have h1 : (2:ℝ)^(2*k) ≤ 2^6 := pow_le_pow_right₀ (by norm_num) (by omega)
    have h2 : (2:ℝ)^(2*k-2) ≤ 2^4 := pow_le_pow_right₀ (by norm_num) (by omega)
    have h3 : (16:ℝ)^(2*k) ≤ 2^24 := by
      rw [show (16:ℝ) = 2^4 by norm_num, ← pow_mul]
      exact pow_le_pow_right₀ (by norm_num) (by omega)
    have h4 : (2:ℝ)^(2*k) ≤ 2^6 := h1
    have h5 : (2:ℝ)^(2*k) ≤ 2^6 := h1
    have h6 : (20000:ℝ) * 4 * 4 * 2 ≤ 2^20 := by norm_num
    calc (2:ℝ)^(2*k) * 2^(2*k-2) * 20000 * 4 * 2^(2*k) * 4 * 2 * 16^(2*k) * 2^(2*k)
        = ((2:ℝ)^(2*k) * 2^(2*k-2) * 2^(2*k) * 16^(2*k) * 2^(2*k)) * (20000 * 4 * 4 * 2) := by ring
      _ ≤ (2^6 * 2^4 * 2^6 * 2^24 * 2^6) * 2^20 := by gcongr
      _ ≤ 2^68 := by norm_num
  have hhhpow : (hh:ℝ)^(2*k-1) = (hh:ℝ)^(2*k) * ((hh:ℝ))⁻¹ := by
    have h1 : (hh:ℝ)^(2*k) = (hh:ℝ)^(2*k-1) * (hh:ℝ) := by
      rw [← pow_succ]; congr 1; omega
    rw [h1, mul_assoc, mul_inv_cancel₀ (ne_of_gt hhhposR), mul_one]
  have hAlg2 : (2 * (P:ℝ)^2 * (hh:ℝ))^(2*k-2) * (P:ℝ)^2 * (hh:ℝ)
      = 2^(2*k-2) * (P:ℝ)^(4*k-2) * (hh:ℝ)^(2*k-1) := by
    have hP : (P:ℝ)^(2*(2*k-2)) * (P:ℝ)^2 = (P:ℝ)^(4*k-2) := by
      rw [← pow_add]; congr 1; omega
    have hhh : (hh:ℝ)^(2*k-2) * (hh:ℝ) = (hh:ℝ)^(2*k-1) := by
      rw [← pow_succ]; congr 1; omega
    have h2 : (2 * (P:ℝ)^2 * (hh:ℝ))^(2*k-2)
        = 2^(2*k-2) * ((P:ℝ)^2)^(2*k-2) * (hh:ℝ)^(2*k-2) := by rw [mul_pow, mul_pow]
    have h3 : ((P:ℝ)^2)^(2*k-2) = (P:ℝ)^(2*(2*k-2)) := (pow_mul (P:ℝ) 2 (2*k-2)).symm
    rw [h2, h3]
    calc 2^(2*k-2) * (P:ℝ)^(2*(2*k-2)) * (hh:ℝ)^(2*k-2) * (P:ℝ)^2 * (hh:ℝ)
        = 2^(2*k-2) * ((P:ℝ)^(2*(2*k-2)) * (P:ℝ)^2) * ((hh:ℝ)^(2*k-2) * (hh:ℝ)) := by ring
      _ = 2^(2*k-2) * (P:ℝ)^(4*k-2) * (hh:ℝ)^(2*k-1) := by rw [hP, hhh]
  have hLp : (Real.log p)^(8*k+17) * (Real.log p)^(2*k) = (Real.log p)^(10*k+17) := by
    rw [← pow_add]; congr 1; omega
  have hstep : 2^(2*k) * (2 * (P:ℝ)^2 * (hh:ℝ))^(2*k-2) * ((hh:ℝ) * (20000 * (P:ℝ)^2 * (Real.log p)^(8*k+17)))
        * (4 * (2^(2*k) * (Real.log p)^(2*k)) * (4*Cm*(2*16^(2*k)*(p:ℝ)^((3:ℝ)/2))))
      ≤ 2^(2*k) * 2^(2*k-2) * 20000 * 4 * 2^(2*k) * 4 * 2 * 16^(2*k) * Cm
        * (P:ℝ)^(4*k-2) * (hh:ℝ)^(2*k-1) * (Real.log p)^(10*k+17) * (p:ℝ)^((3:ℝ)/2) := by
    have h1 : 2^(2*k) * (2 * (P:ℝ)^2 * (hh:ℝ))^(2*k-2) * ((hh:ℝ) * (20000 * (P:ℝ)^2 * (Real.log p)^(8*k+17)))
          * (4 * (2^(2*k) * (Real.log p)^(2*k)) * (4*Cm*(2*16^(2*k)*(p:ℝ)^((3:ℝ)/2))))
        = 2^(2*k) * 20000 * 4 * 2^(2*k) * 4 * 2 * 16^(2*k) * Cm
          * ((2 * (P:ℝ)^2 * (hh:ℝ))^(2*k-2) * (P:ℝ)^2 * (hh:ℝ))
          * ((Real.log p)^(8*k+17) * (Real.log p)^(2*k)) * (p:ℝ)^((3:ℝ)/2) := by ring
    rw [h1, hAlg2, hLp]
    exact le_of_eq (by ring)
  have hmono : 2^(2*k) * (2 * (P:ℝ)^2 * (hh:ℝ))^(2*k-2) * ((hh:ℝ) * collCount N p hh P)
        * (4 * ((t:ℝ)+1)^(2*k) * (4*Cm*((p:ℝ)*((K:ℝ))^k + ((K:ℝ))^(2*k)*Real.sqrt (p:ℝ))))
      ≤ ((P:ℝ)^(2*k) * (hh:ℝ)^(2*k))
        * (2^68 * Cm * (H:ℝ)^(2*k-2) * (p:ℝ)^(((k:ℝ)+1)/(2*(k:ℝ))) * (Real.log p)^(10*k+17)) := by
    have s1 : 2^(2*k) * (2 * (P:ℝ)^2 * (hh:ℝ))^(2*k-2) * ((hh:ℝ) * collCount N p hh P)
          * (4 * ((t:ℝ)+1)^(2*k) * (4*Cm*((p:ℝ)*((K:ℝ))^k + ((K:ℝ))^(2*k)*Real.sqrt (p:ℝ))))
        ≤ 2^(2*k) * (2 * (P:ℝ)^2 * (hh:ℝ))^(2*k-2) * ((hh:ℝ) * (20000 * (P:ℝ)^2 * (Real.log p)^(8*k+17)))
          * (4 * ((t:ℝ)+1)^(2*k) * (4*Cm*((p:ℝ)*((K:ℝ))^k + ((K:ℝ))^(2*k)*Real.sqrt (p:ℝ)))) := by
      apply mul_le_mul_of_nonneg_right _
        (by positivity : (0:ℝ) ≤ 4 * ((t:ℝ)+1)^(2*k)
          * (4*Cm*((p:ℝ)*((K:ℝ))^k + ((K:ℝ))^(2*k)*Real.sqrt (p:ℝ))))
      apply mul_le_mul_of_nonneg_left _
        (by positivity : (0:ℝ) ≤ 2^(2*k) * (2 * (P:ℝ)^2 * (hh:ℝ))^(2*k-2))
      exact mul_le_mul_of_nonneg_left hcoll hhhposR.le
    have s2 : 2^(2*k) * (2 * (P:ℝ)^2 * (hh:ℝ))^(2*k-2) * ((hh:ℝ) * (20000 * (P:ℝ)^2 * (Real.log p)^(8*k+17)))
          * (4 * ((t:ℝ)+1)^(2*k) * (4*Cm*((p:ℝ)*((K:ℝ))^k + ((K:ℝ))^(2*k)*Real.sqrt (p:ℝ))))
        ≤ 2^(2*k) * (2 * (P:ℝ)^2 * (hh:ℝ))^(2*k-2) * ((hh:ℝ) * (20000 * (P:ℝ)^2 * (Real.log p)^(8*k+17)))
          * (4 * (2^(2*k) * (Real.log p)^(2*k)) * (4*Cm*(2*16^(2*k)*(p:ℝ)^((3:ℝ)/2)))) := by
      apply mul_le_mul_of_nonneg_left _
        (by positivity : (0:ℝ) ≤ 2^(2*k) * (2 * (P:ℝ)^2 * (hh:ℝ))^(2*k-2)
          * ((hh:ℝ) * (20000 * (P:ℝ)^2 * (Real.log p)^(8*k+17))))
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left htb (by norm_num : (0:ℝ) ≤ 4)
      · exact mul_le_mul_of_nonneg_left hmomB (by positivity : (0:ℝ) ≤ 4*Cm)
      · positivity
      · positivity
    have s4 : 2^(2*k) * 2^(2*k-2) * 20000 * 4 * 2^(2*k) * 4 * 2 * 16^(2*k) * Cm
          * (P:ℝ)^(4*k-2) * (hh:ℝ)^(2*k-1) * (Real.log p)^(10*k+17) * (p:ℝ)^((3:ℝ)/2)
        ≤ ((P:ℝ)^(2*k) * (hh:ℝ)^(2*k))
          * (2^68 * Cm * (H:ℝ)^(2*k-2) * (p:ℝ)^(((k:ℝ)+1)/(2*(k:ℝ))) * (Real.log p)^(10*k+17)) := by
      have hpc : (2:ℝ)^(2*k) * 2^(2*k-2) * 20000 * 4 * 2^(2*k) * 4 * 2 * 16^(2*k) * 2^(2*k) ≤ 2^68 := haux
      have hkey : 2^(2*k) * 2^(2*k-2) * 20000 * 4 * 2^(2*k) * 4 * 2 * 16^(2*k)
            * (P:ℝ)^(4*k-2) * (hh:ℝ)^(2*k-1) * (p:ℝ)^((3:ℝ)/2)
          ≤ ((P:ℝ)^(2*k) * (hh:ℝ)^(2*k))
            * (2^68 * (H:ℝ)^(2*k-2) * (p:ℝ)^(((k:ℝ)+1)/(2*(k:ℝ)))) := by
        have hPe : (P:ℝ)^(4*k-2) = (P:ℝ)^(2*k) * (P:ℝ)^(2*k-2) := by
          rw [← pow_add]; congr 1; omega
        have h1 : 2^(2*k) * 2^(2*k-2) * 20000 * 4 * 2^(2*k) * 4 * 2 * 16^(2*k)
              * (P:ℝ)^(4*k-2) * (hh:ℝ)^(2*k-1) * (p:ℝ)^((3:ℝ)/2)
            = ((P:ℝ)^(2*k) * (hh:ℝ)^(2*k))
              * ((2^(2*k) * 2^(2*k-2) * 20000 * 4 * 2^(2*k) * 4 * 2 * 16^(2*k))
                * ((P:ℝ)^(2*k-2) * ((hh:ℝ))⁻¹ * (p:ℝ)^((3:ℝ)/2))) := by
          rw [hPe, hhhpow]; ring
        rw [h1]
        apply mul_le_mul_of_nonneg_left _ (by positivity : (0:ℝ) ≤ (P:ℝ)^(2*k) * (hh:ℝ)^(2*k))
        have h3 : (P:ℝ)^(2*k-2) * ((hh:ℝ))⁻¹ * (p:ℝ)^((3:ℝ)/2)
            ≤ 2^(2*k) * (H:ℝ)^(2*k-2) * (p:ℝ)^(((k:ℝ)+1)/(2*(k:ℝ))) := by
          have hpadd : (p:ℝ)^(1/(2*(k:ℝ)) - 1) * (p:ℝ)^((3:ℝ)/2) = (p:ℝ)^(((k:ℝ)+1)/(2*(k:ℝ))) := by
            rw [← Real.rpow_add hp0]
            congr 1
            field_simp
            ring
          have h4 : (P:ℝ)^(2*k-2) * ((hh:ℝ))⁻¹ * (p:ℝ)^((3:ℝ)/2)
              ≤ (2^(2*k) * (H:ℝ)^(2*k-2) * (p:ℝ)^(1/(2*(k:ℝ)) - 1)) * (p:ℝ)^((3:ℝ)/2) :=
            mul_le_mul_of_nonneg_right hPhh (by positivity)
          refine h4.trans (le_of_eq ?_)
          calc (2^(2*k) * (H:ℝ)^(2*k-2) * (p:ℝ)^(1/(2*(k:ℝ)) - 1)) * (p:ℝ)^((3:ℝ)/2)
              = 2^(2*k) * (H:ℝ)^(2*k-2) * ((p:ℝ)^(1/(2*(k:ℝ)) - 1) * (p:ℝ)^((3:ℝ)/2)) := by ring
            _ = 2^(2*k) * (H:ℝ)^(2*k-2) * (p:ℝ)^(((k:ℝ)+1)/(2*(k:ℝ))) := by rw [hpadd]
        calc (2^(2*k) * 2^(2*k-2) * 20000 * 4 * 2^(2*k) * 4 * 2 * 16^(2*k))
              * ((P:ℝ)^(2*k-2) * ((hh:ℝ))⁻¹ * (p:ℝ)^((3:ℝ)/2))
            ≤ (2^(2*k) * 2^(2*k-2) * 20000 * 4 * 2^(2*k) * 4 * 2 * 16^(2*k))
              * (2^(2*k) * (H:ℝ)^(2*k-2) * (p:ℝ)^(((k:ℝ)+1)/(2*(k:ℝ)))) :=
              mul_le_mul_of_nonneg_left h3 (by positivity)
          _ = ((2^(2*k) * 2^(2*k-2) * 20000 * 4 * 2^(2*k) * 4 * 2 * 16^(2*k)) * 2^(2*k))
              * ((H:ℝ)^(2*k-2) * (p:ℝ)^(((k:ℝ)+1)/(2*(k:ℝ)))) := by ring
          _ ≤ 2^68 * ((H:ℝ)^(2*k-2) * (p:ℝ)^(((k:ℝ)+1)/(2*(k:ℝ)))) :=
              mul_le_mul_of_nonneg_right hpc (by positivity)
          _ = 2^68 * (H:ℝ)^(2*k-2) * (p:ℝ)^(((k:ℝ)+1)/(2*(k:ℝ))) := by ring
      calc 2^(2*k) * 2^(2*k-2) * 20000 * 4 * 2^(2*k) * 4 * 2 * 16^(2*k) * Cm
            * (P:ℝ)^(4*k-2) * (hh:ℝ)^(2*k-1) * (Real.log p)^(10*k+17) * (p:ℝ)^((3:ℝ)/2)
          = Cm * (Real.log p)^(10*k+17) * (2^(2*k) * 2^(2*k-2) * 20000 * 4 * 2^(2*k) * 4 * 2 * 16^(2*k)
              * (P:ℝ)^(4*k-2) * (hh:ℝ)^(2*k-1) * (p:ℝ)^((3:ℝ)/2)) := by ring
        _ ≤ Cm * (Real.log p)^(10*k+17) * (((P:ℝ)^(2*k) * (hh:ℝ)^(2*k))
              * (2^68 * (H:ℝ)^(2*k-2) * (p:ℝ)^(((k:ℝ)+1)/(2*(k:ℝ))))) :=
              mul_le_mul_of_nonneg_left hkey (by positivity)
        _ = ((P:ℝ)^(2*k) * (hh:ℝ)^(2*k))
              * (2^68 * Cm * (H:ℝ)^(2*k-2) * (p:ℝ)^(((k:ℝ)+1)/(2*(k:ℝ))) * (Real.log p)^(10*k+17)) := by ring
    exact s1.trans (s2.trans (hstep.trans s4))
  have hscaled : ((P:ℝ)^(2*k) * (hh:ℝ)^(2*k)) * ‖cSum χ N (N + (H:ℤ))‖^(2*k)
      ≤ ((P:ℝ)^(2*k) * (hh:ℝ)^(2*k))
        * (2^68 * Cm * (H:ℝ)^(2*k-2) * (p:ℝ)^(((k:ℝ)+1)/(2*(k:ℝ))) * (Real.log p)^(10*k+17)) := by
    have h1 : ((P:ℝ) * (hh:ℝ) * ‖cSum χ N (N + (H:ℤ))‖)^(2*k)
        = ((P:ℝ)^(2*k) * (hh:ℝ)^(2*k)) * ‖cSum χ N (N + (H:ℤ))‖^(2*k) := by
      rw [mul_pow, mul_pow]
    rw [h1] at hbig
    exact hbig.trans hmono
  have hpow : ‖cSum χ N (N + (H:ℤ))‖^(2*k)
      ≤ 2^68 * Cm * (H:ℝ)^(2*k-2) * (p:ℝ)^(((k:ℝ)+1)/(2*(k:ℝ))) * (Real.log p)^(10*k+17) :=
    le_of_mul_le_mul_left hscaled (by positivity)
  -- ### extract the 2k-th root
  have hRHSnn : (0:ℝ) ≤ 2^70 * Cm * (p:ℝ)^((k+1)/(4*k^2:ℝ)) * (H:ℝ)^(1 - 1/(k:ℝ)) * (Real.log p)^(10*k+20) := by
    have h1 : (0:ℝ) ≤ (p:ℝ)^((k+1)/(4*k^2:ℝ)) := Real.rpow_nonneg hp0.le _
    have h2 : (0:ℝ) ≤ (H:ℝ)^(1 - 1/(k:ℝ)) := Real.rpow_nonneg hHpos.le _
    have h3 : (0:ℝ) ≤ (Real.log p)^(10*k+20) := by positivity
    positivity
  have hsq : 2^68 * Cm * (H:ℝ)^(2*k-2) * (p:ℝ)^(((k:ℝ)+1)/(2*(k:ℝ))) * (Real.log p)^(10*k+17)
      ≤ (2^70 * Cm * (p:ℝ)^((k+1)/(4*k^2:ℝ)) * (H:ℝ)^(1 - 1/(k:ℝ)) * (Real.log p)^(10*k+20))^(2*k) := by
    have hp2 : ((p:ℝ)^((k+1)/(4*k^2:ℝ)))^(2*k) = (p:ℝ)^(((k:ℝ)+1)/(2*(k:ℝ))) := by
      have hpe : ((k:ℝ)+1)/(4*(k:ℝ)^2) * ((2*k:ℕ):ℝ) = ((k:ℝ)+1)/(2*(k:ℝ)) := by
        have hkne : (k:ℝ) ≠ 0 := ne_of_gt hkpos
        push_cast
        field_simp
        ring
      rw [← Real.rpow_natCast (x := (p:ℝ)^((k+1)/(4*k^2:ℝ))) (n := 2*k), ← Real.rpow_mul hp0.le, hpe]
    have hH2' : ((H:ℝ)^(1 - 1/(k:ℝ)))^(2*k) = (H:ℝ)^(2*k-2) := by
      have hHe : (1 - 1/(k:ℝ)) * ((2*k:ℕ):ℝ) = ((2*k-2:ℕ):ℝ) := by
        have hkne : (k:ℝ) ≠ 0 := ne_of_gt hkpos
        have hcast : ((2*k-2:ℕ):ℝ) = 2*(k:ℝ) - 2 := by
          rw [Nat.cast_sub (by omega : 2 ≤ 2*k)]; push_cast; ring
        rw [hcast]
        push_cast
        field_simp
      rw [← Real.rpow_natCast (x := (H:ℝ)^(1 - 1/(k:ℝ))) (n := 2*k), ← Real.rpow_mul hHpos.le, hHe,
        Real.rpow_natCast]
    have hL2 : ((Real.log p)^(10*k+20))^(2*k) = (Real.log p)^((10*k+20)*(2*k)) :=
      (pow_mul (Real.log p) (10*k+20) (2*k)).symm
    have hB : (2^70 * Cm * (p:ℝ)^((k+1)/(4*k^2:ℝ)) * (H:ℝ)^(1 - 1/(k:ℝ)) * (Real.log p)^(10*k+20))^(2*k)
        = 2^(70*(2*k)) * Cm^(2*k) * (p:ℝ)^(((k:ℝ)+1)/(2*(k:ℝ))) * (H:ℝ)^(2*k-2)
          * (Real.log p)^((10*k+20)*(2*k)) := by
      rw [show 2^70 * Cm * (p:ℝ)^((k+1)/(4*k^2:ℝ)) * (H:ℝ)^(1 - 1/(k:ℝ)) * (Real.log p)^(10*k+20)
          = (2^70 * Cm) * ((p:ℝ)^((k+1)/(4*k^2:ℝ)) * ((H:ℝ)^(1 - 1/(k:ℝ)) * (Real.log p)^(10*k+20))) from by ring]
      simp only [mul_pow]
      rw [← pow_mul, hp2, hH2', hL2]
      ring
    rw [hB]
    have hc : (2:ℝ)^68 * Cm ≤ 2^(70*(2*k)) * Cm^(2*k) := by
      have h2 : (2:ℝ)^68 ≤ 2^(70*(2*k)) :=
        pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) (by omega : 68 ≤ 70*(2*k))
      have h3 : Cm ≤ Cm^(2*k) := by
        have := pow_le_pow_right₀ hCm1 (show 1 ≤ 2*k by omega)
        simpa using this
      exact mul_le_mul h2 h3 (le_trans zero_le_one hCm1) (by positivity)
    have hL : (Real.log p)^(10*k+17) ≤ (Real.log p)^((10*k+20)*(2*k)) :=
      pow_le_pow_right₀ hL1 (by nlinarith [hk1])
    have h2 : (H:ℝ)^(2*k-2) * (p:ℝ)^(((k:ℝ)+1)/(2*(k:ℝ))) * (Real.log p)^(10*k+17)
        ≤ (H:ℝ)^(2*k-2) * (p:ℝ)^(((k:ℝ)+1)/(2*(k:ℝ))) * (Real.log p)^((10*k+20)*(2*k)) :=
      mul_le_mul_of_nonneg_left hL (by positivity)
    calc 2^68 * Cm * (H:ℝ)^(2*k-2) * (p:ℝ)^(((k:ℝ)+1)/(2*(k:ℝ))) * (Real.log p)^(10*k+17)
        = (2^68 * Cm) * ((H:ℝ)^(2*k-2) * (p:ℝ)^(((k:ℝ)+1)/(2*(k:ℝ))) * (Real.log p)^(10*k+17)) := by ring
      _ ≤ 2^(70*(2*k)) * Cm^(2*k) * ((H:ℝ)^(2*k-2) * (p:ℝ)^(((k:ℝ)+1)/(2*(k:ℝ))) * (Real.log p)^((10*k+20)*(2*k))) :=
            mul_le_mul hc h2 (by positivity) (by positivity)
      _ = 2^(70*(2*k)) * Cm^(2*k) * (p:ℝ)^(((k:ℝ)+1)/(2*(k:ℝ))) * (H:ℝ)^(2*k-2) * (Real.log p)^((10*k+20)*(2*k)) := by ring
  have hfin1 : ‖cSum χ N (N + (H:ℤ))‖
      ≤ (2^68 * Cm * (H:ℝ)^(2*k-2) * (p:ℝ)^(((k:ℝ)+1)/(2*(k:ℝ))) * (Real.log p)^(10*k+17))^(((2*k:ℕ):ℝ)⁻¹) := by
    have h2k : (0:ℝ) ≤ ‖cSum χ N (N + (H:ℤ))‖^(2*k) := by positivity
    have := Real.rpow_le_rpow h2k hpow (by positivity : (0:ℝ) ≤ ((2*k:ℕ):ℝ)⁻¹)
    rwa [Real.pow_rpow_inv_natCast (norm_nonneg _) (by omega : 2*k ≠ 0)] at this
  refine hfin1.trans ?_
  calc (2^68 * Cm * (H:ℝ)^(2*k-2) * (p:ℝ)^(((k:ℝ)+1)/(2*(k:ℝ))) * (Real.log p)^(10*k+17))^(((2*k:ℕ):ℝ)⁻¹)
      ≤ ((2^70 * Cm * (p:ℝ)^((k+1)/(4*k^2:ℝ)) * (H:ℝ)^(1 - 1/(k:ℝ)) * (Real.log p)^(10*k+20))^(2*k))^(((2*k:ℕ):ℝ)⁻¹) :=
        Real.rpow_le_rpow (by positivity) hsq (by positivity)
    _ = 2^70 * Cm * (p:ℝ)^((k+1)/(4*k^2:ℝ)) * (H:ℝ)^(1 - 1/(k:ℝ)) * (Real.log p)^(10*k+20) :=
        Real.pow_rpow_inv_natCast hRHSnn (by omega : 2*k ≠ 0)

/-- Periodicity of `cSum` under translation by a multiple of the modulus. -/
lemma cSum_add_q_mul (χ : DirichletCharacter ℂ q) (a b : ℤ) (j : ℕ) :
    cSum χ (a + (q:ℤ)*j) (b + (q:ℤ)*j) = cSum χ a b := by
  induction j with
  | zero => simp
  | succ j ih =>
    have h1 : a + (q:ℤ)*((j+1 : ℕ):ℤ) = (a + (q:ℤ)*j) + (q:ℤ) := by push_cast; ring
    have h2 : b + (q:ℤ)*((j+1 : ℕ):ℤ) = (b + (q:ℤ)*j) + (q:ℤ) := by push_cast; ring
    rw [h1, h2, cSum_add_q, ih]

lemma Ioc_eq_Icc' {N H : ℕ} (h : 1 ≤ H) : Finset.Ioc N (N+H) = Finset.Icc (N+1) (N+H) := by
  ext n
  rw [Finset.mem_Ioc, Finset.mem_Icc]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨by omega, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨by omega, h2⟩

theorem burgess_prime_of_moment
    (hmom : ∀ r : ℕ, 0 < r → ∃ C : ℝ, 0 < C ∧
       ∀ (p : ℕ) [Fact p.Prime] (χ : DirichletCharacter ℂ p), χ ≠ 1 → ∀ H : ℕ, H ≤ p →
         ∑ m ∈ Finset.range p, ‖∑ h ∈ Finset.Ioc m (m + H), χ (h : ZMod p)‖ ^ (2 * r)
           ≤ C * ((p : ℝ) * (H : ℝ) ^ r + (H : ℝ) ^ (2 * r) * Real.sqrt (p : ℝ)))
    {ε : ℝ} (hε : 0 < ε) (k : ℕ) (hk : k = 2 ∨ k = 3) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (p : ℕ) [Fact p.Prime] (χ : DirichletCharacter ℂ p),
        χ.IsPrimitive → χ ≠ 1 →
          ∀ {N H : ℕ}, 1 ≤ N → 1 ≤ H → H ≤ p →
            ‖∑ n ∈ Finset.Ioc N (N + H), χ (n : ZMod p)‖ ≤
              C * (p : ℝ) ^ ((k + 1 : ℝ) / (4 * k ^ 2) + ε) * (H : ℝ) ^ (1 - 1 / (k : ℝ)) := by
  have hk1 : 1 ≤ k := by omega
  have hk2 : 2 ≤ k := by omega
  have hk3 : k ≤ 3 := by omega
  have hkpos : 0 < k := by omega
  have hkposR : (0:ℝ) < (k:ℝ) := by exact_mod_cast hkpos
  have hk1R : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk1
  have hk2R : (2:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk2
  obtain ⟨Cm0, hCm0pos, hCm0⟩ := hmom k hkpos
  set Cm : ℝ := max Cm0 1 with hCmdef
  have hCm0le : Cm0 ≤ Cm := le_max_left _ _
  have hCm1 : 1 ≤ Cm := le_max_right _ _
  have hCmpos : 0 < Cm := lt_of_lt_of_le zero_lt_one hCm1
  have hCmC : ∀ (p : ℕ) [Fact p.Prime] (χ : DirichletCharacter ℂ p), χ ≠ 1 → ∀ L : ℕ, L ≤ p →
      ∑ m ∈ Finset.range p, ‖cSum χ (m:ℤ) ((m:ℤ) + L)‖^(2*k)
        ≤ Cm * ((p:ℝ) * (L:ℝ)^k + (L:ℝ)^(2*k) * Real.sqrt p) := by
    intro p hpF χ hχ L hL
    have h0 := hCm0 p χ hχ L hL
    have hsum : ∑ m ∈ Finset.range p, ‖cSum χ (m:ℤ) ((m:ℤ) + L)‖^(2*k)
        = ∑ m ∈ Finset.range p, ‖∑ h ∈ Finset.Ioc m (m + L), χ (h : ZMod p)‖ ^ (2*k) := by
      refine Finset.sum_congr rfl (fun m hm => ?_)
      rw [cSum_natCast]
    rw [hsum]
    exact h0.trans (mul_le_mul_of_nonneg_right hCm0le (by positivity))
  obtain ⟨Ccs, hCcspos, hCcs⟩ := charSum_range_le_polyaVinogradov
  obtain ⟨C1, hC1pos, hC1⟩ := Commons.Analysis.Real.log_pow_le_mul_rpow hε (10*k+20)
  have hBigpos : (0:ℝ) < 2^60 + 2^70 * Cm * C1 + 2 * Ccs + 1 := by positivity
  refine ⟨2^60 + 2^70 * Cm * C1 + 2 * Ccs + 1, hBigpos, ?_⟩
  intro p hpF χ hχprim hχne N H hN1 hH1 hHp
  have hpPrime : p.Prime := Fact.out
  have hp2 : 2 ≤ p := hpPrime.two_le
  have hp0 : (0:ℝ) < (p:ℝ) := by exact_mod_cast hpPrime.pos
  have hp1 : (1:ℝ) ≤ (p:ℝ) := by exact_mod_cast (show 1 ≤ p by omega)
  have hHpos : (0:ℝ) < (H:ℝ) := by exact_mod_cast hH1
  have hHnn : (0:ℝ) ≤ (H:ℝ) := hHpos.le
  have hσpos : (0:ℝ) < (k + 1 : ℝ) / (4 * k ^ 2) + ε := by
    have h1 : (0:ℝ) < (k + 1 : ℝ) / (4 * k ^ 2) := by positivity
    linarith
  have hσnn : (0:ℝ) ≤ (k + 1 : ℝ) / (4 * k ^ 2) + ε := hσpos.le
  have htriv : ∀ (N' H' : ℕ), ‖∑ n ∈ Finset.Ioc N' (N' + H'), χ (n : ZMod p)‖ ≤ (H':ℝ) := by
    intro N' H'
    calc ‖∑ n ∈ Finset.Ioc N' (N' + H'), χ (n : ZMod p)‖
        ≤ ∑ n ∈ Finset.Ioc N' (N' + H'), ‖χ (n : ZMod p)‖ := norm_sum_le _ _
      _ ≤ ∑ _n ∈ Finset.Ioc N' (N' + H'), (1:ℝ) :=
          Finset.sum_le_sum (fun n _ => DirichletCharacter.norm_le_one χ _)
      _ = (H':ℝ) := by
          rw [Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul, mul_one,
            show N' + H' - N' = H' by omega]
  rcases lt_or_ge p (2^60) with hp60 | hp60
  · -- ### case A: p < 2^60
    have hpexp : (p:ℝ)^((1:ℝ)/(k:ℝ) - ((k + 1 : ℝ) / (4 * k ^ 2) + ε)) ≤ 2^60 := by
      by_cases ha : (0:ℝ) ≤ (1:ℝ)/(k:ℝ) - ((k + 1 : ℝ) / (4 * k ^ 2) + ε)
      · have ha1 : (1:ℝ)/(k:ℝ) - ((k + 1 : ℝ) / (4 * k ^ 2) + ε) ≤ 1 := by
          have h1 : (1:ℝ)/(k:ℝ) ≤ 1 := by
            rw [div_le_one hkposR]; exact hk1R
          linarith [hσpos, h1]
        calc (p:ℝ)^((1:ℝ)/(k:ℝ) - ((k + 1 : ℝ) / (4 * k ^ 2) + ε))
            ≤ (((2^60 : ℕ)):ℝ)^((1:ℝ)/(k:ℝ) - ((k + 1 : ℝ) / (4 * k ^ 2) + ε)) :=
              Real.rpow_le_rpow hp0.le (by exact_mod_cast (le_of_lt hp60)) ha
          _ ≤ (((2^60 : ℕ)):ℝ)^(1:ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) ha1
          _ = (((2^60 : ℕ)):ℝ) := Real.rpow_one _
          _ = 2^60 := by norm_num
      · push_neg at ha
        have hpa : (1:ℝ) ≤ (p:ℝ)^(-((1:ℝ)/(k:ℝ) - ((k + 1 : ℝ) / (4 * k ^ 2) + ε))) :=
          Real.one_le_rpow hp1 (by linarith)
        calc (p:ℝ)^((1:ℝ)/(k:ℝ) - ((k + 1 : ℝ) / (4 * k ^ 2) + ε))
            = ((p:ℝ)^(-((1:ℝ)/(k:ℝ) - ((k + 1 : ℝ) / (4 * k ^ 2) + ε))))⁻¹ := by
              rw [Real.rpow_neg hp0.le, inv_inv]
          _ ≤ 1 := inv_le_one_of_one_le₀ hpa
          _ ≤ 2^60 := by norm_num
    have hsplit : (H:ℝ) = (H:ℝ)^((1:ℝ)/(k:ℝ)) * (H:ℝ)^(1 - 1/(k:ℝ)) := by
      rw [← Real.rpow_add hHpos]
      have he : (1:ℝ)/(k:ℝ) + (1 - 1/(k:ℝ)) = 1 := by ring
      rw [he, Real.rpow_one]
    have hHk : (H:ℝ)^((1:ℝ)/(k:ℝ)) ≤ (p:ℝ)^((1:ℝ)/(k:ℝ)) :=
      Real.rpow_le_rpow hHnn (by exact_mod_cast hHp) (by positivity)
    have hpσ_eq : (p:ℝ)^((1:ℝ)/(k:ℝ))
        = (p:ℝ)^((1:ℝ)/(k:ℝ) - ((k + 1 : ℝ) / (4 * k ^ 2) + ε))
          * (p:ℝ)^((k + 1 : ℝ) / (4 * k ^ 2) + ε) := by
      rw [← Real.rpow_add hp0]
      congr 1
      ring
    calc ‖∑ n ∈ Finset.Ioc N (N + H), χ (n : ZMod p)‖ ≤ (H:ℝ) := htriv N H
      _ = (H:ℝ)^((1:ℝ)/(k:ℝ)) * (H:ℝ)^(1 - 1/(k:ℝ)) := hsplit
      _ ≤ (p:ℝ)^((1:ℝ)/(k:ℝ)) * (H:ℝ)^(1 - 1/(k:ℝ)) :=
          mul_le_mul_of_nonneg_right hHk (Real.rpow_nonneg hHnn _)
      _ = (p:ℝ)^((1:ℝ)/(k:ℝ) - ((k + 1 : ℝ) / (4 * k ^ 2) + ε))
            * (p:ℝ)^((k + 1 : ℝ) / (4 * k ^ 2) + ε) * (H:ℝ)^(1 - 1/(k:ℝ)) := by
          rw [hpσ_eq]
      _ ≤ 2^60 * (p:ℝ)^((k + 1 : ℝ) / (4 * k ^ 2) + ε) * (H:ℝ)^(1 - 1/(k:ℝ)) := by
          apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hHnn _)
          exact mul_le_mul_of_nonneg_right hpexp (by positivity)
      _ ≤ (2^60 + 2^70 * Cm * C1 + 2 * Ccs + 1)
            * (p:ℝ)^((k + 1 : ℝ) / (4 * k ^ 2) + ε) * (H:ℝ)^(1 - 1/(k:ℝ)) := by
          apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hHnn _)
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          have h5 : (0:ℝ) ≤ 2^70 * Cm * C1 := by positivity
          have h6 : (0:ℝ) ≤ 2 * Ccs := by linarith [hCcspos]
          linarith
  · -- p ≥ 2^60
    have hL20 : (20:ℝ) ≤ Real.log p := by
      have h1 : Real.log ((2:ℝ)^60) ≤ Real.log p :=
        Real.log_le_log (by positivity) (by exact_mod_cast hp60)
      have h2 : Real.log ((2:ℝ)^60) = 60 * Real.log 2 := by rw [Real.log_pow]; norm_num
      have h3 : (20:ℝ) ≤ 60 * Real.log 2 := by linarith [Real.log_two_gt_d9]
      linarith
    by_cases hB : (H:ℝ) ≤ (p:ℝ)^((k + 1 : ℝ) / (4 * k : ℝ))
    · -- ### case B: H ≤ p^((k+1)/(4k))
      have hHk : (H:ℝ)^((1:ℝ)/(k:ℝ)) ≤ (p:ℝ)^((k + 1 : ℝ) / (4 * k ^ 2)) := by
        calc (H:ℝ)^((1:ℝ)/(k:ℝ)) ≤ ((p:ℝ)^((k + 1 : ℝ) / (4 * k : ℝ)))^((1:ℝ)/(k:ℝ)) :=
              Real.rpow_le_rpow hHnn hB (by positivity)
          _ = (p:ℝ)^((k + 1 : ℝ) / (4 * k : ℝ) * ((1:ℝ)/(k:ℝ))) := by
              rw [← Real.rpow_mul hp0.le]
          _ = (p:ℝ)^((k + 1 : ℝ) / (4 * k ^ 2)) := by
              congr 1
              field_simp
      have hsplit : (H:ℝ) = (H:ℝ)^((1:ℝ)/(k:ℝ)) * (H:ℝ)^(1 - 1/(k:ℝ)) := by
        rw [← Real.rpow_add hHpos]
        have he : (1:ℝ)/(k:ℝ) + (1 - 1/(k:ℝ)) = 1 := by ring
        rw [he, Real.rpow_one]
      calc ‖∑ n ∈ Finset.Ioc N (N + H), χ (n : ZMod p)‖ ≤ (H:ℝ) := htriv N H
        _ = (H:ℝ)^((1:ℝ)/(k:ℝ)) * (H:ℝ)^(1 - 1/(k:ℝ)) := hsplit
        _ ≤ (p:ℝ)^((k + 1 : ℝ) / (4 * k ^ 2)) * (H:ℝ)^(1 - 1/(k:ℝ)) :=
            mul_le_mul_of_nonneg_right hHk (Real.rpow_nonneg hHnn _)
        _ ≤ (2^60 + 2^70 * Cm * C1 + 2 * Ccs + 1)
              * (p:ℝ)^((k + 1 : ℝ) / (4 * k ^ 2) + ε) * (H:ℝ)^(1 - 1/(k:ℝ)) := by
            have h5 : (p:ℝ)^((k + 1 : ℝ) / (4 * k ^ 2))
                ≤ (p:ℝ)^((k + 1 : ℝ) / (4 * k ^ 2) + ε) :=
              Real.rpow_le_rpow_of_exponent_le hp1 (by linarith [hε])
            have h6 : (1:ℝ) ≤ 2^60 + 2^70 * Cm * C1 + 2 * Ccs + 1 := by
              have h7 : (0:ℝ) ≤ 2^70 * Cm * C1 := by positivity
              linarith [hCcspos, h7]
            calc (p:ℝ)^((k + 1 : ℝ) / (4 * k ^ 2)) * (H:ℝ)^(1 - 1/(k:ℝ))
                ≤ (p:ℝ)^((k + 1 : ℝ) / (4 * k ^ 2) + ε) * (H:ℝ)^(1 - 1/(k:ℝ)) :=
                  mul_le_mul_of_nonneg_right h5 (Real.rpow_nonneg hHnn _)
              _ ≤ (2^60 + 2^70 * Cm * C1 + 2 * Ccs + 1) * (p:ℝ)^((k + 1 : ℝ) / (4 * k ^ 2) + ε)
                    * (H:ℝ)^(1 - 1/(k:ℝ)) := by
                  rw [mul_assoc]
                  exact le_mul_of_one_le_left (by positivity) h6
    · push_neg at hB
      by_cases hC : (p:ℝ)^((2 * k + 1 : ℝ) / (4 * k : ℝ)) * (Real.log p)^(4*k+8) ≤ (H:ℝ)
      · -- ### case C: Polya-Vinogradov
        have hlog : Real.log (2*(p:ℝ) + 2) ≤ 2 * Real.log p := by
          calc Real.log (2*(p:ℝ) + 2) ≤ Real.log (4*(p:ℝ)) :=
                Real.log_le_log (by positivity) (by linarith)
            _ = Real.log 4 + Real.log (p:ℝ) :=
                Real.log_mul (by norm_num) (ne_of_gt hp0)
            _ = 2*Real.log 2 + Real.log p := by
                rw [show (4:ℝ) = (2:ℝ)^2 by norm_num, Real.log_pow]; norm_num
            _ ≤ 2 * Real.log p := by
                have h3 : (2:ℝ) * Real.log 2 ≤ 20 := by linarith [Real.log_two_lt_d9]
                linarith [hL20]
        have hS : ‖∑ n ∈ Finset.Ioc N (N + H), χ (n : ZMod p)‖
            ≤ Ccs * Real.sqrt (p:ℝ) * Real.log (2*(p:ℝ) + 2) := by
          rw [Ioc_eq_Icc' hH1]
          exact hCcs p hp2 χ hχne (N+1) (N+H) (by omega)
        set Me : ℝ := ((4*k+8 : ℕ) : ℝ) * (1 - 1/(k:ℝ)) with hmdef
        have hm1 : (1:ℝ) ≤ Me := by
          have h7 : (1:ℝ)/(k:ℝ) ≤ (1:ℝ)/2 := by
            rw [div_le_div_iff₀ hkposR (by norm_num : (0:ℝ) < 2)]
            linarith [hk2R]
          have h8 : (8:ℝ) ≤ ((4*k+8 : ℕ) : ℝ) := by push_cast; linarith [hk1R]
          have h9 : (1:ℝ)/2 ≤ 1 - 1/(k:ℝ) := by linarith
          rw [hmdef]
          nlinarith [h8, h9]
        have hmnn : (0:ℝ) ≤ Me := le_trans zero_le_one hm1
        have hLpos' : (0:ℝ) ≤ Real.log p := by linarith [hL20]
        have hL1' : (1:ℝ) ≤ Real.log p := by linarith [hL20]
        have hHlower : (p:ℝ)^(((2*k+1:ℝ)/(4*k:ℝ)) * (1 - 1/(k:ℝ))) * (Real.log p)^Me
            ≤ (H:ℝ)^(1 - 1/(k:ℝ)) := by
          have hpow : ((p:ℝ)^((2*k+1:ℝ)/(4*k:ℝ)) * (Real.log p)^(4*k+8))^(1 - 1/(k:ℝ))
              = (p:ℝ)^(((2*k+1:ℝ)/(4*k:ℝ)) * (1 - 1/(k:ℝ))) * (Real.log p)^Me := by
            have h2 : ((Real.log p)^(4*k+8))^(1 - 1/(k:ℝ)) = (Real.log p)^Me := by
              rw [hmdef, ← Real.rpow_natCast (x := Real.log p) (n := 4*k+8),
                ← Real.rpow_mul hLpos']
            rw [Real.mul_rpow (Real.rpow_nonneg hp0.le _) (pow_nonneg hLpos' _),
              ← Real.rpow_mul hp0.le, h2]
          rw [← hpow]
          exact Real.rpow_le_rpow (by positivity : (0:ℝ) ≤ (p:ℝ)^((2*k+1:ℝ)/(4*k:ℝ)) * (Real.log p)^(4*k+8)) hC (by
            have h3 : (1:ℝ)/(k:ℝ) ≤ 1 := by rw [div_le_one hkposR]; exact hk1R
            linarith)
        have hterm : (2:ℝ)*Ccs * Real.log p ≤ (2^60 + 2^70 * Cm * C1 + 2 * Ccs + 1)
            * (p:ℝ)^ε * (Real.log p)^Me := by
          have h1 : Real.log p ≤ (Real.log p)^Me := by
            have h2 := Real.rpow_le_rpow_of_exponent_le hL1' hm1
            rwa [Real.rpow_one] at h2
          have h2 : (0:ℝ) ≤ (Real.log p)^Me := by positivity
          have h3 : (2:ℝ)*Ccs ≤ 2^60 + 2^70 * Cm * C1 + 2 * Ccs + 1 := by
            have h5 : (0:ℝ) ≤ 2^70 * Cm * C1 := by positivity
            linarith
          have h4 : (1:ℝ) ≤ (p:ℝ)^ε := Real.one_le_rpow hp1 hε.le
          calc (2:ℝ)*Ccs * Real.log p
              ≤ (2^60 + 2^70 * Cm * C1 + 2 * Ccs + 1) * (Real.log p)^Me := by
                calc (2:ℝ)*Ccs * Real.log p
                    ≤ (2^60 + 2^70 * Cm * C1 + 2 * Ccs + 1) * Real.log p :=
                      mul_le_mul_of_nonneg_right h3 hLpos'
                  _ ≤ (2^60 + 2^70 * Cm * C1 + 2 * Ccs + 1) * (Real.log p)^Me :=
                      mul_le_mul_of_nonneg_left h1 (by positivity)
            _ ≤ (2^60 + 2^70 * Cm * C1 + 2 * Ccs + 1) * (p:ℝ)^ε * (Real.log p)^Me := by
                have h6 : (Real.log p)^Me ≤ (p:ℝ)^ε * (Real.log p)^Me :=
                  le_mul_of_one_le_left h2 h4
                calc (2^60 + 2^70 * Cm * C1 + 2 * Ccs + 1) * (Real.log p)^Me
                    ≤ (2^60 + 2^70 * Cm * C1 + 2 * Ccs + 1) * ((p:ℝ)^ε * (Real.log p)^Me) :=
                      mul_le_mul_of_nonneg_left h6 (by positivity)
                  _ = (2^60 + 2^70 * Cm * C1 + 2 * Ccs + 1) * (p:ℝ)^ε * (Real.log p)^Me := by ring
        have hσa : (k + 1 : ℝ) / (4 * k ^ 2) + ε + ((2*k+1:ℝ)/(4*k:ℝ)) * (1 - 1/(k:ℝ))
            = (1:ℝ)/2 + ε := by
          have hkne : (k:ℝ) ≠ 0 := ne_of_gt hkposR
          field_simp
          ring
        have hmid : (p:ℝ)^((1:ℝ)/2 + ε) * (Real.log p)^Me
            ≤ (p:ℝ)^((k + 1 : ℝ) / (4 * k ^ 2) + ε) * (H:ℝ)^(1 - 1/(k:ℝ)) := by
          have h1 : (p:ℝ)^((k + 1 : ℝ) / (4 * k ^ 2) + ε
                + ((2*k+1:ℝ)/(4*k:ℝ)) * (1 - 1/(k:ℝ))) = (p:ℝ)^((1:ℝ)/2 + ε) := by
            rw [hσa]
          calc (p:ℝ)^((1:ℝ)/2 + ε) * (Real.log p)^Me
              = (p:ℝ)^((k + 1 : ℝ) / (4 * k ^ 2) + ε
                  + ((2*k+1:ℝ)/(4*k:ℝ)) * (1 - 1/(k:ℝ))) * (Real.log p)^Me := by rw [h1]
            _ = (p:ℝ)^((k + 1 : ℝ) / (4 * k ^ 2) + ε)
                  * (p:ℝ)^(((2*k+1:ℝ)/(4*k:ℝ)) * (1 - 1/(k:ℝ))) * (Real.log p)^Me := by
                rw [Real.rpow_add hp0]
            _ ≤ (p:ℝ)^((k + 1 : ℝ) / (4 * k ^ 2) + ε) * (H:ℝ)^(1 - 1/(k:ℝ)) := by
                calc (p:ℝ)^((k + 1 : ℝ) / (4 * k ^ 2) + ε)
                      * (p:ℝ)^(((2*k+1:ℝ)/(4*k:ℝ)) * (1 - 1/(k:ℝ))) * (Real.log p)^Me
                    = (p:ℝ)^((k + 1 : ℝ) / (4 * k ^ 2) + ε)
                      * ((p:ℝ)^(((2*k+1:ℝ)/(4*k:ℝ)) * (1 - 1/(k:ℝ))) * (Real.log p)^Me) := by ring
                  _ ≤ (p:ℝ)^((k + 1 : ℝ) / (4 * k ^ 2) + ε) * (H:ℝ)^(1 - 1/(k:ℝ)) :=
                      mul_le_mul_of_nonneg_left hHlower (by positivity)
        have hmain : (2:ℝ)*Ccs * (p:ℝ)^((1:ℝ)/2) * (Real.log p)
            ≤ (2^60 + 2^70 * Cm * C1 + 2 * Ccs + 1) * (p:ℝ)^((1:ℝ)/2 + ε)
              * (Real.log p)^Me := by
          have he : (p:ℝ)^ε * (p:ℝ)^((1:ℝ)/2) = (p:ℝ)^((1:ℝ)/2 + ε) := by
            rw [← Real.rpow_add hp0]
            congr 1
            ring
          have h : (2:ℝ)*Ccs * (Real.log p) ≤ (2^60 + 2^70 * Cm * C1 + 2 * Ccs + 1)
              * (p:ℝ)^ε * (Real.log p)^Me := hterm
          calc (2:ℝ)*Ccs * (p:ℝ)^((1:ℝ)/2) * (Real.log p)
              = ((2:ℝ)*Ccs * (Real.log p)) * (p:ℝ)^((1:ℝ)/2) := by ring
            _ ≤ ((2^60 + 2^70 * Cm * C1 + 2 * Ccs + 1) * (p:ℝ)^ε * (Real.log p)^Me)
                  * (p:ℝ)^((1:ℝ)/2) :=
                mul_le_mul_of_nonneg_right h (Real.rpow_nonneg hp0.le _)
            _ = (2^60 + 2^70 * Cm * C1 + 2 * Ccs + 1) * (p:ℝ)^((1:ℝ)/2 + ε)
                  * (Real.log p)^Me := by
                rw [show ((2^60 + 2^70 * Cm * C1 + 2 * Ccs + 1) * (p:ℝ)^ε * (Real.log p)^Me)
                      * (p:ℝ)^((1:ℝ)/2)
                    = (2^60 + 2^70 * Cm * C1 + 2 * Ccs + 1) * ((p:ℝ)^ε * (p:ℝ)^((1:ℝ)/2))
                      * (Real.log p)^Me from by ring]
                rw [he]
        calc ‖∑ n ∈ Finset.Ioc N (N + H), χ (n : ZMod p)‖
            ≤ Ccs * Real.sqrt (p:ℝ) * Real.log (2*(p:ℝ) + 2) := hS
          _ ≤ Ccs * Real.sqrt (p:ℝ) * (2 * Real.log p) :=
              mul_le_mul_of_nonneg_left hlog (by positivity)
          _ = (2:ℝ)*Ccs * (p:ℝ)^((1:ℝ)/2) * (Real.log p) := by
              rw [Real.sqrt_eq_rpow]; ring
          _ ≤ (2^60 + 2^70 * Cm * C1 + 2 * Ccs + 1) * (p:ℝ)^((1:ℝ)/2 + ε)
                * (Real.log p)^Me := hmain
          _ ≤ (2^60 + 2^70 * Cm * C1 + 2 * Ccs + 1)
                * (p:ℝ)^((k + 1 : ℝ) / (4 * k ^ 2) + ε) * (H:ℝ)^(1 - 1/(k:ℝ)) := by
              rw [show (2^60 + 2^70 * Cm * C1 + 2 * Ccs + 1) * (p:ℝ)^((1:ℝ)/2 + ε)
                    * (Real.log p)^Me
                  = (2^60 + 2^70 * Cm * C1 + 2 * Ccs + 1)
                    * ((p:ℝ)^((1:ℝ)/2 + ε) * (Real.log p)^Me) from by ring]
              refine (mul_le_mul_of_nonneg_left hmid
                (by positivity : (0:ℝ) ≤ 2^60 + 2^70 * Cm * C1 + 2 * Ccs + 1)).trans_eq ?_
              ring
      · -- ### case D: core
        push_neg at hC
        have hHhi : (H:ℝ) ≤ (p:ℝ)^((2 * k + 1 : ℝ) / (4 * k : ℝ)) * (Real.log p)^(4*k+8) := le_of_lt hC
        have hHlo : (p:ℝ)^((k + 1 : ℝ) / (4 * k : ℝ)) ≤ (H:ℝ) := le_of_lt hB
        have hcore : ‖cSum χ ((N % p : ℕ) : ℤ) (((N % p : ℕ) : ℤ) + (H:ℤ))‖
            ≤ 2^70 * Cm * (p:ℝ)^((k + 1 : ℝ) / (4 * k ^ 2)) * (H:ℝ)^(1 - 1/(k:ℝ))
              * (Real.log p)^(10*k+20) :=
          burgess_core Cm hCm1 k hk2 hk3 hCmC hp60 χ hχne ((N % p : ℕ) : ℤ)
            (Nat.cast_nonneg _) (by exact_mod_cast Nat.mod_lt N (by omega))
            H hH1 hHp hHlo hHhi
        have hmod : cSum χ (N:ℤ) ((N:ℤ) + (H:ℤ))
            = cSum χ ((N % p : ℕ) : ℤ) (((N % p : ℕ) : ℤ) + (H:ℤ)) := by
          have hN : (N:ℤ) = ((N % p : ℕ) : ℤ) + (p:ℤ) * ((N / p : ℕ) : ℤ) := by
            have h := Nat.mod_add_div N p
            exact_mod_cast h.symm
          rw [hN]
          have key := cSum_add_q_mul χ ((N % p : ℕ) : ℤ) (((N % p : ℕ) : ℤ) + (H:ℤ)) (N/p)
          rw [show ((N % p : ℕ) : ℤ) + (p:ℤ) * ((N / p : ℕ) : ℤ) + (H:ℤ)
              = ((N % p : ℕ) : ℤ) + (H:ℤ) + (p:ℤ) * ((N / p : ℕ) : ℤ) by ring]
          exact key
        have hlogabs : (Real.log p)^(10*k+20) ≤ C1 * (p:ℝ)^ε := hC1 p hp1
        calc ‖∑ n ∈ Finset.Ioc N (N + H), χ (n : ZMod p)‖
            = ‖cSum χ (N:ℤ) ((N:ℤ) + (H:ℤ))‖ := by rw [cSum_natCast]
          _ = ‖cSum χ ((N % p : ℕ) : ℤ) (((N % p : ℕ) : ℤ) + (H:ℤ))‖ := by rw [hmod]
          _ ≤ 2^70 * Cm * (p:ℝ)^((k + 1 : ℝ) / (4 * k ^ 2)) * (H:ℝ)^(1 - 1/(k:ℝ))
                * (Real.log p)^(10*k+20) := hcore
          _ ≤ 2^70 * Cm * (p:ℝ)^((k + 1 : ℝ) / (4 * k ^ 2)) * (H:ℝ)^(1 - 1/(k:ℝ))
                * (C1 * (p:ℝ)^ε) := by
              apply mul_le_mul_of_nonneg_left hlogabs (by positivity)
          _ = 2^70 * Cm * C1 * ((p:ℝ)^((k + 1 : ℝ) / (4 * k ^ 2)) * (p:ℝ)^ε)
                * (H:ℝ)^(1 - 1/(k:ℝ)) := by ring
          _ = 2^70 * Cm * C1 * (p:ℝ)^((k + 1 : ℝ) / (4 * k ^ 2) + ε)
                * (H:ℝ)^(1 - 1/(k:ℝ)) := by rw [← Real.rpow_add hp0]
          _ ≤ (2^60 + 2^70 * Cm * C1 + 2 * Ccs + 1)
                * (p:ℝ)^((k + 1 : ℝ) / (4 * k ^ 2) + ε) * (H:ℝ)^(1 - 1/(k:ℝ)) := by
              apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hHnn _)
              apply mul_le_mul_of_nonneg_right _ (by positivity)
              linarith [hCmpos, hC1pos, hCcspos]


end Commons.NumberTheory.DirichletCharacter
