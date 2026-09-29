import Mathlib
import Submission.Work.ConvR.basic
import Submission.Work.ConvR.convDefs
import Submission.Work.SynFFT.yMulFacts
import Submission.Work.SynFFT.yMulLinear
import Submission.Work.DFT.charSumGen
import Submission.Work.DFT.charSumConv
import Submission.Work.DFT.digitsBij
import Submission.Work.DFT.phaseLin
import Submission.Work.ConvR.synExp_sub3

set_option autoImplicit false
set_option maxHeartbeats 1600000

open scoped BigOperators

namespace Work.ConvR

open HvdH

/-! ## Small facts about `yMul`

`HvdH.yMul r e` is multiplication by `y^e` in `R = ℂ[y]/(y^r+1)` (`y^r = -1`).  We record the
consequences of `Work.SynFFT.yMulFacts` used below. -/

private lemma yMZero (r : ℕ) (hr : 0 < r) (a : Fin r → ℂ) : HvdH.yMul r 0 a = a :=
  (Work.SynFFT.yMulFacts r hr).2.1 a

private lemma yMExpAdd (r : ℕ) (hr : 0 < r) (e e' : ℤ) (a : Fin r → ℂ) :
    HvdH.yMul r (e + e') a = HvdH.yMul r e (HvdH.yMul r e' a) :=
  (Work.SynFFT.yMulFacts r hr).1 e e' a

/-- `yMul r e` is the identity whenever `yMul r e` is the identity. -/
private lemma yMul_zsmul_id (r : ℕ) (hr : 0 < r) (e : ℤ)
    (he : ∀ a : Fin r → ℂ, HvdH.yMul r e a = a) (m : ℤ) (a : Fin r → ℂ) :
    HvdH.yMul r (e * m) a = a := by
  obtain ⟨hExpAdd, hZero, _hAdd, _hSmul, _hSign, _hPeriod, _hTwoR, _hHalf⟩ :=
    Work.SynFFT.yMulFacts r hr
  have hnat : ∀ n : ℕ, HvdH.yMul r (e * n) a = a := by
    intro n
    induction n with
    | zero => simpa using hZero a
    | succ n ih =>
      have h : e * ((n + 1 : ℕ) : ℤ) = e * n + e := by rw [Nat.cast_add, Nat.cast_one]; ring
      rw [h, hExpAdd (e * n) e a, he]
      exact ih
  rcases Int.eq_nat_or_neg m with ⟨n, hn | hn⟩
  · rw [hn]; exact hnat n
  · rw [hn]
    have h1 : e * -(n : ℤ) = -(e * n) := by ring
    rw [h1]
    calc HvdH.yMul r (-(e * n)) a
        = HvdH.yMul r (-(e * n)) (HvdH.yMul r (e * n) a) := by rw [hnat n]
      _ = HvdH.yMul r (-(e * n) + e * n) a := (hExpAdd _ _ a).symm
      _ = HvdH.yMul r 0 a := by ring_nf
      _ = a := hZero a

/-- `yMul r (2 * (r : ℤ) * m) = id`: `y^{2r m} = 1`. -/
private lemma yMul_twoR_mul (r : ℕ) (hr : 0 < r) (m : ℤ) (a : Fin r → ℂ) :
    HvdH.yMul r (2 * (r : ℤ) * m) a = a := by
  obtain ⟨_hExpAdd, _hZero, _hAdd, _hSmul, _hSign, _hPeriod, hTwoR, _hHalf⟩ :=
    Work.SynFFT.yMulFacts r hr
  exact yMul_zsmul_id r hr (2 * (r : ℤ)) (fun b => hTwoR b) m a

/-- If `yMul r e` is the negation, then so is `yMul r (e * m)` for every odd `m`. -/
private lemma yMul_neg_odd (r : ℕ) (hr : 0 < r) (e : ℤ)
    (he : ∀ a : Fin r → ℂ, HvdH.yMul r e a = -a) (m : ℤ) (hm : Odd m) (a : Fin r → ℂ) :
    HvdH.yMul r (e * m) a = -a := by
  obtain ⟨hExpAdd, _hZero, _hAdd, _hSmul, _hSign, _hPeriod, _hTwoR, _hHalf⟩ :=
    Work.SynFFT.yMulFacts r hr
  have h2 : ∀ b : Fin r → ℂ, HvdH.yMul r (e * 2) b = b := by
    intro b
    have h : e * 2 = e + e := by ring
    rw [h, hExpAdd e e b, he, he]
    exact neg_neg b
  obtain ⟨k, hk⟩ := hm
  have hem : e * m = e * 2 * k + e := by rw [hk]; ring
  rw [hem, hExpAdd (e * 2 * k) e a]
  rw [he, yMul_zsmul_id r hr (e * 2) h2 k (-a)]

/-- `yMul r (r * m) = -id` for odd `m` (`y^r = -1`). -/
private lemma yMul_odd_mul_r (r : ℕ) (hr : 0 < r) (m : ℤ) (hm : Odd m) (a : Fin r → ℂ) :
    HvdH.yMul r ((r : ℤ) * m) a = -a := by
  obtain ⟨_hExpAdd, _hZero, _hAdd, _hSmul, _hSign, _hPeriod, _hTwoR, hHalf⟩ :=
    Work.SynFFT.yMulFacts r hr
  have he : ∀ b : Fin r → ℂ, HvdH.yMul r (r : ℤ) b = -b := hHalf
  exact yMul_neg_odd r hr (r : ℤ) he m hm a

/-! ## The one-dimensional character sum

For `r = 2^a` and `t = 2^b` with `b ≤ a + 1`, the sum of `y^{c (2r/t) q}` over `q < t` is `t`
when `t ∣ c` and `0` otherwise.  The induction is on `b`: splitting the index range in two halves
turns the sum into `S + y^{cr} S`; if `c` is odd then `y^{cr} = -1` and the two halves cancel,
while if `c = 2c'` then `y^{cr} = 1` and the sum is twice the sum at level `b - 1` for `c'`. -/

private lemma yCharSum_pow2 (a : ℕ) (W : Fin (2 ^ a) → ℂ) :
    ∀ b : ℕ, b ≤ a + 1 → ∀ c : ℤ,
      (∑ q : Fin (2 ^ b),
          HvdH.yMul (2 ^ a) (c * (((2 * 2 ^ a / 2 ^ b) * (q : ℕ) : ℕ) : ℤ)) W)
        = if ((2 ^ b : ℕ) : ℤ) ∣ c then (((2 ^ b : ℕ) : ℂ)) • W else 0 := by
  have hr : 0 < 2 ^ a := pow_pos (by norm_num) a
  have hlin : ∀ (e : ℤ) (s : Finset ℕ) (f : ℕ → Fin (2 ^ a) → ℂ),
      HvdH.yMul (2 ^ a) e (∑ i ∈ s, f i) = ∑ i ∈ s, HvdH.yMul (2 ^ a) e (f i) :=
    (Work.SynFFT.yMulLinear (ι := ℕ) (2 ^ a)).2
  intro b
  induction b with
  | zero =>
    intro _ c
    show (∑ q : Fin 1, HvdH.yMul (2 ^ a) (c * (((2 * 2 ^ a / 1) * (q : ℕ) : ℕ) : ℤ)) W)
        = if ((1 : ℕ) : ℤ) ∣ c then (((1 : ℕ) : ℂ)) • W else 0
    rw [Fin.sum_univ_one]
    simp [yMZero (2 ^ a) hr W]
  | succ b ih =>
    intro hb c
    have hba : b ≤ a := by omega
    -- arithmetical facts about the leading coefficient `2r/2^b`
    have hpow1 : (2 : ℕ) * 2 ^ a = 2 ^ (a + 1) := by rw [mul_comm, ← pow_succ]
    have hA2 : 2 * 2 ^ a / 2 ^ (b + 1) = 2 ^ (a - b) := by
      rw [hpow1, Nat.pow_div (by omega) (by norm_num)]
      congr 1
      omega
    have hA2r : (2 * 2 ^ a / 2 ^ (b + 1)) * 2 ^ b = 2 ^ a := by
      rw [hA2, ← pow_add]
      congr 1
      omega
    have hA2' : 2 * 2 ^ a / (2 ^ b + 2 ^ b) = 2 * 2 ^ a / 2 ^ (b + 1) := by
      rw [show (2 : ℕ) ^ (b + 1) = 2 ^ b + 2 ^ b by rw [pow_succ, mul_two]]
    have hA2r' : (2 * 2 ^ a / (2 ^ b + 2 ^ b)) * 2 ^ b = 2 ^ a := by
      rw [hA2']; exact hA2r
    have hA21 : (2 * 2 ^ a / 2 ^ (b + 1)) * 2 = 2 * 2 ^ a / 2 ^ b := by
      rw [hA2, hpow1, Nat.pow_div (by omega) (by norm_num), ← pow_succ]
      congr 1
      omega
    -- the sum splits into two equal halves
    have hsplit : (∑ q : Fin (2 ^ (b + 1)),
          HvdH.yMul (2 ^ a) (c * (((2 * 2 ^ a / 2 ^ (b + 1)) * (q : ℕ) : ℕ) : ℤ)) W)
        = (∑ x ∈ Finset.range (2 ^ b),
              HvdH.yMul (2 ^ a) (c * (((2 * 2 ^ a / 2 ^ (b + 1)) * x : ℕ) : ℤ)) W)
          + HvdH.yMul (2 ^ a) (c * ((2 ^ a : ℕ) : ℤ))
              (∑ x ∈ Finset.range (2 ^ b),
                HvdH.yMul (2 ^ a) (c * (((2 * 2 ^ a / 2 ^ (b + 1)) * x : ℕ) : ℤ)) W) := by
      rw [Fin.sum_univ_eq_sum_range
        (fun x => HvdH.yMul (2 ^ a) (c * (((2 * 2 ^ a / 2 ^ (b + 1)) * x : ℕ) : ℤ)) W)
        (2 ^ (b + 1))]
      rw [show (2 : ℕ) ^ (b + 1) = 2 ^ b + 2 ^ b by rw [pow_succ, mul_two]]
      rw [Finset.sum_range_add]
      rw [show (∑ x ∈ Finset.range (2 ^ b),
            HvdH.yMul (2 ^ a) (c * (((2 * 2 ^ a / (2 ^ b + 2 ^ b)) * (2 ^ b + x) : ℕ) : ℤ)) W)
          = HvdH.yMul (2 ^ a) (c * ((2 ^ a : ℕ) : ℤ))
              (∑ x ∈ Finset.range (2 ^ b),
                HvdH.yMul (2 ^ a) (c * (((2 * 2 ^ a / (2 ^ b + 2 ^ b)) * x : ℕ) : ℤ)) W) from by
        rw [hlin (c * ((2 ^ a : ℕ) : ℤ)) (Finset.range (2 ^ b))
              (fun x => HvdH.yMul (2 ^ a) (c * (((2 * 2 ^ a / (2 ^ b + 2 ^ b)) * x : ℕ) : ℤ)) W)]
        refine Finset.sum_congr rfl (fun x _ => ?_)
        show HvdH.yMul (2 ^ a) (c * (((2 * 2 ^ a / (2 ^ b + 2 ^ b)) * (2 ^ b + x) : ℕ) : ℤ)) W
            = HvdH.yMul (2 ^ a) (c * ((2 ^ a : ℕ) : ℤ))
                (HvdH.yMul (2 ^ a) (c * (((2 * 2 ^ a / (2 ^ b + 2 ^ b)) * x : ℕ) : ℤ)) W)
        rw [Nat.mul_add, hA2r', Nat.cast_add, Int.mul_add]
        exact yMExpAdd (2 ^ a) hr (c * ((2 ^ a : ℕ) : ℤ))
          (c * (((2 * 2 ^ a / (2 ^ b + 2 ^ b)) * x : ℕ) : ℤ)) W]
    rw [hsplit]
    rcases Int.even_or_odd c with hc | hc
    · -- `c = 2 c'`: both halves agree, and the sum is twice that of level `b` with `c'`
      obtain ⟨c', hc'⟩ := hc
      have hc2 : c = 2 * c' := by rw [hc']; ring
      have hhalf : (∑ x ∈ Finset.range (2 ^ b),
              HvdH.yMul (2 ^ a) (c * (((2 * 2 ^ a / 2 ^ (b + 1)) * x : ℕ) : ℤ)) W)
            = (∑ q : Fin (2 ^ b),
              HvdH.yMul (2 ^ a) (c' * (((2 * 2 ^ a / 2 ^ b) * (q : ℕ) : ℕ) : ℤ)) W) := by
        rw [Fin.sum_univ_eq_sum_range
          (fun x => HvdH.yMul (2 ^ a) (c' * (((2 * 2 ^ a / 2 ^ b) * x : ℕ) : ℤ)) W) (2 ^ b)]
        refine Finset.sum_congr rfl (fun x _ => ?_)
        have hnat : 2 * ((2 * 2 ^ a / 2 ^ (b + 1)) * x) = (2 * 2 ^ a / 2 ^ b) * x := by
          rw [← hA21]; ring
        have hz : c * (((2 * 2 ^ a / 2 ^ (b + 1)) * x : ℕ) : ℤ)
            = c' * (((2 * 2 ^ a / 2 ^ b) * x : ℕ) : ℤ) := by
          rw [hc2, ← hnat]
          push_cast
          ring
        rw [hz]
      have heven : ∀ A : Fin (2 ^ a) → ℂ, HvdH.yMul (2 ^ a) (c * ((2 ^ a : ℕ) : ℤ)) A = A := by
        intro A
        rw [show c * ((2 ^ a : ℕ) : ℤ) = 2 * (2 ^ a : ℤ) * c' by rw [hc2]; push_cast; ring]
        exact yMul_twoR_mul (2 ^ a) hr c' A
      rw [heven, hhalf, ih (by omega) c']
      have hdiv : (((2 ^ (b + 1) : ℕ)) : ℤ) ∣ c ↔ (((2 ^ b : ℕ)) : ℤ) ∣ c' := by
        rw [hc2]
        have hcast : (((2 ^ (b + 1) : ℕ)) : ℤ) = 2 * (((2 ^ b : ℕ)) : ℤ) := by
          push_cast
          rw [pow_succ]
          ring
        rw [hcast]
        exact Int.mul_dvd_mul_iff_left (by norm_num : (2 : ℤ) ≠ 0)
      by_cases hcc : (((2 ^ b : ℕ)) : ℤ) ∣ c'
      · rw [if_pos (hdiv.mpr hcc), if_pos hcc, ← two_smul ℂ ((((2 ^ b : ℕ)) : ℂ) • W),
          smul_smul]
        congr 1
        push_cast
        rw [pow_succ]
        ring
      · rw [if_neg (fun h => hcc (hdiv.mp h)), if_neg hcc]
        simp
    · -- `c` odd: the two halves cancel
      obtain ⟨k, hk⟩ := hc
      have he : ∀ A : Fin (2 ^ a) → ℂ, HvdH.yMul (2 ^ a) (c * ((2 ^ a : ℕ) : ℤ)) A = -A := by
        intro A
        have h : c * ((2 ^ a : ℕ) : ℤ) = (2 ^ a : ℤ) * c := by push_cast; ring
        rw [h]
        exact yMul_odd_mul_r (2 ^ a) hr c ⟨k, hk⟩ A
      rw [he, add_neg_cancel]
      have hnd : ¬ (((2 ^ (b + 1) : ℕ)) : ℤ) ∣ c := by
        intro hd
        have h2d : (2 : ℤ) ∣ (((2 ^ (b + 1) : ℕ)) : ℤ) :=
          ⟨(((2 ^ b : ℕ)) : ℤ), by push_cast; rw [pow_succ]; ring⟩
        obtain ⟨j, hj⟩ := dvd_trans h2d hd
        omega
      rw [if_neg hnd]

/-- The one-dimensional orthogonality relation for the synthetic character. -/
private lemma yCharSum1_aux (r t : ℕ) (hr : HvdH.IsPow2 r) (ht : t ∣ 2 * r) (c : ℤ)
    (W : Fin r → ℂ) :
    (∑ q : Fin t, HvdH.yMul r (c * (((2 * r / t) * q : ℕ) : ℤ)) W)
      = if (t : ℤ) ∣ c then (t : ℂ) • W else 0 := by
  obtain ⟨a, _ha, rfl⟩ := hr
  have ht' : t ∣ 2 ^ (a + 1) := by
    have h : (2 : ℕ) ^ (a + 1) = 2 * 2 ^ a := by rw [pow_succ]; ring
    rw [h]
    exact ht
  obtain ⟨b, hb, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp ht'
  exact yCharSum_pow2 a W b hb c

/-- `HvdH.IsPow2 r` implies `r > 0`. -/
private lemma isPow2_pos {r : ℕ} (hr : HvdH.IsPow2 r) : 0 < r := by
  obtain ⟨k, _hk, rfl⟩ := hr
  exact pow_pos (by norm_num) k

/-! ## The multidimensional character sum

The multidimensional sum factors dimension by dimension exactly as in
`Work.DFT.charSumGen`: peeling off the first coordinate via the mixed-radix reindexing
`Work.DFT.sumFinMul`, the exponent splits with `Work.SynFFT.yMulExpAdd`, the inner sum is
handled by the induction hypothesis and the outer one by `yCharSum1_aux`. -/

/-- `Work.DFT.sumFinMul` with values in an arbitrary additive commutative monoid
(we need it for `Fin r → ℂ`-valued sums). -/
private lemma sumFinMulVec {M : Type*} [AddCommMonoid M] (m n : ℕ) (f : ℕ → M) :
    (∑ k : Fin (m * n), f k) = ∑ q : Fin m, ∑ r : Fin n, f (r + n * q) := by
  rw [← Equiv.sum_comp (finProdFinEquiv (m := m) (n := n)) (fun k : Fin (m * n) => f k)]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl; intro x _
  apply Finset.sum_congr rfl; intro y _
  congr 1

private lemma ySynCharSum (r : ℕ) (hr : HvdH.IsPow2 r) :
    ∀ (ts : List ℕ), (∀ t ∈ ts, 0 < t) → (∀ t ∈ ts, t ∣ 2 * r) →
      ∀ (c : List ℤ) (W : Fin r → ℂ), c.length = ts.length →
        (∑ k : Fin ts.prod, HvdH.yMul r (synExpZ r ts c (HvdH.digits ts k)) W)
          = if (∀ i < ts.length, ((ts.getD i 0 : ℤ)) ∣ c.getD i 0)
              then (ts.prod : ℂ) • W else 0 := by
  have hr0 : 0 < r := isPow2_pos hr
  intro ts
  induction ts with
  | nil =>
    intro hpos hdiv c W hc
    have hc0 : c = [] := List.eq_nil_of_length_eq_zero (by simpa using hc)
    subst hc0
    have hvac : (∀ i < ([] : List ℕ).length, ((([] : List ℕ).getD i 0 : ℤ)) ∣ ([].getD i 0)) := by
      intro i hi
      simp at hi
    rw [if_pos hvac]
    have hprod : ([] : List ℕ).prod = 1 := List.prod_nil
    rw [hprod, Fin.sum_univ_one]
    have hd : ∀ n : ℕ, HvdH.digits ([] : List ℕ) n = [] := fun n => rfl
    rw [hd, synExpZ_nil, yMZero r hr0 W]
    simp
  | cons t ts' ih =>
    intro hpos hdiv c W hc
    have ht : 0 < t := hpos t (by simp)
    have hpos' : ∀ x ∈ ts', 0 < x := fun x hx => hpos x (by simp [hx])
    have hdiv' : ∀ x ∈ ts', x ∣ 2 * r := fun x hx => hdiv x (by simp [hx])
    have hdt : t ∣ 2 * r := hdiv t (by simp)
    have hP : 0 < ts'.prod := List.prod_pos hpos'
    cases c with
    | nil => simp at hc
    | cons c0 cs =>
      have hcs : cs.length = ts'.length := by simpa using hc
      have hlin : ∀ (e : ℤ) (s : Finset (Fin ts'.prod)) (f : Fin ts'.prod → Fin r → ℂ),
          HvdH.yMul r e (∑ i ∈ s, f i) = ∑ i ∈ s, HvdH.yMul r e (f i) :=
        (Work.SynFFT.yMulLinear (ι := Fin ts'.prod) r).2
      have hslm : ∀ (e : ℤ) (cc : ℂ) (A : Fin r → ℂ),
          HvdH.yMul r e (cc • A) = cc • HvdH.yMul r e A :=
        (Work.SynFFT.yMulLinear (ι := ℕ) r).1
      have hzero : ∀ e : ℤ, HvdH.yMul r e (0 : Fin r → ℂ) = 0 := by
        intro e
        have h := hslm e 0 (0 : Fin r → ℂ)
        simpa using h
      have step1 : (∑ k : Fin (t :: ts').prod,
            HvdH.yMul r (synExpZ r (t :: ts') (c0 :: cs) (HvdH.digits (t :: ts') k)) W)
          = ∑ q : Fin t, ∑ rr : Fin ts'.prod,
              HvdH.yMul r (c0 * (((2 * r / t) * (q : ℕ) : ℕ) : ℤ))
                (HvdH.yMul r (synExpZ r ts' cs (HvdH.digits ts' (rr : ℕ))) W) := by
        rw [show (t :: ts').prod = t * ts'.prod from List.prod_cons]
        rw [sumFinMulVec t ts'.prod
          (fun k => HvdH.yMul r (synExpZ r (t :: ts') (c0 :: cs) (HvdH.digits (t :: ts') k)) W)]
        refine Finset.sum_congr rfl (fun q _ => Finset.sum_congr rfl (fun rr _ => ?_))
        rw [Work.DFT.digits_cons_prod t ts' hP (q : ℕ) (rr : ℕ) q.isLt rr.isLt, synExpZ_cons]
        exact yMExpAdd r hr0 _ _ W
      have step2 : (∑ q : Fin t, ∑ rr : Fin ts'.prod,
              HvdH.yMul r (c0 * (((2 * r / t) * (q : ℕ) : ℕ) : ℤ))
                (HvdH.yMul r (synExpZ r ts' cs (HvdH.digits ts' (rr : ℕ))) W))
          = ∑ q : Fin t, HvdH.yMul r (c0 * (((2 * r / t) * (q : ℕ) : ℕ) : ℤ))
              (∑ rr : Fin ts'.prod,
                HvdH.yMul r (synExpZ r ts' cs (HvdH.digits ts' (rr : ℕ))) W) := by
        refine Finset.sum_congr rfl (fun q _ => ?_)
        rw [← hlin (c0 * (((2 * r / t) * (q : ℕ) : ℕ) : ℤ)) Finset.univ
              (fun rr => HvdH.yMul r (synExpZ r ts' cs (HvdH.digits ts' (rr : ℕ))) W)]
      have hinner : (∑ rr : Fin ts'.prod,
            HvdH.yMul r (synExpZ r ts' cs (HvdH.digits ts' (rr : ℕ))) W)
          = if (∀ i < ts'.length, ((ts'.getD i 0 : ℤ)) ∣ cs.getD i 0)
              then (ts'.prod : ℂ) • W else 0 :=
        ih hpos' hdiv' cs W hcs
      rw [step1, step2, hinner]
      have hcond := Work.DFT.getDDvdCons t ts' c0 cs
      by_cases hcc : ∀ i < ts'.length, ((ts'.getD i 0 : ℤ)) ∣ cs.getD i 0
      · rw [if_pos hcc]
        have h1 : (∑ q : Fin t,
              HvdH.yMul r (c0 * (((2 * r / t) * (q : ℕ) : ℕ) : ℤ)) ((ts'.prod : ℂ) • W))
            = (ts'.prod : ℂ) • (∑ q : Fin t,
              HvdH.yMul r (c0 * (((2 * r / t) * (q : ℕ) : ℕ) : ℤ)) W) := by
          rw [Finset.smul_sum]
          exact Finset.sum_congr rfl (fun q _ => hslm _ _ _)
        rw [h1, yCharSum1_aux r t hr hdt c0 W]
        by_cases hcd : (t : ℤ) ∣ c0
        · rw [if_pos hcd, if_pos (hcond.mpr ⟨hcd, hcc⟩), smul_smul]
          congr 1
          rw [List.prod_cons]
          push_cast
          ring
        · rw [if_neg hcd, smul_zero, if_neg (fun h => hcd (hcond.mp h).1)]
      · rw [if_neg hcc]
        have h1 : (∑ q : Fin t,
              HvdH.yMul r (c0 * (((2 * r / t) * (q : ℕ) : ℕ) : ℤ)) (0 : Fin r → ℂ)) = 0 := by
          rw [Finset.sum_congr rfl (fun q _ => hzero _), Finset.sum_const, Finset.card_univ,
            Fintype.card_fin, smul_zero]
        rw [h1, if_neg (fun h => hcc (hcond.mp h).2)]

theorem yCharSumConv (r : ℕ) (ts : List ℕ) (hr : HvdH.IsPow2 r) (hpos : ∀ t ∈ ts, 0 < t)
    (ht : ∀ t ∈ ts, t ∣ 2 * r) (j a b : Fin ts.prod) (W : Fin r → ℂ) :
    (∑ k : Fin ts.prod, HvdH.yMul r (HvdH.synExp r ts (HvdH.digits ts j) (HvdH.digits ts k) -
        HvdH.synExp r ts (HvdH.digits ts a) (HvdH.digits ts k) -
        HvdH.synExp r ts (HvdH.digits ts b) (HvdH.digits ts k)) W) =
      if b = HvdH.subIdx ts j a then (ts.prod : ℂ) • W else 0 := by
  set cg := Work.DFT.subNZ (Work.DFT.subN (HvdH.digits ts (j : ℕ)) (HvdH.digits ts (a : ℕ)))
    (HvdH.digits ts (b : ℕ)) with hcg
  have hcglen : cg.length = ts.length := by
    rw [hcg]
    simp [Work.DFT.subNZ, Work.DFT.subN, Work.DFT.digits_length]
  have hexp : ∀ k : Fin ts.prod,
      HvdH.synExp r ts (HvdH.digits ts (j : ℕ)) (HvdH.digits ts (k : ℕ)) -
        HvdH.synExp r ts (HvdH.digits ts (a : ℕ)) (HvdH.digits ts (k : ℕ)) -
        HvdH.synExp r ts (HvdH.digits ts (b : ℕ)) (HvdH.digits ts (k : ℕ))
      = synExpZ r ts cg (HvdH.digits ts (k : ℕ)) := fun k => by
    rw [hcg]
    exact synExp_sub3 r ts (HvdH.digits ts (j : ℕ)) (HvdH.digits ts (a : ℕ))
      (HvdH.digits ts (b : ℕ)) (HvdH.digits ts (k : ℕ)) (Work.DFT.digits_length ts _)
      (Work.DFT.digits_length ts _) (Work.DFT.digits_length ts _) (Work.DFT.digits_length ts _)
  rw [Finset.sum_congr rfl (fun k _ => by rw [hexp k])]
  rw [ySynCharSum r hr ts hpos ht cg W hcglen]
  have hcond := Work.DFT.charSumConv_cond_iff_subIdx ts hpos j a b
  rw [← hcg] at hcond
  rw [if_congr hcond rfl rfl]

end Work.ConvR
