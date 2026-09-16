import Mathlib
import Submission.CertGroups
import Submission.CertArith
import Submission.CertRow
import Submission.Commons.Data.Nat.packed_mul3_block_le
import Submission.Commons.Data.Nat.list_zipIdx_sum_eq_range
import Submission.Commons.Data.Int.mul_eq_pos_neg_parts
import Submission.Commons.Data.Nat.sum_sum_mul_kernel

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2000000

open scoped BigOperators
open Finset

/-!
# The packed evaluation of the certificate's quadratic forms

This module computes the two integer double sums `certISum` and `certJSum` of
`Submission/CertArith.lean` by a base-`2^2048` *packed* convolution: the coefficient vector of a
signature group is packed into a single natural number, and the Hankel contraction with the
kernel `K(A,R) = 26^{50+A+R}(100!/(A+R+50)!)A!25^{50-A-R}` is read off as one block of a product
of three packed words.

The key identity (for the `I`-side) is

  `∑_{a,a'} v(a) v'(a') K(a+a', R) = blk(P v, P v') - blk(P v, N v') - blk(N v, P v') + blk(N v, N v')`

with `blk X Y = ((X*Y*Kwz R) / B^{50}) % B` and `Kwz R = ∑_{k<51} K(50-k,R) · B^k`.
-/

namespace Commons.NumberTheory.MaynardSieve

/-- The packing base of the `I`-side.  Large enough that the triple convolution coefficients
of the certificate's coefficient vectors and the kernel are `< BP`. -/
def BP : ℕ := 2 ^ 2048

/-- The positive part of an integer, as a natural number. -/
def ipos (z : ℤ) : ℕ := (max z 0).toNat

/-- The negative part of an integer, as a natural number. -/
def ineg (z : ℤ) : ℕ := (max (-z) 0).toNat

/-- Positive-part vector of a coefficient list. -/
def vpos (v : List ℤ) : List ℕ := v.map ipos

/-- Negative-part vector of a coefficient list. -/
def vneg (v : List ℤ) : List ℕ := v.map ineg

/-- The packed word of a nonnegative digit list: `∑_i u_i · BP^i`. -/
def pw (u : List ℕ) : ℕ := (u.zipIdx.map (fun p => p.1 * BP ^ p.2)).sum

/-- The cleared `I`-kernel, indexed by `A = a+a'` and `R = |α|+|α'|`:
`26^{50+A+R}·(100!/(A+R+50)!)·A!·25^{50-A-R}`. -/
def Km (A R : ℕ) : ℕ :=
  26 ^ (50 + (A + R)) * ((100).factorial / ((A + R) + 50).factorial) * A.factorial
    * 25 ^ (50 - (A + R))

/-- The packed kernel word, in the orientation of the extraction lemma:
`∑_{k<51} Km (50-k) R · BP^k`. -/
def Kwz (R : ℕ) : ℕ := ∑ k ∈ Finset.range 51, Km (50 - k) R * BP ^ k

/-- The packed block extraction: the `50`-th base-`BP` "digit" of `X*Y*Kwz R`. -/
def blk (X Y R : ℕ) : ℕ := ((X * Y * Kwz R) / BP ^ 50) % BP

section Reindex

open Commons.Data.Nat

/-- The `(signature, a-exponent, coefficient)` triples of the certificate basis. -/
def cTrip (j : Fin 1780) : List ℕ × ℕ × ℤ := (certSig j, certA j, certCs j)

/-- The `(signature, a-exponent, coefficient)` list of the certificate basis. -/
def cTrips : List (List ℕ × ℕ × ℤ) :=
  (certBasis.zip certCoefSym).map (fun p => (p.1.2, p.1.1, p.2))

/-- The signature-grouped data list. -/
def cSigs : List (List ℕ × List ℤ) := certGroupSigs.zip certGroupCoefs

/-- The triples of one signature group. -/
def gTrips (p : List ℕ × List ℤ) : List (List ℕ × ℕ × ℤ) :=
  p.2.zipIdx.map (fun q => (p.1, q.2, q.1))

/-- The certificate's `I`-kernel on triples. -/
def Gc (u u' : List ℕ × ℕ × ℤ) : ℤ :=
  u.2.2 * u'.2.2 * (Km (u.2.1 + u'.2.1) (u.1.sum + u'.1.sum) : ℤ) * (Ssum u.1 u'.1 50 : ℤ)

theorem cSigs_flat : cSigs.flatMap gTrips = cTrips := certGroups_flat

theorem certIKern_eq_Km (j j' : Fin 1780) :
    certIKern j j' = (Km (certAA j j') ((certSig j).sum + (certSig j').sum) : ℤ) := by
  have hD : certD j j' = (certA j + certA j') + ((certSig j).sum + (certSig j').sum) := by
    rw [certD]; omega
  have hAA : certAA j j' = certA j + certA j' := rfl
  unfold certIKern
  rw [hD, hAA]
  simp only [Km, certIFall]
  push_cast
  ring

theorem ofFn_cTrip : List.ofFn cTrip = cTrips := by
  apply List.ext_getElem
  · simp only [List.length_ofFn, cTrips, List.length_map, List.length_zip, certBasis_length,
      certCoefSym_length, Nat.min_self]
  · intro i h1 h2
    simp only [List.getElem_ofFn, cTrips, cTrip, List.getElem_map, List.getElem_zip,
      certSig_eq_getElem, certA, certBasisAt, certCs_eq_getElem, List.get_eq_getElem]

theorem sum_flatMap_map {M : Type*} [AddCommMonoid M] {α β : Type*} (l : List α)
    (f : α → List β) (g : β → M) :
    ((l.flatMap f).map g).sum = (l.map (fun x => ((f x).map g).sum)).sum := by
  induction l with
  | nil => simp
  | cons a t ih => simp [List.flatMap_cons, List.map_append, List.sum_append, ih, List.sum_cons]

theorem sum_ofFn_ofFn {M : Type*} [AddCommMonoid M] {n : ℕ} (g : Fin n → Fin n → M) :
    (∑ j : Fin n, ∑ j' : Fin n, g j j')
      = ((List.ofFn (fun j : Fin n => (List.ofFn (fun j' : Fin n => g j j')).sum)).sum) := by
  rw [List.sum_ofFn]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  exact (List.sum_ofFn).symm

theorem ofFn_pair_list {M : Type*} [AddCommMonoid M] {α : Type*} {n : ℕ} (T : Fin n → α)
    (G : α → α → M) :
    (List.ofFn (fun j : Fin n => (List.ofFn (fun j' : Fin n => G (T j) (T j'))).sum))
      = (List.ofFn T).map (fun u => ((List.ofFn T).map (fun u' => G u u')).sum) := by
  rw [List.map_ofFn]
  congr 1
  funext u
  simp only [Function.comp_apply]
  rw [List.map_ofFn]
  rfl

theorem ofFn_pair {M : Type*} [AddCommMonoid M] {α : Type*} {n : ℕ} (T : Fin n → α)
    (G : α → α → M) :
    (List.ofFn (fun j : Fin n => (List.ofFn (fun j' : Fin n => G (T j) (T j'))).sum)).sum
      = ((List.ofFn T).map (fun u => ((List.ofFn T).map (fun u' => G u u')).sum)).sum := by
  rw [ofFn_pair_list]

theorem list_sum_comm {M : Type*} [AddCommMonoid M] {α β : Type*} (l₁ : List α)
    (l₂ : List β) (F : α → β → M) :
    (l₁.map (fun a => (l₂.map (fun b => F a b)).sum)).sum
      = (l₂.map (fun b => (l₁.map (fun a => F a b)).sum)).sum := by
  induction l₁ with
  | nil => simp
  | cons a t ih =>
      simp only [List.map_cons, List.sum_cons, ih, List.sum_map_add]

theorem certISum_step1 :
    certISum = ((cTrips.map (fun u => (cTrips.map (fun u' => Gc u u')).sum)).sum) := by
  have h1 : certISum = ∑ j : Fin 1780, ∑ j' : Fin 1780, Gc (cTrip j) (cTrip j') := by
    unfold certISum
    refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun j' _ => ?_))
    rw [certIKern_eq_Km]
    rfl
  rw [h1, sum_ofFn_ofFn, ofFn_pair, ofFn_cTrip]

theorem certISum_step2 :
    ((cTrips.map (fun u => (cTrips.map (fun u' => Gc u u')).sum)).sum)
      = ((cSigs.map (fun p => ((gTrips p).map (fun u => (cSigs.map (fun p' =>
          ((gTrips p').map (fun u' => Gc u u')).sum)).sum)).sum)).sum) := by
  have hinner : ∀ u : List ℕ × ℕ × ℤ,
      (cTrips.map (fun u' => Gc u u')).sum
        = (cSigs.map (fun p' => ((gTrips p').map (fun u' => Gc u u')).sum)).sum := by
    intro u
    rw [← cSigs_flat, sum_flatMap_map]
  have h1 : (cTrips.map (fun u => (cTrips.map (fun u' => Gc u u')).sum))
      = (cTrips.map (fun u => (cSigs.map (fun p' =>
          ((gTrips p').map (fun u' => Gc u u')).sum)).sum)) :=
    List.map_congr_left (fun u _ => hinner u)
  rw [h1, ← cSigs_flat, sum_flatMap_map]

theorem certISum_step3 :
    ((cSigs.map (fun p => ((gTrips p).map (fun u => (cSigs.map (fun p' =>
        ((gTrips p').map (fun u' => Gc u u')).sum)).sum)).sum)).sum)
      = ((cSigs.map (fun p => (cSigs.map (fun p' => ((gTrips p).map (fun u =>
          ((gTrips p').map (fun u' => Gc u u')).sum)).sum)).sum)).sum) := by
  exact congrArg List.sum (List.map_congr_left (fun p _ =>
    list_sum_comm (gTrips p) cSigs (fun u p' => ((gTrips p').map (fun u' => Gc u u')).sum)))

/-- The `a`-contraction of a signature group pair. -/
def Hc (p p' : List ℕ × List ℤ) : ℤ :=
  ((gTrips p).map (fun u => ((gTrips p').map (fun u' =>
    u.2.2 * u'.2.2 * (Km (u.2.1 + u'.2.1) (p.1.sum + p'.1.sum) : ℤ))).sum)).sum

theorem certISum_step4 (p p' : List ℕ × List ℤ) :
    ((gTrips p).map (fun u => ((gTrips p').map (fun u' => Gc u u')).sum)).sum
      = Hc p p' * (Ssum p.1 p'.1 50 : ℤ) := by
  unfold Hc
  have innerStep : ∀ u ∈ gTrips p,
      ((gTrips p').map (fun u' => Gc u u')).sum
        = ((gTrips p').map (fun u' => u.2.2 * u'.2.2 *
            (Km (u.2.1 + u'.2.1) (p.1.sum + p'.1.sum) : ℤ))).sum
            * (Ssum p.1 p'.1 50 : ℤ) := by
    intro u hu
    obtain ⟨q, r, hq, hqe⟩ := by simpa [gTrips] using hu
    rw [← hqe]
    simp only [Prod.mk.eta]
    have hpoint : ∀ u' ∈ gTrips p',
        Gc (p.1, r, q) u' = (q : ℤ) * u'.2.2 *
          (Km (r + u'.2.1) (p.1.sum + p'.1.sum) : ℤ) * (Ssum p.1 p'.1 50 : ℤ) := by
      intro u' hu'
      obtain ⟨q', r', hq', hqe'⟩ := by simpa [gTrips] using hu'
      rw [← hqe']
      simp only [Prod.mk.eta]
      rfl
    rw [congrArg List.sum (List.map_congr_left hpoint), List.sum_map_mul_right]
  have houter : (gTrips p).map (fun u => ((gTrips p').map (fun u' => Gc u u')).sum)
      = (gTrips p).map (fun u => ((gTrips p').map (fun u' => u.2.2 * u'.2.2 *
            (Km (u.2.1 + u'.2.1) (p.1.sum + p'.1.sum) : ℤ))).sum
            * (Ssum p.1 p'.1 50 : ℤ)) :=
    List.map_congr_left innerStep
  rw [houter, List.sum_map_mul_right]

/-- **The reindexing of `certISum` into the signature-grouped double sum.** -/
theorem certISum_reindex :
    certISum = ((cSigs.map (fun p => (cSigs.map (fun p' =>
        Hc p p' * (Ssum p.1 p'.1 50 : ℤ))).sum)).sum) := by
  rw [certISum_step1, certISum_step2, certISum_step3]
  refine congrArg List.sum (List.map_congr_left (fun p _ => ?_))
  refine congrArg List.sum (List.map_congr_left (fun p' _ => ?_))
  exact certISum_step4 p p'

/-- The mathematical `a`-contraction of two coefficient vectors against the kernel. -/
def contMath (v v' : List ℤ) (R : ℕ) : ℤ :=
  ∑ a ∈ Finset.range v.length, ∑ b ∈ Finset.range v'.length,
    v.getD a 0 * v'.getD b 0 * (Km (a + b) R : ℤ)

theorem zipIdx_sum_map_aux {M : Type*} [AddCommMonoid M] {α : Type*} (l : List α)
    (g : α × ℕ → M) (d : α) (k : ℕ) :
    ((l.zipIdx k).map g).sum = ∑ i ∈ Finset.range l.length, g (l.getD i d, k + i) := by
  induction l generalizing k with
  | nil => simp
  | cons a t ih =>
      rw [List.zipIdx_cons, List.map_cons, List.sum_cons, List.length_cons, ih (k + 1)]
      rw [Finset.sum_range_succ']
      simp only [List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero]
      rw [show (∑ i ∈ Finset.range t.length, g (t.getD i d, k + 1 + i))
          = ∑ i ∈ Finset.range t.length, g (t.getD i d, k + (i + 1)) from by
        refine Finset.sum_congr rfl (fun i _ => by rw [show k + 1 + i = k + (i + 1) from by omega])]
      rw [add_comm (g (a, k))]

theorem zipIdx_sum_map {M : Type*} [AddCommMonoid M] {α : Type*} (l : List α)
    (g : α × ℕ → M) (d : α) :
    (l.zipIdx.map g).sum = ∑ i ∈ Finset.range l.length, g (l.getD i d, i) := by
  simpa using zipIdx_sum_map_aux l g d 0

theorem map_gTrips {M : Type*} (p : List ℕ × List ℤ) (f : List ℕ × ℕ × ℤ → M) :
    (gTrips p).map f = p.2.zipIdx.map (fun q => f (p.1, q.2, q.1)) := by
  rw [gTrips, List.map_map]
  rfl

theorem Hc_eq_contMath (p p' : List ℕ × List ℤ) :
    Hc p p' = contMath p.2 p'.2 (p.1.sum + p'.1.sum) := by
  unfold Hc contMath
  have step : ∀ u ∈ gTrips p,
      ((gTrips p').map (fun u' => u.2.2 * u'.2.2 *
          (Km (u.2.1 + u'.2.1) (p.1.sum + p'.1.sum) : ℤ))).sum
        = ∑ b ∈ Finset.range p'.2.length,
            u.2.2 * p'.2.getD b 0 * (Km (u.2.1 + b) (p.1.sum + p'.1.sum) : ℤ) := by
    intro u hu
    rw [map_gTrips]
    rw [show (fun q : ℤ × ℕ => u.2.2 * (p'.1, q.2, q.1).2.2 *
          (Km (u.2.1 + (p'.1, q.2, q.1).2.1) (p.1.sum + p'.1.sum) : ℤ))
        = (fun q : ℤ × ℕ => u.2.2 * q.1 * (Km (u.2.1 + q.2) (p.1.sum + p'.1.sum) : ℤ))
        from rfl]
    rw [zipIdx_sum_map p'.2 _ 0]
  have houter : (gTrips p).map (fun u => ((gTrips p').map (fun u' => u.2.2 * u'.2.2 *
        (Km (u.2.1 + u'.2.1) (p.1.sum + p'.1.sum) : ℤ))).sum)
      = (gTrips p).map (fun u => ∑ b ∈ Finset.range p'.2.length,
            u.2.2 * p'.2.getD b 0 * (Km (u.2.1 + b) (p.1.sum + p'.1.sum) : ℤ)) :=
    List.map_congr_left step
  rw [houter, map_gTrips]
  rw [show (fun q : ℤ × ℕ => ∑ b ∈ Finset.range p'.2.length,
        (p.1, q.2, q.1).2.2 * p'.2.getD b 0 *
          (Km ((p.1, q.2, q.1).2.1 + b) (p.1.sum + p'.1.sum) : ℤ))
      = (fun q : ℤ × ℕ => ∑ b ∈ Finset.range p'.2.length,
        q.1 * p'.2.getD b 0 * (Km (q.2 + b) (p.1.sum + p'.1.sum) : ℤ)) from rfl]
  rw [zipIdx_sum_map p.2 _ 0]

end Reindex

section Packed

open Commons.Data.Nat

theorem Km_eq_zero_of_gt (A R : ℕ) (h : 50 < A + R) : Km A R = 0 := by
  unfold Km
  have hlt : (100).factorial < ((A + R) + 50).factorial :=
    (Nat.factorial_lt (by norm_num : 0 < (100 : ℕ))).mpr (by omega)
  rw [Nat.div_eq_of_lt hlt]
  ring

theorem pw_eq (u : List ℕ) (h : u.length ≤ 26) :
    pw u = ∑ i ∈ Finset.range 26, u.getD i 0 * BP ^ i := by
  rw [pw, Commons.Data.Nat.list_zipIdx_sum_eq_range]
  refine Finset.sum_subset (fun x hx => by rw [Finset.mem_range] at hx ⊢; omega)
    (fun x hx hxn => ?_)
  rw [Finset.mem_range] at hxn
  rw [List.getD_eq_default _ _ (by omega), zero_mul]

theorem blk_eq (x y : ℕ → ℕ) (R : ℕ)
    (hxy : (∑ i ∈ Finset.range 26, x i) * (∑ j ∈ Finset.range 26, y j) < BP)
    (hxyz : (∑ i ∈ Finset.range 26, x i) * (∑ j ∈ Finset.range 26, y j)
              * (∑ k ∈ Finset.range 51, Km (50 - k) R) < BP) :
    blk (∑ i ∈ Finset.range 26, x i * BP ^ i) (∑ j ∈ Finset.range 26, y j * BP ^ j) R
      = ∑ i ∈ Finset.range 26, ∑ j ∈ Finset.range 26,
          x i * y j * Km (i + j) R := by
  rw [blk, Kwz]
  rw [Commons.Data.Nat.packed_mul3_block_le (B := BP) (n := 26) (m := 26) (l := 51)
    (x := x) (y := y) (z := fun k => Km (50 - k) R) (by norm_num [BP]) hxy hxyz 50]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  by_cases hij : i + j ≤ 50
  · rw [Finset.sum_eq_single (50 - (i + j))]
    · rw [if_pos (by omega), Nat.sub_sub_self hij]
    · intro k hk hne
      rw [if_neg (by omega)]
    · intro hmem
      exact absurd (Finset.mem_range.mpr (by omega)) hmem
  · have h50 : 50 < i + j := not_le.mp hij
    rw [Finset.sum_eq_zero (fun k hk => by
      rw [Finset.mem_range] at hk
      rw [if_neg (by omega)]), Km_eq_zero_of_gt (i + j) R (by omega), mul_zero]

/-- A crude uniform bound for the `I`-kernel on the relevant range. -/
def Kbound : ℕ := 26 ^ 100 * (100).factorial * (50).factorial * 25 ^ 50

theorem Km_le_Kbound (A R : ℕ) (h : A + R ≤ 50) : Km A R ≤ Kbound := by
  unfold Km Kbound
  have h1 : 26 ^ (50 + (A + R)) ≤ 26 ^ 100 := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2 : (100).factorial / ((A + R) + 50).factorial ≤ (100).factorial := Nat.div_le_self _ _
  have h3 : A.factorial ≤ (50).factorial := Nat.factorial_le (by omega)
  have h4 : 25 ^ (50 - (A + R)) ≤ 25 ^ 50 := Nat.pow_le_pow_right (by norm_num) (by omega)
  calc 26 ^ (50 + (A + R)) * ((100).factorial / ((A + R) + 50).factorial) * A.factorial
        * 25 ^ (50 - (A + R))
      ≤ 26 ^ 100 * (100).factorial * (50).factorial * 25 ^ 50 := by
        exact Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul h1 h2) h3) h4

theorem Kwz_le (R : ℕ) :
    (∑ k ∈ Finset.range 51, Km (50 - k) R) ≤ 51 * Kbound := by
  calc (∑ k ∈ Finset.range 51, Km (50 - k) R)
      ≤ ∑ _k ∈ Finset.range 51, Kbound := by
        refine Finset.sum_le_sum (fun k hk => ?_)
        rw [Finset.mem_range] at hk
        by_cases h : R ≤ k
        · exact Km_le_Kbound _ _ (by omega)
        · rw [Km_eq_zero_of_gt _ _ (by omega)]
          exact Nat.zero_le _
    _ = 51 * Kbound := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul]

theorem bound_ok1 : (26 * 2 ^ 160) * (26 * 2 ^ 160) < BP := by decide

theorem bound_ok2 : (26 * 2 ^ 160) * (26 * 2 ^ 160) * (51 * Kbound) < BP := by decide

theorem ipos_le_natAbs (z : ℤ) : ipos z ≤ z.natAbs := by
  rw [ipos]
  rcases le_total 0 z with h | h
  · rw [max_eq_left h]
    have h1 : ((z.natAbs : ℕ) : ℤ) = z := Int.natAbs_of_nonneg h
    have h2 : ((z.toNat : ℕ) : ℤ) = z := Int.toNat_of_nonneg h
    exact_mod_cast (show ((z.toNat : ℕ) : ℤ) ≤ ((z.natAbs : ℕ) : ℤ) by rw [h2, h1])
  · rw [max_eq_right h]; exact Nat.zero_le _

theorem ineg_le_natAbs (z : ℤ) : ineg z ≤ z.natAbs := by
  rw [ineg]
  rcases le_total 0 (-z) with h | h
  · rw [max_eq_left h]
    have h1 : (((-z).natAbs : ℕ) : ℤ) = -z := Int.natAbs_of_nonneg h
    have h2 : (((-z).toNat : ℕ) : ℤ) = -z := Int.toNat_of_nonneg h
    have h3 : (((-z).natAbs : ℕ) : ℤ) = ((z.natAbs : ℕ) : ℤ) := by rw [Int.natAbs_neg]
    have h4 : (((-z).toNat : ℕ) : ℤ) ≤ ((z.natAbs : ℕ) : ℤ) := by
      rw [h2, ← h3]
      exact Int.le_natAbs
    exact_mod_cast h4
  · rw [max_eq_right h]; exact Nat.zero_le _

theorem getD_le_of_natAbs (v : List ℤ) (hb : ∀ z ∈ v, z.natAbs ≤ 2 ^ 160) (i : ℕ) :
    (vpos v).getD i 0 ≤ 2 ^ 160 ∧ (vneg v).getD i 0 ≤ 2 ^ 160 := by
  by_cases hi : i < v.length
  · have hmem : v[i] ∈ v := List.getElem_mem ..
    have h1 : (v[i]).natAbs ≤ 2 ^ 160 := hb _ hmem
    constructor
    · rw [vpos, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hi,
        Option.map_some, Option.getD_some]
      exact le_trans (ipos_le_natAbs _) h1
    · rw [vneg, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hi,
        Option.map_some, Option.getD_some]
      exact le_trans (ineg_le_natAbs _) h1
  · constructor
    · rw [vpos, List.getD_eq_default (v.map ipos) 0 (by rw [List.length_map]; exact not_lt.mp hi)]
      exact Nat.zero_le _
    · rw [vneg, List.getD_eq_default (v.map ineg) 0 (by rw [List.length_map]; exact not_lt.mp hi)]
      exact Nat.zero_le _

theorem sum_getD_le (v : List ℤ) (hb : ∀ z ∈ v, z.natAbs ≤ 2 ^ 160) :
    (∑ i ∈ Finset.range 26, (vpos v).getD i 0) ≤ 26 * 2 ^ 160
      ∧ (∑ i ∈ Finset.range 26, (vneg v).getD i 0) ≤ 26 * 2 ^ 160 := by
  constructor
  · calc (∑ i ∈ Finset.range 26, (vpos v).getD i 0)
        ≤ ∑ _i ∈ Finset.range 26, 2 ^ 160 :=
          Finset.sum_le_sum (fun i _ => (getD_le_of_natAbs v hb i).1)
      _ = 26 * 2 ^ 160 := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
  · calc (∑ i ∈ Finset.range 26, (vneg v).getD i 0)
        ≤ ∑ _i ∈ Finset.range 26, 2 ^ 160 :=
          Finset.sum_le_sum (fun i _ => (getD_le_of_natAbs v hb i).2)
      _ = 26 * 2 ^ 160 := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul]

theorem pwpos_le (v : List ℤ) (hv : v.length ≤ 26) :
    pw (vpos v) = ∑ i ∈ Finset.range 26, (vpos v).getD i 0 * BP ^ i :=
  pw_eq _ (by rw [vpos, List.length_map]; exact hv)

theorem pwneg_le (v : List ℤ) (hv : v.length ≤ 26) :
    pw (vneg v) = ∑ i ∈ Finset.range 26, (vneg v).getD i 0 * BP ^ i :=
  pw_eq _ (by rw [vneg, List.length_map]; exact hv)

theorem blk_bounds (x y : ℕ → ℕ)
    (hx : (∑ i ∈ Finset.range 26, x i) ≤ 26 * 2 ^ 160)
    (hy : (∑ j ∈ Finset.range 26, y j) ≤ 26 * 2 ^ 160) :
    (∑ i ∈ Finset.range 26, x i) * (∑ j ∈ Finset.range 26, y j) < BP
      ∧ (∑ i ∈ Finset.range 26, x i) * (∑ j ∈ Finset.range 26, y j)
          * (∑ k ∈ Finset.range 51, Km (50 - k) 0) < BP := by
  have hx0 : (0:ℕ) ≤ ∑ i ∈ Finset.range 26, x i := Nat.zero_le _
  constructor
  · exact lt_of_le_of_lt (Nat.mul_le_mul hx hy) bound_ok1
  · exact lt_of_le_of_lt (Nat.mul_le_mul (Nat.mul_le_mul hx hy) (Kwz_le 0)) bound_ok2

end Packed

end Commons.NumberTheory.MaynardSieve
