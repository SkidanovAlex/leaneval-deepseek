import Mathlib
import Submission.Work.KMTAreas.A4.invWeylDefs
import Submission.Work.KMTAreas.A4.coeff_comp_add_C_sub

set_option autoImplicit false
set_option maxHeartbeats 4000000

open scoped BigOperators
open Polynomial

namespace Work.KMTAreas.A4

/-! ## Auxiliary lemmas -/

/-- **Pigeonhole.**  A `Finset` of integers on which `f` takes values in `[1,Q]` has a fibre of
size at least `T.card / Q`. -/
theorem fiberCardAux (T : Finset ℤ) (f : ℤ → ℕ) (Q : ℕ) (hQ : 1 ≤ Q)
    (hf : ∀ h ∈ T, 1 ≤ f h ∧ f h ≤ Q) :
    ∃ q : ℕ, 1 ≤ q ∧ q ≤ Q ∧ T.card ≤ Q * (T.filter (fun h => f h = q)).card := by
  classical
  by_contra hcon
  push_neg at hcon
  have hsum : T.card = ∑ q ∈ Finset.Icc 1 Q, (T.filter (fun h => f h = q)).card :=
    Finset.card_eq_sum_card_fiberwise (fun h hh => by
      simp only [Finset.mem_coe, Finset.mem_Icc]
      exact hf h hh)
  have hne : (Finset.Icc 1 Q).Nonempty := ⟨1, by simp [hQ]⟩
  have hlt : ∑ q ∈ Finset.Icc 1 Q, Q * (T.filter (fun h => f h = q)).card
      < ∑ _q ∈ Finset.Icc 1 Q, T.card := by
    refine Finset.sum_lt_sum_of_nonempty hne (fun q hq => ?_)
    simp only [Finset.mem_Icc] at hq
    exact hcon q hq.1 hq.2
  have h1 : ∑ q ∈ Finset.Icc 1 Q, Q * (T.filter (fun h => f h = q)).card = Q * T.card := by
    rw [hsum, ← Finset.mul_sum]
  have h2 : ∑ _q ∈ Finset.Icc 1 Q, T.card = Q * T.card := by
    rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel]
    exact nsmul_eq_mul Q T.card
  rw [h1, h2] at hlt
  exact lt_irrefl _ hlt

/-- The overlap window has at most `(b-a)+1` elements. -/
theorem ovlCardAux (a b h : ℤ) (hab : a ≤ b) :
    ((ovl a b h).card : ℝ) ≤ ((b - a : ℤ) : ℝ) + 1 := by
  have hsub : ovl a b h ⊆ Finset.Icc a b := ovl_subset a b h
  have h1 : (ovl a b h).card ≤ (Finset.Icc a b).card := Finset.card_le_card hsub
  have h5 : ((ovl a b h).card : ℝ) ≤ ((Finset.Icc a b).card : ℝ) := by exact_mod_cast h1
  have h2 : (Finset.Icc a b).card = (b + 1 - a).toNat := Int.card_Icc a b
  have h3 : (((b + 1 - a).toNat : ℕ) : ℝ) = ((b - a : ℤ) : ℝ) + 1 := by
    have h4 : (0:ℤ) ≤ b + 1 - a := by omega
    have h5 : (((b + 1 - a).toNat : ℤ)) = b + 1 - a := Int.toNat_of_nonneg h4
    calc (((b + 1 - a).toNat : ℕ) : ℝ) = ((((b + 1 - a).toNat : ℤ)) : ℝ) := by push_cast; ring
      _ = ((b + 1 - a : ℤ) : ℝ) := by rw [h5]
      _ = ((b - a : ℤ) : ℝ) + 1 := by push_cast; ring
  rw [h2, h3] at h5
  exact h5

/-! ## Real-power bookkeeping -/

theorem rpow_neg_mono {S a b : ℝ} (hS0 : 0 < S) (hS1 : S ≤ 1) (hab : a ≤ b) :
    S ^ (-a) ≤ S ^ (-b) :=
  Real.rpow_le_rpow_of_exponent_ge hS0 hS1 (by linarith)

theorem const_pow_mul_rpow {S A B : ℝ} (hS : 0 < S) (n : ℕ) :
    A ^ n * S ^ (-(B * ((n:ℕ):ℝ))) = (A * S ^ (-B)) ^ n := by
  rw [mul_pow]
  have h : (S ^ (-B)) ^ n = S ^ (-(B * ((n:ℕ):ℝ))) := by
    rw [← Real.rpow_natCast (S ^ (-B)) n, ← Real.rpow_mul hS.le (-B) ((n:ℕ):ℝ)]
    congr 1
    ring
  rw [h]

theorem rpow_neg_nat {S : ℝ} (hS : 0 < S) (n : ℕ) :
    S ^ (-((n:ℕ):ℝ)) = (S ^ n)⁻¹ := by
  calc S ^ (-((n:ℕ):ℝ)) = (S ^ ((n:ℕ):ℝ))⁻¹ := Real.rpow_neg hS.le ((n:ℕ):ℝ)
    _ = (S ^ n)⁻¹ := by rw [Real.rpow_natCast]

theorem div64_rpow_neg {ε : ℝ} (hε : 0 < ε) (K : ℝ) :
    (ε ^ 2 / 64) ^ (-K) = 64 ^ K * ε ^ (-(2*K)) := by
  have h1 : (ε ^ 2 / 64) ^ (-K) = (ε^2)^(-K) / (64:ℝ)^(-K) :=
    Real.div_rpow (by positivity) (by norm_num) (-K)
  have h2 : (64:ℝ)^(-K) = (64^K)⁻¹ := Real.rpow_neg (by norm_num) K
  have h3 : (ε^2)^(-K) = ε ^ (-(2*K)) := by
    have hε2 : (ε^2 : ℝ) = ε ^ (2:ℝ) := (Real.rpow_natCast ε 2).symm
    rw [hε2, ← Real.rpow_mul hε.le (2:ℝ) (-K)]
    congr 1
    ring
  rw [h1, h2, h3, div_eq_mul_inv, inv_inv, mul_comm]

/-! ## Iterated sumsets in `ℤ` -/

/-- The pointwise sum of two finite sets of integers. -/
def addset (A B : Finset ℤ) : Finset ℤ := Finset.image₂ (· + ·) A B

theorem mem_addset {A B : Finset ℤ} {z : ℤ} :
    z ∈ addset A B ↔ ∃ a ∈ A, ∃ b ∈ B, a + b = z :=
  Finset.mem_image₂

theorem addset_nonempty {A B : Finset ℤ} (hA : A.Nonempty) (hB : B.Nonempty) :
    (addset A B).Nonempty := by
  obtain ⟨a, ha⟩ := hA
  obtain ⟨b, hb⟩ := hB
  exact ⟨a + b, mem_addset.mpr ⟨a, ha, b, hb, rfl⟩⟩

/-- For nonempty `A B ⊆ ℤ`, one has `|A| + |B| ≤ |A + B| + 1`. -/
theorem card_addset_ge (A B : Finset ℤ) (hA : A.Nonempty) (hB : B.Nonempty) :
    A.card + B.card ≤ (addset A B).card + 1 := by
  classical
  set m := B.min' hB with hm
  have hmB : m ∈ B := Finset.min'_mem B hB
  set x := A.max' hA with hx
  have hxA : x ∈ A := Finset.max'_mem A hA
  set P : Finset ℤ := A.image (fun a => a + m) with hP
  set Q : Finset ℤ := (B.erase m).image (fun b => x + b) with hQ
  have hPcard : P.card = A.card :=
    Finset.card_image_of_injective _ (fun a a' h => by simpa using h)
  have hQcard : Q.card = B.card - 1 := by
    rw [hQ, Finset.card_image_of_injective _ (fun b b' h => by simpa using h),
      Finset.card_erase_of_mem hmB]
  have hdisj : Disjoint P Q := by
    rw [Finset.disjoint_left]
    intro z hzP hzQ
    obtain ⟨a, haA, haz⟩ := Finset.mem_image.mp hzP
    obtain ⟨b, hbB, hbz⟩ := Finset.mem_image.mp hzQ
    rw [Finset.mem_erase] at hbB
    have h1 : a ≤ x := Finset.le_max' A a haA
    have h2 : m < b := lt_of_le_of_ne (Finset.min'_le B b hbB.2) (fun hc => hbB.1 hc.symm)
    omega
  have hsub : P ∪ Q ⊆ addset A B := by
    intro z hz
    rw [Finset.mem_union] at hz
    rcases hz with hz | hz
    · obtain ⟨a, haA, haz⟩ := Finset.mem_image.mp hz
      rw [← haz]
      exact mem_addset.mpr ⟨a, haA, m, hmB, rfl⟩
    · obtain ⟨b, hbB, hbz⟩ := Finset.mem_image.mp hz
      have hbB' : b ∈ B := (Finset.mem_erase.mp hbB).2
      rw [← hbz]
      exact mem_addset.mpr ⟨x, hxA, b, hbB', rfl⟩
  have h1 : (P ∪ Q).card ≤ (addset A B).card := Finset.card_le_card hsub
  have h2 : (P ∪ Q).card = P.card + Q.card := Finset.card_union_of_disjoint hdisj
  have hB1 : 1 ≤ B.card := Finset.card_pos.mpr hB
  omega

/-- The `k`-fold sumset of a finite set of integers: `sumsetAux 0 T = {0}` and
`sumsetAux (k+1) T = addset (sumsetAux k T) T`. -/
def sumsetAux : ℕ → Finset ℤ → Finset ℤ
  | 0, _ => {0}
  | (k + 1), T => addset (sumsetAux k T) T

theorem sumsetAux_zero (T : Finset ℤ) : sumsetAux 0 T = {0} := rfl

theorem sumsetAux_succ (k : ℕ) (T : Finset ℤ) : sumsetAux (k+1) T = addset (sumsetAux k T) T := rfl

theorem sumsetAux_nonempty (T : Finset ℤ) (hT : T.Nonempty) (k : ℕ) :
    (sumsetAux k T).Nonempty := by
  induction k with
  | zero => exact ⟨0, by rw [sumsetAux_zero]; exact Finset.mem_singleton_self 0⟩
  | succ k ih => exact addset_nonempty ih hT

theorem card_sumsetAux_one (T : Finset ℤ) : (sumsetAux 1 T).card = T.card := by
  rw [sumsetAux_succ, sumsetAux_zero]
  have hzero : addset ({0} : Finset ℤ) T = T := by
    ext z
    constructor
    · intro hz
      obtain ⟨a, ha, b, hb, rfl⟩ := mem_addset.mp hz
      rw [Finset.mem_singleton] at ha
      subst ha
      simpa using hb
    · intro hz
      exact mem_addset.mpr ⟨0, by simp, z, hz, by ring⟩
  rw [hzero]

/-- The `k`-fold sumset has at least `k|T| - (k-1)` elements. -/
theorem card_sumsetAux_ge (T : Finset ℤ) (hT : T.Nonempty) :
    ∀ k : ℕ, 1 ≤ k → k * T.card ≤ (sumsetAux k T).card + (k - 1) := by
  intro k
  induction k with
  | zero => intro hk; omega
  | succ k ih =>
    intro hk
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · subst hk0
      rw [card_sumsetAux_one]
      simp
    · have ihk := ih hkpos
      have hne : (sumsetAux k T).Nonempty := sumsetAux_nonempty T hT k
      have hadd : (sumsetAux k T).card + T.card ≤ (addset (sumsetAux k T) T).card + 1 :=
        card_addset_ge (sumsetAux k T) T hne hT
      rw [sumsetAux_succ]
      have hsub : (k + 1) - 1 = k := by omega
      rw [hsub, Nat.succ_mul]
      omega

/-- Elements of the `k`-fold sumset are bounded by `k` times a bound for `T`. -/
theorem sumsetAux_abs_le (T : Finset ℤ) (M : ℝ) (n : ℕ) (hT : ∀ t ∈ T, |(t:ℝ)| ≤ M) :
    ∀ x ∈ sumsetAux n T, |(x:ℝ)| ≤ n * M := by
  induction n with
  | zero =>
    intro x hx
    rw [sumsetAux_zero, Finset.mem_singleton] at hx
    subst hx
    simp
  | succ n ih =>
    intro x hx
    rw [sumsetAux_succ] at hx
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_addset.mp hx
    have h1 := ih a ha
    have h2 := hT b hb
    push_cast
    calc |(a:ℝ) + (b:ℝ)| ≤ |(a:ℝ)| + |(b:ℝ)| := abs_add_le _ _
      _ ≤ n*M + M := by linarith
      _ = (n+1)*M := by ring

/-- Along the `k`-fold sumset the Weyl sum stays close to an integer. -/
theorem sumsetAux_close (T : Finset ℤ) (β δ : ℝ) (n : ℕ)
    (hT : ∀ t ∈ T, ∃ m : ℤ, |β * (t:ℝ) - (m:ℝ)| ≤ δ) :
    ∀ x ∈ sumsetAux n T, ∃ m : ℤ, |β * (x:ℝ) - (m:ℝ)| ≤ n * δ := by
  induction n with
  | zero =>
    intro x hx
    rw [sumsetAux_zero, Finset.mem_singleton] at hx
    subst hx
    exact ⟨0, by simp⟩
  | succ n ih =>
    intro x hx
    rw [sumsetAux_succ] at hx
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_addset.mp hx
    obtain ⟨m1, hm1⟩ := ih a ha
    obtain ⟨m2, hm2⟩ := hT b hb
    refine ⟨m1 + m2, ?_⟩
    push_cast
    calc |β * ((a:ℝ) + (b:ℝ)) - ((m1:ℝ) + (m2:ℝ))|
        = |(β*(a:ℝ) - (m1:ℝ)) + (β*(b:ℝ) - (m2:ℝ))| := by ring_nf
      _ ≤ |β*(a:ℝ) - (m1:ℝ)| + |β*(b:ℝ) - (m2:ℝ)| := abs_add_le _ _
      _ ≤ n*δ + δ := by linarith
      _ = (n+1)*δ := by ring

/-! ## The arithmetic core -/

/-- Arithmetic bookkeeping for the induction step of the inverse Weyl estimate, with
`s = ε²/64 ∈ (0,1]`, `Q₀ ≤ C s^{-K}` and `M s^{-M} < L^{d+1}`. -/
theorem arithCore2 (d : ℕ) (hd : 1 ≤ d) (C K C₀ : ℝ) (hC : 0 < C) (hK : 0 < K) (hC₀ : 0 < C₀) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ (S L Q₀ : ℝ), 0 < S → S ≤ 1 → 1 ≤ L → 1 ≤ Q₀ →
      Q₀ ≤ C * S ^ (-K) →
      M * S ^ (-M) < L ^ (d + 1) →
      12 * Q₀ / S ≤ L ∧
      96 * Q₀ ^ 2 / S ^ (d + 1) ≤ L ^ d ∧
      192 * Q₀ ^ 2 / S ≤ M * S ^ (-M) ∧
      16384 * 1296 * C₀ * Q₀ ^ 5 / S ^ (d + 4) ≤ M * S ^ (-M) := by
  set M : ℝ := (12*C) ^ (d+1) + (K+1) * ((d+1:ℕ):ℝ) + (96*C^2) ^ (d+1)
      + (2*K + (d:ℝ) + 1) * ((d+1:ℕ):ℝ) + 192*C^2 + (2*K+1)
      + 16384 * 1296 * C₀ * C^5 + (5*K + (d:ℝ) + 4) + 1 with hMdef
  have hn1 : (0:ℝ) ≤ (12*C) ^ (d+1) := by positivity
  have hn2 : (0:ℝ) ≤ (K+1) * ((d+1:ℕ):ℝ) := by positivity
  have hn3 : (0:ℝ) ≤ (96*C^2) ^ (d+1) := by positivity
  have hn4 : (0:ℝ) ≤ (2*K + (d:ℝ) + 1) * ((d+1:ℕ):ℝ) := by positivity
  have hn5 : (0:ℝ) ≤ 192*C^2 := by positivity
  have hn6 : (0:ℝ) ≤ (2*K+1) := by positivity
  have hn7 : (0:ℝ) ≤ 16384 * 1296 * C₀ * C^5 := by positivity
  have hn8 : (0:ℝ) ≤ (5*K + (d:ℝ) + 4) := by positivity
  have hM1 : 1 ≤ M := by
    rw [hMdef]
    linarith [hn1,hn2,hn3,hn4,hn5,hn6,hn7,hn8]
  have hb1 : (12*C) ^ (d+1) ≤ M := by rw [hMdef]; linarith [hn1,hn2,hn3,hn4,hn5,hn6,hn7,hn8]
  have hb2 : (K+1) * ((d+1:ℕ):ℝ) ≤ M := by rw [hMdef]; linarith [hn1,hn2,hn3,hn4,hn5,hn6,hn7,hn8]
  have hb3 : (96*C^2) ^ (d+1) ≤ M := by rw [hMdef]; linarith [hn1,hn2,hn3,hn4,hn5,hn6,hn7,hn8]
  have hb4 : (2*K + (d:ℝ) + 1) * ((d+1:ℕ):ℝ) ≤ M := by
    rw [hMdef]; linarith [hn1,hn2,hn3,hn4,hn5,hn6,hn7,hn8]
  have hb5 : 192*C^2 ≤ M := by rw [hMdef]; linarith [hn1,hn2,hn3,hn4,hn5,hn6,hn7,hn8]
  have hb6 : (2*K+1) ≤ M := by rw [hMdef]; linarith [hn1,hn2,hn3,hn4,hn5,hn6,hn7,hn8]
  have hb7 : 16384 * 1296 * C₀ * C^5 ≤ M := by rw [hMdef]; linarith [hn1,hn2,hn3,hn4,hn5,hn6,hn7,hn8]
  have hb8 : (5*K + (d:ℝ) + 4) ≤ M := by rw [hMdef]; linarith [hn1,hn2,hn3,hn4,hn5,hn6,hn7,hn8]
  refine ⟨M, hM1, ?_⟩
  intro S L Q₀ hS0 hS1 hL1 hQ₀1 hQ₀le hbig
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hM1
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL1
  have hQ₀pos : 0 < Q₀ := lt_of_lt_of_le zero_lt_one hQ₀1
  have hSpow : ∀ (a : ℝ), 0 ≤ S ^ a := fun a => Real.rpow_nonneg hS0.le a
  -- power bounds for Q₀
  have hpow : ∀ n : ℕ, Q₀ ^ n ≤ C ^ n * S ^ (-(n * K)) := by
    intro n
    have h2 : Q₀^n ≤ (C * S ^ (-K))^n := pow_le_pow_left₀ hQ₀pos.le hQ₀le n
    have h3 : (C * S ^ (-K))^n = C^n * S ^ (-(n*K)) := by
      rw [mul_pow]
      congr 1
      rw [← Real.rpow_natCast, ← Real.rpow_mul hS0.le]
      congr 1
      ring
    rwa [h3] at h2
  have hQS : Q₀ / S ≤ C * S ^ (-(K+1)) := by
    rw [div_eq_mul_inv, ← Real.rpow_neg_one S]
    have h1 : Q₀ * S ^ (-1:ℝ) ≤ (C * S ^ (-K)) * S ^ (-1:ℝ) :=
      mul_le_mul_of_nonneg_right hQ₀le (hSpow _)
    have h2 : (C * S ^ (-K)) * S ^ (-1:ℝ) = C * S ^ (-(K+1)) := by
      rw [mul_assoc, ← Real.rpow_add hS0,
        show -K + (-1:ℝ) = -(K+1) by ring]
    linarith [h1, h2]
  have hQ2S : Q₀ ^ 2 / S ≤ C^2 * S ^ (-(2*K+1)) := by
    rw [div_eq_mul_inv, ← Real.rpow_neg_one S]
    have h1 : Q₀^2 * S ^ (-1:ℝ) ≤ (C^2 * S ^ (-(2*K))) * S ^ (-1:ℝ) :=
      mul_le_mul_of_nonneg_right (hpow 2) (hSpow _)
    have h2 : (C^2 * S ^ (-(2*K))) * S ^ (-1:ℝ) = C^2 * S ^ (-(2*K+1)) := by
      rw [mul_assoc, ← Real.rpow_add hS0,
        show -(2*K) + (-1:ℝ) = -(2*K+1) by ring]
    linarith [h1, h2]
  have hQ2L : Q₀ ^ 2 / S ^ (d+1) ≤ C^2 * S ^ (-(2*K+d+1)) := by
    rw [div_eq_mul_inv, ← rpow_neg_nat hS0 (d+1)]
    have h1 : Q₀^2 * S ^ (-((d+1:ℕ):ℝ)) ≤ (C^2 * S ^ (-(2*K))) * S ^ (-((d+1:ℕ):ℝ)) :=
      mul_le_mul_of_nonneg_right (hpow 2) (hSpow _)
    have h2 : (C^2 * S ^ (-(2*K))) * S ^ (-((d+1:ℕ):ℝ)) = C^2 * S ^ (-(2*K+d+1)) := by
      rw [mul_assoc, ← Real.rpow_add hS0,
        show -(2*K) + (-((d+1:ℕ):ℝ)) = -(2*K+(d:ℝ)+1) by push_cast; ring]
    linarith [h1, h2]
  have hQ5 : Q₀ ^ 5 / S ^ (d+4) ≤ C^5 * S ^ (-(5*K+d+4)) := by
    rw [div_eq_mul_inv, ← rpow_neg_nat hS0 (d+4)]
    have h1 : Q₀^5 * S ^ (-((d+4:ℕ):ℝ)) ≤ (C^5 * S ^ (-(5*K))) * S ^ (-((d+4:ℕ):ℝ)) :=
      mul_le_mul_of_nonneg_right (hpow 5) (hSpow _)
    have h2 : (C^5 * S ^ (-(5*K))) * S ^ (-((d+4:ℕ):ℝ)) = C^5 * S ^ (-(5*K+d+4)) := by
      rw [mul_assoc, ← Real.rpow_add hS0,
        show -(5*K) + (-((d+4:ℕ):ℝ)) = -(5*K+(d:ℝ)+4) by push_cast; ring]
    linarith [h1, h2]
  have key : ∀ (A W : ℝ), 0 ≤ A → A ^ (d+1) ≤ M → W * ((d+1:ℕ):ℝ) ≤ M →
      A ^ (d+1) * S ^ (-(W * ((d+1:ℕ):ℝ))) ≤ M * S ^ (-M) := by
    intro A W hA hAM hWM
    exact mul_le_mul hAM (rpow_neg_mono hS0 hS1 hWM) (hSpow _) hMpos.le
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- 12 Q₀ / S ≤ L
    have hmain : 12 * C * S ^ (-(K+1)) ≤ L := by
      have h1 : (12*C)^(d+1) * S ^ (-((K+1) * ((d+1:ℕ):ℝ))) ≤ M * S ^ (-M) :=
        key (12*C) (K+1) (by positivity) hb1 hb2
      rw [const_pow_mul_rpow hS0 (d+1)] at h1
      have h3 : (12*C * S ^ (-(K+1)))^(d+1) < L ^ (d+1) := lt_of_le_of_lt h1 hbig
      exact le_of_lt ((pow_lt_pow_iff_left₀ (by positivity) (le_of_lt hLpos) (by omega)).mp h3)
    calc 12 * Q₀ / S = 12 * (Q₀ / S) := by ring
      _ ≤ 12 * (C * S ^ (-(K+1))) := by linarith [hQS]
      _ = 12 * C * S ^ (-(K+1)) := by ring
      _ ≤ L := hmain
  · -- 96 Q₀^2 / S^(d+1) ≤ L^d
    have hR : 96 * C^2 * S ^ (-(2*K+(d:ℝ)+1)) ≤ L := by
      have h1 : (96*C^2)^(d+1) * S ^ (-((2*K + (d:ℝ) + 1) * ((d+1:ℕ):ℝ))) ≤ M * S ^ (-M) :=
        key (96*C^2) (2*K + (d:ℝ) + 1) (by positivity) hb3 hb4
      rw [const_pow_mul_rpow hS0 (d+1)] at h1
      have h3 : (96*C^2 * S ^ (-(2*K + (d:ℝ) + 1)))^(d+1) < L ^ (d+1) := lt_of_le_of_lt h1 hbig
      exact le_of_lt ((pow_lt_pow_iff_left₀ (by positivity) (le_of_lt hLpos) (by omega)).mp h3)
    calc 96 * Q₀ ^ 2 / S ^ (d+1) = 96 * (Q₀^2 / S^(d+1)) := by ring
      _ ≤ 96 * (C^2 * S ^ (-(2*K+d+1))) := by linarith [hQ2L]
      _ = 96 * C^2 * S ^ (-(2*K+(d:ℝ)+1)) := by ring
      _ ≤ L := hR
      _ ≤ L ^ d := le_self_pow₀ hL1 (by omega)
  · -- 192 Q₀^2 / S ≤ M S^{-M}
    calc 192 * Q₀ ^ 2 / S = 192 * (Q₀^2 / S) := by ring
      _ ≤ 192 * (C^2 * S ^ (-(2*K+1))) := by linarith [hQ2S]
      _ = (192*C^2) * S ^ (-(2*K+1)) := by ring
      _ ≤ M * S ^ (-M) :=
          mul_le_mul hb5 (rpow_neg_mono hS0 hS1 hb6) (hSpow _) hMpos.le
  · -- 16384 * 1296 * C₀ * Q₀^5 / S^(d+4) ≤ M S^{-M}
    calc 16384 * 1296 * C₀ * Q₀ ^ 5 / S ^ (d+4)
        = (16384 * 1296 * C₀) * (Q₀^5 / S^(d+4)) := by ring
      _ ≤ (16384 * 1296 * C₀) * (C^5 * S ^ (-(5*K+d+4))) :=
          mul_le_mul_of_nonneg_left hQ5 (by positivity)
      _ = (16384 * 1296 * C₀ * C^5) * S ^ (-(5*K+d+4)) := by ring
      _ ≤ M * S ^ (-M) :=
          mul_le_mul hb7 (rpow_neg_mono hS0 hS1 hb8) (hSpow _) hMpos.le

/-! ## The induction step -/

theorem invWeylStep (d : ℕ) (hd : 1 ≤ d) (C K : ℝ) (hC : 0 < C) (hK : 0 < K) (hAmp : Work.KMTAreas.A4.AmplifyStatement) (hDense : Work.KMTAreas.A4.DenseExists) : ∃ C' K' : ℝ, 0 < C' ∧ 0 < K' ∧ ∀ (Q : Polynomial ℤ) (hQ : Q.natDegree = d + 1) (ξ : ℝ) (a b : ℤ) (ε : ℝ) (H : Finset ℤ), a ≤ b → 0 < ε → ε ≤ 1 → (∀ h ∈ H, h ≠ 0) → (∀ h ∈ H, -(b - a) ≤ h ∧ h ≤ b - a) → (∀ h ∈ H, ε ^ 2 / 64 * (((b - a : ℤ) : ℝ) + 1) ≤ ((Work.KMTAreas.A4.ovl a b h).card : ℝ)) → (ε ^ 2 / 64 * (((b - a : ℤ) : ℝ) + 1) ^ 2 ≤ ∑ h ∈ H, ((Work.KMTAreas.A4.ovl a b h).card : ℝ)) → (∀ h ∈ H, ∃ q : ℕ, 1 ≤ q ∧ (q : ℝ) ≤ C * (ε ^ 2 / 64) ^ (-K) ∧ ∃ m : ℤ, |(q : ℝ) * ξ * (((Q - Q.comp (Polynomial.X + Polynomial.C h)).coeff d : ℤ) : ℝ) - (m : ℝ)| ≤ C * (ε ^ 2 / 64) ^ (-K) / (((Work.KMTAreas.A4.ovl a b h).card : ℝ)) ^ d) → ∃ q : ℕ, 1 ≤ q ∧ (q : ℝ) ≤ C' * ε ^ (-K') ∧ ∃ m : ℤ, |(q : ℝ) * ξ * ((Q.coeff (d + 1) : ℤ) : ℝ) - (m : ℝ)| ≤ C' * ε ^ (-K') / ((((b - a : ℤ) : ℝ) + 1) ^ (d + 1)) := by
  classical
  obtain ⟨C₀, hC₀pos, hDensestmt⟩ := hDense
  obtain ⟨M, hM1, hMarith⟩ := arithCore2 d hd C K C₀ hC hK hC₀pos
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hM1
  refine ⟨((d:ℝ)+1) * M * 64 ^ M, 2 * M, by positivity, by positivity, ?_⟩
  intro Q hQ ξ a b ε H hab hε0 hε1 hHnz hHrng hcard1 hcardsum hhyp
  set S : ℝ := ε ^ 2 / 64 with hSdef
  set L : ℝ := ((b - a : ℤ) : ℝ) + 1 with hLdef
  set Mnat : ℕ := (b - a).toNat with hMnatdef
  set Q₀ : ℝ := C * S ^ (-K) with hQ₀def
  set cc : ℝ := ((Q.coeff (d + 1) : ℤ) : ℝ) with hccdef
  set β : ℝ := ((d:ℝ)+1) * ξ * cc with hβdef
  have hSpos : 0 < S := by rw [hSdef]; positivity
  have hS1 : S ≤ 1 := by
    rw [hSdef]
    have h1 : ε^2 ≤ 1 := by nlinarith [hε0, hε1]
    linarith
  have hba : (0:ℤ) ≤ b - a := by omega
  have hMnat : ((Mnat:ℤ)) = b - a := Int.toNat_of_nonneg hba
  have hL1 : 1 ≤ L := by
    rw [hLdef]
    have h2 : (0:ℝ) ≤ ((b - a : ℤ) : ℝ) := by exact_mod_cast hba
    linarith
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL1
  have hLM : L = (Mnat:ℝ) + 1 := by rw [hLdef, ← hMnat]; push_cast; ring
  have hcore : ∃ q : ℕ, 1 ≤ q ∧ (q:ℝ) ≤ M * S ^ (-M) ∧
      ∃ m : ℤ, |(q:ℝ) * β - (m:ℝ)| ≤ M * S ^ (-M) / L ^ (d+1) := by
    by_cases hsmall : L ^ (d+1) ≤ M * S ^ (-M)
    · refine ⟨1, le_refl 1, ?_, round β, ?_⟩
      · have h1 : (1:ℝ) ≤ S ^ (-M) := by
          have h := Real.rpow_le_rpow_of_exponent_ge hSpos hS1 (show (-M:ℝ) ≤ 0 by linarith)
          rwa [Real.rpow_zero] at h
        have h2 := mul_le_mul hM1 h1 (by norm_num : (0:ℝ) ≤ 1) hMpos.le
        simpa using h2
      · have h2 : (1:ℝ) ≤ M * S ^ (-M) / L ^ (d+1) := by
          rw [le_div_iff₀ (by positivity)]
          linarith [hsmall]
        have h3 : |β - (round β : ℝ)| ≤ 1/2 := abs_sub_round β
        rw [Nat.cast_one, one_mul]
        linarith
    · have hbig : M * S ^ (-M) < L ^ (d+1) := not_le.mp hsmall
      have hHne : H.Nonempty := by
        by_contra hne
        rw [Finset.not_nonempty_iff_eq_empty] at hne
        rw [hne] at hcardsum
        simp only [Finset.sum_empty] at hcardsum
        have hpos : (0:ℝ) < S * L^2 := by positivity
        linarith
      obtain ⟨h₀, hh₀⟩ := hHne
      obtain ⟨q₀, hq₀1, hq₀le, -⟩ := hhyp h₀ hh₀
      have hQ₀1 : 1 ≤ Q₀ := by
        have h1 : (1:ℝ) ≤ (q₀:ℝ) := by exact_mod_cast hq₀1
        linarith
      have hQ₀pos : 0 < Q₀ := lt_of_lt_of_le zero_lt_one hQ₀1
      obtain ⟨hA1, hA2, hA3, hA4⟩ := hMarith S L Q₀ hSpos hS1 hL1 hQ₀1 hQ₀def.le hbig
      set D₁ : ℝ := Q₀ / (S * L) ^ d with hD₁def
      set D₂ : ℝ := S / (6 * Q₀) with hD₂def
      have hD₁pos : 0 < D₁ := by rw [hD₁def]; positivity
      have hD₂pos : 0 < D₂ := by rw [hD₂def]; positivity
      have hD₂le1 : D₂ ≤ 1 := by
        rw [hD₂def, div_le_one (by positivity)]
        nlinarith [hS1, hQ₀1]
      have hD₂L2 : 2 ≤ D₂ * L := by
        have h1 : D₂ * L = S * L / (6 * Q₀) := by rw [hD₂def]; ring
        rw [h1, le_div_iff₀ (by positivity : (0:ℝ) < 6 * Q₀)]
        rw [div_le_iff₀ (by positivity : (0:ℝ) < S)] at hA1
        linarith [hA1]
      let qf : ℤ → ℕ := fun h => if hh : h ∈ H then Classical.choose (hhyp h hh) else 1
      have hqf : ∀ h ∈ H, 1 ≤ qf h ∧ (qf h : ℝ) ≤ Q₀ ∧
          ∃ m : ℤ, |(qf h : ℝ) * ξ * (((Q - Q.comp (Polynomial.X + Polynomial.C h)).coeff d : ℤ) : ℝ) - (m : ℝ)|
            ≤ Q₀ / (((ovl a b h).card : ℝ)) ^ d := by
        intro h hh
        have hval : qf h = Classical.choose (hhyp h hh) := by
          simp only [qf, dif_pos hh]
        rw [hval]
        exact Classical.choose_spec (hhyp h hh)
      have hper : ∀ h ∈ H, ∃ m : ℤ, |(qf h : ℝ) * (h:ℝ) * β - (m:ℝ)| ≤ D₁ := by
        intro h hh
        obtain ⟨m, hm⟩ := (hqf h hh).2.2
        have hco := (coeff_comp_add_C_sub Q (d+1) hQ (by omega) h (hHnz h hh)).2
        have hcoeff : (Q - Q.comp (Polynomial.X + Polynomial.C h)).coeff d
            = -(h * ((d+1:ℕ):ℤ) * Q.coeff (d+1)) := by
          rw [show d = (d + 1) - 1 by omega]
          exact hco
        have hcoeffR : (((Q - Q.comp (Polynomial.X + Polynomial.C h)).coeff d : ℤ) : ℝ)
            = -((h:ℝ) * ((d:ℝ)+1) * cc) := by
          rw [hcoeff]; simp only [hccdef]; push_cast; ring
        have hrew : (qf h : ℝ) * ξ * (((Q - Q.comp (Polynomial.X + Polynomial.C h)).coeff d : ℤ) : ℝ)
            = -((qf h : ℝ) * (h:ℝ) * β) := by
          rw [hcoeffR]; simp only [hβdef]; ring
        rw [hrew] at hm
        have h1 : |(-((qf h : ℝ) * (h:ℝ) * β)) - (m:ℝ)|
            = |(qf h : ℝ) * (h:ℝ) * β - ((-m : ℤ) : ℝ)| := by
          rw [show (-((qf h : ℝ) * (h:ℝ) * β)) - (m:ℝ)
                = -(((qf h:ℝ) * (h:ℝ) * β) + (m:ℝ)) by ring, abs_neg]
          congr 1
          push_cast
          ring
        refine ⟨-m, ?_⟩
        rw [h1] at hm
        refine le_trans hm ?_
        rw [hD₁def]
        have hSL : S * L ≤ ((ovl a b h).card : ℝ) := hcard1 h hh
        have hpow : (S * L)^d ≤ ((ovl a b h).card : ℝ)^d := pow_le_pow_left₀ (by positivity) hSL d
        exact div_le_div_of_nonneg_left hQ₀pos.le (by positivity) hpow
      have hQn1 : 1 ≤ ⌊Q₀⌋₊ + 1 := by omega
      have hQfQ : ∀ h ∈ H, 1 ≤ qf h ∧ qf h ≤ ⌊Q₀⌋₊ + 1 := by
        intro h hh
        obtain ⟨h1, h2, -⟩ := hqf h hh
        refine ⟨h1, ?_⟩
        have h3 : (qf h : ℝ) < ((⌊Q₀⌋₊ + 1 : ℕ) : ℝ) := by
          have h4 := Nat.lt_floor_add_one Q₀
          push_cast
          linarith [h2, h4]
        exact_mod_cast le_of_lt h3
      obtain ⟨q, hq1, hqq, hqcard⟩ := fiberCardAux H qf (⌊Q₀⌋₊ + 1) hQn1 hQfQ
      set T₀ : Finset ℤ := H.filter (fun h => qf h = q) with hT₀def
      have hQn2 : (((⌊Q₀⌋₊ + 1 : ℕ)) : ℝ) ≤ 2 * Q₀ := by
        have h4 : ((⌊Q₀⌋₊ : ℕ) : ℝ) ≤ Q₀ := Nat.floor_le hQ₀pos.le
        push_cast
        linarith
      have hHcard : S * L ≤ (H.card : ℝ) := by
        have hsum_le : ∑ h ∈ H, ((ovl a b h).card : ℝ) ≤ (H.card : ℝ) * L := by
          have h1 : ∀ h ∈ H, ((ovl a b h).card : ℝ) ≤ L := by
            intro h _
            have h2 := ovlCardAux a b h hab
            rw [← hLdef] at h2
            exact h2
          calc ∑ h ∈ H, ((ovl a b h).card : ℝ) ≤ ∑ _h ∈ H, L := Finset.sum_le_sum h1
            _ = (H.card : ℝ) * L := by rw [Finset.sum_const, nsmul_eq_mul]
        have h3 : (S * L) * L ≤ (H.card : ℝ) * L := by
          have h4 := le_trans hcardsum hsum_le
          nlinarith [h4]
        exact le_of_mul_le_mul_right h3 hLpos
      have hTcard : S * L / (2 * Q₀) ≤ (T₀.card : ℝ) := by
        have h1 : (H.card : ℝ) ≤ ((⌊Q₀⌋₊ + 1 : ℕ) : ℝ) * (T₀.card : ℝ) := by
          have h5 : H.card ≤ (⌊Q₀⌋₊ + 1) * (T₀.card) := by
            rw [hT₀def]; exact hqcard
          exact_mod_cast h5
        have h2 : (H.card : ℝ) / (2 * Q₀) ≤ ((⌊Q₀⌋₊ + 1 : ℕ) : ℝ) * (T₀.card : ℝ) / (2*Q₀) :=
          div_le_div_of_nonneg_right h1 (by positivity)
        have h3 : ((⌊Q₀⌋₊ + 1 : ℕ) : ℝ) / (2*Q₀) ≤ 1 := by
          rw [div_le_one (by positivity)]
          exact hQn2
        calc S * L / (2 * Q₀) ≤ (H.card : ℝ) / (2 * Q₀) :=
              div_le_div_of_nonneg_right hHcard (by positivity)
          _ ≤ ((⌊Q₀⌋₊ + 1 : ℕ) : ℝ) * (T₀.card : ℝ) / (2*Q₀) := h2
          _ = (((⌊Q₀⌋₊ + 1 : ℕ) : ℝ) / (2*Q₀)) * (T₀.card : ℝ) := by ring
          _ ≤ 1 * (T₀.card : ℝ) := mul_le_mul_of_nonneg_right h3 (by positivity)
          _ = (T₀.card : ℝ) := by ring
      have hT₀ne : T₀.Nonempty := by
        have hh : (0:ℝ) < S * L / (2 * Q₀) := by positivity
        have h2 : (0:ℝ) < (T₀.card : ℝ) := lt_of_lt_of_le hh hTcard
        exact Finset.card_pos.mp (by exact_mod_cast h2)
      have hT₀ne' := hT₀ne
      obtain ⟨h₁, hh₁⟩ := hT₀ne'
      have hh₁H : h₁ ∈ H := by
        rw [hT₀def] at hh₁; exact (Finset.mem_filter.mp hh₁).1
      have hqQ₀ : (q:ℝ) ≤ Q₀ := by
        have h1 := (hqf h₁ hh₁H).2.1
        rw [hT₀def] at hh₁
        rw [(Finset.mem_filter.mp hh₁).2] at h1
        exact h1
      have hTabs : ∀ t ∈ T₀, |(t:ℝ)| ≤ (Mnat:ℝ) := by
        intro t ht
        rw [hT₀def] at ht
        have h1 := hHrng t (Finset.mem_filter.mp ht).1
        have h3 : -((Mnat:ℤ)) ≤ t ∧ t ≤ (Mnat:ℤ) := ⟨by omega, by omega⟩
        rw [abs_le]
        exact ⟨by exact_mod_cast h3.1, by exact_mod_cast h3.2⟩
      have hTdens : D₂ * (2 * L + 1) ≤ (T₀.card : ℝ) := by
        rw [hD₂def]
        have h1 : S / (6*Q₀) * (2*L+1) ≤ S * L / (2*Q₀) := by
          rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
          have h2 : (2:ℝ) * (2*L+1) ≤ 6*L := by linarith
          calc S * (2*L+1) * (2*Q₀) = 2*(2*L+1) * (S*Q₀) := by ring
            _ ≤ 6*L * (S*Q₀) := mul_le_mul_of_nonneg_right h2 (by positivity)
            _ = S * L * (6*Q₀) := by ring
        linarith [h1, hTcard]
      set k : ℕ := ⌊D₂ / (16 * D₁)⌋₊ with hkdef
      have hD1le : D₁ ≤ D₂ / 16 := by
        rw [hD₁def, hD₂def, div_le_div_iff₀ (by positivity) (by positivity)]
        rw [mul_pow]
        have h1 : 96 * Q₀^2 ≤ S^(d+1) * L^d := by
          have h2 := (div_le_iff₀ (by positivity : (0:ℝ) < S^(d+1))).mp hA2
          calc 96*Q₀^2 ≤ L^d * S^(d+1) := h2
            _ = S^(d+1) * L^d := by ring
        rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity : (0:ℝ) < 6*Q₀)]
        calc Q₀ * 16 * (6*Q₀) = 96*Q₀^2 := by ring
          _ ≤ S^(d+1)*L^d := h1
          _ = S * (S^d * L^d) := by rw [pow_add]; ring
      have hk1 : 1 ≤ k := by
        rw [hkdef]
        apply Nat.le_floor
        rw [le_div_iff₀ (by positivity), Nat.cast_one, one_mul]
        linarith [hD1le]
      have hkpos : (0:ℝ) < (k:ℝ) := by
        exact_mod_cast (lt_of_lt_of_le zero_lt_one hk1)
      have hk1R : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk1
      have hkD₂ : D₂ ≤ 32 * D₁ * (k:ℝ) := by
        have hx1 : (1:ℝ) ≤ D₂ / (16 * D₁) := by
          rw [le_div_iff₀ (by positivity)]; linarith [hD1le]
        by_cases hx2 : (2:ℝ) ≤ D₂ / (16 * D₁)
        · have h32 : 32 * D₁ ≤ D₂ := by
            rw [le_div_iff₀ (by positivity : (0:ℝ) < 16*D₁)] at hx2
            linarith
          have h1 : D₂ / (16 * D₁) - 1 < (k:ℝ) := by
            rw [hkdef]
            have h2 := Nat.lt_floor_add_one (D₂ / (16 * D₁))
            linarith
          have h3 : D₂ ≤ 32 * D₁ * (D₂ / (16 * D₁) - 1) := by
            have h4 : 32 * D₁ * (D₂ / (16 * D₁)) = 2 * D₂ := by field_simp; ring
            linarith [h4, h32]
          have h5 : 0 ≤ 32 * D₁ := by positivity
          nlinarith [h1, h3, h5]
        · have hx2' : D₂ / (16 * D₁) < 2 := not_le.mp hx2
          have h32 : D₂ ≤ 32 * D₁ := by
            rw [div_lt_iff₀ (by positivity : (0:ℝ) < 16*D₁)] at hx2'
            linarith
          nlinarith [hk1R, h32, hD₁pos]
      set Nk : ℕ := k * (Mnat + 1) with hNkdef
      have hNkR : ((Nk:ℝ)) = (k:ℝ) * L := by
        rw [hNkdef, hLM]; push_cast; ring
      have hNk1 : 1 ≤ Nk := by
        rw [hNkdef]
        exact Nat.one_le_iff_ne_zero.mpr (by positivity)
      have hXcard : D₂ / 4 * (2 * (Nk:ℝ) + 1) ≤ ((sumsetAux k T₀).card : ℝ) := by
        have h1 : (k:ℝ) * (T₀.card : ℝ) ≤ ((sumsetAux k T₀).card : ℝ) + ((k:ℝ) - 1) := by
          have h2 := card_sumsetAux_ge T₀ hT₀ne k hk1
          have h3 : ((k * T₀.card : ℕ) : ℝ) ≤ (((sumsetAux k T₀).card + (k - 1) : ℕ) : ℝ) := by
            exact_mod_cast h2
          rw [Nat.cast_mul, Nat.cast_add, Nat.cast_sub hk1] at h3
          push_cast at h3
          linarith [h3]
        have h2 : (k:ℝ) * (D₂ * (2*L+1)) ≤ (k:ℝ) * (T₀.card : ℝ) :=
          mul_le_mul_of_nonneg_left hTdens (le_of_lt hkpos)
        rw [hNkR]
        nlinarith [h1, h2, hD₂le1, hD₂L2, hk1R]
      have hXabs : ∀ x ∈ sumsetAux k T₀, |(x:ℝ)| ≤ (k:ℝ) * L := by
        intro x hx
        have h1 := sumsetAux_abs_le T₀ (Mnat:ℝ) k hTabs x hx
        have h2 : (Mnat:ℝ) ≤ L := by linarith [hLM]
        nlinarith [h1, h2, hkpos.le]
      have hXrange : ∀ x ∈ sumsetAux k T₀, -((Nk:ℤ)) ≤ x ∧ x ≤ (Nk:ℤ) := by
        intro x hx
        have h1 : |(x:ℝ)| ≤ ((Nk:ℝ)) := by rw [hNkR]; exact hXabs x hx
        have h2 := abs_le.mp h1
        exact ⟨by exact_mod_cast h2.1, by exact_mod_cast h2.2⟩
      have hXclose : ∀ x ∈ sumsetAux k T₀, ∃ m : ℤ, |((q:ℝ)*β) * (x:ℝ) - (m:ℝ)| ≤ (k:ℝ) * D₁ := by
        have h1 : ∀ t ∈ T₀, ∃ m : ℤ, |((q:ℝ)*β) * (t:ℝ) - (m:ℝ)| ≤ D₁ := by
          intro t ht
          rw [hT₀def] at ht
          obtain ⟨htH, htq⟩ := Finset.mem_filter.mp ht
          obtain ⟨m, hm⟩ := hper t htH
          refine ⟨m, ?_⟩
          have h2 : ((q:ℝ)*β) * (t:ℝ) = (qf t : ℝ) * (t:ℝ) * β := by rw [htq]; ring
          rw [h2]; exact hm
        intro x hx
        exact sumsetAux_close T₀ ((q:ℝ)*β) D₁ k h1 x hx
      have hkD₁pos : 0 < (k:ℝ) * D₁ := by positivity
      have hkD₁le : (k:ℝ) * D₁ ≤ (D₂/4) / 4 := by
        have h2 : (k:ℝ) ≤ D₂ / (16 * D₁) := by
          rw [hkdef]; exact Nat.floor_le (by positivity)
        have h3 : (k:ℝ) * D₁ ≤ D₂ / (16 * D₁) * D₁ :=
          mul_le_mul_of_nonneg_right h2 (le_of_lt hD₁pos)
        have h4 : D₂ / (16 * D₁) * D₁ = D₂ / 16 := by field_simp; try ring
        have h5 : (D₂/4)/4 = D₂/16 := by ring
        linarith [h3, h4, h5]
      have hD₂fourle : D₂ / 4 ≤ 1 := by linarith [hD₂le1]
      obtain ⟨qnew, hqnew1, hqnewle, a', ha'⟩ :=
        hDensestmt ((q:ℝ)*β) ((k:ℝ)*D₁) (D₂/4) Nk (sumsetAux k T₀)
          hNk1 hkD₁pos (by positivity) hD₂fourle hkD₁le hXrange hXcard hXclose
      refine ⟨qnew * q, ?_, ?_, a', ?_⟩
      · have h1 : 0 < qnew := lt_of_lt_of_le zero_lt_one hqnew1
        have h2 : 0 < q := lt_of_lt_of_le zero_lt_one hq1
        exact Nat.succ_le_of_lt (Nat.mul_pos h1 h2)
      · have h1 : (qnew:ℝ) ≤ 32/D₂ := by
          have h2 := hqnewle
          rw [show (8:ℝ) / (D₂/4) = 32/D₂ by ring] at h2
          exact h2
        have hprod : (qnew:ℝ) * (q:ℝ) ≤ (32/D₂) * Q₀ :=
          mul_le_mul h1 hqQ₀ (by positivity) (by positivity)
        have heq : (32/D₂) * Q₀ = 192*Q₀^2/S := by rw [hD₂def]; field_simp; ring
        calc (((qnew * q : ℕ)) : ℝ) = (qnew:ℝ) * (q:ℝ) := by push_cast; ring
          _ ≤ (32/D₂) * Q₀ := hprod
          _ = 192*Q₀^2/S := heq
          _ ≤ M * S ^ (-M) := hA3
      · have hbound : |(qnew:ℝ) * ((q:ℝ)*β) - (a':ℝ)| ≤ 16384*C₀*D₁/(D₂^4*L) := by
          have h7 : (qnew:ℝ) * ((q:ℝ)*β - (a':ℝ)/(qnew:ℝ))
              = (qnew:ℝ)*((q:ℝ)*β) - (a':ℝ) := by
            field_simp
          have h8 : |(qnew:ℝ) * ((q:ℝ)*β) - (a':ℝ)|
              = (qnew:ℝ) * |(q:ℝ)*β - (a':ℝ)/(qnew:ℝ)| := by
            rw [← h7, abs_mul, abs_of_nonneg (by positivity)]
          rw [h8]
          have h1 : (qnew:ℝ) ≤ 32/D₂ := by
            have h2 := hqnewle
            rw [show (8:ℝ) / (D₂/4) = 32/D₂ by ring] at h2
            exact h2
          have h6 : (32/D₂) * (C₀ / ((D₂/4)^2 * ((k:ℝ)*L))) ≤ 16384*C₀*D₁/(D₂^4*L) := by
            have h5 : 512*C₀/(D₂^3*(k:ℝ)*L) ≤ 16384*C₀*D₁/(D₂^4*L) := by
              rw [div_le_div_iff₀ (by positivity) (by positivity)]
              rw [show 512*C₀ * (D₂^4*L) = (512*D₂) * (C₀*D₂^3*L) by ring,
                  show 16384*C₀*D₁ * (D₂^3*(k:ℝ)*L) = (16384*D₁*(k:ℝ)) * (C₀*D₂^3*L) by ring]
              have hk' : 512 * D₂ ≤ 16384 * D₁ * (k:ℝ) := by nlinarith [hkD₂]
              exact mul_le_mul_of_nonneg_right hk' (by positivity)
            have h6' : (32/D₂) * (C₀ / ((D₂/4)^2 * ((k:ℝ)*L))) = 512*C₀/(D₂^3*(k:ℝ)*L) := by
              field_simp
              ring
            rw [h6']; exact h5
          calc (qnew:ℝ) * |(q:ℝ)*β - (a':ℝ)/(qnew:ℝ)|
              ≤ (qnew:ℝ) * (C₀ / ((D₂/4)^2 * (Nk:ℝ))) :=
                mul_le_mul_of_nonneg_left ha' (by positivity)
            _ ≤ (32/D₂) * (C₀ / ((D₂/4)^2 * (Nk:ℝ))) :=
                mul_le_mul_of_nonneg_right h1 (by positivity)
            _ = (32/D₂) * (C₀ / ((D₂/4)^2 * ((k:ℝ)*L))) := by rw [hNkR]
            _ ≤ 16384*C₀*D₁/(D₂^4*L) := h6
        calc |(((qnew * q : ℕ)) : ℝ) * β - (a':ℝ)|
            = |(qnew:ℝ) * ((q:ℝ)*β) - (a':ℝ)| := by congr 1; push_cast; ring
          _ ≤ 16384*C₀*D₁/(D₂^4*L) := hbound
          _ ≤ M * S ^ (-M) / L ^ (d+1) := by
              have heq : 16384*C₀*D₁/(D₂^4*L) = 16384*1296*C₀*Q₀^5/(S^(d+4)*L^(d+1)) := by
                rw [hD₁def, hD₂def, div_pow, mul_pow, mul_pow]
                rw [show (6:ℝ)^4 = 1296 by norm_num]
                rw [show S^(d+4) = S^d * S^4 from pow_add S d 4]
                rw [show L^(d+1) = L^d * L from pow_succ L d]
                field_simp
                try ring
              rw [heq]
              have hfin : 16384*1296*C₀*Q₀^5/(S^(d+4)*L^(d+1))
                  = (16384*1296*C₀*Q₀^5/S^(d+4))/L^(d+1) := by
                field_simp
                try ring
              rw [hfin]
              exact div_le_div_of_nonneg_right hA4 (by positivity)
  obtain ⟨q', hq'1, hq'M, m', hm'⟩ := hcore
  have hSpow : S ^ (-M) = 64 ^ M * ε ^ (-(2*M)) := by
    rw [hSdef]
    exact div64_rpow_neg hε0 M
  refine ⟨(d + 1) * q', ?_, ?_, m', ?_⟩
  · have h1 : 0 < q' := lt_of_lt_of_le zero_lt_one hq'1
    exact Nat.succ_le_of_lt (Nat.mul_pos (Nat.succ_pos d) h1)
  · have h1 : (((d+1:ℕ):ℝ)) * (q':ℝ) ≤ (((d+1:ℕ):ℝ)) * (M * S ^ (-M)) :=
      mul_le_mul_of_nonneg_left hq'M (by positivity)
    calc (((d + 1) * q' : ℕ) : ℝ) = (((d+1:ℕ):ℝ)) * (q':ℝ) := by push_cast; ring
      _ ≤ (((d+1:ℕ):ℝ)) * (M * S ^ (-M)) := h1
      _ = (((d:ℝ)+1) * M * 64^M) * ε ^ (-(2*M)) := by rw [hSpow]; push_cast; ring
  · have h3 : (M:ℝ) * (64 ^ M * ε ^ (-(2*M))) ≤ (((d:ℝ)+1) * M) * (64 ^ M * ε ^ (-(2*M))) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      nlinarith [hM1, Nat.cast_nonneg (α := ℝ) d]
    calc |(((d + 1) * q' : ℕ) : ℝ) * ξ * cc - (m':ℝ)|
        = |(q':ℝ) * β - (m':ℝ)| := by congr 1; simp only [hβdef, hccdef]; push_cast; ring
      _ ≤ M * S ^ (-M) / L ^ (d+1) := hm'
      _ ≤ (((d:ℝ)+1) * M * 64^M) * ε ^ (-(2*M)) / L ^ (d+1) := by
          rw [hSpow]
          apply div_le_div_of_nonneg_right _ (by positivity)
          calc M * (64 ^ M * ε ^ (-(2*M))) ≤ (((d:ℝ)+1) * M) * (64 ^ M * ε ^ (-(2*M))) := h3
            _ = ((d:ℝ)+1) * M * (64 ^ M * ε ^ (-(2*M))) := by ring
            _ = (((d:ℝ)+1) * M * 64^M) * ε ^ (-(2*M)) := by ring

end Work.KMTAreas.A4
