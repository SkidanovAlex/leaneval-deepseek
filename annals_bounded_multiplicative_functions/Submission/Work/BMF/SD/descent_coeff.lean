import Mathlib
import Submission.Work.BMF.SD.pin_lemma
import Submission.Work.BMF.SD.tail_bound
import Submission.Work.BMF.SD.small_multiple

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The coefficient descent

Given the "many point" near-integrality hypotheses
`q * Σ_{j > i} binom(j,i) a_j d^{j-i} ∈ ℤ + O(C/(L-d)^i)` for all `d ∈ D` (a `δ₄`-dense set)
and all `i ∈ [1,k]`, we produce a bounded modulus `Q` with `Q * a_j ∈ ℤ + O(Q/L^j)` for
`j ∈ [2,k+1]`.
-/

set_option maxHeartbeats 2000000

namespace Work.BMF.SD

open Finset

noncomputable def PinB (k : ℕ) : ℝ := ((k : ℝ) + 2) * (2 : ℝ) ^ (k + 1)

noncomputable def D1b (δ₁ : ℝ) : ℝ := max 1 (1 / δ₁)

def Pinned (k L : ℕ) (x : ℕ → ℝ) (m : ℕ) (H : ℕ) (K : ℝ) (M : ℕ → ℤ) : Prop :=
  1 ≤ H ∧ 0 ≤ K ∧
    ∀ j ∈ Finset.Icc (m + 1) (k + 1), |(H : ℝ) * x j - (M j : ℝ)| ≤ K / (L : ℝ) ^ j

lemma sum_Icc_succ_bot {M : Type*} [AddCommMonoid M] (f : ℕ → M) {m k : ℕ} (hmk : m ≤ k) :
    ∑ j ∈ Finset.Icc (m + 1) (k + 1), f j = f (m + 1) + ∑ j ∈ Finset.Icc (m + 2) (k + 1), f j := by
  have hidx : Finset.Icc (m + 1) (k + 1) = insert (m + 1) (Finset.Icc (m + 2) (k + 1)) := by
    ext j
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  have hnot : (m + 1) ∉ Finset.Icc (m + 2) (k + 1) := by
    simp only [Finset.mem_Icc]; omega
  rw [hidx, Finset.sum_insert hnot]

noncomputable def Zpart (M : ℕ → ℤ) (m k d : ℕ) : ℤ :=
  ∑ j ∈ Finset.Icc (m + 2) (k + 1), ((j.choose m : ℕ) : ℤ) * M j * ((d : ℤ) ^ (j - m))

end Work.BMF.SD

namespace Work.BMF.SD

open Finset

lemma step_lemma (k : ℕ) (L q : ℕ) (hL : 1 ≤ L) (D : Finset ℕ) (a : ℕ → ℝ)
    (C δ₁ : ℝ) (hC : 0 < C) (hδ₁ : 0 < δ₁)
    (hDm : ∀ d ∈ D, 1 ≤ d ∧ δ₁ * (L : ℝ) ≤ ((L - d : ℕ) : ℝ))
    (hdle : ∀ d ∈ D, d ≤ L)
    (hHyp : ∀ d ∈ D, ∀ i ∈ Finset.Icc 1 k, ∃ m : ℤ,
        |(q : ℝ) * (∑ j ∈ Finset.Icc (i + 1) (k + 1),
            a j * (d : ℝ) ^ (j - i) * ((j.choose i : ℕ) : ℝ)) - m|
          ≤ C / (((L - d : ℕ)) : ℝ) ^ i)
    {m : ℕ} (hm1 : 1 ≤ m) (hmk : m ≤ k)
    {H : ℕ} {K : ℝ} {M : ℕ → ℤ}
    (hpin : Pinned k L (fun j => (q:ℝ)*a j) (m+1) H K M)
    {Qb Eb : ℝ} (hQb : 1 ≤ Qb) (hEb : 0 ≤ Eb)
    (oracle : (∀ d ∈ D, ∃ z : ℤ, |(((m:ℝ)+1) * ((H:ℝ) * ((q:ℝ)*a (m+1)))) * (d:ℝ) - z| ≤
        H*C/(δ₁*(L:ℝ))^m + PinB k*K/(L:ℝ)^m) →
      ∃ r : ℕ, 1 ≤ r ∧ (r:ℝ) ≤ Qb ∧ ∃ z : ℤ,
        |(r:ℝ) * (((m:ℝ)+1) * ((H:ℝ) * ((q:ℝ)*a (m+1)))) - z| ≤
          Eb * (H*C*(D1b δ₁)^k + PinB k*K)/(L:ℝ)^m)
    : ∃ H' K' M', Pinned k L (fun j => (q:ℝ)*a j) m H' K' M' ∧
        (H':ℝ) ≤ Qb * ((m:ℝ)+1) * H ∧
        K' ≤ max (Eb * (H*C*(D1b δ₁)^k + PinB k*K) * (L:ℝ)) (Qb*((m:ℝ)+1)*K) := by
  obtain ⟨hH1, hK0, hM⟩ := hpin
  have hLpos : (0:ℝ) < (L:ℝ) := by exact_mod_cast (by omega : 0 < L)
  have hδLpos : (0:ℝ) < δ₁ * (L:ℝ) := mul_pos hδ₁ hLpos
  set ε : ℝ := H*C/(δ₁*(L:ℝ))^m + PinB k*K/(L:ℝ)^m with hε
  have hPinB : (0:ℝ) ≤ PinB k := by
    rw [PinB]; positivity
  have hε0 : 0 ≤ ε := by
    rw [hε]; positivity
  -- the good-set hypothesis
  have hgood : ∀ d ∈ D, ∃ z : ℤ, |(((m:ℝ)+1) * ((H:ℝ) * ((q:ℝ)*a (m+1)))) * (d:ℝ) - z| ≤ ε := by
    intro d hd
    obtain ⟨hd1, hdLd⟩ := hDm d hd
    have hdL : d ≤ L := hdle d hd
    obtain ⟨n, hn⟩ := hHyp d hd m (by simp [Finset.mem_Icc, hm1, hmk])
    have hxq : (q:ℝ) * (∑ j ∈ Finset.Icc (m+1) (k+1), a j * (d:ℝ)^(j-m) * ((j.choose m : ℕ):ℝ))
        = ∑ j ∈ Finset.Icc (m+1) (k+1), ((q:ℝ)*a j) * (d:ℝ)^(j-m) * ((j.choose m : ℕ):ℝ) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun j _ => by ring)
    rw [hxq] at hn
    rw [sum_Icc_succ_bot (fun j => ((q:ℝ)*a j) * (d:ℝ)^(j-m) * ((j.choose m : ℕ):ℝ)) hmk] at hn
    have hfirst : ((q:ℝ)*a (m+1)) * (d:ℝ)^(m+1-m) * (((m+1).choose m : ℕ):ℝ)
        = ((m:ℝ)+1) * ((q:ℝ)*a (m+1)) * d := by
      rw [Nat.choose_succ_self_right]
      have h1 : m + 1 - m = 1 := by omega
      rw [h1]
      push_cast
      ring
    rw [hfirst] at hn
    have htail := tail_bound (k := k) (m := m) (L := L) (x := fun j => (q:ℝ)*a j) hH1
      (K := K) hK0 (M := M) hdL
      (fun j hj => hM j (Finset.mem_Icc.mpr ⟨by
        have h := (Finset.mem_Icc.mp hj).1
        omega, (Finset.mem_Icc.mp hj).2⟩))
    set Z : ℤ := Zpart M m k d with hZ
    have hZcast : ((Z : ℤ) : ℝ)
        = ∑ j ∈ Finset.Icc (m+2) (k+1), ((j.choose m : ℕ):ℝ) * (M j : ℝ) * (d:ℝ)^(j-m) := by
      rw [hZ, Zpart]
      push_cast
      exact Finset.sum_congr rfl (fun j _ => by ring)
    have htail' : |(∑ j ∈ Finset.Icc (m+2) (k+1), ((q:ℝ)*a j) * (d:ℝ)^(j-m) * ((j.choose m : ℕ):ℝ))
        - (Z:ℝ)/(H:ℝ)| ≤ PinB k*K/((H:ℝ)*(L:ℝ)^m) := by
      have h1 : (∑ j ∈ Finset.Icc (m+2) (k+1), ((q:ℝ)*a j) * (d:ℝ)^(j-m) * ((j.choose m : ℕ):ℝ))
          = ∑ j ∈ Finset.Icc (m+2) (k+1), ((j.choose m : ℕ):ℝ) * ((q:ℝ)*a j) * (d:ℝ)^(j-m) :=
        Finset.sum_congr rfl (fun j _ => by ring)
      rw [h1, hZcast]
      exact htail
    refine ⟨H*n - Z, ?_⟩
    have hExp : (((m:ℝ)+1) * ((H:ℝ) * ((q:ℝ)*a (m+1)))) * (d:ℝ) - (((H:ℝ)*(n:ℝ) - (Z:ℝ) : ℝ))
        = (H:ℝ) * (((m:ℝ)+1) * ((q:ℝ)*a (m+1)) * (d:ℝ)
            + (∑ j ∈ Finset.Icc (m+2) (k+1), ((q:ℝ)*a j) * (d:ℝ)^(j-m) * ((j.choose m : ℕ):ℝ))
            - (n:ℝ))
          - ((H:ℝ) * (∑ j ∈ Finset.Icc (m+2) (k+1), ((q:ℝ)*a j) * (d:ℝ)^(j-m) * ((j.choose m : ℕ):ℝ))
            - (Z:ℝ)) := by ring
    rw [show (((m:ℝ)+1) * ((H:ℝ) * ((q:ℝ)*a (m+1)))) * (d:ℝ) - ((↑(↑H * n - Z) : ℤ) : ℝ)
        = (((m:ℝ)+1) * ((H:ℝ) * ((q:ℝ)*a (m+1)))) * (d:ℝ) - ((H:ℝ)*(n:ℝ) - (Z:ℝ)) by push_cast; ring]
    rw [hExp]
    have hstep1 : |(H:ℝ) * (((m:ℝ)+1) * ((q:ℝ)*a (m+1)) * (d:ℝ)
            + (∑ j ∈ Finset.Icc (m+2) (k+1), ((q:ℝ)*a j) * (d:ℝ)^(j-m) * ((j.choose m : ℕ):ℝ))
            - (n:ℝ))| ≤ (H:ℝ) * (C / (((L - d : ℕ)) : ℝ)^m) := by
      rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (H:ℝ))]
      exact mul_le_mul_of_nonneg_left hn (by positivity)
    have hHne : (H:ℝ) ≠ 0 := by positivity
    have hstep2 : |(H:ℝ) * (∑ j ∈ Finset.Icc (m+2) (k+1), ((q:ℝ)*a j) * (d:ℝ)^(j-m) * ((j.choose m : ℕ):ℝ))
        - (Z:ℝ)| ≤ PinB k*K/(L:ℝ)^m := by
      have hEq : (H:ℝ) * (∑ j ∈ Finset.Icc (m+2) (k+1), ((q:ℝ)*a j) * (d:ℝ)^(j-m) * ((j.choose m : ℕ):ℝ)) - (Z:ℝ)
          = (H:ℝ) * ((∑ j ∈ Finset.Icc (m+2) (k+1), ((q:ℝ)*a j) * (d:ℝ)^(j-m) * ((j.choose m : ℕ):ℝ))
              - (Z:ℝ)/(H:ℝ)) := by
        rw [mul_sub, mul_div_cancel₀ _ hHne]
      rw [hEq, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (H:ℝ))]
      calc (H:ℝ) * |(∑ j ∈ Finset.Icc (m+2) (k+1), ((q:ℝ)*a j) * (d:ℝ)^(j-m) * ((j.choose m : ℕ):ℝ))
            - (Z:ℝ)/(H:ℝ)|
          ≤ (H:ℝ) * (PinB k*K/((H:ℝ)*(L:ℝ)^m)) := mul_le_mul_of_nonneg_left htail' (by positivity)
        _ = PinB k*K/(L:ℝ)^m := by
            simp only [PinB]
            field_simp
    calc |(H:ℝ) * (((m:ℝ)+1) * ((q:ℝ)*a (m+1)) * (d:ℝ)
            + (∑ j ∈ Finset.Icc (m+2) (k+1), ((q:ℝ)*a j) * (d:ℝ)^(j-m) * ((j.choose m : ℕ):ℝ))
            - (n:ℝ))
          - ((H:ℝ) * (∑ j ∈ Finset.Icc (m+2) (k+1), ((q:ℝ)*a j) * (d:ℝ)^(j-m) * ((j.choose m : ℕ):ℝ)) - (Z:ℝ))|
        ≤ (H:ℝ) * (C / (((L - d : ℕ)) : ℝ)^m) + PinB k*K/(L:ℝ)^m :=
          le_trans (by
              have h := abs_sub_le (((H:ℝ) * (((m:ℝ)+1) * ((q:ℝ)*a (m+1)) * (d:ℝ)
                + (∑ j ∈ Finset.Icc (m+2) (k+1), ((q:ℝ)*a j) * (d:ℝ)^(j-m) * ((j.choose m : ℕ):ℝ))
                - (n:ℝ)))) 0
                ((H:ℝ) * (∑ j ∈ Finset.Icc (m+2) (k+1), ((q:ℝ)*a j) * (d:ℝ)^(j-m) * ((j.choose m : ℕ):ℝ)) - (Z:ℝ))
              rw [sub_zero, zero_sub, abs_neg] at h
              exact h) (add_le_add hstep1 hstep2)
      _ ≤ H*C/(δ₁*(L:ℝ))^m + PinB k*K/(L:ℝ)^m := by
          have h1 : (H:ℝ) * (C / (((L - d : ℕ)) : ℝ)^m) = H*C/(((L - d : ℕ)) : ℝ)^m := by
            rw [mul_div_assoc]
          rw [h1]
          have h2 : H*C/(((L - d : ℕ)) : ℝ)^m ≤ H*C/(δ₁*(L:ℝ))^m := by
            apply div_le_div_of_nonneg_left (by positivity) (pow_pos hδLpos m)
            exact pow_le_pow_left₀ (le_of_lt hδLpos) hdLd m
          linarith
      _ = ε := by rw [hε]
  obtain ⟨r, hr1, hrQb, z, hrz⟩ := oracle hgood
  refine ⟨r * ((m+1) * H), max (Eb * (H*C*(D1b δ₁)^k + PinB k*K) * (L:ℝ)) (Qb*((m:ℝ)+1)*K),
      (fun j => if j = m+1 then z else ((r : ℤ) * ((m+1 : ℕ) : ℤ)) * M j), ?_, ?_, ?_⟩
  · have hb2 : 0 ≤ Qb*((m:ℝ)+1)*K := by
      have h1 : (0:ℝ) ≤ Qb := by linarith
      have h2 : (0:ℝ) ≤ (m:ℝ)+1 := by positivity
      exact mul_nonneg (mul_nonneg h1 h2) hK0
    have hb1 : 0 ≤ Eb * (H*C*(D1b δ₁)^k + PinB k*K) * (L:ℝ) := by
      have hD1p : (0:ℝ) < D1b δ₁ := by rw [D1b]; positivity
      have h1a : (0:ℝ) ≤ H*C*(D1b δ₁)^k :=
        mul_nonneg (mul_nonneg (Nat.cast_nonneg H) (le_of_lt hC)) (pow_nonneg (le_of_lt hD1p) k)
      have h1b : (0:ℝ) ≤ PinB k*K := mul_nonneg hPinB hK0
      have h1 : (0:ℝ) ≤ H*C*(D1b δ₁)^k + PinB k*K := add_nonneg h1a h1b
      have hLnn : (0:ℝ) ≤ (L:ℝ) := Nat.cast_nonneg L
      exact mul_nonneg (mul_nonneg hEb h1) hLnn
    have hK'0 : 0 ≤ max (Eb * (H*C*(D1b δ₁)^k + PinB k*K) * (L:ℝ)) (Qb*((m:ℝ)+1)*K) :=
      le_max_of_le_left hb1
    have hH'1 : 1 ≤ r * ((m+1) * H) := by
      have h1 : 0 < r := by omega
      have h2 : 0 < m + 1 := by omega
      have h3 : 0 < H := by omega
      have := Nat.mul_pos h1 (Nat.mul_pos h2 h3)
      omega
    refine ⟨hH'1, hK'0, ?_⟩
    intro j hj
    rw [Finset.mem_Icc] at hj
    rcases eq_or_lt_of_le hj.1 with hjm | hjm
    · subst hjm
      dsimp only
      rw [if_pos rfl]
      have hHcast : ((r * ((m+1)*H) : ℕ) : ℝ) * ((q:ℝ)*a (m+1))
          = (r:ℝ) * (((m:ℝ)+1) * ((H:ℝ) * ((q:ℝ)*a (m+1)))) := by push_cast; ring
      rw [hHcast, le_div_iff₀ (by positivity : (0:ℝ) < (L:ℝ)^(m+1))]
      calc |(r:ℝ) * (((m:ℝ)+1) * ((H:ℝ) * ((q:ℝ)*a (m+1)))) - (z:ℝ)| * (L:ℝ)^(m+1)
          ≤ (Eb * (H*C*(D1b δ₁)^k + PinB k*K)/(L:ℝ)^m) * (L:ℝ)^(m+1) :=
            mul_le_mul_of_nonneg_right hrz (by positivity)
        _ = Eb * (H*C*(D1b δ₁)^k + PinB k*K) * (L:ℝ) := by
            rw [pow_succ]
            field_simp
        _ ≤ max (Eb * (H*C*(D1b δ₁)^k + PinB k*K) * (L:ℝ)) (Qb*((m:ℝ)+1)*K) := le_max_left _ _
    · have hjm2 : m + 2 ≤ j := by omega
      have hM' : (if j = m+1 then z else ((r : ℤ) * ((m+1 : ℕ) : ℤ)) * M j) = ((r : ℤ) * ((m+1 : ℕ) : ℤ)) * M j := by
        rw [if_neg (by omega : ¬ (j = m + 1))]
      dsimp only
      rw [hM']
      have hHcast : ((r * ((m+1)*H) : ℕ) : ℝ) * ((q:ℝ)*a j)
          = (r:ℝ) * ((m:ℝ)+1) * ((H:ℝ) * ((q:ℝ)*a j)) := by push_cast; ring
      have hMc : ((((r:ℤ) * ((m+1:ℕ):ℤ)) * M j : ℤ) : ℝ) = (r:ℝ) * ((m:ℝ)+1) * (M j : ℝ) := by
        push_cast; ring
      rw [hHcast, hMc]
      have hM2 : |(H:ℝ) * ((q:ℝ)*a j) - (M j : ℝ)| ≤ K / (L:ℝ)^j :=
        hM j (Finset.mem_Icc.mpr ⟨by omega, hj.2⟩)
      have hfac : (0:ℝ) ≤ (r:ℝ) * ((m:ℝ)+1) := by positivity
      have hprod : |(r:ℝ) * ((m:ℝ)+1) * ((H:ℝ) * ((q:ℝ)*a j)) - (r:ℝ) * ((m:ℝ)+1) * (M j : ℝ)|
          = (r:ℝ) * ((m:ℝ)+1) * |(H:ℝ) * ((q:ℝ)*a j) - (M j : ℝ)| := by
        rw [← mul_sub, abs_mul, abs_of_nonneg hfac]
      rw [hprod]
      have h1 : (r:ℝ) * ((m:ℝ)+1) ≤ Qb * ((m:ℝ)+1) :=
        mul_le_mul_of_nonneg_right hrQb (by positivity)
      calc (r:ℝ) * ((m:ℝ)+1) * |(H:ℝ) * ((q:ℝ)*a j) - (M j : ℝ)|
          ≤ (Qb * ((m:ℝ)+1)) * (K / (L:ℝ)^j) :=
            mul_le_mul h1 hM2 (abs_nonneg _) (by positivity)
        _ = Qb * ((m:ℝ)+1) * (K / (L:ℝ)^j) := by ring
        _ ≤ max (Eb * (H*C*(D1b δ₁)^k + PinB k*K) * (L:ℝ)) (Qb*((m:ℝ)+1)*K) / (L:ℝ)^j := by
            rw [le_div_iff₀ (by positivity : (0:ℝ) < (L:ℝ)^j)]
            have h2 : Qb * ((m:ℝ)+1) * (K / (L:ℝ)^j) * (L:ℝ)^j = Qb * ((m:ℝ)+1) * K := by
              field_simp
            rw [h2]
            exact le_max_right _ _
  · have hcast2 : ((r * ((m+1) * H) : ℕ) : ℝ) = (r:ℝ) * ((m:ℝ)+1) * (H:ℝ) := by push_cast; ring
    rw [hcast2]
    calc (r:ℝ) * ((m:ℝ)+1) * (H:ℝ) ≤ Qb * ((m:ℝ)+1) * (H:ℝ) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hrQb (by positivity)) (by positivity)
      _ = Qb * ((m:ℝ)+1) * H := by ring
  · exact le_rfl

end Work.BMF.SD

namespace Work.BMF.SD

open Finset

theorem descent_ind (k : ℕ) (hk : 1 ≤ k) (L q : ℕ) (hL : 1 ≤ L) (D : Finset ℕ) (a : ℕ → ℝ)
    (C δ₁ δ₄ Qb Eb V B0 : ℝ) (hC : 0 < C) (hδ₁ : 0 < δ₁) (hδ₄ : 0 < δ₄)
    (hDc : δ₄ * (L : ℝ) ≤ (D.card : ℝ))
    (hDm : ∀ d ∈ D, 1 ≤ d ∧ δ₁ * (L : ℝ) ≤ ((L - d : ℕ) : ℝ))
    (hHyp : ∀ d ∈ D, ∀ i ∈ Finset.Icc 1 k, ∃ m : ℤ,
        |(q : ℝ) * (∑ j ∈ Finset.Icc (i + 1) (k + 1),
            a j * (d : ℝ) ^ (j - i) * ((j.choose i : ℕ) : ℝ)) - m|
          ≤ C / (((L - d : ℕ)) : ℝ) ^ i)
    (hQb : 1 ≤ Qb) (hEb : 0 ≤ Eb) (hV : 1 ≤ V) (hB0 : 1 ≤ B0)
    (hB0a : Qb * ((k : ℝ) + 1) ≤ B0)
    (hB0b : Eb * C * (L : ℝ) * (D1b δ₁) ^ k ≤ B0)
    (hVa : 2 * (Qb * ((k : ℝ) + 1)) ≤ V)
    (hVb : 2 * Eb * (L : ℝ) * ((D1b δ₁) ^ k * C + PinB k) ≤ V)
    (oracle : ∀ (m : ℕ) (H : ℕ) (K β : ℝ) (M : ℕ → ℤ),
        1 ≤ m → m ≤ k →
        Pinned k L (fun j => (q : ℝ) * a j) (m + 1) H K M →
        max (H : ℝ) K ≤ (2 * V) ^ k * B0 →
        (∀ d ∈ D, ∃ z : ℤ, |β * (d : ℝ) - z| ≤
            H * C / (δ₁ * (L : ℝ)) ^ m + PinB k * K / (L : ℝ) ^ m) →
        ∃ r : ℕ, 1 ≤ r ∧ (r : ℝ) ≤ Qb ∧ ∃ z : ℤ,
          |(r : ℝ) * β - z| ≤ Eb * (H * C * (D1b δ₁) ^ k + PinB k * K) / (L : ℝ) ^ m)
    : ∃ H K M, Pinned k L (fun j => (q : ℝ) * a j) 1 H K M ∧
        max (H : ℝ) K ≤ B0 * (2 * V) ^ k := by
  have hdle : ∀ d ∈ D, d ≤ L := by
    intro d hd
    by_contra hcon
    push_neg at hcon
    obtain ⟨hd1, hdLd⟩ := hDm d hd
    have hz : ((L - d : ℕ) : ℝ) = 0 := by
      rw [Nat.sub_eq_zero_of_le (le_of_lt hcon)]
      simp
    rw [hz] at hdLd
    have hpos : (0:ℝ) < δ₁ * (L:ℝ) := by
      have : (0:ℝ) < (L:ℝ) := by exact_mod_cast (by omega : 0 < L)
      exact mul_pos hδ₁ this
    linarith
  have hPinB : (0:ℝ) ≤ PinB k := by rw [PinB]; positivity
  have hD1pos : (0:ℝ) < D1b δ₁ := by rw [D1b]; positivity
  have hD1 : (1:ℝ) ≤ D1b δ₁ := le_max_left _ _
  -- the induction
  have key : ∀ n, n ≤ k → ∃ H K M, Pinned k L (fun j => (q:ℝ)*a j) (k+1-n) H K M ∧
      max (H:ℝ) K ≤ B0 * (2*V)^n := by
    intro n hn
    induction n with
    | zero =>
      exact ⟨1, 0, fun _ => 0, ⟨le_rfl, le_rfl, by
          intro j hj
          exfalso
          rw [Finset.mem_Icc] at hj
          omega⟩, by
        rw [pow_zero, mul_one]
        simpa using hB0⟩
    | succ n ih =>
      obtain ⟨H, K, M, hpin, hbdd⟩ := ih (by omega)
      have hm1 : 1 ≤ k - n := by omega
      have hmk : k - n ≤ k := by omega
      have hpin' : Pinned k L (fun j => (q:ℝ)*a j) ((k-n)+1) H K M := by
        convert hpin using 3
        omega
      have hbdd2 : max (H:ℝ) K ≤ (2*V)^k * B0 := by
        refine le_trans hbdd ?_
        have h2V : (1:ℝ) ≤ 2*V := by linarith
        have hp : (2*V)^n ≤ (2*V)^k := pow_le_pow_right₀ h2V (by omega)
        calc B0 * (2*V)^n ≤ B0 * (2*V)^k := mul_le_mul_of_nonneg_left hp (by linarith)
          _ = (2*V)^k * B0 := by ring
      obtain ⟨H', K', M', hpin2, hH', hK'⟩ :=
        step_lemma k L q hL D a C δ₁ hC hδ₁ hDm hdle hHyp hm1 hmk hpin' hQb hEb
          (fun hgood => oracle (k-n) H K ((((k-n:ℕ):ℝ)+1) * ((H:ℝ) * ((q:ℝ)*a ((k-n)+1)))) M
            hm1 hmk hpin' hbdd2 hgood)
      refine ⟨H', K', M', ?_, ?_⟩
      · rw [show k + 1 - (n+1) = k - n from by omega]
        exact hpin2
      · have hVpos : (0:ℝ) < V := by linarith
        have hHH : (0:ℝ) ≤ (H:ℝ) := Nat.cast_nonneg H
        have hKK : (0:ℝ) ≤ K := hpin.2.1
        have hmaxnn : (0:ℝ) ≤ max (H:ℝ) K := le_max_of_le_left hHH
        have hQb' : Qb * (((k-n:ℕ):ℝ)+1) ≤ V/2 := by
          have hle : ((k-n:ℕ):ℝ) + 1 ≤ (k:ℝ)+1 := by
            have h1 : (k-n:ℕ) ≤ k := by omega
            have hc : ((k-n:ℕ):ℝ) ≤ (k:ℝ) := Nat.cast_le.mpr h1
            linarith
          nlinarith [hVa, hQb, hle, Nat.cast_nonneg (α := ℝ) (k-n)]
        have hH'max : (H':ℝ) ≤ V * max (H:ℝ) K := by
          calc (H':ℝ) ≤ Qb * (((k-n:ℕ):ℝ)+1) * H := hH'
            _ ≤ (V/2) * H := mul_le_mul_of_nonneg_right hQb' hHH
            _ ≤ V * max (H:ℝ) K := by
                calc (V/2) * (H:ℝ) ≤ (V/2) * max (H:ℝ) K :=
                      mul_le_mul_of_nonneg_left (le_max_left _ _) (by linarith)
                  _ ≤ V * max (H:ℝ) K := by
                      apply mul_le_mul_of_nonneg_right _ hmaxnn
                      linarith
        have hK'max : K' ≤ V * max (H:ℝ) K := by
          refine le_trans hK' (max_le ?_ ?_)
          · have hCD : (0:ℝ) ≤ C * (D1b δ₁)^k := mul_nonneg (le_of_lt hC) (pow_nonneg (le_of_lt hD1pos) k)
            have h1 : H*C*(D1b δ₁)^k ≤ (C*(D1b δ₁)^k) * max (H:ℝ) K := by
              have hm : H ≤ max (H:ℝ) K := le_max_left _ _
              have := mul_le_mul_of_nonneg_right hm hCD
              calc H*C*(D1b δ₁)^k = H * (C*(D1b δ₁)^k) := by ring
                _ ≤ max (H:ℝ) K * (C*(D1b δ₁)^k) := this
                _ = (C*(D1b δ₁)^k) * max (H:ℝ) K := by ring
            have h2 : PinB k*K ≤ PinB k * max (H:ℝ) K := by
              have hm : K ≤ max (H:ℝ) K := le_max_right _ _
              exact mul_le_mul_of_nonneg_left hm hPinB
            have h3 : H*C*(D1b δ₁)^k + PinB k*K
                ≤ (C*(D1b δ₁)^k + PinB k) * max (H:ℝ) K := by
              rw [add_mul]
              exact add_le_add h1 h2
            have h4 : (0:ℝ) ≤ Eb * (L:ℝ) := mul_nonneg hEb (Nat.cast_nonneg L)
            calc Eb * (H*C*(D1b δ₁)^k + PinB k*K) * (L:ℝ)
                ≤ Eb * ((C*(D1b δ₁)^k + PinB k) * max (H:ℝ) K) * (L:ℝ) := by
                  have h5 : (0:ℝ) ≤ (L:ℝ) := Nat.cast_nonneg L
                  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h3 hEb) h5
              _ = Eb * (L:ℝ) * ((D1b δ₁)^k * C + PinB k) * max (H:ℝ) K := by ring
              _ ≤ (V/2) * max (H:ℝ) K := by
                  have h6 : Eb * (L:ℝ) * ((D1b δ₁)^k * C + PinB k) ≤ V/2 := by linarith [hVb]
                  have h7 : (0:ℝ) ≤ max (H:ℝ) K := le_max_of_le_left hHH
                  exact mul_le_mul_of_nonneg_right h6 h7
              _ ≤ V * max (H:ℝ) K := by
                  apply mul_le_mul_of_nonneg_right _ hmaxnn
                  linarith
          · have hKKm : K ≤ max (H:ℝ) K := le_max_right _ _
            calc Qb * (((k-n:ℕ):ℝ)+1) * K ≤ (V/2) * K := mul_le_mul_of_nonneg_right hQb' hKK
              _ ≤ (V/2) * max (H:ℝ) K := mul_le_mul_of_nonneg_left hKKm (by linarith)
              _ ≤ V * max (H:ℝ) K := by
                  apply mul_le_mul_of_nonneg_right _ hmaxnn
                  linarith
        have hmax : max (H':ℝ) K' ≤ V * max (H:ℝ) K := max_le hH'max hK'max
        refine le_trans hmax ?_
        calc V * max (H:ℝ) K ≤ V * (B0 * (2*V)^n) := mul_le_mul_of_nonneg_left hbdd (le_of_lt hVpos)
          _ = B0 * (V * (2*V)^n) := by ring
          _ ≤ B0 * ((2*V)^n * (2*V)) := by
              apply mul_le_mul_of_nonneg_left _ (by linarith : (0:ℝ) ≤ B0)
              have h2n : (0:ℝ) ≤ (2*V)^n := pow_nonneg (by linarith : (0:ℝ) ≤ 2*V) n
              calc V * (2*V)^n ≤ (2*V) * (2*V)^n :=
                    mul_le_mul_of_nonneg_right (by linarith : V ≤ 2*V) h2n
                _ = (2*V)^n * (2*V) := by ring
          _ = B0 * (2*V)^(n+1) := by rw [pow_succ]
  obtain ⟨H, K, M, h1, h2⟩ := key k le_rfl
  exact ⟨H, K, M, by rwa [show k + 1 - k = 1 from by omega] at h1, h2⟩

end Work.BMF.SD

namespace Work.BMF.SD

open Finset

/-- From `δ₁ * L ≤ L - d` and `δ₁ > 0` we get `d ≤ L`. -/
lemma le_of_pos_sub {L : ℕ} {δ₁ : ℝ} (hδ₁ : 0 < δ₁) (hL : 1 ≤ L) {d : ℕ}
    (hd : δ₁ * (L : ℝ) ≤ ((L - d : ℕ) : ℝ)) : d ≤ L := by
  by_contra hcon
  push_neg at hcon
  have hz : ((L - d : ℕ) : ℝ) = 0 := by
    rw [Nat.sub_eq_zero_of_le (le_of_lt hcon)]
    simp
  rw [hz] at hd
  have hpos : (0:ℝ) < δ₁ * (L:ℝ) := by
    have : (0:ℝ) < (L:ℝ) := by exact_mod_cast (by omega : 0 < L)
    exact mul_pos hδ₁ this
  linarith

/-- `D1b δ₁ ≥ 1`. -/
lemma one_le_D1b (δ₁ : ℝ) : (1:ℝ) ≤ D1b δ₁ := le_max_left _ _

/-- `D1b δ₁ > 0`. -/
lemma D1b_pos (δ₁ : ℝ) : (0:ℝ) < D1b δ₁ := by rw [D1b]; positivity

/-- `PinB k ≥ 0`. -/
lemma PinB_nonneg (k : ℕ) : (0:ℝ) ≤ PinB k := by rw [PinB]; positivity

/-- `(1/δ₁)^m ≤ (D1b δ₁)^k` for `m ≤ k`, `δ₁ > 0`. -/
lemma inv_pow_le {δ₁ : ℝ} (hδ₁ : 0 < δ₁) {m k : ℕ} (hm : m ≤ k) :
    (1/δ₁)^m ≤ (D1b δ₁)^k := by
  have h1 : (1/δ₁ : ℝ) ≤ D1b δ₁ := le_max_right _ _
  have h2 : (0:ℝ) ≤ 1/δ₁ := by positivity
  calc (1/δ₁)^m ≤ (D1b δ₁)^m := pow_le_pow_left₀ h2 h1 m
    _ ≤ (D1b δ₁)^k := pow_le_pow_right₀ (one_le_D1b δ₁) hm

/-- Scaled error bound: `H*C/(δ₁L)^m + PinB k*K/L^m ≤ (H*C*D1b δ₁^k + PinB k*K)/L^m`. -/
lemma scaled_error {C K H δ₁ L : ℝ} (hδ₁ : 0 < δ₁) (hC : 0 ≤ C) (hK : 0 ≤ K) (hH : 0 ≤ H)
    {m k : ℕ} (hm : m ≤ k) (hL : (0:ℝ) < L) :
    H*C/(δ₁*L)^m + PinB k*K/L^m ≤ (H*C*(D1b δ₁)^k + PinB k*K)/L^m := by
  have hLp : (0:ℝ) < L^m := pow_pos hL m
  have h1 : H*C/(δ₁*L)^m = (H*C/δ₁^m)/L^m := by
    rw [mul_pow, div_mul_eq_div_div]
  have h2 : H*C/δ₁^m ≤ H*C*(D1b δ₁)^k := by
    have hinv : (1/δ₁^m : ℝ) ≤ (D1b δ₁)^k := by
      have hii : (1/δ₁^m : ℝ) = (1/δ₁)^m := by rw [div_pow, one_pow]
      rw [hii]; exact inv_pow_le hδ₁ hm
    calc H*C/δ₁^m = (H*C) * (1/δ₁^m) := div_eq_mul_one_div _ _
      _ ≤ (H*C) * (D1b δ₁)^k := mul_le_mul_of_nonneg_left hinv (by positivity)
  calc H*C/(δ₁*L)^m + PinB k*K/L^m
      = (H*C/δ₁^m)/L^m + PinB k*K/L^m := by rw [h1]
    _ = (H*C/δ₁^m + PinB k*K)/L^m := by rw [← add_div]
    _ ≤ (H*C*(D1b δ₁)^k + PinB k*K)/L^m := by
        apply div_le_div_of_nonneg_right _ (le_of_lt hLp)
        exact add_le_add h2 le_rfl

/-- `(a / (b * L)) * L = a / b` for `L ≠ 0`. -/
lemma ebL (a b L : ℝ) (hL : L ≠ 0) : (a / (b * L)) * L = a / b := by
  rw [mul_comm b L, div_mul_eq_mul_div, mul_comm a L]
  exact mul_div_mul_left a b hL

end Work.BMF.SD

namespace Work.BMF.SD

open Finset

theorem descent_coeff (k : ℕ) (C C₀ δ₁ δ₄ : ℝ) (hC : 0 < C) (hC₀ : 1 ≤ C₀) (hδ₁ : 0 < δ₁)
    (hδ₄0 : 0 < δ₄) (hδ₄1 : δ₄ ≤ 1 / 2) :
    ∃ C' : ℝ, 0 < C' ∧ ∀ (L q : ℕ) (D : Finset ℕ) (a : ℕ → ℝ),
      2 ≤ L → 1 ≤ q → (q:ℝ) ≤ C₀ → 1 ≤ δ₁ * (L:ℝ) →
      C ≤ δ₄ ^ 2 * (δ₁ * (L:ℝ)) / 100 → δ₄ * (L:ℝ) ≤ (D.card : ℝ) →
      (∀ d ∈ D, 1 ≤ d ∧ δ₁ * (L:ℝ) ≤ ((L - d : ℕ) : ℝ)) →
      (∀ d ∈ D, ∀ i ∈ Finset.Icc 1 k, ∃ m : ℤ,
        |(q:ℝ) * (∑ j ∈ Finset.Icc (i+1) (k+1), a j * (d:ℝ)^(j-i) * ((j.choose i : ℕ):ℝ)) - m|
          ≤ C / (((L - d : ℕ)):ℝ)^i) →
      ∃ Q : ℕ, 1 ≤ Q ∧ (Q:ℝ) ≤ C' ∧
        ∀ j ∈ Finset.Icc 2 (k+1), ∃ m : ℤ, |(Q:ℝ)*a j - m| ≤ C'/(L:ℝ)^j := by
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · refine ⟨1, by norm_num, ?_⟩
    intro L q D a hL hq hqC hδ hCb hDc hDm hHyp
    refine ⟨1, le_rfl, by norm_num, ?_⟩
    intro j hj
    rw [Finset.mem_Icc] at hj
    exfalso
    omega
  obtain ⟨Kp, hKp0, hpin⟩ := pin_lemma
  set D1 : ℝ := D1b δ₁ with hD1def
  set Bk : ℝ := PinB k with hBkdef
  set QbB : ℝ := max Kp 4 / δ₄ with hQbB
  set k1 : ℝ := (k:ℝ) + 1 with hk1
  set B0B : ℝ := QbB * k1 + Kp * C * D1^k / δ₄^3 + 1 with hB0B
  set VB : ℝ := 2 * (QbB * k1) + 2 * Kp * (D1^k * C + Bk) / δ₄^3 + 1 with hVB
  set CB : ℝ := B0B * (2 * VB)^k with hCB
  set EE : ℝ := C * D1^k + Bk with hEE
  set L0 : ℝ := 36 * CB * EE / δ₄ with hL0
  set QbS : ℝ := 4 / δ₄ with hQbS
  set MS : ℝ := 2 * L0 + 1 with hMS
  set B0S : ℝ := QbS * k1 + MS * C * D1^k + 1 with hB0S
  set VS : ℝ := 2 * (QbS * k1) + 2 * MS * (D1^k * C + Bk) + 1 with hVS
  set CS : ℝ := B0S * (2 * VS)^k with hCS
  have hD1pos : (0:ℝ) < D1 := by rw [hD1def]; exact D1b_pos δ₁
  have h1D1 : (1:ℝ) ≤ D1 := by rw [hD1def]; exact one_le_D1b δ₁
  have hBk0 : (0:ℝ) ≤ Bk := by rw [hBkdef]; exact PinB_nonneg k
  have h3pos : (0:ℝ) < δ₄^3 := by positivity
  have h3ne : δ₄^3 ≠ 0 := ne_of_gt h3pos
  have hD1k : (0:ℝ) < D1^k := pow_pos hD1pos k
  have hCD1 : (0:ℝ) ≤ C * D1^k := mul_nonneg (le_of_lt hC) (le_of_lt hD1k)
  have hCD1pos : (0:ℝ) < C * D1^k := mul_pos hC hD1k
  have hEEpos : (0:ℝ) < EE := by rw [hEE]; linarith [hCD1pos, hBk0]
  have hEE0 : (0:ℝ) ≤ EE := le_of_lt hEEpos
  have hk1pos : (0:ℝ) < k1 := by rw [hk1]; positivity
  have hk10 : (0:ℝ) ≤ k1 := le_of_lt hk1pos
  have hQbB1 : (1:ℝ) ≤ QbB := by
    rw [hQbB]
    rw [le_div_iff₀ hδ₄0]
    have h : (1:ℝ) ≤ max Kp 4 := by
      have := le_max_right Kp (4:ℝ)
      linarith
    linarith
  have hQbB0 : (0:ℝ) ≤ QbB := le_of_lt (lt_of_lt_of_le one_pos hQbB1)
  have hB0B1 : (1:ℝ) ≤ B0B := by
    rw [hB0B]
    have h1 : (0:ℝ) ≤ QbB * k1 := mul_nonneg hQbB0 hk10
    have h2 : (0:ℝ) ≤ Kp * C * D1^k / δ₄^3 := by positivity
    linarith
  have hVB1 : (1:ℝ) ≤ VB := by
    rw [hVB]
    have h1 : (0:ℝ) ≤ 2 * (QbB * k1) := by positivity
    have h2 : (0:ℝ) ≤ 2 * Kp * (D1^k * C + Bk) / δ₄^3 := by positivity
    linarith
  have hCB1 : (1:ℝ) ≤ CB := by
    rw [hCB]
    have h2V : (1:ℝ) ≤ 2 * VB := by linarith [hVB1]
    have h : (1:ℝ) ≤ (2*VB)^k := one_le_pow₀ h2V
    nlinarith [hB0B1, h, mul_le_mul hB0B1 h (by norm_num) (le_of_lt (lt_of_lt_of_le one_pos hB0B1))]
  have hCB0 : (0:ℝ) ≤ CB := le_of_lt (lt_of_lt_of_le one_pos hCB1)
  have hL0pos : (0:ℝ) < L0 := by
    rw [hL0]
    have h1 : (0:ℝ) < 36 * CB * EE := by nlinarith [hCB1, hEEpos]
    exact div_pos h1 hδ₄0

  have hCSpos : (0:ℝ) < CS := by
    rw [hCS]
    have hB0S1 : (1:ℝ) ≤ B0S := by
      rw [hB0S]
      have h1 : (0:ℝ) ≤ QbS * k1 := by
        have : (0:ℝ) ≤ QbS := by rw [hQbS]; positivity
        positivity
      have h2 : (0:ℝ) ≤ MS * C * D1^k := by
        have hMS0 : (0:ℝ) ≤ MS := by rw [hMS]; linarith [hL0pos]
        have : (0:ℝ) < D1^k := pow_pos hD1pos k
        positivity
      linarith
    have hVS1 : (1:ℝ) ≤ 2 * VS := by
      rw [hVS]
      have h1 : (0:ℝ) ≤ 2 * (QbS * k1) := by
        have : (0:ℝ) ≤ QbS := by rw [hQbS]; positivity
        positivity
      have h2 : (0:ℝ) ≤ 2 * MS * (D1^k * C + Bk) := by
        have hMS0 : (0:ℝ) ≤ MS := by rw [hMS]; linarith [hL0pos]
        have : (0:ℝ) ≤ D1^k * C + Bk := by linarith [hCD1, hBk0]
        positivity
      linarith
    have h3 : (0:ℝ) < (2*VS)^k := pow_pos (by linarith) k
    exact mul_pos (lt_of_lt_of_le one_pos hB0S1) h3
  have hC'pos : (0:ℝ) < (1 + C₀) * max CB CS + 1 := by
    have h1 : (0:ℝ) < max CB CS := lt_of_lt_of_le one_pos (le_trans hCB1 (le_max_left CB CS))
    have h2 : (0:ℝ) ≤ 1 + C₀ := by linarith
    linarith [mul_nonneg h2 (le_of_lt h1)]
  refine ⟨(1 + C₀) * max CB CS + 1, hC'pos, ?_⟩
  intro L q D a hL hq hqC hδ1L hCb hDc hDm hHyp
  have hL1 : 1 ≤ L := by omega
  have hq1 : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq
  have hLpos : (0:ℝ) < (L:ℝ) := by exact_mod_cast (by omega : 0 < L)
  have hdle : ∀ d ∈ D, d ≤ L := fun d hd => le_of_pos_sub hδ₁ hL1 (hDm d hd).2
  by_cases hbig : L0 ≤ (L:ℝ)
  · -- ============ BIG case ============
    have hB0Bb : (Kp / (δ₄^3 * (L:ℝ))) * C * (L:ℝ) * D1^k ≤ B0B := by
      have hLne : (L:ℝ) ≠ 0 := ne_of_gt hLpos
      have heq : (Kp / (δ₄^3 * (L:ℝ))) * C * (L:ℝ) * D1^k = Kp * C * D1^k / δ₄^3 := by
        rw [show (Kp / (δ₄^3 * (L:ℝ))) * C * (L:ℝ) * D1^k
            = ((Kp / (δ₄^3 * (L:ℝ))) * (L:ℝ)) * (C * D1^k) by ring]
        rw [ebL Kp (δ₄^3) (L:ℝ) hLne]
        ring
      rw [heq, hB0B]
      have h1 : (0:ℝ) ≤ QbB * k1 := mul_nonneg hQbB0 hk10
      have h2 : (0:ℝ) ≤ Kp * C * D1^k / δ₄^3 := by positivity
      linarith
    have hVBb : 2 * (Kp / (δ₄^3 * (L:ℝ))) * (L:ℝ) * (D1^k * C + Bk) ≤ VB := by
      have hLne : (L:ℝ) ≠ 0 := ne_of_gt hLpos
      have heq : 2 * (Kp / (δ₄^3 * (L:ℝ))) * (L:ℝ) * (D1^k * C + Bk)
          = 2 * Kp * (D1^k * C + Bk) / δ₄^3 := by
        rw [show 2 * (Kp / (δ₄^3 * (L:ℝ))) * (L:ℝ) * (D1^k * C + Bk)
            = 2 * ((Kp / (δ₄^3 * (L:ℝ))) * (L:ℝ)) * (D1^k * C + Bk) by ring]
        rw [ebL Kp (δ₄^3) (L:ℝ) hLne]
        ring
      rw [heq, hVB]
      have h1 : (0:ℝ) ≤ 2 * (QbB * k1) := by positivity
      have h2 : (0:ℝ) ≤ 2 * Kp * (D1^k * C + Bk) / δ₄^3 := by positivity
      linarith
    have horacle : ∀ (m : ℕ) (H : ℕ) (K β : ℝ) (M : ℕ → ℤ),
        1 ≤ m → m ≤ k →
        Pinned k L (fun j => (q:ℝ)*a j) (m + 1) H K M →
        max (H:ℝ) K ≤ (2 * VB)^k * B0B →
        (∀ d ∈ D, ∃ z : ℤ, |β * (d:ℝ) - z| ≤
            H*C/(δ₁*(L:ℝ))^m + Bk*K/(L:ℝ)^m) →
        ∃ r : ℕ, 1 ≤ r ∧ (r:ℝ) ≤ QbB ∧ ∃ z : ℤ,
          |(r:ℝ) * β - z| ≤ (Kp / (δ₄^3 * (L:ℝ))) * (H*C*D1^k + Bk*K)/(L:ℝ)^m := by
      intro m H K β M hm1 hmk hpin' hbdd hgood
      have hH1 : (1:ℝ) ≤ (H:ℝ) := by exact_mod_cast hpin'.1
      have hH0 : (0:ℝ) ≤ (H:ℝ) := by linarith
      have hK0 : (0:ℝ) ≤ K := hpin'.2.1
      have hmaxb : max (H:ℝ) K ≤ CB := by rw [hCB, mul_comm]; exact hbdd
      have hHm : (H:ℝ) ≤ CB := le_trans (le_max_left _ _) hmaxb
      have hKm : K ≤ CB := le_trans (le_max_right _ _) hmaxb
      -- scaled error
      have hscaled := scaled_error (C := C) (K := K) (H := (H:ℝ)) (m := m) (k := k)
        hδ₁ (le_of_lt hC) hK0 hH0 hmk hLpos
      -- numerator bound
      have hnum : H*C*D1^k + Bk*K ≤ CB * EE := by
        have h1 : H*C*D1^k ≤ CB*(C*D1^k) := by
          calc H*C*D1^k = (H:ℝ) * (C*D1^k) := by ring
            _ ≤ CB * (C*D1^k) := mul_le_mul_of_nonneg_right hHm hCD1
        have h2 : Bk*K ≤ CB*Bk := by
          calc Bk*K ≤ Bk*CB := mul_le_mul_of_nonneg_left hKm hBk0
            _ = CB*Bk := by ring
        have h3 := add_le_add h1 h2
        rw [hEE, mul_add]
        exact h3
      -- L-power facts
      have hLp : (0:ℝ) < (L:ℝ)^m := pow_pos hLpos m
      have hLm : (L:ℝ) ≤ (L:ℝ)^m :=
        le_self_pow₀ (by exact_mod_cast hL1 : (1:ℝ) ≤ (L:ℝ)) (by omega : m ≠ 0)
      have hεhalf : H*C/(δ₁*(L:ℝ))^m + Bk*K/(L:ℝ)^m ≤ CB * EE / (L:ℝ) := by
        have h4 : (0:ℝ) ≤ CB*EE := mul_nonneg hCB0 hEE0
        calc H*C/(δ₁*(L:ℝ))^m + Bk*K/(L:ℝ)^m
            ≤ (H*C*D1^k + Bk*K)/(L:ℝ)^m := hscaled
          _ ≤ (CB * EE)/(L:ℝ)^m := div_le_div_of_nonneg_right hnum (le_of_lt hLp)
          _ ≤ CB * EE / (L:ℝ) := by
              rw [div_le_div_iff₀ hLp hLpos]
              have := mul_le_mul_of_nonneg_left hLm h4
              linarith [this]
      have hε : H*C/(δ₁*(L:ℝ))^m + Bk*K/(L:ℝ)^m ≤ δ₄/36 := by
        refine le_trans hεhalf ?_
        have hbig' : 36 * CB * EE / δ₄ ≤ (L:ℝ) := by rw [hL0] at hbig; exact hbig
        have h5 : 36 * (CB*EE) ≤ (L:ℝ) * δ₄ := by
          have := (div_le_iff₀ hδ₄0).mp hbig'
          linarith [this]
        rw [div_le_iff₀ hLpos, mul_comm, div_mul_eq_mul_div,
          le_div_iff₀ (by norm_num : (0:ℝ) < 36)]
        linarith [h5]
      have hεpos : 0 < H*C/(δ₁*(L:ℝ))^m + Bk*K/(L:ℝ)^m := by
        have h1 : (0:ℝ) < H*C := mul_pos (lt_of_lt_of_le one_pos hH1) hC
        have h3 : (0:ℝ) < (δ₁*(L:ℝ))^m := pow_pos (mul_pos hδ₁ hLpos) m
        have h5 : (0:ℝ) ≤ Bk*K/(L:ℝ)^m := by positivity
        have : (0:ℝ) < H*C/(δ₁*(L:ℝ))^m := div_pos h1 h3
        linarith
      obtain ⟨r, hr1, hrQb, z, hrz⟩ := hpin β L δ₄ (H*C/(δ₁*(L:ℝ))^m + Bk*K/(L:ℝ)^m) D
        hL1 hδ₄0 hδ₄1 hεpos hε (fun h hd => ⟨(hDm h hd).1, hdle h hd⟩) hDc hgood
      refine ⟨r, hr1, ?_, z, ?_⟩
      · rw [hQbB]
        exact le_trans hrQb (div_le_div_of_nonneg_right (le_max_left Kp (4:ℝ)) (le_of_lt hδ₄0))
      · have hKp3 : 0 < Kp / δ₄^3 := div_pos hKp0 h3pos
        have hscale2 : H*C/(δ₁*(L:ℝ))^m + Bk*K/(L:ℝ)^m
            ≤ (H*C*D1^k + Bk*K)/(L:ℝ)^m := by
          have := scaled_error (C := C) (K := K) (H := (H:ℝ)) (m := m) (k := k)
            hδ₁ (le_of_lt hC) hK0 hH0 hmk hLpos
          rwa [← hD1def] at this
        have h6 := mul_le_mul_of_nonneg_left hscale2 (by positivity : (0:ℝ) ≤ Kp / (δ₄^3 * (L:ℝ)))
        have heq2 : Kp * (H*C/(δ₁*(L:ℝ))^m + Bk*K/(L:ℝ)^m) / (δ₄^3 * (L:ℝ))
            = (Kp / (δ₄^3 * (L:ℝ))) * (H*C/(δ₁*(L:ℝ))^m + Bk*K/(L:ℝ)^m) := by ring
        have heq3 : (Kp / (δ₄^3 * (L:ℝ))) * ((H*C*D1^k + Bk*K)/(L:ℝ)^m)
            = (Kp / (δ₄^3 * (L:ℝ))) * (H*C*D1^k + Bk*K)/(L:ℝ)^m := by
          rw [mul_div_assoc']
        linarith [hrz, h6, heq2, heq3]
    have hres := descent_ind k hkpos L q hL1 D a C δ₁ δ₄ QbB (Kp / (δ₄^3 * (L:ℝ))) VB B0B
      hC hδ₁ hδ₄0 hDc hDm hHyp hQbB1
      (div_nonneg (le_of_lt hKp0) (mul_nonneg (le_of_lt h3pos) (le_of_lt hLpos))) hVB1 hB0B1
      (by rw [hB0B]; linarith [show (0:ℝ) ≤ Kp * C * D1^k / δ₄^3 by positivity]) 
      hB0Bb
      (by rw [hVB]; linarith [show (0:ℝ) ≤ 2 * Kp * (D1^k * C + Bk) / δ₄^3 by positivity])
      hVBb horacle
    obtain ⟨H, K, M, hpin1, hbdd1⟩ := hres
    have hHb : (H:ℝ) ≤ CB := le_trans (le_max_left _ _) hbdd1
    have hKb : K ≤ CB := le_trans (le_max_right _ _) hbdd1
    have hCBl : CB ≤ (1 + C₀) * max CB CS + 1 := by
      have h1 : CB ≤ max CB CS := le_max_left _ _
      have h2 : (0:ℝ) ≤ 1 + C₀ := by linarith
      nlinarith [h1, hC₀, hCB0]
    refine ⟨H*q, Nat.succ_le_of_lt (Nat.mul_pos
        (Nat.lt_of_lt_of_le Nat.zero_lt_one hpin1.1) (Nat.lt_of_lt_of_le Nat.zero_lt_one hq)), ?_, ?_⟩
    · have h2 : ((H*q : ℕ) : ℝ) = (H:ℝ) * (q:ℝ) := by push_cast; ring
      rw [h2]
      have h3 : (H:ℝ) * (q:ℝ) ≤ CB * C₀ := mul_le_mul hHb hqC (by linarith) hCB0
      have h4 : CB * C₀ ≤ max CB CS * (1 + C₀) :=
        mul_le_mul (le_max_left CB CS) (le_add_of_nonneg_left (by norm_num : (0:ℝ) ≤ 1))
          (le_of_lt (lt_of_lt_of_le one_pos hC₀)) (le_trans hCB0 (le_max_left CB CS))
      have h5 : max CB CS * (1 + C₀) = (1 + C₀) * max CB CS := by ring
      have h6 : (1 + C₀) * max CB CS ≤ (1 + C₀) * max CB CS + 1 := le_add_of_nonneg_right (by norm_num)
      linarith [h3, h4, h5, h6]
    · intro j hj
      have hz := hpin1.2.2 j hj
      refine ⟨M j, ?_⟩
      have h2 : ((H*q : ℕ) : ℝ) * a j = (H:ℝ) * ((q:ℝ) * a j) := by push_cast; ring
      rw [h2]
      have h3 : K / (L:ℝ)^j ≤ CB / (L:ℝ)^j := div_le_div_of_nonneg_right hKb (by positivity)
      have h4 : CB / (L:ℝ)^j ≤ ((1 + C₀) * max CB CS + 1) / (L:ℝ)^j :=
        div_le_div_of_nonneg_right hCBl (by positivity)
      have hz' : |(H:ℝ) * ((q:ℝ) * a j) - (M j : ℝ)| ≤ K/(L:ℝ)^j := by simpa using hz
      exact le_trans hz' (le_trans h3 h4)
  · -- ============ SMALL case ============
    have hbig' : (L:ℝ) < L0 := not_le.mp hbig
    have hMS1 : (1:ℝ) ≤ MS := by rw [hMS]; linarith [hL0, hCB1, hEEpos, hδ₄0]
    have hMSL : (L:ℝ) ≤ MS := by rw [hMS]; linarith [hbig']
    have h2LMS : 2 * (L:ℝ) ≤ MS := by rw [hMS]; linarith [hbig']
    have hB0Sb : 2 * C * (L:ℝ) * D1^k ≤ B0S := by
      rw [hB0S]
      have h1 : 2 * C * (L:ℝ) * D1^k ≤ MS * C * D1^k := by
        have h2 : 2 * C * (L:ℝ) ≤ MS * C := by nlinarith [h2LMS, hC]
        exact mul_le_mul_of_nonneg_right h2 (le_of_lt hD1k)
      have h3 : (0:ℝ) ≤ QbS * k1 := by
        have : (0:ℝ) ≤ QbS := by rw [hQbS]; positivity
        positivity
      linarith [h1, h3]
    have hVSb : 2 * 2 * (L:ℝ) * (D1^k * C + Bk) ≤ VS := by
      rw [hVS]
      have hX : (0:ℝ) ≤ D1^k * C + Bk := by linarith [hCD1, hBk0]
      have h2 : 4 * (L:ℝ) ≤ 2 * MS := by rw [hMS]; linarith [hbig']
      have h1 : 4 * (L:ℝ) * (D1^k * C + Bk) ≤ 2 * MS * (D1^k * C + Bk) :=
        mul_le_mul_of_nonneg_right h2 hX
      have h3 : (0:ℝ) ≤ 2 * (QbS * k1) := by
        have : (0:ℝ) ≤ QbS := by rw [hQbS]; positivity
        positivity
      linarith [h1, h3]
    have horacle : ∀ (m : ℕ) (H : ℕ) (K β : ℝ) (M : ℕ → ℤ),
        1 ≤ m → m ≤ k →
        Pinned k L (fun j => (q:ℝ)*a j) (m + 1) H K M →
        max (H:ℝ) K ≤ (2 * VS)^k * B0S →
        (∀ d ∈ D, ∃ z : ℤ, |β * (d:ℝ) - z| ≤
            H*C/(δ₁*(L:ℝ))^m + Bk*K/(L:ℝ)^m) →
        ∃ r : ℕ, 1 ≤ r ∧ (r:ℝ) ≤ QbS ∧ ∃ z : ℤ,
          |(r:ℝ) * β - z| ≤ 2 * (H*C*D1^k + Bk*K)/(L:ℝ)^m := by
      intro m H K β M hm1 hmk hpin' hbdd hgood
      have hH1 : (1:ℝ) ≤ (H:ℝ) := by exact_mod_cast hpin'.1
      have hH0 : (0:ℝ) ≤ (H:ℝ) := by linarith
      have hK0 : (0:ℝ) ≤ K := hpin'.2.1
      have hεpos : 0 < H*C/(δ₁*(L:ℝ))^m + Bk*K/(L:ℝ)^m := by
        have h1 : (0:ℝ) < H*C := mul_pos (lt_of_lt_of_le one_pos hH1) hC
        have h3 : (0:ℝ) < (δ₁*(L:ℝ))^m := pow_pos (mul_pos hδ₁ hLpos) m
        have h5 : (0:ℝ) ≤ Bk*K/(L:ℝ)^m := by positivity
        have : (0:ℝ) < H*C/(δ₁*(L:ℝ))^m := div_pos h1 h3
        linarith
      obtain ⟨r, hr1, hrQb, z, hrz⟩ :=
        small_multiple (L := L) (δ := δ₄) (ε := H*C/(δ₁*(L:ℝ))^m + Bk*K/(L:ℝ)^m) (β := β)
          hL1 hδ₄0 hεpos (fun d hd => (hDm d hd).1) hdle hDc hgood
      refine ⟨r, hr1, ?_, z, ?_⟩
      · rw [hQbS]; exact hrQb
      · have hscaled := scaled_error (C := C) (K := K) (H := (H:ℝ)) (m := m) (k := k)
          hδ₁ (le_of_lt hC) hK0 hH0 hmk hLpos
        rw [← hD1def, ← hBkdef] at hscaled
        have heq : 2 * (H*C*D1^k + Bk*K)/(L:ℝ)^m = 2 * ((H*C*D1^k + Bk*K)/(L:ℝ)^m) := by ring
        have h2 := mul_le_mul_of_nonneg_left hscaled (by norm_num : (0:ℝ) ≤ 2)
        linarith [hrz, h2, heq]
    -- the constant facts for the small case
    have hQbS1 : (1:ℝ) ≤ QbS := by rw [hQbS]; rw [le_div_iff₀ hδ₄0]; linarith
    have hQbS0 : (0:ℝ) ≤ QbS := le_of_lt (lt_of_lt_of_le one_pos hQbS1)
    have hX0 : (0:ℝ) ≤ D1^k * C + Bk := by linarith [hCD1, hBk0]
    have hVS1' : (1:ℝ) ≤ VS := by
      rw [hVS]
      have h1 : (0:ℝ) ≤ 2 * (QbS * k1) := by positivity
      have h2 : (0:ℝ) ≤ 2 * MS * (D1^k * C + Bk) := by positivity
      linarith
    have hB0S1' : (1:ℝ) ≤ B0S := by
      rw [hB0S]
      have h1 : (0:ℝ) ≤ QbS * k1 := by positivity
      have h2 : (0:ℝ) ≤ MS * C * D1^k := by positivity
      linarith
    have hB0aS : QbS * ((k:ℝ)+1) ≤ B0S := by
      rw [hB0S]
      have h1 : (0:ℝ) ≤ MS * C * D1^k := by positivity
      linarith
    have hVaS : 2 * (QbS * ((k:ℝ)+1)) ≤ VS := by
      rw [hVS]
      have h1 : (0:ℝ) ≤ 2 * MS * (D1^k * C + Bk) := by positivity
      linarith
    have hB0bS : 2 * C * (L:ℝ) * (D1b δ₁)^k ≤ B0S := by
      rw [hD1def] at hB0Sb
      exact hB0Sb
    have hVbS : 2 * 2 * (L:ℝ) * ((D1b δ₁)^k * C + PinB k) ≤ VS := by
      rw [hD1def, hBkdef] at hVSb
      exact hVSb
    have hres := descent_ind k hkpos L q hL1 D a C δ₁ δ₄ QbS 2 VS B0S
      hC hδ₁ hδ₄0 hDc hDm hHyp hQbS1 (by norm_num) hVS1' hB0S1'
      hB0aS hB0bS hVaS hVbS horacle
    obtain ⟨H, K, M, hpin1, hbdd1⟩ := hres
    have hHb : (H:ℝ) ≤ CS := le_trans (le_max_left _ _) hbdd1
    have hKb : K ≤ CS := le_trans (le_max_right _ _) hbdd1
    have hCS0 : (0:ℝ) ≤ CS := by
      rw [hCS]
      have h1 : (1:ℝ) ≤ B0S := by
        rw [hB0S]
        linarith [show (0:ℝ) ≤ QbS * k1 by
            have : (0:ℝ) ≤ QbS := by rw [hQbS]; positivity
            positivity,
          show (0:ℝ) ≤ MS * C * D1^k by
            have : (0:ℝ) ≤ MS := le_of_lt (lt_of_lt_of_le one_pos hMS1)
            positivity]
      have h2 : (1:ℝ) ≤ 2 * VS := by
        rw [hVS]
        linarith [show (0:ℝ) ≤ 2 * (QbS * k1) by
            have : (0:ℝ) ≤ QbS := by rw [hQbS]; positivity
            positivity,
          show (0:ℝ) ≤ 2 * MS * (D1^k * C + Bk) by
            have : (0:ℝ) ≤ 2 * MS := by linarith [hMS1]
            positivity]
      have h3 : (0:ℝ) ≤ (2 * VS)^k := pow_nonneg (by linarith) k
      exact mul_nonneg (le_of_lt (lt_of_lt_of_le one_pos h1)) h3
    have hCSl : CS ≤ (1 + C₀) * max CB CS + 1 := by
      have h1 : CS ≤ max CB CS := le_max_right _ _
      have h2 : (0:ℝ) ≤ 1 + C₀ := by linarith
      nlinarith [h1, hC₀, hCS0]
    have hCBl : CB ≤ (1 + C₀) * max CB CS + 1 := by
      have h1 : CB ≤ max CB CS := le_max_left _ _
      have h2 : (0:ℝ) ≤ 1 + C₀ := by linarith
      nlinarith [h1, hC₀, hCB0]
    refine ⟨H*q, Nat.succ_le_of_lt (Nat.mul_pos
        (Nat.lt_of_lt_of_le Nat.zero_lt_one hpin1.1) (Nat.lt_of_lt_of_le Nat.zero_lt_one hq)), ?_, ?_⟩
    · have h2 : ((H*q : ℕ) : ℝ) = (H:ℝ) * (q:ℝ) := by push_cast; ring
      rw [h2]
      have h3 : (H:ℝ) * (q:ℝ) ≤ CS * C₀ := mul_le_mul hHb hqC (by linarith) hCS0
      have h4 : CS * C₀ ≤ max CB CS * (1 + C₀) :=
        mul_le_mul (le_max_right CB CS) (le_add_of_nonneg_left (by norm_num : (0:ℝ) ≤ 1))
          (le_of_lt (lt_of_lt_of_le one_pos hC₀)) (le_trans hCS0 (le_max_right CB CS))
      have h5 : max CB CS * (1 + C₀) = (1 + C₀) * max CB CS := by ring
      have h6 : (1 + C₀) * max CB CS ≤ (1 + C₀) * max CB CS + 1 := le_add_of_nonneg_right (by norm_num)
      linarith [h3, h4, h5, h6]
    · intro j hj
      have hz := hpin1.2.2 j hj
      refine ⟨M j, ?_⟩
      have h2 : ((H*q : ℕ) : ℝ) * a j = (H:ℝ) * ((q:ℝ) * a j) := by push_cast; ring
      rw [h2]
      have h3 : K / (L:ℝ)^j ≤ CS / (L:ℝ)^j := div_le_div_of_nonneg_right hKb (by positivity)
      have h4 : CS / (L:ℝ)^j ≤ ((1 + C₀) * max CB CS + 1) / (L:ℝ)^j :=
        div_le_div_of_nonneg_right hCSl (by positivity)
      have hz' : |(H:ℝ) * ((q:ℝ) * a j) - (M j : ℝ)| ≤ K/(L:ℝ)^j := by simpa using hz
      exact le_trans hz' (le_trans h3 h4)

end Work.BMF.SD
