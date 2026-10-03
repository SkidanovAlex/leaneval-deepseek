import Mathlib
import Submission.Work.FIChain.RhoWin2Defs
import Submission.Work.FIChain.TailDefs
import Submission.Work.FIChain.GammaTruncMulCoprime
import Submission.Work.FIChain.PiPartDecomp
import Submission.Work.FIChain.CoprimeProdPPiCond

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.FIChain

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- `μ` is multiplicative on coprime arguments, cast to `ℝ`. -/
lemma moebius_mul_cast {a b : ℕ} (h : a.Coprime b) :
    (ArithmeticFunction.moebius (a * b) : ℝ)
      = (ArithmeticFunction.moebius a : ℝ) * (ArithmeticFunction.moebius b : ℝ) := by
  have hh : ArithmeticFunction.moebius (a * b)
      = ArithmeticFunction.moebius a * ArithmeticFunction.moebius b :=
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime h
  rw [hh]; push_cast; ring

/-- The pointwise Möbius/`ã` relation: `μ(cn)·ã(cn) = μ(c)μ(n)·ã(cn)`, valid because `ã`
vanishes off the squarefree integers. -/
lemma moebius_atilc_mul (c n : ℕ) :
    (ArithmeticFunction.moebius (c * n) : ℝ) * atilc (c * n)
      = (ArithmeticFunction.moebius c : ℝ) * (ArithmeticFunction.moebius n : ℝ)
          * atilc (c * n) := by
  by_cases h : Squarefree (c * n)
  · have hcn : c.Coprime n := Nat.coprime_of_squarefree_mul h
    have hm : ArithmeticFunction.moebius (c * n)
        = ArithmeticFunction.moebius c * ArithmeticFunction.moebius n :=
      ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcn
    rw [hm]; push_cast; ring
  · rw [show atilc (c * n) = 0 from by
      unfold atilc Work.FITop.atilFIa Submission.ASP.atil
      rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree h]; ring]
    ring

theorem RhoWin2Ident (x Pz c : ℕ) (σ t : ℝ) :
    Work.FITop.XrhoC atilc x c σ t (2 * t)
      = (ArithmeticFunction.moebius c : ℝ) *
        ∑ n₁ ∈ (ProdP Pz).divisors,
          (ArithmeticFunction.moebius n₁ : ℝ) *
            ∑ d₁ ∈ n₁.divisors,
              (ArithmeticFunction.moebius d₁ : ℝ) * Xpg x Pz (c * n₁) (σ / d₁) (t / n₁) := by
  classical
  by_cases hc0 : c = 0
  · subst hc0
    simp only [Work.FITop.XrhoC]
    simp
  · have hc1 : 1 ≤ c := Nat.one_le_iff_ne_zero.mpr hc0
    set T : Finset ℕ := (Finset.Icc 1 x).filter
        (fun n => c * n ≤ x ∧ t < (n : ℝ) ∧ (n : ℝ) ≤ 2 * t) with hT
    set Sn : ℕ → Finset ℕ := fun n₁ => (Finset.Icc 1 x).filter
        (fun n => (c * n₁) * n ≤ x ∧ Work.FITop4.PiCond Pz n ∧ t / n₁ < (n : ℝ)
          ∧ (n : ℝ) ≤ 2 * (t / n₁)) with hSn
    set S : Finset (Σ _ : ℕ, ℕ) := (ProdP Pz).divisors.sigma Sn with hS
    have mem_Sn : ∀ n₁ n, n ∈ Sn n₁ ↔ (n ∈ Finset.Icc 1 x ∧ (c * n₁) * n ≤ x
        ∧ Work.FITop4.PiCond Pz n ∧ t / n₁ < (n : ℝ) ∧ (n : ℝ) ≤ 2 * (t / n₁)) := by
      intro n₁ n; rw [hSn, Finset.mem_filter]
    have mem_T : ∀ n, n ∈ T ↔ (n ∈ Finset.Icc 1 x ∧ c * n ≤ x ∧ t < (n : ℝ)
        ∧ (n : ℝ) ≤ 2 * t) := by
      intro n; rw [hT, Finset.mem_filter]
    have mem_S : ∀ p : Σ _ : ℕ, ℕ, p ∈ S ↔ (p.1 ∈ (ProdP Pz).divisors ∧ p.2 ∈ Sn p.1) := by
      intro p; rw [hS, Finset.mem_sigma]
    -- ## (1) The left-hand side, rewritten in the window form.
    have hLex : Work.FITop.XrhoC atilc x c σ t (2 * t)
        = (ArithmeticFunction.moebius c : ℝ) *
          ∑ n ∈ (Finset.Icc 1 x).filter
              (fun n => c * n ≤ x ∧ t < (n : ℝ) ∧ (n : ℝ) ≤ 2 * t),
            Work.FIPlan.gammaTrunc σ n * (ArithmeticFunction.moebius n : ℝ) * atilc (c * n) := by
      rw [Work.FITop.XrhoC, ← Finset.sum_filter, Finset.filter_filter, Finset.mul_sum]
      refine Finset.sum_congr ?_ ?_
      · refine Finset.filter_congr (fun n _ => ?_); tauto
      · intro n _
        have h := moebius_atilc_mul c n
        calc Work.FIPlan.gammaTrunc σ n * (ArithmeticFunction.moebius (c * n) : ℝ)
                * atilc (c * n)
            = Work.FIPlan.gammaTrunc σ n
                * ((ArithmeticFunction.moebius (c * n) : ℝ) * atilc (c * n)) := by ring
          _ = Work.FIPlan.gammaTrunc σ n
                * ((ArithmeticFunction.moebius c : ℝ) * (ArithmeticFunction.moebius n : ℝ)
                    * atilc (c * n)) := by rw [h]
          _ = (ArithmeticFunction.moebius c : ℝ)
                * (Work.FIPlan.gammaTrunc σ n * (ArithmeticFunction.moebius n : ℝ)
                    * atilc (c * n)) := by ring
    have hL : Work.FITop.XrhoC atilc x c σ t (2 * t)
        = (ArithmeticFunction.moebius c : ℝ) *
          ∑ n ∈ T, Work.FIPlan.gammaTrunc σ n * (ArithmeticFunction.moebius n : ℝ)
            * atilc (c * n) := by
      rw [hLex, ← hT]
    -- ## (2) The per-`n₁` inner identity.
    have inner : ∀ n₁ ∈ (ProdP Pz).divisors,
        ∑ d₁ ∈ n₁.divisors, (ArithmeticFunction.moebius d₁ : ℝ)
            * Xpg x Pz (c * n₁) (σ / d₁) (t / n₁)
        = ∑ n₀ ∈ Sn n₁, (ArithmeticFunction.moebius n₀ : ℝ)
            * Work.FIPlan.gammaTrunc σ (n₁ * n₀) * atilc ((c * n₁) * n₀) := by
      intro n₁ hn₁
      have hn₁d : n₁ ∣ ProdP Pz := (Nat.mem_divisors.mp hn₁).1
      have hXpg : ∀ d₁ : ℕ, Xpg x Pz (c * n₁) (σ / d₁) (t / n₁)
          = ∑ n₀ ∈ Sn n₁, (ArithmeticFunction.moebius n₀ : ℝ)
              * Work.FIPlan.gammaTrunc (σ / d₁) n₀ * atilc ((c * n₁) * n₀) := by
        intro d₁; rw [Xpg, hSn]
      simp only [hXpg]
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun n₀ hn₀ => ?_)
      obtain ⟨-, -, hpi, -, -⟩ := (mem_Sn n₁ n₀).mp hn₀
      have hcop : n₁.Coprime n₀ := CoprimeProdPPiCond Pz n₁ n₀ hn₁d hpi
      have hL1 : ∑ d₁ ∈ n₁.divisors, (ArithmeticFunction.moebius d₁ : ℝ)
            * Work.FIPlan.gammaTrunc (σ / (d₁ : ℝ)) n₀
          = Work.FIPlan.gammaTrunc σ (n₁ * n₀) := GammaTruncMulCoprime n₁ n₀ hcop σ
      rw [← hL1]
      rw [show (ArithmeticFunction.moebius n₀ : ℝ)
              * (∑ d₁ ∈ n₁.divisors, (ArithmeticFunction.moebius d₁ : ℝ)
                  * Work.FIPlan.gammaTrunc (σ / (d₁ : ℝ)) n₀)
              * atilc ((c * n₁) * n₀)
            = ∑ d₁ ∈ n₁.divisors, (ArithmeticFunction.moebius d₁ : ℝ)
                * ((ArithmeticFunction.moebius n₀ : ℝ)
                    * Work.FIPlan.gammaTrunc (σ / (d₁ : ℝ)) n₀
                    * atilc ((c * n₁) * n₀)) from by
          rw [Finset.mul_sum, Finset.sum_mul]
          exact Finset.sum_congr rfl (fun d₁ _ => by ring)]
    -- ## (3) Assemble the right-hand side into a sum over the `sigma`-set `S`.
    have hR1 : (∑ n₁ ∈ (ProdP Pz).divisors, (ArithmeticFunction.moebius n₁ : ℝ)
          * ∑ d₁ ∈ n₁.divisors, (ArithmeticFunction.moebius d₁ : ℝ)
              * Xpg x Pz (c * n₁) (σ / d₁) (t / n₁))
        = ∑ n₁ ∈ (ProdP Pz).divisors, (ArithmeticFunction.moebius n₁ : ℝ)
            * ∑ n₀ ∈ Sn n₁, (ArithmeticFunction.moebius n₀ : ℝ)
                * Work.FIPlan.gammaTrunc σ (n₁ * n₀) * atilc ((c * n₁) * n₀) := by
      refine Finset.sum_congr rfl (fun n₁ hn₁ => ?_)
      rw [inner n₁ hn₁]
    have hR2 : (∑ n₁ ∈ (ProdP Pz).divisors, (ArithmeticFunction.moebius n₁ : ℝ)
            * ∑ n₀ ∈ Sn n₁, (ArithmeticFunction.moebius n₀ : ℝ)
                * Work.FIPlan.gammaTrunc σ (n₁ * n₀) * atilc ((c * n₁) * n₀))
        = ∑ p ∈ S, (ArithmeticFunction.moebius p.1 : ℝ)
            * (ArithmeticFunction.moebius p.2 : ℝ)
            * Work.FIPlan.gammaTrunc σ (p.1 * p.2) * atilc ((c * p.1) * p.2) := by
      rw [hS, Finset.sum_sigma]
      refine Finset.sum_congr rfl (fun n₁ _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun n₀ _ => ?_)
      ring
    have hR3 : (∑ p ∈ S, (ArithmeticFunction.moebius p.1 : ℝ)
            * (ArithmeticFunction.moebius p.2 : ℝ)
            * Work.FIPlan.gammaTrunc σ (p.1 * p.2) * atilc ((c * p.1) * p.2))
        = ∑ p ∈ S, Work.FIPlan.gammaTrunc σ (p.1 * p.2)
            * (ArithmeticFunction.moebius (p.1 * p.2) : ℝ) * atilc (c * (p.1 * p.2)) := by
      refine Finset.sum_congr rfl (fun p hp => ?_)
      rw [mem_S] at hp
      obtain ⟨hp1, hp2⟩ := hp
      have hp1d : p.1 ∣ ProdP Pz := (Nat.mem_divisors.mp hp1).1
      obtain ⟨-, -, hpi, -, -⟩ := (mem_Sn p.1 p.2).mp hp2
      have hcop : p.1.Coprime p.2 := CoprimeProdPPiCond Pz p.1 p.2 hp1d hpi
      rw [mul_assoc c p.1 p.2, moebius_mul_cast hcop]
      ring
    have hInj : Set.InjOn (fun p : Σ _ : ℕ, ℕ => p.1 * p.2) ↑S := by
      rintro ⟨p1, p2⟩ hp ⟨q1, q2⟩ hq heq
      rw [Finset.mem_coe, mem_S] at hp hq
      simp only at heq
      have hp1d : p1 ∣ ProdP Pz := (Nat.mem_divisors.mp hp.1).1
      have hq1d : q1 ∣ ProdP Pz := (Nat.mem_divisors.mp hq.1).1
      obtain ⟨-, -, hpi, -, -⟩ := (mem_Sn p1 p2).mp hp.2
      obtain ⟨-, -, hqi, -, -⟩ := (mem_Sn q1 q2).mp hq.2
      obtain ⟨h1, h2⟩ := mul_inj_ProdP hp1d hq1d hpi hqi heq
      subst h1; subst h2; rfl
    have himage_sub : S.image (fun p : Σ _ : ℕ, ℕ => p.1 * p.2) ⊆ T := by
      intro b hb
      rw [Finset.mem_image] at hb
      obtain ⟨p, hp, rfl⟩ := hb
      rw [mem_S] at hp
      obtain ⟨hp1, hp2⟩ := hp
      obtain ⟨hnI, hle1, hpi, hlt, hle2⟩ := (mem_Sn p.1 p.2).mp hp2
      have hp1d : p.1 ∣ ProdP Pz := (Nat.mem_divisors.mp hp1).1
      have hp1pos : 0 < p.1 := Nat.pos_of_dvd_of_pos hp1d (ProdP_pos Pz)
      have hp1R : (0 : ℝ) < (p.1 : ℝ) := by exact_mod_cast hp1pos
      obtain ⟨hn1, hnx⟩ := Finset.mem_Icc.mp hnI
      rw [mem_T]
      refine ⟨Finset.mem_Icc.mpr ⟨?_, ?_⟩, ?_, ?_, ?_⟩
      · exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
      · calc p.1 * p.2 ≤ (c * p.1) * p.2 := Nat.mul_le_mul_right p.2 (by
              calc p.1 = 1 * p.1 := (one_mul p.1).symm
                _ ≤ c * p.1 := Nat.mul_le_mul_right p.1 hc1)
          _ ≤ x := hle1
      · have hcc : c * (p.1 * p.2) = (c * p.1) * p.2 := (mul_assoc c p.1 p.2).symm
        rw [hcc]; exact hle1
      · have hd := (div_lt_iff₀ hp1R).mp hlt
        calc t < (p.2 : ℝ) * (p.1 : ℝ) := hd
          _ = ((p.1 * p.2 : ℕ) : ℝ) := by push_cast; ring
      · have hd : (p.2 : ℝ) ≤ (2 * t) / (p.1 : ℝ) := by
          rw [mul_div_assoc]; exact hle2
        have hd2 := (le_div_iff₀ hp1R).mp hd
        calc ((p.1 * p.2 : ℕ) : ℝ) = (p.2 : ℝ) * (p.1 : ℝ) := by push_cast; ring
          _ ≤ 2 * t := hd2
    have hzero : ∀ b ∈ T, b ∉ S.image (fun p : Σ _ : ℕ, ℕ => p.1 * p.2) →
        Work.FIPlan.gammaTrunc σ b * (ArithmeticFunction.moebius b : ℝ) * atilc (c * b) = 0 := by
      intro b hbT hbnot
      have hμ : (ArithmeticFunction.moebius b : ℝ) = 0 := by
        have hnsq : ¬ Squarefree b := by
          intro hbsq
          apply hbnot
          rw [mem_T] at hbT
          obtain ⟨hbIcc, hbcx, hbt, hb2t⟩ := hbT
          obtain ⟨hb1, hbx⟩ := Finset.mem_Icc.mp hbIcc
          obtain ⟨a, n, hadvd, hnpi, hbeq⟩ := PiPartDecomp Pz b hbsq
          have hapos : 0 < a := Nat.pos_of_dvd_of_pos hadvd (ProdP_pos Pz)
          have haR : (0 : ℝ) < (a : ℝ) := by exact_mod_cast hapos
          have han : (b : ℝ) = (a : ℝ) * (n : ℝ) := by rw [hbeq]; push_cast; ring
          have hn1 : 1 ≤ n := by
            rcases Nat.eq_zero_or_pos n with h | h
            · exfalso; rw [h, mul_zero] at hbeq; omega
            · omega
          have hnx : n ≤ x := by
            have h1 : n ≤ a * n := Nat.le_mul_of_pos_left n hapos
            rw [← hbeq] at h1; exact le_trans h1 hbx
          have hcn : (c * a) * n ≤ x := by
            have h2 : (c * a) * n = c * b := by rw [hbeq]; ring
            rw [h2]; exact hbcx
          have ht' : t / (a : ℝ) < (n : ℝ) := by
            rw [div_lt_iff₀ haR]
            calc t < (b : ℝ) := hbt
              _ = (n : ℝ) * (a : ℝ) := by rw [han]; ring
          have hn2t : (n : ℝ) ≤ 2 * (t / (a : ℝ)) := by
            rw [← mul_div_assoc, le_div_iff₀ haR]
            calc (n : ℝ) * (a : ℝ) = (b : ℝ) := by rw [han]; ring
              _ ≤ 2 * t := hb2t
          have hmem : (⟨a, n⟩ : Σ _ : ℕ, ℕ) ∈ S := by
            rw [mem_S]
            exact ⟨Nat.mem_divisors.mpr ⟨hadvd, (ProdP_pos Pz).ne'⟩,
              (mem_Sn a n).mpr ⟨Finset.mem_Icc.mpr ⟨hn1, hnx⟩, hcn, hnpi, ht', hn2t⟩⟩
          exact Finset.mem_image.mpr ⟨⟨a, n⟩, hmem, hbeq.symm⟩
        have hz : ArithmeticFunction.moebius b = 0 :=
          ArithmeticFunction.moebius_eq_zero_of_not_squarefree hnsq
        rw [hz]; simp
      rw [hμ]; ring
    have hR4 : (∑ p ∈ S, Work.FIPlan.gammaTrunc σ (p.1 * p.2)
            * (ArithmeticFunction.moebius (p.1 * p.2) : ℝ) * atilc (c * (p.1 * p.2)))
        = ∑ n ∈ S.image (fun p : Σ _ : ℕ, ℕ => p.1 * p.2),
            Work.FIPlan.gammaTrunc σ n * (ArithmeticFunction.moebius n : ℝ) * atilc (c * n) := by
      rw [Finset.sum_image hInj]
    have hR5 : (∑ n ∈ S.image (fun p : Σ _ : ℕ, ℕ => p.1 * p.2),
            Work.FIPlan.gammaTrunc σ n * (ArithmeticFunction.moebius n : ℝ) * atilc (c * n))
        = ∑ n ∈ T, Work.FIPlan.gammaTrunc σ n * (ArithmeticFunction.moebius n : ℝ)
            * atilc (c * n) :=
      Finset.sum_subset himage_sub hzero
    have hM : (∑ n ∈ T, Work.FIPlan.gammaTrunc σ n * (ArithmeticFunction.moebius n : ℝ)
            * atilc (c * n))
        = ∑ n₁ ∈ (ProdP Pz).divisors, (ArithmeticFunction.moebius n₁ : ℝ)
            * ∑ d₁ ∈ n₁.divisors, (ArithmeticFunction.moebius d₁ : ℝ)
                * Xpg x Pz (c * n₁) (σ / d₁) (t / n₁) := by
      rw [← hR5, ← hR4, ← hR3, ← hR2, ← hR1]
    rw [hL, hM]

end

end Work.FIChain
