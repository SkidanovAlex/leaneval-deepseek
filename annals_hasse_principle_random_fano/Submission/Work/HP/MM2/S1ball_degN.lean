import Mathlib
import Submission.Work.HP.MM2.Defs
import Submission.Work.HP.lw_sum_inv_le_dyadic_shells
import Submission.Work.HP.isPrim_veronese
import Submission.Work.HP.MDBasic.finite_sets
import Submission.Work.HP.schmidt_sum_form
import Submission.Work.HP.detL_latOrth
import Submission.Work.HP.FM.minkowski_lower
import Submission.Work.HP.Lat.detL_ge_one
import Submission.Work.HP.rk_le_card
import Submission.Work.HP.Vero.finrank_latOrth
import Submission.Work.HP.MM2.dyadic_double_sum
import Submission.Work.HP.MM2.pow_div_lamprod_le
import Submission.Work.HP.MM2.nat_succ_le_log_bound

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section
open Filter Finset MeasureTheory

namespace Work.HP.MM2
open Work.HP

private theorem sum_inv_eNorm_le_lam_last {ι : Type} [Fintype ι] [DecidableEq ι] :
    ∃ K : ℝ, 0 < K ∧ ∀ (L : Submodule ℤ (ι → ℤ)) (T μ : ℝ), 1 ≤ T → 1 ≤ μ →
      lam L (rk L) ≤ μ →
      (∑ᶠ a ∈ {a : ι → ℤ | a ∈ L ∧ a ≠ 0 ∧ eNorm a ≤ T}, 1 / eNorm a) ≤
        K * ((1 + Real.log T) * (T ^ (rk L - 1) + μ ^ (rk L - 1)) / detL L + 1) := by
  classical
  obtain ⟨Ks, hKspos, hsch⟩ := Work.HP.schmidt_sum_form ι
  set K : ℝ := max (8 * Ks) (16 * Ks + 4 * Ks * (Fintype.card ι)) with hKdef
  have hKpos : 0 < K := by
    rw [hKdef]
    exact lt_of_lt_of_le (by positivity) (le_max_left _ _)
  refine ⟨K, hKpos, ?_⟩
  intro L T μ hT hμ hν
  have hT0 : (0 : ℝ) ≤ T := le_trans zero_le_one hT
  have hμ0 : (0 : ℝ) ≤ μ := le_trans zero_le_one hμ
  have hlog0 : 0 ≤ 1 + Real.log T := by linarith [Real.log_nonneg hT]
  have hdetpos : 0 < detL L := lt_of_lt_of_le zero_lt_one (Work.HP.Lat.detL_ge_one L)
  by_cases hbot : L = ⊥
  · subst hbot
    have hempty : ({a : ι → ℤ | a ∈ (⊥ : Submodule ℤ (ι → ℤ)) ∧ a ≠ 0 ∧ eNorm a ≤ T} : Set (ι → ℤ)) = ∅ := by
      ext a
      rw [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨haL, hne, -⟩
      exact hne (by simpa using haL)
    rw [hempty]
    have hz : (∑ᶠ a ∈ (∅ : Set (ι → ℤ)), 1 / eNorm a) = 0 := by simp
    rw [hz]
    refine mul_nonneg hKpos.le (add_nonneg (div_nonneg ?_ hdetpos.le) zero_le_one)
    exact mul_nonneg hlog0 (add_nonneg (pow_nonneg hT0 _) (pow_nonneg hμ0 _))
  · have hRpos : 1 ≤ rk L := by
      rcases Nat.eq_zero_or_pos (rk L) with h0 | hp
      · exfalso
        have hsub : Subsingleton L := by
          have hfin : Module.finrank ℤ L = 0 := by simpa [rk] using h0
          exact Module.finrank_zero_iff.mp hfin
        have hb : L = ⊥ := by
          rw [Submodule.eq_bot_iff]
          intro x hx
          have hx' : (⟨x, hx⟩ : L) = 0 := Subsingleton.elim _ _
          simpa using congrArg (fun y : L => (y : ι → ℤ)) hx'
        exact hbot hb
      · exact hp
    set Q : Set (ι → ℤ) := {a | a ∈ L ∧ a ≠ 0 ∧ eNorm a ≤ T} with hQdef
    set Xs : ℝ := (T ^ (rk L - 1) + μ ^ (rk L - 1)) / detL L with hXsdef
    have hXs0 : 0 ≤ Xs := by
      rw [hXsdef]
      exact div_nonneg (add_nonneg (pow_nonneg hT0 _) (pow_nonneg hμ0 _)) hdetpos.le
    have hQmem : ∀ a, a ∈ Q ↔ (a ∈ L ∧ a ≠ 0 ∧ eNorm a ≤ T) := by
      intro a
      rw [hQdef]
      exact Iff.rfl
    obtain ⟨J, hJ1, hJ2⟩ : ∃ J : ℕ, (2:ℝ)^J ≤ T ∧ T < (2:ℝ)^(J+1) := by
      have hfloor1 : 1 ≤ ⌊T⌋₊ := by
        have h := Nat.floor_mono hT
        simpa using h
      refine ⟨Nat.log 2 ⌊T⌋₊, ?_, ?_⟩
      · have h1' : 2^(Nat.log 2 ⌊T⌋₊) ≤ ⌊T⌋₊ := Nat.pow_log_le_self 2 (by omega)
        have h2' : ((2:ℕ)^(Nat.log 2 ⌊T⌋₊) : ℝ) ≤ (⌊T⌋₊ : ℝ) := by exact_mod_cast h1'
        have h3' : ((⌊T⌋₊ : ℕ) : ℝ) ≤ T := Nat.floor_le hT0
        calc (2:ℝ)^(Nat.log 2 ⌊T⌋₊) = ((2:ℕ)^(Nat.log 2 ⌊T⌋₊) : ℝ) := by push_cast; ring
          _ ≤ (⌊T⌋₊ : ℝ) := h2'
          _ ≤ T := h3'
      · have h1' : ⌊T⌋₊ < 2^((Nat.log 2 ⌊T⌋₊).succ) :=
          Nat.lt_pow_succ_log_self (by norm_num) ⌊T⌋₊
        have h2' : T < (⌊T⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one T
        have h3' : ((⌊T⌋₊ : ℝ) + 1) ≤ (2:ℝ)^((Nat.log 2 ⌊T⌋₊).succ) := by
          have h4 : (⌊T⌋₊ + 1 : ℕ) ≤ 2^((Nat.log 2 ⌊T⌋₊).succ) := Nat.succ_le_of_lt h1'
          have h5 : ((⌊T⌋₊ + 1 : ℕ) : ℝ) ≤ ((2^((Nat.log 2 ⌊T⌋₊).succ) : ℕ) : ℝ) := by exact_mod_cast h4
          push_cast at h5 ⊢
          linarith
        exact lt_of_lt_of_le h2' h3'
    have hQfin : Q.Finite := (MDBasic.finite_eNorm_le (ι := ι) T).subset
      (fun a ha => ((hQmem a).mp ha).2.2)
    have hQ1 : ∀ a ∈ Q, 1 ≤ eNorm a := fun a ha => one_le_eNorm ((hQmem a).mp ha).2.1
    have hQ2 : ∀ a ∈ Q, eNorm a ≤ T := fun a ha => ((hQmem a).mp ha).2.2
    have hshell := lw_sum_inv_le_dyadic_shells Q hQfin hT hQ1 hQ2 J hJ2
    have hcount : ∀ j ∈ Finset.range (J+1),
        (({a | a ∈ Q ∧ eNorm a ≤ T / (2:ℝ)^j} : Set (ι → ℤ)).ncard : ℝ) ≤
          Ks * ∑ m ∈ Finset.range (rk L + 1),
            (T / (2:ℝ)^j) ^ m / (∏ i ∈ Finset.range m, lam L (i + 1)) := by
      intro j hj
      have hjle : j ≤ J := by have := Finset.mem_range.mp hj; omega
      have h2jle : (2:ℝ)^j ≤ T :=
        le_trans (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hjle) hJ1
      have hY1 : 1 ≤ T / (2:ℝ)^j := by
        rw [le_div_iff₀ (by positivity)]
        linarith
      have hsub : ({a | a ∈ Q ∧ eNorm a ≤ T / (2:ℝ)^j} : Set (ι → ℤ)) ⊆
          {a : ι → ℤ | a ∈ L ∧ eNorm a ≤ T / (2:ℝ)^j} := by
        rintro a ⟨haQ, hle⟩
        exact ⟨((hQmem a).mp haQ).1, hle⟩
      have hfin : ({a : ι → ℤ | a ∈ L ∧ eNorm a ≤ T / (2:ℝ)^j} : Set (ι → ℤ)).Finite :=
        (MDBasic.finite_eNorm_le (ι := ι) _).subset (fun a ha => ha.2)
      have h1 : ({a | a ∈ Q ∧ eNorm a ≤ T / (2:ℝ)^j} : Set (ι → ℤ)).ncard ≤
          ballCount L (T / (2:ℝ)^j) := by
        simpa [ballCount] using Set.ncard_le_ncard hsub hfin
      calc (({a | a ∈ Q ∧ eNorm a ≤ T / (2:ℝ)^j} : Set (ι → ℤ)).ncard : ℝ)
          ≤ (ballCount L (T / (2:ℝ)^j) : ℝ) := by exact_mod_cast h1
        _ ≤ Ks * ∑ i ∈ Finset.range (rk L + 1),
              (T / (2:ℝ)^j) ^ (rk L - i) / (∏ i' ∈ Finset.range (rk L - i), lam L (i' + 1)) :=
            hsch L (T / (2:ℝ)^j) hY1
        _ = Ks * ∑ m ∈ Finset.range (rk L + 1),
              (T / (2:ℝ)^j) ^ m / (∏ i ∈ Finset.range m, lam L (i + 1)) := by
            rw [Work.HP.sum_reindex_schmidt]
    set A : ℕ → ℝ := (fun m => Ks / (∏ i ∈ Finset.range m, lam L (i + 1))) with hAdef
    have hA0 : ∀ m, 0 ≤ A m := by
      intro m
      change 0 ≤ Ks / (∏ i ∈ Finset.range m, lam L (i + 1))
      exact div_nonneg hKspos.le (Finset.prod_nonneg (fun i _ => lam_nonneg L (i + 1)))
    have hA0v : A 0 = Ks := by
      change Ks / (∏ i ∈ Finset.range 0, lam L (i + 1)) = Ks
      simp
    have hhterm : ∀ m, 1 ≤ m → m ≤ rk L →
        T ^ (m - 1) / (∏ i ∈ Finset.range m, lam L (i + 1)) ≤ Xs := by
      intro m hm1 hmR
      rw [hXsdef]
      exact pow_div_lamprod_le L hT hμ hν hm1 hmR
    have hA1le : A 1 ≤ Ks * Xs := by
      change Ks / (∏ i ∈ Finset.range 1, lam L (i + 1)) ≤ Ks * Xs
      rw [Finset.prod_range_one]
      have hh : 1 / lam L 1 ≤ Xs := by
        have := hhterm 1 le_rfl hRpos
        simpa using this
      calc Ks / lam L 1 = Ks * (1 / lam L 1) := by ring
        _ ≤ Ks * Xs := mul_le_mul_of_nonneg_left hh hKspos.le
    have hsumA : (∑ m ∈ Finset.range (rk L + 1), T ^ (m - 1) * A m) ≤
        Ks + (rk L : ℝ) * (Ks * Xs) := by
      set f : ℕ → ℝ := fun m => T ^ (m - 1) * A m with hfdef
      have hsum_eq : (∑ m ∈ Finset.range (rk L + 1), T ^ (m - 1) * A m)
          = ∑ m ∈ Finset.range (rk L + 1), f m := rfl
      rw [hsum_eq, Finset.sum_range_succ']
      have h0 : f 0 = Ks := by
        change T ^ (0 - 1) * A 0 = Ks
        simp [hA0v]
      have hstep : ∀ m ∈ Finset.range (rk L), f (m + 1) ≤ Ks * Xs := by
        intro m hm
        have hmR : m + 1 ≤ rk L := by have := Finset.mem_range.mp hm; omega
        have hh := hhterm (m + 1) (by omega) hmR
        have hexp : m + 1 - 1 = m := by omega
        change T ^ (m + 1 - 1) * (Ks / (∏ i ∈ Finset.range (m + 1), lam L (i + 1))) ≤ Ks * Xs
        rw [hexp]
        have heq : T ^ m * (Ks / (∏ i ∈ Finset.range (m + 1), lam L (i + 1)))
            = Ks * (T ^ m / (∏ i ∈ Finset.range (m + 1), lam L (i + 1))) := by ring
        rw [heq]
        exact mul_le_mul_of_nonneg_left (by simpa using hh) hKspos.le
      calc (∑ m ∈ Finset.range (rk L), f (m + 1)) + f 0
          = (∑ m ∈ Finset.range (rk L), f (m + 1)) + Ks := by rw [h0]
        _ ≤ (∑ m ∈ Finset.range (rk L), Ks * Xs) + Ks :=
            add_le_add (Finset.sum_le_sum hstep) le_rfl
        _ = (rk L : ℝ) * (Ks * Xs) + Ks := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        _ = Ks + (rk L : ℝ) * (Ks * Xs) := by ring
    have hstep1 : (∑ᶠ a ∈ Q, 1 / eNorm a) ≤
        ∑ j ∈ Finset.range (J + 1), (2:ℝ)^(j+1) / T *
          (Ks * ∑ m ∈ Finset.range (rk L + 1),
            (T / (2:ℝ)^j) ^ m / (∏ i ∈ Finset.range m, lam L (i + 1))) := by
      refine hshell.trans ?_
      refine Finset.sum_le_sum (fun j hj => ?_)
      exact mul_le_mul_of_nonneg_left (hcount j hj) (by positivity)
    have hstep2 : (∑ j ∈ Finset.range (J + 1), (2:ℝ)^(j+1) / T *
          (Ks * ∑ m ∈ Finset.range (rk L + 1),
            (T / (2:ℝ)^j) ^ m / (∏ i ∈ Finset.range m, lam L (i + 1))))
        = ∑ j ∈ Finset.range (J + 1), (2:ℝ)^(j+1) / T *
          (∑ m ∈ Finset.range (rk L + 1), (T / (2:ℝ)^j) ^ m * A m) := by
      refine Finset.sum_congr rfl (fun j hj => ?_)
      congr 1
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun m hm => ?_)
      change Ks * ((T / (2:ℝ)^j) ^ m / (∏ i ∈ Finset.range m, lam L (i + 1)))
        = (T / (2:ℝ)^j) ^ m * (Ks / (∏ i ∈ Finset.range m, lam L (i + 1)))
      ring
    have hdouble' := dyadic_double_sum (rk L) J T A hT hJ1 hA0
    have h3 : (∑ᶠ a ∈ Q, 1 / eNorm a) ≤
        4 * A 0 + 4 * ((J:ℝ) + 1) * A 1 + 4 * (Ks + (rk L : ℝ) * (Ks * Xs)) := by
      calc (∑ᶠ a ∈ Q, 1 / eNorm a)
          ≤ ∑ j ∈ Finset.range (J + 1), (2:ℝ)^(j+1) / T *
              (∑ m ∈ Finset.range (rk L + 1), (T / (2:ℝ)^j) ^ m * A m) :=
            hstep1.trans (le_of_eq hstep2)
        _ ≤ 4 * A 0 + 4 * ((J:ℝ) + 1) * A 1 + 4 * ∑ m ∈ Finset.range (rk L + 1), T ^ (m - 1) * A m :=
            hdouble'
        _ ≤ 4 * A 0 + 4 * ((J:ℝ) + 1) * A 1 + 4 * (Ks + (rk L : ℝ) * (Ks * Xs)) := by
            linarith [hsumA]
    have hlogb := nat_succ_le_log_bound T J hT hJ1
    have hnk : 0 ≤ Ks * Xs := mul_nonneg hKspos.le hXs0
    have hA1' : 4 * ((J:ℝ) + 1) * A 1 ≤ 16 * (1 + Real.log T) * (Ks * Xs) := by
      have h1 : A 1 * ((J:ℝ) + 1) ≤ (Ks * Xs) * (4 * (1 + Real.log T)) :=
        mul_le_mul hA1le hlogb (by positivity) hnk
      linarith [h1]
    have h4 : 4 * (Ks + (rk L : ℝ) * (Ks * Xs)) ≤
        4 * Ks + 4 * ((rk L : ℝ) * (Ks * Xs) * (1 + Real.log T)) := by
      have hle : (rk L : ℝ) * (Ks * Xs) ≤ (rk L : ℝ) * (Ks * Xs) * (1 + Real.log T) := by
        have hge1 : (1:ℝ) ≤ 1 + Real.log T := by linarith [Real.log_nonneg hT]
        have h1 : (rk L : ℝ) * (Ks * Xs) * 1
            ≤ (rk L : ℝ) * (Ks * Xs) * (1 + Real.log T) :=
          mul_le_mul_of_nonneg_left hge1 (mul_nonneg (by positivity) hnk)
        simpa using h1
      linarith [hle]
    have h3' : (∑ᶠ a ∈ Q, 1 / eNorm a) ≤
        4 * Ks + 4 * ((J:ℝ) + 1) * A 1 + 4 * (Ks + (rk L : ℝ) * (Ks * Xs)) := by
      rw [hA0v] at h3
      exact h3
    have hC : (∑ᶠ a ∈ Q, 1 / eNorm a) ≤
        8 * Ks + (16 * Ks + 4 * Ks * (rk L)) * ((1 + Real.log T) * Xs) := by
      have hexp : 8 * Ks + (16 * Ks + 4 * Ks * (rk L)) * ((1 + Real.log T) * Xs)
          = 8 * Ks + 16 * (1 + Real.log T) * (Ks * Xs)
            + 4 * ((rk L : ℝ) * (Ks * Xs) * (1 + Real.log T)) := by ring
      rw [hexp]
      linarith [h3', hA1', h4]
    have hD : 8 * Ks + (16 * Ks + 4 * Ks * (rk L)) * ((1 + Real.log T) * Xs) ≤
        K * ((1 + Real.log T) * Xs + 1) := by
      have h1 : 8 * Ks ≤ K := by rw [hKdef]; exact le_max_left _ _
      have h2 : 16 * Ks + 4 * Ks * (rk L) ≤ K := by
        rw [hKdef]
        refine le_trans ?_ (le_max_right _ _)
        have hcard : (rk L : ℝ) ≤ (Fintype.card ι : ℝ) := by
          exact_mod_cast Work.HP.rk_le_card L
        nlinarith [hKspos, hcard]
      have hnn : 0 ≤ (1 + Real.log T) * Xs := mul_nonneg hlog0 hXs0
      have h2' : (16 * Ks + 4 * Ks * (rk L)) * ((1 + Real.log T) * Xs)
          ≤ K * ((1 + Real.log T) * Xs) := mul_le_mul_of_nonneg_right h2 hnn
      rw [mul_add, mul_one]
      linarith [h1, h2']
    have hQeq : (∑ᶠ a ∈ Q, 1 / eNorm a)
        = (∑ᶠ a ∈ {a : ι → ℤ | a ∈ L ∧ a ≠ 0 ∧ eNorm a ≤ T}, 1 / eNorm a) := by
      rw [hQdef]
    rw [hQeq] at hC
    have hD' : 8 * Ks + (16 * Ks + 4 * Ks * (rk L)) * ((1 + Real.log T) * Xs)
        ≤ K * ((1 + Real.log T) * (T ^ (rk L - 1) + μ ^ (rk L - 1)) / detL L + 1) := by
      have heq : K * ((1 + Real.log T) * Xs + 1)
          = K * ((1 + Real.log T) * (T ^ (rk L - 1) + μ ^ (rk L - 1)) / detL L + 1) := by
        rw [hXsdef]; ring
      rw [heq] at hD
      exact hD
    exact le_trans hC hD'
theorem S1ball_degN (d n : ℕ) [DecidableEq (Work.HP.Mon d n)] (hd : 2 ≤ d) (hdn : d ≤ n) :
    ∃ K : ℝ, 0 < K ∧ ∀ x : Fin (n + 1) → ℤ, Work.HP.IsPrim x → ∀ T μ : ℝ, 1 ≤ T → 1 ≤ μ →
      Work.HP.MM2.lamX d n x ≤ μ →
      Work.HP.MM2.S1ball d n x T ≤
        K * ((1 + Real.log T) *
          (T ^ (Work.HP.NN d n - 2) + μ ^ (Work.HP.NN d n - 2)) /
          Work.HP.eNorm (Work.HP.veronese d n x) + 1) := by
  obtain ⟨K, hKpos, hK⟩ := sum_inv_eNorm_le_lam_last (ι := Mon d n)
  refine ⟨K, hKpos, ?_⟩
  intro x hx T μ hT hμ hlam
  have hcprim : IsPrim (veronese d n x) := isPrim_veronese d n (by omega) hx
  have hc0 : veronese d n x ≠ 0 := isPrim_ne_zero hcprim
  have hdet : detL (latOrth (veronese d n x)) = eNorm (veronese d n x) :=
    detL_latOrth _ hcprim
  have hrk : rk (latOrth (veronese d n x)) = NN d n - 1 := by
    rw [rk, Work.HP.Vero.finrank_latOrth _ hc0]
  have hν : lam (latOrth (veronese d n x)) (rk (latOrth (veronese d n x))) ≤ μ := by
    rw [hrk]
    exact hlam
  have h := hK (latOrth (veronese d n x)) T μ hT hμ hν
  have hgoal : S1ball d n x T
      = ∑ᶠ a ∈ {a : Mon d n → ℤ | a ∈ latOrth (veronese d n x) ∧ a ≠ 0 ∧ eNorm a ≤ T},
          1 / eNorm a := rfl
  rw [hgoal]
  refine le_trans h ?_
  rw [hrk, hdet]
  have hexp : NN d n - 1 - 1 = NN d n - 2 := by omega
  rw [hexp]

end Work.HP.MM2
