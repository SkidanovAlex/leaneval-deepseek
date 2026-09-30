import Mathlib
import Submission.Work.BMF.mr_direct.primePoly_large_values_window
import Submission.Work.BMF.mr_direct.wellspaced_cells
import Submission.Work.BMF.mr_core.badPartAux.primeHalasz
import Submission.Work.mr_core.badPartAux.largeValues_count_bound
import Submission.Work.BMF.mr_direct_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `Work.mr_core.badPartAux.bp_largeSumHalf`

Average square of a prime-supported Dirichlet polynomial on the large-values set.

Let `Q_{j,K}(1+it) = Σ_{e^{j/K} ≤ p ≤ e^{(j+1)/K}} g p · p^{-1-it}` (`Work.BMF.mrDirect.primePoly`)
be the short prime polynomial of the index `j`, and let `u ⊆ [-T',T']` be measurable with
`2T' ≤ exp(((j/K)/2)^{21/20})` and `log T' ≤ 2 log Y`.  If `(log Y)^{47/48} ≤ 2 j/K` then the
square mass of `Q_{j,K}` on the part of `u` where `|Q_{j,K}| ≥ Θ := (log Y)^{-100}` is at most
a constant times `K²/j²`.

Route (the paper's, MRTTZ Annals 2023 §"Mean and large value theorems"):
* cut `u ∩ {Θ ≤ ‖Q‖}` into cells of length 1 and take two families of 1-separated points
  (`Work.BMF.mr_direct.wellspaced_cells`);
* bound the number of such points by the large-values theorem for Dirichlet polynomials
  (`Work.BMF.mr_direct.primePoly_large_values_window`, the paper's Lemma `le:Rupest`) with
  `V = Θ^{-1} = (log Y)^{100}`, and kill the resulting exponential with
  `Work.mr_core.badPartAux.largeValues_count_bound`;
* bound the sum of `‖Q‖²` over the well-spaced points by Halász's inequality for primes
  (`Work.BMF.mr_direct.primePoly_halasz_vk`), whose `R·exp(-c (j/K)^{1/12})` error term is
  now `≤ 1`.
-/

set_option maxHeartbeats 2000000

open MeasureTheory Set
open scoped BigOperators

namespace Work.mr_core.badPartAux

private lemma continuous_cpow_aux {p : ℕ} (hp : p ≠ 0) :
    Continuous fun t : ℝ => (p : ℂ) ^ (-(1 + Complex.I * (t : ℂ))) := by
  have h : (fun t : ℝ => (p : ℂ) ^ (-(1 + Complex.I * (t : ℂ))))
      = fun t : ℝ => Complex.exp ((-(1 + Complex.I * (t : ℂ))) * Complex.log (p : ℂ)) := by
    funext t
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hp), mul_comm]
  rw [h]
  fun_prop

private lemma continuous_primePoly_aux (g : ℕ → ℂ) (K : ℝ) (j : ℕ) :
    Continuous fun t : ℝ => Work.BMF.mrDirect.primePoly g K j t := by
  unfold Work.BMF.mrDirect.primePoly
  refine continuous_finsetSum _ fun p hp => ?_
  rw [Finset.mem_filter] at hp
  exact Continuous.mul continuous_const (continuous_cpow_aux hp.2.ne_zero)

theorem bp_largeSumHalf :
    ∃ C Y₀ : ℝ, 0 < C ∧ 0 < Y₀ ∧
      ∀ (K : ℝ) (j : ℕ) (g : ℕ → ℂ) (Y T' Θ : ℝ) (u : Set ℝ),
        Y₀ ≤ Y → 2 ≤ K → (Real.log Y) ^ (47 / 48 : ℝ) ≤ 2 * ((j : ℝ) / K) →
        Real.exp 1 ≤ T' → Real.log T' ≤ 2 * Real.log Y →
        2 * T' ≤ Real.exp (((j : ℝ) / K / 2) ^ (21 / 20 : ℝ)) →
        (∀ p, ‖g p‖ ≤ 1) → Θ = (Real.log Y) ^ (-(100 : ℝ)) →
        MeasurableSet u → u ⊆ Set.Icc (-T') T' →
        (∫ t in u ∩ {t : ℝ | Θ ≤ ‖Work.BMF.mrDirect.primePoly g K j t‖},
            ‖Work.BMF.mrDirect.primePoly g K j t‖ ^ 2)
          ≤ C * K ^ 2 / (j : ℝ) ^ 2 := by
  obtain ⟨c, Ch, hc, hCh, hHal⟩ := Work.BMF.mr_direct.primePoly_halasz_vk
  obtain ⟨Clv, hClv, hLV⟩ := Work.BMF.mr_direct.primePoly_large_values_window
  obtain ⟨l₀, hl₀pos, hcount'⟩ := largeValues_count_bound c Clv hc hClv
  refine ⟨8 * Ch, Real.exp (max l₀ 100) + 100, by positivity, by positivity, ?_⟩
  intro K j g Y T' Θ u hY hK hlog hjT' hlogT' hT'exp hg hΘ hu hsub
  have hY0pos : (0 : ℝ) < Real.exp (max l₀ 100) + 100 := by positivity
  have hYpos : 0 < Y := lt_of_lt_of_le hY0pos hY
  have hlogY0 : max l₀ 100 ≤ Real.log (Real.exp (max l₀ 100) + 100) := by
    have h1 : Real.exp (max l₀ 100) ≤ Real.exp (max l₀ 100) + 100 :=
      le_add_of_nonneg_right (by norm_num)
    have h2 := Real.log_le_log (Real.exp_pos (max l₀ 100)) h1
    rwa [Real.log_exp] at h2
  have hlogY : max l₀ 100 ≤ Real.log Y :=
    le_trans hlogY0 (Real.log_le_log hY0pos hY)
  have hl100 : (100 : ℝ) ≤ Real.log Y := le_trans (le_max_right _ _) hlogY
  have hll₀ : l₀ ≤ Real.log Y := le_trans (le_max_left _ _) hlogY
  have hlpos : 0 < Real.log Y := by linarith
  have hKpos : 0 < K := by linarith
  let L : ℝ := (j : ℝ) / K
  have hLdef : L = (j : ℝ) / K := rfl
  have hLge : (Real.log Y) ^ (47 / 48 : ℝ) ≤ 2 * L := hlog
  have hLpos : 0 < L := by
    have h1 : (0 : ℝ) < (Real.log Y) ^ (47 / 48 : ℝ) := Real.rpow_pos_of_pos hlpos _
    linarith
  have hjpos : 0 < (j : ℝ) := by
    have hjnz : j ≠ 0 := by
      intro h
      have h0 : L = 0 := by
        show (j : ℝ) / K = 0
        rw [h]
        norm_num
      linarith [hLpos]
    exact_mod_cast Nat.pos_of_ne_zero hjnz
  have hL4 : 4 ≤ L := by
    have h8 : (8 : ℝ) ≤ (Real.log Y) ^ (47 / 48 : ℝ) := by
      have hsqrt : (8 : ℝ) ≤ Real.sqrt (Real.log Y) := by
        rw [Real.le_sqrt (by norm_num) (le_of_lt hlpos)]
        norm_num
        linarith
      calc (8 : ℝ) ≤ Real.sqrt (Real.log Y) := hsqrt
        _ = (Real.log Y) ^ (1 / 2 : ℝ) := (Real.sqrt_eq_rpow _)
        _ ≤ (Real.log Y) ^ (47 / 48 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
    linarith
  let V : ℝ := (Real.log Y) ^ (100 : ℝ)
  have hVdef : V = (Real.log Y) ^ (100 : ℝ) := rfl
  have hV1 : (1 : ℝ) ≤ V := by
    have h := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1)
      (by linarith : (1 : ℝ) ≤ Real.log Y) (by norm_num : (0 : ℝ) ≤ 100)
    rwa [Real.one_rpow] at h
  have hΘpos : 0 < Θ := by
    rw [hΘ]
    positivity
  have hΘV : 1 / V = Θ := by
    rw [one_div, hVdef]
    rw [← Real.rpow_neg (le_of_lt hlpos) (100 : ℝ)]
    exact hΘ.symm
  let Q : ℝ → ℂ := fun t => Work.BMF.mrDirect.primePoly g K j t
  have hQdef : Q = fun t => Work.BMF.mrDirect.primePoly g K j t := rfl
  have hcont : Continuous Q := continuous_primePoly_aux g K j
  have hcont2 : Continuous fun t : ℝ => ‖Q t‖ ^ 2 := hcont.norm.pow 2
  let T : ℝ := max T' 3
  have hTdef : T = max T' 3 := rfl
  have hT3 : 3 ≤ T := by rw [hTdef]; exact le_max_right _ _
  have hTT' : T' ≤ T := by rw [hTdef]; exact le_max_left _ _
  have hlogT_le : Real.log T ≤ 2 * Real.log Y := by
    rw [hTdef]
    rcases le_or_gt T' 3 with h | h
    · rw [max_eq_right h]
      have h3 : Real.log 3 < 2 := by
        have := Real.log_lt_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num) (by norm_num)
        linarith
      linarith
    · rw [max_eq_left (le_of_lt h)]
      exact hlogT'
  have h2T : 2 * T ≤ Real.exp ((L / 2) ^ (21 / 20 : ℝ)) := by
    have h6 : (6 : ℝ) ≤ Real.exp ((L / 2) ^ (21 / 20 : ℝ)) := by
      have hbase : (2 : ℝ) ≤ L / 2 := by linarith
      have hexp2 : (2 : ℝ) ≤ (L / 2) ^ (21 / 20 : ℝ) := by
        calc (2 : ℝ) ≤ L / 2 := hbase
          _ = (L / 2) ^ (1 : ℝ) := (Real.rpow_one _).symm
          _ ≤ (L / 2) ^ (21 / 20 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
      have hexp : (6 : ℝ) ≤ Real.exp 2 := by
        have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
          rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
        rw [h2]
        nlinarith [Real.exp_one_gt_d9]
      exact le_trans hexp (Real.exp_le_exp.mpr hexp2)
    rw [hTdef]
    rcases le_or_gt T' 3 with h | h
    · rw [max_eq_right h]; linarith
    · rw [max_eq_left (le_of_lt h)]; exact hT'exp
  let U : Set ℝ := u ∩ {t : ℝ | Θ ≤ ‖Q t‖}
  have hUdef : U = u ∩ {t : ℝ | Θ ≤ ‖Q t‖} := rfl
  have hUmeas : MeasurableSet U := by
    refine hu.inter ?_
    exact (isClosed_le continuous_const hcont.norm).measurableSet
  have hUsub : U ⊆ Set.Icc (-T) T := by
    intro t ht
    obtain ⟨htu, _⟩ := ht
    obtain ⟨h1, h2⟩ := hsub htu
    exact ⟨by linarith, by linarith⟩
  obtain ⟨R₁, R₂, t₁, t₂, hmem₁, hmem₂, hsep₁, hsep₂, hint⟩ :=
    Work.BMF.mr_direct.wellspaced_cells (fun t : ℝ => ‖Q t‖ ^ 2) hcont2
      (fun x => by positivity) (by linarith : -T ≤ T) hUmeas hUsub
  have key : ∀ (R : ℕ) (t : Fin R → ℝ),
      (∀ i j : Fin R, i ≠ j → 1 ≤ |t i - t j|) → (∀ i, t i ∈ U) →
      ∑ i, ‖Q (t i)‖ ^ 2 ≤ 2 * Ch / L ^ 2 := by
    intro R t hsep hmem
    have hIcc : ∀ i, t i ∈ Set.Icc (-T) T := fun i => hUsub (hmem i)
    have hval : ∀ i, Θ ≤ ‖Q (t i)‖ := fun i => (hmem i).2
    have hval' : ∀ i, 1 / V ≤ ‖∑ p ∈ (Finset.Icc ⌈Real.exp ((j : ℝ) / K)⌉₊
        ⌊Real.exp (((j : ℝ) + 1) / K)⌋₊).filter Nat.Prime,
        g p * (p : ℂ) ^ (-(1 + Complex.I * ((t i : ℝ) : ℂ)))‖ := by
      intro i
      rw [hΘV]
      exact hval i
    have hA2 : (2 : ℝ) ≤ Real.exp ((j : ℝ) / K) := by
      have h4 : (2 : ℝ) ≤ Real.exp 4 := by
        have h2 : (2 : ℝ) ≤ Real.exp 1 := by
          have := Real.add_one_le_exp (1 : ℝ); linarith
        exact le_trans h2 (Real.exp_le_exp.mpr (by norm_num))
      exact le_trans h4 (Real.exp_le_exp.mpr (by linarith))
    have hAB : Real.exp ((j : ℝ) / K) ≤ Real.exp (((j : ℝ) + 1) / K) :=
      Real.exp_le_exp.mpr (by
        rw [div_le_div_iff_of_pos_right hKpos]; linarith)
    have hB4 : Real.exp (((j : ℝ) + 1) / K) ≤ 4 * Real.exp ((j : ℝ) / K) := by
      have hsp : ((j : ℝ) + 1) / K = (j : ℝ) / K + 1 / K := by ring
      rw [hsp, Real.exp_add]
      have h1 : Real.exp (1 / K) ≤ 4 := by
        have h2 : (1 : ℝ) / K ≤ 1 := by rw [div_le_one hKpos]; linarith
        calc Real.exp (1 / K) ≤ Real.exp 1 := Real.exp_le_exp.mpr h2
          _ ≤ 4 := by have := Real.exp_one_lt_three; linarith
      nlinarith [Real.exp_pos ((j : ℝ) / K)]
    have hR := hLV (Real.exp ((j : ℝ) / K)) (Real.exp (((j : ℝ) + 1) / K)) V T R t g
        hA2 hAB hB4 hT3 hV1 hg hsep hIcc hval'
    rw [Real.log_exp] at hR
    have hcv := hcount' (Real.log Y) T L V hV1 (le_of_eq hVdef) hll₀ hLge hT3 hlogT_le
    have hRexp : (R : ℝ) * Real.exp (-c * L ^ (1 / 12 : ℝ)) ≤ 1 := by
      calc (R : ℝ) * Real.exp (-c * L ^ (1 / 12 : ℝ))
          ≤ (Clv * (T ^ (2 * Real.log V / L) * V ^ 2 *
              Real.exp (2 * (Real.log T / L) * Real.log (Real.log T))))
              * Real.exp (-c * L ^ (1 / 12 : ℝ)) :=
            mul_le_mul_of_nonneg_right hR (Real.exp_pos _).le
        _ = Clv * T ^ (2 * Real.log V / L) * V ^ 2 *
              Real.exp (2 * (Real.log T / L) * Real.log (Real.log T))
              * Real.exp (-c * L ^ (1 / 12 : ℝ)) := by ring
        _ ≤ 1 := hcv
    have h1 : (∑ i, ‖Q (t i)‖ ^ 2) ≤
        Ch * (1 + (R : ℝ) * Real.exp (-c * L ^ (1 / 12 : ℝ))) / L ^ 2 := by
      have h0 := hHal K j T R t g hK hL4 hT3 h2T hg hsep hIcc
      exact h0
    calc ∑ i, ‖Q (t i)‖ ^ 2
        ≤ Ch * (1 + (R : ℝ) * Real.exp (-c * L ^ (1 / 12 : ℝ))) / L ^ 2 := h1
      _ ≤ Ch * (1 + 1) / L ^ 2 := by
          apply div_le_div_of_nonneg_right ?_ (by positivity)
          apply mul_le_mul_of_nonneg_left ?_ hCh.le
          linarith
      _ = 2 * Ch / L ^ 2 := by ring
  have hb₁ := key R₁ t₁ hsep₁ hmem₁
  have hb₂ := key R₂ t₂ hsep₂ hmem₂
  have hgoal : (∫ t in u ∩ {t : ℝ | Θ ≤ ‖Work.BMF.mrDirect.primePoly g K j t‖},
      ‖Work.BMF.mrDirect.primePoly g K j t‖ ^ 2) = ∫ x in U, ‖Q x‖ ^ 2 := rfl
  rw [hgoal]
  have hfinal : 8 * Ch / L ^ 2 = 8 * Ch * K ^ 2 / (j : ℝ) ^ 2 := by
    have hjne : (j : ℝ) ≠ 0 := ne_of_gt hjpos
    have hKne : K ≠ 0 := ne_of_gt hKpos
    rw [hLdef, div_pow]
    field_simp
  calc (∫ x in U, ‖Q x‖ ^ 2) ≤ 8 * Ch / L ^ 2 := by
        calc (∫ x in U, ‖Q x‖ ^ 2)
            ≤ 2 * ((∑ i, ‖Q (t₁ i)‖ ^ 2) + (∑ i, ‖Q (t₂ i)‖ ^ 2)) := hint
          _ ≤ 2 * (2 * Ch / L ^ 2 + 2 * Ch / L ^ 2) := by linarith
          _ = 8 * Ch / L ^ 2 := by ring
    _ = 8 * Ch * K ^ 2 / (j : ℝ) ^ 2 := hfinal

end Work.mr_core.badPartAux
