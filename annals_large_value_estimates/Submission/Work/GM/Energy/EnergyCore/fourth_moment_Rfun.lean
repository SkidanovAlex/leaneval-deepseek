import Mathlib
import Submission.Work.GM.Energy.Defs
import Submission.Work.GM.Energy.EnergyCore.FourthMomentDefs
import Submission.Work.GM.Energy.EnergyCore.normSq_smoothedPoly_eq
import Submission.Work.GM.Energy.EnergyCore.locality_Gsum
import Submission.Work.GM.Energy.EnergyCore.class_bounds
import Submission.Work.GM.Energy.EnergyCore.Rfun_pow4_le_sum_Zclass
import Submission.Work.GM.Energy.EnergyCore.clsNum_sq_bound
import Submission.Work.GM.Energy.EnergyCore.per_class_arith
import Submission.Work.GM.Energy.EnergyCore.arith_final

namespace Work.GM.Energy.EnergyCore

open Complex Finset MeasureTheory
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1000000

section Algebra

/-- `conj (x^{iτ}) = x^{-iτ}` for `x > 0` real. -/
lemma conj_cpow_ofReal_I {x : ℝ} (hx : 0 < x) (τ : ℝ) :
    (starRingEnd ℂ) ((x : ℂ) ^ (Complex.I * (τ : ℂ)))
      = (x : ℂ) ^ (Complex.I * ((-τ : ℝ) : ℂ)) := by
  have harg : ((x : ℂ)).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg hx.le]
    exact Real.pi_ne_zero.symm
  have h := Complex.cpow_conj ((x : ℂ)) (Complex.I * (τ : ℂ)) harg
  rw [Complex.conj_ofReal] at h
  rw [← h]
  congr 1
  rw [map_mul, Complex.conj_I, Complex.conj_ofReal]
  push_cast
  ring

/-- The sum over ratios `n₁/n₂` is the squared modulus of `Gsum`. -/
lemma ratio_cpow_sum (M : ℕ) (hM : 1 ≤ M) (τ : ℝ) :
    (∑ n1 ∈ Finset.Icc M (2 * M), ∑ n2 ∈ Finset.Icc M (2 * M),
        ((((n1 : ℝ) / (n2 : ℝ)) : ℝ) : ℂ) ^ (Complex.I * (τ : ℂ)))
      = ((Complex.normSq (Gsum M τ) : ℝ) : ℂ) := by
  have h1 : ∀ n1 n2 : ℕ, ((((n1 : ℝ) / (n2 : ℝ)) : ℝ) : ℂ) ^ (Complex.I * (τ : ℂ))
      = (n1 : ℂ) ^ (Complex.I * (τ : ℂ))
          * (starRingEnd ℂ) ((n2 : ℂ) ^ (Complex.I * (τ : ℂ))) := by
    intro n1 n2
    have hbase : ((((n1 : ℝ) / (n2 : ℝ)) : ℝ) : ℂ) = (((n1 : ℝ) / (n2 : ℝ)) : ℂ) := by
      rw [Complex.ofReal_div]
    rw [hbase, ← cpow_mul_conj_cpow n1 n2 τ]
  rw [Finset.sum_congr rfl (fun n1 _ => Finset.sum_congr rfl (fun n2 _ => h1 n1 n2))]
  have h2 : (∑ n1 ∈ Finset.Icc M (2 * M), ∑ n2 ∈ Finset.Icc M (2 * M),
        (n1 : ℂ) ^ (Complex.I * (τ : ℂ)) * (starRingEnd ℂ) ((n2 : ℂ) ^ (Complex.I * (τ : ℂ))))
      = (∑ n1 ∈ Finset.Icc M (2 * M), (n1 : ℂ) ^ (Complex.I * (τ : ℂ)))
          * (starRingEnd ℂ) (∑ n2 ∈ Finset.Icc M (2 * M),
              (n2 : ℂ) ^ (Complex.I * (τ : ℂ))) := by
    rw [map_sum]
    rw [← Finset.sum_mul_sum]
  rw [h2, ← Complex.mul_conj]
  rfl

/-- The squared modulus of `Zclass` expanded as a four-fold sum. -/
lemma ofReal_normSq_Zclass (W : Finset ℝ) (U : Finset ℤ) {x : ℝ} (hx : 0 < x) :
    ((Complex.normSq (Zclass W U x) : ℝ) : ℂ)
      = ∑ u1 ∈ U, ∑ u2 ∈ U, ∑ p ∈ repPairs W u1, ∑ q ∈ repPairs W u2,
          (x : ℂ) ^ (Complex.I * (((p.1 - p.2) - (q.1 - q.2) : ℝ) : ℂ)) := by
  have hxne : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have hconj : (starRingEnd ℂ) (Zclass W U x)
      = ∑ u ∈ U, ∑ p ∈ repPairs W u,
          (x : ℂ) ^ (Complex.I * ((-(p.1 - p.2) : ℝ) : ℂ)) := by
    rw [Zclass, map_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [map_sum]
    exact Finset.sum_congr rfl fun p _ => conj_cpow_ofReal_I hx _
  rw [← Complex.mul_conj (Zclass W U x), hconj, Zclass, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun u1 _ => Finset.sum_congr rfl fun u2 _ => ?_
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  rw [← Complex.cpow_add _ _ hxne]
  congr 1
  push_cast
  ring

/-- Swapping the `(n₁,n₂)` block of a sum with the `(u₁,u₂,p,q)` block, where `p` (resp. `q`)
runs over the pairs with key `u₁` (resp. `u₂`). -/
lemma swap_blocks (s : Finset ℕ) (U : Finset ℤ) (W : Finset ℝ)
    (F : ℕ → ℕ → ℤ → ℤ → ℝ × ℝ → ℝ × ℝ → ℂ) :
    (∑ n1 ∈ s, ∑ n2 ∈ s, ∑ u1 ∈ U, ∑ u2 ∈ U, ∑ p ∈ repPairs W u1, ∑ q ∈ repPairs W u2,
        F n1 n2 u1 u2 p q)
      = ∑ u1 ∈ U, ∑ u2 ∈ U, ∑ p ∈ repPairs W u1, ∑ q ∈ repPairs W u2,
          ∑ n1 ∈ s, ∑ n2 ∈ s, F n1 n2 u1 u2 p q := by
  conv_lhs => enter [2, n1]; rw [Finset.sum_comm]
  conv_lhs => enter [2, n1, 2, u1]; rw [Finset.sum_comm]
  conv_lhs => enter [2, n1, 2, u1, 2, u2]; rw [Finset.sum_comm]
  conv_lhs => enter [2, n1, 2, u1, 2, u2, 2, p]; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  conv_lhs => enter [2, u1]; rw [Finset.sum_comm]
  conv_lhs => enter [2, u1, 2, u2]; rw [Finset.sum_comm]
  conv_lhs => enter [2, u1, 2, u2, 2, p]; rw [Finset.sum_comm]

/-- **The class sum identity**: the second moment over `n₁,n₂ ∈ [M,2M]` of `‖Zclass‖²` equals the
four-fold sum of `normSq (Gsum M τ)` over the key-differences `τ = (t₁-t₂)-(t₃-t₄)`. -/
lemma sum_normSq_Zclass_eq (M : ℕ) (hM : 1 ≤ M) (W : Finset ℝ) (U : Finset ℤ) :
    (∑ n1 ∈ Finset.Icc M (2 * M), ∑ n2 ∈ Finset.Icc M (2 * M),
        Complex.normSq (Zclass W U ((n1 : ℝ) / (n2 : ℝ))))
      = ∑ u1 ∈ U, ∑ u2 ∈ U, ∑ p ∈ repPairs W u1, ∑ q ∈ repPairs W u2,
          Complex.normSq (Gsum M ((p.1 - p.2) - (q.1 - q.2))) := by
  have hpos : ∀ n ∈ Finset.Icc M (2 * M), (0 : ℝ) < n := by
    intro n hn
    have h1 : M ≤ n := (Finset.mem_Icc.mp hn).1
    exact_mod_cast lt_of_lt_of_le (by omega : 0 < M) h1
  have hA : (((∑ n1 ∈ Finset.Icc M (2 * M), ∑ n2 ∈ Finset.Icc M (2 * M),
        Complex.normSq (Zclass W U ((n1 : ℝ) / (n2 : ℝ)))) : ℝ) : ℂ)
      = ∑ n1 ∈ Finset.Icc M (2 * M), ∑ n2 ∈ Finset.Icc M (2 * M),
          ∑ u1 ∈ U, ∑ u2 ∈ U, ∑ p ∈ repPairs W u1, ∑ q ∈ repPairs W u2,
            ((((n1 : ℝ) / (n2 : ℝ)) : ℝ) : ℂ) ^
              (Complex.I * ((((p.1 - p.2) - (q.1 - q.2) : ℝ)) : ℂ)) := by
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun n1 hn1 => ?_
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun n2 hn2 => ?_
    exact ofReal_normSq_Zclass W U (div_pos (hpos n1 hn1) (hpos n2 hn2))
  have hB : (∑ n1 ∈ Finset.Icc M (2 * M), ∑ n2 ∈ Finset.Icc M (2 * M),
          ∑ u1 ∈ U, ∑ u2 ∈ U, ∑ p ∈ repPairs W u1, ∑ q ∈ repPairs W u2,
            ((((n1 : ℝ) / (n2 : ℝ)) : ℝ) : ℂ) ^
              (Complex.I * ((((p.1 - p.2) - (q.1 - q.2) : ℝ)) : ℂ)))
      = ∑ u1 ∈ U, ∑ u2 ∈ U, ∑ p ∈ repPairs W u1, ∑ q ∈ repPairs W u2,
          ∑ n1 ∈ Finset.Icc M (2 * M), ∑ n2 ∈ Finset.Icc M (2 * M),
            ((((n1 : ℝ) / (n2 : ℝ)) : ℝ) : ℂ) ^
              (Complex.I * ((((p.1 - p.2) - (q.1 - q.2) : ℝ)) : ℂ)) :=
    swap_blocks _ U W _
  have hC : (∑ u1 ∈ U, ∑ u2 ∈ U, ∑ p ∈ repPairs W u1, ∑ q ∈ repPairs W u2,
          ∑ n1 ∈ Finset.Icc M (2 * M), ∑ n2 ∈ Finset.Icc M (2 * M),
            ((((n1 : ℝ) / (n2 : ℝ)) : ℝ) : ℂ) ^
              (Complex.I * ((((p.1 - p.2) - (q.1 - q.2) : ℝ)) : ℂ)))
      = ∑ u1 ∈ U, ∑ u2 ∈ U, ∑ p ∈ repPairs W u1, ∑ q ∈ repPairs W u2,
          ((Complex.normSq (Gsum M ((p.1 - p.2) - (q.1 - q.2))) : ℝ) : ℂ) := by
    refine Finset.sum_congr rfl fun u1 _ => Finset.sum_congr rfl fun u2 _ =>
      Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    exact ratio_cpow_sum M hM _
  have hD : (∑ u1 ∈ U, ∑ u2 ∈ U, ∑ p ∈ repPairs W u1, ∑ q ∈ repPairs W u2,
          ((Complex.normSq (Gsum M ((p.1 - p.2) - (q.1 - q.2))) : ℝ) : ℂ))
      = (((∑ u1 ∈ U, ∑ u2 ∈ U, ∑ p ∈ repPairs W u1, ∑ q ∈ repPairs W u2,
          Complex.normSq (Gsum M ((p.1 - p.2) - (q.1 - q.2)))) : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun u1 _ => ?_
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun u2 _ => ?_
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Complex.ofReal_sum]
  exact Complex.ofReal_inj.mp (hA.trans (hB.trans (hC.trans hD)))

/-- Keys of pairs from `W ⊆ [0,T]` are bounded by `T + 1` in absolute value. -/
lemma abs_key_le {W : Finset ℝ} {T : ℝ} (hWsub : ∀ t ∈ W, t ∈ Set.Icc 0 T) {u : ℤ}
    (hu : u ∈ keySet W) : |(u : ℝ)| ≤ T + 1 := by
  obtain ⟨p, hp, hpu⟩ := mem_keySet.mp hu
  have hp' := mem_pairSet.mp hp
  have h1 := hWsub p.1 hp'.1
  have h2 := hWsub p.2 hp'.2
  have hup : (u : ℝ) = ((pkey p : ℤ) : ℝ) := by rw [hpu]
  have hle : (u : ℝ) ≤ T := by
    rw [hup]
    have h3 : p.1 - p.2 ≤ T := by linarith [h1.2, h2.1]
    have h4 : pkey p ≤ ⌊T⌋ := by
      rw [pkey]; exact Int.floor_mono h3
    have h5 : ((⌊T⌋ : ℤ) : ℝ) ≤ T := Int.floor_le T
    exact le_trans (by exact_mod_cast h4) h5
  have hge : -T - 1 ≤ (u : ℝ) := by
    rw [hup]
    have h3 : -T ≤ p.1 - p.2 := by linarith [h1.1, h2.2]
    have h4 : ⌊(-T)⌋ ≤ pkey p := by
      rw [pkey]; exact Int.floor_mono h3
    have h5 : -T - 1 ≤ ((⌊(-T)⌋ : ℤ) : ℝ) := by
      have := Int.lt_floor_add_one (-T); linarith
    exact le_trans h5 (by exact_mod_cast h4)
  rw [abs_le]
  constructor
  · linarith
  · linarith

/-- Interchange of a double sum over `(n₁,n₂)` with a sum over `j`. -/
lemma sum_swap_nn_j (s : Finset ℕ) (J : ℕ) (F : ℕ → ℕ → ℕ → ℝ) :
    (∑ n1 ∈ s, ∑ n2 ∈ s, ∑ j ∈ Finset.range J, F n1 n2 j)
      = ∑ j ∈ Finset.range J, ∑ n1 ∈ s, ∑ n2 ∈ s, F n1 n2 j := by
  conv_lhs => enter [2, n1]; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]

/-- Reindexing a sum over a `Finset ℤ` as a sum over `Fin U.card` via the canonical equivalence. -/
lemma sum_finset_eq_sum_fin (U : Finset ℤ) (f : ℤ → ℝ) :
    (∑ u ∈ U, f u) = ∑ i : Fin U.card, f ((Finset.equivFin U).symm i).1 := by
  rw [← Finset.sum_attach U f]
  refine Finset.sum_equiv (Finset.equivFin U) (fun i => ?_) (fun i _ => ?_)
  · simp
  · simp

/-- The norm of `n^{is}` is at most `1`. -/
lemma norm_natCast_cpow_le_one (n : ℕ) (s : ℝ) :
    ‖(n : ℂ) ^ (Complex.I * (s : ℂ))‖ ≤ 1 := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    rw [Nat.cast_zero]
    by_cases hs : Complex.I * (s : ℂ) = 0
    · rw [hs, Complex.cpow_zero]; simp
    · rw [Complex.zero_cpow hs]; simp
  · have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    rw [show (n : ℂ) = ((n : ℝ) : ℂ) by simp,
      Complex.norm_cpow_eq_rpow_re_of_pos hn']
    simp

/-- **Heath-Brown on a `1`-separated integer set with a shift absorbed into the coefficients.** -/
theorem HB_Gsum_shift_self (hHB : Submission.GM.HBStatement) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (M : ℕ), 1 ≤ M → ∀ (T : ℝ), 1 ≤ T → ∀ (K : ℝ), 1 ≤ K →
      ∀ (U : Finset ℤ), (∀ u ∈ U, |(u : ℝ)| ≤ T) →
      ∑ u1 ∈ U, ∑ u2 ∈ U,
          (∫ u in (u1 : ℝ) - (u2 : ℝ) - 2 * K..(u1 : ℝ) - (u2 : ℝ) + 2 * K, ‖Gsum M u‖ ^ 2)
        ≤ K * C * (2 * T) ^ ε * ((U.card : ℝ) ^ 2 * (M : ℝ) + (U.card : ℝ) * (M : ℝ) ^ 2
            + (2 * T) ^ ((1 : ℝ) / 2) * (U.card : ℝ) ^ ((5 : ℝ) / 4) * (M : ℝ)) := by
  obtain ⟨Chb, hChbpos, hHBc⟩ := hHB ε hε
  refine ⟨4 * Chb, by positivity, ?_⟩
  intro M hM T hT K hK U hU
  have hK0 : (0 : ℝ) ≤ K := le_trans zero_le_one hK
  have hT0 : (0 : ℝ) ≤ T := le_trans zero_le_one hT
  -- Heath-Brown at every shift
  have hbound : ∀ s : ℝ, (∑ u1 ∈ U, ∑ u2 ∈ U, ‖Gsum M ((u1 : ℝ) - (u2 : ℝ) + s)‖ ^ 2)
      ≤ Chb * (2 * T) ^ ε * ((U.card : ℝ) ^ 2 * (M : ℝ) + (U.card : ℝ) * (M : ℝ) ^ 2
          + (U.card : ℝ) ^ ((5 : ℝ) / 4) * (2 * T) ^ ((1 : ℝ) / 2) * (M : ℝ)) := by
    intro s
    let v : Fin U.card → ℤ := fun i => ((Finset.equivFin U).symm i).1
    have hv_mem : ∀ i : Fin U.card, v i ∈ U := fun i => ((Finset.equivFin U).symm i).2
    have ht_mem : ∀ i : Fin U.card, ((v i : ℝ) + T) ∈ Set.Icc 0 (2 * T) := by
      intro i
      have h := hU (v i) (hv_mem i)
      rw [abs_le] at h
      exact ⟨by linarith [h.1], by linarith [h.2]⟩
    have ht_sep : ∀ i j : Fin U.card, i ≠ j → 1 ≤ |((v i : ℝ) + T) - ((v j : ℝ) + T)| := by
      intro i j hij
      have hne : v i ≠ v j := by
        intro h
        exact hij ((Finset.equivFin U).symm.injective (Subtype.ext h))
      have h1 : (1 : ℤ) ≤ |v i - v j| := by
        have h2 : (0 : ℤ) < |v i - v j| := abs_pos.mpr (sub_ne_zero.mpr hne)
        omega
      have hcast : ((v i : ℝ) + T) - ((v j : ℝ) + T) = ((v i : ℝ) - (v j : ℝ)) := by ring
      rw [hcast]
      exact_mod_cast h1
    have hHBapp := hHBc M hM (2 * T) (by linarith)
      (fun n => (n : ℂ) ^ (Complex.I * (s : ℂ))) (fun n => norm_natCast_cpow_le_one n s)
      U.card (fun i => (v i : ℝ) + T) ht_mem ht_sep
    -- the pointwise complex identity
    have hpt : ∀ i j : Fin U.card,
        (∑ n ∈ Finset.Icc M (2 * M), (n : ℂ) ^ (Complex.I * (s : ℂ))
            * (n : ℂ) ^ (Complex.I * ((((v i : ℝ) + T) - ((v j : ℝ) + T) : ℝ) : ℂ)))
          = Gsum M ((v i : ℝ) - (v j : ℝ) + s) := by
      intro i j
      rw [Gsum]
      refine Finset.sum_congr rfl fun n hn => ?_
      have hn1 : 1 ≤ n := le_trans hM (Finset.mem_Icc.mp hn).1
      have hnz : (n : ℂ) ≠ 0 := by
        have : (0 : ℕ) < n := lt_of_lt_of_le (by norm_num) hn1
        exact_mod_cast this.ne'
      rw [← Complex.cpow_add _ _ hnz]
      congr 1
      push_cast
      ring
    -- reindex the sums
    have hLHS : (∑ u1 ∈ U, ∑ u2 ∈ U, ‖Gsum M ((u1 : ℝ) - (u2 : ℝ) + s)‖ ^ 2)
        = ∑ i : Fin U.card, ∑ j : Fin U.card, ‖Gsum M ((v i : ℝ) - (v j : ℝ) + s)‖ ^ 2 := by
      rw [sum_finset_eq_sum_fin U (fun u1 => ∑ u2 ∈ U, ‖Gsum M ((u1 : ℝ) - (u2 : ℝ) + s)‖ ^ 2)]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [sum_finset_eq_sum_fin U (fun u2 => ‖Gsum M ((v i : ℝ) - (u2 : ℝ) + s)‖ ^ 2)]
    calc (∑ u1 ∈ U, ∑ u2 ∈ U, ‖Gsum M ((u1 : ℝ) - (u2 : ℝ) + s)‖ ^ 2)
        = ∑ i : Fin U.card, ∑ j : Fin U.card, ‖Gsum M ((v i : ℝ) - (v j : ℝ) + s)‖ ^ 2 := hLHS
      _ = ∑ i : Fin U.card, ∑ j : Fin U.card,
            ‖∑ n ∈ Finset.Icc M (2 * M), (n : ℂ) ^ (Complex.I * (s : ℂ))
              * (n : ℂ) ^ (Complex.I * ((((v i : ℝ) + T) - ((v j : ℝ) + T) : ℝ) : ℂ))‖ ^ 2 := by
            refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
            rw [hpt i j]
      _ ≤ Chb * (2 * T) ^ ε * ((U.card : ℝ) ^ 2 * (M : ℝ) + (U.card : ℝ) * (M : ℝ) ^ 2
          + (U.card : ℝ) ^ ((5 : ℝ) / 4) * (2 * T) ^ ((1 : ℝ) / 2) * (M : ℝ)) := hHBapp
  -- change of variables in each inner integral
  have hcv : ∀ u1 u2 : ℤ,
      (∫ u in (u1 : ℝ) - (u2 : ℝ) - 2 * K..(u1 : ℝ) - (u2 : ℝ) + 2 * K, ‖Gsum M u‖ ^ 2)
        = ∫ σ in (-2 * K)..(2 * K), ‖Gsum M ((u1 : ℝ) - (u2 : ℝ) + σ)‖ ^ 2 := by
    intro u1 u2
    have hb1 : (u1 : ℝ) - (u2 : ℝ) - 2 * K = ((u1 : ℝ) - (u2 : ℝ)) + (-2 * K) := by ring
    have hb2 : (u1 : ℝ) - (u2 : ℝ) + 2 * K = ((u1 : ℝ) - (u2 : ℝ)) + (2 * K) := by ring
    rw [hb1, hb2, ← intervalIntegral.integral_comp_add_left (fun u : ℝ => ‖Gsum M u‖ ^ 2) ((u1 : ℝ) - (u2 : ℝ))]
  have hcont : Continuous fun u : ℝ => ‖Gsum M u‖ ^ 2 := (continuous_Gsum hM).norm.pow 2
  have hcont2 : ∀ u1 : ℤ, Continuous fun σ : ℝ => ∑ u2 ∈ U,
      ‖Gsum M ((u1 : ℝ) - (u2 : ℝ) + σ)‖ ^ 2 := by
    intro u1
    refine continuous_finsetSum _ fun u2 _ => ?_
    exact (hcont.comp (by fun_prop))
  -- swap the sums and the integral
  have hswap : (∑ u1 ∈ U, ∑ u2 ∈ U,
        ∫ σ in (-2 * K)..(2 * K), ‖Gsum M ((u1 : ℝ) - (u2 : ℝ) + σ)‖ ^ 2)
      = ∫ σ in (-2 * K)..(2 * K), ∑ u1 ∈ U, ∑ u2 ∈ U,
          ‖Gsum M ((u1 : ℝ) - (u2 : ℝ) + σ)‖ ^ 2 := by
    have h1 : (∑ u1 ∈ U, ∑ u2 ∈ U,
          ∫ σ in (-2 * K)..(2 * K), ‖Gsum M ((u1 : ℝ) - (u2 : ℝ) + σ)‖ ^ 2)
        = ∑ u1 ∈ U, ∫ σ in (-2 * K)..(2 * K), ∑ u2 ∈ U,
            ‖Gsum M ((u1 : ℝ) - (u2 : ℝ) + σ)‖ ^ 2 := by
      refine Finset.sum_congr rfl fun u1 _ => ?_
      exact (intervalIntegral.integral_finsetSum (μ := volume) (a := -2 * K) (b := 2 * K)
        (f := fun u2 : ℤ => fun σ : ℝ => ‖Gsum M ((u1 : ℝ) - (u2 : ℝ) + σ)‖ ^ 2)
        (h := fun u2 _ => ((hcont.comp (by fun_prop)).intervalIntegrable (-2 * K) (2 * K)))).symm
    rw [h1, ← intervalIntegral.integral_finsetSum (μ := volume) (a := -2 * K) (b := 2 * K)
      (f := fun u1 : ℤ => fun σ : ℝ => ∑ u2 ∈ U, ‖Gsum M ((u1 : ℝ) - (u2 : ℝ) + σ)‖ ^ 2)
      (h := fun u1 _ => (hcont2 u1).intervalIntegrable (-2 * K) (2 * K))]
  have hint : IntervalIntegrable (fun σ : ℝ => ∑ u1 ∈ U, ∑ u2 ∈ U,
      ‖Gsum M ((u1 : ℝ) - (u2 : ℝ) + σ)‖ ^ 2) volume (-2 * K) (2 * K) :=
    (continuous_finsetSum _ fun u1 _ => hcont2 u1).intervalIntegrable _ _
  calc (∑ u1 ∈ U, ∑ u2 ∈ U,
        ∫ u in (u1 : ℝ) - (u2 : ℝ) - 2 * K..(u1 : ℝ) - (u2 : ℝ) + 2 * K, ‖Gsum M u‖ ^ 2)
      = ∑ u1 ∈ U, ∑ u2 ∈ U,
          ∫ σ in (-2 * K)..(2 * K), ‖Gsum M ((u1 : ℝ) - (u2 : ℝ) + σ)‖ ^ 2 := by
        refine Finset.sum_congr rfl fun u1 _ => Finset.sum_congr rfl fun u2 _ => hcv u1 u2
    _ = ∫ σ in (-2 * K)..(2 * K), ∑ u1 ∈ U, ∑ u2 ∈ U,
          ‖Gsum M ((u1 : ℝ) - (u2 : ℝ) + σ)‖ ^ 2 := hswap
    _ ≤ ∫ _σ in (-2 * K)..(2 * K), Chb * (2 * T) ^ ε * ((U.card : ℝ) ^ 2 * (M : ℝ)
          + (U.card : ℝ) * (M : ℝ) ^ 2
          + (U.card : ℝ) ^ ((5 : ℝ) / 4) * (2 * T) ^ ((1 : ℝ) / 2) * (M : ℝ)) := by
        refine intervalIntegral.integral_mono_on (by linarith) hint
          (intervalIntegrable_const) (fun σ _ => hbound σ)
    _ = K * (4 * Chb) * (2 * T) ^ ε * ((U.card : ℝ) ^ 2 * (M : ℝ) + (U.card : ℝ) * (M : ℝ) ^ 2
            + (2 * T) ^ ((1 : ℝ) / 2) * (U.card : ℝ) ^ ((5 : ℝ) / 4) * (M : ℝ)) := by
        rw [intervalIntegral.integral_const, smul_eq_mul]
        ring

/-- A range statement: every key `u ∈ U` has at most `2B` representations. -/
def KeyBound (W : Finset ℝ) (U : Finset ℤ) (B : ℝ) : Prop :=
  ∀ u ∈ U, (repCount W u : ℝ) ≤ 2 * B

/-- The per-class second-moment estimate (GM Lemma 11.6, one dyadic class). -/
lemma Zclass_sum_le (m : ℕ) (Cloc K : ℝ) (M : ℕ) (hM : 1 ≤ M) (hK : 1 ≤ K) (hCloc : 0 < Cloc)
    (hLOC : ∀ τ d : ℝ, |τ - d| ≤ 1 →
      ‖Gsum M τ‖ ^ 2 ≤ 4 * K * Cloc ^ 2 * (∫ u in d - 2 * K..d + 2 * K, ‖Gsum M u‖ ^ 2)
        + 2 * (Cloc / K ^ (m : ℝ) * ((M : ℝ) + 1)) ^ 2)
    (W : Finset ℝ) (U : Finset ℤ) (B : ℝ) (hU : KeyBound W U B) :
    (∑ n1 ∈ Finset.Icc M (2 * M), ∑ n2 ∈ Finset.Icc M (2 * M),
        ‖Zclass W U ((n1 : ℝ) / (n2 : ℝ))‖ ^ 2)
      ≤ (2 * B) ^ 2 * (4 * K * Cloc ^ 2 * (∑ u1 ∈ U, ∑ u2 ∈ U,
            (∫ u in (u1 : ℝ) - (u2 : ℝ) - 2 * K..(u1 : ℝ) - (u2 : ℝ) + 2 * K,
              ‖Gsum M u‖ ^ 2))
          + 2 * (Cloc / K ^ (m : ℝ) * ((M : ℝ) + 1)) ^ 2 * ((U.card : ℝ) ^ 2)) := by
  classical
  set X : ℤ → ℤ → ℝ := fun u1 u2 =>
    4 * K * Cloc ^ 2 * (∫ u in (u1 : ℝ) - (u2 : ℝ) - 2 * K..(u1 : ℝ) - (u2 : ℝ) + 2 * K,
        ‖Gsum M u‖ ^ 2)
      + 2 * (Cloc / K ^ (m : ℝ) * ((M : ℝ) + 1)) ^ 2 with hXdef
  have hXnn : ∀ u1 u2 : ℤ, 0 ≤ X u1 u2 := by
    intro u1 u2
    have hK0 : (0 : ℝ) ≤ K := le_trans zero_le_one hK
    have h1 : 0 ≤ ∫ u in (u1 : ℝ) - (u2 : ℝ) - 2 * K..(u1 : ℝ) - (u2 : ℝ) + 2 * K,
        ‖Gsum M u‖ ^ 2 := by
      refine intervalIntegral.integral_nonneg (by linarith) fun u _ => ?_
      positivity
    have h2 : 0 ≤ 4 * K * Cloc ^ 2 := by positivity
    have h3 : 0 ≤ 2 * (Cloc / K ^ (m : ℝ) * ((M : ℝ) + 1)) ^ 2 := by positivity
    rw [hXdef]
    simp only
    nlinarith [mul_nonneg h2 h1, h3]
  -- Step 1: the exact identity for the second moment.
  have hstep1 : (∑ n1 ∈ Finset.Icc M (2 * M), ∑ n2 ∈ Finset.Icc M (2 * M),
        ‖Zclass W U ((n1 : ℝ) / (n2 : ℝ))‖ ^ 2)
      = ∑ u1 ∈ U, ∑ u2 ∈ U, ∑ p ∈ repPairs W u1, ∑ q ∈ repPairs W u2,
          Complex.normSq (Gsum M ((p.1 - p.2) - (q.1 - q.2))) := by
    simp only [← Complex.normSq_eq_norm_sq]
    exact sum_normSq_Zclass_eq M hM W U
  -- Step 2: pointwise locality bound, summed over the pair block.
  have hstep2 : (∑ u1 ∈ U, ∑ u2 ∈ U, ∑ p ∈ repPairs W u1, ∑ q ∈ repPairs W u2,
          Complex.normSq (Gsum M ((p.1 - p.2) - (q.1 - q.2))))
      ≤ ∑ u1 ∈ U, ∑ u2 ∈ U, ∑ _p ∈ repPairs W u1, ∑ _q ∈ repPairs W u2, X u1 u2 := by
    refine Finset.sum_le_sum fun u1 _ => Finset.sum_le_sum fun u2 _ =>
      Finset.sum_le_sum fun p hp => Finset.sum_le_sum fun q hq => ?_
    have hp' := mem_repPairs.mp hp
    have hq' := mem_repPairs.mp hq
    obtain ⟨hA1, hA2⟩ := floor_residual_bounds (a := p.1 - p.2) (u := u1) hp'.2
    obtain ⟨hB1, hB2⟩ := floor_residual_bounds (a := q.1 - q.2) (u := u2) hq'.2
    have hd : |((p.1 - p.2) - (q.1 - q.2)) - ((u1 : ℝ) - (u2 : ℝ))| ≤ 1 := by
      have e : ((p.1 - p.2) - (q.1 - q.2)) - ((u1 : ℝ) - (u2 : ℝ))
          = ((p.1 - p.2) - ((u1 : ℤ) : ℝ)) - ((q.1 - q.2) - ((u2 : ℤ) : ℝ)) := by
        push_cast; ring
      rw [e, abs_le]
      constructor <;> linarith
    have hloc := hLOC ((p.1 - p.2) - (q.1 - q.2)) ((u1 : ℝ) - (u2 : ℝ)) hd
    rw [hXdef]
    rw [Complex.normSq_eq_norm_sq]
    exact hloc
  -- Step 3: evaluate the pair block sums.
  have hstep3 : (∑ u1 ∈ U, ∑ u2 ∈ U, ∑ _p ∈ repPairs W u1, ∑ _q ∈ repPairs W u2, X u1 u2)
      = ∑ u1 ∈ U, ∑ u2 ∈ U, (repCount W u1 : ℝ) * (repCount W u2 : ℝ) * X u1 u2 := by
    refine Finset.sum_congr rfl fun u1 _ => Finset.sum_congr rfl fun u2 _ => ?_
    rw [Finset.sum_const, Finset.sum_const]
    simp only [nsmul_eq_mul, repCount]
    ring
  -- Step 4: bound the counts by `2B`.
  have hstep4 : (∑ u1 ∈ U, ∑ u2 ∈ U, (repCount W u1 : ℝ) * (repCount W u2 : ℝ) * X u1 u2)
      ≤ (2 * B) ^ 2 * ∑ u1 ∈ U, ∑ u2 ∈ U, X u1 u2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun u1 hu1 => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun u2 hu2 => ?_
    have h1 : (0 : ℝ) ≤ (repCount W u1 : ℝ) := by positivity
    have h2 : (0 : ℝ) ≤ (repCount W u2 : ℝ) := by positivity
    have h3 : (0 : ℝ) ≤ 2 * B := le_trans h1 (hU u1 hu1)
    have h4 : (repCount W u1 : ℝ) ≤ 2 * B := hU u1 hu1
    have h5 : (repCount W u2 : ℝ) ≤ 2 * B := hU u2 hu2
    have h6 : (repCount W u1 : ℝ) * (repCount W u2 : ℝ) ≤ (2 * B) ^ 2 := by
      have := mul_le_mul h4 h5 h2 h3
      nlinarith [this, sq_nonneg (2 * B)]
    calc (repCount W u1 : ℝ) * (repCount W u2 : ℝ) * X u1 u2
        ≤ (2 * B) ^ 2 * X u1 u2 := by
          exact mul_le_mul_of_nonneg_right h6 (hXnn u1 u2)
      _ = (2 * B) ^ 2 * X u1 u2 := rfl
  -- Step 5: pull out the constants.
  have hstep5 : (∑ u1 ∈ U, ∑ u2 ∈ U, X u1 u2)
      = 4 * K * Cloc ^ 2 * (∑ u1 ∈ U, ∑ u2 ∈ U,
            (∫ u in (u1 : ℝ) - (u2 : ℝ) - 2 * K..(u1 : ℝ) - (u2 : ℝ) + 2 * K,
              ‖Gsum M u‖ ^ 2))
          + 2 * (Cloc / K ^ (m : ℝ) * ((M : ℝ) + 1)) ^ 2 * ((U.card : ℝ) ^ 2) := by
    rw [hXdef]
    simp only
    simp only [Finset.sum_add_distrib]
    congr 1
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun u1 _ => ?_
      rw [Finset.mul_sum]
    · rw [Finset.sum_const, Finset.sum_const]
      simp only [nsmul_eq_mul]
      ring
  rw [hstep1]
  calc (∑ u1 ∈ U, ∑ u2 ∈ U, ∑ p ∈ repPairs W u1, ∑ q ∈ repPairs W u2,
        Complex.normSq (Gsum M ((p.1 - p.2) - (q.1 - q.2))))
      ≤ ∑ u1 ∈ U, ∑ u2 ∈ U, (repCount W u1 : ℝ) * (repCount W u2 : ℝ) * X u1 u2 :=
        le_trans hstep2 hstep3.le
    _ ≤ (2 * B) ^ 2 * ∑ u1 ∈ U, ∑ u2 ∈ U, X u1 u2 := hstep4
    _ = (2 * B) ^ 2 * (4 * K * Cloc ^ 2 * (∑ u1 ∈ U, ∑ u2 ∈ U,
            (∫ u in (u1 : ℝ) - (u2 : ℝ) - 2 * K..(u1 : ℝ) - (u2 : ℝ) + 2 * K,
              ‖Gsum M u‖ ^ 2))
          + 2 * (Cloc / K ^ (m : ℝ) * ((M : ℝ) + 1)) ^ 2 * ((U.card : ℝ) ^ 2)) := by
        rw [hstep5]

/-- **GM Lemma 11.6** (discrete fourth moment), given Heath-Brown (`hHB`) and the locality
Lemma 11.3 for general coefficients, with the locality window parameter `K` exposed:
`Σ_{n₁,n₂∈[M,2M]} ‖R(n₁/n₂)‖⁴⪅ K²(|W|⁴M + M²E(W) + E(W)^{3/4}|W|T^{1/2}M) + (M/K^m)²E(W)|W|²`.
(Route: split the pairs `n₁,n₂` by the number of representations `u = ⌊t₁-t₂⌋` in sets `U_B`;
apply the locality bound to replace `sup_{|s|≤1}|Σ_{n∼M}n^{i(u₁-u₂+s)}|²` by an integral over the
window `|s| ≤ K`; then Heath-Brown's theorem (`hHB`) applied to the `1`-separated integer points
`u₁-u₂` gives `|U_B|²M + |U_B|M² + T^{1/2}|U_B|^{5/4}M`; finally `B|U_B| ≤ |W|²` and
`B²|U_B| ≤ E(W)`. The locality error is squared once per pair `(u₁,u₂) ∈ U_B²`.) -/
theorem fourth_moment_Rfun (hHB : Submission.GM.HBStatement) (m : ℕ) (hm : 2 ≤ m)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (Cloc : ℝ), 0 < Cloc →
      (∀ (N' : ℕ), 1 ≤ N' → ∀ (a : ℕ → ℂ), ∀ (K : ℝ), 1 ≤ K → ∀ t : ℝ,
        ‖∑ n ∈ Finset.Icc N' (2 * N'), a n * (n : ℂ) ^ (Complex.I * (t : ℂ))‖ ≤
          Cloc * (∫ u in t - K..t + K,
                    ‖∑ n ∈ Finset.Icc N' (2 * N'), a n * (n : ℂ) ^ (Complex.I * (u : ℂ))‖)
            + Cloc / K ^ (m : ℝ) * (∑ n ∈ Finset.Icc N' (2 * N'), ‖a n‖)) →
      ∀ (M : ℕ), 1 ≤ M → ∀ (T : ℝ), 1 ≤ T → ∀ (W : Finset ℝ),
        (∀ t ∈ W, t ∈ Set.Icc 0 T) → Submission.GM.Separated W 1 →
      ∀ (K : ℝ), 1 ≤ K →
        (∑ n1 ∈ Finset.Icc M (2 * M), ∑ n2 ∈ Finset.Icc M (2 * M),
            ‖Submission.GM.Rfun W ((n1 : ℝ) / (n2 : ℝ))‖ ^ 4)
          ≤ C * (Cloc + 1) ^ 2 * T ^ ε * (K + 1) ^ 2 *
              ((W.card : ℝ) ^ 4 * (M : ℝ) + (M : ℝ) ^ 2 * (Submission.GM.energy W : ℝ)
                + (Submission.GM.energy W : ℝ) ^ ((3 : ℝ) / 4) * (W.card : ℝ)
                    * T ^ ((1 : ℝ) / 2) * (M : ℝ))
            + C * (Cloc + 1) ^ 2 * T ^ ε * (((M : ℝ) + 1) / K ^ (m : ℝ)) ^ 2
                * (Submission.GM.energy W : ℝ) * (W.card : ℝ) ^ 2 := by
  obtain ⟨C1, hC1pos, hC1⟩ := clsNum_sq_bound ε hε
  obtain ⟨Chb, hChbpos, hHBb⟩ := HB_Gsum_shift_self hHB (ε / 2) (by linarith)
  refine ⟨32 * C1 * Chb * 4 ^ (ε / 2) + 8 * C1 + 1, by positivity, ?_⟩
  intro Cloc hCloc hloc M hM T hT W hWsub hsep K hK
  have hKpos : (0 : ℝ) < K := lt_of_lt_of_le zero_lt_one hK
  have hTpos : (0 : ℝ) < T := lt_of_lt_of_le zero_lt_one hT
  have hT1 : (1 : ℝ) ≤ T + 1 := by linarith
  set Wc : ℝ := (W.card : ℝ) with hWc
  set E : ℝ := (Submission.GM.energy W : ℝ) with hE
  set MM : ℝ := (M : ℝ) with hMM
  have hWc0 : 0 ≤ Wc := by rw [hWc]; positivity
  have hE0 : 0 ≤ E := by rw [hE]; positivity
  have hMM0 : 0 ≤ MM := by rw [hMM]; positivity
  -- locality, in the form used by `Zclass_sum_le`
  have hLOC : ∀ τ d : ℝ, |τ - d| ≤ 1 →
      ‖Gsum M τ‖ ^ 2 ≤ 4 * K * Cloc ^ 2 * (∫ u in d - 2 * K..d + 2 * K, ‖Gsum M u‖ ^ 2)
        + 2 * (Cloc / K ^ (m : ℝ) * ((M : ℝ) + 1)) ^ 2 :=
    fun τ d hd => locality_Gsum m Cloc K M hM hK hCloc hloc τ d hd
  -- the uniform per-class bound
  set GB : ℝ := 16 * K ^ 2 * Cloc ^ 2 * Chb * (2 * (T + 1)) ^ (ε / 2) *
        (Wc ^ 4 * MM + E * MM ^ 2 + (2 * (T + 1)) ^ ((1 : ℝ) / 2) * E ^ ((3 : ℝ) / 4) * Wc * MM)
      + 8 * (Cloc / K ^ (m : ℝ) * (MM + 1)) ^ 2 * E * Wc ^ 2 with hGB
  have hpos : ∀ n ∈ Finset.Icc M (2 * M), (0 : ℝ) < (n : ℝ) := by
    intro n hn
    have h1 : M ≤ n := (Finset.mem_Icc.mp hn).1
    exact_mod_cast (lt_of_lt_of_le (by omega : 0 < M) h1)
  -- Step 1: pointwise bound, summed and interchanged
  have hstep1 : (∑ n1 ∈ Finset.Icc M (2 * M), ∑ n2 ∈ Finset.Icc M (2 * M),
        ‖Submission.GM.Rfun W ((n1 : ℝ) / (n2 : ℝ))‖ ^ 4)
      ≤ (clsNum W : ℝ) * ∑ j ∈ Finset.range (clsNum W),
          ∑ n1 ∈ Finset.Icc M (2 * M), ∑ n2 ∈ Finset.Icc M (2 * M),
            ‖Zclass W (clsSet W j) ((n1 : ℝ) / (n2 : ℝ))‖ ^ 2 := by
    have h1 : (∑ n1 ∈ Finset.Icc M (2 * M), ∑ n2 ∈ Finset.Icc M (2 * M),
          ‖Submission.GM.Rfun W ((n1 : ℝ) / (n2 : ℝ))‖ ^ 4)
        ≤ ∑ n1 ∈ Finset.Icc M (2 * M), ∑ n2 ∈ Finset.Icc M (2 * M),
            (clsNum W : ℝ) * ∑ j ∈ Finset.range (clsNum W),
              ‖Zclass W (clsSet W j) ((n1 : ℝ) / (n2 : ℝ))‖ ^ 2 := by
      refine Finset.sum_le_sum fun n1 hn1 => Finset.sum_le_sum fun n2 hn2 => ?_
      exact Rfun_pow4_le_sum_Zclass W (div_pos (hpos n1 hn1) (hpos n2 hn2))
    have h2 : (∑ n1 ∈ Finset.Icc M (2 * M), ∑ n2 ∈ Finset.Icc M (2 * M),
            (clsNum W : ℝ) * ∑ j ∈ Finset.range (clsNum W),
              ‖Zclass W (clsSet W j) ((n1 : ℝ) / (n2 : ℝ))‖ ^ 2)
        = (clsNum W : ℝ) * ∑ n1 ∈ Finset.Icc M (2 * M), ∑ n2 ∈ Finset.Icc M (2 * M),
            ∑ j ∈ Finset.range (clsNum W),
              ‖Zclass W (clsSet W j) ((n1 : ℝ) / (n2 : ℝ))‖ ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun n1 _ => ?_
      rw [Finset.mul_sum]
    have h3 : (∑ n1 ∈ Finset.Icc M (2 * M), ∑ n2 ∈ Finset.Icc M (2 * M),
            ∑ j ∈ Finset.range (clsNum W),
              ‖Zclass W (clsSet W j) ((n1 : ℝ) / (n2 : ℝ))‖ ^ 2)
        = ∑ j ∈ Finset.range (clsNum W), ∑ n1 ∈ Finset.Icc M (2 * M),
            ∑ n2 ∈ Finset.Icc M (2 * M),
              ‖Zclass W (clsSet W j) ((n1 : ℝ) / (n2 : ℝ))‖ ^ 2 :=
      sum_swap_nn_j _ _ _
    calc (∑ n1 ∈ Finset.Icc M (2 * M), ∑ n2 ∈ Finset.Icc M (2 * M),
          ‖Submission.GM.Rfun W ((n1 : ℝ) / (n2 : ℝ))‖ ^ 4)
        ≤ ∑ n1 ∈ Finset.Icc M (2 * M), ∑ n2 ∈ Finset.Icc M (2 * M),
            (clsNum W : ℝ) * ∑ j ∈ Finset.range (clsNum W),
              ‖Zclass W (clsSet W j) ((n1 : ℝ) / (n2 : ℝ))‖ ^ 2 := h1
      _ = (clsNum W : ℝ) * ∑ n1 ∈ Finset.Icc M (2 * M), ∑ n2 ∈ Finset.Icc M (2 * M),
            ∑ j ∈ Finset.range (clsNum W),
              ‖Zclass W (clsSet W j) ((n1 : ℝ) / (n2 : ℝ))‖ ^ 2 := h2
      _ = (clsNum W : ℝ) * ∑ j ∈ Finset.range (clsNum W), ∑ n1 ∈ Finset.Icc M (2 * M),
            ∑ n2 ∈ Finset.Icc M (2 * M),
              ‖Zclass W (clsSet W j) ((n1 : ℝ) / (n2 : ℝ))‖ ^ 2 := by rw [h3]
  -- Step 2: per class bound
  have hstep2 : ∀ j ∈ Finset.range (clsNum W),
      (∑ n1 ∈ Finset.Icc M (2 * M), ∑ n2 ∈ Finset.Icc M (2 * M),
          ‖Zclass W (clsSet W j) ((n1 : ℝ) / (n2 : ℝ))‖ ^ 2) ≤ GB := by
    intro j _
    have hKB : KeyBound W (clsSet W j) ((2 : ℝ) ^ j) := by
      intro u hu
      have h1 : repCount W u < 2 ^ (j + 1) := clsSet_lt_pow hu
      have h2 : (repCount W u : ℝ) ≤ ((2 : ℕ) ^ (j + 1) : ℕ) := by exact_mod_cast h1.le
      have h3 : (((2 : ℕ) ^ (j + 1) : ℕ) : ℝ) = 2 * (2 : ℝ) ^ j := by push_cast; ring
      rw [h3] at h2
      exact h2
    have hpc := Zclass_sum_le m Cloc K M hM hK hCloc hLOC W (clsSet W j) ((2 : ℝ) ^ j) hKB
    have hHBj := hHBb M hM (T + 1) hT1 K hK (clsSet W j)
      (fun u hu => abs_key_le hWsub (clsSet_subset j hu))
    obtain ⟨hc1, hc2, hc3, hc4⟩ := class_bounds W j
    have hc1' : ((2 : ℝ) ^ j) ^ 2 * (((clsSet W j).card : ℕ) : ℝ) ^ 2 ≤ Wc ^ 4 := by
      have h : ((2 : ℝ) ^ j * (((clsSet W j).card : ℕ) : ℝ)) ^ 2 ≤ (W.card : ℝ) ^ 4 := hc1
      calc ((2 : ℝ) ^ j) ^ 2 * (((clsSet W j).card : ℕ) : ℝ) ^ 2
          = ((2 : ℝ) ^ j * (((clsSet W j).card : ℕ) : ℝ)) ^ 2 := by ring
        _ ≤ (W.card : ℝ) ^ 4 := h
        _ = Wc ^ 4 := by rw [hWc]
    have hs0 : 0 ≤ ∑ u1 ∈ clsSet W j, ∑ u2 ∈ clsSet W j,
        (∫ u in (u1 : ℝ) - (u2 : ℝ) - 2 * K..(u1 : ℝ) - (u2 : ℝ) + 2 * K, ‖Gsum M u‖ ^ 2) := by
      refine Finset.sum_nonneg fun u1 _ => Finset.sum_nonneg fun u2 _ => ?_
      refine intervalIntegral.integral_nonneg (by linarith) fun u _ => ?_
      positivity
    have harith := per_class_arith (ε := ε) (b := (2 : ℝ) ^ j)
      (u := (((clsSet W j).card : ℕ) : ℝ))
      (s := ∑ u1 ∈ clsSet W j, ∑ u2 ∈ clsSet W j,
        (∫ u in (u1 : ℝ) - (u2 : ℝ) - 2 * K..(u1 : ℝ) - (u2 : ℝ) + 2 * K, ‖Gsum M u‖ ^ 2))
      (Wc := Wc) (E := E) (T := T) (K := K) (Cloc := Cloc) (Chb := Chb) (Cw := Cloc)
      (mm := (m : ℝ)) (MM := MM)
      (by positivity) (by positivity) hs0 hWc0 hE0 hMM0 hKpos (le_of_lt hCloc)
      (le_of_lt hChbpos) (le_of_lt hCloc) (by positivity) (by positivity) hc1' hc2 hc3 hc4 hHBj
    rw [hGB]
    exact le_trans hpc harith
  -- Step 3: sum over the classes
  have hstep3 : (∑ j ∈ Finset.range (clsNum W), ∑ n1 ∈ Finset.Icc M (2 * M),
        ∑ n2 ∈ Finset.Icc M (2 * M),
          ‖Zclass W (clsSet W j) ((n1 : ℝ) / (n2 : ℝ))‖ ^ 2)
      ≤ (clsNum W : ℝ) * GB := by
    calc (∑ j ∈ Finset.range (clsNum W), ∑ n1 ∈ Finset.Icc M (2 * M),
          ∑ n2 ∈ Finset.Icc M (2 * M),
            ‖Zclass W (clsSet W j) ((n1 : ℝ) / (n2 : ℝ))‖ ^ 2)
        ≤ ∑ _j ∈ Finset.range (clsNum W), GB := Finset.sum_le_sum hstep2
      _ = (clsNum W : ℝ) * GB := by
          rw [Finset.sum_const, nsmul_eq_mul, Finset.card_range]
  have hmain : (∑ n1 ∈ Finset.Icc M (2 * M), ∑ n2 ∈ Finset.Icc M (2 * M),
        ‖Submission.GM.Rfun W ((n1 : ℝ) / (n2 : ℝ))‖ ^ 4)
      ≤ (clsNum W : ℝ) ^ 2 * GB := by
    calc (∑ n1 ∈ Finset.Icc M (2 * M), ∑ n2 ∈ Finset.Icc M (2 * M),
          ‖Submission.GM.Rfun W ((n1 : ℝ) / (n2 : ℝ))‖ ^ 4)
        ≤ (clsNum W : ℝ) * ((clsNum W : ℝ) * GB) :=
          le_trans hstep1 (mul_le_mul_of_nonneg_left hstep3 (by positivity))
      _ = (clsNum W : ℝ) ^ 2 * GB := by ring
  have hJ2 : (clsNum W : ℝ) ^ 2 ≤ C1 * T ^ (ε / 2) := hC1 T hT W hWsub hsep
  have hmain2 : (∑ n1 ∈ Finset.Icc M (2 * M), ∑ n2 ∈ Finset.Icc M (2 * M),
        ‖Submission.GM.Rfun W ((n1 : ℝ) / (n2 : ℝ))‖ ^ 4)
      ≤ C1 * T ^ (ε / 2) * GB :=
    le_trans hmain (mul_le_mul_of_nonneg_right hJ2 (by positivity))
  -- Step 4: the final arithmetic
  have hfin := arith_final ε hε C1 Chb T K Cloc E Wc MM (m : ℝ) hT hKpos (le_of_lt hCloc)
    (le_of_lt hC1pos) (le_of_lt hChbpos) hE0 hWc0 hMM0
  refine le_trans hmain2 ?_
  rw [hGB]
  have hbridge :
      (32 * C1 * Chb * 4 ^ (ε / 2) + 8 * C1 + 1) * (Cloc + 1) ^ 2 * T ^ ε * (K + 1) ^ 2 *
            (Wc ^ 4 * MM + E * MM ^ 2 + T ^ ((1 : ℝ) / 2) * E ^ ((3 : ℝ) / 4) * Wc * MM)
        + (32 * C1 * Chb * 4 ^ (ε / 2) + 8 * C1 + 1) * (Cloc + 1) ^ 2 * T ^ ε *
            ((MM + 1) / K ^ (m : ℝ)) ^ 2 * E * Wc ^ 2
      = (32 * C1 * Chb * 4 ^ (ε / 2) + 8 * C1 + 1) * (Cloc + 1) ^ 2 * T ^ ε * (K + 1) ^ 2 *
            (Wc ^ 4 * MM + MM ^ 2 * E + E ^ ((3 : ℝ) / 4) * Wc * T ^ ((1 : ℝ) / 2) * MM)
        + (32 * C1 * Chb * 4 ^ (ε / 2) + 8 * C1 + 1) * (Cloc + 1) ^ 2 * T ^ ε *
            ((MM + 1) / K ^ (m : ℝ)) ^ 2 * E * Wc ^ 2 := by ring
  rw [hbridge] at hfin
  exact hfin

end Algebra

end Work.GM.Energy.EnergyCore
