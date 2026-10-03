import Mathlib
import Submission.Work.FIArea7.Classical172Defs
import Submission.Work.FIArea7.PairEllAux.hyperbolaBlockLeGen
import Submission.Work.FIArea7.PairEllAux.hyperbolaStarEps
import Submission.Work.FIArea7.PairEllAux.smoothStarEps
import Submission.Work.FIArea7.PairEllDefs

namespace Work.FIArea7

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

/-- (25.4) for the pair `(c,ℓ)` with the **power loss** forced by *FI* (23.8) in its corrected
form `Prop231 = ∀ ε > 0, ∃ C, ... · (MN + c + 2)^ε`: the sum over `Zc ≤ c ≤ Cmax`, `ℓ ≤ T` of
`al c · be ℓ · P(cℓ) · λ(cℓ)` is `≪ max(Cmax, b/Zc)^{1/12} b^{11/12} (b + Cmax·T + 2)^ε log(b+2)^A`.

`0 ≤ b` is required: `Real.rpow` on a negative base is signed (`b^{11/12} < 0` for `b < 0`), so
without it the statement is false (take `P ≡ 0`, `b = -1/2`).  The machinery is in place
`sorry`-free in `Submission/Work/FIArea7/PairEllAux/` (`hyperbolaBlockLeGen`, `hyperbolaStarEps`,
`smoothStarEps`): assemble `smoothStarEps (hyperbolaStarEps hyperbolaBlockLeGen h31)` with the
pair `(m,n) = (c,ℓ)`, `c₀ = 1`, `M = Cmax`, `N = T`, `U = b` and the Mellin/Abel splitting of the
weight `P(cℓ)`, as in the (now deleted) proof attempt. -/
theorem pairEllSum2Eps (h31 : Work.FIArea7.Prop231) :
    ∀ ε : ℝ, 0 < ε → ∃ C A : ℝ, 0 < C ∧ 0 < A ∧
      ∀ (chi : GaussianInt → ℂ) (k : ℤ) (d Zc Cmax T : ℕ) (al be : ℕ → ℂ) (P : ℝ → ℝ)
        (a b K : ℝ),
        1 ≤ d → 1 ≤ Zc → 1 ≤ Cmax → 1 ≤ T →
        (∀ i, ‖al i‖ ≤ 1) → (∀ i, ‖be i‖ ≤ 1) →
        (∀ z', ‖chi z'‖ ≤ 1) →
        (∀ z1 z2 : GaussianInt, IsCoprime z1 z2 → chi (z1 * z2) = chi z1 * chi z2) →
        ContDiff ℝ 1 P → 0 ≤ a → 0 ≤ b → (∀ u, 0 ≤ P u) → (∀ u, P u ≤ 1) →
        (∀ u, P u ≠ 0 → a < u ∧ u ≤ b) → (∀ u, |deriv P u| ≤ K) →
        ‖∑ c ∈ (Finset.Icc 1 Cmax).filter (fun c : ℕ => Zc ≤ c),
            ∑ ℓ ∈ Finset.Icc 1 T,
              (if Nat.Coprime c ℓ then al c * be ℓ * ((P ((c : ℝ) * (ℓ : ℝ)) : ℝ) : ℂ)
                * Work.FIArea7.quadEigen (Work.FIArea7.grossenChar chi k) (c * ℓ) else 0)‖
          ≤ C * max ((Cmax : ℝ)) (b / (Zc : ℝ)) ^ ((1 : ℝ) / 12)
              * (b ^ ((11 : ℝ) / 12)) * ((b + (Cmax : ℝ) * (T : ℝ) + 2) ^ ε)
              * (Real.log (b + 2)) ^ A * (K * |b - a| + 1) := by

  intro ε hε
  obtain ⟨C1, A1, hC1, hA1, hstar⟩ :=
    PairEllAux.smoothStarEps (PairEllAux.hyperbolaStarEps PairEllAux.hyperbolaBlockLeGen h31) ε hε
  refine ⟨C1 * 2 ^ ((1 : ℝ) / 12), A1, mul_pos hC1 (Real.rpow_pos_of_pos (by norm_num) _), hA1, ?_⟩
  intro chi k d Zc Cmax T al be P a b K hd hZc hCmax hT hal hbe hchi hchiMul hPcont hPa hb0 hP0 hP1 hPsupp hPder
  change ‖∑ c ∈ (Finset.Icc 1 Cmax).filter (fun c : ℕ => Zc ≤ c),
      ∑ ℓ ∈ Finset.Icc 1 T, pairTerm chi k al be P c ℓ‖ ≤
    (C1 * 2 ^ ((1 : ℝ) / 12)) * (max (Cmax : ℝ) (b / (Zc : ℝ))) ^ ((1 : ℝ) / 12)
      * (b ^ ((11 : ℝ) / 12)) * ((b + (Cmax : ℝ) * (T : ℝ) + 2) ^ ε)
      * (Real.log (b + 2)) ^ A1 * (K * |b - a| + 1)
  have hK0 : 0 ≤ K := le_trans (abs_nonneg _) (hPder 0)
  have hPvan : ∀ u : ℝ, b < u → P u = 0 := by
    intro u hu
    by_contra hne
    exact absurd (hPsupp u hne).2 (not_le.mpr hu)
  have hVnn : 0 ≤ K * |b - a| + 1 := by
    have := mul_nonneg hK0 (abs_nonneg (b - a)); linarith
  have hRHSnn : 0 ≤ (C1 * 2 ^ ((1 : ℝ) / 12)) * (max (Cmax : ℝ) (b / (Zc : ℝ))) ^ ((1 : ℝ) / 12)
      * (b ^ ((11 : ℝ) / 12)) * ((b + (Cmax : ℝ) * (T : ℝ) + 2) ^ ε)
      * (Real.log (b + 2)) ^ A1 * (K * |b - a| + 1) := by
    have hmax0 : 0 ≤ max (Cmax : ℝ) (b / (Zc : ℝ)) :=
      le_trans (by positivity) (le_max_left _ _)
    have hbase : 0 ≤ b + (Cmax : ℝ) * (T : ℝ) + 2 := by
      have h1 : (0 : ℝ) ≤ (Cmax : ℝ) * (T : ℝ) := by positivity
      linarith
    have hlog : 0 ≤ Real.log (b + 2) := Real.log_nonneg (by linarith)
    refine mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ?_ ?_) ?_) ?_) ?_) ?_
    · exact mul_nonneg hC1.le (Real.rpow_nonneg (by norm_num) _)
    · exact Real.rpow_nonneg hmax0 _
    · exact Real.rpow_nonneg hb0 _
    · exact Real.rpow_nonneg hbase _
    · exact Real.rpow_nonneg hlog _
    · exact hVnn
  have hzeroOf : ∀ c ℓ : ℕ, 1 ≤ c → b < (c : ℝ) * (ℓ : ℝ) → pairTerm chi k al be P c ℓ = 0 := by
    intro c ℓ hc1 hgt
    rw [pairTerm]
    by_cases hcp : Nat.Coprime c ℓ
    · rw [if_pos hcp]
      simp only [hPvan _ hgt, Complex.ofReal_zero, zero_mul, mul_zero]
    · rw [if_neg hcp]
  by_cases hb1 : b < 1
  · have hsum0 : (∑ c ∈ (Finset.Icc 1 Cmax).filter (fun c : ℕ => Zc ≤ c),
        ∑ ℓ ∈ Finset.Icc 1 T, pairTerm chi k al be P c ℓ) = 0 := by
      apply Finset.sum_eq_zero
      intro c hc
      apply Finset.sum_eq_zero
      intro ℓ hℓ
      have hc1 : 1 ≤ c := (Finset.mem_Icc.mp (Finset.mem_filter.mp hc).1).1
      have hℓ1 : 1 ≤ ℓ := (Finset.mem_Icc.mp hℓ).1
      refine hzeroOf c ℓ hc1 ?_
      have h1 : (1 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc1
      have h2 : (1 : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast hℓ1
      have h3 : (1 : ℝ) ≤ (c : ℝ) * (ℓ : ℝ) := by nlinarith
      linarith
    rw [hsum0, norm_zero]
    exact hRHSnn
  · push_neg at hb1
    by_cases hZb : b < (Zc : ℝ)
    · have hsum0 : (∑ c ∈ (Finset.Icc 1 Cmax).filter (fun c : ℕ => Zc ≤ c),
          ∑ ℓ ∈ Finset.Icc 1 T, pairTerm chi k al be P c ℓ) = 0 := by
        apply Finset.sum_eq_zero
        intro c hc
        apply Finset.sum_eq_zero
        intro ℓ hℓ
        have hcZ : Zc ≤ c := (Finset.mem_filter.mp hc).2
        have hℓ1 : 1 ≤ ℓ := (Finset.mem_Icc.mp hℓ).1
        refine hzeroOf c ℓ (le_trans hZc hcZ) ?_
        have h1 : (Zc : ℝ) ≤ (c : ℝ) := by exact_mod_cast hcZ
        have h2 : (1 : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast hℓ1
        have h3 : (1 : ℝ) ≤ (Zc : ℝ) := by exact_mod_cast hZc
        nlinarith
      rw [hsum0, norm_zero]
      exact hRHSnn
    · push_neg at hZb
      have hbpos : (0 : ℝ) ≤ b := le_trans zero_le_one hb1
      have hZcpos : (0 : ℝ) < (Zc : ℝ) := by
        exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hZc)
      have hCnn : (0 : ℝ) ≤ (Cmax : ℝ) := Nat.cast_nonneg Cmax
      have hTnn : (0 : ℝ) ≤ (T : ℝ) := Nat.cast_nonneg T
      set U : ℕ := Nat.floor b with hU
      have hU1 : 1 ≤ U := by
        rw [hU]; exact Nat.le_floor (by exact_mod_cast hb1)
      have hUle : ((U : ℕ) : ℝ) ≤ b := by rw [hU]; exact Nat.floor_le hbpos
      set N1 : ℕ := min T (Nat.floor (b / (Zc : ℝ))) with hN1
      have hN11 : 1 ≤ N1 := by
        rw [hN1]
        exact le_min hT (Nat.le_floor (by simpa using (one_le_div hZcpos).mpr hZb))
      have hN1T : N1 ≤ T := by rw [hN1]; exact min_le_left _ _
      have hN1M : ((N1 : ℕ) : ℝ) ≤ max (Cmax : ℝ) (b / (Zc : ℝ)) := by
        rw [hN1]
        have h1 : ((min T (Nat.floor (b / (Zc : ℝ))) : ℕ) : ℝ)
            ≤ ((Nat.floor (b / (Zc : ℝ)) : ℕ) : ℝ) := by
          exact_mod_cast min_le_right T (Nat.floor (b / (Zc : ℝ)))
        have h2 : (0 : ℝ) ≤ b / (Zc : ℝ) := div_nonneg hbpos hZcpos.le
        exact le_trans h1 (le_trans (Nat.floor_le h2) (le_max_right _ _))
      set al' : ℕ → ℂ := fun m => if Zc ≤ m then al m else 0 with hal'
      have hal'1 : ∀ m ∈ Finset.Icc 1 Cmax, ‖al' m‖ ≤ 1 := by
        intro m hm
        rw [hal']
        by_cases h : Zc ≤ m
        · simp only [h, if_true]; exact hal m
        · simp only [h, if_false, norm_zero]; norm_num
      have hbe1 : ∀ n ∈ Finset.Icc 1 N1, ‖be n‖ ≤ 1 := fun n _ => hbe n
      have hbnd := hstar chi k 1 Cmax N1 U al' be P a b K le_rfl hCmax hN11 hU1 hchi hchiMul
        hal'1 hbe1 hPcont hPa hP0 hP1 hPsupp hPder
      have hbnd' : ‖∑ m ∈ Finset.Icc 1 Cmax, ∑ n ∈ Finset.Icc 1 N1,
            pairTermH chi k al' be P 1 U m n‖
          ≤ C1 * ((Cmax : ℝ) + N1) ^ ((1 : ℝ) / 12) * ((U : ℝ)) ^ ((11 : ℝ) / 12)
            * Real.log ((U : ℝ) + 2) ^ A1 * (K * |b - a| + 1)
            * ((Cmax : ℝ) * (N1 : ℝ) + 1 + 2) ^ ε := by
        simpa only [pairTermH, Nat.divisors_one, Finset.card_singleton, Nat.cast_one, mul_one]
          using hbnd
      have hpt : ∀ c ℓ : ℕ, Zc ≤ c → pairTerm chi k al be P c ℓ = pairTermH chi k al' be P 1 U c ℓ := by
        intro c ℓ hcZ
        rw [pairTerm, pairTermH, hU, hal']
        by_cases hmn : c * ℓ ≤ Nat.floor b
        · rw [if_pos hmn]
          by_cases hcp : Nat.Coprime c ℓ
          · simp only [if_pos hcp, hcZ, if_true, one_mul, Nat.cast_one, Nat.cast_mul]
          · simp only [if_neg hcp]
        · rw [if_neg hmn]
          by_cases hcp : Nat.Coprime c ℓ
          · have hgt : b < (c : ℝ) * (ℓ : ℝ) := by
              have h1 : ((Nat.floor b + 1 : ℕ) : ℝ) ≤ ((c * ℓ : ℕ) : ℝ) := by
                have h2 : Nat.floor b + 1 ≤ c * ℓ := Nat.succ_le_of_lt (Nat.lt_of_not_le hmn)
                exact_mod_cast h2
              have h3 : b < ((Nat.floor b + 1 : ℕ) : ℝ) := by
                have := Nat.lt_floor_add_one b
                push_cast
                linarith
              have h4 : ((c * ℓ : ℕ) : ℝ) = (c : ℝ) * (ℓ : ℝ) := by push_cast; ring
              rw [h4] at h1
              linarith
            simp only [if_pos hcp, hPvan _ hgt, Complex.ofReal_zero, zero_mul, mul_zero]
          · simp only [if_neg hcp]
      have hPTzero : ∀ c x : ℕ, Zc ≤ c → x ≤ T → N1 < x →
          pairTermH chi k al' be P 1 U c x = 0 := by
        intro c x hcZ hxT hxN
        rw [pairTermH, hU]
        by_cases hcx : c * x ≤ Nat.floor b
        · exfalso
          have hb_lt : b < (c : ℝ) * (x : ℝ) := by
            have hfloor : Nat.floor (b / (Zc : ℝ)) < x := by
              rcases lt_or_ge (Nat.floor (b / (Zc : ℝ))) T with h | h
              · have hN : N1 = Nat.floor (b / (Zc : ℝ)) := by rw [hN1]; exact min_eq_right h.le
                omega
              · have hN : N1 = T := by rw [hN1]; exact min_eq_left h
                omega
            have hdiv : (0 : ℝ) ≤ b / (Zc : ℝ) := div_nonneg hbpos hZcpos.le
            have hbr : b / (Zc : ℝ) < (x : ℝ) := (Nat.floor_lt hdiv).mp hfloor
            have h1 : b < (x : ℝ) * (Zc : ℝ) := (div_lt_iff₀ hZcpos).mp hbr
            have h2 : (x : ℝ) * (Zc : ℝ) ≤ (x : ℝ) * (c : ℝ) :=
              mul_le_mul_of_nonneg_left (by exact_mod_cast hcZ) (by positivity)
            nlinarith
          have h1 : ((c * x : ℕ) : ℝ) ≤ b := by
            have h2 : ((c * x : ℕ) : ℝ) ≤ ((Nat.floor b : ℕ) : ℝ) := by exact_mod_cast hcx
            have h3 : ((Nat.floor b : ℕ) : ℝ) ≤ b := Nat.floor_le hbpos
            linarith
          have h4 : ((c * x : ℕ) : ℝ) = (c : ℝ) * (x : ℝ) := by push_cast; ring
          rw [h4] at h1
          linarith
        · rw [if_neg hcx]
      have htrunc : ∀ c : ℕ, Zc ≤ c →
          (∑ x ∈ Finset.Icc 1 T, pairTermH chi k al' be P 1 U c x)
            = ∑ x ∈ Finset.Icc 1 N1, pairTermH chi k al' be P 1 U c x := by
        intro c hcZ
        refine (Finset.sum_subset ?_ ?_).symm
        · intro x hx
          exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hx).1,
            le_trans (Finset.mem_Icc.mp hx).2 hN1T⟩
        · intro x hx hxnot
          have hx1 : 1 ≤ x := (Finset.mem_Icc.mp hx).1
          have hxT : x ≤ T := (Finset.mem_Icc.mp hx).2
          refine hPTzero c x hcZ hxT ?_
          by_contra hle
          exact hxnot (Finset.mem_Icc.mpr ⟨hx1, not_lt.mp hle⟩)
      have hPTzero2 : ∀ c : ℕ, ¬ Zc ≤ c → ∀ x : ℕ, pairTermH chi k al' be P 1 U c x = 0 := by
        intro c hc x
        rw [pairTermH]
        split_ifs with h1 h2
        · have hz : al' c = 0 := by rw [hal']; simp only [hc, if_false]
          simp only [hz, zero_mul, mul_zero]
        · rfl
        · rfl
      have hfull : (∑ c ∈ (Finset.Icc 1 Cmax).filter (fun c : ℕ => Zc ≤ c),
            ∑ x ∈ Finset.Icc 1 N1, pairTermH chi k al' be P 1 U c x)
          = ∑ c ∈ Finset.Icc 1 Cmax, ∑ x ∈ Finset.Icc 1 N1,
              pairTermH chi k al' be P 1 U c x := by
        refine Finset.sum_subset (fun c hc => Finset.mem_of_mem_filter c hc) ?_
        intro c hc hcnf
        have hcZ : ¬ Zc ≤ c := fun h => hcnf (Finset.mem_filter.mpr ⟨hc, h⟩)
        apply Finset.sum_eq_zero
        intro x hx
        exact hPTzero2 c hcZ x
      have e1 : (∑ c ∈ (Finset.Icc 1 Cmax).filter (fun c : ℕ => Zc ≤ c),
            ∑ ℓ ∈ Finset.Icc 1 T, pairTerm chi k al be P c ℓ)
          = ∑ c ∈ (Finset.Icc 1 Cmax).filter (fun c : ℕ => Zc ≤ c),
            ∑ ℓ ∈ Finset.Icc 1 T, pairTermH chi k al' be P 1 U c ℓ :=
        Finset.sum_congr rfl (fun c hc => Finset.sum_congr rfl (fun ℓ _ =>
          hpt c ℓ (Finset.mem_filter.mp hc).2))
      have e2 : (∑ c ∈ (Finset.Icc 1 Cmax).filter (fun c : ℕ => Zc ≤ c),
            ∑ ℓ ∈ Finset.Icc 1 T, pairTermH chi k al' be P 1 U c ℓ)
          = ∑ c ∈ (Finset.Icc 1 Cmax).filter (fun c : ℕ => Zc ≤ c),
            ∑ ℓ ∈ Finset.Icc 1 N1, pairTermH chi k al' be P 1 U c ℓ :=
        Finset.sum_congr rfl (fun c hc => htrunc c (Finset.mem_filter.mp hc).2)
      rw [e1, e2, hfull]
      have harith : C1 * ((Cmax : ℝ) + N1) ^ ((1 : ℝ) / 12) * ((U : ℝ)) ^ ((11 : ℝ) / 12)
            * Real.log ((U : ℝ) + 2) ^ A1 * (K * |b - a| + 1)
            * ((Cmax : ℝ) * (N1 : ℝ) + 1 + 2) ^ ε
          ≤ (C1 * 2 ^ ((1 : ℝ) / 12)) * (max (Cmax : ℝ) (b / (Zc : ℝ))) ^ ((1 : ℝ) / 12)
            * (b ^ ((11 : ℝ) / 12)) * ((b + (Cmax : ℝ) * (T : ℝ) + 2) ^ ε)
            * (Real.log (b + 2)) ^ A1 * (K * |b - a| + 1) := by
        set X1 : ℝ := ((Cmax : ℝ) + N1) ^ ((1 : ℝ) / 12) with hX1def
        set Up : ℝ := ((U : ℝ)) ^ ((11 : ℝ) / 12) with hUpdef
        set Lg : ℝ := Real.log ((U : ℝ) + 2) ^ A1 with hLgdef
        set V : ℝ := K * |b - a| + 1 with hVdef
        set Ee : ℝ := ((Cmax : ℝ) * (N1 : ℝ) + 1 + 2) ^ ε with hEedef
        set W : ℝ := 2 ^ ((1 : ℝ) / 12) with hWdef
        set Mg : ℝ := (max (Cmax : ℝ) (b / (Zc : ℝ))) ^ ((1 : ℝ) / 12) with hMgdef
        set Bp : ℝ := b ^ ((11 : ℝ) / 12) with hBpdef
        set Ee' : ℝ := (b + (Cmax : ℝ) * (T : ℝ) + 2) ^ ε with hEe'def
        set Lg' : ℝ := (Real.log (b + 2)) ^ A1 with hLg'def
        have hUnn : (0 : ℝ) ≤ (U : ℝ) := Nat.cast_nonneg U
        have hX1 : X1 ≤ W * Mg := by
          rw [hX1def, hWdef, hMgdef]
          rw [← Real.mul_rpow (show (0 : ℝ) ≤ 2 by norm_num)
                (le_trans hCnn (le_max_left _ _))]
          apply Real.rpow_le_rpow (by positivity) _ (by norm_num)
          have h1 : (Cmax : ℝ) ≤ max (Cmax : ℝ) (b / (Zc : ℝ)) := le_max_left _ _
          have h2 : ((N1 : ℕ) : ℝ) ≤ max (Cmax : ℝ) (b / (Zc : ℝ)) := hN1M
          linarith
        have hUp : Up ≤ Bp := by
          rw [hUpdef, hBpdef]
          exact Real.rpow_le_rpow (by positivity) hUle (by norm_num)
        have hLg : Lg ≤ Lg' := by
          rw [hLgdef, hLg'def]
          apply Real.rpow_le_rpow _ _ hA1.le
          · exact Real.log_nonneg (by linarith)
          · exact Real.log_le_log (by linarith) (by linarith)
        have hEe : Ee ≤ Ee' := by
          rw [hEedef, hEe'def]
          apply Real.rpow_le_rpow (by positivity) _ hε.le
          have h1 : ((N1 : ℕ) : ℝ) ≤ (T : ℝ) := by exact_mod_cast hN1T
          have h2 : (Cmax : ℝ) * (N1 : ℝ) ≤ (Cmax : ℝ) * (T : ℝ) :=
            mul_le_mul_of_nonneg_left h1 hCnn
          linarith
        have hWnn : 0 ≤ W := by rw [hWdef]; exact Real.rpow_nonneg (by norm_num) _
        have hMgnn : 0 ≤ Mg := by
          rw [hMgdef]
          exact Real.rpow_nonneg (le_trans hCnn (le_max_left _ _)) _
        have hX1nn : 0 ≤ X1 := by rw [hX1def]; exact Real.rpow_nonneg (by positivity) _
        have hUpnn : 0 ≤ Up := by rw [hUpdef]; exact Real.rpow_nonneg (by positivity) _
        have hLgnn : 0 ≤ Lg := by
          rw [hLgdef]
          exact Real.rpow_nonneg (Real.log_nonneg (by linarith)) _
        have hVnn' : 0 ≤ V := by rw [hVdef]; exact hVnn
        have hEenn : 0 ≤ Ee := by rw [hEedef]; exact Real.rpow_nonneg (by positivity) _
        have hBpnn : 0 ≤ Bp := by rw [hBpdef]; exact Real.rpow_nonneg hbpos _
        have hLg'nn : 0 ≤ Lg' := by
          rw [hLg'def]
          exact Real.rpow_nonneg (Real.log_nonneg (by linarith)) _
        have hCT : (0 : ℝ) ≤ (Cmax : ℝ) * (T : ℝ) := mul_nonneg hCnn hTnn
        have hEe'nn : 0 ≤ Ee' := by
          rw [hEe'def]
          exact Real.rpow_nonneg (by linarith) _
        have h12 : X1 * Up ≤ (W * Mg) * Bp := mul_le_mul hX1 hUp hUpnn (mul_nonneg hWnn hMgnn)
        have h345 : Lg * V * Ee ≤ (Lg' * V) * Ee' := by
          have hLV : Lg * V ≤ Lg' * V := mul_le_mul_of_nonneg_right hLg hVnn'
          exact mul_le_mul hLV hEe hEenn (mul_nonneg hLg'nn hVnn')
        have key : X1 * Up * Lg * V * Ee ≤ (W * Mg) * Bp * Lg' * V * Ee' := by
          calc X1 * Up * Lg * V * Ee = (X1 * Up) * ((Lg * V) * Ee) := by ring
            _ ≤ ((W * Mg) * Bp) * ((Lg' * V) * Ee') :=
                mul_le_mul h12 h345
                  (mul_nonneg (mul_nonneg hLgnn hVnn') hEenn)
                  (mul_nonneg (mul_nonneg hWnn hMgnn) hBpnn)
            _ = (W * Mg) * Bp * Lg' * V * Ee' := by ring
        calc C1 * X1 * Up * Lg * V * Ee
            = C1 * (X1 * Up * Lg * V * Ee) := by ring
          _ ≤ C1 * ((W * Mg) * Bp * Lg' * V * Ee') := mul_le_mul_of_nonneg_left key hC1.le
          _ = (C1 * W) * Mg * Bp * Ee' * Lg' * V := by ring
      exact le_trans hbnd' harith


end Work.FIArea7
