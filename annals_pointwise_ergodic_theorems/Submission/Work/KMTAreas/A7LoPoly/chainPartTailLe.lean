import Mathlib
import Submission.Work.KMTPlan.A6.ContinuousVarFromLatticeR

/-!
# The chain part of a walk truncated from below

`Work.KMTAreas.A7Hi.chainPart r a` is the chain term of the `r`-variational norm of a sequence
`a : ℕ → ℂ`: the supremum, over monotone chains `N` and lengths `J`, of the `ℓ^r` norm of the jump
vector `i ↦ a (N (i+1)) - a (N i)`.

The target compares the chain functional of the **truncated** walk `n ↦ if n < M then 0 else a n`
— the walk `a` with its first `M` values replaced by `0` — with the tail `r`-variation
`varRhoFrom r M a` of the original walk (the `r`-variation over chains whose indices all lie in the
tail `[M, ∞)`):

`chainPart r (n ↦ if n < M then 0 else a n) ≤ 2 * supPart r a + 2 * varRhoFrom r M a`.

**The mechanism.**  Fix a chain `N` and split each jump coordinate `i < J` according to whether the
chain has already entered the tail at `N i`:

`DA i = if M ≤ N i then D i else 0`  (the "already in the tail" part),
`DB i = if M ≤ N i then 0 else D i`  (the "still in the head" part), `D = DA + DB`;

the `ℓ^r` norm is subadditive (`‖toLp DA + toLp DB‖ ≤ ‖toLp DA‖ + ‖toLp DB‖`).

* On the head part `DB`, `D i ≠ 0` forces `N i < M ≤ N (i+1)`: the walk jumps from `0` to `a (N (i+1))`
  exactly once, because *two* such crossing coordinates `i < i'` would give
  `M ≤ N (i+1) ≤ N i' < M`.  Hence the support of `DB` has at most one point and every entry is
  bounded by `supPart r a` (`ofReal_norm_toLp_le_of_support`).
* On the tail part `DA`, `DA` is the jump vector of `a` along the sub-chain of `N` living beyond
  `M`.  Writing `L` for the first index with `M ≤ N L` (if there is one), the auxiliary chain
  `w j = if j < L then N L else N j` is monotone with `M ≤ w j ≤ N J` for `j ≤ J`, and
  `DA i = a (w (i+1)) - a (w i)` for **every** `i < J`: the artificial constant prefix `N L` makes
  the jumps below `L` vanish without any reindexing of `Fin J`.  So
  `ofReal ‖toLp DA‖ = ofReal (chainLp r J a w) ≤ varRho r M (N J) a ≤ varRhoFrom r M a`.

If no index satisfies `M ≤ N i`, then `DA = 0` and the same single-support bound applies with `α = V`.
-/

namespace Work.KMTAreas.A7LoPoly

open scoped ENNReal NNReal BigOperators

/-- **The `ℓ^r` norm of a vector supported on at most one point.**  For `1 ≤ r`, if
`d : Fin J → ℂ` vanishes off a set of cardinality at most `1` and every entry is bounded by `α`
in the extended norm, then `ofReal ‖WithLp.toLp r d‖ ≤ α`.

The `ℓ^r` norm is the `r`-sum `(Σ_i ‖d i‖ₑ^r)^{1/r}`
(`Work.KMTAreas.A7.ofReal_norm_toLp_eq_sum`); at most one summand is nonzero and it is `≤ α^r`, so
the sum is `≤ 1 · α^r` and taking `r`-th roots gives `≤ α`. -/
private lemma ofReal_norm_toLp_le_of_support {r : NNReal} (hr : 1 ≤ r) {J : ℕ} {d : Fin J → ℂ}
    {α : ℝ≥0∞} (hcard : (Finset.univ.filter (fun i : Fin J => d i ≠ 0)).card ≤ 1)
    (hbound : ∀ i : Fin J, ‖d i‖ₑ ≤ α) :
    ENNReal.ofReal ‖WithLp.toLp r d‖ ≤ α := by
  classical
  have hr0 : (0 : ℝ) < (r : ℝ) := by
    have : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
    linarith
  rw [Work.KMTAreas.A7.ofReal_norm_toLp_eq_sum r hr d]
  set c : ℝ≥0∞ := (((Finset.univ.filter (fun i : Fin J => d i ≠ 0)).card : ℕ) : ℝ≥0∞) with hc
  have hsum : (∑ i : Fin J, ‖d i‖ₑ ^ (r : ℝ)) ≤ c * α ^ (r : ℝ) := by
    have hsplit : (∑ i : Fin J, ‖d i‖ₑ ^ (r : ℝ))
        = ∑ i ∈ Finset.univ.filter (fun i : Fin J => d i ≠ 0), ‖d i‖ₑ ^ (r : ℝ) := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases hi : d i ≠ 0
      · rw [if_pos hi]
      · rw [if_neg hi]
        rw [show d i = 0 from by simpa using hi]
        simp [ENNReal.zero_rpow_of_pos hr0]
    rw [hsplit, hc]
    calc ∑ i ∈ Finset.univ.filter (fun i : Fin J => d i ≠ 0), ‖d i‖ₑ ^ (r : ℝ)
        ≤ ∑ _i ∈ Finset.univ.filter (fun i : Fin J => d i ≠ 0), α ^ (r : ℝ) :=
          Finset.sum_le_sum (fun i _ => ENNReal.rpow_le_rpow (hbound i) hr0.le)
      _ = ((Finset.univ.filter (fun i : Fin J => d i ≠ 0)).card : ℕ) * α ^ (r : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  have hc1 : c ≤ 1 := by
    rw [hc]
    exact_mod_cast hcard
  calc (((∑ i : Fin J, ‖d i‖ₑ ^ (r : ℝ))) ^ (1 / (r : ℝ)))
      ≤ (c * α ^ (r : ℝ)) ^ (1 / (r : ℝ)) := ENNReal.rpow_le_rpow hsum (by positivity)
    _ = c ^ (1 / (r : ℝ)) * (α ^ (r : ℝ)) ^ (1 / (r : ℝ)) :=
        ENNReal.mul_rpow_of_nonneg _ _ (by positivity)
    _ = c ^ (1 / (r : ℝ)) * α := by
        rw [← ENNReal.rpow_mul, mul_one_div, div_self hr0.ne', ENNReal.rpow_one]
    _ ≤ 1 ^ (1 / (r : ℝ)) * α :=
        mul_le_mul_of_nonneg_right (ENNReal.rpow_le_rpow hc1 (by positivity)) bot_le
    _ = α := by rw [ENNReal.one_rpow, one_mul]

/-- **The chain part of a walk truncated from below is controlled by the tail variation.** -/
theorem chainPartTailLe (r : NNReal) (hr : 1 ≤ r) (M : ℕ) (a : ℕ → ℂ) :
    Work.KMTAreas.A7Hi.chainPart r (fun n : ℕ => if n < M then 0 else a n)
      ≤ 2 * Work.KMTAreas.A7Hi.supPart r a
        + 2 * Work.BourgainPlan.Maximal.varRhoFrom (r : ℝ) M a := by
  haveI : Fact (1 ≤ (r : ℝ≥0∞)) := ⟨by exact_mod_cast hr⟩
  have hr0 : (0 : ℝ) < (r : ℝ) := by
    have h : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
    linarith
  set u : ℕ → ℂ := fun n => if n < M then 0 else a n with hu
  set P : ℝ≥0∞ := Work.KMTAreas.A7Hi.supPart r a with hP
  set V : ℝ≥0∞ := Work.BourgainPlan.Maximal.varRhoFrom (r : ℝ) M a with hV
  have hu_apply : ∀ n : ℕ, u n = (if n < M then 0 else a n) := fun n => congrFun hu n
  have hPle : ∀ n : ℕ, ‖a n‖ₑ ≤ P := by
    intro n
    rw [hP]
    exact le_iSup (fun m : ℕ => ‖a m‖ₑ) n
  have key : Work.KMTAreas.A7Hi.chainPart r u ≤ P + V := by
    rw [Work.KMTAreas.A7Hi.chainPart]
    refine iSup_le fun J => iSup_le fun N => iSup_le fun hN => ?_
    set D : Fin J → ℂ := fun i => u (N (i + 1)) - u (N i) with hD
    set DA : Fin J → ℂ := fun i => if M ≤ N (i:ℕ) then D i else 0 with hDA
    set DB : Fin J → ℂ := fun i => if M ≤ N (i:ℕ) then 0 else D i with hDB
    -- the pointwise splitting of the jump vector
    have hDsplit : D = DA + DB := by
      funext i
      have h1 : DA i = (if M ≤ N (i:ℕ) then D i else 0) := congrFun hDA i
      have h2 : DB i = (if M ≤ N (i:ℕ) then 0 else D i) := congrFun hDB i
      rw [Pi.add_apply, h1, h2]
      by_cases h : M ≤ N (i:ℕ)
      · rw [if_pos h, if_pos h, add_zero]
      · rw [if_neg h, if_neg h, zero_add]
    have hnorm : ENNReal.ofReal ‖WithLp.toLp r D‖
        ≤ ENNReal.ofReal ‖WithLp.toLp r DA‖ + ENNReal.ofReal ‖WithLp.toLp r DB‖ := by
      calc ENNReal.ofReal ‖WithLp.toLp r D‖
          = ENNReal.ofReal ‖WithLp.toLp r DA + WithLp.toLp r DB‖ := by
            rw [hDsplit, WithLp.toLp_add]
        _ ≤ ENNReal.ofReal (‖WithLp.toLp r DA‖ + ‖WithLp.toLp r DB‖) :=
            ENNReal.ofReal_le_ofReal (norm_add_le _ _)
        _ = ENNReal.ofReal ‖WithLp.toLp r DA‖ + ENNReal.ofReal ‖WithLp.toLp r DB‖ :=
            ENNReal.ofReal_add (norm_nonneg (WithLp.toLp r DA)) (norm_nonneg (WithLp.toLp r DB))
    -- the head part: at most one crossing coordinate, each entry bounded by `P`
    have hDB : ENNReal.ofReal ‖WithLp.toLp r DB‖ ≤ P := by
      have cross : ∀ i : Fin J, DB i ≠ 0 → N (i:ℕ) < M ∧ M ≤ N ((i:ℕ)+1) := by
        intro i hi
        have h1 : DB i = (if M ≤ N (i:ℕ) then 0 else D i) := congrFun hDB i
        have hni : ¬ (M ≤ N (i:ℕ)) := by
          intro h
          exact hi (by rw [h1, if_pos h])
        refine ⟨not_le.mp hni, ?_⟩
        by_contra hcon
        have hlt : N ((i:ℕ)+1) < M := not_le.mp hcon
        have hDi : D i = u (N ((i:ℕ)+1)) - u (N (i:ℕ)) := congrFun hD i
        have hz1 : u (N ((i:ℕ)+1)) = 0 := by rw [hu_apply]; exact if_pos hlt
        have hz2 : u (N (i:ℕ)) = 0 := by rw [hu_apply]; exact if_pos (not_le.mp hni)
        exact hi (by rw [h1, if_neg hni, hDi, hz1, hz2, sub_zero])
      have hcard : (Finset.univ.filter (fun i : Fin J => DB i ≠ 0)).card ≤ 1 := by
        rw [Finset.card_le_one]
        intro i hi j hj
        by_contra hij
        obtain ⟨hi1, hi2⟩ := cross i (Finset.mem_filter.mp hi).2
        obtain ⟨hj1, hj2⟩ := cross j (Finset.mem_filter.mp hj).2
        have hvne : (i:ℕ) ≠ (j:ℕ) := fun h => hij (Fin.ext h)
        rcases lt_or_gt_of_ne hvne with hlt | hgt
        · have hle : (i:ℕ)+1 ≤ (j:ℕ) := by omega
          have := hN hle
          omega
        · have hle : (j:ℕ)+1 ≤ (i:ℕ) := by omega
          have := hN hle
          omega
      have hbound : ∀ i : Fin J, ‖DB i‖ₑ ≤ P := by
        intro i
        have h1 : DB i = (if M ≤ N (i:ℕ) then 0 else D i) := congrFun hDB i
        by_cases h : M ≤ N (i:ℕ)
        · rw [h1, if_pos h, enorm_zero]; exact bot_le
        · rw [h1, if_neg h]
          have hDi : D i = u (N ((i:ℕ)+1)) - u (N (i:ℕ)) := congrFun hD i
          rcases lt_or_ge (N ((i:ℕ)+1)) M with hlt | hle
          · have hz1 : u (N ((i:ℕ)+1)) = 0 := by rw [hu_apply]; exact if_pos hlt
            have hz2 : u (N (i:ℕ)) = 0 := by rw [hu_apply]; exact if_pos (not_le.mp h)
            rw [hDi, hz1, hz2, sub_zero, enorm_zero]; exact bot_le
          · have hz1 : u (N ((i:ℕ)+1)) = a (N ((i:ℕ)+1)) := by
              rw [hu_apply]; exact if_neg (not_lt.mpr hle)
            have hz2 : u (N (i:ℕ)) = 0 := by rw [hu_apply]; exact if_pos (not_le.mp h)
            rw [hDi, hz1, hz2, sub_zero]
            exact hPle (N ((i:ℕ)+1))
      exact ofReal_norm_toLp_le_of_support hr hcard hbound
    -- the tail part: the sub-chain of `N` beyond `M`, with an artificial constant prefix
    have hDA : ENNReal.ofReal ‖WithLp.toLp r DA‖ ≤ V := by
      by_cases hne : (Finset.univ.filter (fun i : Fin J => M ≤ N (i:ℕ))).Nonempty
      · set S : Finset (Fin J) := Finset.univ.filter (fun i : Fin J => M ≤ N (i:ℕ)) with hS
        have hneS : S.Nonempty := by rwa [hS]
        set L : Fin J := S.min' hneS with hL
        have hLmem : L ∈ S := Finset.min'_mem S hneS
        have hLge : M ≤ N (L:ℕ) := (Finset.mem_filter.mp hLmem).2
        have hLmin : ∀ i : Fin J, M ≤ N (i:ℕ) → (L:ℕ) ≤ (i:ℕ) := by
          intro i hi
          have hh := Finset.min'_le S i (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩)
          rw [← hL] at hh
          exact hh
        have hiff : ∀ i : Fin J, M ≤ N (i:ℕ) ↔ (L:ℕ) ≤ (i:ℕ) :=
          fun i => ⟨fun h => hLmin i h, fun h => le_trans hLge (hN h)⟩
        let w : ℕ → ℕ := fun j => if j < (L:ℕ) then N (L:ℕ) else N j
        have hwdef : ∀ j : ℕ, w j = (if j < (L:ℕ) then N (L:ℕ) else N j) := fun j => rfl
        have hwmono : Monotone w := by
          intro i j hij
          rw [hwdef i, hwdef j]
          by_cases hi : i < (L:ℕ)
          · rw [if_pos hi]
            by_cases hj : j < (L:ℕ)
            · rw [if_pos hj]
            · rw [if_neg hj]
              exact hN (by omega)
          · rw [if_neg hi, if_neg (by omega : ¬ j < (L:ℕ))]
            exact hN hij
        have hwbdd : ∀ j : ℕ, j ≤ J → M ≤ w j ∧ w j ≤ N J := by
          intro j hj
          rw [hwdef j]
          by_cases h : j < (L:ℕ)
          · rw [if_pos h]
            exact ⟨hLge, hN (by omega)⟩
          · rw [if_neg h]
            exact ⟨le_trans hLge (hN (by omega)), hN hj⟩
        have hchain : ENNReal.ofReal (Work.BourgainPlan.Maximal.chainLp (r:ℝ) J a w) ≤ V := by
          have h1 : ENNReal.ofReal (Work.BourgainPlan.Maximal.chainLp (r:ℝ) J a w)
              ≤ Work.BourgainPlan.Maximal.varRho (r:ℝ) M (N J) a := by
            rw [Work.BourgainPlan.Maximal.varRho]
            exact le_iSup_of_le J (le_iSup_of_le w (le_iSup_of_le hwmono
              (le_iSup_of_le hwbdd le_rfl)))
          rw [hV, Work.BourgainPlan.Maximal.varRhoFrom]
          exact h1.trans
            (le_iSup (fun hi : ℕ => Work.BourgainPlan.Maximal.varRho (r:ℝ) M hi a) (N J))
        -- the artificial chain reproduces `DA` on every coordinate
        have hDAeq : ∀ i : Fin J, DA i = a (w ((i:ℕ)+1)) - a (w (i:ℕ)) := by
          intro i
          have h1 : DA i = (if M ≤ N (i:ℕ) then D i else 0) := congrFun hDA i
          have hDi : D i = u (N ((i:ℕ)+1)) - u (N (i:ℕ)) := congrFun hD i
          rw [h1]
          by_cases hMi : M ≤ N (i:ℕ)
          · rw [if_pos hMi, hDi]
            have hLi : (L:ℕ) ≤ (i:ℕ) := (hiff i).mp hMi
            have hwi : w (i:ℕ) = N (i:ℕ) := by
              rw [hwdef (i:ℕ)]; exact if_neg (by omega)
            have hwj : w ((i:ℕ)+1) = N ((i:ℕ)+1) := by
              rw [hwdef ((i:ℕ)+1)]; exact if_neg (by omega)
            have hu1 : u (N ((i:ℕ)+1)) = a (N ((i:ℕ)+1)) := by
              rw [hu_apply]
              exact if_neg (not_lt.mpr (le_trans hMi (hN (Nat.le_succ _))))
            have hu0 : u (N (i:ℕ)) = a (N (i:ℕ)) := by
              rw [hu_apply]; exact if_neg (not_lt.mpr hMi)
            rw [hu1, hu0, hwi, hwj]
          · rw [if_neg hMi]
            have hLi : (i:ℕ) < (L:ℕ) := by
              by_contra hcon
              exact hMi ((hiff i).mpr (by omega))
            have hle1 : (i:ℕ)+1 ≤ (L:ℕ) := by omega
            have hwi : w (i:ℕ) = N (L:ℕ) := by
              rw [hwdef (i:ℕ)]; exact if_pos hLi
            rcases lt_or_eq_of_le hle1 with hlt | heq
            · have hwj : w ((i:ℕ)+1) = N (L:ℕ) := by
                rw [hwdef ((i:ℕ)+1)]; exact if_pos hlt
              rw [hwi, hwj, sub_self]
            · have hwj : w ((i:ℕ)+1) = N ((i:ℕ)+1) := by
                rw [hwdef ((i:ℕ)+1)]; exact if_neg (by omega)
              rw [hwi, hwj, heq, sub_self]
        have hnormDA : ENNReal.ofReal ‖WithLp.toLp r DA‖
            = ENNReal.ofReal (Work.BourgainPlan.Maximal.chainLp (r:ℝ) J a w) := by
          have hfun : DA = (fun i : Fin J => a (w ((i:ℕ)+1)) - a (w (i:ℕ))) := funext hDAeq
          rw [hfun]
          exact Work.KMTPlan.A6.ofReal_norm_toLp_eq_ofReal_chainLp r hr J a w
        rw [hnormDA]
        exact hchain
      · -- no index of the chain has reached the tail: `DA` vanishes identically
        have hzero : ∀ i : Fin J, DA i = 0 := by
          intro i
          have h1 : DA i = (if M ≤ N (i:ℕ) then D i else 0) := congrFun hDA i
          rw [h1, if_neg (fun h => hne ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, h⟩⟩)]
        refine ofReal_norm_toLp_le_of_support hr ?_ ?_
        · exact Finset.card_le_one.mpr
            (fun i hi _ _ => absurd (hzero i) (Finset.mem_filter.mp hi).2)
        · intro i
          rw [hzero i, enorm_zero]
          exact bot_le
    calc ENNReal.ofReal ‖WithLp.toLp r D‖
        ≤ ENNReal.ofReal ‖WithLp.toLp r DA‖ + ENNReal.ofReal ‖WithLp.toLp r DB‖ := hnorm
      _ ≤ V + P := add_le_add hDA hDB
      _ = P + V := add_comm _ _
  calc Work.KMTAreas.A7Hi.chainPart r u ≤ P + V := key
    _ ≤ 2 * P + 2 * V := by
        refine add_le_add ?_ ?_
        · exact le_mul_of_one_le_left' (by norm_num)
        · exact le_mul_of_one_le_left' (by norm_num)

end Work.KMTAreas.A7LoPoly
