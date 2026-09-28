import Mathlib
import Submission.Work.HP.ArchDefs
import Submission.Work.HP.ArchGlueV2
import Submission.Work.HP.tau_basic
import Submission.Work.HP.dyadic_pigeonhole
import Submission.Work.HP.small_union_volV2

/-!
# `Work.HP.tau_vol_le`

Volume bound for the set of coefficient vectors of norm `≤ 1` which are `IPt` and have a small
Archimedean factor `τ(a;γ) < s`:

`vol{a : IPt a ∧ ‖a‖ ≤ 1 ∧ τ(a;γ) < s} ≤ K · s^{1/n}`, uniformly in `γ ≥ 1`.

The proof covers `IPt ∩ B(1)` by the dyadic strata `Bset d n (M/2^ℓ)` together with the
degenerate set `Lset d n` (measure zero).  On a stratum `Bset λ` with `λ ≤ 1` the hypothesis
`hlow` gives `τ ≥ Kt · λ^{n+1}`, so only the scales `λ ≤ σ := (s/Kt)^{1/(n+1)}` contribute;
their volumes are `≪ λ²` and sum to `≪ σ²`.  The scales `λ > 1` are bounded by the unit ball,
whose volume is finite.
-/

set_option autoImplicit false

noncomputable section

open Classical Finset MvPolynomial MeasureTheory
open scoped BigOperators ENNReal

namespace Work.HP

/-! ## Elementary helpers -/

/-- For `0 ≤ λ ≤ 1` the minimum of the two powers is the smaller (larger-exponent) one. -/
lemma min_pow_of_le_one {n : ℕ} {lam : ℝ} (h0 : 0 ≤ lam) (h1 : lam ≤ 1) :
    min (lam ^ (n + 1)) (lam ^ (n - 1)) = lam ^ (n + 1) := by
  rw [min_eq_left]
  exact pow_le_pow_of_le_one h0 h1 (by omega)

/-- For `1 ≤ λ` the minimum of the two powers is the smaller (smaller-exponent) one. -/
lemma min_pow_of_one_lt {n : ℕ} {lam : ℝ} (h1 : 1 ≤ lam) :
    min (lam ^ (n + 1)) (lam ^ (n - 1)) = lam ^ (n - 1) := by
  rw [min_eq_right]
  exact pow_le_pow_right₀ h1 (by omega)

/-- From `x ^ m < t` with `x ≥ 0`, `t > 0`, `m ≥ 1`, deduce `x < t ^ (1/m)`. -/
lemma lt_rpow_one_div_of_pow_lt {x t : ℝ} {m : ℕ} (hm : 0 < m) (hx : 0 ≤ x) (ht : 0 < t)
    (h : x ^ m < t) : x < t ^ (1 / (m : ℝ)) := by
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hx' : (0 : ℝ) ≤ x ^ ((m : ℝ)) := by
    rw [Real.rpow_natCast]; exact pow_nonneg hx m
  have h' : x ^ ((m : ℝ)) < t := by rw [Real.rpow_natCast]; exact h
  have h2 : (x ^ ((m : ℝ))) ^ (1 / (m : ℝ)) < t ^ (1 / (m : ℝ)) :=
    Real.rpow_lt_rpow hx' h' (div_pos one_pos hmR)
  have h3 : (x ^ ((m : ℝ))) ^ (1 / (m : ℝ)) = x := by
    rw [← Real.rpow_mul hx, mul_one_div, div_self (ne_of_gt hmR), Real.rpow_one]
  rwa [h3] at h2

/-- Every element of `IPt ∩ B(1)` lies in one of the dyadic strata `Bset d n (M/2^ℓ)` or in
the degenerate set `Lset`.  (A `sorry`-free replacement for `Work.HP.cover_Bset`, which
depends on the not-yet-finished `dyadic_sum_tools`.) -/
lemma cover_ip (d n : ℕ) (hd : 2 ≤ d) (hn : 3 ≤ n) {M : ℝ} (hM : 0 < M)
    (hgrad : ∀ (a : Mon d n → ℝ) (x : Fin (n + 1) → ℝ), rNorm x ≤ 1 →
      rNorm (gradVec d n a x) ≤ M * rNorm a) :
    {a : Mon d n → ℝ | IPt d n a ∧ rNorm a ≤ 1} ⊆
      (⋃ ℓ : ℕ, Bset d n (M / 2 ^ ℓ)) ∪ Lset d n := by
  rintro a ⟨haI, ha1⟩
  obtain ⟨x, hx1, hx0⟩ := haI
  by_cases hg : gradVec d n a x = 0
  · exact Or.inr ⟨ha1, x, hx1, hx0, hg⟩
  · have hμpos : 0 < rNorm (gradVec d n a x) :=
      lt_of_le_of_ne (rNorm_nonneg _) (fun h => hg (rNorm_eq_zero.mp h.symm))
    have ha0 : a ≠ 0 := by
      intro h
      apply hg
      rw [h]
      funext j
      simp [gradVec, gradF]
    have han : 0 < rNorm a :=
      lt_of_le_of_ne (rNorm_nonneg _) (fun h => ha0 (rNorm_eq_zero.mp h.symm))
    have htM : rNorm (gradVec d n a x) / rNorm a ≤ M := by
      rw [div_le_iff₀ han]
      exact hgrad a x hx1.le
    obtain ⟨ℓ, hℓ1, hℓ2⟩ :=
      dyadic_pigeonhole M _ hM (div_pos hμpos han) htM
    have hlt : M / 2 ^ ℓ * rNorm a < rNorm (gradVec d n a x) := by
      calc M / 2 ^ ℓ * rNorm a < rNorm (gradVec d n a x) / rNorm a * rNorm a :=
            mul_lt_mul_of_pos_right hℓ1 han
        _ = rNorm (gradVec d n a x) := div_mul_cancel₀ _ han.ne'
    have hle : rNorm (gradVec d n a x) ≤ 2 * (M / 2 ^ ℓ) * rNorm a := by
      calc rNorm (gradVec d n a x)
          = rNorm (gradVec d n a x) / rNorm a * rNorm a := (div_mul_cancel₀ _ han.ne').symm
        _ ≤ (2 * (M / 2 ^ ℓ)) * rNorm a := mul_le_mul_of_nonneg_right hℓ2 han.le
    have hmem : a ∈ Bset d n (M / 2 ^ ℓ) :=
      ⟨ha1, ⟨x, hx1, hx0⟩, x, hx1, hx0, hlt, hle⟩
    rw [Set.mem_union, Set.mem_iUnion]
    exact Or.inl ⟨ℓ, hmem⟩

/-! ## The two `Real.rpow` arithmetic lemmas -/

/-- Small-`s` regime: `Kb · (16/3) · (s/Kt)^{2/(n+1)} ≪ s^{1/n}` for `s ≤ Kt`. -/
lemma rpow_small_bound (n : ℕ) (hn : 1 ≤ n) {Kb Kt : ℝ} (hKb : 0 < Kb) (hKt : 0 < Kt) :
    ∃ K : ℝ, 0 < K ∧ ∀ s : ℝ, 0 < s → s ≤ Kt →
      Kb * (16 / 3) * ((s / Kt) ^ (1 / ((n : ℝ) + 1))) ^ 2 ≤ K * s ^ (1 / (n : ℝ)) := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hn1R : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < 1 / (n : ℝ) := div_pos one_pos hnR
  refine ⟨Kb * (16 / 3) / Kt ^ (1 / (n : ℝ)),
    div_pos (by positivity) (Real.rpow_pos_of_pos hKt _), ?_⟩
  intro s hs hsKt
  have hspos : 0 < s / Kt := div_pos hs hKt
  have hx1 : s / Kt ≤ 1 := (div_le_one hKt).mpr hsKt
  have hexp : (1 : ℝ) / (n : ℝ) ≤ 2 / ((n : ℝ) + 1) := by
    rw [div_le_iff₀ hnR, div_mul_eq_mul_div,
      le_div_iff₀ (by linarith : (0 : ℝ) < (n : ℝ) + 1)]
    linarith [hn1R]
  have hx : (s / Kt) ^ (2 / ((n : ℝ) + 1)) ≤ (s / Kt) ^ (1 / (n : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_ge hspos hx1 hexp
  have hL : ((s / Kt) ^ (1 / ((n : ℝ) + 1))) ^ 2 = (s / Kt) ^ (2 / ((n : ℝ) + 1)) := by
    rw [← Real.rpow_natCast ((s / Kt) ^ (1 / ((n : ℝ) + 1))) 2,
      ← Real.rpow_mul (le_of_lt hspos)]
    congr 1
    ring
  have hR : s ^ (1 / (n : ℝ)) / Kt ^ (1 / (n : ℝ)) = (s / Kt) ^ (1 / (n : ℝ)) :=
    (Real.div_rpow hs.le hKt.le _).symm
  have hfactor : Kb * (16 / 3) / Kt ^ (1 / (n : ℝ)) * s ^ (1 / (n : ℝ))
      = Kb * (16 / 3) * (s ^ (1 / (n : ℝ)) / Kt ^ (1 / (n : ℝ))) := by ring
  rw [hL, hfactor, hR]
  exact mul_le_mul_of_nonneg_left hx (by positivity)

/-- Large-`s` regime: a constant is `≪ s^{1/n}` once `s > Kt`. -/
lemma rpow_large_bound (n : ℕ) (hn : 1 ≤ n) {Kt A : ℝ} (hKt : 0 < Kt) (hA : 0 ≤ A) :
    ∃ K : ℝ, 0 < K ∧ ∀ s : ℝ, Kt < s → A ≤ K * s ^ (1 / (n : ℝ)) := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hnpos : (0 : ℝ) < 1 / (n : ℝ) := div_pos one_pos hnR
  refine ⟨(A + 1) / Kt ^ (1 / (n : ℝ)) + 1,
    by exact add_pos (div_pos (by linarith) (Real.rpow_pos_of_pos hKt _)) one_pos, ?_⟩
  intro s hs
  have hKtp : 0 < Kt ^ (1 / (n : ℝ)) := Real.rpow_pos_of_pos hKt _
  have hspos : 0 < s := lt_trans hKt hs
  have hspos' : 0 ≤ s ^ (1 / (n : ℝ)) := Real.rpow_nonneg hspos.le _
  have hle : Kt ^ (1 / (n : ℝ)) ≤ s ^ (1 / (n : ℝ)) :=
    Real.rpow_le_rpow hKt.le hs.le hnpos.le
  have h1 : (A + 1) ≤ ((A + 1) / Kt ^ (1 / (n : ℝ))) * s ^ (1 / (n : ℝ)) := by
    have hmul := mul_le_mul_of_nonneg_left hle
      (show (0 : ℝ) ≤ (A + 1) / Kt ^ (1 / (n : ℝ)) by positivity)
    rwa [div_mul_cancel₀ (A + 1) (ne_of_gt hKtp)] at hmul
  calc A ≤ A + 1 := by linarith
    _ ≤ ((A + 1) / Kt ^ (1 / (n : ℝ))) * s ^ (1 / (n : ℝ)) := h1
    _ ≤ ((A + 1) / Kt ^ (1 / (n : ℝ)) + 1) * s ^ (1 / (n : ℝ)) := by
        apply mul_le_mul_of_nonneg_right _ hspos'
        linarith

/-! ## The main theorem -/

theorem tau_vol_le (d n : ℕ) (hd : 2 ≤ d) (hn : 3 ≤ n)
    {M Kt Kb : ℝ} (hM : 0 < M) (hKt : 0 < Kt) (hKb : 0 < Kb)
    (hgrad : ∀ (a : Mon d n → ℝ) (x : Fin (n + 1) → ℝ), rNorm x ≤ 1 →
      rNorm (gradVec d n a x) ≤ M * rNorm a)
    (hlow : ∀ (a : Mon d n → ℝ) (lam γ : ℝ), 0 < lam → 1 ≤ γ → a ∈ Bset d n lam →
      Kt * min (lam ^ (n + 1)) (lam ^ (n - 1)) ≤ tauArch d n a γ)
    (hbvol : ∀ lam : ℝ, 0 < lam → lam ≤ 1 →
      volume (Bset d n lam) ≤ ENNReal.ofReal (Kb * lam ^ 2))
    (hL : volume (Lset d n) = 0)
    (hgeom : ∀ (M' σ : ℝ), 0 < M' → 0 < σ →
      (∑' ℓ : ℕ, (if M' / 2 ^ ℓ < σ then ENNReal.ofReal ((M' / 2 ^ ℓ) ^ 2) else 0))
        ≤ ENNReal.ofReal ((4 / 3) * σ ^ 2))
    (hcnt : ({ℓ : ℕ | 1 < M / 2 ^ ℓ}.ncard : ℝ) ≤ (Nat.ceil M : ℝ) + 1)
    (hV : volume {a : Mon d n → ℝ | rNorm a ≤ 1} ≠ ⊤) :
    ∃ K : ℝ, 0 < K ∧ ∀ (γ s : ℝ), 1 ≤ γ → 0 < s →
      volume {a : Mon d n → ℝ | IPt d n a ∧ rNorm a ≤ 1 ∧ tauArch d n a γ < s}
        ≤ ENNReal.ofReal (K * s ^ (1 / (n : ℝ))) := by
  have hn1 : 1 ≤ n := by omega
  -- the volume of the unit ball, as a real number
  set V0 : ℝ := (volume {a : Mon d n → ℝ | rNorm a ≤ 1}).toReal with hV0def
  have hV0nn : 0 ≤ V0 := by rw [hV0def]; exact ENNReal.toReal_nonneg
  have hballV : volume {a : Mon d n → ℝ | rNorm a ≤ 1} = ENNReal.ofReal V0 := by
    rw [hV0def]; exact (ENNReal.ofReal_toReal hV).symm
  -- the two constants
  obtain ⟨K1, hK1pos, hK1⟩ := rpow_small_bound n hn1 hKb hKt
  have hnumpos : 0 < Kb * (16 / 3) + V0 + 1 := by positivity
  set K2 : ℝ := (Kb * (16 / 3) + V0 + 1) / Kt ^ (1 / (n : ℝ)) + 1 with hK2def
  have hK2pos : 0 < K2 := by
    rw [hK2def]
    exact add_pos (div_pos hnumpos (Real.rpow_pos_of_pos hKt _)) one_pos
  -- the generic cover
  have hcov : {a : Mon d n → ℝ | IPt d n a ∧ rNorm a ≤ 1} ⊆
      (⋃ ℓ : ℕ, Bset d n (M / 2 ^ ℓ)) ∪ Lset d n := cover_ip d n hd hn hM hgrad
  refine ⟨max K1 K2, lt_of_lt_of_le hK1pos (le_max_left _ _), ?_⟩
  intro γ s hγ hs
  set S : Set (Mon d n → ℝ) :=
    {a : Mon d n → ℝ | IPt d n a ∧ rNorm a ≤ 1 ∧ tauArch d n a γ < s} with hSdef
  have hfac : 0 < 1 / (n : ℝ) := by
    apply div_pos one_pos
    exact_mod_cast (by omega : 0 < n)
  by_cases hsKt : s ≤ Kt
  · -- Case 1: `s ≤ Kt`
    set σ : ℝ := (s / Kt) ^ (1 / ((n : ℝ) + 1)) with hσdef
    have hσpos : 0 < σ := Real.rpow_pos_of_pos (div_pos hs hKt) _
    have hσle1 : σ ≤ 1 := by
      rw [hσdef]
      refine Real.rpow_le_one (div_nonneg hs.le hKt.le) ?_ (by positivity)
      rw [div_le_one hKt]; exact hsKt
    have hsub : S ⊆ (⋃ ℓ : ℕ, (if M / 2 ^ ℓ ≤ σ then Bset d n (M / 2 ^ ℓ) else ∅))
        ∪ Lset d n := by
      intro a ha
      have haI : a ∈ {a : Mon d n → ℝ | IPt d n a ∧ rNorm a ≤ 1} := ⟨ha.1, ha.2.1⟩
      rcases hcov haI with hU | hLs
      · rcases Set.mem_iUnion.mp hU with ⟨ℓ, hℓ⟩
        have hpos : 0 < M / 2 ^ ℓ := by positivity
        have hmin := hlow a (M / 2 ^ ℓ) γ hpos hγ hℓ
        have hτs : tauArch d n a γ < s := ha.2.2
        have hleσ : M / 2 ^ ℓ ≤ σ := by
          by_cases h1 : M / 2 ^ ℓ ≤ 1
          · rw [min_pow_of_le_one hpos.le h1] at hmin
            have hlt : (M / 2 ^ ℓ) ^ (n + 1) < s / Kt := by
              rw [lt_div_iff₀ hKt, mul_comm]
              exact lt_of_le_of_lt hmin hτs
            have hlt2 : M / 2 ^ ℓ < (s / Kt) ^ (1 / (((n + 1 : ℕ)) : ℝ)) :=
              lt_rpow_one_div_of_pow_lt (by omega) hpos.le (div_pos hs hKt) hlt
            have hexp : (1 : ℝ) / (((n + 1 : ℕ)) : ℝ) = 1 / ((n : ℝ) + 1) := by norm_num
            rw [hexp] at hlt2
            rw [hσdef]; exact hlt2.le
          · push_neg at h1
            rw [min_pow_of_one_lt h1.le] at hmin
            have hone : (1 : ℝ) ≤ (M / 2 ^ ℓ) ^ (n - 1) := by
              have := pow_le_pow_right₀ h1.le (Nat.zero_le (n - 1))
              simpa using this
            have hKgts : Kt < s := by
              have hle : Kt ≤ Kt * (M / 2 ^ ℓ) ^ (n - 1) := by
                have hm := mul_le_mul_of_nonneg_left hone hKt.le
                rwa [mul_one] at hm
              exact lt_of_le_of_lt (le_trans hle hmin) hτs
            exact absurd hsKt (not_le.mpr hKgts)
        rw [Set.mem_union]
        left
        exact Set.mem_iUnion.mpr ⟨ℓ, by rw [if_pos hleσ]; exact hℓ⟩
      · exact Or.inr hLs
    calc volume S
        ≤ volume ((⋃ ℓ : ℕ, (if M / 2 ^ ℓ ≤ σ then Bset d n (M / 2 ^ ℓ) else ∅))
            ∪ Lset d n) := measure_mono hsub
      _ ≤ volume (⋃ ℓ : ℕ, (if M / 2 ^ ℓ ≤ σ then Bset d n (M / 2 ^ ℓ) else ∅))
            + volume (Lset d n) := measure_union_le _ _
      _ = volume (⋃ ℓ : ℕ, (if M / 2 ^ ℓ ≤ σ then Bset d n (M / 2 ^ ℓ) else ∅)) + 0 := by
            rw [hL]
      _ ≤ ENNReal.ofReal (Kb * (16 / 3) * σ ^ 2) + 0 :=
            add_le_add (small_union_vol d n hM hKb.le hbvol hgeom hσpos hσle1) le_rfl
      _ = ENNReal.ofReal (Kb * (16 / 3) * σ ^ 2) := add_zero _
      _ ≤ ENNReal.ofReal (K1 * s ^ (1 / (n : ℝ))) :=
            ENNReal.ofReal_le_ofReal (by rw [hσdef]; exact hK1 s hs hsKt)
      _ ≤ ENNReal.ofReal (max K1 K2 * s ^ (1 / (n : ℝ))) :=
            ENNReal.ofReal_le_ofReal
              (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hs.le _))
  · -- Case 2: `Kt < s`
    push_neg at hsKt
    have hsub : S ⊆
        (⋃ ℓ : ℕ, (if M / 2 ^ ℓ ≤ 1 then Bset d n (M / 2 ^ ℓ) else ∅))
        ∪ (⋃ ℓ : ℕ, (if 1 < M / 2 ^ ℓ then Bset d n (M / 2 ^ ℓ) else ∅)) ∪ Lset d n := by
      intro a ha
      have haI : a ∈ {a : Mon d n → ℝ | IPt d n a ∧ rNorm a ≤ 1} := ⟨ha.1, ha.2.1⟩
      rcases hcov haI with hU | hLs
      · rcases Set.mem_iUnion.mp hU with ⟨ℓ, hℓ⟩
        by_cases h1 : M / 2 ^ ℓ ≤ 1
        · exact Or.inl (Or.inl (Set.mem_iUnion.mpr ⟨ℓ, by rw [if_pos h1]; exact hℓ⟩))
        · push_neg at h1
          exact Or.inl (Or.inr (Set.mem_iUnion.mpr ⟨ℓ, by rw [if_pos h1]; exact hℓ⟩))
      · exact Or.inr hLs
    have hsmall : volume (⋃ ℓ : ℕ, (if M / 2 ^ ℓ ≤ 1 then Bset d n (M / 2 ^ ℓ) else ∅))
        ≤ ENNReal.ofReal (Kb * (16 / 3)) := by
      have h := small_union_vol d n hM hKb.le hbvol hgeom
        (show (0 : ℝ) < 1 by norm_num) (le_refl 1)
      simpa using h
    have hlarge : volume (⋃ ℓ : ℕ, (if 1 < M / 2 ^ ℓ then Bset d n (M / 2 ^ ℓ) else ∅))
        ≤ ENNReal.ofReal V0 := by
      calc volume (⋃ ℓ : ℕ, (if 1 < M / 2 ^ ℓ then Bset d n (M / 2 ^ ℓ) else ∅))
          ≤ volume {a : Mon d n → ℝ | rNorm a ≤ 1} := by
            apply measure_mono
            intro a ha
            rcases Set.mem_iUnion.mp ha with ⟨ℓ, hℓ⟩
            by_cases h : 1 < M / 2 ^ ℓ
            · rw [if_pos h] at hℓ; exact hℓ.1
            · rw [if_neg h] at hℓ; exact absurd hℓ (Set.notMem_empty a)
        _ = ENNReal.ofReal V0 := hballV
    have hb1 : volume ((⋃ ℓ : ℕ, (if M / 2 ^ ℓ ≤ 1 then Bset d n (M / 2 ^ ℓ) else ∅))
          ∪ (⋃ ℓ : ℕ, (if 1 < M / 2 ^ ℓ then Bset d n (M / 2 ^ ℓ) else ∅)))
        ≤ volume (⋃ ℓ : ℕ, (if M / 2 ^ ℓ ≤ 1 then Bset d n (M / 2 ^ ℓ) else ∅))
          + volume (⋃ ℓ : ℕ, (if 1 < M / 2 ^ ℓ then Bset d n (M / 2 ^ ℓ) else ∅)) :=
      measure_union_le _ _
    have hb2 : volume ((⋃ ℓ : ℕ, (if M / 2 ^ ℓ ≤ 1 then Bset d n (M / 2 ^ ℓ) else ∅))
          ∪ (⋃ ℓ : ℕ, (if 1 < M / 2 ^ ℓ then Bset d n (M / 2 ^ ℓ) else ∅)) ∪ Lset d n)
        ≤ volume ((⋃ ℓ : ℕ, (if M / 2 ^ ℓ ≤ 1 then Bset d n (M / 2 ^ ℓ) else ∅))
          ∪ (⋃ ℓ : ℕ, (if 1 < M / 2 ^ ℓ then Bset d n (M / 2 ^ ℓ) else ∅)))
          + volume (Lset d n) := measure_union_le _ _
    have hfin : Kb * (16 / 3) + V0 ≤ max K1 K2 * s ^ (1 / (n : ℝ)) := by
      have hspos1n : 0 ≤ s ^ (1 / (n : ℝ)) := Real.rpow_nonneg (lt_trans hKt hsKt).le _
      have hKtp : 0 < Kt ^ (1 / (n : ℝ)) := Real.rpow_pos_of_pos hKt _
      have hmono : Kt ^ (1 / (n : ℝ)) < s ^ (1 / (n : ℝ)) :=
        Real.rpow_lt_rpow hKt.le hsKt hfac
      have h1 : Kb * (16 / 3) + V0 + 1
          ≤ ((Kb * (16 / 3) + V0 + 1) / Kt ^ (1 / (n : ℝ))) * s ^ (1 / (n : ℝ)) := by
        have hmul := mul_le_mul_of_nonneg_left hmono.le
          (show (0 : ℝ) ≤ (Kb * (16 / 3) + V0 + 1) / Kt ^ (1 / (n : ℝ)) by positivity)
        rwa [div_mul_cancel₀ (Kb * (16 / 3) + V0 + 1) (ne_of_gt hKtp)] at hmul
      have h2 : Kb * (16 / 3) + V0 ≤ K2 * s ^ (1 / (n : ℝ)) := by
        rw [hK2def]
        have h3 : ((Kb * (16 / 3) + V0 + 1) / Kt ^ (1 / (n : ℝ))) * s ^ (1 / (n : ℝ))
            ≤ ((Kb * (16 / 3) + V0 + 1) / Kt ^ (1 / (n : ℝ)) + 1) * s ^ (1 / (n : ℝ)) :=
          mul_le_mul_of_nonneg_right (by linarith) hspos1n
        linarith
      exact le_trans h2 (mul_le_mul_of_nonneg_right (le_max_right K1 K2) hspos1n)
    have hcomb : ENNReal.ofReal (Kb * (16 / 3)) + ENNReal.ofReal V0
        = ENNReal.ofReal (Kb * (16 / 3) + V0) :=
      (ENNReal.ofReal_add (by positivity) hV0nn).symm
    calc volume S
        ≤ volume ((⋃ ℓ : ℕ, (if M / 2 ^ ℓ ≤ 1 then Bset d n (M / 2 ^ ℓ) else ∅))
            ∪ (⋃ ℓ : ℕ, (if 1 < M / 2 ^ ℓ then Bset d n (M / 2 ^ ℓ) else ∅)) ∪ Lset d n) :=
          measure_mono hsub
      _ ≤ volume ((⋃ ℓ : ℕ, (if M / 2 ^ ℓ ≤ 1 then Bset d n (M / 2 ^ ℓ) else ∅))
            ∪ (⋃ ℓ : ℕ, (if 1 < M / 2 ^ ℓ then Bset d n (M / 2 ^ ℓ) else ∅)))
            + volume (Lset d n) := hb2
      _ = volume ((⋃ ℓ : ℕ, (if M / 2 ^ ℓ ≤ 1 then Bset d n (M / 2 ^ ℓ) else ∅))
            ∪ (⋃ ℓ : ℕ, (if 1 < M / 2 ^ ℓ then Bset d n (M / 2 ^ ℓ) else ∅))) + 0 := by rw [hL]
      _ ≤ (volume (⋃ ℓ : ℕ, (if M / 2 ^ ℓ ≤ 1 then Bset d n (M / 2 ^ ℓ) else ∅))
            + volume (⋃ ℓ : ℕ, (if 1 < M / 2 ^ ℓ then Bset d n (M / 2 ^ ℓ) else ∅))) + 0 :=
          add_le_add hb1 le_rfl
      _ ≤ (ENNReal.ofReal (Kb * (16 / 3)) + ENNReal.ofReal V0) + 0 :=
          add_le_add (add_le_add hsmall hlarge) le_rfl
      _ = ENNReal.ofReal (Kb * (16 / 3)) + ENNReal.ofReal V0 := add_zero _
      _ = ENNReal.ofReal (Kb * (16 / 3) + V0) := hcomb
      _ ≤ ENNReal.ofReal (max K1 K2 * s ^ (1 / (n : ℝ))) := ENNReal.ofReal_le_ofReal hfin

end Work.HP
