import Mathlib
import Submission.Work.BourgainPlan.Maximal.mst_freeze_defs

namespace Work.BourgainPlan.Maximal

/-!
# The arithmetic of the freezing estimate

With `J = ⌊exp √(s+1)⌋`, the level scale `c_s = 2^{s(d−χ)}` (`d = P.natDegree ≥ 2`, `0 < χ < 1/10`)
and any fixed `A ≥ 1`, for all sufficiently large `s` the two quotients
`mstThtL P J / c_s` and `(mstThtL P J)² / c_s²` are `≤ A e^{−√(s+1)/2}`.

The proof is elementary: `mstThtL P J = 2π (Σᵢ|cᵢ|) J^d ≤ K e^{d√(s+1)}` for a fixed constant
`K`, while `c_s = e^{s(d−χ) log 2}`, and `√(s+1) = o(s)` against the positive linear rate
`(d−χ) log 2`.  The bulk of the work is the growth comparison for `s ↦ M e^{b√(s+1)}` against
`e^{a s}`, proved here for arbitrary real `a > 0`, `b ≥ 0` and constant `M`.
-/

/-- For `0 < δ`, eventually `√(s+1) ≤ δ s` (an explicit threshold from `δ²s ≥ 2` and `s ≥ 1`). -/
lemma eventually_sqrt_add_one_le_mul (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ s : ℕ in Filter.atTop, Real.sqrt ((s : ℝ) + 1) ≤ δ * (s : ℝ) := by
  refine Filter.eventually_atTop.mpr ⟨max (Nat.ceil (2 / δ ^ 2)) 1, fun s hs => ?_⟩
  have hs1 : 1 ≤ s := le_trans (le_max_right _ _) hs
  have hc_le : Nat.ceil (2 / δ ^ 2) ≤ s := le_trans (le_max_left _ _) hs
  have h2 : 2 / δ ^ 2 ≤ (s : ℝ) := by
    have h1 : 2 / δ ^ 2 ≤ (Nat.ceil (2 / δ ^ 2) : ℝ) := Nat.le_ceil _
    have h2' : (Nat.ceil (2 / δ ^ 2) : ℝ) ≤ (s : ℝ) := by exact_mod_cast hc_le
    linarith
  have hδ2 : 0 < δ ^ 2 := by positivity
  have h3 : 2 ≤ δ ^ 2 * (s : ℝ) := by
    have h := (div_le_iff₀ hδ2).mp h2
    calc (2 : ℝ) ≤ (s : ℝ) * δ ^ 2 := h
      _ = δ ^ 2 * (s : ℝ) := by ring
  have hs1' : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs1
  have hsnn : (0 : ℝ) ≤ (s : ℝ) := by positivity
  have key : (s : ℝ) + 1 ≤ (δ * (s : ℝ)) ^ 2 := by
    have hpq : (δ * (s : ℝ)) ^ 2 = (δ ^ 2 * (s : ℝ)) * (s : ℝ) := by ring
    rw [hpq]
    have h4 : 2 * (s : ℝ) ≤ (δ ^ 2 * (s : ℝ)) * (s : ℝ) :=
      mul_le_mul_of_nonneg_right h3 hsnn
    have h5 : (s : ℝ) + 1 ≤ 2 * (s : ℝ) := by linarith
    linarith
  exact (Real.sqrt_le_left (by positivity)).mpr key

/-- For `0 < a` and `0 ≤ b`, eventually `b √(s+1) ≤ (a/2) s`. -/
lemma eventually_mul_sqrt_add_one_le (a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b) :
    ∀ᶠ s : ℕ in Filter.atTop, b * Real.sqrt ((s : ℝ) + 1) ≤ (a / 2) * (s : ℝ) := by
  rcases lt_or_eq_of_le hb with hbpos | hb0
  · have hδpos : 0 < (a / 2) / b := by positivity
    filter_upwards [eventually_sqrt_add_one_le_mul ((a / 2) / b) hδpos] with s hs
    calc b * Real.sqrt ((s : ℝ) + 1)
        ≤ b * (((a / 2) / b) * (s : ℝ)) := mul_le_mul_of_nonneg_left hs (le_of_lt hbpos)
      _ = (a / 2) * (s : ℝ) := by
          rw [← mul_assoc, mul_div_cancel₀ _ (ne_of_gt hbpos)]
  · subst hb0
    filter_upwards with s
    simp only [zero_mul]
    positivity

/-- **Growth comparison.**  For `0 < a`, `0 ≤ b` and any real `M`,

`M · e^{b √(s+1)} ≤ e^{a s}` for all sufficiently large `s`. -/
lemma eventually_const_mul_exp_sqrt_le_exp (a b M : ℝ) (ha : 0 < a) (hb : 0 ≤ b) :
    ∀ᶠ s : ℕ in Filter.atTop,
      M * Real.exp (b * Real.sqrt ((s : ℝ) + 1)) ≤ Real.exp (a * (s : ℝ)) := by
  have ha2 : 0 < a / 2 := by linarith
  have h1 : ∀ᶠ s : ℕ in Filter.atTop,
      b * Real.sqrt ((s : ℝ) + 1) ≤ (a / 2) * (s : ℝ) :=
    eventually_mul_sqrt_add_one_le a b ha hb
  have h2 : ∀ᶠ s : ℕ in Filter.atTop, M ≤ Real.exp ((a / 2) * (s : ℝ)) := by
    rcases le_or_gt M 0 with hM | hM
    · filter_upwards with s
      exact le_trans hM (le_of_lt (Real.exp_pos _))
    · have htend : Filter.Tendsto (fun s : ℕ => Real.exp ((a / 2) * (s : ℝ)))
          Filter.atTop Filter.atTop :=
        Real.tendsto_exp_atTop.comp (tendsto_natCast_atTop_atTop.const_mul_atTop ha2)
      exact htend.eventually_ge_atTop M
  filter_upwards [h1, h2] with s hs1 hs2
  calc M * Real.exp (b * Real.sqrt ((s : ℝ) + 1))
      ≤ Real.exp ((a / 2) * (s : ℝ)) * Real.exp (b * Real.sqrt ((s : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_right hs2 (le_of_lt (Real.exp_pos _))
    _ ≤ Real.exp ((a / 2) * (s : ℝ)) * Real.exp ((a / 2) * (s : ℝ)) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hs1) (le_of_lt (Real.exp_pos _))
    _ = Real.exp (a * (s : ℝ)) := by
        rw [← Real.exp_add]; congr 1; ring

/-- The level scale as an exponential: `mstScale d χ s = e^{((d−χ) log 2) s}`. -/
lemma mstScale_eq_exp' (d : ℕ) (χ : ℝ) (s : ℕ) :
    mstScale d χ s = Real.exp ((((d : ℝ) - χ) * Real.log 2) * (s : ℝ)) := by
  rw [mstScale, Real.rpow_def_of_pos (show (0 : ℝ) < 2 by norm_num)]
  congr 1
  ring

/-- The square of the level scale as an exponential:
`(mstScale d χ s)² = e^{(2 (d−χ) log 2) s}`. -/
lemma mstScale_sq_eq_exp' (d : ℕ) (χ : ℝ) (s : ℕ) :
    (mstScale d χ s) ^ 2 = Real.exp ((2 * (((d : ℝ) - χ) * Real.log 2)) * (s : ℝ)) := by
  rw [mstScale_eq_exp', ← Real.exp_nat_mul]
  congr 1
  ring

/-- `mstThtL P ⌊e^{√(s+1)}⌋ ≤ M e^{d √(s+1)}` for any `M ≥ 2π (Σᵢ|cᵢ|)`. -/
lemma mstThtL_le_of_max (P : Polynomial ℤ) (s : ℕ) {M : ℝ}
    (hM : 2 * Real.pi * mstCoeffB P ≤ M) (hM0 : 0 ≤ M) :
    mstThtL P ⌊Real.exp (Real.sqrt ((s : ℝ) + 1))⌋₊
      ≤ M * Real.exp ((P.natDegree : ℝ) * Real.sqrt ((s : ℝ) + 1)) := by
  set x : ℝ := Real.exp (Real.sqrt ((s : ℝ) + 1)) with hx
  have hxpos : 0 ≤ x := le_of_lt (Real.exp_pos _)
  have hJle : ((⌊x⌋₊ : ℕ) : ℝ) ≤ x := Nat.floor_le hxpos
  have hpow : ((⌊x⌋₊ : ℕ) : ℝ) ^ P.natDegree ≤ x ^ P.natDegree :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) hJle _
  have hxpow : x ^ P.natDegree = Real.exp ((P.natDegree : ℝ) * Real.sqrt ((s : ℝ) + 1)) := by
    rw [hx, ← Real.exp_nat_mul]
  have hJpow : ((⌊x⌋₊ : ℕ) : ℝ) ^ P.natDegree
      ≤ Real.exp ((P.natDegree : ℝ) * Real.sqrt ((s : ℝ) + 1)) :=
    hpow.trans (le_of_eq hxpow)
  rw [mstThtL]
  calc 2 * Real.pi * mstCoeffB P * (⌊x⌋₊ : ℝ) ^ P.natDegree
      ≤ M * (⌊x⌋₊ : ℝ) ^ P.natDegree :=
        mul_le_mul_of_nonneg_right hM (pow_nonneg (Nat.cast_nonneg _) _)
    _ ≤ M * Real.exp ((P.natDegree : ℝ) * Real.sqrt ((s : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left hJpow hM0

/-- **The abstract division step.**  If `n ≤ M e^{d S}` and `M e^{(d+1/2) S} ≤ D`, then
`n / D ≤ A e^{−S/2}` for `A ≥ 1`, `D > 0`. -/
lemma div_le_mul_exp_of {n M D dd S A : ℝ} (hA : 1 ≤ A) (hD : 0 < D)
    (hn : n ≤ M * Real.exp (dd * S))
    (hbound : M * Real.exp ((dd + 1 / 2) * S) ≤ D) :
    n / D ≤ A * Real.exp (-(S / 2)) := by
  have hsp : Real.exp ((dd + 1 / 2) * S) = Real.exp (dd * S) * Real.exp (S / 2) := by
    rw [← Real.exp_add]; congr 1; ring
  have hMd : M * Real.exp (dd * S) * Real.exp (S / 2) ≤ D := by
    have h : M * Real.exp (dd * S) * Real.exp (S / 2) = M * Real.exp ((dd + 1 / 2) * S) := by
      rw [hsp]; ring
    rw [h]; exact hbound
  have he : Real.exp (S / 2) * Real.exp (-(S / 2)) = 1 := by
    rw [← Real.exp_add]; simp
  have hstep : M * Real.exp (dd * S) ≤ D * Real.exp (-(S / 2)) := by
    have h := mul_le_mul_of_nonneg_right hMd (le_of_lt (Real.exp_pos (-(S / 2))))
    calc M * Real.exp (dd * S)
        = M * Real.exp (dd * S) * Real.exp (S / 2) * Real.exp (-(S / 2)) := by
          rw [mul_assoc, he, mul_one]
      _ ≤ D * Real.exp (-(S / 2)) := h
  have hmain : n ≤ Real.exp (-(S / 2)) * D := by
    calc n ≤ M * Real.exp (dd * S) := hn
      _ ≤ D * Real.exp (-(S / 2)) := hstep
      _ = Real.exp (-(S / 2)) * D := by ring
  have hone : n / D ≤ Real.exp (-(S / 2)) := (div_le_iff₀ hD).mpr hmain
  calc n / D ≤ Real.exp (-(S / 2)) := hone
    _ = 1 * Real.exp (-(S / 2)) := (one_mul _).symm
    _ ≤ A * Real.exp (-(S / 2)) :=
        mul_le_mul_of_nonneg_right hA (le_of_lt (Real.exp_pos _))

/-- **The arithmetic of the freezing estimate.**  With `J = ⌊exp √(s+1)⌋`, the level scale
`c_s = 2^{s(d−χ)}` (`d = P.natDegree ≥ 2`, `0 < χ < 1/10`) and any fixed `A ≥ 1`, for all
sufficiently large `s`:

`1 ≤ s`, `3 ≤ J`, `mstThtL P J / c_s ≤ A e^{−√(s+1)/2}` and `(mstThtL P J)² / c_s² ≤ A e^{−√(s+1)/2}`.

Since `mstThtL P J = 2π (Σᵢ|cᵢ|) J^d ≤ 2π (Σᵢ|cᵢ|) e^{d√(s+1)}` and
`c_s = 2^{s(d−χ)} = e^{s(d−χ) log 2}`, the two quotients are
`≤ 2π(Σᵢ|cᵢ|) e^{(d+1/2)√(s+1) − s(d−χ)log 2}` and the square of that (times a constant), and
`√(s+1) = o(s)` makes both tend to `0` faster than `e^{−√(s+1)/2}`.  The proof only needs
`Real.sqrt_le_sqrt`, `Real.exp_le_exp`, `Real.rpow_def_of_pos`, `Nat.floor_le`,
`Nat.lt_floor_add_one` and elementary growth estimates (`∃ N, ∀ s ≥ N, B s ≤ C s`, `… ≤ e^{s}`). -/
theorem mst_freeze_arith (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) {χ : ℝ} (hχ0 : 0 < χ)
    (hχ1 : χ < 1 / 10) (A : ℝ) (hA : 1 ≤ A) :
    ∃ s₀ : ℕ, ∀ s : ℕ, s₀ ≤ s →
      1 ≤ s ∧
      3 ≤ ⌊Real.exp (Real.sqrt ((s : ℝ) + 1))⌋₊ ∧
      Work.BourgainPlan.Maximal.mstThtL P ⌊Real.exp (Real.sqrt ((s : ℝ) + 1))⌋₊
          / Work.BourgainPlan.Maximal.mstScale P.natDegree χ s
        ≤ A * Real.exp (-(Real.sqrt ((s : ℝ) + 1) / 2)) ∧
      (Work.BourgainPlan.Maximal.mstThtL P ⌊Real.exp (Real.sqrt ((s : ℝ) + 1))⌋₊) ^ 2
          / (Work.BourgainPlan.Maximal.mstScale P.natDegree χ s) ^ 2
        ≤ A * Real.exp (-(Real.sqrt ((s : ℝ) + 1) / 2)) := by
  have hd2 : (2 : ℝ) ≤ (P.natDegree : ℝ) := by exact_mod_cast hd
  have hdchi : (0 : ℝ) < (P.natDegree : ℝ) - χ := by linarith
  have ha1 : 0 < ((P.natDegree : ℝ) - χ) * Real.log 2 :=
    mul_pos hdchi (Real.log_pos (by norm_num))
  have hb1 : (0 : ℝ) ≤ (P.natDegree : ℝ) + 1 / 2 := by positivity
  have ha2 : 0 < 2 * (((P.natDegree : ℝ) - χ) * Real.log 2) := by linarith
  have hb2 : (0 : ℝ) ≤ 2 * (P.natDegree : ℝ) + 1 / 2 := by positivity
  have hcle : 2 * Real.pi * mstCoeffB P ≤ 2 * Real.pi * mstCoeffB P + 1 := by linarith
  have hMnn : (0 : ℝ) ≤ 2 * Real.pi * mstCoeffB P + 1 := by
    have := mstCoeffB_nonneg P
    have hp : (0 : ℝ) ≤ Real.pi := le_of_lt Real.pi_pos
    nlinarith [hcle, this, hp]
  have hM1 : ∀ᶠ s : ℕ in Filter.atTop,
      (2 * Real.pi * mstCoeffB P + 1)
        * Real.exp (((P.natDegree : ℝ) + 1 / 2) * Real.sqrt ((s : ℝ) + 1))
        ≤ Real.exp ((((P.natDegree : ℝ) - χ) * Real.log 2) * (s : ℝ)) :=
    eventually_const_mul_exp_sqrt_le_exp (((P.natDegree : ℝ) - χ) * Real.log 2)
      ((P.natDegree : ℝ) + 1 / 2) (2 * Real.pi * mstCoeffB P + 1) ha1 hb1
  have hM2 : ∀ᶠ s : ℕ in Filter.atTop,
      (2 * Real.pi * mstCoeffB P + 1) ^ 2
        * Real.exp ((2 * (P.natDegree : ℝ) + 1 / 2) * Real.sqrt ((s : ℝ) + 1))
        ≤ Real.exp ((2 * (((P.natDegree : ℝ) - χ) * Real.log 2)) * (s : ℝ)) :=
    eventually_const_mul_exp_sqrt_le_exp (2 * (((P.natDegree : ℝ) - χ) * Real.log 2))
      (2 * (P.natDegree : ℝ) + 1 / 2) ((2 * Real.pi * mstCoeffB P + 1) ^ 2) ha2 hb2
  have hq1 : ∀ᶠ s : ℕ in Filter.atTop,
      mstThtL P ⌊Real.exp (Real.sqrt ((s : ℝ) + 1))⌋₊ / mstScale P.natDegree χ s
        ≤ A * Real.exp (-(Real.sqrt ((s : ℝ) + 1) / 2)) := by
    filter_upwards [hM1] with s hbound
    have hD : 0 < mstScale P.natDegree χ s := by
      rw [mstScale_eq_exp']; exact Real.exp_pos _
    have hn : mstThtL P ⌊Real.exp (Real.sqrt ((s : ℝ) + 1))⌋₊
        ≤ (2 * Real.pi * mstCoeffB P + 1)
            * Real.exp ((P.natDegree : ℝ) * Real.sqrt ((s : ℝ) + 1)) :=
      mstThtL_le_of_max P s hcle hMnn
    have hb : (2 * Real.pi * mstCoeffB P + 1)
        * Real.exp (((P.natDegree : ℝ) + 1 / 2) * Real.sqrt ((s : ℝ) + 1))
        ≤ mstScale P.natDegree χ s := by
      rw [mstScale_eq_exp']; exact hbound
    exact div_le_mul_exp_of hA hD hn hb
  have hq2 : ∀ᶠ s : ℕ in Filter.atTop,
      (mstThtL P ⌊Real.exp (Real.sqrt ((s : ℝ) + 1))⌋₊) ^ 2
        / (mstScale P.natDegree χ s) ^ 2
        ≤ A * Real.exp (-(Real.sqrt ((s : ℝ) + 1) / 2)) := by
    filter_upwards [hM2] with s hbound
    have hD : 0 < mstScale P.natDegree χ s := by
      rw [mstScale_eq_exp']; exact Real.exp_pos _
    have hDsq : 0 < (mstScale P.natDegree χ s) ^ 2 := pow_pos hD 2
    have h1 := mstThtL_le_of_max P s hcle hMnn
    have h2 : (mstThtL P ⌊Real.exp (Real.sqrt ((s : ℝ) + 1))⌋₊) ^ 2
        ≤ ((2 * Real.pi * mstCoeffB P + 1)
            * Real.exp ((P.natDegree : ℝ) * Real.sqrt ((s : ℝ) + 1))) ^ 2 :=
      pow_le_pow_left₀ (mstThtL_nonneg P _) h1 2
    have hn : (mstThtL P ⌊Real.exp (Real.sqrt ((s : ℝ) + 1))⌋₊) ^ 2
        ≤ (2 * Real.pi * mstCoeffB P + 1) ^ 2
            * Real.exp ((2 * (P.natDegree : ℝ)) * Real.sqrt ((s : ℝ) + 1)) := by
      calc (mstThtL P ⌊Real.exp (Real.sqrt ((s : ℝ) + 1))⌋₊) ^ 2
          ≤ ((2 * Real.pi * mstCoeffB P + 1)
              * Real.exp ((P.natDegree : ℝ) * Real.sqrt ((s : ℝ) + 1))) ^ 2 := h2
        _ = (2 * Real.pi * mstCoeffB P + 1) ^ 2
              * Real.exp ((2 * (P.natDegree : ℝ)) * Real.sqrt ((s : ℝ) + 1)) := by
            have hexp : Real.exp ((P.natDegree : ℝ) * Real.sqrt ((s : ℝ) + 1)) ^ 2
                = Real.exp ((2 * (P.natDegree : ℝ)) * Real.sqrt ((s : ℝ) + 1)) := by
              rw [← Real.exp_nat_mul]; congr 1; ring
            rw [mul_pow, hexp]
    have hb : (2 * Real.pi * mstCoeffB P + 1) ^ 2
        * Real.exp ((2 * (P.natDegree : ℝ) + 1 / 2) * Real.sqrt ((s : ℝ) + 1))
        ≤ (mstScale P.natDegree χ s) ^ 2 := by
      rw [mstScale_sq_eq_exp']; exact hbound
    exact div_le_mul_exp_of hA hDsq hn hb
  have hev1 : ∀ᶠ s : ℕ in Filter.atTop, 1 ≤ s := Filter.eventually_ge_atTop 1
  have hev3 : ∀ᶠ s : ℕ in Filter.atTop,
      3 ≤ ⌊Real.exp (Real.sqrt ((s : ℝ) + 1))⌋₊ := by
    filter_upwards [Filter.eventually_ge_atTop 3] with s hs
    apply Nat.le_floor
    have hs4 : (4 : ℝ) ≤ (s : ℝ) + 1 := by
      have : (3 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs
      linarith
    have hsqrt2 : (2 : ℝ) ≤ Real.sqrt ((s : ℝ) + 1) := by
      refine (Real.le_sqrt (by norm_num : (0 : ℝ) ≤ 2) (by positivity)).mpr ?_
      nlinarith
    have h3 : (3 : ℝ) ≤ Real.exp 2 := by
      have h := Real.add_one_le_exp (2 : ℝ)
      linarith
    exact le_trans h3 (Real.exp_le_exp.mpr hsqrt2)
  have evall : ∀ᶠ s : ℕ in Filter.atTop,
      1 ≤ s ∧ (3 ≤ ⌊Real.exp (Real.sqrt ((s : ℝ) + 1))⌋₊ ∧
        ((mstThtL P ⌊Real.exp (Real.sqrt ((s : ℝ) + 1))⌋₊ / mstScale P.natDegree χ s
          ≤ A * Real.exp (-(Real.sqrt ((s : ℝ) + 1) / 2))) ∧
        ((mstThtL P ⌊Real.exp (Real.sqrt ((s : ℝ) + 1))⌋₊) ^ 2
            / (mstScale P.natDegree χ s) ^ 2
          ≤ A * Real.exp (-(Real.sqrt ((s : ℝ) + 1) / 2))))) :=
    hev1.and (hev3.and (hq1.and hq2))
  exact Filter.eventually_atTop.mp evall

end Work.BourgainPlan.Maximal
