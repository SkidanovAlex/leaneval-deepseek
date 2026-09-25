import Mathlib
import Submission.Work.RHContract.A.CaDeltaDefs
import Submission.Commons.NumberTheory.Primes.prime_gap_123
import Submission.Commons.Analysis.Real.log_one_add_inv_div_log_strictAntiOn
import Submission.Commons.Analysis.Real.log_one_add_inv_bounds

namespace Work.RHContract.A

open scoped BigOperators

/-- `caSum k y = y + y^2 + ... + y^k`. -/
noncomputable def caSum (k : ℕ) (y : ℝ) : ℝ := ∑ i ∈ Finset.range k, y ^ (i + 1)

/-- The CA exponent threshold function `F(y,k) = log(1 + 1/caSum k y)/log y`. -/
noncomputable def caFf (k : ℕ) (y : ℝ) : ℝ := Real.log (1 + 1 / caSum k y) / Real.log y

/-- `caG x = log(1 + 1/x)/log x`. -/
noncomputable def caG (x : ℝ) : ℝ := Real.log (1 + 1 / x) / Real.log x

lemma caFf_one (y : ℝ) : caFf 1 y = caG y := by
  simp [caFf, caG, caSum]

lemma caSum_ge_pow (k : ℕ) (hk : 1 ≤ k) {y : ℝ} (hy : 0 ≤ y) : y ^ k ≤ caSum k y := by
  unfold caSum
  have hkpos : 0 < k := hk
  have hmem : k - 1 ∈ Finset.range k := Finset.mem_range.mpr (by omega)
  have h := Finset.single_le_sum (f := fun i => y ^ (i + 1))
    (fun i _ => pow_nonneg hy _) hmem
  have hk1 : k - 1 + 1 = k := by omega
  simpa [hk1] using h

lemma caSum_pos (k : ℕ) (hk : 1 ≤ k) {y : ℝ} (hy : 0 < y) : 0 < caSum k y :=
  lt_of_lt_of_le (pow_pos hy k) (caSum_ge_pow k hk (le_of_lt hy))

/-- `log x ≤ x · log k` for `x ≥ 1` and `k ≥ 2`. -/
lemma log_le_mul_log (x : ℝ) (hx : 1 ≤ x) (k : ℕ) (hk : 2 ≤ k) :
    Real.log x ≤ x * Real.log k := by
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx
  set s : ℝ := Real.sqrt x with hs
  have hs2 : s ^ 2 = x := by rw [hs]; exact Real.sq_sqrt (le_of_lt hxpos)
  have hspos : 0 < s := Real.sqrt_pos.mpr hxpos
  have hlogx : Real.log x = 2 * Real.log s := by
    rw [hs, Real.log_sqrt (le_of_lt hxpos)]
    ring
  have hub : Real.log s ≤ s - 1 := Real.log_le_sub_one_of_pos hspos
  have hquad : 2 * (s - 1) ≤ (5 / 8) * s ^ 2 := by
    have : 0 ≤ (s - 8 / 5) ^ 2 := sq_nonneg _
    nlinarith [this]
  have hlogk : (5 / 8 : ℝ) ≤ Real.log k := by
    have h2 : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have hlog2 : (5 / 8 : ℝ) ≤ Real.log 2 := by
      linarith [Real.log_two_gt_d9]
    exact le_trans hlog2 (Real.log_le_log (by norm_num) h2)
  calc Real.log x = 2 * Real.log s := hlogx
    _ ≤ 2 * (s - 1) := by linarith
    _ ≤ (5 / 8) * s ^ 2 := hquad
    _ = (5 / 8) * x := by rw [hs2]
    _ ≤ x * Real.log k := by
        have : (0:ℝ) ≤ x := le_of_lt hxpos
        nlinarith [hlogk, this]

/-- `t ↦ t^k · log t` is strictly increasing on `[1,∞)`. -/
lemma pow_mul_log_strictMono (k : ℕ) (_hk : 1 ≤ k) {a b : ℝ} (ha : 1 ≤ a) (hab : a < b) :
    a ^ k * Real.log a < b ^ k * Real.log b := by
  have hb1 : 1 < b := lt_of_le_of_lt ha hab
  rcases eq_or_lt_of_le ha with h | h
  · rw [← h, Real.log_one, mul_zero]
    exact mul_pos (pow_pos (by linarith) k) (Real.log_pos hb1)
  · have hla : 0 < Real.log a := Real.log_pos h
    have hlab : Real.log a < Real.log b := Real.log_lt_log (by linarith) hab
    have hpowle : a ^ k ≤ b ^ k := pow_le_pow_left₀ (by linarith) (le_of_lt hab) k
    calc a ^ k * Real.log a ≤ b ^ k * Real.log a :=
          mul_le_mul_of_nonneg_right hpowle (le_of_lt hla)
      _ < b ^ k * Real.log b := mul_lt_mul_of_pos_left hlab (pow_pos (by linarith) k)

/-- `(p^{k+1}-1)/(p^{k+1}-p) = 1 + 1/caSum k p` for `p ≥ 2`, `k ≥ 1`. -/
lemma caRatio (p : ℕ) (hp : 2 ≤ p) (k : ℕ) (hk : 1 ≤ k) :
    (((p : ℝ) ^ (k + 1 : ℕ)) - 1) / (((p : ℝ) ^ (k + 1 : ℕ)) - (p : ℝ)) =
      1 + 1 / caSum k (p : ℝ) := by
  set y : ℝ := (p : ℝ) with hy
  have hy1 : 1 < y := by rw [hy]; exact_mod_cast (by omega : 1 < p)
  have hy0 : 0 < y := by linarith
  have hgeom : (∑ i ∈ Finset.range k, y ^ i) * (y - 1) = y ^ k - 1 := by
    rw [geom_sum_mul]
  have hS : caSum k y = y * (∑ i ∈ Finset.range k, y ^ i) := by
    unfold caSum
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [pow_succ']
  have hden : y ^ (k + 1 : ℕ) - y = (y - 1) * caSum k y := by
    rw [hS, pow_succ]
    have := hgeom
    nlinarith [this]
  have hnum : y ^ (k + 1 : ℕ) - 1 = (y - 1) * (caSum k y + 1) := by
    have : y ^ (k + 1 : ℕ) - 1 = (y ^ (k + 1 : ℕ) - y) + (y - 1) := by ring
    rw [this, hden]; ring
  have hyne : y - 1 ≠ 0 := by linarith
  have hSp : caSum k y ≠ 0 := ne_of_gt (caSum_pos k hk hy0)
  rw [hnum, hden]
  field_simp

/-- The bridge between `caMu` and `caFf`. -/
lemma caMu_ge_iff_caFf (p : ℕ) (hp : 2 ≤ p) (ε : ℝ) (hε : 0 < ε) (k : ℕ) (hk : 1 ≤ k) :
    (k : ℝ) ≤ Work.RHPlan.caMu p ε ↔ ε ≤ caFf k (p : ℝ) := by
  have h := Commons.NumberTheory.Robin.caMu_ge_iff_caF p ε k hp hε hk
  have hratio := caRatio p hp k hk
  have h2 : Real.log (((p : ℝ) ^ (k + 1 : ℕ) - 1) / ((p : ℝ) ^ (k + 1 : ℕ) - (p : ℝ)))
      / Real.log (p : ℝ) = caFf k (p : ℝ) := by
    unfold caFf
    rw [hratio]
  rw [h2] at h
  have h3 : Work.RHPlan.caMu p ε
      = Real.log (((p : ℝ) ^ (1 + ε) - 1) / ((p : ℝ) ^ (1 + ε) - (p : ℝ))) / Real.log (p : ℝ) := rfl
  rw [h3]
  exact h

/-- **Comparison lemma.** If `caG x ≤ caFf k y` with `x, y > 1` and `k ≥ 2`, then `y^k ≤ k x`. -/
lemma caG_le_caFf_imp (x y : ℝ) (hx : 1 < x) (hy : 1 < y) (k : ℕ) (hk : 2 ≤ k)
    (h : caG x ≤ caFf k y) : y ^ k ≤ (k : ℝ) * x := by
  have hxpos : 0 < x := by linarith
  have hypos : 0 < y := by linarith
  have hylog : 0 < Real.log y := Real.log_pos hy
  have hxlog : 0 < Real.log x := Real.log_pos hx
  have hk1 : 1 ≤ k := by omega
  have hSpos : 0 < caSum k y := caSum_pos k hk1 hypos
  -- upper bound on `caFf k y`
  have hub : caFf k y ≤ 1 / (caSum k y * Real.log y) := by
    unfold caFf
    have hlog : Real.log (1 + 1 / caSum k y) ≤ 1 / caSum k y := by
      have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 1 + 1 / caSum k y by positivity)
      linarith
    calc Real.log (1 + 1 / caSum k y) / Real.log y ≤ (1 / caSum k y) / Real.log y :=
          div_le_div_of_nonneg_right hlog (le_of_lt hylog)
      _ = 1 / (caSum k y * Real.log y) := by field_simp
  -- lower bound on `caG x`
  have hlb : 1 / ((x + 1) * Real.log x) ≤ caG x := by
    have hlog : 1 / (x + 1) ≤ Real.log (1 + 1 / x) :=
      le_of_lt (Commons.Analysis.Real.log_one_add_inv_bounds hxpos).1
    unfold caG
    calc 1 / ((x + 1) * Real.log x) = (1 / (x + 1)) / Real.log x := by field_simp
      _ ≤ Real.log (1 + 1 / x) / Real.log x := div_le_div_of_nonneg_right hlog (le_of_lt hxlog)
  -- combine
  have hSlog : caSum k y * Real.log y ≤ (x + 1) * Real.log x := by
    have hpos1 : 0 < (x + 1) * Real.log x := by positivity
    have hpos2 : 0 < caSum k y * Real.log y := mul_pos hSpos hylog
    have h3 : 1 / ((x + 1) * Real.log x) ≤ 1 / (caSum k y * Real.log y) :=
      le_trans hlb (le_trans h hub)
    have h3'' : ((x + 1) * Real.log x)⁻¹ ≤ (caSum k y * Real.log y)⁻¹ := by
      simpa [one_div] using h3
    exact (inv_le_inv₀ hpos1 hpos2).mp h3''
  have hyklog : y ^ k * Real.log y ≤ (x + 1) * Real.log x :=
    le_trans (mul_le_mul_of_nonneg_right (caSum_ge_pow k hk1 (le_of_lt hypos)) (le_of_lt hylog)) hSlog
  -- compare with the reference point `y0 = (k x)^{1/k}`
  set y0 : ℝ := ((k : ℝ) * x) ^ (1 / (k : ℝ)) with hy0
  have hkpos : (0:ℝ) < k := by positivity
  have hkxpos : 0 < (k : ℝ) * x := by positivity
  have hy0pow : y0 ^ k = (k : ℝ) * x := by
    rw [hy0, ← Real.rpow_natCast (((k:ℝ)*x) ^ (1/(k:ℝ))) k,
      ← Real.rpow_mul (le_of_lt hkxpos) (1/(k:ℝ)) (k:ℝ)]
    have h1 : (1/(k : ℝ)) * (k : ℝ) = 1 := by field_simp
    rw [h1, Real.rpow_one]
  have hy01 : 1 ≤ y0 := by
    rw [hy0]
    refine Real.one_le_rpow ?_ (by positivity)
    have hk2r : (2:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
    nlinarith [hk2r, hx]
  have hlogy0 : Real.log y0 = (1 / (k : ℝ)) * Real.log ((k:ℝ) * x) := by
    rw [hy0, Real.log_rpow hkxpos]
  have hkey : (x + 1) * Real.log x ≤ y0 ^ k * Real.log y0 := by
    rw [hy0pow, hlogy0]
    have hlogkx : Real.log ((k:ℝ) * x) = Real.log (k:ℝ) + Real.log x :=
      Real.log_mul (by positivity) (ne_of_gt hxpos)
    rw [hlogkx]
    have hxk : Real.log x ≤ x * Real.log (k:ℝ) :=
      log_le_mul_log x (le_of_lt hx) k hk
    have hkne : (k:ℝ) ≠ 0 := ne_of_gt hkpos
    field_simp
    nlinarith [hxk]
  have hy_le : y ≤ y0 := by
    by_contra hcon
    push Not at hcon
    have hmono := pow_mul_log_strictMono k hk1 hy01 hcon
    rw [hy0pow] at hmono
    rw [hy0pow] at hkey
    linarith [hmono, hyklog, hkey]
  calc y ^ k ≤ y0 ^ k := pow_le_pow_left₀ (le_of_lt hypos) hy_le k
    _ = (k : ℝ) * x := hy0pow

theorem caLevel_le (ε : ℝ) (hε : 0 < ε) (hξ : 1530 ≤ (Work.RHPlan.caXi ε : ℝ)) (k : ℕ) (hk : 2 ≤ k) :
    (Work.RHContract.A.caLevel ε k : ℝ)
      ≤ (1.23 * (k : ℝ) * (Work.RHPlan.caXi ε : ℝ)) ^ (1 / (k : ℝ)) := by
  set ξ : ℝ := (Work.RHPlan.caXi ε : ℝ) with hξdef
  have hξ1530 : 1530 ≤ ξ := by rw [hξdef]; exact hξ
  have hξ1 : 1 < ξ := by linarith
  have hξpos : 0 < ξ := by linarith
  set T : Finset ℕ := ((Finset.range (Work.RHContract.A.caK ε)).filter Nat.Prime).filter
      (fun p : ℕ => k ≤ ⌊Work.RHPlan.caMu p ε⌋₊) with hTdef
  have hcaLevel : Work.RHContract.A.caLevel ε k = T.sup id := by
    rw [hTdef]; rfl
  by_cases hTne : T.Nonempty
  · have hmax : T.sup id = T.max' hTne := by
      rw [Finset.max'_eq_sup', Finset.sup'_eq_sup hTne]
    have hPmem : Work.RHContract.A.caLevel ε k ∈ T := by
      rw [hcaLevel, hmax]
      exact Finset.max'_mem T hTne
    have hPint : Work.RHContract.A.caLevel ε k
        ∈ (Finset.range (Work.RHContract.A.caK ε)).filter Nat.Prime :=
      (Finset.mem_filter.mp hPmem).1
    have hPcond : k ≤ ⌊Work.RHPlan.caMu (Work.RHContract.A.caLevel ε k) ε⌋₊ :=
      (Finset.mem_filter.mp hPmem).2
    have hPprime : Nat.Prime (Work.RHContract.A.caLevel ε k) := (Finset.mem_filter.mp hPint).2
    have hPltK : Work.RHContract.A.caLevel ε k < Work.RHContract.A.caK ε :=
      Finset.mem_range.mp (Finset.mem_filter.mp hPint).1
    have hP2 : 2 ≤ Work.RHContract.A.caLevel ε k := hPprime.two_le
    have hPgt1 : 1 < ((Work.RHContract.A.caLevel ε k : ℕ) : ℝ) := by
      exact_mod_cast (show 1 < Work.RHContract.A.caLevel ε k by omega)
    have hPpos : 0 < ((Work.RHContract.A.caLevel ε k : ℕ) : ℝ) := by positivity
    -- `P` lies in the support, hence `P ≤ ξ(ε)`
    have hPmemSupp : Work.RHContract.A.caLevel ε k ∈ Work.RHPlan.caSupport ε := by
      rw [Work.RHPlan.caSupport]
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hPltK, hPprime⟩,
          le_trans (by omega : 1 ≤ k) hPcond⟩
    have hPleXi : Work.RHContract.A.caLevel ε k ≤ Work.RHPlan.caXi ε := by
      have h := Finset.le_sup (f := id) hPmemSupp
      simpa [Work.RHPlan.caXi] using h
    -- `ε ≤ caFf k P`
    have hmuPos : 0 < Work.RHPlan.caMu (Work.RHContract.A.caLevel ε k) ε :=
      Commons.NumberTheory.Robin.caMu_pos hP2 hε
    have hk_le_mu : (k : ℝ) ≤ Work.RHPlan.caMu (Work.RHContract.A.caLevel ε k) ε :=
      le_trans (by exact_mod_cast hPcond) (Nat.floor_le (le_of_lt hmuPos))
    have hεFfP : ε ≤ caFf k ((Work.RHContract.A.caLevel ε k : ℕ) : ℝ) :=
      (caMu_ge_iff_caFf (Work.RHContract.A.caLevel ε k) hP2 ε hε k (by omega)).mp hk_le_mu
    -- a prime just above `ξ`, still `≤ 1.23 ξ`
    obtain ⟨q, hqprime, hξltq, hqle⟩ := Commons.NumberTheory.Primes.prime_gap_123 ξ hξ1530
    have hq2 : 2 ≤ q := hqprime.two_le
    have hq1 : 1 < (q : ℝ) := by exact_mod_cast (by omega : 1 < q)
    have hqpos : 0 < (q : ℝ) := by linarith
    -- that prime has exponent `< 1`, i.e. `caG q < ε`
    have hqG : caG (q : ℝ) < ε := by
      by_contra hcon
      push Not at hcon
      have hmu1 := (caMu_ge_iff_caFf q hq2 ε hε 1 le_rfl).mpr (by rwa [caFf_one])
      have hqfloor : 1 ≤ ⌊Work.RHPlan.caMu q ε⌋₊ := Nat.le_floor hmu1
      rcases lt_or_ge q (Work.RHContract.A.caK ε) with hqK | hqK
      · have hqmem : q ∈ Work.RHPlan.caSupport ε := by
          rw [Work.RHPlan.caSupport]
          exact Finset.mem_filter.mpr
            ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hqK, hqprime⟩, hqfloor⟩
        have hle : q ≤ Work.RHPlan.caXi ε := Finset.le_sup (f := id) hqmem
        have hcast : (q : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ) := by exact_mod_cast hle
        have hlt : (Work.RHPlan.caXi ε : ℝ) < (q : ℝ) := by rw [← hξdef]; exact hξltq
        exact absurd hcast (not_le.mpr hlt)
      · have hqexp : Real.exp (2 / ε) < (q : ℝ) := by
          have h2 : (Work.RHContract.A.caK ε : ℝ) ≤ (q : ℝ) := by exact_mod_cast hqK
          rw [Work.RHContract.A.caK] at h2
          push_cast at h2
          have hc := Nat.le_ceil (Real.exp (2 / ε))
          linarith
        have hlogq : 2 / ε < Real.log (q : ℝ) := by
          have := Real.log_lt_log (Real.exp_pos (2 / ε)) hqexp
          rwa [Real.log_exp] at this
        have hbound : caG (q : ℝ) ≤ 1 / ((q : ℝ) * Real.log (q : ℝ)) := by
          unfold caG
          have hlog1 : Real.log (1 + 1 / (q : ℝ)) ≤ 1 / (q : ℝ) := by
            have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 1 + 1 / (q : ℝ) by positivity)
            linarith
          have hlogqpos : 0 < Real.log (q : ℝ) := by
            have : (0:ℝ) < 2 / ε := by positivity
            linarith
          calc Real.log (1 + 1 / (q : ℝ)) / Real.log (q : ℝ)
              ≤ (1 / (q : ℝ)) / Real.log (q : ℝ) :=
                div_le_div_of_nonneg_right hlog1 (le_of_lt hlogqpos)
            _ = 1 / ((q : ℝ) * Real.log (q : ℝ)) := by field_simp
        have hlt : 1 / ((q : ℝ) * Real.log (q : ℝ)) < ε := by
          have hq2r : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq2
          have hpos : 0 < (q : ℝ) * Real.log (q : ℝ) := by
            have hh : 0 < Real.log (q : ℝ) := by
              have h2e : (0:ℝ) < 2 / ε := by positivity
              linarith
            exact mul_pos hqpos hh
          rw [div_lt_iff₀ hpos]
          have h2e : (2 : ℝ) < Real.log (q : ℝ) * ε := (div_lt_iff₀ hε).mp hlogq
          have h1 : (q : ℝ) * 2 < (q : ℝ) * (Real.log (q : ℝ) * ε) :=
            mul_lt_mul_of_pos_left h2e hqpos
          nlinarith [h1, hq2r]
        linarith [hcon, hbound, hlt]
    have hGbig : caG (1.23 * ξ) ≤ caG (q : ℝ) := by
      have h1 : (1.23 : ℝ) * ξ ∈ Set.Ioi (1 : ℝ) := by
        simp only [Set.mem_Ioi]; nlinarith [hξ1]
      have h2 : (q : ℝ) ∈ Set.Ioi (1 : ℝ) := by
        simp only [Set.mem_Ioi]; exact hq1
      have hqx1 : (q : ℝ) ≤ 1.23 * ξ := by
        have hd : (1.23 : ℝ) = 123 / 100 := by norm_num
        rw [hd]; exact hqle
      have hanti := Commons.Analysis.Real.log_one_add_inv_div_log_strictAntiOn
      have := (hanti.le_iff_ge h1 h2).mpr hqx1
      simpa [caG] using this
    have hG1 : caG (1.23 * ξ) < ε := lt_of_le_of_lt hGbig hqG
    have hcmp : ((Work.RHContract.A.caLevel ε k : ℕ) : ℝ) ^ k ≤ (k : ℝ) * (1.23 * ξ) := by
      have hx1 : 1 < 1.23 * ξ := by nlinarith [hξ1]
      refine caG_le_caFf_imp (1.23 * ξ) ((Work.RHContract.A.caLevel ε k : ℕ) : ℝ)
        hx1 hPgt1 k hk ?_
      exact le_of_lt (lt_of_lt_of_le hG1 hεFfP)
    have heq : (((Work.RHContract.A.caLevel ε k : ℕ) : ℝ) ^ k) ^ (1 / (k : ℝ))
        = ((Work.RHContract.A.caLevel ε k : ℕ) : ℝ) := by
      rw [← Real.rpow_natCast (((Work.RHContract.A.caLevel ε k : ℕ) : ℝ)) k,
        ← Real.rpow_mul (le_of_lt hPpos) (k : ℝ) (1 / (k : ℝ))]
      have h1 : (k : ℝ) * (1 / (k : ℝ)) = 1 := by field_simp
      rw [h1, Real.rpow_one]
    have h1 : (((Work.RHContract.A.caLevel ε k : ℕ) : ℝ) ^ k) ^ (1 / (k : ℝ))
        ≤ (1.23 * (k : ℝ) * ξ) ^ (1 / (k : ℝ)) := by
      refine Real.rpow_le_rpow (by positivity) ?_ (by positivity)
      nlinarith [hcmp]
    rw [heq] at h1
    rwa [hξdef] at h1
  · have hTempty : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hTne
    have hzero : Work.RHContract.A.caLevel ε k = 0 := by
      rw [hcaLevel, hTempty, Finset.sup_empty]
      rfl
    rw [hzero]
    push_cast
    exact Real.rpow_nonneg (by positivity) _

end Work.RHContract.A
