import Mathlib
import Submission.Work.FITop4.Defs4
import Submission.Work.FITop4.Red5.Vocab
import Submission.Work.FITop4.Numeric4.log_dominance

namespace Work.FITop4.Red5

open Filter

set_option maxHeartbeats 4000000

/-- `D ≤ log x` eventually (for arbitrary, possibly negative, `D`). -/
private lemma eventually_le_log (D : ℝ) :
    ∃ x₀ : ℕ, ∀ x : ℕ, x₀ ≤ x → D ≤ Real.log (x : ℝ) := by
  rcases le_or_gt 0 D with h | h
  · exact Work.FITop4.Numeric4.log_dominance.2.2.2.1 D h
  · obtain ⟨x₀, hx₀⟩ := Work.FITop4.Numeric4.log_dominance.2.2.2.1 0 le_rfl
    exact ⟨x₀, fun x hx => le_trans (le_of_lt h) (hx₀ x hx)⟩

/-- `Y ≤ x^e` eventually, for `Y ≥ 0` and `e > 0` (this is `x^e → ∞`). -/
private lemma eventually_rpow_ge (Y e : ℝ) (hY : 0 ≤ Y) (he : 0 < e) :
    ∃ x₀ : ℕ, ∀ x : ℕ, x₀ ≤ x → Y ≤ (x : ℝ) ^ e := by
  obtain ⟨N, hN⟩ := exists_nat_ge (Y ^ e⁻¹)
  refine ⟨max N 1, fun x hx => ?_⟩
  have hxN : N ≤ x := le_trans (le_max_left _ _) hx
  have hNx : Y ^ e⁻¹ ≤ (x:ℝ) := le_trans hN (by exact_mod_cast hxN)
  calc Y = Y ^ (1:ℝ) := (Real.rpow_one Y).symm
    _ = Y ^ (e⁻¹ * e) := by rw [inv_mul_cancel₀ (ne_of_gt he)]
    _ = (Y ^ e⁻¹) ^ e := Real.rpow_mul hY e⁻¹ e
    _ ≤ (x:ℝ) ^ e := Real.rpow_le_rpow (Real.rpow_nonneg hY _) hNx (le_of_lt he)

/-- **The numerical side conditions of `PieceFacts` at the round-5 exponent `A = Asave`.**  This
is the round-4 `Numeric4.pieceFacts_proof` run at `A = Asave`, `σ = sigmaChoice Asave`
(`= 2A + 4A' + 9`), the saving exponent at which the round-5 reduction works.  The only place
where the frozen `Astar` still enters is the first conjunct of `PieceFacts`, whose exponent
`2Astar + 4Aprime Astar` is fixed: there the argument at `sigmaChoice Astar = 2Astar + 4Aprime Astar + 9`
is lifted to `sigmaChoice Asave ≥ sigmaChoice Astar` by monotonicity of `ℓ^·` (`ℓ ≥ 2`). -/
theorem pieceFacts_proof_save (η : ℝ) (hη0 : 0 < η) (hη1 : η < 3 / 32) (δ : ℝ) (hδ : 0 < δ) :
    ∃ x₀ : ℕ, ∀ (x : ℕ) (N : ℝ) (Pa : Work.FITop.Params), x₀ ≤ x →
      Pa.x = x → Pa.η = η → Pa.A = Asave → Pa.A' = Aprime Asave →
      Pa.θ = thetaOf x Asave → Pa.ϑ = varthetaOf x Asave → Pa.τ = tauOf x Asave →
      N ≤ (Pa.N : ℝ) → (Pa.N : ℝ) ≤ 2 * N →
      N < 2 * ((x : ℝ) ^ ((1 : ℝ) / 2) * (Real.log (x : ℝ)) ^ (-(BmaxBig η))) →
      PieceFacts η δ (sigmaChoice Asave) x Pa := by
  classical
  set σ : ℝ := sigmaChoice Asave with hσdef
  have hσeq : σ = 2 * Asave + 4 * Aprime Asave + 9 := by rw [hσdef]; rfl
  have hA1 : (1:ℝ) ≤ Asave := by norm_num [Asave]
  have hA'1 : (1:ℝ) ≤ Aprime Asave := by
    unfold Aprime
    have : (0:ℝ) ≤ (2:ℝ)^(20:ℕ) := by positivity
    linarith
  have h3σ3 : 0 ≤ 3*σ + 3 := by rw [hσeq]; nlinarith [hA1, hA'1]
  have hσ0 : 0 ≤ σ := by rw [hσeq]; nlinarith [hA1, hA'1]
  have hc : (0:ℝ) < 1/4 + η := by linarith
  -- the smaller exponent `σs = sigmaChoice Astar`, at which conjunct 1 is proved naturally
  set σs : ℝ := sigmaChoice Astar with hσsdef
  have hσseq : σs = 2*Astar + 4*Aprime Astar + 9 := by rw [hσsdef]; rfl
  have hσs9 : 2 * Astar + 4 * Aprime Astar = σs - 9 := by rw [hσseq]; ring
  have hσs0 : 0 ≤ σs := by rw [hσseq]; unfold Astar Aprime; norm_num
  have hσs_le : σs ≤ σ := by
    rw [hσsdef, hσdef]; unfold sigmaChoice Asave Astar Aprime; norm_num
  have hb1 : ∀ᶠ x : ℕ in Filter.atTop, (1:ℝ) ≤ Real.log (x:ℝ) :=
    Filter.eventually_atTop.mpr (eventually_le_log 1)
  have hb2 : ∀ᶠ x : ℕ in Filter.atTop, 16 * (1/4+η) ^ (-σs) ≤ Real.log (x:ℝ) :=
    Filter.eventually_atTop.mpr (eventually_le_log _)
  have hb3 : ∀ᶠ x : ℕ in Filter.atTop, 2/(1/4+η) ≤ Real.log (x:ℝ) :=
    Filter.eventually_atTop.mpr (eventually_le_log _)
  have hb4 : ∀ᶠ x : ℕ in Filter.atTop, (Real.log (x:ℝ)) ^ (3*σ+3) ≤ (x:ℝ) ^ ((1/4+η)/18) :=
    Filter.eventually_atTop.mpr (Work.FITop4.Numeric4.log_dominance.1 (3*σ+3) ((1/4+η)/18) h3σ3 (by positivity))
  have hb5 : ∀ᶠ x : ℕ in Filter.atTop, 2 ≤ (x:ℝ) ^ ((1/4+η)/18) :=
    Filter.eventually_atTop.mpr (eventually_rpow_ge 2 ((1/4+η)/18) (by norm_num) (by positivity))
  have hb6 : ∀ᶠ x : ℕ in Filter.atTop, (Real.log (x:ℝ)) ^ (3*σ+3) ≤ (x:ℝ) ^ ((1/4+η)*δ/2) :=
    Filter.eventually_atTop.mpr (Work.FITop4.Numeric4.log_dominance.1 (3*σ+3) ((1/4+η)*δ/2) h3σ3 (by positivity))
  have hb7 : ∀ᶠ x : ℕ in Filter.atTop, 3 ≤ (x:ℝ) ^ ((1/4+η)*δ/2) :=
    Filter.eventually_atTop.mpr (eventually_rpow_ge 3 ((1/4+η)*δ/2) (by norm_num) (by positivity))
  have hb8 : ∀ᶠ x : ℕ in Filter.atTop, 16 ≤ (x:ℝ) ^ (1/4+η) :=
    Filter.eventually_atTop.mpr (eventually_rpow_ge 16 (1/4+η) (by norm_num) hc)
  have hall := hb1.and (hb2.and (hb3.and (hb4.and (hb5.and (hb6.and (hb7.and hb8))))))
  rw [Filter.eventually_atTop] at hall
  obtain ⟨x₀, hx₀⟩ := hall
  refine ⟨x₀, ?_⟩
  intro x N Pa hx0 hPx hPη hPA hPA' hPθ hPϑ hPτ hNle hN2 hNb
  obtain ⟨hL1, hL2, hL3, hL4, hL5, hL6, hL7, hL8⟩ := hx₀ x hx0
  have hx1 : (1:ℝ) < (x:ℝ) := by
    have : 1 < x := by rw [← hPx]; exact lt_of_lt_of_le (by norm_num) Pa.hx
    exact_mod_cast this
  have hxpos : (0:ℝ) < (x:ℝ) := by linarith
  set L : ℝ := Real.log (x:ℝ) with hLdef
  set ℓ : ℝ := Real.log Pa.N with hℓdef
  have hLpos : 0 < L := by rw [hLdef]; exact Real.log_pos hx1
  have hL0 : 0 ≤ L := le_of_lt hLpos
  have hNlo : (x:ℝ)^((1:ℝ)/4 + η) < Pa.N := by
    have h := Pa.hNlo; rw [hPx, hPη] at h; exact h
  have hMNx : Pa.M * Pa.N ≤ (x:ℝ) := by have h := Pa.hMNx; rw [hPx] at h; exact h
  have hMge : Pa.N ≤ Pa.M := Pa.hMge
  have hPaN1 : (1:ℝ) ≤ Pa.N := Pa.hN1
  have hPaM1 : (1:ℝ) ≤ Pa.M := Pa.hM1
  have hPaNpos : 0 < Pa.N := lt_of_lt_of_le one_pos hPaN1
  have hPaMpos : 0 < Pa.M := lt_of_lt_of_le one_pos hPaM1
  have hMNpos : 0 < Pa.M * Pa.N := mul_pos hPaMpos hPaNpos
  have hMN1 : (1:ℝ) ≤ Pa.M * Pa.N := by nlinarith [hPaM1, hPaN1]
  have hPaNle_x : Pa.N ≤ (x:ℝ) := by
    have h : (1:ℝ) * Pa.N ≤ Pa.M * Pa.N := mul_le_mul_of_nonneg_right hPaM1 (le_of_lt hPaNpos)
    linarith [h, hMNx]
  have hPaNgt1 : 1 < Pa.N := lt_trans (Real.one_lt_rpow hx1 hc) hNlo
  have hlogNpos : 0 < Real.log Pa.N := Real.log_pos hPaNgt1
  have hℓpos : 0 < ℓ := by rw [hℓdef]; exact hlogNpos
  have hℓ0 : 0 ≤ ℓ := le_of_lt hℓpos
  have hℓ_gt : (1/4+η) * L < ℓ := by
    have h := Real.log_lt_log (Real.rpow_pos_of_pos hxpos ((1:ℝ)/4+η)) hNlo
    rw [Real.log_rpow hxpos ((1:ℝ)/4+η), ← hLdef, ← hℓdef] at h
    exact h
  have hℓ_le_L : ℓ ≤ L := by
    rw [hℓdef, hLdef]
    exact Real.log_le_log hPaNpos hPaNle_x
  have hℓ_ge2 : 2 ≤ ℓ := by
    have h := mul_le_mul_of_nonneg_right hL3 (le_of_lt hc)
    rw [div_mul_cancel₀ 2 (ne_of_gt hc)] at h
    have hcomm : (1/4+η)*L = L*(1/4+η) := by ring
    linarith [h, hℓ_gt, hcomm]
  have hceil : (Xcut Pa σ : ℝ) ≤ ℓ^(3*σ+3) + 1 := by
    have h := Nat.ceil_lt_add_one (le_of_lt (Real.rpow_pos_of_pos hlogNpos (3*σ+3)))
    unfold Xcut
    rw [hℓdef]
    exact le_of_lt h
  -- Conjunct 1, proved at the smaller exponent `σs`, then lifted to `σ`
  have hitem1_0 : 16 * (Real.log (Pa.M * Pa.N)) ^ (8:ℕ) * L ^ (σs - 9) ≤ ℓ ^ σs := by
    have hlogMN_le : Real.log (Pa.M*Pa.N) ≤ L := by
      rw [hLdef]; exact Real.log_le_log hMNpos hMNx
    have hlogMN_ge : 0 ≤ Real.log (Pa.M*Pa.N) := Real.log_nonneg hMN1
    have hL8 : (Real.log (Pa.M*Pa.N))^(8:ℕ) ≤ L^(8:ℕ) :=
      pow_le_pow_left₀ hlogMN_ge hlogMN_le 8
    have hLnn9 : 0 ≤ L^(σs-9) := Real.rpow_nonneg hL0 _
    have hstep1 : 16 * (Real.log (Pa.M*Pa.N))^(8:ℕ) * L^(σs-9) ≤ 16 * L^8 * L^(σs-9) := by
      have hh : (Real.log (Pa.M*Pa.N))^(8:ℕ) * L^(σs-9) ≤ L^8 * L^(σs-9) :=
        mul_le_mul_of_nonneg_right hL8 hLnn9
      calc 16 * (Real.log (Pa.M*Pa.N))^(8:ℕ) * L^(σs-9)
          = 16 * ((Real.log (Pa.M*Pa.N))^(8:ℕ) * L^(σs-9)) := by ring
        _ ≤ 16 * (L^8 * L^(σs-9)) := mul_le_mul_of_nonneg_left hh (by norm_num)
        _ = 16 * L^8 * L^(σs-9) := by ring
    have hL8r : L^8 = L^(8:ℝ) := (Real.rpow_natCast L 8).symm
    have hcomp : 16 * L^8 * L^(σs-9) = 16 * L^(σs-1) := by
      rw [hL8r, mul_assoc, ← Real.rpow_add hLpos 8 (σs-9),
          show 8 + (σs - 9) = σs - 1 by ring]
    have h16 : 16 ≤ (1/4+η)^σs * L := by
      have hab : (1/4+η)^σs * (1/4+η)^(-σs) = 1 := by
        rw [← Real.rpow_add hc, add_neg_cancel, Real.rpow_zero]
      have hkey : (1/4+η)^σs * (16 * (1/4+η)^(-σs)) = 16 := by
        calc (1/4+η)^σs * (16*(1/4+η)^(-σs))
            = 16 * ((1/4+η)^σs * (1/4+η)^(-σs)) := by ring
          _ = 16 * 1 := by rw [hab]
          _ = 16 := by ring
      have hg := mul_le_mul_of_nonneg_left hL2 (Real.rpow_nonneg hc.le σs)
      linarith [hkey, hg]
    have hLsm1 : 0 ≤ L^(σs-1) := Real.rpow_nonneg hL0 _
    have heq1 : L * L^(σs-1) = L^σs := by
      have h21 : L^(1:ℝ) * L^(σs-1) = L^σs := by
        rw [← Real.rpow_add hLpos 1 (σs-1), show 1 + (σs - 1) = σs by ring]
      rwa [Real.rpow_one] at h21
    have heq : ((1/4+η)^σs * L) * L^(σs-1) = (1/4+η)^σs * L^σs := by
      rw [mul_assoc, heq1]
    have hstep2 : 16 * L^(σs-1) ≤ ((1/4+η)*L)^σs := by
      rw [Real.mul_rpow hc.le hL0]
      calc 16 * L^(σs-1) ≤ ((1/4+η)^σs * L) * L^(σs-1) := mul_le_mul_of_nonneg_right h16 hLsm1
        _ = (1/4+η)^σs * L^σs := heq
    have hstep3 : ((1/4+η)*L)^σs ≤ ℓ^σs :=
      Real.rpow_le_rpow (mul_nonneg hc.le hL0) (le_of_lt hℓ_gt) hσs0
    calc 16 * (Real.log (Pa.M * Pa.N)) ^ (8:ℕ) * L ^ (σs - 9)
        ≤ 16 * L^8 * L^(σs-9) := hstep1
      _ = 16 * L^(σs-1) := hcomp
      _ ≤ ((1/4+η)*L)^σs := hstep2
      _ ≤ ℓ^σs := hstep3
  have hitem1 : 16 * (Real.log (Pa.M * Pa.N)) ^ (8:ℕ) * L ^ (σs - 9) ≤ ℓ ^ σ :=
    le_trans hitem1_0
      (Real.rpow_le_rpow_of_exponent_le (by linarith [hℓ_ge2] : (1:ℝ) ≤ ℓ) hσs_le)
  -- Conjunct 2, 3
  have hitem2 : 1 ≤ Xcut Pa σ := by
    unfold Xcut
    exact Nat.ceil_pos.mpr (Real.rpow_pos_of_pos hℓpos (3*σ+3))
  have hitem3 : (Xcut Pa σ : ℝ) ≤ Pa.N ^ ((1:ℝ)/9) := by
    have hℓpow : ℓ^(3*σ+3) ≤ (x:ℝ)^((1/4+η)/18) :=
      le_trans (Real.rpow_le_rpow hℓ0 hℓ_le_L h3σ3) hL4
    have h1le : 1 ≤ (x:ℝ)^((1/4+η)/18) := le_trans (by norm_num) hL5
    have hsq : 2 * (x:ℝ)^((1/4+η)/18) ≤ ((x:ℝ)^((1/4+η)/18))^2 := by
      have hy0 : 0 ≤ (x:ℝ)^((1/4+η)/18) := Real.rpow_nonneg hxpos.le _
      nlinarith [hL5, hy0]
    have hxpow9 : ((x:ℝ)^((1/4+η)/18))^2 = (x:ℝ)^((1/4+η)/9) := by
      rw [pow_two, ← Real.rpow_add hxpos,
          show (1/4+η)/18 + (1/4+η)/18 = (1/4+η)/9 by ring]
    have hxpow9_lt : (x:ℝ)^((1/4+η)/9) < Pa.N^((1:ℝ)/9) := by
      have h := Real.rpow_lt_rpow (Real.rpow_nonneg hxpos.le (1/4+η)) hNlo (by norm_num : (0:ℝ) < 1/9)
      rw [← Real.rpow_mul hxpos.le (1/4+η) (1/9)] at h
      rw [show (1/4+η)*(1/9) = (1/4+η)/9 by ring] at h
      exact h
    exact le_of_lt (calc (Xcut Pa σ : ℝ) ≤ ℓ^(3*σ+3) + 1 := hceil
      _ ≤ (x:ℝ)^((1/4+η)/18) + 1 := by linarith
      _ ≤ 2 * (x:ℝ)^((1/4+η)/18) := by linarith
      _ ≤ ((x:ℝ)^((1/4+η)/18))^2 := hsq
      _ = (x:ℝ)^((1/4+η)/9) := hxpow9
      _ < Pa.N^((1:ℝ)/9) := hxpow9_lt)
  -- Conjunct 4
  have hitem4 : (Xcut Pa σ : ℝ) ≤ ℓ^(3*σ+4) := by
    have hpow : ℓ^(3*σ+4) = ℓ^(3*σ+3) * ℓ := by
      rw [show 3*σ+4 = (3*σ+3)+1 by ring, Real.rpow_add hℓpos, Real.rpow_one]
    calc (Xcut Pa σ : ℝ) ≤ ℓ^(3*σ+3) + 1 := hceil
      _ ≤ 2 * ℓ^(3*σ+3) := by
          have hp : 1 ≤ ℓ^(3*σ+3) := Real.one_le_rpow (by linarith [hℓ_ge2] : (1:ℝ) ≤ ℓ) h3σ3
          linarith
      _ ≤ ℓ^(3*σ+3) * ℓ := by
          have hh := mul_le_mul_of_nonneg_left hℓ_ge2 (Real.rpow_nonneg hℓ0 (3*σ+3))
          linarith [hh]
      _ = ℓ^(3*σ+4) := hpow.symm
  -- Conjunct 5
  have hitem5 : (Xcut Pa σ : ℝ) < Pa.N^δ := by
    have hℓpow : ℓ^(3*σ+3) ≤ (x:ℝ)^((1/4+η)*δ/2) :=
      le_trans (Real.rpow_le_rpow hℓ0 hℓ_le_L h3σ3) hL6
    have h1le : 1 ≤ (x:ℝ)^((1/4+η)*δ/2) := le_trans (by norm_num) hL7
    have hsq : 2 * (x:ℝ)^((1/4+η)*δ/2) < ((x:ℝ)^((1/4+η)*δ/2))^2 := by
      have hy0 : 0 < (x:ℝ)^((1/4+η)*δ/2) := lt_of_lt_of_le (by norm_num) hL7
      nlinarith [hL7, hy0]
    have hxpowδ : ((x:ℝ)^((1/4+η)*δ/2))^2 = (x:ℝ)^((1/4+η)*δ) := by
      rw [pow_two, ← Real.rpow_add hxpos,
          show (1/4+η)*δ/2 + (1/4+η)*δ/2 = (1/4+η)*δ by ring]
    have hlt : (x:ℝ)^((1/4+η)*δ) < Pa.N^δ := by
      have h := Real.rpow_lt_rpow (Real.rpow_nonneg hxpos.le (1/4+η)) hNlo hδ
      rw [← Real.rpow_mul hxpos.le (1/4+η) δ] at h
      exact h
    calc (Xcut Pa σ : ℝ) ≤ ℓ^(3*σ+3) + 1 := hceil
      _ ≤ (x:ℝ)^((1/4+η)*δ/2) + 1 := by linarith
      _ ≤ 2 * (x:ℝ)^((1/4+η)*δ/2) := by linarith
      _ < ((x:ℝ)^((1/4+η)*δ/2))^2 := hsq
      _ = (x:ℝ)^((1/4+η)*δ) := hxpowδ
      _ < Pa.N^δ := hlt
  -- Conjunct 6, 7
  have hitem6 : 16 ≤ Pa.M := by linarith [hMge, hNlo, hL8]
  have hitem7 : 3 ≤ Pa.N := by linarith [hNlo, hL8]
  unfold PieceFacts
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [← hLdef, ← hℓdef, hσs9] using hitem1
  · exact hitem2
  · exact hitem3
  · simpa only [← hℓdef] using hitem4
  · exact hitem5
  · exact hitem6
  · exact hitem7

end Work.FITop4.Red5
