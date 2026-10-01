import Mathlib
import Submission.Work.LinnikAreas2.gamma_le_inv

/-!
# `Work.LinnikAreas2.thetaSharp_closing`

The closing ("arithmetic") step of the sharp HB (11.17) estimate
(`Work.LinnikAreas2.theta_diag_sharp2`): a purely real-analytic inequality which turns the output
of the Abel summation + unimodal Euler comparison into the stated right-hand side.

All the content is asymptotic: for `L → ∞` the quantity

`(1 + c K) K^{σ-1} (1 - e^{-K/B}) + c (Γ σ (A^σ - B^σ) + 2 x₀^{σ-1} (1 - e^{-x₀/B}))`

(with `B = U/L²`, `U = e^{uL}`, `A = e^{xL}`, `c = (1+ε/2)/(wL) + C₁/(wL)²`, `σ ∈ (0,1]` with
`σL ≤ (2/3) log log L`) is bounded by `(1+3ε/4) (A^σ - U^σ)/(wσL) + η` for large `L`, while
`(A^σ - U^σ)/(σL) ≥ (x-u)`, giving room `~ (ε/4)(x-u)/w` to absorb the three error terms.
-/

namespace Work.LinnikAreas2

/-! ## Elementary analytic helpers -/

/-- `1 - exp(-y) ≤ y` for `y ≥ 0`. -/
private lemma one_sub_exp_neg_le {y : ℝ} (hy : 0 ≤ y) : 1 - Real.exp (-y) ≤ y := by
  have h := Real.add_one_le_exp (-y)
  linarith

/-- `(log L)^a / L` is eventually `≤ δ`, for `a ≥ 0`, `δ > 0`.  Also returns `1 ≤ log L`. -/
private lemma eventually_logpow_div_le (a : ℝ) (ha : 0 ≤ a) (δ : ℝ) (hδ : 0 < δ) :
    ∃ L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L → (Real.log L)^a / L ≤ δ ∧ 1 ≤ Real.log L := by
  set n : ℕ := ⌈a⌉₊ with hn
  have han : a ≤ (n : ℝ) := by rw [hn]; exact Nat.le_ceil a
  have hlim : Filter.Tendsto (fun L : ℝ => Real.log L ^ n / L) Filter.atTop (nhds 0) := by
    have h := Real.tendsto_pow_log_div_mul_add_atTop (1:ℝ) 0 n one_ne_zero
    simpa using h
  have hev : ∀ᶠ L : ℝ in Filter.atTop, Real.log L ^ n / L ≤ δ :=
    hlim.eventually_le_const hδ
  obtain ⟨L₁, hL₁⟩ := Filter.eventually_atTop.mp hev
  refine ⟨max (max L₁ 1) (Real.exp 1), fun L hL => ⟨?_, ?_⟩⟩
  · have hLL1 : L₁ ≤ L :=
      le_trans (le_trans (le_max_left L₁ 1) (le_max_left (max L₁ 1) (Real.exp 1))) hL
    have hL1 : 1 ≤ L := le_trans (le_trans (le_max_right L₁ 1) (le_max_left _ _)) hL
    have hLpos : 0 < L := lt_of_lt_of_le one_pos hL1
    have hLe : Real.exp 1 ≤ L := le_trans (le_max_right _ _) hL
    have hlog1 : 1 ≤ Real.log L := by
      have h := Real.log_le_log (Real.exp_pos 1) hLe
      rwa [Real.log_exp] at h
    have h1 : (Real.log L)^a ≤ Real.log L ^ n := by
      have hh := Real.rpow_le_rpow_of_exponent_le hlog1 han
      rwa [Real.rpow_natCast] at hh
    have h2 : Real.log L ^ n / L ≤ δ := hL₁ L hLL1
    have h3 : (Real.log L)^a / L ≤ Real.log L ^ n / L :=
      div_le_div_of_nonneg_right h1 hLpos.le
    linarith
  · have hLe : Real.exp 1 ≤ L := le_trans (le_max_right _ _) hL
    have h := Real.log_le_log (Real.exp_pos 1) hLe
    rwa [Real.log_exp] at h

/-- `L^2 * exp(-(u L)) * (log L)^b` is eventually `≤ δ`, for `u > 0`, `b ≥ 0`, `δ > 0`. -/
private lemma eventually_logpow_mul_exp_le (u b : ℝ) (hu : 0 < u) (hb : 0 ≤ b)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L → L^2 * Real.exp (-(u*L)) * (Real.log L)^b ≤ δ := by
  set n : ℕ := ⌈b⌉₊ with hn
  have hbn : b ≤ (n : ℝ) := by rw [hn]; exact Nat.le_ceil b
  have huN : 0 < u ^ (n+2) := pow_pos hu _
  have hlim : Filter.Tendsto (fun L : ℝ => (u*L)^(n+2) * Real.exp (-(u*L)))
      Filter.atTop (nhds 0) :=
    (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero (n+2)).comp
      (Filter.Tendsto.const_mul_atTop hu Filter.tendsto_id)
  have hev : ∀ᶠ L : ℝ in Filter.atTop,
      (u*L)^(n+2) * Real.exp (-(u*L)) ≤ δ * u^(n+2) :=
    hlim.eventually_le_const (by positivity)
  obtain ⟨L₁, hL₁⟩ := Filter.eventually_atTop.mp hev
  refine ⟨max (max L₁ 1) (Real.exp 1), fun L hL => ?_⟩
  have hLL1 : L₁ ≤ L :=
    le_trans (le_trans (le_max_left L₁ 1) (le_max_left (max L₁ 1) (Real.exp 1))) hL
  have hL1 : 1 ≤ L := le_trans (le_trans (le_max_right L₁ 1) (le_max_left _ _)) hL
  have hLpos : 0 < L := lt_of_lt_of_le one_pos hL1
  have hLe : Real.exp 1 ≤ L := le_trans (le_max_right _ _) hL
  have hlog1 : 1 ≤ Real.log L := by
    have h := Real.log_le_log (Real.exp_pos 1) hLe
    rwa [Real.log_exp] at h
  have hlogpos : 0 < Real.log L := lt_of_lt_of_le one_pos hlog1
  have hb1 : (Real.log L)^b ≤ Real.log L ^ n := by
    have hh := Real.rpow_le_rpow_of_exponent_le hlog1 hbn
    rwa [Real.rpow_natCast] at hh
  have hlognn : Real.log L ^ n ≤ L ^ n :=
    pow_le_pow_left₀ (Real.log_nonneg hL1) (Real.log_le_self hLpos.le) n
  have hbound : L^2 * Real.exp (-(u*L)) * (Real.log L)^b ≤ L^(n+2) * Real.exp (-(u*L)) := by
    have h1 : (Real.log L)^b ≤ L^n := le_trans hb1 hlognn
    have h2 : L^2 * (Real.log L)^b ≤ L^2 * L^n :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have h3 : L^2 * L^n = L^(n+2) := by rw [← pow_add, Nat.add_comm]
    calc L^2 * Real.exp (-(u*L)) * (Real.log L)^b
        = Real.exp (-(u*L)) * (L^2 * (Real.log L)^b) := by ring
      _ ≤ Real.exp (-(u*L)) * (L^2 * L^n) :=
            mul_le_mul_of_nonneg_left h2 (Real.exp_nonneg _)
      _ = L^(n+2) * Real.exp (-(u*L)) := by rw [h3]; ring
  have heq : L^(n+2) * Real.exp (-(u*L))
      = ((u*L)^(n+2) * Real.exp (-(u*L))) / u^(n+2) := by
    rw [mul_pow]
    field_simp
  have hkey : L^(n+2) * Real.exp (-(u*L)) ≤ δ := by
    rw [heq, div_le_iff₀ huN]
    exact hL₁ L hLL1
  linarith [hbound, hkey]

/-- `(e^{aL})^σ ≤ (log L)^{2a/3}` when `a > 0`, `log L ≥ 1` and `σL ≤ (2/3) log log L`. -/
private lemma rpow_exp_le (a L σ : ℝ) (ha : 0 < a) (hlog : 1 ≤ Real.log L)
    (hσL : σ*L ≤ (2/3)*Real.log (Real.log L)) :
    (Real.exp (a*L))^σ ≤ (Real.log L)^(2*a/3) := by
  have hlogpos : 0 < Real.log L := lt_of_lt_of_le one_pos hlog
  have h1 : a*L*σ ≤ (2*a/3)*Real.log (Real.log L) := by
    have h2 : a * (σ*L) ≤ a * ((2/3)*Real.log (Real.log L)) :=
      mul_le_mul_of_nonneg_left hσL ha.le
    have he : a*L*σ = a*(σ*L) := by ring
    have he2 : (2*a/3)*Real.log (Real.log L) = a*((2/3)*Real.log (Real.log L)) := by ring
    rw [he, he2]; exact h2
  calc (Real.exp (a*L))^σ = Real.exp (a*L*σ) := (Real.exp_mul (a*L) σ).symm
    _ ≤ Real.exp ((2*a/3)*Real.log (Real.log L)) := Real.exp_le_exp.mpr h1
    _ = (Real.log L)^(2*a/3) := by
        rw [show (2*a/3)*Real.log (Real.log L)
              = Real.log (Real.log L) * (2*a/3) from by ring,
            Real.exp_mul, Real.exp_log hlogpos]

/-- `(e^{uL}/L^2)^{σ-1} ≤ L^2 * e^{-uL} * (log L)^{2u/3}` under `σL ≤ (2/3) log log L`,
`0 < σ ≤ 1`, `L ≥ 1`, `log L ≥ 1`. -/
private lemma B_rpow_sub_one_le (u L σ : ℝ) (hu : 0 < u) (hL : 1 ≤ L) (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (hlog : 1 ≤ Real.log L) (hσL : σ*L ≤ (2/3)*Real.log (Real.log L)) :
    (Real.exp (u*L)/L^2)^(σ-1) ≤ L^2 * Real.exp (-(u*L)) * (Real.log L)^(2*u/3) := by
  have hLpos : 0 < L := lt_of_lt_of_le one_pos hL
  have hlogpos : 0 < Real.log L := lt_of_lt_of_le one_pos hlog
  have hexp : 0 < Real.exp (u*L) := Real.exp_pos _
  have hL2pos : 0 < L^2 := by positivity
  have hB : 0 < Real.exp (u*L)/L^2 := div_pos hexp hL2pos
  have hlogB : Real.log (Real.exp (u*L)/L^2) = u*L - 2*Real.log L := by
    rw [Real.log_div (ne_of_gt hexp) (ne_of_gt hL2pos), Real.log_exp, Real.log_pow]
    ring
  have hA : u*(σ*L) ≤ u*((2/3)*Real.log (Real.log L)) := mul_le_mul_of_nonneg_left hσL hu.le
  have hB' : 2*(1-σ)*Real.log L ≤ 2*Real.log L := by
    have hle : (1-σ) ≤ 1 := by linarith
    nlinarith [hle, hlogpos.le]
  calc (Real.exp (u*L)/L^2)^(σ-1)
      = Real.exp (Real.log (Real.exp (u*L)/L^2) * (σ-1)) := Real.rpow_def_of_pos hB (σ-1)
    _ = Real.exp ((u*L - 2*Real.log L)*(σ-1)) := by rw [hlogB]
    _ ≤ Real.exp (-(u*L) + (2*u/3)*Real.log (Real.log L) + 2*Real.log L) := by
        apply Real.exp_le_exp.mpr
        have hid : (u*L - 2*Real.log L)*(σ-1)
            = -(u*L) + u*(σ*L) + 2*(1-σ)*Real.log L := by ring
        rw [hid]
        have hA' : u*(σ*L) ≤ (2*u/3)*Real.log (Real.log L) := by
          have he : u*((2/3)*Real.log (Real.log L)) = (2*u/3)*Real.log (Real.log L) := by ring
          rwa [he] at hA
        linarith [hA', hB']
    _ = L^2 * Real.exp (-(u*L)) * (Real.log L)^(2*u/3) := by
        rw [Real.exp_add, Real.exp_add,
            show 2*Real.log L = Real.log (L^2) from by
              rw [Real.log_pow]; ring,
            Real.exp_log hL2pos,
            show (2*u/3)*Real.log (Real.log L)
              = Real.log (Real.log L) * (2*u/3) from by ring,
            Real.exp_mul, Real.exp_log hlogpos]
        ring

/-- `c ≤ c₁/L` for `L ≥ 1`. -/
private lemma coef_le (ε C₁ w L : ℝ) (hε : 0 < ε) (hC₁ : 0 < C₁) (hw : 0 < w) (hL : 1 ≤ L) :
    (1+ε/2)/(w*L) + C₁/(w*L)^2 ≤ ((1+ε/2)/w + C₁/w^2)/L := by
  have hLpos : 0 < L := lt_of_lt_of_le one_pos hL
  have hwL : w*L ≠ 0 := ne_of_gt (mul_pos hw hLpos)
  have h1 : C₁/(w*L)^2 ≤ (C₁/w^2)/L := by
    have h : (C₁/w^2)/L^2 ≤ (C₁/w^2)/L := by
      apply div_le_div_of_nonneg_left (by positivity) hLpos
      nlinarith [hL, hLpos]
    have he : (C₁/w^2)/L^2 = C₁/(w*L)^2 := by field_simp
    rwa [he] at h
  have h2 : (1+ε/2)/(w*L) = ((1+ε/2)/w)/L := by field_simp
  rw [h2]
  have : ((1+ε/2)/w)/L + (C₁/w^2)/L = ((1+ε/2)/w + C₁/w^2)/L := by field_simp
  linarith [h1, this.le, this.ge]

/-- **Term 2** (`Γ σ * (U^σ - B^σ)`, `U = e^{uL}`, `B = U/L²`): this is `o(1)`, because
`Γ σ ≤ 1/σ` cancels the `σ` coming from `1 - L^{-2σ} ≤ 2σ log L`. -/
private lemma gamma_term_le (ε C₁ w u : ℝ) (hε : 0 < ε) (hC₁ : 0 < C₁) (hw : 0 < w)
    (hu : 0 < u) (δ : ℝ) (hδ : 0 < δ) :
    ∃ L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L → ∀ σ : ℝ, 0 < σ → σ ≤ 1 →
      σ * L ≤ (2/3) * Real.log (Real.log L) →
        ((1+ε/2)/(w*L) + C₁/(w*L)^2) *
          (Real.Gamma σ * ((Real.exp (u*L))^σ - (Real.exp (u*L)/L^2)^σ)) ≤ δ := by
  set c₁ : ℝ := (1+ε/2)/w + C₁/w^2 with hc₁
  have hc₁pos : 0 < c₁ := by rw [hc₁]; positivity
  obtain ⟨L₁, hL₁⟩ := eventually_logpow_div_le (2*u/3+1) (by linarith) (δ/(2*c₁)) (by positivity)
  refine ⟨max L₁ 1, fun L hL σ hσ hσ1 hσL => ?_⟩
  have hL1 : 1 ≤ L := le_trans (le_max_right _ _) hL
  have hLpos : 0 < L := lt_of_lt_of_le one_pos hL1
  obtain ⟨hloglim, hlog1⟩ := hL₁ L (le_trans (le_max_left _ _) hL)
  have hlogpos : 0 < Real.log L := lt_of_lt_of_le one_pos hlog1
  have hUpos : 0 < Real.exp (u*L) := Real.exp_pos _
  have hL2pos : 0 < L^2 := by positivity
  have hL21 : 1 ≤ L^2 := by nlinarith [hL1]
  have hBpos : 0 < Real.exp (u*L)/L^2 := div_pos hUpos hL2pos
  have hΓ : Real.Gamma σ ≤ 1/σ := gamma_le_inv σ hσ hσ1
  have hUB : (Real.exp (u*L)/L^2)^σ ≤ (Real.exp (u*L))^σ := by
    apply Real.rpow_le_rpow hBpos.le _ hσ.le
    rw [div_le_iff₀ hL2pos]
    nlinarith [hL21, hUpos]
  have hbracket : (Real.exp (u*L))^σ - (Real.exp (u*L)/L^2)^σ
      ≤ (Real.exp (u*L))^σ * (2*σ*Real.log L) := by
    have h1 : (Real.exp (u*L)/L^2)^σ = (Real.exp (u*L))^σ * (L^2)^(-σ) := by
      rw [Real.div_rpow hUpos.le hL2pos.le, div_eq_mul_inv, Real.rpow_neg hL2pos.le]
    have h2 : (L^2)^(-σ) = Real.exp (-(2*σ*Real.log L)) := by
      rw [Real.rpow_def_of_pos hL2pos, Real.log_pow]
      congr 1; ring
    have h4 : 1 - (L^2)^(-σ) ≤ 2*σ*Real.log L := by
      rw [h2]
      exact one_sub_exp_neg_le (show (0:ℝ) ≤ 2*σ*Real.log L by positivity)
    have h3 : Real.exp (u*L)^σ - Real.exp (u*L)^σ * (L^2)^(-σ)
        = Real.exp (u*L)^σ * (1 - (L^2)^(-σ)) := by ring
    rw [h1, h3]
    exact mul_le_mul_of_nonneg_left h4 (Real.rpow_nonneg hUpos.le σ)
  have hUB2 : 0 ≤ (Real.exp (u*L))^σ - (Real.exp (u*L)/L^2)^σ := by linarith [hUB]
  have hstep : Real.Gamma σ * ((Real.exp (u*L))^σ - (Real.exp (u*L)/L^2)^σ)
      ≤ 2 * (Real.log L)^(2*u/3) * Real.log L := by
    have h2 : Real.Gamma σ * ((Real.exp (u*L))^σ - (Real.exp (u*L)/L^2)^σ)
        ≤ (1/σ) * ((Real.exp (u*L))^σ * (2*σ*Real.log L)) :=
      mul_le_mul hΓ hbracket hUB2 (by positivity)
    have h3 : (1/σ) * ((Real.exp (u*L))^σ * (2*σ*Real.log L))
        = 2 * (Real.exp (u*L))^σ * Real.log L := by field_simp
    have h4 : (Real.exp (u*L))^σ ≤ (Real.log L)^(2*u/3) := rpow_exp_le u L σ hu hlog1 hσL
    rw [h3] at h2
    have h5 : 2*(Real.exp (u*L))^σ ≤ 2*(Real.log L)^(2*u/3) := by linarith [h4]
    have h6 : 2*(Real.exp (u*L))^σ * Real.log L
        ≤ 2*(Real.log L)^(2*u/3) * Real.log L :=
      mul_le_mul_of_nonneg_right h5 hlogpos.le
    linarith [h2, h6]
  have hc : (1+ε/2)/(w*L) + C₁/(w*L)^2 ≤ c₁/L := by
    rw [hc₁]; exact coef_le ε C₁ w L hε hC₁ hw hL1
  have hcpos : 0 ≤ (1+ε/2)/(w*L) + C₁/(w*L)^2 := by positivity
  have hΓpos : 0 ≤ Real.Gamma σ := (Real.Gamma_pos_of_pos hσ).le
  have hUσnonneg : 0 ≤ (Real.exp (u*L))^σ := Real.rpow_nonneg hUpos.le σ
  have hc₁ne : c₁ ≠ 0 := ne_of_gt hc₁pos
  have hlogpow : (Real.log L)^(2*u/3+1) = (Real.log L)^(2*u/3) * Real.log L := by
    rw [Real.rpow_add hlogpos, Real.rpow_one]
  calc ((1+ε/2)/(w*L) + C₁/(w*L)^2) *
          (Real.Gamma σ * ((Real.exp (u*L))^σ - (Real.exp (u*L)/L^2)^σ))
      ≤ (c₁/L) * (2 * (Real.log L)^(2*u/3) * Real.log L) :=
        mul_le_mul hc hstep (mul_nonneg hΓpos hUB2) (by positivity)
    _ = 2*c₁ * ((Real.log L)^(2*u/3+1) / L) := by rw [hlogpow]; ring
    _ ≤ 2*c₁ * (δ/(2*c₁)) := mul_le_mul_of_nonneg_left hloglim (by positivity)
    _ = δ := by field_simp

/-- **Term 3** (the `x₀` term): `x₀^{σ-1}(1 - e^{-x₀/B}) ≤ x₀^σ/B ≤ 2 A^σ / B` and
`1/B = L² e^{-uL}`. -/
private lemma x0_term_le (ε C₁ w u x : ℝ) (hε : 0 < ε) (hC₁ : 0 < C₁) (hw : 0 < w)
    (hu : 0 < u) (hux : u < x) (δ : ℝ) (hδ : 0 < δ) :
    ∃ L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L → ∀ σ : ℝ, 0 < σ → σ ≤ 1 →
      σ * L ≤ (2/3) * Real.log (Real.log L) →
      ∀ x₀ : ℝ, 0 < x₀ →
        x₀ ≤ 2*(Real.exp (u*L)/L^2)*(1 + Real.log (Real.exp (x*L)/(Real.exp (u*L)/L^2))) →
        2 * ((1+ε/2)/(w*L) + C₁/(w*L)^2) *
          (x₀^(σ-1) * (1 - Real.exp (-x₀/(Real.exp (u*L)/L^2)))) ≤ δ := by
  set c₁ : ℝ := (1+ε/2)/w + C₁/w^2 with hc₁
  have hc₁pos : 0 < c₁ := by rw [hc₁]; positivity
  obtain ⟨L₁, hL₁⟩ := eventually_logpow_mul_exp_le u (2*x/3) hu (by linarith) (δ/(4*c₁)) (by positivity)
  refine ⟨max (max L₁ 1) (Real.exp 1), fun L hL σ hσ hσ1 hσL x₀ hx₀ hx₀X => ?_⟩
  rw [max_le_iff] at hL
  obtain ⟨hL, hLex⟩ := hL
  rw [max_le_iff] at hL
  obtain ⟨hA1, hL1⟩ := hL
  have hLpos : 0 < L := lt_of_lt_of_le one_pos hL1
  have hlog1 : 1 ≤ Real.log L := by
    have h := Real.log_le_log (Real.exp_pos 1) hLex
    rwa [Real.log_exp] at h
  have hlogpos : 0 < Real.log L := lt_of_lt_of_le one_pos hlog1
  have hL2pos : 0 < L^2 := by positivity
  have hL21 : 1 ≤ L^2 := by nlinarith [hL1]
  have hUpos : 0 < Real.exp (u*L) := Real.exp_pos _
  have hBpos : 0 < Real.exp (u*L)/L^2 := div_pos hUpos hL2pos
  have hApos : 0 < Real.exp (x*L) := Real.exp_pos _
  have hxpos : 0 < x := lt_trans hu hux
  have hAσ : (Real.exp (x*L))^σ ≤ (Real.log L)^(2*x/3) := rpow_exp_le x L σ hxpos hlog1 hσL
  have hABpos : 0 < Real.exp (x*L)/(Real.exp (u*L)/L^2) := div_pos hApos hBpos
  have hX2A : 2*(Real.exp (u*L)/L^2)*(1 + Real.log (Real.exp (x*L)/(Real.exp (u*L)/L^2)))
      ≤ 2*Real.exp (x*L) := by
    have h1 := Real.log_le_sub_one_of_pos hABpos
    have h2 : 1 + Real.log (Real.exp (x*L)/(Real.exp (u*L)/L^2))
        ≤ Real.exp (x*L)/(Real.exp (u*L)/L^2) := by linarith
    calc 2*(Real.exp (u*L)/L^2)*(1 + Real.log (Real.exp (x*L)/(Real.exp (u*L)/L^2)))
        ≤ 2*(Real.exp (u*L)/L^2)*(Real.exp (x*L)/(Real.exp (u*L)/L^2)) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = 2*Real.exp (x*L) := by field_simp
  have hx0σle : x₀^σ ≤ 2*(Real.log L)^(2*x/3) := by
    have h1 : x₀ ≤ 2*Real.exp (x*L) := by linarith [hx₀X, hX2A]
    have h2 : x₀^σ ≤ (2*Real.exp (x*L))^σ := Real.rpow_le_rpow hx₀.le h1 hσ.le
    have h2σ : (2:ℝ)^σ ≤ 2 := Real.rpow_le_self_of_one_le (by norm_num) hσ1
    have hmul : (2*Real.exp (x*L))^σ = 2^σ * (Real.exp (x*L))^σ :=
      Real.mul_rpow (by norm_num) hApos.le
    rw [hmul] at h2
    have h3 := mul_le_mul_of_nonneg_right h2σ (Real.rpow_nonneg hApos.le σ)
    linarith [h2, h3, hAσ]
  have hstep1 : x₀^(σ-1) * (1 - Real.exp (-x₀/(Real.exp (u*L)/L^2)))
      ≤ x₀^σ * (L^2 * Real.exp (-(u*L))) := by
    have h1 : 1 - Real.exp (-x₀/(Real.exp (u*L)/L^2)) ≤ x₀/(Real.exp (u*L)/L^2) := by
      have h := one_sub_exp_neg_le (y := x₀/(Real.exp (u*L)/L^2))
        (show (0:ℝ) ≤ x₀/(Real.exp (u*L)/L^2) by positivity)
      simpa only [neg_div] using h
    have hid : x₀^σ/(Real.exp (u*L)/L^2) = x₀^σ * (L^2 * Real.exp (-(u*L))) := by
      rw [div_eq_mul_inv, inv_div, div_eq_mul_inv, Real.exp_neg]
    calc x₀^(σ-1) * (1 - Real.exp (-x₀/(Real.exp (u*L)/L^2)))
        ≤ x₀^(σ-1) * (x₀/(Real.exp (u*L)/L^2)) :=
          mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg hx₀.le _)
      _ = x₀^σ/(Real.exp (u*L)/L^2) := by
          have hx0pow : x₀^(σ-1) * x₀ = x₀^σ := by
            have h := Real.rpow_add hx₀ (σ-1) 1
            rw [Real.rpow_one] at h
            rw [← h]; congr 1; ring
          rw [mul_div_assoc', hx0pow]
      _ = x₀^σ * (L^2 * Real.exp (-(u*L))) := hid
  have hstep2 : x₀^σ * (L^2 * Real.exp (-(u*L)))
      ≤ 2*(Real.log L)^(2*x/3) * (L^2 * Real.exp (-(u*L))) :=
    mul_le_mul_of_nonneg_right hx0σle (by positivity)
  have hc : (1+ε/2)/(w*L) + C₁/(w*L)^2 ≤ c₁/L := by
    rw [hc₁]; exact coef_le ε C₁ w L hε hC₁ hw hL1
  have hLx : L^2 * Real.exp (-(u*L)) * (Real.log L)^(2*x/3) / L
      ≤ L^2 * Real.exp (-(u*L)) * (Real.log L)^(2*x/3) := by
    have hXnn : 0 ≤ L^2 * Real.exp (-(u*L)) * (Real.log L)^(2*x/3) := by positivity
    rw [div_le_iff₀ hLpos]
    nlinarith [hL1, hXnn]
  calc 2 * ((1+ε/2)/(w*L) + C₁/(w*L)^2)
        * (x₀^(σ-1) * (1 - Real.exp (-x₀/(Real.exp (u*L)/L^2))))
      ≤ 2 * ((1+ε/2)/(w*L) + C₁/(w*L)^2)
        * (2*(Real.log L)^(2*x/3) * (L^2 * Real.exp (-(u*L)))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact le_trans hstep1 hstep2
    _ ≤ 2 * (c₁/L) * (2*(Real.log L)^(2*x/3) * (L^2 * Real.exp (-(u*L)))) := by
        have hYnn : 0 ≤ 2*(Real.log L)^(2*x/3) * (L^2 * Real.exp (-(u*L))) := by positivity
        have h1 : ((1+ε/2)/(w*L) + C₁/(w*L)^2)
              * (2*(Real.log L)^(2*x/3) * (L^2 * Real.exp (-(u*L))))
            ≤ (c₁/L) * (2*(Real.log L)^(2*x/3) * (L^2 * Real.exp (-(u*L)))) :=
          mul_le_mul_of_nonneg_right hc hYnn
        linarith [h1]
    _ = 4*c₁ * (L^2 * Real.exp (-(u*L)) * (Real.log L)^(2*x/3) / L) := by ring
    _ ≤ 4*c₁ * (L^2 * Real.exp (-(u*L)) * (Real.log L)^(2*x/3)) :=
        mul_le_mul_of_nonneg_left hLx (by positivity)
    _ ≤ 4*c₁ * (δ/(4*c₁)) := mul_le_mul_of_nonneg_left (hL₁ L hA1) (by positivity)
    _ = δ := by field_simp

/-- **Term 1** (the Abel head term): `(1+cK)K^{σ-1}(1-e^{-K/B}) = o(1)` uniformly over
`K ≤ 2B(1 + log(A/B)) + 2`. -/
private lemma head_term_le (ε C₁ w u x : ℝ) (hε : 0 < ε) (hC₁ : 0 < C₁) (hw : 0 < w)
    (hu : 0 < u) (hux : u < x) (δ : ℝ) (hδ : 0 < δ) :
    ∃ L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L → ∀ σ : ℝ, 0 < σ → σ ≤ 1 →
      σ * L ≤ (2/3) * Real.log (Real.log L) →
      ∀ K : ℕ,
        (K:ℝ) ≤ 2*(Real.exp (u*L)/L^2)*(1 + Real.log (Real.exp (x*L)/(Real.exp (u*L)/L^2))) + 2 →
        (1 + ((1+ε/2)/(w*L) + C₁/(w*L)^2) * (K:ℝ)) *
          ((K:ℝ)^(σ-1) * (1 - Real.exp (-(K:ℝ)/(Real.exp (u*L)/L^2)))) ≤ δ := by
  set c₁ : ℝ := (1+ε/2)/w + C₁/w^2 with hc₁
  have hc₁pos : 0 < c₁ := by rw [hc₁]; positivity
  obtain ⟨L₁, hL₁⟩ := eventually_logpow_mul_exp_le u (2*u/3) hu (by linarith) (δ/3) (by linarith)
  obtain ⟨L₂, hL₂⟩ := eventually_logpow_div_le (2*u/3) (by linarith) (δ/(3*c₁)) (by positivity)
  obtain ⟨L₃, hL₃⟩ := eventually_logpow_div_le (2*x/3) (by linarith) (δ/(12*c₁)) (by positivity)
  obtain ⟨L₄, hL₄⟩ := eventually_logpow_div_le 0 (by norm_num) (δ/(12*c₁)) (by positivity)
  refine ⟨max (max (max (max (max L₁ L₂) L₃) L₄) 1) (Real.exp 1), fun L hL => ?_⟩
  rw [max_le_iff] at hL
  obtain ⟨hL, hLex⟩ := hL
  rw [max_le_iff] at hL
  obtain ⟨hL, hL1⟩ := hL
  rw [max_le_iff] at hL
  obtain ⟨hL, hA4⟩ := hL
  rw [max_le_iff] at hL
  obtain ⟨hL, hA3⟩ := hL
  rw [max_le_iff] at hL
  obtain ⟨hA1, hA2⟩ := hL
  intro σ hσ hσ1 hσL K hK
  have hLpos : 0 < L := lt_of_lt_of_le one_pos hL1
  have hlog1 : 1 ≤ Real.log L := (hL₂ L hA2).2
  have hlogpos : 0 < Real.log L := lt_of_lt_of_le one_pos hlog1
  have hL2pos : 0 < L^2 := by positivity
  have hL21 : 1 ≤ L^2 := by nlinarith [hL1]
  have hUpos : 0 < Real.exp (u*L) := Real.exp_pos _
  have hApos : 0 < Real.exp (x*L) := Real.exp_pos _
  have hxpos : 0 < x := lt_trans hu hux
  have hBpos : 0 < Real.exp (u*L)/L^2 := div_pos hUpos hL2pos
  have hc : (1+ε/2)/(w*L) + C₁/(w*L)^2 ≤ c₁/L := by
    rw [hc₁]; exact coef_le ε C₁ w L hε hC₁ hw hL1
  have hcpos : 0 ≤ (1+ε/2)/(w*L) + C₁/(w*L)^2 := by positivity
  have hE1 : (Real.exp (u*L)/L^2)^(σ-1) ≤ δ/3 :=
    le_trans (B_rpow_sub_one_le u L σ hu hL1 hσ hσ1 hlog1 hσL) (hL₁ L hA1)
  have hBσ : (Real.exp (u*L)/L^2)^σ ≤ (Real.log L)^(2*u/3) := by
    have h1 : (Real.exp (u*L)/L^2)^σ ≤ (Real.exp (u*L))^σ := by
      apply Real.rpow_le_rpow hBpos.le _ hσ.le
      rw [div_le_iff₀ hL2pos]
      nlinarith [hL21, hUpos]
    exact le_trans h1 (rpow_exp_le u L σ hu hlog1 hσL)
  have hE2 : ((1+ε/2)/(w*L) + C₁/(w*L)^2) * (Real.exp (u*L)/L^2)^σ ≤ δ/3 := by
    have h1 : ((1+ε/2)/(w*L) + C₁/(w*L)^2) * (Real.exp (u*L)/L^2)^σ
        ≤ (c₁/L) * (Real.log L)^(2*u/3) :=
      mul_le_mul hc hBσ (Real.rpow_nonneg hBpos.le _) (by positivity)
    have h2 : (c₁/L) * (Real.log L)^(2*u/3) = c₁ * ((Real.log L)^(2*u/3)/L) := by ring
    have h3 : (Real.log L)^(2*u/3)/L ≤ δ/(3*c₁) := (hL₂ L hA2).1
    calc ((1+ε/2)/(w*L) + C₁/(w*L)^2) * (Real.exp (u*L)/L^2)^σ
        ≤ (c₁/L) * (Real.log L)^(2*u/3) := h1
      _ = c₁ * ((Real.log L)^(2*u/3)/L) := h2
      _ ≤ c₁ * (δ/(3*c₁)) := mul_le_mul_of_nonneg_left h3 hc₁pos.le
      _ = δ/3 := by field_simp
  have hAσ : (Real.exp (x*L))^σ ≤ (Real.log L)^(2*x/3) := rpow_exp_le x L σ hxpos hlog1 hσL
  have hE3 : ((1+ε/2)/(w*L) + C₁/(w*L)^2) * (2*(Real.exp (x*L))^σ + 2) ≤ δ/3 := by
    have h1 : ((1+ε/2)/(w*L) + C₁/(w*L)^2) * (2*(Real.exp (x*L))^σ + 2)
        ≤ (c₁/L) * (2*(Real.log L)^(2*x/3) + 2) :=
      mul_le_mul hc (by linarith [hAσ]) (by positivity) (by positivity)
    have h3 : (Real.log L)^(2*x/3)/L ≤ δ/(12*c₁) := (hL₃ L hA3).1
    have h4 : (Real.log L)^(0:ℝ)/L ≤ δ/(12*c₁) := (hL₄ L hA4).1
    have h4' : 1/L ≤ δ/(12*c₁) := by
      simpa [Real.rpow_zero] using h4
    have he : (c₁/L) * (2*(Real.log L)^(2*x/3) + 2)
        = 2*c₁*((Real.log L)^(2*x/3)/L) + 2*c₁*(1/L) := by ring
    calc ((1+ε/2)/(w*L) + C₁/(w*L)^2) * (2*(Real.exp (x*L))^σ + 2)
        ≤ (c₁/L) * (2*(Real.log L)^(2*x/3) + 2) := h1
      _ = 2*c₁*((Real.log L)^(2*x/3)/L) + 2*c₁*(1/L) := he
      _ ≤ 2*c₁*(δ/(12*c₁)) + 2*c₁*(δ/(12*c₁)) := by
          apply add_le_add <;> exact mul_le_mul_of_nonneg_left ‹_› (by positivity)
      _ = δ/3 := by field_simp; ring
  rcases Nat.eq_zero_or_pos K with hK0 | hKpos
  · subst hK0
    have hz : (1 - Real.exp (-(((0:ℕ):ℝ))/(Real.exp (u*L)/L^2))) = 0 := by simp
    rw [hz]
    nlinarith [hδ]
  · have hKpos' : (0:ℝ) < (K:ℝ) := by exact_mod_cast hKpos
    rcases le_or_gt (K:ℝ) (Real.exp (u*L)/L^2) with hKB | hBK
    · have hnot : 1 - Real.exp (-(K:ℝ)/(Real.exp (u*L)/L^2))
          ≤ (K:ℝ)/(Real.exp (u*L)/L^2) := by
        have h := one_sub_exp_neg_le (show (0:ℝ) ≤ (K:ℝ)/(Real.exp (u*L)/L^2) by positivity)
        simpa only [neg_div] using h
      have hKpow : (K:ℝ)^(σ-1) * (K:ℝ) = (K:ℝ)^σ := by
        have h := Real.rpow_add hKpos' (σ-1) 1
        rw [Real.rpow_one] at h
        rw [← h]; congr 1; ring
      have hBσ_eq : (Real.exp (u*L)/L^2)^(σ-1) * (Real.exp (u*L)/L^2)
          = (Real.exp (u*L)/L^2)^σ := by
        have h := Real.rpow_add hBpos (σ-1) 1
        rw [Real.rpow_one] at h
        rw [← h]; congr 1; ring
      have hKB1 : (K:ℝ)^σ/(Real.exp (u*L)/L^2) ≤ (Real.exp (u*L)/L^2)^(σ-1) := by
        rw [div_le_iff₀ hBpos, hBσ_eq]
        exact Real.rpow_le_rpow hKpos'.le hKB hσ.le
      have hBsig : (Real.exp (u*L)/L^2) * (Real.exp (u*L)/L^2)^(σ-1)
          = (Real.exp (u*L)/L^2)^σ := by
        rw [mul_comm]; exact hBσ_eq
      have hfin : (1 + ((1+ε/2)/(w*L) + C₁/(w*L)^2) * (K:ℝ))
            * ((K:ℝ)^σ/(Real.exp (u*L)/L^2)) ≤ δ := by
        have h2 : (1 + ((1+ε/2)/(w*L) + C₁/(w*L)^2) * (K:ℝ))
              * ((K:ℝ)^σ/(Real.exp (u*L)/L^2))
            ≤ (1 + ((1+ε/2)/(w*L) + C₁/(w*L)^2) * (Real.exp (u*L)/L^2))
              * (Real.exp (u*L)/L^2)^(σ-1) := by
          apply mul_le_mul _ hKB1 (by positivity) (by positivity)
          have := mul_le_mul_of_nonneg_left hKB hcpos
          linarith
        have h3 : (1 + ((1+ε/2)/(w*L) + C₁/(w*L)^2) * (Real.exp (u*L)/L^2))
              * (Real.exp (u*L)/L^2)^(σ-1)
            = (Real.exp (u*L)/L^2)^(σ-1)
              + ((1+ε/2)/(w*L) + C₁/(w*L)^2) * ((Real.exp (u*L)/L^2)^σ) := by
          rw [add_mul, one_mul, mul_assoc, hBsig]
        rw [h3] at h2
        linarith [h2, hE1, hE2]
      have hstep : (1 + ((1+ε/2)/(w*L) + C₁/(w*L)^2) * (K:ℝ))
            * ((K:ℝ)^(σ-1) * (1 - Real.exp (-(K:ℝ)/(Real.exp (u*L)/L^2))))
          ≤ (1 + ((1+ε/2)/(w*L) + C₁/(w*L)^2) * (K:ℝ))
            * ((K:ℝ)^σ/(Real.exp (u*L)/L^2)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        calc (K:ℝ)^(σ-1) * (1 - Real.exp (-(K:ℝ)/(Real.exp (u*L)/L^2)))
            ≤ (K:ℝ)^(σ-1) * ((K:ℝ)/(Real.exp (u*L)/L^2)) :=
              mul_le_mul_of_nonneg_left hnot (Real.rpow_nonneg hKpos'.le _)
          _ = (K:ℝ)^σ/(Real.exp (u*L)/L^2) := by rw [mul_div_assoc', hKpow]
      linarith [hstep, hfin]
    · have hble1 : 1 - Real.exp (-(K:ℝ)/(Real.exp (u*L)/L^2)) ≤ 1 := by
        have := Real.exp_pos (-(K:ℝ)/(Real.exp (u*L)/L^2)); linarith
      have hKpowle : (K:ℝ)^(σ-1) ≤ (Real.exp (u*L)/L^2)^(σ-1) := by
        have h1σ : 0 ≤ 1-σ := by linarith
        rw [show σ-1 = -(1-σ) from by ring, Real.rpow_neg hKpos'.le, Real.rpow_neg hBpos.le]
        rw [inv_le_inv₀ (Real.rpow_pos_of_pos hKpos' _) (Real.rpow_pos_of_pos hBpos _)]
        exact Real.rpow_le_rpow hBpos.le (le_of_lt hBK) h1σ
      have hXσ : (K:ℝ)^σ ≤ 2*(Real.exp (x*L))^σ + 2 := by
        have hX0 : 0 ≤ 2*(Real.exp (u*L)/L^2)
            * (1 + Real.log (Real.exp (x*L)/(Real.exp (u*L)/L^2))) + 2 :=
          le_trans hKpos'.le hK
        have hABpos : 0 < Real.exp (x*L)/(Real.exp (u*L)/L^2) := div_pos hApos hBpos
        have hX2A : 2*(Real.exp (u*L)/L^2)
              * (1 + Real.log (Real.exp (x*L)/(Real.exp (u*L)/L^2))) + 2
            ≤ 2*Real.exp (x*L) + 2 := by
          have h1 := Real.log_le_sub_one_of_pos hABpos
          have h2 : 1 + Real.log (Real.exp (x*L)/(Real.exp (u*L)/L^2))
              ≤ Real.exp (x*L)/(Real.exp (u*L)/L^2) := by linarith
          have h3 : 2*(Real.exp (u*L)/L^2)*(1 + Real.log (Real.exp (x*L)/(Real.exp (u*L)/L^2)))
              ≤ 2*Real.exp (x*L) := by
            calc 2*(Real.exp (u*L)/L^2)*(1 + Real.log (Real.exp (x*L)/(Real.exp (u*L)/L^2)))
                ≤ 2*(Real.exp (u*L)/L^2)*(Real.exp (x*L)/(Real.exp (u*L)/L^2)) :=
                  mul_le_mul_of_nonneg_left h2 (by positivity)
              _ = 2*Real.exp (x*L) := by field_simp
          linarith
        have h2σ : (2:ℝ)^σ ≤ 2 := Real.rpow_le_self_of_one_le (by norm_num) hσ1
        have hmul : (2*Real.exp (x*L))^σ = 2^σ * (Real.exp (x*L))^σ :=
          Real.mul_rpow (by norm_num) hApos.le
        have h3 := mul_le_mul_of_nonneg_right h2σ (Real.rpow_nonneg hApos.le σ)
        calc (K:ℝ)^σ
            ≤ (2*(Real.exp (u*L)/L^2)
                * (1 + Real.log (Real.exp (x*L)/(Real.exp (u*L)/L^2))) + 2)^σ :=
              Real.rpow_le_rpow hKpos'.le hK hσ.le
          _ ≤ (2*Real.exp (x*L) + 2)^σ := Real.rpow_le_rpow hX0 hX2A hσ.le
          _ ≤ (2*Real.exp (x*L))^σ + 2^σ :=
              Real.rpow_add_le_add_rpow (by positivity) (by norm_num) hσ.le hσ1
          _ ≤ 2*(Real.exp (x*L))^σ + 2 := by rw [hmul]; linarith [h3]
      have hfin : (1 + ((1+ε/2)/(w*L) + C₁/(w*L)^2) * (K:ℝ)) * (K:ℝ)^(σ-1) ≤ δ := by
        have h2 : (1 + ((1+ε/2)/(w*L) + C₁/(w*L)^2) * (K:ℝ)) * (K:ℝ)^(σ-1)
            = (K:ℝ)^(σ-1) + ((1+ε/2)/(w*L) + C₁/(w*L)^2) * ((K:ℝ)*(K:ℝ)^(σ-1)) := by
          ring
        have h3 : (K:ℝ)*(K:ℝ)^(σ-1) = (K:ℝ)^σ := by
          have h := Real.rpow_add hKpos' (σ-1) 1
          rw [Real.rpow_one] at h
          rw [mul_comm, ← h]; congr 1; ring
        have h4 : ((1+ε/2)/(w*L) + C₁/(w*L)^2) * ((K:ℝ)^σ)
            ≤ ((1+ε/2)/(w*L) + C₁/(w*L)^2) * (2*(Real.exp (x*L))^σ + 2) :=
          mul_le_mul_of_nonneg_left hXσ hcpos
        rw [h2, h3]
        linarith [hE1, hE3, h4, hKpowle]
      have hstep : (1 + ((1+ε/2)/(w*L) + C₁/(w*L)^2) * (K:ℝ))
            * ((K:ℝ)^(σ-1) * (1 - Real.exp (-(K:ℝ)/(Real.exp (u*L)/L^2))))
          ≤ (1 + ((1+ε/2)/(w*L) + C₁/(w*L)^2) * (K:ℝ)) * (K:ℝ)^(σ-1) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        calc (K:ℝ)^(σ-1) * (1 - Real.exp (-(K:ℝ)/(Real.exp (u*L)/L^2)))
            ≤ (K:ℝ)^(σ-1) * 1 := mul_le_mul_of_nonneg_left hble1 (Real.rpow_nonneg hKpos'.le _)
          _ = (K:ℝ)^(σ-1) := by ring
      linarith [hstep, hfin]

/-- The coefficient identity `wσL·c = (1+ε/2)·σ + (C₁/(wL))·σ` used in the closing. -/
private lemma close_coef_eq (w σ L ε C₁ G : ℝ) (hw : 0 < w) (hL : 0 < L) :
    w*σ*L * (((1+ε/2)/(w*L) + C₁/(w*L)^2) * G)
      = (1+ε/2)*(σ*G) + (C₁/(w*L))*(σ*G) := by
  have hwL : (w*L) ≠ 0 := by positivity
  field_simp

/-- `A^σ - U^σ ≥ (x-u)σL` for `A = e^{xL}`, `U = e^{uL}` (the lower bound on the gain). -/
private lemma exp_surplus {σ u x L : ℝ} (hσ : 0 < σ) (hL : 0 < L) (hu : 0 < u) (hux : u < x) :
    (x-u)*σ*L ≤ (Real.exp (x*L))^σ - (Real.exp (u*L))^σ := by
  have ht : 0 ≤ (x-u)*L*σ := by
    have : 0 < x - u := by linarith
    positivity
  have hUge1 : 1 ≤ Real.exp (u*L*σ) := by
    rw [Real.one_le_exp_iff]; positivity
  have hexp : (x-u)*L*σ ≤ Real.exp ((x-u)*L*σ) - 1 := by
    have := Real.add_one_le_exp ((x-u)*L*σ)
    linarith
  have hA : (Real.exp (x*L))^σ = Real.exp (u*L*σ) * Real.exp ((x-u)*L*σ) := by
    rw [(Real.exp_mul (x*L) σ).symm, ← Real.exp_add]
    congr 1; ring
  have hB : (Real.exp (u*L))^σ = Real.exp (u*L*σ) := (Real.exp_mul (u*L) σ).symm
  have hkey : (Real.exp (x*L))^σ - (Real.exp (u*L))^σ
      = Real.exp (u*L*σ) * (Real.exp ((x-u)*L*σ) - 1) := by
    rw [hA, hB]; ring
  rw [hkey]
  nlinarith [hexp, hUge1, ht]

theorem thetaSharp_closing {ε C₁ w u x : ℝ} (hε : 0 < ε) (hC₁ : 0 < C₁) (hw : 0 < w)
    (hu : 0 < u) (h2wu : 2*w < u) (hux : u < x) :
    ∃ L₀ C₂ : ℝ, 0 < L₀ ∧ 0 < C₂ ∧
      ∀ (L β A U B σ M : ℝ), L₀ ≤ L → (1/2 : ℝ) ≤ β → β < 1 →
        (1-β)*L ≤ Real.log (Real.log L)/3 → A = Real.exp (x*L) → U = Real.exp (u*L) →
        B = U/L^2 → σ = 2-2*β → M = w*L → 0 < B → B < A →
        ∀ (K : ℕ) (x₀ : ℝ),
          ((K:ℝ) ≤ 2*B*(1 + Real.log (A/B)) + 2) → 0 < x₀ → x₀ ≤ 2*B*(1 + Real.log (A/B)) →
          (1 + ((1+ε/2)/M + C₁/M^2) * (K:ℝ)) * ((K:ℝ)^(σ-1) * (1 - Real.exp (-(K:ℝ)/B)))
            + ((1+ε/2)/M + C₁/M^2) *
              (Real.Gamma σ * (A^σ - B^σ) + 2 * (x₀^(σ-1) * (1 - Real.exp (-x₀/B))))
          ≤ (1+ε) * (A^σ - U^σ) / (2*w*(1-β)*L) + C₂/L := by
  set η : ℝ := ε*(x-u)/(4*w) with hηdef
  have hηpos : 0 < η := by rw [hηdef]; positivity
  obtain ⟨Lh, hh⟩ := head_term_le ε C₁ w u x hε hC₁ hw hu hux (η/3) (by linarith)
  obtain ⟨Lg, hg⟩ := gamma_term_le ε C₁ w u hε hC₁ hw hu (η/3) (by linarith)
  obtain ⟨Lx, hx⟩ := x0_term_le ε C₁ w u x hε hC₁ hw hu hux (η/3) (by linarith)
  refine ⟨max (max (max Lh Lg) Lx) (max 1 (4*C₁/(w*ε))), 1, ?_, one_pos, ?_⟩
  · have h1 : (1:ℝ) ≤ max (max (max Lh Lg) Lx) (max 1 (4*C₁/(w*ε))) :=
      le_trans (le_max_left 1 (4*C₁/(w*ε))) (le_max_right _ _)
    linarith
  · intro L β A U B σ M hL hβ1 hβlt hcond hA hU hB hσdef hM hBpos hBA K x₀ hK hx0pos hx0
    rw [max_le_iff] at hL
    obtain ⟨hL', hL4⟩ := hL
    rw [max_le_iff] at hL4
    obtain ⟨hL1, hLε⟩ := hL4
    rw [max_le_iff] at hL'
    obtain ⟨hLlg, hLx0⟩ := hL'
    rw [max_le_iff] at hLlg
    obtain ⟨hLh, hLg⟩ := hLlg
    have hLpos : 0 < L := lt_of_lt_of_le one_pos hL1
    have hσpos : 0 < σ := by rw [hσdef]; linarith
    have hσle : σ ≤ 1 := by rw [hσdef]; linarith
    have hσL : σ*L ≤ (2/3)*Real.log (Real.log L) := by rw [hσdef]; linarith
    simp only [hA, hU, hB] at hK hx0 hBA
    simp only [hA, hU, hB, hM]
    have hden : 2*w*(1-β)*L = w*σ*L := by rw [hσdef]; ring
    rw [hden]
    set t1 : ℝ := (1 + ((1+ε/2)/(w*L) + C₁/(w*L)^2)*(K:ℝ))
      * ((K:ℝ)^(σ-1) * (1 - Real.exp (-(K:ℝ)/(Real.exp (u*L)/L^2)))) with ht1def
    set T2 : ℝ := Real.Gamma σ * ((Real.exp (u*L))^σ - (Real.exp (u*L)/L^2)^σ) with hT2def
    set T3 : ℝ := x₀^(σ-1) * (1 - Real.exp (-x₀/(Real.exp (u*L)/L^2))) with hT3def
    set SS : ℝ := (Real.exp (x*L))^σ - (Real.exp (u*L))^σ with hSSdef
    have hA1 : t1 ≤ η/3 := by rw [ht1def]; exact hh L hLh σ hσpos hσle hσL K hK
    have hA2 : ((1+ε/2)/(w*L) + C₁/(w*L)^2) * T2 ≤ η/3 := by
      rw [hT2def]; exact hg L hLg σ hσpos hσle hσL
    have hA3 : 2 * ((1+ε/2)/(w*L) + C₁/(w*L)^2) * T3 ≤ η/3 := by
      rw [hT3def]; exact hx L hLx0 σ hσpos hσle hσL x₀ hx0pos hx0
    have hS : (x-u)*σ*L ≤ SS := by
      rw [hSSdef]; exact exp_surplus hσpos hLpos hu hux
    have hSnonneg : 0 ≤ SS := by
      have h1 : 0 < x - u := by linarith
      have h2 : 0 < (x-u)*σ*L := by positivity
      linarith [hS, h2]
    have hC1w : C₁/(w*L) ≤ ε/4 := by
      have h1 : 4*C₁/(w*ε) ≤ L := hLε
      rw [div_le_iff₀ (by positivity : (0:ℝ) < w*ε)] at h1
      rw [div_le_iff₀ (by positivity : (0:ℝ) < w*L)]
      linarith
    have hσΓ : σ * Real.Gamma σ ≤ 1 := by
      have h1 := mul_le_mul_of_nonneg_left (gamma_le_inv σ hσpos hσle) hσpos.le
      rwa [mul_div_cancel₀ _ hσpos.ne'] at h1
    have hcg : w*σ*L * (((1+ε/2)/(w*L) + C₁/(w*L)^2) * Real.Gamma σ) ≤ 1 + 3*ε/4 := by
      rw [close_coef_eq w σ L ε C₁ (Real.Gamma σ) hw hLpos]
      have h1 : (1+ε/2)*(σ*Real.Gamma σ) ≤ (1+ε/2)*1 :=
        mul_le_mul_of_nonneg_left hσΓ (by linarith)
      have h2 : (C₁/(w*L))*(σ*Real.Gamma σ) ≤ (ε/4)*1 :=
        mul_le_mul hC1w hσΓ (mul_nonneg hσpos.le (Real.Gamma_pos_of_pos hσpos).le)
          (by linarith)
      linarith [h1, h2]
    have hA4 : w*σ*L*(((1+ε/2)/(w*L) + C₁/(w*L)^2)*(Real.Gamma σ*SS)) ≤ (1+3*ε/4)*SS := by
      have he : w*σ*L*(((1+ε/2)/(w*L) + C₁/(w*L)^2)*(Real.Gamma σ*SS))
          = (w*σ*L*(((1+ε/2)/(w*L) + C₁/(w*L)^2)*Real.Gamma σ))*SS := by ring
      rw [he]
      exact mul_le_mul_of_nonneg_right hcg hSnonneg
    have hηwL : η*(w*σ*L) ≤ (ε/4)*SS := by
      have he : η*(w*σ*L) = (ε/4)*((x-u)*σ*L) := by rw [hηdef]; field_simp
      rw [he]
      exact mul_le_mul_of_nonneg_left hS (by positivity)
    have hsplit : Real.Gamma σ * ((Real.exp (x*L))^σ - (Real.exp (u*L)/L^2)^σ)
        = Real.Gamma σ*SS + T2 := by rw [hSSdef, hT2def]; ring
    have hcore : (t1 + ((1+ε/2)/(w*L) + C₁/(w*L)^2)
          * (Real.Gamma σ * ((Real.exp (x*L))^σ - (Real.exp (u*L)/L^2)^σ) + 2*T3)) * (w*σ*L)
        ≤ (1+ε)*SS + w*σ := by
      have hexp : (t1 + ((1+ε/2)/(w*L) + C₁/(w*L)^2)
            * (Real.Gamma σ * ((Real.exp (x*L))^σ - (Real.exp (u*L)/L^2)^σ) + 2*T3)) * (w*σ*L)
          = w*σ*L*t1
            + w*σ*L*(((1+ε/2)/(w*L) + C₁/(w*L)^2)*(Real.Gamma σ*SS))
            + w*σ*L*(((1+ε/2)/(w*L) + C₁/(w*L)^2)*T2)
            + w*σ*L*(((1+ε/2)/(w*L) + C₁/(w*L)^2)*(2*T3)) := by
        rw [hsplit]; ring
      rw [hexp]
      have hb1 : w*σ*L*t1 ≤ w*σ*L*(η/3) := mul_le_mul_of_nonneg_left hA1 (by positivity)
      have hb2 : w*σ*L*(((1+ε/2)/(w*L) + C₁/(w*L)^2)*T2) ≤ w*σ*L*(η/3) :=
        mul_le_mul_of_nonneg_left hA2 (by positivity)
      have hb3 : w*σ*L*(((1+ε/2)/(w*L) + C₁/(w*L)^2)*(2*T3)) ≤ w*σ*L*(η/3) :=
        mul_le_mul_of_nonneg_left (by linarith [hA3]) (by positivity)
      have hone : (1+3*ε/4)*SS + η*(w*σ*L) ≤ (1+ε)*SS + w*σ := by
        have h6 : 0 ≤ w*σ := by positivity
        linarith [hηwL, h6]
      linarith [hb1, hb2, hb3, hA4, hone]
    have hpos : 0 < w*σ*L := by positivity
    have hsplitdiv : ((1+ε)*SS + w*σ)/(w*σ*L) = (1+ε)*SS/(w*σ*L) + 1/L := by
      field_simp
    rw [← hsplitdiv]
    exact (le_div_iff₀ hpos).mpr hcore

end Work.LinnikAreas2
