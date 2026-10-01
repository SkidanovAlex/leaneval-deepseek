import Mathlib
import Submission.Work.ZeroDensity.LogFree.GramProps
import Submission.Work.ZeroDensity.LogFree.hybridDetector

namespace Work.ZeroDensity.LogFree

open Work.LinnikAreas.Density4

/-- For `0 < t ≤ 1` the geometric-type sum `Σ_{n≥0} e^{-nt}` is at most `4/t`. -/
private lemma expTsumGeomLe {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    ∑' n : ℕ, Real.exp (-((n : ℝ) * t)) ≤ 4 / t := by
  have hnorm : ‖Real.exp (-t)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_lt_one_iff]
    linarith
  have hcongr : (∑' n : ℕ, Real.exp (-((n : ℝ) * t))) = ∑' n : ℕ, Real.exp (-t) ^ n := by
    apply tsum_congr
    intro n
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [hcongr, tsum_geometric_of_norm_lt_one hnorm]
  have hkey : t / 2 ≤ 1 - Real.exp (-t) := by
    have h1 : Real.exp (-t) ≤ 1 / (1 + t) := by
      rw [Real.exp_neg, one_div]
      exact (inv_le_inv₀ (Real.exp_pos t) (by linarith)).mpr (by linarith [Real.add_one_le_exp t])
    have h2 : (1 : ℝ) - 1 / (1 + t) = t / (1 + t) := by
      field_simp
      ring
    have h3 : t / 2 ≤ t / (1 + t) :=
      div_le_div_of_nonneg_left ht0.le (by linarith) (by linarith)
    linarith
  have hpos1 : 0 < 1 - Real.exp (-t) := by linarith [Real.exp_lt_one_iff.mpr (by linarith : -t < 0)]
  calc (1 - Real.exp (-t))⁻¹ ≤ (t / 2)⁻¹ := (inv_le_inv₀ hpos1 (by linarith)).mpr hkey
    _ = 2 / t := by rw [inv_div]
    _ ≤ 4 / t := div_le_div_of_nonneg_right (by norm_num) ht0.le

/-- `n² e^{-n/(2X)} ≤ 64 X² e^{-n/(4X)}` for every `X > 0` and `n : ℕ`. -/
private lemma sqMulExpLe {X : ℝ} (hX : 0 < X) (n : ℕ) :
    (n : ℝ) ^ 2 * Real.exp (-((n : ℝ) / (2 * X))) ≤
      64 * X ^ 2 * Real.exp (-((n : ℝ) / (4 * X))) := by
  set y : ℝ := (n : ℝ) / (4 * X) with hy
  have hy0 : 0 ≤ y := by rw [hy]; positivity
  have hmul : y * Real.exp (-(y / 2)) ≤ 2 * Real.exp (-1) := by
    have := Real.mul_exp_neg_le_exp_neg_one (y / 2)
    linarith
  have hmul0 : 0 ≤ y * Real.exp (-(y / 2)) := by positivity
  have hsq : (y * Real.exp (-(y / 2))) ^ 2 ≤ (2 * Real.exp (-1)) ^ 2 :=
    pow_le_pow_left₀ hmul0 hmul 2
  have h3 : (y * Real.exp (-(y / 2))) ^ 2 = y ^ 2 * Real.exp (-y) := by
    have hh : Real.exp (-(y / 2)) ^ 2 = Real.exp (-y) := by
      rw [sq, ← Real.exp_add]
      congr 1
      ring
    rw [mul_pow, hh]
  have h4 : (2 * Real.exp (-1)) ^ 2 = 4 * Real.exp (-2) := by
    have hh : Real.exp (-1) ^ 2 = Real.exp (-2) := by
      rw [sq, ← Real.exp_add]
      norm_num
    rw [mul_pow, hh]
    norm_num
  rw [h3, h4] at hsq
  have hkey : y ^ 2 * Real.exp (-y) ≤ 4 := by
    have h5 : Real.exp (-2) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
    linarith
  have hexp : Real.exp (-y) * Real.exp (-y) = Real.exp (-(2 * y)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hkey' : y ^ 2 * Real.exp (-(2 * y)) ≤ 4 * Real.exp (-y) := by
    have h := mul_le_mul_of_nonneg_right hkey (Real.exp_pos (-y)).le
    rwa [mul_assoc, hexp] at h
  have haux : (4 * y) ^ 2 * Real.exp (-(2 * y)) ≤ 64 * Real.exp (-y) := by
    calc (4 * y) ^ 2 * Real.exp (-(2 * y)) = 16 * (y ^ 2 * Real.exp (-(2 * y))) := by ring
      _ ≤ 16 * (4 * Real.exp (-y)) := mul_le_mul_of_nonneg_left hkey' (by norm_num)
      _ = 64 * Real.exp (-y) := by ring
  have hy_eq : (n : ℝ) = 4 * X * y := by
    rw [hy]
    field_simp
  have hdiv1 : (n : ℝ) / (2 * X) = 2 * y := by
    rw [hy_eq]
    field_simp
    ring
  calc (n : ℝ) ^ 2 * Real.exp (-((n : ℝ) / (2 * X)))
      = X ^ 2 * ((4 * y) ^ 2 * Real.exp (-(2 * y))) := by rw [hdiv1, hy_eq]; ring
    _ ≤ X ^ 2 * (64 * Real.exp (-y)) :=
        mul_le_mul_of_nonneg_left haux (by positivity)
    _ = 64 * X ^ 2 * Real.exp (-((n : ℝ) / (4 * X))) := by rw [← hy]; ring

/-- For `a, b > 0`, the function `L ↦ e^{aL - bL^{10}}` is eventually at most `1/L`. -/
private lemma expPolyDecayLe {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ L : ℝ, L₀ ≤ L → Real.exp (a * L - b * L ^ 10) ≤ 1 / L := by
  refine ⟨max 1 ((a + 1) / b + 1), le_max_left _ _, ?_⟩
  intro L hL
  have hL1 : 1 ≤ L := le_trans (le_max_left _ _) hL
  have hLpos : 0 < L := by linarith
  have hL9 : (a + 1) / b ≤ L ^ 9 := by
    have h2 : (a + 1) / b ≤ L := by
      have := le_trans (le_max_right _ _) hL
      linarith
    calc (a + 1) / b ≤ L := h2
      _ = L ^ 1 := by ring
      _ ≤ L ^ 9 := pow_le_pow_right₀ hL1 (by norm_num)
  have h1 : a + 1 ≤ b * L ^ 9 := by
    have h := mul_le_mul_of_nonneg_left hL9 hb.le
    have hbc : b * ((a + 1) / b) = a + 1 := by field_simp
    rwa [hbc] at h
  have h2 : Real.log L ≤ L := by
    have := Real.log_le_sub_one_of_pos hLpos
    linarith
  have hkey : a * L + Real.log L ≤ b * L ^ 10 := by
    calc a * L + Real.log L ≤ a * L + L := by linarith
      _ = (a + 1) * L := by ring
      _ ≤ (b * L ^ 9) * L := mul_le_mul_of_nonneg_right h1 hLpos.le
      _ = b * L ^ 10 := by ring
  have : a * L - b * L ^ 10 ≤ -Real.log L := by linarith
  calc Real.exp (a * L - b * L ^ 10) ≤ Real.exp (-Real.log L) := Real.exp_le_exp.mpr this
    _ = 1 / L := by rw [Real.exp_neg, Real.exp_log hLpos, one_div]

/-- The damping factor `g(n) = e^{-n/X} - e^{-n/U'}` is dominated by `2 e^{-n/X}` when
`0 < U' ≤ X`. -/
private lemma absGfunLe (X U' : ℝ) (hX : 0 < X) (hU' : 0 < U') (hle : U' ≤ X) (n : ℕ) :
    |gfun X U' n| ≤ 2 * Real.exp (-((n : ℝ) / X)) := by
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hcmp : (n : ℝ) / X ≤ (n : ℝ) / U' :=
    div_le_div_of_nonneg_left hn hU' hle
  have h2 : Real.exp (-((n : ℝ) / U')) ≤ Real.exp (-((n : ℝ) / X)) :=
    Real.exp_le_exp.mpr (by linarith)
  rw [gfun]
  have hnn : 0 ≤ Real.exp (-((n : ℝ) / X)) - Real.exp (-((n : ℝ) / U')) := by linarith
  rw [abs_of_nonneg hnn]
  have h3 : Real.exp (-((n : ℝ) / X)) - Real.exp (-((n : ℝ) / U')) ≤ Real.exp (-((n : ℝ) / X)) := by
    have := Real.exp_pos (-((n : ℝ) / U'))
    linarith
  have h4 : Real.exp (-((n : ℝ) / X)) ≤ 2 * Real.exp (-((n : ℝ) / X)) := by
    have := Real.exp_pos (-((n : ℝ) / X))
    linarith
  linarith

/-- For `0 ≤ ρ.re` the complex power `n^{-ρ}` has modulus at most one (`n ≥ 1`). -/
private lemma normCpowNatLeOne {n : ℕ} (hn : 0 < n) {ρ : ℂ} (hρ : 0 ≤ ρ.re) :
    ‖(n : ℂ) ^ (-ρ)‖ ≤ 1 := by
  rw [Complex.norm_natCast_cpow_of_pos hn, Complex.neg_re]
  exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hn) (by linarith)

/-- `gfun X (U/L²) n = e^{-n/X} - e^{-nL²/U}`. -/
private lemma gfun_div_eq (X U L : ℝ) (hU : U ≠ 0) (hL : L ≠ 0) (n : ℕ) :
    gfun X (U / L ^ 2) n = Real.exp (-((n : ℝ) / X)) - Real.exp (-((n : ℝ) * L ^ 2 / U)) := by
  rw [gfun]
  have h : (n : ℝ) / (U / L ^ 2) = (n : ℝ) * L ^ 2 / U := by
    field_simp
  rw [h]

/-- The damping factor of `detSum` in terms of `gfun`: `e^{-n/X} - e^{-nL²/U} = gfun X (U/L²) n`. -/
private lemma exp_sub_eq_gfun (X U L : ℝ) (hU : U ≠ 0) (hL : L ≠ 0) (n : ℕ) :
    Real.exp (-(n : ℝ) / X) - Real.exp (-(n : ℝ) * L ^ 2 / U) = gfun X (U / L ^ 2) n := by
  rw [gfun_div_eq X U L hU hL n]
  congr 1
  · congr 1
    ring
  · congr 1
    ring

/-- The common detector coefficient is polynomially bounded by `n²` when `0 ≤ ρ.re`. -/
private lemma norm_detCoeff_le_sq {q : ℕ} [NeZero q] (U V W : ℝ) (χ : DirichletCharacter ℂ q) (ρ : ℂ)
    (hU : 0 < U) (hρ : 0 ≤ ρ.re) (n : ℕ) :
    ‖Work.LinnikAreas.Density4.detCoeff q U V W χ ρ n‖ ≤ (n : ℝ) ^ 2 := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    rw [Work.LinnikAreas.Density4.detCoeff, Work.LinnikAreas.Density4.psiS_zero]
    simp
  · rw [Work.LinnikAreas.Density4.detCoeff, norm_mul, norm_mul, norm_mul]
    have h1 : ‖((Work.LinnikAreas.Density4.psiS U V n : ℝ) : ℂ)‖ ≤ (n : ℝ) := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact Work.LinnikAreas.Density4.abs_psiS_le hU n
    have h2 : ‖((Work.LinnikAreas.Density4.thetaS W n : ℝ) : ℂ)‖ ≤ (n : ℝ) := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact Work.LinnikAreas.Density4.abs_thetaS_le W n
    have h3 : ‖χ (n : ZMod q)‖ ≤ 1 := DirichletCharacter.norm_le_one χ _
    have h4 : ‖((n : ℂ) ^ (-ρ))‖ ≤ 1 := normCpowNatLeOne hn hρ
    calc ‖((Work.LinnikAreas.Density4.psiS U V n : ℝ) : ℂ)‖
            * ‖((Work.LinnikAreas.Density4.thetaS W n : ℝ) : ℂ)‖
            * ‖χ (n : ZMod q)‖ * ‖((n : ℂ) ^ (-ρ))‖
        ≤ (n : ℝ) * (n : ℝ) * 1 * 1 := by
          gcongr
      _ = (n : ℝ) ^ 2 := by ring

/-- The exponential factor of the `i`-th shifted detector term splits as
`e^{-a/X} ≤ e^{-K/(2X)} e^{-a/(2X)}` for `a = i + K`. -/
private lemma shiftTermLe (X : ℝ) (hX : 0 < X) (K i : ℕ) :
    2 * ((i + K : ℕ) : ℝ) ^ 2 * Real.exp (-(((i + K : ℕ) : ℝ) / X))
      ≤ 2 * Real.exp (-((K : ℝ) / (2 * X)))
          * (((i + K : ℕ) : ℝ) ^ 2 * Real.exp (-(((i + K : ℕ) : ℝ) / (2 * X)))) := by
  have hX0 : (0 : ℝ) ≤ 2 * X := by positivity
  have hKa : (K : ℝ) ≤ ((i + K : ℕ) : ℝ) := by
    exact_mod_cast Nat.le_add_left K i
  have h1 : Real.exp (-(((i + K : ℕ) : ℝ) / X))
      ≤ Real.exp (-((K : ℝ) / (2 * X))) * Real.exp (-(((i + K : ℕ) : ℝ) / (2 * X))) := by
    have hdec : Real.exp (-(((i + K : ℕ) : ℝ) / X))
        = Real.exp (-(((i + K : ℕ) : ℝ) / (2 * X)))
          * Real.exp (-(((i + K : ℕ) : ℝ) / (2 * X))) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hdec]
    have hle : Real.exp (-(((i + K : ℕ) : ℝ) / (2 * X)))
        ≤ Real.exp (-((K : ℝ) / (2 * X))) := by
      apply Real.exp_le_exp.mpr
      apply neg_le_neg
      exact div_le_div_of_nonneg_right hKa hX0
    exact mul_le_mul_of_nonneg_right hle (Real.exp_pos _).le
  have hnonneg : (0 : ℝ) ≤ 2 * ((i + K : ℕ) : ℝ) ^ 2 := by positivity
  calc 2 * ((i + K : ℕ) : ℝ) ^ 2 * Real.exp (-(((i + K : ℕ) : ℝ) / X))
      ≤ 2 * ((i + K : ℕ) : ℝ) ^ 2
          * (Real.exp (-((K : ℝ) / (2 * X)))
              * Real.exp (-(((i + K : ℕ) : ℝ) / (2 * X)))) :=
        mul_le_mul_of_nonneg_left h1 hnonneg
    _ = 2 * Real.exp (-((K : ℝ) / (2 * X)))
          * (((i + K : ℕ) : ℝ) ^ 2 * Real.exp (-(((i + K : ℕ) : ℝ) / (2 * X)))) := by ring

/-- The summand of the truncated detector at the parameters of `p`. -/
private noncomputable def detTruncTerm (q : ℕ) [NeZero q] (U V W X L : ℝ) (χ : DirichletCharacter ℂ q)
    (ρ : ℂ) (n : ℕ) : ℂ :=
  Work.LinnikAreas.Density4.detCoeff q U V W χ ρ n
    * ((Real.exp (-(n : ℝ) / X) - Real.exp (-(n : ℝ) * L ^ 2 / U) : ℝ) : ℂ)

/-- The tail of the Heath-Brown detector past `⌈X 𝓛^10⌉`. `Work.ZeroDensity.LogFree.DetectorTruncation p` (defined in `Submission/Work/ZeroDensity/LogFree/GramProps.lean`): for `D = scale q T ≥ D0`, a non-principal character and a zero, the difference between the infinite detector sum `Density4.detSum q U V W X L chi rho` and its truncation at `N ≥ ⌈X L^10⌉` is at most `C/L`. Route: `detSum`'s summand is `psiSum(n)*thetaS(n)*chi(n)*n^{-rho}*g(n)` with `|psiSum(n)| <= d(n)`, `|thetaS(n)| <= d(n)`, `|n^{-rho}| = n^{-Re rho} <= n^{-sigma0}` and `g(n) = e^{-n/X} - e^{-n/U'} <= e^{-n/X}`; bound `d(n)^2 n^{-sigma0} e^{-n/X} <= C_ε n^{ε} e^{-n/(2X)}` (any `ε > 0`), sum the tail `n > N` geometrically against `e^{-n/(2X)}`, and use `N >= X L^10` to get `e^{-N/(2X)} <= e^{-L^10/2}`, which is `O(1/L)`. -/
theorem detectorTruncation (p : Work.ZeroDensity.LogFree.Params) :
    Work.ZeroDensity.LogFree.DetectorTruncation p := by
  have hxpos : 0 < p.x := by linarith [p.hw, p.hwu, p.huv, p.hvx]
  obtain ⟨L₀, hL₀1, hL₀⟩ :=
    expPolyDecayLe (a := 3 * p.x) (b := (1 : ℝ) / 2) (by linarith) (by norm_num)
  refine ⟨2049, by norm_num, Real.exp L₀, Real.exp_pos L₀, ?_⟩
  intro q hq _inst T hT hD χ ρ hχ hz hσ₀ hρ1 hρT N hN
  set D : ℝ := scale q T with hDdef
  set L : ℝ := Lscale q T with hLdef
  set U : ℝ := Dpow q T p.u with hUdef
  set V : ℝ := Dpow q T p.v with hVdef
  set W : ℝ := Dpow q T p.w with hWdef
  set X : ℝ := Dpow q T p.x with hXdef
  have hDpos : 0 < D := by rw [hDdef, scale]; positivity
  have hD6 : 6 ≤ D := by
    rw [hDdef, scale]
    have hq2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    nlinarith
  have hD1 : 1 ≤ D := by linarith
  have hDgt1 : 1 < D := by linarith
  have hLeq : L = Real.log D := by rw [hLdef, Lscale, ← hDdef]
  have hLpos : 0 < L := by rw [hLeq]; exact Real.log_pos hDgt1
  have hLne : L ≠ 0 := ne_of_gt hLpos
  have hL1 : 1 ≤ L := by
    rw [hLeq, ← Real.log_exp 1]
    refine Real.log_le_log (Real.exp_pos 1) ?_
    have h3 := Real.exp_one_lt_three
    linarith
  have hLL₀ : L₀ ≤ L := by
    rw [hLeq, ← Real.log_exp L₀]
    refine Real.log_le_log (Real.exp_pos L₀) ?_
    rw [hDdef]
    exact hD
  have hUeq : U = D ^ p.u := by rw [hUdef, Dpow, ← hDdef]
  have hVeq : V = D ^ p.v := by rw [hVdef, Dpow, ← hDdef]
  have hWeq : W = D ^ p.w := by rw [hWdef, Dpow, ← hDdef]
  have hXeq : X = D ^ p.x := by rw [hXdef, Dpow, ← hDdef]
  have hUpos : 0 < U := by rw [hUeq]; exact Real.rpow_pos_of_pos hDpos _
  have hVpos : 0 < V := by rw [hVeq]; exact Real.rpow_pos_of_pos hDpos _
  have hWpos : 0 < W := by rw [hWeq]; exact Real.rpow_pos_of_pos hDpos _
  have hXpos : 0 < X := by rw [hXeq]; exact Real.rpow_pos_of_pos hDpos _
  have hX1 : 1 ≤ X := by rw [hXeq]; exact Real.one_le_rpow hD1 hxpos.le
  have hUV : U < V := by
    rw [hUeq, hVeq]
    exact Real.rpow_lt_rpow_of_exponent_lt hDgt1 p.huv
  have hW1 : 1 < W := by rw [hWeq]; exact Real.one_lt_rpow hDgt1 p.hw
  have hUleX : U ≤ X := by
    rw [hUeq, hXeq]
    exact Real.rpow_le_rpow_of_exponent_le hD1 (by linarith [p.hwu, p.huv, p.hvx])
  have hL2pos : 0 < L ^ 2 := pow_pos hLpos 2
  have hL2one : 1 ≤ L ^ 2 := by nlinarith
  have hUp : 0 < U / L ^ 2 := div_pos hUpos hL2pos
  have hUpX : U / L ^ 2 ≤ X := by
    rw [div_le_iff₀ hL2pos]
    nlinarith [hUleX, hL2one, hXpos]
  have hρ0 : 0 ≤ ρ.re := by
    have h0 : (0 : ℝ) < p.σ₀ := by linarith [p.hσ₀]
    linarith
  -- the summand of the statement is the summand of `detSum`
  have hpsi : ∀ n : ℕ, psiSum U V n = Work.LinnikAreas.Density4.psiS U V n := fun n => rfl
  have hth : ∀ n : ℕ, thetaS W n = Work.LinnikAreas.Density4.thetaS W n := fun n => rfl
  have hsterm : ∀ n : ℕ,
      ((psiSum U V n : ℝ) : ℂ) * ((thetaS W n : ℝ) : ℂ) * χ (n : ZMod q) * ((n : ℂ) ^ (-ρ))
        * (((gfun X (U / L ^ 2) n : ℝ) : ℂ)) = detTruncTerm q U V W X L χ ρ n := by
    intro n
    rw [hpsi n, hth n, ← exp_sub_eq_gfun X U L (ne_of_gt hUpos) hLne n, detTruncTerm,
      Work.LinnikAreas.Density4.detCoeff]
  have hdet : Work.LinnikAreas.Density4.detSum q U V W X L χ ρ
      = ∑' n : ℕ, detTruncTerm q U V W X L χ ρ n := by
    rw [Work.LinnikAreas.Density4.detSum]
    apply tsum_congr
    intro n
    simp only [detTruncTerm, Work.LinnikAreas.Density4.detCoeff,
      Work.LinnikAreas.Density4.psiS, Work.LinnikAreas.Density4.thetaS]
  -- summability
  have hsm1 : Summable (fun n : ℕ => Work.LinnikAreas.Density4.detCoeff q U V W χ ρ n
      * ((Real.exp (-(n : ℝ) / X) : ℝ) : ℂ)) := by
    have hXt : 0 < (1 : ℝ) / X := div_pos one_pos hXpos
    have h := Work.LinnikAreas.Density4.summable_detCoeff_mul_exp (q := q) U V W χ ρ
      (t := 1 / X) hUpos hXt
    simpa [div_eq_mul_inv] using h
  have hsm2 : Summable (fun n : ℕ => Work.LinnikAreas.Density4.detCoeff q U V W χ ρ n
      * ((Real.exp (-(n : ℝ) * L ^ 2 / U) : ℝ) : ℂ)) := by
    have h := Work.LinnikAreas.Density4.summable_detCoeff_mul_exp (q := q) U V W χ ρ
      (t := L ^ 2 / U) hUpos (div_pos (pow_pos hLpos 2) hUpos)
    simpa only [div_eq_mul_inv, mul_assoc] using h
  have hsumm : Summable (detTruncTerm q U V W X L χ ρ) := by
    refine (hsm1.sub hsm2).congr ?_
    intro n
    simp only [Pi.sub_apply, detTruncTerm, Work.LinnikAreas.Density4.detCoeff,
      Complex.ofReal_sub]
    ring
  -- the partial sum is a initial segment of the series
  have h0term : detTruncTerm q U V W X L χ ρ 0 = 0 := by
    rw [detTruncTerm, Work.LinnikAreas.Density4.detCoeff, Work.LinnikAreas.Density4.psiS_zero]
    simp
  have hsumK : (∑ n ∈ Finset.Icc 1 N, detTruncTerm q U V W X L χ ρ n)
      = ∑ i ∈ Finset.range (N + 1), detTruncTerm q U V W X L χ ρ i := by
    have hset : Finset.range (N + 1) = insert 0 (Finset.Icc 1 N) := by
      ext i
      simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
      omega
    rw [hset, Finset.sum_insert (by simp), h0term, zero_add]
  have hsplit := hsumm.sum_add_tsum_nat_add (N + 1)
  have hdiff : (∑ n ∈ Finset.Icc 1 N, detTruncTerm q U V W X L χ ρ n)
      - (∑' n : ℕ, detTruncTerm q U V W X L χ ρ n)
      = -(∑' i : ℕ, detTruncTerm q U V W X L χ ρ (i + (N + 1))) := by
    rw [hsumK, ← hsplit]
    ring
  rw [Finset.sum_congr rfl (fun n (_ : n ∈ Finset.Icc 1 N) => hsterm n), hdet, hdiff, norm_neg]
  -- the height condition
  have hKge : X * L ^ 10 ≤ ((N + 1 : ℕ) : ℝ) := by
    have h1 : X * L ^ 10 ≤ ((⌈X * L ^ 10⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
    have hN' : ⌈X * L ^ 10⌉₊ ≤ N := by
      have heq : Dpow q T p.x * (Lscale q T) ^ 10 = X * L ^ 10 := by
        rw [← hXdef, ← hLdef]
      rwa [heq] at hN
    have h2 : ((⌈X * L ^ 10⌉₊ : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN'
    have h3 : (N : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by push_cast; linarith
    linarith
  -- summability of the majorants
  have hsqsumm : Summable (fun m : ℕ => (m : ℝ) ^ 2 * Real.exp (-((m : ℝ) / X))) := by
    have h := Real.summable_pow_mul_exp_neg_nat_mul 2 (show 0 < (1 : ℝ) / X by positivity)
    refine h.congr (fun m => ?_)
    have harg : -((1 : ℝ) / X) * (m : ℝ) = -((m : ℝ) / X) := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      ring
    rw [harg]
  have hsqsumm2 : Summable (fun m : ℕ => (m : ℝ) ^ 2 * Real.exp (-((m : ℝ) / (2 * X)))) := by
    have h := Real.summable_pow_mul_exp_neg_nat_mul 2 (show 0 < (1 : ℝ) / (2 * X) by positivity)
    refine h.congr (fun m => ?_)
    have harg : -((1 : ℝ) / (2 * X)) * (m : ℝ) = -((m : ℝ) / (2 * X)) := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      ring
    rw [harg]
  have hgeomsumm : Summable (fun m : ℕ => Real.exp (-((m : ℝ) / (4 * X)))) := by
    have h := Real.summable_pow_mul_exp_neg_nat_mul 0 (show 0 < (1 : ℝ) / (4 * X) by positivity)
    refine h.congr (fun m => ?_)
    have harg : -((1 : ℝ) / (4 * X)) * (m : ℝ) = -((m : ℝ) / (4 * X)) := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      ring
    rw [harg, pow_zero, one_mul]
  have hSs : Summable (fun m : ℕ => 64 * X ^ 2 * Real.exp (-((m : ℝ) / (4 * X)))) :=
    hgeomsumm.mul_left _
  -- the full quadratic-exponential sum
  have hsq_sum : ∑' m : ℕ, (m : ℝ) ^ 2 * Real.exp (-((m : ℝ) / (2 * X))) ≤ 1024 * X ^ 3 := by
    have ht1 : (1 : ℝ) / (4 * X) ≤ 1 := by
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < 4 * X)]
      linarith
    have hgexp := expTsumGeomLe (show 0 < (1 : ℝ) / (4 * X) by positivity) ht1
    calc ∑' m : ℕ, (m : ℝ) ^ 2 * Real.exp (-((m : ℝ) / (2 * X)))
        ≤ ∑' m : ℕ, 64 * X ^ 2 * Real.exp (-((m : ℝ) / (4 * X))) :=
          Summable.tsum_le_tsum (fun m => sqMulExpLe hXpos m) hsqsumm2 hSs
      _ = 64 * X ^ 2 * ∑' m : ℕ, Real.exp (-((m : ℝ) / (4 * X))) := tsum_mul_left
      _ = 64 * X ^ 2 * ∑' m : ℕ, Real.exp (-((m : ℝ) * (1 / (4 * X)))) := by
          rw [tsum_congr (fun m => by
            have harg : -((m : ℝ) / (4 * X)) = -((m : ℝ) * (1 / (4 * X))) := by
              rw [div_eq_mul_inv, div_eq_mul_inv]
              ring
            rw [harg])]
      _ ≤ 64 * X ^ 2 * (4 / (1 / (4 * X))) :=
          mul_le_mul_of_nonneg_left hgexp (by positivity)
      _ = 1024 * X ^ 3 := by
          field_simp
          ring
  -- the shifted tail
  have hshiftS : Summable (fun i : ℕ => ((i + (N + 1) : ℕ) : ℝ) ^ 2
      * Real.exp (-(((i + (N + 1) : ℕ) : ℝ) / (2 * X)))) :=
    (summable_nat_add_iff (N + 1) (f := fun m : ℕ =>
      (m : ℝ) ^ 2 * Real.exp (-((m : ℝ) / (2 * X))))).mpr hsqsumm2
  have hMsumm : Summable (fun i : ℕ => 2 * Real.exp (-(((N + 1 : ℕ) : ℝ) / (2 * X)))
      * (((i + (N + 1) : ℕ) : ℝ) ^ 2
          * Real.exp (-(((i + (N + 1) : ℕ) : ℝ) / (2 * X))))) :=
    hshiftS.mul_left _
  have hnorm : ∀ m : ℕ, ‖detTruncTerm q U V W X L χ ρ m‖
      ≤ 2 * (m : ℝ) ^ 2 * Real.exp (-((m : ℝ) / X)) := by
    intro m
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm
      rw [detTruncTerm, Work.LinnikAreas.Density4.detCoeff, Work.LinnikAreas.Density4.psiS_zero]
      simp
    · have hdc := norm_detCoeff_le_sq U V W χ ρ hUpos hρ0 m
      have hg := absGfunLe X (U / L ^ 2) hXpos hUp hUpX m
      rw [detTruncTerm, exp_sub_eq_gfun X U L (ne_of_gt hUpos) hLne m]
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      calc ‖Work.LinnikAreas.Density4.detCoeff q U V W χ ρ m‖ * |gfun X (U / L ^ 2) m|
          ≤ (m : ℝ) ^ 2 * (2 * Real.exp (-((m : ℝ) / X))) :=
            mul_le_mul hdc hg (abs_nonneg _) (by positivity)
        _ = 2 * (m : ℝ) ^ 2 * Real.exp (-((m : ℝ) / X)) := by ring
  have hpoint : ∀ i : ℕ, ‖detTruncTerm q U V W X L χ ρ (i + (N + 1))‖
      ≤ 2 * Real.exp (-(((N + 1 : ℕ) : ℝ) / (2 * X)))
          * (((i + (N + 1) : ℕ) : ℝ) ^ 2
              * Real.exp (-(((i + (N + 1) : ℕ) : ℝ) / (2 * X)))) := by
    intro i
    refine le_trans (hnorm (i + (N + 1))) ?_
    exact shiftTermLe X hXpos (N + 1) i
  have hnormsumm : Summable (fun i : ℕ => ‖detTruncTerm q U V W X L χ ρ (i + (N + 1))‖) :=
    (Summable.of_norm_bounded hMsumm hpoint).norm
  have htailbound : ∑' i : ℕ, ‖detTruncTerm q U V W X L χ ρ (i + (N + 1))‖
      ≤ 2048 * X ^ 3 * Real.exp (-(L ^ 10) / 2) := by
    calc ∑' i : ℕ, ‖detTruncTerm q U V W X L χ ρ (i + (N + 1))‖
        ≤ ∑' i : ℕ, 2 * Real.exp (-(((N + 1 : ℕ) : ℝ) / (2 * X)))
            * (((i + (N + 1) : ℕ) : ℝ) ^ 2
                * Real.exp (-(((i + (N + 1) : ℕ) : ℝ) / (2 * X)))) :=
          Summable.tsum_le_tsum hpoint hnormsumm hMsumm
      _ = 2 * Real.exp (-(((N + 1 : ℕ) : ℝ) / (2 * X)))
            * ∑' i : ℕ, (((i + (N + 1) : ℕ) : ℝ) ^ 2
                * Real.exp (-(((i + (N + 1) : ℕ) : ℝ) / (2 * X)))) := tsum_mul_left
      _ ≤ 2 * Real.exp (-(((N + 1 : ℕ) : ℝ) / (2 * X)))
            * ∑' m : ℕ, (m : ℝ) ^ 2 * Real.exp (-((m : ℝ) / (2 * X))) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have hsp := hsqsumm2.sum_add_tsum_nat_add (N + 1)
          have hnn : 0 ≤ ∑ m ∈ Finset.range (N + 1),
              (m : ℝ) ^ 2 * Real.exp (-((m : ℝ) / (2 * X))) :=
            Finset.sum_nonneg (fun m _ => by positivity)
          rw [← hsp]
          exact le_add_of_nonneg_left hnn
      _ ≤ 2 * Real.exp (-(L ^ 10 / 2)) * (1024 * X ^ 3) := by
          have h1 : 2 * Real.exp (-(((N + 1 : ℕ) : ℝ) / (2 * X)))
              ≤ 2 * Real.exp (-(L ^ 10 / 2)) := by
            apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
            apply Real.exp_le_exp.mpr
            have hKdiv : L ^ 10 ≤ ((N + 1 : ℕ) : ℝ) / X := by
              rw [le_div_iff₀ hXpos]
              simpa only [mul_comm] using hKge
            have h2 : L ^ 10 / 2 ≤ ((N + 1 : ℕ) : ℝ) / (2 * X) := by
              rw [show ((N + 1 : ℕ) : ℝ) / (2 * X) = (((N + 1 : ℕ) : ℝ) / X) / 2 by ring]
              linarith
            linarith
          exact mul_le_mul h1 hsq_sum (by positivity) (by positivity)
      _ = 2048 * X ^ 3 * Real.exp (-(L ^ 10) / 2) := by
          have he : Real.exp (-(L ^ 10 / 2)) = Real.exp (-(L ^ 10) / 2) := by
            congr 1
            ring
          rw [he]
          ring
  -- final constants
  have hfinal : 2048 * X ^ 3 * Real.exp (-(L ^ 10) / 2) ≤ 2049 / L := by
    have hXe : X = Real.exp (p.x * L) := by
      rw [hXeq, Real.rpow_def_of_pos hDpos]
      congr 1
      rw [hLeq]
      ring
    have h3 : X ^ 3 = Real.exp (3 * (p.x * L)) := by
      rw [hXe, ← Real.exp_nat_mul]
      norm_num
    have hA : X ^ 3 * Real.exp (-(L ^ 10) / 2)
        = Real.exp (3 * p.x * L - (1 / 2) * L ^ 10) := by
      rw [h3, ← Real.exp_add]
      congr 1
      ring
    have hb := hL₀ L hLL₀
    calc 2048 * X ^ 3 * Real.exp (-(L ^ 10) / 2)
        = 2048 * (X ^ 3 * Real.exp (-(L ^ 10) / 2)) := by ring
      _ = 2048 * Real.exp (3 * p.x * L - (1 / 2) * L ^ 10) := by rw [hA]
      _ ≤ 2048 * (1 / L) := mul_le_mul_of_nonneg_left hb (by norm_num)
      _ ≤ 2049 / L := by
          rw [mul_one_div]
          exact div_le_div_of_nonneg_right (by norm_num) hLpos.le
  calc ‖∑' i : ℕ, detTruncTerm q U V W X L χ ρ (i + (N + 1))‖
      ≤ ∑' i : ℕ, ‖detTruncTerm q U V W X L χ ρ (i + (N + 1))‖ :=
        norm_tsum_le_tsum_norm hnormsumm
    _ ≤ 2048 * X ^ 3 * Real.exp (-(L ^ 10) / 2) := htailbound
    _ ≤ 2049 / L := hfinal

end Work.ZeroDensity.LogFree
