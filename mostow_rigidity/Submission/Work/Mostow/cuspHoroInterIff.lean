import Mathlib
import Submission.Work.Mostow.QIDefs
import Submission.Work.Mostow.geomFiniteDefs
import Submission.Work.Mostow.BaryBase

/-!
# Intersection of two horoballs at distinct boundary points

For `ξ ≠ η` on the boundary sphere `Sph n` and levels `t, t'`, the two open horoballs
`busemann ξ · < t` and `busemann η · < t'` have a common point exactly when
`exp (t + t') > (1 - ⟪ξ,η⟫)/2`.

We write `lev ξ u = tpart u - ⟪u,ξ⟫ = exp (busemann ξ u)`, so the two conditions
`busemann ξ u < t`, `busemann η u < t'` are `lev ξ u < exp t`, `lev η u < exp t'`.  The two
halves of the equivalence are separated:

* `horoProdGe_aux`: for every `u`, `lev ξ u * lev η u ≥ (1 - ⟪ξ,η⟫)/2` — the product of the
  two levels dominates the critical constant (via the `3 × 3` Gram determinant).
* `horoAttain`: conversely, when `X * Y = (1 - ⟪ξ,η⟫)/2` with `X,Y > 0`, the explicit point
  `u = (Y/(1-⟪ξ,η⟫)) • ξ + (X/(1-⟪ξ,η⟫)) • η` realises both levels.
-/

namespace Work.Mostow

open Submission.Mostow

/-- If `ξ,η` are unit vectors with `⟪ξ,η⟫ = -1` then `η = -ξ`. -/
private lemma neg_of_inner_eq_neg_one {n : ℕ} {ξ η : E n} (hξ : ‖ξ‖ = 1) (hη : ‖η‖ = 1)
    (h : inner ℝ ξ η = -1) : η = -ξ := by
  have h2 : ‖ξ + η‖ ^ 2 = 0 := by
    rw [norm_add_sq_real, hξ, hη]; nlinarith [h]
  have h3 : ξ + η = 0 := by
    have := sq_eq_zero_iff.mp h2
    exact norm_eq_zero.mp this
  exact eq_neg_of_add_eq_zero_right h3

/-- The `3 × 3` Gram determinant inequality behind the product bound:
`(⟪u,ξ⟫)² - 2⟪ξ,η⟫⟪u,ξ⟫⟪u,η⟫ + (⟪u,η⟫)² ≤ (1 - ⟪ξ,η⟫²)‖u‖²`. -/
private lemma gram_bound (n : ℕ) (ξ η u : E n) (hξ : ξ ∈ Sph n) (hη : η ∈ Sph n) :
    (inner ℝ u ξ)^2 - 2*(inner ℝ ξ η)*(inner ℝ u ξ)*(inner ℝ u η) + (inner ℝ u η)^2
      ≤ (1 - (inner ℝ ξ η)^2) * ‖u‖^2 := by
  have hξn : ‖ξ‖ = 1 := (mem_Sph_iff ξ).mp hξ
  have hηn : ‖η‖ = 1 := (mem_Sph_iff η).mp hη
  have hξ2 : inner ℝ ξ ξ = 1 := by rw [real_inner_self_eq_norm_sq, hξn]; norm_num
  have hη2 : inner ℝ η η = 1 := by rw [real_inner_self_eq_norm_sq, hηn]; norm_num
  have huu : inner ℝ u u = ‖u‖^2 := real_inner_self_eq_norm_sq u
  have hηξ : inner ℝ η ξ = inner ℝ ξ η := (real_inner_comm η ξ).symm
  have hξu : inner ℝ ξ u = inner ℝ u ξ := (real_inner_comm ξ u).symm
  have hηu : inner ℝ η u = inner ℝ u η := (real_inner_comm η u).symm
  let v : Fin 3 → E n := ![ξ, η, u]
  have hdet : 0 ≤ (Matrix.gram ℝ v).det := (Matrix.posSemidef_gram ℝ v).det_nonneg
  have hval : (Matrix.gram ℝ v).det =
      (1 - (inner ℝ ξ η)^2) * ‖u‖^2
        - ((inner ℝ u ξ)^2 - 2*(inner ℝ ξ η)*(inner ℝ u ξ)*(inner ℝ u η) + (inner ℝ u η)^2) := by
    show (Matrix.gram ℝ ![ξ, η, u]).det = _
    rw [Matrix.det_fin_three]
    simp only [Matrix.gram_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, hξ2, hη2, huu, hηξ, hξu, hηu]
    ring
  linarith [hdet, hval]

set_option maxHeartbeats 800000 in
/-- Product lower bound for the exponential Busemann levels: for unit `ξ,η` and any `u`,
`(tpart u - ⟪u,ξ⟫)(tpart u - ⟪u,η⟫) ≥ (1 - ⟪ξ,η⟫)/2`. -/
private theorem horoProdGe_aux (n : ℕ) (ξ η u : E n) (hξ : ξ ∈ Sph n) (hη : η ∈ Sph n) :
    (tpart u - inner ℝ u ξ) * (tpart u - inner ℝ u η) ≥ (1 - inner ℝ ξ η) / 2 := by
  have hξn : ‖ξ‖ = 1 := (mem_Sph_iff ξ).mp hξ
  have hηn : ‖η‖ = 1 := (mem_Sph_iff η).mp hη
  have hstar := gram_bound n ξ η u hξ hη
  set c : ℝ := inner ℝ ξ η with hc
  set p : ℝ := inner ℝ u ξ with hp
  set q : ℝ := inner ℝ u η with hq
  set s : ℝ := tpart u with hs
  set X : ℝ := s - p with hX
  set Y : ℝ := s - q with hY
  have hs2 : s ^ 2 = 1 + ‖u‖ ^ 2 := by
    rw [hs, tpart]; exact Real.sq_sqrt (by positivity)
  have hcabs : |c| ≤ 1 := by
    rw [hc]
    have h := abs_real_inner_le_norm ξ η
    rwa [hξn, hηn, mul_one] at h
  by_cases hcm1 : c = -1
  · have hneg : η = -ξ := neg_of_inner_eq_neg_one hξn hηn (by rw [← hc]; exact hcm1)
    have hq_eq : q = -p := by
      rw [hq, hp, hneg, inner_neg_right]
    have hp2 : p ^ 2 ≤ ‖u‖ ^ 2 := by
      rw [hp]
      have h := abs_real_inner_le_norm u ξ
      rw [hξn, mul_one] at h
      have hsqa : |inner ℝ u ξ| ^ 2 = (inner ℝ u ξ) ^ 2 := sq_abs _
      nlinarith [h, hsqa, abs_nonneg (inner ℝ u ξ)]
    rw [hcm1]; norm_num
    have hXYeq : X * Y = s ^ 2 - p ^ 2 := by rw [hX, hY, hq_eq]; ring
    nlinarith [hXYeq, hs2, hp2]
  · have hcgt : -1 < c := lt_of_le_of_ne (abs_le.mp hcabs).1 (Ne.symm hcm1)
    have hQ : ((1-c)*s - (X+Y))^2 ≤ (1+c)*(2*X*Y - (1-c)) := by
      nlinarith [hstar, hs2, hX, hY, hp, hq, hc]
    have h1c : 0 < 1 + c := by linarith
    have hnn : 0 ≤ (1+c)*(2*X*Y - (1-c)) := le_trans (sq_nonneg _) hQ
    have hmain : 0 ≤ 2*X*Y - (1-c) := by nlinarith [hnn, h1c]
    nlinarith [hmain]

/-- The Busemann inequality `busemann ξ u < t` is `exp` of the level being below `exp t`. -/
private theorem busemann_lt_exp_iff (n : ℕ) (ζ : E n) (hζ : ζ ∈ Sph n) (u : E n) (s : ℝ) :
    (busemann ζ u < s ↔ tpart u - inner ℝ u ζ < Real.exp s) := by
  rw [busemann]
  exact Real.log_lt_iff_lt_exp (busemann_arg_pos ζ hζ u)

/-- Attainment of a pair of Busemann levels whose product is the critical value
`(1 - ⟪ξ,η⟫)/2`: the explicit point `u = (Y/d) • ξ + (X/d) • η`, `d = 1 - ⟪ξ,η⟫`. -/
theorem horoAttain (n : ℕ) (ξ η : E n) (hξ : ξ ∈ Sph n) (hη : η ∈ Sph n) (hne : ξ ≠ η)
    (X Y : ℝ) (hX : 0 < X) (hY : 0 < Y) (hXY : X * Y = (1 - inner ℝ ξ η) / 2) :
    ∃ u : E n, tpart u - inner ℝ u ξ = X ∧ tpart u - inner ℝ u η = Y := by
  have hξn : ‖ξ‖ = 1 := (mem_Sph_iff ξ).mp hξ
  have hηn : ‖η‖ = 1 := (mem_Sph_iff η).mp hη
  have hclt : inner ℝ ξ η < 1 := (inner_lt_one_iff_real_of_norm_eq_one hξn hηn).mpr hne
  set c : ℝ := inner ℝ ξ η with hcdef
  set d : ℝ := 1 - c with hddef
  have hdpos : 0 < d := by rw [hddef, hcdef]; linarith
  have hXYd : X * Y = d / 2 := by rw [hddef, hcdef]; exact hXY
  have hξ2 : inner ℝ ξ ξ = 1 := by rw [real_inner_self_eq_norm_sq, hξn]; norm_num
  have hη2 : inner ℝ η η = 1 := by rw [real_inner_self_eq_norm_sq, hηn]; norm_num
  have hηξ : inner ℝ η ξ = inner ℝ ξ η := (real_inner_comm η ξ).symm
  set u : E n := (Y / d) • ξ + (X / d) • η with hudef
  have hinnerξ : inner ℝ u ξ = Y / d + (X / d) * c := by
    rw [hudef]
    simp only [inner_add_left, real_inner_smul_left, hξ2, hηξ, ← hcdef]
    ring
  have hinnerη : inner ℝ u η = (Y / d) * c + X / d := by
    rw [hudef]
    simp only [inner_add_left, real_inner_smul_left, hη2, ← hcdef]
    ring
  have hnorm : ‖u‖ ^ 2 = (Y ^ 2 + 2 * (X * Y) * c + X ^ 2) / d ^ 2 := by
    rw [← real_inner_self_eq_norm_sq u, hudef]
    simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
      hξ2, hη2, hηξ, ← hcdef]
    field_simp
    ring
  have htpart : tpart u = (X + Y) / d := by
    have hsq : 1 + ‖u‖ ^ 2 = ((X + Y) / d) ^ 2 := by
      rw [hnorm]
      field_simp
      nlinarith [hXYd]
    have hpos : 0 < (X + Y) / d := by positivity
    rw [tpart, hsq, Real.sqrt_sq hpos.le]
  refine ⟨u, ?_, ?_⟩
  · rw [htpart, hinnerξ]
    field_simp
    rw [hddef]; ring
  · rw [htpart, hinnerη]
    field_simp
    rw [hddef]; ring

theorem cuspHoroInterIff (n : ℕ) (hA : Submission.Mostow.POActionProp n) (hI : Submission.Mostow.HypIsometryProp n)
    (ξ η : Submission.Mostow.E n) (hξ : ξ ∈ Submission.Mostow.Sph n) (hη : η ∈ Submission.Mostow.Sph n)
    (hne : ξ ≠ η) (t t' : ℝ) :
    ((∃ u : Submission.Mostow.E n, Submission.Mostow.busemann ξ u < t ∧ Submission.Mostow.busemann η u < t') ↔
      Real.exp (t + t') > (1 - inner ℝ ξ η) / 2) := by
  constructor
  · rintro ⟨u, hu1, hu2⟩
    have h1 := (busemann_lt_exp_iff n ξ hξ u t).1 hu1
    have h2 := (busemann_lt_exp_iff n η hη u t').1 hu2
    have hXpos : 0 < tpart u - inner ℝ u ξ := busemann_arg_pos ξ hξ u
    have hYpos : 0 < tpart u - inner ℝ u η := busemann_arg_pos η hη u
    have ha : 0 < Real.exp t := Real.exp_pos t
    have hlt : (tpart u - inner ℝ u ξ) * (tpart u - inner ℝ u η) <
        Real.exp t * Real.exp t' := by
      have h3 : (tpart u - inner ℝ u ξ) * (tpart u - inner ℝ u η) <
          Real.exp t * (tpart u - inner ℝ u η) := mul_lt_mul_of_pos_right h1 hYpos
      have h4 : Real.exp t * (tpart u - inner ℝ u η) < Real.exp t * Real.exp t' :=
        mul_lt_mul_of_pos_left h2 ha
      linarith
    have hge := horoProdGe_aux n ξ η u hξ hη
    rw [Real.exp_add]
    linarith
  · intro h
    have ha : 0 < Real.exp t := Real.exp_pos t
    have hb : 0 < Real.exp t' := Real.exp_pos t'
    have hprod : (1 - inner ℝ ξ η) / 2 < Real.exp t * Real.exp t' := by
      rw [← Real.exp_add]; exact h
    set c : ℝ := 1 - inner ℝ ξ η with hcdef
    have hcpos : 0 < c := by
      have hξn : ‖ξ‖ = 1 := (mem_Sph_iff ξ).mp hξ
      have hηn : ‖η‖ = 1 := (mem_Sph_iff η).mp hη
      have := (inner_lt_one_iff_real_of_norm_eq_one hξn hηn).mpr hne
      simp only [hcdef]; linarith
    set L : ℝ := c / (2 * Real.exp t') with hLdef
    have hLnonneg : 0 ≤ L := by rw [hLdef]; positivity
    have hLlt : L < Real.exp t := by
      rw [hLdef, div_lt_iff₀ (by positivity : (0:ℝ) < 2 * Real.exp t')]
      nlinarith [hprod, ha, hb]
    set X0 : ℝ := (L + Real.exp t) / 2 with hX0def
    have hX0pos : 0 < X0 := by rw [hX0def]; linarith
    have hX0lt : X0 < Real.exp t := by rw [hX0def]; linarith
    set Y0 : ℝ := c / (2 * X0) with hY0def
    have hY0pos : 0 < Y0 := by rw [hY0def]; positivity
    have hY0lt : Y0 < Real.exp t' := by
      rw [hY0def, div_lt_iff₀ (by positivity : (0:ℝ) < 2 * X0)]
      have hL' : c / (2 * Real.exp t') < X0 := by rw [hX0def]; linarith
      rw [div_lt_iff₀ (by positivity : (0:ℝ) < 2 * Real.exp t')] at hL'
      nlinarith [hL']
    have hXY0 : X0 * Y0 = (1 - inner ℝ ξ η) / 2 := by
      rw [hY0def, hcdef]
      field_simp
    obtain ⟨u, huX, huY⟩ := horoAttain n ξ η hξ hη hne X0 Y0 hX0pos hY0pos hXY0
    refine ⟨u, ?_, ?_⟩
    · rw [busemann_lt_exp_iff n ξ hξ u t, huX]; exact hX0lt
    · rw [busemann_lt_exp_iff n η hη u t', huY]; exact hY0lt

end Work.Mostow
