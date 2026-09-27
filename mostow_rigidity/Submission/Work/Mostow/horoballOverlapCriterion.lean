import Mathlib
import Submission.Work.Mostow.horoball_minkowski_pair
import Submission.Work.Mostow.BaryBase

/-!
# The horoball overlap criterion

For two boundary points `ξ, η ∈ Sph n` and levels `t, t'`, the two open horoballs
`horoball ξ t` and `horoball η t'` have a common point exactly when

`1 - ⟪ξ,η⟫ < 2 exp (t + t')`.

Writing `X = tpart u - ⟪u,ξ⟫`, `Y = tpart u - ⟪u,η⟫` (so that `u ∈ horoball ξ t ⟺ X < exp t`),
the sharp inequality `X * Y ≥ (1 - ⟪ξ,η⟫)/2` (`Work.Mostow.horoball_minkowski_pair`) gives the
"only if" direction, while the "if" direction is the *attainment* of the critical product
`X * Y = (1 - ⟪ξ,η⟫)/2` in the totally geodesic plane through `ξ, η`: the point
`u = (Y/d) ξ + (X/d) η` with `d = 1 - ⟪ξ,η⟫` realises the two prescribed levels exactly. The
degenerate case `ξ = η` is trivial since the horoballs are nested.

Everything is pure algebra in the chart `E n`; no group action is involved.
-/

namespace Work.Mostow

open Submission.Mostow

noncomputable section

variable {n : ℕ}

/-- `busemann ζ u < s` is the statement that the Busemann level `tpart u - ⟪u,ζ⟫` is below
`exp s`. -/
private theorem busemann_lt_exp_iff (n : ℕ) (ζ : E n) (hζ : ζ ∈ Sph n) (u : E n) (s : ℝ) :
    (busemann ζ u < s ↔ tpart u - inner ℝ u ζ < Real.exp s) := by
  rw [busemann]
  exact Real.log_lt_iff_lt_exp (busemann_arg_pos ζ hζ u)

/-- **Attainment of the critical product** in the plane spanned by `ξ ≠ η`: for positive `X,Y`
with `X * Y = (1 - ⟪ξ,η⟫)/2`, the point `u = (Y/d) ξ + (X/d) η` (`d = 1 - ⟪ξ,η⟫`) satisfies
`tpart u - ⟪u,ξ⟫ = X` and `tpart u - ⟪u,η⟫ = Y`. -/
private theorem horoLevelAttainAux (n : ℕ) (ξ η : E n) (hξ : ξ ∈ Sph n) (hη : η ∈ Sph n)
    (hne : ξ ≠ η) (X Y : ℝ) (hX : 0 < X) (hY : 0 < Y)
    (hXY : X * Y = (1 - inner ℝ ξ η) / 2) :
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

/-- **The diagonal case.**  Both horoballs are the same, and there are points at arbitrarily small
Busemann level: along the ray `r ↦ r • ξ` the level `tpart u - ⟪u,ξ⟫ = √(1+r²) - r` tends
to `0`.  Concretely, with `p = min (exp t) (exp t')/2` and `r = 1/p`, one has
`(p+r)² = p² + 2 + r² > 1 + r² = (√(1+r²))²`, so `√(1+r²) - r < p`. -/
private theorem exists_busemann_lt_diag (n : ℕ) (ξ : E n) (hξ : ξ ∈ Sph n) (t t' : ℝ) :
    ∃ u : E n, busemann ξ u < t ∧ busemann ξ u < t' := by
  have hξn : ‖ξ‖ = 1 := (mem_Sph_iff ξ).mp hξ
  have hminpos : 0 < min (Real.exp t) (Real.exp t') :=
    lt_min (Real.exp_pos t) (Real.exp_pos t')
  set p : ℝ := min (Real.exp t) (Real.exp t') / 2 with hp
  have hppos : 0 < p := by rw [hp]; linarith
  have hplt : p < min (Real.exp t) (Real.exp t') := by rw [hp]; linarith
  set r : ℝ := 1 / p with hr
  have hrpos : 0 < r := by rw [hr]; positivity
  have hpr : p * r = 1 := by rw [hr]; field_simp
  have hnorm : ‖r • ξ‖ = r := by
    rw [norm_smul, hξn, mul_one, Real.norm_of_nonneg hrpos.le]
  have htpart : tpart (r • ξ) = Real.sqrt (1 + r ^ 2) := by
    rw [tpart, hnorm]
  have hinner : inner ℝ (r • ξ) ξ = r := by
    rw [real_inner_smul_left, real_inner_self_eq_norm_sq, hξn]
    ring
  have hsq : Real.sqrt (1 + r ^ 2) ^ 2 = 1 + r ^ 2 :=
    Real.sq_sqrt (by nlinarith [sq_nonneg r])
  have hlt : Real.sqrt (1 + r ^ 2) < p + r := by
    have h1 : Real.sqrt (1 + r ^ 2) ^ 2 < (p + r) ^ 2 := by
      rw [hsq]
      nlinarith [hpr, sq_nonneg p]
    have h2 := sq_lt_sq.mp h1
    rwa [abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg (by linarith : (0:ℝ) ≤ p + r)] at h2
  have harg : tpart (r • ξ) - inner ℝ (r • ξ) ξ < p := by
    rw [htpart, hinner]; linarith
  have harg' : tpart (r • ξ) - inner ℝ (r • ξ) ξ < min (Real.exp t) (Real.exp t') :=
    lt_of_lt_of_le harg hplt.le
  refine ⟨r • ξ,
    (busemann_lt_exp_iff n ξ hξ (r • ξ) t).2 (lt_of_lt_of_le harg' (min_le_left _ _)),
    (busemann_lt_exp_iff n ξ hξ (r • ξ) t').2 (lt_of_lt_of_le harg' (min_le_right _ _))⟩

/-- Elementary real arithmetic: below a level `c/2` that is smaller than the product `a * b`
there are positive `X < a`, `Y < b` with `X * Y = c / 2`. -/
private theorem exists_levels_real {c a b : ℝ} (hc : 0 < c) (ha : 0 < a) (hb : 0 < b)
    (h : c / 2 < a * b) : ∃ X Y : ℝ, 0 < X ∧ 0 < Y ∧ X < a ∧ Y < b ∧ X * Y = c / 2 := by
  have hLpos : 0 < c / (2 * b) := div_pos hc (by positivity)
  have hLlt : c / (2 * b) < a := by
    rw [div_lt_iff₀ (by positivity : (0:ℝ) < 2 * b)]
    nlinarith [h, hb]
  set X : ℝ := (c / (2 * b) + a) / 2 with hX
  have hLX : c / (2 * b) < X := by rw [hX]; linarith
  have hXa : X < a := by rw [hX]; linarith
  have hXpos : 0 < X := by linarith
  have hYpos : 0 < c / (2 * X) := div_pos hc (by positivity)
  have hYlt : c / (2 * X) < b := by
    rw [div_lt_iff₀ (by positivity : (0:ℝ) < 2 * X)]
    have h4 : c < X * (2 * b) :=
      (div_lt_iff₀ (by positivity : (0:ℝ) < 2 * b)).mp hLX
    nlinarith [h4]
  have hmul : X * (c / (2 * X)) = c / 2 := by
    field_simp
  exact ⟨X, c / (2 * X), hXpos, hYpos, hXa, hYlt, hmul⟩

theorem horoballOverlapCriterion (n : ℕ) (ξ η : Submission.Mostow.E n) (hξ : ξ ∈ Submission.Mostow.Sph n) (hη : η ∈ Submission.Mostow.Sph n) (t t' : ℝ) : (∃ u : Submission.Mostow.E n, u ∈ Submission.Mostow.horoball ξ t ∧ u ∈ Submission.Mostow.horoball η t') ↔ 1 - inner ℝ ξ η < 2 * Real.exp (t + t') := by
  constructor
  · rintro ⟨u, hu1, hu2⟩
    simp only [horoball, Set.mem_ofPred_eq] at hu1 hu2
    have h1 : tpart u - inner ℝ u ξ < Real.exp t := (busemann_lt_exp_iff n ξ hξ u t).1 hu1
    have h2 : tpart u - inner ℝ u η < Real.exp t' := (busemann_lt_exp_iff n η hη u t').1 hu2
    have hX : 0 < tpart u - inner ℝ u ξ := busemann_arg_pos ξ hξ u
    have hY : 0 < tpart u - inner ℝ u η := busemann_arg_pos η hη u
    have hlt : (tpart u - inner ℝ u ξ) * (tpart u - inner ℝ u η)
        < Real.exp t * Real.exp t' := by
      have h3 := mul_lt_mul_of_pos_right h1 hY
      have h4 := mul_lt_mul_of_pos_left h2 (Real.exp_pos t)
      linarith
    have hge := horoball_minkowski_pair n ξ η hξ hη u
    have hfin : (1 - inner ℝ ξ η) / 2 < Real.exp (t + t') := by
      rw [Real.exp_add]; linarith
    linarith
  · intro h
    by_cases hne : ξ = η
    · subst hne
      obtain ⟨u, hu1, hu2⟩ := exists_busemann_lt_diag n ξ hξ t t'
      exact ⟨u, by simpa only [horoball, Set.mem_ofPred_eq] using hu1,
        by simpa only [horoball, Set.mem_ofPred_eq] using hu2⟩
    · have hξn : ‖ξ‖ = 1 := (mem_Sph_iff ξ).mp hξ
      have hηn : ‖η‖ = 1 := (mem_Sph_iff η).mp hη
      have hclt : inner ℝ ξ η < 1 := (inner_lt_one_iff_real_of_norm_eq_one hξn hηn).mpr hne
      have hcpos : 0 < 1 - inner ℝ ξ η := by linarith
      have hprod : (1 - inner ℝ ξ η) / 2 < Real.exp t * Real.exp t' := by
        rw [← Real.exp_add]; linarith
      obtain ⟨X, Y, hXpos, hYpos, hXlt, hYlt, hXY⟩ :=
        exists_levels_real hcpos (Real.exp_pos t) (Real.exp_pos t') hprod
      obtain ⟨u, huX, huY⟩ := horoLevelAttainAux n ξ η hξ hη hne X Y hXpos hYpos hXY
      refine ⟨u, ?_, ?_⟩
      · simpa only [horoball, Set.mem_ofPred_eq] using
          (busemann_lt_exp_iff n ξ hξ u t).2 (by rw [huX]; exact hXlt)
      · simpa only [horoball, Set.mem_ofPred_eq] using
          (busemann_lt_exp_iff n η hη u t').2 (by rw [huY]; exact hYlt)

end

end Work.Mostow
