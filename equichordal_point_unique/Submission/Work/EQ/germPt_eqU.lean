import Mathlib
import Submission.Work.EQ.Defs
import Submission.Work.EQ.germPt_smallData
import Submission.Work.EQ.eqU_germPt_algebra

namespace Work.EQ

open Complex

/-!
# The germ functional equation linearises the half-map

Main result `germPt_eqU`: for `0 < a < 1` and a stable germ `h`, the half-map `eqU a` acts on the
germ curve by the linearising parameter, `eqU a (germPt a h t) = germPt a h (λ t)` for small real
`t > 0` (`λ = eqLam a`).

Writing `p = h t`, `q = h (λt)`, `s = h (λ²t)` (all real, with `p < q < s < 0` for small `t > 0`),
the point `P = germPt a h t` has coordinates `(a q/(q-p) - a/2, a p q/(q-p))`, whence
`P - a/2 = c (1 + i q)` with `c = a p/(q-p) < 0`, so `‖P - a/2‖ = -c √(1+q²)` and
`eqU a P = -P - (1+iq)/√(1+q²)`.  Rychlik's recurrence `GermFE a h (λt)` is exactly
`(q-p)(s-q) + a q (s-p)√(1+q²) = 0`, which says `1/√(1+q²) = -a p/(q-p) - a s/(s-q)`; substituting
this shows that `eqU a P` has coordinates `(a s/(s-q) - a/2, a q s/(s-q))`, i.e. is
`germPt a h (λt)`.
-/

noncomputable section

/-- `(1 + q ^ 2) ^ (1 / 2 : ℂ)` (the principal complex power, for real `q`) is the coercion of
the real square root `√(1 + q²)`. -/
lemma germPt_eqU_cpow_half_one_add_sq (q : ℝ) :
    (1 + (q : ℂ) ^ 2) ^ (1 / 2 : ℂ) = ((Real.sqrt (1 + q ^ 2) : ℝ) : ℂ) := by
  have h1 : (1 : ℂ) + (q : ℂ) ^ 2 = ((1 + q ^ 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_add, Complex.ofReal_one, Complex.ofReal_pow]
  rw [h1, show (1 / 2 : ℂ) = (((1 / 2 : ℝ)) : ℂ) by norm_num,
    ← Complex.ofReal_cpow (by positivity : (0 : ℝ) ≤ 1 + q ^ 2) (1 / 2 : ℝ)]
  congr 1
  exact (Real.sqrt_eq_rpow (1 + q ^ 2)).symm

/-- `GermFE a h (λ t)`, together with realness of `h t`, `h (λt)`, `h (λ²t)`, is the real
recurrence `(q - p) (s - q) + a q (s - p) √(1 + q²) = 0` for `p = h t`, `q = h (λt)`,
`s = h (λ²t)`. -/
lemma germPt_eqU_germFE_real {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {t : ℝ}
    (him_1 : (h (t : ℂ)).im = 0)
    (him_2 : (h ((eqLam a : ℂ) * (t : ℂ))).im = 0)
    (him_3 : (h ((eqLam a : ℂ) * ((eqLam a : ℂ) * (t : ℂ)))).im = 0)
    (hFE : GermFE a h ((eqLam a : ℂ) * (t : ℂ))) :
    ((h ((eqLam a : ℂ) * (t : ℂ))).re - (h (t : ℂ)).re) *
        ((h ((eqLam a : ℂ) * ((eqLam a : ℂ) * (t : ℂ)))).re - (h ((eqLam a : ℂ) * (t : ℂ))).re)
      + a * (h ((eqLam a : ℂ) * (t : ℂ))).re *
        ((h ((eqLam a : ℂ) * ((eqLam a : ℂ) * (t : ℂ)))).re - (h (t : ℂ)).re) *
        Real.sqrt (1 + (h ((eqLam a : ℂ) * (t : ℂ))).re ^ 2) = 0 := by
  have hlam : (eqLam a) ≠ 0 := by
    have : 0 < eqLam a := by rw [eqLam]; exact div_pos (by linarith) (by linarith)
    exact ne_of_gt this
  set p := (h (t : ℂ)).re
  set q := (h ((eqLam a : ℂ) * (t : ℂ))).re
  set s := (h ((eqLam a : ℂ) * ((eqLam a : ℂ) * (t : ℂ)))).re
  have e1 : h (t : ℂ) = (p : ℂ) := Complex.ext (by simp [p]) (by simp [p, him_1])
  have e2 : h ((eqLam a : ℂ) * (t : ℂ)) = (q : ℂ) :=
    Complex.ext (by simp [q]) (by simp [q, him_2])
  have e3 : h ((eqLam a : ℂ) * ((eqLam a : ℂ) * (t : ℂ))) = (s : ℂ) :=
    Complex.ext (by simp [s]) (by simp [s, him_3])
  have hu : ((eqLam a : ℂ) * (t : ℂ)) / (eqLam a : ℂ) = (t : ℂ) :=
    mul_div_cancel_left₀ _ (by exact_mod_cast hlam)
  have main : (((q - p) * (s - q) + a * q * (s - p) * Real.sqrt (1 + q ^ 2) : ℝ) : ℂ) = 0 := by
    rw [← hFE]
    rw [hu, e1, e2, e3, germPt_eqU_cpow_half_one_add_sq q]
    push_cast
    ring
  have hz := Complex.ofReal_eq_zero.mp main
  simpa [p, q, s] using hz

/-- **The germ functional equation linearises the half-map.**  For `0 < a < 1` and a stable germ
`h`, one has `eqU a (germPt a h t) = germPt a h (λ t)` for all sufficiently small real `t > 0`,
where `λ = eqLam a = (1 - a)/(1 + a)`. -/
theorem germPt_eqU {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, 0 < t → t < ε →
      eqU a (germPt a h t) = germPt a h (eqLam a * t) := by
  obtain ⟨ε₁, hε₁, H⟩ := germPt_smallData ha0 ha1 hh
  obtain ⟨hr, -, -, -, -, hFEs⟩ := hh
  have hlam0 : 0 < eqLam a := by rw [eqLam]; exact div_pos (by linarith) (by linarith)
  refine ⟨min ε₁ r, lt_min hε₁ hr, ?_⟩
  intro t ht htε
  have ht₁ : t < ε₁ := lt_of_lt_of_le htε (min_le_left _ _)
  have htr : t < r := lt_of_lt_of_le htε (min_le_right _ _)
  obtain ⟨ht_abs, habs1, habs2, him1, him2, him3, hp_neg, hpq_lt, hqs_lt⟩ := H t ht ht₁
  set p := (h (t : ℂ)).re with hp_eq
  set q := (h ((eqLam a : ℂ) * (t : ℂ))).re with hq_eq
  set s := (h ((eqLam a : ℂ) * ((eqLam a : ℂ) * (t : ℂ)))).re with hs_eq
  have e1 : h (t : ℂ) = (p : ℂ) := Complex.ext (by simp [hp_eq]) (by simp [hp_eq, him1])
  have e2 : h ((eqLam a : ℂ) * (t : ℂ)) = (q : ℂ) :=
    Complex.ext (by simp [hq_eq]) (by simp [hq_eq, him2])
  have e3 : h ((eqLam a : ℂ) * ((eqLam a : ℂ) * (t : ℂ))) = (s : ℂ) :=
    Complex.ext (by simp [hs_eq]) (by simp [hs_eq, him3])
  -- `GermFE` at `u = λ t`; the point `u` lies in the ball of radius `λ r`
  have hGE : GermFE a h ((eqLam a : ℂ) * (t : ℂ)) := by
    apply hFEs
    rw [Metric.mem_ball, dist_zero_right]
    have hnorm : ‖((eqLam a : ℂ) * (t : ℂ))‖ = eqLam a * t := by
      rw [← Complex.ofReal_mul]
      rw [show ‖((eqLam a * t : ℝ) : ℂ)‖ = |eqLam a * t| by simp,
        abs_of_pos (mul_pos hlam0 ht)]
    rw [hnorm]
    exact mul_lt_mul_of_pos_left htr hlam0
  -- the real recurrence for `p, q, s`
  have hFEreal : (q - p) * (s - q) + a * q * (s - p) * Real.sqrt (1 + q ^ 2) = 0 := by
    have h1 := germPt_eqU_germFE_real ha0 ha1 him1 him2 him3 hGE
    rw [← hp_eq, ← hq_eq, ← hs_eq] at h1
    exact h1
  -- coordinates of `germPt a h t`
  have hPt : germPt a h t =
      ((a * q / (q - p) - a / 2 : ℝ) : ℂ) +
        ((a * p * q / (q - p) : ℝ) : ℂ) * Complex.I := by
    rw [germPt, e1, e2]
    refine Complex.ext ?_ ?_
    · simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero]
      rw [← Complex.ofReal_mul, ← Complex.ofReal_sub, ← Complex.ofReal_div, Complex.ofReal_re]
    · simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_zero, mul_one, add_zero, zero_add]
      rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_sub, ← Complex.ofReal_div,
        Complex.ofReal_re]
  -- coordinates of `germPt a h (λ t)`
  have e2' : h (((eqLam a * t : ℝ)) : ℂ) = (q : ℂ) := by
    rw [Complex.ofReal_mul]; exact e2
  have e3' : h ((eqLam a : ℂ) * (((eqLam a * t : ℝ)) : ℂ)) = (s : ℂ) := by
    rw [Complex.ofReal_mul]; exact e3
  have hQt : germPt a h (eqLam a * t) =
      ((a * s / (s - q) - a / 2 : ℝ) : ℂ) +
        ((a * q * s / (s - q) : ℝ) : ℂ) * Complex.I := by
    rw [germPt, e2', e3']
    refine Complex.ext ?_ ?_
    · simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero]
      rw [← Complex.ofReal_mul, ← Complex.ofReal_sub, ← Complex.ofReal_div, Complex.ofReal_re]
    · simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_zero, mul_one, add_zero, zero_add]
      rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_sub, ← Complex.ofReal_div,
        Complex.ofReal_re]
  rw [hPt, hQt]
  simp only [Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_div]
  exact eqU_germPt_algebra ha0 hp_neg (sub_pos.mpr hpq_lt) (sub_pos.mpr hqs_lt) hFEreal

end

end Work.EQ
