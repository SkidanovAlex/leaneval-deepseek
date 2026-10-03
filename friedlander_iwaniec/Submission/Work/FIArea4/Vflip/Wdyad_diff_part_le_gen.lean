import Mathlib
import Submission.Work.FIArea4.Vflip.Wloc_bound_fresh
import Submission.Work.FIArea4.lemma_11_4
import Submission.Work.FIArea4.sigma_gamma_le
import Submission.Work.FIArea4.WdyadDefs2

set_option maxHeartbeats 1000000

/-!
# The non-flat (`♦`) part of the dyadic dual form, general kernel version

This is the general-`F` form of `Work.FIArea4.Vflip.Wdyad_diff_part_le`: for an arbitrary
sampling function `F` with the decay `‖F ξ‖ ≤ C₀ S (1 + S|ξ|)⁻²` of `Wloc_bound_fresh`, the
non-flat (`♦`) part of the Poisson-expanded dyadic form is bounded by

`C · (S R^{3/4} + D R + D√(RS)) (DR)^ε · Σ_d Σ_{a<d} |γ(a,d)|²`.

The proof follows `Wdyad_diff_part_le`, with `Wloc_bound` replaced by its general form
`Wloc_bound_fresh` (which takes `σ = S`, `C₀` and the decay hypothesis as parameters) and with the
Cauchy--Schwarz step `cs_nonflat` generalised to an arbitrary kernel.  The inputs are the local
variance estimate (`Wloc_bound_fresh`), the §11.4 character-sum estimate (`lemma_11_4`) and
`sigma_gamma_le`; hence the constant `C` depends on `ε`, `S`, `F`, `C₀` only.
-/

namespace Work.FIArea4.Vflip

open Finset
open scoped BigOperators

noncomputable section

/-- The Jacobi character sum over the first `R'` integers, restricted to the units modulo `d₁d₂`. -/
def wdg_CSsum (d1 d2 R' : ℕ) : ℝ :=
  Complex.normSq (∑ r ∈ (Finset.Icc 1 R').filter (fun r => Nat.Coprime r (d1 * d2)),
    (jacobiSym (r : ℤ) (Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2) : ℂ))

/-- The Jacobi character sum over the dyadic interval `(R, 2R]`. -/
def wdg_CSsumIoc (d1 d2 R : ℕ) : ℝ :=
  Complex.normSq (∑ r ∈ (Finset.Ioc R (2 * R)).filter (fun r => Nat.Coprime r (d1 * d2)),
    (jacobiSym (r : ℤ) (Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2) : ℂ))

/-! ## Elementary inequalities -/

lemma wdg_normSq_sub_le (a b : ℂ) :
    Complex.normSq (a - b) ≤ 2 * (Complex.normSq a + Complex.normSq b) := by
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
  have h : ‖a - b‖ ≤ ‖a‖ + ‖b‖ := norm_sub_le a b
  have h1 : (0:ℝ) ≤ ‖a - b‖ := norm_nonneg _
  have h2 : (0:ℝ) ≤ ‖a‖ := norm_nonneg _
  have h3 : (0:ℝ) ≤ ‖b‖ := norm_nonneg _
  nlinarith [sq_nonneg (‖a‖ - ‖b‖), h, h1, h2, h3]

/-- `√(a+b) ≤ √a + √b`. -/
lemma wdg_sqrt_add_le_sqrt_add_sqrt {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
  have h1 : (0:ℝ) ≤ a + b := by linarith
  have h2 : (0:ℝ) ≤ Real.sqrt a + Real.sqrt b := by
    have := Real.sqrt_nonneg a; have := Real.sqrt_nonneg b; linarith
  rw [Real.sqrt_le_iff]
  refine ⟨h2, ?_⟩
  nlinarith [Real.sq_sqrt ha, Real.sq_sqrt hb, Real.sqrt_nonneg a, Real.sqrt_nonneg b]

/-- For `D,R ≥ 1` and `c ≥ 1`: `(c D² R)^{ε/4} ≤ c^{ε/4} (DR)^ε`. -/
lemma wdg_rpow_quarter_le (c : ℝ) (hc : 1 ≤ c) (D R : ℕ) (hD : 1 ≤ D) (hR : 1 ≤ R)
    (ε : ℝ) (hε : 0 < ε) :
    (c * (D:ℝ)^2 * (R:ℝ))^(ε/4) ≤ c^(ε/4) * ((D:ℝ)*(R:ℝ))^ε := by
  have hc0 : (0:ℝ) < c := lt_of_lt_of_le zero_lt_one hc
  have hD0 : (0:ℝ) < (D:ℝ) := by exact_mod_cast (by omega : 0 < D)
  have hR0 : (0:ℝ) < (R:ℝ) := by exact_mod_cast (by omega : 0 < R)
  have hD1 : (1:ℝ) ≤ (D:ℝ) := by exact_mod_cast hD
  have hR1 : (1:ℝ) ≤ (R:ℝ) := by exact_mod_cast hR
  rw [show c * (D:ℝ)^2 * (R:ℝ) = c * ((D:ℝ)^2 * (R:ℝ)) by ring]
  rw [Real.mul_rpow hc0.le (by positivity : (0:ℝ) ≤ (D:ℝ)^2 * (R:ℝ))]
  rw [Real.mul_rpow (by positivity : (0:ℝ) ≤ (D:ℝ)^2) (by positivity : (0:ℝ) ≤ (R:ℝ))]
  rw [show ((D:ℝ)^2)^(ε/4) = (D:ℝ)^(ε/2) from by
    rw [← Real.rpow_natCast (D:ℝ) 2, ← Real.rpow_mul hD0.le]
    congr 1; push_cast; ring]
  rw [Real.mul_rpow hD0.le hR0.le]
  refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hc0.le _)
  exact mul_le_mul (Real.rpow_le_rpow_of_exponent_le hD1 (by linarith))
    (Real.rpow_le_rpow_of_exponent_le hR1 (by linarith))
    (Real.rpow_nonneg hR0.le _) (Real.rpow_nonneg hD0.le _)

/-- For `D,R ≥ 1` and `c ≥ 1`: `(c D² R)^{ε/4} (DR)^{ε/4} ≤ c^{ε/4} (DR)^ε`. -/
lemma wdg_rpow_quarter_mul_le (c : ℝ) (hc : 1 ≤ c) (D R : ℕ) (hD : 1 ≤ D) (hR : 1 ≤ R)
    (ε : ℝ) (hε : 0 < ε) :
    (c * (D:ℝ)^2 * (R:ℝ))^(ε/4) * ((D:ℝ)*(R:ℝ))^(ε/4) ≤ c^(ε/4) * ((D:ℝ)*(R:ℝ))^ε := by
  have hc0 : (0:ℝ) < c := lt_of_lt_of_le zero_lt_one hc
  have hD0 : (0:ℝ) < (D:ℝ) := by exact_mod_cast (by omega : 0 < D)
  have hR0 : (0:ℝ) < (R:ℝ) := by exact_mod_cast (by omega : 0 < R)
  have hD1 : (1:ℝ) ≤ (D:ℝ) := by exact_mod_cast hD
  have hR1 : (1:ℝ) ≤ (R:ℝ) := by exact_mod_cast hR
  rw [show c * (D:ℝ)^2 * (R:ℝ) = c * ((D:ℝ)^2 * (R:ℝ)) by ring]
  rw [Real.mul_rpow hc0.le (by positivity : (0:ℝ) ≤ (D:ℝ)^2 * (R:ℝ))]
  rw [Real.mul_rpow (by positivity : (0:ℝ) ≤ (D:ℝ)^2) (by positivity : (0:ℝ) ≤ (R:ℝ))]
  rw [show ((D:ℝ)^2)^(ε/4) = (D:ℝ)^(ε/2) from by
    rw [← Real.rpow_natCast (D:ℝ) 2, ← Real.rpow_mul hD0.le]
    congr 1; push_cast; ring]
  rw [Real.mul_rpow hD0.le hR0.le, Real.mul_rpow hD0.le hR0.le]
  rw [show c ^ (ε/4) * ((D:ℝ)^(ε/2) * (R:ℝ)^(ε/4)) * ((D:ℝ)^(ε/4) * (R:ℝ)^(ε/4))
      = c^(ε/4) * ((D:ℝ)^(ε/2) * (D:ℝ)^(ε/4)) * ((R:ℝ)^(ε/4) * (R:ℝ)^(ε/4)) from by ring]
  rw [← Real.rpow_add hD0 (ε/2) (ε/4), ← Real.rpow_add hR0 (ε/4) (ε/4)]
  rw [show ε/2 + ε/4 = 3*ε/4 by ring, show ε/4 + ε/4 = ε/2 by ring]
  have hDx : (D:ℝ)^(3*ε/4) ≤ (D:ℝ)^ε := Real.rpow_le_rpow_of_exponent_le hD1 (by linarith)
  have hRx : (R:ℝ)^(ε/2) ≤ (R:ℝ)^ε := Real.rpow_le_rpow_of_exponent_le hR1 (by linarith)
  have hc4 : (0:ℝ) ≤ c^(ε/4) := Real.rpow_nonneg hc0.le _
  have h1 : (0:ℝ) ≤ (D:ℝ)^(3*ε/4) := Real.rpow_nonneg hD0.le _
  have h2 : (0:ℝ) ≤ (R:ℝ)^(ε/2) := Real.rpow_nonneg hR0.le _
  have h3 : (0:ℝ) ≤ (D:ℝ)^ε := Real.rpow_nonneg hD0.le _
  have h4 : (0:ℝ) ≤ (R:ℝ)^ε := Real.rpow_nonneg hR0.le _
  nlinarith [hDx, hRx, mul_nonneg hc4 h1, mul_nonneg hc4 h3,
    mul_le_mul_of_nonneg_left hDx (mul_nonneg hc4 h2)]

/-- The bracket `S R^{3/4} + D R + D√(RS)` dominates `√(S²R^{3/2} + D²(R+S)R)`. -/
lemma wdg_sq_le_bracket_sq (D R S : ℕ) (hD : 1 ≤ D) (hR : 1 ≤ R) :
    (S:ℝ)^2 * (R:ℝ)^((3:ℝ)/2) + (D:ℝ)^2 * ((R:ℝ) + (S:ℝ)) * (R:ℝ)
      ≤ ((S:ℝ) * (R:ℝ)^((3:ℝ)/4) + (D:ℝ) * (R:ℝ)
          + (D:ℝ) * Real.sqrt ((R:ℝ)*(S:ℝ)))^2 := by
  have hR0 : (0:ℝ) < (R:ℝ) := by exact_mod_cast (by omega : 0 < R)
  have hS0 : (0:ℝ) ≤ (S:ℝ) := Nat.cast_nonneg S
  have hD0 : (0:ℝ) ≤ (D:ℝ) := Nat.cast_nonneg D
  have hu2 : ((R:ℝ)^((3:ℝ)/4))^2 = (R:ℝ)^((3:ℝ)/2) := by
    rw [pow_two, ← Real.rpow_add hR0]; norm_num
  have hs2 : (Real.sqrt ((R:ℝ)*(S:ℝ)))^2 = (R:ℝ)*(S:ℝ) := Real.sq_sqrt (by positivity)
  have hu : (0:ℝ) ≤ (R:ℝ)^((3:ℝ)/4) := Real.rpow_nonneg hR0.le _
  have hs : (0:ℝ) ≤ Real.sqrt ((R:ℝ)*(S:ℝ)) := Real.sqrt_nonneg _
  nlinarith [sq_nonneg ((S:ℝ) * (R:ℝ)^((3:ℝ)/4) + (D:ℝ) * (R:ℝ) + (D:ℝ) * Real.sqrt ((R:ℝ)*(S:ℝ))),
    mul_nonneg hS0 hu, mul_nonneg hD0 (by linarith : (0:ℝ) ≤ (R:ℝ)), mul_nonneg hD0 hs,
    sq_nonneg (S:ℝ), sq_nonneg (D:ℝ), sq_nonneg (R:ℝ)]

/-! ## The character-sum transfer -/

/-- `(Icc 1 (2R)).filter · = (Icc 1 R).filter · ∪ (Ioc R (2R)).filter ·`. -/
lemma wdg_icc_filter_eq_union (d1 d2 R : ℕ) :
    (Finset.Icc 1 (2*R)).filter (fun r => Nat.Coprime r (d1*d2))
      = (Finset.Icc 1 R).filter (fun r => Nat.Coprime r (d1*d2))
        ∪ (Finset.Ioc R (2*R)).filter (fun r => Nat.Coprime r (d1*d2)) := by
  ext r
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc, Finset.mem_union]
  constructor
  · rintro ⟨⟨h1, h2⟩, hc⟩
    rcases le_or_gt r R with h | h
    · exact Or.inl ⟨⟨h1, h⟩, hc⟩
    · exact Or.inr ⟨⟨h, h2⟩, hc⟩
  · rintro (⟨⟨h1, h2⟩, hc⟩ | ⟨⟨h1, h2⟩, hc⟩)
    · exact ⟨⟨h1, by omega⟩, hc⟩
    · exact ⟨⟨by omega, h2⟩, hc⟩

lemma wdg_disjoint_icc_ioc (d1 d2 R : ℕ) :
    Disjoint ((Finset.Icc 1 R).filter (fun r => Nat.Coprime r (d1*d2)))
      ((Finset.Ioc R (2*R)).filter (fun r => Nat.Coprime r (d1*d2))) := by
  rw [Finset.disjoint_left]
  intro x hx hy
  rw [Finset.mem_filter, Finset.mem_Icc] at hx
  rw [Finset.mem_filter, Finset.mem_Ioc] at hy
  omega

/-- The dyadic character sum is controlled by the two prefix sums (`X ≤ 2(X₁+X₂)`). -/
lemma wdg_CSsumIoc_le (R d1 d2 : ℕ) :
    wdg_CSsumIoc d1 d2 R ≤ 2 * (wdg_CSsum d1 d2 (2*R) + wdg_CSsum d1 d2 R) := by
  have hsum : (∑ r ∈ (Finset.Icc 1 (2*R)).filter (fun r => Nat.Coprime r (d1*d2)),
        (jacobiSym (r : ℤ) (Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2) : ℂ))
      = (∑ r ∈ (Finset.Ioc R (2*R)).filter (fun r => Nat.Coprime r (d1*d2)),
          (jacobiSym (r : ℤ) (Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2) : ℂ))
        + (∑ r ∈ (Finset.Icc 1 R).filter (fun r => Nat.Coprime r (d1*d2)),
          (jacobiSym (r : ℤ) (Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2) : ℂ)) := by
    rw [wdg_icc_filter_eq_union d1 d2 R, Finset.sum_union (wdg_disjoint_icc_ioc d1 d2 R)]
    ring
  have hdiff : (∑ r ∈ (Finset.Ioc R (2*R)).filter (fun r => Nat.Coprime r (d1*d2)),
          (jacobiSym (r : ℤ) (Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2) : ℂ))
      = (∑ r ∈ (Finset.Icc 1 (2*R)).filter (fun r => Nat.Coprime r (d1*d2)),
          (jacobiSym (r : ℤ) (Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2) : ℂ))
        - (∑ r ∈ (Finset.Icc 1 R).filter (fun r => Nat.Coprime r (d1*d2)),
          (jacobiSym (r : ℤ) (Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2) : ℂ)) := by
    rw [hsum]; ring
  rw [wdg_CSsumIoc, wdg_CSsum, wdg_CSsum, hdiff]
  exact wdg_normSq_sub_le _ _

/-! ## Cauchy–Schwarz over the index set `(d₁,d₂,a)` -/

/-- Cauchy–Schwarz for a finite sum of complex products. -/
lemma wdg_norm_sum_mul_le_sqrt {ι : Type*} (s : Finset ι) (f g : ι → ℂ) :
    ‖∑ i ∈ s, f i * g i‖ ≤ Real.sqrt (∑ i ∈ s, ‖f i‖ ^ 2) * Real.sqrt (∑ i ∈ s, ‖g i‖ ^ 2) := by
  have h1 : ‖∑ i ∈ s, f i * g i‖ ≤ ∑ i ∈ s, ‖f i‖ * ‖g i‖ := by
    calc ‖∑ i ∈ s, f i * g i‖ ≤ ∑ i ∈ s, ‖f i * g i‖ := norm_sum_le _ _
      _ = ∑ i ∈ s, ‖f i‖ * ‖g i‖ := by simp only [norm_mul]
  have h2 : (∑ i ∈ s, ‖f i‖ * ‖g i‖) ^ 2
      ≤ (∑ i ∈ s, ‖f i‖ ^ 2) * ∑ i ∈ s, ‖g i‖ ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq s _ _
  have h3 : (0:ℝ) ≤ ∑ i ∈ s, ‖f i‖ ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have h4 : (0:ℝ) ≤ ∑ i ∈ s, ‖g i‖ ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have h5 : (0:ℝ) ≤ ∑ i ∈ s, ‖f i‖ * ‖g i‖ :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
  have h6 : ∑ i ∈ s, ‖f i‖ * ‖g i‖ ≤ Real.sqrt ((∑ i ∈ s, ‖f i‖^2) * ∑ i ∈ s, ‖g i‖^2) := by
    rw [← Real.sqrt_sq h5]
    exact Real.sqrt_le_sqrt h2
  refine h1.trans (h6.trans ?_)
  rw [Real.sqrt_mul h3]

/-- Cauchy–Schwarz with square-root weights. -/
lemma wdg_sum_sqrt_mul_le_sqrt {ι : Type*} (s : Finset ι) (x y : ι → ℝ)
    (hx : ∀ i ∈ s, 0 ≤ x i) (hy : ∀ i ∈ s, 0 ≤ y i) :
    ∑ i ∈ s, Real.sqrt (x i) * Real.sqrt (y i)
      ≤ Real.sqrt (∑ i ∈ s, x i) * Real.sqrt (∑ i ∈ s, y i) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq s (fun i => Real.sqrt (x i)) (fun i => Real.sqrt (y i))
  rw [Finset.sum_congr rfl (fun i hi => Real.sq_sqrt (hx i hi)),
      Finset.sum_congr rfl (fun i hi => Real.sq_sqrt (hy i hi))] at h
  have hnn : (0:ℝ) ≤ ∑ i ∈ s, Real.sqrt (x i) * Real.sqrt (y i) :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  have hX : (0:ℝ) ≤ ∑ i ∈ s, x i := Finset.sum_nonneg hx
  rw [← Real.sqrt_sq hnn, ← Real.sqrt_mul hX]
  exact Real.sqrt_le_sqrt h

/-- The `‖γ‖²`-factor of the Cauchy–Schwarz step. -/
lemma wdg_sum_normSq_gamma_pair (d1 d2 : ℕ) (γ : ℕ → ℕ → ℂ) :
    (∑ a ∈ Finset.range (Nat.lcm d1 d2),
        ‖γ (a % d1) d1 * (starRingEnd ℂ) (γ (a % d2) d2)‖ ^ 2)
      = ∑ a ∈ Finset.range (Nat.lcm d1 d2),
          Complex.normSq (γ (a % d1) d1) * Complex.normSq (γ (a % d2) d2) := by
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_mul, Complex.normSq_conj]

/-- The local-variance factor of the Cauchy–Schwarz step. -/
lemma wdg_sum_normSq_KK (F : ℝ → ℂ) (R d1 d2 : ℕ) :
    (∑ a ∈ Finset.range (Nat.lcm d1 d2), ‖KK F R d1 d2 a‖ ^ 2) = Wloc F R d1 d2 := by
  unfold Work.FIArea4.Wloc
  exact Finset.sum_congr rfl (fun a _ => (Complex.normSq_eq_norm_sq _).symm)

/-- **The Cauchy–Schwarz reduction.**  The non-flat bilinear form is bounded by the square root of
the `γ`-energy (summed over all pairs) times the square root of the summed local variance. -/
lemma wdg_cs_nonflat (F : ℝ → ℂ) (D R : ℕ) (γ : ℕ → ℕ → ℂ) :
    ‖∑ d1 ∈ Finset.Ioc D (2*D), ∑ d2 ∈ (Finset.Ioc D (2*D)).filter (fun d2 => Nat.sqrt (Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2) ^ 2 ≠ Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2),
        ∑ a ∈ Finset.range (Nat.lcm d1 d2),
          γ (a % d1) d1 * (starRingEnd ℂ) (γ (a % d2) d2) *
            KK (F) R d1 d2 a‖
      ≤ Real.sqrt (∑ d1 ∈ Finset.Ioc D (2*D), ∑ d2 ∈ Finset.Ioc D (2*D),
              ∑ a ∈ Finset.range (Nat.lcm d1 d2),
                Complex.normSq (γ (a % d1) d1) * Complex.normSq (γ (a % d2) d2))
        * Real.sqrt (∑ d1 ∈ Finset.Ioc D (2*D),
              ∑ d2 ∈ (Finset.Ioc D (2*D)).filter (fun d2 => Nat.sqrt (Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2) ^ 2 ≠ Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2),
                Wloc (F) R d1 d2) := by
  have hstep1 : ‖∑ d1 ∈ Finset.Ioc D (2*D),
        ∑ d2 ∈ (Finset.Ioc D (2*D)).filter (fun d2 => Nat.sqrt (Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2) ^ 2 ≠ Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2),
        ∑ a ∈ Finset.range (Nat.lcm d1 d2),
          γ (a % d1) d1 * (starRingEnd ℂ) (γ (a % d2) d2) *
            KK (F) R d1 d2 a‖
      ≤ ∑ d1 ∈ Finset.Ioc D (2*D), ∑ d2 ∈ (Finset.Ioc D (2*D)).filter (fun d2 => Nat.sqrt (Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2) ^ 2 ≠ Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2),
          ‖∑ a ∈ Finset.range (Nat.lcm d1 d2),
            γ (a % d1) d1 * (starRingEnd ℂ) (γ (a % d2) d2) *
              KK (F) R d1 d2 a‖ := by
    calc ‖∑ d1 ∈ Finset.Ioc D (2*D),
          ∑ d2 ∈ (Finset.Ioc D (2*D)).filter (fun d2 => Nat.sqrt (Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2) ^ 2 ≠ Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2),
          ∑ a ∈ Finset.range (Nat.lcm d1 d2),
            γ (a % d1) d1 * (starRingEnd ℂ) (γ (a % d2) d2) *
              KK (F) R d1 d2 a‖
        ≤ ∑ d1 ∈ Finset.Ioc D (2*D),
            ‖∑ d2 ∈ (Finset.Ioc D (2*D)).filter (fun d2 => Nat.sqrt (Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2) ^ 2 ≠ Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2),
              ∑ a ∈ Finset.range (Nat.lcm d1 d2),
                γ (a % d1) d1 * (starRingEnd ℂ) (γ (a % d2) d2) *
                  KK (F) R d1 d2 a‖ := norm_sum_le _ _
      _ ≤ ∑ d1 ∈ Finset.Ioc D (2*D), ∑ d2 ∈ (Finset.Ioc D (2*D)).filter (fun d2 => Nat.sqrt (Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2) ^ 2 ≠ Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2),
            ‖∑ a ∈ Finset.range (Nat.lcm d1 d2),
              γ (a % d1) d1 * (starRingEnd ℂ) (γ (a % d2) d2) *
                KK (F) R d1 d2 a‖ :=
          Finset.sum_le_sum (fun d1 _ => norm_sum_le _ _)
  have hstep2 : (∑ d1 ∈ Finset.Ioc D (2*D),
        ∑ d2 ∈ (Finset.Ioc D (2*D)).filter (fun d2 => Nat.sqrt (Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2) ^ 2 ≠ Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2),
          ‖∑ a ∈ Finset.range (Nat.lcm d1 d2),
            γ (a % d1) d1 * (starRingEnd ℂ) (γ (a % d2) d2) *
              KK (F) R d1 d2 a‖)
      ≤ ∑ d1 ∈ Finset.Ioc D (2*D), ∑ d2 ∈ (Finset.Ioc D (2*D)).filter (fun d2 => Nat.sqrt (Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2) ^ 2 ≠ Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2),
          Real.sqrt (∑ a ∈ Finset.range (Nat.lcm d1 d2),
              Complex.normSq (γ (a % d1) d1) * Complex.normSq (γ (a % d2) d2))
            * Real.sqrt (Wloc (F) R d1 d2) := by
    refine Finset.sum_le_sum (fun d1 _ => Finset.sum_le_sum (fun d2 _ => ?_))
    refine (wdg_norm_sum_mul_le_sqrt (Finset.range (Nat.lcm d1 d2))
      (fun a => γ (a % d1) d1 * (starRingEnd ℂ) (γ (a % d2) d2))
      (fun a => KK (F) R d1 d2 a)).trans ?_
    rw [wdg_sum_normSq_gamma_pair d1 d2 γ, wdg_sum_normSq_KK]
  have hstep3 : (∑ d1 ∈ Finset.Ioc D (2*D),
        ∑ d2 ∈ (Finset.Ioc D (2*D)).filter (fun d2 => Nat.sqrt (Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2) ^ 2 ≠ Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2),
          Real.sqrt (∑ a ∈ Finset.range (Nat.lcm d1 d2),
              Complex.normSq (γ (a % d1) d1) * Complex.normSq (γ (a % d2) d2))
            * Real.sqrt (Wloc (F) R d1 d2))
      ≤ ∑ d1 ∈ Finset.Ioc D (2*D),
          Real.sqrt (∑ d2 ∈ (Finset.Ioc D (2*D)).filter (fun d2 => Nat.sqrt (Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2) ^ 2 ≠ Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2),
              ∑ a ∈ Finset.range (Nat.lcm d1 d2),
                Complex.normSq (γ (a % d1) d1) * Complex.normSq (γ (a % d2) d2))
            * Real.sqrt (∑ d2 ∈ (Finset.Ioc D (2*D)).filter (fun d2 => Nat.sqrt (Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2) ^ 2 ≠ Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2),
                Wloc (F) R d1 d2) := by
    refine Finset.sum_le_sum (fun d1 _ => ?_)
    exact wdg_sum_sqrt_mul_le_sqrt _
      (fun d2 => ∑ a ∈ Finset.range (Nat.lcm d1 d2),
        Complex.normSq (γ (a % d1) d1) * Complex.normSq (γ (a % d2) d2))
      (fun d2 => Wloc (F) R d1 d2)
      (fun d2 _ => Finset.sum_nonneg
        (fun a _ => mul_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)))
      (fun d2 _ => Finset.sum_nonneg (fun a _ => Complex.normSq_nonneg _))
  have hstep4 : (∑ d1 ∈ Finset.Ioc D (2*D),
          Real.sqrt (∑ d2 ∈ (Finset.Ioc D (2*D)).filter (fun d2 => Nat.sqrt (Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2) ^ 2 ≠ Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2),
              ∑ a ∈ Finset.range (Nat.lcm d1 d2),
                Complex.normSq (γ (a % d1) d1) * Complex.normSq (γ (a % d2) d2))
            * Real.sqrt (∑ d2 ∈ (Finset.Ioc D (2*D)).filter (fun d2 => Nat.sqrt (Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2) ^ 2 ≠ Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2),
                Wloc (F) R d1 d2))
      ≤ Real.sqrt (∑ d1 ∈ Finset.Ioc D (2*D),
            ∑ d2 ∈ (Finset.Ioc D (2*D)).filter (fun d2 => Nat.sqrt (Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2) ^ 2 ≠ Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2),
              ∑ a ∈ Finset.range (Nat.lcm d1 d2),
                Complex.normSq (γ (a % d1) d1) * Complex.normSq (γ (a % d2) d2))
        * Real.sqrt (∑ d1 ∈ Finset.Ioc D (2*D),
              ∑ d2 ∈ (Finset.Ioc D (2*D)).filter (fun d2 => Nat.sqrt (Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2) ^ 2 ≠ Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2),
                Wloc (F) R d1 d2) := by
    exact wdg_sum_sqrt_mul_le_sqrt _
      (fun d1 => ∑ d2 ∈ (Finset.Ioc D (2*D)).filter (fun d2 => Nat.sqrt (Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2) ^ 2 ≠ Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2),
        ∑ a ∈ Finset.range (Nat.lcm d1 d2),
          Complex.normSq (γ (a % d1) d1) * Complex.normSq (γ (a % d2) d2))
      (fun d1 => ∑ d2 ∈ (Finset.Ioc D (2*D)).filter (fun d2 => Nat.sqrt (Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2) ^ 2 ≠ Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2),
        Wloc (F) R d1 d2)
      (fun d1 _ => Finset.sum_nonneg (fun d2 _ => Finset.sum_nonneg
        (fun a _ => mul_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _))))
      (fun d1 _ => Finset.sum_nonneg (fun d2 _ => Finset.sum_nonneg
        (fun a _ => Complex.normSq_nonneg _)))
  have hstep5 : Real.sqrt (∑ d1 ∈ Finset.Ioc D (2*D),
          ∑ d2 ∈ (Finset.Ioc D (2*D)).filter (fun d2 => Nat.sqrt (Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2) ^ 2 ≠ Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2),
            ∑ a ∈ Finset.range (Nat.lcm d1 d2),
              Complex.normSq (γ (a % d1) d1) * Complex.normSq (γ (a % d2) d2))
      ≤ Real.sqrt (∑ d1 ∈ Finset.Ioc D (2*D), ∑ d2 ∈ Finset.Ioc D (2*D),
            ∑ a ∈ Finset.range (Nat.lcm d1 d2),
              Complex.normSq (γ (a % d1) d1) * Complex.normSq (γ (a % d2) d2)) := by
    refine Real.sqrt_le_sqrt ?_
    refine Finset.sum_le_sum (fun d1 _ => ?_)
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun d2 _ _ => ?_)
    exact Finset.sum_nonneg (fun a _ => mul_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _))
  exact hstep1.trans (hstep2.trans (hstep3.trans (hstep4.trans
    (mul_le_mul_of_nonneg_right hstep5 (Real.sqrt_nonneg _)))))


/-! ## Sum-linearity and arithmetic helpers for the assembly -/

lemma wdg_sum_const_mul_add {ι : Type*} (s : Finset ι) (A S2 : ℝ) (X Y : ι → ℝ) :
    (∑ i ∈ s, A * (S2 * X i + Y i)) = A * (S2 * (∑ i ∈ s, X i) + ∑ i ∈ s, Y i) := by
  have h1 : (∑ i ∈ s, A * (S2 * X i + Y i)) = ∑ i ∈ s, (A * (S2 * X i) + A * Y i) :=
    Finset.sum_congr rfl (fun i _ => mul_add A (S2 * X i) (Y i))
  rw [h1, Finset.sum_add_distrib, mul_add]
  congr 1
  · rw [Finset.sum_congr rfl (fun i _ => show A * (S2 * X i) = (A*S2) * X i by ring),
      ← Finset.mul_sum]
    ring
  · rw [← Finset.mul_sum]

lemma wdg_sum_mul_const {ι : Type*} (s : Finset ι) (T : ι → Finset ℕ) (c : ι → ℕ → ℝ) (k : ℝ) :
    (∑ i ∈ s, ∑ j ∈ T i, k * c i j) = k * (∑ i ∈ s, ∑ j ∈ T i, c i j) := by
  have h1 : ∀ i ∈ s, (∑ j ∈ T i, k * c i j) = k * (∑ j ∈ T i, c i j) := by
    intro i _
    exact (Finset.mul_sum (T i) (fun j => c i j) k).symm
  rw [Finset.sum_congr rfl h1]
  exact (Finset.mul_sum s (fun i => ∑ j ∈ T i, c i j) k).symm

lemma wdg_sum_two_mul_add {ι : Type*} (s : Finset ι) (T : ι → Finset ℕ)
    (c A B : ι → ℕ → ℝ) :
    (∑ i ∈ s, ∑ j ∈ T i, 2 * (c i j * (A i j + B i j)))
      = 2 * ((∑ i ∈ s, ∑ j ∈ T i, c i j * A i j)
             + (∑ i ∈ s, ∑ j ∈ T i, c i j * B i j)) := by
  rw [Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl
      (fun j _ => show 2 * (c i j * (A i j + B i j))
        = 2 * (c i j * A i j) + 2 * (c i j * B i j) by ring))]
  simp only [Finset.sum_add_distrib]
  rw [wdg_sum_mul_const s T (fun i j => c i j * A i j) 2,
      wdg_sum_mul_const s T (fun i j => c i j * B i j) 2]
  ring

/-- A flat algebraic combination step for the final assembly. -/
lemma wdg_combine_alg (A P P2 Q T X1 X2 Cb : ℝ) (hA : 0 ≤ A) (hQ : 0 ≤ Q) (hT : 0 ≤ T)
    (hX1 : 0 ≤ X1) (hX2 : 0 ≤ X2) (hCb : 0 ≤ Cb)
    (hP : P * P2 ≤ Q * T) (hP' : P ≤ Q * T) :
    A * P * (X1 * Cb * P2 + X2) ≤ A * Q * (Cb + 1) * (X1 + X2) * T := by
  have h1 : A * P * (X1 * Cb * P2 + X2) = A * (X1 * Cb * (P * P2) + X2 * P) := by ring
  rw [h1]
  have h2 : X1 * Cb * (P * P2) ≤ X1 * Cb * (Q * T) :=
    mul_le_mul_of_nonneg_left hP (mul_nonneg hX1 hCb)
  have h3 : X2 * P ≤ X2 * (Q * T) := mul_le_mul_of_nonneg_left hP' hX2
  have h4 : X1 * Cb + X2 ≤ (Cb + 1) * (X1 + X2) := by
    nlinarith [hX1, hX2, hCb, mul_nonneg hX1 hCb]
  calc A * (X1 * Cb * (P * P2) + X2 * P)
      ≤ A * (X1 * Cb * (Q * T) + X2 * (Q * T)) := by
        apply mul_le_mul_of_nonneg_left _ hA; linarith
    _ = A * Q * T * (X1 * Cb + X2) := by ring
    _ ≤ A * Q * T * ((Cb + 1) * (X1 + X2)) := by
        apply mul_le_mul_of_nonneg_left h4 (by positivity)
    _ = A * Q * (Cb + 1) * (X1 + X2) * T := by ring

lemma wdg_rpow_two_quarter (ε : ℝ) :
    (4:ℝ)^(ε/4) * (4:ℝ)^(ε/4) = (4:ℝ)^(ε/2) := by
  rw [← Real.rpow_add (by norm_num : (0:ℝ) < 4)]
  congr 1
  ring

/-- The arithmetic combination of the local-variance bound and the character-sum bound. -/
lemma wdg_combine_step (C1 C0 C2 ε : ℝ) (hC1 : 0 ≤ C1) (hC0 : 0 ≤ C0) (hC2 : 0 ≤ C2) (hε : 0 < ε)
    (D R S : ℕ) (hD : 1 ≤ D) (hR : 1 ≤ R) :
    C1 * C0^2 * (4*(D:ℝ)^2*(R:ℝ))^(ε/4) *
        ((S:ℝ)^2 * (2 * C2 * ((2:ℝ)^((3:ℝ)/2) + 1) * (R:ℝ)^((3:ℝ)/2) * (4*(D:ℝ)*(R:ℝ))^(ε/4))
          + (D:ℝ)^2 * ((R:ℝ)+(S:ℝ))*(R:ℝ))
      ≤ C1 * C0^2 * (4:ℝ)^(ε/2) * (2 * C2 * ((2:ℝ)^((3:ℝ)/2) + 1) + 1) *
          ((S:ℝ)^2 * (R:ℝ)^((3:ℝ)/2) + (D:ℝ)^2 * ((R:ℝ)+(S:ℝ))*(R:ℝ)) * ((D:ℝ)*(R:ℝ))^ε := by
  have hD0 : (0:ℝ) < (D:ℝ) := by exact_mod_cast (by omega : 0 < D)
  have hR0 : (0:ℝ) < (R:ℝ) := by exact_mod_cast (by omega : 0 < R)
  have hD1 : (1:ℝ) ≤ (D:ℝ) := by exact_mod_cast hD
  have hR1 : (1:ℝ) ≤ (R:ℝ) := by exact_mod_cast hR
  have hP : (4*(D:ℝ)^2*(R:ℝ))^(ε/4) * (4*(D:ℝ)*(R:ℝ))^(ε/4)
      ≤ (4:ℝ)^(ε/2) * ((D:ℝ)*(R:ℝ))^ε := by
    have h := wdg_rpow_quarter_mul_le 4 (by norm_num) D R hD hR ε hε
    have hexp : (4*(D:ℝ)*(R:ℝ))^(ε/4) = (4:ℝ)^(ε/4) * ((D:ℝ)*(R:ℝ))^(ε/4) := by
      rw [show (4:ℝ)*(D:ℝ)*(R:ℝ) = 4 * ((D:ℝ)*(R:ℝ)) by ring,
          Real.mul_rpow (by norm_num : (0:ℝ) ≤ 4) (by positivity : (0:ℝ) ≤ (D:ℝ)*(R:ℝ))]
    calc (4*(D:ℝ)^2*(R:ℝ))^(ε/4) * (4*(D:ℝ)*(R:ℝ))^(ε/4)
        = (4:ℝ)^(ε/4) * ((4*(D:ℝ)^2*(R:ℝ))^(ε/4) * ((D:ℝ)*(R:ℝ))^(ε/4)) := by
          rw [hexp]; ring
      _ ≤ (4:ℝ)^(ε/4) * ((4:ℝ)^(ε/4) * ((D:ℝ)*(R:ℝ))^ε) :=
          mul_le_mul_of_nonneg_left h (by positivity)
      _ = (4:ℝ)^(ε/2) * ((D:ℝ)*(R:ℝ))^ε := by
          rw [← mul_assoc, wdg_rpow_two_quarter ε]
  have hP' : (4*(D:ℝ)^2*(R:ℝ))^(ε/4) ≤ (4:ℝ)^(ε/2) * ((D:ℝ)*(R:ℝ))^ε := by
    refine (wdg_rpow_quarter_le 4 (by norm_num) D R hD hR ε hε).trans ?_
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by positivity) _)
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 4) (by linarith)
  have := wdg_combine_alg (C1*C0^2) ((4*(D:ℝ)^2*(R:ℝ))^(ε/4)) ((4*(D:ℝ)*(R:ℝ))^(ε/4))
    ((4:ℝ)^(ε/2)) (((D:ℝ)*(R:ℝ))^ε) ((S:ℝ)^2*(R:ℝ)^((3:ℝ)/2))
    ((D:ℝ)^2*((R:ℝ)+(S:ℝ))*(R:ℝ)) (2 * C2 * ((2:ℝ)^((3:ℝ)/2) + 1))
    (by positivity) (by positivity) (by positivity) (by positivity) (by positivity) (by positivity)
    hP hP'
  convert this using 2 <;> ring

/-! ## The main theorem -/

theorem Wdyad_diff_part_le_gen (S : ℕ) (F : ℝ → ℂ) (C₀ : ℝ) (hC₀ : 0 < C₀)
    (hdec : ∀ ξ : ℝ, ‖F ξ‖ ≤ C₀ * (S : ℝ) * (1 + (S : ℝ) * |ξ|) ^ (-(2 : ℝ))) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ (D R : ℕ) (γ : ℕ → ℕ → ℂ), 1 ≤ D → 1 ≤ R → 1 ≤ S →
        ‖∑ d1 ∈ Finset.Ioc D (2 * D), ∑ d2 ∈ (Finset.Ioc D (2 * D)).filter
            (fun d2 => Nat.sqrt (Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2) ^ 2
                        ≠ Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2),
          ∑ a ∈ Finset.range (Nat.lcm d1 d2),
            γ (a % d1) d1 * (starRingEnd ℂ) (γ (a % d2) d2) *
              Work.FIArea4.KK F R d1 d2 a‖
        ≤ C * (((S : ℝ) * (R : ℝ) ^ ((3 : ℝ) / 4) + (D : ℝ) * R
                + (D : ℝ) * Real.sqrt ((R : ℝ) * (S : ℝ))) * (((D : ℝ) * (R : ℝ)) ^ ε))
            * (∑ d ∈ Finset.Ioc D (2 * D), ∑ a ∈ Finset.range d, Complex.normSq (γ a d)) := by
  intro ε hε
  obtain ⟨C1, hC1pos, hC1⟩ := Wloc_bound_fresh (ε/4) (by linarith)
  have hC₀pos : (0:ℝ) < C₀ := hC₀
  obtain ⟨C2, hC2pos, hC2⟩ := Work.FIArea4.lemma_11_4 (ε/4) (by linarith)
  have hC1n : (0:ℝ) ≤ C1 := hC1pos.le
  have hC₀n : (0:ℝ) ≤ C₀ := hC₀pos.le
  have hC2n : (0:ℝ) ≤ C2 := hC2pos.le
  set C3 : ℝ := C1 * C₀^2 * (4:ℝ)^(ε/2) * (2 * C2 * ((2:ℝ)^((3:ℝ)/2) + 1) + 1) with hC3def
  refine ⟨Real.sqrt C3 + 1, by positivity, ?_⟩
  intro D R γ hD hR hS
  have hε4 : (0:ℝ) < ε/4 := by linarith
  have hε0 : (0:ℝ) ≤ ε := hε.le
  have hD1 : (1:ℝ) ≤ (D:ℝ) := by exact_mod_cast hD
  have hR1 : (1:ℝ) ≤ (R:ℝ) := by exact_mod_cast hR
  have hS1 : (1:ℝ) ≤ (S:ℝ) := by exact_mod_cast hS
  have hD0 : (0:ℝ) < (D:ℝ) := by linarith
  have hR0 : (0:ℝ) < (R:ℝ) := by linarith
  have hS0 : (0:ℝ) < (S:ℝ) := by linarith
  have hC3n : (0:ℝ) ≤ C3 := by rw [hC3def]; positivity
  have hCS := wdg_cs_nonflat F D R γ
  have hEnergy : (∑ d1 ∈ Finset.Ioc D (2*D), ∑ d2 ∈ Finset.Ioc D (2*D),
        ∑ a ∈ Finset.range (Nat.lcm d1 d2),
          Complex.normSq (γ (a % d1) d1) * Complex.normSq (γ (a % d2) d2))
      ≤ (∑ d ∈ Finset.Ioc D (2*D), ∑ a ∈ Finset.range d, Complex.normSq (γ a d))
        * (∑ d ∈ Finset.Ioc D (2*D), ∑ a ∈ Finset.range d, Complex.normSq (γ a d)) := by
    have h := Work.FIArea4.sigma_gamma_le D γ
    simpa [pow_two] using h
  have hN0 : (0:ℝ) ≤ ∑ d ∈ Finset.Ioc D (2*D), ∑ a ∈ Finset.range d, Complex.normSq (γ a d) :=
    Finset.sum_nonneg (fun d _ => Finset.sum_nonneg (fun a _ => Complex.normSq_nonneg _))
  have hsqrtE : Real.sqrt (∑ d1 ∈ Finset.Ioc D (2*D), ∑ d2 ∈ Finset.Ioc D (2*D),
        ∑ a ∈ Finset.range (Nat.lcm d1 d2),
          Complex.normSq (γ (a % d1) d1) * Complex.normSq (γ (a % d2) d2))
      ≤ ∑ d ∈ Finset.Ioc D (2*D), ∑ a ∈ Finset.range d, Complex.normSq (γ a d) := by
    rw [Real.sqrt_le_iff]
    exact ⟨hN0, by rw [pow_two]; exact hEnergy⟩
  -- per-pair local variance bound with a uniform lcm-power
  have hpair : ∀ d1 d2 : ℕ, d1 ∈ Finset.Ioc D (2*D) → d2 ∈ Finset.Ioc D (2*D) →
      Wloc (F) R d1 d2
        ≤ C1 * C₀^2 * (4 * (D:ℝ)^2 * (R:ℝ))^(ε/4) *
            ((S:ℝ)^2 * (((Nat.lcm d1 d2 : ℕ) : ℝ)⁻¹ * wdg_CSsumIoc d1 d2 R)
              + ((R:ℝ) + (S:ℝ)) * (R:ℝ)) := by
    intro d1 d2 hd1 hd2
    have hd1' : 1 ≤ d1 := by
      have h := (Finset.mem_Ioc.mp hd1).1; omega
    have hd2' : 1 ≤ d2 := by
      have h := (Finset.mem_Ioc.mp hd2).1; omega
    have hp := hC1 (S:ℝ) hS1 F C₀ hC₀pos hdec R hR d1 d2 hd1' hd2'
    have hqle : (((Nat.lcm d1 d2 : ℕ)) : ℝ) ≤ 4 * (D:ℝ)^2 := by
      have h1 : Nat.lcm d1 d2 ≤ d1 * d2 := by
        have hpos : 0 < d1 * d2 :=
          Nat.mul_pos (by have a := (Finset.mem_Ioc.mp hd1).1; omega)
                      (by have b := (Finset.mem_Ioc.mp hd2).1; omega)
        exact Nat.le_of_dvd hpos (Nat.lcm_dvd (dvd_mul_right d1 d2) (dvd_mul_left d2 d1))
      have h2 : ((d1:ℕ):ℝ) ≤ 2 * (D:ℝ) := by
        have := (Finset.mem_Ioc.mp hd1).2
        exact_mod_cast this
      have h3 : ((d2:ℕ):ℝ) ≤ 2 * (D:ℝ) := by
        have := (Finset.mem_Ioc.mp hd2).2
        exact_mod_cast this
      have h4 : ((Nat.lcm d1 d2 : ℕ) : ℝ) ≤ (d1:ℝ) * (d2:ℝ) := by exact_mod_cast h1
      have h5 : ((d1:ℕ):ℝ) * ((d2:ℕ):ℝ) ≤ (2 * (D:ℝ)) * (2 * (D:ℝ)) :=
        mul_le_mul h2 h3 (Nat.cast_nonneg d2) (by positivity)
      nlinarith [h4, h5, hD0.le]
    have hpow : (((Nat.lcm d1 d2 : ℕ) : ℝ) * (R:ℝ))^(ε/4) ≤ (4 * (D:ℝ)^2 * (R:ℝ))^(ε/4) :=
      Real.rpow_le_rpow (by positivity) (by nlinarith [hqle, hR0.le]) hε4.le
    have hbase0 : (0:ℝ) ≤ ((Nat.lcm d1 d2 : ℕ) : ℝ)⁻¹ * (S:ℝ)^2 * wdg_CSsumIoc d1 d2 R
        + ((R:ℝ) + (S:ℝ)) * (R:ℝ) := by
      have h1 : (0:ℝ) ≤ ((Nat.lcm d1 d2 : ℕ) : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
      have h2 : (0:ℝ) ≤ wdg_CSsumIoc d1 d2 R := Complex.normSq_nonneg _
      have h3 : (0:ℝ) ≤ ((R:ℝ) + (S:ℝ)) * (R:ℝ) := by positivity
      have h4 : (0:ℝ) ≤ (S:ℝ)^2 := sq_nonneg _
      nlinarith [h1, h2, h3, h4, mul_nonneg (mul_nonneg h1 h4) h2]
    have hp' : Wloc (F) R d1 d2
        ≤ C1 * C₀^2 * ((((Nat.lcm d1 d2 : ℕ) : ℝ)⁻¹ * (S:ℝ)^2 * wdg_CSsumIoc d1 d2 R
              + ((R:ℝ) + (S:ℝ)) * (R:ℝ)) * (((Nat.lcm d1 d2 : ℕ) : ℝ) * (R:ℝ))^(ε/4)) := by
      refine hp.trans (le_of_eq ?_)
      rw [wdg_CSsumIoc]
      ring
    calc Wloc (F) R d1 d2
        ≤ C1 * C₀^2 * ((((Nat.lcm d1 d2 : ℕ) : ℝ)⁻¹ * (S:ℝ)^2 * wdg_CSsumIoc d1 d2 R
              + ((R:ℝ) + (S:ℝ)) * (R:ℝ)) * (((Nat.lcm d1 d2 : ℕ) : ℝ) * (R:ℝ))^(ε/4)) := hp'
      _ ≤ C1 * C₀^2 * ((((Nat.lcm d1 d2 : ℕ) : ℝ)⁻¹ * (S:ℝ)^2 * wdg_CSsumIoc d1 d2 R
              + ((R:ℝ) + (S:ℝ)) * (R:ℝ)) * (4 * (D:ℝ)^2 * (R:ℝ))^(ε/4)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpow hbase0)
            (mul_nonneg hC1n (sq_nonneg C₀))
      _ = C1 * C₀^2 * (4 * (D:ℝ)^2 * (R:ℝ))^(ε/4) *
            ((S:ℝ)^2 * (((Nat.lcm d1 d2 : ℕ) : ℝ)⁻¹ * wdg_CSsumIoc d1 d2 R)
              + ((R:ℝ) + (S:ℝ)) * (R:ℝ)) := by ring
  have hW1 : (∑ d1 ∈ Finset.Ioc D (2*D), ∑ d2 ∈ (Finset.Ioc D (2*D)).filter
        (fun d2 => Nat.sqrt (Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2) ^ 2
                    ≠ Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2),
        Wloc (F) R d1 d2)
      ≤ ∑ d1 ∈ Finset.Ioc D (2*D), ∑ d2 ∈ (Finset.Ioc D (2*D)).filter
        (fun d2 => Nat.sqrt (Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2) ^ 2
                    ≠ Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2),
        C1 * C₀^2 * (4 * (D:ℝ)^2 * (R:ℝ))^(ε/4) *
            ((S:ℝ)^2 * (((Nat.lcm d1 d2 : ℕ) : ℝ)⁻¹ * wdg_CSsumIoc d1 d2 R)
              + ((R:ℝ) + (S:ℝ)) * (R:ℝ)) := by
    refine Finset.sum_le_sum (fun d1 hd1 => Finset.sum_le_sum (fun d2 hd2 => ?_))
    exact hpair d1 d2 hd1 (Finset.mem_filter.mp hd2).1
  have hW2 : (∑ d1 ∈ Finset.Ioc D (2*D), ∑ d2 ∈ (Finset.Ioc D (2*D)).filter
        (fun d2 => Nat.sqrt (Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2) ^ 2
                    ≠ Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2),
        C1 * C₀^2 * (4 * (D:ℝ)^2 * (R:ℝ))^(ε/4) *
            ((S:ℝ)^2 * (((Nat.lcm d1 d2 : ℕ) : ℝ)⁻¹ * wdg_CSsumIoc d1 d2 R)
              + ((R:ℝ) + (S:ℝ)) * (R:ℝ)))
      = C1 * C₀^2 * (4 * (D:ℝ)^2 * (R:ℝ))^(ε/4) *
          ((S:ℝ)^2 * (∑ d1 ∈ Finset.Ioc D (2*D), ∑ d2 ∈ (Finset.Ioc D (2*D)).filter
                (fun d2 => Nat.sqrt (Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2) ^ 2
                            ≠ Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2),
                ((Nat.lcm d1 d2 : ℕ) : ℝ)⁻¹ * wdg_CSsumIoc d1 d2 R)
            + (∑ d1 ∈ Finset.Ioc D (2*D), ∑ d2 ∈ (Finset.Ioc D (2*D)).filter
                (fun d2 => Nat.sqrt (Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2) ^ 2
                            ≠ Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2),
                ((R:ℝ) + (S:ℝ)) * (R:ℝ))) := by
    have step1 : ∀ d1, (∑ d2 ∈ (Finset.Ioc D (2*D)).filter
          (fun d2 => Nat.sqrt (Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2) ^ 2
                      ≠ Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2),
          C1 * C₀^2 * (4 * (D:ℝ)^2 * (R:ℝ))^(ε/4) *
              ((S:ℝ)^2 * (((Nat.lcm d1 d2 : ℕ) : ℝ)⁻¹ * wdg_CSsumIoc d1 d2 R)
                + ((R:ℝ) + (S:ℝ)) * (R:ℝ)))
        = C1 * C₀^2 * (4 * (D:ℝ)^2 * (R:ℝ))^(ε/4) *
            ((S:ℝ)^2 * (∑ d2 ∈ (Finset.Ioc D (2*D)).filter
                  (fun d2 => Nat.sqrt (Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2) ^ 2
                              ≠ Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2),
                  ((Nat.lcm d1 d2 : ℕ) : ℝ)⁻¹ * wdg_CSsumIoc d1 d2 R)
              + (∑ d2 ∈ (Finset.Ioc D (2*D)).filter
                  (fun d2 => Nat.sqrt (Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2) ^ 2
                              ≠ Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2),
                  ((R:ℝ) + (S:ℝ)) * (R:ℝ))) := by
      intro d1
      exact wdg_sum_const_mul_add _ _ _ _ _
    rw [Finset.sum_congr rfl (fun d1 _ => step1 d1)]
    exact wdg_sum_const_mul_add _ _ _ _ _

  have hSump : (∑ d1 ∈ Finset.Ioc D (2*D), ∑ d2 ∈ (Finset.Ioc D (2*D)).filter (fun d2 => Nat.sqrt (Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2) ^ 2 ≠ Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2),
        ((Nat.lcm d1 d2 : ℕ) : ℝ)⁻¹ * wdg_CSsumIoc d1 d2 R)
      ≤ 2 * C2 * ((2:ℝ)^((3:ℝ)/2) + 1) * (R:ℝ)^((3:ℝ)/2) * (4 * (D:ℝ) * (R:ℝ))^(ε/4) := by
    have step1 : (∑ d1 ∈ Finset.Ioc D (2*D), ∑ d2 ∈ (Finset.Ioc D (2*D)).filter (fun d2 => Nat.sqrt (Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2) ^ 2 ≠ Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2),
          ((Nat.lcm d1 d2 : ℕ) : ℝ)⁻¹ * wdg_CSsumIoc d1 d2 R)
        ≤ (∑ d1 ∈ Finset.Ioc D (2*D), ∑ d2 ∈ (Finset.Ioc D (2*D)).filter (fun d2 => Nat.sqrt (Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2) ^ 2 ≠ Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2),
            2 * (((Nat.lcm d1 d2 : ℕ) : ℝ)⁻¹ * (wdg_CSsum d1 d2 (2*R) + wdg_CSsum d1 d2 R))) := by
      apply Finset.sum_le_sum; intro d1 _
      apply Finset.sum_le_sum; intro d2 _
      have h := wdg_CSsumIoc_le R d1 d2
      have hl : (0:ℝ) ≤ ((Nat.lcm d1 d2 : ℕ) : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
      calc ((Nat.lcm d1 d2 : ℕ) : ℝ)⁻¹ * wdg_CSsumIoc d1 d2 R
          ≤ ((Nat.lcm d1 d2 : ℕ) : ℝ)⁻¹ * (2 * (wdg_CSsum d1 d2 (2*R) + wdg_CSsum d1 d2 R)) :=
            mul_le_mul_of_nonneg_left h hl
        _ = 2 * (((Nat.lcm d1 d2 : ℕ) : ℝ)⁻¹ * (wdg_CSsum d1 d2 (2*R) + wdg_CSsum d1 d2 R)) := by ring
    refine step1.trans ?_
    have hsplit : (∑ d1 ∈ Finset.Ioc D (2*D), ∑ d2 ∈ (Finset.Ioc D (2*D)).filter (fun d2 => Nat.sqrt (Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2) ^ 2 ≠ Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2),
          2 * (((Nat.lcm d1 d2 : ℕ) : ℝ)⁻¹ * (wdg_CSsum d1 d2 (2*R) + wdg_CSsum d1 d2 R)))
        = 2 * ((∑ d1 ∈ Finset.Ioc D (2*D), ∑ d2 ∈ (Finset.Ioc D (2*D)).filter (fun d2 => Nat.sqrt (Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2) ^ 2 ≠ Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2),
                  ((Nat.lcm d1 d2 : ℕ) : ℝ)⁻¹ * wdg_CSsum d1 d2 (2*R))
              + (∑ d1 ∈ Finset.Ioc D (2*D), ∑ d2 ∈ (Finset.Ioc D (2*D)).filter (fun d2 => Nat.sqrt (Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2) ^ 2 ≠ Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2),
                  ((Nat.lcm d1 d2 : ℕ) : ℝ)⁻¹ * wdg_CSsum d1 d2 R)) :=
      wdg_sum_two_mul_add _ _ (fun d1 d2 => ((Nat.lcm d1 d2 : ℕ) : ℝ)⁻¹)
        (fun d1 d2 => wdg_CSsum d1 d2 (2*R)) (fun d1 d2 => wdg_CSsum d1 d2 R)
    rw [hsplit]
    have henl : ∀ R' : ℕ, (∑ d1 ∈ Finset.Ioc D (2*D), ∑ d2 ∈ (Finset.Ioc D (2*D)).filter (fun d2 => Nat.sqrt (Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2) ^ 2 ≠ Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2),
            ((Nat.lcm d1 d2 : ℕ) : ℝ)⁻¹ * wdg_CSsum d1 d2 R')
        ≤ ∑ d1 ∈ Finset.Icc 1 (2*D), ∑ d2 ∈ (Finset.Icc 1 (2*D)).filter (fun d2 => Nat.sqrt (Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2) ^ 2 ≠ Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2),
            ((Nat.lcm d1 d2 : ℕ) : ℝ)⁻¹ * wdg_CSsum d1 d2 R' := by
      intro R'
      have stepA : (∑ d1 ∈ Finset.Ioc D (2*D), ∑ d2 ∈ (Finset.Ioc D (2*D)).filter (fun d2 => Nat.sqrt (Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2) ^ 2 ≠ Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2),
            ((Nat.lcm d1 d2 : ℕ) : ℝ)⁻¹ * wdg_CSsum d1 d2 R')
          ≤ ∑ d1 ∈ Finset.Ioc D (2*D), ∑ d2 ∈ (Finset.Icc 1 (2*D)).filter (fun d2 => Nat.sqrt (Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2) ^ 2 ≠ Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2),
            ((Nat.lcm d1 d2 : ℕ) : ℝ)⁻¹ * wdg_CSsum d1 d2 R' := by
        apply Finset.sum_le_sum; intro d1 _
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun d2 _ _ => ?_)
        · intro d2 hd2
          rw [Finset.mem_filter] at hd2 ⊢
          obtain ⟨hd2', hp⟩ := hd2
          have h1 := (Finset.mem_Ioc.mp hd2').1
          have h2 := (Finset.mem_Ioc.mp hd2').2
          exact ⟨by rw [Finset.mem_Icc]; omega, hp⟩
        · exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (Complex.normSq_nonneg _)
      have stepB : (∑ d1 ∈ Finset.Ioc D (2*D), ∑ d2 ∈ (Finset.Icc 1 (2*D)).filter (fun d2 => Nat.sqrt (Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2) ^ 2 ≠ Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2),
            ((Nat.lcm d1 d2 : ℕ) : ℝ)⁻¹ * wdg_CSsum d1 d2 R')
          ≤ ∑ d1 ∈ Finset.Icc 1 (2*D), ∑ d2 ∈ (Finset.Icc 1 (2*D)).filter (fun d2 => Nat.sqrt (Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2) ^ 2 ≠ Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2),
            ((Nat.lcm d1 d2 : ℕ) : ℝ)⁻¹ * wdg_CSsum d1 d2 R' := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun d1 _ _ => ?_)
        · intro d1 hd1
          rw [Finset.mem_Icc]
          have h1 := (Finset.mem_Ioc.mp hd1).1
          have h2 := (Finset.mem_Ioc.mp hd1).2
          omega
        · exact Finset.sum_nonneg (fun d2 _ =>
            mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (Complex.normSq_nonneg _))
      exact stepA.trans stepB
    have h11a := hC2 (2*D) (2*R) (by omega) (by omega)
    have h11b := hC2 (2*D) R (by omega) hR
    have hB1 : (∑ d1 ∈ Finset.Icc 1 (2*D), ∑ d2 ∈ (Finset.Icc 1 (2*D)).filter (fun d2 => Nat.sqrt (Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2) ^ 2 ≠ Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2),
            ((Nat.lcm d1 d2 : ℕ) : ℝ)⁻¹ * wdg_CSsum d1 d2 (2*R))
        ≤ C2 * (2:ℝ)^((3:ℝ)/2) * (R:ℝ)^((3:ℝ)/2) * (4 * (D:ℝ) * (R:ℝ))^(ε/4) := by
      refine h11a.trans (le_of_eq ?_)
      rw [show (((2*D : ℕ) : ℝ) * ((2*R : ℕ) : ℝ)) = 4 * (D:ℝ) * (R:ℝ) by
            push_cast; ring]
      rw [show (((2*R : ℕ) : ℝ)) = 2 * (R:ℝ) by push_cast; ring]
      rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hR0.le]
      ring
    have hB2 : (∑ d1 ∈ Finset.Icc 1 (2*D), ∑ d2 ∈ (Finset.Icc 1 (2*D)).filter (fun d2 => Nat.sqrt (Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2) ^ 2 ≠ Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2),
            ((Nat.lcm d1 d2 : ℕ) : ℝ)⁻¹ * wdg_CSsum d1 d2 R)
        ≤ C2 * (R:ℝ)^((3:ℝ)/2) * (4 * (D:ℝ) * (R:ℝ))^(ε/4) := by
      refine h11b.trans ?_
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC2n (Real.rpow_nonneg hR0.le _))
      rw [show (((2*D : ℕ) : ℝ) * ((R : ℕ) : ℝ)) = 2 * (D:ℝ) * (R:ℝ) by push_cast; ring,
          show (2 * (D:ℝ) * (R:ℝ)) = 2 * ((D:ℝ)*(R:ℝ)) by ring,
          show (4 * (D:ℝ) * (R:ℝ)) = 4 * ((D:ℝ)*(R:ℝ)) by ring]
      exact Real.rpow_le_rpow (by positivity) (by nlinarith [hD1, hR1]) hε4.le
    have h1 := (henl (2*R)).trans hB1
    have h2 := (henl R).trans hB2
    nlinarith [h1, h2, hC2n, hR0.le, Real.rpow_nonneg hR0.le ((3:ℝ)/2),
      Real.rpow_nonneg (by positivity : (0:ℝ) ≤ 4 * (D:ℝ) * (R:ℝ)) (ε/4),
      Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 2) ((3:ℝ)/2)]
  have hSumY : (∑ d1 ∈ Finset.Ioc D (2*D), ∑ d2 ∈ (Finset.Ioc D (2*D)).filter (fun d2 => Nat.sqrt (Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2) ^ 2 ≠ Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2),
        ((R:ℝ) + (S:ℝ)) * (R:ℝ)) ≤ (D:ℝ)^2 * ((R:ℝ) + (S:ℝ)) * (R:ℝ) := by
    have h1 : (∑ d1 ∈ Finset.Ioc D (2*D), ∑ d2 ∈ (Finset.Ioc D (2*D)).filter (fun d2 => Nat.sqrt (Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2) ^ 2 ≠ Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2),
          ((R:ℝ) + (S:ℝ)) * (R:ℝ))
        ≤ ∑ d1 ∈ Finset.Ioc D (2*D), ∑ _d2 ∈ Finset.Ioc D (2*D), ((R:ℝ) + (S:ℝ)) * (R:ℝ) := by
      apply Finset.sum_le_sum; intro d1 _
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun d2 _ _ => by positivity)
    refine h1.trans (le_of_eq ?_)
    have hc : ((Finset.Ioc D (2*D)).card : ℝ) = (D:ℝ) := by
      rw [Nat.card_Ioc]
      have : 2*D - D = D := by omega
      rw [this]
    rw [Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul, hc]
    ring
  have hWle : (∑ d1 ∈ Finset.Ioc D (2*D), ∑ d2 ∈ (Finset.Ioc D (2*D)).filter (fun d2 => Nat.sqrt (Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2) ^ 2 ≠ Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2),
        Wloc (F) R d1 d2)
      ≤ C1 * C₀^2 * (4 * (D:ℝ)^2 * (R:ℝ))^(ε/4) *
          ((S:ℝ)^2 * (2 * C2 * ((2:ℝ)^((3:ℝ)/2) + 1) * (R:ℝ)^((3:ℝ)/2)
              * (4 * (D:ℝ) * (R:ℝ))^(ε/4))
            + (D:ℝ)^2 * ((R:ℝ) + (S:ℝ)) * (R:ℝ)) := by
    refine hW1.trans ?_
    rw [hW2]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine add_le_add ?_ hSumY
    exact mul_le_mul_of_nonneg_left hSump (by positivity)
  have hWfin : (∑ d1 ∈ Finset.Ioc D (2*D), ∑ d2 ∈ (Finset.Ioc D (2*D)).filter (fun d2 => Nat.sqrt (Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2) ^ 2 ≠ Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2),
        Wloc (F) R d1 d2)
      ≤ C3 * ((S:ℝ)^2 * (R:ℝ)^((3:ℝ)/2)
          + (D:ℝ)^2 * ((R:ℝ) + (S:ℝ)) * (R:ℝ)) * ((D:ℝ)*(R:ℝ))^ε := by
    refine hWle.trans ?_
    rw [hC3def]
    convert wdg_combine_step C1 C₀ C2 ε hC1n hC₀n hC2n hε D R S hD hR using 2 <;> ring
  have hb0 : (0:ℝ) ≤ (S:ℝ) * (R:ℝ)^((3:ℝ)/4) + (D:ℝ) * (R:ℝ)
      + (D:ℝ) * Real.sqrt ((R:ℝ)*(S:ℝ)) := by positivity
  have hW3 : (∑ d1 ∈ Finset.Ioc D (2*D), ∑ d2 ∈ (Finset.Ioc D (2*D)).filter (fun d2 => Nat.sqrt (Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2) ^ 2 ≠ Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2),
        Wloc (F) R d1 d2)
      ≤ C3 * (((S:ℝ) * (R:ℝ)^((3:ℝ)/4) + (D:ℝ) * (R:ℝ)
      + (D:ℝ) * Real.sqrt ((R:ℝ)*(S:ℝ)))^2 * ((D:ℝ)*(R:ℝ))^ε) := by
    have h := wdg_sq_le_bracket_sq D R S hD hR
    have h2 : C3 * ((S:ℝ)^2 * (R:ℝ)^((3:ℝ)/2) + (D:ℝ)^2 * ((R:ℝ) + (S:ℝ)) * (R:ℝ))
        ≤ C3 * ((S:ℝ) * (R:ℝ)^((3:ℝ)/4) + (D:ℝ) * (R:ℝ)
      + (D:ℝ) * Real.sqrt ((R:ℝ)*(S:ℝ)))^2 := mul_le_mul_of_nonneg_left h hC3n
    have hTnn : (0:ℝ) ≤ ((D:ℝ)*(R:ℝ))^ε := Real.rpow_nonneg (by positivity) _
    have h3 := mul_le_mul_of_nonneg_right h2 hTnn
    refine hWfin.trans ?_
    calc C3 * ((S:ℝ)^2 * (R:ℝ)^((3:ℝ)/2) + (D:ℝ)^2 * ((R:ℝ) + (S:ℝ)) * (R:ℝ))
            * ((D:ℝ)*(R:ℝ))^ε
        = (C3 * ((S:ℝ)^2 * (R:ℝ)^((3:ℝ)/2) + (D:ℝ)^2 * ((R:ℝ) + (S:ℝ)) * (R:ℝ)))
            * ((D:ℝ)*(R:ℝ))^ε := by ring
      _ ≤ (C3 * ((S:ℝ) * (R:ℝ)^((3:ℝ)/4) + (D:ℝ) * (R:ℝ)
      + (D:ℝ) * Real.sqrt ((R:ℝ)*(S:ℝ)))^2) * ((D:ℝ)*(R:ℝ))^ε := h3
      _ = C3 * (((S:ℝ) * (R:ℝ)^((3:ℝ)/4) + (D:ℝ) * (R:ℝ)
      + (D:ℝ) * Real.sqrt ((R:ℝ)*(S:ℝ)))^2 * ((D:ℝ)*(R:ℝ))^ε) := by ring
  have hsqrtW : Real.sqrt (∑ d1 ∈ Finset.Ioc D (2*D), ∑ d2 ∈ (Finset.Ioc D (2*D)).filter (fun d2 => Nat.sqrt (Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2) ^ 2 ≠ Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2),
        Wloc (F) R d1 d2)
      ≤ Real.sqrt C3 * ((S:ℝ) * (R:ℝ)^((3:ℝ)/4) + (D:ℝ) * (R:ℝ)
      + (D:ℝ) * Real.sqrt ((R:ℝ)*(S:ℝ))) * ((D:ℝ)*(R:ℝ))^(ε/2) := by
    calc Real.sqrt (∑ d1 ∈ Finset.Ioc D (2*D), ∑ d2 ∈ (Finset.Ioc D (2*D)).filter (fun d2 => Nat.sqrt (Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2) ^ 2 ≠ Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2),
        Wloc (F) R d1 d2)
        ≤ Real.sqrt (C3 * (((S:ℝ) * (R:ℝ)^((3:ℝ)/4) + (D:ℝ) * (R:ℝ)
      + (D:ℝ) * Real.sqrt ((R:ℝ)*(S:ℝ)))^2 * ((D:ℝ)*(R:ℝ))^ε)) := Real.sqrt_le_sqrt hW3
      _ = Real.sqrt C3 * (Real.sqrt (((S:ℝ) * (R:ℝ)^((3:ℝ)/4) + (D:ℝ) * (R:ℝ)
      + (D:ℝ) * Real.sqrt ((R:ℝ)*(S:ℝ)))^2) * Real.sqrt (((D:ℝ)*(R:ℝ))^ε)) := by
          rw [Real.sqrt_mul hC3n, Real.sqrt_mul (sq_nonneg _)]
      _ = Real.sqrt C3 * (((S:ℝ) * (R:ℝ)^((3:ℝ)/4) + (D:ℝ) * (R:ℝ)
      + (D:ℝ) * Real.sqrt ((R:ℝ)*(S:ℝ))) * Real.sqrt (((D:ℝ)*(R:ℝ))^ε)) := by
          rw [Real.sqrt_sq hb0]
      _ = Real.sqrt C3 * (((S:ℝ) * (R:ℝ)^((3:ℝ)/4) + (D:ℝ) * (R:ℝ)
      + (D:ℝ) * Real.sqrt ((R:ℝ)*(S:ℝ))) * ((D:ℝ)*(R:ℝ))^(ε/2)) := by
          have hs : Real.sqrt (((D:ℝ)*(R:ℝ))^ε) = ((D:ℝ)*(R:ℝ))^(ε/2) := by
            rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity : (0:ℝ) ≤ (D:ℝ)*(R:ℝ)),
                show ε * (1/2) = ε/2 by ring]
          rw [hs]
      _ = Real.sqrt C3 * ((S:ℝ) * (R:ℝ)^((3:ℝ)/4) + (D:ℝ) * (R:ℝ)
      + (D:ℝ) * Real.sqrt ((R:ℝ)*(S:ℝ))) * ((D:ℝ)*(R:ℝ))^(ε/2) := by ring
  have hT : ((D:ℝ)*(R:ℝ))^(ε/2) ≤ ((D:ℝ)*(R:ℝ))^ε :=
    Real.rpow_le_rpow_of_exponent_le (by nlinarith [hD1, hR1]) (by linarith)
  calc ‖∑ d1 ∈ Finset.Ioc D (2*D), ∑ d2 ∈ (Finset.Ioc D (2*D)).filter (fun d2 => Nat.sqrt (Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2) ^ 2 ≠ Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2),
        ∑ a ∈ Finset.range (Nat.lcm d1 d2),
          γ (a % d1) d1 * (starRingEnd ℂ) (γ (a % d2) d2) *
            KK (F) R d1 d2 a‖
      ≤ Real.sqrt (∑ d1 ∈ Finset.Ioc D (2*D), ∑ d2 ∈ Finset.Ioc D (2*D),
              ∑ a ∈ Finset.range (Nat.lcm d1 d2),
                Complex.normSq (γ (a % d1) d1) * Complex.normSq (γ (a % d2) d2))
          * Real.sqrt (∑ d1 ∈ Finset.Ioc D (2*D), ∑ d2 ∈ (Finset.Ioc D (2*D)).filter (fun d2 => Nat.sqrt (Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2) ^ 2 ≠ Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2),
        Wloc (F) R d1 d2) := hCS
    _ ≤ (∑ d ∈ Finset.Ioc D (2*D), ∑ a ∈ Finset.range d, Complex.normSq (γ a d)) * Real.sqrt (∑ d1 ∈ Finset.Ioc D (2*D), ∑ d2 ∈ (Finset.Ioc D (2*D)).filter (fun d2 => Nat.sqrt (Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2) ^ 2 ≠ Work.FIPlan.oddPart d1 * Work.FIPlan.oddPart d2),
        Wloc (F) R d1 d2) :=
        mul_le_mul_of_nonneg_right hsqrtE (Real.sqrt_nonneg _)
    _ ≤ (∑ d ∈ Finset.Ioc D (2*D), ∑ a ∈ Finset.range d, Complex.normSq (γ a d)) * (Real.sqrt C3 * ((S:ℝ) * (R:ℝ)^((3:ℝ)/4) + (D:ℝ) * (R:ℝ)
      + (D:ℝ) * Real.sqrt ((R:ℝ)*(S:ℝ))) * ((D:ℝ)*(R:ℝ))^(ε/2)) :=
        mul_le_mul_of_nonneg_left hsqrtW hN0
    _ ≤ (Real.sqrt C3 + 1) * (((S:ℝ) * (R:ℝ)^((3:ℝ)/4) + (D:ℝ) * (R:ℝ)
      + (D:ℝ) * Real.sqrt ((R:ℝ)*(S:ℝ))) * ((D:ℝ)*(R:ℝ))^ε) * (∑ d ∈ Finset.Ioc D (2*D), ∑ a ∈ Finset.range d, Complex.normSq (γ a d)) := by
        have hTnn : (0:ℝ) ≤ ((D:ℝ)*(R:ℝ))^ε := Real.rpow_nonneg (by positivity) _
        have h1 : (∑ d ∈ Finset.Ioc D (2*D), ∑ a ∈ Finset.range d, Complex.normSq (γ a d)) * (Real.sqrt C3 * ((S:ℝ) * (R:ℝ)^((3:ℝ)/4) + (D:ℝ) * (R:ℝ)
      + (D:ℝ) * Real.sqrt ((R:ℝ)*(S:ℝ))) * ((D:ℝ)*(R:ℝ))^(ε/2))
            ≤ (∑ d ∈ Finset.Ioc D (2*D), ∑ a ∈ Finset.range d, Complex.normSq (γ a d)) * (Real.sqrt C3 * ((S:ℝ) * (R:ℝ)^((3:ℝ)/4) + (D:ℝ) * (R:ℝ)
      + (D:ℝ) * Real.sqrt ((R:ℝ)*(S:ℝ))) * ((D:ℝ)*(R:ℝ))^ε) := by
          apply mul_le_mul_of_nonneg_left _ hN0
          exact mul_le_mul_of_nonneg_left hT (mul_nonneg (Real.sqrt_nonneg C3) hb0)
        have h2 : (∑ d ∈ Finset.Ioc D (2*D), ∑ a ∈ Finset.range d, Complex.normSq (γ a d)) * (Real.sqrt C3 * ((S:ℝ) * (R:ℝ)^((3:ℝ)/4) + (D:ℝ) * (R:ℝ)
      + (D:ℝ) * Real.sqrt ((R:ℝ)*(S:ℝ))) * ((D:ℝ)*(R:ℝ))^ε)
            ≤ (Real.sqrt C3 + 1) * (((S:ℝ) * (R:ℝ)^((3:ℝ)/4) + (D:ℝ) * (R:ℝ)
      + (D:ℝ) * Real.sqrt ((R:ℝ)*(S:ℝ))) * ((D:ℝ)*(R:ℝ))^ε) * (∑ d ∈ Finset.Ioc D (2*D), ∑ a ∈ Finset.range d, Complex.normSq (γ a d)) := by
          nlinarith [hTnn, hN0, hb0, Real.sqrt_nonneg C3,
            mul_nonneg hN0 (mul_nonneg hb0 hTnn), mul_nonneg (mul_nonneg hb0 hTnn) hN0]
        exact h1.trans h2


end

end Work.FIArea4.Vflip
