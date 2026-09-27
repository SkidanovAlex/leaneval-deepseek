import Mathlib
import Submission.Work.EQ.Defs

namespace Work.EQ

open Filter Complex Metric

/-- The explicit formula for `germPt` on the real axis (in terms of `B t = h t/t` and
`C t = h (λ t)/t`) tends to `A₁ = -1/2` as `t → 0⁺`, when `B → -1` and `C → -λ`. -/
lemma tendsto_germPt_formula {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {B C : ℝ → ℝ}
    (hB : Filter.Tendsto B (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds (-1)))
    (hC : Filter.Tendsto C (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds (-(eqLam a)))) :
    Filter.Tendsto (fun t : ℝ => (((a * C t / (C t - B t) - a / 2 : ℝ)) : ℂ) +
        (((a * t * B t * C t / (C t - B t) : ℝ)) : ℂ) * Complex.I)
      (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds ((-(1 / 2) : ℝ) : ℂ)) := by
  set l : Filter ℝ := nhdsWithin (0:ℝ) (Set.Ioi 0) with hl
  -- `λ = eqLam a > 0` and the resonance identity `1 - λ = a (1 + λ)`.
  have hlampos : 0 < eqLam a := by unfold eqLam; exact div_pos (by linarith) (by linarith)
  have hsub : 1 - eqLam a = a * (1 + eqLam a) := by
    unfold eqLam; field_simp; ring
  have hDne : 1 - eqLam a ≠ 0 := by
    rw [hsub]; exact ne_of_gt (mul_pos ha0 (by linarith))
  -- `C t - B t → 1 - λ`, hence is eventually nonzero.
  have hD : Tendsto (fun t => C t - B t) l (nhds (1 - eqLam a)) := by
    have h := hC.sub hB
    convert h using 2
    ring
  have hevne : ∀ᶠ t in l, C t - B t ≠ 0 := by
    filter_upwards [hD.eventually (isOpen_ne.mem_nhds hDne)] with t ht
    exact ht
  -- The limiting value of the real part.
  have hval : (a * (-(eqLam a)) / 2 + a * (-1) / 2) / (1 - eqLam a) = -(1/2) := by
    rw [show a * (-(eqLam a)) / 2 + a * (-1) / 2 = -(a * (1 + eqLam a) / 2) by ring, hsub]
    field_simp
  -- Real part: `a C/(C-B) - a/2 = (a(C+B)/2)/(C-B) → -1/2`.
  have hRlim : Tendsto (fun t => a * C t / (C t - B t) - a / 2) l (nhds (-(1/2))) := by
    have hnum : Tendsto (fun t => a * C t / 2 + a * B t / 2) l
        (nhds (a * (-(eqLam a)) / 2 + a * (-1) / 2)) :=
      ((hC.const_mul a).div_const 2).add ((hB.const_mul a).div_const 2)
    have hratio : Tendsto (fun t => (a * C t / 2 + a * B t / 2) / (C t - B t)) l
        (nhds ((a * (-(eqLam a)) / 2 + a * (-1) / 2) / (1 - eqLam a))) :=
      hnum.div hD hDne
    rw [hval] at hratio
    refine Filter.Tendsto.congr' ?_ hratio
    filter_upwards [hevne] with t ht
    field_simp
    ring
  -- Imaginary part: `a t B C/(C-B) = t · (a B C/(C-B)) → 0`.
  have hIlim : Tendsto (fun t => a * t * B t * C t / (C t - B t)) l (nhds 0) := by
    have hl_le : l ≤ nhds (0:ℝ) := by rw [hl]; exact nhdsWithin_le_nhds
    have htt : Tendsto (fun t : ℝ => t) l (nhds (0:ℝ)) := tendsto_id.mono_left hl_le
    have hfac : Tendsto (fun t => a * B t * C t / (C t - B t)) l
        (nhds (a * (-1) * (-(eqLam a)) / (1 - eqLam a))) := by
      have hBC : Tendsto (fun t => a * B t * C t) l (nhds (a * (-1) * (-(eqLam a)))) :=
        (hB.const_mul a).mul hC
      exact hBC.div hD hDne
    have hprod : Tendsto (fun t => t * (a * B t * C t / (C t - B t))) l
        (nhds ((0:ℝ) * (a * (-1) * (-(eqLam a)) / (1 - eqLam a)))) := htt.mul hfac
    rw [show (0:ℝ) * (a * (-1) * (-(eqLam a)) / (1 - eqLam a)) = 0 by ring] at hprod
    refine Filter.Tendsto.congr' ?_ hprod
    filter_upwards [hevne] with t ht
    field_simp
  -- Assembly in `ℂ`.
  have hreal : Tendsto (fun t => (((a * C t / (C t - B t) - a / 2 : ℝ)) : ℂ)) l
      (nhds ((-(1/2) : ℝ) : ℂ)) :=
    (Complex.continuous_ofReal.tendsto (-(1/2))).comp hRlim
  have himag : Tendsto (fun t => (((a * t * B t * C t / (C t - B t) : ℝ)) : ℂ) * Complex.I) l
      (nhds (0:ℂ)) := by
    have h1 : Tendsto (fun t => (((a * t * B t * C t / (C t - B t) : ℝ)) : ℂ)) l
        (nhds ((0:ℝ) : ℂ)) :=
      (Complex.continuous_ofReal.tendsto (0:ℝ)).comp hIlim
    have h2 := h1.mul_const Complex.I
    simpa using h2
  have hsum := hreal.add himag
  simpa using hsum

end Work.EQ
