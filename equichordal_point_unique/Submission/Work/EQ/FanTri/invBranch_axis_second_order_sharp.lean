import Mathlib
import Submission.Work.EQ.DefsCore
import Submission.Work.EQ.FanSep.Defs
import Submission.Work.EQ.FanSep.centre_numbers
import Submission.Work.EQ.FanSep.sqrt_step
import Submission.Work.EQ.SqrtNearOne
import Submission.Work.EQ.FanTri.invBranchDefs
import Submission.Work.EQ.FanTri.invBranch_eq_unitDir

set_option maxHeartbeats 8000000

namespace Work.EQ.FanTri

open Work.EQ Complex

noncomputable section

/-- **Sharp second-order one-step expansion of a backward branch at an arbitrary axis point.**
There is `C > 0` (depending only on `a`) such that for every axis point `c = -1/2 + 2k` of the
equichordal grid, every branch sign `s`, and every deviation `p` with `‖p‖ ≤ (1-a)/8`, the
difference `X = invBranch a s ((c,0) + p) - invBranch a s ((c,0))` satisfies the coordinate-wise
sharp second-order estimate with linearisation `p ↦ (-p.1, (-1 + sgnB s/|c+a/2|)·p.2)`:
`‖X.1 + p.1‖ ≤ C·‖p.2‖²/|c+a/2|²` and `‖X.2 - (-1 + sgnB s/|c+a/2|)·p.2‖ ≤ C·‖p.2‖·‖p‖/|c+a/2|²`.
The first error is controlled by `‖p.2‖` alone (not by `‖p‖`), which is essential for the
composition induction of `Work.EQ.FanTri.branchComp_radius`.

Concrete route (all pieces are elementary; `C = 16` is more than enough, the reviewers computed
`sup‖X.1+p.1‖/(‖p.2‖²/q²) ≤ 0.94` and `sup‖X.2-σp.2‖/(‖p.2‖‖p‖/q²) ≤ 1.58` numerically).
Write `C₀ := c + a/2 ∈ ℝ`, `q := |C₀| ≥ (1-a)/2`, `μ := sgnB s`, `ς := if 0 < C₀ then (1:ℝ) else -1`
(so `ς² = 1` and `ςC₀ = q`), `ζ := Q.1 + a/2` with `Q := (c,0) + p`, `y := p.2`.  Then
`ζ = C₀ + p.1`, `‖ζ‖ ≥ 3q/4`, and with `D := ς*ζ` (so `0 < D.re`, `|D.im| ≤ D.re/2`, `‖y‖ ≤ ‖D‖/2`)
the principal-square-root step `FanSep.sqrt_step` gives
`ρ' := (ζ²+y²)^{1/2} = D * sqHalf ((y/D)²) =: D*s` (use `ς² = 1` to identify `(ςζ)² = ζ²`).
Consequences: `s² = 1 + (y/ζ)²` and `‖s - 1‖ ≤ 2‖y/ζ‖²`, hence `7/9 ≤ ‖s‖` (from `‖y/ζ‖ ≤ 1/3`).
From `invBranch`'s definition: `X.1 + p.1 = μς(1/s - 1)`, so
`‖X.1+p.1‖ ≤ (32/7)‖p.2‖²/q²` via `‖y/ζ‖ ≤ 4‖p.2‖/(3q)`.  Also `X.2 - σ p.2 = μ*y*(ς/(ζ*s) - 1/q)`
with `σ = -1 + μ/q` (at the base point `Q₀ = (c,0)` one has `ζ₀ = C₀`, `s₀ = 1`, `ρ'₀ = q`, hence
`invBranch a s Q₀ = (-c + μς, 0)`), and
`|X.2 - σp.2| ≤ ‖p.2‖(‖1-s‖/‖s‖ + ‖p.1‖)/(‖ζ‖ q) ≤ (32/21 + 4/3)‖p.2‖‖p‖/q²`
using `‖p.1‖ ≤ ‖p‖`, `‖p.2‖/q ≤ 1/4` and `ςq = C₀`. -/
theorem invBranch_axis_second_order_sharp {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (c : ℝ) (_hc : ∃ k : ℤ, c = -1 / 2 + 2 * (k : ℝ)) (s : Bool)
      {p : ℂ × ℂ}, ‖p‖ ≤ (1 - a) / 8 →
      ‖(Work.EQ.invBranch a s (((c : ℂ), (0 : ℂ)) + p)
          - Work.EQ.invBranch a s (((c : ℂ), (0 : ℂ)))).1 + p.1‖
        ≤ C * ‖p.2‖ ^ 2 / |c + a / 2| ^ 2 ∧
      ‖(Work.EQ.invBranch a s (((c : ℂ), (0 : ℂ)) + p)
          - Work.EQ.invBranch a s (((c : ℂ), (0 : ℂ)))).2
          - (-1 + Work.EQ.sgnB s / |c + a / 2|) * p.2‖
        ≤ C * ‖p.2‖ * ‖p‖ / |c + a / 2| ^ 2 := by
  refine ⟨16, by norm_num, ?_⟩
  intro c hc s p hp
  obtain ⟨hcn1, -⟩ := FanSep.centre_numbers ha0 ha1
  obtain ⟨-, -, hsqrt3⟩ := FanSep.sqrt_step
  have hA2 : (1-a)/2 ≤ |c + a/2| := by
    obtain ⟨k, hk⟩ := hc
    have h := (hcn1 k).1
    rw [FanSep.norm_ofReal_add_eq_abs] at h
    rw [hk]; exact h
  have hαpos : 0 < |c + a/2| := by linarith
  have hAne : c + a/2 ≠ 0 := abs_ne_zero.mp hαpos.ne'
  have hp1 : ‖p.1‖ ≤ ‖p‖ := norm_fst_le p
  have hp2 : ‖p.2‖ ≤ ‖p‖ := norm_snd_le p
  have hp1' : ‖p.1‖ ≤ |c + a/2|/4 := by linarith
  have hP' : ‖p‖ ≤ |c + a/2|/4 := by linarith
  have hcabs : (1-a)/2 ≤ ‖((c:ℂ) + ((a/2:ℝ):ℂ))‖ := by
    rw [FanSep.norm_ofReal_add_eq_abs]; exact hA2
  have hQ : ‖(((c:ℂ),(0:ℂ)) + p) - ((c:ℂ),(0:ℂ))‖ ≤ (1-a)/8 := by simpa using hp
  have hmain := invBranch_eq_unitDir ha0 ha1 hcabs s hQ
  have hbase := invBranch_eq_unitDir ha0 ha1 hcabs s (Q := ((c:ℂ),(0:ℂ))) (by simp; positivity)
  -- ===== the two residual identities =====
  have hres1 : (invBranch a s (((c:ℂ),(0:ℂ)) + p) - invBranch a s (((c:ℂ),(0:ℂ)))).1 + p.1
      = ((if s then (1:ℂ) else -1) * ((sgnR (c + a/2) : ℝ) : ℂ)) *
          ((sqHalf ((p.2 / ((c:ℂ) + p.1 + ((a/2:ℝ):ℂ)))^2))⁻¹ - 1) := by
    rw [hmain, hbase, Prod.fst_sub]
    simp only [Prod.fst_add, Prod.snd_add, zero_div, unitDir_fst, pow_two, mul_zero,
      inv_one, sqHalf_zero, zero_add]
    ring
  have hres2 : (invBranch a s (((c:ℂ),(0:ℂ)) + p) - invBranch a s (((c:ℂ),(0:ℂ)))).2
        - (-1 + sgnB s / |c + a/2|) * p.2
      = ((sgnB s : ℝ) : ℂ) * (((sgnR (c + a/2) : ℝ) : ℂ) * (p.2 / ((c:ℂ) + p.1 + ((a/2:ℝ):ℂ))) *
            (sqHalf ((p.2 / ((c:ℂ) + p.1 + ((a/2:ℝ):ℂ)))^2))⁻¹
          - p.2 * (((|c + a/2| : ℝ)) : ℂ)⁻¹) := by
    rw [hmain, hbase, Prod.snd_sub]
    simp only [Prod.fst_add, Prod.snd_add, zero_div, unitDir_snd, pow_two, mul_zero, zero_mul,
      neg_zero, add_zero, zero_add, sub_zero]
    rw [div_eq_mul_inv]
    have hb : (if s = true then (1:ℂ) else -1) = ((sgnB s : ℝ) : ℂ) := by
      cases s <;> simp [sgnB]
    rw [hb]
    ring
  -- ===== abbreviations =====
  set α : ℝ := |c + a/2| with hαdef
  set z : ℂ := (c:ℂ) + p.1 + ((a/2:ℝ):ℂ) with hzdef
  set u : ℂ := p.2 / z with hudef
  set S : ℂ := sqHalf (u^2) with hSdef
  set σc : ℂ := ((sgnR (c + a/2) : ℝ) : ℂ) with hσcdef
  set b : ℂ := ((sgnB s : ℝ) : ℂ) with hbdef
  set t : ℝ := ‖p.2‖ / α with htdef
  set T : ℝ := ‖p‖ / α with hTdef
  -- ===== scalar facts =====
  have hσcnorm : ‖σc‖ = 1 := by
    rw [hσcdef]; simp [abs_sgnR]
  have hbnorm : ‖b‖ = 1 := by
    rw [hbdef]; simp [abs_sgnB]
  have hσne : σc ≠ 0 := by rw [hσcdef]; exact_mod_cast sgnR_ne_zero (c + a/2)
  have hσ2 : σc * σc = 1 := by rw [hσcdef, ← Complex.ofReal_mul, sgnR_sq]; norm_num
  have hσinv : σc⁻¹ = σc := inv_eq_of_mul_eq_one_left hσ2
  have hz_eq : z = (((c + a/2 : ℝ)) : ℂ) + p.1 := by rw [hzdef]; push_cast; ring
  set Ac : ℂ := (((c + a/2 : ℝ)) : ℂ) with hAcdef
  have hAcne : Ac ≠ 0 := by
    rw [hAcdef]; rw [← Complex.ofReal_zero, Ne, Complex.ofReal_inj]; exact hAne
  have hAcnorm : ‖Ac‖ = α := by rw [hAcdef, hαdef]; exact RCLike.norm_ofReal _
  have hσA : σc * Ac = ((α:ℝ):ℂ) := by
    rw [hσcdef, hAcdef, ← Complex.ofReal_mul, hαdef, sgnR_mul_self hAne]
  have hznorm : (3/4) * α ≤ ‖z‖ := by
    have h1 : ‖Ac‖ ≤ ‖z‖ + ‖p.1‖ := by
      have h2 := norm_add_le z (-p.1)
      have h3 : z + (-p.1) = Ac := by rw [hz_eq]; ring
      rw [h3, norm_neg] at h2
      exact h2
    rw [hAcnorm] at h1
    linarith [h1, hp1', hαpos]
  have hzpos : 0 < ‖z‖ := by linarith
  have hzne : z ≠ 0 := norm_ne_zero_iff.mp hzpos.ne'
  have hαne : α ≠ 0 := by rw [hαdef]; exact hαpos.ne'
  have htα : t * α = ‖p.2‖ := by rw [htdef]; exact div_mul_cancel₀ _ hαne
  have hTα : T * α = ‖p‖ := by rw [hTdef]; exact div_mul_cancel₀ _ hαne
  have ht0 : 0 ≤ t := by rw [htdef]; positivity
  have hT0 : 0 ≤ T := by rw [hTdef]; positivity
  have htq : t ≤ 1/4 := by
    rw [htdef, div_le_iff₀ hαpos]
    rw [hαdef]
    linarith [hp2, hP']
  have htT : t ≤ T := by
    rw [htdef, hTdef]
    exact div_le_div_of_nonneg_right hp2 hαpos.le
  have hunorm : ‖u‖ ≤ (4/3) * t := by
    rw [hudef, norm_div]
    have h1 : ‖p.2‖ / ‖z‖ ≤ ‖p.2‖ / ((3/4)*α) :=
      div_le_div₀ (norm_nonneg _) le_rfl (by positivity) hznorm
    have h2 : ‖p.2‖ / ((3/4)*α) = (4/3) * t := by
      rw [htdef]; field_simp
    linarith [h1, h2.le, h2.ge]
  have hu_half : ‖u‖ ≤ 1/2 := by
    have h1 : (4/3) * t ≤ (4/3) * (1/4) := mul_le_mul_of_nonneg_left htq (by norm_num)
    linarith [hunorm, h1]
  have hu2 : ‖u‖^2 ≤ 16/9 * t^2 := by
    have h3 := pow_le_pow_left₀ (norm_nonneg u) hunorm 2
    calc ‖u‖^2 ≤ ((4:ℝ)/3 * t)^2 := h3
      _ = 16/9 * t^2 := by ring
  have hSbound : ‖S⁻¹ - 1‖ ≤ 2 * ‖u‖^2 := by rw [hSdef]; exact hsqrt3 u hu_half
  have hSne : S ≠ 0 := by
    intro h
    have h1 : ‖S⁻¹ - 1‖ = 1 := by rw [h, inv_zero, zero_sub, norm_neg, norm_one]
    have h2 := hSbound
    rw [h1] at h2
    have h3 : ‖u‖^2 ≤ (1/2)^2 := pow_le_pow_left₀ (norm_nonneg u) hu_half 2
    nlinarith
  have hz1 : ‖z‖⁻¹ ≤ 4/(3*α) := by
    have h1 : ‖z‖⁻¹ ≤ (((3:ℝ)/4*α))⁻¹ := by
      simpa [one_div] using
        one_div_le_one_div_of_le (show 0 < (3:ℝ)/4*α by positivity) hznorm
    have h2 : (((3:ℝ)/4*α))⁻¹ = 4/(3*α) := by field_simp
    linarith [h1, h2.le, h2.ge]
  refine ⟨?_, ?_⟩
  -- ================= first coordinate =================
  · rw [hres1]
    have hτnorm : ‖(if s then (1:ℂ) else -1) * ((sgnR (c + a/2) : ℝ) : ℂ)‖ = 1 := by
      rw [norm_mul, hσcnorm, mul_one]
      cases s <;> simp
    calc ‖((if s then (1:ℂ) else -1) * ((sgnR (c + a/2) : ℝ) : ℂ)) * (S⁻¹ - 1)‖
        = ‖S⁻¹ - 1‖ := by rw [norm_mul, hτnorm, one_mul]
      _ ≤ 2 * ‖u‖^2 := hSbound
      _ ≤ 16 * ‖p.2‖^2 / α^2 := by
        have h6 : (16:ℝ) * ‖p.2‖^2/α^2 = 16 * t^2 := by rw [htdef, div_pow]; ring
        nlinarith [hu2, sq_nonneg t, norm_nonneg u]
  -- ================= second coordinate =================
  · rw [hres2, norm_mul, hbnorm, one_mul]
    have hXfac : σc * u * S⁻¹ - p.2 * ((α:ℂ))⁻¹
        = p.2 * σc * (z⁻¹ * S⁻¹ - Ac⁻¹) := by
      rw [hudef, div_eq_mul_inv, ← hσA, mul_inv_rev, hσinv]
      ring
    have hSfac : z⁻¹ * S⁻¹ - Ac⁻¹ = z⁻¹ * (S⁻¹ - z * Ac⁻¹) := by
      rw [mul_sub, ← mul_assoc, inv_mul_cancel₀ hzne, one_mul]
    rw [hXfac, hSfac]
    have htri : ‖S⁻¹ - z * Ac⁻¹‖ ≤ 2 * ‖u‖^2 + ‖p.1‖/α := by
      have h1 : S⁻¹ - z * Ac⁻¹ = (S⁻¹ - 1) + (1 - z * Ac⁻¹) := by ring
      rw [h1]
      have h2 := norm_add_le (S⁻¹ - 1) (1 - z * Ac⁻¹)
      have h3 : ‖1 - z * Ac⁻¹‖ = ‖p.1‖/α := by
        have h4 : 1 - z * Ac⁻¹ = -(p.1 * Ac⁻¹) := by
          rw [hz_eq]; field_simp; ring
        rw [h4, norm_neg, norm_mul, norm_inv, hAcnorm, div_eq_mul_inv]
      linarith [h2, h3, hSbound]
    have hnum : 2 * ‖u‖^2 + ‖p.1‖/α ≤ 2 * (16/9 * t^2) + T := by
      have h1 : ‖p.1‖/α ≤ T := by
        rw [hTdef]; exact div_le_div_of_nonneg_right hp1 hαpos.le
      linarith [hu2, h1]
    calc ‖p.2 * σc * (z⁻¹ * (S⁻¹ - z * Ac⁻¹))‖
        = ‖p.2‖ * ‖z‖⁻¹ * ‖S⁻¹ - z * Ac⁻¹‖ := by
          rw [norm_mul, norm_mul, norm_mul, norm_inv, hσcnorm]; ring
      _ ≤ ‖p.2‖ * ‖z‖⁻¹ * (2 * ‖u‖^2 + ‖p.1‖/α) := by
          apply mul_le_mul_of_nonneg_left htri; positivity
      _ ≤ ‖p.2‖ * (4/(3*α)) * (2 * (16/9 * t^2) + T) := by
          apply mul_le_mul
          · exact mul_le_mul_of_nonneg_left hz1 (norm_nonneg p.2)
          · exact hnum
          · positivity
          · positivity
      _ = (4/3) * t * (32/9 * t^2 + T) := by
          rw [← htα]; field_simp; ring
      _ ≤ 16 * t * T := by nlinarith [ht0, hT0, htq, htT, sq_nonneg t]
      _ = 16 * ‖p.2‖ * ‖p‖ / α^2 := by rw [htdef, hTdef]; field_simp

end

end Work.EQ.FanTri
