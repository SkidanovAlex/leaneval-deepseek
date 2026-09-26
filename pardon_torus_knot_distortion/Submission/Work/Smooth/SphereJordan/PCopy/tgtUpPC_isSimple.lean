import Mathlib
import Submission.Work.Smooth.SphereJordan.PCopy.SpanHyp
import Submission.Work.Smooth.SphereJordan.PCopy.SpanSetup

/-!
# The upper target curve of the cut-and-paste is a simple closed curve

`Work.SphereJordan.pctgtUpPC_isSimple`: for a simple closed plane curve `γ` in the open unit disc with
Schoenflies datum `S`, and the configuration `H : pcSpanHyp`, the `4`-arc curve `H.pcupPC b` (the boundary
of the upper piece of the cut pcannulus) is simple.

The total curve is `pctgtUpB = pctgtUpBun ∘ pcperPt`; on one period `pcperPt` is the identity, so it suffices
to show that the piecewise function `pctgtUpBun` is injective on `[0, 2π)`.  Its four pieces are

* the upper outer semicircle `pcsrcOuterUp S`,
* the second crosscut `pctgtCut₂ S t₂ s₂`,
* the inner arc `x ↦ γ (θ₂ + x·(θ₁ - θ₂))` (or `θ₁ - θ₂ - 2π` when `b = false`),
* the first crosscut `pctgtCut₁ S t₁ s₁`,

and the proof is the elementary four-arc analysis: each piece is injective on `[0,1]` (the two pccuts
because `tᵢ ≠ sᵢ` and the inner arc because `γ` is simple and the parameter interval is shorter than a
period), and the four pieces are pairwise disjoint except at the junctions, which follows from
`hball` (the inner arc lies in the open disc, the outer arc on the circle), `hmax₁`, `hmax₂` (the
crosscuts meet `γ` only in their inner endpoints) and the arithmetic of the configuration.
-/

namespace Work.SphereJordan

open Set

noncomputable section

variable {γ : Work.Smooth.Jordan.PlaneCurve}

/-! ## Normal forms for the four arcs -/

/-- The outer semicircle, as a multiple of the unit direction `pccutDir S` of the point `e^{iπx}`. -/
theorem pcsrcOuterUp_cp (S : Work.Smooth.Jordan.PlaneSchoenflies γ) (x : ℝ) :
    Work.Smooth.SphereJordan.pcsrcOuterUp S x =
      Work.Smooth.SphereJordan.pccutDir S *
        ((Work.Smooth.Jordan.circlePoint (Real.pi * x) : Work.Smooth.Jordan.Disc) : ℂ) := by
  rw [Work.Smooth.SphereJordan.pcsrcOuterUp, Work.Smooth.Jordan.circlePoint_coe]

/-- A point of the boundary circle has norm one. -/
theorem pcnorm_cp (θ : ℝ) :
    ‖((Work.Smooth.Jordan.circlePoint θ : Work.Smooth.Jordan.Disc) : ℂ)‖ = 1 := by
  rw [Work.Smooth.Jordan.circlePoint_coe, Complex.norm_exp_ofReal_mul_I]

/-- The boundary point at `π` is `-1`. -/
theorem pccp_pi :
    ((Work.Smooth.Jordan.circlePoint Real.pi : Work.Smooth.Jordan.Disc) : ℂ) = -1 := by
  rw [Work.Smooth.Jordan.circlePoint_coe, Complex.exp_pi_mul_I]

/-- The outer semicircle lies on the unit circle. -/
theorem pcnorm_srcOuterUp (S : Work.Smooth.Jordan.PlaneSchoenflies γ) (x : ℝ) :
    ‖Work.Smooth.SphereJordan.pcsrcOuterUp S x‖ = 1 := by
  rw [pcsrcOuterUp_cp, norm_mul, pcnorm_cp, Work.Smooth.SphereJordan.pcnorm_cutDir, mul_one]

/-- The scalar `1 - x·(s₁ - t₁)` giving `pctgtCut₁` in terms of `pccutDir`. -/
theorem pctgtCut₁_nf (S : Work.Smooth.Jordan.PlaneSchoenflies γ) {t₁ s₁ : ℝ}
    (h : (Work.Smooth.SphereJordan.pcbase S : ℂ) + (s₁ : ℂ) * Work.Smooth.SphereJordan.pccutDir S =
      Work.Smooth.SphereJordan.pccutDir S) (x : ℝ) :
    Work.Smooth.SphereJordan.pctgtCut₁ S t₁ s₁ x = ((1 - x * (s₁ - t₁) : ℝ) : ℂ) *
      Work.Smooth.SphereJordan.pccutDir S := by
  have hb : (Work.Smooth.SphereJordan.pcbase S : ℂ) = ((1 - s₁ : ℝ) : ℂ) *
      Work.Smooth.SphereJordan.pccutDir S := by
    have h' : (Work.Smooth.SphereJordan.pcbase S : ℂ) =
        Work.Smooth.SphereJordan.pccutDir S - (s₁ : ℂ) * Work.Smooth.SphereJordan.pccutDir S := by
      linear_combination h
    rw [h']; push_cast; ring
  rw [Work.Smooth.SphereJordan.pctgtCut₁, hb]; push_cast; ring

/-- The scalar `x·(s₂ - t₂) - 1` giving `pctgtCut₂` in terms of `pccutDir`. -/
theorem pctgtCut₂_nf (S : Work.Smooth.Jordan.PlaneSchoenflies γ) {t₂ s₂ : ℝ}
    (h : (Work.Smooth.SphereJordan.pcbase S : ℂ) - (s₂ : ℂ) * Work.Smooth.SphereJordan.pccutDir S =
      -Work.Smooth.SphereJordan.pccutDir S) (x : ℝ) :
    Work.Smooth.SphereJordan.pctgtCut₂ S t₂ s₂ x = ((x * (s₂ - t₂) - 1 : ℝ) : ℂ) *
      Work.Smooth.SphereJordan.pccutDir S := by
  have hb : (Work.Smooth.SphereJordan.pcbase S : ℂ) = ((s₂ - 1 : ℝ) : ℂ) *
      Work.Smooth.SphereJordan.pccutDir S := by
    have h' : (Work.Smooth.SphereJordan.pcbase S : ℂ) =
        -Work.Smooth.SphereJordan.pccutDir S + (s₂ : ℂ) * Work.Smooth.SphereJordan.pccutDir S := by
      linear_combination h
    rw [h']; push_cast; ring
  rw [Work.Smooth.SphereJordan.pctgtCut₂, hb]; push_cast; ring

/-! ## The four arcs are injective on `[0,1]` -/

theorem pcsrcOuterUp_injOn (S : Work.Smooth.Jordan.PlaneSchoenflies γ) :
    Set.InjOn (Work.Smooth.SphereJordan.pcsrcOuterUp S) (Set.Icc (0:ℝ) 1) := by
  intro x hx y hy hxy
  rw [pcsrcOuterUp_cp, pcsrcOuterUp_cp] at hxy
  have h2 : ((Work.Smooth.Jordan.circlePoint (Real.pi * x) : Work.Smooth.Jordan.Disc) : ℂ) =
      ((Work.Smooth.Jordan.circlePoint (Real.pi * y) : Work.Smooth.Jordan.Disc) : ℂ) :=
    mul_left_cancel₀ (Work.Smooth.SphereJordan.pccutDir_ne_zero S) hxy
  have hpx : Real.pi * x ∈ Set.Ico (0:ℝ) (2 * Real.pi) :=
    ⟨mul_nonneg Real.pi_pos.le hx.1, by nlinarith [Real.pi_pos, hx.1, hx.2]⟩
  have hpy : Real.pi * y ∈ Set.Ico (0:ℝ) (2 * Real.pi) :=
    ⟨mul_nonneg Real.pi_pos.le hy.1, by nlinarith [Real.pi_pos, hy.1, hy.2]⟩
  have h3 : Real.pi * x = Real.pi * y :=
    Work.Smooth.SphereJordan.injOn_circlePoint hpx hpy (Subtype.ext h2)
  exact mul_left_cancel₀ (ne_of_gt Real.pi_pos) h3

theorem pctgtCut₁_injOn (S : Work.Smooth.Jordan.PlaneSchoenflies γ) {t₁ s₁ : ℝ}
    (hout : (Work.Smooth.SphereJordan.pcbase S : ℂ) + (s₁ : ℂ) * Work.Smooth.SphereJordan.pccutDir S =
      Work.Smooth.SphereJordan.pccutDir S) (hts : t₁ ≠ s₁) :
    Set.InjOn (Work.Smooth.SphereJordan.pctgtCut₁ S t₁ s₁) (Set.Icc (0:ℝ) 1) := by
  intro x hx y hy hxy
  rw [pctgtCut₁_nf S hout x, pctgtCut₁_nf S hout y] at hxy
  have h2 : ((1 - x * (s₁ - t₁) : ℝ) : ℂ) = ((1 - y * (s₁ - t₁) : ℝ) : ℂ) :=
    mul_right_cancel₀ (Work.Smooth.SphereJordan.pccutDir_ne_zero S) hxy
  have h3 : 1 - x * (s₁ - t₁) = 1 - y * (s₁ - t₁) := Complex.ofReal_inj.mp h2
  have h4 : x * (s₁ - t₁) = y * (s₁ - t₁) := by linarith
  exact mul_right_cancel₀ (sub_ne_zero.mpr (Ne.symm hts)) h4

theorem pctgtCut₂_injOn (S : Work.Smooth.Jordan.PlaneSchoenflies γ) {t₂ s₂ : ℝ}
    (hout : (Work.Smooth.SphereJordan.pcbase S : ℂ) - (s₂ : ℂ) * Work.Smooth.SphereJordan.pccutDir S =
      -Work.Smooth.SphereJordan.pccutDir S) (hts : t₂ ≠ s₂) :
    Set.InjOn (Work.Smooth.SphereJordan.pctgtCut₂ S t₂ s₂) (Set.Icc (0:ℝ) 1) := by
  intro x hx y hy hxy
  rw [pctgtCut₂_nf S hout x, pctgtCut₂_nf S hout y] at hxy
  have h2 : ((x * (s₂ - t₂) - 1 : ℝ) : ℂ) = ((y * (s₂ - t₂) - 1 : ℝ) : ℂ) :=
    mul_right_cancel₀ (Work.Smooth.SphereJordan.pccutDir_ne_zero S) hxy
  have h3 : x * (s₂ - t₂) - 1 = y * (s₂ - t₂) - 1 := Complex.ofReal_inj.mp h2
  have h4 : x * (s₂ - t₂) = y * (s₂ - t₂) := by linarith
  exact mul_right_cancel₀ (sub_ne_zero.mpr (Ne.symm hts)) h4

/-- A simple curve is injective on the affine image of `[0,1]` under `x ↦ a + x·L` when `|L| < 2π`
and `L ≠ 0`. -/
theorem pcgammaArc_injOn (hs : γ.IsSimple) {a L : ℝ}
    (hL : L ≠ 0) (hL2 : |L| < 2 * Real.pi) :
    Set.InjOn (fun x : ℝ => γ.γ (a + x * L)) (Set.Icc (0:ℝ) 1) := by
  intro x hx y hy hxy
  have hab : |(a + x * L) - (a + y * L)| < 2 * Real.pi := by
    have h1 : |x - y| ≤ 1 := by
      rw [abs_sub_le_iff]; constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]
    have h2 : |(a + x * L) - (a + y * L)| = |x - y| * |L| := by
      rw [show a + x * L - (a + y * L) = (x - y) * L by ring, abs_mul]
    rw [h2]
    calc |x - y| * |L| ≤ 1 * |L| := mul_le_mul_of_nonneg_right h1 (abs_nonneg L)
      _ = |L| := by ring
      _ < 2 * Real.pi := hL2
  have h3 : a + x * L = a + y * L := Work.SphereJordan.pcinjOn_of_abs_lt hs hab hxy
  have h4 : x * L = y * L := by linarith
  exact mul_right_cancel₀ hL h4

/-! ## The four-arc injectivity lemma -/

/-- **Four arcs glued in order along the four quadrants of a circle are simple**, provided the four
arcs are injective on `[0,1]` and are pairwise disjoint except at the four junctions, as expressed by
the hypotheses `d₁₂`, `d₁₃`, `d₁₄`, `d₂₃`, `d₂₄`, `d₃₄`.  The junction conditions are those
appropriate to injectivity on the *half-open* period `[0, 2π)`: the pair `(1,4)` only has to be
disjoint because the wrap-around point `2π` is outside the domain. -/
theorem pcinjOn_four_arcs {F : ℝ → ℂ} {f₁ f₂ f₃ f₄ : ℝ → ℂ}
    (hF1 : ∀ σ : ℝ, σ ≤ Real.pi / 2 → F σ = f₁ (σ / (Real.pi / 2)))
    (hF2 : ∀ σ : ℝ, Real.pi / 2 < σ → σ ≤ Real.pi → F σ = f₂ ((σ - Real.pi / 2) / (Real.pi / 2)))
    (hF3 : ∀ σ : ℝ, Real.pi < σ → σ ≤ 3 * Real.pi / 2 → F σ = f₃ ((σ - Real.pi) / (Real.pi / 2)))
    (hF4 : ∀ σ : ℝ, 3 * Real.pi / 2 < σ → F σ = f₄ (1 - (σ - 3 * Real.pi / 2) / (Real.pi / 2)))
    (i₁ : Set.InjOn f₁ (Set.Icc 0 1)) (i₂ : Set.InjOn f₂ (Set.Icc 0 1))
    (i₃ : Set.InjOn f₃ (Set.Icc 0 1)) (i₄ : Set.InjOn f₄ (Set.Icc 0 1))
    (d₁₂ : ∀ a ∈ Set.Icc (0 : ℝ) 1, ∀ b ∈ Set.Icc (0 : ℝ) 1, f₁ a = f₂ b → a = 1 ∧ b = 0)
    (d₁₃ : ∀ a ∈ Set.Icc (0 : ℝ) 1, ∀ b ∈ Set.Icc (0 : ℝ) 1, f₁ a ≠ f₃ b)
    (d₁₄ : ∀ a ∈ Set.Icc (0 : ℝ) 1, ∀ b ∈ Set.Icc (0 : ℝ) 1, f₁ a = f₄ b → b = 0)
    (d₂₃ : ∀ a ∈ Set.Icc (0 : ℝ) 1, ∀ b ∈ Set.Icc (0 : ℝ) 1, f₂ a = f₃ b → a = 1 ∧ b = 0)
    (d₂₄ : ∀ a ∈ Set.Icc (0 : ℝ) 1, ∀ b ∈ Set.Icc (0 : ℝ) 1, f₂ a ≠ f₄ b)
    (d₃₄ : ∀ a ∈ Set.Icc (0 : ℝ) 1, ∀ b ∈ Set.Icc (0 : ℝ) 1, f₃ a = f₄ b → a = 1 ∧ b = 1) :
    Set.InjOn F (Set.Ico 0 (2 * Real.pi)) := by
  have hπ : (0 : ℝ) < Real.pi / 2 := by positivity
  have hπ' : Real.pi / 2 ≠ 0 := ne_of_gt hπ
  have h4h : 4 * (Real.pi / 2) = 2 * Real.pi := by ring
  have m1 : ∀ σ : ℝ, 0 ≤ σ → σ ≤ Real.pi / 2 → σ / (Real.pi / 2) ∈ Set.Icc (0 : ℝ) 1 := by
    intro σ h0 h
    refine ⟨div_nonneg h0 hπ.le, ?_⟩
    rw [div_le_iff₀ hπ]; linarith
  have m2 : ∀ σ : ℝ, Real.pi / 2 ≤ σ → σ ≤ Real.pi →
      (σ - Real.pi / 2) / (Real.pi / 2) ∈ Set.Icc (0 : ℝ) 1 := by
    intro σ h0 h
    refine ⟨div_nonneg (by linarith) hπ.le, ?_⟩
    rw [div_le_iff₀ hπ]; linarith
  have m3 : ∀ σ : ℝ, Real.pi ≤ σ → σ ≤ 3 * Real.pi / 2 →
      (σ - Real.pi) / (Real.pi / 2) ∈ Set.Icc (0 : ℝ) 1 := by
    intro σ h0 h
    refine ⟨div_nonneg (by linarith) hπ.le, ?_⟩
    rw [div_le_iff₀ hπ]; linarith
  have m4 : ∀ σ : ℝ, 3 * Real.pi / 2 ≤ σ → σ ≤ 2 * Real.pi →
      1 - (σ - 3 * Real.pi / 2) / (Real.pi / 2) ∈ Set.Icc (0 : ℝ) 1 := by
    intro σ h0 h
    constructor
    · have hh : (σ - 3 * Real.pi / 2) / (Real.pi / 2) ≤ 1 := by
        rw [div_le_iff₀ hπ]; linarith
      linarith
    · have hh : 0 ≤ (σ - 3 * Real.pi / 2) / (Real.pi / 2) := div_nonneg (by linarith) hπ.le
      linarith
  have mono : ∀ σ₁ σ₂ : ℝ, σ₁ ∈ Set.Ico 0 (2 * Real.pi) → σ₂ ∈ Set.Ico 0 (2 * Real.pi) →
      σ₁ ≤ σ₂ → F σ₁ = F σ₂ → σ₁ = σ₂ := by
    intro σ₁ σ₂ hσ₁ hσ₂ hle heq
    obtain ⟨hσ₁0, hσ₁2⟩ := hσ₁
    obtain ⟨hσ₂0, hσ₂2⟩ := hσ₂
    by_cases h2a : σ₂ ≤ Real.pi / 2
    · have h1a : σ₁ ≤ Real.pi / 2 := le_trans hle h2a
      have h' : f₁ (σ₁ / (Real.pi / 2)) = f₁ (σ₂ / (Real.pi / 2)) := by
        rw [← hF1 σ₁ h1a, ← hF1 σ₂ h2a]; exact heq
      have h2 := i₁ (m1 σ₁ hσ₁0 h1a) (m1 σ₂ hσ₂0 h2a) h'
      rw [div_eq_div_iff hπ' hπ'] at h2
      exact mul_right_cancel₀ hπ' h2
    · have h2a' : Real.pi / 2 < σ₂ := not_le.mp h2a
      by_cases h1a : σ₁ ≤ Real.pi / 2
      · by_cases h2b : σ₂ ≤ Real.pi
        · have h' : f₁ (σ₁ / (Real.pi / 2)) = f₂ ((σ₂ - Real.pi / 2) / (Real.pi / 2)) := by
            rw [← hF1 σ₁ h1a, ← hF2 σ₂ h2a' h2b]; exact heq
          obtain ⟨e1, e2⟩ := d₁₂ _ (m1 σ₁ hσ₁0 h1a) _ (m2 σ₂ h2a'.le h2b) h'
          have hs1 : σ₁ = Real.pi / 2 := by rw [div_eq_iff hπ'] at e1; simpa using e1
          have hs2 : σ₂ = Real.pi / 2 := by
            rw [div_eq_zero_iff] at e2
            rcases e2 with e2 | e2
            · linarith
            · exact absurd e2 hπ'
          rw [hs1, hs2]
        · have h2b' : Real.pi < σ₂ := not_le.mp h2b
          by_cases h2c : σ₂ ≤ 3 * Real.pi / 2
          · have h' : f₁ (σ₁ / (Real.pi / 2)) = f₃ ((σ₂ - Real.pi) / (Real.pi / 2)) := by
              rw [← hF1 σ₁ h1a, ← hF3 σ₂ h2b' h2c]; exact heq
            exact absurd h' (d₁₃ _ (m1 σ₁ hσ₁0 h1a) _ (m3 σ₂ h2b'.le h2c))
          · have h2c' : 3 * Real.pi / 2 < σ₂ := not_le.mp h2c
            have h' : f₁ (σ₁ / (Real.pi / 2)) =
                f₄ (1 - (σ₂ - 3 * Real.pi / 2) / (Real.pi / 2)) := by
              rw [← hF1 σ₁ h1a, ← hF4 σ₂ h2c']; exact heq
            have hb := d₁₄ _ (m1 σ₁ hσ₁0 h1a) _ (m4 σ₂ h2c'.le hσ₂2.le) h'
            have hx : (σ₂ - 3 * Real.pi / 2) / (Real.pi / 2) = 1 := by linarith
            rw [div_eq_iff hπ'] at hx
            linarith [hx, hσ₂2, h4h]
      · have h1a' : Real.pi / 2 < σ₁ := not_le.mp h1a
        by_cases h2b : σ₂ ≤ Real.pi
        · by_cases h1b : σ₁ ≤ Real.pi
          · have h' : f₂ ((σ₁ - Real.pi / 2) / (Real.pi / 2)) =
                f₂ ((σ₂ - Real.pi / 2) / (Real.pi / 2)) := by
              rw [← hF2 σ₁ h1a' h1b, ← hF2 σ₂ h2a' h2b]; exact heq
            have h2 := i₂ (m2 σ₁ h1a'.le h1b) (m2 σ₂ h2a'.le h2b) h'
            rw [div_eq_div_iff hπ' hπ'] at h2
            have h3 := mul_right_cancel₀ hπ' h2
            linarith
          · exact absurd (le_trans hle h2b) h1b
        · have h2b' : Real.pi < σ₂ := not_le.mp h2b
          by_cases h2c : σ₂ ≤ 3 * Real.pi / 2
          · by_cases h1b : σ₁ ≤ Real.pi
            · have h' : f₂ ((σ₁ - Real.pi / 2) / (Real.pi / 2)) =
                  f₃ ((σ₂ - Real.pi) / (Real.pi / 2)) := by
                rw [← hF2 σ₁ h1a' h1b, ← hF3 σ₂ h2b' h2c]; exact heq
              obtain ⟨e1, e2⟩ := d₂₃ _ (m2 σ₁ h1a'.le h1b) _ (m3 σ₂ h2b'.le h2c) h'
              have hs1 : σ₁ = Real.pi := by rw [div_eq_iff hπ'] at e1; linarith
              have hs2 : σ₂ = Real.pi := by
                rw [div_eq_zero_iff] at e2
                rcases e2 with e2 | e2
                · linarith
                · exact absurd e2 hπ'
              rw [hs1, hs2]
            · have h1b' : Real.pi < σ₁ := not_le.mp h1b
              by_cases h1c : σ₁ ≤ 3 * Real.pi / 2
              · have h' : f₃ ((σ₁ - Real.pi) / (Real.pi / 2)) =
                    f₃ ((σ₂ - Real.pi) / (Real.pi / 2)) := by
                  rw [← hF3 σ₁ h1b' h1c, ← hF3 σ₂ h2b' h2c]; exact heq
                have h2 := i₃ (m3 σ₁ h1b'.le h1c) (m3 σ₂ h2b'.le h2c) h'
                rw [div_eq_div_iff hπ' hπ'] at h2
                have h3 := mul_right_cancel₀ hπ' h2
                linarith
              · exact absurd (le_trans hle h2c) h1c
          · have h2c' : 3 * Real.pi / 2 < σ₂ := not_le.mp h2c
            by_cases h1b : σ₁ ≤ Real.pi
            · have h' : f₂ ((σ₁ - Real.pi / 2) / (Real.pi / 2)) =
                  f₄ (1 - (σ₂ - 3 * Real.pi / 2) / (Real.pi / 2)) := by
                rw [← hF2 σ₁ h1a' h1b, ← hF4 σ₂ h2c']; exact heq
              exact absurd h' (d₂₄ _ (m2 σ₁ h1a'.le h1b) _ (m4 σ₂ h2c'.le hσ₂2.le))
            · have h1b' : Real.pi < σ₁ := not_le.mp h1b
              by_cases h1c : σ₁ ≤ 3 * Real.pi / 2
              · have h' : f₃ ((σ₁ - Real.pi) / (Real.pi / 2)) =
                    f₄ (1 - (σ₂ - 3 * Real.pi / 2) / (Real.pi / 2)) := by
                  rw [← hF3 σ₁ h1b' h1c, ← hF4 σ₂ h2c']; exact heq
                obtain ⟨e1, e2⟩ := d₃₄ _ (m3 σ₁ h1b'.le h1c) _ (m4 σ₂ h2c'.le hσ₂2.le) h'
                have hs1 : σ₁ = 3 * Real.pi / 2 := by rw [div_eq_iff hπ'] at e1; linarith
                have hs2 : σ₂ = 3 * Real.pi / 2 := by
                  have hz : (σ₂ - 3 * Real.pi / 2) / (Real.pi / 2) = 0 := by linarith
                  rw [div_eq_zero_iff] at hz
                  rcases hz with hz | hz
                  · linarith
                  · exact absurd hz hπ'
                rw [hs1, hs2]
              · have h1c' : 3 * Real.pi / 2 < σ₁ := not_le.mp h1c
                have h' : f₄ (1 - (σ₁ - 3 * Real.pi / 2) / (Real.pi / 2)) =
                    f₄ (1 - (σ₂ - 3 * Real.pi / 2) / (Real.pi / 2)) := by
                  rw [← hF4 σ₁ h1c', ← hF4 σ₂ h2c']; exact heq
                have h2 := i₄ (m4 σ₁ h1c'.le hσ₁2.le) (m4 σ₂ h2c'.le hσ₂2.le) h'
                have h3 : (σ₁ - 3 * Real.pi / 2) / (Real.pi / 2) =
                    (σ₂ - 3 * Real.pi / 2) / (Real.pi / 2) := by linarith
                rw [div_eq_div_iff hπ' hπ'] at h3
                have h4 := mul_right_cancel₀ hπ' h3
                linarith
  intro σ₁ h₁ σ₂ h₂ heq
  rcases le_total σ₁ σ₂ with h | h
  · exact mono σ₁ σ₂ h₁ h₂ h heq
  · exact (mono σ₂ σ₁ h₂ h₁ h heq.symm).symm

/-! ## The configuration-dependent arithmetic and disjointness -/

variable {h : Work.Smooth.SphereJordan.PlaneHypothesis} {hs : γ.IsSimple}
  {hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1} {S : Work.Smooth.Jordan.PlaneSchoenflies γ}

theorem pcsum_cuts (H : pcSpanHyp h hs hball S) : H.s₁ + H.s₂ = 2 := by
  rw [H.pcs₁_eq, H.pcs₂_eq]; ring

theorem pcdiff_cuts_lt_two (H : pcSpanHyp h hs hball S) : H.s₁ - H.t₁ < 2 := by
  have h1 := H.pcs₁_eq
  have h2 := H.pcnorm_base_lt_one
  have h3 : (0:ℝ) ≤ ‖(Work.Smooth.SphereJordan.pcbase S : ℂ)‖ := norm_nonneg _
  linarith [H.ht₁]

theorem pcs₂_sub_t₂_lt_two (H : pcSpanHyp h hs hball S) : H.s₂ - H.t₂ < 2 := by
  have h1 := H.pcs₂_eq
  have h2 := H.pcnorm_base_lt_one
  linarith [H.ht₂]

/-- The outer arc meets the second cut only at the common junction `-pccutDir`. -/
theorem pcdisj₁₂ (H : pcSpanHyp h hs hball S) :
    ∀ a ∈ Set.Icc (0 : ℝ) 1, ∀ b ∈ Set.Icc (0 : ℝ) 1,
      Work.Smooth.SphereJordan.pcsrcOuterUp S a =
        Work.Smooth.SphereJordan.pctgtCut₂ S H.t₂ H.s₂ b → a = 1 ∧ b = 0 := by
  intro a ha b hb heq
  rw [pcsrcOuterUp_cp S a, pctgtCut₂_nf S H.hout₂ b] at heq
  have h2 : ((Work.Smooth.Jordan.circlePoint (Real.pi * a) : Work.Smooth.Jordan.Disc) : ℂ) =
      ((b * (H.s₂ - H.t₂) - 1 : ℝ) : ℂ) := by
    have h3 : Work.Smooth.SphereJordan.pccutDir S *
        ((Work.Smooth.Jordan.circlePoint (Real.pi * a) : Work.Smooth.Jordan.Disc) : ℂ) =
        Work.Smooth.SphereJordan.pccutDir S * ((b * (H.s₂ - H.t₂) - 1 : ℝ) : ℂ) := by
      rw [heq]; ring
    exact mul_left_cancel₀ (Work.Smooth.SphereJordan.pccutDir_ne_zero S) h3
  have hnorm : |b * (H.s₂ - H.t₂) - 1| = 1 := by
    have hh := congrArg (fun z : ℂ => ‖z‖) h2
    rw [pcnorm_cp, Complex.norm_real, Real.norm_eq_abs] at hh
    exact hh.symm
  have hb_lt : b * (H.s₂ - H.t₂) - 1 < 1 := by
    have h1 : b * (H.s₂ - H.t₂) ≤ H.s₂ - H.t₂ :=
      mul_le_of_le_one_left (by linarith [H.ht₂s₂]) hb.2
    linarith [h1, pcs₂_sub_t₂_lt_two H]
  have hb_ge : -1 ≤ b * (H.s₂ - H.t₂) - 1 := by
    have h1 : 0 ≤ b * (H.s₂ - H.t₂) := mul_nonneg hb.1 (by linarith [H.ht₂s₂])
    linarith
  have hcoeff : b * (H.s₂ - H.t₂) - 1 = -1 := by
    rcases (abs_eq (by norm_num : (0:ℝ) ≤ 1)).mp hnorm with hh | hh
    · linarith
    · exact hh
  have hb0 : b = 0 := by
    have h1 : b * (H.s₂ - H.t₂) = 0 := by linarith
    exact (mul_eq_zero.mp h1).resolve_right (sub_ne_zero.mpr (ne_of_lt H.ht₂s₂).symm)
  refine ⟨?_, hb0⟩
  subst hb0
  have h4 : ((Work.Smooth.Jordan.circlePoint (Real.pi * a) : Work.Smooth.Jordan.Disc) : ℂ) =
      ((Work.Smooth.Jordan.circlePoint Real.pi : Work.Smooth.Jordan.Disc) : ℂ) := by
    rw [h2, hcoeff, pccp_pi]; norm_num
  have hpa : Real.pi * a ∈ Set.Ico (0:ℝ) (2 * Real.pi) :=
    ⟨mul_nonneg Real.pi_pos.le ha.1, by nlinarith [Real.pi_pos, ha.1, ha.2]⟩
  have hpπ : Real.pi ∈ Set.Ico (0:ℝ) (2 * Real.pi) :=
    ⟨Real.pi_pos.le, by linarith [Real.pi_pos]⟩
  have h5 : Real.pi * a = Real.pi :=
    Work.Smooth.SphereJordan.injOn_circlePoint hpa hpπ (Subtype.ext h4)
  exact mul_left_cancel₀ (ne_of_gt Real.pi_pos) (by simpa using h5)

/-- The outer arc never meets the inner arc (which lies in the open disc). -/
theorem pcdisj₁₃ (H : pcSpanHyp h hs hball S) {K : ℝ} :
    ∀ a ∈ Set.Icc (0 : ℝ) 1, ∀ b ∈ Set.Icc (0 : ℝ) 1,
      Work.Smooth.SphereJordan.pcsrcOuterUp S a ≠ γ.γ (H.θ₂ + b * K) := by
  intro a ha b hb heq
  have h1 : ‖Work.Smooth.SphereJordan.pcsrcOuterUp S a‖ = 1 := pcnorm_srcOuterUp S a
  rw [heq] at h1
  have h2 : ‖γ.γ (H.θ₂ + b * K)‖ < 1 := hball _
  linarith

/-- The outer arc meets the first cut only at the outer endpoint `pccutDir`. -/
theorem pcdisj₁₄ (H : pcSpanHyp h hs hball S) :
    ∀ a ∈ Set.Icc (0 : ℝ) 1, ∀ b ∈ Set.Icc (0 : ℝ) 1,
      Work.Smooth.SphereJordan.pcsrcOuterUp S a =
        Work.Smooth.SphereJordan.pctgtCut₁ S H.t₁ H.s₁ b → b = 0 := by
  intro a ha b hb heq
  rw [pcsrcOuterUp_cp S a, pctgtCut₁_nf S H.hout₁ b] at heq
  have h2 : ((Work.Smooth.Jordan.circlePoint (Real.pi * a) : Work.Smooth.Jordan.Disc) : ℂ) =
      ((1 - b * (H.s₁ - H.t₁) : ℝ) : ℂ) := by
    have h3 : Work.Smooth.SphereJordan.pccutDir S *
        ((Work.Smooth.Jordan.circlePoint (Real.pi * a) : Work.Smooth.Jordan.Disc) : ℂ) =
        Work.Smooth.SphereJordan.pccutDir S * ((1 - b * (H.s₁ - H.t₁) : ℝ) : ℂ) := by
      rw [heq]; ring
    exact mul_left_cancel₀ (Work.Smooth.SphereJordan.pccutDir_ne_zero S) h3
  have hnorm : |1 - b * (H.s₁ - H.t₁)| = 1 := by
    have hh := congrArg (fun z : ℂ => ‖z‖) h2
    rw [pcnorm_cp, Complex.norm_real, Real.norm_eq_abs] at hh
    exact hh.symm
  have hle : 1 - b * (H.s₁ - H.t₁) ≤ 1 := by
    have h1 : 0 ≤ b * (H.s₁ - H.t₁) := mul_nonneg hb.1 (by linarith [H.ht₁s₁])
    linarith
  have hgt : -1 < 1 - b * (H.s₁ - H.t₁) := by
    have h1 : b * (H.s₁ - H.t₁) ≤ H.s₁ - H.t₁ :=
      mul_le_of_le_one_left (by linarith [H.ht₁s₁]) hb.2
    linarith [h1, pcdiff_cuts_lt_two H]
  have hc : 1 - b * (H.s₁ - H.t₁) = 1 := by
    rcases (abs_eq (by norm_num : (0:ℝ) ≤ 1)).mp hnorm with hh | hh
    · exact hh
    · linarith
  have h1 : b * (H.s₁ - H.t₁) = 0 := by linarith
  exact (mul_eq_zero.mp h1).resolve_right (sub_ne_zero.mpr (ne_of_lt H.ht₁s₁).symm)

/-- The two pccuts are disjoint. -/
theorem pcdisj₂₄ (H : pcSpanHyp h hs hball S) :
    ∀ a ∈ Set.Icc (0 : ℝ) 1, ∀ b ∈ Set.Icc (0 : ℝ) 1,
      Work.Smooth.SphereJordan.pctgtCut₂ S H.t₂ H.s₂ a ≠
        Work.Smooth.SphereJordan.pctgtCut₁ S H.t₁ H.s₁ b := by
  intro a ha b hb heq
  rw [pctgtCut₂_nf S H.hout₂ a, pctgtCut₁_nf S H.hout₁ b] at heq
  have h2 : a * (H.s₂ - H.t₂) - 1 = 1 - b * (H.s₁ - H.t₁) := by
    have hh := mul_right_cancel₀ (Work.Smooth.SphereJordan.pccutDir_ne_zero S) heq
    exact Complex.ofReal_inj.mp hh
  have hle1 : a * (H.s₂ - H.t₂) - 1 ≤ H.s₂ - H.t₂ - 1 := by
    have h1 : a * (H.s₂ - H.t₂) ≤ H.s₂ - H.t₂ :=
      mul_le_of_le_one_left (by linarith [H.ht₂s₂]) ha.2
    linarith
  have hle2 : 1 - (H.s₁ - H.t₁) ≤ 1 - b * (H.s₁ - H.t₁) := by
    have h1 : b * (H.s₁ - H.t₁) ≤ H.s₁ - H.t₁ :=
      mul_le_of_le_one_left (by linarith [H.ht₁s₁]) hb.2
    linarith
  have hlt : H.s₂ - H.t₂ - 1 < 1 - (H.s₁ - H.t₁) := by
    have hss := pcsum_cuts H
    linarith [H.ht₁, H.ht₂]
  linarith

/-- The second cut meets the inner arc only at the junction `γ θ₂`. -/
theorem pcdisj₂₃ (H : pcSpanHyp h hs hball S) {K : ℝ} (hK : K ≠ 0)
    (hK2 : |K| < 2 * Real.pi) :
    ∀ a ∈ Set.Icc (0 : ℝ) 1, ∀ b ∈ Set.Icc (0 : ℝ) 1,
      Work.Smooth.SphereJordan.pctgtCut₂ S H.t₂ H.s₂ a = γ.γ (H.θ₂ + b * K) →
        a = 1 ∧ b = 0 := by
  intro a ha b hb heq
  have hmem : γ.γ (H.θ₂ + b * K) ∈ closure S.V := by
    rw [← S.range_e]
    exact ⟨Work.Smooth.Jordan.circlePoint (H.θ₂ + b * K), S.boundary _⟩
  have hσle : H.s₂ + a * (H.t₂ - H.s₂) ≤ H.t₂ := by
    by_contra hcon
    have hlt : H.t₂ < H.s₂ + a * (H.t₂ - H.s₂) := not_le.mp hcon
    refine (H.hmax₂ _ hlt) ?_
    change Work.Smooth.SphereJordan.pctgtCut₂ S H.t₂ H.s₂ a ∈ closure S.V
    rw [heq]; exact hmem
  have ha1 : a = 1 := by
    have h1 : (a - 1) * (H.t₂ - H.s₂) ≤ 0 := by nlinarith [hσle]
    have h2 : H.t₂ - H.s₂ < 0 := by linarith [H.ht₂s₂]
    have h3 : 0 ≤ a - 1 := by
      by_contra hcon
      have h4 : 0 < (a - 1) * (H.t₂ - H.s₂) := mul_pos_of_neg_of_neg (not_le.mp hcon) h2
      linarith
    linarith [h3, ha.2]
  refine ⟨ha1, ?_⟩
  have hf2 : Work.Smooth.SphereJordan.pctgtCut₂ S H.t₂ H.s₂ 1 = γ.γ H.θ₂ := by
    rw [Work.Smooth.SphereJordan.pctgtCut₂]
    have hh : ((H.s₂ + 1 * (H.t₂ - H.s₂) : ℝ) : ℂ) = (H.t₂ : ℂ) := by push_cast; ring
    rw [hh]; exact H.hθ₂.symm
  have hγeq : γ.γ (H.θ₂ + b * K) = γ.γ (H.θ₂ + 0 * K) := by
    rw [zero_mul, add_zero, ← hf2, ← ha1]
    exact heq.symm
  have hab : |(H.θ₂ + b * K) - (H.θ₂ + 0 * K)| < 2 * Real.pi := by
    rw [zero_mul, add_zero, add_sub_cancel_left, abs_mul, abs_of_nonneg hb.1]
    calc b * |K| ≤ 1 * |K| := mul_le_mul_of_nonneg_right hb.2 (abs_nonneg K)
      _ = |K| := by ring
      _ < 2 * Real.pi := hK2
  have h4 := Work.SphereJordan.pcinjOn_of_abs_lt hs hab hγeq
  have h5 : b * K = 0 := by linarith
  exact (mul_eq_zero.mp h5).resolve_right hK

/-- The inner arc meets the first cut only at the junction `γ θ₁`. -/
theorem pcdisj₃₄ (H : pcSpanHyp h hs hball S) {K : ℝ}
    (hKstep : ∀ a ∈ Set.Icc (0 : ℝ) 1, a ≠ 1 → γ.γ (H.θ₂ + a * K) ≠ γ.γ H.θ₁) :
    ∀ a ∈ Set.Icc (0 : ℝ) 1, ∀ b ∈ Set.Icc (0 : ℝ) 1,
      γ.γ (H.θ₂ + a * K) = Work.Smooth.SphereJordan.pctgtCut₁ S H.t₁ H.s₁ b →
        a = 1 ∧ b = 1 := by
  intro a ha b hb heq
  have hmem : Work.Smooth.SphereJordan.pctgtCut₁ S H.t₁ H.s₁ b ∈ closure S.V := by
    rw [← heq, ← S.range_e]
    exact ⟨Work.Smooth.Jordan.circlePoint (H.θ₂ + a * K), S.boundary _⟩
  have hσle : H.s₁ + b * (H.t₁ - H.s₁) ≤ H.t₁ := by
    by_contra hcon
    have hlt : H.t₁ < H.s₁ + b * (H.t₁ - H.s₁) := not_le.mp hcon
    refine (H.hmax₁ _ hlt) ?_
    simpa only [Work.Smooth.SphereJordan.pctgtCut₁] using hmem
  have hb1 : b = 1 := by
    have h1 : (H.s₁ - H.t₁) * (1 - b) ≤ 0 := by nlinarith [hσle]
    have h2 : 0 < H.s₁ - H.t₁ := by linarith [H.ht₁s₁]
    have h3 : 1 - b ≤ 0 := nonpos_of_mul_nonpos_right h1 h2
    linarith [h3, hb.2]
  refine ⟨?_, hb1⟩
  have hf4 : Work.Smooth.SphereJordan.pctgtCut₁ S H.t₁ H.s₁ 1 = γ.γ H.θ₁ := by
    rw [Work.Smooth.SphereJordan.pctgtCut₁]
    have hh : ((H.s₁ + 1 * (H.t₁ - H.s₁) : ℝ) : ℂ) = (H.t₁ : ℂ) := by push_cast; ring
    rw [hh]; exact H.hθ₁.symm
  have haeq : γ.γ (H.θ₂ + a * K) = γ.γ H.θ₁ := by
    rw [hb1] at heq
    rw [hf4] at heq
    exact heq
  by_contra ha1
  exact hKstep a ha ha1 haeq

/-! ## The inner arc does not meet `γ θ₁` before its endpoint -/

theorem pcgammaArc_ne_gammaθ₁ (hs : γ.IsSimple) {θ₂ θ₁ K : ℝ} (hθ : θ₂ < θ₁)
    (hθ' : θ₁ < θ₂ + 2 * Real.pi) (hK : K = θ₁ - θ₂ ∨ K = θ₁ - θ₂ - 2 * Real.pi) :
    ∀ a ∈ Set.Icc (0 : ℝ) 1, a ≠ 1 → γ.γ (θ₂ + a * K) ≠ γ.γ θ₁ := by
  intro a ha ha1 heq
  have hL : 0 < θ₁ - θ₂ := by linarith
  have hL2 : θ₁ - θ₂ < 2 * Real.pi := by linarith
  rcases hK with hK | hK
  · subst hK
    have habs : |(θ₂ + a * (θ₁ - θ₂)) - θ₁| < 2 * Real.pi := by
      have he : (θ₂ + a * (θ₁ - θ₂)) - θ₁ = (a - 1) * (θ₁ - θ₂) := by ring
      rw [he, abs_mul]
      have h1 : |a - 1| ≤ 1 := by rw [abs_le]; constructor <;> linarith [ha.1, ha.2]
      have h2 : |θ₁ - θ₂| < 2 * Real.pi := by rw [abs_of_pos hL]; exact hL2
      calc |a - 1| * |θ₁ - θ₂| ≤ 1 * |θ₁ - θ₂| := mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
        _ = |θ₁ - θ₂| := by ring
        _ < 2 * Real.pi := h2
    have h3 := Work.SphereJordan.pcinjOn_of_abs_lt hs habs heq
    have h4 : (a - 1) * (θ₁ - θ₂) = 0 := by linarith
    rcases mul_eq_zero.mp h4 with hh | hh
    · exact ha1 (by linarith)
    · exact absurd hh (ne_of_gt hL)
  · subst hK
    have ha_lt : a < 1 := lt_of_le_of_ne ha.2 ha1
    have habs : |(θ₂ + a * (θ₁ - θ₂ - 2 * Real.pi)) - θ₁| < 2 * Real.pi := by
      have he : (θ₂ + a * (θ₁ - θ₂ - 2 * Real.pi)) - θ₁ =
          -((1 - a) * (θ₁ - θ₂) + 2 * Real.pi * a) := by ring
      rw [he, abs_neg]
      have h1 : 0 ≤ (1 - a) * (θ₁ - θ₂) + 2 * Real.pi * a := by
        nlinarith [hL, ha_lt, ha.1, Real.pi_pos]
      rw [abs_of_nonneg h1]
      nlinarith [hL2, ha_lt, Real.pi_pos]
    have h3 := Work.SphereJordan.pcinjOn_of_abs_lt hs habs heq
    have hKneg : θ₁ - θ₂ - 2 * Real.pi < 0 := by linarith
    have he : a * (θ₁ - θ₂ - 2 * Real.pi) = θ₁ - θ₂ := by linarith
    have hnp : a * (θ₁ - θ₂ - 2 * Real.pi) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ha.1 hKneg.le
    linarith [hnp, he, hL]

/-! ## The upper target curve is simple -/

/-- The unfolded upper target curve is injective on one period. -/
theorem pctgtUpBun_injOn (H : pcSpanHyp h hs hball S) (b : Bool) :
    Set.InjOn (Work.SphereJordan.pctgtUpBun S H.t₁ H.s₁ H.t₂ H.s₂ b H.θ₁ H.θ₂)
      (Set.Ico 0 (2 * Real.pi)) := by
  have hLpos : 0 < H.θ₁ - H.θ₂ := by linarith [H.hθ]
  have hLlt : H.θ₁ - H.θ₂ < 2 * Real.pi := by linarith [H.hθ']
  cases b
  · refine pcinjOn_four_arcs (F := Work.SphereJordan.pctgtUpBun S H.t₁ H.s₁ H.t₂ H.s₂ false
        H.θ₁ H.θ₂)
      (f₁ := Work.Smooth.SphereJordan.pcsrcOuterUp S)
      (f₂ := Work.Smooth.SphereJordan.pctgtCut₂ S H.t₂ H.s₂)
      (f₃ := fun x : ℝ => γ.γ (H.θ₂ + x * (H.θ₁ - H.θ₂ - 2 * Real.pi)))
      (f₄ := Work.Smooth.SphereJordan.pctgtCut₁ S H.t₁ H.s₁)
      ?_ ?_ ?_ ?_
      (pcsrcOuterUp_injOn S) (pctgtCut₂_injOn S H.hout₂ (ne_of_lt H.ht₂s₂))
      (pcgammaArc_injOn hs (a := H.θ₂) (L := H.θ₁ - H.θ₂ - 2 * Real.pi)
        (by intro hh; linarith [hh, hLlt]) (by rw [abs_of_neg (by linarith)]; linarith))
      (pctgtCut₁_injOn S H.hout₁ (ne_of_lt H.ht₁s₁))
      (pcdisj₁₂ H) (pcdisj₁₃ H) (pcdisj₁₄ H)
      (pcdisj₂₃ H (K := H.θ₁ - H.θ₂ - 2 * Real.pi) (by intro hh; linarith [hh, hLlt])
        (by rw [abs_of_neg (by linarith)]; linarith))
      (pcdisj₂₄ H)
      (pcdisj₃₄ H (K := H.θ₁ - H.θ₂ - 2 * Real.pi)
        (pcgammaArc_ne_gammaθ₁ hs H.hθ H.hθ' (Or.inr rfl)))
    · intro σ hσ; simp only [Work.SphereJordan.pctgtUpBun]; rw [if_pos hσ]
    · intro σ h1 h2; simp only [Work.SphereJordan.pctgtUpBun]
      rw [if_neg (not_le.mpr h1), if_pos h2]
    · intro σ h1 h2; simp only [Work.SphereJordan.pctgtUpBun]
      rw [if_neg (by linarith [h1] : ¬ σ ≤ Real.pi / 2), if_neg (not_le.mpr h1), if_pos h2]
      simp
    · intro σ h1; simp only [Work.SphereJordan.pctgtUpBun]
      rw [if_neg (by linarith [h1] : ¬ σ ≤ Real.pi / 2),
        if_neg (not_le.mpr (by linarith [h1] : Real.pi < σ)), if_neg (not_le.mpr h1)]
  · refine pcinjOn_four_arcs (F := Work.SphereJordan.pctgtUpBun S H.t₁ H.s₁ H.t₂ H.s₂ true
        H.θ₁ H.θ₂)
      (f₁ := Work.Smooth.SphereJordan.pcsrcOuterUp S)
      (f₂ := Work.Smooth.SphereJordan.pctgtCut₂ S H.t₂ H.s₂)
      (f₃ := fun x : ℝ => γ.γ (H.θ₂ + x * (H.θ₁ - H.θ₂)))
      (f₄ := Work.Smooth.SphereJordan.pctgtCut₁ S H.t₁ H.s₁)
      ?_ ?_ ?_ ?_
      (pcsrcOuterUp_injOn S) (pctgtCut₂_injOn S H.hout₂ (ne_of_lt H.ht₂s₂))
      (pcgammaArc_injOn hs (a := H.θ₂) (L := H.θ₁ - H.θ₂) (ne_of_gt hLpos)
        (by rw [abs_of_pos hLpos]; exact hLlt))
      (pctgtCut₁_injOn S H.hout₁ (ne_of_lt H.ht₁s₁))
      (pcdisj₁₂ H) (pcdisj₁₃ H) (pcdisj₁₄ H)
      (pcdisj₂₃ H (K := H.θ₁ - H.θ₂) (ne_of_gt hLpos) (by rw [abs_of_pos hLpos]; exact hLlt))
      (pcdisj₂₄ H)
      (pcdisj₃₄ H (K := H.θ₁ - H.θ₂)
        (pcgammaArc_ne_gammaθ₁ hs H.hθ H.hθ' (Or.inl rfl)))
    · intro σ hσ; simp only [Work.SphereJordan.pctgtUpBun]; rw [if_pos hσ]
    · intro σ h1 h2; simp only [Work.SphereJordan.pctgtUpBun]
      rw [if_neg (not_le.mpr h1), if_pos h2]
    · intro σ h1 h2; simp only [Work.SphereJordan.pctgtUpBun]
      rw [if_neg (by linarith [h1] : ¬ σ ≤ Real.pi / 2), if_neg (not_le.mpr h1), if_pos h2]
      simp
    · intro σ h1; simp only [Work.SphereJordan.pctgtUpBun]
      rw [if_neg (by linarith [h1] : ¬ σ ≤ Real.pi / 2),
        if_neg (not_le.mpr (by linarith [h1] : Real.pi < σ)), if_neg (not_le.mpr h1)]

theorem pctgtUpPC_isSimple {γ : Work.Smooth.Jordan.PlaneCurve}
    (h : Work.Smooth.SphereJordan.PlaneHypothesis) (hs : γ.IsSimple)
    (hball : ∀ θ : ℝ, ‖γ.γ θ‖ < 1) (S : Work.Smooth.Jordan.PlaneSchoenflies γ)
    (H : Work.SphereJordan.pcSpanHyp h hs hball S) (b : Bool) : (H.pcupPC b).IsSimple := by
  intro σ₁ h₁ σ₂ h₂ heq
  rw [Work.SphereJordan.pcSpanHyp.pcupPC_apply, Work.SphereJordan.pcSpanHyp.pcupPC_apply] at heq
  rw [Work.SphereJordan.pctgtUpB_eq, Work.SphereJordan.pctgtUpB_eq] at heq
  rw [Work.SphereJordan.pcperPt_self h₁, Work.SphereJordan.pcperPt_self h₂] at heq
  exact pctgtUpBun_injOn H b h₁ h₂ heq

end

end Work.SphereJordan
