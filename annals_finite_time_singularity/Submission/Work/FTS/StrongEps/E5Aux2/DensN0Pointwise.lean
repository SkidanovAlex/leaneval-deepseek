/-
`DensN0Pointwise` — the pointwise bound
`K θ * |N₀ α (F_* + f) f s θ| ≤ C (1+C₀)(1+B) (Maj s + s/(1+s)²) cos θ` on `Iθ`
(`f = slice (JfamP ρ ε g) τ`, `K θ = 3 sin θ cos²θ`), built from `EpsDecay`'s slot bounds,
`FstarSlotBounds`, `L12XnBound` (`L₁₂(f)(s) ≤ CL C₀ α²`), `ClassC` (differentiability of the
`f`-slices, for the split of `pth F`, `Dz F` off `F_*`) and `AngFacts` (`K θ ≤ 2 cos θ`).
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.EpsMem
import Submission.Work.FTS.StrongEps.PZeroScheme
import Submission.Work.FTS.StrongEps.E5Aux2.L12XnBound
import Submission.Work.FTS.OpenPkg.Basic
import Submission.Work.Construction.L12_Fstar_eq
import Submission.Work.FTS.StrongEps.E5Aux2.AngFacts
import Submission.Work.FTS.StrongEps.E5Aux2.FstarSlotBounds
import Submission.Work.FTS.StrongEps.E5Aux2.Helpers

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E5Aux2

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false
set_option maxHeartbeats 1600000

theorem DensN0Pointwise :
    ∃ C : ℝ, 0 < C ∧ ∀ {α : ℝ}, α ∈ Set.Ioc 0 1 →
      ∀ {ρ : ℝ × ℝ → ℝ} {Φs : Fn} {E : Fn → Fn} {ε τ C₀ B : ℝ} {g : Fam} {Maj : ℝ → ℝ},
      Work.FTS.StrongEps.EpsDecay α ρ Φs E ε τ g Maj →
      Work.FTS.ClassC.ClassC α (slice (Work.FTS.StrongEps.JfamP ρ ε g) τ) →
      Work.FTS.Nonlin.Xn α (slice (Work.FTS.StrongEps.JfamP ρ ε g) τ) ≤ C₀ * α ^ 2 →
      Work.FTS.StrongGlobal.Xn6 α (slice (Work.FTS.StrongEps.JfamP ρ ε g) τ) ≤ B →
      ∀ s ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Work.Spaces.Iθ,
        Work.Spaces.K θ * |Work.Construction.N0 α
            (Work.Construction.Ftau α (Work.FTS.StrongEps.JfamP ρ ε g) τ)
            (slice (Work.FTS.StrongEps.JfamP ρ ε g) τ) s θ|
          ≤ C * (1 + C₀) * (1 + B) * (Maj s + s / (1 + s) ^ 2) * Real.cos θ := by
  obtain ⟨CL, hCLpos, hCL⟩ := L12XnBound
  obtain ⟨CFs, hCFspos, hCFs⟩ := FstarSlotBounds
  have hCL0 : 0 ≤ CL := hCLpos.le
  have hCFs0 : 0 ≤ CFs := hCFspos.le
  refine ⟨14 * CFs + 14 * CL * (CFs + 1) + 2 * CL + 8, ?_, ?_⟩
  · have h2 : 0 < 14 * CL * (CFs + 1) := by nlinarith
    linarith
  intro α hαIoc ρ Φs E ε τ C₀ B g Maj hDec hClass hXn hXn6 s hs θ hθ
  have hα : 0 < α := hαIoc.1
  have hα1 : α ≤ 1 := hαIoc.2
  have hs0 : (0 : ℝ) < s := hs
  obtain ⟨hMaj0, hMaj1, -, hSlot1, -⟩ := hDec
  -- ## the projected slice `f` and the full profile `F = F_* + f`
  set f : ℝ → ℝ → ℝ := slice (Work.FTS.StrongEps.JfamP ρ ε g) τ with hfdef
  set F : ℝ → ℝ → ℝ := Work.Construction.Ftau α (Work.FTS.StrongEps.JfamP ρ ε g) τ with hFdef
  have hF : ∀ z θ : ℝ, F z θ = Work.Construction.Fstar α z θ + f z θ := by
    intro z θ; rw [hFdef, hfdef]; rfl
  -- ## the two size constants are nonnegative
  have hC₀0 : 0 ≤ C₀ := by
    have hX : 0 ≤ Work.FTS.Nonlin.Xn α f := Work.Spaces.HkNorm_nonneg α 4 _
    nlinarith [hX, hXn, pow_pos hα 2]
  have hB0 : 0 ≤ B := by
    have hX : 0 ≤ Work.FTS.StrongGlobal.Xn6 α f := Work.Spaces.HkNorm_nonneg α 6 _
    linarith
  have hA1 : 1 ≤ (1 + C₀) * (1 + B) := by nlinarith
  have h1C : 0 ≤ 1 + C₀ := by linarith
  have h1B : 0 ≤ 1 + B := by linarith
  -- ## the angular facts
  obtain ⟨hKnn, hKcos, hcos0, -, -, -, -, -⟩ := AngFacts
  -- ## abbreviations
  set H : ℝ := s / (1 + s) ^ 2 with hHdef
  have hH0 : 0 ≤ H := by rw [hHdef]; exact div_nonneg hs0.le (sq_nonneg _)
  set Q : ℝ := Maj s + H with hQdef
  have hQ0 : 0 ≤ Q := by rw [hQdef]; exact add_nonneg (hMaj0 s) hH0
  have hHQ : H ≤ Q := by rw [hQdef]; linarith [hMaj0 s]
  have hMQ : Maj s ≤ Q := by rw [hQdef]; linarith [hH0]
  -- ## the slot bounds for `f`
  have hf0 : |f s θ| ≤ Maj s := by
    simpa using hSlot1 s hs θ 0 0 (by norm_num)
  have hDthf : |Work.Spaces.Dth f s θ| ≤ Maj s := by
    simpa using hSlot1 s hs θ 0 1 (by norm_num)
  have hDzf : |Work.Spaces.Dz f s θ| ≤ Maj s := by
    simpa using hSlot1 s hs θ 1 0 (by norm_num)
  -- ## the `F_*`-slot bounds
  obtain ⟨hFa, hs2pthFa, hDzFa, hKpthFa, -⟩ :=
    hCFs (α := α) (z := s) (θ := θ) hαIoc hs0 hθ
  have hL12Fa : Work.Construction.L12 (Work.Construction.Fstar α) s = 2 * α / (1 + s) :=
    Work.Construction.L12_Fstar_eq hα hα1 hs0.le
  have hL12Fa_abs : |Work.Construction.L12 (Work.Construction.Fstar α) s| ≤ 2 * α / (1 + s) :=
    le_of_eq (by rw [hL12Fa, abs_of_nonneg (by positivity)])
  -- ## the `L₁₂(f)`-size
  have hqo : Work.FTS.VocabO.HQo α 4 f :=
    ⟨hClass.reg, Work.FTS.OpenPkg.HkMem_mono_open hClass.reg 4 (by norm_num) hClass.mem⟩
  have hl : |Work.Construction.L12 f s| ≤ CL * (C₀ * α ^ 2) :=
    le_trans (hCL α hα f hqo s hs0.le) (mul_le_mul_of_nonneg_left hXn hCL0)
  -- ## the combined slot bound `CFs H + Maj s ≤ (CFs+1) Q`
  have hWle : CFs * H + Maj s ≤ (CFs + 1) * Q := by
    have h1 : CFs * H ≤ CFs * Q := mul_le_mul_of_nonneg_left hHQ hCFs0
    have h2 : CFs * Q + Maj s ≤ CFs * Q + Q := add_le_add_right hMQ (CFs * Q)
    have h3 : (CFs + 1) * Q = CFs * Q + Q := by ring
    linarith [h1, h2, h3]
  rcases eq_or_lt_of_le hθ.1 with hθz | hθz
  · -- the endpoint `θ = 0`: `K 0 = 0`
    subst hθz
    have hKz : Work.Spaces.K 0 = 0 := by rw [Work.Spaces.K, Real.sin_zero]; ring
    rw [hKz, zero_mul, Real.cos_zero, mul_one]
    have hCpos : 0 < 14 * CFs + 14 * CL * (CFs + 1) + 2 * CL + 8 := by
      have h2 : 0 < 14 * CL * (CFs + 1) := by nlinarith
      linarith
    exact mul_nonneg (mul_nonneg (mul_nonneg hCpos.le h1C) h1B) hQ0
  · rcases eq_or_lt_of_le hθ.2 with hθp | hθp
    · -- the endpoint `θ = π/2`: `K (π/2) = 0` and `cos (π/2) = 0`
      subst hθp
      have hKp : Work.Spaces.K (Real.pi / 2) = 0 := by
        rw [Work.Spaces.K, Real.cos_pi_div_two]; ring
      rw [hKp, zero_mul, Real.cos_pi_div_two, mul_zero]
    · -- ## the interior of `Iθ`
      have hθi : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hθz, hθp⟩
      have hK0 : 0 ≤ Work.Spaces.K θ := hKnn θ hθ
      have hKle : Work.Spaces.K θ ≤ 2 * Real.cos θ := hKcos θ hθ
      have hc0 : 0 ≤ Real.cos θ := hcos0 θ hθ
      -- ## the `θ`- and `z`-slices of `f` are differentiable (for the split of `Dz F`, `pth F`)
      have hfdθ : DifferentiableAt ℝ (fun θ' : ℝ => f s θ') θ :=
        ((hClass.reg.curry_θ hs0).differentiableOn (by simp)).differentiableAt
          (isOpen_Ioo.mem_nhds hθi)
      have hfdz : DifferentiableAt ℝ (fun z' : ℝ => f z' θ) s :=
        (hClass.reg.hasDerivAt_slice hθi hs0).differentiableAt
      have hpthF : |Work.Spaces.pth F s θ - Work.Spaces.pth (Work.Construction.Fstar α) s θ|
          ≤ |Work.Spaces.pth f s θ| := by
        have h := abs_deriv_add_sub_le (fun t : ℝ => Work.Construction.Fstar α s t)
          (fun t : ℝ => f s t) hfdθ
        have hcongr : (fun t : ℝ => Work.Construction.Fstar α s t + f s t) = fun t => F s t := by
          funext t; rw [hF s t]
        rw [hcongr] at h
        simpa only [Work.Spaces.pth] using h
      have hpzF : |Work.Spaces.pz F s θ - Work.Spaces.pz (Work.Construction.Fstar α) s θ|
          ≤ |Work.Spaces.pz f s θ| := by
        have h := abs_deriv_add_sub_le (fun t : ℝ => Work.Construction.Fstar α t θ)
          (fun t : ℝ => f t θ) hfdz
        have hcongr : (fun t : ℝ => Work.Construction.Fstar α t θ + f t θ) = fun t => F t θ := by
          funext t; rw [hF t θ]
        rw [hcongr] at h
        simpa only [Work.Spaces.pz] using h
      -- ## the combined slot bounds for `F = F_* + f`
      have hs2pthF : |Real.sin (2 * θ) * Work.Spaces.pth F s θ| ≤ (CFs + 1) * Q := by
        have hsplit : Real.sin (2 * θ) * Work.Spaces.pth F s θ
            = Real.sin (2 * θ) * Work.Spaces.pth (Work.Construction.Fstar α) s θ
              + Real.sin (2 * θ)
                * (Work.Spaces.pth F s θ - Work.Spaces.pth (Work.Construction.Fstar α) s θ) := by
          ring
        rw [hsplit]
        have h2 : |Real.sin (2 * θ)
            * (Work.Spaces.pth F s θ - Work.Spaces.pth (Work.Construction.Fstar α) s θ)|
            ≤ |Work.Spaces.Dth f s θ| := by
          rw [abs_mul]
          calc |Real.sin (2 * θ)| * |Work.Spaces.pth F s θ
                - Work.Spaces.pth (Work.Construction.Fstar α) s θ|
              ≤ |Real.sin (2 * θ)| * |Work.Spaces.pth f s θ| :=
                mul_le_mul_of_nonneg_left hpthF (abs_nonneg _)
            _ = |Work.Spaces.Dth f s θ| := by rw [Work.Spaces.Dth, abs_mul]
        have h3 : |Real.sin (2 * θ) * Work.Spaces.pth (Work.Construction.Fstar α) s θ
              + Real.sin (2 * θ)
                * (Work.Spaces.pth F s θ - Work.Spaces.pth (Work.Construction.Fstar α) s θ)|
            ≤ CFs * H + Maj s := by
          have h1 := abs_add_le
            (Real.sin (2 * θ) * Work.Spaces.pth (Work.Construction.Fstar α) s θ)
            (Real.sin (2 * θ)
              * (Work.Spaces.pth F s θ - Work.Spaces.pth (Work.Construction.Fstar α) s θ))
          linarith [h1, hs2pthFa, h2, hDthf]
        linarith [h3, hWle]
      have hDzF : |Work.Spaces.Dz F s θ| ≤ (CFs + 1) * Q := by
        have hsplit : Work.Spaces.Dz F s θ
            = Work.Spaces.Dz (Work.Construction.Fstar α) s θ
              + (Work.Spaces.Dz F s θ - Work.Spaces.Dz (Work.Construction.Fstar α) s θ) := by
          ring
        rw [hsplit]
        have h2 : |Work.Spaces.Dz F s θ - Work.Spaces.Dz (Work.Construction.Fstar α) s θ|
            ≤ |Work.Spaces.Dz f s θ| := by
          have h3 : Work.Spaces.Dz F s θ - Work.Spaces.Dz (Work.Construction.Fstar α) s θ
              = s * (Work.Spaces.pz F s θ
                  - Work.Spaces.pz (Work.Construction.Fstar α) s θ) := by
            rw [Work.Spaces.Dz, Work.Spaces.Dz]; ring
          have h4 : |s * (Work.Spaces.pz F s θ - Work.Spaces.pz (Work.Construction.Fstar α) s θ)|
              = s * |Work.Spaces.pz F s θ - Work.Spaces.pz (Work.Construction.Fstar α) s θ| := by
            rw [abs_mul, abs_of_pos hs0]
          rw [h3, h4]
          calc s * |Work.Spaces.pz F s θ - Work.Spaces.pz (Work.Construction.Fstar α) s θ|
              ≤ s * |Work.Spaces.pz f s θ| := mul_le_mul_of_nonneg_left hpzF hs0.le
            _ = |Work.Spaces.Dz f s θ| := by rw [Work.Spaces.Dz, abs_mul, abs_of_pos hs0]
        have h4 : |Work.Spaces.Dz (Work.Construction.Fstar α) s θ
              + (Work.Spaces.Dz F s θ - Work.Spaces.Dz (Work.Construction.Fstar α) s θ)|
            ≤ CFs * H + Maj s := by
          have h1 := abs_add_le (Work.Spaces.Dz (Work.Construction.Fstar α) s θ)
            (Work.Spaces.Dz F s θ - Work.Spaces.Dz (Work.Construction.Fstar α) s θ)
          linarith [h1, hDzFa, h2, hDzf]
        linarith [h4, hWle]
      -- ## `|c2m θ| ≤ 2`
      have hc2m : |Work.Construction.c2m θ| ≤ 2 := by
        have h1 : Work.Construction.c2m θ = Real.cos (2 * θ) - Real.sin θ ^ 2 := rfl
        rw [h1, abs_le]
        have hsin0 : 0 ≤ Real.sin θ :=
          Real.sin_nonneg_of_mem_Icc ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
        constructor
        · nlinarith [Real.neg_one_le_cos (2 * θ), sq_nonneg (Real.sin θ), Real.sin_le_one θ, hsin0]
        · nlinarith [Real.cos_le_one (2 * θ), sq_nonneg (Real.sin θ)]
      -- ## the ratio bound `2α/(1+s) ≤ 2`
      have hrat : 2 * α / (1 + s) ≤ 2 := by
        rw [div_le_iff₀ (by linarith : (0 : ℝ) < 1 + s)]
        nlinarith [hα.le]
      -- ## T1
      set T1 : ℝ := (3 / (2 * α)) * Real.sin (2 * θ)
        * Work.Construction.L12 (Work.Construction.Fstar α) s
        * Work.Spaces.pth (Work.Construction.Fstar α) s θ with hT1def
      set T2 : ℝ := Work.Construction.c2m θ
        * Work.Construction.L12 (Work.Construction.Fstar α) s
        * Work.Spaces.Dz (Work.Construction.Fstar α) s θ with hT2def
      set T3 : ℝ := (1 / α) * Work.Construction.L12 f s * f s θ with hT3def
      set T4 : ℝ := (3 / (2 * α)) * Real.sin (2 * θ) * Work.Construction.L12 f s
        * Work.Spaces.pth F s θ with hT4def
      set T5 : ℝ := Work.Construction.c2m θ * Work.Construction.L12 f s
        * Work.Spaces.Dz F s θ with hT5def
      set T6 : ℝ := Work.Construction.c2m θ
        * Work.Construction.L12 (Work.Construction.Fstar α) s
        * Work.Spaces.Dz f s θ with hT6def
      have hT1fac : |T1| ≤ 3 * CFs * H := by
        have h0 : |T1| ≤ |3 / (2 * α)| * |Real.sin (2 * θ)|
            * |Work.Construction.L12 (Work.Construction.Fstar α) s|
            * |Work.Spaces.pth (Work.Construction.Fstar α) s θ| := by
          rw [hT1def]
          exact abs_mul4_le _ _ _ _
        rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 3 / (2 * α))] at h0
        have h3 : 3 / (2 * α) * |Real.sin (2 * θ)|
            * |Work.Construction.L12 (Work.Construction.Fstar α) s|
            * |Work.Spaces.pth (Work.Construction.Fstar α) s θ|
            = 3 / (2 * α) * |Work.Construction.L12 (Work.Construction.Fstar α) s|
              * (|Real.sin (2 * θ)| * |Work.Spaces.pth (Work.Construction.Fstar α) s θ|) := by
          ring
        rw [h3] at h0
        have h4 : |Real.sin (2 * θ)| * |Work.Spaces.pth (Work.Construction.Fstar α) s θ|
            = |Real.sin (2 * θ) * Work.Spaces.pth (Work.Construction.Fstar α) s θ| := by
          rw [abs_mul]
        rw [h4] at h0
        have h6 : 3 / (2 * α) * |Work.Construction.L12 (Work.Construction.Fstar α) s|
            * |Real.sin (2 * θ) * Work.Spaces.pth (Work.Construction.Fstar α) s θ|
            ≤ 3 / (2 * α) * (2 * α / (1 + s)) * (CFs * H) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hL12Fa_abs (by positivity)) hs2pthFa
            (abs_nonneg _) (by positivity)
        have h5 : 3 / (2 * α) * (2 * α / (1 + s)) * (CFs * H) = 3 * CFs * H / (1 + s) := by
          field_simp
        have hnn : 0 ≤ 3 * CFs * H := mul_nonneg (mul_nonneg (by norm_num) hCFs0) hH0
        have h7 : 3 * CFs * H / (1 + s) ≤ 3 * CFs * H := by
          rw [div_le_iff₀ (by linarith : (0 : ℝ) < 1 + s)]
          have h8 : 0 ≤ 3 * CFs * H * s := mul_nonneg hnn hs0.le
          linarith
        linarith [h0, h6, h5, h7]
      have hT1 : Work.Spaces.K θ * |T1| ≤ 6 * CFs * Q * Real.cos θ := by
        have hX0 : 0 ≤ 3 * CFs * H := mul_nonneg (mul_nonneg (by norm_num) hCFs0) hH0
        have h1 : Work.Spaces.K θ * |T1| ≤ Work.Spaces.K θ * (3 * CFs * H) :=
          mul_le_mul_of_nonneg_left hT1fac hK0
        have h2 : Work.Spaces.K θ * (3 * CFs * H) ≤ (2 * Real.cos θ) * (3 * CFs * H) :=
          mul_le_mul_of_nonneg_right hKle hX0
        have hXQ0 : 0 ≤ 3 * CFs * Q := mul_nonneg (mul_nonneg (by norm_num) hCFs0) hQ0
        have h3 : (2 * Real.cos θ) * (3 * CFs * H) ≤ (2 * Real.cos θ) * (3 * CFs * Q) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hHQ (by positivity)) (by positivity)
        have h4 : (2 * Real.cos θ) * (3 * CFs * Q) = 6 * CFs * Q * Real.cos θ := by ring
        linarith [h1, h2, h3, h4]
      have hT2fac : |T2| ≤ 4 * CFs * H := by
        have h0 : |T2| ≤ |Work.Construction.c2m θ|
            * |Work.Construction.L12 (Work.Construction.Fstar α) s|
            * |Work.Spaces.Dz (Work.Construction.Fstar α) s θ| := by
          rw [hT2def]
          exact abs_mul3_le _ _ _
        have h3 : |Work.Construction.c2m θ|
            * |Work.Construction.L12 (Work.Construction.Fstar α) s|
            * |Work.Spaces.Dz (Work.Construction.Fstar α) s θ|
            ≤ 2 * (2 * α / (1 + s)) * (CFs * H) :=
          mul_le_mul (mul_le_mul hc2m hL12Fa_abs (abs_nonneg _) (by norm_num)) hDzFa
            (abs_nonneg _) (by positivity)
        have hnn : 0 ≤ CFs * H := mul_nonneg hCFs0 hH0
        have h5 : 2 * (2 * α / (1 + s)) ≤ 4 := by linarith [hrat]
        have h6 := mul_le_mul_of_nonneg_right h5 hnn
        have h4 : 2 * (2 * α / (1 + s)) * (CFs * H) ≤ 4 * CFs * H := by linarith [h6]
        linarith [h0, h3, h4]
      have hT2 : Work.Spaces.K θ * |T2| ≤ 8 * CFs * Q * Real.cos θ := by
        have hX0 : 0 ≤ 4 * CFs * H := mul_nonneg (mul_nonneg (by norm_num) hCFs0) hH0
        have h1 : Work.Spaces.K θ * |T2| ≤ Work.Spaces.K θ * (4 * CFs * H) :=
          mul_le_mul_of_nonneg_left hT2fac hK0
        have h2 : Work.Spaces.K θ * (4 * CFs * H) ≤ (2 * Real.cos θ) * (4 * CFs * H) :=
          mul_le_mul_of_nonneg_right hKle hX0
        have h3 : (2 * Real.cos θ) * (4 * CFs * H) ≤ (2 * Real.cos θ) * (4 * CFs * Q) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hHQ (by positivity)) (by positivity)
        have h4 : (2 * Real.cos θ) * (4 * CFs * Q) = 8 * CFs * Q * Real.cos θ := by ring
        linarith [h1, h2, h3, h4]
      have hT3fac : |T3| ≤ CL * C₀ * Q := by
        have h0 : |T3| ≤ |1 / α| * |Work.Construction.L12 f s| * |f s θ| := by
          rw [hT3def]
          exact abs_mul3_le _ _ _
        rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / α)] at h0
        have h3 : 1 / α * |Work.Construction.L12 f s| * |f s θ|
            ≤ 1 / α * (CL * (C₀ * α ^ 2)) * Maj s :=
          mul_le_mul (mul_le_mul_of_nonneg_left hl (by positivity)) hf0
            (abs_nonneg _) (by positivity)
        have h5 : 1 / α * (CL * (C₀ * α ^ 2)) * Maj s = CL * C₀ * α * Maj s := by
          field_simp
        have hnn : 0 ≤ CL * C₀ := mul_nonneg hCL0 hC₀0
        have h7 : CL * C₀ * α ≤ CL * C₀ * 1 := mul_le_mul_of_nonneg_left hα1 hnn
        have h8 : CL * C₀ * α * Maj s ≤ CL * C₀ * Maj s := by
          have h9 := mul_le_mul_of_nonneg_right h7 (hMaj0 s)
          linarith [h9]
        have h10 : CL * C₀ * Maj s ≤ CL * C₀ * Q := mul_le_mul_of_nonneg_left hMQ hnn
        have h6 : CL * C₀ * α * Maj s ≤ CL * C₀ * Q := by linarith [h8, h10]
        linarith [h0, h3, h5, h6]
      have hT3 : Work.Spaces.K θ * |T3| ≤ 2 * CL * (1 + C₀) * Q * Real.cos θ := by
        have hX0 : 0 ≤ CL * C₀ * Q := mul_nonneg (mul_nonneg hCL0 hC₀0) hQ0
        have h1 : Work.Spaces.K θ * |T3| ≤ Work.Spaces.K θ * (CL * C₀ * Q) :=
          mul_le_mul_of_nonneg_left hT3fac hK0
        have h2 : Work.Spaces.K θ * (CL * C₀ * Q) ≤ (2 * Real.cos θ) * (CL * C₀ * Q) :=
          mul_le_mul_of_nonneg_right hKle hX0
        have h5 : CL * C₀ ≤ CL * (1 + C₀) := mul_le_mul_of_nonneg_left (by linarith) hCL0
        have h6 : CL * C₀ * Q ≤ CL * (1 + C₀) * Q := mul_le_mul_of_nonneg_right h5 hQ0
        have h3 : (2 * Real.cos θ) * (CL * C₀ * Q) ≤ (2 * Real.cos θ) * (CL * (1 + C₀) * Q) :=
          mul_le_mul_of_nonneg_left h6 (by positivity)
        have h4 : (2 * Real.cos θ) * (CL * (1 + C₀) * Q)
            = 2 * CL * (1 + C₀) * Q * Real.cos θ := by ring
        linarith [h1, h2, h3, h4]
      have hT4fac : |T4| ≤ 3 * CL * (CFs + 1) * (1 + C₀) * Q := by
        have h0 : |T4| ≤ |3 / (2 * α)| * |Real.sin (2 * θ)|
            * |Work.Construction.L12 f s| * |Work.Spaces.pth F s θ| := by
          rw [hT4def]
          exact abs_mul4_le _ _ _ _
        rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 3 / (2 * α))] at h0
        have h3 : 3 / (2 * α) * |Real.sin (2 * θ)| * |Work.Construction.L12 f s|
            * |Work.Spaces.pth F s θ|
            = 3 / (2 * α) * |Work.Construction.L12 f s|
              * (|Real.sin (2 * θ)| * |Work.Spaces.pth F s θ|) := by ring
        rw [h3] at h0
        have h4 : |Real.sin (2 * θ)| * |Work.Spaces.pth F s θ|
            = |Real.sin (2 * θ) * Work.Spaces.pth F s θ| := by rw [abs_mul]
        rw [h4] at h0
        have h6 : 3 / (2 * α) * |Work.Construction.L12 f s|
            * |Real.sin (2 * θ) * Work.Spaces.pth F s θ|
            ≤ 3 / (2 * α) * (CL * (C₀ * α ^ 2)) * ((CFs + 1) * Q) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hl (by positivity)) hs2pthF
            (abs_nonneg _) (by positivity)
        have h8 : 3 / (2 * α) * (CL * (C₀ * α ^ 2)) * ((CFs + 1) * Q)
            = 3 / 2 * CL * C₀ * α * ((CFs + 1) * Q) := by field_simp
        have hZ0 : 0 ≤ (CFs + 1) * Q := by positivity
        have hnn : 0 ≤ CL * C₀ := mul_nonneg hCL0 hC₀0
        have h11 : CL * C₀ * α ≤ CL * C₀ := by
          have h12 := mul_le_mul_of_nonneg_left hα1 hnn
          linarith [h12]
        have h13 : CL * C₀ * α * ((CFs + 1) * Q) ≤ CL * C₀ * ((CFs + 1) * Q) :=
          mul_le_mul_of_nonneg_right h11 hZ0
        have h14 : CL * C₀ * ((CFs + 1) * Q) ≤ CL * (1 + C₀) * ((CFs + 1) * Q) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (by linarith : C₀ ≤ 1 + C₀) hCL0) hZ0
        have h15 : CL * C₀ * α * ((CFs + 1) * Q) ≤ CL * (1 + C₀) * ((CFs + 1) * Q) := by
          linarith [h13, h14]
        have h16 : 3 / 2 * (CL * C₀ * α * ((CFs + 1) * Q))
            ≤ 3 / 2 * (CL * (1 + C₀) * ((CFs + 1) * Q)) :=
          mul_le_mul_of_nonneg_left h15 (by norm_num)
        have hD0 : 0 ≤ CL * (1 + C₀) * ((CFs + 1) * Q) := by positivity
        have h18 : 3 / 2 * (CL * (1 + C₀) * ((CFs + 1) * Q))
            ≤ 3 * (CL * (1 + C₀) * ((CFs + 1) * Q)) := by linarith [hD0]
        have h19 : 3 * (CL * (1 + C₀) * ((CFs + 1) * Q))
            = 3 * CL * (CFs + 1) * (1 + C₀) * Q := by ring
        have hfinal : 3 / 2 * CL * C₀ * α * ((CFs + 1) * Q)
            ≤ 3 * CL * (CFs + 1) * (1 + C₀) * Q := by
          calc 3 / 2 * CL * C₀ * α * ((CFs + 1) * Q)
              = 3 / 2 * (CL * C₀ * α * ((CFs + 1) * Q)) := by ring
            _ ≤ 3 / 2 * (CL * (1 + C₀) * ((CFs + 1) * Q)) := h16
            _ ≤ 3 * CL * (CFs + 1) * (1 + C₀) * Q := by linarith [h18, h19]
        linarith [h0, h6, h8, hfinal]
      have hT4 : Work.Spaces.K θ * |T4| ≤ 6 * CL * (CFs + 1) * (1 + C₀) * Q * Real.cos θ := by
        have hX0 : 0 ≤ 3 * CL * (CFs + 1) * (1 + C₀) * Q := by positivity
        have h1 : Work.Spaces.K θ * |T4|
            ≤ Work.Spaces.K θ * (3 * CL * (CFs + 1) * (1 + C₀) * Q) :=
          mul_le_mul_of_nonneg_left hT4fac hK0
        have h2 : Work.Spaces.K θ * (3 * CL * (CFs + 1) * (1 + C₀) * Q)
            ≤ (2 * Real.cos θ) * (3 * CL * (CFs + 1) * (1 + C₀) * Q) :=
          mul_le_mul_of_nonneg_right hKle hX0
        have h4 : (2 * Real.cos θ) * (3 * CL * (CFs + 1) * (1 + C₀) * Q)
            = 6 * CL * (CFs + 1) * (1 + C₀) * Q * Real.cos θ := by ring
        linarith [h1, h2, h4]
      have hT5fac : |T5| ≤ 4 * CL * (CFs + 1) * (1 + C₀) * Q := by
        have h0 : |T5| ≤ |Work.Construction.c2m θ| * |Work.Construction.L12 f s|
            * |Work.Spaces.Dz F s θ| := by
          rw [hT5def]
          exact abs_mul3_le _ _ _
        have h3 : |Work.Construction.c2m θ| * |Work.Construction.L12 f s|
            * |Work.Spaces.Dz F s θ| ≤ 2 * (CL * (C₀ * α ^ 2)) * ((CFs + 1) * Q) :=
          mul_le_mul (mul_le_mul hc2m hl (abs_nonneg _) (by norm_num)) hDzF
            (abs_nonneg _) (by positivity)
        have hZ0 : 0 ≤ (CFs + 1) * Q := by positivity
        have hnn : 0 ≤ CL * C₀ := mul_nonneg hCL0 hC₀0
        have hα2 : α ^ 2 ≤ 1 := by nlinarith [hα1, hα.le]
        have h9 : CL * C₀ * α ^ 2 ≤ CL * C₀ := by
          have h10 := mul_le_mul_of_nonneg_left hα2 hnn
          linarith [h10]
        have h10 : CL * C₀ * α ^ 2 * ((CFs + 1) * Q) ≤ CL * C₀ * ((CFs + 1) * Q) :=
          mul_le_mul_of_nonneg_right h9 hZ0
        have h11 : CL * C₀ * ((CFs + 1) * Q) ≤ CL * (1 + C₀) * ((CFs + 1) * Q) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (by linarith : C₀ ≤ 1 + C₀) hCL0) hZ0
        have h13 : CL * (1 + C₀) * ((CFs + 1) * Q) = CL * (CFs + 1) * (1 + C₀) * Q := by ring
        have h15 : 2 * (CL * (C₀ * α ^ 2)) * ((CFs + 1) * Q)
            = 2 * (CL * C₀ * α ^ 2 * ((CFs + 1) * Q)) := by ring
        have hfinal : 2 * (CL * C₀ * α ^ 2 * ((CFs + 1) * Q))
            ≤ 4 * CL * (CFs + 1) * (1 + C₀) * Q := by
          have hx : 0 ≤ CL * (CFs + 1) * (1 + C₀) * Q := by positivity
          calc 2 * (CL * C₀ * α ^ 2 * ((CFs + 1) * Q))
              ≤ 2 * (CL * C₀ * ((CFs + 1) * Q)) := by linarith [h10]
            _ ≤ 2 * (CL * (1 + C₀) * ((CFs + 1) * Q)) := by linarith [h11]
            _ = 2 * CL * (CFs + 1) * (1 + C₀) * Q := by rw [h13]; ring_nf
            _ ≤ 4 * CL * (CFs + 1) * (1 + C₀) * Q := by linarith [hx]
        linarith [h0, h3, h15, hfinal]
      have hT5 : Work.Spaces.K θ * |T5| ≤ 8 * CL * (CFs + 1) * (1 + C₀) * Q * Real.cos θ := by
        have hX0 : 0 ≤ 4 * CL * (CFs + 1) * (1 + C₀) * Q := by positivity
        have h1 : Work.Spaces.K θ * |T5|
            ≤ Work.Spaces.K θ * (4 * CL * (CFs + 1) * (1 + C₀) * Q) :=
          mul_le_mul_of_nonneg_left hT5fac hK0
        have h2 : Work.Spaces.K θ * (4 * CL * (CFs + 1) * (1 + C₀) * Q)
            ≤ (2 * Real.cos θ) * (4 * CL * (CFs + 1) * (1 + C₀) * Q) :=
          mul_le_mul_of_nonneg_right hKle hX0
        have h4 : (2 * Real.cos θ) * (4 * CL * (CFs + 1) * (1 + C₀) * Q)
            = 8 * CL * (CFs + 1) * (1 + C₀) * Q * Real.cos θ := by ring
        linarith [h1, h2, h4]
      have hT6fac : |T6| ≤ 4 * Q := by
        have h0 : |T6| ≤ |Work.Construction.c2m θ|
            * |Work.Construction.L12 (Work.Construction.Fstar α) s|
            * |Work.Spaces.Dz f s θ| := by
          rw [hT6def]
          exact abs_mul3_le _ _ _
        have h3 : |Work.Construction.c2m θ|
            * |Work.Construction.L12 (Work.Construction.Fstar α) s|
            * |Work.Spaces.Dz f s θ| ≤ 2 * (2 * α / (1 + s)) * Maj s :=
          mul_le_mul (mul_le_mul hc2m hL12Fa_abs (abs_nonneg _) (by norm_num)) hDzf
            (abs_nonneg _) (by positivity)
        have h5 : 2 * (2 * α / (1 + s)) ≤ 4 := by linarith [hrat]
        have h6 : 2 * (2 * α / (1 + s)) * Maj s ≤ 4 * Maj s :=
          mul_le_mul_of_nonneg_right h5 (hMaj0 s)
        have h7 : 4 * Maj s ≤ 4 * Q := mul_le_mul_of_nonneg_left hMQ (by norm_num)
        linarith [h0, h3, h6, h7]
      have hT6 : Work.Spaces.K θ * |T6| ≤ 8 * Q * Real.cos θ := by
        have hX0 : 0 ≤ 4 * Q := by linarith [hQ0]
        have h1 : Work.Spaces.K θ * |T6| ≤ Work.Spaces.K θ * (4 * Q) :=
          mul_le_mul_of_nonneg_left hT6fac hK0
        have h2 : Work.Spaces.K θ * (4 * Q) ≤ (2 * Real.cos θ) * (4 * Q) :=
          mul_le_mul_of_nonneg_right hKle hX0
        have h4 : (2 * Real.cos θ) * (4 * Q) = 8 * Q * Real.cos θ := by ring
        linarith [h1, h2, h4]
      -- ## assembly
      have hexp : Work.Construction.N0 α F f s θ = T1 + (-T2) + T3 + T4 + (-T5) + (-T6) := by
        rw [hT1def, hT2def, hT3def, hT4def, hT5def, hT6def]
        simp only [Work.Construction.N0, Work.Construction.s2]
        ring
      rw [hexp]
      have hsumabs : |T1 + -T2 + T3 + T4 + -T5 + -T6|
          ≤ |T1| + |T2| + |T3| + |T4| + |T5| + |T6| := by
        simpa only [abs_neg] using abs_six_le T1 (-T2) T3 T4 (-T5) (-T6)
      have hXX : Work.Spaces.K θ * (|T1| + |T2| + |T3| + |T4| + |T5| + |T6|)
          = Work.Spaces.K θ * |T1| + Work.Spaces.K θ * |T2| + Work.Spaces.K θ * |T3|
            + Work.Spaces.K θ * |T4| + Work.Spaces.K θ * |T5| + Work.Spaces.K θ * |T6| := by
        ring
      have hmain : Work.Spaces.K θ * |T1 + -T2 + T3 + T4 + -T5 + -T6|
          ≤ (14 * CFs + 2 * CL * (1 + C₀) + 14 * CL * (CFs + 1) * (1 + C₀) + 8) * Q
            * Real.cos θ := by
        have h1 : Work.Spaces.K θ * |T1 + -T2 + T3 + T4 + -T5 + -T6|
            ≤ Work.Spaces.K θ * (|T1| + |T2| + |T3| + |T4| + |T5| + |T6|) :=
          mul_le_mul_of_nonneg_left hsumabs hK0
        linarith [h1, hXX, hT1, hT2, hT3, hT4, hT5, hT6]
      -- ## the final scalar comparison
      have hsc : 14 * CFs + 2 * CL * (1 + C₀) + 14 * CL * (CFs + 1) * (1 + C₀) + 8
          ≤ (14 * CFs + 14 * CL * (CFs + 1) + 2 * CL + 8) * (1 + C₀) * (1 + B) := by
        have hA0 : 0 ≤ 14 * CFs := by linarith
        have hB0' : 0 ≤ 14 * CL * (CFs + 1) := by positivity
        have hC0' : 0 ≤ 2 * CL := by linarith
        have h1 : 14 * CFs ≤ 14 * CFs * ((1 + C₀) * (1 + B)) := by
          have h := mul_le_mul_of_nonneg_left hA1 hA0
          linarith [h]
        have h1B1 : (1 : ℝ) ≤ 1 + B := by linarith
        have h2 : 1 + C₀ ≤ (1 + C₀) * (1 + B) := by
          have h := mul_le_mul_of_nonneg_left h1B1 h1C
          linarith [h]
        have h3 : 2 * CL * (1 + C₀) ≤ 2 * CL * ((1 + C₀) * (1 + B)) :=
          mul_le_mul_of_nonneg_left h2 hC0'
        have h4 : 14 * CL * (CFs + 1) * (1 + C₀)
            ≤ 14 * CL * (CFs + 1) * ((1 + C₀) * (1 + B)) := by
          have h := mul_le_mul_of_nonneg_left h2 hB0'
          linarith [h]
        have h5 : 8 ≤ 8 * ((1 + C₀) * (1 + B)) := by
          have h := mul_le_mul_of_nonneg_left hA1 (by norm_num : (0 : ℝ) ≤ 8)
          linarith [h]
        have h6 : (14 * CFs + 14 * CL * (CFs + 1) + 2 * CL + 8) * ((1 + C₀) * (1 + B))
            = 14 * CFs * ((1 + C₀) * (1 + B))
              + 14 * CL * (CFs + 1) * ((1 + C₀) * (1 + B))
              + 2 * CL * ((1 + C₀) * (1 + B)) + 8 * ((1 + C₀) * (1 + B)) := by ring
        have h7 : (14 * CFs + 14 * CL * (CFs + 1) + 2 * CL + 8) * (1 + C₀) * (1 + B)
            = (14 * CFs + 14 * CL * (CFs + 1) + 2 * CL + 8) * ((1 + C₀) * (1 + B)) := by ring
        linarith [h1, h3, h4, h5, h6, h7]
      have hfin : (14 * CFs + 2 * CL * (1 + C₀) + 14 * CL * (CFs + 1) * (1 + C₀) + 8) * Q
            * Real.cos θ
          ≤ (14 * CFs + 14 * CL * (CFs + 1) + 2 * CL + 8) * (1 + C₀) * (1 + B) * Q
            * Real.cos θ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hsc hQ0) hc0
      linarith [hmain, hfin]

end Work.FTS.StrongEps.E5Aux2
