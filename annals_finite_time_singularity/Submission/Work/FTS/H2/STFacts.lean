/-
Copyright: work module for the Elgindi finite-time singularity project.

# Pointwise facts for `SpecialTransport`

This file collects the pointwise facts on which the proof of
`Work.FTS.H2.SpecialTransport` rests:

* `abs_DthIter_Sfun_le`: `|D_θ^r (sin 2·)| ≤ A_r · sin(2·)` for `r ≤ 3` (proved by an explicit
  computation of the three iterates) — the "extra `sin` factor" which makes `D_θ` a
  `sin(2θ)`-divisible operator.
* `dthIter_mul_le_open`: the local Leibniz bound for `D_θ^i` on the open interval `(0,π/2)`,
  stated with only the interior smoothness hypotheses, so that it applies to `SmoothInt`
  functions and their multipliers.
* `sin_mul_dzIter_pth`: the exact identity `sin(2θ) · D_z^c(∂_θ g) = D_z^c D_θ g`.
* `STSigmaBound`: `sin(2θ)·D_θ^c(∂_θ g)` is a bounded combination of the `D_θ^m g`, `1 ≤ m ≤ c+1`
  (Elgindi's commutator identity, obtained from `Work.Elliptic.WtoW_g_ident`).
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.IntervalCases
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.H2.STBounds2
import Submission.Work.FTS.H2.Whz_Wm_sq
import Submission.Work.Elliptic.WtoW_g_bound
import Submission.Work.Elliptic.WtoW_g_coeff_bound
import Submission.Work.Spaces.DzIterSmoothOn
import Submission.Work.Spaces.DzDthIterCommOn
import Submission.Work.Spaces.DthIter_mul
import Submission.Work.Spaces.DthIter_mul_le
import Submission.Work.Spaces.mixed_mul_eq
import Submission.Work.Spaces.WlInf_terms
import Submission.Work.Spaces.SmoothCompact_Aux
import Submission.Work.FTS.H2.mixed_sin_bound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## The angular function `sin (2·)` and its `D_θ`-iterates -/

/-- The angular function `θ ↦ sin(2θ)`, viewed as a function of `(z,θ)`.  It is the
multiplier relating `D_θ` and `∂_θ`. -/
def Sfun : ℝ → ℝ → ℝ := fun _ θ => Real.sin (2 * θ)

/-- The constant multiplying `sin(2θ)` in the bound for `D_θ^r (sin 2·)`. -/
def Asin : ℕ → ℝ
  | 0 => 1
  | 1 => 2
  | 2 => 4
  | 3 => 48
  | _ + 4 => 384

theorem Asin_pos (r : ℕ) : 0 < Asin r := by
  rcases r with _ | _ | _ | _ | _ <;> norm_num [Asin]

theorem hasDerivAt_sin_two (θ : ℝ) :
    HasDerivAt (fun θ' : ℝ => Real.sin (2 * θ')) (2 * Real.cos (2 * θ)) θ := by
  have h2 : HasDerivAt (fun θ' : ℝ => 2 * θ') 2 θ := by
    simpa using (hasDerivAt_id θ).const_mul (2 : ℝ)
  have h := (Real.hasDerivAt_sin (2 * θ)).comp θ h2
  simpa [Function.comp_def, mul_comm] using h

theorem hasDerivAt_cos_two (θ : ℝ) :
    HasDerivAt (fun θ' : ℝ => Real.cos (2 * θ')) (-(Real.sin (2 * θ)) * 2) θ := by
  have h2 : HasDerivAt (fun θ' : ℝ => 2 * θ') 2 θ := by
    simpa using (hasDerivAt_id θ).const_mul (2 : ℝ)
  have h := (Real.hasDerivAt_cos (2 * θ)).comp θ h2
  simpa [Function.comp_def] using h

theorem hasDerivAt_two_cos_two (θ : ℝ) :
    HasDerivAt (fun θ' : ℝ => 2 * Real.cos (2 * θ')) (2 * (-(Real.sin (2 * θ)) * 2)) θ := by
  have h := (hasDerivAt_cos_two θ).const_mul (2 : ℝ)
  convert h using 1 <;> ring

theorem deriv_sin_two (θ : ℝ) :
    deriv (fun θ' : ℝ => Real.sin (2 * θ')) θ = 2 * Real.cos (2 * θ) :=
  (hasDerivAt_sin_two θ).deriv

theorem DthIter_one_Sfun : Work.Spaces.DthIter 1 Sfun
    = fun _ θ => Real.sin (2 * θ) * (2 * Real.cos (2 * θ)) := by
  funext z θ
  show Real.sin (2 * θ) * Work.Spaces.pth Sfun z θ
      = Real.sin (2 * θ) * (2 * Real.cos (2 * θ))
  rw [show Work.Spaces.pth Sfun z θ = deriv (fun θ' : ℝ => Real.sin (2 * θ')) θ from rfl,
    deriv_sin_two]

theorem DthIter_two_Sfun : Work.Spaces.DthIter 2 Sfun
    = fun _ θ => Real.sin (2 * θ)
        * (4 * Real.cos (2 * θ) ^ 2 - 4 * Real.sin (2 * θ) ^ 2) := by
  funext z θ
  rw [show Work.Spaces.DthIter 2 Sfun
      = Work.Spaces.Dth (Work.Spaces.DthIter 1 Sfun) from rfl, DthIter_one_Sfun]
  show Real.sin (2 * θ)
      * deriv (fun θ' : ℝ => Real.sin (2 * θ') * (2 * Real.cos (2 * θ'))) θ = _
  have hfun : (fun θ' : ℝ => Real.sin (2 * θ') * (2 * Real.cos (2 * θ')))
      = (fun θ' : ℝ => Real.sin (2 * θ')) * (fun θ' : ℝ => 2 * Real.cos (2 * θ')) := rfl
  rw [hfun, ((hasDerivAt_sin_two θ).mul (hasDerivAt_two_cos_two θ)).deriv]
  ring

theorem DthIter_three_Sfun : Work.Spaces.DthIter 3 Sfun
    = fun _ θ => Real.sin (2 * θ)
        * (8 * Real.cos (2 * θ) ^ 3 - 40 * Real.cos (2 * θ) * Real.sin (2 * θ) ^ 2) := by
  funext z θ
  rw [show Work.Spaces.DthIter 3 Sfun
      = Work.Spaces.Dth (Work.Spaces.DthIter 2 Sfun) from rfl, DthIter_two_Sfun]
  show Real.sin (2 * θ) * deriv (fun θ' : ℝ => Real.sin (2 * θ')
      * (4 * Real.cos (2 * θ') ^ 2 - 4 * Real.sin (2 * θ') ^ 2)) θ = _
  have hq : HasDerivAt (fun θ' : ℝ => 4 * Real.cos (2 * θ') ^ 2 - 4 * Real.sin (2 * θ') ^ 2)
      (-(32 * Real.cos (2 * θ) * Real.sin (2 * θ))) θ := by
    have h := (((hasDerivAt_cos_two θ).pow 2).const_mul 4).sub
      (((hasDerivAt_sin_two θ).pow 2).const_mul 4)
    convert h using 1 <;> ring
  have hfun : (fun θ' : ℝ => Real.sin (2 * θ')
        * (4 * Real.cos (2 * θ') ^ 2 - 4 * Real.sin (2 * θ') ^ 2))
      = (fun θ' : ℝ => Real.sin (2 * θ'))
        * (fun θ' : ℝ => 4 * Real.cos (2 * θ') ^ 2 - 4 * Real.sin (2 * θ') ^ 2) := rfl
  rw [hfun, ((hasDerivAt_sin_two θ).mul hq).deriv]
  ring

theorem DthIter_four_Sfun : Work.Spaces.DthIter 4 Sfun
    = fun _ θ => Real.sin (2 * θ)
        * (16 * Real.cos (2 * θ) ^ 4 - 288 * Real.cos (2 * θ) ^ 2 * Real.sin (2 * θ) ^ 2
          + 80 * Real.sin (2 * θ) ^ 4) := by
  funext z θ
  rw [show Work.Spaces.DthIter 4 Sfun
      = Work.Spaces.Dth (Work.Spaces.DthIter 3 Sfun) from rfl, DthIter_three_Sfun]
  have hQ : (fun θ' : ℝ => Real.sin (2 * θ')
        * (8 * Real.cos (2 * θ') ^ 3 - 40 * Real.cos (2 * θ') * Real.sin (2 * θ') ^ 2))
      = (fun θ' : ℝ => Real.sin (2 * θ')
        * (8 * Real.cos (2 * θ') ^ 3
          - 40 * (Real.cos (2 * θ') * Real.sin (2 * θ') ^ 2))) := by
    funext θ'; ring
  rw [hQ]
  show Real.sin (2 * θ) * deriv (fun θ' : ℝ => Real.sin (2 * θ')
      * (8 * Real.cos (2 * θ') ^ 3
        - 40 * (Real.cos (2 * θ') * Real.sin (2 * θ') ^ 2))) θ = _
  have h1 : HasDerivAt (fun θ' : ℝ => 8 * Real.cos (2 * θ') ^ 3)
      (-48 * Real.cos (2 * θ) ^ 2 * Real.sin (2 * θ)) θ := by
    convert ((hasDerivAt_cos_two θ).pow 3).const_mul (8 : ℝ) using 1
    ring
  have h2 : HasDerivAt (fun θ' : ℝ => 40 * (Real.cos (2 * θ') * Real.sin (2 * θ') ^ 2))
      (-80 * Real.sin (2 * θ) ^ 3 + 160 * Real.cos (2 * θ) ^ 2 * Real.sin (2 * θ)) θ := by
    convert ((hasDerivAt_cos_two θ).mul ((hasDerivAt_sin_two θ).pow 2)).const_mul (40 : ℝ)
      using 1
    simp only [Pi.pow_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hq : HasDerivAt (fun θ' : ℝ => 8 * Real.cos (2 * θ') ^ 3
      - 40 * (Real.cos (2 * θ') * Real.sin (2 * θ') ^ 2))
      (80 * Real.sin (2 * θ) ^ 3 - 208 * Real.cos (2 * θ) ^ 2 * Real.sin (2 * θ)) θ := by
    convert h1.sub h2 using 1
    ring
  have hfun : (fun θ' : ℝ => Real.sin (2 * θ')
        * (8 * Real.cos (2 * θ') ^ 3
          - 40 * (Real.cos (2 * θ') * Real.sin (2 * θ') ^ 2)))
      = (fun θ' : ℝ => Real.sin (2 * θ'))
        * (fun θ' : ℝ => 8 * Real.cos (2 * θ') ^ 3
            - 40 * (Real.cos (2 * θ') * Real.sin (2 * θ') ^ 2)) := rfl
  rw [hfun, ((hasDerivAt_sin_two θ).mul hq).deriv]
  ring

theorem abs_DthIter_Sfun_le (r : ℕ) (hr : r ≤ 4) (z : ℝ) {θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Spaces.DthIter r Sfun z θ| ≤ Asin r * Real.sin (2 * θ) := by
  have hs : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_Iθ hθ
  have hcos : |Real.cos (2 * θ)| ≤ 1 := Real.abs_cos_le_one (2 * θ)
  have hsin1 : |Real.sin (2 * θ)| ≤ 1 := Real.abs_sin_le_one (2 * θ)
  have hsc : Real.cos (2 * θ) ^ 2 + Real.sin (2 * θ) ^ 2 = 1 := by
    linarith [Real.sin_sq_add_cos_sq (2 * θ)]
  interval_cases r
  · have h0 : Work.Spaces.DthIter 0 Sfun z θ = Real.sin (2 * θ) := rfl
    rw [h0, abs_of_nonneg hs]
    have hA : Asin 0 = 1 := by norm_num [Asin]
    rw [hA]; linarith
  · rw [DthIter_one_Sfun, abs_mul, abs_of_nonneg hs]
    have h2 : |2 * Real.cos (2 * θ)| ≤ 2 := by
      rw [abs_mul, show |(2:ℝ)| = 2 by norm_num]; linarith
    have hA : Asin 1 = 2 := by norm_num [Asin]
    rw [hA]; nlinarith [hs, h2]
  · rw [DthIter_two_Sfun, abs_mul, abs_of_nonneg hs]
    have h2 : |4 * Real.cos (2 * θ) ^ 2 - 4 * Real.sin (2 * θ) ^ 2| ≤ 4 := by
      have h1 : 4 * Real.cos (2 * θ) ^ 2 - 4 * Real.sin (2 * θ) ^ 2
          = 4 * (Real.cos (2 * θ) ^ 2 - Real.sin (2 * θ) ^ 2) := by ring
      rw [h1, abs_mul, show |(4:ℝ)| = 4 by norm_num]
      have h3 : |Real.cos (2 * θ) ^ 2 - Real.sin (2 * θ) ^ 2| ≤ 1 := by
        refine abs_le.mpr ⟨?_, ?_⟩ <;> nlinarith [sq_nonneg (Real.sin (2 * θ)), hsc]
      linarith
    have hA : Asin 2 = 4 := by norm_num [Asin]
    rw [hA]; nlinarith [hs, h2]
  · rw [DthIter_three_Sfun, abs_mul, abs_of_nonneg hs]
    have h2 : |8 * Real.cos (2 * θ) ^ 3 - 40 * Real.cos (2 * θ) * Real.sin (2 * θ) ^ 2|
        ≤ 48 := by
      have h1 : 8 * Real.cos (2 * θ) ^ 3 - 40 * Real.cos (2 * θ) * Real.sin (2 * θ) ^ 2
          = 8 * (Real.cos (2 * θ) ^ 3 - 5 * (Real.cos (2 * θ) * Real.sin (2 * θ) ^ 2)) := by
        ring
      rw [h1, abs_mul, show |(8:ℝ)| = 8 by norm_num]
      have h4 : |Real.cos (2 * θ) ^ 3| ≤ 1 := by
        rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) hcos
      have h5 : |Real.cos (2 * θ) * Real.sin (2 * θ) ^ 2| ≤ 1 := by
        rw [abs_mul, abs_pow]
        have hs1 : |Real.sin (2 * θ)| ^ 2 ≤ 1 :=
          pow_le_one₀ (abs_nonneg _) hsin1
        calc |Real.cos (2 * θ)| * |Real.sin (2 * θ)| ^ 2 ≤ 1 * 1 :=
              mul_le_mul hcos hs1 (by positivity) (by norm_num)
          _ = 1 := by norm_num
      have h6 : |Real.cos (2 * θ) ^ 3 - 5 * (Real.cos (2 * θ) * Real.sin (2 * θ) ^ 2)| ≤ 6 := by
        calc |Real.cos (2 * θ) ^ 3 - 5 * (Real.cos (2 * θ) * Real.sin (2 * θ) ^ 2)|
            ≤ |Real.cos (2 * θ) ^ 3|
              + |5 * (Real.cos (2 * θ) * Real.sin (2 * θ) ^ 2)| := abs_sub_le_abs_add _ _
          _ ≤ 1 + 5 := by
              refine add_le_add h4 ?_
              rw [abs_mul, show |(5:ℝ)| = 5 by norm_num]; linarith
          _ = 6 := by norm_num
      linarith
    have hA : Asin 3 = 48 := by norm_num [Asin]
    rw [hA]; nlinarith [hs, h2]
  · rw [DthIter_four_Sfun, abs_mul, abs_of_nonneg hs, Asin]
    have h4c : |Real.cos (2 * θ) ^ 4| ≤ 1 := by
      rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) hcos
    have hs4 : |Real.sin (2 * θ) ^ 4| ≤ 1 := by
      rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) hsin1
    have hcs : |Real.cos (2 * θ) ^ 2 * Real.sin (2 * θ) ^ 2| ≤ 1 := by
      rw [abs_mul, abs_pow, abs_pow]
      exact mul_le_one₀ (pow_le_one₀ (abs_nonneg _) hcos)
        (pow_nonneg (abs_nonneg _) 2) (pow_le_one₀ (abs_nonneg _) hsin1)
    have h2 : |16 * Real.cos (2 * θ) ^ 4 - 288 * Real.cos (2 * θ) ^ 2 * Real.sin (2 * θ) ^ 2
        + 80 * Real.sin (2 * θ) ^ 4| ≤ 384 := by
      have e1 : |(16:ℝ) * Real.cos (2 * θ) ^ 4| ≤ 16 := by
        rw [abs_mul, show |(16:ℝ)| = 16 by norm_num]; nlinarith [h4c]
      have e2 : |(288:ℝ) * Real.cos (2 * θ) ^ 2 * Real.sin (2 * θ) ^ 2| ≤ 288 := by
        rw [show (288:ℝ) * Real.cos (2 * θ) ^ 2 * Real.sin (2 * θ) ^ 2
            = 288 * (Real.cos (2 * θ) ^ 2 * Real.sin (2 * θ) ^ 2) from by ring, abs_mul,
          show |(288:ℝ)| = 288 by norm_num]
        nlinarith [hcs]
      have e3 : |(80:ℝ) * Real.sin (2 * θ) ^ 4| ≤ 80 := by
        rw [abs_mul, show |(80:ℝ)| = 80 by norm_num]; nlinarith [hs4]
      have e4 := abs_sub_le_abs_add ((16:ℝ) * Real.cos (2 * θ) ^ 4)
        ((288:ℝ) * Real.cos (2 * θ) ^ 2 * Real.sin (2 * θ) ^ 2)
      have e5 := abs_add_le ((16:ℝ) * Real.cos (2 * θ) ^ 4
          - (288:ℝ) * Real.cos (2 * θ) ^ 2 * Real.sin (2 * θ) ^ 2)
        ((80:ℝ) * Real.sin (2 * θ) ^ 4)
      linarith
    nlinarith [hs, h2]


/-! ## The local Leibniz bound for `D_θ^i` on the open interval -/

/-- Leibniz for `D_θ^i` on the open interval `(0,π/2)`, with only the interior smoothness
hypotheses: this is the part of `Work.Spaces.DthIter_mul_le` that is actually used, and it
applies to `SmoothInt` multipliers. -/
theorem dthIter_mul_le_open (i : ℕ) (f g : ℝ → ℝ → ℝ) {z θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (π / 2))
    (hf : ContDiffOn ℝ ⊤ (fun θ' => f z θ') (Set.Ioo 0 (π / 2)))
    (hg : ContDiffOn ℝ ⊤ (fun θ' => g z θ') (Set.Ioo 0 (π / 2))) :
    |Work.Spaces.DthIter i (fun z θ => f z θ * g z θ) z θ|
      ≤ (1 + ∑ a ∈ Finset.range (i + 1), (i.choose a : ℝ))
        * ∑ a ∈ Finset.range (i + 1),
            |Work.Spaces.DthIter a f z θ| * |Work.Spaces.DthIter (i - a) g z θ| := by
  set S : ℝ := ∑ a ∈ Finset.range (i + 1), (i.choose a : ℝ) with hSdef
  have hSnn : 0 ≤ S := by
    rw [hSdef]
    exact Finset.sum_nonneg (fun a _ => Nat.cast_nonneg (i.choose a))
  have hCpos : 0 < 1 + S := by linarith
  rw [Work.Spaces.DthIter_mul i f g z (Set.Ioo 0 (π / 2)) isOpen_Ioo hf hg θ hθ]
  have hc0 : ∀ a ∈ Finset.range (i + 1), (0 : ℝ) ≤ (i.choose a : ℝ) :=
    fun a _ => Nat.cast_nonneg (i.choose a)
  have hcS : ∀ a ∈ Finset.range (i + 1), (i.choose a : ℝ) ≤ 1 + S := by
    intro a ha
    have h1 : (i.choose a : ℝ) ≤ S := by
      rw [hSdef]
      exact Finset.single_le_sum (fun b _ => Nat.cast_nonneg (i.choose b)) ha
    linarith
  have hTnn : 0 ≤ ∑ a ∈ Finset.range (i + 1),
      |Work.Spaces.DthIter a f z θ| * |Work.Spaces.DthIter (i - a) g z θ| :=
    Finset.sum_nonneg fun a _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)
  calc |∑ a ∈ Finset.range (i + 1),
          (i.choose a : ℝ) * (Work.Spaces.DthIter a f z θ * Work.Spaces.DthIter (i - a) g z θ)|
      ≤ ∑ a ∈ Finset.range (i + 1),
          |(i.choose a : ℝ) * (Work.Spaces.DthIter a f z θ * Work.Spaces.DthIter (i - a) g z θ)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ a ∈ Finset.range (i + 1),
          (i.choose a : ℝ) * (|Work.Spaces.DthIter a f z θ| * |Work.Spaces.DthIter (i - a) g z θ|) := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [abs_mul, abs_of_nonneg (hc0 a ha), abs_mul]
    _ ≤ ∑ a ∈ Finset.range (i + 1),
          (1 + S) * (|Work.Spaces.DthIter a f z θ| * |Work.Spaces.DthIter (i - a) g z θ|) := by
        apply Finset.sum_le_sum
        intro a ha
        exact mul_le_mul_of_nonneg_right (hcS a ha)
          (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    _ = (1 + S) * ∑ a ∈ Finset.range (i + 1),
          |Work.Spaces.DthIter a f z θ| * |Work.Spaces.DthIter (i - a) g z θ| := by
        rw [Finset.mul_sum]

/-! ## A `z`-independent factor passes through `∂_z^j` -/

theorem pzIter_const_mul (c : ℝ → ℝ) (K : ℝ → ℝ → ℝ) (j : ℕ) (z θ : ℝ) :
    Work.Spaces.pzIter j (fun z θ => c θ * K z θ) z θ = c θ * Work.Spaces.pzIter j K z θ := by
  induction j generalizing z θ with
  | zero => rfl
  | succ j ih =>
    rw [Work.Spaces.pzIter_succ, Work.Spaces.pzIter_succ]
    have heq : Work.Spaces.pzIter j (fun z θ => c θ * K z θ)
        = fun z θ => c θ * Work.Spaces.pzIter j K z θ :=
      funext fun z => funext fun θ => ih z θ
    rw [heq, pz_const_mul]

theorem pzIter_Dth_eq (f : ℝ → ℝ → ℝ) (j : ℕ) (z θ : ℝ) :
    Work.Spaces.pzIter j (Work.Spaces.Dth f) z θ
      = Real.sin (2 * θ) * Work.Spaces.pzIter j (Work.Spaces.pth f) z θ :=
  pzIter_const_mul (fun θ => Real.sin (2 * θ)) (Work.Spaces.pth f) j z θ

/-- Multiplication by `sin(2θ)` converts `D_z^c (∂_θ g)` into `D_z^c D_θ g`. -/
theorem sin_mul_dzIter_pth (g : ℝ → ℝ → ℝ) (c : ℕ) (z θ : ℝ) :
    Real.sin (2 * θ) * Work.Spaces.DzIter c (Work.Spaces.pth g) z θ
      = Work.Spaces.mixed c 1 g z θ := by
  have h1 : Work.Spaces.mixed c 1 g = Work.Spaces.DzIter c (Work.Spaces.Dth g) := by
    simp only [Work.Spaces.mixed, Work.Spaces.DthIter_succ, Work.Spaces.DthIter_zero]
  rw [h1]
  exact (DzIter_const_mul_apply (fun θ => Real.sin (2 * θ)) (Work.Spaces.pth g) c z θ).symm

/-! ## Congruence and smoothness of the `D_θ`-iterates -/

theorem DthIter_congr_of_isOpen {u v : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : Set.EqOn (Function.uncurry u) (Function.uncurry v) V) (c : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.DthIter c u))
      (Function.uncurry (Work.Spaces.DthIter c v)) V := by
  induction c with
  | zero => exact h
  | succ c ih =>
    intro y hy
    show Real.sin (2 * y.2) * Work.Spaces.pth (Work.Spaces.DthIter c u) y.1 y.2
      = Real.sin (2 * y.2) * Work.Spaces.pth (Work.Spaces.DthIter c v) y.1 y.2
    rw [Work.Spaces.pth_congr_of_isOpen hV ih hy]

theorem contDiffOn_uncurry_Dth {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : ContDiffOn ℝ ⊤ (Function.uncurry G) V) :
    ContDiffOn ℝ ⊤ (Function.uncurry (Work.Spaces.Dth G)) V := by
  have hfd : ContDiffOn ℝ ⊤ (fderiv ℝ (Function.uncurry G)) V :=
    ContDiffOn.fderiv_of_isOpen h hV (by simp)
  have hev : ContDiffOn ℝ ⊤ (fun y : ℝ × ℝ => (fderiv ℝ (Function.uncurry G) y) (0,1)) V :=
    hfd.clm_apply contDiffOn_const
  have hsin : ContDiffOn ℝ ⊤ (fun y : ℝ × ℝ => Real.sin (2 * y.2)) V :=
    (Real.contDiff_sin.comp (contDiff_const.mul contDiff_snd)).contDiffOn
  have hfun : ContDiffOn ℝ ⊤ (fun y : ℝ × ℝ =>
      Real.sin (2 * y.2) * (fderiv ℝ (Function.uncurry G) y) (0,1)) V := hsin.mul hev
  refine hfun.congr (fun y hy => ?_)
  have hdiff : DifferentiableAt ℝ (Function.uncurry G) y :=
    (ContDiffOn.contDiffAt h (hV.mem_nhds hy)).differentiableAt (by norm_num)
  have hderiv : deriv (fun θ' => Function.uncurry G (y.1, θ')) y.2
      = (fderiv ℝ (Function.uncurry G) y) (0,1) := Work.Spaces.deriv_slice_snd _ _ _ hdiff
  show Real.sin (2 * y.2) * deriv (fun θ' => Function.uncurry G (y.1, θ')) y.2
      = Real.sin (2 * y.2) * (fderiv ℝ (Function.uncurry G) y) (0,1)
  rw [hderiv]

theorem contDiffOn_uncurry_DthIter {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : ContDiffOn ℝ ⊤ (Function.uncurry G) V) (c : ℕ) :
    ContDiffOn ℝ ⊤ (Function.uncurry (Work.Spaces.DthIter c G)) V := by
  induction c with
  | zero => simpa using h
  | succ c ih => simpa [Work.Spaces.DthIter_succ] using contDiffOn_uncurry_Dth hV ih

theorem contDiffOn_zslice_of_uncurry {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : ContDiffOn ℝ ⊤ (Function.uncurry G) V) {θ : ℝ} {W : Set ℝ} (hW : IsOpen W)
    (hθ : ∀ z ∈ W, (z, θ) ∈ V) :
    ContDiffOn ℝ ⊤ (fun z => G z θ) W := by
  have hp : ContDiffOn ℝ ⊤ (fun z : ℝ => (z, θ)) W := by fun_prop
  have h2 := h.comp hp hθ
  simpa [Function.comp_def, Function.uncurry] using h2

/-- The `z`-slices of `D_θ f` are smooth down to `z = -1`, for `SmoothInt f`. -/
theorem contDiffOn_zslice_Dth {f : ℝ → ℝ → ℝ} (hsm : Work.Spaces.SmoothInt f) :
    ∀ θ ∈ Work.Spaces.Iθ,
      ContDiffOn ℝ ⊤ (fun z => Work.Spaces.Dth f z θ) (Set.Ioi (-1)) := by
  intro θ hθ
  by_cases hθi : θ ∈ Set.Ioo 0 (π / 2)
  · have hjoint : ContDiffOn ℝ ⊤ (Function.uncurry (Work.Spaces.Dth f)) strp :=
      contDiffOn_uncurry_Dth isOpen_strp hsm.1
    exact contDiffOn_zslice_of_uncurry isOpen_strp hjoint isOpen_Ioi
      (fun z hz => ⟨hz, hθi⟩)
  · have hsin : Real.sin (2 * θ) = 0 :=
      Work.Spaces.sin_two_mul_eq_zero_of_mem_Iθ_of_not_mem_Ioo hθ hθi
    have hzero : (fun z => Work.Spaces.Dth f z θ) = fun _ => (0 : ℝ) := by
      funext z; simp [Work.Spaces.Dth, hsin]
    rw [hzero]
    exact contDiffOn_const

/-- The `z`-slices of `D_θ^c (∂_θ f)` for `c ≥ 1` are smooth down to `z = -1`. -/
theorem contDiffOn_zslice_DthIter_pth {f : ℝ → ℝ → ℝ} (hsm : Work.Spaces.SmoothInt f)
    (c : ℕ) (hc : 1 ≤ c) :
    ∀ θ ∈ Work.Spaces.Iθ,
      ContDiffOn ℝ ⊤ (fun z => Work.Spaces.DthIter c (Work.Spaces.pth f) z θ) (Set.Ioi (-1)) := by
  intro θ hθ
  by_cases hθi : θ ∈ Set.Ioo 0 (π / 2)
  · have hjoint : ContDiffOn ℝ ⊤ (Function.uncurry (Work.Spaces.DthIter c (Work.Spaces.pth f)))
        strp :=
      contDiffOn_uncurry_DthIter isOpen_strp
        (Work.Spaces.contDiffOn_uncurry_pth isOpen_strp hsm.1) c
    exact contDiffOn_zslice_of_uncurry isOpen_strp hjoint isOpen_Ioi
      (fun z hz => ⟨hz, hθi⟩)
  · obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
    have hsin : Real.sin (2 * θ) = 0 :=
      Work.Spaces.sin_two_mul_eq_zero_of_mem_Iθ_of_not_mem_Ioo hθ hθi
    have hzero : (fun z => Work.Spaces.DthIter (c' + 1) (Work.Spaces.pth f) z θ)
        = fun _ => (0 : ℝ) :=
      funext fun z => Work.Spaces.DthIter_eq_zero_of_sin_eq_zero (Work.Spaces.pth f) c' hsin z
    rw [hzero]
    exact contDiffOn_const

/-! ## `D_z`-bounds from the pointwise bounds on `z^k ∂_z^k` -/

/-- If the functions `z^k ∂_z^k h` (`k ≤ b`) are bounded by `M θ` on `z > 0`, then so is
`D_z^b h`, by the Stirling expansion `D_z^b = ∑_k S(b,k) z^k ∂_z^k`. -/
theorem dzIter_le_of_pz_bound {h : ℝ → ℝ → ℝ}
    (hsmooth : ∀ θ ∈ Work.Spaces.Iθ,
      ContDiffOn ℝ ⊤ (fun z => h z θ) (Set.Ioi (-1)))
    {M : ℝ → ℝ} (hM : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ M θ)
    (b : ℕ) (hb4 : b ≤ 4)
    (hb : ∀ k ≤ b, ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Work.Spaces.Iθ,
      |z ^ k * Work.Spaces.pzIter k h z θ| ≤ M θ) :
    ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.DzIter b h z θ| ≤ 100 * M θ := by
  intro z hz θ hθ
  have hz0 : (0 : ℝ) < z := hz
  have hz' : z ∈ Set.Ioi (-1 : ℝ) := by
    show (-1 : ℝ) < z
    linarith
  rw [Work.Spaces.DzIter_eq_sum_scoef hsmooth b z hz' θ hθ]
  have hsum := Work.Spaces.abs_sum_scoef_mul_le b (M θ)
    (fun k => z ^ k * Work.Spaces.pzIter k h z θ)
    (fun k hk => hb k hk z hz θ hθ)
  have hbell : (Work.Spaces.bell b : ℝ) ≤ 100 := by
    exact_mod_cast Work.Spaces.bell_le b hb4
  calc |∑ k ∈ Finset.range (b + 1),
        (Work.Spaces.scoef b k : ℝ) * (z ^ k * Work.Spaces.pzIter k h z θ)|
      ≤ (Work.Spaces.bell b : ℝ) * M θ := hsum
    _ ≤ 100 * M θ := mul_le_mul_of_nonneg_right hbell (hM θ hθ)

/-! ## The pointwise bounds on the `f`-side -/

/-- `|D_z^b f| ≤ 10^4 sin(2θ) |∂_θ f|_𝒲` for `z > 0`. -/
theorem abs_DzIter_f_le {α : ℝ} {f : ℝ → ℝ → ℝ}
    (hsm : Work.Spaces.SmoothInt f)
    (hcont : ContinuousOn (Function.uncurry f) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ))
    (hvt : Work.Spaces.VanishTheta f) (hW : Work.Spaces.WlInfMem α 4 (Work.Spaces.pth f)) :
    ∀ b ≤ 4, ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.DzIter b f z θ|
        ≤ 10000 * Real.sin (2 * θ) * Work.Spaces.WlInf α 4 (Work.Spaces.pth f) := by
  intro b hb z hz θ hθ
  have h := dzIter_le_of_pz_bound (h := f) (M := fun θ => 100 * Real.sin (2 * θ)
      * Work.Spaces.WlInf α 4 (Work.Spaces.pth f))
    (fun θ hθ => hsm.2 θ hθ)
    (fun θ hθ => by
      have : 0 ≤ Work.Spaces.WlInf α 4 (Work.Spaces.pth f) := WlInf_nonneg hW
      exact mul_nonneg (mul_nonneg (by norm_num) (sin_two_nonneg_Iθ hθ)) this)
    b hb
    (fun k hk z hz θ hθ => z_pzIter_bound hsm hcont hvt hW k (le_trans hk hb) z hz θ hθ)
    z hz θ hθ
  calc |Work.Spaces.DzIter b f z θ|
      ≤ 100 * (100 * Real.sin (2 * θ) * Work.Spaces.WlInf α 4 (Work.Spaces.pth f)) := h
    _ = 10000 * Real.sin (2 * θ) * Work.Spaces.WlInf α 4 (Work.Spaces.pth f) := by ring

/-- `|D_z^b (D_θ f)| ≤ 100 sin(2θ) |∂_θ f|_𝒲` for `z > 0`, `θ ∈ Iθ`. -/
theorem abs_DzIter_Dth_le {α : ℝ} {f : ℝ → ℝ → ℝ}
    (hsm : Work.Spaces.SmoothInt f) (hα : 0 < α) (hα1 : α ≤ 1)
    (hW : Work.Spaces.WlInfMem α 4 (Work.Spaces.pth f)) :
    ∀ b ≤ 4, ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.DzIter b (Work.Spaces.Dth f) z θ|
        ≤ 100 * Real.sin (2 * θ) * Work.Spaces.WlInf α 4 (Work.Spaces.pth f) := by
  intro b hb z hz θ hθ
  have h := dzIter_le_of_pz_bound (h := Work.Spaces.Dth f)
      (M := fun θ => Real.sin (2 * θ) * Work.Spaces.WlInf α 4 (Work.Spaces.pth f))
    (contDiffOn_zslice_Dth hsm)
    (fun θ hθ => mul_nonneg (sin_two_nonneg_Iθ hθ) (WlInf_nonneg hW))
    b hb
    (fun k hk z hz θ hθ => by
      have hz0 : (0 : ℝ) < z := hz
      have hziz : z ∈ Work.Spaces.Iz := Set.mem_Ici.mpr hz.le
      have hS : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_Iθ hθ
      rw [pzIter_Dth_eq, abs_mul, abs_mul, abs_of_nonneg hS,
        abs_of_nonneg (pow_nonneg hz.le k)]
      have hWnn : 0 ≤ Work.Spaces.WlInf α 4 (Work.Spaces.pth f) := WlInf_nonneg hW
      have h2 : z ^ k * |Work.Spaces.pzIter k (Work.Spaces.pth f) z θ|
          ≤ Work.Spaces.WlInf α 4 (Work.Spaces.pth f) := by
        have h3 : (z + 1) ^ k * |Work.Spaces.pzIter k (Work.Spaces.pth f) z θ|
            ≤ Work.Spaces.WlInf α 4 (Work.Spaces.pth f) := by
          have hbnd := Work.Spaces.WlInf_z_bound α 4 (Work.Spaces.pth f) hW k
            (le_trans hk hb) z θ hziz hθ
          rwa [abs_mul, abs_of_nonneg (pow_nonneg (by linarith : (0:ℝ) ≤ z + 1) k)] at hbnd
        have hzk : z ^ k / (z + 1) ^ k ≤ 1 := by
          rw [div_le_one (pow_pos (by linarith : (0:ℝ) < z + 1) k)]
          exact pow_le_pow_left₀ hz.le (by linarith) k
        calc z ^ k * |Work.Spaces.pzIter k (Work.Spaces.pth f) z θ|
            = (z ^ k / (z + 1) ^ k)
                * ((z + 1) ^ k * |Work.Spaces.pzIter k (Work.Spaces.pth f) z θ|) := by
              field_simp
          _ ≤ 1 * Work.Spaces.WlInf α 4 (Work.Spaces.pth f) :=
              mul_le_mul hzk h3
                (mul_nonneg (pow_nonneg (by linarith : (0:ℝ) ≤ z + 1) k) (abs_nonneg _))
                (by norm_num)
          _ = Work.Spaces.WlInf α 4 (Work.Spaces.pth f) := one_mul _
      calc z ^ k * (Real.sin (2 * θ) * |Work.Spaces.pzIter k (Work.Spaces.pth f) z θ|)
          = Real.sin (2 * θ) * (z ^ k * |Work.Spaces.pzIter k (Work.Spaces.pth f) z θ|) := by ring
        _ ≤ Real.sin (2 * θ) * Work.Spaces.WlInf α 4 (Work.Spaces.pth f) :=
            mul_le_mul_of_nonneg_left h2 hS)
    z hz θ hθ
  calc |Work.Spaces.DzIter b (Work.Spaces.Dth f) z θ|
      ≤ 100 * (Real.sin (2 * θ) * Work.Spaces.WlInf α 4 (Work.Spaces.pth f)) := h
    _ = 100 * Real.sin (2 * θ) * Work.Spaces.WlInf α 4 (Work.Spaces.pth f) := by ring

/-- `|D_z^b (D_θ^c (∂_θ f))| ≤ 200 |∂_θ f|_𝒲` for `c ≥ 1`, `b + c ≤ 4`. -/
theorem abs_DzIter_DthIter_pth_le {α : ℝ} {f : ℝ → ℝ → ℝ}
    (hsm : Work.Spaces.SmoothInt f) (hα : 0 < α) (hα1 : α ≤ 1)
    (hW : Work.Spaces.WlInfMem α 4 (Work.Spaces.pth f)) :
    ∀ c : ℕ, 1 ≤ c → ∀ b : ℕ, b + c ≤ 4 → ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.DzIter b (Work.Spaces.DthIter c (Work.Spaces.pth f)) z θ|
        ≤ 200 * Work.Spaces.WlInf α 4 (Work.Spaces.pth f) := by
  intro c hc b hbc z hz θ hθ
  have h := dzIter_le_of_pz_bound (h := Work.Spaces.DthIter c (Work.Spaces.pth f))
      (M := fun _ => 2 * Work.Spaces.WlInf α 4 (Work.Spaces.pth f))
    (contDiffOn_zslice_DthIter_pth hsm c hc)
    (fun θ hθ => by have := WlInf_nonneg hW; linarith)
    b (by omega)
    (fun k hk z hz θ hθ => by
      have hz0 : (0 : ℝ) < z := hz
      have hziz : z ∈ Work.Spaces.Iz := Set.mem_Ici.mpr hz.le
      have h1 := Work.Spaces.pz_Dth_sup_bound α hα 4 (Work.Spaces.pth f) hW c k hc
        (by omega) z θ hziz hθ
      have hzk : z ^ k / (z + 1) ^ k ≤ 1 := by
        rw [div_le_one (pow_pos (by linarith : (0:ℝ) < z + 1) k)]
        exact pow_le_pow_left₀ hz.le (by linarith) k
      have hsin1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
      have hsin0 : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_Iθ hθ
      have hpow : (Real.sin (2 * θ)) ^ (α / 5) ≤ 1 :=
        Real.rpow_le_one hsin0 hsin1 (by linarith)
      have hWnn : 0 ≤ Work.Spaces.WlInf α 4 (Work.Spaces.pth f) := WlInf_nonneg hW
      have hfac : Work.Spaces.WlInf α 4 (Work.Spaces.pth f)
          * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) ≤ 2 * Work.Spaces.WlInf α 4 (Work.Spaces.pth f) := by
        have hA : (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) ≤ 2 := by
          have h1' : Real.sin (2 * θ) ^ (α / 5) ≤ 1 := hpow
          nlinarith [Real.rpow_nonneg hsin0 (α / 5)]
        nlinarith
      calc |z ^ k * Work.Spaces.pzIter k (Work.Spaces.DthIter c (Work.Spaces.pth f)) z θ|
          = z ^ k * |Work.Spaces.pzIter k (Work.Spaces.DthIter c (Work.Spaces.pth f)) z θ| := by
            rw [abs_mul, abs_of_nonneg (pow_nonneg hz.le k)]
        _ ≤ z ^ k * (Work.Spaces.WlInf α 4 (Work.Spaces.pth f) / (z + 1) ^ k
              * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))) :=
            mul_le_mul_of_nonneg_left h1 (pow_nonneg hz.le k)
        _ = (z ^ k / (z + 1) ^ k) * (Work.Spaces.WlInf α 4 (Work.Spaces.pth f)
              * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))) := by
            field_simp
        _ ≤ 1 * (2 * Work.Spaces.WlInf α 4 (Work.Spaces.pth f)) :=
            mul_le_mul hzk hfac (by positivity) (by norm_num)
        _ = 2 * Work.Spaces.WlInf α 4 (Work.Spaces.pth f) := one_mul _)
    z hz θ hθ
  calc |Work.Spaces.DzIter b (Work.Spaces.DthIter c (Work.Spaces.pth f)) z θ|
      ≤ 100 * (2 * Work.Spaces.WlInf α 4 (Work.Spaces.pth f)) := h
    _ = 200 * Work.Spaces.WlInf α 4 (Work.Spaces.pth f) := by ring

/-! ## The commutation of `D_z^b` with `D_θ^a` on an open set -/

theorem DzIter_DthIter_comm {g : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (hg : ContDiffOn ℝ ⊤ (Function.uncurry g) V) (b a : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.DzIter b (Work.Spaces.DthIter a g)))
      (Function.uncurry (Work.Spaces.DthIter a (Work.Spaces.DzIter b g))) V := by
  induction b with
  | zero => intro p hp; rfl
  | succ b ih =>
    intro p hp
    have hstep : Work.Spaces.Dz (Work.Spaces.DthIter a (Work.Spaces.DzIter b g)) p.1 p.2
        = Work.Spaces.DthIter a (Work.Spaces.Dz (Work.Spaces.DzIter b g)) p.1 p.2 :=
      Work.Spaces.DzDthIterCommOn hV (Work.Spaces.DzIterSmoothOn hV hg b) a hp
    have hpz : Work.Spaces.pz (Work.Spaces.DzIter b (Work.Spaces.DthIter a g)) p.1 p.2
        = Work.Spaces.pz (Work.Spaces.DthIter a (Work.Spaces.DzIter b g)) p.1 p.2 :=
      Work.Spaces.pz_congr_of_isOpen hV ih hp
    show p.1 * Work.Spaces.pz (Work.Spaces.DzIter b (Work.Spaces.DthIter a g)) p.1 p.2
        = Work.Spaces.DthIter a (Work.Spaces.Dz (Work.Spaces.DzIter b g)) p.1 p.2
    rw [hpz]
    show Work.Spaces.Dz (Work.Spaces.DthIter a (Work.Spaces.DzIter b g)) p.1 p.2
        = Work.Spaces.DthIter a (Work.Spaces.Dz (Work.Spaces.DzIter b g)) p.1 p.2
    exact hstep


/-! ## The angular commutator bound -/


/-! ## A `θ`-slice version of the slicing lemma -/

theorem contDiffOn_thslice_of_uncurry {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : ContDiffOn ℝ ⊤ (Function.uncurry G) V) {z : ℝ} {W : Set ℝ} (hW : IsOpen W)
    (hz : ∀ θ' ∈ W, (z, θ') ∈ V) :
    ContDiffOn ℝ ⊤ (fun θ' => G z θ') W := by
  have hp : ContDiffOn ℝ ⊤ (fun θ' : ℝ => (z, θ')) W := by fun_prop
  have h2 := h.comp hp hz
  simpa [Function.comp_def, Function.uncurry] using h2

theorem Asin_le (r : ℕ) (hr : r ≤ 3) : Asin r ≤ 48 := by
  interval_cases r <;> norm_num [Asin]

/-- `sin(2θ)·D_θ^c(∂_θ g)` is a bounded combination of `D_θ^m g`, `1 ≤ m ≤ c+1`. -/
theorem STSigmaBound : ∃ B : ℝ, 0 < B ∧ ∀ (g : ℝ → ℝ → ℝ), Work.Spaces.SmoothNbhd g →
    ∀ c : ℕ, c ≤ 3 → ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Set.Ioo 0 (π / 2),
      |Real.sin (2 * θ) * Work.Spaces.DthIter c (Work.Spaces.pth g) z θ|
        ≤ B * ∑ m ∈ Finset.Icc 1 (c + 1), |Work.Spaces.DthIter m g z θ| := by
  refine ⟨1500, by norm_num, ?_⟩
  intro g hg c hc z hz θ hθ
  have hθIθ : θ ∈ Work.Spaces.Iθ := ⟨hθ.1.le, hθ.2.le⟩
  have hy : (z, θ) ∈ Work.Spaces.nbhU := Work.Spaces.mem_nbhU hz hθIθ
  rw [Work.Elliptic.WtoW_g_ident c g hg z θ hy]
  set T : ℝ := ∑ m ∈ Finset.Icc 1 (c + 1), |Work.Spaces.DthIter m g z θ| with hT
  have hTnn : 0 ≤ T := Finset.sum_nonneg fun m _ => abs_nonneg _
  have h1 : |∑ i ∈ Finset.range (c + 1),
      Work.Elliptic.WtoW_ccoeff c i θ * Work.Spaces.DthIter (i + 1) g z θ|
      ≤ ∑ i ∈ Finset.range (c + 1),
        (375 : ℝ) * |Work.Spaces.DthIter (i + 1) g z θ| := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine Finset.sum_le_sum fun i hi => ?_
    rw [abs_mul]
    refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
    have hb := Work.Elliptic.WtoW_g_coeff_bound c i θ
    have h5 : (5 : ℝ) ^ c ≤ 125 := by
      calc (5 : ℝ) ^ c ≤ (5 : ℝ) ^ 3 := pow_le_pow_right₀ (by norm_num) hc
        _ = 125 := by norm_num
    linarith
  have h2 : ∀ i ∈ Finset.range (c + 1), |Work.Spaces.DthIter (i + 1) g z θ| ≤ T := by
    intro i hi
    have hi1 : i < c + 1 := Finset.mem_range.mp hi
    have hi' : i + 1 ∈ Finset.Icc 1 (c + 1) := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    exact Finset.single_le_sum (f := fun m => |Work.Spaces.DthIter m g z θ|)
      (fun m _ => abs_nonneg _) hi'
  calc |∑ i ∈ Finset.range (c + 1),
        Work.Elliptic.WtoW_ccoeff c i θ * Work.Spaces.DthIter (i + 1) g z θ|
      ≤ ∑ i ∈ Finset.range (c + 1), (375 : ℝ) * |Work.Spaces.DthIter (i + 1) g z θ| := h1
    _ ≤ ∑ _i ∈ Finset.range (c + 1), (375 : ℝ) * T :=
        Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (h2 i hi) (by norm_num)
    _ = ((c + 1 : ℕ) : ℝ) * (375 * T) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ 4 * (375 * T) := by
        refine mul_le_mul_of_nonneg_right ?_ (by linarith [hTnn])
        have h4 : (c + 1 : ℕ) ≤ 4 := by omega
        exact_mod_cast h4
    _ = 1500 * T := by ring

/-! ## The mixed `f`-derivative bound -/

/-- `|D_z^b ∂_θ f| ≤ 100 |∂_θ f|_𝒲` for `z > 0`, `θ ∈ Ioo`: the identity
`sin(2θ)·D_z^b(∂_θ f) = D_z^b D_θ f` together with the bound for `D_z^b D_θ f`. -/
theorem abs_Dz_iter_pth_le {α : ℝ} {f : ℝ → ℝ → ℝ}
    (hsm : Work.Spaces.SmoothInt f) (hα : 0 < α) (hα1 : α ≤ 1)
    (hW : Work.Spaces.WlInfMem α 4 (Work.Spaces.pth f)) :
    ∀ b ≤ 4, ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo 0 (π / 2),
      |Work.Spaces.DzIter b (Work.Spaces.pth f) z θ|
        ≤ 100 * Work.Spaces.WlInf α 4 (Work.Spaces.pth f) := by
  intro b hb z hz θ hθ
  have hθIθ : θ ∈ Work.Spaces.Iθ := ⟨hθ.1.le, hθ.2.le⟩
  have hS : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_Iθ hθIθ
  have hSpos : 0 < Real.sin (2 * θ) := sin_two_pos_of_Ioo hθ
  have hident : Real.sin (2 * θ) * Work.Spaces.DzIter b (Work.Spaces.pth f) z θ
      = Work.Spaces.DzIter b (Work.Spaces.Dth f) z θ := by
    rw [← DzIter_const_mul_apply (fun θ => Real.sin (2 * θ)) (Work.Spaces.pth f) b z θ]
    rfl
  have h2 := abs_DzIter_Dth_le hsm hα hα1 hW b hb z hz θ hθIθ
  have h3 : Real.sin (2 * θ) * |Work.Spaces.DzIter b (Work.Spaces.pth f) z θ|
      = |Work.Spaces.DzIter b (Work.Spaces.Dth f) z θ| := by
    rw [← hident, abs_mul, abs_of_nonneg hS]
  exact le_of_mul_le_mul_left (by
    calc Real.sin (2 * θ) * |Work.Spaces.DzIter b (Work.Spaces.pth f) z θ|
        = |Work.Spaces.DzIter b (Work.Spaces.Dth f) z θ| := h3
      _ ≤ 100 * Real.sin (2 * θ) * Work.Spaces.WlInf α 4 (Work.Spaces.pth f) := h2
      _ = Real.sin (2 * θ) * (100 * Work.Spaces.WlInf α 4 (Work.Spaces.pth f)) := by ring) hSpos

/-- **The mixed derivative bound.**  For `a ≥ 1` and `a + b ≤ 4`, the mixed derivative
`D_z^b D_θ^a f` is bounded by `C sin(2θ) |∂_θ f|_{𝒲^{4,∞}}`. -/
theorem abs_mixed_f_le {α : ℝ} {f : ℝ → ℝ → ℝ}
    (hsm : Work.Spaces.SmoothInt f) (hα : 0 < α) (hα1 : α ≤ 1)
    (hW : Work.Spaces.WlInfMem α 4 (Work.Spaces.pth f)) :
    ∀ a b : ℕ, 1 ≤ a → a + b ≤ 4 → ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo 0 (π / 2),
      |Work.Spaces.mixed b a f z θ|
        ≤ 400000 * Real.sin (2 * θ) * Work.Spaces.WlInf α 4 (Work.Spaces.pth f) := by
  intro a b ha hab z hz θ hθ
  have hz0 : (0 : ℝ) < z := hz
  have hzIoi : z ∈ Set.Ioi (-1 : ℝ) := by show (-1 : ℝ) < z; linarith
  have hθIθ : θ ∈ Work.Spaces.Iθ := ⟨hθ.1.le, hθ.2.le⟩
  have hstrp : (z, θ) ∈ strp := ⟨hzIoi, hθ⟩
  have hS : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_Iθ hθIθ
  set W := Work.Spaces.WlInf α 4 (Work.Spaces.pth f) with hWdef
  have hWnn : 0 ≤ W := WlInf_nonneg hW
  set G : ℝ → ℝ → ℝ := Work.Spaces.DzIter b (Work.Spaces.pth f) with hGdef
  have hSF : ContDiffOn ℝ ⊤ (Function.uncurry (fun z θ => Sfun z θ * Work.Spaces.pth f z θ))
      strp := by
    have : ((fun z θ => Sfun z θ * Work.Spaces.pth f z θ) : ℝ → ℝ → ℝ) = Work.Spaces.Dth f := rfl
    rw [this]
    exact contDiffOn_uncurry_Dth isOpen_strp hsm.1
  have hGsm : ContDiffOn ℝ ⊤ (Function.uncurry G) strp := by
    rw [hGdef]
    exact Work.Spaces.DzIterSmoothOn isOpen_strp
      (Work.Spaces.contDiffOn_uncurry_pth isOpen_strp hsm.1) b
  have hconst : Work.Spaces.DzIter b (fun z θ => Sfun z θ * Work.Spaces.pth f z θ)
      = fun z θ => Sfun z θ * G z θ := by
    funext z θ
    show Work.Spaces.DzIter b (fun z θ => Real.sin (2 * θ) * Work.Spaces.pth f z θ) z θ
        = Real.sin (2 * θ) * G z θ
    rw [DzIter_const_mul_apply (fun θ => Real.sin (2 * θ)) (Work.Spaces.pth f) b z θ, hGdef]
  have hshift : Work.Spaces.DthIter a f
      = Work.Spaces.DthIter (a - 1) (fun z θ => Sfun z θ * Work.Spaces.pth f z θ) := by
    have h := Work.Spaces.DthIter_add_right (a - 1) 1 f
    rw [show a - 1 + 1 = a from Nat.succ_pred_eq_of_pos (by omega : 0 < a),
      show Work.Spaces.DthIter 1 f = Work.Spaces.Dth f from rfl] at h
    exact h.symm
  have key : Work.Spaces.mixed b a f z θ
      = Work.Spaces.DthIter (a - 1) (fun z θ => Sfun z θ * G z θ) z θ := by
    rw [show Work.Spaces.mixed b a f = Work.Spaces.DzIter b (Work.Spaces.DthIter a f) from rfl,
      hshift]
    have hc : Work.Spaces.DzIter b (Work.Spaces.DthIter (a - 1)
          (fun z θ => Sfun z θ * Work.Spaces.pth f z θ)) z θ
        = Work.Spaces.DthIter (a - 1)
          (Work.Spaces.DzIter b (fun z θ => Sfun z θ * Work.Spaces.pth f z θ)) z θ :=
      DzIter_DthIter_comm (g := fun z θ => Sfun z θ * Work.Spaces.pth f z θ) isOpen_strp hSF
        b (a - 1) hstrp
    rw [hc, hconst]
  rw [key]
  have hSsm : ContDiffOn ℝ ⊤ (fun θ' => Sfun z θ') (Set.Ioo 0 (π / 2)) := by
    show ContDiffOn ℝ ⊤ (fun θ' => Real.sin (2 * θ')) _
    fun_prop
  have hGsl : ContDiffOn ℝ ⊤ (fun θ' => G z θ') (Set.Ioo 0 (π / 2)) :=
    contDiffOn_thslice_of_uncurry isOpen_strp hGsm isOpen_Ioo
      (fun θ' hθ' => ⟨hzIoi, hθ'⟩)
  have hml := dthIter_mul_le_open (a - 1) Sfun G hθ hSsm hGsl
  refine le_trans hml ?_
  have hcoef : (1 + ∑ r ∈ Finset.range ((a - 1) + 1), ((a - 1).choose r : ℝ)) ≤ 9 := by
    have hsplit : (∑ r ∈ Finset.range ((a - 1) + 1), ((a - 1).choose r : ℝ))
        = (2 : ℝ) ^ (a - 1) := by
      rw [← Nat.cast_sum, Nat.sum_range_choose, Nat.cast_pow]; norm_num
    have h8 : (2 : ℝ) ^ (a - 1) ≤ 8 := by
      calc (2 : ℝ) ^ (a - 1) ≤ (2 : ℝ) ^ 3 := pow_le_pow_right₀ (by norm_num) (by omega)
        _ = 8 := by norm_num
    linarith
  have hterm : ∀ r ∈ Finset.range ((a - 1) + 1),
      |Work.Spaces.DthIter r Sfun z θ| * |Work.Spaces.DthIter (a - 1 - r) G z θ|
        ≤ 48 * (200 * W) * Real.sin (2 * θ) := by
    intro r hr
    have hrlt : r < (a - 1) + 1 := Finset.mem_range.mp hr
    have hr4 : r ≤ 3 := by omega
    have h1 : |Work.Spaces.DthIter r Sfun z θ| ≤ Asin r * Real.sin (2 * θ) :=
      abs_DthIter_Sfun_le r (by omega) z hθIθ
    have h2 : |Work.Spaces.DthIter (a - 1 - r) G z θ| ≤ 200 * W := by
      rcases Nat.eq_zero_or_pos (a - 1 - r) with h0 | hpos
      · rw [h0]
        show |G z θ| ≤ 200 * W
        have hd := abs_Dz_iter_pth_le hsm hα hα1 hW b (by omega) z hz θ hθ
        rw [show G = Work.Spaces.DzIter b (Work.Spaces.pth f) from hGdef]
        linarith
      · obtain ⟨c, hc⟩ : ∃ c, a - 1 - r = c + 1 := ⟨a - 1 - r - 1, by omega⟩
        rw [hc]
        have hcomm := DzIter_DthIter_comm (g := Work.Spaces.pth f) isOpen_strp
          (Work.Spaces.contDiffOn_uncurry_pth isOpen_strp hsm.1) b (c + 1)
        have hstar : Work.Spaces.DthIter (c + 1) G z θ
            = Work.Spaces.DzIter b (Work.Spaces.DthIter (c + 1) (Work.Spaces.pth f)) z θ := by
          rw [hGdef]
          exact (hcomm hstrp).symm
        rw [hstar]
        have hbc : b + (c + 1) ≤ 4 := by omega
        exact abs_DzIter_DthIter_pth_le hsm hα hα1 hW (c + 1) (by omega) b hbc z hz θ hθIθ
    have hA : Asin r * Real.sin (2 * θ) ≤ 48 * Real.sin (2 * θ) :=
      mul_le_mul_of_nonneg_right (Asin_le r hr4) hS
    calc |Work.Spaces.DthIter r Sfun z θ| * |Work.Spaces.DthIter (a - 1 - r) G z θ|
        ≤ (Asin r * Real.sin (2 * θ)) * (200 * W) :=
          mul_le_mul h1 h2 (abs_nonneg _)
            (mul_nonneg (Asin_pos r).le hS)
      _ ≤ (48 * Real.sin (2 * θ)) * (200 * W) :=
          mul_le_mul_of_nonneg_right hA (by linarith [hWnn])
      _ = 48 * (200 * W) * Real.sin (2 * θ) := by ring
  calc (1 + ∑ r ∈ Finset.range ((a - 1) + 1), ((a - 1).choose r : ℝ))
        * ∑ r ∈ Finset.range ((a - 1) + 1),
            |Work.Spaces.DthIter r Sfun z θ| * |Work.Spaces.DthIter (a - 1 - r) G z θ|
      ≤ 9 * ∑ r ∈ Finset.range ((a - 1) + 1), (48 * (200 * W) * Real.sin (2 * θ)) := by
        refine mul_le_mul hcoef (Finset.sum_le_sum hterm)
          (Finset.sum_nonneg fun r _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))
          (by norm_num)
    _ = 9 * ((((a - 1) + 1 : ℕ) : ℝ) * (48 * (200 * W) * Real.sin (2 * θ))) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ 9 * (4 * (48 * (200 * W) * Real.sin (2 * θ))) := by
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        have h4 : (((a - 1) + 1 : ℕ) : ℝ) ≤ 4 := by
          have : (a - 1) + 1 ≤ 4 := by omega
          exact_mod_cast this
        exact mul_le_mul_of_nonneg_right h4
          (mul_nonneg (mul_nonneg (by norm_num) (mul_nonneg (by norm_num) hWnn)) hS)
    _ = 345600 * Real.sin (2 * θ) * W := by ring_nf
    _ ≤ 400000 * Real.sin (2 * θ) * W := by
        have hSW : (0 : ℝ) ≤ Real.sin (2 * θ) * W := mul_nonneg hS hWnn
        nlinarith

end Work.FTS.H2
