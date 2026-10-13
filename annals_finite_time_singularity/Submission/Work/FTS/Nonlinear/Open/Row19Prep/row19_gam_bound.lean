/-
# Row 19 (`N₃^{**}`): the `γ`-family of pointwise bounds

The main estimate of `Submission/Work/FTS/Nonlinear/Open/Row19Prep/row19_gam_bound.lean`; the
auxiliary vocabulary and the elementary smoothness/calculus lemmas live in
`Submission.Work.FTS.Nonlinear.Open.Row19Prep.gam_aux`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.NonlinRows.sqm_pz_DthIter_mul_le_4_open
import Submission.Work.FTS.Nonlinear.Open.Row19Prep.Defs
import Submission.Work.FTS.Nonlinear.Open.Row19Prep.H2bBound
import Submission.Work.FTS.Nonlinear.Open.Row19Prep.gam_aux
import Submission.Work.Spaces.Gamma_WlInf
import Submission.Work.Spaces.factor_bound
import Submission.Work.Spaces.WlInf_terms

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.Open.Row19Prep

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-- **Row 19, the `γ`-family of pointwise bounds.** With `A` a coefficient in `𝒲^{4,∞}` of norm
`≤ Λ` (this is `StarPkgo2.VzW` for `A = ((z+1)/z)·V(Φ̃_*)`),

`|(1+z)·w(z)·z^l·∂_z^l D_θ^i (α·Γ(θ)·(A·H₂))| ≤ C·α·Λ·Φ(θ)`  for `1 ≤ i`, `l+i ≤ 4`,
`z > 0`, `θ ∈ (0,π/2)`,

where `H₂(z) = 2z²(1-z)/(1+z)⁴`, `w(z) = (1+z)²/z²` and `Φ(θ) = (α+sin 2θ)·sin(2θ)^{α/5}`.
These are exactly the `hB`-hypotheses of `Work.FTS.NonlinRows.wtoHQ_of_pointwise_open` for
`f = V(Φ̃_*)·D_zF_*` (up to the constant `1/c(α)`); the `Φ` factor is the *inverse* of the
`𝒲^{l,∞}` angular weight, so every `D_θ`-derivative of the coefficient `A` supplies one copy of
it.

Suggested route (all ingredients exist):
* `Work.FTS.NonlinRows.sqm_pz_DthIter_mul_le_4_open` with `(l, i)` is the Leibniz bound
  `≤ 257·Σ_{c≤l}Σ_{a≤i}|∂_z^cD_θ^a(α·Γ)|·|∂_z^{l-c}D_θ^{i-a}K|` for `K = A·H₂`; the terms with
  `c ≥ 1` vanish because `D_θ^a(Γ)` is `θ`-only (`Work.FTS.Nonlinear.Open.Row19Prep.pzIter_theta_only`);
* for the `K`-factor iterate the second Leibniz (with `k := l-c`, `j := i-a`) together with
  `Work.FTS.Nonlinear.Open.Row19Prep.DthIter_succ_z_only`, which kills every term in which at
  least one `D_θ` falls on the `z`-only `H₂` — so only the term with *all* `D_θ`-derivatives on
  `A` survives;
* `Work.Spaces.pz_Dth_sup_bound` gives `|∂_z^{c}D_θ^{b}A| ≤ Λ/(1+z)^{c}·Φ(θ)` for `b ≥ 1`, and
  `Work.Spaces.WlInf_z_bound` gives `|∂_z^{c}A| ≤ Λ/(1+z)^{c}` for `b = 0`;
* `|D_θ^a Γ| ≤ C_a·α·Γ` for `a ≥ 1` (`Work.Spaces.dthU_Gam_le`) and `Γ ≤ 1`
  (`Work.Spaces.Gam_bounds`), together with `α·Γ ≤ Φ`
  (`Row19Prep.alpha_mul_Gam_le_PhiA`);
* `Work.FTS.Nonlinear.Open.Row19Prep.H2b_weight_le` bounds the radial factor, and `Φ ≤ 2` on
  `Iθ` (`Row19Prep.PhiA_le_two`) absorbs the extra copies of `Φ`. -/
theorem row19_gam_bound : ∃ C : ℝ, 0 < C ∧ ∀ (α Λ : ℝ) (A : ℝ → ℝ → ℝ),
    0 < α → α ≤ 1 → 0 ≤ Λ → Work.Spaces.WlInf α 4 A ≤ Λ →
    Work.Spaces.WlInfMem α 4 A → Work.FTS.EllipticEst.SmoothOpen A →
    ∀ (i l : ℕ), 1 ≤ i → l + i ≤ 4 → ∀ z : ℝ, 0 < z → ∀ θ : ℝ, θ ∈ Set.Ioo 0 (π / 2) →
      |(1 + z) * Work.Spaces.w z * z ^ l * Work.Spaces.pzIter l
        (Work.Spaces.DthIter i (fun z θ => α * Work.Spaces.Gam α θ
          * (A z θ * Work.FTS.Nonlinear.Open.Row19Prep.H2b z))) z θ|
        ≤ C * (α * Λ) * Work.FTS.Nonlinear.Open.Row19Prep.PhiA α θ := by
  obtain ⟨CH, hCH0, hCH⟩ := H2b_weight_le
  refine ⟨257 * 257 * 125 * CH * (1 + TB), ?_, ?_⟩
  · exact mul_pos (mul_pos (by norm_num) hCH0) (by linarith [TB_nonneg])
  intro α Λ A hα hα1 hΛ0 hWΛ hmem hAsm i l hi hli z hz θ hθ
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hzI : z ∈ Work.Spaces.Iz := le_of_lt hz
  have hl4 : l ≤ 4 := by omega
  have hi4 : i ≤ 4 := by omega
  have hz1 : (0 : ℝ) < 1 + z := by linarith
  have hΦ0 : 0 ≤ PhiA α θ := PhiA_nonneg hα hθI
  have hG0 : 0 ≤ Work.Spaces.Gam α θ := Gam_nonneg hα hθI
  have hG1 : Work.Spaces.Gam α θ ≤ 1 := Gam_le_one hα hθI
  have hαG : α * Work.Spaces.Gam α θ ≤ PhiA α θ := alpha_mul_Gam_le_PhiA hα hα1 hθI
  have hL0 : 0 ≤ Work.Spaces.WlInf α 4 A := WlInf_nonneg α 4 A hmem
  have hAraw : (1 + z) * Work.Spaces.w z * z ^ l = (1 + z) ^ 3 * z ^ l / z ^ 2 := by
    rw [Work.Spaces.w]; field_simp
  have hAraw0 : (0 : ℝ) ≤ (1 + z) ^ 3 * z ^ l / z ^ 2 := by positivity
  have hTB0 : 0 ≤ TB := TB_nonneg
  -- (i) the `θ`-only factor: `c ≥ 1` gives nothing, `c = 0` gives the `dthU`-iterate
  have hcpart : ∀ c a : ℕ,
      (1 + z) ^ c * |Work.Spaces.pzIter c
          (Work.Spaces.DthIter a (fun z θ : ℝ => α * Work.Spaces.Gam α θ)) z θ|
        ≤ |Work.Spaces.dthU^[a] (fun t : ℝ => α * Work.Spaces.Gam α t) θ| := by
    intro c a
    have h1 : Work.Spaces.pzIter c
          (Work.Spaces.DthIter a (fun z θ : ℝ => α * Work.Spaces.Gam α θ))
        = fun z θ => (if c = 0 then
            Work.Spaces.dthU^[a] (fun t : ℝ => α * Work.Spaces.Gam α t) θ else 0) := by
      rw [DthIter_theta_only, pzIter_theta_only]
    rcases Nat.eq_zero_or_pos c with hc | hc
    · subst hc
      rw [pow_zero, one_mul, h1]
      change |(if (0 : ℕ) = 0 then
          Work.Spaces.dthU^[a] (fun t : ℝ => α * Work.Spaces.Gam α t) θ else 0)|
        ≤ |Work.Spaces.dthU^[a] (fun t : ℝ => α * Work.Spaces.Gam α t) θ|
      rw [if_pos rfl]
    · rw [h1]
      change (1 + z) ^ c * |(if c = 0 then
          Work.Spaces.dthU^[a] (fun t : ℝ => α * Work.Spaces.Gam α t) θ else 0)|
        ≤ |Work.Spaces.dthU^[a] (fun t : ℝ => α * Work.Spaces.Gam α t) θ|
      rw [if_neg (Nat.pos_iff_ne_zero.mp hc), abs_zero, mul_zero]
      exact abs_nonneg _
  -- (ii) the angular jets of `α·Γ`
  have hdth : ∀ a : ℕ, a ≤ 4 →
      |Work.Spaces.dthU^[a] (fun t : ℝ => α * Work.Spaces.Gam α t) θ|
        ≤ α * (if a = 0 then (1 : ℝ) else α * TB) * Work.Spaces.Gam α θ := by
    intro a ha
    rw [Work.Spaces.dthU_iter_const_mul]
    change |α * Work.Spaces.dthU^[a] (fun t : ℝ => Work.Spaces.Gam α t) θ|
      ≤ α * (if a = 0 then (1 : ℝ) else α * TB) * Work.Spaces.Gam α θ
    rcases Nat.eq_zero_or_pos a with h | h
    · subst h
      have h0 : Work.Spaces.dthU^[0] (fun t : ℝ => Work.Spaces.Gam α t) θ
          = Work.Spaces.Gam α θ := rfl
      rw [h0, if_pos rfl, mul_one, abs_mul, abs_of_pos hα, abs_of_nonneg hG0]
    · have hd := Work.Spaces.dthU_Gam_le a h α hα hα1 θ hθI
      have hb := tBound_le_TB h ha
      rw [if_neg (Nat.pos_iff_ne_zero.mp h), abs_mul, abs_of_pos hα]
      calc α * |Work.Spaces.dthU^[a] (fun t : ℝ => Work.Spaces.Gam α t) θ|
          ≤ α * (α * TB * Work.Spaces.Gam α θ) := by
            refine mul_le_mul_of_nonneg_left ?_ hα.le
            exact hd.trans (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hb hα.le) hG0)
        _ = α * (α * TB) * Work.Spaces.Gam α θ := by ring
  -- (iii) the combined angular bound `|D_θ^a(αΓ)|·Ψ(a) ≤ (1+TB)·α·Φ`
  have hkey : ∀ a : ℕ, a ≤ i →
      |Work.Spaces.dthU^[a] (fun t : ℝ => α * Work.Spaces.Gam α t) θ| * PsiA α (i - a) θ
        ≤ (1 + TB) * (α * PhiA α θ) := by
    intro a hai
    have ha4 : a ≤ 4 := by omega
    have hd := hdth a ha4
    rw [PsiA_eq]
    by_cases hia : i - a = 0
    · rw [if_pos hia]
      have hdz : α * (if a = 0 then (1 : ℝ) else α * TB) = α * (α * TB) := by
        rw [if_neg (by omega : a ≠ 0)]
      rw [hdz] at hd
      calc |Work.Spaces.dthU^[a] (fun t : ℝ => α * Work.Spaces.Gam α t) θ| * 1
          ≤ (α * (α * TB) * Work.Spaces.Gam α θ) * 1 :=
            mul_le_mul_of_nonneg_right hd (by norm_num)
        _ = TB * (α * (α * Work.Spaces.Gam α θ)) := by ring
        _ ≤ TB * (α * PhiA α θ) := by
            refine mul_le_mul_of_nonneg_left ?_ hTB0
            exact mul_le_mul_of_nonneg_left hαG hα.le
        _ ≤ (1 + TB) * (α * PhiA α θ) := by
            have hx : 0 ≤ α * PhiA α θ := mul_nonneg hα.le hΦ0
            nlinarith [hTB0, hx]
    · rw [if_neg hia]
      rcases Nat.eq_zero_or_pos a with ha0 | hapos
      · subst ha0
        have hdz : α * (if (0 : ℕ) = 0 then (1 : ℝ) else α * TB) = α := by
          rw [if_pos rfl, mul_one]
        rw [hdz] at hd
        calc |Work.Spaces.dthU^[0] (fun t : ℝ => α * Work.Spaces.Gam α t) θ| * PhiA α θ
            ≤ (α * Work.Spaces.Gam α θ) * PhiA α θ :=
              mul_le_mul_of_nonneg_right hd hΦ0
          _ ≤ (α * 1) * PhiA α θ :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hG1 hα.le) hΦ0
          _ = α * PhiA α θ := by ring
          _ ≤ (1 + TB) * (α * PhiA α θ) := by
              have hx : 0 ≤ α * PhiA α θ := mul_nonneg hα.le hΦ0
              nlinarith [hTB0, hx]
      · have hdz : α * (if a = 0 then (1 : ℝ) else α * TB) = α * (α * TB) := by
          rw [if_neg (by omega : a ≠ 0)]
        rw [hdz] at hd
        have hαG1 : α * Work.Spaces.Gam α θ ≤ 1 := by
          have h2 := mul_le_mul hα1 hG1 hG0 (by norm_num : (0 : ℝ) ≤ 1)
          linarith
        calc |Work.Spaces.dthU^[a] (fun t : ℝ => α * Work.Spaces.Gam α t) θ| * PhiA α θ
            ≤ (α * (α * TB) * Work.Spaces.Gam α θ) * PhiA α θ :=
              mul_le_mul_of_nonneg_right hd hΦ0
          _ = TB * ((α * Work.Spaces.Gam α θ) * (α * PhiA α θ)) := by ring
          _ ≤ TB * (1 * (α * PhiA α θ)) := by
              refine mul_le_mul_of_nonneg_left ?_ hTB0
              exact mul_le_mul_of_nonneg_right hαG1 (mul_nonneg hα.le hΦ0)
          _ = TB * (α * PhiA α θ) := by ring
          _ ≤ (1 + TB) * (α * PhiA α θ) := by
              have hx : 0 ≤ α * PhiA α θ := mul_nonneg hα.le hΦ0
              nlinarith [hTB0, hx]
  -- (iv) the per-`(c,a,c')` factor bound: `A`-jet times `H₂`-jet
  have hsub : ∀ c a c' : ℕ, c ≤ l → a ≤ i → c' ≤ l - c →
      ((1 + z) ^ c' * |Work.Spaces.pzIter c' (Work.Spaces.DthIter (i - a) A) z θ|)
        * ((1 + z) ^ 3 * z ^ l / z ^ 2 / (1 + z) ^ (c + c')
            * |deriv^[l - c - c'] H2b z|)
      ≤ (Λ * PsiA α (i - a) θ) * CH := by
    intro c a c' hcl hai hc'
    have hPsi0 : 0 ≤ PsiA α (i - a) θ := PsiA_nonneg hα hθI
    have hcf : c' ≤ 4 := by omega
    have hb := Work.Spaces.factor_bound α hα A hmem c' (i - a) hcf (fun _ => by omega)
      z θ hzI hθI
    have hX : (1 + z) ^ c' * |Work.Spaces.pzIter c' (Work.Spaces.DthIter (i - a) A) z θ|
        ≤ Λ * PsiA α (i - a) θ := by
      have hb' : |(z + 1) ^ c' * Work.Spaces.pzIter c' (Work.Spaces.DthIter (i - a) A) z θ|
          ≤ Work.Spaces.WlInf α 4 A * PsiA α (i - a) θ := by
        have h1 : (if (i - a) = 0 then (1 : ℝ) else
            (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))
              = PsiA α (i - a) θ := rfl
        rw [← h1]
        exact hb
      rw [show (z : ℝ) + 1 = 1 + z by ring, abs_mul,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ (1 + z) ^ c')] at hb'
      exact hb'.trans (mul_le_mul_of_nonneg_right hWΛ hPsi0)
    have hY : (1 + z) ^ 3 * z ^ l / z ^ 2 / (1 + z) ^ (c + c') * |deriv^[l - c - c'] H2b z|
        ≤ CH := by
      have hZ := hCH l (l - c - c') hl4 (by omega) z hz
      have hcc : l - (l - c - c') = c + c' := by omega
      rw [hcc, hAraw] at hZ
      exact hZ
    exact mul_le_mul hX hY (by positivity) (mul_nonneg hΛ0 hPsi0)
  -- (v) the outer Leibniz expansion of `∂_z^l D_θ^i (αΓ · (A·H₂))`
  have hstep2 : (1 + z) ^ 3 * z ^ l / z ^ 2
        * |Work.Spaces.pzIter l (Work.Spaces.DthIter i (fun z θ : ℝ =>
            α * Work.Spaces.Gam α θ * (A z θ * H2b z))) z θ|
      ≤ 257 * ∑ c ∈ Finset.range (l + 1), ∑ a ∈ Finset.range (i + 1),
          (1 + z) ^ 3 * z ^ l / z ^ 2
            * (|Work.Spaces.pzIter c (Work.Spaces.DthIter a
                (fun z θ : ℝ => α * Work.Spaces.Gam α θ)) z θ|
              * |Work.Spaces.pzIter (l - c) (Work.Spaces.DthIter (i - a)
                (fun z θ : ℝ => A z θ * H2b z)) z θ|) := by
    have hout := Work.FTS.NonlinRows.sqm_pz_DthIter_mul_le_4_open l i hl4 hi4
      (fun z θ : ℝ => α * Work.Spaces.Gam α θ) (fun z θ : ℝ => A z θ * H2b z)
      (smoothOpen_alpha_Gam α) (smoothOpen_mul hAsm smoothOpen_H2b) z hz θ hθ
    have hs := mul_le_mul_of_nonneg_left hout hAraw0
    have he : (1 + z) ^ 3 * z ^ l / z ^ 2
          * (257 * ∑ c ∈ Finset.range (l + 1), ∑ a ∈ Finset.range (i + 1),
              |Work.Spaces.pzIter c (Work.Spaces.DthIter a
                (fun z θ : ℝ => α * Work.Spaces.Gam α θ)) z θ|
                * |Work.Spaces.pzIter (l - c) (Work.Spaces.DthIter (i - a)
                (fun z θ : ℝ => A z θ * H2b z)) z θ|)
        = 257 * ∑ c ∈ Finset.range (l + 1), ∑ a ∈ Finset.range (i + 1),
            (1 + z) ^ 3 * z ^ l / z ^ 2
              * (|Work.Spaces.pzIter c (Work.Spaces.DthIter a
                  (fun z θ : ℝ => α * Work.Spaces.Gam α θ)) z θ|
                * |Work.Spaces.pzIter (l - c) (Work.Spaces.DthIter (i - a)
                  (fun z θ : ℝ => A z θ * H2b z)) z θ|) := by
      rw [show (1 + z) ^ 3 * z ^ l / z ^ 2
            * (257 * ∑ c ∈ Finset.range (l + 1), ∑ a ∈ Finset.range (i + 1),
                |Work.Spaces.pzIter c (Work.Spaces.DthIter a
                  (fun z θ : ℝ => α * Work.Spaces.Gam α θ)) z θ|
                  * |Work.Spaces.pzIter (l - c) (Work.Spaces.DthIter (i - a)
                  (fun z θ : ℝ => A z θ * H2b z)) z θ|)
          = 257 * ((1 + z) ^ 3 * z ^ l / z ^ 2
            * ∑ c ∈ Finset.range (l + 1), ∑ a ∈ Finset.range (i + 1),
                |Work.Spaces.pzIter c (Work.Spaces.DthIter a
                  (fun z θ : ℝ => α * Work.Spaces.Gam α θ)) z θ|
                  * |Work.Spaces.pzIter (l - c) (Work.Spaces.DthIter (i - a)
                  (fun z θ : ℝ => A z θ * H2b z)) z θ|) from by ring]
      congr 1
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [Finset.mul_sum]
    rw [he] at hs
    exact hs
  have hK5 : 0 ≤ 257 * 5 * CH * Λ * ((1 + TB) * (α * PhiA α θ)) := by
    have h1 : 0 ≤ Λ * ((1 + TB) * (α * PhiA α θ)) :=
      mul_nonneg hΛ0 (mul_nonneg (by linarith [hTB0]) (mul_nonneg hα.le hΦ0))
    nlinarith [h1, hCH0]
  -- (vi) the per-`(c,a)` bound
  have hstep3 : ∀ c ∈ Finset.range (l + 1), ∀ a ∈ Finset.range (i + 1),
      (1 + z) ^ 3 * z ^ l / z ^ 2
        * (|Work.Spaces.pzIter c (Work.Spaces.DthIter a
              (fun z θ : ℝ => α * Work.Spaces.Gam α θ)) z θ|
            * |Work.Spaces.pzIter (l - c) (Work.Spaces.DthIter (i - a)
              (fun z θ : ℝ => A z θ * H2b z)) z θ|)
      ≤ 257 * 5 * CH * Λ * ((1 + TB) * (α * PhiA α θ)) := by
    intro c hc a ha
    rw [Finset.mem_range] at hc ha
    have hcl : c ≤ l := by omega
    have hai : a ≤ i := by omega
    have hA2 := Kaf_pz_Dth_le A hAsm (l - c) (i - a) (by omega) (by omega) z hz θ hθ
    have hsplit1 : (1 + z) ^ 3 * z ^ l / z ^ 2
        = (1 + z) ^ c * ((1 + z) ^ 3 * z ^ l / z ^ 2 / (1 + z) ^ c) :=
      (mul_div_cancel₀ ((1 + z) ^ 3 * z ^ l / z ^ 2) (ne_of_gt (pow_pos hz1 c))).symm
    have hstep31 : (1 + z) ^ 3 * z ^ l / z ^ 2
          * (|Work.Spaces.pzIter c (Work.Spaces.DthIter a
                (fun z θ : ℝ => α * Work.Spaces.Gam α θ)) z θ|
              * |Work.Spaces.pzIter (l - c) (Work.Spaces.DthIter (i - a)
                (fun z θ : ℝ => A z θ * H2b z)) z θ|)
        = ((1 + z) ^ c * |Work.Spaces.pzIter c (Work.Spaces.DthIter a
              (fun z θ : ℝ => α * Work.Spaces.Gam α θ)) z θ|)
          * ((1 + z) ^ 3 * z ^ l / z ^ 2 / (1 + z) ^ c
            * |Work.Spaces.pzIter (l - c) (Work.Spaces.DthIter (i - a)
              (fun z θ : ℝ => A z θ * H2b z)) z θ|) := by
      have hc': (1 + z) ^ c * ((1 + z) ^ 3 * z ^ l / z ^ 2 / (1 + z) ^ c)
          = (1 + z) ^ 3 * z ^ l / z ^ 2 :=
        mul_div_cancel₀ ((1 + z) ^ 3 * z ^ l / z ^ 2) (ne_of_gt (pow_pos hz1 c))
      nth_rewrite 1 [← hc']
      ring
    rw [hstep31]
    have hb1 := hcpart c a
    have hcw : 0 ≤ (1 + z) ^ 3 * z ^ l / z ^ 2 / (1 + z) ^ c := by positivity
    have hb2 : (1 + z) ^ 3 * z ^ l / z ^ 2 / (1 + z) ^ c
          * |Work.Spaces.pzIter (l - c) (Work.Spaces.DthIter (i - a)
            (fun z θ : ℝ => A z θ * H2b z)) z θ|
        ≤ 257 * (((l - c + 1 : ℕ)) : ℝ) * ((Λ * PsiA α (i - a) θ) * CH) := by
      have hleib := mul_le_mul_of_nonneg_left hA2 hcw
      have heq : (1 + z) ^ 3 * z ^ l / z ^ 2 / (1 + z) ^ c
            * (257 * ∑ c' ∈ Finset.range (l - c + 1),
                |Work.Spaces.pzIter c' (Work.Spaces.DthIter (i - a) A) z θ|
                  * |deriv^[l - c - c'] H2b z|)
          = 257 * ∑ c' ∈ Finset.range (l - c + 1),
              ((1 + z) ^ 3 * z ^ l / z ^ 2 / (1 + z) ^ c)
                * (|Work.Spaces.pzIter c' (Work.Spaces.DthIter (i - a) A) z θ|
                  * |deriv^[l - c - c'] H2b z|) := by
        rw [show (1 + z) ^ 3 * z ^ l / z ^ 2 / (1 + z) ^ c
              * (257 * ∑ c' ∈ Finset.range (l - c + 1),
                  |Work.Spaces.pzIter c' (Work.Spaces.DthIter (i - a) A) z θ|
                    * |deriv^[l - c - c'] H2b z|)
            = 257 * ((1 + z) ^ 3 * z ^ l / z ^ 2 / (1 + z) ^ c
              * ∑ c' ∈ Finset.range (l - c + 1),
                  |Work.Spaces.pzIter c' (Work.Spaces.DthIter (i - a) A) z θ|
                    * |deriv^[l - c - c'] H2b z|) from by ring]
        congr 1
        rw [Finset.mul_sum]
      rw [heq] at hleib
      have hsum' : (∑ c' ∈ Finset.range (l - c + 1),
            (1 + z) ^ 3 * z ^ l / z ^ 2 / (1 + z) ^ c
              * (|Work.Spaces.pzIter c' (Work.Spaces.DthIter (i - a) A) z θ|
                * |deriv^[l - c - c'] H2b z|))
          ≤ (((l - c + 1 : ℕ)) : ℝ) * ((Λ * PsiA α (i - a) θ) * CH) := by
        have hsum1 : (∑ c' ∈ Finset.range (l - c + 1),
              (1 + z) ^ 3 * z ^ l / z ^ 2 / (1 + z) ^ c
                * (|Work.Spaces.pzIter c' (Work.Spaces.DthIter (i - a) A) z θ|
                  * |deriv^[l - c - c'] H2b z|))
            ≤ ∑ _c' ∈ Finset.range (l - c + 1), ((Λ * PsiA α (i - a) θ) * CH) :=
          Finset.sum_le_sum fun c' hc' => by
            rw [Finset.mem_range] at hc'
            have hc'le : c' ≤ l - c := by omega
            have hsp : (1 + z) ^ 3 * z ^ l / z ^ 2 / (1 + z) ^ c
                = (1 + z) ^ c' * ((1 + z) ^ 3 * z ^ l / z ^ 2 / (1 + z) ^ (c + c')) := by
              rw [pow_add, ← div_div]
              exact (mul_div_cancel₀ _ (ne_of_gt (pow_pos hz1 c'))).symm
            rw [show (1 + z) ^ 3 * z ^ l / z ^ 2 / (1 + z) ^ c
                  * (|Work.Spaces.pzIter c' (Work.Spaces.DthIter (i - a) A) z θ|
                    * |deriv^[l - c - c'] H2b z|)
                = ((1 + z) ^ c' * |Work.Spaces.pzIter c' (Work.Spaces.DthIter (i - a) A) z θ|)
                  * ((1 + z) ^ 3 * z ^ l / z ^ 2 / (1 + z) ^ (c + c')
                    * |deriv^[l - c - c'] H2b z|) from by rw [hsp]; ring]
            exact hsub c a c' hcl hai hc'le
        refine hsum1.trans ?_
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      calc (1 + z) ^ 3 * z ^ l / z ^ 2 / (1 + z) ^ c
            * |Work.Spaces.pzIter (l - c) (Work.Spaces.DthIter (i - a)
              (fun z θ : ℝ => A z θ * H2b z)) z θ|
          ≤ 257 * (∑ c' ∈ Finset.range (l - c + 1),
              (1 + z) ^ 3 * z ^ l / z ^ 2 / (1 + z) ^ c
                * (|Work.Spaces.pzIter c' (Work.Spaces.DthIter (i - a) A) z θ|
                  * |deriv^[l - c - c'] H2b z|)) := hleib
        _ ≤ 257 * ((((l - c + 1 : ℕ)) : ℝ) * ((Λ * PsiA α (i - a) θ) * CH)) :=
            mul_le_mul_of_nonneg_left hsum' (by norm_num)
        _ = 257 * (((l - c + 1 : ℕ)) : ℝ) * ((Λ * PsiA α (i - a) θ) * CH) := by ring
    refine (mul_le_mul hb1 hb2 (by positivity) (abs_nonneg _)).trans ?_
    calc |Work.Spaces.dthU^[a] (fun t : ℝ => α * Work.Spaces.Gam α t) θ|
          * (257 * (((l - c + 1 : ℕ)) : ℝ) * ((Λ * PsiA α (i - a) θ) * CH))
        ≤ |Work.Spaces.dthU^[a] (fun t : ℝ => α * Work.Spaces.Gam α t) θ|
          * (257 * 5 * ((Λ * PsiA α (i - a) θ) * CH)) := by
          refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
          have h1 : (((l - c + 1 : ℕ)) : ℝ) ≤ 5 := by
            have h2 : l - c + 1 ≤ 5 := by omega
            exact_mod_cast h2
          have h2 : 0 ≤ (Λ * PsiA α (i - a) θ) * CH :=
            mul_nonneg (mul_nonneg hΛ0 (PsiA_nonneg hα hθI)) hCH0.le
          nlinarith [h1, h2]
      _ = 257 * 5 * CH * Λ
            * (|Work.Spaces.dthU^[a] (fun t : ℝ => α * Work.Spaces.Gam α t) θ|
              * PsiA α (i - a) θ) := by ring
      _ ≤ 257 * 5 * CH * Λ * ((1 + TB) * (α * PhiA α θ)) :=
          mul_le_mul_of_nonneg_left (hkey a hai) (by nlinarith [hCH0, hΛ0])
  -- (vii) the double sum
  have hsum : (∑ c ∈ Finset.range (l + 1), ∑ a ∈ Finset.range (i + 1),
        (1 + z) ^ 3 * z ^ l / z ^ 2
          * (|Work.Spaces.pzIter c (Work.Spaces.DthIter a
                (fun z θ : ℝ => α * Work.Spaces.Gam α θ)) z θ|
              * |Work.Spaces.pzIter (l - c) (Work.Spaces.DthIter (i - a)
                (fun z θ : ℝ => A z θ * H2b z)) z θ|))
      ≤ 25 * (257 * 5 * CH * Λ * ((1 + TB) * (α * PhiA α θ))) := by
    refine (Finset.sum_le_sum fun c hc =>
      Finset.sum_le_sum fun a ha => hstep3 c hc a ha).trans ?_
    calc (∑ c ∈ Finset.range (l + 1), ∑ a ∈ Finset.range (i + 1),
          (257 * 5 * CH * Λ * ((1 + TB) * (α * PhiA α θ))))
        = (((l + 1) * (i + 1) : ℕ) : ℝ)
            * (257 * 5 * CH * Λ * ((1 + TB) * (α * PhiA α θ))) := by
          rw [Finset.sum_const, Finset.card_range, Finset.sum_const, Finset.card_range,
            nsmul_eq_mul, nsmul_eq_mul, Nat.cast_mul]
          ring
      _ ≤ 25 * (257 * 5 * CH * Λ * ((1 + TB) * (α * PhiA α θ))) := by
          refine mul_le_mul_of_nonneg_right ?_ hK5
          have h1 : (l + 1) * (i + 1) ≤ 25 := by
            have a1 : l + 1 ≤ 5 := by omega
            have a2 : i + 1 ≤ 5 := by omega
            calc (l + 1) * (i + 1) ≤ 5 * 5 := Nat.mul_le_mul a1 a2
              _ = 25 := rfl
          exact_mod_cast h1
  calc |(1 + z) * Work.Spaces.w z * z ^ l * Work.Spaces.pzIter l
        (Work.Spaces.DthIter i (fun z θ => α * Work.Spaces.Gam α θ
          * (A z θ * H2b z))) z θ|
      = (1 + z) ^ 3 * z ^ l / z ^ 2
        * |Work.Spaces.pzIter l (Work.Spaces.DthIter i (fun z θ : ℝ =>
            α * Work.Spaces.Gam α θ * (A z θ * H2b z))) z θ| := by
        rw [hAraw, abs_mul, abs_of_nonneg hAraw0]
    _ ≤ 257 * ∑ c ∈ Finset.range (l + 1), ∑ a ∈ Finset.range (i + 1),
          (1 + z) ^ 3 * z ^ l / z ^ 2
            * (|Work.Spaces.pzIter c (Work.Spaces.DthIter a
                (fun z θ : ℝ => α * Work.Spaces.Gam α θ)) z θ|
              * |Work.Spaces.pzIter (l - c) (Work.Spaces.DthIter (i - a)
                (fun z θ : ℝ => A z θ * H2b z)) z θ|) := hstep2
    _ ≤ 257 * (25 * (257 * 5 * CH * Λ * ((1 + TB) * (α * PhiA α θ)))) :=
        mul_le_mul_of_nonneg_left hsum (by norm_num)
    _ = (257 * 257 * 125 * CH * (1 + TB)) * (α * Λ) * PhiA α θ := by ring

end Work.FTS.Nonlinear.Open.Row19Prep
