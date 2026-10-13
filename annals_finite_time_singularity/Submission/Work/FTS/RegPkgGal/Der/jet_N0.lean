import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Submission.Work.FTS.Regularity.Defs
import Submission.Work.FTS.Regularity.regPkg_inhabited
import Submission.Work.Construction.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS.RegPkgGal.Der.jet_N0`

The quadratic term `N₀` of the fake-time equation (tex `\eqref{N0}`),

  `N₀(α, F, g) = (3/(2α)) sin(2θ) L₁₂(F_*)(z) ∂_θF_*(z,θ)
      - c₂(θ) L₁₂(F_*)(z) D_zF_*(z,θ)
      + (1/α) L₁₂(g)(z) g(z,θ)
      + (3/(2α)) sin(2θ) L₁₂(g)(z) ∂_θF(z,θ)
      - c₂(θ) L₁₂(g)(z) D_zF(z,θ)
      - c₂(θ) L₁₂(F_*)(z) D_zg(z,θ)`

evaluated on the fake-time family `F(τ) = F_* + g(τ)`, `g(τ)` (i.e. on
`Construction.Ftau (pExp α) g τ` and `Regularity.gSlice g τ`), is again a `Jet` (bounded and
jointly `α`-Hölder on the strip `z ≥ 0, θ ∈ Iθ, τ ∈ [0,S]`).

The proof is the `Jet`-calculus of `Submission.Work.FTS.Regularity.regPkg_inhabited`
(`Jet.add`, `Jet.neg`, `Jet.mul`, `Jet.congr`) together with

* the elementary `Jet` of the angular coefficient `c₂(θ) = cos 2θ - sin²θ` (`jN0_c2m`: bounded by
  `2` and `4`-Lipschitz, hence an `α`-Hölder `Jet` with constant `4`);
* the `Jet` of the explicit profile `F_* = Construction.Fstar (pExp α)` (`hFstJ`, constant `100`),
  from the packaged moduli `Regularity.fstar_abs_le_gamma` and
  `Regularity.fstar_joint_modulus` — this is what turns the hypothesis `hF` on
  `F(τ) = F_* + g(τ)` into the `Jet` of the perturbation `g` itself;
* the substitution `sin(2θ)∂_θ = D_θ` (`Spaces.Dth`), which is what makes the two `∂_θ`-slots
  consumable from the hypotheses `hDthF`, `hDthFstar` (the *weighted* angular derivative is the
  only one that is a `Jet` for the genuine profile — see `NOTES_RegPkgGal` §6);
* `Coercivity.L12f = Construction.L12` (definitional), so the hypotheses `hL12g`, `hL12Fstar`
  supply the two `L₁₂`-slots.

This is the leaf `Der.jet_N0` of the `R5Slot` tree (NOTES_RegPkgGal §14), consumed by
`Der.rhs_jet_of_parts`.
-/

namespace Work.FTS.RegPkgGal.Der

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## Two elementary `Jet`-closure helpers -/

/-- Multiplication of a `Jet` by a constant: if `f` is a `Jet` of constant `N`, then so is
`c · f`, with constant `|c| · N`. -/
theorem jN0_const_mul {α S N c : ℝ} {f : ℝ → ℝ → ℝ → ℝ}
    (h : Work.FTS.Regularity.Jet α S N f) :
    Work.FTS.Regularity.Jet α S (|c| * N) (fun z θ τ => c * f z θ τ) := by
  refine ⟨mul_nonneg (abs_nonneg c) h.1, ?_, ?_⟩
  · intro z θ τ hz hθ hτ
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (h.abs_le hz hθ hτ) (abs_nonneg c)
  · intro z z' θ θ' τ τ' hz hz' hθ hθ' hτ hτ'
    have h1 := h.2.2 z z' θ θ' τ τ' hz hz' hθ hθ' hτ hτ'
    rw [show c * f z θ τ - c * f z' θ' τ' = c * (f z θ τ - f z' θ' τ') by ring, abs_mul]
    calc |c| * |f z θ τ - f z' θ' τ'| ≤ |c| * (N * (|z - z'| + |θ - θ'| + |τ - τ'|) ^ α) :=
          mul_le_mul_of_nonneg_left h1 (abs_nonneg c)
      _ = (|c| * N) * (|z - z'| + |θ - θ'| + |τ - τ'|) ^ α := by ring

/-- The angular coefficient `c₂(θ) = cos 2θ - sin²θ` (`Construction.c2m`) is bounded by `2`. -/
theorem jN0_c2m_abs (θ : ℝ) : |Work.Construction.c2m θ| ≤ 2 := by
  rw [Work.Construction.c2m_eq]
  have h1 : |Real.cos (2 * θ)| ≤ 1 := abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
  have h2 : |Real.sin θ ^ 2| ≤ 1 := by
    rw [abs_sq]
    nlinarith [Real.neg_one_le_sin θ, Real.sin_le_one θ]
  calc |Real.cos (2 * θ) - Real.sin θ ^ 2|
      = |Real.cos (2 * θ) + -(Real.sin θ ^ 2)| := by rw [sub_eq_add_neg]
    _ ≤ |Real.cos (2 * θ)| + |-(Real.sin θ ^ 2)| := abs_add_le _ _
    _ = |Real.cos (2 * θ)| + |Real.sin θ ^ 2| := by rw [abs_neg]
    _ ≤ 1 + 1 := add_le_add h1 h2
    _ = 2 := by norm_num

/-- `θ ↦ c₂(θ) = cos 2θ - sin²θ` is `4`-Lipschitz. -/
theorem jN0_c2m_lip (θ θ' : ℝ) :
    |Work.Construction.c2m θ - Work.Construction.c2m θ'| ≤ 4 * |θ - θ'| := by
  rw [Work.Construction.c2m_eq θ, Work.Construction.c2m_eq θ']
  have hcos : |Real.cos (2 * θ) - Real.cos (2 * θ')| ≤ 2 * |θ - θ'| := by
    have h : |Real.cos (2 * θ) - Real.cos (2 * θ')| ≤ |2 * θ - 2 * θ'| := by
      have hh := Real.lipschitzWith_cos.dist_le_mul (2 * θ) (2 * θ')
      simpa [Real.dist_eq] using hh
    have h2 : |2 * θ - 2 * θ'| = 2 * |θ - θ'| := by
      rw [show 2 * θ - 2 * θ' = 2 * (θ - θ') by ring, abs_mul,
        abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
    rw [h2] at h
    exact h
  have hsin : |Real.sin θ ^ 2 - Real.sin θ' ^ 2| ≤ 2 * |θ - θ'| := by
    have hs : |Real.sin θ - Real.sin θ'| ≤ |θ - θ'| := by
      have h := Real.lipschitzWith_sin.dist_le_mul θ θ'
      simpa [Real.dist_eq] using h
    have hsum : |Real.sin θ + Real.sin θ'| ≤ 2 := by
      calc |Real.sin θ + Real.sin θ'| ≤ |Real.sin θ| + |Real.sin θ'| := abs_add_le _ _
        _ ≤ 1 + 1 := add_le_add (abs_le.mpr ⟨Real.neg_one_le_sin θ, Real.sin_le_one θ⟩)
              (abs_le.mpr ⟨Real.neg_one_le_sin θ', Real.sin_le_one θ'⟩)
        _ = 2 := by norm_num
    rw [show Real.sin θ ^ 2 - Real.sin θ' ^ 2
        = (Real.sin θ - Real.sin θ') * (Real.sin θ + Real.sin θ') by ring, abs_mul]
    calc |Real.sin θ - Real.sin θ'| * |Real.sin θ + Real.sin θ'| ≤ |θ - θ'| * 2 :=
          mul_le_mul hs hsum (abs_nonneg _) (abs_nonneg _)
      _ = 2 * |θ - θ'| := by ring
  calc |(Real.cos (2 * θ) - Real.sin θ ^ 2) - (Real.cos (2 * θ') - Real.sin θ' ^ 2)|
      = |(Real.cos (2 * θ) - Real.cos (2 * θ')) + -(Real.sin θ ^ 2 - Real.sin θ' ^ 2)| := by
        congr 1; ring
    _ ≤ |Real.cos (2 * θ) - Real.cos (2 * θ')| + |-(Real.sin θ ^ 2 - Real.sin θ' ^ 2)| :=
        abs_add_le _ _
    _ = |Real.cos (2 * θ) - Real.cos (2 * θ')| + |Real.sin θ ^ 2 - Real.sin θ' ^ 2| := by
        rw [abs_neg]
    _ ≤ 2 * |θ - θ'| + 2 * |θ - θ'| := add_le_add hcos hsin
    _ = 4 * |θ - θ'| := by ring

/-- **The angular coefficient `c₂` is a `Jet`** with constant `4`: it is bounded by `2` and
`4`-Lipschitz, and a bounded Lipschitz function is `α`-Hölder for `0 < α ≤ 1`. -/
theorem jN0_c2m {α S : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    Work.FTS.Regularity.Jet α S 4 (fun _ θ _ => Work.Construction.c2m θ) := by
  refine ⟨by norm_num, ?_, ?_⟩
  · intro z θ τ hz hθ hτ
    exact le_trans (jN0_c2m_abs θ) (by norm_num)
  · intro z z' θ θ' τ τ' hz hz' hθ hθ' hτ hτ'
    set d := |z - z'| + |θ - θ'| + |τ - τ'| with hd
    have hd0 : 0 ≤ d := by rw [hd]; positivity
    have h2 : |Work.Construction.c2m θ - Work.Construction.c2m θ'| ≤ 4 := by
      rw [sub_eq_add_neg]
      calc |Work.Construction.c2m θ + -Work.Construction.c2m θ'|
          ≤ |Work.Construction.c2m θ| + |-Work.Construction.c2m θ'| := abs_add_le _ _
        _ = |Work.Construction.c2m θ| + |Work.Construction.c2m θ'| := by rw [abs_neg]
        _ ≤ 2 + 2 := add_le_add (jN0_c2m_abs θ) (jN0_c2m_abs θ')
        _ = 4 := by norm_num
    rcases le_or_gt d 1 with hdle | hdgt
    · have hself : d ≤ d ^ α := Work.FTS.Regularity.self_le_rpow_of_le_one hα hα1 hd0 hdle
      have hθd : |θ - θ'| ≤ d := by rw [hd]; linarith [abs_nonneg (z - z'), abs_nonneg (τ - τ')]
      have h1 := jN0_c2m_lip θ θ'
      have h3 : (4:ℝ) * |θ - θ'| ≤ 4 * d := by linarith [abs_nonneg (θ - θ')]
      have h4 : (4:ℝ) * d ≤ 4 * d ^ α := by linarith [hself]
      linarith
    · have hone : (1:ℝ) ≤ d ^ α := Real.one_le_rpow hdgt.le hα.le
      linarith

theorem jet_N0 {α S : ℝ} {g : ℝ → ℝ → ℝ → ℝ} {N₁ N₂ N₃ N₄ N₅ N₆ N₇ : ℝ}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3) (hS : 0 < S)
    (hF : Work.FTS.Regularity.Jet α S N₁ (fun z θ τ => Work.Construction.Ftau
      (Work.FTS.Regularity.pExp α) g τ z θ))
    (hDthF : Work.FTS.Regularity.Jet α S N₂ (fun z θ τ => Work.Spaces.Dth
      (fun z θ => Work.Construction.Ftau (Work.FTS.Regularity.pExp α) g τ z θ) z θ))
    (hDzF : Work.FTS.Regularity.Jet α S N₃ (fun z θ τ => Work.Spaces.Dz
      (fun z θ => Work.Construction.Ftau (Work.FTS.Regularity.pExp α) g τ z θ) z θ))
    (hDzg : Work.FTS.Regularity.Jet α S N₃ (fun z θ τ => Work.Spaces.Dz
      (fun z θ => g z θ τ) z θ))
    (hL12g : Work.FTS.Regularity.Jet α S N₄ (fun z θ τ => Work.Coercivity.L12f
      (Work.FTS.Regularity.gSlice g τ) z))
    (hL12Fstar : Work.FTS.Regularity.Jet α S N₅ (fun z θ τ => Work.Coercivity.L12f
      (fun z θ => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ) z))
    (hDthFstar : Work.FTS.Regularity.Jet α S N₆ (fun z θ τ => Work.Spaces.Dth
      (fun z θ => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ) z θ))
    (hDzFstar : Work.FTS.Regularity.Jet α S N₇ (fun z θ τ => Work.Spaces.Dz
      (fun z θ => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ) z θ)) :
    ∃ Nc : ℝ, Work.FTS.Regularity.Jet α S Nc
      (fun z θ τ => Work.Construction.N0 (Work.FTS.Regularity.pExp α)
        (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) g τ)
        (Work.FTS.Regularity.gSlice g τ) z θ) := by
  have hα1 : α ≤ 1 := by linarith
  -- the `Jet` of the explicit profile `F_* = Fstar (pExp α)` (constant `100`)
  have hFstJ : Work.FTS.Regularity.Jet α S 100
      (fun z θ _ => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ) := by
    refine ⟨by norm_num, ?_, ?_⟩
    · intro z θ τ hz hθ hτ
      have h1 : |Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ|
          ≤ 20 * Work.FTS.Regularity.Gamma α θ :=
        Work.FTS.Regularity.fstar_abs_le_gamma hα hα13 hz hθ
      have h2 : Work.FTS.Regularity.Gamma α θ ≤ 1 :=
        Work.ConstructionInstance.Gamma_le_one hα.le hθ
      have h3 : (0:ℝ) ≤ Work.FTS.Regularity.Gamma α θ :=
        Work.ConstructionInstance.Gamma_nonneg hθ
      linarith
    · intro z z' θ θ' τ τ' hz hz' hθ hθ' hτ hτ'
      have h1 := Work.FTS.Regularity.fstar_joint_modulus (α := α) hα hα13 hz hz' hθ hθ'
      refine le_trans h1 (mul_le_mul_of_nonneg_left ?_ (by norm_num : (0:ℝ) ≤ 100))
      refine Real.rpow_le_rpow (by positivity) ?_ hα.le
      linarith [abs_nonneg (τ - τ')]
  -- hence the `Jet` of the perturbation `g`: `g(τ) = F(τ) - F_*`
  have hgJ : Work.FTS.Regularity.Jet α S (N₁ + 100) (fun z θ τ => g z θ τ) := by
    refine Work.FTS.Regularity.Jet.congr
      (Work.FTS.Regularity.Jet.add hF (Work.FTS.Regularity.Jet.neg hFstJ)) ?_
    intro z θ τ hz hθ hτ
    simp only [Work.Construction.Ftau]
    ring
  -- the hypotheses, rewritten in the curried `Dth (·)` / `L₁₂(·)` forms of `N₀`
  have hL12FstJ : Work.FTS.Regularity.Jet α S N₅ (fun z θ τ =>
      Work.Construction.L12 (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) z) :=
    Work.FTS.Regularity.Jet.congr hL12Fstar (fun z θ τ _ _ _ => rfl)
  have hL12gJ : Work.FTS.Regularity.Jet α S N₄ (fun z θ τ =>
      Work.Construction.L12 (Work.FTS.Regularity.gSlice g τ) z) :=
    Work.FTS.Regularity.Jet.congr hL12g (fun z θ τ _ _ _ => rfl)
  have hDthFJ : Work.FTS.Regularity.Jet α S N₂ (fun z θ τ =>
      Work.Spaces.Dth (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) g τ) z θ) := hDthF
  have hDzFJ : Work.FTS.Regularity.Jet α S N₃ (fun z θ τ =>
      Work.Spaces.Dz (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) g τ) z θ) := hDzF
  have hDthFstJ : Work.FTS.Regularity.Jet α S N₆ (fun z θ τ =>
      Work.Spaces.Dth (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) z θ) := hDthFstar
  have hDzFstJ : Work.FTS.Regularity.Jet α S N₇ (fun z θ τ =>
      Work.Spaces.Dz (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) z θ) := hDzFstar
  have hDzgJ : Work.FTS.Regularity.Jet α S N₃ (fun z θ τ =>
      Work.Spaces.Dz (Work.FTS.Regularity.gSlice g τ) z θ) := hDzg
  have hC2mJ := jN0_c2m (S := S) hα hα1
  -- the six terms of `N₀`, with `sin(2θ)·∂_θ = D_θ`
  have hJ1 := jN0_const_mul (c := 3 / (2 * Work.FTS.Regularity.pExp α))
    (Work.FTS.Regularity.Jet.mul hL12FstJ hDthFstJ)
  have hJ2 := Work.FTS.Regularity.Jet.neg
    (Work.FTS.Regularity.Jet.mul hC2mJ (Work.FTS.Regularity.Jet.mul hL12FstJ hDzFstJ))
  have hJ3 := jN0_const_mul (c := 1 / Work.FTS.Regularity.pExp α)
    (Work.FTS.Regularity.Jet.mul hL12gJ hgJ)
  have hJ4 := jN0_const_mul (c := 3 / (2 * Work.FTS.Regularity.pExp α))
    (Work.FTS.Regularity.Jet.mul hL12gJ hDthFJ)
  have hJ5 := Work.FTS.Regularity.Jet.neg
    (Work.FTS.Regularity.Jet.mul hC2mJ (Work.FTS.Regularity.Jet.mul hL12gJ hDzFJ))
  have hJ6 := Work.FTS.Regularity.Jet.neg
    (Work.FTS.Regularity.Jet.mul hC2mJ (Work.FTS.Regularity.Jet.mul hL12FstJ hDzgJ))
  have hsum := Work.FTS.Regularity.Jet.add
    (Work.FTS.Regularity.Jet.add
      (Work.FTS.Regularity.Jet.add
        (Work.FTS.Regularity.Jet.add
          (Work.FTS.Regularity.Jet.add hJ1 hJ2) hJ3) hJ4) hJ5) hJ6
  refine ⟨_, Work.FTS.Regularity.Jet.congr hsum ?_⟩
  -- the pointwise identification of the six-term sum with `N₀`
  intro z θ τ hz hθ hτ
  simp only [Work.Construction.N0, Work.FTS.Regularity.gSlice, Work.Construction.s2_eq,
    Work.Spaces.Dth]
  ring

end Work.FTS.RegPkgGal.Der
