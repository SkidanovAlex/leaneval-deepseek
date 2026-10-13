import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.RegPkgGal.Der.Defs
import Submission.Work.FTS.RegPkgGal.Der.jet_N0
import Submission.Work.FTS.RegPkgGal.Der.zderiv_N
import Submission.Work.Construction.Defs
import Submission.Work.FTS.Regularity.gammaFstarModuli
import Submission.Work.FTS.Regularity.fstarDzUniform

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS.RegPkgGal.Der.zderiv_N0`

The `z`-derivative bound for the quadratic term `N₀` of the fake-time equation.  The statement is

  `∃ Nc, C1Jet α S Nc (fun z θ τ => N0 (pExp α) (Ftau (pExp α) g τ) (gSlice g τ) z θ)`,

i.e. the composite of the six summands of `N₀` is *jointly* `α`-Hölder with a uniform value bound
(the `Jet` half, which is `Der.jet_N0`) **and** has `z`-slices differentiable on `z > 0` with a
uniform derivative bound.

The two halves are produced by the same calculus: `C1Jet α S N h` bundles a `Jet α S N h` and the
`z`-differentiability bound with the *same* constant `N`.  The closure of `C1Jet` under
`neg`/`add`/`mul`/`const_mul`/`congr` is `Work.FTS.RegPkgGal.C1Jet.*`, proved in the sibling module
`Submission.Work.FTS.RegPkgGal.Der.zderiv_N`; this file uses it and assembles `N₀` from its six
summands.

The one input that is not a hypothesis of the statement is the static profile `F_* = Fstar (pExp α)`
itself: it enters through the perturbation `g(τ) = F(τ) - F_*` (third summand) and through the
constants `L₁₂(F_*)`, `∂_θF_*`, `D_zF_*`.  Its `C1Jet`-data is `c1JetFstar_aux` below (value bound
from `fstar_abs_le_gamma`/`Gamma ≤ 1`, modulus from `fstar_joint_modulus`, `z`-derivative from
`deriv_fstar_z` + `fstarDz_abs_le`).
-/

noncomputable section

set_option autoImplicit false

namespace Work.FTS.RegPkgGal.Der

/-! ## The static profile as a `C1Jet` -/

/-- **The static profile `F_* = Fstar (pExp α)` is a `C1Jet`** with constant `100 + 20·pExp α`:
the value bound `|F_*| ≤ 20Γ ≤ 20 ≤ 100` (`fstar_abs_le_gamma`, `Gamma_le_one`), the joint modulus
`fstar_joint_modulus` (constant `100`, and `F_*` does not depend on `τ`), and the explicit
`z`-derivative `deriv_fstar_z` bounded by `20·pExp α` (`fstarDz_abs_le`). -/
theorem c1JetFstar_aux {α S : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3) :
    Work.FTS.RegPkgGal.C1Jet α S (100 + 20 * Work.FTS.Regularity.pExp α)
      (fun z θ _ => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ) := by
  have hp0 : 0 < Work.FTS.Regularity.pExp α := Work.FTS.Regularity.pExp_pos hα
  have hN0 : 0 ≤ 100 + 20 * Work.FTS.Regularity.pExp α := by linarith
  refine ⟨⟨hN0, ?_, ?_⟩, ?_⟩
  · intro z θ τ hz hθ _
    have h1 := Work.FTS.Regularity.fstar_abs_le_gamma hα hα13 (z := z) (θ := θ) hz hθ
    have hG1 : Work.FTS.Regularity.Gamma α θ ≤ 1 :=
      Work.ConstructionInstance.Gamma_le_one hα.le hθ
    calc |Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ|
        ≤ 20 * Work.FTS.Regularity.Gamma α θ := h1
      _ ≤ 20 * 1 := mul_le_mul_of_nonneg_left hG1 (by norm_num)
      _ ≤ 100 + 20 * Work.FTS.Regularity.pExp α := by linarith
  · intro z z' θ θ' τ τ' hz hz' hθ hθ' hτ hτ'
    have h1 := Work.FTS.Regularity.fstar_joint_modulus hα hα13 hz hz' hθ hθ'
    have h2 : (|z - z'| + |θ - θ'|) ^ α ≤ (|z - z'| + |θ - θ'| + |τ - τ'|) ^ α :=
      Real.rpow_le_rpow (by positivity) (by linarith [abs_nonneg (τ - τ')]) hα.le
    calc |Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ
            - Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z' θ'|
        ≤ 100 * (|z - z'| + |θ - θ'|) ^ α := h1
      _ ≤ 100 * (|z - z'| + |θ - θ'| + |τ - τ'|) ^ α := mul_le_mul_of_nonneg_left h2 (by norm_num)
      _ ≤ (100 + 20 * Work.FTS.Regularity.pExp α)
            * (|z - z'| + |θ - θ'| + |τ - τ'|) ^ α :=
          mul_le_mul_of_nonneg_right (by linarith)
            (Real.rpow_nonneg (by positivity) α)
  · intro τ hτ θ hθ z hz
    have hzp : 0 < z := hz
    have hz1 : -1 < z := by linarith
    refine ⟨deriv (fun z' => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z' θ) z, ?_, ?_⟩
    · have hdiff : DifferentiableAt ℝ
          (fun z' => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z' θ) z := by
        have hfun : (fun z' => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z' θ)
            = fun z' => (Work.FTS.Regularity.pExp α * (Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ
                / Work.Spaces.c (Work.FTS.Regularity.pExp α))) * Work.FM.Fstar z' := by
          funext z'
          rw [Work.Construction.Fstar]
        rw [hfun]
        exact ((Work.FM.hasDerivAt_Fstar z hz1).const_mul _).differentiableAt
      exact hdiff.hasDerivAt
    · rw [Work.FTS.Regularity.deriv_fstar_z]
      exact le_trans (Work.FTS.Regularity.fstarDz_abs_le hα hα13 hzp.le hθ)
        (by linarith)

/-! ## The angular coefficient `c₂` as a `C1Jet` -/

/-- `θ ↦ c₂(θ) = cos 2θ - sin²θ` is a `C1Jet` with constant `4`: its `Jet` is `jN0_c2m` and its
`z`-slices are constant. -/
theorem c1JetC2m_aux {α S : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    Work.FTS.RegPkgGal.C1Jet α S 4 (fun z θ _ => Work.Construction.c2m θ) := by
  refine ⟨jN0_c2m (S := S) hα hα1, ?_⟩
  intro τ hτ θ hθ z hz
  exact ⟨0, by simpa using hasDerivAt_const (x := z) (c := Work.Construction.c2m θ),
    by norm_num⟩

theorem zderiv_N0 {α S : ℝ} {g : ℝ → ℝ → ℝ → ℝ} {N₁ N₂ N₃ N₄ N₅ N₆ N₇ : ℝ}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3) (hS : 0 < S)
    (hF : Work.FTS.RegPkgGal.C1Jet α S N₁ (fun z θ τ => Work.Construction.Ftau
      (Work.FTS.Regularity.pExp α) g τ z θ))
    (hDthF : Work.FTS.RegPkgGal.C1Jet α S N₂ (fun z θ τ => Work.Spaces.Dth
      (fun z θ => Work.Construction.Ftau (Work.FTS.Regularity.pExp α) g τ z θ) z θ))
    (hDzF : Work.FTS.RegPkgGal.C1Jet α S N₃ (fun z θ τ => Work.Spaces.Dz
      (fun z θ => Work.Construction.Ftau (Work.FTS.Regularity.pExp α) g τ z θ) z θ))
    (hDzg : Work.FTS.RegPkgGal.C1Jet α S N₃ (fun z θ τ => Work.Spaces.Dz
      (fun z θ => g z θ τ) z θ))
    (hL12g : Work.FTS.RegPkgGal.C1Jet α S N₄ (fun z θ τ => Work.Coercivity.L12f
      (Work.FTS.Regularity.gSlice g τ) z))
    (hL12Fstar : Work.FTS.RegPkgGal.C1Jet α S N₅ (fun z θ τ => Work.Coercivity.L12f
      (fun z θ => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ) z))
    (hDthFstar : Work.FTS.RegPkgGal.C1Jet α S N₆ (fun z θ τ => Work.Spaces.Dth
      (fun z θ => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ) z θ))
    (hDzFstar : Work.FTS.RegPkgGal.C1Jet α S N₇ (fun z θ τ => Work.Spaces.Dz
      (fun z θ => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ) z θ)) :
    ∃ Nc : ℝ, Work.FTS.RegPkgGal.C1Jet α S Nc
      (fun z θ τ => Work.Construction.N0 (Work.FTS.Regularity.pExp α)
        (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) g τ)
        (Work.FTS.Regularity.gSlice g τ) z θ) := by
  have hα1 : α ≤ 1 := by linarith
  -- the static profile and the perturbation `g = F(τ) - F_*`
  have hFst : Work.FTS.RegPkgGal.C1Jet α S (100 + 20 * Work.FTS.Regularity.pExp α)
      (fun z θ _ => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ) :=
    c1JetFstar_aux hα hα13
  have hgs : Work.FTS.RegPkgGal.C1Jet α S (N₁ + (100 + 20 * Work.FTS.Regularity.pExp α))
      (fun z θ τ => g z θ τ) := by
    refine Work.FTS.RegPkgGal.C1Jet.congr
      (Work.FTS.RegPkgGal.C1Jet.add hF (Work.FTS.RegPkgGal.C1Jet.neg hFst)) ?_
    intro z θ τ hz hθ hτ
    simp only [Work.Construction.Ftau]
    ring
  have hc2 : Work.FTS.RegPkgGal.C1Jet α S 4 (fun z θ _ => Work.Construction.c2m θ) :=
    c1JetC2m_aux hα hα1
  -- the eight `C1Jet` slots, in the normalised form used by `N₀`
  have hL12Fst : Work.FTS.RegPkgGal.C1Jet α S N₅ (fun z θ _ =>
      Work.Coercivity.L12f (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) z) := hL12Fstar
  have hDthFst : Work.FTS.RegPkgGal.C1Jet α S N₆ (fun z θ _ =>
      Work.Spaces.Dth (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) z θ) := hDthFstar
  have hDzFst : Work.FTS.RegPkgGal.C1Jet α S N₇ (fun z θ _ =>
      Work.Spaces.Dz (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) z θ) := hDzFstar
  have hL12gs : Work.FTS.RegPkgGal.C1Jet α S N₄ (fun z θ τ =>
      Work.Coercivity.L12f (Work.FTS.Regularity.gSlice g τ) z) := hL12g
  have hDthF' : Work.FTS.RegPkgGal.C1Jet α S N₂ (fun z θ τ =>
      Work.Spaces.Dth (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) g τ) z θ) := hDthF
  have hDzF' : Work.FTS.RegPkgGal.C1Jet α S N₃ (fun z θ τ =>
      Work.Spaces.Dz (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) g τ) z θ) := hDzF
  have hDzgs : Work.FTS.RegPkgGal.C1Jet α S N₃ (fun z θ τ =>
      Work.Spaces.Dz (Work.FTS.Regularity.gSlice g τ) z θ) := hDzg
  -- the six summands of `N₀`
  have hT1 : Work.FTS.RegPkgGal.C1Jet α S _ (fun z θ τ =>
      (3 / (2 * Work.FTS.Regularity.pExp α)) * (Work.Coercivity.L12f
        (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) z
        * Work.Spaces.Dth (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) z θ)) :=
    Work.FTS.RegPkgGal.C1Jet.const_mul (c := 3 / (2 * Work.FTS.Regularity.pExp α))
      (Work.FTS.RegPkgGal.C1Jet.mul hL12Fst hDthFst)
  have hT2 : Work.FTS.RegPkgGal.C1Jet α S _ (fun z θ τ =>
      -(Work.Construction.c2m θ * (Work.Coercivity.L12f
        (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) z
        * Work.Spaces.Dz (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) z θ))) :=
    Work.FTS.RegPkgGal.C1Jet.neg (Work.FTS.RegPkgGal.C1Jet.mul hc2
      (Work.FTS.RegPkgGal.C1Jet.mul hL12Fst hDzFst))
  have hT3 : Work.FTS.RegPkgGal.C1Jet α S _ (fun z θ τ =>
      (1 / Work.FTS.Regularity.pExp α) * (Work.Coercivity.L12f
        (Work.FTS.Regularity.gSlice g τ) z * g z θ τ)) :=
    Work.FTS.RegPkgGal.C1Jet.const_mul (c := 1 / Work.FTS.Regularity.pExp α)
      (Work.FTS.RegPkgGal.C1Jet.mul hL12gs hgs)
  have hT4 : Work.FTS.RegPkgGal.C1Jet α S _ (fun z θ τ =>
      (3 / (2 * Work.FTS.Regularity.pExp α)) * (Work.Coercivity.L12f
        (Work.FTS.Regularity.gSlice g τ) z
        * Work.Spaces.Dth (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) g τ) z θ)) :=
    Work.FTS.RegPkgGal.C1Jet.const_mul (c := 3 / (2 * Work.FTS.Regularity.pExp α))
      (Work.FTS.RegPkgGal.C1Jet.mul hL12gs hDthF')
  have hT5 : Work.FTS.RegPkgGal.C1Jet α S _ (fun z θ τ =>
      -(Work.Construction.c2m θ * (Work.Coercivity.L12f
        (Work.FTS.Regularity.gSlice g τ) z
        * Work.Spaces.Dz (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) g τ) z θ))) :=
    Work.FTS.RegPkgGal.C1Jet.neg (Work.FTS.RegPkgGal.C1Jet.mul hc2
      (Work.FTS.RegPkgGal.C1Jet.mul hL12gs hDzF'))
  have hT6 : Work.FTS.RegPkgGal.C1Jet α S _ (fun z θ τ =>
      -(Work.Construction.c2m θ * (Work.Coercivity.L12f
        (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) z
        * Work.Spaces.Dz (Work.FTS.Regularity.gSlice g τ) z θ))) :=
    Work.FTS.RegPkgGal.C1Jet.neg (Work.FTS.RegPkgGal.C1Jet.mul hc2
      (Work.FTS.RegPkgGal.C1Jet.mul hL12Fst hDzgs))
  refine ⟨_, Work.FTS.RegPkgGal.C1Jet.congr
    (Work.FTS.RegPkgGal.C1Jet.add (Work.FTS.RegPkgGal.C1Jet.add
      (Work.FTS.RegPkgGal.C1Jet.add (Work.FTS.RegPkgGal.C1Jet.add
        (Work.FTS.RegPkgGal.C1Jet.add hT1 hT2) hT3) hT4) hT5) hT6) ?_⟩
  intro z θ τ hz hθ hτ
  simp only [Work.Construction.N0, Work.Construction.L12, Work.Coercivity.L12f,
    Work.Spaces.Dth, Work.Construction.s2, Work.FTS.Regularity.gSlice]
  ring

end Work.FTS.RegPkgGal.Der
