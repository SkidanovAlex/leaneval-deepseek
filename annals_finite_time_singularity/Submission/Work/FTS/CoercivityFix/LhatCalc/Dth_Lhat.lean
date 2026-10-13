/-
# `D_θ(𝓛̂ f) = 𝓛̂(D_θ f)`: the `D_θ`-commutator of the clean operator `𝓛̂`

The corrected coercivity operator of the fix of node N2
(`Submission/Work/FTS/CoercivityFix/Basic.lean`) is

  `Lhat f = 𝓛 f − Transport f`,
  `𝓛 f = f + D_z f − 2f/(1+z)`,
  `Transport f = 3 D_θ f/(1+z)`;

its mathematical point is that `D_θ` commutes with it *exactly*:

  **`D_θ(Lhat f) = Lhat(D_θ f)`**

with no commutator term, no nonlocal piece and no zero-mode hypothesis, on the interior class
`Work.FTS.LocData.SmoothQuad` (genuine `C^∞` on the open quadrant `z > -1`, `0 < θ < π/2`).

The proof is a direct computation with the chain rule.  The analytic inputs are

* `contDiffOn_uncurry_pz_sm`, `contDiffOn_uncurry_pth_sm`: the slice derivatives `∂_z`, `∂_θ`
  of a `SmoothQuad` datum are again `C^∞` on the quadrant.  These are the `smoothOrder`-analogues
  of `Work.Spaces.contDiffOn_uncurry_pz`/`_pth`, which are stated for the *analytic* order `⊤`
  and therefore do **not** apply to `SmoothQuad` (see the warning below);
* Clairaut/Schwarz for the two slice derivatives in the `C²` class
  (`Work.Spaces.pz_pth_comm`);
* `∂_θ 𝓛 g = ∂_θ g + z ∂_z∂_θ g − (2/(1+z))∂_θ g` (`pth_L_of_smooth`) and
  `∂_θ D_θ g = 2cos(2θ) ∂_θ g + sin(2θ) ∂_θ² g` (`pth_Dth_eq`), together with the
  hypothesis-free identities of `Submission/Work/Coercivity/dth_LGammaT_expansion.lean`
  (`pth_Transport`, `pz_Dth_val`).

**Warning (`smoothOrder` versus `⊤`).**  In Mathlib `ContDiffOn ℝ n` with `n = ⊤ : WithTop ℕ∞`
is the *analytic* order, whereas `Work.Stability.smoothOrder = ((⊤ : ℕ∞) : WithTop ℕ∞)` is the
genuine `C^∞` order in which `SmoothQuad` is stated.  Since `WithTop (WithTop ℕ)` has
`⊤ = none` while `smoothOrder = some none`, the two are *not* definitionally equal, and none of
the `⊤`-lemmas can be applied to a `SmoothQuad` datum.  Every statement below therefore uses
`Work.Stability.smoothOrder` explicitly.
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.CoercivityFix.Basic
import Submission.Work.Spaces.CurrySmooth
import Submission.Work.Spaces.mixed_comm
import Submission.Work.Coercivity.dth_LGammaT_expansion

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.LhatCalc

set_option autoImplicit false

namespace DthAux

/-! ## The open quadrant of `SmoothQuad`

`Work.FTS.LocData.SmoothQuad g = ContDiffOn ℝ smoothOrder (uncurry g) QuadL`, where
`QuadL = (-1,∞) × (0,π/2)`. -/

/-- The open quadrant on which `Work.FTS.LocData.SmoothQuad` is stated. -/
abbrev QuadL : Set (ℝ × ℝ) := Set.Ioi (-1) ×ˢ Set.Ioo (0 : ℝ) (π / 2)

theorem isOpen_QuadL : IsOpen QuadL := isOpen_Ioi.prod isOpen_Ioo

theorem mem_QuadL_iff {z θ : ℝ} : ((z, θ) ∈ QuadL) ↔ -1 < z ∧ 0 < θ ∧ θ < π / 2 := by
  rw [QuadL, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo]

/-- `SmoothQuad` is smoothness in the genuine order `smoothOrder` on `QuadL` (definitional). -/
theorem smoothQuad_iff (g : ℝ → ℝ → ℝ) :
    Work.FTS.LocData.SmoothQuad g
      ↔ ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry g) QuadL := Iff.rfl

theorem smoothQuad_contDiffOn {g : ℝ → ℝ → ℝ} (hg : Work.FTS.LocData.SmoothQuad g) :
    ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry g) QuadL := hg

theorem smoothOrder_ne_zero : Work.Stability.smoothOrder ≠ 0 := by
  simp [Work.Stability.smoothOrder]

theorem smoothOrder_add_one : Work.Stability.smoothOrder + 1 = Work.Stability.smoothOrder := rfl

/-! ## Differential calculus in the genuine smooth order

The two lemmas below are the `smoothOrder`-analogues of `Work.Spaces.contDiffOn_uncurry_pz` and
`Work.Spaces.contDiffOn_uncurry_pth`; a `SmoothQuad` datum is only `C^∞`, so the `⊤`-versions
do not apply to it.  The proofs are those of the `⊤`-versions with `⊤` replaced by
`smoothOrder` and `le_rfl` by `le_of_eq smoothOrder_add_one`. -/

theorem contDiffOn_uncurry_pz_sm {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry G) V) :
    ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry (Work.Spaces.pz G)) V := by
  have hchain : ∀ p ∈ V, Work.Spaces.pz G p.1 p.2
      = fderiv ℝ (Function.uncurry G) p (1, 0) := by
    intro p hp
    exact Work.Spaces.pz_eq_fderiv
      ((h.differentiableOn (n := Work.Stability.smoothOrder) smoothOrder_ne_zero).differentiableAt
        (hV.mem_nhds hp))
  have hfd : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun (p : ℝ × ℝ) => fderiv ℝ (Function.uncurry G) p) V := by
    have h' := h.fderivWithin (m := Work.Stability.smoothOrder) hV.uniqueDiffOn
      (le_of_eq smoothOrder_add_one)
    refine h'.congr ?_
    intro p hp
    rw [fderivWithin_of_isOpen hV hp]
  have hcomp : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun (p : ℝ × ℝ) => (fderiv ℝ (Function.uncurry G) p) (1, 0)) V := by
    simpa using hfd.clm_apply contDiffOn_const
  exact hcomp.congr hchain

theorem contDiffOn_uncurry_pth_sm {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry G) V) :
    ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry (Work.Spaces.pth G)) V := by
  have hchain : ∀ p ∈ V, Work.Spaces.pth G p.1 p.2
      = fderiv ℝ (Function.uncurry G) p (0, 1) := by
    intro p hp
    exact Work.Spaces.pth_eq_fderiv
      ((h.differentiableOn (n := Work.Stability.smoothOrder) smoothOrder_ne_zero).differentiableAt
        (hV.mem_nhds hp))
  have hfd : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun (p : ℝ × ℝ) => fderiv ℝ (Function.uncurry G) p) V := by
    have h' := h.fderivWithin (m := Work.Stability.smoothOrder) hV.uniqueDiffOn
      (le_of_eq smoothOrder_add_one)
    refine h'.congr ?_
    intro p hp
    rw [fderivWithin_of_isOpen hV hp]
  have hcomp : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun (p : ℝ × ℝ) => (fderiv ℝ (Function.uncurry G) p) (0, 1)) V := by
    simpa using hfd.clm_apply contDiffOn_const
  exact hcomp.congr hchain

/-! ## Two `θ`-derivative computations -/

/-- **The `θ`-derivative of `𝓛`**: at an interior point of the quadrant, where `g` is `C^∞`,
`∂_θ(𝓛 g) = ∂_θ g + z ∂_z∂_θ g − (2/(1+z)) ∂_θ g`.  (The `⊤`-version is
`Work.Coercivity.pth_L`; here the class is `SmoothQuad`, i.e. the genuine smooth order.) -/
theorem pth_L_of_smooth {g : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (hcd : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry g) V) {z θ : ℝ}
    (hy : (z, θ) ∈ V) :
    Work.Spaces.pth (Work.Coercivity.L g) z θ
      = Work.Spaces.pth g z θ + z * Work.Spaces.pz (Work.Spaces.pth g) z θ
        - (2 / (1 + z)) * Work.Spaces.pth g z θ := by
  have hcf : ContDiffAt ℝ Work.Stability.smoothOrder (Function.uncurry g) (z, θ) :=
    hcd.contDiffAt (hV.mem_nhds hy)
  have hcd2 : ContDiffAt ℝ 2 (Function.uncurry g) (z, θ) :=
    hcf.of_le (by simp [Work.Stability.smoothOrder])
  have hgθ : DifferentiableAt ℝ (fun θ' => g z θ') θ :=
    Work.Spaces.differentiableAt_curry_right (hcf.differentiableAt smoothOrder_ne_zero)
  have hpz_sm : ContDiffOn ℝ Work.Stability.smoothOrder
      (Function.uncurry (Work.Spaces.pz g)) V :=
    contDiffOn_uncurry_pz_sm hV hcd
  have hpzθ : DifferentiableAt ℝ (fun θ' => Work.Spaces.pz g z θ') θ :=
    Work.Spaces.differentiableAt_curry_right
      ((hpz_sm.contDiffAt (hV.mem_nhds hy)).differentiableAt smoothOrder_ne_zero)
  have e : (fun θ' => Work.Coercivity.L g z θ')
      = (fun θ' => g z θ' + z * Work.Spaces.pz g z θ' - (2 / (1 + z)) * g z θ') := by
    funext θ'; simp only [Work.Coercivity.L, Work.Spaces.Dz]; ring
  show deriv (fun θ' => Work.Coercivity.L g z θ') θ = _
  rw [e]
  rw [show (fun θ' : ℝ => g z θ' + z * Work.Spaces.pz g z θ' - (2 / (1 + z)) * g z θ')
      = (((fun θ' : ℝ => g z θ') + (fun θ' : ℝ => z * Work.Spaces.pz g z θ'))
          - (fun θ' : ℝ => (2 / (1 + z)) * g z θ')) from rfl]
  rw [deriv_sub (hgθ.add (hpzθ.const_mul z)) (hgθ.const_mul (2 / (1 + z)))]
  rw [deriv_add hgθ (hpzθ.const_mul z)]
  rw [deriv_const_mul_field, deriv_const_mul_field]
  rw [show deriv (fun θ' => g z θ') θ = Work.Spaces.pth g z θ from rfl,
      show deriv (fun θ' => Work.Spaces.pz g z θ') θ
        = Work.Spaces.pth (Work.Spaces.pz g) z θ from rfl,
      ← Work.Spaces.pz_pth_comm hcd2]

/-- `deriv (fun θ' => sin (2θ')) θ = 2 cos (2θ)`. -/
theorem hasDerivAt_sin_two (θ : ℝ) :
    HasDerivAt (fun θ' : ℝ => Real.sin (2 * θ')) (2 * Real.cos (2 * θ)) θ := by
  have h2 : HasDerivAt (fun θ' : ℝ => 2 * θ') 2 θ := by
    simpa using (hasDerivAt_id θ).const_mul (2 : ℝ)
  have h := (Real.hasDerivAt_sin (2 * θ)).comp θ h2
  simpa [Function.comp_def, mul_comm] using h

/-- **The `θ`-derivative of `D_θ g`**: `∂_θ D_θ g = 2cos(2θ) ∂_θ g + sin(2θ) ∂_θ² g`, as soon
as the `θ`-slice of `∂_θ g` is differentiable at `θ`. -/
theorem pth_Dth_eq {g : ℝ → ℝ → ℝ} {z θ : ℝ}
    (h : DifferentiableAt ℝ (fun θ' => Work.Spaces.pth g z θ') θ) :
    Work.Spaces.pth (Work.Spaces.Dth g) z θ
      = 2 * Real.cos (2 * θ) * Work.Spaces.pth g z θ
        + Real.sin (2 * θ) * Work.Spaces.pth (Work.Spaces.pth g) z θ := by
  have h2 : HasDerivAt (fun θ' : ℝ => Real.sin (2 * θ') * Work.Spaces.pth g z θ')
      (2 * Real.cos (2 * θ) * Work.Spaces.pth g z θ
        + Real.sin (2 * θ) * Work.Spaces.pth (Work.Spaces.pth g) z θ) θ :=
    (hasDerivAt_sin_two θ).mul h.hasDerivAt
  show deriv (fun θ' => Work.Spaces.Dth g z θ') θ = _
  rw [show (fun θ' => Work.Spaces.Dth g z θ')
      = (fun θ' => Real.sin (2 * θ') * Work.Spaces.pth g z θ') from by
    funext θ'; simp only [Work.Spaces.Dth]]
  exact h2.deriv

end DthAux

open DthAux

/-! ## The `D_θ`-commutator of `𝓛̂` -/

/-- **`D_θ` commutes exactly with `𝓛̂ = 𝓛 − Transport`**:
`D_θ(𝓛̂ f) = 𝓛̂(D_θ f)` for every `C^∞` datum on the open quadrant.  There is no commutator
term, no nonlocal contribution and no zero-mode hypothesis. -/
theorem Dth_Lhat {f : ℝ → ℝ → ℝ} (hf : Work.FTS.LocData.SmoothQuad f) {z θ : ℝ}
    (hz : 0 < z) (hθ : 0 < θ) (hθ2 : θ < Real.pi / 2) :
    Work.Spaces.Dth (Work.FTS.CoercivityFix.Lhat f) z θ
      = Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dth f) z θ := by
  have hlt : -1 < z := by linarith
  have hmem : (z, θ) ∈ QuadL := mem_QuadL_iff.mpr ⟨hlt, hθ, hθ2⟩
  have hcd : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry f) QuadL := hf
  have hcf : ContDiffAt ℝ Work.Stability.smoothOrder (Function.uncurry f) (z, θ) :=
    hcd.contDiffAt (isOpen_QuadL.mem_nhds hmem)
  have hfθ : DifferentiableAt ℝ (fun θ' => f z θ') θ :=
    Work.Spaces.differentiableAt_curry_right (hcf.differentiableAt smoothOrder_ne_zero)
  have hpz_sm : ContDiffOn ℝ Work.Stability.smoothOrder
      (Function.uncurry (Work.Spaces.pz f)) QuadL := contDiffOn_uncurry_pz_sm isOpen_QuadL hcd
  have hpzθ : DifferentiableAt ℝ (fun θ' => Work.Spaces.pz f z θ') θ :=
    Work.Spaces.differentiableAt_curry_right
      ((hpz_sm.contDiffAt (isOpen_QuadL.mem_nhds hmem)).differentiableAt smoothOrder_ne_zero)
  have hpth_sm : ContDiffOn ℝ Work.Stability.smoothOrder
      (Function.uncurry (Work.Spaces.pth f)) QuadL := contDiffOn_uncurry_pth_sm isOpen_QuadL hcd
  have hpthθ : DifferentiableAt ℝ (fun θ' => Work.Spaces.pth f z θ') θ :=
    Work.Spaces.differentiableAt_curry_right
      ((hpth_sm.contDiffAt (isOpen_QuadL.mem_nhds hmem)).differentiableAt smoothOrder_ne_zero)
  have dL : DifferentiableAt ℝ (fun θ' => Work.Coercivity.L f z θ') θ := by
    rw [show (fun θ' => Work.Coercivity.L f z θ')
        = (fun θ' => f z θ' + z * Work.Spaces.pz f z θ' - (2 / (1 + z)) * f z θ') from by
      funext θ'; simp only [Work.Coercivity.L, Work.Spaces.Dz]; ring]
    exact (hfθ.add (hpzθ.const_mul z)).sub (hfθ.const_mul (2 / (1 + z)))
  have hDθ : DifferentiableAt ℝ (fun θ' => Work.Spaces.Dth f z θ') θ := by
    rw [show (fun θ' => Work.Spaces.Dth f z θ')
        = (fun θ' => Real.sin (2 * θ') * Work.Spaces.pth f z θ') from by
      funext θ'; simp only [Work.Spaces.Dth]]
    exact ((hasDerivAt_sin_two θ).differentiableAt).mul hpthθ
  have dTr : DifferentiableAt ℝ (fun θ' => Work.Coercivity.Transport f z θ') θ := by
    rw [show (fun θ' => Work.Coercivity.Transport f z θ')
        = (fun θ' => (3 / (1 + z)) * Work.Spaces.Dth f z θ') from by
      funext θ'; simp only [Work.Coercivity.Transport]; ring]
    exact hDθ.const_mul (3 / (1 + z))
  have hpth : Work.Spaces.pth (Work.FTS.CoercivityFix.Lhat f) z θ
      = Work.Spaces.pth (Work.Coercivity.L f) z θ
        - Work.Spaces.pth (Work.Coercivity.Transport f) z θ := by
    show deriv (fun θ' => Work.FTS.CoercivityFix.Lhat f z θ') θ = _
    rw [show (fun θ' => Work.FTS.CoercivityFix.Lhat f z θ')
        = ((fun θ' => Work.Coercivity.L f z θ')
            - fun θ' => Work.Coercivity.Transport f z θ') from by
      funext θ'; simp only [Work.FTS.CoercivityFix.Lhat, Pi.sub_apply]]
    rw [deriv_sub dL dTr]
    rfl
  rw [show Work.Spaces.Dth (Work.FTS.CoercivityFix.Lhat f) z θ
      = Real.sin (2 * θ) * Work.Spaces.pth (Work.FTS.CoercivityFix.Lhat f) z θ from rfl]
  rw [hpth]
  rw [Work.FTS.CoercivityFix.Lhat_eq (Work.Spaces.Dth f) z θ]
  rw [pth_L_of_smooth isOpen_QuadL hcd hmem, Work.Coercivity.pth_Transport]
  rw [show Work.Spaces.Dz (Work.Spaces.Dth f) z θ
      = z * Work.Spaces.pz (Work.Spaces.Dth f) z θ from rfl]
  rw [Work.Coercivity.pz_Dth_val]
  rw [show Work.Spaces.Dth (Work.Spaces.Dth f) z θ
      = Real.sin (2 * θ) * Work.Spaces.pth (Work.Spaces.Dth f) z θ from rfl]
  rw [show Work.Spaces.Dth f z θ = Real.sin (2 * θ) * Work.Spaces.pth f z θ from rfl]
  rw [pth_Dth_eq (g := f) hpthθ]
  ring

end Work.FTS.CoercivityFix.LhatCalc

end
