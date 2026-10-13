/-
# Congruence of the concrete inner products on the open quadrant

The concrete inner products of this chapter are sums of `wip`-pairings
`wip ρ A B = ∫_{z ∈ [0,∞)} ∫_{θ ∈ [0,π/2]} A z θ · B z θ · ρ z θ` (iterated Bochner
integrals), so they see the first argument only through its values almost everywhere.  The
open quadrant `Qd = (0,∞) × (0,π/2)` is co-null in `Iz × Iθ` *and open*, so an equality on
`Qd` propagates to **every** slot `D_z^j D_θ^i` (derivatives are local) and hence to the
pairings — **with no membership, measurability or integrability hypothesis at all**.

This is the ingredient that lets the corrected step of `NOTES.md` §6 avoid the class-depth
obstruction: the congruence `IP_m x y = IP_m x' y` for `x = x'` on `Qd` needs no `RegQ`
membership, unlike the `congr_qd` fields of the frozen `UnifIP` (which carry one for the
abstract inner product).

Source of the method: the delivered `Submission/Work/FTS/CoercivityStep/Base/H1IP_congr_qd.lean`
(whose three `HkReg` hypotheses its own docstring already declares unnecessary).
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.CoercivityFix.Basic
import Submission.Work.Coercivity.Defs
import Submission.Work.Coercivity.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.StepAssembly

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-- The iterated integral over `Iz × Iθ` equals the iterated integral over the open quadrant
`(0,∞) × (0,π/2)`: the difference is a null set, and both components are Bochner integrals. -/
lemma wip_eq_Ioi_Ioo (F : ℝ → ℝ → ℝ) :
    (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, F z θ)
      = ∫ z in Set.Ioi (0 : ℝ), ∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), F z θ := by
  have h1 : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, F z θ)
      = ∫ z in Work.Spaces.Iz, ∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), F z θ := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici (fun z _ => ?_)
    exact MeasureTheory.integral_Icc_eq_integral_Ioo
  rw [h1]
  exact MeasureTheory.integral_Ici_eq_integral_Ioi

/-- **Congruence of `wip` in its first argument on the open quadrant**, with no hypotheses. -/
lemma wip_congr_Qd {ρ A A' B : ℝ → ℝ → ℝ}
    (h : ∀ z θ, (z, θ) ∈ Work.Construction.Qd → A z θ = A' z θ) :
    Work.Coercivity.wip ρ A B = Work.Coercivity.wip ρ A' B := by
  simp only [Work.Coercivity.wip]
  rw [wip_eq_Ioi_Ioo (fun z θ => A z θ * B z θ * ρ z θ),
    wip_eq_Ioi_Ioo (fun z θ => A' z θ * B z θ * ρ z θ)]
  refine MeasureTheory.setIntegral_congr_fun
    (isOpen_Ioi (a := (0 : ℝ))).measurableSet (fun z hz => ?_)
  refine MeasureTheory.setIntegral_congr_fun
    (isOpen_Ioo (a := (0 : ℝ)) (b := Real.pi / 2)).measurableSet (fun θ hθ => ?_)
  rw [h z θ ⟨hz, hθ⟩]

/-- `D_z` preserves equality on the open quadrant (derivatives are local and `Qd` is open). -/
lemma Dz_congr_Qd {f f' : ℝ → ℝ → ℝ}
    (h : ∀ z θ, (z, θ) ∈ Work.Construction.Qd → f z θ = f' z θ) :
    ∀ z θ, (z, θ) ∈ Work.Construction.Qd → Work.Spaces.Dz f z θ = Work.Spaces.Dz f' z θ := by
  intro z θ hzθ
  have hz : (0 : ℝ) < z := hzθ.1
  have heq : Set.EqOn (fun t => f t θ) (fun t => f' t θ) (Set.Ioi 0) :=
    fun t ht => h t θ ⟨ht, hzθ.2⟩
  have hd := (heq.deriv isOpen_Ioi) hz
  simp only [Work.Spaces.Dz, Work.Spaces.pz]
  rw [hd]

/-- `D_θ` preserves equality on the open quadrant. -/
lemma Dth_congr_Qd {f f' : ℝ → ℝ → ℝ}
    (h : ∀ z θ, (z, θ) ∈ Work.Construction.Qd → f z θ = f' z θ) :
    ∀ z θ, (z, θ) ∈ Work.Construction.Qd → Work.Spaces.Dth f z θ = Work.Spaces.Dth f' z θ := by
  intro z θ hzθ
  have hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := hzθ.2
  have heq : Set.EqOn (fun t => f z t) (fun t => f' z t) (Set.Ioo 0 (Real.pi / 2)) :=
    fun t ht => h z t ⟨hzθ.1, ht⟩
  have hd := (heq.deriv isOpen_Ioo) hθ
  simp only [Work.Spaces.Dth, Work.Spaces.pth]
  rw [hd]

/-- **The congruence of `H1IP α` in its first argument**, with no regularity hypotheses. -/
theorem H1IP_congr_qd (α : ℝ) {f f' g : ℝ → ℝ → ℝ}
    (h : ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd → f z θ = f' z θ) :
    Work.Coercivity.H1IP α f g = Work.Coercivity.H1IP α f' g := by
  have hDz := Dz_congr_Qd h
  have hDth := Dth_congr_Qd h
  simp only [Work.Coercivity.H1IP]
  have h1 := wip_congr_Qd
    (ρ := (fun z θ => Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)))
    (A := Work.Spaces.Dz f) (A' := Work.Spaces.Dz f') (B := Work.Spaces.Dz g) hDz
  have h2 := wip_congr_Qd
    (ρ := (fun z θ => Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)))
    (A := f) (A' := f') (B := g) h
  have h3 := wip_congr_Qd
    (ρ := (fun z _ => Work.Spaces.w z ^ 2)) (A := f) (A' := f') (B := g) h
  have h4 := wip_congr_Qd
    (ρ := (fun z θ => Work.Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.gam α)))
    (A := Work.Spaces.Dth f) (A' := Work.Spaces.Dth f') (B := Work.Spaces.Dth g) hDth
  rw [h1, h2, h3, h4]

end Work.FTS.CoercivityFix.StepAssembly
