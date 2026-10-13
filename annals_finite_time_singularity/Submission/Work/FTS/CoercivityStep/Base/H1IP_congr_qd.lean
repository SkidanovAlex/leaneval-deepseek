import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Coercivity.Defs
import Submission.Work.Coercivity.Basic
import Submission.Work.FTS.CoercivityStep.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Set

namespace Work.FTS.CoercivityStep.Base

/-! ## Congruence of `wip` on the open quadrant

The pairing `wip ρ A B = ∫_{z ∈ [0,∞)} ∫_{θ ∈ [0,π/2]} A z θ · B z θ · ρ z θ` is an
iterated Bochner integral, so it only sees the values of `A` almost everywhere.  The open
quadrant `Qd = (0,∞) × (0,π/2)` is co-null in the domain `[0,∞) × [0,π/2]` (the difference
is contained in the two lines `θ = 0`, `θ = π/2` and the point `z = 0`), so `wip` is
invariant under changing the first argument on `Qd`.

The two ingredients are the two "reduce to the open interval" identities

* `∫_{[0,∞)} = ∫_{(0,∞)}`  (`MeasureTheory.integral_Ici_eq_integral_Ioi`),
* `∫_{[0,π/2]} = ∫_{(0,π/2)}` (`MeasureTheory.integral_Icc_eq_integral_Ioo`),

both of which hold for the total Bochner integral without any measurability or
integrability hypothesis. -/

/-- The iterated integral `∫_{z∈[0,∞)} ∫_{θ∈[0,π/2]} F z θ` equals the iterated integral
over the open quadrant `∫_{z∈(0,∞)} ∫_{θ∈(0,π/2)} F z θ`.  No regularity is needed: the
Bochner integral is insensitive to null sets. -/
lemma wip_eq_Ioi_Ioo (F : ℝ → ℝ → ℝ) :
    (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, F z θ)
      = ∫ z in Set.Ioi (0 : ℝ), ∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), F z θ := by
  have h1 : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, F z θ)
      = ∫ z in Work.Spaces.Iz, ∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), F z θ := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici (fun z _ => ?_)
    exact MeasureTheory.integral_Icc_eq_integral_Ioo
  rw [h1]
  exact MeasureTheory.integral_Ici_eq_integral_Ioi

/-- `wip ρ A B` only depends on the first argument `A` through its values on the open
quadrant `Qd`: if `A = A'` on `Qd`, then `wip ρ A B = wip ρ A' B`.  No measurability,
integrability or smoothness hypothesis is required. -/
lemma wip_congr_Qd {ρ A A' B : ℝ → ℝ → ℝ}
    (h : ∀ z θ, (z, θ) ∈ Qd → A z θ = A' z θ) :
    Work.Coercivity.wip ρ A B = Work.Coercivity.wip ρ A' B := by
  simp only [Work.Coercivity.wip]
  rw [wip_eq_Ioi_Ioo (fun z θ => A z θ * B z θ * ρ z θ),
    wip_eq_Ioi_Ioo (fun z θ => A' z θ * B z θ * ρ z θ)]
  refine MeasureTheory.setIntegral_congr_fun
    (isOpen_Ioi (a := (0 : ℝ))).measurableSet (fun z hz => ?_)
  refine MeasureTheory.setIntegral_congr_fun
    (isOpen_Ioo (a := (0 : ℝ)) (b := Real.pi / 2)).measurableSet (fun θ hθ => ?_)
  rw [h z θ ⟨hz, hθ⟩]

/-! ## The derivative congruence

If `f` and `f'` agree on the open quadrant, then so do `D_z f` and `D_z f'` (resp.
`D_θ f` and `D_θ f'`): at a point of the open quadrant the two functions agree on a whole
neighbourhood, so the partial derivatives coincide there.  This is `Set.EqOn.deriv`
applied on the open sets `(0,∞)` and `(0,π/2)` of the two coordinate lines through the
point. -/

/-- `D_z f = D_z f'` on the open quadrant whenever `f = f'` there. -/
lemma Dz_congr_Qd {f f' : ℝ → ℝ → ℝ}
    (h : ∀ z θ, (z, θ) ∈ Qd → f z θ = f' z θ) :
    ∀ z θ, (z, θ) ∈ Qd → Work.Spaces.Dz f z θ = Work.Spaces.Dz f' z θ := by
  intro z θ hzθ
  have hz : (0 : ℝ) < z := hzθ.1
  have heq : Set.EqOn (fun t => f t θ) (fun t => f' t θ) (Set.Ioi 0) :=
    fun t ht => h t θ ⟨ht, hzθ.2⟩
  have hd := (heq.deriv isOpen_Ioi) hz
  simp only [Work.Spaces.Dz, Work.Spaces.pz]
  rw [hd]

/-- `D_θ f = D_θ f'` on the open quadrant whenever `f = f'` there. -/
lemma Dth_congr_Qd {f f' : ℝ → ℝ → ℝ}
    (h : ∀ z θ, (z, θ) ∈ Qd → f z θ = f' z θ) :
    ∀ z θ, (z, θ) ∈ Qd → Work.Spaces.Dth f z θ = Work.Spaces.Dth f' z θ := by
  intro z θ hzθ
  have hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := hzθ.2
  have heq : Set.EqOn (fun t => f z t) (fun t => f' z t) (Set.Ioo 0 (Real.pi / 2)) :=
    fun t ht => h z t ⟨hzθ.1, ht⟩
  have hd := (heq.deriv isOpen_Ioo) hθ
  simp only [Work.Spaces.Dth, Work.Spaces.pth]
  rw [hd]

/-! ## The congruence of the `ℋ¹` inner product in its first argument -/

/-- **`H1IP α` only depends on its first argument through the values on the open
quadrant.**  `H1IP α` is the sum of four weighted pairings `wip`, applied to `f`, `D_z f`,
`f` and `D_θ f`; on `Qd` these agree with the corresponding functions built from `f'`
(the pointwise hypothesis `h` for `f` itself, and `Dz_congr_Qd`/`Dth_congr_Qd` for the
derivatives — derivatives are local and `Qd` is open, so the hypotheses `hf`, `hf'`, `hg`
are not needed).  `wip_congr_Qd` then identifies the four pairings. -/
theorem H1IP_congr_qd (α : ℝ) {f f' g : ℝ → ℝ → ℝ}
    (hf : Work.FTS.CoercivityStep.HkReg α 1 f)
    (hf' : Work.FTS.CoercivityStep.HkReg α 1 f')
    (hg : Work.FTS.CoercivityStep.HkReg α 1 g)
    (h : ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.CoercivityStep.Qd → f z θ = f' z θ) :
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

end Work.FTS.CoercivityStep.Base

end
