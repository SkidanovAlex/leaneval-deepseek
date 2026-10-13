/-
# The `D_θ`-expansion of `D_z^j D_θ^i (∂_θG)` on the open box `V`

Elgindi's expansion of the iterated angular operator applied to a single angular derivative:

  `D_θ^i (∂_θG) = ∑_{a ≤ i-1} C(i-1,a) · (D_θ^a sin 2θ) · (D_θ^{i-1-a} ∂_θ²G)`,

written with the angular profile `sinIter a = D_θ^a (sin 2θ)`, and pushed through `D_z^j`
(which only sees the `z`-variable, so it acts termwise on the `a`-sum).

Two ingredients are built here, both in the genuine `C^∞` class `SmV` on the open box
`V = (0,∞) × (-1, π/2+1)`:

* `DzIter_sum_eqOn_V`: `D_z^j` is linear over a finite sum with coefficients `c a θ`
  depending only on `θ` (the smooth-order `z`-linearity that the localisation chapter needs);
* `DthIter_pth_eq_sum_V`: the `D_θ`-expansion above, in the genuine smooth order (the
  analytic-order version `Work.FTS.EllipticEst.ThetaU.DthIter_pth_eq_sum` does not apply to
  the smooth localisation data).

The target `mixed_pth_expand_V` is the combination of the two.
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Submission.Work.FTS.EllipticEst.ThetaU.SlotVDefs
import Submission.Work.FTS.LocData.DthIter_mul_smoothQuad

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.ThetaU

set_option autoImplicit false

/-! ## Linearity of `∂_z` (and of `D_z^j`) over a finite sum with `θ`-dependent coefficients -/

/-- `∂_z` is linear over a finite sum whose coefficients depend only on `θ`, in the smooth
class `SmV` on the open box `V`. -/
theorem pz_sum_eqOn_V (N : ℕ) (c : ℕ → ℝ → ℝ) (F : ℕ → ℝ → ℝ → ℝ)
    (hF : ∀ m, SmV (F m)) :
    Set.EqOn
      (Function.uncurry
        (Work.Spaces.pz (fun z θ => ∑ m ∈ Finset.range N, c m θ * F m z θ)))
      (Function.uncurry
        (fun z θ => ∑ m ∈ Finset.range N, c m θ * Work.Spaces.pz (F m) z θ)) V := by
  intro p hp
  obtain ⟨z, θ⟩ := p
  have hdiff : ∀ m, DifferentiableAt ℝ (fun z' => F m z' θ) z := by
    intro m
    have h1 : DifferentiableAt ℝ (Function.uncurry (F m)) (z, θ) :=
      ((hF m).contDiffAt hp.1 hp.2).differentiableAt Work.FTS.LocData.smoothOrder_ne_zero
    have h2 : DifferentiableAt ℝ (fun e : ℝ => (e, θ)) z :=
      (hasFDerivAt_prodMk_left z θ).differentiableAt
    have h3 := h1.comp z h2
    simpa [Function.comp_def, Function.uncurry] using h3
  show deriv (fun z' => ∑ m ∈ Finset.range N, c m θ * F m z' θ) z
      = ∑ m ∈ Finset.range N, c m θ * deriv (fun z' => F m z' θ) z
  have hfun : (fun z' => ∑ m ∈ Finset.range N, c m θ * F m z' θ)
      = ∑ m ∈ Finset.range N, (fun z' => c m θ * F m z' θ) := by
    funext z'
    rw [Finset.sum_apply]
  rw [hfun, deriv_sum (fun m _ => (hdiff m).const_mul (c m θ))]
  exact Finset.sum_congr rfl fun m _ => deriv_const_mul_field (c m θ)

/-- `D_z^j` is linear over a finite sum whose coefficients depend only on `θ`. -/
theorem DzIter_sum_eqOn_V (j N : ℕ) (c : ℕ → ℝ → ℝ) (F : ℕ → ℝ → ℝ → ℝ)
    (hF : ∀ m, SmV (F m)) :
    Set.EqOn
      (Function.uncurry
        (Work.Spaces.DzIter j (fun z θ => ∑ m ∈ Finset.range N, c m θ * F m z θ)))
      (Function.uncurry
        (fun z θ => ∑ m ∈ Finset.range N, c m θ * Work.Spaces.DzIter j (F m) z θ)) V := by
  induction j with
  | zero => intro p hp; rfl
  | succ j ih =>
      intro p hp
      obtain ⟨z, θ⟩ := p
      have hFs : ∀ m, SmV (Work.Spaces.DzIter j (F m)) := fun m => (hF m).DzIter j
      have hcongr := Work.Spaces.pz_congr_of_isOpen isOpen_V ih hp
      have hstep := pz_sum_eqOn_V N c (fun m => Work.Spaces.DzIter j (F m)) hFs hp
      simp only [Function.uncurry] at hstep
      show Work.Spaces.Dz
          (Work.Spaces.DzIter j (fun z θ => ∑ m ∈ Finset.range N, c m θ * F m z θ)) z θ
        = ∑ m ∈ Finset.range N, c m θ * Work.Spaces.Dz (Work.Spaces.DzIter j (F m)) z θ
      show z * Work.Spaces.pz
            (Work.Spaces.DzIter j (fun z θ => ∑ m ∈ Finset.range N, c m θ * F m z θ)) z θ
        = ∑ m ∈ Finset.range N, c m θ * (z * Work.Spaces.pz (Work.Spaces.DzIter j (F m)) z θ)
      rw [hcongr, hstep, Finset.mul_sum]
      exact Finset.sum_congr rfl fun m _ => by ring

/-! ## The `D_θ`-expansion of `D_θ^i (∂_θG)` in the genuine smooth order -/

/-- **The derivation identity, genuine smooth order.**  On the angular interval
`U = (-1, π/2+1)` where the `θ`-slice of `∂_θ²f` is `C^∞`,

`D_θ^i (∂_θ f)(z,θ) = ∑_{a ≤ i-1} C(i-1,a) · (D_θ^a sin 2θ) · D_θ^{i-1-a} (∂_θ²f)(z,θ)`. -/
theorem DthIter_pth_eq_sum_V {f : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hθ : θ ∈ Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1))
    (hg : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun θ' => Work.Spaces.pthIter 2 f z θ') (Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)))
    (i : ℕ) (hi : 1 ≤ i) :
    Work.Spaces.DthIter i (Work.Spaces.pth f) z θ
      = ∑ m ∈ Finset.range i, ((i - 1).choose m : ℝ) *
          (Work.Spaces.DthIter m sinTwo z θ
            * Work.Spaces.DthIter (i - 1 - m) (Work.Spaces.pthIter 2 f) z θ) := by
  have hsplit : Work.Spaces.DthIter i (Work.Spaces.pth f)
      = Work.Spaces.DthIter (i - 1)
          (fun z θ => Real.sin (2 * θ) * Work.Spaces.pthIter 2 f z θ) := by
    conv_lhs => rw [show i = (i - 1) + 1 from (Nat.sub_add_cancel hi).symm]
    rw [DthIter_add_apply, DthIter_one_pth]
  rw [hsplit]
  have hs2 : ContDiffOn ℝ Work.Stability.smoothOrder (fun θ : ℝ => Real.sin (2 * θ))
      (Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)) := by
    simpa [Function.comp_def] using
      (Real.contDiff_sin.comp (contDiff_const.mul contDiff_id)).contDiffOn
  rw [Work.FTS.LocData.DthIter_mul_smooth (i - 1) (fun _ θ' => Real.sin (2 * θ'))
      (Work.Spaces.pthIter 2 f) z (Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)) isOpen_Ioo
      hs2 hg θ hθ, Nat.sub_add_cancel hi]

/-! ## The target -/

theorem mixed_pth_expand_V {G : ℝ → ℝ → ℝ} (hG : Work.FTS.EllipticEst.ThetaU.SmV G)
    (j i : ℕ) (hi : 1 ≤ i) {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)) :
    Work.Spaces.mixed j i (Work.Spaces.pth G) z θ
      = ∑ a ∈ Finset.range i, ((i - 1).choose a : ℝ) *
          (Work.FTS.EllipticEst.sinIter a θ
            * Work.Spaces.mixed j (i - 1 - a) (Work.Spaces.pthIter 2 G) z θ) := by
  have hmem : (z, θ) ∈ V := mem_V hz hθ
  -- the `D_θ`-expansion, with the angular profile `sinIter` in place of `D_θ^a sin 2θ`
  have hDth : Set.EqOn (Function.uncurry (Work.Spaces.DthIter i (Work.Spaces.pth G)))
      (Function.uncurry (fun z θ => ∑ a ∈ Finset.range i, ((i - 1).choose a : ℝ) *
        (Work.FTS.EllipticEst.sinIter a θ *
          Work.Spaces.DthIter (i - 1 - a) (Work.Spaces.pthIter 2 G) z θ))) V := by
    intro p hp
    obtain ⟨z', θ'⟩ := p
    simpa [DthIter_sinTwo_eq_sinIter] using
      DthIter_pth_eq_sum_V (f := G) (z := z') hp.2 (hG.slice_pthIter 2 hp.1) i hi
  -- reassociating the coefficients
  have hZ : Set.EqOn
      (Function.uncurry (fun z θ => ∑ a ∈ Finset.range i, ((i - 1).choose a : ℝ) *
        (Work.FTS.EllipticEst.sinIter a θ *
          Work.Spaces.DthIter (i - 1 - a) (Work.Spaces.pthIter 2 G) z θ)))
      (Function.uncurry (fun z θ => ∑ a ∈ Finset.range i,
        (((i - 1).choose a : ℝ) * Work.FTS.EllipticEst.sinIter a θ) *
          Work.Spaces.DthIter (i - 1 - a) (Work.Spaces.pthIter 2 G) z θ)) V := by
    intro p hp
    simp only [Function.uncurry]
    exact Finset.sum_congr rfl fun a _ => by ring
  calc Work.Spaces.mixed j i (Work.Spaces.pth G) z θ
      = Work.Spaces.DzIter j (Work.Spaces.DthIter i (Work.Spaces.pth G)) z θ := rfl
    _ = Work.Spaces.DzIter j (fun z θ => ∑ a ∈ Finset.range i, ((i - 1).choose a : ℝ) *
          (Work.FTS.EllipticEst.sinIter a θ *
            Work.Spaces.DthIter (i - 1 - a) (Work.Spaces.pthIter 2 G) z θ)) z θ :=
        DzIter_congr_V hDth j hmem
    _ = Work.Spaces.DzIter j (fun z θ => ∑ a ∈ Finset.range i,
          (((i - 1).choose a : ℝ) * Work.FTS.EllipticEst.sinIter a θ) *
            Work.Spaces.DthIter (i - 1 - a) (Work.Spaces.pthIter 2 G) z θ) z θ :=
        DzIter_congr_V hZ j hmem
    _ = ∑ a ∈ Finset.range i,
          (((i - 1).choose a : ℝ) * Work.FTS.EllipticEst.sinIter a θ) *
            Work.Spaces.DzIter j
              (Work.Spaces.DthIter (i - 1 - a) (Work.Spaces.pthIter 2 G)) z θ :=
        DzIter_sum_eqOn_V j i
          (fun a θ => ((i - 1).choose a : ℝ) * Work.FTS.EllipticEst.sinIter a θ)
          (fun a => Work.Spaces.DthIter (i - 1 - a) (Work.Spaces.pthIter 2 G))
          (fun a => (hG.pthIter 2).DthIter (i - 1 - a)) hmem
    _ = ∑ a ∈ Finset.range i, ((i - 1).choose a : ℝ) *
          (Work.FTS.EllipticEst.sinIter a θ *
            Work.Spaces.mixed j (i - 1 - a) (Work.Spaces.pthIter 2 G) z θ) := by
        apply Finset.sum_congr rfl
        intro a ha
        simp only [Work.Spaces.mixed]
        ring

end Work.FTS.EllipticEst.ThetaU
