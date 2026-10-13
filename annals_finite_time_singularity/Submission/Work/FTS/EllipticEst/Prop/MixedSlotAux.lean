import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Order.CompletePartialOrder
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.Prop.thFluxHasDerivAt
import Submission.Work.FTS.EllipticEst.Prop.zFluxHasDerivAt

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Prop

set_option autoImplicit false

/-! ## The box, the support predicate, and basic two-variable calculus -/

/-- The closed box `[1/2,2] × [π/8,3π/8]` (as a subset of `ℝ × ℝ`). -/
def MBox : Set (ℝ × ℝ) := Set.Icc (1 / 2 : ℝ) 2 ×ˢ Set.Icc (Real.pi / 8) (3 * Real.pi / 8)

/-- The open box. -/
def MBoxo : Set (ℝ × ℝ) := Set.Ioo (1 / 2 : ℝ) 2 ×ˢ Set.Ioo (Real.pi / 8) (3 * Real.pi / 8)

/-- The half strip `(0,∞) × (0,π/2)` on which `v` is smooth. -/
def MStrip : Set (ℝ × ℝ) := Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)

theorem isOpen_MStrip : IsOpen MStrip := isOpen_Ioi.prod isOpen_Ioo

theorem isCompact_MBox : IsCompact MBox := isCompact_Icc.prod isCompact_Icc

theorem MBox_subset_MStrip : MBox ⊆ MStrip := by
  intro p hp
  simp only [MBox, Set.mem_prod, Set.mem_Icc] at hp
  simp only [MStrip, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo]
  exact ⟨by linarith [hp.1.1], ⟨by linarith [hp.2.1, Real.pi_pos],
    by linarith [hp.2.2, Real.pi_pos]⟩⟩

/-- `f` vanishes off the open box. -/
def Van (f : ℝ → ℝ → ℝ) : Prop :=
  ∀ z θ, z ∉ Set.Ioo (1 / 2 : ℝ) 2 ∨ θ ∉ Set.Ioo (Real.pi / 8) (3 * Real.pi / 8) → f z θ = 0

theorem Van.mul {f g : ℝ → ℝ → ℝ} (hf : Van f) : Van (fun z θ => f z θ * g z θ) :=
  fun z θ h => by show f z θ * g z θ = 0; rw [hf z θ h, zero_mul]

theorem Van.mul' {f g : ℝ → ℝ → ℝ} (hg : Van g) : Van (fun z θ => f z θ * g z θ) :=
  fun z θ h => by show f z θ * g z θ = 0; rw [hg z θ h, mul_zero]

theorem Van.neg {f : ℝ → ℝ → ℝ} (hf : Van f) : Van (fun z θ => -f z θ) :=
  fun z θ h => by show -f z θ = 0; rw [hf z θ h, neg_zero]

theorem Van.sq {f : ℝ → ℝ → ℝ} (hf : Van f) : Van (fun z θ => (f z θ) ^ 2) :=
  fun z θ h => by show (f z θ) ^ 2 = 0; rw [hf z θ h]; ring

theorem Van.zmul {f : ℝ → ℝ → ℝ} (hf : Van f) : Van (fun z θ => z * f z θ) :=
  fun z θ h => by show z * f z θ = 0; rw [hf z θ h, mul_zero]

/-- `D_z f = z·∂_z f` vanishes off the box as soon as `∂_z f` does. -/
theorem Van.Dz {f : ℝ → ℝ → ℝ} (hf : Van (Work.Spaces.pz f)) : Van (Work.Spaces.Dz f) := by
  intro z θ h
  show z * Work.Spaces.pz f z θ = 0
  rw [hf z θ h, mul_zero]

/-- The curried `z`-partial of a two-variable function is differentiable at a point where the
function is differentiable. -/
theorem differentiableAt_curry_left {f : ℝ → ℝ → ℝ} {z θ : ℝ}
    (h : DifferentiableAt ℝ (Function.uncurry f) (z, θ)) :
    DifferentiableAt ℝ (fun z' => f z' θ) z := by
  have hcurve : HasDerivAt (fun t : ℝ => (t, θ)) (1, 0) z := by
    simpa using (hasDerivAt_id z).prodMk (hasDerivAt_const z θ)
  have hh := (h.hasFDerivAt.comp_hasDerivAt z hcurve).differentiableAt
  have hmem : (Function.uncurry f ∘ fun t : ℝ => (t, θ)) = fun z' => f z' θ := rfl
  rwa [hmem] at hh

/-- The curried `θ`-partial of a two-variable function is differentiable at a point where the
function is differentiable. -/
theorem differentiableAt_curry_right {f : ℝ → ℝ → ℝ} {z θ : ℝ}
    (h : DifferentiableAt ℝ (Function.uncurry f) (z, θ)) :
    DifferentiableAt ℝ (fun θ' => f z θ') θ := by
  have hcurve : HasDerivAt (fun t : ℝ => (z, t)) (0, 1) θ := by
    simpa using (hasDerivAt_const θ z).prodMk (hasDerivAt_id θ)
  have hh := (h.hasFDerivAt.comp_hasDerivAt θ hcurve).differentiableAt
  have hmem : (Function.uncurry f ∘ fun t : ℝ => (z, t)) = fun θ' => f z θ' := rfl
  rwa [hmem] at hh

/-- Membership tests for the box intervals, in the direction in which they are used. -/
theorem notMem_Ioo_of_le {y a b : ℝ} (h : y ≤ a) : y ∉ Set.Ioo a b :=
  fun hy => absurd hy.1 (not_lt.mpr h)

theorem notMem_Ioo_of_ge {y a b : ℝ} (h : b ≤ y) : y ∉ Set.Ioo a b :=
  fun hy => absurd hy.2 (not_lt.mpr h)

/-- Joint smoothness on an open set implies smoothness at each of its points. -/
theorem contDiffAt_of_contDiffOn {f : ℝ → ℝ → ℝ} {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    {n : WithTop ℕ∞} (h : ContDiffOn ℝ n (Function.uncurry f) U) {p : ℝ × ℝ} (hp : p ∈ U) :
    ContDiffAt ℝ n (Function.uncurry f) p :=
  (h.contDiffWithinAt hp).contDiffAt (hU.mem_nhds hp)

/-- The Fréchet derivative of a function on `ℝ × ℝ` evaluated at `(1,0)` is the derivative of
its first slice. -/
theorem fderiv_fst_apply {F : ℝ × ℝ → ℝ} {z θ : ℝ} (h : DifferentiableAt ℝ F (z, θ)) :
    (fderiv ℝ F (z, θ)) (1, 0) = deriv (fun z' => F (z', θ)) z := by
  have hcurve : HasDerivAt (fun t : ℝ => (t, θ)) (1, 0) z := by
    simpa using (hasDerivAt_id z).prodMk (hasDerivAt_const z θ)
  exact ((h.hasFDerivAt.comp_hasDerivAt z hcurve).deriv).symm

/-- The Fréchet derivative of a function on `ℝ × ℝ` evaluated at `(0,1)` is the derivative of
its second slice. -/
theorem fderiv_snd_apply {F : ℝ × ℝ → ℝ} {z θ : ℝ} (h : DifferentiableAt ℝ F (z, θ)) :
    (fderiv ℝ F (z, θ)) (0, 1) = deriv (fun θ' => F (z, θ')) θ := by
  have hcurve : HasDerivAt (fun t : ℝ => (z, t)) (0, 1) θ := by
    simpa using (hasDerivAt_const θ z).prodMk (hasDerivAt_id θ)
  exact ((h.hasFDerivAt.comp_hasDerivAt θ hcurve).deriv).symm

/-- If a function differentiable at `x` vanishes on `(-∞,x]`, then its derivative at `x` is `0`. -/
theorem deriv_eq_zero_of_eq_zero_of_forall_le {g : ℝ → ℝ} {x : ℝ}
    (hd : DifferentiableAt ℝ g x) (h0 : ∀ y, y ≤ x → g y = 0) : deriv g x = 0 := by
  have h1 : HasDerivWithinAt g (deriv g x) (Set.Iio x) x := hd.hasDerivAt.hasDerivWithinAt
  have h2 : HasDerivWithinAt g 0 (Set.Iio x) x :=
    (hasDerivWithinAt_const x (Set.Iio x) 0).congr (fun y hy => h0 y (le_of_lt hy))
      (h0 x le_rfl)
  have e1 := h1.derivWithin (uniqueDiffWithinAt_Iio x)
  have e2 := h2.derivWithin (uniqueDiffWithinAt_Iio x)
  rw [e2] at e1
  exact e1.symm

/-- If a function differentiable at `x` vanishes on `[x,∞)`, then its derivative at `x` is `0`. -/
theorem deriv_eq_zero_of_eq_zero_of_forall_ge {g : ℝ → ℝ} {x : ℝ}
    (hd : DifferentiableAt ℝ g x) (h0 : ∀ y, x ≤ y → g y = 0) : deriv g x = 0 := by
  have h1 : HasDerivWithinAt g (deriv g x) (Set.Ioi x) x := hd.hasDerivAt.hasDerivWithinAt
  have h2 : HasDerivWithinAt g 0 (Set.Ioi x) x :=
    (hasDerivWithinAt_const x (Set.Ioi x) 0).congr (fun y hy => h0 y (le_of_lt hy))
      (h0 x le_rfl)
  have e1 := h1.derivWithin (uniqueDiffWithinAt_Ioi x)
  have e2 := h2.derivWithin (uniqueDiffWithinAt_Ioi x)
  rw [e2] at e1
  exact e1.symm

/-- `pz` preserves vanishing off the box (for a function smooth on the half strip). -/
theorem Van.pz {f : ℝ → ℝ → ℝ} (hvan : Van f)
    (hc : ContDiffOn ℝ 1 (Function.uncurry f) MStrip) : Van (Work.Spaces.pz f) := by
  intro z θ h
  rw [show Work.Spaces.pz f z θ = deriv (fun z' => f z' θ) z from rfl]
  by_cases hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)
  · rcases lt_or_ge z (1 / 2) with hlt | hge
    · have hev : (fun z' : ℝ => f z' θ) =ᶠ[𝓝 z] (fun _ => 0) := by
        filter_upwards [isOpen_Ioo.mem_nhds
          (show z ∈ Set.Ioo (z - 1) (1 / 2) from ⟨by linarith, hlt⟩)] with y hy
        exact hvan y θ (Or.inl (notMem_Ioo_of_le (le_of_lt hy.2)))
      rw [hev.deriv_eq]; simp
    · by_cases hzb : z ∈ Set.Ioo (1 / 2 : ℝ) 2
      · have hθb : θ ∉ Set.Ioo (Real.pi / 8) (3 * Real.pi / 8) := by
          rcases h with h' | h'
          · exact absurd hzb h'
          · exact h'
        have h0 : ∀ z' : ℝ, f z' θ = 0 := fun z' => hvan z' θ (Or.inr hθb)
        rw [show (fun z' : ℝ => f z' θ) = fun _ => 0 from funext h0]
        simp
      · rcases eq_or_lt_of_le hge with heq | hlt2
        · obtain rfl : z = (1 / 2 : ℝ) := heq.symm
          refine deriv_eq_zero_of_eq_zero_of_forall_le ?_ ?_
          · have hmem : ((1 / 2 : ℝ), θ) ∈ MStrip := by
              simp only [MStrip, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo]
              exact ⟨by norm_num, hθ⟩
            exact differentiableAt_curry_left
              ((contDiffAt_of_contDiffOn isOpen_MStrip hc hmem).differentiableAt one_ne_zero)
          · intro y hy
            exact hvan y θ (Or.inl (notMem_Ioo_of_le hy))
        · have hz2 : (2 : ℝ) ≤ z := by
            by_contra hc'
            exact hzb ⟨hlt2, not_le.mp hc'⟩
          rcases lt_or_eq_of_le hz2 with hlt' | heq
          · have hev : (fun z' : ℝ => f z' θ) =ᶠ[𝓝 z] (fun _ => 0) := by
              filter_upwards [isOpen_Ioo.mem_nhds
                (show z ∈ Set.Ioo (2 : ℝ) (z + 1) from ⟨hlt', by linarith⟩)] with y hy
              exact hvan y θ (Or.inl (notMem_Ioo_of_ge (le_of_lt hy.1)))
            rw [hev.deriv_eq]; simp
          · obtain rfl : z = (2 : ℝ) := heq.symm
            refine deriv_eq_zero_of_eq_zero_of_forall_ge ?_ ?_
            · have hmem : ((2 : ℝ), θ) ∈ MStrip := by
                simp only [MStrip, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo]
                exact ⟨by norm_num, hθ⟩
              exact differentiableAt_curry_left
                ((contDiffAt_of_contDiffOn isOpen_MStrip hc hmem).differentiableAt one_ne_zero)
            · intro y hy
              exact hvan y θ (Or.inl (notMem_Ioo_of_ge hy))
  · have h0 : ∀ z' : ℝ, f z' θ = 0 := fun z' => by
      by_cases hz' : z' ∈ Set.Ioo (1 / 2 : ℝ) 2
      · exact hvan z' θ (Or.inr (fun hθb =>
          hθ ⟨by linarith [hθb.1, Real.pi_pos], by linarith [hθb.2, Real.pi_pos]⟩))
      · exact hvan z' θ (Or.inl hz')
    rw [show (fun z' : ℝ => f z' θ) = fun _ => 0 from funext h0]
    simp

/-- `pth` preserves vanishing off the box (for a function smooth on the half strip). -/
theorem Van.pth {f : ℝ → ℝ → ℝ} (hvan : Van f)
    (hc : ContDiffOn ℝ 1 (Function.uncurry f) MStrip) : Van (Work.Spaces.pth f) := by
  intro z θ h
  rw [show Work.Spaces.pth f z θ = deriv (fun θ' => f z θ') θ from rfl]
  by_cases hz : z ∈ Set.Ioo (1 / 2 : ℝ) 2
  · have hθb : θ ∉ Set.Ioo (Real.pi / 8) (3 * Real.pi / 8) := by
      rcases h with h' | h'
      · exact absurd hz h'
      · exact h'
    rcases lt_or_ge θ (Real.pi / 8) with hlt | hge
    · have hev : (fun θ' : ℝ => f z θ') =ᶠ[𝓝 θ] (fun _ => 0) := by
        filter_upwards [isOpen_Ioo.mem_nhds
          (show θ ∈ Set.Ioo (θ - 1) (Real.pi / 8) from ⟨by linarith, hlt⟩)] with y hy
        exact hvan z y (Or.inr (notMem_Ioo_of_le (le_of_lt hy.2)))
      rw [hev.deriv_eq]; simp
    · rcases eq_or_lt_of_le hge with heq | hlt2
      · obtain rfl : θ = Real.pi / 8 := heq.symm
        refine deriv_eq_zero_of_eq_zero_of_forall_le ?_ ?_
        · have hmem : (z, Real.pi / 8) ∈ MStrip := by
            simp only [MStrip, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo]
            exact ⟨by linarith [hz.1], ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩⟩
          exact differentiableAt_curry_right
            ((contDiffAt_of_contDiffOn isOpen_MStrip hc hmem).differentiableAt one_ne_zero)
        · intro y hy
          exact hvan z y (Or.inr (notMem_Ioo_of_le hy))
      · have hge3 : 3 * Real.pi / 8 ≤ θ := by
          by_contra hc'
          exact hθb ⟨hlt2, not_le.mp hc'⟩
        rcases lt_or_eq_of_le hge3 with hlt' | heq2
        · have hev : (fun θ' : ℝ => f z θ') =ᶠ[𝓝 θ] (fun _ => 0) := by
            filter_upwards [isOpen_Ioo.mem_nhds
              (show θ ∈ Set.Ioo (3 * Real.pi / 8) (θ + 1) from ⟨hlt', by linarith⟩)] with y hy
            exact hvan z y (Or.inr (notMem_Ioo_of_ge (le_of_lt hy.1)))
          rw [hev.deriv_eq]; simp
        · obtain rfl : θ = 3 * Real.pi / 8 := heq2.symm
          refine deriv_eq_zero_of_eq_zero_of_forall_ge ?_ ?_
          · have hmem : (z, 3 * Real.pi / 8) ∈ MStrip := by
              simp only [MStrip, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo]
              exact ⟨by linarith [hz.1], ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩⟩
            exact differentiableAt_curry_right
              ((contDiffAt_of_contDiffOn isOpen_MStrip hc hmem).differentiableAt one_ne_zero)
          · intro y hy
            exact hvan z y (Or.inr (notMem_Ioo_of_ge hy))
  · have h0 : ∀ θ' : ℝ, f z θ' = 0 := fun θ' => by
      by_cases hθ' : θ' ∈ Set.Ioo (Real.pi / 8) (3 * Real.pi / 8)
      · exact hvan z θ' (Or.inl (fun hz' => hz ⟨hz'.1, hz'.2⟩))
      · exact hvan z θ' (Or.inr hθ')
    rw [show (fun θ' : ℝ => f z θ') = fun _ => 0 from funext h0]
    simp

theorem Van.congr {f g : ℝ → ℝ → ℝ} (h : Van f) (hfg : ∀ z θ, f z θ = g z θ) : Van g :=
  fun z θ hh => by rw [← hfg z θ, h z θ hh]

/-! ## The weights, the fluxes and the four integrands -/

/-- The radial weight `w(z)²`. -/
def W2 (z : ℝ) : ℝ := (Work.Spaces.w z) ^ 2

/-- The angular weight `sin(2θ)^q`. -/
def Sq (q : ℝ) (θ : ℝ) : ℝ := (Real.sin (2 * θ)) ^ q

/-- The derivative of the angular weight. -/
def dSq (q : ℝ) (θ : ℝ) : ℝ := deriv (fun t : ℝ => (Real.sin (2 * t)) ^ q) θ

/-- The coefficient `(z-3)/(1+z)`. -/
def xi (z : ℝ) : ℝ := (z - 3) / (1 + z)

/-- The integrand of the left-hand side of the identity. -/
def FL (q : ℝ) (v : ℝ → ℝ → ℝ) (z θ : ℝ) : ℝ :=
  (Work.Spaces.Dz (Work.Spaces.pth v) z θ) ^ 2 * W2 z * Sq q θ

/-- The first integrand of the right-hand side. -/
def FT1 (q : ℝ) (v : ℝ → ℝ → ℝ) (z θ : ℝ) : ℝ :=
  (Work.Spaces.Dz (Work.Spaces.Dz v) z θ) * (Work.Spaces.pth (Work.Spaces.pth v) z θ)
    * W2 z * Sq q θ

/-- The second integrand of the right-hand side. -/
def FT2 (q : ℝ) (v : ℝ → ℝ → ℝ) (z θ : ℝ) : ℝ :=
  (Work.Spaces.Dz v z θ) * (Work.Spaces.Dz (Work.Spaces.pth v) z θ) * W2 z * dSq q θ

/-- The third integrand of the right-hand side. -/
def FT3 (q : ℝ) (v : ℝ → ℝ → ℝ) (z θ : ℝ) : ℝ :=
  (Work.Spaces.Dz v z θ) * (Work.Spaces.pth (Work.Spaces.pth v) z θ) * W2 z * xi z * Sq q θ

/-- The radial flux of the divergence identity (curried version). -/
def zFlC (q : ℝ) (v : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => -(z * (Work.Spaces.Dz v z θ) * (Work.Spaces.pth (Work.Spaces.pth v) z θ)
    * W2 z * Sq q θ)

/-- The radial flux of the divergence identity. -/
def zFl (q : ℝ) (v : ℝ → ℝ → ℝ) : ℝ × ℝ → ℝ := fun p => zFlC q v p.1 p.2

/-- The angular flux of the divergence identity (curried version). -/
def thFlC (q : ℝ) (v : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => (Work.Spaces.Dz v z θ) * (Work.Spaces.Dz (Work.Spaces.pth v) z θ) * W2 z * Sq q θ

/-- The angular flux of the divergence identity. -/
def thFl (q : ℝ) (v : ℝ → ℝ → ℝ) : ℝ × ℝ → ℝ := fun p => thFlC q v p.1 p.2

theorem zFl_apply (q : ℝ) (v : ℝ → ℝ → ℝ) (z θ : ℝ) :
    zFl q v (z, θ) = zFlC q v z θ := rfl

theorem thFl_apply (q : ℝ) (v : ℝ → ℝ → ℝ) (z θ : ℝ) :
    thFl q v (z, θ) = thFlC q v z θ := rfl

/-- Vanishing is preserved by adding the weights `W2 z · Sq q θ`. -/
theorem Van_w {q : ℝ} {A : ℝ → ℝ → ℝ} (hA : Van A) :
    Van (fun z θ => A z θ * W2 z * Sq q θ) :=
  Van.congr (Van.mul (f := A) (g := fun z θ => W2 z * Sq q θ) hA) (fun z θ => by ring)

/-- Vanishing is preserved by adding the weights `W2 z · ξ z · Sq q θ`. -/
theorem Van_w3 {q : ℝ} {A : ℝ → ℝ → ℝ} (hA : Van A) :
    Van (fun z θ => A z θ * W2 z * xi z * Sq q θ) :=
  Van.congr (Van.mul (f := A) (g := fun z θ => W2 z * xi z * Sq q θ) hA) (fun z θ => by ring)

/-! ## Smoothness of the curried partials and of the weights -/

theorem pz_eq_fderiv {G : ℝ → ℝ → ℝ} {z θ : ℝ}
    (h : DifferentiableAt ℝ (Function.uncurry G) (z, θ)) :
    Work.Spaces.pz G z θ = fderiv ℝ (Function.uncurry G) (z, θ) (1, 0) := by
  have hcurve : HasDerivAt (fun t : ℝ => (t, θ)) (1, 0) z := by
    simpa using (hasDerivAt_id z).prodMk (hasDerivAt_const z θ)
  have hh := (h.hasFDerivAt.comp_hasDerivAt z hcurve).deriv
  have hmem : (Function.uncurry G ∘ fun t : ℝ => (t, θ)) = fun z' => G z' θ := rfl
  rw [hmem] at hh
  show deriv (fun z' => G z' θ) z = _
  exact hh

theorem pth_eq_fderiv {G : ℝ → ℝ → ℝ} {z θ : ℝ}
    (h : DifferentiableAt ℝ (Function.uncurry G) (z, θ)) :
    Work.Spaces.pth G z θ = fderiv ℝ (Function.uncurry G) (z, θ) (0, 1) := by
  have hcurve : HasDerivAt (fun t : ℝ => (z, t)) (0, 1) θ := by
    simpa using (hasDerivAt_const θ z).prodMk (hasDerivAt_id θ)
  have hh := (h.hasFDerivAt.comp_hasDerivAt θ hcurve).deriv
  have hmem : (Function.uncurry G ∘ fun t : ℝ => (z, t)) = fun θ' => G z θ' := rfl
  rw [hmem] at hh
  show deriv (fun θ' => G z θ') θ = _
  exact hh

/-- `∂_z` lowers the order of differentiability by one on an open set. -/
theorem contDiffOn_uncurry_pz_succ {n : ℕ} {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : ContDiffOn ℝ (n + 1) (Function.uncurry G) V) :
    ContDiffOn ℝ n (Function.uncurry (Work.Spaces.pz G)) V := by
  have hchain : ∀ p ∈ V, Work.Spaces.pz G p.1 p.2 = fderiv ℝ (Function.uncurry G) p (1, 0) :=
    fun p hp =>
      pz_eq_fderiv ((h.differentiableOn (by simp)).differentiableAt (hV.mem_nhds hp))
  have hfd : ContDiffOn ℝ n (fderiv ℝ (Function.uncurry G)) V :=
    h.fderiv_of_isOpen hV (m := n) (by simp)
  have hcomp : ContDiffOn ℝ n (fun p : ℝ × ℝ => fderiv ℝ (Function.uncurry G) p (1, 0)) V :=
    hfd.clm_apply contDiffOn_const
  exact hcomp.congr (fun p hp => by
    show Function.uncurry (Work.Spaces.pz G) p = fderiv ℝ (Function.uncurry G) p (1, 0)
    exact hchain p hp)

/-- `∂_θ` lowers the order of differentiability by one on an open set. -/
theorem contDiffOn_uncurry_pth_succ {n : ℕ} {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : ContDiffOn ℝ (n + 1) (Function.uncurry G) V) :
    ContDiffOn ℝ n (Function.uncurry (Work.Spaces.pth G)) V := by
  have hchain : ∀ p ∈ V, Work.Spaces.pth G p.1 p.2 = fderiv ℝ (Function.uncurry G) p (0, 1) :=
    fun p hp =>
      pth_eq_fderiv ((h.differentiableOn (by simp)).differentiableAt (hV.mem_nhds hp))
  have hfd : ContDiffOn ℝ n (fderiv ℝ (Function.uncurry G)) V :=
    h.fderiv_of_isOpen hV (m := n) (by simp)
  have hcomp : ContDiffOn ℝ n (fun p : ℝ × ℝ => fderiv ℝ (Function.uncurry G) p (0, 1)) V :=
    hfd.clm_apply contDiffOn_const
  exact hcomp.congr (fun p hp => by
    show Function.uncurry (Work.Spaces.pth G) p = fderiv ℝ (Function.uncurry G) p (0, 1)
    exact hchain p hp)

theorem contDiffOn_uncurry_mul {A B : ℝ → ℝ → ℝ} {U : Set (ℝ × ℝ)} {n : WithTop ℕ∞}
    (hA : ContDiffOn ℝ n (Function.uncurry A) U) (hB : ContDiffOn ℝ n (Function.uncurry B) U) :
    ContDiffOn ℝ n (Function.uncurry (fun z θ => A z θ * B z θ)) U :=
  (hA.mul hB).congr (fun p _ => rfl)

theorem contDiffOn_uncurry_pow {A : ℝ → ℝ → ℝ} {U : Set (ℝ × ℝ)} {n : WithTop ℕ∞} (m : ℕ)
    (hA : ContDiffOn ℝ n (Function.uncurry A) U) :
    ContDiffOn ℝ n (Function.uncurry (fun z θ => (A z θ) ^ m)) U :=
  (hA.pow m).congr (fun p _ => rfl)

theorem contDiffOn_uncurry_neg {A : ℝ → ℝ → ℝ} {U : Set (ℝ × ℝ)} {n : WithTop ℕ∞}
    (hA : ContDiffOn ℝ n (Function.uncurry A) U) :
    ContDiffOn ℝ n (Function.uncurry (fun z θ => -(A z θ))) U :=
  hA.neg.congr (fun p _ => rfl)

theorem contDiffOn_uncurry_z_mul {A : ℝ → ℝ → ℝ} {U : Set (ℝ × ℝ)} {n : WithTop ℕ∞}
    (hA : ContDiffOn ℝ n (Function.uncurry A) U) :
    ContDiffOn ℝ n (Function.uncurry (fun z θ => z * A z θ)) U :=
  (contDiffOn_fst.mul hA).congr (fun p _ => rfl)

theorem contDiffOn_uncurry_Dz {f : ℝ → ℝ → ℝ} {U : Set (ℝ × ℝ)} {n : WithTop ℕ∞}
    (h : ContDiffOn ℝ n (Function.uncurry (Work.Spaces.pz f)) U) :
    ContDiffOn ℝ n (Function.uncurry (Work.Spaces.Dz f)) U := by
  unfold Work.Spaces.Dz
  exact contDiffOn_uncurry_z_mul h

/-- `W2` is smooth on `(0,∞)`. -/
theorem contDiffOn_W2 {n : WithTop ℕ∞} : ContDiffOn ℝ n W2 (Set.Ioi 0) := by
  have h1 : ContDiffOn ℝ n (fun z : ℝ => (1 + z) ^ 2 / z ^ 2) (Set.Ioi 0) := by
    apply ContDiffOn.div
    · exact ((contDiff_const.add contDiff_id).pow 2).contDiffOn
    · exact (contDiff_id.pow 2).contDiffOn
    · intro z hz; exact pow_ne_zero 2 (ne_of_gt hz)
  have h2 : ContDiffOn ℝ n (fun z : ℝ => ((1 + z) ^ 2 / z ^ 2) ^ 2) (Set.Ioi 0) := h1.pow 2
  exact h2.congr (fun z _ => rfl)

/-- `p ↦ sin(2p.2)^q` is smooth on the half strip. -/
theorem contDiffOn_Sq {q : ℝ} {n : ℕ} :
    ContDiffOn ℝ n (fun θ : ℝ => Sq q θ) (Set.Ioo 0 (Real.pi / 2)) := by
  intro θ hθ
  have h1 : ContDiffAt ℝ (n : ℕ∞) (fun t : ℝ => Real.sin (2 * t)) θ := by fun_prop
  have h2 : ContDiffAt ℝ (n : ℕ∞) (fun x : ℝ => x ^ q) (Real.sin (2 * θ)) :=
    Real.contDiffAt_rpow_const (Or.inl (ne_of_gt (Real.sin_pos_of_mem_Ioo ⟨by linarith [hθ.1],
      by linarith [hθ.2, Real.pi_pos]⟩)))
  exact (h2.comp θ h1).contDiffWithinAt

/-- `p ↦ sin(2p.2)^q` is smooth on the half strip. -/
theorem contDiffOn_Sq_snd {q : ℝ} {n : ℕ} :
    ContDiffOn ℝ n (fun p : ℝ × ℝ => Sq q p.2) MStrip :=
  (contDiffOn_Sq (q := q) (n := n)).comp contDiffOn_snd (fun p hp => hp.2)

theorem contDiffOn_W2_fst {n : WithTop ℕ∞} :
    ContDiffOn ℝ n (fun p : ℝ × ℝ => W2 p.1) MStrip :=
  contDiffOn_W2.comp contDiffOn_fst (fun p hp => hp.1)

/-- The derivative of the angular weight, explicitly. -/
theorem hasDerivAt_Sq (q : ℝ) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    HasDerivAt (fun t : ℝ => Sq q t)
      (q * (Real.sin (2 * θ)) ^ (q - 1) * 2 * Real.cos (2 * θ)) θ := by
  have hne : Real.sin (2 * θ) ≠ 0 :=
    ne_of_gt (Real.sin_pos_of_mem_Ioo ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩)
  have hsin : HasDerivAt (fun t : ℝ => Real.sin (2 * t)) (2 * Real.cos (2 * θ)) θ := by
    have h1 : HasDerivAt (fun t : ℝ => 2 * t) 2 θ := by
      simpa using (hasDerivAt_id θ).const_mul (2 : ℝ)
    have h2 := Real.hasDerivAt_sin (2 * θ)
    have h3 := h2.comp θ h1
    have h4 : Real.cos (2 * θ) * 2 = 2 * Real.cos (2 * θ) := by ring
    rw [h4] at h3
    exact h3
  have h3 := (Real.hasDerivAt_rpow_const (x := Real.sin (2 * θ)) (p := q) (Or.inl hne)).comp θ hsin
  have hcomp : ((fun x : ℝ => x ^ q) ∘ fun t : ℝ => Real.sin (2 * t))
      = fun t : ℝ => (Real.sin (2 * t)) ^ q := rfl
  rw [hcomp] at h3
  simpa only [Sq, mul_assoc] using h3

/-- `dSq q` is the explicit continuous expression on `(0,π/2)`. -/
theorem dSq_eq (q : ℝ) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    dSq q θ = q * (Real.sin (2 * θ)) ^ (q - 1) * 2 * Real.cos (2 * θ) := by
  rw [dSq]
  exact (hasDerivAt_Sq q hθ).deriv

/-- `dSq q` is continuous on `(0,π/2)`. -/
theorem continuousOn_dSq {q : ℝ} :
    ContinuousOn (dSq q) (Set.Ioo 0 (Real.pi / 2)) := by
  have hsin : ContinuousOn (fun θ : ℝ => Real.sin (2 * θ)) (Set.Ioo 0 (Real.pi / 2)) := by
    fun_prop
  have hne : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), Real.sin (2 * θ) ≠ 0 := by
    intro θ hθ
    exact ne_of_gt (Real.sin_pos_of_mem_Ioo
      ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩)
  have hpow : ContinuousOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (q - 1))
      (Set.Ioo 0 (Real.pi / 2)) := by
    refine ContinuousOn.rpow_const hsin ?_
    intro θ hθ
    exact Or.inl (hne θ hθ)
  have hcos : ContinuousOn (fun θ : ℝ => Real.cos (2 * θ)) (Set.Ioo 0 (Real.pi / 2)) := by
    fun_prop
  have hmain : ContinuousOn (fun θ : ℝ => q * (Real.sin (2 * θ)) ^ (q - 1) * 2 * Real.cos (2 * θ))
      (Set.Ioo 0 (Real.pi / 2)) :=
    (((continuousOn_const.mul hpow).mul continuousOn_const).mul hcos)
  exact hmain.congr (fun θ hθ => dSq_eq q hθ)


/-! ## Vanishing of the elementary factors -/

/-- Vanishing is preserved by adding the weights `W2 z · B z θ`. -/
theorem Van_wB {A B : ℝ → ℝ → ℝ} (hA : Van A) :
    Van (fun z θ => A z θ * W2 z * B z θ) :=
  Van.congr (Van.mul (f := A) (g := fun z θ => W2 z * B z θ) hA) (fun z θ => by ring)

/-- Vanishing is preserved by adding the weights `W2 z · ξ z · B z θ`. -/
theorem Van_wB3 {A B : ℝ → ℝ → ℝ} (hA : Van A) :
    Van (fun z θ => A z θ * W2 z * xi z * B z θ) :=
  Van.congr (Van.mul (f := A) (g := fun z θ => W2 z * xi z * B z θ) hA) (fun z θ => by ring)

theorem Van_thFlC {q : ℝ} {v : ℝ → ℝ → ℝ} (h1 : Van (Work.Spaces.Dz v))
    (h2 : Van (Work.Spaces.Dz (Work.Spaces.pth v))) : Van (thFlC q v) :=
  Van.congr (Van_wB (A := fun z θ => Work.Spaces.Dz v z θ * Work.Spaces.Dz (Work.Spaces.pth v) z θ)
    (B := fun z θ => Sq q θ)
    (Van.mul (f := Work.Spaces.Dz v) (g := Work.Spaces.Dz (Work.Spaces.pth v)) h1))
    (fun z θ => rfl)

theorem Van_zFlC {q : ℝ} {v : ℝ → ℝ → ℝ} (h1 : Van (Work.Spaces.Dz v))
    (h2 : Van (Work.Spaces.pth (Work.Spaces.pth v))) : Van (zFlC q v) := by
  have hA : Van (fun z θ => z * Work.Spaces.Dz v z θ) := Van.zmul h1
  have hB : Van (fun z θ => z * Work.Spaces.Dz v z θ * Work.Spaces.pth (Work.Spaces.pth v) z θ) :=
    Van.mul (f := fun z θ => z * Work.Spaces.Dz v z θ)
      (g := Work.Spaces.pth (Work.Spaces.pth v)) hA
  have hC : Van (fun z θ => (z * Work.Spaces.Dz v z θ
      * Work.Spaces.pth (Work.Spaces.pth v) z θ) * W2 z * Sq q θ) := Van_wB (B := fun z θ => Sq q θ) hB
  exact Van.congr hC.neg (fun z θ => rfl)

theorem Van_FL {q : ℝ} {v : ℝ → ℝ → ℝ} (h : Van (Work.Spaces.Dz (Work.Spaces.pth v))) :
    Van (FL q v) :=
  Van.congr (Van_wB (A := fun z θ => (Work.Spaces.Dz (Work.Spaces.pth v) z θ) ^ 2)
    (B := fun z θ => Sq q θ) (Van.sq h)) (fun z θ => rfl)

theorem Van_FT1 {q : ℝ} {v : ℝ → ℝ → ℝ} (h : Van (Work.Spaces.pth (Work.Spaces.pth v))) :
    Van (FT1 q v) :=
  Van.congr (Van_wB (A := fun z θ => Work.Spaces.Dz (Work.Spaces.Dz v) z θ
      * Work.Spaces.pth (Work.Spaces.pth v) z θ) (B := fun z θ => Sq q θ)
    (Van.mul' (f := Work.Spaces.Dz (Work.Spaces.Dz v))
      (g := Work.Spaces.pth (Work.Spaces.pth v)) h)) (fun z θ => rfl)

theorem Van_FT2 {q : ℝ} {v : ℝ → ℝ → ℝ} (h : Van (Work.Spaces.Dz (Work.Spaces.pth v))) :
    Van (FT2 q v) :=
  Van.congr (Van_wB (A := fun z θ => Work.Spaces.Dz v z θ
      * Work.Spaces.Dz (Work.Spaces.pth v) z θ) (B := fun z θ => dSq q θ)
    (Van.mul' (f := Work.Spaces.Dz v) (g := Work.Spaces.Dz (Work.Spaces.pth v)) h))
    (fun z θ => rfl)

theorem Van_FT3 {q : ℝ} {v : ℝ → ℝ → ℝ} (h : Van (Work.Spaces.pth (Work.Spaces.pth v))) :
    Van (FT3 q v) :=
  Van.congr (Van_wB3 (A := fun z θ => Work.Spaces.Dz v z θ
      * Work.Spaces.pth (Work.Spaces.pth v) z θ) (B := fun z θ => Sq q θ)
    (Van.mul' (f := Work.Spaces.Dz v) (g := Work.Spaces.pth (Work.Spaces.pth v)) h))
    (fun z θ => rfl)

/-! ## Smoothness and continuity of the pieces -/

/-- `ξ` is smooth on `(0,∞)`. -/
theorem contDiffOn_xi {n : WithTop ℕ∞} : ContDiffOn ℝ n xi (Set.Ioi 0) := by
  apply ContDiffOn.div
  · exact (contDiff_id.sub contDiff_const).contDiffOn
  · exact (contDiff_const.add contDiff_id).contDiffOn
  · intro z hz
    exact ne_of_gt (by simp only [Set.mem_Ioi] at hz; linarith)

theorem contDiffOn_xi_fst {n : WithTop ℕ∞} :
    ContDiffOn ℝ n (fun p : ℝ × ℝ => xi p.1) MStrip :=
  contDiffOn_xi.comp contDiffOn_fst (fun p hp => hp.1)

theorem continuousOn_dSq_snd {q : ℝ} :
    ContinuousOn (fun p : ℝ × ℝ => dSq q p.2) MStrip :=
  (continuousOn_dSq (q := q)).comp continuousOn_snd (fun p hp => hp.2)

/-- The three derivatives of `v` that appear in the fluxes, and their smoothness. -/
theorem contDiffOn_fluxes {q : ℝ} {v : ℝ → ℝ → ℝ}
    (hv : ContDiffOn ℝ 3 (Function.uncurry v) MStrip) :
    ContDiffOn ℝ 2 (Function.uncurry (Work.Spaces.pz v)) MStrip ∧
    ContDiffOn ℝ 2 (Function.uncurry (Work.Spaces.pth v)) MStrip ∧
    ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.pz (Work.Spaces.pth v))) MStrip ∧
    ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.pth (Work.Spaces.pth v))) MStrip ∧
    ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.Dz v)) MStrip ∧
    ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.Dz (Work.Spaces.pth v))) MStrip ∧
    ContDiffOn ℝ 0 (Function.uncurry (Work.Spaces.Dz (Work.Spaces.Dz v))) MStrip ∧
    ContDiffOn ℝ 1 (zFl q v) MStrip ∧
    ContDiffOn ℝ 1 (thFl q v) MStrip := by
  have hpz1 : ContDiffOn ℝ 2 (Function.uncurry (Work.Spaces.pz v)) MStrip :=
    contDiffOn_uncurry_pz_succ isOpen_MStrip (n := 2) hv
  have hpth1 : ContDiffOn ℝ 2 (Function.uncurry (Work.Spaces.pth v)) MStrip :=
    contDiffOn_uncurry_pth_succ isOpen_MStrip (n := 2) hv
  have hpz2 : ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.pz (Work.Spaces.pth v))) MStrip :=
    contDiffOn_uncurry_pz_succ isOpen_MStrip (n := 1) hpth1
  have hpth2 : ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.pth (Work.Spaces.pth v))) MStrip :=
    contDiffOn_uncurry_pth_succ isOpen_MStrip (n := 1) hpth1
  have hDz : ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.Dz v)) MStrip :=
    contDiffOn_uncurry_Dz (hpz1.of_le (by norm_num))
  have hDzpth : ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.Dz (Work.Spaces.pth v))) MStrip :=
    contDiffOn_uncurry_Dz hpz2
  have hDDz : ContDiffOn ℝ 0 (Function.uncurry (Work.Spaces.Dz (Work.Spaces.Dz v))) MStrip :=
    contDiffOn_uncurry_Dz (contDiffOn_uncurry_pz_succ isOpen_MStrip (n := 0) hDz)
  refine ⟨hpz1, hpth1, hpz2, hpth2, hDz, hDzpth, hDDz, ?_, ?_⟩
  · -- `zFl`
    have h := ((((contDiffOn_fst.mul hDz).mul hpth2).mul contDiffOn_W2_fst).mul
      (contDiffOn_Sq_snd (q := q) (n := 1))).neg
    exact h.congr (fun p _ => rfl)
  · -- `thFl`
    have h := (((hDz.mul hDzpth).mul contDiffOn_W2_fst).mul
      (contDiffOn_Sq_snd (q := q) (n := 1)))
    exact h.congr (fun p _ => rfl)

/-- Continuity of the four integrands on the half strip. -/
theorem continuousOn_integrands {q : ℝ} {v : ℝ → ℝ → ℝ}
    (hDz : ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.Dz v)) MStrip)
    (hDzpth : ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.Dz (Work.Spaces.pth v))) MStrip)
    (hDDz : ContDiffOn ℝ 0 (Function.uncurry (Work.Spaces.Dz (Work.Spaces.Dz v))) MStrip)
    (hPP : ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.pth (Work.Spaces.pth v))) MStrip) :
    ContinuousOn (fun p : ℝ × ℝ => FL q v p.1 p.2) MStrip ∧
    ContinuousOn (fun p : ℝ × ℝ => FT1 q v p.1 p.2) MStrip ∧
    ContinuousOn (fun p : ℝ × ℝ => FT2 q v p.1 p.2) MStrip ∧
    ContinuousOn (fun p : ℝ × ℝ => FT3 q v p.1 p.2) MStrip := by
  have hW : ContinuousOn (fun p : ℝ × ℝ => W2 p.1) MStrip :=
    (contDiffOn_W2_fst (n := 0)).continuousOn
  have hSq : ContinuousOn (fun p : ℝ × ℝ => Sq q p.2) MStrip :=
    (contDiffOn_Sq_snd (q := q) (n := 0)).continuousOn
  have hdSq : ContinuousOn (fun p : ℝ × ℝ => dSq q p.2) MStrip := continuousOn_dSq_snd
  have hxi : ContinuousOn (fun p : ℝ × ℝ => xi p.1) MStrip :=
    (contDiffOn_xi_fst (n := 0)).continuousOn
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (((hDzpth.continuousOn.pow 2).mul hW).mul hSq).congr (fun p _ => rfl)
  · exact ((((hDDz.continuousOn).mul hPP.continuousOn).mul hW).mul hSq).congr (fun p _ => rfl)
  · exact (((hDz.continuousOn.mul hDzpth.continuousOn).mul hW).mul hdSq).congr (fun p _ => rfl)
  · exact ((((hDz.continuousOn.mul hPP.continuousOn).mul hW).mul hxi).mul hSq).congr
      (fun p _ => rfl)

/-! ## Reduction of the iterated integrals to the box, and linearity -/

/-- A function vanishing off `(0,π/2)` outside `[a,b]` has the same integral over both. -/
theorem setIntegral_Ioo_eq_intervalIntegral_of_support {f : ℝ → ℝ} {a b : ℝ}
    (ha : 0 < a) (hb : b < Real.pi / 2) (hab : a ≤ b)
    (hf : ∀ θ, 0 < θ → θ < Real.pi / 2 → (θ < a ∨ b < θ) → f θ = 0) :
    (∫ θ in Set.Ioo 0 (Real.pi / 2), f θ) = ∫ θ in a..b, f θ := by
  have h1 : (∫ θ in Set.Ioo 0 (Real.pi / 2), f θ) = ∫ θ in Set.Icc a b, f θ :=
    MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioo
      (fun x hx => ⟨lt_of_lt_of_le ha hx.1, lt_of_le_of_lt hx.2 hb⟩)
      (fun x hx => by
        have hx' : x ∉ Set.Icc a b := hx.2
        simp only [Set.mem_Icc, not_and_or, not_le] at hx'
        exact hf x hx.1.1 hx.1.2 hx')
  rw [h1, MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]

/-- A function vanishing off `(0,∞)` outside `[a,b]` has the same integral over both. -/
theorem setIntegral_Ioi_eq_intervalIntegral_of_support {f : ℝ → ℝ} {a b : ℝ} (ha : 0 < a)
    (hab : a ≤ b) (hf : ∀ z, 0 < z → (z < a ∨ b < z) → f z = 0) :
    (∫ z in Set.Ioi 0, f z) = ∫ z in a..b, f z := by
  have h1 : (∫ z in Set.Ioi 0, f z) = ∫ z in Set.Icc a b, f z :=
    MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
      (fun x hx => by simp only [Set.mem_Ioi]; linarith [hx.1, ha])
      (fun x hx => by
        have hx2 : x < a ∨ b < x := by
          simpa only [Set.mem_Icc, not_and_or, not_le] using hx.2
        exact hf x hx.1 hx2)
  rw [h1, MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]

/-- The iterated interval integral over the box is the integral over the product box. -/
theorem iterated_eq_boxIntegral {X : ℝ → ℝ → ℝ}
    (hX : IntegrableOn (fun p : ℝ × ℝ => X p.1 p.2) MBox volume) :
    (∫ z in (1 / 2 : ℝ)..2, ∫ θ in (Real.pi / 8)..(3 * Real.pi / 8), X z θ)
      = ∫ p in MBox, X p.1 p.2 := by
  have hab1 : (1 / 2 : ℝ) ≤ 2 := by norm_num
  have hab2 : Real.pi / 8 ≤ 3 * Real.pi / 8 := by linarith [Real.pi_pos]
  have h1 : (∫ z in (1 / 2 : ℝ)..2, ∫ θ in (Real.pi / 8)..(3 * Real.pi / 8), X z θ)
      = ∫ z in Set.Ioc (1 / 2 : ℝ) 2, ∫ θ in Set.Ioc (Real.pi / 8) (3 * Real.pi / 8),
          X z θ := by
    rw [intervalIntegral.integral_of_le hab1]
    exact setIntegral_congr_fun measurableSet_Ioc (fun z _ =>
      intervalIntegral.integral_of_le hab2)
  have h2 : (∫ z in Set.Ioc (1 / 2 : ℝ) 2, ∫ θ in Set.Ioc (Real.pi / 8) (3 * Real.pi / 8),
        X z θ)
      = ∫ z in Set.Icc (1 / 2 : ℝ) 2, ∫ θ in Set.Icc (Real.pi / 8) (3 * Real.pi / 8),
          X z θ := by
    rw [← MeasureTheory.integral_Icc_eq_integral_Ioc
      (f := fun z => ∫ θ in Set.Ioc (Real.pi / 8) (3 * Real.pi / 8), X z θ)
      (x := (1 / 2 : ℝ)) (y := 2)]
    exact setIntegral_congr_fun measurableSet_Icc (fun z _ =>
      (MeasureTheory.integral_Icc_eq_integral_Ioc (f := fun θ => X z θ)
        (x := Real.pi / 8) (y := 3 * Real.pi / 8)).symm)
  have h3 : (∫ z in Set.Icc (1 / 2 : ℝ) 2, ∫ θ in Set.Icc (Real.pi / 8) (3 * Real.pi / 8),
        X z θ)
      = ∫ p in MBox, X p.1 p.2 :=
    (setIntegral_prod (fun p : ℝ × ℝ => X p.1 p.2) hX).symm
  rw [h1, h2, h3]

/-- The target's iterated set integral equals the integral over the box, for a function
vanishing off the box. -/
theorem target_eq_boxIntegral {X : ℝ → ℝ → ℝ} (hvan : Van X)
    (hX : IntegrableOn (fun p : ℝ × ℝ => X p.1 p.2) MBox volume) :
    (∫ z in Set.Ioi 0, ∫ θ in Set.Ioo 0 (Real.pi / 2), X z θ)
      = ∫ p in MBox, X p.1 p.2 := by
  have hin : (∫ z in Set.Ioi 0, ∫ θ in Set.Ioo 0 (Real.pi / 2), X z θ)
      = ∫ z in Set.Ioi 0, ∫ θ in (Real.pi / 8)..(3 * Real.pi / 8), X z θ := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun z _ => ?_)
    refine setIntegral_Ioo_eq_intervalIntegral_of_support (a := Real.pi / 8)
      (b := 3 * Real.pi / 8) ?_ ?_ ?_ ?_
    · linarith [Real.pi_pos]
    · linarith [Real.pi_pos]
    · linarith [Real.pi_pos]
    · intro θ hθ1 hθ2 hθ
      exact hvan z θ (Or.inr (hθ.elim (fun h => notMem_Ioo_of_le (le_of_lt h))
        (fun h => notMem_Ioo_of_ge (le_of_lt h))))
  have hout : (∫ z in Set.Ioi 0, ∫ θ in (Real.pi / 8)..(3 * Real.pi / 8), X z θ)
      = ∫ z in (1 / 2 : ℝ)..2, ∫ θ in (Real.pi / 8)..(3 * Real.pi / 8), X z θ := by
    refine setIntegral_Ioi_eq_intervalIntegral_of_support (a := 1 / 2) (b := 2)
      (by norm_num) (by norm_num) ?_
    intro z hz hz'
    have h0 : ∀ θ, X z θ = 0 := fun θ =>
      hvan z θ (Or.inl (hz'.elim (fun h => notMem_Ioo_of_le (le_of_lt h))
        (fun h => notMem_Ioo_of_ge (le_of_lt h))))
    rw [show (fun θ => X z θ) = fun _ => 0 from funext h0]
    simp
  rw [hin, hout, iterated_eq_boxIntegral hX]

end Work.FTS.EllipticEst.Prop
