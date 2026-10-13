/-
Copyright: work module for the Elgindi finite-time singularity project.

# `STQ`: the `C^∞`-calculus of the interior class on the open quadrant

The target `Work.FTS.H2.STQ` is Elgindi's Proposition `SpecialTransport` (tex 1126) in the
interior class `Work.FTS.LocData.SmoothQuad` (`ContDiffOn ℝ Work.Stability.smoothOrder`,
`smoothOrder = ∞` — genuine `C^∞`, *not* the analytic order `⊤` used by
`Work.Spaces.SmoothInt`/`SmoothNbhd`).  This file collects the Leibniz rules and the
elementary `D_z`/`D_θ` calculus in that class, which the rest of the `STQ` development runs on.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.H2.Defs
import Submission.Work.FTS.H2.STSigma
import Submission.Work.FTS.LocData.SmoothChain
import Submission.Work.FTS.LocData.DzIter_mul_smoothQuad
import Submission.Work.FTS.LocData.DthIter_mul_smoothQuad
import Submission.Work.Spaces.DzDthIterCommOn

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2.STQ

set_option autoImplicit false

open Work.Spaces
open Work.FTS.LocData (SmoothQuad)

/-! ## Elementary closure properties of `SmoothQuad` -/

theorem SmoothQuad.pth {f : ℝ → ℝ → ℝ} (hf : SmoothQuad f) : SmoothQuad (Spaces.pth f) :=
  Work.FTS.LocData.contDiffOn_pth Work.Spaces.isOpen_quadU hf

theorem SmoothQuad.zslice {f : ℝ → ℝ → ℝ} (hf : SmoothQuad f) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    ContDiffOn ℝ Work.Stability.smoothOrder (fun z => f z θ) (Set.Ioi (-1)) :=
  hf.curry_z hθ

theorem SmoothQuad.thslice {f : ℝ → ℝ → ℝ} (hf : SmoothQuad f) {z : ℝ}
    (hz : (-1 : ℝ) < z) :
    ContDiffOn ℝ Work.Stability.smoothOrder (fun θ => f z θ) (Set.Ioo 0 (π / 2)) :=
  hf.curry_θ hz

/-! ## The Leibniz rules in the interior class -/

/-- Leibniz rule for `D_z^j` on the open quadrant, at a point with `z ∈ Iz`, `0 < θ < π/2`. -/
theorem DzIter_mul_quad {j : ℕ} {f g : ℝ → ℝ → ℝ} (hf : SmoothQuad f) (hg : SmoothQuad g)
    {z θ : ℝ} (hz : z ∈ Spaces.Iz) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    Spaces.DzIter j (fun z θ => f z θ * g z θ) z θ =
      ∑ b ∈ Finset.range (j + 1),
        (j.choose b : ℝ) * (Spaces.DzIter b f z θ * Spaces.DzIter (j - b) g z θ) :=
  Work.FTS.LocData.DzIter_mul_smoothQuad j f g hz (hf.curry_z hθ) (hg.curry_z hθ)

/-- Leibniz rule for `D_θ^i` on the open quadrant. -/
theorem DthIter_mul_quad {i : ℕ} {f g : ℝ → ℝ → ℝ} (hf : SmoothQuad f) (hg : SmoothQuad g)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    Spaces.DthIter i (fun z θ => f z θ * g z θ) z θ =
      ∑ a ∈ Finset.range (i + 1),
        (i.choose a : ℝ) * (Spaces.DthIter a f z θ * Spaces.DthIter (i - a) g z θ) :=
  Work.FTS.LocData.DthIter_mul_smoothQuad i f g hθ
    (Work.FTS.LocData.SmoothQuad.curry_θ hf (show (-1 : ℝ) < z by linarith))
    (Work.FTS.LocData.SmoothQuad.curry_θ hg (show (-1 : ℝ) < z by linarith))

/-- The same identity as an `EqOn` on the open quadrant (needed to commute it with `D_z^j`). -/
theorem DthIter_mul_eqOn_quad {i : ℕ} {f g : ℝ → ℝ → ℝ} (hf : SmoothQuad f)
    (hg : SmoothQuad g) :
    Set.EqOn (Function.uncurry (Spaces.DthIter i (fun z θ => f z θ * g z θ)))
      (Function.uncurry (fun z θ => ∑ a ∈ Finset.range (i + 1),
        (i.choose a : ℝ) * (Spaces.DthIter a f z θ * Spaces.DthIter (i - a) g z θ)))
      Spaces.quadU := by
  intro p hp
  obtain ⟨z, θ⟩ := p
  exact Work.FTS.LocData.DthIter_mul_smoothQuad i f g hp.2
    (Work.FTS.LocData.SmoothQuad.curry_θ hf hp.1)
    (Work.FTS.LocData.SmoothQuad.curry_θ hg hp.1)

/-! ## Linearity of `D_z^j` over a finite sum with constant coefficients -/

/-- `D_z^j` acts termwise on a finite sum with constant coefficients, on an open set on which
every summand is `C^∞`. -/
theorem DzIter_sum_eqOn {ι : Type*} (s : Finset ι) (c : ι → ℝ) (F : ι → ℝ → ℝ → ℝ)
    {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (hF : ∀ i ∈ s, ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry (F i)) V) (j : ℕ) :
    Set.EqOn (Function.uncurry (Spaces.DzIter j (fun z θ => ∑ i ∈ s, c i * F i z θ)))
      (Function.uncurry (fun z θ => ∑ i ∈ s, c i * Spaces.DzIter j (F i) z θ)) V := by
  induction j with
  | zero => intro p hp; rfl
  | succ j ih =>
    have hFs : ∀ i ∈ s, ContDiffOn ℝ Work.Stability.smoothOrder
        (Function.uncurry (Spaces.DzIter j (F i))) V := fun i hi =>
      Work.FTS.LocData.contDiffOn_DzIter hV (hF i hi) j
    intro p hp
    obtain ⟨z, θ⟩ := p
    have hdiff : ∀ i ∈ s, DifferentiableAt ℝ (fun z' => Spaces.DzIter j (F i) z' θ) z :=
      fun i hi => by
        have h1 : DifferentiableAt ℝ (Function.uncurry (Spaces.DzIter j (F i))) (z, θ) :=
          ((hFs i hi).contDiffAt (hV.mem_nhds hp)).differentiableAt
            (by simp [Work.FTS.LocData.smoothOrder_ne_zero])
        have h2 : DifferentiableAt ℝ (fun e : ℝ => (e, θ)) z :=
          (hasFDerivAt_prodMk_left z θ).differentiableAt
        have h3 := h1.comp z h2
        simpa [Function.comp_def, Function.uncurry] using h3
    have hcongr : Spaces.pz (Spaces.DzIter j (fun z θ => ∑ i ∈ s, c i * F i z θ)) z θ
        = Spaces.pz (fun z θ => ∑ i ∈ s, c i * Spaces.DzIter j (F i) z θ) z θ :=
      Spaces.pz_congr_of_isOpen hV ih hp
    have h1 : Spaces.pz (fun z θ => ∑ i ∈ s, c i * Spaces.DzIter j (F i) z θ) z θ
        = ∑ i ∈ s, c i * Spaces.pz (Spaces.DzIter j (F i)) z θ := by
      show deriv (fun z' => ∑ i ∈ s, c i * Spaces.DzIter j (F i) z' θ) z = _
      have hfun : (fun z' => ∑ i ∈ s, c i * Spaces.DzIter j (F i) z' θ)
          = ∑ i ∈ s, (fun z' => c i * Spaces.DzIter j (F i) z' θ) := by
        funext z'; rw [Finset.sum_apply]
      rw [hfun, deriv_sum (fun i hi => (hdiff i hi).const_mul (c i))]
      exact Finset.sum_congr rfl fun i hi => deriv_const_mul_field (c i)
    show Spaces.Dz (Spaces.DzIter j (fun z θ => ∑ i ∈ s, c i * F i z θ)) z θ
        = ∑ i ∈ s, c i * Spaces.Dz (Spaces.DzIter j (F i)) z θ
    show z * Spaces.pz (Spaces.DzIter j (fun z θ => ∑ i ∈ s, c i * F i z θ)) z θ
        = ∑ i ∈ s, c i * (z * Spaces.pz (Spaces.DzIter j (F i)) z θ)
    rw [hcongr, h1, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i hi => by ring

/-! ## The two-operator Leibniz rule for `D_z^j D_θ^i` -/

/-- **The mixed Leibniz rule in the interior class**:
`D_z^j D_θ^i (f·g) = Σ_a Σ_b C(i,a) C(j,b) D_z^b D_θ^a f · D_z^{j-b} D_θ^{i-a} g` at a point
of the open quadrant.  It is the composition of the two one-operator rules (the `D_θ`-rule
applied to the product, then the `D_z`-rule on each summand); no two-operator commutator is
involved. -/
theorem mixed_mul_quad {j i : ℕ} {f g : ℝ → ℝ → ℝ} (hf : SmoothQuad f) (hg : SmoothQuad g)
    {z θ : ℝ} (hz : z ∈ Spaces.Iz) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    Spaces.mixed j i (fun z θ => f z θ * g z θ) z θ =
      ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
        ((i.choose a : ℝ) * (j.choose b : ℝ))
          * (Spaces.mixed b a f z θ * Spaces.mixed (j - b) (i - a) g z θ) := by
  have hz1 : (-1 : ℝ) < z := by
    rw [Spaces.Iz, Set.mem_Ici] at hz; linarith
  have hp : (z, θ) ∈ Spaces.quadU := ⟨hz1, hθ⟩
  -- step 1: `D_θ^i(fg)` expands on the open quadrant
  have hfun := DthIter_mul_eqOn_quad (i := i) hf hg
  -- step 2: apply `D_z^j` to both sides
  have h2 := Work.FTS.H2.DzIter_congr_of_isOpen Work.Spaces.isOpen_quadU hfun j hp
  -- step 3: linearity of `D_z^j` over the finite sum
  have h3 := DzIter_sum_eqOn (Finset.range (i + 1)) (fun a => (i.choose a : ℝ))
    (fun a => fun z θ => Spaces.DthIter a f z θ * Spaces.DthIter (i - a) g z θ)
    Work.Spaces.isOpen_quadU ?_ j hp
  · -- step 4: expand each `D_z^j` of a product
    simp only [Function.uncurry] at h2 h3
    rw [show Spaces.mixed j i (fun z θ => f z θ * g z θ) z θ
          = Spaces.DzIter j (Spaces.DthIter i (fun z θ => f z θ * g z θ)) z θ from rfl, h2, h3]
    have hterm : ∀ a ∈ Finset.range (i + 1),
        Spaces.DzIter j (fun z θ => Spaces.DthIter a f z θ * Spaces.DthIter (i - a) g z θ) z θ
          = ∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ)
              * (Spaces.mixed b a f z θ * Spaces.mixed (j - b) (i - a) g z θ) := by
      intro a ha
      exact DzIter_mul_quad (hf.DthIter a) (hg.DthIter (i - a)) hz hθ
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [hterm a ha, Finset.mul_sum]
    exact Finset.sum_congr rfl fun b hb => by ring
  · intro a ha
    exact Work.FTS.LocData.smoothQuad_mul (hf.DthIter a) (hg.DthIter (i - a))

/-! ## Linearity of `D_z^j` over a finite sum with `θ`-dependent coefficients -/

/-- `D_z` acts termwise on a finite sum with `θ`-dependent coefficients. -/
theorem Dz_sum_theta_coeff_eqOn {ι : Type*} (s : Finset ι) (c : ι → ℝ → ℝ)
    (F : ι → ℝ → ℝ → ℝ) {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (hF : ∀ i ∈ s, ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry (F i)) V) :
    Set.EqOn (Function.uncurry (Spaces.Dz (fun z θ => ∑ i ∈ s, c i θ * F i z θ)))
      (Function.uncurry (fun z θ => ∑ i ∈ s, c i θ * Spaces.Dz (F i) z θ)) V := by
  intro p hp
  obtain ⟨z, θ⟩ := p
  have hdiff : ∀ i ∈ s, DifferentiableAt ℝ (fun z' => F i z' θ) z := fun i hi => by
    have h1 : DifferentiableAt ℝ (Function.uncurry (F i)) (z, θ) :=
      ((hF i hi).contDiffAt (hV.mem_nhds hp)).differentiableAt
        (by simp [Work.FTS.LocData.smoothOrder_ne_zero])
    have h2 : DifferentiableAt ℝ (fun e : ℝ => (e, θ)) z :=
      (hasFDerivAt_prodMk_left z θ).differentiableAt
    have h3 := h1.comp z h2
    simpa [Function.comp_def, Function.uncurry] using h3
  have h1 : Spaces.pz (fun z θ => ∑ i ∈ s, c i θ * F i z θ) z θ
      = ∑ i ∈ s, c i θ * Spaces.pz (F i) z θ := by
    show deriv (fun z' => ∑ i ∈ s, c i θ * F i z' θ) z = _
    have hfun : (fun z' => ∑ i ∈ s, c i θ * F i z' θ)
        = ∑ i ∈ s, (fun z' => c i θ * F i z' θ) := by
      funext z'; rw [Finset.sum_apply]
    rw [hfun, deriv_sum (fun i hi => (hdiff i hi).const_mul (c i θ))]
    exact Finset.sum_congr rfl fun i hi => deriv_const_mul_field (c i θ)
  show z * Spaces.pz (fun z θ => ∑ i ∈ s, c i θ * F i z θ) z θ
      = ∑ i ∈ s, c i θ * (z * Spaces.pz (F i) z θ)
  rw [h1, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i hi => by ring

/-- The `pz`-form of `Dz_sum_theta_coeff_eqOn`. -/
theorem pz_sum_theta_coeff_eqOn {ι : Type*} (s : Finset ι) (c : ι → ℝ → ℝ)
    (F : ι → ℝ → ℝ → ℝ) {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (hF : ∀ i ∈ s, ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry (F i)) V) :
    Set.EqOn (Function.uncurry (Spaces.pz (fun z θ => ∑ i ∈ s, c i θ * F i z θ)))
      (Function.uncurry (fun z θ => ∑ i ∈ s, c i θ * Spaces.pz (F i) z θ)) V := by
  intro p hp
  obtain ⟨z, θ⟩ := p
  have hdiff : ∀ i ∈ s, DifferentiableAt ℝ (fun z' => F i z' θ) z := fun i hi => by
    have h1 : DifferentiableAt ℝ (Function.uncurry (F i)) (z, θ) :=
      ((hF i hi).contDiffAt (hV.mem_nhds hp)).differentiableAt
        (by simp [Work.FTS.LocData.smoothOrder_ne_zero])
    have h2 : DifferentiableAt ℝ (fun e : ℝ => (e, θ)) z :=
      (hasFDerivAt_prodMk_left z θ).differentiableAt
    have h3 := h1.comp z h2
    simpa [Function.comp_def, Function.uncurry] using h3
  show deriv (fun z' => ∑ i ∈ s, c i θ * F i z' θ) z
      = ∑ i ∈ s, c i θ * Spaces.pz (F i) z θ
  have hfun : (fun z' => ∑ i ∈ s, c i θ * F i z' θ)
      = ∑ i ∈ s, (fun z' => c i θ * F i z' θ) := by
    funext z'; rw [Finset.sum_apply]
  rw [hfun, deriv_sum (fun i hi => (hdiff i hi).const_mul (c i θ))]
  exact Finset.sum_congr rfl fun i hi => deriv_const_mul_field (c i θ)

/-- The iterated form of `Dz_sum_theta_coeff_eqOn`. -/
theorem DzIter_sum_theta_coeff_eqOn {ι : Type*} (s : Finset ι) (c : ι → ℝ → ℝ)
    (F : ι → ℝ → ℝ → ℝ) {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (hF : ∀ i ∈ s, ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry (F i)) V)
    (j : ℕ) :
    Set.EqOn (Function.uncurry (Spaces.DzIter j (fun z θ => ∑ i ∈ s, c i θ * F i z θ)))
      (Function.uncurry (fun z θ => ∑ i ∈ s, c i θ * Spaces.DzIter j (F i) z θ)) V := by
  induction j with
  | zero => intro p hp; rfl
  | succ j ih =>
    have hFs : ∀ i ∈ s, ContDiffOn ℝ Work.Stability.smoothOrder
        (Function.uncurry (Spaces.DzIter j (F i))) V := fun i hi =>
      Work.FTS.LocData.contDiffOn_DzIter hV (hF i hi) j
    have hstep' := pz_sum_theta_coeff_eqOn s c (fun i => Spaces.DzIter j (F i)) hV hFs
    intro p hp
    obtain ⟨z, θ⟩ := p
    have hcongr : Spaces.pz (Spaces.DzIter j (fun z θ => ∑ i ∈ s, c i θ * F i z θ)) z θ
        = Spaces.pz (fun z θ => ∑ i ∈ s, c i θ * Spaces.DzIter j (F i) z θ) z θ :=
      Spaces.pz_congr_of_isOpen hV ih hp
    have h2 := hstep' hp
    simp only [Function.uncurry] at h2
    show Spaces.Dz (Spaces.DzIter j (fun z θ => ∑ i ∈ s, c i θ * F i z θ)) z θ
        = ∑ i ∈ s, c i θ * Spaces.Dz (Spaces.DzIter j (F i)) z θ
    show z * Spaces.pz (Spaces.DzIter j (fun z θ => ∑ i ∈ s, c i θ * F i z θ)) z θ
        = ∑ i ∈ s, c i θ * (z * Spaces.pz (Spaces.DzIter j (F i)) z θ)
    rw [hcongr, h2, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i hi => by ring

end Work.FTS.H2.STQ
