import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Submission.Work.Spaces.Defs
import Submission.Work.Construction.Defs
import Submission.Work.Spaces.CurrySmooth
import Submission.Work.FTS_RegExport.RXT.SysAux.PieceDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXT.SysAux.PieceCalc` — calculus for separable data on the open quadrant

Every function occurring in `explicit_piece_bounds` is an analytic function of `(z,θ)` on the
open quadrant `Q0 = (0,∞) × (0,π/2)` that is a finite sum of products `A(z)·B(θ)`.  This file
provides the two calculus tools needed to exploit that structure:

* **congruence** of `D_z^j D_θ^i` under agreement on an open set
  (`DzIter_congr_of_isOpen`, `DthIter_congr_of_isOpen`, `mixed_congr_of_isOpen`) — used to
  replace the explicit expression of a piece by its simplified closed form;
* **additivity** of `D_z^j D_θ^i` over a sum of two analytic functions
  (`DthIter_add_eqOn`, `DzIter_add_eqOn`, `mixed_add`) — used to split a finite sum of
  products into its summands.

Everything rests on `[propext, Classical.choice, Quot.sound]` only (the imports
`Spaces.CurrySmooth` and `Spaces.Defs` are `sorry`-free).
-/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_RegExport.RXT.SysAux

set_option autoImplicit false

/-- The open quadrant `(0,∞) × (0,π/2)`. -/
def Q0 : Set (ℝ × ℝ) := Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)

theorem isOpen_Q0 : IsOpen Q0 := isOpen_Ioi.prod isOpen_Ioo

/-! ## §1  `D_θ` and `D_z` lower the order of differentiability -/

/-- `D_θ` of a function analytic on an open set is analytic there. -/
theorem contDiffOn_uncurry_Dth_of_contDiffOn {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    {G : ℝ → ℝ → ℝ} (h : ContDiffOn ℝ ⊤ (Function.uncurry G) V) :
    ContDiffOn ℝ ⊤ (Function.uncurry (Work.Spaces.Dth G)) V := by
  have hfun : Function.uncurry (Work.Spaces.Dth G)
      = (fun p : ℝ × ℝ => Real.sin (2 * p.2)) * Function.uncurry (Work.Spaces.pth G) := by
    funext p
    obtain ⟨z, θ⟩ := p
    rfl
  rw [hfun]
  exact ((Real.contDiff_sin.comp (contDiff_const.mul contDiff_snd)).contDiffOn).mul
    (Work.Spaces.contDiffOn_uncurry_pth hV h)

/-- `D_z` of a function analytic on an open set is analytic there. -/
theorem contDiffOn_uncurry_Dz_of_contDiffOn {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    {G : ℝ → ℝ → ℝ} (h : ContDiffOn ℝ ⊤ (Function.uncurry G) V) :
    ContDiffOn ℝ ⊤ (Function.uncurry (Work.Spaces.Dz G)) V := by
  have hfun : Function.uncurry (Work.Spaces.Dz G)
      = (fun p : ℝ × ℝ => p.1) * Function.uncurry (Work.Spaces.pz G) := by
    funext p
    obtain ⟨z, θ⟩ := p
    rfl
  rw [hfun]
  exact (contDiffOn_fst : ContDiffOn ℝ ⊤ (Prod.fst : ℝ × ℝ → ℝ) V).mul
    (Work.Spaces.contDiffOn_uncurry_pz hV h)

/-- `D_θ^i` of a function analytic on an open set is analytic there. -/
theorem contDiffOn_uncurry_DthIter_of_contDiffOn {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    {G : ℝ → ℝ → ℝ} (h : ContDiffOn ℝ ⊤ (Function.uncurry G) V) (i : ℕ) :
    ContDiffOn ℝ ⊤ (Function.uncurry (Work.Spaces.DthIter i G)) V := by
  induction i with
  | zero => exact h
  | succ i ih =>
      rw [Work.Spaces.DthIter_succ]
      exact contDiffOn_uncurry_Dth_of_contDiffOn hV ih

/-- `D_z^j` of a function analytic on an open set is analytic there. -/
theorem contDiffOn_uncurry_DzIter_of_contDiffOn {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    {G : ℝ → ℝ → ℝ} (h : ContDiffOn ℝ ⊤ (Function.uncurry G) V) (j : ℕ) :
    ContDiffOn ℝ ⊤ (Function.uncurry (Work.Spaces.DzIter j G)) V := by
  induction j with
  | zero => exact h
  | succ j ih =>
      rw [Work.Spaces.DzIter_succ]
      exact contDiffOn_uncurry_Dz_of_contDiffOn hV ih

/-! ## §2  Congruence of the iterated operators on an open set -/

/-- `D_θ` respects agreement on an open set. -/
theorem Dth_congr_of_isOpen {V : Set (ℝ × ℝ)} (hV : IsOpen V) {f g : ℝ → ℝ → ℝ}
    (h : Set.EqOn (Function.uncurry f) (Function.uncurry g) V) {z θ : ℝ}
    (hz : (z, θ) ∈ V) : Work.Spaces.Dth f z θ = Work.Spaces.Dth g z θ := by
  have hnb : ∀ᶠ θ' in 𝓝 θ, (z, θ') ∈ V :=
    (Continuous.prodMk_right z).continuousAt.eventually (hV.mem_nhds hz)
  have hev : (fun θ' => f z θ') =ᶠ[𝓝 θ] (fun θ' => g z θ') :=
    hnb.mono (fun θ' hθ' => h hθ')
  simp only [Work.Spaces.Dth, Work.Spaces.pth]
  rw [hev.deriv_eq]

/-- `D_z` respects agreement on an open set. -/
theorem Dz_congr_of_isOpen {V : Set (ℝ × ℝ)} (hV : IsOpen V) {f g : ℝ → ℝ → ℝ}
    (h : Set.EqOn (Function.uncurry f) (Function.uncurry g) V) {z θ : ℝ}
    (hz : (z, θ) ∈ V) : Work.Spaces.Dz f z θ = Work.Spaces.Dz g z θ := by
  have hnb : ∀ᶠ z' in 𝓝 z, (z', θ) ∈ V :=
    (Continuous.prodMk_left θ).continuousAt.eventually (hV.mem_nhds hz)
  have hev : (fun z' => f z' θ) =ᶠ[𝓝 z] (fun z' => g z' θ) :=
    hnb.mono (fun z' hz' => h hz')
  simp only [Work.Spaces.Dz, Work.Spaces.pz]
  rw [hev.deriv_eq]

/-- `D_θ^i` respects agreement on an open set. -/
theorem DthIter_congr_of_isOpen {V : Set (ℝ × ℝ)} (hV : IsOpen V) {f g : ℝ → ℝ → ℝ}
    (h : Set.EqOn (Function.uncurry f) (Function.uncurry g) V) (i : ℕ) :
    ∀ z θ : ℝ, (z, θ) ∈ V → Work.Spaces.DthIter i f z θ = Work.Spaces.DthIter i g z θ := by
  induction i with
  | zero => intro z θ hz; exact h hz
  | succ i ih =>
      intro z θ hz
      exact Dth_congr_of_isOpen hV (fun p hp => ih p.1 p.2 hp) hz

/-- `D_z^j` respects agreement on an open set. -/
theorem DzIter_congr_of_isOpen {V : Set (ℝ × ℝ)} (hV : IsOpen V) {f g : ℝ → ℝ → ℝ}
    (h : Set.EqOn (Function.uncurry f) (Function.uncurry g) V) (j : ℕ) :
    ∀ z θ : ℝ, (z, θ) ∈ V → Work.Spaces.DzIter j f z θ = Work.Spaces.DzIter j g z θ := by
  induction j with
  | zero => intro z θ hz; exact h hz
  | succ j ih =>
      intro z θ hz
      exact Dz_congr_of_isOpen hV (fun p hp => ih p.1 p.2 hp) hz

/-- **`mixed` respects agreement on an open set.** -/
theorem mixed_congr_of_isOpen {V : Set (ℝ × ℝ)} (hV : IsOpen V) {f g : ℝ → ℝ → ℝ}
    (h : Set.EqOn (Function.uncurry f) (Function.uncurry g) V) (j i : ℕ) :
    ∀ z θ : ℝ, (z, θ) ∈ V → Work.Spaces.mixed j i f z θ = Work.Spaces.mixed j i g z θ := by
  have h1 := DthIter_congr_of_isOpen hV h i
  intro z θ hz
  simp only [Work.Spaces.mixed]
  exact DzIter_congr_of_isOpen hV (fun p hp => h1 p.1 p.2 hp) j z θ hz

/-! ## §3  Additivity of the iterated operators over a sum -/

/-- `D_θ` of a sum of two analytic functions. -/
theorem Dth_add_pt {V : Set (ℝ × ℝ)} (hV : IsOpen V) {u v : ℝ → ℝ → ℝ}
    (hu : ContDiffOn ℝ ⊤ (Function.uncurry u) V) (hv : ContDiffOn ℝ ⊤ (Function.uncurry v) V)
    {z θ : ℝ} (h : (z, θ) ∈ V) :
    Work.Spaces.Dth (u + v) z θ = Work.Spaces.Dth u z θ + Work.Spaces.Dth v z θ := by
  have hdu : DifferentiableAt ℝ (fun θ' : ℝ => u z θ') θ :=
    Work.Spaces.differentiableAt_curry_right
      ((hu.differentiableOn (n := ⊤) (by simp)).differentiableAt (hV.mem_nhds h))
  have hdv : DifferentiableAt ℝ (fun θ' : ℝ => v z θ') θ :=
    Work.Spaces.differentiableAt_curry_right
      ((hv.differentiableOn (n := ⊤) (by simp)).differentiableAt (hV.mem_nhds h))
  show Real.sin (2 * θ) * deriv (fun θ' => (u + v) z θ') θ
      = Real.sin (2 * θ) * deriv (fun θ' => u z θ') θ
        + Real.sin (2 * θ) * deriv (fun θ' => v z θ') θ
  rw [show (fun θ' : ℝ => (u + v) z θ') = (fun θ' : ℝ => u z θ') + (fun θ' => v z θ')
      from by funext θ'; rfl, deriv_add hdu hdv]
  ring

/-- `D_z` of a sum of two analytic functions. -/
theorem Dz_add_pt {V : Set (ℝ × ℝ)} (hV : IsOpen V) {u v : ℝ → ℝ → ℝ}
    (hu : ContDiffOn ℝ ⊤ (Function.uncurry u) V) (hv : ContDiffOn ℝ ⊤ (Function.uncurry v) V)
    {z θ : ℝ} (h : (z, θ) ∈ V) :
    Work.Spaces.Dz (u + v) z θ = Work.Spaces.Dz u z θ + Work.Spaces.Dz v z θ := by
  have hdu : DifferentiableAt ℝ (fun z' : ℝ => u z' θ) z :=
    Work.Spaces.differentiableAt_curry_left
      ((hu.differentiableOn (n := ⊤) (by simp)).differentiableAt (hV.mem_nhds h))
  have hdv : DifferentiableAt ℝ (fun z' : ℝ => v z' θ) z :=
    Work.Spaces.differentiableAt_curry_left
      ((hv.differentiableOn (n := ⊤) (by simp)).differentiableAt (hV.mem_nhds h))
  show z * deriv (fun z' => (u + v) z' θ) z
      = z * deriv (fun z' => u z' θ) z + z * deriv (fun z' => v z' θ) z
  rw [show (fun z' : ℝ => (u + v) z' θ) = (fun z' : ℝ => u z' θ) + (fun z' => v z' θ)
      from by funext z'; rfl, deriv_add hdu hdv]
  ring

/-- `D_θ^i` of a sum of two analytic functions. -/
theorem DthIter_add_eqOn {V : Set (ℝ × ℝ)} (hV : IsOpen V) {f g : ℝ → ℝ → ℝ}
    (hf : ContDiffOn ℝ ⊤ (Function.uncurry f) V) (hg : ContDiffOn ℝ ⊤ (Function.uncurry g) V)
    (i : ℕ) :
    ∀ z θ : ℝ, (z, θ) ∈ V →
      Work.Spaces.DthIter i (f + g) z θ
        = Work.Spaces.DthIter i f z θ + Work.Spaces.DthIter i g z θ := by
  induction i with
  | zero => intro z θ hz; rfl
  | succ i ih =>
      intro z θ hz
      have hf' := contDiffOn_uncurry_DthIter_of_contDiffOn hV hf i
      have hg' := contDiffOn_uncurry_DthIter_of_contDiffOn hV hg i
      have hEq : Set.EqOn (Function.uncurry (Work.Spaces.DthIter i (f + g)))
          (Function.uncurry (Work.Spaces.DthIter i f + Work.Spaces.DthIter i g)) V := by
        intro p hp
        obtain ⟨z', θ'⟩ := p
        exact ih z' θ' hp
      show Work.Spaces.Dth (Work.Spaces.DthIter i (f + g)) z θ
          = Work.Spaces.Dth (Work.Spaces.DthIter i f) z θ
            + Work.Spaces.Dth (Work.Spaces.DthIter i g) z θ
      rw [Dth_congr_of_isOpen hV hEq hz]
      exact Dth_add_pt hV hf' hg' hz

/-- `D_z^j` of a sum of two analytic functions. -/
theorem DzIter_add_eqOn {V : Set (ℝ × ℝ)} (hV : IsOpen V) {f g : ℝ → ℝ → ℝ}
    (hf : ContDiffOn ℝ ⊤ (Function.uncurry f) V) (hg : ContDiffOn ℝ ⊤ (Function.uncurry g) V)
    (j : ℕ) :
    ∀ z θ : ℝ, (z, θ) ∈ V →
      Work.Spaces.DzIter j (f + g) z θ
        = Work.Spaces.DzIter j f z θ + Work.Spaces.DzIter j g z θ := by
  induction j with
  | zero => intro z θ hz; rfl
  | succ j ih =>
      intro z θ hz
      have hf' := contDiffOn_uncurry_DzIter_of_contDiffOn hV hf j
      have hg' := contDiffOn_uncurry_DzIter_of_contDiffOn hV hg j
      have hEq : Set.EqOn (Function.uncurry (Work.Spaces.DzIter j (f + g)))
          (Function.uncurry (Work.Spaces.DzIter j f + Work.Spaces.DzIter j g)) V := by
        intro p hp
        obtain ⟨z', θ'⟩ := p
        exact ih z' θ' hp
      show Work.Spaces.Dz (Work.Spaces.DzIter j (f + g)) z θ
          = Work.Spaces.Dz (Work.Spaces.DzIter j f) z θ
            + Work.Spaces.Dz (Work.Spaces.DzIter j g) z θ
      rw [Dz_congr_of_isOpen hV hEq hz]
      exact Dz_add_pt hV hf' hg' hz

/-- **`mixed` is additive over a sum of two analytic functions.** -/
theorem mixed_add {V : Set (ℝ × ℝ)} (hV : IsOpen V) {f g : ℝ → ℝ → ℝ}
    (hf : ContDiffOn ℝ ⊤ (Function.uncurry f) V) (hg : ContDiffOn ℝ ⊤ (Function.uncurry g) V)
    (j i : ℕ) {z θ : ℝ} (h : (z, θ) ∈ V) :
    Work.Spaces.mixed j i (f + g) z θ
      = Work.Spaces.mixed j i f z θ + Work.Spaces.mixed j i g z θ := by
  have hEq : Set.EqOn (Function.uncurry (Work.Spaces.DthIter i (f + g)))
      (Function.uncurry (Work.Spaces.DthIter i f + Work.Spaces.DthIter i g)) V := by
    intro p hp
    obtain ⟨z', θ'⟩ := p
    exact DthIter_add_eqOn hV hf hg i z' θ' hp
  have h1 := DzIter_congr_of_isOpen hV hEq j z θ h
  have h2 := DzIter_add_eqOn hV (contDiffOn_uncurry_DthIter_of_contDiffOn hV hf i)
    (contDiffOn_uncurry_DthIter_of_contDiffOn hV hg i) j z θ h
  simp only [Work.Spaces.mixed]
  rw [h1, h2]

/-! ## §4  Analyticity of a separable product -/

/-- A product `A(z)·B(θ)` of an analytic function of `z` on `(0,∞)` with an analytic
function of `θ` on `(0,π/2)` is analytic on the open quadrant. -/
theorem contDiffOn_uncurry_sep {n : WithTop ℕ∞} {A B : ℝ → ℝ}
    (hA : ContDiffOn ℝ n A (Set.Ioi 0)) (hB : ContDiffOn ℝ n B (Set.Ioo 0 (π / 2))) :
    ContDiffOn ℝ n (Function.uncurry (fun z θ => A z * B θ)) Q0 := by
  have h1 : ContDiffOn ℝ n (fun p : ℝ × ℝ => A p.1) Q0 := by
    have hc := hA.comp (contDiffOn_fst (s := Q0)) (fun p hp => hp.1)
    have hfun : (A ∘ Prod.fst) = fun p : ℝ × ℝ => A p.1 := by
      funext p
      obtain ⟨z, θ⟩ := p
      rfl
    rwa [hfun] at hc
  have h2 : ContDiffOn ℝ n (fun p : ℝ × ℝ => B p.2) Q0 := by
    have hc := hB.comp (contDiffOn_snd (s := Q0)) (fun p hp => hp.2)
    have hfun : (B ∘ Prod.snd) = fun p : ℝ × ℝ => B p.2 := by
      funext p
      obtain ⟨z, θ⟩ := p
      rfl
    rwa [hfun] at hc
  have h3 : ContDiffOn ℝ n (fun p : ℝ × ℝ => A p.1 * B p.2) Q0 := h1.mul h2
  have hfun : Function.uncurry (fun z θ => A z * B θ) = fun p : ℝ × ℝ => A p.1 * B p.2 := by
    funext p
    obtain ⟨z, θ⟩ := p
    rfl
  rwa [hfun]

end Work.FTS_RegExport.RXT.SysAux
