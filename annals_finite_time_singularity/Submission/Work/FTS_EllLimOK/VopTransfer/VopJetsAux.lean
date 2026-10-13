/-
Copyright: work module for the Elgindi finite-time singularity project.

# Auxiliary lemmas for the `Vop`-jet transfer (`mixed_le_of_Vop_jets`)

These are the elementary interface lemmas used by
`Submission/Work/FTS_EllLimOK/VopTransfer/mixed_le_of_Vop_jets.lean`:

* `smoothOpen_vop` — `Vop Ψ = ∂_θΨ - tan θ·Ψ` is `C^∞` on the open quadrant when `Ψ` is;
* `smoothOpen_angular_mul` — multiplication by a `C^∞` angular factor preserves
  `SmoothOpen`;
* `DthIter_congr_Q0`, `mixed_congr_Q0` — locality of the `D_θ`-iterates (and of `mixed`) on
  the open quadrant;
* `DzIter_theta_const_mul` — an angular (i.e. `z`-independent) factor passes through the
  `D_z`-iterates;
* `Dth_eq_sfun_mul_add` — the pointwise recurrence
  `D_θΨ = sin(2θ)·Vop Ψ + 2 sin²θ·Ψ` on the open quadrant;
* `mixed_angular_mul` — the Leibniz rule
  `D_z^j D_θ^i (c(θ)·f) = ∑_{m ≤ i} C(i,m) (Lop^m c)(θ) · D_z^j D_θ^{i-m} f` for a `C^∞`
  angular factor `c` and `f` smooth on the open quadrant.

All declarations are `sorry`-free and rest on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.DthIter_mul
import Submission.Work.Spaces.DzDthIterCommOn
import Submission.Work.Construction.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.ThetaPoincareDefs
import Submission.Work.FTS.TransportS.flat_mixed_le
import Submission.Work.FTS_EllLimOK.VopTransfer.contDiff_Lop_iterate

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK.VopTransfer

set_option maxHeartbeats 800000

/-- `Vop Ψ = ∂_θΨ - tan θ·Ψ` is `C^∞` on the open quadrant when `Ψ` is. -/
theorem smoothOpen_vop {Ψ : ℝ → ℝ → ℝ} (hsm : Work.FTS.EllipticEst.SmoothOpen Ψ) :
    Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Vop Ψ) := by
  have h1 : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pth Ψ) := hsm.pth
  have h2 : Work.FTS.EllipticEst.SmoothOpen (fun z θ => Real.tan θ * Ψ z θ) := by
    rw [Work.FTS.EllipticEst.SmoothOpen] at hsm ⊢
    have h : Function.uncurry (fun z θ => Real.tan θ * Ψ z θ)
        = (fun p : ℝ × ℝ => Real.tan p.2) * (Function.uncurry Ψ) := by
      funext p; rcases p with ⟨z, θ⟩; rfl
    rw [h]
    refine ContDiffOn.mul ?_ hsm
    have heq : (fun p : ℝ × ℝ => Real.tan p.2)
        = (fun p : ℝ × ℝ => Real.sin p.2) / (fun p : ℝ × ℝ => Real.cos p.2) := by
      funext p; exact Real.tan_eq_sin_div_cos p.2
    rw [heq]
    refine ContDiffOn.div (contDiffOn_snd.sin) (contDiffOn_snd.cos) ?_
    intro p hp
    exact ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [hp.2.1, Real.pi_pos], hp.2.2⟩)
  rw [Work.FTS.EllipticEst.SmoothOpen] at h1 h2 ⊢
  have h : Function.uncurry (Work.Construction.Vop Ψ)
      = Function.uncurry (Work.Spaces.pth Ψ)
        - Function.uncurry (fun z θ => Real.tan θ * Ψ z θ) := by
    funext p; rcases p with ⟨z, θ⟩; rfl
  rw [h]
  exact h1.sub h2

/-- Multiplication by a `C^∞` angular factor preserves `SmoothOpen`. -/
theorem smoothOpen_angular_mul {c : ℝ → ℝ} (hc : ContDiff ℝ ⊤ c) {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => c θ * f z θ) := by
  rw [Work.FTS.EllipticEst.SmoothOpen] at hf ⊢
  have h : Function.uncurry (fun z θ => c θ * f z θ)
      = (fun p : ℝ × ℝ => c p.2) * (Function.uncurry f) := by
    funext p; rcases p with ⟨z, θ⟩; rfl
  rw [h]
  refine ContDiffOn.mul ?_ hf
  exact ((hc.comp contDiff_snd).of_le le_top).contDiffOn

/-- `D_θ`-iterates only see the values on the open quadrant. -/
theorem DthIter_congr_Q0 {u v : ℝ → ℝ → ℝ}
    (h : Set.EqOn (Function.uncurry u) (Function.uncurry v) Work.FTS.EllipticEst.Q0)
    (i : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.DthIter i u))
      (Function.uncurry (Work.Spaces.DthIter i v)) Work.FTS.EllipticEst.Q0 := by
  induction i with
  | zero => exact h
  | succ n ih =>
      intro p hp
      show Real.sin (2 * p.2) * Work.Spaces.pth (Work.Spaces.DthIter n u) p.1 p.2
        = Real.sin (2 * p.2) * Work.Spaces.pth (Work.Spaces.DthIter n v) p.1 p.2
      rw [Work.Spaces.pth_congr_of_isOpen Work.FTS.EllipticEst.isOpen_Q0 ih hp]

/-- Locality of `mixed` on the open quadrant. -/
theorem mixed_congr_Q0 {u v : ℝ → ℝ → ℝ}
    (h : Set.EqOn (Function.uncurry u) (Function.uncurry v) Work.FTS.EllipticEst.Q0)
    (j i : ℕ) :
    ∀ z θ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) →
      Work.Spaces.mixed j i u z θ = Work.Spaces.mixed j i v z θ := by
  intro z θ hz hθ
  have hDth := DthIter_congr_Q0 h i
  exact Work.FTS.EllipticEst.SmoothOpen.DzIter_congr
    (F := Work.Spaces.DthIter i u) (G := Work.Spaces.DthIter i v)
    (fun z' θ' hz' h1 h2 => hDth (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz', h1, h2⟩))
    j z θ hz hθ.1 hθ.2

/-- A `θ`-only factor passes through `D_z`-iterates. -/
theorem DzIter_theta_const_mul (c : ℝ → ℝ) (H : ℝ → ℝ → ℝ) (j : ℕ) :
    ∀ z θ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) →
      Work.Spaces.DzIter j (fun z θ => c θ * H z θ) z θ
        = c θ * Work.Spaces.DzIter j H z θ := by
  induction j with
  | zero => intro z θ _ _; rfl
  | succ n ih =>
      intro z θ hz hθ
      have heq : Set.EqOn
          (Function.uncurry (Work.Spaces.DzIter n (fun z θ => c θ * H z θ)))
          (Function.uncurry (fun z θ => c θ * Work.Spaces.DzIter n H z θ))
          Work.FTS.EllipticEst.Q0 := by
        intro p hp
        rcases p with ⟨z', θ'⟩
        obtain ⟨hz', hθ'1, hθ'2⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
        exact ih z' θ' hz' ⟨hθ'1, hθ'2⟩
      have hpz := Work.Spaces.pz_congr_of_isOpen Work.FTS.EllipticEst.isOpen_Q0 heq
        (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ.1, hθ.2⟩)
      simp only [Work.Spaces.pz] at hpz
      simp only [Work.Spaces.DzIter_succ, Work.Spaces.Dz, Work.Spaces.pz]
      rw [hpz, deriv_const_mul_field]
      ring

/-- The recurrence `D_θΨ = sin(2θ)·VopΨ + 2 sin²θ·Ψ` on the open quadrant. -/
theorem Dth_eq_sfun_mul_add {Ψ : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    Work.Spaces.Dth Ψ z θ = Real.sin (2 * θ) * Work.Construction.Vop Ψ z θ
      + 2 * Real.sin θ ^ 2 * Ψ z θ := by
  have hc : Real.cos θ ≠ 0 := ne_of_gt
    (Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩)
  have htan : Real.sin (2 * θ) * Real.tan θ = 2 * Real.sin θ ^ 2 := by
    rw [Real.tan_eq_sin_div_cos, Real.sin_two_mul]
    field_simp
  simp only [Work.Spaces.Dth, Work.Construction.Vop]
  rw [show Real.sin (2 * θ) * (Work.Spaces.pth Ψ z θ - Real.tan θ * Ψ z θ)
        + 2 * Real.sin θ ^ 2 * Ψ z θ
      = Real.sin (2 * θ) * Work.Spaces.pth Ψ z θ
        - (Real.sin (2 * θ) * Real.tan θ) * Ψ z θ + 2 * Real.sin θ ^ 2 * Ψ z θ from by ring]
  rw [htan]
  ring

/-- **Leibniz for `mixed` with an angular factor.**  For a `C^∞` angular factor `c` and `f`
smooth on the open quadrant, `D_z^j D_θ^i (c(θ)·f) = ∑_{m ≤ i} C(i,m)·(Lop^m c)(θ) ·
D_z^j D_θ^{i-m} f` at every point of the open quadrant. -/
theorem mixed_angular_mul {c : ℝ → ℝ} (hc : ∀ θ : ℝ, ContDiffAt ℝ ⊤ c θ)
    {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f) (j i : ℕ) {z θ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    Work.Spaces.mixed j i (fun z θ => c θ * f z θ) z θ
      = ∑ m ∈ Finset.range (i + 1), (i.choose m : ℝ) * Work.FTS.EllipticEst.LopIter m c θ
          * Work.Spaces.mixed j (i - m) f z θ := by
  have hck : ∀ k : ℕ, ContDiff ℝ k c := fun k => (contDiff_iff_contDiffAt.mpr hc).of_le le_top
  have hcd : ∀ (a : ℕ) (z₀ : ℝ), a ≤ i → DifferentiableOn ℝ
      (fun θ' => Work.Spaces.DthIter a (fun z θ => c θ) z₀ θ') (Set.Ioo 0 (π / 2)) := by
    intro a z₀ _
    have h1 : ContDiff ℝ 1 (Work.Spaces.Lop^[a] c) := contDiff_Lop_iterate c hck a 1
    have h2 : (fun θ' => Work.Spaces.DthIter a (fun z θ => c θ) z₀ θ') = Work.Spaces.Lop^[a] c := by
      funext θ'
      exact congrFun (Work.Spaces.DthIter_eq_iterate_Lop a (fun z θ => c θ) z₀) θ'
    rw [h2]
    exact (h1.differentiable (by norm_num)).differentiableOn
  have hfd : ∀ z' : ℝ, 0 < z' → ∀ a ≤ i, DifferentiableOn ℝ
      (fun θ' => Work.Spaces.DthIter a f z' θ') (Set.Ioo 0 (π / 2)) := by
    intro z' hz' a _
    have h1 : ContDiffOn ℝ 1 (fun θ' => Work.Spaces.DthIter a f z' θ') (Set.Ioo 0 (π / 2)) :=
      contDiffOn_iff_forall_nat_le.mp ((hf.DthIter a).curry_θ hz') 1 le_top
    exact h1.differentiableOn (by norm_num)
  have hident : ∀ (m : ℕ) (z₀ θ₀ : ℝ), Work.Spaces.DthIter m (fun z θ => c θ) z₀ θ₀
      = Work.FTS.EllipticEst.LopIter m c θ₀ := by
    intro m z₀ θ₀
    rw [Work.Spaces.DthIter_eq_iterate_Lop]
    rfl
  have hEqOn : Set.EqOn
      (Function.uncurry (Work.Spaces.DthIter i (fun a b : ℝ => c b * f a b)))
      (Function.uncurry (fun z' θ' => ∑ m ∈ Finset.range (i + 1),
        ((i.choose m : ℝ) * Work.FTS.EllipticEst.LopIter m c θ')
          * Work.Spaces.DthIter (i - m) f z' θ'))
      Work.FTS.EllipticEst.Q0 := by
    intro p hp
    rcases p with ⟨z', θ'⟩
    obtain ⟨hz', hθ'1, hθ'2⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    have hleib := Work.FTS.TransportS.DthIter_mul_eq_of_diffOn i (fun z θ => c θ) f
      (z := z') (θ := θ') ⟨hθ'1, hθ'2⟩ (fun a ha => hcd a z' ha) (fun a ha => hfd z' hz' a ha)
    show Work.Spaces.DthIter i (fun a b : ℝ => c b * f a b) z' θ'
      = ∑ m ∈ Finset.range (i + 1), ((i.choose m : ℝ) * Work.FTS.EllipticEst.LopIter m c θ')
          * Work.Spaces.DthIter (i - m) f z' θ'
    rw [hleib]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [hident m z' θ']
    ring
  rw [show Work.Spaces.mixed j i (fun z θ => c θ * f z θ)
      = Work.Spaces.DzIter j (Work.Spaces.DthIter i (fun a b : ℝ => c b * f a b)) from rfl,
    Work.FTS.EllipticEst.SmoothOpen.DzIter_congr
      (F := Work.Spaces.DthIter i (fun a b : ℝ => c b * f a b))
      (G := fun z' θ' => ∑ m ∈ Finset.range (i + 1),
        ((i.choose m : ℝ) * Work.FTS.EllipticEst.LopIter m c θ')
          * Work.Spaces.DthIter (i - m) f z' θ')
      (fun z' θ' hz' h1 h2 => hEqOn (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz', h1, h2⟩))
      j z θ hz hθ.1 hθ.2,
    Work.FTS.TransportS.DzIter_sum_const_mul (Finset.range (i + 1))
      (fun m θ' => (i.choose m : ℝ) * Work.FTS.EllipticEst.LopIter m c θ')
      (fun m => Work.Spaces.DthIter (i - m) f) (fun m _ => hf.DthIter (i - m)) j hz hθ.1 hθ.2]
  exact Finset.sum_congr rfl fun m _ => rfl

end Work.FTS_EllLimOK.VopTransfer
