import Mathlib
import Submission.Work.Asymptotics.PropagateDefs
import Submission.Work.Asymptotics.DomainD
import Submission.Work.Asymptotics.exists_extension_of_propagates
import Submission.Work.Kernels.Section5Facts.Fgen_third

open scoped Manifold

namespace Work.Asymptotics

/-- The Gaussian `τ ↦ e^{πiτr²}` is holomorphic in `τ`. -/
lemma mdifferentiable_gaussTerm (r : ℝ) :
    MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
      (fun τ : UpperHalfPlane => Work.Kernels.gaussTerm τ r) := by
  rw [UpperHalfPlane.mdifferentiable_iff]
  refine (by fun_prop : DifferentiableOn ℂ
    (fun z : ℂ => Complex.exp (Real.pi * Complex.I * z * (r : ℂ) ^ 2))
      {z | 0 < z.im}).congr ?_
  intro z hz
  simp only [Function.comp_apply]
  rw [UpperHalfPlane.ofComplex_apply_of_im_pos hz]
  simp only [Work.Kernels.gaussTerm]

/-- The second difference `(T-I)²` of the Gaussian is holomorphic in `τ`. -/
lemma mdifferentiable_T2op_gaussTerm (r : ℝ) :
    MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
      (Work.Kernels.T2op (fun σ : UpperHalfPlane => Work.Kernels.gaussTerm σ r)) := by
  rw [UpperHalfPlane.mdifferentiable_iff]
  refine (by fun_prop : DifferentiableOn ℂ (fun z : ℂ =>
    Complex.exp (Real.pi * Complex.I * ((2 : ℂ) + z) * (r : ℂ) ^ 2)
    - 2 * Complex.exp (Real.pi * Complex.I * ((1 : ℂ) + z) * (r : ℂ) ^ 2)
    + Complex.exp (Real.pi * Complex.I * z * (r : ℂ) ^ 2)) {z | 0 < z.im}).congr ?_
  intro z hz
  simp only [Function.comp_apply, Work.Kernels.T2op, Work.Kernels.gaussTerm,
    UpperHalfPlane.coe_vadd]
  have hz' : ((UpperHalfPlane.ofComplex z : UpperHalfPlane) : ℂ) = z := by
    rw [UpperHalfPlane.ofComplex_apply_of_im_pos hz]
  rw [hz']
  push_cast
  ring_nf

/-- **The corrected generating functions: clauses (1) and (5) of Theorem 3.1** (declare in
namespace `Work.Asymptotics`).  CKMRV Corollary 4.1 plus Proposition 3.2: given, for every `r`, a
function `F₂` holomorphic on an open neighbourhood `O` of the closure of `𝒟` satisfying the two
propagation recurrences

* `F₂(τ+2,r) - 2F₂(τ+1,r) + F₂(τ,r) = -((T-I)² e^{πiτr²})`,
* `F₂|^τ_{d/2}S(T-I)² = 0`

(i.e. exactly `Work.Asymptotics.Propagates ((d:ℤ)/2) O F₂ (-T2op (gaussTerm · r)) 0` — these are
the conclusions of CKMRV Proposition 4.6 for the contour integral (5.2)), there are
`F, F̃ : ℍ → ℝ → ℂ` — namely `F = gaussTerm + Ψ` and `F̃ = -Ψ|^τ_{d/2}S`, where `Ψ` is the
propagation extension of `F₂` — which are holomorphic in `τ` for every `r` (clause (1)) and
satisfy the three functional equations of clause (5):

  `(T-I)²F = 0`,  `(T-I)²F̃ = 0`,  `F(τ,r) + (i/τ)^{d/2} F̃(Sτ,r) = e^{πiτr²}`.

Use `Work.Asymptotics.exists_extension_of_propagates` (CKMRV Proposition 3.2(1), proved) applied
to `F₂`, together with `Work.Kernels.slash_T2`, `Work.Asymptotics.S2op_eq_T2op_slash`,
`Work/Kernels/Section5Facts/Fgen_third.lean` and the fact that `gaussTerm · r` is holomorphic in
`τ` for every `r`. -/
theorem exists_pair_of_propagated_F2 {d : ℕ} (hdI : (-Complex.I) ^ (d / 2) = 1)
    (h : ∀ r : ℝ, ∃ (O : Set UpperHalfPlane) (F₂ : UpperHalfPlane → ℂ),
        IsOpen O ∧ closure Work.Asymptotics.DomainD ⊆ O ∧
        MDifferentiableOn (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) F₂ O ∧
        (∀ τ : UpperHalfPlane, τ ∈ O → (1 : ℝ) +ᵥ τ ∈ O → (2 : ℝ) +ᵥ τ ∈ O →
          Work.Kernels.T2op F₂ τ = -Work.Kernels.T2op (fun σ => Work.Kernels.gaussTerm σ r) τ) ∧
        (∀ τ : UpperHalfPlane, ModularGroup.S • τ ∈ O →
          ModularGroup.S • ((1 : ℝ) +ᵥ τ) ∈ O → ModularGroup.S • ((2 : ℝ) +ᵥ τ) ∈ O →
          Work.Asymptotics.S2op ((d : ℤ) / 2) F₂ τ = 0)) :
    ∃ F Ft : UpperHalfPlane → ℝ → ℂ,
      (∀ r : ℝ, MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
        (fun τ => F τ r)) ∧
      (∀ r : ℝ, MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
        (fun τ => Ft τ r)) ∧
      (∀ (r : ℝ) (τ : UpperHalfPlane), Work.Kernels.T2op (fun σ => F σ r) τ = 0) ∧
      (∀ (r : ℝ) (τ : UpperHalfPlane), Work.Kernels.T2op (fun σ => Ft σ r) τ = 0) ∧
      (∀ (r : ℝ) (τ : UpperHalfPlane),
        F τ r + (Complex.I / (τ : ℂ)) ^ (d / 2) * Ft (ModularGroup.S • τ) r
          = Work.Kernels.gaussTerm τ r) := by
  classical
  -- CKMRV Proposition 3.2(1) applied to `F₂` produces the propagation extension `Ψ`.
  have hkey : ∀ r : ℝ, ∃ Ψ : UpperHalfPlane → ℂ,
      MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) Ψ ∧
      (∀ τ : UpperHalfPlane, Work.Kernels.T2op Ψ τ =
        -Work.Kernels.T2op (fun σ => Work.Kernels.gaussTerm σ r) τ) ∧
      (∀ τ : UpperHalfPlane, S2op ((d : ℤ) / 2) Ψ τ = 0) := by
    intro r
    obtain ⟨O, F₂, hO, hsub, hF₂, hdef1, hdef2⟩ := h r
    have hprop : Propagates ((d : ℤ) / 2) O F₂
        (fun τ : UpperHalfPlane =>
          -Work.Kernels.T2op (fun σ => Work.Kernels.gaussTerm σ r) τ) 0 :=
      ⟨hO, (mdifferentiable_T2op_gaussTerm r).neg, mdifferentiable_const, hF₂,
        hdef1, hdef2⟩
    obtain ⟨Ψ, hΨmd, -, hΨT2, hΨS2⟩ := exists_extension_of_propagates hprop hsub
    exact ⟨Ψ, hΨmd, hΨT2, hΨS2⟩
  choose Ψ hΨspec using hkey
  refine ⟨fun τ r => Work.Kernels.gaussTerm τ r + Ψ r τ,
    fun τ r => -Work.Kernels.slash ((d : ℤ) / 2) Work.Kernels.R_S (Ψ r) τ,
    ?_, ?_, ?_, ?_, ?_⟩
  · intro r
    show MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
      (fun τ : UpperHalfPlane => Work.Kernels.gaussTerm τ r + Ψ r τ)
    exact (mdifferentiable_gaussTerm r).add (hΨspec r).1
  · intro r
    show MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
      (fun τ : UpperHalfPlane =>
        -(Work.Kernels.slash ((d : ℤ) / 2) Work.Kernels.R_S (Ψ r)) τ)
    exact (mdifferentiable_slash (hΨspec r).1 _ _).neg
  · intro r τ
    show Work.Kernels.T2op
      (fun σ : UpperHalfPlane => Work.Kernels.gaussTerm σ r + Ψ r σ) τ = 0
    have h1 : Work.Kernels.T2op
        (fun σ : UpperHalfPlane => Work.Kernels.gaussTerm σ r + Ψ r σ) = 0 := by
      have hT2Ψ : Work.Kernels.T2op (Ψ r)
          = -Work.Kernels.T2op (fun σ : UpperHalfPlane => Work.Kernels.gaussTerm σ r) :=
        funext (hΨspec r).2.1
      rw [Work.Kernels.T2op_add', hT2Ψ]
      simp
    exact congr_fun h1 τ
  · intro r τ
    show Work.Kernels.T2op
      (fun σ : UpperHalfPlane =>
        -Work.Kernels.slash ((d : ℤ) / 2) Work.Kernels.R_S (Ψ r) σ) τ = 0
    have hS2 : Work.Kernels.T2op
        (Work.Kernels.slash ((d : ℤ) / 2) Work.Kernels.R_S (Ψ r)) = 0 := by
      rw [Work.Kernels.slash_R_S, Work.Kernels.T2op_slash_S]
      exact funext (hΨspec r).2.2
    have hFtT2 : Work.Kernels.T2op (fun σ : UpperHalfPlane =>
        -Work.Kernels.slash ((d : ℤ) / 2) Work.Kernels.R_S (Ψ r) σ) = 0 := by
      rw [Work.Kernels.T2op_neg', hS2]
      simp
    exact congr_fun hFtT2 τ
  · intro r τ
    -- `Ft (S•τ) r = -(Ψ r τ · (-τ⁻¹)^{-d/2})` and the elementary Gaussian identity close the
    -- third functional equation.
    have hSS : ModularGroup.S • (ModularGroup.S • τ) = τ := by
      rw [UpperHalfPlane.ext_iff, UpperHalfPlane.modular_S_smul, UpperHalfPlane.modular_S_smul]
      simp
    have hslash : Work.Kernels.slash ((d : ℤ) / 2) Work.Kernels.R_S (Ψ r)
          (ModularGroup.S • τ)
        = Ψ r τ * (-((τ : ℂ))⁻¹) ^ (-((d : ℤ) / 2)) := by
      rw [Work.Kernels.slash_R_S, Work.Kernels.slash_S_apply, hSS, Work.Kernels.S_smul_coe]
    show Work.Kernels.gaussTerm τ r + Ψ r τ
        + (Complex.I / (τ : ℂ)) ^ (d / 2)
          * (-(Work.Kernels.slash ((d : ℤ) / 2) Work.Kernels.R_S (Ψ r)
              (ModularGroup.S • τ)))
        = Work.Kernels.gaussTerm τ r
    rw [hslash]
    have hkey2 := Work.Kernels.Section5Facts.Fgen_third_Ipow_key (τ : ℂ)
      (UpperHalfPlane.ne_zero τ) d hdI
    rw [show (Complex.I / (τ : ℂ)) ^ (d / 2)
          * (-(Ψ r τ * (-((τ : ℂ))⁻¹) ^ (-((d : ℤ) / 2))))
        = -((Complex.I / (τ : ℂ)) ^ (d / 2)
            * (-((τ : ℂ))⁻¹) ^ (-((d : ℤ) / 2))) * (Ψ r τ) by ring]
    rw [hkey2]
    ring

end Work.Asymptotics
