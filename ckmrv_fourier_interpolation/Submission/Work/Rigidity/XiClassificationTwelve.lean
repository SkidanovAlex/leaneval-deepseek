import Mathlib
import Submission.Work.Kernels.Classical
import Submission.Work.Rigidity.Basic
import Submission.Work.Rigidity.gamma2_generators
import Submission.Work.Rigidity.BoundedAtImInftyPeriodicInP
import Submission.Work.Rigidity.boundedAtImInfty_of_periodic_inP
import Submission.Work.Kernels.Slash
import Submission.Work.Rigidity.M12HSpan
import Submission.Work.Rigidity.XiKernelAtom

set_option maxHeartbeats 1000000

namespace Work.Rigidity

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle Topology

noncomputable section

/-! ## The slash action lemmas at weight `12` and `Γ(2)`-invariance -/

/-- The weight-`12` slash of `T` is the shift `τ ↦ τ + 1`. -/
lemma xiSlashT12 (F : ℍ → ℂ) : F ∣[(12:ℤ)] ModularGroup.T = fun τ => F ((1:ℝ) +ᵥ τ) := by
  funext τ
  rw [Work.Kernels.slash_apply', Work.Kernels.jFun_apply, UpperHalfPlane.modular_T_smul]
  simp

/-- The weight-`12` slash of `S`: `(F ∣[12] S) τ = τ^{-12} F (S • τ)`. -/
lemma xiSlashS12 (F : ℍ → ℂ) (τ : ℍ) :
    (F ∣[(12:ℤ)] ModularGroup.S) τ = (τ:ℂ)^(-12:ℤ) * F (ModularGroup.S • τ) := by
  rw [ModularForm.SL_slash_apply, ModularGroup.denom_S, mul_comm]

/-- At even weight, `-1 ∈ SL(2,ℤ)` acts trivially. -/
lemma xiSlashNegOne (F : ℍ → ℂ) : F ∣[(12:ℤ)] (-1 : SL(2,ℤ)) = F := by
  funext τ
  rw [ModularForm.SL_slash_apply]
  have h1 : ((-1 : SL(2,ℤ)) • τ : ℍ) = τ := by
    apply UpperHalfPlane.ext; simp
  have h2 : UpperHalfPlane.denom (Work.Kernels.glOf (-1 : SL(2,ℤ))) (τ:ℂ) = -1 := by
    rw [show UpperHalfPlane.denom (Work.Kernels.glOf (-1 : SL(2,ℤ))) (τ:ℂ)
        = (Work.Kernels.glOf (-1 : SL(2,ℤ))) 1 0 * (τ:ℂ)
          + (Work.Kernels.glOf (-1 : SL(2,ℤ))) 1 1 from rfl]
    rw [Work.Kernels.glOf_apply, Work.Kernels.glOf_apply]
    norm_num
  rw [h1, h2]
  have : ((-1 : ℂ)) ^ (-(12:ℤ)) = 1 := by
    rw [show (-(12:ℤ)) = -((12:ℕ):ℤ) by norm_num, _root_.zpow_neg, zpow_natCast]
    norm_num
  rw [this, mul_one]

/-- The trace relation in slash form: `P + P ∣[12] S + P ∣[12] (S * T) = 0`. -/
lemma xiTraceSlash {P : ℍ → ℂ}
    (htrace : ∀ τ : ℍ, P τ + (τ:ℂ)^(-12:ℤ) * P (ModularGroup.S • τ)
        + ((τ:ℂ) + 1)^(-12:ℤ) * P (ModularGroup.S • ((1:ℝ) +ᵥ τ)) = 0) :
    P + P ∣[(12:ℤ)] ModularGroup.S + P ∣[(12:ℤ)] (ModularGroup.S * ModularGroup.T) = 0 := by
  funext τ
  have hc : (((1:ℝ) +ᵥ τ : ℍ) : ℂ) = (τ:ℂ) + 1 := by
    rw [UpperHalfPlane.coe_vadd]; push_cast; ring
  simp only [Pi.add_apply, Pi.zero_apply, SlashAction.slash_mul, xiSlashT12, xiSlashS12, hc]
  exact htrace τ

/-- **`P` is invariant under `Γ(2)`.**  This is the structural content of the two
functional equations: the pair `(P, P ∣[12] S)` spans the two-dimensional standard
representation of `S₃ = Γ(1)/Γ(2)`, so the generators of `Γ(2)` act trivially. -/
theorem xiSlashGamma2 {P : ℍ → ℂ}
    (hper : ∀ τ : ℍ, P ((1:ℝ) +ᵥ τ) = P τ)
    (htrace : ∀ τ : ℍ, P τ + (τ:ℂ)^(-12:ℤ) * P (ModularGroup.S • τ)
        + ((τ:ℂ) + 1)^(-12:ℤ) * P (ModularGroup.S • ((1:ℝ) +ᵥ τ)) = 0) :
    ∀ γ ∈ CongruenceSubgroup.Gamma 2, P ∣[(12:ℤ)] γ = P := by
  have hT : P ∣[(12:ℤ)] ModularGroup.T = P := by
    rw [xiSlashT12]; funext τ; exact hper τ
  have hrel' : P + P ∣[(12:ℤ)] ModularGroup.S
      + (P ∣[(12:ℤ)] ModularGroup.S) ∣[(12:ℤ)] ModularGroup.T = 0 := by
    simpa only [SlashAction.slash_mul] using xiTraceSlash htrace
  -- applying `T` to the trace relation and subtracting
  have hST2 : P ∣[(12:ℤ)] (ModularGroup.S * (ModularGroup.T * ModularGroup.T))
      = P ∣[(12:ℤ)] ModularGroup.S := by
    have h2 : (P + P ∣[(12:ℤ)] ModularGroup.S
        + (P ∣[(12:ℤ)] ModularGroup.S) ∣[(12:ℤ)] ModularGroup.T) ∣[(12:ℤ)] ModularGroup.T = 0 := by
      rw [hrel']; simp
    rw [SlashAction.add_slash, SlashAction.add_slash] at h2
    rw [hT] at h2
    have key : ((P ∣[(12:ℤ)] ModularGroup.S) ∣[(12:ℤ)] ModularGroup.T) ∣[(12:ℤ)] ModularGroup.T
        = P ∣[(12:ℤ)] ModularGroup.S := by linear_combination h2 - hrel'
    rw [← SlashAction.slash_mul, ← SlashAction.slash_mul] at key
    exact key
  have hS2 : P ∣[(12:ℤ)] (ModularGroup.S * ModularGroup.S) = P := by
    have : ModularGroup.S * ModularGroup.S = (-1 : SL(2,ℤ)) := by decide
    rw [this, xiSlashNegOne]
  have hSTS : P ∣[(12:ℤ)]
      (ModularGroup.S * (ModularGroup.T * ModularGroup.T) * ModularGroup.S) = P := by
    have h := congrArg (fun F : ℍ → ℂ => F ∣[(12:ℤ)] ModularGroup.S) hST2
    simp only [← SlashAction.slash_mul] at h
    rw [hS2] at h
    exact h
  have hT2 : P ∣[(12:ℤ)] (ModularGroup.T * ModularGroup.T) = P := by
    rw [SlashAction.slash_mul, hT, hT]
  let H : Subgroup SL(2,ℤ) :=
    { carrier := {γ | P ∣[(12:ℤ)] γ = P}
      one_mem' := SlashAction.slash_one 12 P
      mul_mem' := by
        intro a b ha hb
        simp only [Set.mem_ofPred_eq] at ha hb ⊢
        rw [SlashAction.slash_mul, ha, hb]
      inv_mem' := by
        intro a ha
        simp only [Set.mem_ofPred_eq] at ha ⊢
        have h := congrArg (fun F : ℍ → ℂ => F ∣[(12:ℤ)] a⁻¹) ha
        rw [← SlashAction.slash_mul, mul_inv_cancel, SlashAction.slash_one] at h
        exact h.symm }
  have hgen : ({ModularGroup.T * ModularGroup.T,
      ModularGroup.S * (ModularGroup.T * ModularGroup.T) * ModularGroup.S,
      ModularGroup.S * ModularGroup.S} : Set SL(2,ℤ)) ⊆ H := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact hT2
    · exact hSTS
    · exact hS2
  have hle : CongruenceSubgroup.Gamma 2 ≤ H := by
    rw [gamma2_generators]
    exact (Subgroup.closure_le H).mpr hgen
  intro γ hγ
  exact hle hγ


/-- **`P` is bounded at every cusp.**  Since `𝒫` is preserved by the slash action and every
`P ∣[12] γ` is `Γ(2)`-invariant (hence periodic of period `2`), each `P ∣[12] γ` is bounded
at the cusp `i∞`. -/
lemma xiCuspBounded {P : ℍ → ℂ} (hP : Work.Kernels.InP P)
    (hΓ : ∀ γ ∈ CongruenceSubgroup.Gamma 2, P ∣[(12:ℤ)] γ = P) :
    ∀ g : SL(2,ℤ), UpperHalfPlane.IsBoundedAtImInfty (P ∣[(12:ℤ)] g) := by
  have hTT : ModularGroup.T * ModularGroup.T ∈ CongruenceSubgroup.Gamma 2 := by
    rw [CongruenceSubgroup.Gamma_mem]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> decide
  intro g
  have hPg : Work.Kernels.InP (P ∣[(12:ℤ)] g) := hP.slash (12:ℤ) g
  have hconj : (g * (ModularGroup.T * ModularGroup.T) * g⁻¹) ∈ CongruenceSubgroup.Gamma 2 :=
    Subgroup.Normal.conj_mem (CongruenceSubgroup.Gamma_normal 2)
      (ModularGroup.T * ModularGroup.T) hTT g
  have hshift : (P ∣[(12:ℤ)] g) ∣[(12:ℤ)] (ModularGroup.T * ModularGroup.T) = P ∣[(12:ℤ)] g := by
    have hgg : g * (ModularGroup.T * ModularGroup.T)
        = (g * (ModularGroup.T * ModularGroup.T) * g⁻¹) * g := by group
    rw [← SlashAction.slash_mul, hgg, SlashAction.slash_mul, hΓ _ hconj]
  have hper2 : ∀ τ : ℍ, (P ∣[(12:ℤ)] g) ((2:ℝ) +ᵥ τ) = (P ∣[(12:ℤ)] g) τ := by
    intro τ
    have h := congrFun hshift τ
    rw [SlashAction.slash_mul, xiSlashT12, xiSlashT12] at h
    simp only [Pi.add_apply] at h
    rw [← Work.Kernels.vadd_one_add_one] at h
    exact h
  exact BoundedAtImInftyPeriodicInP (by norm_num) hPg hper2


/-- **Classification of the cusp-holomorphic weight-`12` solutions.**  A holomorphic
function `P` of moderate growth which is `1`-periodic and satisfies the trace relation
`P + P∣[12]S + P∣[12](ST) = 0` (with `P∣[12]S` also of moderate growth) is a linear
combination of `ξ₄E₄²` and `ξ₂E₄E₆`. -/
theorem XiClassificationTwelve (P : UpperHalfPlane → Complex) (hP : Work.Kernels.InP P)
    (hPS : Work.Kernels.InP (fun τ : UpperHalfPlane => (τ : Complex) ^ (-12 : Int) * P (ModularGroup.S • τ)))
    (hper : ∀ τ : UpperHalfPlane, P ((1 : Real) +ᵥ τ) = P τ)
    (htrace : ∀ τ : UpperHalfPlane, P τ + (τ : Complex) ^ (-12 : Int) * P (ModularGroup.S • τ)
        + ((τ : Complex) + 1) ^ (-12 : Int) * P (ModularGroup.S • ((1 : Real) +ᵥ τ)) = 0) :
    ∃ c1 c2 : Complex, ∀ τ : UpperHalfPlane,
      P τ = c1 * (Work.Kernels.xi4Fun τ * Work.Kernels.E4Fun τ ^ 2)
            + c2 * (Work.Kernels.xi2Fun τ * Work.Kernels.E4Fun τ * Work.Kernels.E6Fun τ) := by
  have hΓ : ∀ γ ∈ CongruenceSubgroup.Gamma 2, SlashAction.map (12 : ℤ) γ P = P :=
    xiSlashGamma2 hper htrace
  have hbdd : ∀ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ,
      UpperHalfPlane.IsBoundedAtImInfty (SlashAction.map (12 : ℤ) γ P) := xiCuspBounded hP hΓ
  have hT : SlashAction.map (12 : ℤ) ModularGroup.T P = P := by
    show P ∣[(12 : ℤ)] ModularGroup.T = P
    rw [xiSlashT12]; funext τ; exact hper τ
  have hparam := M12HSpan P hP hΓ hbdd hT
  exact XiKernelAtom P htrace hparam

end

end Work.Rigidity
