import Mathlib
import Submission.Work.Kernels.Classical
import Submission.Work.Residues.KMinusClear_T
import Submission.Work.Kernels.KernelFacts.psi2_T2
import Submission.Work.Modular.E4_tendsto_atImInfty

namespace Work.Rigidity

open UpperHalfPlane ModularForm ModularGroup Matrix Filter
open scoped MatrixGroups ModularForm Modular Manifold Bundle Topology

noncomputable section

/-!
# The trace-kernel inside the four-dimensional space `M₁₂(H)`

`hparam` says `D = a E₄³ + b E₆² + c ξ₂ E₄ E₆ + d V² E₄²` (the shape produced by
`Work.Rigidity.M12HSpan`).  Together with the trace relation `D + D∣[12]S + D∣[12](ST) = 0`
this forces `D ∈ ℂ·ξ₄E₄² + ℂ·ξ₂E₄E₆`.

## Plan

Apply `I + S + ST` (weight-`12` slash) to both sides.  Since `E₄, E₆` are level-one forms,
`(I+S+ST)E₄³ = 3E₄³` and `(I+S+ST)E₆² = 3E₆²`.  From `ξ₂ = U + W` together with the `S`/`T`-actions
of `U, V, W` one gets `ξ₂ + ξ₂∣S + ξ₂∣ST = 0`, so `(I+S+ST)(ξ₂E₄E₆) = 0`.  Finally
`V∣S = -W`, `V∣T = -V`, `U∣T = W` and `U²+V²+W² = 2E₄` give `(I+S+ST)(V²E₄²) = 2E₄³`.  Hence
`0 = (3a+2d)E₄³ + 3bE₆²`.  Since `E₄³, E₆²` are linearly independent (`1` at the cusp and
`E₄³ - E₆² = 1728Δ ≠ 0`), `b = 0` and `d = -3a/2`, and with `ξ₄ = 2E₄ - 3V²` this is
`D = (a/2)ξ₄E₄² + c ξ₂E₄E₆`.

Useful facts: `Work.Residues.KMinusClear_T` (`E₄ = (U²+V²+W²)/2`),
`Work.Kernels.KernelFacts.psi2_T2` (`ξ₂∣[2]S = -(U+V)`, `U∣[2]S = -U`, `W∣[2]S = -V`,
`U∣T = W`, `W∣T = U`, `V∣T = -V`), `Work.Kernels.TildeFacts.theta_quartic` (`U = V + W`),
and `Work.Kernels.KernelFacts.fk_slash` (`f_k ∣[k] γ = f_k` for `γ ∈ SL(2,ℤ)`).
-/

namespace XiKernelAux

open Work.Kernels

/-! ## The trace operator -/

/-- The weight-`12` trace operator `f ↦ f + f∣[12]S + f∣[12](ST)`. -/
def Tr12 (f : ℍ → ℂ) : ℍ → ℂ :=
  f + SlashAction.map (12 : ℤ) ModularGroup.S f
    + SlashAction.map (12 : ℤ) (ModularGroup.S * ModularGroup.T) f

lemma Tr12_apply (f : ℍ → ℂ) (τ : ℍ) :
    Tr12 f τ = f τ + f (ModularGroup.S • τ) * (τ : ℂ) ^ (-12 : ℤ)
      + f (ModularGroup.S • ((1 : ℝ) +ᵥ τ)) * ((τ : ℂ) + 1) ^ (-12 : ℤ) := by
  simp only [Tr12, Pi.add_apply, SlashAction.slash_mul, Work.Kernels.slash_S_apply,
    Work.Kernels.slash_T_apply, UpperHalfPlane.coe_vadd]
  push_cast
  ring_nf

/-- The trace relation says exactly that `Tr12 D = 0`. -/
lemma Tr12_eq_zero_of_trace (D : ℍ → ℂ)
    (htrace : ∀ τ : ℍ, D τ + (τ : ℂ) ^ (-12 : ℤ) * D (ModularGroup.S • τ)
        + ((τ : ℂ) + 1) ^ (-12 : ℤ) * D (ModularGroup.S • ((1 : ℝ) +ᵥ τ)) = 0) :
    Tr12 D = 0 := by
  funext τ
  rw [Tr12_apply, Pi.zero_apply]
  linear_combination htrace τ

/-! ## Slash-invariance in pointwise form -/

lemma slash_inv_S {k : ℤ} {f : ℍ → ℂ} (hf : SlashAction.map k ModularGroup.S f = f)
    (τ : ℍ) : f (ModularGroup.S • τ) * (τ : ℂ) ^ (-k) = f τ := by
  have h := congrFun hf τ
  rwa [Work.Kernels.slash_S_apply] at h

lemma slash_inv_ST {k : ℤ} {f : ℍ → ℂ}
    (hf : SlashAction.map k (ModularGroup.S * ModularGroup.T) f = f) (τ : ℍ) :
    f (ModularGroup.S • ((1:ℝ) +ᵥ τ)) * ((τ : ℂ) + 1) ^ (-k) = f τ := by
  have h := congrFun hf τ
  rw [SlashAction.slash_mul, Work.Kernels.slash_T_apply, Work.Kernels.slash_S_apply,
    UpperHalfPlane.coe_vadd] at h
  push_cast at h
  rwa [show ((1:ℂ) + (τ:ℂ)) = ((τ:ℂ) + 1) by ring] at h

/-- Powers of a slash-invariant function are slash-invariant. -/
lemma pow_slash_inv {k : ℤ} {γ : SL(2,ℤ)} {f : ℍ → ℂ}
    (hf : SlashAction.map k γ f = f) (n : ℕ) :
    SlashAction.map ((n : ℤ) * k) γ (f ^ n) = f ^ n := by
  induction n with
  | zero => rw [Nat.cast_zero, zero_mul, pow_zero, ModularForm.is_invariant_one]
  | succ n ih =>
      rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul, pow_succ, ModularForm.mul_slash_SL2,
        ih, hf]

/-- `Tr12` is additive. -/
lemma Tr12_add (f g : ℍ → ℂ) : Tr12 (f + g) = Tr12 f + Tr12 g := by
  simp only [Tr12, SlashAction.add_slash]
  abel

/-- The slash commutes with multiplication by a constant function. -/
lemma slash_smul (k : ℤ) (γ : SL(2,ℤ)) (c : ℂ) (f : ℍ → ℂ) :
    SlashAction.map k γ (c • f) = c • SlashAction.map k γ f := by
  funext τ
  simp only [Pi.smul_apply, Work.Kernels.slash_apply']
  ring

/-- `Tr12` is `ℂ`-linear. -/
lemma Tr12_smul (c : ℂ) (f : ℍ → ℂ) : Tr12 (c • f) = c • Tr12 f := by
  simp only [Tr12, slash_smul]
  funext τ
  simp only [Pi.add_apply, Pi.smul_apply]
  ring

/-! ## The values of `Tr12` on the four basis functions -/

lemma Tr12_E4cube : Tr12 (E4Fun ^ 3) = fun τ => 3 * E4Fun τ ^ 3 := by
  have hS : SlashAction.map (12:ℤ) ModularGroup.S (E4Fun ^ 3) = E4Fun ^ 3 := by
    have h := pow_slash_inv (k := (4:ℤ)) (γ := ModularGroup.S) (f := E4Fun)
      (Work.Kernels.KernelFacts.E4Fun_slash ModularGroup.S) 3
    norm_num at h
    exact h
  have hST : SlashAction.map (12:ℤ) (ModularGroup.S * ModularGroup.T) (E4Fun ^ 3) = E4Fun ^ 3 := by
    have h := pow_slash_inv (k := (4:ℤ)) (γ := ModularGroup.S * ModularGroup.T) (f := E4Fun)
      (Work.Kernels.KernelFacts.E4Fun_slash (ModularGroup.S * ModularGroup.T)) 3
    norm_num at h
    exact h
  funext τ
  rw [Tr12_apply, slash_inv_S hS τ, slash_inv_ST hST τ]
  simp only [Pi.pow_apply]
  ring

lemma Tr12_E6sq : Tr12 (E6Fun ^ 2) = fun τ => 3 * E6Fun τ ^ 2 := by
  have hS : SlashAction.map (12:ℤ) ModularGroup.S (E6Fun ^ 2) = E6Fun ^ 2 := by
    have h := pow_slash_inv (k := (6:ℤ)) (γ := ModularGroup.S) (f := E6Fun)
      (Work.Kernels.KernelFacts.E6Fun_slash ModularGroup.S) 2
    norm_num at h
    exact h
  have hST : SlashAction.map (12:ℤ) (ModularGroup.S * ModularGroup.T) (E6Fun ^ 2) = E6Fun ^ 2 := by
    have h := pow_slash_inv (k := (6:ℤ)) (γ := ModularGroup.S * ModularGroup.T) (f := E6Fun)
      (Work.Kernels.KernelFacts.E6Fun_slash (ModularGroup.S * ModularGroup.T)) 2
    norm_num at h
    exact h
  funext τ
  rw [Tr12_apply, slash_inv_S hS τ, slash_inv_ST hST τ]
  simp only [Pi.pow_apply]
  ring

/-! ### The `ξ₂E₄E₆` term -/

lemma xi2_slash_S : SlashAction.map (2:ℤ) ModularGroup.S xi2Fun = -(UFun + VFun) := by
  funext τ
  rw [Pi.neg_apply, Pi.add_apply]
  exact Work.Kernels.KernelFacts.xi2Fun_slash_S τ

lemma UFun_slash_T : SlashAction.map (2:ℤ) ModularGroup.T UFun = WFun := by
  funext τ; rw [Work.Kernels.slash_T_apply]; exact Work.Kernels.KernelFacts.UFun_vadd_one τ

lemma WFun_slash_T : SlashAction.map (2:ℤ) ModularGroup.T WFun = UFun := by
  funext τ; rw [Work.Kernels.slash_T_apply]; exact Work.Kernels.KernelFacts.WFun_vadd_one τ

lemma VFun_slash_T : SlashAction.map (2:ℤ) ModularGroup.T VFun = -VFun := by
  funext τ; rw [Work.Kernels.slash_T_apply]; exact Work.Kernels.KernelFacts.VFun_vadd_one τ

/-- `ξ₂ + ξ₂∣S + ξ₂∣ST = 0`. -/
lemma xi2_trace : xi2Fun + SlashAction.map (2:ℤ) ModularGroup.S xi2Fun
    + SlashAction.map (2:ℤ) (ModularGroup.S * ModularGroup.T) xi2Fun = 0 := by
  rw [SlashAction.slash_mul, xi2_slash_S, SlashAction.neg_slash, SlashAction.add_slash,
    UFun_slash_T, VFun_slash_T]
  funext τ
  simp only [Pi.add_apply, Pi.neg_apply, Pi.zero_apply, xi2Fun]
  ring

lemma slash_S_xi2E4E6 :
    SlashAction.map (12:ℤ) ModularGroup.S (xi2Fun * E4Fun * E6Fun)
      = SlashAction.map (2:ℤ) ModularGroup.S xi2Fun * E4Fun * E6Fun := by
  have key : SlashAction.map ((2:ℤ) + 4 + 6) ModularGroup.S (xi2Fun * E4Fun * E6Fun)
      = SlashAction.map (2:ℤ) ModularGroup.S xi2Fun * E4Fun * E6Fun := by
    rw [ModularForm.mul_slash_SL2, ModularForm.mul_slash_SL2,
      Work.Kernels.KernelFacts.E4Fun_slash, Work.Kernels.KernelFacts.E6Fun_slash]
  exact key

lemma slash_ST_xi2E4E6 :
    SlashAction.map (12:ℤ) (ModularGroup.S * ModularGroup.T) (xi2Fun * E4Fun * E6Fun)
      = SlashAction.map (2:ℤ) (ModularGroup.S * ModularGroup.T) xi2Fun * E4Fun * E6Fun := by
  have key : SlashAction.map ((2:ℤ) + 4 + 6) (ModularGroup.S * ModularGroup.T)
      (xi2Fun * E4Fun * E6Fun)
      = SlashAction.map (2:ℤ) (ModularGroup.S * ModularGroup.T) xi2Fun * E4Fun * E6Fun := by
    rw [ModularForm.mul_slash_SL2, ModularForm.mul_slash_SL2,
      Work.Kernels.KernelFacts.E4Fun_slash, Work.Kernels.KernelFacts.E6Fun_slash]
  exact key

/-- `Tr12` kills `ξ₂E₄E₆`. -/
lemma Tr12_xi2E4E6 : Tr12 (xi2Fun * E4Fun * E6Fun) = 0 := by
  have h : xi2Fun * E4Fun * E6Fun + (SlashAction.map (2:ℤ) ModularGroup.S xi2Fun * E4Fun * E6Fun)
      + (SlashAction.map (2:ℤ) (ModularGroup.S * ModularGroup.T) xi2Fun * E4Fun * E6Fun)
      = (xi2Fun + SlashAction.map (2:ℤ) ModularGroup.S xi2Fun
          + SlashAction.map (2:ℤ) (ModularGroup.S * ModularGroup.T) xi2Fun) * (E4Fun * E6Fun) := by
    ring
  rw [Tr12, slash_S_xi2E4E6, slash_ST_xi2E4E6, h, xi2_trace]
  ring

/-! ### The `V²E₄²` term -/

lemma VFun_slash_S : SlashAction.map (2:ℤ) ModularGroup.S VFun = -WFun := by
  funext τ
  rw [Work.Kernels.slash_S_apply, Work.Kernels.KernelFacts.VFun_S_smul_km]
  have hτ : (τ:ℂ) ≠ 0 := Work.Kernels.coe_tau_ne_zero τ
  have hpow : (τ:ℂ) ^ 2 = (τ:ℂ) ^ (2:ℤ) := zpow_natCast (τ:ℂ) 2
  have h2 : (τ:ℂ) ^ (2:ℤ) * (τ:ℂ) ^ (-2:ℤ) = 1 := by rw [← zpow_add₀ hτ]; norm_num
  rw [hpow]
  calc -(τ:ℂ) ^ (2:ℤ) * WFun τ * (τ:ℂ) ^ (-2:ℤ)
      = -(((τ:ℂ) ^ (2:ℤ) * (τ:ℂ) ^ (-2:ℤ)) * WFun τ) := by ring
    _ = -WFun τ := by rw [h2, one_mul]

lemma VFun_slash_ST : SlashAction.map (2:ℤ) (ModularGroup.S * ModularGroup.T) VFun = -UFun := by
  rw [SlashAction.slash_mul, VFun_slash_S, SlashAction.neg_slash, WFun_slash_T]

lemma Vsq_slash_S : SlashAction.map (4:ℤ) ModularGroup.S (VFun ^ 2) = WFun ^ 2 := by
  have key : SlashAction.map ((2:ℤ) + 2) ModularGroup.S (VFun ^ 2) = WFun ^ 2 := by
    rw [pow_two, ModularForm.mul_slash_SL2, VFun_slash_S]
    ring
  exact key

lemma Vsq_slash_ST :
    SlashAction.map (4:ℤ) (ModularGroup.S * ModularGroup.T) (VFun ^ 2) = UFun ^ 2 := by
  have key : SlashAction.map ((2:ℤ) + 2) (ModularGroup.S * ModularGroup.T) (VFun ^ 2)
      = UFun ^ 2 := by
    rw [pow_two, ModularForm.mul_slash_SL2, VFun_slash_ST]
    ring
  exact key

lemma E4sq_slash_S : SlashAction.map (8:ℤ) ModularGroup.S (E4Fun ^ 2) = E4Fun ^ 2 := by
  have key : SlashAction.map ((4:ℤ) + 4) ModularGroup.S (E4Fun ^ 2) = E4Fun ^ 2 := by
    rw [pow_two, ModularForm.mul_slash_SL2, Work.Kernels.KernelFacts.E4Fun_slash]
  exact key

lemma E4sq_slash_ST :
    SlashAction.map (8:ℤ) (ModularGroup.S * ModularGroup.T) (E4Fun ^ 2) = E4Fun ^ 2 := by
  have key : SlashAction.map ((4:ℤ) + 4) (ModularGroup.S * ModularGroup.T) (E4Fun ^ 2)
      = E4Fun ^ 2 := by
    rw [pow_two, ModularForm.mul_slash_SL2, Work.Kernels.KernelFacts.E4Fun_slash]
  exact key

lemma VsqE4sq_slash_S :
    SlashAction.map (12:ℤ) ModularGroup.S (VFun ^ 2 * E4Fun ^ 2) = WFun ^ 2 * E4Fun ^ 2 := by
  have key : SlashAction.map ((4:ℤ) + 8) ModularGroup.S (VFun ^ 2 * E4Fun ^ 2)
      = WFun ^ 2 * E4Fun ^ 2 := by
    rw [ModularForm.mul_slash_SL2, Vsq_slash_S, E4sq_slash_S]
  exact key

lemma VsqE4sq_slash_ST :
    SlashAction.map (12:ℤ) (ModularGroup.S * ModularGroup.T) (VFun ^ 2 * E4Fun ^ 2)
      = UFun ^ 2 * E4Fun ^ 2 := by
  have key : SlashAction.map ((4:ℤ) + 8) (ModularGroup.S * ModularGroup.T)
      (VFun ^ 2 * E4Fun ^ 2) = UFun ^ 2 * E4Fun ^ 2 := by
    rw [ModularForm.mul_slash_SL2, Vsq_slash_ST, E4sq_slash_ST]
  exact key

/-- `Tr12 (V²E₄²) = 2E₄³`. -/
lemma Tr12_VsqE4sq : Tr12 (VFun ^ 2 * E4Fun ^ 2) = fun τ => 2 * E4Fun τ ^ 3 := by
  have hsum : VFun ^ 2 * E4Fun ^ 2 + WFun ^ 2 * E4Fun ^ 2 + UFun ^ 2 * E4Fun ^ 2
      = fun τ => 2 * E4Fun τ ^ 3 := by
    funext τ
    simp only [Pi.add_apply, Pi.mul_apply, Pi.pow_apply]
    rw [Work.Residues.KMinusT_E4Fun_eq_theta τ]
    ring
  rw [Tr12, VsqE4sq_slash_S, VsqE4sq_slash_ST]
  exact hsum

/-! ## Linear independence of `E₄³` and `E₆²` -/

lemma tendsto_UFun : Tendsto UFun atImInfty (nhds (1 : ℂ)) := by
  have hfun : UFun = fun τ : ℍ => Work.Modular.theta3 τ ^ 4 := by
    funext τ; simp [UFun, theta00Fun, Work.Modular.theta3]
  rw [hfun]
  simpa using Work.Modular.tendsto_theta3_atImInfty.pow 4

lemma tendsto_WFun : Tendsto WFun atImInfty (nhds (1 : ℂ)) := by
  have hfun : WFun = fun τ : ℍ => Work.Modular.theta4 τ ^ 4 := by
    funext τ; simp [WFun, theta01Fun, Work.Modular.theta4]
  rw [hfun]
  simpa using Work.Modular.tendsto_theta4_atImInfty.pow 4

lemma tendsto_VFun : Tendsto VFun atImInfty (nhds (0 : ℂ)) := by
  have hfun : VFun = fun τ : ℍ => Work.Modular.theta2 τ ^ 4 := by
    funext τ; simp [VFun, theta10Fun, Work.Modular.theta2]
  rw [hfun]
  simpa using Work.Modular.theta2_at_cusp.pow 4

lemma tendsto_E6Fun : Tendsto E6Fun atImInfty (nhds (1 : ℂ)) := by
  have hfun : E6Fun = fun τ : ℍ => (WFun τ - VFun τ) *
      (VFun τ ^ 2 + WFun τ ^ 2 + (5 / 2) * (VFun τ * WFun τ)) := by
    funext τ
    rw [Work.Kernels.TildeFacts.E6Fun_eq_theta τ]
    ring
  rw [hfun]
  have hm := ((tendsto_WFun.sub tendsto_VFun).mul
    (((tendsto_VFun.pow 2).add (tendsto_WFun.pow 2)).add
      ((tendsto_VFun.mul tendsto_WFun).const_mul (5 / 2))))
  simpa using hm

/-- The discriminant identity `E₄³ - E₆² = 1728Δ`. -/
lemma E4cube_sub_E6sq (τ : ℍ) :
    E4Fun τ ^ 3 - E6Fun τ ^ 2 = 1728 * DeltaFun τ := by
  have h := ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq τ
  have hΔ : DeltaFun τ = ModularForm.discriminant τ := by
    rw [show DeltaFun = ⇑CuspForm.discriminant from rfl, CuspForm.coe_discriminant]
  have hE4 : ModularForm.E₄ τ = E4Fun τ := rfl
  have hE6 : ModularForm.E₆ τ = E6Fun τ := rfl
  rw [hE4, hE6] at h
  have h' : 1728 * DeltaFun τ = E4Fun τ ^ 3 - E6Fun τ ^ 2 := by
    rw [hΔ, h]; field_simp
  linear_combination -h'

/-- If `α E₄³ + β E₆² = 0` as functions then `α = β = 0`. -/
lemma E4cube_E6sq_linearIndependent {α β : ℂ}
    (h : ∀ τ : ℍ, α * E4Fun τ ^ 3 + β * E6Fun τ ^ 2 = 0) : α = 0 ∧ β = 0 := by
  have hlim : α + β = 0 := by
    have h1 : Tendsto (fun τ : ℍ => α * E4Fun τ ^ 3 + β * E6Fun τ ^ 2)
        atImInfty (nhds (α * 1 ^ 3 + β * 1 ^ 2)) :=
      ((tendsto_const_nhds.mul (Work.Modular.E4_tendsto_atImInfty.pow 3)).add
        (tendsto_const_nhds.mul (tendsto_E6Fun.pow 2)))
    have h2 : Tendsto (fun τ : ℍ => α * E4Fun τ ^ 3 + β * E6Fun τ ^ 2)
        atImInfty (nhds 0) := by
      rw [show (fun τ : ℍ => α * E4Fun τ ^ 3 + β * E6Fun τ ^ 2) = fun _ => 0 from
        funext h]
      exact tendsto_const_nhds
    have := tendsto_nhds_unique h1 h2
    simpa using this
  have hβ : β = -α := by linear_combination hlim
  have hα : α = 0 := by
    set i : ℍ := ⟨Complex.I, by simp [Complex.I_im]⟩
    have h2 : α * (E4Fun i ^ 3 - E6Fun i ^ 2) = 0 := by
      have h1 := h i
      rw [hβ] at h1
      linear_combination h1
    rw [E4cube_sub_E6sq] at h2
    exact (mul_eq_zero.mp h2).resolve_right
      (mul_ne_zero (by norm_num) (ClassicalFacts.DeltaFun_ne_zero i))
  refine ⟨hα, ?_⟩
  have := hlim
  rw [hα] at this
  simpa using this

end XiKernelAux

/-
# The trace-kernel inside the four-dimensional space `M₁₂(H)`

`hparam` says `D = a E₄³ + b E₆² + c ξ₂ E₄ E₆ + d V² E₄²`, and the trace relation
`D + D∣[12]S + D∣[12](ST) = 0` then forces `D ∈ ℂ·ξ₄E₄² + ℂ·ξ₂E₄E₆`; see the module
docstring of `XiKernelAux` above for the argument.
-/
theorem XiKernelAtom (D : UpperHalfPlane → Complex)
    (htrace : ∀ τ : UpperHalfPlane, D τ + (τ : Complex) ^ (-12 : ℤ) * D (ModularGroup.S • τ)
        + ((τ : Complex) + 1) ^ (-12 : ℤ) * D (ModularGroup.S • ((1 : Real) +ᵥ τ)) = 0)
    (hparam : ∃ a b c d : Complex, ∀ τ : UpperHalfPlane,
      D τ = a * Work.Kernels.E4Fun τ ^ 3 + b * Work.Kernels.E6Fun τ ^ 2
        + c * (Work.Kernels.xi2Fun τ * Work.Kernels.E4Fun τ * Work.Kernels.E6Fun τ)
        + d * (Work.Kernels.VFun τ ^ 2 * Work.Kernels.E4Fun τ ^ 2)) :
    ∃ c1 c2 : Complex, ∀ τ : UpperHalfPlane,
      D τ = c1 * (Work.Kernels.xi4Fun τ * Work.Kernels.E4Fun τ ^ 2)
        + c2 * (Work.Kernels.xi2Fun τ * Work.Kernels.E4Fun τ * Work.Kernels.E6Fun τ) := by
  obtain ⟨a, b, c, d, hd⟩ := hparam
  -- the trace relation
  have hBzero : XiKernelAux.Tr12 D = 0 := XiKernelAux.Tr12_eq_zero_of_trace D htrace
  -- `D` is the corresponding linear combination of the four basis functions
  have hDsum : D = a • (Work.Kernels.E4Fun ^ 3) + b • (Work.Kernels.E6Fun ^ 2)
      + c • (Work.Kernels.xi2Fun * Work.Kernels.E4Fun * Work.Kernels.E6Fun)
      + d • (Work.Kernels.VFun ^ 2 * Work.Kernels.E4Fun ^ 2) := by
    funext τ
    simp only [Pi.add_apply, Pi.smul_apply, Pi.pow_apply, Pi.mul_apply]
    exact hd τ
  -- applying `Tr12` gives `(3a+2d)E₄³ + 3bE₆² = 0`
  have hkey : ∀ τ : ℍ, (3 * a + 2 * d) * Work.Kernels.E4Fun τ ^ 3
      + (3 * b) * Work.Kernels.E6Fun τ ^ 2 = 0 := by
    intro τ
    have h1 : XiKernelAux.Tr12 D
        = XiKernelAux.Tr12 (a • (Work.Kernels.E4Fun ^ 3) + b • (Work.Kernels.E6Fun ^ 2)
            + c • (Work.Kernels.xi2Fun * Work.Kernels.E4Fun * Work.Kernels.E6Fun)
            + d • (Work.Kernels.VFun ^ 2 * Work.Kernels.E4Fun ^ 2)) := by rw [hDsum]
    rw [hBzero] at h1
    rw [XiKernelAux.Tr12_add, XiKernelAux.Tr12_add, XiKernelAux.Tr12_add,
      XiKernelAux.Tr12_smul, XiKernelAux.Tr12_smul, XiKernelAux.Tr12_smul,
      XiKernelAux.Tr12_smul, XiKernelAux.Tr12_E4cube, XiKernelAux.Tr12_E6sq,
      XiKernelAux.Tr12_xi2E4E6, XiKernelAux.Tr12_VsqE4sq] at h1
    have h2 := congrFun h1 τ
    simp only [Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul, mul_zero,
      add_zero] at h2
    linear_combination -h2
  obtain ⟨hα0, hβ0⟩ := XiKernelAux.E4cube_E6sq_linearIndependent
    (α := 3 * a + 2 * d) (β := 3 * b) hkey
  have hb0 : b = 0 := by linear_combination (1 / 3) * hβ0
  have hd_eq : d = -(3 * a) / 2 := by linear_combination (1 / 2) * hα0
  refine ⟨a / 2, c, fun τ => ?_⟩
  have hxi4 : Work.Kernels.xi4Fun τ
      = 2 * Work.Kernels.E4Fun τ - 3 * Work.Kernels.VFun τ ^ 2 := by
    simp only [Work.Kernels.xi4Fun]
    rw [Work.Residues.KMinusT_E4Fun_eq_theta τ]
    ring
  rw [hd τ, hb0, hd_eq, hxi4]
  ring

end

end Work.Rigidity
