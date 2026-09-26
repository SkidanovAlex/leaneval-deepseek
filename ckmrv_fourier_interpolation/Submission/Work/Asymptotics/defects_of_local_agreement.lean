/-
# The defects of a holomorphic function admitting a local extension

CKMRV Proposition 3.2(1) (Cohn--Kumar--Miller--Radchenko--Viazovska, *Universal optimality of
the E8 and Leech lattices and interpolation formulas*, Ann. of Math. 196 (2022), Section 3.1)
constructs, from a holomorphic `f` on an open set `O ⊇ closure 𝒟` satisfying the two defect
identities of (3.2),

  `(T-I)² f = h₁`   on `O ∩ T⁻¹O ∩ T⁻²O`,   `S(T-I)² f = h₂`   on `SO ∩ T⁻¹SO ∩ T⁻²SO`,

a holomorphic function `F` on all of `ℍ` agreeing with `f` near `𝒟̄` and having *globally* the
same defects `h₁`, `h₂`.  The last step of that construction is the statement proved here:
once one has *any* holomorphic `F` on `ℍ` agreeing with `f` on a neighbourhood `U` of the closure
of the fundamental domain `𝒟` – no matter how it was produced – the two defects of `F` are
automatically the global functions `h₁` and `h₂`.

The argument is the identity theorem.  Both defect operators preserve holomorphy:
`(T-I)²` is the group-algebra slash by `(R_T - 1)²` and `S(T-I)²` the slash by
`R_S (R_T - 1)²`, and the slash by any element of `R = ℂ[SL(2,ℤ)]` is a finite linear combination
of `F ↦ F ∣[k] γ`, each of which preserves holomorphy (`MDifferentiable.slash`).  Hence
`G₁ = (T-I)²F - h₁` and `G₂ = S(T-I)²F - h₂` are holomorphic on `ℍ`.  They vanish on the open
sets

  `V₁ = {τ | τ, τ+1, τ+2 ∈ U}`,   `V₂ = {τ | S τ, S(τ+1), S(τ+2) ∈ U}`,

because on `U` the function `F` may be replaced by `f` in the defect, and the hypothesis
`Propagates` applies.  Both are nonempty: `Work.Asymptotics.triple_mem_closure_DomainD` produces
`τ` with `τ, τ+1, τ+2 ∈ closure 𝒟 ⊆ U`, and `S` preserves `closure 𝒟`
(`Work.Asymptotics.S_smul_mem_closure_DomainD`), so the same `τ` also lies in `V₂`.  Since `ℍ` is
connected, `UpperHalfPlane.eq_zero_of_frequently` (the identity theorem for holomorphic functions
on `ℍ`) gives `G₁ = 0` and `G₂ = 0`.
-/
import Mathlib
import Submission.Work.Asymptotics.DomainD
import Submission.Work.Asymptotics.PropagateDefs
import Submission.Work.Asymptotics.triple_mem_closure_DomainD
import Submission.Work.Asymptotics.OddIdeal
import Submission.Work.Asymptotics.S_smul_mem_closure_DomainD

namespace Work.Asymptotics

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm Manifold Bundle Topology
open Filter

noncomputable section

/-! ## The defect operators preserve holomorphy -/

/-- The weight-`k` group-algebra slash `F ↦ F|_k r`, `r ∈ R = ℂ[SL(2,ℤ)]`, of a holomorphic
function `F : ℍ → ℂ` is holomorphic: it is a finite linear combination of the slashes
`F ↦ F ∣[k] γ`, and `MDifferentiable.slash` covers those. -/
private lemma mdifferentiable_slash {F : ℍ → ℂ} (hF : MDiff F) (k : ℤ) (r : Work.Kernels.R) :
    MDiff (Work.Kernels.slash k r F) := by
  refine MonoidAlgebra.induction_on (motive := fun r => MDiff (Work.Kernels.slash k r F)) r ?_ ?_ ?_
  · intro m
    rw [MonoidAlgebra.of_apply, Work.Kernels.slash_single]
    simpa only [ModularForm.SL_slash, one_smul] using (hF.slash k (m : GL (Fin 2) ℝ))
  · intro x y hx hy
    rw [Work.Kernels.slash_add]
    exact hx.add hy
  · intro c x hx
    rw [Work.Kernels.AlgebraFacts.slash_smul]
    exact hx.const_smul c

/-- The defect operator `(T-I)²` preserves holomorphy (it is the weight-`k` slash by
`(R_T - 1)²`, whose value is independent of `k`). -/
private lemma mdifferentiable_T2op (k : ℤ) {F : ℍ → ℂ} (hF : MDiff F) : MDiff (Work.Kernels.T2op F) := by
  rw [Work.Asymptotics.T2op_eq_slash_T2 k]
  exact mdifferentiable_slash hF k _

/-- The defect operator `S(T-I)²` preserves holomorphy. -/
private lemma mdifferentiable_S2op (k : ℤ) {F : ℍ → ℂ} (hF : MDiff F) : MDiff (S2op k F) :=
  mdifferentiable_slash hF k _

/-! ## The identity theorem on `ℍ`, and continuity of the two transports -/

/-- **The identity theorem for holomorphic functions on `ℍ`.**  A holomorphic `G : ℍ → ℂ` that
vanishes on a nonempty open subset of `ℍ` vanishes identically. -/
private lemma eq_zero_of_eqOn_isOpen {G : ℍ → ℂ} (hG : MDiff G) {V : Set ℍ} (hV : IsOpen V)
    (hne : V.Nonempty) (hzero : ∀ τ ∈ V, G τ = 0) : G = 0 := by
  obtain ⟨τ₀, hτ₀⟩ := hne
  have hVnhds : V ∈ 𝓝 τ₀ := IsOpen.mem_nhds hV hτ₀
  have hev : G =ᶠ[𝓝 τ₀] 0 := by
    filter_upwards [show ∀ᶠ x in 𝓝 τ₀, x ∈ V from hVnhds] with τ hτ
    exact hzero τ hτ
  exact UpperHalfPlane.eq_zero_of_frequently hG (hev.filter_mono nhdsWithin_le_nhds).frequently

/-- Translation by a real number is continuous on `ℍ`. -/
private lemma continuous_vadd (c : ℝ) : Continuous (fun τ : ℍ => c +ᵥ τ) := by
  rw [UpperHalfPlane.isEmbedding_coe.continuous_iff]
  show Continuous (fun τ : ℍ => (c : ℂ) + (τ : ℂ))
  fun_prop

/-- `S : z ↦ -1/z` is continuous on `ℍ`. -/
private lemma continuous_S_smul : Continuous (fun τ : ℍ => ModularGroup.S • τ) := by
  rw [UpperHalfPlane.isEmbedding_coe.continuous_iff]
  simp only [Function.comp_def]
  have h : (fun τ : ℍ => ((ModularGroup.S • τ : ℍ) : ℂ)) = fun τ : ℍ => -((τ : ℂ))⁻¹ :=
    funext fun τ => Work.Kernels.S_smul_coe τ
  rw [h]
  exact (UpperHalfPlane.continuous_coe.inv₀ (fun τ => UpperHalfPlane.ne_zero τ)).neg

/-! ## The main theorem -/

theorem defects_of_local_agreement {k : ℤ} {O : Set UpperHalfPlane} {f h₁ h₂ : UpperHalfPlane → ℂ}
    (h : Work.Asymptotics.Propagates k O f h₁ h₂) {F : UpperHalfPlane → ℂ}
    (hF : MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) F)
    (hFU : ∃ U : Set UpperHalfPlane, IsOpen U ∧ closure Work.Asymptotics.DomainD ⊆ U ∧ U ⊆ O ∧
      ∀ τ ∈ U, F τ = f τ) :
    (∀ τ : UpperHalfPlane, Work.Kernels.T2op F τ = h₁ τ) ∧
      (∀ τ : UpperHalfPlane, Work.Asymptotics.S2op k F τ = h₂ τ) := by
  obtain ⟨-, hh₁md, hh₂md, -, hT2f, hS2f⟩ := h
  obtain ⟨U, hUopen, hclU, hUO, hFUeq⟩ := hFU
  -- the common witness point: `τ, τ+1, τ+2 ∈ closure 𝒟` and `S τ, S(τ+1), S(τ+2) ∈ closure 𝒟`
  obtain ⟨τ₀, hτ₀, hτ₀₁, hτ₀₂⟩ := Work.Asymptotics.triple_mem_closure_DomainD (t := 1) one_pos
  -- the two open sets of agreement
  have hV₁open : IsOpen {τ : ℍ | τ ∈ U ∧ (1 : ℝ) +ᵥ τ ∈ U ∧ (2 : ℝ) +ᵥ τ ∈ U} := by
    rw [show {τ : ℍ | τ ∈ U ∧ (1 : ℝ) +ᵥ τ ∈ U ∧ (2 : ℝ) +ᵥ τ ∈ U} =
      U ∩ ((fun τ : ℍ => (1 : ℝ) +ᵥ τ) ⁻¹' U) ∩ ((fun τ : ℍ => (2 : ℝ) +ᵥ τ) ⁻¹' U) from by
        ext τ
        simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage]
        tauto]
    exact (hUopen.inter (hUopen.preimage (continuous_vadd 1))).inter
      (hUopen.preimage (continuous_vadd 2))
  have hV₂open : IsOpen {τ : ℍ | S • τ ∈ U ∧ S • ((1 : ℝ) +ᵥ τ) ∈ U ∧
      S • ((2 : ℝ) +ᵥ τ) ∈ U} := by
    rw [show {τ : ℍ | S • τ ∈ U ∧ S • ((1 : ℝ) +ᵥ τ) ∈ U ∧ S • ((2 : ℝ) +ᵥ τ) ∈ U} =
      ((fun τ : ℍ => S • τ) ⁻¹' U) ∩ ((fun τ : ℍ => S • ((1 : ℝ) +ᵥ τ)) ⁻¹' U) ∩
        ((fun τ : ℍ => S • ((2 : ℝ) +ᵥ τ)) ⁻¹' U) from by
        ext τ
        simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage]
        tauto]
    exact ((hUopen.preimage continuous_S_smul).inter
      (hUopen.preimage (continuous_S_smul.comp (continuous_vadd 1)))).inter
      (hUopen.preimage (continuous_S_smul.comp (continuous_vadd 2)))
  have hV₁ne : ({τ : ℍ | τ ∈ U ∧ (1 : ℝ) +ᵥ τ ∈ U ∧ (2 : ℝ) +ᵥ τ ∈ U} : Set ℍ).Nonempty := by
    refine ⟨τ₀, ?_⟩
    exact ⟨hclU hτ₀, hclU hτ₀₁, hclU hτ₀₂⟩
  have hV₂ne : ({τ : ℍ | S • τ ∈ U ∧ S • ((1 : ℝ) +ᵥ τ) ∈ U ∧
      S • ((2 : ℝ) +ᵥ τ) ∈ U} : Set ℍ).Nonempty := by
    refine ⟨τ₀, ?_⟩
    exact ⟨hclU (Work.Asymptotics.S_smul_mem_closure_DomainD hτ₀),
      hclU (Work.Asymptotics.S_smul_mem_closure_DomainD hτ₀₁),
      hclU (Work.Asymptotics.S_smul_mem_closure_DomainD hτ₀₂)⟩
  -- vanishing of the first defect
  have hG₁ : (fun τ : ℍ => Work.Kernels.T2op F τ - h₁ τ) = 0 := by
    refine eq_zero_of_eqOn_isOpen ((mdifferentiable_T2op k hF).sub hh₁md) hV₁open hV₁ne ?_
    rintro τ ⟨h1, h2, h3⟩
    have hft : Work.Kernels.T2op f τ = h₁ τ := hT2f τ (hUO h1) (hUO h2) (hUO h3)
    have e1 := hFUeq τ h1
    have e2 := hFUeq ((1 : ℝ) +ᵥ τ) h2
    have e3 := hFUeq ((2 : ℝ) +ᵥ τ) h3
    simp only [Work.Kernels.T2op] at hft ⊢
    rw [e1, e2, e3, hft, sub_self]
  -- vanishing of the second defect
  have hG₂ : (fun τ : ℍ => S2op k F τ - h₂ τ) = 0 := by
    refine eq_zero_of_eqOn_isOpen ((mdifferentiable_S2op k hF).sub hh₂md) hV₂open hV₂ne ?_
    rintro τ ⟨h1, h2, h3⟩
    have hft : S2op k f τ = h₂ τ := hS2f τ (hUO h1) (hUO h2) (hUO h3)
    have hc : S2op k F τ = S2op k f τ := by
      rw [Work.Asymptotics.S2op_apply_eq k F τ, Work.Asymptotics.S2op_apply_eq k f τ]
      simp only [ModularForm.SL_slash_apply]
      rw [hFUeq _ h3, hFUeq _ h2, hFUeq _ h1]
    rw [hc, hft, sub_self]
  exact ⟨fun τ => sub_eq_zero.mp (congrFun hG₁ τ), fun τ => sub_eq_zero.mp (congrFun hG₂ τ)⟩

end

end Work.Asymptotics
