/-
# The "small extension" claim at odd weight

This file proves the pointwise identity which the well-definedness of CKMRV's extension formula
needs (CKMRV, proof of Proposition 3.2(1), the paragraph containing (smallextensionclaim)), in
the odd-weight setting of `Work.Asymptotics.small_extension_odd`.

The two ingredients are

* the finite check `Work.Asymptotics.exists_carry_neighborsP_odd`: for a neighbour `ν` and a row
  `i`, there are *monomial* (or zero) carries `A = c • ofSL γ`, `B = c' • ofSL γ'` with
  `rowDiffOdd ν i - ((T-I)²A + S(T-I)²B) ∈ (1+z)R`, whose group elements are `safe`
  (`SafePairOdd`, `SafePairSOdd`);
* the *safety* itself: the translates `γ • τ, T γ • τ, T² γ • τ` (resp. the `S`-analogues) of a
  safe element land in `O`, so that the two defect identities for `f` may be applied there
  (`Work.Asymptotics.smul_mem_of_mem_SafeThick_odd`).
-/
import Mathlib
import Submission.Work.Asymptotics.OddAssembly
import Submission.Work.Asymptotics.SmallExtensionOddDefs
import Submission.Work.Asymptotics.exists_carry_neighborsP_odd

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix Work.Kernels
open scoped MatrixGroups ModularForm Modular Manifold Bundle Topology

namespace Work.Asymptotics

/-- The translate by `1` is the action of `T`. -/
lemma vadd_one_eq_T_smul (x : ℍ) : (1 : ℝ) +ᵥ x = ModularGroup.T • x := by
  apply UpperHalfPlane.coe_injective
  rw [UpperHalfPlane.coe_vadd, show (((ModularGroup.T • x : ℍ)) : ℂ) = (x : ℂ) + 1 from by
    have h := ModularGroup.coe_T_zpow_smul_eq x (n := 1)
    simpa using h]
  norm_num
  ring

/-- The translate by `2` is the action of `T ^ 2`. -/
lemma vadd_two_eq_T_sq_smul (x : ℍ) : (2 : ℝ) +ᵥ x = (ModularGroup.T ^ 2) • x := by
  rw [show (2 : ℝ) = 1 + 1 from by norm_num, add_vadd, vadd_one_eq_T_smul, vadd_one_eq_T_smul,
    sq, mul_smul]

/-- **The `(T-I)²`-carry identity.**  If `A` is a scalar multiple of a group element whose
`T`-translates all land in `O`, then the defect identity for `f` may be applied to `A`. -/
lemma slash_T2op_eq_of_safe {O O_F : Set ℍ} {f h₁ : ℍ → ℂ} {ν : X} {i : Fin 6} {τ : ℍ}
    (hMpO : ∀ j : Fin 6, ∀ σ ∈ O_F, (Mp j) • σ ∈ O) (hτ : τ ∈ O_F) (hντ : ν • τ ∈ O_F)
    (hT : ∀ x : ℍ, x ∈ O → (1 : ℝ) +ᵥ x ∈ O → (2 : ℝ) +ᵥ x ∈ O → T2op f x = h₁ x)
    {a : Option (ℂ × X)} (hsa : SafePairOdd ν i a) (k : ℤ) :
    slash k (ofOptC a) (T2op f) τ = slash k (ofOptC a) h₁ τ := by
  rcases a with _ | ⟨c, γ⟩
  · simp
  · have hset := hsa c γ rfl
    have h1 : γ ∈ SafeThick ν i := hset (by simp)
    have h2 : ModularGroup.T * γ ∈ SafeThick ν i := hset (by simp)
    have h3 : ModularGroup.T * ModularGroup.T * γ ∈ SafeThick ν i := hset (by simp)
    have e1 : (γ • τ) ∈ O := smul_mem_of_mem_SafeThick_odd hMpO hτ hντ h1
    have hf : T2op f (γ • τ) = h₁ (γ • τ) := by
      refine hT _ e1 ?_ ?_
      · rw [vadd_one_eq_T_smul, ← mul_smul]
        exact smul_mem_of_mem_SafeThick_odd hMpO hτ hντ h2
      · rw [vadd_two_eq_T_sq_smul, sq, ← mul_smul]
        exact smul_mem_of_mem_SafeThick_odd hMpO hτ hντ h3
    simp only [ofOptC_some, Work.Kernels.AlgebraFacts.slash_smul, Pi.smul_apply, smul_eq_mul,
      slash_ofSL, Work.Kernels.slash_apply']
    rw [hf]


/-- **The `S(T-I)²`-carry identity.** -/
lemma slash_S2op_eq_of_safe {O O_F : Set ℍ} {k : ℤ} {f h₂ : ℍ → ℂ} {ν : X} {i : Fin 6} {τ : ℍ}
    (hMpO : ∀ j : Fin 6, ∀ σ ∈ O_F, (Mp j) • σ ∈ O) (hτ : τ ∈ O_F) (hντ : ν • τ ∈ O_F)
    (hS : ∀ x : ℍ, ModularGroup.S • x ∈ O → ModularGroup.S • ((1 : ℝ) +ᵥ x) ∈ O →
      ModularGroup.S • ((2 : ℝ) +ᵥ x) ∈ O → S2op k f x = h₂ x)
    {b : Option (ℂ × X)} (hsb : SafePairSOdd ν i b) :
    slash k (ofOptC b) (S2op k f) τ = slash k (ofOptC b) h₂ τ := by
  rcases b with _ | ⟨c, γ⟩
  · simp
  · have hset := hsb c γ rfl
    have h1 : ModularGroup.S * γ ∈ SafeThick ν i := hset (by simp)
    have h2 : ModularGroup.S * ModularGroup.T * γ ∈ SafeThick ν i :=
      hset (by simp [mul_assoc])
    have h3 : ModularGroup.S * (ModularGroup.T * ModularGroup.T) * γ ∈ SafeThick ν i :=
      hset (by simp [mul_assoc])
    have hf : S2op k f (γ • τ) = h₂ (γ • τ) := by
      refine hS (γ • τ) ?_ ?_ ?_
      · rw [← mul_smul]
        exact smul_mem_of_mem_SafeThick_odd hMpO hτ hντ h1
      · rw [vadd_one_eq_T_smul, ← mul_smul, ← mul_smul]
        exact smul_mem_of_mem_SafeThick_odd hMpO hτ hντ h2
      · rw [vadd_two_eq_T_sq_smul, sq, ← mul_smul, ← mul_smul]
        exact smul_mem_of_mem_SafeThick_odd hMpO hτ hντ h3
    simp only [ofOptC_some, Work.Kernels.AlgebraFacts.slash_smul, Pi.smul_apply, smul_eq_mul,
      slash_ofSL, Work.Kernels.slash_apply']
    rw [hf]

/-- **The small extension claim at odd weight** (CKMRV, proof of Proposition 3.2(1)). -/
theorem small_extension_odd {k : ℤ} (hk : Odd k) {O O_F : Set ℍ} {f h₁ h₂ : ℍ → ℂ}
    (hMpO : ∀ i : Fin 6, ∀ τ ∈ O_F, (Mp i) • τ ∈ O)
    (hT : ∀ x : ℍ, x ∈ O → (1 : ℝ) +ᵥ x ∈ O → (2 : ℝ) +ᵥ x ∈ O → T2op f x = h₁ x)
    (hS : ∀ x : ℍ, ModularGroup.S • x ∈ O → ModularGroup.S • ((1 : ℝ) +ᵥ x) ∈ O →
      ModularGroup.S • ((2 : ℝ) +ᵥ x) ∈ O → S2op k f x = h₂ x)
    {ν : X} (hν : ν ∈ NeighborsP) {τ : ℍ} (hτ : τ ∈ O_F) (hντ : ν • τ ∈ O_F) (i : Fin 6) :
    (∑ j : Fin 6, (sigmaHom ν) i j • (slash k (MpElem j) f) τ)
      + (slash k (carryOdd₁ ν i) h₁) τ
      + (slash k (carryOdd₂ ν i) h₂) τ
      = (slash k (MpElem i * ofSL ν) f) τ := by
  obtain ⟨a, b, hok, hsa, hsb⟩ := exists_carry_neighborsP_odd hν i
  -- the canonical carries agree with the monomial carries modulo `(1+z)R`
  have hdiff : (R_T - 1) ^ 2 * (carryOdd₁ ν i - ofOptC a)
      + R_S * (R_T - 1) ^ 2 * (carryOdd₂ ν i - ofOptC b) ∈ augIdealOdd := by
    have h1 := carryOdd_spec ν i
    have h2 : rowDiffOdd ν i - ((R_T - 1) ^ 2 * ofOptC a
        + R_S * (R_T - 1) ^ 2 * ofOptC b) ∈ augIdealOdd := hok
    have hgen : (Rneg + 1) * carryOdd₃ ν i ∈ augIdealOdd :=
      Submodule.subset_span ⟨1, carryOdd₃ ν i, by rw [one_mul]⟩
    have hthis : (R_T - 1) ^ 2 * (carryOdd₁ ν i - ofOptC a)
        + R_S * (R_T - 1) ^ 2 * (carryOdd₂ ν i - ofOptC b)
        = (rowDiffOdd ν i - (R_T - 1) ^ 2 * ofOptC a - R_S * (R_T - 1) ^ 2 * ofOptC b)
          - (Rneg + 1) * carryOdd₃ ν i := by
      rw [h1]
      noncomm_ring
    rw [hthis]
    have h2' : rowDiffOdd ν i - (R_T - 1) ^ 2 * ofOptC a
        - R_S * (R_T - 1) ^ 2 * ofOptC b ∈ augIdealOdd := by
      simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using h2
    exact Submodule.sub_mem _ h2' hgen
  obtain ⟨hs₁, hs₂⟩ := idealI_direct_augIdealOdd hdiff
  have hcar₁ : slash k (ofOptC a) h₁ = slash k (carryOdd₁ ν i) h₁ :=
    (slash_eq_of_sub_mem_augIdealOdd k hk (by simpa [sub_eq_add_neg] using neg_mem hs₁) h₁)
  have hcar₂ : slash k (ofOptC b) h₂ = slash k (carryOdd₂ ν i) h₂ :=
    (slash_eq_of_sub_mem_augIdealOdd k hk (by simpa [sub_eq_add_neg] using neg_mem hs₂) h₂)
  -- the defect identity applied to the monomial carries
  have hrow : slash k (rowDiffOdd ν i) f τ
      = slash k (ofOptC a) h₁ τ + slash k (ofOptC b) h₂ τ := by
    obtain ⟨Δ, hΔ⟩ := mem_augIdealOdd_exists hok
    have hsplit : rowDiffOdd ν i = ((R_T - 1) ^ 2 * ofOptC a + R_S * (R_T - 1) ^ 2 * ofOptC b)
        + (Rneg + 1) * Δ := by
      rw [← hΔ]; abel
    have hgen : (Rneg + 1) * Δ ∈ augIdealOdd :=
      Submodule.subset_span ⟨1, Δ, by rw [one_mul]⟩
    have hzero : slash k ((Rneg + 1) * Δ) f = 0 :=
      slash_eq_zero_of_mem_augIdealOdd k hk hgen f
    rw [hsplit, Work.Kernels.slash_add, Work.Kernels.slash_add, hzero]
    simp only [Pi.add_apply, Pi.zero_apply, add_zero]
    rw [Work.Kernels.AlgebraFacts.slash_mul, Work.Kernels.slash_T2,
      Work.Kernels.AlgebraFacts.slash_mul,
      show slash k (R_S * (R_T - 1) ^ 2) f = S2op k f from rfl,
      slash_T2op_eq_of_safe hMpO hτ hντ hT hsa k,
      slash_S2op_eq_of_safe hMpO hτ hντ hS hsb]
  -- assemble
  have hexp : slash k (MpElem i * ofSL ν) f τ
      = (∑ j : Fin 6, (sigmaHom ν) i j • (slash k (MpElem j) f) τ)
        + slash k (rowDiffOdd ν i) f τ := by
    have hf : slash k (MpElem i * ofSL ν) f
        = (∑ j : Fin 6, (sigmaHom ν) i j • slash k (MpElem j) f)
          + slash k (rowDiffOdd ν i) f := by
      rw [MpElem_mul_ofSL ν i, Work.Kernels.slash_add, Work.Kernels.slash_sum]
      congr 1
      exact Finset.sum_congr rfl (fun j _ => by rw [Work.Kernels.AlgebraFacts.slash_smul])
    have := congrFun hf τ
    simpa only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply] using this
  rw [hexp, hrow, show slash k (ofOptC a) h₁ τ = slash k (carryOdd₁ ν i) h₁ τ from by
    rw [hcar₁], show slash k (ofOptC b) h₂ τ = slash k (carryOdd₂ ν i) h₂ τ from by rw [hcar₂]]
  ring

end Work.Asymptotics
