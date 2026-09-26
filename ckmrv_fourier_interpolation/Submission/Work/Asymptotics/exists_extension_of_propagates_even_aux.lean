import Mathlib
import Submission.Work.Asymptotics.PropagateDefs
import Submission.Work.Asymptotics.DomainD
import Submission.Work.Asymptotics.PropagateCarries
import Submission.Work.Residues.ResidueTheorem
import Submission.Work.Modular.All
import Submission.Work.Asymptotics.EvenSetup
import Submission.Work.Asymptotics.EvenWellDefined
import Submission.Work.Asymptotics.defects_of_local_agreement

namespace Work.Asymptotics

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle Topology

/-- CKMRV Proposition 3.2(1) at even weight (an independent attempt; it is the same statement
as `Work.Asymptotics.exists_extension_of_propagates_even`, which imports the result).

Route (the paper's proof): `R = ℂ[SL(2,ℤ)]`, `𝓘 = (T-I)²R + S(T-I)²R + (z-1)R` with `z = -I`.
`Work.Residues.rowDiff_mem_of_idealI` gives `M6 i * x = ∑ j, σ_R x i j • M6 j + rowDiff x i` with
`rowDiff x i ∈ 𝓘`, and `Submission/Work/Asymptotics/PropagateCarries.lean` (already proved, no
sorries) supplies the carries `N₁, N₂, N₃` and the master relation `slash_carry`.

(1) The carries have the cocycle `N(x·γ) ≡ σ(x)·N(γ) + N(x)·γ` **modulo `(z-1)R`**: this is
`Work.Asymptotics.groupRing_idealI_direct` (freeness of `𝓘`, requested separately; the same
freeness is `Work.Residues`'s Prop 3.3 direct-sum assertion), which gives that two
decompositions of the same element of `𝓘` differ by an element of `(z-1)R`; at even weight
`(z-1)R` acts as `0` by `Work.Residues.slash_mem_augIdeal`.
(2) Let `Mp = (I, T⁻¹, STS, S, ST⁻¹, TS)` (`Work.Asymptotics.Mp`) be the six `SL(2,ℤ)`-elements
tiling `closure DomainD` by translates of `closure DomainF`, and `Neighbors`
(`Work.Asymptotics.Neighbors`). For `ω ∈ Neighbors` and each `i`, the residual
`Mp i * ω - ∑ j, σ'(ω) i j • Mp j` is `0`, `(T-I)²·γ` or `S(T-I)²·γ` for a group element `γ`
(finite check; the paper's "small extension claim").
(3) Shrink `O` to an open `O_F ⊇ closure DomainF` with `⋃ i, Mp i • O_F ⊆ O` and `O_F` so small
that `γ O_F ∩ O_F ≠ ∅ ⟹ γ ∈ Neighbors` (`Work.Asymptotics.exists_neighbour_nbdh`).
(4) Define `F(w)` for `w = γ τ`, `τ ∈ O_F`, by CKMRV's formula
`j(γ,τ)^{-k}F(w) = ∑ j, σ(γ) 0 j • (f|_k Mp j) τ + (h₁|_kN₁) τ + (h₂|_kN₂) τ`; well-definedness
is (1)+(3), holomorphy is local in each `γ O_F`, and `F = f` on the neighbourhood `⋃ i, Mp i •
O_F` of `closure DomainD`.  Then `T2op F - h₁` and `S2op k F - h₂` are holomorphic on `ℍ` and
vanish on an open set, so they vanish (connectedness), giving the two laws. -/
theorem exists_extension_of_propagates_even_aux {k : ℤ} (hk : Even k) {O : Set UpperHalfPlane}
    {f h₁ h₂ : UpperHalfPlane → ℂ}
    (h : Work.Asymptotics.Propagates k O f h₁ h₂)
    (hO : closure Work.Asymptotics.DomainD ⊆ O) :
    ∃ F : UpperHalfPlane → ℂ,
      MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) F ∧
      (∃ U : Set UpperHalfPlane, IsOpen U ∧ closure Work.Asymptotics.DomainD ⊆ U ∧ U ⊆ O ∧
        ∀ τ ∈ U, F τ = f τ) ∧
      (∀ τ : UpperHalfPlane, Work.Kernels.T2op F τ = h₁ τ) ∧
      (∀ τ : UpperHalfPlane, Work.Asymptotics.S2op k F τ = h₂ τ) := by
  have hOopen : IsOpen O := h.1
  have hh₁md : MDiff h₁ := h.2.1
  have hh₂md : MDiff h₂ := h.2.2.1
  have hfOn : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) f O := h.2.2.2.1
  obtain ⟨O_F, hOp, hclF, hMpO, hNbd⟩ :=
    Work.Asymptotics.exists_neighbour_nbdh_of_Propagates hOopen hO
  -- well-definedness of the extension formula
  have hwd : ∀ (γ γ' : X) (τ τ' : UpperHalfPlane), τ ∈ O_F → τ' ∈ O_F → γ • τ = γ' • τ' →
      Work.Kernels.jFun γ (τ : ℂ) ^ k
          * Work.Asymptotics.PsiEven k f h₁ h₂ (MonoidAlgebra.of ℂ X γ) τ
        = Work.Kernels.jFun γ' (τ' : ℂ) ^ k
          * Work.Asymptotics.PsiEven k f h₁ h₂ (MonoidAlgebra.of ℂ X γ') τ' := by
    intro γ γ' τ τ' hτ hτ' heq
    have hν : (γ⁻¹ * γ') • τ' = τ := by rw [mul_smul, ← heq, inv_smul_smul]
    have hmem : γ⁻¹ * γ' ∈ Work.Asymptotics.NeighborsP :=
      hNbd _ ⟨τ', hτ', by rw [hν]; exact hτ⟩
    have hkey := Work.Asymptotics.PsiEven_well_defined (ν := γ⁻¹ * γ') (τ := τ') hk h hMpO
      hmem hτ' (by rw [hν]; exact hτ) γ
    rw [hν] at hkey
    rw [show γ * (γ⁻¹ * γ') = γ' from by rw [← mul_assoc, mul_inv_cancel, one_mul]] at hkey
    rw [hkey]
    rw [show τ = (γ⁻¹ * γ') • τ' from hν.symm, ← mul_assoc, ← mul_zpow,
      show Work.Kernels.jFun γ (((γ⁻¹ * γ') • τ' : UpperHalfPlane) : ℂ)
            * Work.Kernels.jFun (γ⁻¹ * γ') (τ' : ℂ)
          = Work.Kernels.jFun (γ * (γ⁻¹ * γ')) (τ' : ℂ)
        from (Work.Asymptotics.jFun_mul_even γ (γ⁻¹ * γ') τ').symm,
      show γ * (γ⁻¹ * γ') = γ' from by rw [← mul_assoc, mul_inv_cancel, one_mul]]
  let F : UpperHalfPlane → ℂ := Work.Asymptotics.Feven O_F k f h₁ h₂
  have hmd : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F :=
    Work.Asymptotics.mdifferentiable_Feven (O := O) hOp hclF hMpO hfOn hh₁md hh₂md hwd
  have hU : ∃ U : Set UpperHalfPlane, IsOpen U ∧ closure Work.Asymptotics.DomainD ⊆ U ∧
      U ⊆ O ∧ ∀ τ ∈ U, F τ = f τ := by
    refine ⟨⋃ i : Fin 6, (fun τ : UpperHalfPlane => (Work.Asymptotics.Mp i) • τ) '' O_F,
      Work.Asymptotics.isOpen_iUnion_Mp_smul_even hOp,
      Work.Asymptotics.closure_DomainD_subset_iUnion_Mp_smul_even hclF,
      Work.Asymptotics.iUnion_Mp_smul_subset_even hMpO, ?_⟩
    intro τ hτ
    rw [Set.mem_iUnion] at hτ
    obtain ⟨i, σ, hσ, rfl⟩ := hτ
    exact Work.Asymptotics.Feven_Mp_eq (O := O) hk hwd i hσ
  obtain ⟨hd₁, hd₂⟩ := Work.Asymptotics.defects_of_local_agreement h hmd hU
  exact ⟨F, hmd, hU, hd₁, hd₂⟩

end Work.Asymptotics
