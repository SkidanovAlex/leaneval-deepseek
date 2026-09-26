/-
# The carries of the odd-weight defect ideal `𝓘_odd` and the "master relation"

This file sets up the algebraic input for the analytic-continuation half of CKMRV
Proposition 3.2(1) *at odd weight*, in the form needed by
`Work.Asymptotics.exists_extension_of_propagates_odd`.  It is the odd-weight analogue of
`Submission/Work/Asymptotics/PropagateCarries.lean`, with the two substitutions

* the collapse ideal `(z-1)R` is replaced by `(1+z)R = Work.Asymptotics.augIdealOdd`
  (`z = -I`), and
* `Work.Residues.slash_mem_augIdeal` (which uses `(-1)^k = 1`) is replaced by
  `Work.Asymptotics.slash_one_add_Rneg` (which uses `(-1)^k = -1`).

The six elements `MpElem i` of `R = ℂ[SL(2,ℤ)]` (the images of `Work.Asymptotics.Mp`) reduce any
`γ ∈ SL(2,ℤ)` modulo the odd-weight defect ideal `𝓘_odd = (T-I)²R + S(T-I)²R + (1+z)R`:

  `MpElem i * γ = ∑ j, σ γ i j • MpElem j + rowDiffOdd γ i`,   `rowDiffOdd γ i ∈ 𝓘_odd`

(`Work.Asymptotics.exists_sigma_odd`).  Choosing a decomposition of `rowDiffOdd γ i` along the
three generators of `𝓘_odd` gives the *carries*.

The point of the carries is the **master relation** `slash_carry_odd`: because the slash action is
a right action (`slash k (r * s) F = slash k s (slash k r F)`), applying `ξ ∈ 𝓘_odd` to a
function `f` satisfying `T2op f = h₁` and `S2op k f = h₂` at odd weight `k` (so `1 + z` acts as
`0`, `Work.Asymptotics.slash_one_add_Rneg`) gives `slash k ξ f = slash k A h₁ + slash k B h₂`.
-/
import Mathlib
import Submission.Work.Kernels.All
import Submission.Work.Asymptotics.OddIdeal
import Submission.Work.Asymptotics.mem_idealIOdd_exists
import Submission.Work.Asymptotics.exists_sigma_odd
import Submission.Work.Asymptotics.PropagateDefs
import Submission.Work.Asymptotics.PropagateMpDefs

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle

namespace Work.Asymptotics

open Work.Kernels

/-! ## The error vector `rowDiffOdd` -/

/-- `MpElem i` is the monomial attached to the group element `Mp i`; in particular it agrees with
`MpR i` of `PropagateMpDefs`. -/
lemma MpElem_eq_MpR (i : Fin 6) : MpElem i = MpR i := (MpR_eq_of i).symm

lemma MpElem_zero : MpElem (0 : Fin 6) = (1 : R) := by
  show MonoidAlgebra.single (Mp 0) (1 : ℂ) = 1
  rw [show Mp 0 = (1 : SL(2,ℤ)) from rfl, MonoidAlgebra.one_def]

/-- The error vector of the reduction of `MpElem i * ofSL γ` modulo `𝓘_odd`:
`rowDiffOdd γ i = MpElem i * ofSL γ - ∑ j, σ(γ)_{ij} • MpElem j`. -/
def rowDiffOdd (γ : SL(2,ℤ)) (i : Fin 6) : R :=
  MpElem i * ofSL γ - ∑ j, (sigmaHom γ) i j • MpElem j

/-- `rowDiffOdd γ i` lies in the odd-weight defect ideal `𝓘_odd`; this is the content of
`Work.Asymptotics.exists_sigma_odd`, made explicit for the representation `sigmaHom`. -/
theorem rowDiffOdd_mem_idealIOdd (γ : SL(2,ℤ)) (i : Fin 6) : rowDiffOdd γ i ∈ idealIOdd := by
  change MpElem i * ofSL γ - ∑ j, (sigmaMat γ) i j • MpElem j ∈ idealIOdd
  have hkey : Submodule.mkQ idealIOdd
      (MpElem i * ofSL γ - ∑ j, (sigmaMat γ) i j • MpElem j) = 0 := by
    rw [map_sub, map_sum]
    simp only [map_smul]
    rw [← act_mkQ γ (MpElem i), ← Phi_single i]
    have hsum : (∑ j, (sigmaMat γ) i j • Submodule.mkQ idealIOdd (MpElem j))
        = Phi (sHat γ (Pi.single i 1)) := by
      rw [Phi]
      apply Finset.sum_congr rfl
      intro j _
      rw [sigmaMat_row]
    rw [hsum, sHat, LinearMap.add_apply, LinearMap.comp_apply, map_add, Phi_sect_apply,
      Phi_Lam_apply, add_zero, LinearMap.comp_apply, sub_self]
  exact (Submodule.Quotient.mk_eq_zero idealIOdd).mp hkey

/-! ## The carries of `𝓘_odd` -/

/-- The decomposition of `rowDiffOdd γ i` along the three generators of `𝓘_odd`. -/
noncomputable def carrOdd (γ : SL(2,ℤ)) (i : Fin 6) : R × R × R :=
  Classical.choose (show ∃ p : R × R × R,
      rowDiffOdd γ i = (R_T - 1) ^ 2 * p.1
        + R_S * (R_T - 1) ^ 2 * p.2.1 + (Rneg + 1) * p.2.2 from by
    obtain ⟨A, B, C, h⟩ := mem_idealIOdd_exists (rowDiffOdd_mem_idealIOdd γ i)
    exact ⟨(A, B, C), h⟩)

lemma carrOdd_spec (γ : SL(2,ℤ)) (i : Fin 6) :
    rowDiffOdd γ i
      = (R_T - 1) ^ 2 * (carrOdd γ i).1
        + R_S * (R_T - 1) ^ 2 * (carrOdd γ i).2.1
        + (Rneg + 1) * (carrOdd γ i).2.2 :=
  Classical.choose_spec (show ∃ p : R × R × R,
      rowDiffOdd γ i = (R_T - 1) ^ 2 * p.1
        + R_S * (R_T - 1) ^ 2 * p.2.1 + (Rneg + 1) * p.2.2 from by
    obtain ⟨A, B, C, h⟩ := mem_idealIOdd_exists (rowDiffOdd_mem_idealIOdd γ i)
    exact ⟨(A, B, C), h⟩)

/-- The first carry `A` of `rowDiffOdd γ i`, applied to the first defect `h₁`. -/
noncomputable def carryOdd₁ (γ : SL(2,ℤ)) (i : Fin 6) : R := (carrOdd γ i).1

/-- The second carry `B` of `rowDiffOdd γ i`, applied to the second defect `h₂`. -/
noncomputable def carryOdd₂ (γ : SL(2,ℤ)) (i : Fin 6) : R := (carrOdd γ i).2.1

/-- The third carry of `rowDiffOdd γ i`; it is invisible at odd weight (`1 + z` acts as `0`). -/
noncomputable def carryOdd₃ (γ : SL(2,ℤ)) (i : Fin 6) : R := (carrOdd γ i).2.2

lemma carryOdd_spec (γ : SL(2,ℤ)) (i : Fin 6) :
    rowDiffOdd γ i
      = (R_T - 1) ^ 2 * carryOdd₁ γ i
        + R_S * (R_T - 1) ^ 2 * carryOdd₂ γ i
        + (Rneg + 1) * carryOdd₃ γ i :=
  carrOdd_spec γ i

/-! ## The collapsed generator acts by zero -/

/-- Any right multiple of `1 + z` acts by zero on functions of odd weight. -/
lemma slash_augIdealOdd_mul_eq_zero (k : ℤ) (hk : Odd k) (C : R) (F : ℍ → ℂ) :
    slash k ((Rneg + 1) * C) F = 0 := by
  rw [Work.Kernels.AlgebraFacts.slash_mul, slash_one_add_Rneg k hk F]
  exact Work.Kernels.AlgebraFacts.slash_mul_aux_zero k C

/-! ## The master relation -/

/-- **The master relation at odd weight.**  If `f` satisfies the two functional equations
`T2op f = h₁` and `S2op k f = h₂` (everywhere) at odd weight `k`, then the slash of `f` by any
element `ξ` of `𝓘_odd` is the corresponding combination of the defect functions with the carries
of `ξ`. -/
theorem slash_carry_odd (k : ℤ) (hk : Odd k) {ξ : R} (hξ : ξ ∈ idealIOdd)
    {f h₁ h₂ : ℍ → ℂ} (hT : T2op f = h₁) (hS : S2op k f = h₂) :
    ∃ A B : R, slash k ξ f = slash k A h₁ + slash k B h₂ := by
  obtain ⟨A, B, C, rfl⟩ := mem_idealIOdd_exists hξ
  refine ⟨A, B, ?_⟩
  simp only [Work.Kernels.slash_add]
  rw [Work.Kernels.AlgebraFacts.slash_mul, Work.Kernels.slash_T2, hT]
  rw [show Work.Kernels.slash k (R_S * (R_T - 1) ^ 2 * B) f
      = slash k B (S2op k f) from by
    rw [Work.Kernels.AlgebraFacts.slash_mul]; rfl]
  rw [hS]
  rw [slash_augIdealOdd_mul_eq_zero k hk C f]
  ring

/-- The master relation specialised to the error vector `rowDiffOdd`. -/
theorem slash_rowDiffOdd (k : ℤ) (hk : Odd k) (γ : SL(2,ℤ)) (i : Fin 6) {f h₁ h₂ : ℍ → ℂ}
    (hT : T2op f = h₁) (hS : S2op k f = h₂) :
    slash k (rowDiffOdd γ i) f
      = slash k (carryOdd₁ γ i) h₁ + slash k (carryOdd₂ γ i) h₂ := by
  rw [carryOdd_spec γ i]
  simp only [Work.Kernels.slash_add]
  rw [Work.Kernels.AlgebraFacts.slash_mul, Work.Kernels.slash_T2, hT]
  rw [show Work.Kernels.slash k (R_S * (R_T - 1) ^ 2 * carryOdd₂ γ i) f
      = slash k (carryOdd₂ γ i) (S2op k f) from by
    rw [Work.Kernels.AlgebraFacts.slash_mul]; rfl]
  rw [hS]
  rw [slash_augIdealOdd_mul_eq_zero k hk (carryOdd₃ γ i) f]
  ring

/-- **The propagation formula at odd weight.**  For any `γ ∈ SL(2,ℤ)`, the slash by `γ` of a
function `f` satisfying the two functional equations is the corresponding combination of the six
basis slashes `f|Mp_j` and of the two defect functions, with the carries of `rowDiffOdd γ 0` as
coefficients. -/
theorem slash_of_eq_odd (k : ℤ) (hk : Odd k) (γ : SL(2,ℤ)) {f h₁ h₂ : ℍ → ℂ}
    (hT : T2op f = h₁) (hS : S2op k f = h₂) :
    slash k (ofSL γ) f
      = slash k (∑ j : Fin 6, (sigmaHom γ) 0 j • MpElem j) f
        + slash k (carryOdd₁ γ 0) h₁
        + slash k (carryOdd₂ γ 0) h₂ := by
  have hrow := slash_rowDiffOdd k hk γ 0 hT hS
  have hsplit : ofSL γ = (∑ j : Fin 6, (sigmaHom γ) 0 j • MpElem j) + rowDiffOdd γ 0 := by
    rw [rowDiffOdd, MpElem_zero, one_mul, add_comm]
    exact (sub_add_cancel _ _).symm
  conv_lhs => rw [hsplit]
  rw [Work.Kernels.slash_add, hrow, add_assoc]

end Work.Asymptotics
