/-
# Well-definedness of the even-weight extension formula

This file proves the well-definedness (`Work.Asymptotics.PsiEven_well_defined`) of the extension
formula of CKMRV Proposition 3.2(1) at even weight: for a neighbour `ν` of `𝓕̄` and `τ, ν • τ ∈ O_F`,

  `Ψ(γ, ν • τ) = j(ν,τ)^k · Ψ(γν, τ)`,

where `Ψ(γ,τ) = ∑_j σ'(γ)_{0j} (f|_k M'_j)(τ) + (h₁|_k N(γ)_{0,1})(τ) + (h₂|_k N(γ)_{0,2})(τ)`.

The proof combines the three ingredients of the paper:

* the **small extension claim** `Work.Asymptotics.small_extension_claim`, which evaluates the
  reduction of `M'_i ν` on `f` – here it is used for the six rows `i` of the second basis;
* the **cocycle for the carries** `NN_cocycle₁`, `NN_cocycle₂` for the reduction
  `rowDiffP (γν) 0` in terms of `rowDiffP γ 0` and `rowDiffP ν 0` (the collapse-ideal part being
  killed by `Work.Residues.slash_mem_augIdeal` at even weight);
* the **cocycle for the automorphy factor** `Work.Asymptotics.jFun_mul_even`.
-/
import Mathlib
import Submission.Work.Asymptotics.EvenSetup

set_option maxHeartbeats 4000000

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle Topology

namespace Work.Asymptotics

open Work.Kernels Work.Residues

/-- Pulling a scalar out of a sum of scalar multiples. -/
lemma mul_sum_smul_even (a : ℂ) (c Y : Fin 6 → ℂ) :
    (∑ j : Fin 6, c j • (a * Y j)) = a * ∑ j : Fin 6, c j • Y j := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  simp only [smul_eq_mul]
  ring

/-- Distributing a sum of scalar multiples of a three-term sum. -/
lemma sum_smul_expand_even (c : Fin 6 → ℂ) (d : Fin 6 → Fin 6 → ℂ) (X A B : Fin 6 → ℂ) :
    (∑ j : Fin 6, c j • ((∑ l : Fin 6, d j l • X l) + A j + B j))
      = (∑ j : Fin 6, c j • (∑ l : Fin 6, d j l • X l)) + (∑ j : Fin 6, c j • A j)
        + (∑ j : Fin 6, c j • B j) := by
  rw [Finset.sum_congr rfl (fun j _ => by rw [smul_add, smul_add]),
    Finset.sum_add_distrib, Finset.sum_add_distrib]

/-- **The well-definedness identity for the even-weight extension formula.** -/
theorem PsiEven_well_defined {k : ℤ} (hk : Even k) {O O_F : Set ℍ} {f h₁ h₂ : ℍ → ℂ}
    (h : Propagates k O f h₁ h₂) (hMpO : ∀ i : Fin 6, ∀ τ : ℍ, τ ∈ O_F → (Mp i) • τ ∈ O)
    {ν : X} (hν : ν ∈ NeighborsP) {τ : ℍ} (hτ : τ ∈ O_F) (hντ : ν • τ ∈ O_F) (γ : X) :
    PsiEven k f h₁ h₂ (MonoidAlgebra.of ℂ X γ) (ν • τ)
      = Work.Kernels.jFun ν (τ : ℂ) ^ k
        * PsiEven k f h₁ h₂ (MonoidAlgebra.of ℂ X (γ * ν)) τ := by
  /- The small extension claim at each of the six rows. -/
  have hsmall : ∀ i : Fin 6, slash k (MpR i * MonoidAlgebra.of ℂ X ν) f τ
      = (∑ l : Fin 6, (sigmaP (MonoidAlgebra.of ℂ X ν)) i l • slash k (MpR l) f τ)
        + slash k (NN (MonoidAlgebra.of ℂ X ν) i).1 h₁ τ
        + slash k (NN (MonoidAlgebra.of ℂ X ν) i).2 h₂ τ :=
    fun i => small_extension_claim hk h hMpO hν hτ hντ
  /- Step 1: rewriting `Ψ` at `ν • τ` as `j(ν,τ)^k` times the expanded value at `τ`. -/
  have hstep : ∀ (r : R) (g : ℍ → ℂ), slash k r g (ν • τ)
      = Work.Kernels.jFun ν (τ : ℂ) ^ k * slash k (r * MonoidAlgebra.of ℂ X ν) g τ :=
    fun r g => slash_smul_point_even k r g ν τ
  have hPsi : PsiEven k f h₁ h₂ (MonoidAlgebra.of ℂ X γ) (ν • τ)
      = Work.Kernels.jFun ν (τ : ℂ) ^ k
        * ((∑ j : Fin 6, (sigmaP (MonoidAlgebra.of ℂ X γ)) 0 j
              • slash k (MpR j * MonoidAlgebra.of ℂ X ν) f τ)
            + slash k ((NN (MonoidAlgebra.of ℂ X γ) 0).1 * MonoidAlgebra.of ℂ X ν) h₁ τ
            + slash k ((NN (MonoidAlgebra.of ℂ X γ) 0).2 * MonoidAlgebra.of ℂ X ν) h₂ τ) := by
    have e1 : (∑ j : Fin 6, (sigmaP (MonoidAlgebra.of ℂ X γ)) 0 j • slash k (MpR j) f (ν • τ))
        = ∑ j : Fin 6, (sigmaP (MonoidAlgebra.of ℂ X γ)) 0 j
            • (Work.Kernels.jFun ν (τ : ℂ) ^ k * slash k (MpR j * MonoidAlgebra.of ℂ X ν) f τ) :=
      Finset.sum_congr rfl (fun j _ => by rw [hstep (MpR j) f])
    have e2 : slash k (NN (MonoidAlgebra.of ℂ X γ) 0).1 h₁ (ν • τ)
        = Work.Kernels.jFun ν (τ : ℂ) ^ k
          * slash k ((NN (MonoidAlgebra.of ℂ X γ) 0).1 * MonoidAlgebra.of ℂ X ν) h₁ τ :=
      hstep _ _
    have e3 : slash k (NN (MonoidAlgebra.of ℂ X γ) 0).2 h₂ (ν • τ)
        = Work.Kernels.jFun ν (τ : ℂ) ^ k
          * slash k ((NN (MonoidAlgebra.of ℂ X γ) 0).2 * MonoidAlgebra.of ℂ X ν) h₂ τ :=
      hstep _ _
    unfold PsiEven
    rw [e1, e2, e3, mul_sum_smul_even (Work.Kernels.jFun ν (τ : ℂ) ^ k)
        (fun j => (sigmaP (MonoidAlgebra.of ℂ X γ)) 0 j)
        (fun j => slash k (MpR j * MonoidAlgebra.of ℂ X ν) f τ),
      mul_add, mul_add]
  /- Step 2: the three components of the bracket. -/
  have h1 : (∑ j : Fin 6, (sigmaP (MonoidAlgebra.of ℂ X γ)) 0 j
        • (∑ l : Fin 6, (sigmaP (MonoidAlgebra.of ℂ X ν)) j l • slash k (MpR l) f τ))
      = (∑ l : Fin 6, (sigmaP (MonoidAlgebra.of ℂ X (γ * ν))) 0 l • slash k (MpR l) f τ) := by
    rw [sum_smul_sum_smul_even (fun j => (sigmaP (MonoidAlgebra.of ℂ X γ)) 0 j)
      (fun j l => (sigmaP (MonoidAlgebra.of ℂ X ν)) j l) (fun l => slash k (MpR l) f τ)]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [show (∑ j : Fin 6, (sigmaP (MonoidAlgebra.of ℂ X γ)) 0 j
            * (sigmaP (MonoidAlgebra.of ℂ X ν)) j l)
          = (sigmaP (MonoidAlgebra.of ℂ X (γ * ν))) 0 l from by
      rw [← Matrix.mul_apply, ← sigmaP_mul, ← map_mul]]
  have h2 : (∑ j : Fin 6, (sigmaP (MonoidAlgebra.of ℂ X γ)) 0 j
        • slash k (NN (MonoidAlgebra.of ℂ X ν) j).1 h₁ τ)
      = slash k (∑ j : Fin 6, (sigmaP (MonoidAlgebra.of ℂ X γ)) 0 j
          • (NN (MonoidAlgebra.of ℂ X ν) j).1) h₁ τ := by
    exact (congrFun (slash_sum_smul_even k (fun j => (sigmaP (MonoidAlgebra.of ℂ X γ)) 0 j)
      (fun j => (NN (MonoidAlgebra.of ℂ X ν) j).1) h₁) τ).symm
  have h3 : (∑ j : Fin 6, (sigmaP (MonoidAlgebra.of ℂ X γ)) 0 j
        • slash k (NN (MonoidAlgebra.of ℂ X ν) j).2 h₂ τ)
      = slash k (∑ j : Fin 6, (sigmaP (MonoidAlgebra.of ℂ X γ)) 0 j
          • (NN (MonoidAlgebra.of ℂ X ν) j).2) h₂ τ := by
    exact (congrFun (slash_sum_smul_even k (fun j => (sigmaP (MonoidAlgebra.of ℂ X γ)) 0 j)
      (fun j => (NN (MonoidAlgebra.of ℂ X ν) j).2) h₂) τ).symm
  have hA : (∑ j : Fin 6, (sigmaP (MonoidAlgebra.of ℂ X γ)) 0 j
          • slash k (MpR j * MonoidAlgebra.of ℂ X ν) f τ)
      = (∑ l : Fin 6, (sigmaP (MonoidAlgebra.of ℂ X (γ * ν))) 0 l • slash k (MpR l) f τ)
        + slash k (∑ j : Fin 6, (sigmaP (MonoidAlgebra.of ℂ X γ)) 0 j
            • (NN (MonoidAlgebra.of ℂ X ν) j).1) h₁ τ
        + slash k (∑ j : Fin 6, (sigmaP (MonoidAlgebra.of ℂ X γ)) 0 j
            • (NN (MonoidAlgebra.of ℂ X ν) j).2) h₂ τ := by
    have hsumeq : (∑ j : Fin 6, (sigmaP (MonoidAlgebra.of ℂ X γ)) 0 j
            • slash k (MpR j * MonoidAlgebra.of ℂ X ν) f τ)
        = ∑ j : Fin 6, (sigmaP (MonoidAlgebra.of ℂ X γ)) 0 j
            • ((∑ l : Fin 6, (sigmaP (MonoidAlgebra.of ℂ X ν)) j l • slash k (MpR l) f τ)
                + slash k (NN (MonoidAlgebra.of ℂ X ν) j).1 h₁ τ
                + slash k (NN (MonoidAlgebra.of ℂ X ν) j).2 h₂ τ) :=
      Finset.sum_congr rfl (fun j _ => by rw [hsmall j])
    rw [hsumeq, sum_smul_expand_even (fun j => (sigmaP (MonoidAlgebra.of ℂ X γ)) 0 j)
        (fun j l => (sigmaP (MonoidAlgebra.of ℂ X ν)) j l)
        (fun l => slash k (MpR l) f τ) (fun j => slash k (NN (MonoidAlgebra.of ℂ X ν) j).1 h₁ τ)
        (fun j => slash k (NN (MonoidAlgebra.of ℂ X ν) j).2 h₂ τ), h1, h2, h3]
  /- Step 3: the cocycle for the two carries. -/
  have hcarry₁ : slash k (∑ j : Fin 6, (sigmaP (MonoidAlgebra.of ℂ X γ)) 0 j
          • (NN (MonoidAlgebra.of ℂ X ν) j).1) h₁ τ
        + slash k ((NN (MonoidAlgebra.of ℂ X γ) 0).1 * MonoidAlgebra.of ℂ X ν) h₁ τ
      = slash k (NN (MonoidAlgebra.of ℂ X (γ * ν)) 0).1 h₁ τ := by
    have hcoc := NN_cocycle₁ (MonoidAlgebra.of ℂ X γ) (MonoidAlgebra.of ℂ X ν) 0
    have hmul : (MonoidAlgebra.of ℂ X γ * MonoidAlgebra.of ℂ X ν : R)
        = MonoidAlgebra.of ℂ X (γ * ν) := by rw [← map_mul]
    rw [hmul] at hcoc
    have hzero := congrFun (Work.Residues.slash_mem_augIdeal hk hcoc h₁) τ
    rw [Work.Kernels.slash_sub, Work.Kernels.slash_sub] at hzero
    have h1 : Work.Kernels.slash k (NN (MonoidAlgebra.of ℂ X (γ * ν)) 0).1 h₁ τ
          - Work.Kernels.slash k (∑ j : Fin 6, (sigmaP (MonoidAlgebra.of ℂ X γ)) 0 j
              • (NN (MonoidAlgebra.of ℂ X ν) j).1) h₁ τ
        = Work.Kernels.slash k ((NN (MonoidAlgebra.of ℂ X γ) 0).1
            * MonoidAlgebra.of ℂ X ν) h₁ τ := sub_eq_zero.mp hzero
    have h2 := sub_eq_iff_eq_add.mp h1
    rw [add_comm]
    exact h2.symm
  have hcarry₂ : slash k (∑ j : Fin 6, (sigmaP (MonoidAlgebra.of ℂ X γ)) 0 j
          • (NN (MonoidAlgebra.of ℂ X ν) j).2) h₂ τ
        + slash k ((NN (MonoidAlgebra.of ℂ X γ) 0).2 * MonoidAlgebra.of ℂ X ν) h₂ τ
      = slash k (NN (MonoidAlgebra.of ℂ X (γ * ν)) 0).2 h₂ τ := by
    have hcoc := NN_cocycle₂ (MonoidAlgebra.of ℂ X γ) (MonoidAlgebra.of ℂ X ν) 0
    have hmul : (MonoidAlgebra.of ℂ X γ * MonoidAlgebra.of ℂ X ν : R)
        = MonoidAlgebra.of ℂ X (γ * ν) := by rw [← map_mul]
    rw [hmul] at hcoc
    have hzero := congrFun (Work.Residues.slash_mem_augIdeal hk hcoc h₂) τ
    rw [Work.Kernels.slash_sub, Work.Kernels.slash_sub] at hzero
    have h1 : Work.Kernels.slash k (NN (MonoidAlgebra.of ℂ X (γ * ν)) 0).2 h₂ τ
          - Work.Kernels.slash k (∑ j : Fin 6, (sigmaP (MonoidAlgebra.of ℂ X γ)) 0 j
              • (NN (MonoidAlgebra.of ℂ X ν) j).2) h₂ τ
        = Work.Kernels.slash k ((NN (MonoidAlgebra.of ℂ X γ) 0).2
            * MonoidAlgebra.of ℂ X ν) h₂ τ := sub_eq_zero.mp hzero
    have h2 := sub_eq_iff_eq_add.mp h1
    rw [add_comm]
    exact h2.symm
  /- Step 4: assembly. -/
  have hkey : ((∑ j : Fin 6, (sigmaP (MonoidAlgebra.of ℂ X γ)) 0 j
            • slash k (MpR j * MonoidAlgebra.of ℂ X ν) f τ)
          + slash k ((NN (MonoidAlgebra.of ℂ X γ) 0).1 * MonoidAlgebra.of ℂ X ν) h₁ τ
          + slash k ((NN (MonoidAlgebra.of ℂ X γ) 0).2 * MonoidAlgebra.of ℂ X ν) h₂ τ)
      = PsiEven k f h₁ h₂ (MonoidAlgebra.of ℂ X (γ * ν)) τ := by
    rw [hA]
    unfold PsiEven
    have hab : ((((∑ l : Fin 6, (sigmaP (MonoidAlgebra.of ℂ X (γ * ν))) 0 l • slash k (MpR l) f τ)
            + slash k (∑ j : Fin 6, (sigmaP (MonoidAlgebra.of ℂ X γ)) 0 j
                • (NN (MonoidAlgebra.of ℂ X ν) j).1) h₁ τ)
            + slash k (∑ j : Fin 6, (sigmaP (MonoidAlgebra.of ℂ X γ)) 0 j
                • (NN (MonoidAlgebra.of ℂ X ν) j).2) h₂ τ)
            + slash k ((NN (MonoidAlgebra.of ℂ X γ) 0).1 * MonoidAlgebra.of ℂ X ν) h₁ τ)
            + slash k ((NN (MonoidAlgebra.of ℂ X γ) 0).2 * MonoidAlgebra.of ℂ X ν) h₂ τ
        = ((∑ l : Fin 6, (sigmaP (MonoidAlgebra.of ℂ X (γ * ν))) 0 l • slash k (MpR l) f τ)
            + (slash k (∑ j : Fin 6, (sigmaP (MonoidAlgebra.of ℂ X γ)) 0 j
                  • (NN (MonoidAlgebra.of ℂ X ν) j).1) h₁ τ
                + slash k ((NN (MonoidAlgebra.of ℂ X γ) 0).1
                    * MonoidAlgebra.of ℂ X ν) h₁ τ))
            + (slash k (∑ j : Fin 6, (sigmaP (MonoidAlgebra.of ℂ X γ)) 0 j
                  • (NN (MonoidAlgebra.of ℂ X ν) j).2) h₂ τ
                + slash k ((NN (MonoidAlgebra.of ℂ X γ) 0).2
                    * MonoidAlgebra.of ℂ X ν) h₂ τ) := by abel
    rw [hab, hcarry₁, hcarry₂]
  rw [hPsi, hkey]

end Work.Asymptotics
