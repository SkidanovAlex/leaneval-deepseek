/-
# Analytic assembly for the even-weight propagation (CKMRV Proposition 3.2(1))

This file contains the analytic and group-algebra infrastructure of the even-weight case of
CKMRV Proposition 3.2(1) (`Work.Asymptotics.exists_extension_of_propagates_even_aux`): the
vanishing of the error vector `rowDiffP (of (Mp i)) 0`, the coefficients of the extension
formula `Ψ`, and the holomorphy of the extension
`F w = j(γ,τ)^k Ψ(γ,τ)` (`w = γ • τ`, `τ ∈ O_F`).

## The extension formula

For `x ∈ R = ℂ[SL(2,ℤ)]` and `τ ∈ ℍ` put

  `Ψ x τ = ∑_j σ'(x)_{0j} · (f |_k M'_j)(τ) + (h₁ |_k N(x)_{0,1})(τ) + (h₂ |_k N(x)_{0,2})(τ)`,

where `N` is the carry of `rowDiffP x 0` (`Work.Asymptotics.NN`).  The paper's extension formula
is `F w = j(γ,τ)^k Ψ (of γ) τ` for `w = γ • τ`, `τ ∈ O_F`; its well-definedness is
`Work.Asymptotics.PsiEven_well_defined`, proved in `EvenWellDefined.lean`.

The key structural input proved here is that row `0` of `σ'(M'_i)` is the `i`-th standard basis
vector, so that the error vector of `M'_i` itself vanishes
(`Work.Asymptotics.rowDiffP_of_Mp`) and the extension formula reproduces `f` on every translate
`M'_i • O_F` without any use of the propagation hypotheses
(`Work.Asymptotics.Feven_Mp_eq`).
-/
import Mathlib
import Submission.Work.Asymptotics.SmallExtensionClaim
import Submission.Work.Asymptotics.defects_of_local_agreement
import Submission.Work.Asymptotics.upperHalfPlane_subset_iUnion_smul_closure_DomainF
import Submission.Work.Asymptotics.carry_letters_assembly

set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle Topology

namespace Work.Asymptotics

open Work.Kernels Work.Residues

/-- The action of `SL(2,ℤ)` on `ℍ` is continuous (the group is discrete). -/
instance continuousSMul_sl2z_uhp_even : ContinuousSMul SL(2,ℤ) ℍ :=
  MulAction.continuousSMul_compHom (f := SpecialLinearGroup.mapGL ℝ)
    continuous_of_discreteTopology

/-! ## Row `0` of `σ'(M'_i)` -/

/-- The explicit matrix `σ'(S)`. -/
def sigmaP_S_mat : Matrix (Fin 6) (Fin 6) ℂ :=
  !![0,0,0,1,0,0; 0,0,0,2,0,-1; 0,0,0,2,-1,0; 1,0,0,0,0,0; 2,0,-1,0,0,0; 2,-1,0,0,0,0]

/-- The explicit matrix `σ'(T)`. -/
def sigmaP_T_mat : Matrix (Fin 6) (Fin 6) ℂ :=
  !![2,-1,0,0,0,0; 1,0,0,0,0,0; 0,0,0,2,0,-1; 0,0,0,2,-1,0; 0,0,0,1,0,0; 2,0,-1,0,0,0]

lemma sigmaP_R_S_eq : sigmaP R_S = sigmaP_S_mat := by
  ext i j
  fin_cases i <;> simp only [sigmaP_S_mat]
  · rw [show R_S = MonoidAlgebra.of ℂ X (ModularGroup.S) from (of_S).symm]
    exact sigmaP_ofS_row0 j
  · rw [show R_S = MonoidAlgebra.of ℂ X (ModularGroup.S) from (of_S).symm]
    exact sigmaP_ofS_row1 j
  · rw [show R_S = MonoidAlgebra.of ℂ X (ModularGroup.S) from (of_S).symm]
    exact sigmaP_ofS_row2 j
  · rw [show R_S = MonoidAlgebra.of ℂ X (ModularGroup.S) from (of_S).symm]
    exact sigmaP_ofS_row3 j
  · rw [show R_S = MonoidAlgebra.of ℂ X (ModularGroup.S) from (of_S).symm]
    exact sigmaP_ofS_row4 j
  · rw [show R_S = MonoidAlgebra.of ℂ X (ModularGroup.S) from (of_S).symm]
    exact sigmaP_ofS_row5 j

lemma sigmaP_R_T_eq : sigmaP R_T = sigmaP_T_mat := by
  ext i j
  fin_cases i <;> simp only [sigmaP_T_mat]
  · rw [show R_T = MonoidAlgebra.of ℂ X (ModularGroup.T) from (of_T).symm]
    exact sigmaP_ofT_row0 j
  · rw [show R_T = MonoidAlgebra.of ℂ X (ModularGroup.T) from (of_T).symm]
    exact sigmaP_ofT_row1 j
  · rw [show R_T = MonoidAlgebra.of ℂ X (ModularGroup.T) from (of_T).symm]
    exact sigmaP_ofT_row2 j
  · rw [show R_T = MonoidAlgebra.of ℂ X (ModularGroup.T) from (of_T).symm]
    exact sigmaP_ofT_row3 j
  · rw [show R_T = MonoidAlgebra.of ℂ X (ModularGroup.T) from (of_T).symm]
    exact sigmaP_ofT_row4 j
  · rw [show R_T = MonoidAlgebra.of ℂ X (ModularGroup.T) from (of_T).symm]
    exact sigmaP_ofT_row5 j

lemma of_STS : (MonoidAlgebra.of ℂ X (ModularGroup.S * ModularGroup.T * ModularGroup.S) : R)
    = R_S * R_T * R_S := by
  rw [map_mul, map_mul, of_S, of_T]

/-- Row `0` of `σ'(STS)`, the last of the six rows of the second basis: `STS = M'_2`. -/
lemma sigmaP_ofSTS_row0 (j : Fin 6) :
    (sigmaP (MonoidAlgebra.of ℂ X (ModularGroup.S * ModularGroup.T * ModularGroup.S))) 0 j =
      (if j = 2 then 1 else 0 : ℂ) := by
  rw [of_STS]
  rw [show sigmaP (R_S * R_T * R_S) = sigmaP R_S * sigmaP R_T * sigmaP R_S from by
    rw [sigmaP_mul, sigmaP_mul]]
  rw [sigmaP_R_S_eq, sigmaP_R_T_eq]
  fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_six, sigmaP_S_mat, sigmaP_T_mat]

/-- **Row `0` of `σ'(M'_i)` is the `i`-th standard basis vector**: `σ'` reads off the
coordinates in the second basis `M' = (I, T⁻¹, STS, S, ST⁻¹, TS)` of `R/𝓘`. -/
lemma sigmaP_Mp_row0 (i j : Fin 6) :
    (sigmaP (MonoidAlgebra.of ℂ X (Mp i))) 0 j = (if j = i then 1 else 0 : ℂ) := by
  revert j
  fin_cases i
  · intro j
    show (sigmaP (MonoidAlgebra.of ℂ X (Mp (0 : Fin 6)))) 0 j =
      (if j = (0 : Fin 6) then 1 else 0 : ℂ)
    rw [show Mp (0 : Fin 6) = (1 : X) by decide, map_one, sigmaP_one]
    simp [Matrix.one_apply, eq_comm]
  · intro j
    show (sigmaP (MonoidAlgebra.of ℂ X (Mp (1 : Fin 6)))) 0 j =
      (if j = (1 : Fin 6) then 1 else 0 : ℂ)
    rw [show Mp (1 : Fin 6) = ModularGroup.T⁻¹ by decide, sigmaP_ofTinv_row0 j]
    fin_cases j <;> simp
  · intro j
    show (sigmaP (MonoidAlgebra.of ℂ X (Mp (2 : Fin 6)))) 0 j =
      (if j = (2 : Fin 6) then 1 else 0 : ℂ)
    rw [show Mp (2 : Fin 6) = ModularGroup.S * ModularGroup.T * ModularGroup.S by decide,
      sigmaP_ofSTS_row0 j]
  · intro j
    show (sigmaP (MonoidAlgebra.of ℂ X (Mp (3 : Fin 6)))) 0 j =
      (if j = (3 : Fin 6) then 1 else 0 : ℂ)
    rw [show Mp (3 : Fin 6) = ModularGroup.S by decide, sigmaP_ofS_row0 j]
    fin_cases j <;> simp
  · intro j
    show (sigmaP (MonoidAlgebra.of ℂ X (Mp (4 : Fin 6)))) 0 j =
      (if j = (4 : Fin 6) then 1 else 0 : ℂ)
    rw [show Mp (4 : Fin 6) = ModularGroup.S * ModularGroup.T⁻¹ by decide, sigmaP_ofSTinv_row0 j]
    fin_cases j <;> simp
  · intro j
    show (sigmaP (MonoidAlgebra.of ℂ X (Mp (5 : Fin 6)))) 0 j =
      (if j = (5 : Fin 6) then 1 else 0 : ℂ)
    rw [show Mp (5 : Fin 6) = ModularGroup.T * ModularGroup.S by decide, sigmaP_ofTS_row0 j]
    fin_cases j <;> simp

/-- **The error vector of `M'_i` vanishes**: `rowDiffP (of (Mp i)) 0 = 0`, i.e. the reduction
of the basis element `M'_i` in the second basis is trivial. -/
lemma rowDiffP_of_Mp (i : Fin 6) :
    rowDiffP (MonoidAlgebra.of ℂ X (Mp i)) 0 = 0 := by
  rw [rowDiffP, MpR_zero, one_mul]
  rw [Finset.sum_congr rfl (fun j _ => by rw [sigmaP_Mp_row0 i j])]
  rw [Finset.sum_eq_single i (fun j _ hj => by rw [if_neg hj, zero_smul])
      (fun h => absurd (Finset.mem_univ i) h)]
  rw [if_pos rfl, one_smul, MpR_eq_of i]
  exact sub_self _

/-- The carry of `rowDiffP (of (Mp i)) 0 = 0` lies in the collapse ideal, so it slashes to `0`
on every function at even weight. -/
lemma NN_Mp_mem_augIdeal (i : Fin 6) :
    (NN (MonoidAlgebra.of ℂ X (Mp i)) 0).1 ∈ augIdeal ∧
      (NN (MonoidAlgebra.of ℂ X (Mp i)) 0).2 ∈ augIdeal := by
  have h : (R_T - 1) ^ 2 * (NN (MonoidAlgebra.of ℂ X (Mp i)) 0).1
      + R_S * (R_T - 1) ^ 2 * (NN (MonoidAlgebra.of ℂ X (Mp i)) 0).2 ∈ augIdeal := by
    have hspec := NN_spec (MonoidAlgebra.of ℂ X (Mp i)) 0
    rw [rowDiffP_of_Mp, zero_sub] at hspec
    simpa using Submodule.neg_mem _ hspec
  exact idealI_direct_augIdeal h

/-! ## The automorphy cocycle and the slash at a translate -/

/-- **The cocycle identity for the automorphy factor.** -/
lemma jFun_mul_even (γ δ : X) (τ : ℍ) :
    Work.Kernels.jFun (γ * δ) (τ : ℂ)
      = Work.Kernels.jFun γ ((δ • τ : ℍ) : ℂ) * Work.Kernels.jFun δ (τ : ℂ) := by
  have h := congrFun (SlashAction.slash_mul (-1 : ℤ) γ δ (1 : ℍ → ℂ)) τ
  rw [Work.Kernels.slash_apply', Work.Kernels.slash_apply', Work.Kernels.slash_apply'] at h
  simpa using h

/-- **The slash at a translate.**  Evaluating the slash by `r` at the point `ν • τ` is the same
as evaluating the slash by `r * of ν` at `τ`, up to the automorphy factor
`j(ν,τ)^k`. -/
lemma slash_smul_point_even (k : ℤ) (r : R) (g : ℍ → ℂ) (ν : X) (τ : ℍ) :
    slash k r g (ν • τ)
      = Work.Kernels.jFun ν (τ : ℂ) ^ k * slash k (r * MonoidAlgebra.of ℂ X ν) g τ := by
  have h : slash k (r * MonoidAlgebra.of ℂ X ν) g τ
      = slash k r g (ν • τ) * Work.Kernels.jFun ν (τ : ℂ) ^ (-k) := by
    rw [Work.Kernels.AlgebraFacts.slash_mul]
    rw [show MonoidAlgebra.of ℂ X ν = MonoidAlgebra.single ν (1 : ℂ) from by
      rw [MonoidAlgebra.of_apply]]
    rw [Work.Kernels.slash_single, one_smul, Work.Kernels.slash_apply']
  rw [h, ← mul_assoc, mul_comm (Work.Kernels.jFun ν (τ : ℂ) ^ k) (slash k r g (ν • τ)),
    mul_assoc, ← zpow_add₀ (Work.Kernels.jFun_ne_zero ν τ) k (-k), add_neg_cancel, zpow_zero,
    mul_one]

/-- `slash k · g` is `ℂ`-linear in the group-algebra element. -/
lemma slash_sum_smul_even (k : ℤ) (c : Fin 6 → ℂ) (r : Fin 6 → R) (g : ℍ → ℂ) :
    slash k (∑ j, c j • r j) g = ∑ j, c j • slash k (r j) g := by
  rw [show (∑ j : Fin 6, c j • r j) = ∑ j ∈ Finset.univ, c j • r j from rfl,
    Work.Kernels.slash_sum]
  exact Finset.sum_congr rfl
    (fun j _ => Work.Kernels.AlgebraFacts.slash_smul k (c j) (r j) g)

/-- A double sum of scalars reassociated: `∑_j c_j (∑_l d_{jl} x_l) = ∑_l (∑_j c_j d_{jl}) x_l`. -/
lemma sum_smul_sum_smul_even (c : Fin 6 → ℂ) (d : Fin 6 → Fin 6 → ℂ) (X : Fin 6 → ℂ) :
    (∑ j, c j • (∑ l, d j l • X l)) = ∑ l, (∑ j, c j * d j l) • X l := by
  simp only [smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  ring


/-! ## The slash of a monomial and of the six basis elements -/

/-- The slash by the group-algebra monomial `of γ` is the slash by `γ`. -/
lemma slash_ofX_even (k : ℤ) (γ : SL(2,ℤ)) (F : ℍ → ℂ) :
    slash k (MonoidAlgebra.of ℂ SL(2,ℤ) γ) F = F ∣[k] γ := by
  rw [show MonoidAlgebra.of ℂ SL(2,ℤ) γ = MonoidAlgebra.single γ (1 : ℂ) from by
      rw [MonoidAlgebra.of_apply], Work.Kernels.slash_single]
  exact one_smul ℂ _

/-- The slash by `M'_i` is the slash by the group element `Mp i`. -/
lemma slash_MpR_even (k : ℤ) (i : Fin 6) (F : ℍ → ℂ) :
    slash k (MpR i) F = F ∣[k] (Mp i) := by
  rw [MpR_eq_of, slash_ofX_even]

/-! ## The extension formula `Ψ` -/

/-- The CKMRV expansion of `j(γ,τ)^{-k}F(γ • τ)`: the six basis slashes `f|M'_j` with the
coefficients from row `0` of the representation `σ'`, plus the two defect functions `h₁`, `h₂`
slashed by the carries of `rowDiffP x 0`. -/
noncomputable def PsiEven (k : ℤ) (f h₁ h₂ : ℍ → ℂ) (x : R) (τ : ℍ) : ℂ :=
  (∑ j : Fin 6, (sigmaP x) 0 j • slash k (MpR j) f τ)
    + slash k (NN x 0).1 h₁ τ + slash k (NN x 0).2 h₂ τ

/-- On the six basis elements the extension formula reproduces the slash of `f`: the carries
of `rowDiffP (of (Mp i)) 0 = 0` lie in the collapse ideal and row `0` of `σ'(of (Mp i))` is the
`i`-th standard basis vector. -/
lemma PsiEven_Mp_eq {k : ℤ} (hk : Even k) {f h₁ h₂ : ℍ → ℂ} (i : Fin 6) (τ : ℍ) :
    PsiEven k f h₁ h₂ (MonoidAlgebra.of ℂ X (Mp i)) τ = slash k (MpR i) f τ := by
  have hsum : (∑ j : Fin 6, (sigmaP (MonoidAlgebra.of ℂ X (Mp i))) 0 j • slash k (MpR j) f τ)
      = slash k (MpR i) f τ := by
    rw [Finset.sum_eq_single i
      (fun j _ hj => by rw [sigmaP_Mp_row0 i j, if_neg hj, zero_smul])
      (fun h => absurd (Finset.mem_univ i) h)]
    rw [sigmaP_Mp_row0 i i, if_pos rfl, one_smul]
  have hA : slash k (NN (MonoidAlgebra.of ℂ X (Mp i)) 0).1 h₁ τ = 0 :=
    congrFun (Work.Residues.slash_mem_augIdeal hk (NN_Mp_mem_augIdeal i).1 h₁) τ
  have hB : slash k (NN (MonoidAlgebra.of ℂ X (Mp i)) 0).2 h₂ τ = 0 :=
    congrFun (Work.Residues.slash_mem_augIdeal hk (NN_Mp_mem_augIdeal i).2 h₂) τ
  unfold PsiEven
  rw [hsum, hA, hB, add_zero, add_zero]

/-! ## Holomorphy -/

/-- The weight-`k` group-algebra slash of a holomorphic function is holomorphic. -/
lemma mdifferentiable_slash_even {F : ℍ → ℂ} (hF : MDiff F) (k : ℤ) (r : R) :
    MDiff (slash k r F) := by
  refine MonoidAlgebra.induction_on (motive := fun r => MDiff (slash k r F)) r ?_ ?_ ?_
  · intro m
    rw [MonoidAlgebra.of_apply, Work.Kernels.slash_single]
    simpa only [ModularForm.SL_slash, one_smul] using (hF.slash k (m : GL (Fin 2) ℝ))
  · intro x y hx hy
    rw [Work.Kernels.slash_add]
    exact hx.add hy
  · intro c x hx
    rw [Work.Kernels.AlgebraFacts.slash_smul]
    exact hx.const_smul c

/-- The slash by `γ` of a function holomorphic on `O` is holomorphic on `O_F`, provided
`γ • O_F ⊆ O`. -/
lemma mdifferentiableOn_slash_of_mapsTo_even {O O_F : Set ℍ} {γ : SL(2,ℤ)} {f : ℍ → ℂ}
    (hsub : ∀ τ ∈ O_F, γ • τ ∈ O) (hf : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) f O) (k : ℤ) :
    MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) (fun τ : ℍ => (f ∣[k] γ) τ) O_F := by
  have hdet : 0 < (Work.Kernels.glOf γ).det.val := by
    simp [Work.Kernels.glOf, Matrix.SpecialLinearGroup.coeToGL_det]
  have hsmul : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun τ : ℍ => γ • τ) :=
    UpperHalfPlane.mdifferentiable_smul hdet
  have hj : MDifferentiable 𝓘(ℂ) 𝓘(ℂ)
      (fun τ : ℍ => (Work.Kernels.jFun γ (τ : ℂ)) ^ (-k)) :=
    UpperHalfPlane.mdifferentiable_denom_zpow (Work.Kernels.glOf γ) (-k)
  have hcoe : (fun τ : ℍ => (f ∣[k] γ) τ)
      = fun τ : ℍ => f (γ • τ) * (Work.Kernels.jFun γ (τ : ℂ)) ^ (-k) := by
    funext τ
    rw [Work.Kernels.slash_apply']
  rw [hcoe]
  have hcomp : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) (fun τ : ℍ => f (γ • τ)) O_F :=
    MDifferentiableOn.comp (I := 𝓘(ℂ)) (I' := 𝓘(ℂ)) (I'' := 𝓘(ℂ)) (u := O) (s := O_F)
      hf hsmul.mdifferentiableOn (fun τ hτ => hsub τ hτ)
  exact hcomp.mul hj.mdifferentiableOn

/-- `Ψ x` is holomorphic on `O_F` whenever the six translates `Mp i • O_F` land in `O` and the
two defect functions are holomorphic. -/
lemma mdifferentiableOn_PsiEven {O O_F : Set ℍ} {k : ℤ} {f h₁ h₂ : ℍ → ℂ}
    (hMpO : ∀ i : Fin 6, ∀ τ ∈ O_F, (Mp i) • τ ∈ O)
    (hf : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) f O) (hh₁ : MDiff h₁) (hh₂ : MDiff h₂) (x : R) :
    MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) (PsiEven k f h₁ h₂ x) O_F := by
  have hterm : ∀ j : Fin 6, MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ)
      (fun τ : ℍ => (sigmaP x) 0 j • slash k (MpR j) f τ) O_F := by
    intro j
    refine MDifferentiableOn.const_smul _ ?_
    have h := mdifferentiableOn_slash_of_mapsTo_even (O := O) (O_F := O_F) (γ := Mp j)
      (fun τ hτ => hMpO j τ hτ) hf k
    simpa only [slash_MpR_even] using h
  have hsum : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ)
      (fun τ : ℍ => ∑ j : Fin 6, (sigmaP x) 0 j • slash k (MpR j) f τ) O_F :=
    MDifferentiableOn.sum (s := O_F) (t := Finset.univ)
      (f := fun j : Fin 6 => fun τ : ℍ => (sigmaP x) 0 j • slash k (MpR j) f τ)
      (fun j _ => hterm j)
  unfold PsiEven
  exact ((hsum.add
    (mdifferentiable_slash_even hh₁ k (NN x 0).1).mdifferentiableOn).add
    (mdifferentiable_slash_even hh₂ k (NN x 0).2).mdifferentiableOn)

/-! ## The geometry of the translates of `O_F` -/

/-- Every point of `ℍ` is carried into `O_F` by some `SL(2,ℤ)`-translate. -/
lemma exists_inv_smul_mem_even {O_F : Set ℍ} (hFF : closure DomainF ⊆ O_F) (w : ℍ) :
    ∃ γ : SL(2,ℤ), γ⁻¹ • w ∈ O_F := by
  have hw : w ∈ ⋃ γ : SL(2,ℤ), (fun τ : ℍ => γ • τ) '' closure DomainF :=
    upperHalfPlane_subset_iUnion_smul_closure_DomainF (Set.mem_univ w)
  rw [Set.mem_iUnion] at hw
  obtain ⟨γ, hγ⟩ := hw
  rw [Set.mem_image] at hγ
  obtain ⟨x, hx, rfl⟩ := hγ
  exact ⟨γ, by rw [inv_smul_smul]; exact hFF hx⟩

/-- The open set `⋃ i, (Mp i) • O_F` covers `closure 𝒟`. -/
lemma closure_DomainD_subset_iUnion_Mp_smul_even {O_F : Set ℍ} (hFF : closure DomainF ⊆ O_F) :
    closure DomainD ⊆ ⋃ i : Fin 6, (fun τ : ℍ => (Mp i) • τ) '' O_F :=
  closure_DomainD_subset_iUnion_Mp.trans (Set.iUnion_mono fun i => Set.image_mono hFF)

/-- The set `⋃ i, (Mp i) • O_F` is contained in any open set containing the six translates
`Mp i • O_F`. -/
lemma iUnion_Mp_smul_subset_even {O O_F : Set ℍ}
    (hMpO : ∀ i : Fin 6, ∀ τ ∈ O_F, (Mp i) • τ ∈ O) :
    (⋃ i : Fin 6, (fun τ : ℍ => (Mp i) • τ) '' O_F) ⊆ O := by
  intro w hw
  rw [Set.mem_iUnion] at hw
  obtain ⟨i, τ, hτ, rfl⟩ := hw
  exact hMpO i τ hτ

/-- The translate `γ • O_F` of an open set is open. -/
lemma isOpen_smul_image_even {O_F : Set ℍ} (hOp : IsOpen O_F) (γ : SL(2,ℤ)) :
    IsOpen ((fun τ : ℍ => γ • τ) '' O_F) := by
  have hset : (fun τ : ℍ => γ • τ) '' O_F = (fun τ : ℍ => γ⁻¹ • τ) ⁻¹' O_F := by
    ext w
    constructor
    · rintro ⟨τ, hτ, rfl⟩
      show γ⁻¹ • (γ • τ) ∈ O_F
      rwa [inv_smul_smul]
    · intro hw
      refine ⟨γ⁻¹ • w, hw, ?_⟩
      show γ • (γ⁻¹ • w) = w
      rw [smul_inv_smul]
  rw [hset]
  exact hOp.preimage (continuous_const_smul γ⁻¹)

/-- `⋃ i, (Mp i) • O_F` is open. -/
lemma isOpen_iUnion_Mp_smul_even {O_F : Set ℍ} (hOp : IsOpen O_F) :
    IsOpen (⋃ i : Fin 6, (fun τ : ℍ => (Mp i) • τ) '' O_F) := by
  refine isOpen_iUnion fun i => ?_
  exact isOpen_smul_image_even hOp (Mp i)

/-! ## The extension `F` -/

/-- **The extension of `f` to `ℍ`.**  For `w ∈ ℍ`, choose `γ ∈ SL(2,ℤ)` and `τ ∈ O_F` with
`w = γ • τ` and set `F w = j(γ,τ)^k Ψ(γ,τ)`.  The value does not depend on the choice (see
`Feven_apply`, which uses the well-definedness hypothesis). -/
noncomputable def Feven (O_F : Set ℍ) (k : ℤ) (f h₁ h₂ : ℍ → ℂ) (w : ℍ) : ℂ := by
  classical
  exact if h : ∃ p : SL(2,ℤ) × ℍ, p.2 ∈ O_F ∧ p.1 • p.2 = w then
    Work.Kernels.jFun (Classical.choose h).1 ((Classical.choose h).2 : ℂ) ^ k
      * PsiEven k f h₁ h₂ (MonoidAlgebra.of ℂ X (Classical.choose h).1) (Classical.choose h).2
  else 0

/-- The local expression for the extension on the `γ`-translate of `O_F`:
`w ↦ j(γ, γ⁻¹w)^k Ψ(γ, γ⁻¹w)`. -/
noncomputable def PsiEvenLoc (k : ℤ) (f h₁ h₂ : ℍ → ℂ) (γ : SL(2,ℤ)) (w : ℍ) : ℂ :=
  Work.Kernels.jFun γ ((γ⁻¹ • w : ℍ) : ℂ) ^ k
    * PsiEven k f h₁ h₂ (MonoidAlgebra.of ℂ X γ) (γ⁻¹ • w)

/-- The local expression `PsiEvenLoc γ` is holomorphic on `γ • O_F`. -/
lemma mdifferentiableAt_PsiEvenLoc {O O_F : Set ℍ} {k : ℤ} {f h₁ h₂ : ℍ → ℂ}
    (hOp : IsOpen O_F) (hMpO : ∀ i : Fin 6, ∀ τ ∈ O_F, (Mp i) • τ ∈ O)
    (hf : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) f O) (hh₁ : MDiff h₁) (hh₂ : MDiff h₂)
    {γ : SL(2,ℤ)} {w : ℍ} (hw : γ⁻¹ • w ∈ O_F) :
    MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (PsiEvenLoc k f h₁ h₂ γ) w := by
  have hdet : 0 < (Work.Kernels.glOf γ⁻¹).det.val := by
    simp [Work.Kernels.glOf, Matrix.SpecialLinearGroup.coeToGL_det]
  have hsmul : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun x : ℍ => γ⁻¹ • x) :=
    UpperHalfPlane.mdifferentiable_smul hdet
  have hj : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ)
      (fun σ : ℍ => (Work.Kernels.jFun γ (σ : ℂ)) ^ k) (γ⁻¹ • w) :=
    (UpperHalfPlane.mdifferentiable_denom_zpow (Work.Kernels.glOf γ) k).mdifferentiableAt
  have hPsi : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ)
      (PsiEven k f h₁ h₂ (MonoidAlgebra.of ℂ X γ)) (γ⁻¹ • w) :=
    (mdifferentiableOn_PsiEven hMpO hf hh₁ hh₂ (MonoidAlgebra.of ℂ X γ)).mdifferentiableAt
      (hOp.mem_nhds hw)
  unfold PsiEvenLoc
  exact ((hj.comp w hsmul.mdifferentiableAt).mul (hPsi.comp w hsmul.mdifferentiableAt))

/-- **Well-definedness of the extension formula.**  If the value `j(γ,τ)^k Ψ(γ,τ)` is independent
of the presentation `w = γ • τ` with `τ ∈ O_F` (this is the content of the paper's well-definedness
argument, `Work.Asymptotics.PsiEven_well_defined`), then `Feven` computes it for every
presentation. -/
lemma Feven_apply {O_F : Set ℍ} {k : ℤ} {f h₁ h₂ : ℍ → ℂ}
    (hwd : ∀ (γ γ' : SL(2,ℤ)) (τ τ' : ℍ), τ ∈ O_F → τ' ∈ O_F → γ • τ = γ' • τ' →
      Work.Kernels.jFun γ (τ : ℂ) ^ k * PsiEven k f h₁ h₂ (MonoidAlgebra.of ℂ X γ) τ
        = Work.Kernels.jFun γ' (τ' : ℂ) ^ k * PsiEven k f h₁ h₂ (MonoidAlgebra.of ℂ X γ') τ')
    {γ : SL(2,ℤ)} {τ : ℍ} (hτ : τ ∈ O_F) :
    Feven O_F k f h₁ h₂ (γ • τ)
      = Work.Kernels.jFun γ (τ : ℂ) ^ k * PsiEven k f h₁ h₂ (MonoidAlgebra.of ℂ X γ) τ := by
  classical
  have hex : ∃ p : SL(2,ℤ) × ℍ, p.2 ∈ O_F ∧ p.1 • p.2 = γ • τ := ⟨(γ, τ), hτ, rfl⟩
  have hspec := Classical.choose_spec hex
  unfold Feven
  rw [dif_pos hex]
  exact hwd _ _ _ _ hspec.1 hτ hspec.2

/-- **The extension agrees with `f` on `Mp i • O_F`.** -/
lemma Feven_Mp_eq {O_F O : Set ℍ} {k : ℤ} (hk : Even k) {f h₁ h₂ : ℍ → ℂ}
    (hwd : ∀ (γ γ' : SL(2,ℤ)) (τ τ' : ℍ), τ ∈ O_F → τ' ∈ O_F → γ • τ = γ' • τ' →
      Work.Kernels.jFun γ (τ : ℂ) ^ k * PsiEven k f h₁ h₂ (MonoidAlgebra.of ℂ X γ) τ
        = Work.Kernels.jFun γ' (τ' : ℂ) ^ k * PsiEven k f h₁ h₂ (MonoidAlgebra.of ℂ X γ') τ')
    (i : Fin 6) {τ : ℍ} (hτ : τ ∈ O_F) :
    Feven O_F k f h₁ h₂ ((Mp i) • τ) = f ((Mp i) • τ) := by
  rw [Feven_apply hwd hτ, PsiEven_Mp_eq hk i τ, slash_MpR_even, Work.Kernels.slash_apply']
  have hne : (Work.Kernels.jFun (Mp i) (τ : ℂ)) ^ k ≠ 0 :=
    zpow_ne_zero _ (Work.Kernels.jFun_ne_zero (Mp i) τ)
  rw [show (Work.Kernels.jFun (Mp i) (τ : ℂ)) ^ (-k)
      = ((Work.Kernels.jFun (Mp i) (τ : ℂ)) ^ k)⁻¹ from zpow_neg _ _]
  rw [← mul_assoc, mul_comm (Work.Kernels.jFun (Mp i) (τ : ℂ) ^ k), mul_inv_cancel_right₀ hne]

/-- **`Feven` is holomorphic**, given the well-definedness of the formula. -/
lemma mdifferentiable_Feven {O O_F : Set ℍ} {k : ℤ} {f h₁ h₂ : ℍ → ℂ}
    (hOp : IsOpen O_F) (hFF : closure DomainF ⊆ O_F)
    (hMpO : ∀ i : Fin 6, ∀ τ ∈ O_F, (Mp i) • τ ∈ O)
    (hf : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) f O) (hh₁ : MDiff h₁) (hh₂ : MDiff h₂)
    (hwd : ∀ (γ γ' : SL(2,ℤ)) (τ τ' : ℍ), τ ∈ O_F → τ' ∈ O_F → γ • τ = γ' • τ' →
      Work.Kernels.jFun γ (τ : ℂ) ^ k * PsiEven k f h₁ h₂ (MonoidAlgebra.of ℂ X γ) τ
        = Work.Kernels.jFun γ' (τ' : ℂ) ^ k * PsiEven k f h₁ h₂ (MonoidAlgebra.of ℂ X γ') τ') :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (Feven O_F k f h₁ h₂) := by
  intro w
  obtain ⟨γ, hγ⟩ := exists_inv_smul_mem_even hFF w
  have hmem : w ∈ (fun τ : ℍ => γ • τ) '' O_F := by
    refine ⟨γ⁻¹ • w, hγ, ?_⟩
    show γ • (γ⁻¹ • w) = w
    rw [smul_inv_smul]
  have hopen := isOpen_smul_image_even hOp γ
  have hev : Feven O_F k f h₁ h₂ =ᶠ[𝓝 w] PsiEvenLoc k f h₁ h₂ γ := by
    filter_upwards [hopen.mem_nhds hmem] with x hx
    obtain ⟨σ, hσ, rfl⟩ := hx
    have h1 := Feven_apply (γ := γ) hwd hσ
    have h2 : PsiEvenLoc k f h₁ h₂ γ (γ • σ)
        = Work.Kernels.jFun γ (σ : ℂ) ^ k * PsiEven k f h₁ h₂ (MonoidAlgebra.of ℂ X γ) σ := by
      have hσ' : γ⁻¹ • (γ • σ) = σ := inv_smul_smul γ σ
      simp only [PsiEvenLoc, hσ']
    rw [h2]
    exact h1
  exact (mdifferentiableAt_PsiEvenLoc hOp hMpO hf hh₁ hh₂ hγ).congr_of_eventuallyEq hev

end Work.Asymptotics
