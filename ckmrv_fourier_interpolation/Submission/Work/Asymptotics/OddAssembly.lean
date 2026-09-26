/-
# Analytic assembly for the odd-weight propagation (CKMRV Proposition 3.2(1))

This file contains the analytic part of the odd-weight case of CKMRV Proposition 3.2(1)
(`Work.Asymptotics.exists_extension_of_propagates_odd`): the automorphy cocycle for the factor
`j(γ,τ)`, the basic slash manipulations, and the explicit extension formula
`F(w) = j(γ,τ)^k · Ψ(γ,τ)` together with its well-definedness.

## Structure

Let `𝓕` be the standard fundamental domain and `O_F` the open neighbourhood of `closure 𝓕`
produced by `Work.Asymptotics.exists_neighbour_nbdh_of_Propagates`, so that

* `Mp i • O_F ⊆ O` for the six translates tiling `closure 𝒟`, and
* `γ • O_F ∩ O_F ≠ ∅` forces `γ ∈ NeighborsP`.

For `γ ∈ SL(2,ℤ)` and `τ ∈ O_F` define

  `Ψ γ τ = ∑_j σ(γ)_{0j} · (f |_k Mp_j)(τ) + (h₁ |_k A(γ)_0)(τ) + (h₂ |_k B(γ)_0)(τ)`,

with `A(γ)_0, B(γ)_0` the carries of `rowDiffOdd γ 0`.  Then every `w ∈ ℍ` can be written
`w = γ • τ` with `τ ∈ O_F`, and we set `F w = j(γ,τ)^k Ψ γ τ`.  The paper's well-definedness
argument uses (i) the multiplicativity of `σ`, (ii) the cocycle for the carries (which follows
from `Work.Asymptotics.idealI_direct_augIdealOdd`), and (iii) the "small extension claim" for
the neighbours (`Work.Asymptotics.small_decomp_neighbor_odd`).
-/
import Mathlib
import Submission.Work.Asymptotics.PropagateCarriesOdd
import Submission.Work.Asymptotics.exists_neighbour_nbdh_of_Propagates
import Submission.Work.Asymptotics.defects_of_local_agreement
import Submission.Work.Asymptotics.upperHalfPlane_subset_iUnion_smul_closure_DomainF
import Submission.Work.Asymptotics.OddCocycle
import Submission.Work.Asymptotics.sigmaHom_Mp_row0

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle Topology

namespace Work.Asymptotics

open Work.Kernels

/-- The action of `SL(2,ℤ)` on `ℍ` is continuous (the group is discrete). -/
instance : ContinuousSMul SL(2,ℤ) ℍ :=
  MulAction.continuousSMul_compHom (f := SpecialLinearGroup.mapGL ℝ)
    continuous_of_discreteTopology

/-! ## The automorphy cocycle `j(γδ,τ) = j(γ,δτ)·j(δ,τ)` -/

/-- **The cocycle identity for the automorphy factor.** -/
lemma jFun_mul (γ δ : SL(2,ℤ)) (τ : ℍ) :
    Work.Kernels.jFun (γ * δ) (τ : ℂ)
      = Work.Kernels.jFun γ ((δ • τ : ℍ) : ℂ) * Work.Kernels.jFun δ (τ : ℂ) := by
  have h := congrFun (SlashAction.slash_mul (-1 : ℤ) γ δ (1 : ℍ → ℂ)) τ
  rw [Work.Kernels.slash_apply', Work.Kernels.slash_apply', Work.Kernels.slash_apply'] at h
  simpa using h

/-! ## Basic slash manipulations -/

/-- The slash by the group-algebra element `ofSL γ` is the slash by `γ`. -/
lemma slash_ofSL (k : ℤ) (γ : SL(2,ℤ)) (F : ℍ → ℂ) :
    slash k (ofSL γ) F = F ∣[k] γ := by
  rw [show ofSL γ = MonoidAlgebra.single γ (1 : ℂ) from rfl, Work.Kernels.slash_single]
  exact one_smul ℂ _

/-- **Every element of `(1+z)R` kills every function at odd weight.** -/
lemma slash_eq_zero_of_mem_augIdealOdd (k : ℤ) (hk : Odd k) {r : R} (hr : r ∈ augIdealOdd)
    (F : ℍ → ℂ) : slash k r F = 0 := by
  induction hr using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, b, rfl⟩ := hx
    rw [Work.Kernels.AlgebraFacts.slash_mul, Work.Kernels.AlgebraFacts.slash_mul,
      slash_one_add_Rneg k hk]
    exact Work.Kernels.AlgebraFacts.slash_mul_aux_zero k b
  | zero => exact Work.Kernels.slash_zero k F
  | add x y hx hy ihx ihy => rw [Work.Kernels.slash_add, ihx, ihy, add_zero]
  | smul c x hx ih => rw [Work.Kernels.AlgebraFacts.slash_smul, ih, smul_zero]

/-! ## Slash preserves holomorphy -/

/-- The weight-`k` group-algebra slash of a holomorphic function is holomorphic. -/
lemma mdifferentiable_slash {F : ℍ → ℂ} (hF : MDiff F) (k : ℤ) (r : R) :
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


/-! ## The geometry of `O_F` -/

/-- Every point of `ℍ` is carried into `O_F` by some `SL(2,ℤ)`-translate. -/
lemma exists_inv_smul_mem {O_F : Set ℍ} (hFF : closure DomainF ⊆ O_F) (w : ℍ) :
    ∃ γ : SL(2,ℤ), γ⁻¹ • w ∈ O_F := by
  have hw : w ∈ ⋃ γ : SL(2,ℤ), (fun τ : ℍ => γ • τ) '' closure DomainF :=
    upperHalfPlane_subset_iUnion_smul_closure_DomainF (Set.mem_univ w)
  rw [Set.mem_iUnion] at hw
  obtain ⟨γ, hγ⟩ := hw
  rw [Set.mem_image] at hγ
  obtain ⟨x, hx, rfl⟩ := hγ
  exact ⟨γ, by rw [inv_smul_smul]; exact hFF hx⟩

/-- The open set `⋃ i, (Mp i) • O_F` covers `closure 𝒟`. -/
lemma closure_DomainD_subset_iUnion_Mp_smul {O_F : Set ℍ} (hFF : closure DomainF ⊆ O_F) :
    closure DomainD ⊆ ⋃ i : Fin 6, (fun τ : ℍ => (Mp i) • τ) '' O_F :=
  closure_DomainD_subset_iUnion_Mp.trans (Set.iUnion_mono fun i => Set.image_mono hFF)

/-- The set `⋃ i, (Mp i) • O_F` is contained in any open set containing the six closed translates
`Mp i • closure 𝓕`. -/
lemma iUnion_Mp_smul_subset {O O_F : Set ℍ} (hMpO : ∀ i : Fin 6, ∀ τ ∈ O_F, (Mp i) • τ ∈ O) :
    (⋃ i : Fin 6, (fun τ : ℍ => (Mp i) • τ) '' O_F) ⊆ O := by
  intro w hw
  rw [Set.mem_iUnion] at hw
  obtain ⟨i, τ, hτ, rfl⟩ := hw
  exact hMpO i τ hτ

/-- `⋃ i, (Mp i) • O_F` is open. -/
lemma isOpen_iUnion_Mp_smul {O_F : Set ℍ} (hOp : IsOpen O_F) :
    IsOpen (⋃ i : Fin 6, (fun τ : ℍ => (Mp i) • τ) '' O_F) := by
  refine isOpen_iUnion fun i => ?_
  have hset : (fun τ : ℍ => (Mp i) • τ) '' O_F = (fun τ : ℍ => (Mp i)⁻¹ • τ) ⁻¹' O_F := by
    ext w
    constructor
    · rintro ⟨τ, hτ, rfl⟩
      show (Mp i)⁻¹ • (Mp i • τ) ∈ O_F
      rwa [inv_smul_smul]
    · intro hw
      refine ⟨(Mp i)⁻¹ • w, hw, ?_⟩
      show (Mp i) • ((Mp i)⁻¹ • w) = w
      rw [smul_inv_smul]
  rw [hset]
  exact hOp.preimage (continuous_const_smul (Mp i)⁻¹)

/-! ## Slashes of functions holomorphic on a set -/

/-- If `r - r' ∈ (1+z)R` then `r` and `r'` act in the same way on every function at odd weight. -/
lemma slash_eq_of_sub_mem_augIdealOdd (k : ℤ) (hk : Odd k) {r r' : R}
    (h : r - r' ∈ augIdealOdd) (F : ℍ → ℂ) : slash k r F = slash k r' F := by
  have h0 : slash k (r - r') F = 0 := slash_eq_zero_of_mem_augIdealOdd k hk h F
  have hsub : slash k (r - r') F = slash k r F - slash k r' F := by
    rw [sub_eq_add_neg, show (-r' : R) = (-1 : ℂ) • r' from (neg_one_smul ℂ r').symm,
      Work.Kernels.slash_add, Work.Kernels.AlgebraFacts.slash_smul]
    simp [sub_eq_add_neg]
  rw [hsub] at h0
  exact sub_eq_zero.mp h0

/-- The slash by `γ` of a function holomorphic on `O` is holomorphic on `O_F`, provided
`γ • O_F ⊆ O`. -/
lemma mdifferentiableOn_slash_of_mapsTo {O O_F : Set ℍ} {γ : SL(2,ℤ)} {f : ℍ → ℂ}
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

/-! ## Holomorphy of the expansion -/

/-! ## The extension formula -/

/-- The CKMRV expansion of `j(γ,τ)^{-k}F(γ • τ)`: the six basis slashes `f|Mp_j` with the
coefficients from row `0` of the odd-weight representation `σ`, plus the two defect functions
`h₁`, `h₂` slashed by the carries of `rowDiffOdd γ 0`. -/
noncomputable def Psi (k : ℤ) (f h₁ h₂ : ℍ → ℂ) (γ : SL(2,ℤ)) (τ : ℍ) : ℂ :=
  (∑ j : Fin 6, (sigmaHom γ) 0 j • (slash k (MpElem j) f) τ)
    + (slash k (carryOdd₁ γ 0) h₁) τ + (slash k (carryOdd₂ γ 0) h₂) τ

/-- `Ψ(γ,·)` is holomorphic on `O_F` whenever the six translates `Mp i • O_F` land in `O` and the
two defect functions are holomorphic. -/
lemma mdifferentiableOn_Psi {O O_F : Set ℍ} {k : ℤ} {f h₁ h₂ : ℍ → ℂ}
    (hMpO : ∀ i : Fin 6, ∀ τ ∈ O_F, (Mp i) • τ ∈ O)
    (hf : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) f O) (hh₁ : MDiff h₁) (hh₂ : MDiff h₂) (γ : SL(2,ℤ)) :
    MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) (Psi k f h₁ h₂ γ) O_F := by
  have hterm : ∀ j : Fin 6, MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ)
      (fun τ : ℍ => (sigmaHom γ) 0 j • (slash k (MpElem j) f) τ) O_F := by
    intro j
    refine MDifferentiableOn.const_smul _ ?_
    have h := mdifferentiableOn_slash_of_mapsTo (O := O) (O_F := O_F) (γ := Mp j)
      (fun τ hτ => hMpO j τ hτ) hf k
    simpa only [slash_ofSL, show MpElem j = ofSL (Mp j) from rfl] using h
  unfold Psi
  have hsum : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ)
      (fun τ : ℍ => ∑ j : Fin 6, (sigmaHom γ) 0 j • (slash k (MpElem j) f) τ) O_F :=
    MDifferentiableOn.sum (s := O_F) (t := Finset.univ)
      (f := fun j : Fin 6 => fun τ : ℍ => (sigmaHom γ) 0 j • (slash k (MpElem j) f) τ)
      (fun j _ => hterm j)
  exact ((hsum.add
    (mdifferentiable_slash hh₁ k (carryOdd₁ γ 0)).mdifferentiableOn).add
    (mdifferentiable_slash hh₂ k (carryOdd₂ γ 0)).mdifferentiableOn)

/-- **The extension of `f` to `ℍ`.**  For `w ∈ ℍ`, choose `γ ∈ SL(2,ℤ)` and `τ ∈ O_F` with
`w = γ • τ` and set `F w = j(γ,τ)^k Ψ(γ,τ)`.  The value does not depend on the choice (see
`Fodd_apply`, which uses the well-definedness hypothesis). -/
noncomputable def Fodd (O_F : Set ℍ) (k : ℤ) (f h₁ h₂ : ℍ → ℂ) (w : ℍ) : ℂ := by
  classical
  exact if h : ∃ p : SL(2,ℤ) × ℍ, p.2 ∈ O_F ∧ p.1 • p.2 = w then
    Work.Kernels.jFun (Classical.choose h).1 ((Classical.choose h).2 : ℂ) ^ k
      * Psi k f h₁ h₂ (Classical.choose h).1 (Classical.choose h).2
  else 0

/-- The local expression for the extension on the `γ`-translate of `O_F`:
`w ↦ j(γ, γ⁻¹w)^k Ψ(γ, γ⁻¹w)`. -/
noncomputable def PsiLoc (k : ℤ) (f h₁ h₂ : ℍ → ℂ) (γ : SL(2,ℤ)) (w : ℍ) : ℂ :=
  Work.Kernels.jFun γ ((γ⁻¹ • w : ℍ) : ℂ) ^ k * Psi k f h₁ h₂ γ (γ⁻¹ • w)

/-- The translate `γ • O_F` of an open set is open. -/
lemma isOpen_smul_image {O_F : Set ℍ} (hOp : IsOpen O_F) (γ : SL(2,ℤ)) :
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

/-- The local expression `PsiLoc γ` is holomorphic on `γ • O_F`. -/
lemma mdifferentiableAt_PsiLoc {O O_F : Set ℍ} {k : ℤ} {f h₁ h₂ : ℍ → ℂ}
    (hOp : IsOpen O_F) (hMpO : ∀ i : Fin 6, ∀ τ ∈ O_F, (Mp i) • τ ∈ O)
    (hf : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) f O) (hh₁ : MDiff h₁) (hh₂ : MDiff h₂)
    {γ : SL(2,ℤ)} {w : ℍ} (hw : γ⁻¹ • w ∈ O_F) :
    MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (PsiLoc k f h₁ h₂ γ) w := by
  have hdet : 0 < (Work.Kernels.glOf γ⁻¹).det.val := by
    simp [Work.Kernels.glOf, Matrix.SpecialLinearGroup.coeToGL_det]
  have hsmul : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun x : ℍ => γ⁻¹ • x) :=
    UpperHalfPlane.mdifferentiable_smul hdet
  have hj : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ)
      (fun σ : ℍ => (Work.Kernels.jFun γ (σ : ℂ)) ^ k) (γ⁻¹ • w) :=
    (UpperHalfPlane.mdifferentiable_denom_zpow (Work.Kernels.glOf γ) k).mdifferentiableAt
  have hPsi : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (Psi k f h₁ h₂ γ) (γ⁻¹ • w) :=
    (mdifferentiableOn_Psi hMpO hf hh₁ hh₂ γ).mdifferentiableAt (hOp.mem_nhds hw)
  unfold PsiLoc
  exact ((hj.comp w hsmul.mdifferentiableAt).mul (hPsi.comp w hsmul.mdifferentiableAt))

/-- **Well-definedness of the extension formula.**  If the value `j(γ,τ)^k Ψ(γ,τ)` is independent
of the presentation `w = γ • τ` with `τ ∈ O_F` (this is the content of the paper's well-definedness
argument), then `Fodd` computes it for every presentation. -/
lemma Fodd_apply {O_F : Set ℍ} {k : ℤ} {f h₁ h₂ : ℍ → ℂ}
    (hwd : ∀ (γ γ' : SL(2,ℤ)) (τ τ' : ℍ), τ ∈ O_F → τ' ∈ O_F → γ • τ = γ' • τ' →
      Work.Kernels.jFun γ (τ : ℂ) ^ k * Psi k f h₁ h₂ γ τ
        = Work.Kernels.jFun γ' (τ' : ℂ) ^ k * Psi k f h₁ h₂ γ' τ')
    {γ : SL(2,ℤ)} {τ : ℍ} (hτ : τ ∈ O_F) :
    Fodd O_F k f h₁ h₂ (γ • τ)
      = Work.Kernels.jFun γ (τ : ℂ) ^ k * Psi k f h₁ h₂ γ τ := by
  classical
  have hex : ∃ p : SL(2,ℤ) × ℍ, p.2 ∈ O_F ∧ p.1 • p.2 = γ • τ := ⟨(γ, τ), hτ, rfl⟩
  have hspec := Classical.choose_spec hex
  unfold Fodd
  rw [dif_pos hex]
  exact hwd _ _ _ _ hspec.1 hτ hspec.2

/-! ## The values at the six translates `Mp i` -/

/-- The error vector of the reduction of `Mp i` itself vanishes, because row `0` of `σ(Mp i)` is
the `i`-th standard basis vector. -/
lemma rowDiffOdd_of_Mp (i : Fin 6) : rowDiffOdd (Mp i) 0 = 0 := by
  rw [rowDiffOdd, MpElem_zero, one_mul,
    Finset.sum_eq_single i
      (fun j _ hj => by rw [sigmaHom_Mp_row0, if_neg hj, zero_smul])
      (fun hi => absurd (Finset.mem_univ i) hi),
    sigmaHom_Mp_row0, if_pos rfl, one_smul]
  exact sub_eq_zero.mpr rfl

/-- The carries of `rowDiffOdd (Mp i) 0 = 0` lie in the collapse ideal, hence kill `h₁` and `h₂`. -/
lemma carryOdd_Mp_mem (i : Fin 6) :
    carryOdd₁ (Mp i) 0 ∈ augIdealOdd ∧ carryOdd₂ (Mp i) 0 ∈ augIdealOdd := by
  have h : (R_T - 1) ^ 2 * carryOdd₁ (Mp i) 0
      + R_S * (R_T - 1) ^ 2 * carryOdd₂ (Mp i) 0 ∈ augIdealOdd := by
    rw [carryOdd_pair (Mp i) 0, rowDiffOdd_of_Mp, zero_sub]
    exact Submodule.neg_mem _ (Submodule.subset_span ⟨1, carryOdd₃ (Mp i) 0, by rw [one_mul]⟩)
  exact idealI_direct_augIdealOdd h

/-- **The extension agrees with `f` on `Mp i • O_F`.** -/
lemma Fodd_Mp_eq {O_F O : Set ℍ} {k : ℤ} (hk : Odd k) {f h₁ h₂ : ℍ → ℂ}
    (hwd : ∀ (γ γ' : SL(2,ℤ)) (τ τ' : ℍ), τ ∈ O_F → τ' ∈ O_F → γ • τ = γ' • τ' →
      Work.Kernels.jFun γ (τ : ℂ) ^ k * Psi k f h₁ h₂ γ τ
        = Work.Kernels.jFun γ' (τ' : ℂ) ^ k * Psi k f h₁ h₂ γ' τ')
    (i : Fin 6) {τ : ℍ} (hτ : τ ∈ O_F) :
    Fodd O_F k f h₁ h₂ ((Mp i) • τ) = f ((Mp i) • τ) := by
  rw [Fodd_apply hwd hτ]
  have hsum : (∑ j : Fin 6, (sigmaHom (Mp i)) 0 j • (slash k (MpElem j) f) τ)
      = (slash k (MpElem i) f) τ := by
    rw [Finset.sum_eq_single i
      (fun j _ hj => by rw [sigmaHom_Mp_row0, if_neg hj, zero_smul])
      (fun hi => absurd (Finset.mem_univ i) hi), sigmaHom_Mp_row0, if_pos rfl, one_smul]
  have hA : (slash k (carryOdd₁ (Mp i) 0) h₁) τ = 0 := by
    rw [slash_eq_zero_of_mem_augIdealOdd k hk (carryOdd_Mp_mem i).1 h₁]
    rfl
  have hB : (slash k (carryOdd₂ (Mp i) 0) h₂) τ = 0 := by
    rw [slash_eq_zero_of_mem_augIdealOdd k hk (carryOdd_Mp_mem i).2 h₂]
    rfl
  unfold Psi
  rw [hsum, hA, hB, add_zero, add_zero, show MpElem i = ofSL (Mp i) from rfl, slash_ofSL,
    Work.Kernels.slash_apply']
  have hne : (Work.Kernels.jFun (Mp i) (τ : ℂ)) ^ k ≠ 0 :=
    zpow_ne_zero _ (Work.Kernels.jFun_ne_zero (Mp i) τ)
  rw [show (Work.Kernels.jFun (Mp i) (τ : ℂ)) ^ (-k)
      = ((Work.Kernels.jFun (Mp i) (τ : ℂ)) ^ k)⁻¹ from zpow_neg _ _]
  rw [← mul_assoc, mul_comm (Work.Kernels.jFun (Mp i) (τ : ℂ) ^ k), mul_inv_cancel_right₀ hne]

/-! ## Holomorphy of the extension -/

/-- **`Fodd` is holomorphic**, given the well-definedness of the formula. -/
lemma mdifferentiable_Fodd {O O_F : Set ℍ} {k : ℤ} {f h₁ h₂ : ℍ → ℂ}
    (hOp : IsOpen O_F) (hFF : closure DomainF ⊆ O_F)
    (hMpO : ∀ i : Fin 6, ∀ τ ∈ O_F, (Mp i) • τ ∈ O)
    (hf : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) f O) (hh₁ : MDiff h₁) (hh₂ : MDiff h₂)
    (hwd : ∀ (γ γ' : SL(2,ℤ)) (τ τ' : ℍ), τ ∈ O_F → τ' ∈ O_F → γ • τ = γ' • τ' →
      Work.Kernels.jFun γ (τ : ℂ) ^ k * Psi k f h₁ h₂ γ τ
        = Work.Kernels.jFun γ' (τ' : ℂ) ^ k * Psi k f h₁ h₂ γ' τ') :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (Fodd O_F k f h₁ h₂) := by
  intro w
  obtain ⟨γ, hγ⟩ := exists_inv_smul_mem hFF w
  have hmem : w ∈ (fun τ : ℍ => γ • τ) '' O_F := by
    refine ⟨γ⁻¹ • w, hγ, ?_⟩
    show γ • (γ⁻¹ • w) = w
    rw [smul_inv_smul]
  have hopen := isOpen_smul_image hOp γ
  have hev : Fodd O_F k f h₁ h₂ =ᶠ[𝓝 w] PsiLoc k f h₁ h₂ γ := by
    filter_upwards [hopen.mem_nhds hmem] with x hx
    obtain ⟨σ, hσ, rfl⟩ := hx
    have h1 := Fodd_apply (γ := γ) hwd hσ
    have h2 : PsiLoc k f h₁ h₂ γ (γ • σ)
        = Work.Kernels.jFun γ (σ : ℂ) ^ k * Psi k f h₁ h₂ γ σ := by
      have hσ' : γ⁻¹ • (γ • σ) = σ := inv_smul_smul γ σ
      simp only [PsiLoc, hσ']
    rw [h2]
    exact h1
  exact (mdifferentiableAt_PsiLoc hOp hMpO hf hh₁ hh₂ hγ).congr_of_eventuallyEq hev

end Work.Asymptotics
