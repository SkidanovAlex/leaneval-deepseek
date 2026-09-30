import Mathlib
import Submission.Work.Kunneth.EzawAux

/-!
# The boundary identity for the level defect `EmS`

`EmS p q N h = (Ezaw - 1)(Ugen p q N h)` is the defect of the composite `ezMap ≫ awMap` on the
`(p,q)`-model placed in degree `N`.  This file computes its differential:
`d (EmS p q (N+1) h) = Σ_i (-1)^i φ_i (EmS (p-1) q N _) + (-1)^p Σ_j (-1)^j ψ_j (EmS p (q-1) N _)`,
in the three non-vacuous cases (the case `(0,0)` is `Em 0 0 = 0`).
-/

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits HomologicalComplex AlgebraicTopology
open scoped MonoidalCategory TensorProduct Simplicial

namespace Work.Kunneth

noncomputable section

attribute [-instance] AddCommGroup.toIntModule

/-! ## 1. Elementary manipulations with sums of tensors -/

/-- Distributing a finite sum through the left factor of an elementary tensor. -/
lemma finset_sum_tmul_conc (C D : ChainComplex (ModuleCat ℤ) ℕ) (p q : ℕ) (ι : Type*)
    (s : Finset ι) (z : ι → ↥(C.X p)) (n : ↥(D.X q)) :
    (∑ i ∈ s, z i) ⊗ₜ[ℤ] n = ∑ i ∈ s, z i ⊗ₜ[ℤ] n := by
  classical
  induction s using Finset.induction with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, TensorProduct.zero_tmul]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, TensorProduct.add_tmul, ih]

/-- Distributing a finite sum of scalars through the left factor of an elementary tensor. -/
lemma finset_sum_smul_tmul_conc (C D : ChainComplex (ModuleCat ℤ) ℕ) (p q : ℕ) (ι : Type*)
    (s : Finset ι) (c : ι → ℤ) (z : ι → ↥(C.X p)) (n : ↥(D.X q)) :
    (∑ i ∈ s, c i • z i) ⊗ₜ[ℤ] n = ∑ i ∈ s, c i • (z i ⊗ₜ[ℤ] n) := by
  classical
  induction s using Finset.induction with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, TensorProduct.zero_tmul]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, TensorProduct.add_tmul, ih]
      rfl

/-- Distributing a finite sum through the right factor of an elementary tensor. -/
lemma finset_tmul_sum_conc (C D : ChainComplex (ModuleCat ℤ) ℕ) (p q : ℕ) (ι : Type*)
    (s : Finset ι) (m : ↥(C.X p)) (z : ι → ↥(D.X q)) :
    m ⊗ₜ[ℤ] (∑ i ∈ s, z i) = ∑ i ∈ s, m ⊗ₜ[ℤ] z i := by
  classical
  induction s using Finset.induction with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, TensorProduct.tmul_zero]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, TensorProduct.tmul_add, ih]

/-- Pulling a scalar out of the right factor of an elementary tensor. -/
lemma tmul_smul_conc (C D : ChainComplex (ModuleCat ℤ) ℕ) (p q : ℕ) (c : ℤ)
    (m : ↥(C.X p)) (n : ↥(D.X q)) :
    m ⊗ₜ[ℤ] (c • n) = c • (m ⊗ₜ[ℤ] n) :=
  map_zsmul (TensorProduct.mk ℤ ↥(C.X p) ↥(D.X q) m) c n

/-- The summand inclusion is additive. -/
lemma tpLof_sum_conc (C D : ChainComplex (ModuleCat ℤ) ℕ) (N p q : ℕ) (h : p + q = N)
    {ι : Type*} (s : Finset ι) (z : ι → tpSummand C D p q) :
    tpLof C D N ⟨(p, q), h⟩ (∑ i ∈ s, z i) = ∑ i ∈ s, tpLof C D N ⟨(p, q), h⟩ (z i) :=
  map_sum (tpLof C D N ⟨(p, q), h⟩) z s

/-- Distribution of a `ℤ`-scalar over a sum in a `ℤ`-module (instance-robust version). -/
lemma smul_add_mod {M : Type*} [AddCommGroup M] [Module ℤ M] (c : ℤ) (x y : M) :
    c • (x + y) = c • x + c • y :=
  map_add (c • (1 : M →ₗ[ℤ] M)) x y

/-! ## 2. The differential of `Ugen` -/

/-- The two-term expansion of the Koszul differential of a summand generator. -/
lemma tpD_lof_tmul'' (C D : ChainComplex (ModuleCat ℤ) ℕ) (N a b : ℕ) (hab : a + b = N + 1)
    (x : ↥(C.X a)) (y : ↥(D.X b)) :
    tpD C D N (tpLof C D (N + 1) ⟨(a, b), hab⟩ (x ⊗ₜ[ℤ] y))
      = (if hp : 1 ≤ a then
           tpLof C D N ⟨(a - 1, b), by omega⟩ (((C.d a (a - 1)).hom x) ⊗ₜ[ℤ] y)
         else 0)
        + (if hq : 1 ≤ b then
           (-1 : ℤ) ^ a • tpLof C D N ⟨(a, b - 1), by omega⟩ (x ⊗ₜ[ℤ] ((D.d b (b - 1)).hom y))
         else 0) := by
  rw [tpD_lof_tmul]

/-- The differential of the universal element, case `(p+1, q+1)`. -/
lemma tpD_Ugen_pp (p q N : ℕ) (h : (p + 1) + (q + 1) = N + 1)
    (h₁ : p + (q + 1) = N) (h₂ : (p + 1) + q = N) :
    tpD (sMod (p + 1)) (sMod (q + 1)) N (Ugen (p + 1) (q + 1) (N + 1) h)
      = tpLof (sMod (p + 1)) (sMod (q + 1)) N ⟨(p, q + 1), h₁⟩
          (((sMod (p + 1)).d (p + 1) p).hom (genCh (SdS (p + 1)) (univS (p + 1)))
            ⊗ₜ[ℤ] genCh (SdS (q + 1)) (univS (q + 1)))
        + (-1 : ℤ) ^ (p + 1) •
          tpLof (sMod (p + 1)) (sMod (q + 1)) N ⟨(p + 1, q), h₂⟩
            (genCh (SdS (p + 1)) (univS (p + 1))
              ⊗ₜ[ℤ] ((sMod (q + 1)).d (q + 1) q).hom (genCh (SdS (q + 1)) (univS (q + 1)))) := by
  rw [Ugen, tpD_lof_tmul'' (C := sMod (p + 1)) (D := sMod (q + 1)) (N := N) (a := p + 1)
    (b := q + 1) (hab := h)]
  rw [dif_pos (show (1 : ℕ) ≤ p + 1 by omega), dif_pos (show (1 : ℕ) ≤ q + 1 by omega)]
  rfl

/-- The differential of the universal element, case `(0, q+1)`. -/
lemma tpD_Ugen_zp (q N : ℕ) (h : 0 + (q + 1) = N + 1) (h₂ : 0 + q = N) :
    tpD (sMod 0) (sMod (q + 1)) N (Ugen 0 (q + 1) (N + 1) h)
      = tpLof (sMod 0) (sMod (q + 1)) N ⟨(0, q), h₂⟩
          (genCh (SdS 0) (univS 0)
            ⊗ₜ[ℤ] ((sMod (q + 1)).d (q + 1) q).hom (genCh (SdS (q + 1)) (univS (q + 1)))) := by
  rw [Ugen, tpD_lof_tmul'' (C := sMod 0) (D := sMod (q + 1)) (N := N) (a := 0) (b := q + 1)
    (hab := h)]
  rw [dif_neg (show ¬ (1 : ℕ) ≤ 0 by omega), dif_pos (show (1 : ℕ) ≤ q + 1 by omega),
    zero_add, pow_zero, one_zsmul]
  rfl

/-- The differential of the universal element, case `(p+1, 0)`. -/
lemma tpD_Ugen_pz (p N : ℕ) (h : (p + 1) + 0 = N + 1) (h₁ : p + 0 = N) :
    tpD (sMod (p + 1)) (sMod 0) N (Ugen (p + 1) 0 (N + 1) h)
      = tpLof (sMod (p + 1)) (sMod 0) N ⟨(p, 0), h₁⟩
          (((sMod (p + 1)).d (p + 1) p).hom (genCh (SdS (p + 1)) (univS (p + 1)))
            ⊗ₜ[ℤ] genCh (SdS 0) (univS 0)) := by
  rw [Ugen, tpD_lof_tmul'' (C := sMod (p + 1)) (D := sMod 0) (N := N) (a := p + 1) (b := 0)
    (hab := h)]
  rw [dif_pos (show (1 : ℕ) ≤ p + 1 by omega), dif_neg (show ¬ (1 : ℕ) ≤ 0 by omega), add_zero]
  rfl

/-! ## 3. The two parts of `d (Ugen)` in coface form -/

/-- The `d⊗1`-part of the differential of `Ugen`, in coface form. -/
lemma dg1_phi (p q N : ℕ) (h₁ : p + q = N) :
    tpLof (sMod (p + 1)) (sMod q) N ⟨(p, q), h₁⟩
        (((sMod (p + 1)).d (p + 1) p).hom (genCh (SdS (p + 1)) (univS (p + 1)))
          ⊗ₜ[ℤ] genCh (SdS q) (univS q))
      = (phiSum p q).f N (Ugen p q N h₁) := by
  rw [d_genCh (SdS (p + 1)) p (univS (p + 1)),
    finset_sum_smul_tmul_conc (sMod (p + 1)) (sMod q) p q (Fin (p + 2)) Finset.univ
      (fun i : Fin (p + 2) => (-1 : ℤ) ^ (i : ℕ))
      (fun i : Fin (p + 2) => genCh (SdS (p + 1)) ((SdS (p + 1)).δ i (univS (p + 1))))
      (genCh (SdS q) (univS q)),
    tpLof_sum_conc (sMod (p + 1)) (sMod q) N p q h₁ Finset.univ
      (fun i : Fin (p + 2) => (-1 : ℤ) ^ (i : ℕ) •
        ((genCh (SdS (p + 1)) ((SdS (p + 1)).δ i (univS (p + 1))))
          ⊗ₜ[ℤ] genCh (SdS q) (univS q)))]
  rw [phiSum_f_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [map_zsmul]
  congr 1
  rw [show tpLof (sMod (p + 1)) (sMod q) N ⟨(p, q), h₁⟩
      (genCh (SdS (p + 1)) ((SdS (p + 1)).δ i (univS (p + 1)))
        ⊗ₜ[ℤ] genCh (SdS q) (univS q))
      = tpLof (sMod (p + 1)) (sMod q) N ⟨(p, q), h₁⟩
      (genCh (SdS (p + 1)) ((SdS (p + 1)).map (SimplexCategory.δ i).op (univS (p + 1)))
        ⊗ₜ[ℤ] genCh (SdS q) (univS q)) from rfl]
  rw [← phiMod_Ugen p q N h₁ i]

/-- The `1⊗d`-part of the differential of `Ugen`, in coface form. -/
lemma dg2_psi (p q N : ℕ) (h₂ : p + q = N) :
    tpLof (sMod p) (sMod (q + 1)) N ⟨(p, q), h₂⟩
        (genCh (SdS p) (univS p)
          ⊗ₜ[ℤ] ((sMod (q + 1)).d (q + 1) q).hom (genCh (SdS (q + 1)) (univS (q + 1))))
      = (psiSum p q).f N (Ugen p q N h₂) := by
  rw [d_genCh (SdS (q + 1)) q (univS (q + 1)),
    finset_tmul_sum_conc (sMod p) (sMod (q + 1)) p q (Fin (q + 2)) Finset.univ
      (genCh (SdS p) (univS p))
      (fun i : Fin (q + 2) => (-1 : ℤ) ^ (i : ℕ) •
        genCh (SdS (q + 1)) ((SdS (q + 1)).δ i (univS (q + 1)))),
    tpLof_sum_conc (sMod p) (sMod (q + 1)) N p q h₂ Finset.univ
      (fun i : Fin (q + 2) =>
        (genCh (SdS p) (univS p)
          ⊗ₜ[ℤ] ((-1 : ℤ) ^ (i : ℕ) •
            genCh (SdS (q + 1)) ((SdS (q + 1)).δ i (univS (q + 1))))))]
  rw [psiSum_f_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [show (genCh (SdS p) (univS p)
        ⊗ₜ[ℤ] ((-1 : ℤ) ^ (i : ℕ) • genCh (SdS (q + 1)) ((SdS (q + 1)).δ i (univS (q + 1)))))
      = (-1 : ℤ) ^ (i : ℕ) • (genCh (SdS p) (univS p)
          ⊗ₜ[ℤ] genCh (SdS (q + 1)) ((SdS (q + 1)).δ i (univS (q + 1)))) from
    tmul_smul_conc (sMod p) (sMod (q + 1)) p q _ _ _]
  rw [map_zsmul]
  congr 1
  rw [show tpLof (sMod p) (sMod (q + 1)) N ⟨(p, q), h₂⟩
      (genCh (SdS p) (univS p)
        ⊗ₜ[ℤ] genCh (SdS (q + 1)) ((SdS (q + 1)).δ i (univS (q + 1))))
      = tpLof (sMod p) (sMod (q + 1)) N ⟨(p, q), h₂⟩
      (genCh (SdS p) (univS p)
        ⊗ₜ[ℤ] genCh (SdS (q + 1)) ((SdS (q + 1)).map (SimplexCategory.δ i).op
          (univS (q + 1)))) from rfl]
  rw [← psiMod_Ugen p q N h₂ i]

/-! ## 4. Naturality of `Ezaw` with respect to the coface sums -/

/-- `Ezaw` commutes with the first alternating coface sum. -/
lemma ezaw_phiSum (p q N : ℕ) (h : p + q = N) :
    ((Ezaw (SdS (p + 1)) (SdS q)).f N).hom ((phiSum p q).f N (Ugen p q N h))
      = (phiSum p q).f N (((Ezaw (SdS p) (SdS q)).f N).hom (Ugen p q N h)) := by
  rw [phiSum_f_apply p q N (Ugen p q N h),
    phiSum_f_apply p q N (((Ezaw (SdS p) (SdS q)).f N).hom (Ugen p q N h))]
  rw [map_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [map_zsmul]
  congr 1
  exact ezaw_ind_nat_apply (SSet.stdSimplex.map (SimplexCategory.δ i)) (𝟙 (SdS q)) N (Ugen p q N h)

/-- `Ezaw` commutes with the second alternating coface sum. -/
lemma ezaw_psiSum (p q N : ℕ) (h : p + q = N) :
    ((Ezaw (SdS p) (SdS (q + 1))).f N).hom ((psiSum p q).f N (Ugen p q N h))
      = (psiSum p q).f N (((Ezaw (SdS p) (SdS q)).f N).hom (Ugen p q N h)) := by
  rw [psiSum_f_apply p q N (Ugen p q N h),
    psiSum_f_apply p q N (((Ezaw (SdS p) (SdS q)).f N).hom (Ugen p q N h))]
  rw [map_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [map_zsmul]
  congr 1
  exact ezaw_ind_nat_apply (𝟙 (SdS p)) (SSet.stdSimplex.map (SimplexCategory.δ i)) N (Ugen p q N h)

/-- The differential of the level defect is the difference of the two `Ezaw` terms. -/
lemma d_EmS (p q N : ℕ) (h : p + q = N + 1) :
    (tMod p q).d (N + 1) N (EmS p q (N + 1) h)
      = ((Ezaw (SdS p) (SdS q)).f N).hom ((tMod p q).d (N + 1) N (Ugen p q (N + 1) h))
        - (tMod p q).d (N + 1) N (Ugen p q (N + 1) h) := by
  have h1 : ((Ezaw (SdS p) (SdS q)).f N).hom ((tMod p q).d (N + 1) N (Ugen p q (N + 1) h))
      = (tMod p q).d (N + 1) N
          (((Ezaw (SdS p) (SdS q)).f (N + 1)).hom (Ugen p q (N + 1) h)) := by
    change (ModuleCat.Hom.hom ((Ezaw (SdS p) (SdS q)).f N))
        ((ModuleCat.Hom.hom ((tpC (sChain (SdS p)) (sChain (SdS q))).d (N + 1) N))
          (Ugen p q (N + 1) h))
      = (ModuleCat.Hom.hom ((tpC (sChain (SdS p)) (sChain (SdS q))).d (N + 1) N))
        ((ModuleCat.Hom.hom ((Ezaw (SdS p) (SdS q)).f (N + 1))) (Ugen p q (N + 1) h))
    simpa only [tChain] using
      (Hom_comm_apply (Ezaw (SdS p) (SdS q)) (N + 1) N (Ugen p q (N + 1) h)).symm
  rw [EmS, map_sub, ← h1]

/-! ## 5. The boundary identity -/

/-- **The Em-boundary identity, case `(p+1, q+1)`.** -/
theorem ezaw_boundary_pp (p q N : ℕ) (h : (p + 1) + (q + 1) = N + 1)
    (h₁ : p + (q + 1) = N) (h₂ : (p + 1) + q = N) :
    (tMod (p + 1) (q + 1)).d (N + 1) N (EmS (p + 1) (q + 1) (N + 1) h)
      = (phiSum p (q + 1)).f N (EmS p (q + 1) N h₁)
        + (-1 : ℤ) ^ (p + 1) • (psiSum (p + 1) q).f N (EmS (p + 1) q N h₂) := by
  have hU : (tMod (p + 1) (q + 1)).d (N + 1) N (Ugen (p + 1) (q + 1) (N + 1) h)
      = (phiSum p (q + 1)).f N (Ugen p (q + 1) N h₁)
        + (-1 : ℤ) ^ (p + 1) • (psiSum (p + 1) q).f N (Ugen (p + 1) q N h₂) := by
    rw [d_Ugen (p + 1) (q + 1) N h, tpD_Ugen_pp p q N h h₁ h₂, dg1_phi p (q + 1) N h₁,
      dg2_psi (p + 1) q N h₂]
  have hA : (phiSum p (q + 1)).f N (((Ezaw (SdS p) (SdS (q + 1))).f N).hom (Ugen p (q + 1) N h₁))
      = (phiSum p (q + 1)).f N (EmS p (q + 1) N h₁)
        + (phiSum p (q + 1)).f N (Ugen p (q + 1) N h₁) := by
    rw [show ((Ezaw (SdS p) (SdS (q + 1))).f N).hom (Ugen p (q + 1) N h₁)
        = EmS p (q + 1) N h₁ + Ugen p (q + 1) N h₁ from by rw [EmS, sub_add_cancel]]
    rw [map_add]
  have hB : (psiSum (p + 1) q).f N
        (((Ezaw (SdS (p + 1)) (SdS q)).f N).hom (Ugen (p + 1) q N h₂))
      = (psiSum (p + 1) q).f N (EmS (p + 1) q N h₂)
        + (psiSum (p + 1) q).f N (Ugen (p + 1) q N h₂) := by
    rw [show ((Ezaw (SdS (p + 1)) (SdS q)).f N).hom (Ugen (p + 1) q N h₂)
        = EmS (p + 1) q N h₂ + Ugen (p + 1) q N h₂ from by rw [EmS, sub_add_cancel]]
    rw [map_add]
  rw [d_EmS (p + 1) (q + 1) N h, hU, map_add, map_zsmul,
    ezaw_phiSum p (q + 1) N h₁, ezaw_psiSum (p + 1) q N h₂, hA, hB, smul_add_mod]
  abel

/-- **The Em-boundary identity, case `(0, q+1)`.** -/
theorem ezaw_boundary_zp (q N : ℕ) (h : 0 + (q + 1) = N + 1) (h₂ : 0 + q = N) :
    (tMod 0 (q + 1)).d (N + 1) N (EmS 0 (q + 1) (N + 1) h)
      = (psiSum 0 q).f N (EmS 0 q N h₂) := by
  have hU : (tMod 0 (q + 1)).d (N + 1) N (Ugen 0 (q + 1) (N + 1) h)
      = (psiSum 0 q).f N (Ugen 0 q N h₂) := by
    rw [d_Ugen 0 (q + 1) N h, tpD_Ugen_zp q N h h₂, dg2_psi 0 q N h₂]
  have hB : (psiSum 0 q).f N (((Ezaw (SdS 0) (SdS q)).f N).hom (Ugen 0 q N h₂))
      = (psiSum 0 q).f N (EmS 0 q N h₂) + (psiSum 0 q).f N (Ugen 0 q N h₂) := by
    rw [show ((Ezaw (SdS 0) (SdS q)).f N).hom (Ugen 0 q N h₂)
        = EmS 0 q N h₂ + Ugen 0 q N h₂ from by rw [EmS, sub_add_cancel]]
    rw [map_add]
  rw [d_EmS 0 (q + 1) N h, hU, ezaw_psiSum 0 q N h₂, hB]
  abel

/-- **The Em-boundary identity, case `(p+1, 0)`.** -/
theorem ezaw_boundary_pz (p N : ℕ) (h : (p + 1) + 0 = N + 1) (h₁ : p + 0 = N) :
    (tMod (p + 1) 0).d (N + 1) N (EmS (p + 1) 0 (N + 1) h)
      = (phiSum p 0).f N (EmS p 0 N h₁) := by
  have hU : (tMod (p + 1) 0).d (N + 1) N (Ugen (p + 1) 0 (N + 1) h)
      = (phiSum p 0).f N (Ugen p 0 N h₁) := by
    rw [d_Ugen (p + 1) 0 N h, tpD_Ugen_pz p N h h₁, dg1_phi p 0 N h₁]
  have hA : (phiSum p 0).f N (((Ezaw (SdS p) (SdS 0)).f N).hom (Ugen p 0 N h₁))
      = (phiSum p 0).f N (EmS p 0 N h₁) + (phiSum p 0).f N (Ugen p 0 N h₁) := by
    rw [show ((Ezaw (SdS p) (SdS 0)).f N).hom (Ugen p 0 N h₁)
        = EmS p 0 N h₁ + Ugen p 0 N h₁ from by rw [EmS, sub_add_cancel]]
    rw [map_add]
  rw [d_EmS (p + 1) 0 N h, hU, ezaw_phiSum p 0 N h₁, hA]
  abel


end

end Work.Kunneth
