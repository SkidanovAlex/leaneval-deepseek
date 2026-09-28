-- PORTED COPY (neutral island) of `Submission/Work/Serre/Surj/v0OfClassNeZero.lean`.
-- The only changes are: the imports of ratShuffle-island modules are redirected to the
-- copies in `Submission/Work/Serre/Neu/`, and the abbrev `singSSet` is renamed to
-- `singSSetN` (same body) so that this module can coexist with `Work.Serre.E0Defs`,
-- which declares the same name.  Declarations and proofs are unchanged.
import Mathlib
import Submission.Work.Serre.Neu.SurjSetup2
import Submission.Work.Serre.Surj.exists_d_eq_of_homologypi_eq_rat
import Submission.Work.ThomBordism.PontryaginThom.Torsion

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct

namespace Work.Serre.Surj

noncomputable section

/-! ## Rationalising cycles: technical lemmas

The target `Work.Serre.Surj.v0OfClassNeZero` compares the class of the rational relative cycle
`v0Of` (built from an integral lift `vtz` of an integral relative cycle `z`) with the class of the
rationalisation of `z`.  The bridge is the observation that the class of a cycle of `K` dies in the
homology of the base changed complex `K ⊗[ℤ] ℚ` exactly when it is a torsion class. -/

/-- `(a : ℚ) • (1 ⊗ m) = 1 ⊗ (a • m)` for an integer `a`. -/
private theorem rat_smul_one_tmul_aux {M : Type*} [AddCommGroup M] [Module ℤ M] (a : ℤ) (m : M) :
    (a : ℚ) • (TensorProduct.tmul ℤ (1 : ℚ) m) = TensorProduct.tmul ℤ (1 : ℚ) (a • m) := by
  rcases Int.eq_nat_or_neg a with ⟨n, h | h⟩
  · rw [h, Int.cast_natCast, Nat.cast_smul_eq_nsmul (R := ℚ) n (TensorProduct.tmul ℤ (1 : ℚ) m),
      ← TensorProduct.tmul_smul (R := ℤ) (R' := ℕ) n (1 : ℚ) m, natCast_zsmul]
  · rw [h, Int.cast_neg, Int.cast_natCast, neg_smul,
      Nat.cast_smul_eq_nsmul (R := ℚ) n (TensorProduct.tmul ℤ (1 : ℚ) m),
      ← TensorProduct.tmul_smul (R := ℤ) (R' := ℕ) n (1 : ℚ) m, ← TensorProduct.tmul_neg]
    congr 1
    rw [neg_zsmul, natCast_zsmul]

/-- **Clearing denominators.**  Every element of `ℚ ⊗[ℤ] M` is, after multiplication by a positive
integer, a pure tensor of the form `1 ⊗ m`. -/
private theorem exists_nat_smul_tmul_one_aux (M : Type*) [AddCommGroup M] [Module ℤ M]
    (z : ℚ ⊗[ℤ] M) :
    ∃ N : ℕ, 0 < N ∧ ∃ m : M, (N : ℚ) • z = TensorProduct.tmul ℤ (1 : ℚ) m := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨1, Nat.one_pos, 0, by simp⟩
  | tmul q m =>
      refine ⟨q.den, q.den_pos, q.num • m, ?_⟩
      have hden : (q.den : ℚ) ≠ 0 := by exact_mod_cast Rat.den_nz q
      have hq : (q.den : ℚ) * q = (q.num : ℚ) := by
        have h : (q.den : ℚ) * ((q.num : ℚ) / (q.den : ℚ)) = (q.num : ℚ) :=
          mul_div_cancel₀ _ hden
        rwa [Rat.num_div_den q] at h
      rw [TensorProduct.tmul_eq_smul_one_tmul q m, smul_smul, hq]
      exact rat_smul_one_tmul_aux q.num m
  | add z₁ z₂ h₁ h₂ =>
      obtain ⟨N₁, hN₁, m₁, h₁⟩ := h₁
      obtain ⟨N₂, hN₂, m₂, h₂⟩ := h₂
      refine ⟨N₁ * N₂, Nat.mul_pos hN₁ hN₂, N₂ • m₁ + N₁ • m₂, ?_⟩
      rw [Nat.cast_mul, mul_smul, smul_add, smul_add, smul_comm (N₁ : ℚ) (N₂ : ℚ) z₁, h₁, h₂]
      rw [Nat.cast_smul_eq_nsmul (R := ℚ) N₂, Nat.cast_smul_eq_nsmul (R := ℚ) N₁,
        ← TensorProduct.tmul_smul (R := ℤ) (R' := ℕ) N₂ (1 : ℚ) m₁,
        ← TensorProduct.tmul_smul (R := ℤ) (R' := ℕ) N₁ (1 : ℚ) m₂,
        ← TensorProduct.tmul_add]

/-- **A positive multiple kills a rationalised torsion element.**  If `u ⊗ 1 = 0` in `M ⊗[ℤ] ℚ`,
then `k • u = 0` for some positive integer `k`. -/
private theorem nsmul_eq_zero_of_tmul_eq_zero (K : ChainComplex (ModuleCat ℤ) ℕ) (n : ℕ)
    (u : ↥(K.X n)) (hu : TensorProduct.tmul ℤ u (1 : ℚ) = 0) :
    ∃ k : ℕ, 0 < k ∧ k • u = 0 := by
  have hu' := hu
  rw [show (K.X n).isModule = AddCommGroup.toIntModule ↥(K.X n) from
    Subsingleton.elim _ _] at hu'
  obtain ⟨k, hk, hk0⟩ := Work.ThomBordism.PontryaginThom.torsion_of_tmul_one_eq_zero u hu'
  exact ⟨k, hk, (natCast_zsmul u k).symm.trans hk0⟩

/-- **A torsion class dies after rationalisation.** -/
private theorem tmul_eq_zero_of_nsmul_eq_zero {M : Type*} [AddCommGroup M] [Module ℤ M] (h : M)
    {N : ℕ} (hN : 0 < N) (hh : N • h = 0) :
    TensorProduct.tmul ℤ h (1 : ℚ) = 0 := by
  have hNq : (N : ℚ) ≠ 0 := by exact_mod_cast hN.ne'
  have hq : (1 : ℚ) = N • ((1 : ℚ) / (N : ℚ)) := by
    rw [nsmul_eq_mul]; field_simp
  rw [hq, ← TensorProduct.smul_tmul (R := ℤ) N h ((1 : ℚ) / (N : ℚ)), hh,
    TensorProduct.zero_tmul]

/-- **A cycle whose rationalisation is a boundary is a torsion class.**  If the pure tensor
`1 ⊗ iCycles y` of the base changed complex `K ⊗[ℤ] ℚ` is a boundary, then the class of `y` in
`Hₙ(K)` is torsion. -/
private theorem torsion_of_d_eq_tmul_aux (K : ChainComplex (ModuleCat ℤ) ℕ) (n : ℕ)
    (y : ↥(K.cycles n)) (w : ↥((Work.StemsB.IntRatCM.obj K).X (n + 1)))
    (hw : (ModuleCat.Hom.hom ((Work.StemsB.IntRatCM.obj K).d (n + 1) n)) w
        = TensorProduct.tmul ℤ (1 : ℚ) ((ModuleCat.Hom.hom (K.iCycles n)) y)) :
    TensorProduct.tmul ℤ ((ModuleCat.Hom.hom (K.homologyπ n)) y) (1 : ℚ) = 0 := by
  obtain ⟨N, hN, M, hM⟩ := exists_nat_smul_tmul_one_aux ↥(K.X (n + 1)) w
  set a : ↥(K.X n) := (ModuleCat.Hom.hom (K.iCycles n)) y with ha
  set b : ↥(K.X n) := (ModuleCat.Hom.hom (K.d (n + 1) n)) M with hb
  -- `1 ⊗ (N • a) = 1 ⊗ b`
  have h3 : TensorProduct.tmul ℤ (1 : ℚ) (N • a) = TensorProduct.tmul ℤ (1 : ℚ) b := by
    rw [hb, ← IntRatCM_d_tmul K (n + 1) n M, ← hM, map_smul, hw,
      Nat.cast_smul_eq_nsmul (R := ℚ) N,
      ← TensorProduct.tmul_smul (R := ℤ) (R' := ℕ) N (1 : ℚ) a]
  set u : ↥(K.X n) := N • a - b with hu
  have h4 : TensorProduct.tmul ℤ (1 : ℚ) u = 0 := by
    rw [hu, TensorProduct.tmul_sub, h3, sub_self]
  have h5 : TensorProduct.tmul ℤ u (1 : ℚ) = 0 := by
    refine (TensorProduct.comm ℤ ↥(K.X n) ℚ).injective.eq_iff.mp ?_
    rw [map_zero, TensorProduct.comm_tmul]
    exact h4
  obtain ⟨k, hk, hk0⟩ := nsmul_eq_zero_of_tmul_eq_zero K n u h5
  -- `u` is a cycle
  have hda : (ModuleCat.Hom.hom (K.d n (n - 1))) a = 0 := by
    rw [ha]; exact Work.Kunneth.d_iCycles K n y
  have hdb : (ModuleCat.Hom.hom (K.d n (n - 1))) b = 0 := by
    rw [hb]
    have h := congrArg (fun (g : K.X (n + 1) ⟶ K.X (n - 1)) => (ModuleCat.Hom.hom g) M)
      (HomologicalComplex.d_comp_d K (n + 1) n (n - 1))
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
      LinearMap.zero_apply] using h
  have hdu : (ModuleCat.Hom.hom (K.d n (n - 1))) u = 0 := by
    rw [hu, map_sub, map_nsmul, hda, hdb]
    simp
  -- the cycle `u`
  have hmem : u ∈ Work.Kunneth.cycKer K n := by
    rw [Work.Kunneth.cycKer, LinearMap.mem_ker]
    exact hdu
  set cu : ↥(K.cycles n) := Work.Kunneth.cycleOf K n ⟨u, hmem⟩ with hcu
  have hicu : (ModuleCat.Hom.hom (K.iCycles n)) cu = u := by
    rw [hcu]; exact Work.Kunneth.iCycles_cycleOf K n ⟨u, hmem⟩
  have hto : (ModuleCat.Hom.hom (K.iCycles n)) (K.toCycles (n + 1) n M) = b := by
    rw [hb]
    have h := congrArg (fun (g : K.X (n + 1) ⟶ K.X n) => ModuleCat.Hom.hom g)
      (HomologicalComplex.toCycles_i K (n + 1) n)
    rw [ModuleCat.hom_comp] at h
    exact LinearMap.congr_fun h M
  -- `N • y = cu + toCycles M`
  have hNy : N • y = cu + K.toCycles (n + 1) n M := by
    apply (ModuleCat.mono_iff_injective (K.iCycles n)).mp inferInstance
    rw [map_nsmul, map_add, hicu, hto, hu, ← ha, sub_add_cancel]
  -- the class of `cu` is killed by `k`
  have hzero : k • cu = 0 := by
    apply (ModuleCat.mono_iff_injective (K.iCycles n)).mp inferInstance
    rw [map_nsmul, map_zero, hicu]
    exact hk0
  have hto0 : (ModuleCat.Hom.hom (K.homologyπ n)) (K.toCycles (n + 1) n M) = 0 := by
    have h := congrArg (fun (g : K.X (n + 1) ⟶ K.homology n) => (ModuleCat.Hom.hom g) M)
      (HomologicalComplex.toCycles_comp_homologyπ K (n + 1) n)
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
      LinearMap.zero_apply] using h
  have hfinal : (N * k) • (ModuleCat.Hom.hom (K.homologyπ n)) y = 0 := by
    have hcl : N • (ModuleCat.Hom.hom (K.homologyπ n)) y
        = (ModuleCat.Hom.hom (K.homologyπ n)) cu := by
      rw [← map_nsmul, hNy, map_add, hto0, add_zero]
    rw [mul_nsmul, hcl, ← map_nsmul, hzero, map_zero]
  exact tmul_eq_zero_of_nsmul_eq_zero _ (Nat.mul_pos hN hk) hfinal

end

theorem v0OfClassNeZero (P : Type) [TopologicalSpace P] (Q : Set P) (r : ℕ)
    (z : ↥((Work.Cohomology.relChains (TopCat.of P) Q).cycles (r + 1)))
    (vtz : ↥((Work.Cohomology.singularChains ℤ (TopCat.of P)).X (r + 1)))
    (hvtz : (ModuleCat.Hom.hom ((Work.Cohomology.relChainsProj (TopCat.of P) Q).f (r + 1))) vtz
      = (ModuleCat.Hom.hom ((Work.Cohomology.relChains (TopCat.of P) Q).iCycles (r + 1))) z)
    (hzt : TensorProduct.tmul ℤ ((ModuleCat.Hom.hom
        ((Work.Cohomology.relChains (TopCat.of P) Q).homologyπ (r + 1))) z) (1 : ℚ) ≠ 0) :
    (ModuleCat.Hom.hom ((Work.StemsB.relChainsR ℚ (TopCat.of P) Q).homologyπ (r + 1)))
      (Work.Serre.Surj.v0Of P Q r z vtz hvtz) ≠ 0 := by
  intro h0
  -- the underlying chain of `v0Of` is the base change of `1 ⊗ iCycles z`
  have hchain : (ModuleCat.Hom.hom ((Work.StemsB.relChainsR ℚ (TopCat.of P) Q).iCycles (r + 1)))
        (Work.Serre.Surj.v0Of P Q r z vtz hvtz)
      = (ModuleCat.Hom.hom ((bcRel (TopCat.of P) Q).hom.f (r + 1)))
          (TensorProduct.tmul ℤ (1 : ℚ) ((ModuleCat.Hom.hom
            ((Work.Cohomology.relChains (TopCat.of P) Q).iCycles (r + 1))) z)) := by
    unfold Work.Serre.Surj.v0Of Work.Serre.Surj.vt0Of
    rw [Work.Serre.Surj.iCycles_cycleOfQ]
    rw [← hvtz]
    exact (bcRel_value (TopCat.of P) Q (r + 1) vtz).symm
  -- if the class of `v0Of` vanishes, `1 ⊗ iCycles z` is a boundary
  obtain ⟨v, hv⟩ := exists_d_eq_of_homologypi_eq_rat
    (Work.StemsB.relChainsR ℚ (TopCat.of P) Q) (r + 1)
    (Work.Serre.Surj.v0Of P Q r z vtz hvtz) h0
  set W := (bcRel (TopCat.of P) Q).inv.f ((r + 1) + 1) v with hW
  have hinv : (ModuleCat.Hom.hom ((bcRel (TopCat.of P) Q).inv.f (r + 1)))
      ((ModuleCat.Hom.hom ((bcRel (TopCat.of P) Q).hom.f (r + 1)))
        (TensorProduct.tmul ℤ (1 : ℚ) ((ModuleCat.Hom.hom
          ((Work.Cohomology.relChains (TopCat.of P) Q).iCycles (r + 1))) z)))
      = TensorProduct.tmul ℤ (1 : ℚ) ((ModuleCat.Hom.hom
          ((Work.Cohomology.relChains (TopCat.of P) Q).iCycles (r + 1))) z) := by
    have h : (bcRel (TopCat.of P) Q).hom.f (r + 1) ≫ (bcRel (TopCat.of P) Q).inv.f (r + 1)
        = 𝟙 ((Work.StemsB.IntRatCM.obj (Work.Cohomology.relChains (TopCat.of P) Q)).X (r + 1)) := by
      rw [← HomologicalComplex.comp_f, Iso.hom_inv_id, HomologicalComplex.id_f]
    exact congrArg (fun (g : (Work.StemsB.IntRatCM.obj (Work.Cohomology.relChains (TopCat.of P) Q)).X
          (r + 1) ⟶ (Work.StemsB.IntRatCM.obj (Work.Cohomology.relChains (TopCat.of P) Q)).X (r + 1)) =>
        (ModuleCat.Hom.hom g) (TensorProduct.tmul ℤ (1 : ℚ) ((ModuleCat.Hom.hom
          ((Work.Cohomology.relChains (TopCat.of P) Q).iCycles (r + 1))) z))) h
  have hd : (ModuleCat.Hom.hom ((Work.StemsB.IntRatCM.obj
        (Work.Cohomology.relChains (TopCat.of P) Q)).d ((r + 1) + 1) (r + 1))) W
      = TensorProduct.tmul ℤ (1 : ℚ) ((ModuleCat.Hom.hom
        ((Work.Cohomology.relChains (TopCat.of P) Q).iCycles (r + 1))) z) := by
    have hcomm := congrArg (fun (g : (Work.StemsB.relChainsR ℚ (TopCat.of P) Q).X ((r + 1) + 1) ⟶
        (Work.StemsB.IntRatCM.obj (Work.Cohomology.relChains (TopCat.of P) Q)).X (r + 1)) =>
        (ModuleCat.Hom.hom g) v)
      (HomologicalComplex.Hom.comm (bcRel (TopCat.of P) Q).inv ((r + 1) + 1) (r + 1))
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hcomm
    rw [hv, hchain, hinv] at hcomm
    exact hcomm
  exact hzt (torsion_of_d_eq_tmul_aux (Work.Cohomology.relChains (TopCat.of P) Q) (r + 1) z W hd)

end Work.Serre.Surj
