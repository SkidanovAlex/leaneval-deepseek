/-
# The small extension claim of CKMRV Proposition 3.2(1)

This file proves the "small extension claim" (CKMRV, proof of Proposition 3.2(1)): for every
neighbour `ν` of `𝓕̄`, every row `i` and every `τ ∈ O_F` whose `ν`-translate also lies in `O_F`,

  `(f |_k M'_i ν)(τ) = ∑_j σ'(ν)_{ij} (f |_k M'_j)(τ) + (h₁ |_k N'_{1i}(ν))(τ)
                        + (h₂ |_k N'_{2i}(ν))(τ)`,

where `N'` are the carries of the reduction of `rowDiffP` – the content being that the
propagation hypothesis applies at all the points in the support of the carries.

The ingredients:

* `Work.Asymptotics.exists_carry_neighborsP` : the finite check producing carries `a`, `b` whose
  support is safe, i.e. consists of group elements mapping `O_F` into `O`;
* `Work.Asymptotics.NN` : the actual carry of `carryP_exists`, whose `(T-I)²`- and
  `S(T-I)²`-parts are unique modulo `(z-1)R` (`Work.Residues.idealI_direct_augIdeal`), hence agree
  with the safe carries;
* the propagation hypothesis `Propagates`, applied at the (finitely many) safe points.
-/
import Submission.Work.Asymptotics.ExtensionEvenDefs
import Submission.Work.Asymptotics.carry_letters_assembly
import Submission.Work.Asymptotics.rowDiffP_mem

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix
open Work.Kernels Work.Residues
open scoped MatrixGroups ModularForm Modular Manifold Bundle Topology

namespace Work.Asymptotics

/-! ## The carry of the second basis -/

/-- The carry of `carryP_exists` for the reduction in the second basis `M'`. -/
noncomputable def NN : R → Fin 6 → R × R :=
  Classical.choose (carryP_exists (k := 0) (fun x i => rowDiffP_mem x i))

lemma NN_spec (x : R) (i : Fin 6) :
    rowDiffP x i - ((R_T - 1)^2 * (NN x i).1 + R_S * (R_T - 1)^2 * (NN x i).2)
      ∈ augIdeal :=
  (Classical.choose_spec (carryP_exists (k := 0) (fun x i => rowDiffP_mem x i))).1 x i

lemma NN_cocycle₁ (x y : R) (i : Fin 6) :
    (NN (x * y) i).1 - ∑ j, sigmaP x i j • (NN y j).1 - (NN x i).1 * y ∈ augIdeal :=
  (Classical.choose_spec (carryP_exists (k := 0) (fun x i => rowDiffP_mem x i))).2.1 x y i

lemma NN_cocycle₂ (x y : R) (i : Fin 6) :
    (NN (x * y) i).2 - ∑ j, sigmaP x i j • (NN y j).2 - (NN x i).2 * y ∈ augIdeal :=
  (Classical.choose_spec (carryP_exists (k := 0) (fun x i => rowDiffP_mem x i))).2.2 x y i

/-- The two carries of a safe decomposition agree with the canonical carry modulo the collapse
ideal: this is the uniqueness of the decomposition of `rowDiffP` along `(T-I)²`, `S(T-I)²`. -/
lemma carry_agree {ν : X} {i : Fin 6} {a b : Option X} (h : CarryOk ν i a b) :
    (NN (MonoidAlgebra.of ℂ X ν) i).1 - ofOpt a ∈ augIdeal ∧
      (NN (MonoidAlgebra.of ℂ X ν) i).2 - ofOpt b ∈ augIdeal := by
  have h1 := NN_spec (MonoidAlgebra.of ℂ X ν) i
  have h2 : rowDiffP (MonoidAlgebra.of ℂ X ν) i
      - ((R_T - 1)^2 * ofOpt a + R_S * (R_T - 1)^2 * ofOpt b) ∈ augIdeal := h
  have h3 : (R_T - 1)^2 * ((NN (MonoidAlgebra.of ℂ X ν) i).1 - ofOpt a)
      + R_S * (R_T - 1)^2 * ((NN (MonoidAlgebra.of ℂ X ν) i).2 - ofOpt b) ∈ augIdeal := by
    have h4 : (R_T - 1)^2 * ((NN (MonoidAlgebra.of ℂ X ν) i).1 - ofOpt a)
        + R_S * (R_T - 1)^2 * ((NN (MonoidAlgebra.of ℂ X ν) i).2 - ofOpt b)
        = -( (rowDiffP (MonoidAlgebra.of ℂ X ν) i
              - ((R_T - 1)^2 * (NN (MonoidAlgebra.of ℂ X ν) i).1
                 + R_S * (R_T - 1)^2 * (NN (MonoidAlgebra.of ℂ X ν) i).2))
             - (rowDiffP (MonoidAlgebra.of ℂ X ν) i
              - ((R_T - 1)^2 * ofOpt a + R_S * (R_T - 1)^2 * ofOpt b)) ) := by
      noncomm_ring
    rw [h4]
    exact Submodule.neg_mem _ (Submodule.sub_mem _ h1 h2)
  exact idealI_direct_augIdeal h3

/-! ## The safe points lie in `O` -/

lemma vadd_one_eq_T_smul (τ : ℍ) : (1 : ℝ) +ᵥ τ = ModularGroup.T • τ := by
  apply UpperHalfPlane.coe_injective
  have h := ModularGroup.coe_T_zpow_smul_eq τ (n := 1)
  rw [zpow_one] at h
  rw [UpperHalfPlane.coe_vadd, h]
  push_cast
  ring

lemma vadd_two_eq_TT_smul (τ : ℍ) : (2 : ℝ) +ᵥ τ = (ModularGroup.T * ModularGroup.T) • τ := by
  apply UpperHalfPlane.coe_injective
  have h := ModularGroup.coe_T_zpow_smul_eq τ (n := 2)
  rw [show (ModularGroup.T ^ (2:ℤ) : SL(2,ℤ)) = ModularGroup.T * ModularGroup.T from by
    rw [show (2:ℤ) = ((2:ℕ):ℤ) from rfl, zpow_natCast, pow_two]] at h
  rw [UpperHalfPlane.coe_vadd, h]
  push_cast
  ring

/-- A group element of the safe set maps `O_F` (and the relevant `ν`-translate) into `O`. -/
lemma smul_mem_of_mem_SafeThick {O : Set ℍ} {O_F : Set ℍ}
    (hMp : ∀ i : Fin 6, ∀ τ : ℍ, τ ∈ O_F → Mp i • τ ∈ O)
    {ν : X} {i : Fin 6} {τ : ℍ} (hτ : τ ∈ O_F) (hντ : ν • τ ∈ O_F)
    {δ : X} (hδ : δ ∈ SafeThick ν i) : δ • τ ∈ O := by
  have keyR : ∀ δ : X, (∃ j : Fin 6, Mp j = δ) → δ • τ ∈ O := by
    rintro δ ⟨j, rfl⟩
    exact hMp j τ hτ
  have keyI : (Mp i * ν) • τ ∈ O := by
    rw [mul_smul]
    exact hMp i (ν • τ) hντ
  have keyN : (-(Mp i * ν)) • τ ∈ O := by
    rw [SL_neg_smul]
    exact keyI
  simp only [SafeThick, SafeF, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
    Finset.mem_image, Finset.mem_univ, true_and] at hδ
  rcases hδ with ((hδ | hδ) | hδ) | hδ
  · exact keyR δ hδ
  · obtain ⟨γ, hγ, rfl⟩ := hδ
    rw [ModularGroup.SL_neg_smul]
    exact keyR γ hγ
  · rw [hδ]; exact keyI
  · rw [hδ]; exact keyN

/-! ## The propagation hypothesis at the safe points -/

section Propagate

variable {k : ℤ} {O : Set ℍ} {f h₁ h₂ : ℍ → ℂ}

/-- At the points of a safe `(T-I)²`-carry, the propagation hypothesis applies. -/
lemma slash_ofOpt_T2op_eq (h : Propagates k O f h₁ h₂) {O_F : Set ℍ}
    (hMp : ∀ i : Fin 6, ∀ τ : ℍ, τ ∈ O_F → Mp i • τ ∈ O)
    {ν : X} {i : Fin 6} {τ : ℍ} (hτ : τ ∈ O_F) (hντ : ν • τ ∈ O_F)
    {a : Option X} (hS : SafePair ν i a) :
    slash k (ofOpt a) (T2op f) τ = slash k (ofOpt a) h₁ τ := by
  cases a with
  | none => simp
  | some α =>
    have hsub := hS α rfl
    have h1 : α • τ ∈ O := smul_mem_of_mem_SafeThick hMp hτ hντ (hsub (by simp))
    have h2 : (1 : ℝ) +ᵥ (α • τ) ∈ O := by
      rw [vadd_one_eq_T_smul, ← mul_smul]
      exact smul_mem_of_mem_SafeThick hMp hτ hντ (hsub (by simp))
    have h3 : (2 : ℝ) +ᵥ (α • τ) ∈ O := by
      rw [vadd_two_eq_TT_smul, ← mul_smul]
      exact smul_mem_of_mem_SafeThick hMp hτ hντ (hsub (by simp))
    have hp := h.2.2.2.2.1 (α • τ) h1 h2 h3
    simp only [ofOpt_some, MonoidAlgebra.of_apply, slash_single, one_smul]
    rw [Work.Kernels.slash_apply', Work.Kernels.slash_apply', hp]

/-- At the points of a safe `S(T-I)²`-carry, the propagation hypothesis applies. -/
lemma slash_ofOpt_S2op_eq (h : Propagates k O f h₁ h₂) {O_F : Set ℍ}
    (hMp : ∀ i : Fin 6, ∀ τ : ℍ, τ ∈ O_F → Mp i • τ ∈ O)
    {ν : X} {i : Fin 6} {τ : ℍ} (hτ : τ ∈ O_F) (hντ : ν • τ ∈ O_F)
    {b : Option X} (hS : SafePairS ν i b) :
    slash k (ofOpt b) (S2op k f) τ = slash k (ofOpt b) h₂ τ := by
  cases b with
  | none => simp
  | some β =>
    have hsub := hS β rfl
    have hmem : ∀ δ : X, δ ∈ ({ModularGroup.S * β, ModularGroup.S * (ModularGroup.T * β),
        ModularGroup.S * (ModularGroup.T * ModularGroup.T * β)} : Finset X) → δ • τ ∈ O :=
      fun δ hδ => smul_mem_of_mem_SafeThick hMp hτ hντ (hsub hδ)
    have h1 : ModularGroup.S • (β • τ) ∈ O := by
      rw [← mul_smul]
      exact hmem _ (by simp)
    have h2 : ModularGroup.S • ((1 : ℝ) +ᵥ (β • τ)) ∈ O := by
      rw [vadd_one_eq_T_smul, ← mul_smul, ← mul_smul]
      exact hmem _ (by simp [mul_assoc])
    have h3 : ModularGroup.S • ((2 : ℝ) +ᵥ (β • τ)) ∈ O := by
      rw [vadd_two_eq_TT_smul, ← mul_smul, ← mul_smul]
      exact hmem _ (by simp [mul_assoc])
    have hp := h.2.2.2.2.2 (β • τ) h1 h2 h3
    simp only [ofOpt_some, MonoidAlgebra.of_apply, slash_single, one_smul]
    rw [Work.Kernels.slash_apply', Work.Kernels.slash_apply', hp]

end Propagate

/-! ## Slashing the reduction identity -/

lemma slash_rowDiffP (k : ℤ) (x : R) (i : Fin 6) (F : ℍ → ℂ) :
    slash k (rowDiffP x i) F
      = slash k (MpR i * x) F - ∑ j, (sigmaP x) i j • slash k (MpR j) F := by
  rw [rowDiffP, Work.Kernels.slash_sub, Work.Kernels.slash_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  exact Work.Kernels.AlgebraFacts.slash_smul k ((sigmaP x) i j) (MpR j) F

/-! ## The small extension claim -/

theorem small_extension_claim {k : ℤ} (hk : Even k) {O : Set ℍ} {f h₁ h₂ : ℍ → ℂ}
    (h : Propagates k O f h₁ h₂) {O_F : Set ℍ}
    (hMp : ∀ i : Fin 6, ∀ τ : ℍ, τ ∈ O_F → Mp i • τ ∈ O)
    {ν : X} (hν : ν ∈ NeighborsP) {i : Fin 6} {τ : ℍ} (hτ : τ ∈ O_F) (hντ : ν • τ ∈ O_F) :
    slash k (MpR i * MonoidAlgebra.of ℂ X ν) f τ
      = ∑ j, (sigmaP (MonoidAlgebra.of ℂ X ν)) i j • slash k (MpR j) f τ
        + slash k (NN (MonoidAlgebra.of ℂ X ν) i).1 h₁ τ
        + slash k (NN (MonoidAlgebra.of ℂ X ν) i).2 h₂ τ := by
  obtain ⟨a, b, hC, hSa, hSb⟩ := exists_carry_neighborsP ν hν i
  obtain ⟨ha1, ha2⟩ := carry_agree hC
  -- the reduction identity of `NN`, slashed
  have step1 : slash k (MpR i * MonoidAlgebra.of ℂ X ν) f τ
      = ∑ j, (sigmaP (MonoidAlgebra.of ℂ X ν)) i j • slash k (MpR j) f τ
        + slash k (NN (MonoidAlgebra.of ℂ X ν) i).1 (T2op f) τ
        + slash k (NN (MonoidAlgebra.of ℂ X ν) i).2 (S2op k f) τ := by
    obtain ⟨c, hc, hcx⟩ : ∃ c ∈ augIdeal, rowDiffP (MonoidAlgebra.of ℂ X ν) i
        = ((R_T - 1)^2 * (NN (MonoidAlgebra.of ℂ X ν) i).1
            + R_S * (R_T - 1)^2 * (NN (MonoidAlgebra.of ℂ X ν) i).2) + c :=
      ⟨_, NN_spec (MonoidAlgebra.of ℂ X ν) i, by abel⟩
    have h2 : slash k (MpR i * MonoidAlgebra.of ℂ X ν) f τ
        = slash k (rowDiffP (MonoidAlgebra.of ℂ X ν) i) f τ
          + ∑ j, (sigmaP (MonoidAlgebra.of ℂ X ν)) i j • slash k (MpR j) f τ := by
      rw [slash_rowDiffP k (MonoidAlgebra.of ℂ X ν) i f]
      simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, Finset.sum_apply, neg_one_smul]
      abel
    rw [h2, hcx]
    rw [Work.Kernels.slash_add, Work.Kernels.slash_add,
      Work.Residues.slash_mem_augIdeal hk hc f, add_zero]
    rw [Work.Kernels.AlgebraFacts.slash_mul, Work.Kernels.AlgebraFacts.slash_mul,
      Work.Kernels.slash_T2]
    simp only [Pi.add_apply, Finset.sum_apply, S2op]
    abel
  -- replacing the defects by `h₁`, `h₂`
  have step2 : slash k (NN (MonoidAlgebra.of ℂ X ν) i).1 (T2op f) τ
      = slash k (NN (MonoidAlgebra.of ℂ X ν) i).1 h₁ τ := by
    have hsplit : (NN (MonoidAlgebra.of ℂ X ν) i).1
        = ofOpt a + ((NN (MonoidAlgebra.of ℂ X ν) i).1 - ofOpt a) := by abel
    rw [hsplit, Work.Kernels.slash_add, Work.Kernels.slash_add,
      Work.Residues.slash_mem_augIdeal hk ha1 (T2op f),
      Work.Residues.slash_mem_augIdeal hk ha1 h₁]
    simp only [Pi.add_apply, Pi.zero_apply, add_zero, zero_add]
    exact slash_ofOpt_T2op_eq h hMp hτ hντ hSa
  have step3 : slash k (NN (MonoidAlgebra.of ℂ X ν) i).2 (S2op k f) τ
      = slash k (NN (MonoidAlgebra.of ℂ X ν) i).2 h₂ τ := by
    have hsplit : (NN (MonoidAlgebra.of ℂ X ν) i).2
        = ofOpt b + ((NN (MonoidAlgebra.of ℂ X ν) i).2 - ofOpt b) := by abel
    rw [hsplit, Work.Kernels.slash_add, Work.Kernels.slash_add,
      Work.Residues.slash_mem_augIdeal hk ha2 (S2op k f),
      Work.Residues.slash_mem_augIdeal hk ha2 h₂]
    simp only [Pi.add_apply, Pi.zero_apply, add_zero, zero_add]
    exact slash_ofOpt_S2op_eq h hMp hτ hντ hSb
  rw [step1, step2, step3]

end Work.Asymptotics
