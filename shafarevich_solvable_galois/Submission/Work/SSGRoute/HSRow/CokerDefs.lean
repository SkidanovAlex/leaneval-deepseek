
import Mathlib
import Submission.Work.SSGRoute.HSConj
import Submission.Work.SSGRoute.HSRestrict
import Submission.Work.SSGRoute.HS.Setup
import Submission.Work.SSGRoute.HS.Basic
import Submission.Work.SSGRoute.isCoboundary2On_top_of_procyclicGrowth
import Submission.Work.SSGRoute.HSRow.Coords
import Submission.Work.SSGRoute.PT.H2RowAux
import Submission.Work.SSGRoute.HSTwoRow.exists_lcCocycleOn_zpowers_gen_eq
import Submission.Work.SSGRoute.HSTwoRow.procyclic_hypotheses
import Submission.Work.SSGRoute.HSTwoRow.exists_zmodN_cocycle
import Submission.Work.SSGRoute.HSTwoRow.finrank_H1loc_decomp
import Submission.Work.SSGRoute.exists_openSubgroup_comap_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The inverse transgression: the `Φ`-construction (definitions)

Vocabulary for the proof of `Work.SSGRoute.HSRow.coker_injects_H2loc`.
-/

open scoped Pointwise
open Classical

namespace Work.SSGRoute.HSRow

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

variable (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]

/-- `C = closure (zpowers σ)`. -/
abbrev Ccl (σ : Ω ≃ₐ[k] Ω) : Subgroup (Ω ≃ₐ[k] Ω) :=
  Subgroup.topologicalClosure (Subgroup.zpowers σ)

/-- `σ` as an element of `C`. -/
def sigC (σ : Ω ≃ₐ[k] Ω) : ↥(Ccl k Ω σ) :=
  ⟨σ, Subgroup.le_topologicalClosure _ (Subgroup.mem_zpowers σ)⟩

@[simp] lemma sigC_coe (σ : Ω ≃ₐ[k] Ω) :
    ((sigC k Ω σ : ↥(Ccl k Ω σ)) : Ω ≃ₐ[k] Ω) = σ := rfl

/-- The locally constant `1`-cocycles on `I`. -/
abbrev Z1 (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (I : Subgroup (Ω ≃ₐ[k] Ω)) : Submodule (ZMod p) ((Ω ≃ₐ[k] Ω) → M) :=
  SSGRoute.lcCocycles p k Ω K M I

/-- The group-theoretic hypotheses on the pair `(I, σ)`. -/
structure Hcx (I : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω) where
  A : ValuationSubring Ω
  hI : I ≤ SSGRoute.decomp k A
  hnorm : ∀ δ ∈ SSGRoute.decomp k A, ∀ u ∈ I, δ * u * δ⁻¹ ∈ I
  hσ : σ ∈ SSGRoute.decomp k A
  hsup : SSGRoute.decomp k A ≤ I ⊔ Subgroup.topologicalClosure (Subgroup.zpowers σ)
  hinf : I ⊓ Subgroup.topologicalClosure (Subgroup.zpowers σ) = ⊥

lemma conj_inv_mem (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (I : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω) (H : Hcx k Ω I σ)
    (γ : ↥(Ccl k Ω σ)) :
    ∀ n ∈ I, (γ : Ω ≃ₐ[k] Ω)⁻¹ * n * (γ : Ω ≃ₐ[k] Ω) ∈ I := by
  intro n hn
  have hγD : (γ : Ω ≃ₐ[k] Ω) ∈ SSGRoute.decomp k H.A :=
    Work.SSGRoute.HS.CC_le_DD H.A σ H.hσ γ.2
  have h := H.hnorm (γ : Ω ≃ₐ[k] Ω)⁻¹ ((SSGRoute.decomp k H.A).inv_mem hγD) n hn
  simpa using h

/-- The conjugation action of `γ ∈ C` on `Z1`. -/
def tw1 (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (I : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω) (H : Hcx k Ω I σ)
    (γ : ↥(Ccl k Ω σ)) : ↥(Z1 p k Ω K M I) →ₗ[ZMod p] ↥(Z1 p k Ω K M I) where
  toFun z := ⟨h1locConjShift p k Ω K M (γ : Ω ≃ₐ[k] Ω) z.1,
    h1locConjShift_mem_lcCocycles p k Ω K M I (γ : Ω ≃ₐ[k] Ω)
      (conj_inv_mem p k Ω K M I σ H γ) z.2⟩
  map_add' z w := Subtype.ext ((h1locConjShift p k Ω K M (γ : Ω ≃ₐ[k] Ω)).map_add z.1 w.1)
  map_smul' c z := Subtype.ext ((h1locConjShift p k Ω K M (γ : Ω ≃ₐ[k] Ω)).map_smul c z.1)

@[simp] lemma tw1_apply (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (I : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω) (H : Hcx k Ω I σ)
    (γ : ↥(Ccl k Ω σ)) (z : ↥(Z1 p k Ω K M I)) (n : Ω ≃ₐ[k] Ω) :
    ((tw1 p k Ω K M I σ H γ z : ↥(Z1 p k Ω K M I)) : (Ω ≃ₐ[k] Ω) → M) n
      = SSGRoute.res k K (γ : Ω ≃ₐ[k] Ω)
          • (z : (Ω ≃ₐ[k] Ω) → M) ((γ : Ω ≃ₐ[k] Ω)⁻¹ * n * (γ : Ω ≃ₐ[k] Ω)) := rfl

/-- The conjugation shift is multiplicative in the group element. -/
lemma h1locConjShift_comp (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (γ δ : Ω ≃ₐ[k] Ω) (f : (Ω ≃ₐ[k] Ω) → M) :
    h1locConjShift p k Ω K M γ (h1locConjShift p k Ω K M δ f)
      = h1locConjShift p k Ω K M (γ * δ) f := by
  funext n
  show SSGRoute.res k K γ • (SSGRoute.res k K δ • f (δ⁻¹ * (γ⁻¹ * n * γ) * δ))
    = SSGRoute.res k K (γ * δ) • f ((γ * δ)⁻¹ * n * (γ * δ))
  rw [show δ⁻¹ * (γ⁻¹ * n * γ) * δ = (γ * δ)⁻¹ * n * (γ * δ) from by group,
    map_mul, mul_smul]

lemma tw1_comp (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (I : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω) (H : Hcx k Ω I σ)
    (γ δ : ↥(Ccl k Ω σ)) (z : ↥(Z1 p k Ω K M I)) :
    tw1 p k Ω K M I σ H γ (tw1 p k Ω K M I σ H δ z) = tw1 p k Ω K M I σ H (γ * δ) z := by
  refine Subtype.ext ?_
  exact h1locConjShift_comp p k Ω K M (γ : Ω ≃ₐ[k] Ω) (δ : Ω ≃ₐ[k] Ω) (z : (Ω ≃ₐ[k] Ω) → M)

lemma tw1_one (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (I : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω) (H : Hcx k Ω I σ) :
    tw1 p k Ω K M I σ H (1 : ↥(Ccl k Ω σ)) = LinearMap.id := by
  refine LinearMap.ext fun z => Subtype.ext (funext fun n => ?_)
  simp only [tw1_apply, OneMemClass.coe_one, map_one, one_mul, inv_one, one_smul]
  rfl

lemma tw1_inv_comp (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (I : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω) (H : Hcx k Ω I σ)
    (γ : ↥(Ccl k Ω σ)) (z : ↥(Z1 p k Ω K M I)) :
    tw1 p k Ω K M I σ H γ⁻¹ (tw1 p k Ω K M I σ H γ z) = z := by
  rw [tw1_comp, inv_mul_cancel]
  have h : tw1 p k Ω K M I σ H (1 : ↥(Ccl k Ω σ)) z = z := by
    rw [tw1_one]; rfl
  exact h

lemma tw1_comp_inv (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (I : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω) (H : Hcx k Ω I σ)
    (γ : ↥(Ccl k Ω σ)) (z : ↥(Z1 p k Ω K M I)) :
    tw1 p k Ω K M I σ H γ (tw1 p k Ω K M I σ H γ⁻¹ z) = z := by
  rw [tw1_comp, mul_inv_cancel]
  have h : tw1 p k Ω K M I σ H (1 : ↥(Ccl k Ω σ)) z = z := by
    rw [tw1_one]; rfl
  exact h

/-- The conjugation action of `C` on `Z1`, as a homomorphism into the endomorphism monoid. -/
def twHom1 (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (I : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω) (H : Hcx k Ω I σ) :
    ↥(Ccl k Ω σ) →* (↥(Z1 p k Ω K M I) →ₗ[ZMod p] ↥(Z1 p k Ω K M I)) where
  toFun := tw1 p k Ω K M I σ H
  map_one' := tw1_one p k Ω K M I σ H
  map_mul' γ δ := by
    refine LinearMap.ext fun z => ?_
    rw [Module.End.mul_apply]
    exact (tw1_comp p k Ω K M I σ H γ δ z).symm

/-- The conjugation action of `γ ∈ C` on `Z1`, as a linear equivalence. -/
def tw1e (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (I : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω) (H : Hcx k Ω I σ)
    (γ : ↥(Ccl k Ω σ)) : ↥(Z1 p k Ω K M I) ≃ₗ[ZMod p] ↥(Z1 p k Ω K M I) where
  toLinearMap := tw1 p k Ω K M I σ H γ
  invFun := tw1 p k Ω K M I σ H γ⁻¹
  left_inv z := tw1_inv_comp p k Ω K M I σ H γ z
  right_inv z := tw1_comp_inv p k Ω K M I σ H γ z

@[simp] lemma tw1e_apply (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (I : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω) (H : Hcx k Ω I σ)
    (γ : ↥(Ccl k Ω σ)) (z : ↥(Z1 p k Ω K M I)) :
    tw1e p k Ω K M I σ H γ z = tw1 p k Ω K M I σ H γ z := rfl

/-- The conjugation action of `C` on `Z1`, as a monoid homomorphism into its automorphism
group. -/
def twHom (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (I : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω) (H : Hcx k Ω I σ) :
    ↥(Ccl k Ω σ) →* (↥(Z1 p k Ω K M I) ≃ₗ[ZMod p] ↥(Z1 p k Ω K M I)) where
  toFun := tw1e p k Ω K M I σ H
  map_one' := by
    refine LinearEquiv.ext fun z => Subtype.ext (funext fun n => ?_)
    simp only [tw1e_apply, tw1_apply, OneMemClass.coe_one, map_one, one_mul, inv_one,
      one_smul]
    rfl
  map_mul' γ δ := by
    refine LinearEquiv.ext fun z => ?_
    simp only [LinearEquiv.mul_apply, tw1e_apply]
    exact (tw1_comp p k Ω K M I σ H γ δ z).symm

lemma twHom_apply (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (I : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω) (H : Hcx k Ω I σ)
    (γ : ↥(Ccl k Ω σ)) (z : ↥(Z1 p k Ω K M I)) :
    twHom p k Ω K M I σ H γ z = tw1 p k Ω K M I σ H γ z := rfl

/-- The conjugation action is multiplicative in the group element, as an equality of linear
maps. -/
lemma tw1_comp_map (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (I : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω) (H : Hcx k Ω I σ)
    (γ δ : ↥(Ccl k Ω σ)) :
    tw1 p k Ω K M I σ H (γ * δ) =
      (tw1 p k Ω K M I σ H γ).comp (tw1 p k Ω K M I σ H δ) := by
  refine LinearMap.ext fun z => ?_
  rw [LinearMap.comp_apply]
  exact (tw1_comp p k Ω K M I σ H γ δ z).symm

/-- Powers act by composition of the conjugation action. -/
lemma tw1_pow (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (I : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω) (H : Hcx k Ω I σ)
    (γ : ↥(Ccl k Ω σ)) (j : ℕ) :
    tw1 p k Ω K M I σ H (γ ^ j) = (tw1 p k Ω K M I σ H γ) ^ j := by
  induction j with
  | zero =>
      rw [pow_zero, tw1_one, pow_zero]
      rfl
  | succ j ih =>
      rw [pow_succ', tw1_comp_map, ih, pow_succ', Module.End.mul_eq_comp]

/-- **The period.**  If `Z1` is finite, the conjugation action of `σ` on it has a positive
period `e`. -/
lemma exists_period (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (I : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω) (H : Hcx k Ω I σ)
    [Finite ↥(Z1 p k Ω K M I)] :
    ∃ e : ℕ, 0 < e ∧ ∀ z : ↥(Z1 p k Ω K M I),
      tw1 p k Ω K M I σ H ((sigC k Ω σ) ^ e) z = z := by
  classical
  haveI : Fintype ↥(Z1 p k Ω K M I) := Fintype.ofFinite _
  let g : ↥(Z1 p k Ω K M I) → ↥(Z1 p k Ω K M I) := tw1 p k Ω K M I σ H (sigC k Ω σ)
  have hg_inj : Function.Injective g := by
    intro z w hzw
    have h := congrArg (fun x => tw1 p k Ω K M I σ H ((sigC k Ω σ))⁻¹ x) hzw
    simpa [g, tw1_inv_comp] using h
  have hg_surj : Function.Surjective g := Finite.surjective_of_injective hg_inj
  let T : Equiv.Perm ↥(Z1 p k Ω K M I) := Equiv.ofBijective g ⟨hg_inj, hg_surj⟩
  have hTcoe : (T : ↥(Z1 p k Ω K M I) → ↥(Z1 p k Ω K M I)) = g := rfl
  refine ⟨Fintype.card (Equiv.Perm ↥(Z1 p k Ω K M I)), Fintype.card_pos_iff.mpr ⟨1⟩, ?_⟩
  intro z
  have hcard : T ^ (Fintype.card (Equiv.Perm ↥(Z1 p k Ω K M I))) = 1 := pow_card_eq_one
  have h1 : (T ^ (Fintype.card (Equiv.Perm ↥(Z1 p k Ω K M I)))) z = z := by
    rw [hcard]
    rfl
  have h2 : (T ^ (Fintype.card (Equiv.Perm ↥(Z1 p k Ω K M I)))) z
      = ((tw1 p k Ω K M I σ H (sigC k Ω σ)) ^
          (Fintype.card (Equiv.Perm ↥(Z1 p k Ω K M I)))) z := by
    rw [Equiv.Perm.coe_pow, hTcoe]
    induction (Fintype.card (Equiv.Perm ↥(Z1 p k Ω K M I))) with
    | zero => rfl
    | succ n ih =>
        rw [Function.iterate_succ_apply', ih, pow_succ', Module.End.mul_apply]
  rw [tw1_pow, ← h2, h1]

/-- The partial sums `j ↦ ∑_{i<j} tw1 σ^i β`. -/
def Psi (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (I : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω) (H : Hcx k Ω I σ)
    (β : ↥(Z1 p k Ω K M I)) (j : ℕ) : ↥(Z1 p k Ω K M I) :=
  ∑ i ∈ Finset.range j, tw1 p k Ω K M I σ H ((sigC k Ω σ) ^ i) β

@[simp] lemma Psi_zero (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (I : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω) (H : Hcx k Ω I σ)
    (β : ↥(Z1 p k Ω K M I)) : Psi p k Ω K M I σ H β 0 = 0 := by
  simp [Psi]

lemma Psi_succ (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (I : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω) (H : Hcx k Ω I σ)
    (β : ↥(Z1 p k Ω K M I)) (j : ℕ) :
    Psi p k Ω K M I σ H β (j + 1) =
      Psi p k Ω K M I σ H β j + tw1 p k Ω K M I σ H ((sigC k Ω σ) ^ j) β := by
  rw [Psi, Finset.sum_range_succ, Psi]

lemma Psi_add (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (I : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω) (H : Hcx k Ω I σ)
    (β : ↥(Z1 p k Ω K M I)) (j m : ℕ) :
    Psi p k Ω K M I σ H β (j + m) =
      Psi p k Ω K M I σ H β j + tw1 p k Ω K M I σ H ((sigC k Ω σ) ^ j)
        (Psi p k Ω K M I σ H β m) := by
  simp only [Psi, Finset.sum_range_add]
  congr 1
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [tw1_comp, pow_add]

/-- The sum over a full period `p·e` vanishes. -/
lemma Psi_mul_period (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (I : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω) (H : Hcx k Ω I σ)
    (β : ↥(Z1 p k Ω K M I)) (e : ℕ)
    (he : ∀ z : ↥(Z1 p k Ω K M I), tw1 p k Ω K M I σ H ((sigC k Ω σ) ^ e) z = z) :
    Psi p k Ω K M I σ H β (p * e) = 0 := by
  have htw : tw1 p k Ω K M I σ H ((sigC k Ω σ) ^ e) = 1 := by
    rw [Module.End.one_eq_id]
    exact LinearMap.ext he
  have h1 : ∀ m : ℕ, Psi p k Ω K M I σ H β (m * e) =
      m • (Psi p k Ω K M I σ H β e) := by
    intro m
    induction m with
    | zero => rw [Nat.zero_mul, zero_smul, Psi_zero]
    | succ m ih =>
        rw [Nat.succ_mul, Psi_add, ih]
        have h2 : tw1 p k Ω K M I σ H ((sigC k Ω σ) ^ (m * e))
            (Psi p k Ω K M I σ H β e) = Psi p k Ω K M I σ H β e := by
          rw [pow_mul' (sigC k Ω σ) m e, tw1_pow, htw, one_pow]
          rfl
        rw [h2, succ_nsmul]
  rw [h1 p, ← Nat.cast_smul_eq_nsmul (ZMod p) p (Psi p k Ω K M I σ H β e),
    ZMod.natCast_self, zero_smul]

/-- Periodicity of the partial sums. -/
lemma Psi_period (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (I : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω) (H : Hcx k Ω I σ)
    (β : ↥(Z1 p k Ω K M I)) (e : ℕ)
    (he : ∀ z : ↥(Z1 p k Ω K M I), tw1 p k Ω K M I σ H ((sigC k Ω σ) ^ e) z = z)
    (j : ℕ) :
    Psi p k Ω K M I σ H β (j + p * e) = Psi p k Ω K M I σ H β j := by
  rw [Psi_add, Psi_mul_period p k Ω K M I σ H β e he, map_zero, add_zero]

/-- The partial sums as a function on `ZMod (p·e)`. -/
def PsiZ (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (I : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω) (H : Hcx k Ω I σ)
    (e : ℕ) (β : ↥(Z1 p k Ω K M I)) : ZMod (p * e) → ↥(Z1 p k Ω K M I) :=
  fun x => Psi p k Ω K M I σ H β x.val

@[simp] lemma PsiZ_apply (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (I : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω) (H : Hcx k Ω I σ)
    (e : ℕ) (β : ↥(Z1 p k Ω K M I)) (x : ZMod (p * e)) :
    PsiZ p k Ω K M I σ H e β x = Psi p k Ω K M I σ H β x.val := rfl

/-- The crossed homomorphism identity for the partial sums on `ZMod (p·e)`. -/
lemma PsiZ_add (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (I : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω) (H : Hcx k Ω I σ)
    (e : ℕ) [NeZero (p * e)] (β : ↥(Z1 p k Ω K M I))
    (he : ∀ z : ↥(Z1 p k Ω K M I), tw1 p k Ω K M I σ H ((sigC k Ω σ) ^ e) z = z)
    (x y : ZMod (p * e)) :
    PsiZ p k Ω K M I σ H e β (x + y) =
      PsiZ p k Ω K M I σ H e β x
        + tw1 p k Ω K M I σ H ((sigC k Ω σ) ^ x.val)
            (PsiZ p k Ω K M I σ H e β y) := by
  classical
  show Psi p k Ω K M I σ H β (x + y).val =
    Psi p k Ω K M I σ H β x.val
      + tw1 p k Ω K M I σ H ((sigC k Ω σ) ^ x.val) (Psi p k Ω K M I σ H β y.val)
  rw [ZMod.val_add, ← Psi_add]
  rcases Nat.lt_or_ge (x.val + y.val) (p * e) with hlt | hge
  · rw [Nat.mod_eq_of_lt hlt]
  · have h2 : (x.val + y.val) % (p * e) = x.val + y.val - p * e := by
      rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt]
      have := ZMod.val_lt (n := p * e) x
      have := ZMod.val_lt (n := p * e) y
      omega
    have h3 : Psi p k Ω K M I σ H β (x.val + y.val) =
        Psi p k Ω K M I σ H β (x.val + y.val - p * e) := by
      have h1 : x.val + y.val = (x.val + y.val - p * e) + p * e := by
        have := ZMod.val_lt (n := p * e) x
        have := ZMod.val_lt (n := p * e) y
        omega
      conv_lhs => rw [h1]
      rw [Psi_period p k Ω K M I σ H β e he]
    rw [h2, h3]

/-- A continuous homomorphism `C →* Multiplicative (ZMod N)` sending `σ` to `1`. -/
lemma exists_chiC (σ : Ω ≃ₐ[k] Ω) (N : ℕ) (hN : 0 < N)
    (hZ : ∀ n : ℕ, 0 < n → ∃ f : ↥(Ccl k Ω σ) →* Multiplicative (ZMod n),
      Function.Surjective f) :
    ∃ χ : ↥(Ccl k Ω σ) →* Multiplicative (ZMod N),
      Continuous χ ∧ χ (sigC k Ω σ) = Multiplicative.ofAdd 1 :=
  Work.SSGRoute.HSTwoRow.exists_cont_hom_zmod_zpowers k Ω σ N hN
    Work.SSGRoute.HSTwoRow.mem_powSubgroup_all_eq_one hZ

/-- The crossed homomorphism `C → Z1` attached to `β`, `e` and `χ`. -/
def Phi (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (I : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω) (H : Hcx k Ω I σ)
    (e : ℕ) (χ : ↥(Ccl k Ω σ) →* Multiplicative (ZMod (p * e)))
    (β : ↥(Z1 p k Ω K M I)) (γ : ↥(Ccl k Ω σ)) : ↥(Z1 p k Ω K M I) :=
  PsiZ p k Ω K M I σ H e β (Multiplicative.toAdd (χ γ))

@[simp] lemma Phi_apply (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (I : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω) (H : Hcx k Ω I σ)
    (e : ℕ) (χ : ↥(Ccl k Ω σ) →* Multiplicative (ZMod (p * e)))
    (β : ↥(Z1 p k Ω K M I)) (γ : ↥(Ccl k Ω σ)) :
    Phi p k Ω K M I σ H e χ β γ
      = PsiZ p k Ω K M I σ H e β (Multiplicative.toAdd (χ γ)) := rfl

lemma Phi_sigC (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (I : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω) (H : Hcx k Ω I σ)
    (e : ℕ) (h1lt : 1 < p * e)
    (χ : ↥(Ccl k Ω σ) →* Multiplicative (ZMod (p * e)))
    (hχ : χ (sigC k Ω σ) = Multiplicative.ofAdd 1)
    (β : ↥(Z1 p k Ω K M I)) :
    Phi p k Ω K M I σ H e χ β (sigC k Ω σ) = β := by
  haveI : Fact (1 < p * e) := ⟨h1lt⟩
  rw [Phi_apply, hχ, toAdd_ofAdd, PsiZ_apply, ZMod.val_one, Psi, Finset.sum_range_one,
    pow_zero, tw1_one]
  rfl

lemma Phi_one (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (I : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω) (H : Hcx k Ω I σ)
    (e : ℕ) [NeZero (p * e)] (χ : ↥(Ccl k Ω σ) →* Multiplicative (ZMod (p * e)))
    (β : ↥(Z1 p k Ω K M I)) :
    Phi p k Ω K M I σ H e χ β 1 = 0 := by
  rw [Phi_apply, map_one, toAdd_one, PsiZ_apply, ZMod.val_zero, Psi_zero]

end

end Work.SSGRoute.HSRow
