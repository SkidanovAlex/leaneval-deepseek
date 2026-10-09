import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.DualMod.Main
import Submission.Work.SSGRoute.LTDArch.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped TensorProduct

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace Work.SSGRoute

namespace ArchAux

theorem exists_isOpen_subgroup_not_mem {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (c : Ω ≃ₐ[k] Ω) (hc : c ^ 2 = 1) (hc1 : c ≠ 1) :
    ∃ U : Subgroup (Ω ≃ₐ[k] Ω), IsOpen (U : Set (Ω ≃ₐ[k] Ω)) ∧
      ∀ u ∈ U, u ∈ Subgroup.zpowers c → u = 1 := by
  obtain ⟨x, hx⟩ := DFunLike.exists_ne hc1
  haveI : Algebra.IsIntegral k Ω := Algebra.IsAlgebraic.isIntegral
  let F : IntermediateField k Ω := IntermediateField.adjoin k {x}
  haveI hF : FiniteDimensional k F :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral x)
  have hcF : c ∉ F.fixingSubgroup := by
    intro hmem
    rw [IntermediateField.mem_fixingSubgroup_iff] at hmem
    refine hx (hmem x ?_)
    exact IntermediateField.subset_adjoin k ({x} : Set Ω) (Set.mem_singleton x)
  refine ⟨F.fixingSubgroup, IntermediateField.fixingSubgroup_isOpen F, ?_⟩
  intro u hu huzp
  rcases Ach.mem_zpowers_eq_one_or c hc huzp with h1 | h1
  · exact h1
  · exact absurd (h1 ▸ hu) hcF

section Conc

variable {Γ G M : Type} [Group Γ] [TopologicalSpace Γ] [Group G] [AddCommGroup M]
  [DistribMulAction G M]

noncomputable def conc (c : Γ) (m : M) : Γ → M := by
  classical
  exact fun x => if x = c then m else 0

@[simp] lemma conc_self (c : Γ) (m : M) : conc c m c = m := by
  classical
  simp [conc]

lemma conc_of_ne {x : Γ} (c : Γ) (m : M) (hx : x ≠ c) : conc c m x = 0 := by
  classical
  simp [conc, hx]

lemma isCocycleOn_conc (act : Γ →* G) (c : Γ) (hc : c ^ 2 = 1) (hc1 : c ≠ 1) (m : M)
    (hm : m + act c • m = 0) :
    SSGRoute.IsCocycleOn act (Subgroup.zpowers c) (conc c m) := by
  rw [Ach.isCocycleOn_zpowers_iff act c hc]
  exact ⟨conc_of_ne c m (Ne.symm hc1), by rw [conc_self]; exact hm⟩

lemma isLocConstOn_conc (c : Γ) (m : M) (U : Subgroup Γ) (hU : IsOpen (U : Set Γ))
    (hUdisj : ∀ u ∈ U, u ∈ Subgroup.zpowers c → u = 1) :
    SSGRoute.IsLocConstOn (Subgroup.zpowers c) (conc c m) := by
  refine ⟨U, hU, ?_⟩
  intro g hg u hu huH
  rw [hUdisj u hu huH, mul_one]

theorem exists_cocycle_locConst_conc (act : Γ →* G) (c : Γ) (hc : c ^ 2 = 1) (hc1 : c ≠ 1)
    (U : Subgroup Γ) (hU : IsOpen (U : Set Γ))
    (hUdisj : ∀ u ∈ U, u ∈ Subgroup.zpowers c → u = 1) (m : M)
    (hm : m + act c • m = 0) :
    ∃ f : Γ → M, SSGRoute.IsCocycleOn act (Subgroup.zpowers c) f ∧
      SSGRoute.IsLocConstOn (Subgroup.zpowers c) f ∧ f c = m :=
  ⟨conc c m, isCocycleOn_conc act c hc hc1 m hm, isLocConstOn_conc c m U hU hUdisj, conc_self c m⟩

end Conc

section Op

variable {p : ℕ} [Fact p.Prime] {G M : Type} [Group G] [AddCommGroup M] [Module (ZMod p) M]
  [DistribMulAction G M] [SMulCommClass G (ZMod p) M]

noncomputable def onePlus (σ : G) : M →ₗ[ZMod p] M :=
  1 + DistribSMul.toLinearMap (ZMod p) M σ

lemma onePlus_apply (σ : G) (y : M) : onePlus (p := p) σ y = y + σ • y := by
  simp [onePlus, DistribSMul.toLinearMap]

lemma dualSMul_apply_of_inv_eq_self (σ : G) (hσ : σ⁻¹ = σ) (ψ : DualMod p M) (y : M) :
    (σ • ψ) y = ψ (σ • y) := by
  rw [DualMod.dualSMul_apply, hσ]

lemma onePlus_dualMap_apply (σ : G) (ψ : DualMod p M) (y : M) :
    (onePlus (p := p) σ).dualMap ψ y = ψ y + ψ (σ • y) := by
  rw [LinearMap.dualMap_apply, onePlus_apply, map_add]

lemma dualMap_onePlus (σ : G) (hσ : σ⁻¹ = σ) (ψ : DualMod p M) :
    (onePlus (p := p) σ).dualMap ψ = σ • ψ + ψ := by
  ext y
  rw [onePlus_dualMap_apply, ← dualSMul_apply_of_inv_eq_self σ hσ, LinearMap.add_apply, add_comm]

end Op

theorem isCoboundaryOn_of_isCocycleOn_of_ne_two (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    {Γ G M : Type} [Group Γ] [Group G] [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction G M] [SMulCommClass G (ZMod p) M]
    (act : Γ →* G) (c : Γ) (hc : c ^ 2 = 1) (f : Γ → M)
    (hf : SSGRoute.IsCocycleOn act (Subgroup.zpowers c) f) :
    SSGRoute.IsCoboundaryOn act (Subgroup.zpowers c) f := by
  obtain ⟨hf1, hfc⟩ := (Ach.isCocycleOn_zpowers_iff act c hc f).mp hf
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h
    have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
    have hge : 2 ≤ p := (Fact.out : Nat.Prime p).two_le
    exact hp (le_antisymm hle hge)
  have hσv : act c • f c = -f c := eq_neg_of_add_eq_zero_right hfc
  have hsum : (2⁻¹ : ZMod p) + 2⁻¹ = 1 := by
    rw [← two_mul, mul_inv_cancel₀ h2]
  refine (Ach.isCoboundaryOn_zpowers_iff act c hc f).mpr
    ⟨hf1, -(2⁻¹ : ZMod p) • f c, ?_⟩
  have h1 : act c • (-(2⁻¹ : ZMod p) • f c) = (2⁻¹ : ZMod p) • f c := by
    rw [smul_comm (act c) (-(2⁻¹ : ZMod p)) (f c), hσv, neg_smul_neg]
  have h2' : - (-(2⁻¹ : ZMod p) • f c) = (2⁻¹ : ZMod p) • f c := by
    rw [neg_smul, neg_neg]
  rw [h1, sub_eq_add_neg, h2', ← add_smul, hsum, one_smul]

end ArchAux

theorem local_tate_duality_archimedean (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (E T : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
    [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (c : Ω ≃ₐ[k] Ω) (hc : c ^ 2 = 1) :
    ∃ pair : ((Ω ≃ₐ[k] Ω) → E) →
        ((Ω ≃ₐ[k] Ω) → SSGRoute.DualMod p (TensorProduct (ZMod p) E T)) → ZMod p,
      (∀ (f f' g : (Ω ≃ₐ[k] Ω) → E)
          (g' g'' : (Ω ≃ₐ[k] Ω) → SSGRoute.DualMod p (TensorProduct (ZMod p) E T)),
        (SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) f ∧
          SSGRoute.IsLocConstOn (Subgroup.zpowers c) f) →
        (SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) f' ∧
          SSGRoute.IsLocConstOn (Subgroup.zpowers c) f') →
        (SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) g' ∧
          SSGRoute.IsLocConstOn (Subgroup.zpowers c) g') →
        pair (f + f') g' = pair f g' + pair f' g') ∧
      (∀ (g g' : (Ω ≃ₐ[k] Ω) → E)
          (f f' : (Ω ≃ₐ[k] Ω) → SSGRoute.DualMod p (TensorProduct (ZMod p) E T)),
        (SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) g ∧
          SSGRoute.IsLocConstOn (Subgroup.zpowers c) g) →
        (SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) f ∧
          SSGRoute.IsLocConstOn (Subgroup.zpowers c) f) →
        (SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) f' ∧
          SSGRoute.IsLocConstOn (Subgroup.zpowers c) f') →
        pair g (f + f') = pair g f + pair g f') ∧
      (∀ (f : (Ω ≃ₐ[k] Ω) → E)
          (g : (Ω ≃ₐ[k] Ω) → SSGRoute.DualMod p (TensorProduct (ZMod p) E T)),
        (SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) f ∧
          SSGRoute.IsLocConstOn (Subgroup.zpowers c) f) →
        (SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) g ∧
          SSGRoute.IsLocConstOn (Subgroup.zpowers c) g) →
        SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (Subgroup.zpowers c) f →
        pair f g = 0) ∧
      (∀ (f : (Ω ≃ₐ[k] Ω) → E)
          (g : (Ω ≃ₐ[k] Ω) → SSGRoute.DualMod p (TensorProduct (ZMod p) E T)),
        (SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) f ∧
          SSGRoute.IsLocConstOn (Subgroup.zpowers c) f) →
        (SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) g ∧
          SSGRoute.IsLocConstOn (Subgroup.zpowers c) g) →
        SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (Subgroup.zpowers c) g →
        pair f g = 0) ∧
      (∀ (f : (Ω ≃ₐ[k] Ω) → E),
        (SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) f ∧
          SSGRoute.IsLocConstOn (Subgroup.zpowers c) f) →
        (∀ g : (Ω ≃ₐ[k] Ω) → SSGRoute.DualMod p (TensorProduct (ZMod p) E T),
          (SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) g ∧
          SSGRoute.IsLocConstOn (Subgroup.zpowers c) g) → pair f g = 0) →
        SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (Subgroup.zpowers c) f) ∧
      (∀ (g : (Ω ≃ₐ[k] Ω) → SSGRoute.DualMod p (TensorProduct (ZMod p) E T)),
        (SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) g ∧
          SSGRoute.IsLocConstOn (Subgroup.zpowers c) g) →
        (∀ f : (Ω ≃ₐ[k] Ω) → E,
          (SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) f ∧
          SSGRoute.IsLocConstOn (Subgroup.zpowers c) f) → pair f g = 0) →
        SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (Subgroup.zpowers c) g) := by
  classical
  have hfin : Module.finrank (ZMod p) T = 1 := hT.1
  have hσinv : (SSGRoute.res k K c)⁻¹ = SSGRoute.res k K c :=
    inv_eq_of_mul_eq_one_right (by rw [← map_mul, ← pow_two, hc, map_one])
  have hTtriv : p = 2 → ∀ (σ : Ω ≃ₐ[k] Ω) (t : T), SSGRoute.res k K σ • t = t := by
    intro hp2 σ t
    subst hp2
    have hz : ζ = -1 := IsPrimitiveRoot.eq_neg_one_of_two_right hζ
    have hσζ : σ • ζ = ζ ^ 1 := by rw [hz, pow_one]; simp
    have := hT.2 σ 1 hσζ t
    simpa using this
  have htoE : p = 2 → ∀ (σ : Ω ≃ₐ[k] Ω) (y : E ⊗[ZMod p] T),
      Ach.toE p E T (Ach.coord p T hfin) (SSGRoute.res k K σ • y) =
        SSGRoute.res k K σ • Ach.toE p E T (Ach.coord p T hfin) y := by
    intro hp2 σ y
    subst hp2
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul e t =>
        show Ach.coord 2 T hfin (SSGRoute.res k K σ • t) • (SSGRoute.res k K σ • e) =
          SSGRoute.res k K σ • (Ach.coord 2 T hfin t • e)
        rw [hTtriv rfl σ t, smul_comm (SSGRoute.res k K σ) (Ach.coord 2 T hfin t) e]
    | add x y hx hy => simp only [smul_add, map_add, hx, hy]
  have hAB : ∀ y : E ⊗[ZMod p] T,
      Ach.toE p E T (Ach.coord p T hfin) y ⊗ₜ[ZMod p] Ach.t0 p T hfin = y := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul e t => rw [Ach.toE_tmul, TensorProduct.smul_tmul, Ach.smul_coord_t0]
    | add x y hx hy => rw [map_add, TensorProduct.add_tmul, hx, hy]
  refine ⟨Ach.archPair p (Ω ≃ₐ[k] Ω) E T hfin c, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro f f' g g' g'' hf hf' hg'
    by_cases hp2 : p = 2
    · rw [Ach.archPair_apply_of_eq_two (h := hfin) p (Ω ≃ₐ[k] Ω) E T hp2 c (f + f') g',
        Ach.archPair_apply_of_eq_two (h := hfin) p (Ω ≃ₐ[k] Ω) E T hp2 c f g',
        Ach.archPair_apply_of_eq_two (h := hfin) p (Ω ≃ₐ[k] Ω) E T hp2 c f' g']
      simp only [Pi.add_apply, TensorProduct.add_tmul, map_add]
    · rw [Ach.archPair_apply_of_ne_two (h := hfin) p (Ω ≃ₐ[k] Ω) E T hp2 c (f + f') g',
        Ach.archPair_apply_of_ne_two (h := hfin) p (Ω ≃ₐ[k] Ω) E T hp2 c f g',
        Ach.archPair_apply_of_ne_two (h := hfin) p (Ω ≃ₐ[k] Ω) E T hp2 c f' g', add_zero]
  · intro g g' f f' h5 h6 h7
    by_cases hp2 : p = 2
    · rw [Ach.archPair_apply_of_eq_two (h := hfin) p (Ω ≃ₐ[k] Ω) E T hp2 c g (f + f'),
        Ach.archPair_apply_of_eq_two (h := hfin) p (Ω ≃ₐ[k] Ω) E T hp2 c g f,
        Ach.archPair_apply_of_eq_two (h := hfin) p (Ω ≃ₐ[k] Ω) E T hp2 c g f']
      simp only [Pi.add_apply, LinearMap.add_apply]
    · rw [Ach.archPair_apply_of_ne_two (h := hfin) p (Ω ≃ₐ[k] Ω) E T hp2 c g (f + f'),
        Ach.archPair_apply_of_ne_two (h := hfin) p (Ω ≃ₐ[k] Ω) E T hp2 c g f,
        Ach.archPair_apply_of_ne_two (h := hfin) p (Ω ≃ₐ[k] Ω) E T hp2 c g f', add_zero]
  · intro f g hf hg hfb
    by_cases hp2 : p = 2
    · subst hp2
      obtain ⟨-, m, hm⟩ := (Ach.isCoboundaryOn_zpowers_iff (SSGRoute.res k K) c hc f).mp hfb
      obtain ⟨-, hgc⟩ := (Ach.isCocycleOn_zpowers_iff (SSGRoute.res k K) c hc g).mp hg.1
      have hψzero : (ArchAux.onePlus (p := 2) (SSGRoute.res k K c)).dualMap (g c) = 0 := by
        rw [ArchAux.dualMap_onePlus (SSGRoute.res k K c) hσinv, add_comm]
        exact hgc
      rw [Ach.archPair_apply_of_eq_two (h := hfin) 2 (Ω ≃ₐ[k] Ω) E T rfl c f g]
      have hkey : f c = SSGRoute.res k K c • m + m := by
        rw [hm, Ach.sub_eq_add_of_eq_two 2 rfl]
      have hsmul : (SSGRoute.res k K c • m) ⊗ₜ[ZMod 2] Ach.t0 2 T hfin =
          SSGRoute.res k K c • (m ⊗ₜ[ZMod 2] Ach.t0 2 T hfin) := by
        rw [show SSGRoute.res k K c • (m ⊗ₜ[ZMod 2] Ach.t0 2 T hfin) =
            (SSGRoute.res k K c • m) ⊗ₜ[ZMod 2] (SSGRoute.res k K c • Ach.t0 2 T hfin) from rfl,
          hTtriv rfl c (Ach.t0 2 T hfin)]
      have h2 : f c ⊗ₜ[ZMod 2] Ach.t0 2 T hfin =
          ArchAux.onePlus (p := 2) (SSGRoute.res k K c) (m ⊗ₜ[ZMod 2] Ach.t0 2 T hfin) := by
        rw [hkey, ArchAux.onePlus_apply, TensorProduct.add_tmul, ← hsmul, add_comm]
      rw [h2, ← LinearMap.dualMap_apply, hψzero, LinearMap.zero_apply]
    · rw [Ach.archPair_apply_of_ne_two (h := hfin) p (Ω ≃ₐ[k] Ω) E T hp2 c f g]
  · intro f g hf hg hgb
    by_cases hp2 : p = 2
    · subst hp2
      obtain ⟨-, ψ₀, hψ₀⟩ := (Ach.isCoboundaryOn_zpowers_iff (SSGRoute.res k K) c hc g).mp hgb
      obtain ⟨-, hfc⟩ := (Ach.isCocycleOn_zpowers_iff (SSGRoute.res k K) c hc f).mp hf.1
      rw [Ach.archPair_apply_of_eq_two (h := hfin) 2 (Ω ≃ₐ[k] Ω) E T rfl c f g]
      have hgc : g c = SSGRoute.res k K c • ψ₀ + ψ₀ := by
        rw [hψ₀, Ach.sub_eq_add_of_eq_two 2 rfl]
      have hsmul : (SSGRoute.res k K c • f c) ⊗ₜ[ZMod 2] Ach.t0 2 T hfin =
          SSGRoute.res k K c • (f c ⊗ₜ[ZMod 2] Ach.t0 2 T hfin) := by
        rw [show SSGRoute.res k K c • (f c ⊗ₜ[ZMod 2] Ach.t0 2 T hfin) =
            (SSGRoute.res k K c • f c) ⊗ₜ[ZMod 2] (SSGRoute.res k K c • Ach.t0 2 T hfin) from rfl,
          hTtriv rfl c (Ach.t0 2 T hfin)]
      have hx : SSGRoute.res k K c • (f c ⊗ₜ[ZMod 2] Ach.t0 2 T hfin) +
          (f c ⊗ₜ[ZMod 2] Ach.t0 2 T hfin) = 0 := by
        rw [← hsmul, ← TensorProduct.add_tmul, add_comm, hfc, TensorProduct.zero_tmul]
      rw [hgc, LinearMap.add_apply, ArchAux.dualSMul_apply_of_inv_eq_self _ hσinv, ← map_add, hx,
        map_zero]
    · rw [Ach.archPair_apply_of_ne_two (h := hfin) p (Ω ≃ₐ[k] Ω) E T hp2 c f g]
  · intro f hf hzero
    by_cases hp2 : p = 2
    · subst hp2
      obtain ⟨hf1, hfc⟩ := (Ach.isCocycleOn_zpowers_iff (SSGRoute.res k K) c hc f).mp hf.1
      by_cases hc1 : c = 1
      · refine (Ach.isCoboundaryOn_zpowers_iff (SSGRoute.res k K) c hc f).mpr ⟨hf1, 0, ?_⟩
        rw [hc1, hf1, map_one, one_smul, sub_self]
      · obtain ⟨U, hUopen, hUdisj⟩ := ArchAux.exists_isOpen_subgroup_not_mem c hc hc1
        have hsmul : ∀ e : E, (SSGRoute.res k K c • e) ⊗ₜ[ZMod 2] Ach.t0 2 T hfin =
            SSGRoute.res k K c • (e ⊗ₜ[ZMod 2] Ach.t0 2 T hfin) := by
          intro e
          rw [show SSGRoute.res k K c • (e ⊗ₜ[ZMod 2] Ach.t0 2 T hfin) =
              (SSGRoute.res k K c • e) ⊗ₜ[ZMod 2] (SSGRoute.res k K c • Ach.t0 2 T hfin) from rfl,
            hTtriv rfl c (Ach.t0 2 T hfin)]
        have hmem : f c ∈ (ArchAux.onePlus (p := 2) (SSGRoute.res k K c) : E →ₗ[ZMod 2] E).range := by
          rw [Ach.mem_range_iff_forall_dual]
          intro φ hφ
          have hφ' : φ + SSGRoute.res k K c • φ = 0 := by
            ext v
            rw [LinearMap.add_apply, LinearMap.zero_apply,
              ArchAux.dualSMul_apply_of_inv_eq_self _ hσinv, ← map_add,
              ← ArchAux.onePlus_apply (p := 2) (SSGRoute.res k K c) v]
            exact hφ v
          set ψ : SSGRoute.DualMod 2 (E ⊗[ZMod 2] T) :=
            φ.comp (Ach.toE 2 E T (Ach.coord 2 T hfin)) with hψdef
          have hψinv : ∀ y : E ⊗[ZMod 2] T, ψ (SSGRoute.res k K c • y) = ψ y := by
            intro y
            show φ (Ach.toE 2 E T (Ach.coord 2 T hfin) (SSGRoute.res k K c • y)) =
              φ (Ach.toE 2 E T (Ach.coord 2 T hfin) y)
            rw [htoE rfl c y, ← ArchAux.dualSMul_apply_of_inv_eq_self _ hσinv]
            have h2 := DFunLike.congr_fun hφ' (Ach.toE 2 E T (Ach.coord 2 T hfin) y)
            rw [LinearMap.add_apply, LinearMap.zero_apply] at h2
            exact ((Ach.add_eq_zero_iff_eq_of_eq_two 2 rfl _ _).mp h2).symm
          have hψfix : ψ + SSGRoute.res k K c • ψ = 0 := by
            have hs : SSGRoute.res k K c • ψ = ψ := LinearMap.ext fun y => by
              rw [ArchAux.dualSMul_apply_of_inv_eq_self _ hσinv, hψinv y]
            rw [hs]
            exact Ach.add_self_eq_zero_of_eq_two 2 rfl ψ
          obtain ⟨g, hg1, hg2, hgc⟩ := ArchAux.exists_cocycle_locConst_conc (SSGRoute.res k K) c hc hc1
            U hUopen hUdisj ψ hψfix
          have h0 := hzero g ⟨hg1, hg2⟩
          rw [Ach.archPair_apply_of_eq_two (h := hfin) 2 (Ω ≃ₐ[k] Ω) E T rfl c f g, hgc,
            hψdef, LinearMap.comp_apply, Ach.toE_tmul, Ach.coord_t0, one_smul] at h0
          exact h0
        obtain ⟨m, hm⟩ := hmem
        refine (Ach.isCoboundaryOn_zpowers_iff (SSGRoute.res k K) c hc f).mpr ⟨hf1, m, ?_⟩
        rw [Ach.sub_eq_add_of_eq_two 2 rfl, ← hm, ArchAux.onePlus_apply, add_comm]
    · exact ArchAux.isCoboundaryOn_of_isCocycleOn_of_ne_two p hp2 (SSGRoute.res k K) c hc f hf.1
  · intro g hg hzero
    by_cases hp2 : p = 2
    · subst hp2
      obtain ⟨hg1, hgc⟩ := (Ach.isCocycleOn_zpowers_iff (SSGRoute.res k K) c hc g).mp hg.1
      by_cases hc1 : c = 1
      · refine (Ach.isCoboundaryOn_zpowers_iff (SSGRoute.res k K) c hc g).mpr ⟨hg1, 0, ?_⟩
        rw [hc1, hg1, map_one, one_smul, sub_self]
      · obtain ⟨U, hUopen, hUdisj⟩ := ArchAux.exists_isOpen_subgroup_not_mem c hc hc1
        have hψinv : ∀ y : E ⊗[ZMod 2] T, (g c) (SSGRoute.res k K c • y) = (g c) y := by
          intro y
          have h2 := DFunLike.congr_fun hgc y
          rw [LinearMap.add_apply, LinearMap.zero_apply,
            ArchAux.dualSMul_apply_of_inv_eq_self _ hσinv] at h2
          exact ((Ach.add_eq_zero_iff_eq_of_eq_two 2 rfl _ _).mp h2).symm
        have hBop : ∀ y : E ⊗[ZMod 2] T,
            ArchAux.onePlus (p := 2) (SSGRoute.res k K c) (Ach.toE 2 E T (Ach.coord 2 T hfin) y) =
              Ach.toE 2 E T (Ach.coord 2 T hfin) (ArchAux.onePlus (p := 2) (SSGRoute.res k K c) y) := by
          intro y
          rw [ArchAux.onePlus_apply, ArchAux.onePlus_apply, map_add, htoE rfl c y]
        have hker : ∀ y : E ⊗[ZMod 2] T,
            ArchAux.onePlus (p := 2) (SSGRoute.res k K c) y = 0 → (g c) y = 0 := by
          intro y hy
          obtain ⟨f, hf1, hf2, hfc⟩ := ArchAux.exists_cocycle_locConst_conc (SSGRoute.res k K) c hc hc1
            U hUopen hUdisj (Ach.toE 2 E T (Ach.coord 2 T hfin) y) (by rw [← ArchAux.onePlus_apply (p := 2) (SSGRoute.res k K c) (Ach.toE 2 E T (Ach.coord 2 T hfin) y), hBop, hy, map_zero])
          have h0 := hzero f ⟨hf1, hf2⟩
          rw [Ach.archPair_apply_of_eq_two (h := hfin) 2 (Ω ≃ₐ[k] Ω) E T rfl c f g, hfc] at h0
          rwa [hAB y] at h0
        have hmem : (g c) ∈ (ArchAux.onePlus (p := 2) (SSGRoute.res k K c) :
            (E ⊗[ZMod 2] T) →ₗ[ZMod 2] (E ⊗[ZMod 2] T)).dualMap.range := by
          rw [LinearMap.range_dualMap_eq_dualAnnihilator_ker, Submodule.mem_dualAnnihilator]
          intro y hy
          exact hker y (by simpa using hy)
        obtain ⟨ψ₀, hψ₀⟩ := hmem
        refine (Ach.isCoboundaryOn_zpowers_iff (SSGRoute.res k K) c hc g).mpr ⟨hg1, ψ₀, ?_⟩
        rw [Ach.sub_eq_add_of_eq_two 2 rfl]
        refine LinearMap.ext fun y => ?_
        rw [← hψ₀, ArchAux.onePlus_dualMap_apply, ← ArchAux.dualSMul_apply_of_inv_eq_self _ hσinv,
          LinearMap.add_apply, add_comm]
    · exact ArchAux.isCoboundaryOn_of_isCocycleOn_of_ne_two p hp2 (SSGRoute.res k K) c hc g hg.1

end Work.SSGRoute
