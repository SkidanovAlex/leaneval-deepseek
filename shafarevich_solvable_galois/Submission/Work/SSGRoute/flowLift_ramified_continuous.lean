import Mathlib
import Submission.Work.SSGRoute.flowLift_ramified
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

open SSGRoute
open Work.CohomologicalShrinking

set_option maxHeartbeats 1600000 in
theorem flowLift_ramified_continuous (p : ℕ) [Fact p.Prime]
    (K : IntermediateField ℚ SSGRoute.QBar)
    [FiniteDimensional ℚ K] [Normal ℚ K] (i j : ℕ) (hj : 1 ≤ j) (hji : j ≤ i)
    (hμ : SSGRoute.HasRootsOfUnity p K i) (m : ℕ)
    (φ : SSGRoute.GalQ →* Work.CohomologicalShrinking.flowGroup p (K ≃ₐ[ℚ] K) m i j)
    (hφ : SSGRoute.IsScholzSolution p K m i j φ)
    (A : ValuationSubring SSGRoute.QBar) (hfin : SSGRoute.IsFinPlace ℚ A)
    (hnT1 : ¬ SSGRoute.IsT1Place p K A)
    (hram : ∃ σ : ↥(SSGRoute.decomp ℚ A),
      SSGRoute.IsInertia ℚ A (σ : SSGRoute.GalQ) ∧ φ (σ : SSGRoute.GalQ) ≠ 1) :
    ∃ l : ↥(SSGRoute.decomp ℚ A) →* Work.CohomologicalShrinking.flowGroup p (K ≃ₐ[ℚ] K) m
          (Work.CohomologicalShrinking.tauSucc i j).1 (Work.CohomologicalShrinking.tauSucc i j).2,
      (∀ σ : ↥(SSGRoute.decomp ℚ A), SSGRoute.LiftsFlowAt (l σ) (φ σ)) ∧
      IsOpen (l.ker : Set ↥(SSGRoute.decomp ℚ A)) := by
  classical
  obtain ⟨hsurj, hopen, hres⟩ := hφ.1
  obtain ⟨hc1, hc2, hc3⟩ := hφ.2
  have hnotRam : ¬ SSGRoute.IsRamifiedIn ℚ K A := fun h => hnT1 ⟨hfin, Or.inr h⟩
  have hvalp : ¬ A.valuation (p : SSGRoute.QBar) < 1 := fun h => hnT1 ⟨hfin, Or.inl h⟩
  have hmemK : ∀ σ : SSGRoute.GalQ, SSGRoute.IsInertia ℚ A σ → σ ∈ K.fixingSubgroup :=
    fun σ hσ => by_contra (fun h => hnotRam ⟨σ, hσ, h⟩)
  obtain ⟨σ₀, hσ₀I, hσ₀ne⟩ := hram
  have hσ₀K : (σ₀ : SSGRoute.GalQ) ∈ K.fixingSubgroup := hmemK _ hσ₀I
  obtain ⟨hDfix, hcycC, himg⟩ := hc3 A hfin ⟨σ₀, hσ₀I, hσ₀K, hσ₀ne⟩
  have hres1 : ∀ x : ↥(SSGRoute.decomp ℚ A),
      AlgEquiv.restrictNormalHom K (x : SSGRoute.GalQ) = 1 := fun x =>
    @restrictNormalHom_eq_one_of_mem_fixingSubgroup ℚ SSGRoute.QBar _ _ _ K
      ‹Normal ℚ K› (x : SSGRoute.GalQ) (hDfix _ x.2)
  let Φa : ↥(SSGRoute.decomp ℚ A) →* flowGroup p (K ≃ₐ[ℚ] K) m i j :=
    φ.comp (Subgroup.subtype (SSGRoute.decomp ℚ A))
  have hrange : Φa.range = (SSGRoute.decomp ℚ A).map φ := by
    rw [show Φa = φ.comp (Subgroup.subtype (SSGRoute.decomp ℚ A)) from rfl,
      MonoidHom.range_comp, Subgroup.range_subtype]
  have hcycA : IsCyclic ↥(Φa.range) := hrange.symm ▸ hcycC
  obtain ⟨g, hggen⟩ := hcycA.exists_generator
  let c : flowGroup p (K ≃ₐ[ℚ] K) m i j := (g : flowGroup p (K ≃ₐ[ℚ] K) m i j)
  have hrange_eq : Φa.range = Subgroup.zpowers c := by
    apply le_antisymm
    · rintro x hx
      have hx' : (⟨x, hx⟩ : ↥(Φa.range)) ∈ Subgroup.zpowers g := hggen _
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hx'
      refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
      change ((g : flowGroup p (K ≃ₐ[ℚ] K) m i j)) ^ k = x
      rw [← Subgroup.coe_zpow (Φa.range) g k, hk]
    · rintro x hx
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hx
      rw [← hk]
      exact Subgroup.zpow_mem _ g.2 k
  have hc_normal : c ∈ flowNormal p (K ≃ₐ[ℚ] K) m i j := by
    have hgmem : c ∈ (SSGRoute.decomp ℚ A).map φ := hrange ▸ g.2
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hgmem
    rw [← flowQuot_ker, MonoidHom.mem_ker, ← hyx, hres y, hres1 ⟨y, hy⟩]
  have hc_pow_i : c ^ (p ^ i) = 1 := by
    have hc0 : (flowNormalEquiv p (K ≃ₐ[ℚ] K) m i j).symm ⟨c, hc_normal⟩
        ^ (p ^ i) = 1 := flowQuotient_pow_eq_one p (K ≃ₐ[ℚ] K) m i j _
    have := congrArg (fun z => (flowNormalEquiv p (K ≃ₐ[ℚ] K) m i j) z) hc0
    simp only [map_pow, map_one] at this
    simpa using this
  have hordC_dvd : orderOf c ∣ p ^ i := orderOf_dvd_iff_pow_eq_one.mpr hc_pow_i
  obtain ⟨a, ha_le, ha_eq⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).mp hordC_dvd
  have hcard : Nat.card ↥(Φa.range) = p ^ a := by
    rw [hrange_eq, Nat.card_zpowers]; exact ha_eq
  have hc_pa : c ^ (p ^ a) = 1 := by
    rw [← ha_eq]; exact pow_orderOf_eq_one c
  let e : Multiplicative (ZMod (p ^ a)) ≃* ↥(Φa.range) :=
    zmodMulEquivOfGenerator hggen hcard
  let Φa' : ↥(SSGRoute.decomp ℚ A) →* ↥(Φa.range) :=
    Φa.codRestrict (Φa.range) (fun x => ⟨x, rfl⟩)
  let χ : ↥(SSGRoute.decomp ℚ A) →* Multiplicative (ZMod (p ^ a)) :=
    e.symm.toMonoidHom.comp Φa'
  have he : ∀ k : ZMod (p ^ a),
      ((e (Multiplicative.ofAdd k) : ↥(Φa.range)) : flowGroup p (K ≃ₐ[ℚ] K) m i j)
        = c ^ k.val := by
    intro k
    have hkey : e (Multiplicative.ofAdd k) = g ^ (k.val : ℤ) := by
      conv_lhs => rw [show k = ((k.val : ℤ) : ZMod (p ^ a)) by
        rw [Int.cast_natCast, ZMod.natCast_zmod_val]]
      exact zmodMulEquivOfGenerator_apply_ofAdd_intCast hggen hcard (k.val : ℤ)
    rw [hkey]
    show ((g ^ (k.val : ℤ) : ↥(Φa.range)) : flowGroup p (K ≃ₐ[ℚ] K) m i j) = c ^ k.val
    rw [Subgroup.coe_zpow]
    show c ^ (k.val : ℤ) = c ^ k.val
    rw [zpow_natCast]
  have hΦae : ∀ x : ↥(SSGRoute.decomp ℚ A),
      ((e (χ x) : ↥(Φa.range)) : flowGroup p (K ≃ₐ[ℚ] K) m i j) = Φa x := by
    intro x
    have h2 : e (χ x) = Φa' x := by
      show e (e.symm (Φa' x)) = Φa' x
      exact Equiv.apply_symm_apply e.toEquiv (Φa' x)
    rw [h2]; rfl
  have hχopen : IsOpen (χ.ker : Set ↥(SSGRoute.decomp ℚ A)) := by
    have h1 : (χ.ker : Set ↥(SSGRoute.decomp ℚ A))
        = ((φ.comp (Subgroup.subtype (SSGRoute.decomp ℚ A))).ker :
            Set ↥(SSGRoute.decomp ℚ A)) := by
      ext x
      simp only [SetLike.mem_coe, MonoidHom.mem_ker]
      constructor
      · intro hx
        have hx' : Φa' x = 1 := e.symm.injective (by
          rw [show e.symm (Φa' x) = χ x from rfl, hx, map_one])
        exact congrArg Subtype.val hx'
      · intro hx
        show χ x = 1
        have hx' : Φa' x = 1 := Subtype.ext (show Φa x = 1 from hx)
        rw [show χ x = e.symm (Φa' x) from rfl, hx', map_one]
    rw [h1]
    exact isOpen_ker_comp_subtype φ A hopen
  have hχiner : ∀ σ : ↥(SSGRoute.decomp ℚ A),
      ∃ τ : ↥(SSGRoute.decomp ℚ A), SSGRoute.IsInertia ℚ A (τ : SSGRoute.GalQ) ∧ χ τ = χ σ := by
    intro σ
    obtain ⟨τ, hτI, hτeq⟩ := himg (σ : SSGRoute.GalQ) σ.2
    refine ⟨(⟨τ, hτI.1⟩ : ↥(SSGRoute.decomp ℚ A)), hτI, ?_⟩
    show χ (⟨τ, hτI.1⟩ : ↥(SSGRoute.decomp ℚ A)) = χ σ
    show e.symm (Φa' (⟨τ, hτI.1⟩ : ↥(SSGRoute.decomp ℚ A))) = e.symm (Φa' σ)
    rw [show Φa' (⟨τ, hτI.1⟩ : ↥(SSGRoute.decomp ℚ A)) = Φa' σ from Subtype.ext hτeq]
  have hμζ : ∃ ζ : SSGRoute.QBar, IsPrimitiveRoot ζ (p ^ (a + 1)) ∧
      ∀ σ ∈ SSGRoute.decomp ℚ A, σ ζ = ζ := by
    obtain ⟨ζ, hζmem, hζprim⟩ := hμ
    refine ⟨ζ ^ (p ^ (i - a)), ?_, ?_⟩
    · exact hζprim.pow (pow_pos (Fact.out : p.Prime).pos _)
        (by rw [← pow_add]; congr 1; omega)
    · intro σ hσ
      rw [map_pow]
      congr 1
      exact @fixingSubgroup_apply ℚ SSGRoute.QBar _ _ _ K σ (hDfix σ hσ) ζ hζmem
  obtain ⟨χ', hχ'open, hχ'iner, hχ'lift⟩ :=
    ramified_char_lift p a (Fact.out : p.Prime) A hfin hvalp hμζ χ hχopen hχiner
  -- the lift `cT` in the left factor
  let c₀ : flowQuotient p (K ≃ₐ[ℚ] K) m i j :=
    (flowNormalEquiv p (K ≃ₐ[ℚ] K) m i j).symm ⟨c, hc_normal⟩
  obtain ⟨cT0, hcT0⟩ := flowQuotSucc_surjective p (K ≃ₐ[ℚ] K) m i j c₀
  let cT : flowGroup p (K ≃ₐ[ℚ] K) m (tauSucc i j).1 (tauSucc i j).2 :=
    flowInl p (K ≃ₐ[ℚ] K) m (tauSucc i j).1 (tauSucc i j).2 cT0
  have hsucc_cT : flowGroupSucc p (K ≃ₐ[ℚ] K) m i j cT = c := by
    show flowGroupSucc p (K ≃ₐ[ℚ] K) m i j
      (flowInl p (K ≃ₐ[ℚ] K) m (tauSucc i j).1 (tauSucc i j).2 cT0) = c
    rw [flowGroupSucc, flowInl, SemidirectProduct.map_inl, hcT0]
    show flowInl p (K ≃ₐ[ℚ] K) m i j
      ((flowNormalEquiv p (K ≃ₐ[ℚ] K) m i j).symm ⟨c, hc_normal⟩) = c
    rw [← flowNormalEquiv_apply]
    rw [MulEquiv.apply_symm_apply]
  have hc₀_pa : c₀ ^ (p ^ a) = 1 := by
    have h1 : (flowNormalEquiv p (K ≃ₐ[ℚ] K) m i j) c₀ = ⟨c, hc_normal⟩ := by
      show (flowNormalEquiv p (K ≃ₐ[ℚ] K) m i j)
        ((flowNormalEquiv p (K ≃ₐ[ℚ] K) m i j).symm ⟨c, hc_normal⟩) = ⟨c, hc_normal⟩
      exact Equiv.apply_symm_apply _ _
    apply (flowNormalEquiv p (K ≃ₐ[ℚ] K) m i j).injective
    rw [map_pow, h1, map_one]
    exact Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one]; exact hc_pa)
  have hcT0_pa_mem : cT0 ^ (p ^ a) ∈ (flowQuotSucc p (K ≃ₐ[ℚ] K) m i j).ker := by
    rw [MonoidHom.mem_ker, map_pow, hcT0, hc₀_pa]
  have hcT0_pow : cT0 ^ (p ^ (a + 1)) = 1 := by
    have hk := flowQuotSucc_ker_pow p (K ≃ₐ[ℚ] K) m i j (le_trans hj hji)
      (⟨cT0 ^ (p ^ a), hcT0_pa_mem⟩ : ↥(flowQuotSucc p (K ≃ₐ[ℚ] K) m i j).ker)
    have h3 := congrArg (fun z : ↥(flowQuotSucc p (K ≃ₐ[ℚ] K) m i j).ker =>
      (z : flowQuotient p (K ≃ₐ[ℚ] K) m (tauSucc i j).1 (tauSucc i j).2)) hk
    simp only [Subgroup.coe_pow, Subgroup.coe_one] at h3
    rw [pow_succ, pow_mul]
    exact h3
  have hcT_pow : cT ^ (p ^ (a + 1)) = 1 := by
    show (flowInl p (K ≃ₐ[ℚ] K) m (tauSucc i j).1 (tauSucc i j).2 cT0) ^ (p ^ (a + 1)) = 1
    rw [← map_pow, hcT0_pow, map_one]
  have hlift : ∀ σ : ↥(SSGRoute.decomp ℚ A),
      SSGRoute.LiftsFlowAt ((zmodPowHom cT hcT_pow).comp χ' σ) (φ σ) := by
    intro σ
    rw [liftsFlowAt_iff_flowGroupSucc]
    show flowGroupSucc p (K ≃ₐ[ℚ] K) m i j ((zmodPowHom cT hcT_pow).comp χ' σ)
      = φ (σ : SSGRoute.GalQ)
    rw [MonoidHom.comp_apply, zmodPowHom_apply, map_pow, hsucc_cT]
    have hval : (Multiplicative.toAdd (χ σ)).val
        = (Multiplicative.toAdd (χ' σ)).val % p ^ a := by
      rw [hχ'lift σ, ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.val_natCast]
    have hΦ : c ^ (Multiplicative.toAdd (χ σ)).val = φ (σ : SSGRoute.GalQ) := by
      have h1 := he (Multiplicative.toAdd (χ σ))
      have h2 : Multiplicative.ofAdd (Multiplicative.toAdd (χ σ)) = χ σ :=
        Equiv.symm_apply_apply Multiplicative.toAdd (χ σ)
      rw [h2, hΦae σ] at h1
      exact h1.symm
    rw [hval] at hΦ
    rw [pow_eq_pow_of_modEq (Nat.mod_modEq (Multiplicative.toAdd (χ' σ)).val (p ^ a)) hc_pa] at hΦ
    exact hΦ
  have hker : IsOpen (((zmodPowHom cT hcT_pow).comp χ').ker :
      Set ↥(SSGRoute.decomp ℚ A)) :=
    Subgroup.isOpen_mono (H₁ := χ'.ker) (fun σ hσ => by
      rw [MonoidHom.mem_ker] at hσ ⊢
      rw [MonoidHom.comp_apply, hσ, map_one]) hχ'open
  exact ⟨_, hlift, hker⟩

end Work.SSGRoute
