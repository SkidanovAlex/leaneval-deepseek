import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.SSGRoute.H9.lPinned_eq_kummerPinnedValue
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.NodeS37

theorem pinnedZeroImpLocalGroup {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] [IsAlgClosed Ω]
    {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    [IsSepClosure ↥K Ω]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ 2) (hζK : ζ ∈ K) (α : (↥K)ˣ)
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (hkill : ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k A σ →
      Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ α σ = 0)
    (ψ : Ω ≃ₐ[k] Ω) (hψ : ψ ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup)
    [FiniteDimensional ↥K ↥(Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := 2) α)]
    [IsGalois ↥K ↥(Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := 2) α)]
    [NumberField ↥(Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := 2) α)]
    (hpin : AlgEquiv.restrictNormalHom (F := ↥K) (K₁ := Ω)
        ↥(Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := 2) α)
        ((IntermediateField.fixingSubgroupEquiv K) ⟨ψ, (Subgroup.mem_inf.mp hψ).2⟩) =
      NK.Chebotarev.frobAtPrime (K := ↥K)
        (L := ↥(Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := 2) α))
        (Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K) A hA))
    (h0 : Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ α ψ = 0) :
    ∀ u ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup,
      Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ α u = 0 := by
  classical
  intro u hu
  -- the primitive `2`-nd root of unity inside `↥K`
  have hζ' : IsPrimitiveRoot (⟨ζ, hζK⟩ : ↥K) 2 :=
    Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ
  -- abbreviations: the Kummer level and the two elements as `↥K`-automorphisms
  set hLev := Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel (Ω := Ω) (K := K) (p := 2) α
    with hLevdef
  set ψ' : Ω ≃ₐ[↥K] Ω :=
    (IntermediateField.fixingSubgroupEquiv K) ⟨ψ, (Subgroup.mem_inf.mp hψ).2⟩ with hψ'def
  set u' : Ω ≃ₐ[↥K] Ω :=
    (IntermediateField.fixingSubgroupEquiv K) ⟨u, (Subgroup.mem_inf.mp hu).2⟩ with hu'def
  -- (i) the Kummer level is unramified over `↥K` at the prime below `A` (`hkill`)
  have hunrK : NK.HeckeL.IsUnramifiedIn (K := ↥K) (L := ↥hLev)
      (Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K) A hA) :=
    Work.SSGRoute.H9.swIsUnramifiedIn_hLevel_of_kills_inertia (p := 2) ζ hζ hζK α A hA hkill
  have h𝔮 := Work.SSGRoute.ZDataMup.OddForm.oddPrime_spec (K := K) (A := A) hA
  have hA' : _root_.SSGRoute.IsFinPlace ↥K A :=
    Work.SSGRoute.ZDataMup.OddForm.oddFinPlace (K := K) hA
  -- (ii) the Kummer level has prime degree, hence commutative Galois group, hence the chosen
  -- Frobenius is a Frobenius; `hpin` says it is the restriction of `ψ`
  have hcomm : ∀ a b : ↥hLev ≃ₐ[↥K] ↥hLev, a * b = b * a :=
    Work.SSGRoute.ZDataMup.LTRecFamHonest.hLevel_isMulCommutative (ζ := (⟨ζ, hζK⟩ : ↥K)) hζ' α
  have hfrob' : NK.Chebotarev.IsFrobAtPrime (K := ↥K) (L := ↥hLev)
      (Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K) A hA)
      ((AlgEquiv.restrictNormalHom hLev) ψ') := by
    rw [(NK.Chebotarev.isFrobAtPrime_iff_frobAtPrime_eq hcomm
      (Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K) A hA) hunrK
      ((AlgEquiv.restrictNormalHom hLev) ψ'))]
    exact hpin.symm
  -- (iii) the ramification index of the prime of the Kummer level below `A` is `1`
  have hpram : (Work.SSGRoute.levelPrime ↥K Ω A hA' hLev).asIdeal.ramificationIdx
      (NumberField.RingOfIntegers ↥K) = 1 := by
    apply hunrK
    have h := NK.ResidueFrob.primeOfLevel_liesOver (K := ↥K) (K' := Ω)
      (⟨A, hA'⟩ : NK.FrobeniusBridge.FinitePlaceOf ↥K Ω) hLev
    have hprimeOf : Submission.NeukirchUchida.primeOf A hA' =
        Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K) A hA := by
      apply Commons.RingTheory.Valuation.valuationSubringAtPrime_injective (K := ↥K)
      rw [← Submission.NeukirchUchida.primeOf_spec A hA', h𝔮]
    simp only [Work.SSGRoute.levelPrime]
    rwa [hprimeOf] at h
  -- (iv) the two elements as elements of `Gal(Ω/↥K)` are the given ones, and they lie in the
  -- `↥K`-decomposition group of `A`
  have hψ'restrict : ψ'.restrictScalars k = ψ := by
    have h1 : (IntermediateField.fixingSubgroupEquiv K)
        ⟨ψ'.restrictScalars k,
          Work.SSGRoute.H9.restrictScalars_mem_fixingSubgroup (k := k) (Ω := Ω) (K := K) ψ'⟩
        = ψ' :=
      Work.SSGRoute.H9.fixingSubgroupEquiv_restrictScalars (k := k) (Ω := Ω) (K := K) ψ'
    have h2 : (IntermediateField.fixingSubgroupEquiv K) ⟨ψ, (Subgroup.mem_inf.mp hψ).2⟩ = ψ' :=
      hψ'def.symm
    exact congrArg Subtype.val
      ((IntermediateField.fixingSubgroupEquiv K).injective (h1.trans h2.symm))
  have hu'restrict : u'.restrictScalars k = u := by
    have h1 : (IntermediateField.fixingSubgroupEquiv K)
        ⟨u'.restrictScalars k,
          Work.SSGRoute.H9.restrictScalars_mem_fixingSubgroup (k := k) (Ω := Ω) (K := K) u'⟩
        = u' :=
      Work.SSGRoute.H9.fixingSubgroupEquiv_restrictScalars (k := k) (Ω := Ω) (K := K) u'
    have h2 : (IntermediateField.fixingSubgroupEquiv K) ⟨u, (Subgroup.mem_inf.mp hu).2⟩ = u' :=
      hu'def.symm
    exact congrArg Subtype.val
      ((IntermediateField.fixingSubgroupEquiv K).injective (h1.trans h2.symm))
  have hψ'mem : ψ' ∈ _root_.SSGRoute.decomp (k := ↥K) A :=
    Work.SSGRoute.H9.mem_decomp_of_restrictScalars (k := k) (Ω := Ω) (K := K)
      (by rw [hψ'restrict]; exact (Subgroup.mem_inf.mp hψ).1)
  have hu'mem : u' ∈ _root_.SSGRoute.decomp (k := ↥K) A :=
    Work.SSGRoute.H9.mem_decomp_of_restrictScalars (k := k) (Ω := Ω) (K := K)
      (by rw [hu'restrict]; exact (Subgroup.mem_inf.mp hu).1)
  -- (v) the local group of the Kummer level is generated by the pinned `ψ`
  have hmap : Subgroup.map (AlgEquiv.restrictNormalHom hLev)
      (_root_.SSGRoute.decomp (k := ↥K) A)
      = Subgroup.zpowers ((AlgEquiv.restrictNormalHom hLev) ψ') :=
    Work.SSGRoute.ZDataTwo.map_decomp_res_eq_zpowers_of_isFrobAtPrime ↥K Ω hLev A hA'
      (Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K) A hA) h𝔮 hpram ψ' hψ'mem hfrob'
  obtain ⟨m, hm⟩ : ∃ m : ℤ, (AlgEquiv.restrictNormalHom hLev) u'
      = ((AlgEquiv.restrictNormalHom hLev) ψ') ^ m := by
    have hmem : (AlgEquiv.restrictNormalHom hLev) u' ∈
        Subgroup.map (AlgEquiv.restrictNormalHom hLev) (_root_.SSGRoute.decomp (k := ↥K) A) :=
      Subgroup.mem_map.mpr ⟨u', hu'mem, rfl⟩
    rw [hmap] at hmem
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hmem
    exact ⟨n, hn.symm⟩
  -- (vi) the `↥K`-level Kummer cochain `z := χ_α ∘ restrictScalars` is additive on the local
  -- group, and kills the kernel of the restriction to the Kummer level (Kummer faithfulness)
  have hz : ∀ g ∈ (⊥ : IntermediateField ↥K Ω).fixingSubgroup,
      ∀ h ∈ (⊥ : IntermediateField ↥K Ω).fixingSubgroup,
      (fun σ : Ω ≃ₐ[↥K] Ω =>
          Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ α (σ.restrictScalars k)) (g * h)
        = (fun σ : Ω ≃ₐ[↥K] Ω =>
            Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ α (σ.restrictScalars k)) g
          + (fun σ : Ω ≃ₐ[↥K] Ω =>
              Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ α (σ.restrictScalars k)) h := by
    intro g _ h _
    show Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ α ((g * h).restrictScalars k)
        = Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ α (g.restrictScalars k)
          + Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ α (h.restrictScalars k)
    have hmul : (g * h).restrictScalars k = g.restrictScalars k * h.restrictScalars k := by
      ext x; rfl
    rw [hmul]
    exact Work.SSGRoute.ZSplit.nodeKummerCocharZMod_add K ζ hζK hζ α (g.restrictScalars k)
      (Work.SSGRoute.H9.restrictScalars_mem_fixingSubgroup (k := k) (Ω := Ω) (K := K) g)
      (h.restrictScalars k)
      (Work.SSGRoute.H9.restrictScalars_mem_fixingSubgroup (k := k) (Ω := Ω) (K := K) h)
  have hker' : ∀ v ∈ _root_.SSGRoute.decomp (k := ↥K) A
      ⊓ (⊥ : IntermediateField ↥K Ω).fixingSubgroup,
      (AlgEquiv.restrictNormalHom hLev) v = 1 →
        (fun σ : Ω ≃ₐ[↥K] Ω =>
          Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ α (σ.restrictScalars k)) v = 0 := by
    intro v _ hv1
    show Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ α (v.restrictScalars k) = 0
    have hvK : v.restrictScalars k ∈ K.fixingSubgroup :=
      Work.SSGRoute.H9.restrictScalars_mem_fixingSubgroup (k := k) (Ω := Ω) (K := K) v
    rw [Work.SSGRoute.ZSplit.nodeKummerCocharZMod_apply (K := K) (ζ := ζ) (hζK := hζK)
      (hζ := hζ) (β := α) hvK]
    rw [Work.SSGRoute.H9.fixingSubgroupEquiv_restrictScalars (k := k) (Ω := Ω) (K := K) v]
    refine (Work.SSGRoute.ZDataMup.OddForm.odd_kummerCharZMod_eq_zero_iff_mem_fixingSubgroup
      (K := K) (p := 2) (⟨ζ, hζK⟩ : ↥K) hζ' α v).mpr ?_
    refine (IntermediateField.mem_fixingSubgroup_iff hLev v).mpr (fun x hx => ?_)
    have h := congrArg (fun (g : ↥hLev ≃ₐ[↥K] ↥hLev) => (g ⟨x, hx⟩ : Ω)) hv1
    rwa [AlgEquiv.restrictNormalHom_apply] at h
  have hψ'' : ψ' ∈ _root_.SSGRoute.decomp (k := ↥K) A
      ⊓ (⊥ : IntermediateField ↥K Ω).fixingSubgroup :=
    Subgroup.mem_inf.mpr ⟨hψ'mem, by
      rw [IntermediateField.fixingSubgroup_bot]; exact Subgroup.mem_top _⟩
  have hu'' : u' ∈ _root_.SSGRoute.decomp (k := ↥K) A
      ⊓ (⊥ : IntermediateField ↥K Ω).fixingSubgroup :=
    Subgroup.mem_inf.mpr ⟨hu'mem, by
      rw [IntermediateField.fixingSubgroup_bot]; exact Subgroup.mem_top _⟩
  -- (vii) the local value computation at the Kummer level
  have hkey := Work.SSGRoute.ZSplit.localValue_eq_zsmul_of_res_eq_zpow (k := ↥K)
    (⊥ : IntermediateField ↥K Ω) hLev A
    (fun σ : Ω ≃ₐ[↥K] Ω =>
      Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ α (σ.restrictScalars k)) hz
    ψ' hψ'' u' hu'' m hm hker'
  change Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ α (u'.restrictScalars k)
      = m • Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ α (ψ'.restrictScalars k)
    at hkey
  rw [hu'restrict, hψ'restrict, h0] at hkey
  simpa using hkey

end Work.SSGRoute.NodeS37
