import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.Instances.ZMod
import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Completion
import Submission.Work.SSGRoute.HSTwoRow.exists_zmodN_cocycle
import Submission.Work.SSGRoute.exists_openSubgroup_comap_le
import Submission.Work.SSGRoute.map_topologicalClosure_zpowers_subtype
import Submission.Work.SSGRoute.zhat_le_of_index

/-!
# A locally constant `1`-cocycle on `C = closure (zpowers σ)` with prescribed value at `σ`

`Work.SSGRoute.HSTwoRow.exists_lcCocycleOn_zpowers_gen_eq`: for a `𝔽_p`-module `M` with an action
of `Gal(K/k)`, a stable submodule `W ⊆ M` and `v ∈ W`, there is a locally constant `1`-cocycle `a`
on `C = closure (zpowers σ)` for the `Gal(K/k)`-action through `res k K` with `a σ = v` and
`a C ⊆ W`.

The group-theoretic input is `Work.SSGRoute.HSTwoRow.zhat_equiv_topologicalClosure_zpowers`
(`hZ` forces `C ≅ Ẑ` with `σ ↦ zhatGen`), so `C` has a continuous surjection onto `ZMod (p * d)`
(`d = orderOf (res k K σ)`) sending `σ` to `1`; the values of the cocycle are then the partial sums
`Σ_{i<m} (res k K σ)^i • v`, made well defined by `p • (Σ_{i<d} (res k K σ)^i • v) = 0`
(`exists_zmodN_cocycle`, with `N = p * d`).

`hinf` is the elementary fact that the positive power subgroups of `Ẑ` have trivial intersection.
-/

open scoped BigOperators
open Classical

namespace Work.SSGRoute.HSTwoRow

/-- The positive power subgroups `Ẑ ^ n` of `Ẑ` have trivial intersection: an element of `Ẑ`
which is an `n`-th power for every `n > 0` is `1`.  (Reduce to the vanishing of all components
`compHomZMod d hd`, using the universal property of `Ẑ`.) -/
lemma mem_powSubgroup_all_eq_one : ∀ x : NK.LocalAnabelian.Zhat,
    (∀ n : ℕ, 0 < n → x ∈ NK.TowerRank.powSubgroup n) → x = 1 := by
  intro x hx
  obtain ⟨z, hz, huniq⟩ := NK.TameStructureDeep.Degree.zhat_existsUnique_compHomZMod_eq
      (fun d _ => 1) (fun d e hd he h => by simp)
  have hx' : ∀ (d : ℕ) (hd : d ≠ 0),
      NK.TameStructureDeep.Degree.compHomZMod d hd x = 1 := by
    intro d hd
    have hmem : x ∈ (NK.TameStructureDeep.Degree.compHomZMod d hd).ker := by
      rw [NK.TameStructureDeep.Degree.ker_compHomZMod_eq_powSubgroup d hd]
      exact hx d (Nat.pos_of_ne_zero hd)
    simpa using hmem
  have h1 : ∀ (d : ℕ) (hd : d ≠ 0),
      NK.TameStructureDeep.Degree.compHomZMod d hd (1 : NK.LocalAnabelian.Zhat) = 1 :=
    fun d hd => map_one _
  rw [huniq x hx', huniq 1 h1]

/-- **A continuous homomorphism `C →* ZMod N` sending `σ` to `1`.**  The group `C` is pro-cyclic,
so the canonical continuous surjection `phiHom σ : Ẑ ↠ C` sends `zhatGen` to `σ`; `hinf` makes it
injective, hence `C ≅ Ẑ`, and composing with the `N`-th component `compHomZMod N : Ẑ →* ZMod N`
gives the required homomorphism. -/
lemma exists_cont_hom_zmod_zpowers
    (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (σ : Ω ≃ₐ[k] Ω)
    (N : ℕ) (hN : 0 < N)
    (hinf : ∀ x : NK.LocalAnabelian.Zhat,
      (∀ n : ℕ, 0 < n → x ∈ NK.TowerRank.powSubgroup n) → x = 1)
    (hZ : ∀ n : ℕ, 0 < n → ∃ f : ↥(Subgroup.topologicalClosure (Subgroup.zpowers σ)) →*
        Multiplicative (ZMod n), Function.Surjective f) :
    ∃ φ : ↥(Subgroup.topologicalClosure (Subgroup.zpowers σ)) →* Multiplicative (ZMod N),
      Continuous φ ∧ φ ⟨σ, Subgroup.le_topologicalClosure _ (Subgroup.mem_zpowers σ)⟩
        = Multiplicative.ofAdd 1 := by
  classical
  let C : Subgroup (Ω ≃ₐ[k] Ω) := Subgroup.topologicalClosure (Subgroup.zpowers σ)
  have hσC : σ ∈ C := Subgroup.le_topologicalClosure _ (Subgroup.mem_zpowers σ)
  haveI hcompC : CompactSpace ↥C :=
    isCompact_iff_compactSpace.mp
      (Subgroup.isClosed_topologicalClosure (Subgroup.zpowers σ)).isCompact
  have htop : Subgroup.topologicalClosure (Subgroup.zpowers (⟨σ, hσC⟩ : ↥C)) = ⊤ := by
    have hmap := Work.SSGRoute.map_topologicalClosure_zpowers_subtype C
        (Subgroup.isClosed_topologicalClosure _) σ hσC
    have hCeq : Subgroup.topologicalClosure (Subgroup.zpowers σ) = C := rfl
    rw [hCeq] at hmap
    have hmap2 : (Subgroup.topologicalClosure (Subgroup.zpowers (⟨σ, hσC⟩ : ↥C))).map
          (Subgroup.subtype C) = (⊤ : Subgroup ↥C).map (Subgroup.subtype C) := by
      rw [hmap, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    exact Subgroup.map_injective (f := Subgroup.subtype C) (fun a b h => Subtype.ext h) hmap2
  let χ : NK.LocalAnabelian.Zhat →* ↥C := NK.TameStructure.ProCyclic.phiHom ⟨σ, hσC⟩
  have hχc : Continuous χ := NK.TameStructure.ProCyclic.phiHom_continuous _
  have hχzg : χ NK.TowerRank.zhatGen = (⟨σ, hσC⟩ : ↥C) := by
    apply NK.TameStructure.ProCyclic.eq_of_forall_mk'_eq
    intro U
    show (QuotientGroup.mk' U.toSubgroup)
        (NK.TameStructure.ProCyclic.phiFun (⟨σ, hσC⟩ : ↥C) NK.TowerRank.zhatGen)
      = (QuotientGroup.mk' U.toSubgroup) (⟨σ, hσC⟩ : ↥C)
    rw [NK.TameStructure.ProCyclic.phiFun_spec]
    rw [show NK.TowerRank.zhatGen = NK.TameStructure.ProCyclic.intCastZhat 1 from rfl]
    rw [NK.TameStructure.ProCyclic.famHom_intCastZhat]
    simp
  have hχs : Function.Surjective χ := by
    have himg_closed : IsClosed (Set.range χ) := (isCompact_range hχc).isClosed
    have hg_mem : (⟨σ, hσC⟩ : ↥C) ∈ Set.range χ := ⟨NK.TowerRank.zhatGen, hχzg⟩
    have hsub : Subgroup.zpowers (⟨σ, hσC⟩ : ↥C) ≤ χ.range :=
      Subgroup.zpowers_le.mpr hg_mem
    have hclosed : IsClosed ((χ.range : Subgroup ↥C) : Set ↥C) := himg_closed
    have htop_le : Subgroup.topologicalClosure (Subgroup.zpowers (⟨σ, hσC⟩ : ↥C)) ≤ χ.range :=
      Subgroup.topologicalClosure_minimal _ hsub hclosed
    rw [htop] at htop_le
    intro y
    exact htop_le (Subgroup.mem_top y)
  have hker_le : ∀ n : ℕ, 0 < n → χ.ker ≤ NK.TowerRank.powSubgroup n := by
    intro n hn
    obtain ⟨f, hf⟩ := hZ n hn
    have hsurj : Function.Surjective (f.comp χ) := hf.comp hχs
    have hidx : (f.comp χ).ker.index = n := by
      haveI : NeZero n := ⟨hn.ne'⟩
      have e := QuotientGroup.quotientKerEquivOfSurjective (f.comp χ) hsurj
      rw [Subgroup.index_eq_card, Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card,
        Fintype.card_multiplicative, ZMod.card]
    have hker_eq : (f.comp χ).ker = NK.TowerRank.powSubgroup n :=
      Work.SSGRoute.eq_powSubgroup_of_index hn hidx
    intro x hx
    rw [← hker_eq]
    rw [MonoidHom.mem_ker] at hx ⊢
    rw [MonoidHom.comp_apply, hx, map_one]
  have hχinj : Function.Injective χ := by
    rw [← MonoidHom.ker_eq_bot_iff, Subgroup.eq_bot_iff_forall]
    intro x hx
    exact hinf x (fun n hn => hker_le n hn hx)
  let χe : NK.LocalAnabelian.Zhat ≃* ↥C := MulEquiv.ofBijective χ ⟨hχinj, hχs⟩
  have hχet : (χe : NK.LocalAnabelian.Zhat → ↥C) = χ := rfl
  have hχec : Continuous χe := by rw [hχet]; exact hχc
  have hχecs : Continuous χe.symm := by
    let hh : NK.LocalAnabelian.Zhat ≃ₜ ↥C :=
      Continuous.homeoOfEquivCompactToT2 (f := χe.toEquiv) hχec
    have h2 : ∀ y : ↥C, hh.symm y = χe.symm y := fun y => by
      apply χe.injective
      rw [MulEquiv.apply_symm_apply]
      have h3 : hh (hh.symm y) = y := hh.apply_symm_apply y
      rwa [show hh (hh.symm y) = χe (hh.symm y) from rfl] at h3
    exact hh.symm.continuous.congr h2
  have hsyg : χe.symm (⟨σ, hσC⟩ : ↥C) = NK.TowerRank.zhatGen := by
    have hχzg' : χe NK.TowerRank.zhatGen = (⟨σ, hσC⟩ : ↥C) := by rw [hχet]; exact hχzg
    rw [← hχzg', MulEquiv.symm_apply_apply]
  have hcont_compHomZMod : Continuous (NK.TameStructureDeep.Degree.compHomZMod N hN.ne') := by
    haveI hdisc : DiscreteTopology
        ((Multiplicative ℤ) ⧸ (NK.TameStructure.ProCyclic.mZ N hN.ne').toSubgroup) :=
      QuotientGroup.discreteTopology (N := (NK.TameStructure.ProCyclic.mZ N hN.ne').toSubgroup)
        (isOpen_discrete _)
    have h2 : Continuous (fun q : (Multiplicative ℤ) ⧸
        (NK.TameStructure.ProCyclic.mZ N hN.ne').toSubgroup =>
          NK.TameStructureDeep.Degree.zmodQuotEquiv N hN.ne' q) := continuous_of_discreteTopology
    exact show Continuous (fun z => NK.TameStructureDeep.Degree.zmodQuotEquiv N hN.ne'
        (NK.TameStructure.ProCyclic.compHom N hN.ne' z)) from
      h2.comp (NK.TameStructure.ProCyclic.compHom_cont N hN.ne')
  refine ⟨{ toFun := fun x => NK.TameStructureDeep.Degree.compHomZMod N hN.ne' (χe.symm x)
            map_one' := by simp
            map_mul' := by intro a b; simp [map_mul] }, ?_, ?_⟩
  · exact hcont_compHomZMod.comp hχecs
  · show NK.TameStructureDeep.Degree.compHomZMod N hN.ne' (χe.symm ⟨σ, hσC⟩)
      = Multiplicative.ofAdd 1
    rw [hsyg]
    exact NK.TameStructureDeep.Degree.compHomZMod_zhatGen N hN.ne'


theorem exists_lcCocycleOn_zpowers_gen_eq
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (σ : Ω ≃ₐ[k] Ω)
    (hZ : ∀ n : ℕ, 0 < n → ∃ f : ↥(Subgroup.topologicalClosure (Subgroup.zpowers σ)) →*
        Multiplicative (ZMod n), Function.Surjective f)
    (W : Submodule (ZMod p) M)
    (hW : ∀ (γ : Ω ≃ₐ[k] Ω), γ ∈ Subgroup.topologicalClosure (Subgroup.zpowers σ) →
        ∀ w : M, w ∈ W → SSGRoute.res k K γ • w ∈ W)
    (v : M) (hv : v ∈ W) :
    ∃ a : (Ω ≃ₐ[k] Ω) → M,
      SSGRoute.IsCocycleOn (SSGRoute.res k K)
        (Subgroup.topologicalClosure (Subgroup.zpowers σ)) a ∧
      SSGRoute.IsLocConstOn (Subgroup.topologicalClosure (Subgroup.zpowers σ)) a ∧
      a σ = v ∧ ∀ γ ∈ Subgroup.topologicalClosure (Subgroup.zpowers σ), a γ ∈ W := by
  classical
  let C : Subgroup (Ω ≃ₐ[k] Ω) := Subgroup.topologicalClosure (Subgroup.zpowers σ)
  have hσC : σ ∈ C := Subgroup.le_topologicalClosure _ (Subgroup.mem_zpowers σ)
  haveI hcompC : CompactSpace ↥C :=
    isCompact_iff_compactSpace.mp
      (Subgroup.isClosed_topologicalClosure (Subgroup.zpowers σ)).isCompact
  let s : K ≃ₐ[k] K := SSGRoute.res k K σ
  let d : ℕ := orderOf s
  let N : ℕ := p * d
  have hs_d : s ^ d = 1 := pow_orderOf_eq_one s
  have hN : N = p * d := rfl
  have hNne : N ≠ 0 := by
    have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
    have hd1 : 0 < d := orderOf_pos s
    have : 0 < p * d := Nat.mul_pos (by omega) hd1
    omega
  have hN2 : 1 < N := by
    have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
    have hd1 : 1 ≤ d := orderOf_pos s
    have hmul : 2 * 1 ≤ p * d := Nat.mul_le_mul hp2 hd1
    simp only [mul_one] at hmul
    omega
  haveI : NeZero N := ⟨hNne⟩
  haveI : Fact (1 < N) := ⟨hN2⟩
  obtain ⟨φ, hφc, hφσ⟩ :=
    exists_cont_hom_zmod_zpowers k Ω σ N (by omega) mem_powSubgroup_all_eq_one hZ
  obtain ⟨coc, hcoc0, hcoc1, hcoc_formula, hcoc_add⟩ :=
    exists_zmodN_cocycle p d N hN hN2 (K ≃ₐ[k] K) M s hs_d v
  let a : (Ω ≃ₐ[k] Ω) → M :=
    fun γ => if h : γ ∈ C then coc (Multiplicative.toAdd (φ ⟨γ, h⟩)) else 0
  have htop : Subgroup.topologicalClosure (Subgroup.zpowers (⟨σ, hσC⟩ : ↥C)) = ⊤ := by
    have hmap := Work.SSGRoute.map_topologicalClosure_zpowers_subtype C
        (Subgroup.isClosed_topologicalClosure _) σ hσC
    have hCeq : Subgroup.topologicalClosure (Subgroup.zpowers σ) = C := rfl
    rw [hCeq] at hmap
    have hmap2 : (Subgroup.topologicalClosure (Subgroup.zpowers (⟨σ, hσC⟩ : ↥C))).map
          (Subgroup.subtype C) = (⊤ : Subgroup ↥C).map (Subgroup.subtype C) := by
      rw [hmap, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    exact Subgroup.map_injective (f := Subgroup.subtype C) (fun a b h => Subtype.ext h) hmap2
  have hspowN : s ^ N = 1 := by
    rw [hN, mul_comm p d, pow_mul, hs_d, one_pow]
  let F : ↥C →* K ≃ₐ[k] K := (SSGRoute.res k K).comp (Subgroup.subtype C)
  have hGfin_one : s ^ (Multiplicative.toAdd (φ (1 : ↥C))).val = 1 := by
    rw [map_one, toAdd_one, ZMod.val_zero, pow_zero]
  have hGfin_mul : ∀ g h : ↥C,
      s ^ (Multiplicative.toAdd (φ (g * h))).val
        = s ^ (Multiplicative.toAdd (φ g)).val * s ^ (Multiplicative.toAdd (φ h)).val := by
    intro g h
    have h1 : (Multiplicative.toAdd (φ (g * h))).val
        = ((Multiplicative.toAdd (φ g)).val + (Multiplicative.toAdd (φ h)).val) % N := by
      rw [map_mul, toAdd_mul, ZMod.val_add]
    rw [h1, ← pow_eq_pow_mod ((Multiplicative.toAdd (φ g)).val
      + (Multiplicative.toAdd (φ h)).val) hspowN, pow_add]
  let Gfin : ↥C →* K ≃ₐ[k] K :=
    { toFun := fun g => s ^ (Multiplicative.toAdd (φ g)).val
      map_one' := hGfin_one
      map_mul' := hGfin_mul }
  let S : Subgroup ↥C :=
    { carrier := {g | F g = Gfin g}
      one_mem' := by simp
      mul_mem' := fun {a b} (ha : F a = Gfin a) (hb : F b = Gfin b) => by
        show F (a * b) = Gfin (a * b)
        rw [map_mul, map_mul, ha, hb]
      inv_mem' := fun {a} (ha : F a = Gfin a) => by
        show F a⁻¹ = Gfin a⁻¹
        rw [map_inv, map_inv, ha] }
  have hσS : (⟨σ, hσC⟩ : ↥C) ∈ S := by
    show F ⟨σ, hσC⟩ = Gfin ⟨σ, hσC⟩
    have hF : F ⟨σ, hσC⟩ = s := rfl
    have h1 : Gfin ⟨σ, hσC⟩ = s := by
      show s ^ (Multiplicative.toAdd (φ ⟨σ, hσC⟩)).val = s
      rw [hφσ, toAdd_ofAdd, ZMod.val_one N, pow_one]
    exact hF.trans h1.symm
  have hSclosed : IsClosed (S : Set ↥C) := by
    show IsClosed {g : ↥C | F g = Gfin g}
    refine isClosed_eq ?_ ?_
    · exact (InfiniteGalois.restrictNormalHom_continuous K).comp continuous_subtype_val
    · exact (continuous_of_discreteTopology (f := fun y : Multiplicative (ZMod N) =>
        s ^ (Multiplicative.toAdd y).val)).comp hφc
  have hS_top : S = ⊤ := by
    have h1 : Subgroup.topologicalClosure (Subgroup.zpowers (⟨σ, hσC⟩ : ↥C)) ≤ S :=
      Subgroup.topologicalClosure_minimal _ (Subgroup.zpowers_le.mpr hσS) hSclosed
    rw [htop] at h1
    exact top_le_iff.mp h1
  have hres : ∀ g : ↥C, SSGRoute.res k K (g : Ω ≃ₐ[k] Ω)
      = s ^ (Multiplicative.toAdd (φ g)).val := by
    intro g
    have hg : g ∈ S := by rw [hS_top]; exact Subgroup.mem_top g
    exact hg
  have hcyc : SSGRoute.IsCocycleOn (SSGRoute.res k K) C a := by
    intro g hg h hh
    have hgh : g * h ∈ C := C.mul_mem hg hh
    have hae : a (g * h) = coc (Multiplicative.toAdd (φ ⟨g * h, hgh⟩)) := by
      simp only [a]; rw [dif_pos hgh]
    have hag : a g = coc (Multiplicative.toAdd (φ ⟨g, hg⟩)) := by
      simp only [a]; rw [dif_pos hg]
    have hah : a h = coc (Multiplicative.toAdd (φ ⟨h, hh⟩)) := by
      simp only [a]; rw [dif_pos hh]
    rw [hae, hag, hah]
    have hsub2 : (⟨g * h, hgh⟩ : ↥C) = ⟨g, hg⟩ * ⟨h, hh⟩ := Subtype.ext rfl
    rw [hsub2, map_mul, toAdd_mul]
    rw [hcoc_add]
    rw [hres ⟨g, hg⟩]
  have haσ : a σ = v := by
    have hae : a σ = coc (Multiplicative.toAdd (φ ⟨σ, hσC⟩)) := by
      simp only [a]; rw [dif_pos hσC]
    rw [hae, hφσ, toAdd_ofAdd, hcoc1]
  have hmemW : ∀ γ ∈ C, a γ ∈ W := by
    intro γ hγ
    have hae : a γ = coc (Multiplicative.toAdd (φ ⟨γ, hγ⟩)) := by
      simp only [a]; rw [dif_pos hγ]
    rw [hae, hcoc_formula]
    refine Submodule.sum_mem W ?_
    intro i hi
    have hsi : s ^ i = SSGRoute.res k K (σ ^ i) := by rw [map_pow]
    rw [hsi]
    exact hW (σ ^ i) (C.pow_mem hσC i) v hv
  have hlc : SSGRoute.IsLocConstOn C a := by
    have hopen : IsOpen ((φ.ker : Subgroup ↥C) : Set ↥C) := by
      have hset : (φ.ker : Set ↥C) = φ ⁻¹' ({1} : Set (Multiplicative (ZMod N))) := by
        ext x; simp [MonoidHom.mem_ker]
      rw [hset]
      exact (isOpen_discrete _).preimage hφc
    obtain ⟨U, hUopen, hUle⟩ :=
      Work.SSGRoute.exists_openSubgroup_comap_le (K := k) (L := Ω) C φ.ker hopen
    refine ⟨U, hUopen, ?_⟩
    intro g hg u hu huC
    have hgu : g * u ∈ C := C.mul_mem hg huC
    have hker : (⟨u, huC⟩ : ↥C) ∈ φ.ker :=
      hUle (by rw [Subgroup.mem_comap]; exact hu)
    have hphi : φ ⟨g * u, hgu⟩ = φ ⟨g, hg⟩ := by
      have h1 : (⟨g * u, hgu⟩ : ↥C) = ⟨g, hg⟩ * ⟨u, huC⟩ := Subtype.ext rfl
      rw [h1, map_mul, MonoidHom.mem_ker.mp hker, mul_one]
    have hae : a (g * u) = coc (Multiplicative.toAdd (φ ⟨g * u, hgu⟩)) := by
      simp only [a]; rw [dif_pos hgu]
    have hag : a g = coc (Multiplicative.toAdd (φ ⟨g, hg⟩)) := by
      simp only [a]; rw [dif_pos hg]
    rw [hae, hag, hphi]
  exact ⟨a, hcyc, hlc, haσ, hmemW⟩


end Work.SSGRoute.HSTwoRow
