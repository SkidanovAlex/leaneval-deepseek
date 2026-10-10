import Mathlib.FieldTheory.KrullTopology
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.Algebra.Order.Star.Basic
import Submission.Work.SSGRoute.LevelInertiaProEll.stabilizerValuationSubringAtPrime
import Submission.Work.SSGRoute.PT.inertia_power_quotients
import Submission.Work.SSGRoute.PT.inertia_wild_exists
import Submission.Work.SSGRoute.SSGIW.levelBasic
import Submission.Work.SSGRoute.exists_level_inertiaDeg_mul_dvd
import Submission.Work.SSGRoute.mem_levelSub_iff_mem_inertia
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

open scoped Pointwise NumberField Topology

namespace Work.SSGRoute

variable (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)

/-- **A homomorphism from a pro-prime-to-`p` group into a finite `p`-group is trivial.** -/
theorem hom_eq_one_of_isProPrimeToP_of_card_dvd_pow {V H : Type*} [Group V] [Group H] [Finite H]
    (n : ℕ) (hV : Work.SSGRoute.IsProPrimeToP p V) (hcard : Nat.card H = p ^ n)
    (φ : V →* H) : φ = 1 := by
  have hp : p.Prime := Fact.out
  haveI hkfin : φ.ker.FiniteIndex := by
    rw [Subgroup.finiteIndex_iff_finite_quotient]
    exact Finite.of_equiv _ (QuotientGroup.quotientKerEquivRange φ).symm.toEquiv
  have hcop : Nat.Coprime p φ.ker.index := hV φ.ker inferInstance
  have hcard_range : Nat.card ↥φ.range = φ.ker.index := by
    rw [Subgroup.index_eq_card]
    exact Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).symm.toEquiv
  have hcop' : Nat.Coprime p (Nat.card ↥φ.range) := by rw [hcard_range]; exact hcop
  have hdvd : Nat.card ↥φ.range ∣ p ^ n := by
    rw [← hcard]
    exact Subgroup.card_subgroup_dvd_card φ.range
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow hp).mp hdvd
  have hcop_i : Nat.Coprime p (p ^ i) := by rw [← hi]; exact hcop'
  have hone : Nat.card ↥φ.range = 1 := by
    rw [hi]
    rcases Nat.eq_zero_or_pos i with h0 | hpos
    · rw [h0, pow_zero]
    · exfalso
      have hpdvd : p ∣ p ^ i := dvd_pow_self p hpos.ne'
      have h2 : p ∣ Nat.gcd p (p ^ i) := Nat.dvd_gcd dvd_rfl hpdvd
      rw [hcop_i.gcd_eq_one] at h2
      exact hp.not_dvd_one h2
  have hrange : φ.range = ⊥ := Subgroup.card_eq_one.mp hone
  ext x
  have hmem : φ x ∈ φ.range := ⟨x, rfl⟩
  rw [hrange] at hmem
  exact Subgroup.mem_bot.mp hmem

/-- **The arithmetic structure of the inertia of a finite place whose residue characteristic is not `p`** (`I = Work.SSGRoute.inertiaSub k Ω A`, `h` says `p` is a unit at `A`): there is a closed normal pro-prime-to-`p` subgroup `V ≤ ↥I` (the wild inertia) such that every finite quotient of `I` by a normal subgroup containing `V` is cyclic, and every open normal `K ≥ V` contains an open normal `L ≥ V` with `p ∣ [K : L]`. Route: describe `I` as the intersection of the level subgroups `Work.SSGRoute.levelSub A M` over the finite normal levels `M/k` (`Work.SSGRoute.mem_levelSub_iff`, `mem_levelSub_iff_mem_inertia`); at each such level the level inertia `Work.SSGRoute.levelInertiaOf` has a normal `ℓ`-subgroup `W_M` with cyclic quotient, `ℓ` the residue characteristic `≠ p` (`Work.SSGRoute.levelInertiaNormalProEll`, whose proof uses `LevelInertiaProEll.levelRingBasic`, `levelRingInertiaIdent`, `levelRingUniformizerData`, all proved); define `V` as the elements of `I` whose image in every level quotient lies in `W_M`; then `V` is closed (an intersection of preimages of subgroups under continuous restriction maps), normal, pro-prime-to-`p` (each finite quotient of `V` embeds in a product of the `ℓ`-groups `W_M`), `I/V` is pro-cyclic (a quotient of the inverse limit of the cyclic groups `I_M/W_M`), and the `p`-divisibility growth comes from `Work.SSGRoute.levelInertiaCardGrowth` together with the unboundedness of the level inertia degrees (`Work.SSGRoute.exists_level_inertiaDeg_mul_dvd`). -/
theorem zhat_inertia_wild_structure
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (h : ¬ A.valuation ((p : ℚ) : Ω) < 1) :
    ∃ V : Subgroup (↥(Work.SSGRoute.inertiaSub k Ω A)), V.Normal ∧
      IsClosed (V : Set (↥(Work.SSGRoute.inertiaSub k Ω A))) ∧
      NK.LocalTame.IsProPrimeToP p ↥V ∧
      (∀ (K : Subgroup (↥(Work.SSGRoute.inertiaSub k Ω A))) [K.Normal], V ≤ K → K.FiniteIndex →
        IsCyclic ((↥(Work.SSGRoute.inertiaSub k Ω A)) ⧸ K)) ∧
      (∀ (K : Subgroup (↥(Work.SSGRoute.inertiaSub k Ω A))) [K.Normal], V ≤ K →
        IsOpen (K : Set (↥(Work.SSGRoute.inertiaSub k Ω A))) →
        ∃ (L : Subgroup (↥(Work.SSGRoute.inertiaSub k Ω A))) (_ : L.Normal),
          V ≤ L ∧ L ≤ K ∧ IsOpen (L : Set (↥(Work.SSGRoute.inertiaSub k Ω A))) ∧
            p ∣ (L.subgroupOf K).index) := by
  -- the wild inertia `W ≤ I_A` with its properties
  obtain ⟨W, hWle, hWnorm, hWclosed, hWpro, hWcyc⟩ := PT.inertia_wild_exists (p := p) k Ω A hA h
  refine ⟨W.subgroupOf (inertiaSub k Ω A), ?_, ?_, ?_, ?_, ?_⟩
  · -- normality
    rw [Subgroup.normal_subgroupOf_iff hWle]
    intro h x hh hx
    exact hWnorm x hx h hh
  · -- closedness
    rw [Subgroup.coe_subgroupOf]
    exact hWclosed.preimage continuous_subtype_val
  · -- pro-prime-to-`p`
    have hpro : Work.SSGRoute.IsProPrimeToP p ↥(W.subgroupOf (inertiaSub k Ω A)) :=
      (NK.LocalTame.isProPrimeToP_congr (Subgroup.subgroupOfEquivOfLe hWle) p).mpr hWpro
    exact hpro
  · -- cyclic quotients
    intro K hKnorm hVK hKfi
    set U : Subgroup (Ω ≃ₐ[k] Ω) := K.map (Subgroup.subtype (inertiaSub k Ω A)) with hUdef
    have hUle : U ≤ inertiaSub k Ω A := by
      rintro x ⟨y, hy, rfl⟩
      exact y.2
    have hWU : W ≤ U := by
      have hmono : (W.subgroupOf (inertiaSub k Ω A)).map
          (Subgroup.subtype (inertiaSub k Ω A)) ≤ U := Subgroup.map_mono hVK
      have hWsub : (W.subgroupOf (inertiaSub k Ω A)).map
          (Subgroup.subtype (inertiaSub k Ω A)) = W := by
        rw [Subgroup.subgroupOf_map_subtype]
        exact inf_eq_left.mpr hWle
      rwa [hWsub] at hmono
    have hUsub : U.subgroupOf (inertiaSub k Ω A) = K := by
      ext x
      rw [Subgroup.mem_subgroupOf, hUdef, Subgroup.mem_map]
      constructor
      · rintro ⟨y, hy, hyx⟩
        have : y = x := Subtype.ext hyx
        rwa [this] at hy
      · intro hx
        exact ⟨x, hx, rfl⟩
    have hUn : (U.subgroupOf (inertiaSub k Ω A)).Normal := by rw [hUsub]; exact hKnorm
    have hUfi : (U.subgroupOf (inertiaSub k Ω A)).FiniteIndex := by rw [hUsub]; exact hKfi
    have hcyc := hWcyc U hWU hUle hUn hUfi
    have e : (↥(inertiaSub k Ω A) ⧸ U.subgroupOf (inertiaSub k Ω A)) ≃*
        (↥(inertiaSub k Ω A) ⧸ K) := QuotientGroup.quotientMulEquivOfEq hUsub
    exact isCyclic_of_surjective e e.surjective
  · -- the `p`-power growth
    intro K hKnorm hVK hKopen
    haveI hIcomp : CompactSpace ↥(inertiaSub k Ω A) := compactSpace_inertiaSub k Ω A
    haveI hKquot : Finite (↥(inertiaSub k Ω A) ⧸ K) := Subgroup.quotient_finite_of_isOpen K hKopen
    haveI hKfin : K.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
    have hKne : K.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    set n : ℕ := (Nat.log p K.index).succ with hn
    have hlt : K.index < p ^ n := by
      rw [hn]; exact Nat.lt_pow_succ_log_self (Fact.out : p.Prime).one_lt K.index
    haveI : NeZero (p ^ n) := ⟨pow_ne_zero n (Fact.out : p.Prime).ne_zero⟩
    have hcardH : Nat.card (Multiplicative (ZMod (p ^ n))) = p ^ n := by
      simp [Nat.card_eq_fintype_card, ZMod.card]
    -- an explicit level with `p ^ n ∣ |I_M|`, and the character it produces
    obtain ⟨M, hMfd, hMnm, hMnf, hMdiv⟩ := levelInertiaCardGrowth p k Ω A hA h n
    haveI := hMfd
    haveI := hMnm
    haveI := hMnf
    obtain ⟨χM, hχMsurj⟩ := PT.levelInertia_quotient p k Ω A hA h M n hMdiv
    let ρ : ↥(inertiaSub k Ω A) →* ↥(levelInertiaOf k Ω A hA M) := idxHomOf k Ω A hA M
    have hρsurj : Function.Surjective ρ := by
      intro y
      have hy : (y : ↥M ≃ₐ[k] ↥M) ∈ (inertiaSub k Ω A).map (AlgEquiv.restrictNormalHom M) := by
        rw [inertiaSub_image_eq_levelInertia k Ω A hA M]
        exact y.2
      obtain ⟨σ, hσ, hσeq⟩ := Subgroup.mem_map.mp hy
      refine ⟨⟨σ, hσ⟩, ?_⟩
      show (idxHomOf k Ω A hA M ⟨σ, hσ⟩ : ↥(levelInertiaOf k Ω A hA M)) = y
      exact Subtype.ext hσeq
    let χ : ↥(inertiaSub k Ω A) →* Multiplicative (ZMod (p ^ n)) := χM.comp ρ
    have hχsurj : Function.Surjective χ := hχMsurj.comp hρsurj
    have hχker : χ.ker.index = p ^ n := by
      rw [Subgroup.index_eq_card]
      rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective χ hχsurj).toEquiv]
      exact hcardH
    -- `χ.ker` is open: it contains the (open) fixing subgroup of the level `M`
    have hkeropen : IsOpen ((χ.ker : Subgroup ↥(inertiaSub k Ω A)) :
        Set ↥(inertiaSub k Ω A)) := by
      have hlevel : ((M.fixingSubgroup).comap (inertiaSub k Ω A).subtype :
          Subgroup ↥(inertiaSub k Ω A)) ≤ χ.ker := by
        intro x hx
        rw [MonoidHom.mem_ker]
        have hxmem : (x : Ω ≃ₐ[k] Ω) ∈ M.fixingSubgroup := hx
        have hx1 : ρ x = 1 := by
          apply Subtype.ext
          change AlgEquiv.restrictNormalHom M (x : Ω ≃ₐ[k] Ω) = 1
          exact MonoidHom.mem_ker.mp (by rwa [IntermediateField.restrictNormalHom_ker M])
        change χM (ρ x) = 1
        rw [hx1, map_one]
      have hopen : IsOpen (((M.fixingSubgroup).comap (inertiaSub k Ω A).subtype :
          Subgroup ↥(inertiaSub k Ω A)) : Set ↥(inertiaSub k Ω A)) :=
        (IntermediateField.fixingSubgroup_isOpen M).preimage continuous_subtype_val
      have h1mem : (1 : ↥(inertiaSub k Ω A)) ∈ ((M.fixingSubgroup).comap
          (inertiaSub k Ω A).subtype : Subgroup ↥(inertiaSub k Ω A)) := by
        rw [Subgroup.mem_comap]
        simp
      have hker_nhds : (χ.ker : Set ↥(inertiaSub k Ω A)) ∈ 𝓝 (1 : ↥(inertiaSub k Ω A)) :=
        Filter.mem_of_superset (hopen.mem_nhds h1mem) hlevel
      exact Subgroup.isOpen_of_mem_nhds χ.ker hker_nhds
    -- `V ≤ χ.ker`: `V` is pro-prime-to-`p`, the target a finite `p`-group
    have hVker : W.subgroupOf (inertiaSub k Ω A) ≤ χ.ker := by
      have hpro : Work.SSGRoute.IsProPrimeToP p ↥(W.subgroupOf (inertiaSub k Ω A)) :=
        (NK.LocalTame.isProPrimeToP_congr (Subgroup.subgroupOfEquivOfLe hWle) p).mpr hWpro
      have htriv : χ.comp (W.subgroupOf (inertiaSub k Ω A)).subtype = 1 :=
        hom_eq_one_of_isProPrimeToP_of_card_dvd_pow p n hpro hcardH _
      intro v hv
      have : (χ.comp (W.subgroupOf (inertiaSub k Ω A)).subtype) ⟨v, hv⟩ = 1 := by
        rw [htriv]; rfl
      simpa using this
    -- `χ` is not trivial on `K`
    have hKnontriv : ¬ (K ≤ χ.ker) := by
      intro hKle
      have hdvd : χ.ker.index ∣ K.index := Subgroup.index_dvd_of_le hKle
      rw [hχker] at hdvd
      have := Nat.le_of_dvd (Nat.pos_of_ne_zero hKne) hdvd
      exact absurd (lt_of_lt_of_le hlt this) (lt_irrefl _)
    -- `p ∣ [K : K ⊓ χ.ker]`
    set ψ : ↥K →* Multiplicative (ZMod (p ^ n)) := χ.comp K.subtype with hψdef
    have hsub : (K ⊓ χ.ker).subgroupOf K = ψ.ker := by
      rw [hψdef]
      ext x
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, MonoidHom.mem_ker]
      exact ⟨fun h => h.2, fun h => ⟨x.2, h⟩⟩
    have hidx : ((K ⊓ χ.ker).subgroupOf K).index = Nat.card ↥ψ.range := by
      rw [hsub, Subgroup.index_eq_card]
      exact Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv
    have hrange_ne : ψ.range ≠ ⊥ := by
      intro hbot
      have hKle : K ≤ χ.ker := by
        intro x hx
        have hmem : ψ ⟨x, hx⟩ ∈ ψ.range := ⟨⟨x, hx⟩, rfl⟩
        rw [hbot] at hmem
        have h1 : ψ ⟨x, hx⟩ = 1 := Subgroup.mem_bot.mp hmem
        rw [MonoidHom.mem_ker]
        simpa [hψdef] using h1
      exact hKnontriv hKle
    have hcarddvd : Nat.card ↥ψ.range ∣ p ^ n := by
      have h1 : Nat.card ↥ψ.range ∣ Nat.card (Multiplicative (ZMod (p ^ n))) :=
        Subgroup.card_subgroup_dvd_card ψ.range
      rwa [hcardH] at h1
    have hcardne : Nat.card ↥ψ.range ≠ 1 := fun h1 => hrange_ne (Subgroup.card_eq_one.mp h1)
    obtain ⟨q, hqprime, hqdiv⟩ := Nat.exists_prime_and_dvd hcardne
    have hqpn : q ∣ p ^ n := dvd_trans hqdiv hcarddvd
    have hqp : q = p := (Nat.prime_dvd_prime_iff_eq hqprime (Fact.out : p.Prime)).mp
      (hqprime.dvd_of_dvd_pow hqpn)
    have hpdiv : p ∣ Nat.card ↥ψ.range := hqp ▸ hqdiv
    haveI : χ.ker.Normal := χ.normal_ker
    refine ⟨K ⊓ χ.ker, ?_, le_inf hVK hVker, inf_le_left, hKopen.inter hkeropen, ?_⟩
    · exact ⟨fun n hn g => ⟨hKnorm.conj_mem n hn.1 g, χ.normal_ker.conj_mem n hn.2 g⟩⟩
    · rw [hidx]; exact hpdiv

end Work.SSGRoute
