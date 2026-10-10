import Mathlib.FieldTheory.IsSepClosed
import Mathlib.FieldTheory.KrullTopology
import Submission.NK.Mine.exists_isHomeomorph_mulEquiv_sepClosure_of_decompositionGroup_map
import Submission.NK.TameStructureDeep.Tame.Unconditional
import Submission.Work.SSGRoute.InertiaDefs
import Submission.Work.SSGRoute.LTDDefs.Basic
import Submission.Work.SSGRoute.PTW.Prelude
import Submission.Work.SSGRoute.finite_homs_of_unique_index
import Submission.Work.SSGRoute.natCard_eq_prime_pow_of_module_zmod
import Submission.Work.SSGRoute.subgroup_eq_of_index_eq_of_isProCyclicQuotients
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped Classical

set_option linter.style.haveILetI false

namespace Work.SSGRoute

noncomputable section

/-!
# Finiteness of the open-kernel homomorphisms of the inertia subgroup

`Work.SSGRoute.finite_homs_local_inertia`: for a field `κ` whose separable closure is `K'`, a
residue characteristic `p₀` with `NK.TameData.TameInertiaInput p₀ κ K'`, a prime `l ≠ p₀` and a
finite `𝔽_l`-module `M`, there are only finitely many group homomorphisms

  `χ : ↥I →* Multiplicative M`,  `I = NK.LocalAnabelian.inertiaSubgroup p₀`,

whose kernel is open for the Krull topology on `↥I`.

## Proof

Write `V = NK.LocalTame.wildInertiaSubgroup p₀ ≤ I` for the wild inertia (a pro-`p₀` group:
`NK.LocalTame.wildInertiaSubgroup_isProP`), and `V' = V.subgroupOf I`.

1. **Every homomorphism kills `V`.**  `Nat.card M = l ^ k`
   (`natCard_eq_prime_pow_of_module_zmod`), so `Nat.card M` is coprime to `p₀`.  For any
   `ψ : ↥V →* Multiplicative M` the kernel has finite index `Nat.card ψ.range ∣ Nat.card M`,
   while the normal core is a normal finite-index subgroup of the pro-`p₀` group `↥V`, so its
   index is a `p₀`-power dividing `Nat.card M`; hence the index is `1` and `ψ = 1`
   (`hom_eq_one_of_isProP_of_coprime`).  In particular no openness is needed here.
2. **`I/V` is pro-cyclic.**  `hT.isTameInertia` states that the image of `I` in `G_κ/V` is the
   maximal closed normal pro-cyclic subgroup; the quotient `↥I ⧸ V'` is isomorphic to it
   (`QuotientGroup.quotientKerEquivRange`), so `NK.LocalTame.IsProCyclic (↥I ⧸ V')`.
3. **Finitely many homs into `M`.**  Since every hom kills `V'`, the set of homomorphisms
   `↥I →* Multiplicative M` is in bijection with `(↥I ⧸ V') →* Multiplicative M`
   (`QuotientGroup.lift`/`lift_comp_mk'`), and this is finite because in a pro-cyclic group two
   subgroups with the same nonzero index coincide
   (`subgroup_eq_of_index_eq_of_isProCyclicQuotients`), so a hom is determined by the index of
   its kernel; with the fibres finite (`finite_homs_of_unique_index`).

The openness hypothesis is not used: the statement holds for all homomorphisms.
-/

/-! ## A homomorphism from a pro-`p` group into a finite group of coprime order is trivial -/

/-- Every group homomorphism from a pro-`p` group into a finite group whose order is coprime
to `p` is trivial: its image is a finite quotient of the pro-`p` group (so has `p`-power order,
via the normal core) and a subgroup of `M` (so has order dividing `Nat.card M`). -/
theorem hom_eq_one_of_isProP_of_coprime {V M : Type*} [Group V] [Group M] [Finite M] {p : ℕ}
    (hV : NK.LocalTame.IsProP p V) (hcop : Nat.Coprime p (Nat.card M)) (ψ : V →* M) : ψ = 1 := by
  haveI hfi : ψ.ker.FiniteIndex := Subgroup.finiteIndex_ker ψ
  haveI hcore : ψ.ker.normalCore.Normal := Subgroup.normalCore_normal ψ.ker
  haveI hcfi : ψ.ker.normalCore.FiniteIndex := Subgroup.finiteIndex_normalCore ψ.ker
  obtain ⟨m, hm⟩ := hV ψ.ker.normalCore hcfi
  have hdvd : ψ.ker.index ∣ p ^ m := by
    rw [← hm]
    exact Subgroup.index_dvd_of_le (Subgroup.normalCore_le ψ.ker)
  have hdvd2 : ψ.ker.index ∣ Nat.card M := by
    rw [Subgroup.index_ker ψ]
    exact Subgroup.card_subgroup_dvd_card ψ.range
  have h1 : ψ.ker.index = 1 := by
    have hg : ψ.ker.index ∣ Nat.gcd (p ^ m) (Nat.card M) := Nat.dvd_gcd hdvd hdvd2
    rw [Nat.Coprime.gcd_eq_one (hcop.pow_left m)] at hg
    exact Nat.dvd_one.mp hg
  rw [← MonoidHom.ker_eq_top_iff, ← Subgroup.index_eq_one]
  exact h1

theorem finite_homs_local_inertia {κ K' : Type*} [Field κ] [Field K'] [Algebra κ K']
    [IsSepClosure κ K'] (p₀ : ℕ) (hT : NK.TameData.TameInertiaInput p₀ κ K')
    (l : ℕ) (hl : l.Prime) (hne : p₀ ≠ l)
    (M : Type) [AddCommGroup M] [Module (ZMod l) M] [Finite M] :
    Finite {χ : ↥(NK.LocalAnabelian.inertiaSubgroup (κ := κ) (K' := K') p₀) →* Multiplicative M //
      IsOpen (χ.ker : Set ↥(NK.LocalAnabelian.inertiaSubgroup (κ := κ) (K' := K') p₀))} := by
  classical
  haveI hgal : IsGalois κ K' := IsSepClosure.isGalois
  set V : Subgroup (Gal(K'/κ)) := NK.LocalTame.wildInertiaSubgroup (κ := κ) (K' := K') p₀
    with hVdef
  set I : Subgroup (Gal(K'/κ)) := NK.LocalAnabelian.inertiaSubgroup (κ := κ) (K' := K') p₀
    with hIdef
  haveI hVnorm : V.Normal := by
    rw [hVdef]; exact NK.LocalTame.wildInertiaSubgroup_normal p₀
  have hVI : V ≤ I := by rw [hVdef, hIdef]; exact hT.isTameInertia.1
  haveI hVsN : (V.subgroupOf I).Normal := Subgroup.Normal.comap hVnorm (Subgroup.subtype I)
  -- the cardinality of `M` is a power of `l`, hence coprime to `p₀`
  have hcop : Nat.Coprime p₀ (Nat.card M) := by
    obtain ⟨k, hk⟩ := natCard_eq_prime_pow_of_module_zmod hl M
    rw [hk]
    exact ((Nat.coprime_primes hT.hp hl).mpr hne).pow_right k
  -- Step 1: every homomorphism `↥I →* Multiplicative M` kills the wild inertia
  have hkill : ∀ χ : ↥I →* Multiplicative M, V.subgroupOf I ≤ χ.ker := by
    intro χ
    have hψ : χ.comp (Subgroup.inclusion hVI) = 1 :=
      hom_eq_one_of_isProP_of_coprime (V := ↥V) (M := Multiplicative M) (p := p₀)
        (by rw [hVdef]; exact NK.LocalTame.wildInertiaSubgroup_isProP p₀) hcop
        (χ.comp (Subgroup.inclusion hVI))
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx
    rw [MonoidHom.mem_ker]
    have hincl : (Subgroup.inclusion hVI ⟨(x : Gal(K'/κ)), hx⟩ : ↥I) = x := Subtype.ext rfl
    have h2 : χ ((Subgroup.inclusion hVI) ⟨(x : Gal(K'/κ)), hx⟩) = 1 := by
      have h3 := DFunLike.congr_fun hψ (⟨(x : Gal(K'/κ)), hx⟩ : ↥V)
      simpa using h3
    rw [← hincl]
    exact h2
  -- Step 2: `I / V` is pro-cyclic
  let f : ↥I →* Gal(K'/κ) ⧸ V := (QuotientGroup.mk' V).comp (Subgroup.subtype I)
  have hfker : f.ker = V.subgroupOf I := by
    show f.ker = V.comap (Subgroup.subtype I)
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
  have hfrange : f.range = NK.LocalTame.quotientImage V I := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rfl
  have hprocyc : NK.LocalTame.IsProCyclic (↥I ⧸ V.subgroupOf I) :=
    (NK.LocalTame.isProCyclic_congr
      ((QuotientGroup.quotientMulEquivOfEq hfker.symm).trans
        ((QuotientGroup.quotientKerEquivRange f).trans (MulEquiv.subgroupCongr hfrange)))).mpr
      hT.isTameInertia.2.2.1
  -- Step 3: finitely many homomorphisms out of the pro-cyclic quotient
  have huniq : ∀ K K' : Subgroup (↥I ⧸ V.subgroupOf I),
      K.index = K'.index → K.index ≠ 0 → K = K' :=
    fun K K' h h0 => subgroup_eq_of_index_eq_of_isProCyclicQuotients (by
      intro N hN hf
      haveI := hN
      exact hprocyc N hf) h h0
  haveI hfinQ : Finite ((↥I ⧸ V.subgroupOf I) →* Multiplicative M) :=
    finite_homs_of_unique_index (Multiplicative M) huniq
  haveI hfin : Finite {χ : ↥I →* Multiplicative M // V.subgroupOf I ≤ χ.ker} := by
    refine Finite.of_injective (fun χ => QuotientGroup.lift (V.subgroupOf I) χ.1 χ.2) ?_
    intro a b hab
    apply Subtype.ext
    have h := congrArg (fun g : (↥I ⧸ V.subgroupOf I) →* Multiplicative M =>
      g.comp (QuotientGroup.mk' (V.subgroupOf I))) hab
    simpa only [QuotientGroup.lift_comp_mk'] using h
  exact Finite.of_injective
    (fun χ : {χ : ↥I →* Multiplicative M // IsOpen (χ.ker : Set ↥I)} =>
      (⟨χ.1, hkill χ.1⟩ : {χ : ↥I →* Multiplicative M // V.subgroupOf I ≤ χ.ker}))
    (fun a b hab => Subtype.ext (by simpa using congrArg Subtype.val hab))

end

end Work.SSGRoute
