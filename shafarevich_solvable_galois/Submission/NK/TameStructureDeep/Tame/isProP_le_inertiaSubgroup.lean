import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.Topology.Algebra.ClopenNhdofOne
import Mathlib.Topology.Connected.Separation
import Submission.NK.TameStructureDeep.Inertia
import Submission.NK.TameStructureDeep.Tame.WildInertiaAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Every normal pro-`p` subgroup of `G_κ` lies in the inertia subgroup

For a number field `K`, a finite place `𝔭`, `κ = K_𝔭` its `𝔭`-adic completion, `K'` a separable
closure of `κ`, `p = resCharAt 𝔭` the residue characteristic and `N ⊴ Gal(K'/κ)` a pro-`p` subgroup
in the finite-quotient sense (`NK.LocalTame.IsProP`), the conclusion is

  `N ≤ I_κ`,   `I_κ = NK.LocalAnabelian.inertiaSubgroup p` = the fixing subgroup of `κ^ur`.

Equivalently (`NK.LocalTame.wildInertiaSubgroup`): the join `W_κ` of the normal pro-`p` subgroups
of `G_κ` is contained in `I_κ`.

## The route

`W_κ = NK.LocalTame.wildInertiaSubgroup p` is *by definition* the join of the normal pro-`p`
subgroups of `G_κ`, so `N ≤ W_κ` holds for every normal pro-`p` `N`
(`NK.LocalTame.le_wildInertiaSubgroup`) and it suffices to prove `W_κ ≤ I_κ`; this is what the
main auxiliary `wildInertiaSubgroup_le_inertiaSubgroup` below does.

* `W_κ` is normal, pro-`p` (`NK.LocalTame.wildInertiaSubgroup_isProP`) and closed
  (`NK.TameStructureDeep.Support.wildInertiaSubgroup_isClosed`).
* `W_κ ∩ I_κ` is pro-`p`: it is a *closed* subgroup of the profinite group `W_κ`, hence compact,
  and every open normal subgroup `U ≤ W_κ ∩ I_κ` contains `(W_κ ∩ I_κ) ∩ V` for some open normal
  `V ◁ G_κ`; then
  `[W_κ ∩ I_κ : U] ∣ [W_κ ∩ I_κ : (W_κ ∩ I_κ) ∩ V] ∣ [W_κ : W_κ ∩ V] = p^k`,
  the second divisibility coming from `V ≤ I_κ` together with the index identity
  `[W_κ ∩ I_κ : (W_κ ∩ I_κ) ∩ V] = [(W_κ ∩ I_κ) ⊔ V : V]` and multiplicativity of `relIndex`
  along the tower `V ≤ (W_κ ∩ I_κ) ⊔ V ≤ W_κ ⊔ V`.  The bridge
  `NK.TameStructureDeep.Support.isProP_of_openNormal_index` turns "every open normal subgroup has
  `p`-power index" into the finite-quotient formulation.
* `W_κ ∩ I_κ ≤ V_κ = Gal(K'/κ^{tr})`: a pro-`p` subgroup of the inertia fixes every prime-to-`p`
  root of a uniformiser (`Tame.isProP_of_le_inertia_fixes_pow_root`), and it fixes `κ^ur` because
  it lies in `I_κ`; `Tame.mem_correctedWildInertia_of_forall` then gives membership in `V_κ`.
* Finally, if `σ ∈ W_κ \ I_κ` then faithfulness of the cyclotomic character
  (`Tame.exists_conj_notMem_correctedWildInertia`) produces `y ∈ I_κ` with
  `σ y σ⁻¹ y⁻¹ ∉ V_κ`; but `σ y σ⁻¹ y⁻¹ ∈ W_κ` (normality of `W_κ`) and `∈ I_κ` (normality of
  `I_κ`), so `W_κ ∩ I_κ ≤ V_κ` gives the contradiction.
-/

open scoped Classical
open IntermediateField

set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace NK.TameStructureDeep.Tame

noncomputable section

variable {K : Type*} [Field K] [NumberField K]
variable (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
variable {K' : Type*} [Field K'] [Algebra (𝔭.adicCompletion K) K'] [IsSepClosure (𝔭.adicCompletion K) K']

local notation "κc" => 𝔭.adicCompletion K
local notation "pc" => NK.TameStructureDeep.Tame.resCharAt 𝔭
local notation "Gc" => Gal(K'/𝔭.adicCompletion K)
local notation "Wc" => NK.LocalTame.wildInertiaSubgroup (κ := κc) (K' := K') pc
local notation "Ic" => NK.LocalAnabelian.inertiaSubgroup (κ := κc) (K' := K') pc

/-! ## `W_κ` is pro-`p` for the topology -/

/-- **The wild inertia is pro-`p` as a topological group**: every open normal subgroup of `W_κ` has
`p`-power index.  This is immediate from the finite-quotient formulation
(`NK.LocalTame.wildInertiaSubgroup_isProP`), because an open subgroup of the compact group `W_κ`
has finite index. -/
theorem wildInertiaSubgroup_isProP_topf (hp : Nat.Prime pc) :
    NK.ProfiniteP.IsProP pc ↥Wc := by
  have hWcl : IsClosed (Wc : Set Gc) :=
    NK.TameStructureDeep.Support.wildInertiaSubgroup_isClosed (κ := κc) (K' := K') pc hp
  haveI : CompactSpace ↥Wc := isCompact_iff_compactSpace.mp hWcl.isCompact
  intro U
  haveI hfi : (U : Subgroup ↥Wc).FiniteIndex := by
    rw [Subgroup.finiteIndex_iff_finite_quotient]
    exact Subgroup.quotient_finite_of_isOpen (U : Subgroup ↥Wc) U.isOpen
  exact NK.LocalTame.wildInertiaSubgroup_isProP (κ := κc) (K' := K') pc
    (U : Subgroup ↥Wc) hfi

/-! ## `W_κ ∩ I_κ` is pro-`p` -/

/-- **The intersection of the wild inertia with the inertia is pro-`p`.**

`W_κ ∩ I_κ` is closed in `G_κ` (`W_κ` is closed by
`NK.TameStructureDeep.Support.wildInertiaSubgroup_isClosed`, `I_κ` by
`NK.TameStructureDeep.inertiaSubgroup_isClosed`), hence compact, and so a profinite group.  Let
`U ≤ W_κ ∩ I_κ` be an open normal subgroup.  It contains `(W_κ ∩ I_κ) ∩ V` for some open normal
`V ◁ G_κ` (`ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one`), so
`[W_κ ∩ I_κ : U] ∣ [W_κ ∩ I_κ : (W_κ ∩ I_κ) ∩ V]`.  Writing `V_κ` for the *corrected* wild inertia,
which satisfies `V_κ ≤ I_κ` (`correctedWildInertia_le_inertia`), the second factor equals
`[(W_κ ∩ I_κ) ⊔ V : V]` (`index_subgroupOf_eq_of_normal`), and `relIndex` is multiplicative along
the tower `V ≤ (W_κ ∩ I_κ) ⊔ V ≤ W_κ ⊔ V ≤ W_κ`, so it divides
`[W_κ ⊔ V : V] = [W_κ : W_κ ∩ V] = p ^ k` (`NK.LocalTame.IsProP` of `W_κ`).

The bridge `NK.TameStructureDeep.Support.isProP_of_openNormal_index` converts "every open normal
subgroup has `p`-power index" into the finite-quotient formulation. -/
theorem isProP_inf_wildInertiaSubgroup_inertia {π : 𝔭.adicCompletionIntegers K} :
    NK.LocalTame.IsProP pc ↥(Wc ⊓ Ic) := by
  have hp : Nat.Prime pc := NK.Mine.prime_ringChar_residueField_adicCompletion 𝔭
  have hWcl : IsClosed (Wc : Set Gc) :=
    NK.TameStructureDeep.Support.wildInertiaSubgroup_isClosed (κ := κc) (K' := K') pc hp
  have hIcl : IsClosed (Ic : Set Gc) :=
    NK.TameStructureDeep.inertiaSubgroup_isClosed (κ := κc) (K' := K') pc
  have hDcl : IsClosed ((Wc ⊓ Ic : Subgroup Gc) : Set Gc) := hWcl.inter hIcl
  haveI : CompactSpace ↥(Wc ⊓ Ic) := isCompact_iff_compactSpace.mp hDcl.isCompact
  have hWpro : NK.LocalTame.IsProP pc ↥Wc :=
    NK.LocalTame.wildInertiaSubgroup_isProP (κ := κc) (K' := K') pc
  refine NK.TameStructureDeep.Support.isProP_of_openNormal_index hp ?_
  intro U
  obtain ⟨W', hW'open, hW'U⟩ := isOpen_induced_iff.mp U.isOpen
  have h1 : (1 : Gc) ∈ W' := by
    have hmem : (1 : ↥(Wc ⊓ Ic)) ∈ (Subtype.val ⁻¹' W' : Set ↥(Wc ⊓ Ic)) := by
      rw [hW'U]; exact U.one_mem
    simpa using hmem
  obtain ⟨V, hVW'⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hW'open h1
  have hVU : (V : Subgroup Gc).subgroupOf (Wc ⊓ Ic) ≤ (U : Subgroup ↥(Wc ⊓ Ic)) := by
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx
    have hx' : ((x : ↥(Wc ⊓ Ic)) : Gc) ∈ W' := hVW' hx
    have hmem : x ∈ (Subtype.val ⁻¹' W' : Set ↥(Wc ⊓ Ic)) := hx'
    rwa [hW'U] at hmem
  have hVfiG : (V : Subgroup Gc).FiniteIndex :=
    Subgroup.finiteIndex_iff_finite_quotient.mpr (Subgroup.quotient_finite_of_isOpen _ V.isOpen)
  have hVrel : (V : Subgroup Gc).relIndex Wc ∣ (V : Subgroup Gc).index :=
    Subgroup.relIndex_dvd_index_of_normal (V : Subgroup Gc) Wc
  have hrelne : (V : Subgroup Gc).relIndex Wc ≠ 0 := by
    intro h0
    rw [h0] at hVrel
    exact (Subgroup.finiteIndex_iff.mp hVfiG) (zero_dvd_iff.mp hVrel)
  have hfiW : ((V : Subgroup Gc).subgroupOf Wc).FiniteIndex :=
    Subgroup.finiteIndex_iff.mpr hrelne
  obtain ⟨k, hk⟩ := hWpro ((V : Subgroup Gc).subgroupOf Wc) hfiW
  -- the index of `U` divides `[W_κ ∩ I_κ : (W_κ ∩ I_κ) ∩ V]`, which divides `[W_κ : W_κ ∩ V]`
  have hdiv1 : (U : Subgroup ↥(Wc ⊓ Ic)).index ∣
      ((V : Subgroup Gc).subgroupOf (Wc ⊓ Ic)).index := Subgroup.index_dvd_of_le hVU
  have hVnorm : (V : Subgroup Gc).Normal := inferInstance
  -- the tower `V ≤ V ⊔ (W_κ ∩ I_κ) ≤ V ⊔ W_κ` computes `relIndex V` multiplicatively
  have htower : (V : Subgroup Gc).relIndex ((V : Subgroup Gc) ⊔ (Wc ⊓ Ic)) *
      ((V : Subgroup Gc) ⊔ (Wc ⊓ Ic)).relIndex ((V : Subgroup Gc) ⊔ Wc) =
      (V : Subgroup Gc).relIndex ((V : Subgroup Gc) ⊔ Wc) :=
    Subgroup.relIndex_mul_relIndex (V : Subgroup Gc) ((V : Subgroup Gc) ⊔ (Wc ⊓ Ic))
      ((V : Subgroup Gc) ⊔ Wc) le_sup_left (sup_le_sup_left inf_le_left (V : Subgroup Gc))
  have hdiv2 : ((V : Subgroup Gc).subgroupOf (Wc ⊓ Ic)).index ∣ pc ^ k := by
    have hA : (V : Subgroup Gc).relIndex (Wc ⊓ Ic) =
        (V : Subgroup Gc).relIndex ((V : Subgroup Gc) ⊔ (Wc ⊓ Ic)) :=
      NK.LocalTame.ProP.index_subgroupOf_eq_of_normal hVnorm
    have hB : (V : Subgroup Gc).relIndex ((V : Subgroup Gc) ⊔ Wc) =
        (V : Subgroup Gc).relIndex Wc :=
      (NK.LocalTame.ProP.index_subgroupOf_eq_of_normal hVnorm (B := Wc)).symm
    have hrelW : (V : Subgroup Gc).relIndex Wc = pc ^ k := hk
    have hmid : (V : Subgroup Gc).relIndex ((V : Subgroup Gc) ⊔ (Wc ⊓ Ic)) ∣
        (V : Subgroup Gc).relIndex ((V : Subgroup Gc) ⊔ Wc) := ⟨_, htower.symm⟩
    rw [show ((V : Subgroup Gc).subgroupOf (Wc ⊓ Ic)).index =
        (V : Subgroup Gc).relIndex (Wc ⊓ Ic) from rfl, hA]
    exact hmid.trans (dvd_of_eq (hB.trans hrelW))
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).mp (hdiv1.trans hdiv2)
  exact ⟨j, hj⟩

/-! ## `W_κ ∩ I_κ` lies in the wild inertia -/

/-- **The intersection of the wild inertia with the inertia lies in the (corrected) wild
inertia `V_κ = Gal(K'/κ^{tr})`.**

An element of `W_κ ∩ I_κ` fixes `κ^ur` because it lies in `I_κ`, and fixes every `n`-th root of a
uniformiser `π` with `p ∤ n` by the Kummer argument of
`Tame.isProP_of_le_inertia_fixes_pow_root` applied to the pro-`p` group `W_κ ∩ I_κ`
(`isProP_inf_wildInertiaSubgroup_inertia`).  These two facts are exactly the input of
`Tame.mem_correctedWildInertia_of_forall`. -/
theorem inf_wildInertiaSubgroup_inertia_le_correctedWildInertia
    {π : 𝔭.adicCompletionIntegers K} (hπ : NK.TameStructureDeep.Tame.IsUniformizerAt 𝔭 π) :
    Wc ⊓ Ic ≤ NK.TameStructureDeep.Tame.correctedWildInertia (κ := κc) (K' := K') pc
      (π : κc) := by
  have hp : Nat.Prime pc := NK.Mine.prime_ringChar_residueField_adicCompletion 𝔭
  have hDpro : NK.LocalTame.IsProP pc ↥(Wc ⊓ Ic) :=
    isProP_inf_wildInertiaSubgroup_inertia 𝔭 (π := π)
  intro x hx
  obtain ⟨_, hxI⟩ := Subgroup.mem_inf.mp hx
  refine NK.TameStructureDeep.Tame.mem_correctedWildInertia_of_forall (p := pc) hp.ne_one x ?_ ?_
  · rw [NK.LocalAnabelian.ResidueField.inertiaSubgroup_eq_fixingSubgroup_unramifiedClosure
      (κ := κc) (K' := K') pc] at hxI
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).mp hxI
  · intro n hn β hβ
    have hcop : Nat.Coprime n pc := (Nat.Prime.coprime_iff_not_dvd hp).mpr hn |>.symm
    exact NK.TameStructureDeep.Tame.isProP_of_le_inertia_fixes_pow_root 𝔭 inf_le_right hDpro
      (Nat.pos_of_ne_zero fun h0 => hn (by rw [h0]; exact dvd_zero pc)) hcop hπ hβ hx

/-! ## The wild inertia lies in the inertia -/

/-- **Every normal pro-`p` subgroup lies in the inertia**, in the join form: the wild inertia
`W_κ = ⨆ {N ◁ G_κ : N pro-`p`}` is contained in `I_κ`.

If `σ ∈ W_κ \ I_κ`, then the faithfulness of the cyclotomic character
(`Tame.exists_conj_notMem_correctedWildInertia`) gives `y ∈ I_κ` with `σ y σ⁻¹ y⁻¹ ∉ V_κ`.  On the
other hand `σ y σ⁻¹ y⁻¹ = σ * (y σ y⁻¹)⁻¹ ∈ W_κ` (normality of `W_κ`) and
`σ y σ⁻¹ y⁻¹ = (σ y σ⁻¹) * y⁻¹ ∈ I_κ` (normality of `I_κ`), so
`inf_wildInertiaSubgroup_inertia_le_correctedWildInertia` contradicts `∉ V_κ`. -/
theorem wildInertiaSubgroup_le_inertiaSubgroup
    {π : 𝔭.adicCompletionIntegers K} (hπ : NK.TameStructureDeep.Tame.IsUniformizerAt 𝔭 π) :
    Wc ≤ Ic := by
  intro σ hσ
  by_contra hσI
  obtain ⟨y, hyI, hy⟩ :=
    NK.TameStructureDeep.Tame.exists_conj_notMem_correctedWildInertia 𝔭 hπ hσI
  refine hy (inf_wildInertiaSubgroup_inertia_le_correctedWildInertia 𝔭 hπ ?_)
  have hWn := NK.LocalTame.wildInertiaSubgroup_normal (κ := κc) (K' := K') pc
  have hIn := NK.LocalAnabelian.inertiaSubgroup_normal (κ := κc) (K' := K') pc
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · have h1 : y * σ * y⁻¹ ∈ Wc := hWn.conj_mem σ hσ y
    rw [show σ * y * σ⁻¹ * y⁻¹ = σ * (y * σ * y⁻¹)⁻¹ by group]
    exact Subgroup.mul_mem _ hσ (Subgroup.inv_mem _ h1)
  · have h1 : σ * y * σ⁻¹ ∈ Ic := hIn.conj_mem y hyI σ
    rw [show σ * y * σ⁻¹ * y⁻¹ = (σ * y * σ⁻¹) * y⁻¹ by group]
    exact Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ hyI)

/-! ## The target -/

theorem isProP_le_inertiaSubgroup {K : Type*} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) {K' : Type*}
    [Field K'] [Algebra (𝔭.adicCompletion K) K'] [IsSepClosure (𝔭.adicCompletion K) K']
    {N : Subgroup (Gal(K'/𝔭.adicCompletion K))} (hN : N.Normal)
    (hNpro : NK.LocalTame.IsProP (NK.TameStructureDeep.Tame.resCharAt 𝔭) ↥N) :
    N ≤ NK.LocalAnabelian.inertiaSubgroup (κ := 𝔭.adicCompletion K) (K' := K')
      (NK.TameStructureDeep.Tame.resCharAt 𝔭) := by
  obtain ⟨π, hπ⟩ := NK.TameStructureDeep.Tame.exists_isUniformizerAt 𝔭
  exact (NK.LocalTame.le_wildInertiaSubgroup (κ := 𝔭.adicCompletion K) (K' := K')
    hN hNpro).trans (wildInertiaSubgroup_le_inertiaSubgroup 𝔭 hπ)


/-! ## Every normal pro-`p` subgroup fixes the maximal tame extension -/

/-- **Every normal pro-`p` subgroup lies in the corrected wild inertia `V_κ = Gal(K'/κ^{tr})`.**

This is the statement that `N` fixes both `κ^ur` and all prime-to-`p` roots of a uniformiser `π`,
i.e. the `N`-form of `W_κ ≤ V_κ`.  By `isProP_le_inertiaSubgroup` we have `N ≤ I_κ`, so `N` fixes
`κ^ur`, and the Kummer argument `Tame.isProP_of_le_inertia_fixes_pow_root` gives that `N` fixes
every `n`-th root of `π` with `p ∤ n`; `Tame.mem_correctedWildInertia_of_forall` combines the
two. -/
theorem isProP_le_correctedWildInertia_of_normal {N : Subgroup Gc} (hN : N.Normal)
    (hNpro : NK.LocalTame.IsProP pc ↥N) {π : 𝔭.adicCompletionIntegers K}
    (hπ : NK.TameStructureDeep.Tame.IsUniformizerAt 𝔭 π) :
    N ≤ NK.TameStructureDeep.Tame.correctedWildInertia (κ := κc) (K' := K') pc (π : κc) := by
  have hp : Nat.Prime pc := NK.Mine.prime_ringChar_residueField_adicCompletion 𝔭
  have hNI : N ≤ Ic := isProP_le_inertiaSubgroup 𝔭 hN hNpro
  intro x hx
  obtain hxI := hNI hx
  refine NK.TameStructureDeep.Tame.mem_correctedWildInertia_of_forall (p := pc) hp.ne_one x ?_ ?_
  · rw [NK.LocalAnabelian.ResidueField.inertiaSubgroup_eq_fixingSubgroup_unramifiedClosure
      (κ := κc) (K' := K') pc] at hxI
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).mp hxI
  · intro n hn β hβ
    have hcop : Nat.Coprime n pc := (Nat.Prime.coprime_iff_not_dvd hp).mpr hn |>.symm
    exact NK.TameStructureDeep.Tame.isProP_of_le_inertia_fixes_pow_root 𝔭 hNI hNpro
      (Nat.pos_of_ne_zero fun h0 => hn (by rw [h0]; exact dvd_zero pc)) hcop hπ hβ hx

end

end NK.TameStructureDeep.Tame
