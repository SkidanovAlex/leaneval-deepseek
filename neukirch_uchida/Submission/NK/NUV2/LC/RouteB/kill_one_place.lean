import Mathlib
import Submission.NK.NUV2.LC.RouteB.Defs
import Submission.NK.NUV2.LC.RouteB.res_eq_zero_of_isOpen_v2

/-!
# Route B: killing the localisation of a class at a single place

Let `G = Gal(K'/K)` be the absolute Galois group of a number field `K`, `V ≤ G` a **closed**
subgroup, `W ≤ G` an **open** subgroup with `V ≤ W`, `Y ∈ H²(W, Z/p)` and `A` a place of `K'` over a
finite prime of `K`.  This file proves

`NK.NUV2.LC.RouteB.kill_one_place`:

if the localisation of `Y` at `A` vanishes *on `V`* (`loc p V (res p hVW Y) A = 0`, i.e.
`res (V ⊓ D_A ≤ W) Y = 0` by `loc_eq_res`), then there is an open `W'` with `V ≤ W' ≤ W` such that
the localisation of `Y` at `A` vanishes on `W'` as well:

`∃ W' , V ≤ W' ∧ W' ≤ W ∧ IsOpen W' ∧ loc p W' (res p h₂ Y) A = 0`.

## The mathematical content

Write `D := D_A` for the decomposition group of `A` (closed in `G`) and let `N := Gal(K'/L₁)` be the
finite level at which `Y` is killed over `V ⊓ D` (killing criterion
`NK.NUV2.LC.OddTwist.H2Profinite_ofLevel_eq_zero_iff`).  The point is that one needs an open `W'`
with `V ≤ W'` **and** `W' ⊓ D ≤ (V ⊓ D) · N`.  The naive choice `W' = V ⊔ N` fails: the Dedekind
step `(V·N) ⊓ D ≤ (V ⊓ D)·N` is false in general.  The correct choice is `W' = V ⊔ M` where `M` is
an open normal subgroup which is *small enough*: by compactness of `G` and the descending chain
`V ⊔ M` (`M` ranging over the finite levels contained in `W`), whose intersection is `V` because `V`
is closed, one finds a single level `M` with `(V ⊔ M) ⊓ D ⊆ (V ⊓ D)·N`
(`exists_open_le_inf_le_sup_aux` below, a compactness/FIP argument in the compact group `G`).

Given such a `W'`, the level inclusion `V ⊓ D ↪ W' ⊓ D` is surjective at the level of the finite
quotients `_/(_ ⊓ N)` (it is exactly `W' ⊓ D ≤ (V ⊓ D) ⊔ N`), hence `H²(·, Z/p)`-injective there,
and the vanishing over `V ⊓ D` propagates to `W' ⊓ D`, which is `loc p W' (res p h₂ Y) A = 0`.
-/

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

open CategoryTheory
open scoped Topology

universe u

namespace NK.NUV2.LC.RouteB

/-! ## Auxiliary compactness lemmas -/

/-- **Finite intersection property, directed form.**  Let `F : ι → Set X` be a family of closed sets
of a compact space, directed downwards (`hdir`), and let `U` be an open set containing the
intersection `⋂ i, F i`.  Then a *single* member of the family is already contained in `U`.

Proof: if no `F i` were contained in `U`, the sets `F i ∩ Uᶜ` would be non-empty closed sets,
directed downwards, so by Cantor's intersection theorem
(`IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed`) their intersection would be
non-empty; but it is contained in `⋂ i, F i ⊆ U` and in `Uᶜ`. -/
lemma exists_subset_of_iInf_subset_open_aux {X : Type*} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] {ι : Type*} [Nonempty ι] {F : ι → Set X} (hF : ∀ i, IsClosed (F i))
    (hdir : ∀ i j, ∃ k, F k ⊆ F i ∩ F j) {U : Set X} (hU : IsOpen U)
    (hsub : (⋂ i, F i) ⊆ U) : ∃ i, F i ⊆ U := by
  by_contra hcon
  have hne : ∀ i, (F i ∩ (Uᶜ : Set X)).Nonempty := by
    intro i
    obtain ⟨y, hyF, hyU⟩ := Set.not_subset.mp (fun hsub_i => hcon ⟨i, hsub_i⟩)
    exact ⟨y, hyF, hyU⟩
  have hdir' : Directed (· ⊇ ·) (fun i => F i ∩ (Uᶜ : Set X)) := by
    intro i j
    obtain ⟨k, hk⟩ := hdir i j
    exact ⟨k, fun y hy => ⟨(hk hy.1).1, hy.2⟩, fun y hy => ⟨(hk hy.1).2, hy.2⟩⟩
  have hne' : (⋂ i, (F i ∩ (Uᶜ : Set X))).Nonempty :=
    IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed _
      hdir' hne (fun i => (hF i).isCompact.inter hU.isClosed_compl.isCompact)
      (fun i => (hF i).inter hU.isClosed_compl)
  obtain ⟨y, hy⟩ := hne'
  have hyU : y ∈ U := hsub (Set.mem_iInter.mpr (fun i => (Set.mem_iInter.mp hy i).1))
  exact (Set.mem_iInter.mp hy (Classical.arbitrary ι)).2 hyU

variable {K K' : Type u} [Field K] [NumberField K] [Field K'] [Algebra K K'] [IsSepClosure K K']

/-- **The compactness step of Route B.**  Let `V ≤ W ≤ Gal(K'/K)` with `V` closed and `W` open, let
`D` be a closed subgroup and `N` an open subgroup.  Then there is an open `W'` with
`V ≤ W' ≤ W` and `W' ⊓ D ≤ (V ⊓ D) ⊔ N`.

The family `V ⊔ Gal(K'/L)` over the finite Galois levels `L` contained in `W` is descending with
intersection `V` (because `V` is closed), so by the finite intersection property in the compact
group `G` some member already lies below the open subgroup `(V ⊓ D) ⊔ N` *after* intersecting
with `D`; the level in question is a genuine open subgroup of `G` (since `V ≤ W`). -/
lemma exists_open_le_inf_le_sup_aux (V W D N : Subgroup Gal(K'/K))
    (hVcl : IsClosed (V : Set Gal(K'/K))) (hVW : V ≤ W) (hW : IsOpen (W : Set Gal(K'/K)))
    (hD : IsClosed (D : Set Gal(K'/K))) (hN : IsOpen (N : Set Gal(K'/K))) :
    ∃ W' : Subgroup Gal(K'/K), V ≤ W' ∧ W' ≤ W ∧ IsOpen (W' : Set Gal(K'/K)) ∧
      W' ⊓ D ≤ (V ⊓ D) ⊔ N := by
  classical
  haveI : IsGalois K K' := IsSepClosure.isGalois
  have hfixopen : ∀ L : FiniteGaloisIntermediateField K K',
      IsOpen ((L.fixingSubgroup : Subgroup Gal(K'/K)) : Set Gal(K'/K)) :=
    fun L => IntermediateField.fixingSubgroup_isOpen (L : IntermediateField K K')
  -- the finite levels form a cofinal system of neighbourhoods of `1`
  have hB : ∀ U ∈ 𝓝 (1 : Gal(K'/K)), ∃ L : FiniteGaloisIntermediateField K K',
      (L.fixingSubgroup : Set Gal(K'/K)) ⊆ U := by
    intro U hU
    rw [krullTopology_mem_nhds_one_iff_of_normal K K'] at hU
    obtain ⟨E, hEfin, hEnorm, hEsub⟩ := hU
    refine ⟨{ toIntermediateField := E
              finiteDimensional := hEfin
              isGalois := { to_isSeparable :=
                              Algebra.IsSeparable.of_algHom K K' (IntermediateField.val E)
                            to_normal := hEnorm } }, ?_⟩
    simpa using hEsub
  -- `V` is the intersection of the open subgroups `V ⊔ Gal(K'/L)`
  have hVinf : (⨅ L : FiniteGaloisIntermediateField K K',
      (V ⊔ L.fixingSubgroup : Subgroup Gal(K'/K))) = V :=
    NK.HassePrinciple.iInf_sup_eq_of_isClosed V hVcl
      (fun L : FiniteGaloisIntermediateField K K' => L.fixingSubgroup)
      (fun L => inferInstance) hB
  -- a level contained in the open subgroup `W`
  obtain ⟨EW, hEW⟩ := hB W (hW.mem_nhds (Subgroup.one_mem W))
  set ι := {L : FiniteGaloisIntermediateField K K' // EW ≤ L} with hι
  haveI : Nonempty ι := ⟨⟨EW, le_rfl⟩⟩
  set F : ι → Set Gal(K'/K) := fun i =>
    (((V ⊔ i.1.fixingSubgroup : Subgroup Gal(K'/K)) : Set Gal(K'/K)) ∩ (D : Set Gal(K'/K)))
    with hFdef
  have hFclosed : ∀ i : ι, IsClosed (F i) := by
    intro i
    have hop : IsOpen (((V ⊔ i.1.fixingSubgroup : Subgroup Gal(K'/K)) : Set Gal(K'/K))) :=
      Subgroup.isOpen_mono (le_sup_right : (i.1.fixingSubgroup : Subgroup Gal(K'/K)) ≤
        V ⊔ i.1.fixingSubgroup) (hfixopen i.1)
    exact (Subgroup.isClosed_of_isOpen _ hop).inter hD
  have hdir : ∀ i j : ι, ∃ k : ι, F k ⊆ F i ∩ F j := by
    intro i j
    refine ⟨⟨i.1 ⊔ j.1, le_trans i.2 le_sup_left⟩, ?_⟩
    intro x hx
    refine ⟨⟨?_, hx.2⟩, ⟨?_, hx.2⟩⟩
    · exact (sup_le_sup_left (IntermediateField.fixingSubgroup_le
        (show (i.1 : IntermediateField K K') ≤ ((i.1 ⊔ j.1 : FiniteGaloisIntermediateField K K') :
          IntermediateField K K') from le_sup_left)) V) hx.1
    · exact (sup_le_sup_left (IntermediateField.fixingSubgroup_le
        (show (j.1 : IntermediateField K K') ≤ ((i.1 ⊔ j.1 : FiniteGaloisIntermediateField K K') :
          IntermediateField K K') from le_sup_right)) V) hx.1
  have hsub : (⋂ i : ι, F i) ⊆ (((V ⊓ D) ⊔ N : Subgroup Gal(K'/K)) : Set Gal(K'/K)) := by
    intro x hx
    have hxD : x ∈ D := (Set.mem_iInter.mp hx ⟨EW, le_rfl⟩).2
    have hxV : x ∈ V := by
      have hxall : x ∈ (⨅ L : FiniteGaloisIntermediateField K K',
          (V ⊔ L.fixingSubgroup : Subgroup Gal(K'/K))) := by
        rw [Subgroup.mem_iInf]
        intro L
        have hmem := Set.mem_iInter.mp hx ⟨L ⊔ EW, le_sup_right⟩
        exact (sup_le_sup_left (IntermediateField.fixingSubgroup_le
          (show (L : IntermediateField K K') ≤ ((L ⊔ EW : FiniteGaloisIntermediateField K K') :
            IntermediateField K K') from le_sup_left)) V) hmem.1
      rwa [hVinf] at hxall
    exact Subgroup.mem_sup_left (show x ∈ V ⊓ D from ⟨hxV, hxD⟩)
  have hUopen : IsOpen (((V ⊓ D) ⊔ N : Subgroup Gal(K'/K)) : Set Gal(K'/K)) :=
    Subgroup.isOpen_mono (le_sup_right : N ≤ V ⊓ D ⊔ N) hN
  obtain ⟨k, hk⟩ := exists_subset_of_iInf_subset_open_aux hFclosed hdir hUopen hsub
  refine ⟨V ⊔ k.1.fixingSubgroup, le_sup_left, ?_, ?_, hk⟩
  · exact sup_le hVW (le_trans (IntermediateField.fixingSubgroup_le k.2) hEW)
  · exact Subgroup.isOpen_mono le_sup_right (hfixopen k.1)

/-! ## The main step -/

/-- **Route B, the per-place killing step.**  Let `V ≤ W ≤ Gal(K'/K)` with `V` closed and `W` open,
`Y ∈ H²(W, Z/p)` and `A` a place of `K'` over a finite prime of `K`.  If the localisation of `Y` at
`A` vanishes on `V`, then it vanishes on an open subgroup `W'` with `V ≤ W' ≤ W`. -/
theorem kill_one_place (p : ℕ) [NeZero p] {K K' : Type} [Field K] [NumberField K] [Field K']
    [Algebra K K'] [IsSepClosure K K'] (V W : Subgroup Gal(K'/K))
    (hVcl : IsClosed (V : Set Gal(K'/K))) (hW : IsOpen (W : Set Gal(K'/K))) (hVW : V ≤ W)
    (Y : NK.BrauerHasse.H2Profinite p W) (A : NK.BrauerHasse.OverFinitePrime K K')
    (h : NK.BrauerHasse.H2Profinite.loc p V
      (NK.NUV2.LC.RouteB.res (K := K) (K' := K') p hVW Y) A = 0) :
    ∃ (W' : Subgroup Gal(K'/K)) (h1 : V ≤ W') (h2 : W' ≤ W),
      IsOpen (W' : Set Gal(K'/K)) ∧
        NK.BrauerHasse.H2Profinite.loc p W'
          (NK.NUV2.LC.RouteB.res (K := K) (K' := K') p h2 Y) A = 0 := by
  classical
  haveI : IsGalois K K' := IsSepClosure.isGalois
  -- destruct the class as a finite level class
  obtain ⟨L₀, a₀, rfl⟩ := NK.BrauerHasse.H2Profinite.ofLevel_surjective Y
  -- the hypothesis is the vanishing of the restriction to `V ⊓ D_A`
  have hv : NK.LocalDecomposition.H2Profinite.res p
      (inf_le_left.trans hVW : V ⊓ NK.BrauerHasse.stabSubgroup A.1 ≤ W)
      (NK.BrauerHasse.H2Profinite.ofLevel L₀ a₀) = 0 := by
    have h1 : NK.LocalDecomposition.H2Profinite.res p
        (inf_le_left : V ⊓ NK.BrauerHasse.stabSubgroup A.1 ≤ V)
        (NK.LocalDecomposition.H2Profinite.res p hVW
          (NK.BrauerHasse.H2Profinite.ofLevel L₀ a₀)) = 0 := by
      rw [← NK.LocalDecomposition.loc_eq_res p V A
        (NK.LocalDecomposition.H2Profinite.res p hVW
          (NK.BrauerHasse.H2Profinite.ofLevel L₀ a₀))]
      exact h
    rwa [NK.NUV2.LC.OddTwist.H2Profinite_res_comp p
      (inf_le_left : V ⊓ NK.BrauerHasse.stabSubgroup A.1 ≤ V) hVW _] at h1
  -- the killing criterion: a level `L₁` kills the class over `V ⊓ D_A`
  rw [NK.LocalDecomposition.H2Profinite.res_ofLevel] at hv
  obtain ⟨L₁, hL, hz⟩ := (NK.NUV2.LC.OddTwist.H2Profinite_ofLevel_eq_zero_iff (p := p)
    (U := V ⊓ NK.BrauerHasse.stabSubgroup A.1) _).mp hv
  rw [NK.NUV2.LC.OddTwist.levelMap_triv_levelInclHom_apply p
    (inf_le_left.trans hVW : V ⊓ NK.BrauerHasse.stabSubgroup A.1 ≤ W) hL a₀] at hz
  -- the compactness step: an open `W' ≥ V` with `W' ⊓ D_A ≤ (V ⊓ D_A) ⊔ Gal(K'/L₁)`
  obtain ⟨W', hVW', hW'W, hW'open, hkilling⟩ :=
    exists_open_le_inf_le_sup_aux V W (NK.BrauerHasse.stabSubgroup A.1) L₁.fixingSubgroup
      hVcl hVW hW (NK.LocalDecomposition.isClosed_stabSubgroup A.1)
      (IntermediateField.fixingSubgroup_isOpen (L₁ : IntermediateField K K'))
  refine ⟨W', hVW', hW'W, hW'open, ?_⟩
  -- the level inclusion `V ⊓ D_A → W' ⊓ D_A` is an isomorphism at level `L₁`, so it kills
  have h₁ : V ⊓ NK.BrauerHasse.stabSubgroup A.1 ≤ W' ⊓ NK.BrauerHasse.stabSubgroup A.1 :=
    le_inf (inf_le_left.trans hVW') inf_le_right
  have hsurj : Function.Surjective
      (NK.BrauerHasse.levelInclHom (K := K) (K' := K') h₁ L₁) :=
    levelInclHom_surjective_of_le_sup_v2 h₁ L₁ hkilling
  have hinj : ∀ x y : NK.BrauerHasse.LevelH2 p (W' ⊓ NK.BrauerHasse.stabSubgroup A.1) L₁,
      (ModuleCat.Hom.hom (NK.BrauerHasse.H2.map (p := p)
          (NK.BrauerHasse.levelInclHom (K := K) (K' := K') h₁ L₁))) x
        = (ModuleCat.Hom.hom (NK.BrauerHasse.H2.map (p := p)
          (NK.BrauerHasse.levelInclHom (K := K) (K' := K') h₁ L₁))) y → x = y :=
    fun x y hxy => NK.HassePrinciple.H2_map_injective_of_bijective
      (NK.BrauerHasse.levelInclHom (K := K) (K' := K') h₁ L₁)
      ⟨NK.HassePrinciple.levelInclHom_injective h₁ L₁, hsurj⟩ hxy
  let h₂ : W' ⊓ NK.BrauerHasse.stabSubgroup A.1 ≤ W :=
    (inf_le_left : W' ⊓ NK.BrauerHasse.stabSubgroup A.1 ≤ W').trans hW'W
  have hcomp : (ModuleCat.Hom.hom (NK.BrauerHasse.H2.map (p := p)
        (NK.BrauerHasse.levelInclHom (K := K) (K' := K')
          (inf_le_left.trans hVW : V ⊓ NK.BrauerHasse.stabSubgroup A.1 ≤ W) L₁)))
        (NK.BrauerHasse.levelMap p (U := W) hL a₀)
      = (ModuleCat.Hom.hom (NK.BrauerHasse.H2.map (p := p)
        (NK.BrauerHasse.levelInclHom (K := K) (K' := K') h₁ L₁)))
        ((ModuleCat.Hom.hom (NK.BrauerHasse.H2.map (p := p)
          (NK.BrauerHasse.levelInclHom (K := K) (K' := K') h₂ L₁)))
          (NK.BrauerHasse.levelMap p (U := W) hL a₀)) := by
    have heq : NK.BrauerHasse.levelInclHom (K := K) (K' := K')
          (inf_le_left.trans hVW : V ⊓ NK.BrauerHasse.stabSubgroup A.1 ≤ W) L₁
        = (NK.BrauerHasse.levelInclHom (K := K) (K' := K') h₂ L₁).comp
          (NK.BrauerHasse.levelInclHom (K := K) (K' := K') h₁ L₁) :=
      (congrArg (fun hh => NK.BrauerHasse.levelInclHom (K := K) (K' := K') hh L₁)
        (Subsingleton.elim _ _)).trans
        (NK.NUV2.LC.OddTwist.levelInclHom_comp p h₁ h₂ L₁).symm
    have hmap := NK.BrauerHasse.H2.map_comp (p := p)
      (f := NK.BrauerHasse.levelInclHom (K := K) (K' := K') h₂ L₁)
      (g := NK.BrauerHasse.levelInclHom (K := K) (K' := K') h₁ L₁)
    simp only [heq, hmap, ModuleCat.comp_apply]
  have hkill : (ModuleCat.Hom.hom (NK.BrauerHasse.H2.map (p := p)
        (NK.BrauerHasse.levelInclHom (K := K) (K' := K') h₂ L₁)))
        (NK.BrauerHasse.levelMap p (U := W) hL a₀) = 0 :=
    hinj _ 0 (by rw [← hcomp, hz, map_zero])
  -- consequently the restriction of `Y` to `W' ⊓ D_A` vanishes
  have hres : NK.LocalDecomposition.H2Profinite.res p h₂
      (NK.BrauerHasse.H2Profinite.ofLevel L₀ a₀) = 0 := by
    rw [NK.LocalDecomposition.H2Profinite.res_ofLevel]
    refine (NK.NUV2.LC.OddTwist.H2Profinite_ofLevel_eq_zero_iff (p := p)
      (U := W' ⊓ NK.BrauerHasse.stabSubgroup A.1) _).mpr ⟨L₁, hL, ?_⟩
    rw [NK.NUV2.LC.OddTwist.levelMap_triv_levelInclHom_apply p h₂ hL a₀]
    exact hkill
  -- and this is exactly the vanishing of the localisation on `W'`
  rw [show NK.NUV2.LC.RouteB.res (K := K) (K' := K') p hW'W
        (NK.BrauerHasse.H2Profinite.ofLevel L₀ a₀)
      = NK.LocalDecomposition.H2Profinite.res p hW'W
        (NK.BrauerHasse.H2Profinite.ofLevel L₀ a₀) from rfl]
  rw [NK.LocalDecomposition.loc_eq_res p W' A
    (NK.LocalDecomposition.H2Profinite.res p hW'W
      (NK.BrauerHasse.H2Profinite.ofLevel L₀ a₀))]
  rw [NK.NUV2.LC.OddTwist.H2Profinite_res_comp p
    (inf_le_left : W' ⊓ NK.BrauerHasse.stabSubgroup A.1 ≤ W') hW'W
    (NK.BrauerHasse.H2Profinite.ofLevel L₀ a₀)]
  exact hres

end NK.NUV2.LC.RouteB
