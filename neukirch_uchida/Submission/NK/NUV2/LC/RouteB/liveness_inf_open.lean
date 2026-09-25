import Mathlib
import Submission.NK.NUV2.LC.RouteB.Defs
import Submission.NK.NUV2.LC.RouteB.coprime_relIndex_of_res_ne_zero
import Submission.NK.NUV2.LC.RouteB.isLive_of_isMuOpen
import Submission.NK.NUV2.LC.RouteB.res_surjective_open
import Submission.NK.NUV2.LC.RouteB.res_injective_of_coprime_index
import Submission.NK.NUV2.LC.RouteB.exists_isOpen_res_eq_zero_of_le
import Submission.NK.NUV2.LC.RouteB.exists_isOpen_subgroup_avoid
import Submission.NK.NUV2.LC.finite_support_loc_odd_of_twist

/-!
# (L3 = Loc1) Liveness passes to open subgroups

This file proves `NK.NUV2.LC.RouteB.liveness_inf_open`, the "Loc1" node of Branch L of the
non-circular route to `decompContainment_B` (see `DESIGN_containment_v3.md`).

**Proof.** Let `S := D`, `T := D' = S ⊓ N` (`N` open) and let `0 ≠ y ∈ H²(S, Z/p)`.

1. Choose an open normal `N₀ ≤ N` and put `U₁ := C' ⊓ rootFix ζ ⊓ (S ⊔ N₀)`, where `C' ⊇ S` is an
   open subgroup to which `y` lifts (`res_surjective_open`).  `U₁` is `μ`-open and contains `S`.
2. For every open `U'` with `S ≤ U' ≤ U₁`, the restriction of the lift `b' ∈ H²(O₁)`
   (`O₁ := U₁ ⊓ D_A`) to `U' ⊓ D_A` is non-zero (otherwise `y = 0`), so by (F3)
   (`coprime_relIndex_of_res_ne_zero`) the index `[O₁ : U' ⊓ D_A]` is prime to `p`.
3. `isLive_of_isMuOpen` gives `0 ≠ c ∈ H²(O₁ ⊓ N)`.  If `c` died on `T`, then by continuity (S5,
   `exists_isOpen_res_eq_zero_of_le`) it would already die on `O₁ ⊓ N ⊓ N'` for some open
   `N' ⊇ T`; compactness (S1, `exists_isOpen_subgroup_avoid`) then produces an open `U'` with
   `S ≤ U' ≤ U₁` and `U' ⊓ N ⊓ D_A ≤ N'`, so that `c` dies on `O₂' := U' ⊓ N ⊓ D_A`.
4. The index identity `[O₁ ⊓ N : O₂'] = [O₁ : U' ⊓ D_A]` (the Dedekind modular law for the normal
   subgroup `N₀ ≤ N`, compared through `Subgroup.relIndex_mul_relIndex`) makes `[O₁ ⊓ N : O₂']`
   prime to `p`; by `H2Profinite_res_injective_of_coprime_index` the restriction
   `H²(O₁ ⊓ N) → H²(O₂')` is injective, so `c = 0`, a contradiction.

Hence `H²(T, Z/p)` is non-trivial.  No Demushkin input is used.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 4000000

open scoped Pointwise

namespace NK.NUV2.LC.RouteB

universe u

variable {K K' : Type u} [Field K] [Field K'] [Algebra K K']

/-! ### Two elementary group-theoretic helpers -/

/-- **The modular law** in the form used below: for a *normal* subgroup `M ≤ N`,
`(X ⊓ N) ⊔ M = (X ⊔ M) ⊓ N`. -/
private lemma sup_inf_eq_of_normal_le {G : Type*} [Group G] (M N X : Subgroup G) [M.Normal]
    (hMN : M ≤ N) : (X ⊓ N) ⊔ M = (X ⊔ M) ⊓ N := by
  refine le_antisymm ?_ ?_
  · intro g hg
    rw [Subgroup.mem_sup_of_normal_right] at hg
    obtain ⟨y, hy, m, hm, rfl⟩ := hg
    exact ⟨mul_mem (Subgroup.mem_sup_left (Subgroup.mem_inf.mp hy).1)
        (Subgroup.mem_sup_right hm),
      mul_mem (Subgroup.mem_inf.mp hy).2 (hMN hm)⟩
  · intro g hg
    rw [Subgroup.mem_inf] at hg
    obtain ⟨hgXM, hgN⟩ := hg
    rw [Subgroup.mem_sup_of_normal_right] at hgXM
    obtain ⟨x, hxX, m, hmM, hxm⟩ := hgXM
    have hxN : x ∈ N := by
      have h1 : x = g * m⁻¹ := by rw [← hxm]; group
      rw [h1]
      exact mul_mem hgN (inv_mem (hMN hmM))
    rw [← hxm]
    exact mul_mem (Subgroup.mem_sup_left (Subgroup.mem_inf.mpr ⟨hxX, hxN⟩))
      (Subgroup.mem_sup_right hmM)

/-- **Index identity.**  Let `M ◁ G` be of finite index, `M ≤ N`, and let `O₂ ≤ O₁` be subgroups with
`O₁ ⊔ M = O₂ ⊔ M`.  Then `[(O₂ ⊓ N) : (O₁ ⊓ N)] = [O₁ : O₂]` as relative indices.

This descends the index of `O₂` in `O₁` along `N`, using that the two groups have the same
`M`-saturation (Dedekind's modular law + multiplicativity of the index). -/
private lemma relIndex_inf_eq_relIndex_of_sup_eq {G : Type*} [Group G]
    (M N O₁ O₂ : Subgroup G) [M.Normal] (hMN : M ≤ N) (h₂₁ : O₂ ≤ O₁)
    (hsup : O₁ ⊔ M = O₂ ⊔ M) (hf : M.FiniteIndex) :
    (O₂ ⊓ N).relIndex (O₁ ⊓ N) = O₂.relIndex O₁ := by
  have hMind : M.index ≠ 0 := Subgroup.finiteIndex_iff.mp hf
  have hdiv : ∀ X : Subgroup G, M.relIndex X ≠ 0 := fun X h0 =>
    hMind (Nat.eq_zero_of_zero_dvd (h0 ▸ Subgroup.relIndex_dvd_index_of_normal M X))
  have hmod : ∀ X : Subgroup G, (X ⊓ N) ⊔ M = (X ⊔ M) ⊓ N := fun X => by
    exact sup_inf_eq_of_normal_le M N X hMN
  have hsup' : (O₂ ⊓ N) ⊔ M = (O₁ ⊓ N) ⊔ M := by rw [hmod O₂, hmod O₁, hsup]
  have eB : ((O₂ ⊓ N) ⊓ M).relIndex (O₂ ⊓ N) = M.relIndex ((O₂ ⊓ N) ⊔ M) := by
    rw [inf_comm, Subgroup.inf_relIndex_right, Subgroup.relIndex_sup_right]
  have eA : ((O₁ ⊓ N) ⊓ M).relIndex (O₁ ⊓ N) = M.relIndex ((O₁ ⊓ N) ⊔ M) := by
    rw [inf_comm, Subgroup.inf_relIndex_right, Subgroup.relIndex_sup_right]
  have hm : ((O₂ ⊓ N) ⊓ M).relIndex (O₂ ⊓ N) = ((O₁ ⊓ N) ⊓ M).relIndex (O₁ ⊓ N) := by
    rw [eB, eA, hsup']
  have hm0 : ((O₂ ⊓ N) ⊓ M).relIndex (O₂ ⊓ N) ≠ 0 := by rw [eB]; exact hdiv _
  have hmul₁ : ((O₂ ⊓ N) ⊓ M).relIndex (O₂ ⊓ N) * (O₂ ⊓ N).relIndex (O₁ ⊓ N)
      = ((O₂ ⊓ N) ⊓ M).relIndex (O₁ ⊓ N) :=
    Subgroup.relIndex_mul_relIndex ((O₂ ⊓ N) ⊓ M) (O₂ ⊓ N) (O₁ ⊓ N) inf_le_left
      (inf_le_inf_right N h₂₁)
  have hmul₂ : ((O₂ ⊓ N) ⊓ M).relIndex ((O₁ ⊓ N) ⊓ M) * ((O₁ ⊓ N) ⊓ M).relIndex (O₁ ⊓ N)
      = ((O₂ ⊓ N) ⊓ M).relIndex (O₁ ⊓ N) :=
    Subgroup.relIndex_mul_relIndex ((O₂ ⊓ N) ⊓ M) ((O₁ ⊓ N) ⊓ M) (O₁ ⊓ N)
      (inf_le_inf_right M (inf_le_inf_right N h₂₁)) inf_le_left
  have hAB : (O₂ ⊓ N).relIndex (O₁ ⊓ N) = ((O₂ ⊓ N) ⊓ M).relIndex ((O₁ ⊓ N) ⊓ M) := by
    have h3 : ((O₂ ⊓ N) ⊓ M).relIndex (O₂ ⊓ N) * (O₂ ⊓ N).relIndex (O₁ ⊓ N)
        = ((O₂ ⊓ N) ⊓ M).relIndex (O₂ ⊓ N) * ((O₂ ⊓ N) ⊓ M).relIndex ((O₁ ⊓ N) ⊓ M) := by
      calc ((O₂ ⊓ N) ⊓ M).relIndex (O₂ ⊓ N) * (O₂ ⊓ N).relIndex (O₁ ⊓ N)
          = ((O₂ ⊓ N) ⊓ M).relIndex (O₁ ⊓ N) := hmul₁
        _ = ((O₂ ⊓ N) ⊓ M).relIndex ((O₁ ⊓ N) ⊓ M)
              * ((O₁ ⊓ N) ⊓ M).relIndex (O₁ ⊓ N) := hmul₂.symm
        _ = ((O₂ ⊓ N) ⊓ M).relIndex ((O₁ ⊓ N) ⊓ M)
              * ((O₂ ⊓ N) ⊓ M).relIndex (O₂ ⊓ N) := by rw [hm]
        _ = ((O₂ ⊓ N) ⊓ M).relIndex (O₂ ⊓ N)
              * ((O₂ ⊓ N) ⊓ M).relIndex ((O₁ ⊓ N) ⊓ M) := by rw [Nat.mul_comm]
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hm0) h3
  have fB : (O₂ ⊓ M).relIndex O₂ = M.relIndex (O₂ ⊔ M) := by
    rw [show O₂ ⊓ M = M ⊓ O₂ from inf_comm O₂ M, Subgroup.inf_relIndex_right,
      Subgroup.relIndex_sup_right]
  have fA : (O₁ ⊓ M).relIndex O₁ = M.relIndex (O₁ ⊔ M) := by
    rw [show O₁ ⊓ M = M ⊓ O₁ from inf_comm O₁ M, Subgroup.inf_relIndex_right,
      Subgroup.relIndex_sup_right]
  have hm' : (O₂ ⊓ M).relIndex O₂ = (O₁ ⊓ M).relIndex O₁ := by rw [fB, fA, hsup]
  have hm0' : (O₂ ⊓ M).relIndex O₂ ≠ 0 := by rw [fB]; exact hdiv _
  have hmul₁' : (O₂ ⊓ M).relIndex O₂ * O₂.relIndex O₁ = (O₂ ⊓ M).relIndex O₁ :=
    Subgroup.relIndex_mul_relIndex (O₂ ⊓ M) O₂ O₁ inf_le_left h₂₁
  have hmul₂' : (O₂ ⊓ M).relIndex (O₁ ⊓ M) * (O₁ ⊓ M).relIndex O₁ = (O₂ ⊓ M).relIndex O₁ :=
    Subgroup.relIndex_mul_relIndex (O₂ ⊓ M) (O₁ ⊓ M) O₁ (inf_le_inf_right M h₂₁) inf_le_left
  have hO' : O₂.relIndex O₁ = (O₂ ⊓ M).relIndex (O₁ ⊓ M) := by
    have h3 : (O₂ ⊓ M).relIndex O₂ * O₂.relIndex O₁
        = (O₂ ⊓ M).relIndex O₂ * ((O₂ ⊓ M).relIndex (O₁ ⊓ M)) := by
      calc (O₂ ⊓ M).relIndex O₂ * O₂.relIndex O₁
          = (O₂ ⊓ M).relIndex O₁ := hmul₁'
        _ = (O₂ ⊓ M).relIndex (O₁ ⊓ M) * (O₁ ⊓ M).relIndex O₁ := hmul₂'.symm
        _ = (O₂ ⊓ M).relIndex (O₁ ⊓ M) * (O₂ ⊓ M).relIndex O₂ := by rw [hm']
        _ = (O₂ ⊓ M).relIndex O₂ * ((O₂ ⊓ M).relIndex (O₁ ⊓ M)) := by rw [Nat.mul_comm]
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hm0') h3
  have hAeq : (O₁ ⊓ N) ⊓ M = O₁ ⊓ M := by rw [inf_assoc, inf_eq_right.mpr hMN]
  have hBeq : (O₂ ⊓ N) ⊓ M = O₂ ⊓ M := by rw [inf_assoc, inf_eq_right.mpr hMN]
  rw [hAB, hAeq, hBeq, hO']

/-- `rootFix ζ` is open for a primitive `p`-th root of unity `ζ`. -/
private lemma isOpen_rootFix (p : ℕ) (hp : p.Prime) (ζ : K') (hζ : IsPrimitiveRoot ζ p) :
    IsOpen (rootFix (K := K) (K' := K') ζ : Set Gal(K'/K)) := by
  have hint : IsIntegral K ζ :=
    IsIntegral.of_pow hp.pos (by rw [hζ.pow_eq_one]; exact isIntegral_one)
  have hfd : FiniteDimensional K ↥(IntermediateField.adjoin K ({ζ} : Set K')) := by
    simpa using IntermediateField.adjoin.finiteDimensional (K := K) hint
  simpa [rootFix] using
    IntermediateField.fixingSubgroup_isOpen (K := K) (L := K')
      (IntermediateField.adjoin K ({ζ} : Set K'))

variable [NumberField K] [IsSepClosure K K']

/-! ### The main theorem -/

/-- **Cheap alias for the heavy subterm `D_A ⊓ rootFix ζ`.**  `NK.BrauerHasse.stabSubgroup A.1`
is the `MulAction.stabilizer` of a `ValuationSubring`, and unfolding it (together with the `⊓` of
subgroups) inside a declaration was forcing a large `whnf`; stating results through this `abbrev`
lets the declaration elaborate from a constant, with the unfolding deferred to the points that
actually need it. -/
noncomputable abbrev stabRootFix (p : ℕ) (ζ : K') (A : NK.BrauerHasse.OverFinitePrime K K') :
    Subgroup Gal(K'/K) :=
  NK.BrauerHasse.stabSubgroup A.1 ⊓ NK.NUV2.LC.RouteB.rootFix (K := K) (K' := K') ζ

/-- **Cheap alias for the profinite cohomology type** `H²(D, Z/p)`, whose `Quot`-based definition is
expensive to unfold during elaboration. -/
noncomputable abbrev H2P (p : ℕ) (D : Subgroup Gal(K'/K)) : Type _ :=
  NK.BrauerHasse.H2Profinite (K := K) (K' := K') p D


/-- **(Loc1) Liveness passes to open subgroups**, for closed subgroups of a decomposition group
fixing a primitive `p`-th root of unity.  Replaces `liveness_openSubgroup_clean` /
`liveness_local_clean` (same shape plus `hp2`); proved from (F3), `isLive_of_isMuOpen`,
coprime-index injectivity and continuity, with no Demushkin input. -/
theorem liveness_inf_open (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) {K K' : Type} [Field K]
    [NumberField K] [Field K'] [Algebra K K'] [IsSepClosure K K'] (ζ : K')
    (hζ : IsPrimitiveRoot ζ p) (A : NK.BrauerHasse.OverFinitePrime K K')
    (D D' : Subgroup Gal(K'/K)) (hD : IsClosed (D : Set Gal(K'/K)))
    (hDle : D ≤ stabRootFix p ζ A)
    (hD'le : D' ≤ D)
    (hD'open : ∃ N : Subgroup Gal(K'/K), IsOpen (N : Set Gal(K'/K)) ∧ D' = D ⊓ N)
    (h : Nontrivial (H2P p D)) :
    Nontrivial (H2P p D') := by
  classical
  haveI : NeZero p := ⟨hp.ne_zero⟩
  -- ## setup
  obtain ⟨N, hNopen, hD'eq⟩ := hD'open
  set DA : Subgroup Gal(K'/K) := NK.BrauerHasse.stabSubgroup A.1 with hDAdef
  have hDDA : D ≤ DA := le_trans hDle inf_le_left
  have hDroot : D ≤ rootFix (K := K) (K' := K') ζ := le_trans hDle inf_le_right
  have hrootOpen : IsOpen (rootFix (K := K) (K' := K') ζ : Set Gal(K'/K)) :=
    isOpen_rootFix p hp ζ hζ
  -- ## 1. an open normal subgroup `M ≤ N`
  obtain ⟨M₀, hM₀le⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
    (G := Gal(K'/K)) hNopen (Subgroup.one_mem N)
  set M : Subgroup Gal(K'/K) := (M₀ : Subgroup Gal(K'/K)) with hMdef
  have hMle : M ≤ N := hM₀le
  have hMopen : IsOpen (M : Set Gal(K'/K)) := M₀.isOpen
  have hMnormal : M.Normal := M₀.isNormal'
  haveI : M.Normal := hMnormal
  have hMfin : M.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  -- ## 2. lift the non-zero class `y ∈ H²(D)` to an open subgroup `C' ⊇ D`
  obtain ⟨y, hy⟩ := exists_ne (0 : NK.BrauerHasse.H2Profinite (K := K) (K' := K') p D)
  obtain ⟨C', hC'open, hDC', -, b, hb⟩ :=
    res_surjective_open (K := K) (K' := K') p (U := ⊤) isOpen_univ le_top y
  -- ## the `μ`-open subgroup `U₁ ⊇ D`
  set U₁ : Subgroup Gal(K'/K) := C' ⊓ rootFix (K := K) (K' := K') ζ ⊓ (D ⊔ M) with hU₁def
  have hDsupOpen : IsOpen ((D ⊔ M : Subgroup Gal(K'/K)) : Set Gal(K'/K)) :=
    Subgroup.isOpen_mono le_sup_right hMopen
  have hU₁open : IsOpen (U₁ : Set Gal(K'/K)) := by
    rw [hU₁def]
    exact (hC'open.inter hrootOpen).inter hDsupOpen
  have hU₁root : U₁ ≤ rootFix (K := K) (K' := K') ζ := by
    rw [hU₁def]; exact le_trans inf_le_left inf_le_right
  have hU₁mu : IsMuOpen (K := K) (K' := K') ζ U₁ := ⟨hU₁open, hU₁root⟩
  have hDU₁ : D ≤ U₁ := by
    intro x hx
    rw [hU₁def]
    exact Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨hDC' hx, hDroot hx⟩,
      Subgroup.mem_sup_left hx⟩
  have hU₁le_sup : U₁ ≤ D ⊔ M := by rw [hU₁def]; exact inf_le_right
  have hU₁Dsup : U₁ ⊔ M = D ⊔ M := by
    have hC : D ≤ U₁ ⊔ M := le_trans hDU₁ le_sup_left
    exact le_antisymm (sup_le hU₁le_sup le_sup_right) (sup_le hC le_sup_right)
  -- ## `O₁ := U₁ ⊓ D_A` and the lifted class `b'`
  set O₁ : Subgroup Gal(K'/K) := U₁ ⊓ DA with hO₁def
  have hO₁U₁ : O₁ ≤ U₁ := inf_le_left
  have hO₁C' : O₁ ≤ C' :=
    le_trans hO₁U₁ (by rw [hU₁def]; exact le_trans inf_le_left inf_le_left)
  have hDO₁ : D ≤ O₁ := le_inf hDU₁ hDDA
  set b' : NK.BrauerHasse.H2Profinite (K := K) (K' := K') p O₁ :=
    NK.LocalDecomposition.H2Profinite.res p hO₁C' b with hb'def
  have hyb' : y = NK.LocalDecomposition.H2Profinite.res p hDO₁ b' := by
    rw [hb'def]
    rw [NK.NUV2.LC.OddTwist.H2Profinite_res_comp p hDO₁ hO₁C' b]
    rw [show (hDO₁.trans hO₁C' : D ≤ C') = hDC' from Subsingleton.elim _ _]
    exact hb.symm
  -- ## 3. (F3): the index `[O₁ : U' ⊓ D_A]` is prime to `p` for every open `U'` with `D ≤ U' ≤ U₁`
  have hF3 : ∀ (U' : Subgroup Gal(K'/K)), IsOpen (U' : Set Gal(K'/K)) → D ≤ U' → U' ≤ U₁ →
      Nat.Coprime ((U' ⊓ DA).relIndex O₁) p := by
    intro U' hU'open hDU' hU'U₁
    have h2 : U' ⊓ DA ≤ O₁ := inf_le_inf_right DA hU'U₁
    have hy' : NK.LocalDecomposition.H2Profinite.res p h2 b' ≠ 0 := by
      intro hzero
      refine hy ?_
      rw [hyb']
      have h1 : D ≤ U' ⊓ DA := le_inf hDU' hDDA
      have heq : (h1.trans h2 : D ≤ O₁) = hDO₁ := Subsingleton.elim _ _
      rw [← heq, ← NK.NUV2.LC.OddTwist.H2Profinite_res_comp p h1 h2 b', hzero]
      exact NK.NUV2.LC.OddTwist.H2Profinite_res_zero p h1
    exact coprime_relIndex_of_res_ne_zero (K := K) (K' := K') p hp hp2 ζ hζ A hU₁mu hU'open
      hU'U₁ b' hy'
  -- ## 4. a non-zero class `c` at `W := U₁ ⊓ N ⊓ D_A`
  set W : Subgroup Gal(K'/K) := U₁ ⊓ N ⊓ DA with hWdef
  have hVopen : IsOpen ((U₁ ⊓ N : Subgroup Gal(K'/K)) : Set Gal(K'/K)) := hU₁open.inter hNopen
  have hVroot : U₁ ⊓ N ≤ rootFix (K := K) (K' := K') ζ := le_trans inf_le_left hU₁root
  have hVmu : IsMuOpen (K := K) (K' := K') ζ (U₁ ⊓ N) := ⟨hVopen, hVroot⟩
  obtain ⟨c, hc⟩ := isLive_of_isMuOpen (K := K) (K' := K') p hp hp2 ζ hζ (U₁ ⊓ N) hVmu A
  -- ## the target subgroup `T = D ⊓ N ≤ W`
  have hTW : D ⊓ N ≤ W := by
    intro x hx
    rw [hWdef]
    exact Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨hDU₁ hx.1, hx.2⟩, hDDA hx.1⟩
  -- ## 5. the main contradiction
  have hres_ne : NK.LocalDecomposition.H2Profinite.res p hTW c ≠ 0 := by
    intro hzero
    -- S5: the vanishing already happens at `W ⊓ N'` for some open `N' ⊇ D ⊓ N`
    obtain ⟨N', hN'open, hD'N', hzeroN'⟩ :=
      exists_isOpen_res_eq_zero_of_le (K := K) (K' := K') p hTW c hzero
    -- S1: avoid the closed set `N \ N'` by an open `U'` with `D ≤ U' ≤ U₁`
    have hNclosed : IsClosed ((N : Subgroup Gal(K'/K)) : Set Gal(K'/K)) :=
      Subgroup.isClosed_of_isOpen N hNopen
    have hZclosed : IsClosed (((N : Subgroup Gal(K'/K)) : Set Gal(K'/K))
        \ ((N' : Subgroup Gal(K'/K)) : Set Gal(K'/K))) := hNclosed.sdiff hN'open
    have hdisj : Disjoint (D : Set Gal(K'/K))
        (((N : Subgroup Gal(K'/K)) : Set Gal(K'/K))
          \ ((N' : Subgroup Gal(K'/K)) : Set Gal(K'/K))) := by
      rw [Set.disjoint_left]
      intro g hgD hg
      exact hg.2 (hD'N' ⟨hgD, hg.1⟩)
    obtain ⟨U', hDU', hU'U₁, hU'open, hU'disj⟩ :=
      exists_isOpen_subgroup_avoid (K := K) (K' := K') hD hU₁open hDU₁ hZclosed hdisj
    have hU'N' : U' ⊓ N ≤ N' := by
      rw [Set.disjoint_left] at hU'disj
      intro g hg
      by_contra hgN'
      exact hU'disj hg.1 ⟨hg.2, hgN'⟩
    -- the vanishing class at `V' := U' ⊓ N ⊓ D_A`
    set V' : Subgroup Gal(K'/K) := U' ⊓ N ⊓ DA with hV'def
    have hV'W : V' ≤ W := by
      intro x hx
      rw [hV'def] at hx
      rw [hWdef]
      exact Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨hU'U₁ hx.1.1, hx.1.2⟩, hx.2⟩
    have hV'N' : V' ≤ N' := by
      intro x hx
      rw [hV'def] at hx
      exact hU'N' ⟨hx.1.1, hx.1.2⟩
    have hV'W' : V' ≤ W ⊓ N' := le_inf hV'W hV'N'
    have hzeroV' : NK.LocalDecomposition.H2Profinite.res p hV'W c = 0 := by
      rw [show hV'W = (hV'W'.trans (inf_le_left : W ⊓ N' ≤ W)) from Subsingleton.elim _ _]
      rw [← NK.NUV2.LC.OddTwist.H2Profinite_res_comp p hV'W' (inf_le_left : W ⊓ N' ≤ W) c]
      rw [hzeroN']
      exact NK.NUV2.LC.OddTwist.H2Profinite_res_zero p hV'W'
    -- the index `[W : V']` is `[O₁ : U' ⊓ D_A]`, hence prime to `p`
    have hU'sup : (U' ⊓ DA) ⊔ M = D ⊔ M := by
      have hA : U' ⊓ DA ≤ D ⊔ M := le_trans inf_le_left (le_trans hU'U₁ hU₁le_sup)
      have hC : D ≤ (U' ⊓ DA) ⊔ M := le_trans (le_inf hDU' hDDA) le_sup_left
      exact le_antisymm (sup_le hA le_sup_right) (sup_le hC le_sup_right)
    have hO₁sup : O₁ ⊔ M = D ⊔ M := by
      have hA : O₁ ≤ D ⊔ M := le_trans hO₁U₁ hU₁le_sup
      have hC : D ≤ O₁ ⊔ M := le_trans hDO₁ le_sup_left
      exact le_antisymm (sup_le hA le_sup_right) (sup_le hC le_sup_right)
    have hidx : V'.relIndex W = (U' ⊓ DA).relIndex O₁ := by
      have hmain := relIndex_inf_eq_relIndex_of_sup_eq (M := M) (N := N) (O₁ := O₁)
        (O₂ := U' ⊓ DA) hMle (inf_le_inf_right DA hU'U₁) (hO₁sup.trans hU'sup.symm) hMfin
      have hV'eq : (U' ⊓ DA) ⊓ N = V' := by rw [hV'def, inf_right_comm]
      have hWeq : (U₁ ⊓ DA) ⊓ N = W := by rw [hWdef, inf_right_comm]
      rw [hO₁def] at hmain
      rw [hV'eq, hWeq] at hmain
      rw [hO₁def]
      exact hmain
    have hcop : Nat.Coprime (Subgroup.index (V'.subgroupOf W)) p := by
      have h1 : Subgroup.index (V'.subgroupOf W) = V'.relIndex W := rfl
      rw [h1, hidx]
      exact hF3 U' hU'open hDU' hU'U₁
    have hinj := H2Profinite_res_injective_of_coprime_index (K := K) (K' := K') p hp hV'W hcop
    have hEq : NK.LocalDecomposition.H2Profinite.res p hV'W c
        = NK.LocalDecomposition.H2Profinite.res p hV'W
            (0 : NK.BrauerHasse.H2Profinite (K := K) (K' := K') p W) := by
      rw [hzeroV']
      exact (NK.NUV2.LC.OddTwist.H2Profinite_res_zero p hV'W).symm
    exact hc (hinj hEq)
  -- ## conclusion
  rw [hD'eq]
  exact ⟨NK.LocalDecomposition.H2Profinite.res p hTW c, 0, hres_ne⟩

end NK.NUV2.LC.RouteB
