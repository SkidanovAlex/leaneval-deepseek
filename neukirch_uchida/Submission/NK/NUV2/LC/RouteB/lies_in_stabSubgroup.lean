import Mathlib
import Submission.NK.NUV2.LC.RouteB.Defs
import Submission.NK.NUV2.LC.RouteB.card_open_local
import Submission.NK.NUV2.LC.RouteB.conjTransportP
import Submission.NK.NUV2.LC.RouteB.exists_loc_ne_zero_of_isClosed
import Submission.NK.NUV2.LC.RouteB.card_h2P_of_open_le_localType
import Submission.NK.NUV2.LC.RouteB.liveness_inf_open
import Submission.NK.NUV2.LC.RouteB.onePlaceAssembly
import Submission.NK.NUV2.LC.RouteB.onePlaceClassesHasse
import Submission.NK.NUV2.LC.RouteB.hasseSurj_of_top
import Submission.NK.NUV2.LC.RouteB.live_places_one_orbit_of_hasseSurj

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open scoped Pointwise

open NK.BrauerHasse (stabSubgroup)

namespace NK.NUV2.LC.RouteB

universe u

variable {K K' : Type u} [Field K] [NumberField K] [Field K'] [Algebra K K'] [IsSepClosure K K']

/-! ## The liveness transfer, from the clean local input -/

/-- **Route B, (L3'): liveness passes to an open subgroup of a decomposition-group subgroup** —
the instantiation of the Branch-L liveness descent `NK.NUV2.LC.RouteB.liveness_inf_open`
(design `DESIGN_containment_v3.md`, L3). -/
theorem liveness_openSubgroup_clean (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) {K K' : Type} [Field K]
    [NumberField K] [Field K'] [Algebra K K'] [IsSepClosure K K'] (ζ : K')
    (hζ : IsPrimitiveRoot ζ p) (A : NK.BrauerHasse.OverFinitePrime K K')
    (D D' : Subgroup Gal(K'/K)) (hD : IsClosed (D : Set Gal(K'/K)))
    (hDle : D ≤ stabSubgroup A.1 ⊓ rootFix (K := K) (K' := K') ζ)
    (hD'le : D' ≤ D)
    (hD'open : ∃ N : Subgroup Gal(K'/K), IsOpen (N : Set Gal(K'/K)) ∧ D' = D ⊓ N)
    (h : Nontrivial (NK.BrauerHasse.H2Profinite (K := K) (K' := K') p D)) :
    Nontrivial (NK.BrauerHasse.H2Profinite (K := K) (K' := K') p D') :=
  liveness_inf_open p hp hp2 ζ hζ A D D' hD hDle hD'le hD'open h

/-- **The finite-family Hasse surjectivity** (`NK.NUV2.LC.RouteB.HasseSurj`), derived from the
classical one-place classes (`onePlaceClassesHasse`) by the on-disk linear-algebra assembly
`hasseSurjTop_of_onePlaceClasses` + `hasseSurj_of_top`. -/
theorem hasseSurj_of_onePlaceClasses (p : ℕ) {K K' : Type} [Field K] [NumberField K] [Field K']
    [Algebra K K'] [IsSepClosure K K'] (ζ : K') : HasseSurj p K K' ζ :=
  hasseSurj_of_top p (hasseSurjTop_of_onePlaceClasses onePlaceClassesHasse p) ζ

/-! ## Elementary place bookkeeping -/

lemma smul_comap_eq (σ : Gal(K'/K)) (A : ValuationSubring K') :
    (σ • A).comap (algebraMap K K') = A.comap (algebraMap K K') := by
  ext x
  rw [ValuationSubring.mem_comap, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
    ValuationSubring.mem_comap]
  have h : σ⁻¹ • (algebraMap K K' x) = algebraMap K K' x := by
    simp only [AlgEquiv.smul_def]
    exact AlgEquiv.commutes σ⁻¹ x
  rw [h]

lemma stabSubgroup_smul_eq (σ : Gal(K'/K)) (A : ValuationSubring K') :
    stabSubgroup (σ • A) = (stabSubgroup A).map (MulAut.conj σ).toMonoidHom :=
  MulAction.stabilizer_smul_eq_stabilizer_map_conj σ A

lemma map_conj_apply_eq (g : Gal(K'/K)) (X : Subgroup Gal(K'/K)) :
    X.map (MulAut.conj g).toMonoidHom = {x : Gal(K'/K) | g⁻¹ * x * g ∈ X} := by
  ext x
  change x ∈ Subgroup.map (MulAut.conj g).toMonoidHom X ↔ g⁻¹ * x * g ∈ X
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, hyx⟩
    have : g⁻¹ * x * g = y := by
      rw [← hyx]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [this]; exact hy
  · intro hx
    refine ⟨g⁻¹ * x * g, hx, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

lemma map_conj_map_conj_inv (g : Gal(K'/K)) (X : Subgroup Gal(K'/K)) :
    (X.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom = X := by
  rw [Subgroup.map_map]
  have h : (MulAut.conj g).toMonoidHom.comp (MulAut.conj g⁻¹).toMonoidHom
      = MonoidHom.id Gal(K'/K) := by
    ext x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MonoidHom.id_apply,
      MulAut.conj_apply]
    group
  rw [h, Subgroup.map_id]

lemma map_conj_eq_self (g : Gal(K'/K)) (V : Subgroup Gal(K'/K)) (hg : g ∈ V) :
    V.map (MulAut.conj g).toMonoidHom = V := by
  refine le_antisymm ?_ ?_
  · intro x hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
    rw [← hyx]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact V.mul_mem (V.mul_mem hg hy) (V.inv_mem hg)
  · intro x hx
    refine Subgroup.mem_map.mpr ⟨g⁻¹ * x * g, ?_, ?_⟩
    · exact V.mul_mem (V.mul_mem (V.inv_mem hg) hx) hg
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group

lemma isOpen_map_conj (g : Gal(K'/K)) {X : Subgroup Gal(K'/K)}
    (hX : IsOpen (X : Set Gal(K'/K))) :
    IsOpen ((X.map (MulAut.conj g).toMonoidHom : Subgroup Gal(K'/K)) : Set Gal(K'/K)) := by
  rw [map_conj_apply_eq]
  have hcont : Continuous (fun x : Gal(K'/K) => g⁻¹ * x * g) := by
    continuity
  exact hX.preimage hcont

lemma isLive_of_nontrivial {p : ℕ} {V : Subgroup Gal(K'/K)} {A : ValuationSubring K'}
    (h : Nontrivial (NK.BrauerHasse.H2Profinite (K := K) (K' := K') p
      (V ⊓ stabSubgroup A))) :
    IsLive (K := K) (K' := K') p V A := by
  obtain ⟨a, b, hab⟩ := h
  by_cases ha : a = 0
  · exact ⟨b, fun hb => hab (ha.trans hb.symm)⟩
  · exact ⟨a, ha⟩

/-- **An open subgroup of `V` avoiding a given coset.** -/
lemma exists_level_avoiding_mul {V : Subgroup Gal(K'/K)} (hVcl : IsClosed (V : Set Gal(K'/K)))
    {A : ValuationSubring K'} {h : Gal(K'/K)} (hh : h ∈ V) (hnot : h ∉ stabSubgroup A) :
    ∃ E : IntermediateField K K', FiniteDimensional K ↥E ∧
      ¬ ∃ v ∈ (V ⊓ E.fixingSubgroup : Subgroup Gal(K'/K)),
        ∃ s ∈ (V ⊓ stabSubgroup A : Subgroup Gal(K'/K)), v * s = h := by
  classical
  have hSclosed : IsClosed ((V ⊓ stabSubgroup A : Subgroup Gal(K'/K)) : Set Gal(K'/K)) := by
    refine hVcl.inter ?_
    exact NK.LocalDecomposition.isClosed_stabSubgroup A
  have hKclosed : IsClosed
      {x : Gal(K'/K) | h⁻¹ * x ∈ (V ⊓ stabSubgroup A : Subgroup Gal(K'/K))} :=
    hSclosed.preimage (continuous_const.mul continuous_id)
  have hone : (1 : Gal(K'/K)) ∉
      {x : Gal(K'/K) | h⁻¹ * x ∈ (V ⊓ stabSubgroup A : Subgroup Gal(K'/K))} := by
    simp only [Set.mem_setOf_eq, mul_one]
    intro hc
    exact hnot ((Subgroup.inv_mem_iff (stabSubgroup A)).mp (Subgroup.mem_inf.mp hc).2)
  obtain ⟨E, hEfin, hEsub⟩ :=
    (krullTopology_mem_nhds_one_iff K K' _).mp (hKclosed.isOpen_compl.mem_nhds hone)
  refine ⟨E, hEfin, ?_⟩
  rintro ⟨v, hv, s, hs, hvs⟩
  have hvmem : v ∈ {x : Gal(K'/K) | h⁻¹ * x ∈ (V ⊓ stabSubgroup A : Subgroup Gal(K'/K))} := by
    simp only [Set.mem_setOf_eq]
    have hs' : h⁻¹ * v = s⁻¹ := by rw [← hvs]; group
    rw [hs']
    obtain ⟨hsV, hsstab⟩ := Subgroup.mem_inf.mp hs
    exact Subgroup.mem_inf.mpr ⟨Subgroup.inv_mem _ hsV, Subgroup.inv_mem _ hsstab⟩
  exact (hEsub hv.2) hvmem

/-! ## The assembly -/

/-- **Route B, the core: a closed subgroup of local type lies in a decomposition group.**

Let `hFC` be Hasse's global fundamental class (the arithmetic input for the two-place realisation
`NK.NUV2.LC.RouteB.two_place_realisation`), `p ≠ 2` a prime, `ζ` a primitive `p`-th root of unity
in `K'`, and `V ≤ Gal(K'/K)` closed, fixing `ζ`, continuously isomorphic to `Gal(κ'/M)` for a finite
Galois extension `M/κ` of a `p`-adic completion `κ = 𝔮.adicCompletion L` containing a primitive
`p`-th root of unity.  Then `V` is contained in the decomposition group of some place of `K'` over a
finite prime of `K`.

This is Neukirch's containment (NSW (12.1.9)) for closed subgroups of *local type*; the general
case follows by the Step 0 reduction (`NK.NUV2.LC.RouteB.step0_open_normal`) together with
`NK.LocalDecomposition.le_stabSubgroup_of_openSubgroup_le`.

Proof (the "final argument" of `NOTES_assembly_design.md`):
`|H²(V, Z/p)| = p` (`card_open_local`), so pick a non-zero class and a place `A` with
`H²(V ⊓ D_A, Z/p) ≠ 0` (`exists_live_place_of_localType`).  For `h ∈ V` with `h ∉ D_A`, choose an
open `N` with `h ∉ (N ⊓ V)·D_A` (`exists_level_avoiding_mul`), put `V' := V ⊓ N` (open in `V`,
closed, `≤ rootFix ζ`, with `|H²(V', Z/p)| = p` by `card_h2P_of_open_le_localType`), and observe
that `A` and `hA` are both `V'`-live (`liveness_openSubgroup_clean`), lie over the same prime, and
are not `V'`-conjugate (else `h ∈ V'·D_A`).  Claim U (`live_places_one_orbit_of_hasseSurj`, with `HasseSurj` derived here from the one-place
classes `onePlaceClassesHasse`) gives
`hA ∈ V'•A`, i.e. `h ∈ V'·D_A`, a contradiction.  Hence `h ∈ D_A` for all `h ∈ V`. -/
theorem lies_in_stabSubgroup (hFC : NK.GlobalCFTdeep.FundamentalClassElement) (p : ℕ)
    (hp : p.Prime) (hp2 : p ≠ 2) {K K' : Type} [Field K] [NumberField K] [Field K']
    [Algebra K K'] [IsSepClosure K K'] (ζ : K') (hζ : IsPrimitiveRoot ζ p) {L : Type} [Field L]
    [NumberField L] (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (M : FiniteGaloisIntermediateField (𝔮.adicCompletion L)
      (SeparableClosure (𝔮.adicCompletion L)))
    (hζM : ∃ ζ' : ↥M, IsPrimitiveRoot ζ' p) (V : Subgroup Gal(K'/K))
    (hVcl : IsClosed (V : Set Gal(K'/K)))
    (hVζ : V ≤ NK.NUV2.LC.RouteB.rootFix (K := K) (K' := K') ζ)
    (e : ↥V ≃ₜ* ↥(M.fixingSubgroup)) :
    ∃ A : NK.BrauerHasse.OverFinitePrime K K', V ≤ NK.BrauerHasse.stabSubgroup A.1 := by
  classical
  -- `|H²(V, Z/p)| = p` gives a non-zero class, and the closed-level Hasse principle
  -- (`exists_loc_ne_zero_of_isClosed`) gives a place at which its local component is non-zero,
  -- i.e. a live place.
  have hcardV : Nat.card (NK.BrauerHasse.H2Profinite (K := K) (K' := K') p V) = p :=
    card_open_local p hp 𝔮 M hζM V e
  haveI : Finite (NK.BrauerHasse.H2Profinite (K := K) (K' := K') p V) :=
    (Nat.card_pos_iff.mp (by rw [hcardV]; exact hp.pos)).2
  haveI : Fintype (NK.BrauerHasse.H2Profinite (K := K) (K' := K') p V) :=
    Fintype.ofFinite _
  haveI : Nontrivial (NK.BrauerHasse.H2Profinite (K := K) (K' := K') p V) := by
    rw [← Fintype.one_lt_card_iff_nontrivial, ← Nat.card_eq_fintype_card, hcardV]
    exact hp.one_lt
  haveI hfinV : Finite (NK.BrauerHasse.H2Profinite (K := K) (K' := K') p V) :=
    Nat.finite_of_card_ne_zero (by rw [hcardV]; exact hp.ne_zero)
  haveI hfintV : Fintype (NK.BrauerHasse.H2Profinite (K := K) (K' := K') p V) :=
    Fintype.ofFinite _
  have honeV : 1 < Fintype.card (NK.BrauerHasse.H2Profinite (K := K) (K' := K') p V) := by
    rw [← Nat.card_eq_fintype_card, hcardV]
    exact hp.one_lt
  obtain ⟨x, hx⟩ := Fintype.exists_ne_of_one_lt_card honeV
    (0 : NK.BrauerHasse.H2Profinite (K := K) (K' := K') p V)
  obtain ⟨A, hA⟩ :=
    exists_loc_ne_zero_of_isClosed (K := K) (K' := K') p hp hp2 ζ hζ V hVcl hVζ x hx
  have hAlive : IsLive (K := K) (K' := K') p V A.1 :=
    ⟨NK.BrauerHasse.H2Profinite.loc p V x A, hA⟩
  refine ⟨A, ?_⟩
  intro h hh
  by_contra hnot
  have hD : h ∉ stabSubgroup A.1 := hnot
  obtain ⟨E, hEfin, hEavoid⟩ :=
    exists_level_avoiding_mul (K := K) (K' := K') hVcl (A := A.1) hh hD
  haveI : FiniteDimensional K ↥E := hEfin
  set V' : Subgroup Gal(K'/K) := V ⊓ E.fixingSubgroup with hV'def
  have hV'le : V' ≤ V := inf_le_left
  have hV'open : ∃ N : Subgroup Gal(K'/K), IsOpen (N : Set Gal(K'/K)) ∧ V' = V ⊓ N :=
    ⟨E.fixingSubgroup, IntermediateField.fixingSubgroup_isOpen E, rfl⟩
  have hV'cl : IsClosed (V' : Set Gal(K'/K)) := by
    obtain ⟨N, hNopen, hN⟩ := hV'open
    rw [hN]
    exact hVcl.inter (Subgroup.isClosed_of_isOpen N hNopen)
  have hV'ζ : V' ≤ rootFix (K := K) (K' := K') ζ := fun x hx => hVζ hx.1
  have hcard : Nat.card (NK.BrauerHasse.H2Profinite (K := K) (K' := K') p V') = p :=
    card_h2P_of_open_le_localType (K := K) (K' := K') p hp ζ hζ 𝔮 M hζM V hVcl e V' hV'le hV'open
  have hScl : IsClosed ((V ⊓ stabSubgroup A.1 : Subgroup Gal(K'/K)) : Set Gal(K'/K)) := by
    refine hVcl.inter ?_
    exact NK.LocalDecomposition.isClosed_stabSubgroup A.1
  have hDle : (V ⊓ stabSubgroup A.1 : Subgroup Gal(K'/K))
      ≤ stabSubgroup A.1 ⊓ rootFix (K := K) (K' := K') ζ :=
    le_inf inf_le_right (fun x hx => hVζ hx.1)
  -- `A` is `V'`-live
  have hliveA : IsLive (K := K) (K' := K') p V' A.1 := by
    refine isLive_of_nontrivial (K := K) (K' := K') ?_
    have hD'le : (V' ⊓ stabSubgroup A.1 : Subgroup Gal(K'/K))
        ≤ (V ⊓ stabSubgroup A.1 : Subgroup Gal(K'/K)) :=
      le_inf (inf_le_left.trans hV'le) inf_le_right
    have hD'open : ∃ N : Subgroup Gal(K'/K), IsOpen (N : Set Gal(K'/K)) ∧
        (V' ⊓ stabSubgroup A.1 : Subgroup Gal(K'/K))
          = (V ⊓ stabSubgroup A.1 : Subgroup Gal(K'/K)) ⊓ N := by
      refine ⟨E.fixingSubgroup, IntermediateField.fixingSubgroup_isOpen E, ?_⟩
      rw [hV'def]
      ext x
      simp only [Subgroup.mem_inf]
      tauto
    exact liveness_openSubgroup_clean (K := K) (K' := K') p hp hp2 ζ hζ A
      (V ⊓ stabSubgroup A.1) (V' ⊓ stabSubgroup A.1) hScl hDle hD'le hD'open hAlive.nontrivial
  set A₂ : NK.BrauerHasse.OverFinitePrime K K' :=
    ⟨h • A.1, by rw [smul_comap_eq (K := K) (K' := K') h A.1]; exact A.2⟩ with hA₂def
  have hA₂coe : A₂.1 = h • A.1 := rfl
  have hsame : A.1.comap (algebraMap K K') = A₂.1.comap (algebraMap K K') := by
    rw [hA₂coe, smul_comap_eq]
  -- `h • A` is `V'`-live
  have hliveA₂ : IsLive (K := K) (K' := K') p V' A₂.1 := by
    rw [hA₂coe]
    refine isLive_of_nontrivial (K := K) (K' := K') ?_
    set M : Subgroup Gal(K'/K) := (E.fixingSubgroup).map (MulAut.conj h⁻¹).toMonoidHom with hMdef
    set W : Subgroup Gal(K'/K) := V ⊓ M with hWdef
    have hW'_eq : W = V'.map (MulAut.conj h⁻¹).toMonoidHom := by
      rw [hWdef, hMdef, hV'def, Subgroup.map_inf_eq _ _ _ (MulAut.conj h⁻¹).injective,
        map_conj_eq_self (K := K) (K' := K') h⁻¹ V (V.inv_mem hh)]
    have hOpenM : IsOpen (M : Set Gal(K'/K)) := by
      rw [hMdef]
      exact isOpen_map_conj (K := K) (K' := K') h⁻¹ (IntermediateField.fixingSubgroup_isOpen E)
    have hWV : W ≤ V := by rw [hWdef]; exact inf_le_left
    have hle : (W ⊓ stabSubgroup A.1 : Subgroup Gal(K'/K))
        ≤ (V ⊓ stabSubgroup A.1 : Subgroup Gal(K'/K)) :=
      le_inf (inf_le_left.trans hWV) inf_le_right
    have hopen : ∃ N : Subgroup Gal(K'/K), IsOpen (N : Set Gal(K'/K)) ∧
        (W ⊓ stabSubgroup A.1 : Subgroup Gal(K'/K))
          = (V ⊓ stabSubgroup A.1 : Subgroup Gal(K'/K)) ⊓ N := by
      refine ⟨M, hOpenM, ?_⟩
      rw [hWdef]
      ext x
      simp only [Subgroup.mem_inf]
      tauto
    have hmain := liveness_openSubgroup_clean (K := K) (K' := K') p hp hp2 ζ hζ A
      (V ⊓ stabSubgroup A.1) (W ⊓ stabSubgroup A.1) hScl hDle hle hopen hAlive.nontrivial
    have heq : ((W ⊓ stabSubgroup A.1 : Subgroup Gal(K'/K)).map
        (MulAut.conj h).toMonoidHom) = (V' ⊓ stabSubgroup (h • A.1) : Subgroup Gal(K'/K)) := by
      rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj h).injective, hW'_eq,
        map_conj_map_conj_inv, stabSubgroup_smul_eq]
    have hconj := nontrivial_conjSub_p (K := K) (K' := K') (p := p)
      (V := (W ⊓ stabSubgroup A.1 : Subgroup Gal(K'/K))) h hmain
    rwa [heq] at hconj
  -- Claim U at `V'`
  obtain ⟨g, hg, hgA⟩ := live_places_one_orbit_of_hasseSurj (K := K) (K' := K') hFC p hp hp2 ζ hζ
    (hasseSurj_of_onePlaceClasses (K := K) (K' := K') p ζ) V' hV'cl hV'ζ hcard
    hliveA hliveA₂ hsame
  have hg' : g ∈ V ⊓ E.fixingSubgroup := by
    rw [hV'def] at hg
    exact hg
  have hs : g⁻¹ * h ∈ (V ⊓ stabSubgroup A.1 : Subgroup Gal(K'/K)) := by
    refine Subgroup.mem_inf.mpr ⟨V.mul_mem (V.inv_mem hg'.1) hh, ?_⟩
    rw [show (stabSubgroup A.1 : Subgroup Gal(K'/K))
        = MulAction.stabilizer Gal(K'/K) A.1 from rfl, MulAction.mem_stabilizer_iff]
    rw [hA₂coe] at hgA
    calc (g⁻¹ * h) • A.1 = g⁻¹ • (h • A.1) := by rw [mul_smul]
      _ = g⁻¹ • (g • A.1) := by rw [← hgA]
      _ = A.1 := inv_smul_smul g A.1
  exact hEavoid ⟨g, hg', g⁻¹ * h, hs, by group⟩

end NK.NUV2.LC.RouteB
