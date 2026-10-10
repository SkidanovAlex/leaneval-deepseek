import Mathlib.FieldTheory.KrullTopology
import Mathlib.GroupTheory.Nilpotent
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.ValuationSubring
import Submission.Work.SSGRoute.ZConstruction.exists_finset_KConj_cover
import Submission.Work.SSGRoute.ZDataMup.LocalData
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The p. 18 diagram chase of Schmidt--Wingberg, with the relaxation level corrected

`Work.SSGRoute.AuxExists` (`ZConstruction/ZDataAux.lean`) is the auxiliary-class obligation of
Schmidt--Wingberg §4, p. 18 -- the last obligation of the node
`Work.SSGRoute.shafarevich_z_construction` beyond the one-dimensional gate `Work.SSGRoute.MupGate`.
Its two halves are

* a **realisation** of local data (`Work.SSGRoute.AuxRealisationGate`, the Tate--Poitou degree-one
  surjectivity, the deep arithmetic), whose hypothesis is
* the **orthogonality of the prescribed datum** against the relaxed dual Selmer group -- the
  *diagram chase* of p. 18.

This file proves the second half **outright**, from the local axioms of the pairing alone.  The point
is that no arithmetic is hidden in it: given

* a local Tate system `pair` with the Hilbert-symbol product formula `IsProductFormula` and the
  vanishing of the pairing of two inertia-trivial local classes (`IsUnramifiedOrthogonal`),
* a place set `T` of pairwise level-`K`-non-conjugate finite places, all of them conjugate into `S`
  and meeting every level-`K` class of `cs(S)`,
* a data family `y₁` satisfying `ZHyp` at `(Λ,S)`, and
* a class `b` which is *relaxed dual* at the level `Λ` (`IsRelaxedDual K Λ T b`: a global cocycle on
  `G_K`, unramified outside the level-`K` classes of `T`, and *locally trivial* at the `Λ`-split
  places outside those classes),

the prescribed datum `auxDatum K S y₁` of `y₁` is orthogonal to `b`:
`∑_{A ∈ T} pair (decomp k A ⊓ G_K) (auxDatum K S y₁ A) b = 0`.

## Why the relaxation level must be `Λ` and not a larger field

The chase is Hilbert reciprocity over a place set `T'' ⊇ T` which covers, up to level-`K` conjugacy,
the *ramification of `y₁` at level `K`* as well as that of `b`.  The extra places `R = T'' ∖ T` are
ramified for `y₁`, hence -- by `ZHyp.hyS` and `ZHyp.hyT` -- they are **`Λ`-split** and outside
`cs(S)`.  At such a place the term of the reciprocity sum is `pair_A y₁ b`, and it vanishes because
`b` is *locally trivial* there, which is precisely the relaxation condition at the field **`Λ`**
(the split places of `Λ` are the ones at which `IsRelaxedDual K Λ T b` asks `b` to vanish).  Asking
instead for the relaxation at a *larger* level `M ⊇ Λ` is unsound here: `M`-split implies
`Λ`-split (for `Λ ≤ M`, `fixingSubgroup` is antitone), so the `M`-split places form a *proper*
subset of the `Λ`-split ones and the `M`-split condition gives nothing at the places of `R`.  This
is exactly the direction error which the retracted statement `Work.SSGRoute.AuxOrthogonalityGate`
(with `Λ ≤ M`) carried; the correction below keeps the relaxation at `Λ` itself, which is also the
level at which the realisation `AuxRealisationGate` consumes the conclusion.

## The finiteness input

The place set `R` is produced by a *finiteness* statement at level `K` -- the ramification of a
locally constant cochain is finite up to level-`K` conjugacy
(`Work.SSGRoute.ZConstruction.exists_finset_KConj_ramification_cover`) -- glued to the given `T` by
the level-`K` cover `Work.SSGRoute.ZConstruction.exists_finset_KConj_cover`.  Both are pure
place/Galois bookkeeping.
-/

open scoped Pointwise BigOperators

open Classical

namespace Work.SSGRoute

open _root_.SSGRoute

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 800000

variable {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω]

/-! ## Zero-extension off `G_K`

`IsProductFormula` asks for the two global cocycles to be unramified at *level `k`*
(`∀ σ : G_k, IsInertia k B σ → a σ = 0 ∧ b σ = 0`), whereas the data of this node are only
constrained on `G_K`.  Since the local pairings see a cochain only through its restriction to the
level-`K` local group (`ZDataMup.pair_congr_of_eqOn_left/right`), one may *replace* both cochains by
their zero extension off `G_K` before applying the product formula. -/

/-- The function which agrees with `f` on `G_K` and vanishes elsewhere. -/
noncomputable def zeroOff (K : IntermediateField k Ω) {M : Type} [Zero M]
    (f : (Ω ≃ₐ[k] Ω) → M) : (Ω ≃ₐ[k] Ω) → M := by
  classical
  exact fun σ => if σ ∈ K.fixingSubgroup then f σ else 0

/-- On a subgroup of `G_K` the crossed-homomorphism condition for the restriction `res k K` is
plain additivity, because `res` is trivial on `G_K`
(`ZDataMup.res_eq_one_of_mem_fixingSubgroup`). -/
theorem isCocycleOn_of_addOn {K : IntermediateField k Ω} [Normal k K]
    [DistribMulAction (K ≃ₐ[k] K) (ZMod p)] {H : Subgroup (Ω ≃ₐ[k] Ω)}
    (hH : H ≤ K.fixingSubgroup) {f : (Ω ≃ₐ[k] Ω) → ZMod p}
    (hadd : ∀ g ∈ H, ∀ h ∈ H, f (g * h) = f g + f h) :
    SSGRoute.IsCocycleOn (SSGRoute.res k K) H f := by
  intro g hg h hh
  rw [hadd g hg h hh, ZDataMup.res_eq_one_of_mem_fixingSubgroup (hH hg), one_smul]

theorem zeroOff_eq_of_mem {K : IntermediateField k Ω} {M : Type} [Zero M]
    {f : (Ω ≃ₐ[k] Ω) → M} {σ : Ω ≃ₐ[k] Ω} (h : σ ∈ K.fixingSubgroup) :
    zeroOff K f σ = f σ := by
  unfold zeroOff
  rw [if_pos h]

theorem zeroOff_eq_zero_of_not_mem {K : IntermediateField k Ω} {M : Type} [Zero M]
    {f : (Ω ≃ₐ[k] Ω) → M} {σ : Ω ≃ₐ[k] Ω} (h : σ ∉ K.fixingSubgroup) :
    zeroOff K f σ = 0 := by
  unfold zeroOff
  rw [if_neg h]

/-- The zero extension of a level-`K` cocycle is again a level-`K` cocycle. -/
theorem isCocycleOn_zeroOff {K : IntermediateField k Ω} [Normal k K]
    [DistribMulAction (K ≃ₐ[k] K) (ZMod p)] {f : (Ω ≃ₐ[k] Ω) → ZMod p}
    (h : SSGRoute.IsCocycleOn (SSGRoute.res k K) K.fixingSubgroup f) :
    SSGRoute.IsCocycleOn (SSGRoute.res k K) K.fixingSubgroup (zeroOff K f) := by
  intro g hg h' hh
  rw [zeroOff_eq_of_mem (K.fixingSubgroup.mul_mem hg hh), zeroOff_eq_of_mem hg,
    zeroOff_eq_of_mem hh]
  exact h g hg h' hh

/-- The zero extension of a level-`K` locally constant function is again locally constant. -/
theorem isLocConstOn_zeroOff {K : IntermediateField k Ω} {f : (Ω ≃ₐ[k] Ω) → ZMod p}
    (h : SSGRoute.IsLocConstOn K.fixingSubgroup f) :
    SSGRoute.IsLocConstOn K.fixingSubgroup (zeroOff K f) := by
  obtain ⟨U, hUo, hU⟩ := h
  refine ⟨U, hUo, ?_⟩
  intro g hg u hu huK
  rw [zeroOff_eq_of_mem (K.fixingSubgroup.mul_mem hg huK), zeroOff_eq_of_mem hg]
  exact hU g hg u hu huK

/-- The `G_k`-conjugacy clause of `ZDataMup.IsProductFormula`, rewritten in the `KConj` vocabulary:
`∃ τ ∈ G_K, ∀ x, x ∈ B ↔ τ⁻¹ • x ∈ A` says that `B` is the transport of `A` by `τ`. -/
theorem kConj_of_forall_mem {K : IntermediateField k Ω} {A B : ValuationSubring Ω}
    (h : ∃ τ ∈ K.fixingSubgroup, ∀ x : Ω, x ∈ B ↔ (τ⁻¹ : Ω ≃ₐ[k] Ω) • x ∈ A) :
    KConj K A B := by
  obtain ⟨τ, hτ, hx⟩ := h
  refine ⟨τ, hτ, ?_⟩
  refine SetLike.ext fun x => ?_
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
  exact (hx x).symm

/-- The converse of `kConj_of_forall_mem`. -/
theorem kConj_forall_mem_of_kConj {K : IntermediateField k Ω} {A B : ValuationSubring Ω}
    (h : KConj K A B) :
    ∃ τ ∈ K.fixingSubgroup, ∀ x : Ω, x ∈ B ↔ (τ⁻¹ : Ω ≃ₐ[k] Ω) • x ∈ A := by
  obtain ⟨τ, hτ, hτA⟩ := h
  refine ⟨τ, hτ, fun x => ?_⟩
  rw [← hτA]
  exact ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem

/-! ## The corrected p. 18 chase -/

/-- **The p. 18 diagram chase, with the relaxation level at `Λ`.**  See the module docstring. -/
theorem auxDatum_orthogonal_of_productFormula
    {K Λ : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
    [DistribMulAction (K ≃ₐ[k] K) (ZMod p)]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]
    {pair : Subgroup (Ω ≃ₐ[k] Ω) → ((Ω ≃ₐ[k] Ω) → ZMod p) → ((Ω ≃ₐ[k] Ω) → ZMod p) → ZMod p}
    (hpair : ZDataMup.IsLocalTateSystem p k Ω K pair)
    (hprod : ZDataMup.IsProductFormula p k Ω K pair)
    (hunr : IsUnramifiedOrthogonal (p := p) K pair)
    {S T : Finset (ValuationSubring Ω)}
    (hTfin : ∀ A ∈ T, SSGRoute.IsFinPlace k A)
    (hTdisj : ∀ A ∈ T, ∀ B ∈ T, KConj K A B → A = B)
    (hTconj : ∀ A ∈ T, ∃ A' ∈ S, SSGRoute.IsConjPlace k A' A)
    (hTcov : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∃ A ∈ S, SSGRoute.IsConjPlace k A B) → ∃ A' ∈ T, KConj K A' B)
    {y₁ : (Ω ≃ₐ[k] Ω) → ZMod p} (hy₁ : ZHyp (p := p) K Λ S y₁)
    {b : (Ω ≃ₐ[k] Ω) → ZMod p} (hb : IsRelaxedDual (p := p) K Λ T b) :
    ∑ A ∈ T, pair (SSGRoute.decomp k A ⊓ K.fixingSubgroup) (auxDatum (p := p) K S y₁ A) b = 0 := by
  classical
  obtain ⟨hboc, hbloc, hbunr, hbtriv⟩ := hb
  -- (0) `ZHyp.add` is the crossed cocycle condition for `res k K`
  have hcocY₁ : SSGRoute.IsCocycleOn (SSGRoute.res k K) K.fixingSubgroup y₁ :=
    isCocycleOn_of_addOn (le_refl K.fixingSubgroup) hy₁.add
  -- (1) the level at which `y₁` vanishes
  obtain ⟨N, _hKN, hNfin, hNgal, hNv⟩ :=
    exists_level_vanishing_finite (K := K) hy₁.add hy₁.locconst
  haveI : FiniteDimensional k N := hNfin
  haveI : IsGalois k N := hNgal
  -- (2) the `G_k`-conjugacy cover of the places ramified in `N|k`
  obtain ⟨S', hS'fin, hS'disj, _hS'sub, hS'ram⟩ :=
    ZConstruction.exists_finset_ramifiedPlaces p (Fact.out : p.Prime) k Ω N ∅ (by simp) (by simp)
  -- (3) the level-`K` cover, glued to `T`
  obtain ⟨T'', hT''fin, hT''disj, hT''sub, _hT''cov⟩ :=
    ZConstruction.exists_finset_KConj_cover p k Ω K T S'
      hTfin hTdisj hS'fin hS'disj
  -- (4) the zero extensions
  have hcocZ : SSGRoute.IsCocycleOn (SSGRoute.res k K) K.fixingSubgroup (zeroOff K y₁) :=
    isCocycleOn_zeroOff hcocY₁
  have hlocZ : SSGRoute.IsLocConstOn K.fixingSubgroup (zeroOff K y₁) :=
    isLocConstOn_zeroOff hy₁.locconst
  have hcocB : SSGRoute.IsCocycleOn (SSGRoute.res k K) K.fixingSubgroup (zeroOff K b) :=
    isCocycleOn_zeroOff hboc
  have hlocB : SSGRoute.IsLocConstOn K.fixingSubgroup (zeroOff K b) :=
    isLocConstOn_zeroOff hbloc
  -- (5) the unramifiedness outside `T''`, at level `k`
  have hunram : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∀ A ∈ T'', ¬ ∃ τ ∈ K.fixingSubgroup,
        ∀ x : Ω, x ∈ B ↔ (τ⁻¹ : Ω ≃ₐ[k] Ω) • x ∈ A) →
      ∀ σ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k B σ →
        zeroOff K y₁ σ = 0 ∧ zeroOff K b σ = 0 := by
    intro B hB hnot σ hσI
    have hnotK : ∀ A ∈ T'', ¬ KConj K A B := by
      intro A hA hc
      exact hnot A hA (kConj_forall_mem_of_kConj hc)
    by_cases hσK : σ ∈ K.fixingSubgroup
    · rw [zeroOff_eq_of_mem hσK, zeroOff_eq_of_mem hσK]
      refine ⟨?_, ?_⟩
      · by_contra hne
        have hσN : σ ∈ N.fixingSubgroup := by
          by_contra hσN
          have hram : SSGRoute.IsRamifiedIn k N B := ⟨σ, hσI, hσN⟩
          obtain ⟨A, hA, hconj⟩ := hS'ram B hB (Or.inl hram)
          obtain ⟨A', hA', hc⟩ := _hT''cov B hB ⟨A, hA, hconj⟩
          exact hnotK A' hA' hc
        exact hne (hNv σ hσN)
      · exact hbunr B hB (fun A₀ hA₀ hc => hnotK A₀ (hT''sub A₀ hA₀) hc) σ hσK hσI
    · rw [zeroOff_eq_zero_of_not_mem hσK, zeroOff_eq_zero_of_not_mem hσK]
      exact ⟨rfl, rfl⟩
  -- (6) Hilbert reciprocity over `T''`
  have hsumZ : ∑ A ∈ T'', pair (SSGRoute.decomp k A ⊓ K.fixingSubgroup) (zeroOff K y₁)
      (zeroOff K b) = 0 :=
    hprod (zeroOff K y₁) (zeroOff K b) hcocZ hlocZ hcocB hlocB T'' hT''fin
      (fun A hA B hB' h => hT''disj A hA B hB' (kConj_of_forall_mem h)) hunram
  -- (7) replace the zero extensions by the original cochains
  have hsumY : ∑ A ∈ T'', pair (SSGRoute.decomp k A ⊓ K.fixingSubgroup) y₁ b = 0 := by
    rw [← hsumZ]
    refine Finset.sum_congr rfl fun A hA => ?_
    have hAfin : SSGRoute.IsFinPlace k A := hT''fin A hA
    have hH : ∃ A' : ValuationSubring Ω, SSGRoute.IsFinPlace k A' ∧
        (SSGRoute.decomp k A ⊓ K.fixingSubgroup) = (SSGRoute.decomp k A' ⊓ K.fixingSubgroup) :=
      ⟨A, hAfin, rfl⟩
    have hle : SSGRoute.decomp k A ⊓ K.fixingSubgroup ≤ K.fixingSubgroup := inf_le_right
    have hcY : SSGRoute.IsCocycleOn (SSGRoute.res k K)
        (SSGRoute.decomp k A ⊓ K.fixingSubgroup) y₁ :=
      ZDataMup.isCocycleOn_of_le hle hcocY₁
    have hlY : SSGRoute.IsLocConstOn (SSGRoute.decomp k A ⊓ K.fixingSubgroup) y₁ :=
      ZDataMup.isLocConstOn_of_le hle hy₁.locconst
    have hcZ' : SSGRoute.IsCocycleOn (SSGRoute.res k K)
        (SSGRoute.decomp k A ⊓ K.fixingSubgroup) (zeroOff K y₁) :=
      ZDataMup.isCocycleOn_of_le hle hcocZ
    have hlZ' : SSGRoute.IsLocConstOn (SSGRoute.decomp k A ⊓ K.fixingSubgroup) (zeroOff K y₁) :=
      ZDataMup.isLocConstOn_of_le hle hlocZ
    have hcB' : SSGRoute.IsCocycleOn (SSGRoute.res k K)
        (SSGRoute.decomp k A ⊓ K.fixingSubgroup) b :=
      ZDataMup.isCocycleOn_of_le hle hboc
    have hlB' : SSGRoute.IsLocConstOn (SSGRoute.decomp k A ⊓ K.fixingSubgroup) b :=
      ZDataMup.isLocConstOn_of_le hle hbloc
    have hcB'' : SSGRoute.IsCocycleOn (SSGRoute.res k K)
        (SSGRoute.decomp k A ⊓ K.fixingSubgroup) (zeroOff K b) :=
      ZDataMup.isCocycleOn_of_le hle hcocB
    have hlB'' : SSGRoute.IsLocConstOn (SSGRoute.decomp k A ⊓ K.fixingSubgroup) (zeroOff K b) :=
      ZDataMup.isLocConstOn_of_le hle hlocB
    have hstep1 : pair (SSGRoute.decomp k A ⊓ K.fixingSubgroup) y₁ b
        = pair (SSGRoute.decomp k A ⊓ K.fixingSubgroup) y₁ (zeroOff K b) :=
      ZDataMup.pair_congr_of_eqOn_right hpair hH ⟨hcY, hlY⟩ ⟨hcB', hlB'⟩ ⟨hcB'', hlB''⟩
        (fun g hg => (zeroOff_eq_of_mem (f := b) (hle hg)).symm)
    have hstep2 : pair (SSGRoute.decomp k A ⊓ K.fixingSubgroup) y₁ (zeroOff K b)
        = pair (SSGRoute.decomp k A ⊓ K.fixingSubgroup) (zeroOff K y₁) (zeroOff K b) :=
      ZDataMup.pair_congr_of_eqOn_left hpair hH ⟨hcY, hlY⟩ ⟨hcZ', hlZ'⟩ ⟨hcB'', hlB''⟩
        (fun g hg => (zeroOff_eq_of_mem (f := y₁) (hle hg)).symm)
    rw [hstep1, hstep2]
  -- (8) the terms at the new places `T'' ∖ T` vanish
  have hRvan : ∀ A ∈ T'' \ T,
      pair (SSGRoute.decomp k A ⊓ K.fixingSubgroup) y₁ b = 0 := by
    intro A hA
    obtain ⟨hAT'', hAnT⟩ := Finset.mem_sdiff.mp hA
    have hAfin : SSGRoute.IsFinPlace k A := hT''fin A hAT''
    have hnotT : ∀ A₀ ∈ T, ¬ KConj K A₀ A := by
      intro A₀ hA₀ hc
      have hA₀T'' : A₀ ∈ T'' := hT''sub A₀ hA₀
      have hEq : A = A₀ := hT''disj A hAT'' A₀ hA₀T'' (ZConstruction.kConj_symm hc)
      exact hAnT (hEq ▸ hA₀)
    have hH : ∃ A' : ValuationSubring Ω, SSGRoute.IsFinPlace k A' ∧
        (SSGRoute.decomp k A ⊓ K.fixingSubgroup) = (SSGRoute.decomp k A' ⊓ K.fixingSubgroup) :=
      ⟨A, hAfin, rfl⟩
    have hle : SSGRoute.decomp k A ⊓ K.fixingSubgroup ≤ K.fixingSubgroup := inf_le_right
    have hcY : SSGRoute.IsCocycleOn (SSGRoute.res k K)
        (SSGRoute.decomp k A ⊓ K.fixingSubgroup) y₁ :=
      ZDataMup.isCocycleOn_of_le hle hcocY₁
    have hlY : SSGRoute.IsLocConstOn (SSGRoute.decomp k A ⊓ K.fixingSubgroup) y₁ :=
      ZDataMup.isLocConstOn_of_le hle hy₁.locconst
    have hcB' : SSGRoute.IsCocycleOn (SSGRoute.res k K)
        (SSGRoute.decomp k A ⊓ K.fixingSubgroup) b :=
      ZDataMup.isCocycleOn_of_le hle hboc
    have hlB' : SSGRoute.IsLocConstOn (SSGRoute.decomp k A ⊓ K.fixingSubgroup) b :=
      ZDataMup.isLocConstOn_of_le hle hbloc
    by_cases hsplit : SSGRoute.IsSplitIn k Λ A
    · -- `b` is locally trivial at the `Λ`-split place `A`
      have hbcob : SSGRoute.IsCoboundaryOn (SSGRoute.res k K)
          (SSGRoute.decomp k A ⊓ K.fixingSubgroup) b := by
        refine ⟨0, fun g hg => ?_⟩
        rw [hbtriv A hAfin hnotT hsplit g (Subgroup.mem_inf.mp hg).2 (Subgroup.mem_inf.mp hg).1]
        simp
      exact hpair.vanishes_coboundary _ hH y₁ b ⟨hcY, hlY⟩ ⟨hcB', hlB'⟩ (Or.inr hbcob)
    · -- otherwise both classes are unramified at `A`
      have hAcsS : ∀ A' ∈ S, ¬ SSGRoute.IsConjPlace k A' A := by
        intro A' hA' hconj
        obtain ⟨t, htT, hc⟩ := hTcov A hAfin ⟨A', hA', hconj⟩
        exact hnotT t htT hc
      exact hunr A hAfin y₁ b ⟨hcY, hlY⟩ ⟨hcB', hlB'⟩
        (fun σ hσ hσI => hy₁.hyS A hAfin hAcsS hsplit σ hσ hσI)
        (fun σ hσ hσI => hbunr A hAfin hnotT σ hσ hσI)
  -- (9) split the sum
  have hunion : T ∪ (T'' \ T) = T'' := Finset.union_sdiff_of_subset (fun a ha => hT''sub a ha)
  have hdisj : Disjoint T (T'' \ T) := Finset.disjoint_sdiff
  have hsplitSum : ∑ A ∈ T'', pair (SSGRoute.decomp k A ⊓ K.fixingSubgroup) y₁ b
      = ∑ A ∈ T, pair (SSGRoute.decomp k A ⊓ K.fixingSubgroup) y₁ b
        + ∑ A ∈ T'' \ T, pair (SSGRoute.decomp k A ⊓ K.fixingSubgroup) y₁ b := by
    conv_lhs => rw [← hunion]
    rw [Finset.sum_union hdisj]
  have hTsum : ∑ A ∈ T, pair (SSGRoute.decomp k A ⊓ K.fixingSubgroup) y₁ b = 0 := by
    have h2 : (∑ A ∈ T, pair (SSGRoute.decomp k A ⊓ K.fixingSubgroup) y₁ b)
        + (∑ A ∈ T'' \ T, pair (SSGRoute.decomp k A ⊓ K.fixingSubgroup) y₁ b) = 0 := by
      rw [← hsplitSum]
      exact hsumY
    simpa [Finset.sum_eq_zero hRvan] using h2
  -- (10) replace `y₁` by the prescribed datum, which agrees with it on `T`
  have hcongr : (∑ A ∈ T, pair (SSGRoute.decomp k A ⊓ K.fixingSubgroup)
        (auxDatum (p := p) K S y₁ A) b)
      = ∑ A ∈ T, pair (SSGRoute.decomp k A ⊓ K.fixingSubgroup) y₁ b :=
    Finset.sum_congr rfl fun A hA => by
      have hfun : auxDatum (p := p) K S y₁ A = y₁ := by
        simp only [auxDatum]
        rw [if_pos (hTconj A hA)]
      rw [hfun]
  rw [hcongr]
  exact hTsum

end Work.SSGRoute
