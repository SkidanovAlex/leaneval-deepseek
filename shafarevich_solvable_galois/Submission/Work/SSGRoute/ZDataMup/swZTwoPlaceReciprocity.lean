import Mathlib.FieldTheory.KrullTopology
import Mathlib.GroupTheory.Nilpotent
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.SSGRoute.ZConstruction.auxPairingGate_odd_aux
import Submission.Work.SSGRoute.ZDataMup.OddForm.oTheta_eq_one_of_ne_oddPrime
import Submission.Work.SSGRoute.ZDataMup.oPairAtDef
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The two-place reciprocity of the Grünwald route (Schmidt--Wingberg §4(b))

This is the single arithmetic input of the odd-`p` construction of the auxiliary class `z`
(`ZDataMup/sw_odd_kummer_core.lean` §3, §4(b)): the *localised product formula* of the odd-`p`
Kummer pairing at the two escape classes `Zi`, `ZN`.

`oPairAt ζ hζ A hA a b` is the local Kummer pairing `⟨a, b⟩_A = χ_α(θ_A(β_A))` at the finite place
`A`.  The theorem `swZTwoPlaceReciprocity` below says: for two global cocycles `a`, `b` on `G_K`
which are the Kummer characters of global units `α β ∈ ↥Kˣ`, which *agree* on the local groups of a
place set `S` (`hagr`, hence `⟨a, b⟩_A = ⟨x_A, x_A⟩`) and are *unramified* outside the classes of
`S ∪ {Zi, ZN}` (`hunr`), the product formula `OddForm.oPairForm_sum_attach_eq_zero_of_outside` over
`T' = S ∪ {Zi, ZN}` collapses to the two surviving terms:

  `⟨a, b⟩_Zi + ⟨a, b⟩_ZN = 0`.

With the `-1` normalisation of the escape elements at the escape primes and the antisymmetry of the
Kummer symbol this identity is exactly the paper's `χ b_i ψ_N = χ b_N ψ_i` of §4(b); together with
the prescription of condition (3) and the shoe-box matching of the Frobenius values it yields the
sibling vanishing `χ b_i ψ_{tQ_N} + χ b_N ψ_{tQ_N} = 0`.

## Division of the proof

* The product formula over `T'` and the triviality of the local factors outside `T'` are available
  and clean: `OddForm.oPairForm_sum_attach_eq_zero_of_outside` (proved) and
  `OddForm.oTheta_eq_one_of_ne_oddPrime` (proved), which supplies the product formula's hypothesis
  `hout` verbatim.
* The collapse `swZTwoPlaceReciprocity_of_Szero` is *proved below* from the vanishing of the
  `S`-terms; it is the routine assembly (place bookkeeping and `Finset` sums) and contains no
  arithmetic.
* The vanishing of the `S`-terms (`swz_S_term_eq_zero`) needs the agreement `hagr` together with
  the *alternation* `⟨x, x⟩ = 0` of the pairing (respectively the antisymmetry of the Kummer
  symbol for odd `p`).  That alternation is proved on disk only inside the *frozen copy* cone of
  `ZConstruction/levelK_pairing_productFormula.lean` (`ZConstruction.oPairForm_self_eq_zero`,
  whose copy is `ZConstruction.OddGate.oddGate_oPairForm_self_eq_zero`), and that cone cannot be
  imported together with the present one: both declare
  `Work.SSGRoute.ZDataMup.OddForm.oPairForm` (and `mupCocycleChar` etc.), so a single file may use
  only one of them (`PING_zdatamup_clash_and_honest_local_system.md`; the de-duplication is
  prepared in `ZDataMup/exists_cocycle_of_lcHoms_localCocycle.lean` but not applied on disk).
  Either the alternation is ported into this cone (the proof of
  `ZConstruction.oPairForm_self_eq_zero` is a verbatim template and its ingredients have
  counterparts here: `LTRecFamHonest.hLift`, `LTRecFamHonest.hLevel`, `hChar`,
  `mupLocalForm`'s `oddLocalFactor_eq_one_of_localPowClass_eq_one`,
  `ZConstruction.aux_localImageAt_mem_localNormSubgroup_hLevel_of_notMem`,
  `LTRecFamHonest.hLocalFactor_eq_one_of_mem_localNormSubgroup`), or the two cones are merged, after
  which `swz_S_term_eq_zero` is the two-line argument via `lt_toClass_congr_of_eqOn` (proved,
  `ZDataMup/localTate_reciprocityFamily.lean`) and the alternation.
-/

open scoped Pointwise

namespace Work.SSGRoute.ZDataMup

open _root_.SSGRoute
open Work.SSGRoute.ZDataMup.OddForm
open Work.SSGRoute.ZDataMup.LTRecFamHonest

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

variable {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] [IsAlgClosed Ω]
  {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
  [IsSepClosure ↥K Ω]
  [DistribMulAction (K ≃ₐ[k] K) (ZMod p)] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]

/-- **Symmetry of the `•`-form of `k`-conjugacy of places.**  If `B = τ • A` is expressed as
`∀ x, x ∈ B ↔ τ⁻¹ • x ∈ A`, then `A = τ⁻¹ • B` is expressed in the same shape.  This is the
bookkeeping used to derive the pairwise non-`K`-conjugacy of `S ∪ {Zi, ZN}`. -/
theorem swz_mem_conj_symm {A B : ValuationSubring Ω} {τ : Ω ≃ₐ[k] Ω}
    (h : ∀ x : Ω, x ∈ B ↔ (τ⁻¹ : Ω ≃ₐ[k] Ω) • x ∈ A) :
    ∀ x : Ω, x ∈ A ↔ ((τ⁻¹)⁻¹ : Ω ≃ₐ[k] Ω) • x ∈ B := by
  intro x
  have h' := h (τ • x)
  rw [show (τ⁻¹ : Ω ≃ₐ[k] Ω) • (τ • x) = x from by
    rw [← mul_smul, inv_mul_cancel, one_smul]] at h'
  simpa using h'.symm

/-- **The alternation of the odd-`p` local pairing**: `⟨x, x⟩_A = 0` for `p ≠ 2`.  This is the
`ZDataMup`-cone port of `ZConstruction.oPairForm_self_eq_zero` (the same proof: the local factor of
the coherent lift of `x` at the place of `x` is trivial, either because the lift is a global `p`-th
power, or by the norm argument via `aux_localImageAt_mem_localNormSubgroup_hLevel_of_notMem`). -/
theorem swz_oPairForm_self_eq_zero {A : ValuationSubring Ω} (hp : p ≠ 2) (ζ : ↥K)
    (hζ : IsPrimitiveRoot ζ p) (hA : SSGRoute.IsFinPlace k A)
    (x : hV (K := K) (p := p) (k := k) (Ω := Ω) A) :
    oPairForm (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ hA x x = 0 := by
  have hfac : oFactor (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ hA x
      (LTRecFamHonest.hLift ζ hζ A hA x) = 1 := by
    by_cases hα : LTRecFamHonest.hLift ζ hζ A hA x ∈ NK.LocalAnabelian.powSubgroup p ↥K
    · obtain ⟨c, hc⟩ := hα
      simp only [NK.LocalAnabelian.powSubgroup, MonoidHom.mem_range, powMonoidHom_apply] at hc
      refine oddLocalFactor_eq_one_of_localPowClass_eq_one (K := K) (p := p) (k := k) (Ω := Ω)
        ζ hζ hA x _ ?_
      rw [← hc]
      show QuotientGroup.mk' (NK.UchidaKummer.ellPowSubgroup
          ((oddPrime (K := K) A hA).adicCompletion ↥K) p)
          (Units.map (algebraMap ↥K ((oddPrime (K := K) A hA).adicCompletion ↥K)).toMonoidHom
            (c ^ p)) = 1
      rw [map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact ⟨Units.map (algebraMap ↥K ((oddPrime (K := K) A hA).adicCompletion ↥K)).toMonoidHom c,
        by rw [powMonoidHom_apply]⟩
    · have hAK : A.comap (algebraMap ↥K Ω) ≠ ⊤ :=
        Work.SSGRoute.ZConstruction.isFinPlace_of_isFinPlace_below (K := K) (A := A) hA
      haveI hfdL : FiniteDimensional ↥K
          ↥(hLevel (K := K) (Ω := Ω) (p := p) (LTRecFamHonest.hLift ζ hζ A hA x)) :=
        hLevel_finiteDimensional ζ hζ _
      haveI hgalL : IsGalois ↥K
          ↥(hLevel (K := K) (Ω := Ω) (p := p) (LTRecFamHonest.hLift ζ hζ A hA x)) :=
        hLevel_isGalois ζ hζ _
      haveI hnfL : NumberField
          ↥(hLevel (K := K) (Ω := Ω) (p := p) (LTRecFamHonest.hLift ζ hζ A hA x)) :=
        hLevel_numberField ζ hζ _
      have hcomm := hLevel_isMulCommutative (Ω := Ω) (K := K) (p := p) ζ hζ
        (LTRecFamHonest.hLift ζ hζ A hA x)
      have hmem := Work.SSGRoute.ZConstruction.aux_localImageAt_mem_localNormSubgroup_hLevel_of_notMem
        ζ hζ hp A hA hAK (LTRecFamHonest.hLift ζ hζ A hA x) hα
      have hΦ : ∀ y ∈ NK.GlobalCFT.Idele.normImage ↥K
          ↥(hLevel (K := K) (Ω := Ω) (p := p) (LTRecFamHonest.hLift ζ hζ A hA x)),
          Work.SSGRoute.ZDataMup.oddArtin (K := K)
            (hLevel (K := K) (Ω := Ω) (p := p) (LTRecFamHonest.hLift ζ hζ A hA x)) hcomm y = 1 := by
        intro y hy
        rw [NK.GlobalCFT.Idele.normImage_eq_range, MonoidHom.mem_range] at hy
        obtain ⟨z, rfl⟩ := hy
        exact Work.SSGRoute.ZDataMup.oddArtin_norm (K := K)
          (hLevel (K := K) (Ω := Ω) (p := p) (LTRecFamHonest.hLift ζ hζ A hA x)) hcomm z
      rw [show oFactor (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ hA x
            (LTRecFamHonest.hLift ζ hζ A hA x) =
          LTRecFamHonest.hLocalFactor A hA
            (hLevel (K := K) (Ω := Ω) (p := p) (LTRecFamHonest.hLift ζ hζ A hA x))
            (Work.SSGRoute.ZDataMup.oddArtin (K := K)
              (hLevel (K := K) (Ω := Ω) (p := p) (LTRecFamHonest.hLift ζ hζ A hA x)) hcomm)
            (LTRecFamHonest.hLift ζ hζ A hA x) from rfl]
      exact LTRecFamHonest.hLocalFactor_eq_one_of_mem_localNormSubgroup (K := K) hA _
        (Work.SSGRoute.ZDataMup.oddArtin (K := K)
          (hLevel (K := K) (Ω := Ω) (p := p) (LTRecFamHonest.hLift ζ hζ A hA x)) hcomm) hΦ _ hmem
  rw [oPairForm_apply]
  show (oChar (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ hA x
    (oFactor (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ hA x
      (LTRecFamHonest.hLift ζ hζ A hA x))).toAdd = 0
  rw [hfac, map_one, toAdd_one]

/-- **The `S`-terms of the localised product formula.**  Under the agreement `hagr` of the two
Kummer characters on the local groups of `S`, the pairing at every place of `S` vanishes: there the
two arguments have the same local class, and the pairing is alternating.  This is the only step of
`swZTwoPlaceReciprocity` that is not place bookkeeping. -/
theorem swz_S_term_eq_zero (hp : p ≠ 2) (ζ : ↥K) (hζ : IsPrimitiveRoot ζ p)
    (a b : (Ω ≃ₐ[k] Ω) → ZMod p)
    (ha : SSGRoute.IsCocycleOn (SSGRoute.res k K) K.fixingSubgroup a)
    (hla : SSGRoute.IsLocConstOn K.fixingSubgroup a)
    (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) K.fixingSubgroup b)
    (hlb : SSGRoute.IsLocConstOn K.fixingSubgroup b)
    (S : Finset (ValuationSubring Ω))
    (hagr : ∀ A ∈ S, ∀ σ ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup, a σ = b σ) :
    ∀ A ∈ S, ∀ hA : SSGRoute.IsFinPlace k A,
      oPairAt (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ A hA a b = 0 := by
  intro A hAS hA
  classical
  have hH : SSGRoute.decomp k A ⊓ K.fixingSubgroup ≤ K.fixingSubgroup := inf_le_right
  have hf : a ∈ Work.SSGRoute.lcCocycles p k Ω K (ZMod p)
      (SSGRoute.decomp k A ⊓ K.fixingSubgroup) := by
    refine ⟨fun g hg h hh => ha g (hH hg) h (hH hh), ?_⟩
    obtain ⟨U, hUo, hU⟩ := hla
    exact ⟨U, hUo, fun g hg u hu huH => hU g (hH hg) u hu (hH huH)⟩
  have hg : b ∈ Work.SSGRoute.lcCocycles p k Ω K (ZMod p)
      (SSGRoute.decomp k A ⊓ K.fixingSubgroup) := by
    refine ⟨fun g hg h hh => hb g (hH hg) h (hH hh), ?_⟩
    obtain ⟨U, hUo, hU⟩ := hlb
    exact ⟨U, hUo, fun g hg u hu huH => hU g (hH hg) u hu (hH huH)⟩
  have hsub : a - b ∈ Work.SSGRoute.lcCocycles p k Ω K (ZMod p)
      (SSGRoute.decomp k A ⊓ K.fixingSubgroup) := Submodule.sub_mem _ hf hg
  have hcob : a - b ∈ Work.SSGRoute.coboundaries p k Ω K (ZMod p)
      (SSGRoute.decomp k A ⊓ K.fixingSubgroup) :=
    ⟨0, fun g hg' => by rw [Pi.sub_apply, hagr A hAS g hg']; simp⟩
  have hzero : Work.SSGRoute.toClass p k Ω K (ZMod p)
      (SSGRoute.decomp k A ⊓ K.fixingSubgroup) (a - b) = 0 :=
    (Work.SSGRoute.toClass_eq_zero_iff p k Ω K (ZMod p)
      (SSGRoute.decomp k A ⊓ K.fixingSubgroup) hsub).mpr hcob
  have hcls : Work.SSGRoute.toClass p k Ω K (ZMod p)
        (SSGRoute.decomp k A ⊓ K.fixingSubgroup) a =
      Work.SSGRoute.toClass p k Ω K (ZMod p)
        (SSGRoute.decomp k A ⊓ K.fixingSubgroup) b := by
    have hdec : a = b + (a - b) := by funext σ; simp
    rw [hdec, Work.SSGRoute.toClass_add p k Ω K (ZMod p)
      (SSGRoute.decomp k A ⊓ K.fixingSubgroup) hg hsub, hzero, add_zero]
  rw [show oPairAt (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ A hA a b =
      oPairForm (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ hA
        (Work.SSGRoute.toClass p k Ω K (ZMod p)
          (SSGRoute.decomp k A ⊓ K.fixingSubgroup) a)
        (Work.SSGRoute.toClass p k Ω K (ZMod p)
          (SSGRoute.decomp k A ⊓ K.fixingSubgroup) b) from rfl, hcls]
  exact swz_oPairForm_self_eq_zero (K := K) hp ζ hζ hA _

/-- **The collapse of the product formula to the two escape terms**, given the vanishing of the
`S`-terms.  This is the whole of `swZTwoPlaceReciprocity` except for the arithmetic input
`swz_S_term_eq_zero`. -/
theorem swZTwoPlaceReciprocity_of_Szero (hp : p ≠ 2) (ζ : ↥K) (hζ : IsPrimitiveRoot ζ p)
    (a b : (Ω ≃ₐ[k] Ω) → ZMod p) (α β : (↥K)ˣ)
    (ha : SSGRoute.IsCocycleOn (SSGRoute.res k K) K.fixingSubgroup a)
    (hla : SSGRoute.IsLocConstOn K.fixingSubgroup a)
    (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) K.fixingSubgroup b)
    (hlb : SSGRoute.IsLocConstOn K.fixingSubgroup b)
    (hα : ∀ (σ : Ω ≃ₐ[k] Ω) (hσ : σ ∈ K.fixingSubgroup),
      a σ = Work.SSGRoute.kummerCharZMod (Ω := Ω) (K := ↥K) p (ζ := ζ) hζ α
        ((IntermediateField.fixingSubgroupEquiv K) ⟨σ, hσ⟩))
    (hβ : ∀ (σ : Ω ≃ₐ[k] Ω) (hσ : σ ∈ K.fixingSubgroup),
      b σ = Work.SSGRoute.kummerCharZMod (Ω := Ω) (K := ↥K) p (ζ := ζ) hζ β
        ((IntermediateField.fixingSubgroupEquiv K) ⟨σ, hσ⟩))
    (S : Finset (ValuationSubring Ω)) (hSfin : ∀ A ∈ S, SSGRoute.IsFinPlace k A)
    (hSdisj : ∀ A ∈ S, ∀ B ∈ S,
      (∃ τ ∈ K.fixingSubgroup, ∀ x : Ω, x ∈ B ↔ (τ⁻¹ : Ω ≃ₐ[k] Ω) • x ∈ A) → A = B)
    (Zi ZN : ValuationSubring Ω) (hZi : SSGRoute.IsFinPlace k Zi)
    (hZN : SSGRoute.IsFinPlace k ZN)
    (hZiS : ∀ A ∈ S, ¬ ∃ τ ∈ K.fixingSubgroup, ∀ x : Ω, x ∈ Zi ↔ (τ⁻¹ : Ω ≃ₐ[k] Ω) • x ∈ A)
    (hZNS : ∀ A ∈ S, ¬ ∃ τ ∈ K.fixingSubgroup, ∀ x : Ω, x ∈ ZN ↔ (τ⁻¹ : Ω ≃ₐ[k] Ω) • x ∈ A)
    (hZiN : ¬ ∃ τ ∈ K.fixingSubgroup, ∀ x : Ω, x ∈ Zi ↔ (τ⁻¹ : Ω ≃ₐ[k] Ω) • x ∈ ZN)
    (hunr : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∀ A ∈ S, ¬ ∃ τ ∈ K.fixingSubgroup, ∀ x : Ω, x ∈ B ↔ (τ⁻¹ : Ω ≃ₐ[k] Ω) • x ∈ A) →
      (¬ ∃ τ ∈ K.fixingSubgroup, ∀ x : Ω, x ∈ B ↔ (τ⁻¹ : Ω ≃ₐ[k] Ω) • x ∈ Zi) →
      (¬ ∃ τ ∈ K.fixingSubgroup, ∀ x : Ω, x ∈ B ↔ (τ⁻¹ : Ω ≃ₐ[k] Ω) • x ∈ ZN) →
      ∀ σ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k B σ → a σ = 0 ∧ b σ = 0)
    (hSz : ∀ A ∈ S, ∀ hA : SSGRoute.IsFinPlace k A,
      oPairAt (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ A hA a b = 0) :
    oPairAt (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ Zi hZi a b
      + oPairAt (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ ZN hZN a b = 0 := by
  classical
  -- ## The enlarged place set `T' = S ∪ {Zi, ZN}`
  set T' : Finset (ValuationSubring Ω) := S ∪ ({Zi, ZN} : Finset (ValuationSubring Ω)) with hT'def
  have hmemT' : ∀ A : ValuationSubring Ω, A ∈ T' ↔ A ∈ S ∨ A = Zi ∨ A = ZN := by
    intro A
    rw [hT'def, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
  have hZi_notin_S : Zi ∉ S := fun h =>
    hZiS Zi h ⟨1, K.fixingSubgroup.one_mem, fun x => by simp⟩
  have hZN_notin_S : ZN ∉ S := fun h =>
    hZNS ZN h ⟨1, K.fixingSubgroup.one_mem, fun x => by simp⟩
  have hZiZN : Zi ≠ ZN := fun h =>
    hZiN ⟨1, K.fixingSubgroup.one_mem, fun x => by simp [h]⟩
  have hTfin : ∀ A ∈ T', SSGRoute.IsFinPlace k A := by
    intro A hA
    rcases (hmemT' A).mp hA with h | h | h
    · exact hSfin A h
    · rw [h]; exact hZi
    · rw [h]; exact hZN
  have hTdisj : ∀ A ∈ T', ∀ B ∈ T',
      (∃ τ ∈ K.fixingSubgroup, ∀ x : Ω, x ∈ B ↔ (τ⁻¹ : Ω ≃ₐ[k] Ω) • x ∈ A) → A = B := by
    intro A hA B hB hconj
    rcases (hmemT' A).mp hA with hA1 | rfl | rfl
    · rcases (hmemT' B).mp hB with hB1 | rfl | rfl
      · exact hSdisj A hA1 B hB1 hconj
      · exact absurd hconj (hZiS A hA1)
      · exact absurd hconj (hZNS A hA1)
    · rcases (hmemT' B).mp hB with hB1 | rfl | rfl
      · obtain ⟨τ, hτ, hτeq⟩ := hconj
        exact absurd ⟨τ⁻¹, K.fixingSubgroup.inv_mem hτ, swz_mem_conj_symm hτeq⟩ (hZiS B hB1)
      · rfl
      · obtain ⟨τ, hτ, hτeq⟩ := hconj
        exact absurd ⟨τ⁻¹, K.fixingSubgroup.inv_mem hτ, swz_mem_conj_symm hτeq⟩ hZiN
    · rcases (hmemT' B).mp hB with hB1 | rfl | rfl
      · obtain ⟨τ, hτ, hτeq⟩ := hconj
        exact absurd ⟨τ⁻¹, K.fixingSubgroup.inv_mem hτ, swz_mem_conj_symm hτeq⟩ (hZNS B hB1)
      · obtain ⟨τ, hτ, hτeq⟩ := hconj
        exact absurd ⟨τ, hτ, hτeq⟩ hZiN
      · rfl
  -- ## Unramifiedness outside `T'`
  have hunrT : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∀ A ∈ T', ¬ ∃ τ ∈ K.fixingSubgroup, ∀ x : Ω, x ∈ B ↔ (τ⁻¹ : Ω ≃ₐ[k] Ω) • x ∈ A) →
      ∀ σ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k B σ → a σ = 0 ∧ b σ = 0 := by
    intro B hB hnc σ hI
    refine hunr B hB (fun A hA hc => hnc A ((hmemT' A).mpr (Or.inl hA)) hc)
      (fun hc => hnc Zi ((hmemT' Zi).mpr (Or.inr (Or.inl rfl))) hc)
      (fun hc => hnc ZN ((hmemT' ZN).mpr (Or.inr (Or.inr rfl))) hc) σ hI
  -- ## The local factors are trivial outside `T'`
  have hout : ∀ v : NK.GlobalCFT.Place ↥K,
      (∀ A ∈ T'.attach, NK.GlobalCFT.Place.ofFinite
        (oddPrime (K := K) A.1 (hTfin A.1 A.2)) ≠ v) →
      oTheta (K := K) (p := p) ζ hζ α β v = 1 :=
    fun v hv => oTheta_eq_one_of_ne_oddPrime (p := p) hp (K := K) ζ hζ a b α β hα hβ
      T' hTfin hunrT v hv
  -- ## The product formula over `T'`
  have hsum0 : ∑ A ∈ T'.attach,
      oPairAt (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ A.1 (hTfin A.1 A.2) a b = 0 :=
    oPairForm_sum_attach_eq_zero_of_outside (K := K) (p := p) (k := k) (Ω := Ω)
      ζ hζ a b α β ha hla hb hlb hα hβ T' hTfin hTdisj hout
  -- ## Reduction of the sum to the two escape terms
  have hpair_eq : (∑ A ∈ T'.attach,
        oPairAt (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ A.1 (hTfin A.1 A.2) a b)
      = oPairAt (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ Zi
          (hTfin Zi ((hmemT' Zi).mpr (Or.inr (Or.inl rfl)))) a b
        + oPairAt (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ ZN
          (hTfin ZN ((hmemT' ZN).mpr (Or.inr (Or.inr rfl)))) a b := by
    let xi : {A : ValuationSubring Ω // A ∈ T'} :=
      ⟨Zi, (hmemT' Zi).mpr (Or.inr (Or.inl rfl))⟩
    let xN : {A : ValuationSubring Ω // A ∈ T'} :=
      ⟨ZN, (hmemT' ZN).mpr (Or.inr (Or.inr rfl))⟩
    let s : Finset {A : ValuationSubring Ω // A ∈ T'} := {xi, xN}
    have hs_sub : s ⊆ T'.attach := by
      intro x hx
      simp only [s, Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with h | h
      · rw [h]; exact Finset.mem_attach T' xi
      · rw [h]; exact Finset.mem_attach T' xN
    have hzero_off : ∀ x ∈ T'.attach, x ∉ s →
        oPairAt (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ x.1
          (hTfin x.1 x.2) a b = 0 := by
      intro x _ hx
      rcases (hmemT' x.1).mp x.2 with h | h | h
      · exact hSz x.1 h (hTfin x.1 x.2)
      · exfalso
        apply hx
        simp only [s, Finset.mem_insert, Finset.mem_singleton]
        exact Or.inl (Subtype.ext h)
      · exfalso
        apply hx
        simp only [s, Finset.mem_insert, Finset.mem_singleton]
        exact Or.inr (Subtype.ext h)
    have hsum_pair : (∑ x ∈ s, oPairAt (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ x.1
        (hTfin x.1 x.2) a b) = (∑ x ∈ T'.attach,
        oPairAt (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ x.1 (hTfin x.1 x.2) a b) :=
      Finset.sum_subset hs_sub hzero_off
    have hsval : (∑ x ∈ s, oPairAt (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ x.1
        (hTfin x.1 x.2) a b)
        = oPairAt (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ Zi
            (hTfin Zi ((hmemT' Zi).mpr (Or.inr (Or.inl rfl)))) a b
          + oPairAt (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ ZN
            (hTfin ZN ((hmemT' ZN).mpr (Or.inr (Or.inr rfl)))) a b := by
      have hne : xi ≠ xN := by
        intro h
        exact hZiZN (Subtype.ext_iff.mp h)
      rw [show s = insert xi {xN} from rfl, Finset.sum_insert (by
        simp only [Finset.mem_singleton]; exact hne), Finset.sum_singleton]
    rw [← hsum_pair, hsval]
  rw [hpair_eq] at hsum0
  have hZi' : oPairAt (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ Zi
      (hTfin Zi ((hmemT' Zi).mpr (Or.inr (Or.inl rfl)))) a b
      = oPairAt (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ Zi hZi a b :=
    congrArg (fun hh => oPairAt (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ Zi hh a b)
      (Subsingleton.elim _ _)
  have hZN' : oPairAt (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ ZN
      (hTfin ZN ((hmemT' ZN).mpr (Or.inr (Or.inr rfl)))) a b
      = oPairAt (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ ZN hZN a b :=
    congrArg (fun hh => oPairAt (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ ZN hh a b)
      (Subsingleton.elim _ _)
  rw [hZi', hZN'] at hsum0
  exact hsum0

/-- **The two-place reciprocity (localised product formula at the two escape classes).** -/
theorem swZTwoPlaceReciprocity (hp : p ≠ 2) (ζ : ↥K) (hζ : IsPrimitiveRoot ζ p)
    (a b : (Ω ≃ₐ[k] Ω) → ZMod p) (α β : (↥K)ˣ)
    (ha : SSGRoute.IsCocycleOn (SSGRoute.res k K) K.fixingSubgroup a)
    (hla : SSGRoute.IsLocConstOn K.fixingSubgroup a)
    (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) K.fixingSubgroup b)
    (hlb : SSGRoute.IsLocConstOn K.fixingSubgroup b)
    (hα : ∀ (σ : Ω ≃ₐ[k] Ω) (hσ : σ ∈ K.fixingSubgroup),
      a σ = Work.SSGRoute.kummerCharZMod (Ω := Ω) (K := ↥K) p (ζ := ζ) hζ α
        ((IntermediateField.fixingSubgroupEquiv K) ⟨σ, hσ⟩))
    (hβ : ∀ (σ : Ω ≃ₐ[k] Ω) (hσ : σ ∈ K.fixingSubgroup),
      b σ = Work.SSGRoute.kummerCharZMod (Ω := Ω) (K := ↥K) p (ζ := ζ) hζ β
        ((IntermediateField.fixingSubgroupEquiv K) ⟨σ, hσ⟩))
    (S : Finset (ValuationSubring Ω)) (hSfin : ∀ A ∈ S, SSGRoute.IsFinPlace k A)
    (hSdisj : ∀ A ∈ S, ∀ B ∈ S,
      (∃ τ ∈ K.fixingSubgroup, ∀ x : Ω, x ∈ B ↔ (τ⁻¹ : Ω ≃ₐ[k] Ω) • x ∈ A) → A = B)
    (Zi ZN : ValuationSubring Ω) (hZi : SSGRoute.IsFinPlace k Zi)
    (hZN : SSGRoute.IsFinPlace k ZN)
    (hZiS : ∀ A ∈ S, ¬ ∃ τ ∈ K.fixingSubgroup, ∀ x : Ω, x ∈ Zi ↔ (τ⁻¹ : Ω ≃ₐ[k] Ω) • x ∈ A)
    (hZNS : ∀ A ∈ S, ¬ ∃ τ ∈ K.fixingSubgroup, ∀ x : Ω, x ∈ ZN ↔ (τ⁻¹ : Ω ≃ₐ[k] Ω) • x ∈ A)
    (hZiN : ¬ ∃ τ ∈ K.fixingSubgroup, ∀ x : Ω, x ∈ Zi ↔ (τ⁻¹ : Ω ≃ₐ[k] Ω) • x ∈ ZN)
    (hagr : ∀ A ∈ S, ∀ σ ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup, a σ = b σ)
    (hunr : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∀ A ∈ S, ¬ ∃ τ ∈ K.fixingSubgroup, ∀ x : Ω, x ∈ B ↔ (τ⁻¹ : Ω ≃ₐ[k] Ω) • x ∈ A) →
      (¬ ∃ τ ∈ K.fixingSubgroup, ∀ x : Ω, x ∈ B ↔ (τ⁻¹ : Ω ≃ₐ[k] Ω) • x ∈ Zi) →
      (¬ ∃ τ ∈ K.fixingSubgroup, ∀ x : Ω, x ∈ B ↔ (τ⁻¹ : Ω ≃ₐ[k] Ω) • x ∈ ZN) →
      ∀ σ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k B σ → a σ = 0 ∧ b σ = 0) :
    oPairAt (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ Zi hZi a b
      + oPairAt (K := K) (p := p) (k := k) (Ω := Ω) ζ hζ ZN hZN a b = 0 :=
  swZTwoPlaceReciprocity_of_Szero (p := p) (K := K) hp ζ hζ a b α β ha hla hb hlb hα hβ
    S hSfin hSdisj Zi ZN hZi hZN hZiS hZNS hZiN hunr
    (swz_S_term_eq_zero (p := p) (K := K) hp ζ hζ a b ha hla hb hlb S hagr)

end Work.SSGRoute.ZDataMup
