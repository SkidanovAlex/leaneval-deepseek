import Mathlib
import Submission.Work.CFTLib.ShafDeps
import Submission.Work.CFTLib.Basic
import Submission.Work.CFTLib.ProP.Galois
import Submission.Work.CFTLib.ProP.le_maximalUnramifiedProPF
import Submission.Work.CFTLib.ProP.isUnramifiedAtInfinitePlaces_sup
import Submission.Work.CFTLib.ConjSup.isUnramifiedConjSup
import Submission.Work.CFTLib.ConjSup.finiteDimensional_isGalois
import Submission.Work.CFTLib.ConjSup.isPGroupPow
import Submission.Work.CFTLib.Transport.isUnramified_algEquiv
import Submission.Work.CFTLib.Unramified.isEverywhereUnramified_iff
import Submission.Work.Tower.TowerCut.Transfer
import Submission.Work.CFTLib.InfinitePlace.isUnramifiedAtInfinitePlaces_iSup

namespace Work.CFTLib.ProP

open NumberField
open scoped Classical

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

noncomputable section

/-- **Every finite Galois subfield of `F^{un,p}`, presented over `F^{un,p}` itself, is an
everywhere-unramified `p`-extension of `F`.**

This is an inlined copy of `Work.CFTLib.ProP.isUnramified_isPGroup_of_le` (which lives in the
forbidden module `maxAbelianSubextension`): it is proved from the imported
`le_maximalUnramifiedProPF` by mapping `K` into `AlgebraicClosure F` along `(E F p).val`. -/
theorem isUnramified_isPGroup_of_le_sc (F : Type) [Field F] [NumberField F] (p : ℕ)
    [Fact (Nat.Prime p)]
    (K : IntermediateField F ↥(E F p)) [FiniteDimensional F K] [IsGalois F K]
    [NumberField ↥K] :
    CFTLib.IsUnramified F ↥K ∧ IsPGroup p (↥K ≃ₐ[F] ↥K) := by
  let M : IntermediateField F (AlgebraicClosure F) := K.map (E F p).val
  have hMle : M ≤ E F p := by
    intro x hx
    rw [IntermediateField.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact y.2
  let e : ↥K ≃ₐ[F] ↥M := IntermediateField.equivMap K (E F p).val
  haveI hfd : FiniteDimensional F ↥M := Module.Finite.equiv e.toLinearEquiv
  haveI hgal : IsGalois F ↥M := IsGalois.of_algEquiv e
  haveI hnf : NumberField ↥M := NumberField.of_module_finite F ↥M
  obtain ⟨hunr, hp⟩ := le_maximalUnramifiedProPF F p M hMle
  refine ⟨?_, ?_⟩
  · exact Work.CFTLib.Transport.isUnramified_algEquiv e.symm
      ((Work.CFTLib.Unramified.isEverywhereUnramified_iff F ↥M).mp hunr)
  · exact IsPGroup.of_equiv hp (AlgEquiv.autCongr e).symm

/-- **Every finite Galois abelian unramified `p`-extension of `K` embeds into `F^{un,p}` over `K`**
(self-contained copy).

This has the same statement as `Work.CFTLib.ProP.embeds_abelian_unramifiedP` in
`Submission/Work/CFTLib/ProP/embeds_abelian_unramifiedP.lean`, which is **already proved** there; that
file imports `Submission.Work.CFTLib.ProP.maxAbelianSubextension`, so importing it from that module
would create an import cycle — hence this copy must be proved *without* importing
`Submission.Work.CFTLib.ProP.maxAbelianSubextension`.  The existing proof in the sibling file
(`Submission/Work/CFTLib/ProP/embeds_abelian_unramifiedP.lean`, one self-contained 250-line proof,
with no auxiliary declarations) is a good reference and is expected to adapt directly.

The only auxiliary result of that sibling's dependency closure that lives in the forbidden module is
`Work.CFTLib.ProP.isUnramified_isPGroup_of_le`: for a finite Galois intermediate field `K` of
`F^{un,p}` over `F` it gives `CFTLib.IsUnramified F ↥K ∧ IsPGroup p (↥K ≃ₐ[F] ↥K)`, proved from the
imported `le_maximalUnramifiedProPF` by mapping `K` into `AlgebraicClosure F` along
`(↥(maximalUnramifiedProPF F p)).val` (`IntermediateField.map`, `IntermediateField.equivMap`,
transported by `Work.CFTLib.Transport.isUnramified_algEquiv` and `AlgEquiv.autCongr`).  Please
inline your own copy of that (it is about fifteen lines).

Setting: `F` a number field, `p` a prime, `E = F^{un,p} = maximalUnramifiedProPF F p`,
`K : IntermediateField F ↥E` finite Galois over `F` and unramified over `F` (hypothesis `hKunr`),
and `L/K` an abstract finite Galois abelian `p`-extension, unramified over `K`.  Conclusion: there
is a finite intermediate field `M` of `E/K` (an `↥K`-intermediate field of `↥E`) which is finite
Galois over `K`, abelian, `p`-group and unramified over `K`, with `L` embedding into `M` over `K`. -/
theorem embeds_abelian_unramifiedP_sc
    (F : Type) [Field F] [NumberField F] (p : ℕ) [Fact (Nat.Prime p)]
    (K : IntermediateField F ↥(LeanEval.NumberTheory.maximalUnramifiedProPF F p))
    [FiniteDimensional F K] [IsGalois F K] [NumberField ↥K]
    (hKunr : CFTLib.IsUnramified F ↥K)
    (L : Type) [Field L] [NumberField L] [Algebra ↥K L] [FiniteDimensional ↥K L] [IsGalois ↥K L]
    (hLcom : ∀ a b : L ≃ₐ[↥K] L, a * b = b * a) (hLp : IsPGroup p (L ≃ₐ[↥K] L))
    (hLunr : CFTLib.IsUnramified ↥K L) :
    ∃ (M : IntermediateField ↥K ↥(LeanEval.NumberTheory.maximalUnramifiedProPF F p))
      (_ : NumberField ↥M),
      FiniteDimensional ↥K M ∧ IsGalois ↥K M ∧
      (∀ a b : ↥M ≃ₐ[↥K] ↥M, a * b = b * a) ∧ IsPGroup p (↥M ≃ₐ[↥K] ↥M) ∧
      CFTLib.IsUnramified ↥K ↥M ∧ Nonempty (L →ₐ[↥K] ↥M) := by
  classical
  -- ### 0. F-algebra structure on L
  letI : Algebra F L := Algebra.compHom L (algebraMap F ↥K)
  haveI hST1 : IsScalarTower F ↥K L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI hfdFL : FiniteDimensional F L := Module.Finite.trans ↥K L
  -- ### 1. unramifiedness up the tower, degree data
  have hunrKF : Work.Tower.IsUnramifiedExtensionForallPrimes F ↥K :=
    Work.CFTLib.forallPrimes_of_isUnramified hKunr
  have hunrKL : Work.Tower.IsUnramifiedExtensionForallPrimes ↥K L :=
    Work.CFTLib.forallPrimes_of_isUnramified hLunr
  have hunrFL : Work.Tower.IsUnramifiedExtensionForallPrimes F L := by
    intro 𝔓 h𝔓
    haveI := h𝔓
    have hh : 𝔓.ramificationIdx (𝓞 F) =
        (𝔓.under (𝓞 ↥K)).ramificationIdx (𝓞 F) * 𝔓.ramificationIdx (𝓞 ↥K) :=
      Ideal.ramificationIdx_tower (R := 𝓞 F) (S := 𝓞 ↥K) (T := 𝓞 L) (q := 𝔓.under (𝓞 ↥K)) (r := 𝔓)
    rw [hh, hunrKF _ (inferInstance : (𝔓.under (𝓞 ↥K)).IsPrime), hunrKL 𝔓 h𝔓, one_mul]
  have hinfFL : IsUnramifiedAtInfinitePlaces F L := by
    haveI : IsUnramifiedAtInfinitePlaces F ↥K := hKunr.2
    haveI : IsUnramifiedAtInfinitePlaces ↥K L := hLunr.2
    exact IsUnramifiedAtInfinitePlaces.trans F ↥K L
  obtain ⟨-, hKpGal⟩ := isUnramified_isPGroup_of_le_sc F p K
  haveI : Finite (↥K ≃ₐ[F] ↥K) := inferInstance
  obtain ⟨j, hj⟩ := (IsPGroup.iff_card).mp hKpGal
  have hKdeg : Module.finrank F ↥K = p ^ j := by
    rw [← IsGalois.card_aut_eq_finrank F ↥K, hj]
  haveI : Finite (L ≃ₐ[↥K] L) := inferInstance
  obtain ⟨m, hm⟩ := (IsPGroup.iff_card).mp hLp
  have hLdegK : Module.finrank ↥K L = p ^ m := by
    rw [← IsGalois.card_aut_eq_finrank ↥K L, hm]
  -- ### 2. the embedding ψ, its image AF, and K'
  haveI : Module.IsTorsionFree ↥K L := inferInstance
  haveI : Module.IsTorsionFree ↥K (AlgebraicClosure F) := inferInstance
  haveI hAlgK : Algebra.IsAlgebraic ↥K L := Algebra.IsAlgebraic.of_finite ↥K L
  let ψ : L →ₐ[↥K] AlgebraicClosure F := IsAlgClosed.lift
  let ψF : L →ₐ[F] AlgebraicClosure F := ψ.restrictScalars F
  let AF : IntermediateField F (AlgebraicClosure F) := ψF.fieldRange
  haveI hAFfd : FiniteDimensional F ↥AF :=
    LinearEquiv.finiteDimensional ψF.equivFieldRange.toLinearEquiv
  haveI hAFnf : NumberField ↥AF := NumberField.of_module_finite F ↥AF
  let K' : IntermediateField F (AlgebraicClosure F) := K.map (E F p).val
  haveI hK'fd : FiniteDimensional F ↥K' :=
    LinearEquiv.finiteDimensional (IntermediateField.equivMap K (E F p).val).toLinearEquiv
  haveI hK'nf : NumberField ↥K' := NumberField.of_module_finite F ↥K'
  haveI hK'gal : IsGalois F ↥K' :=
    IsGalois.of_algEquiv (IntermediateField.equivMap K (E F p).val)
  let eK : ↥K ≃ₐ[F] ↥K' := IntermediateField.equivMap K (E F p).val
  have hmemAF : ∀ x : L, ψ x ∈ (AF : Set (AlgebraicClosure F)) :=
    fun x => (AlgHom.mem_fieldRange (f := ψF)).mpr ⟨x, rfl⟩
  -- the pullback ↥K'-algebra structure on L, and the ↥K'-linear embedding ψK'
  letI : Algebra ↥K' L := Algebra.compHom L eK.symm.toRingHom
  have key : ∀ z : ↥K, algebraMap ↥K (AlgebraicClosure F) z =
      algebraMap ↥K' (AlgebraicClosure F) (eK z) := by
    intro z
    have h1 : algebraMap ↥K' (AlgebraicClosure F) (eK z) =
        (↑(IntermediateField.equivMap K (E F p).val z) : ↥(K.map (E F p).val)) := by
      rw [show algebraMap ↥K' (AlgebraicClosure F) (eK z) = K'.val (eK z) from rfl]
      rw [show eK z = (IntermediateField.equivMap K (E F p).val) z from rfl]
      exact congrFun (IntermediateField.coe_val K')
        (IntermediateField.equivMap K (E F p).val z)
    rw [h1, IntermediateField.coe_equivMap_apply (L := K) (f := (E F p).val) z]
    rfl
  have hψK'lin : ∀ k' : ↥K', ψ (algebraMap ↥K' L k') = algebraMap ↥K' (AlgebraicClosure F) k' := by
    intro k'
    rw [Algebra.compHom_algebraMap_apply, ψ.commutes]
    have h1 : algebraMap ↥K (AlgebraicClosure F) (eK.symm k') =
        algebraMap ↥K' (AlgebraicClosure F) k' := by
      rw [key (eK.symm k'), AlgEquiv.apply_symm_apply]
    exact h1
  let ψK' : L →ₐ[↥K'] AlgebraicClosure F :=
    { (ψ : L →+* AlgebraicClosure F) with commutes' := hψK'lin }
  let L' : IntermediateField ↥K' (AlgebraicClosure F) := ψK'.fieldRange
  have eK' : L ≃ₐ[↥K'] ↥L' := ψK'.equivFieldRange
  have hL'set : (AF : Set (AlgebraicClosure F)) = (L' : Set (AlgebraicClosure F)) := by ext x; rfl
  have hmemL' : ∀ x : L, ψF x ∈ (L' : Set (AlgebraicClosure F)) :=
    fun x => (Set.ext_iff.mp hL'set (ψF x)).mpr (hmemAF x)
  have hmemAF' : ∀ y : ↥L', y.1 ∈ (AF : Set (AlgebraicClosure F)) :=
    fun y => (Set.ext_iff.mp hL'set y.1).symm.mpr y.2
  haveI hL'galK' : IsGalois ↥K' L := by
    refine IsGalois.of_equiv_equiv (F := ↥K) (E := L) (M := ↥K') (N := L)
      (f := eK.toRingEquiv) (g := RingEquiv.refl L) ?_
    refine RingHom.ext fun x => ?_
    show algebraMap ↥K' L (eK x) = algebraMap ↥K L x
    rw [Algebra.compHom_algebraMap_apply]
    exact congrArg (algebraMap ↥K L) (AlgEquiv.symm_apply_apply eK x)
  have hL'gal : IsGalois ↥K' ↥L' := IsGalois.of_algEquiv eK'
  letI : Algebra F ↥L' := inferInstanceAs (Algebra F ↥(L'.restrictScalars F))
  have hL'd : Module.finrank F ↥L' = Module.finrank F ↥AF := by
    have h : (L'.restrictScalars F) = AF := by ext x; rfl
    show Module.finrank F ↥(L'.restrictScalars F) = Module.finrank F ↥AF
    rw [h]
  haveI hL'fdF : FiniteDimensional F ↥L' :=
    FiniteDimensional.of_finrank_pos (by rw [hL'd]; exact Module.finrank_pos)
  haveI hL'nf : NumberField ↥L' := NumberField.of_module_finite F ↥L'
  have eF : L ≃ₐ[F] ↥L' := AlgEquiv.ofBijective
    ({ toFun := fun x => ⟨ψF x, hmemL' x⟩
       map_one' := Subtype.ext (map_one ψF)
       map_mul' := fun x y => Subtype.ext (map_mul ψF x y)
       map_zero' := Subtype.ext (map_zero ψF)
       map_add' := fun x y => Subtype.ext (map_add ψF x y)
       commutes' := fun c => by
         refine Subtype.ext ?_
         show ψF (algebraMap F L c) = algebraMap F (AlgebraicClosure F) c
         rw [show algebraMap F L c = algebraMap ↥K L (algebraMap F ↥K c) from
           (IsScalarTower.algebraMap_apply F ↥K L c).symm]
         rw [show ψF (algebraMap ↥K L (algebraMap F ↥K c)) =
             ψ (algebraMap ↥K L (algebraMap F ↥K c)) from rfl, ψ.commutes,
           ← IsScalarTower.algebraMap_apply F ↥K (AlgebraicClosure F) c] } : L →ₐ[F] ↥L')
    ⟨fun x y h => by
       have h3 : ψF x = ψF y := by
         have h2 : (⟨ψF x, hmemL' x⟩ : ↥L') = ⟨ψF y, hmemL' y⟩ := h
         exact congrArg (fun z : ↥L' => (z : AlgebraicClosure F)) h2
       exact ψF.injective h3,
     fun y => ⟨(ψF.equivFieldRange.symm ⟨y.1, hmemAF' y⟩ : L), by
        refine Subtype.ext ?_
        exact congrArg Subtype.val (ψF.equivFieldRange.apply_symm_apply ⟨y.1, hmemAF' y⟩)⟩⟩
  -- ### 4. degree [L' : K'] = p^m
  have hAFdeg : Module.finrank F ↥AF = p ^ (j + m) := by
    have h1 : Module.finrank F ↥AF = Module.finrank F L :=
      (LinearEquiv.finrank_eq ψF.equivFieldRange.toLinearEquiv).symm
    have h2 : Module.finrank F L = Module.finrank F ↥K * Module.finrank ↥K L :=
      (Module.finrank_mul_finrank F ↥K L).symm
    rw [h1, h2, hKdeg, hLdegK, ← pow_add]
  have hK'deg : Module.finrank F ↥K' = p ^ j :=
    (LinearEquiv.finrank_eq eK.toLinearEquiv).symm.trans hKdeg
  have hL'finrank : Module.finrank ↥K' ↥L' = p ^ m := by
    have htower := Module.finrank_mul_finrank F ↥K' ↥L'
    rw [hK'deg, hL'd, hAFdeg, pow_add] at htower
    exact Nat.mul_left_cancel (pow_pos (Fact.out : p.Prime).pos j) htower
  haveI hL'fd : FiniteDimensional ↥K' ↥L' :=
    FiniteDimensional.of_finrank_pos (by rw [hL'finrank]; exact pow_pos (Fact.out : p.Prime).pos m)
  have hL'deg : ∃ m' : ℕ, Module.finrank ↥K' ↥L' = p ^ m' := ⟨m, hL'finrank⟩
  -- ### 5. unramifiedness of L'/K'
  have hK'unrF : Work.Tower.IsUnramifiedExtensionForallPrimes F ↥K' :=
    Work.Tower.TowerCut.isUnramifiedExtensionForallPrimes_of_algEquiv eK hunrKF
  have hK'infF : IsUnramifiedAtInfinitePlaces F ↥K' :=
    Work.CFTLib.Transport.unramifiedAtInfinitePlaces_algEquiv eK hKunr.2
  have hK'p : IsPGroup p (↥K' ≃ₐ[F] ↥K') := IsPGroup.of_equiv hKpGal (AlgEquiv.autCongr eK)
  have hL'unrF : Work.Tower.IsUnramifiedExtensionForallPrimes F ↥L' :=
    Work.Tower.TowerCut.isUnramifiedExtensionForallPrimes_of_algEquiv eF hunrFL
  have hL'infF : IsUnramifiedAtInfinitePlaces F ↥L' :=
    Work.CFTLib.Transport.unramifiedAtInfinitePlaces_algEquiv eF hinfFL
  have hL'unr : Work.Tower.IsUnramifiedExtensionForallPrimes ↥K' ↥L' := by
    intro 𝔓 h𝔓
    haveI := h𝔓
    have hh : 𝔓.ramificationIdx (𝓞 F) =
        (𝔓.under (𝓞 ↥K')).ramificationIdx (𝓞 F) * 𝔓.ramificationIdx (𝓞 ↥K') :=
      Ideal.ramificationIdx_tower (R := 𝓞 F) (S := 𝓞 ↥K') (T := 𝓞 ↥L')
        (q := 𝔓.under (𝓞 ↥K')) (r := 𝔓)
    have h2 : 𝔓.ramificationIdx (𝓞 ↥K') = 1 := by
      have h3 := hh
      rw [hL'unrF 𝔓 h𝔓, hK'unrF _ (inferInstance : (𝔓.under (𝓞 ↥K')).IsPrime), one_mul] at h3
      exact h3.symm
    exact h2
  have hL'inf : IsUnramifiedAtInfinitePlaces ↥K' ↥L' := by
    refine ⟨fun w => ?_⟩
    rw [InfinitePlace.isUnramified_iff]
    by_cases hw : w.IsReal
    · exact Or.inl hw
    · refine Or.inr ?_
      rw [← InfinitePlace.not_isReal_iff_isComplex]
      intro hreal
      have hFc : (w.comap (algebraMap F ↥L')).IsComplex := by
        rcases (InfinitePlace.isUnramified_iff.mp (hL'infF.isUnramified w)) with h | h
        · exact absurd h hw
        · exact h
      rw [← InfinitePlace.not_isReal_iff_isComplex] at hFc
      have hcomp : (w.comap (algebraMap ↥K' ↥L')).comap (algebraMap F ↥K') =
          w.comap (algebraMap F ↥L') := by
        rw [← InfinitePlace.comap_comp, IsScalarTower.algebraMap_eq F ↥K' ↥L']
      exact hFc (hcomp ▸ InfinitePlace.IsReal.comap (algebraMap F ↥K') hreal)
  -- ### 6. the normal closure N = conjSup p K' L' and its properties
  haveI hNfd : FiniteDimensional F ↥(Work.CFTLib.conjSup p K' L') :=
    (Work.CFTLib.ConjSup.finiteDimensional_isGalois F p K' L' hL'gal).1
  have hNgal : IsGalois F ↥(Work.CFTLib.conjSup p K' L') :=
    (Work.CFTLib.ConjSup.finiteDimensional_isGalois F p K' L' hL'gal).2
  haveI hNnf : NumberField ↥(Work.CFTLib.conjSup p K' L') :=
    NumberField.of_module_finite F ↥(Work.CFTLib.conjSup p K' L')
  have hNunr : CFTLib.IsUnramified F ↥(Work.CFTLib.conjSup p K' L') :=
    Work.CFTLib.ConjSup.isUnramifiedConjSup F p K' L' hK'unrF hK'infF hL'gal hL'unr hL'inf
  have hNp : IsPGroup p (↥(Work.CFTLib.conjSup p K' L') ≃ₐ[F] ↥(Work.CFTLib.conjSup p K' L')) :=
    Work.CFTLib.ConjSup.isPGroupPow F p K' hK'p L' hL'gal hL'deg hNgal
  -- ### 7. N ≤ E and AF ≤ N
  have hNleE : Work.CFTLib.conjSup p K' L' ≤ LeanEval.NumberTheory.maximalUnramifiedProPF F p := by
    rw [LeanEval.NumberTheory.maximalUnramifiedProPF]
    exact le_iSup_of_le (Work.CFTLib.conjSup p K' L')
      (le_iSup_of_le hNfd (le_iSup_of_le hNgal (le_iSup_of_le hNp
        (le_iSup_of_le hNnf (le_iSup_of_le ((Work.CFTLib.Unramified.isEverywhereUnramified_iff F
          ↥(Work.CFTLib.conjSup p K' L')).mpr hNunr) le_rfl)))))
  have hAFleN : AF ≤ Work.CFTLib.conjSup p K' L' := by
    have hh : (L'.restrictScalars F) = AF := by ext x; rfl
    have h := Work.CFTLib.ConjSup.fieldRange_le_conjSup F p K' L' hL'gal (L'.restrictScalars F).val
    rw [IntermediateField.fieldRange_val] at h
    rwa [hh] at h
  have hAFE : ∀ x : AlgebraicClosure F, x ∈ AF → x ∈ (E F p : Set (AlgebraicClosure F)) :=
    fun x hx => hNleE (hAFleN hx)
  -- ### 8. the intermediate field M and the embedding
  have hAKE : ∀ x : L, ψ x ∈ (E F p : Set (AlgebraicClosure F)) := fun x => hAFE _ (hmemAF x)
  let M : IntermediateField ↥K ↥(E F p) :=
    { Subfield.comap ((E F p).val : ↥(E F p) →+* AlgebraicClosure F) AF.toSubfield with
      algebraMap_mem' := fun x => by
        show (E F p).val (algebraMap ↥K ↥(E F p) x) ∈ AF
        rw [show (E F p).val (algebraMap ↥K ↥(E F p) x) = (algebraMap ↥K (AlgebraicClosure F)) x
          from rfl]
        exact (AlgHom.mem_fieldRange (f := ψF)).mpr ⟨algebraMap ↥K L x, ψ.commutes x⟩ }
  have hMmem : ∀ x : L, (⟨ψ x, hAKE x⟩ : ↥(E F p)) ∈ M :=
    fun x => hmemAF x
  let φ : L →ₐ[↥K] ↥M :=
    { toFun := fun x => ⟨⟨ψ x, hAKE x⟩, hMmem x⟩
      map_one' := Subtype.ext (Subtype.ext (map_one ψ))
      map_mul' := fun x y => Subtype.ext (Subtype.ext (map_mul ψ x y))
      map_zero' := Subtype.ext (Subtype.ext (map_zero ψ))
      map_add' := fun x y => Subtype.ext (Subtype.ext (map_add ψ x y))
      commutes' := fun c => by
        refine Subtype.ext (Subtype.ext ?_)
        exact ψ.commutes c }
  have hinj : Function.Injective φ := fun x y h => by
    have h2 : ψ x = ψ y := congrArg (fun z : ↥M => ((z : ↥(E F p)) : AlgebraicClosure F)) h
    exact ψ.injective h2
  have hsurj : Function.Surjective φ := fun y => by
    have hy : ((y : ↥(E F p)) : AlgebraicClosure F) ∈ (AF : Set (AlgebraicClosure F)) :=
      Subfield.mem_comap.mp y.2
    obtain ⟨x, hx⟩ := hy
    exact ⟨x, by
      refine Subtype.ext (Subtype.ext ?_)
      exact hx⟩
  let e : L ≃ₐ[↥K] ↥M := AlgEquiv.ofBijective φ ⟨hinj, hsurj⟩
  haveI hMfin : Module.Finite ↥K ↥M := LinearEquiv.finiteDimensional e.toLinearEquiv
  haveI hMnf : NumberField ↥M := NumberField.of_module_finite ↥K ↥M
  refine ⟨M, hMnf, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hMfin
  · exact IsGalois.of_algEquiv e
  · intro a b
    have h := hLcom ((AlgEquiv.autCongr e).symm a) ((AlgEquiv.autCongr e).symm b)
    apply (AlgEquiv.autCongr e).symm.injective
    rw [map_mul, map_mul]
    exact h
  · exact IsPGroup.of_equiv hLp (AlgEquiv.autCongr e)
  · exact Work.CFTLib.Transport.isUnramified_algEquiv e hLunr
  · exact ⟨e.toAlgHom⟩

end

end Work.CFTLib.ProP
