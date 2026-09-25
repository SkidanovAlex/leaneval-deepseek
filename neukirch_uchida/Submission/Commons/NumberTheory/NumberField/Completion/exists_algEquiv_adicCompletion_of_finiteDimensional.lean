import Mathlib
import Submission.Commons.RingTheory.Henselian.adicCompletionMap_liesOver
import Submission.Commons.NumberTheory.NumberField.Completion.exists_algEquiv_tensor_adicCompletion_prod
import Submission.Commons.NumberTheory.NumberField.Completion.exists_polynomial_map_close_adicCompletion
import Submission.Commons.FieldTheory.Polynomial.mem_adjoin_of_close
import Submission.Commons.NumberTheory.NumberField.numberField_of_intermediateField
import Submission.Commons.NumberTheory.NumberField.charZero_adicCompletion
import Submission.Commons.NumberTheory.NumberField.countable
import Submission.Commons.Analysis.Normed.exists_root_separation
import Submission.Commons.Analysis.Polynomial.exists_eps_forall_root_close
import Submission.Commons.FieldTheory.Polynomial.natDegree_eq_of_supNorm_lt
import Submission.Commons.Algebra.Field.exists_algEquiv_factor_of_surjective_pi

/-!
# Every finite extension of `K_𝔭` is the completion of a finite extension of `K`

Let `K` be a number field, `Q` a finite place of `K` and `B` a finite-dimensional field
extension of the local field `F = Q.adicCompletion K`.  The main theorem of this file produces a
number field `L` together with a place `q` of `L` lying over `Q` such that the local field
`L_q` is `F`-isomorphic to `B`.

This is the "local fields come from global fields" statement used throughout local
class field theory; here it is needed for the norm index computations in
`Commons.NumberTheory.NumberField.Completion.natCard_quotient_units_range_norm_*`.

## Proof outline

* Fix a primitive element `α` of `B` over `F`, with `f = minpoly F α`, and embed `B` into the
  algebraic closure `C` of `F`; let `x` be the image of `α`.
* By Krasner's lemma in the form `Commons.Analysis.Polynomial.adjoin_rootSet_eq_of_close` /
  `Commons.FieldTheory.Polynomial.mem_adjoin_of_close`, a small perturbation `g ∈ K[X]` of `f`
  has a root `β ∈ C` with `x ∈ F⟮β⟯`; comparing degrees then gives `F⟮β⟯ = F⟮x⟯` and
  `minpoly F β = g.map`.  In particular `B ≃ₐ[F] F⟮β⟯`.
* The natural map `K⟮β⟯ ⊗[K] F → F⟮β⟯` is surjective
  (`surjective_tensorProduct_adjoin_of`), and the tensor product decomposes as the product of
  the completions of `K⟮β⟯` at the places above `Q`
  (`exists_algEquiv_tensor_adicCompletion_prod`); a finite product of fields mapping onto a field
  factors through one factor, whence `B ≃ₐ[F] q.adicCompletion K⟮β⟯` for some place `q | Q`.
* To place the number field in an arbitrary universe, `K⟮β⟯` is replaced by its `Shrink` to the
  target universe (all the number field structures transport across the induced ring
  isomorphism), and the surjectivity statement is transported accordingly. -/

open scoped Valued NumberField TensorProduct
open IsDedekindDomain.HeightOneSpectrum

namespace Commons.NumberTheory.NumberField.Completion
noncomputable section
set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false

universe uK uB uL

/-- A finite-dimensional domain over a field is a field. -/
private lemma isField_of_isDomain_of_finiteDimensional {F R : Type*} [Field F] [CommRing R]
    [Algebra F R] [IsDomain R] [FiniteDimensional F R] : IsField R := by
  refine ⟨⟨0, 1, zero_ne_one⟩, mul_comm, ?_⟩
  intro a ha
  have hinj : Function.Injective (LinearMap.mulLeft F a) := by
    intro x y hxy
    have h : a * (x - y) = 0 := by
      rw [mul_sub, show a * x = a * y from hxy, sub_self]
    rcases mul_eq_zero.mp h with h0 | h0
    · exact absurd h0 ha
    · exact sub_eq_zero.mp h0
  have hsurj : Function.Surjective (LinearMap.mulLeft F a) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp)).mp hinj
  obtain ⟨b, hb⟩ := hsurj 1
  exact ⟨b, by simpa using hb⟩

/-- **Surjectivity of the natural map for a simple extension**, general form: any `K`-field `A`
mapping into `F⟮β⟯` and hitting `β` gives a surjection `A ⊗[K] F →ₐ[F] F⟮β⟯`.

This is the engine behind the local-global construction: it identifies the `F`-algebra
`A ⊗[K] F` with (a quotient of) the simple extension `F⟮β⟯`, where `A` is a global field such as
`K⟮β⟯` or a universe-shrunken model of it. -/
theorem surjective_tensorProduct_adjoin_of
    {K F C : Type*} [Field K] [Field F] [Algebra K F] [Field C] [Algebra F C] [Algebra K C]
    [IsScalarTower K F C] (β : C) (hβint : IsIntegral F β)
    {A : Type*} [Field A] [Algebra K A]
    (incl : A →ₐ[K] ↥(IntermediateField.adjoin F ({β} : Set C)))
    (hβmem : (⟨β, IntermediateField.subset_adjoin F {β} (Set.mem_singleton β)⟩ :
      ↥(IntermediateField.adjoin F ({β} : Set C))) ∈ incl.range) :
    let E' : IntermediateField F C := IntermediateField.adjoin F ({β} : Set C)
    letI : Algebra F (TensorProduct K A F) := Algebra.TensorProduct.rightAlgebra
    ∃ φ : TensorProduct K A F →ₐ[F] ↥E', Function.Surjective φ := by
  intro E'
  letI : Algebra F (TensorProduct K A F) := Algebra.TensorProduct.rightAlgebra
  let ψ : TensorProduct K F A →ₐ[F] ↥E' :=
    Algebra.TensorProduct.lift (Algebra.ofId F ↥E') incl (fun x y => Commute.all _ _)
  have hψ_tmul : ∀ (f : F) (a : A), ψ (f ⊗ₜ[K] a) = algebraMap F ↥E' f * incl a := by
    intro f a
    rw [Algebra.TensorProduct.lift_tmul]
    rfl
  let flip : TensorProduct K A F ≃ₐ[F] TensorProduct K F A :=
    AlgEquiv.ofRingEquiv (f := (Algebra.TensorProduct.comm K A F).toRingEquiv) (by
      intro c
      rw [Algebra.TensorProduct.right_algebraMap_apply]
      change (Algebra.TensorProduct.comm K A F) (1 ⊗ₜ[K] c) = _
      rw [Algebra.TensorProduct.comm_tmul, Algebra.algebraMap_eq_smul_one,
        Algebra.TensorProduct.one_def, TensorProduct.smul_tmul', smul_eq_mul, mul_one])
  let φ : TensorProduct K A F →ₐ[F] ↥E' := ψ.comp flip.toAlgHom
  have hflip : ∀ (a : A) (f : F), flip (a ⊗ₜ[K] f) = f ⊗ₜ[K] a := by
    intro a f
    change (Algebra.TensorProduct.comm K A F) (a ⊗ₜ[K] f) = f ⊗ₜ[K] a
    rw [Algebra.TensorProduct.comm_tmul]
  have hφ_tmul : ∀ (a : A) (f : F), φ (a ⊗ₜ[K] f) = incl a * algebraMap F ↥E' f := by
    intro a f
    change ψ (flip (a ⊗ₜ[K] f)) = incl a * algebraMap F ↥E' f
    rw [hflip, hψ_tmul, mul_comm]
  refine ⟨φ, ?_⟩
  have hrange : ∀ x : C, ∀ hx : x ∈ (E' : Set C), ∃ y : TensorProduct K A F,
      φ y = (⟨x, hx⟩ : ↥E') := by
    intro x hx
    revert hx
    refine IntermediateField.adjoin_induction (F := F) (s := ({β} : Set C))
      (p := fun x hx => ∃ y : TensorProduct K A F, φ y = (⟨x, hx⟩ : ↥E')) ?_ ?_ ?_ ?_ ?_
    · intro x hx
      have hxβ : x = β := Set.mem_singleton_iff.mp hx
      obtain ⟨a, ha⟩ := hβmem
      refine ⟨a ⊗ₜ[K] (1 : F), ?_⟩
      rw [hφ_tmul, map_one, mul_one]
      have ha' : (incl a : C) = β := congrArg Subtype.val ha
      exact Subtype.ext (ha'.trans hxβ.symm)
    · intro c
      refine ⟨(1 : A) ⊗ₜ[K] c, ?_⟩
      rw [hφ_tmul, map_one, one_mul]
      exact Subtype.ext (by simp)
    · intro a b ha hb ⟨ya, hya⟩ ⟨yb, hyb⟩
      exact ⟨ya + yb, by rw [map_add, hya, hyb]; exact Subtype.ext (by simp)⟩
    · intro a ha ⟨y, hy⟩
      by_cases h0 : a = 0
      · refine ⟨0, ?_⟩
        rw [map_zero]
        apply Subtype.ext
        simp only [ZeroMemClass.coe_zero]
        rw [h0, inv_zero]
      · haveI : FiniteDimensional F ↥E' := by
          apply IntermediateField.finiteDimensional_adjoin
          intro x hx
          rw [Set.mem_singleton_iff] at hx
          rw [hx]
          exact hβint
        haveI hfield : IsField ↥(φ.range) :=
          isField_of_isDomain_of_finiteDimensional (F := F)
        have hmem : (⟨a, ha⟩ : ↥E') ∈ φ.range := ⟨y, hy⟩
        let Aa : ↥(φ.range) := ⟨⟨a, ha⟩, hmem⟩
        have hne : Aa ≠ 0 := by
          intro hc
          refine h0 (Subtype.ext_iff.mp (Subtype.ext_iff.mp hc))
        obtain ⟨b, hb⟩ := hfield.mul_inv_cancel hne
        obtain ⟨y', hy'⟩ := b.2
        have hy'' : φ y' = (b : ↥E') := hy'
        refine ⟨y', ?_⟩
        rw [hy'']
        have hb' : (⟨a, ha⟩ : ↥E') * (b : ↥E') = 1 := by
          have := congrArg (fun z : ↥(φ.range) => (z : ↥E')) hb
          simpa using this
        have hb'' : (b : ↥E') = (⟨a, ha⟩ : ↥E')⁻¹ := eq_inv_of_mul_eq_one_right hb'
        rw [hb'']
        exact Subtype.ext rfl
    · intro a b ha hb ⟨ya, hya⟩ ⟨yb, hyb⟩
      exact ⟨ya * yb, by rw [map_mul, hya, hyb]; exact Subtype.ext (by simp)⟩
  intro y
  obtain ⟨x, hx⟩ := hrange (y : C) y.2
  exact ⟨x, hx⟩

/-- **The main construction, in an explicit target universe `uL`.**

For every universe `uL`, the witnessing number field can be found in `Type uL`: this is achieved
at the end of the proof by shrinking the concrete number field `K⟮β⟯` to `Type uL`
(all the number field structures transport across the induced ring isomorphism) and transporting
the surjectivity statement `TensorProduct K K⟮β⟯ F ↠ F⟮β⟯` accordingly. -/
theorem exists_algEquiv_adicCompletion_of_finiteDimensional_aux {K : Type uK} [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    {B : Type uB} [Field B] [Algebra (Q.adicCompletion K) B]
    [FiniteDimensional (Q.adicCompletion K) B] :
    ∃ (L : Type uL) (_ : Field L) (_ : NumberField L) (_ : Algebra K L)
      (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
      (hq : q.asIdeal.LiesOver Q.asIdeal),
      letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
        RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
      Nonempty (B ≃ₐ[Q.adicCompletion K] q.adicCompletion L) := by
  classical
  let F := Q.adicCompletion K
  haveI hcharF : CharZero F := Commons.NumberTheory.NumberField.charZero_adicCompletion Q
  haveI hAlgB : Algebra.IsAlgebraic F B := Algebra.IsAlgebraic.of_finite F B
  haveI hTFB : Module.IsTorsionFree F B := inferInstance
  haveI hTFC : Module.IsTorsionFree F (AlgebraicClosure F) := inferInstance
  haveI hSep : Algebra.IsSeparable F B := Algebra.IsAlgebraic.isSeparable_of_perfectField
  obtain ⟨α, hα⟩ := Field.exists_primitive_element F B
  set f : Polynomial F := minpoly F α with hf
  have hfint : IsIntegral F α := Algebra.IsIntegral.isIntegral α
  have hfdeg : f.natDegree = Module.finrank F B :=
    (Field.primitive_element_iff_minpoly_natDegree_eq F α).mp hα
  have hfmonic : f.Monic := minpoly.monic hfint
  have hfsep : f.Separable := Algebra.IsSeparable.isSeparable F α
  have hfne : f ≠ 0 := minpoly.ne_zero hfint
  have hf1 : 1 ≤ f.natDegree := by
    have hpos : 0 < Module.finrank F B := Module.finrank_pos
    omega
  let σ : B →ₐ[F] AlgebraicClosure F := IsAlgClosed.lift
  have hσinj : Function.Injective σ :=
    fun x y hxy => RingHom.injective (σ : B →+* AlgebraicClosure F) hxy
  let x : AlgebraicClosure F := σ α
  have hminx : minpoly F x = f := minpoly.algHom_eq σ hσinj α
  have hxroot : x ∈ f.rootSet (AlgebraicClosure F) := by
    rw [← hminx]
    exact (minpoly.monic (Algebra.IsIntegral.isIntegral x)).mem_rootSet.mpr (minpoly.aeval F x)
  letI : NontriviallyNormedField (AlgebraicClosure F) :=
    spectralNorm.nontriviallyNormedField F (AlgebraicClosure F)
  letI : NormedAlgebra F (AlgebraicClosure F) :=
    spectralNorm.normedAlgebra F (AlgebraicClosure F)
  have h_ext : ∀ k : F, ‖algebraMap F (AlgebraicClosure F) k‖ = ‖k‖ :=
    fun k => spectralNorm_extends k
  haveI hultraC : IsUltrametricDist (AlgebraicClosure F) := IsUltrametricDist.of_normedAlgebra F
  obtain ⟨δ, hδpos, hδsep⟩ :=
    Commons.Analysis.Normed.exists_root_separation (K := F) (L := AlgebraicClosure F) f
  obtain ⟨ε₀, hε₀pos, hε₀⟩ :=
    Commons.Analysis.Polynomial.exists_eps_forall_root_close (K := F) (L := AlgebraicClosure F)
      h_ext hf1 hδpos hδsep
  have hlcne : f.coeff f.natDegree ≠ 0 := by
    rw [Polynomial.coeff_natDegree]
    exact fun h => hfne (Polynomial.leadingCoeff_eq_zero.mp h)
  have hlcpos : 0 < ‖f.coeff f.natDegree‖ := norm_pos_iff.mpr hlcne
  have hεpos : 0 < min ε₀ ‖f.coeff f.natDegree‖ := lt_min hε₀pos hlcpos
  obtain ⟨g, hgdeg, hgclose⟩ :=
    Commons.NumberTheory.NumberField.Completion.exists_polynomial_map_close_adicCompletion
      Q f f.natDegree le_rfl hεpos
  have hgmapdeg : (g.map (algebraMap K F)).natDegree ≤ f.natDegree :=
    le_trans Polynomial.natDegree_map_le hgdeg
  have hdeg2 : (g.map (algebraMap K F)).natDegree = f.natDegree :=
    Commons.FieldTheory.Polynomial.natDegree_eq_of_supNorm_lt f (g.map (algebraMap K F)) _
      hgmapdeg hlcpos le_rfl (lt_of_lt_of_le hgclose (min_le_right _ _))
  have hf2ne : g.map (algebraMap K F) ≠ 0 := by
    intro h
    rw [h, Polynomial.natDegree_zero] at hdeg2
    omega
  have hclose' : (g.map (algebraMap K F) - f).supNorm < ε₀ := by
    rw [show g.map (algebraMap K F) - f = -(f - g.map (algebraMap K F)) from (neg_sub _ _).symm,
      Commons.Analysis.Polynomial.supNorm_neg]
    exact lt_of_lt_of_le hgclose (min_le_left _ _)
  obtain ⟨β, hβroots, hβδ, hβclose⟩ :=
    hε₀ (g.map (algebraMap K F)) (le_of_eq hdeg2) hf2ne hclose' hxroot
  have hxβ : x ∈ IntermediateField.adjoin F ({β} : Set (AlgebraicClosure F)) :=
    Commons.FieldTheory.Polynomial.mem_adjoin_of_close hfsep hfne hf2ne
      (by rw [← hminx]; exact minpoly.aeval F x) hβroots (IsAlgClosed.splits _) hβclose
  have hβrootF : Polynomial.aeval β (g.map (algebraMap K F)) = 0 := by
    have h := (Polynomial.mem_roots (Polynomial.map_ne_zero hf2ne)).mp hβroots
    rw [Polynomial.IsRoot.def, Polynomial.eval_map] at h
    rwa [Polynomial.aeval_def]
  have hβint : IsIntegral F β :=
    Commons.FieldTheory.IntegralClosure.isIntegral_of_aeval_eq_zero hf2ne hβrootF
  have hfin_x : Module.finrank F ↥(IntermediateField.adjoin F ({x} : Set (AlgebraicClosure F)))
      = f.natDegree := by
    rw [← hminx]
    exact IntermediateField.adjoin.finrank (Algebra.IsIntegral.isIntegral x)
  have hfin_β_le : Module.finrank F ↥(IntermediateField.adjoin F ({β} : Set (AlgebraicClosure F)))
      ≤ f.natDegree := by
    rw [IntermediateField.adjoin.finrank hβint, ← hdeg2]
    exact Polynomial.natDegree_le_of_dvd (minpoly.dvd F β hβrootF) hf2ne
  haveI hfdE : FiniteDimensional F ↥(IntermediateField.adjoin F ({β} : Set (AlgebraicClosure F))) :=
    IntermediateField.finiteDimensional_adjoin (fun y hy => by
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      exact hβint)
  have hle : IntermediateField.adjoin F ({x} : Set (AlgebraicClosure F))
      ≤ IntermediateField.adjoin F ({β} : Set (AlgebraicClosure F)) :=
    IntermediateField.adjoin_le_iff.mpr (by
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      exact hxβ)
  have hEq : IntermediateField.adjoin F ({x} : Set (AlgebraicClosure F))
      = IntermediateField.adjoin F ({β} : Set (AlgebraicClosure F)) :=
    IntermediateField.eq_of_le_of_finrank_le hle (by rw [hfin_x]; exact hfin_β_le)
  let E' : IntermediateField F (AlgebraicClosure F) :=
    IntermediateField.adjoin F ({β} : Set (AlgebraicClosure F))
  have hBrange : σ.fieldRange = IntermediateField.adjoin F ({x} : Set (AlgebraicClosure F)) := by
    rw [AlgHom.fieldRange_eq_map, ← hα, IntermediateField.adjoin_map]
    simp [x]
  have hBiso : Nonempty (B ≃ₐ[F] ↥E') :=
    ⟨σ.equivFieldRange.trans (IntermediateField.equivOfEq (hBrange.trans hEq))⟩
  -- integrality of β over K
  have hg0 : g ≠ 0 := by
    intro h
    rw [h, Polynomial.map_zero, Polynomial.natDegree_zero] at hdeg2
    omega
  have hβrootsKC : β ∈ (Polynomial.map (algebraMap K (AlgebraicClosure F)) g).roots := by
    rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq K F (AlgebraicClosure F)] at hβroots
    exact hβroots
  have hβintK : IsIntegral K β := by
    refine Commons.FieldTheory.IntegralClosure.isIntegral_of_aeval_eq_zero
      (f := g) hg0 ?_
    have h := (Polynomial.mem_roots (Polynomial.map_ne_zero hg0)).mp hβrootsKC
    rw [Polynomial.IsRoot.def, Polynomial.eval_map] at h
    rwa [Polynomial.aeval_def]
  -- the number field `L0 = K⟮β⟯`
  let L0 : IntermediateField K (AlgebraicClosure F) :=
    IntermediateField.adjoin K ({β} : Set (AlgebraicClosure F))
  haveI hL0fd : FiniteDimensional K ↥L0 := by
    apply IntermediateField.finiteDimensional_adjoin
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    exact hβintK
  haveI hL0nf : NumberField ↥L0 :=
    Commons.NumberTheory.NumberField.numberField_of_intermediateField L0
  -- the inclusion and the surjection for `L0`
  have hLE : (L0 : Set (AlgebraicClosure F)) ⊆ (E' : Set (AlgebraicClosure F)) := by
    have h : L0 ≤ IntermediateField.restrictScalars K E' := by
      rw [IntermediateField.adjoin_le_iff]
      intro y hy
      exact IntermediateField.subset_adjoin F {β} hy
    intro y hy
    exact h hy
  let incl0 : ↥L0 →ₐ[K] ↥E' :=
    { toFun := fun l => ⟨l.1, hLE l.2⟩
      map_one' := rfl
      map_mul' := fun a b => rfl
      map_zero' := rfl
      map_add' := fun a b => rfl
      commutes' := fun c => Subtype.ext (by
        rw [IntermediateField.coe_algebraMap_apply, IsScalarTower.algebraMap_apply K F ↥E',
          IntermediateField.coe_algebraMap_apply,
          IsScalarTower.algebraMap_apply K F (AlgebraicClosure F)]) }
  have hβmem0 : (⟨β, IntermediateField.subset_adjoin F {β} (Set.mem_singleton β)⟩ : ↥E')
      ∈ incl0.range :=
    ⟨⟨β, IntermediateField.subset_adjoin K {β} (Set.mem_singleton β)⟩, Subtype.ext rfl⟩
  -- shrink `L0` to the target universe
  haveI hcount : Countable ↥L0 := Commons.NumberTheory.NumberField.countable
  haveI hsmall : Small.{uL} ↥L0 := Countable.toSmall ↥L0
  let L := Shrink.{uL} ↥L0
  letI hSemL : Semiring L := Shrink.instSemiring
  letI hRingL : Ring L := Shrink.instRing
  letI hCommRingL : CommRing L := Shrink.instCommRing
  letI hFieldL : Field L := Shrink.instField
  haveI hNFL : NumberField L := NumberField.of_ringEquiv ↥L0 L (Shrink.ringEquiv ↥L0).symm
  letI hAL : Algebra K L := Shrink.instAlgebra (R := K) (α := ↥L0)
  letI hModL : Module K L := Algebra.toModule
  haveI hFDL : FiniteDimensional K L := by
    have e : ↥L0 ≃ₐ[K] L :=
      AlgEquiv.ofRingEquiv (f := (Shrink.ringEquiv ↥L0).symm) (by
        intro c
        show (Shrink.ringEquiv ↥L0).symm ((algebraMap K ↥L0) c) =
          ((Shrink.ringEquiv ↥L0).symm.toRingHom.comp (algebraMap K ↥L0)) c
        rfl)
    exact Module.Finite.equiv e.toLinearEquiv
  -- the surjection for `L`
  let inclL : L →ₐ[K] ↥E' := incl0.comp (Shrink.algEquiv K ↥L0)
  have hβmemL : (⟨β, IntermediateField.subset_adjoin F {β} (Set.mem_singleton β)⟩ : ↥E')
      ∈ inclL.range := by
    refine ⟨(Shrink.algEquiv K ↥L0).symm
      ⟨β, IntermediateField.subset_adjoin K {β} (Set.mem_singleton β)⟩, ?_⟩
    show incl0 ((Shrink.algEquiv K ↥L0)
      ((Shrink.algEquiv K ↥L0).symm ⟨β, IntermediateField.subset_adjoin K {β}
        (Set.mem_singleton β)⟩)) = _
    rw [AlgEquiv.apply_symm_apply]
    exact Subtype.ext rfl
  obtain ⟨φ, hφ⟩ := surjective_tensorProduct_adjoin_of (K := K) (F := F)
    (C := AlgebraicClosure F) β hβint inclL hβmemL
  -- Chinese remainder decomposition of the tensor product
  letI : Algebra F (TensorProduct K L F) := Algebra.TensorProduct.rightAlgebra
  haveI hfinq : Fintype {q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L) //
      q.asIdeal.LiesOver Q.asIdeal} :=
    Fintype.ofEquiv (Q.asIdeal.primesOver (NumberField.RingOfIntegers L))
      (Commons.NumberTheory.NumberField.Completion.primesOverEquiv Q).symm
  letI : ∀ q : {q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L) //
      q.asIdeal.LiesOver Q.asIdeal}, Algebra F (q.1.adicCompletion L) :=
    fun q => RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q.1 q.2)
  obtain ⟨ψ⟩ :=
    Commons.NumberTheory.NumberField.Completion.exists_algEquiv_tensor_adicCompletion_prod K L Q
  -- assembly
  have hsurj : Function.Surjective
      ((hBiso.some).symm.toAlgHom.comp (φ.comp ψ.symm.toAlgHom)) := by
    intro y
    obtain ⟨t, ht⟩ := hφ ((hBiso.some) y)
    refine ⟨ψ t, ?_⟩
    show (hBiso.some).symm (φ (ψ.symm (ψ t))) = y
    rw [AlgEquiv.symm_apply_apply, ht, AlgEquiv.symm_apply_apply]
  obtain ⟨q, ⟨e_q⟩⟩ := Commons.Algebra.Field.exists_algEquiv_factor_of_surjective_pi
    (fun q : {q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L) //
        q.asIdeal.LiesOver Q.asIdeal} => q.1.adicCompletion L)
    ((hBiso.some).symm.toAlgHom.comp (φ.comp ψ.symm.toAlgHom)) hsurj
  exact ⟨L, hFieldL, hNFL, hAL, q.1, q.2, ⟨e_q.symm⟩⟩

theorem exists_algEquiv_adicCompletion_of_finiteDimensional
    {K : Type*} [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    {B : Type*} [Field B] [Algebra (Q.adicCompletion K) B]
    [FiniteDimensional (Q.adicCompletion K) B] :
    ∃ (L : Type*) (_ : Field L) (_ : NumberField L) (_ : Algebra K L)
      (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
      (hq : q.asIdeal.LiesOver Q.asIdeal),
      letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
        RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
      Nonempty (B ≃ₐ[Q.adicCompletion K] q.adicCompletion L) :=
  exists_algEquiv_adicCompletion_of_finiteDimensional_aux Q

end
end Commons.NumberTheory.NumberField.Completion

