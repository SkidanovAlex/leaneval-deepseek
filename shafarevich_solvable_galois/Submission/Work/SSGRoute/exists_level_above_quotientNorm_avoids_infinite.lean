import Mathlib
import Submission.Work.SSGRoute.PTDefs
import Submission.Work.SSGRoute.QLImports
import Submission.Work.SSGRoute.normImage_at_level_proper
import Submission.Work.SSGRoute.exists_level_pthRoot
import Submission.Work.SSGRoute.localUnitsEquiv_fixed_iff_ringEquiv_fixed
import Submission.Work.SSGRoute.phi1_level_naturality
import Submission.Work.SSGRoute.localAlgebraMapUnits_self
import Submission.NK.GlobalCFT.Inclusion.globalCFT_idele_smul_eq_self_iff
import Submission.NK.GlobalCFT.Galois.exists_stabilizer_isConj_of_isReal_isComplex
import Submission.NK.GlobalCFT.Galois.globalCFT_localFixed_infinite
import Submission.NK.NUV2.LC.RouteB.locUnits_tower_eq_zero
import Submission.Work.SSGRoute.exists_pow_eq_complex_units
import Submission.Work.SSGRoute.exists_sign_mul_pow_eq_real
import Submission.Commons.NumberTheory.NumberField.numberField_of_intermediateField
import Submission.Commons.NumberTheory.NumberField.Completion.exists_galois_realization
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

noncomputable section

open Polynomial

set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

/-! ## Auxiliary lemmas for the archimedean case -/

section Bridges

variable {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [FiniteDimensional k K] [IsGalois k K]

/-- **Fixed local units come from the base local field.** -/
theorem localFixedUnits_mem_range_place (w : NK.GlobalCFT.Place K) (v : NK.GlobalCFT.Place k)
    (hv : NK.GlobalCFT.Place.LiesOver w v) (a : (NK.GlobalCFT.Place.localField K w)ˣ)
    (hafix : ∀ σ : SSGRoute.PTExt.decompK (k := k) w,
      NK.HassePrinciple.localUnitsEquiv (K := k) w σ a = a) :
    ∃ a₀ : (NK.GlobalCFT.Place.localField k v)ˣ,
      NK.GlobalCFT.Place.localAlgebraMapUnits w v hv a₀ = a :=
  NK.GlobalCFT.Inclusion.globalCFT_localFixed_mem_range hv a
    ((localUnitsEquiv_fixed_iff_ringEquiv_fixed_general k K w a).mp hafix)

/-- **The image of the base local units is fixed by the decomposition group.** -/
theorem localUnitsEquiv_localAlgebraMapUnits_eq_self_place {w : NK.GlobalCFT.Place K}
    {v : NK.GlobalCFT.Place k} (hv : NK.GlobalCFT.Place.LiesOver w v)
    (u : (NK.GlobalCFT.Place.localField k v)ˣ) (σ : SSGRoute.PTExt.decompK (k := k) w) :
    NK.HassePrinciple.localUnitsEquiv (K := k) w σ
        (NK.GlobalCFT.Place.localAlgebraMapUnits w v hv u)
      = NK.GlobalCFT.Place.localAlgebraMapUnits w v hv u := by
  have h := NK.NUV2.LC.RouteB.localUnitsEquiv_localAlgebraMapUnits_tower
    (F := k) (L := k) (M := K) (w := v) (w' := w) hv σ u
  rw [← h]
  congr 1
  have hτ : (NK.NUV2.LC.RouteB.localStabilizerMapTower (F := k) (L := k) (M := K)
      (w := v) (w' := w) hv σ) = 1 := Subsingleton.elim _ _
  rw [hτ, NK.HassePrinciple.localUnitsEquiv_one]
  rfl

/-- Units map, injectivity inherits from the underlying map. -/
theorem units_map_injective {M N : Type*} [Monoid M] [Monoid N] {f : M →* N}
    (hf : Function.Injective f) : Function.Injective (Units.map f) := by
  intro x y h
  refine Units.ext (hf ?_)
  exact congrArg (fun u : Nˣ => (u : N)) h

/-- **Injectivity of the local embedding at an infinite place.** -/
theorem localAlgebraMapUnits_injective_ofInfinite {k K : Type} [Field k] [NumberField k]
    [Field K] [NumberField K] [Algebra k K]
    {w : NumberField.InfinitePlace K} {v : NumberField.InfinitePlace k} [w.LiesOver v]
    (h : NK.GlobalCFT.Place.LiesOver (NK.GlobalCFT.Place.ofInfinite w)
      (NK.GlobalCFT.Place.ofInfinite v)) :
    Function.Injective (NK.GlobalCFT.Place.localAlgebraMapUnits
      (NK.GlobalCFT.Place.ofInfinite w) (NK.GlobalCFT.Place.ofInfinite v) h) := by
  rw [NK.GlobalCFT.Inclusion.globalCFT_localAlgebraMapUnits_congr
    (NK.GlobalCFT.Place.ofInfinite w) (NK.GlobalCFT.Place.ofInfinite v) h
    (NK.GlobalCFT.Place.liesOver_ofInfinite ‹w.LiesOver v›)]
  rw [NK.GlobalCFT.Inclusion.globalCFT_localAlgebraMapUnits_ofInfinite w v
    (NK.GlobalCFT.Place.liesOver_ofInfinite ‹w.LiesOver v›)]
  exact units_map_injective (RingHom.injective _)

end Bridges

/-! ### `p`-th roots in the unit group of an archimedean local field -/

/-- At a complex archimedean place every unit of the completion is a `p`-th power. -/
theorem units_pow_surjective_of_isComplex {k : Type} [Field k] [NumberField k]
    (v : NumberField.InfinitePlace k) (hvC : v.IsComplex) (p : ℕ) [Fact p.Prime]
    (c : (v.Completion)ˣ) : ∃ c' : (v.Completion)ˣ, c' ^ p = c := by
  classical
  set Φ : (v.Completion)ˣ ≃* ℂˣ :=
    Units.mapEquiv (NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hvC).toMulEquiv
    with hΦ
  obtain ⟨c', hc'⟩ := exists_pow_eq_complex_units p (Φ c)
  exact ⟨Φ.symm c', Φ.injective (by rw [map_pow, MulEquiv.apply_symm_apply]; exact hc')⟩

/-- At a real archimedean place every unit of the completion is a `p`-th power for `p` odd. -/
theorem units_pow_surjective_of_odd {k : Type} [Field k] [NumberField k]
    (v : NumberField.InfinitePlace k) (hvR : v.IsReal) {p : ℕ} [Fact p.Prime] (hp : Odd p)
    (c : (v.Completion)ˣ) : ∃ c' : (v.Completion)ˣ, c' ^ p = c := by
  classical
  set Ψ : (v.Completion)ˣ ≃* ℝˣ :=
    Units.mapEquiv (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hvR).toMulEquiv
    with hΨ
  obtain ⟨s, y, hs, hsy⟩ := exists_sign_mul_pow_eq_real p (Ψ c)
  have hsp : s ^ p = s := by
    rcases hs with rfl | rfl
    · simp
    · exact Odd.neg_one_pow hp
  refine ⟨Ψ.symm (s * y), Ψ.injective ?_⟩
  rw [map_pow, MulEquiv.apply_symm_apply, mul_pow, hsp, hsy]

/-- **In the archimedean case the exponent is `2` and the base place is real.** -/
theorem p_eq_two_of_fixed_not_pthPower_infinite
    (p : ℕ) [Fact p.Prime] (k K : Type) [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (w : NumberField.InfinitePlace K) (v : NumberField.InfinitePlace k) [w.LiesOver v]
    (a : (NumberField.InfinitePlace.Completion w)ˣ)
    (hafix : ∀ σ : SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofInfinite w),
      NK.HassePrinciple.localUnitsEquiv (K := k) (NK.GlobalCFT.Place.ofInfinite w) σ a = a)
    (ha : ¬ ∃ b : (NumberField.InfinitePlace.Completion w)ˣ,
      (∀ σ : SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofInfinite w),
        NK.HassePrinciple.localUnitsEquiv (K := k) (NK.GlobalCFT.Place.ofInfinite w) σ b = b) ∧
        b ^ p = a) :
    p = 2 ∧ v.IsReal := by
  classical
  have hv' : NK.GlobalCFT.Place.LiesOver (NK.GlobalCFT.Place.ofInfinite w)
      (NK.GlobalCFT.Place.ofInfinite v) := NK.GlobalCFT.Place.liesOver_ofInfinite ‹w.LiesOver v›
  obtain ⟨c, hc⟩ := localFixedUnits_mem_range_place (k := k) (K := K)
    (NK.GlobalCFT.Place.ofInfinite w) (NK.GlobalCFT.Place.ofInfinite v) hv' a hafix
  have key : ∀ c' : (v.Completion)ˣ, c' ^ p = c →
      ∃ b : (NumberField.InfinitePlace.Completion w)ˣ,
        (∀ σ : SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofInfinite w),
          NK.HassePrinciple.localUnitsEquiv (K := k) (NK.GlobalCFT.Place.ofInfinite w) σ b = b) ∧
          b ^ p = a := by
    intro c' hc'
    refine ⟨NK.GlobalCFT.Place.localAlgebraMapUnits (NK.GlobalCFT.Place.ofInfinite w)
      (NK.GlobalCFT.Place.ofInfinite v) hv' c', ?_, ?_⟩
    · intro σ
      exact localUnitsEquiv_localAlgebraMapUnits_eq_self_place hv' c' σ
    · rw [← hc, ← map_pow, hc']
  have hnotC : ¬ v.IsComplex := by
    intro hvC
    obtain ⟨c', hc'⟩ := units_pow_surjective_of_isComplex v hvC p c
    exact ha (key c' hc')
  have hp2 : p = 2 := by
    by_contra hpne
    have hpodd : Odd p :=
      Nat.not_even_iff_odd.mp fun he => hpne ((Fact.out : p.Prime).even_iff.mp he)
    rcases NumberField.InfinitePlace.isReal_or_isComplex v with hvR | hvC
    · obtain ⟨c', hc'⟩ := units_pow_surjective_of_odd v hvR hpodd c
      exact ha (key c' hc')
    · exact hnotC hvC
  exact ⟨hp2, NumberField.InfinitePlace.not_isComplex_iff_isReal.mp hnotC⟩

/-! ### A level in which a prescribed infinite place becomes complex -/

/-- **Auxiliary level construction.**  There is a finite Galois extension `L/k` of number fields
containing `L₀`, a place `u` of `L` over `u₀`, and an element `x ∈ L` with `x ^ 2 = -1`. -/
theorem exists_level_infinite_complex_aux (k L₀ : Type) [Field k] [NumberField k] [Field L₀]
    [NumberField L₀] [Algebra k L₀] [FiniteDimensional k L₀] [IsGalois k L₀]
    (u₀ : NumberField.InfinitePlace L₀) :
    ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra k L) (_ : Algebra L₀ L)
      (_ : IsScalarTower k L₀ L) (_ : FiniteDimensional k L) (_ : IsGalois k L)
      (u : NumberField.InfinitePlace L) (x : L), u.LiesOver u₀ ∧ x ^ 2 = -1 := by
  classical
  let Ω := AlgebraicClosure k
  haveI hΩ : IsAlgClosed Ω := inferInstance
  let f : k[X] := X ^ 2 + C 1
  let S : Set Ω := f.rootSet Ω
  let E : IntermediateField k Ω := IntermediateField.adjoin k S
  haveI hsplit : Polynomial.IsSplittingField k ↥E f :=
    IntermediateField.adjoin_rootSet_isSplittingField (p := f)
      (IsAlgClosed.splits (f.map (algebraMap k Ω)))
  haveI hnormE : Normal k ↥E := Normal.of_isSplittingField f
  haveI hfdE : FiniteDimensional k ↥E := Polynomial.IsSplittingField.finiteDimensional ↥E f
  haveI hgalE : IsGalois k ↥E := isGalois_iff.mpr ⟨inferInstance, hnormE⟩
  haveI hAlgAlg : Algebra.IsAlgebraic k L₀ := Algebra.IsAlgebraic.of_finite k L₀
  let ιL : L₀ →ₐ[k] Ω := IsAlgClosed.lift
  let L₀' : IntermediateField k Ω := ιL.fieldRange
  haveI hfdL₀' : FiniteDimensional k ↥L₀' :=
    LinearEquiv.finiteDimensional (AlgHom.equivFieldRange ιL).toLinearEquiv
  haveI hgalL₀' : IsGalois k ↥L₀' := IsGalois.of_algEquiv (AlgHom.equivFieldRange ιL)
  haveI hsepL₀' : Algebra.IsSeparable k ↥L₀' :=
    (isGalois_iff.mp (inferInstance : IsGalois k ↥L₀')).1
  haveI hnormL₀' : Normal k ↥L₀' :=
    (isGalois_iff.mp (inferInstance : IsGalois k ↥L₀')).2
  haveI hsepE : Algebra.IsSeparable k ↥E := inferInstance
  let M : IntermediateField k Ω := L₀' ⊔ E
  haveI hsepM : Algebra.IsSeparable k ↥M := IntermediateField.isSeparable_sup k Ω L₀' E
  haveI hnormM : Normal k ↥M := IntermediateField.normal_sup k Ω L₀' E
  haveI hfdM : FiniteDimensional k ↥M := IntermediateField.finiteDimensional_sup L₀' E
  haveI hgalM : IsGalois k ↥M := isGalois_iff.mpr ⟨hsepM, hnormM⟩
  haveI hnfM : NumberField ↥M :=
    Commons.NumberTheory.NumberField.numberField_of_intermediateField (K := k) (K' := Ω) M
  let fL : L₀ →ₐ[k] ↥M :=
    (IntermediateField.inclusion (show L₀' ≤ M from le_sup_left)).comp (AlgHom.equivFieldRange ιL)
  letI : Algebra L₀ ↥M := RingHom.toAlgebra fL.toRingHom
  haveI hSTL : IsScalarTower k L₀ ↥M := IsScalarTower.of_algebraMap_eq (fun a => by
    rw [RingHom.algebraMap_toAlgebra]
    exact (fL.commutes a).symm)
  haveI hAlgL₀M : Algebra.IsAlgebraic L₀ ↥M := Algebra.IsAlgebraic.of_finite L₀ ↥M
  obtain ⟨u, hu⟩ := NumberField.InfinitePlace.comap_surjective (k := L₀) (K := ↥M) u₀
  have hsplitE : (f.map (algebraMap k ↥E)).Splits := Polynomial.IsSplittingField.splits ↥E f
  have hmapE : f.map (algebraMap k ↥E) = X ^ 2 + C (1 : ↥E) := by simp [f]
  have hdegE : (f.map (algebraMap k ↥E)).degree ≠ 0 := by
    rw [hmapE]
    have h2 : (X ^ 2 + C (1 : ↥E)).degree = 2 := by compute_degree!
    rw [h2]
    norm_num
  obtain ⟨x, hx⟩ := hsplitE.exists_eval_eq_zero hdegE
  have hx2 : x ^ 2 = -1 := by
    have h : x ^ 2 + 1 = 0 := by
      have h' := hx
      rw [hmapE] at h'
      simpa using h'
    exact eq_neg_iff_add_eq_zero.mpr h
  refine ⟨↥M, inferInstance, hnfM, inferInstance, RingHom.toAlgebra fL.toRingHom, hSTL, hfdM,
    hgalM, u, (IntermediateField.inclusion (le_sup_right : E ≤ M)) x, ?_, ?_⟩
  · refine ⟨?_⟩
    have hh : (u.comap (algebraMap L₀ ↥M)).val = u₀.val := congrArg Subtype.val hu
    rw [← hh]
    rfl
  · rw [← map_pow, hx2, map_neg, map_one]

/-- **A level containing `L₀` with a complex place over `u₀`.** -/
theorem exists_level_infinite_complex (k L₀ : Type) [Field k] [NumberField k] [Field L₀]
    [NumberField L₀] [Algebra k L₀] [FiniteDimensional k L₀] [IsGalois k L₀]
    (u₀ : NumberField.InfinitePlace L₀) :
    ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra k L) (_ : Algebra L₀ L)
      (_ : IsScalarTower k L₀ L) (_ : FiniteDimensional k L) (_ : IsGalois k L)
      (u : NumberField.InfinitePlace L), u.LiesOver u₀ ∧ u.IsComplex := by
  obtain ⟨L, hLf, hLn, hLk, hLL₀, hST, hLfd, hLgal, u, x, hux, hx⟩ :=
    exists_level_infinite_complex_aux k L₀ u₀
  refine ⟨L, hLf, hLn, hLk, hLL₀, hST, hLfd, hLgal, u, hux, ?_⟩
  rw [← NumberField.InfinitePlace.not_isReal_iff_isComplex]
  rintro ⟨φ, hφreal, -⟩
  let ψ : L →+* ℝ := hφreal.embedding
  have h1 : ψ (x ^ 2) = ψ (-1) := congrArg ψ hx
  rw [map_pow, map_neg, map_one] at h1
  have hnn : (0 : ℝ) ≤ ψ x ^ 2 := sq_nonneg _
  rw [h1] at hnn
  norm_num at hnn

/-! ### The stabiliser of an infinite place is of order two at a complex place over a real one -/

/-- The stabiliser of `Place.ofInfinite u` is the stabiliser of `u`. -/
theorem stabilizer_place_ofInfinite_eq {k L : Type} [Field k] [NumberField k] [Field L]
    [NumberField L] [Algebra k L]
    (u : NumberField.InfinitePlace L) :
    MulAction.stabilizer (L ≃ₐ[k] L) (NK.GlobalCFT.Place.ofInfinite u)
      = MulAction.stabilizer (L ≃ₐ[k] L) u := by
  ext σ
  simp only [MulAction.mem_stabilizer_iff, NK.GlobalCFT.Place.smul_ofInfinite,
    NK.GlobalCFT.Place.ofInfinite_inj]

/-- **The decomposition group of a complex place over a real one has order two.** -/
theorem natCard_stabilizer_place_ofInfinite_eq_two {k L : Type} [Field k] [NumberField k]
    [Field L] [NumberField L] [Algebra k L] [FiniteDimensional k L] [IsGalois k L]
    (u : NumberField.InfinitePlace L) (v : NumberField.InfinitePlace k) [u.LiesOver v]
    (hv : v.IsReal) (hu : u.IsComplex) :
    Nat.card ↥(MulAction.stabilizer (L ≃ₐ[k] L) (NK.GlobalCFT.Place.ofInfinite u)) = 2 := by
  obtain ⟨σ, hσne, hσfix, -⟩ :=
    NK.GlobalCFT.Galois.exists_stabilizer_isConj_of_isReal_isComplex u v hv hu
  have hne1 : Nat.card ↥(MulAction.stabilizer (L ≃ₐ[k] L) u) ≠ 1 := by
    intro h1
    have hbot : MulAction.stabilizer (L ≃ₐ[k] L) u = ⊥ := Subgroup.card_eq_one.mp h1
    have hmem : σ ∈ MulAction.stabilizer (L ≃ₐ[k] L) u := MulAction.mem_stabilizer_iff.mpr hσfix
    rw [hbot] at hmem
    exact hσne (Subgroup.mem_bot.mp hmem)
  rcases NumberField.InfinitePlace.nat_card_stabilizer_eq_one_or_two k u with h | h
  · exact absurd h hne1
  · rwa [stabilizer_place_ofInfinite_eq (k := k) u]

/-! ### Elementary combinatorics of a group with two elements -/

/-- A group of cardinality two is covered by `1` and a further element. -/
theorem exists_two_cover_of_card_eq_two {α : Type} [Group α] [Fintype α]
    (h : Fintype.card α = 2) :
    ∃ q₁ : α, q₁ ≠ 1 ∧ ∀ c : α, c = 1 ∨ c = q₁ := by
  classical
  obtain ⟨a, b, hab, hset⟩ :=
    Finset.card_eq_two.mp (show (Finset.univ : Finset α).card = 2 by simpa using h)
  have hmem : ∀ c : α, c ∈ ({a, b} : Finset α) := by
    intro c
    rw [← hset]
    exact Finset.mem_univ c
  rcases Finset.mem_insert.mp (hmem 1) with h1a | h1b
  · refine ⟨b, fun hb => hab (h1a.symm.trans hb.symm), fun c => ?_⟩
    rcases Finset.mem_insert.mp (hmem c) with hca | hcb
    · exact Or.inl (hca.trans h1a.symm)
    · exact Or.inr (Finset.mem_singleton.mp hcb)
  · have h1b' : (1 : α) = b := Finset.mem_singleton.mp h1b
    refine ⟨a, fun ha => hab (ha.trans h1b'), fun c => ?_⟩
    rcases Finset.mem_insert.mp (hmem c) with hca | hcb
    · exact Or.inr hca
    · exact Or.inl ((Finset.mem_singleton.mp hcb).trans h1b'.symm)

/-- A product over a type covered by two distinct elements. -/
theorem prod_eq_mul_of_cover {α : Type*} [Fintype α] {M : Type*} [CommMonoid M]
    (a b : α) (hne : a ≠ b) (hcov : ∀ c : α, c = a ∨ c = b) (f : α → M) :
    (∏ c : α, f c) = f a * f b := by
  classical
  have huniv : ({a, b} : Finset α) = Finset.univ := by
    apply Finset.eq_univ_iff_forall.mpr
    intro c
    rcases hcov c with h | h <;> simp [h]
  rw [← huniv, Finset.prod_insert (by simp [hne]), Finset.prod_singleton]

end

theorem exists_level_above_quotientNorm_avoids_infinite
    (p : ℕ) [Fact p.Prime] (k K : Type) [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K] [FiniteDimensional k K] [IsGalois k K] (w : NK.GlobalCFT.Place K)
    (hwinf : w.IsInfinite)
    (a : (NK.GlobalCFT.Place.localField K w)ˣ)
    (hafix : ∀ σ : SSGRoute.PTExt.decompK (k := k) w,
      NK.HassePrinciple.localUnitsEquiv (K := k) w σ a = a)
    (ha : ¬ ∃ b : (NK.GlobalCFT.Place.localField K w)ˣ,
      (∀ σ : SSGRoute.PTExt.decompK (k := k) w,
        NK.HassePrinciple.localUnitsEquiv (K := k) w σ b = b) ∧ b ^ p = a)
    (L₀ : Type) [Field L₀] [NumberField L₀] [Algebra k L₀] [Algebra K L₀] [IsScalarTower k K L₀]
    [FiniteDimensional k L₀] [IsGalois k L₀]
    (w₀ : NK.GlobalCFT.Place L₀) (hw₀ : NK.GlobalCFT.Place.LiesOver w₀ w) :
    ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra k L) (_ : Algebra L₀ L)
      (_ : IsScalarTower k L₀ L) (_ : FiniteDimensional k L) (_ : IsGalois k L)
      (w' : NK.GlobalCFT.Place L) (hw' : NK.GlobalCFT.Place.LiesOver w' w₀)
      (N : Subgroup (MulAction.stabilizer (L ≃ₐ[k] L) w')) (_ : N.Normal)
      (_ : Fintype (MulAction.stabilizer (L ≃ₐ[k] L) w' ⧸ N)),
      IsCyclic (MulAction.stabilizer (L ≃ₐ[k] L) w' ⧸ N) ∧
      Nat.card (MulAction.stabilizer (L ≃ₐ[k] L) w' ⧸ N) = p ∧
      ¬ (∃ bb : NK.HassePrinciple.localUnitsRep k L w',
        (∀ n : N, (NK.HassePrinciple.localUnitsRep k L w').ρ
          (n : MulAction.stabilizer (L ≃ₐ[k] L) w') bb = bb) ∧
        (∑ x : MulAction.stabilizer (L ≃ₐ[k] L) w' ⧸ N,
          (NK.HassePrinciple.localUnitsRep k L w').ρ (Quotient.out x) bb) =
          Additive.ofMul (NK.GlobalCFT.Place.localAlgebraMapUnits w' w₀ hw'
            (NK.GlobalCFT.Place.localAlgebraMapUnits w₀ w hw₀ a))) := by
  classical
  obtain ⟨wK, rfl⟩ := NK.GlobalCFT.Place.isInfinite_iff.mp hwinf
  let v : NumberField.InfinitePlace k := wK.comap (algebraMap k K)
  haveI hvlies : wK.LiesOver v := ⟨rfl⟩
  have hvw : NK.GlobalCFT.Place.LiesOver (NK.GlobalCFT.Place.ofInfinite wK)
      (NK.GlobalCFT.Place.ofInfinite v) := NK.GlobalCFT.Place.liesOver_ofInfinite hvlies
  obtain ⟨hp2, hvR⟩ := p_eq_two_of_fixed_not_pthPower_infinite p k K wK v a hafix ha
  subst hp2
  obtain ⟨u₀, rfl⟩ : ∃ u₀ : NumberField.InfinitePlace L₀,
      w₀ = NK.GlobalCFT.Place.ofInfinite u₀ := by
    rcases (NK.GlobalCFT.Place.liesOver_iff w₀ (NK.GlobalCFT.Place.ofInfinite wK)).mp hw₀ with
      ⟨w', v', h1, h2, h3⟩ | ⟨q', Q', h1, h2, h3⟩
    · exact ⟨w', h1⟩
    · exact absurd h2 (NK.GlobalCFT.Place.ofInfinite_ne_ofFinite wK Q')
  haveI hu₀lies : u₀.LiesOver wK := by
    rcases (NK.GlobalCFT.Place.liesOver_iff (NK.GlobalCFT.Place.ofInfinite u₀)
      (NK.GlobalCFT.Place.ofInfinite wK)).mp hw₀ with
      ⟨w', v', h1, h2, h3⟩ | ⟨q', Q', h1, h2, h3⟩
    · rw [NK.GlobalCFT.Place.ofInfinite_inj] at h1 h2
      rw [← h1, ← h2] at h3
      exact h3
    · exact absurd h1 (NK.GlobalCFT.Place.ofInfinite_ne_ofFinite u₀ q')
  obtain ⟨L, hLf, hLn, hLk, hLL₀, hST, hLfd, hLgal, u, hulies, huC⟩ :=
    exists_level_infinite_complex k L₀ u₀
  letI : Field L := hLf
  letI : NumberField L := hLn
  letI : Algebra k L := hLk
  letI : Algebra L₀ L := hLL₀
  letI : IsScalarTower k L₀ L := hST
  letI : FiniteDimensional k L := hLfd
  letI : IsGalois k L := hLgal
  haveI huLiesu₀ : u.LiesOver u₀ := hulies
  have huw : NK.GlobalCFT.Place.LiesOver (NK.GlobalCFT.Place.ofInfinite u)
      (NK.GlobalCFT.Place.ofInfinite u₀) := NK.GlobalCFT.Place.liesOver_ofInfinite hulies
  have huv₀ : NK.GlobalCFT.Place.LiesOver (NK.GlobalCFT.Place.ofInfinite u₀)
      (NK.GlobalCFT.Place.ofInfinite v) :=
    place_liesOver_trans (NK.GlobalCFT.Place.liesOver_ofInfinite hu₀lies) hvw
  have huv : NK.GlobalCFT.Place.LiesOver (NK.GlobalCFT.Place.ofInfinite u)
      (NK.GlobalCFT.Place.ofInfinite v) := place_liesOver_trans huw huv₀
  haveI huvI : u.LiesOver v := by
    rcases (NK.GlobalCFT.Place.liesOver_iff (NK.GlobalCFT.Place.ofInfinite u)
      (NK.GlobalCFT.Place.ofInfinite v)).mp huv with
      ⟨w', v', h1, h2, h3⟩ | ⟨q', Q', h1, h2, h3⟩
    · rw [NK.GlobalCFT.Place.ofInfinite_inj] at h1 h2
      rw [← h1, ← h2] at h3
      exact h3
    · exact absurd h1 (NK.GlobalCFT.Place.ofInfinite_ne_ofFinite u q')
  let φ₁ := NK.GlobalCFT.Place.localAlgebraMapUnits (NK.GlobalCFT.Place.ofInfinite u₀)
    (NK.GlobalCFT.Place.ofInfinite wK) hw₀
  let φ₂ := NK.GlobalCFT.Place.localAlgebraMapUnits (NK.GlobalCFT.Place.ofInfinite u)
    (NK.GlobalCFT.Place.ofInfinite u₀) huw
  let φ1' := NK.GlobalCFT.Place.localAlgebraMapUnits (NK.GlobalCFT.Place.ofInfinite wK)
    (NK.GlobalCFT.Place.ofInfinite v) hvw
  let ψ₀ := NK.GlobalCFT.Place.localAlgebraMapUnits (NK.GlobalCFT.Place.ofInfinite u₀)
    (NK.GlobalCFT.Place.ofInfinite v) huv₀
  let ψ₂ := NK.GlobalCFT.Place.localAlgebraMapUnits (NK.GlobalCFT.Place.ofInfinite u)
    (NK.GlobalCFT.Place.ofInfinite v) huv
  have hcompA : φ₁.comp φ1' = ψ₀ := localAlgebraMapUnits_comp hw₀ hvw huv₀
  have hcompB : φ₂.comp ψ₀ = ψ₂ := localAlgebraMapUnits_comp huw huv₀ huv
  have hinj : Function.Injective (φ₂.comp φ₁) :=
    (localAlgebraMapUnits_injective_ofInfinite (k := L₀) (K := L) (w := u) (v := u₀) huw).comp
      (localAlgebraMapUnits_injective_ofInfinite (k := K) (K := L₀) (w := u₀) (v := wK) hw₀)
  let D : Subgroup (L ≃ₐ[k] L) := MulAction.stabilizer (L ≃ₐ[k] L)
    (NK.GlobalCFT.Place.ofInfinite u)
  have hcardD : Nat.card ↥D = 2 :=
    natCard_stabilizer_place_ofInfinite_eq_two (k := k) u v hvR huC
  haveI : Fintype ↥D := Fintype.ofFinite ↥D
  have hfinQ : Fintype (↥D ⧸ (⊥ : Subgroup ↥D)) :=
    Fintype.ofSurjective (QuotientGroup.mk' (⊥ : Subgroup ↥D))
      (QuotientGroup.mk'_surjective (⊥ : Subgroup ↥D))
  have hcardQ : Nat.card (↥D ⧸ (⊥ : Subgroup ↥D)) = 2 := by
    rw [Nat.card_congr (QuotientGroup.quotientBot (G := ↥D)).toEquiv]
    exact hcardD
  refine ⟨L, hLf, hLn, hLk, hLL₀, hST, hLfd, hLgal, NK.GlobalCFT.Place.ofInfinite u, huw,
    (⊥ : Subgroup ↥D), inferInstance, hfinQ, ?_, ?_, ?_⟩
  · exact isCyclic_of_prime_card hcardQ
  · exact hcardQ
  · rintro ⟨bb, -, hsum⟩
    set uu : (NK.GlobalCFT.Place.localField L (NK.GlobalCFT.Place.ofInfinite u))ˣ :=
      Additive.toMul bb with huu
    have hbb : bb = Additive.ofMul uu := by
      rw [huu]
      exact (Equiv.apply_symm_apply Additive.ofMul bb).symm
    have hcardD' : Fintype.card ↥D = 2 := by rw [← Nat.card_eq_fintype_card]; exact hcardD
    have hcardQ' : Fintype.card (↥D ⧸ (⊥ : Subgroup ↥D)) = 2 := by
      rw [← Nat.card_eq_fintype_card]; exact hcardQ
    obtain ⟨c₁, hc₁ne, hcovD⟩ := exists_two_cover_of_card_eq_two hcardD'
    obtain ⟨q₁, hq₁ne, hcovQ⟩ := exists_two_cover_of_card_eq_two hcardQ' 
    have hc₁C : NumberField.ComplexEmbedding.IsConj u.embedding (c₁ : L ≃ₐ[k] L) := by
      have hmem : (c₁ : L ≃ₐ[k] L) ∈ MulAction.stabilizer (L ≃ₐ[k] L) u := by
        have h : (c₁ : L ≃ₐ[k] L) ∈ MulAction.stabilizer (L ≃ₐ[k] L)
            (NK.GlobalCFT.Place.ofInfinite u) := c₁.2
        rwa [stabilizer_place_ofInfinite_eq (k := k) u] at h
      rw [← NumberField.InfinitePlace.mk_embedding u] at hmem
      rcases (NumberField.InfinitePlace.mem_stabilizer_mk_iff u.embedding
        (c₁ : L ≃ₐ[k] L)).mp hmem with h | h
      · exact absurd (Subtype.ext h) hc₁ne
      · exact h
    set e := NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex huC with he
    have hc₁act : ∀ y : NK.GlobalCFT.Place.localField L (NK.GlobalCFT.Place.ofInfinite u),
        e (NK.HassePrinciple.localAutHom (K := k) (L := L) (NK.GlobalCFT.Place.ofInfinite u)
          c₁ y) = starRingEnd ℂ (e y) := by
      intro y
      exact Work.SSGRoute.ringEquivComplex_localAutHom (k := k) u huC c₁ (fun x => by
        have h := DFunLike.congr_fun hc₁C x
        rw [NumberField.ComplexEmbedding.conjugate_coe_eq] at h
        exact h.symm) y
    set E : (NK.GlobalCFT.Place.localField L (NK.GlobalCFT.Place.ofInfinite u))ˣ ≃* ℂˣ :=
      Units.mapEquiv e.toMulEquiv with hE
    have hElu : ∀ y : (NK.GlobalCFT.Place.localField L (NK.GlobalCFT.Place.ofInfinite u))ˣ,
        E (NK.HassePrinciple.localUnitsEquiv (K := k) (NK.GlobalCFT.Place.ofInfinite u) c₁ y)
          = Units.map (starRingEnd ℂ).toMonoidHom (E y) := by
      intro y
      apply Units.ext
      show e ((NK.HassePrinciple.localUnitsEquiv (K := k) (NK.GlobalCFT.Place.ofInfinite u) c₁ y :
            (NK.GlobalCFT.Place.localField L (NK.GlobalCFT.Place.ofInfinite u))ˣ) :
            NK.GlobalCFT.Place.localField L (NK.GlobalCFT.Place.ofInfinite u))
          = starRingEnd ℂ (e (y : NK.GlobalCFT.Place.localField L
              (NK.GlobalCFT.Place.ofInfinite u)))
      rw [NK.HassePrinciple.coe_localUnitsEquiv]
      exact hc₁act (y : NK.GlobalCFT.Place.localField L (NK.GlobalCFT.Place.ofInfinite u))
    set z : ℂ := e (uu : NK.GlobalCFT.Place.localField L (NK.GlobalCFT.Place.ofInfinite u)) with hz
    have hzne : z ≠ 0 := by
      intro h
      have h0 : e (uu : NK.GlobalCFT.Place.localField L (NK.GlobalCFT.Place.ofInfinite u)) = e 0 := by
        rw [← hz, h, map_zero]
      exact Units.ne_zero uu (e.injective h0)
    have hgnz : ((‖z‖ : ℝ) : ℂ) ≠ 0 := by
      simp only [Ne, Complex.ofReal_eq_zero]
      exact norm_ne_zero_iff.mpr hzne
    set g : (NK.GlobalCFT.Place.localField L (NK.GlobalCFT.Place.ofInfinite u))ˣ :=
      E.symm (Units.mk0 ((‖z‖ : ℝ) : ℂ) hgnz) with hgdef
    have hEg : E g = Units.mk0 ((‖z‖ : ℝ) : ℂ) hgnz := by
      rw [hgdef]; exact E.apply_symm_apply _
    have hEuu : E uu = Units.mk0 z hzne := by
      apply Units.ext
      show e (uu : NK.GlobalCFT.Place.localField L (NK.GlobalCFT.Place.ofInfinite u)) = z
      rfl
    have hg2 : g ^ 2 = uu * NK.HassePrinciple.localUnitsEquiv (K := k)
        (NK.GlobalCFT.Place.ofInfinite u) c₁ uu := by
      apply E.injective
      rw [map_pow, map_mul, hElu uu, hEg, hEuu]
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, Units.val_mul, Units.val_mk0, Units.coe_map]
      change (((‖z‖ : ℝ) : ℂ)) ^ 2 = z * (starRingEnd ℂ) z
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, ← Complex.ofReal_pow]
    have hgfix : ∀ τ : ↥D, NK.HassePrinciple.localUnitsEquiv (K := k)
        (NK.GlobalCFT.Place.ofInfinite u) τ g = g := by
      intro τ
      rcases hcovD τ with h | h
      · rw [h, NK.HassePrinciple.localUnitsEquiv_one]
        rfl
      · apply E.injective
        rw [h, hElu g, hEg]
        apply Units.ext
        rw [Units.coe_map, Units.val_mk0]
        change (starRingEnd ℂ) (((‖z‖ : ℝ) : ℂ)) = ((‖z‖ : ℝ) : ℂ)
        rw [Complex.conj_ofReal]
    have hsumprod : φ₂ (φ₁ a) = uu * NK.HassePrinciple.localUnitsEquiv (K := k)
        (NK.GlobalCFT.Place.ofInfinite u) c₁ uu := by
      have h := hsum
      rw [hbb] at h
      change (∑ x : ↥D ⧸ (⊥ : Subgroup ↥D), Additive.ofMul (NK.HassePrinciple.localUnitsEquiv
        (K := k) (NK.GlobalCFT.Place.ofInfinite u) (Quotient.out x) uu))
        = Additive.ofMul (φ₂ (φ₁ a)) at h
      rw [Work.SSGRoute.fintype_sum_ofMul] at h
      have hprod := Additive.ofMul.injective h
      rw [← hprod, Work.SSGRoute.prod_eq_mul_of_cover (1 : ↥D ⧸ (⊥ : Subgroup ↥D)) q₁
        (Ne.symm hq₁ne) hcovQ]
      have hout1 : (Quotient.out (1 : ↥D ⧸ (⊥ : Subgroup ↥D)) : ↥D) = 1 := by
        have h1 : QuotientGroup.mk' (⊥ : Subgroup ↥D)
            (Quotient.out (1 : ↥D ⧸ (⊥ : Subgroup ↥D))) = 1 := by
          rw [QuotientGroup.mk'_apply, QuotientGroup.out_eq']
        have hmem : (Quotient.out (1 : ↥D ⧸ (⊥ : Subgroup ↥D)) : ↥D) ∈
            (QuotientGroup.mk' (⊥ : Subgroup ↥D)).ker := MonoidHom.mem_ker.mpr h1
        rw [QuotientGroup.ker_mk'] at hmem
        exact Subgroup.mem_bot.mp hmem
      have houtq1 : (Quotient.out q₁ : ↥D) = c₁ := by
        rcases hcovD (Quotient.out q₁) with h | h
        · have hq : q₁ = 1 := by
            calc q₁ = QuotientGroup.mk' (⊥ : Subgroup ↥D) (Quotient.out q₁) := by
                  rw [QuotientGroup.mk'_apply, QuotientGroup.out_eq']
              _ = QuotientGroup.mk' (⊥ : Subgroup ↥D) 1 := by rw [h]
              _ = 1 := map_one _
          exact absurd hq hq₁ne
        · exact h
      rw [hout1, NK.HassePrinciple.localUnitsEquiv_one, houtq1]
      rfl
    obtain ⟨c₀, hc₀⟩ := localFixedUnits_mem_range_place (k := k) (K := L)
      (NK.GlobalCFT.Place.ofInfinite u) (NK.GlobalCFT.Place.ofInfinite v) huv g
      (fun σ => hgfix σ)
    have hpow : (φ1' c₀) ^ 2 = a := by
      apply hinj
      calc φ₂ (φ₁ ((φ1' c₀) ^ 2)) = φ₂ (φ₁ (φ1' (c₀ ^ 2))) := by rw [← map_pow φ1' c₀ 2]
        _ = φ₂ ((φ₁.comp φ1') (c₀ ^ 2)) := rfl
        _ = φ₂ (ψ₀ (c₀ ^ 2)) := by rw [hcompA]
        _ = (φ₂.comp ψ₀) (c₀ ^ 2) := rfl
        _ = ψ₂ (c₀ ^ 2) := by rw [hcompB]
        _ = (ψ₂ c₀) ^ 2 := map_pow ψ₂ c₀ 2
        _ = g ^ 2 := by rw [hc₀]
        _ = uu * NK.HassePrinciple.localUnitsEquiv (K := k)
              (NK.GlobalCFT.Place.ofInfinite u) c₁ uu := hg2
        _ = φ₂ (φ₁ a) := hsumprod.symm
    exact ha ⟨φ1' c₀, fun σ => localUnitsEquiv_localAlgebraMapUnits_eq_self_place hvw c₀ σ, hpow⟩

end Work.SSGRoute
