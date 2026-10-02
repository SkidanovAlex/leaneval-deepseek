import Mathlib
import Submission.Work.Cohomology.sphere3DiscPairDefs
import Submission.Work.Cohomology.CupRing
import Submission.Work.Cohomology.Pullback
import Submission.Work.Cohomology.kronH_isIso
import Submission.Work.Cohomology.sphereCohomologyTop
import Submission.Work.Cohomology.sphereVanishing
import Submission.Work.Cohomology.sphereInUnitHomologyIso
import Submission.Work.Cohomology.CompatTrans.sphere3DiscPairHomology
import Submission.Work.Cohomology.cup1Identity
import Submission.Work.Cohomology.Kunneth.KunnethPullbackAux
import Submission.Work.Endgame.VkClean.EZShuffleLoc

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

open CategoryTheory AlgebraicTopology CategoryTheory.Limits
open scoped Topology Simplicial MonoidalCategory

namespace Work.Cohomology

noncomputable section

/-! ## 0. Notation -/

/-- The sphere `S³ = ∂D⁴ ⊆ D⁴`. -/
abbrev SphInT : TopCat := TopCat.of (sphereInUnit 4)

/-- The singular simplicial set of `S³ = Sph3T`. -/
abbrev ssSph3T : SSet := TopCat.toSSet.obj Sph3T

/-- The singular simplicial set of `S³ ⊆ D⁴`. -/
abbrev ssSphInT : SSet := TopCat.toSSet.obj SphInT

/-- The singular simplicial set of the sphere bundle `A = PairAT`. -/
abbrev ssPairAT : SSet := TopCat.toSSet.obj (TopCat.of PairAT)

/-- The singular simplicial set of the total space `X = PairXT`. -/
abbrev ssPairXT : SSet := TopCat.toSSet.obj PairXT

/-! ## 1. The additive (co)homology of `A = PairAT = S³ × S³` -/

/-- The singular homology of `A = PairAT = S³ × S³` is degreewise free. -/
theorem free_singularHomology_PairAT (n : ℕ) :
    Module.Free ℤ ↥((chainC ℤ ssPairAT).homology n) := by
  obtain ⟨e⟩ := HA_iso_expo n
  haveI : Module.Free ℤ ↥(ModuleCat.of ℤ (Fin (expo 3 3 n) → ℤ)) := inferInstance
  exact Module.Free.of_equiv (σ := RingHom.id ℤ) (σ' := RingHom.id ℤ)
    (uctIsoToLinearEquiv e).symm

/-- `H₆(S³ × S³; ℤ) ≅ ℤ`. -/
theorem HA_six_iso_int : Nonempty ((chainC ℤ ssPairAT).homology 6 ≅ ModuleCat.of ℤ ℤ) := by
  obtain ⟨e⟩ := HA_iso_expo 6
  have h6 : expo 3 3 6 = 1 := by
    have h := expo_top 3 3 (by norm_num) (by norm_num)
    norm_num at h
    exact h
  rw [h6] at e
  exact ⟨e ≪≫ LinearEquiv.toModuleIso (LinearEquiv.funUnique (Fin 1) ℤ ℤ)⟩

/-- A chosen additive isomorphism `H₆(S³ × S³; ℤ) ≅ ℤ`. -/
noncomputable def e6PairAT : ↥((chainC ℤ ssPairAT).homology 6) ≃ₗ[ℤ] ℤ :=
  uctIsoToLinearEquiv (HA_six_iso_int.some)

/-! ## 2. The isomorphism `H⁶(A) ≅ ℤ` induced by the Kronecker pairing -/

/-- Every class of `H₆` is a multiple of the chosen generator. -/
theorem smul_symm_one_e6 (v : ↥((chainC ℤ ssPairAT).homology 6)) :
    v = (e6PairAT v) • e6PairAT.symm 1 := by
  apply e6PairAT.injective
  rw [map_zsmul, LinearEquiv.apply_symm_apply, smul_eq_mul, mul_one]

/-- Evaluation at the chosen generator of `H₆`. -/
noncomputable def evalGen6 : (↥((chainC ℤ ssPairAT).homology 6) →ₗ[ℤ] ℤ) →ₗ[ℤ] ℤ where
  toFun φ := φ (e6PairAT.symm 1)
  map_add' φ ψ := by simp
  map_smul' a φ := by simp

theorem evalGen6_apply (φ : ↥((chainC ℤ ssPairAT).homology 6) →ₗ[ℤ] ℤ) :
    evalGen6 φ = φ (e6PairAT.symm 1) := rfl

theorem evalGen6_bijective : Function.Bijective evalGen6 := by
  constructor
  · intro φ ψ h
    ext v
    have key : ∀ χ : ↥((chainC ℤ ssPairAT).homology 6) →ₗ[ℤ] ℤ,
        χ v = (e6PairAT v) * χ (e6PairAT.symm 1) := by
      intro χ
      nth_rewrite 1 [smul_symm_one_e6 v]
      rw [map_zsmul, smul_eq_mul]
    rw [key φ, key ψ]
    rw [show φ (e6PairAT.symm 1) = ψ (e6PairAT.symm 1) from h]
  · intro m
    exact ⟨m • (e6PairAT : _ →ₗ[ℤ] ℤ), by
      show (m • (e6PairAT : _ →ₗ[ℤ] ℤ)) (e6PairAT.symm 1) = m
      rw [LinearMap.smul_apply]
      have hsym : (e6PairAT : _ →ₗ[ℤ] ℤ) (e6PairAT.symm 1) = (1 : ℤ) :=
        LinearEquiv.apply_symm_apply e6PairAT 1
      rw [hsym, smul_eq_mul, mul_one]⟩

/-- The isomorphism `H⁶(S³ × S³; ℤ) ≅ ℤ` obtained by composing the Kronecker pairing with the
evaluation at the chosen generator of `H₆`. -/
noncomputable def e6CohPairAT : ↥((cochainC ℤ ssPairAT).homology 6) ≃ₗ[ℤ] ℤ :=
  (LinearEquiv.ofBijective (kronH ℤ ssPairAT 6)
      (kronH_isIso (TopCat.of PairAT) free_singularHomology_PairAT 6)).trans
    (LinearEquiv.ofBijective evalGen6 evalGen6_bijective)

theorem e6CohPairAT_apply (γ : ↥((cochainC ℤ ssPairAT).homology 6)) :
    e6CohPairAT γ = kronH ℤ ssPairAT 6 γ (e6PairAT.symm 1) := rfl

/-- **The Kronecker pairing against a class is the product of the two `e6`-coordinates.** -/
theorem kronH_eq_mul (γ : ↥((cochainC ℤ ssPairAT).homology 6))
    (v : ↥((chainC ℤ ssPairAT).homology 6)) :
    kronH ℤ ssPairAT 6 γ v = e6CohPairAT γ * e6PairAT v := by
  nth_rewrite 1 [smul_symm_one_e6 v]
  rw [map_zsmul, smul_eq_mul, ← e6CohPairAT_apply, mul_comm]

/-! ## 3. Linear algebra over `ℤ`: `±1` generates `ℤ` -/

/-- Transporting a generating singleton along a linear isomorphism. -/
theorem span_eq_top_of_iso_int {M N : Type*} [AddCommGroup M] [Module ℤ M] [AddCommGroup N]
    [Module ℤ N] (e : M ≃ₗ[ℤ] N) {x : M} (hx : Submodule.span ℤ {x} = ⊤) :
    Submodule.span ℤ {e x} = ⊤ := by
  have h1 : Submodule.map (e : M →ₗ[ℤ] N) (Submodule.span ℤ {x}) = Submodule.span ℤ {e x} := by
    rw [Submodule.map_span]
    simp
  rw [← h1, hx, Submodule.map_top]
  exact LinearMap.range_eq_top.mpr e.surjective

/-- `1` generates `ℤ` as a `ℤ`-submodule. -/
theorem span_one_int : Submodule.span ℤ ({(1 : ℤ)} : Set ℤ) = ⊤ := by
  rw [Submodule.span_singleton_eq_top_iff]
  intro v
  exact ⟨v, by rw [smul_eq_mul, mul_one]⟩

/-- `-1` generates `ℤ` as a `ℤ`-submodule. -/
theorem span_neg_one_int : Submodule.span ℤ ({(-1 : ℤ)} : Set ℤ) = ⊤ := by
  rw [Submodule.span_singleton_eq_top_iff]
  intro v
  refine ⟨-v, ?_⟩
  rw [smul_eq_mul]
  ring

/-- **A class of `H⁶(S³ × S³; ℤ)` whose Kronecker pairing with some class of `H₆` hits `1` is a
generator.** -/
theorem span_eq_top_of_kronH_eq_one
    (γ : ↥((cochainC ℤ ssPairAT).homology 6))
    (z : ↥((chainC ℤ ssPairAT).homology 6))
    (h : kronH ℤ ssPairAT 6 γ z = 1) :
    Submodule.span ℤ {γ} = ⊤ := by
  have hmul : e6CohPairAT γ * e6PairAT z = 1 := by
    rw [← kronH_eq_mul γ z, h]
  have hγ : e6CohPairAT γ = 1 ∨ e6CohPairAT γ = -1 :=
    Int.eq_one_or_neg_one_of_mul_eq_one hmul
  rcases hγ with hg | hg
  · have hgen := span_eq_top_of_iso_int e6CohPairAT.symm (x := e6CohPairAT γ)
      (by rw [hg]; exact span_one_int)
    simpa using hgen
  · have hgen := span_eq_top_of_iso_int e6CohPairAT.symm (x := e6CohPairAT γ)
      (by rw [hg]; exact span_neg_one_int)
    simpa using hgen

/-! ## 4. Pullback of cochains along simplicial maps -/

/-- **Functoriality of the pullback of cochains along simplicial maps.** -/
theorem ssetPullback_comp' (X Y Z : SSet) (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ)
    (γ : Cochain ℤ Z n) :
    Kunneth.ssetPullback X Z (f ≫ g) n γ
      = Kunneth.ssetPullback X Y f n (Kunneth.ssetPullback Y Z g n γ) := by
  apply cup_ext ℤ X
  intro σ
  rw [Kunneth.ssetPullback_genEval, Kunneth.ssetPullback_genEval,
    Kunneth.ssetPullback_genEval]
  rfl

/-- The pullback of a coboundary is the coboundary of the pullback. -/
theorem ssetPullback_cochainDiff' (X Y : SSet) (f : X ⟶ Y) (n : ℕ) (γ : Cochain ℤ Y n) :
    Kunneth.ssetPullback X Y f (n + 1) (cochainDiff ℤ Y γ)
      = cochainDiff ℤ X (Kunneth.ssetPullback X Y f n γ) := by
  apply LinearMap.ext
  intro w
  simp only [Kunneth.ssetPullback, LinearMap.dualMap_apply, cochainDiff, LinearMap.comp_apply]
  congr 1
  exact LinearMap.congr_fun
    (congrArg ModuleCat.Hom.hom ((SSet.chainComplexMap f (ModuleCat.of ℤ ℤ)).comm (n + 1) n)) w

/-- The pullback of a cocycle is a cocycle. -/
theorem ssetPullback_cocycle' (X Y : SSet) (f : X ⟶ Y) (n : ℕ) (γ : Cochain ℤ Y n)
    (hγ : cochainDiff ℤ Y γ = 0) :
    cochainDiff ℤ X (Kunneth.ssetPullback X Y f n γ) = 0 := by
  rw [← ssetPullback_cochainDiff' X Y f n γ, hγ]
  simp only [Kunneth.ssetPullback, map_zero]

/-! ## 5. Freeness of the (co)homology of the two spheres -/

/-- The singular homology of `S³ = Sph3T` is degreewise free. -/
theorem free_homology_Sph3T (n : ℕ) :
    Module.Free ℤ ↥((chainC ℤ ssSph3T).homology n) := by
  rcases eq_or_ne n 0 with h0 | h0
  · subst h0
    haveI : PathConnectedSpace ↥Sph3T := inferInstance
    haveI : IsIso (TopCat.singularHomology₀ε Sph3T (ModuleCat.of ℤ ℤ)) := inferInstance
    haveI : Module.Free ℤ ↥(ModuleCat.of ℤ ℤ) := inferInstance
    exact Module.Free.of_equiv (σ := RingHom.id ℤ) (σ' := RingHom.id ℤ)
      (uctIsoToLinearEquiv
        (asIso (TopCat.singularHomology₀ε Sph3T (ModuleCat.of ℤ ℤ)))).symm
  · rcases eq_or_ne n 3 with h3 | h3
    · subst h3
      obtain ⟨e⟩ := sphereHomologyTop 3 (by norm_num)
      haveI : Module.Free ℤ ↥(ModuleCat.of ℤ ℤ) := inferInstance
      exact Module.Free.of_equiv (σ := RingHom.id ℤ) (σ' := RingHom.id ℤ)
        (uctIsoToLinearEquiv e).symm
    · have hz := sphereVanishing 3 n (by norm_num) h0 h3
      haveI : Subsingleton ↥((chainC ℤ ssSph3T).homology n) :=
        (ModuleCat.isZero_iff_subsingleton).mp hz
      exact Module.Free.of_subsingleton ℤ _

/-- `H₃(S³; ℤ) ≅ ℤ`. -/
theorem homologyTop_Sph3T :
    Nonempty ((chainC ℤ ssSph3T).homology 3 ≅ ModuleCat.of ℤ ℤ) :=
  sphereHomologyTop 3 (by norm_num)

/-- The singular homology of `S³ = ∂D⁴ ⊆ D⁴` is degreewise free. -/
theorem free_homology_SphInT (n : ℕ) :
    Module.Free ℤ ↥((chainC ℤ ssSphInT).homology n) := by
  obtain ⟨e⟩ := sphereInUnitHomologyIso 4 n
  exact Module.Free.of_equiv' (free_homology_Sph3T n) (uctIsoToLinearEquiv e).symm

/-- `H₃(S³ = ∂D⁴; ℤ) ≅ ℤ`. -/
theorem homologyTop_SphInT :
    Nonempty ((chainC ℤ ssSphInT).homology 3 ≅ ModuleCat.of ℤ ℤ) := by
  obtain ⟨e1⟩ := sphereInUnitHomologyIso 4 3
  obtain ⟨e2⟩ := sphereHomologyTop 3 (by norm_num)
  exact ⟨e1 ≪≫ e2⟩

/-! ## 6. A cycle chain detected exactly by a cocycle -/

/-- **A `3`-cycle and a `3`-cocycle evaluating to `1` on it.**  Used for a space whose singular
homology is degreewise free with `H₃ ≅ ℤ`; the cocycle is chosen so that its Kronecker functional
is the inverse isomorphism to `ℤ`. -/
theorem exists_cycle_cocycle_eval_one (T : TopCat)
    (hfree : ∀ n, Module.Free ℤ ↥((singularChains ℤ T).homology n))
    (hH3 : Nonempty ((singularChains ℤ T).homology 3 ≅ ModuleCat.of ℤ ℤ)) :
    ∃ (z : (chainC ℤ (TopCat.toSSet.obj T)).cycles 3)
      (Θ : Cochain ℤ (TopCat.toSSet.obj T) 3),
      cochainDiff ℤ (TopCat.toSSet.obj T) Θ = 0 ∧
      Θ (((chainC ℤ (TopCat.toSSet.obj T)).iCycles 3).hom z) = 1 := by
  obtain ⟨e⟩ := hH3
  have hbij := kronH_isIso T hfree 3
  obtain ⟨x, hx⟩ := hbij.2 (ModuleCat.Hom.hom e.hom)
  obtain ⟨y, hy⟩ := (ModuleCat.epi_iff_surjective
    ((cochainC ℤ (TopCat.toSSet.obj T)).homologyπ 3)).mp inferInstance x
  set Θ : Cochain ℤ (TopCat.toSSet.obj T) 3 :=
    cochainOfCycle ℤ (TopCat.toSSet.obj T) 3 y with hΘdef
  have hΘ : cochainDiff ℤ (TopCat.toSSet.obj T) Θ = 0 :=
    cochainDiff_iCycles ℤ (TopCat.toSSet.obj T) 3 y
  have hxΘ : cohomologyClassOf ℤ (TopCat.toSSet.obj T) Θ hΘ = x := by
    show (cochainC ℤ (TopCat.toSSet.obj T)).homologyπ 3
      (cocycleOf ℤ (TopCat.toSSet.obj T) Θ hΘ) = x
    rw [show cocycleOf ℤ (TopCat.toSSet.obj T) Θ hΘ = y from ?_, hy]
    apply iCycles_injective ℤ (TopCat.toSSet.obj T) 3
    rw [iCycles_cocycleOf]
    rfl
  set v : ↥((singularChains ℤ T).homology 3) := (ModuleCat.Hom.hom e.inv) 1 with hv
  obtain ⟨z, hz⟩ := (ModuleCat.epi_iff_surjective
    ((chainC ℤ (TopCat.toSSet.obj T)).homologyπ 3)).mp inferInstance v
  refine ⟨z, Θ, hΘ, ?_⟩
  have hcomp : ModuleCat.Hom.hom e.hom (ModuleCat.Hom.hom e.inv (1 : ℤ)) = 1 := by
    have h := congrArg (fun (g : ModuleCat.of ℤ ℤ ⟶ ModuleCat.of ℤ ℤ) => g.hom (1 : ℤ))
      e.inv_hom_id
    simpa using h
  have hkey : (kronH ℤ (TopCat.toSSet.obj T) 3) x v = 1 :=
    calc (kronH ℤ (TopCat.toSSet.obj T) 3) x v
        = ModuleCat.Hom.hom e.hom v := LinearMap.congr_fun hx v
      _ = 1 := by rw [hv]; exact hcomp
  rw [← kronH_apply (R := ℤ) (X := TopCat.toSSet.obj T) (α := Θ) hΘ z, hxΘ, hz]
  exact hkey

/-- **On a cycle, `α ∘ PInfty` agrees with `α`, for every cocycle `α`** (chain-level form). -/
theorem PInf_apply_cycle_eq_chain' (X : SSet) (c : (chainC ℤ X).X 3)
    (hc : ((chainC ℤ X).d 3 2).hom c = 0) (α : Cochain ℤ X 3)
    (hα : cochainDiff ℤ X α = 0) :
    α (PInf X 3 c) = α c := by
  set H := X.homotopyEquivNormalizedChainComplex (ModuleCat.of ℤ ℤ) with hH
  have hcomm := congrArg (fun (f : (X.chainComplex (ModuleCat.of ℤ ℤ)).X 3 ⟶
      (X.chainComplex (ModuleCat.of ℤ ℤ)).X 3) => f.hom c) (H.homotopyHomInvId.comm 3)
  rw [HomologicalComplex.comp_f] at hcomm
  simp only [ModuleCat.hom_add, LinearMap.add_apply] at hcomm
  have hD : (ModuleCat.Hom.hom ((dNext 3) H.homotopyHomInvId.hom)) c = 0 := by
    rw [dNext_eq _ (show (ComplexShape.down ℕ).Rel 3 2 from rfl), ModuleCat.hom_comp]
    simp only [LinearMap.comp_apply, hc, map_zero]
  rw [hD, zero_add] at hcomm
  rw [prevD_eq _ (show (ComplexShape.down ℕ).Rel 4 3 from rfl)] at hcomm
  rw [ModuleCat.hom_comp] at hcomm
  simp only [LinearMap.comp_apply] at hcomm
  rw [show (ModuleCat.Hom.hom (((𝟙 (X.chainComplex (ModuleCat.of ℤ ℤ)) :
      X.chainComplex (ModuleCat.of ℤ ℤ) ⟶ X.chainComplex (ModuleCat.of ℤ ℤ))).f 3)) c = c
      from rfl] at hcomm
  have hhom : H.hom = X.toNormalizedChainComplex (ModuleCat.of ℤ ℤ) := by
    rw [hH]; exact SSet.homotopyEquivNormalizedChainComplex_hom X (ModuleCat.of ℤ ℤ)
  have hinv : H.inv = X.fromNormalizedChainComplex (ModuleCat.of ℤ ℤ) := by
    rw [hH]; exact SSet.homotopyEquivNormalizedChainComplex_inv X (ModuleCat.of ℤ ℤ)
  have hcomp : PInf X 3 c
      = (ModuleCat.Hom.hom (H.inv.f 3)) ((ModuleCat.Hom.hom (H.hom.f 3)) c) := by
    simp only [PInf, HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply,
      hhom, hinv]
  have hcomm' : (ModuleCat.Hom.hom (H.inv.f 3)) ((ModuleCat.Hom.hom (H.hom.f 3)) c)
      = ((X.chainComplex (ModuleCat.of ℤ ℤ)).d 4 3).hom
          ((H.homotopyHomInvId.hom 3 4) c) + c := by
    rw [hcomm, ModuleCat.hom_comp, LinearMap.comp_apply]
  have hzero : α (((X.chainComplex (ModuleCat.of ℤ ℤ)).d 4 3).hom
      ((H.homotopyHomInvId.hom 3 4) c)) = 0 := by
    have h := congrArg (fun (g : (X.chainComplex (ModuleCat.of ℤ ℤ)).X 4 →ₗ[ℤ] ℤ) =>
      g ((H.homotopyHomInvId.hom 3 4) c)) hα
    simpa only [cochainDiff, LinearMap.comp_apply, LinearMap.zero_apply] using h
  rw [hcomp, hcomm', map_add, hzero, zero_add]

/-- A simplex obtained from a non-surjective monotone self-map of `⦋n+1⦌` is degenerate. -/
theorem mem_degenerate_of_not_surjective' {X : SSet} (n : ℕ) (f : ⦋n + 1⦌ ⟶ ⦋n + 1⦌)
    (hf : ¬ Function.Surjective ⇑f) (x : X _⦋n + 1⦌) :
    X.map f.op x ∈ X.degenerate (n + 1) :=
  Crux33.mem_degenerate_of_not_injective n f
    (fun hinj => hf (Finite.injective_iff_surjective.mp hinj)) x

/-- **A `3`-cycle and a normalised `3`-cocycle evaluating to `1` on it.** -/
theorem exists_cycle_normalized_eval_one (T : TopCat)
    (hfree : ∀ n, Module.Free ℤ ↥((singularChains ℤ T).homology n))
    (hH3 : Nonempty ((singularChains ℤ T).homology 3 ≅ ModuleCat.of ℤ ℤ)) :
    ∃ (z : (chainC ℤ (TopCat.toSSet.obj T)).cycles 3)
      (Λ : Cochain ℤ (TopCat.toSSet.obj T) 3),
      cochainDiff ℤ (TopCat.toSSet.obj T) Λ = 0 ∧
      (∀ (v : (TopCat.toSSet.obj T) _⦋3⦌) (g : ⦋3⦌ ⟶ ⦋3⦌), ¬ Function.Surjective ⇑g →
        genEval ℤ (TopCat.toSSet.obj T) Λ ((TopCat.toSSet.obj T).map g.op v) = 0) ∧
      Λ (((chainC ℤ (TopCat.toSSet.obj T)).iCycles 3).hom z) = 1 := by
  obtain ⟨z, Θ, hΘ, hev⟩ := exists_cycle_cocycle_eval_one T hfree hH3
  refine ⟨z, Θ.comp (PInf (TopCat.toSSet.obj T) 3), ?_, ?_, ?_⟩
  · exact cochainDiff_comp_PInf _ Θ hΘ
  · intro v g hg
    simp only [genEval, LinearMap.comp_apply]
    rw [PInf_degenerate (TopCat.toSSet.obj T) ((TopCat.toSSet.obj T).map g.op v)
      (mem_degenerate_of_not_surjective' 2 g hg v)]
    simp
  · rw [LinearMap.comp_apply, PInf_apply_cycle_eq_chain' (TopCat.toSSet.obj T) _ ?_ Θ hΘ]
    · exact hev
    · have h := congrArg (fun (g : (chainC ℤ (TopCat.toSSet.obj T)).cycles 3 ⟶
          (chainC ℤ (TopCat.toSSet.obj T)).X 2) => g.hom z)
        (HomologicalComplex.iCycles_d (chainC ℤ (TopCat.toSSet.obj T)) 3 2)
      simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
        LinearMap.zero_apply] using h

/-! ## 7. The transport `Sing S³ ⊗ Sing (S³ ⊆ D⁴) ⟶ Sing A` -/

/-- The homeomorphism `S³ × S³ ≅ A = PairAT`. -/
def pairHomeo : TopCat.of (↥Sph3T × ↥SphInT) ≅ TopCat.of PairAT :=
  TopCat.isoOfHomeo
    { toFun := fun p ↦ ⟨(p.1, p.2.1), p.2.2⟩
      invFun := fun q ↦ (q.1.1, ⟨q.1.2, q.2⟩)
      left_inv := fun p ↦ by rfl
      right_inv := fun q ↦ by rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }

/-- The first projection of the pairing homeomorphism. -/
theorem pairHomeo_fst :
    pairHomeo.hom ≫ pj1A = SemiCartesianMonoidalCategory.fst Sph3T SphInT := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro p
  rfl

/-- The second projection of the pairing homeomorphism. -/
theorem pairHomeo_snd :
    pairHomeo.hom ≫ pj2A = SemiCartesianMonoidalCategory.snd Sph3T SphInT := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro q
  rfl

/-- **The pairing simplicial map `Sing S³ ⊗ Sing (S³ ⊆ D⁴) ⟶ Sing A` with its two
projections.** -/
theorem pairMapToPairAT' :
    ∃ φ : ssSph3T ⊗ ssSphInT ⟶ ssPairAT,
      (φ ≫ TopCat.toSSet.map pj1A = SemiCartesianMonoidalCategory.fst ssSph3T ssSphInT) ∧
      (φ ≫ TopCat.toSSet.map pj2A = SemiCartesianMonoidalCategory.snd ssSph3T ssSphInT) := by
  refine ⟨(Functor.Monoidal.μIso TopCat.toSSet Sph3T SphInT).hom ≫
    TopCat.toSSet.map pairHomeo.hom, ?_, ?_⟩
  · rw [Category.assoc, ← Functor.map_comp, pairHomeo_fst]
    exact Functor.Monoidal.μ_fst TopCat.toSSet Sph3T SphInT
  · rw [Category.assoc, ← Functor.map_comp, pairHomeo_snd]
    exact Functor.Monoidal.μ_snd TopCat.toSSet Sph3T SphInT

/-! ## 8. Graded commutativity of the cup product of two odd cochains on a cycle -/

/-- **The cup product of two degree `3` cochains is graded-commutative on cycles.**  The two
products differ by the coboundary `d (cup1 α β)`, which vanishes on a cycle. -/
theorem cup_swap_on_cycle (X : SSet) (α β : Cochain ℤ X 3)
    (hα : cochainDiff ℤ X α = 0) (hβ : cochainDiff ℤ X β = 0)
    (z : (chainC ℤ X).X 6) (hz : ((chainC ℤ X).d 6 5).hom z = 0) :
    (cup ℤ X α β) z = - (cup ℤ X β α) z := by
  have hid := cup1Identity ℤ X 3 3 (by norm_num) (by norm_num) α β hα hβ
  have hcast1 : (Nat.sub_add_cancel (by omega : 1 ≤ 3 + 3)) ▸
      (cochainDiff ℤ X (cup1 ℤ X 3 3 α β)) = cochainDiff ℤ X (cup1 ℤ X 3 3 α β) := by
    rw [Subsingleton.elim (Nat.sub_add_cancel (by omega : 1 ≤ 3 + 3)) rfl]
  have hcast2 : ((Nat.add_comm 3 3 : 3 + 3 = 3 + 3)) ▸ (cup ℤ X β α) = cup ℤ X β α := by
    rw [Subsingleton.elim (Nat.add_comm 3 3 : 3 + 3 = 3 + 3) rfl]
  rw [hcast1, hcast2, show ((-1 : ℤ) ^ (3 * 3)) = -1 from by norm_num] at hid
  have h2 := congrArg (fun (γ : Cochain ℤ X (3 + 3)) => γ z) hid
  have h3 : (cochainDiff ℤ X (cup1 ℤ X 3 3 α β)) z = 0 := by
    show (cup1 ℤ X 3 3 α β) (((chainC ℤ X).d 6 5) z) = 0
    rw [hz, map_zero]
  have h2' : (cup ℤ X α β - (-1 : ℤ) • cup ℤ X β α) z = 0 := by rw [← h2, h3]
  rw [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, neg_one_mul] at h2'
  exact sub_eq_zero.mp h2'

/-! ## 9. The evaluated external product -/

/-- **The external product of the two factor classes of the sphere bundle, in evaluated form.**
For `X = PairXT = S³ × D⁴` and `A = PairAT = S³ × S³ = ∂X` there are classes `b ∈ H³(X;ℤ)`,
`β ∈ H³(A;ℤ)` and a homology class `z ∈ H₆(A;ℤ)` such that the Kronecker pairing of the
Alexander–Whitney product of the restriction of `b` with `β` against `z` is `1`.

The proof takes `b` to be the pullback of a generator of `H³(S³)` along the first projection and
`β` the pullback of a normalised cocycle of the second sphere along `pj2A`; the homology class is
the Eilenberg–Zilber shuffle of the two fundamental cycles transported to `A`.  The value of the
pairing is `-(-β(c)·θ(d)) = β(c)θ(d) = 1`, the two signs being the sign of the shuffle cell and the
graded commutativity of `⌣` in odd degrees. -/
theorem sph3Disc_restr_cup_eval_one :
    ∃ (b : singularCohomology ℤ 3 PairXT) (β : singularCohomology ℤ 3 (TopCat.of PairAT))
      (z : (singularChains ℤ (TopCat.of PairAT)).homology 6),
      kronH ℤ ssPairAT 6
        (cupH' ℤ ssPairAT 3 3
          (ModuleCat.Hom.hom (HomologicalComplex.homologyMap (restr ℤ PairXT PairAT) 3) b) β)
        z = 1 := by
  obtain ⟨zX, ψ, hψ, hevψ⟩ :=
    exists_cycle_cocycle_eval_one Sph3T free_homology_Sph3T homologyTop_Sph3T
  obtain ⟨zY, Λ, hΛ, hΛdeg, hevΛ⟩ :=
    exists_cycle_normalized_eval_one SphInT free_homology_SphInT homologyTop_SphInT
  obtain ⟨phi, hphi1, hphi2⟩ := pairMapToPairAT'
  -- the two `3`-cycles
  set c : (chainC ℤ ssSph3T).X 3 := ((chainC ℤ ssSph3T).iCycles 3).hom zX with hcdef
  set d : (chainC ℤ ssSphInT).X 3 := ((chainC ℤ ssSphInT).iCycles 3).hom zY with hddef
  have hc : Crux33.d32 ssSph3T c = 0 := by
    rw [hcdef]
    have h := congrArg (fun (g : (chainC ℤ ssSph3T).cycles 3 ⟶ (chainC ℤ ssSph3T).X 2) =>
      g.hom zX) (HomologicalComplex.iCycles_d (chainC ℤ ssSph3T) 3 2)
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
      LinearMap.zero_apply] using h
  have hd : Crux33.d32 ssSphInT d = 0 := by
    rw [hddef]
    have h := congrArg (fun (g : (chainC ℤ ssSphInT).cycles 3 ⟶ (chainC ℤ ssSphInT).X 2) =>
      g.hom zY) (HomologicalComplex.iCycles_d (chainC ℤ ssSphInT) 3 2)
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
      LinearMap.zero_apply] using h
  have hcycle : Crux33.Td65 ssSph3T ssSphInT (Kunneth.ezChain ssSph3T ssSphInT c d) = 0 :=
    Crux33.ezChain_isCycle ssSph3T ssSphInT c d hc hd
  -- the transported `6`-cycle of `A`
  set w : (chainC ℤ ssPairAT).X 6 :=
    (SSet.chainComplexMap phi (ModuleCat.of ℤ ℤ)).f 6
      (Kunneth.ezChain ssSph3T ssSphInT c d) with hwdef
  have hw : ((chainC ℤ ssPairAT).d 6 5) w = 0 := by
    rw [hwdef]
    have hcomm := congrArg ModuleCat.Hom.hom
      ((SSet.chainComplexMap phi (ModuleCat.of ℤ ℤ)).comm 6 5)
    have h := LinearMap.congr_fun hcomm (Kunneth.ezChain ssSph3T ssSphInT c d)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
    rw [hcycle, map_zero] at h
    exact h
  have hk : (ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ ((chainC ℤ ssPairAT).X 6) w)) ≫
      (chainC ℤ ssPairAT).d 6 5 = 0 := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext_ring
    show (ModuleCat.Hom.hom ((chainC ℤ ssPairAT).d 6 5))
        ((LinearMap.toSpanSingleton ℤ ((chainC ℤ ssPairAT).X 6) w) 1) = 0
    rw [LinearMap.toSpanSingleton_apply_one]
    exact hw
  set wcycle : (chainC ℤ ssPairAT).cycles 6 :=
    ((chainC ℤ ssPairAT).liftCycles
      (ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ ((chainC ℤ ssPairAT).X 6) w)) 5
      (ChainComplex.next_nat_succ 5) hk).hom 1 with hwcdef
  have hwcycle : ((chainC ℤ ssPairAT).iCycles 6).hom wcycle = w := by
    rw [hwcdef]
    have h := congrArg (fun (g : ModuleCat.of ℤ ℤ ⟶ (chainC ℤ ssPairAT).X 6) => g.hom 1)
      (HomologicalComplex.liftCycles_i (chainC ℤ ssPairAT)
        (ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ ((chainC ℤ ssPairAT).X 6) w)) 5
        (ChainComplex.next_nat_succ 5) hk)
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom,
      LinearMap.toSpanSingleton_apply_one] using h
  -- the two cocycles on `A`
  set αA : Cochain ℤ ssPairAT 3 :=
    (cochainPullbackHom ℤ (TopCat.of PairAT) Sph3T pj1A 3).hom ψ with hαAdef
  set βA : Cochain ℤ ssPairAT 3 :=
    (cochainPullbackHom ℤ (TopCat.of PairAT) SphInT pj2A 3).hom Λ with hβAdef
  have hαAcoc : cochainDiff ℤ ssPairAT αA = 0 := by
    rw [hαAdef]
    exact Kunneth.pullback_cocycle (TopCat.of PairAT) Sph3T pj1A 3 ψ hψ
  have hβAcoc : cochainDiff ℤ ssPairAT βA = 0 := by
    rw [hβAdef]
    exact Kunneth.pullback_cocycle (TopCat.of PairAT) SphInT pj2A 3 Λ hΛ
  -- the evaluation
  have hev1 : (cup ℤ ssPairAT αA βA) w
      = (Kunneth.ssetPullback (ssSph3T ⊗ ssSphInT) ssPairAT phi 6 (cup ℤ ssPairAT αA βA))
          (Kunneth.ezChain ssSph3T ssSphInT c d) := by
    rw [hwdef]
    rfl
  have hev2 : Kunneth.ssetPullback (ssSph3T ⊗ ssSphInT) ssPairAT phi 6 (cup ℤ ssPairAT αA βA)
      = cup ℤ (ssSph3T ⊗ ssSphInT)
          (Kunneth.ssetPullback (ssSph3T ⊗ ssSphInT) ssPairAT phi 3 αA)
          (Kunneth.ssetPullback (ssSph3T ⊗ ssSphInT) ssPairAT phi 3 βA) :=
    (cupNatural ℤ phi αA βA).symm
  have hev3 : Kunneth.ssetPullback (ssSph3T ⊗ ssSphInT) ssPairAT phi 3 αA
      = Crux33.pullFst ssSph3T ssSphInT 3 ψ := by
    rw [hαAdef]
    show Kunneth.ssetPullback (ssSph3T ⊗ ssSphInT) ssPairAT phi 3
        (Kunneth.ssetPullback ssPairAT ssSph3T (TopCat.toSSet.map pj1A) 3 ψ)
      = Crux33.pullFst ssSph3T ssSphInT 3 ψ
    rw [← ssetPullback_comp' (ssSph3T ⊗ ssSphInT) ssPairAT ssSph3T phi
      (TopCat.toSSet.map pj1A) 3 ψ, hphi1]
  have hev4 : Kunneth.ssetPullback (ssSph3T ⊗ ssSphInT) ssPairAT phi 3 βA
      = Crux33.pullSnd ssSph3T ssSphInT 3 Λ := by
    rw [hβAdef]
    show Kunneth.ssetPullback (ssSph3T ⊗ ssSphInT) ssPairAT phi 3
        (Kunneth.ssetPullback ssPairAT ssSphInT (TopCat.toSSet.map pj2A) 3 Λ)
      = Crux33.pullSnd ssSph3T ssSphInT 3 Λ
    rw [← ssetPullback_comp' (ssSph3T ⊗ ssSphInT) ssPairAT ssSphInT phi
      (TopCat.toSSet.map pj2A) 3 Λ, hphi2]
  have hαF : cochainDiff ℤ (ssSph3T ⊗ ssSphInT)
      (Crux33.pullFst ssSph3T ssSphInT 3 ψ) = 0 :=
    ssetPullback_cocycle' (ssSph3T ⊗ ssSphInT) ssSph3T
      (SemiCartesianMonoidalCategory.fst ssSph3T ssSphInT) 3 ψ hψ
  have hαS : cochainDiff ℤ (ssSph3T ⊗ ssSphInT)
      (Crux33.pullSnd ssSph3T ssSphInT 3 Λ) = 0 :=
    ssetPullback_cocycle' (ssSph3T ⊗ ssSphInT) ssSphInT
      (SemiCartesianMonoidalCategory.snd ssSph3T ssSphInT) 3 Λ hΛ
  have hev5 := cup_swap_on_cycle (ssSph3T ⊗ ssSphInT)
    (Crux33.pullFst ssSph3T ssSphInT 3 ψ) (Crux33.pullSnd ssSph3T ssSphInT 3 Λ)
    hαF hαS (Kunneth.ezChain ssSph3T ssSphInT c d) hcycle
  have hev6 : (cup ℤ (ssSph3T ⊗ ssSphInT) (Crux33.pullSnd ssSph3T ssSphInT 3 Λ)
      (Crux33.pullFst ssSph3T ssSphInT 3 ψ)) (Kunneth.ezChain ssSph3T ssSphInT c d)
      = - ψ c * Λ d :=
    Crux33.ezChainEval ssSph3T ssSphInT ψ Λ c d (fun g hg v => hΛdeg v g hg)
  have hcupval : (cup ℤ ssPairAT αA βA) w = 1 := by
    rw [hev1, hev2, hev3, hev4, hev5, hev6, hcdef, hddef, hevψ, hevΛ]
    norm_num
  -- the class `b` on `X` and its restriction to `A`
  set βX : Cochain ℤ ssPairXT 3 := (cochainPullbackHom ℤ PairXT Sph3T pj1X 3).hom ψ with hβXdef
  have hβXcoc : cochainDiff ℤ ssPairXT βX = 0 := by
    rw [hβXdef]
    exact Kunneth.pullback_cocycle PairXT Sph3T pj1X 3 ψ hψ
  set b : singularCohomology ℤ 3 PairXT := cohomologyClassOf ℤ ssPairXT βX hβXcoc with hbdef
  have hpullcoc : cochainDiff ℤ ssPairAT
      ((cochainPullbackHom ℤ (TopCat.of PairAT) PairXT inclA 3).hom βX) = 0 :=
    Kunneth.pullback_cocycle (TopCat.of PairAT) PairXT inclA 3 βX hβXcoc
  have hrestreq : ModuleCat.Hom.hom
      (HomologicalComplex.homologyMap (restr ℤ PairXT PairAT) 3)
      (cohomologyClassOf ℤ ssPairXT βX hβXcoc)
      = cohomologyClassOf ℤ ssPairAT
          ((cochainPullbackHom ℤ (TopCat.of PairAT) PairXT inclA 3).hom βX) hpullcoc :=
    Kunneth.pullback_class_eq (TopCat.of PairAT) PairXT inclA 3 βX hβXcoc hpullcoc
  have hβXαA : ((cochainPullbackHom ℤ (TopCat.of PairAT) PairXT inclA 3).hom βX) = αA := by
    rw [hβXdef, hαAdef]
    have hc := congrArg ModuleCat.Hom.hom (cochainPullbackHom_comp ℤ inclA pj1X 3)
    rw [ModuleCat.hom_comp] at hc
    have hcψ := LinearMap.congr_fun hc ψ
    simp only [LinearMap.comp_apply] at hcψ
    rw [← hcψ, ← pj1A_eq_incl_pj1X]
  have hrestr : ModuleCat.Hom.hom
      (HomologicalComplex.homologyMap (restr ℤ PairXT PairAT) 3) b
      = cohomologyClassOf ℤ ssPairAT αA hαAcoc := by
    calc ModuleCat.Hom.hom (HomologicalComplex.homologyMap (restr ℤ PairXT PairAT) 3) b
        = ModuleCat.Hom.hom (HomologicalComplex.homologyMap (restr ℤ PairXT PairAT) 3)
            (cohomologyClassOf ℤ ssPairXT βX hβXcoc) := by rw [hbdef]
      _ = cohomologyClassOf ℤ ssPairAT
            ((cochainPullbackHom ℤ (TopCat.of PairAT) PairXT inclA 3).hom βX) hpullcoc :=
            hrestreq
      _ = cohomologyClassOf ℤ ssPairAT αA hαAcoc :=
            cohomologyClassOf_congr ℤ ssPairAT hβXαA hpullcoc hαAcoc
  refine ⟨b, cohomologyClassOf ℤ ssPairAT βA hβAcoc,
    ((chainC ℤ ssPairAT).homologyπ 6).hom wcycle, ?_⟩
  rw [hrestr, cupH'_apply' ℤ ssPairAT αA βA hαAcoc hβAcoc,
    kronH_apply (R := ℤ) (X := ssPairAT) (α := cup ℤ ssPairAT αA βA)
      (hα := cochainDiff_cup_of_cocycles ℤ ssPairAT αA βA hαAcoc hβAcoc) wcycle,
    hwcycle]
  exact hcupval

/-- **The external product of the two factor classes of the sphere bundle generates `H⁶`.**

For `X = PairXT = S³ × D⁴` and `A = PairAT = S³ × S³ = ∂X`, there are classes
`b ∈ H³(X;ℤ)` (e.g. the pullback of a generator of `H³(S³)` along the projection `X → S³`) and
`β ∈ H³(A;ℤ)` (e.g. the pullback of a generator of `H³(∂D⁴) ≅ ℤ` along the second projection
`A → ∂D⁴`) such that the Alexander–Whitney product of the *restriction* of `b` to `A` with `β`
generates `H⁶(A;ℤ) ≅ ℤ`.

Route: `restr b = pj1A^*gen` and `β = pj2A^*gen` are the two factor classes of
`A = S³ × S³ ≅ Sph3T × ∂D⁴`, and `H^*(S³ × S³) = Λ[x,y]` with `x ⌣ y` generating `H⁶`;
equivalently (Kronecker plus universal coefficients) it suffices to exhibit `a ∈ H₆(A)` with
`⟨pj1A^*gen ⌣ pj2A^*gen, a⟩ = ±1`.  The Eilenberg–Zilber shuffle evaluation of
`Work.Cohomology.Crux33.sph3DiscCupEval` computes this to be `± β(σ)β'(τ)`, which is `±1` when the
cocycles are chosen with `β(σ) = β'(τ) = 1`; that is the required `a`.  (The shuffle machinery is
`Submission/Work/Cohomology/Crux33/ezShuffleDefs.lean`; the vanishing of the junk faces is
`Submission/Work/Cohomology/Crux33/witnessAux.lean`.) -/
theorem sph3Disc_restr_cup_generator :
    ∃ (b : Work.Cohomology.singularCohomology ℤ 3 Work.Cohomology.PairXT)
      (β : Work.Cohomology.singularCohomology ℤ 3 (TopCat.of Work.Cohomology.PairAT)),
      Submodule.span ℤ {(Work.Cohomology.cupH' ℤ
        (TopCat.toSSet.obj (TopCat.of Work.Cohomology.PairAT)) 3 3
        (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
          (Work.Cohomology.restr ℤ Work.Cohomology.PairXT Work.Cohomology.PairAT) 3) b) β)} = ⊤ := by
  obtain ⟨b, β, z, hz⟩ := sph3Disc_restr_cup_eval_one
  exact ⟨b, β, span_eq_top_of_kronH_eq_one _ z hz⟩

end

end Work.Cohomology
