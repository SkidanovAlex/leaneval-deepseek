import Mathlib
import Submission.Work.ThomBordism.ratDefs
import Submission.Work.ThomBordism.bdryCapBdryBijective
import Submission.Work.StemsB.SphLoopTools
import Submission.Work.ThomBordism.detectionOfSSetRat
import Submission.Work.Cohomology.kronH_natural

/-!
# `Work.ThomBordism.finrank_bdryLQ_add_bdryKQ`

The dimension count `dim L_ℚ + dim K_ℚ = b` for the middle-dimensional Lefschetz duality of the
pair `(W, ∂W)` of a `NullBordismFamily`, where

* `K_ℚ = bdryKQ W = im(H⁴(W;ℚ) → H⁴(∂W;ℚ))` and
* `L_ℚ = bdryLQ W = ker(H₄(∂W;ℚ) → H₄(W;ℚ))` and
* `b = bdryB W = dim_ℚ (H⁴(∂W;ℤ) ⊗ ℚ)`.

The proof has three parts.

1. **Duality of the two maps.**  The two maps are transposes of one another under the rational
   Kronecker pairing (`kronHNatRat`, the `ℚ`-coefficient form of `Work.Cohomology.kronH_natural`),
   and over a field the pairing is perfect in both variables (`kronHRatInjective`,
   `kronHRatSurjective`).  Hence `dim (im i^*) = dim (im i_*)`, and rank–nullity for `i_*` gives
   `dim L_ℚ + dim K_ℚ = dim H₄(∂W;ℚ)`.

2. **The coefficient change `ℤ → ℚ` for homology** (`ratHomologyIso`): the rational singular chains
   are the extension of scalars of the integral ones, so `Hₙ(X;ℚ) ≃ Hₙ(X;ℤ) ⊗ ℚ`.

3. **Poincaré duality of `∂W`** in the integral form `Work.ThomBordism.bdryCapBdryBijective` (capping
   with the boundary class is a bijection `H⁴(∂W;ℤ) → H₄(∂W;ℤ)`), base changed to `ℚ`:
   `(H⁴(∂W;ℤ) ⊗ ℚ) ≃ (H₄(∂W;ℤ) ⊗ ℚ)`.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits
open scoped TensorProduct

namespace Work.ThomBordism

noncomputable section

open Work.Cohomology

/-! ## 1. The abstract cycles of a chain complex of `ℚ`-modules

Mathlib's `K.cycles n` is a categorical kernel; its concrete model is the submodule
`ker (dₙ : Kₙ → K_{n-1})`.  The two are isomorphic (`cycIsoZRat`), and the isomorphism does not
change the underlying element (`cycIsoZRat_hom_val`). -/

/-- The index of the previous degree for the shape `ℕ` with descending differentials. -/
lemma down_next_rat (n : ℕ) : (ComplexShape.down ℕ).next n = n - 1 := by
  rcases n with _ | n
  · rw [ComplexShape.next_eq_self' _ _ (fun k hk => Nat.succ_ne_zero k hk)]
  · rw [ComplexShape.next_eq' _ (rfl : n + 1 = n + 1)]
    exact (Nat.succ_sub_one n).symm

/-- The index of the following degree for the shape `ℕ` with descending differentials. -/
lemma down_prev_rat (n : ℕ) : (ComplexShape.down ℕ).prev n = n + 1 := by
  rw [ComplexShape.prev_eq' _ (rfl : n + 1 = n + 1)]

/-- **The abstract `n`-cycles, as the concrete kernel `ker dₙ`.** -/
noncomputable def cycIsoZRat (K : ChainComplex (ModuleCat ℚ) ℕ) (n : ℕ) :
    K.cycles n ≅ ModuleCat.of ℚ ↥(LinearMap.ker ((K.d n (n - 1)).hom)) :=
  K.cyclesIsoSc' (n + 1) n (n - 1) (down_prev_rat n) (down_next_rat n) ≪≫
    ShortComplex.moduleCatCyclesIso (K.sc' (n + 1) n (n - 1))

/-- The inclusion of the cycles is the inclusion of the concrete kernel. -/
lemma cycIsoZRat_hom_i (K : ChainComplex (ModuleCat ℚ) ℕ) (n : ℕ) :
    (cycIsoZRat K n).hom ≫
        (ShortComplex.moduleCatLeftHomologyData (K.sc' (n + 1) n (n - 1))).i
      = K.iCycles n := by
  rw [cycIsoZRat, Iso.trans_hom, Category.assoc, ShortComplex.moduleCatCyclesIso_hom_i,
    HomologicalComplex.cyclesIsoSc'_hom_iCycles]

/-- `cycIsoZRat` does not change the underlying element. -/
lemma cycIsoZRat_hom_val (K : ChainComplex (ModuleCat ℚ) ℕ) (n : ℕ) (c : ↥(K.cycles n)) :
    ((cycIsoZRat K n).hom c : ↥(K.X n)) = (K.iCycles n).hom c := by
  have h := congrArg (fun (m : K.cycles n ⟶ K.X n) => ModuleCat.Hom.hom m c)
    (cycIsoZRat_hom_i K n)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  exact h

/-- The inverse of `cycIsoZRat`, evaluated on an element of the concrete kernel. -/
lemma cycIsoZRat_symm_val (K : ChainComplex (ModuleCat ℚ) ℕ) (n : ℕ)
    (z : ↥(LinearMap.ker ((K.d n (n - 1)).hom))) :
    (K.iCycles n) (((cycIsoZRat K n).toLinearEquiv).symm z) = (z : ↥(K.X n)) := by
  have h2 := cycIsoZRat_hom_val K n (((cycIsoZRat K n).toLinearEquiv).symm z)
  rw [show (cycIsoZRat K n).hom (((cycIsoZRat K n).toLinearEquiv).symm z) = z from
    ((cycIsoZRat K n).toLinearEquiv).apply_symm_apply z] at h2
  exact h2.symm

/-! ## 2. The Kronecker pairing over `ℚ` is perfect

Over a field the universal coefficient theorem holds without any finiteness hypothesis: the
comparison map `Hⁿ(X;k) → Hom_k(Hₙ(X;k),k)` is an isomorphism.  This is proved directly here for
`k = ℚ`, avoiding the `Module.Projective`/`Module.Free` hypotheses that the integral statement
`Work.Cohomology.kronH_isIso` needs. -/

/-- **The rational Kronecker pairing is surjective**: every functional on `Hₙ(X;ℚ)` is the
evaluation on some cohomology class.  A functional on the cycles which vanishes on the boundaries
extends to the chains, because every `ℚ`-module is injective. -/
theorem kronHRatSurjective (X : SSet) (n : ℕ) :
    Function.Surjective (Work.Cohomology.kronH ℚ X n) := by
  intro φ
  set Z : Submodule ℚ ((chainC ℚ X).X n) := LinearMap.ker ((chainC ℚ X).d n (n - 1)).hom with hZ
  let cycInv : ↥Z →ₗ[ℚ] ↥((chainC ℚ X).cycles n) := (cycIsoZRat (chainC ℚ X) n).toLinearEquiv.symm
  let ψ : Z →ₗ[ℚ] ℚ := (φ.comp ((chainC ℚ X).homologyπ n).hom).comp cycInv
  let α : (chainC ℚ X).X n →ₗ[ℚ] ℚ := Subspace.dualLift Z ψ
  have hαval : ∀ (x : (chainC ℚ X).X n) (hx : x ∈ Z), α x = ψ ⟨x, hx⟩ :=
    fun x hx => Subspace.dualLift_of_mem hx
  have hψval : ∀ z : Z, ψ z = φ (((chainC ℚ X).homologyπ n).hom (cycInv z)) := fun z => rfl
  have hycle : ∀ z : Z, (chainC ℚ X).iCycles n (cycInv z) = (z : (chainC ℚ X).X n) :=
    fun z => cycIsoZRat_symm_val (chainC ℚ X) n z
  have hαcyc : cochainDiff ℚ X α = 0 := by
    apply LinearMap.ext
    intro y
    change α (((chainC ℚ X).d (n + 1) n).hom y) = 0
    have hdy : ((chainC ℚ X).d (n + 1) n).hom y ∈ Z := by
      rw [hZ, LinearMap.mem_ker]
      have h := congrArg ModuleCat.Hom.hom
        (HomologicalComplex.d_comp_d (chainC ℚ X) (n + 1) n (n - 1))
      simp only [ModuleCat.hom_comp, ModuleCat.hom_zero] at h
      exact LinearMap.congr_fun h y
    have hπ0 : ((chainC ℚ X).homologyπ n).hom
        (cycInv ⟨((chainC ℚ X).d (n + 1) n).hom y, hdy⟩) = 0 :=
      homologyπ_eq_zero_of_iCycles_eq_d ℚ (chainC ℚ X) n _ y (hycle ⟨_, hdy⟩)
    rw [hαval _ hdy, hψval, hπ0, map_zero]
  refine ⟨cohomologyClassOf ℚ X α hαcyc, ?_⟩
  apply LinearMap.ext
  intro z₀
  obtain ⟨c, rfl⟩ :=
    (ModuleCat.epi_iff_surjective ((chainC ℚ X).homologyπ n)).mp inferInstance z₀
  rw [kronH_apply ℚ X α hαcyc c]
  have hci : (chainC ℚ X).iCycles n c ∈ Z := by
    rw [hZ, LinearMap.mem_ker]
    have h := congrArg (fun (m : (chainC ℚ X).cycles n ⟶ (chainC ℚ X).X (n - 1)) =>
      ModuleCat.Hom.hom m c) (HomologicalComplex.iCycles_d (chainC ℚ X) n (n - 1))
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
      LinearMap.zero_apply] using h
  show α ((chainC ℚ X).iCycles n c) = φ (((chainC ℚ X).homologyπ n).hom c)
  rw [hαval _ hci, hψval]
  congr 1
  have hinv : cycInv ⟨(chainC ℚ X).iCycles n c, hci⟩ = c := by
    apply iCycles_injective_C ℚ (chainC ℚ X) n
    rw [hycle ⟨(chainC ℚ X).iCycles n c, hci⟩]
  rw [hinv]

/-- **The rational Kronecker pairing is injective**: a cohomology class which pairs trivially with
every homology class vanishes.  A cocycle whose underlying cochain vanishes on the cycles is a
coboundary, by `LinearMap.range_dualMap_eq_dualAnnihilator_ker` together with the identification of
the abstract cycles with `ker dₙ`. -/
theorem kronHRatInjective (X : SSet) (n : ℕ) :
    Function.Injective (Work.Cohomology.kronH ℚ X n) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro u hu
  rw [LinearMap.mem_ker] at hu
  obtain ⟨w, rfl⟩ :=
    (ModuleCat.epi_iff_surjective ((cochainC ℚ X).homologyπ n)).mp inferInstance u
  have hzw : ∀ c : (chainC ℚ X).cycles n,
      cochainOfCycle ℚ X n w ((chainC ℚ X).iCycles n c) = 0 := by
    intro c
    have h : (Work.Cohomology.kronH ℚ X n) ((cochainC ℚ X).homologyπ n w)
        (((chainC ℚ X).homologyπ n) c) = 0 := by
      rw [hu]; rfl
    rw [← cohomologyClassOf_eq_homologyπ ℚ X n w,
      kronH_apply ℚ X ((cochainC ℚ X).iCycles n w) (cochainDiff_iCycles ℚ X n w) c] at h
    exact h
  have hvan : ∀ x : (chainC ℚ X).X n, ((chainC ℚ X).d n (n - 1)).hom x = 0 →
      cochainOfCycle ℚ X n w x = 0 := by
    intro x hx
    have h1 : (chainC ℚ X).iCycles n
        (((cycIsoZRat (chainC ℚ X) n).toLinearEquiv).symm ⟨x, hx⟩) = x :=
      cycIsoZRat_symm_val (chainC ℚ X) n ⟨x, hx⟩
    rw [← h1]
    exact hzw _
  obtain ⟨β, hβ⟩ := LinearMap.mem_range.mp (show cochainOfCycle ℚ X n w ∈
      LinearMap.range (((chainC ℚ X).d n (n - 1)).hom).dualMap from by
    rw [LinearMap.range_dualMap_eq_dualAnnihilator_ker, Submodule.mem_dualAnnihilator]
    intro x hx
    exact hvan x hx)
  rcases n with _ | m
  · -- degree `0`: the differential out of degree `0` of a chain complex vanishes
    have hf0 : ((chainC ℚ X).d 0 (0 - 1)).hom = 0 := by
      rw [show (0 : ℕ) - 1 = 0 from rfl]
      simpa using congrArg ModuleCat.Hom.hom
        (HomologicalComplex.shape (chainC ℚ X) 0 0 (by simp [ComplexShape.down]))
    have hco0 : cochainOfCycle ℚ X 0 w = 0 := by
      have h := hβ
      rw [hf0, LinearMap.dualMap_apply'] at h
      simpa using h.symm
    have hw0 : w = 0 := by
      apply iCycles_injective ℚ X 0
      simpa only [cochainOfCycle, map_zero] using hco0
    rw [hw0, map_zero]
  · -- degree `m+1`: `β` is a cochain whose coboundary is the underlying cochain of `w`
    have hβ' : (((chainC ℚ X).d (m + 1) m).hom).dualMap β
        = ((cochainC ℚ X).iCycles (m + 1)).hom w := hβ
    have hco : (SSetCochainComplex ℚ X).d m (m + 1) β
        = ((cochainC ℚ X).iCycles (m + 1)).hom w := by
      rw [SSetCochainComplex_d_apply]
      show cochainDiff ℚ X β = ((cochainC ℚ X).iCycles (m + 1)).hom w
      rw [show cochainDiff ℚ X β = β.comp (((chainC ℚ X).d (m + 1) m)).hom from rfl,
        ← LinearMap.dualMap_apply']
      exact hβ'
    have hz : (SSetCochainComplex ℚ X).toCycles m (m + 1) β = w := by
      apply iCycles_injective ℚ X (m + 1)
      rw [iCycles_toCycles ℚ X m (m + 1) β]
      exact hco
    rw [← hz, homologyπ_toCycles ℚ X m (m + 1) β]

/-! ## 3. Naturality of the rational Kronecker pairing -/

/-- The computation rule for the rational Kronecker pairing on classes of cycles. -/
lemma kronHCycApplyRat (X : SSet) (n : ℕ)
    (w : (cochainC ℚ X).cycles n) (v : (chainC ℚ X).cycles n) :
    kronH ℚ X n ((cochainC ℚ X).homologyπ n w) ((chainC ℚ X).homologyπ n v) =
      cochainOfCycle ℚ X n w ((chainC ℚ X).iCycles n v) := by
  rw [← cohomologyClassOf_eq_homologyπ ℚ X n w]
  exact kronH_apply ℚ X ((cochainC ℚ X).iCycles n w) (cochainDiff_iCycles ℚ X n w) v

/-- The transpose of the chain map sends the underlying cochain of a cycle to the underlying
cochain of the image cycle. -/
lemma cochainOfCycle_cyclesMapRat (X Y : TopCat) (f : X ⟶ Y) (n : ℕ)
    (w : (cochainC ℚ (TopCat.toSSet.obj Y)).cycles n) :
    cochainOfCycle ℚ (TopCat.toSSet.obj X) n
        ((HomologicalComplex.cyclesMap (dualChainMapS ℚ X Y f) n).hom w)
      = (cochainPullbackHomS ℚ X Y f n).hom
          (cochainOfCycle ℚ (TopCat.toSSet.obj Y) n w) := by
  exact congrArg (fun (g : (cochainC ℚ (TopCat.toSSet.obj Y)).cycles n ⟶
      (cochainC ℚ (TopCat.toSSet.obj X)).X n) => g.hom w)
    (HomologicalComplex.cyclesMap_i (dualChainMapS ℚ X Y f) n)

/-- The pointwise form of `cochainOfCycle_cyclesMapRat`. -/
lemma cochainOfCycle_cyclesMapRat_apply (X Y : TopCat) (f : X ⟶ Y) (n : ℕ)
    (w : (cochainC ℚ (TopCat.toSSet.obj Y)).cycles n)
    (x : (chainC ℚ (TopCat.toSSet.obj X)).X n) :
    cochainOfCycle ℚ (TopCat.toSSet.obj X) n
        ((HomologicalComplex.cyclesMap (dualChainMapS ℚ X Y f) n).hom w) x
      = cochainOfCycle ℚ (TopCat.toSSet.obj Y) n w (((chainMapS ℚ X Y f).f n).hom x) := by
  have h := LinearMap.congr_fun (cochainOfCycle_cyclesMapRat X Y f n w) x
  exact h.trans (cochainPullbackHomS_apply ℚ X Y f n
    (cochainOfCycle ℚ (TopCat.toSSet.obj Y) n w) x)

/-- **Naturality of the rational Kronecker pairing**: `⟨α, f_* c⟩ = ⟨f^* α, c⟩`. -/
theorem kronHNatRat (X Y : TopCat) (f : X ⟶ Y) (n : ℕ)
    (α : (Work.Cohomology.singularCochainComplex ℚ Y).homology n)
    (c : (Work.Cohomology.singularChains ℚ X).homology n) :
    (Work.Cohomology.kronH ℚ (TopCat.toSSet.obj Y) n) α
        ((HomologicalComplex.homologyMap (Work.Cohomology.chainMap ℚ X Y f) n).hom c)
      = (Work.Cohomology.kronH ℚ (TopCat.toSSet.obj X) n)
          ((Work.Cohomology.singularCohomologyMap ℚ X Y f n).hom α) c := by
  change kronH ℚ (TopCat.toSSet.obj Y) n α
      (HomologicalComplex.homologyMap (chainMapS ℚ X Y f) n c)
    = kronH ℚ (TopCat.toSSet.obj X) n
      (HomologicalComplex.homologyMap (dualChainMapS ℚ X Y f) n α) c
  obtain ⟨w, rfl⟩ := (ModuleCat.epi_iff_surjective
    ((cochainC ℚ (TopCat.toSSet.obj Y)).homologyπ n)).mp inferInstance α
  obtain ⟨v, rfl⟩ := (ModuleCat.epi_iff_surjective
    ((chainC ℚ (TopCat.toSSet.obj X)).homologyπ n)).mp inferInstance c
  have hA : (HomologicalComplex.homologyMap (chainMapS ℚ X Y f) n)
      ((chainC ℚ (TopCat.toSSet.obj X)).homologyπ n v)
      = (chainC ℚ (TopCat.toSSet.obj Y)).homologyπ n
          ((HomologicalComplex.cyclesMap (chainMapS ℚ X Y f) n).hom v) :=
    homologyMap_homologyπ_apply (chainMapS ℚ X Y f) n v
  have hB : (HomologicalComplex.homologyMap (dualChainMapS ℚ X Y f) n)
      ((cochainC ℚ (TopCat.toSSet.obj Y)).homologyπ n w)
      = (cochainC ℚ (TopCat.toSSet.obj X)).homologyπ n
          ((HomologicalComplex.cyclesMap (dualChainMapS ℚ X Y f) n).hom w) :=
    homologyMap_homologyπ_apply (dualChainMapS ℚ X Y f) n w
  have hcA : ((chainC ℚ (TopCat.toSSet.obj Y)).iCycles n).hom
        ((HomologicalComplex.cyclesMap (chainMapS ℚ X Y f) n).hom v)
      = ((chainMapS ℚ X Y f).f n).hom
        (((chainC ℚ (TopCat.toSSet.obj X)).iCycles n).hom v) :=
    congrArg (fun (g : (chainC ℚ (TopCat.toSSet.obj X)).cycles n ⟶
        (chainC ℚ (TopCat.toSSet.obj Y)).X n) => g.hom v)
      (HomologicalComplex.cyclesMap_i (chainMapS ℚ X Y f) n)
  rw [hA, hB]
  rw [kronHCycApplyRat (TopCat.toSSet.obj Y) n w
        ((HomologicalComplex.cyclesMap (chainMapS ℚ X Y f) n).hom v),
      kronHCycApplyRat (TopCat.toSSet.obj X) n
        ((HomologicalComplex.cyclesMap (dualChainMapS ℚ X Y f) n).hom w) v]
  rw [hcA, cochainOfCycle_cyclesMapRat_apply X Y f n w
        (((chainC ℚ (TopCat.toSSet.obj X)).iCycles n).hom v)]

/-! ## 4. The coefficient change `ℤ → ℚ` for singular homology -/

/-- **The rational singular homology is the rationalisation of the integral one**:
`Hₙ(X;ℚ) ≃ Hₙ(X;ℤ) ⊗[ℤ] ℚ`. -/
theorem ratHomologyIso (X : TopCat) (n : ℕ) :
    Nonempty ((Work.Cohomology.singularChains ℚ X).homology n ≃ₗ[ℚ]
      (TensorProduct ℤ ℚ ((Work.Cohomology.singularChains ℤ X).homology n))) := by
  haveI : PreservesFiniteLimits (ModuleCat.extendScalars (Int.castRingHom ℚ)) :=
    ModuleCat.preservesFiniteLimits_extendScalars_of_flat (by rw [RingHom.Flat]; infer_instance)
  haveI : PreservesFiniteColimits (ModuleCat.extendScalars (Int.castRingHom ℚ)) := inferInstance
  haveI : ∀ (S : Type), PreservesColimitsOfShape (Discrete S)
      (ModuleCat.extendScalars (Int.castRingHom ℚ)) := fun _ => inferInstance
  let F : ModuleCat ℤ ⥤ ModuleCat ℚ := ModuleCat.extendScalars (Int.castRingHom ℚ)
  haveI : F.PreservesHomology := inferInstance
  let K : ChainComplex (ModuleCat ℤ) ℕ := Work.Cohomology.singularChains ℤ X
  let L : ChainComplex (ModuleCat ℚ) ℕ := Work.Cohomology.singularChains ℚ X
  have hΦ : (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj K ≅ L :=
    Work.StemsB.SphRat.chainComplexBaseChange F (TopCat.toSSet.obj X) (ModuleCat.of ℤ ℤ) ≪≫
      Work.StemsB.SphRat.chainComplexCoeffIso (TopCat.toSSet.obj X)
        Work.StemsB.SphRat.extendScalarsIntRatIso
  have hΨ : L.homology n ≅ F.obj (K.homology n) :=
    (HomologicalComplex.homologyMapIso hΦ n).symm ≪≫
      (Work.StemsB.SphRat.homologyMapBaseChange F K n).some
  exact ⟨hΨ.toLinearEquiv⟩

/-! ## 5. The dimension count -/

/-- **`dim L_ℚ + dim K_ℚ = b`.** -/
theorem finrank_bdryLQ_add_bdryKQ {ι : Type} [Fintype ι] {F : ι → Work.ThomBordism.Man8}
    (W : Work.ThomBordism.NullBordismFamily ι F) :
    Module.finrank ℚ (Work.ThomBordism.bdryLQ W) + Module.finrank ℚ (Work.ThomBordism.bdryKQ W)
      = Work.ThomBordism.bdryB W := by
  -- (i) the Poincaré-duality base change `H⁴(∂W;ℤ) ⊗ ℚ ≃ H₄(∂W;ℤ) ⊗ ℚ`
  have ePD : (TensorProduct ℤ ℚ ((Work.Cohomology.singularCochainComplex ℤ
        (TopCat.of (Work.ThomBordism.bdrySet W.W))).homology 4)) ≃ₗ[ℚ]
      (TensorProduct ℤ ℚ ((Work.Cohomology.singularChains ℤ
        (TopCat.of (Work.ThomBordism.bdrySet W.W))).homology 4)) :=
    (ModuleCat.extendScalars (Int.castRingHom ℚ)).mapIso
      (LinearEquiv.toModuleIso (LinearEquiv.ofBijective
        ((LinearMap.applyₗ
            (Work.Cohomology.hPairδ (TopCat.of W.W) (Work.ThomBordism.bdrySet W.W) 8 W.w)).comp
          (Work.Cohomology.capPair ℤ
            (TopCat.toSSet.obj (TopCat.of (Work.ThomBordism.bdrySet W.W))) 4 4))
        (Work.ThomBordism.bdryCapBdryBijective W))) |>.toLinearEquiv
  -- (ii) the base change for rational homology
  obtain ⟨eH⟩ := ratHomologyIso (TopCat.of (Work.ThomBordism.bdrySet W.W)) 4
  have hfinB : FiniteDimensional ℚ
      ((Work.Cohomology.chainC ℚ
        (TopCat.toSSet.obj (TopCat.of (Work.ThomBordism.bdrySet W.W)))).homology 4) := by
    haveI : FiniteDimensional ℚ (TensorProduct ℤ ℚ ((Work.Cohomology.singularCochainComplex ℤ
        (TopCat.of (Work.ThomBordism.bdrySet W.W))).homology 4)) :=
      bdryRatCohFinite F W
    haveI : FiniteDimensional ℚ (TensorProduct ℤ ℚ ((Work.Cohomology.singularChains ℤ
        (TopCat.of (Work.ThomBordism.bdrySet W.W))).homology 4)) :=
      ePD.finiteDimensional
    exact eH.symm.finiteDimensional
  -- (iii) the coefficient change for the dimension of `H₄(∂W;ℚ)`
  have hbdy : Module.finrank ℚ
        ((Work.Cohomology.chainC ℚ
          (TopCat.toSSet.obj (TopCat.of (Work.ThomBordism.bdrySet W.W)))).homology 4)
      = Work.ThomBordism.bdryB W := by
    show Module.finrank ℚ
        ((Work.Cohomology.chainC ℚ
          (TopCat.toSSet.obj (TopCat.of (Work.ThomBordism.bdrySet W.W)))).homology 4)
      = Module.finrank ℚ (TensorProduct ℤ ℚ ((Work.Cohomology.singularCochainComplex ℤ
          (TopCat.of (Work.ThomBordism.bdrySet W.W))).homology 4))
    exact eH.finrank_eq.trans ePD.finrank_eq.symm
  -- (iv) the duality of the two maps and rank–nullity
  have hmain : Module.finrank ℚ (Work.ThomBordism.bdryLQ W)
      + Module.finrank ℚ (Work.ThomBordism.bdryKQ W)
      = Module.finrank ℚ
        ((Work.Cohomology.chainC ℚ
          (TopCat.toSSet.obj (TopCat.of (Work.ThomBordism.bdrySet W.W)))).homology 4) := by
    set S : (Work.Cohomology.cochainC ℚ
          (TopCat.toSSet.obj (TopCat.of W.W))).homology 4 →ₗ[ℚ]
        (Work.Cohomology.cochainC ℚ
          (TopCat.toSSet.obj (TopCat.of (Work.ThomBordism.bdrySet W.W)))).homology 4 :=
      (Work.Cohomology.singularCohomologyMap ℚ (TopCat.of (Work.ThomBordism.bdrySet W.W))
        (TopCat.of W.W) (bdryInc W) 4).hom with hS
    set T : (Work.Cohomology.chainC ℚ
          (TopCat.toSSet.obj (TopCat.of (Work.ThomBordism.bdrySet W.W)))).homology 4 →ₗ[ℚ]
        (Work.Cohomology.chainC ℚ
          (TopCat.toSSet.obj (TopCat.of W.W))).homology 4 :=
      pushQ W with hT
    have hKQ : Work.ThomBordism.bdryKQ W = LinearMap.range S := rfl
    have hLQ : Work.ThomBordism.bdryLQ W = LinearMap.ker T := rfl
    rw [hKQ, hLQ]
    -- naturality of the Kronecker pairing
    have hnat : ∀ (u : (Work.Cohomology.cochainC ℚ
            (TopCat.toSSet.obj (TopCat.of W.W))).homology 4)
        (z : (Work.Cohomology.chainC ℚ
            (TopCat.toSSet.obj (TopCat.of (Work.ThomBordism.bdrySet W.W)))).homology 4),
        Work.Cohomology.kronH ℚ (TopCat.toSSet.obj (TopCat.of W.W)) 4 u (T z)
          = Work.Cohomology.kronH ℚ
              (TopCat.toSSet.obj (TopCat.of (Work.ThomBordism.bdrySet W.W))) 4 (S u) z := by
      intro u z
      exact kronHNatRat (TopCat.of (Work.ThomBordism.bdrySet W.W)) (TopCat.of W.W)
        (bdryInc W) 4 u z
    have hcomp : (Work.Cohomology.kronH ℚ
            (TopCat.toSSet.obj (TopCat.of (Work.ThomBordism.bdrySet W.W))) 4).comp S
        = T.dualMap.comp (Work.Cohomology.kronH ℚ
            (TopCat.toSSet.obj (TopCat.of W.W)) 4) := by
      apply LinearMap.ext; intro u
      apply LinearMap.ext; intro z
      exact (hnat u z).symm
    have hrange : Module.finrank ℚ (LinearMap.range S) = Module.finrank ℚ (LinearMap.range T) := by
      have hUk : Function.Injective (Work.Cohomology.kronH ℚ
          (TopCat.toSSet.obj (TopCat.of (Work.ThomBordism.bdrySet W.W))) 4) :=
        kronHRatInjective _ 4
      have hNs : Function.Surjective (Work.Cohomology.kronH ℚ
          (TopCat.toSSet.obj (TopCat.of W.W)) 4) :=
        kronHRatSurjective _ 4
      have hmap : Submodule.map (Work.Cohomology.kronH ℚ
            (TopCat.toSSet.obj (TopCat.of (Work.ThomBordism.bdrySet W.W))) 4)
            (LinearMap.range S)
          = LinearMap.range T.dualMap := by
        have h1 : Submodule.map (Work.Cohomology.kronH ℚ
              (TopCat.toSSet.obj (TopCat.of (Work.ThomBordism.bdrySet W.W))) 4)
              (LinearMap.range S)
            = LinearMap.range ((Work.Cohomology.kronH ℚ
                (TopCat.toSSet.obj (TopCat.of (Work.ThomBordism.bdrySet W.W))) 4).comp S) :=
          (LinearMap.range_comp S _).symm
        have h3 : Submodule.map T.dualMap (LinearMap.range (Work.Cohomology.kronH ℚ
              (TopCat.toSSet.obj (TopCat.of W.W)) 4)) = LinearMap.range T.dualMap := by
          rw [LinearMap.range_eq_top.mpr hNs, Submodule.map_top]
        rw [h1, hcomp]
        exact (LinearMap.range_comp _ T.dualMap).trans h3
      calc Module.finrank ℚ (LinearMap.range S)
          = Module.finrank ℚ (Submodule.map (Work.Cohomology.kronH ℚ
              (TopCat.toSSet.obj (TopCat.of (Work.ThomBordism.bdrySet W.W))) 4)
              (LinearMap.range S)) :=
            (Submodule.equivMapOfInjective _ hUk (LinearMap.range S)).finrank_eq
        _ = Module.finrank ℚ (LinearMap.range T.dualMap) := by rw [hmap]
        _ = Module.finrank ℚ (LinearMap.range T) :=
            LinearMap.finrank_range_dualMap_eq_finrank_range T
    haveI := hfinB
    have hrn := LinearMap.finrank_range_add_finrank_ker T
    rw [← hrange] at hrn
    rw [add_comm, hrn]
  rw [hmain, hbdy]

end

end Work.ThomBordism
