import Mathlib
import Submission.Work.Cohomology.RelCapHTransfer
import Submission.Work.Cohomology.Duality.euclidean_convex_local_cohomology
import Submission.Work.Cohomology.Duality.ball_local_homology
import Submission.Work.Cohomology.homologyContractible
import Submission.Work.Cohomology.h0Evaluation
import Submission.Work.Cohomology.relCohomologyDual
import Submission.Work.Cohomology.Crux.relCapPair_cup_adjunction
import Submission.Work.Cohomology.relChainsProjective
import Submission.Work.Cohomology.relChainsHomeomorphCompat
import Submission.Work.Cohomology.Compat.diskPairRelCapPair_ne_zero
import Submission.Work.Cohomology.localHomology
import Submission.Work.Cohomology.uctDual_evaluation

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The base case of Poincaré–Lefschetz duality: a coordinate ball

Let `M` be a topological space with a chart `e = chartAt _ z` in dimension `N`, let `r > 0` with
`Metric.ball (e z) r ⊆ e.target` and put

* `U = e ⁻¹' Metric.ball (e z) r ∩ e.source` (an open ball),
* `K = e ⁻¹' Metric.closedBall (e z) (r/2) ∩ e.source` (a concentric closed ball),
* `A = U ∖ K` (an annulus).

The pair `(U, A)` is a "local pair": `H_k(U,A) = 0` for `k ≠ N` and `H_N(U,A) ≅ ℤ`, while `U` is
contractible, so `H_m(U) = 0` for `m ≥ 1` and `H_0(U) ≅ ℤ`.  The main theorem
`pd_coordinate_ball` states that for a generator `μ ∈ H_N(U,A;ℤ)` the relative cap product

`x ↦ x ⌢ μ : H^k(U,A;ℤ) → H_{N-k}(U;ℤ)`

is bijective for all `k`; this is the base case (C) of the proof of Poincaré–Lefschetz duality.

## Structure of the proof

* `chartBallPair_relHomology_iso` — the chart identifies `(U, U∖K)` with the flat pair
  `(𝔹, 𝔹∖K')`.
* `euclideanBallPair_relHomology_iso` — excision identifies the flat ball pair with
  `(ℝ^N, ℝ^N ∖ K')`.
* `Duality.ball_local_homology` / `Duality.free_relChains_compl` then compute `H_*(U,A)`.
* `contractibleSpace_coordinateBall` — `U` is contractible, giving `H_m(U) = 0` for `m ≥ 1`.
* `relCapPair_zero_bijective` — the top-degree case, where the cap product is compared with the
  universal coefficient evaluation (`Compat.relCapPair_kronH_eq`).
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.unusedTactic false

open CategoryTheory AlgebraicTopology Limits

namespace Work.Cohomology

noncomputable section

/-! ## The chart identifies the coordinate ball pair with the flat ball pair -/

/-- **The chart identifies the relative homology of a coordinate ball pair with the flat model.**
The chart restricts to a homeomorphism of pairs `(U, U ∖ K) ≅ (𝔹, 𝔹 ∖ K')`, where
`𝔹 = Metric.ball (e z) r` and `K' = Metric.closedBall (e z) (r/2)`. -/
theorem chartBallPair_relHomology_iso (N : ℕ) (M : TopCat) [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin N)) M] (z : M) (r : ℝ) (hr : 0 < r) :
    let e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin N)) := chartAt _ z
    Metric.ball (e z) r ⊆ e.target →
    let U : Set M := e ⁻¹' Metric.ball (e z) r ∩ e.source
    let K : Set M := e ⁻¹' Metric.closedBall (e z) (r/2) ∩ e.source
    let A : Set U := {y | (y : M) ∈ Kᶜ}
    ∀ k, Nonempty ((relChains (TopCat.of U) A).homology k ≅
      (relChains (TopCat.of ↥(Metric.ball (e z) r))
        {ζ : ↥(Metric.ball (e z) r) |
          (ζ : EuclideanSpace ℝ (Fin N)) ∉ Metric.closedBall (e z) (r/2)}).homology k) := by
  intro e hball U K A k
  have hU : U = e.source ∩ e ⁻¹' Metric.ball (e z) r := by
    show e ⁻¹' Metric.ball (e z) r ∩ e.source = e.source ∩ e ⁻¹' Metric.ball (e z) r
    rw [Set.inter_comm]
  let φ : ↥U ≃ₜ ↥(Metric.ball (e z) r) :=
    (Homeomorph.setCongr hU).trans (partialHomeomorphBallHomeo e hball)
  have hφ : ∀ y : ↥U, (φ y : EuclideanSpace ℝ (Fin N)) = e (y : M) := fun y => rfl
  refine relChainsHomeomorphCompat ↥U ↥(Metric.ball (e z) r) A _ φ ?_ k
  intro y
  have hy : (y : M) ∈ e.source := by
    have h := y.2
    simp only [U, Set.mem_inter_iff, Set.mem_preimage] at h
    exact h.2
  show (y : M) ∈ Kᶜ ↔ φ y ∈ {ζ : ↥(Metric.ball (e z) r) |
      (ζ : EuclideanSpace ℝ (Fin N)) ∉ Metric.closedBall (e z) (r/2)}
  rw [Set.mem_ofPred_eq, hφ y]
  constructor
  · intro h he
    apply h
    simp only [K, Set.mem_inter_iff, Set.mem_preimage]
    exact ⟨he, hy⟩
  · intro h hK
    apply h
    have h' := hK
    simp only [K, Set.mem_inter_iff, Set.mem_preimage] at h'
    exact h'.1

/-! ## Excision of the flat ball pair -/

/-- **Excision: the relative homology of the flat ball pair is that of its ambient space.**
For `r > 0` the pair `(𝔹, 𝔹 ∖ K')`, `𝔹 = Metric.ball y r`, `K' = Metric.closedBall y (r/2)`, has
the same relative singular homology as `(ℝ^N, ℝ^N ∖ K')`. -/
theorem euclideanBallPair_relHomology_iso (N : ℕ) (y : EuclideanSpace ℝ (Fin N)) (r : ℝ)
    (hr : 0 < r) (k : ℕ) :
    Nonempty ((relChains (TopCat.of ↥(Metric.ball y r))
        {v : ↥(Metric.ball y r) |
          (v : EuclideanSpace ℝ (Fin N)) ∉ Metric.closedBall y (r/2)}).homology k ≅
      (relChains (TopCat.of (EuclideanSpace ℝ (Fin N)))
        {v : EuclideanSpace ℝ (Fin N) | v ∉ Metric.closedBall y (r/2)}).homology k) := by
  have hsub : Metric.closedBall y (r/2) ⊆ Metric.ball y r := by
    intro v hv
    rw [Metric.mem_ball]
    have h1 : dist v y ≤ r / 2 := Metric.mem_closedBall.mp hv
    linarith
  have hcov : Metric.ball y r
      ∪ {v : EuclideanSpace ℝ (Fin N) | v ∉ Metric.closedBall y (r/2)} = Set.univ := by
    ext v
    by_cases hv : v ∈ Metric.closedBall y (r/2)
    · exact ⟨fun _ => trivial, fun _ => Or.inl (hsub hv)⟩
    · exact ⟨fun _ => trivial, fun _ => Or.inr hv⟩
  haveI hiso : IsIso (HomologicalComplex.homologyMap
      (relChainsMap (TopCat.of (EuclideanSpace ℝ (Fin N))) (Metric.ball y r)
        {v : EuclideanSpace ℝ (Fin N) | v ∉ Metric.closedBall y (r/2)}) k) :=
    excision_relChainsMap_isIso (X := TopCat.of (EuclideanSpace ℝ (Fin N)))
      (U := Metric.ball y r)
      (A := {v : EuclideanSpace ℝ (Fin N) | v ∉ Metric.closedBall y (r/2)})
      Metric.isOpen_ball Metric.isClosed_closedBall.isOpen_compl hcov k
  exact ⟨asIso (HomologicalComplex.homologyMap
    (relChainsMap (TopCat.of (EuclideanSpace ℝ (Fin N))) (Metric.ball y r)
      {v : EuclideanSpace ℝ (Fin N) | v ∉ Metric.closedBall y (r/2)}) k)⟩

/-! ## The coordinate ball is contractible -/

/-- The coordinate ball `U = e ⁻¹' Metric.ball (e z) r ∩ e.source` is contractible (the chart
identifies it with a metric ball, which is convex). -/
theorem contractibleSpace_coordinateBall (N : ℕ) (M : TopCat) [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin N)) M] (z : M) (r : ℝ) (hr : 0 < r) :
    let e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin N)) := chartAt _ z
    Metric.ball (e z) r ⊆ e.target →
    let U : Set M := e ⁻¹' Metric.ball (e z) r ∩ e.source
    ContractibleSpace ↥(TopCat.of U) := by
  intro e hball U
  have hU : U = e.source ∩ e ⁻¹' Metric.ball (e z) r := by
    show e ⁻¹' Metric.ball (e z) r ∩ e.source = e.source ∩ e ⁻¹' Metric.ball (e z) r
    rw [Set.inter_comm]
  haveI : ContractibleSpace ↥(Metric.ball (e z) r) :=
    Convex.contractibleSpace (convex_ball (e z) r) ⟨e z, by simpa using hr⟩
  exact Homeomorph.contractibleSpace
    ((Homeomorph.setCongr hU).trans (partialHomeomorphBallHomeo e hball))

/-! ## A nonvanishing functional out of a module isomorphic to `ℤ` is injective -/

/-- If `M ≅ ℤ` (as a `ℤ`-module) then every nonzero linear map `M →ₗ[ℤ] ℤ` is injective. -/
private lemma injective_of_ne_zero_of_iso_int {M : Type*} [AddCommGroup M] [Module ℤ M]
    (e : M ≃ₗ[ℤ] ℤ) (κ : M →ₗ[ℤ] ℤ) (h : κ ≠ 0) : Function.Injective κ := by
  have hsmul : ∀ z : ℤ, e.symm z = z • e.symm (1 : ℤ) := by
    intro z
    calc e.symm z = e.symm (z • (1 : ℤ)) := by rw [show z • (1 : ℤ) = z from by simp]
      _ = z • e.symm (1 : ℤ) := map_zsmul e.symm z 1
  have hformula : ∀ m : M, κ m = (e m) * (κ (e.symm 1)) := by
    intro m
    calc κ m = κ (e.symm (e m)) := by rw [e.symm_apply_apply]
      _ = κ ((e m) • e.symm (1 : ℤ)) := by rw [hsmul (e m)]
      _ = (e m) • κ (e.symm (1 : ℤ)) := map_zsmul κ (e m) (e.symm 1)
      _ = (e m) * (κ (e.symm 1)) := by rw [smul_eq_mul]
  have hc : κ (e.symm (1 : ℤ)) ≠ 0 := by
    intro h0
    apply h
    ext m
    rw [hformula m, h0, mul_zero, LinearMap.zero_apply]
  intro a b hab
  have h2 : (e a) * (κ (e.symm 1)) = (e b) * (κ (e.symm 1)) := by
    rw [← hformula a, ← hformula b, hab]
  have h3 : (e a - e b) * (κ (e.symm 1)) = 0 := by
    rw [sub_mul, h2, sub_self]
  have h4 : e a - e b = 0 := (mul_eq_zero.mp h3).resolve_right hc
  exact e.injective (sub_eq_zero.mp h4)

/-! ## The top degree: the cap product with a generator of `H_n(X,A)` -/

/-- **The cap product with a generator of the top relative homology is bijective.**

Let `X` be contractible, `A ⊆ X`, and suppose `H_n(X,A) ≅ ℤ` is generated by `ν`.  Then

`x ↦ x ⌢ ν : H^n(X,A;ℤ) → H_0(X;ℤ)`

is bijective (the other two sides vanish because `H_0(X) ≅ ℤ` and, in the applications,
`H^k(X,A) = 0` for `k ≠ n` and `H_m(X) = 0` for `m ≥ 1`).

The proof compares `x ⌢ ν` with the universal coefficient evaluation
`H^n(X,A) ≅ Hom(H_n(X,A),ℤ)` (`Work.Cohomology.uctDual_evaluation`, via
`Work.Cohomology.Compat.relCapPair_kronH_eq`): the composite of `x ↦ x ⌢ ν` with the augmentation
`κ = ⟨1, ·⟩ : H_0(X) → ℤ` is `E(x)(ν)`.  Since the augmentation is an isomorphism (`X` is path
connected) it suffices that `κ ≠ 0`, which holds because `E` is onto and `ν` generates `H_n(X,A)`
(so some functional takes the value `1` at `ν`). -/
private theorem relCapPair_zero_bijective (X : TopCat) (A : Set X) [ContractibleSpace ↥X] (n : ℕ)
    (hfree : ∀ i, Module.Free ℤ ↥((relChains X A).homology i))
    (htop : Nonempty ((relChains X A).homology n ≅ ModuleCat.of ℤ ℤ))
    (ν : (relChains X A).homology n) (hν : Submodule.span ℤ {ν} = ⊤) :
    Function.Bijective (fun x => relCapPair X A n 0 x ν) := by
  haveI : IsIso (TopCat.singularHomology₀ε X (ModuleCat.of ℤ ℤ)) := inferInstance
  obtain ⟨eU, heU⟩ := uctDual_evaluation (relChains X A) (relChainsProjective X A) hfree n
  let E : relCohomology ℤ X A n ≅ ModuleCat.of ℤ (↥((relChains X A).homology n) →ₗ[ℤ] ℤ) :=
    (HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.up ℕ) n).mapIso
      (Compat.relDualComplexIso X A) ≪≫ eU
  let κ : (singularChains ℤ X).homology 0 →ₗ[ℤ] ℤ :=
    kronH ℤ (TopCat.toSSet.obj X) 0 (oneH ℤ (TopCat.toSSet.obj X))
  have key : ∀ (u : relCohomology ℤ X A n) (z : (relChains X A).homology n),
      κ ((relCapPair X A n 0) u z) = (E.hom u) z := by
    intro u z
    have h := Compat.relCapPair_kronH_eq X A n eU heU u z
    change kronH ℤ (TopCat.toSSet.obj X) 0 (oneH ℤ (TopCat.toSSet.obj X))
      ((relCapPair X A n 0) u z) = (E.hom u) z
    rw [h]
    rfl
  have hevν : Function.Bijective (fun f : ↥((relChains X A).homology n) →ₗ[ℤ] ℤ => f ν) := by
    constructor
    · intro f g hfg
      have hmem : Submodule.span ℤ ({ν} : Set _) ≤ LinearMap.ker (f - g) := by
        rw [Submodule.span_le]
        intro y hy
        rw [Set.mem_singleton_iff] at hy
        rw [hy]
        show (f - g) ν = 0
        rw [LinearMap.sub_apply, sub_eq_zero]
        exact hfg
      rw [hν] at hmem
      have hzero : f - g = 0 := by
        rw [← LinearMap.ker_eq_top]
        exact top_le_iff.mp hmem
      exact sub_eq_zero.mp hzero
    · intro z
      obtain ⟨eN⟩ := htop
      have hspan_e : Submodule.span ℤ ({eN.hom.hom ν} : Set ℤ) = ⊤ := by
        have h1 : Submodule.span ℤ ({eN.hom.hom ν} : Set ℤ)
            = Submodule.map eN.hom.hom (Submodule.span ℤ ({ν} : Set _)) := by
          rw [Submodule.map_span, Set.image_singleton]
        rw [h1, hν, Submodule.map_top,
          LinearMap.range_eq_top.mpr ((ModuleCat.epi_iff_surjective eN.hom).mp inferInstance)]
      have hmem : (1 : ℤ) ∈ Submodule.span ℤ ({eN.hom.hom ν} : Set ℤ) := by
        rw [hspan_e]; trivial
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
      have hc1 : (eN.hom.hom ν) * c = 1 := by
        have h : c * (eN.hom.hom ν) = 1 := by simpa [smul_eq_mul] using hc
        rwa [mul_comm] at h
      obtain hgen | hgen := Int.eq_one_or_neg_one_of_mul_eq_one hc1
      · refine ⟨(z * (eN.hom.hom ν)) • (eN.hom.hom), ?_⟩
        simp only [LinearMap.smul_apply, smul_eq_mul]
        rw [hgen]; ring
      · refine ⟨(z * (eN.hom.hom ν)) • (eN.hom.hom), ?_⟩
        simp only [LinearMap.smul_apply, smul_eq_mul]
        rw [hgen]; ring
  have hκne : κ ≠ 0 := by
    obtain ⟨f0, hf0⟩ := hevν.2 1
    intro h0
    have hx := key (E.inv f0) ν
    have h1 : (E.hom (E.inv f0)) ν = 1 :=
      (congrArg (fun g => g ν) (Iso.inv_hom_id_apply E f0)).trans hf0
    rw [h1] at hx
    rw [h0] at hx
    simp only [LinearMap.zero_apply] at hx
    exact one_ne_zero hx.symm
  have hκinj : Function.Injective κ :=
    injective_of_ne_zero_of_iso_int
      (uctIsoToLinearEquiv (asIso (TopCat.singularHomology₀ε X (ModuleCat.of ℤ ℤ)))) κ hκne
  refine ⟨?_, ?_⟩
  · intro x y hxy
    have hxy' : (relCapPair X A n 0) x ν = (relCapPair X A n 0) y ν := hxy
    have h1 : (E.hom x) ν = (E.hom y) ν := by rw [← key x ν, ← key y ν, hxy']
    have h2 : E.hom x = E.hom y := hevν.1 h1
    exact (ModuleCat.mono_iff_injective E.hom).mp inferInstance h2
  · intro y
    obtain ⟨f, hf⟩ := hevν.2 (κ y)
    refine ⟨E.inv f, ?_⟩
    have hkey : κ ((relCapPair X A n 0) (E.inv f) ν) = κ y := by
      have h2 : E.hom (E.inv f) = f := Iso.inv_hom_id_apply E f
      have h3 : κ ((relCapPair X A n 0) (E.inv f) ν) = f ν :=
        (key (E.inv f) ν).trans (congrArg (fun g => g ν) h2)
      exact h3.trans hf
    exact hκinj hkey

/-! ## The base case of Poincaré–Lefschetz duality -/

theorem pd_coordinate_ball (N : ℕ) (hN : 1 ≤ N) (M : TopCat) [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin N)) M] (z : M) (r : ℝ) (hr : 0 < r) :
    let e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin N)) := chartAt _ z
    Metric.ball (e z) r ⊆ e.target →
    let U : Set M := e ⁻¹' Metric.ball (e z) r ∩ e.source
    let K : Set M := e ⁻¹' Metric.closedBall (e z) (r/2) ∩ e.source
    let A : Set U := {y | (y : M) ∈ Kᶜ}
    ∀ (μ : (Work.Cohomology.relChains (TopCat.of U) A).homology N), Submodule.span ℤ {μ} = ⊤ →
      ∀ (k m : ℕ) (hkm : k + m = N), Function.Bijective
        (fun x => (Work.Cohomology.relCapPair (TopCat.of U) A k m) x (hkm ▸ μ)) := by
  intro e hball U K A μ hμ k m hkm
  haveI hUcontr : ContractibleSpace ↥(TopCat.of U) :=
    contractibleSpace_coordinateBall N M z r hr hball
  have hK'c : IsCompact (Metric.closedBall (e z) (r / 2)) := isCompact_closedBall (e z) (r/2)
  have hK'conv : Convex ℝ (Metric.closedBall (e z) (r / 2)) := convex_closedBall (e z) (r/2)
  have hK'ne : (Metric.closedBall (e z) (r / 2)).Nonempty :=
    ⟨e z, Metric.mem_closedBall_self (by linarith)⟩
  have hmodel := Duality.ball_local_homology N hN (Metric.closedBall (e z) (r/2)) hK'c hK'conv hK'ne
  have hmodelfree :=
    Duality.free_relChains_compl N hN (Metric.closedBall (e z) (r/2)) hK'c hK'conv hK'ne
  have hiso : ∀ i, Nonempty ((relChains (TopCat.of U) A).homology i ≅
      (relChains (TopCat.of (EuclideanSpace ℝ (Fin N)))
        {v | v ∉ Metric.closedBall (e z) (r/2)}).homology i) := by
    intro i
    obtain ⟨e1⟩ := chartBallPair_relHomology_iso N M z r hr hball i
    obtain ⟨e2⟩ := euclideanBallPair_relHomology_iso N (e z) r hr i
    exact ⟨e1 ≪≫ e2⟩
  have hfree : ∀ i, Module.Free ℤ ↥((relChains (TopCat.of U) A).homology i) := by
    intro i
    obtain ⟨e1⟩ := hiso i
    haveI : Module.Free ℤ ↥((relChains (TopCat.of (EuclideanSpace ℝ (Fin N)))
        {v | v ∉ Metric.closedBall (e z) (r/2)}).homology i) := hmodelfree i
    exact Module.Free.of_equiv (σ := RingHom.id ℤ) (σ' := RingHom.id ℤ)
      (uctIsoToLinearEquiv e1).symm
  have hvan : ∀ i, i ≠ N → IsZero ((relChains (TopCat.of U) A).homology i) := by
    intro i hi
    obtain ⟨e1⟩ := hiso i
    exact IsZero.of_iso (hmodel.1 i hi) e1
  have htop : Nonempty ((relChains (TopCat.of U) A).homology N ≅ ModuleCat.of ℤ ℤ) := by
    obtain ⟨e1⟩ := hiso N
    obtain ⟨e2⟩ := hmodel.2
    exact ⟨e1 ≪≫ e2⟩
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · -- ## the top degree: `m = 0`
    -- eliminating the cast `hkm ▸ μ` first: substituting `N := k + m` and then `m := 0`
    -- turns the goal into the canonical form handled by `relCapPair_zero_bijective`
    cases hkm
    subst hm0
    exact relCapPair_zero_bijective (TopCat.of U) A k hfree htop μ hμ
  · -- ## degrees `k < N`: both sides vanish
    have hk : k ≠ N := by omega
    haveI : Subsingleton ↥(relCohomology ℤ (TopCat.of U) A k) := by
      obtain ⟨e1⟩ := relCohomologyDual (TopCat.of U) A hfree k
      haveI : Subsingleton
          ↥(ModuleCat.of ℤ (↥((relChains (TopCat.of U) A).homology k) →ₗ[ℤ] ℤ)) := by
        haveI : Subsingleton ↥((relChains (TopCat.of U) A).homology k) :=
          ModuleCat.subsingleton_of_isZero (hvan k hk)
        refine ⟨fun f g => LinearMap.ext fun m => ?_⟩
        rw [Subsingleton.elim m 0, map_zero, map_zero]
      exact ((ConcreteCategory.bijective_of_isIso e1.hom).1).subsingleton
    haveI : Subsingleton ↥((singularChains ℤ (TopCat.of U)).homology m) :=
      ModuleCat.subsingleton_of_isZero (homologyContractible m hmpos)
    exact ⟨fun a b _ => Subsingleton.elim a b, fun y => ⟨0, Subsingleton.elim _ _⟩⟩

end

end Work.Cohomology
