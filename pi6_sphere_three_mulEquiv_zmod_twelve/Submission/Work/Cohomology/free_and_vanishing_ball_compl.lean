import Mathlib
import Submission.Work.Cohomology.SingularTopFreeDefs
import Submission.Work.Cohomology.homology_vanishing_relative_compact
import Submission.Work.Cohomology.homologyMV_honest_les
import Submission.Work.Cohomology.homologyTwoCover
import Submission.Work.Cohomology.Duality.ball_local_homology
import Submission.Work.Cohomology.homologyContractible
import Submission.Work.Cohomology.homology_zero_free
import Submission.Work.Cohomology.good_empty
import Submission.Work.Cohomology.biprodFinFun
import Submission.Work.Cohomology.pd_glue_defs

set_option synthInstance.maxHeartbeats 400000

/-!
# Free and vanishing homology of the complement of a finite union of balls

The complement of a finite union of closed balls inside an open ball `B₀ ⊆ ℝ^N` has free
`(N-1)`-st homology and vanishing homology in all degrees `≥ N`.

The proof has three independent layers.

* **The flat engine.**  For a finite union `K` of compact convex sets in `ℝ^N` we prove, by
  induction on the finite family, that `H_{N-1}(ℝ^N ∖ K)` embeds into a finitely generated free
  `ℤ`-module; the induction step is the Mayer–Vietoris exact sequence of the open cover
  `{ℝ^N ∖ D, ℝ^N ∖ K'}` of `ℝ^N ∖ (D ∩ K')`.  Vanishing in degrees `≥ N` is
  `Work.Cohomology.flat_compl_union_convex_homology_vanishing`.
* **The transfer to the ball.**  `H_m(B₀ ∖ K) → H_m(ℝ^N ∖ K)` is injective: it is the first map of
  the long exact sequence of the pair `(ℝ^N ∖ K, B₀ ∖ K)`, and the relative term
  `H_m(ℝ^N ∖ K, B₀ ∖ K)` is identified with `H_m(ℝ^N, B₀) = 0` by the two-cover lemma.
* **Free/finite/torsion-free bookkeeping.**  A `ℤ`-submodule of a finitely generated free
  `ℤ`-module which is torsion-free is free of finite rank
  (`injective_into_fun_free`, `Submodule.nonempty_basis_of_pid`).

The main statement is `free_and_vanishing_ball_compl`.
-/

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.Cohomology

noncomputable section

/-! ## Homeomorphism invariance of the properties we are after -/

/-- A homeomorphism of spaces induces an isomorphism on singular homology in every degree. -/
theorem homologyIsoOfHomeomorph {X Y : TopCat} (e : X ≃ₜ Y) (n : ℕ) :
    Nonempty ((singularChains ℤ X).homology n ≅ (singularChains ℤ Y).homology n) := by
  let f : X ⟶ Y := TopCat.ofHom e
  let g : Y ⟶ X := TopCat.ofHom e.symm
  have h1 : TopCat.Homotopy (f ≫ g) (𝟙 X) := e.toHomotopyEquiv.left_inv.some
  have h2 : TopCat.Homotopy (g ≫ f) (𝟙 Y) := e.toHomotopyEquiv.right_inv.some
  haveI : IsIso (HomologicalComplex.homologyMap (chainMap ℤ X Y f) n) :=
    homologyEquiv ℤ X Y f g h1 h2 n
  exact ⟨asIso (HomologicalComplex.homologyMap (chainMap ℤ X Y f) n)⟩

/-- `Module.Free` of singular homology transports backwards along a homeomorphism. -/
theorem moduleFree_homology_of_homeomorph {X Y : TopCat} (e : X ≃ₜ Y) (n : ℕ)
    (h : Module.Free ℤ ↥((singularChains ℤ Y).homology n)) :
    Module.Free ℤ ↥((singularChains ℤ X).homology n) :=
  Module.Free.of_equiv' h (Classical.choice (homologyIsoOfHomeomorph e n)).toLinearEquiv.symm

/-- `IsZero` of singular homology transports backwards along a homeomorphism. -/
theorem isZero_homology_of_homeomorph {X Y : TopCat} (e : X ≃ₜ Y) (n : ℕ)
    (h : IsZero ((singularChains ℤ Y).homology n)) :
    IsZero ((singularChains ℤ X).homology n) :=
  isZero_homology_of_homotopyEquiv e.toHomotopyEquiv n h

/-- The same for `TopCat.of` of two equal sets. -/
theorem homologyIsoOfSetEq {α : Type} [TopologicalSpace α] {A B : Set α} (h : A = B) (n : ℕ) :
    Nonempty ((singularChains ℤ (TopCat.of A)).homology n ≅
      (singularChains ℤ (TopCat.of B)).homology n) :=
  homologyIsoOfHomeomorph (Homeomorph.setCongr h) n

/-! ## Submodules of finitely generated free `ℤ`-modules

A `ℤ`-linear injection into `Fin n → ℤ` exhibits its source as a subgroup of a finitely generated
free abelian group, hence as a free `ℤ`-module of finite rank. -/

/-- **A `ℤ`-module injecting into the free module `ι → ℤ` of finite rank is free of finite
rank.** -/
theorem injective_into_fun_free {ι : Type*} [Finite ι] {M : Type} [AddCommGroup M]
    [Module ℤ M] (φ : M →ₗ[ℤ] (ι → ℤ)) (hφ : Function.Injective φ) :
    (∃ r : ℕ, Nonempty (M ≃ₗ[ℤ] (Fin r → ℤ))) ∧ Module.Free ℤ M ∧ Module.Finite ℤ M := by
  classical
  obtain ⟨r, ⟨b⟩⟩ :=
    Submodule.nonempty_basis_of_pid (Pi.basisFun ℤ ι) (LinearMap.range φ)
  have e1 : M ≃ₗ[ℤ] ↥(LinearMap.range φ) := LinearEquiv.ofInjective φ hφ
  have e2 : ↥(LinearMap.range φ) ≃ₗ[ℤ] (Fin r → ℤ) :=
    b.repr.trans (Finsupp.linearEquivFunOnFinite ℤ ℤ (Fin r))
  refine ⟨⟨r, ⟨e1.trans e2⟩⟩, Module.Free.of_equiv' (Module.Free.of_basis b) e1.symm, ?_⟩
  exact Module.Finite.equiv (e2.symm.trans e1.symm)

/-! ## Vanishing of the relative homology of the pair `(ℝ^N, B₀)`

For the open ball `B₀ = Metric.ball c₀ R` with `R > 0` we have `H_m(ℝ^N, B₀) = 0` for `m ≥ 1`.
The case `m ≥ 2` follows from the long exact sequence of the pair, both ends being contractible;
the case `m = 1` needs additionally that `H₀(B₀) → H₀(ℝ^N)` is an isomorphism. -/

/-- **`H₀(B₀) → H₀(ℝ^N)` is an isomorphism** for an open ball `B₀`. -/
theorem isIso_h0_inclChains_ball {N : ℕ} (c₀ : EuclideanSpace ℝ (Fin N)) (R : ℝ) (hR : 0 < R) :
    IsIso (HomologicalComplex.homologyMap
      (inclChains (TopCat.of (EuclideanSpace ℝ (Fin N))) (Metric.ball c₀ R)) 0) := by
  haveI hcontr : ContractibleSpace ↥(Metric.ball c₀ R) :=
    (convex_ball c₀ R).contractibleSpace ⟨c₀, Metric.mem_ball_self hR⟩
  haveI hεX : IsIso (TopCat.singularHomology₀ε
      (TopCat.of (EuclideanSpace ℝ (Fin N))) (ModuleCat.of ℤ ℤ)) := inferInstance
  haveI hεA : IsIso (TopCat.singularHomology₀ε
      (TopCat.of ↥(Metric.ball c₀ R)) (ModuleCat.of ℤ ℤ)) := inferInstance
  have hnat := epsilonNaturality (TopCat.of ↥(Metric.ball c₀ R))
    (TopCat.of (EuclideanSpace ℝ (Fin N)))
    (subtypeIncl (TopCat.of (EuclideanSpace ℝ (Fin N))) (Metric.ball c₀ R))
  have hα : HomologicalComplex.homologyMap
        (inclChains (TopCat.of (EuclideanSpace ℝ (Fin N))) (Metric.ball c₀ R)) 0
      = TopCat.singularHomology₀ε (TopCat.of ↥(Metric.ball c₀ R)) (ModuleCat.of ℤ ℤ)
        ≫ inv (TopCat.singularHomology₀ε
          (TopCat.of (EuclideanSpace ℝ (Fin N))) (ModuleCat.of ℤ ℤ)) := by
    rw [← hnat, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  rw [hα]
  infer_instance

/-- **`H_m(ℝ^N, B₀) = 0` for `m ≥ 1`**, with `B₀ = Metric.ball c₀ R` an open ball. -/
theorem isZero_relChains_ball {N : ℕ} (c₀ : EuclideanSpace ℝ (Fin N)) (R : ℝ) (hR : 0 < R)
    {m : ℕ} (hm : 1 ≤ m) :
    IsZero ((relChains (TopCat.of (EuclideanSpace ℝ (Fin N))) (Metric.ball c₀ R)).homology m) := by
  rcases eq_or_lt_of_le hm with h1 | h2
  · -- `m = 1`: the connecting map `H₁(ℝ^N,B₀) → H₀(B₀)` is both mono and zero.
    subst h1
    haveI hcontr : ContractibleSpace ↥(Metric.ball c₀ R) :=
      (convex_ball c₀ R).contractibleSpace ⟨c₀, Metric.mem_ball_self hR⟩
    have hX1 : IsZero ((singularChains ℤ
        (TopCat.of (EuclideanSpace ℝ (Fin N)))).homology 1) :=
      homologyContractible 1 (by norm_num)
    haveI hδmono : Mono (hPairδ (TopCat.of (EuclideanSpace ℝ (Fin N))) (Metric.ball c₀ R) 0) := by
      have hf : HomologicalComplex.homologyMap
          (cokernel.π (inclChains (TopCat.of (EuclideanSpace ℝ (Fin N)))
            (Metric.ball c₀ R))) 1 = 0 := hX1.eq_of_src _ 0
      exact (ShortComplex.exact_iff_mono _ hf).mp
        (hPair_exact₃ (TopCat.of (EuclideanSpace ℝ (Fin N))) (Metric.ball c₀ R) 0)
    have hδ0 : hPairδ (TopCat.of (EuclideanSpace ℝ (Fin N))) (Metric.ball c₀ R) 0 = 0 := by
      haveI : IsIso (HomologicalComplex.homologyMap
          (inclChains (TopCat.of (EuclideanSpace ℝ (Fin N))) (Metric.ball c₀ R)) 0) :=
        isIso_h0_inclChains_ball c₀ R hR
      have hEx := hPair_exact₁ (TopCat.of (EuclideanSpace ℝ (Fin N))) (Metric.ball c₀ R) 0
      rw [ShortComplex.moduleCat_exact_iff_range_eq_ker] at hEx
      have hker : (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
          (inclChains (TopCat.of (EuclideanSpace ℝ (Fin N))) (Metric.ball c₀ R)) 0)).ker = ⊥ := by
        rw [LinearMap.ker_eq_bot]
        exact (ModuleCat.mono_iff_injective _).mp inferInstance
      rw [hker] at hEx
      exact ModuleCat.hom_ext (LinearMap.range_eq_bot.mp hEx)
    refine IsZero.iff_id_eq_zero _ |>.mpr ?_
    have h : (𝟙 _) ≫ hPairδ (TopCat.of (EuclideanSpace ℝ (Fin N))) (Metric.ball c₀ R) 0
        = 0 ≫ hPairδ (TopCat.of (EuclideanSpace ℝ (Fin N))) (Metric.ball c₀ R) 0 := by
      rw [Category.id_comp, hδ0, zero_comp]
    exact (cancel_mono (hPairδ (TopCat.of (EuclideanSpace ℝ (Fin N))) (Metric.ball c₀ R) 0)).mp h
  · -- `m ≥ 2`: the connecting map is an isomorphism onto `H_{m-1}(B₀) = 0`.
    haveI hcontr : ContractibleSpace ↥(Metric.ball c₀ R) :=
      (convex_ball c₀ R).contractibleSpace ⟨c₀, Metric.mem_ball_self hR⟩
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
    haveI hiso : IsIso (hPairδ (TopCat.of (EuclideanSpace ℝ (Fin N))) (Metric.ball c₀ R) (k + 1)) :=
      hPairδ_isIso (TopCat.of (EuclideanSpace ℝ (Fin N))) (Metric.ball c₀ R) (k + 1)
        (homologyContractible (k + 2) (by omega)) (homologyContractible (k + 1) (by omega))
    exact IsZero.of_iso (homologyContractible (k + 1) (by omega))
      (asIso (hPairδ (TopCat.of (EuclideanSpace ℝ (Fin N))) (Metric.ball c₀ R) (k + 1)))


/-! ## Injectivity from a biproduct into a finitely generated free module -/

/-- **Two injections of the components of a biproduct combine into one injection.** -/
theorem biprod_injective_into_fun (A B : ModuleCat ℤ) {n₁ n₂ : ℕ}
    (φA : ↥A →ₗ[ℤ] (Fin n₁ → ℤ)) (hA : Function.Injective φA)
    (φB : ↥B →ₗ[ℤ] (Fin n₂ → ℤ)) (hB : Function.Injective φB) :
    ∃ ψ : ↥(biprod A B) →ₗ[ℤ] ((Fin n₁ ⊕ Fin n₂) → ℤ), Function.Injective ψ := by
  classical
  let πA : ↥(biprod A B) →ₗ[ℤ] ↥A := ModuleCat.Hom.hom (biprod.fst : A ⊞ B ⟶ A)
  let πB : ↥(biprod A B) →ₗ[ℤ] ↥B := ModuleCat.Hom.hom (biprod.snd : A ⊞ B ⟶ B)
  refine ⟨LinearMap.pi (fun i : Fin n₁ ⊕ Fin n₂ =>
    match i with
    | Sum.inl a => (LinearMap.proj a).comp (φA.comp πA)
    | Sum.inr b => (LinearMap.proj b).comp (φB.comp πB)), ?_⟩
  intro x y hxy
  have h1 : πA x = πA y := by
    apply hA
    funext a
    have h := congrFun hxy (Sum.inl a)
    simpa [LinearMap.pi_apply, πA, LinearMap.comp_apply] using h
  have h2 : πB x = πB y := by
    apply hB
    funext b
    have h := congrFun hxy (Sum.inr b)
    simpa [LinearMap.pi_apply, πB, LinearMap.comp_apply] using h
  exact biprod_ext_apply (M := A) (N := B) h1 h2

/-! ## The base case: the complement of a single compact convex set -/

/-- **The complement of a compact convex set in `ℝ^N` (`N ≥ 2`) has free `(N-1)`-st homology of
finite rank**: `H_{N-1}(ℝ^N ∖ D) ≅ ℤ` for `D` nonempty. -/
theorem exists_inj_fin_compl_single_convex {N : ℕ} (hN : 2 ≤ N)
    (D : Set (EuclideanSpace ℝ (Fin N))) (hDc : IsCompact D) (hDv : Convex ℝ D) :
    ∃ n : ℕ, ∃ φ : ↥((singularChains ℤ
      (TopCat.of {x : EuclideanSpace ℝ (Fin N) | x ∉ D})).homology (N - 1)) →ₗ[ℤ]
        (Fin n → ℤ), Function.Injective φ := by
  classical
  by_cases hne : D.Nonempty
  · obtain ⟨e⟩ := Duality.complHomologyTop N hN D hDc hDv hne
    exact ⟨1, (e.toLinearEquiv.trans (LinearEquiv.funUnique (Fin 1) ℤ ℤ).symm).toLinearMap,
      (e.toLinearEquiv.trans (LinearEquiv.funUnique (Fin 1) ℤ ℤ).symm).injective⟩
  · rw [Set.not_nonempty_iff_eq_empty.mp hne]
    refine ⟨0, 0, fun x y _ => ?_⟩
    have hset : {x : EuclideanSpace ℝ (Fin N) | x ∉ (∅ : Set (EuclideanSpace ℝ (Fin N)))}
        = Set.univ := by ext x; simp
    haveI : ContractibleSpace ↥(Set.univ : Set (EuclideanSpace ℝ (Fin N))) :=
      convex_univ.contractibleSpace ⟨0, trivial⟩
    have hz : IsZero ((singularChains ℤ (TopCat.of {x : EuclideanSpace ℝ (Fin N) |
        x ∉ (∅ : Set (EuclideanSpace ℝ (Fin N)))})).homology (N - 1)) :=
      isZero_homology_of_homeomorph
        (X := TopCat.of {x : EuclideanSpace ℝ (Fin N) | x ∉ (∅ : Set (EuclideanSpace ℝ (Fin N)))}) 
        (Y := TopCat.of ↥(Set.univ : Set (EuclideanSpace ℝ (Fin N))))
        (Homeomorph.setCongr hset) (N - 1)
        (homologyContractible (N - 1) (by omega))
    haveI := ModuleCat.subsingleton_of_isZero hz
    exact Subsingleton.elim _ _

/-! ## Elementary transports -/

/-- If `P` implies `q`, the nested subtype `{z : {x // q x} // P z.1}` is canonically homeomorphic
to `{x // P x}`. -/
def homeomorphNestedSubset {α : Type*} [TopologicalSpace α] {q P : α → Prop}
    (h : ∀ x, P x → q x) : {z : {x // q x} // P z.1} ≃ₜ {x : α // P x} :=
  (flatHomeo (q := q) (P := P)).trans (Homeomorph.setCongr (by
    ext x
    constructor
    · rintro ⟨-, h2⟩; exact h2
    · intro h2; exact ⟨h x h2, h2⟩))

/-- An injection of the homology of `Y` transports to a space homotopy equivalent to `Y`. -/
theorem exists_injective_of_homotopyEquiv {X Y : TopCat} (e : ContinuousMap.HomotopyEquiv X Y)
    {n r : ℕ} (φ : ↥((singularChains ℤ Y).homology n) →ₗ[ℤ] (Fin r → ℤ))
    (hφ : Function.Injective φ) :
    ∃ ψ : ↥((singularChains ℤ X).homology n) →ₗ[ℤ] (Fin r → ℤ), Function.Injective ψ := by
  let f : X ⟶ Y := TopCat.ofHom e.toFun
  let g : Y ⟶ X := TopCat.ofHom e.invFun
  have h1 : TopCat.Homotopy (f ≫ g) (𝟙 X) := e.left_inv.some
  have h2 : TopCat.Homotopy (g ≫ f) (𝟙 Y) := e.right_inv.some
  haveI : IsIso (HomologicalComplex.homologyMap (chainMap ℤ X Y f) n) :=
    homologyEquiv ℤ X Y f g h1 h2 n
  exact ⟨φ.comp (asIso (HomologicalComplex.homologyMap (chainMap ℤ X Y f) n)).toLinearEquiv.toLinearMap,
    hφ.comp (asIso (HomologicalComplex.homologyMap (chainMap ℤ X Y f) n)).toLinearEquiv.injective⟩

/-! ## The flat engine -/

/-- **The flat engine.**  For a finite union `K` of compact convex sets in `ℝ^N` (`N ≥ 2`),
the top homology `H_{N-1}(ℝ^N ∖ K)` injects into a finitely generated free `ℤ`-module.

The induction is over the finite family: the induction step is the Mayer–Vietoris sequence of the
open cover `{ℝ^N ∖ D, ℝ^N ∖ K'}` of `ℝ^N ∖ (D ∩ K')`, whose middle term is a biproduct of the
homologies of the two pieces; the connecting map into `H_{N-1}` vanishes because the relative term
`H_N(ℝ^N ∖ (D ∩ K'))` does (`flat_compl_union_convex_homology_vanishing`). -/
theorem exists_inj_fin_compl_union_convex {N : ℕ} (hN : 2 ≤ N) {ι : Type}
    (s : Finset ι) (D : ι → Set (EuclideanSpace ℝ (Fin N)))
    (hDc : ∀ i ∈ s, IsCompact (D i)) (hDv : ∀ i ∈ s, Convex ℝ (D i)) :
    ∃ n : ℕ, ∃ φ : ↥((singularChains ℤ (TopCat.of {x : EuclideanSpace ℝ (Fin N) |
        x ∉ ⋃ i ∈ s, D i})).homology (N - 1)) →ₗ[ℤ] (Fin n → ℤ), Function.Injective φ := by
  classical
  revert D hDc hDv
  refine Finset.induction_on s ?_ ?_
  · intro D hDc hDv
    have hset : {x : EuclideanSpace ℝ (Fin N) | x ∉ ⋃ i ∈ (∅ : Finset ι), D i} = Set.univ := by
      ext x; simp
    refine ⟨0, 0, fun x y _ => ?_⟩
    haveI : ContractibleSpace ↥(Set.univ : Set (EuclideanSpace ℝ (Fin N))) :=
      convex_univ.contractibleSpace ⟨0, trivial⟩
    have hz := isZero_homology_of_homeomorph
      (X := TopCat.of {x : EuclideanSpace ℝ (Fin N) | x ∉ ⋃ i ∈ (∅ : Finset ι), D i})
      (Y := TopCat.of ↥(Set.univ : Set (EuclideanSpace ℝ (Fin N))))
      (Homeomorph.setCongr hset) (N - 1) (homologyContractible (N - 1) (by omega))
    haveI := ModuleCat.subsingleton_of_isZero hz
    exact Subsingleton.elim _ _
  · intro a s has ih D hDc hDv
    obtain ⟨n₁, φ₁, hφ₁⟩ := ih D (fun i hi => hDc i (Finset.mem_insert_of_mem hi))
      (fun i hi => hDv i (Finset.mem_insert_of_mem hi))
    obtain ⟨n₂, φ₂, hφ₂⟩ := exists_inj_fin_compl_single_convex hN (D a)
      (hDc a (Finset.mem_insert_self a s)) (hDv a (Finset.mem_insert_self a s))
    -- The ambient space of the Mayer–Vietoris sequence and its two open pieces.
    let W : TopCat := TopCat.of {x : EuclideanSpace ℝ (Fin N) | x ∉ (D a ∩ ⋃ i ∈ s, D i)}
    let U : Set W := {y : W | (y : EuclideanSpace ℝ (Fin N)) ∉ D a}
    let V : Set W := {y : W | (y : EuclideanSpace ℝ (Fin N)) ∉ ⋃ i ∈ s, D i}
    have hDacl : IsClosed (D a) := (hDc a (Finset.mem_insert_self a s)).isClosed
    have hKscl : IsClosed (⋃ i ∈ s, D i) :=
      Set.Finite.isClosed_biUnion s.finite_toSet
        (fun i hi => (hDc i (Finset.mem_insert_of_mem hi)).isClosed)
    have hU : IsOpen U := hDacl.isOpen_compl.preimage continuous_subtype_val
    have hV : IsOpen V := hKscl.isOpen_compl.preimage continuous_subtype_val
    have hcov : U ∪ V = Set.univ := by
      ext y
      simp only [Set.mem_union, Set.mem_univ, iff_true]
      by_cases h : (y : EuclideanSpace ℝ (Fin N)) ∈ D a
      · exact Or.inr fun hc => (y.2 ⟨h, hc⟩)
      · exact Or.inl h
    -- Vanishing of `H_N` of the ambient space, transported from the flat statement.
    have hvan_sub : Subsingleton ((singularChains ℤ (TopCat.of {x : EuclideanSpace ℝ (Fin N) |
        x ∉ ⋃ i ∈ s, (D i ∩ D a)})).homology N) :=
      flat_compl_union_convex_homology_vanishing (by omega : 1 ≤ N) s (fun i => D i ∩ D a)
        (fun i hi => (hDc i (Finset.mem_insert_of_mem hi)).inter
          (hDc a (Finset.mem_insert_self a s)))
        (fun i hi => (hDv i (Finset.mem_insert_of_mem hi)).inter
          (hDv a (Finset.mem_insert_self a s))) N le_rfl
    have hsetW : {x : EuclideanSpace ℝ (Fin N) | x ∉ (D a ∩ ⋃ i ∈ s, D i)}
        = {x : EuclideanSpace ℝ (Fin N) | x ∉ ⋃ i ∈ s, (D i ∩ D a)} := by
      have hunion : D a ∩ ⋃ i ∈ s, D i = ⋃ i ∈ s, (D i ∩ D a) := by
        rw [Set.inter_iUnion₂]
        exact Set.iUnion₂_congr fun i _ => Set.inter_comm _ _
      rw [hunion]
    haveI hvanN : IsZero (pdHom W N) := by
      have hz : IsZero ((singularChains ℤ (TopCat.of {x : EuclideanSpace ℝ (Fin N) |
          x ∉ ⋃ i ∈ s, (D i ∩ D a)})).homology N) :=
        ModuleCat.isZero_iff_subsingleton.mpr hvan_sub
      exact isZero_homology_of_homeomorph (X := W)
        (Y := TopCat.of {x : EuclideanSpace ℝ (Fin N) | x ∉ ⋃ i ∈ s, (D i ∩ D a)})
        (Homeomorph.setCongr hsetW) N hz
    -- The Mayer–Vietoris injection.
    have hF : Function.Injective (ModuleCat.Hom.hom (homMVF W U V (N - 1))) := by
      have hvanZ : IsZero (pdHom W ((N - 1) + 1)) := by
        rw [Nat.sub_add_cancel (by omega : 1 ≤ N)]
        exact hvanN
      have hδ0 : homMVδ W U V hU hV hcov (N - 1) = 0 := IsZero.eq_zero_of_src hvanZ _
      have hker : (ModuleCat.Hom.hom (homMVF W U V (N - 1))).ker = ⊥ := by
        have hex := ShortComplex.Exact.moduleCat_range_eq_ker
          (homMV_exact₁ W U V hU hV hcov (N - 1))
        have hrange : (ModuleCat.Hom.hom (homMVδ W U V hU hV hcov (N - 1))).range = ⊥ := by
          rw [hδ0]
          exact LinearMap.range_zero
        rw [← hex]
        exact hrange
      exact LinearMap.ker_eq_bot.mp hker
    -- Injections for the two pieces, transported along the canonical homeomorphisms.
    obtain ⟨ψU, hψU⟩ := exists_injective_of_homotopyEquiv
      (X := TopCat.of ↥U) (Y := TopCat.of {x : EuclideanSpace ℝ (Fin N) | x ∉ D a})
      (homeomorphNestedSubset (q := fun x : EuclideanSpace ℝ (Fin N) => x ∉ (D a ∩ ⋃ i ∈ s, D i))
        (P := fun x : EuclideanSpace ℝ (Fin N) => x ∉ D a)
        (fun x hx hc => hx hc.1)).toHomotopyEquiv φ₂ hφ₂
    obtain ⟨ψV, hψV⟩ := exists_injective_of_homotopyEquiv
      (X := TopCat.of ↥V)
      (Y := TopCat.of {x : EuclideanSpace ℝ (Fin N) | x ∉ ⋃ i ∈ s, D i})
      (homeomorphNestedSubset (q := fun x : EuclideanSpace ℝ (Fin N) => x ∉ (D a ∩ ⋃ i ∈ s, D i))
        (P := fun x : EuclideanSpace ℝ (Fin N) => x ∉ ⋃ i ∈ s, D i)
        (fun x hx hc => hx hc.2)).toHomotopyEquiv φ₁ hφ₁
    obtain ⟨ψ, hψ⟩ := biprod_injective_into_fun (pdHomSub W U (N - 1)) (pdHomSub W V (N - 1))
      ψU hψU ψV hψV
    -- The new space `ℝ^N ∖ (⋃ i ∈ insert a s, D i)` is homeomorphic to `U ∩ V`.
    have hsetE : {x : EuclideanSpace ℝ (Fin N) | x ∉ D a ∧ x ∉ ⋃ i ∈ s, D i}
        = {x : EuclideanSpace ℝ (Fin N) | x ∉ ((⋃ i ∈ s, D i) ∪ D a)} := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_union]
      tauto
    have he : (↥(U ∩ V)) ≃ₜ
        (↥{x : EuclideanSpace ℝ (Fin N) | x ∉ ⋃ i ∈ insert a s, D i}) := by
      refine (homeomorphNestedSubset (q := fun x : EuclideanSpace ℝ (Fin N) =>
        x ∉ (D a ∩ ⋃ i ∈ s, D i))
        (P := fun x : EuclideanSpace ℝ (Fin N) => x ∉ D a ∧ x ∉ ⋃ i ∈ s, D i)
        (fun x hx hc => hx.1 hc.1)).trans ?_
      rw [iUnion_insert_finset a s D]
      exact Homeomorph.setCongr hsetE
    obtain ⟨eX⟩ := homologyIsoOfHomeomorph (X := TopCat.of ↥(U ∩ V))
      (Y := TopCat.of {x : EuclideanSpace ℝ (Fin N) | x ∉ ⋃ i ∈ insert a s, D i}) he (N - 1)
    refine ⟨n₂ + n₁, ?_, ?_⟩
    · exact ((LinearEquiv.funCongrLeft ℤ ℤ (finSumFinEquiv (m := n₂) (n := n₁))).symm.toLinearMap).comp
        ((ψ.comp (ModuleCat.Hom.hom (homMVF W U V (N - 1)))).comp eX.toLinearEquiv.symm.toLinearMap)
    · exact ((LinearEquiv.funCongrLeft ℤ ℤ (finSumFinEquiv (m := n₂) (n := n₁))).symm.injective).comp
        (hψ.comp (hF.comp eX.toLinearEquiv.symm.injective))

/-! ## The transfer from the flat complement to the ball -/

/-- **The inclusion `B₀ ∖ K ⊆ ℝ^N ∖ K` is injective on homology in positive degrees**, for
`B₀ = Metric.ball c₀ R` an open ball and `K ⊆ B₀` closed.

Indeed, the long exact sequence of the pair `(ℝ^N ∖ K, B₀ ∖ K)` expresses the kernel of the
inclusion as the image of the connecting map `H_{m+1}(ℝ^N ∖ K, B₀ ∖ K) → H_m(B₀ ∖ K)`, and the
two-cover lemma identifies `H_{m+1}(ℝ^N ∖ K, B₀ ∖ K) ≅ H_{m+1}(ℝ^N, B₀) = 0`. -/
theorem pdHomIncl_injective_ball {N : ℕ} (c₀ : EuclideanSpace ℝ (Fin N)) (R : ℝ) (hR : 0 < R)
    (K : Set (EuclideanSpace ℝ (Fin N))) (hKcl : IsClosed K) (hK : K ⊆ Metric.ball c₀ R)
    {m : ℕ} (hm : 1 ≤ m) :
    Function.Injective (ModuleCat.Hom.hom (pdHomIncl
      (TopCat.of {y : EuclideanSpace ℝ (Fin N) | y ∉ K})
      {y : {y : EuclideanSpace ℝ (Fin N) | y ∉ K} |
        (y : EuclideanSpace ℝ (Fin N)) ∈ Metric.ball c₀ R} m)) := by
  classical
  have hballopen : IsOpen {y : EuclideanSpace ℝ (Fin N) | y ∉ K} := hKcl.isOpen_compl
  have hcov : {y : EuclideanSpace ℝ (Fin N) | y ∉ K} ∪ Metric.ball c₀ R = Set.univ := by
    ext y
    constructor
    · intro _; trivial
    · intro _
      by_cases h : y ∈ K
      · exact Or.inr (hK h)
      · exact Or.inl h
  obtain ⟨e⟩ := homologyTwoCover (TopCat.of (EuclideanSpace ℝ (Fin N)))
    {y : EuclideanSpace ℝ (Fin N) | y ∉ K} (Metric.ball c₀ R) hballopen Metric.isOpen_ball
    hcov (m + 1)
  haveI hz1 : IsZero ((relChains (TopCat.of (EuclideanSpace ℝ (Fin N)))
      (Metric.ball c₀ R)).homology (m + 1)) := isZero_relChains_ball c₀ R hR (by omega)
  haveI hz2 : IsZero ((relChains (TopCat.of {y : EuclideanSpace ℝ (Fin N) | y ∉ K})
      {y : {y : EuclideanSpace ℝ (Fin N) | y ∉ K} |
        (y : EuclideanSpace ℝ (Fin N)) ∈ Metric.ball c₀ R}).homology (m + 1)) :=
    IsZero.of_iso hz1 e.symm
  have hker : (ModuleCat.Hom.hom (pdHomIncl
      (TopCat.of {y : EuclideanSpace ℝ (Fin N) | y ∉ K})
      {y : {y : EuclideanSpace ℝ (Fin N) | y ∉ K} |
        (y : EuclideanSpace ℝ (Fin N)) ∈ Metric.ball c₀ R} m)).ker = ⊥ := by
    change (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
      (inclChains (TopCat.of {y : EuclideanSpace ℝ (Fin N) | y ∉ K})
        {y : {y : EuclideanSpace ℝ (Fin N) | y ∉ K} |
          (y : EuclideanSpace ℝ (Fin N)) ∈ Metric.ball c₀ R}) m)).ker = ⊥
    have hex := ShortComplex.Exact.moduleCat_range_eq_ker
      (hPair_exact₁ (TopCat.of {y : EuclideanSpace ℝ (Fin N) | y ∉ K})
        {y : {y : EuclideanSpace ℝ (Fin N) | y ∉ K} |
          (y : EuclideanSpace ℝ (Fin N)) ∈ Metric.ball c₀ R} m)
    have hrange : (ModuleCat.Hom.hom (hPairδ (TopCat.of {y : EuclideanSpace ℝ (Fin N) | y ∉ K})
        {y : {y : EuclideanSpace ℝ (Fin N) | y ∉ K} |
          (y : EuclideanSpace ℝ (Fin N)) ∈ Metric.ball c₀ R} m)).range = ⊥ := by
      rw [IsZero.eq_zero_of_src hz2 (hPairδ (TopCat.of {y : EuclideanSpace ℝ (Fin N) | y ∉ K})
        {y : {y : EuclideanSpace ℝ (Fin N) | y ∉ K} |
          (y : EuclideanSpace ℝ (Fin N)) ∈ Metric.ball c₀ R} m)]
      exact LinearMap.range_zero
    rw [← hex]
    exact hrange
  exact LinearMap.ker_eq_bot.mp hker

/-! ## The main statement -/

/-- For `N ≥ 1`, an open ball `B₀ ⊆ ℝ^N` and finitely many closed balls `B j ⊆ B₀`, the
complement of `⋃ j, B j` in `B₀` has free `(N-1)`-st homology and vanishing homology in all
degrees `m ≥ N`.  Both assertions are needed simultaneously in the induction on the number of
balls: for a single added ball `B`, the relative homology of the pair `(X_k, X_{k+1})` is the local
homology of `B`, which is `0` in degrees below `N` and `ℤ` in degree `N`. -/
theorem free_and_vanishing_ball_compl {N : ℕ} (hN : 1 ≤ N)
    (c₀ : EuclideanSpace ℝ (Fin N)) (R : ℝ) (hR : 0 < R) {k : ℕ}
    (c : Fin k → EuclideanSpace ℝ (Fin N)) (r : Fin k → ℝ) (hr : ∀ j, 0 < r j)
    (hsub : ∀ j, Metric.closedBall (c j) (r j) ⊆ Metric.ball c₀ R) :
    Module.Free ℤ ↥((Work.Cohomology.singularChains ℤ (TopCat.of {x : EuclideanSpace ℝ (Fin N) |
        x ∈ Metric.ball c₀ R ∧ ∀ j, x ∉ Metric.closedBall (c j) (r j)})).homology (N - 1)) ∧
      (∀ m, N ≤ m → CategoryTheory.Limits.IsZero
        ((Work.Cohomology.singularChains ℤ (TopCat.of {x : EuclideanSpace ℝ (Fin N) |
          x ∈ Metric.ball c₀ R ∧ ∀ j, x ∉ Metric.closedBall (c j) (r j)})).homology m)) := by
  classical
  -- The union of the closed balls.
  set K : Set (EuclideanSpace ℝ (Fin N)) :=
    ⋃ i ∈ (Finset.univ : Finset (Fin k)), Metric.closedBall (c i) (r i) with hKdef
  have hKcl : IsClosed K :=
    Set.Finite.isClosed_biUnion (Finset.finite_toSet _)
      (fun i _ => (isCompact_closedBall (c i) (r i)).isClosed)
  have hKsub : K ⊆ Metric.ball c₀ R := by
    intro x hx
    obtain ⟨i, -, hxi⟩ := Set.mem_iUnion₂.mp hx
    exact hsub i hxi
  -- Membership in `K`.
  have hKmem : ∀ x : EuclideanSpace ℝ (Fin N),
      (x ∈ K) ↔ ∃ j : Fin k, x ∈ Metric.closedBall (c j) (r j) := by
    intro x
    rw [hKdef, Set.mem_iUnion₂]
    constructor
    · rintro ⟨i, -, hi⟩; exact ⟨i, hi⟩
    · rintro ⟨i, hi⟩; exact ⟨i, Finset.mem_univ i, hi⟩
  -- The piece of the flat complement to work with.
  set U : Set (TopCat.of {y : EuclideanSpace ℝ (Fin N) | y ∉ K}) :=
    {y : TopCat.of {y : EuclideanSpace ℝ (Fin N) | y ∉ K} |
      (y : EuclideanSpace ℝ (Fin N)) ∈ Metric.ball c₀ R} with hUdef
  -- The target space is homeomorphic to `↥U`.
  have hsetT : {x : EuclideanSpace ℝ (Fin N) | x ∉ K ∧ x ∈ Metric.ball c₀ R}
      = {x : EuclideanSpace ℝ (Fin N) |
          x ∈ Metric.ball c₀ R ∧ ∀ j, x ∉ Metric.closedBall (c j) (r j)} := by
    ext x
    rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, hKmem x, not_exists]
    tauto
  have htgt : (↥U) ≃ₜ (↥{x : EuclideanSpace ℝ (Fin N) |
      x ∈ Metric.ball c₀ R ∧ ∀ j, x ∉ Metric.closedBall (c j) (r j)}) :=
    (flatHomeo (q := fun x : EuclideanSpace ℝ (Fin N) => x ∉ K)
      (P := fun x : EuclideanSpace ℝ (Fin N) => x ∈ Metric.ball c₀ R)).trans
      (Homeomorph.setCongr hsetT)
  -- Vanishing of the homology of the flat complement above the dimension.
  have hzX : ∀ m, N ≤ m → IsZero ((singularChains ℤ
      (TopCat.of {y : EuclideanSpace ℝ (Fin N) | y ∉ K})).homology m) := by
    intro m hm
    have hsub' : Subsingleton ((singularChains ℤ (TopCat.of {x : EuclideanSpace ℝ (Fin N) |
        x ∉ ⋃ i ∈ (Finset.univ : Finset (Fin k)), Metric.closedBall (c i) (r i)})).homology m) :=
      flat_compl_union_convex_homology_vanishing hN (Finset.univ : Finset (Fin k))
        (fun i => Metric.closedBall (c i) (r i)) (fun i _ => isCompact_closedBall _ _)
        (fun i _ => convex_closedBall _ _) m hm
    have hsetK : {x : EuclideanSpace ℝ (Fin N) | x ∉ K}
        = {x : EuclideanSpace ℝ (Fin N) |
            x ∉ ⋃ i ∈ (Finset.univ : Finset (Fin k)), Metric.closedBall (c i) (r i)} := by
      rw [hKdef]
    exact isZero_homology_of_homeomorph (Homeomorph.setCongr hsetK) m
      (ModuleCat.isZero_iff_subsingleton.mpr hsub')
  -- Freeness of `H_{N-1}` of the piece `U`.
  have hfreeU : Module.Free ℤ ↥((singularChains ℤ (TopCat.of ↥U)).homology (N - 1)) := by
    rcases eq_or_lt_of_le hN with hN1 | hN2
    · have h0 : N - 1 = 0 := by omega
      rw [h0]
      exact homology_zero_free (TopCat.of ↥U)
    · obtain ⟨n, φ, hφ⟩ := exists_inj_fin_compl_union_convex hN2
        (Finset.univ : Finset (Fin k)) (fun i => Metric.closedBall (c i) (r i))
        (fun i _ => isCompact_closedBall _ _) (fun i _ => convex_closedBall _ _)
      have hincl : Function.Injective (ModuleCat.Hom.hom
          (pdHomIncl (TopCat.of {y : EuclideanSpace ℝ (Fin N) | y ∉ K}) U (N - 1))) :=
        pdHomIncl_injective_ball c₀ R hR K hKcl hKsub (by omega)
      exact (injective_into_fun_free
        (φ.comp (ModuleCat.Hom.hom (pdHomIncl
          (TopCat.of {y : EuclideanSpace ℝ (Fin N) | y ∉ K}) U (N - 1))))
        (hφ.comp hincl)).2.1
  -- Vanishing of the homology of `U` above the dimension.
  have hzU : ∀ m, N ≤ m → IsZero ((singularChains ℤ (TopCat.of ↥U)).homology m) := by
    intro m hm
    have hincl : Function.Injective (ModuleCat.Hom.hom
        (pdHomIncl (TopCat.of {y : EuclideanSpace ℝ (Fin N) | y ∉ K}) U m)) :=
      pdHomIncl_injective_ball c₀ R hR K hKcl hKsub (by omega)
    haveI : Subsingleton ↥((singularChains ℤ
        (TopCat.of {y : EuclideanSpace ℝ (Fin N) | y ∉ K})).homology m) :=
      ModuleCat.subsingleton_of_isZero (hzX m hm)
    exact ModuleCat.isZero_iff_subsingleton.mpr
      ⟨fun a b => hincl (Subsingleton.elim _ _)⟩
  refine ⟨?_, ?_⟩
  · exact moduleFree_homology_of_homeomorph htgt.symm (N - 1) hfreeU
  · intro m hm
    exact isZero_homology_of_homeomorph htgt.symm m (hzU m hm)

end

end Work.Cohomology
