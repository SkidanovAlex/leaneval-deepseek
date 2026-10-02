/-
# Vanishing of the singular homology of the sphere below the top degree

For `n ≥ 1` and `k ≠ 0, n`, the `k`-th singular homology of the `n`-sphere with `ℤ` coefficients
vanishes: `H_k(Sⁿ; ℤ) = 0`.

The proof is the classical Mayer–Vietoris induction.  The sphere `Sⁿ` is covered by the two
complements `coverU n`, `coverV n` of two antipodal points (`sphereN n`, `sphereS n`); each is
contractible (`sphere_compl_singleton_contractible`, via stereographic projection), and their
intersection is the sphere with two points removed, which is homeomorphic to `ℝⁿ ∖ {0}`
(`coverInterHomeo`) and hence homotopy equivalent to `Sⁿ⁻¹` (`punctured_homotopyEquiv_sphere`).
The Mayer–Vietoris sequence of this cover therefore gives

* `H_k(Sⁿ) ≅ H_{k-1}(coverU n ∩ coverV n) ≅ H_{k-1}(Sⁿ⁻¹)` for `k ≥ 2`, which lowers both `n`
  and `k` and reduces to the induction hypothesis;
* for `k = 1`, since `H_1` of both (contractible) pieces vanishes, the connecting map embeds
  `H_1(Sⁿ)` into `H_0(coverU n ∩ coverV n)`, and by `ker_mvLeft_zero_eq_ker_eps` the latter embeds
  into the kernel of the augmentation of the intersection — which is zero because the intersection
  is path connected for `n ≥ 2` (`pathConnectedSpace_coverInter`).

The induction is started at `S⁰`, a finite discrete space, whose positive-degree homology vanishes
by Mathlib's `isZero_singularHomologyFunctor_of_totallyDisconnectedSpace`.
-/
import Mathlib
import Submission.Work.Cohomology.MVSequence
import Submission.Work.Cohomology.sphereHomologyTop
import Submission.Work.Cohomology.sphere_compl_singleton_contractible
import Submission.Work.Cohomology.punctured_homotopyEquiv_sphere
import Submission.Work.Cohomology.isZero_homology_of_homotopyEquiv
import Submission.Work.Cohomology.sphereInUnitOneHomologyZero
import Submission.Work.Cohomology.sphereInUnitHomologyIso

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

open CategoryTheory AlgebraicTopology Limits
open scoped Topology

namespace Work.Cohomology

noncomputable section

/-- The unit sphere `Sⁿ ⊆ ℝⁿ⁺¹`, as a topological space. -/
abbrev sph (n : ℕ) : TopCat :=
  TopCat.of ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)

/-! ## Part 1: the cover of `Sⁿ` by the complements of two antipodal points -/

/-- `OnePoint X \ {∞}` is homeomorphic to `X`. -/
noncomputable def onePointNeInftyHomeo (X : Type*) [TopologicalSpace X] :
    {p : OnePoint X // p ≠ OnePoint.infty} ≃ₜ X :=
  ((OnePoint.isOpenEmbedding_coe.toIsEmbedding.homeomorphOfSubsetRange
      (s := {p | p ≠ OnePoint.infty})
      (by
        intro p hp
        obtain ⟨x, rfl⟩ := OnePoint.ne_infty_iff_exists.mp hp
        exact ⟨x, rfl⟩)).symm.trans
    ((Homeomorph.setCongr (by
        ext v
        simp)).trans
      (Homeomorph.Set.univ X)))

/-- `OnePoint X \ {∞, 0}` is homeomorphic to `X \ {0}`. -/
noncomputable def onePointNeInftyNeZeroHomeo (X : Type*) [TopologicalSpace X] [Zero X] :
    {p : OnePoint X // p ≠ OnePoint.infty ∧ p ≠ ((0 : X) : OnePoint X)} ≃ₜ {v : X // v ≠ 0} :=
  ((OnePoint.isOpenEmbedding_coe.toIsEmbedding.homeomorphOfSubsetRange
      (s := {p | p ≠ OnePoint.infty ∧ p ≠ ((0 : X) : OnePoint X)})
      (by
        intro p hp
        obtain ⟨x, rfl⟩ := OnePoint.ne_infty_iff_exists.mp hp.1
        exact ⟨x, rfl⟩)).symm.trans
    (Homeomorph.setCongr (by
      ext v
      constructor
      · intro hv
        exact fun h => hv.2 (by rw [h])
      · intro hv
        exact ⟨OnePoint.coe_ne_infty v, fun h => hv (OnePoint.coe_eq_coe.mp h)⟩)))

/-- `OnePoint (ℝⁿ)` is homeomorphic to `Sⁿ`. -/
noncomputable def sphereOnePointHomeo (n : ℕ) :
    OnePoint (EuclideanSpace ℝ (Fin n)) ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 :=
  onePointEquivSphereOfFinrankEq (V := EuclideanSpace ℝ (Fin n)) (ι := Fin (n+1)) (by simp)

/-- The "north pole" of `Sⁿ`, the point corresponding to `∞`. -/
noncomputable def sphereN (n : ℕ) : Metric.sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1 :=
  (sphereOnePointHomeo n) OnePoint.infty

/-- The "south pole" of `Sⁿ`, the point corresponding to `0`. -/
noncomputable def sphereS (n : ℕ) : Metric.sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1 :=
  (sphereOnePointHomeo n) (0 : EuclideanSpace ℝ (Fin n))

theorem sphereN_ne_sphereS (n : ℕ) : sphereN n ≠ sphereS n := by
  intro h
  exact OnePoint.infty_ne_coe (0 : EuclideanSpace ℝ (Fin n)) ((sphereOnePointHomeo n).injective h)

/-- The open piece of the cover of `Sⁿ`: the complement of the north pole. -/
def coverU (n : ℕ) : Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1) :=
  {y | y ≠ sphereN n}

/-- The open piece of the cover of `Sⁿ`: the complement of the south pole. -/
def coverV (n : ℕ) : Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1) :=
  {y | y ≠ sphereS n}

theorem isOpen_coverU (n : ℕ) : IsOpen (coverU n) := isOpen_compl_singleton
theorem isOpen_coverV (n : ℕ) : IsOpen (coverV n) := isOpen_compl_singleton

theorem coverU_union_coverV (n : ℕ) : coverU n ∪ coverV n = Set.univ := by
  ext y
  simp only [Set.mem_union, Set.mem_univ, iff_true, coverU, coverV, Set.mem_ofPred_eq]
  by_cases h : y = sphereN n
  · exact Or.inr (by rw [h]; exact sphereN_ne_sphereS n)
  · exact Or.inl h

/-- The image of the complement of a point under a homeomorphism. -/
theorem image_compl_singleton {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    (e : α ≃ₜ β) (c : α) : e '' {p | p ≠ c} = {y | y ≠ e c} := by
  ext y
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact fun h => hp (e.injective h)
  · intro hy
    exact ⟨e.symm y, fun h => hy (by rw [← h, Homeomorph.apply_symm_apply]), by simp⟩

/-- The complement of the two poles is homeomorphic to `ℝⁿ \ {0}`. -/
noncomputable def coverInterHomeo (n : ℕ) :
    ↥(coverU n ∩ coverV n) ≃ₜ {v : EuclideanSpace ℝ (Fin n) // v ≠ 0} :=
  (Homeomorph.setCongr (by
    rw [show coverU n ∩ coverV n =
        {y | y ≠ (sphereOnePointHomeo n) OnePoint.infty} ∩
          {y | y ≠ (sphereOnePointHomeo n) ((0 : EuclideanSpace ℝ (Fin n)) : OnePoint _)} from rfl,
      ← image_compl_singleton (sphereOnePointHomeo n) OnePoint.infty,
      ← image_compl_singleton (sphereOnePointHomeo n) ((0 : EuclideanSpace ℝ (Fin n)) : OnePoint _),
      ← Set.image_inter (sphereOnePointHomeo n).injective])).symm.trans
    ((Homeomorph.image (sphereOnePointHomeo n)
      ({p | p ≠ OnePoint.infty} ∩
        {p | p ≠ ((0 : EuclideanSpace ℝ (Fin n)) : OnePoint _)})).symm.trans
      (onePointNeInftyNeZeroHomeo (EuclideanSpace ℝ (Fin n))))

/-- The intersection of the two pieces of the cover is path connected as soon as `n ≥ 2`. -/
theorem pathConnectedSpace_coverInter (n : ℕ) (hn : 2 ≤ n) :
    PathConnectedSpace ↥(coverU n ∩ coverV n) := by
  have hrank : 1 < Module.rank ℝ (EuclideanSpace ℝ (Fin n)) := by
    rw [← Module.finrank_eq_rank]
    have h : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n := by simp
    rw [h, ← Nat.cast_one, Nat.cast_lt]
    omega
  haveI : PathConnectedSpace {v : EuclideanSpace ℝ (Fin n) // v ≠ 0} :=
    (isPathConnected_iff_pathConnectedSpace
      (F := ({0} : Set (EuclideanSpace ℝ (Fin n)))ᶜ)).mp
      (by simpa using isPathConnected_compl_singleton_of_one_lt_rank hrank 0)
  have h : IsPathConnected (Set.univ : Set {v : EuclideanSpace ℝ (Fin n) // v ≠ 0}) :=
    isPathConnected_univ
  refine (pathConnectedSpace_iff_univ).mpr ?_
  simpa using (Homeomorph.isPathConnected_preimage (coverInterHomeo n)).mpr h

/-! ## Part 2: the degree-zero augmentation of a path-connected space -/

/-- For a path-connected space the augmentation `H₀(X) ⟶ ℤ` is an isomorphism, so the kernel of
its underlying linear map, viewed as a `ModuleCat ℤ`, is a zero object. -/
lemma isZero_kerMod_eps_of_pathConnected (X : TopCat) [PathConnectedSpace X] :
    IsZero (kerMod (ModuleCat.Hom.hom
      (TopCat.singularHomology₀ε X (ModuleCat.of ℤ ℤ)))) := by
  haveI : IsIso (TopCat.singularHomology₀ε X (ModuleCat.of ℤ ℤ)) := inferInstance
  rw [ModuleCat.isZero_iff_subsingleton]
  show Subsingleton ↥(LinearMap.ker (ModuleCat.Hom.hom
    (TopCat.singularHomology₀ε X (ModuleCat.of ℤ ℤ))))
  rw [LinearMap.ker_eq_bot.mpr ((ModuleCat.mono_iff_injective _).mp inferInstance)]
  infer_instance

/-! ## Part 3: the base case `S⁰` -/

/-- `H_k(S⁰) = 0` for `k ≥ 1`: the zero-dimensional sphere is a finite discrete space. -/
theorem isZero_homology_sphereZero (k : ℕ) (hk : 1 ≤ k) :
    IsZero ((singularChains ℤ (sph 0)).homology k) := by
  obtain ⟨e⟩ := sphereInUnitHomologyIso 1 k
  exact IsZero.of_iso (sphereInUnitOneHomologyZero k hk) e.symm

/-! ## Part 4: vanishing below the top degree -/

/-- **`H_k(Sⁿ) = 0` for `k ≥ 1`, `k ≠ n`** (this is the induction form; the case `n = 0` is the
finite discrete sphere `S⁰`). -/
theorem sphereHomologyZero_aux (n : ℕ) :
    ∀ k, 1 ≤ k → k ≠ n → IsZero ((singularChains ℤ (sph n)).homology k) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro k hk hnk
    rcases Nat.eq_zero_or_pos n with rfl | hnpos
    · -- `n = 0`: the two-point sphere `S⁰`
      exact isZero_homology_sphereZero k hk
    · rcases eq_or_lt_of_le hk with hk1 | hk2
      · -- `k = 1`, hence `n ≥ 2`
        subst hk1
        have hn2 : 2 ≤ n := by omega
        haveI hUc : ContractibleSpace ↥(coverU n) :=
          sphere_compl_singleton_contractible (EuclideanSpace ℝ (Fin (n+1))) (sphereN n)
        haveI hVc : ContractibleSpace ↥(coverV n) :=
          sphere_compl_singleton_contractible (EuclideanSpace ℝ (Fin (n+1))) (sphereS n)
        haveI hpc : PathConnectedSpace ↥(coverU n ∩ coverV n) :=
          pathConnectedSpace_coverInter n hn2
        -- `H₁(Sⁿ)` embeds into `H₀(coverU n ∩ coverV n)` …
        obtain ⟨e1⟩ := mvδX_zero_iso (X := sph n) (coverU n) (coverV n) (isOpen_coverU n)
          (isOpen_coverV n) (coverU_union_coverV n)
        -- … whose image lies in the kernel of the augmentation of the intersection,
        have hker : LinearMap.ker (ModuleCat.Hom.hom
              (HomologicalComplex.homologyMap (mvLeft (X := sph n) (coverU n) (coverV n)) 0))
            = LinearMap.ker (ModuleCat.Hom.hom (TopCat.singularHomology₀ε
                (TopCat.of ↥(coverU n ∩ coverV n)) (ModuleCat.of ℤ ℤ))) :=
          ker_mvLeft_zero_eq_ker_eps (X := sph n) (coverU n) (coverV n)
        have e2 : kerMod (ModuleCat.Hom.hom
              (HomologicalComplex.homologyMap (mvLeft (X := sph n) (coverU n) (coverV n)) 0))
            ≅ kerMod (ModuleCat.Hom.hom (TopCat.singularHomology₀ε
                (TopCat.of ↥(coverU n ∩ coverV n)) (ModuleCat.of ℤ ℤ))) :=
          LinearEquiv.toModuleIso (LinearEquiv.ofEq _ _ hker)
        have hz : IsZero (kerMod (ModuleCat.Hom.hom
            (HomologicalComplex.homologyMap (mvLeft (X := sph n) (coverU n) (coverV n)) 0))) :=
          IsZero.of_iso
            (isZero_kerMod_eps_of_pathConnected (TopCat.of ↥(coverU n ∩ coverV n))) e2
        -- … which is zero because the intersection is path connected.
        exact IsZero.of_iso hz e1
      · -- `k ≥ 2`
        have hk1 : 1 ≤ k - 1 := by omega
        have hnk1 : k - 1 ≠ n - 1 := by omega
        haveI hUc : ContractibleSpace ↥(coverU n) :=
          sphere_compl_singleton_contractible (EuclideanSpace ℝ (Fin (n+1))) (sphereN n)
        haveI hVc : ContractibleSpace ↥(coverV n) :=
          sphere_compl_singleton_contractible (EuclideanSpace ℝ (Fin (n+1))) (sphereS n)
        -- The Mayer–Vietoris connecting map `H_k(Sⁿ) ⟶ H_{k-1}(coverU n ∩ coverV n)` is an
        -- isomorphism because both `H_k` and `H_{k-1}` of the (contractible) pieces vanish.
        haveI hiso : IsIso (mvδX (X := sph n) (coverU n) (coverV n) (isOpen_coverU n)
            (isOpen_coverV n) (coverU_union_coverV n) (k - 1)) :=
          mvδX_isIso (X := sph n) (coverU n) (coverV n) (isOpen_coverU n) (isOpen_coverV n)
            (coverU_union_coverV n) (k - 1) hk1
        -- The intersection is homotopy equivalent to `Sⁿ⁻¹ = sph (n-1)`.
        have he : ContinuousMap.HomotopyEquiv (TopCat.of ↥(coverU n ∩ coverV n))
            (TopCat.of (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1)) :=
          ((coverInterHomeo n).toHomotopyEquiv).trans
            (punctured_homotopyEquiv_sphere (EuclideanSpace ℝ (Fin n))).some
        have hn1 : n - 1 + 1 = n := Nat.sub_add_cancel hnpos
        -- the two spellings of `Sⁿ⁻¹` agree
        have hsph : sph (n - 1) =
            TopCat.of ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) := by
          show TopCat.of ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n - 1 + 1))) 1) = _
          rw [hn1]
        have hIH : IsZero ((singularChains ℤ (sph (n - 1))).homology (k - 1)) :=
          ih (n - 1) (by omega) (k - 1) hk1 hnk1
        rw [hsph] at hIH
        have hInter : IsZero ((singularChains ℤ
            (TopCat.of ↥(coverU n ∩ coverV n))).homology (k - 1)) :=
          isZero_homology_of_homotopyEquiv he (k - 1) hIH
        have key : (singularChains ℤ (sph n)).homology ((k - 1) + 1) ≅
            (singularChains ℤ (TopCat.of ↥(coverU n ∩ coverV n))).homology (k - 1) :=
          asIso (mvδX (X := sph n) (coverU n) (coverV n) (isOpen_coverU n) (isOpen_coverV n)
            (coverU_union_coverV n) (k - 1))
        rw [Nat.sub_add_cancel hk] at key
        exact IsZero.of_iso hInter key

/-- **The homology of `Sⁿ` vanishes in every degree `k ≠ 0, n`** (`n ≥ 1`). -/
theorem sphereHomologyZero (n k : ℕ) (hn : 1 ≤ n) (h0 : k ≠ 0) (hnk : k ≠ n) :
    CategoryTheory.Limits.IsZero
      ((Work.Cohomology.singularChains ℤ
        (TopCat.of (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1))).homology k) :=
  sphereHomologyZero_aux n k (by omega) hnk

end

end Work.Cohomology
