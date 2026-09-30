import Mathlib
import Submission.Work.Cohomology.smallChains_homology_iso
import Submission.Work.Cohomology.SmallChainsIsoAux
import Submission.Work.Cohomology.exists_iter_small
import Submission.Work.Cohomology.exists_small_homotopy

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The small-simplices theorem for covers by interiors

`Work.Cohomology.smallChains_homology_iso` proves that for an **open** cover `X = U ∪ V` the
inclusion `smallToSing U V` of the small chains into the singular chains of `X` is an isomorphism
on homology.  The classical hypothesis needed for the Mayer–Vietoris sequence is weaker: it
suffices that the *interiors* cover, `interior U ∪ interior V = univ`.

The proof of the open version uses the openness of `U` and `V` in exactly one place: the
refinement statement `exists_iter_small` ("some iterate of the barycentric subdivision of a
simplex is small"), which is proved from the Lebesgue number of the pulled-back cover of `Δⁿ`.
Everything downstream of it — the directed-limit argument giving `exists_iter_small_chain`, the
local homotopy `Sd^N ~ id` (`exists_small_homotopy`) and the two elementwise statements
`exists_d_eq_of_smallToSing_eq` / `exists_smallToSing_add_d` — never uses openness again.

Accordingly this file separates that one use:

* `exists_iter_small_int` — for a cover by interiors, some iterate of the subdivision of a
  generator is small.  It is deduced from `exists_iter_small` applied to the open cover
  `interior U ∪ interior V = univ`, together with monotonicity of smallness in the sets
  (`IsSmall.mono_of_subset`, `IsSmallChain.mono_of_subset`);
* `exists_iter_small_chain_of` — the directed-limit argument, stated with the refinement property
  as a hypothesis rather than with openness;
* `exists_d_eq_of_smallToSing_eq_gen`, `exists_smallToSing_add_d_gen` — the two elementwise steps
  of the small-simplices theorem, again with the refinement property as a hypothesis.

The requested statement `smallChains_homology_iso_int` is then assembled in the same way as the
open version, from the `_int` specialisations of those two elementwise steps.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option linter.style.haveILetI false

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Cohomology

noncomputable section

variable {X : TopCat}

/-! ## Monotonicity of smallness in the covering sets -/

/-- A simplex that is small for `(A, B)` is small for any larger pair of sets. -/
theorem IsSmall.mono_of_subset {A A' B B' : Set X} (hA : A ⊆ A') (hB : B ⊆ B')
    {n : SimplexCategoryᵒᵖ} {σ : (TopCat.toSSet.obj X).obj n} (h : IsSmall A B σ) :
    IsSmall A' B' σ :=
  h.imp (fun h1 => h1.trans hA) (fun h2 => h2.trans hB)

/-- A chain that is small for `(A, B)` is small for any larger pair of sets. -/
theorem IsSmallChain.mono_of_subset {A A' B B' : Set X} (hA : A ⊆ A') (hB : B ⊆ B') {n : ℕ}
    {c : (singularChains ℤ X).X n} (hc : IsSmallChain A B c) : IsSmallChain A' B' c := by
  obtain ⟨c', rfl⟩ := hc
  exact isSmallChain_of_gen (U := A') (V := B') ((smallToSing A B).f n)
    (fun y => by
      rw [smallToSing_gen]
      exact isSmallChain_gen (IsSmall.mono_of_subset hA hB y.2)) c'

/-- **Refinement for a cover by interiors.**  If `interior U ∪ interior V = univ`, then some
iterate of the barycentric subdivision of every singular simplex generates a small chain. -/
theorem exists_iter_small_int (U V : Set X) (hcov : interior U ∪ interior V = Set.univ)
    (n : ℕ) (σ : Simplex X n) :
    ∃ N, IsSmallChain U V ((sdChainMapIter X N).f n (gen X n σ)) := by
  obtain ⟨N, hN⟩ :=
    exists_iter_small (interior U) (interior V) isOpen_interior isOpen_interior hcov n σ
  exact ⟨N, IsSmallChain.mono_of_subset interior_subset interior_subset hN⟩

/-! ## The directed-limit refinement of an arbitrary chain -/

/-- **Some iterate of the subdivision sends any chain into the small chains**, assuming the
refinement property on generators.  This is `exists_iter_small_chain` with the openness hypotheses
replaced by the single refinement hypothesis actually used. -/
theorem exists_iter_small_chain_of (U V : Set X) (n : ℕ) (c : (singularChains ℤ X).X n)
    (href : ∀ m (σ : Simplex X m),
      ∃ N, IsSmallChain U V ((sdChainMapIter X N).f m (gen X m σ))) :
    ∃ N, IsSmallChain U V ((sdChainMapIter X N).f n c) := by
  let P : Submodule ℤ ↥((singularChains ℤ X).X n) :=
    ⨆ N, Submodule.comap (ModuleCat.Hom.hom ((sdChainMapIter X N).f n))
      (smallChainSubmodule U V n)
  have hgen : ∀ σ : (TopCat.toSSet.obj X) _⦋n⦌, gen X n σ ∈ P := by
    intro σ
    obtain ⟨N, hN⟩ := href n σ
    exact le_iSup (fun N => Submodule.comap (ModuleCat.Hom.hom ((sdChainMapIter X N).f n))
      (smallChainSubmodule U V n)) N hN
  have htop : P = ⊤ := mem_of_gen X n P hgen
  have hdir : Directed (· ≤ ·)
      (fun N => Submodule.comap (ModuleCat.Hom.hom ((sdChainMapIter X N).f n))
        (smallChainSubmodule U V n)) := by
    intro N M
    refine ⟨N + M, ?_, ?_⟩
    · rintro x hx
      rw [Submodule.mem_comap] at hx ⊢
      rw [sdChainMapIter_f_apply X N M n x]
      exact iter_sd_small U V M hx
    · rintro x hx
      rw [Submodule.mem_comap] at hx ⊢
      rw [show N + M = M + N from Nat.add_comm N M, sdChainMapIter_f_apply X M N n x]
      exact iter_sd_small U V N hx
  have hmem : c ∈ P := by
    rw [htop]
    exact Submodule.mem_top
  rw [Submodule.mem_iSup_of_directed _ hdir] at hmem
  obtain ⟨N, hN⟩ := hmem
  exact ⟨N, hN⟩

/-- **Some iterate of the subdivision sends any chain into the small chains**, for a cover by
interiors. -/
theorem exists_iter_small_chain_int (U V : Set X) (hcov : interior U ∪ interior V = Set.univ)
    (n : ℕ) (c : (singularChains ℤ X).X n) :
    ∃ N, IsSmallChain U V ((sdChainMapIter X N).f n c) :=
  exists_iter_small_chain_of U V n c (fun m σ => exists_iter_small_int U V hcov m σ)

/-! ## The two elementwise steps of the small-simplices theorem -/

/-- **El-Mono**, assuming the refinement property.  A cycle of small chains whose image in the
singular chains of `X` is a boundary is itself a boundary. -/
theorem exists_d_eq_of_smallToSing_eq_gen (U V : Set X) (n : ℕ)
    (href : ∀ m (σ : Simplex X m),
      ∃ N, IsSmallChain U V ((sdChainMapIter X N).f m (gen X m σ)))
    {z : (smallChains U V).X n}
    (hz : ((smallChains U V).d n (n-1)) z = 0)
    {a : (singularChains ℤ X).X (n+1)}
    (ha : ((smallToSing U V).f n) z = ((singularChains ℤ X).d (n+1) n) a) :
    ∃ w : (smallChains U V).X (n+1), ((smallChains U V).d (n+1) n) w = z := by
  obtain ⟨N, hN⟩ := exists_iter_small_chain_of U V (n+1) a href
  obtain ⟨b, hb⟩ := hN
  obtain ⟨T, hT⟩ := exists_small_homotopy X U V N
  obtain ⟨b', hb'⟩ := hT n (((smallToSing U V).f n) z) ⟨z, rfl⟩
  have hcomm : ∀ (m : ℕ) (c : (smallChains U V).X (m+1)),
      ((singularChains ℤ X).d (m+1) m) (((smallToSing U V).f (m+1)) c)
        = ((smallToSing U V).f m) (((smallChains U V).d (m+1) m) c) := by
    intro m c
    have h := congrArg (fun (g : (smallChains U V).X (m+1) ⟶ (singularChains ℤ X).X m) =>
      g c) (HomologicalComplex.Hom.comm (smallToSing U V) (m+1) m)
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h
  have hiter : ((singularChains ℤ X).d (n+1) n) (((sdChainMapIter X N).f (n+1)) a)
      = ((sdChainMapIter X N).f n) (((singularChains ℤ X).d (n+1) n) a) := by
    have h := congrArg (fun (g : (singularChains ℤ X).X (n+1) ⟶ (singularChains ℤ X).X n) =>
      g a) (HomologicalComplex.Hom.comm (sdChainMapIter X N) (n+1) n)
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h
  have hzero : ((singularChains ℤ X).d n (n-1)) (((smallToSing U V).f n) z) = 0 := by
    have h := congrArg (fun (g : (smallChains U V).X n ⟶ (singularChains ℤ X).X (n-1)) =>
      g z) (HomologicalComplex.Hom.comm (smallToSing U V) n (n-1))
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, hz, map_zero] at h
    exact h
  have key : ((smallChains U V).d (n+1) n) b = ((smallChains U V).d (n+1) n) b' + z := by
    apply smallToSing_f_injective U V n
    calc ((smallToSing U V).f n) (((smallChains U V).d (n+1) n) b)
        = ((singularChains ℤ X).d (n+1) n) (((smallToSing U V).f (n+1)) b) := (hcomm n b).symm
      _ = ((singularChains ℤ X).d (n+1) n) (((sdChainMapIter X N).f (n+1)) a) := by rw [hb]
      _ = ((sdChainMapIter X N).f n) (((singularChains ℤ X).d (n+1) n) a) := hiter
      _ = ((sdChainMapIter X N).f n) (((smallToSing U V).f n) z) := by rw [ha]
      _ = ((singularChains ℤ X).d (n+1) n) ((T.hom n (n+1)) (((smallToSing U V).f n) z))
            + ((smallToSing U V).f n) z := by
          rw [homotopy_apply_eq X N n T (((smallToSing U V).f n) z), hzero, map_zero, zero_add]
      _ = ((smallToSing U V).f n) (((smallChains U V).d (n+1) n) b')
            + ((smallToSing U V).f n) z := by
          rw [← hb', hcomm n b']
      _ = ((smallToSing U V).f n) (((smallChains U V).d (n+1) n) b' + z) := by rw [map_add]
  refine ⟨b - b', ?_⟩
  rw [map_sub, key]
  abel

/-- **El-Epi**, assuming the refinement property.  Every cycle of the singular chains of `X`
differs from a cycle of small chains by a boundary. -/
theorem exists_smallToSing_add_d_gen (U V : Set X) (n : ℕ)
    (href : ∀ m (σ : Simplex X m),
      ∃ N, IsSmallChain U V ((sdChainMapIter X N).f m (gen X m σ)))
    {z : (singularChains ℤ X).X n}
    (hz : ((singularChains ℤ X).d n (n-1)) z = 0) :
    ∃ (c : (smallChains U V).X n) (b : (singularChains ℤ X).X (n+1)),
      ((smallChains U V).d n (n-1)) c = 0 ∧
        ((smallToSing U V).f n) c = z + ((singularChains ℤ X).d (n+1) n) b := by
  obtain ⟨N, hN⟩ := exists_iter_small_chain_of U V n z href
  obtain ⟨c, hc⟩ := hN
  obtain ⟨T, _hT⟩ := exists_small_homotopy X U V N
  have hcycle : ((smallChains U V).d n (n-1)) c = 0 := by
    have hcomm : ((smallToSing U V).f (n-1)) (((smallChains U V).d n (n-1)) c)
        = ((singularChains ℤ X).d n (n-1)) (((smallToSing U V).f n) c) := by
      have h := congrArg (fun (g : (smallChains U V).X n ⟶ (singularChains ℤ X).X (n-1)) =>
        g c) (HomologicalComplex.Hom.comm (smallToSing U V) n (n-1))
      simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h.symm
    have hiter : ((singularChains ℤ X).d n (n-1)) (((sdChainMapIter X N).f n) z)
        = ((sdChainMapIter X N).f (n-1)) (((singularChains ℤ X).d n (n-1)) z) := by
      have h := congrArg (fun (g : (singularChains ℤ X).X n ⟶ (singularChains ℤ X).X (n-1)) =>
        g z) (HomologicalComplex.Hom.comm (sdChainMapIter X N) n (n-1))
      simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h
    have h2 : ((smallToSing U V).f (n-1)) (((smallChains U V).d n (n-1)) c)
        = ((smallToSing U V).f (n-1)) 0 := by
      rw [map_zero, hcomm, hc, hiter, hz, map_zero]
    exact smallToSing_f_injective U V (n-1) h2
  refine ⟨c, ((T.hom n (n+1)) z), hcycle, ?_⟩
  calc ((smallToSing U V).f n) c
      = ((sdChainMapIter X N).f n) z := hc
    _ = ((singularChains ℤ X).d (n+1) n) ((T.hom n (n+1)) z) + z := by
        rw [homotopy_apply_eq X N n T z, hz, map_zero, zero_add]
    _ = z + ((singularChains ℤ X).d (n+1) n) ((T.hom n (n+1)) z) := by
        rw [add_comm]

/-- **El-Mono** for a cover by interiors. -/
theorem exists_d_eq_of_smallToSing_eq_int (U V : Set X)
    (hcov : interior U ∪ interior V = Set.univ) (n : ℕ) {z : (smallChains U V).X n}
    (hz : ((smallChains U V).d n (n-1)) z = 0)
    {a : (singularChains ℤ X).X (n+1)}
    (ha : ((smallToSing U V).f n) z = ((singularChains ℤ X).d (n+1) n) a) :
    ∃ w : (smallChains U V).X (n+1), ((smallChains U V).d (n+1) n) w = z :=
  exists_d_eq_of_smallToSing_eq_gen U V n (fun m σ => exists_iter_small_int U V hcov m σ) hz ha

/-- **El-Epi** for a cover by interiors. -/
theorem exists_smallToSing_add_d_int (U V : Set X)
    (hcov : interior U ∪ interior V = Set.univ) (n : ℕ) {z : (singularChains ℤ X).X n}
    (hz : ((singularChains ℤ X).d n (n-1)) z = 0) :
    ∃ (c : (smallChains U V).X n) (b : (singularChains ℤ X).X (n+1)),
      ((smallChains U V).d n (n-1)) c = 0 ∧
        ((smallToSing U V).f n) c = z + ((singularChains ℤ X).d (n+1) n) b :=
  exists_smallToSing_add_d_gen U V n (fun m σ => exists_iter_small_int U V hcov m σ) hz

/-! ## The small-simplices theorem for a cover by interiors -/

/-- Small simplices compute homology for a cover by interiors: the statement
`Work.Cohomology.smallChains_homology_iso` with `IsOpen U`, `IsOpen V`, `U ∪ V = univ` replaced
by `interior U ∪ interior V = univ`. -/
theorem smallChains_homology_iso_int {X : TopCat} (U V : Set X)
    (hcov : interior U ∪ interior V = Set.univ) (n : ℕ) :
    CategoryTheory.IsIso (HomologicalComplex.homologyMap (smallToSing U V) n) := by
  haveI hmono : CategoryTheory.Mono (HomologicalComplex.homologyMap (smallToSing U V) n) :=
    mono_homologyMap_of_cycles (smallToSing U V) n (fun z hz a ha =>
      exists_d_eq_of_smallToSing_eq_int U V hcov n hz ha)
  haveI hepi : CategoryTheory.Epi (HomologicalComplex.homologyMap (smallToSing U V) n) :=
    epi_homologyMap_of_cycles (smallToSing U V) n (fun z hz =>
      exists_smallToSing_add_d_int U V hcov n hz)
  exact (ConcreteCategory.isIso_iff_bijective
      (HomologicalComplex.homologyMap (smallToSing U V) n)).mpr
    ⟨(ModuleCat.mono_iff_injective (HomologicalComplex.homologyMap (smallToSing U V) n)).mp hmono,
      (ModuleCat.epi_iff_surjective (HomologicalComplex.homologyMap (smallToSing U V) n)).mp hepi⟩

end

end Work.Cohomology
