import Mathlib
import Submission.Work.Whitney.Signed.ModelSide
import Submission.Work.Thom.stepDefs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

open Work.Cohomology Work.Thom
open CategoryTheory
open scoped Simplicial

/-!
# Vanishing of a band-relative lifted cochain on band-small chains

Let `ψ` be an `n`-cocycle of `Y × Sⁿ` relative to the lower band `SphB Y n`, and let `bt` be any
cochain of the total space `Y × ℝⁿ⁺¹` whose restriction to the unit sphere `Sph Y (n+1)` is the
push-forward `sphPushCochain Y n ψ.1` of `ψ.1` along the identification `Sph Y (n+1) ≃ Y × Sⁿ`.

The lemma below says that `bt` pairs to zero with every chain `c` carried by the lower band
`BandFull Y n = {p | p.2 ∈ mLower n}`:
the band is contained in the sphere (`BandFull_subset_Sph`), so a band-small simplex comes from a
simplex of the sphere, its generator is the push-forward of a generator, and on a generator the
pushed cochain is evaluated at a simplex whose image lies in `SphB Y n` — where a relative cocycle
vanishes (`genEval_eq_zero_of_mem_relKern`).

The chain-level statement is deduced from the generator-level one by the `mem_of_genSSet` pattern
already used in `Work.Cohomology.kronecker_eq_zero_of_isSmallChain_of_mem_relKern`.
-/

namespace Work.Whitney.tcmSuspAux

/-- **A cochain which vanishes on the generators of the `U`-small simplices vanishes on every
`U`-small chain.** -/
theorem kronecker_eq_zero_of_isSmallChain_of_gen_zero {X : TopCat} (U : Set X) (n : ℕ)
    (bt : Cochain ℤ (TopCat.toSSet.obj X) n)
    (hgen : ∀ σ : Simplex X n, IsSmall U (∅ : Set X) σ → bt (gen X n σ) = 0)
    (c : (singularChains ℤ X).X n) (hc : IsSmallChain U (∅ : Set X) c) :
    kronecker ℤ (TopCat.toSSet.obj X) bt c = 0 := by
  classical
  obtain ⟨c', hc'⟩ := hc
  let Q : Submodule ℤ ↥((smallChains U (∅ : Set X)).X n) :=
    Submodule.comap ((smallToSing U (∅ : Set X)).f n).hom (LinearMap.ker bt)
  have hQ : Q = ⊤ := by
    refine mem_of_genSSet (smallSSet U (∅ : Set X)) n Q ?_
    intro τ
    show ((smallToSing U (∅ : Set X)).f n).hom
      (genSSet (smallSSet U (∅ : Set X)) n τ) ∈ LinearMap.ker bt
    rw [smallToSing_gen τ, LinearMap.mem_ker]
    exact hgen τ.1 τ.2
  have hmem : c' ∈ Q := by rw [hQ]; exact Submodule.mem_top
  have hval : bt (((smallToSing U (∅ : Set X)).f n).hom c') = 0 := hmem
  rw [← hc']
  exact hval

theorem kronecker_eq_zero_of_isSmallChain_of_restr_sphPush
    (Y : Type) [TopologicalSpace Y] (n : ℕ)
    (ψ : ↥(Work.Cohomology.relKern ℤ (TopCat.of (Y × Work.Thom.MSph (n + 1))) (Work.Thom.SphB Y n) n))
    (bt : Work.Cohomology.Cochain ℤ (Work.Whitney.ssB (Y × EuclideanSpace ℝ (Fin (n + 1)))) n)
    (hbt : (ModuleCat.Hom.hom ((Work.Cohomology.restr ℤ (TopCat.of (Y × EuclideanSpace ℝ (Fin (n+1))))
        (Work.Thom.Sph Y (n+1))).f n)) bt = Work.Whitney.sphPushCochain Y n ψ.1)
    (c : (Work.Cohomology.singularChains ℤ (TopCat.of (Y × EuclideanSpace ℝ (Fin (n+1))))).X n)
    (hc : Work.Cohomology.IsSmallChain (Work.Whitney.BandFull Y n)
        (∅ : Set (Y × EuclideanSpace ℝ (Fin (n+1)))) c) :
    Work.Cohomology.kronecker ℤ (Work.Whitney.ssB (Y × EuclideanSpace ℝ (Fin (n + 1)))) bt c = 0 := by
  classical
  refine kronecker_eq_zero_of_isSmallChain_of_gen_zero
    (X := TopCat.of (Y × EuclideanSpace ℝ (Fin (n + 1)))) (Work.Whitney.BandFull Y n) n
    bt ?_ c hc
  intro σ hσ
  -- The sphere simplex whose push-forward is `σ`.
  have hσS : IsSmall (Sph Y (n+1)) (∅ : Set (Y × EuclideanSpace ℝ (Fin (n+1)))) σ :=
    Work.Whitney.IsSmall.mono (Work.Whitney.BandFull_subset_Sph Y n) hσ
  obtain ⟨τ, hτ⟩ := exists_simplex_subtypeIncl_of_isSmall
    (X := TopCat.of (Y × EuclideanSpace ℝ (Fin (n+1)))) (A := Sph Y (n+1)) hσS
  -- `σ` is the push-forward of `τ` along the inclusion of the sphere.
  have hpush : gen (TopCat.of (Y × EuclideanSpace ℝ (Fin (n+1)))) n σ
      = pushChain (TopCat.of ↥(Sph Y (n+1))) (TopCat.of (Y × EuclideanSpace ℝ (Fin (n+1))))
          (subtypeIncl (TopCat.of (Y × EuclideanSpace ℝ (Fin (n+1)))) (Sph Y (n+1))) n
          (gen (TopCat.of ↥(Sph Y (n+1))) n τ) := by
    rw [pushChain_gen, hτ]
  -- On the sphere, `bt` is the pushed cochain.
  have h1 : bt (pushChain (TopCat.of ↥(Sph Y (n+1))) (TopCat.of (Y × EuclideanSpace ℝ (Fin (n+1))))
          (subtypeIncl (TopCat.of (Y × EuclideanSpace ℝ (Fin (n+1)))) (Sph Y (n+1))) n
          (gen (TopCat.of ↥(Sph Y (n+1))) n τ))
      = Work.Whitney.sphPushCochain Y n ψ.1 (gen (TopCat.of ↥(Sph Y (n+1))) n τ) := by
    rw [Work.Whitney.cochain_push_apply
      (X := TopCat.of ↥(Sph Y (n+1)))
      (Z := TopCat.of (Y × EuclideanSpace ℝ (Fin (n+1))))
      (f := subtypeIncl (TopCat.of (Y × EuclideanSpace ℝ (Fin (n+1)))) (Sph Y (n+1)))
      n bt (gen (TopCat.of ↥(Sph Y (n+1))) n τ)]
    rw [show (ModuleCat.Hom.hom ((dualChainMap ℤ (TopCat.of ↥(Sph Y (n+1)))
        (TopCat.of (Y × EuclideanSpace ℝ (Fin (n+1))))
        (subtypeIncl (TopCat.of (Y × EuclideanSpace ℝ (Fin (n+1)))) (Sph Y (n+1)))).f n)) bt
        = Work.Whitney.sphPushCochain Y n ψ.1 from hbt]
    rfl
  rw [hpush, h1]
  -- The image of `τ` lies in the band (inside the sphere).
  have hsd : ∀ z, sdMap n σ z
      = ((sdMap n τ z : ↥(Sph Y (n+1))) : Y × EuclideanSpace ℝ (Fin (n+1))) := by
    intro z
    have h := sdMap_map (TopCat.of ↥(Sph Y (n+1))) (TopCat.of (Y × EuclideanSpace ℝ (Fin (n+1))))
      (subtypeIncl (TopCat.of (Y × EuclideanSpace ℝ (Fin (n+1)))) (Sph Y (n+1))) n τ
    rw [hτ] at h
    rw [h]
    rfl
  have hσim : ∀ z, sdMap n σ z ∈ Work.Whitney.BandFull Y n := by
    rw [isSmall_iff] at hσ
    rcases hσ with h | h
    · exact fun z => h (Set.mem_range_self z)
    · exfalso
      rcases Set.range_nonempty (fun z : (Delta n : TopCat) => sdMap n σ z) with ⟨y, hy⟩
      simpa using h hy
  -- The pushed simplex is small for the band `SphB` of the sphere bundle.
  have hpushσ : IsSmall (SphB Y n) (∅ : Set (Y × MSph (n+1)))
      ((TopCat.toSSet.map (Work.Whitney.sphUnflatHom Y n)).app (Opposite.op ⦋n⦌) τ) := by
    rw [isSmall_iff]
    left
    rintro y ⟨z, rfl⟩
    have h := sdMap_map (TopCat.of ↥(Sph Y (n+1))) (TopCat.of (Y × MSph (n+1)))
      (Work.Whitney.sphUnflatHom Y n) n τ
    rw [h]
    have hz : ((sdMap n τ z : ↥(Sph Y (n+1))) : Y × EuclideanSpace ℝ (Fin (n+1)))
        ∈ Work.Whitney.BandFull Y n := by
      rw [← hsd z]; exact hσim z
    exact Work.Whitney.sphUnflat_mem_SphB Y n hz
  exact Work.Whitney.sphPushCochain_gen_eq_zero Y n ψ.1 ψ.2 τ hpushσ

end Work.Whitney.tcmSuspAux
