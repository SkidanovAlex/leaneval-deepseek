import Mathlib
import Submission.Work.Compact.Noncompact.relMVDefs
import Submission.Work.Compact.Noncompact.Good
import Submission.Work.Cohomology.mem_range_incl_of_smallOfV_eq

/-!
# The support submodules are compatible with intersections

For a topological space `X` and subsets `U V ⊆ X`, the submodule `rSupp X S n` of the `n`-chains
of `X` supported in `S` (the image of the inclusion `C_n(S) ⟶ C_n(X)` of singular chains) satisfies

`rSupp X U n ⊓ rSupp X V n = rSupp X (U ∩ V) n`.

One inclusion is formal (`suppS_mono`: `U ∩ V ⊆ U` and `U ∩ V ⊆ V`).  For the other one a chain `c`
supported in `U` and in `V` is written as `c = (inclChains X U) y`, and it is pushed through the
retraction `chainRetract ℤ X V n : C_n(X) ⟶ C_n(V)` (a left inverse of `inclChains X V`, see
`chainRetract_spec`).  The retract of a chain of `U` is a chain of `U ∩ V` *inside* `C_n(V)`, which
is the content of `range_inclChains_comp_chainRetract_le`; this in turn is proved on the generators
`gen (TopCat.of U) n σ` of the coproduct `C_n(U)`, using `mem_of_gen` and the explicit description
`chainRetract_gen_apply` of the retraction on a generator.

Finally the identification `relSubsetInclInter : V ∩ U → U ∩ V` turns the witness chain of
`C_n(V ∩ U)` into a chain of `C_n(U ∩ V)`, and `chainMap_relSubsetInclInter_apply` shows that it
still maps to `c` in `C_n(X)`.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open CategoryTheory AlgebraicTopology CategoryTheory.Limits
open scoped Simplicial
open Work.Cohomology

namespace Work.Compact.Noncompact

noncomputable section

/-- The identity `relSubset U V = U ∩ V` of subsets of `X`, as a continuous map of the
corresponding subspaces: `⟨x, h⟩ ↦ ⟨x, h, x.2⟩`. -/
def relSubsetInclInter {X : TopCat} (U V : Set X) :
    TopCat.of (relSubset U V) ⟶ TopCat.of ↥(U ∩ V) :=
  TopCat.ofHom ⟨fun x => ⟨((x : ↥V) : X), x.2, x.1.2⟩, by fun_prop⟩

/-- The defining property of `relSubsetInclInter`: the two ways of including `V ∩ U` into `X`
agree. -/
lemma relSubsetInclInter_comp_subtypeIncl {X : TopCat} (U V : Set X) :
    relSubsetInclInter U V ≫ subtypeIncl X (U ∩ V)
      = subtypeIncl (TopCat.of V) (relSubset U V) ≫ subtypeIncl X V := by
  ext x
  rfl

/-- `chainRetract` inverts `inclChains` on the chain level. -/
lemma chainRetract_inclChains (X : TopCat) (A : Set X) (n : ℕ)
    {c : (singularChains ℤ X).X n} {d : (singularChains ℤ (TopCat.of A)).X n}
    (h : (ModuleCat.Hom.hom ((inclChains X A).f n)) d = c) :
    (ModuleCat.Hom.hom (chainRetract ℤ X A n)) c = d := by
  have hspec : (ModuleCat.Hom.hom (chainRetract ℤ X A n)).comp
      (ModuleCat.Hom.hom ((SSet.chainComplexMap (TopCat.toSSet.map (subtypeIncl X A))
        (ModuleCat.of ℤ ℤ)).f n)) = LinearMap.id := by
    have hh := congrArg ModuleCat.Hom.hom (chainRetract_spec ℤ X A n)
    rw [ModuleCat.hom_comp, ModuleCat.hom_id] at hh
    exact hh
  have h3 : (ModuleCat.Hom.hom (chainRetract ℤ X A n))
      ((ModuleCat.Hom.hom ((inclChains X A).f n)) d) = d := by
    have hh := LinearMap.congr_fun hspec d
    rw [LinearMap.comp_apply, LinearMap.id_apply] at hh
    exact hh
  rw [← h]
  exact h3

/-- The retraction `chainRetract` on the generator of a simplex of `A`: the resulting chain of `B`
is (in the `gen`-guise) either `0` or a generator of `B` whose image in `X` agrees with the image of
the simplex of `A` we started from, hence generates a chain of `A ∩ B ⊆ B`.  This is the
generator-level input of `range_inclChains_comp_chainRetract_le`. -/
lemma chainRetract_gen_mem (X : TopCat) (A B : Set X) (n : ℕ)
    (σ : (TopCat.toSSet.obj (TopCat.of A)) _⦋n⦌) :
    (ModuleCat.Hom.hom (chainRetract ℤ X B n))
        ((ModuleCat.Hom.hom ((inclChains X A).f n)) (gen (TopCat.of A) n σ))
      ∈ rSupp (TopCat.of B) (relSubset A B) n := by
  classical
  have hA : (ModuleCat.Hom.hom ((inclChains X A).f n)) (gen (TopCat.of A) n σ)
      = gen X n ((TopCat.toSSet.map (subtypeIncl X A)).app (Opposite.op ⦋n⦌) σ) :=
    chainComplexMap_ι_apply (TopCat.toSSet.map (subtypeIncl X A)) n σ 1
  have hgen := chainRetract_gen_apply B n
    ((TopCat.toSSet.map (subtypeIncl X A)).app (Opposite.op ⦋n⦌) σ)
  rw [hA, hgen]
  by_cases hz : ∃ x : (TopCat.toSSet.obj (TopCat.of B)) _⦋n⦌,
      (TopCat.toSSet.map (subtypeIncl X B)).app (Opposite.op ⦋n⦌) x
        = (TopCat.toSSet.map (subtypeIncl X A)).app (Opposite.op ⦋n⦌) σ
  · rw [dif_pos hz]
    exact gen_mem_range_incl_of_factors A B n σ (Classical.choose hz) (Classical.choose_spec hz)
  · rw [dif_neg hz]
    exact Submodule.zero_mem _

/-- **The key retraction estimate.** If a chain of `A ⊆ X` is retracted from `X` to `B`, the
result is a chain of `A ∩ B ⊆ B`. -/
theorem range_inclChains_comp_chainRetract_le (X : TopCat) (A B : Set X) (n : ℕ) :
    LinearMap.range ((ModuleCat.Hom.hom (chainRetract ℤ X B n)).comp
        (ModuleCat.Hom.hom ((inclChains X A).f n)))
      ≤ rSupp (TopCat.of B) (relSubset A B) n := by
  classical
  have htop : (rSupp (TopCat.of B) (relSubset A B) n).comap
      ((ModuleCat.Hom.hom (chainRetract ℤ X B n)).comp
        (ModuleCat.Hom.hom ((inclChains X A).f n))) = ⊤ := by
    apply mem_of_gen (TopCat.of A) n
    intro σ
    exact Submodule.mem_comap.mpr (chainRetract_gen_mem X A B n σ)
  intro w hw
  obtain ⟨y, rfl⟩ := LinearMap.mem_range.mp hw
  exact (show y ∈ (rSupp (TopCat.of B) (relSubset A B) n).comap
      ((ModuleCat.Hom.hom (chainRetract ℤ X B n)).comp
        (ModuleCat.Hom.hom ((inclChains X A).f n))) by rw [htop]; exact Submodule.mem_top)

/-- Inserting `C_*(V) → C_*(X)` does not change the chain map `C_*(V ∩ U) → C_*(X)`: the two
inclusions `V ∩ U ⊆ U ⊆ X` and `V ∩ U ⊆ V ⊆ X` agree. -/
lemma chainMap_relSubsetInclInter_comp {X : TopCat} (U V : Set X) :
    chainMap ℤ (TopCat.of (relSubset U V)) (TopCat.of ↥(U ∩ V)) (relSubsetInclInter U V)
        ≫ inclChains X (U ∩ V)
      = inclChains (TopCat.of V) (relSubset U V) ≫ inclChains X V := by
  change chainMap ℤ (TopCat.of (relSubset U V)) (TopCat.of ↥(U ∩ V)) (relSubsetInclInter U V)
      ≫ chainMap ℤ (TopCat.of ↥(U ∩ V)) X (subtypeIncl X (U ∩ V))
    = chainMap ℤ (TopCat.of (relSubset U V)) (TopCat.of V)
        (subtypeIncl (TopCat.of V) (relSubset U V))
      ≫ chainMap ℤ (TopCat.of V) X (subtypeIncl X V)
  rw [Work.Compact.Noncompact.chainMap_comp, Work.Compact.Noncompact.chainMap_comp,
    relSubsetInclInter_comp_subtypeIncl]

/-- The elementwise form of `chainMap_relSubsetInclInter_comp`. -/
lemma chainMap_relSubsetInclInter_apply {X : TopCat} (U V : Set X) (n : ℕ)
    (z : (singularChains ℤ (TopCat.of (relSubset U V))).X n) :
    (ModuleCat.Hom.hom ((inclChains X (U ∩ V)).f n))
        ((ModuleCat.Hom.hom ((chainMap ℤ (TopCat.of (relSubset U V)) (TopCat.of ↥(U ∩ V))
          (relSubsetInclInter U V)).f n)) z)
      = (ModuleCat.Hom.hom ((inclChains X V).f n))
          ((ModuleCat.Hom.hom ((inclChains (TopCat.of V) (relSubset U V)).f n)) z) := by
  have h := congrArg (fun (φ : singularChains ℤ (TopCat.of (relSubset U V)) ⟶ singularChains ℤ X) =>
      (ModuleCat.Hom.hom (φ.f n)) z) (chainMap_relSubsetInclInter_comp U V)
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, ModuleCat.hom_comp, ModuleCat.hom_comp,
    LinearMap.comp_apply, LinearMap.comp_apply] at h
  exact h

/-- **The support submodules are compatible with intersections.** -/
theorem rSupp_inf_eq {X : TopCat} (U V : Set X) (n : ℕ) :
    Work.Compact.Noncompact.rSupp X U n ⊓ Work.Compact.Noncompact.rSupp X V n
      = Work.Compact.Noncompact.rSupp X (U ∩ V) n := by
  refine le_antisymm ?_ ?_
  · intro c hc
    rw [Submodule.mem_inf] at hc
    obtain ⟨y, hy⟩ := hc.1
    obtain ⟨x, hx⟩ := hc.2
    have hxretr : (ModuleCat.Hom.hom (chainRetract ℤ X V n)) c = x :=
      chainRetract_inclChains X V n hx
    have hρy : ((ModuleCat.Hom.hom (chainRetract ℤ X V n)).comp
        (ModuleCat.Hom.hom ((inclChains X U).f n))) y = x := by
      rw [LinearMap.comp_apply]
      exact (congrArg (fun w => (ModuleCat.Hom.hom (chainRetract ℤ X V n)) w) hy).trans hxretr
    have hxP : x ∈ rSupp (TopCat.of V) (relSubset U V) n := by
      have h1 : ((ModuleCat.Hom.hom (chainRetract ℤ X V n)).comp
          (ModuleCat.Hom.hom ((inclChains X U).f n))) y
          ∈ rSupp (TopCat.of V) (relSubset U V) n :=
        range_inclChains_comp_chainRetract_le X U V n (LinearMap.mem_range_self _ y)
      exact hρy ▸ h1
    obtain ⟨z, hz⟩ := hxP
    refine ⟨(ModuleCat.Hom.hom ((chainMap ℤ (TopCat.of (relSubset U V)) (TopCat.of ↥(U ∩ V))
      (relSubsetInclInter U V)).f n)) z, ?_⟩
    rw [chainMap_relSubsetInclInter_apply U V n z, hz, hx]
  · exact le_inf (suppS_mono Set.inter_subset_left n) (suppS_mono Set.inter_subset_right n)

end

end Work.Compact.Noncompact
