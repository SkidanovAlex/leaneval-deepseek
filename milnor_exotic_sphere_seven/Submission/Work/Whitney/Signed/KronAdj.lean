import Mathlib
import Submission.Work.Whitney.Signed.CapFull
import Submission.Work.Cohomology.PushChain
import Submission.Work.Cohomology.relCochain_shortExact
import Submission.Work.Whitney.relCycleKron
import Submission.Work.Whitney.sdIter_smallChain_local

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

/-!
# The Kronecker pairing against a subspace

Two elementary facts about the evaluation pairing `⟨α, c⟩ = α(c)` (`Work.Cohomology.kronecker`):

* **`kronecker_subtypeIncl_push`** — a cochain `bt` on `X` whose restriction to `A ⊆ X` is `b`
  evaluates on the push-forward of a chain of `A` exactly as `b` does: this is the
  restriction/push-forward adjunction, i.e. `Work.Cohomology.cochainPullbackHom_apply` read at the
  level of `Work.Cohomology.kronecker`;
* **`isSmallChain_pushChain_of_image`** — the push-forward of an arbitrary chain along a map whose
  image lies in `S` is carried by `S`.

They are the two bookkeeping ingredients of the "model side" evaluation of the rank-one model
product formula (`Submission/Work/Whitney/Signed/ModelSide.lean`), whose cochain is defined on the
sphere bundle while the chains live in the total space.
-/

namespace Work.Whitney

open Work.Thom Work.Cohomology
open CategoryTheory AlgebraicTopology CategoryTheory.Limits
open scoped Simplicial

noncomputable section

/-- **The restriction/push-forward adjunction, pointwise.**  If the cochain `bt` on `X` restricts
to `b` on the subspace `A`, then `bt` evaluated on the push-forward of a chain of `A` is `b`
evaluated on it. -/
theorem subtypeIncl_push_apply {X : TopCat} (A : Set X) (n : ℕ)
    (bt : Cochain ℤ (ssB X) n) (b : Cochain ℤ (ssB ↥A) n)
    (h : (restr ℤ X A).f n bt = b)
    (c : (singularChains ℤ (TopCat.of ↥A)).X n) :
    bt (pushChain (TopCat.of ↥A) X (subtypeIncl X A) n c) = b c := by
  have h2 : bt.comp ((chainMap ℤ (TopCat.of ↥A) X (subtypeIncl X A)).f n).hom
      = ((b : Cochain ℤ (ssB ↥A) n) : (singularChains ℤ (TopCat.of ↥A)).X n →ₗ[ℤ] ℤ) := by
    rw [← restr_f_apply ℤ X A n bt]
    exact h
  have h3 := LinearMap.congr_fun h2 c
  rw [show (bt.comp ((chainMap ℤ (TopCat.of ↥A) X (subtypeIncl X A)).f n).hom) c
      = bt (((chainMap ℤ (TopCat.of ↥A) X (subtypeIncl X A)).f n).hom c) from rfl] at h3
  exact h3

/-- **The push-forward of a chain along a map whose image lies in `S` is carried by `S`.** -/
theorem isSmallChain_pushChain_of_image {X Y : TopCat} (f : X ⟶ Y) (S : Set Y)
    (hS : ∀ x, f x ∈ S) (n : ℕ) (c : (singularChains ℤ X).X n) :
    IsSmallChain S (∅ : Set Y) (pushChain X Y f n c) := by
  classical
  have hgen : ∀ (m : ℕ) (τ : (TopCat.toSSet.obj X) _⦋m⦌),
      IsSmallChain S (∅ : Set Y) (pushChain X Y f m (Work.Cohomology.gen X m τ)) := by
    intro m τ
    rw [pushChain_gen]
    refine isSmallChain_gen ?_
    rw [isSmall_iff]
    left
    rintro y ⟨z, rfl⟩
    rw [sdMap_map X Y f m τ]
    exact hS (sdMap m τ z)
  let Q : Submodule ℤ ((singularChains ℤ X).X n) :=
    Submodule.comap (pushChain X Y f n) (smallChainSubmodule S (∅ : Set Y) n)
  have hQ : Q = ⊤ := by
    refine mem_of_genSSet (TopCat.toSSet.obj X) n Q ?_
    intro σ
    exact hgen n σ
  have hmem : c ∈ Q := by rw [hQ]; exact Submodule.mem_top
  exact hmem


/-- **The pull-back / push-forward adjunction for the Kronecker pairing**, in the general form
(any continuous map): evaluating a pulled-back cochain on a chain of the source is evaluating the
cochain on the push-forward. -/
theorem cochain_push_apply {X Z : TopCat} (f : X ⟶ Z) (n : ℕ)
    (φ : Cochain ℤ (ssB Z) n) (c : (singularChains ℤ X).X n) :
    φ (pushChain X Z f n c)
      = cochainLM ℤ X n (((dualChainMap ℤ X Z f).f n).hom φ) c := by
  have h1 : cochainLM ℤ X n (((dualChainMap ℤ X Z f).f n).hom φ)
      = φ.comp ((chainMap ℤ X Z f).f n).hom := by
    apply LinearMap.ext
    intro x
    exact cochainPullbackHom_apply ℤ X Z f n φ x
  rw [h1]
  rfl

/-- **Smallness is monotone in the set.** -/
theorem isSmallChain_mono {X : TopCat} {S T : Set X} (hST : S ⊆ T) {n : ℕ}
    {c : (singularChains ℤ X).X n} (hc : IsSmallChain S (∅ : Set X) c) :
    IsSmallChain T (∅ : Set X) c := by
  obtain ⟨c', hc'⟩ := hc
  have hrange : ∀ y : (smallChains S (∅ : Set X)).X n,
      (smallToSing S (∅ : Set X)).f n y ∈ smallChainSubmodule T (∅ : Set X) n := by
    intro y
    let Q : Submodule ℤ ((smallChains S (∅ : Set X)).X n) :=
      Submodule.comap (((smallToSing S (∅ : Set X)).f n).hom) (smallChainSubmodule T (∅ : Set X) n)
    have hQ : Q = ⊤ := by
      refine mem_of_genSSet (smallSSet S (∅ : Set X)) n Q ?_
      intro τ
      show (smallToSing S (∅ : Set X)).f n
        (genSSet (smallSSet S (∅ : Set X)) n τ) ∈ smallChainSubmodule T (∅ : Set X) n
      rw [smallToSing_gen τ]
      refine isSmallChain_gen ?_
      rcases τ.2 with h | h
      · exact Or.inl (fun z hz => hST (h hz))
      · exact Or.inr h
    have hy : y ∈ Q := by rw [hQ]; exact Submodule.mem_top
    exact hy
  rw [← hc']
  exact hrange c'

end

end Work.Whitney
