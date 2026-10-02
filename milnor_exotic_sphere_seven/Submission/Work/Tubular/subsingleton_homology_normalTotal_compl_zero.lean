import Mathlib
import Submission.Work.Tubular.Interface
import Submission.Work.Cohomology.Chains
import Submission.Work.SphHomology.Final
import Submission.Work.Cohomology.euclidean_top_homology_vanishing

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

open CategoryTheory.Limits

set_option maxHeartbeats 1600000

namespace Work.Tubular

/-- **The complement of the zero section of the normal bundle has no homology in degree `≥ k + 8`.**

The complement of the zero section of the normal bundle `ν` of an embedded compact smooth
`8`-manifold `V ⊆ ℝ^{8+k}` is homotopy equivalent to the unit sphere bundle `S(ν)`, a closed
`(k+7)`-manifold; the sphere bundle is covered by finitely many trivialised pieces
`↥(Z.baseSet i) × S^{k-1}`, each of which has vanishing homology above `8 + (k-1) = k+7`, and the
Mayer–Vietoris induction `Work.SphHomology.isZero_relChains_sphSub_finsetUnion` gives the bound. -/
theorem subsingleton_homology_normalTotal_compl_zero {V : Work.ThomBordism.Man8} {k : ℕ}
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) (n : ℕ) (hn : k + 8 ≤ n) :
    Subsingleton ((Work.Cohomology.singularChains ℤ
      (TopCat.of {p : Work.Tubular.NormalTotal E |
        Work.Tubular.normalNorm E p ≠ 0})).homology n) := by
  rcases Nat.eq_zero_or_pos k with hk0 | hk
  · -- rank `0`: the normal space is trivial, so the space is empty
    subst hk0
    have hzero : ∀ p : Work.Tubular.NormalTotal E, Work.Tubular.normalNorm E p = 0 := by
      intro p
      have hbot : Work.Tubular.normalSpace E p.1.1 = ⊥ := by
        have hfr := Work.Tubular.finrank_normalSpace E p.1.1
        rw [show (8 + 0) - 8 = 0 from by norm_num] at hfr
        exact Submodule.finrank_eq_zero.mp hfr
      have hv : p.1.2 = 0 := by
        have hmem := p.2
        rw [hbot] at hmem
        simpa using hmem
      simp [Work.Tubular.normalNorm, hv]
    haveI : IsEmpty {p : Work.Tubular.NormalTotal E | Work.Tubular.normalNorm E p ≠ 0} :=
      ⟨fun p => p.2 (hzero p.1)⟩
    refine ModuleCat.isZero_iff_subsingleton.mp ?_
    exact Work.Cohomology.isZero_homology_of_isEmpty_aux _ n
  · -- positive rank: pass to the abstract Euclidean model of the normal bundle
    obtain ⟨ι, nu, hnu, phi, hphi⟩ := Work.Tubular.exists_euclidean_normalBundle E
    have h : IsZero ((Work.Cohomology.singularChains ℤ
        (TopCat.of (Work.Thom.SphSub nu))).homology n) :=
      Work.SphHomology.isZero_homology_sphSub hk nu hnu n (by omega)
    exact ModuleCat.isZero_iff_subsingleton.mp
      (Work.SphHomology.isZero_homology_normalTotal_compl_of_sphSub nu hnu phi hphi n h)

end Work.Tubular
