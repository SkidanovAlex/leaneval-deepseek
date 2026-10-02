import Mathlib
import Submission.Work.ThomBordism.tautologicalClassSensitivity
import Submission.Work.ThomBordism.gtdGaussCandidate
import Submission.Work.ThomBordism.padGaussFunM_eq_of_normalData

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The class `gtdUWith` does not depend on the normal datum

`Work.ThomBordism.gtdUWith E ND G hgm U` (`Submission/Work/ThomBordism/tautologicalClassSensitivity.lean`)
is the pull-back of a Thom class `U` of the tautological bundle over the Grassmannian along a bundle
map `G : ν(ND) → γ` over the (padded) Gauss map of the normal data `ND`:
it is `(relCohMap G U.τ)` transported along the Euclidean normal homeomorphism
`eucNormalHomeomorph E ND : ν(ND).TotalSpace ≃ₜ NormalTotal E` to a relative class on the pair
`(NormalTotal E, normalNonzero E)` — the class whose cap product with the collapse class is the
local degree class of the tube.

Here we prove the **datum independence** of this class: for two normal data `ND`, `ND'` of the same
embedding `E` and two bundle maps `G`, `G'` that are *both* the (plane, vector) model of the Gauss
data — `proj (G p) = padGaussFun E ND p.1` and `evalVec (G p) = padEuc k 10 (normal vector)`, and
similarly for `G'` — with *the same* Thom class `u₀`, the two relative classes agree:

`gtdUWith E ND G hgm u₀ = gtdUWith E ND' G' hgm' u₀`.

The mathematical content is the geomdetric fact that `eucNormalHomeomorph` identifies the two models
of the normal bundle *fibrewise over `V`* (both insert the same normal vector, in the orthonormal
frame of the respective datum), while the (plane, vector) data of `G` and of the transport of `G'`
along that identification agree:

* the *plane* agrees because the padded `σ`-corrected Gauss map is independent of the normal datum
  (`Work.ThomBordism.padGaussFunM_eq_of_normalData`, generalised here to `padGaussFun` and to all
  `k`, including `k = 0`, where it is a `Subsingleton` statement), and the padded Gauss map is a
  function of `V` alone;
* the *vector* agrees because the normal vector read in the frame of `ND'` and transported back is
  the normal vector of `ND` (`bundleToNormal_normalToBundle`);
* the pair `(plane, vector)` *determines* a point of the total space of the tautological bundle
  (`Work.ThomBordism.Grassmann.evalVec_injective_of_proj_eq`).

So the transfer map `T = eucNormalHomeomorph E ND' ∘ normalToBundle` satisfies `G = G' ∘ T` *as
functions*, which is the input of the functoriality of `relCohMap` that gives the statement. -/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.ThomBordism

open Work.ThomBordism.PontryaginThom Work.Tubular

noncomputable section

/-- **`padGaussFun` is the `10`-padding of the general formula `padGaussFunM`.**  (The two were
written independently: `padGaussFun` in `_gtd/P3` with the explicit padding `padIsom`, and
`padGaussFunM` in `padGaussFunM` with `padIsomM`.) -/
theorem padGaussFun_eq_padGaussFunM {V : Work.ThomBordism.Man8} {k : ℕ}
    (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e) (x : V.pt) :
    Grassmann.padGaussFun E ND x = padGaussFunM E ND 10 (by norm_num) x := by
  rw [Grassmann.padGaussFun_eq E ND (ND.D.indexAt x) (ND.D.mem_baseSet_at x),
      padGaussFunM_eq E ND 10 (by norm_num) x]
  congr 1

/-- **The padded Gauss map of an embedding does not depend on the normal datum — all ranks.**  This
is `Work.ThomBordism.padGaussFunM_eq_of_normalData` transported to `padGaussFun`, together with the
rank-zero case, where `G̃r_0(ℝ^{10})` is a subsingleton and the statement is trivial. -/
theorem padGaussFun_eq_of_normalData {V : Work.ThomBordism.Man8} {k : ℕ}
    (E : EmbeddingData V (8 + k)) (ND ND' : NormalData V k E.e) (x : V.pt) :
    Grassmann.padGaussFun E ND x = Grassmann.padGaussFun E ND' x := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    exact @Subsingleton.elim _ (Grassmann.subsingleton_OG_zero 10) _ _
  · rw [padGaussFun_eq_padGaussFunM E ND x, padGaussFun_eq_padGaussFunM E ND' x]
    exact padGaussFunM_eq_of_normalData hk E ND ND' 10 (by norm_num) x

/-- **`gtdUWith` does not depend on the normal datum** (nor on the bundle map, which is pinned by the
Gauss data).  See the module docstring. -/
theorem gtdUWith_eq_of_normalData {V : Work.ThomBordism.Man8} {k : ℕ}
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    (ND ND' : Work.ThomBordism.PontryaginThom.NormalData V k E.e)
    (G : C((Work.Tubular.normalBundle E ND).TotalSpace,
      (Work.ThomBordism.Grassmann.tautologicalBundle k 10).TotalSpace))
    (hgm : ∀ p ∈ Work.Thom.zeroComplement (Work.Tubular.normalBundle E ND),
      G p ∈ Work.Thom.zeroComplement (Work.ThomBordism.Grassmann.tautologicalBundle k 10))
    (hbp : ∀ p, (Work.ThomBordism.Grassmann.tautologicalBundle k 10).proj (G p)
      = Work.ThomBordism.Grassmann.padGaussFun E ND p.1)
    (hvec : ∀ p, Work.ThomBordism.Grassmann.evalVec (G p)
      = Work.PTGeometric.padEuc k 10 (by norm_num)
          (Work.Tubular.NormalTotal.vec (Work.Tubular.bundleToNormal E ND p)))
    (G' : C((Work.Tubular.normalBundle E ND').TotalSpace,
      (Work.ThomBordism.Grassmann.tautologicalBundle k 10).TotalSpace))
    (hgm' : ∀ p ∈ Work.Thom.zeroComplement (Work.Tubular.normalBundle E ND'),
      G' p ∈ Work.Thom.zeroComplement (Work.ThomBordism.Grassmann.tautologicalBundle k 10))
    (hbp' : ∀ p, (Work.ThomBordism.Grassmann.tautologicalBundle k 10).proj (G' p)
      = Work.ThomBordism.Grassmann.padGaussFun E ND' p.1)
    (hvec' : ∀ p, Work.ThomBordism.Grassmann.evalVec (G' p)
      = Work.PTGeometric.padEuc k 10 (by norm_num)
          (Work.Tubular.NormalTotal.vec (Work.Tubular.bundleToNormal E ND' p)))
    (u₀ : Work.Thom.ThomClass (Work.ThomBordism.Grassmann.tautologicalBundle k 10) k) :
    Work.ThomBordism.gtdUWith E ND G hgm u₀
      = Work.ThomBordism.gtdUWith E ND' G' hgm' u₀ := by
  -- the two Euclidean normal homeomorphisms (as continuous maps) and the transfer map
  let h : C(Work.Tubular.NormalTotal E, (Work.Tubular.normalBundle E ND).TotalSpace) :=
    ((Work.Tubular.eucNormalHomeomorph E ND).symm :
      C(Work.Tubular.NormalTotal E, (Work.Tubular.normalBundle E ND).TotalSpace))
  let h' : C(Work.Tubular.NormalTotal E, (Work.Tubular.normalBundle E ND').TotalSpace) :=
    ((Work.Tubular.eucNormalHomeomorph E ND').symm :
      C(Work.Tubular.NormalTotal E, (Work.Tubular.normalBundle E ND').TotalSpace))
  let T_map : C((Work.Tubular.normalBundle E ND).TotalSpace,
      (Work.Tubular.normalBundle E ND').TotalSpace) :=
    h'.comp ((Work.Tubular.eucNormalHomeomorph E ND) :
      C((Work.Tubular.normalBundle E ND).TotalSpace, Work.Tubular.NormalTotal E))
  let A : Set (Work.Tubular.normalBundle E ND).TotalSpace :=
    Work.Thom.zeroComplement (Work.Tubular.normalBundle E ND)
  let A' : Set (Work.Tubular.normalBundle E ND').TotalSpace :=
    Work.Thom.zeroComplement (Work.Tubular.normalBundle E ND')
  let B : Set (Work.ThomBordism.Grassmann.tautologicalBundle k 10).TotalSpace :=
    Work.Thom.zeroComplement (Work.ThomBordism.Grassmann.tautologicalBundle k 10)
  let Nz : Set (Work.Tubular.NormalTotal E) := Work.Tubular.normalNonzero E
  have h'_apply : ∀ z : Work.Tubular.NormalTotal E, h' z = Work.Tubular.normalToBundle E ND' z :=
    fun z => gtdEucNormalHomeomorph_symm_apply E ND' z
  have h_apply : ∀ z : Work.Tubular.NormalTotal E, h z = Work.Tubular.normalToBundle E ND z :=
    fun z => gtdEucNormalHomeomorph_symm_apply E ND z
  have T_map_apply : ∀ p, T_map p = Work.Tubular.normalToBundle E ND'
      (Work.Tubular.bundleToNormal E ND p) := by
    intro p
    show h' ((Work.Tubular.eucNormalHomeomorph E ND) p) = _
    rw [h'_apply, Work.Tubular.eucNormalHomeomorph_apply]
  have T_proj : ∀ p, (T_map p).1 = p.1 := fun p => by rw [T_map_apply p]; rfl
  have T_bundle : ∀ p, Work.Tubular.bundleToNormal E ND' (T_map p)
      = Work.Tubular.bundleToNormal E ND p := by
    intro p
    rw [T_map_apply p]
    exact Work.Tubular.bundleToNormal_normalToBundle E ND' (Work.Tubular.bundleToNormal E ND p)
  -- the transfer map carries the nonzero complement to the nonzero complement
  have hT : ∀ p ∈ A, T_map p ∈ A' := by
    have hfn : ∀ p, Work.Thom.fibreNorm (Work.Tubular.normalBundle E ND') (T_map p)
        = Work.Thom.fibreNorm (Work.Tubular.normalBundle E ND) p := by
      intro p
      rw [Work.Tubular.fibreNorm_eq_normalNorm, T_bundle p,
        ← Work.Tubular.fibreNorm_eq_normalNorm]
    intro p hp
    rw [Work.Thom.mem_zeroComplement] at hp ⊢
    intro h0
    have hp' : Work.Thom.fibreNorm (Work.Tubular.normalBundle E ND) p ≠ 0 := by
      rw [Work.Thom.fibreNorm]
      exact fun hh => hp (norm_eq_zero.mp hh)
    refine hp' ?_
    rw [← hfn p, Work.Thom.fibreNorm, h0, norm_zero]
  -- the bundle map is pinned by the Gauss data, so `G = G' ∘ T`
  have hG : G = G'.comp T_map := by
    apply ContinuousMap.ext
    intro p
    exact Work.ThomBordism.Grassmann.evalVec_injective_of_proj_eq
      (p := G p) (q := G' (T_map p)) (by
        change VectorBundleCore.proj (Work.ThomBordism.Grassmann.tautologicalBundle k 10) (G p)
          = VectorBundleCore.proj (Work.ThomBordism.Grassmann.tautologicalBundle k 10)
              (G' (T_map p))
        rw [hbp p, hbp' (T_map p), T_proj p]
        exact padGaussFun_eq_of_normalData E ND ND' p.1) (by
        show Work.ThomBordism.Grassmann.evalVec (G p)
          = Work.ThomBordism.Grassmann.evalVec (G' (T_map p))
        rw [hvec p, hvec' (T_map p), T_bundle p])
  -- and the transfer map intertwines the two Euclidean normal homeomorphisms
  have hcomp : T_map.comp h = h' := by
    apply ContinuousMap.ext
    intro y
    show h' ((Work.Tubular.eucNormalHomeomorph E ND) (h y)) = h' y
    rw [h_apply y, Work.Tubular.eucNormalHomeomorph_apply,
      Work.Tubular.bundleToNormal_normalToBundle]
  have hgf : ∀ p ∈ A, G' (T_map p) ∈ B := fun p hp => hgm' (T_map p) (hT p hp)
  -- functoriality of the pull-back, in the two forms needed
  have hmap1 : Work.Thom.relCohMap G A B hgm ℤ k
      = CategoryTheory.CategoryStruct.comp (Work.Thom.relCohMap G' A' B hgm' ℤ k)
          (Work.Thom.relCohMap T_map A A' hT ℤ k) :=
    (Work.Thom.relCohMap_congr' A B hG hgm hgf ℤ k).trans
      (Work.Thom.relCohMap_comp A A' B T_map G' hT hgm' hgf ℤ k).symm
  have hrel1 : (Work.Thom.relCohMap G A B hgm ℤ k).hom u₀.τ
      = (Work.Thom.relCohMap T_map A A' hT ℤ k).hom
          ((Work.Thom.relCohMap G' A' B hgm' ℤ k).hom u₀.τ) := by
    have := congrArg (fun φ => φ.hom u₀.τ) hmap1
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using this
  have hmap2 : CategoryTheory.CategoryStruct.comp (Work.Thom.relCohMap T_map A A' hT ℤ k)
        (Work.Thom.relCohMap h Nz A (gtd_mem E ND) ℤ k)
      = Work.Thom.relCohMap h' Nz A' (gtd_mem E ND') ℤ k :=
    (Work.Thom.relCohMap_comp Nz A A' h T_map (gtd_mem E ND) hT
      (fun y hy => hT (h y) (gtd_mem E ND y hy)) ℤ k).trans
      (Work.Thom.relCohMap_congr' Nz A' hcomp _ (gtd_mem E ND') ℤ k)
  have hrel2 : (Work.Thom.relCohMap h Nz A (gtd_mem E ND) ℤ k).hom
        ((Work.Thom.relCohMap T_map A A' hT ℤ k).hom
          ((Work.Thom.relCohMap G' A' B hgm' ℤ k).hom u₀.τ))
      = (Work.Thom.relCohMap h' Nz A' (gtd_mem E ND') ℤ k).hom
          ((Work.Thom.relCohMap G' A' B hgm' ℤ k).hom u₀.τ) := by
    have := congrArg (fun φ => φ.hom ((Work.Thom.relCohMap G' A' B hgm' ℤ k).hom u₀.τ)) hmap2
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using this
  -- unfold the two sides and rewrite
  show (Work.Thom.relCohMap h Nz A (gtd_mem E ND) ℤ k).hom
      ((Work.Thom.relCohMap G A B hgm ℤ k).hom u₀.τ)
    = (Work.Thom.relCohMap h' Nz A' (gtd_mem E ND') ℤ k).hom
      ((Work.Thom.relCohMap G' A' B hgm' ℤ k).hom u₀.τ)
  rw [hrel1, hrel2]

end

end Work.ThomBordism
