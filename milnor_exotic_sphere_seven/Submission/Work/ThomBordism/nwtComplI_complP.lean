import Mathlib
import Submission.Work.ThomBordism.nwtDefs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

/-!
# The complement of the normal bundle of an embedding: `I ∘ P = orthInj`

`nwtDefs.lean` records the projection `complP` and the insertion `complI` of the normal bundle of an
embedding `E : EmbeddingData V (8+k)` with normal data `ND`, in the coordinate spaces
`Fin (8+k) → ℝ` and `Fin k → ℝ`.  Here we prove the identity that identifies the composition
`complI ∘ complP` with the orthogonal projection onto the normal space, read in the coordinates of
the tangent frame of the chart `coverChart i`:

`complI E ND i x (complP E ND i x u) = orthInj (frame E.e (coverChart i) x) u`.

The proof reduces to the ambient statement `insCLM ∘ readCLM = orthInj` (in coordinates): the
orthonormal frame `orthFrame` used to build `insCLM`/`readCLM` spans exactly the normal space
`ν_x = (tangentSpace E x)ᗮ`, so `insCLM ∘ readCLM` is the orthogonal projection onto `ν_x`; and
`orthInj (frame …)` is the matrix orthogonal projection onto the *same* space
(`range_orthInj_frame`).
-/

namespace Work.ThomBordism

open Work.ThomBordism.PontryaginThom

noncomputable section

variable {V : Work.ThomBordism.Man8} {k : ℕ}

/-- **`insCLM ∘ readCLM` is the orthogonal projection onto the normal space**, read in the
coordinates of the tangent frame of the chart: it agrees with the matrix orthogonal insertion
`orthInj (frame E.e (coverChart i) x)`. -/
theorem insCLM_readCLM_eq_orthInj (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e)
    (i : CoverIdx V k) {x : V.pt} (hx : x ∈ ND.D.baseSet i) (w : Euc (8 + k)) :
    Work.Tubular.insCLM E ND i x (Work.Tubular.readCLM E ND i x w)
      = funToEuc (8 + k) (orthInj (frame E.e (coverChart i) x) (eucToFun (8 + k) w)) := by
  have hsrc : x ∈ (coverChart i).1.source := ND.baseSet_sub i.1 i.2 x hx
  have hLI : LinearIndependent ℝ (frame E.e (coverChart i) x) :=
    Work.Tubular.frame_linearIndependent_at E (coverChart i) hsrc
  have hQmem : Work.Tubular.insCLM E ND i x (Work.Tubular.readCLM E ND i x w)
      ∈ Work.Tubular.normalSpace E x := Work.Tubular.insCLM_mem E ND i hx _
  refine Work.Tubular.eucToFun_injective (8 + k) ?_
  rw [eucToFun_funToEuc]
  -- `Q - w` is a tangent vector: it is orthogonal to the orthonormal frame of the normal space
  have hsub : Work.Tubular.insCLM E ND i x (Work.Tubular.readCLM E ND i x w) - w
      ∈ Work.Tubular.tangentSpace E x := by
    have hmem : Work.Tubular.insCLM E ND i x (Work.Tubular.readCLM E ND i x w) - w
        ∈ (Work.Tubular.normalSpace E x)ᗮ := by
      rw [Submodule.mem_orthogonal]
      intro u hu
      rw [← Work.Tubular.span_orthFrame E ND i hx] at hu
      refine Submodule.span_induction
        (p := fun u _ => inner ℝ u
          (Work.Tubular.insCLM E ND i x (Work.Tubular.readCLM E ND i x w) - w) = 0)
        ?_ ?_ ?_ ?_ hu
      · rintro u ⟨l, rfl⟩
        have hexp : Work.Tubular.insCLM E ND i x (Work.Tubular.readCLM E ND i x w)
            = ∑ m : Fin k, inner ℝ (Work.Tubular.orthFrame E ND i x m) w
                • Work.Tubular.orthFrame E ND i x m := by
          rw [Work.Tubular.insCLM_apply]
          refine Finset.sum_congr rfl fun m _ => ?_
          rw [Work.Tubular.readCLM_apply, eucToFun_funToEuc]
        rw [hexp, inner_sub_right]
        have h1 : inner ℝ (Work.Tubular.orthFrame E ND i x l)
            (∑ m : Fin k, inner ℝ (Work.Tubular.orthFrame E ND i x m) w
              • Work.Tubular.orthFrame E ND i x m)
            = inner ℝ (Work.Tubular.orthFrame E ND i x l) w :=
          (Work.Tubular.orthFrame_orthonormal E ND i hx).inner_right_fintype
            (fun m : Fin k => inner ℝ (Work.Tubular.orthFrame E ND i x m) w) l
        rw [h1, sub_self]
      · rw [inner_zero_left]
      · intro a b ha hb iha ihb
        rw [inner_add_left, iha, ihb, add_zero]
      · intro c a ha iha
        rw [inner_smul_left, iha, mul_zero]
    have hmem' : Work.Tubular.insCLM E ND i x (Work.Tubular.readCLM E ND i x w) - w
        ∈ ((Work.Tubular.tangentSpace E x)ᗮ)ᗮ := by
      simpa only [Work.Tubular.normalSpace] using hmem
    rwa [Submodule.orthogonal_orthogonal (Work.Tubular.tangentSpace E x)] at hmem'
  -- the insertion is fixed by the orthogonal projection onto the normal space
  have hfix : orthInj (frame E.e (coverChart i) x)
      (eucToFun (8 + k) (Work.Tubular.insCLM E ND i x (Work.Tubular.readCLM E ND i x w)))
      = eucToFun (8 + k)
          (Work.Tubular.insCLM E ND i x (Work.Tubular.readCLM E ND i x w)) := by
    have h3 : eucToFun (8 + k)
          (Work.Tubular.insCLM E ND i x (Work.Tubular.readCLM E ND i x w))
        ∈ (orthInj (frame E.e (coverChart i) x)).range := by
      rw [Work.Tubular.range_orthInj_frame E (coverChart i) hsrc]
      exact Submodule.mem_map_of_mem hQmem
    obtain ⟨y, hy⟩ := LinearMap.mem_range.mp h3
    rw [← hy, Work.Tubular.orthInj_idem (frame E.e (coverChart i) x) hLI y]
  -- the difference to `orthInj u` lies in the kernel of the orthogonal projection
  have hker : eucToFun (8 + k)
        (Work.Tubular.insCLM E ND i x (Work.Tubular.readCLM E ND i x w))
      - orthInj (frame E.e (coverChart i) x) (eucToFun (8 + k) w)
      ∈ (orthInj (frame E.e (coverChart i) x)).ker := by
    rw [Work.ThomBordism.PontryaginThom.ker_orthInj (frame E.e (coverChart i) x) hLI]
    have h1 : eucToFun (8 + k)
          (Work.Tubular.insCLM E ND i x (Work.Tubular.readCLM E ND i x w) - w)
        = eucToFun (8 + k) (Work.Tubular.insCLM E ND i x (Work.Tubular.readCLM E ND i x w))
          - eucToFun (8 + k) w := map_sub _ _ _
    have h2 : orthInj (frame E.e (coverChart i) x) (eucToFun (8 + k) w)
        = eucToFun (8 + k) w
          - orthProj (frame E.e (coverChart i) x) (eucToFun (8 + k) w) := by
      simp only [orthInj, LinearMap.sub_apply, LinearMap.id_apply]
    have hdecomp : eucToFun (8 + k)
          (Work.Tubular.insCLM E ND i x (Work.Tubular.readCLM E ND i x w))
        - orthInj (frame E.e (coverChart i) x) (eucToFun (8 + k) w)
        = eucToFun (8 + k)
            (Work.Tubular.insCLM E ND i x (Work.Tubular.readCLM E ND i x w) - w)
          + orthProj (frame E.e (coverChart i) x) (eucToFun (8 + k) w) := by
      rw [h1, h2]
      abel
    rw [hdecomp]
    refine (Work.ThomBordism.Grassmann.coeffMap (frame E.e (coverChart i) x)).range.add_mem ?_ ?_
    · rw [Work.Tubular.range_coeffMap_frame_eq_tangentSpace E (coverChart i) hsrc]
      exact Submodule.mem_map_of_mem hsub
    · exact Work.ThomBordism.PontryaginThom.range_orthProj_le (frame E.e (coverChart i) x)
        ⟨eucToFun (8 + k) w, rfl⟩
  have hd : eucToFun (8 + k)
        (Work.Tubular.insCLM E ND i x (Work.Tubular.readCLM E ND i x w))
      - orthInj (frame E.e (coverChart i) x) (eucToFun (8 + k) w)
      = orthInj (frame E.e (coverChart i) x)
          (eucToFun (8 + k) (Work.Tubular.insCLM E ND i x (Work.Tubular.readCLM E ND i x w))
            - orthInj (frame E.e (coverChart i) x) (eucToFun (8 + k) w)) := by
    rw [map_sub, hfix, Work.Tubular.orthInj_idem (frame E.e (coverChart i) x) hLI
      (eucToFun (8 + k) w)]
  exact sub_eq_zero.mp (hd.trans (LinearMap.mem_ker.mp hker))

/-- **The composite `complI ∘ complP` of the normal bundle is the orthogonal insertion** of the
tangent frame of the chart. -/
theorem nwtComplI_complP {V : Work.ThomBordism.Man8} {k : ℕ}
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    (ND : Work.ThomBordism.PontryaginThom.NormalData V k E.e)
    (i : Work.ThomBordism.PontryaginThom.CoverIdx V k) {x : V.pt}
    (hx : x ∈ ND.D.baseSet i) (u : Fin (8 + k) → ℝ) :
    Work.ThomBordism.complI E ND i x (Work.ThomBordism.complP E ND i x u)
      = Work.ThomBordism.PontryaginThom.orthInj
          (Work.ThomBordism.PontryaginThom.frame E.e
            (Work.ThomBordism.PontryaginThom.coverChart i) x) u := by
  rw [complP_apply_of_mem E ND i hx, complI_apply_of_mem E ND i hx, funToEuc_eucToFun,
    insCLM_readCLM_eq_orthInj E ND i hx]
  rw [eucToFun_funToEuc, eucToFun_funToEuc]

end

end Work.ThomBordism
