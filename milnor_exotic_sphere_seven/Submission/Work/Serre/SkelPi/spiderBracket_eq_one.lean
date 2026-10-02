import Mathlib
import Submission.Work.Serre.SkelPi.Basic
import Submission.Work.Serre.SkelPi.spiderContraction

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The spider bracket of a path in the spider is null-homotopic

The product `(legOf p) · P · (legOf q)⁻¹` of the legs of the endpoints of a path `P` lying in the
spider is a loop at the base point; since the spider is contractible to the base point
(`Work.Serre.SkelPi.spiderContraction`), this loop is null-homotopic.
-/

open scoped Topology unitInterval

namespace Work.Serre.SkelPi

noncomputable section

theorem Path_trans_mem {Z : Type} [TopologicalSpace Z] {a b c : Z} {S : Set Z}
    (p : Path a b) (q : Path b c) (hp : ∀ s, p s ∈ S) (hq : ∀ s, q s ∈ S) :
    ∀ s, (p.trans q) s ∈ S := by
  intro s
  rw [Path.trans_apply]
  split_ifs with h
  · exact hp _
  · exact hq _

theorem Path_symm_mem {Z : Type} [TopologicalSpace Z] {a b : Z} {S : Set Z}
    (p : Path a b) (hp : ∀ s, p s ∈ S) : ∀ s, p.symm s ∈ S := by
  intro s
  exact hp _

/-- **The spider bracket is null-homotopic.** -/
theorem spiderBracket_eq_one (X : Type) [TopologicalSpace X] (pt : X)
    {p q : Skel X pt} (hp : p ∈ spider X pt) (hq : q ∈ spider X pt)
    (P : Path p q) (hP : ∀ t, P t ∈ spider X pt) :
    ((Path.Homotopic.Quotient.mk (legOf X pt p)).trans (Path.Homotopic.Quotient.mk P)).trans
      (Path.Homotopic.Quotient.mk (legOf X pt q)).symm
      = Path.Homotopic.Quotient.refl (base X pt) := by
  obtain ⟨H, hH0, hH1, hb, -⟩ := spiderContraction X pt
  set L : Path (base X pt) (base X pt) :=
    (legOf X pt p).trans P |>.trans (legOf X pt q).symm with hLdef
  have hLmem : ∀ s, L s ∈ spider X pt :=
    Path_trans_mem _ _
      (Path_trans_mem _ _ (fun s => legOf_mem_spider X pt hp s) (fun s => hP s))
      (Path_symm_mem _ (fun s => legOf_mem_spider X pt hq s))
  have hkey : L.Homotopic (Path.refl (base X pt)) := by
    refine ⟨?_⟩
    refine
      { toFun := fun r => H (⟨L r.2, hLmem r.2⟩, r.1)
        continuous_toFun := ?_
        map_zero_left := ?_
        map_one_left := ?_
        prop' := ?_ }
    · exact H.continuous.comp (Continuous.prodMk
        (Continuous.subtype_mk (L.continuous.comp continuous_snd) (fun x => hLmem x.2))
        continuous_fst)
    · intro s
      exact hH0 _
    · intro s
      exact hH1 _
    · intro t s hs
      rcases hs with hs | hs
      · rw [hs]
        show H (⟨L (0 : unitInterval), hLmem (0 : unitInterval)⟩, t) = L (0 : unitInterval)
        rw [show (⟨L (0 : unitInterval), hLmem (0 : unitInterval)⟩ : ↥(spider X pt))
            = ⟨base X pt, base_mem_spider X pt⟩ from Subtype.ext L.source, L.source]
        exact hb t
      · rw [Set.mem_singleton_iff] at hs
        rw [hs]
        show H (⟨L (1 : unitInterval), hLmem (1 : unitInterval)⟩, t) = L (1 : unitInterval)
        rw [show (⟨L (1 : unitInterval), hLmem (1 : unitInterval)⟩ : ↥(spider X pt))
            = ⟨base X pt, base_mem_spider X pt⟩ from Subtype.ext L.target, L.target]
        exact hb t
  have hgoal : ((Path.Homotopic.Quotient.mk (legOf X pt p)).trans
        (Path.Homotopic.Quotient.mk P)).trans
        (Path.Homotopic.Quotient.mk (legOf X pt q)).symm
      = Path.Homotopic.Quotient.mk L := by
    rw [← Path.Homotopic.Quotient.mk_symm, ← Path.Homotopic.Quotient.mk_trans,
      ← Path.Homotopic.Quotient.mk_trans]
  rw [hgoal, Path.Homotopic.Quotient.eq.mpr hkey]
  exact Path.Homotopic.Quotient.mk_refl (base X pt)

end

end Work.Serre.SkelPi
