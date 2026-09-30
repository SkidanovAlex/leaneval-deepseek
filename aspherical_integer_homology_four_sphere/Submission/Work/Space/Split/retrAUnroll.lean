import Mathlib
import Submission.Work.Space.Split
import Submission.Work.Space.Split.retrABasic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open Set Topology Function Filter
open scoped Topology
open unitInterval

namespace Work.Space

theorem isOpen_SS : IsOpen {p : SquarePt | 1/4 < sqNorm p} :=
  isOpen_lt continuous_const continuous_sqNorm

theorem isOpenMap_subtype_val_SS : IsOpenMap (Subtype.val : SS → SquarePt) :=
  isOpen_SS.isOpenMap_subtype_val

end Work.Space

namespace Work.Space.Assembly

variable (a : Assembly)

/-- The unrolled outer shell `⊔_v (1/4,1] × T_v`. -/
abbrev ShellY : Type _ := Σ v : Cusp, SS × a.Torus v

/-- The "unrolled" model of `A`: `M̄` together with the outer shells. -/
abbrev U : Type _ := a.Mbar ⊕ a.ShellY

/-- The inclusion of the unrolled shell into the filling pieces. -/
def incShell (y : a.ShellY) : a.Y := ⟨y.1, (y.2.1.1, y.2.2)⟩

theorem continuous_incShell : Continuous a.incShell := by
  rw [continuous_sigma_iff]
  intro v
  exact continuous_sigmaMk.comp
    ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)

theorem incShell_mem_outer (y : a.ShellY) : a.incShell y ∈ outerShell a.Torus := by
  obtain ⟨v, ⟨⟨p, hp⟩, t⟩⟩ := y
  exact hp

/-- The canonical surjection `M̄ ⊔ ⊔_v (1/4,1] × T_v → A`. -/
def qA (x : a.U) : {z : a.Mhat // z ∈ a.Aset} :=
  Sum.elim (fun m => ⟨a.incMbar m, a.incMbar_mem_Aset m⟩)
    (fun y => ⟨a.incY (a.incShell y), a.incY_mem_Aset_iff.mpr (a.incShell_mem_outer y)⟩) x

theorem continuous_qA : Continuous a.qA := by
  rw [continuous_sum_dom]
  refine ⟨?_, ?_⟩
  · exact Continuous.subtype_mk a.continuous_incMbar fun m => a.incMbar_mem_Aset m
  · exact Continuous.subtype_mk (a.continuous_incY.comp a.continuous_incShell)
      fun y => a.incY_mem_Aset_iff.mpr (a.incShell_mem_outer y)

theorem surjective_qA : Function.Surjective a.qA := by
  rintro ⟨z, hz⟩
  change z ∈ (range a.incMbar ∪ a.incY '' outerShell a.Torus) at hz
  rcases hz with ⟨m, hm⟩ | ⟨⟨v, p, t⟩, hq, hzq⟩
  · exact ⟨(Sum.inl m : a.U), Subtype.ext hm⟩
  · refine ⟨(Sum.inr ⟨v, (⟨p, hq⟩, t)⟩ : a.U), Subtype.ext ?_⟩
    show a.incY (a.incShell ⟨v, (⟨p, hq⟩, t)⟩) = z
    rw [← hzq]
    rfl

/-- The image of a subset of `A` under the inclusion is open iff the subset is. -/
theorem isOpen_subtype_image_iff {s : Set {z : a.Mhat // z ∈ a.Aset}} :
    IsOpen (Subtype.val '' s : Set a.Mhat) ↔ IsOpen s := by
  constructor
  · intro h
    have hpre : Subtype.val ⁻¹' (Subtype.val '' s : Set a.Mhat) = s := by
      ext z
      exact ⟨fun ⟨z', hz', hz'z⟩ => Subtype.val_injective hz'z ▸ hz',
        fun hz => ⟨z, hz, rfl⟩⟩
    rw [← hpre]
    exact h.preimage continuous_subtype_val
  · intro h
    exact a.Aset.is_open'.isOpenMap_subtype_val _ h

/-- A point of `A` coming from the filling pieces has `1/4 < ‖p‖∞`. -/
theorem sqNorm_gt_of_incW_mem_Aset {v : Cusp} {p : SquarePt} {t : a.Torus v}
    (h : a.incW v (p, t) ∈ (a.Aset : Set a.Mhat)) : 1/4 < sqNorm p :=
  a.incY_mem_Aset_iff.mp h

theorem qA_inl_mem_iff {s : Set {z : a.Mhat // z ∈ a.Aset}} (m : a.Mbar) :
    a.qA (Sum.inl m) ∈ s ↔ a.incMbar m ∈ (Subtype.val '' s : Set a.Mhat) :=
  ⟨fun h => ⟨a.qA (Sum.inl m), h, rfl⟩,
   fun ⟨x, hx, hval⟩ => by
     have hx' : x = a.qA (Sum.inl m) := Subtype.ext (by simpa [qA] using hval)
     rwa [← hx']⟩

theorem qA_inr_mem_iff {s : Set {z : a.Mhat // z ∈ a.Aset}} {v : Cusp} {p : SquarePt}
    (hp : 1/4 < sqNorm p) (t : a.Torus v) :
    a.qA (Sum.inr ⟨v, (⟨p, hp⟩, t)⟩) ∈ s ↔
      a.incW v (p, t) ∈ (Subtype.val '' s : Set a.Mhat) :=
  ⟨fun h => ⟨a.qA (Sum.inr ⟨v, (⟨p, hp⟩, t)⟩), h, rfl⟩,
   fun ⟨x, hx, hval⟩ => by
     have hx' : x = a.qA (Sum.inr ⟨v, (⟨p, hp⟩, t)⟩) :=
       Subtype.ext (by simpa [qA, incShell] using hval)
     rwa [← hx']⟩

theorem image_val_prodMap_preimage {v : Cusp} {V : Set (SquarePt × a.Torus v)}
    (hV : V ⊆ ({p : SquarePt | 1/4 < sqNorm p} ×ˢ (univ : Set (a.Torus v)))) :
    (Prod.map (Subtype.val : SS → SquarePt) id) ''
        ((Prod.map (Subtype.val : SS → SquarePt) id) ⁻¹' V) = V :=
  Set.image_preimage_eq_of_subset fun x hx => ⟨(⟨x.1, (hV hx).1⟩, x.2), rfl⟩

theorem isOpen_sigma_preimage {v : Cusp} {S : Set (SquarePt × a.Torus v)}
    (h : IsOpen ((Prod.map (Subtype.val : SS → SquarePt) id) ⁻¹' S))
    (hS : S ⊆ ({p : SquarePt | 1/4 < sqNorm p} ×ˢ (univ : Set (a.Torus v)))) :
    IsOpen S := by
  have hj : IsOpenMap (Prod.map (Subtype.val : SS → SquarePt) id :
      SS × a.Torus v → SquarePt × a.Torus v) :=
    isOpenMap_subtype_val_SS.prodMap IsOpenMap.id
  have h2 : IsOpen ((Prod.map (Subtype.val : SS → SquarePt) id) ''
      ((Prod.map (Subtype.val : SS → SquarePt) id) ⁻¹' S)) := hj _ h
  rwa [image_val_prodMap_preimage a hS] at h2

theorem isQuotientMap_qA : IsQuotientMap a.qA := by
  refine ⟨IsCoinducing.of_isOpen_preimage_iff_isOpen ?_, a.surjective_qA⟩
  intro s
  refine ⟨fun hs => ?_, fun hs => hs.preimage a.continuous_qA⟩
  set s' : Set a.Mhat := Subtype.val '' s with hs'_def
  have key : IsOpen (a.mkq ⁻¹' s') := by
    rw [isOpen_sum_iff]
    refine ⟨?_, ?_⟩
    · have h := (isOpen_sum_iff.mp hs).1
      have heq : Sum.inl ⁻¹' a.qA ⁻¹' s = Sum.inl ⁻¹' a.mkq ⁻¹' s' := by
        ext m
        simp only [Set.mem_preimage]
        exact qA_inl_mem_iff a m
      rwa [heq] at h
    · rw [isOpen_sigma_iff]
      intro v
      have h := (isOpen_sum_iff.mp hs).2
      rw [isOpen_sigma_iff] at h
      have hv := h v
      change IsOpen {x : SquarePt × a.Torus v | a.incY (⟨v, x⟩ : a.Y) ∈ s'}
      refine isOpen_sigma_preimage a ?_ ?_
      · have heq : (Prod.map (Subtype.val : SS → SquarePt) id) ⁻¹'
            {x : SquarePt × a.Torus v | a.incY (⟨v, x⟩ : a.Y) ∈ s'} =
            Sigma.mk v ⁻¹' Sum.inr ⁻¹' a.qA ⁻¹' s := by
          ext x
          simp only [Set.mem_preimage, Set.mem_setOf_eq]
          exact ⟨fun h => (qA_inr_mem_iff a x.1.2 x.2).mpr h,
            fun h => (qA_inr_mem_iff a x.1.2 x.2).mp h⟩
        rw [heq]
        exact hv
      · rintro ⟨p, t⟩ hp
        obtain ⟨z, hz, hz1⟩ := hp
        exact ⟨sqNorm_gt_of_incW_mem_Aset a (hz1 ▸ z.2), trivial⟩
  have hs' : IsOpen s' :=
    (Work.QuotientT2.isOpen_quotient_iff_preimage (r := a.glueData.setoid)).mpr key
  exact (isOpen_subtype_image_iff a).mp (hs'_def ▸ hs')

end Work.Space.Assembly
