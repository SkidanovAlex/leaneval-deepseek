import Mathlib
import Submission.Work.ShafarevichKoch.Cohomology3Map

namespace Work.ShafarevichKoch

open Work.ConCohomology

/-- `d²` is additive on differences of `2`-cochains. -/
private lemma d2Fun_sub_aux {G : Type*} [Group G] [TopologicalSpace G] {M : Type*}
    [AddCommGroup M] [DistribMulAction G M] (f g : G × G → M) :
    d2Fun (f - g) = d2Fun f - d2Fun g := by
  rw [sub_eq_add_neg, d2Fun_add, d2Fun_neg, sub_eq_add_neg]

theorem exact_H2_C {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [DistribMulAction G A] [DistribMulAction G B] [DistribMulAction G C]
    [Work.ConCohomology.IsDiscreteGModule G A] [Work.ConCohomology.IsDiscreteGModule G B]
    [Work.ConCohomology.IsDiscreteGModule G C]
    (S : Work.ConCohomology.CoeffSES G A B C)
    (δ : Work.ConCohomology.H2 G C →+ Work.ShafarevichKoch.H3 G A)
    (hδ : ∀ (z : Work.ConCohomology.Z2 G C) (u : Work.ConCohomology.Cochain2 G B),
      (∀ p : G × G, S.g (u p) = (z : Work.ConCohomology.Cochain2 G C) p) →
      ∃ w : Work.ShafarevichKoch.Z3 G A,
        Work.ShafarevichKoch.H3.mk w = δ (Work.ConCohomology.H2.mk z) ∧
        (∀ p : G × G × G, S.f ((w : G × G × G → A) p) =
          Work.ConCohomology.d2Fun (u : G × G → B) p)) :
    ∀ x : Work.ConCohomology.H2 G C,
      δ x = 0 ↔ ∃ y : Work.ConCohomology.H2 G B, Work.ConCohomology.H2Map S.g y = x := by
  intro x
  constructor
  · -- `ker δ ⊆ im H²(g)`
    intro hx
    revert hx
    refine QuotientAddGroup.induction_on x ?_
    intro z hz
    -- a lift of the cocycle `z` to a cochain in `B` along the section of `S.g`
    let u : Cochain2 G B :=
      ⟨fun p : G × G => S.sect ((z : Cochain2 G C) p),
        (z : Cochain2 G C).isLocallyConstant.comp S.sect⟩
    have hu : ∀ p : G × G, S.g (u p) = (z : Cochain2 G C) p := fun p => S.g_sect _
    obtain ⟨w, hw1, hw2⟩ := hδ z u hu
    -- `δ [z] = 0`, so the `3`-cocycle `w` is a `3`-coboundary
    have hw0 : H3.mk w = 0 := by rw [hw1]; exact hz
    have hwB : (w : Cochain3 G A) ∈ B3 G A := by
      have h : ((w - 0 : Z3 G A) : Cochain3 G A) ∈ B3 G A :=
        (mem_B3' (G := G) (M := A)).mp ((H3.mk_eq_mk_iff w 0).mp (by rw [hw0]; rfl))
      simpa using h
    obtain ⟨v, hv⟩ : ∃ v : Cochain2 G A, d2Hom G A v = (w : Cochain3 G A) := hwB
    have hvw : ∀ p : G × G × G, d2Fun (v : G × G → A) p = (w : G × G × G → A) p := by
      intro p
      have h := congrFun (congrArg (fun x : Cochain3 G A => (x : G × G × G → A)) hv) p
      simp only [d2Hom, AddMonoidHom.coe_mk, ZeroHom.coe_mk, LocallyConstant.coe_mk] at h
      exact h
    have hgf : ∀ a : A, S.g (S.f a) = 0 := fun a => (S.exact (S.f a)).mpr ⟨a, rfl⟩
    -- `u - f_* v` is the desired `2`-cocycle of `B`
    let u' : Cochain2 G B := u - cochain2Map S.f v
    have hu'Z : u' ∈ Z2 G B := by
      rw [mem_Z2, isCocycle2_iff_d2Fun]
      funext p
      have h1 : (u' : G × G → B) = (u : G × G → B) - fun q => S.f ((v : G × G → A) q) := rfl
      rw [h1, d2Fun_sub_aux, d2Fun_comp]
      show d2Fun (u : G × G → B) p - S.f (d2Fun (v : G × G → A) p) = 0
      rw [hvw p, ← hw2 p, sub_self]
    have hZeq : (Z2Map S.g ⟨u', hu'Z⟩ : Z2 G C) = z := by
      apply Subtype.ext
      refine LocallyConstant.ext fun p => ?_
      have h2 : (u' : Cochain2 G B) p = (u : Cochain2 G B) p - S.f ((v : Cochain2 G A) p) := rfl
      rw [show (((Z2Map S.g ⟨u', hu'Z⟩ : Z2 G C)) : Cochain2 G C) p =
            S.g ((u' : Cochain2 G B) p) from rfl,
        h2, EqHom.map_sub, hgf, hu p, sub_zero]
    refine ⟨H2.mk ⟨u', hu'Z⟩, ?_⟩
    rw [H2Map_mk, hZeq]
    rfl
  · -- `im H²(g) ⊆ ker δ`
    rintro ⟨y, rfl⟩
    refine QuotientAddGroup.induction_on y ?_
    intro zB
    change δ ((H2Map S.g) (H2.mk zB)) = 0
    rw [H2Map_mk]
    obtain ⟨w, hw1, hw2⟩ := hδ (Z2Map S.g zB) zB (fun p => rfl)
    have hz0 : ∀ p : G × G × G, d2Fun (zB : G × G → B) p = 0 := by
      intro p
      have hc : d2Fun (zB : G × G → B) = 0 := (isCocycle2_iff_d2Fun _).mp (mem_Z2.mp zB.2)
      simp [hc]
    have hw2' : ∀ p : G × G × G, (w : G × G × G → A) p = 0 := by
      intro p
      refine S.injective_f ?_
      rw [hw2 p, hz0 p, EqHom.map_zero]
    have hwzero : w = 0 := by
      apply Subtype.ext
      refine LocallyConstant.ext fun p => ?_
      simpa using hw2' p
    rw [← hw1, hwzero]
    rfl

end Work.ShafarevichKoch
