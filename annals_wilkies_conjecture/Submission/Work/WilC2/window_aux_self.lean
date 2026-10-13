import Mathlib
import Submission.Work.WilC2.Dcl
import Submission.Work.WilC2.Main
import Submission.Work.WilC2.Uniform
import Submission.Work.WilC2.boundary_finite
import Submission.Work.WilC2.BndDefs
import Submission.Work.WilC2.bnd_ordConnected_finite
import Submission.Work.WilC2.finite_definable_singleton
import Submission.Work.WilC2.meetsDefinable_dcl
import Submission.Work.WilC4.sup_exists_dcl
import Submission.Work.WilC2.bnd_definable_alt
import Submission.Work.WilC2.Iio_definable
import Submission.Work.WilC2.Ioi_definable
import Submission.Work.WilC2.gap_subset_of_bnd

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section
open Classical FirstOrder FirstOrder.Language

namespace Work.WilC2

open WilkiesDesign WilkiesDesign.CG

/-! ## Small definability helpers -/

private lemma definable₁_inter {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
    [FirstOrder.Ring.CompatibleRing M] [WilkiesDesign.CG.rexpL.Structure M]
    [(FirstOrder.Language.constantsOn ℝ).Structure M]
    {T : Set M} {s t : Set M}
    (hs : T.Definable₁ WilkiesDesign.CG.LRc s) (ht : T.Definable₁ WilkiesDesign.CG.LRc t) :
    T.Definable₁ WilkiesDesign.CG.LRc (s ∩ t) := by
  rw [Set.Definable₁] at hs ht ⊢
  convert hs.inter ht using 1
  ext x
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]

private lemma definable₁_Icc {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
    [FirstOrder.Ring.CompatibleRing M] [WilkiesDesign.CG.rexpL.Structure M]
    [(FirstOrder.Language.constantsOn ℝ).Structure M]
    (hM : M ⊨ WilkiesDesign.CG.TR) {T : Set M} {u v : M} (hu : u ∈ T) (hv : v ∈ T) :
    T.Definable₁ WilkiesDesign.CG.LRc (Set.Icc u v) := by
  have h1 : T.Definable₁ WilkiesDesign.CG.LRc (Set.Ici u) := by
    have h := Iio_definable (M := M) hM (T := T) (c := u) hu
    rw [Set.Definable₁] at h ⊢
    convert h.compl using 1
    ext x
    simp only [Set.mem_Ici, Set.mem_Iio, Set.mem_compl_iff, Set.mem_ofPred_eq, not_lt]
  have h2 : T.Definable₁ WilkiesDesign.CG.LRc (Set.Iic v) := by
    have h := Ioi_definable (M := M) hM (T := T) (c := v) hv
    rw [Set.Definable₁] at h ⊢
    convert h.compl using 1
    ext x
    simp only [Set.mem_Iic, Set.mem_Ioi, Set.mem_compl_iff, Set.mem_ofPred_eq, not_lt]
  have h3 := definable₁_inter h1 h2
  rw [Set.Definable₁] at h3 ⊢
  convert h3 using 1
  ext x
  simp only [Set.mem_Icc, Set.mem_Ici, Set.mem_Iic, Set.mem_inter_iff, Set.mem_ofPred_eq]

private lemma definable₁_Ioo {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
    [FirstOrder.Ring.CompatibleRing M] [WilkiesDesign.CG.rexpL.Structure M]
    [(FirstOrder.Language.constantsOn ℝ).Structure M]
    (hM : M ⊨ WilkiesDesign.CG.TR) {T : Set M} {a b : M} (ha : a ∈ T) (hb : b ∈ T) :
    T.Definable₁ WilkiesDesign.CG.LRc (Set.Ioo a b) := by
  have h1 := Ioi_definable (M := M) hM (T := T) (c := a) ha
  have h2 := Iio_definable (M := M) hM (T := T) (c := b) hb
  have h3 := definable₁_inter h1 h2
  rw [Set.Definable₁] at h3 ⊢
  convert h3 using 1
  ext x
  simp only [Set.mem_Ioo, Set.mem_Ioi, Set.mem_Iio, Set.mem_inter_iff, Set.mem_ofPred_eq]

private lemma subset_dcl {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
    [FirstOrder.Ring.CompatibleRing M] [WilkiesDesign.CG.rexpL.Structure M]
    [(FirstOrder.Language.constantsOn ℝ).Structure M]
    (A : Set M) : A ⊆ Dcl A :=
  fun a ha => mem_dcl.mpr (Set.Definable.singleton_of_mem (L := WilkiesDesign.CG.LRc) (A := A) ha)

/-! ## The main theorem -/

/-- If `H` is `A`-definable and `b ∈ H` is not definable from `A`, then `H` contains a point `r`
definable from `A` such that the whole interval between `r` and `b` lies in `H` (i.e. `r` lies in
the same convex component of `H` as `b`).

Sketch: the boundary points of `H` are `A`-definable (`bnd_definable_alt` together with
`boundary_finite` and `finite_definable_singleton`, where the square hypothesis comes from
`Work.WilC2.model_exists_sq`), and being not in `Dcl A`, the point `b` is an interior point of `H`.
Writing `F` for the (finite) set of boundary points, let `α` be the largest boundary point below
`b` and `β` the smallest one above `b` (only the existing ones are used).  Then the interval `J`
cut out between them is `Dcl A`-definable, so by Tarski--Vaught (`meetsDefinable_dcl`) it contains
a point `r ∈ Dcl A`; and `J` avoids `F`, so the interval between `r` and `b` lies in `H`
(`gap_subset_of_bnd`), which is the claim. -/
theorem window_point_aux_self
    (hR : ∀ (n : ℕ) (X : Set (Fin n → ℝ)), WilkiesDesign.RExpExist X → WilkiesDesign.RExpExist Xᶜ)
    (hC0 : ∀ (n : ℕ) (X : Set (Fin n → ℝ)), (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc X → WilkiesDesign.RExpExist X)
    (hUF : WilkiesDesign.CG.UnifFiniteRExp)
    {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M] [FirstOrder.Ring.CompatibleRing M]
    [WilkiesDesign.CG.rexpL.Structure M] [(FirstOrder.Language.constantsOn ℝ).Structure M]
    [M ⊨ WilkiesDesign.CG.TR] {A : Set M} {H : Set M}
    (hH : A.Definable WilkiesDesign.CG.LRc {v : Fin 1 → M | v 0 ∈ H})
    {b : M} (hb : b ∈ H) (hbA : b ∉ Dcl A) :
    ∃ r ∈ Dcl A, Set.Icc (min r b) (max r b) ⊆ H := by
  classical
  have hTR : M ⊨ WilkiesDesign.CG.TR := ‹M ⊨ WilkiesDesign.CG.TR›
  have hsq : ∀ x : M, 0 ≤ x → ∃ z : M, x = z * z := model_exists_sq (M := M) hTR
  -- the boundary set of `H`
  let Bd : Set M := {x : M | IsBnd H x}
  have hBd_def : A.Definable WilkiesDesign.CG.LRc {v : Fin 1 → M | v 0 ∈ Bd} := by
    have h := bnd_definable_alt (M := M) hsq (A := A) (D := H) hH
    simpa only [Bd, Set.mem_ofPred_eq] using h
  have hBd_fin : Bd.Finite := by
    obtain ⟨F, hF⟩ := boundary_finite hR hC0 hUF (M := M) (A := A) (D := H) hH
    refine Set.Finite.subset F.finite_toSet ?_
    intro x hx
    simp only [Bd, Set.mem_ofPred_eq] at hx
    exact hF x hx.1 hx.2
  have hBd_dcl : ∀ x : M, x ∈ Bd → x ∈ Dcl A := fun x hx =>
    mem_dcl.mpr (finite_definable_singleton (M := M) hTR (A := A) (E := Bd)
      (show A.Definable₁ WilkiesDesign.CG.LRc Bd from hBd_def) hBd_fin x hx)
  have hbnb : ¬ IsBnd H b := fun h => hbA (hBd_dcl b (by simp only [Bd, Set.mem_ofPred_eq]; exact h))
  -- `b` is an interior point of `H`
  have hbint : ∃ ε : M, 0 < ε ∧ Set.Ioo (b - ε) (b + ε) ⊆ H := by
    by_contra hcon
    refine hbnb ⟨hcon, ?_⟩
    rintro ⟨ε, hε, hsub⟩
    exact absurd hb (by simpa using hsub ⟨by linarith, by linarith⟩)
  -- supremum lemmas for `H` and `Hᶜ`
  have hHc : A.Definable WilkiesDesign.CG.LRc {v : Fin 1 → M | v 0 ∈ Hᶜ} := by
    have h := hH.compl
    convert h using 1
    ext v
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff]
  have hsupH : ∀ {u v : M}, u < v → (H ∩ Set.Icc u v).Nonempty →
      ∃ s : M, IsLUB (H ∩ Set.Icc u v) s := by
    intro u v huv hne
    have hT : (A ∪ {u, v}).Definable₁ WilkiesDesign.CG.LRc (H ∩ Set.Icc u v) :=
      definable₁_inter (hH.mono Set.subset_union_left)
        (definable₁_Icc (M := M) hTR (T := A ∪ {u, v}) (u := u) (v := v) (by simp) (by simp))
    obtain ⟨s, hs, _⟩ :=
      Work.WilC4.sup_exists_dcl (M := M) hTR (T := A ∪ {u, v}) hT hne ⟨v, fun a ha => ha.2.2⟩
    exact ⟨s, hs⟩
  have hsupHc : ∀ {u v : M}, u < v → (Hᶜ ∩ Set.Icc u v).Nonempty →
      ∃ s : M, IsLUB (Hᶜ ∩ Set.Icc u v) s := by
    intro u v huv hne
    have hT : (A ∪ {u, v}).Definable₁ WilkiesDesign.CG.LRc (Hᶜ ∩ Set.Icc u v) :=
      definable₁_inter (hHc.mono Set.subset_union_left)
        (definable₁_Icc (M := M) hTR (T := A ∪ {u, v}) (u := u) (v := v) (by simp) (by simp))
    obtain ⟨s, hs, _⟩ :=
      Work.WilC4.sup_exists_dcl (M := M) hTR (T := A ∪ {u, v}) hT hne ⟨v, fun a ha => ha.2.2⟩
    exact ⟨s, hs⟩
  -- the finitely many boundary points
  let FB : Finset M := hBd_fin.toFinset
  have hFB : ∀ x : M, x ∈ FB ↔ x ∈ Bd := fun x => hBd_fin.mem_toFinset
  by_cases hL : ∃ l : M, l ∈ FB ∧ l < b
  · by_cases hR' : ∃ r : M, r ∈ FB ∧ b < r
    · -- case (1): boundary points on both sides
      let SL : Finset M := FB.filter (fun t => t < b)
      let SR : Finset M := FB.filter (fun t => b < t)
      have hLne : SL.Nonempty := by
        obtain ⟨l, hl⟩ := hL
        exact ⟨l, Finset.mem_filter.mpr hl⟩
      have hRne : SR.Nonempty := by
        obtain ⟨r, hr⟩ := hR'
        exact ⟨r, Finset.mem_filter.mpr hr⟩
      let α : M := SL.max' hLne
      let β : M := SR.min' hRne
      have hαBd : α ∈ Bd := hFB α |>.mp (Finset.mem_filter.mp (Finset.max'_mem SL hLne)).1
      have hβBd : β ∈ Bd := hFB β |>.mp (Finset.mem_filter.mp (Finset.min'_mem SR hRne)).1
      have hαltb : α < b := (Finset.mem_filter.mp (Finset.max'_mem SL hLne)).2
      have hbltβ : b < β := (Finset.mem_filter.mp (Finset.min'_mem SR hRne)).2
      have hα_dcl : α ∈ Dcl A := hBd_dcl α hαBd
      have hβ_dcl : β ∈ Dcl A := hBd_dcl β hβBd
      have hmax : ∀ s : M, s ∈ FB → s < b → s ≤ α := fun s hs hsb =>
        Finset.le_max' SL s (Finset.mem_filter.mpr ⟨hs, hsb⟩)
      have hmin : ∀ s : M, s ∈ FB → b < s → β ≤ s := fun s hs hbs =>
        Finset.min'_le SR s (Finset.mem_filter.mpr ⟨hs, hbs⟩)
      have hJdef : (Dcl A).Definable₁ WilkiesDesign.CG.LRc (Set.Ioo α β) :=
        definable₁_Ioo (M := M) hTR (T := Dcl A) (a := α) (b := β) hα_dcl hβ_dcl
      have hJne : (Set.Ioo α β).Nonempty := ⟨b, ⟨hαltb, hbltβ⟩⟩
      obtain ⟨r, hrJ, hrDcl⟩ :=
        meetsDefinable_dcl hR hC0 hUF (M := M) A (Set.Ioo α β) hJne hJdef
      refine ⟨r, hrDcl, ?_⟩
      refine gap_subset_of_bnd (M := M) hb hbnb ?_ (fun x hx => hx) ?_ hsupH hsupHc
      · -- `r` is not a boundary point
        intro hrBd
        have hrFB : r ∈ FB := hFB r |>.mpr hrBd
        rcases lt_trichotomy r b with hrb | hrb | hbr
        · exact absurd hrJ.1 (not_lt.mpr (hmax r hrFB hrb))
        · exact hbnb (hrb ▸ hrBd)
        · exact absurd hrJ.2 (not_lt.mpr (hmin r hrFB hbr))
      · intro f hf hcon
        have hfFB : f ∈ FB := hFB f |>.mpr hf
        rcases hcon with ⟨hrf, hfb⟩ | ⟨hbf, hfr⟩
        · exact absurd (lt_of_lt_of_le hrf (hmax f hfFB hfb)) (not_lt.mpr hrJ.1.le)
        · exact absurd (lt_of_le_of_lt (hmin f hfFB hbf) hfr) (not_lt.mpr hrJ.2.le)
    · -- case (2): boundary points only below `b`
      let SL : Finset M := FB.filter (fun t => t < b)
      have hLne : SL.Nonempty := by
        obtain ⟨l, hl⟩ := hL
        exact ⟨l, Finset.mem_filter.mpr hl⟩
      let α : M := SL.max' hLne
      have hαBd : α ∈ Bd := hFB α |>.mp (Finset.mem_filter.mp (Finset.max'_mem SL hLne)).1
      have hαltb : α < b := (Finset.mem_filter.mp (Finset.max'_mem SL hLne)).2
      have hα_dcl : α ∈ Dcl A := hBd_dcl α hαBd
      have hmax : ∀ s : M, s ∈ FB → s < b → s ≤ α := fun s hs hsb =>
        Finset.le_max' SL s (Finset.mem_filter.mpr ⟨hs, hsb⟩)
      have hJdef : (Dcl A).Definable₁ WilkiesDesign.CG.LRc (Set.Ioi α) :=
        Ioi_definable (M := M) hTR (T := Dcl A) (c := α) hα_dcl
      have hJne : (Set.Ioi α).Nonempty := ⟨b, hαltb⟩
      obtain ⟨r, hrJ, hrDcl⟩ :=
        meetsDefinable_dcl hR hC0 hUF (M := M) A (Set.Ioi α) hJne hJdef
      refine ⟨r, hrDcl, ?_⟩
      refine gap_subset_of_bnd (M := M) hb hbnb ?_ (fun x hx => hx) ?_ hsupH hsupHc
      · intro hrBd
        have hrFB : r ∈ FB := hFB r |>.mpr hrBd
        have hrb_le : r ≤ b := by
          by_contra hlt
          exact hR' ⟨r, hrFB, not_le.mp hlt⟩
        have hrne : r ≠ b := fun h => hbnb (h ▸ hrBd)
        exact absurd hrJ (not_lt.mpr (hmax r hrFB (lt_of_le_of_ne hrb_le hrne)))
      · intro f hf hcon
        have hfFB : f ∈ FB := hFB f |>.mpr hf
        rcases hcon with ⟨hrf, hfb⟩ | ⟨hbf, hfr⟩
        · exact absurd (lt_of_lt_of_le hrf (hmax f hfFB hfb)) (not_lt.mpr hrJ.le)
        · exact hR' ⟨f, hfFB, hbf⟩
  · by_cases hR' : ∃ r : M, r ∈ FB ∧ b < r
    · -- case (3): boundary points only above `b`
      let SR : Finset M := FB.filter (fun t => b < t)
      have hRne : SR.Nonempty := by
        obtain ⟨r, hr⟩ := hR'
        exact ⟨r, Finset.mem_filter.mpr hr⟩
      let β : M := SR.min' hRne
      have hβBd : β ∈ Bd := hFB β |>.mp (Finset.mem_filter.mp (Finset.min'_mem SR hRne)).1
      have hbltβ : b < β := (Finset.mem_filter.mp (Finset.min'_mem SR hRne)).2
      have hβ_dcl : β ∈ Dcl A := hBd_dcl β hβBd
      have hmin : ∀ s : M, s ∈ FB → b < s → β ≤ s := fun s hs hbs =>
        Finset.min'_le SR s (Finset.mem_filter.mpr ⟨hs, hbs⟩)
      have hJdef : (Dcl A).Definable₁ WilkiesDesign.CG.LRc (Set.Iio β) :=
        Iio_definable (M := M) hTR (T := Dcl A) (c := β) hβ_dcl
      have hJne : (Set.Iio β).Nonempty := ⟨b, hbltβ⟩
      obtain ⟨r, hrJ, hrDcl⟩ :=
        meetsDefinable_dcl hR hC0 hUF (M := M) A (Set.Iio β) hJne hJdef
      refine ⟨r, hrDcl, ?_⟩
      refine gap_subset_of_bnd (M := M) hb hbnb ?_ (fun x hx => hx) ?_ hsupH hsupHc
      · intro hrBd
        have hrFB : r ∈ FB := hFB r |>.mpr hrBd
        have hbr_le : b ≤ r := by
          by_contra hlt
          exact hL ⟨r, hrFB, not_le.mp hlt⟩
        have hrne : r ≠ b := fun h => hbnb (h ▸ hrBd)
        exact absurd hrJ (not_lt.mpr (hmin r hrFB (lt_of_le_of_ne hbr_le (Ne.symm hrne))))
      · intro f hf hcon
        have hfFB : f ∈ FB := hFB f |>.mpr hf
        rcases hcon with ⟨hrf, hfb⟩ | ⟨hbf, hfr⟩
        · exact hL ⟨f, hfFB, hfb⟩
        · exact absurd (lt_of_le_of_lt (hmin f hfFB hbf) hfr) (not_lt.mpr hrJ.le)
    · -- case (4): there are no boundary points at all
      have hBd_empty : ∀ x : M, ¬ IsBnd H x := by
        intro x hx
        have hxFB : x ∈ FB := hFB x |>.mpr (by simp only [Bd, Set.mem_ofPred_eq]; exact hx)
        rcases lt_trichotomy x b with h | h | h
        · exact hL ⟨x, hxFB, h⟩
        · exact hbnb (h ▸ hx)
        · exact hR' ⟨x, hxFB, h⟩
      obtain ⟨r, hrH, hrDcl⟩ :=
        meetsDefinable_dcl hR hC0 hUF (M := M) A H ⟨b, hb⟩
          (hH.mono (subset_dcl A))
      refine ⟨r, hrDcl, ?_⟩
      refine gap_subset_of_bnd (M := M) hb hbnb (hBd_empty r)
        (fun x hx => absurd hx (hBd_empty x)) (fun f hf => absurd hf (hBd_empty f)) hsupH hsupHc

end Work.WilC2
