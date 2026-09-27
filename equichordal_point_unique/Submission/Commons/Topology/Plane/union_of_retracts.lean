import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.Tietze
import Mathlib.Topology.GDelta.MetrizableSpace

/-!
# `Commons.Topology.Plane.union_of_retracts`

**Borsuk's gluing theorem for plane absolute retracts (the Aronszajn–Borusk step).**

If `A`, `B` and `A ∩ B` are all retracts of `ℂ`, then so is `A ∪ B`.

The proof is elementary and uses no ANR theory:

* a retract of the Hausdorff space `ℂ` is closed (it is an equalizer);
* a retract of `ℂ` has the Tietze extension property (`TietzeExtension.of_retract`);
* the continuous comparison function `g x = infDist x A - infDist x B` separates `A \ B`
  (`g ≤ 0`) from `B \ A` (`g ≥ 0`), and its zero level `Lev = {g = 0}` meets `A` exactly in
  `A ∩ B`;
* extend `id` on `A` and the retraction onto `A ∩ B` on `Lev` to `ρA : C(ℂ, ↥A)` (Tietze for
  `↥A`), and symmetrically `ρB : C(ℂ, ↥B)`; on `Lev` both extensions equal the `A ∩ B`-retraction,
  so `ρA` and `ρB` agree there;
* glue `ρA` (where `g ≤ 0`) to `ρB` (where `g ≥ 0`) over the two-piece closed cover
  `{g ≤ 0} ∪ {g ≥ 0} = ℂ`.

On `A`, `g ≤ 0` and `ρA = id`; on `B`, `g ≥ 0` and `ρB = id`; hence the glued map fixes `A ∪ B`.
-/

open Set Metric
open scoped Topology

namespace Commons.Topology.Plane

/-- A retract of the Hausdorff space `ℂ` is closed: it is the equalizer of the retraction and the
identity. -/
private theorem isClosed_of_retract_of_plane {K : Set ℂ}
    (h : ∃ r : C(ℂ, ↥K), ∀ x : ↥K, r (x : ℂ) = x) : IsClosed K := by
  obtain ⟨r, hr⟩ := h
  have hK : K = {x : ℂ | (r x : ℂ) = x} := by
    ext x
    constructor
    · intro hx; exact congrArg Subtype.val (hr ⟨x, hx⟩)
    · intro hx
      have h2 : (r x : ℂ) ∈ K := (r x).2
      rwa [hx] at h2
  rw [hK]
  exact isClosed_eq (continuous_subtype_val.comp r.continuous) continuous_id

/-- A retract of `ℂ` has the Tietze extension property. -/
private theorem tietze_of_retract_of_plane {K : Set ℂ}
    (hret : ∃ r : C(ℂ, ↥K), ∀ x : ↥K, r (x : ℂ) = x) :
    TietzeExtension.{0, 0} ↥K := by
  obtain ⟨r, hr⟩ := hret
  refine TietzeExtension.of_retract (ι := ⟨fun x : ↥K => ((x : ℂ)),
    continuous_subtype_val⟩) r ?_
  ext x
  simpa using congrArg (fun y : ↥K => (y : ℂ)) (hr x)

/-- If `A ∪ B = univ` with `A`, `B` closed and `g` continuous on each, then `g` is continuous
(pasting lemma for a two-piece closed cover). -/
private theorem continuous_of_isClosed_cover_pair_of_plane {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {A B : Set X} (hA : IsClosed A) (hB : IsClosed B) (hAB : A ∪ B = univ)
    {g : X → Y} (hgA : ContinuousOn g A) (hgB : ContinuousOn g B) : Continuous g := by
  rw [continuous_iff_isClosed]
  intro C hC
  have h1 : IsClosed (A ∩ g ⁻¹' C) := hgA.preimage_isClosed_of_isClosed hA hC
  have h2 : IsClosed (B ∩ g ⁻¹' C) := hgB.preimage_isClosed_of_isClosed hB hC
  have hunion : (A ∩ g ⁻¹' C) ∪ (B ∩ g ⁻¹' C) = g ⁻¹' C := by
    ext x
    constructor
    · rintro (⟨-, hx⟩ | ⟨-, hx⟩) <;> exact hx
    · intro hx
      have hxAB : x ∈ A ∪ B := by rw [hAB]; trivial
      rcases hxAB with h | h
      · exact Or.inl ⟨h, hx⟩
      · exact Or.inr ⟨h, hx⟩
  rw [← hunion]
  exact h1.union h2

theorem union_of_retracts {A B : Set ℂ}
    (hA : ∃ r : C(ℂ, ↥A), ∀ x : ↥A, r (x : ℂ) = x)
    (hB : ∃ r : C(ℂ, ↥B), ∀ x : ↥B, r (x : ℂ) = x)
    (hAB : ∃ r : C(ℂ, ↥(A ∩ B)), ∀ x : ↥(A ∩ B), r (x : ℂ) = x) :
    ∃ r : C(ℂ, ↥(A ∪ B)), ∀ x : ↥(A ∪ B), r (x : ℂ) = x := by
  classical
  obtain ⟨w, hw⟩ := hAB
  have hTA : TietzeExtension.{0, 0} ↥A := tietze_of_retract_of_plane hA
  have hTB : TietzeExtension.{0, 0} ↥B := tietze_of_retract_of_plane hB
  have hAc : IsClosed A := isClosed_of_retract_of_plane hA
  have hBc : IsClosed B := isClosed_of_retract_of_plane hB
  have hABne : (A ∩ B).Nonempty := ⟨(w 0 : ℂ), (w 0).2⟩
  have hAne : A.Nonempty := hABne.mono inter_subset_left
  have hBne : B.Nonempty := hABne.mono inter_subset_right
  have hwA : ∀ y : ℂ, (w y : ℂ) ∈ A := fun y => ((Set.mem_inter_iff (w y : ℂ) A B).mp (w y).2).1
  have hwB : ∀ y : ℂ, (w y : ℂ) ∈ B := fun y => ((Set.mem_inter_iff (w y : ℂ) A B).mp (w y).2).2
  -- the comparison function
  set g : ℂ → ℝ := fun x => Metric.infDist x A - Metric.infDist x B with hgdef
  have hgc : Continuous g := by
    rw [hgdef]; exact (Metric.continuous_infDist_pt A).sub (Metric.continuous_infDist_pt B)
  have hgA : ∀ x ∈ A, g x ≤ 0 := by
    intro x hx
    rw [hgdef]
    simp only [Metric.infDist_zero_of_mem hx, zero_sub]
    linarith [Metric.infDist_nonneg (x := x) (s := B)]
  have hgB : ∀ x ∈ B, 0 ≤ g x := by
    intro x hx
    rw [hgdef]
    simp only [Metric.infDist_zero_of_mem hx, sub_zero]
    exact Metric.infDist_nonneg
  have hgA0 : ∀ x ∈ A, g x = 0 → x ∈ B := by
    intro x hxA hg0
    rw [hgdef] at hg0
    simp only [Metric.infDist_zero_of_mem hxA, zero_sub, neg_eq_zero] at hg0
    have hmem : x ∈ closure B := (Metric.mem_closure_iff_infDist_zero hBne).mpr hg0
    rwa [hBc.closure_eq] at hmem
  have hgB0 : ∀ x ∈ B, g x = 0 → x ∈ A := by
    intro x hxB hg0
    rw [hgdef] at hg0
    simp only [Metric.infDist_zero_of_mem hxB, sub_zero] at hg0
    have hmem : x ∈ closure A := (Metric.mem_closure_iff_infDist_zero hAne).mpr hg0
    rwa [hAc.closure_eq] at hmem
  -- the interface
  set Lev : Set ℂ := {x : ℂ | g x = 0} with hLevdef
  have hLevc : IsClosed Lev := by
    rw [hLevdef]; exact isClosed_eq hgc continuous_const
  -- first extension: fix A, send the interface to A ∩ B
  set ZA : Set ℂ := A ∪ Lev with hZAdef
  have hZAc : IsClosed ZA := by rw [hZAdef]; exact hAc.union hLevc
  set φAf : ↥ZA → ↥A := fun z =>
    if h : ((z : ℂ) ∈ A) then ⟨(z : ℂ), h⟩
    else ⟨(w (z : ℂ) : ℂ), hwA (z : ℂ)⟩ with hφAdef
  have hZA1 : IsClosed {z : ↥ZA | (z : ℂ) ∈ A} := hAc.preimage continuous_subtype_val
  have hZA2 : IsClosed {z : ↥ZA | g (z : ℂ) = 0} :=
    isClosed_eq (hgc.comp continuous_subtype_val) continuous_const
  have hcovA : ({z : ↥ZA | (z : ℂ) ∈ A} : Set ↥ZA) ∪ {z : ↥ZA | g (z : ℂ) = 0} = univ := by
    ext z
    simp only [mem_union, mem_ofPred_eq, mem_univ, iff_true]
    rcases (show (z : ℂ) ∈ A ∪ Lev from (z : ↥ZA).2) with h | h
    · exact Or.inl h
    · exact Or.inr h
  have hconA1 : ContinuousOn φAf {z : ↥ZA | (z : ℂ) ∈ A} := by
    rw [continuousOn_iff_continuous_domRestrict]
    refine Continuous.congr (Continuous.subtype_mk
      (continuous_subtype_val.comp continuous_subtype_val)
      (fun z => (show ((z : ↥ZA) : ℂ) ∈ A from z.2))) ?_
    intro z
    change ⟨((z : ↥ZA) : ℂ), (show ((z : ↥ZA) : ℂ) ∈ A from z.2)⟩ = φAf (z : ↥ZA)
    simp only [hφAdef, dif_pos (show ((z : ↥ZA) : ℂ) ∈ A from z.2)]
  have hconA2 : ContinuousOn φAf {z : ↥ZA | g (z : ℂ) = 0} := by
    rw [continuousOn_iff_continuous_domRestrict]
    refine Continuous.congr (Continuous.subtype_mk
      (continuous_subtype_val.comp (w.continuous.comp
        (continuous_subtype_val.comp continuous_subtype_val))) (fun z => hwA ((z : ↥ZA) : ℂ))) ?_
    intro z
    by_cases h : ((z : ↥ZA) : ℂ) ∈ A
    · have hzb : ((z : ↥ZA) : ℂ) ∈ B := hgA0 _ h (show g ((z : ↥ZA) : ℂ) = 0 from z.2)
      have hfix : (w ((z : ↥ZA) : ℂ) : ℂ) = ((z : ↥ZA) : ℂ) :=
        congrArg Subtype.val (hw ⟨((z : ↥ZA) : ℂ), ⟨h, hzb⟩⟩)
      change ⟨(w ((z : ↥ZA) : ℂ) : ℂ), hwA ((z : ↥ZA) : ℂ)⟩ = φAf (z : ↥ZA)
      simp only [hφAdef, dif_pos h, hfix]
    · change ⟨(w ((z : ↥ZA) : ℂ) : ℂ), hwA ((z : ↥ZA) : ℂ)⟩ = φAf (z : ↥ZA)
      simp only [hφAdef, dif_neg h]
  have hφAc : Continuous φAf :=
    continuous_of_isClosed_cover_pair_of_plane hZA1 hZA2 hcovA hconA1 hconA2
  obtain ⟨ρA, hρA⟩ := ContinuousMap.exists_restrict_eq (Y := ↥A) hZAc ⟨φAf, hφAc⟩
  have hρA_Z : ∀ z : ↥ZA, ρA (z : ℂ) = φAf z := by
    intro z
    have h := congrArg (fun (m : C(↥ZA, ↥A)) => m z) hρA
    simpa [ContinuousMap.restrict_apply] using h
  -- second extension: fix B, send the interface to A ∩ B
  set ZB : Set ℂ := B ∪ Lev with hZBdef
  have hZBc : IsClosed ZB := by rw [hZBdef]; exact hBc.union hLevc
  set φBf : ↥ZB → ↥B := fun z =>
    if h : ((z : ℂ) ∈ B) then ⟨(z : ℂ), h⟩
    else ⟨(w (z : ℂ) : ℂ), hwB (z : ℂ)⟩ with hφBdef
  have hZB1 : IsClosed {z : ↥ZB | (z : ℂ) ∈ B} := hBc.preimage continuous_subtype_val
  have hZB2 : IsClosed {z : ↥ZB | g (z : ℂ) = 0} :=
    isClosed_eq (hgc.comp continuous_subtype_val) continuous_const
  have hcovB : ({z : ↥ZB | (z : ℂ) ∈ B} : Set ↥ZB) ∪ {z : ↥ZB | g (z : ℂ) = 0} = univ := by
    ext z
    simp only [mem_union, mem_ofPred_eq, mem_univ, iff_true]
    rcases (show (z : ℂ) ∈ B ∪ Lev from (z : ↥ZB).2) with h | h
    · exact Or.inl h
    · exact Or.inr h
  have hconB1 : ContinuousOn φBf {z : ↥ZB | (z : ℂ) ∈ B} := by
    rw [continuousOn_iff_continuous_domRestrict]
    refine Continuous.congr (Continuous.subtype_mk
      (continuous_subtype_val.comp continuous_subtype_val)
      (fun z => (show ((z : ↥ZB) : ℂ) ∈ B from z.2))) ?_
    intro z
    change ⟨((z : ↥ZB) : ℂ), (show ((z : ↥ZB) : ℂ) ∈ B from z.2)⟩ = φBf (z : ↥ZB)
    simp only [hφBdef, dif_pos (show ((z : ↥ZB) : ℂ) ∈ B from z.2)]
  have hconB2 : ContinuousOn φBf {z : ↥ZB | g (z : ℂ) = 0} := by
    rw [continuousOn_iff_continuous_domRestrict]
    refine Continuous.congr (Continuous.subtype_mk
      (continuous_subtype_val.comp (w.continuous.comp
        (continuous_subtype_val.comp continuous_subtype_val))) (fun z => hwB ((z : ↥ZB) : ℂ))) ?_
    intro z
    by_cases h : ((z : ↥ZB) : ℂ) ∈ B
    · have hza : ((z : ↥ZB) : ℂ) ∈ A := hgB0 _ h (show g ((z : ↥ZB) : ℂ) = 0 from z.2)
      have hfix : (w ((z : ↥ZB) : ℂ) : ℂ) = ((z : ↥ZB) : ℂ) :=
        congrArg Subtype.val (hw ⟨((z : ↥ZB) : ℂ), ⟨hza, h⟩⟩)
      change ⟨(w ((z : ↥ZB) : ℂ) : ℂ), hwB ((z : ↥ZB) : ℂ)⟩ = φBf (z : ↥ZB)
      simp only [hφBdef, dif_pos h, hfix]
    · change ⟨(w ((z : ↥ZB) : ℂ) : ℂ), hwB ((z : ↥ZB) : ℂ)⟩ = φBf (z : ↥ZB)
      simp only [hφBdef, dif_neg h]
  have hφBc : Continuous φBf :=
    continuous_of_isClosed_cover_pair_of_plane hZB1 hZB2 hcovB hconB1 hconB2
  obtain ⟨ρB, hρB⟩ := ContinuousMap.exists_restrict_eq (Y := ↥B) hZBc ⟨φBf, hφBc⟩
  have hρB_Z : ∀ z : ↥ZB, ρB (z : ℂ) = φBf z := by
    intro z
    have h := congrArg (fun (m : C(↥ZB, ↥B)) => m z) hρB
    simpa [ContinuousMap.restrict_apply] using h
  -- key facts about the extensions
  have hA_on : ∀ x ∈ A, (ρA x : ℂ) = x := by
    intro x hx
    have hxZ : x ∈ ZA := (show x ∈ A ∪ Lev from ((Set.mem_union x A Lev).mpr (Or.inl hx)))
    have h := hρA_Z ⟨x, hxZ⟩
    rw [hφAdef] at h
    simp only [dif_pos hx] at h
    exact congrArg Subtype.val h
  have hB_on : ∀ x ∈ B, (ρB x : ℂ) = x := by
    intro x hx
    have hxZ : x ∈ ZB := (show x ∈ B ∪ Lev from ((Set.mem_union x B Lev).mpr (Or.inl hx)))
    have h := hρB_Z ⟨x, hxZ⟩
    rw [hφBdef] at h
    simp only [dif_pos hx] at h
    exact congrArg Subtype.val h
  have hA_lev : ∀ x, g x = 0 → (ρA x : ℂ) = (w x : ℂ) := by
    intro x hx
    have hxZ : x ∈ ZA := (show x ∈ A ∪ Lev from ((Set.mem_union x A Lev).mpr (Or.inr hx)))
    have h := hρA_Z ⟨x, hxZ⟩
    by_cases hxA : x ∈ A
    · have hxB : x ∈ B := hgA0 x hxA hx
      have hfix : (w x : ℂ) = x := congrArg Subtype.val (hw ⟨x, ⟨hxA, hxB⟩⟩)
      rw [hφAdef] at h
      simp only [dif_pos hxA] at h
      rw [congrArg Subtype.val h, hfix]
    · rw [hφAdef] at h
      simp only [dif_neg hxA] at h
      exact congrArg Subtype.val h
  have hB_lev : ∀ x, g x = 0 → (ρB x : ℂ) = (w x : ℂ) := by
    intro x hx
    have hxZ : x ∈ ZB := (show x ∈ B ∪ Lev from ((Set.mem_union x B Lev).mpr (Or.inr hx)))
    have h := hρB_Z ⟨x, hxZ⟩
    by_cases hxB : x ∈ B
    · have hxA : x ∈ A := hgB0 x hxB hx
      have hfix : (w x : ℂ) = x := congrArg Subtype.val (hw ⟨x, ⟨hxA, hxB⟩⟩)
      rw [hφBdef] at h
      simp only [dif_pos hxB] at h
      rw [congrArg Subtype.val h, hfix]
    · rw [hφBdef] at h
      simp only [dif_neg hxB] at h
      exact congrArg Subtype.val h
  -- assemble
  set rfun : ℂ → ↥(A ∪ B) := fun x =>
    if g x ≤ 0 then ⟨(ρA x : ℂ), (Set.mem_union (ρA x : ℂ) A B).mpr (Or.inl (ρA x).2)⟩
    else ⟨(ρB x : ℂ), (Set.mem_union (ρB x : ℂ) A B).mpr (Or.inr (ρB x).2)⟩ with hrdef
  have hcontr : Continuous rfun := by
    refine continuous_of_isClosed_cover_pair_of_plane
      (A := {x : ℂ | g x ≤ 0}) (B := {x : ℂ | 0 ≤ g x}) ?_ ?_ ?_ ?_ ?_
    · exact isClosed_le hgc continuous_const
    · exact isClosed_le continuous_const hgc
    · ext x; simp only [mem_union, mem_ofPred_eq, mem_univ, iff_true]
      rcases le_or_gt (g x) 0 with h | h
      · exact Or.inl h
      · exact Or.inr (le_of_lt h)
    · have hc1 : Continuous fun x : ℂ =>
          (⟨(ρA x : ℂ), (Set.mem_union (ρA x : ℂ) A B).mpr (Or.inl (ρA x).2)⟩ : ↥(A ∪ B)) :=
        Continuous.subtype_mk (continuous_subtype_val.comp ρA.continuous)
          (fun x => (Set.mem_union (ρA x : ℂ) A B).mpr (Or.inl (ρA x).2))
      refine ContinuousOn.congr hc1.continuousOn ?_
      intro x hx
      rw [hrdef]; beta_reduce; rw [if_pos (show g x ≤ 0 from hx)]
    · have hc2 : Continuous fun x : ℂ =>
          (⟨(ρB x : ℂ), (Set.mem_union (ρB x : ℂ) A B).mpr (Or.inr (ρB x).2)⟩ : ↥(A ∪ B)) :=
        Continuous.subtype_mk (continuous_subtype_val.comp ρB.continuous)
          (fun x => (Set.mem_union (ρB x : ℂ) A B).mpr (Or.inr (ρB x).2))
      refine ContinuousOn.congr hc2.continuousOn ?_
      intro x hx
      rcases eq_or_lt_of_le (show 0 ≤ g x from hx) with h | h
      · have h0 : g x = 0 := h.symm
        rw [hrdef]; beta_reduce; rw [if_pos (le_of_eq h0)]
        exact Subtype.ext ((hA_lev x h0).trans ((hB_lev x h0).symm))
      · rw [hrdef]; beta_reduce; rw [if_neg (not_le.mpr h)]
  refine ⟨⟨rfun, hcontr⟩, ?_⟩
  intro x
  show rfun (x : ℂ) = x
  rcases (Set.mem_union (x : ℂ) A B).mp x.2 with hx | hx
  · have hgx : g (x : ℂ) ≤ 0 := hgA (x : ℂ) hx
    have h1 : rfun (x : ℂ) = (⟨(x : ℂ), (Set.mem_union (x : ℂ) A B).mpr (Or.inl hx)⟩ : ↥(A ∪ B)) := by
      rw [hrdef]; beta_reduce; rw [if_pos hgx]
      exact Subtype.ext (hA_on (x : ℂ) hx)
    rw [h1]
  · have hgx : 0 ≤ g (x : ℂ) := hgB (x : ℂ) hx
    rcases eq_or_lt_of_le hgx with h0 | hpos
    · have h1 : rfun (x : ℂ) = (⟨(x : ℂ), (Set.mem_union (x : ℂ) A B).mpr (Or.inr hx)⟩ : ↥(A ∪ B)) := by
        rw [hrdef]; beta_reduce; rw [if_pos (le_of_eq h0.symm)]
        exact Subtype.ext (((hA_lev (x : ℂ) h0.symm).trans ((hB_lev (x : ℂ) h0.symm)).symm).trans
          (hB_on (x : ℂ) hx))
      rw [h1]
    · have h1 : rfun (x : ℂ) = (⟨(x : ℂ), (Set.mem_union (x : ℂ) A B).mpr (Or.inr hx)⟩ : ↥(A ∪ B)) := by
        rw [hrdef]; beta_reduce; rw [if_neg (not_le.mpr hpos)]
        exact Subtype.ext (hB_on (x : ℂ) hx)
      rw [h1]

end Commons.Topology.Plane