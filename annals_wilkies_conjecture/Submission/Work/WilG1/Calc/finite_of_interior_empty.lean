/-
  WilG1/Calc : `Ω`-sets of empty interior in `ℝ¹` are finite.

  In dimension one the sharp-o-minimality axioms give `SOMin.comps`: every `A ∈ S.Ω F D 1`
  is a finite union of *preconnected* sets (with an explicit cardinal bound `p.eval D`).
  A preconnected subset of `ℝ¹` is an interval; if it is moreover contained in a set with
  empty interior, two distinct points would produce an open subinterval inside it, hence a
  nonempty interior.  So every piece is a subsingleton and `A` is finite.

  The one-dimensional space `Fin 1 → ℝ` is used through the homeomorphism
  `Homeomorph.funUnique (Fin 1) ℝ` with `ℝ`, where `IsPreconnected.ordConnected` is available.
-/
import Mathlib
import Submission.Work.WilG1.Basic

set_option autoImplicit false

noncomputable section

open Classical

namespace Work.WilG1.Calc

open WilkiesDesign WilkiesConjecture

/-- A preconnected subset of `ℝ¹ = Fin 1 → ℝ` whose interior is empty is a subsingleton.

Indeed, transporting along the homeomorphism `Fin 1 → ℝ ≃ₜ ℝ` (evaluation at the unique
index), the image is preconnected in `ℝ`, hence order-convex (`isPreconnected_iff_ordConnected`);
two distinct points of it would sandwich a nonempty open interval, giving a nonempty interior. -/
lemma isPreconnected_subsingleton_of_interior_empty {c : Set (Fin 1 → ℝ)}
    (hc : IsPreconnected c) (hint : interior c = ∅) : c.Subsingleton := by
  let e : (Fin 1 → ℝ) ≃ₜ ℝ := Homeomorph.funUnique (Fin 1) ℝ
  have hpre : IsPreconnected (e '' c) := hc.image e e.continuous.continuousOn
  have hint' : interior (e '' c) = ∅ := by
    rw [← Homeomorph.image_interior e c, hint, Set.image_empty]
  have hsub : (e '' c).Subsingleton := by
    intro x hx y hy
    by_contra hxy
    rcases lt_or_gt_of_ne hxy with h | h
    · obtain ⟨z, hz⟩ : (Set.Ioo x y).Nonempty := ⟨(x + y) / 2, by constructor <;> linarith⟩
      have hzI : z ∈ interior (Set.Ioo x y) := by rw [isOpen_Ioo.interior_eq]; exact hz
      have hz' : z ∈ interior (e '' c) :=
        interior_mono (fun w hw => hpre.Icc_subset hx hy ⟨le_of_lt hw.1, le_of_lt hw.2⟩) hzI
      rw [hint'] at hz'
      exact hz'
    · obtain ⟨z, hz⟩ : (Set.Ioo y x).Nonempty := ⟨(x + y) / 2, by constructor <;> linarith⟩
      have hzI : z ∈ interior (Set.Ioo y x) := by rw [isOpen_Ioo.interior_eq]; exact hz
      have hz' : z ∈ interior (e '' c) :=
        interior_mono (fun w hw => hpre.Icc_subset hy hx ⟨le_of_lt hw.1, le_of_lt hw.2⟩) hzI
      rw [hint'] at hz'
      exact hz'
  have h2 := hsub.preimage (f := ⇑e) e.injective
  rwa [Set.preimage_image_eq c e.injective] at h2

/-- An `Ω`-set with empty interior in dimension one is finite: by `SOMin.comps` it is a finite
union of preconnected sets, each of which is a subsingleton by the previous lemma. -/
theorem finite_of_interior_empty {S : WilkiesDesign.SOMin} {a D : ℕ} {b : Polynomial ℕ}
    {A : Set (Fin 1 → ℝ)} (hA : A ∈ S.Ω a (b.eval D) 1) (hint : interior A = ∅) :
    A.Finite := by
  obtain ⟨p, hp⟩ := S.comps a
  obtain ⟨s, _hcard, hconn, hAeq⟩ := hp (b.eval D) A hA
  rw [hAeq]
  refine Set.Finite.sUnion s.finite_toSet (fun c hc => ?_)
  have hcA : c ⊆ ⋃₀ (↑s : Set (Set (Fin 1 → ℝ))) := by
    intro z hz; exact Set.mem_sUnion.mpr ⟨c, by simpa using hc, hz⟩
  have h0 : interior (⋃₀ (↑s : Set (Set (Fin 1 → ℝ)))) = ∅ := by rw [← hAeq, hint]
  have hsub : interior c ⊆ (∅ : Set (Fin 1 → ℝ)) := by
    rw [← h0]; exact interior_mono hcA
  exact Set.Subsingleton.finite
    (isPreconnected_subsingleton_of_interior_empty (hconn c hc)
      (Set.Subset.antisymm hsub (Set.empty_subset _)))

end Work.WilG1.Calc

end
