import Mathlib
import Submission.Work.WilC4aP.Basic

namespace Work.WilC4aP

/-- A monic complex polynomial of degree `m`, all of whose roots are simple, has exactly `m`
distinct roots; enumerate them by `Fin m`. -/
theorem exists_root_enum {m : ℕ} {p : Polynomial ℂ} (hmon : p.Monic) (hdeg : p.natDegree = m)
    (hsep : ∀ w : ℂ, p.eval w = 0 → p.derivative.eval w ≠ 0) :
    ∃ r : Fin m → ℂ, Function.Injective r ∧ ∀ j, p.eval (r j) = 0 := by
  classical
  have hp0 : p ≠ 0 := hmon.ne_zero
  -- Every root is simple, so the multiset of roots has no repetitions.
  have hcount : ∀ a : ℂ, p.roots.count a ≤ 1 := by
    intro a
    rw [Polynomial.count_roots]
    by_contra h
    rw [not_le] at h
    obtain ⟨hr, hdr⟩ := (Polynomial.one_lt_rootMultiplicity_iff_isRoot hp0).mp h
    exact (hsep a hr) hdr
  have hnodup : p.roots.Nodup := Multiset.nodup_iff_count_le_one.mpr hcount
  -- Over an algebraically closed field the roots are counted with multiplicity equal the degree.
  have hscard : (p.roots.toFinset).card = m := by
    rw [Multiset.toFinset_card_of_nodup hnodup]
    exact (IsAlgClosed.card_roots_eq_natDegree).trans hdeg
  -- Enumerate the (finitely many) roots through an equivalence with `Fin m`.
  let e : ↥(p.roots.toFinset) ≃ Fin m :=
    (p.roots.toFinset).equivFin.trans (Fin.castOrderIso hscard).toEquiv
  refine ⟨fun j => (e.symm j : ℂ), fun i j hij => ?_, fun j => ?_⟩
  · exact e.symm.injective (Subtype.ext hij)
  · have hj : ((e.symm j : ℂ)) ∈ p.roots.toFinset := (e.symm j).2
    rw [Multiset.mem_toFinset] at hj
    exact (Polynomial.mem_roots hp0).mp hj

end Work.WilC4aP
