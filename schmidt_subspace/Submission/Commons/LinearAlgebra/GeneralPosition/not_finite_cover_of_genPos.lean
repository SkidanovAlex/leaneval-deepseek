import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

namespace Commons.LinearAlgebra.GeneralPosition

/-- **An infinite general-position set is not covered by finitely many proper subspaces.**

If every finite subset of `s` with at most `Module.finrank K V` elements is linearly
independent (i.e. `s` is in general position) and `s` is infinite, then `s` cannot be
contained in a finite union of proper subspaces: otherwise one of them would contain
`finrank K V` elements of `s`, which would then be linearly dependent. -/
theorem not_finite_cover_of_genPos {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {s : Set V}
    (hgp : ∀ T : Finset V, (↑T : Set V) ⊆ s → T.card ≤ Module.finrank K V →
      LinearIndependent K (fun x : T => (x : V)))
    (hinf : s.Infinite) :
    ¬ ∃ T : Finset (Submodule K V), (∀ W ∈ T, W ≠ ⊤) ∧ ∀ x ∈ s, ∃ W ∈ T, x ∈ W := by
  rintro ⟨T, hprop, hcover⟩
  -- Some member of `T` contains infinitely many points of `s`.
  have hinfW : ∃ W ∈ T, (s ∩ (W : Set V)).Infinite := by
    by_contra hcon
    rw [not_exists] at hcon
    have hfin : ∀ W ∈ T, (s ∩ (W : Set V)).Finite := by
      intro W hW
      by_contra hf
      exact hcon W ⟨hW, hf⟩
    have hsub : s ⊆ ⋃ W ∈ (T : Set (Submodule K V)), (s ∩ (W : Set V)) := by
      intro x hx
      obtain ⟨W, hWT, hxW⟩ := hcover x hx
      exact Set.mem_biUnion hWT ⟨hx, hxW⟩
    have hUfin : (⋃ W ∈ (T : Set (Submodule K V)), (s ∩ (W : Set V))).Finite :=
      Set.Finite.biUnion T.finite_toSet hfin
    exact hinf.not_finite (hUfin.subset hsub)
  obtain ⟨W, hWT, hWinf⟩ := hinfW
  have hWne : W ≠ ⊤ := hprop W hWT
  -- Choose `finrank K V` distinct points of `s ∩ W`.
  obtain ⟨t, ht_sub, ht_card⟩ := hWinf.exists_subset_card_eq (Module.finrank K V)
  have hLI : LinearIndependent K (fun x : t => (x : V)) :=
    hgp t (fun x hx => (ht_sub hx).1) (le_of_eq ht_card)
  -- They are linearly independent as elements of `W` too.
  have hLIW : LinearIndependent K (fun x : t => (⟨(x : V), (ht_sub x.2).2⟩ : W)) :=
    LinearIndependent.of_comp (Submodule.subtype W) hLI
  have hcard : t.card ≤ Module.finrank K W := by
    have h := hLIW.fintype_card_le_finrank
    rwa [Fintype.card_coe] at h
  have hlt : Module.finrank K W < Module.finrank K V := Submodule.finrank_lt hWne
  omega

end Commons.LinearAlgebra.GeneralPosition