import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.PairsAux
import Submission.Work.HP.MinkDefs
import Submission.Work.HP.lam_basic
import Submission.Work.HP.MDBasic.finite_sets

/-!
# Finiteness of the lattice window `IsPrimLat L ∧ rk L = r ∧ λ_{j+1}(L) ≤ s_j`

This is the universe-polymorphic form of `Work.HP.prim_lat_window_finite` (whose index type is
pinned to `Type 0`), together with the promised target `Work.HP.Sig2.Tset_finite`, which drops
the normalization hypothesis `1 ≤ s j`.

The mathematical content (as in `prim_lat_window_finite`) is the standard fact that a saturated
sublattice of `ℤ^ι` of rank `r` is *determined* by the `ℚ`-span of any `r` linearly independent
vectors it contains: since `L` is saturated one has `L = span_ℚ(L) ∩ ℤ^ι`, and if `f : Fin r → L`
is `ℤ`-linearly independent then `span_ℚ (range f) = span_ℚ(L)`.  The key lemma expressing this is
`primLatTorsionU`, which says that `ℤ^ι ⧸ span_ℤ (range f)` is torsion on `L`: every `v ∈ L` has
a nonzero integer multiple in `span_ℤ (range f)`.

The successive-minima condition then supplies, for each admissible `L`, a tuple `f` of `r`
independent vectors of `L` whose norms are bounded by a fixed constant depending only on the
`s j`; each `L` is recovered from `f`, so the set is the image of a finite set of tuples.
-/

set_option autoImplicit false

namespace Work.HP.Sig2

/-- **Torsion lemma.** If `f : Fin r → ℤ^ι` is `ℤ`-linearly independent, all its values lie in
a submodule `L ≤ ℤ^ι`, and `Module.finrank ℤ L = r`, then every `v ∈ L` has a nonzero integer
multiple lying in `Submodule.span ℤ (Set.range f)`. -/
theorem primLatTorsionU {ι : Type*} [Fintype ι] (r : ℕ) (f : Fin r → ι → ℤ)
    (L : Submodule ℤ (ι → ℤ)) (hf : LinearIndependent ℤ f) (hmem : ∀ i, f i ∈ L)
    (hrank : Module.finrank ℤ L = r) :
    ∀ v ∈ L, ∃ m : ℤ, m ≠ 0 ∧ m • v ∈ Submodule.span ℤ (Set.range f) := by
  intro v hv
  set M : Submodule ℤ (ι → ℤ) := Submodule.span ℤ (Set.range f) with hMdef
  have hML : M ≤ L := Submodule.span_le.mpr (Set.range_subset_iff.mpr hmem)
  have hMrank : Module.finrank ℤ M = r := by
    rw [hMdef, finrank_span_eq_card hf, Fintype.card_fin]
  set M' : Submodule ℤ L := Submodule.comap L.subtype M with hM'def
  have hM'rank : Module.finrank ℤ M' = r := by
    rw [← hMrank]
    exact (Submodule.comapSubtypeEquivOfLe hML).finrank_eq
  have hq := Submodule.finrank_quotient_add_finrank (M := L) M'
  rw [hM'rank, hrank] at hq
  have hq0 : Module.finrank ℤ (L ⧸ M') = 0 := by omega
  have htors : Module.IsTorsion ℤ (L ⧸ M') := Module.finrank_eq_zero_iff_isTorsion.mp hq0
  obtain ⟨a, ha⟩ := htors (x := Submodule.Quotient.mk (⟨v, hv⟩ : L))
  rw [Submonoid.smul_def] at ha
  refine ⟨(a : ℤ), mem_nonZeroDivisors_iff_ne_zero.mp a.2, ?_⟩
  rw [← Submodule.Quotient.mk_smul M' (a : ℤ) (⟨v, hv⟩ : L),
    Submodule.Quotient.mk_eq_zero] at ha
  have : L.subtype ((a : ℤ) • (⟨v, hv⟩ : L)) ∈ M := ha
  simpa using this

/-- A saturated sublattice of `ℤ^ι` of rank `r` with all successive minima bounded by
`1 ≤ s j` is one of finitely many. -/
theorem prim_lat_window_finiteU {ι : Type*} [Fintype ι] [DecidableEq ι] (r : ℕ) (s : Fin r → ℝ)
    (hs : ∀ j, 1 ≤ s j) :
    ({L : Submodule ℤ (ι → ℤ) | IsPrimLat L ∧ rk L = r ∧
      ∀ j : Fin r, lam L (j.1 + 1) ≤ s j}).Finite := by
  classical
  -- A common bound `C` for all the `s j`, and `N = C + 1`.
  set C : ℝ := max 1 (∑ j : Fin r, max (s j) 1) with hCdef
  have hsC : ∀ j : Fin r, s j ≤ C := by
    intro j
    have h1 : s j ≤ max (s j) 1 := le_max_left _ _
    have h2 : max (s j) 1 ≤ ∑ k : Fin r, max (s k) 1 :=
      Finset.single_le_sum
        (fun k _ => le_trans zero_le_one (le_max_right (s k) 1)) (Finset.mem_univ j)
    have h3 : (∑ k : Fin r, max (s k) 1) ≤ C := by
      rw [hCdef]; exact le_max_right _ _
    exact le_trans h1 (le_trans h2 h3)
  set N : ℝ := C + 1 with hNdef
  have hCN : C < N := by rw [hNdef]; linarith
  -- Every admissible lattice contains `r` independent vectors of norm `≤ N`.
  have hwit : ∀ (L : Submodule ℤ (ι → ℤ)), IsPrimLat L → rk L = r →
      (∀ j : Fin r, lam L (j.1 + 1) ≤ s j) →
      ∃ f : Fin r → ι → ℤ, (∀ i, f i ∈ L) ∧ LinearIndependent ℤ f ∧ ∀ i, eNorm (f i) ≤ N := by
    intro L _ hrk hlam
    rcases Nat.eq_zero_or_pos r with h0 | hpos
    · subst h0
      obtain ⟨f, hfL, hfLI⟩ := exists_linIndep_card L (i := 0) (by omega)
      exact ⟨f, hfL, hfLI, fun i => i.elim0⟩
    · have hj : (⟨r - 1, by omega⟩ : Fin r).1 + 1 = r := by
        simp only [Fin.val_mk]; omega
      have hle : lam L r ≤ C := by
        rw [← hj]
        exact le_trans (hlam ⟨r - 1, by omega⟩) (hsC ⟨r - 1, by omega⟩)
      obtain ⟨f, hfL, hfLI, hfb⟩ :=
        lam_witness L (i := r) (le_of_eq hrk.symm) (ρ := N) (by linarith)
      exact ⟨f, hfL, hfLI, hfb⟩
  -- Finiteness of the set of admissible tuples.
  have htupleFin : Finite {f : Fin r → ι → ℤ // ∀ i, eNorm (f i) ≤ N} := by
    have hpi : (Set.univ.pi fun _ : Fin r => {v : ι → ℤ | eNorm v ≤ N}).Finite :=
      Set.Finite.pi fun _ => MDBasic.finite_eNorm_le N
    refine Set.finite_coe_iff.mp (hpi.subset ?_)
    intro f hf
    rw [Set.mem_univ_pi]
    intro i
    exact hf i
  -- The map sending each admissible lattice to a chosen tuple of short independent vectors.
  let g : {L : Submodule ℤ (ι → ℤ) // IsPrimLat L ∧ rk L = r ∧ ∀ j : Fin r, lam L (j.1 + 1) ≤ s j} →
      {f : Fin r → ι → ℤ // ∀ i, eNorm (f i) ≤ N} :=
    fun L => ⟨Classical.choose (hwit L.1 L.2.1 L.2.2.1 L.2.2.2),
      (Classical.choose_spec (hwit L.1 L.2.1 L.2.2.1 L.2.2.2)).2.2⟩
  -- `g` is injective: a saturated lattice of rank `r` is the saturation of the `ℤ`-span of any
  -- `r` independent vectors it contains.
  have hinj : Function.Injective g := by
    intro L L' h
    have hval : (g L).1 = (g L').1 := congrArg Subtype.val h
    refine Subtype.ext (le_antisymm ?_ ?_)
    · intro v hv
      have hLI : LinearIndependent ℤ (g L).1 :=
        (Classical.choose_spec (hwit L.1 L.2.1 L.2.2.1 L.2.2.2)).2.1
      have hmemL : ∀ i, (g L).1 i ∈ L.1 :=
        (Classical.choose_spec (hwit L.1 L.2.1 L.2.2.1 L.2.2.2)).1
      have hmemL' : ∀ i, (g L).1 i ∈ L'.1 := by
        intro i
        have h' : (g L').1 i ∈ L'.1 :=
          (Classical.choose_spec (hwit L'.1 L'.2.1 L'.2.2.1 L'.2.2.2)).1 i
        rwa [← hval] at h'
      obtain ⟨m, hm0, hmv⟩ := primLatTorsionU r (g L).1 L.1 hLI hmemL L.2.2.1 v hv
      exact L'.2.1 v m hm0 ((Submodule.span_le.mpr (Set.range_subset_iff.mpr hmemL')) hmv)
    · intro v hv
      have hLI : LinearIndependent ℤ (g L').1 :=
        (Classical.choose_spec (hwit L'.1 L'.2.1 L'.2.2.1 L'.2.2.2)).2.1
      have hmemL' : ∀ i, (g L').1 i ∈ L'.1 :=
        (Classical.choose_spec (hwit L'.1 L'.2.1 L'.2.2.1 L'.2.2.2)).1
      have hmemL : ∀ i, (g L').1 i ∈ L.1 := by
        intro i
        have h' : (g L).1 i ∈ L.1 :=
          (Classical.choose_spec (hwit L.1 L.2.1 L.2.2.1 L.2.2.2)).1 i
        rwa [hval] at h'
      obtain ⟨m, hm0, hmv⟩ := primLatTorsionU r (g L').1 L'.1 hLI hmemL' L'.2.2.1 v hv
      exact L.2.1 v m hm0 ((Submodule.span_le.mpr (Set.range_subset_iff.mpr hmemL)) hmv)
  exact Set.finite_coe_iff.mp (@Finite.of_injective _ _ htupleFin g hinj)

/-- The set of primitive sublattices of `ℤ^ι` of rank `r` whose successive minima are
bounded by `s` is finite.

This is the un-normalized form of `prim_lat_window_finiteU` (which assumes `1 ≤ s j`):
replacing each bound `s j` by `max (s j) 1` only enlarges the set, and the enlarged set is
finite by `prim_lat_window_finiteU`. -/
theorem Tset_finite {ι : Type*} [Fintype ι] [DecidableEq ι] (r : ℕ) (s : Fin r → ℝ) :
    ({L : Submodule ℤ (ι → ℤ) | IsPrimLat L ∧ rk L = r ∧
      ∀ j : Fin r, lam L (j.1 + 1) ≤ s j}).Finite := by
  refine Set.Finite.subset
    (prim_lat_window_finiteU r (fun j => max (s j) 1) (fun j => le_max_right _ _)) ?_
  intro L hL
  exact ⟨hL.1, hL.2.1, fun j => le_trans (hL.2.2 j) (le_max_left _ _)⟩

end Work.HP.Sig2
