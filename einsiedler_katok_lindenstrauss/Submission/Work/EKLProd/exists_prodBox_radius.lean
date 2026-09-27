import Mathlib
import Submission.Work.EKLProd.prodPlaqueAux
import Submission.Work.EKLProd.sl3EntryBox_compact

/-!
# A uniform product-box radius over `H ∩ V b`

For closed subgroups `T, U ≤ H ≤ SL₃(ℝ)` with `H = T · U`, `T ⊓ U = ⊥` and `T` normalising `U`,
every `h ∈ H` has a *unique* decomposition `h = t · u` with `t ∈ T`, `u ∈ U`, and the two
coordinates depend continuously on `h` (`Work.EKLProd.tCoord`, `Work.EKLProd.uCoord`).

The point of this module is that the coordinates are **uniformly bounded** on the piece of `H`
that lies in the displacement neighbourhood `V b` of the identity: since `V b` is entrywise
bounded, `H ∩ closure (V b)` is a closed and bounded — hence compact — subset of `SL₃(ℝ)`, and a
continuous function on a compact set is bounded above.  Consequently there is a radius `R` with

`∀ h ∈ H, h ∈ V b → h ∈ prodBox T U R = (V R ∩ T) * (V R ∩ U)`.

The work is done once, in the general form `exists_bound_of_continuous_on_V`: for a closed
subgroup `H ≤ SL₃(ℝ)` and a continuous `f : ↥H → ℝ`, the values of `f` on the set of `h ∈ H` with
`h ∈ V b` are bounded above.  It is then applied to the sum of the absolute deviations of the
entries of `tCoord h` (resp. `uCoord h`) from those of the identity, which dominates each single
entry.
-/

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

noncomputable section

namespace Work.EKLProd

open Work.EKLContract

/-- The sum of the absolute deviations of the entries of `φ x` from those of the identity matrix
is continuous whenever `φ` is. -/
theorem continuous_sum_abs_entry_dev {α : Type*} [TopologicalSpace α] (φ : α → SL3)
    (hφ : Continuous φ) :
    Continuous fun x : α => ∑ p : Fin 3 × Fin 3,
      |(φ x) p.1 p.2 - (1 : Matrix (Fin 3) (Fin 3) ℝ) p.1 p.2| := by
  fun_prop

/-- **Boundedness of a continuous function on `H ∩ V b`.**  For a closed subgroup `H` of
`SL₃(ℝ)`, a real number `b` and a continuous function `f` on `H`, the values of `f` at the points
of `H` lying in the displacement neighbourhood `V b` are bounded above.

The set `{g : SL₃(ℝ) | ∀ i j, |g i j - 1 i j| ≤ b}` containing `V b` is closed, and
`H ∩ {|g i j - 1 i j| ≤ b}` is contained in the entrywise box `|g i j| ≤ b + 1`, hence compact;
its preimage in `↥H` (a closed subobject) is compact as well, being the image under the closed
embedding `Subtype.val`.  A continuous function on a compact set is bounded above. -/
theorem exists_bound_of_continuous_on_V {H : Subgroup SL3} (hHc : IsClosed (H : Set SL3))
    (b : ℝ) (f : ↥H → ℝ) (hf : Continuous f) :
    ∃ M : ℝ, ∀ h : ↥H, (h : SL3) ∈ V b → f h ≤ M := by
  classical
  set F : Set SL3 := {g : SL3 | ∀ i j, |g i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ b}
    with hFdef
  have hFclosed : IsClosed F := by
    rw [hFdef]
    have hEq : {g : SL3 | ∀ i j, |g i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ b}
        = ⋂ (i : Fin 3), ⋂ (j : Fin 3),
            {g : SL3 | |g i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ b} := by
      ext g; simp
    rw [hEq]
    refine isClosed_iInter fun i => isClosed_iInter fun j => ?_
    exact isClosed_le (by fun_prop) continuous_const
  have hBcomp : IsCompact {g : SL3 | ∀ i j, -(b + 1) ≤ g i j ∧ g i j ≤ b + 1} :=
    sl3EntryBox_compact _ _
  have hsub : (H : Set SL3) ∩ F ⊆ {g : SL3 | ∀ i j, -(b + 1) ≤ g i j ∧ g i j ≤ b + 1} := by
    rintro g ⟨hgH, hgF⟩ i j
    have hgF' : |g i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ b := hgF i j
    have hone : |(1 : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ 1 := by
      rw [Matrix.one_apply]; split_ifs <;> simp
    have h1 : |g i j| ≤ b + 1 := by
      calc |g i j| = |(g i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j)
                          + (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| := by rw [sub_add_cancel]
        _ ≤ |g i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j|
              + |(1 : Matrix (Fin 3) (Fin 3) ℝ) i j| := abs_add_le _ _
        _ ≤ b + 1 := by linarith
    exact abs_le.mp h1
  have hHFcomp : IsCompact ((H : Set SL3) ∩ F) :=
    hBcomp.of_isClosed_subset (hHc.inter hFclosed) hsub
  set KH : Set ↥H := {h : ↥H | (h : SL3) ∈ F} with hKHdef
  have hKHcomp : IsCompact KH := by
    have himg : (Subtype.val : ↥H → SL3) '' KH = (H : Set SL3) ∩ F := by
      ext g; constructor
      · rintro ⟨h, hh, rfl⟩; exact ⟨h.2, hh⟩
      · rintro ⟨hgH, hgF⟩; exact ⟨⟨g, hgH⟩, hgF, rfl⟩
    rw [Topology.IsEmbedding.subtypeVal.isCompact_iff, himg]
    exact hHFcomp
  have hCS : CompactSpace ↥KH := isCompact_iff_compactSpace.mp hKHcomp
  haveI := hCS
  have hcont : ContinuousOn (fun x : ↥KH => f x.1) Set.univ :=
    (hf.comp continuous_subtype_val).continuousOn
  obtain ⟨M, hM⟩ := isCompact_univ.bddAbove_image (f := fun x : ↥KH => f x.1) hcont
  refine ⟨M, fun h hh => ?_⟩
  have hF : (h : SL3) ∈ F := by
    rw [hFdef]; intro i j; exact le_of_lt (hh i j)
  exact hM (show f h ∈ (fun x : ↥KH => f x.1) '' Set.univ from
    ⟨⟨h, hF⟩, Set.mem_univ _, rfl⟩)

/-- **A uniform product-box radius.**  For closed subgroups `T, U ≤ H ≤ SL₃(ℝ)` with `H = T · U`,
`T ⊓ U = ⊥` and `T` normalising `U`, and every real `b`, there is a radius `R ≥ 1` such that
every `h ∈ H ∩ V b` lies in the product box `prodBox T U R = (V R ∩ T) * (V R ∩ U)`. -/
theorem exists_prodBox_radius {H T U : Subgroup Work.EKLContract.SL3}
    (hTH : T ≤ H) (hUH : U ≤ H)
    (hnorm : ∀ g ∈ T, ∀ u ∈ U, g * u * g⁻¹ ∈ U)
    (hcop : ∀ h ∈ H, ∃ g ∈ T, ∃ u ∈ U, h = g * u)
    (hdisj : ∀ g ∈ T, g ∈ U → g = 1)
    (hHc : IsClosed (H : Set Work.EKLContract.SL3))
    (hTc : IsClosed (T : Set Work.EKLContract.SL3))
    (hUc : IsClosed (U : Set Work.EKLContract.SL3))
    (b : ℝ) :
    ∃ R : ℝ, 1 ≤ R ∧ ∀ h : Work.EKLContract.SL3,
      h ∈ (H : Set Work.EKLContract.SL3) → h ∈ Work.EKLContract.V b →
        h ∈ Work.EKLProd.prodBox T U R := by
  classical
  -- the two coordinates of the decomposition are continuous on `H`
  have htc : Continuous (fun h : ↥H =>
      ((tCoord hTH hUH hnorm hcop hdisj hHc hTc hUc h : ↥T) : SL3)) :=
    continuous_subtype_val.comp (tCoord_continuous hTH hUH hnorm hcop hdisj hHc hTc hUc)
  have huc : Continuous (fun h : ↥H =>
      ((uCoord hTH hUH hnorm hcop hdisj hHc hTc hUc h : ↥U) : SL3)) :=
    continuous_subtype_val.comp (uCoord_continuous hTH hUH hnorm hcop hdisj hHc hTc hUc)
  -- their entrywise deviations from the identity are uniformly bounded on `H ∩ V b`
  obtain ⟨Mt, hMt⟩ := exists_bound_of_continuous_on_V hHc b
    (fun h : ↥H => ∑ p : Fin 3 × Fin 3,
      |((tCoord hTH hUH hnorm hcop hdisj hHc hTc hUc h : ↥T) : SL3) p.1 p.2
        - (1 : Matrix (Fin 3) (Fin 3) ℝ) p.1 p.2|)
    (continuous_sum_abs_entry_dev _ htc)
  obtain ⟨Mu, hMu⟩ := exists_bound_of_continuous_on_V hHc b
    (fun h : ↥H => ∑ p : Fin 3 × Fin 3,
      |((uCoord hTH hUH hnorm hcop hdisj hHc hTc hUc h : ↥U) : SL3) p.1 p.2
        - (1 : Matrix (Fin 3) (Fin 3) ℝ) p.1 p.2|)
    (continuous_sum_abs_entry_dev _ huc)
  set R : ℝ := max 1 (max (Mt + 1) (Mu + 1)) with hRdef
  refine ⟨R, le_max_left _ _, ?_⟩
  intro h hhH hhV
  have hRb : Mt < R := by
    rw [hRdef]
    have h1 : Mt + 1 ≤ max (Mt + 1) (Mu + 1) := le_max_left _ _
    have h2 : max (Mt + 1) (Mu + 1) ≤ max 1 (max (Mt + 1) (Mu + 1)) := le_max_right _ _
    linarith
  have hRc : Mu < R := by
    rw [hRdef]
    have h1 : Mu + 1 ≤ max (Mt + 1) (Mu + 1) := le_max_right _ _
    have h2 : max (Mt + 1) (Mu + 1) ≤ max 1 (max (Mt + 1) (Mu + 1)) := le_max_right _ _
    linarith
  refine (mem_prodBox_iff hTH hUH hnorm hcop hdisj hHc hTc hUc ⟨h, hhH⟩).mpr ⟨?_, ?_⟩
  · intro i j
    have hle : |((tCoord hTH hUH hnorm hcop hdisj hHc hTc hUc ⟨h, hhH⟩ : ↥T) : SL3) i j
        - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ Mt := by
      have h1 := hMt ⟨h, hhH⟩ hhV
      have h2 : |((tCoord hTH hUH hnorm hcop hdisj hHc hTc hUc ⟨h, hhH⟩ : ↥T) : SL3) i j
          - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j|
          ≤ ∑ p : Fin 3 × Fin 3,
            |((tCoord hTH hUH hnorm hcop hdisj hHc hTc hUc ⟨h, hhH⟩ : ↥T) : SL3) p.1 p.2
              - (1 : Matrix (Fin 3) (Fin 3) ℝ) p.1 p.2| :=
        Finset.single_le_sum (f := fun p : Fin 3 × Fin 3 =>
            |((tCoord hTH hUH hnorm hcop hdisj hHc hTc hUc ⟨h, hhH⟩ : ↥T) : SL3) p.1 p.2
              - (1 : Matrix (Fin 3) (Fin 3) ℝ) p.1 p.2|)
          (fun p _ => abs_nonneg _) (Finset.mem_univ (i, j))
      linarith
    exact lt_of_le_of_lt hle hRb
  · intro i j
    have hle : |((uCoord hTH hUH hnorm hcop hdisj hHc hTc hUc ⟨h, hhH⟩ : ↥U) : SL3) i j
        - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ Mu := by
      have h1 := hMu ⟨h, hhH⟩ hhV
      have h2 : |((uCoord hTH hUH hnorm hcop hdisj hHc hTc hUc ⟨h, hhH⟩ : ↥U) : SL3) i j
          - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j|
          ≤ ∑ p : Fin 3 × Fin 3,
            |((uCoord hTH hUH hnorm hcop hdisj hHc hTc hUc ⟨h, hhH⟩ : ↥U) : SL3) p.1 p.2
              - (1 : Matrix (Fin 3) (Fin 3) ℝ) p.1 p.2| :=
        Finset.single_le_sum (f := fun p : Fin 3 × Fin 3 =>
            |((uCoord hTH hUH hnorm hcop hdisj hHc hTc hUc ⟨h, hhH⟩ : ↥U) : SL3) p.1 p.2
              - (1 : Matrix (Fin 3) (Fin 3) ℝ) p.1 p.2|)
          (fun p _ => abs_nonneg _) (Finset.mem_univ (i, j))
      linarith
    exact lt_of_le_of_lt hle hRc

end Work.EKLProd
