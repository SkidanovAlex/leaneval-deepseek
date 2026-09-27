import Mathlib
import Submission.Work.EKLC6Core.PlaqueCellDefs
import Submission.Work.EKLC6Core.exists_base_sat_sep
import Submission.Work.EKLC6Core.atom_MSig
import Submission.Work.EKLC6Core.CellBaseCore
import Submission.Work.EKLC6Core.atom_MSig2
import Submission.Work.EKLC6Core.uminus_isHoro

/-!
# `Work.EKLC6Core.cell_facts_of_base`

Every raw cell family `S : CellBase μ U` carries the σ-algebraic/analytic content packaged in
`CellFacts`: choosing a countable family `O` of open sets of `SL₃(ℝ)` whose *membership pattern*
`m ↦ (∃ u ∈ U, u * g ∈ O m)` determines the left `U`-coset (`Work.EKLC6Core.exists_base_sat_sep`,
which only needs `U` closed — here `U = Uminus t`, closed by `Work.EKLC6Core.uminus_isHoro`), the
clipped generators are open, and the atoms of the generated σ-algebra inside a cell are pieces of
`U`-orbits (`Work.EKLC6Core.atom_MSig2`).

## Proof

* `exists_open_sep` — the separating family `O` of `CellFacts.hOsep`: `exists_base_sat_sep`
  provides a countable family of open sets such that the pattern `m ↦ (z ∈ sat U (O m))`
  determines the left coset of `z`; translating membership in `sat U (O m)` into the
  `∃ u ∈ U, u * g ∈ O m` form (`Work.EKLC6Core.mem_sat_iff`) turns its conclusion
  `w ∈ sat U {z}` into `w = u * z`.
* `measurableSet_genC2` (`CellBaseCore`) — the clipped generators are open because `satU U (O m)`
  and the lifted ball are open and `mkX` is an open map; hence `CellFacts.hmeas`.
* `atom_MSig2` (`Submission/Work/EKLC6Core/atom_MSig2.lean`) — the atom identity for a raw cell
  family; it is the `CellBase` analogue of `Work.EKLC6Core.atom_MSig` and consumes exactly the
  fields `hopen`, `hdisj`, `hsub`, `hinj`, `hδpos` of `CellBase`.  An in-file proof of the same
  identity is available as `Work.EKLC6Core.atom_MSig2_self` (`CellBaseCore`), so the development
  is independent of that module.
* `shape_MSig2` / `shape_open_of_base` / `shape_bdd_of_base` — the shape of an atom of `MSig2` at
  a point `y` of a cell is `{u ∈ U | u * lift2 S k y ∈ lifted (δ k) (g k) ∧ u • y ∈ S.Q k}`,
  which is the trace on `U` of an open set and is entrywise bounded (`u` is the product of an
  element of the lifted ball — bounded entries — with `(lift2 S k y)⁻¹`).
* `atom_orb_of_base` — the atoms of `MSig2` inside a cell lie in the `U`-orbit (Pisa 6.3(iii)).

None of this uses the fields `hgood`/`hthin` of the richer `CellSys`, which is why the raw
`CellBase` suffices.
-/

open MeasureTheory Filter Topology
open scoped ENNReal Pointwise

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

noncomputable section

namespace Work.EKLC6Core

open Work.EKLContract

variable {μ : MeasureTheory.Measure X3} {U : Subgroup SL3}

/-! ## The separating family of open cylinder sets -/

/-- For `U = Uminus t` (a closed subgroup) there is a countable family of open sets of `SL₃(ℝ)`
whose membership pattern in the form `∃ u ∈ U, u * g ∈ O m` determines the left `U`-coset of `g`:
this is the hypothesis `CellFacts.hOsep`. -/
theorem exists_open_sep (t : Fin 3 → ℝ) :
    ∃ O : ℕ → Set SL3, (∀ m, IsOpen (O m)) ∧
      ∀ g g' : SL3,
        (∀ m, (∃ u ∈ Uminus t, u * g ∈ O m) ↔ (∃ u ∈ Uminus t, u * g' ∈ O m)) →
        ∃ u ∈ Uminus t, g' = u * g := by
  obtain ⟨O, hOopen, -, hsep⟩ := exists_base_sat_sep (Uminus t) (uminus_isHoro t).1.1
  refine ⟨O, hOopen, ?_⟩
  intro g g' hgg'
  have hpat : ∀ m, (g ∈ sat (Uminus t) (O m) ↔ g' ∈ sat (Uminus t) (O m)) := by
    intro m
    rw [mem_sat_iff, mem_sat_iff]
    exact hgg' m
  have hmem : g' ∈ sat (Uminus t) ({g} : Set SL3) := hsep g g' hpat
  rw [mem_sat_iff] at hmem
  obtain ⟨u, huU, hug⟩ := hmem
  have hug' : u * g' = g := Set.mem_singleton_iff.mp hug
  exact ⟨u⁻¹, (Uminus t).inv_mem huU, by rw [← hug', inv_mul_cancel_left]⟩

/-! ## The shape of an atom of `MSig2` inside a cell -/

/-- **The shape of an atom of `MSig2`.** -/
theorem shape_MSig2 (S : CellBase μ U) (O : ℕ → Set SL3)
    (hOsep : ∀ g g' : SL3,
      (∀ m, (∃ u ∈ U, u * g ∈ O m) ↔ (∃ u ∈ U, u * g' ∈ O m)) → ∃ u ∈ U, g' = u * g)
    (hmeas : ∀ k m, MeasurableSet (genC2 U S.Q S.δ S.g O k m))
    {k : ℕ} {y : X3} (hy : y ∈ S.Q k) (hfree : ∀ u ∈ U, u • y = y → u = 1) :
    shape (MSig2 U S.Q S.δ S.g O) U y
      = {u : SL3 | u ∈ U ∧ u * lift2 S k y ∈ lifted (S.δ k) (S.g k) ∧ u • y ∈ S.Q k} := by
  have hatom := atom_MSig2 S O hOsep hmeas hy
  have hℓmk : mkX (lift2 S k y) = y := mkX_lift2 S k hy
  ext u
  constructor
  · rintro ⟨huU, huA⟩
    rw [hatom] at huA
    obtain ⟨huA', huyQ⟩ := huA
    obtain ⟨g, hgmem, hgk⟩ := huA'
    obtain ⟨hgcos, hgl⟩ := hgmem
    obtain ⟨u₀, hu₀U, hgu⟩ := hgcos
    have hgl' : u₀ * lift2 S k y ∈ lifted (S.δ k) (S.g k) := by rw [← hgu]; exact hgl
    have huy : u • y = u₀ • y := by
      rw [← hgk, hgu, ← smul_mkX_eq u₀ (lift2 S k y), hℓmk]
    have hfix : (u₀⁻¹ * u) • y = y := by rw [mul_smul, huy, inv_smul_smul]
    have hu_eq : u = u₀ := by
      have h1 : u₀⁻¹ * u = 1 := hfree _ (U.mul_mem (U.inv_mem hu₀U) huU) hfix
      calc u = u₀ * (u₀⁻¹ * u) := (mul_inv_cancel_left u₀ u).symm
        _ = u₀ * 1 := by rw [h1]
        _ = u₀ := mul_one u₀
    refine ⟨huU, ?_, huyQ⟩
    rw [hu_eq]
    exact hgl'
  · rintro ⟨huU, hgl, huyQ⟩
    refine ⟨huU, ?_⟩
    rw [hatom]
    refine ⟨⟨u * lift2 S k y, ⟨⟨u, huU, rfl⟩, hgl⟩, ?_⟩, huyQ⟩
    rw [← smul_mkX_eq u (lift2 S k y), hℓmk]

/-- The shape of an atom of `MSig2` at a free point is the trace of an open set of `SL₃(ℝ)`. -/
theorem shape_open_of_base (S : CellBase μ U) (O : ℕ → Set SL3)
    (hOsep : ∀ g g' : SL3,
      (∀ m, (∃ u ∈ U, u * g ∈ O m) ↔ (∃ u ∈ U, u * g' ∈ O m)) → ∃ u ∈ U, g' = u * g)
    (hmeas : ∀ k m, MeasurableSet (genC2 U S.Q S.δ S.g O k m))
    {k : ℕ} {y : X3} (hy : y ∈ S.Q k) (hfree : ∀ u ∈ U, u • y = y → u = 1) :
    ∃ W : Set SL3, IsOpen W ∧ shape (MSig2 U S.Q S.δ S.g O) U y = W ∩ (U : Set SL3) := by
  refine ⟨(fun g : SL3 => g * lift2 S k y) ⁻¹' lifted (S.δ k) (S.g k)
    ∩ (fun g : SL3 => g • y) ⁻¹' S.Q k, ?_, ?_⟩
  · refine IsOpen.inter ?_ ?_
    · exact (isOpen_lifted' (S.δ k) (S.g k)).preimage (by fun_prop)
    · exact (S.hopen k).preimage (by fun_prop)
  · have h := shape_MSig2 S O hOsep hmeas hy hfree
    rw [h]
    ext u
    constructor
    · rintro ⟨huU, h1, h2⟩
      exact ⟨⟨h1, h2⟩, huU⟩
    · rintro ⟨⟨h1, h2⟩, huU⟩
      exact ⟨huU, h1, h2⟩

/-- The shape of an atom of `MSig2` at a free point is entrywise bounded. -/
theorem shape_bdd_of_base (S : CellBase μ U) (O : ℕ → Set SL3)
    (hOsep : ∀ g g' : SL3,
      (∀ m, (∃ u ∈ U, u * g ∈ O m) ↔ (∃ u ∈ U, u * g' ∈ O m)) → ∃ u ∈ U, g' = u * g)
    (hmeas : ∀ k m, MeasurableSet (genC2 U S.Q S.δ S.g O k m))
    {k : ℕ} {y : X3} (hy : y ∈ S.Q k) (hfree : ∀ u ∈ U, u • y = y → u = 1) :
    ∃ C : ℝ, ∀ u ∈ shape (MSig2 U S.Q S.δ S.g O) U y, ∀ i j, |u i j| ≤ C := by
  obtain ⟨M, hM0, hM⟩ := exists_entries_bound_lifted (S.δ k) (S.hδpos k) (S.g k)
  obtain ⟨M', hM'0, hM'⟩ := exists_entries_bound_inv (lift2 S k y)
  refine ⟨3 * M * M', ?_⟩
  intro u hu i j
  rw [shape_MSig2 S O hOsep hmeas hy hfree] at hu
  obtain ⟨huU, hgl, -⟩ := hu
  have hcoe : ((u : SL3) : Matrix (Fin 3) (Fin 3) ℝ)
      = ((u * lift2 S k y : SL3) : Matrix (Fin 3) (Fin 3) ℝ)
        * (((lift2 S k y)⁻¹ : SL3) : Matrix (Fin 3) (Fin 3) ℝ) := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel_right]
  rw [hcoe]
  exact mul_entries_le i j (fun a b => hM _ hgl a b) (fun a b => hM' a b) hM0 hM'0

/-- The atoms of `MSig2` inside a cell lie in the `U`-orbit. -/
theorem atom_orb_of_base (S : CellBase μ U) (O : ℕ → Set SL3)
    (hOsep : ∀ g g' : SL3,
      (∀ m, (∃ u ∈ U, u * g ∈ O m) ↔ (∃ u ∈ U, u * g' ∈ O m)) → ∃ u ∈ U, g' = u * g)
    (hmeas : ∀ k m, MeasurableSet (genC2 U S.Q S.δ S.g O k m)) :
    ∀ k (y : X3), y ∈ S.Q k →
      atom (MSig2 U S.Q S.δ S.g O) y ⊆ (fun u : SL3 => u • y) '' (U : Set SL3) := by
  intro k y hy z hz
  rw [atom_MSig2 S O hOsep hmeas hy] at hz
  obtain ⟨⟨w, ⟨hwcos, -⟩, hwz⟩, -⟩ := hz
  obtain ⟨u, huU, hwu⟩ := hwcos
  refine ⟨u, huU, ?_⟩
  rw [← hwz, hwu, ← smul_mkX_eq u (lift2 S k y), mkX_lift2 S k hy]

/-! ## The target -/

theorem cell_facts_of_base {μ : MeasureTheory.Measure Work.EKLContract.X3}
    (t : Fin 3 → ℝ) (S : Work.EKLC6Core.CellBase μ (Work.EKLC6Core.Uminus t)) :
    Nonempty (Work.EKLC6Core.CellFacts t S) := by
  obtain ⟨O, hOopen, hOsep⟩ := exists_open_sep t
  have hmeas : ∀ k m, MeasurableSet (genC2 (Uminus t) S.Q S.δ S.g O k m) :=
    fun k m => measurableSet_genC2 S O hOopen k m
  exact ⟨{ O := O
           hOopen := hOopen
           hOsep := hOsep
           hmeas := hmeas
           hshape_open := fun k y hy hfree => shape_open_of_base S O hOsep hmeas hy hfree
           hshape_bdd := fun k y hy hfree => shape_bdd_of_base S O hOsep hmeas hy hfree
           hatom_orb := fun k y hy => atom_orb_of_base S O hOsep hmeas k y hy }⟩

end Work.EKLC6Core
