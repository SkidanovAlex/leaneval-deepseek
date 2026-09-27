import Mathlib
import Submission.Work.EKLC6Core.Basic
import Submission.Work.EKLC6Core.cutHelpers
import Submission.Work.EKLContract.Interfaces

/-!
# `Work.EKLC6Core.ae_transfer_descending_plaque`

Let `μ` be a probability measure on `X₃ = SL₃(ℝ)/SL₃(ℤ)` which is preserved by and *ergodic* for
the diagonal action `φ = (aDiag t ·)`, let `U ≤ SL₃(ℝ)` be horospherical (`IsHoro U`) and let
`A` be a σ-algebra which is *descending* for `φ` (`comap φ A ≤ A`).  If `A` is a plaque algebra
for `U` on a set `Y` of *positive* `μ`-measure (`IsPlaqueAlgebra U Y A`), then the plaque
structure holds `μ`-a.e. on the whole space:

* a.e. `x` has `atom A x ⊆ U • x` (its atom is inside its `U`-orbit);
* a.e. `x` has a neighbourhood of `1` in `U` contained in `shape A U x`, i.e. the atom of `x`
  contains a `U`-neighbourhood of `x` (the atom is a "fat" plaque at `x`).

This is the ergodicity transfer which upgrades the `ε`-version of the geometric construction
(`Work.EKLC6Core.exists_desc_subordinate`, `IsPlaqueAlgebra U Z A` with `μ Zᶜ < ε`) to the
a.e. statements consumed by the entropy computation.

## The two propagation directions

Write `φ x = aDiag t • x` and `φ⁻¹ x = aDiag (-t) • x`.

* **The descent is one-sided.**  From `comap φ A ≤ A` one gets `φ '' atom A x ⊆ atom A (φ x)`
  (`atom_image_subset`): for an `A`-measurable `s ∋ φ x`, the set `φ ⁻¹' s` is `A`-measurable and
  contains `x`, hence contains `atom A x` — no measurability of the atom itself is needed.  Since
  `φ` normalises `U`, this transfers the *orbit clause* `atom ⊆ U • ·` **backwards**:
  `atom A (φ x) ⊆ U • (φ x)` implies `atom A x ⊆ U • x` (`orbit_backward_one`).

* **The shape is open, and conjugation is a homeomorphism of `U`.**  `IsHoro U` gives that
  `Ad(aDiag t) = Ad(aDiag (-t))⁻¹` maps `U` bijectively (both ways) onto itself, so it is a
  homeomorphism of `U` and preserves `1`.  Hence the openness of the shape,
  `∃ O, IsOpen O ∧ 1 ∈ O ∧ O ∩ U ⊆ shape A U x`, transfers **forwards**:
  `∃ O', IsOpen O' ∧ 1 ∈ O' ∧ O' ∩ U ⊆ shape A U (φ x)`
  (`shape_forward_one`, with `O' = {v | aDiag (-t) * v * aDiag t ∈ O}`).

## The conclusion

`W = ⋃_{n ≥ 0} φⁿ '' Y` (written as `⋃_n (φ⁻¹)ⁿ ⁻¹' Y`) and `Z = ⋃_{n ≥ 0} (φⁿ) ⁻¹' Y` are both
Borel, both contain `Y`, and both are `φ`-invariant up to null sets (`φ ⁻¹' W ⊇ W` and
`φ ⁻¹' Z ⊆ Z` with `μ (φ ⁻¹' S) = μ S`); by the ergodicity hypothesis `hqerg` both are conull.
Since every `z ∈ Y` satisfies both clauses (by `IsPlaqueAlgebra`, using `1 ∈ shape A U z`), the
forward propagation of the fatness gives clause 2 on all of `W`, and the backward propagation of
the orbit clause gives clause 1 on all of `Z`.
-/

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

noncomputable section

namespace Work.EKLC6Core

open MeasureTheory Set Topology Filter
open Work.EKLContract

/-! ## Elementary propagation lemmas -/

-- NOTE: the helper lemmas below carry their σ-algebra `A` as an *explicit* binder and the file
-- uses no file-level `variable` of a class type, so that the statement of the main theorem
-- (which has its own `{A : MeasurableSpace X3}` binder) elaborates with exactly the same
-- `MeasurableSpace X₃` instances as in the request (a local hypothesis of class type would
-- otherwise be picked up by typeclass search inside the statement).

/-- `(aDiag t)⁻¹ = aDiag (-t)`. -/
private theorem inv_aDiag (t : Fin 3 → ℝ) : (aDiag t)⁻¹ = aDiag (-t) :=
  inv_eq_of_mul_eq_one_right (aDiag_mul_neg t)

/-- The descent `comap φ A ≤ A` makes `φ` well defined on atoms:
`φ '' atom A x ⊆ atom A (φ x)`. -/
private theorem atom_image_subset {A : MeasurableSpace X3} {φ : X3 → X3}
    (hdesc : MeasurableSpace.comap φ A ≤ A) (x : X3) :
    φ '' atom A x ⊆ atom A (φ x) := by
  intro y hy
  obtain ⟨z, hz, rfl⟩ := hy
  rw [atom, Set.mem_sInter] at hz ⊢
  intro s hs
  exact hz (φ ⁻¹' s)
    ⟨hdesc (φ ⁻¹' s) (MeasurableSpace.measurableSet_comap.mpr ⟨s, hs.1, rfl⟩), hs.2⟩

/-- The `U`-orbit of `aDiag t • x` pulls back along `aDiag t ·` to the `U`-orbit of `x`
(the `A`-normalisation of `U`). -/
private theorem orbit_preimage_eq {U : Subgroup SL3} (hU : IsHoro U) (t : Fin 3 → ℝ) (x : X3) :
    (fun y : X3 => aDiag t • y) ⁻¹' ((fun u : SL3 => u • (aDiag t • x)) '' (U : Set SL3)) =
      (fun u : SL3 => u • x) '' (U : Set SL3) := by
  ext z
  constructor
  · rintro ⟨u, hu, hu'⟩
    change u • (aDiag t • x) = aDiag t • z at hu'
    refine ⟨aDiag (-t) * u * aDiag t, ?_, ?_⟩
    · have h := hU.2.1 (-t) u hu
      rwa [inv_eq_of_mul_eq_one_right (aDiag_neg_mul t)] at h
    · show (aDiag (-t) * u * aDiag t) • x = z
      rw [mul_smul, mul_smul, hu', aDiag_neg_smul]
  · rintro ⟨u, hu, rfl⟩
    refine ⟨aDiag t * u * (aDiag t)⁻¹, hU.2.1 t u hu, ?_⟩
    show (aDiag t * u * (aDiag t)⁻¹) • (aDiag t • x) = aDiag t • (u • x)
    rw [mul_smul, mul_smul, inv_smul_smul]

/-- **Backward transfer of the orbit clause.**  If the atom of `φ x` lies in the `U`-orbit of
`φ x`, then the atom of `x` lies in the `U`-orbit of `x`. -/
private theorem orbit_backward_one {A : MeasurableSpace X3} {U : Subgroup SL3}
    (hU : IsHoro U) (t : Fin 3 → ℝ)
    (hdesc : MeasurableSpace.comap (fun y : X3 => aDiag t • y) A ≤ A) {x : X3}
    (h : atom A (aDiag t • x) ⊆ (fun u : SL3 => u • (aDiag t • x)) '' (U : Set SL3)) :
    atom A x ⊆ (fun u : SL3 => u • x) '' (U : Set SL3) := by
  have h1 : (fun y : X3 => aDiag t • y) '' atom A x ⊆
      (fun u : SL3 => u • (aDiag t • x)) '' (U : Set SL3) :=
    (atom_image_subset hdesc x).trans h
  rw [Set.image_subset_iff] at h1
  rwa [orbit_preimage_eq hU t x] at h1

/-- Iterated backward transfer of the orbit clause. -/
private theorem orbit_backward_iter {A : MeasurableSpace X3} {U : Subgroup SL3}
    (hU : IsHoro U) (t : Fin 3 → ℝ)
    (hdesc : MeasurableSpace.comap (fun y : X3 => aDiag t • y) A ≤ A) :
    ∀ (n : ℕ) {x : X3},
      atom A (((fun y : X3 => aDiag t • y)^[n]) x) ⊆
        (fun u : SL3 => u • (((fun y : X3 => aDiag t • y)^[n]) x)) '' (U : Set SL3) →
      atom A x ⊆ (fun u : SL3 => u • x) '' (U : Set SL3) := by
  intro n
  induction n with
  | zero => intro x h; exact h
  | succ k ih =>
      intro x h
      have h' : atom A (((fun y : X3 => aDiag t • y)^[Nat.succ k]) x) ⊆
          (fun u : SL3 => u • (((fun y : X3 => aDiag t • y)^[Nat.succ k]) x)) ''
            (U : Set SL3) := h
      rw [Function.iterate_succ_apply'] at h'
      exact ih (orbit_backward_one hU t hdesc h')

/-- **Forward transfer of the openness of the shape.**  Conjugation by `aDiag (-t)` is a
homeomorphism of `U` fixing `1`, so a neighbourhood of `1` inside `shape A U x` gives a
neighbourhood of `1` inside `shape A U (aDiag t • x)`. -/
private theorem shape_forward_one {A : MeasurableSpace X3} {U : Subgroup SL3}
    (hU : IsHoro U) (t : Fin 3 → ℝ)
    (hdesc : MeasurableSpace.comap (fun y : X3 => aDiag t • y) A ≤ A) {x : X3}
    (h : ∃ O : Set SL3, IsOpen O ∧ (1 : SL3) ∈ O ∧
      O ∩ (U : Set SL3) ⊆ shape A U x) :
    ∃ O : Set SL3, IsOpen O ∧ (1 : SL3) ∈ O ∧
      O ∩ (U : Set SL3) ⊆ shape A U (aDiag t • x) := by
  obtain ⟨O, hOo, hO1, hOsub⟩ := h
  refine ⟨{v : SL3 | aDiag (-t) * v * aDiag t ∈ O}, ?_, ?_, ?_⟩
  · exact hOo.preimage ((continuous_const.mul continuous_id).mul continuous_const)
  · show aDiag (-t) * (1 : SL3) * aDiag t ∈ O
    rw [mul_one, aDiag_neg_mul]
    exact hO1
  · rintro v ⟨hvO, hvU⟩
    have hwU : aDiag (-t) * v * aDiag t ∈ U := by
      have hh := hU.2.1 (-t) v hvU
      rwa [inv_eq_of_mul_eq_one_right (aDiag_neg_mul t)] at hh
    have hw : aDiag (-t) * v * aDiag t ∈ shape A U x := hOsub ⟨hvO, hwU⟩
    have h1 : aDiag t • ((aDiag (-t) * v * aDiag t) • x) ∈ atom A (aDiag t • x) :=
      atom_image_subset hdesc x ⟨(aDiag (-t) * v * aDiag t) • x, hw.2, rfl⟩
    have h2 : aDiag t • ((aDiag (-t) * v * aDiag t) • x) = v • (aDiag t • x) := by
      rw [← mul_smul, ← mul_smul]
      congr 1
      have hg : aDiag t * (aDiag (-t) * v * aDiag t)
          = aDiag t * aDiag (-t) * (v * aDiag t) := by group
      rw [hg, aDiag_mul_neg, one_mul]
    rw [h2] at h1
    exact ⟨hvU, h1⟩

/-- Iterated forward transfer of the openness of the shape. -/
private theorem shape_forward_iter {A : MeasurableSpace X3} {U : Subgroup SL3}
    (hU : IsHoro U) (t : Fin 3 → ℝ)
    (hdesc : MeasurableSpace.comap (fun y : X3 => aDiag t • y) A ≤ A) :
    ∀ (n : ℕ) {x : X3},
      (∃ O : Set SL3, IsOpen O ∧ (1 : SL3) ∈ O ∧ O ∩ (U : Set SL3) ⊆ shape A U x) →
      ∃ O : Set SL3, IsOpen O ∧ (1 : SL3) ∈ O ∧
        O ∩ (U : Set SL3) ⊆ shape A U (((fun y : X3 => aDiag t • y)^[n]) x) := by
  intro n
  induction n with
  | zero => intro x h; exact h
  | succ k ih =>
      intro x h
      rw [Function.iterate_succ_apply']
      exact shape_forward_one hU t hdesc (ih h)

/-! ## The transfer -/

theorem ae_transfer_descending_plaque
    {μ : MeasureTheory.Measure Work.EKLContract.X3} [MeasureTheory.IsProbabilityMeasure μ]
    {U : Subgroup Work.EKLContract.SL3} (hU : Work.EKLContract.IsHoro U) (t : Fin 3 → ℝ)
    (hmp : MeasureTheory.MeasurePreserving
      (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) μ μ)
    (hqerg : ∀ E : Set Work.EKLContract.X3, MeasurableSet E →
      (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) ⁻¹' E =ᵐ[μ] E →
      μ E = 0 ∨ μ Eᶜ = 0)
    {A : MeasurableSpace Work.EKLContract.X3} {Y : Set Work.EKLContract.X3}
    (hplq : Work.EKLContract.IsPlaqueAlgebra U Y A)
    (hdesc : MeasurableSpace.comap
      (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) A ≤ A)
    (hY : 0 < μ Y) :
    (∀ᵐ x ∂μ, Work.EKLContract.atom A x ⊆
        (fun u : Work.EKLContract.SL3 => u • x) '' (U : Set Work.EKLContract.SL3)) ∧
      (∀ᵐ x ∂μ, ∃ O : Set Work.EKLContract.SL3, IsOpen O ∧ (1 : Work.EKLContract.SL3) ∈ O ∧
        O ∩ (U : Set Work.EKLContract.SL3) ⊆ Work.EKLContract.shape A U x) := by
  classical
  -- every unannotated `MeasurableSet` below refers to the Borel σ-algebra of `X₃`, not to `A`
  letI : MeasurableSpace X3 := Work.EKLContract.instMeasurableSpaceX3
  -- `Y` is Borel measurable
  have hYmeas : MeasurableSet Y := hplq.1 Y hplq.2.2.1
  -- the two conull sets
  set W : Set X3 := ⋃ n : ℕ, ((fun y : X3 => aDiag (-t) • y)^[n]) ⁻¹' Y with hWdef
  set Z : Set X3 := ⋃ n : ℕ, ((fun y : X3 => aDiag t • y)^[n]) ⁻¹' Y with hZdef
  have hWmeas : MeasurableSet W := by
    rw [hWdef]
    exact MeasurableSet.iUnion fun n =>
      hYmeas.preimage (Continuous.measurable ((continuous_const_smul (aDiag (-t))).iterate n))
  have hZmeas : MeasurableSet Z := by
    rw [hZdef]
    exact MeasurableSet.iUnion fun n =>
      hYmeas.preimage (Continuous.measurable ((continuous_const_smul (aDiag t)).iterate n))
  have hYsubW : Y ⊆ W := by
    intro y hy
    rw [hWdef]
    exact Set.mem_iUnion.mpr ⟨0, by simpa using hy⟩
  have hYsubZ : Y ⊆ Z := by
    intro y hy
    rw [hZdef]
    exact Set.mem_iUnion.mpr ⟨0, by simpa using hy⟩
  have hWstep : W ⊆ (fun y : X3 => aDiag t • y) ⁻¹' W := by
    intro x hx
    rw [hWdef] at hx
    rw [Set.mem_preimage, hWdef]
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
    rw [Set.mem_preimage] at hn
    refine Set.mem_iUnion.mpr ⟨Nat.succ n, ?_⟩
    rw [Set.mem_preimage, Function.iterate_succ_apply]
    simpa [aDiag_neg_smul] using hn
  have hZstep : (fun y : X3 => aDiag t • y) ⁻¹' Z ⊆ Z := by
    intro x hx
    rw [Set.mem_preimage, hZdef, Set.mem_iUnion] at hx
    obtain ⟨n, hn⟩ := hx
    rw [Set.mem_preimage] at hn
    rw [hZdef]
    refine Set.mem_iUnion.mpr ⟨Nat.succ n, ?_⟩
    rw [Set.mem_preimage, Function.iterate_succ_apply]
    simpa using hn
  have hWpre : μ ((fun y : X3 => aDiag t • y) ⁻¹' W) = μ W :=
    hmp.measure_preimage hWmeas.nullMeasurableSet
  have hZpre : μ ((fun y : X3 => aDiag t • y) ⁻¹' Z) = μ Z :=
    hmp.measure_preimage hZmeas.nullMeasurableSet
  have hWdiff : μ ((fun y : X3 => aDiag t • y) ⁻¹' W \ W) = 0 := by
    have h1 : μ ((fun y : X3 => aDiag t • y) ⁻¹' W \ W)
        = μ ((fun y : X3 => aDiag t • y) ⁻¹' W) - μ W :=
      MeasureTheory.measure_sdiff (μ := μ) hWstep hWmeas.nullMeasurableSet
        (MeasureTheory.measure_ne_top μ W)
    rw [h1, hWpre]
    simp
  have hZdiff : μ (Z \ (fun y : X3 => aDiag t • y) ⁻¹' Z) = 0 := by
    have h1 : μ (Z \ (fun y : X3 => aDiag t • y) ⁻¹' Z)
        = μ Z - μ ((fun y : X3 => aDiag t • y) ⁻¹' Z) :=
      MeasureTheory.measure_sdiff (μ := μ) hZstep
        (hZmeas.preimage (Continuous.measurable (continuous_const_smul (aDiag t)))).nullMeasurableSet
        (MeasureTheory.measure_ne_top μ ((fun y : X3 => aDiag t • y) ⁻¹' Z))
    rw [h1, hZpre]
    simp
  have hWae : (fun y : X3 => aDiag t • y) ⁻¹' W =ᵐ[μ] W := by
    rw [MeasureTheory.ae_eq_set]
    exact ⟨hWdiff, by rw [Set.sdiff_eq_empty.mpr hWstep]; simp⟩
  have hZae : (fun y : X3 => aDiag t • y) ⁻¹' Z =ᵐ[μ] Z := by
    rw [MeasureTheory.ae_eq_set]
    exact ⟨by rw [Set.sdiff_eq_empty.mpr hZstep]; simp, hZdiff⟩
  have hWcompl : μ Wᶜ = 0 := by
    rcases hqerg W hWmeas hWae with h | h
    · exact absurd h (ne_of_gt (lt_of_lt_of_le hY (MeasureTheory.measure_mono hYsubW)))
    · exact h
  have hZcompl : μ Zᶜ = 0 := by
    rcases hqerg Z hZmeas hZae with h | h
    · exact absurd h (ne_of_gt (lt_of_lt_of_le hY (MeasureTheory.measure_mono hYsubZ)))
    · exact h
  have haeW : ∀ᵐ x ∂μ, x ∈ W := by
    rw [MeasureTheory.ae_iff]
    have h := hWcompl
    rw [Set.compl_def] at h
    exact h
  have haeZ : ∀ᵐ x ∂μ, x ∈ Z := by
    rw [MeasureTheory.ae_iff]
    have h := hZcompl
    rw [Set.compl_def] at h
    exact h
  -- `(aDiag t ·)^[n]` inverts `(aDiag (-t) ·)^[n]`
  have hiter : ∀ n : ℕ, ∀ x : X3,
      ((fun y : X3 => aDiag t • y)^[n]) (((fun y : X3 => aDiag (-t) • y)^[n]) x) = x := by
    intro n
    induction n with
    | zero => intro x; rfl
    | succ k ih =>
        intro x
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply]
        rw [ih ((fun y : X3 => aDiag (-t) • y) x)]
        simpa using aDiag_mul_neg_smul t x
  refine ⟨?_, ?_⟩
  · -- the orbit clause, by backward transfer along `Z`
    filter_upwards [haeZ] with x hx
    rw [hZdef, Set.mem_iUnion] at hx
    obtain ⟨n, hn⟩ := hx
    exact orbit_backward_iter (A := A) hU t hdesc n (hplq.2.2.2 _ hn).2.1
  · -- the openness of the shape, by forward transfer along `W`
    filter_upwards [haeW] with x hx
    rw [hWdef, Set.mem_iUnion] at hx
    obtain ⟨n, hn⟩ := hx
    obtain ⟨O, hOo, hOsh⟩ := (hplq.2.2.2 _ hn).2.2.1
    have h1s : (1 : SL3) ∈ shape A U (((fun y : X3 => aDiag (-t) • y)^[n]) x) := by
      refine ⟨U.one_mem, ?_⟩
      rw [one_smul]
      exact mem_atom_self_c A _
    have h1O : (1 : SL3) ∈ O := by
      rw [hOsh] at h1s
      exact h1s.1
    have hprop := shape_forward_iter (A := A) hU t hdesc n
      (x := ((fun y : X3 => aDiag (-t) • y)^[n]) x)
      ⟨O, hOo, h1O, by intro z hz; rw [hOsh]; exact hz⟩
    rw [hiter n x] at hprop
    exact hprop

end Work.EKLC6Core

end
