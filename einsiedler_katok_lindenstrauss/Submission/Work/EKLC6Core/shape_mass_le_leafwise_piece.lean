import Mathlib
import Submission.Work.EKLC6Core.Basic
import Submission.Work.EKLC6Core.HcondSig_aux
import Submission.Work.EKLC6Core.AtomInfoSetup
import Submission.Work.EKLC6Core.uminus_isHoro

/-!
# `Work.EKLC6Core.shape_mass_le_leafwise_piece`

The leafwise comparison of the masses of the `U`-shapes of an atom of a plaque algebra `A` and of
the corresponding atom of the pull-back algebra `B = comap (aDiag t ·) A`.

## The statement

Let `U ≤ SL₃(ℝ)` be horospherical (`IsHoro U`, in particular `A`-normalised), let `mU` be a
measure on `SL₃(ℝ)` which is invariant under right translations by elements of `U` (tested on
measurable subsets of `U`), let `Z` carry a plaque algebra `A` for `U` whose atoms are open
`U`-plaques, and let `A` be *decreasing* under the pull-back along `aDiag t ·`, `B ≤ A` with
`B = comap (aDiag t ·) A`.

For `x, y` with `aDiag t • x ∈ Z`, `y ∈ Z` and `y ∈ [x]_B`, the theorem asserts

  `mU (shape A U y) ≤ mU (shape B U x ∩ {u | u • x ∈ atom A y})`.

## The proof

* `y ∈ [x]_B` means, since the atom of a pull-back σ-algebra is the preimage of the atom
  (`hcsg_atom_comap`), that `aDiag t • y ∈ [aDiag t • x]_A`.
* As `aDiag t • x ∈ Z` and the atoms of the plaque algebra are `U`-plaques, there is `u ∈ U` with
  `aDiag t • y = u • (aDiag t • x)`; normality of `U` turns `u` into
  `g := (aDiag t)⁻¹ u aDiag t ∈ U`, and then `g • x = y`.
* Since `y ∈ [x]_B` and `B ≤ A`, the `A`-atom of `y` is contained in `[y]_B = [x]_B`
  (`hcsg_atom_mono`, `hcsg_atom_eq_of_mem`).  Hence for every `v ∈ shape A U y` (so `v ∈ U` and
  `v • y ∈ [y]_A`) the element `v * g` satisfies
  `(v * g) • x = v • y ∈ [y]_A ⊆ [x]_B` and `(v * g) • x = v • y ∈ [y]_A`, i.e.

    `shape A U y * {g} ⊆ shape B U x ∩ {u | u • x ∈ atom A y}`.

  Right-invariance of `mU` along `U` gives `mU (shape A U y * {g}) = mU (shape A U y)`
  (`shape A U y` is measurable by `measurableSet_shape`, being an open piece of `U`), and
  monotonicity of `mU` finishes.  In fact both sides are *equal*; the statement only needs `≤`.
-/

open MeasureTheory

namespace Work.EKLC6Core

open Work.EKLContract

theorem shape_mass_le_leafwise_piece {U : Subgroup Work.EKLContract.SL3}
    (hU : Work.EKLContract.IsHoro U)
    {mU : MeasureTheory.Measure Work.EKLContract.SL3}
    (hri : ∀ u ∈ U, ∀ s : Set Work.EKLContract.SL3, s ⊆ (U : Set Work.EKLContract.SL3) →
      MeasurableSet s → mU ((fun g : Work.EKLContract.SL3 => g * u) '' s) = mU s)
    {A : MeasurableSpace Work.EKLContract.X3} {Z : Set Work.EKLContract.X3}
    (hplq : Work.EKLContract.IsPlaqueAlgebra U Z A) (t : Fin 3 → ℝ)
    (hdec : MeasurableSpace.comap
      (fun z : Work.EKLContract.X3 => Work.EKLContract.aDiag t • z) A ≤ A)
    {x y : Work.EKLContract.X3} (hx : Work.EKLContract.aDiag t • x ∈ Z) (hyZ : y ∈ Z)
    (hy : y ∈ Work.EKLContract.atom (MeasurableSpace.comap
      (fun z : Work.EKLContract.X3 => Work.EKLContract.aDiag t • z) A) x) :
    mU (Work.EKLContract.shape A U y) ≤
      mU (Work.EKLContract.shape (MeasurableSpace.comap
        (fun z : Work.EKLContract.X3 => Work.EKLContract.aDiag t • z) A) U x
          ∩ {u : Work.EKLContract.SL3 | u • x ∈ Work.EKLContract.atom A y}) := by
  classical
  -- Step 1: `y ∈ [x]_B` unfolds to `aDiag t • y ∈ [aDiag t • x]_A`.
  have hyT : aDiag t • y ∈ atom A (aDiag t • x) := by
    have hcomap := hcsg_atom_comap (fun z : X3 => aDiag t • z) A x
    have hy' : y ∈ atom (MeasurableSpace.comap (fun z : X3 => aDiag t • z) A) x := hy
    rw [hcomap] at hy'
    exact hy'
  -- Step 2: the `A`-atom of `aDiag t • x` is a `U`-plaque, so `aDiag t • y` is its `U`-translate.
  obtain ⟨u, huU, hug⟩ := (hplq.2.2.2 (aDiag t • x) hx).2.1 hyT
  -- Step 3: the conjugating element `g = (aDiag t)⁻¹ u (aDiag t) ∈ U` moves `x` to `y`.
  let g : SL3 := aDiag (-t) * u * aDiag t
  have hneg : (aDiag (-t))⁻¹ = aDiag t := by
    rw [aDiag_neg_eq_inv, inv_inv]
  have hgU : g ∈ U := by
    have h : aDiag (-t) * u * (aDiag (-t))⁻¹ ∈ U := hU.2.1 (-t) u huU
    rw [hneg] at h
    exact h
  have hug' : u • (aDiag t • x) = aDiag t • y := hug
  have hgx : g • x = y := by
    show (aDiag (-t) * u * aDiag t) • x = y
    rw [mul_smul, mul_smul, hug', ← mul_smul, aDiag_neg_eq_inv, inv_mul_cancel, one_smul]
  -- Step 4: `atom A y ⊆ atom B x`.
  have hyA : atom A y ⊆ atom (MeasurableSpace.comap (fun z : X3 => aDiag t • z) A) x := by
    have h1 : atom A y ⊆ atom (MeasurableSpace.comap (fun z : X3 => aDiag t • z) A) y :=
      hcsg_atom_mono (m := MeasurableSpace.comap (fun z : X3 => aDiag t • z) A) (A := A) hdec y
    have h2 : atom (MeasurableSpace.comap (fun z : X3 => aDiag t • z) A) y
        = atom (MeasurableSpace.comap (fun z : X3 => aDiag t • z) A) x :=
      hcsg_atom_eq_of_mem hy
    rwa [h2] at h1
  -- Step 5: the geometric inclusion.
  have hsub : (fun e : SL3 => e * g) '' shape A U y ⊆
      shape (MeasurableSpace.comap (fun z : X3 => aDiag t • z) A) U x ∩
        {u : SL3 | u • x ∈ atom A y} := by
    rintro w ⟨v, hvE, rfl⟩
    have hvU : v ∈ U := hvE.1
    have hvy : v • y ∈ atom A y := hvE.2
    have hvx : (v * g) • x = v • y := by rw [mul_smul, hgx]
    refine ⟨⟨U.mul_mem hvU hgU, ?_⟩, ?_⟩
    · show (v * g) • x ∈ atom (MeasurableSpace.comap (fun z : X3 => aDiag t • z) A) x
      rw [hvx]
      exact hyA hvy
    · show (v * g) • x ∈ atom A y
      rw [hvx]
      exact hvy
  -- Step 6: right-invariance of `mU` along `U` plus monotonicity.
  have hmeas : MeasurableSet (shape A U y) := measurableSet_shape hU hplq hyZ
  calc mU (shape A U y)
      = mU ((fun e : SL3 => e * g) '' shape A U y) :=
        (hri g hgU (shape A U y) (fun v hv => hv.1) hmeas).symm
    _ ≤ mU (shape (MeasurableSpace.comap (fun z : X3 => aDiag t • z) A) U x ∩
        {u : SL3 | u • x ∈ atom A y}) := measure_mono hsub

end Work.EKLC6Core
