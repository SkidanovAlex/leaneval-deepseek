import Mathlib
import Submission.Work.EKLRelCross.flower
import Submission.Work.EKLContract.All

/-!
# `Work.EKLRelCross.atom_flower_local` — the atom of the flower σ-algebra, cross-section
property only on a displacement box

This is the *local* version of `Work.EKLRelCross.atom_flower`.  There, the cross-section
property is assumed for *all* `u ∈ U`; here it is only assumed for the `u` that lie in a
displacement box `V b`:

`hCS : ∀ z ∈ C, ∀ u ∈ U, u ∈ V b → u • z ∈ C → u = 1`.

The price paid is the hypothesis

`hprod : ∀ w ∈ U, w ∈ Vinv δ → ∀ u ∈ U, u ∈ V δ → w * u ∈ V b`,

which guarantees that whenever `w ∈ Vinv δ ∩ U` carries a plaque point `u • z'`
(`u ∈ V δ ∩ U`, `z' ∈ C`) back into `C`, the product `w * u` really does lie in `V b`, so that
`hCS` applies and gives `w * u = 1` exactly as in the global case.

Consequently the key computation `flowerSet_mem_iff_of_mem_local` is identical in shape to
`flowerSet_mem_iff_of_mem`, and the rest of the argument is a verbatim transcription of the
proof of `atom_flower` with `B` renamed to `C`.
-/

open MeasureTheory Topology Filter
open scoped ENNReal

set_option linter.unusedVariables false

noncomputable section

namespace Work.EKLRelCross

open Work.EKLContract

/-- **The flower membership of a plaque point (local version).**

If `u ∈ V δ ∩ U` and `z' ∈ C`, then `u • z'` lies in the flower set `flowerSet U δ C W`
exactly when `z' ∈ W`.

The forward implication is where the hypotheses `hCS` and `hprod` are used: any
`w ∈ Vinv δ ∩ U` carrying `u • z'` back into `C` has `w * u ∈ V b`, hence `w * u = 1` by `hCS`,
and therefore `w • (u • z') = z'`. -/
lemma flowerSet_mem_iff_of_mem_local {U : Subgroup SL3} {C W : Set X3} {b δ : ℝ}
    (hCS : ∀ z ∈ C, ∀ u ∈ U, u ∈ V b → u • z ∈ C → u = 1)
    (hprod : ∀ w ∈ U, w ∈ Vinv δ → ∀ u ∈ U, u ∈ V δ → w * u ∈ V b)
    {u : SL3} (hu : u ∈ V δ ∩ (U : Set SL3)) {z' : X3} (hz' : z' ∈ C) :
    u • z' ∈ flowerSet U δ C W ↔ z' ∈ W := by
  constructor
  · rintro ⟨w, ⟨hwV, hwU⟩, hwy⟩
    have hmemC : (w * u) • z' ∈ C := by rw [mul_smul]; exact hwy.1
    have h1 : w * u = 1 :=
      hCS z' hz' (w * u) (U.mul_mem hwU hu.2) (hprod w hwU hwV u hu.2 hu.1) hmemC
    have : w • (u • z') = z' := by rw [← mul_smul, h1, one_smul]
    rw [this] at hwy
    exact hwy.2
  · intro hz'W
    refine ⟨u⁻¹, ⟨?_, U.inv_mem hu.2⟩, ?_⟩
    · show (u⁻¹)⁻¹ ∈ V δ
      rw [inv_inv]
      exact hu.1
    · show u⁻¹ • (u • z') ∈ C ∩ W
      have : u⁻¹ • (u • z') = z' := by rw [← mul_smul, inv_mul_cancel, one_smul]
      rw [this]
      exact ⟨hz', hz'W⟩

theorem atom_flower_local {U : Subgroup Work.EKLContract.SL3} {C : Set Work.EKLContract.X3}
    {b : ℝ}
    (hCS : ∀ z ∈ C, ∀ u ∈ U, u ∈ Work.EKLContract.V b → u • z ∈ C → u = 1)
    {δ : ℝ} (hδ : 0 < δ)
    (hprod : ∀ w ∈ U, w ∈ Work.EKLRelCross.Vinv δ → ∀ u ∈ U, u ∈ Work.EKLContract.V δ →
      w * u ∈ Work.EKLContract.V b)
    {W : ℕ → Set Work.EKLContract.X3} (hW0 : W 0 = Set.univ)
    (hsep : ∀ z ∈ C, ∀ z' ∈ C, (∀ n, z ∈ W n ↔ z' ∈ W n) → z = z')
    {v : Work.EKLContract.SL3} (hv : v ∈ Work.EKLContract.V δ) (hvU : v ∈ U)
    {z : Work.EKLContract.X3} (hz : z ∈ C) :
    ∀ {x : Work.EKLContract.X3}, x = v • z →
      Work.EKLContract.atom (Work.EKLRelCross.flowerSigma U δ C W) x
        = (fun u : Work.EKLContract.SL3 => u • z) '' (Work.EKLContract.V δ ∩ (U : Set Work.EKLContract.SL3)) := by
  rintro x rfl
  -- The atom at `v • z` is the class of points with the same `(W n)`-membership as `z`.
  have key : ∀ y : X3, y ∈ atom (flowerSigma U δ C W) (v • z)
      ↔ ∀ n, y ∈ flowerSet U δ C (W n) ↔ z ∈ W n := by
    intro y
    rw [show flowerSigma U δ C W
        = MeasurableSpace.generateFrom (Set.range (fun n => flowerSet U δ C (W n))) from rfl,
      mem_atom_iff_pattern]
    constructor
    · intro h n
      exact (h _ ⟨n, rfl⟩).trans
        (flowerSet_mem_iff_of_mem_local hCS hprod ⟨hv, hvU⟩ hz)
    · intro h A hA
      obtain ⟨n, rfl⟩ := hA
      exact (h n).trans (flowerSet_mem_iff_of_mem_local hCS hprod ⟨hv, hvU⟩ hz).symm
  ext y
  constructor
  · -- `atom ⊆ (V δ ∩ U) • z`: read off a translate of `y` into `C`, then separate via `W`.
    intro hy
    rw [key] at hy
    have hy0 : y ∈ flowerSet U δ C (W 0) := by rw [hy 0, hW0]; trivial
    obtain ⟨w, ⟨hw, hwU⟩, hwy⟩ := hy0
    set z' : X3 := w • y with hz'def
    have hz'C : z' ∈ C := by rw [hz'def]; exact hwy.1
    have hy_eq : y = w⁻¹ • z' := by rw [hz'def, ← mul_smul, inv_mul_cancel, one_smul]
    have hpat' : ∀ n, y ∈ flowerSet U δ C (W n) ↔ z' ∈ W n := by
      intro n
      rw [hy_eq]
      exact flowerSet_mem_iff_of_mem_local hCS hprod ⟨hw, U.inv_mem hwU⟩ hz'C
    have hz'z : z' = z := hsep z' hz'C z hz (fun n => (hpat' n).symm.trans (hy n))
    refine ⟨w⁻¹, ⟨hw, U.inv_mem hwU⟩, ?_⟩
    rw [← hz'z]
    exact hy_eq.symm
  · -- `(V δ ∩ U) • z ⊆ atom`: every translate of `z` has the same flower pattern.
    rintro ⟨u, ⟨hu, huU⟩, rfl⟩
    rw [key]
    intro n
    exact flowerSet_mem_iff_of_mem_local hCS hprod ⟨hu, huU⟩ hz

end Work.EKLRelCross
