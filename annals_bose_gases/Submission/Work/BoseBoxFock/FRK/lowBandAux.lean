import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.ZMod.ValMinAbs
import Submission.Work.BoseBoxFock.frkCore
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.FRK.lowBandAux` — the lattice-count toolkit of the low band arithmetic

Two self-contained facts used by `Work.BoseBoxFock.FRK.lowBandArith_exists`:

* `card_labVec_lt` — the labels of `Lab N = (ZMod (2N+1))³` whose centred integer
  coordinates `labVec N k` are all bounded by `M` number at most `(2M+1)³` (the cube
  `[-M,M]³ ∩ ℤ³`, which receives `labVec` injectively);
* `abs_labVec_le` — the coordinate bound `|labVec N k i| ≤ ℓ‖kmomLab ℓ N k‖/(2π)`,
  i.e. `‖kmomLab‖` dominates `(2π/ℓ)·‖labVec‖_∞`.

Together they turn any statement of the form "the modes with `‖kmomLab‖ < R`" into the
explicit count `(2⌈ℓR/(2π)⌉+1)³`.
-/

noncomputable section
open scoped BigOperators
open Finset

namespace Work.BoseBoxFock.FRK

open Work.BoseBoxFock

set_option linter.unusedVariables false

/-- The integer cube `[-M, M]³`. -/
def intCube (M : ℕ) : Finset (Fin 3 → ℤ) :=
  Fintype.piFinset (fun _ : Fin 3 => Finset.Icc (-(M : ℤ)) (M : ℤ))

lemma mem_intCube {M : ℕ} {m : Fin 3 → ℤ} : m ∈ intCube M ↔ ∀ i : Fin 3, |m i| ≤ (M : ℤ) := by
  rw [intCube, Fintype.mem_piFinset]
  simp only [Finset.mem_Icc, abs_le]

lemma card_intCube (M : ℕ) : (intCube M).card = (2 * M + 1) ^ 3 := by
  rw [intCube, Fintype.card_piFinset]
  have h1 : ∀ i : Fin 3, (Finset.Icc (-(M : ℤ)) (M : ℤ)).card = 2 * M + 1 := by
    intro i
    rw [Int.card_Icc]
    have h2 : (M : ℤ) + 1 - (-(M : ℤ)) = ((2 * M + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [h2, Int.toNat_natCast]
  rw [Finset.prod_congr rfl (fun i _ => h1 i), Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]

/-- **Lattice count.**  The labels of `Lab N` whose centred integer coordinates are all
`< M` number at most `(2M+1)³`. -/
theorem card_labVec_lt (N M : ℕ) :
    ((Finset.univ : Finset (Lab N)).filter
        (fun k => ∀ i : Fin 3, |labVec N k i| < (M : ℤ))).card ≤ (2 * M + 1) ^ 3 := by
  set sf := (Finset.univ : Finset (Lab N)).filter
    (fun k => ∀ i : Fin 3, |labVec N k i| < (M : ℤ)) with hsf
  have hmap : Set.MapsTo (labVec N) (↑sf : Set (Lab N)) (↑(intCube M) : Set (Fin 3 → ℤ)) := by
    intro k hk
    rw [Finset.mem_coe, hsf, Finset.mem_filter] at hk
    rw [Finset.mem_coe, mem_intCube]
    intro i
    exact le_of_lt (hk.2 i)
  have hinj : Set.InjOn (labVec N) (↑sf : Set (Lab N)) := by
    intro a _ b _ hab
    funext i
    exact ZMod.valMinAbs_inj.mp (congrFun hab i)
  have h := Finset.card_le_card_of_injOn (labVec N) hmap hinj
  rwa [card_intCube] at h

/-- The centred integer coordinates of a label are bounded by `ℓ‖kmomLab ℓ N k‖/(2π)`. -/
lemma abs_labVec_le (ℓ : ℝ) (hℓ : 0 < ℓ) (N : ℕ) (k : Lab N) (i : Fin 3) :
    |(labVec N k i : ℝ)| ≤ ℓ * ‖kmomLab ℓ N k‖ / (2 * Real.pi) := by
  have h1 := PiLp.norm_apply_le (Work.BoseB4.vec (labVec N k)) i
  have h2 : (Work.BoseB4.vec (labVec N k)).ofLp i = 2 * Real.pi * (labVec N k i : ℝ) := rfl
  rw [h2, Real.norm_eq_abs, abs_mul, abs_of_pos (show (0 : ℝ) < 2 * Real.pi by positivity)] at h1
  have h3 : ‖Work.BoseB4.vec (labVec N k)‖ = ℓ * ‖kmomLab ℓ N k‖ := by
    rw [kmomLab, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hℓ.le)]
    field_simp
  rw [h3] at h1
  have hpos : (0 : ℝ) < 2 * Real.pi := by positivity
  rw [le_div_iff₀ hpos]
  linarith [h1]

end Work.BoseBoxFock.FRK
