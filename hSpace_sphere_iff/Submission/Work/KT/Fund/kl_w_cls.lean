import Mathlib
import Submission.Work.KT.Fund.Kappa
import Submission.Work.KT.Fund.kl_defs
import Submission.Work.KT.Fund.kl_wh_defs
import Submission.Work.KT.Fund.kappa_const
import Submission.Work.KT.Fund.kappa_homotopic
import Submission.Work.KT.Fund.isUnit_matrix_forall
import Submission.Work.KT.Fund.klWh_slice0
import Submission.Work.KT.Fund.klWh_slice1
import Submission.Work.KT.Fund.klWh_isUnit

/-!
# `Work.KT.Fund.kl_w_cls` — the clutched class of the "outside" factor `klW` is trivial

For `b`, `E` matrices over `C(X, ℂ)` (in the intended application `E` is the inside spectral
projection of `b`) such that the straight-line family

  `H_t = t z (1 - E) + (1 - E) b + E`   (`t ∈ [0,1]`, `‖z‖ = 1`)

is pointwise invertible, the "outside" factor

  `w = klW X n b E = E + z (1 - E) + (1 - E) b`

has trivial clutched class:

  `kappa X n w = cls (Mat.one C(X × S², ℂ) n)`.

The argument is a homotopy of units:

* at `t = 0` the family is the `z`-independent matrix `E + (1 - E) b` — a unit by `hout` at
  `t = 0`, `z = 1` (`isUnit_klW0`), and the pulled-back unit `w₀ = pullMat X (E + (1-E)b)` has
  trivial clutched class by `Work.KT.Fund.kappa_const`;
* at `t = 1` the family is `w = klW X n b E` (`klWh_slice1`);
* the family is a unit throughout (`klWh_isUnit`), so the homotopy invariance of the clutched class
  (`Work.KT.Fund.kappa_homotopic`) gives `kappa w = kappa w₀ = cls (Mat.one ... n)`.

The homotopy matrix itself, and its value `klWh_eval` at a point, live in `Work.KT.Fund.kl_wh_defs`;
the two slices are `Work.KT.Fund.klWh_slice0`, `Work.KT.Fund.klWh_slice1`.
-/

namespace Work.KT.Fund

/-- The `t = 0` (and `z = 1`) endpoint `klW0 = E + (1 - E) * b` of the homotopy is a unit. -/
theorem isUnit_klW0 (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (n : ℕ) (b E : Matrix (Fin n) (Fin n) C(X, ℂ))
    (hout : ∀ (x : X) (t : ℝ) (z : ℂ), 0 ≤ t → t ≤ 1 → ‖z‖ = 1 →
      IsUnit ((((t : ℂ) * z) • (1 - E) + (1 - E) * b + E).map (fun f => f x))) :
    IsUnit (E + (1 - E) * b) := by
  rw [add_comm E ((1 - E) * b)]
  refine (isUnit_matrix_forall n ((1 - E) * b + E)).mpr (fun x => ?_)
  have h := hout x 0 1 (le_refl 0) zero_le_one (by simp)
  simpa using h

theorem kl_w_cls (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (n : ℕ) (b E : Matrix (Fin n) (Fin n) C(X, ℂ)) (hE : E * E = E) (hc : E * b = b * E)
    (hout : ∀ (x : X) (t : ℝ) (z : ℂ), 0 ≤ t → t ≤ 1 → ‖z‖ = 1 →
      IsUnit ((((t : ℂ) * z) • (1 - E) + (1 - E) * b + E).map (fun f => f x)))
    (w : (Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))ˣ)
    (hw : (w : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ)) = Work.KT.Fund.klW X n b E) :
    Work.KT.Fund.kappa X n w = Work.KT.cls (Work.KT.Mat.one C(X × S2, ℂ) n) := by
  classical
  -- the `t = 0`, `z = 1` endpoint `E + (1 - E) * b` is a unit
  have hunit0 : IsUnit (E + (1 - E) * b) := isUnit_klW0 X n b E hout
  obtain ⟨g₀, hg₀⟩ := hunit0
  -- the pulled-back unit `w₀ = pullMat (E + (1 - E) * b)` over `C(X × S¹, ℂ)`
  let w₀ : (Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))ˣ := Units.map (KC.pullHomM X n) g₀
  have hw₀ : (w₀ : Matrix (Fin n) (Fin n) C(X × Sph ℂ, ℂ))
      = pullMat X (E + (1 - E) * b) := by
    change KC.pullHomM X n (g₀ : Matrix (Fin n) (Fin n) C(X, ℂ))
      = pullMat X (E + (1 - E) * b)
    rw [← KC.pullMat_eq_pullHomM, hg₀]
  -- `kappa` of a pulled-back unit is the trivial class
  have hconst : kappa X n w₀ = Work.KT.cls (Work.KT.Mat.one C(X × S2, ℂ) n) :=
    kappa_const X n g₀ w₀ (by rw [hw₀, hg₀])
  -- the homotopy `klWh` runs through units from `w₀` to `w`
  obtain ⟨H, hH⟩ := klWh_isUnit X n b E hout
  have hhom : kappa X n w₀ = kappa X n w :=
    kappa_homotopic X n w₀ w H
      (by rw [hH]; exact (klWh_slice0 X n b E).trans hw₀.symm)
      (by rw [hH]; exact (klWh_slice1 X n b E).trans hw.symm)
  exact hhom.symm.trans hconst

end Work.KT.Fund
