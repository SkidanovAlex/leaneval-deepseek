/-
  annals_wilkies_conjecture, AREA E3K (`Submission.Work.WilE3K`): the **linear algebra core** of
  `Work.WilE3K.ETReg_bad_null`.

  For `E : ETData N (rt+1) n re`, `E.gLast = E.tanFun (Fin.last rt)` is the eliminated arctan
  equation and `E.chart` (see `ETRegDefs.lean`) is the graph chart of its zero set.  The point of
  this file is the *criticality transfer*: at a point `x` of the chart domain, the differential of
  the square system map `E.map` at `E.chart x` is singular if and only if the differential of the
  square chart map `E.chartMap = E.psiMap ∘ E.chart` at `x` is singular:

    `(E.dmap (E.chart x)).det = 0 ↔ (E.dG x).det = 0`.

  The proof is elementary linear algebra.  Writing `A := E.dmap (E.chart x) : W → W`,
  `D := E.dpsi (E.chart x) : W → V` (`V = Fin N → ℝ`), `g := E.dgLast (E.chart x) : W → ℝ` and
  `B := E.dchart x : V → W` (`W = Fin (N+1) → ℝ`), so that `E.dG x = D ∘ B`:

  * `A u = 0 ↔ D u = 0 ∧ g u = 0` (`dmap_eq_zero_iff`), i.e. `ker A = ker D ⊓ ker g`;
  * `g ∘ B = 0` and `ker g = range B` (`dgLast_dchart`, `ker_dgLast_eq_range_dchart`) — both
    inclusions are explicit computations with the row formula `ETData.sum_dTanFun`, and use
    `(E.chart x) E.lastRow = Real.tan (E.ell x)` and `E.dchart x v (E.lastRow.succAbove i) = v i`;
  * `B` is injective (`dchart_injective`);
  * hence `ker A = ⊥ ↔ ker(D ∘ B) = ⊥`, and each side is equivalent to non-singularity of the
    respective determinant (`LinearMap.det_eq_zero_iff_ker_ne_bot`).
-/
import Mathlib
import Submission.Work.WilE3K.ET
import Submission.Work.WilE3K.Elim
import Submission.Work.WilE3K.ETRegDefs
import Submission.Work.WilE3K.contDiff_map_and_det
import Submission.Work.WilE2.khoReg_bad_null

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Classical Topology Filter
namespace Work.WilE3K
open WilkiesConjecture WilkiesDesign WilkiesDesign.E

variable {N rt n re : ℕ}

namespace ETData

variable (E : ETData N (rt + 1) n re)

/-! ## §1. Basic evaluations -/

/-- The explicit evaluation of the derivative `E.dell` of `E.ell`. -/
theorem dell_apply (v : Fin N → ℝ) :
    E.dell v = ∑ j : Fin n, E.lam (Fin.last rt) j * v (E.freeIdx j) := by
  simp only [dell, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul]

/-- The coordinate `E.lastRow` is the `tan` coordinate of the eliminated arctan equation. -/
theorem tanCoord_last_eq_lastRow : E.tanCoord (Fin.last rt) = E.lastRow := by
  apply Fin.ext
  simp [ETData.tanCoord, ETData.lastRow]

/-- The `E.lastRow` row of the Jacobian is the row of the eliminated arctan equation. -/
theorem jac_lastRow_eq (z : Fin (N + 1) → ℝ) (c : Fin (N + 1)) :
    E.jac z E.lastRow c = E.dTanFun (Fin.last rt) z c := by
  rw [← E.tanCoord_last_eq_lastRow, E.jac_tan]

/-! ## §2. The chart differential lies in the kernel of the eliminated row -/

/-- The derivative of the eliminated equation annihilates the differential of the chart. -/
theorem dgLast_dchart (x : Fin N → ℝ) (v : Fin N → ℝ) :
    E.dgLast (E.chart x) (E.dchart x v) = 0 := by
  have hden : (1 : ℝ) + Real.tan (E.ell x) ^ 2 ≠ 0 := by positivity
  have hfree : ∀ i : Fin n, E.dchart x v (E.freeCoord i) = v (E.freeIdx i) := by
    intro i
    rw [← E.succAbove_freeIdx i, E.dchart_apply_succAbove x (E.freeIdx i) v]
  have h1 : E.dgLast (E.chart x) (E.dchart x v)
      = (1 / (1 + Real.tan (E.ell x) ^ 2)) * ((1 + Real.tan (E.ell x) ^ 2) * E.dell v)
        - ∑ i : Fin n, E.lam (Fin.last rt) i * v (E.freeIdx i) := by
    rw [E.dgLast_apply, E.djac_apply]
    rw [Finset.sum_congr rfl (fun c _ => by rw [E.jac_lastRow_eq])]
    rw [E.sum_dTanFun (Fin.last rt) (E.chart x) (E.dchart x v)]
    rw [E.tanCoord_last_eq_lastRow, E.chart_lastRow,
      E.dchart_apply_lastRow x v]
    rw [Finset.sum_congr rfl (fun i _ => by rw [hfree i])]
  rw [h1]
  have hone : (1 / (1 + Real.tan (E.ell x) ^ 2)) * ((1 + Real.tan (E.ell x) ^ 2) * E.dell v)
      = E.dell v := by
    rw [one_div, ← mul_assoc, inv_mul_cancel₀ hden, one_mul]
  rw [hone, E.dell_apply]
  exact sub_self _

/-- The kernel of the eliminated row is exactly the range of the chart differential.  Both
inclusions are explicit computations with the row formula `ETData.sum_dTanFun`. -/
theorem ker_dgLast_eq_range_dchart (x : Fin N → ℝ) :
    (E.dgLast (E.chart x)).ker = (E.dchart x).range := by
  refine le_antisymm ?_ ?_
  · intro u hu
    have hu' : E.dgLast (E.chart x) u = 0 := LinearMap.mem_ker.mp hu
    refine ⟨fun i => u (E.lastRow.succAbove i), ?_⟩
    funext r
    by_cases hr : r = E.lastRow
    · subst hr
      change E.dchart x (fun i => u (E.lastRow.succAbove i)) E.lastRow = u E.lastRow
      rw [E.dchart_apply_lastRow x (fun i => u (E.lastRow.succAbove i))]
      have hval : u E.lastRow
          = (1 + Real.tan (E.ell x) ^ 2) *
              ∑ i : Fin n, E.lam (Fin.last rt) i * u (E.freeCoord i) := by
        have h0 : (1 / (1 + Real.tan (E.ell x) ^ 2)) * u E.lastRow
            - ∑ i : Fin n, E.lam (Fin.last rt) i * u (E.freeCoord i) = 0 := by
          have h1 : E.dgLast (E.chart x) u = 0 := hu'
          rw [E.dgLast_apply, E.djac_apply] at h1
          rw [Finset.sum_congr rfl (fun c _ => by rw [E.jac_lastRow_eq])] at h1
          rw [E.sum_dTanFun (Fin.last rt) (E.chart x) u] at h1
          rwa [E.tanCoord_last_eq_lastRow, E.chart_lastRow] at h1
        have h2 : (1 / (1 + Real.tan (E.ell x) ^ 2)) * u E.lastRow
            = ∑ i : Fin n, E.lam (Fin.last rt) i * u (E.freeCoord i) := sub_eq_zero.mp h0
        have h3 := congrArg (fun r => (1 + Real.tan (E.ell x) ^ 2) * r) h2
        have hone : (1 + Real.tan (E.ell x) ^ 2) * (1 / (1 + Real.tan (E.ell x) ^ 2)) = 1 := by
          rw [one_div, mul_inv_cancel₀ (by positivity : (1 : ℝ) + Real.tan (E.ell x) ^ 2 ≠ 0)]
        rw [← mul_assoc, hone, one_mul] at h3
        exact h3
      rw [hval]
      congr 1
      rw [E.dell_apply]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [E.succAbove_freeIdx]
    · obtain ⟨j, hj⟩ : ∃ j : Fin N, E.lastRow.succAbove j = r :=
        ⟨E.outIdx r hr, E.succAbove_outIdx r hr⟩
      rw [← hj]
      change E.dchart x (fun i => u (E.lastRow.succAbove i)) (E.lastRow.succAbove j)
        = u (E.lastRow.succAbove j)
      rw [E.dchart_apply_succAbove x j (fun i => u (E.lastRow.succAbove i))]
  · intro w hw
    obtain ⟨v, hv⟩ := LinearMap.mem_range.mp hw
    rw [← hv]
    exact LinearMap.mem_ker.mpr (E.dgLast_dchart x v)

/-- The differential of the chart is injective. -/
theorem dchart_injective (x : Fin N → ℝ) : Function.Injective (E.dchart x) := by
  intro u v huv
  funext i
  have h := congrFun huv (E.lastRow.succAbove i)
  rw [E.dchart_apply_succAbove x i u, E.dchart_apply_succAbove x i v] at h
  exact h

/-! ## §3. The kernel of the system differential -/

/-- The system differential vanishes exactly when the remaining-system differential and the
eliminated row vanish. -/
theorem dmap_eq_zero_iff (z u : Fin (N + 1) → ℝ) :
    E.dmap z u = 0 ↔ E.dpsi z u = 0 ∧ E.dgLast z u = 0 := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · funext i
      have h' : E.djac z (E.lastRow.succAbove i) u = 0 := by
        have h2 := congrFun h (E.lastRow.succAbove i)
        simpa only [E.dmap_apply, Pi.zero_apply] using h2
      simpa [E.dpsi_apply] using h'
    · have h' : E.djac z E.lastRow u = 0 := by
        have h2 := congrFun h E.lastRow
        simpa only [E.dmap_apply, Pi.zero_apply] using h2
      simpa [E.dgLast_apply] using h'
  · rintro ⟨h1, h2⟩
    funext r
    by_cases hr : r = E.lastRow
    · subst hr
      simpa [E.dmap_apply, E.dgLast_apply] using h2
    · obtain ⟨j, hj⟩ : ∃ j : Fin N, E.lastRow.succAbove j = r :=
        ⟨E.outIdx r hr, E.succAbove_outIdx r hr⟩
      rw [← hj]
      have h3 := congrFun h1 j
      simpa [E.dmap_apply, E.dpsi_apply] using h3

/-! ## §4. The determinant of the explicit system differential -/

/-- The determinant of the explicit system differential is the determinant of the symbolic
Jacobian. -/
theorem dmap_det_eq_jac_det (z : Fin (N + 1) → ℝ) :
    (E.dmap z).det = (E.jac z).det := by
  rw [Work.WilE2.clm_det_eq]
  congr 1
  ext i j
  show (E.dmap z) (Pi.single j (1 : ℝ) : Fin (N + 1) → ℝ) i = E.jac z i j
  rw [E.dmap_apply, E.djac_apply]
  have hterm : ∀ c, E.jac z i c * (Pi.single j (1 : ℝ) : Fin (N + 1) → ℝ) c
      = (if c = j then E.jac z i c else 0) := by
    intro c
    by_cases h : c = j
    · subst h; rw [Pi.single_eq_same, mul_one, if_pos rfl]
    · rw [Pi.single_eq_of_ne h, mul_zero, if_neg h]
  rw [Finset.sum_congr rfl (fun c _ => hterm c), Finset.sum_ite_eq']
  simp

/-! ## §5. The criticality transfer -/

/-- **The criticality transfer.**  The differential of the square system map at a point of the
graph chart is singular exactly when the differential of the square chart map is singular there. -/
theorem dmap_det_eq_zero_iff_dG_det (x : Fin N → ℝ) :
    (E.dmap (E.chart x)).det = 0 ↔ (E.dG x).det = 0 := by
  have hker : (E.dmap (E.chart x)).ker = ⊥ ↔ (E.dG x).ker = ⊥ := by
    constructor
    · intro hA
      rw [Submodule.eq_bot_iff] at hA ⊢
      intro v hv
      have hv' : E.dG x v = 0 := hv
      have h1 : E.dmap (E.chart x) (E.dchart x v) = 0 :=
        (E.dmap_eq_zero_iff (E.chart x) (E.dchart x v)).mpr ⟨hv', E.dgLast_dchart x v⟩
      have h2 : E.dchart x v = 0 := hA (E.dchart x v) h1
      exact E.dchart_injective x (by simp [h2])
    · intro hG
      rw [Submodule.eq_bot_iff] at hG ⊢
      intro u hu
      have hu' : E.dmap (E.chart x) u = 0 := hu
      obtain ⟨hD, hg⟩ := (E.dmap_eq_zero_iff (E.chart x) u).mp hu'
      have hmem : u ∈ (E.dchart x).range := by
        rw [← E.ker_dgLast_eq_range_dchart x]
        exact LinearMap.mem_ker.mpr hg
      obtain ⟨v, hv⟩ := LinearMap.mem_range.mp hmem
      have hD' : E.dG x v = 0 := by
        change E.dpsi (E.chart x) (E.dchart x v) = 0
        rw [show E.dchart x v = u from hv]
        exact hD
      have hv0 : v = 0 := hG v (LinearMap.mem_ker.mpr hD')
      rw [← hv, hv0, map_zero]
  rw [show (E.dmap (E.chart x)).det = LinearMap.det (E.dmap (E.chart x)).toLinearMap from rfl,
    show (E.dG x).det = LinearMap.det (E.dG x).toLinearMap from rfl,
    LinearMap.det_eq_zero_iff_ker_ne_bot, LinearMap.det_eq_zero_iff_ker_ne_bot]
  exact not_congr hker

end ETData

end Work.WilE3K
