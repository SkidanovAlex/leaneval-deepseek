import Mathlib
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.B3.perTransferDef
import Submission.Work.Diff.STE.B3.pdVec_integral_le_CSq
import Submission.Work.Diff.STE.B3.integral_pd_comp_le_tsupport
import Submission.Work.Diff.STE.B3.SymCalcStep8.periodization_compact_csq_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The local chart transfer `perTransfer c T` is bounded on `Hᵗ`

This is the "assembly" step of the local layer of `ENormB_pair_J_commutator_v2`: for a *fixed*
smooth, compactly supported amplitude `c` and a *fixed* smooth map `T` whose differential is
invertible and which is injective on the support of `c`, the local transfer

`perTransfer c T W z = Σ' m : ι → ℤ, c (z + iVec m) * W (T (z + iVec m))`

(the periodisation of `z ↦ c z * W (T z)`) is bounded on the Sobolev space `Hᵗ`, uniformly in the
smooth `1`-periodic `W`:

`CSq t (fourierCoeff (perTransfer c T W)) ≤ C * CSq t (fourierCoeff W)`.

⚠ No uniformity in `c`, `T` (or in the support of `c`) is claimed — that is impossible (the
periodisation of `K` lattice translates of a bump has `H⁰` norm of order `√K`, while its physical
`L²` norm is translation invariant); here `c`, `T` are fixed parameters, so `C` may depend on them.

## Route

Two analytic inputs, both independent of `W`:

* `Work.Diff.STE.B3.integral_pd_comp_le_tsupport`: for each multi-index `l : Fin m → ι` the physical
  `L²` norm of `∂^m_l (c · (W ∘ T))` is bounded by a constant (depending on `c, T, m, l`) times the
  sum of the `unitCube`-`L²` norms of all partial derivatives of `W` of order `≤ m`; this is the
  chain rule `pdVecMulCompExpansion` together with the change of variables
  `integralCompPeriodicLe` on `tsupport c` (the single place where `hinj` and `hdet` are used, via
  `IsCompact (tsupport c)`).
* `Work.Diff.STE.B3.SymCalcStep8.CSq_period_le_integral_deriv_compact`: for a fixed compact `K`,
  `CSq t` of the Fourier coefficients of the periodisation of a smooth `Φ` with `tsupport Φ ⊆ K` is
  bounded by a constant times the sum of the whole-space `L²` norms of all its partial derivatives
  of order `≤ t`.
* `Work.Diff.STE.B3.pdVec_integral_le_CSq`: `∫_{unitCube} ‖∂^j_{l'} W‖² ≤ C * CSq t (fourierCoeff W)`
  for `j ≤ t`.

Feeding `Φ = c · (W ∘ T)` (with `tsupport Φ ⊆ tsupport c`) through these three and summing over the
finitely many multi-indices gives the claim. -/

namespace Work.Diff.STE.B3.SymCalcStep8

open MeasureTheory BigOperators

theorem perTransfer_csq_le_of_support {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c : (ι → ℝ) → ℂ) (hc : ContDiff ℝ (⊤ : ℕ∞) c) (hcs : HasCompactSupport c)
    (T : (ι → ℝ) → (ι → ℝ)) (hT : ContDiff ℝ (⊤ : ℕ∞) T)
    (hinj : Set.InjOn T (tsupport c))
    (hdet : ∀ z ∈ tsupport c, (fderiv ℝ T z).det ≠ 0) (t : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ W : (ι → ℝ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) W → Work.Diff.STE.Periodic1 W →
      Work.Diff.STE.CSq t (Work.Diff.STE.fourierCoeff (Work.Diff.STE.B3.perTransfer c T W))
        ≤ C * Work.Diff.STE.CSq t (Work.Diff.STE.fourierCoeff W) := by
  classical
  obtain ⟨C2, hC2nn, hC2b⟩ :=
    Work.Diff.STE.B3.SymCalcStep8.periodization_compact_csq_le (ι := ι) t (tsupport c) hcs
  obtain ⟨C1, hC1nn, hC1b⟩ := Work.Diff.STE.B3.pdVec_integral_le_CSq (ι := ι) t
  choose Cd hCdnn hCdb using fun (m : ℕ) (l : Fin m → ι) =>
    Work.Diff.STE.B3.integral_pd_comp_le_tsupport (ι := ι) T hT c hc hcs hinj hdet m l
  set N2 : ℝ := ∑ m ∈ Finset.range (t + 1), ∑ _l : Fin m → ι, (1 : ℝ) with hN2def
  set N3 : ℝ := ∑ m ∈ Finset.range (t + 1), ∑ l : Fin m → ι, Cd m l with hN3def
  have hN2nn : 0 ≤ N2 := by
    rw [hN2def]
    exact Finset.sum_nonneg fun m _ => Finset.sum_nonneg fun _ _ => by norm_num
  have hN3nn : 0 ≤ N3 := by
    rw [hN3def]
    exact Finset.sum_nonneg fun m _ => Finset.sum_nonneg fun l _ => hCdnn m l
  refine ⟨C2 * N3 * (N2 * C1), ?_, ?_⟩
  · exact mul_nonneg (mul_nonneg hC2nn hN3nn) (mul_nonneg hN2nn hC1nn)
  · intro W hW hWper
    set Φ : (ι → ℝ) → ℂ := fun z => c z * W (T z) with hΦdef
    have hΦsm : ContDiff ℝ (⊤ : ℕ∞) Φ := hc.mul (hW.comp hT)
    have hΦts : tsupport Φ ⊆ tsupport c := by
      have hsub : Function.support Φ ⊆ Function.support c := by
        intro z hz
        rw [Function.mem_support] at hz ⊢
        intro hc0
        exact hz (by rw [hΦdef]; simp [hc0])
      exact closure_mono hsub
    set H : ℝ := ∑ j ∈ Finset.range (t + 1), ∑ l' : Fin j → ι,
      ∫ x in Work.Diff.STE.unitCube (ι := ι), ‖Work.Diff.STE.pdVec j l' W x‖ ^ 2 with hHdef
    have hHnn : 0 ≤ H := by
      rw [hHdef]
      exact Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun l' _ =>
        integral_nonneg fun x => sq_nonneg _
    have hkey : ∀ (m : ℕ) (hm : m ≤ t) (l : Fin m → ι),
        ∫ z : ι → ℝ, ‖Work.Diff.STE.pdVec m l Φ z‖ ^ 2 ≤ Cd m l * H := by
      intro m hm l
      have h1 := hCdb m l W hW hWper
      have h1' : ∫ z : ι → ℝ, ‖Work.Diff.STE.pdVec m l Φ z‖ ^ 2 ≤
          Cd m l * (∑ j ∈ Finset.range (m + 1), ∑ l' : Fin j → ι,
            ∫ x in Work.Diff.STE.unitCube (ι := ι), ‖Work.Diff.STE.pdVec j l' W x‖ ^ 2) := by
        rw [hΦdef]
        exact h1
      refine h1'.trans (mul_le_mul_of_nonneg_left ?_ (hCdnn m l))
      rw [hHdef]
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
      · intro j hj
        rw [Finset.mem_range] at hj ⊢
        omega
      · intro j _ _
        exact Finset.sum_nonneg fun l' _ => integral_nonneg fun x => sq_nonneg _
    have hsum1 : (∑ m ∈ Finset.range (t + 1), ∑ l : Fin m → ι,
        ∫ z : ι → ℝ, ‖Work.Diff.STE.pdVec m l Φ z‖ ^ 2) ≤ N3 * H := by
      calc (∑ m ∈ Finset.range (t + 1), ∑ l : Fin m → ι,
            ∫ z : ι → ℝ, ‖Work.Diff.STE.pdVec m l Φ z‖ ^ 2)
          ≤ ∑ m ∈ Finset.range (t + 1), ∑ l : Fin m → ι, Cd m l * H :=
            Finset.sum_le_sum fun m hm => Finset.sum_le_sum fun l _ =>
              hkey m (by have := Finset.mem_range.mp hm; omega) l
        _ = N3 * H := by
            rw [hN3def, Finset.sum_mul]
            exact Finset.sum_congr rfl fun m _ => by rw [Finset.sum_mul]
    have hsum2 : H ≤ N2 * (C1 * Work.Diff.STE.CSq t (Work.Diff.STE.fourierCoeff W)) := by
      calc H = ∑ j ∈ Finset.range (t + 1), ∑ l' : Fin j → ι,
            ∫ x in Work.Diff.STE.unitCube (ι := ι), ‖Work.Diff.STE.pdVec j l' W x‖ ^ 2 := hHdef
        _ ≤ ∑ j ∈ Finset.range (t + 1), ∑ l' : Fin j → ι,
              (1 : ℝ) * (C1 * Work.Diff.STE.CSq t (Work.Diff.STE.fourierCoeff W)) :=
            Finset.sum_le_sum fun j hj => Finset.sum_le_sum fun l' _ => by
              have := hC1b W hW hWper j (by have := Finset.mem_range.mp hj; omega) l'
              simpa using this
        _ = N2 * (C1 * Work.Diff.STE.CSq t (Work.Diff.STE.fourierCoeff W)) := by
            rw [hN2def]
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro j _
            rw [Finset.sum_mul]
    have hmain := hC2b Φ hΦsm hΦts
    have hEq : Work.Diff.STE.B3.perTransfer c T W
        = fun z : ι → ℝ => ∑' m : ι → ℤ, Φ (z + Work.Diff.STE.iVec m) := by
      funext z
      simp only [Work.Diff.STE.B3.perTransfer, hΦdef]
    rw [hEq]
    calc Work.Diff.STE.CSq t (Work.Diff.STE.fourierCoeff (fun z : ι → ℝ =>
            ∑' m : ι → ℤ, Φ (z + Work.Diff.STE.iVec m)))
        ≤ C2 * (∑ m ∈ Finset.range (t + 1), ∑ l : Fin m → ι,
            ∫ z : ι → ℝ, ‖Work.Diff.STE.pdVec m l Φ z‖ ^ 2) := hmain
      _ ≤ C2 * (N3 * H) := mul_le_mul_of_nonneg_left hsum1 hC2nn
      _ ≤ C2 * (N3 * (N2 * (C1 * Work.Diff.STE.CSq t (Work.Diff.STE.fourierCoeff W)))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsum2 hN3nn) hC2nn
      _ = C2 * N3 * (N2 * C1) * Work.Diff.STE.CSq t (Work.Diff.STE.fourierCoeff W) := by ring

end Work.Diff.STE.B3.SymCalcStep8
