import Mathlib
import Submission.Work.Diff.STE.B3.SymCalcStep6.conj_cut_comm_lapPow_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.B3.SymCalcStep7

/-- **The conjugate Laplacian power is subtractive** on smooth `1`-periodic functions: `P_k (u − v) = P_k u − P_k v` for `P_k = conjLapPow k T T'`. Route: `Work.Diff.STE.B3.SymCalcStep6.conjLapPow_add` applied to `u − v` and `v`, using `u = (u − v) + v`; `conjLapPow_add` needs smoothness and `1`-periodicity of both arguments (`u − v` inherits both), the smoothness of `T'`, the periodicity of `T`, and the inverse identities `T' ∘ T = id`, `T ∘ T' = id`. -/
theorem conjLapPow_sub {ι : Type*} [Fintype ι] [DecidableEq ι]
    (T T' : (ι → ℝ) → (ι → ℝ)) (hT' : ContDiff ℝ (⊤ : ℕ∞) T')
    (hTper : ∀ (i : ι) (x : ι → ℝ), T (x + Pi.single i 1) = T x + Pi.single i 1)
    (hTinv1 : ∀ x : ι → ℝ, T' (T x) = x) (hTinv2 : ∀ y : ι → ℝ, T (T' y) = y) (k : ℕ)
    {u v : (ι → ℝ) → ℂ} (hu : ContDiff ℝ (⊤ : ℕ∞) u) (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    (hup : Work.Diff.STE.Periodic1 u) (hvp : Work.Diff.STE.Periodic1 v) :
    Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T' (fun x => u x - v x)
      = Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T' u
        - Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T' v := by
  -- `u - v` inherits smoothness and `1`-periodicity from `u` and `v`.
  have hw : ContDiff ℝ (⊤ : ℕ∞) (fun x => u x - v x) := hu.sub hv
  have hwp : Work.Diff.STE.Periodic1 (fun x => u x - v x) := by
    intro i x
    show u (x + Pi.single i 1) - v (x + Pi.single i 1) = u x - v x
    rw [hup i x, hvp i x]
  -- Additivity of `P_k` applied to the two summands `u - v` and `v`.
  have hadd :=
    Work.Diff.STE.B3.SymCalcStep6.conjLapPow_add T T' hT' hTper hTinv1 hTinv2 k
      hw hv hwp hvp
  -- `(u - v) + v = u`.
  have hsum : (fun x => u x - v x) + v = u := by
    funext x
    show u x - v x + v x = u x
    ring
  rw [hsum] at hadd
  rw [hadd]
  abel

end Work.Diff.STE.B3.SymCalcStep7
