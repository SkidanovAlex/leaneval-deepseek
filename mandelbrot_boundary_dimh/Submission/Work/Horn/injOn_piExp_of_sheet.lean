import Mathlib
import Submission.Work.Interfaces.HornParts
import Submission.Work.Horn.basic

namespace Work.Horn

open Set Metric

/-- If `E` is `T`-equivariant on the `T`-invariant set `X ⊇ W` and `E '' W` lies in a ball of
radius `ε` with `2ε < 1`, then `π` is injective on `W`. -/
theorem injOn_piExp_of_sheet {E : ℂ → ℂ} {X W : Set ℂ} {c : ℂ} {ε : ℝ}
    (hX : MandelDim.IsTInvariant X) (hE : ∀ w ∈ X, E (w + 1) = E w + 1)
    (hWX : W ⊆ X) (hε : 2 * ε < 1)
    (hW : ∀ v ∈ W, E v ∈ Metric.ball c ε) :
    Set.InjOn MandelDim.piExp W := by
  intro v hv w hw hvw
  -- two points of `W` with the same `π`-image differ by an integer
  obtain ⟨k, hk⟩ := MandelDim.piExp_eq_iff.mp hvw
  -- `T`-equivariance transports the integral shift to `E`
  have hEk : E v = E w + k := by
    rw [hk]
    exact MandelDim.E_add_int hX (fun u hu _ => hE u hu) (hWX hw) k
  have hvε : ‖E v - c‖ < ε := by
    have h := hW v hv
    rwa [Metric.mem_ball, dist_eq_norm] at h
  have hwε : ‖E w - c‖ < ε := by
    have h := hW w hw
    rwa [Metric.mem_ball, dist_eq_norm] at h
  -- hence the two images are closer than `1`, so the integer must vanish
  have hsmall : ‖((k : ℤ) : ℂ)‖ < 1 := by
    have hEq : E v - E w = ((k : ℤ) : ℂ) := by rw [hEk]; ring
    have h1 : ‖E v - E w‖ ≤ ‖E v - c‖ + ‖E w - c‖ := by
      have hsub : E v - c - (E w - c) = E v - E w := by ring
      calc ‖E v - E w‖ = ‖E v - c - (E w - c)‖ := by rw [hsub]
        _ ≤ ‖E v - c‖ + ‖E w - c‖ := norm_sub_le _ _
    rw [hEq] at h1
    linarith
  have hk0 : k = 0 := by
    rw [Complex.norm_intCast] at hsmall
    rw [← Int.cast_abs (R := ℝ)] at hsmall
    exact Int.abs_lt_one_iff.mp (by exact_mod_cast hsmall)
  rw [hk, hk0]
  simp

end Work.Horn
