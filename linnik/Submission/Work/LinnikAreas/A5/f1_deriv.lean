import Mathlib
import Submission.Work.LinnikAreas.A5.Basic

open scoped Topology

namespace Work.LinnikAreas.A5

theorem f1_deriv (K lam : ℝ) {t : ℝ} (ht : t < K) :
    deriv (Work.LinnikAreas.A5.f1 K lam) t = -lam * Real.cosh ((K - t) * lam) := by
  have hmem : Set.Iio K ∈ 𝓝 t := isOpen_Iio.mem_nhds ht
  have hev : f1 K lam =ᶠ[𝓝 t] fun s => Real.sinh ((K - s) * lam) := by
    filter_upwards [hmem] with s hs
    exact f1_of_le hs.le
  rw [hev.deriv_eq]
  have hg : HasDerivAt (fun s : ℝ => (K - s) * lam) (-lam) t := by
    have h1 : HasDerivAt (fun s : ℝ => K - s) (0 - 1) t :=
      (hasDerivAt_const (x := t) K).sub (hasDerivAt_id t)
    have h2 := h1.mul_const lam
    simpa using h2
  have h3 : deriv (fun s : ℝ => Real.sinh ((K - s) * lam)) t
      = Real.cosh ((K - t) * lam) * (-lam) := hg.sinh.deriv
  rw [h3]
  ring

end Work.LinnikAreas.A5
