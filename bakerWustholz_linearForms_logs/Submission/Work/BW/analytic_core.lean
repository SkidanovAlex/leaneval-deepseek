import Mathlib
import Submission.Work.BW.ACBase
import Submission.Work.BW.analytic_core_assembly

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open MvPolynomial

namespace Work.BW

/-- BW §14–20 (auxiliary functions, algebraic estimates, Blaschke-product extrapolation,
Kummer descent): if `p` satisfies BW (9) and (12) and `log|Λ| ≤ -9·2^r S D` (BW (10)), then
some polynomial `P` has the vanishing property `PolyOut` required by BW §21. -/
theorem analytic_core {K : Type*} [Field K] [NumberField K] {n r : ℕ} (φ : K →+* ℂ)
    (α : Fin n → K) (b : Fin n → ℤ) (k : Fin n) (c : ℝ) (hst : Standing φ α b k c)
    (hr : 2 ≤ r) (v : ℕ) (L : Fin r → Fin n → ℤ) (α' : Fin r → K) (σ : Fin r → ℝ)
    (hBH : BH φ α b v c r L α' σ) (ι : Fin (r - 1) → Fin n) (hι : IotaOK b k L ι)
    (p : AuxIdx r (ph (hL b (Module.finrank ℚ K)) v) (pD0 r (Module.finrank ℚ K) σ)
        (pDj r (Module.finrank ℚ K) σ) → K)
    (hp0 : p ≠ 0)
    (hp9 : ∀ (s : ℤ), |s| ≤ (pS r (Module.finrank ℚ K) (ph (hL b (Module.finrank ℚ K)) v) : ℤ) →
        ∀ (t0 : ℕ) (t : Fin (r - 1) → ℕ),
          t0 + ∑ m, t m ≤ pT r (Module.finrank ℚ K) σ →
          Qval φ b k L ι α' (ph (hL b (Module.finrank ℚ K)) v) (pD0 r (Module.finrank ℚ K) σ)
            (pDj r (Module.finrank ℚ K) σ) p t0 t s = 0)
    (hp12 : Height.logHeight p ≤
        0.85 * (pS r (Module.finrank ℚ K) (ph (hL b (Module.finrank ℚ K)) v) : ℝ) *
          pD r (Module.finrank ℚ K) σ)
    (h10 : Real.log ‖lam φ α b‖ ≤
        -(9 * 2 ^ r * (pS r (Module.finrank ℚ K) (ph (hL b (Module.finrank ℚ K)) v) : ℝ) *
          pD r (Module.finrank ℚ K) σ)) :
    ∃ P : MvPolynomial (Fin (r + 1)) ℂ, PolyOut φ α b k v L ι σ P :=
  analytic_core_assembly (H := ⟨hst, hr, hBH, hι, hp0, hp9, hp12, h10⟩)

end Work.BW
