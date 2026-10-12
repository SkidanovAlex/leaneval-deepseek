import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseBoxFock.pairRowS2Honest
import Submission.Work.BoseBoxFock.pairRowWordParts
import Submission.Work.BoseBoxFock.qmqDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.qmqAssemblyAux` — the plumbing of the (A)-assembly

Auxiliary, node-independent facts used by the assembly of
`Work.BoseBoxFock.pairRowNice_le_wordParts` (see the module docstring and
`FINDING_pairRowNice_le_wordParts.md` for the route):

* `q1PairWord_eq_q1WordK`, `q4PairWord_eq_q4WordK` — the corpus's two pair words are the
  general-kernel words of `qmqDefs` at the honest kernels `wPairC ℓ (g₂ v h)`, `wPairC ℓ (g₀ v h)`;
* `kPer_eq_wPair_add_img` — the periodised kernel of `K1lim` is (definitionally, up to the lattice
  `tsum` split) the `m = 0` kernel `wPair` plus the images kernel `imgKernel`.

Everything here is `sorry`-free.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- The corpus's `T₁` word is the general-kernel word at `k = wPairC ℓ (g₂ v h)`. -/
theorem q1PairWord_eq_q1WordK {N : ℕ} (ℓ : ℝ) {v : ℝ³ → ℝ}
    (h : Work.UBB.ScatSol v) (Φ : Submission.BoseGases.X N → ℝ) :
    Submission.BoseGases.q1PairWord (ℓ := ℓ) (v := v) h (Φ := Φ)
      = q1WordK ℓ (Submission.BoseGases.wPairC ℓ (Submission.BoseGases.g2 v h)) Φ := rfl

/-- The corpus's `T₄` word is the general-kernel word at `k = wPairC ℓ (g₀ v h)`. -/
theorem q4PairWord_eq_q4WordK {N : ℕ} (ℓ : ℝ) {v : ℝ³ → ℝ}
    (h : Work.UBB.ScatSol v) (Φ : Submission.BoseGases.X N → ℝ) :
    Submission.BoseGases.q4PairWord (ℓ := ℓ) (v := v) h (Φ := Φ)
      = q4WordK ℓ (Submission.BoseGases.wPairC ℓ (Submission.BoseGases.g0 v h)) Φ := rfl

/-- The lattice vector of `0` vanishes (a local copy of `Work.BoseRowsFS.vecZ_zero`). -/
theorem latVec_zero' : latVec (0 : Fin 3 → ℤ) = 0 := by
  ext i
  simp [latVec]

/-- The periodised kernel of `K1lim ℓ (wScaled ℓ h)` splits into its `m = 0` part `wPair ℓ h` and
the images kernel `imgKernel ℓ (wScaled ℓ h)`.  (The summability hypothesis is automatic for the
honest weights, which are compactly supported; `ℓ ≠ 0` is needed because `(0³)⁻¹ = 0` in Lean
while `chiScale 0` is a nonzero constant.) -/
theorem kPer_eq_wPair_add_img (ℓ : ℝ) (h : E3 → ℝ) (w y : E3) (hℓ : ℓ ≠ 0)
    (hsum : Summable (fun m : Fin 3 → ℤ =>
      ((Submission.BoseGases.wScaled ℓ h (w - y + ℓ • latVec m) : ℝ) : ℂ))) :
    ((ℓ ^ 3)⁻¹ : ℂ) * ((Submission.BoseGases.chiScale ℓ w : ℝ) : ℂ)
        * latPer3 ℓ (Submission.BoseGases.wScaled ℓ h) (w - y)
        * ((Submission.BoseGases.chiScale ℓ y : ℝ) : ℂ)
      = ((Submission.BoseGases.wPair ℓ h w y : ℝ) : ℂ)
        + ((imgKernel ℓ (Submission.BoseGases.wScaled ℓ h) w y : ℝ) : ℂ) := by
  have hsplit := hsum.tsum_eq_add_tsum_ite (0 : Fin 3 → ℤ)
  have hfirst : ((Submission.BoseGases.wScaled ℓ h (w - y + ℓ • latVec 0) : ℝ) : ℂ)
      = ((Submission.BoseGases.wScaled ℓ h (w - y) : ℝ) : ℂ) := by
    rw [latVec_zero', smul_zero, add_zero]
  have hsecond : (∑' m : Fin 3 → ℤ, if m = 0 then (0 : ℂ)
        else ((Submission.BoseGases.wScaled ℓ h (w - y + ℓ • latVec m) : ℝ) : ℂ))
      = ((∑' m : Fin 3 → ℤ, if m = 0 then (0 : ℝ)
          else Submission.BoseGases.wScaled ℓ h (w - y + ℓ • latVec m) : ℝ) : ℂ) := by
    rw [Complex.ofReal_tsum]
    refine tsum_congr (fun m => ?_)
    by_cases hm : m = 0 <;> simp [hm]
  have hkey : (∑' m : Fin 3 → ℤ,
        ((Submission.BoseGases.wScaled ℓ h (w - y + ℓ • latVec m) : ℝ) : ℂ))
      = ((Submission.BoseGases.wScaled ℓ h (w - y) : ℝ) : ℂ)
        + ((∑' m : Fin 3 → ℤ, if m = 0 then (0 : ℝ)
            else Submission.BoseGases.wScaled ℓ h (w - y + ℓ • latVec m) : ℝ) : ℂ) := by
    rw [hsplit, hfirst, hsecond]
  have hcard : ((ℓ : ℂ) ^ 3)⁻¹ * (ℓ : ℂ) ^ 3 = 1 :=
    inv_mul_cancel₀ (pow_ne_zero 3 (Complex.ofReal_ne_zero.mpr hℓ))
  have haux : ∀ X : ℂ, ((ℓ : ℂ) ^ 3)⁻¹ * ((Submission.BoseGases.chiScale ℓ w : ℝ) : ℂ)
      * ((ℓ : ℂ) ^ 3 * X) = ((Submission.BoseGases.chiScale ℓ w : ℝ) : ℂ) * X := by
    intro X
    calc ((ℓ : ℂ) ^ 3)⁻¹ * ((Submission.BoseGases.chiScale ℓ w : ℝ) : ℂ)
          * ((ℓ : ℂ) ^ 3 * X)
        = ((ℓ : ℂ) ^ 3)⁻¹ * (((Submission.BoseGases.chiScale ℓ w : ℝ) : ℂ)
            * ((ℓ : ℂ) ^ 3 * X)) := by rw [mul_assoc]
      _ = ((ℓ : ℂ) ^ 3)⁻¹ * ((((Submission.BoseGases.chiScale ℓ w : ℝ) : ℂ)
            * (ℓ : ℂ) ^ 3) * X) := by rw [mul_assoc]
      _ = ((ℓ : ℂ) ^ 3)⁻¹ * (((ℓ : ℂ) ^ 3 * ((Submission.BoseGases.chiScale ℓ w : ℝ) : ℂ))
            * X) := by rw [mul_comm ((Submission.BoseGases.chiScale ℓ w : ℝ) : ℂ) ((ℓ : ℂ) ^ 3)]
      _ = ((ℓ : ℂ) ^ 3)⁻¹ * ((ℓ : ℂ) ^ 3
            * (((Submission.BoseGases.chiScale ℓ w : ℝ) : ℂ) * X)) := by rw [mul_assoc]
      _ = (((ℓ : ℂ) ^ 3)⁻¹ * (ℓ : ℂ) ^ 3)
            * (((Submission.BoseGases.chiScale ℓ w : ℝ) : ℂ) * X) := by rw [mul_assoc]
      _ = ((Submission.BoseGases.chiScale ℓ w : ℝ) : ℂ) * X := by rw [hcard, one_mul]
  rw [latPer3, LatFourier.latPer, hkey, imgKernel, Submission.BoseGases.wPair]
  push_cast
  rw [mul_add, mul_add, add_mul, haux, haux]

end Work.BoseBoxFock
