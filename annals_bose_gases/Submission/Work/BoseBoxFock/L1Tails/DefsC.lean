import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Submission.Work.BoseBoxFock.L1Tails.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.L1Tails.DefsC` — the vocabulary of the `kernelTail` development

The target `Work.BoseBoxFock.L1Tails.kernelTail` (design `sources/boseDCF/bose_L1tails.md`, T6)
bounds the truncation tail of the `χχ` periodised kernel: for an `L¹` weight `W` supported in the
ball of radius `R`, a smooth box-supported kernel `H` and any truncation `c` (`|c| ≤ 1`, `c = 1`
below `Λ`),

    ‖∫∫ latPer3 ℓ W (w − y) H − Σ_{n ∈ S} c_n Ŵ(κ_n) Ȟ_n‖ ≤ 2 √(τ ℓ⁹ D) ,

where `D = ∫∫ Σ_j ‖∂_{w_j}H‖²` and `τ` bounds the Coulomb tail `(ℓ³)⁻¹ Σ_{n : ‖κ_n‖ ≥ Λ}
‖Ŵ(κ_n)‖²/‖κ_n‖²`.

The argument (all of it is the mathematics of Fourier series on the ℓ-cube):

* the periodisation `latPer3 ℓ W` is paired against the **smooth** kernel `H` by folding the second
  variable into `Φ(u) = ∫_y H (u + y) y` (`foldH`): the pairing equals `ℓ³ ∫_z W z · Π z` where
  `Π = latPerC ℓ Φ` is the periodisation of `Φ`;
* `Φ` smooth compactly supported makes the Fourier series of `Π` **absolutely and uniformly
  convergent** with coefficients `ℓ^{-3} Ŵ(κ_n)` (`latPerC_hasSum_fourier`), which identifies the
  pairing with the lattice sum `Σ_n Ŵ(κ_n) Ȟ_n`;
* the tail is then split by Cauchy–Schwarz: `hτ` bounds `Σ ‖Ŵ(κ_n)‖²/‖κ_n‖²` on the tail while the
  sharp per-`y` frame identity bounds `Σ ‖κ_n‖² ‖Ȟ_n‖² ≤ ℓ⁶ D`.

This module only fixes the vocabulary of that development (`latPerC`, `foldH`, `hPair`, `wSample`)
and records its elementary properties.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators Real

namespace Work.BoseBoxFock.L1Tails

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false

/-! ## 1. The `ℂ`-valued periodisation -/

/-- The `ℓℤ³`-periodisation of a `ℂ`-valued function:
`latPerC ℓ Φ z = Σ'_m Φ (z + ℓ • latVec m)`.

(The corpus's `Work.BoseBoxFock.LatFourier.latPer` is the same object for *real*-valued weights,
with the coercion to `ℂ` inside the summand; `latPerC` is the version for complex-valued
functions, whose periodisation has to be expanded in the Fourier series.) -/
noncomputable def latPerC (ℓ : ℝ) (Φ : E3 → ℂ) (z : E3) : ℂ :=
  ∑' m : Fin 3 → ℤ, Φ (z + ℓ • latVec m)

/-- **Periodicity** of `latPerC`: it is invariant under the lattice translations. -/
theorem latPerC_add_latVec (ℓ : ℝ) (Φ : E3 → ℂ) (v : Fin 3 → ℤ) (z : E3) :
    latPerC ℓ Φ (z + ℓ • latVec v) = latPerC ℓ Φ z := by
  unfold latPerC
  have hf : (fun m : Fin 3 → ℤ => Φ (z + ℓ • latVec v + ℓ • latVec m))
      = fun m : Fin 3 → ℤ => Φ (z + ℓ • latVec (v + m)) := by
    funext m
    congr 1
    rw [add_assoc, ← smul_add, ← Work.BoseBoxFock.LatFourier.latVec_add]
  rw [hf]
  let e : (Fin 3 → ℤ) ≃ (Fin 3 → ℤ) :=
    { toFun := fun m => v + m
      invFun := fun m => -v + m
      left_inv := fun m => by simp [add_assoc]
      right_inv := fun m => by simp [add_assoc] }
  simpa [e] using (Equiv.tsum_eq e (fun m : Fin 3 → ℤ => Φ (z + ℓ • latVec m)))

/-! ## 2. The folded kernel and the lattice pairing -/

/-- The `y`-fold `Φ u = ∫_y H (u + y) y` of a kernel `H`: the function whose `ℓℤ³`-periodisation is
the periodisation of the `w − y` kernel. -/
noncomputable def foldH (H : E3 → E3 → ℂ) (u : E3) : ℂ := ∫ y, H (u + y) y

/-- The lattice pairing `Ȟ_n = ∫_w ∫_y e^{i⟪κ_n, w − y⟫} H w y` of the kernel `H`. -/
noncomputable def hPair (ℓ : ℝ) (H : E3 → E3 → ℂ) (n : Fin 3 → ℤ) : ℂ :=
  ∫ w, ∫ y, Complex.exp (Complex.I * ((inner ℝ (kappaL ℓ n) (w - y) : ℝ) : ℂ)) * H w y

/-- The lattice sample `Ŵ(κ_n)` of a real weight `W`, as a complex number. -/
noncomputable def wSample (ℓ : ℝ) (W : E3 → ℝ) (n : Fin 3 → ℤ) : ℂ :=
  Submission.BoseGases.kinFT (fun y : E3 => ((W y : ℝ) : ℂ)) (kappaL ℓ n)

/-- The target's lattice summand `Ŵ(κ_n) Ȟ_n`. -/
noncomputable def summand (ℓ : ℝ) (W : E3 → ℝ) (H : E3 → E3 → ℂ) (n : Fin 3 → ℤ) : ℂ :=
  wSample ℓ W n * hPair ℓ H n

/-- The target's second summand `c_n Ŵ(κ_n) Ȟ_n`. -/
noncomputable def cSummand (ℓ : ℝ) (W : E3 → ℝ) (H : E3 → E3 → ℂ)
    (c : (Fin 3 → ℤ) → ℂ) (n : Fin 3 → ℤ) : ℂ :=
  c n * (wSample ℓ W n * hPair ℓ H n)

/-! ## 3. Elementary lattice-momentum facts -/

/-- The dual-lattice vector `vec` vanishes only at `n = 0`. -/
lemma vec_eq_zero_iff (n : Fin 3 → ℤ) : Work.BoseB4.vec n = 0 ↔ n = 0 := by
  constructor
  · intro h
    have hcoord : ∀ i : Fin 3, (2 * Real.pi * (n i : ℝ)) = 0 := by
      intro i
      have h2 : (Work.BoseB4.vec n) i = (0 : E3) i := by rw [h]
      simpa [Work.BoseB4.vec] using h2
    funext i
    have h3 : (n i : ℝ) = 0 := by
      rcases mul_eq_zero.mp (hcoord i) with h4 | h4
      · exact absurd h4 (by positivity)
      · exact h4
    exact_mod_cast h3
  · intro h
    rw [h, Work.BoseB4.vec]
    ext i
    simp

/-- The lattice momentum vanishes only at `n = 0`. -/
lemma kappaL_eq_zero_iff {ℓ : ℝ} (hℓ : ℓ ≠ 0) (n : Fin 3 → ℤ) :
    kappaL ℓ n = 0 ↔ n = 0 := by
  rw [kappaL, Work.BoseBoxFock.kmomInt, smul_eq_zero]
  rw [or_iff_right (inv_ne_zero hℓ), vec_eq_zero_iff]

/-- **The lattice momentum is odd.** -/
lemma kappaL_neg (ℓ : ℝ) (n : Fin 3 → ℤ) :
    kappaL ℓ (-n) = -kappaL ℓ n := by
  have hvec : Work.BoseB4.vec (-n) = -Work.BoseB4.vec n := by
    rw [Work.BoseB4.vec, Work.BoseB4.vec]
    ext i
    simp [Int.cast_neg]
  rw [kappaL, kappaL, Work.BoseBoxFock.kmomInt, Work.BoseBoxFock.kmomInt, hvec, smul_neg]

/-- A nonzero lattice momentum has positive norm. -/
lemma norm_kappaL_pos {ℓ : ℝ} (hℓ : 0 < ℓ) {n : Fin 3 → ℤ} (hn : n ≠ 0) :
    0 < ‖kappaL ℓ n‖ :=
  norm_pos_iff.mpr fun h => hn ((kappaL_eq_zero_iff (ne_of_gt hℓ) n).mp h)

end Work.BoseBoxFock.L1Tails
