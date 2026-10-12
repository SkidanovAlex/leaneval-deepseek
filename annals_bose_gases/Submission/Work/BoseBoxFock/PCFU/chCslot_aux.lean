import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.PCFU.SlotPieceDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.PCFU.chCslot_aux` — the vocabulary of the `(C)`-slot estimate

The `(C)`-slot of the cubic dictionary (`PCFU.chCslot`) pairs the **alias kernel**

    D = KfrU − ℓ³·W₁        (ℓ = ellH v μ)

against the state.  This module names `D` (`chD`) and the pointwise kernel bound
(`ChKerLe`) that the two halves of the estimate are phrased in:

* `ChKerLe v h μ fu N K` — `χ_ℓ(w)·χ_ℓ(z)·‖D(w−z)‖ ≤ K` for all `w, z`, where
  `χ_ℓ = chiLam ℓ` (the corpus bump, supported in `ball(0, ℓ/2)` and flat on its
  boundary);

* the **reduction** (`PCFU.chCslot_le_of_kernel`) — the slot is bounded by the
  kernel bound `K` times `(1+ℓ³)·normB`;

* the **kernel estimate** (`PCFU.chCslot_kernelSup`) — `ChKerLe` holds with
  `K = η·ℓ³ + C·ℓ³·(R/ℓ)¹²` for every `η > 0`, provided the UV label threshold
  `N` is large enough.

The decomposition of `D` used by the kernel estimate is the periodisation
identity `KfrU_periodisation`: `KfrU = ℓ³·Σ'_d uvSmear(· + ℓ d)`, so that

    D = ℓ³·[ Σ'_{d≠0} uvSmear(· + ℓ d) + (uvSmear − W₁) ] .

The images (`d ≠ 0`) are controlled by the face-layer smallness of `χ` at the
boundary of `ball(0, ℓ/2)` (`chi_mul_chi_le_of_alias`, applied with `v = d`,
which forces *both* arguments into the `R`-layer of the boundary) and the
`Λ`-uniform bound/decay of `uvSmear`; the `d = 0` term and the deep tail are
controlled by the UV cut-off (`N` large).
-/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace Work.BoseBoxFock.PCFU

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **The alias kernel of the `(C)`-slot**: `D(z) = KfrU(z) − ℓ³·W₁(z)`, `ℓ = ellH v μ`. -/
noncomputable def chD (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (μ : ℝ)
    (fu : Work.BoseBoxFix.LowCut) (N : ℕ) (z : E3) : ℂ :=
  KfrU v h μ fu N z
    - ((Work.BoseBoxFock.ellH v μ : ℂ) ^ 3)
        * ((Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ) z : ℝ) : ℂ)

/-- **The pointwise bound on the alias kernel**: with `χ_ℓ = chiLam ℓ`
(`ℓ = ellH v μ`), every product `χ_ℓ(w)·χ_ℓ(z)·‖D(w−z)‖` is at most `K`. -/
noncomputable def ChKerLe (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (μ : ℝ)
    (fu : Work.BoseBoxFix.LowCut) (N : ℕ) (K : ℝ) : Prop :=
  ∀ w z : E3, Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) w
      * Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) z
      * ‖chD v h μ fu N (w - z)‖ ≤ K

/-- **The `χ`-weighted *pairing* bound on the alias kernel** — the form in which the alias
kernel is actually small (the *pointwise* sup of `χ_ℓ(w)χ_ℓ(z)‖D(w−z)‖` is **not** small as
`N → ∞`: `KfrU` is a trigonometric polynomial, and at a jump of `W₁` the mollification
`uvSmear ⋆ W₁ → ½(W₁⁺+W₁⁻) ≠ W₁` keeps a fixed size).

For all `f g ∈ L²(ℝ³)`,

    ‖∫_w ∫_z f w · χ_ℓ(w) · D(w−z) · χ_ℓ(z) · g z‖  ≤  P · ‖f‖₂ · ‖g‖₂ .

The two halves of `D` are handled differently: the smoothing part `ℓ³(uvSmear − W₁)` obeys the
*multiplier* bound `sup_p‖chat (uvSmear−W₁) p‖ ≤ C/Λ` (`PCFU.chat_uvSmear_sub_W1fun_le`), while
the lattice images `ℓ³Σ'_{d≠0}uvSmear(·+ℓd)` are killed by the face-layer smallness of `χ`
(`chi_mul_chi_le_of_alias`) together with the `Λ`-uniform decay of `uvSmear`. -/
noncomputable def ChKerPair (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (μ : ℝ)
    (fu : Work.BoseBoxFix.LowCut) (N : ℕ) (P : ℝ) : Prop :=
  ∀ f g : E3 → ℂ,
    MeasureTheory.MemLp f 2 (MeasureTheory.volume : MeasureTheory.Measure E3) →
    MeasureTheory.MemLp g 2 (MeasureTheory.volume : MeasureTheory.Measure E3) →
    ‖∫ w : E3, ∫ z : E3,
        f w * ((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) w : ℝ) : ℂ)
          * chD v h μ fu N (w - z)
          * ((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) z : ℝ) : ℂ) * g z‖
      ≤ P * Real.sqrt (∫ w : E3, ‖f w‖ ^ 2) * Real.sqrt (∫ z : E3, ‖g z‖ ^ 2)

end Work.BoseBoxFock.PCFU
