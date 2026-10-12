import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Data.ZMod.ValMinAbs
import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.L1Tails.highModeTail
import Submission.Work.BoseBoxFock.kinFormB_le_of_isLowB
import Submission.Work.BoseBoxFock.pairRowWordParts
import Submission.Work.BoseBoxFock.pinDirChi_le_kinFormB
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.PB3Defs` — the vocabulary of the block-III (`pairRowB3`) comparison

This module fixes the definitions shared by the pieces of the proof of

    `Work.BoseBoxFock.pairRowB3_le_massWord`

(the block-III half of the `Q₂` row: the constant-weight `K1exp` sum against the mass word
`rowMassWord`).  The comparison runs through the *frame* of the localised modes
`pinQ_k = (√ℓ³)⁻¹Q(χ_ℓ e^{i⟪κ_k,·⟫})`:

* `pinQInf ℓ k` is the free-lattice version (`k : Fin 3 → ℤ`, momentum `kappaL ℓ k`);
* `mf ℓ f = f − (ℓ³)⁻¹∫_{boxL ℓ} f` is the mean-free part; on the support of `χ_ℓ` the
  subtraction coincides with the corpus box projection `Qb f = f − ℓ⁻³∫_{boxL}f·1_{boxL}`;
* `frameSum ℓ S f` is the truncated frame sum `Σ_{k∈S}‖⟨pinQInf ℓ k, f⟩‖²`, i.e. also
  `ℓ⁻³Σ_{k∈S}‖kinFT (χ_ℓ·mf ℓ f)(κ_k)‖²` (`finFT_pinQInf`);
* `slotOne K j Ψ` is the slot-`j` one-body operator of the kernel `K` (first quantisation).

The three analytic facts about the frame are

* `finFT_pinQInf` — the identification of the inner products with the Fourier coefficients;
* `frameSum_le_mass` — the truncated Bessel/Parseval bound `frameSum ≤ ∫χ²|Qf|²`;
* `frameSum_tail_le` — the tail bound by the Dirichlet energy of `χ_ℓ·mf ℓ f`.

They are proved in the sibling modules `PB3Frame`.  Nothing here is `sorry`-free-dependent.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Xn" => Work.BoseDict.Xn
local notation "boxL" => Work.BoseK15.corpusBox.boxL

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **The mean-free part of a one-body state** `f − (ℓ³)⁻¹∫_{boxL ℓ} f`.  On the support of
`chiScale ℓ` (the inscribed ball) this equals the corpus box projection `Q_Λf`; the difference is
killed by the `chiScale ℓ` factor. -/
noncomputable def mf (ℓ : ℝ) (f : E3 → ℂ) : E3 → ℂ :=
  fun x => f x - ((ℓ ^ 3)⁻¹ : ℝ) * ∫ y in boxL ℓ, f y

/-- **The free-lattice pinned mode** `(√ℓ³)⁻¹ Q(χ_ℓ e^{i⟪κ_k,·⟫})`: the `pinQ` of the corpus with
the lattice label `k : Fin 3 → ℤ` replaced by the free lattice vector. -/
noncomputable def pinQInf (ℓ : ℝ) (k : Fin 3 → ℤ) : E3 → ℂ :=
  fun x => (((Real.sqrt (ℓ ^ 3))⁻¹ : ℝ) : ℂ)
    * Work.BoseK15.corpusBox.qVec ℓ (Work.BoseBoxFock.kappaL ℓ k) x

/-- **The truncated frame sum** `Σ_{k∈S}‖⟨pinQInf ℓ k, f⟩‖²`. -/
noncomputable def frameSum (ℓ : ℝ) (S : Finset (Fin 3 → ℤ)) (f : E3 → ℂ) : ℝ :=
  ∑ k ∈ S, ‖∫ x : E3, (starRingEnd ℂ) (pinQInf ℓ k x) * f x‖ ^ 2

/-- **The slot-`j` one-body operator** of the kernel `K` on `n`-body states (first
quantisation): `(slotOne K j Ψ)(x) = ∫_u K (x j) u · Ψ (x[j ↦ u]) du`. -/
noncomputable def slotOne {n : ℕ} (K : E3 → E3 → ℂ) (j : Fin n) (Ψ : Xn n → ℂ) : Xn n → ℂ :=
  fun x => ∫ u : E3, K (x j) u * Ψ (Function.update x j u)

/-- `kappaL ℓ (labVec N k) = kmomLab ℓ N k`. -/
theorem kmomLab_eq_kappaL (ℓ : ℝ) (N : ℕ) (k : Lab N) :
    Work.BoseBoxFock.kappaL ℓ (labVec N k) = kmomLab ℓ N k := rfl

/-- **The `pinQ` of the truncation `Lab N`** is `pinQInf` at the label `labVec N k`. -/
theorem pinQ_eq_pinQInf {v : ℝ³ → ℝ} {μ : ℝ} (N : ℕ) (k : Lab N) :
    pinQ v μ N k = pinQInf (ellH v μ) (labVec N k) := by
  unfold pinQ pinQInf
  rw [kmomLab_eq_kappaL]

/-- **The slot-`j` box projection** `Q_j`: the state minus its slot-`j` box mean
`ℓ⁻³∫_{acube ℓ}`.  This is the one-body projection `Q_Λ` acting in slot `j`. -/
noncomputable def boxQ {n : ℕ} (ℓ : ℝ) (j : Fin n) (Ψ : Xn n → ℂ) : Xn n → ℂ :=
  fun x => Ψ x - (((ℓ ^ 3)⁻¹ : ℝ) : ℂ)
    * ∫ y in Submission.BoseGases.acube ℓ, Ψ (Function.update x j y)

/-- The **slot section** of an `n`-body state `Ψ` at the fixed value `x'` of the other slots:
`v ↦ Ψ (x'` with slot `j` set to `v`)`. -/
noncomputable def sect {n : ℕ} (j : Fin n) (x' : {k : Fin n // k ≠ j} → E3) (Ψ : Xn n → ℂ) :
    E3 → ℂ :=
  fun v => Ψ (insertCoord j v x')

/-- The **`χ_ℓ`-weighted Dirichlet energy** of a one-body state, in the form in which the tail
bound of the frame produces it: `Σ_j ∫_w χ(w)²‖∂_{w_j}(χ(w)·f w)‖²` is *not* what appears; the
statements below use the plain form `Σ_j∫‖∂_j(χ·f)‖²`. -/
noncomputable def dirEnergy (ℓ : ℝ) (f : E3 → ℂ) : ℝ :=
  ∫ w : E3, ∑ j : Fin 3, ‖fderiv ℝ f w (EuclideanSpace.single j (1 : ℝ))‖ ^ 2

/-- The image of the truncation labels in the free lattice: `{labVec N k | k : Lab N}`, i.e. the
integer vectors of the cube `{−N,…,N}³`. -/
noncomputable def labSet (N : ℕ) : Finset (Fin 3 → ℤ) :=
  Finset.univ.image (labVec N)

/-- **The lattice label set of the truncation**: the integer vectors of the cube
`{−N,…,N}³`, presented as the image of `Lab N` under `labVec` (the two are equal, but only this
presentation is needed). -/
def labcube (N : ℕ) : Set (Fin 3 → ℤ) := {n | n ∈ labSet N}

/-- The truncated frame sum over the *complement* of the label cube. -/
noncomputable def frameTail (v : ℝ³ → ℝ) (μ : ℝ) (N : ℕ) (f : E3 → ℂ) : ℝ :=
  ∑' k : {k : Fin 3 → ℤ // k ∉ labcube N},
    ‖∫ x : E3, (starRingEnd ℂ) (pinQInf (ellH v μ) k.1 x) * f x‖ ^ 2

/-- **The membership bound of the truncation labels**: the integer coordinates of `labVec N k`
are bounded by `N`. -/
theorem abs_labVec_le (N : ℕ) (k : Lab N) (i : Fin 3) : |labVec N k i| ≤ (N : ℤ) := by
  have h := ((ZMod.valMinAbs_spec (n := 2 * N + 1) (k i) ((k i).valMinAbs)).1 rfl).2
  have h1 : (k i).valMinAbs * 2 ≤ (2 * (N : ℤ) + 1) := by
    have := h.2; push_cast at this; exact this
  have h2 : -(2 * (N : ℤ) + 1) < (k i).valMinAbs * 2 := by
    have := h.1; push_cast at this; exact this
  rw [labVec]
  refine abs_le.mpr ⟨?_, ?_⟩ <;> omega

/-- The free-lattice labels of the truncation are contained in the integer cube. -/
theorem labSet_subset_cube (N : ℕ) {n : Fin 3 → ℤ} (hn : n ∈ labSet N) (i : Fin 3) :
    |n i| ≤ (N : ℤ) := by
  obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hn
  exact abs_labVec_le N k i

/-- **Every free label outside the truncation has norm at least `N + 1`.** -/
theorem norm_ge_of_not_mem_labSet {N : ℕ} {n : Fin 3 → ℤ} (hn : n ∉ labSet N) :
    (N : ℝ) + 1 ≤ ‖Work.BoseBoxFock.latVec n‖ := by
  -- some coordinate exceeds `N` in modulus
  have hsome : ∃ i : Fin 3, (N : ℤ) + 1 ≤ |n i| := by
    by_contra hc
    refine hn (Finset.mem_image.mpr ?_)
    push_neg at hc
    have hb : ∀ i : Fin 3, |n i| ≤ (N : ℤ) := by
      intro i
      have := hc i
      omega
    have hpre : ∀ i : Fin 3, ∃ k : ZMod (2 * N + 1), k.valMinAbs = n i := by
      intro i
      refine ⟨(n i : ZMod (2 * N + 1)), ?_⟩
      rw [ZMod.valMinAbs_spec]
      refine ⟨rfl, ?_⟩
      have hi2 : |n i| ≤ (N : ℤ) := hb i
      obtain ⟨hi2a, hi2b⟩ := abs_le.mp hi2
      have h4 : (n i) * 2 ≤ (2 * (N : ℤ) + 1) := by omega
      have h5 : -(2 * (N : ℤ) + 1) < (n i) * 2 := by omega
      constructor
      · push_cast; exact h5
      · push_cast; exact h4
    choose k hk using hpre
    exact ⟨fun i => k i, Finset.mem_univ _, funext fun i => hk i⟩
  obtain ⟨i, hi⟩ := hsome
  have h1 : ((N : ℤ) + 1 : ℝ) ≤ |(n i : ℝ)| := by exact_mod_cast hi
  have h2 : |(n i : ℝ)| ≤ ‖Work.BoseBoxFock.latVec n‖ := by
    have h3 := PiLp.norm_apply_le (p := 2) (x := Work.BoseBoxFock.latVec n) i
    rw [Work.BoseBoxFock.latVec_apply] at h3
    simpa [Real.norm_eq_abs] using h3
  exact le_trans h1 h2

/-- **The block-III pair shape** of `pairRowB3`: the `pairSet n`-sum of the triple integrals with
the two condensate pins, the kernel `K` in slot `p.2` and the state `Θ`. -/
noncomputable def b3PairSum {n : ℕ} (Θ : Xn n → ℂ) (A B : E3 → ℂ) (K : E3 → E3 → ℂ) : ℂ :=
  ∑ p ∈ Submission.BoseGases.pairSet n,
    ∫ x : Xn n, ∫ y : E3, ∫ u : E3,
      (starRingEnd ℂ) (Θ x) * A (x p.1) * (starRingEnd ℂ) (B y) * K (x p.2) u
        * Θ (Function.update (Function.update x p.1 y) p.2 u)

/-- **The slot form** of the block-III pair shape with the condensate pins stripped: the
`pairSet n`-sum of `⟨Θ, (K)_{p.2}(P_{p.1}Θ)⟩`, where `(K)_{j}` is the slot-`j` one-body operator of
the kernel `K` (`slotOne`) and `P_i` is the slot-`i` box mean (`aPC`). -/
noncomputable def b3SlotSum {n : ℕ} (ℓ : ℝ) (Θ : Xn n → ℂ) (K : E3 → E3 → ℂ) : ℂ :=
  ∑ p ∈ Submission.BoseGases.pairSet n,
    ∫ x : Xn n, (starRingEnd ℂ) (Θ x) * slotOne K p.2 (aPC ℓ p.1 Θ) x

/-- The quadratic form of the truncated frame operator `Σ_{k∈Lab N}|pinQ_k⟩⟨pinQ_k|` in the slot
`j`, evaluated at `Θ` (the real part of the raw complex integral). -/
noncomputable def frameSlotForm {n : ℕ} (v : ℝ³ → ℝ) (μ : ℝ) (N : ℕ) (j : Fin n)
    (Θ : Xn n → ℂ) : ℝ :=
  (∑ k : Lab N, ∫ x in Submission.BoseGases.abox n (ellH v μ),
      (starRingEnd ℂ) (Θ x) * (pinQ v μ N k (x j)
        * (∫ u : E3, (starRingEnd ℂ) (pinQ v μ N k u) * Θ (Function.update x j u)))).re

/-- The quadratic form of the *limit* frame operator (the multiplication by `χ_ℓ²` composed with
the box projection `boxQ`) in the slot `j`. -/
noncomputable def limSlotForm {n : ℕ} (ℓ : ℝ) (j : Fin n) (Θ : Xn n → ℂ) : ℝ :=
  ∫ x in Submission.BoseGases.abox n ℓ,
    (Submission.BoseGases.chiScale ℓ (x j)) ^ 2 * ‖boxQ ℓ j Θ x‖ ^ 2

end Work.BoseBoxFock
