import Mathlib
import Submission.Work.Diff.STE.B3.SymCalcStep5.conjCut_lapPow
import Submission.Work.Diff.STE.B3.SymCalcStep1.conj_cut_comm_laplacian_le
import Submission.Work.Diff.STE.flat.seriesFun_fourierCoeff
import Submission.Work.Diff.STE.eq_zero_of_fourierCoeff_eq_zero
import Submission.Work.Diff.STE.summable_weighted_fourierCoeff_of_contDiff
import Submission.Work.Diff.STE.contDiff_seriesFun
import Submission.Work.Diff.STE.B3.SymCalcStep6.lapPow_toolbox
import Submission.Work.Diff.STE.B3.SymCalcStep6.lapPow_one_eq_neg_lapC
import Submission.Work.Diff.STE.B3.SymCalcStep6.lapPow_algebra

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# B3 symbol calculus, step 6: `[Λ^k, V]` is of order `2k − 1`, uniformly in `ε`

This is PIECE 4 in the general-`k` form consumed by the order reduction of the `B3` layer (the
cross terms of `[Qk, J]`).  With

* `Λ^k = lapPow k` — the flat Laplacian power (the Fourier multiplier with symbol `flatLam ^ k`),
* `V = conjCut ρ ε T T' = comp_T' ∘ S_ε ∘ comp_T` — the Friedrichs cutoff `S_ε` transported into
  the other chart, where `T` is the chart transition (a `1`-periodic diffeomorphism of the torus
  with inverse `T'`),

the theorem bounds the commutator defect

  `CSq s (fourierCoeff ([Λ^k, V] g))  ≤  C · CSq (s + 2k − 1) (fourierCoeff g)`,

with `C` independent of `ε ∈ (0,1]` and of `g`.

## Route

1. **The exact conjugation identity** (`SymCalcStep5.conjCut_lapPow_comm`, proved): with
   `P_k = conjLapPow k T T' = comp_T ∘ Λ^k ∘ comp_T'` and `h = comp_T g`,

     `[Λ^k, V] g = comp_T' ( [P_k, S_ε] h )`.

   So everything is pushed into the commutator of `P_k` with the *plain* Friedrichs cutoff.

2. **The conjugation is harmless** (`fourierCoeff_comp_le`, from `SymCalcStep1`): composition with
   `T` resp. `T'` is bounded on the `CSq s` scale, with constants depending only on `T`.

3. **The commutator `[P_k, S_ε]` is of order `2k − 1`, uniformly in `ε`.**  This is the content of
   the file.  Writing `P_k = P_1^k` with `P_1 = conjLapPow 1 T T'` (the `Λ^k` compose as Fourier
   multipliers, `lapPow_algebra`) and using the recursion

     `[P_1^{k+1}, S_ε] h = P_1 ([P_1^k, S_ε] h) + [P_1, S_ε] (P_1^k h)`

   (in the file: `W (k+1) ε h = P_1 (W k ε h) + W 1 ε (P_k h)`, where
   `W k ε h = [P_k, S_ε] h`), the estimate follows by induction on `k`, because

   * `P_j` is ε-free of order `2j` (`conjLapPow_CSq_le`: composition bounds + the multiplier bound
     `lapPow_toolbox`),
   * `[P_1, S_ε]` is ε-uniformly of order `1`: on smooth `1`-periodic functions
     `P_1 = conjLapPow 1 T T' = − pullLap T T'` (the sign bridge `lapPow_one_eq_neg_lapC`
     identifies the *positive* symbol `flatLam` of `Λ = lapPow 1` with the *negative* symbol of the
     differential operator `lapC = Σᵢ ∂ᵢ∂ᵢ`), and `[pullLap, S_ε]` is of order `1`, uniformly in
     `ε` (`SymCalcStep1.pullLap_comm_bound_self`, proved).

The induction is run with the *sharp* index: level `k+1` at regularity `s` uses the level `k`
estimate at regularity `s+2` (one factor `P_1`, of order `2`) and the level `1` estimate at
regularity `s+1` (one factor `P_k`, of order `2k`); both produce the index `s + 2k − 1`.
-/

noncomputable section

open MeasureTheory BigOperators

namespace Work.Diff.STE.B3.SymCalcStep6

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Elementary linearity of `compMap` -/

/-- Composition with `T` commutes with negation (pointwise). -/
theorem compMap_neg (T : (ι → ℝ) → (ι → ℝ)) (u : (ι → ℝ) → ℂ) :
    Work.Diff.STE.B3.SymCalc.compMap T (fun x => -u x)
      = fun x => - Work.Diff.STE.B3.SymCalc.compMap T u x := by
  funext x
  rfl

/-- Composition with `T` commutes with addition (pointwise). -/
theorem compMap_add (T : (ι → ℝ) → (ι → ℝ)) (u v : (ι → ℝ) → ℂ) :
    Work.Diff.STE.B3.SymCalc.compMap T (u + v)
      = Work.Diff.STE.B3.SymCalc.compMap T u + Work.Diff.STE.B3.SymCalc.compMap T v := by
  funext x
  rfl

/-! ## Linearity of `fourierCoeff` under negation, and its consequence for `CSq` -/

/-- `fourierCoeff` is compatible with negation (unconditionally: both sides are Bochner integrals,
for which `∫ -f = -∫ f` holds without any integrability hypothesis). -/
theorem fourierCoeff_neg (u : (ι → ℝ) → ℂ) (k : ι → ℤ) :
    Work.Diff.STE.fourierCoeff (fun x => -u x) k = - Work.Diff.STE.fourierCoeff u k := by
  simp only [Work.Diff.STE.fourierCoeff]
  rw [show (fun x : ι → ℝ => Work.Diff.STE.fourierExp (-k) x * -u x)
      = fun x => - (Work.Diff.STE.fourierExp (-k) x * u x) from by
    funext x
    ring]
  rw [MeasureTheory.integral_neg]

/-- `CSq` only sees the norms of a coefficient family. -/
theorem CSq_congr_norm (s : ℕ) {c d : (ι → ℤ) → ℂ} (h : ∀ k, ‖c k‖ = ‖d k‖) :
    Work.Diff.STE.CSq s c = Work.Diff.STE.CSq s d := by
  simp only [Work.Diff.STE.CSq]
  congr 1
  funext k
  rw [h k]

/-- Negating the function does not change `CSq` of its Fourier coefficients. -/
theorem CSq_fourierCoeff_neg (s : ℕ) (u : (ι → ℝ) → ℂ) :
    Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff (fun x => -u x))
      = Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff u) :=
  CSq_congr_norm s fun k => by rw [fourierCoeff_neg u k, norm_neg]

/-! ## `flatCut` and `conjCut` are compatible with negation -/

/-- The Friedrichs cutoff `S_ε = flatCut ρ ε` is compatible with negation. -/
theorem flatCut_neg (ρ : (ι → ℝ) → ℝ) (ε : ℝ) (w : (ι → ℝ) → ℂ) :
    Work.Diff.STE.B3.SymCalc.flatCut ρ ε (fun x => -w x)
      = fun x => - Work.Diff.STE.B3.SymCalc.flatCut ρ ε w x := by
  have hc : Work.Diff.STE.fourierCoeff (fun x => -w x)
      = fun k : ι → ℤ => - Work.Diff.STE.fourierCoeff w k :=
    funext fun k => fourierCoeff_neg w k
  unfold Work.Diff.STE.B3.SymCalc.flatCut
  rw [hc]
  funext x
  rw [Work.Diff.STE.seriesFun, Work.Diff.STE.seriesFun]
  rw [show (fun k : ι → ℤ => Work.Diff.STE.trunc ρ ε
        (fun k => - Work.Diff.STE.fourierCoeff w k) k * Work.Diff.STE.fourierExp k x)
      = fun k : ι → ℤ => - (Work.Diff.STE.trunc ρ ε (Work.Diff.STE.fourierCoeff w) k
          * Work.Diff.STE.fourierExp k x) from by
    funext k
    simp only [Work.Diff.STE.trunc]
    ring]
  rw [tsum_neg]

/-- The transported cutoff `V = conjCut ρ ε T T'` is compatible with negation. -/
theorem conjCut_neg (ρ : (ι → ℝ) → ℝ) (ε : ℝ) (T T' : (ι → ℝ) → (ι → ℝ))
    (u : (ι → ℝ) → ℂ) :
    Work.Diff.STE.B3.SymCalc.conjCut ρ ε T T' (fun x => -u x)
      = fun x => - Work.Diff.STE.B3.SymCalc.conjCut ρ ε T T' u x := by
  have h1 : Work.Diff.STE.B3.SymCalc.compMap T (fun x => -u x)
      = fun x => - Work.Diff.STE.B3.SymCalc.compMap T u x := compMap_neg T u
  have h3 := flatCut_neg ρ ε (Work.Diff.STE.B3.SymCalc.compMap T u)
  unfold Work.Diff.STE.B3.SymCalc.conjCut
  rw [h1, h3, compMap_neg T'
    (Work.Diff.STE.B3.SymCalc.flatCut ρ ε (Work.Diff.STE.B3.SymCalc.compMap T u))]

/-! ## Smoothness and periodicity of the conjugate Laplacian power -/

/-- `conjLapPow k T T' u` is `1`-periodic, for every argument `u`: the only input is that the
Fourier multiplier `lapPow k` (being a `seriesFun`) is `1`-periodic. -/
theorem conjLapPow_periodic (T T' : (ι → ℝ) → (ι → ℝ))
    (hTper : ∀ (i : ι) (x : ι → ℝ), T (x + Pi.single i 1) = T x + Pi.single i 1) (k : ℕ)
    (u : (ι → ℝ) → ℂ) :
    Work.Diff.STE.Periodic1 (Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T' u) := by
  have hdef : Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T' u
      = Work.Diff.STE.B3.SymCalc.compMap T
          (Work.Diff.STE.B3.SymCalcStep5.lapPow k (Work.Diff.STE.B3.SymCalc.compMap T' u)) :=
    rfl
  rw [hdef]
  intro i x
  show Work.Diff.STE.B3.SymCalcStep5.lapPow k (Work.Diff.STE.B3.SymCalc.compMap T' u)
      (T (x + Pi.single i 1))
    = Work.Diff.STE.B3.SymCalcStep5.lapPow k (Work.Diff.STE.B3.SymCalc.compMap T' u) (T x)
  rw [hTper i x]
  exact (lapPow_toolbox (ι := ι) k 0).2.2.2 _ i (T x)

/-- `conjLapPow k T T' u` is smooth for smooth `1`-periodic `u`. -/
theorem conjLapPow_contDiff (T T' : (ι → ℝ) → (ι → ℝ)) (hT : ContDiff ℝ (⊤ : ℕ∞) T)
    (hT' : ContDiff ℝ (⊤ : ℕ∞) T')
    (hTper : ∀ (i : ι) (x : ι → ℝ), T (x + Pi.single i 1) = T x + Pi.single i 1)
    (hTinv1 : ∀ x : ι → ℝ, T' (T x) = x) (hTinv2 : ∀ y : ι → ℝ, T (T' y) = y) (k : ℕ)
    {u : (ι → ℝ) → ℂ} (hu : ContDiff ℝ (⊤ : ℕ∞) u) (hup : Work.Diff.STE.Periodic1 u) :
    ContDiff ℝ (⊤ : ℕ∞) (Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T' u) := by
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (Work.Diff.STE.B3.SymCalc.compMap T' u) := hu.comp hT'
  have h1p : Work.Diff.STE.Periodic1 (Work.Diff.STE.B3.SymCalc.compMap T' u) := by
    intro i x
    show u (T' (x + Pi.single i 1)) = u (T' x)
    rw [Work.Diff.STE.B3.SymCalcStep1.shift_T' T T' hTper hTinv1 hTinv2 i x]
    exact hup i (T' x)
  have h2 : ContDiff ℝ (⊤ : ℕ∞)
      (Work.Diff.STE.B3.SymCalcStep5.lapPow k (Work.Diff.STE.B3.SymCalc.compMap T' u)) :=
    (lapPow_toolbox (ι := ι) k 0).2.2.1 _ h1 h1p
  exact h2.comp hT

/-! ## The commutator `W k ε h = [P_k, S_ε] h` -/

/-- The commutator of the conjugate Laplacian power with the Friedrichs cutoff. -/
def W (ρ : (ι → ℝ) → ℝ) (T T' : (ι → ℝ) → (ι → ℝ)) (k : ℕ) (ε : ℝ) (h : (ι → ℝ) → ℂ) :
    (ι → ℝ) → ℂ :=
  Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T' (Work.Diff.STE.B3.SymCalc.flatCut ρ ε h)
    - Work.Diff.STE.B3.SymCalc.flatCut ρ ε
        (Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T' h)

/-- `W` preserves smoothness. -/
theorem W_contDiff (ρ : (ι → ℝ) → ℝ) (hρb : ∀ y : ι → ℝ, ‖ρ y‖ ≤ 1)
    (T T' : (ι → ℝ) → (ι → ℝ)) (hT : ContDiff ℝ (⊤ : ℕ∞) T) (hT' : ContDiff ℝ (⊤ : ℕ∞) T')
    (hTper : ∀ (i : ι) (x : ι → ℝ), T (x + Pi.single i 1) = T x + Pi.single i 1)
    (hTinv1 : ∀ x : ι → ℝ, T' (T x) = x) (hTinv2 : ∀ y : ι → ℝ, T (T' y) = y)
    (k : ℕ) (ε : ℝ) {h : (ι → ℝ) → ℂ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hhp : Work.Diff.STE.Periodic1 h) :
    ContDiff ℝ (⊤ : ℕ∞) (W ρ T T' k ε h) := by
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (Work.Diff.STE.B3.SymCalc.flatCut ρ ε h) :=
    Work.Diff.STE.B3.SymCalcStep1.flatCut_contDiff ρ hρb ε hh hhp
  have h1p : Work.Diff.STE.Periodic1 (Work.Diff.STE.B3.SymCalc.flatCut ρ ε h) :=
    Work.Diff.STE.B3.SymCalcStep1.flatCut_periodic ρ ε h
  have h2 : ContDiff ℝ (⊤ : ℕ∞)
      (Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T' h) :=
    conjLapPow_contDiff T T' hT hT' hTper hTinv1 hTinv2 k hh hhp
  have h2p : Work.Diff.STE.Periodic1 (Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T' h) :=
    conjLapPow_periodic T T' hTper k h
  exact (conjLapPow_contDiff T T' hT hT' hTper hTinv1 hTinv2 k h1 h1p).sub
    (Work.Diff.STE.B3.SymCalcStep1.flatCut_contDiff ρ hρb ε h2 h2p)

/-- `W` preserves `1`-periodicity. -/
theorem W_periodic (ρ : (ι → ℝ) → ℝ) (T T' : (ι → ℝ) → (ι → ℝ))
    (hTper : ∀ (i : ι) (x : ι → ℝ), T (x + Pi.single i 1) = T x + Pi.single i 1)
    (k : ℕ) (ε : ℝ) (h : (ι → ℝ) → ℂ) :
    Work.Diff.STE.Periodic1 (W ρ T T' k ε h) :=
  Work.Diff.STE.B3.SymCalcStep1.Periodic1_sub'
    (conjLapPow_periodic T T' hTper k (Work.Diff.STE.B3.SymCalc.flatCut ρ ε h))
    (Work.Diff.STE.B3.SymCalcStep1.flatCut_periodic ρ ε _)

/-! ## The order-`2j` bound for `P_j` -/

/-- `P_j = conjLapPow j T T'` composes: `P_{i+j} = P_i ∘ P_j` (on smooth `1`-periodic
functions), because the multipliers `Λ^i` compose. -/
theorem conjLapPow_succ (T T' : (ι → ℝ) → (ι → ℝ)) (hT : ContDiff ℝ (⊤ : ℕ∞) T)
    (hT' : ContDiff ℝ (⊤ : ℕ∞) T')
    (hTper : ∀ (i : ι) (x : ι → ℝ), T (x + Pi.single i 1) = T x + Pi.single i 1)
    (hTinv1 : ∀ x : ι → ℝ, T' (T x) = x) (hTinv2 : ∀ y : ι → ℝ, T (T' y) = y) (k : ℕ)
    {u : (ι → ℝ) → ℂ} (hu : ContDiff ℝ (⊤ : ℕ∞) u) (hup : Work.Diff.STE.Periodic1 u) :
    Work.Diff.STE.B3.SymCalcStep5.conjLapPow (k + 1) T T' u
      = Work.Diff.STE.B3.SymCalcStep5.conjLapPow 1 T T'
          (Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T' u) := by
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (Work.Diff.STE.B3.SymCalc.compMap T' u) := hu.comp hT'
  have h1p : Work.Diff.STE.Periodic1 (Work.Diff.STE.B3.SymCalc.compMap T' u) := by
    intro i x
    show u (T' (x + Pi.single i 1)) = u (T' x)
    rw [Work.Diff.STE.B3.SymCalcStep1.shift_T' T T' hTper hTinv1 hTinv2 i x]
    exact hup i (T' x)
  have hkey : Work.Diff.STE.B3.SymCalcStep5.lapPow 1
        (Work.Diff.STE.B3.SymCalcStep5.lapPow k (Work.Diff.STE.B3.SymCalc.compMap T' u))
      = Work.Diff.STE.B3.SymCalcStep5.lapPow (k + 1)
          (Work.Diff.STE.B3.SymCalc.compMap T' u) := by
    rw [Work.Diff.STE.B3.SymCalcStep6.lapPow_algebra.1 1 k _ h1 h1p, Nat.add_comm 1 k]
  have hgoal : Work.Diff.STE.B3.SymCalcStep5.conjLapPow (k + 1) T T' u
      = Work.Diff.STE.B3.SymCalc.compMap T
          (Work.Diff.STE.B3.SymCalcStep5.lapPow (k + 1)
            (Work.Diff.STE.B3.SymCalc.compMap T' u)) := rfl
  rw [hgoal]
  show Work.Diff.STE.B3.SymCalc.compMap T
        (Work.Diff.STE.B3.SymCalcStep5.lapPow (k + 1)
          (Work.Diff.STE.B3.SymCalc.compMap T' u))
      = Work.Diff.STE.B3.SymCalc.compMap T
        (Work.Diff.STE.B3.SymCalcStep5.lapPow 1
          (Work.Diff.STE.B3.SymCalc.compMap T'
            (Work.Diff.STE.B3.SymCalc.compMap T
              (Work.Diff.STE.B3.SymCalcStep5.lapPow k
                (Work.Diff.STE.B3.SymCalc.compMap T' u)))))
  rw [Work.Diff.STE.B3.SymCalcStep5.compMap_T'_compMap_T T T' hTinv2
    (Work.Diff.STE.B3.SymCalcStep5.lapPow k (Work.Diff.STE.B3.SymCalc.compMap T' u)), hkey]

/-- `P_j = conjLapPow j T T'` is additive on smooth `1`-periodic functions. -/
theorem conjLapPow_add (T T' : (ι → ℝ) → (ι → ℝ)) (hT' : ContDiff ℝ (⊤ : ℕ∞) T')
    (hTper : ∀ (i : ι) (x : ι → ℝ), T (x + Pi.single i 1) = T x + Pi.single i 1)
    (hTinv1 : ∀ x : ι → ℝ, T' (T x) = x) (hTinv2 : ∀ y : ι → ℝ, T (T' y) = y) (k : ℕ)
    {u v : (ι → ℝ) → ℂ} (hu : ContDiff ℝ (⊤ : ℕ∞) u) (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    (hup : Work.Diff.STE.Periodic1 u) (hvp : Work.Diff.STE.Periodic1 v) :
    Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T' (u + v)
      = Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T' u
        + Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T' v := by
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (Work.Diff.STE.B3.SymCalc.compMap T' u) := hu.comp hT'
  have h2 : ContDiff ℝ (⊤ : ℕ∞) (Work.Diff.STE.B3.SymCalc.compMap T' v) := hv.comp hT'
  have h1p : Work.Diff.STE.Periodic1 (Work.Diff.STE.B3.SymCalc.compMap T' u) := by
    intro i x
    show u (T' (x + Pi.single i 1)) = u (T' x)
    rw [Work.Diff.STE.B3.SymCalcStep1.shift_T' T T' hTper hTinv1 hTinv2 i x]
    exact hup i (T' x)
  have h2p : Work.Diff.STE.Periodic1 (Work.Diff.STE.B3.SymCalc.compMap T' v) := by
    intro i x
    show v (T' (x + Pi.single i 1)) = v (T' x)
    rw [Work.Diff.STE.B3.SymCalcStep1.shift_T' T T' hTper hTinv1 hTinv2 i x]
    exact hvp i (T' x)
  have hsum : Work.Diff.STE.B3.SymCalc.compMap T' (u + v)
      = Work.Diff.STE.B3.SymCalc.compMap T' u + Work.Diff.STE.B3.SymCalc.compMap T' v :=
    compMap_add T' u v
  have hlap := lapPow_algebra.2 k _ _ h1 h2 h1p h2p
  have hcomp := compMap_add T
    (Work.Diff.STE.B3.SymCalcStep5.lapPow k (Work.Diff.STE.B3.SymCalc.compMap T' u))
    (Work.Diff.STE.B3.SymCalcStep5.lapPow k (Work.Diff.STE.B3.SymCalc.compMap T' v))
  show Work.Diff.STE.B3.SymCalc.compMap T
        (Work.Diff.STE.B3.SymCalcStep5.lapPow k (Work.Diff.STE.B3.SymCalc.compMap T' (u + v)))
      = Work.Diff.STE.B3.SymCalc.compMap T
          (Work.Diff.STE.B3.SymCalcStep5.lapPow k (Work.Diff.STE.B3.SymCalc.compMap T' u))
        + Work.Diff.STE.B3.SymCalc.compMap T
          (Work.Diff.STE.B3.SymCalcStep5.lapPow k (Work.Diff.STE.B3.SymCalc.compMap T' v))
  rw [hsum, hlap, hcomp]

/-- `P_j` costs exactly `2j` derivatives on the `CSq` scale, uniformly in the frequency. -/
theorem conjLapPow_CSq_le (T T' : (ι → ℝ) → (ι → ℝ)) (hT : ContDiff ℝ (⊤ : ℕ∞) T)
    (hT' : ContDiff ℝ (⊤ : ℕ∞) T')
    (hTper : ∀ (i : ι) (x : ι → ℝ), T (x + Pi.single i 1) = T x + Pi.single i 1)
    (hTinv1 : ∀ x : ι → ℝ, T' (T x) = x) (hTinv2 : ∀ y : ι → ℝ, T (T' y) = y)
    (hinjT : Function.Injective T) (hinjT' : Function.Injective T')
    (hdetT : ∀ z : ι → ℝ, (fderiv ℝ T z).det ≠ 0)
    (hdetT' : ∀ z : ι → ℝ, (fderiv ℝ T' z).det ≠ 0) (j Lv : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ u : (ι → ℝ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) u →
      Work.Diff.STE.Periodic1 u →
      Work.Diff.STE.CSq Lv (Work.Diff.STE.fourierCoeff
          (Work.Diff.STE.B3.SymCalcStep5.conjLapPow j T T' u))
        ≤ K * Work.Diff.STE.CSq (Lv + 2 * j) (Work.Diff.STE.fourierCoeff u) := by
  have hshift : ∀ (i : ι) (z : ι → ℝ), T' (z + Pi.single i 1) = T' z + Pi.single i 1 :=
    fun i => Work.Diff.STE.B3.SymCalcStep1.shift_T' T T' hTper hTinv1 hTinv2 i
  obtain ⟨K1, hK1, hK1b⟩ :=
    Work.Diff.STE.B3.SymCalcStep1.fourierCoeff_comp_le Lv T hT hTper hinjT hdetT
  obtain ⟨K2, hK2, hK2b⟩ := (lapPow_toolbox (ι := ι) j Lv).2.1
  obtain ⟨K3, hK3, hK3b⟩ :=
    Work.Diff.STE.B3.SymCalcStep1.fourierCoeff_comp_le (Lv + 2 * j) T' hT' hshift hinjT' hdetT'
  refine ⟨K1 * K2 * K3, by positivity, fun u hu hup => ?_⟩
  have hw1 : ContDiff ℝ (⊤ : ℕ∞) (Work.Diff.STE.B3.SymCalc.compMap T' u) := hu.comp hT'
  have hw1p : Work.Diff.STE.Periodic1 (Work.Diff.STE.B3.SymCalc.compMap T' u) := by
    intro i x
    show u (T' (x + Pi.single i 1)) = u (T' x)
    rw [hshift i x]
    exact hup i (T' x)
  have hw2 : ContDiff ℝ (⊤ : ℕ∞)
      (Work.Diff.STE.B3.SymCalcStep5.lapPow j (Work.Diff.STE.B3.SymCalc.compMap T' u)) :=
    (lapPow_toolbox (ι := ι) j Lv).2.2.1 _ hw1 hw1p
  have hw2p : Work.Diff.STE.Periodic1
      (Work.Diff.STE.B3.SymCalcStep5.lapPow j (Work.Diff.STE.B3.SymCalc.compMap T' u)) :=
    (lapPow_toolbox (ι := ι) j Lv).2.2.2 _
  show Work.Diff.STE.CSq Lv (Work.Diff.STE.fourierCoeff (Work.Diff.STE.B3.SymCalc.compMap T
        (Work.Diff.STE.B3.SymCalcStep5.lapPow j (Work.Diff.STE.B3.SymCalc.compMap T' u))))
      ≤ (K1 * K2 * K3) * Work.Diff.STE.CSq (Lv + 2 * j) (Work.Diff.STE.fourierCoeff u)
  calc Work.Diff.STE.CSq Lv (Work.Diff.STE.fourierCoeff (Work.Diff.STE.B3.SymCalc.compMap T
        (Work.Diff.STE.B3.SymCalcStep5.lapPow j (Work.Diff.STE.B3.SymCalc.compMap T' u))))
      ≤ K1 * Work.Diff.STE.CSq Lv (Work.Diff.STE.fourierCoeff
          (Work.Diff.STE.B3.SymCalcStep5.lapPow j (Work.Diff.STE.B3.SymCalc.compMap T' u))) :=
        hK1b _ hw2 hw2p
    _ ≤ K1 * (K2 * Work.Diff.STE.CSq (Lv + 2 * j)
          (Work.Diff.STE.fourierCoeff (Work.Diff.STE.B3.SymCalc.compMap T' u))) :=
        mul_le_mul_of_nonneg_left (hK2b _ hw1 hw1p) hK1
    _ ≤ K1 * (K2 * (K3 * Work.Diff.STE.CSq (Lv + 2 * j)
          (Work.Diff.STE.fourierCoeff u))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hK3b u hu hup) hK2) hK1
    _ = (K1 * K2 * K3) * Work.Diff.STE.CSq (Lv + 2 * j) (Work.Diff.STE.fourierCoeff u) := by
        ring

/-! ## The recursion `[P_{k+1}, S_ε] = P_1 [P_k, S_ε] + [P_1, S_ε] P_k` -/

/-- The recursion for the commutator defect `W` (as a function identity). -/
theorem W_succ (ρ : (ι → ℝ) → ℝ) (hρb : ∀ y : ι → ℝ, ‖ρ y‖ ≤ 1)
    (T T' : (ι → ℝ) → (ι → ℝ)) (hT : ContDiff ℝ (⊤ : ℕ∞) T) (hT' : ContDiff ℝ (⊤ : ℕ∞) T')
    (hTper : ∀ (i : ι) (x : ι → ℝ), T (x + Pi.single i 1) = T x + Pi.single i 1)
    (hTinv1 : ∀ x : ι → ℝ, T' (T x) = x) (hTinv2 : ∀ y : ι → ℝ, T (T' y) = y)
    (k : ℕ) (ε : ℝ) {h : (ι → ℝ) → ℂ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hhp : Work.Diff.STE.Periodic1 h) :
    W ρ T T' (k + 1) ε h
      = Work.Diff.STE.B3.SymCalcStep5.conjLapPow 1 T T' (W ρ T T' k ε h)
        + W ρ T T' 1 ε (Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T' h) := by
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (Work.Diff.STE.B3.SymCalc.flatCut ρ ε h) :=
    Work.Diff.STE.B3.SymCalcStep1.flatCut_contDiff ρ hρb ε hh hhp
  have h1p : Work.Diff.STE.Periodic1 (Work.Diff.STE.B3.SymCalc.flatCut ρ ε h) :=
    Work.Diff.STE.B3.SymCalcStep1.flatCut_periodic ρ ε h
  have h3 : ContDiff ℝ (⊤ : ℕ∞)
      (Work.Diff.STE.B3.SymCalc.flatCut ρ ε
        (Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T' h)) :=
    Work.Diff.STE.B3.SymCalcStep1.flatCut_contDiff ρ hρb ε
      (conjLapPow_contDiff T T' hT hT' hTper hTinv1 hTinv2 k hh hhp)
      (conjLapPow_periodic T T' hTper k h)
  have h3p : Work.Diff.STE.Periodic1
      (Work.Diff.STE.B3.SymCalc.flatCut ρ ε
        (Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T' h)) :=
    Work.Diff.STE.B3.SymCalcStep1.flatCut_periodic ρ ε _
  have hW : ContDiff ℝ (⊤ : ℕ∞) (W ρ T T' k ε h) :=
    W_contDiff ρ hρb T T' hT hT' hTper hTinv1 hTinv2 k ε hh hhp
  have hWp : Work.Diff.STE.Periodic1 (W ρ T T' k ε h) := W_periodic ρ T T' hTper k ε h
  have hA : Work.Diff.STE.B3.SymCalcStep5.conjLapPow (k + 1) T T'
        (Work.Diff.STE.B3.SymCalc.flatCut ρ ε h)
      = Work.Diff.STE.B3.SymCalcStep5.conjLapPow 1 T T'
          (Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T'
            (Work.Diff.STE.B3.SymCalc.flatCut ρ ε h)) :=
    conjLapPow_succ T T' hT hT' hTper hTinv1 hTinv2 k h1 h1p
  have hB : Work.Diff.STE.B3.SymCalcStep5.conjLapPow (k + 1) T T' h
      = Work.Diff.STE.B3.SymCalcStep5.conjLapPow 1 T T'
          (Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T' h) :=
    conjLapPow_succ T T' hT hT' hTper hTinv1 hTinv2 k hh hhp
  have hC : Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T'
        (Work.Diff.STE.B3.SymCalc.flatCut ρ ε h)
      = W ρ T T' k ε h + Work.Diff.STE.B3.SymCalc.flatCut ρ ε
          (Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T' h) := by
    rw [W, sub_add_cancel]
  have hD : Work.Diff.STE.B3.SymCalcStep5.conjLapPow 1 T T'
        (W ρ T T' k ε h + Work.Diff.STE.B3.SymCalc.flatCut ρ ε
          (Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T' h))
      = Work.Diff.STE.B3.SymCalcStep5.conjLapPow 1 T T' (W ρ T T' k ε h)
        + Work.Diff.STE.B3.SymCalcStep5.conjLapPow 1 T T'
            (Work.Diff.STE.B3.SymCalc.flatCut ρ ε
              (Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T' h)) :=
    conjLapPow_add T T' hT' hTper hTinv1 hTinv2 1 hW h3 hWp h3p
  have hstep1 : W ρ T T' (k + 1) ε h
      = Work.Diff.STE.B3.SymCalcStep5.conjLapPow 1 T T'
            (Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T'
              (Work.Diff.STE.B3.SymCalc.flatCut ρ ε h))
        - Work.Diff.STE.B3.SymCalc.flatCut ρ ε
            (Work.Diff.STE.B3.SymCalcStep5.conjLapPow 1 T T'
              (Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T' h)) := by
    rw [W, hA, hB]
  have hstep4 : Work.Diff.STE.B3.SymCalcStep5.conjLapPow 1 T T'
          (Work.Diff.STE.B3.SymCalc.flatCut ρ ε
            (Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T' h))
        - Work.Diff.STE.B3.SymCalc.flatCut ρ ε
            (Work.Diff.STE.B3.SymCalcStep5.conjLapPow 1 T T'
              (Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T' h))
      = W ρ T T' 1 ε (Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T' h) := by
    rw [W]
  calc W ρ T T' (k + 1) ε h
      = Work.Diff.STE.B3.SymCalcStep5.conjLapPow 1 T T'
            (Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T'
              (Work.Diff.STE.B3.SymCalc.flatCut ρ ε h))
        - Work.Diff.STE.B3.SymCalc.flatCut ρ ε
            (Work.Diff.STE.B3.SymCalcStep5.conjLapPow 1 T T'
              (Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T' h)) := hstep1
    _ = Work.Diff.STE.B3.SymCalcStep5.conjLapPow 1 T T'
          (W ρ T T' k ε h + Work.Diff.STE.B3.SymCalc.flatCut ρ ε
            (Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T' h))
        - Work.Diff.STE.B3.SymCalc.flatCut ρ ε
            (Work.Diff.STE.B3.SymCalcStep5.conjLapPow 1 T T'
              (Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T' h)) := by rw [hC]
    _ = (Work.Diff.STE.B3.SymCalcStep5.conjLapPow 1 T T' (W ρ T T' k ε h)
          + Work.Diff.STE.B3.SymCalcStep5.conjLapPow 1 T T'
              (Work.Diff.STE.B3.SymCalc.flatCut ρ ε
                (Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T' h)))
        - Work.Diff.STE.B3.SymCalc.flatCut ρ ε
            (Work.Diff.STE.B3.SymCalcStep5.conjLapPow 1 T T'
              (Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T' h)) := by rw [hD]
    _ = Work.Diff.STE.B3.SymCalcStep5.conjLapPow 1 T T' (W ρ T T' k ε h)
          + (Work.Diff.STE.B3.SymCalcStep5.conjLapPow 1 T T'
              (Work.Diff.STE.B3.SymCalc.flatCut ρ ε
                (Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T' h))
            - Work.Diff.STE.B3.SymCalc.flatCut ρ ε
                (Work.Diff.STE.B3.SymCalcStep5.conjLapPow 1 T T'
                  (Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T' h))) := by
        funext x
        simp only [Pi.add_apply, Pi.sub_apply]
        ring
    _ = Work.Diff.STE.B3.SymCalcStep5.conjLapPow 1 T T' (W ρ T T' k ε h)
          + W ρ T T' 1 ε (Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T' h) := by
        rw [hstep4]

/-! ## The `k = 1` case -/

/-- The `k = 1` case: `[P_1, S_ε] = −[pullLap, S_ε]` is of order `1`, uniformly in `ε`. -/
theorem W_one_bound (ρ : (ι → ℝ) → ℝ) (hρb : ∀ y : ι → ℝ, ‖ρ y‖ ≤ 1)
    (hdiam : ∀ y : ι → ℝ, 2 < ∑ i, (y i) ^ 2 → ρ y = 0)
    (L : ℝ) (hL : 0 ≤ L) (hρlip : ∀ y z : ι → ℝ, ‖ρ y - ρ z‖ ≤ L * ‖y - z‖)
    (T T' : (ι → ℝ) → (ι → ℝ)) (hT : ContDiff ℝ (⊤ : ℕ∞) T) (hT' : ContDiff ℝ (⊤ : ℕ∞) T')
    (hTper : ∀ (i : ι) (x : ι → ℝ), T (x + Pi.single i 1) = T x + Pi.single i 1)
    (hTinv1 : ∀ x : ι → ℝ, T' (T x) = x) (hTinv2 : ∀ y : ι → ℝ, T (T' y) = y) (s : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ h : (ι → ℝ) → ℂ,
      ContDiff ℝ (⊤ : ℕ∞) h → Work.Diff.STE.Periodic1 h →
      Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff (W ρ T T' 1 ε h))
        ≤ C * Work.Diff.STE.CSq (s + 1) (Work.Diff.STE.fourierCoeff h) := by
  obtain ⟨C, hC, hCb⟩ := Work.Diff.STE.B3.SymCalcStep1.pullLap_comm_bound_self ρ hρb hdiam L hL
    hρlip T T' hTper hTinv1 hTinv2 hT hT' s
  refine ⟨C, hC, fun ε hε hε1 h hh hhp => ?_⟩
  have hSsm : ContDiff ℝ (⊤ : ℕ∞) (Work.Diff.STE.B3.SymCalc.flatCut ρ ε h) :=
    Work.Diff.STE.B3.SymCalcStep1.flatCut_contDiff ρ hρb ε hh hhp
  have hSp : Work.Diff.STE.Periodic1 (Work.Diff.STE.B3.SymCalc.flatCut ρ ε h) :=
    Work.Diff.STE.B3.SymCalcStep1.flatCut_periodic ρ ε h
  have hV1 : ∀ {u : (ι → ℝ) → ℂ}, ContDiff ℝ (⊤ : ℕ∞) u → Work.Diff.STE.Periodic1 u →
      Work.Diff.STE.B3.SymCalcStep5.conjLapPow 1 T T' u
        = fun x => - Work.Diff.STE.B3.SymCalcStep1.pullLap T T' u x := by
    intro u hu hup
    have h1 : ContDiff ℝ (⊤ : ℕ∞) (Work.Diff.STE.B3.SymCalc.compMap T' u) := hu.comp hT'
    have h1p : Work.Diff.STE.Periodic1 (Work.Diff.STE.B3.SymCalc.compMap T' u) := by
      intro i x
      show u (T' (x + Pi.single i 1)) = u (T' x)
      rw [Work.Diff.STE.B3.SymCalcStep1.shift_T' T T' hTper hTinv1 hTinv2 i x]
      exact hup i (T' x)
    have hlap : Work.Diff.STE.B3.SymCalcStep5.lapPow 1
          (Work.Diff.STE.B3.SymCalc.compMap T' u)
        = fun y => - Work.Diff.STE.B3.SymCalc.lapC
            (Work.Diff.STE.B3.SymCalc.compMap T' u) y :=
      funext fun y => Work.Diff.STE.B3.SymCalcStep6.lapPow_one_eq_neg_lapC _ h1 h1p y
    show Work.Diff.STE.B3.SymCalc.compMap T
        (Work.Diff.STE.B3.SymCalcStep5.lapPow 1 (Work.Diff.STE.B3.SymCalc.compMap T' u))
      = fun x => - Work.Diff.STE.B3.SymCalcStep1.pullLap T T' u x
    rw [hlap]
    rfl
  have hid : W ρ T T' 1 ε h
      = - (Work.Diff.STE.B3.SymCalcStep1.pullLap T T' (Work.Diff.STE.B3.SymCalc.flatCut ρ ε h)
          - Work.Diff.STE.B3.SymCalc.flatCut ρ ε
              (Work.Diff.STE.B3.SymCalcStep1.pullLap T T' h)) := by
    rw [W, hV1 hSsm hSp, hV1 hh hhp]
    rw [flatCut_neg]
    funext x
    simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply]
    ring
  rw [hid]
  calc Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff (fun x =>
          - (Work.Diff.STE.B3.SymCalcStep1.pullLap T T' (Work.Diff.STE.B3.SymCalc.flatCut ρ ε h)
            - Work.Diff.STE.B3.SymCalc.flatCut ρ ε
                (Work.Diff.STE.B3.SymCalcStep1.pullLap T T' h)) x))
      = Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff
          (Work.Diff.STE.B3.SymCalcStep1.pullLap T T' (Work.Diff.STE.B3.SymCalc.flatCut ρ ε h)
            - Work.Diff.STE.B3.SymCalc.flatCut ρ ε
                (Work.Diff.STE.B3.SymCalcStep1.pullLap T T' h))) :=
        CSq_fourierCoeff_neg s _
    _ ≤ C * Work.Diff.STE.CSq (s + 1) (Work.Diff.STE.fourierCoeff h) :=
        hCb ε hε hε1 h hh hhp

/-! ## The induction in `k` -/

/-- The main estimate for `W k ε h = [P_k, S_ε] h`: order `2k − 1`, uniformly in `ε`. -/
theorem W_bound (ρ : (ι → ℝ) → ℝ) (hρb : ∀ y : ι → ℝ, ‖ρ y‖ ≤ 1)
    (hdiam : ∀ y : ι → ℝ, 2 < ∑ i, (y i) ^ 2 → ρ y = 0)
    (L : ℝ) (hL : 0 ≤ L) (hρlip : ∀ y z : ι → ℝ, ‖ρ y - ρ z‖ ≤ L * ‖y - z‖)
    (T T' : (ι → ℝ) → (ι → ℝ)) (hT : ContDiff ℝ (⊤ : ℕ∞) T) (hT' : ContDiff ℝ (⊤ : ℕ∞) T')
    (hTper : ∀ (i : ι) (x : ι → ℝ), T (x + Pi.single i 1) = T x + Pi.single i 1)
    (hTinv1 : ∀ x : ι → ℝ, T' (T x) = x) (hTinv2 : ∀ y : ι → ℝ, T (T' y) = y)
    (k : ℕ) (hk : 1 ≤ k) (s : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ h : (ι → ℝ) → ℂ,
      ContDiff ℝ (⊤ : ℕ∞) h → Work.Diff.STE.Periodic1 h →
      Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff (W ρ T T' k ε h))
        ≤ C * Work.Diff.STE.CSq (s + 2 * k - 1) (Work.Diff.STE.fourierCoeff h) := by
  classical
  -- the two `ε`-free estimates on the composite operators
  have hinjT : Function.Injective T := fun x y hxy => by rw [← hTinv1 x, hxy, hTinv1 y]
  have hinjT' : Function.Injective T' := fun x y hxy => by rw [← hTinv2 x, hxy, hTinv2 y]
  have hdet_of : ∀ (A B : (ι → ℝ) →L[ℝ] (ι → ℝ)), A.comp B = 1 → B.det ≠ 0 := by
    intro A B hcomp hz
    have hinj : Function.Injective B := fun u v huv => by
      have h1 := congrArg (fun (L : (ι → ℝ) →L[ℝ] (ι → ℝ)) => L u) hcomp
      have h2 := congrArg (fun (L : (ι → ℝ) →L[ℝ] (ι → ℝ)) => L v) hcomp
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.one_apply] at h1 h2
      rw [huv] at h1
      exact h1.symm.trans h2
    have hz' : LinearMap.det ((B : (ι → ℝ) →ₗ[ℝ] (ι → ℝ))) = 0 := hz
    exact (LinearMap.det_eq_zero_iff_ker_ne_bot.mp hz') (by rw [LinearMap.ker_eq_bot]; exact hinj)
  have hdetT : ∀ z : ι → ℝ, (fderiv ℝ T z).det ≠ 0 := by
    intro z
    have hcomp : fderiv ℝ (fun x => T' (T x)) z
        = (fderiv ℝ T' (T z)).comp (fderiv ℝ T z) :=
      fderiv_comp z ((hT'.differentiable (by simp)).differentiableAt)
        ((hT.differentiable (by simp)).differentiableAt)
    have h1 : fderiv ℝ (fun x => T' (T x)) z = 1 := by
      rw [show (fun x : ι → ℝ => T' (T x)) = id from funext hTinv1]
      exact fderiv_id
    have h2 : (fderiv ℝ T' (T z)).comp (fderiv ℝ T z) = 1 := by rw [← hcomp]; exact h1
    exact hdet_of _ _ h2
  have hdetT' : ∀ z : ι → ℝ, (fderiv ℝ T' z).det ≠ 0 := by
    intro z
    have hcomp : fderiv ℝ (fun y => T (T' y)) z
        = (fderiv ℝ T (T' z)).comp (fderiv ℝ T' z) :=
      fderiv_comp z ((hT.differentiable (by simp)).differentiableAt)
        ((hT'.differentiable (by simp)).differentiableAt)
    have h1 : fderiv ℝ (fun y => T (T' y)) z = 1 := by
      rw [show (fun y : ι → ℝ => T (T' y)) = id from funext hTinv2]
      exact fderiv_id
    have h2 : (fderiv ℝ T (T' z)).comp (fderiv ℝ T' z) = 1 := by rw [← hcomp]; exact h1
    exact hdet_of _ _ h2
  have hCL : ∀ (j Lv : ℕ), ∃ K : ℝ, 0 ≤ K ∧ ∀ u : (ι → ℝ) → ℂ,
      ContDiff ℝ (⊤ : ℕ∞) u → Work.Diff.STE.Periodic1 u →
      Work.Diff.STE.CSq Lv (Work.Diff.STE.fourierCoeff
          (Work.Diff.STE.B3.SymCalcStep5.conjLapPow j T T' u))
        ≤ K * Work.Diff.STE.CSq (Lv + 2 * j) (Work.Diff.STE.fourierCoeff u) :=
    fun j Lv => conjLapPow_CSq_le T T' hT hT' hTper hTinv1 hTinv2 hinjT hinjT' hdetT hdetT' j Lv
  have keyY : ∀ j : ℕ, ∀ s' : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∀ h : (ι → ℝ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) h → Work.Diff.STE.Periodic1 h →
      Work.Diff.STE.CSq s' (Work.Diff.STE.fourierCoeff (W ρ T T' (j + 1) ε h))
        ≤ C * Work.Diff.STE.CSq (s' + 2 * (j + 1) - 1) (Work.Diff.STE.fourierCoeff h) := by
    intro j
    induction j with
    | zero =>
        intro s'
        exact W_one_bound ρ hρb hdiam L hL hρlip T T' hT hT' hTper hTinv1 hTinv2 s'
    | succ j IH =>
        intro s'
        obtain ⟨C1, hC1, hC1b⟩ := IH (s' + 2)
        obtain ⟨K1, hK1, hK1b⟩ := hCL 1 s'
        obtain ⟨Kn, hKn, hKnb⟩ := hCL (j + 1) (s' + 1)
        obtain ⟨Cb, hCb, hCbb⟩ :=
          W_one_bound ρ hρb hdiam L hL hρlip T T' hT hT' hTper hTinv1 hTinv2 s'
        refine ⟨2 * (K1 * C1 + Cb * Kn), by positivity, fun ε hε hε1 h hh hhp => ?_⟩
        have hWsm : ContDiff ℝ (⊤ : ℕ∞) (W ρ T T' (j + 1) ε h) :=
          W_contDiff ρ hρb T T' hT hT' hTper hTinv1 hTinv2 (j + 1) ε hh hhp
        have hWp : Work.Diff.STE.Periodic1 (W ρ T T' (j + 1) ε h) :=
          W_periodic ρ T T' hTper (j + 1) ε h
        have hCLsm : ContDiff ℝ (⊤ : ℕ∞)
            (Work.Diff.STE.B3.SymCalcStep5.conjLapPow (j + 1) T T' h) :=
          conjLapPow_contDiff T T' hT hT' hTper hTinv1 hTinv2 (j + 1) hh hhp
        have hCLp : Work.Diff.STE.Periodic1
            (Work.Diff.STE.B3.SymCalcStep5.conjLapPow (j + 1) T T' h) :=
          conjLapPow_periodic T T' hTper (j + 1) h
        have hAsm : ContDiff ℝ (⊤ : ℕ∞)
            (Work.Diff.STE.B3.SymCalcStep5.conjLapPow 1 T T' (W ρ T T' (j + 1) ε h)) :=
          conjLapPow_contDiff T T' hT hT' hTper hTinv1 hTinv2 1 hWsm hWp
        have hBsm : ContDiff ℝ (⊤ : ℕ∞)
            (W ρ T T' 1 ε (Work.Diff.STE.B3.SymCalcStep5.conjLapPow (j + 1) T T' h)) :=
          W_contDiff ρ hρb T T' hT hT' hTper hTinv1 hTinv2 1 ε hCLsm hCLp
        rw [W_succ ρ hρb T T' hT hT' hTper hTinv1 hTinv2 (j + 1) ε hh hhp]
        have hfc : Work.Diff.STE.fourierCoeff
            (Work.Diff.STE.B3.SymCalcStep5.conjLapPow 1 T T' (W ρ T T' (j + 1) ε h)
              + W ρ T T' 1 ε (Work.Diff.STE.B3.SymCalcStep5.conjLapPow (j + 1) T T' h))
            = fun k => Work.Diff.STE.fourierCoeff
                (Work.Diff.STE.B3.SymCalcStep5.conjLapPow 1 T T' (W ρ T T' (j + 1) ε h)) k
              + Work.Diff.STE.fourierCoeff
                (W ρ T T' 1 ε (Work.Diff.STE.B3.SymCalcStep5.conjLapPow (j + 1) T T' h)) k :=
          funext fun k => Work.Diff.STE.B3.SymCalcStep1.fourierCoeff_add_of_continuous _ _
            hAsm.continuous hBsm.continuous k
        rw [hfc]
        have hAsum : Summable (fun k : ι → ℤ => (Work.Diff.STE.wt k) ^ s'
            * ‖Work.Diff.STE.fourierCoeff
                (Work.Diff.STE.B3.SymCalcStep5.conjLapPow 1 T T' (W ρ T T' (j + 1) ε h)) k‖ ^ 2) :=
          Work.Diff.STE.B3.SymCalcStep1.summable_CSq_fourierCoeff s' hAsm
            (conjLapPow_periodic T T' hTper 1 _)
        have hBsum : Summable (fun k : ι → ℤ => (Work.Diff.STE.wt k) ^ s'
            * ‖Work.Diff.STE.fourierCoeff
                (W ρ T T' 1 ε
                  (Work.Diff.STE.B3.SymCalcStep5.conjLapPow (j + 1) T T' h)) k‖ ^ 2) :=
          Work.Diff.STE.B3.SymCalcStep1.summable_CSq_fourierCoeff s' hBsm
            (W_periodic ρ T T' hTper 1 ε _)
        have e1 : (s' + 2) + 2 * (j + 1) - 1 = s' + 2 * (j + 1 + 1) - 1 := by omega
        have e2 : (s' + 1) + 2 * (j + 1) = s' + 2 * (j + 1 + 1) - 1 := by omega
        calc Work.Diff.STE.CSq s' (fun k => Work.Diff.STE.fourierCoeff
                (Work.Diff.STE.B3.SymCalcStep5.conjLapPow 1 T T'
                  (W ρ T T' (j + 1) ε h)) k
              + Work.Diff.STE.fourierCoeff
                (W ρ T T' 1 ε
                  (Work.Diff.STE.B3.SymCalcStep5.conjLapPow (j + 1) T T' h)) k)
            ≤ 2 * (Work.Diff.STE.CSq s' (Work.Diff.STE.fourierCoeff
                  (Work.Diff.STE.B3.SymCalcStep5.conjLapPow 1 T T'
                    (W ρ T T' (j + 1) ε h)))
                + Work.Diff.STE.CSq s' (Work.Diff.STE.fourierCoeff
                  (W ρ T T' 1 ε
                    (Work.Diff.STE.B3.SymCalcStep5.conjLapPow (j + 1) T T' h)))) :=
              Work.Diff.STE.B3.SymCalcStep1.CSq_add_le s' _ _ hAsum hBsum
          _ ≤ 2 * (K1 * Work.Diff.STE.CSq (s' + 2) (Work.Diff.STE.fourierCoeff
                  (W ρ T T' (j + 1) ε h))
                + Cb * Work.Diff.STE.CSq (s' + 1) (Work.Diff.STE.fourierCoeff
                  (Work.Diff.STE.B3.SymCalcStep5.conjLapPow (j + 1) T T' h))) := by
              refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) (by norm_num)
              · exact hK1b _ hWsm hWp
              · exact hCbb ε hε hε1 _ hCLsm hCLp
          _ ≤ 2 * (K1 * (C1 * Work.Diff.STE.CSq ((s' + 2) + 2 * (j + 1) - 1)
                  (Work.Diff.STE.fourierCoeff h))
                + Cb * (Kn * Work.Diff.STE.CSq ((s' + 1) + 2 * (j + 1))
                  (Work.Diff.STE.fourierCoeff h))) := by
              refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) (by norm_num)
              · exact mul_le_mul_of_nonneg_left (hC1b ε hε hε1 h hh hhp) hK1
              · exact mul_le_mul_of_nonneg_left (hKnb h hh hhp) hCb
          _ = (2 * (K1 * C1 + Cb * Kn))
                * Work.Diff.STE.CSq (s' + 2 * (j + 1 + 1) - 1)
                    (Work.Diff.STE.fourierCoeff h) := by
              rw [e1, e2]
              ring
  obtain ⟨C, hC, hCb⟩ := keyY (k - 1) s
  refine ⟨C, hC, fun ε hε hε1 h hh hhp => ?_⟩
  have hkey := hCb ε hε hε1 h hh hhp
  rwa [show k - 1 + 1 = k from Nat.sub_add_cancel hk] at hkey

/-! ## The target -/

theorem conj_cut_comm_lapPow_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ : (ι → ℝ) → ℝ)
    (hρb : ∀ y : ι → ℝ, ‖ρ y‖ ≤ 1)
    (hdiam : ∀ y : ι → ℝ, 2 < ∑ i, (y i) ^ 2 → ρ y = 0)
    (hρ0 : ρ 0 = 1)
    (L : ℝ) (hL : 0 ≤ L) (hρlip : ∀ y z : ι → ℝ, ‖ρ y - ρ z‖ ≤ L * ‖y - z‖)
    (T T' : (ι → ℝ) → (ι → ℝ))
    (hTsm : ContDiff ℝ (⊤ : ℕ∞) T) (hTsm' : ContDiff ℝ (⊤ : ℕ∞) T')
    (hTinv1 : ∀ x : ι → ℝ, T' (T x) = x)
    (hTinv2 : ∀ y : ι → ℝ, T (T' y) = y)
    (hTper : ∀ (i : ι) (x : ι → ℝ), T (x + Pi.single i 1) = T x + Pi.single i 1)
    (k : ℕ) (hk : 1 ≤ k) (s : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (ε : ℝ), 0 < ε → ε ≤ 1 → ∀ g : (ι → ℝ) → ℂ,
        ContDiff ℝ (⊤ : ℕ∞) g → Work.Diff.STE.Periodic1 g →
        Summable (fun m : ι → ℤ =>
            (Work.Diff.STE.wt m) ^ (s + 2 * k - 1) * ‖Work.Diff.STE.fourierCoeff g m‖ ^ 2) →
        Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff (fun x =>
            Work.Diff.STE.B3.SymCalcStep5.lapPow k
                (Work.Diff.STE.B3.SymCalc.conjCut ρ ε T T' g) x
              - Work.Diff.STE.B3.SymCalc.conjCut ρ ε T T'
                  (Work.Diff.STE.B3.SymCalcStep5.lapPow k g) x))
          ≤ C * Work.Diff.STE.CSq (s + 2 * k - 1) (Work.Diff.STE.fourierCoeff g) := by
  classical
  obtain ⟨C, hC, hCb⟩ := W_bound ρ hρb hdiam L hL hρlip T T' hTsm hTsm' hTper hTinv1 hTinv2 k hk s
  have hinjT : Function.Injective T := fun x y hxy => by rw [← hTinv1 x, hxy, hTinv1 y]
  have hinjT' : Function.Injective T' := fun x y hxy => by rw [← hTinv2 x, hxy, hTinv2 y]
  have hdet_of : ∀ (A B : (ι → ℝ) →L[ℝ] (ι → ℝ)), A.comp B = 1 → B.det ≠ 0 := by
    intro A B hcomp hz
    have hinj : Function.Injective B := fun u v huv => by
      have h1 := congrArg (fun (L : (ι → ℝ) →L[ℝ] (ι → ℝ)) => L u) hcomp
      have h2 := congrArg (fun (L : (ι → ℝ) →L[ℝ] (ι → ℝ)) => L v) hcomp
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.one_apply] at h1 h2
      rw [huv] at h1
      exact h1.symm.trans h2
    have hz' : LinearMap.det ((B : (ι → ℝ) →ₗ[ℝ] (ι → ℝ))) = 0 := hz
    exact (LinearMap.det_eq_zero_iff_ker_ne_bot.mp hz') (by rw [LinearMap.ker_eq_bot]; exact hinj)
  have hdetT : ∀ z : ι → ℝ, (fderiv ℝ T z).det ≠ 0 := by
    intro z
    have hcomp : fderiv ℝ (fun x => T' (T x)) z
        = (fderiv ℝ T' (T z)).comp (fderiv ℝ T z) :=
      fderiv_comp z ((hTsm'.differentiable (by simp)).differentiableAt)
        ((hTsm.differentiable (by simp)).differentiableAt)
    have h1 : fderiv ℝ (fun x => T' (T x)) z = 1 := by
      rw [show (fun x : ι → ℝ => T' (T x)) = id from funext hTinv1]
      exact fderiv_id
    have h2 : (fderiv ℝ T' (T z)).comp (fderiv ℝ T z) = 1 := by rw [← hcomp]; exact h1
    exact hdet_of _ _ h2
  have hdetT' : ∀ z : ι → ℝ, (fderiv ℝ T' z).det ≠ 0 := by
    intro z
    have hcomp : fderiv ℝ (fun y => T (T' y)) z
        = (fderiv ℝ T (T' z)).comp (fderiv ℝ T' z) :=
      fderiv_comp z ((hTsm.differentiable (by simp)).differentiableAt)
        ((hTsm'.differentiable (by simp)).differentiableAt)
    have h1 : fderiv ℝ (fun y => T (T' y)) z = 1 := by
      rw [show (fun y : ι → ℝ => T (T' y)) = id from funext hTinv2]
      exact fderiv_id
    have h2 : (fderiv ℝ T (T' z)).comp (fderiv ℝ T' z) = 1 := by rw [← hcomp]; exact h1
    exact hdet_of _ _ h2
  have hshift : ∀ (i : ι) (z : ι → ℝ), T' (z + Pi.single i 1) = T' z + Pi.single i 1 :=
    fun i => Work.Diff.STE.B3.SymCalcStep1.shift_T' T T' hTper hTinv1 hTinv2 i
  obtain ⟨KA, hKA, hKAle⟩ :=
    Work.Diff.STE.B3.SymCalcStep1.fourierCoeff_comp_le s T' hTsm' hshift hinjT' hdetT'
  obtain ⟨KB, hKB, hKBle⟩ :=
    Work.Diff.STE.B3.SymCalcStep1.fourierCoeff_comp_le (s + 2 * k - 1) T hTsm hTper hinjT hdetT
  refine ⟨KA * C * KB, by positivity, fun ε hε hε1 g hg hgp _ => ?_⟩
  have hh : ContDiff ℝ (⊤ : ℕ∞) (Work.Diff.STE.B3.SymCalc.compMap T g) := hg.comp hTsm
  have hhp : Work.Diff.STE.Periodic1 (Work.Diff.STE.B3.SymCalc.compMap T g) := by
    intro i x
    show g (T (x + Pi.single i 1)) = g (T x)
    rw [hTper i x]
    exact hgp i (T x)
  have hid := Work.Diff.STE.B3.SymCalcStep5.conjCut_lapPow_comm ρ ε k T T' hTinv1 hTinv2 g
  have hWsm : ContDiff ℝ (⊤ : ℕ∞)
      (W ρ T T' k ε (Work.Diff.STE.B3.SymCalc.compMap T g)) :=
    W_contDiff ρ hρb T T' hTsm hTsm' hTper hTinv1 hTinv2 k ε hh hhp
  have hWp : Work.Diff.STE.Periodic1 (W ρ T T' k ε (Work.Diff.STE.B3.SymCalc.compMap T g)) :=
    W_periodic ρ T T' hTper k ε _
  have hkey := hCb ε hε hε1 (Work.Diff.STE.B3.SymCalc.compMap T g) hh hhp
  calc Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff (fun x =>
        Work.Diff.STE.B3.SymCalcStep5.lapPow k
            (Work.Diff.STE.B3.SymCalc.conjCut ρ ε T T' g) x
          - Work.Diff.STE.B3.SymCalc.conjCut ρ ε T T'
              (Work.Diff.STE.B3.SymCalcStep5.lapPow k g) x))
      = Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff (Work.Diff.STE.B3.SymCalc.compMap T'
          (W ρ T T' k ε (Work.Diff.STE.B3.SymCalc.compMap T g)))) := by
        change Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff
            (Work.Diff.STE.B3.SymCalcStep5.lapPow k (Work.Diff.STE.B3.SymCalc.conjCut ρ ε T T' g)
              - Work.Diff.STE.B3.SymCalc.conjCut ρ ε T T'
                  (Work.Diff.STE.B3.SymCalcStep5.lapPow k g))) = _
        rw [hid]
        simp only [W]
    _ ≤ KA * Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff
          (W ρ T T' k ε (Work.Diff.STE.B3.SymCalc.compMap T g))) :=
        hKAle _ hWsm hWp
    _ ≤ KA * (C * Work.Diff.STE.CSq (s + 2 * k - 1) (Work.Diff.STE.fourierCoeff
          (Work.Diff.STE.B3.SymCalc.compMap T g))) :=
        mul_le_mul_of_nonneg_left hkey hKA
    _ ≤ KA * (C * (KB * Work.Diff.STE.CSq (s + 2 * k - 1)
          (Work.Diff.STE.fourierCoeff g))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hKBle g hg hgp) hC) hKA
    _ = (KA * C * KB) * Work.Diff.STE.CSq (s + 2 * k - 1) (Work.Diff.STE.fourierCoeff g) := by
        ring

end Work.Diff.STE.B3.SymCalcStep6
