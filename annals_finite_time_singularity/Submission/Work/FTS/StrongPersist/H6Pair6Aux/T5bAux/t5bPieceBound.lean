import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T5bAux.t5bPiecePtwAux
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T5bAux.t5bPiecePtwIntegrable
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T5bPrep
import Submission.Work.FTS.StrongPersist.SP6.EUz6
import Submission.Work.FTS.StrongPersist.SP6.Flat6Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Pair6Aux.T5bAux

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-!
# The pointwise (single-summand) bound for the row `T5bRow`

The row `T5bRow` expands the pairing `∫∫ ρ·(D_z^bD_θ^a u)·(D_z^bD_θ^af)` of the product
`u = c₂ₘ(θ)·L₁₂(f)(z)·D_zf` by the two Leibniz rules (radial in `D_z`, angular in `D_θ`):

`D_z^bD_θ^a u = Σ_{k ≤ b}Σ_{i ≤ a} C(b,k)C(a,i)·D_z^k(L₁₂f)·D_θ^i(c₂ₘ)·D_z^{b-k+1}D_θ^{a-i}f`,

whose `(k,i)`-summand is exactly `t5bPiece f ρ a b k i`.  This file proves the estimate for one
summand.  The coefficient bounds `|D_z^k(L₁₂f)| ≤ C₄|f|_{ℋ⁴}` (`k ≤ 4`) resp. `≤ C₆|f|_{ℋ⁶}`
(`k ≥ 5`) and `|D_θ^i(c₂ₘ)| ≤ Cc·sin(2θ)` (`i ≥ 1`), `|c₂ₘ| ≤ Cc` (`i = 0`) are separated from
the two remaining slots, which are estimated by the two-level weighted Cauchy–Schwarz
`slotCrossLeGen`.  The two branches of the statement's constant correspond to the two possible
levels of the slot `D_z^{b-k+1}D_θ^{a-i}f`: level six (for `k ≤ 4`, where only `|f|_{ℋ⁶}` is
used) resp. level four (for `k ≥ 5`, where the order of that slot drops to `a+b-k-i+1 ≤ 2`).
The binomial coefficient of the statement is a slack: it is `≥ 1`, so the single-summand
estimate suffices.

The elementary ingredients (continuity and vanishing at `z = 0` of the leaf weights, and the
two arithmetic reductions) are in `T5bAux/t5bPieceAux.lean`; the pointwise bounds of the two
cases `i = 0` and `i ≥ 1` are in `T5bAux/t5bPiecePtw.lean`.
-/

theorem t5bPieceBound {α : ℝ} {f : ℝ → ℝ → ℝ} {a b : ℕ} {ρ : ℝ → ℝ → ℝ}
    {C4 C6 Cc : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hso : Work.FTS.EllipticEst.SmoothOpen f)
    (hm6 : Work.Spaces.HkMem α 6 f)
    (hab : a + b ≤ 6) (hleaf : Work.FTS.TransportS.IsLeafW α a ρ)
    (hC4 : 0 ≤ C4) (hC6 : 0 ≤ C6) (hCc : 0 ≤ Cc)
    (hsup4 : ∀ k : ℕ, k ≤ 4 → ∀ z : ℝ, 0 < z →
      |Work.Elliptic.DzdIter k (fun z => Work.Construction.L12 f z) z|
        ≤ C4 * Work.Spaces.HkNorm α 4 f)
    (hsup6 : ∀ k : ℕ, k ≤ 6 → ∀ z : ℝ, 0 < z →
      |Work.Elliptic.DzdIter k (fun z => Work.Construction.L12 f z) z|
        ≤ C6 * Work.Spaces.HkNorm α 6 f)
    (hCcbd : ∀ θ ∈ Work.Spaces.Iθ, |Work.Construction.c2m θ| ≤ Cc)
    (hCcg : ∀ i : ℕ, 1 ≤ i → i ≤ 8 → ∀ (z θ : ℝ), θ ∈ Work.Spaces.Iθ →
      |Work.Spaces.DthIter i (fun _ θ : ℝ => Work.Construction.c2m θ) z θ|
        ≤ Cc * Real.sin (2 * θ))
    {k i : ℕ} (hk : k ≤ b) (hi : i ≤ a) (hne : ¬ (k = 0 ∧ i = 0)) :
    |∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        Work.FTS.StrongPersist.H6Pair6Aux.t5bPiece f ρ a b k i (z, θ)|
      ≤ ((b.choose k : ℝ) * (a.choose i : ℝ)) * Cc *
          (if k ≤ 4
           then C4 * Work.Spaces.HkNorm α 4 f
                * (Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 6 f
                   + Work.Spaces.HkNorm α 6 f * Work.Spaces.HkNorm α 6 f)
           else C6 * Work.Spaces.HkNorm α 6 f
                * (Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 6 f)) := by
  have hb6 : b ≤ 6 := by omega
  have hN4 : 0 ≤ Work.Spaces.HkNorm α 4 f := Work.Spaces.HkNorm_nonneg α 4 f
  have hN6 : 0 ≤ Work.Spaces.HkNorm α 6 f := Work.Spaces.HkNorm_nonneg α 6 f
  have hb1 : (1 : ℝ) ≤ (b.choose k : ℝ) := by exact_mod_cast Nat.choose_pos hk
  by_cases hi0 : i = 0
  · -- ## the case `i = 0`: the weight is the leaf weight `ρ`
    subst hi0
    have hk1 : 1 ≤ k := by
      rcases Nat.eq_zero_or_pos k with h0 | hpos
      · exfalso; exact hne ⟨h0, rfl⟩
      · exact hpos
    have ha1 : (1 : ℝ) ≤ (a.choose 0 : ℝ) := by
      exact_mod_cast Nat.choose_pos (Nat.zero_le a)
    have hbin : (1 : ℝ) ≤ (b.choose k : ℝ) * (a.choose 0 : ℝ) := by
      nlinarith [hb1, ha1]
    have hXc : ContinuousOn
        (Function.uncurry (fun z θ => Work.Spaces.mixed (b - k + 1) a f z θ))
        Work.FTS.EllipticEst.Q0 := (hso.mixed (b - k + 1) a).continuousOn
    have hYc : ContinuousOn (Function.uncurry (fun z θ => Work.Spaces.mixed b a f z θ))
        Work.FTS.EllipticEst.Q0 := (hso.mixed b a).continuousOn
    have hWc : ContinuousOn (Function.uncurry ρ) Work.FTS.EllipticEst.Q0 :=
      contOn_leafW hleaf
    have hWnn : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2), 0 ≤ ρ z θ :=
      fun z _ θ hθ => Work.FTS.StrongPersist.H6Pair6Aux.leaf_nonneg hleaf z
        ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
    by_cases hk4 : k ≤ 4
    · -- ### `i = 0`, `k ≤ 4`
      have hordX : a + (b - k + 1) ≤ 6 := by omega
      have hdomX : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
          ρ z θ * (Work.Spaces.mixed (b - k + 1) a f z θ) ^ 2
            ≤ Work.Spaces.HkIntegrand α 6 f z θ :=
        fun z _ θ hθ => Work.FTS.StrongPersist.H6Pair6Aux.domLeaf_all
          (f := f) (b' := b - k + 1) (n := 6) hα hleaf hθ hordX
      have hdomY : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
          ρ z θ * (Work.Spaces.mixed b a f z θ) ^ 2
            ≤ Work.Spaces.HkIntegrand α 6 f z θ :=
        fun z _ θ hθ => Work.FTS.StrongPersist.H6Pair6Aux.domLeaf_all
          (f := f) (b' := b) (n := 6) hα hleaf hθ hab
      have hP : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
          |Work.FTS.StrongPersist.H6Pair6Aux.t5bPiece f ρ a b k 0 (z, θ)|
            ≤ (Cc * (C4 * Work.Spaces.HkNorm α 4 f))
              * (ρ z θ * |Work.Spaces.mixed (b - k + 1) a f z θ|
                  * |Work.Spaces.mixed b a f z θ|) := by
        intro z hz θ hθ
        rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
        · rw [← hz0, piece_at_zero hleaf θ, leaf_zero_left hleaf θ]
          simp
        · have h := piece_abs_le_zero (f := f) (ρ := ρ) (a := a) (b := b) (k := k)
            hC4 hC6 hCc hsup4 hsup6 hCcbd hk hb6 hleaf hzpos hθ
          rw [if_pos hk4] at h
          exact h
      have hres := slotCrossLeGen (f := f)
        (X := fun z θ => Work.Spaces.mixed (b - k + 1) a f z θ)
        (Y := fun z θ => Work.Spaces.mixed b a f z θ)
        (W := fun z θ => ρ z θ)
        (P := fun z θ => Work.FTS.StrongPersist.H6Pair6Aux.t5bPiece f ρ a b k 0 (z, θ))
        (p := 6) (n := 6) (C := Cc * (C4 * Work.Spaces.HkNorm α 4 f))
        (hC := mul_nonneg hCc (mul_nonneg hC4 hN4)) (hp := hm6) (hn := hm6)
        (hXc := hXc) (hYc := hYc) (hWc := hWc) (hWnn := hWnn)
        (hdomX := hdomX) (hdomY := hdomY) (hP := hP)
      rw [if_pos hk4]
      exact arith_four hCc hC4 hN4 hN6 hbin hres
    · -- ### `i = 0`, `k ≥ 5`
      have hk5 : 5 ≤ k := by omega
      have hmem4 : Work.Spaces.HkMem α 4 f :=
        Work.FTS.StrongPersist.H6Pair6Aux.HkMem_of_le (show (4 : ℕ) ≤ 6 by norm_num) hso hm6
      have hordX : a + (b - k + 1) ≤ 4 := by omega
      have hdomX : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
          ρ z θ * (Work.Spaces.mixed (b - k + 1) a f z θ) ^ 2
            ≤ Work.Spaces.HkIntegrand α 4 f z θ :=
        fun z _ θ hθ => Work.FTS.StrongPersist.H6Pair6Aux.domLeaf_all
          (f := f) (b' := b - k + 1) (n := 4) hα hleaf hθ hordX
      have hdomY : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
          ρ z θ * (Work.Spaces.mixed b a f z θ) ^ 2
            ≤ Work.Spaces.HkIntegrand α 6 f z θ :=
        fun z _ θ hθ => Work.FTS.StrongPersist.H6Pair6Aux.domLeaf_all
          (f := f) (b' := b) (n := 6) hα hleaf hθ hab
      have hP : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
          |Work.FTS.StrongPersist.H6Pair6Aux.t5bPiece f ρ a b k 0 (z, θ)|
            ≤ (Cc * (C6 * Work.Spaces.HkNorm α 6 f))
              * (ρ z θ * |Work.Spaces.mixed (b - k + 1) a f z θ|
                  * |Work.Spaces.mixed b a f z θ|) := by
        intro z hz θ hθ
        rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
        · rw [← hz0, piece_at_zero hleaf θ, leaf_zero_left hleaf θ]
          simp
        · have h := piece_abs_le_zero (f := f) (ρ := ρ) (a := a) (b := b) (k := k)
            hC4 hC6 hCc hsup4 hsup6 hCcbd hk hb6 hleaf hzpos hθ
          rw [if_neg hk4] at h
          exact h
      have hres := slotCrossLeGen (f := f)
        (X := fun z θ => Work.Spaces.mixed (b - k + 1) a f z θ)
        (Y := fun z θ => Work.Spaces.mixed b a f z θ)
        (W := fun z θ => ρ z θ)
        (P := fun z θ => Work.FTS.StrongPersist.H6Pair6Aux.t5bPiece f ρ a b k 0 (z, θ))
        (p := 4) (n := 6) (C := Cc * (C6 * Work.Spaces.HkNorm α 6 f))
        (hC := mul_nonneg hCc (mul_nonneg hC6 hN6)) (hp := hmem4) (hn := hm6)
        (hXc := hXc) (hYc := hYc) (hWc := hWc) (hWnn := hWnn)
        (hdomX := hdomX) (hdomY := hdomY) (hP := hP)
      rw [if_neg hk4]
      exact arith_six hCc hC6 hN4 hN6 hbin hres
  · -- ## the case `i ≥ 1`: the weight is `w²·sin(2θ)^{-(γ-1)}`
    have hi1 : 1 ≤ i := Nat.one_le_iff_ne_zero.mpr hi0
    have hi8 : i ≤ 8 := by omega
    have ha1 : (1 : ℝ) ≤ (a.choose i : ℝ) := by exact_mod_cast Nat.choose_pos hi
    have hbin : (1 : ℝ) ≤ (b.choose k : ℝ) * (a.choose i : ℝ) := by
      nlinarith [hb1, ha1]
    have hXc : ContinuousOn
        (Function.uncurry (fun z θ => Work.Spaces.mixed (b - k + 1) (a - i) f z θ))
        Work.FTS.EllipticEst.Q0 := (hso.mixed (b - k + 1) (a - i)).continuousOn
    have hYc : ContinuousOn (Function.uncurry (fun z θ => Work.Spaces.mixed b a f z θ))
        Work.FTS.EllipticEst.Q0 := (hso.mixed b a).continuousOn
    have hWc : ContinuousOn
        (Function.uncurry (fun z θ =>
          (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α - 1))))
        Work.FTS.EllipticEst.Q0 := contOn_Wgam α
    have hWnn : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
        0 ≤ (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α - 1)) := by
      intro z _ θ hθ
      exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (le_of_lt
        (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
          (by linarith [hθ.2, Real.pi_pos]))) _)
    by_cases hk4 : k ≤ 4
    · -- ### `i ≥ 1`, `k ≤ 4`
      have hordX : (a - i) + (b - k + 1) ≤ 6 := by omega
      have hdomX : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
          (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α - 1))
            * (Work.Spaces.mixed (b - k + 1) (a - i) f z θ) ^ 2
            ≤ Work.Spaces.HkIntegrand α 6 f z θ :=
        fun z _ θ hθ => Work.FTS.StrongPersist.H6Pair6Aux.domGm1
          (f := f) (a' := a - i) (b' := b - k + 1) (n := 6) hα hα1 hθ hordX
      have hdomY : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
          (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α - 1))
            * (Work.Spaces.mixed b a f z θ) ^ 2
            ≤ Work.Spaces.HkIntegrand α 6 f z θ :=
        fun z _ θ hθ => Work.FTS.StrongPersist.H6Pair6Aux.domGm1
          (f := f) (a' := a) (b' := b) (n := 6) hα hα1 hθ hab
      have hP : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
          |Work.FTS.StrongPersist.H6Pair6Aux.t5bPiece f ρ a b k i (z, θ)|
            ≤ (Cc * (C4 * Work.Spaces.HkNorm α 4 f))
              * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α - 1))
                  * |Work.Spaces.mixed (b - k + 1) (a - i) f z θ|
                  * |Work.Spaces.mixed b a f z θ|) := by
        intro z hz θ hθ
        rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
        · rw [← hz0, piece_at_zero hleaf θ]
          have hw0 : (Work.Spaces.w 0) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α - 1)) = 0 := by
            rw [show Work.Spaces.w 0 = 0 by simp [Work.Spaces.w]]; simp
          rw [hw0]; simp
        · have h := piece_abs_le_pos (f := f) (ρ := ρ) (a := a) (b := b) (k := k) (i := i)
            hα hα1 hC4 hC6 hCc hsup4 hsup6 hCcg hk hb6 hleaf hi1 hi8 hzpos hθ
          rw [if_pos hk4] at h
          exact h
      have hres := slotCrossLeGen (f := f)
        (X := fun z θ => Work.Spaces.mixed (b - k + 1) (a - i) f z θ)
        (Y := fun z θ => Work.Spaces.mixed b a f z θ)
        (W := fun z θ => (Work.Spaces.w z) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α - 1)))
        (P := fun z θ => Work.FTS.StrongPersist.H6Pair6Aux.t5bPiece f ρ a b k i (z, θ))
        (p := 6) (n := 6) (C := Cc * (C4 * Work.Spaces.HkNorm α 4 f))
        (hC := mul_nonneg hCc (mul_nonneg hC4 hN4)) (hp := hm6) (hn := hm6)
        (hXc := hXc) (hYc := hYc) (hWc := hWc) (hWnn := hWnn)
        (hdomX := hdomX) (hdomY := hdomY) (hP := hP)
      rw [if_pos hk4]
      exact arith_four hCc hC4 hN4 hN6 hbin hres
    · -- ### `i ≥ 1`, `k ≥ 5`
      have hk5 : 5 ≤ k := by omega
      have hmem4 : Work.Spaces.HkMem α 4 f :=
        Work.FTS.StrongPersist.H6Pair6Aux.HkMem_of_le (show (4 : ℕ) ≤ 6 by norm_num) hso hm6
      have hordX : (a - i) + (b - k + 1) ≤ 4 := by omega
      have hdomX : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
          (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α - 1))
            * (Work.Spaces.mixed (b - k + 1) (a - i) f z θ) ^ 2
            ≤ Work.Spaces.HkIntegrand α 4 f z θ :=
        fun z _ θ hθ => Work.FTS.StrongPersist.H6Pair6Aux.domGm1
          (f := f) (a' := a - i) (b' := b - k + 1) (n := 4) hα hα1 hθ hordX
      have hdomY : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
          (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α - 1))
            * (Work.Spaces.mixed b a f z θ) ^ 2
            ≤ Work.Spaces.HkIntegrand α 6 f z θ :=
        fun z _ θ hθ => Work.FTS.StrongPersist.H6Pair6Aux.domGm1
          (f := f) (a' := a) (b' := b) (n := 6) hα hα1 hθ hab
      have hP : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
          |Work.FTS.StrongPersist.H6Pair6Aux.t5bPiece f ρ a b k i (z, θ)|
            ≤ (Cc * (C6 * Work.Spaces.HkNorm α 6 f))
              * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α - 1))
                  * |Work.Spaces.mixed (b - k + 1) (a - i) f z θ|
                  * |Work.Spaces.mixed b a f z θ|) := by
        intro z hz θ hθ
        rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
        · rw [← hz0, piece_at_zero hleaf θ]
          have hw0 : (Work.Spaces.w 0) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α - 1)) = 0 := by
            rw [show Work.Spaces.w 0 = 0 by simp [Work.Spaces.w]]; simp
          rw [hw0]; simp
        · have h := piece_abs_le_pos (f := f) (ρ := ρ) (a := a) (b := b) (k := k) (i := i)
            hα hα1 hC4 hC6 hCc hsup4 hsup6 hCcg hk hb6 hleaf hi1 hi8 hzpos hθ
          rw [if_neg hk4] at h
          exact h
      have hres := slotCrossLeGen (f := f)
        (X := fun z θ => Work.Spaces.mixed (b - k + 1) (a - i) f z θ)
        (Y := fun z θ => Work.Spaces.mixed b a f z θ)
        (W := fun z θ => (Work.Spaces.w z) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α - 1)))
        (P := fun z θ => Work.FTS.StrongPersist.H6Pair6Aux.t5bPiece f ρ a b k i (z, θ))
        (p := 4) (n := 6) (C := Cc * (C6 * Work.Spaces.HkNorm α 6 f))
        (hC := mul_nonneg hCc (mul_nonneg hC6 hN6)) (hp := hmem4) (hn := hm6)
        (hXc := hXc) (hYc := hYc) (hWc := hWc) (hWnn := hWnn)
        (hdomX := hdomX) (hdomY := hdomY) (hP := hP)
      rw [if_neg hk4]
      exact arith_six hCc hC6 hN4 hN6 hbin hres


end Work.FTS.StrongPersist.H6Pair6Aux.T5bAux
