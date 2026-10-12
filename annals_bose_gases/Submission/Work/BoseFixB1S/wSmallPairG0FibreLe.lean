import ChallengeDeps
import Mathlib.Tactic.Have
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Submission.Work.BoseFixB1.KernelFacts
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1S.wSmallPairG0FibreLe`

The **fibre bound for the localised two-body kernel at the numerator `g₀`**, with the
*first* kernel slot integrated and the second slot held fixed: for every `(u,a)` and every
measurable `A ⊆ acube ℓ`,

    ∫_{y ∈ A} |wSmallPair M ℓ d u (g₀ v h) y a| dy ≤ C · (a v)

with `C = C(M)` uniform in `v`, `R`, `ℓ`, `d`, `u`, `a` (and in `A`).

Proof.  `abs_wSmallPair_le` (BoseFixB1) dominates the kernel pointwise by

    (chiSupAbs · χ_M(((ℓd)⁻¹a − u))) · ((2/smallConvLower M)·(chiSupAbs · chiSmallDecay M)·|g₀(a−y)|),

after the symmetry `wSmallPair_symm` (with `g₀` even, `g0_even`) moves `y` into the second
slot.  The *sharp* sup bound `|χ_M| ≤ chiSmallNormFactor M` makes the first factor
`a`-independent, and `∫|g₀| = 8π·(a v)` (`g0_abs_integral`) closes the estimate.

At `M = 0` the bump degenerates (`χ_0 = 1/√∫1 = 0`), the kernel vanishes identically and
`C = 0` works.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseFixB1S

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## Two elementary facts about the bump -/

/-- **Sharp sup bound for the `ℓd`-scale bump**: `|χ_M(w)| ≤ chiSmallNormFactor M`.
(`χ_M = (ζζζ)^M/√∫(ζζζ)^{2M}` and `ζζζ ∈ [0,1]`.) -/
lemma abs_chiSmall_le_normFactor {M : ℕ} (hM : 1 ≤ M) (w : ℝ³) :
    |Submission.BoseGases.chiSmall M w| ≤ Submission.BoseGases.chiSmallNormFactor M := by
  rw [Submission.BoseGases.chiSmall_abs_eq hM w]
  have h1 : |Submission.BoseGases.chiSmallBase M w| ≤ (1 : ℝ) := by
    have h0 : 0 ≤ Submission.BoseGases.zeta1d (w.ofLp 0) := Submission.BoseGases.zeta1d_nonneg _
    have h1' : 0 ≤ Submission.BoseGases.zeta1d (w.ofLp 1) := Submission.BoseGases.zeta1d_nonneg _
    have h2 : 0 ≤ Submission.BoseGases.zeta1d (w.ofLp 2) := Submission.BoseGases.zeta1d_nonneg _
    have hp0 : Submission.BoseGases.zeta1d (w.ofLp 0) ≤ 1 := Submission.BoseGases.zeta1d_le_one _
    have hp1 : Submission.BoseGases.zeta1d (w.ofLp 1) ≤ 1 := Submission.BoseGases.zeta1d_le_one _
    have hp2 : Submission.BoseGases.zeta1d (w.ofLp 2) ≤ 1 := Submission.BoseGases.zeta1d_le_one _
    have hprod0 : 0 ≤ Submission.BoseGases.zeta1d (w.ofLp 0)
        * Submission.BoseGases.zeta1d (w.ofLp 1) * Submission.BoseGases.zeta1d (w.ofLp 2) :=
      mul_nonneg (mul_nonneg h0 h1') h2
    have hprod1 : Submission.BoseGases.zeta1d (w.ofLp 0)
        * Submission.BoseGases.zeta1d (w.ofLp 1) * Submission.BoseGases.zeta1d (w.ofLp 2) ≤ 1 := by
      have h01 : Submission.BoseGases.zeta1d (w.ofLp 0)
          * Submission.BoseGases.zeta1d (w.ofLp 1) ≤ 1 := by nlinarith
      nlinarith
    have hpow : (Submission.BoseGases.zeta1d (w.ofLp 0)
        * Submission.BoseGases.zeta1d (w.ofLp 1) * Submission.BoseGases.zeta1d (w.ofLp 2)) ^ M ≤ 1 :=
      pow_le_one₀ hprod0 hprod1
    rw [Submission.BoseGases.chiSmallBase, abs_of_nonneg (pow_nonneg hprod0 M)]
    exact hpow
  calc |Submission.BoseGases.chiSmallBase M w| * Submission.BoseGases.chiSmallNormFactor M
      ≤ 1 * Submission.BoseGases.chiSmallNormFactor M :=
        mul_le_mul_of_nonneg_right h1 (Submission.BoseGases.chiSmallNormFactor_nonneg M)
    _ = Submission.BoseGases.chiSmallNormFactor M := one_mul _

/-- **The bump degenerates at `M = 0`**: `χ_0 = (ζζζ)^0/√∫(ζζζ)^0 = 1/√∫1 = 1/0 = 0`. -/
lemma chiSmall_zero_of_M_zero (z : ℝ³) : Submission.BoseGases.chiSmall 0 z = 0 := by
  have h : Submission.BoseGases.chiSmallNormSq 0 = 0 := by
    have hbase : ∀ z : ℝ³, Submission.BoseGases.chiSmallBase 0 z = 1 := by
      intro z
      simp [Submission.BoseGases.chiSmallBase]
    dsimp only [Submission.BoseGases.chiSmallNormSq]
    simp only [hbase, one_pow, MeasureTheory.integral_const]
    rw [MeasureTheory.Measure.real, show (volume : Measure ℝ³) Set.univ = ⊤ by simp]
    simp
  simp [Submission.BoseGases.chiSmall, h]

/-- **The localised kernel vanishes at `M = 0`** (both cutoff factors carry `χ_0 = 0`). -/
lemma wSmallPair_zero_of_M_zero {ℓ d : ℝ} (u : ℝ³) (f : ℝ³ → ℝ) (x y : ℝ³) :
    Submission.BoseGases.wSmallPair 0 ℓ d u f x y = 0 := by
  have hx : Submission.BoseGases.chiSmallB 0 ℓ d u x = 0 := by
    rw [Submission.BoseGases.chiSmallB, chiSmall_zero_of_M_zero, mul_zero]
  have hy : Submission.BoseGases.chiSmallB 0 ℓ d u y = 0 := by
    rw [Submission.BoseGases.chiSmallB, chiSmall_zero_of_M_zero, mul_zero]
  rw [Submission.BoseGases.wSmallPair, hx, hy]
  ring

/-! ## The fibre bound -/

theorem wSmallPairG0FibreLe (M : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R ℓ d : ℝ}, 0 < R → 0 < ℓ → 0 < d →
        0 ≤ v → _root_.BoseGases.IsRadial v →
        tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R →
        (h : ∃ w : EuclideanSpace ℝ (Fin 3) → ℝ,
              _root_.BoseGases.IsRadial w ∧ _root_.BoseGases.IsScatteringSolution w v) →
        R ≤ ℓ * d / 16 → R ≤ ℓ * Submission.BoseGases.chiR0 →
        ∀ (A : Set (EuclideanSpace ℝ (Fin 3))), MeasurableSet A →
          A ⊆ Submission.BoseGases.acube ℓ →
        ∀ (u a : EuclideanSpace ℝ (Fin 3)),
          ∫ y in A, |Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g0 v h) y a|
            ≤ C * _root_.BoseGases.a v := by
  by_cases hM : 1 ≤ M
  · -- the genuine case `M ≥ 1`
    refine ⟨(Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallNormFactor M) *
        ((2 / Work.SmallBoxSliding.smallConvLower M) *
          (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M)) * (8 * π), ?_, ?_⟩
    · exact mul_nonneg (mul_nonneg (mul_nonneg Submission.BoseGases.chiSupAbs_nonneg
        (Submission.BoseGases.chiSmallNormFactor_nonneg M))
        (mul_nonneg (div_nonneg (by norm_num) (le_of_lt (Work.SmallBoxSliding.smallConvLower_pos M)))
          (mul_nonneg Submission.BoseGases.chiSupAbs_nonneg
            (Submission.BoseGases.chiSmallDecay_nonneg M))))
        (by positivity)
    · intro v R ℓ d hR hℓ hd hv hvrad hv_supp h hRd hRχ A hAmeas hAsub u a
      have hfsupp : ∀ z : ℝ³, R ≤ ‖z‖ → Submission.BoseGases.g0 v h z = 0 :=
        fun z hz => Submission.BoseGases.g0_zero_of_norm_ge hv_supp hz h
      have hAnn : 0 ≤ Submission.BoseGases.chiSupAbs := Submission.BoseGases.chiSupAbs_nonneg
      have hNnn : 0 ≤ Submission.BoseGases.chiSmallNormFactor M :=
        Submission.BoseGases.chiSmallNormFactor_nonneg M
      have hDnn : 0 ≤ Submission.BoseGases.chiSmallDecay M :=
        Submission.BoseGases.chiSmallDecay_nonneg M
      have hSpos : 0 < Work.SmallBoxSliding.smallConvLower M :=
        Work.SmallBoxSliding.smallConvLower_pos M
      have hKnn : 0 ≤ (2 / Work.SmallBoxSliding.smallConvLower M) *
          (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M) :=
        mul_nonneg (div_nonneg (by norm_num) (le_of_lt hSpos)) (mul_nonneg hAnn hDnn)
      have hev : ∀ z : ℝ³, Submission.BoseGases.g0 v h (-z) = Submission.BoseGases.g0 v h z :=
        Submission.BoseGases.g0_even hvrad h
      -- pointwise domination, with the sharp sup bound on the (now `a`-slot) cutoff factor
      have hpt : ∀ y : ℝ³,
          |Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g0 v h) y a| ≤
          (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallNormFactor M) *
            (((2 / Work.SmallBoxSliding.smallConvLower M) *
              (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M)) *
              |Submission.BoseGases.g0 v h (a - y)|) := by
        intro y
        rw [Submission.BoseGases.wSmallPair_symm (M := M) hM u hev y a]
        have hbase := Work.BoseFixB1.abs_wSmallPair_le (M := M) hM hℓ hd hfsupp hRd hRχ u a y
        have hchi : Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • a - u)
            ≤ Submission.BoseGases.chiSmallNormFactor M :=
          le_trans (le_abs_self _) (abs_chiSmall_le_normFactor hM _)
        have hfac : Submission.BoseGases.chiSupAbs
              * Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • a - u)
            ≤ Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallNormFactor M :=
          mul_le_mul_of_nonneg_left hchi hAnn
        have hrest : 0 ≤ ((2 / Work.SmallBoxSliding.smallConvLower M) *
            (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M)) *
            |Submission.BoseGases.g0 v h (a - y)| := mul_nonneg hKnn (abs_nonneg _)
        exact le_trans hbase (mul_le_mul_of_nonneg_right hfac hrest)
      -- integrability of the shifted modulus of `g₀`
      have hfabs : MeasureTheory.Integrable
          (fun y : ℝ³ => |Submission.BoseGases.g0 v h (a - y)|) :=
        (Submission.BoseGases.g0_integrable hR hv_supp h).abs.comp_sub_left a
      have hdom_int : MeasureTheory.IntegrableOn
          (fun y : ℝ³ =>
            (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallNormFactor M) *
              (((2 / Work.SmallBoxSliding.smallConvLower M) *
                (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M)) *
                |Submission.BoseGases.g0 v h (a - y)|)) A :=
        (((hfabs.const_mul ((2 / Work.SmallBoxSliding.smallConvLower M) *
            (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M))).const_mul
            (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallNormFactor M))).integrableOn
      have hstep1 : (∫ y in A,
            |Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g0 v h) y a|)
          ≤ ∫ y in A,
            (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallNormFactor M) *
              (((2 / Work.SmallBoxSliding.smallConvLower M) *
                (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M)) *
                |Submission.BoseGases.g0 v h (a - y)|) :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall (fun y => abs_nonneg _)) hdom_int
          (Filter.Eventually.of_forall hpt)
      have hstep2 : (∫ y in A,
            (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallNormFactor M) *
              (((2 / Work.SmallBoxSliding.smallConvLower M) *
                (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M)) *
                |Submission.BoseGases.g0 v h (a - y)|))
          = (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallNormFactor M) *
              (((2 / Work.SmallBoxSliding.smallConvLower M) *
                (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M)) *
                ∫ y in A, |Submission.BoseGases.g0 v h (a - y)|) := by
        rw [integral_const_mul, integral_const_mul]
      have hstep3 : (∫ y in A, |Submission.BoseGases.g0 v h (a - y)|)
          ≤ ∫ y : ℝ³, |Submission.BoseGases.g0 v h (a - y)| :=
        setIntegral_le_integral hfabs (Filter.Eventually.of_forall (fun y => abs_nonneg _))
      have hstep4 : (∫ y : ℝ³, |Submission.BoseGases.g0 v h (a - y)|)
          = ∫ z : ℝ³, |Submission.BoseGases.g0 v h z| :=
        Submission.BoseGases.integral_comp_sub_left
          (fun z : ℝ³ => |Submission.BoseGases.g0 v h z|) a
      have hstep5 : (∫ z : ℝ³, |Submission.BoseGases.g0 v h z|)
          = 8 * π * _root_.BoseGases.a v :=
        Submission.BoseGases.g0_abs_integral hR hv hvrad hv_supp h
      have hAnn' : 0 ≤ Submission.BoseGases.chiSupAbs
          * Submission.BoseGases.chiSmallNormFactor M := mul_nonneg hAnn hNnn
      calc ∫ y in A, |Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g0 v h) y a|
          ≤ ∫ y in A,
              (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallNormFactor M) *
                (((2 / Work.SmallBoxSliding.smallConvLower M) *
                  (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M)) *
                  |Submission.BoseGases.g0 v h (a - y)|) := hstep1
        _ = (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallNormFactor M) *
              (((2 / Work.SmallBoxSliding.smallConvLower M) *
                (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M)) *
                ∫ y in A, |Submission.BoseGases.g0 v h (a - y)|) := hstep2
        _ ≤ (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallNormFactor M) *
              (((2 / Work.SmallBoxSliding.smallConvLower M) *
                (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M)) *
                ∫ y : ℝ³, |Submission.BoseGases.g0 v h (a - y)|) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hstep3 hKnn) hAnn'
        _ = (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallNormFactor M) *
              (((2 / Work.SmallBoxSliding.smallConvLower M) *
                (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M)) *
                ∫ z : ℝ³, |Submission.BoseGases.g0 v h z|) := by rw [hstep4]
        _ = (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallNormFactor M) *
              (((2 / Work.SmallBoxSliding.smallConvLower M) *
                (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M)) *
                (8 * π * _root_.BoseGases.a v)) := by rw [hstep5]
        _ = ((Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallNormFactor M) *
              ((2 / Work.SmallBoxSliding.smallConvLower M) *
                (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M)) * (8 * π)) *
              _root_.BoseGases.a v := by ring
  · -- the degenerate case `M = 0`: the kernel vanishes identically, so `C = 0` works
    have hM0 : M = 0 := by omega
    refine ⟨0, le_refl 0, ?_⟩
    intro v R ℓ d hR hℓ hd hv hvrad hv_supp h hRd hRχ A hAmeas hAsub u a
    subst hM0
    have hzero : ∀ y : ℝ³,
        Submission.BoseGases.wSmallPair 0 ℓ d u (Submission.BoseGases.g0 v h) y a = 0 :=
      fun y => wSmallPair_zero_of_M_zero u (Submission.BoseGases.g0 v h) y a
    simp [hzero]

end Work.BoseFixB1S
