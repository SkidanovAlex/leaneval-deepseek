import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1.Defs
import Submission.Work.BoseFixB1.KH.GapDefs
import Submission.Work.BoseFixB1P.cnPlusBoxInd_integral_u_le_neuFrac
import Submission.Work.BoseFixB1S.boxPoincareBox3
import Submission.Work.OneBodyKin.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BoseFixB1.KH

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-!
# `Work.BoseFixB1.KH.gap_pairing` — the small-box gap pairing

This module proves the lemma of the paper's §5 reduction that pairs the *small-box excited count*
with the *anchored box's Neumann resolvent fraction*: the `u`-average of `n₊(B(u))` at one
particle is at most `(1 + π⁻²)` times `neuFrac ℓ (dℓ)⁻² 0 (Q₀φ)`, with the **sharp** constant
(Brietzke–Solovej Lemma 3.10 first part; FS `eq:appTB` against FS `eq:DefT`'s Neumann term).

## The formal route implemented here

* **Per box** (`per_box_gap`): for an axis-parallel box `B = Box3 p q` with all sides `≤ a`, a
  coefficient `c` with `c·a² ≤ 1`, and smooth `h`, `g`: writing `u = h − ⨍_B h`, `w = g − ⨍_B g`,

      ∫_B u² ≤ (1+π⁻²)·[∫_B h² − 2c∫_B hg + c∑_k∫_B(∂_k g)² + c²∫_B g²].

  Proof: `∫_B(h−cg)² = ∫_B(u−cw+D)² + (perfect square) ≥ A − 2cB + c²C` with `A = ∫_B u²`,
  `B = ∫_B uw`, `C = ∫_B w²`, `D = ⨍_Bh − c⍍_Bg`; the SHARP box Poincaré
  (`Work.BoseFixB1S.boxPoincareBox3`, from the corpus's Neumann cosine-mode Parseval machinery)
  gives `π²c·C ≤ c·∑_k∫_B(∂_kw)²`, and the exact Young inequality
  `2c·B ≤ (1+π²)⁻¹A + (1+π²)c²C` (equality at `t = √A/((1+π²)c)`) closes the chain with
  `A ≤ (1+π⁻²)·[∫_B(h−cg)² + c∑_k∫_B(∂_kg)²]`.
* **Summing over the sliding family**: the count is the local mean-free mass
  (`Work.BoseFixB1P.cnPlusBoxInd_one_eq`), and with `h := φ − ⨍_{acube ℓ}φ` the box means shift
  correctly, so the per-box bound can be integrated in `u`; the trial functional telescopes
  because `∫_u boxTrialForm c (dlBox ℓ d u) h g = boxTrialForm c (acube ℓ) h g`
  (`Work.BoseFixB1P.integral_u_boxTrialForm`, i.e. the `u`-tube identity
  `∫_u 1_{B(u)}(x) du = 1_{acube ℓ}(x)` applied to the four linear terms).
* **The `sInf`**: `boxTrialForm c (acube ℓ) (Q₀φ) g` is exactly the `neuFrac` trial value, so
  `X ≤ (1+π⁻²)·sInf` follows from `X ≤` every trial value (`le_csInf`, nonemptiness by `g = 0`).
-/

/-! ## 1. The per-box inequality -/

/-- The axis-parallel box `Box3 p q` is compact (the image of the compact coordinate box `Icc p q`
under the continuous homeomorphism `WithLp.toLp 2`). -/
lemma isCompact_box3 (p q : Fin 3 → ℝ) : IsCompact (Work.BoseFixB1P.Box3 p q) := by
  have h : Work.BoseFixB1P.Box3 p q = WithLp.toLp 2 '' Set.Icc p q := by
    ext x
    constructor
    · intro hx
      refine ⟨x.ofLp, ?_, ?_⟩
      · rw [Set.mem_Icc]; exact ⟨fun j => (hx j).1, fun j => (hx j).2⟩
      · simp
    · rintro ⟨y, hy, rfl⟩ j
      rw [Set.mem_Icc] at hy
      exact ⟨hy.1 j, hy.2 j⟩
  rw [h]
  exact (isCompact_Icc (a := p) (b := q)).image (PiLp.continuous_toLp ..)

/-- The Bochner integral of a constant over a set is the constant times its real volume. -/
lemma integral_const_set (P : Set E3) (c : ℝ) :
    (∫ x in P, c) = c * Work.BoseFixB1P.volBox P := by
  rw [MeasureTheory.setIntegral_const]
  simp [Work.BoseFixB1P.volBox, MeasureTheory.Measure.real_def, smul_eq_mul, mul_comm]

/-- **The one-particle excited count is the mass of `bQ φ`.**  In the notation of this area
(`Work.BoseFixB1.KH.bQ ℓ d u φ = 1_{B(u)}(φ − ⍍_{B(u)}φ)`, the indicator-based mean-free
projection of the target's statement), the sliding excited count is the integral of the square of
`bQ φ`. -/
lemma cnPlusBoxInd_one_eq_bQ {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (φ : E3 → ℝ) (hφ : ContDiff ℝ (⊤ : ENat) φ) (u : E3) :
    Work.UBBInputs8.cnPlusBoxInd ℓ (Submission.BoseGases.dlBox ℓ d u)
        (Work.SmallBoxSliding.boxMass ℓ d u) (fun x : Submission.BoseGases.X 1 => φ (x 0))
      = ∫ z : E3, (bQ ℓ d u φ z) ^ 2 := by
  have hmean : (1 / Work.SmallBoxSliding.boxMass ℓ d u) *
        (∫ w in Submission.BoseGases.dlBox ℓ d u, φ w)
      = bMean ℓ d u φ := by
    rw [bMean]
    congr 1
    rw [← MeasureTheory.integral_indicator (Work.SmallBoxSliding.measurableSet_dlBox ℓ d u)]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with w
    by_cases hw : w ∈ Submission.BoseGases.dlBox ℓ d u
    · simp [boxInd_apply, Set.indicator_of_mem hw]
    · simp [boxInd_apply, Set.indicator_of_notMem hw]
  rw [Work.BoseFixB1P.cnPlusBoxInd_one_eq hℓ hd φ hφ.continuous u, hmean,
    ← MeasureTheory.integral_indicator (Work.SmallBoxSliding.measurableSet_dlBox ℓ d u)]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with z
  rw [bQ_apply, boxInd_apply]
  by_cases hz : z ∈ Submission.BoseGases.dlBox ℓ d u
  · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz, one_mul]
  · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz, zero_mul]
    simp

/-- **The per-box gap inequality.**  On an axis-parallel box `P = Box3 p q` with all sides `≤ a`
and a coefficient `c > 0` with `c·a² ≤ 1`, the local mean-free mass of a smooth `h` is bounded by
`(1 + π⁻²)` times the `neuFrac` trial functional of `(h, g)`:

    localVar P h ≤ (1 + π⁻²) · boxTrialForm c P h g .

The constant is sharp (the box Poincaré constant is `π²/a²` and the Young inequality is exact). -/
theorem per_box_gap {a c : ℝ} (ha : 0 < a) (hc : 0 < c) (hca : c * a ^ 2 ≤ 1)
    (p q : Fin 3 → ℝ) (hpq : ∀ j : Fin 3, q j - p j ≤ a)
    (hvol : 0 < Work.BoseFixB1P.volBox (Work.BoseFixB1P.Box3 p q))
    {h g : E3 → ℝ} (hh : ContDiff ℝ (⊤ : ENat) h) (hg : ContDiff ℝ (⊤ : ENat) g) :
    Work.BoseFixB1P.localVar (Work.BoseFixB1P.Box3 p q) h
      ≤ (1 + (Real.pi ^ 2)⁻¹) *
          Work.BoseFixB1P.boxTrialForm c (Work.BoseFixB1P.Box3 p q) h g := by
  classical
  set P : Set E3 := Work.BoseFixB1P.Box3 p q with hPdef
  have hPcomp : IsCompact P := by rw [hPdef]; exact isCompact_box3 p q
  have hint : ∀ {f : E3 → ℝ}, Continuous f → IntegrableOn f P volume :=
    fun {f} hf => ContinuousOn.integrableOn_compact hPcomp hf.continuousOn
  -- the box means, the mean-free parts and their mismatch
  set M : ℝ := ∫ x in P, h x with hMdef
  set m : ℝ := (1 / Work.BoseFixB1P.volBox P) * M with hmdef
  set N : ℝ := ∫ x in P, g x with hNdef
  set n : ℝ := (1 / Work.BoseFixB1P.volBox P) * N with hndef
  set u : E3 → ℝ := fun x => h x - m with hudef
  set w : E3 → ℝ := fun x => g x - n with hwdef
  set D : ℝ := m - c * n with hDdef
  have hu_cont : Continuous u := by rw [hudef]; exact hh.continuous.sub continuous_const
  have hw_cont : Continuous w := by rw [hwdef]; exact hg.continuous.sub continuous_const
  have hmM : m * Work.BoseFixB1P.volBox P = M := by rw [hmdef]; field_simp
  have hnN : n * Work.BoseFixB1P.volBox P = N := by rw [hndef]; field_simp
  have hu_zero : (∫ x in P, u x) = 0 := by
    rw [hudef, MeasureTheory.integral_sub (hint hh.continuous) (hint continuous_const),
      integral_const_set, hmM, sub_self]
  have hw_zero : (∫ x in P, w x) = 0 := by
    rw [hwdef, MeasureTheory.integral_sub (hint hg.continuous) (hint continuous_const),
      integral_const_set, hnN, sub_self]
  have hw_cd : ContDiff ℝ (⊤ : ENat) w := by rw [hwdef]; exact hg.sub contDiff_const
  -- the aggregated quantities
  set A : ℝ := ∫ x in P, (u x) ^ 2 with hAdef
  set B : ℝ := ∫ x in P, u x * w x with hBdef
  set C : ℝ := ∫ x in P, (w x) ^ 2 with hCdef
  set Sw : ℝ := ∑ k : Fin 3, ∫ x in P,
      (fderiv ℝ w x (Submission.BoseGases.kcStdBasis k)) ^ 2 with hSwdef
  set Sg : ℝ := ∑ k : Fin 3, ∫ x in P,
      (fderiv ℝ g x (Submission.BoseGases.kcStdBasis k)) ^ 2 with hSgdef
  set T : ℝ := Work.BoseFixB1P.boxTrialForm c P h g with hTdef
  -- the SHARP box Poincare inequality at the mean-free part of `g`
  have hpoin : Real.pi ^ 2 / a ^ 2 * C ≤ Sw := by
    rw [hSwdef]
    have h0 : (∫ x in Work.BoseFixB1P.Box3 p q, w x) = 0 := by rw [← hPdef]; exact hw_zero
    exact Work.BoseFixB1S.boxPoincareBox3 ha p q hpq w hw_cd h0
  have hCn : 0 ≤ C := integral_nonneg (fun x => sq_nonneg _)
  -- the trial form is `int (h - c g)^2` plus the kinetic sum of `g`
  have hT1 : T = (∫ x in P, (h x - c * g x) ^ 2) + c * Sg := by
    rw [hTdef, Work.BoseFixB1P.boxTrialForm, hSgdef,
      Work.BoseFixB1S.integral_sq_sub_mul hPcomp hh.continuous hg.continuous c]
    ring
  have hT2 : (∫ x in P, (h x - c * g x) ^ 2) = ∫ x in P, (u x - c * w x + D) ^ 2 := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards with x
    rw [hudef, hwdef, hDdef]
    ring
  have hSv : Sg = Sw := by
    rw [hSgdef, hSwdef]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    apply MeasureTheory.integral_congr_ae
    filter_upwards with x
    rw [hwdef, fderiv_sub_const]
  -- the constant part of the shift is a perfect square
  have hT3 : A - 2 * c * B + c ^ 2 * C ≤ ∫ x in P, (u x - c * w x + D) ^ 2 := by
    have hexp := Work.BoseFixB1S.integral_sq_sub_mul_add_const hPcomp hu_cont hw_cont c D
    rw [hexp, hAdef, hBdef, hCdef, hu_zero, hw_zero]
    have hvolnn : 0 ≤ Work.BoseFixB1P.volBox P := Work.BoseFixB1P.volBox_nonneg P
    nlinarith [sq_nonneg D, hvolnn]
  -- the exact Young inequality
  have hamgm : 2 * c * B ≤ (1 + Real.pi ^ 2)⁻¹ * A + (1 + Real.pi ^ 2) * c ^ 2 * C := by
    have hraw := Work.BoseFixB1S.two_mul_integral_mul_le hPcomp hu_cont hw_cont c
    rw [← hAdef, ← hBdef, ← hCdef] at hraw
    exact hraw
  -- the Poincare term scaled by `c`, using `c a^2 ≤ 1`
  have hSc : c * (Real.pi ^ 2 / a ^ 2 * C) ≤ c * Sw :=
    mul_le_mul_of_nonneg_left hpoin (le_of_lt hc)
  have ha2 : (0 : ℝ) < a ^ 2 := by positivity
  have key : Real.pi ^ 2 * c ^ 2 * a ^ 2 ≤ c * Real.pi ^ 2 := by
    calc Real.pi ^ 2 * c ^ 2 * a ^ 2 = (Real.pi ^ 2 * c) * (c * a ^ 2) := by ring
      _ ≤ (Real.pi ^ 2 * c) * 1 := mul_le_mul_of_nonneg_left hca (by positivity)
      _ = c * Real.pi ^ 2 := by ring
  have h1 : Real.pi ^ 2 * c ^ 2 ≤ c * (Real.pi ^ 2 / a ^ 2) := by
    rw [← mul_div_assoc, le_div_iff₀ ha2]
    exact key
  have hcc : Real.pi ^ 2 * c ^ 2 * C ≤ c * (Real.pi ^ 2 / a ^ 2 * C) := by
    calc Real.pi ^ 2 * c ^ 2 * C = (Real.pi ^ 2 * c ^ 2) * C := by ring
      _ ≤ (c * (Real.pi ^ 2 / a ^ 2)) * C := mul_le_mul_of_nonneg_right h1 hCn
      _ = c * (Real.pi ^ 2 / a ^ 2 * C) := by ring
  have hT_expr : T = (∫ x in P, (u x - c * w x + D) ^ 2) + c * Sw := by rw [hT1, hT2, hSv]
  have hTlb : A - 2 * c * B + (1 + Real.pi ^ 2) * c ^ 2 * C ≤ T := by
    have hgoal : A - 2 * c * B + (1 + Real.pi ^ 2) * c ^ 2 * C
        = (A - 2 * c * B + c ^ 2 * C) + Real.pi ^ 2 * c ^ 2 * C := by ring
    rw [hgoal, hT_expr]
    linarith [hT3, hSc, hcc]
  have hfinal : A ≤ (1 + (Real.pi ^ 2)⁻¹) * T := Work.BoseFixB1S.arith_final_le hTlb hamgm
  have hloc : Work.BoseFixB1P.localVar (Work.BoseFixB1P.Box3 p q) h = A := by
    rw [Work.BoseFixB1P.localVar, hAdef, hudef, hmdef, hMdef, hPdef]
  rw [hloc]
  exact hfinal

/-! ## 2. The gap pairing -/

/-- **The small-box gap pairing** (namespace `Work.BoseFixB1.KH`; Brietzke–Solovej
`arXiv:1901.00537` Lemma 3.10 first part; FS `eq:appTB` against FS `eq:DefT`'s Neumann term).
With `B(u) = dlBox ℓ d u = acube ℓ ∩ ((dℓ)•u + acube (dℓ))` the small boxes cut by the anchored box
`Λ = acube ℓ`, `boxMass ℓ d u = |B(u)|` its true volume and `Q_{B(u)} = 1_{B(u)} − P_{B(u)}` the
indicator-based mean-free projection (`Work.UBBInputs8.boxQInd`):

  `∫_u cnPlusBoxInd ℓ (dlBox ℓ d u) (boxMass ℓ d u) φ du ≤ (1+π⁻²)·neuFrac ℓ (dℓ)⁻² 0 (Q_0 φ)`

`neuFrac` being the corpus's Dirichlet-principle `sInf` (`Work.BoseKinLoc.neuFrac`, the anchored
box Neumann resolvent fraction) and `Q_0 = Qfree ℓ 0`.  No smallness hypothesis on `ℓ, d` is
needed; the constant `1+π⁻²` is exactly the sharp one.

Proof route: unfold the count to the local mean-free mass (`cnPlusBoxInd_one_eq`), shift `φ` by the
anchored mean `⍍_Λφ` so that the box means transform correctly, apply the per-box inequality
`per_box_gap` at `a = ℓd`, `c = (ℓd)⁻²` pointwise in `u` (the box `dlBox ℓ d u` is `Box3` with
corners `boxLo`, `boxHi` and sides `≤ ℓd`), integrate in `u` (the trial functional telescopes by
`integral_u_boxTrialForm`), and take the `sInf` of the remaining trial functional, which is exactly
`neuFrac`'s defining set. -/
theorem gap_pairing {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (φ : EuclideanSpace ℝ (Fin 3) → ℝ) (hφ : ContDiff ℝ (⊤ : ENat) φ) :
    (∫ u : EuclideanSpace ℝ (Fin 3),
        Work.UBBInputs8.cnPlusBoxInd ℓ (Submission.BoseGases.dlBox ℓ d u)
          (Work.SmallBoxSliding.boxMass ℓ d u) (fun x : Submission.BoseGases.X 1 => φ (x 0)))
      ≤ (1 + (Real.pi ^ 2)⁻¹) *
          Work.BoseKinLoc.neuFrac ℓ ((d * ℓ) ^ (-2 : ℤ)) 0 (Work.BoseKinLoc.Qfree ℓ 0 φ) := by
  classical
  set c : ℝ := (d * ℓ) ^ (-2 : ℤ) with hc
  set M : ℝ := (ℓ ^ 3)⁻¹ * ∫ x in Submission.BoseGases.acube ℓ, φ x with hM
  set h : E3 → ℝ := fun x => φ x - M with hh
  have hcd : ContDiff ℝ (⊤ : ENat) h := by rw [hh]; exact hφ.sub contDiff_const
  have hcpos : 0 < c := by rw [hc]; positivity
  have hcL : c * (ℓ * d) ^ 2 ≤ 1 := by
    rw [hc, zpow_neg, zpow_ofNat]
    rw [show (ℓ * d) ^ 2 = ((d * ℓ) ^ 2) by ring]
    rw [inv_mul_cancel₀ (by positivity : ((d * ℓ) ^ 2) ≠ 0)]
  -- (1) the count is the local mean-free mass
  have hloc : (∫ u : E3, Work.UBBInputs8.cnPlusBoxInd ℓ (Submission.BoseGases.dlBox ℓ d u)
        (Work.SmallBoxSliding.boxMass ℓ d u) (fun x : Submission.BoseGases.X 1 => φ (x 0)))
      = ∫ u : E3, Work.BoseFixB1P.localVar (Submission.BoseGases.dlBox ℓ d u) h := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards with u
    rw [Work.BoseFixB1P.cnPlusBoxInd_one_eq hℓ hd φ hφ.continuous u]
    rw [Work.BoseFixB1P.localVar, Work.BoseFixB1P.boxMass_eq_volBox]
    by_cases hnull : (volume : Measure E3) (Submission.BoseGases.dlBox ℓ d u) = 0
    · rw [MeasureTheory.setIntegral_measure_zero _ hnull,
        MeasureTheory.setIntegral_measure_zero _ hnull]
    · have hlt := Work.SmallBoxSliding.volume_dlBox_lt_top hℓ d u
      have hvne : Work.BoseFixB1P.volBox (Submission.BoseGases.dlBox ℓ d u) ≠ 0 := by
        rw [Work.BoseFixB1P.volBox, MeasureTheory.Measure.real_def]
        intro h0
        rcases (ENNReal.toReal_eq_zero_iff _).mp h0 with h1 | h1
        · exact hnull h1
        · exact absurd h1 (ne_of_lt hlt)
      have hIntφ : IntegrableOn φ (Submission.BoseGases.dlBox ℓ d u) volume :=
        hφ.continuous.continuousOn.integrableOn_compact
          (Work.SmallBoxTBWord.isCompact_dlBox hℓ hd u)
      have hIntM : IntegrableOn (fun _ : E3 => M) (Submission.BoseGases.dlBox ℓ d u) volume :=
        continuous_const.continuousOn.integrableOn_compact
          (Work.SmallBoxTBWord.isCompact_dlBox hℓ hd u)
      have hsub : (∫ w in Submission.BoseGases.dlBox ℓ d u, h w)
          = (∫ w in Submission.BoseGases.dlBox ℓ d u, φ w)
            - M * Work.BoseFixB1P.volBox (Submission.BoseGases.dlBox ℓ d u) := by
        rw [show h = fun w : E3 => φ w - M from hh]
        rw [MeasureTheory.integral_sub hIntφ hIntM, integral_const_set]
      rw [hsub]
      have hbm : (1 / Work.BoseFixB1P.volBox (Submission.BoseGases.dlBox ℓ d u)) *
            ((∫ w in Submission.BoseGases.dlBox ℓ d u, φ w)
              - M * Work.BoseFixB1P.volBox (Submission.BoseGases.dlBox ℓ d u))
          = (1 / Work.BoseFixB1P.volBox (Submission.BoseGases.dlBox ℓ d u)) *
              (∫ w in Submission.BoseGases.dlBox ℓ d u, φ w) - M := by
        field_simp
      rw [hbm]
      apply MeasureTheory.integral_congr_ae
      filter_upwards with z
      rw [show h z = φ z - M from by rw [hh]]
      ring
  -- (2) the per-box bound, integrated in `u`
  have hkey : ∀ g : E3 → ℝ, ContDiff ℝ (⊤ : ENat) g → HasCompactSupport g →
      (∫ u : E3, Work.BoseFixB1P.localVar (Submission.BoseGases.dlBox ℓ d u) h)
        ≤ (1 + (Real.pi ^ 2)⁻¹) *
            Work.BoseFixB1P.boxTrialForm c (Submission.BoseGases.acube ℓ) h g := by
    intro g hg _
    have hper : ∀ u : E3, Work.BoseFixB1P.localVar (Submission.BoseGases.dlBox ℓ d u) h
        ≤ (1 + (Real.pi ^ 2)⁻¹) *
            Work.BoseFixB1P.boxTrialForm c (Submission.BoseGases.dlBox ℓ d u) h g := by
      intro u
      by_cases hnull : (volume : Measure E3) (Submission.BoseGases.dlBox ℓ d u) = 0
      · have hz : ∀ F : E3 → ℝ, (∫ x in Submission.BoseGases.dlBox ℓ d u, F x) = 0 :=
          fun F => MeasureTheory.setIntegral_measure_zero F hnull
        have hl : Work.BoseFixB1P.localVar (Submission.BoseGases.dlBox ℓ d u) h = 0 := by
          rw [Work.BoseFixB1P.localVar]; exact hz _
        have hsum0 : (∑ k : Fin 3, ∫ x in Submission.BoseGases.dlBox ℓ d u,
            (fderiv ℝ g x (Submission.BoseGases.kcStdBasis k)) ^ 2) = 0 :=
          Finset.sum_eq_zero (fun k _ => hz _)
        have hb : Work.BoseFixB1P.boxTrialForm c (Submission.BoseGases.dlBox ℓ d u) h g = 0 := by
          rw [Work.BoseFixB1P.boxTrialForm, hz _, hz _, hsum0, hz _]; ring
        rw [hl, hb, mul_zero]
      · have hlt := Work.SmallBoxSliding.volume_dlBox_lt_top hℓ d u
        have hvolpos : 0 < Work.BoseFixB1P.volBox
            (Work.BoseFixB1P.Box3 (Work.BoseFixB1P.boxLo ℓ d u) (Work.BoseFixB1P.boxHi ℓ d u)) := by
          rw [← Work.BoseFixB1P.dlBox_eq_Box3]
          rw [Work.BoseFixB1P.volBox, MeasureTheory.Measure.real_def, ENNReal.toReal_pos_iff]
          exact ⟨bot_lt_iff_ne_bot.mpr hnull, hlt⟩
        have hbox := per_box_gap (a := ℓ * d) (c := c) (by positivity) hcpos hcL
          (p := Work.BoseFixB1P.boxLo ℓ d u) (q := Work.BoseFixB1P.boxHi ℓ d u)
          (fun j => Work.BoseFixB1P.boxHi_sub_boxLo_le u j) hvolpos hcd hg
        simpa [Work.BoseFixB1P.dlBox_eq_Box3] using hbox
    obtain ⟨hint, hint_eq⟩ := Work.BoseFixB1P.integral_u_boxTrialForm hℓ hd c
      hcd.continuous hg
    rw [← hint_eq]
    calc (∫ u : E3, Work.BoseFixB1P.localVar (Submission.BoseGases.dlBox ℓ d u) h)
        ≤ ∫ u : E3, (1 + (Real.pi ^ 2)⁻¹) *
            Work.BoseFixB1P.boxTrialForm c (Submission.BoseGases.dlBox ℓ d u) h g :=
          MeasureTheory.integral_mono_of_nonneg
            (Filter.Eventually.of_forall fun u => integral_nonneg fun _ => sq_nonneg _)
            (hint.const_mul _) (Filter.Eventually.of_forall hper)
      _ = (1 + (Real.pi ^ 2)⁻¹) *
            ∫ u : E3, Work.BoseFixB1P.boxTrialForm c (Submission.BoseGases.dlBox ℓ d u) h g :=
          MeasureTheory.integral_const_mul _ _
  -- (3) the `sInf` of the trial functional is `neuFrac`
  have hpos : 0 < 1 + (Real.pi ^ 2)⁻¹ := by positivity
  have hSinf : (∫ u : E3, Work.BoseFixB1P.localVar (Submission.BoseGases.dlBox ℓ d u) h)
        / (1 + (Real.pi ^ 2)⁻¹)
      ≤ sInf {v : ℝ | ∃ g : E3 → ℝ, ContDiff ℝ (⊤ : ENat) g ∧ HasCompactSupport g ∧
          v = Work.BoseFixB1P.boxTrialForm c (Submission.BoseGases.acube ℓ) h g} := by
    refine le_csInf ⟨Work.BoseFixB1P.boxTrialForm c (Submission.BoseGases.acube ℓ) h 0,
      ⟨0, contDiff_const, HasCompactSupport.zero, rfl⟩⟩ ?_
    rintro v ⟨g, hg, hgs, rfl⟩
    rw [div_le_iff₀ hpos]
    simpa [mul_comm] using hkey g hg hgs
  have hlam : Work.BoseKinLoc.lamBox ℓ 0 = Submission.BoseGases.acube ℓ := by
    ext x; simp [Work.BoseKinLoc.lamBox, Work.BSKinetic.bsBox]
  have hQ : Work.BoseKinLoc.Qfree ℓ 0 φ = h := by
    funext x
    have hx : h x = φ x - M := by rw [hh]
    rw [Work.BoseKinLoc.Qfree, Work.BSKinetic.bsQ, Work.BSKinetic.bsMean, hx, hM]
    congr 1
    congr 1
    apply MeasureTheory.integral_congr_ae
    filter_upwards with z
    simp
  have hneufrac : Work.BoseKinLoc.neuFrac ℓ c 0 (Work.BoseKinLoc.Qfree ℓ 0 φ)
      = sInf {v : ℝ | ∃ g : E3 → ℝ, ContDiff ℝ (⊤ : ENat) g ∧ HasCompactSupport g ∧
          v = Work.BoseFixB1P.boxTrialForm c (Submission.BoseGases.acube ℓ) h g} := by
    rw [Work.BoseKinLoc.neuFrac]
    congr 1
    ext v
    constructor
    · rintro ⟨g, hg, hgs, rfl⟩
      exact ⟨g, hg, hgs, by rw [hQ, hlam, Work.BoseFixB1P.boxTrialForm]⟩
    · rintro ⟨g, hg, hgs, rfl⟩
      exact ⟨g, hg, hgs, by rw [hQ, hlam, Work.BoseFixB1P.boxTrialForm]⟩
  rw [hloc, hneufrac]
  calc (∫ u : E3, Work.BoseFixB1P.localVar (Submission.BoseGases.dlBox ℓ d u) h)
      = (1 + (Real.pi ^ 2)⁻¹) *
          ((∫ u : E3, Work.BoseFixB1P.localVar (Submission.BoseGases.dlBox ℓ d u) h)
            / (1 + (Real.pi ^ 2)⁻¹)) := (mul_div_cancel₀ _ (ne_of_gt hpos)).symm
    _ ≤ (1 + (Real.pi ^ 2)⁻¹) *
          sInf {v : ℝ | ∃ g : E3 → ℝ, ContDiff ℝ (⊤ : ENat) g ∧ HasCompactSupport g ∧
            v = Work.BoseFixB1P.boxTrialForm c (Submission.BoseGases.acube ℓ) h g} :=
        mul_le_mul_of_nonneg_left hSinf hpos.le

end Work.BoseFixB1.KH
