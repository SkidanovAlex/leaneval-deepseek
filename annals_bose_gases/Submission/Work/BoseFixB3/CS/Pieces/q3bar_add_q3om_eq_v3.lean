import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB2.Pot.aestronglyMeasurable_potWordU
import Submission.Work.BoseFixB3.CS.Ledger
import Submission.Work.BoseFixB3.CS.Pieces.integrable_highpass_integrands
import Submission.Work.BoseFixB3.CS.Pieces.leakFn_abs_le
import Submission.Work.BoseFixB3.CS.Pieces.q3bar_add_q3om_eq_v2_of_pos
import Submission.Work.BoseFixB3.Conv.stronglyMeasurable_lowMult
import Submission.Work.BoseFixB3.HighMass.measurable_highSlot
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB3.CS.Pieces.q3bar_add_q3om_eq_v3`

The **chosen-branch** (`w₁ = wLoc ℓ (g₀ v h) 0`, `ω = omC w₀`) instance of the sum-level
decomposition `q3barWord + q3omWord = 2Σ_p∫ F'_p(q4B_p − ω_p S_p)w₁ + 2Σ_p∫(P_jP_iΦ)²·leak·ω·w₁`
proved in `Pieces.q3bar_add_q3om_eq_v2_of_pos` (FS `eq:pq'pp-sf`, `cl:advQ3sch`).

The general lemma `q3bar_add_q3om_eq_v2_of_pos` carries, besides its structural hypotheses, four
*integrability* hypotheses (`hI1`–`hI4`) on the four integrands, together with the a.e. strong
measurability of the two weights.  Those are **not** automatic from continuity of the state:
the weight `w₁ = wLoc ℓ (g₀ v h) 0` is `χ_ℓ(x)·W₁(x−y)·χ_ℓ(y)` with `W₁ = g₀/(χ⋆χ)(·/ℓ)`, which
is *unbounded* where the χ⋆χ-denominator is small, and `ω` is only a.e. bounded (by `1`,
`ScatT3.scattering_bounds_ae`).  This file discharges the six conditions for the specific weights
of the chosen branch, so that the decomposition is available in the form in which the `CS` chapter
consumes it.

## Route

* `aesm_wLoc_pair_X` — a.e. strong measurability of `x ↦ wLoc ℓ g u (x i) (x j)` for an a.e.
  strongly measurable numerator (the `i = j` case is continuity; the `i ≠ j` case is
  `BoseFixB2.Pot.aesm_wLoc_pair_X`);
* `aesm_choose_sub` — the same for `x ↦ w₀(x i − x j)` (`w₀ = Classical.choose h`), from the
  quasi-measure-preserving `BoseFixB2.Pot.qmp_coordDiff_X`;
* `integrableOn_bdd_mul_wLoc` — the master integrability tool: a multiplier `G` that is a.e.
  bounded on the box times `wLoc ℓ g 0` is integrable on the box (from `WordInteg`'s
  `integrableOn_bounded_mul_wPair_sub_abox`, i.e. `|wLoc|` need not be bounded pointwise);
* the four integrands are then dominated by `C·|wLoc|` with `C` obtained from the box bounds
  `aP_abs_le`/`highSlot_bound_of_pos`/`leakFn_abs_le` and the a.e. bound `|ω| ≤ 1`.
-/

noncomputable section

open MeasureTheory
open scoped Real Topology BigOperators

namespace Work.BoseFixB3.CS.Pieces

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option linter.unusedVariables false

/-! ## 0. Auxiliary measurability/domination facts -/

/-- A continuous function is bounded on the (compact) centred box. -/
private lemma abox_abs_bound {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {f : Submission.BoseGases.X n → ℝ}
    (hf : Continuous f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ Submission.BoseGases.abox n ℓ, |f x| ≤ C := by
  obtain ⟨C₀, hC₀⟩ := (Submission.BoseGases.abox_compact n hℓ).exists_bound_of_continuousOn
    hf.continuousOn
  refine ⟨max C₀ 0, le_max_right _ _, fun x hx => ?_⟩
  have h := hC₀ x hx
  rw [Real.norm_eq_abs] at h
  exact le_trans h (le_max_left _ _)

/-- **A.e. strong measurability of the slot pair kernel** `x ↦ wLoc ℓ g u (x i) (x j)` for an
a.e. strongly measurable numerator `g`. -/
private lemma aesm_wLoc_pair_X {n : ℕ} {ℓ : ℝ} {u : E3} {g : E3 → ℝ}
    (hg : AEStronglyMeasurable g (volume : Measure E3)) (i j : Fin n) :
    AEStronglyMeasurable (fun x : Submission.BoseGases.X n =>
        Submission.BoseGases.wLoc ℓ g u (x i) (x j))
      (volume : Measure (Submission.BoseGases.X n)) := by
  by_cases hij : i = j
  · subst hij
    have hchi : Continuous (fun x : Submission.BoseGases.X n =>
        Submission.BoseGases.chiU ℓ u (x i)) :=
      Submission.BoseGases.chi_continuous.comp (by fun_prop)
    have heq : (fun x : Submission.BoseGases.X n =>
        Submission.BoseGases.wLoc ℓ g u (x i) (x i))
        = fun x : Submission.BoseGases.X n => Submission.BoseGases.chiU ℓ u (x i) *
            Submission.BoseGases.wScaled ℓ g 0 * Submission.BoseGases.chiU ℓ u (x i) := by
      funext x
      simp [Submission.BoseGases.wLoc]
    rw [heq]
    exact ((hchi.mul continuous_const).mul hchi).aestronglyMeasurable
  · exact Work.BoseFixB2.Pot.aesm_wLoc_pair_X (ℓ := ℓ) (u := u) hg i j hij

/-- **A.e. strong measurability of the `ω`-pair** `x ↦ w₀(x i − x j)`. -/
private lemma aesm_choose_sub {n : ℕ} {v : E3 → ℝ}
    (h : ∃ w : E3 → ℝ, BoseGases.IsRadial w ∧ BoseGases.IsScatteringSolution w v)
    (i j : Fin n) :
    AEStronglyMeasurable (fun x : Submission.BoseGases.X n =>
      Classical.choose h (x i - x j)) (volume : Measure (Submission.BoseGases.X n)) := by
  by_cases hij : i = j
  · subst hij
    have heq : (fun x : Submission.BoseGases.X n => Classical.choose h (x i - x i))
        = fun _ => Classical.choose h 0 := by
      funext x; rw [sub_self]
    rw [heq]
    exact aestronglyMeasurable_const
  · have hspec := Classical.choose_spec h
    have hae : AEMeasurable (Classical.choose h) (volume : Measure E3) :=
      hspec.2.lhs_integrable.aestronglyMeasurable.aemeasurable
    exact (hae.comp_quasiMeasurePreserving
      (Work.BoseFixB2.Pot.qmp_coordDiff_X i j hij)).aestronglyMeasurable

/-- **The master integrability tool.**  A multiplier `G` which is a.e. bounded on the box and a.e.
strongly measurable there, times the slot pair kernel `wLoc ℓ g 0 (· i) (· j)`, is integrable over
the box — `|wLoc|` itself is *not* assumed bounded (the two `χ_ℓ`-factors cancel the
`(χ⋆χ)`-denominator only in the joint integral). -/
private lemma integrableOn_bdd_mul_wLoc {n : ℕ} {ℓ R : ℝ} (hℓ : 0 < ℓ)
    {g : E3 → ℝ} (hg : Integrable g) (hgsupp : ∀ z : E3, R ≤ ‖z‖ → g z = 0)
    (hRℓ : R ≤ ℓ * Submission.BoseGases.chiR0)
    {i j : Fin n} (hij : i ≠ j) {G : Submission.BoseGases.X n → ℝ}
    (hGm : AEStronglyMeasurable G (volume.restrict (Submission.BoseGases.abox n ℓ)))
    {B : ℝ} (hB : 0 ≤ B)
    (hGb : ∀ᵐ x ∂(volume.restrict (Submission.BoseGases.abox n ℓ)), |G x| ≤ B) :
    Integrable (fun x : Submission.BoseGases.X n =>
        G x * Submission.BoseGases.wLoc ℓ g 0 (x i) (x j))
      (volume.restrict (Submission.BoseGases.abox n ℓ)) := by
  have hbase := Submission.BoseGases.integrableOn_bounded_mul_wPair_sub_abox
    (N := n) (ℓ := ℓ) (R := R) hℓ (g := G) (h := g) hg hgsupp hRℓ i j hij hGm hB hGb
  refine hbase.congr (Filter.Eventually.of_forall (fun x => ?_))
  simp only [Work.BoseFixB3.wLoc_zero_eq_wPair]

/-! ## 1. The chosen-branch instance -/

theorem q3bar_add_q3om_eq_v3 {v : EuclideanSpace ℝ (Fin 3) → ℝ} (hv : 0 ≤ v)
    (hvrad : BoseGases.IsRadial v) (R : ℝ) (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball 0 R) (hav : 0 < BoseGases.a v)
    (h : ∃ w : EuclideanSpace ℝ (Fin 3) → ℝ, BoseGases.IsRadial w ∧ BoseGases.IsScatteringSolution w v)
    (fc : Work.BoseBoxFix.LowCut) (κ ℓ : ℝ) (hκ : 0 < κ) (hℓ : 0 < ℓ)
    (hRℓ : R ≤ ℓ * Submission.BoseGases.chiR0)
    {n : ℕ} (Φ : Submission.BoseGases.X n → ℝ) (hΦc : Continuous Φ) :
    Work.BoseFixB3.q3barWord fc κ ℓ (Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g0 v h) 0) Φ
      + Work.BoseFixB3.q3omWord fc κ ℓ (Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g0 v h) 0)
          (Submission.BoseGases.omC (Classical.choose h)) Φ
      = 2 * (∑ p ∈ Submission.BoseGases.pairSet n, ∫ x in Submission.BoseGases.abox n ℓ,
            Work.BoseFixB3.highSlot fc κ ℓ p.2
                (Submission.BoseGases.aP ℓ p.1 (Submission.BoseGases.aQ ℓ p.2 Φ)) x
              * (Submission.BoseGases.q4B ℓ (Submission.BoseGases.omC (Classical.choose h)) Φ p x
                 - Classical.choose h (x p.1 - x p.2)
                   * (Submission.BoseGases.aP ℓ p.2 (Submission.BoseGases.aQ ℓ p.1 Φ) x
                      + Submission.BoseGases.aQ ℓ p.2 (Submission.BoseGases.aP ℓ p.1 Φ) x))
              * Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g0 v h) 0 (x p.1) (x p.2))
        + 2 * (∑ p ∈ Submission.BoseGases.pairSet n, ∫ x in Submission.BoseGases.abox n ℓ,
            (Submission.BoseGases.aP ℓ p.1 (Submission.BoseGases.aP ℓ p.2 Φ) x) ^ 2
              * Work.BoseFixB3.CS.leakFn fc κ ℓ (x p.2)
              * Classical.choose h (x p.1 - x p.2)
              * Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g0 v h) 0 (x p.1) (x p.2)) := by
  classical
  have hg0i : Integrable (Submission.BoseGases.g0 v h) :=
    Submission.BoseGases.g0_integrable hR hv_supp h
  have hg0supp : ∀ z : E3, R ≤ ‖z‖ → Submission.BoseGases.g0 v h z = 0 :=
    fun z hz => Submission.BoseGases.g0_zero_of_norm_ge hv_supp hz h
  have hg0asm : AEStronglyMeasurable (Submission.BoseGases.g0 v h) (volume : Measure E3) :=
    hg0i.aestronglyMeasurable
  have hmem : ∀ᵐ x ∂(volume.restrict (Submission.BoseGases.abox n ℓ)),
      x ∈ Submission.BoseGases.abox n ℓ :=
    MeasureTheory.ae_restrict_mem (Submission.BoseGases.abox_measurable n ℓ)
  refine q3bar_add_q3om_eq_v2_of_pos fc κ ℓ hκ hℓ
    (Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g0 v h) 0)
    (Submission.BoseGases.omC (Classical.choose h)) Φ hΦc ?_ ?_ ?_ ?_ ?_ ?_
  · -- measurability of `w₁`
    intro p
    exact (aesm_wLoc_pair_X (ℓ := ℓ) (u := 0) hg0asm p.1 p.2).restrict
  · -- measurability of `ω`
    intro p
    exact (aesm_choose_sub h p.1 p.2).restrict
  · -- `hI1`
    intro p hp
    have hne : p.1 ≠ p.2 := (Finset.mem_filter.mp hp).2
    obtain ⟨C1, hC1_0, hC1b⟩ := Work.BoseFixB3.CS.highSlot_bound_of_pos (fc := fc) (κ := κ) (ℓ := ℓ)
      hκ hℓ p.2 (Ψ := Submission.BoseGases.aP ℓ p.1 (Submission.BoseGases.aQ ℓ p.2 Φ))
      (Submission.BoseGases.aP_continuous hℓ p.1 (Submission.BoseGases.aQ_continuous hℓ p.2 hΦc))
    obtain ⟨C2, hC2_0, hC2b⟩ := abox_abs_bound hℓ
      (Submission.BoseGases.aQ_continuous hℓ p.2 (Submission.BoseGases.aQ_continuous hℓ p.1 hΦc))
    have hGm : AEStronglyMeasurable (fun x : Submission.BoseGases.X n =>
        Work.BoseFixB3.highSlot fc κ ℓ p.2
            (Submission.BoseGases.aP ℓ p.1 (Submission.BoseGases.aQ ℓ p.2 Φ)) x
          * Submission.BoseGases.aQ ℓ p.2 (Submission.BoseGases.aQ ℓ p.1 Φ) x)
        (volume.restrict (Submission.BoseGases.abox n ℓ)) :=
      (((Work.BoseFixB3.HighMass.measurable_highSlot (fc := fc) (κ := κ) (ℓ := ℓ) p.2
          (Φ := Submission.BoseGases.aP ℓ p.1 (Submission.BoseGases.aQ ℓ p.2 Φ))
          (Submission.BoseGases.aP_continuous hℓ p.1
            (Submission.BoseGases.aQ_continuous hℓ p.2 hΦc))).aestronglyMeasurable.mul
        (Submission.BoseGases.aQ_continuous hℓ p.2
          (Submission.BoseGases.aQ_continuous hℓ p.1 hΦc)).aestronglyMeasurable)).restrict
    have hGb : ∀ᵐ x ∂(volume.restrict (Submission.BoseGases.abox n ℓ)),
        |(Work.BoseFixB3.highSlot fc κ ℓ p.2
            (Submission.BoseGases.aP ℓ p.1 (Submission.BoseGases.aQ ℓ p.2 Φ)) x)
          * Submission.BoseGases.aQ ℓ p.2 (Submission.BoseGases.aQ ℓ p.1 Φ) x| ≤ C1 * C2 := by
      rw [MeasureTheory.ae_restrict_iff' (Submission.BoseGases.abox_measurable n ℓ)]
      refine MeasureTheory.ae_of_all volume (fun x hx => ?_)
      rw [abs_mul]
      exact mul_le_mul (hC1b x hx) (hC2b x hx) (abs_nonneg _) hC1_0
    exact integrableOn_bdd_mul_wLoc hℓ hg0i hg0supp hRℓ hne hGm (mul_nonneg hC1_0 hC2_0) hGb
  · -- `hI2`
    intro p hp
    have hne : p.1 ≠ p.2 := (Finset.mem_filter.mp hp).2
    obtain ⟨C1, hC1_0, hC1b⟩ := Work.BoseFixB3.CS.highSlot_bound_of_pos (fc := fc) (κ := κ) (ℓ := ℓ)
      hκ hℓ p.2 (Ψ := Submission.BoseGases.aP ℓ p.1 Φ)
      (Submission.BoseGases.aP_continuous hℓ p.1 hΦc)
    obtain ⟨C2, hC2_0, hC2b⟩ := abox_abs_bound hℓ
      (Submission.BoseGases.aP_continuous hℓ p.2 (Submission.BoseGases.aP_continuous hℓ p.1 hΦc))
    have homm : AEStronglyMeasurable (fun x : Submission.BoseGases.X n =>
        Classical.choose h (x p.1 - x p.2)) (volume.restrict (Submission.BoseGases.abox n ℓ)) :=
      (aesm_choose_sub h p.1 p.2).restrict
    have hGm : AEStronglyMeasurable (fun x : Submission.BoseGases.X n =>
        Work.BoseFixB3.highSlot fc κ ℓ p.2 (Submission.BoseGases.aP ℓ p.1 Φ) x
          * Submission.BoseGases.aP ℓ p.2 (Submission.BoseGases.aP ℓ p.1 Φ) x
          * Classical.choose h (x p.1 - x p.2))
        (volume.restrict (Submission.BoseGases.abox n ℓ)) :=
      (((Work.BoseFixB3.HighMass.measurable_highSlot (fc := fc) (κ := κ) (ℓ := ℓ) p.2
          (Φ := Submission.BoseGases.aP ℓ p.1 Φ)
          (Submission.BoseGases.aP_continuous hℓ p.1 hΦc)).aestronglyMeasurable.mul
        (Submission.BoseGases.aP_continuous hℓ p.2
          (Submission.BoseGases.aP_continuous hℓ p.1 hΦc)).aestronglyMeasurable).mul homm)
    have homb : ∀ᵐ x ∂(volume.restrict (Submission.BoseGases.abox n ℓ)),
        |Classical.choose h (x p.1 - x p.2)| ≤ 1 :=
      Submission.BoseGases.w0_abs_le_one_box_ae hℓ hR hv hvrad hv_supp h hne
    have hGb : ∀ᵐ x ∂(volume.restrict (Submission.BoseGases.abox n ℓ)),
        |(Work.BoseFixB3.highSlot fc κ ℓ p.2 (Submission.BoseGases.aP ℓ p.1 Φ) x
          * Submission.BoseGases.aP ℓ p.2 (Submission.BoseGases.aP ℓ p.1 Φ) x
          * Classical.choose h (x p.1 - x p.2))| ≤ C1 * C2 := by
      filter_upwards [homb, hmem] with x homx hxmem
      rw [abs_mul, abs_mul]
      have h1 : |Work.BoseFixB3.highSlot fc κ ℓ p.2 (Submission.BoseGases.aP ℓ p.1 Φ) x|
            * |Submission.BoseGases.aP ℓ p.2 (Submission.BoseGases.aP ℓ p.1 Φ) x| ≤ C1 * C2 :=
        mul_le_mul (hC1b x hxmem) (hC2b x hxmem) (abs_nonneg _) hC1_0
      calc |Work.BoseFixB3.highSlot fc κ ℓ p.2 (Submission.BoseGases.aP ℓ p.1 Φ) x|
              * |Submission.BoseGases.aP ℓ p.2 (Submission.BoseGases.aP ℓ p.1 Φ) x|
              * |Classical.choose h (x p.1 - x p.2)|
          ≤ (C1 * C2) * 1 := mul_le_mul h1 homx (abs_nonneg _) (mul_nonneg hC1_0 hC2_0)
        _ = C1 * C2 := mul_one _
    have hres := integrableOn_bdd_mul_wLoc hℓ hg0i hg0supp hRℓ hne hGm
      (mul_nonneg hC1_0 hC2_0) hGb
    refine hres.congr (Filter.Eventually.of_forall (fun x => ?_))
    simp only [Submission.BoseGases.omC]
    ring
  · -- `hI3`
    intro p hp
    have hne : p.1 ≠ p.2 := (Finset.mem_filter.mp hp).2
    obtain ⟨C1, hC1_0, hC1b⟩ := Work.BoseFixB3.CS.highSlot_bound_of_pos (fc := fc) (κ := κ) (ℓ := ℓ)
      hκ hℓ p.2 (Ψ := Submission.BoseGases.aP ℓ p.1 (Submission.BoseGases.aQ ℓ p.2 Φ))
      (Submission.BoseGases.aP_continuous hℓ p.1 (Submission.BoseGases.aQ_continuous hℓ p.2 hΦc))
    obtain ⟨C3, hC3_0, hC3b⟩ := abox_abs_bound hℓ
      (Submission.BoseGases.aQ_continuous hℓ p.2 (Submission.BoseGases.aQ_continuous hℓ p.1 hΦc))
    obtain ⟨C4, hC4_0, hC4b⟩ := abox_abs_bound hℓ
      (Submission.BoseGases.aP_continuous hℓ p.2 (Submission.BoseGases.aP_continuous hℓ p.1 hΦc))
    have homm : AEStronglyMeasurable (fun x : Submission.BoseGases.X n =>
        Classical.choose h (x p.1 - x p.2)) (volume.restrict (Submission.BoseGases.abox n ℓ)) :=
      (aesm_choose_sub h p.1 p.2).restrict
    have hq4asm : AEStronglyMeasurable (fun x : Submission.BoseGases.X n =>
        Submission.BoseGases.q4B ℓ (Submission.BoseGases.omC (Classical.choose h)) Φ p x)
        (volume.restrict (Submission.BoseGases.abox n ℓ)) := by
      simp only [Submission.BoseGases.q4B]
      exact (Submission.BoseGases.aQ_continuous hℓ p.2
            (Submission.BoseGases.aQ_continuous hℓ p.1 hΦc)).aestronglyMeasurable.restrict.add
        (homm.mul (((Submission.BoseGases.aP_continuous hℓ p.2
            (Submission.BoseGases.aP_continuous hℓ p.1 hΦc)).aestronglyMeasurable.restrict.add
          (Submission.BoseGases.aP_continuous hℓ p.2
            (Submission.BoseGases.aQ_continuous hℓ p.1 hΦc)).aestronglyMeasurable.restrict).add
          (Submission.BoseGases.aQ_continuous hℓ p.2
            (Submission.BoseGases.aP_continuous hℓ p.1 hΦc)).aestronglyMeasurable.restrict))
    have hGm : AEStronglyMeasurable (fun x : Submission.BoseGases.X n =>
        Work.BoseFixB3.highSlot fc κ ℓ p.2
            (Submission.BoseGases.aP ℓ p.1 (Submission.BoseGases.aQ ℓ p.2 Φ)) x
          * (Submission.BoseGases.q4B ℓ (Submission.BoseGases.omC (Classical.choose h)) Φ p x
              - Submission.BoseGases.omC (Classical.choose h) (x p.1) (x p.2)
                * (Submission.BoseGases.aP ℓ p.2 (Submission.BoseGases.aQ ℓ p.1 Φ) x
                    + Submission.BoseGases.aQ ℓ p.2 (Submission.BoseGases.aP ℓ p.1 Φ) x)))
        (volume.restrict (Submission.BoseGases.abox n ℓ)) :=
      (Work.BoseFixB3.HighMass.measurable_highSlot (fc := fc) (κ := κ) (ℓ := ℓ) p.2
          (Φ := Submission.BoseGases.aP ℓ p.1 (Submission.BoseGases.aQ ℓ p.2 Φ))
          (Submission.BoseGases.aP_continuous hℓ p.1
            (Submission.BoseGases.aQ_continuous hℓ p.2 hΦc))).aestronglyMeasurable.mul
        (hq4asm.sub (homm.mul (((Submission.BoseGases.aP_continuous hℓ p.2
            (Submission.BoseGases.aQ_continuous hℓ p.1 hΦc)).aestronglyMeasurable.restrict.add
          (Submission.BoseGases.aQ_continuous hℓ p.2
            (Submission.BoseGases.aP_continuous hℓ p.1 hΦc)).aestronglyMeasurable.restrict))))
    have homb : ∀ᵐ x ∂(volume.restrict (Submission.BoseGases.abox n ℓ)),
        |Classical.choose h (x p.1 - x p.2)| ≤ 1 :=
      Submission.BoseGases.w0_abs_le_one_box_ae hℓ hR hv hvrad hv_supp h hne
    have hGb : ∀ᵐ x ∂(volume.restrict (Submission.BoseGases.abox n ℓ)),
        |Work.BoseFixB3.highSlot fc κ ℓ p.2
            (Submission.BoseGases.aP ℓ p.1 (Submission.BoseGases.aQ ℓ p.2 Φ)) x
          * (Submission.BoseGases.q4B ℓ (Submission.BoseGases.omC (Classical.choose h)) Φ p x
              - Submission.BoseGases.omC (Classical.choose h) (x p.1) (x p.2)
                * (Submission.BoseGases.aP ℓ p.2 (Submission.BoseGases.aQ ℓ p.1 Φ) x
                    + Submission.BoseGases.aQ ℓ p.2 (Submission.BoseGases.aP ℓ p.1 Φ) x))|
          ≤ C1 * (C3 + C4) := by
      filter_upwards [homb, hmem] with x homx hxmem
      have hq : Submission.BoseGases.q4B ℓ (Submission.BoseGases.omC (Classical.choose h)) Φ p x
          - Submission.BoseGases.omC (Classical.choose h) (x p.1) (x p.2)
            * (Submission.BoseGases.aP ℓ p.2 (Submission.BoseGases.aQ ℓ p.1 Φ) x
                + Submission.BoseGases.aQ ℓ p.2 (Submission.BoseGases.aP ℓ p.1 Φ) x)
          = Submission.BoseGases.aQ ℓ p.2 (Submission.BoseGases.aQ ℓ p.1 Φ) x
            + Classical.choose h (x p.1 - x p.2)
              * Submission.BoseGases.aP ℓ p.2 (Submission.BoseGases.aP ℓ p.1 Φ) x := by
        simp only [Submission.BoseGases.q4B, Submission.BoseGases.omC]
        ring
      have hbr : |Submission.BoseGases.aQ ℓ p.2 (Submission.BoseGases.aQ ℓ p.1 Φ) x
            + Classical.choose h (x p.1 - x p.2)
              * Submission.BoseGases.aP ℓ p.2 (Submission.BoseGases.aP ℓ p.1 Φ) x| ≤ C3 + C4 := by
        calc |Submission.BoseGases.aQ ℓ p.2 (Submission.BoseGases.aQ ℓ p.1 Φ) x
              + Classical.choose h (x p.1 - x p.2)
                * Submission.BoseGases.aP ℓ p.2 (Submission.BoseGases.aP ℓ p.1 Φ) x|
            ≤ |Submission.BoseGases.aQ ℓ p.2 (Submission.BoseGases.aQ ℓ p.1 Φ) x|
              + |Classical.choose h (x p.1 - x p.2)
                * Submission.BoseGases.aP ℓ p.2 (Submission.BoseGases.aP ℓ p.1 Φ) x| :=
                abs_add_le _ _
          _ = |Submission.BoseGases.aQ ℓ p.2 (Submission.BoseGases.aQ ℓ p.1 Φ) x|
              + |Classical.choose h (x p.1 - x p.2)|
                * |Submission.BoseGases.aP ℓ p.2 (Submission.BoseGases.aP ℓ p.1 Φ) x| := by
                rw [abs_mul]
          _ ≤ C3 + 1 * C4 := add_le_add (hC3b x hxmem)
              (mul_le_mul homx (hC4b x hxmem) (abs_nonneg _) zero_le_one)
          _ = C3 + C4 := by ring
      rw [abs_mul, hq]
      exact mul_le_mul (hC1b x hxmem) hbr (abs_nonneg _) hC1_0
    exact integrableOn_bdd_mul_wLoc hℓ hg0i hg0supp hRℓ hne hGm
      (mul_nonneg hC1_0 (add_nonneg hC3_0 hC4_0)) hGb
  · -- `hI4`
    intro p hp
    have hne : p.1 ≠ p.2 := (Finset.mem_filter.mp hp).2
    obtain ⟨C5, hC5_0, hC5b⟩ := abox_abs_bound hℓ
      (Submission.BoseGases.aP_continuous hℓ p.1 (Submission.BoseGases.aP_continuous hℓ p.2 hΦc))
    have hleakb : ∀ y : E3, |Work.BoseFixB3.CS.leakFn fc κ ℓ y|
        ≤ 1 + ((2 * Real.pi) ^ 3)⁻¹ * ℓ ^ 3
            * (volume (Metric.closedBall (0 : E3) (2 * κ))).toReal :=
      fun y => Work.BoseFixB3.CS.Pieces.leakFn_abs_le fc hκ hℓ y
    have hK4_0 : (0 : ℝ) ≤ 1 + ((2 * Real.pi) ^ 3)⁻¹ * ℓ ^ 3
        * (volume (Metric.closedBall (0 : E3) (2 * κ))).toReal := by
      have h1 : (0 : ℝ) ≤ ((2 * Real.pi) ^ 3)⁻¹ := by positivity
      have h2 : (0 : ℝ) ≤ ℓ ^ 3 := by positivity
      have h3 : (0 : ℝ) ≤ (volume (Metric.closedBall (0 : E3) (2 * κ))).toReal :=
        ENNReal.toReal_nonneg
      linarith [mul_nonneg (mul_nonneg h1 h2) h3]
    have hleakm : AEStronglyMeasurable (fun x : Submission.BoseGases.X n =>
        Work.BoseFixB3.CS.leakFn fc κ ℓ (x p.2))
        (volume.restrict (Submission.BoseGases.abox n ℓ)) :=
      ((stronglyMeasurable_const.sub (Work.BoseFixB3.Conv.stronglyMeasurable_lowMult
          (fc := fc) (κ := κ) (ℓ := ℓ) (Ψ := Work.BoseFixB3.CS.oneFn)
          measurable_const)).comp_measurable
        (by fun_prop : Measurable (fun x : Submission.BoseGases.X n => x p.2))).aestronglyMeasurable.restrict
    have homm : AEStronglyMeasurable (fun x : Submission.BoseGases.X n =>
        Classical.choose h (x p.1 - x p.2)) (volume.restrict (Submission.BoseGases.abox n ℓ)) :=
      (aesm_choose_sub h p.1 p.2).restrict
    have hGm : AEStronglyMeasurable (fun x : Submission.BoseGases.X n =>
        (Submission.BoseGases.aP ℓ p.1 (Submission.BoseGases.aP ℓ p.2 Φ) x) ^ 2
          * Work.BoseFixB3.CS.leakFn fc κ ℓ (x p.2)
          * Classical.choose h (x p.1 - x p.2))
        (volume.restrict (Submission.BoseGases.abox n ℓ)) :=
      (((Submission.BoseGases.aP_continuous hℓ p.1
          (Submission.BoseGases.aP_continuous hℓ p.2 hΦc)).aestronglyMeasurable.restrict.pow 2).mul
        hleakm).mul homm
    have homb : ∀ᵐ x ∂(volume.restrict (Submission.BoseGases.abox n ℓ)),
        |Classical.choose h (x p.1 - x p.2)| ≤ 1 :=
      Submission.BoseGases.w0_abs_le_one_box_ae hℓ hR hv hvrad hv_supp h hne
    have hGb : ∀ᵐ x ∂(volume.restrict (Submission.BoseGases.abox n ℓ)),
        |(Submission.BoseGases.aP ℓ p.1 (Submission.BoseGases.aP ℓ p.2 Φ) x) ^ 2
          * Work.BoseFixB3.CS.leakFn fc κ ℓ (x p.2)
          * Classical.choose h (x p.1 - x p.2)| ≤ C5 ^ 2
            * (1 + ((2 * Real.pi) ^ 3)⁻¹ * ℓ ^ 3
                * (volume (Metric.closedBall (0 : E3) (2 * κ))).toReal) := by
      filter_upwards [homb, hmem] with x homx hxmem
      rw [abs_mul, abs_mul, abs_pow]
      have h1 : |Submission.BoseGases.aP ℓ p.1 (Submission.BoseGases.aP ℓ p.2 Φ) x| ^ 2
          ≤ C5 ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) (hC5b x hxmem) 2
      calc |Submission.BoseGases.aP ℓ p.1 (Submission.BoseGases.aP ℓ p.2 Φ) x| ^ 2
              * |Work.BoseFixB3.CS.leakFn fc κ ℓ (x p.2)|
              * |Classical.choose h (x p.1 - x p.2)|
          ≤ (C5 ^ 2 * (1 + ((2 * Real.pi) ^ 3)⁻¹ * ℓ ^ 3
              * (volume (Metric.closedBall (0 : E3) (2 * κ))).toReal)) * 1 :=
            mul_le_mul (mul_le_mul h1 (hleakb (x p.2)) (abs_nonneg _) (sq_nonneg C5))
              homx (abs_nonneg _) (mul_nonneg (sq_nonneg C5) hK4_0)
        _ = C5 ^ 2 * (1 + ((2 * Real.pi) ^ 3)⁻¹ * ℓ ^ 3
              * (volume (Metric.closedBall (0 : E3) (2 * κ))).toReal) := mul_one _
    exact integrableOn_bdd_mul_wLoc hℓ hg0i hg0supp hRℓ hne hGm
      (mul_nonneg (sq_nonneg C5) hK4_0) hGb

end Work.BoseFixB3.CS.Pieces
