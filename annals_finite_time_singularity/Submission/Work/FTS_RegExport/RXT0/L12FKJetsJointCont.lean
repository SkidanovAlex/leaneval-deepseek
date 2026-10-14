import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.FinalV2.Defs
import Submission.Work.FTS.RegExportIface.RXT.Leaves
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKaux.L12_limit_bound
import Submission.Work.FTS_RegExport.RXT0.L12FtauTauLip
import Submission.Work.FTS_RegExport.RXT0.QlimZLipBox
import Submission.Work.FTS_RegExport.RXT0.SJC.slotJetContinuousOn
import Submission.Work.FTS_RegExport.RXVP3.velPert_unif
import Submission.Work.FTS_RegExport.RXVP3.velVanish2_unif
import Submission.Work.Spaces.bt_integral_weight_id

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `RXT0.L12FKJetsJointCont` — joint continuity of the profile transforms `L₁₂(F(τ))`, `𝔽K(F(τ))`

The target: for `0 < α ≤ 1/3` and the strong-route data `DynOK' (pExp α) C₀ Φs E g`
(which in particular carries the approximation clause `LimApprox`), the order-`≤ 2` `z`-jets
of the two profile transforms of `F(τ) = F_* + slice (GR α g) τ`, evaluated at `θ = 0`,

  `(z,τ) ↦ D_z^j (L₁₂ F(τ))(z)`,  `(z,τ) ↦ D_z^j (𝔽K F(τ))(z)`   (`j ≤ 2`),

are `ContinuousOn (0,∞) × [0,S]`.

**Route.**  Everything is reduced to the angular moments
`Qlim α g τ k z = ∫_θ K(θ)·(D_z^k F_*(z,θ) + D_z^k (slice g τ)(z,θ)) dθ`:

* `FK_DzIter_eq` identifies `D_z^j (𝔽K F(τ))(z) = Qlim α g τ j z` (`j ≤ 2`);
* `D_z (L₁₂ F(τ)) = -𝔽K F(τ)` (`L12_jet_one`), and one more `z`-derivative gives
  `D_z² (L₁₂ F(τ)) = -Qlim α g τ 1 z` (`L12_jet_two`);
* the `j = 0` case is the identity `L₁₂ F(τ)(z) = ∫_{Ioi z} L₁₂dens (F(τ))`, handled with the
  `z`-Lipschitz bound `L12_z_lip` (derivative `-L₁₂dens`, bounded by `3(π/2)C_B/z`) and the
  delegated τ-modulus `L12FtauTauLip` (which consumes the density τ-modulus, itself derived from
  the delegated `QlimTauLipW` via `mul_L12dens_eq_FK`/`Qlim_eq_FK`).

The two Lipschitz bounds of the moments — `QlimZLipBox` (in `z`, uniform in `τ`) and
`QlimTauLipW` (in `τ`, uniformly weighted by `z^{3/2}/(1+z)² ≤ 1`) — feed the ε-δ device
`continuousOn_prod_of_box_lip`, which turns a box-wise Lipschitz bound into `ContinuousOn`.

Complete; rests on `[propext, Classical.choice, Quot.sound]`.
-/

namespace Work.FTS_RegExport.RXT0

open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false

noncomputable section

namespace L12FKjc

abbrev Qm (α : ℝ) (g : Fam) (τ : ℝ) (k : ℕ) : ℝ → ℝ :=
  Work.FTS_RegExport.RXT.Sys.L12FKaux.Qlim α g τ k

abbrev SWe (z : ℝ) : ℝ := Work.FTS_RegExport.RXT.Sys.L12FKaux.SW z

abbrev Prof (α : ℝ) (g : Fam) (τ : ℝ) : ℝ → ℝ → ℝ :=
  Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
    (Work.FTS.RegExportIface.RXT.GR α g) τ

/-- **The ε-δ device.** -/
theorem continuousOn_prod_of_box_lip {f : ℝ × ℝ → ℝ} {S : ℝ}
    (h : ∀ a b : ℝ, 0 < a → a ≤ b → ∃ C : ℝ, 0 ≤ C ∧
      ∀ τ ∈ Set.Icc (0:ℝ) S, ∀ τ' ∈ Set.Icc (0:ℝ) S, ∀ z ∈ Set.Icc a b,
        ∀ z' ∈ Set.Icc a b,
        |f (z, τ) - f (z', τ')| ≤ C * (|z - z'| + |τ - τ'|)) :
    ContinuousOn f (Set.Ioi (0:ℝ) ×ˢ Set.Icc (0:ℝ) S) := by
  intro p hp
  obtain ⟨hp1, hp2⟩ := hp
  have hp1' : (0 : ℝ) < p.1 := hp1
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  obtain ⟨C, hC0, hC⟩ := h (p.1 / 2) (2 * p.1) (by linarith) (by linarith)
  refine ⟨min (p.1 / 2) (ε / (2 * C + 1)),
    lt_min (by linarith) (div_pos hε (by linarith)), ?_⟩
  intro q hq hdist
  obtain ⟨hq1, hq2⟩ := hq
  have hCpos : 0 < 2 * C + 1 := by linarith
  have hdq1 : dist q.1 p.1 ≤ dist q p := by rw [Prod.dist_eq]; exact le_max_left _ _
  have hdq2 : dist q.2 p.2 ≤ dist q p := by rw [Prod.dist_eq]; exact le_max_right _ _
  have hd1 : |q.1 - p.1| < p.1 / 2 := by
    have h1 : |q.1 - p.1| < min (p.1 / 2) (ε / (2 * C + 1)) := by
      have h2 := lt_of_le_of_lt hdq1 hdist
      rwa [Real.dist_eq] at h2
    exact lt_of_lt_of_le h1 (min_le_left _ _)
  have hq1a : p.1 / 2 ≤ q.1 := by linarith [(abs_lt.mp hd1).1]
  have hq1b : q.1 ≤ 2 * p.1 := by linarith [(abs_lt.mp hd1).2]
  have hb := hC q.2 hq2 p.2 hp2 q.1 ⟨hq1a, hq1b⟩ p.1 ⟨by linarith, by linarith⟩
  have hfin : C * (|q.1 - p.1| + |q.2 - p.2|) < ε := by
    have e1 : |q.1 - p.1| ≤ dist q p := by rw [← Real.dist_eq]; exact hdq1
    have e2 : |q.2 - p.2| ≤ dist q p := by rw [← Real.dist_eq]; exact hdq2
    have h1 : |q.1 - p.1| + |q.2 - p.2| ≤ 2 * min (p.1 / 2) (ε / (2 * C + 1)) := by
      linarith [e1, e2, hdist.le]
    calc C * (|q.1 - p.1| + |q.2 - p.2|)
        ≤ C * (2 * min (p.1 / 2) (ε / (2 * C + 1))) := mul_le_mul_of_nonneg_left h1 hC0
      _ ≤ C * (2 * (ε / (2 * C + 1))) := by
          exact mul_le_mul_of_nonneg_left
            (by linarith [min_le_right (p.1 / 2) (ε / (2 * C + 1))]) hC0
      _ = ε * (2 * C / (2 * C + 1)) := by field_simp
      _ < ε * 1 := by
          refine mul_lt_mul_of_pos_left ?_ hε
          exact (div_lt_one hCpos).mpr (by linarith)
      _ = ε := by ring
  rw [Real.dist_eq]
  exact lt_of_le_of_lt (by simpa using hb) hfin

/-- The standing data of `LimApprox` on the horizon `[0,S]`. -/
structure Stand (α C₀ S : ℝ) (Φs : Fn) (E : Fn →ₗ[ℝ] Fn) (g : Fam)
    (gn : ℕ → Fam) (Cw CB : ℝ) : Prop where
  hα : 0 < α
  hα13 : α ≤ 1 / 3
  hCw : 0 ≤ Cw
  hCB : 0 ≤ CB
  hscl : ∀ (n : ℕ) (τ : ℝ), τ ∈ Set.Icc (0:ℝ) S →
    Work.FTS.ClassC.ClassC (Work.FTS.Regularity.pExp α) (slice (gn n) τ)
  hbd : ∀ (n : ℕ) (τ : ℝ), τ ∈ Set.Icc (0:ℝ) S → ∀ (k : ℕ), k ≤ 2 → ∀ z θ : ℝ,
    0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.DzIter k (slice (gn n) τ) z θ| ≤ Cw * Work.FTS_RegExport.RXT.Sys.L12FKaux.SW z
  hsl : ∀ (τ : ℝ), τ ∈ Set.Icc (0:ℝ) S → ∀ (n k : ℕ), k ≤ 3 → ∀ z θ : ℝ,
    0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.DzIter k (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) (gn n) τ)
        z θ| ≤ CB
  hjet : ∀ (τ : ℝ), τ ∈ Set.Icc (0:ℝ) S → ∀ (k : ℕ), k ≤ 2 → ∀ z θ : ℝ,
    (z, θ) ∈ Work.Construction.Qd →
      Filter.Tendsto (fun n => Work.Spaces.DzIter k (slice (gn n) τ) z θ) Filter.atTop
        (𝓝 (Work.Spaces.DzIter k (slice g τ) z θ))
  hconv : ∀ (τ : ℝ), τ ∈ Set.Icc (0:ℝ) S → ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      Filter.Tendsto (fun n => slice (gn n) τ z θ) Filter.atTop
        (𝓝 (slice (Work.FTS.RegExportIface.RXT.GR α g) τ z θ))

theorem stand_exists {α C₀ : ℝ} {Φs : Fn} {E : Fn →ₗ[ℝ] Fn} {g : Fam}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3) {S : ℝ}
    (hA : Work.FTS.FinalV2.LimApprox (Work.FTS.Regularity.pExp α) C₀ Φs E g) :
    ∃ (gn : ℕ → Fam) (Cw CB : ℝ), Stand α C₀ S Φs E g gn Cw CB := by
  obtain ⟨T, hT, hST⟩ : ∃ T : ℝ, 0 < T ∧ S ≤ T :=
    ⟨max S 1, lt_of_lt_of_le zero_lt_one (le_max_right S 1), le_max_left S 1⟩
  obtain ⟨gn, B, L, hC, hLip, hjet0, -⟩ := hA T hT
  have hmem : ∀ τ ∈ Set.Icc (0:ℝ) S, τ ∈ Set.Icc (0:ℝ) T := fun τ hτ =>
    ⟨hτ.1, le_trans hτ.2 hST⟩
  have hcl : ∀ (n : ℕ) (τ : ℝ), τ ∈ Set.Icc (0:ℝ) T →
      Work.FTS.ClassC.ClassC (Work.FTS.Regularity.pExp α) (slice (gn n) τ) :=
    fun n τ hτ => (hC n τ hτ).1
  have hXn : ∀ (n : ℕ) (τ : ℝ), τ ∈ Set.Icc (0:ℝ) T →
      Work.FTS.Nonlin.Xn (Work.FTS.Regularity.pExp α) (slice (gn n) τ)
        ≤ C₀ * (Work.FTS.Regularity.pExp α) ^ 2 := fun n τ hτ => (hC n τ hτ).2.1
  have hXn6 : ∀ (n : ℕ) (τ : ℝ), τ ∈ Set.Icc (0:ℝ) T →
      Work.FTS.StrongGlobal.Xn6 (Work.FTS.Regularity.pExp α) (slice (gn n) τ) ≤ B :=
    fun n τ hτ => (hC n τ hτ).2.2
  obtain ⟨Cw, hCw, hbdT⟩ :=
    Work.FTS_RegExport.RXT.Sys.L12FKaux.approx_slot_bound (C₀ := C₀) hα hα13 hT hcl hXn
  obtain ⟨CB, hCB, hslT⟩ :=
    Work.FTS_RegExport.RXT.Sys.L12FKaux.ftau_slot_bound (B := B) hα hα13 hcl hXn6
  refine ⟨gn, Cw, CB, hα, hα13, hCw, hCB, ?_, ?_, ?_, ?_, ?_⟩
  · intro n τ hτ; exact hcl n τ (hmem τ hτ)
  · intro n τ hτ k hk z θ hz hθ hθ2; exact hbdT n τ (hmem τ hτ) k hk z θ hz hθ hθ2
  · intro τ hτ n k hk z θ hz hθ hθ2; exact hslT τ (hmem τ hτ) n k hk z θ hz hθ hθ2
  · intro τ hτ k hk z θ hzθ
    have h := hjet0 τ (hmem τ hτ) k 0 (by omega) z θ hzθ
    simpa only [Work.Spaces.mixed_zero_right] using h
  · intro τ hτ z θ hzθ
    have h := hjet0 τ (hmem τ hτ) 0 0 (by norm_num) z θ hzθ
    have hGR : Work.FTS.RegExportIface.RXT.GR α g z θ τ = g z θ τ :=
      Work.FTS_RegExport.RXT.ftau_GR_of_quad (α := α) (g := g) hτ.1 hzθ.1
        hzθ.2.1.le hzθ.2.2.le
    simpa only [Work.Spaces.mixed_zero_right, Work.Spaces.DzIter_zero,
      Work.FTS.Galerkin.slice_apply, hGR] using h

/-- The `z`-jets of `𝔽K F(τ)` are the angular moments. -/
theorem FK_jets_eq {α C₀ S : ℝ} {Φs : Fn} {E : Fn →ₗ[ℝ] Fn} {g : Fam}
    {gn : ℕ → Fam} {Cw CB : ℝ} (h : Stand α C₀ S Φs E g gn Cw CB)
    {τ : ℝ} (hτ : τ ∈ Set.Icc (0:ℝ) S) {j : ℕ} (hj : j ≤ 2) {z : ℝ} (hz : 0 < z) :
    Work.Spaces.DzIter j (fun z _ => Work.Construction.FK (Prof α g τ) z) z 0
      = Qm α g τ j z := by
  have hβ : 0 < Work.FTS.Regularity.pExp α := Work.FTS.Regularity.pExp_pos h.hα
  have hβ1 : Work.FTS.Regularity.pExp α ≤ 1 := Work.FTS.Regularity.pExp_le_one h.hα13
  exact Work.FTS_RegExport.RXT.Sys.L12FKaux.FK_DzIter_eq (α := α) h.hα h.hα13 hτ.1
    h.hCw h.hCB (fun n => (h.hscl n τ hτ).reg.forall 4)
    (fun n k hk z θ hz' h0 h1 => h.hbd n τ hτ k hk z θ hz' h0 h1)
    (fun n => (Work.FTS_RegExport.RXT.Sys.L12FKaux.Fstar_contDiffOn hβ hβ1 4).add
      ((h.hscl n τ hτ).reg.forall 4))
    (fun n k hk z θ hz' h0 h1 => h.hsl τ hτ n k hk z θ hz' h0 h1)
    (fun k hk z θ hzθ => h.hjet τ hτ k hk z θ hzθ) hz hj

/-- `D_z L₁₂(F(τ)) = -𝔽K F(τ)`. -/
theorem L12_jet_one {α C₀ S : ℝ} {Φs : Fn} {E : Fn →ₗ[ℝ] Fn} {g : Fam}
    {gn : ℕ → Fam} {Cw CB : ℝ} (h : Stand α C₀ S Φs E g gn Cw CB)
    {τ : ℝ} (hτ : τ ∈ Set.Icc (0:ℝ) S) {z : ℝ} (hz : 0 < z) :
    Work.Spaces.DzIter 1 (fun z _ => Work.Construction.L12 (Prof α g τ) z) z 0
      = -Qm α g τ 0 z := by
  have hder := Work.FTS_RegExport.RXT.Sys.L12FKaux.L12_hasDerivAt (α := α) h.hα h.hα13
    h.hCw (fun n => (h.hscl n τ hτ).reg.forall 4)
    (fun n k hk z θ hz' h0 h1 => h.hbd n τ hτ k hk z θ hz' h0 h1)
    (fun z θ hzθ => h.hconv τ hτ z θ hzθ) hz
  show z * deriv (fun y => Work.Construction.L12 (Prof α g τ) y) z = -Qm α g τ 0 z
  rw [hder.deriv, mul_neg,
    Work.Construction.mul_L12dens_eq_FK (F := Prof α g τ) (z := z) (ne_of_gt hz)]
  rw [Work.FTS_RegExport.RXT.Sys.L12FKaux.Qlim_eq_FK (α := α) h.hα hτ.1 hz]

/-- `D_z² L₁₂(F(τ)) = -D_z 𝔽K F(τ)`. -/
theorem L12_jet_two {α C₀ S : ℝ} {Φs : Fn} {E : Fn →ₗ[ℝ] Fn} {g : Fam}
    {gn : ℕ → Fam} {Cw CB : ℝ} (h : Stand α C₀ S Φs E g gn Cw CB)
    {τ : ℝ} (hτ : τ ∈ Set.Icc (0:ℝ) S) {z : ℝ} (hz : 0 < z) :
    Work.Spaces.DzIter 2 (fun z _ => Work.Construction.L12 (Prof α g τ) z) z 0
      = -Qm α g τ 1 z := by
  have hβ : 0 < Work.FTS.Regularity.pExp α := Work.FTS.Regularity.pExp_pos h.hα
  have hβ1 : Work.FTS.Regularity.pExp α ≤ 1 := Work.FTS.Regularity.pExp_le_one h.hα13
  have hev : (fun y => Work.Spaces.DzIter 1
      (fun z _ => Work.Construction.L12 (Prof α g τ) z) y 0)
      =ᶠ[𝓝 z] fun y => -Qm α g τ 0 y := by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with y hy
    exact L12_jet_one h hτ hy
  have hd : HasDerivAt (fun y => -Qm α g τ 0 y) (-(Qm α g τ 1 z / z)) z :=
    (Work.FTS_RegExport.RXT.Sys.L12FKaux.Qlim_hasDerivAt_1 (α := α) h.hα h.hα13
      h.hCw h.hCB (fun n => (h.hscl n τ hτ).reg.forall 4)
      (fun n k hk z θ hz' h0 h1 => h.hbd n τ hτ k hk z θ hz' h0 h1)
      (fun n => (Work.FTS_RegExport.RXT.Sys.L12FKaux.Fstar_contDiffOn hβ hβ1 4).add
        ((h.hscl n τ hτ).reg.forall 4))
      (fun n k hk z θ hz' h0 h1 => h.hsl τ hτ n k hk z θ hz' h0 h1)
      (fun k hk z θ hzθ => h.hjet τ hτ k hk z θ hzθ) hz).neg
  show z * deriv (fun y => Work.Spaces.DzIter 1
    (fun z _ => Work.Construction.L12 (Prof α g τ) z) y 0) z = -Qm α g τ 1 z
  rw [hev.deriv_eq, hd.deriv, mul_neg, neg_inj]
  field_simp

/-- **Uniform `z`-Lipschitz bound of the `L₁₂` family on a compact box.** -/
theorem L12_z_lip {α C₀ S : ℝ} {Φs : Fn} {E : Fn →ₗ[ℝ] Fn} {g : Fam}
    {gn : ℕ → Fam} {Cw CB : ℝ} (h : Stand α C₀ S Φs E g gn Cw CB)
    {a b : ℝ} (ha : 0 < a) (_hab : a ≤ b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ τ ∈ Set.Icc (0:ℝ) S, ∀ z ∈ Set.Icc a b, ∀ z' ∈ Set.Icc a b,
      |Work.Construction.L12 (Prof α g τ) z - Work.Construction.L12 (Prof α g τ) z'|
        ≤ C * |z - z'| := by
  have hπ : (0 : ℝ) ≤ 3 * (Real.pi / 2) := by positivity
  refine ⟨3 * (Real.pi / 2) * CB * 3 / a, ?_, ?_⟩
  · exact div_nonneg (by nlinarith [h.hCB, Real.pi_pos]) ha.le
  · intro τ hτ z hz z' hz'
    have hβ : 0 < Work.FTS.Regularity.pExp α := Work.FTS.Regularity.pExp_pos h.hα
    have hβ1 : Work.FTS.Regularity.pExp α ≤ 1 := Work.FTS.Regularity.pExp_le_one h.hα13
    have hderiv : ∀ w ∈ Set.Icc a b,
        deriv (fun y => Work.Construction.L12 (Prof α g τ) y) w
          = -(Work.Construction.L12dens (Prof α g τ) w) := by
      intro w hw
      exact (Work.FTS_RegExport.RXT.Sys.L12FKaux.L12_hasDerivAt (α := α) h.hα h.hα13
        h.hCw (fun n => (h.hscl n τ hτ).reg.forall 4)
        (fun n k hk z θ hz' h0 h1 => h.hbd n τ hτ k hk z θ hz' h0 h1)
        (fun z θ hzθ => h.hconv τ hτ z θ hzθ) (lt_of_lt_of_le ha hw.1)).deriv
    have hbd : ∀ w ∈ Set.Icc a b,
        ‖deriv (fun y => Work.Construction.L12 (Prof α g τ) y) w‖
          ≤ 3 * (Real.pi / 2) * CB * 3 / a := by
      intro w hw
      have hw0 : 0 < w := lt_of_lt_of_le ha hw.1
      have hQ : |Qm α g τ 0 w| ≤ 3 * (Real.pi / 2) * CB :=
        Work.FTS_RegExport.RXT.Sys.L12FKaux.Qlim_bound (α := α) h.hα h.hα13
          h.hCw h.hCB (fun n => (h.hscl n τ hτ).reg.forall 4)
          (fun n k hk z θ hz' h0 h1 => h.hbd n τ hτ k hk z θ hz' h0 h1)
          (fun n => (Work.FTS_RegExport.RXT.Sys.L12FKaux.Fstar_contDiffOn hβ hβ1 4).add
            ((h.hscl n τ hτ).reg.forall 4))
          (fun n k hk z θ hz' h0 h1 => h.hsl τ hτ n k hk z θ hz' h0 h1)
          (fun k hk z θ hzθ => h.hjet τ hτ k hk z θ hzθ) (k := 0) (by norm_num) hw0
      have hFK : Work.Construction.FK (Prof α g τ) w = Qm α g τ 0 w :=
        Work.FTS_RegExport.RXT.Sys.L12FKaux.Qlim_eq_FK (α := α) h.hα hτ.1 hw0
      have hdens : Work.Construction.L12dens (Prof α g τ) w
          = Work.Construction.FK (Prof α g τ) w / w := by
        rw [eq_div_iff (ne_of_gt hw0), mul_comm]
        exact Work.Construction.mul_L12dens_eq_FK (ne_of_gt hw0)
      rw [hderiv w hw, Real.norm_eq_abs, abs_neg, hdens, hFK, abs_div, abs_of_pos hw0]
      rw [div_le_div_iff₀ hw0 ha]
      have h1 : |Qm α g τ 0 w| * a ≤ (3 * (Real.pi / 2) * CB) * a :=
        mul_le_mul_of_nonneg_right hQ ha.le
      have h2 : (3 * (Real.pi / 2) * CB) * a ≤ (3 * (Real.pi / 2) * CB) * w :=
        mul_le_mul_of_nonneg_left hw.1 (by nlinarith [h.hCB, Real.pi_pos])
      have h3 : (3 * (Real.pi / 2) * CB) * w ≤ (3 * (Real.pi / 2) * CB * 3) * w :=
        mul_le_mul_of_nonneg_right (by nlinarith [h.hCB, Real.pi_pos]) hw0.le
      linarith [h1, h2, h3]
    have hdiff : ∀ x ∈ Set.Icc a b, DifferentiableAt ℝ
        (fun y => Work.Construction.L12 (Prof α g τ) y) x := fun x hx =>
      (Work.FTS_RegExport.RXT.Sys.L12FKaux.L12_hasDerivAt (α := α) h.hα h.hα13
        h.hCw (fun n => (h.hscl n τ hτ).reg.forall 4)
        (fun n k hk z θ hz' h0 h1 => h.hbd n τ hτ k hk z θ hz' h0 h1)
        (fun z θ hzθ => h.hconv τ hτ z θ hzθ) (lt_of_lt_of_le ha hx.1)).differentiableAt
    have := Convex.norm_image_sub_le_of_norm_deriv_le (𝕜 := ℝ) (f := fun y =>
        Work.Construction.L12 (Prof α g τ) y) (s := Set.Icc a b) hdiff hbd
      (convex_Icc a b) hz hz'
    simpa only [Real.norm_eq_abs, abs_sub_comm] using this


/-! ## Temporary axioms standing for the delegated lemmas (development only) -/

/-- Joint continuity of the angular moments. -/
theorem Qlim_jointCont {α C₀ : ℝ} {Φs : Fn} {E : Fn →ₗ[ℝ] Fn} {g : Fam}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hA : Work.FTS.FinalV2.LimApprox (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    {S : ℝ} (hS : 0 < S) :
    ∀ k : ℕ, k ≤ 2 → ContinuousOn (fun p : ℝ × ℝ => Qm α g p.2 k p.1)
      (Set.Ioi (0:ℝ) ×ˢ Set.Icc (0:ℝ) S) := by
  intro k hk
  refine continuousOn_prod_of_box_lip (fun a b ha hab => ?_)
  obtain ⟨Cz, hCz0, hCz⟩ := QlimZLipBox hα hα13 hA S hS a b ha hab
  obtain ⟨Ct, hCt0, hCt⟩ := QlimTauLipW hα hα13 hA S hS
  refine ⟨Cz + Ct, by linarith, ?_⟩
  intro τ hτ τ' hτ' z hz z' hz'
  have hz0 : 0 < z' := lt_of_lt_of_le ha hz'.1
  have h1 : |Qm α g τ k z - Qm α g τ k z'| ≤ Cz * |z - z'| := hCz k hk τ hτ z hz z' hz'
  have h2 : |Qm α g τ k z' - Qm α g τ' k z'| ≤ Ct * SWe z' * |τ - τ'| :=
    hCt k hk τ hτ τ' hτ' z' hz0
  have hSW : SWe z' ≤ 1 := Work.FTS_RegExport.RXT.Sys.L12FKaux.SW_le_one hz0
  calc |Qm α g τ k z - Qm α g τ' k z'|
      ≤ |Qm α g τ k z - Qm α g τ k z'| + |Qm α g τ k z' - Qm α g τ' k z'| :=
        abs_sub_le _ _ _
    _ ≤ Cz * |z - z'| + Ct * SWe z' * |τ - τ'| := add_le_add h1 h2
    _ ≤ Cz * |z - z'| + Ct * |τ - τ'| := by
        refine add_le_add le_rfl ?_
        have h1 : SWe z' * |τ - τ'| ≤ 1 * |τ - τ'| :=
          mul_le_mul_of_nonneg_right hSW (abs_nonneg _)
        calc Ct * SWe z' * |τ - τ'| = Ct * (SWe z' * |τ - τ'|) := by ring
          _ ≤ Ct * (1 * |τ - τ'|) := mul_le_mul_of_nonneg_left h1 hCt0
          _ = Ct * |τ - τ'| := by ring
    _ ≤ (Cz + Ct) * (|z - z'| + |τ - τ'|) := by
        nlinarith [hCz0, hCt0, abs_nonneg (z - z'), abs_nonneg (τ - τ'),
          mul_nonneg hCz0 (abs_nonneg (τ - τ')), mul_nonneg hCt0 (abs_nonneg (z - z'))]

/-- Joint continuity of `L₁₂(F(τ))`. -/
theorem L12_jointCont {α C₀ : ℝ} {Φs : Fn} {E : Fn →ₗ[ℝ] Fn} {g : Fam}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hA : Work.FTS.FinalV2.LimApprox (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    {S : ℝ} (hS : 0 < S) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Construction.L12 (Prof α g p.2) p.1)
      (Set.Ioi (0:ℝ) ×ˢ Set.Icc (0:ℝ) S) := by
  obtain ⟨gn, Cw, CB, hst⟩ := stand_exists hα hα13 hA
  have hQ : ∃ C : ℝ, 0 ≤ C ∧ ∀ τ ∈ Set.Icc (0:ℝ) S, ∀ τ' ∈ Set.Icc (0:ℝ) S,
      ∀ r : ℝ, 0 < r →
        |Work.Construction.L12dens (Prof α g τ) r
          - Work.Construction.L12dens (Prof α g τ') r|
        ≤ C * (Work.FTS_RegExport.RXT.Sys.L12FKaux.SW r / r) * |τ - τ'| := by
    obtain ⟨C, hC0, hC⟩ := QlimTauLipW hα hα13 hA S hS
    refine ⟨C, hC0, ?_⟩
    intro τ hτ τ' hτ' r hr
    have e1 : Work.Construction.L12dens (Prof α g τ) r
        = Work.Construction.FK (Prof α g τ) r / r := by
      rw [eq_div_iff (ne_of_gt hr), mul_comm]
      exact Work.Construction.mul_L12dens_eq_FK (ne_of_gt hr)
    have e2 : Work.Construction.L12dens (Prof α g τ') r
        = Work.Construction.FK (Prof α g τ') r / r := by
      rw [eq_div_iff (ne_of_gt hr), mul_comm]
      exact Work.Construction.mul_L12dens_eq_FK (ne_of_gt hr)
    have f1 : Work.Construction.FK (Prof α g τ) r = Qm α g τ 0 r :=
      Work.FTS_RegExport.RXT.Sys.L12FKaux.Qlim_eq_FK (α := α) hα hτ.1 hr
    have f2 : Work.Construction.FK (Prof α g τ') r = Qm α g τ' 0 r :=
      Work.FTS_RegExport.RXT.Sys.L12FKaux.Qlim_eq_FK (α := α) hα hτ'.1 hr
    rw [e1, e2, f1, f2, ← sub_div, abs_div, abs_of_pos hr]
    calc |Qm α g τ 0 r - Qm α g τ' 0 r| / r
        ≤ (C * Work.FTS_RegExport.RXT.Sys.L12FKaux.SW r * |τ - τ'|) / r :=
          div_le_div_of_nonneg_right (hC 0 (by norm_num) τ hτ τ' hτ' r hr) hr.le
      _ = C * (Work.FTS_RegExport.RXT.Sys.L12FKaux.SW r / r) * |τ - τ'| := by ring
  have hint := L12densFtauIntegrable hα hα13 hA S hS
  refine continuousOn_prod_of_box_lip (fun a b ha hab => ?_)
  obtain ⟨Ct, hCt0, hCt⟩ := L12FtauTauLip S hS hQ hint a b ha hab
  obtain ⟨Cz, hCz0, hCz⟩ := L12_z_lip hst ha hab
  refine ⟨Cz + Ct, by linarith, ?_⟩
  intro τ hτ τ' hτ' z hz z' hz'
  calc |Work.Construction.L12 (Prof α g τ) z - Work.Construction.L12 (Prof α g τ') z'|
      ≤ |Work.Construction.L12 (Prof α g τ) z - Work.Construction.L12 (Prof α g τ) z'|
        + |Work.Construction.L12 (Prof α g τ) z' - Work.Construction.L12 (Prof α g τ') z'| :=
        abs_sub_le _ _ _
    _ ≤ Cz * |z - z'| + Ct * |τ - τ'| := add_le_add (hCz τ hτ z hz z' hz')
        (hCt τ hτ τ' hτ' z' hz')
    _ ≤ (Cz + Ct) * (|z - z'| + |τ - τ'|) := by
        nlinarith [hCz0, hCt0, abs_nonneg (z - z'), abs_nonneg (τ - τ'),
          mul_nonneg hCz0 (abs_nonneg (τ - τ')), mul_nonneg hCt0 (abs_nonneg (z - z'))]

end L12FKjc

open L12FKjc

theorem L12FKJetsJointCont {α C₀ : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g) :
    ∀ S > 0, ∀ j : ℕ, j ≤ 2 →
      ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.DzIter j
        (fun z (_ : ℝ) => Work.Construction.L12
          (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
            (Work.FTS.RegExportIface.RXT.GR α g) p.2) z) p.1 0)
        (Set.Ioi (0:ℝ) ×ˢ Set.Icc (0:ℝ) S) ∧
      ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.DzIter j
        (fun z (_ : ℝ) => Work.Construction.FK
          (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
            (Work.FTS.RegExportIface.RXT.GR α g) p.2) z) p.1 0)
        (Set.Ioi (0:ℝ) ×ˢ Set.Icc (0:ℝ) S) := by
  intro S hS j hj
  have hA : Work.FTS.FinalV2.LimApprox (Work.FTS.Regularity.pExp α) C₀ Φs E g := hOK.2
  obtain ⟨gn, Cw, CB, hst⟩ := stand_exists hα hα13 hA
  have hQlim := Qlim_jointCont hα hα13 hA hS
  have hL12 := L12_jointCont hα hα13 hA hS
  refine ⟨?_, ?_⟩
  · rcases (show j = 0 ∨ j = 1 ∨ j = 2 by omega) with rfl | rfl | rfl
    · refine hL12.congr (fun p _ => ?_)
      simp only [Work.Spaces.DzIter_zero]
    · refine ((hQlim 0 (by norm_num)).neg).congr (fun p hp => ?_)
      exact L12_jet_one hst hp.2 hp.1
    · refine ((hQlim 1 (by norm_num)).neg).congr (fun p hp => ?_)
      exact L12_jet_two hst hp.2 hp.1
  · refine (hQlim j hj).congr (fun p hp => ?_)
    exact FK_jets_eq hst hp.2 hj hp.1

end

end Work.FTS_RegExport.RXT0
