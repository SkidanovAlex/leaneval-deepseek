import Mathlib
import Submission.Work.Diff.Dim2.Lib
import Submission.Work.Diff.Dim2.reeb_field2
import Submission.Work.Diff.Dim2.reeb_field_bound

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.Dim2

-- NOTE for the prover: this is `Work.Diff.Dim2.reeb_field2` (in `Diff/Dim2/reeb_field2`) with the
-- extra clause `∀ y, ‖V y‖ ≤ 1`.  Copy the proof of `reeb_field2` verbatim and replace the middle
-- ascent field `W` by a positive multiple `W' := c • W` with `c` so small that `‖W'‖ ≤ 1`
-- (use the proved `Work.Diff.Dim2.reeb_field_bound` for a bound `C ≥ ‖W‖`; `IsAscentAt` is invariant
-- under multiplication by a positive scalar, cf. `Submission.GSField`).  Then
-- `V = ρ₁ ∇f + ρ₂ W' - ρ₃ ∇g` satisfies `‖V y‖ ≤ ρ₁ + ρ₂ + ρ₃`, and although
-- `ρ₁ + ρ₂ + ρ₃ = 1 + ρ₁ρ₃`, the triangle inequality `D ≤ f y + g y` (`htri`, as in the proof of
-- `reeb_field2`) gives `ρ₁ρ₃ = 0`: `ρ₁ρ₃ > 0` forces `f y < 7a/4` and `g y < dc ≤ 3γ`, whence
-- `f y + g y < 7a/4 + 3γ ≤ 7a/4 + 5γ/2 < D` (hsep2), a contradiction.  Hence `‖V y‖ ≤ 1`.
-- (Both reviewers verified the statement and this route.  Beware: `‖∇f‖ = ‖∇g‖ = 1` on the supports
-- comes from the eikonal `Work.Diff.C.rgrad_rdist_eikonal` + `hsmP`/`hsmQ`.)
open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

theorem reeb_field3
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
      [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M] [RegularSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [ContMDiffCovariantDerivative cov ∞]
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) (hpinch : QuarterPinched cov)
    {p q : M} {D v a γ : ℝ}
    (ha : 0 < a) (hg : 0 < γ) (hv : 0 < v)
    (h2a : 2 * a < v) (h2g : 2 * γ < v)
    (hDGt : Real.pi / 2 < D) (hDLt : D < Real.pi)
    (hdiam : ∀ r s : M, Manifold.riemannianEDist I r s ≤ ENNReal.ofReal D)
    (hpq : Manifold.riemannianEDist I p q = ENNReal.ofReal D)
    (hsmP : ∀ y : M, 0 < Work.Diff.C.rdist (I := I) (M := M) p y →
      Work.Diff.C.rdist (I := I) (M := M) p y < v →
      CMDiffAt ∞ (fun z : M ↦ Work.Diff.C.rdist (I := I) (M := M) p z) y)
    (hsmQ : ∀ y : M, 0 < Work.Diff.C.rdist (I := I) (M := M) q y →
      Work.Diff.C.rdist (I := I) (M := M) q y < v →
      CMDiffAt ∞ (fun z : M ↦ Work.Diff.C.rdist (I := I) (M := M) q z) y)
    (hsep1 : 3 * a / 2 + 3 * γ < D) (hsep2 : 7 * a / 4 + 5 * γ / 2 < D)
    (hsep3 : 3 * γ < D - Real.pi / 2) (hsep4 : 5 * γ / 2 < v)
    (hsep5 : 3 * γ < Real.pi / 2) :
    ∃ V : (y : M) → TangentSpace I y,
      (ContMDiff I (I.prod (modelWithCornersSelf ℝ E)) ∞
        (fun y : M => (⟨y, V y⟩ : Bundle.TotalSpace E (TangentSpace I)))) ∧
      (∀ y : M, ‖V y‖ ≤ 1) ∧
      (∀ y : M, a / 4 ≤ Work.Diff.C.rdist (I := I) (M := M) p y →
        Work.Diff.C.rdist (I := I) (M := M) p y ≤ 3 * a / 2 →
        V y = Work.Diff.C.rgrad (I := I) (M := M)
          (fun z : M ↦ Work.Diff.C.rdist (I := I) (M := M) p z) y) ∧
      (∀ y : M, γ / 4 ≤ Work.Diff.C.rdist (I := I) (M := M) q y →
        Work.Diff.C.rdist (I := I) (M := M) q y ≤ 5 * γ / 2 →
        V y = - Work.Diff.C.rgrad (I := I) (M := M)
          (fun z : M ↦ Work.Diff.C.rdist (I := I) (M := M) q z) y) ∧
      (∀ y : M, a / 4 ≤ Work.Diff.C.rdist (I := I) (M := M) p y →
        γ / 8 < Work.Diff.C.rdist (I := I) (M := M) q y →
        Submission.GSField.IsAscentAt hmet p y (V y)) ∧
      (∀ y : M, a / 4 ≤ Work.Diff.C.rdist (I := I) (M := M) p y →
        γ / 8 ≤ Work.Diff.C.rdist (I := I) (M := M) q y → V y ≠ 0) := by
  classical
  -- ## numerical facts
  have hDnn : 0 ≤ D := le_trans (by linarith [Real.pi_pos]) hDGt.le
  have ha8 : 0 < a / 8 := by linarith
  have hg8 : 0 < γ / 8 := by linarith
  have hA1 : a / 8 < a / 4 := by linarith
  have hA2 : 3 * a / 2 < 7 * a / 4 := by linarith
  have hA4 : 7 * a / 4 < v := by linarith
  have hG1 : γ / 8 < γ / 4 := by linarith
  have hG2 : 5 * γ / 2 < 3 * γ := by linarith
  -- the cut-off of the `q`-window: purely above `5γ/2`, below `3γ` (so that the case
  -- `f ≤ 3a/2` forces the `q`-weight to vanish), below `D - 7a/4` (so that the two tail
  -- windows can never both be non-zero: this is where `hsep2` is used) and below `v`
  set dc : ℝ := min (min (3 * γ) (D - 7 * a / 4)) ((v + 5 * γ / 2) / 2) with hdcdef
  have hdc_gt : 5 * γ / 2 < dc := by
    rw [hdcdef]
    exact lt_min (lt_min hG2 (by linarith [hsep2])) (by linarith [hsep4])
  have hdc_le3 : dc ≤ 3 * γ := le_trans (min_le_left _ _) (min_le_left _ _)
  have hdc_leD : dc ≤ D - 7 * a / 4 := le_trans (min_le_left _ _) (min_le_right _ _)
  have hdc_lt_v : dc < v :=
    lt_of_le_of_lt (min_le_right _ _) (by linarith [hsep4])
  -- ## the two distance functions
  set f : M → ℝ := fun y : M => Work.Diff.C.rdist (I := I) (M := M) p y with hfdef
  set g : M → ℝ := fun y : M => Work.Diff.C.rdist (I := I) (M := M) q y with hgdef
  have hfcont : Continuous f := Work.Diff.C.rdist_continuous (I := I) (M := M) p
  have hgcont : Continuous g := Work.Diff.C.rdist_continuous (I := I) (M := M) q
  have hfp : f p = 0 := by
    rw [hfdef]; simp [Work.Diff.C.rdist, Manifold.riemannianEDist_self]
  have hgq : g q = 0 := by
    rw [hgdef]; simp [Work.Diff.C.rdist, Manifold.riemannianEDist_self]
  have hsmPf : ∀ y : M, 0 < f y → f y < v → CMDiffAt ∞ f y := fun y h1 h2 => hsmP y h1 h2
  have hsmQg : ∀ y : M, 0 < g y → g y < v → CMDiffAt ∞ g y := fun y h1 h2 => hsmQ y h1 h2
  -- ## the triangle inequality `D ≤ f + g`
  have htri : ∀ y : M, D ≤ f y + g y := by
    intro y
    change D ≤ (Manifold.riemannianEDist I p y).toReal
      + (Manifold.riemannianEDist I q y).toReal
    have he1 : Manifold.riemannianEDist I p y ≠ ⊤ :=
      ne_of_lt (lt_of_le_of_lt (hdiam p y) ENNReal.ofReal_lt_top)
    have he2 : Manifold.riemannianEDist I y q ≠ ⊤ :=
      ne_of_lt (lt_of_le_of_lt (hdiam y q) ENNReal.ofReal_lt_top)
    have h3 := Manifold.riemannianEDist_triangle (I := I) (x := p) (y := y) (z := q)
    rw [hpq] at h3
    have h4 := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨he1, he2⟩) h3
    rw [ENNReal.toReal_add he1 he2, ENNReal.toReal_ofReal hDnn] at h4
    have h5 : (Manifold.riemannianEDist I y q).toReal
        = (Manifold.riemannianEDist I q y).toReal := by
      rw [Manifold.riemannianEDist_comm]
    rw [h5] at h4
    exact h4
  -- ## the windows
  set wp : ℝ → ℝ := win (a / 8) (a / 4) (3 * a / 2) (7 * a / 4) with hwpdef
  set wq : ℝ → ℝ := win (γ / 8) (γ / 4) (5 * γ / 2) dc with hwqdef
  have hwpsm : ContDiff ℝ ∞ wp := by rw [hwpdef]; exact win_smooth hA1 hA2
  have hwqsm : ContDiff ℝ ∞ wq := by rw [hwqdef]; exact win_smooth hG1 hdc_gt
  have hwp_nn : ∀ x : ℝ, 0 ≤ wp x := by intro x; rw [hwpdef]; exact win_nonneg x
  have hwp_le1 : ∀ x : ℝ, wp x ≤ 1 := by intro x; rw [hwpdef]; exact win_le_one x
  have hwq_nn : ∀ x : ℝ, 0 ≤ wq x := by intro x; rw [hwqdef]; exact win_nonneg x
  have hwq_le1 : ∀ x : ℝ, wq x ≤ 1 := by intro x; rw [hwqdef]; exact win_le_one x
  have hwp_le : ∀ x : ℝ, x ≤ a / 8 → wp x = 0 := by
    intro x hx; rw [hwpdef]; exact win_eq_zero_of_le hA1 hx
  have hwp_ge : ∀ x : ℝ, 7 * a / 4 ≤ x → wp x = 0 := by
    intro x hx; rw [hwpdef]; exact win_eq_zero_of_ge hA2 hx
  have hwp_one : ∀ x : ℝ, a / 4 ≤ x → x ≤ 3 * a / 2 → wp x = 1 := by
    intro x h1 h2; rw [hwpdef]; exact win_eq_one hA1 h1 h2 hA2
  have hwq_le : ∀ x : ℝ, x ≤ γ / 8 → wq x = 0 := by
    intro x hx; rw [hwqdef]; exact win_eq_zero_of_le hG1 hx
  have hwq_ge : ∀ x : ℝ, dc ≤ x → wq x = 0 := by
    intro x hx; rw [hwqdef]; exact win_eq_zero_of_ge hdc_gt hx
  have hwq_one : ∀ x : ℝ, γ / 4 ≤ x → x ≤ 5 * γ / 2 → wq x = 1 := by
    intro x h1 h2; rw [hwqdef]; exact win_eq_one hG1 h1 h2 hdc_gt
  have hwp_le' : ∀ x : ℝ, x ≤ a / 8 → wp x = wp (a / 8) :=
    fun x hx => by rw [hwp_le x hx, hwp_le (a / 8) le_rfl]
  have hwp_ge' : ∀ x : ℝ, 7 * a / 4 ≤ x → wp x = wp (7 * a / 4) :=
    fun x hx => by rw [hwp_ge x hx, hwp_ge (7 * a / 4) le_rfl]
  have hwq_le' : ∀ x : ℝ, x ≤ γ / 8 → wq x = wq (γ / 8) :=
    fun x hx => by rw [hwq_le x hx, hwq_le (γ / 8) le_rfl]
  have hwq_ge' : ∀ x : ℝ, dc ≤ x → wq x = wq dc :=
    fun x hx => by rw [hwq_ge x hx, hwq_ge dc le_rfl]
  -- ## the compact middle region and the ascent field `W` on it
  set t : Set M := {y : M | 3 * a / 2 ≤ f y ∧ γ / 8 ≤ g y} with htdef
  have htc : IsCompact t := by
    rw [htdef]
    exact ((isClosed_le continuous_const hfcont).inter
      (isClosed_le continuous_const hgcont)).isCompact
  have htp : ∀ x ∈ t, x ≠ p := by
    intro x hx hxp
    rw [htdef] at hx
    have h1 : 3 * a / 2 ≤ f x := hx.1
    rw [hxp, hfp] at h1
    linarith
  have htq : ∀ x ∈ t, x ≠ q := by
    intro x hx hxq
    rw [htdef] at hx
    have h1 : γ / 8 ≤ g x := hx.2
    rw [hxq, hgq] at h1
    linarith
  obtain ⟨W, hWasc, -, hWsm⟩ :=
    Submission.GSGlobal2.exists_continuous_ascent_field_of_diam (cov := cov) hmet htor hpinch
      hdiam hDGt hDLt hpq htc htp htq
  -- ## a small positive multiple of `W` which is bounded by `1`
  obtain ⟨C, hCnn, hCb⟩ := reeb_field_bound (I := I) (M := M) (V := W) hWsm
  have hC1pos : 0 < C + 1 := by linarith
  set c : ℝ := 1 / (C + 1) with hcdef
  have hcinv : c = (C + 1)⁻¹ := by rw [hcdef]; ring
  have hcpos : 0 < c := by rw [hcinv]; positivity
  have hcC : c * (C + 1) = 1 := by
    rw [hcinv]; exact inv_mul_cancel₀ (ne_of_gt hC1pos)
  have hcCle : c * C ≤ 1 := by nlinarith [hcC, hcpos.le]
  have hWssm : CMDiff ∞ (T% (c • W)) := hWsm.const_smul_section (a := c)
  have hWsasc : ∀ y ∈ t, Submission.GSField.IsAscentAt hmet p y (c • W y) :=
    fun y hy => Submission.GSField.isAscentAt_smul (cov := cov) (hmet := hmet) (p := p)
      (x := y) (v := W y) (hWasc y hy) hcpos
  have hWsnorm : ∀ y : M, ‖c • W y‖ ≤ 1 := by
    intro y
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hcpos]
    exact le_trans (mul_le_mul_of_nonneg_left (hCb y) hcpos.le) hcCle
  -- ## the weights
  set ρ₁ : M → ℝ := fun y => wp (f y) with hρ₁def
  set ρ₃ : M → ℝ := fun y => wq (g y) with hρ₃def
  set ρ₂ : M → ℝ := fun y => (1 - ρ₁ y) * (1 - ρ₃ y) with hρ₂def
  have hρ₁sm : CMDiff ∞ ρ₁ := by
    rw [hρ₁def]
    exact reeb_window_comp (f := f) (c := a / 8) (d := 7 * a / 4) ha8 hA4 hfcont hsmPf hwpsm
      hwp_le' hwp_ge'
  have hρ₃sm : CMDiff ∞ ρ₃ := by
    rw [hρ₃def]
    exact reeb_window_comp (f := g) (c := γ / 8) (d := dc) hg8 hdc_lt_v hgcont hsmQg hwqsm
      hwq_le' hwq_ge'
  have hρ₂sm : CMDiff ∞ ρ₂ := by
    rw [hρ₂def]
    exact ((contMDiff_const (c := (1 : ℝ))).sub hρ₁sm).mul
      ((contMDiff_const (c := (1 : ℝ))).sub hρ₃sm)
  -- ## the three summands and the field `V`
  set F1 : (y : M) → TangentSpace I y :=
    fun y => ρ₁ y • Work.Diff.C.rgrad (I := I) (M := M) f y with hF1def
  set F2 : (y : M) → TangentSpace I y :=
    fun y => ρ₃ y • Work.Diff.C.rgrad (I := I) (M := M) g y with hF2def
  set F3 : (y : M) → TangentSpace I y := fun y => ρ₂ y • (c • W y) with hF3def
  set V : (y : M) → TangentSpace I y := F1 + (-F2) + F3 with hVdef
  have hF1sm : CMDiff ∞ (T% F1) := by
    rw [hF1def]
    exact reeb_window_smul_rgrad (f := f) (c := a / 8) (d := 7 * a / 4) ha8 hA4 hfcont hsmPf
      hwpsm hwp_le hwp_ge
  have hF2sm : CMDiff ∞ (T% F2) := by
    rw [hF2def]
    exact reeb_window_smul_rgrad (f := g) (c := γ / 8) (d := dc) hg8 hdc_lt_v hgcont hsmQg
      hwqsm hwq_le hwq_ge
  have hF3sm : CMDiff ∞ (T% F3) := by
    rw [hF3def]
    exact hρ₂sm.smul_section hWssm
  have hVsm : CMDiff ∞ (T% V) := by
    rw [hVdef]
    exact (hF1sm.add_section hF2sm.neg_section).add_section hF3sm
  -- ## the ascent property on the closed slab `{a/4 ≤ f} ∩ {γ/8 ≤ g}`
  have hascC : ∀ y : M, a / 4 ≤ f y → γ / 8 ≤ g y →
      Submission.GSField.IsAscentAt hmet p y (V y) := by
    intro y hfy hgy
    by_cases hcase : f y ≤ 3 * a / 2
    · -- ### Case 1: `f y ≤ 3a/2`; then the triangle inequality forces `g y > 3γ ≥ dc`
      have hgy3 : 3 * γ < g y := by
        have h := htri y
        linarith
      have hρ₁ : ρ₁ y = 1 := by rw [hρ₁def]; exact hwp_one (f y) hfy hcase
      have hρ₃ : ρ₃ y = 0 := by rw [hρ₃def]; exact hwq_ge (g y) (le_trans hdc_le3 hgy3.le)
      have hρ₂ : ρ₂ y = 0 := by rw [hρ₂def]; simp [hρ₁, hρ₃]
      have hVy : V y = Work.Diff.C.rgrad (I := I) (M := M) f y := by
        rw [hVdef]
        simp only [Pi.add_apply, Pi.neg_apply, hF1def, hF2def, hF3def, hρ₁, hρ₃, hρ₂]
        simp
      rw [hVy]
      exact Work.Diff.Dim2.isAscentAt_rgrad_rdist (cov := cov) hmet (by linarith)
        (hsmPf y (by linarith) (by linarith [hcase, hA4]))
    · -- ### Case 2: `3a/2 < f y`; `y` lies in `t`, so all three summands are ascent
      have hf3 : 3 * a / 2 < f y := not_le.mp hcase
      have hgpos : 0 < g y := by linarith
      have hyt : y ∈ t := by
        rw [htdef]
        exact ⟨le_of_lt hf3, hgy⟩
      have hWasc_y : Submission.GSField.IsAscentAt hmet p y (c • W y) := hWsasc y hyt
      have hρ₁nn : 0 ≤ ρ₁ y := by rw [hρ₁def]; exact hwp_nn (f y)
      have hρ₃nn : 0 ≤ ρ₃ y := by rw [hρ₃def]; exact hwq_nn (g y)
      have hρ₁le1 : ρ₁ y ≤ 1 := by rw [hρ₁def]; exact hwp_le1 (f y)
      have hρ₃le1 : ρ₃ y ≤ 1 := by rw [hρ₃def]; exact hwq_le1 (g y)
      have hρ₂nn : 0 ≤ ρ₂ y := by
        rw [hρ₂def]
        exact mul_nonneg (by linarith) (by linarith)
      have hsum : 0 < ρ₁ y + ρ₂ y + ρ₃ y := by
        have he : ρ₁ y + ρ₂ y + ρ₃ y = 1 + ρ₁ y * ρ₃ y := by
          rw [hρ₂def]; ring
        rw [he]
        nlinarith [hρ₁nn, hρ₃nn]
      have hv1 : ρ₁ y ≠ 0 → Submission.GSField.IsAscentAt hmet p y
          (Work.Diff.C.rgrad (I := I) (M := M) f y) := by
        intro hne
        have hfw : a / 8 < f y := by
          by_contra hcon
          exact hne (by rw [hρ₁def]; exact hwp_le (f y) (le_of_not_gt hcon))
        have hfv : f y < 7 * a / 4 := by
          by_contra hcon
          exact hne (by rw [hρ₁def]; exact hwp_ge (f y) (le_of_not_gt hcon))
        exact Work.Diff.Dim2.isAscentAt_rgrad_rdist (cov := cov) hmet (by linarith)
          (hsmPf y (by linarith) (by linarith [hfv, hA4]))
      have hv3 : ρ₃ y ≠ 0 → Submission.GSField.IsAscentAt hmet p y
          (- Work.Diff.C.rgrad (I := I) (M := M) g y) := by
        intro hne
        have hgw : γ / 8 < g y := by
          by_contra hcon
          exact hne (by rw [hρ₃def]; exact hwq_le (g y) (le_of_not_gt hcon))
        have hgdc : g y < dc := by
          by_contra hcon
          exact hne (by rw [hρ₃def]; exact hwq_ge (g y) (le_of_not_gt hcon))
        have hgy3 : g y < 3 * γ := lt_of_lt_of_le hgdc hdc_le3
        have hfπ : Real.pi / 2 < f y := by
          have h := htri y
          linarith
        exact negRgradQ_ascent (cov := cov) hmet htor hpinch hDGt hDLt hdiam hpq hgpos hfπ
          (hsmQg y hgpos (lt_of_lt_of_le hgdc hdc_lt_v.le))
      have hthree := isAscentAt_smul_add_three (cov := cov) (hmet := hmet) (p := p) (x := y)
        (v := Work.Diff.C.rgrad (I := I) (M := M) f y) (w := c • W y)
        (z := - Work.Diff.C.rgrad (I := I) (M := M) g y)
        (α := ρ₁ y) (β := ρ₂ y) (δ := ρ₃ y) hρ₁nn hρ₂nn hρ₃nn hsum hv1
        (fun _ => hWasc_y) hv3
      have hVy : V y = ρ₁ y • Work.Diff.C.rgrad (I := I) (M := M) f y + ρ₂ y • (c • W y)
          + ρ₃ y • (- Work.Diff.C.rgrad (I := I) (M := M) g y) := by
        rw [hVdef]
        simp only [Pi.add_apply, Pi.neg_apply, hF1def, hF2def, hF3def]
        rw [smul_neg]
        abel
      rw [hVy]
      exact hthree
  refine ⟨V, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show ContMDiff I (I.prod (modelWithCornersSelf ℝ E)) ∞
      (fun y : M => (⟨y, V y⟩ : Bundle.TotalSpace E (TangentSpace I)))
    exact hVsm
  · -- ## clause: `‖V y‖ ≤ 1` everywhere
    intro y
    have hρ1nn : 0 ≤ ρ₁ y := by rw [hρ₁def]; exact hwp_nn (f y)
    have hρ3nn : 0 ≤ ρ₃ y := by rw [hρ₃def]; exact hwq_nn (g y)
    have hρ1le1 : ρ₁ y ≤ 1 := by rw [hρ₁def]; exact hwp_le1 (f y)
    have hρ3le1 : ρ₃ y ≤ 1 := by rw [hρ₃def]; exact hwq_le1 (g y)
    have hρ2nn : 0 ≤ ρ₂ y := by
      rw [hρ₂def]; exact mul_nonneg (by linarith) (by linarith)
    -- the product of the two outer weights vanishes
    have hprod : ρ₁ y * ρ₃ y = 0 := by
      by_contra hne
      have h1 : ρ₁ y ≠ 0 := fun h => hne (by rw [h, zero_mul])
      have h3 : ρ₃ y ≠ 0 := fun h => hne (by rw [h, mul_zero])
      have hf_gt : a / 8 < f y :=
        lt_of_not_ge (fun hle => h1 (by rw [hρ₁def]; exact hwp_le (f y) hle))
      have hf_lt : f y < 7 * a / 4 :=
        lt_of_not_ge (fun hle => h1 (by rw [hρ₁def]; exact hwp_ge (f y) hle))
      have hg_gt : γ / 8 < g y :=
        lt_of_not_ge (fun hle => h3 (by rw [hρ₃def]; exact hwq_le (g y) hle))
      have hg_lt : g y < dc :=
        lt_of_not_ge (fun hle => h3 (by rw [hρ₃def]; exact hwq_ge (g y) hle))
      have h := htri y
      linarith
    have hsum : ρ₁ y + ρ₂ y + ρ₃ y = 1 := by
      have he : ρ₁ y + ρ₂ y + ρ₃ y = 1 + ρ₁ y * ρ₃ y := by rw [hρ₂def]; ring
      rw [he, hprod, add_zero]
    have hterm1 : ‖ρ₁ y • Work.Diff.C.rgrad (I := I) (M := M) f y‖ ≤ ρ₁ y := by
      by_cases h0 : ρ₁ y = 0
      · rw [h0, zero_smul, norm_zero]
      · have hfpos : 0 < f y := by
          have hle : a / 8 < f y :=
            lt_of_not_ge (fun hle => h0 (by rw [hρ₁def]; exact hwp_le (f y) hle))
          linarith
        have hfv : f y < v := by
          have hlt : f y < 7 * a / 4 :=
            lt_of_not_ge (fun hle => h0 (by rw [hρ₁def]; exact hwp_ge (f y) hle))
          linarith
        have heik := Work.Diff.C.rgrad_rdist_eikonal (I := I) (M := M) (cov := cov) hmet htor
          (q := p) (x := y) (ne_of_gt hfpos)
          (by simpa only [hfdef] using hsmPf y hfpos hfv)
        rw [real_inner_self_eq_norm_sq] at heik
        have hnorm1 : ‖Work.Diff.C.rgrad (I := I) (M := M) f y‖ = 1 := by
          have h2 : ‖Work.Diff.C.rgrad (I := I) (M := M) f y‖ ^ 2 = 1 := by
            simpa only [hfdef] using heik
          nlinarith [norm_nonneg (Work.Diff.C.rgrad (I := I) (M := M) f y)]
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hρ1nn, hnorm1, mul_one]
    have hterm2 : ‖ρ₂ y • (c • W y)‖ ≤ ρ₂ y := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hρ2nn]
      exact mul_le_of_le_one_right hρ2nn (hWsnorm y)
    have hterm3 : ‖ρ₃ y • (- Work.Diff.C.rgrad (I := I) (M := M) g y)‖ ≤ ρ₃ y := by
      by_cases h0 : ρ₃ y = 0
      · rw [h0, zero_smul, norm_zero]
      · have hgpos : 0 < g y := by
          have hle : γ / 8 < g y :=
            lt_of_not_ge (fun hle => h0 (by rw [hρ₃def]; exact hwq_le (g y) hle))
          linarith
        have hgv : g y < v := by
          have hlt : g y < dc :=
            lt_of_not_ge (fun hle => h0 (by rw [hρ₃def]; exact hwq_ge (g y) hle))
          linarith
        have heik := Work.Diff.C.rgrad_rdist_eikonal (I := I) (M := M) (cov := cov) hmet htor
          (q := q) (x := y) (ne_of_gt hgpos)
          (by simpa only [hgdef] using hsmQg y hgpos hgv)
        rw [real_inner_self_eq_norm_sq] at heik
        have hnorm1 : ‖Work.Diff.C.rgrad (I := I) (M := M) g y‖ = 1 := by
          have h2 : ‖Work.Diff.C.rgrad (I := I) (M := M) g y‖ ^ 2 = 1 := by
            simpa only [hgdef] using heik
          nlinarith [norm_nonneg (Work.Diff.C.rgrad (I := I) (M := M) g y)]
        rw [norm_smul, norm_neg, Real.norm_eq_abs, abs_of_nonneg hρ3nn, hnorm1, mul_one]
    have hVy : V y = ρ₁ y • Work.Diff.C.rgrad (I := I) (M := M) f y + ρ₂ y • (c • W y)
        + ρ₃ y • (- Work.Diff.C.rgrad (I := I) (M := M) g y) := by
      rw [hVdef]
      simp only [Pi.add_apply, Pi.neg_apply, hF1def, hF2def, hF3def]
      rw [smul_neg]
      abel
    rw [hVy]
    calc ‖ρ₁ y • Work.Diff.C.rgrad (I := I) (M := M) f y + ρ₂ y • (c • W y)
            + ρ₃ y • (- Work.Diff.C.rgrad (I := I) (M := M) g y)‖
        ≤ ‖ρ₁ y • Work.Diff.C.rgrad (I := I) (M := M) f y + ρ₂ y • (c • W y)‖
            + ‖ρ₃ y • (- Work.Diff.C.rgrad (I := I) (M := M) g y)‖ :=
          norm_add_le _ _
      _ ≤ (‖ρ₁ y • Work.Diff.C.rgrad (I := I) (M := M) f y‖ + ‖ρ₂ y • (c • W y)‖)
            + ‖ρ₃ y • (- Work.Diff.C.rgrad (I := I) (M := M) g y)‖ :=
          add_le_add (norm_add_le _ _) le_rfl
      _ ≤ (ρ₁ y + ρ₂ y) + ρ₃ y := add_le_add (add_le_add hterm1 hterm2) hterm3
      _ = 1 := by rw [hsum]
  · -- ## clause: `V = ∇f` on `{a/4 ≤ f ≤ 3a/2}`
    intro y h1 h2
    have hgy : 3 * γ < g y := by
      have h := htri y
      linarith
    have hρ₁ : ρ₁ y = 1 := by rw [hρ₁def]; exact hwp_one (f y) h1 h2
    have hρ₃ : ρ₃ y = 0 := by rw [hρ₃def]; exact hwq_ge (g y) (le_trans hdc_le3 hgy.le)
    have hρ₂ : ρ₂ y = 0 := by rw [hρ₂def]; simp [hρ₁, hρ₃]
    rw [hVdef]
    simp only [Pi.add_apply, Pi.neg_apply, hF1def, hF2def, hF3def, hρ₁, hρ₃, hρ₂]
    simp
  · -- ## clause: `V = -∇g` on `{γ/4 ≤ g ≤ 5γ/2}`
    intro y h1 h2
    have hfy : 7 * a / 4 < f y := by
      have h := htri y
      linarith
    have hρ₃ : ρ₃ y = 1 := by rw [hρ₃def]; exact hwq_one (g y) h1 h2
    have hρ₁ : ρ₁ y = 0 := by rw [hρ₁def]; exact hwp_ge (f y) (le_of_lt hfy)
    have hρ₂ : ρ₂ y = 0 := by rw [hρ₂def]; simp [hρ₁, hρ₃]
    rw [hVdef]
    simp only [Pi.add_apply, Pi.neg_apply, hF1def, hF2def, hF3def, hρ₁, hρ₃, hρ₂]
    simp
  · -- ## clause: ascent on `{a/4 ≤ f} ∩ {γ/8 < g}`
    intro y h1 h2
    exact hascC y h1 (le_of_lt h2)
  · -- ## clause: non-vanishing on `{a/4 ≤ f} ∩ {γ/8 ≤ g}`
    intro y h1 h2 hzero
    have hpos : 0 < f y := by linarith
    have hpy : Manifold.riemannianEDist I y p = ENNReal.ofReal (f y) := by
      rw [Manifold.riemannianEDist_comm]
      exact (ENNReal.ofReal_toReal
        (ne_of_lt (lt_of_le_of_lt (hdiam p y) ENNReal.ofReal_lt_top))).symm
    obtain ⟨u, hu1, hpGu⟩ := Submission.GSCritical.exists_unit_of_dist (cov := cov) hmet htor
      (x := y) (p := p) hpy hpos
    have hlt := hascC y h1 h2 (f y) u hpos.le hu1 hpGu hpy
    rw [hzero] at hlt
    simp at hlt

end Work.Diff.Dim2
