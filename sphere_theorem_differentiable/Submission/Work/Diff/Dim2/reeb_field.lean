import Mathlib
import Submission.Work.Diff.Dim2.Field
import Submission.Work.Diff.C.rdist_continuous

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The Reeb field of the `d = 2` branch

This file proves `Work.Diff.Dim2.reeb_field`, the existence of the global `C^∞` field `V` driving
the smooth Reeb construction of the `d = 2` branch (see `Plan2.lean`, §2), namely a field with

* `V = ∇(d(p,·))` on the annulus `{a/4 ≤ d(p,·) ≤ 3a/2}`,
* `V = -∇(d(q,·))` on the annulus `{γ/4 ≤ d(q,·) ≤ 3γ/2}`,
* `V` an ascent direction for `d(p,·)` on the slab `{a/4 ≤ d(p,·) ≤ D - 2γ}`.

The construction is the partition-of-unity gluing of three pieces:

* `χ₁(f)·∇f` with `χ₁` the window `win (a/8) (a/4) (3a/2) (7a/4)` of `Field.lean`: smooth because
  the varying part of `χ₁` lies inside `{0 < f < v}`, where `f` is smooth by hypothesis;
* `-χ₃(g)·∇g` with `χ₃ = win (γ/8) (γ/4) (3γ/2) (7γ/4)`, symmetrically;
* `χ₂·W` with `χ₂ := (1-χ₁)(1-χ₃)` and `W` the `C^∞` ascent field on the compact set
  `t = {3a/2 ≤ f} ∩ {γ ≤ g}` produced by `Submission.GSGlobal2.exists_continuous_ascent_field_of_diam`.

The separation hypotheses `hsep1 : 3a/2 + 2γ < D` and `hsep2 : 2a + 3γ/2 < D` together with the
triangle inequality `D ≤ f + g` show that `χ₃(g)` vanishes on the first annulus, that `χ₁(f)`
vanishes on the second one, and that on the slab `{a/4 ≤ f ≤ D - 2γ}` one has `g ≥ 2γ`, so that
`V = χ₁(f)·∇f + (1-χ₁(f))·W`, a convex combination of two ascent directions.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.Dim2

section Helpers

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

/-- **Smoothness of a window composed with a function that is smooth on `{0 < f < v}`.**

Let `f : M → ℝ` be continuous and `C^∞` at every point with `0 < f y < v`, and let `ψ : ℝ → ℝ` be
smooth and constant on `(-∞, c]` and on `[d, ∞)`, where `0 < c` and `d < v`.  Then `ψ ∘ f` is
`C^∞`.  Indeed, the only points at which `f` may fail to be smooth satisfy `f y ≤ 0` or
`f y ≥ v`; at the former `f y < c` (as `0 < c`), at the latter `f y > d` (as `d < v`), so `ψ ∘ f`
is locally constant there. -/
lemma reeb_window_comp
    {f : M → ℝ} {c d v : ℝ} (hc : 0 < c) (hd : d < v) (hf : Continuous f)
    (hsm : ∀ y : M, 0 < f y → f y < v → CMDiffAt ∞ f y)
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hψc : ∀ x : ℝ, x ≤ c → ψ x = ψ c)
    (hψd : ∀ x : ℝ, d ≤ x → ψ x = ψ d) :
    CMDiff ∞ (fun y : M => ψ (f y)) := by
  intro y
  rcases lt_or_ge (f y) c with h | h
  · have hmem : {z : M | f z < c} ∈ 𝓝 y := (isOpen_lt hf continuous_const).mem_nhds h
    exact (contMDiffAt_const (c := ψ c)).congr_of_eventuallyEq
      (Filter.eventually_of_mem hmem fun z hz => hψc (f z) (le_of_lt hz))
  · rcases lt_or_ge d (f y) with h2 | h2
    · have hmem : {z : M | d < f z} ∈ 𝓝 y := (isOpen_lt continuous_const hf).mem_nhds h2
      exact (contMDiffAt_const (c := ψ d)).congr_of_eventuallyEq
        (Filter.eventually_of_mem hmem fun z hz => hψd (f z) (le_of_lt hz))
    · exact ContMDiffAt.comp y hψ.contDiffAt.contMDiffAt
        (hsm y (lt_of_lt_of_le hc h) (lt_of_le_of_lt h2 hd))

/-- **Smoothness of a window multiple of `∇f`.**

Same hypotheses as `reeb_window_comp`, but `ψ` now vanishes on both sides of the interval `[c,d]`,
and we conclude that the section `y ↦ ψ (f y) • ∇f y` is `C^∞`.  Off `{0 < f < v}` the section
vanishes on a neighbourhood; on `{0 < f < v}` it is a product of the smooth scalar `ψ ∘ f` with the
smooth section `∇f` (`Work.Diff.C.grad_smoothAt`). -/
lemma reeb_window_smul_rgrad
    {f : M → ℝ} {c d v : ℝ} (hc : 0 < c) (hd : d < v) (hf : Continuous f)
    (hsm : ∀ y : M, 0 < f y → f y < v → CMDiffAt ∞ f y)
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hψc : ∀ x : ℝ, x ≤ c → ψ x = 0)
    (hψd : ∀ x : ℝ, d ≤ x → ψ x = 0) :
    CMDiff ∞ (T% (fun y : M => ψ (f y) • Work.Diff.C.rgrad (I := I) (M := M) f y)) := by
  intro y
  by_cases h1 : 0 < f y ∧ f y < v
  · have hψf : CMDiffAt ∞ (fun z : M => ψ (f z)) y :=
      ContMDiffAt.comp y hψ.contDiffAt.contMDiffAt (hsm y h1.1 h1.2)
    have hgrad : ContMDiffAt I I.tangent ∞
        (fun z : M => (⟨z, Work.Diff.C.rgrad (I := I) (M := M) f z⟩ :
          TotalSpace E (TangentSpace I))) y :=
      Work.Diff.C.grad_smoothAt (I := I) (M := M) (F := f) (x := y) (hsm y h1.1 h1.2)
    exact hψf.smul_section hgrad
  · refine (Bundle.contMDiffAt_zeroSection ℝ (fun x : M => TangentSpace I x)
      (IB := I) (x := y)).congr_of_eventuallyEq ?_
    rcases not_and_or.mp h1 with h1 | h1
    · have hfy : f y ≤ 0 := not_lt.mp h1
      have hmem : {z : M | f z < c} ∈ 𝓝 y :=
        (isOpen_lt hf continuous_const).mem_nhds (lt_of_le_of_lt hfy hc)
      refine Filter.eventually_of_mem hmem fun z hz => ?_
      show (⟨z, ψ (f z) • Work.Diff.C.rgrad (I := I) (M := M) f z⟩ :
          TotalSpace E (TangentSpace I))
        = Bundle.zeroSection E (fun x : M => TangentSpace I x) z
      rw [hψc (f z) (le_of_lt hz), zero_smul]
      rfl
    · have hfy : v ≤ f y := not_lt.mp h1
      have hmem : {z : M | d < f z} ∈ 𝓝 y :=
        (isOpen_lt continuous_const hf).mem_nhds (lt_of_lt_of_le hd hfy)
      refine Filter.eventually_of_mem hmem fun z hz => ?_
      show (⟨z, ψ (f z) • Work.Diff.C.rgrad (I := I) (M := M) f z⟩ :
          TotalSpace E (TangentSpace I))
        = Bundle.zeroSection E (fun x : M => TangentSpace I x) z
      rw [hψd (f z) (le_of_lt hz), zero_smul]
      rfl

end Helpers

theorem reeb_field
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
    (hsep1 : 3 * a / 2 + 2 * γ < D) (hsep2 : 2 * a + 3 * γ / 2 < D) :
    ∃ V : (y : M) → TangentSpace I y,
      IsReebField (I := I) (M := M) cov hmet p q D a γ V := by
  classical
  -- ## elementary numerical facts
  have hDpos : 0 < D := by linarith [hDGt, Real.pi_pos]
  have hDnn : 0 ≤ D := hDpos.le
  have ha8 : 0 < a / 8 := by linarith
  have hg8 : 0 < γ / 8 := by linarith
  have hA1 : a / 8 < a / 4 := by linarith
  have hA2 : 3 * a / 2 < 7 * a / 4 := by linarith
  have hA4 : 7 * a / 4 < v := by linarith
  have hG1 : γ / 8 < γ / 4 := by linarith
  have hG2 : 3 * γ / 2 < 7 * γ / 4 := by linarith
  have hG4 : 7 * γ / 4 < v := by linarith
  have h74a : 7 * a / 4 ≤ 2 * a := by linarith
  have h74g : 7 * γ / 4 ≤ 2 * γ := by linarith
  -- ## the two distance functions
  set f : M → ℝ := fun y => Work.Diff.C.rdist (I := I) (M := M) p y with hf
  set g : M → ℝ := fun y => Work.Diff.C.rdist (I := I) (M := M) q y with hgd
  have hfcont : Continuous f := Work.Diff.C.rdist_continuous (I := I) (M := M) p
  have hgcont : Continuous g := Work.Diff.C.rdist_continuous (I := I) (M := M) q
  have hfp : f p = 0 := by
    rw [hf]
    simp [Work.Diff.C.rdist, Manifold.riemannianEDist_self]
  have hgq : g q = 0 := by
    rw [hgd]
    simp [Work.Diff.C.rdist, Manifold.riemannianEDist_self]
  have hsmPf : ∀ y : M, 0 < f y → f y < v → CMDiffAt ∞ f y :=
    fun y h1 h2 => hsmP y h1 h2
  have hsmQg : ∀ y : M, 0 < g y → g y < v → CMDiffAt ∞ g y :=
    fun y h1 h2 => hsmQ y h1 h2
  -- ## the triangle inequality `D ≤ f y + g y`
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
  -- ## the middle ascent region and the field `W` on it
  have htc : IsCompact {y : M | 3 * a / 2 ≤ f y ∧ γ ≤ g y} :=
    ((isClosed_le continuous_const hfcont).inter
      (isClosed_le continuous_const hgcont)).isCompact
  obtain ⟨W, hWasc, -, hWsm⟩ :=
    Submission.GSGlobal2.exists_continuous_ascent_field_of_diam (cov := cov) hmet htor hpinch
      hdiam hDGt hDLt hpq htc
      (fun x hx => by
        have hx1 : 3 * a / 2 ≤ f x := hx.1
        intro hxp
        rw [hxp, hfp] at hx1
        linarith [hx1, ha])
      (fun x hx => by
        have hx2 : γ ≤ g x := hx.2
        intro hxq
        rw [hxq, hgq] at hx2
        linarith [hx2, hg])
  -- ## the windows and the weights
  set wp : ℝ → ℝ := win (a / 8) (a / 4) (3 * a / 2) (7 * a / 4) with hwp
  set wq : ℝ → ℝ := win (γ / 8) (γ / 4) (3 * γ / 2) (7 * γ / 4) with hwq
  have hwpsm : ContDiff ℝ ∞ wp := by rw [hwp]; exact win_smooth hA1 hA2
  have hwqsm : ContDiff ℝ ∞ wq := by rw [hwq]; exact win_smooth hG1 hG2
  have hwp_le : ∀ x : ℝ, x ≤ a / 8 → wp x = 0 := by
    intro x hx; rw [hwp]; exact win_eq_zero_of_le hA1 hx
  have hwp_ge : ∀ x : ℝ, 7 * a / 4 ≤ x → wp x = 0 := by
    intro x hx; rw [hwp]; exact win_eq_zero_of_ge hA2 hx
  have hwp_one : ∀ x : ℝ, a / 4 ≤ x → x ≤ 3 * a / 2 → wp x = 1 := by
    intro x h1 h2; rw [hwp]; exact win_eq_one hA1 h1 h2 hA2
  have hwq_le : ∀ x : ℝ, x ≤ γ / 8 → wq x = 0 := by
    intro x hx; rw [hwq]; exact win_eq_zero_of_le hG1 hx
  have hwq_ge : ∀ x : ℝ, 7 * γ / 4 ≤ x → wq x = 0 := by
    intro x hx; rw [hwq]; exact win_eq_zero_of_ge hG2 hx
  have hwq_one : ∀ x : ℝ, γ / 4 ≤ x → x ≤ 3 * γ / 2 → wq x = 1 := by
    intro x h1 h2; rw [hwq]; exact win_eq_one hG1 h1 h2 hG2
  have hwp_nn : ∀ x : ℝ, 0 ≤ wp x := by intro x; rw [hwp]; exact win_nonneg x
  have hwp_le1 : ∀ x : ℝ, wp x ≤ 1 := by intro x; rw [hwp]; exact win_le_one x
  have hwq_nn : ∀ x : ℝ, 0 ≤ wq x := by intro x; rw [hwq]; exact win_nonneg x
  have hwq_le1 : ∀ x : ℝ, wq x ≤ 1 := by intro x; rw [hwq]; exact win_le_one x
  have hwp_le' : ∀ x : ℝ, x ≤ a / 8 → wp x = wp (a / 8) := by
    intro x hx; rw [hwp_le x hx, hwp_le (a / 8) le_rfl]
  have hwq_le' : ∀ x : ℝ, x ≤ γ / 8 → wq x = wq (γ / 8) := by
    intro x hx; rw [hwq_le x hx, hwq_le (γ / 8) le_rfl]
  have hwp_ge' : ∀ x : ℝ, 7 * a / 4 ≤ x → wp x = wp (7 * a / 4) := by
    intro x hx; rw [hwp_ge x hx, hwp_ge (7 * a / 4) le_rfl]
  have hwq_ge' : ∀ x : ℝ, 7 * γ / 4 ≤ x → wq x = wq (7 * γ / 4) := by
    intro x hx; rw [hwq_ge x hx, hwq_ge (7 * γ / 4) le_rfl]
  set ρ₁ : M → ℝ := fun y => wp (f y) with hρ₁
  set ρ₃ : M → ℝ := fun y => wq (g y) with hρ₃
  set ρ₂ : M → ℝ := fun y => (1 - ρ₁ y) * (1 - ρ₃ y) with hρ₂
  have hρ₁sm : CMDiff ∞ ρ₁ := by
    rw [hρ₁]
    exact reeb_window_comp (f := f) (c := a / 8) (d := 7 * a / 4) ha8 hA4 hfcont
      hsmPf hwpsm hwp_le' hwp_ge'
  have hρ₃sm : CMDiff ∞ ρ₃ := by
    rw [hρ₃]
    exact reeb_window_comp (f := g) (c := γ / 8) (d := 7 * γ / 4) hg8 hG4 hgcont
      hsmQg hwqsm hwq_le' hwq_ge'
  have hρ₂sm : CMDiff ∞ ρ₂ := by
    rw [hρ₂]
    exact ((contMDiff_const (c := (1 : ℝ))).sub hρ₁sm).mul
      ((contMDiff_const (c := (1 : ℝ))).sub hρ₃sm)
  -- ## the three summands and the field `V`
  set F1 : (y : M) → TangentSpace I y :=
    fun y => ρ₁ y • Work.Diff.C.rgrad (I := I) (M := M) f y with hF1
  set F2 : (y : M) → TangentSpace I y :=
    fun y => ρ₃ y • Work.Diff.C.rgrad (I := I) (M := M) g y with hF2
  set F3 : (y : M) → TangentSpace I y := fun y => ρ₂ y • W y with hF3
  set V : (y : M) → TangentSpace I y := F1 + (-F2) + F3 with hV
  have hF1sm : CMDiff ∞ (T% F1) := by
    rw [hF1]
    exact reeb_window_smul_rgrad (f := f) (c := a / 8) (d := 7 * a / 4) ha8 hA4 hfcont
      hsmPf hwpsm hwp_le hwp_ge
  have hF2sm : CMDiff ∞ (T% F2) := by
    rw [hF2]
    exact reeb_window_smul_rgrad (f := g) (c := γ / 8) (d := 7 * γ / 4) hg8 hG4 hgcont
      hsmQg hwqsm hwq_le hwq_ge
  have hF3sm : CMDiff ∞ (T% F3) := by
    rw [hF3]
    exact hρ₂sm.smul_section hWsm
  refine ⟨V, ?_, ?_, ?_, ?_⟩
  · -- ## `V` is a globally smooth section
    rw [hV]
    exact (hF1sm.add_section hF2sm.neg_section).add_section hF3sm
  · -- ## `V = ∇f` on `{a/4 ≤ f ≤ 3a/2}`
    intro y h1 h2
    have hgy : 2 * γ ≤ g y := by have h := htri y; linarith
    have hρ₁y : ρ₁ y = 1 := by rw [hρ₁]; exact hwp_one (f y) h1 h2
    have hρ₃y : ρ₃ y = 0 := by
      rw [hρ₃]; exact hwq_ge (g y) (le_trans h74g hgy)
    have hρ₂y : ρ₂ y = 0 := by rw [hρ₂]; simp [hρ₁y, hρ₃y]
    rw [hV]
    simp only [Pi.add_apply, Pi.neg_apply, hF1, hF2, hF3, hρ₁y, hρ₃y, hρ₂y, hf]
    simp
  · -- ## `V = -∇g` on `{γ/4 ≤ g ≤ 3γ/2}`
    intro y h1 h2
    have hfx : 2 * a ≤ f y := by have h := htri y; linarith
    have hρ₁y : ρ₁ y = 0 := by
      rw [hρ₁]; exact hwp_ge (f y) (le_trans h74a hfx)
    have hρ₃y : ρ₃ y = 1 := by rw [hρ₃]; exact hwq_one (g y) h1 h2
    have hρ₂y : ρ₂ y = 0 := by rw [hρ₂]; simp [hρ₁y, hρ₃y]
    rw [hV]
    simp only [Pi.add_apply, Pi.neg_apply, hF1, hF2, hF3, hρ₁y, hρ₃y, hρ₂y, hgd]
    simp
  · -- ## `V` is an ascent field on the slab `{a/4 ≤ f ≤ D - 2γ}`
    intro y h1 h2
    have hgy : 2 * γ ≤ g y := by have h := htri y; linarith
    have hρ₃y : ρ₃ y = 0 := by
      rw [hρ₃]; exact hwq_ge (g y) (le_trans h74g hgy)
    have hρ₂y : ρ₂ y = 1 - ρ₁ y := by rw [hρ₂]; simp [hρ₃y]
    have hVval : V y = ρ₁ y • Work.Diff.C.rgrad (I := I) (M := M) f y
        + (1 - ρ₁ y) • W y := by
      rw [hV]
      simp only [Pi.add_apply, Pi.neg_apply, hF1, hF2, hF3, hρ₃y, hρ₂y]
      simp
    have hρ₁nn : 0 ≤ ρ₁ y := by rw [hρ₁]; exact hwp_nn (f y)
    have hρ₁le1 : ρ₁ y ≤ 1 := by rw [hρ₁]; exact hwp_le1 (f y)
    have hgt : γ ≤ g y := by linarith
    -- `∇f` is an ascent direction wherever its weight is positive
    have hagrad : 0 < ρ₁ y → Submission.GSField.IsAscentAt hmet p y
        (Work.Diff.C.rgrad (I := I) (M := M) f y) := by
      intro hpos
      have hfypos : 0 < f y := by linarith
      have hfyv : f y < v := by
        by_contra hcon
        push_neg at hcon
        have hz : ρ₁ y = 0 := by rw [hρ₁]; exact hwp_ge (f y) (le_trans hA4.le hcon)
        linarith
      exact Work.Diff.Dim2.isAscentAt_rgrad_rdist (cov := cov) (hmet := hmet)
        (p := p) (y := y) hfypos (hsmP y hfypos hfyv)
    -- `W` is an ascent direction wherever its weight is positive
    have haW : ρ₁ y < 1 → Submission.GSField.IsAscentAt hmet p y (W y) := by
      intro hlt
      have hfy2 : 3 * a / 2 ≤ f y := by
        by_contra hcon
        push_neg at hcon
        have hone : ρ₁ y = 1 := by rw [hρ₁]; exact hwp_one (f y) h1 (le_of_lt hcon)
        linarith
      exact hWasc y ⟨hfy2, hgt⟩
    rcases eq_or_lt_of_le hρ₁nn with h0 | hpos
    · -- `ρ₁ y = 0`: then `V y = W y`
      have hβ : ρ₁ y = 0 := h0.symm
      have hlt1 : ρ₁ y < 1 := by rw [hβ]; norm_num
      rw [hVval, hβ]
      simpa using haW hlt1
    · rcases eq_or_lt_of_le hρ₁le1 with h1' | h1lt
      · -- `ρ₁ y = 1`: then `V y = ∇f y`
        have hβ : ρ₁ y = 1 := h1'
        have hpos1 : 0 < ρ₁ y := by rw [hβ]; norm_num
        rw [hVval, hβ]
        simpa using hagrad hpos1
      · -- `0 < ρ₁ y < 1`: a convex combination of two ascent directions
        have hcomb := Submission.GSField.isAscentAt_add (cov := cov)
          (v := Work.Diff.C.rgrad (I := I) (M := M) f y) (w := W y)
          (a := ρ₁ y) (b := 1 - ρ₁ y) (hagrad hpos) (haW h1lt)
          (le_of_lt hpos) (by linarith) (by linarith)
        rw [hVval]
        exact hcomb

end Work.Diff.Dim2
