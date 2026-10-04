import Mathlib
import Submission.Work.Diff.Dim2.Lib
import Submission.Work.Diff.Dim2.Field
import Submission.Work.Diff.Dim2.reeb_field
import Submission.Work.Diff.Dim2.geodDir_to_q_isAscentAt

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The Reeb field of the `d = 2` branch (widened version)

This file proves `Work.Diff.Dim2.reeb_field2`: a globally `C^∞` field `V` with

* `V y = ∇(d(p,·)) y`   on the annulus `{a/4 ≤ d(p,·) ≤ 3a/2}`;
* `V y = -∇(d(q,·)) y`  on the annulus `{γ/4 ≤ d(q,·) ≤ 5γ/2}`;
* `V y` is an ascent direction for `d(p,·)` on `{a/4 ≤ d(p,·)} ∩ {γ/8 < d(q,·)}`;
* `V y ≠ 0` on `{a/4 ≤ d(p,·)} ∩ {γ/8 ≤ d(q,·)}`.

The construction follows `reeb_field.lean`, with two changes: the `q`-window is widened (its plateau
is `[γ/4, 5γ/2]`, so that the `-∇g` identity holds on the wider annulus requested here), and the
middle piece `W` is an ascent field on `{3a/2 ≤ f} ∩ {γ/8 ≤ g}` (instead of `{3a/2 ≤ f} ∩ {γ ≤ g}`),
which makes the ascent clause valid on the whole slab `{a/4 ≤ f} ∩ {γ/8 ≤ g}`.

With `f := rdist p` and `g := rdist q` the field is

`V = χ₁ ∇f + χ₂ W - χ₃ ∇g`,   `χ₁ = win (a/8) (a/4) (3a/2) (7a/4) ∘ f`,
`χ₃ = win (γ/8) (γ/4) (5γ/2) dc ∘ g`, `χ₂ = (1-χ₁)(1-χ₃)`,

for a cut-off `dc ∈ (5γ/2, min(3γ, v))` (it exists because `5γ/2 < v` and `5γ/2 < 3γ`).

The ascent of the `-∇g` term on `{γ/8 < g < 3γ}` is the geometric input: there `f > π/2` (triangle
inequality plus `3γ < D - π/2`) and `f < D` (uniqueness of the maximiser of `d(p,·)` at `q`, for
`π/2 < D < π`), and then `-∇(d(q,·))` is an ascent direction for `d(p,·)`:
`Work.Diff.Dim2.negRgradQ_ascent` below.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

namespace Work.Diff.Dim2

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.Geodesic Submission.GlobalExp

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M] [RegularSpace M]

/-! ## Auxiliary: a convex combination of ascent directions -/

/-- **A combination `α • v + β • w + δ • z` with non-negative weights and positive total weight is an
ascent direction**, provided each of the three vectors is an ascent direction whenever its weight is
non-zero.  This is `GSField.isAscentAt_add` in the form needed for the partition-of-unity gluing,
where the weight of a summand may vanish and the summand is then irrelevant. -/
theorem isAscentAt_smul_add_three
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [ContMDiffCovariantDerivative cov ∞]
    {hmet : IsMetricCompatible cov} {p x : M} {v w z : TangentSpace I x} {α β δ : ℝ}
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hδ : 0 ≤ δ) (hsum : 0 < α + β + δ)
    (hv : α ≠ 0 → Submission.GSField.IsAscentAt hmet p x v)
    (hw : β ≠ 0 → Submission.GSField.IsAscentAt hmet p x w)
    (hz : δ ≠ 0 → Submission.GSField.IsAscentAt hmet p x z) :
    Submission.GSField.IsAscentAt hmet p x (α • v + β • w + δ • z) := by
  intro r u hr hu hpG hd
  have key : ∀ (c : ℝ) (y : TangentSpace I x), 0 ≤ c →
      (c ≠ 0 → Submission.GSField.IsAscentAt hmet p x y) → c * inner ℝ y u ≤ 0 := by
    intro c y hc hcy
    rcases eq_or_lt_of_le hc with h | h
    · simp [← h]
    · exact (mul_neg_of_pos_of_neg h (hcy h.ne' r u hr hu hpG hd)).le
  have hstrict : 0 < α ∨ 0 < β ∨ 0 < δ := by
    by_contra hcon
    push_neg at hcon
    linarith [hcon.1, hcon.2.1, hcon.2.2]
  have hlt : α * inner ℝ v u + β * inner ℝ w u + δ * inner ℝ z u < 0 := by
    have kα := key α v hα hv
    have kβ := key β w hβ hw
    have kδ := key δ z hδ hz
    rcases hstrict with h | h | h
    · have h' := mul_neg_of_pos_of_neg h (hv h.ne' r u hr hu hpG hd)
      linarith
    · have h' := mul_neg_of_pos_of_neg h (hw h.ne' r u hr hu hpG hd)
      linarith
    · have h' := mul_neg_of_pos_of_neg h (hz h.ne' r u hr hu hpG hd)
      linarith
  rw [inner_add_left, inner_add_left, real_inner_smul_left, real_inner_smul_left,
    real_inner_smul_left]
  linarith [hlt]

/-! ## Auxiliary: `∇(rdist q) y = -ξ` for a minimising direction `ξ` towards `q` -/

/-- **The gradient of `rdist q` at `y` is the opposite of the unit direction towards `q`.**

If `q = GExp y (s • ξ)` with `‖ξ‖ = 1` and `d(y,q) = s > 0` (so `ξ` is the initial direction of a
minimising geodesic from `y` to `q`) and `rdist q ·` is smooth at `y`, then
`∇(rdist q)(y) = -ξ`.

Indeed, along the minimizing geodesic `G` from `y` to `q` one has `rdist q (G t) = s - t`, so the
directional derivative of `rdist q ·` at `y` in the direction `ξ` is `-1`; since `‖∇(rdist q)(y)‖ = 1`
(eikonal) and `‖ξ‖ = 1`, the Cauchy–Schwarz equality case gives `∇(rdist q)(y) = -ξ`. -/
theorem rgrad_rdist_q_eq_neg_dir
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [ContMDiffCovariantDerivative cov ∞]
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    {q y : M} {s : ℝ} {ξ : TangentSpace I y}
    (hs : 0 < s) (hξ : ‖ξ‖ = 1)
    (hq : q = Submission.GlobalExp.GExp (cov := cov) hmet y (s • ξ))
    (hsd : Manifold.riemannianEDist I y q = ENNReal.ofReal s)
    (hsm : CMDiffAt ∞ (fun z : M ↦ Work.Diff.C.rdist (I := I) (M := M) q z) y) :
    Work.Diff.C.rgrad (I := I) (M := M)
      (fun z : M ↦ Work.Diff.C.rdist (I := I) (M := M) q z) y = -ξ := by
  classical
  set F : M → ℝ := fun z : M ↦ Work.Diff.C.rdist (I := I) (M := M) q z with hFdef
  set G : ℝ → M := Submission.GlobalExp.geodCurve (cov := cov) hmet s hs.le y ξ hξ with hGdef
  have hspec := Submission.GlobalExp.geodCurve_spec (cov := cov) hmet s hs.le y ξ hξ
  have hG0 : G 0 = y := hspec.1
  have hvel : Submission.Geodesic.curveVelocity (I := I) G 0 = ξ := hspec.2.1
  have hδpos := Submission.GlobalExp.geodDelta_pos (cov := cov) hmet
  have h0mem : (0 : ℝ) ∈ Set.Ioo (-(Submission.GlobalExp.geodDelta (cov := cov) hmet))
      (s + Submission.GlobalExp.geodDelta (cov := cov) hmet) :=
    ⟨by linarith, by linarith⟩
  have hGsmAt : ContMDiffAt 𝓘(ℝ) I ∞ G 0 :=
    (hspec.2.2.1 0 h0mem).contMDiffAt (isOpen_Ioo.mem_nhds h0mem)
  have hGmd : MDifferentiableAt 𝓘(ℝ) I G 0 := hGsmAt.mdifferentiableAt (by simp)
  -- the geodesic is minimizing up to time `s`, where it reaches `q`
  have hGs : G s = q := by
    rw [hGdef]
    rw [← Submission.HopfRinow.GExp_eq_geodCurve (cov := cov) hmet (x := y) (u := ξ) hξ
      (T := s) hs.le (r := s) hs.le le_rfl]
    exact hq.symm
  have hmin : Manifold.riemannianEDist I y (G s) = ENNReal.ofReal s := by
    rw [hGs]; exact hsd
  have hsub : ∀ a ∈ Set.Icc (0 : ℝ) s, ∀ b ∈ Set.Icc (0 : ℝ) s, a ≤ b →
      Manifold.riemannianEDist I (G a) (G b) = ENNReal.ofReal (b - a) :=
    Submission.HingeKey.geodCurve_sub_arc_minimising' (cov := cov) hmet
      (T := s) hs.le hξ (s := s) hs.le le_rfl hmin
  -- the value of `rdist q` along the geodesic
  have hval : ∀ t ∈ Set.Icc (0 : ℝ) s, F (G t) = s - t := by
    intro t ht
    have h1 := hsub t ht s ⟨hs.le, le_rfl⟩ ht.2
    rw [hGs] at h1
    rw [hFdef]
    show (Manifold.riemannianEDist I q (G t)).toReal = s - t
    rw [Manifold.riemannianEDist_comm, h1, ENNReal.toReal_ofReal (by linarith [ht.1, ht.2])]
  -- differentiability of the two functions
  have hFmd : MDifferentiableAt I 𝓘(ℝ, ℝ) F y := hsm.mdifferentiableAt (by simp)
  have hFGmd : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (F ∘ G) 0 :=
    (hG0 ▸ hFmd).comp 0 hGmd
  -- the chain rule
  have hchain : mvfderiv I F y ξ = deriv (F ∘ G) 0 := by
    have h := Commons.Geometry.Manifold.Tangent.mvfderiv_comp_curve (I := I) (g := F) (γ := G)
      (t := 0) (by rw [hG0]; exact hFmd) hGmd
    rw [← Submission.Geodesic.curveVelocity_apply (I := I) G 0] at h
    rw [hvel] at h
    have h2 : (mvfderiv I F (G 0)) ξ = (mvfderiv I F y) ξ := by rw [hG0]
    rw [h2] at h
    exact h
  -- the derivative of `t ↦ rdist q (G t)` at `0` is `-1`
  have hderiv : deriv (F ∘ G) 0 = -1 := by
    have hbase : HasDerivWithinAt (fun t : ℝ => s - t) (-1) (Set.Ici 0) 0 := by
      have h : HasDerivAt (fun t : ℝ => s - t) (-1) 0 := by
        simpa using (hasDerivAt_id (0 : ℝ)).const_sub s
      exact h.hasDerivWithinAt
    have heq : (F ∘ G) =ᶠ[𝓝[Set.Ici (0 : ℝ)] 0] (fun t : ℝ => s - t) := by
      have hIio : Set.Iio s ∈ 𝓝[Set.Ici (0 : ℝ)] 0 :=
        nhdsWithin_le_nhds (Iio_mem_nhds hs)
      filter_upwards [self_mem_nhdsWithin, hIio] with t ht htr
      exact hval t ⟨ht, le_of_lt htr⟩
    have h0 : (F ∘ G) 0 = (fun t : ℝ => s - t) 0 := by
      show F (G 0) = s - 0
      rw [hval 0 ⟨le_refl 0, hs.le⟩, sub_zero]
    have hGW : HasDerivWithinAt (F ∘ G) (-1) (Set.Ici 0) 0 :=
      hbase.congr_of_eventuallyEq heq h0
    have hdiff : DifferentiableAt ℝ (F ∘ G) 0 :=
      mdifferentiableAt_iff_differentiableAt.mp hFGmd
    have h1 := hGW.derivWithin (uniqueDiffWithinAt_Ici 0)
    have h2 := hdiff.derivWithin (uniqueDiffWithinAt_Ici 0)
    rw [h2] at h1
    exact h1
  -- the two facts about the gradient
  have hmvf : mvfderiv I F y ξ = -1 := by rw [hchain, hderiv]
  have hinner : inner ℝ (Work.Diff.C.rgrad (I := I) (M := M) F y) ξ = -1 := by
    rw [Work.Diff.C.inner_rgrad]
    exact hmvf
  have hrd : Work.Diff.C.rdist (I := I) (M := M) q y = s := by
    rw [Work.Diff.C.rdist, Manifold.riemannianEDist_comm, hsd,
      ENNReal.toReal_ofReal (le_of_lt hs)]
  have hnorm : ‖Work.Diff.C.rgrad (I := I) (M := M) F y‖ = 1 := by
    have h := Work.Diff.C.rgrad_rdist_eikonal (cov := cov) hmet htor (q := q) (x := y)
      (by rw [hrd]; exact ne_of_gt hs) hsm
    rw [real_inner_self_eq_norm_sq] at h
    nlinarith [norm_nonneg (Work.Diff.C.rgrad (I := I) (M := M) F y)]
  -- Cauchy–Schwarz equality
  have hzero : ‖Work.Diff.C.rgrad (I := I) (M := M) F y + ξ‖ ^ 2 = 0 := by
    rw [norm_add_sq_real, hnorm, hξ, hinner]
    norm_num
  have hz : Work.Diff.C.rgrad (I := I) (M := M) F y + ξ = 0 :=
    norm_eq_zero.mp (sq_eq_zero_iff.mp hzero)
  exact eq_neg_of_add_eq_zero_left hz

/-! ## Auxiliary: `-∇(rdist q)` is an ascent direction -/

/-- **`-∇(rdist q)(y)` is an ascent direction for `d(p,·)` at `y`.**

Let `p, q` be a diameter pair (`d(p,q) = D`, `π/2 < D < π`, all mutual distances `≤ D`) and let
`y` be a point with `π/2 < d(p,y)` and `0 < d(q,y)` at which `rdist q ·` is smooth.  Then every
shortest direction `u` from `y` to `p` satisfies `⟪-∇(rdist q)(y), u⟫ < 0`, i.e. every shortest
geodesic from `y` to `p` starts by moving away from `q`.  (`d(p,y) < D` is deduced from the
uniqueness of the maximiser `q` of `d(p,·)`, `GSStep1.step1_diameter_unique_of_lt_pi`.)

Proof: Hopf–Rinow gives a unit direction `ξ` with `q = GExp y (s • ξ)`, `d(y,q) = s`;
`Work.Diff.Dim2.geodDir_to_q_isAscentAt` gives `IsAscentAt hmet p y ξ`, and
`rgrad_rdist_q_eq_neg_dir` identifies `ξ = -∇(rdist q)(y)`. -/
theorem negRgradQ_ascent
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [ContMDiffCovariantDerivative cov ∞]
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) (hpinch : QuarterPinched cov)
    {p q : M} {D : ℝ}
    (hDGt : Real.pi / 2 < D) (hDLt : D < Real.pi)
    (hdiam : ∀ r t : M, Manifold.riemannianEDist I r t ≤ ENNReal.ofReal D)
    (hpq : Manifold.riemannianEDist I p q = ENNReal.ofReal D)
    {y : M} (hyq : 0 < Work.Diff.C.rdist (I := I) (M := M) q y)
    (hypfar : Real.pi / 2 < Work.Diff.C.rdist (I := I) (M := M) p y)
    (hsm : CMDiffAt ∞ (fun z : M ↦ Work.Diff.C.rdist (I := I) (M := M) q z) y) :
    Submission.GSField.IsAscentAt hmet p y
      (- Work.Diff.C.rgrad (I := I) (M := M)
        (fun z : M ↦ Work.Diff.C.rdist (I := I) (M := M) q z) y) := by
  classical
  have hDnn : 0 ≤ D := le_trans (by linarith [Real.pi_pos]) hDGt.le
  -- `y ≠ q`
  have hyne : y ≠ q := by
    intro h
    have h0 : Work.Diff.C.rdist (I := I) (M := M) q y = 0 := by
      rw [h]
      show (Manifold.riemannianEDist I q q).toReal = 0
      rw [Manifold.riemannianEDist_self, ENNReal.toReal_zero]
    linarith
  -- `d(p,y) < D`, by uniqueness of the maximiser of `d(p,·)`
  have hyplt : Work.Diff.C.rdist (I := I) (M := M) p y < D := by
    rcases lt_or_eq_of_le (hdiam p y) with h | h
    · have hfin : Manifold.riemannianEDist I p y ≠ ⊤ :=
        (lt_of_lt_of_le h ENNReal.ofReal_lt_top.le).ne
      have h2 := (ENNReal.toReal_lt_toReal hfin ENNReal.ofReal_ne_top).mpr h
      rw [ENNReal.toReal_ofReal hDnn] at h2
      exact h2
    · exact absurd (Submission.GSStep1.step1_diameter_unique_of_lt_pi (cov := cov) hmet htor
        hpinch (p := p) (q₁ := q) (q₂ := y) hdiam hDGt hDLt hpq h (fun hc => hyne hc.symm))
        not_false
  -- Hopf–Rinow: a minimizing geodesic from `y` to `q`
  obtain ⟨v, hvG, hvd⟩ :=
    Submission.HopfRinow.exists_geodesic_riemannianEDist_eq (cov := cov) hmet htor y q
  set s : ℝ := ‖v‖ with hsdef
  have hsy : Work.Diff.C.rdist (I := I) (M := M) q y = s := by
    rw [Work.Diff.C.rdist, Manifold.riemannianEDist_comm, hvd,
      ENNReal.toReal_ofReal (norm_nonneg v)]
  have hspos : 0 < s := by rw [← hsy]; exact hyq
  have hvne : v ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hsdef
    rw [hsdef] at hspos
    exact lt_irrefl 0 hspos
  set ξ : TangentSpace I y := unitOf v hvne with hξdef
  have hξ1 : ‖ξ‖ = 1 := unitOf_norm v hvne
  have hsξ : s • ξ = v := by
    rw [hξdef, hsdef, unitOf, smul_smul, mul_inv_cancel₀ (by positivity), one_smul]
  have hq : q = Submission.GlobalExp.GExp (cov := cov) hmet y (s • ξ) := by
    rw [hsξ]; exact hvG.symm
  have hDir := geodDir_to_q_isAscentAt (cov := cov) hmet htor hpinch hDGt hDLt hdiam hpq
    hspos hξ1 hq hvd hypfar hyplt
  have hGrad := rgrad_rdist_q_eq_neg_dir (cov := cov) hmet htor hspos hξ1 hq hvd hsm
  rw [hGrad]
  simpa using hDir

/-- **The Reeb field data of the `d = 2` branch (widened version).** -/
theorem reeb_field2
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
  -- the cut-off of the `q`-window, in `(5γ/2, min (3γ) v)`
  set dc : ℝ := min (3 * γ) ((v + 5 * γ / 2) / 2) with hdcdef
  have hdc_gt : 5 * γ / 2 < dc := by
    rw [hdcdef]
    exact lt_min hG2 (by linarith [hsep4])
  have hdc_le : dc ≤ 3 * γ := by rw [hdcdef]; exact min_le_left _ _
  have hdc_lt_v : dc < v := by
    rw [hdcdef]
    exact lt_of_le_of_lt (min_le_right _ _) (by linarith [hsep4])
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
  set F3 : (y : M) → TangentSpace I y := fun y => ρ₂ y • W y with hF3def
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
    exact hρ₂sm.smul_section hWsm
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
      have hρ₃ : ρ₃ y = 0 := by rw [hρ₃def]; exact hwq_ge (g y) (le_trans hdc_le hgy3.le)
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
      have hWasc_y : Submission.GSField.IsAscentAt hmet p y (W y) := hWasc y hyt
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
        have hgy3 : g y < 3 * γ := lt_of_lt_of_le hgdc hdc_le
        have hfπ : Real.pi / 2 < f y := by
          have h := htri y
          linarith
        exact negRgradQ_ascent (cov := cov) hmet htor hpinch hDGt hDLt hdiam hpq hgpos hfπ
          (hsmQg y hgpos (lt_of_lt_of_le hgdc hdc_lt_v.le))
      have hthree := isAscentAt_smul_add_three (cov := cov) (hmet := hmet) (p := p) (x := y)
        (v := Work.Diff.C.rgrad (I := I) (M := M) f y) (w := W y)
        (z := - Work.Diff.C.rgrad (I := I) (M := M) g y)
        (α := ρ₁ y) (β := ρ₂ y) (δ := ρ₃ y) hρ₁nn hρ₂nn hρ₃nn hsum hv1
        (fun _ => hWasc_y) hv3
      have hVy : V y = ρ₁ y • Work.Diff.C.rgrad (I := I) (M := M) f y + ρ₂ y • W y
          + ρ₃ y • (- Work.Diff.C.rgrad (I := I) (M := M) g y) := by
        rw [hVdef]
        simp only [Pi.add_apply, Pi.neg_apply, hF1def, hF2def, hF3def]
        rw [smul_neg]
        abel
      rw [hVy]
      exact hthree
  refine ⟨V, ?_, ?_, ?_, ?_, ?_⟩
  · show ContMDiff I (I.prod (modelWithCornersSelf ℝ E)) ∞
      (fun y : M => (⟨y, V y⟩ : Bundle.TotalSpace E (TangentSpace I)))
    exact hVsm
  · -- ## clause: `V = ∇f` on `{a/4 ≤ f ≤ 3a/2}`
    intro y h1 h2
    have hgy : 3 * γ < g y := by
      have h := htri y
      linarith
    have hρ₁ : ρ₁ y = 1 := by rw [hρ₁def]; exact hwp_one (f y) h1 h2
    have hρ₃ : ρ₃ y = 0 := by rw [hρ₃def]; exact hwq_ge (g y) (le_trans hdc_le hgy.le)
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
