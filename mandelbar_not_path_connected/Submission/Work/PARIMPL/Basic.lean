/-
Copyright: subproject `Submission/Work/PARIMPL/` of `mandelbar_not_path_connected`.

# `Work.PARIMPL` — the implosion side of the mandelbar endgame: vocabulary

Area `Submission/Work/PARIMPL/` — the formal chapter for
`Submission/Work/NOTES_LEAD_mandelbar_residuals.md` §1 (items 1.1–1.5) and §4: the
**implosion side** `Nm` of the parabolic root arc, the **parameter normal form**
(Hubbard–Schleicher, *Multicorns are not Path Connected*, Prop. 4.1, uniform in `c`), the
**MATCH** of the approximate perturbed Fatou coordinate with the Leau–Fatou flower at `c₀`,
the **TRANSIT** coordinate with its phase blow-up, the **LEAK** disc, and the **PATH**
statement `noPath` (the `hLB` of the endgame, in path form).

## What this module fixes

* `gtc c = (T_c)^[5]`, the antiholomorphic square root of `Ft c = Work.EL.F c = (T_c)^[10]`;
* `ParBounds` — the uniform smallness of the germ `h` of the normal form in the **rotated**
  normalization of the residuals note §1.1: `h ζ = τ + h₁ ζ + O(ζ²)` with `‖τ‖ = 1`;
* `GoodTransitRot` — the transit regime of the rotated normal form (the `h(0) = τ` analogue of
  `Work.Implosion.GoodTransit`);
* `ParNormal d` — the **parameter normal form** at a root-arc parameter
  `d : Work.EL.RootParabolic c₀`: the charts `z = m c + s c·ζ`, the roots `a c` of `a₂ c`, the
  germs `h c` with their first coefficients `h₁ c` and the normalization constant `κ c`, the
  conjugation of the second return map `F c` to `ζ + (ζ² − a²)h ζ` on the chart ball, the
  uniform bounds, and the two **splitting** statements `swap`/`fix` for the antiholomorphic
  square root `g c` (which side period-5 points die on);
* `ParNormal.Nm`, `ParNormal.Par`, `ParNormal.Np` — the three sides `a₂ < 0`, `a₂ = 0`,
  `a₂ > 0` of the parabolic locus;
* `ImplSide` — the structural properties of the implosion side, with the *same field names and
  types* as `Work.Final.ImplosionSide` (`Submission/Work/PARIMPL/Bridge.lean` converts).

## Conventions

* `a₂` is `ℝ`-valued (its realness is part of the normal form, as in the design's `a2_real`);
  `a c` is a chosen square root, `a c ^ 2 = (a₂ c : ℂ)`.
* `Nm` is the **implosion side**: there `a₂ < 0`, hence the normal form has the two *repelling*
  fixed points `±a` with `a = i·λ`, `λ = lam c > 0` — the "eggbeater" situation of HS §4.
* The rotation `e^{iθ_c}` of §1.1 is *absorbed into `h`*: `h c 0` is the modulus-one constant
  `τ c`, and the correction constant of the approximate Écalle coordinate is
  `κ c = τ c − h₁ c/τ c` (for `τ = 1` this is `1 − h₁`, the `κ` of `Work.Implosion.Approx`).
  See `Submission/Work/PARIMPL/NOTES.md` for the derivation of the cancellation condition.
-/
import Submission.Work.ELRig.Defs
import Submission.Work.Implosion.All
import Submission.Work.Implosion.Approx.approxEcal_step
import Submission.Work.Implosion.Approx.approxEcal_transit

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option linter.unusedVariables false

open Classical Filter Set Metric
open scoped Topology

noncomputable section

namespace Work.PARIMPL

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

variable {c₀ : ℂ}

/-! ## The two maps -/

/-- `g c = (T_c)^[5]`: the antiholomorphic square root of `Work.EL.F c = (T_c)^[10]`. -/
abbrev gtc (c : ℂ) : ℂ → ℂ := (Tantibar c)^[5]

/-- `Work.EL.F` under a shorter name: `Ft c = (T_c)^[10] = (gtc c) ∘ (gtc c)`. -/
abbrev Ft (c : ℂ) : ℂ → ℂ := Work.EL.F c

theorem Ft_eq_tantibar (c : ℂ) : Ft c = (Tantibar c)^[10] := Work.EL.F_eq_tantibar c

/-- `F = g ∘ g`: the second return map is the square of the antiholomorphic first return. -/
theorem Ft_eq_g_comp (c : ℂ) : Ft c = gtc c ∘ gtc c := by
  rw [Ft_eq_tantibar]
  funext z
  simp only [Function.comp_apply, gtc]
  rw [show (10 : ℕ) = 5 + 5 from rfl, Function.iterate_add_apply]

theorem Ft_fixed_of_gtc_fixed {c z : ℂ} (h : gtc c z = z) : Ft c z = z := by
  rw [Ft_eq_g_comp, Function.comp_apply, h, h]

theorem continuous_tantibar (c : ℂ) : Continuous (Tantibar c) := by
  unfold LeanEval.ComplexAnalysis.Tantibar
  fun_prop

theorem gtc_continuous (c : ℂ) : Continuous (gtc c) :=
  (continuous_tantibar c).iterate 5

/-! ## The uniform bounds of the rotated normal form -/

/-- The uniform smallness hypotheses of the local model, in the **rotated** normalization of
`NOTES_LEAD_mandelbar_residuals.md` §1.1:

* `h ζ = τ + h₁ ζ + O(ζ²)` on `‖ζ‖ < r`, with `‖τ‖ = 1`;
* the rotation is small, `‖τ − 1‖ ≤ 1/2` — in the geometry `τ = e^{iθ_c}` with `θ_c = O(λ_c)`,
  so this is a weak consequence;
* `h` is bounded by `2` and bounded away from `0` by `1/2` on the chart ball.

For `τ = 1` and without the last three conjuncts this is
`Work.Implosion.Approx.ImplosionBounds`. -/
def ParBounds (h : ℂ → ℂ) (τ h1 : ℂ) (A r : ℝ) : Prop :=
  0 < r ∧ ‖τ‖ = 1 ∧ (∀ ζ : ℂ, ‖ζ‖ < r → ‖h ζ - τ - h1 * ζ‖ ≤ A * ‖ζ‖ ^ 2) ∧
    (∀ ζ : ℂ, ‖ζ‖ < r → ‖h ζ‖ ≤ 2) ∧ (∀ ζ : ℂ, ‖ζ‖ < r → 1 / 2 ≤ ‖h ζ‖) ∧
    ‖τ - 1‖ ≤ 1 / 2

theorem ParBounds.h_zero {h : ℂ → ℂ} {τ h1 : ℂ} {A r : ℝ} (hb : ParBounds h τ h1 A r) :
    h 0 = τ := by
  have h1 := hb.2.2.1 0 (by simpa using hb.1)
  have : ‖h 0 - τ‖ ≤ A * ‖(0 : ℂ)‖ ^ 2 := by simpa using h1
  simp only [norm_zero, pow_two, mul_zero] at this
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm this (norm_nonneg _)))

theorem ParBounds.h_ne_zero {h : ℂ → ℂ} {τ h1 : ℂ} {A r : ℝ} (hb : ParBounds h τ h1 A r)
    {ζ : ℂ} (hζ : ‖ζ‖ < r) : h ζ ≠ 0 := by
  intro h0
  have := hb.2.2.2.2.1 ζ hζ
  rw [h0, norm_zero] at this
  norm_num at this

/-- The **transit regime** of the rotated normal form: the `h(0) = τ` analogue of
`Work.Implosion.GoodTransit`.  It is the region on which the per-step error of the approximate
Écalle coordinate is `O(‖ζ‖² + λ²)`.

Besides the strip, the smallness of `ζ`, the slit-plane condition and the bounds
`‖h − τ‖ ≤ 1/2`, `‖h‖ ≤ 2` of `GoodTransit`, it records the *unrotated* bound
`‖h (ζ) − 1‖ ≤ 1/2`: this is what makes the real part of the model displacement strictly
negative (so that the transit lasts `≈ π/λ` steps, uniformly in the number of steps) even when
`τ ≠ 1`.  In the geometry both hold, because `‖τ − 1‖ = O(λ)` and `‖ζ‖ ≤ 1/4`. -/
def GoodTransitRot (a : ℂ) (h : ℂ → ℂ) (τ : ℂ) (lam R : ℝ) (u : ℂ) : Prop :=
  u ∈ Work.Implosion.transitStrip lam R ∧ 4 ≤ R ∧
    4 * (‖Work.Implosion.ecalPt a u‖ + lam) ≤ 1 ∧
    ‖h (Work.Implosion.ecalPt a u) - τ‖ ≤ 1 / 2 ∧
    ‖h (Work.Implosion.ecalPt a u) - 1‖ ≤ 1 / 2 ∧
    ‖h (Work.Implosion.ecalPt a u)‖ ≤ 2 ∧
    Complex.sinh (a * u) / a ∈ Complex.slitPlane

theorem mem_transitStrip_iff (lam R : ℝ) (u : ℂ) :
    u ∈ Work.Implosion.transitStrip lam R ↔ R ≤ u.re ∧ u.re ≤ Real.pi / lam - R :=
  Work.Implosion.mem_transitStrip_iff lam R u

/-! ## The parameter normal form (HS Prop. 4.1, uniform in `c`) -/

/-- **The parameter normal form** of the parabolic root arc at `c₀`: Hubbard–Schleicher
Prop. 4.1, uniform in the parameter `c` on a ball around `c₀`, in the rotated normalization of
`NOTES_LEAD_mandelbar_residuals.md` §1.1.

* `m c + s c·ζ` is the chart in which the second return map `Ft c = (T_c)^[10]` takes the
  normal form `ζ + (ζ² − a_c²)·h_c(ζ)`;
* `a c` is a chosen square root of `a₂ c = a c²` (the square of the root is the real number
  `a₂ c`); on the implosion side `Nm = {a₂ < 0}` the choice is normalized to `a c = lam c·i`
  with `lam c > 0`.  **`a` is only a pointwise square root**: it is *not* continuous on a
  neighbourhood of `c₀` — only `a₂ = a²` is (HS §4: "`a_c` may not be a continuous function in a
  neighborhood of `c`, but `a_c²` is").  All the estimates of this chapter are pointwise in `c`,
  and every consumer lives on `Nm`, where `a = i·√(−a₂)` *is* continuous:
  `ParNormal.continuousOn_a_Nm`;
* `h c 0 =: τ c` has modulus one (the rotation `e^{iθ_c}` of §1.1 is absorbed into `h`), and
  `κ c = τ c − h₁ c/τ c` is the constant of the approximate Écalle coordinate that makes the
  per-step error `O(‖ζ‖² + λ²)` — cf. `Work.PARIMPL.approxEcal_step_rot`;
* `swap`/`fix` are the two **splitting** statements for the antiholomorphic square root
  `g c = (T_c)^[5]`: on `Nm` the root *swaps* the two split fixed points `m c ± s c·a c`
  (so no period-`5` point survives near `z₁`), on `Np` it *fixes* both. -/
structure ParNormal (d : Work.EL.RootParabolic c₀) where
  /-- radius of the parameter ball on which the normal form is uniform. -/
  ρ₀ : ℝ
  hρ₀ : 0 < ρ₀
  /-- radius of the chart ball `‖ζ‖ < r`. -/
  r : ℝ
  hr : 0 < r
  /-- the midpoint of the two split fixed points. -/
  m : ℂ → ℂ
  /-- the scale of the chart. -/
  s : ℂ → ℂ
  /-- the chosen square root of `a₂`. -/
  a : ℂ → ℂ
  /-- `a₂ c = (a c)²`, real-valued. -/
  a2 : ℂ → ℝ
  /-- the germ of the normal form (in `(c, ζ)`). -/
  h : ℂ → ℂ → ℂ
  /-- the linear coefficient of the germ. -/
  h1 : ℂ → ℂ
  /-- the correction constant of the approximate Écalle coordinate. -/
  κ : ℂ → ℂ
  /-- the positive scale on the implosion side. -/
  lam : ℂ → ℝ
  /-- the constant of the uniform bounds. -/
  A : ℝ
  hA : 0 ≤ A
  cont_m : ContinuousOn m (ball c₀ ρ₀)
  cont_s : ContinuousOn s (ball c₀ ρ₀)
  cont_a2 : ContinuousOn a2 (ball c₀ ρ₀)
  cont_h1 : ContinuousOn h1 (ball c₀ ρ₀)
  cont_κ : ContinuousOn κ (ball c₀ ρ₀)
  cont_τ : ContinuousOn (fun c => h c 0) (ball c₀ ρ₀)
  cont_h : ContinuousOn (fun p : ℂ × ℂ => h p.1 p.2) (ball c₀ ρ₀ ×ˢ ball (0 : ℂ) r)
  s_ne : ∀ c ∈ ball c₀ ρ₀, s c ≠ 0
  a_sq : ∀ c ∈ ball c₀ ρ₀, a c ^ 2 = ((a2 c : ℝ) : ℂ)
  m₀ : m c₀ = d.z₁
  a2₀ : a2 c₀ = 0
  κ_eq : ∀ c ∈ ball c₀ ρ₀, h c 0 ≠ 0 ∧ κ c = h c 0 - h1 c / (h c 0)
  /-- the conjugation of the return map to the normal form on the chart ball. -/
  conj : ∀ c ∈ ball c₀ ρ₀, ∀ ζ ∈ ball (0 : ℂ) r,
    Ft c (m c + s c * ζ) = m c + s c * Work.Implosion.normalForm (a c) (h c) ζ
  bounds : ∀ c ∈ ball c₀ ρ₀, ParBounds (h c) (h c 0) (h1 c) A r
  /-- on the implosion side the chosen root is `lam c·i` with `lam c > 0`. -/
  a_eq : ∀ c ∈ ball c₀ ρ₀, a2 c < 0 → a c = (lam c : ℂ) * Complex.I
  lam_pos : ∀ c ∈ ball c₀ ρ₀, a2 c < 0 → 0 < lam c
  /-- on `Nm` the antiholomorphic square root **swaps** the two split fixed points. -/
  swap : ∀ c ∈ ball c₀ ρ₀, a2 c < 0 →
    gtc c (m c + s c * a c) = m c - s c * a c
  /-- on `Np` the antiholomorphic square root **fixes** both split fixed points. -/
  fix : ∀ c ∈ ball c₀ ρ₀, 0 < a2 c →
    gtc c (m c + s c * a c) = m c + s c * a c ∧
      gtc c (m c - s c * a c) = m c - s c * a c

namespace ParNormal

variable {d : Work.EL.RootParabolic c₀} (P : ParNormal d)

/-- **The implosion side**: the parameters in the normal-form ball at which `a₂ < 0`, i.e.
where the period-`5` point near `z₁` has imploded into a pair of repelling fixed points. -/
def Nm : Set ℂ := {c : ℂ | c ∈ ball c₀ P.ρ₀ ∧ P.a2 c < 0}

/-- **The parabolic locus**: `a₂ = 0`, the parameters at which the two roots collide. -/
def Par : Set ℂ := {c : ℂ | c ∈ ball c₀ P.ρ₀ ∧ P.a2 c = 0}

/-- **The other side**: `a₂ > 0`, where the period-`5` point survives (a pair of fixed
points of `g`, one of them attracting). -/
def Np : Set ℂ := {c : ℂ | c ∈ ball c₀ P.ρ₀ ∧ 0 < P.a2 c}

@[simp] theorem mem_Nm {c : ℂ} : c ∈ P.Nm ↔ c ∈ ball c₀ P.ρ₀ ∧ P.a2 c < 0 := Iff.rfl

@[simp] theorem mem_Par {c : ℂ} : c ∈ P.Par ↔ c ∈ ball c₀ P.ρ₀ ∧ P.a2 c = 0 := Iff.rfl

@[simp] theorem mem_Np {c : ℂ} : c ∈ P.Np ↔ c ∈ ball c₀ P.ρ₀ ∧ 0 < P.a2 c := Iff.rfl

theorem Nm_subset_ball : P.Nm ⊆ ball c₀ P.ρ₀ := fun _ h => h.1

theorem Par_subset_ball : P.Par ⊆ ball c₀ P.ρ₀ := fun _ h => h.1

theorem Np_subset_ball : P.Np ⊆ ball c₀ P.ρ₀ := fun _ h => h.1

theorem a2_neg_of_mem_Nm {c : ℂ} (h : c ∈ P.Nm) : P.a2 c < 0 := h.2

theorem a2_pos_of_mem_Np {c : ℂ} (h : c ∈ P.Np) : 0 < P.a2 c := h.2

theorem a2_zero_of_mem_Par {c : ℂ} (h : c ∈ P.Par) : P.a2 c = 0 := h.2

/-- On the implosion side the chosen root is purely imaginary with positive imaginary part. -/
theorem a_of_mem_Nm {c : ℂ} (h : c ∈ P.Nm) : P.a c = (P.lam c : ℂ) * Complex.I :=
  P.a_eq c h.1 h.2

theorem lam_pos_of_mem_Nm {c : ℂ} (h : c ∈ P.Nm) : 0 < P.lam c := P.lam_pos c h.1 h.2

/-- On the implosion side, `a₂ = −λ²`. -/
theorem a2_eq_neg_sq {c : ℂ} (h : c ∈ P.Nm) : P.a2 c = -(P.lam c) ^ 2 := by
  have hs := P.a_sq c h.1
  rw [P.a_of_mem_Nm h] at hs
  have hI : ((P.lam c : ℂ) * Complex.I) ^ 2 = -(((P.lam c) ^ 2 : ℝ) : ℂ) := by
    rw [mul_pow, Complex.I_sq, Complex.ofReal_pow]; ring
  rw [hI] at hs
  rw [← Complex.ofReal_neg] at hs
  exact_mod_cast (Complex.ofReal_inj.mp hs).symm

/-- On the implosion side, the normal form at `ζ = 0` is `λ²·h 0`. -/
theorem normalForm_zero_of_mem_Nm {c : ℂ} (h : c ∈ P.Nm) :
    Work.Implosion.normalForm (P.a c) (P.h c) 0 = ((P.lam c) ^ 2 : ℝ) * P.h c 0 := by
  rw [Work.Implosion.normalForm_zero, P.a_sq c h.1, P.a2_eq_neg_sq h]
  push_cast
  ring

/-- The implosion side is open. -/
theorem isOpen_Nm : IsOpen P.Nm := by
  rw [isOpen_iff_mem_nhds]
  intro c hc
  refine Filter.inter_mem (isOpen_ball.mem_nhds hc.1) ?_
  exact (P.cont_a2.continuousAt (isOpen_ball.mem_nhds hc.1)).preimage_mem_nhds
    (isOpen_Iio.mem_nhds hc.2)

/-- The other side `Np` is open. -/
theorem isOpen_Np : IsOpen P.Np := by
  rw [isOpen_iff_mem_nhds]
  intro c hc
  refine Filter.inter_mem (isOpen_ball.mem_nhds hc.1) ?_
  exact (P.cont_a2.continuousAt (isOpen_ball.mem_nhds hc.1)).preimage_mem_nhds
    (isOpen_Ioi.mem_nhds hc.2)

theorem disjoint_Nm_Np : Disjoint P.Nm P.Np := by
  rw [Set.disjoint_left]
  intro c h1 h2
  exact absurd h1.2 (not_lt.mpr (le_of_lt h2.2))

/-- On the closure of the implosion side (inside the normal-form ball), `a₂ ≤ 0`. -/
theorem closure_Nm_subset : closure P.Nm ∩ ball c₀ P.ρ₀ ⊆ {c : ℂ | P.a2 c ≤ 0} := by
  intro c hc
  obtain ⟨hcl, hball⟩ := hc
  by_contra hcon
  have hcon' : 0 < P.a2 c := lt_of_not_ge hcon
  have hmem : c ∈ P.Np := ⟨hball, hcon'⟩
  have hnhds : P.Np ∈ 𝓝 c := P.isOpen_Np.mem_nhds hmem
  rw [mem_closure_iff_nhds] at hcl
  obtain ⟨y, hyNp, hyNm⟩ := hcl P.Np hnhds
  exact absurd hyNp.2 (not_lt.mpr (le_of_lt hyNm.2))

/-- A point of the closure of the implosion side, inside the normal-form ball, which is not
itself on the implosion side, lies on the parabolic locus. -/
theorem a2_zero_of_closure_notMem {c : ℂ} (hcl : c ∈ closure P.Nm)
    (hball : c ∈ ball c₀ P.ρ₀) (hnot : c ∉ P.Nm) : P.a2 c = 0 := by
  have hle : P.a2 c ≤ 0 := P.closure_Nm_subset ⟨hcl, hball⟩
  rcases lt_or_eq_of_le hle with hlt | heq
  · exact absurd ⟨hball, hlt⟩ hnot
  · exact heq

/-- On the implosion side, `λ = √(−a₂)`. -/
theorem lam_eq_sqrt_of_mem_Nm {c : ℂ} (h : c ∈ P.Nm) :
    P.lam c = Real.sqrt (-(P.a2 c)) := by
  have hsq := P.a2_eq_neg_sq h
  have hpos : 0 < P.lam c := P.lam_pos_of_mem_Nm h
  have : (P.lam c) ^ 2 = -(P.a2 c) := by linarith [hsq]
  rw [← this, Real.sqrt_sq (le_of_lt hpos)]

/-- `λ` tends to `0` along the implosion side at a point of the parabolic locus. -/
theorem tendsto_lam (a : ℂ) (ha : P.a2 a = 0) (hab : a ∈ ball c₀ P.ρ₀) :
    Tendsto P.lam (𝓝[P.Nm] a) (𝓝 0) := by
  have hcont : Tendsto (fun c => P.a2 c) (𝓝[P.Nm] a) (𝓝 (P.a2 a)) :=
    ((P.cont_a2.continuousAt (isOpen_ball.mem_nhds hab)).tendsto).mono_left inf_le_left
  rw [ha] at hcont
  have hsqrt : Tendsto (fun c => Real.sqrt (-(P.a2 c))) (𝓝[P.Nm] a) (𝓝 0) := by
    have h1 : Tendsto (fun c => -(P.a2 c)) (𝓝[P.Nm] a) (𝓝 0) := by
      have := hcont.neg
      simpa using this
    simpa using h1.sqrt
  refine hsqrt.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with c hc
  exact (P.lam_eq_sqrt_of_mem_Nm hc).symm

/-- On the implosion side, `λ = √(−a₂)` is continuous. -/
theorem continuousOn_lam_Nm : ContinuousOn P.lam P.Nm := by
  have hcont : ContinuousOn (fun c => -(P.a2 c)) P.Nm :=
    (P.cont_a2.mono (fun c hc => hc.1)).neg
  have h := Real.continuous_sqrt.comp_continuousOn hcont
  exact h.congr (fun c hc => P.lam_eq_sqrt_of_mem_Nm hc)

/-- On the implosion side the square root `a = i·√(−a₂)` **is** continuous.  This is the only
continuity that the construction provides: `a` itself is not continuous on a full neighbourhood
of `c₀` (only `a₂ = a²` is, HS §4), and every consumer of this chapter works on `Nm`. -/
theorem continuousOn_a_Nm : ContinuousOn P.a P.Nm := by
  have h : ContinuousOn (fun c => (P.lam c : ℂ) * Complex.I) P.Nm :=
    (Complex.continuous_ofReal.comp_continuousOn P.continuousOn_lam_Nm).mul continuousOn_const
  exact h.congr (fun c hc => P.a_of_mem_Nm hc)

/-- The normal form's two fixed points in the chart: `ζ = ±a`, whenever `h ≠ 0` on the chart
ball. -/
theorem normalForm_eq_self_iff {c : ℂ} (hc : c ∈ ball c₀ P.ρ₀) {ζ : ℂ}
    (hζ : ‖ζ‖ < P.r) :
    Work.Implosion.normalForm (P.a c) (P.h c) ζ = ζ ↔ (ζ = P.a c ∨ ζ = -P.a c) := by
  have hne : P.h c ζ ≠ 0 := (P.bounds c hc).h_ne_zero hζ
  constructor
  · intro h
    have h' : (ζ ^ 2 - (P.a c) ^ 2) * P.h c ζ = 0 := by
      have h1 : ζ + (ζ ^ 2 - (P.a c) ^ 2) * P.h c ζ = ζ + 0 := by
        rw [add_zero]
        simpa [Work.Implosion.normalForm] using h
      exact add_left_cancel h1
    have hsq : ζ ^ 2 - (P.a c) ^ 2 = 0 := by
      rcases mul_eq_zero.mp h' with h3 | h3
      · exact h3
      · exact absurd h3 hne
    have hfac : (ζ - P.a c) * (ζ + P.a c) = 0 := by
      linear_combination hsq
    rcases mul_eq_zero.mp hfac with hz | hz
    · exact Or.inl (sub_eq_zero.mp hz)
    · exact Or.inr (by linear_combination hz)
  · rintro (rfl | rfl)
    · exact Work.Implosion.normalForm_fixed_left _ _
    · exact Work.Implosion.normalForm_fixed_right _ _

/-- **The period-`5` point near `z₁` has disappeared on the implosion side**: on `Nm` (near
`c₀`) the antiholomorphic square root `g c = (T_c)^[5]` has no fixed point in a ball around
`z₁`.  Equivalently: `z₁`'s period-`5` cycle has imploded into a pair of period-`10` points
which `g` swaps (`swap`).  This is the third field of `Work.Final.ImplosionSide`. -/
def PeriodFiveGone (P : ParNormal d) : Prop :=
  ∃ ρ : ℝ, 0 < ρ ∧ ∃ δ : ℝ, 0 < δ ∧
    ∀ c' ∈ P.Nm ∩ ball c₀ ρ, ∀ z ∈ ball d.z₁ δ, gtc c' z ≠ z

end ParNormal

/-- **The implosion side of the root arc**: the structural properties consumed by the endgame,
with the *same field names and types* as `Work.Final.ImplosionSide`
(`Submission/Work/PARIMPL/Bridge.lean` converts them verbatim). -/
structure ImplSide (c z₁ : ℂ) (Nm : Set ℂ) : Prop where
  /-- the implosion side is open. -/
  isOpen_Nm : IsOpen Nm
  /-- the implosion side accumulates at the root parameter. -/
  c_mem_closure : c ∈ closure Nm
  /-- on the implosion side the period-`5` point near `z₁` has disappeared. -/
  period_five_gone : ∃ ρ : ℝ, 0 < ρ ∧ ∃ δ : ℝ, 0 < δ ∧
    ∀ c' ∈ Nm ∩ ball c ρ, ∀ z ∈ ball z₁ δ, (Tantibar c')^[5] z ≠ z

namespace ParNormal

variable {d : Work.EL.RootParabolic c₀} (P : ParNormal d)

/-- The implosion side data, from the parameter normal form, the accumulation of `Nm` at `c₀`
(the `FBif` side, a named hypothesis) and the disappearance of the period-`5` point. -/
theorem toImplSide (hcl : c₀ ∈ closure P.Nm) (hg : P.PeriodFiveGone) : ImplSide c₀ d.z₁ P.Nm :=
  ⟨P.isOpen_Nm, hcl, hg⟩

/-- The root parameter is **not** on the implosion side: `z₁` is a fixed point of
`g c₀ = (T_{c₀})^[5]` (`Work.EL.RootParabolic.per_half`), while on `Nm` no such point survives
near `z₁`.  Hence `c₀ ∈ closure Nm \ Nm`. -/
theorem notMem_Nm (hg : P.PeriodFiveGone) (hcl : c₀ ∈ closure P.Nm) : c₀ ∉ P.Nm := by
  intro hc
  obtain ⟨ρ, hρ, δ, hδ, hgone⟩ := hg
  have hcρ : c₀ ∈ P.Nm ∩ ball c₀ ρ := ⟨hc, by simpa using hρ⟩
  have hz : d.z₁ ∈ ball d.z₁ δ := by simpa using hδ
  exact hgone c₀ hcρ d.z₁ hz d.per_half

/-- The root parameter lies on the frontier of the implosion side. -/
theorem mem_frontier_Nm (hg : P.PeriodFiveGone) (hcl : c₀ ∈ closure P.Nm) :
    c₀ ∈ frontier P.Nm := by
  rw [frontier_eq_closure_inter_closure, P.isOpen_Nm.isClosed_compl.closure_eq]
  exact ⟨hcl, P.notMem_Nm hg hcl⟩

end ParNormal

end Work.PARIMPL
