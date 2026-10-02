/-
# The mandelbar: the parameter Böttcher map, external angles and parameter rays

This file is the **interface** of the parameter-ray area, matching the names requested by the
lead in `Submission/Work/NOTES_LEAD_mandelbar_arc_top.md` §1:

* `Mb`        : the mandelbar `LeanEval.ComplexAnalysis.Mandelbar`.
* `Phi`       : the parameter Böttcher map `Φ c = φ_c(c)` of Nakane; junk value `0` on `Mb`.
  Here `φ_c` is a **critical** Böttcher coordinate, `IsCritBottcher c φ_c`, i.e. a Böttcher
  coordinate on `critDomain c = {G_c > G_c 0}`: this is the only form in which Böttcher's
  theorem is true off the mandelbar (`IsDynBottcher` is satisfiable only for `c ∈ M*`).
* `extAngle`  : the external angle of a parameter outside `Mb`, in `[0,1)`.
* `potential` : `log ‖Φ c‖` outside `Mb`, `0` on `Mb`.
* `paramRay θ`: the parameter ray `R(θ) = {c ∉ Mb : Φ c = r e^{2πiθ}, r > 1}`.
* `equipotential R`, `equipotentialArc R β₁ β₂`, `circleArc R β₁ β₂`.

The classical inputs are packaged as the structure `NakaneInput`, to be taken as a hypothesis
(it bundles Böttcher's theorem *on the critical domain* — `BottcherExists c = ∃ φ, IsCritBottcher c φ` —
the uniform asymptotic `Φ c / c → 1`, and Nakane's theorem that
`Φ` is a homeomorphism of `ℂ \ Mb` onto `‖w‖ > 1`).  The endgame consumes the interface through
`Phi_homeo` and `Phi_isBigO_atTop`.

## Main definitions and results

* `Work.ParamRays.Phi`, `Work.ParamRays.extAngle`, `Work.ParamRays.potential`,
  `Work.ParamRays.paramRay`, `Work.ParamRays.equipotentialArc`, `Work.ParamRays.NakaneInput`.
* `Work.ParamRays.Phi_homeo`, `Work.ParamRays.Phi_isBigO_atTop`.
* `Work.ParamRays.quarter_mem` : `1/4 ∈ Mb` (the period-1 parabolic parameter).
-/
import Submission.Work.ParamRays.Bottcher

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Filter
open scoped Real Topology ComplexConjugate
open Classical

namespace Work.ParamRays

open LeanEval.ComplexAnalysis (Tantibar)

/-- The mandelbar (tricorn), the connectedness locus of `z ↦ z̄² + c`. -/
abbrev Mb : Set ℂ := LeanEval.ComplexAnalysis.Mandelbar

/-- The parameter Böttcher map of Nakane: `Φ c = φ_c(c)` is the value at the critical value of
a **critical** Böttcher coordinate of `T_c` (a Böttcher coordinate on
`critDomain c = {G_c > G_c 0}`, which contains `c` whenever `c ∉ Mb`), for `c` outside the
mandelbar.  If no critical Böttcher coordinate is available, and in particular on the
mandelbar, the value is the junk value `0`.

The value is independent of the choice of `φ_c` by `isCritBottcher_unique` applied at the
critical value (`self_mem_critDomain`); see `Phi_eq_of_isCritBottcher`. -/
noncomputable def Phi (c : ℂ) : ℂ :=
  if hc : c ∈ LeanEval.ComplexAnalysis.Mandelbar then 0
  else if h : ∃ φ : ℂ → ℂ, IsCritBottcher c φ then (Classical.choose h) c
  else 0

theorem Phi_eq_zero_of_mem {c : ℂ} (hc : c ∈ Mb) : Phi c = 0 := by
  rw [Phi, dif_pos hc]

theorem Phi_eq_choose {c : ℂ} (hc : c ∉ Mb) (h : ∃ φ : ℂ → ℂ, IsCritBottcher c φ) :
    Phi c = (Classical.choose h) c := by
  rw [Phi, dif_neg hc, dif_pos h]

/-- **Nakane's theorem** (the held structural input): the parameter Böttcher map is a
homeomorphism of the exterior of the mandelbar onto the exterior of the unit disk.  This is the
statement `Phi_homeo` of the lead's interface note, packaged as a proposition so that it can be
used as a hypothesis. -/
def NakaneHomeo : Prop :=
  ∃ e : (↥(Mbᶜ) ≃ₜ ↥{w : ℂ | 1 < ‖w‖}), ∀ c : ↥(Mbᶜ), (e c : ℂ) = Phi c

/-- The **uniform asymptotic input**: for every `ε > 0`, every critical Böttcher coordinate of
`T_c` is `ε`-close to the identity at the critical value, for all sufficiently large parameters
`c`.

This uniformity in the parameter is *not* implied by the pointwise definition `IsCritBottcher`
(whose third clause is a statement about one fixed `φ_c`); it follows from the explicit product
formula for the Böttcher coordinate (`Φ c / c → 1`). -/
def UniformBottcherAsymptotic : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ c : ℂ in Filter.cocompact ℂ,
    ∀ φ : ℂ → ℂ, IsCritBottcher c φ → ‖φ c - c‖ ≤ ε * ‖c‖

/-- **The Nakane input bundle.**  The classical structural inputs of the parameter theory, taken
as hypotheses by the endgame (`TOP`):

* `bottcher` : critical Böttcher coordinates exist outside the mandelbar (Böttcher's theorem);
* `uniform` : the uniform asymptotic `Φ c / c → 1` at infinity;
* `homeo`   : `Φ` is a homeomorphism of `ℂ \\ Mb` onto `‖w‖ > 1` (Nakane's theorem). -/
structure NakaneInput : Prop where
  /-- Critical Böttcher coordinates exist outside the mandelbar. -/
  bottcher : BottcherExists
  /-- `Φ` is asymptotic to the identity at infinity, uniformly in the parameter. -/
  uniform : UniformBottcherAsymptotic
  /-- `Φ` is a homeomorphism of the exterior of the mandelbar onto the exterior of the unit
  disk. -/
  homeo : NakaneHomeo

/-! ## External angles, the potential and parameter rays -/

/-- The point of the unit circle with external angle `θ` (in revolutions). -/
noncomputable def rayDir (θ : ℝ) : ℂ := Complex.exp (((2 * Real.pi * θ : ℝ) : ℂ) * Complex.I)

/-- The external angle (in revolutions, normalised to `[0,1)`) of a parameter outside the
mandelbar. -/
noncomputable def extAngle (c : ℂ) : ℝ :=
  toIcoMod one_pos 0 (Complex.arg (Phi c) / (2 * Real.pi))

/-- The potential of the mandelbar: `log ‖Φ c‖` outside `Mb` and `0` on `Mb`. -/
noncomputable def potential (c : ℂ) : ℝ := if hc : c ∈ Mb then 0 else Real.log ‖Phi c‖

theorem potential_eq_zero_of_mem {c : ℂ} (hc : c ∈ Mb) : potential c = 0 := by
  rw [potential, dif_pos hc]

/-- **The parameter ray** `R(θ)`: the parameters outside the mandelbar whose critical value has
external angle `θ`, equivalently `Φ c = r · e^{2πiθ}` with `r > 1`. -/
def paramRay (θ : ℝ) : Set ℂ :=
  {c : ℂ | c ∉ Mb ∧ ∃ r : ℝ, 1 < r ∧ Phi c = (r : ℂ) * rayDir θ}

theorem mem_paramRay {θ : ℝ} {c : ℂ} :
    c ∈ paramRay θ ↔ c ∉ Mb ∧ ∃ r : ℝ, 1 < r ∧ Phi c = (r : ℂ) * rayDir θ := Iff.rfl

theorem paramRay_subset (θ : ℝ) : paramRay θ ⊆ {c : ℂ | c ∉ Mb} := fun _ hc => hc.1

/-- The equipotential of level `R`: the parameters outside the mandelbar with `‖Φ c‖ = R`. -/
def equipotential (R : ℝ) : Set ℂ := {c : ℂ | c ∉ Mb ∧ ‖Phi c‖ = R}

theorem mem_equipotential {R : ℝ} {c : ℂ} :
    c ∈ equipotential R ↔ c ∉ Mb ∧ ‖Phi c‖ = R := Iff.rfl

/-- The circle arc of radius `R` from external angle `β₁` to external angle `β₂`
(counterclockwise), as a set of values of `Φ`. -/
def circleArc (R β₁ β₂ : ℝ) : Set ℂ :=
  {w : ℂ | ‖w‖ = R ∧ ∃ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 ∧ w = (R : ℂ) * rayDir (β₁ + s * (β₂ - β₁))}

/-- The equipotential arc of level `R` from the external angle `β₁` to the external angle `β₂`
(counterclockwise): its points are the parameters outside the mandelbar whose `Φ`-value lies on
the corresponding circle arc. -/
def equipotentialArc (R β₁ β₂ : ℝ) : Set ℂ :=
  {c : ℂ | c ∉ Mb ∧ Phi c ∈ circleArc R β₁ β₂}

theorem mem_equipotentialArc {R β₁ β₂ : ℝ} {c : ℂ} :
    c ∈ equipotentialArc R β₁ β₂ ↔ c ∉ Mb ∧ Phi c ∈ circleArc R β₁ β₂ := Iff.rfl

/-! ## Elementary facts about rays, angles and equipotential arcs -/

theorem norm_rayDir (θ : ℝ) : ‖rayDir θ‖ = 1 := by
  simp [rayDir, Complex.norm_exp]

theorem rayDir_add_one (θ : ℝ) : rayDir (θ + 1) = rayDir θ := by
  rw [rayDir, rayDir, show ((2 * Real.pi * (θ + 1) : ℝ) : ℂ) * Complex.I =
      ((2 * Real.pi * θ : ℝ) : ℂ) * Complex.I + 2 * ↑Real.pi * Complex.I by push_cast; ring,
    Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

/-- The external angle of a parameter lies in `[0,1)`. -/
theorem extAngle_mem_Ico (c : ℂ) : extAngle c ∈ Set.Ico (0 : ℝ) 1 := by
  have := toIcoMod_mem_Ico (p := (1 : ℝ)) one_pos (0 : ℝ)
    (Complex.arg (Phi c) / (2 * Real.pi))
  simpa [extAngle] using this

/-- The rays are periodic with period `1` in the angle. -/
theorem paramRay_add_one (θ : ℝ) : paramRay (θ + 1) = paramRay θ := by
  rw [paramRay, paramRay, rayDir_add_one]

theorem rayDir_add_int (θ : ℝ) (m : ℤ) : rayDir (θ + m) = rayDir θ := by
  have h1 : Complex.exp ((m : ℂ) * (2 * ↑Real.pi * Complex.I)) = 1 := by
    rw [Complex.exp_int_mul, Complex.exp_two_pi_mul_I, one_zpow]
  rw [rayDir, rayDir, show ((2 * Real.pi * (θ + m) : ℝ) : ℂ) * Complex.I =
      ((2 * Real.pi * θ : ℝ) : ℂ) * Complex.I + (m : ℂ) * (2 * ↑Real.pi * Complex.I) by
    push_cast; ring, Complex.exp_add, h1, mul_one]

/-- Two points of the unit circle agree exactly when their external angles differ by an
integer. -/
theorem rayDir_eq_iff {θ θ' : ℝ} : rayDir θ = rayDir θ' ↔ ∃ k : ℤ, θ' = θ + k := by
  constructor
  · intro h
    rw [rayDir, rayDir] at h
    obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp h
    have him : (2 * Real.pi * θ : ℝ) = 2 * Real.pi * θ' + (n : ℝ) * (2 * Real.pi) := by
      have := congrArg Complex.im hn
      simpa [Complex.mul_I_im, Complex.ofReal_re] using this
    refine ⟨-n, ?_⟩
    have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
    push_cast
    nlinarith
  · rintro ⟨k, rfl⟩
    exact (rayDir_add_int θ k).symm

/-- The rays are periodic with integer period in the angle. -/
theorem paramRay_add_int (θ : ℝ) (m : ℤ) : paramRay (θ + m) = paramRay θ := by
  rw [paramRay, paramRay, rayDir_add_int]

/-- A point of `Φ` of modulus `R` and angle `β₁` lies on the equipotential arc from `β₁`. -/
theorem mem_circleArc_left {R β₁ β₂ : ℝ} (hR : 0 ≤ R) :
    (R : ℂ) * rayDir β₁ ∈ circleArc R β₁ β₂ := by
  refine ⟨?_, 0, ⟨le_rfl, zero_le_one⟩, by rw [zero_mul, add_zero]⟩
  have hnorm : ‖(R : ℂ)‖ = R := by
    have h2 : ‖(R : ℂ)‖ ^ 2 = R ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal]; ring
    nlinarith [norm_nonneg (R : ℂ), hR]
  rw [norm_mul, norm_rayDir, mul_one, hnorm]

theorem mem_circleArc_right {R β₁ β₂ : ℝ} (hR : 0 ≤ R) :
    (R : ℂ) * rayDir β₂ ∈ circleArc R β₁ β₂ := by
  refine ⟨?_, 1, ⟨zero_le_one, le_rfl⟩, by rw [one_mul, add_sub_cancel]⟩
  have hnorm : ‖(R : ℂ)‖ = R := by
    have h2 : ‖(R : ℂ)‖ ^ 2 = R ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal]; ring
    nlinarith [norm_nonneg (R : ℂ), hR]
  rw [norm_mul, norm_rayDir, mul_one, hnorm]

/-! ## Elementary facts about the mandelbar -/

/-- Beyond the escape radius the mandelbar is empty, so cocompactly every parameter lies outside
it. -/
theorem eventually_not_mem_mandelbar :
    ∀ᶠ c : ℂ in Filter.cocompact ℂ, c ∉ Mb := by
  filter_upwards [tendsto_norm_cocompact_atTop.eventually_ge_atTop (3 : ℝ)] with c hc hmem
  have h2 := mandelbar_subset_closedBall hmem
  rw [Metric.mem_closedBall, dist_zero_right] at h2
  linarith

/-- The period-1 parabolic parameter `1/4` lies in the mandelbar. -/
theorem quarter_mem : (1/4 : ℂ) ∈ Mb := by
  rw [mem_mandelbar_iff]
  have h : ∀ n : ℕ, ‖critOrbit (1/4 : ℂ) n‖ ≤ 1/2 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [show critOrbit (1/4 : ℂ) (n + 1) = Tantibar (1/4) (critOrbit (1/4) n) from
        orbit_succ (1/4) 0 n]
      calc ‖Tantibar (1/4 : ℂ) (critOrbit (1/4) n)‖
          ≤ ‖critOrbit (1/4) n‖ ^ 2 + ‖(1/4 : ℂ)‖ := norm_Tantibar_le _ _
        _ = ‖critOrbit (1/4) n‖ ^ 2 + 1/4 := by norm_num
        _ ≤ (1/2 : ℝ) ^ 2 + 1/4 := by
              have := norm_nonneg (critOrbit (1/4 : ℂ) n)
              nlinarith
        _ = 1/2 := by norm_num
  intro n
  have := h n
  linarith

/-! ## The interface consumed by the endgame -/

/-- **Nakane's theorem**, in the form requested by the lead's interface note: there is a
homeomorphism of `ℂ \\ Mb` onto `{w : ℂ | 1 < ‖w‖}` which agrees with `Phi`. -/
theorem Phi_homeo (h : NakaneInput) :
    ∃ e : (↥(Mbᶜ) ≃ₜ ↥{w : ℂ | 1 < ‖w‖}), ∀ c : ↥(Mbᶜ), (e c : ℂ) = Phi c :=
  h.homeo

/-- `Phi` is asymptotic to the identity at infinity: `Φ c / c → 1`. -/
theorem Phi_isBigO_atTop (h : NakaneInput) :
    Filter.Tendsto (fun c : ℂ => Phi c / c) (Filter.cocompact ℂ) (nhds 1) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hε2 : 0 < ε / 2 := by linarith
  filter_upwards [h.uniform (ε / 2) hε2, eventually_not_mem_mandelbar] with c hc hcMb
  have hB : ∃ φ : ℂ → ℂ, IsCritBottcher c φ := h.bottcher c hcMb
  have hc0 : c ≠ 0 := fun h0 => hcMb (h0 ▸ zero_mem_mandelbar)
  have h1 : ‖Phi c - c‖ ≤ (ε / 2) * ‖c‖ := by
    rw [Phi_eq_choose hcMb hB]
    exact hc _ (Classical.choose_spec hB)
  have hcpos : 0 < ‖c‖ := norm_pos_iff.mpr hc0
  rw [dist_eq_norm, show Phi c / c - 1 = (Phi c - c) / c by rw [sub_div, div_self hc0],
    norm_div, div_lt_iff₀ hcpos]
  have : ε / 2 * ‖c‖ < ε * ‖c‖ := by nlinarith
  linarith

end Work.ParamRays
