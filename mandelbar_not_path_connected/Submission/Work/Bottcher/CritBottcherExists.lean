/-
# The critical Böttcher coordinate of the tricorn: existence, canonical choice, and rays

This file closes the BOT-2 area: it packages

`∀ c : ℂ, c ∉ M*, ∃ φ, IsCritBottcher c φ`

(`Work.ParamRays.BottcherExists`, the existence half of Böttcher's theorem for the family
`T_c(z) = z̄² + c` on the critical domain `{G_c > G_c 0}`), selects a **canonical** coordinate
`varphiCrit c` from it, and defines the dynamic rays `dynRayCrit c θ` of that canonical
coordinate together with the angle-doubling rule `θ ↦ -2θ`.

## Main results

* `Work.Bottcher.bottcherExists_crit : Work.ParamRays.BottcherExists` — the export requested by
  the parameter-ray interface.
* `Work.Bottcher.exists_isCritBottcher c : ∃ φ, IsCritBottcher c φ` (every parameter).
* `Work.Bottcher.varphiCrit`, `isCritBottcher_varphiCrit`, `varphiCrit_unique`,
  `norm_varphiCrit`, `varphiCrit_comm_Tantibar`, `varphiCrit_ne_zero`,
  `varphiCrit_div_tendsto_one`.
* `Work.Bottcher.PhiCrit : ℂ → ℂ` — the parameter Böttcher coordinate `φ_c(c)`, `0` on `M*`;
  with `PhiCrit_eq_of_isCritBottcher`, `norm_PhiCrit_eq_exp_green_self` and
  `norm_PhiCrit_eq_exp_two_greenParam`.
* `Work.Bottcher.dynRayCrit`, `mem_dynRayCrit`, `Tantibar_maps_dynRayCrit` (the angle-doubling
  rule `θ ↦ -2θ`), `dynRayCrit_period`.

## Warning

The *product formula* `Work.Bottcher.bottcher` is **not** a Böttcher coordinate of `T_c` outside
the far region `{escapeRadius c ≤ ‖z‖}`: it has a branch defect (see `NOTES.md` §4).  The
definitions `Work.Bottcher.Phi`, `Work.Bottcher.dynamicRay`, `Work.Bottcher.paramRay` use it only
as a formula and are therefore phase-ambiguous; consumers must use the analytic coordinate
`varphiCrit`/`PhiCrit` (or `Work.ParamRays.IsCritBottcher`) instead.
-/
import Mathlib
import Submission.Work.Bottcher.Defs
import Submission.Work.Bottcher.Basic
import Submission.Work.Bottcher.CritBasic
import Submission.Work.Bottcher.Contraction.exists_analyticBottcher_of_CritDomain
import Submission.Work.Bottcher.Contraction.bottcher_comm_Tantibar_on_CritDomain
import Submission.Work.Bottcher.Contraction.isPreconnected_green_le_greenParam
import Submission.Work.Bottcher.Contraction.bottcherExists_of_mem_mandelbar
import Submission.Work.ParamRaysCrit.All
import Submission.Work.ParamRays.Interface
import Submission.Work.ParamRays.PhiUnique
import Submission.Work.ParamRays.Phi_conj
import Submission.Work.ParamRays.Phi_smul_omega

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Filter
open scoped Topology ComplexConjugate
open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

namespace Work.Bottcher

noncomputable section

/-! ## Existence of the critical Böttcher coordinate -/

/-- The **analytic** form of a critical Böttcher coordinate: `Work.ParamRays.IsCritBottcher`
with `ContinuousOn` strengthened to `AnalyticOnNhd`.  This is the classical form of Böttcher's
theorem for the family `z ↦ z̄² + c` on the critical domain, and it is what this chapter proves. -/
def IsAnalyticCritBottcher (c : ℂ) (φ : ℂ → ℂ) : Prop :=
  AnalyticOnNhd ℂ φ (Work.ParamRays.critDomain c) ∧
    (∀ z : ℂ, z ∈ Work.ParamRays.critDomain c →
      φ (Tantibar c z) = conj (φ z) ^ 2) ∧
    (∀ ε : ℝ, 0 < ε → ∀ᶠ z : ℂ in Filter.cocompact ℂ, ‖φ z - z‖ ≤ ε * ‖z‖)

/-- An analytic Böttcher coordinate is in particular a critical Böttcher coordinate. -/
theorem IsAnalyticCritBottcher.isCritBottcher {c : ℂ} {φ : ℂ → ℂ}
    (h : IsAnalyticCritBottcher c φ) : Work.ParamRays.IsCritBottcher c φ :=
  ⟨h.1.continuousOn, h.2.1, h.2.2⟩

/-- **Böttcher's theorem for the tricorn on the critical domain** (analytic form).  For every
parameter `c` the critical domain `critDomain c = {G_c > G_c 0}` carries an analytic function
satisfying `φ (T_c z) = conj (φ z)^2` there and tangent to the identity at infinity.

The proof is the chapter's construction of the logarithm of `p_c z / z^4` on `CritDomain c`
(`Contraction.exists_analytic_log_normFactor_of_CritDomain`), the Böttcher series
`φ z = z · exp (Σ_k 4^{-(k+1)} L (p_c^k z))`
(`Contraction.exists_analyticBottcher_of_CritDomain`) and the passage from the holomorphic
Böttcher equation of `p_c = T_c ∘ T_c` to the antiholomorphic equation of `T_c`
(`Contraction.bottcher_comm_Tantibar_on_CritDomain`). -/
theorem exists_isAnalyticCritBottcher (c : ℂ) : ∃ φ : ℂ → ℂ, IsAnalyticCritBottcher c φ := by
  obtain ⟨φ, han, hfe, hmod, has⟩ :=
    Contraction.exists_analyticBottcher_of_CritDomain c
      (Contraction.isPreconnected_green_le_greenParam c)
  refine ⟨φ, ?_, ?_, ?_⟩
  · rw [← CritBasic.critDomain_eq c]
    exact han
  · intro z hz
    rw [← CritBasic.critDomain_eq c] at hz
    exact Contraction.bottcher_comm_Tantibar_on_CritDomain c φ han hfe hmod has z hz
  · intro ε hε
    exact Contraction.eventually_norm_sub_le_of_tendsto_div has hε

/-- **Böttcher's theorem for the tricorn on the critical domain.**  For every parameter `c` the
critical domain `critDomain c = {G_c > G_c 0}` carries a Böttcher coordinate of `T_c`: a function
satisfying `φ (T_c z) = conj (φ z)^2` there and tangent to the identity at infinity. -/
theorem exists_isCritBottcher (c : ℂ) : ∃ φ : ℂ → ℂ, Work.ParamRays.IsCritBottcher c φ := by
  obtain ⟨φ, h⟩ := exists_isAnalyticCritBottcher c
  exact ⟨φ, h.isCritBottcher⟩

/-- **The export for the parameter-ray interface.** -/
theorem bottcherExists_crit : Work.ParamRays.BottcherExists := fun c _ => exists_isCritBottcher c

/-! ## The canonical critical Böttcher coordinate -/

/-- The canonical critical Böttcher coordinate of `T_c`: chosen from the *analytic* existence
theorem (`IsCritBottcher` is a subsingleton on `critDomain c`,
`Work.ParamRays.isCritBottcher_unique`, so the choice is canonical for either formulation). -/
def varphiCrit (c : ℂ) : ℂ → ℂ := Classical.choose (exists_isAnalyticCritBottcher c)

theorem isAnalyticCritBottcher_varphiCrit (c : ℂ) :
    IsAnalyticCritBottcher c (varphiCrit c) :=
  Classical.choose_spec (exists_isAnalyticCritBottcher c)

/-- The canonical coordinate is analytic on the critical domain. -/
theorem analyticOnNhd_varphiCrit (c : ℂ) :
    AnalyticOnNhd ℂ (varphiCrit c) (Work.ParamRays.critDomain c) :=
  (isAnalyticCritBottcher_varphiCrit c).1

theorem isCritBottcher_varphiCrit (c : ℂ) : Work.ParamRays.IsCritBottcher c (varphiCrit c) :=
  (isAnalyticCritBottcher_varphiCrit c).isCritBottcher

theorem varphiCrit_continuousOn (c : ℂ) :
    ContinuousOn (varphiCrit c) (Work.ParamRays.critDomain c) :=
  (isCritBottcher_varphiCrit c).1

/-- Uniqueness: any critical Böttcher coordinate agrees with the canonical one. -/
theorem varphiCrit_unique {c : ℂ} {φ : ℂ → ℂ} (hφ : Work.ParamRays.IsCritBottcher c φ) {z : ℂ}
    (hz : z ∈ Work.ParamRays.critDomain c) : varphiCrit c z = φ z :=
  Work.ParamRays.isCritBottcher_unique (isCritBottcher_varphiCrit c) hφ hz

/-- The Böttcher equation of the canonical coordinate. -/
theorem varphiCrit_comm_Tantibar {c z : ℂ} (hz : z ∈ Work.ParamRays.critDomain c) :
    varphiCrit c (Tantibar c z) = conj (varphiCrit c z) ^ 2 :=
  (isCritBottcher_varphiCrit c).2.1 z hz

/-- The modulus of the canonical coordinate. -/
theorem norm_varphiCrit {c z : ℂ} (hz : z ∈ Work.ParamRays.critDomain c) :
    ‖varphiCrit c z‖ = Real.exp (Work.Bottcher.green c z) := by
  rw [Work.ParamRays.IsCritBottcher_modulus (isCritBottcher_varphiCrit c) hz,
    ← CritBasic.green_eq c z]

/-- The classical normalisation: on the critical domain the Böttcher coordinate lies *outside*
the unit circle (strictly, outside the circle of radius `exp (greenParam c)`, i.e. outside the
level `G_c 0`). -/
theorem one_lt_norm_varphiCrit {c z : ℂ} (hz : z ∈ Work.ParamRays.critDomain c) :
    1 < ‖varphiCrit c z‖ := by
  rw [norm_varphiCrit hz, ← Real.exp_zero]
  refine Real.exp_lt_exp.mpr ?_
  have h : Work.Bottcher.greenParam c < Work.Bottcher.green c z := by
    have h' := Work.ParamRays.mem_critDomain.mp hz
    rw [← CritBasic.green_eq, ← CritBasic.greenParam_eq] at h'
    exact h'
  have h0 := Work.Bottcher.Green.green_nonneg c 0
  rw [Work.Bottcher.greenParam_def] at h
  linarith

theorem varphiCrit_ne_zero {c z : ℂ} (hz : z ∈ Work.ParamRays.critDomain c) :
    varphiCrit c z ≠ 0 := by
  intro h
  have h1 := norm_varphiCrit hz
  rw [h, norm_zero] at h1
  have h2 := Real.exp_pos (Work.Bottcher.green c z)
  linarith

/-- Tangency at infinity, in quotient form. -/
theorem varphiCrit_div_tendsto_one (c : ℂ) :
    Tendsto (fun z : ℂ => varphiCrit c z / z) (Filter.cocompact ℂ) (nhds (1 : ℂ)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have htang : ∀ᶠ z : ℂ in Filter.cocompact ℂ,
      ‖varphiCrit c z - z‖ ≤ (ε / 2) * ‖z‖ :=
    (isCritBottcher_varphiCrit c).2.2 (ε / 2) (half_pos hε)
  have hbig : ∀ᶠ z : ℂ in Filter.cocompact ℂ, (1 : ℝ) ≤ ‖z‖ := by
    refine Filter.mem_of_superset
      (isCompact_closedBall (0 : ℂ) 1).compl_mem_cocompact ?_
    intro z hz
    rw [Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right, not_le] at hz
    exact le_of_lt hz
  filter_upwards [htang, hbig] with z hz hz1
  have hz0 : z ≠ 0 := by
    intro h
    rw [h, norm_zero] at hz1
    linarith
  have hpos : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  rw [dist_eq_norm, show varphiCrit c z / z - 1 = (varphiCrit c z - z) / z by
    field_simp, norm_div]
  rw [div_lt_iff₀ hpos]
  nlinarith [hz, hpos, hε]

/-! ## The parameter Böttcher coordinate at the critical value -/

/-- The Green function at the critical value: `G_c c = 2 G_c 0`. -/
theorem green_self_eq_two_greenParam (c : ℂ) :
    Work.Bottcher.green c c = 2 * Work.Bottcher.greenParam c := by
  have h := Work.Bottcher.Green.green_comm c 0
  rw [Work.Bottcher.Tantibar_zero] at h
  simpa [Work.Bottcher.greenParam_def] using h

/-- The parameter Böttcher coordinate: the value of the critical Böttcher coordinate at the
critical value `c`, set to `0` on the mandelbar (where the critical orbit does not escape). -/
def PhiCrit (c : ℂ) : ℂ := by
  classical
  exact if c ∈ Mandelbar then 0 else varphiCrit c c

theorem PhiCrit_eq_of_notMem {c : ℂ} (hc : c ∉ Mandelbar) : PhiCrit c = varphiCrit c c := by
  classical
  simp [PhiCrit, hc]

theorem PhiCrit_eq_zero_of_mem {c : ℂ} (hc : c ∈ Mandelbar) : PhiCrit c = 0 := by
  classical
  simp [PhiCrit, hc]

/-- The parameter coordinate of `c ∉ M*` is the critical Böttcher coordinate evaluated at the
critical value, and its modulus is `exp (G_c c) = exp (2 G_c 0)`. -/
theorem norm_PhiCrit_eq_exp_green_self {c : ℂ} (hc : c ∉ Mandelbar) :
    ‖PhiCrit c‖ = Real.exp (Work.Bottcher.green c c) := by
  rw [PhiCrit_eq_of_notMem hc]
  exact norm_varphiCrit (Work.ParamRays.self_mem_critDomain hc)

theorem norm_PhiCrit_eq_exp_two_greenParam {c : ℂ} (hc : c ∉ Mandelbar) :
    ‖PhiCrit c‖ = Real.exp (2 * Work.Bottcher.greenParam c) := by
  rw [norm_PhiCrit_eq_exp_green_self hc, green_self_eq_two_greenParam]

theorem PhiCrit_ne_zero {c : ℂ} (hc : c ∉ Mandelbar) : PhiCrit c ≠ 0 := by
  rw [PhiCrit_eq_of_notMem hc]
  exact varphiCrit_ne_zero (Work.ParamRays.self_mem_critDomain hc)

/-- **Uniqueness of the parameter coordinate**: every critical Böttcher coordinate of `c ∉ M*`
takes the value `PhiCrit c` at the critical value. -/
theorem PhiCrit_eq_of_isCritBottcher {c : ℂ} (hc : c ∉ Mandelbar) {φ : ℂ → ℂ}
    (hφ : Work.ParamRays.IsCritBottcher c φ) : PhiCrit c = φ c := by
  rw [PhiCrit_eq_of_notMem hc]
  exact varphiCrit_unique hφ (Work.ParamRays.self_mem_critDomain hc)

/-! ## Dynamic rays of the canonical coordinate -/

/-- The point of the unit circle at angle `θ`, conjugated and squared, is the point at angle
`-2θ`. -/
theorem conj_rayDirection_sq (θ : ℝ) : conj (rayDirection θ) ^ 2 = rayDirection (-2 * θ) := by
  have h1 : conj (rayDirection θ) = rayDirection (-θ) := by
    rw [rayDirection, rayDirection, ← Complex.exp_conj]
    congr 1
    rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring
  have h2 : rayDirection (-θ) ^ 2 = rayDirection (-2 * θ) := by
    rw [rayDirection, rayDirection, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [h1, h2]

/-- The **dynamic ray** `R_c(θ)` of the canonical critical Böttcher coordinate: the points of
`critDomain c` whose Böttcher value lies on the radial ray of direction `rayDirection θ` outside
the unit circle.  For `c ∉ M*` this is the piece of the classical dynamic ray in
`{G_c > G_c 0}`; the critical value `c` lies on `R_c(θ)` exactly when `c` lies on the parameter
ray `R(θ)`. -/
def dynRayCrit (c : ℂ) (θ : ℝ) : Set ℂ :=
  {z : ℂ | z ∈ Work.ParamRays.critDomain c ∧
    ∃ r : ℝ, 1 < r ∧ varphiCrit c z = (r : ℂ) * rayDirection θ}

theorem mem_dynRayCrit {c : ℂ} {θ : ℝ} {z : ℂ} :
    z ∈ dynRayCrit c θ ↔ z ∈ Work.ParamRays.critDomain c ∧
      ∃ r : ℝ, 1 < r ∧ varphiCrit c z = (r : ℂ) * rayDirection θ := Iff.rfl

theorem dynRayCrit_subset_critDomain (c : ℂ) (θ : ℝ) :
    dynRayCrit c θ ⊆ Work.ParamRays.critDomain c := fun _ h => h.1

/-- **The angle-doubling rule**: `T_c` sends the dynamic ray of angle `θ` into the dynamic ray of
angle `-2θ`.  (The map `T_c` is anti-holomorphic, whence the sign.) -/
theorem Tantibar_maps_dynRayCrit (c : ℂ) (θ : ℝ) :
    Tantibar c '' dynRayCrit c θ ⊆ dynRayCrit c (-2 * θ) := by
  rintro w ⟨z, ⟨hz, r, hr, hrz⟩, rfl⟩
  refine ⟨Work.ParamRays.Tantibar_mem_critDomain hz, r ^ 2, by nlinarith, ?_⟩
  rw [varphiCrit_comm_Tantibar hz, hrz, map_mul, Complex.conj_ofReal, mul_pow,
    ← Complex.ofReal_pow, conj_rayDirection_sq]

/-- The dynamic ray is periodic in the angle with period `1`. -/
theorem dynRayCrit_period (c : ℂ) (θ : ℝ) :
    dynRayCrit c (θ + 1) = dynRayCrit c θ := by
  unfold dynRayCrit
  rw [Work.Bottcher.rayDirection_add_one]

/-! ## The parameter interface, instantiated at the proved existence theorem -/

/-- The canonical coordinate of this area *is* the parameter Böttcher map
`Work.ParamRays.Phi` (both are the value of every critical Böttcher coordinate at the critical
value, by uniqueness).  Hence the whole `Work.ParamRays` parameter-ray interface is available for
`PhiCrit`, and it is now unconditional: `bottcherExists_crit` discharges its `BottcherExists`
hypothesis. -/
theorem PhiCrit_eq_Phi (c : ℂ) : PhiCrit c = Work.ParamRays.Phi c := by
  by_cases hc : c ∈ Mandelbar
  · rw [PhiCrit_eq_zero_of_mem hc, Work.ParamRays.Phi_eq_zero_of_mem hc]
  · rw [PhiCrit_eq_of_notMem hc]
    exact (Work.ParamRays.Phi_eq_of_isCritBottcher hc (isCritBottcher_varphiCrit c)).symm

/-- The critical value of an escaping parameter lies on the **parameter ray** `R(θ)` exactly
when it lies on the **dynamic ray** `R_c(θ)` of the analytic Böttcher coordinate: this is the
sense in which `PhiCrit` "extends the Böttcher coordinate to the critical value". -/
theorem mem_dynRayCrit_self_iff_paramRay {c : ℂ} (hc : c ∉ Mandelbar) {θ : ℝ} :
    c ∈ dynRayCrit c θ ↔ c ∈ Work.ParamRays.paramRay θ := by
  have h1 : varphiCrit c c = Work.ParamRays.Phi c := by
    rw [← PhiCrit_eq_of_notMem hc, PhiCrit_eq_Phi]
  rw [mem_dynRayCrit, Work.ParamRays.mem_paramRay, h1]
  constructor
  · rintro ⟨-, r, hr, hrz⟩
    exact ⟨hc, r, hr, by simpa [rayDirection, Work.ParamRays.rayDir] using hrz⟩
  · rintro ⟨-, r, hr, hrz⟩
    exact ⟨Work.ParamRays.self_mem_critDomain hc, r, hr,
      by simpa [rayDirection, Work.ParamRays.rayDir] using hrz⟩

theorem norm_PhiCrit (c : ℂ) (hc : c ∉ Mandelbar) :
    ‖PhiCrit c‖ = Real.exp (2 * Work.ParamRays.paramPotential c) := by
  rw [PhiCrit_eq_Phi]
  exact Work.ParamRays.norm_Phi_eq_exp bottcherExists_crit hc

theorem one_lt_norm_PhiCrit (c : ℂ) (hc : c ∉ Mandelbar) : 1 < ‖PhiCrit c‖ := by
  rw [PhiCrit_eq_Phi]
  exact Work.ParamRays.one_lt_norm_Phi bottcherExists_crit hc

/-- The parameter Böttcher map commutes with complex conjugation. -/
theorem PhiCrit_conj (c : ℂ) : PhiCrit (conj c) = conj (PhiCrit c) := by
  rw [PhiCrit_eq_Phi, PhiCrit_eq_Phi]
  exact Work.ParamRays.Phi_conj bottcherExists_crit c

/-- The parameter Böttcher map equivaries with the rotation `c ↦ ω c`. -/
theorem PhiCrit_smul_omega (c : ℂ) :
    PhiCrit (Work.ParamRays.omega * c) = Work.ParamRays.omega * PhiCrit c := by
  rw [PhiCrit_eq_Phi, PhiCrit_eq_Phi]
  exact Work.ParamRays.Phi_smul_omega bottcherExists_crit c

theorem potential_eq_zero_iff (c : ℂ) :
    Work.ParamRays.potential c = 0 ↔ c ∈ Mandelbar :=
  Work.ParamRays.potential_eq_zero_iff bottcherExists_crit c

theorem potential_pos_PhiCrit {c : ℂ} (hc : c ∉ Mandelbar) :
    0 < Work.ParamRays.potential c :=
  Work.ParamRays.potential_pos bottcherExists_crit hc

/-! ## The `M*` case, for completeness -/

/-- For a parameter of the mandelbar the escaping set itself carries a Böttcher coordinate
(re-export of the construction of `Work.Bottcher.Contraction`). -/
theorem exists_isDynBottcher_of_mem_mandelbar (c : ℂ) (hc : c ∈ Mandelbar) :
    ∃ φ : ℂ → ℂ, Work.ParamRays.IsDynBottcher c φ :=
  Contraction.bottcherExists_of_mem_mandelbar c hc

end

end Work.Bottcher
