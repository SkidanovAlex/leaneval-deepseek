import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.StreamBdryIface.Producers

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_StreamBdry.Basic` — vocabulary and elementary API for the StreamBdry (`SB`) area

This module is the entry point of the `FTS_StreamBdry` subproject (curric-46 lead): the
producers `sb1_gauge`, `sb0_psiField`, `sb3_bounds`, `sb2_dthDV`, `sb2_c2`, `sb4_near0`,
`sb5_barrier`, `sb5_decay`, `sb6_rates`, `slice_inputs`, `hid9''_of_parts` of
`Submission/Work/FTS/StreamBdryIface/Producers.lean` (frozen) are proved under the
names `<name>_proved`, with *identical* types.

## The object of study

`Ψ : Fn = ℝ → ℝ → ℝ` is the (slice of the) stream function, on the open quadrant
`Qd = (0,∞) × (0,π/2)`.  The `U`-slot is
`U'(Ψ) = Uop αG Ψ / s2`, where `Uop αG Ψ = -3Ψ - αG z ∂_zΨ` and `s2 θ = sin 2θ`, so that
the *level-0 ODE*
`αG·D_zΨ + 3Ψ = -s2·U'(Ψ)`  (`D_zΨ = z ∂_zΨ`)
holds **by definition** on `Qd`.  Its general solution is
`Ψ = psiP αG Ψ + c(θ)·z^{-3/αG}` with
`psiP αG Ψ = -(s2/αG)·∫₀¹ v^{3/αG-1}·U'(Ψ)(zv) dv`  (the particular solution).
SB1′ shows the constant of integration is `κ/cos θ`, i.e. the gauge mode
`gaugeMode αG = z^{-3/αG}/cos θ` is the only ambiguity; SB2–SB6 then run on `psiP`.

## Conventions of this file

* `Iint αG Ψ z θ = ∫₀¹ v^{3/αG-1}·U'(Ψ)(zv,θ) dv`, so that `psiP = -(s2/αG)·Iint`
  *definitionally* (`psiP_eq_Iint`).
* `gaugeGen k z θ = z^{-k}/cos θ`, so that `gaugeMode αG = gaugeGen (3/αG)` definitionally
  (`gaugeMode_eq_gaugeGen`); the algebra of `U(gaugeGen k) = V(gaugeGen k) = 0` is done with
  the abstract exponent `k` and the single relation `αG·k = 3`.
* everything is stated on `Qd`, where `s2 θ > 0` and `cos θ > 0`.
-/

noncomputable section
open scoped Real Topology NNReal
open Set Filter MeasureTheory

namespace Work.FTS_StreamBdry

open Work.FTS.StreamBdryIface (Uprime SlotBd SrcOK gaugeMode psiP psiHatP SB5Barrier oddPerS)
open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false

/-! ## §0 Vocabulary -/

/-- The exponent `3/αG - 1 ≥ -1` of the kernel in `psiP`. -/
def pexp (αG : ℝ) : ℝ := 3 / αG - 1

/-- The integral `I(z,θ) = ∫₀¹ v^{3/αG-1}·U'(Ψ)(zv,θ) dv`; `psiP = -(s2/αG)·I`. -/
def Iint (αG : ℝ) (Ψ : Fn) : Fn := fun z θ =>
  ∫ v in (0 : ℝ)..1, v ^ (3 / αG - 1) * Uprime αG Ψ (z * v) θ

/-- The gauge mode with an abstract exponent: `z^{-k}/cos θ`. -/
def gaugeGen (k : ℝ) : Fn := fun z θ => z ^ (-k) / Real.cos θ

/-- `psiP` *is* `-(s2/αG)·Iint`, definitionally. -/
lemma psiP_eq_Iint (αG : ℝ) (Ψ : Fn) (z θ : ℝ) :
    psiP αG Ψ z θ = -(Work.Construction.s2 θ / αG) * Iint αG Ψ z θ := rfl

/-- The frozen gauge mode is the abstract one at `k = 3/αG`. -/
lemma gaugeMode_eq_gaugeGen (αG : ℝ) : gaugeMode αG = gaugeGen (3 / αG) := rfl

/-- `gaugeMode` is the abstract gauge mode, pointwise. -/
lemma gaugeMode_apply (αG z θ : ℝ) : gaugeMode αG z θ = gaugeGen (3 / αG) z θ := rfl

/-! ## §1 Membership and sign facts on the open quadrant -/

lemma mem_Qd {z θ : ℝ} : (z, θ) ∈ Work.Construction.Qd ↔ 0 < z ∧ 0 < θ ∧ θ < π / 2 := by
  simp [Work.Construction.Qd]

lemma Qd_pos {z θ : ℝ} (h : (z, θ) ∈ Work.Construction.Qd) : 0 < z := (mem_Qd.mp h).1

lemma Qd_theta_mem {z θ : ℝ} (h : (z, θ) ∈ Work.Construction.Qd) : θ ∈ Ioo 0 (π / 2) :=
  ⟨(mem_Qd.mp h).2.1, (mem_Qd.mp h).2.2⟩

lemma Qd_theta_Iθ {z θ : ℝ} (h : (z, θ) ∈ Work.Construction.Qd) : θ ∈ Work.Spaces.Iθ :=
  ⟨le_of_lt (mem_Qd.mp h).2.1, le_of_lt (mem_Qd.mp h).2.2⟩

lemma s2_pos_of_Ioo {θ : ℝ} (h : θ ∈ Ioo (0 : ℝ) (π / 2)) : 0 < Work.Construction.s2 θ := by
  rw [Work.Construction.s2_eq]
  exact Real.sin_pos_of_pos_of_lt_pi (by linarith [h.1]) (by linarith [h.2])

lemma s2_pos_of_Qd {z θ : ℝ} (h : (z, θ) ∈ Work.Construction.Qd) :
    0 < Work.Construction.s2 θ := s2_pos_of_Ioo (Qd_theta_mem h)

lemma cos_pos_of_Ioo {θ : ℝ} (h : θ ∈ Ioo (0 : ℝ) (π / 2)) : 0 < Real.cos θ :=
  Real.cos_pos_of_mem_Ioo ⟨by linarith [h.1, Real.pi_pos], h.2⟩

lemma cos_pos_of_Qd {z θ : ℝ} (h : (z, θ) ∈ Work.Construction.Qd) :
    0 < Real.cos θ := cos_pos_of_Ioo (Qd_theta_mem h)

lemma s2_nonneg_of_Iθ {θ : ℝ} (h : θ ∈ Work.Spaces.Iθ) : 0 ≤ Work.Construction.s2 θ := by
  rw [Work.Construction.s2_eq]
  exact Real.sin_nonneg_of_mem_Icc
    ⟨by linarith [h.1], by linarith [h.2, Real.pi_pos]⟩

/-- `s2 = 2 sin θ cos θ`, the form in which the angular cancellations are done. -/
lemma s2_eq_two_sin_cos (θ : ℝ) :
    Work.Construction.s2 θ = 2 * Real.sin θ * Real.cos θ := by
  rw [Work.Construction.s2_eq, Real.sin_two_mul]

/-- `tan θ · s2 θ = 2 sin²θ` (the bounded form of the product, at `π/2`). -/
lemma tan_mul_s2 {θ : ℝ} (hc : Real.cos θ ≠ 0) :
    Real.tan θ * Work.Construction.s2 θ = 2 * Real.sin θ ^ 2 := by
  rw [s2_eq_two_sin_cos, Real.tan_eq_sin_div_cos]
  field_simp

/-! ## §2 The level-0 ODE, by definition -/

/-- `s2·U' = Uop` on the open quadrant (the only place where the division by `s2` is undone). -/
lemma s2_mul_Uprime {αG : ℝ} (Ψ : Fn) {z θ : ℝ} (h : (z, θ) ∈ Work.Construction.Qd) :
    Work.Construction.s2 θ * Uprime αG Ψ z θ = Work.Construction.Uop αG Ψ z θ := by
  rw [Uprime, mul_div_cancel₀ _ (ne_of_gt (s2_pos_of_Qd h))]

/-- **The level-0 ODE**, which holds by definition of `Uprime`:
`αG·D_zΨ + 3Ψ = -s2·U'(Ψ)` on the open quadrant. -/
lemma ode_of_Uprime {αG : ℝ} (Ψ : Fn) {z θ : ℝ} (h : (z, θ) ∈ Work.Construction.Qd) :
    αG * z * Work.Spaces.pz Ψ z θ + 3 * Ψ z θ = -Work.Construction.s2 θ * Uprime αG Ψ z θ := by
  rw [neg_mul, s2_mul_Uprime Ψ h, Work.Construction.Uop]
  ring

/-- The ODE in the `D_z` form: `αG·D_z(Ψ) = -s2·U'(Ψ) - 3Ψ`. -/
lemma Dz_eq_of_ode {αG : ℝ} (hαG : 0 < αG) (Ψ : Fn) {z θ : ℝ}
    (h : (z, θ) ∈ Work.Construction.Qd) :
    Work.Spaces.Dz Ψ z θ = (-(Work.Construction.s2 θ * Uprime αG Ψ z θ) - 3 * Ψ z θ) / αG := by
  have h1 := ode_of_Uprime (αG := αG) Ψ h
  rw [Work.Spaces.Dz, eq_div_iff (ne_of_gt hαG)]
  linarith [h1]

/-! ## §3 The gauge mode is slot-invisible -/

lemma pz_gaugeGen {k z θ : ℝ} (hz : z ≠ 0) :
    Work.Spaces.pz (gaugeGen k) z θ = -k * z ^ (-k - 1) / Real.cos θ := by
  have h : HasDerivAt (fun z' : ℝ => z' ^ (-k)) (-k * z ^ (-k - 1)) z :=
    Real.hasDerivAt_rpow_const (Or.inl hz)
  have h2 : HasDerivAt (fun z' : ℝ => gaugeGen k z' θ)
      (-k * z ^ (-k - 1) / Real.cos θ) z := by
    simpa [gaugeGen, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      h.div_const (Real.cos θ)
  exact h2.deriv

lemma pth_gaugeGen {k z θ : ℝ} (hc : Real.cos θ ≠ 0) :
    Work.Spaces.pth (gaugeGen k) z θ = z ^ (-k) * (Real.sin θ / Real.cos θ ^ 2) := by
  have h1 : HasDerivAt (fun θ' : ℝ => (Real.cos θ')⁻¹) (Real.sin θ / Real.cos θ ^ 2) θ := by
    have h0 : HasDerivAt Real.cos (-Real.sin θ) θ := Real.hasDerivAt_cos θ
    have h2 := h0.inv (by simpa using hc)
    convert h2 using 1
    ring
  have h3 : HasDerivAt (fun θ' : ℝ => gaugeGen k z θ')
      (z ^ (-k) * (Real.sin θ / Real.cos θ ^ 2)) θ := by
    simpa [gaugeGen, div_eq_mul_inv] using h1.const_mul (z ^ (-k))
  exact h3.deriv

/-- The algebra behind `U(gauge) = 0`, with an abstract exponent. -/
lemma gaugeGen_Uop_alg {αG k z θ : ℝ} (hk : αG * k = 3) (hz : z ≠ 0) :
    αG * z * (-k * z ^ (-k - 1) / Real.cos θ) + 3 * (z ^ (-k) / Real.cos θ) = 0 := by
  have hp : z ^ (-k - 1) * z = z ^ (-k) := by
    rw [← Real.rpow_add_one hz (-k - 1)]
    norm_num
  have hp' : z * z ^ (-k - 1) = z ^ (-k) := by rw [mul_comm, hp]
  have h1 : αG * z * (-k * z ^ (-k - 1) / Real.cos θ) + 3 * (z ^ (-k) / Real.cos θ)
      = (αG * (-k) * (z * z ^ (-k - 1)) + 3 * z ^ (-k)) / Real.cos θ := by ring
  rw [h1, hp', show αG * (-k) = -3 from by linarith [hk]]
  ring

/-- `U(gaugeMode) = 0` on points with `z ≠ 0`. -/
lemma Uop_gaugeGen {αG k : ℝ} (hk : αG * k = 3) {z θ : ℝ} (hz : z ≠ 0) :
    Work.Construction.Uop αG (gaugeGen k) z θ = 0 := by
  rw [Work.Construction.Uop, pz_gaugeGen (k := k) hz, gaugeGen]
  have := gaugeGen_Uop_alg (αG := αG) (k := k) (z := z) (θ := θ) hk hz
  linarith [this]

/-- `U(gaugeMode) = 0` on the open quadrant. -/
lemma Uop_gaugeMode {αG : ℝ} (hαG : 0 < αG) {z θ : ℝ} (hz : z ≠ 0) :
    Work.Construction.Uop αG (gaugeMode αG) z θ = 0 :=
  Uop_gaugeGen (k := 3 / αG) (by field_simp) hz

/-- `V(gaugeMode) = 0` wherever `cos θ ≠ 0`. -/
lemma Vop_gaugeGen {k : ℝ} {z θ : ℝ} (hc : Real.cos θ ≠ 0) :
    Work.Construction.Vop (gaugeGen k) z θ = 0 := by
  rw [Work.Construction.Vop, pth_gaugeGen (k := k) hc, gaugeGen, Real.tan_eq_sin_div_cos]
  field_simp
  ring

/-- `V(gaugeMode) = 0` wherever `cos θ ≠ 0`. -/
lemma Vop_gaugeMode {αG : ℝ} {z θ : ℝ} (hc : Real.cos θ ≠ 0) :
    Work.Construction.Vop (gaugeMode αG) z θ = 0 :=
  Vop_gaugeGen (k := 3 / αG) (z := z) hc

/-- The gauge mode does not vanish on the open quadrant. -/
lemma gaugeMode_ne_zero {αG : ℝ} {z θ : ℝ} (hz : 0 < z) (hc : Real.cos θ ≠ 0) :
    gaugeMode αG z θ ≠ 0 := by
  rw [gaugeMode]
  exact div_ne_zero (ne_of_gt (Real.rpow_pos_of_pos hz _)) hc

/-! ## §4 Slot bounds, unfolded -/

/-- The three slot bounds of `SlotBd`, extracted. -/
lemma SlotBd.Dz_le {αG M : ℝ} {Ψ : Fn} (h : SlotBd αG Ψ M) {z θ : ℝ}
    (hmem : (z, θ) ∈ Work.Construction.Qd) {j : ℕ} (hj : j ≤ 2) :
    |Work.Spaces.DzIter j (Uprime αG Ψ) z θ| ≤ M := (h z θ hmem).1 j hj

lemma SlotBd.mixed_le {αG M : ℝ} {Ψ : Fn} (h : SlotBd αG Ψ M) {z θ : ℝ}
    (hmem : (z, θ) ∈ Work.Construction.Qd) :
    |Work.Spaces.mixed 0 1 (Uprime αG Ψ) z θ| ≤ M := (h z θ hmem).2.1

lemma SlotBd.V_le {αG M : ℝ} {Ψ : Fn} (h : SlotBd αG Ψ M) {z θ : ℝ}
    (hmem : (z, θ) ∈ Work.Construction.Qd) {j : ℕ} (hj : j ≤ 1) :
    |Work.Spaces.DzIter j (Work.Construction.Vop Ψ) z θ| ≤ M := (h z θ hmem).2.2 j hj

lemma SlotBd.Uprime_le {αG M : ℝ} {Ψ : Fn} (h : SlotBd αG Ψ M) {z θ : ℝ}
    (hmem : (z, θ) ∈ Work.Construction.Qd) : |Uprime αG Ψ z θ| ≤ M :=
  SlotBd.Dz_le h hmem (j := 0) (by norm_num)

/-- `SrcOK`, extracted: `|F| ≤ Mf` on the closed angular strip. -/
lemma SrcOK.F_le {F : Fn} {L Mf : ℝ} (h : SrcOK F L Mf) {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Work.Spaces.Iθ) : |F z θ| ≤ Mf := (h.2.2.1 z θ hz hθ).1

/-- `SrcOK`, extracted: `|D_zF| ≤ Mf` on the closed angular strip. -/
lemma SrcOK.Dz_le {F : Fn} {L Mf : ℝ} (h : SrcOK F L Mf) {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Work.Spaces.Iθ) : |Work.Spaces.Dz F z θ| ≤ Mf := (h.2.2.1 z θ hz hθ).2

/-! ## §5 Named targets (the statements handed to delegated lemmas) -/

/-- **The level-0 ODE for `psiP`** (SB1 engine).  Consumed by SB1′ (`sb1_gauge`), SB2, SB3. -/
def PsiPOde (αG M : ℝ) (Ψ : Fn) : Prop :=
  ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
    αG * z * Work.Spaces.pz (psiP αG Ψ) z θ + 3 * psiP αG Ψ z θ
      = -Work.Construction.s2 θ * Uprime αG Ψ z θ

/-- **The `D_z`-derivatives of `Iint` commute with the integral**: `D_z^j` of the integral is the
integral of `D_z^j` of the slot, for `j ≤ 2`.  Consumed by SB3 (`psiP_DzIter_le`). -/
def DzIterIint (αG M : ℝ) (Ψ : Fn) : Prop :=
  ∀ z θ, (z, θ) ∈ Work.Construction.Qd → ∀ j : ℕ, j ≤ 2 →
    Work.Spaces.DzIter j (Iint αG Ψ) z θ
      = ∫ v in (0 : ℝ)..1, v ^ (3 / αG - 1) * Work.Spaces.DzIter j (Uprime αG Ψ) (z * v) θ

/-- **`psiP` is differentiable in each variable on the open quadrant** (SB1 engine: the `z`-half is
what the constancy argument in `z` needs, the `θ`-half what the `c' = tan θ·c` step needs). -/
def PsiPDiff (αG M : ℝ) (Ψ : Fn) : Prop :=
  ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
    DifferentiableAt ℝ (fun z' => psiP αG Ψ z' θ) z ∧
    DifferentiableAt ℝ (fun θ' => psiP αG Ψ z θ') θ

/-- **`V(psiP)` is bounded in `z` near `z = 0`, at every fixed `θ`** (SB1 engine: this is the
"`psiP` carries `s2` and `|D_θU'| ≤ M`" input of SB1′; it is what forces the constant of
integration to be `κ/cos θ` rather than a general `c(θ)`). -/
def VopPsiPBnd (αG M : ℝ) (Ψ : Fn) : Prop :=
  ∀ θ ∈ Ioo (0 : ℝ) (π / 2), ∃ C : ℝ, ∀ z ∈ Ioo (0 : ℝ) 1,
    |Work.Construction.Vop (psiP αG Ψ) z θ| ≤ C

/-- **`|psiP| ≤ M·s2/3`-type bound** (SB1/SB3: `|D_z^j psiP| ≤ M·s2` for `j ≤ 2`, straight from the
integral formula and the `SlotBd` slots). -/
def PsiPDzLe (αG M : ℝ) (Ψ : Fn) : Prop :=
  ∀ z θ, (z, θ) ∈ Work.Construction.Qd → ∀ j : ℕ, j ≤ 2 →
    |Work.Spaces.DzIter j (psiP αG Ψ) z θ| ≤ M * Work.Construction.s2 θ

/-- **The FIX-SB5 barrier function** `φ(θ) = log 2 - log(sin 2θ) = log(2/sin 2θ)`.

It is `C²` (indeed `C^∞`) on `(0,π/2)`, nonnegative (in fact `≥ log 2`), and blows up at both ends;
moreover `𝓐φ = -φ'' - (4cot 2θ - tan θ)φ' ≥ -10` on `(0,π/2)`.  Since `φ ≥ log 2 > 0`, this gives
`𝓐φ ≥ -16φ`, i.e. `SB5Barrier` with `Cφ = 16`. -/
def sbPhi (θ : ℝ) : ℝ := Real.log 2 - Real.log (Real.sin (2 * θ))

/-- The elementary properties of the barrier `sbPhi`: `C²` on `(0,π/2)`, nonnegative, and blowing up
at both ends. -/
def SB5PhiBasic : Prop :=
  ContDiffOn ℝ 2 sbPhi (Ioo 0 (π / 2)) ∧
    (∀ θ ∈ Ioo (0 : ℝ) (π / 2), 0 ≤ sbPhi θ) ∧
    Tendsto sbPhi (𝓝[>] 0) atTop ∧ Tendsto sbPhi (𝓝[<] (π / 2)) atTop

/-- The barrier inequality for `sbPhi`: `𝓐φ ≥ -10` on `(0,π/2)`. -/
def SB5PhiA : Prop :=
  ∀ θ ∈ Ioo (0 : ℝ) (π / 2),
    -10 ≤ -deriv (deriv sbPhi) θ
      - (4 * Real.cos (2 * θ) / Real.sin (2 * θ) - Real.tan θ) * deriv sbPhi θ

end Work.FTS_StreamBdry
