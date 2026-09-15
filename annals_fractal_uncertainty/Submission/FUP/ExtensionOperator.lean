import Submission.FUP.BMReduction
import Submission.FUP.PshLimit
import Submission.FUP.HilbertLine
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

open FractalUncertainty MeasureTheory FourierTransform Metric Filter Set
open scoped ENNReal BigOperators Real RealInnerProductSpace Topology

set_option autoImplicit false
set_option maxHeartbeats 1600000
variable {d : ℕ}
local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)
local notation "ℂᵈ" => (Fin d → ℂ)

namespace Submission.FUP

/-!
# The extension operator `Eω` of §3 of the paper

The paper's §3 ("Exact plurisubharmonic extensions") is built around the operator

  `Eω(x + iy) = (1/π) ∫_ℝ ω(x + t y)/(1 + t²) dt`

(equation (3.2)), which harmonically extends `ω` to each complex line, together with the
truncated operators `E_Rω` (equation (3.5)).  This module records the definitions, the
elementary identity `Eω(x) = ω(x)`, and the analytic statements about `Eω` that §3, §4 and
the passage to the limit supply:

* `Eomega_convergence_statement` (Lemma `lem:ext_lip_func_with_growth`): for a Lipschitz weight
  `ω` satisfying the Beurling–Malliavin growth condition the integral defining `Eω` converges
  absolutely and `E_Rω → Eω` uniformly on compact sets;
* `exact_psh_extension_statement` (Proposition `prop:Ew_is_psh`, in the equivalent form in which
  it is used): **for a compactly supported** `C³` weight `ω` satisfying the two conditions
  (boundedness of the normal derivative of the harmonic extension, and the lower bound for the
  integral of the second derivative over lines) the function `Eω + C|y|` is continuous and
  plurisubharmonic;
The passage from the compactly supported truncations to the full modified weight uses
`PshLimit.IsPSH.of_tendstoUniformlyOn_compacts` (plurisubharmonicity is closed under locally
uniform limits).

All the statements here are `Prop`s (not axioms): they are the interfaces through which §3 and §4
enter the rest of the development.
-/

/-- The extension operator of equation (3.2) of the paper:
`Eω(x + iy) = (1/π) ∫_ℝ ω(x + t y)/(1+t²) dt`. -/
noncomputable def Eomega (ω : ℝᵈ → ℝ) (x y : ℝᵈ) : ℝ :=
  (1 / π) * ∫ t : ℝ, ω (x + t • y) * (1 + t ^ 2)⁻¹

/-- The truncated extension operator `E_Rω` of equation (3.5). -/
noncomputable def EomegaR (ω : ℝᵈ → ℝ) (R : ℝ) (x y : ℝᵈ) : ℝ :=
  (1 / π) * ∫ t in (-R)..R, ω (x + t • y) * (1 + t ^ 2)⁻¹

/-- The extension operator, as a function on `ℂᵈ`: `Eω(z) = Eω(Re z + i Im z)`. -/
noncomputable def EomegaC (ω : ℝᵈ → ℝ) (z : ℂᵈ) : ℝ :=
  Eomega ω (reVec z) (imVec z)

/-- On the boundary `y = 0` the extension operator reproduces `ω`. -/
lemma Eomega_apply_zero (ω : ℝᵈ → ℝ) (x : ℝᵈ) : Eomega ω x 0 = ω x := by
  have h1 : ∀ t : ℝ, ω (x + t • (0 : ℝᵈ)) * (1 + t ^ 2)⁻¹ = ω x * (1 + t ^ 2)⁻¹ := by
    intro t; simp
  rw [Eomega]
  simp only [h1]
  rw [MeasureTheory.integral_const_mul, integral_univ_inv_one_add_sq]
  have hpi : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  field_simp

/-- `E_Rω` agrees with `Eω` in the limit `R → ∞` whenever the integral converges. -/
lemma EomegaC_apply (ω : ℝᵈ → ℝ) (z : ℂᵈ) :
    EomegaC ω z = (1 / π) * ∫ t : ℝ, ω (reVec z + t • imVec z) * (1 + t ^ 2)⁻¹ := rfl

/-- **Lemma `lem:ext_lip_func_with_growth`.**  For a Lipschitz weight satisfying the
Beurling–Malliavin growth condition, the integral defining `Eω` is absolutely convergent and
the truncated operators converge to it uniformly on compact subsets of `ℂᵈ`. -/
def Eomega_convergence_statement : Prop :=
  ∀ (CLip Cgr : ℝ), 0 ≤ CLip → 0 ≤ Cgr →
    ∀ (ω : ℝᵈ → ℝ), (∀ x₁ x₂, |ω x₁ - ω x₂| ≤ CLip * ‖x₁ - x₂‖) →
      HasFiniteGrowth ω Cgr →
      (∀ x y : ℝᵈ, Integrable (fun t : ℝ => ω (x + t • y) * (1 + t ^ 2)⁻¹)) ∧
      (∀ (K : Set ℂᵈ), IsCompact K → ∀ ε > 0, ∃ R₀ : ℝ, ∀ R ≥ R₀, ∀ z ∈ K,
        |EomegaR ω R (reVec z) (imVec z) - EomegaC ω z| < ε)

/-- **Proposition `prop:Ew_is_psh` in the form used in §4.**  Suppose `ω : ℝᵈ → ℝ` is `C³`,
**compactly supported**, is `≤ 0`, has bounded normal derivative of its harmonic extension
(condition `item_Ew_psh:hilbert`, written here in the equivalent form
`|Eω(x + ty) - ω(x)| ≤ C₁|y|`, cf. Lemma `lem:props_Eomega`(b)), and satisfies the lower bound
`∫_ℝ ⟨(D²ω(x + t ŷ))v̂, v̂⟩ dt/π ≥ -C₂` for all `x` and all orthonormal `ŷ, v̂` (condition
`item_Ew_psh:second_deriv`).  Then `Eω + C|y|` is continuous and plurisubharmonic on `ℂᵈ` for
`C ≥ max(C₁, C₂)`, and `u(x) ≤ u(x+iy) ≤ u(x) + 2C|y|`.

The compact-support hypothesis is *essential*: the second-derivative condition is stated in terms
of a Bochner integral over the whole line, which is only meaningful for a compactly supported
weight.  This is exactly the hypothesis of the published proposition (`ω ∈ C²₀`); §4 applies it
to the compactly supported truncations `ω̃_{≤n}` and passes to the limit. -/
def exact_psh_extension_statement : Prop :=
  ∀ (C₁ C₂ : ℝ), 0 ≤ C₁ → 0 ≤ C₂ →
    ∀ (ω : ℝᵈ → ℝ), ContDiff ℝ 3 ω → HasCompactSupport ω → (∀ x, ω x ≤ 0) →
      -- condition (i) of `prop:Ew_is_psh`: `‖H[ω|_ℓ']‖_∞ ≤ C₁` for every line `ℓ`, written
      -- pointwise as `|H[ω|_ℓ'](x)| ≤ C₁` for every `x` and every unit `ŷ`.
      (∀ x y : ℝᵈ, ‖y‖ = 1 → |hilbertLine ω x y| ≤ C₁) →
      (∀ (x yhat vhat : ℝᵈ), ‖yhat‖ = 1 → ‖vhat‖ = 1 → inner ℝ yhat vhat = 0 →
        -C₂ ≤ (1 / π) * ∫ t : ℝ,
          ((iteratedFDeriv ℝ 2 ω (x + t • yhat)) (fun _ : Fin 2 => vhat))) →
      ∃ C : ℝ, C = max C₁ C₂ ∧
        ∃ u : ℂᵈ → ℝ, Continuous u ∧ IsPSH u ∧
          (∀ z, u z = EomegaC ω z + C * ‖imVec z‖) ∧
          (∀ z : ℂᵈ, u (toCpx (reVec z)) ≤ u z) ∧
          (∀ z : ℂᵈ, u z ≤ u (toCpx (reVec z)) + 2 * C * ‖imVec z‖)

/-- **Lemma `lem:modify_weight_lemma` + `lem:modified_weight_good_lemma`** (Cohen §4), in the
form needed by the Beurling–Malliavin theorem.  A weight `ω` satisfying the hypotheses of the
Beurling–Malliavin theorem can be replaced by a weight `ω̃ ≤ ω` which vanishes on `B₂`,
Lipschitz with a constant depending only on `C_reg, C_gr, d`, and which is the pointwise limit of
an increasing family of **compactly supported truncations** `T_n` such that

* each `T_n` is `C³`, compactly supported, `≤ 0`, Lipschitz with the *same* constant `C_Lip`, and
  has growth functional bounded by `C_gr'` (`HasFiniteGrowth (T_n) C_gr'`);
* the two conditions of `exact_psh_extension_statement` hold for **every** `T_n` with the same
  constants `C₁, C₂` (this is where the second-derivative estimate of §4 is used).

In the paper `T_n = ω̃_{≤n} = ∑_{k ≤ n} ω̃_k`.  The two conditions are verified in §4 in the form
`‖H[ω̃_k|_ℓ']‖_∞ ≤ C₁` and `∑_k |∫_ℝ ⟨D²ω̃_k(x+tŷ)v̂,v̂⟩dt| ≤ C₂`; condition (i) is written here in
the equivalent pointwise form used by `exact_psh_extension_statement`, and condition (ii) is
exactly the finite-sum form of the second-derivative estimate
(`SecondDerivSum.sum_abs_integral_second_deriv_le` for the concrete construction of §4). -/
def modify_weight_statement : Prop :=
  ∀ (Creg Cgr : ℝ), 0 < Creg → 0 < Cgr →
    ∃ (C₁ C₂ CLip Cgr' : ℝ), 0 < C₁ ∧ 0 < C₂ ∧ 0 < CLip ∧ 0 < Cgr' ∧
      ∀ (ω : ℝᵈ → ℝ), (∀ x, ω x ≤ 0) → (∀ x, ‖x‖ ≤ 2 → ω x = 0) →
        ContDiff ℝ 3 ω →
        (∀ (a : ℕ), a ≤ 3 → ∀ x : ℝᵈ,
          ‖iteratedFDeriv ℝ a ω x‖ ≤ Creg * (1 + ‖x‖ ^ 2) ^ ((1 - (a : ℝ)) / 2)) →
        HasFiniteGrowth ω Cgr →
        ∃ (ωt : ℝᵈ → ℝ) (T : ℕ → ℝᵈ → ℝ),
          (∀ n, ContDiff ℝ 3 (T n)) ∧
          (∀ n, HasCompactSupport (T n)) ∧
          (∀ n x, T n x ≤ 0) ∧
          (∀ x, Tendsto (fun n => T n x) atTop (𝓝 (ωt x))) ∧
          ContDiff ℝ 3 ωt ∧ (∀ x, ωt x ≤ ω x) ∧ (∀ x, ‖x‖ ≤ 2 → ωt x = 0) ∧
          (∀ x₁ x₂, |ωt x₁ - ωt x₂| ≤ CLip * ‖x₁ - x₂‖) ∧
          HasFiniteGrowth ωt Cgr' ∧
          (∀ n, ∀ x₁ x₂, |T n x₁ - T n x₂| ≤ CLip * ‖x₁ - x₂‖) ∧
          (∀ n, HasFiniteGrowth (T n) Cgr') ∧
          (∀ n, ∀ x y : ℝᵈ, ‖y‖ = 1 → |hilbertLine (T n) x y| ≤ C₁) ∧
          (∀ n, ∀ (x yhat vhat : ℝᵈ), ‖yhat‖ = 1 → ‖vhat‖ = 1 → inner ℝ yhat vhat = 0 →
            -C₂ ≤ (1 / π) * ∫ t : ℝ,
              ((iteratedFDeriv ℝ 2 (T n) (x + t • yhat)) (fun _ : Fin 2 => vhat))) ∧
          -- the extensions of the truncations converge to the extension of `ωt` uniformly on
          -- compacta (Lemma 3.1, `lem:Ew_conv_cpct_subsets`, proved in `EomegaTail`)
          (∀ K : Set ℂᵈ, IsCompact K →
            TendstoUniformlyOn (fun n z => EomegaC (T n) z) (fun z => EomegaC ωt z) atTop K)

section Reduction

/-- Adding a fixed function to a locally uniformly convergent family preserves the convergence:
the pointwise differences are unchanged. -/
lemma tendstoUniformlyOn_add_const {F : ℕ → ℂᵈ → ℝ} {f : ℂᵈ → ℝ} {g : ℂᵈ → ℝ}
    {s : Set ℂᵈ} (h : TendstoUniformlyOn F f atTop s) :
    TendstoUniformlyOn (fun n z => F n z + g z) (fun z => f z + g z) atTop s := by
  rw [Metric.tendstoUniformlyOn_iff] at h ⊢
  intro ε hε
  filter_upwards [h ε hε] with n hn z hz
  have h1 := hn z hz
  rw [dist_eq_norm] at h1 ⊢
  have h2 : (f z + g z) - (F n z + g z) = f z - F n z := by ring
  rw [h2]; exact h1

/-- **`prop:BM_step1_prop`**: the plurisubharmonic Beurling–Malliavin problem.  This combines
§4 (`modify_weight_statement`, which already contains the convergence of the extensions of the
truncations — Lemma 3.1, proved in `Submission.FUP.EomegaTail`) and §3
(`exact_psh_extension_statement`, applied to the compactly supported truncations of the modified
weight), and the fact that plurisubharmonicity is closed under locally uniform limits
(`PshLimit`). -/
theorem BM_step1_of_components
    (hMod : modify_weight_statement (d := d))
    (hPSH : exact_psh_extension_statement (d := d)) :
    BM_step1_statement (d := d) := by
  intro Creg Cgr hCreg hCgr
  obtain ⟨C₁, C₂, CLip, Cgr', hC₁, hC₂, hCLip, hCgr', hmain⟩ := hMod Creg Cgr hCreg hCgr
  refine ⟨CLip, 2 * max C₁ C₂, hCLip, by positivity, ?_⟩
  intro ω hωnonpos hωzero hωcont hωreg hωgrowth
  obtain ⟨ωt, T, hTcont, hTcpt, hTnonpos, hTconv, hωtcont, hωtle, hωtzero, hωtlip,
    hωtgrowth, hTlip, hTgrowth, hTcond1, hTcond2, hTEconv⟩ :=
    hmain ω hωnonpos hωzero hωcont hωreg hωgrowth
  set C : ℝ := max C₁ C₂ with hCdef
  -- (1) §3 applied to each truncation
  have hu_exists : ∀ n : ℕ, ∃ u : ℂᵈ → ℝ, Continuous u ∧ IsPSH u ∧
      (∀ z, u z = EomegaC (T n) z + C * ‖imVec z‖) ∧
      (∀ z, u (toCpx (reVec z)) ≤ u z) ∧
      (∀ z, u z ≤ u (toCpx (reVec z)) + 2 * C * ‖imVec z‖) := by
    intro n
    obtain ⟨C', hC'def, u, hcont, hpsh, hform, hlow, hup⟩ :=
      hPSH C₁ C₂ hC₁.le hC₂.le (T n) (hTcont n) (hTcpt n) (hTnonpos n)
        (hTcond1 n) (hTcond2 n)
    have hCC : C' = C := by rw [hC'def, hCdef]
    refine ⟨u, hcont, hpsh, ?_, hlow, ?_⟩
    · intro z
      rw [hform z, hCC]
    · intro z
      rw [hCC] at hup
      exact hup z
  choose un hucont hupsh huform hulow huup using hu_exists
  -- (2) Lemma 3.1 for the sequence of truncations
  have hEconv : ∀ K : Set ℂᵈ, IsCompact K → TendstoUniformlyOn un
      (fun z => EomegaC ωt z + C * ‖imVec z‖) atTop K := by
    intro K hK
    have h2 := tendstoUniformlyOn_add_const (g := fun z : ℂᵈ => C * ‖imVec z‖) (hTEconv K hK)
    exact h2.congr (Eventually.of_forall fun n z _ => (huform n z).symm)
  -- (3) the limit is plurisubharmonic
  obtain ⟨-, hpsh_lim⟩ := IsPSH.of_tendstoUniformlyOn_compacts (u := un)
    (w := fun z => EomegaC ωt z + C * ‖imVec z‖) hupsh hucont hEconv
  have hlu : TendstoLocallyUniformly un (fun z => EomegaC ωt z + C * ‖imVec z‖) atTop :=
    tendstoLocallyUniformly_iff_forall_isCompact.mpr hEconv
  refine ⟨fun z => EomegaC ωt z + C * ‖imVec z‖, hpsh_lim, ?_, ?_, ?_, ?_⟩
  · intro x
    simp only [EomegaC, reVec_toCpx, imVec_toCpx, Eomega_apply_zero, norm_zero, mul_zero, add_zero]
    exact hωtle x
  · intro x hx
    simp only [EomegaC, reVec_toCpx, imVec_toCpx, Eomega_apply_zero, norm_zero, mul_zero, add_zero]
    exact hωtzero x hx
  · intro x₁ x₂
    simp only [EomegaC, reVec_toCpx, imVec_toCpx, Eomega_apply_zero, norm_zero, mul_zero, add_zero]
    exact hωtlip x₁ x₂
  · intro z
    have hz : Tendsto (fun n => un n z) atTop (𝓝 (EomegaC ωt z + C * ‖imVec z‖)) :=
      hlu.tendstoLocallyUniformlyOn.tendsto_at (Set.mem_univ z)
    have hz' : Tendsto (fun n => un n (toCpx (reVec z))) atTop
        (𝓝 (EomegaC ωt (toCpx (reVec z)) + C * ‖imVec (toCpx (reVec z))‖)) :=
      hlu.tendstoLocallyUniformlyOn.tendsto_at (Set.mem_univ _)
    constructor
    · refine le_of_tendsto_of_tendsto hz' hz (Eventually.of_forall fun n => ?_)
      exact hulow n z
    · have hz3 : Tendsto (fun n => un n (toCpx (reVec z)) + 2 * C * ‖imVec z‖) atTop
          (𝓝 (EomegaC ωt (toCpx (reVec z)) + C * ‖imVec (toCpx (reVec z))‖
            + 2 * C * ‖imVec z‖)) :=
        hz'.add_const (2 * C * ‖imVec z‖)
      exact le_of_tendsto_of_tendsto hz hz3 (Eventually.of_forall fun n => huup n z)

end Reduction

end Submission.FUP
