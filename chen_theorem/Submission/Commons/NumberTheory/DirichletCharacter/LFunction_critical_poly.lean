import Mathlib.Analysis.MellinInversion
import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Topology.Separation.CompletelyRegular
import Submission.Commons.NumberTheory.DirichletCharacter.completedLFunction_eq
import Submission.Commons.NumberTheory.DirichletCharacter.norm_LFunction_vertical

open Complex DirichletCharacter
open scoped Real
set_option autoImplicit false
set_option maxHeartbeats 0


/-!
# Choice of rotation angle with exponential decay (pure real analysis)

Used by `Submission/GammaDecay.lean`: the contour-rotation estimate
`|Γ(σ+it)| ≤ Γ(σ)·e^{θt}·(cos θ)^{-σ}` (valid for every admissible rotation angle θ, |θ|<π/2)
is optimized over θ to extract the classical decay:

`e^{θt}·(cos θ)^{-σ} ≤ C(σ)·(1+|t|)^σ·e^{-π|t|/2}`.

**Proof outline (for `t ≥ 0`; `t ≤ 0` symmetric):**
1. take `θ := -π/2 + 1/(1+t)` (so `|θ| < π/2`, `θ·t = -πt/2 + t/(1+t) ≤ -πt/2 + 1`);
2. `cos θ = cos(π/2 - 1/(1+t)) = sin(1/(1+t))`, and `sin δ ≥ (2/π)·δ` for `0 ≤ δ ≤ π/2`
   (concavity of `sin` on `[0, π]`: graph above the chord, or any equivalent proof);
3. hence `(cos θ)^{-σ} ≤ ((π/2)(1+t))^σ`.
-/

open Filter
open scoped Real Topology
set_option autoImplicit false

namespace PL.AngleChoice

/-- Jordan-type bound: for `0 < σ` and `0 < d ≤ 1`,
`(sin d)^{-σ} ≤ (π/2)^σ · (1/d)^σ`.
Used twice: `d = 1/(1+|t|)`, so `1/d = 1 + |t|`. -/
private lemma sin_pow_neg_le (σ : ℝ) (hσ : 0 < σ) {d : ℝ} (hd : 0 < d) (hd' : d ≤ 1) :
    (Real.sin d) ^ (-σ) ≤ (Real.pi / 2) ^ σ * (1 / d) ^ σ := by
  have hdpi : d ≤ Real.pi / 2 := by linarith [hd', Real.two_le_pi]
  have hdpi' : d < Real.pi := by linarith [hd', Real.two_le_pi]
  have hsinpos : 0 < Real.sin d := Real.sin_pos_of_pos_of_lt_pi hd hdpi'
  let a : ℝ := (2 / Real.pi) * d
  have ha : 0 < a := by
    dsimp [a]
    positivity
  have ha_sin : a ≤ Real.sin d := by
    dsimp [a]
    exact Real.mul_le_sin hd.le hdpi
  have hsininv_le : (Real.sin d)⁻¹ ≤ a⁻¹ := (inv_le_inv₀ hsinpos ha).2 ha_sin
  have ha_inv : a⁻¹ = (Real.pi / 2) * (1 / d) := by
    dsimp [a]
    field_simp [Real.pi_ne_zero, hd.ne']
  calc
    (Real.sin d) ^ (-σ) = (Real.sin d)⁻¹ ^ σ := by rw [Real.rpow_neg_eq_inv_rpow]
    _ ≤ a⁻¹ ^ σ := Real.rpow_le_rpow (inv_nonneg.mpr hsinpos.le) hsininv_le (le_of_lt hσ)
    _ = (Real.pi / 2 * (1 / d)) ^ σ := by rw [ha_inv]
    _ = (Real.pi / 2) ^ σ * (1 / d) ^ σ := Real.mul_rpow (le_of_lt Real.pi_div_two_pos) (by positivity)

/-- The case `0 ≤ t`: choose `θ = -π/2 + 1/(1+t)` (i.e. rotate clockwise by a little less
than a right angle). -/
private lemma bound_nonneg (σ : ℝ) (hσ : 0 < σ) {t : ℝ} (ht : 0 ≤ t) :
    ∃ θ : ℝ, |θ| < Real.pi / 2 ∧ 0 < Real.cos θ ∧
      Real.exp (θ * t) * (Real.cos θ) ^ (-σ) ≤
        (Real.exp 1 * (Real.pi / 2) ^ σ) * (1 + |t|) ^ σ * Real.exp (-(Real.pi / 2) * |t|) := by
  rw [abs_of_nonneg ht]
  let θ : ℝ := -(Real.pi / 2) + 1 / (1 + t)
  have h1pt : 0 < 1 + t := by linarith
  have hu0 : 0 < 1 / (1 + t) := by exact div_pos zero_lt_one h1pt
  have hu1 : 1 / (1 + t) ≤ 1 := by
    exact div_le_one_of_le₀ (by linarith) (by linarith)
  have hθlt : |θ| < Real.pi / 2 := by
    rw [abs_lt]
    constructor
    · dsimp [θ]; linarith
    · dsimp [θ]; linarith [hu1, Real.two_le_pi]
  have hcos_pos : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo (abs_lt.mp hθlt)
  have hcos_eq : Real.cos θ = Real.sin (1 / (1 + t)) := by
    dsimp [θ]
    rw [show -(Real.pi / 2) + 1 / (1 + t) = -(Real.pi / 2 - 1 / (1 + t)) by ring]
    rw [Real.cos_neg, Real.cos_pi_div_two_sub]
  have hpow : (Real.sin (1 / (1 + t))) ^ (-σ) ≤
      (Real.pi / 2) ^ σ * (1 / (1 / (1 + t))) ^ σ := sin_pow_neg_le σ hσ hu0 hu1
  have hrec : 1 / (1 / (1 + t)) = 1 + t := by
    field_simp [h1pt.ne']
  have hB : (Real.cos θ) ^ (-σ) ≤ (Real.pi / 2) ^ σ * (1 + t) ^ σ := by
    rw [hcos_eq]
    calc
      (Real.sin (1 / (1 + t))) ^ (-σ)
          ≤ (Real.pi / 2) ^ σ * (1 / (1 / (1 + t))) ^ σ := hpow
      _ = (Real.pi / 2) ^ σ * (1 + t) ^ σ := by rw [hrec]
  have hut : (1 / (1 + t)) * t ≤ 1 := by
    field_simp [h1pt.ne']
    linarith
  have hθt : θ * t ≤ -(Real.pi / 2) * t + 1 := by
    dsimp [θ]
    calc
      (-(Real.pi / 2) + 1 / (1 + t)) * t
          = -(Real.pi / 2) * t + (1 / (1 + t)) * t := by ring
      _ ≤ -(Real.pi / 2) * t + 1 := add_le_add_right hut (-(Real.pi / 2) * t)
  have hA : Real.exp (θ * t) ≤ Real.exp 1 * Real.exp (-(Real.pi / 2) * t) := by
    calc
      Real.exp (θ * t) ≤ Real.exp (-(Real.pi / 2) * t + 1) := (Real.exp_le_exp).2 hθt
      _ = Real.exp (-(Real.pi / 2) * t) * Real.exp 1 := by rw [Real.exp_add]
      _ = Real.exp 1 * Real.exp (-(Real.pi / 2) * t) := by ring
  have hc0 : 0 ≤ (Real.cos θ) ^ (-σ) := (Real.rpow_pos_of_pos hcos_pos (-σ)).le
  have hb0 : 0 ≤ Real.exp 1 * Real.exp (-(Real.pi / 2) * t) :=
    (mul_pos (Real.exp_pos 1) (Real.exp_pos (-(Real.pi / 2) * t))).le
  have hcomb : Real.exp (θ * t) * (Real.cos θ) ^ (-σ) ≤
      (Real.exp 1 * Real.exp (-(Real.pi / 2) * t)) * ((Real.pi / 2) ^ σ * (1 + t) ^ σ) := by
    exact mul_le_mul hA hB hc0 hb0
  exact ⟨θ, hθlt, hcos_pos, by
    calc
      Real.exp (θ * t) * (Real.cos θ) ^ (-σ)
          ≤ (Real.exp 1 * Real.exp (-(Real.pi / 2) * t)) * ((Real.pi / 2) ^ σ * (1 + t) ^ σ) := hcomb
      _ = (Real.exp 1 * (Real.pi / 2) ^ σ) * (1 + t) ^ σ * Real.exp (-(Real.pi / 2) * t) := by ring⟩

/-- The case `t ≤ 0`: choose `θ = π/2 - 1/(1-t)` (rotate counterclockwise). -/
private lemma bound_nonpos (σ : ℝ) (hσ : 0 < σ) {t : ℝ} (ht : t ≤ 0) :
    ∃ θ : ℝ, |θ| < Real.pi / 2 ∧ 0 < Real.cos θ ∧
      Real.exp (θ * t) * (Real.cos θ) ^ (-σ) ≤
        (Real.exp 1 * (Real.pi / 2) ^ σ) * (1 + |t|) ^ σ * Real.exp (-(Real.pi / 2) * |t|) := by
  let s : ℝ := -t
  have hs : 0 ≤ s := by dsimp [s]; linarith
  have hts : t = -s := by dsimp [s]; ring
  have habs : |t| = s := by
    dsimp [s]
    rw [abs_of_nonpos ht]
  rw [habs, hts]
  let θ : ℝ := Real.pi / 2 - 1 / (1 + s)
  have h1ps : 0 < 1 + s := by linarith
  have hu0 : 0 < 1 / (1 + s) := by exact div_pos zero_lt_one h1ps
  have hu1 : 1 / (1 + s) ≤ 1 := by
    exact div_le_one_of_le₀ (by linarith) (by linarith)
  have hθlt : |θ| < Real.pi / 2 := by
    rw [abs_lt]
    constructor
    · dsimp [θ]; linarith [hu1, Real.two_le_pi]
    · dsimp [θ]; linarith
  have hcos_pos : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo (abs_lt.mp hθlt)
  have hcos_eq : Real.cos θ = Real.sin (1 / (1 + s)) := by
    dsimp [θ]
    rw [Real.cos_pi_div_two_sub]
  have hpow : (Real.sin (1 / (1 + s))) ^ (-σ) ≤
      (Real.pi / 2) ^ σ * (1 / (1 / (1 + s))) ^ σ := sin_pow_neg_le σ hσ hu0 hu1
  have hrec : 1 / (1 / (1 + s)) = 1 + s := by
    field_simp [h1ps.ne']
  have hB : (Real.cos θ) ^ (-σ) ≤ (Real.pi / 2) ^ σ * (1 + s) ^ σ := by
    rw [hcos_eq]
    calc
      (Real.sin (1 / (1 + s))) ^ (-σ)
          ≤ (Real.pi / 2) ^ σ * (1 / (1 / (1 + s))) ^ σ := hpow
      _ = (Real.pi / 2) ^ σ * (1 + s) ^ σ := by rw [hrec]
  have hus : (1 / (1 + s)) * s ≤ 1 := by
    field_simp [h1ps.ne']
    linarith
  have hθt : θ * (-s) ≤ -(Real.pi / 2) * s + 1 := by
    dsimp [θ]
    calc
      (Real.pi / 2 - 1 / (1 + s)) * (-s)
          = -(Real.pi / 2) * s + (1 / (1 + s)) * s := by ring
      _ ≤ -(Real.pi / 2) * s + 1 := add_le_add_right hus (-(Real.pi / 2) * s)
  have hA : Real.exp (θ * (-s)) ≤ Real.exp 1 * Real.exp (-(Real.pi / 2) * s) := by
    calc
      Real.exp (θ * (-s)) ≤ Real.exp (-(Real.pi / 2) * s + 1) := (Real.exp_le_exp).2 hθt
      _ = Real.exp (-(Real.pi / 2) * s) * Real.exp 1 := by rw [Real.exp_add]
      _ = Real.exp 1 * Real.exp (-(Real.pi / 2) * s) := by ring
  have hc0 : 0 ≤ (Real.cos θ) ^ (-σ) := (Real.rpow_pos_of_pos hcos_pos (-σ)).le
  have hb0 : 0 ≤ Real.exp 1 * Real.exp (-(Real.pi / 2) * s) :=
    (mul_pos (Real.exp_pos 1) (Real.exp_pos (-(Real.pi / 2) * s))).le
  have hcomb : Real.exp (θ * (-s)) * (Real.cos θ) ^ (-σ) ≤
      (Real.exp 1 * Real.exp (-(Real.pi / 2) * s)) * ((Real.pi / 2) ^ σ * (1 + s) ^ σ) := by
    exact mul_le_mul hA hB hc0 hb0
  exact ⟨θ, hθlt, hcos_pos, by
    calc
      Real.exp (θ * (-s)) * (Real.cos θ) ^ (-σ)
          ≤ (Real.exp 1 * Real.exp (-(Real.pi / 2) * s)) * ((Real.pi / 2) ^ σ * (1 + s) ^ σ) := hcomb
      _ = (Real.exp 1 * (Real.pi / 2) ^ σ) * (1 + s) ^ σ * Real.exp (-(Real.pi / 2) * s) := by ring⟩

/-- The rotation-angle bound: for every `σ > 0` there is `C > 0` such that for every real `t`
there is an admissible rotation angle `θ` (`|θ| < π/2`, `cos θ > 0`) with

`e^{θt}·(cos θ)^{-σ} ≤ C·(1+|t|)^σ·e^{-π|t|/2}`. -/
theorem angle_choice (σ : ℝ) (hσ : 0 < σ) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, ∃ θ : ℝ,
      |θ| < Real.pi / 2 ∧ 0 < Real.cos θ ∧
        Real.exp (θ * t) * (Real.cos θ) ^ (-σ)
          ≤ C * (1 + |t|) ^ σ * Real.exp (-(Real.pi / 2) * |t|) := by
  refine ⟨Real.exp 1 * (Real.pi / 2) ^ σ, ?_, ?_⟩
  · exact mul_pos (Real.exp_pos 1) (Real.rpow_pos_of_pos Real.pi_div_two_pos σ)
  · intro t
    rcases le_total 0 t with ht | ht
    · exact bound_nonneg σ hσ ht
    · exact bound_nonpos σ hσ ht

end PL.AngleChoice


/-!
# The slope-limit lemma (T2, `rectBoundary_K` prerequisite)

If `f : ℂ → ℂ` is complex-differentiable at `0` with derivative `f'`, then the *slope*

`u ↦ u⁻¹ • (f u - f 0)   =   (f u - f 0) / u`

tends to `f'` as `u → 0` through nonzero values:

`Tendsto (fun u => u⁻¹ • (f u - f 0)) (𝓝[≠] 0) (𝓝 f')`.

Mathlib's `Mathlib.Analysis.Calculus.Deriv.Slope` states precisely that a
`HasDerivAt` function equals the limit of its slope on the punctured filter:
`hasDerivAt_iff_tendsto_slope : HasDerivAt f f' x ↔ Tendsto (slope f x) (𝓝[≠] x) (𝓝 f')`
where `slope f x y = (y - x)⁻¹ • (f y - f x)` (`slope_def_module`).  Setting
`x = 0` and unfolding `slope` gives exactly the statement above.
-/

open Filter Complex
open scoped Topology

set_option autoImplicit false

namespace PL.DerivSlope

/-- If `f : ℂ → ℂ` has derivative `f'` at `0`, then the difference quotient
`(f u - f 0) / u` tends to `f'` as `u → 0`, `u ≠ 0`. -/
lemma hasDerivAt_tendsto_slope (f : ℂ → ℂ) {f' : ℂ} (h : HasDerivAt f f' 0) :
    Tendsto (fun u : ℂ => u⁻¹ • (f u - f 0)) (𝓝[≠] 0) (𝓝 f') := by
  -- `slope f 0 u = u⁻¹ • (f u - f 0)`, so this is Mathlib's slope-limit statement at `0`.
  simpa [slope_def_module] using
    (show Tendsto (fun u : ℂ => slope f 0 u) (𝓝[≠] 0) (𝓝 f') from h.tendsto_slope)

end PL.DerivSlope


/-!
# Continuity of a function extended across a punctured limit

Let `g : α → ℂ` tend to `c` as `u → a` through values `≠ a`.  Then the function that is
`c` at `a` and `g u` elsewhere is continuous at `a`:

`ContinuousAt (fun u => if u = a then c else g u) a`.

This is the topological fact used to turn the slope-limit lemma
(`Submission/DerivSlope.lean`) into continuity of the extended pole-subtraction
`ψ(u) = (φ u - φ 0)/u` (with `ψ(0) = deriv φ 0`) at the origin.
-/

open Filter
open scoped Topology

set_option autoImplicit false

namespace PL.ExtendPunctured

/-- A function that is `c` at `a` and agrees with `g` (which tends to `c` puncturedly)
elsewhere is continuous at `a`. -/
lemma continuousAt_extend_punctured {α : Type*} [TopologicalSpace α] [DecidableEq α] (g : α → ℂ) (a : α) (c : ℂ)
    (hg : Tendsto g (𝓝[≠] a) (𝓝 c)) :
    ContinuousAt (fun u : α => if u = a then c else g u) a := by
  -- Unfold `ContinuousAt`; the value at `a` is `c`.
  rw [ContinuousAt]
  simp
  -- Now prove `Tendsto (fun u => if u = a then c else g u) (𝓝 a) (𝓝 c)`.
  rw [tendsto_def]
  intro s hs
  -- Along the punctured neighbourhood `g` is eventually in the neighbourhood `s` of `c`.
  have hgs : ∀ᶠ u in 𝓝[≠] a, g u ∈ s := (tendsto_def.mp hg) s hs
  rw [eventually_nhdsWithin_iff] at hgs
  -- At `u = a` the extended function takes the value `c ∈ s`; elsewhere it is `g u ∈ s`.
  filter_upwards [hgs] with u hu
  by_cases hua : u = a
  · subst u
    simp [mem_of_mem_nhds hs]
  · simp [hua, hu hua]

end PL.ExtendPunctured


/-!
# Base algebra for the rotated-contour identity (PL.GRBase)

Definitions (all pointwise, no measure theory here):
* `J0 s r = e^{-r}·r^{s-1}` — the unrotated Γ integrand on `r > 0`;
* `Jr s θ r = e^{-r·e^{-iθ}}·r^{s-1}` — the rotated integrand;
* `Hs s x = e^{-e^x}·e^{sx}` — pullback of the Γ integrand to the real line;
* `Hr s θ x = e^{-e^{x-iθ}}·e^{s(x-iθ)}` — rotated pullback.

Plus the pure-algebra lemmas connecting them:
* `cpow_ofReal_exp` — `(e^x : ℂ)^z = cexp(z·x)`;
* `Hs_smul`, `Hr_smul` — the pullbacks are `exp x • (rotated) integrand (exp x)` up to the
  constant phase `e^{-iθs}`;
* norm lemmas `norm_J0`, `norm_Jr` used for integrability.
-/

open Complex Filter MeasureTheory Set
open scoped Real
set_option autoImplicit false

namespace PL.GRBase

noncomputable section

/-- `cexp (x : ℂ) = (Real.exp x : ℂ)`. -/
lemma cexp_ofReal_exp (x : ℝ) : cexp (x : ℂ) = (Real.exp x : ℂ) := (Complex.ofReal_exp x).symm

/-- The unrotated Γ integrand `e^{-r}·r^{s-1}` (`r > 0`). -/
noncomputable def J0 (s : ℂ) (r : ℝ) : ℂ := cexp (-(r : ℂ)) * (r : ℂ) ^ (s - 1)

/-- The rotated Γ integrand `e^{-r·e^{-iθ}}·r^{s-1}` (`r > 0`). -/
noncomputable def Jr (s : ℂ) (θ : ℝ) (r : ℝ) : ℂ :=
  cexp (-((r : ℂ) * cexp (-(I * (θ : ℂ))))) * (r : ℂ) ^ (s - 1)

/-- Pullback to the real line of the unrotated integrand: `Hs s x = e^{-e^x}·e^{s·x}`. -/
noncomputable def Hs (s : ℂ) (x : ℝ) : ℂ := cexp (-cexp (x : ℂ)) * cexp (s * (x : ℂ))

/-- Pullback to the real line of the rotated integrand: `Hr s θ x = e^{-e^{x-iθ}}·e^{s·(x-iθ)}`. -/
noncomputable def Hr (s : ℂ) (θ : ℝ) (x : ℝ) : ℂ :=
  cexp (-(cexp ((x : ℂ) - (θ : ℂ) * I))) * cexp (s * ((x : ℂ) - (θ : ℂ) * I))

/-- `(e^x : ℂ)^z = cexp (z·x)` for real `x`. -/
lemma cpow_ofReal_exp (x : ℝ) (z : ℂ) : ((Real.exp x : ℝ) : ℂ) ^ z = cexp (z * (x : ℂ)) := by
  have hx : (Real.exp x : ℂ) ≠ 0 := by exact_mod_cast (Real.exp_pos x).ne'
  rw [Complex.cpow_def_of_ne_zero hx]
  have hlog : Complex.log ((Real.exp x : ℝ) : ℂ) = (x : ℂ) := by
    rw [← Complex.ofReal_log (Real.exp_pos x).le]
    norm_num [Real.log_exp]
  rw [hlog]
  ring_nf

/-- `(e^x : ℂ)^{s-1}·(e^x : ℂ) = (e^x : ℂ)^s`. -/
lemma cpow_exp_sub_one_mul (x : ℝ) (s : ℂ) :
    ((Real.exp x : ℝ) : ℂ) ^ (s - 1) * ((Real.exp x : ℝ) : ℂ) = ((Real.exp x : ℝ) : ℂ) ^ s := by
  have hx : (Real.exp x : ℂ) ≠ 0 := by exact_mod_cast (Real.exp_pos x).ne'
  calc
    ((Real.exp x : ℝ) : ℂ) ^ (s - 1) * ((Real.exp x : ℝ) : ℂ)
        = ((Real.exp x : ℝ) : ℂ) ^ (s - 1) * ((Real.exp x : ℝ) : ℂ) ^ 1 := by
          rw [Complex.cpow_one]
    _ = ((Real.exp x : ℝ) : ℂ) ^ ((s - 1) + 1) := (Complex.cpow_add (s - 1) 1 hx).symm
    _ = ((Real.exp x : ℝ) : ℂ) ^ s := by congr 1; ring

/-- `(e^x : ℂ)·(e^x : ℂ)^{s-1} = (e^x : ℂ)^s`. -/
lemma cpow_exp_mul_sub_one (x : ℝ) (s : ℂ) :
    ((Real.exp x : ℝ) : ℂ) * ((Real.exp x : ℝ) : ℂ) ^ (s - 1) = ((Real.exp x : ℝ) : ℂ) ^ s := by
  rw [mul_comm, cpow_exp_sub_one_mul]

/-- `Hs s x = exp x • J0 s (exp x)` pointwise. -/
lemma Hs_smul (s : ℂ) (x : ℝ) : Hs s x = Real.exp x • J0 s (Real.exp x) := by
  calc
    Hs s x = cexp (-((Real.exp x : ℝ) : ℂ)) * (((Real.exp x : ℝ) : ℂ) ^ s) := by
      unfold Hs
      rw [cexp_ofReal_exp x]
      rw [← cpow_ofReal_exp x s]
    _ = Real.exp x • J0 s (Real.exp x) := by
      unfold J0
      rw [← cpow_exp_sub_one_mul x s]
      change cexp (-((Real.exp x : ℝ) : ℂ))
          * ((((Real.exp x : ℝ) : ℂ) ^ (s - 1)) * ((Real.exp x : ℝ) : ℂ))
        = (Real.exp x : ℂ) * (cexp (-((Real.exp x : ℝ) : ℂ)) * (((Real.exp x : ℝ) : ℂ) ^ (s - 1)))
      ring

/-- `e^{-iθ} = cos θ - i·sin θ`. -/
lemma cexp_neg_I_mul (θ : ℝ) :
    cexp (-(I * (θ : ℂ))) = (Real.cos θ : ℂ) - (Real.sin θ : ℂ) * I := by
  rw [show -(I * (θ : ℂ)) = (-(θ : ℂ)) * I by ring]
  rw [Complex.exp_mul_I]
  have hc : cos (-(θ : ℂ)) = (Real.cos θ : ℂ) := by
    rw [Complex.cos_neg, ← Complex.ofReal_cos]
  have hs : sin (-(θ : ℂ)) = -((Real.sin θ : ℂ)) := by
    rw [Complex.sin_neg, ← Complex.ofReal_sin]
  rw [hc, hs]
  ring

/-- `exp (x - iθ) = e^x · e^{-iθ}`. -/
lemma cexp_sub_I_mul_exp (x : ℝ) (θ : ℝ) :
    cexp ((x : ℂ) - (θ : ℂ) * I) = ((Real.exp x : ℝ) : ℂ) * cexp (-(I * (θ : ℂ))) := by
  calc
    cexp ((x : ℂ) - (θ : ℂ) * I) = cexp ((x : ℂ) + -((θ : ℂ) * I)) := rfl
    _ = cexp (x : ℂ) * cexp (-((θ : ℂ) * I)) := Complex.exp_add _ _
    _ = ((Real.exp x : ℝ) : ℂ) * cexp (-((θ : ℂ) * I)) := by rw [cexp_ofReal_exp x]
    _ = ((Real.exp x : ℝ) : ℂ) * cexp (-(I * (θ : ℂ))) := by
          have harg : -((θ : ℂ) * I) = -(I * (θ : ℂ)) := by ring
          rw [harg]

/-- `exp (s·(x - iθ)) = exp(s·x) · exp(-(iθ)·s)`. -/
lemma cexp_mul_sub (s : ℂ) (x : ℝ) (θ : ℝ) :
    cexp (s * ((x : ℂ) - (θ : ℂ) * I)) = cexp (s * (x : ℂ)) * cexp (-((I * (θ : ℂ)) * s)) := by
  calc
    cexp (s * ((x : ℂ) - (θ : ℂ) * I))
        = cexp (s * (x : ℂ) + -(s * ((θ : ℂ) * I))) := by congr 1; ring
    _ = cexp (s * (x : ℂ)) * cexp (-(s * ((θ : ℂ) * I))) := Complex.exp_add _ _
    _ = cexp (s * (x : ℂ)) * cexp (-((I * (θ : ℂ)) * s)) := by
          have harg : -(s * ((θ : ℂ) * I)) = -((I * (θ : ℂ)) * s) := by ring
          rw [harg]

/-- `Hr s θ x = cexp(-(I·θ)·s) * (exp x • Jr s θ (exp x))` pointwise. -/
lemma Hr_smul (s : ℂ) (θ : ℝ) (x : ℝ) :
    Hr s θ x = cexp (-((I * (θ : ℂ)) * s)) * (Real.exp x • Jr s θ (Real.exp x)) := by
  calc
    Hr s θ x = cexp (-(((Real.exp x : ℝ) : ℂ) * cexp (-(I * (θ : ℂ)))))
        * cexp (s * ((x : ℂ) - (θ : ℂ) * I)) := by
          unfold Hr
          rw [cexp_sub_I_mul_exp x θ]
    _ = cexp (-(((Real.exp x : ℝ) : ℂ) * cexp (-(I * (θ : ℂ)))))
        * (cexp (s * (x : ℂ)) * cexp (-((I * (θ : ℂ)) * s))) := by
          rw [cexp_mul_sub s x θ]
    _ = cexp (-(((Real.exp x : ℝ) : ℂ) * cexp (-(I * (θ : ℂ)))))
        * ((((Real.exp x : ℝ) : ℂ) ^ s) * cexp (-((I * (θ : ℂ)) * s))) := by
          rw [← cpow_ofReal_exp x s]
    _ = cexp (-((I * (θ : ℂ)) * s)) * (cexp (-(((Real.exp x : ℝ) : ℂ) * cexp (-(I * (θ : ℂ)))))
        * (((Real.exp x : ℝ) : ℂ) ^ s)) := by ring
    _ = cexp (-((I * (θ : ℂ)) * s)) * (cexp (-(((Real.exp x : ℝ) : ℂ) * cexp (-(I * (θ : ℂ)))))
        * (((Real.exp x : ℝ) : ℂ) * (((Real.exp x : ℝ) : ℂ) ^ (s - 1)))) := by
          rw [← cpow_exp_mul_sub_one x s]
    _ = cexp (-((I * (θ : ℂ)) * s)) * (Real.exp x • Jr s θ (Real.exp x)) := by
          unfold Jr
          change cexp (-((I * (θ : ℂ)) * s))
              * (cexp (-(((Real.exp x : ℝ) : ℂ) * cexp (-(I * (θ : ℂ)))))
                * (((Real.exp x : ℝ) : ℂ) * (((Real.exp x : ℝ) : ℂ) ^ (s - 1))))
            = cexp (-((I * (θ : ℂ)) * s))
              * ((Real.exp x : ℂ) * (cexp (-(((Real.exp x : ℝ) : ℂ) * cexp (-(I * (θ : ℂ)))))
                * (((Real.exp x : ℝ) : ℂ) ^ (s - 1))))
          ring

/-- Real part of `e^{-iθ}` is `cos θ`. -/
lemma re_cexp_neg_I_mul (θ : ℝ) : (cexp (-(I * (θ : ℂ)))).re = Real.cos θ := by
  rw [cexp_neg_I_mul]
  rw [Complex.sub_re, Complex.mul_re]
  rw [Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

/-- Real part of `-r·e^{-iθ}` is `-r·cos θ`. -/
lemma re_neg_mul_cexp_neg_I_mul (r : ℝ) (θ : ℝ) :
    (-((r : ℂ) * cexp (-(I * (θ : ℂ))))).re = -(r * Real.cos θ) := by
  rw [cexp_neg_I_mul]
  simp only [Complex.neg_re, Complex.mul_re, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

/-- Norm of the rotated integrand: `‖Jr s θ r‖ = exp(-r·cos θ)·r^{Re s - 1}` for `r > 0`. -/
lemma norm_Jr (s : ℂ) (θ : ℝ) (r : ℝ) (hr : 0 < r) :
    ‖Jr s θ r‖ = Real.exp (-(r * Real.cos θ)) * r ^ (s.re - 1) := by
  unfold Jr
  rw [norm_mul]
  have h₁ : ‖cexp (-((r : ℂ) * cexp (-(I * (θ : ℂ)))))‖ =
      Real.exp (-(r * Real.cos θ)) := by
    rw [Complex.norm_exp, re_neg_mul_cexp_neg_I_mul]
  have h₅ : ‖(r : ℂ) ^ (s - 1)‖ = r ^ (s.re - 1) := by
    have h₆ : ((s - 1 : ℂ).re) = s.re - 1 := by simp
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hr, h₆]
  rw [h₁, h₅]

/-- Norm of the unrotated integrand: `‖J0 s r‖ = exp(-r)·r^{Re s - 1}` for `r > 0`. -/
lemma norm_J0 (s : ℂ) (r : ℝ) (hr : 0 < r) :
    ‖J0 s r‖ = Real.exp (-r) * r ^ (s.re - 1) := by
  unfold J0
  rw [norm_mul]
  have h₁ : ‖cexp (-(r : ℂ))‖ = Real.exp (-r) := by
    rw [Complex.norm_exp]
    simp
  have h₅ : ‖(r : ℂ) ^ (s - 1)‖ = r ^ (s.re - 1) := by
    have h₆ : ((s - 1 : ℂ).re) = s.re - 1 := by simp
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hr, h₆]
  rw [h₁, h₅]

end
end PL.GRBase


/-!
# Real Euler-integral convergence with a damping rate (PL.GRRealInt)

**Single lemma** (needed as the real-analysis core of the rotated-contour Γ argument):

    real_integrable_exp_neg_mul_rpow {c σ : ℝ} (hc : 0 < c) (hσ : 0 < σ) :
        IntegrableOn (fun r : ℝ => Real.exp (-(c * r)) * r ^ (σ - 1)) (Ioi 0) volume

## Proof plan (mirror `Real.GammaIntegral_convergent` in
`Mathlib/Analysis/SpecialFunctions/Gamma/Basic.lean`, lines ~66-76):

1. `rw [← Ioc_union_Ioi_eq_Ioi (a := (0:ℝ)) (b := 1) (by norm_num : (0:ℝ) ≤ 1),
   MeasureTheory.integrableOn_union]` and prove the two conjuncts.

2. Piece on `Ioc 0 1`: `rw [← MeasureTheory.integrableOn_Icc_iff_integrableOn_Ioc]`,
   then `(intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mp` so the goal becomes
   an `IntervalIntegrable` of `f r = exp (-(c*r)) * r ^ (σ - 1)`.
   Apply `IntervalIntegrable.continuousOn_mul` to the interval-integrable factor
   `r ↦ r ^ (σ - 1)` (given by `intervalIntegrable_rpow'` since `-1 < σ - 1`) and the
   continuous factor `r ↦ exp (-(c*r))` (given by `fun_prop`).

3. Piece on `Ioi 1`: use `integrable_of_isBigO_exp_neg (div_pos hc two_pos)`:
   continuity of the integrand on `Ici 1` (product of the two continuous factors), and the
   bound `f =O[atTop] (fun r => exp (-(c / 2) * r))` obtained from
   `isLittleO_exp_mul_rpow_of_lt (σ - 1) (a := -c) (b := -(c / 2)) (by linarith)`.
-/

open Filter MeasureTheory Set Real intervalIntegral
open scoped Real
set_option autoImplicit false

namespace PL.GRRealInt

/-- The Euler-type real integral `∫₀^∞ e^{-c·r}·r^{σ-1} dr` converges for `c > 0`, `σ > 0`. -/
lemma real_integrable_exp_neg_mul_rpow {c σ : ℝ} (hc : 0 < c) (hσ : 0 < σ) :
    IntegrableOn (fun r : ℝ => Real.exp (-(c * r)) * r ^ (σ - 1)) (Ioi 0) := by
  rw [← Ioc_union_Ioi_eq_Ioi (@zero_le_one ℝ _ _ _ _), integrableOn_union]
  constructor
  · rw [← integrableOn_Icc_iff_integrableOn_Ioc]
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mp
      ((intervalIntegrable_rpow' (by linarith : -1 < σ - 1)).continuousOn_mul
        (by fun_prop : ContinuousOn (fun r : ℝ => Real.exp (-(c * r))) (Set.uIcc 0 1)))
  · have hcont : ContinuousOn (fun r : ℝ => Real.exp (-(c * r)) * r ^ (σ - 1)) (Ici 1) := by
      have h1 : ContinuousOn (fun r : ℝ => Real.exp (-(c * r))) (Ici 1) := by fun_prop
      have h2 : ContinuousOn (fun r : ℝ => r ^ (σ - 1)) (Ici 1) :=
        continuousOn_id.rpow_const (by
          intro x hx
          exact Or.inl (ne_of_gt (lt_of_lt_of_le zero_lt_one hx)))
      exact h1.mul h2
    have ho : (fun r : ℝ => Real.exp (-(c * r)) * r ^ (σ - 1)) =O[atTop]
        (fun r : ℝ => Real.exp (-(c / 2) * r)) := by
      have hlt : -c < -(c / 2) := by linarith
      simpa [neg_mul] using
        (isLittleO_exp_mul_rpow_of_lt (σ - 1) (a := -c) (b := -(c / 2)) hlt).isBigO
    exact integrable_of_isBigO_exp_neg (div_pos hc two_pos) hcont ho

end PL.GRRealInt


/-!
# Measure-level substitution and Γ-integrand integrability (PL.GRSubst)

* `integrable_J0` — `J0 s` integrable over `(0,∞)` (Euler, `0 < Re s`);
* `integrable_Jr` — **T2**: the rotated integrand is integrable over `(0,∞)`
  (`0 < Re s`, `|θ| < π/2`);
* substitution `r = e^x`:
  - `integral_comp_exp_Iio` (the `Iio` mirror of the library `integral_comp_exp_Ioi`);
  - `integral_comp_exp` — whole line: `∫_ℝ exp x • g(exp x) = ∫_{(0,∞)} g`;
  - integrability transfers `integrable_comp_exp`, `integrable_comp_exp_union`;
* the pullback identities:
  - `integral_Hs` — `∫_ℝ Hs s = Γ(s)`;
  - `integral_Hr` — `∫_ℝ Hr s θ = e^{-iθs}·∫_{(0,∞)} Jr s θ`;
  - `integrable_Hs`, `integrable_Hr`.
-/

open Complex Filter MeasureTheory Set
open PL.GRBase
open scoped Real
set_option autoImplicit false

namespace PL.GRSubst

noncomputable section

/-- ae: `(-∞,0) ∪ (0,∞) = ℝ`. -/
lemma Iio_union_Ioi_ae_univ : (Iio (0 : ℝ) ∪ Ioi 0 : Set ℝ) =ᵐ[volume] (Set.univ : Set ℝ) := by
  rw [ae_eq_univ]
  have hcomp : ((Iio (0 : ℝ) ∪ Ioi 0)ᶜ : Set ℝ) = {0} := by
    ext x
    simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_Iio, Set.mem_Ioi, Set.mem_singleton_iff]
    constructor
    · intro hx
      by_contra hx0
      exact hx (lt_or_gt_of_ne hx0)
    · intro hx
      simp [hx]
  rw [hcomp]
  simp

/-- `(0,∞) = (0,1) ∪ {1} ∪ (1,∞)`. -/
lemma Ioi_eq_union : Ioi (0 : ℝ) = Ioo (0 : ℝ) 1 ∪ ({1} : Set ℝ) ∪ Ioi 1 := by
  ext x
  constructor
  · intro hx
    rcases lt_trichotomy x 1 with h | h | h
    · exact Or.inl (Or.inl ⟨hx, h⟩)
    · exact Or.inl (Or.inr h)
    · exact Or.inr h
  · intro hx
    rcases hx with h | h
    · rcases h with h | h
      · exact h.1
      · have hx1 : x = 1 := Set.mem_singleton_iff.mp h
        simp [hx1]
    · exact lt_trans zero_lt_one (by simpa using h)

/-- The unrotated integrand equals the `GammaIntegral` integrand pointwise on `r > 0`. -/
lemma J0_eq_GammaIntegrand (s : ℂ) (r : ℝ) (_hr : 0 < r) :
    J0 s r = ↑(Real.exp (-r)) * (r : ℂ) ^ (s - 1) := by
  unfold J0
  have h1 : cexp (-(r : ℂ)) = (Real.exp (-r) : ℂ) := by
    rw [← Complex.ofReal_neg, (Complex.ofReal_exp (-r)).symm]
  rw [h1]

/-- `J0 s` is integrable over `(0,∞)` (Euler's integral, `0 < Re s`). -/
lemma integrable_J0 (s : ℂ) (hs : 0 < s.re) : IntegrableOn (J0 s) (Ioi 0) := by
  have hg : IntegrableOn (fun r : ℝ => ↑(Real.exp (-r)) * (r : ℂ) ^ (s - 1)) (Ioi 0) := by
    simpa [Complex.GammaIntegral] using Complex.GammaIntegral_convergent hs
  refine hg.congr_fun ?_ measurableSet_Ioi
  intro r hr
  exact (J0_eq_GammaIntegrand s r hr).symm

/-- **T2**: the rotated integrand is integrable over `(0,∞)` for `0 < Re s`, `|θ| < π/2`. -/
lemma integrable_Jr (s : ℂ) (hs : 0 < s.re) {θ : ℝ} (hθ : |θ| < Real.pi / 2) :
    IntegrableOn (Jr s θ) (Ioi 0) := by
  have hcos : 0 < Real.cos θ := by
    exact Real.cos_pos_of_mem_Ioo (abs_lt.mp hθ)
  constructor
  · have hc1 : ContinuousOn (fun r : ℝ => cexp (-((r : ℂ) * cexp (-(I * (θ : ℂ)))))) (Ioi 0) := by
      fun_prop
    have hc2 : ContinuousOn (fun r : ℝ => (r : ℂ) ^ (s - 1)) (Ioi 0) := by
      apply continuousOn_of_forall_continuousAt
      intro r hr
      refine ContinuousAt.comp (continuousAt_cpow_const ?_) Complex.continuous_ofReal.continuousAt
      exact ofReal_mem_slitPlane.2 hr
    exact (hc1.mul hc2).aestronglyMeasurable measurableSet_Ioi
  · rw [← hasFiniteIntegral_norm_iff]
    have hreal : IntegrableOn (fun r : ℝ => Real.exp (-(r * Real.cos θ)) * r ^ (s.re - 1)) (Ioi 0) := by
      refine (GRRealInt.real_integrable_exp_neg_mul_rpow hcos hs).congr_fun ?_ measurableSet_Ioi
      intro r hr
      have harg : -(Real.cos θ * r) = -(r * Real.cos θ) := by ring
      simp [harg]
    refine HasFiniteIntegral.congr hreal.2 ?_
    apply (ae_restrict_iff' measurableSet_Ioi).mpr
    filter_upwards with r hr
    exact (norm_Jr s θ r hr).symm

/-- Substitution `r = e^x` on the negative half-line: image `(0, exp a)`. -/
lemma integral_comp_exp_Iio (g : ℝ → ℂ) (a : ℝ) :
    ∫ x in Iio a, Real.exp x • g (Real.exp x) = ∫ y in Ioo 0 (Real.exp a), g y := by
  rw [← Real.image_exp_Iio a]
  rw [MeasureTheory.integral_image_eq_integral_abs_deriv_smul (s := Iio a) (f := Real.exp)
    (f' := fun x : ℝ => Real.exp x) measurableSet_Iio
    (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt)
    (fun x _ y _ hxy => Real.exp_injective hxy) g]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Iio ?_
  intro x hx
  simp [abs_of_pos (Real.exp_pos x)]

/-- Substitution `r = e^x` on the negative half-line: integrability transfer. -/
lemma integrableOn_comp_exp_Iio (g : ℝ → ℂ) (a : ℝ) :
    IntegrableOn (fun x => Real.exp x • g (Real.exp x)) (Iio a) ↔
      IntegrableOn g (Ioo 0 (Real.exp a)) := by
  rw [← Real.image_exp_Iio a]
  rw [MeasureTheory.integrableOn_image_iff_integrableOn_abs_deriv_smul (s := Iio a) (f := Real.exp)
    (f' := fun x : ℝ => Real.exp x) measurableSet_Iio
    (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt)
    (fun x _ y _ hxy => Real.exp_injective hxy) g]
  refine Iff.intro ?_ ?_
  · intro h
    exact h.congr_fun (fun x hx => by simp [abs_of_pos (Real.exp_pos x)]) measurableSet_Iio
  · intro h
    exact h.congr_fun (fun x hx => by simp [abs_of_pos (Real.exp_pos x)]) measurableSet_Iio

/-- abbreviation: the substitution integrand `x ↦ e^x • g(e^x)`. -/
noncomputable def phi (g : ℝ → ℂ) (x : ℝ) : ℂ := Real.exp x • g (Real.exp x)

/-- integrability of `x ↦ e^x • g(e^x)` on the two half-lines. -/
lemma integrable_comp_exp_union (g : ℝ → ℂ) (hg : IntegrableOn g (Ioi 0)) :
    IntegrableOn (phi g) (Iio 0 ∪ Ioi 0) := by
  have hIio : IntegrableOn (phi g) (Iio 0) := by
    exact (integrableOn_comp_exp_Iio g 0).2 (hg.mono_set (by intro x hx; exact hx.1))
  have hIoi : IntegrableOn (phi g) (Ioi 0) := by
    exact (integrableOn_comp_exp_Ioi g 0).2 (hg.mono_set (by intro x hx; exact lt_trans (Real.exp_pos 0) (by simpa using hx)))
  exact hIio.union hIoi

/-- disjointness of the split pieces of `(0,∞)`. -/
lemma disjoint_Iio_Ioi : Disjoint (Iio (0 : ℝ)) (Ioi 0) := by
  rw [Set.disjoint_left]
  intro x hx1 hx2
  change x < 0 at hx1
  change 0 < x at hx2
  linarith

/-- disjointness of the split pieces of `(0,∞)`. -/
lemma disjoint_Ioo_singleton : Disjoint (Ioo (0 : ℝ) 1) ({1} : Set ℝ) := by
  rw [Set.disjoint_left]
  intro x hx1 hxs
  change 0 < x ∧ x < 1 at hx1
  have hxs' : x = 1 := Set.mem_singleton_iff.mp hxs
  linarith

/-- disjointness of the split pieces of `(0,∞)`. -/
lemma disjoint_IooIoi_singleton : Disjoint (Ioo (0 : ℝ) 1 ∪ ({1} : Set ℝ)) (Ioi 1) := by
  rw [Set.disjoint_left]
  intro x hxAC hxB
  change 1 < x at hxB
  rcases hxAC with hxA | hxs
  · change 0 < x ∧ x < 1 at hxA
    linarith
  · have hxs' : x = 1 := Set.mem_singleton_iff.mp hxs
    linarith

/-- `∫_{(0,1)} g + ∫_{(1,∞)} g = ∫_{(0,∞)} g`. -/
lemma integral_Ioi_eq_add (g : ℝ → ℂ) (hg : IntegrableOn g (Ioi 0)) :
    (∫ y in Ioo (0 : ℝ) 1, g y) + (∫ y in Ioi 1, g y) = ∫ y in Ioi 0, g y := by
  have hA : IntegrableOn g (Ioo (0 : ℝ) 1) := hg.mono_set (by intro x hx; exact hx.1)
  have hB : IntegrableOn g (Ioi 1) := hg.mono_set (by intro x hx; exact lt_trans zero_lt_one (by simpa using hx))
  have hC : IntegrableOn g ({1} : Set ℝ) := hg.mono_set (by intro x hx; simp at hx; simp [hx])
  have hsing : (∫ y in ({1} : Set ℝ), g y) = 0 := by
    rw [MeasureTheory.integral_singleton]
    have hvol : volume.real ({1} : Set ℝ) = 0 := by
      change (volume ({1} : Set ℝ)).toReal = 0
      rw [MeasureTheory.measure_singleton (x := (1 : ℝ))]
      simp
    rw [hvol]
    simp
  have hAC : (∫ y in Ioo (0 : ℝ) 1, g y) + (∫ y in ({1} : Set ℝ), g y)
      = ∫ y in Ioo (0 : ℝ) 1 ∪ ({1} : Set ℝ), g y := by
    exact (MeasureTheory.setIntegral_union (s := Ioo (0 : ℝ) 1) (t := ({1} : Set ℝ))
      disjoint_Ioo_singleton (measurableSet_singleton 1) hA hC).symm
  have hACB : (∫ y in Ioo (0 : ℝ) 1 ∪ ({1} : Set ℝ), g y) + (∫ y in Ioi 1, g y)
      = ∫ y in (Ioo (0 : ℝ) 1 ∪ ({1} : Set ℝ)) ∪ Ioi 1, g y := by
    exact (MeasureTheory.setIntegral_union (s := Ioo (0 : ℝ) 1 ∪ ({1} : Set ℝ)) (t := Ioi 1)
      disjoint_IooIoi_singleton measurableSet_Ioi (hA.union hC) hB).symm
  calc
    (∫ y in Ioo (0 : ℝ) 1, g y) + (∫ y in Ioi 1, g y)
        = ((∫ y in Ioo (0 : ℝ) 1, g y) + (∫ y in ({1} : Set ℝ), g y)) + (∫ y in Ioi 1, g y) := by
          rw [hsing]
          ring
    _ = (∫ y in Ioo (0 : ℝ) 1 ∪ ({1} : Set ℝ), g y) + (∫ y in Ioi 1, g y) := by rw [hAC]
    _ = ∫ y in (Ioo (0 : ℝ) 1 ∪ ({1} : Set ℝ)) ∪ Ioi 1, g y := hACB
    _ = ∫ y in Ioi 0, g y := by rw [Ioi_eq_union]

/-- integral of `x ↦ e^x • g(e^x)` over the two half-lines equals `∫_{(0,∞)} g`. -/
lemma integral_comp_exp_union (g : ℝ → ℂ) (hg : IntegrableOn g (Ioi 0)) :
    (∫ x in Iio 0 ∪ Ioi 0, phi g x) = ∫ y in Ioi 0, g y := by
  calc
    (∫ x in Iio 0 ∪ Ioi 0, phi g x)
        = (∫ x in Iio 0, phi g x) + (∫ x in Ioi 0, phi g x) := by
          have hpieces := MeasureTheory.integrableOn_union.mp (integrable_comp_exp_union g hg)
          exact MeasureTheory.setIntegral_union (s := Iio (0 : ℝ)) (t := Ioi 0)
            disjoint_Iio_Ioi measurableSet_Ioi hpieces.1 hpieces.2
    _ = (∫ y in Ioo 0 1, g y) + (∫ y in Ioi 1, g y) := by
          change (∫ x in Iio 0, Real.exp x • g (Real.exp x)) + (∫ x in Ioi 0, Real.exp x • g (Real.exp x))
            = (∫ y in Ioo 0 1, g y) + (∫ y in Ioi 1, g y)
          rw [integral_comp_exp_Iio g 0, integral_comp_exp_Ioi g 0]
          norm_num
    _ = ∫ y in Ioi 0, g y := integral_Ioi_eq_add g hg

/-- whole-line substitution: `∫_ℝ e^x • g(e^x) = ∫_{(0,∞)} g`. -/
lemma integral_comp_exp (g : ℝ → ℂ) (hg : IntegrableOn g (Ioi 0)) :
    (∫ x : ℝ, phi g x) = ∫ y in Ioi 0, g y := by
  calc
    (∫ x : ℝ, phi g x) = ∫ x in (Set.univ : Set ℝ), phi g x := by simp
    _ = ∫ x in (Iio 0 ∪ Ioi 0), phi g x :=
      (MeasureTheory.setIntegral_congr_set Iio_union_Ioi_ae_univ).symm
    _ = ∫ y in Ioi 0, g y := integral_comp_exp_union g hg

/-- whole-line integrability of `x ↦ e^x • g(e^x)`. -/
lemma integrable_comp_exp (g : ℝ → ℂ) (hg : IntegrableOn g (Ioi 0)) : Integrable (phi g) := by
  have hunion : IntegrableOn (phi g) (Iio 0 ∪ Ioi 0) := integrable_comp_exp_union g hg
  have huniv : IntegrableOn (phi g) (Set.univ : Set ℝ) := hunion.congr_set_ae Iio_union_Ioi_ae_univ.symm
  exact (MeasureTheory.integrableOn_univ).mp huniv

/-- `∫_ℝ Hs s = Γ(s)` for `0 < Re s`. -/
lemma integral_Hs (s : ℂ) (hs : 0 < s.re) : (∫ x : ℝ, Hs s x) = Complex.Gamma s := by
  have hφ : (fun x : ℝ => Hs s x) = phi (J0 s) := by
    funext x
    exact GRBase.Hs_smul s x
  rw [hφ]
  rw [integral_comp_exp (J0 s) (integrable_J0 s hs)]
  have hg : (∫ y in Ioi 0, J0 s y) = Complex.GammaIntegral s := by
    rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun y hy => J0_eq_GammaIntegrand s y hy)]
    rfl
  rw [hg, ← Complex.Gamma_eq_integral hs]

/-- `∫_ℝ Hr s θ = e^{-iθs}·∫_{(0,∞)} Jr s θ`. -/
lemma integral_Hr (s : ℂ) (θ : ℝ) (hs : 0 < s.re) (hθ : |θ| < Real.pi / 2) :
    (∫ x : ℝ, Hr s θ x) = cexp (-((I * (θ : ℂ)) * s)) * (∫ y in Ioi 0, Jr s θ y) := by
  have hφ : (fun x : ℝ => Hr s θ x) = fun x => cexp (-((I * (θ : ℂ)) * s)) * phi (Jr s θ) x := by
    funext x
    exact GRBase.Hr_smul s θ x
  rw [hφ]
  rw [MeasureTheory.integral_const_mul (cexp (-((I * (θ : ℂ)) * s))) (phi (Jr s θ))]
  rw [integral_comp_exp (Jr s θ) (integrable_Jr s hs hθ)]

/-- `Hs s` is integrable over `ℝ`. -/
lemma integrable_Hs (s : ℂ) (hs : 0 < s.re) : Integrable (Hs s) := by
  have hφ : (fun x : ℝ => Hs s x) = phi (J0 s) := by
    funext x
    exact GRBase.Hs_smul s x
  change Integrable (fun x : ℝ => Hs s x)
  rw [hφ]
  exact integrable_comp_exp (J0 s) (integrable_J0 s hs)

/-- `Hr s θ` is integrable over `ℝ`. -/
lemma integrable_Hr (s : ℂ) (θ : ℝ) (hs : 0 < s.re) (hθ : |θ| < Real.pi / 2) :
    Integrable (Hr s θ) := by
  have hφ : (fun x : ℝ => Hr s θ x) = fun x => cexp (-((I * (θ : ℂ)) * s)) * phi (Jr s θ) x := by
    funext x
    exact GRBase.Hr_smul s θ x
  change Integrable (fun x : ℝ => Hr s θ x)
  rw [hφ]
  have hf : Integrable (phi (Jr s θ)) := integrable_comp_exp (Jr s θ) (integrable_Jr s hs hθ)
  exact hf.const_mul (cexp (-((I * (θ : ℂ)) * s)))

end
end PL.GRSubst


/-!
# Vanishing of the vertical edges of the Γ contour rectangle (PL.GRVert)

For `0 < Re s` and `|θ| < π/2`, the rectangle with corners `(-T, 0)` and `(T, -θ)`
(complex coordinates) has vertical edges at `Re z = ±T` on which the Γ-contour integrand
`F(z) = e^{-e^z}·e^{s·z}` is exponentially small:

    ‖V s x₀ y‖ = ‖e^{-e^{x₀+iy}}·e^{s·(x₀+iy)}‖ = e^{-e^{x₀}·cos y}·e^{s.re·x₀ - s.im·y}

so for the right edge (`x₀ = T → +∞`) the factor `e^{-e^T·cosθ}·e^{s.re·T}` kills everything,
and for the left edge (`x₀ = -T → -∞`) the factor `e^{-s.re·T}` kills everything
(`e^{-e^{-T}·cos y} ≤ 1`).  These two theorems (`right_edge_tendsto`, `left_edge_tendsto`) say
that the two vertical boundary integrals `∫_{y in 0..(-θ)} V s (±T) y` tend to `0` as `T → ∞`.

## Proof structure implemented below

1. Pointwise norm identity (`norm_V_eq`): for every real `y`,

       ‖V s x₀ y‖ = exp (-(exp x₀ * cos y)) * exp (s.re * x₀ - s.im * y)

   (`Complex.norm_exp`, `Complex.exp_re`, re/im of `(x₀:ℂ) + (y:ℂ) * I`).

2. Trig monotonicity (`cos_le_cos_of_abs_le`): `|y| ≤ |θ|`, `|θ| < π/2`  ⟹  `cos θ ≤ cos y`,
   via `Real.cos_abs` and `Real.cos_le_cos_of_nonneg_of_le_pi`; together with `Real.exp_pos`
   and monotonicity of `exp` this gives the pointwise bound `norm_V_le`:

       ‖V s x₀ y‖ ≤ exp (-(exp x₀ * cos θ)) * exp (s.re * x₀ + |s.im| * |θ|).

3. Integral bounds (`right_edge_norm_le`, `left_edge_norm_le`) via
   `intervalIntegral.norm_integral_le_of_norm_le_const`, using that `y ∈ Ι 0 (-θ)` forces
   `|y| ≤ |θ|` (`abs_le_of_mem_uIoc`); for the left edge the additional factor
   `exp (-(exp (-T) * cos θ)) ≤ 1` (`left_edge_pointwise_le`) removes the double exponential.

4. Decay `tendsto_exp_neg_exp_mul`: `exp (-(exp T · c)) · exp (k · T) → 0` when `c > 0`,
   from `Real.tendsto_exp_div_pow_atTop` (exp grows faster than linearly), so the exponent
   `k·T - c·exp T` tends to `atBot`, and `Real.tendsto_exp_atBot`.

5. `right_edge_tendsto` / `left_edge_tendsto`: squeeze the norm of the boundary integral
   between `0` and the decaying envelope, then use `tendsto_zero_iff_norm_tendsto_zero`.
-/

open Complex Filter MeasureTheory Set
open scoped Real Topology
set_option autoImplicit false

namespace PL.GRVert

noncomputable section

/-- The Γ-contour integrand restricted to a vertical line: `V s x₀ y = F s (x₀ + iy)`. -/
noncomputable def V (s : ℂ) (x₀ y : ℝ) : ℂ :=
  cexp (-cexp ((x₀ : ℂ) + (y : ℂ) * I)) * cexp (s * ((x₀ : ℂ) + (y : ℂ) * I))

/-- Real part of `(x : ℂ) + (y : ℂ) * I`. -/
lemma re_ofReal_add_mul_I (x y : ℝ) : ((x : ℂ) + (y : ℂ) * I).re = x := by
  rw [Complex.add_re, Complex.ofReal_re, Complex.mul_I_re, Complex.ofReal_im]
  ring_nf

/-- Imaginary part of `(x : ℂ) + (y : ℂ) * I`. -/
lemma im_ofReal_add_mul_I (x y : ℝ) : ((x : ℂ) + (y : ℂ) * I).im = y := by
  rw [Complex.add_im, Complex.ofReal_im, Complex.mul_I_im, Complex.ofReal_re]
  ring_nf

/-- Real part of `s · (x₀ + iy)` for real `x₀`, `y`. -/
lemma re_smul_ofReal_add_mul_I (s : ℂ) (x₀ y : ℝ) :
    (s * ((x₀ : ℂ) + (y : ℂ) * I)).re = s.re * x₀ - s.im * y := by
  rw [Complex.mul_re, re_ofReal_add_mul_I, im_ofReal_add_mul_I]

/-- Exact norm of the vertical-line integrand: `‖V s x₀ y‖ = e^{-e^{x₀}cos y} e^{s.re·x₀ - s.im·y}`. -/
lemma norm_V_eq (s : ℂ) (x₀ y : ℝ) :
    ‖V s x₀ y‖ = Real.exp (-(Real.exp x₀ * Real.cos y)) * Real.exp (s.re * x₀ - s.im * y) := by
  unfold V
  rw [norm_mul]
  have h1 : ‖cexp (-cexp ((x₀ : ℂ) + (y : ℂ) * I))‖ =
      Real.exp (-(Real.exp x₀ * Real.cos y)) := by
    rw [Complex.norm_exp]
    congr 1
    rw [Complex.neg_re, Complex.exp_re, re_ofReal_add_mul_I, im_ofReal_add_mul_I]
  have h2 : ‖cexp (s * ((x₀ : ℂ) + (y : ℂ) * I))‖ = Real.exp (s.re * x₀ - s.im * y) := by
    rw [Complex.norm_exp]
    congr 1
    rw [re_smul_ofReal_add_mul_I]
  rw [h1, h2]

/-- For `|y| ≤ |θ| < π/2`: `cos θ ≤ cos y`. -/
lemma cos_le_cos_of_abs_le {θ y : ℝ} (hθ : |θ| < Real.pi / 2) (hy : |y| ≤ |θ|) :
    Real.cos θ ≤ Real.cos y := by
  have hθπ : |θ| ≤ Real.pi := by linarith [Real.pi_pos]
  calc
    Real.cos θ = Real.cos |θ| := by rw [Real.cos_abs]
    _ ≤ Real.cos |y| := Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg y) hθπ hy
    _ = Real.cos y := by rw [Real.cos_abs]

/-- `|θ| < π/2` ⟹ `0 < cos θ`. -/
lemma cos_pos_of_abs_lt_pi_div_two {θ : ℝ} (hθ : |θ| < Real.pi / 2) : 0 < Real.cos θ := by
  exact Real.cos_pos_of_mem_Ioo (abs_lt.mp hθ)

/-- Pointwise norm bound on the vertical lines, valid for `|y| ≤ |θ| < π/2`:

    ‖V s x₀ y‖ ≤ exp (-(exp x₀ * cos θ)) * exp (s.re * x₀ + |s.im| * |θ|)  -/
lemma norm_V_le (s : ℂ) (x₀ : ℝ) {θ y : ℝ} (hθ : |θ| < Real.pi / 2) (hy : |y| ≤ |θ|) :
    ‖V s x₀ y‖ ≤ Real.exp (-(Real.exp x₀ * Real.cos θ)) * Real.exp (s.re * x₀ + |s.im| * |θ|) := by
  rw [norm_V_eq]
  have hcos : Real.cos θ ≤ Real.cos y := cos_le_cos_of_abs_le hθ hy
  have hc1 : Real.exp x₀ * Real.cos θ ≤ Real.exp x₀ * Real.cos y :=
    mul_le_mul_of_nonneg_left hcos (Real.exp_pos x₀).le
  have hExp1 : Real.exp (-(Real.exp x₀ * Real.cos y)) ≤ Real.exp (-(Real.exp x₀ * Real.cos θ)) := by
    exact Real.exp_le_exp.mpr (by linarith)
  have hsm : -(s.im * y) ≤ |s.im| * |θ| := by
    calc
      -(s.im * y) ≤ |s.im * y| := neg_le_abs (s.im * y)
      _ = |s.im| * |y| := by rw [abs_mul]
      _ ≤ |s.im| * |θ| := mul_le_mul_of_nonneg_left hy (abs_nonneg s.im)
  have hExp2 : Real.exp (s.re * x₀ - s.im * y) ≤ Real.exp (s.re * x₀ + |s.im| * |θ|) := by
    exact Real.exp_le_exp.mpr (by linarith)
  exact mul_le_mul hExp1 hExp2 (Real.exp_pos _).le (Real.exp_pos _).le

/-- Any point of the open-closed interval `Ι 0 (-θ)` lies in `[-|θ|, |θ|]`. -/
lemma abs_le_of_mem_uIoc {θ : ℝ} {y : ℝ} (hy : y ∈ Set.uIoc 0 (-θ)) : |y| ≤ |θ| := by
  rw [Set.mem_uIoc] at hy
  rcases hy with h | h
  · have hy0 : 0 ≤ y := le_of_lt h.1
    have hθ0 : θ ≤ 0 := by linarith
    rw [abs_of_nonneg hy0, abs_of_nonpos hθ0]
    exact h.2
  · have hθp : 0 ≤ θ := by linarith
    rw [abs_of_nonpos h.2, abs_of_nonneg hθp]
    linarith

/-- Norm bound for the right-edge vertical integral. -/
lemma right_edge_norm_le (s : ℂ) {θ : ℝ} (hθ : |θ| < Real.pi / 2) (T : ℝ) :
    ‖∫ y in 0..(-θ), V s T y‖ ≤
      (Real.exp (-(Real.exp T * Real.cos θ)) * Real.exp (s.re * T + |s.im| * |θ|)) * |θ| := by
  have hpt : ∀ y ∈ Set.uIoc 0 (-θ), ‖V s T y‖ ≤
      Real.exp (-(Real.exp T * Real.cos θ)) * Real.exp (s.re * T + |s.im| * |θ|) := by
    intro y hy
    exact norm_V_le s T hθ (abs_le_of_mem_uIoc hy)
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := -θ)
    (f := fun y => V s T y) hpt
  simpa [sub_zero] using hb

/-- Pointwise bound on the left edge: `‖V s (-T) y‖ ≤ e^{-s.re·T}·e^{|s.im||θ|}`. -/
lemma left_edge_pointwise_le (s : ℂ) {θ y : ℝ} (hθ : |θ| < Real.pi / 2) (hy : |y| ≤ |θ|) (T : ℝ) :
    ‖V s (-T) y‖ ≤ Real.exp (-(s.re * T)) * Real.exp (|s.im| * |θ|) := by
  have hb := norm_V_le s (-T) hθ hy
  have hnonneg : 0 ≤ Real.exp (-T) * Real.cos θ :=
    mul_nonneg (Real.exp_pos (-T)).le (cos_pos_of_abs_lt_pi_div_two hθ).le
  have hle1 : Real.exp (-(Real.exp (-T) * Real.cos θ)) ≤ 1 := by
    have hle0 : -(Real.exp (-T) * Real.cos θ) ≤ 0 := neg_nonpos.mpr hnonneg
    simpa using (Real.exp_le_exp.mpr hle0)
  calc
    ‖V s (-T) y‖ ≤ Real.exp (-(Real.exp (-T) * Real.cos θ)) * Real.exp (s.re * (-T) + |s.im| * |θ|) := hb
    _ = Real.exp (-(Real.exp (-T) * Real.cos θ)) * Real.exp (-(s.re * T) + |s.im| * |θ|) := by
      congr 1
      ring_nf
    _ = Real.exp (-(Real.exp (-T) * Real.cos θ)) * (Real.exp (-(s.re * T)) * Real.exp (|s.im| * |θ|)) := by
      rw [Real.exp_add]
    _ ≤ 1 * (Real.exp (-(s.re * T)) * Real.exp (|s.im| * |θ|)) := by
      exact mul_le_mul_of_nonneg_right hle1 (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
    _ = Real.exp (-(s.re * T)) * Real.exp (|s.im| * |θ|) := by simp

/-- Norm bound for the left-edge vertical integral. -/
lemma left_edge_norm_le (s : ℂ) {θ : ℝ} (hθ : |θ| < Real.pi / 2) (T : ℝ) :
    ‖∫ y in 0..(-θ), V s (-T) y‖ ≤
      Real.exp (-(s.re * T)) * Real.exp (|s.im| * |θ|) * |θ| := by
  have hpt : ∀ y ∈ Set.uIoc 0 (-θ), ‖V s (-T) y‖ ≤
      Real.exp (-(s.re * T)) * Real.exp (|s.im| * |θ|) := by
    intro y hy
    exact left_edge_pointwise_le s hθ (abs_le_of_mem_uIoc hy) T
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := -θ)
    (f := fun y => V s (-T) y) hpt
  simpa [sub_zero] using hb

/-- `exp (-(exp T · c)) · exp (k·T) → 0` as `T → ∞`, for `0 < c`. -/
lemma tendsto_exp_neg_exp_mul (c k : ℝ) (hc : 0 < c) :
    Tendsto (fun T : ℝ => Real.exp (-(Real.exp T * c)) * Real.exp (k * T)) atTop (𝓝 0) := by
  have hdiv : Tendsto (fun T : ℝ => c * (Real.exp T / T)) atTop atTop := by
    have h := Real.tendsto_exp_div_pow_atTop 1
    simpa [pow_one] using h.const_mul_atTop hc
  have hge : ∀ᶠ T in atTop, (k + 1) ≤ c * (Real.exp T / T) :=
    hdiv.eventually (eventually_ge_atTop (k + 1))
  have hmain : Tendsto (fun T : ℝ => k * T - c * Real.exp T) atTop atBot := by
    refine Filter.tendsto_atBot_mono' atTop ?hle Filter.tendsto_neg_atTop_atBot
    filter_upwards [hge, eventually_ge_atTop 1] with T hT hT1
    have hTpos : 0 < T := by linarith
    have hm : (k + 1) * T ≤ (c * (Real.exp T / T)) * T :=
      mul_le_mul_of_nonneg_right hT (le_of_lt hTpos)
    have hcancel : (c * (Real.exp T / T)) * T = c * Real.exp T := by
      field_simp [hTpos.ne']
    rw [hcancel] at hm
    linarith
  have hExp : Tendsto (fun T : ℝ => Real.exp (k * T - c * Real.exp T)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp hmain
  refine hExp.congr' (Filter.Eventually.of_forall (fun T => ?_))
  change Real.exp (k * T - c * Real.exp T) = Real.exp (-(Real.exp T * c)) * Real.exp (k * T)
  rw [← Real.exp_add]
  congr 1
  ring_nf

/-- The right vertical edge of the Γ-contour rectangle tends to zero as `T → ∞`. -/
theorem right_edge_tendsto (s : ℂ) (hs : 0 < s.re) {θ : ℝ} (hθ : |θ| < Real.pi / 2) :
    Tendsto (fun T : ℝ => ∫ y in 0..(-θ), V s T y) atTop (𝓝 0) := by
  have _hσ : 0 < s.re := hs
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hcos : 0 < Real.cos θ := cos_pos_of_abs_lt_pi_div_two hθ
  let Bd : ℝ → ℝ := fun T => Real.exp (-(Real.exp T * Real.cos θ)) * Real.exp (s.re * T)
  have hBd : Tendsto Bd atTop (𝓝 0) := tendsto_exp_neg_exp_mul (Real.cos θ) s.re hcos
  refine squeeze_zero (fun T => norm_nonneg _) (fun T => right_edge_norm_le s hθ T) ?_
  have hg : (fun T : ℝ =>
        (Real.exp (-(Real.exp T * Real.cos θ)) * Real.exp (s.re * T + |s.im| * |θ|)) * |θ|)
      = (fun T : ℝ => (|θ| * Real.exp (|s.im| * |θ|)) * Bd T) := by
    funext T
    dsimp [Bd]
    rw [Real.exp_add]
    ring_nf
  rw [hg]
  simpa using (tendsto_const_nhds.mul hBd)

/-- The left vertical edge of the Γ-contour rectangle tends to zero as `T → ∞`. -/
theorem left_edge_tendsto (s : ℂ) (hs : 0 < s.re) {θ : ℝ} (hθ : |θ| < Real.pi / 2) :
    Tendsto (fun T : ℝ => ∫ y in 0..(-θ), V s (-T) y) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero (fun T => norm_nonneg _) (fun T => left_edge_norm_le s hθ T) ?_
  have hneg : Tendsto (fun T : ℝ => Real.exp (-(s.re * T))) atTop (𝓝 0) := by
    have hst : Tendsto (fun T : ℝ => s.re * T) atTop atTop :=
      (Filter.tendsto_id : Tendsto (fun T : ℝ => T) atTop atTop).const_mul_atTop hs
    exact Real.tendsto_exp_neg_atTop_nhds_zero.comp hst
  have hg : (fun T : ℝ => Real.exp (-(s.re * T)) * Real.exp (|s.im| * |θ|) * |θ|)
      = (fun T : ℝ => (|θ| * Real.exp (|s.im| * |θ|)) * Real.exp (-(s.re * T))) := by
    funext T
    ring_nf
  rw [hg]
  simpa using (tendsto_const_nhds.mul hneg)

end
end PL.GRVert


/-!
# Left vertical edge of the Γ contour rectangle (PL.GRVertL)

Prove `left_edge_tendsto` below: with `V s x₀ y = e^{-e^{x₀+iy}}·e^{s(x₀+iy)}` (as in
`PL.GRVert`), for `0 < s.re` and `|θ| < π/2`,

    Tendsto (fun T : ℝ => ∫ y in 0..(-θ), V s (-T) y) atTop (𝓝 0)

## Proof plan
On the left edge `x₀ = -T`, for `|y| ≤ |θ|` (`|θ| < π/2`, so `cos y > 0`):
`‖V s (-T) y‖ = exp (-(e^{-T}·cos y))·exp (-s.re·T - s.im·y) ≤ exp (-s.re·T)·exp (|s.im|·|θ|)`
since `e^{-T}·cos y ≥ 0` (so `exp (-(…)) ≤ 1`) and `-s.im·y ≤ |s.im|·|θ|`.

Key steps used below:
- `norm_V_eq`: the exact pointwise norm identity of `V` (via `Complex.norm_exp` and
  `Complex.exp_re`).
- `mem_uIoc_abs_le`: `y ∈ uIoc 0 (-θ)` implies `|y| ≤ |θ|`.
- `norm_V_left_le`: the pointwise bound above.
- Then `intervalIntegral.norm_integral_le_of_norm_le_const` bounds the norm of the whole edge
  integral by `exp (-s.re·T)·exp (|s.im|·|θ|)·|θ|`, which tends to `0` because `s.re > 0`
  (`Real.tendsto_exp_atBot.comp`), and `squeeze_zero_norm` finishes.

Do NOT modify `Submission/GRVert.lean` (this file may only import it).  The statement of
`left_edge_tendsto` stays exactly as below.
-/

open Complex Filter MeasureTheory Set
open scoped Real Topology
set_option autoImplicit false

namespace PL.GRVertL

open PL.GRVert

noncomputable section

/-- Exact pointwise norm of the vertical-edge integrand:
`‖V s x₀ y‖ = exp (-(e^{x₀}·cos y)) · exp (s.re·x₀ - s.im·y)`. -/
lemma norm_V_eq (s : ℂ) (x₀ y : ℝ) :
    ‖V s x₀ y‖ = Real.exp (-(Real.exp x₀ * Real.cos y)) * Real.exp (s.re * x₀ - s.im * y) := by
  unfold V
  rw [norm_mul]
  have hw_re : (((x₀ : ℂ) + (y : ℂ) * I).re) = x₀ := by simp
  have hw_im : (((x₀ : ℂ) + (y : ℂ) * I).im) = y := by simp
  have hinner : (cexp ((x₀ : ℂ) + (y : ℂ) * I)).re = Real.exp x₀ * Real.cos y := by
    rw [Complex.exp_re, hw_re, hw_im]
  have hre1 : (-cexp ((x₀ : ℂ) + (y : ℂ) * I)).re = -(Real.exp x₀ * Real.cos y) := by
    simp [hinner]
  have h1 : ‖cexp (-cexp ((x₀ : ℂ) + (y : ℂ) * I))‖ = Real.exp (-(Real.exp x₀ * Real.cos y)) := by
    rw [Complex.norm_exp, hre1]
  have hre2 : (s * ((x₀ : ℂ) + (y : ℂ) * I)).re = s.re * x₀ - s.im * y := by
    rw [Complex.mul_re, hw_re, hw_im]
  have h2 : ‖cexp (s * ((x₀ : ℂ) + (y : ℂ) * I))‖ = Real.exp (s.re * x₀ - s.im * y) := by
    rw [Complex.norm_exp, hre2]
  rw [h1, h2]

/-- A point of the unordered interval between `0` and `-θ` has `|y| ≤ |θ|`. -/
lemma mem_uIoc_abs_le {θ y : ℝ} (hy : y ∈ uIoc 0 (-θ)) : |y| ≤ |θ| := by
  change y ∈ Ioc (min 0 (-θ)) (max 0 (-θ)) at hy
  have hlo : -|θ| ≤ min 0 (-θ) := by
    apply le_min
    · linarith [abs_nonneg θ]
    · linarith [le_abs_self θ]
  have hhi : max 0 (-θ) ≤ |θ| := by
    apply max_le
    · exact abs_nonneg θ
    · exact neg_le_abs θ
  have h1 : -|θ| ≤ y := le_trans hlo hy.1.le
  have h2 : y ≤ |θ| := le_trans hy.2 hhi
  exact abs_le.mpr ⟨h1, h2⟩

/-- Pointwise bound on the left edge: for `|y| ≤ |θ| < π/2`,
`‖V s (-T) y‖ ≤ exp (-s.re·T) · exp (|s.im|·|θ|)`. -/
lemma norm_V_left_le (s : ℂ) {θ : ℝ} (hθ : |θ| < Real.pi / 2)
    (T y : ℝ) (hy : |y| ≤ |θ|) :
    ‖V s (-T) y‖ ≤ Real.exp (-(s.re * T)) * Real.exp (|s.im| * |θ|) := by
  have hy_lt : |y| < Real.pi / 2 := lt_of_le_of_lt hy hθ
  have hcos0 : 0 < Real.cos y := Real.cos_pos_of_mem_Ioo (abs_lt.mp hy_lt)
  have hprod_nonneg : 0 ≤ Real.exp (-T) * Real.cos y :=
    mul_nonneg (Real.exp_pos (-T)).le hcos0.le
  have h_expA_le_one : Real.exp (-(Real.exp (-T) * Real.cos y)) ≤ 1 := by
    have h : -(Real.exp (-T) * Real.cos y) ≤ (0 : ℝ) := neg_nonpos.mpr hprod_nonneg
    simpa using Real.exp_le_exp.mpr h
  have hB : -(s.re * T) - s.im * y ≤ -(s.re * T) + |s.im| * |θ| := by
    have h1 : -(s.im * y) ≤ |s.im| * |y| := by
      calc
        -(s.im * y) ≤ |s.im * y| := neg_le_abs _
        _ = |s.im| * |y| := by rw [abs_mul]
    exact (add_le_add_iff_left (-(s.re * T))).2
      (le_trans h1 (mul_le_mul_of_nonneg_left hy (abs_nonneg s.im)))
  have h_expB : Real.exp (s.re * (-T) - s.im * y) ≤ Real.exp (-(s.re * T) + |s.im| * |θ|) := by
    have harg : s.re * (-T) - s.im * y = -(s.re * T) - s.im * y := by ring
    rw [harg]
    exact Real.exp_le_exp.mpr hB
  rw [norm_V_eq]
  calc
    Real.exp (-(Real.exp (-T) * Real.cos y)) * Real.exp (s.re * (-T) - s.im * y)
        ≤ 1 * Real.exp (s.re * (-T) - s.im * y) :=
            mul_le_mul h_expA_le_one le_rfl (Real.exp_pos _).le zero_le_one
    _ = Real.exp (s.re * (-T) - s.im * y) := by simp
    _ ≤ Real.exp (-(s.re * T) + |s.im| * |θ|) := h_expB
    _ = Real.exp (-(s.re * T)) * Real.exp (|s.im| * |θ|) := by rw [Real.exp_add]

/-- The left vertical edge of the Γ-contour rectangle tends to zero as `T → ∞`. -/
theorem left_edge_tendsto (s : ℂ) (hs : 0 < s.re) {θ : ℝ} (hθ : |θ| < Real.pi / 2) :
    Tendsto (fun T : ℝ => ∫ y in 0..(-θ), V s (-T) y) atTop (𝓝 0) := by
  let C : ℝ → ℝ := fun T => Real.exp (-(s.re * T)) * Real.exp (|s.im| * |θ|)
  have hnorm : ∀ T y, y ∈ uIoc 0 (-θ) → ‖V s (-T) y‖ ≤ C T := by
    intro T y hy
    exact norm_V_left_le s hθ T y (mem_uIoc_abs_le hy)
  have hbound : ∀ T, ‖∫ y in 0..(-θ), V s (-T) y‖ ≤ C T * |θ| := by
    intro T
    have hh := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := -θ) (C := C T)
      (f := fun y => V s (-T) y) (hnorm T)
    simpa using hh
  have hC0 : Tendsto C atTop (𝓝 0) := by
    have h1 : Tendsto (fun T : ℝ => Real.exp (-(s.re * T))) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp (Filter.tendsto_neg_atTop_atBot.comp
        (Filter.Tendsto.const_mul_atTop hs tendsto_id))
    simpa [C] using h1.mul (tendsto_const_nhds (x := Real.exp (|s.im| * |θ|)))
  have hphi0 : Tendsto (fun T : ℝ => C T * |θ|) atTop (𝓝 0) := by
    simpa using hC0.mul (tendsto_const_nhds (x := |θ|))
  exact squeeze_zero_norm hbound hphi0

end
end PL.GRVertL


/-!
# Vertical bounds for the complex Gamma function

The whole "Archimedean" analysis of Dirichlet L-functions (bounds for the gamma factors
appearing in the completed L-functions, convergence of the approximate-functional-equation
weight integrals, convexity bounds for `|L(σ + it, χ)|`) rests on one elementary fact,
proved here directly from Euler's integral representation:

`‖Γ(s)‖ ≤ Γ(Re s)`  whenever `0 < Re s`.

(For `s = σ + it` with `t ≠ 0` this is a strict inequality; the point is that the
imaginary part `t` never increases the modulus.  Everything else needed — lower bounds
via the reflection formula, ratios of `Complex.Gammaℝ` factors along vertical lines —
is derived from this.)

## Main definitions and results

* `norm_Gamma_le_norm_Gamma_re`: `‖Γ(s)‖ ≤ ‖Γ(Re s)‖` for `0 < Re s`.
* `Gammaℝ` (imported from `Complex`): Deligne's real gamma factor
  `Gammaℝ s = π^(-s/2) · Γ(s/2)`.
-/

open Complex Filter MeasureTheory Set
open scoped Real

set_option autoImplicit false

namespace PL.GammaVertical

/-- Pointwise norm identity for the integrand of Euler's integral. -/
lemma norm_integrand (s : ℂ) {x : ℝ} (hx : 0 < x) :
    ‖(Real.exp (-x) : ℂ) * (x : ℂ) ^ (s - 1)‖ = Real.exp (-x) * x ^ (s.re - 1) := by
  rw [norm_mul, Complex.norm_of_nonneg (le_of_lt (Real.exp_pos (-x))),
      norm_cpow_eq_rpow_re_of_pos hx]
  rw [Complex.sub_re, Complex.one_re]

/-- The Euler integral for the gamma function is non-negative for real exponents. -/
lemma integral_nonneg_Ioi {σ : ℝ} :
    (0 : ℝ) ≤ ∫ x : ℝ in Ioi (0 : ℝ), Real.exp (-x) * x ^ (σ - 1) := by
  refine integral_nonneg_of_ae ?_
  refine (ae_restrict_iff' (p := fun x : ℝ => 0 ≤ Real.exp (-x) * x ^ (σ - 1))
    measurableSet_Ioi).mpr ?_
  filter_upwards with x hx
  exact mul_nonneg (le_of_lt (Real.exp_pos (-x)))
    (Real.rpow_nonneg (le_of_lt (mem_Ioi.mp hx)) (σ - 1))

/--
**Vertical bound for the Gamma function.**  For `0 < Re s`, the modulus of `Γ(s)` is at
most the value of `Γ` at the real point `Re s`:

`‖Γ(s)‖ ≤ ‖Γ(Re s)‖`.
-/
theorem norm_Gamma_le_norm_Gamma_re (s : ℂ) (hs : 0 < s.re) :
    ‖Complex.Gamma s‖ ≤ ‖Complex.Gamma (s.re : ℂ)‖ := by
  have hsσ : 0 < (s.re : ℂ).re := by simpa using hs
  rw [Complex.Gamma_eq_integral hs, Complex.Gamma_eq_integral hsσ]
  let R : ℝ := ∫ x : ℝ in Ioi (0 : ℝ), Real.exp (-x) * x ^ (s.re - 1)
  have h1 : ‖Complex.GammaIntegral s‖ ≤ R := by
    calc
    ‖Complex.GammaIntegral s‖
        = ‖∫ x : ℝ in Ioi (0 : ℝ), (Real.exp (-x) : ℂ) * (x : ℂ) ^ (s - 1)‖ := by
          simp [Complex.GammaIntegral]
    _ ≤ ∫ x : ℝ in Ioi (0 : ℝ), ‖(Real.exp (-x) : ℂ) * (x : ℂ) ^ (s - 1)‖ := by
        exact MeasureTheory.norm_integral_le_integral_norm _
    _ = R := by
        dsimp [R]
        refine setIntegral_congr_fun measurableSet_Ioi ?_
        intro x hx
        exact norm_integrand s (mem_Ioi.mp hx)
  have h2 : ‖Complex.GammaIntegral (s.re : ℂ)‖ = R := by
    rw [Complex.GammaIntegral_ofReal]
    dsimp [R]
    rw [Complex.norm_of_nonneg (integral_nonneg_Ioi)]
  calc
    ‖Complex.GammaIntegral s‖ ≤ R := h1
    _ = ‖Complex.GammaIntegral (s.re : ℂ)‖ := h2.symm

/--
**Vertical bound for the Gamma function at half-shifted arguments.**  For a shift `a`
(so that the argument is `(z + a + I·t) / 2`, the shape that occurs in the archimedean
gamma factor of a Dirichlet L-function) and `0 < Re z`, `‖Γ((z + a + I t)/2)‖` is
bounded uniformly in `t : ℝ` by the value of `Γ` at the real midpoint
`(Re z + Re a) / 2`.
-/
theorem norm_Gamma_vertical_shifted_le (z a : ℂ) (t : ℝ) (hz : 0 < z.re) (ha : 0 ≤ a.re) :
    ‖Complex.Gamma ((z + a + I * t) / 2)‖
      ≤ ‖Complex.Gamma (((z.re + a.re) / 2 : ℝ) : ℂ)‖ := by
  have hdiv : ((z + a + I * t) / 2).re = (z.re + a.re) / 2 := by
    rw [Complex.div_re]
    simp
    ring_nf
  have hre : 0 < ((z + a + I * t) / 2).re := by
    rw [hdiv]
    exact div_pos (by linarith) (by norm_num)
  have h := norm_Gamma_le_norm_Gamma_re ((z + a + I * t) / 2) hre
  rwa [hdiv] at h

/-- Real part of a half: `(s / 2).re = s.re / 2`. -/
lemma re_of_half (s : ℂ) : (s / 2).re = s.re / 2 := by
  rw [Complex.div_re]
  norm_num
  ring

/--
**Vertical bound for Deligne's real gamma factor.**  For `0 < Re s`,
`‖Gammaℝ s‖ ≤ ‖Gammaℝ (Re s)‖` where `Gammaℝ s = π^(-s/2) · Γ(s/2)`.
-/
theorem norm_Gammaℝ_le_norm_Gammaℝ_re (s : ℂ) (hs : 0 < s.re) :
    ‖Complex.Gammaℝ s‖ ≤ ‖Complex.Gammaℝ (s.re : ℂ)‖ := by
  rw [Complex.Gammaℝ_def, Complex.Gammaℝ_def]
  rw [norm_mul, norm_mul]
  rw [norm_cpow_eq_rpow_re_of_pos Real.pi_pos, norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
  have h1 : (-s / 2).re = -s.re / 2 := by
    rw [Complex.div_re, Complex.neg_re]
    norm_num
    ring
  have h2 : (-(s.re : ℂ) / 2).re = -s.re / 2 := by
    rw [Complex.div_re, Complex.neg_re]
    norm_num
    ring
  rw [h1, h2]
  have hpos : 0 < (s / 2).re := by
    rw [re_of_half]
    exact div_pos hs (by norm_num)
  have h := norm_Gamma_le_norm_Gamma_re (s / 2) hpos
  have hArg : ((s / 2).re : ℂ) = (s.re : ℂ) / 2 := by
    rw [re_of_half]
    rw [Complex.ofReal_div]
    rw [show ((2 : ℝ) : ℂ) = (2 : ℂ) by norm_num]
  have hΓ : ‖Complex.Gamma (s / 2)‖ ≤ ‖Complex.Gamma ((s.re : ℂ) / 2)‖ := by
    simpa [hArg] using h
  exact mul_le_mul_of_nonneg_left hΓ (Real.rpow_nonneg (le_of_lt Real.pi_pos) _)

end PL.GammaVertical


/-!
# Lower bounds for the complex Gamma function in the critical strip

The completed L-function `Λ(s) = γ(s)·L(s)` can only be converted into upper bounds for
`|L(s)|` when the archimedean factor `γ(s)` does not vanish and does not get too small.
This file proves the elementary **lower bound** for `Γ` in the strip `0 < Re s < 1`,
directly from the Euler upper bound (a peer file `PL.GammaVertical`) and the
reflection formula:

`|Γ(σ + I t)| ≥ C(σ) · exp(-π |t|)`   for `0 < σ < 1`, all `t : ℝ`.

## Proof strategy (Euler's reflection formula)

1. For `z = σ + I·t`, reflection gives `Γ(z)·Γ(1 - z) = π / sin(π·z)`
   (`Complex.Gamma_mul_Gamma_one_sub`), so
   `1 / |Γ(z)| = |Γ(1 - z)| · |sin(π·z)| / π`.
2. `|Γ(1 - z)| ≤ Γ(1 - σ)`: apply `PL.GammaVertical.norm_Gamma_le_norm_Gamma_re`
   to `s = (1 - σ) - I·t` whose real part is `1 - σ > 0`, and identify the value at the
   real point `(1 - σ : ℝ)` (positive real; e.g. via `Complex.Gamma_ofReal`).
3. `|sin(π·σ + I·π·t)| ≤ exp(π|t|)`: prove first the auxiliary lemma
   `norm_sin_le_exp_im x y : ‖sin (x + I·y)‖ ≤ exp |y|`, using
   `Complex.sin_add_mul_I`, triangle inequality, `|cosh b|, |sinh b| ≤ exp |b|`
   (derive from `Real.cosh_add_sinh`, `Real.cosh_sub_sinh`, `Real.cosh_abs`, the
   nonnegativity of `Real.cosh` (`Real.cosh_pos`) and of `Real.sinh` on `[0, ∞)`,
   and `Real.exp` monotonicity), then specialize at `x = πσ, y = π t`.
4. Conclude with `C := π / ‖Γ ((1 - σ : ℝ) : ℂ)‖` (positive, since `Γ((1-σ:ℝ):ℂ) ≠ 0`
   by `Complex.Gamma_ne_zero_of_re_pos` because `1 - σ > 0`), dividing the reflection
   identity through by `|Γ(1 - z)|`.

All results are elementary and available in Mathlib as listed.
-/

open Complex Filter MeasureTheory Set
open scoped Real

set_option autoImplicit false

namespace PL.GammaLower

open PL.GammaVertical

/-- Norm of `cosh` at a real point. -/
lemma norm_cosh_ofReal (y : ℝ) : ‖Complex.cosh (y : ℂ)‖ = Real.cosh y := by
  rw [← Complex.ofReal_cosh]
  rw [Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_nonneg (le_of_lt (Real.cosh_pos y))]

/-- Norm of `sinh` at a real point. -/
lemma norm_sinh_ofReal (y : ℝ) : ‖Complex.sinh (y : ℂ)‖ = |Real.sinh y| := by
  rw [← Complex.ofReal_sinh]
  rw [Complex.norm_real, Real.norm_eq_abs]

/-- `cosh y + |sinh y| = e^|y|` for all real `y`. -/
lemma cosh_add_abs_sinh (y : ℝ) : Real.cosh y + |Real.sinh y| = Real.exp |y| := by
  by_cases hy : 0 ≤ y
  · have hs0 : 0 ≤ Real.sinh y := by
      rw [Real.sinh_eq]
      have h : Real.exp (-y) ≤ Real.exp y := (Real.exp_le_exp).2 (by linarith)
      exact div_nonneg (sub_nonneg.mpr h) (by norm_num)
    calc
      Real.cosh y + |Real.sinh y| = Real.cosh y + Real.sinh y := by rw [abs_of_nonneg hs0]
      _ = Real.exp y := by rw [Real.cosh_add_sinh]
      _ = Real.exp |y| := by rw [abs_of_nonneg hy]
  · have hy' : y ≤ 0 := le_of_not_ge hy
    have hs0 : Real.sinh y ≤ 0 := by
      rw [Real.sinh_eq]
      have h : Real.exp y - Real.exp (-y) ≤ 0 := sub_nonpos.mpr ((Real.exp_le_exp).2 (by linarith))
      exact (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).2 (by simpa using h)
    calc
      Real.cosh y + |Real.sinh y| = Real.cosh y - Real.sinh y := by
        rw [abs_of_nonpos hs0]
        ring
      _ = Real.exp (-y) := by rw [Real.cosh_sub_sinh]
      _ = Real.exp |y| := by rw [abs_of_nonpos hy']

/-- `|sin (x + I·y)| ≤ e^|y|` for real `x, y`. -/
lemma norm_sin_le_exp_im (x y : ℝ) : ‖Complex.sin (x + I * (y : ℂ))‖ ≤ Real.exp |y| := by
  have hz_re : ((x : ℂ) + I * (y : ℂ)).re = x := by simp
  have hz_im : ((x : ℂ) + I * (y : ℂ)).im = y := by simp
  have hsin := Complex.sin_eq ((x : ℂ) + I * (y : ℂ))
  rw [hz_re, hz_im] at hsin
  rw [hsin]
  calc
    ‖Complex.sin (x : ℂ) * Complex.cosh (y : ℂ) + Complex.cos (x : ℂ) * Complex.sinh (y : ℂ) * I‖
        ≤ ‖Complex.sin (x : ℂ) * Complex.cosh (y : ℂ)‖ +
            ‖Complex.cos (x : ℂ) * Complex.sinh (y : ℂ) * I‖ := norm_add_le _ _
    _ = ‖Complex.sin (x : ℂ)‖ * ‖Complex.cosh (y : ℂ)‖ +
        ‖Complex.cos (x : ℂ)‖ * ‖Complex.sinh (y : ℂ)‖ * ‖I‖ := by
          rw [norm_mul, norm_mul, norm_mul]
    _ = ‖Complex.sin (x : ℂ)‖ * ‖Complex.cosh (y : ℂ)‖ +
        ‖Complex.cos (x : ℂ)‖ * ‖Complex.sinh (y : ℂ)‖ := by
          rw [norm_I]; simp
    _ ≤ ‖Complex.cosh (y : ℂ)‖ + ‖Complex.sinh (y : ℂ)‖ := by
      have hsin1 : ‖Complex.sin (x : ℂ)‖ ≤ 1 := by
        rw [← Complex.ofReal_sin, Complex.norm_real, Real.norm_eq_abs]
        exact Real.abs_sin_le_one x
      have hcos1 : ‖Complex.cos (x : ℂ)‖ ≤ 1 := by
        rw [← Complex.ofReal_cos, Complex.norm_real, Real.norm_eq_abs]
        exact Real.abs_cos_le_one x
      have h1 : ‖Complex.sin (x : ℂ)‖ * ‖Complex.cosh (y : ℂ)‖ ≤ ‖Complex.cosh (y : ℂ)‖ := by
        simpa using mul_le_mul_of_nonneg_right hsin1 (norm_nonneg _)
      have h2 : ‖Complex.cos (x : ℂ)‖ * ‖Complex.sinh (y : ℂ)‖ ≤ ‖Complex.sinh (y : ℂ)‖ := by
        simpa using mul_le_mul_of_nonneg_right hcos1 (norm_nonneg _)
      exact add_le_add h1 h2
    _ = Real.exp |y| := by
      rw [norm_cosh_ofReal, norm_sinh_ofReal, cosh_add_abs_sinh]

/-- `|sin (π·(σ + I·t))| ≤ e^(π·|t|)` for real `σ, t`. -/
lemma sin_bound_aux (σ t : ℝ) :
    ‖Complex.sin ((Real.pi : ℂ) * ((σ : ℂ) + I * (t : ℂ)))‖ ≤ Real.exp (Real.pi * |t|) := by
  have harg : (Real.pi : ℂ) * ((σ : ℂ) + I * (t : ℂ)) =
      ((Real.pi * σ : ℝ) : ℂ) + I * ((Real.pi * t : ℝ) : ℂ) := by
    rw [Complex.ofReal_mul, Complex.ofReal_mul]
    ring
  rw [harg]
  have hs := norm_sin_le_exp_im (Real.pi * σ) (Real.pi * t)
  convert hs using 1
  rw [abs_mul, abs_of_nonneg (le_of_lt Real.pi_pos)]

/-- Lower bound for the complex Gamma function on the critical strip: for `0 < σ < 1`,
`C(σ) · exp (-π·|t|) ≤ |Γ(σ + I·t)|` for all real `t`. -/
theorem norm_Gamma_lower_bound (σ : ℝ) (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ,
      C * Real.exp (-Real.pi * |t|) ≤ ‖Complex.Gamma (σ + I * (t : ℂ))‖ := by
  refine ⟨Real.pi / ‖Complex.Gamma (((1 - σ : ℝ) : ℂ))‖, ?pos, ?body⟩
  · have h1σ : 0 < (1 - σ : ℝ) := by linarith
    have hg : Complex.Gamma (((1 - σ : ℝ) : ℂ)) ≠ 0 := by
      apply Complex.Gamma_ne_zero_of_re_pos
      simpa using h1σ
    exact div_pos Real.pi_pos (norm_pos_iff.mpr hg)
  · intro t
    let z : ℂ := (σ : ℂ) + I * (t : ℂ)
    change (Real.pi / ‖Complex.Gamma (((1 - σ : ℝ) : ℂ))‖) * Real.exp (-Real.pi * |t|)
      ≤ ‖Complex.Gamma z‖
    have hzre : z.re = σ := by simp [z]
    have hrez : 0 < z.re := by rw [hzre]; exact hσ0
    have hgz : Complex.Gamma z ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hrez
    have h1zre : (1 - z).re = 1 - σ := by simp [z, hzre]
    have hre1z : 0 < (1 - z).re := by rw [h1zre]; linarith
    have hg1z : Complex.Gamma (1 - z) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hre1z
    have hsin_ne : Complex.sin ((Real.pi : ℂ) * z) ≠ 0 := by
      intro hs
      have h := Complex.Gamma_mul_Gamma_one_sub z
      rw [hs, div_zero] at h
      exact (mul_ne_zero hgz hg1z) h
    have hnorm : ‖Complex.Gamma z‖ * ‖Complex.Gamma (1 - z)‖ =
        Real.pi / ‖Complex.sin ((Real.pi : ℂ) * z)‖ := by
      have h := congrArg (fun w : ℂ => ‖w‖) (Complex.Gamma_mul_Gamma_one_sub z)
      rw [norm_mul, norm_div] at h
      rw [Complex.norm_real, Real.norm_eq_abs] at h
      rw [abs_of_nonneg (le_of_lt Real.pi_pos)] at h
      exact h
    set a : ℝ := ‖Complex.Gamma z‖ with ha
    set b : ℝ := ‖Complex.Gamma (1 - z)‖ with hb
    set c : ℝ := ‖Complex.sin ((Real.pi : ℂ) * z)‖ with hc
    set d : ℝ := ‖Complex.Gamma (((1 - σ : ℝ) : ℂ))‖ with hd
    set e : ℝ := Real.exp (Real.pi * |t|) with he
    set f : ℝ := Real.exp (-Real.pi * |t|) with hf
    have hgz_pos : 0 < a := by dsimp [a]; exact norm_pos_iff.mpr hgz
    have hg1z_pos : 0 < b := by dsimp [b]; exact norm_pos_iff.mpr hg1z
    have hsin_pos : 0 < c := by dsimp [c]; exact norm_pos_iff.mpr hsin_ne
    have hd_pos : 0 < d := by
      dsimp [d]
      apply norm_pos_iff.mpr
      apply Complex.Gamma_ne_zero_of_re_pos
      simpa using (show 0 < (1 - σ : ℝ) by linarith)
    have he_pos : 0 < e := by dsimp [e]; exact Real.exp_pos _
    have hf_pos : 0 < f := by dsimp [f]; exact Real.exp_pos _
    have hprod : a * b * c = Real.pi := by
      rw [hnorm]
      rw [div_mul_cancel₀ _ (ne_of_gt hsin_pos)]
    have hg1z_ub : b ≤ d := by
      simpa [b, d, h1zre] using (norm_Gamma_le_norm_Gamma_re (1 - z) hre1z)
    have hsin_ub : c ≤ e := by
      simpa [c, e, z] using (sin_bound_aux σ t)
    have hef : e * f = 1 := by
      dsimp [e, f]
      rw [← Real.exp_add]
      ring_nf
      rw [Real.exp_zero]
    have hbc : b * c ≤ d * e := by
      exact mul_le_mul hg1z_ub hsin_ub (le_of_lt hsin_pos) (le_of_lt hd_pos)
    have hbcf : b * c * f ≤ d := by
      calc
        b * c * f ≤ (d * e) * f := mul_le_mul_of_nonneg_right hbc (le_of_lt hf_pos)
        _ = d := by
          rw [mul_assoc, hef, mul_one]
    have hπf : Real.pi * f ≤ a * d := by
      calc
        Real.pi * f = (a * b * c) * f := by rw [hprod]
        _ = a * (b * c * f) := by ring
        _ ≤ a * d := mul_le_mul_of_nonneg_left hbcf (le_of_lt hgz_pos)
    have hgoal : (Real.pi / d) * f ≤ a := by
      rw [div_mul_eq_mul_div]
      exact (div_le_iff₀ hd_pos).2 hπf
    simpa using hgoal

end PL.GammaLower


/-!
# Vertical bounds for archimedean gamma-factor ratios (even characters)

For an **even** Dirichlet character `χ` the archimedean gamma factor is
`γ(s) = Complex.Gammaℝ s = π^(-s/2) · Γ(s/2)` (Deligne's real gamma factor).

The approximate-functional-equation weight of `PL.AFE.afeWeight` contains the ratio
`γ(z + u) / γ(z)` evaluated on the vertical line `u = 1 + I·t`.  This file proves that
ratio is **bounded uniformly in `t`** for fixed `z` with `0 < Re z`; this is the input that
makes the defining integral of the weight absolutely convergent and lets one interchange
sums and integrals in the Mellin-inversion step of the AFE argument.

The proof reduces to the vertical bound `PL.GammaVertical.norm_Gamma_vertical_shifted_le`
(which is itself derived from `|Γ(s)| ≤ Γ(Re s)`, Euler's integral estimate) together with
the observation that `π^(-(1 + I t)/2)` has modulus `π^(-1/2)`.
-/

open Complex Filter MeasureTheory Set
open scoped Real

set_option autoImplicit false

namespace PL.GammaRatioEven

/-- Pointwise bound for the numerator `Γℝ(z + 1 + I t)`: the modulus of the gamma factor
at the shifted point is at most the value taken at the real midpoint `(Re z + 1)/2`,
uniformly in `t`.  The power `π^(-(z + 1 + I t)/2)` has modulus `π^(-(Re z + 1)/2)`
(`|a^w| = a^(Re w)` for real `a > 0`), and the Gamma factor is controlled by
`PL.GammaVertical.norm_Gamma_vertical_shifted_le` with shift `a = 1`. -/
lemma gammaRatio_even_num_bound (z : ℂ) (hz : 0 < z.re) (t : ℝ) :
    ‖Complex.Gammaℝ (z + 1 + (I * t : ℂ))‖
      ≤ (Real.pi ^ (-(z.re + 1) / 2 : ℝ)) *
          ‖Complex.Gamma (((z.re + 1) / 2 : ℝ) : ℂ)‖ := by
  rw [Complex.Gammaℝ_def, Complex.norm_mul]
  have h1 : ‖(Real.pi : ℂ) ^ (-(z + 1 + (I * t : ℂ)) / 2)‖
      = Real.pi ^ (-(z.re + 1) / 2 : ℝ) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
    congr
    simp
  rw [h1]
  have hv : ‖Complex.Gamma ((z + 1 + (I * t : ℂ)) / 2)‖
      ≤ ‖Complex.Gamma (((z.re + 1) / 2 : ℝ) : ℂ)‖ := by
    simpa using (PL.GammaVertical.norm_Gamma_vertical_shifted_le z 1 t hz (by norm_num))
  have hp : 0 ≤ Real.pi ^ (-(z.re + 1) / 2 : ℝ) := by
    exact le_of_lt (Real.rpow_pos_of_pos Real.pi_pos _)
  exact mul_le_mul_of_nonneg_left hv hp

/-- The denominator `Γℝ(z)` does not vanish for `0 < Re z`, so its modulus is a positive
real number. -/
lemma gammaℝ_z_norm_pos (z : ℂ) (hz : 0 < z.re) : 0 < ‖Complex.Gammaℝ z‖ := by
  have h := Complex.Gammaℝ_ne_zero_of_re_pos (s := z) hz
  rw [norm_pos_iff]
  exact h

/-- For an even character (gamma factor `Gammaℝ`), the vertical-line ratio
`γ(z + 1 + I t) / γ(z)` is bounded uniformly in `t : ℝ`, for fixed `z` with `0 < Re z`. -/
theorem gammaRatio_even_vertical_bound (z : ℂ) (hz : 0 < z.re) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ,
      ‖Complex.Gammaℝ (z + 1 + I * t) / Complex.Gammaℝ z‖ ≤ C := by
  let numB : ℝ := (Real.pi ^ (-(z.re + 1) / 2 : ℝ)) *
      ‖Complex.Gamma (((z.re + 1) / 2 : ℝ) : ℂ)‖
  let C : ℝ := numB / ‖Complex.Gammaℝ z‖
  have hGz_pos : 0 < ‖Complex.Gammaℝ z‖ := gammaℝ_z_norm_pos z hz
  have hnumB_pos : 0 < numB := by
    have h1 : 0 < Real.pi ^ (-(z.re + 1) / 2 : ℝ) := by
      exact Real.rpow_pos_of_pos Real.pi_pos _
    have h2 : 0 < ‖Complex.Gamma (((z.re + 1) / 2 : ℝ) : ℂ)‖ := by
      have hpos : 0 < (z.re + 1) / 2 := by linarith
      have hne : Complex.Gamma (((z.re + 1) / 2 : ℝ) : ℂ) ≠ 0 :=
        Complex.Gamma_ne_zero_of_re_pos (s := (((z.re + 1) / 2 : ℝ) : ℂ)) (by simpa using hpos)
      rw [norm_pos_iff]
      exact hne
    dsimp [numB]
    exact mul_pos h1 h2
  refine ⟨C, div_pos hnumB_pos hGz_pos, ?_⟩
  intro t
  have hnum := gammaRatio_even_num_bound z hz t
  calc
    ‖Complex.Gammaℝ (z + 1 + I * t) / Complex.Gammaℝ z‖
        = ‖Complex.Gammaℝ (z + 1 + I * t)‖ / ‖Complex.Gammaℝ z‖ := by
          rw [Complex.norm_div]
    _ ≤ numB / ‖Complex.Gammaℝ z‖ := div_le_div_of_nonneg_right hnum (le_of_lt hGz_pos)
    _ = C := by rfl

end PL.GammaRatioEven


/-!
# Vertical bounds for archimedean gamma-factor ratios (odd characters)

For an **odd** Dirichlet character `χ` the archimedean gamma factor is
`γ(s) = Complex.Gammaℝ (s + 1) = π^(-(s+1)/2) · Γ((s+1)/2)`.

The approximate-functional-equation weight of `PL.AFE.afeWeight` contains the ratio
`γ(z + u) / γ(z)` evaluated on the vertical line `u = 1 + I·t`.  This file proves that
ratio is **bounded uniformly in `t`** for fixed `z` with `0 < Re z`; this is the input that
makes the defining integral of the weight absolutely convergent and lets one interchange
sums and integrals in the Mellin-inversion step of the AFE argument.

The proof reduces to the vertical bound `PL.GammaVertical.norm_Gamma_vertical_shifted_le`
(taking the shift `a = 2`, since `γ(z + 1 + I t) = Gammaℝ (z + 2 + I t)`) together with
the observation that `π^(-(z + 2 + I t)/2) · π^(+(z+1)/2)` has modulus `π^(-1/2)`-scale
(constant in `t`).
-/

open Complex Filter MeasureTheory Set
open scoped Real

set_option autoImplicit false

namespace PL.GammaRatioOdd

lemma re_of_half (s : ℂ) : (s / 2).re = s.re / 2 := by
  rw [Complex.div_re]
  norm_num
  ring

/-- **Pointwise vertical bound for `Gammaℝ`.**  For `0 < Re s`, the modulus of
`Gammaℝ s = π^(-s/2) · Γ(s/2)` is at most its value at the real point `Re s`. -/
lemma norm_Gammaℝ_le_norm_Gammaℝ_re (s : ℂ) (hs : 0 < s.re) :
    ‖Complex.Gammaℝ s‖ ≤ ‖Complex.Gammaℝ (s.re : ℂ)‖ := by
  rw [Complex.Gammaℝ_def, Complex.Gammaℝ_def]
  rw [norm_mul, norm_mul]
  rw [norm_cpow_eq_rpow_re_of_pos Real.pi_pos, norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
  have h1 : (-s / 2).re = -s.re / 2 := by
    rw [Complex.div_re, Complex.neg_re]
    norm_num
    ring
  have h2 : (-(s.re : ℂ) / 2).re = -s.re / 2 := by
    rw [Complex.div_re, Complex.neg_re]
    norm_num
    ring
  rw [h1, h2]
  have hpos : 0 < (s / 2).re := by
    rw [re_of_half]
    exact div_pos hs (by norm_num)
  have h := PL.GammaVertical.norm_Gamma_le_norm_Gamma_re (s / 2) hpos
  have hArg : ((s / 2).re : ℂ) = (s.re : ℂ) / 2 := by
    rw [re_of_half]
    rw [Complex.ofReal_div]
    rw [show ((2 : ℝ) : ℂ) = (2 : ℂ) by norm_num]
  have hΓ : ‖Complex.Gamma (s / 2)‖ ≤ ‖Complex.Gamma ((s.re : ℂ) / 2)‖ := by
    simpa [hArg] using h
  exact mul_le_mul_of_nonneg_left hΓ (Real.rpow_nonneg (le_of_lt Real.pi_pos) _)

/-- For an odd character (gamma factor `Gammaℝ (· + 1)`), the vertical-line ratio
`γ(z + 1 + I t) / γ(z)` is bounded uniformly in `t : ℝ`, for fixed `z` with `0 < Re z`. -/
theorem gammaRatio_odd_vertical_bound (z : ℂ) (hz : 0 < z.re) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ,
      ‖Complex.Gammaℝ (z + 2 + I * t) / Complex.Gammaℝ (z + 1)‖ ≤ C := by
  have hz1 : 0 < (z + 1).re := by
    rw [Complex.add_re]
    simp
    linarith
  have hden_ne : Complex.Gammaℝ (z + 1) ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos hz1
  have hden_pos : 0 < ‖Complex.Gammaℝ (z + 1)‖ := norm_pos_iff.mpr hden_ne
  let C : ℝ := ‖Complex.Gammaℝ (((z.re + 2 : ℝ) : ℂ))‖ / ‖Complex.Gammaℝ (z + 1)‖
  refine ⟨C, ?_, ?_⟩
  · dsimp [C]
    exact div_pos
      (norm_pos_iff.mpr (Complex.Gammaℝ_ne_zero_of_re_pos (by rw [Complex.ofReal_re]; linarith)))
      hden_pos
  · intro t
    have hs : 0 < (z + 2 + I * t).re := by
      rw [Complex.add_re]
      simp
      linarith
    have hnum := norm_Gammaℝ_le_norm_Gammaℝ_re (z + 2 + I * t) hs
    have hrew : (z + 2 + I * t).re = z.re + 2 := by
      simp [Complex.add_re, Complex.mul_re, Complex.ofReal_im]
    have hnum' : ‖Complex.Gammaℝ (z + 2 + I * t)‖ ≤
        ‖Complex.Gammaℝ (((z.re + 2 : ℝ) : ℂ))‖ := by
      simpa [hrew] using hnum
    calc
      ‖Complex.Gammaℝ (z + 2 + I * t) / Complex.Gammaℝ (z + 1)‖
          = ‖Complex.Gammaℝ (z + 2 + I * t)‖ / ‖Complex.Gammaℝ (z + 1)‖ := by
            rw [norm_div]
      _ ≤ ‖Complex.Gammaℝ (((z.re + 2 : ℝ) : ℂ))‖ / ‖Complex.Gammaℝ (z + 1)‖ := by
            exact div_le_div_of_nonneg_right hnum' (le_of_lt hden_pos)
      _ = C := by
            rfl

end PL.GammaRatioOdd


/-!
# Root numbers have norm one (lemma for `Submission/LGrowth.lean`)

Prove: a primitive Dirichlet character's root number has norm `1`.
-/

open Complex DirichletCharacter
open scoped Real

set_option autoImplicit false

namespace PL.LGrowth

variable {N : ℕ} [NeZero N]

/-! ## Conjugation of the root number

The classical identity `conj (ε(χ)) = ε(χ⁻¹)` follows directly from the definition of the
root number as a Gauss sum divided by the archimedean factor `I ^ a` and by `N ^ (1/2)`:

* conjugating the Gauss sum inverts both characters (`star_gaussSum_eq`), and the inverse of
  the standard additive character is its multiplicative shift by `-1`, which introduces the
  value `χ (-1)` (`star_gaussSum_of_isPrimitive`);
* the archimedean factor is real (`I^0 = 1` in the even case, and `conj I = -I = χ(-1) · I`
  in the odd case);
* the factor `N ^ (1/2)` is a nonnegative real, hence fixed by conjugation.
-/

/-- The complex conjugate of the power `N ^ (1/2)` (a positive real) is itself. -/
lemma conj_cpow_half (N : ℕ) :
    star ((N : ℂ) ^ (1 / 2 : ℂ)) = (N : ℂ) ^ (1 / 2 : ℂ) := by
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (Nat.zero_le N)
  rw [← Complex.ofReal_natCast (n := N)]
  rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num]
  rw [← Complex.ofReal_cpow hN0 (1 / 2 : ℝ)]
  simp

/-- Variant with the exponent written `2⁻¹` (the form `simp` produces from `1 / 2`). -/
lemma conj_cpow_half' (N : ℕ) :
    star ((N : ℂ) ^ ((2 : ℂ)⁻¹)) = (N : ℂ) ^ ((2 : ℂ)⁻¹) := by
  have h := conj_cpow_half N
  rwa [show (1 / 2 : ℂ) = (2 : ℂ)⁻¹ by norm_num] at h

omit [NeZero N] in
/-- A primitive character has primitive inverse. -/
lemma isPrimitive_inv {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) :
    (χ⁻¹).IsPrimitive := by
  rw [IsPrimitive, conductor_inv, ← isPrimitive_def]
  exact hχ

/-- Conjugating the Gauss sum of `χ` against the standard additive character inverts both
characters (and the inverse additive character is the shift by `-1`). -/
lemma star_gaussSum_stdAddChar (χ : DirichletCharacter ℂ N) :
    star (gaussSum χ (ZMod.stdAddChar (N := N))) =
      gaussSum (χ⁻¹) ((ZMod.stdAddChar (N := N)).mulShift (-1)) := by
  calc
    star (gaussSum χ (ZMod.stdAddChar (N := N)))
        = gaussSum (χ⁻¹) (ZMod.stdAddChar (N := N))⁻¹ := by
          rw [star_gaussSum_eq]
    _ = gaussSum (χ⁻¹) ((ZMod.stdAddChar (N := N)).mulShift (-1)) := by
          rw [AddChar.inv_mulShift]

/-- For a primitive character, the conjugate Gauss sum is `χ (-1)` times the Gauss sum of the
inverse character: `conj (gaussSum χ e) = χ (-1) * gaussSum χ⁻¹ e`. -/
lemma star_gaussSum_of_isPrimitive (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive) :
    star (gaussSum χ (ZMod.stdAddChar (N := N))) =
      χ (-1) * gaussSum (χ⁻¹) (ZMod.stdAddChar (N := N)) := by
  calc
    star (gaussSum χ (ZMod.stdAddChar (N := N)))
        = gaussSum (χ⁻¹) ((ZMod.stdAddChar (N := N)).mulShift (-1)) :=
          star_gaussSum_stdAddChar χ
    _ = (χ⁻¹)⁻¹ (-1) * gaussSum (χ⁻¹) (ZMod.stdAddChar (N := N)) := by
          rw [gaussSum_mulShift_of_isPrimitive (ZMod.stdAddChar (N := N))
            (isPrimitive_inv hχ) (-1)]
    _ = χ (-1) * gaussSum (χ⁻¹) (ZMod.stdAddChar (N := N)) := by
          simp

omit [NeZero N] in
/-- Even characters have even inverse. -/
lemma Even_inv {χ : DirichletCharacter ℂ N} (hχ : χ.Even) : (χ⁻¹).Even := by
  change (χ⁻¹) (-1) = 1
  rw [MulChar.inv_apply_eq_inv' χ (-1), hχ]
  norm_num

omit [NeZero N] in
/-- Odd characters have odd inverse. -/
lemma Odd_inv {χ : DirichletCharacter ℂ N} (hχ : χ.Odd) : (χ⁻¹).Odd := by
  change (χ⁻¹) (-1) = -1
  rw [MulChar.inv_apply_eq_inv' χ (-1), hχ]
  norm_num

/-- The root number of an even primitive character conjugates to the root number of its
inverse. -/
lemma rootNumber_star_even (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive)
    (hE : χ.Even) :
    star (χ.rootNumber) = (χ⁻¹).rootNumber := by
  classical
  have hEinv : (χ⁻¹).Even := Even_inv hE
  have hconj : star (gaussSum χ (ZMod.stdAddChar (N := N))) =
      gaussSum (χ⁻¹) (ZMod.stdAddChar (N := N)) := by
    rw [star_gaussSum_of_isPrimitive χ hχ, hE]
    simp
  have hstarW : star ((N : ℂ) ^ ((2 : ℂ)⁻¹)) = (N : ℂ) ^ ((2 : ℂ)⁻¹) := conj_cpow_half' N
  rw [rootNumber]
  rw [← rootNumber]
  simp only [rootNumber]
  simp [hE, hEinv, hconj, hstarW]

/-- The root number of an odd primitive character conjugates to the root number of its
inverse. -/
lemma rootNumber_star_odd (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive)
    (hO : χ.Odd) :
    star (χ.rootNumber) = (χ⁻¹).rootNumber := by
  classical
  have hOinv : (χ⁻¹).Odd := Odd_inv hO
  have hconj : star (gaussSum χ (ZMod.stdAddChar (N := N))) =
      -gaussSum (χ⁻¹) (ZMod.stdAddChar (N := N)) := by
    rw [star_gaussSum_of_isPrimitive χ hχ, hO]
    simp
  have hnotE : ¬ χ.Even := by
    change ¬ (χ (-1) = 1)
    rw [hO]
    norm_num
  have hnotEinv : ¬ (χ⁻¹).Even := by
    change ¬ ((χ⁻¹) (-1) = 1)
    rw [hOinv]
    norm_num
  have hstarW : star ((N : ℂ) ^ ((2 : ℂ)⁻¹)) = (N : ℂ) ^ ((2 : ℂ)⁻¹) := conj_cpow_half' N
  rw [rootNumber]
  rw [← rootNumber]
  simp only [rootNumber]
  simp [hnotE, hnotEinv, hconj, hstarW]

/-- Conjugating the root number of a primitive character gives the root number of its inverse:
`conj (ε(χ)) = ε(χ⁻¹)`. -/
lemma rootNumber_star (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive) :
    star (χ.rootNumber) = (χ⁻¹).rootNumber := by
  rcases χ.even_or_odd with hE | hO
  · exact rootNumber_star_even χ hχ hE
  · exact rootNumber_star_odd χ hχ hO

/-! ## The product `ε(χ) · ε(χ⁻¹) = 1`

Applying the functional equation for `χ` and for `χ⁻¹` and comparing at a point where the
completed L-function does not vanish (say `s = 2`) shows that the product of the two root
numbers is `1`. -/

/-- The completed L-function of a (possibly trivial) character is non-zero at `s = 2`. -/
lemma completedLFunction_apply_two_ne_zero (χ : DirichletCharacter ℂ N) :
    DirichletCharacter.completedLFunction χ 2 ≠ 0 := by
  have hL : DirichletCharacter.LFunction χ 2 ≠ 0 :=
    DirichletCharacter.LFunction_ne_zero_of_one_le_re (χ := χ)
      (Or.inr (by norm_num : (2 : ℂ) ≠ 1)) (by norm_num : 1 ≤ (2 : ℂ).re)
  have hγ : gammaFactor χ 2 ≠ 0 := by
    rcases χ.even_or_odd with hχ | hχ
    · rw [hχ.gammaFactor_def]
      exact Gammaℝ_ne_zero_of_re_pos (by norm_num : 0 < (2 : ℂ).re)
    · rw [hχ.gammaFactor_def]
      exact Gammaℝ_ne_zero_of_re_pos (by norm_num : 0 < ((2 : ℂ) + 1).re)
  have h := LFunction_eq_completed_div_gammaFactor χ 2 (Or.inl (by norm_num : (2 : ℂ) ≠ 0))
  intro hzero
  apply hL
  rw [h]
  simp [hzero]

/-- The rearranged functional equation:
`DirichletCharacter.completedLFunction χ s = N ^ (1/2 - s) * rootNumber χ * DirichletCharacter.completedLFunction χ⁻¹ (1 - s)`. -/
lemma completedLFunction_eq (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive) (s : ℂ) :
    DirichletCharacter.completedLFunction χ s = (N : ℂ) ^ (1 / 2 - s) * χ.rootNumber *
      DirichletCharacter.completedLFunction (χ⁻¹) (1 - s) := by
  have h := DirichletCharacter.IsPrimitive.completedLFunction_one_sub hχ (1 - s)
  have hs : 1 - (1 - s) = s := by ring
  have hexp : (1 - s) - (1 / 2 : ℂ) = 1 / 2 - s := by ring
  rw [hs, hexp] at h
  exact h

/-- The root numbers of a primitive character and its inverse multiply to one:
`ε(χ) · ε(χ⁻¹) = 1`. -/
lemma rootNumber_mul_rootNumber_inv (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive) :
    χ.rootNumber * (χ⁻¹).rootNumber = 1 := by
  have hprod (s : ℂ) :
      DirichletCharacter.completedLFunction χ s =
        χ.rootNumber * (χ⁻¹).rootNumber * DirichletCharacter.completedLFunction χ s := by
    have h1 := completedLFunction_eq χ hχ s
    have h2 := completedLFunction_eq (χ⁻¹) (isPrimitive_inv hχ) (1 - s)
    have h2' : DirichletCharacter.completedLFunction (χ⁻¹) (1 - s) = (N : ℂ) ^ (1 / 2 - (1 - s)) *
        (χ⁻¹).rootNumber * DirichletCharacter.completedLFunction χ s := by
      simpa [inv_inv, sub_sub] using h2
    have hN : (N : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne N)
    have hpows : (N : ℂ) ^ (1 / 2 - s) * (N : ℂ) ^ (1 / 2 - (1 - s)) = 1 := by
      rw [← Complex.cpow_add (1 / 2 - s) (1 / 2 - (1 - s)) hN]
      have hexp : (1 / 2 - s) + (1 / 2 - (1 - s)) = (0 : ℂ) := by ring
      rw [hexp]
      exact Complex.cpow_zero (N : ℂ)
    calc
      DirichletCharacter.completedLFunction χ s
          = (N : ℂ) ^ (1 / 2 - s) * χ.rootNumber * DirichletCharacter.completedLFunction (χ⁻¹) (1 - s) := h1
      _ = (N : ℂ) ^ (1 / 2 - s) * χ.rootNumber *
              ((N : ℂ) ^ (1 / 2 - (1 - s)) * (χ⁻¹).rootNumber * DirichletCharacter.completedLFunction χ s) := by
            rw [h2']
      _ = (N : ℂ) ^ (1 / 2 - s) * (N : ℂ) ^ (1 / 2 - (1 - s)) *
              (χ.rootNumber * (χ⁻¹).rootNumber) * DirichletCharacter.completedLFunction χ s := by
            ring
      _ = 1 * (χ.rootNumber * (χ⁻¹).rootNumber) * DirichletCharacter.completedLFunction χ s := by
            rw [hpows]
      _ = χ.rootNumber * (χ⁻¹).rootNumber * DirichletCharacter.completedLFunction χ s := by
            ring
  exact mul_right_cancel₀ (completedLFunction_apply_two_ne_zero χ)
    (by simpa using (hprod (2 : ℂ)).symm)

/-- The root number of the inverse character is the inverse of the root number. -/
lemma rootNumber_inv (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive) :
    (χ⁻¹).rootNumber = (χ.rootNumber)⁻¹ := by
  exact eq_inv_of_mul_eq_one_right (rootNumber_mul_rootNumber_inv χ hχ)

/-- A primitive character's root number has norm `1`:
`‖rootNumber χ‖ = 1`. -/
theorem norm_rootNumber_of_isPrimitive (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive) :
    ‖χ.rootNumber‖ = 1 := by
  have h1 : (Complex.normSq χ.rootNumber : ℂ) = 1 := by
    rw [Complex.normSq_eq_conj_mul_self]
    change star χ.rootNumber * χ.rootNumber = 1
    rw [rootNumber_star χ hχ]
    simpa [mul_comm] using rootNumber_mul_rootNumber_inv χ hχ
  have h2 : Complex.normSq χ.rootNumber = 1 := by
    exact_mod_cast h1
  calc
    ‖χ.rootNumber‖ = Real.sqrt (Complex.normSq χ.rootNumber) := Complex.norm_def _
    _ = 1 := by simp [h2]

end PL.LGrowth


/-!
# Growth of Mellin transforms of strong FE-pairs (`Λ₀` bounded on vertical strips)

The vertical-line identity for the Mellin integrand of the approximate functional equation
(`PL.AfeVerticalLine.vertical_line_identity`) is proved under the strip-growth
hypothesis `Λ_growth χ s` (sub-exponential growth of the completed L-function in the strip
`s.re-1 ≤ Re z ≤ s.re+1`).  This module supplies that analytic input from **Mathlib's own
explicit Mellin-transform construction of the completed Hurwitz zeta functions**, avoiding
Phragmén–Lindelöf entirely:

**Key observation.**  The completed Hurwitz zeta functions of Mathlib
(`HurwitzZeta.completedHurwitzZetaEven₀ a s = (hurwitzEvenFEPair a).Λ₀ (s/2) / 2`,
`HurwitzZeta.completedHurwitzZetaOdd a s = (hurwitzOddFEPair a).Λ ((s+1)/2) / 2`) are
built from `WeakFEPair.Λ₀ s = mellin P.f_modif s`, the Mellin transform of the modified
kernel `f_modif`, which converges **absolutely for every `s`** (the kernel decays faster
than any power at both `0` and `∞`).  For a Mellin transform with absolute convergence the
norm on the vertical line `Re s = σ` is bounded by the **t-independent constant**
`∫₀^∞ ‖f_modif x‖ · x^(σ-1) dx`.  Hence each `P.Λ₀` — and therefore each completed Hurwitz
zeta component — is **bounded uniformly in `t` on every bounded vertical strip**.  Summing
the components against `χ(j)` (with the pole parts cancelling because `∑_j χ(j) = 0`) gives
a uniform-in-`t` bound for the completed Dirichlet L-function on any bounded vertical strip
— a vastly stronger statement than `Λ_growth`.

## Contents

* `mellinIntegrand_norm`: `‖t^(s-1) · f t‖ = ‖f t‖ · t^(Re s - 1)` for `t > 0`.
* `mellin_norm_le`: `‖mellin f s‖ ≤ ∫₀^∞ ‖f t‖ t^(Re s - 1) dt`.
* `mellinConvergent_norm_integrable`: the norm-integrand is integrable.
* `rpow_split_upper`: `t^(σ-1) ≤ t^(b-1) + t^(a-1)` for `a ≤ σ ≤ b`.
* `mellinConvergent_f_modif`: `MellinConvergent P.f_modif s` for every `s` (absolute
  convergence of the Mellin transform defining `P.Λ₀`), for any weak FE-pair `P`.
* **`lambda0_strip_bound`**: for any weak FE-pair `P` and any `a b`, there is `C ≥ 0` with
  `‖P.Λ₀ z‖ ≤ C` for all `z` with `a ≤ Re z ≤ b` (uniformly in `Im z`).
-/

open HurwitzZeta Complex MeasureTheory Filter Set
open scoped Real

set_option autoImplicit false

namespace PL.MellinGrowth

noncomputable section

/-- Pointwise norm identity for the Mellin integrand: for `t > 0`,
`‖t^(s-1) · f t‖ = ‖f t‖ · t^(Re s - 1)`. -/
lemma mellinIntegrand_norm (f : ℝ → ℂ) (s : ℂ) {t : ℝ} (ht : 0 < t) :
    ‖(t : ℂ) ^ (s - 1) * f t‖ = ‖f t‖ * (t : ℝ) ^ (s.re - 1) := by
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht]
  rw [Complex.sub_re, Complex.one_re]
  ring

/-- The norm of a Mellin transform is bounded by the integral of the pointwise norms,
which depends only on `Re s` (not on `Im s`). -/
lemma mellin_norm_le {f : ℝ → ℂ} {s : ℂ} (_hf : MellinConvergent f s) :
    ‖mellin f s‖ ≤ ∫ t : ℝ in Ioi 0, ‖f t‖ * (t : ℝ) ^ (s.re - 1) := by
  calc
    ‖mellin f s‖ = ‖∫ t : ℝ in Ioi 0, (t : ℂ) ^ (s - 1) * f t‖ := by
      simp [mellin]
    _ ≤ ∫ t : ℝ in Ioi 0, ‖(t : ℂ) ^ (s - 1) * f t‖ := by
      exact MeasureTheory.norm_integral_le_integral_norm _
    _ = ∫ t : ℝ in Ioi 0, ‖f t‖ * (t : ℝ) ^ (s.re - 1) := by
      refine setIntegral_congr_fun measurableSet_Ioi ?_
      intro t ht
      exact mellinIntegrand_norm f s (mem_Ioi.mp ht)

/-- Absolute Mellin convergence implies integrability of the norm integrand. -/
lemma mellinConvergent_norm_integrable {f : ℝ → ℂ} {s : ℂ} (hf : MellinConvergent f s) :
    IntegrableOn (fun t : ℝ => ‖f t‖ * (t : ℝ) ^ (s.re - 1)) (Ioi 0) := by
  have hnorm := hf.norm
  refine hnorm.congr ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr ?_
  filter_upwards with t ht
  simpa [smul_eq_mul] using mellinIntegrand_norm f s (mem_Ioi.mp ht)

/-- For `a ≤ σ ≤ b` and `t > 0`: `t^(σ-1) ≤ t^(b-1) + t^(a-1)`. -/
lemma rpow_split_upper {a b σ : ℝ} (hσ1 : a ≤ σ) (hσ2 : σ ≤ b) {t : ℝ} (ht0 : 0 < t) :
    t ^ (σ - 1) ≤ t ^ (b - 1) + t ^ (a - 1) := by
  by_cases ht1 : 1 ≤ t
  · have h1 : t ^ (σ - 1) ≤ t ^ (b - 1) := Real.rpow_le_rpow_of_exponent_le ht1 (by linarith)
    exact le_trans h1 (le_add_of_nonneg_right (Real.rpow_nonneg (le_of_lt ht0) (a - 1)))
  · have htle : t ≤ 1 := le_of_not_ge ht1
    have h2 : t ^ (σ - 1) ≤ t ^ (a - 1) := by
      exact Real.rpow_le_rpow_of_exponent_ge ht0 htle (by linarith)
    exact le_trans h2 (le_add_of_nonneg_left (Real.rpow_nonneg (le_of_lt ht0) (b - 1)))

/-- For a weak FE-pair, the modified kernel `f_modif` is Mellin-convergent at every point
(the kernel decays faster than any power at both `0⁺` and `∞`). -/
lemma mellinConvergent_f_modif (P : WeakFEPair ℂ) (s : ℂ) : MellinConvergent P.f_modif s := by
  let Q := P.toStrongFEPair
  have hQ : IsStrongFEPair Q := WeakFEPair.isStrongFEPair_toStrongFEPair P
  have hM : MellinConvergent Q.f s := by
    refine mellinConvergent_of_isBigO_rpow (a := s.re + 1) (b := s.re - 1) Q.hf_int ?_ ?_ ?_ ?_
    · have hf := IsStrongFEPair.hf_top hQ (-(s.re + 1))
      simpa [Q] using hf
    · linarith
    · have hf := IsStrongFEPair.hf_zero hQ (1 - s.re)
      simpa [Q] using hf
    · linarith
  convert hM using 1 <;> rfl

/-- Integral of a pointwise-nonnegative function over `(0,∞)` is nonnegative. -/
lemma integral_nonneg_Ioi_aux {g : ℝ → ℝ} (hg : ∀ t : ℝ, 0 < t → 0 ≤ g t) :
    (0 : ℝ) ≤ ∫ t : ℝ in Ioi 0, g t := by
  refine integral_nonneg_of_ae ?_
  refine (ae_restrict_iff' (p := fun t : ℝ => 0 ≤ g t) measurableSet_Ioi).mpr ?_
  filter_upwards with t ht
  exact hg t (mem_Ioi.mp ht)

/--
**Strip bound for `Λ₀` of a weak FE pair.**  For any `a b : ℝ` there is `C ≥ 0` with
`‖P.Λ₀ z‖ ≤ C` for all `z` with `a ≤ Re z ≤ b`.  In particular `P.Λ₀` is bounded
uniformly in `Im z` on every bounded vertical strip.  (Proof: `P.Λ₀ z = mellin P.f_modif z`
and the Mellin norm bound is independent of `Im z`, with the `σ`-dependence absorbed by the
`t^(σ-1) ≤ t^(b-1) + t^(a-1)` bound.)
-/
lemma lambda0_strip_bound (P : WeakFEPair ℂ) {a b : ℝ} :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, a ≤ z.re → z.re ≤ b → ‖P.Λ₀ z‖ ≤ C := by
  let fb : ℝ → ℝ := fun t => ‖P.f_modif t‖ * (t : ℝ) ^ (b - 1)
  let fa : ℝ → ℝ := fun t => ‖P.f_modif t‖ * (t : ℝ) ^ (a - 1)
  have hMa : MellinConvergent P.f_modif (a : ℂ) := mellinConvergent_f_modif P (a : ℂ)
  have hMb : MellinConvergent P.f_modif (b : ℂ) := mellinConvergent_f_modif P (b : ℂ)
  have hfb : IntegrableOn fb (Ioi 0) := by
    simpa [fb, Complex.ofReal_re] using mellinConvergent_norm_integrable hMb
  have hfa : IntegrableOn fa (Ioi 0) := by
    simpa [fa, Complex.ofReal_re] using mellinConvergent_norm_integrable hMa
  refine ⟨(∫ t : ℝ in Ioi 0, fb t) + (∫ t : ℝ in Ioi 0, fa t), ?_, ?_⟩
  · exact add_nonneg (integral_nonneg_Ioi_aux (fun t ht => by
        dsimp [fb]; exact mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (le_of_lt ht) _)))
      (integral_nonneg_Ioi_aux (fun t ht => by
        dsimp [fa]; exact mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (le_of_lt ht) _)))
  · intro z hza hzb
    let gz : ℝ → ℝ := fun t => ‖P.f_modif t‖ * (t : ℝ) ^ (z.re - 1)
    have hgz : IntegrableOn gz (Ioi 0) := by
      simpa [gz] using mellinConvergent_norm_integrable (mellinConvergent_f_modif P z)
    have hz' : ‖P.Λ₀ z‖ ≤ ∫ t : ℝ in Ioi 0, gz t := by
      simpa [gz, WeakFEPair.Λ₀] using mellin_norm_le (s := z) (mellinConvergent_f_modif P z)
    have hmono : (∫ t : ℝ in Ioi 0, gz t) ≤
        (∫ t : ℝ in Ioi 0, fb t) + (∫ t : ℝ in Ioi 0, fa t) := by
      have hle : gz ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] (fun t : ℝ => fb t + fa t) := by
        refine (ae_restrict_iff' measurableSet_Ioi).mpr ?_
        filter_upwards with t ht
        dsimp [gz, fb, fa]
        have hs := rpow_split_upper (a := a) (b := b) (σ := z.re) hza hzb (mem_Ioi.mp ht)
        exact le_trans (mul_le_mul_of_nonneg_left hs (norm_nonneg _)) (by
          rw [mul_add])
      calc
        (∫ t : ℝ in Ioi 0, gz t) ≤ ∫ t : ℝ in Ioi 0, fb t + fa t := by
          exact integral_mono_ae hgz (hfb.add hfa) hle
        _ = (∫ t : ℝ in Ioi 0, fb t) + (∫ t : ℝ in Ioi 0, fa t) := by
          exact integral_add hfb hfa
    exact le_trans hz' hmono

end
end PL.MellinGrowth


/-!
# Completed Hurwitz zeta components are bounded on vertical strips

Each completed Hurwitz zeta component used in Mathlib's analytic continuation of Dirichlet
L-functions is `P.Λ₀` of an explicit weak FE-pair, evaluated at `s/2` (even case) or
`(s+1)/2` (odd case).  By `PL.MellinGrowth.lambda0_strip_bound` each such component
is **bounded uniformly in `Im s` on every bounded vertical strip**.

## Results

* `completedHurwitzZetaEven₀_strip_bound`: for any `a : UnitAddCircle` and `c d : ℝ` there is
  `C ≥ 0` with `‖completedHurwitzZetaEven₀ a z‖ ≤ C` for all `z` with `c ≤ Re z ≤ d`.
* `completedHurwitzZetaOdd_strip_bound`: the same for `completedHurwitzZetaOdd a z`
  (using that the odd FE-pair has `f₀ = g₀ = 0`, so `Λ = Λ₀`).
-/

open HurwitzZeta Complex MeasureTheory Filter Set
open scoped Real

set_option autoImplicit false

namespace PL.HurwitzStrip

noncomputable section

/-- Real part of `(z + 1) / 2`. -/
lemma re_add_one_div_two (z : ℂ) : ((z + 1) / 2).re = (z.re + 1) / 2 := by
  rw [Complex.div_re]
  norm_num
  ring

/-- Real part of `z / 2`. -/
lemma re_div_two (z : ℂ) : (z / 2).re = z.re / 2 := by
  rw [Complex.div_re]
  norm_num
  ring

/-- The even completed Hurwitz zeta component `completedHurwitzZetaEven₀ a` is bounded
uniformly in the imaginary part on any bounded vertical strip. -/
lemma completedHurwitzZetaEven₀_strip_bound (a : UnitAddCircle) {c d : ℝ} :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ z : ℂ, c ≤ z.re → z.re ≤ d → ‖completedHurwitzZetaEven₀ a z‖ ≤ C := by
  rcases PL.MellinGrowth.lambda0_strip_bound (hurwitzEvenFEPair a) (a := c / 2)
      (b := d / 2) with ⟨C, hC0, hC⟩
  refine ⟨C / 2, div_nonneg hC0 (by norm_num), ?_⟩
  intro z hzc hzd
  have hre : (z / 2).re = z.re / 2 := re_div_two z
  have hz1 : c / 2 ≤ (z / 2).re := by
    rw [hre]
    exact div_le_div_of_nonneg_right hzc (by norm_num)
  have hz2 : (z / 2).re ≤ d / 2 := by
    rw [hre]
    exact div_le_div_of_nonneg_right hzd (by norm_num)
  have hb : ‖(hurwitzEvenFEPair a).Λ₀ (z / 2)‖ ≤ C := hC (z / 2) hz1 hz2
  calc
    ‖completedHurwitzZetaEven₀ a z‖ = ‖(hurwitzEvenFEPair a).Λ₀ (z / 2) / 2‖ := by rfl
    _ = ‖(hurwitzEvenFEPair a).Λ₀ (z / 2)‖ / 2 := by rw [norm_div]; norm_num
    _ ≤ C / 2 := by
      exact div_le_div_of_nonneg_right hb (by norm_num)

/-- The odd completed Hurwitz zeta component `completedHurwitzZetaOdd a` is bounded
uniformly in the imaginary part on any bounded vertical strip. -/
lemma completedHurwitzZetaOdd_strip_bound (a : UnitAddCircle) {c d : ℝ} :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ z : ℂ, c ≤ z.re → z.re ≤ d → ‖completedHurwitzZetaOdd a z‖ ≤ C := by
  have hΛ : ∀ w : ℂ, (hurwitzOddFEPair a).Λ w = (hurwitzOddFEPair a).Λ₀ w := by
    intro w
    rw [WeakFEPair.Λ]
    simp
  rcases PL.MellinGrowth.lambda0_strip_bound (hurwitzOddFEPair a)
      (a := (c + 1) / 2) (b := (d + 1) / 2) with ⟨C, hC0, hC⟩
  refine ⟨C / 2, div_nonneg hC0 (by norm_num), ?_⟩
  intro z hzc hzd
  have hre : ((z + 1) / 2).re = (z.re + 1) / 2 := re_add_one_div_two z
  have hz1 : (c + 1) / 2 ≤ ((z + 1) / 2).re := by
    rw [hre]
    exact div_le_div_of_nonneg_right (by linarith) (by norm_num)
  have hz2 : ((z + 1) / 2).re ≤ (d + 1) / 2 := by
    rw [hre]
    exact div_le_div_of_nonneg_right (by linarith) (by norm_num)
  have hb : ‖(hurwitzOddFEPair a).Λ₀ ((z + 1) / 2)‖ ≤ C := hC ((z + 1) / 2) hz1 hz2
  calc
    ‖completedHurwitzZetaOdd a z‖ = ‖(hurwitzOddFEPair a).Λ ((z + 1) / 2) / 2‖ := by rfl
    _ = ‖(hurwitzOddFEPair a).Λ₀ ((z + 1) / 2)‖ / 2 := by
      rw [norm_div, hΛ]; norm_num
    _ ≤ C / 2 := by
      exact div_le_div_of_nonneg_right hb (by norm_num)

end
end PL.HurwitzStrip


/-!
# The completed Dirichlet L-function is bounded on vertical strips

This file proves the analytic growth fact which (via `PL.AfeVerticalLine.Λ_growth`)
permits the passage `T → ∞` in the rectangle/Cauchy argument of the approximate functional
equation:

**`completedLFunction_strip_bound`**: for a non-trivial character `χ : DirichletCharacter ℂ N`
and any `c d : ℝ` there is `C ≥ 0` with `‖χ.completedLFunction z‖ ≤ C` for all
`z : ℂ` with `c ≤ Re z ≤ d` — i.e. the completed L-function is **bounded uniformly in
`Im z` on every bounded vertical strip**.

## Proof strategy

Unfold `χ.completedLFunction z = ZMod.completedLFunction χ z`:

`ZMod.completedLFunction χ z =
   (N:ℂ)^(-z) · ∑ j : ZMod N, χ j · completedHurwitzZetaEven (toAddCircle j) z
 + (N:ℂ)^(-z) · ∑ j : ZMod N, χ j · completedHurwitzZetaOdd (toAddCircle j) z`.

The two inner sums differ from the `Λ₀`-based sums `∑ j, χ j · completedHurwitzZetaEven₀ ...`
(resp. the plain `completedHurwitzZetaOdd` terms) only by the pole corrections coming from
`completedHurwitzZetaEven_eq`, and *Mathlib* performs that whole summation once and for all
in `ZMod.completedLFunction_eq`:

`ZMod.completedLFunction Φ s = completedLFunction₀ Φ s - N^(-s) · Φ 0 / s
                               - N^(-s) · (∑ j, Φ j) / (1-s)`

where `completedLFunction₀ Φ s = N^(-s) · ∑ j, Φ j · completedHurwitzZetaEven₀ (toAddCircle j) s
  + N^(-s) · ∑ j, Φ j · completedHurwitzZetaOdd (toAddCircle j) s`.

For a **non-trivial** character `χ ≠ 1` the two correction terms vanish: `χ 0 = 0` (from
`χ.map_zero' hN` once `N ≠ 1`, which follows from `χ ≠ 1` via `DirichletCharacter.level_one'`),
and `∑ j, χ j = 0` (`MulChar.sum_eq_zero_of_ne_one`).  Hence
`DirichletCharacter.completedLFunction χ z = completedLFunction₀ χ z`.

By `HurwitzStrip.completedHurwitzZetaEven₀_strip_bound` and
`.completedHurwitzZetaOdd_strip_bound` each component `completedHurwitzZetaEven₀ a`
(resp. `completedHurwitzZetaOdd a`) is bounded uniformly in `Im z` on the strip, with a bound
`Ce a` (resp. `Co a`) that may depend on `a : UnitAddCircle` and on `c d`.  Bounding the
finite sums with the triangle inequality (`norm_sum_le`), `‖χ j‖ ≤ 1`
(`χ.norm_le_one`), and `‖(N:ℂ)^(-z)‖ ≤ (N:ℝ)^(max (-c) (-d))`
(`Complex.norm_cpow_eq_rpow_re_of_pos` + `Real.rpow_le_rpow_of_exponent_le` since
`1 ≤ (N:ℝ)`), the bound `C` is the finite quantity
`(N:ℝ)^(max (-c) (-d)) · ((∑ j, Ce j) + (∑ j, Co j))`, where
`Ce j`/`Co j` are the per-component strip bounds chosen by `Classical.choose`.

## Main consequences

* `completedLFunction_strip_bound`: the theorem above.
* `completedLFunction_vertical_bound_strip`: same statement, phrased as a function of a
  complex strip parameter: for `0 < σ < 1` and a *primitive* `χ ≠ 1`,
  `∃ C ≥ 0, ∀ z, σ - 1 ≤ z.re → z.re ≤ σ + 1 → ‖DirichletCharacter.completedLFunction χ z‖ ≤ C`
  (this is the precise hypothesis used to instantiate `AfeVerticalLine.Λ_growth`).
-/

open HurwitzZeta Complex MeasureTheory Filter DirichletCharacter
open scoped Real BigOperators

set_option autoImplicit false

namespace PL.CompletedStrip

noncomputable section

variable {N : ℕ} [NeZero N]

/-- `toAddCircle j = 0 ↔ j = 0`. -/
lemma toAddCircle_eq_zero' (j : ZMod N) : ZMod.toAddCircle j = 0 ↔ j = 0 :=
  ZMod.toAddCircle_eq_zero

/-- A nontrivial character modulo `N` forces `N ≠ 1`. -/
lemma ne_one_of_character_ne_one (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) : N ≠ 1 := by
  intro hN
  exact hχ (DirichletCharacter.level_one' χ hN)

/-- The sum of a nontrivial character over all residues is zero. -/
lemma sum_char_zero (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) :
    (∑ j : ZMod N, χ j) = 0 :=
  χ.sum_eq_zero_of_ne_one hχ

/-- Only the residue `0` has `toAddCircle j = 0`, so
`∑ j, χ j · (if toAddCircle j = 0 then 1 else 0) = χ 0`. -/
lemma sum_char_ite_zero (χ : DirichletCharacter ℂ N) :
    (∑ j : ZMod N, χ j * (if ZMod.toAddCircle j = 0 then (1 : ℂ) else 0)) = χ 0 := by
  simp

/-- `ZMod.completedLFunction` of the character, written as
`(N:ℂ)^(-z) · (even part + odd part)`. -/
lemma completedLFunction_zmod_def (χ : DirichletCharacter ℂ N) (z : ℂ) :
    ZMod.completedLFunction χ z =
      (N : ℂ) ^ (-z) * (∑ j : ZMod N, χ j * completedHurwitzZetaEven (ZMod.toAddCircle j) z)
        + (N : ℂ) ^ (-z) * (∑ j : ZMod N, χ j * completedHurwitzZetaOdd (ZMod.toAddCircle j) z) := by
  rfl

/-- Bounding factor for `‖(N:ℂ)^(-z)‖` on the strip: `(N:ℝ)^(max (-c) (-d))`. -/
lemma norm_cpow_N_le {c d : ℝ} {z : ℂ} (hz1 : c ≤ z.re) (hz2 : z.re ≤ d) :
    ‖(N : ℂ) ^ (-z)‖ ≤ (N : ℝ) ^ (max (-c) (-d)) := by
  have hNpos : (0 : ℝ) < N := by
    exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne N))
  have hN1 : (1 : ℝ) ≤ N := by
    exact_mod_cast (Nat.succ_le_of_lt (Nat.pos_of_ne_zero (NeZero.ne N)))
  calc
    ‖(N : ℂ) ^ (-z)‖ = (N : ℝ) ^ (-z).re := by
      exact norm_cpow_eq_rpow_re_of_pos hNpos (-z)
    _ ≤ (N : ℝ) ^ (max (-c) (-d)) := by
      apply Real.rpow_le_rpow_of_exponent_le hN1
      rw [neg_re]
      exact le_max_of_le_left (neg_le_neg hz1)

/--
**The completed Dirichlet L-function of a nontrivial character is bounded uniformly in
`Im z` on every bounded vertical strip.**
-/
theorem completedLFunction_strip_bound (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) {c d : ℝ} :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ z : ℂ, c ≤ z.re → z.re ≤ d → ‖χ.completedLFunction z‖ ≤ C := by
  classical
  have hN : N ≠ 1 := ne_one_of_character_ne_one χ hχ
  have hχ0 : χ 0 = 0 := χ.map_zero' hN
  have hsum0 : (∑ j : ZMod N, χ j) = 0 := sum_char_zero χ hχ
  -- A per-residue bound for each entire component `completedHurwitzZetaEven₀ (toAddCircle j)`.
  let Ce : ZMod N → ℝ := fun j =>
    Classical.choose (HurwitzStrip.completedHurwitzZetaEven₀_strip_bound (ZMod.toAddCircle j)
      (c := c) (d := d))
  have hCe0 : ∀ j : ZMod N, 0 ≤ Ce j := fun j =>
    (Classical.choose_spec (HurwitzStrip.completedHurwitzZetaEven₀_strip_bound (ZMod.toAddCircle j)
      (c := c) (d := d))).1
  have hCe : ∀ (j : ZMod N) (z : ℂ), c ≤ z.re → z.re ≤ d →
      ‖completedHurwitzZetaEven₀ (ZMod.toAddCircle j) z‖ ≤ Ce j := by
    intro j z hz1 hz2
    exact (Classical.choose_spec (HurwitzStrip.completedHurwitzZetaEven₀_strip_bound
      (ZMod.toAddCircle j) (c := c) (d := d))).2 z hz1 hz2
  -- A per-residue bound for each odd component `completedHurwitzZetaOdd (toAddCircle j)`.
  let Co : ZMod N → ℝ := fun j =>
    Classical.choose (HurwitzStrip.completedHurwitzZetaOdd_strip_bound (ZMod.toAddCircle j)
      (c := c) (d := d))
  have hCo0 : ∀ j : ZMod N, 0 ≤ Co j := fun j =>
    (Classical.choose_spec (HurwitzStrip.completedHurwitzZetaOdd_strip_bound (ZMod.toAddCircle j)
      (c := c) (d := d))).1
  have hCo : ∀ (j : ZMod N) (z : ℂ), c ≤ z.re → z.re ≤ d →
      ‖completedHurwitzZetaOdd (ZMod.toAddCircle j) z‖ ≤ Co j := by
    intro j z hz1 hz2
    exact (Classical.choose_spec (HurwitzStrip.completedHurwitzZetaOdd_strip_bound
      (ZMod.toAddCircle j) (c := c) (d := d))).2 z hz1 hz2
  let B : ℝ := (N : ℝ) ^ max (-c) (-d)
  let CE := ∑ j : ZMod N, Ce j
  let CO := ∑ j : ZMod N, Co j
  have hB0 : 0 ≤ B := by
    dsimp [B]
    exact Real.rpow_nonneg (by exact_mod_cast (Nat.zero_le N)) _
  have hCE0 : 0 ≤ CE := Finset.sum_nonneg (fun j _ => hCe0 j)
  have hCO0 : 0 ≤ CO := Finset.sum_nonneg (fun j _ => hCo0 j)
  refine ⟨B * (CE + CO), mul_nonneg hB0 (add_nonneg hCE0 hCO0), ?_⟩
  intro z hz1 hz2
  -- For a nontrivial character the pole corrections vanish, so
  -- `χ.completedLFunction z = ZMod.completedLFunction₀ χ z` (Mathlib's entire variant).
  have hmain : χ.completedLFunction z = ZMod.completedLFunction₀ χ z := by
    change ZMod.completedLFunction χ z = ZMod.completedLFunction₀ χ z
    rw [ZMod.completedLFunction_eq]
    simp [hχ0, hsum0]
  rw [hmain]
  -- Even-part sum is bounded by `CE`.
  have hSe : ‖(∑ j : ZMod N, χ j * completedHurwitzZetaEven₀ (ZMod.toAddCircle j) z)‖ ≤ CE := by
    dsimp [CE]
    calc
      ‖(∑ j : ZMod N, χ j * completedHurwitzZetaEven₀ (ZMod.toAddCircle j) z)‖
          ≤ ∑ j : ZMod N, ‖χ j * completedHurwitzZetaEven₀ (ZMod.toAddCircle j) z‖ := by
            exact norm_sum_le _ _
      _ ≤ ∑ j : ZMod N, Ce j := by
          refine Finset.sum_le_sum ?_
          intro j _
          calc
            ‖χ j * completedHurwitzZetaEven₀ (ZMod.toAddCircle j) z‖
                ≤ ‖χ j‖ * ‖completedHurwitzZetaEven₀ (ZMod.toAddCircle j) z‖ := norm_mul_le _ _
            _ ≤ ‖completedHurwitzZetaEven₀ (ZMod.toAddCircle j) z‖ := by
                simpa using mul_le_mul_of_nonneg_right (χ.norm_le_one j) (norm_nonneg _)
            _ ≤ Ce j := hCe j z hz1 hz2
  -- Odd-part sum is bounded by `CO`.
  have hSo : ‖(∑ j : ZMod N, χ j * completedHurwitzZetaOdd (ZMod.toAddCircle j) z)‖ ≤ CO := by
    dsimp [CO]
    calc
      ‖(∑ j : ZMod N, χ j * completedHurwitzZetaOdd (ZMod.toAddCircle j) z)‖
          ≤ ∑ j : ZMod N, ‖χ j * completedHurwitzZetaOdd (ZMod.toAddCircle j) z‖ := by
            exact norm_sum_le _ _
      _ ≤ ∑ j : ZMod N, Co j := by
          refine Finset.sum_le_sum ?_
          intro j _
          calc
            ‖χ j * completedHurwitzZetaOdd (ZMod.toAddCircle j) z‖
                ≤ ‖χ j‖ * ‖completedHurwitzZetaOdd (ZMod.toAddCircle j) z‖ := norm_mul_le _ _
            _ ≤ ‖completedHurwitzZetaOdd (ZMod.toAddCircle j) z‖ := by
                simpa using mul_le_mul_of_nonneg_right (χ.norm_le_one j) (norm_nonneg _)
            _ ≤ Co j := hCo j z hz1 hz2
  have hBz : ‖(N : ℂ) ^ (-z)‖ ≤ B := by
    dsimp [B]
    exact norm_cpow_N_le hz1 hz2
  calc
    ‖ZMod.completedLFunction₀ χ z‖
        ≤ ‖(N : ℂ) ^ (-z) * (∑ j : ZMod N, χ j * completedHurwitzZetaEven₀ (ZMod.toAddCircle j) z)‖
          + ‖(N : ℂ) ^ (-z) * (∑ j : ZMod N, χ j * completedHurwitzZetaOdd (ZMod.toAddCircle j) z)‖ := by
          rw [ZMod.completedLFunction₀]
          exact norm_add_le _ _
    _ ≤ ‖(N : ℂ) ^ (-z)‖ * ‖(∑ j : ZMod N, χ j * completedHurwitzZetaEven₀ (ZMod.toAddCircle j) z)‖
        + ‖(N : ℂ) ^ (-z)‖ * ‖(∑ j : ZMod N, χ j * completedHurwitzZetaOdd (ZMod.toAddCircle j) z)‖ := by
          exact add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ ≤ B * CE + B * CO := by
          gcongr
    _ = B * (CE + CO) := by ring

/--
Strip-bound instance for a *primitive* character in the range needed by the approximate
functional equation (`AfeVerticalLine.Λ_growth`): for `0 < σ < 1` (here `σ = s.re`) the
completed L-function is bounded on the strip `σ-1 ≤ Re z ≤ σ+1`.
-/
theorem completedLFunction_vertical_bound_strip (χ : DirichletCharacter ℂ N)
    (hχprim : χ.IsPrimitive) (hχ : χ ≠ 1) {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ z : ℂ, σ - 1 ≤ z.re → z.re ≤ σ + 1 → ‖χ.completedLFunction z‖ ≤ C := by
  exact completedLFunction_strip_bound χ hχ (c := σ - 1) (d := σ + 1)

end
end PL.CompletedStrip


/-!
# The pole-subtraction `ψ(u) = (φ u - φ 0)/u` (T2, `rectBoundary_K`)

For a differentiable `φ : ℂ → ℂ` define the meromorphic-part subtraction

`ψ(u) = if u = 0 then deriv φ 0 else (φ u - φ 0) / u`.

Machine-verified here:
* `psi_of_ne_zero` — `ψ u = (φ u - φ 0)/u` for `u ≠ 0`,
* `psi_eq_slope` — `ψ u = u⁻¹ • (φ u - φ 0)` for `u ≠ 0`,
* `continuousAt_psi_zero` — continuity at `0` (via `DerivSlope.hasDerivAt_tendsto_slope`
  and `ExtendPunctured.continuousAt_extend_punctured`),
* `continuous_psi` — continuity everywhere (differentiability off `0` gives continuity
  at the other points),
* `differentiableAt_psi_of_ne_zero` — complex differentiability at every `u ≠ 0`.
-/

open Filter
open scoped Topology

set_option autoImplicit false

namespace PL.AfeRect

open Complex

/-- The pole subtraction `ψ` associated to `φ`: `(φ u - φ 0)/u`, extended at `0` by the
derivative `deriv φ 0`. -/
noncomputable def psi (φ : ℂ → ℂ) : ℂ → ℂ :=
  fun u => if u = 0 then deriv φ 0 else (φ u - φ 0) / u

/-- `ψ u = (φ u - φ 0)/u` for `u ≠ 0`. -/
lemma psi_of_ne_zero (φ : ℂ → ℂ) {u : ℂ} (hu : u ≠ 0) : psi φ u = (φ u - φ 0) / u := by
  simp [psi, hu]

/-- `ψ u = u⁻¹ • (φ u - φ 0)` for `u ≠ 0` (slope form). -/
lemma psi_eq_slope (φ : ℂ → ℂ) {u : ℂ} (hu : u ≠ 0) : psi φ u = u⁻¹ • (φ u - φ 0) := by
  rw [psi_of_ne_zero φ hu]
  rw [div_eq_mul_inv]
  rw [mul_comm]
  rw [smul_eq_mul]

/-- Continuity of `ψ` at `0` (the extension across the removable singularity). -/
lemma continuousAt_psi_zero (φ : ℂ → ℂ) (hφ : HasDerivAt φ (deriv φ 0) 0) :
    ContinuousAt (psi φ) 0 := by
  have hslope := DerivSlope.hasDerivAt_tendsto_slope φ hφ
  -- hslope : Tendsto (fun u => u⁻¹ • (φ u - φ 0)) (𝓝[≠] 0) (𝓝 (deriv φ 0))
  have hcont := ExtendPunctured.continuousAt_extend_punctured
    (g := fun u : ℂ => u⁻¹ • (φ u - φ 0)) (a := 0) (c := deriv φ 0) hslope
  -- hcont : ContinuousAt (fun u => if u = 0 then deriv φ 0 else u⁻¹ • (φ u - φ 0)) 0
  -- ψ agrees with this function pointwise
  have heq : psi φ = fun u : ℂ => if u = 0 then deriv φ 0 else u⁻¹ • (φ u - φ 0) := by
    funext u
    by_cases hu : u = 0
    · subst u
      simp [psi]
    · rw [if_neg hu]
      rw [psi_of_ne_zero φ hu]
      rw [div_eq_mul_inv]
      rw [smul_eq_mul]
      rw [mul_comm]
  simpa [heq] using hcont

/-- `ψ` is complex-differentiable at every `u ≠ 0`. -/
lemma differentiableAt_psi_of_ne_zero (φ : ℂ → ℂ) (hφ : Differentiable ℂ φ)
    {u : ℂ} (hu : u ≠ 0) : DifferentiableAt ℂ (psi φ) u := by
  have hφu : DifferentiableAt ℂ φ u := Differentiable.differentiableAt (x := u) hφ
  have hφu' : HasDerivAt φ (deriv φ u) u := hφu.hasDerivAt
  have hnum : HasDerivAt (fun w : ℂ => φ w - φ 0) (deriv φ u - 0) u :=
    hφu'.sub (hasDerivAt_const u (φ 0))
  have hden : HasDerivAt (fun w : ℂ => w) 1 u := hasDerivAt_id u
  have hdiv : DifferentiableAt ℂ (fun w : ℂ => (φ w - φ 0) / w) u :=
    (hnum.div hden hu).differentiableAt
  -- ψ agrees with this function in a punctured neighbourhood of u (u ≠ 0)
  refine hdiv.congr_of_eventuallyEq ?_
  filter_upwards [show {w : ℂ | w ≠ 0} ∈ 𝓝 u from
    isOpen_compl_singleton.mem_nhds (by simpa using hu)] with w hw
  rw [psi_of_ne_zero φ hw]

/-- `ψ` is continuous everywhere. -/
lemma continuous_psi (φ : ℂ → ℂ) (hφ : Differentiable ℂ φ) : Continuous (psi φ) := by
  rw [continuous_iff_continuousAt]
  intro u
  by_cases hu : u = 0
  · subst u
    have hφ0 : HasDerivAt φ (deriv φ 0) 0 :=
      (Differentiable.differentiableAt (x := 0) hφ).hasDerivAt
    exact continuousAt_psi_zero φ hφ0
  · exact (differentiableAt_psi_of_ne_zero φ hφ hu).continuousAt

end PL.AfeRect


/-! Prove: `∫ x in -1..1, 1/(x²+c²) = 2·arctan(1/c)/c` for `0 < c`.

Suggested route: by the substitution `x = c·t` (change variable `x ↦ x/c`, i.e. use
`intervalIntegral.integral_comp_mul_right` or `integral_comp_mul_left` with scale `1/c`
or `c`), reduce to `(1/c)·∫ t in -1/c..1/c, 1/(1+t²)`.  Then use the Mathlib lemma
`integral_one_div_one_add_sq {a b} : ∫ x in a..b, 1/(1+x²) = Real.arctan b - Real.arctan a`
together with `Real.arctan_neg` (arctan(-x) = -arctan x) to evaluate at `±1/c`.
Alternatively prove `∫ x in a..b, 1/(x²+c²) = (1/c)(arctan(b/c) - arctan(a/c))` by
`intervalIntegral.integral_eq_sub_of_hasDerivAt` with the primitive `fun x => (1/c) * Real.arctan (x/c)`, whose derivative is `1/(x²+c²)` by `Real.hasDerivAt_arctan` composed with `x ↦ x/c`, then instantiate `a = -1, b = 1`.
Note the interval integral needs no integrability side conditions to be *equal* once you
have the derivative-based formula (intervalIntegral handles it). -/

open MeasureTheory
open scoped Real 

set_option autoImplicit false

namespace PL.AfeRect

/-- `∫ x in -1..1, 1/(x²+c²) = 2·arctan(1/c)/c` for `0 < c`. -/
lemma integral_sq_add_inv (c : ℝ) (hc : 0 < c) :
    (∫ x : ℝ in (-1 : ℝ)..1, 1 / (x ^ 2 + c ^ 2)) = 2 * Real.arctan (1 / c) / c := by
  have hc' : c ≠ 0 := ne_of_gt hc
  calc
    (∫ x : ℝ in (-1 : ℝ)..1, 1 / (x ^ 2 + c ^ 2))
        = ∫ x : ℝ in (-1 : ℝ)..1, (c ^ 2 + x ^ 2)⁻¹ := by
            apply intervalIntegral.integral_congr
            intro x hx
            change 1 / (x ^ 2 + c ^ 2) = (c ^ 2 + x ^ 2)⁻¹
            rw [one_div]
            congr 1
            ring
    _ = c⁻¹ * (Real.arctan (1 / c) - Real.arctan ((-1 : ℝ) / c)) := by
            simpa using (integral_inv_sq_add_sq (a := (-1 : ℝ)) (b := 1) hc')
    _ = 2 * Real.arctan (1 / c) / c := by
            rw [neg_div, Real.arctan_neg]
            ring

end PL.AfeRect


/-! Prove: `∫ x in -1..1, x/(x²+c²) = 0` for `0 < c` (the integrand is odd).

Let `f x := x/(x²+c²)`.  We show `f (-x) = -f x` (field_simp/ring on ℝ),
rewrite the integrand via `intervalIntegral.integral_comp_neg`
(`∫ x in -1..1, f (-x) = ∫ x in -1..1, f x`, since the interval `-1..1` is
symmetric), and conclude `∫ f = -∫ f`, hence `∫ f = 0` by `linarith`. -/

open MeasureTheory
open scoped Real 

set_option autoImplicit false

namespace PL.AfeRect

/-- `∫ x in -1..1, x/(x²+c²) = 0` for `0 < c` (odd integrand). -/
lemma integral_odd_sq_add_inv (c : ℝ) (hc : 0 < c) :
    (∫ x : ℝ in (-1 : ℝ)..1, x / (x ^ 2 + c ^ 2)) = 0 := by
  let f : ℝ → ℝ := fun x => x / (x ^ 2 + c ^ 2)
  -- The integrand is odd.
  have hodd : ∀ x : ℝ, f (-x) = -f x := by
    intro x
    have hD : x ^ 2 + c ^ 2 ≠ 0 := by positivity
    simp [f]
    field_simp [hD]
  -- Rewrite `∫ f (-x) = ∫ (-f x)` using pointwise oddness.
  have hcongr : (∫ x in (-1 : ℝ)..1, f (-x)) = ∫ x in (-1 : ℝ)..1, -f x := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards with x hx
    exact hodd x
  -- Change variables `x ↦ -x` (interval `-1..1` is symmetric) to get `∫ f = -∫ f`.
  have hA : (∫ x in (-1 : ℝ)..1, f x) = - (∫ x in (-1 : ℝ)..1, f x) := by
    calc
      (∫ x in (-1 : ℝ)..1, f x) = ∫ x in (-1 : ℝ)..1, f (-x) := by simp
      _ = ∫ x in (-1 : ℝ)..1, -f x := hcongr
      _ = - (∫ x in (-1 : ℝ)..1, f x) := intervalIntegral.integral_neg
  have hfin : (∫ x : ℝ in (-1 : ℝ)..1, f x) = 0 := by linarith
  change (∫ x : ℝ in (-1 : ℝ)..1, f x) = 0
  exact hfin

end PL.AfeRect


/-! Prove: `∫ y in -T..T, y/(1+y²) = 0` for any real `T` (the integrand is odd).

Same method as in `RectReal2`: use `intervalIntegral.integral_comp_neg` with the odd
integrand `y ↦ y/(1+y²)` and the symmetric interval `-T..T`. -/

open MeasureTheory
open scoped Real 

set_option autoImplicit false

namespace PL.AfeRect

/-- `∫ y in -T..T, y/(1+y²) = 0` (odd integrand). -/
lemma integral_odd_one_add_sq (T : ℝ) :
    (∫ y : ℝ in -T..T, y / (1 + y ^ 2)) = 0 := by
  let f : ℝ → ℝ := fun y => y / (1 + y ^ 2)
  have hf_neg : ∀ y, f (-y) = -f y := by
    intro y
    dsimp [f]
    rw [neg_sq]
    ring
  have hpoint : ∀ y, f y = -f (-y) := by
    intro y
    have h1 : -f (-y) = f y := by
      calc
        -f (-y) = -(-f y) := by rw [hf_neg y]
        _ = f y := by ring
    exact h1.symm
  have hJ : (∫ y : ℝ in -T..T, f (-y)) = (∫ y : ℝ in -T..T, f y) := by
    simp
  have hI : (∫ y : ℝ in -T..T, f y) = - (∫ y : ℝ in -T..T, f y) := by
    calc
      (∫ y in -T..T, f y) = ∫ y in -T..T, -f (-y) := by
        apply intervalIntegral.integral_congr_ae
        exact ae_of_all _ (fun y _ => hpoint y)
      _ = -(∫ y in -T..T, f (-y)) := by simp
      _ = -(∫ y in -T..T, f y) := by rw [hJ]
  have hx0 : (∫ y : ℝ in -T..T, f y) = 0 := by
    linarith
  simpa [f] using hx0

end PL.AfeRect


/-! Prove the classical identity `Real.arctan T + Real.arctan (1/T) = π/2` for `0 < T`.

Suggested route: with `a := Real.arctan T`, `b := Real.arctan (1/T)` (both in `(0, π/2)`
by `Real.arctan_pos`, `Real.arctan_lt_pi_div_two`), show `Real.cos (a + b) = 0` using the
cosine addition formula (`Real.cos_add`), `Real.cos_arctan`, `Real.sin_arctan`
(cos(arctan x) = 1/√(1+x²), sin(arctan x) = x/√(1+x²)) — the combination yields
`(1 - T·(1/T)) / (√(1+T²)·√(1+1/T²)) = 0`.  Also note `0 < a + b` and `a + b < π`
(from the range facts; π/2 + π/2 = π and each < π/2, sum < π), then conclude from
`Real.cos_eq_zero_iff` that `a + b = π/2` (the only solution in `(0, π)` of `cos = 0`).
Alternative: use `Real.arctan_add`-style tangent formula or `Real.tan_pi_div_two_sub` with
`Real.tan_arctan`, `Real.arctan_inj` — whichever route compiles most easily. -/

open scoped Real

set_option autoImplicit false

namespace PL.AfeRect

/-- `arctan T + arctan(1/T) = π/2` for `0 < T`. -/
lemma arctan_inv_add (T : ℝ) (hT : 0 < T) :
    Real.arctan T + Real.arctan (1 / T) = π / 2 := by
  rw [one_div]
  rw [Real.arctan_inv_of_pos hT]
  ring

end PL.AfeRect


/-!
# The finite-rectangle residue relation (T2, second step)

Boundary integral around the rectangle with corners `⟨-1,-T⟩`, `⟨1,T⟩` (`0 < T`):

`B_T(f) = ∫_{x=-1}^{1} f(x-iT) dx - ∫_{x=-1}^{1} f(x+iT) dx
        + I·∫_{y=-T}^{T} f(1+iy) dy - I·∫_{y=-T}^{T} f(-1+iy) dy`

matching Mathlib's rectangle-boundary integral in the Cauchy-Goursat theorems of
`Mathlib/Analysis/Complex/CauchyIntegral.lean`.

Machine-verified here: `rectBoundary` (def), `rectBoundary_eq_zero_of_differentiableOn`
(Cauchy-Goursat), the four edges of `u ↦ u⁻¹` (`bottom_edge`, `top_edge`, `right_edge`,
`left_edge`, built on the real integrals of `Submission/RectReal*.lean`), the model
computation **`rectBoundary_inv : B_T(1/u) = 2πi`**, and `rectBoundary_inv_corners`.
-/

open MeasureTheory
open scoped Real 
set_option autoImplicit false

namespace PL.AfeRect

open Complex

noncomputable section

/-- The boundary integral of `f` over the rectangle with opposite corners `z w`
(positively oriented; matches the left-hand side of Mathlib's Cauchy-Goursat rectangle
theorems). -/
noncomputable def rectBoundary (z w : ℂ) (f : ℂ → ℂ) : ℂ :=
  (∫ x : ℝ in z.re..w.re, f (x + z.im * I))
    - (∫ x : ℝ in z.re..w.re, f (x + w.im * I))
    + I • (∫ y : ℝ in z.im..w.im, f (re w + y * I))
    - I • (∫ y : ℝ in z.im..w.im, f (re z + y * I))

/-- **Cauchy-Goursat for a rectangle**: if `f` is holomorphic on the closed rectangle then
the boundary integral vanishes. -/
lemma rectBoundary_eq_zero_of_differentiableOn (f : ℂ → ℂ) (z w : ℂ)
    (H : DifferentiableOn ℂ f (Set.uIcc z.re w.re ×ℂ Set.uIcc z.im w.im)) :
    rectBoundary z w f = 0 := by
  unfold rectBoundary
  exact integral_boundary_rect_eq_zero_of_differentiableOn f z w H

/-- `x² + T² ≠ 0` for `0 < T`. -/
lemma D_ne_zero (x T : ℝ) (hT : 0 < T) : x ^ 2 + T ^ 2 ≠ 0 := by
  nlinarith [sq_nonneg x, sq_nonneg T]

lemma bottom_edge_pointwise (T : ℝ) (hT : 0 < T) (x : ℝ) :
    ((x : ℂ) - I * (T : ℂ))⁻¹ = ((x : ℂ) + I * (T : ℂ)) * (((x ^ 2 + T ^ 2 : ℝ) : ℂ)⁻¹) := by
  rw [Complex.inv_def]
  have hconj : starRingEnd ℂ ((x : ℂ) - I * (T : ℂ)) = (x : ℂ) + I * (T : ℂ) := by
    simp
  have hns : Complex.normSq ((x : ℂ) - I * (T : ℂ)) = x ^ 2 + T ^ 2 := by
    rw [Complex.normSq_apply]
    simp
    ring
  rw [hconj, hns]
  rw [← Complex.ofReal_inv]

lemma integrable_bottom1 (T : ℝ) (hT : 0 < T) :
    IntervalIntegrable (fun x : ℝ => (x : ℂ) * (((x ^ 2 + T ^ 2 : ℝ) : ℂ)⁻¹)) volume (-1) 1 := by
  have hc1 : Continuous (fun x : ℝ => (x : ℂ)) := Complex.continuous_ofReal
  have hD : Continuous (fun x : ℝ => ((x ^ 2 + T ^ 2 : ℝ) : ℂ)) := by fun_prop
  have hDnz : ∀ x : ℝ, ((x ^ 2 + T ^ 2 : ℝ) : ℂ) ≠ 0 := by
    intro x
    exact ofReal_ne_zero.mpr (D_ne_zero x T hT)
  exact (hc1.mul (hD.inv₀ hDnz)).intervalIntegrable _ _

lemma integrable_bottom2 (T : ℝ) (hT : 0 < T) :
    IntervalIntegrable (fun x : ℝ => (I * (T : ℂ)) * (((x ^ 2 + T ^ 2 : ℝ) : ℂ)⁻¹)) volume (-1) 1 := by
  have hc1 : Continuous (fun x : ℝ => I * (T : ℂ)) := continuous_const
  have hD : Continuous (fun x : ℝ => ((x ^ 2 + T ^ 2 : ℝ) : ℂ)) := by fun_prop
  have hDnz : ∀ x : ℝ, ((x ^ 2 + T ^ 2 : ℝ) : ℂ) ≠ 0 := by
    intro x
    exact ofReal_ne_zero.mpr (D_ne_zero x T hT)
  exact (hc1.mul (hD.inv₀ hDnz)).intervalIntegrable _ _

lemma odd_part_zero (T : ℝ) (hT : 0 < T) :
    (∫ x : ℝ in (-1 : ℝ)..1, (x : ℂ) * (((x ^ 2 + T ^ 2 : ℝ) : ℂ)⁻¹)) = 0 := by
  have h3p : ∀ x : ℝ, (x : ℂ) * (((x ^ 2 + T ^ 2 : ℝ) : ℂ)⁻¹) = (((x * ((x ^ 2 + T ^ 2 : ℝ)⁻¹) : ℝ) : ℂ)) := by
    intro x
    rw [← Complex.ofReal_inv]
    rw [Complex.ofReal_mul]
  calc
    (∫ x : ℝ in (-1 : ℝ)..1, (x : ℂ) * (((x ^ 2 + T ^ 2 : ℝ) : ℂ)⁻¹))
        = ∫ x : ℝ in (-1 : ℝ)..1, (((x * ((x ^ 2 + T ^ 2 : ℝ)⁻¹) : ℝ) : ℂ)) := by
          apply intervalIntegral.integral_congr
          intro x hx
          exact h3p x
    _ = (((∫ x : ℝ in (-1 : ℝ)..1, x * ((x ^ 2 + T ^ 2 : ℝ)⁻¹)) : ℝ) : ℂ) := by
          rw [intervalIntegral.integral_ofReal]
    _ = 0 := by
          have heq : (fun x : ℝ => x * ((x ^ 2 + T ^ 2 : ℝ)⁻¹)) = fun x : ℝ => x / (x ^ 2 + T ^ 2) := by
            funext x
            have hD : x ^ 2 + T ^ 2 ≠ 0 := D_ne_zero x T hT
            field_simp [hD]
          rw [heq, integral_odd_sq_add_inv T hT]
          norm_num

lemma const_part (T : ℝ) (hT : 0 < T) :
    (∫ x : ℝ in (-1 : ℝ)..1, (I * (T : ℂ)) * (((x ^ 2 + T ^ 2 : ℝ) : ℂ)⁻¹))
      = I • ((2 * Real.arctan (1 / T) : ℝ) : ℂ) := by
  have h4p : ∀ x : ℝ, (I * (T : ℂ)) * (((x ^ 2 + T ^ 2 : ℝ) : ℂ)⁻¹)
      = I • (((T * ((x ^ 2 + T ^ 2 : ℝ)⁻¹) : ℝ) : ℂ)) := by
    intro x
    rw [smul_eq_mul]
    rw [← Complex.ofReal_inv]
    rw [Complex.ofReal_mul]
    ring
  calc
    (∫ x : ℝ in (-1 : ℝ)..1, (I * (T : ℂ)) * (((x ^ 2 + T ^ 2 : ℝ) : ℂ)⁻¹))
        = ∫ x : ℝ in (-1 : ℝ)..1, I • (((T * ((x ^ 2 + T ^ 2 : ℝ)⁻¹) : ℝ) : ℂ)) := by
          apply intervalIntegral.integral_congr
          intro x hx
          exact h4p x
    _ = I • (∫ x : ℝ in (-1 : ℝ)..1, (((T * ((x ^ 2 + T ^ 2 : ℝ)⁻¹) : ℝ) : ℂ))) := by
          rw [intervalIntegral.integral_smul]
    _ = I • (((∫ x : ℝ in (-1 : ℝ)..1, T * ((x ^ 2 + T ^ 2 : ℝ)⁻¹)) : ℝ) : ℂ) := by
          congr 1
          rw [intervalIntegral.integral_ofReal]
    _ = I • (((T * (∫ x : ℝ in (-1 : ℝ)..1, ((x ^ 2 + T ^ 2 : ℝ)⁻¹))) : ℝ) : ℂ) := by
          congr 2
          rw [← intervalIntegral.integral_const_mul]
    _ = I • ((2 * Real.arctan (1 / T) : ℝ) : ℂ) := by
          congr 1
          have hval : (∫ x : ℝ in (-1 : ℝ)..1, ((x ^ 2 + T ^ 2 : ℝ)⁻¹)) = 2 * Real.arctan (1 / T) / T := by
            have heq : (fun x : ℝ => (x ^ 2 + T ^ 2 : ℝ)⁻¹) = fun x : ℝ => 1 / (x ^ 2 + T ^ 2) := by
              funext x
              rw [one_div]
            rw [heq]
            exact integral_sq_add_inv T hT
          have hT0 : T ≠ 0 := ne_of_gt hT
          rw [hval]
          field_simp [hT0]

lemma bottom_edge (T : ℝ) (hT : 0 < T) :
    (∫ x : ℝ in (-1 : ℝ)..1, ((x : ℂ) - I * (T : ℂ))⁻¹)
      = I • ((2 * Real.arctan (1 / T) : ℝ) : ℂ) := by
  have h1 : (∫ x : ℝ in (-1 : ℝ)..1, ((x : ℂ) - I * (T : ℂ))⁻¹)
      = ∫ x : ℝ in (-1 : ℝ)..1, ((x : ℂ) + I * (T : ℂ)) * (((x ^ 2 + T ^ 2 : ℝ) : ℂ)⁻¹) := by
    apply intervalIntegral.integral_congr
    intro x hx
    exact bottom_edge_pointwise T hT x
  have h2 : (∫ x : ℝ in (-1 : ℝ)..1, ((x : ℂ) + I * (T : ℂ)) * (((x ^ 2 + T ^ 2 : ℝ) : ℂ)⁻¹))
      = (∫ x : ℝ in (-1 : ℝ)..1, (x : ℂ) * (((x ^ 2 + T ^ 2 : ℝ) : ℂ)⁻¹))
        + ∫ x : ℝ in (-1 : ℝ)..1, (I * (T : ℂ)) * (((x ^ 2 + T ^ 2 : ℝ) : ℂ)⁻¹) := by
    calc
      (∫ x : ℝ in (-1 : ℝ)..1, ((x : ℂ) + I * (T : ℂ)) * (((x ^ 2 + T ^ 2 : ℝ) : ℂ)⁻¹))
          = ∫ x : ℝ in (-1 : ℝ)..1, (x : ℂ) * (((x ^ 2 + T ^ 2 : ℝ) : ℂ)⁻¹) + (I * (T : ℂ)) * (((x ^ 2 + T ^ 2 : ℝ) : ℂ)⁻¹) := by
            apply intervalIntegral.integral_congr
            intro x hx
            ring
      _ = (∫ x : ℝ in (-1 : ℝ)..1, (x : ℂ) * (((x ^ 2 + T ^ 2 : ℝ) : ℂ)⁻¹))
            + ∫ x : ℝ in (-1 : ℝ)..1, (I * (T : ℂ)) * (((x ^ 2 + T ^ 2 : ℝ) : ℂ)⁻¹) := by
            rw [intervalIntegral.integral_add]
            · exact integrable_bottom1 T hT
            · exact integrable_bottom2 T hT
  calc
    (∫ x : ℝ in (-1 : ℝ)..1, ((x : ℂ) - I * (T : ℂ))⁻¹)
        = ∫ x : ℝ in (-1 : ℝ)..1, ((x : ℂ) + I * (T : ℂ)) * (((x ^ 2 + T ^ 2 : ℝ) : ℂ)⁻¹) := h1
    _ = I • ((2 * Real.arctan (1 / T) : ℝ) : ℂ) := by
          rw [h2, odd_part_zero T hT, const_part T hT]
          simp

lemma top_pointwise (T : ℝ) (x : ℝ) :
    ((x : ℂ) + I * (T : ℂ))⁻¹
      = (x : ℂ) * (((x ^ 2 + T ^ 2 : ℝ) : ℂ)⁻¹) - (I * (T : ℂ)) * (((x ^ 2 + T ^ 2 : ℝ) : ℂ)⁻¹) := by
  rw [Complex.inv_def]
  have hconj : starRingEnd ℂ ((x : ℂ) + I * (T : ℂ)) = (x : ℂ) - I * (T : ℂ) := by
    simp
    ring
  have hns : Complex.normSq ((x : ℂ) + I * (T : ℂ)) = x ^ 2 + T ^ 2 := by
    rw [Complex.normSq_apply]
    simp
    ring
  rw [hconj, hns]
  rw [← Complex.ofReal_inv]
  ring

lemma top_edge (T : ℝ) (hT : 0 < T) :
    (∫ x : ℝ in (-1 : ℝ)..1, ((x : ℂ) + I * (T : ℂ))⁻¹)
      = - I • ((2 * Real.arctan (1 / T) : ℝ) : ℂ) := by
  calc
    (∫ x : ℝ in (-1 : ℝ)..1, ((x : ℂ) + I * (T : ℂ))⁻¹)
        = ∫ x : ℝ in (-1 : ℝ)..1, (x : ℂ) * (((x ^ 2 + T ^ 2 : ℝ) : ℂ)⁻¹) - (I * (T : ℂ)) * (((x ^ 2 + T ^ 2 : ℝ) : ℂ)⁻¹) := by
          apply intervalIntegral.integral_congr
          intro x hx
          exact top_pointwise T x
    _ = (∫ x : ℝ in (-1 : ℝ)..1, (x : ℂ) * (((x ^ 2 + T ^ 2 : ℝ) : ℂ)⁻¹))
        - (∫ x : ℝ in (-1 : ℝ)..1, (I * (T : ℂ)) * (((x ^ 2 + T ^ 2 : ℝ) : ℂ)⁻¹)) := by
          rw [intervalIntegral.integral_sub]
          · exact integrable_bottom1 T hT
          · exact integrable_bottom2 T hT
    _ = - I • ((2 * Real.arctan (1 / T) : ℝ) : ℂ) := by
          rw [odd_part_zero T hT, const_part T hT]
          simp

/-- `∫ y in -T..T, 1/(1+y²) = 2·arctan T`. -/
lemma int_one_add_sq (T : ℝ) :
    (∫ y : ℝ in -T..T, 1 / (1 + y ^ 2)) = 2 * Real.arctan T := by
  have h := integral_one_div_one_add_sq (a := -T) (b := T)
  rw [h, Real.arctan_neg]
  ring

/-- continuity of `y ↦ ↑(1/(1+y²))`. -/
lemma cont_ofReal_one_add_sq : Continuous (fun y : ℝ => ((1 / (1 + y ^ 2) : ℝ) : ℂ)) := by
  have hc : Continuous (fun y : ℝ => (1 / (1 + y ^ 2) : ℝ)) := by
    refine Continuous.div continuous_const (by fun_prop) ?_
    intro y
    nlinarith [sq_nonneg y]
  exact Complex.continuous_ofReal.comp hc

/-- continuity of `y ↦ (I * (y:ℂ)) · ↑((1+y²)⁻¹)`. -/
lemma cont_Iy_one_add_sq : Continuous (fun y : ℝ => (I * (y : ℂ)) * (((1 + y ^ 2 : ℝ) : ℂ)⁻¹)) := by
  have hD : Continuous (fun y : ℝ => ((1 + y ^ 2 : ℝ) : ℂ)) := by fun_prop
  have hDnz : ∀ y : ℝ, ((1 + y ^ 2 : ℝ) : ℂ) ≠ 0 := by
    intro y
    exact ofReal_ne_zero.mpr (by nlinarith [sq_nonneg y])
  have hc1 : Continuous (fun y : ℝ => I * (y : ℂ)) := by
    exact (continuous_const.mul (Complex.continuous_ofReal.comp continuous_id))
  exact hc1.mul (hD.inv₀ hDnz)

lemma vert_odd_zero (T : ℝ) :
    (∫ y : ℝ in -T..T, (I * (y : ℂ)) * (((1 + y ^ 2 : ℝ) : ℂ)⁻¹)) = 0 := by
  have hpw : ∀ y : ℝ, (I * (y : ℂ)) * (((1 + y ^ 2 : ℝ) : ℂ)⁻¹)
      = I • (((y * ((1 + y ^ 2 : ℝ)⁻¹) : ℝ) : ℂ)) := by
    intro y
    rw [smul_eq_mul]
    rw [← Complex.ofReal_inv]
    rw [Complex.ofReal_mul]
    ring
  calc
    (∫ y : ℝ in -T..T, (I * (y : ℂ)) * (((1 + y ^ 2 : ℝ) : ℂ)⁻¹))
        = ∫ y : ℝ in -T..T, I • (((y * ((1 + y ^ 2 : ℝ)⁻¹) : ℝ) : ℂ)) := by
          apply intervalIntegral.integral_congr
          intro y hy
          exact hpw y
    _ = I • (∫ y : ℝ in -T..T, (((y * ((1 + y ^ 2 : ℝ)⁻¹) : ℝ) : ℂ))) := by
          rw [intervalIntegral.integral_smul]
    _ = I • (((∫ y : ℝ in -T..T, y * ((1 + y ^ 2 : ℝ)⁻¹)) : ℝ) : ℂ) := by
          congr 1
          rw [intervalIntegral.integral_ofReal]
    _ = 0 := by
          have heq : (fun y : ℝ => y * ((1 + y ^ 2 : ℝ)⁻¹)) = fun y : ℝ => y / (1 + y ^ 2) := by
            funext y
            have hD : 1 + y ^ 2 ≠ 0 := by nlinarith [sq_nonneg y]
            field_simp [hD]
          rw [heq, integral_odd_one_add_sq T]
          norm_num

lemma right_edge (T : ℝ) :
    (∫ y : ℝ in -T..T, ((1 : ℂ) + I * (y : ℂ))⁻¹)
      = ((2 * Real.arctan T : ℝ) : ℂ) := by
  have hpw : ∀ y : ℝ, ((1 : ℂ) + I * (y : ℂ))⁻¹
      = ((1 / (1 + y ^ 2) : ℝ) : ℂ) - (I * (y : ℂ)) * (((1 + y ^ 2 : ℝ) : ℂ)⁻¹) := by
    intro y
    rw [Complex.inv_def]
    have hconj : starRingEnd ℂ ((1 : ℂ) + I * (y : ℂ)) = (1 : ℂ) - I * (y : ℂ) := by
      simp
      ring
    have hns : Complex.normSq ((1 : ℂ) + I * (y : ℂ)) = 1 + y ^ 2 := by
      rw [Complex.normSq_apply]
      simp
      ring
    rw [hconj, hns]
    rw [← Complex.ofReal_inv]
    rw [one_div]
    ring
  have h1 : (∫ y : ℝ in -T..T, ((1 / (1 + y ^ 2) : ℝ) : ℂ))
      = ((2 * Real.arctan T : ℝ) : ℂ) := by
    calc
      (∫ y : ℝ in -T..T, ((1 / (1 + y ^ 2) : ℝ) : ℂ))
          = (((∫ y : ℝ in -T..T, 1 / (1 + y ^ 2)) : ℝ) : ℂ) := by
            rw [intervalIntegral.integral_ofReal]
      _ = ((2 * Real.arctan T : ℝ) : ℂ) := by congr 1; exact int_one_add_sq T
  calc
    (∫ y : ℝ in -T..T, ((1 : ℂ) + I * (y : ℂ))⁻¹)
        = ∫ y : ℝ in -T..T, ((1 / (1 + y ^ 2) : ℝ) : ℂ) - (I * (y : ℂ)) * (((1 + y ^ 2 : ℝ) : ℂ)⁻¹) := by
          apply intervalIntegral.integral_congr
          intro y hy
          exact hpw y
    _ = (∫ y : ℝ in -T..T, ((1 / (1 + y ^ 2) : ℝ) : ℂ))
        - (∫ y : ℝ in -T..T, (I * (y : ℂ)) * (((1 + y ^ 2 : ℝ) : ℂ)⁻¹)) := by
          rw [intervalIntegral.integral_sub]
          · exact cont_ofReal_one_add_sq.intervalIntegrable _ _
          · exact cont_Iy_one_add_sq.intervalIntegrable _ _
    _ = ((2 * Real.arctan T : ℝ) : ℂ) := by
          rw [h1, vert_odd_zero T]
          simp

lemma left_pointwise (T : ℝ) (y : ℝ) :
    ((-1 : ℂ) + I * (y : ℂ))⁻¹
      = -((1 / (1 + y ^ 2) : ℝ) : ℂ) - (I * (y : ℂ)) * (((1 + y ^ 2 : ℝ) : ℂ)⁻¹) := by
  rw [Complex.inv_def]
  have hconj : starRingEnd ℂ ((-1 : ℂ) + I * (y : ℂ)) = (-1 : ℂ) - I * (y : ℂ) := by
    simp
    ring
  have hns : Complex.normSq ((-1 : ℂ) + I * (y : ℂ)) = 1 + y ^ 2 := by
    rw [Complex.normSq_apply]
    simp
    ring
  rw [hconj, hns]
  rw [← Complex.ofReal_inv]
  rw [one_div]
  ring

lemma left_edge (T : ℝ) :
    (∫ y : ℝ in -T..T, ((-1 : ℂ) + I * (y : ℂ))⁻¹)
      = - ((2 * Real.arctan T : ℝ) : ℂ) := by
  have h1 : (∫ y : ℝ in -T..T, -((1 / (1 + y ^ 2) : ℝ) : ℂ))
      = - ((2 * Real.arctan T : ℝ) : ℂ) := by
    calc
      (∫ y : ℝ in -T..T, -((1 / (1 + y ^ 2) : ℝ) : ℂ))
          = - (∫ y : ℝ in -T..T, ((1 / (1 + y ^ 2) : ℝ) : ℂ)) := by
            rw [intervalIntegral.integral_neg]
      _ = - ((2 * Real.arctan T : ℝ) : ℂ) := by
            congr 1
            calc
              (∫ y : ℝ in -T..T, ((1 / (1 + y ^ 2) : ℝ) : ℂ))
                  = (((∫ y : ℝ in -T..T, 1 / (1 + y ^ 2)) : ℝ) : ℂ) := by
                    rw [intervalIntegral.integral_ofReal]
              _ = ((2 * Real.arctan T : ℝ) : ℂ) := by congr 1; exact int_one_add_sq T
  calc
    (∫ y : ℝ in -T..T, ((-1 : ℂ) + I * (y : ℂ))⁻¹)
        = ∫ y : ℝ in -T..T, -((1 / (1 + y ^ 2) : ℝ) : ℂ) - (I * (y : ℂ)) * (((1 + y ^ 2 : ℝ) : ℂ)⁻¹) := by
          apply intervalIntegral.integral_congr
          intro y hy
          exact left_pointwise T y
    _ = (∫ y : ℝ in -T..T, -((1 / (1 + y ^ 2) : ℝ) : ℂ))
        - (∫ y : ℝ in -T..T, (I * (y : ℂ)) * (((1 + y ^ 2 : ℝ) : ℂ)⁻¹)) := by
          rw [intervalIntegral.integral_sub]
          · exact cont_ofReal_one_add_sq.neg.intervalIntegrable _ _
          · exact cont_Iy_one_add_sq.intervalIntegrable _ _
    _ = - ((2 * Real.arctan T : ℝ) : ℂ) := by
          rw [h1, vert_odd_zero T]
          simp

lemma rectBoundary_inv (T : ℝ) (hT : 0 < T) :
    (∫ x : ℝ in (-1 : ℝ)..1, ((x : ℂ) - I * (T : ℂ))⁻¹)
      - (∫ x : ℝ in (-1 : ℝ)..1, ((x : ℂ) + I * (T : ℂ))⁻¹)
      + I • (∫ y : ℝ in -T..T, ((1 : ℂ) + I * (y : ℂ))⁻¹)
      - I • (∫ y : ℝ in -T..T, ((-1 : ℂ) + I * (y : ℂ))⁻¹)
    = 2 * π * I := by
  rw [bottom_edge T hT, top_edge T hT, right_edge T, left_edge T]
  have hs2 : Real.arctan T⁻¹ + Real.arctan T = π / 2 := by
    simpa [add_comm, one_div] using (arctan_inv_add T hT)
  simp [smul_eq_mul]
  ring_nf
  have hL' : I * ↑(Real.arctan T⁻¹) * 4 + I * ↑(Real.arctan T) * 4 = I * ↑π * 2 := by
    calc
      I * ↑(Real.arctan T⁻¹) * 4 + I * ↑(Real.arctan T) * 4
          = I * (↑(Real.arctan T⁻¹) + ↑(Real.arctan T)) * 4 := by ring
      _ = I * (↑(Real.arctan T⁻¹ + Real.arctan T)) * 4 := by rw [← Complex.ofReal_add]
      _ = I * ↑π * 2 := by
            rw [hs2]
            apply Complex.ext <;> simp <;> ring
  convert hL' using 1
  · rw [← Complex.ofReal_inv, ← Complex.ofReal_arctan, ← Complex.ofReal_arctan]


/-- The boundary integral of `u ↦ u⁻¹` over the rectangle with opposite corners
`⟨-1,-T⟩`, `⟨1,T⟩` equals `2πi` for `0 < T`. -/
lemma rectBoundary_inv_corners (T : ℝ) (hT : 0 < T) :
    rectBoundary ⟨-1, -T⟩ ⟨1, T⟩ (fun u : ℂ => u⁻¹) = 2 * π * I := by
  unfold rectBoundary
  have hb : (∫ x : ℝ in (-1 : ℝ)..1, (fun u : ℂ => u⁻¹) (x + (⟨-1, -T⟩ : ℂ).im * I))
      = ∫ x : ℝ in (-1 : ℝ)..1, ((x : ℂ) - I * (T : ℂ))⁻¹ := by
    apply intervalIntegral.integral_congr
    intro x hx
    change (((x : ℂ) + (⟨-1, -T⟩ : ℂ).im * I)⁻¹) = (((x : ℂ) - I * (T : ℂ))⁻¹)
    congr 1
    rw [show (⟨-1, -T⟩ : ℂ).im = -T by rfl]
    rw [Complex.ofReal_neg]
    ring
  have ht : (∫ x : ℝ in (-1 : ℝ)..1, (fun u : ℂ => u⁻¹) (x + (⟨1, T⟩ : ℂ).im * I))
      = ∫ x : ℝ in (-1 : ℝ)..1, ((x : ℂ) + I * (T : ℂ))⁻¹ := by
    apply intervalIntegral.integral_congr
    intro x hx
    change (((x : ℂ) + (⟨1, T⟩ : ℂ).im * I)⁻¹) = (((x : ℂ) + I * (T : ℂ))⁻¹)
    congr 1
    rw [show (⟨1, T⟩ : ℂ).im = T by rfl]
    ring
  have hr : (∫ y : ℝ in -T..T, (fun u : ℂ => u⁻¹) (re ⟨1, T⟩ + y * I))
      = ∫ y : ℝ in -T..T, ((1 : ℂ) + I * (y : ℂ))⁻¹ := by
    apply intervalIntegral.integral_congr
    intro y hy
    change (((re ⟨1, T⟩ : ℝ) + (y : ℝ) * I : ℂ)⁻¹) = (((1 : ℂ) + I * (y : ℂ))⁻¹)
    congr 1
    simp [Complex.ofReal_add]
    ring
  have hl : (∫ y : ℝ in -T..T, (fun u : ℂ => u⁻¹) (re ⟨-1, -T⟩ + y * I))
      = ∫ y : ℝ in -T..T, ((-1 : ℂ) + I * (y : ℂ))⁻¹ := by
    apply intervalIntegral.integral_congr
    intro y hy
    change (((re ⟨-1, -T⟩ : ℝ) + (y : ℝ) * I : ℂ)⁻¹) = (((-1 : ℂ) + I * (y : ℂ))⁻¹)
    congr 1
    simp [Complex.ofReal_add]
    ring
  rw [hb, ht, hr, hl]
  exact rectBoundary_inv T hT

end

end PL.AfeRect


/-!
# The finite-rectangle identity and the T → ∞ limit (PL.GRRect)

Proves the rotated-contour identity for Euler's Gamma integral at the measure level:

    gamma_eq_Jr_integral (s : ℂ) (hs : 0 < s.re) {θ : ℝ} (hθ : |θ| < Real.pi / 2) :
        Complex.Gamma s = cexp (-((I * (θ : ℂ)) * s)) * (∫ r in Ioi 0, Jr s θ r)

via Cauchy-Goursat on the rectangle with corners `(-T, 0)`, `(T, -θ)` for the integrand
`F s z = e^{-e^z}·e^{s·z}` (entire), rewriting the two horizontal edges with the substitutions
`r = e^x` (`integral_Hs`/`integral_Hr` from `PL.GRSubst`), letting the two vertical edges
vanish (`PL.GRVert.right_edge_tendsto` / `PL.GRVertL.left_edge_tendsto`), and
taking `T → ∞` with the two-sided interval-integral limit
`MeasureTheory.intervalIntegral_tendsto_integral`.
-/

open Complex Filter MeasureTheory Set
open scoped Real Topology 
set_option autoImplicit false

namespace PL.GRRect

open PL.GRBase
open PL.GRVert
open PL.GRSubst

noncomputable section

/-- `F s z = e^{-e^z}·e^{s·z}` (the pullback of the Γ integrand to the `z`-plane). -/
noncomputable def F (s : ℂ) (z : ℂ) : ℂ := cexp (-cexp z) * cexp (s * z)

/-- `F s` is entire. -/
lemma F_differentiable (s : ℂ) : Differentiable ℂ (F s) := by
  unfold F
  fun_prop

/-- The finite-rectangle boundary identity, expanded in the horizontal/vertical edge integrals.
The corners are `z = -T` (bottom-left) and `w = T - iθ` (top-right). -/
lemma rectBoundary_horizontal (s : ℂ) (θ : ℝ) (T : ℝ) :
    AfeRect.rectBoundary (-(T : ℂ)) ((T : ℂ) - (θ : ℂ) * I) (F s)
      = (∫ x in (-T)..T, Hs s x) - (∫ x in (-T)..T, Hr s θ x)
        + I • (∫ y in 0..(-θ), V s T y) - I • (∫ y in 0..(-θ), V s (-T) y) := by
  unfold AfeRect.rectBoundary
  simp only [Complex.ofReal_re, Complex.ofReal_im, Complex.neg_re, Complex.neg_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_I_re, Complex.mul_I_im, zero_sub, neg_zero, sub_zero]
  have h1 : (∫ x in (-T)..T, F s ((x : ℂ) + ((0 : ℝ) : ℂ) * I)) = ∫ x in (-T)..T, Hs s x := by
    apply intervalIntegral.integral_congr
    intro x hx
    have harg : (x : ℂ) + ((0 : ℝ) : ℂ) * I = (x : ℂ) := by norm_num
    simp only [F, Hs, harg]
  have h2 : (∫ x in (-T)..T, F s ((x : ℂ) + ((-θ : ℝ) : ℂ) * I)) = ∫ x in (-T)..T, Hr s θ x := by
    apply intervalIntegral.integral_congr
    intro x hx
    have harg : (x : ℂ) + ((-θ : ℝ) : ℂ) * I = (x : ℂ) - (θ : ℂ) * I := by
      rw [Complex.ofReal_neg]
      ring
    simp only [F, Hr, harg]
  have h3 : (∫ y in 0..(-θ), F s (((T : ℝ) : ℂ) + ((y : ℝ) : ℂ) * I)) = ∫ y in 0..(-θ), V s T y := by
    apply intervalIntegral.integral_congr
    intro y hy
    simp only [F, V]
  have h4 : (∫ y in 0..(-θ), F s ((((-T : ℝ)) : ℂ) + ((y : ℝ) : ℂ) * I)) = ∫ y in 0..(-θ), V s (-T) y := by
    apply intervalIntegral.integral_congr
    intro y hy
    simp only [F, V]
  rw [h1, h2, h3, h4]

/-- bottom edge of the Γ-contour rectangle tends to `Γ(s)` as `T → ∞`. -/
lemma tendsto_bottom (s : ℂ) (hs : 0 < s.re) :
    Tendsto (fun T : ℝ => ∫ x in (-T)..T, Hs s x) atTop (𝓝 (Complex.Gamma s)) := by
  have h : Tendsto (fun T : ℝ => ∫ x in (-T)..T, Hs s x) atTop
      (𝓝 (∫ x : ℝ, Hs s x)) := by
    exact MeasureTheory.intervalIntegral_tendsto_integral (integrable_Hs s hs)
      tendsto_neg_atTop_atBot tendsto_id
  simpa [integral_Hs s hs] using h

/-- top edge of the Γ-contour rectangle tends to `e^{-iθs}·∫ Jr` as `T → ∞`. -/
lemma tendsto_top (s : ℂ) (θ : ℝ) (hs : 0 < s.re) (hθ : |θ| < Real.pi / 2) :
    Tendsto (fun T : ℝ => ∫ x in (-T)..T, Hr s θ x) atTop
      (𝓝 (cexp (-((I * (θ : ℂ)) * s)) * (∫ r in Ioi 0, Jr s θ r))) := by
  have h : Tendsto (fun T : ℝ => ∫ x in (-T)..T, Hr s θ x) atTop
      (𝓝 (∫ x : ℝ, Hr s θ x)) := by
    exact MeasureTheory.intervalIntegral_tendsto_integral (integrable_Hr s θ hs hθ)
      tendsto_neg_atTop_atBot tendsto_id
  simpa [integral_Hr s θ hs hθ] using h

/-- **T1**: the rotated-contour identity `Γ(s) = e^{-iθs}·∫_{(0,∞)} e^{-r e^{-iθ}} r^{s-1} dr`. -/
theorem gamma_eq_Jr_integral (s : ℂ) (hs : 0 < s.re) {θ : ℝ} (hθ : |θ| < Real.pi / 2) :
    Complex.Gamma s = cexp (-((I * (θ : ℂ)) * s)) * (∫ r in Ioi 0, Jr s θ r) := by
  have hrect : ∀ T : ℝ, AfeRect.rectBoundary (-(T : ℂ)) ((T : ℂ) - (θ : ℂ) * I) (F s) = 0 := by
    intro T
    exact AfeRect.rectBoundary_eq_zero_of_differentiableOn (F s) (-(T : ℂ))
      ((T : ℂ) - (θ : ℂ) * I) (F_differentiable s).differentiableOn
  let E : ℝ → ℂ := fun T => ((∫ x in (-T)..T, Hs s x) - (∫ x in (-T)..T, Hr s θ x))
      + (I • (∫ y in 0..(-θ), V s T y) - I • (∫ y in 0..(-θ), V s (-T) y))
  have hE0 : ∀ T : ℝ, E T = 0 := by
    intro T
    have hz := hrect T
    rw [rectBoundary_horizontal s θ T] at hz
    dsimp [E]
    calc
      ((∫ x in (-T)..T, Hs s x) - (∫ x in (-T)..T, Hr s θ x))
          + (I • (∫ y in 0..(-θ), V s T y) - I • (∫ y in 0..(-θ), V s (-T) y))
          = ((∫ x in (-T)..T, Hs s x) - (∫ x in (-T)..T, Hr s θ x))
            + I • (∫ y in 0..(-θ), V s T y) - I • (∫ y in 0..(-θ), V s (-T) y) := by ring
      _ = 0 := hz
  have hEconst : Tendsto E atTop (𝓝 (0 : ℂ)) := by
    refine (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℂ)) atTop (𝓝 (0 : ℂ))).congr' ?_
    exact Filter.Eventually.of_forall (fun T => (hE0 T).symm)
  have hBv := tendsto_bottom s hs
  have hPv := tendsto_top s θ hs hθ
  have hRv : Tendsto (fun T : ℝ => ∫ y in 0..(-θ), V s T y) atTop (𝓝 0) :=
    right_edge_tendsto s hs hθ
  have hLv : Tendsto (fun T : ℝ => ∫ y in 0..(-θ), V s (-T) y) atTop (𝓝 0) :=
    GRVertL.left_edge_tendsto s hs hθ
  have htot : Tendsto E atTop
      (𝓝 (Complex.Gamma s - cexp (-((I * (θ : ℂ)) * s)) * (∫ r in Ioi 0, Jr s θ r))) := by
    have hsub : Tendsto (fun T : ℝ => (∫ x in (-T)..T, Hs s x) - (∫ x in (-T)..T, Hr s θ x)) atTop
        (𝓝 (Complex.Gamma s - cexp (-((I * (θ : ℂ)) * s)) * (∫ r in Ioi 0, Jr s θ r))) :=
      hBv.sub hPv
    have hR2 : Tendsto (fun T : ℝ => I • (∫ y in 0..(-θ), V s T y)) atTop (𝓝 (0 : ℂ)) := by
      simpa using hRv.const_smul I
    have hL2 : Tendsto (fun T : ℝ => I • (∫ y in 0..(-θ), V s (-T) y)) atTop (𝓝 (0 : ℂ)) := by
      simpa using hLv.const_smul I
    have hvert : Tendsto (fun T : ℝ =>
        I • (∫ y in 0..(-θ), V s T y) - I • (∫ y in 0..(-θ), V s (-T) y)) atTop (𝓝 (0 : ℂ)) := by
      simpa using hR2.sub hL2
    have htot' : Tendsto (fun T : ℝ => ((∫ x in (-T)..T, Hs s x) - (∫ x in (-T)..T, Hr s θ x))
        + (I • (∫ y in 0..(-θ), V s T y) - I • (∫ y in 0..(-θ), V s (-T) y))) atTop
        (𝓝 (Complex.Gamma s - cexp (-((I * (θ : ℂ)) * s)) * (∫ r in Ioi 0, Jr s θ r))) := by
      simpa using hsub.add hvert
    exact htot'.congr' (Filter.Eventually.of_forall (fun T => by rfl))
  have heq : (0 : ℂ) = Complex.Gamma s - cexp (-((I * (θ : ℂ)) * s)) * (∫ r in Ioi 0, Jr s θ r) :=
    tendsto_nhds_unique hEconst htot
  exact sub_eq_zero.mp heq.symm

/-- The norm form of the rotation identity (`rot_estimate`):
`|Γ(s)| ≤ Γ(Re s)·e^{θ·Im s}·(cos θ)^{-Re s}`. -/
theorem rot_estimate (s : ℂ) (hs : 0 < s.re) {θ : ℝ} (hθ : |θ| < Real.pi / 2) :
    ‖Complex.Gamma s‖ ≤ (Real.Gamma s.re) * Real.exp (θ * s.im) * (Real.cos θ) ^ (-s.re) := by
  have hcos : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo (abs_lt.mp hθ)
  have hmain := gamma_eq_Jr_integral s hs hθ
  have hnorm_exp : ‖cexp (-((I * (θ : ℂ)) * s))‖ = Real.exp (θ * s.im) := by
    rw [Complex.norm_exp]
    congr 1
    have h₂ : re ((I * (θ : ℂ)) * s) = -(θ * s.im) := by
      rw [show (I * (θ : ℂ)) * s = I * ((θ : ℂ) * s) by ring]
      rw [Complex.I_mul_re]
      congr 1
      simp
    rw [Complex.neg_re, h₂]
    ring
  have hJr : (∫ r in Ioi 0, ‖Jr s θ r‖) = ∫ r in Ioi 0, Real.exp (-(r * Real.cos θ)) * r ^ (s.re - 1) := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi ?_
    intro r hr
    exact norm_Jr s θ r hr
  have hval : (∫ r in Ioi 0, Real.exp (-(r * Real.cos θ)) * r ^ (s.re - 1))
      = (Real.cos θ) ^ (-s.re) * Real.Gamma s.re := by
    have hlib := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := s.re) (r := Real.cos θ) hs hcos
    -- hlib : ∫ t in Ioi 0, t ^ (s.re - 1) * exp (-(cos θ * t)) = (1 / cos θ) ^ s.re * Gamma s.re
    have hrew : (1 / Real.cos θ) ^ s.re = (Real.cos θ) ^ (-s.re) := by
      rw [one_div, Real.inv_rpow (le_of_lt hcos), (Real.rpow_neg (le_of_lt hcos) s.re).symm]
    calc
      (∫ r in Ioi 0, Real.exp (-(r * Real.cos θ)) * r ^ (s.re - 1))
          = ∫ r in Ioi 0, r ^ (s.re - 1) * Real.exp (-(Real.cos θ * r)) := by
            refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi ?_
            intro r hr
            congr 2
            ring
      _ = (1 / Real.cos θ) ^ s.re * Real.Gamma s.re := hlib
      _ = (Real.cos θ) ^ (-s.re) * Real.Gamma s.re := by rw [hrew]
  calc
    ‖Complex.Gamma s‖ = ‖cexp (-((I * (θ : ℂ)) * s)) * (∫ r in Ioi 0, Jr s θ r)‖ := by
      rw [hmain]
    _ = ‖cexp (-((I * (θ : ℂ)) * s))‖ * ‖(∫ r in Ioi 0, Jr s θ r)‖ := by rw [norm_mul]
    _ = Real.exp (θ * s.im) * ‖(∫ r in Ioi 0, Jr s θ r)‖ := by rw [hnorm_exp]
    _ ≤ Real.exp (θ * s.im) * (∫ r in Ioi 0, ‖Jr s θ r‖) := by
      apply mul_le_mul_of_nonneg_left _ (le_of_lt (Real.exp_pos _))
      exact MeasureTheory.norm_integral_le_integral_norm (fun r => Jr s θ r)
    _ = Real.exp (θ * s.im) * ((Real.cos θ) ^ (-s.re) * Real.Gamma s.re) := by
      rw [hJr, hval]
    _ = Real.exp (θ * s.im) * (Real.Gamma s.re) * (Real.cos θ) ^ (-s.re) := by ring
    _ = (Real.Gamma s.re) * Real.exp (θ * s.im) * (Real.cos θ) ^ (-s.re) := by ring


end
end PL.GRRect


/-!
# The rotated-contour identity for Euler's Gamma integral (PL.GammaRotate)

**Master statements (all proved here, no sorries):**

* `rotIntegrand s θ r` — the rotated integrand `e^{-r e^{-iθ}}·r^{s-1}` (`r > 0`);
* `integrable_rotIntegrand` (T2) — integrable over `r ∈ Ioi 0` for `0 < Re s`, `|θ| < π/2`;
* `gamma_eq_rotated` (T1) — the rotation identity `Γ(s) = e^{-iθs}·∫₀^∞ e^{-r e^{-iθ}} r^{s-1} dr`;
* `rot_estimate` — the norm estimate `|Γ(s)| ≤ Γ(Re s)·e^{θ·Im s}·(cos θ)^{-Re s}`;
* `F`, `F_differentiable`, `rayIntegrand` — auxiliary definitions kept from earlier versions.

The mathematical work lives in `Submission/GRRect.lean` (rectangle Cauchy + limit), which builds
on `Submission/GRSubst.lean` (substitution `r = e^x`, integrability) and `Submission/GRBase.lean`
(pointwise algebra).  This file only connects the statements.
-/

open Complex Filter MeasureTheory Set
open PL.GRBase
open PL.GRSubst
open scoped Real
set_option autoImplicit false

namespace PL.GammaRotate

noncomputable section

/-- The rotated Euler integrand `e^{-r·e^{-iθ}}·r^{s-1}` for `r > 0`. -/
noncomputable def rotIntegrand (s : ℂ) (θ : ℝ) (r : ℝ) : ℂ :=
  cexp (-((r : ℂ) * cexp (-(I * (θ : ℂ))))) * (r : ℂ) ^ (s - 1)

/-- **T2**: the rotated integrand is integrable over `r ∈ Ioi 0` for `0 < Re s`, `|θ| < π/2`. -/
theorem integrable_rotIntegrand (s : ℂ) (hs : 0 < s.re) {θ : ℝ} (hθ : |θ| < Real.pi / 2) :
    IntegrableOn (rotIntegrand s θ) (Ioi 0) := by
  change IntegrableOn (GRBase.Jr s θ) (Ioi 0)
  exact GRSubst.integrable_Jr s hs hθ

/-- **T1**: the contour-rotation identity for the Gamma integral:
`Γ(s) = e^{-iθs} · ∫₀^∞ e^{-r e^{-iθ}} r^{s-1} dr`  for `0 < Re s`, `|θ| < π/2`. -/
theorem gamma_eq_rotated (s : ℂ) (hs : 0 < s.re) {θ : ℝ} (hθ : |θ| < Real.pi / 2) :
    Complex.Gamma s =
      cexp (-(I * (θ : ℂ)) * s) * (∫ r : ℝ in Ioi 0, rotIntegrand s θ r) := by
  change Complex.Gamma s =
      cexp (-(I * (θ : ℂ)) * s) * (∫ r : ℝ in Ioi 0, GRBase.Jr s θ r)
  have hmain := GRRect.gamma_eq_Jr_integral s hs hθ
  -- hmain: Γ s = cexp (-((I * (θ : ℂ)) * s)) * ∫ Jr
  calc
    Complex.Gamma s = cexp (-((I * (θ : ℂ)) * s)) * (∫ r : ℝ in Ioi 0, GRBase.Jr s θ r) := hmain
    _ = cexp (-(I * (θ : ℂ)) * s) * (∫ r : ℝ in Ioi 0, GRBase.Jr s θ r) := by
      congr 2
      ring

/-- Norm form of the rotation identity:
`|Γ(s)| ≤ Γ(Re s) · e^{θ·Im s} · (cos θ)^{-Re s}`  for `0 < Re s`, `|θ| < π/2`. -/
theorem rot_estimate (s : ℂ) (hs : 0 < s.re) {θ : ℝ} (hθ : |θ| < Real.pi / 2) :
    ‖Complex.Gamma s‖ ≤ (Real.Gamma s.re) * Real.exp (θ * s.im) * (Real.cos θ) ^ (-s.re) := by
  exact GRRect.rot_estimate s hs hθ

/-- The pullback `w ↦ exp w` of the Gamma integrand to the `z`-plane:
`F s z = exp(-exp z)·exp(s·z)` (entire, so rectangle-Cauchy applies). -/
noncomputable def F (s : ℂ) (z : ℂ) : ℂ :=
  cexp (-cexp z) * cexp (s * z)

/-- `F s` is entire. -/
lemma F_differentiable (s : ℂ) : Differentiable ℂ (F s) := by
  unfold F
  fun_prop

/-- Real-axis Gamma integrand `e^{-r}·r^{s-1}`, `r > 0` (real variable; matches
`Complex.GammaIntegral`). -/
noncomputable def rayIntegrand (s : ℂ) (r : ℝ) : ℂ :=
  cexp (-(r : ℂ)) * (r : ℂ) ^ (s - 1)
end
end PL.GammaRotate



/-!
# Polynomial-with-exponential-decay bounds for `|Γ(σ + I·t)|` (the Stirling layer)

From the rotated-contour estimate `PL.GammaRotate.rot_estimate`
(`|Γ(s)| ≤ Γ(Re s)·e^{θ·Im s}·(cos θ)^{-Re s}` for every admissible rotation angle θ) one
chooses θ = ∓(π/2 − 1/(1+|t|)) (`Submission/AngleChoice.lean`) to obtain the classical
**upper bound with exponential decay**

`|Γ(σ + I·t)| ≤ C(σ)·(1+|t|)^σ·e^{-π|t|/2}`   (`gamma_norm_decay`, all `σ > 0`),

and by Euler's reflection formula `Γ(z)·Γ(1-z) = π/sin(πz)` (plus `|sin| ≤ e^{π|t|}` and
the upper bound at `1-σ`) the matching **lower bound**

`c(σ)·(1+|t|)^{σ-1}·e^{-π|t|/2} ≤ |Γ(σ + I·t)|`   (`gamma_norm_lower`, `0 < σ < 1`).

These are the Stirling-type bounds that upgrade every earlier exponential bound
(`GammaLower`, `GammaFactorLower`) to polynomial-in-`|t|` ones, unlocking the convexity
layer (polynomial growth of Dirichlet L-functions on the critical strip) and the
`|t|`-polynomial bounds for the AFE weight functions.
-/

open Complex Filter MeasureTheory Set
open scoped Real
set_option autoImplicit false

namespace PL.GammaDecay

/-- **Upper bound with decay**: for `σ > 0`, `|Γ(σ + I t)| ≤ C(σ)·(1+|t|)^σ·e^{-π|t|/2}`
for all real `t`. -/
theorem gamma_norm_decay (σ : ℝ) (hσ : 0 < σ) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ,
      ‖Complex.Gamma ((σ : ℂ) + I * (t : ℂ))‖ ≤
        C * (1 + |t|) ^ σ * Real.exp (-(Real.pi / 2) * |t|) := by
  rcases AngleChoice.angle_choice σ hσ with ⟨C₀, hC₀, hC₀body⟩
  refine ⟨Real.Gamma σ * C₀, mul_pos (Real.Gamma_pos_of_pos hσ) hC₀, ?_⟩
  intro t
  rcases hC₀body t with ⟨θ, hθabs, hθcos, hθb⟩
  let s : ℂ := (σ : ℂ) + I * (t : ℂ)
  have hs0 : 0 < s.re := by
    dsimp [s]; simp [hσ]
  have hest := GammaRotate.rot_estimate s hs0 hθabs
  have h₁ : ‖Complex.Gamma s‖ ≤
      (Real.Gamma σ) * (Real.exp (θ * t) * (Real.cos θ) ^ (-σ)) := by
    have hre : s.re = σ := by simp [s]
    have him : s.im = t := by simp [s]
    rw [hre, him] at hest
    rw [← mul_assoc]
    exact hest
  have h₂ : (Real.exp (θ * t) * (Real.cos θ) ^ (-σ)) ≤
      C₀ * (1 + |t|) ^ σ * Real.exp (-(Real.pi / 2) * |t|) := by
    simpa [mul_assoc] using hθb
  calc
    ‖Complex.Gamma s‖ ≤ (Real.Gamma σ) * (Real.exp (θ * t) * (Real.cos θ) ^ (-σ)) := h₁
    _ ≤ (Real.Gamma σ) * (C₀ * (1 + |t|) ^ σ * Real.exp (-(Real.pi / 2) * |t|)) := by
      exact mul_le_mul_of_nonneg_left h₂ (le_of_lt (Real.Gamma_pos_of_pos hσ))
    _ = (Real.Gamma σ * C₀) * (1 + |t|) ^ σ * Real.exp (-(Real.pi / 2) * |t|) := by
      ring

/-- **Lower bound with decay** (reflection): for `0 < σ < 1`,
`c(σ)·(1+|t|)^{σ-1}·e^{-π|t|/2} ≤ |Γ(σ + I t)|` for all real `t`. -/
theorem gamma_norm_lower (σ : ℝ) (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    ∃ c : ℝ, 0 < c ∧ ∀ t : ℝ,
      c * (1 + |t|) ^ (σ - 1) * Real.exp (-(Real.pi / 2) * |t|) ≤
        ‖Complex.Gamma ((σ : ℂ) + I * (t : ℂ))‖ := by
  rcases gamma_norm_decay (1 - σ) (by linarith) with ⟨C, hC, hCbody⟩
  refine ⟨Real.pi / C, div_pos Real.pi_pos hC, ?_⟩
  intro t
  let z : ℂ := (σ : ℂ) + I * (t : ℂ)
  change (Real.pi / C) * (1 + |t|) ^ (σ - 1) * Real.exp (-(Real.pi / 2) * |t|)
      ≤ ‖Complex.Gamma z‖
  have hzre : z.re = σ := by simp [z]
  have hrez : 0 < z.re := by rw [hzre]; exact hσ0
  have hgz : Complex.Gamma z ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hrez
  have h1zre : (1 - z).re = 1 - σ := by simp [z, hzre]
  have hre1z : 0 < (1 - z).re := by rw [h1zre]; linarith
  have hg1z : Complex.Gamma (1 - z) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hre1z
  have hsin_ne : Complex.sin ((Real.pi : ℂ) * z) ≠ 0 := by
    intro hs
    have h := Complex.Gamma_mul_Gamma_one_sub z
    rw [hs, div_zero] at h
    exact (mul_ne_zero hgz hg1z) h
  have hnorm : ‖Complex.Gamma z‖ * ‖Complex.Gamma (1 - z)‖ =
      Real.pi / ‖Complex.sin ((Real.pi : ℂ) * z)‖ := by
    have h := congrArg (fun w : ℂ => ‖w‖) (Complex.Gamma_mul_Gamma_one_sub z)
    rw [norm_mul, norm_div] at h
    rw [Complex.norm_real, Real.norm_eq_abs] at h
    rw [abs_of_nonneg (le_of_lt Real.pi_pos)] at h
    exact h
  set a : ℝ := ‖Complex.Gamma z‖ with ha
  set b : ℝ := ‖Complex.Gamma (1 - z)‖ with hb
  set c : ℝ := ‖Complex.sin ((Real.pi : ℂ) * z)‖ with hc
  set e : ℝ := Real.exp (Real.pi * |t|) with he
  have hgz_pos : 0 < a := by dsimp [a]; exact norm_pos_iff.mpr hgz
  have hg1z_pos : 0 < b := by dsimp [b]; exact norm_pos_iff.mpr hg1z
  have hsin_pos : 0 < c := by dsimp [c]; exact norm_pos_iff.mpr hsin_ne
  have he_pos : 0 < e := by dsimp [e]; exact Real.exp_pos _
  have hC_pos : 0 < C := hC
  have hprod : a * b * c = Real.pi := by
    rw [hnorm]
    rw [div_mul_cancel₀ _ (ne_of_gt hsin_pos)]
  have h1z_im : (1 - z).im = -t := by simp [z]
  have hg1z_ub : b ≤ C * (1 + |t|) ^ (1 - σ) * Real.exp (-(Real.pi / 2) * |t|) := by
    -- |Γ(1-σ-It)|: instantiate gamma_norm_decay at 1-σ with argument -t
    have hinst := hCbody (-t)
    have harg : Complex.Gamma (((1 - σ : ℝ) : ℂ) + I * ((-t : ℝ) : ℂ))
        = Complex.Gamma (1 - z) := by
      congr 1
      apply Complex.ext <;> simp [z] <;> ring
    calc
      b = ‖Complex.Gamma (1 - z)‖ := hb
      _ = ‖Complex.Gamma (((1 - σ : ℝ) : ℂ) + I * ((-t : ℝ) : ℂ))‖ := by rw [harg]
      _ ≤ C * (1 + |(-t)|) ^ (1 - σ) * Real.exp (-(Real.pi / 2) * |(-t)|) := hinst
      _ = C * (1 + |t|) ^ (1 - σ) * Real.exp (-(Real.pi / 2) * |t|) := by
        simp [abs_neg]
  have hsin_ub : c ≤ Real.exp (Real.pi * |t|) := by
    simpa [c, z] using (GammaLower.sin_bound_aux σ t)
  have hbce : 0 < b * c := mul_pos hg1z_pos hsin_pos
  have hbc_ne : b * c ≠ 0 := ne_of_gt hbce
  have hprod' : a = Real.pi / (b * c) := by
    have this := hprod
    rw [mul_assoc] at this
    exact (eq_div_iff hbc_ne).2 this
  let U : ℝ := C * (1 + |t|) ^ (1 - σ) * Real.exp ((Real.pi / 2) * |t|)
  have hU : 0 < U := by
    dsimp [U]
    positivity
  have hbcU : b * c ≤ U := by
    calc
      b * c ≤ (C * (1 + |t|) ^ (1 - σ) * Real.exp (-(Real.pi / 2) * |t|))
          * Real.exp (Real.pi * |t|) :=
        mul_le_mul hg1z_ub hsin_ub (norm_nonneg _) (by positivity)
      _ = U := by
        dsimp [U]
        rw [mul_assoc, ← Real.exp_add]
        rw [show (-(Real.pi / 2) * |t|) + Real.pi * |t| = (Real.pi / 2) * |t| by ring]
  let L : ℝ := (Real.pi / C) * (1 + |t|) ^ (σ - 1) * Real.exp (-(Real.pi / 2) * |t|)
  have hLU : L * U = Real.pi := by
    dsimp [L, U]
    rw [show ((Real.pi / C) * (1 + |t|) ^ (σ - 1) * Real.exp (-(Real.pi / 2) * |t|))
            * (C * (1 + |t|) ^ (1 - σ) * Real.exp ((Real.pi / 2) * |t|))
        = (Real.pi / C * C)
            * ((1 + |t|) ^ (σ - 1) * (1 + |t|) ^ (1 - σ))
            * (Real.exp (-(Real.pi / 2) * |t|) * Real.exp ((Real.pi / 2) * |t|)) by ring]
    rw [(show Real.pi / C * C = Real.pi by field_simp [hC])]
    rw [← Real.rpow_add (by positivity : 0 < 1 + |t|)]
    rw [← Real.exp_add]
    rw [show (σ - 1) + (1 - σ) = 0 by ring]
    rw [show (-(Real.pi / 2) * |t|) + (Real.pi / 2) * |t| = 0 by ring]
    simp
  have hL : L = Real.pi / U := (eq_div_iff (ne_of_gt hU)).2 hLU
  have h_ge : Real.pi / U ≤ Real.pi / (b * c) := by
    have hinv : U⁻¹ ≤ (b * c)⁻¹ := by
      exact (inv_le_inv₀ hU hbce).2 hbcU
    have hπ0 : 0 ≤ (Real.pi : ℝ) := le_of_lt Real.pi_pos
    simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_left hinv hπ0
  calc
    (Real.pi / C) * (1 + |t|) ^ (σ - 1) * Real.exp (-(Real.pi / 2) * |t|) = L := by rfl
    _ = Real.pi / U := hL
    _ ≤ Real.pi / (b * c) := h_ge
    _ = a := by rw [hprod']



/-- `‖(x : ℂ) ^ z‖ = x ^ z.re` for real `x > 0`. -/
lemma norm_cpow_ofReal_pos (x : ℝ) (hx : 0 < x) (z : ℂ) :
    ‖(x : ℂ) ^ z‖ = x ^ z.re := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]

end PL.GammaDecay


/-!
# A decaying lower bound for `|Γ(1 + iτ)|`

Prove:

`gamma_one_lower : ∃ c : ℝ, 0 < c ∧ ∀ τ : ℝ,
   c * Real.exp (-(Real.pi / 2) * |τ|) ≤ ‖Complex.Gamma ((1 : ℂ) + I * (τ : ℂ))‖`

This is the (crude) Stirling-type lower bound on the vertical line `Re = 1`, whose true
decay is `|Γ(1+iτ)| ~ √(2π|τ|) · exp(−π|τ|/2)`.  Everything needed is available in mathlib
(`Complex.Gamma_mul_Gamma_one_sub`, `Complex.Gamma_add_one`, `Complex.Gamma_conj`,
`Complex.sin_mul_I`, `Complex.ofReal_sinh`, `Real.sinh_eq`) plus the project files
`PL.GammaDecay.gamma_norm_decay (1 : ℝ) (by norm_num)` (an upper bound
`‖Gamma (1 + I u)‖ ≤ C·(1+|u|)·exp (−(π/2)|u|)`) and
`PL.GammaVertical.norm_Gamma_le_norm_Gamma_re` (`‖Gamma s‖ ≤ ‖Gamma s.re‖` for
`0 < s.re`, giving `|Γ(1−iτ)| ≤ |Γ(1)| = 1`).

## Proof sketch

Euler's reflection formula at `z = iτ` together with the functional equation
`Γ(1+z) = z·Γ(z)` give (after taking moduli)

`‖Γ(1+iτ)‖ · ‖Γ(1−iτ)‖ = π|τ| / sinh(π|τ|)`   (`gamma_one_lower_prod_norm`, valid for `τ ≠ 0`).

1. **Bounded regime `|τ| ≤ 1`**: `|Γ(1−iτ)| ≤ |Γ(1)| = 1`
   (`gamma_one_lower_norm_minus_one_le`, from the vertical bound), so
   `‖Γ(1+iτ)‖ ≥ π|τ|/sinh(π|τ|) ≥ exp(−π|τ|)` (using `sinh u ≤ u·e^u`, lemma
   `gamma_one_lower_pi_div_sinh_ge_exp`) `≥ exp(−π/2)·exp(−(π/2)|τ|)`.

2. **Decaying regime `1 ≤ |τ|`**: `|Γ(1−iτ)| ≤ C(1+|τ|)·exp(−(π/2)|τ|)`
   (`gamma_norm_decay (1 : ℝ)` at `−τ`), so
   `‖Γ(1+iτ)‖ ≥ P/H` with `P = π|τ|/sinh(π|τ|)`, `H = C(1+|τ|)·exp(−(π/2)|τ|)`;
   since `1/sinh(πy) ≥ 2e^{−πy}` (`gamma_one_lower_pi_div_sinh_ge_two_mul_exp`),
   `P/H ≥ (2π/C)·(|τ|/(1+|τ|))·exp(−(π/2)|τ|) ≥ (π/C)·exp(−(π/2)|τ|)`.

3. Combine with `c := min (exp(−π/2)) (π/C)` and split by `|τ| ≤ 1`; handle `τ = 0`
   separately (`‖Γ(1)‖ = 1`).
-/

open Complex Filter MeasureTheory Set
open scoped Real

set_option autoImplicit false

namespace PL.WeightPoly

/-- `sin x = sinh x * I` for real `x` (as complex numbers). -/
lemma gamma_one_lower_sin_ofReal_mul_I (x : ℝ) :
    Complex.sin ((x : ℂ) * I) = (Real.sinh x : ℂ) * I := by
  rw [Complex.sin_mul_I, ← Complex.ofReal_sinh]

/-- `sin (π·i·τ) = i·sinh(πτ)` for real `τ`. -/
lemma gamma_one_lower_sin_pi_I_mul (τ : ℝ) :
    Complex.sin ((Real.pi : ℂ) * (I * (τ : ℂ))) = (Real.sinh (Real.pi * τ) : ℂ) * I := by
  have harg : (Real.pi : ℂ) * (I * (τ : ℂ)) = ((Real.pi * τ : ℝ) : ℂ) * I := by
    rw [show (I * (τ : ℂ)) = (τ : ℂ) * I by ring]
    rw [← mul_assoc]
    rw [← Complex.ofReal_mul]
  rw [harg]
  exact gamma_one_lower_sin_ofReal_mul_I (Real.pi * τ)

/-- `‖sin (π·i·τ)‖ = sinh(π|τ|)` for real `τ`. -/
lemma gamma_one_lower_norm_sin_pi_I_mul (τ : ℝ) :
    ‖Complex.sin ((Real.pi : ℂ) * (I * (τ : ℂ)))‖ = Real.sinh (Real.pi * |τ|) := by
  rw [gamma_one_lower_sin_pi_I_mul τ]
  rw [norm_mul, norm_I, mul_one]
  rw [Complex.norm_real, Real.norm_eq_abs]
  rw [Real.abs_sinh]
  congr 1
  rw [abs_mul, abs_of_nonneg (le_of_lt Real.pi_pos)]

/-- Euler reflection + the functional equation on the line `Re = 1`:
`‖Γ(1+iτ)‖·‖Γ(1−iτ)‖ = π|τ|/sinh(π|τ|)` for `τ ≠ 0`. -/
lemma gamma_one_lower_prod_norm (τ : ℝ) (hτ : τ ≠ 0) :
    ‖Complex.Gamma ((1 : ℂ) + I * (τ : ℂ))‖ *
        ‖Complex.Gamma ((1 : ℂ) - I * (τ : ℂ))‖ =
      Real.pi * |τ| / Real.sinh (Real.pi * |τ|) := by
  let a : ℂ := I * (τ : ℂ)
  have ha : a ≠ 0 := by
    dsimp [a]
    intro h
    apply hτ
    have hzero : (τ : ℂ) = 0 := by
      have := congrArg Complex.im h
      simpa using this
    exact_mod_cast (Complex.ofReal_eq_zero.mp hzero)
  have hnorm_ref : ‖Complex.Gamma a‖ * ‖Complex.Gamma (1 - a)‖ =
      Real.pi / ‖Complex.sin ((Real.pi : ℂ) * a)‖ := by
    have h := congrArg (fun w : ℂ => ‖w‖) (Complex.Gamma_mul_Gamma_one_sub a)
    rw [norm_mul, norm_div] at h
    rw [Complex.norm_real, Real.norm_eq_abs] at h
    rw [abs_of_nonneg (le_of_lt Real.pi_pos)] at h
    exact h
  have hga : Complex.Gamma (a + 1) = a * Complex.Gamma a :=
    Complex.Gamma_add_one a ha
  have hga' : Complex.Gamma ((1 : ℂ) + a) = a * Complex.Gamma a := by
    simpa [add_comm] using hga
  have hn1 : ‖Complex.Gamma ((1 : ℂ) + a)‖ = ‖a‖ * ‖Complex.Gamma a‖ := by
    rw [hga', norm_mul]
  calc
    ‖Complex.Gamma ((1 : ℂ) + I * (τ : ℂ))‖ *
        ‖Complex.Gamma ((1 : ℂ) - I * (τ : ℂ))‖
        = ‖Complex.Gamma ((1 : ℂ) + a)‖ * ‖Complex.Gamma (1 - a)‖ := by rfl
    _ = (‖a‖ * ‖Complex.Gamma a‖) * ‖Complex.Gamma (1 - a)‖ := by rw [hn1]
    _ = ‖a‖ * (‖Complex.Gamma a‖ * ‖Complex.Gamma (1 - a)‖) := by ring
    _ = ‖a‖ * (Real.pi / ‖Complex.sin ((Real.pi : ℂ) * a)‖) := by rw [hnorm_ref]
    _ = |τ| * (Real.pi / ‖Complex.sin ((Real.pi : ℂ) * a)‖) := by
      dsimp [a]
      rw [norm_mul, norm_I, one_mul]
      rw [Complex.norm_real, Real.norm_eq_abs]
    _ = |τ| * (Real.pi / Real.sinh (Real.pi * |τ|)) := by
      congr 2
      dsimp [a]
      exact gamma_one_lower_norm_sin_pi_I_mul τ
    _ = Real.pi * |τ| / Real.sinh (Real.pi * |τ|) := by
      have hsinpos : 0 < Real.sinh (Real.pi * |τ|) := by
        rw [Real.sinh_pos_iff]
        exact mul_pos Real.pi_pos (abs_pos.mpr hτ)
      field_simp [ne_of_gt hsinpos]

/-- `‖Γ(1 − iτ)‖ ≤ 1` for all real `τ`. -/
lemma gamma_one_lower_norm_minus_one_le (τ : ℝ) :
    ‖Complex.Gamma ((1 : ℂ) - I * (τ : ℂ))‖ ≤ 1 := by
  let s : ℂ := (1 : ℂ) - I * (τ : ℂ)
  change ‖Complex.Gamma s‖ ≤ 1
  have hre : 0 < s.re := by
    dsimp [s]
    simp
  have h := PL.GammaVertical.norm_Gamma_le_norm_Gamma_re s hre
  have hsre : s.re = 1 := by
    dsimp [s]
    simp
  rw [hsre] at h
  simpa using h

/-- `sinh x ≤ x·e^x` for all real `x`. -/
lemma gamma_one_lower_sinh_mul_le_exp (x : ℝ) : Real.sinh x ≤ x * Real.exp x := by
  rw [Real.sinh_eq]
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).2
  have h12 : 1 - 2 * x ≤ Real.exp (-(2 * x)) := by
    have := Real.add_one_le_exp (-(2 * x))
    linarith
  calc
    Real.exp x - Real.exp (-x)
        = Real.exp x * (1 - Real.exp (-(2 * x))) := by
          rw [show Real.exp (-x) = Real.exp x * Real.exp (-(2 * x)) by
            rw [← Real.exp_add]
            congr 1
            ring]
          ring
    _ ≤ Real.exp x * (2 * x) := by
      refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos x).le
      linarith
    _ = (x * Real.exp x) * 2 := by ring

/-- `e^{−πy} ≤ πy / sinh(πy)` for `0 < y`. -/
lemma gamma_one_lower_pi_div_sinh_ge_exp (y : ℝ) (hy : 0 < y) :
    Real.exp (-(Real.pi * y)) ≤ (Real.pi * y) / Real.sinh (Real.pi * y) := by
  have hu0 : 0 < Real.pi * y := mul_pos Real.pi_pos hy
  have hsin0 : 0 < Real.sinh (Real.pi * y) := by
    simpa using (Real.sinh_pos_iff).2 hu0
  have hsin_le : Real.sinh (Real.pi * y) ≤ Real.pi * y * Real.exp (Real.pi * y) := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (gamma_one_lower_sinh_mul_le_exp (Real.pi * y))
  have hA : Real.exp (-(Real.pi * y)) * Real.sinh (Real.pi * y) ≤ Real.pi * y := by
    calc
      Real.exp (-(Real.pi * y)) * Real.sinh (Real.pi * y)
          ≤ Real.exp (-(Real.pi * y)) * (Real.pi * y * Real.exp (Real.pi * y)) :=
            mul_le_mul_of_nonneg_left hsin_le (Real.exp_pos (-(Real.pi * y))).le
      _ = Real.pi * y := by
        calc
          Real.exp (-(Real.pi * y)) * (Real.pi * y * Real.exp (Real.pi * y))
              = Real.pi * y * (Real.exp (-(Real.pi * y)) * Real.exp (Real.pi * y)) := by ring
          _ = Real.pi * y := by
            rw [← Real.exp_add]
            have hz : -(Real.pi * y) + Real.pi * y = 0 := by ring
            rw [hz, Real.exp_zero, mul_one]
  exact (le_div_iff₀ hsin0).2 hA

/-- `sinh x ≤ e^x / 2` for all real `x`. -/
lemma gamma_one_lower_sinh_le_half_exp (x : ℝ) : Real.sinh x ≤ Real.exp x / 2 := by
  rw [Real.sinh_eq]
  rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 2) (by norm_num : (0 : ℝ) < 2)]
  linarith [Real.exp_pos (-x)]

/-- `2πy·e^{−πy} ≤ πy / sinh(πy)` for `0 < y`. -/
lemma gamma_one_lower_pi_div_sinh_ge_two_mul_exp (y : ℝ) (hy : 0 < y) :
    2 * (Real.pi * y) * Real.exp (-(Real.pi * y)) ≤
      (Real.pi * y) / Real.sinh (Real.pi * y) := by
  have hu0 : 0 < Real.pi * y := mul_pos Real.pi_pos hy
  have hsin0 : 0 < Real.sinh (Real.pi * y) := by
    simpa using (Real.sinh_pos_iff).2 hu0
  have htwo : 2 * Real.sinh (Real.pi * y) ≤ Real.exp (Real.pi * y) := by
    nlinarith [gamma_one_lower_sinh_le_half_exp (Real.pi * y)]
  have hA : 2 * Real.exp (-(Real.pi * y)) * Real.sinh (Real.pi * y) ≤ 1 := by
    calc
      2 * Real.exp (-(Real.pi * y)) * Real.sinh (Real.pi * y)
          = Real.exp (-(Real.pi * y)) * (2 * Real.sinh (Real.pi * y)) := by ring
      _ ≤ Real.exp (-(Real.pi * y)) * Real.exp (Real.pi * y) :=
            mul_le_mul_of_nonneg_left htwo (Real.exp_pos (-(Real.pi * y))).le
      _ = 1 := by
        rw [← Real.exp_add]
        have hz : -(Real.pi * y) + Real.pi * y = 0 := by ring
        rw [hz, Real.exp_zero]
  have hB : (2 * (Real.pi * y) * Real.exp (-(Real.pi * y))) * Real.sinh (Real.pi * y) ≤ Real.pi * y := by
    calc
      (2 * (Real.pi * y) * Real.exp (-(Real.pi * y))) * Real.sinh (Real.pi * y)
          = (Real.pi * y) * (2 * Real.exp (-(Real.pi * y)) * Real.sinh (Real.pi * y)) := by ring
      _ ≤ (Real.pi * y) * 1 := by
        refine mul_le_mul_of_nonneg_left hA ?_
        positivity
      _ = Real.pi * y := by ring
  exact (le_div_iff₀ hsin0).2 hB

/-- `e^{−π/2}·e^{−(π/2)y} ≤ e^{−πy}` for `y ≤ 1`. -/
lemma gamma_one_lower_exp_half_compare (y : ℝ) (hy : y ≤ 1) :
    Real.exp (-(Real.pi / 2)) * Real.exp (-(Real.pi / 2) * y) ≤
      Real.exp (-(Real.pi * y)) := by
  rw [← Real.exp_add]
  exact (Real.exp_le_exp).2 (by
    nlinarith [Real.pi_pos])

/-- Region-two chain:
`(π/C)·e^{−(π/2)y} ≤ (2πy·e^{−πy}) / (C(1+y)·e^{−(π/2)y})` for `1 ≤ y`, `0 < C`. -/
lemma gamma_one_lower_region2_chain (C y : ℝ) (hC : 0 < C) (hy1 : 1 ≤ y) :
    (Real.pi / C) * Real.exp (-(Real.pi / 2) * y) ≤
      (2 * (Real.pi * y) * Real.exp (-(Real.pi * y))) /
        (C * (1 + y) * Real.exp (-(Real.pi / 2) * y)) := by
  have hden : 0 < C * (1 + y) * Real.exp (-(Real.pi / 2) * y) := by
    positivity
  rw [le_div_iff₀ hden]
  calc
    (Real.pi / C) * Real.exp (-(Real.pi / 2) * y) *
        (C * (1 + y) * Real.exp (-(Real.pi / 2) * y))
        = Real.pi * (1 + y) * Real.exp (-(Real.pi * y)) := by
          field_simp [ne_of_gt hC]
          rw [← Real.exp_nat_mul (-(Real.pi * y / 2)) 2]
          congr 1
          ring
    _ ≤ Real.pi * (2 * y) * Real.exp (-(Real.pi * y)) := by
      have hπ : 0 ≤ Real.pi := le_of_lt Real.pi_pos
      have he : 0 ≤ Real.exp (-(Real.pi * y)) := (Real.exp_pos _).le
      have hm : Real.pi * (1 + y) ≤ Real.pi * (2 * y) := by
        exact mul_le_mul_of_nonneg_left (by linarith) hπ
      exact mul_le_mul_of_nonneg_right hm he
    _ = 2 * (Real.pi * y) * Real.exp (-(Real.pi * y)) := by ring

/-- Lower bound for the complex Gamma function on the line `Re = 1`:
`c·exp (-(π/2)|τ|) ≤ ‖Gamma (1 + Iτ)‖` for all real `τ`. -/
lemma gamma_one_lower :
    ∃ c : ℝ, 0 < c ∧ ∀ τ : ℝ,
      c * Real.exp (-(Real.pi / 2) * |τ|) ≤ ‖Complex.Gamma ((1 : ℂ) + I * (τ : ℂ))‖ := by
  rcases PL.GammaDecay.gamma_norm_decay (1 : ℝ) (by norm_num) with ⟨C, hC, hCbody⟩
  let c : ℝ := min (Real.exp (-(Real.pi / 2))) (Real.pi / C)
  refine ⟨c, ?hcpos, ?hbody⟩
  · dsimp [c]
    exact lt_min (Real.exp_pos (-(Real.pi / 2))) (div_pos Real.pi_pos hC)
  · intro τ
    by_cases hτ0 : τ = 0
    · subst τ
      have hc1 : c ≤ 1 := by
        dsimp [c]
        calc
          min (Real.exp (-(Real.pi / 2))) (Real.pi / C) ≤ Real.exp (-(Real.pi / 2)) :=
            min_le_left _ _
          _ ≤ 1 := by
            rw [← Real.exp_zero]
            exact (Real.exp_le_exp).2 (by linarith [Real.pi_pos])
      calc
        c * Real.exp (-(Real.pi / 2) * |(0 : ℝ)|) = c := by simp
        _ ≤ ‖Complex.Gamma ((1 : ℂ) + I * (0 : ℂ))‖ := by
          simpa [Complex.Gamma_one] using hc1
    · have habs : 0 < |τ| := abs_pos.mpr hτ0
      have hprod : ‖Complex.Gamma ((1 : ℂ) + I * (τ : ℂ))‖ *
            ‖Complex.Gamma ((1 : ℂ) - I * (τ : ℂ))‖ =
          Real.pi * |τ| / Real.sinh (Real.pi * |τ|) :=
        gamma_one_lower_prod_norm τ hτ0
      by_cases hsmall : |τ| ≤ 1
      · calc
          c * Real.exp (-(Real.pi / 2) * |τ|)
              ≤ Real.exp (-(Real.pi / 2)) * Real.exp (-(Real.pi / 2) * |τ|) := by
                exact mul_le_mul_of_nonneg_right (by dsimp [c]; exact min_le_left _ _)
                  (Real.exp_pos (-(Real.pi / 2) * |τ|)).le
          _ ≤ Real.exp (-(Real.pi * |τ|)) := gamma_one_lower_exp_half_compare |τ| hsmall
          _ ≤ Real.pi * |τ| / Real.sinh (Real.pi * |τ|) :=
                gamma_one_lower_pi_div_sinh_ge_exp |τ| habs
          _ ≤ ‖Complex.Gamma ((1 : ℂ) + I * (τ : ℂ))‖ := by
                have hh1 : ‖Complex.Gamma ((1 : ℂ) - I * (τ : ℂ))‖ ≤ 1 :=
                  gamma_one_lower_norm_minus_one_le τ
                calc
                  Real.pi * |τ| / Real.sinh (Real.pi * |τ|)
                      = ‖Complex.Gamma ((1 : ℂ) + I * (τ : ℂ))‖ *
                          ‖Complex.Gamma ((1 : ℂ) - I * (τ : ℂ))‖ := hprod.symm
                  _ ≤ ‖Complex.Gamma ((1 : ℂ) + I * (τ : ℂ))‖ * 1 :=
                        mul_le_mul_of_nonneg_left hh1 (norm_nonneg _)
                  _ = ‖Complex.Gamma ((1 : ℂ) + I * (τ : ℂ))‖ := by simp
      · have hlarge : 1 ≤ |τ| := by
          have hlt : 1 < |τ| := lt_of_not_ge hsmall
          exact le_of_lt hlt
        have hdec : ‖Complex.Gamma ((1 : ℂ) - I * (τ : ℂ))‖ ≤
            C * (1 + |τ|) * Real.exp (-(Real.pi / 2) * |τ|) := by
          have hinst := hCbody (-τ)
          calc
            ‖Complex.Gamma ((1 : ℂ) - I * (τ : ℂ))‖
                = ‖Complex.Gamma (((1 : ℝ) : ℂ) + I * ((-τ : ℝ) : ℂ))‖ := by
                  congr 2
                  norm_num
                  ring
            _ ≤ C * (1 + |(-τ)|) ^ 1 * Real.exp (-(Real.pi / 2) * |(-τ)|) := hinst
            _ = C * (1 + |τ|) * Real.exp (-(Real.pi / 2) * |τ|) := by
              simp [abs_neg]
        have hH : 0 < C * (1 + |τ|) * Real.exp (-(Real.pi / 2) * |τ|) := by
          positivity
        have hP_le_gH : Real.pi * |τ| / Real.sinh (Real.pi * |τ|) ≤
            ‖Complex.Gamma ((1 : ℂ) + I * (τ : ℂ))‖ *
              (C * (1 + |τ|) * Real.exp (-(Real.pi / 2) * |τ|)) := by
          calc
            Real.pi * |τ| / Real.sinh (Real.pi * |τ|)
                = ‖Complex.Gamma ((1 : ℂ) + I * (τ : ℂ))‖ *
                    ‖Complex.Gamma ((1 : ℂ) - I * (τ : ℂ))‖ := hprod.symm
            _ ≤ ‖Complex.Gamma ((1 : ℂ) + I * (τ : ℂ))‖ *
                  (C * (1 + |τ|) * Real.exp (-(Real.pi / 2) * |τ|)) :=
                  mul_le_mul_of_nonneg_left hdec (norm_nonneg _)
        have hPH_le_g : (Real.pi * |τ| / Real.sinh (Real.pi * |τ|)) /
              (C * (1 + |τ|) * Real.exp (-(Real.pi / 2) * |τ|)) ≤
            ‖Complex.Gamma ((1 : ℂ) + I * (τ : ℂ))‖ :=
          (div_le_iff₀ hH).2 hP_le_gH
        calc
          c * Real.exp (-(Real.pi / 2) * |τ|)
              ≤ (Real.pi / C) * Real.exp (-(Real.pi / 2) * |τ|) := by
                exact mul_le_mul_of_nonneg_right (by dsimp [c]; exact min_le_right _ _)
                  (Real.exp_pos (-(Real.pi / 2) * |τ|)).le
          _ ≤ (2 * (Real.pi * |τ|) * Real.exp (-(Real.pi * |τ|))) /
                (C * (1 + |τ|) * Real.exp (-(Real.pi / 2) * |τ|)) :=
                gamma_one_lower_region2_chain C |τ| hC hlarge
          _ ≤ (Real.pi * |τ| / Real.sinh (Real.pi * |τ|)) /
                (C * (1 + |τ|) * Real.exp (-(Real.pi / 2) * |τ|)) := by
                exact div_le_div_of_nonneg_right
                  (gamma_one_lower_pi_div_sinh_ge_two_mul_exp |τ| habs) (le_of_lt hH)
          _ ≤ ‖Complex.Gamma ((1 : ℂ) + I * (τ : ℂ))‖ := hPH_le_g

end PL.WeightPoly


/-!
# Root numbers of Dirichlet characters

The global root number `ε(χ) = rootNumber χ` of a primitive Dirichlet character appears in the
functional equation of the completed L-function:

`DirichletCharacter.completedLFunction χ (1 - s) = N ^ (s - 1/2) * rootNumber χ * DirichletCharacter.completedLFunction χ⁻¹ s`

(see `DirichletCharacter.IsPrimitive.completedLFunction_one_sub`), and hence, in the rearranged
form used in the approximate functional equation,

`DirichletCharacter.completedLFunction χ s = N ^ (1/2 - s) * rootNumber χ * DirichletCharacter.completedLFunction χ⁻¹ (1 - s)`.

The main result here is the consistency identity

`rootNumber χ * rootNumber χ⁻¹ = 1`,

which expresses that applying the functional equation twice (once for `χ`, once for `χ⁻¹`)
returns the identity.  It is a prerequisite for deriving the two-sided approximate functional
equation for Dirichlet L-functions (`PL.AFE.approx_functional_equation`).

## Proof strategy

Apply the rearranged functional equation for `χ` and for `χ⁻¹` at suitable points and compare:

* `DirichletCharacter.completedLFunction χ s = N^(1/2 - s) * ε(χ) * DirichletCharacter.completedLFunction χ⁻¹ (1 - s)`   (FE for χ)
* `DirichletCharacter.completedLFunction χ⁻¹ (1 - s) = N^(s - 1/2) * ε(χ⁻¹) * DirichletCharacter.completedLFunction χ s`
  (FE for `χ⁻¹`, with `s` replaced by `1 - s`)

Multiplying the `N`-powers away leaves `DirichletCharacter.completedLFunction χ s = ε(χ) * ε(χ⁻¹) * DirichletCharacter.completedLFunction χ s`.
It remains to evaluate at a point `s` where `DirichletCharacter.completedLFunction χ s ≠ 0`; take `s = 2`, which is
non-zero because `DirichletCharacter.LFunction χ 2 ≠ 0` (`DirichletCharacter.LFunction_ne_zero_of_one_le_re`) and
`gammaFactor χ 2 ≠ 0` (`Complex.Gammaℝ_ne_zero_of_re_pos`), together with
`LFunction_eq_completed_div_gammaFactor`.
-/

open Complex DirichletCharacter
open scoped Real

set_option autoImplicit false

namespace PL.RootNumber

variable {N : ℕ} [NeZero N]

omit [NeZero N] in
/-- A primitive character has primitive inverse. -/
lemma isPrimitive_inv {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) : (χ⁻¹).IsPrimitive := by
  rw [IsPrimitive, conductor_inv, ← isPrimitive_def]
  exact hχ

/-- The completed L-function of a (possibly trivial) character is non-zero at `s = 2`. -/
lemma completedLFunction_apply_two_ne_zero (χ : DirichletCharacter ℂ N) :
    DirichletCharacter.completedLFunction χ 2 ≠ 0 := by
  have hL : DirichletCharacter.LFunction χ 2 ≠ 0 :=
    DirichletCharacter.LFunction_ne_zero_of_one_le_re (χ := χ) (Or.inr (by norm_num : (2 : ℂ) ≠ 1))
      (by norm_num : 1 ≤ (2 : ℂ).re)
  have hγ : gammaFactor χ 2 ≠ 0 := by
    rcases χ.even_or_odd with hχ | hχ
    · rw [hχ.gammaFactor_def]
      exact Gammaℝ_ne_zero_of_re_pos (by norm_num : 0 < (2 : ℂ).re)
    · rw [hχ.gammaFactor_def]
      exact Gammaℝ_ne_zero_of_re_pos (by norm_num : 0 < ((2 : ℂ) + 1).re)
  -- DirichletCharacter.LFunction χ 2 = DirichletCharacter.completedLFunction χ 2 / gammaFactor χ 2
  have h := LFunction_eq_completed_div_gammaFactor χ 2 (Or.inl (by norm_num : (2 : ℂ) ≠ 0))
  -- completed = L * gamma
  intro hzero
  apply hL
  rw [h]
  simp [hzero]

/-- The rearranged functional equation:
`DirichletCharacter.completedLFunction χ s = N ^ (1/2 - s) * rootNumber χ * DirichletCharacter.completedLFunction χ⁻¹ (1 - s)`.
-/
lemma completedLFunction_eq (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive) (s : ℂ) :
    DirichletCharacter.completedLFunction χ s = (N : ℂ) ^ (1 / 2 - s) * χ.rootNumber *
      DirichletCharacter.completedLFunction (χ⁻¹) (1 - s) := by
  have h := DirichletCharacter.IsPrimitive.completedLFunction_one_sub hχ (1 - s)
  -- h : DirichletCharacter.completedLFunction χ (1 - (1 - s)) =
  --     N ^ ((1 - s) - 1 / 2) * rootNumber χ * DirichletCharacter.completedLFunction χ⁻¹ (1 - s)
  have hs : 1 - (1 - s) = s := by ring
  have hexp : (1 - s) - (1 / 2 : ℂ) = 1 / 2 - s := by ring
  rw [hs, hexp] at h
  exact h

/-- The root numbers of a primitive character and its inverse multiply to one:
`ε(χ) · ε(χ⁻¹) = 1`. -/
lemma rootNumber_mul_rootNumber_inv (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive) :
    χ.rootNumber * (χ⁻¹).rootNumber = 1 := by
  -- Apply the rearranged functional equation for χ and for χ⁻¹ at the points `s` and `1 - s`.
  have hprod (s : ℂ) :
      DirichletCharacter.completedLFunction χ s =
        χ.rootNumber * (χ⁻¹).rootNumber * DirichletCharacter.completedLFunction χ s := by
    have h1 := completedLFunction_eq χ hχ s
    -- h1 : DirichletCharacter.completedLFunction χ s = N ^ (1/2 - s) * rootNumber χ * DirichletCharacter.completedLFunction χ⁻¹ (1 - s)
    have h2 := completedLFunction_eq (χ⁻¹) (isPrimitive_inv hχ) (1 - s)
    have h2' : DirichletCharacter.completedLFunction (χ⁻¹) (1 - s) = (N : ℂ) ^ (1 / 2 - (1 - s)) *
        (χ⁻¹).rootNumber * DirichletCharacter.completedLFunction χ s := by
      simpa [inv_inv, sub_sub] using h2
    have hN : (N : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne N)
    have hpows : (N : ℂ) ^ (1 / 2 - s) * (N : ℂ) ^ (1 / 2 - (1 - s)) = 1 := by
      rw [← Complex.cpow_add (1 / 2 - s) (1 / 2 - (1 - s)) hN]
      have hexp : (1 / 2 - s) + (1 / 2 - (1 - s)) = (0 : ℂ) := by ring
      rw [hexp]
      exact Complex.cpow_zero (N : ℂ)
    calc
      DirichletCharacter.completedLFunction χ s
          = (N : ℂ) ^ (1 / 2 - s) * χ.rootNumber * DirichletCharacter.completedLFunction (χ⁻¹) (1 - s) := h1
      _ = (N : ℂ) ^ (1 / 2 - s) * χ.rootNumber *
              ((N : ℂ) ^ (1 / 2 - (1 - s)) * (χ⁻¹).rootNumber * DirichletCharacter.completedLFunction χ s) := by
            rw [h2']
      _ = (N : ℂ) ^ (1 / 2 - s) * (N : ℂ) ^ (1 / 2 - (1 - s)) *
              (χ.rootNumber * (χ⁻¹).rootNumber) * DirichletCharacter.completedLFunction χ s := by
            ring
      _ = 1 * (χ.rootNumber * (χ⁻¹).rootNumber) * DirichletCharacter.completedLFunction χ s := by
            rw [hpows]
      _ = χ.rootNumber * (χ⁻¹).rootNumber * DirichletCharacter.completedLFunction χ s := by
            ring
  -- Evaluate at `s = 2`, where the completed L-function is non-zero, and cancel.
  exact mul_right_cancel₀ (completedLFunction_apply_two_ne_zero χ)
    (by simpa using (hprod (2 : ℂ)).symm)

/-- The root number of the inverse character is the inverse of the root number. -/
lemma rootNumber_inv (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive) :
    (χ⁻¹).rootNumber = (χ.rootNumber)⁻¹ := by
  exact eq_inv_of_mul_eq_one_right (rootNumber_mul_rootNumber_inv χ hχ)

end PL.RootNumber


/-!
# Approximate functional equation for Dirichlet L-functions

This file lays the first stone under `PL.corollary_1_3` (the Weyl bound of
Petrow--Young).  Following the dependency chain identified in the audit of the main
challenge, the first self-contained package is an **exact smooth approximate functional
equation** for the Dirichlet L-functions `L(s, χ)` at issue (primitive `χ`, conductor `N`).

## Mathematical statement

Let `χ` be a primitive Dirichlet character mod `N`, and write

* `γ(s) = gammaFactor χ s` for the archimedean Gamma factor
  (`Gammaℝ s` in the even case, `Gammaℝ (s + 1)` in the odd case);
* `Λ(s) = DirichletCharacter.completedLFunction χ s = γ(s) · L(s, χ)` for the completed L-function;
* `ε = rootNumber χ` for the global root number.

The completed L-function satisfies the functional equation
`Λ(s) = ε · N^(1/2 - s) · Λ̄(1 - s)` where `Λ̄` is the completed L-function of `χ⁻¹`
(see `DirichletCharacter.IsPrimitive.completedLFunction_one_sub`).

Choosing an even holomorphic test function `g` (here `g(u) = exp(u²)`, so `g(0) = 1`)
with rapid decay on vertical lines, define the archimedean smoothing weight by the
vertical Mellin inverse

`W_z(x) = (1 / (2πi)) · ∫_{Re u = 1} x^(-u) · (γ(z + u) / γ(z)) · g(u)/u · du`.

Then for `0 < Re s < 1` the **approximate functional equation** holds:

`L(s, χ) = Σ_{n ≥ 1} χ(n) · n^(-s) · W_s(n / √N)
         + ε · N^(1/2 - s) · (γ(1 - s) / γ(s)) · Σ_{n ≥ 1} χ̄(n) · n^(-(1-s)) · W_{1-s}(n / √N)`.

Both series converge absolutely (the weights decay super-polynomially), and each is a
"short" Dirichlet polynomial up to the transition scale `√N · (1 + |Im s|)`.

This is the Dirichlet-L-function instance of [Iwaniec--Kowalski, Theorem 5.3], written in
the completed normalisation used by Mathlib's `NumberTheory/LSeries` development, and it is
the shape of approximate functional equation used in the analytic-number-theory argument of
Petrow--Young.

The identity was verified numerically (mpmath, 30 digits) for primitive characters of
conductors 5, 7 and 8, real and complex, even and odd, for many values of
`s = σ + it` with `0 < σ < 1`; residuals ~ 1e-7 (integration/truncation accuracy).

## Roadmap (dependency chain toward `corollary_1_3`)

1. ✅ Exact statement of the smooth AFE (this file), definitions of the weight.
2. ✅ Structural layer (this file): gamma-factor non-vanishing in the right half plane,
   rearrangement of the functional equation, `L = Λ/γ` on `Re s > 0`, smoothing function
   `g(u) = exp(u²)` is even with `g(0) = 1`.
3. ✅ Root-number layer (`Submission/RootNumber.lean`): `ε(χ)·ε(χ⁻¹) = 1`, `ε(χ⁻¹) = ε(χ)⁻¹`
   (required to convert the functional-equation leftover in the AFE derivation), and the
   non-vanishing of completed L-functions at `s = 2`.
4. ✅ Archimedean bounds (`Submission/GammaVertical.lean`): the elementary vertical bound
   `|Γ(σ + it)| ≤ Γ(σ)` from Euler's integral, and the uniform-in-`t` bound for
   `Γ((z + a + It)/2)` used by both gamma-factor parities.
5. ✅ (`Submission/GammaRatio*.lean`): uniform-in-`t` bounds for the ratios
   `γ(z + 1 + It)/γ(z)` entering the AFE weight, for even and odd characters.
6. ✅ Archimedean weight convergence (`Submission/WeightConvergesEven.lean`,
   `Submission/WeightConvergesOdd.lean`, `Submission/AfeBounds.lean`): the weight integral is
   (Bochner-)integrable in `t` for both parities; `‖W_z(x)‖ ≤ C(z)·x⁻¹` for `x > 0`; and the
   main/dual smoothed Dirichlet series `Σₙ χ(n)·n⁻ˢ·W_s(n/√N)` converge absolutely for
   `0 < Re s < 1` (`Submission/AfeBounds.summable_main`, `summable_dual`).
   **Super-polynomial decay of `W_z(x)` as `x → ∞` is MACHINE-VERIFIED**
   (`Submission/WeightDecay.lean`, `PL.WeightDecay.afeWeight_norm_decay`):
   for every `n : ℕ` there are `C, k` (independent of `x`, polynomial in `|Im z|`) with
   `‖afeWeight χ (a0 + I·T) x‖ ≤ C·(1+|T|)^k·x^(-n)` for all `x ≥ 1`, `0 < a0`
   (contour shift `Re u = 1 → n` in `Submission/WrContour.lean`, line-`n` bounds in
   `Submission/WrLineBound.lean`).  `W_z(x) → 1` as `x → 0⁺` remains open.)
7. ✅ Mellin inversion (T1): identity between the smoothed Dirichlet sum and a vertical
   integral of the completed L-function (interchange of sum and integral + identifying the
   inner sum with `L(s + u)` on `Re u = 1`, where `Re(s+u) = Re s + 1 > 1`).
   **MACHINE-VERIFIED**: `PL.AfeMellin.main_sum_eq_completed_integral` (files
   `Submission/T1dev.lean`, `Submission/T1Weight.lean`, `Submission/T1asm.lean`,
   `Submission/AfeMellin.lean`).
8. ✅ Functional-equation step (T2–T5): substitute the FE `Λ(s+u) = ε·N^(1/2-s-u)·Λ̄(1-s-u)`,
   shift the contour `Re u = -1 → Re u = +1` collecting the residue `Λ̄(1-s)` at `u = 0`,
   expand the shifted integral into the dual smoothed sum, cancel the leftover against
   `L(s, χ)` (`Submission/AfeAssembly`, `Submission/RootNumber`).  No Phragmén–Lindelöf is
   needed for the contour decay: `Λ` is *bounded* in `t` on the two vertical lines
   `Re(s + u) = σ ± 1` by trivial bounds + the functional equation
   (`Submission/TrivialBounds.norm_completedLFunction_vertical(_left)`), and the smoothing
   function supplies the `exp(-t²)` decay on the horizontal arcs.

   (Implemented in `Submission/AfeVerticalLine.lean` (vertical-line identity +
   `Λ_growth`), `Submission/MellinGrowth.lean` + `Submission/HurwitzStrip.lean` +
   `Submission/CompletedStrip.lean` (strip boundedness of the completed L-function),
   `Submission/AfeGrowth.lean` (`Λ_growth` instance), `Submission/AfeProof.lean`
   (T1/dual/left-line assembly, theorem `afe_identity`), and
   `Submission/AfeTheorem.lean` (**`PL.AFE.approx_functional_equation`**,
   machine-verified, no sorries).  Earlier residue work: `Submission/AfeResidue.lean`,
   `u = 0` of the Mellin integrand `F(u) = x⁻ᵘ·Λ(s+u)·g(u)/u` equals `Λ(s)`:
   `circleIntegral_residue_at_zero` gives `∮_{|u|=R} F(u) du = 2πi·Λ(s)` via Mathlib's
   Cauchy integral formula (`circleIntegral_div_sub_of_differentiable_on_off_countable`)
   applied to the entire numerator `φ(u) = x⁻ᵘ·Λ(s+u)·g(u)` (`φ(0) = Λ(s)`).  The contour
   identity `Λ(s) = c∫_{Re u=1} K - c∫_{Re u=-1} K` (validated numerically) still needs:
   the finite-rectangle residue relation `B_T(K) = 2πi·Λ(s)` (rect boundary integral of the
   FE-transformed integrand `K(u) = ε·N^{1/2-s-u}·x⁻ᵘ·Λ̄(1-s-u)·g(u)/u`, using the
   rectangle Cauchy-Goursat lemmas of `Mathlib/Analysis/Complex/CauchyIntegral.lean`
   `integral_boundary_rect_eq_zero_of_differentiable_on_off_countable` on the subtracted
   holomorphic part, plus the model computation `B_T(1/u) = 2πi`), and then the passage
   `T → ∞` with the horizontal-segment decay.
9. ⬜ Consequences: convexity-type bounds for `|L(1/2 + it, χ)|` in `(N, |t|)`, then the
   subconvex (Weyl) machinery.
8. ⬜ Functional-equation step: contour shift + the FE (2.-3.), giving the two-sided AFE
   (the theorem stated below).
9. ⬜ Consequences: convexity-type bounds for `|L(1/2 + it, χ)|` in `(N, |t|)`, then the
   subconvex (Weyl) machinery.

-/

open Complex DirichletCharacter Filter Topology
open scoped Real Topology BigOperators

set_option autoImplicit false

namespace PL.AFE

noncomputable section

/-! ## The archimedean smoothing weight -/

variable {N : ℕ} [NeZero N]

/-- The even holomorphic test function `g(u) = exp(u²)` used to smooth the approximate
functional equation.  It satisfies `g(0) = 1` and decays rapidly on vertical lines. -/
def smoothingFunction (u : ℂ) : ℂ :=
  cexp (u ^ 2)

/--
The archimedean smoothing weight

`W_z(x) = (1 / (2πi)) · ∫_{Re u = 1} x^(-u) · (γ(z + u) / γ(z)) · exp(u²) / u · du`

of the approximate functional equation for the Dirichlet L-function of `χ`.  Here `γ` is
`χ.gammaFactor`.  (The integral is taken over the vertical line `Re u = 1`, with the
parametrisation matching `Mathlib.Analysis.MellinTransform.mellinInv`.)
-/
def afeWeight (χ : DirichletCharacter ℂ N) (z : ℂ) (x : ℝ) : ℂ :=
  mellinInv 1
    (fun u : ℂ => (χ.gammaFactor (z + u) / χ.gammaFactor z) * smoothingFunction u / u) x

/-- The scale at which the smoothed sums of the approximate functional equation
transition: `x = n / √N`. -/
def afeScale (N : ℕ) (n : ℕ) : ℝ :=
  (n : ℝ) / Real.sqrt (N : ℝ)

/-! ## The approximate functional equation -/

/-! ## First layer: exact structural lemmas (proved) -/

namespace Structural

variable {N : ℕ} [NeZero N]

omit [NeZero N] in
/-- The archimedean gamma factor is non-zero for arguments of positive real part. -/
lemma gammaFactor_ne_zero_of_zero_lt_re (χ : DirichletCharacter ℂ N) {s : ℂ}
    (hs : 0 < s.re) : χ.gammaFactor s ≠ 0 := by
  rcases χ.even_or_odd with hχ | hχ
  · rw [hχ.gammaFactor_def]
    exact Gammaℝ_ne_zero_of_re_pos hs
  · rw [hχ.gammaFactor_def]
    exact Gammaℝ_ne_zero_of_re_pos (by rw [Complex.add_re, one_re]; linarith)

/-- Rearrangement of the functional equation for a primitive character `χ`:
`Λ(s) = ε(χ) · N^(1/2 - s) · Λ(χ⁻¹, 1 - s)`. -/
lemma completedLFunction_eq_rootNumber_mul (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive)
    (s : ℂ) :
    DirichletCharacter.completedLFunction χ s =
      (N : ℂ) ^ (1 / 2 - s) * χ.rootNumber * DirichletCharacter.completedLFunction (χ⁻¹) (1 - s) := by
  have h := DirichletCharacter.IsPrimitive.completedLFunction_one_sub hχ (1 - s)
  rw [show 1 - (1 - s) = s by ring] at h
  rw [show (1 - s) - (1 / 2 : ℂ) = (1 / 2 : ℂ) - s by ring] at h
  exact h

/-- The L-function equals the completed L-function divided by the archimedean gamma
factor, for arguments of positive real part. -/
lemma LFunction_eq_completed_div_gammaFactor_of_zero_lt_re (χ : DirichletCharacter ℂ N)
    {s : ℂ} (hs : 0 < s.re) :
    DirichletCharacter.LFunction χ s = DirichletCharacter.completedLFunction χ s / χ.gammaFactor s := by
  refine LFunction_eq_completed_div_gammaFactor χ s (Or.inl ?_)
  intro hs0
  exact (ne_of_gt hs) (by rw [hs0]; simp)

/-- The test function `g(u) = exp(u²)` is even and satisfies `g(0) = 1`. -/
lemma smoothingFunction_even (u : ℂ) : smoothingFunction (-u) = smoothingFunction u := by
  simp [smoothingFunction, sq]

@[simp] lemma smoothingFunction_zero : smoothingFunction 0 = 1 := by
  simp [smoothingFunction]

omit [NeZero N] in
/-- The character `χ` vanishes at `0` when the modulus is not `1`. -/
lemma apply_zero_of_ne_one {χ : DirichletCharacter ℂ N} (hN : N ≠ 1) : χ 0 = 0 :=
  χ.map_zero' hN

end Structural

end
end PL.AFE


/-!
# Parity and functional-equation glue for the approximate functional equation

This file proves the small algebraic lemmas needed to *assemble* the two-sided
approximate functional equation of `PL.AFE.approx_functional_equation`
from its parts:

1. Inverting a Dirichlet character preserves parity:
   `Even (χ⁻¹) ↔ Even χ`, `Odd (χ⁻¹) ↔ Odd χ`.  Since
   `Even χ` is defined as `χ (-1) = 1` and `Odd χ` as `χ (-1) = -1`
   (`DirichletCharacter.Basic`, with `(-1 : ZMod N)` the unit of order 2 when
   `N ≠ 1`; for `N = 1` everything is trivial), these follow from
   `MulChar.inv_apply χ a : χ⁻¹ a = χ (Ring.inverse a)` together with
   `Ring.inverse (-1) = -1` (use `Ring.inverse_of_isUnit (isUnit_neg_one)` and
   show `↑(isUnit_neg_one.unit⁻¹) = -1` by `Units.ext`, using that the unit with
   value `-1` satisfies `u·u = 1` hence `u⁻¹ = u`, e.g. via
   `eq_inv_of_mul_eq_one_left`).  Handle `N = 1` by `by_cases hN : N = 1` (for
   `N = 1` the unique character is trivial and `Even`).
2. The Archimedean gamma factor depends only on the parity, hence is invariant
   under inversion: `gammaFactor (χ⁻¹) s = gammaFactor χ s` (rewrite both sides
   with the appropriate `Even.gammaFactor_def` / `Odd.gammaFactor_def`), and
   consequently the AFE weights agree: `afeWeight (χ⁻¹) z x = afeWeight χ z x`.
3. The L-function version of the functional equation, valid in the critical
   strip for a primitive non-trivial character:
   `DirichletCharacter.LFunction χ s = rootNumber χ · N ^ (1/2 - s) · (gammaFactor χ (1 - s) / gammaFactor χ s)
                     · DirichletCharacter.LFunction (χ⁻¹) (1 - s)`.
   Proof: `completedLFunction_eq` (FE) + `LFunction_eq_completed_div_gammaFactor_of_zero_lt_re`
   for `DirichletCharacter.LFunction χ s` (at `s`, needs `0 < s.re`) and for `DirichletCharacter.LFunction (χ⁻¹) (1 - s)`
   (needs `0 < (1 - s).re`), then cancel `gammaFactor (χ⁻¹) (1 - s)` using lemma (2).
-/

open Complex DirichletCharacter PL.AFE
open scoped Real

set_option autoImplicit false

namespace PL.AfeAssembly

variable {N : ℕ} [NeZero N]

omit [NeZero N] in
/-- Inversion preserves even parity. -/
lemma even_inv {χ : DirichletCharacter ℂ N} (hχ : χ.Even) : (χ⁻¹).Even := by
  change (χ⁻¹) (-1) = 1
  have h := congrArg (fun φ : DirichletCharacter ℂ N => φ (-1)) (MulChar.inv_mul χ)
  rw [MulChar.mul_apply, MulChar.one_apply (isUnit_neg_one : IsUnit (-1 : ZMod N))] at h
  rwa [hχ, mul_one] at h

omit [NeZero N] in
/-- Inversion preserves odd parity. -/
lemma odd_inv {χ : DirichletCharacter ℂ N} (hχ : χ.Odd) : (χ⁻¹).Odd := by
  change (χ⁻¹) (-1) = -1
  have h := congrArg (fun φ : DirichletCharacter ℂ N => φ (-1)) (MulChar.inv_mul χ)
  rw [MulChar.mul_apply, MulChar.one_apply (isUnit_neg_one : IsUnit (-1 : ZMod N))] at h
  rw [hχ] at h
  calc
    (χ⁻¹) (-1) = (χ⁻¹) (-1) * ((-1 : ℂ) * (-1)) := by ring
    _ = ((χ⁻¹) (-1) * (-1)) * (-1) := by ring
    _ = (1 : ℂ) * (-1) := by rw [h]
    _ = -1 := by ring

omit [NeZero N] in
/-- The Archimedean gamma factor is invariant under inversion of the character. -/
lemma gammaFactor_inv_eq (χ : DirichletCharacter ℂ N) (s : ℂ) :
    gammaFactor (χ⁻¹) s = gammaFactor χ s := by
  rcases χ.even_or_odd with hχ | hχ
  · rw [hχ.gammaFactor_def, (even_inv hχ).gammaFactor_def]
  · rw [hχ.gammaFactor_def, (odd_inv hχ).gammaFactor_def]

/-- The archimedean AFE weight is invariant under inversion of the character. -/
lemma afeWeight_inv_eq (χ : DirichletCharacter ℂ N) (z : ℂ) (x : ℝ) :
    afeWeight (χ⁻¹) z x = afeWeight χ z x := by
  unfold afeWeight
  apply congrArg (fun f : ℂ → ℂ => mellinInv 1 f x)
  funext u
  simp [gammaFactor_inv_eq]

/-- L-function functional equation in the critical strip for a primitive
non-trivial character: `L(s) = ε · N^(1/2 - s) · (γ(1-s)/γ(s)) · L̄(1 - s)`. -/
theorem LFunction_eq (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive) (hχne : χ ≠ 1)
    {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    DirichletCharacter.LFunction χ s = χ.rootNumber * (N : ℂ) ^ (1 / 2 - s)
      * (χ.gammaFactor (1 - s) / χ.gammaFactor s) * DirichletCharacter.LFunction (χ⁻¹) (1 - s) := by
  have hs1' : 0 < (1 - s).re := by
    rw [Complex.sub_re, Complex.one_re]
    linarith
  have h1 : DirichletCharacter.LFunction χ s = DirichletCharacter.completedLFunction χ s / χ.gammaFactor s :=
    PL.AFE.Structural.LFunction_eq_completed_div_gammaFactor_of_zero_lt_re χ hs0
  have h3 : DirichletCharacter.LFunction (χ⁻¹) (1 - s) =
      DirichletCharacter.completedLFunction (χ⁻¹) (1 - s) / gammaFactor (χ⁻¹) (1 - s) :=
    PL.AFE.Structural.LFunction_eq_completed_div_gammaFactor_of_zero_lt_re (χ := χ⁻¹)
      (s := 1 - s) hs1'
  calc
    DirichletCharacter.LFunction χ s
        = DirichletCharacter.completedLFunction χ s / χ.gammaFactor s := h1
    _ = ((N : ℂ) ^ (1 / 2 - s) * χ.rootNumber * DirichletCharacter.completedLFunction (χ⁻¹) (1 - s))
          / χ.gammaFactor s := by
          rw [PL.RootNumber.completedLFunction_eq χ hχ s]
    _ = χ.rootNumber * (N : ℂ) ^ (1 / 2 - s)
          * (χ.gammaFactor (1 - s) / χ.gammaFactor s) * DirichletCharacter.LFunction (χ⁻¹) (1 - s) := by
          rw [h3]
          rw [← gammaFactor_inv_eq χ (1 - s)]
          have hγinv : gammaFactor (χ⁻¹) (1 - s) ≠ 0 :=
            PL.AFE.Structural.gammaFactor_ne_zero_of_zero_lt_re (χ := χ⁻¹) (s := 1 - s) hs1'
          have hg : χ.gammaFactor s ≠ 0 :=
            PL.AFE.Structural.gammaFactor_ne_zero_of_zero_lt_re χ hs0
          field_simp [hγinv, hg]

end PL.AfeAssembly


/-!
# The residue at `u = 0` of the Mellin-kernel integrand (T2, first step)

The approximate-functional-equation contour identity will be built from the meromorphic
integrand

`F(u) = x⁻ᵘ · Λ(s+u) · g(u) / u`          (`x > 0` real, `g(u) = exp(u²)`)

whose only pole in a neighbourhood of `0` is a simple pole at `u = 0`, with residue
`F(0)·u |_{u=0} = Λ(s)` (because `g(0) = 1`).  This file proves that fact in the form of
the Cauchy integral formula around the origin:

`∮_{|u| = R} F(u) du = 2πi · Λ(s)`.

The proof applies Mathlib's Cauchy integral formula
`circleIntegral_div_sub_of_differentiable_on_off_countable` to the *entire* function
`φ(u) = x⁻ᵘ · Λ(s+u) · g(u)` (differentiable because `Λ` is entire when `χ ≠ 1`, the
smoothing function is entire, and complex powers with a fixed positive-real base are
entire), noting `F(u) = φ(u) / u` and `φ(0) = Λ(s)`.

## Status
Machine-verified statements so far: the residue identity
`PL.AfeResidue.circleIntegral_residue_at_zero` below.
-/

open Complex DirichletCharacter Filter MeasureTheory Set Metric
open PL.AFE
open scoped Real Topology 

set_option autoImplicit false

namespace PL.AfeResidue

variable {N : ℕ} [NeZero N]

/-- The power kernel `u ↦ x⁻ᵘ` (fixed positive real base) is entire. -/
lemma differentiable_kernel {x : ℝ} (hx : 0 < x) :
    Differentiable ℂ (fun u : ℂ => (x : ℂ) ^ (-u)) := by
  refine Differentiable.cpow ?_ ?_ ?_
  · exact differentiable_const (x : ℂ)
  · exact Differentiable.neg differentiable_id
  · intro u
    exact Complex.ofReal_mem_slitPlane.mpr hx

/-- The completed-L-function shift `u ↦ Λ(s+u)` is entire when `χ ≠ 1`. -/
lemma differentiable_completed_shift (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (s : ℂ) :
    Differentiable ℂ (fun u : ℂ => DirichletCharacter.completedLFunction χ (s + u)) := by
  have hΛ : Differentiable ℂ (DirichletCharacter.completedLFunction χ) :=
    DirichletCharacter.differentiable_completedLFunction hχ
  have hadd : Differentiable ℂ (fun u : ℂ => s + u) := (differentiable_const s).add differentiable_id
  simpa [Function.comp_def] using hΛ.comp hadd

/-- The Mellin-kernel integrand numerator `φ(u) = x⁻ᵘ · Λ(s+u) · g(u)` is entire. -/
lemma differentiable_phi (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (s : ℂ) {x : ℝ} (hx : 0 < x) :
    Differentiable ℂ (fun u : ℂ => (x : ℂ) ^ (-u) * DirichletCharacter.completedLFunction χ (s + u) * smoothingFunction u) := by
  have h1 := differentiable_kernel (x := x) hx
  have h2 := differentiable_completed_shift χ hχ s
  have hg : Differentiable ℂ (fun u : ℂ => smoothingFunction u) := by
    unfold smoothingFunction
    exact Differentiable.cexp (differentiable_pow 2)
  change Differentiable ℂ
    (((fun u : ℂ => (x : ℂ) ^ (-u)) * fun u : ℂ => DirichletCharacter.completedLFunction χ (s + u))
      * fun u : ℂ => smoothingFunction u)
  exact (h1.mul h2).mul hg

/-- **Residue at `u = 0` of the AFE Mellin integrand equals `Λ(s)`**:
for `χ ≠ 1`, `0 < x`, `0 < R`,

`∮_{|u|=R} x⁻ᵘ·Λ(s+u)·g(u)/u du = 2πi · Λ(s)`.

(`x` will be instantiated with `(√N)⁻¹` in the AFE; `g(u) = exp(u²)`.) -/
theorem circleIntegral_residue_at_zero (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (s : ℂ)
    {x : ℝ} (hx : 0 < x) {R : ℝ} (hR : 0 < R) :
    (∮ u in C(0, R), ((x : ℂ) ^ (-u) * DirichletCharacter.completedLFunction χ (s + u) * smoothingFunction u) / u)
      = (2 * π * I : ℂ) * DirichletCharacter.completedLFunction χ s := by
  let φ : ℂ → ℂ := fun u => (x : ℂ) ^ (-u) * DirichletCharacter.completedLFunction χ (s + u) * smoothingFunction u
  have hφ : Differentiable ℂ φ := differentiable_phi χ hχ s hx
  have hw : (0 : ℂ) ∈ ball (0 : ℂ) R := by
    exact Metric.mem_ball_self hR
  have hc : ContinuousOn φ (closedBall (0 : ℂ) R) := (hφ.continuous).continuousOn
  have hd : ∀ z ∈ ball (0 : ℂ) R \ (∅ : Set ℂ), DifferentiableAt ℂ φ z := by
    intro z hz
    exact Differentiable.differentiableAt (x := z) hφ
  have hCIF := circleIntegral_div_sub_of_differentiable_on_off_countable (R := R) (c := (0 : ℂ))
    (w := (0 : ℂ)) (s := (∅ : Set ℂ)) countable_empty hw hc hd
  -- hCIF : ∮ z in C(0,R), φ z / (z - 0) = 2πI * φ 0
  have hφ0 : φ 0 = DirichletCharacter.completedLFunction χ s := by
    dsimp [φ]
    simp [smoothingFunction]
  calc
    (∮ u in C(0, R), ((x : ℂ) ^ (-u) * DirichletCharacter.completedLFunction χ (s + u) * smoothingFunction u) / u)
        = ∮ u in C(0, R), φ u / (u - 0) := by
          congr 1
          funext u
          dsimp [φ]
          rw [sub_zero]
    _ = (2 * π * I : ℂ) * φ 0 := hCIF
    _ = (2 * π * I : ℂ) * DirichletCharacter.completedLFunction χ s := by rw [hφ0]

end PL.AfeResidue


/-!
# The finite-rectangle residue relation for the Mellin integrand (T2, third step)

For the AFE Mellin integrand `K(u) = x⁻ᵘ · Λ(s+u) · g(u)/u` (entire numerator
`φ(u) = u·K(u)`, `φ(0) = Λ(s)`) we prove the finite-rectangle residue identity

`B_T(K) = 2πi · Λ(s)`    (`rectBoundary_K` below),

i.e. `rectBoundary ⟨-1,-T⟩ ⟨1,T⟩ (u ↦ x⁻ᵘΛ(s+u)g(u)/u) = 2πi·Λ(s)`.

Strategy (three moves):
1. `rectBoundary_four`: expand `rectBoundary ⟨-1,-T⟩ ⟨1,T⟩ f` into the four edge
   integrals (bottom/top/right/left, matching the convention of `AfeRect.rectBoundary_inv`);
2. the pole subtraction: `ψ(u) = (φ(u)-φ(0))/u` (extended at `u = 0` by `deriv φ 0`) is
   continuous on the closed rectangle and holomorphic off `{0}` (so the off-countable
   Cauchy-Goursat theorem `integral_boundary_rect_eq_zero_of_differentiable_on_off_countable`
   gives `rectBoundary ψ = 0`); pointwise `K(u) = φ(0)·u⁻¹ + ψ(u)` on the boundary;
3. linearity of `rectBoundary` in the integrand (edge by edge, with continuity-based
   integrability) gives `B_T(K) = φ(0)·B_T(1/u) + B_T(ψ) = Λ(s)·2πi + 0`, using the model
   computation `AfeRect.rectBoundary_inv`.
-/

open MeasureTheory
open scoped Real 
set_option autoImplicit false

namespace PL.AfeRect

noncomputable section

variable {N : ℕ} [NeZero N]

open Complex

/-- The four-edge expression for the rectangle with corners `⟨-1,-T⟩`, `⟨1,T⟩`
(bottom, top, right, left edges), matching the convention of `rectBoundary_inv`. -/
noncomputable def rectBoundaryFour (T : ℝ) (f : ℂ → ℂ) : ℂ :=
  (∫ x : ℝ in (-1 : ℝ)..1, f ((x : ℂ) - I * (T : ℂ)))
    - (∫ x : ℝ in (-1 : ℝ)..1, f ((x : ℂ) + I * (T : ℂ)))
    + I • (∫ y : ℝ in -T..T, f ((1 : ℂ) + I * (y : ℂ)))
    - I • (∫ y : ℝ in -T..T, f ((-1 : ℂ) + I * (y : ℂ)))

/-- `rectBoundary ⟨-1,-T⟩ ⟨1,T⟩ f` expands into the four edge integrals. -/
lemma rectBoundary_four (T : ℝ) (f : ℂ → ℂ) :
    rectBoundary ⟨-1, -T⟩ ⟨1, T⟩ f = rectBoundaryFour T f := by
  unfold rectBoundary rectBoundaryFour
  have hb : (∫ x : ℝ in (-1 : ℝ)..1, f (x + (⟨-1, -T⟩ : ℂ).im * I))
      = ∫ x : ℝ in (-1 : ℝ)..1, f ((x : ℂ) - I * (T : ℂ)) := by
    apply intervalIntegral.integral_congr
    intro x hx
    congr 1
    rw [show (⟨-1, -T⟩ : ℂ).im = -T by rfl]
    rw [Complex.ofReal_neg]
    ring
  have ht : (∫ x : ℝ in (-1 : ℝ)..1, f (x + (⟨1, T⟩ : ℂ).im * I))
      = ∫ x : ℝ in (-1 : ℝ)..1, f ((x : ℂ) + I * (T : ℂ)) := by
    apply intervalIntegral.integral_congr
    intro x hx
    congr 1
    rw [show (⟨1, T⟩ : ℂ).im = T by rfl]
    ring
  have hr : (∫ y : ℝ in -T..T, f (re ⟨1, T⟩ + y * I))
      = ∫ y : ℝ in -T..T, f ((1 : ℂ) + I * (y : ℂ)) := by
    apply intervalIntegral.integral_congr
    intro y hy
    congr 1
    rw [show (⟨1, T⟩ : ℂ).re = 1 by rfl]
    rw [Complex.ofReal_one]
    ring
  have hl : (∫ y : ℝ in -T..T, f (re ⟨-1, -T⟩ + y * I))
      = ∫ y : ℝ in -T..T, f ((-1 : ℂ) + I * (y : ℂ)) := by
    apply intervalIntegral.integral_congr
    intro y hy
    congr 1
    rw [show (⟨-1, -T⟩ : ℂ).re = -1 by rfl]
    rw [Complex.ofReal_neg, Complex.ofReal_one]
    ring
  rw [hb, ht, hr, hl]

/-- The bottom edge map `x ↦ x - iT` avoids `0`. -/
lemma edge_bot_ne_zero (T : ℝ) (hT : 0 < T) (x : ℝ) : (x : ℂ) - I * (T : ℂ) ≠ 0 := by
  intro h
  have hns := congrArg (fun u : ℂ => Complex.normSq u) h
  rw [Complex.normSq_apply, Complex.normSq_apply] at hns
  simp at hns
  ring_nf at hns
  have hT2 : 0 < T ^ 2 := sq_pos_of_ne_zero (ne_of_gt hT)
  nlinarith [sq_nonneg x, hT2]
/-- The top edge map `x ↦ x + iT` avoids `0`. -/
lemma edge_top_ne_zero (T : ℝ) (hT : 0 < T) (x : ℝ) : (x : ℂ) + I * (T : ℂ) ≠ 0 := by
  intro h
  have hns := congrArg (fun u : ℂ => Complex.normSq u) h
  rw [Complex.normSq_apply, Complex.normSq_apply] at hns
  simp at hns
  ring_nf at hns
  have hT2 : 0 < T ^ 2 := sq_pos_of_ne_zero (ne_of_gt hT)
  nlinarith [sq_nonneg x, hT2]
/-- The right edge map `y ↦ 1 + iy` avoids `0`. -/
lemma edge_right_ne_zero (y : ℝ) : (1 : ℂ) + I * (y : ℂ) ≠ 0 := by
  intro h
  have hns := congrArg (fun u : ℂ => Complex.normSq u) h
  rw [Complex.normSq_apply, Complex.normSq_apply] at hns
  simp at hns
  ring_nf at hns
  nlinarith [sq_nonneg y]
/-- The left edge map `y ↦ -1 + iy` avoids `0`. -/
lemma edge_left_ne_zero (y : ℝ) : (-1 : ℂ) + I * (y : ℂ) ≠ 0 := by
  intro h
  have hns := congrArg (fun u : ℂ => Complex.normSq u) h
  rw [Complex.normSq_apply, Complex.normSq_apply] at hns
  simp at hns
  ring_nf at hns
  nlinarith [sq_nonneg y]

/-- Continuity of `u ↦ u⁻¹` along the four edges. -/
lemma cont_inv_edge_bot (T : ℝ) (hT : 0 < T) :
    Continuous (fun x : ℝ => (((x : ℂ) - I * (T : ℂ))⁻¹)) := by
  refine Continuous.inv₀ ?_ (edge_bot_ne_zero T hT)
  fun_prop
lemma cont_inv_edge_top (T : ℝ) (hT : 0 < T) :
    Continuous (fun x : ℝ => (((x : ℂ) + I * (T : ℂ))⁻¹)) := by
  refine Continuous.inv₀ ?_ (edge_top_ne_zero T hT)
  fun_prop
lemma cont_inv_edge_right : Continuous (fun y : ℝ => (((1 : ℂ) + I * (y : ℂ))⁻¹)) := by
  refine Continuous.inv₀ ?_ edge_right_ne_zero
  fun_prop
lemma cont_inv_edge_left : Continuous (fun y : ℝ => (((-1 : ℂ) + I * (y : ℂ))⁻¹)) := by
  refine Continuous.inv₀ ?_ edge_left_ne_zero
  fun_prop

/-- Pointwise pole subtraction: for `u ≠ 0`, `φ u / u = a·u⁻¹ + (φ u - a)/u`. -/
lemma pole_split (φ : ℂ → ℂ) (a : ℂ) (u : ℂ) (hu : u ≠ 0) (hφ0 : φ 0 = a) :
    φ u / u = a * u⁻¹ + (φ u - φ 0) / u := by
  rw [hφ0]
  field_simp [hu]
  ring

/-- Linearity of the four-edge integral: `B_T(a·u⁻¹ + ψ) = a·B_T(u⁻¹) + B_T(ψ)`,
whenever `ψ` is continuous (so that the edge compositions are integrable). -/
lemma rectBoundaryFour_add_const_inv (T : ℝ) (hT : 0 < T) (a : ℂ) (ψ : ℂ → ℂ)
    (hψ : Continuous ψ) :
    rectBoundaryFour T (fun u : ℂ => a * u⁻¹ + ψ u)
      = a * rectBoundaryFour T (fun u : ℂ => u⁻¹) + rectBoundaryFour T ψ := by
  unfold rectBoundaryFour
  have hb : (∫ x : ℝ in (-1 : ℝ)..1, a * (((x : ℂ) - I * (T : ℂ))⁻¹) + ψ ((x : ℂ) - I * (T : ℂ)))
      = a * (∫ x : ℝ in (-1 : ℝ)..1, (((x : ℂ) - I * (T : ℂ))⁻¹))
        + (∫ x : ℝ in (-1 : ℝ)..1, ψ ((x : ℂ) - I * (T : ℂ))) := by
    rw [intervalIntegral.integral_add]
    · rw [← intervalIntegral.integral_const_mul]
    · exact ((continuous_const.mul (cont_inv_edge_bot T hT)).intervalIntegrable _ _)
    · exact (hψ.comp (by fun_prop : Continuous fun x : ℝ => (x : ℂ) - I * (T : ℂ))).intervalIntegrable _ _
  have ht : (∫ x : ℝ in (-1 : ℝ)..1, a * (((x : ℂ) + I * (T : ℂ))⁻¹) + ψ ((x : ℂ) + I * (T : ℂ)))
      = a * (∫ x : ℝ in (-1 : ℝ)..1, (((x : ℂ) + I * (T : ℂ))⁻¹))
        + (∫ x : ℝ in (-1 : ℝ)..1, ψ ((x : ℂ) + I * (T : ℂ))) := by
    rw [intervalIntegral.integral_add]
    · rw [← intervalIntegral.integral_const_mul]
    · exact ((continuous_const.mul (cont_inv_edge_top T hT)).intervalIntegrable _ _)
    · exact (hψ.comp (by fun_prop : Continuous fun x : ℝ => (x : ℂ) + I * (T : ℂ))).intervalIntegrable _ _
  have hr : (∫ y : ℝ in -T..T, a * (((1 : ℂ) + I * (y : ℂ))⁻¹) + ψ ((1 : ℂ) + I * (y : ℂ)))
      = a * (∫ y : ℝ in -T..T, (((1 : ℂ) + I * (y : ℂ))⁻¹))
        + (∫ y : ℝ in -T..T, ψ ((1 : ℂ) + I * (y : ℂ))) := by
    rw [intervalIntegral.integral_add]
    · rw [← intervalIntegral.integral_const_mul]
    · exact ((continuous_const.mul cont_inv_edge_right).intervalIntegrable _ _)
    · exact (hψ.comp (by fun_prop : Continuous fun y : ℝ => (1 : ℂ) + I * (y : ℂ))).intervalIntegrable _ _
  have hl : (∫ y : ℝ in -T..T, a * (((-1 : ℂ) + I * (y : ℂ))⁻¹) + ψ ((-1 : ℂ) + I * (y : ℂ)))
      = a * (∫ y : ℝ in -T..T, (((-1 : ℂ) + I * (y : ℂ))⁻¹))
        + (∫ y : ℝ in -T..T, ψ ((-1 : ℂ) + I * (y : ℂ))) := by
    rw [intervalIntegral.integral_add]
    · rw [← intervalIntegral.integral_const_mul]
    · exact ((continuous_const.mul cont_inv_edge_left).intervalIntegrable _ _)
    · exact (hψ.comp (by fun_prop : Continuous fun y : ℝ => (-1 : ℂ) + I * (y : ℂ))).intervalIntegrable _ _
  rw [hb, ht, hr, hl]
  ring


end



end PL.AfeRect


/-!
# The finite-rectangle residue relation for the Mellin integrand (T2 completion)

**`rectBoundary_K`**: for a character `χ ≠ 1`, `0 < x`, `0 < T`, the boundary integral of
the AFE Mellin integrand around the rectangle with corners `⟨-1,-T⟩`, `⟨1,T⟩` equals
`2πi·Λ(s)`:

`rectBoundary ⟨-1,-T⟩ ⟨1,T⟩ (u ↦ x⁻ᵘ·Λ(s+u)·g(u)/u) = 2πi · Λ(s)`.

Assembly:
1. `phi_entire`: `φ(u) = x⁻ᵘΛ(s+u)g(u)` is entire (`AfeResidue.differentiable_phi`),
   and `φ 0 = Λ(s)` (`phi_zero`).
2. `psi` facts (`PsiPkg`): `ψ(u) = (φ u - φ 0)/u` extended at `0` is continuous and
   differentiable off `{0}`; hence the off-countable Cauchy-Goursat theorem gives
   `rectBoundary ψ = 0` (`rectBoundary_psi_zero`).
3. Edge linearity (`AfeRectResidue.rectBoundaryFour_add_const_inv`) plus the pointwise
   splitting `K(u) = Λ(s)·u⁻¹ + ψ(u)` (on the boundary `u ≠ 0`) and the model value
   `rectBoundary_inv` give `B_T(K) = Λ(s)·2πi`.
-/

open MeasureTheory DirichletCharacter
open PL.AFE
open scoped Real 
set_option autoImplicit false

namespace PL.AfeRect

noncomputable section

variable {N : ℕ} [NeZero N]

open Complex

/-- `φ(u) = x⁻ᵘ·Λ(s+u)·g(u)` (entire numerator of the Mellin integrand). -/
noncomputable def phi (χ : DirichletCharacter ℂ N) (s : ℂ) (x : ℝ) : ℂ → ℂ :=
  fun u => (x : ℂ) ^ (-u) * DirichletCharacter.completedLFunction χ (s + u) * smoothingFunction u

/-- `φ(0) = Λ(s)`. -/
lemma phi_zero (χ : DirichletCharacter ℂ N) (s : ℂ) (x : ℝ) : phi χ s x 0 = DirichletCharacter.completedLFunction χ s := by
  unfold phi
  simp [smoothingFunction]

/-- `φ` is entire for `χ ≠ 1`, `0 < x`. -/
lemma phi_entire (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (s : ℂ) {x : ℝ} (hx : 0 < x) :
    Differentiable ℂ (phi χ s x) := by
  unfold phi
  exact AfeResidue.differentiable_phi χ hχ s hx

/-- The Mellin integrand `K(u) = x⁻ᵘΛ(s+u)g(u)/u` is `φ(u)/u`. -/
lemma mellinIntegrand_eq_phi_div (χ : DirichletCharacter ℂ N) (s : ℂ) (x : ℝ) (u : ℂ) :
    (x : ℂ) ^ (-u) * DirichletCharacter.completedLFunction χ (s + u) * smoothingFunction u / u
      = phi χ s x u / u := by
  unfold phi
  rfl

/-- `rectBoundary ψ = 0` for the pole subtraction `ψ = psi φ`, by Cauchy-Goursat
(off the countable set `{0}`). -/
lemma rectBoundary_psi_zero (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (s : ℂ)
    {x : ℝ} (hx : 0 < x) (T : ℝ) (hT : 0 < T) :
    rectBoundary ⟨-1, -T⟩ ⟨1, T⟩ (psi (phi χ s x)) = 0 := by
  have hφ : Differentiable ℂ (phi χ s x) := phi_entire χ hχ s hx
  have hψc : Continuous (psi (phi χ s x)) := continuous_psi (phi χ s x) hφ
  -- apply the off-countable Cauchy-Goursat theorem
  unfold rectBoundary
  refine integral_boundary_rect_eq_zero_of_differentiable_on_off_countable
    (f := psi (phi χ s x)) (z := ⟨-1, -T⟩) (w := ⟨1, T⟩)
    (s := ({0} : Set ℂ)) ?_ ?_ ?_
  · exact Set.countable_singleton 0
  · exact hψc.continuousOn
  · intro z hz
    exact differentiableAt_psi_of_ne_zero (phi χ s x) hφ (by simpa using hz.2)


/-- Pointwise-congruence of the four-edge integral on the (pole-free) boundary. -/
lemma rectBoundaryFour_congr_of_ne_zero (T : ℝ) (hT : 0 < T) {f g : ℂ → ℂ}
    (h : ∀ u : ℂ, u ≠ 0 → f u = g u) :
    rectBoundaryFour T f = rectBoundaryFour T g := by
  unfold rectBoundaryFour
  have hb : (∫ x : ℝ in (-1 : ℝ)..1, f ((x : ℂ) - I * (T : ℂ)))
      = ∫ x : ℝ in (-1 : ℝ)..1, g ((x : ℂ) - I * (T : ℂ)) := by
    apply intervalIntegral.integral_congr
    intro x hx
    exact h ((x : ℂ) - I * (T : ℂ)) (edge_bot_ne_zero T hT x)
  have ht : (∫ x : ℝ in (-1 : ℝ)..1, f ((x : ℂ) + I * (T : ℂ)))
      = ∫ x : ℝ in (-1 : ℝ)..1, g ((x : ℂ) + I * (T : ℂ)) := by
    apply intervalIntegral.integral_congr
    intro x hx
    exact h ((x : ℂ) + I * (T : ℂ)) (edge_top_ne_zero T hT x)
  have hr : (∫ y : ℝ in -T..T, f ((1 : ℂ) + I * (y : ℂ)))
      = ∫ y : ℝ in -T..T, g ((1 : ℂ) + I * (y : ℂ)) := by
    apply intervalIntegral.integral_congr
    intro y hy
    exact h ((1 : ℂ) + I * (y : ℂ)) (edge_right_ne_zero y)
  have hl : (∫ y : ℝ in -T..T, f ((-1 : ℂ) + I * (y : ℂ)))
      = ∫ y : ℝ in -T..T, g ((-1 : ℂ) + I * (y : ℂ)) := by
    apply intervalIntegral.integral_congr
    intro y hy
    exact h ((-1 : ℂ) + I * (y : ℂ)) (edge_left_ne_zero y)
  rw [hb, ht, hr, hl]

/-- **The finite-rectangle residue relation** for the Mellin integrand:
`B_T(K) = 2πi·Λ(s)`. -/
lemma rectBoundary_K (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (s : ℂ)
    {x : ℝ} (hx : 0 < x) (T : ℝ) (hT : 0 < T) :
    rectBoundary ⟨-1, -T⟩ ⟨1, T⟩
        (fun u : ℂ => (x : ℂ) ^ (-u) * DirichletCharacter.completedLFunction χ (s + u) * smoothingFunction u / u)
      = 2 * π * I * DirichletCharacter.completedLFunction χ s := by
  let φ : ℂ → ℂ := phi χ s x
  let a : ℂ := DirichletCharacter.completedLFunction χ s
  have hφ : Differentiable ℂ φ := by simpa [φ] using phi_entire χ hχ s hx
  have hψc : Continuous (psi φ) := continuous_psi φ hφ
  have hK : (fun u : ℂ => (x : ℂ) ^ (-u) * DirichletCharacter.completedLFunction χ (s + u) * smoothingFunction u / u)
      = fun u : ℂ => φ u / u := by
    funext u
    simp [φ, phi]
  have hsplit : ∀ u : ℂ, u ≠ 0 → φ u / u = a * u⁻¹ + psi φ u := by
    intro u hu
    have hφ0 : φ 0 = a := by simp [φ, a, phi]
    rw [pole_split φ a u hu hφ0]
    rw [← psi_of_ne_zero φ hu]
  have hC : rectBoundaryFour T (fun u : ℂ => φ u / u) = rectBoundaryFour T (fun u : ℂ => a * u⁻¹ + psi φ u) := by
    refine rectBoundaryFour_congr_of_ne_zero T hT ?_
    intro u hu
    exact hsplit u hu
  have hLin := rectBoundaryFour_add_const_inv T hT a (psi φ) hψc
  have hInv4 : rectBoundaryFour T (fun u : ℂ => u⁻¹) = 2 * π * I := by
    exact (rectBoundary_four T (fun u : ℂ => u⁻¹)).symm.trans (rectBoundary_inv_corners T hT)
  have hPsi4 : rectBoundaryFour T (psi φ) = 0 := by
    have hzero : rectBoundary ⟨-1, -T⟩ ⟨1, T⟩ (psi (phi χ s x)) = 0 :=
      rectBoundary_psi_zero χ hχ s hx T hT
    have heq1 : rectBoundaryFour T (psi (phi χ s x)) = 0 := by
      exact (rectBoundary_four T (psi (phi χ s x))).symm.trans hzero
    simpa [φ] using heq1
  calc
    rectBoundary ⟨-1, -T⟩ ⟨1, T⟩ (fun u : ℂ => (x : ℂ) ^ (-u) * DirichletCharacter.completedLFunction χ (s + u) * smoothingFunction u / u)
        = rectBoundaryFour T (fun u : ℂ => φ u / u) := by
          rw [hK]
          exact rectBoundary_four T (fun u : ℂ => φ u / u)
    _ = rectBoundaryFour T (fun u : ℂ => a * u⁻¹ + psi φ u) := hC
    _ = a * rectBoundaryFour T (fun u : ℂ => u⁻¹) + rectBoundaryFour T (psi φ) := hLin
    _ = 2 * π * I * a := by
          rw [hInv4, hPsi4]
          ring
    _ = 2 * π * I * DirichletCharacter.completedLFunction χ s := by simp [a]

end

end PL.AfeRect


/-!
# Lower bounds for the archimedean gamma factor in the critical strip

This file upgrades the complex-Gamma lower bound
(`PL.GammaLower.norm_Gamma_lower_bound`) to the *archimedean gamma factor*
`γ(s) = gammaFactor χ s` (`Complex.Gammaℝ s` for even `χ`, `Complex.Gammaℝ (s + 1)` for
odd `χ`), uniformly on vertical lines inside the critical strip:

For a character `χ` (even or odd) and `0 < σ < 1` there is a constant `C(σ, parity) > 0`
with

`C · exp(-(π/2)·|t|) ≤ |γ(σ + I t)|`   for all real `t`.

## Proof strategy

Split on `χ.even_or_odd`.

* **Even**: `γ(s) = Complex.Gammaℝ s = π^(-s/2) · Γ(s/2)`; so
  `|γ(σ + I t)| = π^(-σ/2) · |Γ(σ/2 + I (t/2))|`.  Apply
  `PL.GammaLower.norm_Gamma_lower_bound` at `σ' := σ / 2` (so `0 < σ' < 1`),
  `t' := t / 2`, giving `|Γ(σ/2 + I(t/2))| ≥ C(σ/2)·exp(-π·|t/2|) = C·exp(-(π/2)|t|)`.
  The factor `π^(-σ/2)` is a positive constant (use
  `Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos` for the power of `π`).
* **Odd**: `γ(s) = Complex.Gammaℝ (s + 1)`, so with `s = σ + I t` the argument is
  `(σ + 1) + I t`, whose Gammaℝ expansion gives `|γ| = π^(-(σ+1)/2)·|Γ((σ+1)/2 + I (t/2))|`;
  apply the lower bound at `σ' := (σ + 1) / 2 ∈ (1/2, 1)`.

All constant expressions must be witnessed by existential `C > 0`; explicit closed forms
are not needed.

The shared content of both parity cases is the auxiliary lemma
`norm_Gammaℝ_lower_bound_line`: for real `0 < a < 2` (i.e. real part of the
`Gammaℝ` argument, divided by two, lies in `(0, 1)`),
`|Gammaℝ (a + I t)| ≥ C · exp (-(π/2)·|t|)` uniformly in `t`.
-/

open Complex DirichletCharacter
open scoped Real

set_option autoImplicit false

namespace PL.GammaFactorLower

variable {N : ℕ} [NeZero N]

omit [NeZero N] in
/-- For real `0 < a < 2` the archimedean factor `Gammaℝ` is bounded below on the vertical
line `Re s = a`: `C · exp (-(π/2)·|t|) ≤ |Gammaℝ (a + I t)|` uniformly in real `t`.

Since `Gammaℝ s = π^(-s/2) · Γ(s/2)`, the power contributes the fixed positive constant
`π^(-a/2)` and the Gamma factor is controlled by
`PL.GammaLower.norm_Gamma_lower_bound` at the real part `a / 2 ∈ (0, 1)`. -/
lemma norm_Gammaℝ_lower_bound_line {a : ℝ} (ha0 : 0 < a) (ha2 : a < 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ,
      C * Real.exp (-(Real.pi / 2) * |t|) ≤ ‖Complex.Gammaℝ ((a : ℂ) + I * (t : ℂ))‖ := by
  have hA : 0 < Real.pi ^ (-a / 2) := Real.rpow_pos_of_pos Real.pi_pos _
  have hha0 : 0 < a / 2 := by positivity
  have hha2 : a / 2 < 1 := by nlinarith
  obtain ⟨C0, hC0pos, hC0⟩ :=
    PL.GammaLower.norm_Gamma_lower_bound (a / 2) hha0 hha2
  refine ⟨Real.pi ^ (-a / 2) * C0, mul_pos hA hC0pos, ?_⟩
  intro t
  have harg : ((a : ℂ) + I * (t : ℂ)) / 2 = ((a / 2 : ℝ) : ℂ) + I * (((t / 2 : ℝ) : ℂ)) := by
    apply Complex.ext <;> simp
  have hΓu : C0 * Real.exp (-Real.pi * |t / 2|) ≤
      ‖Complex.Gamma (((a / 2 : ℝ) : ℂ) + I * (((t / 2 : ℝ) : ℂ)))‖ := hC0 (t / 2)
  have hΓz : C0 * Real.exp (-Real.pi * |t / 2|) ≤
      ‖Complex.Gamma (((a : ℂ) + I * (t : ℂ)) / 2)‖ := by
    simpa [harg] using hΓu
  have hExp : -Real.pi * |t / 2| = -(Real.pi / 2) * |t| := by
    rw [abs_div]
    norm_num
    ring
  have hΓexp : C0 * Real.exp (-(Real.pi / 2) * |t|) ≤
      ‖Complex.Gamma (((a : ℂ) + I * (t : ℂ)) / 2)‖ := by
    rwa [hExp] at hΓz
  have hnorm : ‖Complex.Gammaℝ ((a : ℂ) + I * (t : ℂ))‖
      = (Real.pi ^ (-a / 2)) * ‖Complex.Gamma (((a : ℂ) + I * (t : ℂ)) / 2)‖ := by
    rw [Complex.Gammaℝ_def, Complex.norm_mul]
    rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
    congr 1
    simp
  calc
    (Real.pi ^ (-a / 2) * C0) * Real.exp (-(Real.pi / 2) * |t|)
        = Real.pi ^ (-a / 2) * (C0 * Real.exp (-(Real.pi / 2) * |t|)) := by ring
    _ ≤ Real.pi ^ (-a / 2) * ‖Complex.Gamma (((a : ℂ) + I * (t : ℂ)) / 2)‖ := by
        exact mul_le_mul_of_nonneg_left hΓexp (le_of_lt hA)
    _ = ‖Complex.Gammaℝ ((a : ℂ) + I * (t : ℂ))‖ := hnorm.symm

/-- Lower bound for the archimedean gamma factor in the critical strip:
`C·exp(-(π/2)|t|) ≤ |γ(σ + I t)|` for `0 < σ < 1`, all real `t`. -/
theorem norm_gammaFactor_lower_bound (χ : DirichletCharacter ℂ N) {σ : ℝ}
    (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ,
      C * Real.exp (-(Real.pi / 2) * |t|) ≤ ‖χ.gammaFactor (σ + I * (t : ℂ))‖ := by
  rcases χ.even_or_odd with hEven | hOdd
  · -- even character: gammaFactor s = Gammaℝ s
    have hb := norm_Gammaℝ_lower_bound_line (a := σ) hσ0 (by nlinarith)
    rcases hb with ⟨C, hCpos, hCbody⟩
    refine ⟨C, hCpos, ?_⟩
    intro t
    rw [hEven.gammaFactor_def]
    exact hCbody t
  · -- odd character: gammaFactor s = Gammaℝ (s + 1)
    have hb := norm_Gammaℝ_lower_bound_line (a := σ + 1) (by linarith) (by linarith)
    rcases hb with ⟨C, hCpos, hCbody⟩
    refine ⟨C, hCpos, ?_⟩
    intro t
    rw [hOdd.gammaFactor_def]
    have harg : ((σ : ℂ) + I * (t : ℂ)) + 1 = ((σ + 1 : ℝ) : ℂ) + I * (t : ℂ) := by
      apply Complex.ext <;> simp
    rw [harg]
    exact hCbody t

end PL.GammaFactorLower


/-!
# Polynomial bounds for Deligne's real Gamma factor `Gammaℝ` (roadmap item [3])

This file upgrades the complex-`Γ` Stirling layer
(`PL.GammaDecay.gamma_norm_decay` / `gamma_norm_lower`:

* upper:  `|Γ(σ + I t)| ≤ C_σ · (1+|t|)^σ · e^{-π|t|/2}`   for `0 < σ`;
* lower:  `c_σ · (1+|t|)^{σ-1} · e^{-π|t|/2} ≤ |Γ(σ + I t)|` for `0 < σ < 1`)

to the **archimedean factor** `Complex.Gammaℝ s = π^{-s/2}·Γ(s/2)` used by Mathlib's
`DirichletCharacter.gammaFactor`.  The point is bounds whose dependence on the
*imaginary part* is **polynomial in `(1+|t|)`** (with the matching exponential decay
`e^{-π|t|/4}`), rather than the crude *uniform* bounds that hide `t`-dependence in an
arbitrary constant.

## Main results

* `gammaℝ_norm_upper`:  for `0 < a` there is `C > 0` with
  `‖Gammaℝ (a + I t)‖ ≤ C · (1+|t|)^{a/2} · e^{-(π/4)|t|}` for all real `t`.
* `gammaℝ_norm_lower`:  for `0 < a < 2` there is `c > 0` with
  `c · (1+|t|)^{a/2 - 1} · e^{-(π/4)|t|} ≤ ‖Gammaℝ (a + I t)‖` for all real `t`.
* `gammaFactor_ratio_poly`:
  for a character `χ` and `0 < σ < 1`,
  `‖γ(1 - s)/γ(s)‖ ≤ C · (1+|t|)^{3/2 - σ}` for `s = σ + I t`.

## Proof strategy (use `Submission/GammaFactorLower.lean` as a template)

`GammaFactorLower.norm_Gammaℝ_lower_bound_line` shows the standard dance:

```
have harg : ((a : ℂ) + I * (t : ℂ)) / 2 = ((a / 2 : ℝ) : ℂ) + I * (((t / 2 : ℝ) : ℂ)) := by
  apply Complex.ext <;> simp
have hnorm : ‖Complex.Gammaℝ ((a : ℂ) + I * (t : ℂ))‖
    = (Real.pi ^ (-a / 2)) * ‖Complex.Gamma (((a : ℂ) + I * (t : ℂ)) / 2)‖ := by
  rw [Complex.Gammaℝ_def, Complex.norm_mul]
  rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
  congr 1
  simp
```

For the **upper** bound apply `GammaDecay.gamma_norm_decay (a / 2)` at the real argument
`t / 2`:

`‖Γ((a:ℂ)+I*(t:ℂ))/2‖ = ‖Γ(a/2 + I(t/2))‖ ≤ C(1+|t/2|)^(a/2) · e^{-(π/2)|t/2|}`
`= C(1+|t/2|)^(a/2) · e^{-(π/4)|t|}`

and use `(1 + |t|/2) ≤ (1 + |t|)` with nonneg exponent `a/2 ≥ 0`
(`Real.rpow_le_rpow_of_exponent_le` needs the base `≥ 1`, or prove directly that
`x ≤ y → x^p ≤ y^p` for `0 ≤ x`, `0 ≤ p` via `Real.rpow_le_rpow hx hy hp`).

For the **lower** bound apply `GammaDecay.gamma_norm_lower (a/2)` (requires `0 < a/2 < 1`,
i.e. `0 < a < 2`) at `t / 2`:

`c(1+|t/2|)^(a/2-1) · e^{-(π/4)|t|} ≤ ‖Γ(a/2 + I(t/2))‖`,

then `(1+|t|)^(a/2-1) ≤ (1+|t/2|)^(a/2-1)` needs care: for the exponent `p = a/2 - 1 < 0`,
`Real.rpow_le_rpow_of_nonpos hpos hle hp` gives exactly `(1+|t|)^p ≤ (1+|t/2|)^p`
(`x ≤ y → y^p ≤ x^p` for `0 < x` and `p ≤ 0`).

The **ratio** results (`gammaℝ_ratio_even`, `gammaℝ_ratio_odd`, `gammaFactor_ratio_poly`):
bound numerator by the upper bound at real part `1-σ` (resp. `2-σ`) with the argument `-t`,
bound the denominator from below at real part `σ` (resp. `σ+1`), then divide:
`‖a/b‖ = ‖a‖/‖b‖` (`norm_div`), `div_le_div₀`, and the exponential factors `e^{-(π/4)|t|}`
cancel.  Exponent arithmetic:
`(1-σ)/2 - (σ/2-1) = 3/2 - σ` and `(2-σ)/2 - ((σ+1)/2-1) = 3/2 - σ` (ring).
-/

open Complex Filter MeasureTheory Set DirichletCharacter
open scoped Real

set_option autoImplicit false

namespace PL.GammaℝPoly

/-- **Upper bound with polynomial growth and exponential decay**:
for `0 < a`, `‖Gammaℝ (a + I t)‖ ≤ C·(1+|t|)^{a/2}·e^{-(π/4)|t|}` uniformly in real `t`. -/
theorem gammaℝ_norm_upper (a : ℝ) (ha : 0 < a) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ,
      ‖Complex.Gammaℝ ((a : ℂ) + I * (t : ℂ))‖ ≤
        C * (1 + |t|) ^ (a / 2) * Real.exp (-(Real.pi / 4) * |t|) := by
  have hA : 0 < Real.pi ^ (-a / 2) := Real.rpow_pos_of_pos Real.pi_pos _
  have hha0 : 0 < a / 2 := by positivity
  obtain ⟨C0, hC0pos, hC0⟩ := PL.GammaDecay.gamma_norm_decay (a / 2) hha0
  refine ⟨Real.pi ^ (-a / 2) * C0, mul_pos hA hC0pos, ?_⟩
  intro t
  have hAbsDiv : |t / 2| = |t| / 2 := by
    rw [abs_div]
    norm_num
  have hExp : -(Real.pi / 2) * |t / 2| = -(Real.pi / 4) * |t| := by
    rw [hAbsDiv]
    ring
  have hAbs : |t / 2| ≤ |t| := by
    rw [hAbsDiv]
    have ht : 0 ≤ |t| := abs_nonneg t
    nlinarith
  have hpoly : (1 + |t / 2|) ^ (a / 2) ≤ (1 + |t|) ^ (a / 2) := by
    refine Real.rpow_le_rpow ?_ ?_ ?_
    · positivity
    · linarith
    · positivity
  have harg : ((a : ℂ) + I * (t : ℂ)) / 2 = ((a / 2 : ℝ) : ℂ) + I * (((t / 2 : ℝ) : ℂ)) := by
    apply Complex.ext <;> simp
  have hΓu : ‖Complex.Gamma (((a / 2 : ℝ) : ℂ) + I * (((t / 2 : ℝ) : ℂ)))‖ ≤
      C0 * (1 + |t / 2|) ^ (a / 2) * Real.exp (-(Real.pi / 2) * |t / 2|) := hC0 (t / 2)
  have hΓz : ‖Complex.Gamma (((a : ℂ) + I * (t : ℂ)) / 2)‖ ≤
      C0 * (1 + |t / 2|) ^ (a / 2) * Real.exp (-(Real.pi / 2) * |t / 2|) := by
    simpa [harg] using hΓu
  have hΓexp : ‖Complex.Gamma (((a : ℂ) + I * (t : ℂ)) / 2)‖ ≤
      C0 * (1 + |t / 2|) ^ (a / 2) * Real.exp (-(Real.pi / 4) * |t|) := by
    simpa [hExp] using hΓz
  have hExpPos : 0 ≤ Real.exp (-(Real.pi / 4) * |t|) := le_of_lt (Real.exp_pos _)
  have hΓ' : ‖Complex.Gamma (((a : ℂ) + I * (t : ℂ)) / 2)‖ ≤
      C0 * (1 + |t|) ^ (a / 2) * Real.exp (-(Real.pi / 4) * |t|) := by
    calc
      ‖Complex.Gamma (((a : ℂ) + I * (t : ℂ)) / 2)‖
          ≤ C0 * (1 + |t / 2|) ^ (a / 2) * Real.exp (-(Real.pi / 4) * |t|) := hΓexp
      _ ≤ C0 * (1 + |t|) ^ (a / 2) * Real.exp (-(Real.pi / 4) * |t|) := by
        have h1 : C0 * (1 + |t / 2|) ^ (a / 2)
            ≤ C0 * (1 + |t|) ^ (a / 2) := by
          exact mul_le_mul_of_nonneg_left hpoly (le_of_lt hC0pos)
        exact mul_le_mul_of_nonneg_right h1 hExpPos
  have hnorm : ‖Complex.Gammaℝ ((a : ℂ) + I * (t : ℂ))‖
      = (Real.pi ^ (-a / 2)) * ‖Complex.Gamma (((a : ℂ) + I * (t : ℂ)) / 2)‖ := by
    rw [Complex.Gammaℝ_def, Complex.norm_mul]
    rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
    congr 1
    simp
  calc
    ‖Complex.Gammaℝ ((a : ℂ) + I * (t : ℂ))‖
        = (Real.pi ^ (-a / 2)) * ‖Complex.Gamma (((a : ℂ) + I * (t : ℂ)) / 2)‖ := hnorm
    _ ≤ (Real.pi ^ (-a / 2)) * (C0 * (1 + |t|) ^ (a / 2)
          * Real.exp (-(Real.pi / 4) * |t|)) := by
      exact mul_le_mul_of_nonneg_left hΓ' (le_of_lt hA)
    _ = (Real.pi ^ (-a / 2) * C0) * (1 + |t|) ^ (a / 2)
          * Real.exp (-(Real.pi / 4) * |t|) := by ring

/-- **Lower bound**: for `0 < a < 2`,
`c·(1+|t|)^{a/2-1}·e^{-(π/4)|t|} ≤ ‖Gammaℝ (a + I t)‖` uniformly in real `t`. -/
theorem gammaℝ_norm_lower (a : ℝ) (ha0 : 0 < a) (ha2 : a < 2) :
    ∃ c : ℝ, 0 < c ∧ ∀ t : ℝ,
      c * (1 + |t|) ^ (a / 2 - 1) * Real.exp (-(Real.pi / 4) * |t|) ≤
        ‖Complex.Gammaℝ ((a : ℂ) + I * (t : ℂ))‖ := by
  have hA : 0 < Real.pi ^ (-a / 2) := Real.rpow_pos_of_pos Real.pi_pos _
  have hha0 : 0 < a / 2 := by positivity
  have hha1 : a / 2 < 1 := by nlinarith
  obtain ⟨c0, hc0pos, hc0⟩ :=
    PL.GammaDecay.gamma_norm_lower (a / 2) hha0 hha1
  refine ⟨Real.pi ^ (-a / 2) * c0, mul_pos hA hc0pos, ?_⟩
  intro t
  have hAbsDiv : |t / 2| = |t| / 2 := by
    rw [abs_div]
    norm_num
  have hExp : -(Real.pi / 2) * |t / 2| = -(Real.pi / 4) * |t| := by
    rw [hAbsDiv]
    ring
  have hAbs : |t / 2| ≤ |t| := by
    rw [hAbsDiv]
    have ht : 0 ≤ |t| := abs_nonneg t
    nlinarith
  have hbases : 1 + |t / 2| ≤ 1 + |t| := by linarith
  have hp : a / 2 - 1 ≤ 0 := by nlinarith
  have hpoly : (1 + |t|) ^ (a / 2 - 1) ≤ (1 + |t / 2|) ^ (a / 2 - 1) := by
    exact Real.rpow_le_rpow_of_nonpos (by positivity : 0 < 1 + |t / 2|) hbases hp
  have harg : ((a : ℂ) + I * (t : ℂ)) / 2 = ((a / 2 : ℝ) : ℂ) + I * (((t / 2 : ℝ) : ℂ)) := by
    apply Complex.ext <;> simp
  have hΓu : c0 * (1 + |t / 2|) ^ (a / 2 - 1) * Real.exp (-(Real.pi / 2) * |t / 2|) ≤
      ‖Complex.Gamma (((a / 2 : ℝ) : ℂ) + I * (((t / 2 : ℝ) : ℂ)))‖ := hc0 (t / 2)
  have hΓz : c0 * (1 + |t / 2|) ^ (a / 2 - 1) * Real.exp (-(Real.pi / 2) * |t / 2|) ≤
      ‖Complex.Gamma (((a : ℂ) + I * (t : ℂ)) / 2)‖ := by
    simpa [harg] using hΓu
  have hΓexp : c0 * (1 + |t / 2|) ^ (a / 2 - 1) * Real.exp (-(Real.pi / 4) * |t|) ≤
      ‖Complex.Gamma (((a : ℂ) + I * (t : ℂ)) / 2)‖ := by
    simpa [hExp] using hΓz
  have hExpPos : 0 ≤ Real.exp (-(Real.pi / 4) * |t|) := le_of_lt (Real.exp_pos _)
  have hΓ' : c0 * (1 + |t|) ^ (a / 2 - 1) * Real.exp (-(Real.pi / 4) * |t|) ≤
      c0 * (1 + |t / 2|) ^ (a / 2 - 1) * Real.exp (-(Real.pi / 4) * |t|) := by
    have h1 : c0 * (1 + |t|) ^ (a / 2 - 1)
        ≤ c0 * (1 + |t / 2|) ^ (a / 2 - 1) := by
      exact mul_le_mul_of_nonneg_left hpoly (le_of_lt hc0pos)
    exact mul_le_mul_of_nonneg_right h1 hExpPos
  have hnorm : ‖Complex.Gammaℝ ((a : ℂ) + I * (t : ℂ))‖
      = (Real.pi ^ (-a / 2)) * ‖Complex.Gamma (((a : ℂ) + I * (t : ℂ)) / 2)‖ := by
    rw [Complex.Gammaℝ_def, Complex.norm_mul]
    rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
    congr 1
    simp
  calc
    (Real.pi ^ (-a / 2) * c0) * (1 + |t|) ^ (a / 2 - 1)
        * Real.exp (-(Real.pi / 4) * |t|)
        = Real.pi ^ (-a / 2) * (c0 * (1 + |t|) ^ (a / 2 - 1)
            * Real.exp (-(Real.pi / 4) * |t|)) := by ring
    _ ≤ Real.pi ^ (-a / 2) * (c0 * (1 + |t / 2|) ^ (a / 2 - 1)
          * Real.exp (-(Real.pi / 4) * |t|)) := by
      exact mul_le_mul_of_nonneg_left hΓ' (le_of_lt hA)
    _ ≤ Real.pi ^ (-a / 2) * ‖Complex.Gamma (((a : ℂ) + I * (t : ℂ)) / 2)‖ := by
      exact mul_le_mul_of_nonneg_left hΓexp (le_of_lt hA)
    _ = ‖Complex.Gammaℝ ((a : ℂ) + I * (t : ℂ))‖ := hnorm.symm

end PL.GammaℝPoly


/-!
# Polynomial gamma-ratio bounds (from Submission/GammaℝPoly.lean)

The ratio results `gammaℝ_ratio_even`, `gammaℝ_ratio_odd`, `gammaFactor_ratio_poly`:
bound numerator by the upper bound at real part `1-σ` (resp. `2-σ`) with the argument `-t`,
bound the denominator from below at real part `σ` (resp. `σ+1`), then divide:
`‖a/b‖ = ‖a‖/‖b‖` (`norm_div`), `div_le_div₀`, and the exponential factors `e^{-(π/4)|t|}`
cancel.  Exponent arithmetic:
`(1-σ)/2 - (σ/2-1) = 3/2 - σ` and `(2-σ)/2 - ((σ+1)/2-1) = 3/2 - σ` (ring).
-/

open Complex Filter MeasureTheory Set DirichletCharacter
open scoped Real

set_option autoImplicit false

namespace PL.GammaℝPoly

/-- Even-parity gamma ratio: `‖Gammaℝ (1 - s) / Gammaℝ s‖ ≤ C·(1+|t|)^{3/2-σ}`
for `s = σ + I t`, `0 < σ < 1`. -/
lemma gammaℝ_ratio_even (σ : ℝ) (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ,
      ‖Complex.Gammaℝ (1 - ((σ : ℂ) + I * (t : ℂ))) / Complex.Gammaℝ ((σ : ℂ) + I * (t : ℂ))‖ ≤
        C * (1 + |t|) ^ (3 / 2 - σ) := by
  obtain ⟨Cu, hCu, hNu⟩ := PL.GammaℝPoly.gammaℝ_norm_upper (1 - σ) (by linarith)
  obtain ⟨cl, hcl, hNl⟩ := PL.GammaℝPoly.gammaℝ_norm_lower σ hσ0 (by linarith)
  refine ⟨Cu / cl, div_pos hCu hcl, ?_⟩
  intro t
  let s : ℂ := (σ : ℂ) + I * (t : ℂ)
  let B : ℝ := 1 + |t|
  let E : ℝ := Real.exp (-(Real.pi / 4) * |t|)
  let p : ℝ := (1 - σ) / 2
  let q : ℝ := σ / 2 - 1
  have hBpos : 0 < B := by dsimp [B]; positivity
  have hEpos : 0 < E := by dsimp [E]; exact Real.exp_pos _
  have hnum_arg : 1 - s = ((1 - σ : ℝ) : ℂ) + I * ((-t : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [s]
  have hnum : ‖Complex.Gammaℝ (1 - s)‖ ≤ Cu * B ^ p * E := by
    simpa [hnum_arg, B, E, p, abs_neg] using hNu (-t)
  have hden : cl * B ^ q * E ≤ ‖Complex.Gammaℝ s‖ := by
    simpa [s, B, E, q] using hNl t
  have hnum_nonneg : 0 ≤ Cu * B ^ p * E := by
    have hBp : 0 ≤ B ^ p := le_of_lt (Real.rpow_pos_of_pos hBpos p)
    positivity
  have hden_pos : 0 < cl * B ^ q * E := by
    have hBq : 0 < B ^ q := Real.rpow_pos_of_pos hBpos q
    positivity
  have hpq : p - q = 3 / 2 - σ := by dsimp [p, q]; ring
  have hEq : (Cu * B ^ p * E) / (cl * B ^ q * E) = (Cu / cl) * B ^ (3 / 2 - σ) := by
    have hEne : E ≠ 0 := ne_of_gt hEpos
    have hBqE_pos : 0 < B ^ q * E := mul_pos (Real.rpow_pos_of_pos hBpos q) hEpos
    have hclne : cl ≠ 0 := ne_of_gt hcl
    calc
      (Cu * B ^ p * E) / (cl * B ^ q * E)
          = (Cu / cl) * ((B ^ p * E) / (B ^ q * E)) := by
            field_simp [hclne, hBqE_pos.ne']
      _ = (Cu / cl) * (B ^ p / B ^ q) := by
            congr 1
            field_simp [hEne]
      _ = (Cu / cl) * B ^ (p - q) := by
            congr 1
            exact (Real.rpow_sub hBpos p q).symm
      _ = (Cu / cl) * B ^ (3 / 2 - σ) := by rw [hpq]
  change ‖Complex.Gammaℝ (1 - s) / Complex.Gammaℝ s‖ ≤ (Cu / cl) * B ^ (3 / 2 - σ)
  calc
    ‖Complex.Gammaℝ (1 - s) / Complex.Gammaℝ s‖
        = ‖Complex.Gammaℝ (1 - s)‖ / ‖Complex.Gammaℝ s‖ := by rw [norm_div]
    _ ≤ (Cu * B ^ p * E) / ‖Complex.Gammaℝ s‖ := by
          exact div_le_div_of_nonneg_right hnum (norm_nonneg _)
    _ ≤ (Cu * B ^ p * E) / (cl * B ^ q * E) := by
          exact div_le_div_of_nonneg_left hnum_nonneg hden_pos hden
    _ = (Cu / cl) * B ^ (3 / 2 - σ) := hEq

/-- Odd-parity gamma ratio: `‖Gammaℝ (2 - s) / Gammaℝ (s + 1)‖ ≤ C·(1+|t|)^{3/2-σ}`
for `s = σ + I t`, `0 < σ < 1`. -/
lemma gammaℝ_ratio_odd (σ : ℝ) (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ,
      ‖Complex.Gammaℝ (2 - ((σ : ℂ) + I * (t : ℂ))) /
          Complex.Gammaℝ (((σ : ℂ) + I * (t : ℂ)) + 1)‖ ≤
        C * (1 + |t|) ^ (3 / 2 - σ) := by
  obtain ⟨Cu, hCu, hNu⟩ := PL.GammaℝPoly.gammaℝ_norm_upper (2 - σ) (by linarith)
  obtain ⟨cl, hcl, hNl⟩ := PL.GammaℝPoly.gammaℝ_norm_lower (σ + 1) (by linarith) (by linarith)
  refine ⟨Cu / cl, div_pos hCu hcl, ?_⟩
  intro t
  let s : ℂ := (σ : ℂ) + I * (t : ℂ)
  let B : ℝ := 1 + |t|
  let E : ℝ := Real.exp (-(Real.pi / 4) * |t|)
  let p : ℝ := (2 - σ) / 2
  let q : ℝ := (σ + 1) / 2 - 1
  have hBpos : 0 < B := by dsimp [B]; positivity
  have hEpos : 0 < E := by dsimp [E]; exact Real.exp_pos _
  have hnum_arg : 2 - s = ((2 - σ : ℝ) : ℂ) + I * ((-t : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [s]
  have hden_arg : s + 1 = ((σ + 1 : ℝ) : ℂ) + I * (t : ℂ) := by
    apply Complex.ext <;> simp [s]
  have hnum : ‖Complex.Gammaℝ (2 - s)‖ ≤ Cu * B ^ p * E := by
    simpa [hnum_arg, B, E, p, abs_neg] using hNu (-t)
  have hden : cl * B ^ q * E ≤ ‖Complex.Gammaℝ (s + 1)‖ := by
    simpa [hden_arg, B, E, q] using hNl t
  have hnum_nonneg : 0 ≤ Cu * B ^ p * E := by
    have hBp : 0 ≤ B ^ p := le_of_lt (Real.rpow_pos_of_pos hBpos p)
    positivity
  have hden_pos : 0 < cl * B ^ q * E := by
    have hBq : 0 < B ^ q := Real.rpow_pos_of_pos hBpos q
    positivity
  have hpq : p - q = 3 / 2 - σ := by dsimp [p, q]; ring
  have hEq : (Cu * B ^ p * E) / (cl * B ^ q * E) = (Cu / cl) * B ^ (3 / 2 - σ) := by
    have hEne : E ≠ 0 := ne_of_gt hEpos
    have hBqE_pos : 0 < B ^ q * E := mul_pos (Real.rpow_pos_of_pos hBpos q) hEpos
    have hclne : cl ≠ 0 := ne_of_gt hcl
    calc
      (Cu * B ^ p * E) / (cl * B ^ q * E)
          = (Cu / cl) * ((B ^ p * E) / (B ^ q * E)) := by
            field_simp [hclne, hBqE_pos.ne']
      _ = (Cu / cl) * (B ^ p / B ^ q) := by
            congr 1
            field_simp [hEne]
      _ = (Cu / cl) * B ^ (p - q) := by
            congr 1
            exact (Real.rpow_sub hBpos p q).symm
      _ = (Cu / cl) * B ^ (3 / 2 - σ) := by rw [hpq]
  change ‖Complex.Gammaℝ (2 - s) / Complex.Gammaℝ (s + 1)‖ ≤ (Cu / cl) * B ^ (3 / 2 - σ)
  calc
    ‖Complex.Gammaℝ (2 - s) / Complex.Gammaℝ (s + 1)‖
        = ‖Complex.Gammaℝ (2 - s)‖ / ‖Complex.Gammaℝ (s + 1)‖ := by rw [norm_div]
    _ ≤ (Cu * B ^ p * E) / ‖Complex.Gammaℝ (s + 1)‖ := by
          exact div_le_div_of_nonneg_right hnum (norm_nonneg _)
    _ ≤ (Cu * B ^ p * E) / (cl * B ^ q * E) := by
          exact div_le_div_of_nonneg_left hnum_nonneg hden_pos hden
    _ = (Cu / cl) * B ^ (3 / 2 - σ) := hEq

/-- **Polynomial gamma-ratio bound for a Dirichlet character** (both parities):
for `0 < σ < 1`, `‖γ(1 - s)/γ(s)‖ ≤ C·(1+|t|)^{3/2-σ}` where `s = σ + I t`
and `γ = χ.gammaFactor`.  Split on `χ.even_or_odd` and use
`DirichletCharacter.Even.gammaFactor_def` / `.Odd.gammaFactor_def`. -/
theorem gammaFactor_ratio_poly {N : ℕ} (χ : DirichletCharacter ℂ N) {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ,
      ‖χ.gammaFactor (1 - ((σ : ℂ) + I * (t : ℂ))) /
          χ.gammaFactor ((σ : ℂ) + I * (t : ℂ))‖ ≤
        C * (1 + |t|) ^ (3 / 2 - σ) := by
  rcases χ.even_or_odd with hχe | hχo
  · obtain ⟨C, hCpos, hC⟩ := gammaℝ_ratio_even σ hσ0 hσ1
    refine ⟨C, hCpos, ?_⟩
    intro t
    simpa [DirichletCharacter.Even.gammaFactor_def hχe] using hC t
  · obtain ⟨C, hCpos, hC⟩ := gammaℝ_ratio_odd σ hσ0 hσ1
    refine ⟨C, hCpos, ?_⟩
    intro t
    have harg : 1 - ((σ : ℂ) + I * (t : ℂ)) + 1 =
        2 - ((σ : ℂ) + I * (t : ℂ)) := by
      apply Complex.ext
      · simp
        ring
      · simp
    simpa [DirichletCharacter.Odd.gammaFactor_def hχo, harg] using hC t

end PL.GammaℝPoly


/-!
# Trivial (absolute-convergence) bounds for L-functions on vertical lines Re s > 1

The first bounds needed on the road to the Weyl bound are the **trivial bounds** from
absolute convergence to the right of `Re s = 1`: for fixed `1 < σ` the value of
`|L(σ + I t, χ)|` is bounded **uniformly in `t`**:

`|L(σ + I t, χ)| ≤ B(σ)`   for all real `t`.

(The bound is on a vertical *line* `Re s = σ`; it genuinely depends on `σ` and tends to
`∞` as `σ → ∞`, so there is no half-plane version.)  The archimedean gamma-factor bounds
(`Submission/GammaVertical.lean`) upgrade this to the completed L-function `Λ = γ·L`, and
the functional equation (`Submission/RootNumber.lean`) reflects these to vertical lines to
the left of `Re s = 0`.

## Main results

* `norm_LFunction_le_of_re_ge`: `|L(s, χ)| ≤ B(σ)` for all `s` with `σ ≤ Re s`, `σ > 1`.
* `norm_completedLFunction_vertical`: `|Λ(σ + I t, χ)| ≤ B(σ, χ)` uniformly in `t`, `σ > 1`.
-/

open Complex DirichletCharacter Filter MeasureTheory Set
open scoped Real

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace PL.TrivialBounds

variable {N : ℕ} [NeZero N]

omit [NeZero N] in
/-- `‖χ n‖ ≤ 1` for natural arguments. -/
lemma norm_char_nat_le_one (χ : DirichletCharacter ℂ N) (n : ℕ) : ‖χ n‖ ≤ 1 := by
  exact χ.norm_le_one (n : ZMod N)

/-- For `1 < σ`, `|L(s, χ)|` is bounded on `{s | σ ≤ Re s}` by the tail sum of `n^(-σ)`. -/
theorem norm_LFunction_le_of_re_ge (χ : DirichletCharacter ℂ N) {σ : ℝ} (hσ : 1 < σ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ {s : ℂ}, σ ≤ s.re → ‖DirichletCharacter.LFunction χ s‖ ≤ B := by
  let g : ℕ → ℝ := fun n => ‖LSeries.term (fun m : ℕ => χ (m : ZMod N)) (σ : ℂ) n‖
  have hgsum : Summable g := by
    have hs : 1 < (σ : ℂ).re := by simpa using hσ
    have hS : LSeriesSummable (fun n : ℕ => χ (n : ZMod N)) (σ : ℂ) :=
      DirichletCharacter.LSeriesSummable_of_one_lt_re χ hs
    exact (summable_norm_iff).2 hS
  let B : ℝ := ∑' n : ℕ, g n
  refine ⟨B, ?_, ?_⟩
  · dsimp [B]
    exact tsum_nonneg (fun n => norm_nonneg _)
  · intro s hsσ
    have hs : 1 < s.re := lt_of_lt_of_le hσ hsσ
    have hS : LSeriesSummable (fun n : ℕ => χ (n : ZMod N)) s :=
      DirichletCharacter.LSeriesSummable_of_one_lt_re χ hs
    calc
      ‖DirichletCharacter.LFunction χ s‖ = ‖LSeries (fun n : ℕ => χ (n : ZMod N)) s‖ := by
            rw [DirichletCharacter.LFunction_eq_LSeries χ hs]
      _ ≤ ∑' n : ℕ, ‖LSeries.term (fun m : ℕ => χ (m : ZMod N)) s n‖ := by
            exact norm_tsum_le_tsum_norm (summable_norm_iff.2 hS)
      _ ≤ ∑' n : ℕ, g n := by
            exact Summable.tsum_le_tsum
              (fun n => LSeries.norm_term_le_of_re_le_re (fun m : ℕ => χ (m : ZMod N)) hsσ n)
              (summable_norm_iff.2 hS) hgsum
      _ = B := by rfl

/-- `|L(σ + I t, χ)|` is bounded uniformly in `t` for `1 < σ`. -/
theorem norm_LFunction_vertical (χ : DirichletCharacter ℂ N) {σ : ℝ} (hσ : 1 < σ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t : ℝ, ‖DirichletCharacter.LFunction χ (σ + I * (t : ℂ))‖ ≤ B := by
  rcases norm_LFunction_le_of_re_ge χ hσ with ⟨B, hB0, hB⟩
  refine ⟨B, hB0, ?_⟩
  intro t
  have hre : σ ≤ (σ + I * (t : ℂ)).re := by simp
  exact hB hre

/-- The archimedean gamma factor is bounded uniformly in `t` on the vertical line
`Re s = σ` for `σ > 1`. -/
lemma gammaFactor_norm_vertical (χ : DirichletCharacter ℂ N) {σ : ℝ} (hσ : 1 < σ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ t : ℝ, ‖χ.gammaFactor (σ + I * (t : ℂ))‖ ≤ A := by
  rcases χ.even_or_odd with hχ | hχ
  · let A : ℝ := ‖Complex.Gammaℝ ((σ : ℝ) : ℂ)‖
    refine ⟨A, norm_nonneg _, ?_⟩
    intro t
    rw [hχ.gammaFactor_def]
    have hs : 0 < (σ + I * (t : ℂ)).re := by simp; linarith
    calc
      ‖Complex.Gammaℝ (σ + I * (t : ℂ))‖ ≤ ‖Complex.Gammaℝ ((σ : ℝ) : ℂ)‖ := by
            simpa using GammaVertical.norm_Gammaℝ_le_norm_Gammaℝ_re (σ + I * (t : ℂ)) hs
      _ = A := by rfl
  · let A : ℝ := ‖Complex.Gammaℝ (((σ + 1 : ℝ) : ℂ))‖
    refine ⟨A, norm_nonneg _, ?_⟩
    intro t
    rw [hχ.gammaFactor_def]
    have hs : 0 < (σ + 1 + I * (t : ℂ)).re := by simp; linarith
    have hle : ‖Complex.Gammaℝ (σ + 1 + I * (t : ℂ))‖ ≤ A := by
      dsimp [A]
      simpa using GammaVertical.norm_Gammaℝ_le_norm_Gammaℝ_re (σ + 1 + I * (t : ℂ)) hs
    -- rewrite (σ + I t) + 1 into σ + 1 + I t
    simpa [add_assoc, add_comm, add_left_comm] using hle

/-- `|Λ(σ + I t, χ)|` is bounded uniformly in `t` for `1 < σ`. -/
theorem norm_completedLFunction_vertical (χ : DirichletCharacter ℂ N) {σ : ℝ} (hσ : 1 < σ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t : ℝ, ‖DirichletCharacter.completedLFunction χ (σ + I * (t : ℂ))‖ ≤ B := by
  rcases norm_LFunction_vertical χ hσ with ⟨B, hB0, hB⟩
  rcases gammaFactor_norm_vertical χ hσ with ⟨A, hA0, hA⟩
  let C : ℝ := A * B
  refine ⟨C, mul_nonneg hA0 hB0, ?_⟩
  intro t
  have hs0 : 0 < (σ + I * (t : ℂ)).re := by simp; linarith
  have hz : σ + I * (t : ℂ) ≠ 0 := by
    intro hzero
    have hre := congrArg Complex.re hzero
    simp at hre
    linarith
  have hγne : χ.gammaFactor (σ + I * (t : ℂ)) ≠ 0 :=
    PL.AFE.Structural.gammaFactor_ne_zero_of_zero_lt_re χ hs0
  have hEq : DirichletCharacter.completedLFunction χ (σ + I * (t : ℂ)) =
      DirichletCharacter.LFunction χ (σ + I * (t : ℂ)) * χ.gammaFactor (σ + I * (t : ℂ)) := by
    have h := LFunction_eq_completed_div_gammaFactor χ (σ + I * (t : ℂ)) (Or.inl hz)
    calc
      DirichletCharacter.completedLFunction χ (σ + I * (t : ℂ))
          = (DirichletCharacter.completedLFunction χ (σ + I * (t : ℂ)) / χ.gammaFactor (σ + I * (t : ℂ)))
              * χ.gammaFactor (σ + I * (t : ℂ)) := (div_mul_cancel₀ _ hγne).symm
      _ = DirichletCharacter.LFunction χ (σ + I * (t : ℂ)) * χ.gammaFactor (σ + I * (t : ℂ)) := by rw [h]
  calc
    ‖DirichletCharacter.completedLFunction χ (σ + I * (t : ℂ))‖
        = ‖DirichletCharacter.LFunction χ (σ + I * (t : ℂ)) * χ.gammaFactor (σ + I * (t : ℂ))‖ := by rw [hEq]
    _ ≤ ‖DirichletCharacter.LFunction χ (σ + I * (t : ℂ))‖ * ‖χ.gammaFactor (σ + I * (t : ℂ))‖ :=
          norm_mul_le _ _
    _ ≤ B * A := by
          exact mul_le_mul (hB t) (hA t) (norm_nonneg _) hB0
    _ = A * B := by ring
    _ = C := by rfl

/-- `|Λ(σ + I t, χ)|` is bounded uniformly in `t` for `σ < 0`, for primitive `χ`
(via the functional equation reflecting to `Re = 1 - σ > 1`). -/
theorem norm_completedLFunction_vertical_left {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive)
    {σ : ℝ} (hσ : σ < 0) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t : ℝ, ‖DirichletCharacter.completedLFunction χ (σ + I * (t : ℂ))‖ ≤ B := by
  let σ' : ℝ := 1 - σ
  have hσ' : 1 < σ' := by linarith
  -- completed L of χ⁻¹ is bounded on Re = σ'
  rcases norm_completedLFunction_vertical (χ := χ⁻¹) hσ' with ⟨B1, hB10, hB1⟩
  have hχinv : (χ⁻¹).IsPrimitive := PL.RootNumber.isPrimitive_inv hχ
  let B : ℝ := ((N : ℝ) ^ (1 / 2 - σ)) * ‖χ.rootNumber‖ * B1
  refine ⟨B, ?_, ?_⟩
  · dsimp [B]
    exact mul_nonneg (mul_nonneg (Real.rpow_nonneg (by positivity : 0 ≤ (N : ℝ)) _) (norm_nonneg _)) hB10
  · intro t
    have hEq := PL.AFE.Structural.completedLFunction_eq_rootNumber_mul χ hχ (σ + I * (t : ℂ))
    -- completedLFunction_eq_rootNumber_mul: DirichletCharacter.completedLFunction χ s = (N:ℂ)^(1/2 - s) * rootNumber * DirichletCharacter.completedLFunction (χ⁻¹) (1 - s)
    calc
      ‖DirichletCharacter.completedLFunction χ (σ + I * (t : ℂ))‖
          = ‖(N : ℂ) ^ (1 / 2 - (σ + I * (t : ℂ))) * χ.rootNumber * DirichletCharacter.completedLFunction (χ⁻¹) (1 - (σ + I * (t : ℂ)))‖ := by rw [hEq]
      _ ≤ ‖(N : ℂ) ^ (1 / 2 - (σ + I * (t : ℂ)))‖ * ‖χ.rootNumber‖ * ‖DirichletCharacter.completedLFunction (χ⁻¹) (1 - (σ + I * (t : ℂ)))‖ := by
            rw [mul_assoc]
            -- ‖a * (b * c)‖: need chain
            calc ‖(N : ℂ) ^ (1 / 2 - (σ + I * (t : ℂ))) * (χ.rootNumber * DirichletCharacter.completedLFunction (χ⁻¹) (1 - (σ + I * (t : ℂ))))‖
                ≤ ‖(N : ℂ) ^ (1 / 2 - (σ + I * (t : ℂ)))‖ * ‖χ.rootNumber * DirichletCharacter.completedLFunction (χ⁻¹) (1 - (σ + I * (t : ℂ)))‖ := norm_mul_le _ _
            _ ≤ ‖(N : ℂ) ^ (1 / 2 - (σ + I * (t : ℂ)))‖ * (‖χ.rootNumber‖ * ‖DirichletCharacter.completedLFunction (χ⁻¹) (1 - (σ + I * (t : ℂ)))‖) := by
                  exact mul_le_mul_of_nonneg_left (norm_mul_le _ _) (norm_nonneg _)
            _ = ‖(N : ℂ) ^ (1 / 2 - (σ + I * (t : ℂ)))‖ * ‖χ.rootNumber‖ * ‖DirichletCharacter.completedLFunction (χ⁻¹) (1 - (σ + I * (t : ℂ)))‖ := by ring
      _ ≤ ((N : ℝ) ^ (1 / 2 - σ)) * ‖χ.rootNumber‖ * B1 := by
            have hpow : ‖(N : ℂ) ^ (1 / 2 - (σ + I * (t : ℂ)))‖ = (N : ℝ) ^ (1 / 2 - σ) := by
              have hNpos : 0 < (N : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
              have hcast : (N : ℂ) = ((N : ℝ) : ℂ) := by norm_num
              rw [hcast]
              rw [Complex.norm_cpow_eq_rpow_re_of_pos hNpos]
              congr 1
              simp
            rw [hpow]
            -- completedL χ⁻¹ at 1 - σ - i t: re = 1 - σ = σ': = σ' + i(-t): match B1's statement (σ' + I * (u:ℂ))
            have harg : 1 - (σ + I * (t : ℂ)) = σ' + I * (-(t : ℂ)) := by
              dsimp [σ']
              apply Complex.ext <;> simp <;> ring
            have hval : DirichletCharacter.completedLFunction (χ⁻¹) (1 - (σ + I * (t : ℂ))) = DirichletCharacter.completedLFunction (χ⁻¹) (σ' + I * (-(t : ℂ))) := by
              exact congrArg (DirichletCharacter.completedLFunction (χ⁻¹)) harg
            have hb1t := hB1 (-t)
            have hle : ‖DirichletCharacter.completedLFunction (χ⁻¹) (1 - (σ + I * (t : ℂ)))‖ ≤ B1 := by
              rw [hval]
              simpa using hb1t
            have h1 : 0 ≤ (N : ℝ) ^ (1 / 2 - σ) := Real.rpow_nonneg (by positivity : 0 ≤ (N : ℝ)) _
            have h2 : 0 ≤ ‖χ.rootNumber‖ := norm_nonneg _
            calc
              (N : ℝ) ^ (1 / 2 - σ) * ‖χ.rootNumber‖ * ‖DirichletCharacter.completedLFunction (χ⁻¹) (1 - (σ + I * (t : ℂ)))‖
                  = (N : ℝ) ^ (1 / 2 - σ) * (‖χ.rootNumber‖ * ‖DirichletCharacter.completedLFunction (χ⁻¹) (1 - (σ + I * (t : ℂ)))‖) := by ring
              _ ≤ (N : ℝ) ^ (1 / 2 - σ) * (‖χ.rootNumber‖ * B1) := by
                    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hle h2) h1
              _ = ((N : ℝ) ^ (1 / 2 - σ)) * ‖χ.rootNumber‖ * B1 := by ring
      _ = B := by rfl
end PL.TrivialBounds


/-!
# Convergence of the truncated vertical integrals (T2, `T → ∞` passage)

Standalone fact for the `T → ∞` step: if `f : ℝ → ℂ` is (Bochner-)integrable, then the
integrals over the symmetric intervals `[-T, T]` converge to the full integral:

`Tendsto (fun T => ∫ y in -T..T, f y) atTop (𝓝 ∫ y, f y)`

This is an immediate instance of Mathlib's
`MeasureTheory.intervalIntegral_tendsto_integral` (improper-integral file) with
`a T = -T → atBot` and `b T = T → atTop`.
-/

open MeasureTheory Filter
open scoped Real Topology

set_option autoImplicit false

namespace PL.VertLimit

/-- `∫ y in -T..T, f y → ∫ y, f y` as `T → ∞`, for integrable `f : ℝ → ℂ`. -/
lemma tendsto_interval_vertical (f : ℝ → ℂ) (hf : Integrable f) :
    Tendsto (fun T : ℝ => ∫ y in -T..T, f y) atTop (𝓝 (∫ y : ℝ, f y)) := by
  exact intervalIntegral_tendsto_integral (a := fun T : ℝ => -T) (b := fun T : ℝ => T)
    (μ := volume) hf tendsto_neg_atTop_atBot tendsto_id

end PL.VertLimit


/-!
# The vertical-line identity (T2, `T → ∞` passage) — MACHINE-VERIFIED

From the finite-rectangle identity `AfeRectK.rectBoundary_K` we obtain, after the limit
`T → ∞`, the **vertical-line identity** for the Mellin integrand

`K(u) = x⁻ᵘ · Λ(s+u) · g(u)/u`:

`Λ(s) = (1/(2π)) · (∫_ℝ K(1+iy) dy − ∫_ℝ K(−1+iy) dy)`.

All statements below are **proved** (no `sorries`).  Structure:

1. Horizontal-segment machinery (`segmentK`, norm bounds, Gaussian envelope,
   `tendsto_horizontal_segment_top/neg`): the horizontal integrals `∫_{[-1,1]} K(x ± iT) dx`
   tend to `0` as `T → ∞`, under the strip-growth hypothesis `Λ_growth`
   (sub-exponential growth of `Λ` on `s.re-1 ≤ Re z ≤ s.re+1` — enough to beat the
   `exp(-T²)` decay of `g(u) = exp(u²)`).  Proving `Λ_growth` itself (without it as a
   hypothesis) remains the separate analytic task: it needs a polynomial-growth bound for
   `L` on the critical strip (not yet in Mathlib).
2. Vertical-line integrability: `norm_Lambda_right_line` / `norm_Lambda_left_line`
   (boundedness of `Λ` on the two lines `Re(s+u) = σ ± 1` from trivial bounds, resp. the
   functional equation for primitive `χ`), the Gaussian pointwise bounds
   `lineRight_norm_le` / `lineLeft_norm_le`, continuity and Bochner integrability
   (`integrable_lineRight` / `integrable_lineLeft`), and convergence of the truncated
   vertical integrals (`tendsto_truncated_right/left` via `VertLimit`).
3. Edge-connection lemmas (`botK_eq_segment`, `topK_eq_segment`,
   `rawRight_eq_lineRight`, `rawLeft_eq_lineLeft`) express the four rectangle edges in the
   forms used by the limit theorems.
4. **`vertical_line_identity`** — assemble the finite-`T` identity
   `rectBoundary_K = 2πi·Λ(s)` with the edge expansions and pass `T → ∞`, for a primitive
   nontrivial character `χ` with `0 < Re s < 1` under the hypothesis `Λ_growth χ s`.
-/

open MeasureTheory Filter DirichletCharacter
open PL.AFE
open scoped Real Topology 
set_option autoImplicit false

namespace PL.AfeVerticalLine

noncomputable section

variable {N : ℕ} [NeZero N]

open Complex

/-- The Mellin integrand on the vertical lines: `K_z(y) = x⁻ᵘΛ(s+u)g(u)/u`, `u = z + Iy`. -/
noncomputable def mellinLine (χ : DirichletCharacter ℂ N) (s : ℂ) (x : ℝ) (z : ℂ) (y : ℝ) : ℂ :=
  (x : ℂ) ^ (-(z + I * (y : ℂ))) * DirichletCharacter.completedLFunction χ (s + z + I * (y : ℂ))
    * smoothingFunction (z + I * (y : ℂ)) / (z + I * (y : ℂ))

/-- `K` on the line `Re u = 1`: `K(1 + Iy) = mellinLine χ s x 1 y`. -/
lemma mellinLine_eq_K_right (χ : DirichletCharacter ℂ N) (s : ℂ) (x : ℝ) (y : ℝ) :
    (x : ℂ) ^ (-(1 + I * (y : ℂ))) * DirichletCharacter.completedLFunction χ (s + 1 + I * (y : ℂ))
        * smoothingFunction (1 + I * (y : ℂ)) / (1 + I * (y : ℂ))
      = mellinLine χ s x 1 y := by
  rfl

/-- `K` on the line `Re u = -1`: `K(-1 + Iy) = mellinLine χ s x (-1) y`. -/
lemma mellinLine_eq_K_left (χ : DirichletCharacter ℂ N) (s : ℂ) (x : ℝ) (y : ℝ) :
    (x : ℂ) ^ (-(-1 + I * (y : ℂ))) * DirichletCharacter.completedLFunction χ (s - 1 + I * (y : ℂ))
        * smoothingFunction (-1 + I * (y : ℂ)) / (-1 + I * (y : ℂ))
      = mellinLine χ s x (-1) y := by
  rfl

/-- **Strip-growth hypothesis** for `Λ` on `s.re-1 ≤ Re z ≤ s.re+1`: sub-exponential
growth in the imaginary part.  (To be established from `TrivialBounds` together with a
polynomial-growth bound for `L` on the critical strip — a separate, well-identified
analytic lemma.) -/
def Λ_growth (χ : DirichletCharacter ℂ N) (s : ℂ) : Prop :=
  ∃ A B : ℝ, 0 < A ∧ 0 < B ∧
    ∀ z : ℂ, s.re - 1 ≤ z.re → z.re ≤ s.re + 1 →
      ‖DirichletCharacter.completedLFunction χ z‖ ≤ A * Real.exp (B * |z.im|)

noncomputable def segmentK (χ : DirichletCharacter ℂ N) (s : ℂ) (x0 : ℝ) (T0 x : ℝ) : ℂ :=
  (x0 : ℂ) ^ (-(x + I * (T0 : ℂ))) * DirichletCharacter.completedLFunction χ (s + x + I * (T0 : ℂ))
    * smoothingFunction (x + I * (T0 : ℂ)) * (x + I * (T0 : ℂ))⁻¹

lemma norm_cpow_horiz (x0 : ℝ) (hx0 : 0 < x0) (T x : ℝ) :
    ‖(x0 : ℂ) ^ (-(x + I * (T : ℂ)))‖ = x0 ^ (-x) := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hx0]
  simp

lemma rpow_x_le_max (x0 : ℝ) (hx0 : 0 < x0) {x : ℝ} (hx1 : -1 ≤ x) (hx2 : x ≤ 1) :
    x0 ^ x ≤ max x0 (x0⁻¹) := by
  by_cases h : 1 ≤ x0
  · calc x0 ^ x ≤ x0 ^ 1 := Real.rpow_le_rpow_of_exponent_le h hx2
      _ ≤ max x0 (x0⁻¹) := by rw [Real.rpow_one]; exact le_max_left _ _
  · have hx0le1 : x0 ≤ 1 := le_of_not_ge h
    calc x0 ^ x ≤ x0 ^ (-1) := Real.rpow_le_rpow_of_exponent_ge hx0 hx0le1 hx1
      _ ≤ max x0 (x0⁻¹) := by
        rw [Real.rpow_neg_one]
        exact le_max_right _ _

lemma norm_cpow_factor_le (x0 : ℝ) (hx0 : 0 < x0) {x : ℝ} (hx1 : -1 ≤ x) (hx2 : x ≤ 1) (T : ℝ) :
    ‖(x0 : ℂ) ^ (-(x + I * (T : ℂ)))‖ ≤ max x0 (x0⁻¹) := by
  rw [norm_cpow_horiz x0 hx0 T x]
  have h1 : -1 ≤ -x := by linarith
  have h2 : -x ≤ 1 := by linarith
  exact rpow_x_le_max x0 hx0 h1 h2

lemma norm_smoothing_horiz (T x : ℝ) :
    ‖smoothingFunction (x + I * (T : ℂ))‖ = Real.exp (x ^ 2 - T ^ 2) := by
  unfold smoothingFunction
  rw [Complex.norm_exp]
  congr 1
  rw [show ((x + I * (T : ℂ)) ^ 2).re = x ^ 2 - T ^ 2 by
    rw [pow_two]
    simp
    ring]

lemma norm_inv_horiz_le (T : ℝ) (hT : T ≠ 0) (x : ℝ) :
    ‖(x + I * (T : ℂ))⁻¹‖ ≤ |T|⁻¹ := by
  rw [norm_inv]
  have hle : |T| ≤ ‖x + I * (T : ℂ)‖ := by
    calc |T| = |(x + I * (T : ℂ)).im| := by congr 1; simp
      _ ≤ ‖x + I * (T : ℂ)‖ := Complex.abs_im_le_norm _
  have hnorm : 0 < ‖x + I * (T : ℂ)‖ := lt_of_lt_of_le (abs_pos.mpr hT) hle
  exact (inv_le_inv₀ hnorm (abs_pos.mpr hT)).2 hle

lemma norm_Lambda_horiz {χ : DirichletCharacter ℂ N} {s : ℂ} {A B : ℝ} (hA : 0 < A) (hB : 0 < B)
    (hΛb : ∀ z : ℂ, s.re - 1 ≤ z.re → z.re ≤ s.re + 1 → ‖DirichletCharacter.completedLFunction χ z‖ ≤ A * Real.exp (B * |z.im|))
    (T0 x : ℝ) (hx1 : -1 ≤ x) (hx2 : x ≤ 1) :
    ‖DirichletCharacter.completedLFunction χ (s + x + I * (T0 : ℂ))‖ ≤ A * Real.exp (B * (|T0| + |s.im|)) := by
  have hz1 : s.re - 1 ≤ (s + x + I * (T0 : ℂ)).re := by
    simp
    linarith
  have hz2 : (s + x + I * (T0 : ℂ)).re ≤ s.re + 1 := by
    simp
    linarith
  have hb := hΛb (s + x + I * (T0 : ℂ)) hz1 hz2
  have him : |(s + x + I * (T0 : ℂ)).im| ≤ |T0| + |s.im| := by
    have : (s + x + I * (T0 : ℂ)).im = s.im + T0 := by simp
    rw [this]
    simpa [add_comm] using (abs_add_le s.im T0)
  have he : Real.exp (B * |(s + x + I * (T0 : ℂ)).im|) ≤ Real.exp (B * (|T0| + |s.im|)) := by
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left him (le_of_lt hB))
  exact le_trans hb (mul_le_mul_of_nonneg_left he (le_of_lt hA))

lemma norm_mul4_le {a b c d : ℂ} {A B C D : ℝ} (ha : ‖a‖ ≤ A) (hb : ‖b‖ ≤ B)
    (hc : ‖c‖ ≤ C) (hd : ‖d‖ ≤ D) (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hD : 0 ≤ D) :
    ‖a * b * c * d‖ ≤ A * B * C * D := by
  have h1 : ‖a * b * c * d‖ ≤ ‖a * b * c‖ * ‖d‖ := norm_mul_le _ _
  have h2 : ‖a * b * c‖ ≤ ‖a * b‖ * ‖c‖ := norm_mul_le _ _
  have h3 : ‖a * b‖ ≤ ‖a‖ * ‖b‖ := norm_mul_le _ _
  have h3' : ‖a‖ * ‖b‖ ≤ A * B := mul_le_mul ha hb (norm_nonneg _) hA
  have h2' : ‖a * b * c‖ ≤ A * B * C := by
    calc ‖a * b * c‖ ≤ ‖a * b‖ * ‖c‖ := h2
      _ ≤ (A * B) * C := mul_le_mul (le_trans h3 h3') hc (norm_nonneg _) (mul_nonneg hA hB)
  calc ‖a * b * c * d‖ ≤ ‖a * b * c‖ * ‖d‖ := h1
    _ ≤ (A * B * C) * D := mul_le_mul h2' hd (norm_nonneg _) (mul_nonneg (mul_nonneg hA hB) hC)
    _ = A * B * C * D := by ring

lemma segmentK_norm_le {χ : DirichletCharacter ℂ N} (s : ℂ) {x0 : ℝ} (hx0 : 0 < x0)
    {A B : ℝ} (hA : 0 < A) (hB : 0 < B)
    (hΛb : ∀ z : ℂ, s.re - 1 ≤ z.re → z.re ≤ s.re + 1 → ‖DirichletCharacter.completedLFunction χ z‖ ≤ A * Real.exp (B * |z.im|))
    (T0 : ℝ) (hT0 : 1 ≤ |T0|) (x : ℝ) (hx1 : -1 ≤ x) (hx2 : x ≤ 1) :
    ‖segmentK χ s x0 T0 x‖
      ≤ (max x0 (x0⁻¹)) * A * Real.exp (B * |s.im| + 1)
          * Real.exp (-T0 ^ 2 + B * |T0|) / |T0| := by
  let C0 : ℝ := max x0 (x0⁻¹)
  have hT0ne : T0 ≠ 0 := by
    intro h
    rw [h] at hT0
    norm_num at hT0
  have hLa := norm_Lambda_horiz (χ := χ) (s := s) hA hB hΛb T0 x hx1 hx2
  have hc0 : ‖(x0 : ℂ) ^ (-(x + I * (T0 : ℂ)))‖ ≤ C0 := by
    simpa [C0] using (norm_cpow_factor_le x0 hx0 hx1 hx2 T0)
  have hg : ‖smoothingFunction (x + I * (T0 : ℂ))‖ ≤ Real.exp (1 - T0 ^ 2) := by
    rw [norm_smoothing_horiz]
    exact Real.exp_le_exp.mpr (sub_le_sub_right (by nlinarith [sq_nonneg x, hx1, hx2]) (T0 ^ 2))
  have hinv : ‖(x + I * (T0 : ℂ))⁻¹‖ ≤ |T0|⁻¹ := norm_inv_horiz_le T0 hT0ne x
  have hC00 : 0 ≤ C0 := by
    dsimp [C0]
    positivity
  have hA' : 0 ≤ A * Real.exp (B * (|T0| + |s.im|)) := by positivity
  have hg0 : 0 ≤ Real.exp (1 - T0 ^ 2) := (Real.exp_pos _).le
  have hd0 : 0 ≤ |T0|⁻¹ := by positivity
  have hmain : ‖segmentK χ s x0 T0 x‖ ≤ C0 * (A * Real.exp (B * (|T0| + |s.im|)))
      * Real.exp (1 - T0 ^ 2) * |T0|⁻¹ := by
    unfold segmentK
    exact norm_mul4_le hc0 hLa hg hinv hC00 hA' hg0 hd0
  have h_exp : Real.exp (B * (|T0| + |s.im|)) * Real.exp (1 - T0 ^ 2)
      = Real.exp (B * |s.im| + 1) * Real.exp (-T0 ^ 2 + B * |T0|) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  calc
    ‖segmentK χ s x0 T0 x‖ ≤ C0 * (A * Real.exp (B * (|T0| + |s.im|))) * Real.exp (1 - T0 ^ 2) * |T0|⁻¹ := hmain
    _ = (C0 * A * Real.exp (B * |s.im| + 1)) * Real.exp (-T0 ^ 2 + B * |T0|) * |T0|⁻¹ := by
          calc C0 * (A * Real.exp (B * (|T0| + |s.im|))) * Real.exp (1 - T0 ^ 2) * |T0|⁻¹
              = C0 * A * (Real.exp (B * (|T0| + |s.im|)) * Real.exp (1 - T0 ^ 2)) * |T0|⁻¹ := by ring
          _ = C0 * A * (Real.exp (B * |s.im| + 1) * Real.exp (-T0 ^ 2 + B * |T0|)) * |T0|⁻¹ := by rw [h_exp]
          _ = (C0 * A * Real.exp (B * |s.im| + 1)) * Real.exp (-T0 ^ 2 + B * |T0|) * |T0|⁻¹ := by ring
    _ = (max x0 (x0⁻¹)) * A * Real.exp (B * |s.im| + 1) * Real.exp (-T0 ^ 2 + B * |T0|) / |T0| := by
          dsimp [C0]
          ring

lemma continuous_segmentK (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (s : ℂ) {x0 : ℝ} (hx0 : 0 < x0)
    (T0 : ℝ) (hT0 : T0 ≠ 0) :
    Continuous (fun x : ℝ => segmentK χ s x0 T0 x) := by
  have hx0ne : (x0 : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt hx0)
  have hcp : Continuous (fun x : ℝ => (x0 : ℂ) ^ (-(x + I * (T0 : ℂ)))) := by
    have h_eq : (fun x : ℝ => (x0 : ℂ) ^ (-(x + I * (T0 : ℂ))))
        = fun x : ℝ => cexp (Complex.log (x0 : ℂ) * (-(x + I * (T0 : ℂ)))) := by
      funext x
      rw [Complex.cpow_def_of_ne_zero hx0ne]
    rw [h_eq]
    exact Continuous.cexp (continuous_const.mul (by fun_prop : Continuous fun x : ℝ => -(x + I * (T0 : ℂ))))
  have hL : Continuous (fun x : ℝ => DirichletCharacter.completedLFunction χ (s + x + I * (T0 : ℂ))) := by
    exact ((differentiable_completedLFunction hχ).continuous).comp
      (by fun_prop : Continuous fun x : ℝ => s + x + I * (T0 : ℂ))
  have hg : Continuous (fun x : ℝ => smoothingFunction (x + I * (T0 : ℂ))) := by
    unfold smoothingFunction
    exact Continuous.cexp (by fun_prop : Continuous fun x : ℝ => (x + I * (T0 : ℂ)) ^ 2)
  have hu : Continuous (fun x : ℝ => (x + I * (T0 : ℂ))⁻¹) := by
    refine Continuous.inv₀ (f := fun x : ℝ => x + I * (T0 : ℂ)) (by fun_prop) ?_
    intro x
    intro h
    have him := congrArg Complex.im h
    simp at him
    exact hT0 him
  unfold segmentK
  exact (((hcp.mul hL).mul hg).mul hu)

/-- Integrated bound: ‖∫_{-1}^{1} segmentK(T0)‖ ≤ 2·C1·exp(-T0²+B|T0|)/|T0| for 1 ≤ |T0|. -/
lemma horiz_int_norm_le {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) (s : ℂ) {x0 : ℝ} (hx0 : 0 < x0)
    {A B : ℝ} (hA : 0 < A) (hB : 0 < B)
    (hΛb : ∀ z : ℂ, s.re - 1 ≤ z.re → z.re ≤ s.re + 1 → ‖DirichletCharacter.completedLFunction χ z‖ ≤ A * Real.exp (B * |z.im|))
    (T0 : ℝ) (hT0 : 1 ≤ |T0|) :
    ‖∫ x : ℝ in (-1 : ℝ)..1, segmentK χ s x0 T0 x‖
      ≤ 2 * ((max x0 (x0⁻¹)) * A * Real.exp (B * |s.im| + 1))
          * Real.exp (-T0 ^ 2 + B * |T0|) / |T0| := by
  let C1 : ℝ := (max x0 (x0⁻¹)) * A * Real.exp (B * |s.im| + 1)
  let g : ℝ → ℝ := fun x => C1 * Real.exp (-T0 ^ 2 + B * |T0|) / |T0|
  have hT0ne : T0 ≠ 0 := by
    intro h
    rw [h] at hT0
    norm_num at hT0
  have hcont : Continuous (fun x : ℝ => ‖segmentK χ s x0 T0 x‖) :=
    (continuous_segmentK χ hχ s hx0 T0 hT0ne).norm
  have hfint : IntervalIntegrable (fun x : ℝ => ‖segmentK χ s x0 T0 x‖) volume (-1) 1 :=
    hcont.intervalIntegrable _ _
  have hgint : IntervalIntegrable g volume (-1) 1 := (continuous_const : Continuous g).intervalIntegrable _ _
  have hpt : ∀ x ∈ Set.Icc (-1 : ℝ) 1, ‖segmentK χ s x0 T0 x‖ ≤ g x := by
    intro x hx
    have hp := segmentK_norm_le (χ := χ) (s := s) (x0 := x0) hx0 hA hB hΛb T0 hT0 x hx.1 hx.2
    simpa [C1, g] using hp
  have hmono : (∫ x : ℝ in (-1 : ℝ)..1, ‖segmentK χ s x0 T0 x‖) ≤ ∫ x : ℝ in (-1 : ℝ)..1, g x := by
    exact intervalIntegral.integral_mono_on (by norm_num : (-1 : ℝ) ≤ 1) hfint hgint hpt
  calc
    ‖∫ x : ℝ in (-1 : ℝ)..1, segmentK χ s x0 T0 x‖
        ≤ ∫ x : ℝ in (-1 : ℝ)..1, ‖segmentK χ s x0 T0 x‖ := by
          exact intervalIntegral.norm_integral_le_integral_norm (by norm_num : (-1 : ℝ) ≤ 1)
    _ ≤ ∫ x : ℝ in (-1 : ℝ)..1, g x := hmono
    _ = 2 * C1 * Real.exp (-T0 ^ 2 + B * |T0|) / |T0| := by
          have hgconst : (fun x : ℝ => g x) = fun _ : ℝ => (C1 * Real.exp (-T0 ^ 2 + B * |T0|) / |T0|) := by
            funext x
            rfl
          rw [hgconst]
          rw [intervalIntegral.integral_const]
          ring
    _ = 2 * ((max x0 (x0⁻¹)) * A * Real.exp (B * |s.im| + 1))
          * Real.exp (-T0 ^ 2 + B * |T0|) / |T0| := by
          dsimp [C1]

/-- decay of the horizontal envelope at +∞. -/
lemma tendsto_env (B C1 : ℝ) :
    Tendsto (fun T : ℝ => 2 * C1 * Real.exp (-T ^ 2 + B * T) / T) atTop (𝓝 0) := by
  have hf : Tendsto (fun T : ℝ => -(T ^ 2) + B * T) atTop atBot := by
    refine Filter.tendsto_atBot_mono' atTop ?hle tendsto_neg_atTop_atBot
    filter_upwards [eventually_ge_atTop (B + 1), eventually_ge_atTop 0] with T hT hT0
    have hTB : 0 ≤ T - B - 1 := by linarith
    have hprod : 0 ≤ T * (T - B - 1) := mul_nonneg hT0 hTB
    have hprod' : 0 ≤ T ^ 2 - B * T - T := by
      have hring : T * (T - B - 1) = T ^ 2 - B * T - T := by ring
      rw [← hring]
      exact hprod
    nlinarith
  have hE : Tendsto (fun T : ℝ => Real.exp (-(T ^ 2) + B * T)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp hf
  have hInv : Tendsto (fun T : ℝ => T⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have hmul : Tendsto (fun T : ℝ => Real.exp (-(T ^ 2) + B * T) * T⁻¹) atTop (𝓝 0) := by
    simpa using (hE.mul hInv)
  have hconst : Tendsto (fun T : ℝ => (2 * C1) * (Real.exp (-(T ^ 2) + B * T) * T⁻¹)) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul hmul)
  simpa [div_eq_mul_inv, mul_assoc] using hconst

/-- Main horizontal decay at height T ≥ 0. -/
lemma tendsto_horizontal_segment_top (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (s : ℂ)
    {x0 : ℝ} (hx0 : 0 < x0) (hΛ : Λ_growth χ s) :
    Tendsto (fun T : ℝ => ∫ x : ℝ in (-1 : ℝ)..1, segmentK χ s x0 T x) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  rcases hΛ with ⟨A, B, hA, hB, hΛb⟩
  let C1 : ℝ := (max x0 (x0⁻¹)) * A * Real.exp (B * |s.im| + 1)
  let env : ℝ → ℝ := fun T => 2 * C1 * Real.exp (-T ^ 2 + B * T) / T
  apply Filter.Tendsto.squeeze' (g := fun _ : ℝ => (0 : ℝ)) (h := env)
  · exact tendsto_const_nhds
  · have ht := tendsto_env B C1
    simpa [env] using ht
  · exact Filter.Eventually.of_forall (fun T => norm_nonneg _)
  · filter_upwards [eventually_ge_atTop 1] with T hT
    have hT0 : 0 ≤ T := by linarith
    have hTab : 1 ≤ |T| := by
      rw [abs_of_nonneg hT0]
      exact hT
    have hb := horiz_int_norm_le (χ := χ) hχ s hx0 hA hB hΛb T hTab
    have hb' : ‖∫ x : ℝ in (-1 : ℝ)..1, segmentK χ s x0 T x‖ ≤ env T := by
      -- hb RHS: 2·C1·exp(-T²+B·|T|)/|T| with |T| = T
      simpa [env, C1, abs_of_nonneg hT0] using hb
    exact hb'



/-- decay at negative heights: `∫ segmentK(-T) → 0` as `T → +∞`. -/
lemma tendsto_horizontal_segment_neg (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (s : ℂ)
    {x0 : ℝ} (hx0 : 0 < x0) (hΛ : Λ_growth χ s) :
    Tendsto (fun T : ℝ => ∫ x : ℝ in (-1 : ℝ)..1, segmentK χ s x0 (-T) x) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  rcases hΛ with ⟨A, B, hA, hB, hΛb⟩
  let C1 : ℝ := (max x0 (x0⁻¹)) * A * Real.exp (B * |s.im| + 1)
  let env : ℝ → ℝ := fun T => 2 * C1 * Real.exp (-T ^ 2 + B * T) / T
  apply Filter.Tendsto.squeeze' (g := fun _ : ℝ => (0 : ℝ)) (h := env)
  · exact tendsto_const_nhds
  · have ht := tendsto_env B C1
    simpa [env] using ht
  · exact Filter.Eventually.of_forall (fun T => norm_nonneg _)
  · filter_upwards [eventually_ge_atTop 1] with T hT
    have hT0 : 0 ≤ T := by linarith
    have hTab : 1 ≤ |(-T)| := by
      rw [abs_neg, abs_of_nonneg hT0]
      exact hT
    have hb := horiz_int_norm_le (χ := χ) hχ s hx0 hA hB hΛb (-T) hTab
    have hb' : ‖∫ x : ℝ in (-1 : ℝ)..1, segmentK χ s x0 (-T) x‖ ≤ env T := by
      simpa [env, C1, abs_of_nonneg hT0, abs_neg] using hb
    exact hb'


/-- Horizontal decay (top/bottom segments, right side `u = x + iT`): the integral over
`x ∈ [-1,1]` of `K(x+iT)` vanishes as `T → ∞`, under the strip-growth hypothesis. -/
lemma tendsto_horizontal_right (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (s : ℂ)
    (hs0 : 0 < s.re) (hs1 : s.re < 1) {x0 : ℝ} (hx0 : 0 < x0) (hΛ : Λ_growth χ s) :
    Tendsto (fun T : ℝ => ∫ x : ℝ in (-1 : ℝ)..1,
        (x0 : ℂ) ^ (-(x + I * (T : ℂ))) * DirichletCharacter.completedLFunction χ (s + x + I * (T : ℂ))
          * smoothingFunction (x + I * (T : ℂ)) / (x + I * (T : ℂ))) atTop (𝓝 0) := by
  have hcongr : (fun T : ℝ => ∫ x : ℝ in (-1 : ℝ)..1,
        (x0 : ℂ) ^ (-(x + I * (T : ℂ))) * DirichletCharacter.completedLFunction χ (s + x + I * (T : ℂ))
          * smoothingFunction (x + I * (T : ℂ)) / (x + I * (T : ℂ)))
      = (fun T : ℝ => ∫ x : ℝ in (-1 : ℝ)..1, segmentK χ s x0 T x) := by
    funext T
    apply intervalIntegral.integral_congr
    intro x hx
    dsimp [segmentK]
    rw [div_eq_mul_inv]
  rw [hcongr]
  exact tendsto_horizontal_segment_top χ hχ s hx0 hΛ


/-- Horizontal decay (bottom segment, `u = x - iT`). -/
lemma tendsto_horizontal_left (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (s : ℂ)
    (hs0 : 0 < s.re) (hs1 : s.re < 1) {x0 : ℝ} (hx0 : 0 < x0) (hΛ : Λ_growth χ s) :
    Tendsto (fun T : ℝ => ∫ x : ℝ in (-1 : ℝ)..1,
        (x0 : ℂ) ^ (-(x - I * (T : ℂ))) * DirichletCharacter.completedLFunction χ (s + x - I * (T : ℂ))
          * smoothingFunction (x - I * (T : ℂ)) / (x - I * (T : ℂ))) atTop (𝓝 0) := by
  have hcongr : (fun T : ℝ => ∫ x : ℝ in (-1 : ℝ)..1,
        (x0 : ℂ) ^ (-(x - I * (T : ℂ))) * DirichletCharacter.completedLFunction χ (s + x - I * (T : ℂ))
          * smoothingFunction (x - I * (T : ℂ)) / (x - I * (T : ℂ)))
      = (fun T : ℝ => ∫ x : ℝ in (-1 : ℝ)..1, segmentK χ s x0 (-T) x) := by
    funext T
    apply intervalIntegral.integral_congr
    intro x hx
    dsimp [segmentK]
    rw [div_eq_mul_inv]
    have h1 : (x0 : ℂ) ^ (-(x - I * (T : ℂ))) = (x0 : ℂ) ^ (-(x + I * ((-T : ℝ) : ℂ))) := by
      congr 1
      apply Complex.ext <;> simp <;> ring
    have h2 : DirichletCharacter.completedLFunction χ (s + x - I * (T : ℂ)) = DirichletCharacter.completedLFunction χ (s + x + I * ((-T : ℝ) : ℂ)) := by
      congr 1
      apply Complex.ext <;> simp <;> ring
    have h3 : smoothingFunction (x - I * (T : ℂ)) = smoothingFunction (x + I * ((-T : ℝ) : ℂ)) := by
      congr 1
      apply Complex.ext <;> simp <;> ring
    have h4 : (x - I * (T : ℂ))⁻¹ = (x + I * ((-T : ℝ) : ℂ))⁻¹ := by
      congr 1
      apply Complex.ext <;> simp <;> ring
    rw [h1, h2, h3, h4]
  rw [hcongr]
  exact tendsto_horizontal_segment_neg χ hχ s hx0 hΛ


/-- The Mellin integrand on the right vertical line `Re u = 1`. -/
noncomputable def lineRight (χ : DirichletCharacter ℂ N) (s : ℂ) (x : ℝ) (y : ℝ) : ℂ :=
  (x : ℂ) ^ (-(1 + I * (y : ℂ))) * DirichletCharacter.completedLFunction χ (s + 1 + I * (y : ℂ))
    * smoothingFunction (1 + I * (y : ℂ)) / (1 + I * (y : ℂ))

/-- The Mellin integrand on the left vertical line `Re u = -1`. -/
noncomputable def lineLeft (χ : DirichletCharacter ℂ N) (s : ℂ) (x : ℝ) (y : ℝ) : ℂ :=
  (x : ℂ) ^ (-(-1 + I * (y : ℂ))) * DirichletCharacter.completedLFunction χ (s - 1 + I * (y : ℂ))
    * smoothingFunction (-1 + I * (y : ℂ)) / (-1 + I * (y : ℂ))

/-- `‖Λ(s+1+iy)‖` is bounded uniformly in `y`, for `0 < Re s`. -/
lemma norm_Lambda_right_line (χ : DirichletCharacter ℂ N) {s : ℂ} (hs0 : 0 < s.re) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ y : ℝ, ‖DirichletCharacter.completedLFunction χ (s + 1 + I * (y : ℂ))‖ ≤ B := by
  have hσ : 1 < s.re + 1 := by linarith
  rcases TrivialBounds.norm_completedLFunction_vertical (χ := χ) (σ := s.re + 1) hσ with ⟨B, hB0, hB⟩
  refine ⟨B, hB0, ?_⟩
  intro y
  have harg : s + 1 + I * (y : ℂ) = ((s.re + 1 : ℝ) : ℂ) + I * ((s.im + y : ℝ) : ℂ) := by
    apply Complex.ext <;> simp <;> ring
  rw [harg]
  exact hB (s.im + y)

/-- `‖Λ(s-1+iy)‖` is bounded uniformly in `y` for primitive `χ` and `Re s < 1`
(via the functional equation, reflecting to `Re = 2 - Re s > 1`). -/
lemma norm_Lambda_left_line {χ : DirichletCharacter ℂ N} (hprim : χ.IsPrimitive) {s : ℂ}
    (hs1 : s.re < 1) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ y : ℝ, ‖DirichletCharacter.completedLFunction χ (s - 1 + I * (y : ℂ))‖ ≤ B := by
  have hσ : s.re - 1 < 0 := by linarith
  rcases TrivialBounds.norm_completedLFunction_vertical_left hprim hσ with ⟨B, hB0, hB⟩
  refine ⟨B, hB0, ?_⟩
  intro y
  have harg : s - 1 + I * (y : ℂ) = ((s.re - 1 : ℝ) : ℂ) + I * ((s.im + y : ℝ) : ℂ) := by
    apply Complex.ext <;> simp <;> ring
  rw [harg]
  exact hB (s.im + y)

/-- `‖x^(-(1+Iy))‖ = x⁻¹` (base `x > 0`). -/
lemma norm_cpow_lineRight (x : ℝ) (hx : 0 < x) (y : ℝ) :
    ‖(x : ℂ) ^ (-(1 + I * (y : ℂ)))‖ = x⁻¹ := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp
  rw [Real.rpow_neg_one]

/-- `‖x^(-(-1+Iy))‖ = x` (base `x > 0`). -/
lemma norm_cpow_lineLeft (x : ℝ) (hx : 0 < x) (y : ℝ) :
    ‖(x : ℂ) ^ (-(-1 + I * (y : ℂ)))‖ = x := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
  congr 1
  simp

/-- `‖(1+iy)⁻¹‖ ≤ 1` and `‖(-1+iy)⁻¹‖ ≤ 1`. -/
lemma norm_inv_one_add_mul_I_le (t : ℝ) : ‖(1 + I * (t : ℂ))⁻¹‖ ≤ 1 := by
  rw [norm_inv]
  have hsq : ‖1 + I * (t : ℂ)‖ ^ 2 = 1 + t ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq]
    simpa [pow_two, mul_comm, add_comm, add_left_comm, add_assoc] using
      (Complex.normSq_add_mul_I (1 : ℝ) t)
  have hnn : 0 ≤ ‖1 + I * (t : ℂ)‖ := norm_nonneg _
  have hbig : 1 ≤ ‖1 + I * (t : ℂ)‖ := by
    rw [← sq_le_sq₀ (by norm_num) hnn]
    nlinarith [hsq, sq_nonneg t]
  exact (inv_le_one₀ (lt_of_lt_of_le (by norm_num) hbig)).mpr hbig

/-- `‖(x+iy)⁻¹‖ ≤ 1` for real part of modulus 1: `|x| = 1` handled through `normSq = 1 + y²`. -/
lemma norm_inv_lineLeft_le (t : ℝ) : ‖(-1 + I * (t : ℂ))⁻¹‖ ≤ 1 := by
  rw [norm_inv]
  have hsq : ‖-1 + I * (t : ℂ)‖ ^ 2 = 1 + t ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq]
    simpa [pow_two, mul_comm, add_comm, add_left_comm, add_assoc] using
      (Complex.normSq_add_mul_I (-1 : ℝ) t)
  have hnn : 0 ≤ ‖-1 + I * (t : ℂ)‖ := norm_nonneg _
  have hbig : 1 ≤ ‖-1 + I * (t : ℂ)‖ := by
    rw [← sq_le_sq₀ (by norm_num) hnn]
    nlinarith [hsq, sq_nonneg t]
  exact (inv_le_one₀ (lt_of_lt_of_le (by norm_num) hbig)).mpr hbig

/-- Pointwise domination of the right-line integrand by a Gaussian. -/
lemma lineRight_norm_le (χ : DirichletCharacter ℂ N) {s : ℂ} (hs0 : 0 < s.re) {x : ℝ} (hx : 0 < x) :
    ∃ A : ℝ, 0 < A ∧ ∀ y : ℝ, ‖lineRight χ s x y‖ ≤ A * Real.exp (-(y ^ 2)) := by
  rcases norm_Lambda_right_line χ hs0 with ⟨B, hB0, hB⟩
  let A : ℝ := x⁻¹ * (B + 1) * Real.exp 1
  refine ⟨A, ?_, ?_⟩
  · dsimp [A]
    positivity
  · intro y
    have hα : ‖(x : ℂ) ^ (-(1 + I * (y : ℂ)))‖ = x⁻¹ := norm_cpow_lineRight x hx y
    have hγ : ‖smoothingFunction (1 + I * (y : ℂ))‖ = Real.exp (1 - y ^ 2) := by
      simpa using (norm_smoothing_horiz y 1)
    have hδ : ‖(1 + I * (y : ℂ))⁻¹‖ ≤ 1 := norm_inv_one_add_mul_I_le y
    have hle1 : ‖lineRight χ s x y‖ ≤ x⁻¹ * B * Real.exp (1 - y ^ 2) := by
      calc
        ‖lineRight χ s x y‖
            = ‖(x : ℂ) ^ (-(1 + I * (y : ℂ)))‖ * ‖DirichletCharacter.completedLFunction χ (s + 1 + I * (y : ℂ))‖
                * ‖smoothingFunction (1 + I * (y : ℂ))‖ * ‖(1 + I * (y : ℂ))⁻¹‖ := by
                unfold lineRight
                rw [div_eq_mul_inv]
                simp only [norm_mul]
        _ ≤ x⁻¹ * B * Real.exp (1 - y ^ 2) * 1 := by
                rw [hα, hγ]
                have hβ : ‖DirichletCharacter.completedLFunction χ (s + 1 + I * (y : ℂ))‖ ≤ B := hB y
                gcongr
        _ = x⁻¹ * B * Real.exp (1 - y ^ 2) := by ring
    have hle2 : x⁻¹ * B * Real.exp (1 - y ^ 2) ≤ A * Real.exp (-(y ^ 2)) := by
      have hB1 : B ≤ B + 1 := by linarith
      have hx0 : 0 ≤ x⁻¹ := inv_nonneg.mpr (le_of_lt hx)
      have hB0' : 0 ≤ B := hB0
      have he1 : Real.exp (1 - y ^ 2) = Real.exp 1 * Real.exp (-(y ^ 2)) := by
        rw [← Real.exp_add]
        congr 1
      calc
        x⁻¹ * B * Real.exp (1 - y ^ 2) ≤ x⁻¹ * (B + 1) * Real.exp (1 - y ^ 2) := by
              gcongr
        _ = x⁻¹ * (B + 1) * (Real.exp 1 * Real.exp (-(y ^ 2))) := by rw [he1]
        _ = A * Real.exp (-(y ^ 2)) := by
              dsimp [A]
              ring
    exact le_trans hle1 hle2

/-- Pointwise domination of the left-line integrand by a Gaussian. -/
lemma lineLeft_norm_le {χ : DirichletCharacter ℂ N} (hprim : χ.IsPrimitive) {s : ℂ}
    (hs1 : s.re < 1) {x : ℝ} (hx : 0 < x) :
    ∃ A : ℝ, 0 < A ∧ ∀ y : ℝ, ‖lineLeft χ s x y‖ ≤ A * Real.exp (-(y ^ 2)) := by
  rcases norm_Lambda_left_line hprim hs1 with ⟨B, hB0, hB⟩
  let A : ℝ := x * (B + 1) * Real.exp 1
  refine ⟨A, ?_, ?_⟩
  · dsimp [A]
    positivity
  · intro y
    have hα : ‖(x : ℂ) ^ (-(-1 + I * (y : ℂ)))‖ = x := norm_cpow_lineLeft x hx y
    have hγ : ‖smoothingFunction (-1 + I * (y : ℂ))‖ = Real.exp (1 - y ^ 2) := by
      simpa using (norm_smoothing_horiz y (-1))
    have hδ : ‖(-1 + I * (y : ℂ))⁻¹‖ ≤ 1 := norm_inv_lineLeft_le y
    have hle1 : ‖lineLeft χ s x y‖ ≤ x * B * Real.exp (1 - y ^ 2) := by
      calc
        ‖lineLeft χ s x y‖
            = ‖(x : ℂ) ^ (-(-1 + I * (y : ℂ)))‖ * ‖DirichletCharacter.completedLFunction χ (s - 1 + I * (y : ℂ))‖
                * ‖smoothingFunction (-1 + I * (y : ℂ))‖ * ‖(-1 + I * (y : ℂ))⁻¹‖ := by
                unfold lineLeft
                rw [div_eq_mul_inv]
                simp only [norm_mul]
        _ ≤ x * B * Real.exp (1 - y ^ 2) * 1 := by
                rw [hα, hγ]
                have hβ : ‖DirichletCharacter.completedLFunction χ (s - 1 + I * (y : ℂ))‖ ≤ B := hB y
                gcongr
        _ = x * B * Real.exp (1 - y ^ 2) := by ring
    have hle2 : x * B * Real.exp (1 - y ^ 2) ≤ A * Real.exp (-(y ^ 2)) := by
      have hB1 : B ≤ B + 1 := by linarith
      have he1 : Real.exp (1 - y ^ 2) = Real.exp 1 * Real.exp (-(y ^ 2)) := by
        rw [← Real.exp_add]
        congr 1
      calc
        x * B * Real.exp (1 - y ^ 2) ≤ x * (B + 1) * Real.exp (1 - y ^ 2) := by
              gcongr
        _ = x * (B + 1) * (Real.exp 1 * Real.exp (-(y ^ 2))) := by rw [he1]
        _ = A * Real.exp (-(y ^ 2)) := by
              dsimp [A]
              ring
    exact le_trans hle1 hle2

/-- The right-line integrand is continuous in `y`. -/
lemma continuous_lineRight (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (s : ℂ) {x : ℝ} (hx : 0 < x) :
    Continuous (fun y : ℝ => lineRight χ s x y) := by
  rw [continuous_iff_continuousAt]
  intro y0
  have hA : ContinuousAt (fun y : ℝ => (x : ℂ) ^ (-(1 + I * (y : ℂ)))) y0 := by
    refine ContinuousAt.const_cpow (f := fun y : ℝ => -(1 + I * (y : ℂ))) (a := y0) (b := (x : ℂ)) ?_ ?_
    · fun_prop
    · left
      exact (ofReal_ne_zero.mpr (ne_of_gt hx))
  have hL : ContinuousAt (fun y : ℝ => DirichletCharacter.completedLFunction χ (s + 1 + I * (y : ℂ))) y0 := by
    exact ((differentiable_completedLFunction hχ).continuous.continuousAt).comp
      (by fun_prop : ContinuousAt (fun y : ℝ => s + 1 + I * (y : ℂ)) y0)
  have hC : ContinuousAt (fun y : ℝ => smoothingFunction (1 + I * (y : ℂ))) y0 := by
    unfold smoothingFunction
    fun_prop
  have hD : ContinuousAt (fun y : ℝ => (1 : ℂ) + I * (y : ℂ)) y0 := by fun_prop
  have hz0 : (1 : ℂ) + I * (y0 : ℂ) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp at hre
  have hF : ContinuousAt (fun y : ℝ =>
      (x : ℂ) ^ (-(1 + I * (y : ℂ))) * DirichletCharacter.completedLFunction χ (s + 1 + I * (y : ℂ))
        * smoothingFunction (1 + I * (y : ℂ)) / (1 + I * (y : ℂ))) y0 := by
    refine ContinuousAt.div ((hA.mul hL).mul hC) hD hz0
  convert hF using 1
  ext y
  rfl

/-- The left-line integrand is continuous in `y`. -/
lemma continuous_lineLeft (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (s : ℂ) {x : ℝ} (hx : 0 < x) :
    Continuous (fun y : ℝ => lineLeft χ s x y) := by
  rw [continuous_iff_continuousAt]
  intro y0
  have hA : ContinuousAt (fun y : ℝ => (x : ℂ) ^ (-(-1 + I * (y : ℂ)))) y0 := by
    refine ContinuousAt.const_cpow (f := fun y : ℝ => -(-1 + I * (y : ℂ))) (a := y0) (b := (x : ℂ)) ?_ ?_
    · fun_prop
    · left
      exact (ofReal_ne_zero.mpr (ne_of_gt hx))
  have hL : ContinuousAt (fun y : ℝ => DirichletCharacter.completedLFunction χ (s - 1 + I * (y : ℂ))) y0 := by
    exact ((differentiable_completedLFunction hχ).continuous.continuousAt).comp
      (by fun_prop : ContinuousAt (fun y : ℝ => s - 1 + I * (y : ℂ)) y0)
  have hC : ContinuousAt (fun y : ℝ => smoothingFunction (-1 + I * (y : ℂ))) y0 := by
    unfold smoothingFunction
    fun_prop
  have hD : ContinuousAt (fun y : ℝ => (-1 : ℂ) + I * (y : ℂ)) y0 := by fun_prop
  have hz0 : (-1 : ℂ) + I * (y0 : ℂ) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp at hre
  have hF : ContinuousAt (fun y : ℝ =>
      (x : ℂ) ^ (-(-1 + I * (y : ℂ))) * DirichletCharacter.completedLFunction χ (s - 1 + I * (y : ℂ))
        * smoothingFunction (-1 + I * (y : ℂ)) / (-1 + I * (y : ℂ))) y0 := by
    refine ContinuousAt.div ((hA.mul hL).mul hC) hD hz0
  convert hF using 1
  ext y
  rfl

/-- The right-line integrand is integrable over `ℝ`. -/
lemma integrable_lineRight (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) {s : ℂ} (hs0 : 0 < s.re)
    {x : ℝ} (hx : 0 < x) :
    Integrable (fun y : ℝ => lineRight χ s x y) := by
  rcases lineRight_norm_le χ hs0 hx with ⟨A, hApos, hAbound⟩
  have hg : Integrable (fun y : ℝ => A * Real.exp (-(y ^ 2))) := by
    have hbase : Integrable (fun y : ℝ => Real.exp (-(y ^ 2))) := by
      simpa using (integrable_exp_neg_mul_sq (b := (1 : ℝ)) (by norm_num) :
        Integrable fun y : ℝ => Real.exp (-(1 : ℝ) * y ^ 2))
    exact hbase.const_mul A
  have hmeas : AEStronglyMeasurable (fun y : ℝ => lineRight χ s x y) :=
    (continuous_lineRight χ hχ s hx).aestronglyMeasurable
  have hle : ∀ᵐ y : ℝ ∂(volume : Measure ℝ), ‖lineRight χ s x y‖ ≤ A * Real.exp (-(y ^ 2)) := by
    exact ae_of_all _ hAbound
  exact Integrable.mono' hg hmeas hle

/-- The left-line integrand is integrable over `ℝ`. -/
lemma integrable_lineLeft {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) (hprim : χ.IsPrimitive)
    {s : ℂ} (hs1 : s.re < 1) {x : ℝ} (hx : 0 < x) :
    Integrable (fun y : ℝ => lineLeft χ s x y) := by
  rcases lineLeft_norm_le hprim hs1 hx with ⟨A, hApos, hAbound⟩
  have hg : Integrable (fun y : ℝ => A * Real.exp (-(y ^ 2))) := by
    have hbase : Integrable (fun y : ℝ => Real.exp (-(y ^ 2))) := by
      simpa using (integrable_exp_neg_mul_sq (b := (1 : ℝ)) (by norm_num) :
        Integrable fun y : ℝ => Real.exp (-(1 : ℝ) * y ^ 2))
    exact hbase.const_mul A
  have hmeas : AEStronglyMeasurable (fun y : ℝ => lineLeft χ s x y) :=
    (continuous_lineLeft χ hχ s hx).aestronglyMeasurable
  have hle : ∀ᵐ y : ℝ ∂(volume : Measure ℝ), ‖lineLeft χ s x y‖ ≤ A * Real.exp (-(y ^ 2)) := by
    exact ae_of_all _ hAbound
  exact Integrable.mono' hg hmeas hle

/-- Truncated right vertical integrals converge to the full-line integral. -/
lemma tendsto_truncated_right (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) {s : ℂ} (hs0 : 0 < s.re)
    {x : ℝ} (hx : 0 < x) :
    Tendsto (fun T : ℝ => ∫ y : ℝ in -T..T, lineRight χ s x y) atTop
      (𝓝 (∫ y : ℝ, lineRight χ s x y)) :=
  VertLimit.tendsto_interval_vertical (fun y : ℝ => lineRight χ s x y) (integrable_lineRight χ hχ hs0 hx)

/-- Truncated left vertical integrals converge to the full-line integral. -/
lemma tendsto_truncated_left {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) (hprim : χ.IsPrimitive)
    {s : ℂ} (hs1 : s.re < 1) {x : ℝ} (hx : 0 < x) :
    Tendsto (fun T : ℝ => ∫ y : ℝ in -T..T, lineLeft χ s x y) atTop
      (𝓝 (∫ y : ℝ, lineLeft χ s x y)) :=
  VertLimit.tendsto_interval_vertical (fun y : ℝ => lineLeft χ s x y) (integrable_lineLeft hχ hprim hs1 hx)

/-- The bottom horizontal edge equals the `segmentK`-based integral at `-T`
(pointwise in `T`). -/
lemma botK_eq_segment (χ : DirichletCharacter ℂ N) (s : ℂ) {x : ℝ} (T : ℝ) :
    (∫ z : ℝ in (-1 : ℝ)..1,
        (x : ℂ) ^ (-(z - I * (T : ℂ))) * DirichletCharacter.completedLFunction χ (s + (z - I * (T : ℂ)))
          * smoothingFunction (z - I * (T : ℂ)) / (z - I * (T : ℂ)))
      = (∫ z : ℝ in (-1 : ℝ)..1, segmentK χ s x (-T) z) := by
  apply intervalIntegral.integral_congr
  intro z hz
  change (x : ℂ) ^ (-(z - I * (T : ℂ))) * DirichletCharacter.completedLFunction χ (s + (z - I * (T : ℂ)))
          * smoothingFunction (z - I * (T : ℂ)) / (z - I * (T : ℂ))
      = (x : ℂ) ^ (-(z + I * ((-T : ℝ) : ℂ))) * DirichletCharacter.completedLFunction χ (s + z + I * ((-T : ℝ) : ℂ))
          * smoothingFunction (z + I * ((-T : ℝ) : ℂ)) * (z + I * ((-T : ℝ) : ℂ))⁻¹
  rw [div_eq_mul_inv]
  have h1 : (x : ℂ) ^ (-(z - I * (T : ℂ))) = (x : ℂ) ^ (-(z + I * ((-T : ℝ) : ℂ))) := by
    congr 1
    apply Complex.ext <;> simp <;> ring
  have h2 : DirichletCharacter.completedLFunction χ (s + (z - I * (T : ℂ))) = DirichletCharacter.completedLFunction χ (s + z + I * ((-T : ℝ) : ℂ)) := by
    congr 1
    apply Complex.ext <;> simp <;> ring
  have h3 : smoothingFunction (z - I * (T : ℂ)) = smoothingFunction (z + I * ((-T : ℝ) : ℂ)) := by
    congr 1
    apply Complex.ext <;> simp <;> ring
  have h4 : (z - I * (T : ℂ))⁻¹ = (z + I * ((-T : ℝ) : ℂ))⁻¹ := by
    congr 1
    apply Complex.ext <;> simp <;> ring
  rw [h1, h2, h3, h4]

/-- The top horizontal edge equals the `segmentK`-based integral at `T`. -/
lemma topK_eq_segment (χ : DirichletCharacter ℂ N) (s : ℂ) {x : ℝ} (T : ℝ) :
    (∫ z : ℝ in (-1 : ℝ)..1,
        (x : ℂ) ^ (-(z + I * (T : ℂ))) * DirichletCharacter.completedLFunction χ (s + (z + I * (T : ℂ)))
          * smoothingFunction (z + I * (T : ℂ)) / (z + I * (T : ℂ)))
      = (∫ z : ℝ in (-1 : ℝ)..1, segmentK χ s x T z) := by
  apply intervalIntegral.integral_congr
  intro z hz
  change (x : ℂ) ^ (-(z + I * (T : ℂ))) * DirichletCharacter.completedLFunction χ (s + (z + I * (T : ℂ)))
          * smoothingFunction (z + I * (T : ℂ)) / (z + I * (T : ℂ))
      = (x : ℂ) ^ (-(z + I * ((T : ℝ) : ℂ))) * DirichletCharacter.completedLFunction χ (s + z + I * ((T : ℝ) : ℂ))
          * smoothingFunction (z + I * ((T : ℝ) : ℂ)) * (z + I * ((T : ℝ) : ℂ))⁻¹
  rw [div_eq_mul_inv]
  have h1 : (x : ℂ) ^ (-(z + I * (T : ℂ))) = (x : ℂ) ^ (-(z + I * ((T : ℝ) : ℂ))) := by rfl
  have h2 : DirichletCharacter.completedLFunction χ (s + (z + I * (T : ℂ))) = DirichletCharacter.completedLFunction χ (s + z + I * ((T : ℝ) : ℂ)) := by
    congr 1
    apply Complex.ext <;> simp <;> ring
  have h3 : smoothingFunction (z + I * (T : ℂ)) = smoothingFunction (z + I * ((T : ℝ) : ℂ)) := by rfl
  have h4 : (z + I * (T : ℂ))⁻¹ = (z + I * ((T : ℝ) : ℂ))⁻¹ := by rfl
  rw [h1, h2, h3, h4]

/-- The right vertical edge in `K`-form equals `lineRight` (pointwise in `T`). -/
lemma rawRight_eq_lineRight (χ : DirichletCharacter ℂ N) (s : ℂ) {x : ℝ} (T : ℝ) :
    (∫ y : ℝ in -T..T, (x : ℂ) ^ (-(1 + I * (y : ℂ))) * DirichletCharacter.completedLFunction χ (s + (1 + I * (y : ℂ)))
        * smoothingFunction (1 + I * (y : ℂ)) / (1 + I * (y : ℂ)))
      = (∫ y : ℝ in -T..T, lineRight χ s x y) := by
  apply intervalIntegral.integral_congr
  intro y hy
  change (x : ℂ) ^ (-(1 + I * (y : ℂ))) * DirichletCharacter.completedLFunction χ (s + (1 + I * (y : ℂ)))
      * smoothingFunction (1 + I * (y : ℂ)) / (1 + I * (y : ℂ))
      = lineRight χ s x y
  have harg : s + (1 + I * (y : ℂ)) = s + 1 + I * (y : ℂ) := by ring
  unfold lineRight
  rw [harg]

/-- The left vertical edge in `K`-form equals `lineLeft` (pointwise in `T`). -/
lemma rawLeft_eq_lineLeft (χ : DirichletCharacter ℂ N) (s : ℂ) {x : ℝ} (T : ℝ) :
    (∫ y : ℝ in -T..T, (x : ℂ) ^ (-(-1 + I * (y : ℂ))) * DirichletCharacter.completedLFunction χ (s + (-1 + I * (y : ℂ)))
        * smoothingFunction (-1 + I * (y : ℂ)) / (-1 + I * (y : ℂ)))
      = (∫ y : ℝ in -T..T, lineLeft χ s x y) := by
  apply intervalIntegral.integral_congr
  intro y hy
  change (x : ℂ) ^ (-(-1 + I * (y : ℂ))) * DirichletCharacter.completedLFunction χ (s + (-1 + I * (y : ℂ)))
      * smoothingFunction (-1 + I * (y : ℂ)) / (-1 + I * (y : ℂ))
      = lineLeft χ s x y
  have harg : s + (-1 + I * (y : ℂ)) = s - 1 + I * (y : ℂ) := by ring
  unfold lineLeft
  rw [harg]

/-- **Vertical-line identity**: from the finite rectangle (`AfeRectK.rectBoundary_K`) and
the `T → ∞` passage,
`Λ(s) = (1/(2π))·(∫_ℝ K(1+iy) dy − ∫_ℝ K(−1+iy) dy)`. -/
theorem vertical_line_identity (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (hprim : χ.IsPrimitive)
    (s : ℂ) (hs0 : 0 < s.re) (hs1 : s.re < 1) {x : ℝ} (hx : 0 < x) (hΛ : Λ_growth χ s) :
    DirichletCharacter.completedLFunction χ s =
      (1 / (2 * Real.pi) : ℝ) •
        ((∫ y : ℝ, lineRight χ s x y) - (∫ y : ℝ, lineLeft χ s x y)) := by
  -- the rectangle boundary integrand K(u) = x^(-u) Λ(s+u) g(u)/u
  let K : ℂ → ℂ := fun u : ℂ => (x : ℂ) ^ (-u) * DirichletCharacter.completedLFunction χ (s + u) * smoothingFunction u / u
  let R : ℝ → ℂ := fun T : ℝ => AfeRect.rectBoundary ⟨-1, -T⟩ ⟨1, T⟩ K
  let fr : ℝ → ℂ := fun T : ℝ => ∫ y : ℝ in -T..T, lineRight χ s x y
  let fl : ℝ → ℂ := fun T : ℝ => ∫ y : ℝ in -T..T, lineLeft χ s x y
  have hfrT : Tendsto fr atTop (𝓝 (∫ y : ℝ, lineRight χ s x y)) := by
    simpa [fr] using tendsto_truncated_right χ hχ hs0 hx
  have hflT : Tendsto fl atTop (𝓝 (∫ y : ℝ, lineLeft χ s x y)) := by
    simpa [fl] using tendsto_truncated_left (hχ := hχ) (hprim := hprim) (hs1 := hs1) (hx := hx)
  -- horizontal edges decay to 0
  have hbT : Tendsto (fun T : ℝ => ∫ z : ℝ in (-1 : ℝ)..1, segmentK χ s x (-T) z) atTop (𝓝 0) :=
    tendsto_horizontal_segment_neg χ hχ s hx hΛ
  have htT : Tendsto (fun T : ℝ => ∫ z : ℝ in (-1 : ℝ)..1, segmentK χ s x T z) atTop (𝓝 0) :=
    tendsto_horizontal_segment_top χ hχ s hx hΛ
  -- rectangle = four edges (K form)
  have hRectRaw : ∀ T : ℝ, R T = AfeRect.rectBoundaryFour T K := by
    intro T
    dsimp [R]
    exact AfeRect.rectBoundary_four T K
  -- four edges in K form = bottom/top via segmentK and vertical via lineRight/lineLeft
  have hEdge : ∀ T : ℝ, R T =
      (∫ z : ℝ in (-1 : ℝ)..1, segmentK χ s x (-T) z)
        - (∫ z : ℝ in (-1 : ℝ)..1, segmentK χ s x T z)
        + I • (∫ y : ℝ in -T..T, lineRight χ s x y)
        - I • (∫ y : ℝ in -T..T, lineLeft χ s x y) := by
    intro T
    -- expand rectBoundaryFour edges in K form
    have hK : AfeRect.rectBoundaryFour T K =
        (∫ z : ℝ in (-1 : ℝ)..1, (x : ℂ) ^ (-(z - I * (T : ℂ))) * DirichletCharacter.completedLFunction χ (s + (z - I * (T : ℂ)))
            * smoothingFunction (z - I * (T : ℂ)) / (z - I * (T : ℂ)))
          - (∫ z : ℝ in (-1 : ℝ)..1, (x : ℂ) ^ (-(z + I * (T : ℂ))) * DirichletCharacter.completedLFunction χ (s + (z + I * (T : ℂ)))
            * smoothingFunction (z + I * (T : ℂ)) / (z + I * (T : ℂ)))
          + I • (∫ y : ℝ in -T..T, (x : ℂ) ^ (-(1 + I * (y : ℂ))) * DirichletCharacter.completedLFunction χ (s + (1 + I * (y : ℂ)))
            * smoothingFunction (1 + I * (y : ℂ)) / (1 + I * (y : ℂ)))
          - I • (∫ y : ℝ in -T..T, (x : ℂ) ^ (-(-1 + I * (y : ℂ))) * DirichletCharacter.completedLFunction χ (s + (-1 + I * (y : ℂ)))
            * smoothingFunction (-1 + I * (y : ℂ)) / (-1 + I * (y : ℂ))) := by
          unfold AfeRect.rectBoundaryFour K
          ring
    calc
      R T = AfeRect.rectBoundaryFour T K := hRectRaw T
      _ = (∫ z : ℝ in (-1 : ℝ)..1, (x : ℂ) ^ (-(z - I * (T : ℂ))) * DirichletCharacter.completedLFunction χ (s + (z - I * (T : ℂ)))
            * smoothingFunction (z - I * (T : ℂ)) / (z - I * (T : ℂ)))
          - (∫ z : ℝ in (-1 : ℝ)..1, (x : ℂ) ^ (-(z + I * (T : ℂ))) * DirichletCharacter.completedLFunction χ (s + (z + I * (T : ℂ)))
            * smoothingFunction (z + I * (T : ℂ)) / (z + I * (T : ℂ)))
          + I • (∫ y : ℝ in -T..T, (x : ℂ) ^ (-(1 + I * (y : ℂ))) * DirichletCharacter.completedLFunction χ (s + (1 + I * (y : ℂ)))
            * smoothingFunction (1 + I * (y : ℂ)) / (1 + I * (y : ℂ)))
          - I • (∫ y : ℝ in -T..T, (x : ℂ) ^ (-(-1 + I * (y : ℂ))) * DirichletCharacter.completedLFunction χ (s + (-1 + I * (y : ℂ)))
            * smoothingFunction (-1 + I * (y : ℂ)) / (-1 + I * (y : ℂ))) := hK
      _ = (∫ z : ℝ in (-1 : ℝ)..1, segmentK χ s x (-T) z)
          - (∫ z : ℝ in (-1 : ℝ)..1, segmentK χ s x T z)
          + I • (∫ y : ℝ in -T..T, lineRight χ s x y)
          - I • (∫ y : ℝ in -T..T, lineLeft χ s x y) := by
          rw [botK_eq_segment χ s (T := T)]
          rw [topK_eq_segment χ s (T := T)]
          rw [rawRight_eq_lineRight χ s (T := T)]
          rw [rawLeft_eq_lineLeft χ s (T := T)]
  -- the limit of R
  have hlim : Tendsto R atTop (𝓝 (I • (∫ y : ℝ, lineRight χ s x y) - I • (∫ y : ℝ, lineLeft χ s x y))) := by
    -- R = B - Tp + I fr - I fl with the four tendsto
    have h1 : Tendsto (fun T : ℝ => (∫ z : ℝ in (-1 : ℝ)..1, segmentK χ s x (-T) z)
          - (∫ z : ℝ in (-1 : ℝ)..1, segmentK χ s x T z)
          + I • (∫ y : ℝ in -T..T, lineRight χ s x y)
          - I • (∫ y : ℝ in -T..T, lineLeft χ s x y)) atTop
          (𝓝 (I • (∫ y : ℝ, lineRight χ s x y) - I • (∫ y : ℝ, lineLeft χ s x y))) := by
      -- combine
      have hBt : Tendsto (fun T : ℝ => (∫ z : ℝ in (-1 : ℝ)..1, segmentK χ s x (-T) z)
            - (∫ z : ℝ in (-1 : ℝ)..1, segmentK χ s x T z)) atTop (𝓝 0) := by
        simpa using (hbT.sub htT)
      have hIfr : Tendsto (fun T : ℝ => I • (∫ y : ℝ in -T..T, lineRight χ s x y)) atTop
          (𝓝 (I • (∫ y : ℝ, lineRight χ s x y))) := by
        -- smul with tendsto: fr → L gives I•fr → I•L: use Tendsto.smul? complex smul: is a continuous linear map
        exact hfrT.const_smul I
      have hIfl : Tendsto (fun T : ℝ => I • (∫ y : ℝ in -T..T, lineLeft χ s x y)) atTop
          (𝓝 (I • (∫ y : ℝ, lineLeft χ s x y))) := hflT.const_smul I
      have hA : Tendsto (fun T : ℝ => (∫ z : ℝ in (-1 : ℝ)..1, segmentK χ s x (-T) z)
            - (∫ z : ℝ in (-1 : ℝ)..1, segmentK χ s x T z)
            + I • (∫ y : ℝ in -T..T, lineRight χ s x y)) atTop
            (𝓝 (I • (∫ y : ℝ, lineRight χ s x y))) := by
            simpa using (hBt.add hIfr)
      simpa using (hA.sub hIfl)
    exact Tendsto.congr' (Eventually.of_forall (fun T => (hEdge T).symm)) h1
  -- first limit: R → 2πi Λ(s) (eventually, from rectBoundary_K)
  have hRK : (fun _ : ℝ => 2 * π * I * DirichletCharacter.completedLFunction χ s) =ᶠ[atTop] R := by
    filter_upwards [eventually_ge_atTop 1] with T hT
    have hTpos : 0 < T := by linarith
    have hv' : 2 * π * I * DirichletCharacter.completedLFunction χ s = R T := by
      simpa [R, K] using (AfeRect.rectBoundary_K χ hχ s hx T hTpos).symm
    exact hv'
  have hlim2 : Tendsto R atTop (𝓝 (2 * π * I * DirichletCharacter.completedLFunction χ s)) := by
    exact Filter.Tendsto.congr' hRK tendsto_const_nhds
  -- equality of the two limits
  have hEqLim := tendsto_nhds_unique hlim hlim2
  -- hEqLim : I • (∫ lineRight) - I • (∫ lineLeft) = 2πI·Λ(s)
  -- equivalently I · X = 2πI · Λ
  let X : ℂ := (∫ y : ℝ, lineRight χ s x y) - (∫ y : ℝ, lineLeft χ s x y)
  have hIeq : I * X = 2 * π * I * DirichletCharacter.completedLFunction χ s := by
    -- hEqLim expressed via X
    have : I • (∫ y : ℝ, lineRight χ s x y) - I • (∫ y : ℝ, lineLeft χ s x y) = I * X := by
      dsimp [X]
      ring
    rwa [this] at hEqLim
  -- cancel I: X = 2π Λ(s)
  have hX : X = (2 * π) * DirichletCharacter.completedLFunction χ s := by
    have hI0 : I ≠ 0 := by simp
    calc
      X = I⁻¹ * (I * X) := by field_simp [hI0]
      _ = I⁻¹ * (2 * π * I * DirichletCharacter.completedLFunction χ s) := by rw [hIeq]
      _ = (2 * π) * DirichletCharacter.completedLFunction χ s := by
            field_simp [hI0]
  -- conclude: Λ = (1/2π) · X
  have hpi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  have hX' : X = (((2 * Real.pi : ℝ) : ℂ)) * DirichletCharacter.completedLFunction χ s := by simpa using hX
  calc
    DirichletCharacter.completedLFunction χ s
        = (1 / (2 * Real.pi) : ℝ) • X := by
            have h2c : ((2 * Real.pi : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr hpi
            calc
              DirichletCharacter.completedLFunction χ s
                  = (((2 * Real.pi : ℝ) : ℂ)⁻¹) * (((2 * Real.pi : ℝ) : ℂ) * DirichletCharacter.completedLFunction χ s) := by
                    field_simp [h2c]
              _ = (((2 * Real.pi : ℝ) : ℂ)⁻¹) * X := by rw [hX']
              _ = (((2 * Real.pi : ℝ)⁻¹ : ℝ) : ℂ) * X := by
                    exact congrArg (fun w : ℂ => w * X) ((map_inv₀ (algebraMap ℝ ℂ) (2 * Real.pi)).symm)
              _ = ((2 * Real.pi : ℝ)⁻¹ : ℝ) • X := by rfl
              _ = (1 / (2 * Real.pi) : ℝ) • X := by
                    congr 1
                    rw [one_div]
    _ = (1 / (2 * Real.pi) : ℝ) • ((∫ y : ℝ, lineRight χ s x y) - (∫ y : ℝ, lineLeft χ s x y)) := by
          dsimp [X]

end

end PL.AfeVerticalLine


/-!
# The strip-growth hypothesis `Λ_growth` for primitive characters

`PL.AfeVerticalLine.vertical_line_identity` (the `T → ∞` passage for the Mellin
contour of the approximate functional equation) is proved under the hypothesis
`AfeVerticalLine.Λ_growth χ s`: sub-exponential growth of the completed L-function in the
strip `s.re-1 ≤ Re z ≤ s.re+1`.  This file provides that hypothesis **as a theorem**, from
`PL.CompletedStrip.completedLFunction_vertical_bound_strip`: the completed L-function
of a non-trivial primitive character is *bounded* (uniformly in `Im z`) on every bounded
vertical strip, which is much stronger than sub-exponential growth.
-/

open Complex DirichletCharacter Filter MeasureTheory Set
open scoped Real

set_option autoImplicit false

namespace PL.AfeGrowth

noncomputable section

variable {N : ℕ} [NeZero N]

/-- The completed L-function of a non-trivial primitive character grows at most
sub-exponentially in the strip `s.re-1 ≤ Re z ≤ s.re+1` (`0 < Re s < 1`). -/
theorem lambda_growth (χ : DirichletCharacter ℂ N) (hχprim : χ.IsPrimitive)
    (hχ : χ ≠ 1) {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    AfeVerticalLine.Λ_growth χ s := by
  rcases CompletedStrip.completedLFunction_vertical_bound_strip χ hχprim hχ (σ := s.re)
      hs0 hs1 with ⟨C, hC0, hC⟩
  refine ⟨max C 1, 1, ?_, by norm_num, ?_⟩
  · exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_right C 1)
  · intro z hz1 hz2
    have hb := hC z hz1 hz2
    have h1 : (1 : ℝ) ≤ Real.exp (1 * |z.im|) := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr (by positivity)
    calc
      ‖DirichletCharacter.completedLFunction χ z‖ ≤ C := hb
      _ ≤ max C 1 := le_max_left C 1
      _ ≤ max C 1 * Real.exp (1 * |z.im|) :=
          le_mul_of_one_le_right (by positivity) h1

end
end PL.AfeGrowth


/-!
# Absolute convergence of the archimedean weight integral (even characters)

The archimedean smoothing weight of the approximate functional equation is the inverse
Mellin transform (vertical integral at `Re u = 1`)

`W_z(x) = (1 / (2π)) · ∫ (t : ℝ), x^(-(1 + I t)) · (γ(z + 1 + I t)/γ(z)) · g(1 + I t)/(1 + I t) dt`

(see `PL.AFE.afeWeight`), with `g(u) = exp(u²)` the smoothing function.  For an
**even** character `γ = Complex.Gammaℝ`.

This file proves the integrand is (Bochner-)integrable in `t` for fixed `z` with
`0 < Re z` and fixed `x > 0`.  The proof combines:

* the uniform vertical bound on the ratio
  `PL.GammaRatioEven.gammaRatio_even_vertical_bound` (bounded by a constant `C`),
* `|x^(-(1 + I t))| = x^(-1)`,
* the super-exponential decay `|g(1 + I t)| = exp(1 - t²)` of the smoothing function, and
* the known integrability of `t ↦ exp(-t²)` over the real line.
-/

open Complex Filter MeasureTheory Set
open scoped Real

set_option autoImplicit false

namespace PL.WeightConvergesEven

/-- The integrand of the archimedean weight (even case), as a function of `t`. -/
noncomputable def weightIntegrand (z : ℂ) (x : ℝ) (t : ℝ) : ℂ :=
  (x : ℂ) ^ (-(1 + I * (t : ℂ))) *
    (Complex.Gammaℝ (z + 1 + I * (t : ℂ)) / Complex.Gammaℝ z) *
    cexp ((1 + I * (t : ℂ)) ^ 2) / (1 + I * (t : ℂ))

/-- Continuity of `Complex.Gammaℝ` away from its poles at `0, -2, -4, ...`. -/
lemma continuousAt_Gammaℝ_of_ne (s : ℂ) (hs : ∀ m : ℕ, s ≠ (-2 : ℂ) * (m : ℂ)) :
    ContinuousAt Complex.Gammaℝ s := by
  have h2 : ∀ m : ℕ, (s / 2) ≠ - (m : ℂ) := by
    intro m hm
    apply hs m
    calc
      s = 2 * (s / 2) := by ring
      _ = 2 * (-(m : ℂ)) := by rw [hm]
      _ = (-2 : ℂ) * (m : ℂ) := by ring
  have h1 : ContinuousAt (fun u : ℂ => (Real.pi : ℂ) ^ (-u / 2)) s := by
    refine ContinuousAt.const_cpow (f := fun u : ℂ => -u / 2) (a := s) (b := (Real.pi : ℂ)) ?_ ?_
    · fun_prop
    · left
      exact (ofReal_ne_zero.mpr Real.pi_ne_zero)
  have hg : ContinuousAt (fun u : ℂ => Complex.Gamma (u / 2)) s := by
    refine ContinuousAt.comp (g := Complex.Gamma) (f := fun u : ℂ => u / 2) (x := s) ?_ ?_
    · exact continuousAt_Gamma (s / 2) h2
    · fun_prop
  change ContinuousAt (fun u : ℂ => (Real.pi : ℂ) ^ (-u / 2) * Complex.Gamma (u / 2)) s
  exact h1.mul hg

/-- The gamma-factor ratio is continuous in `t` along the vertical line through `z + 1`. -/
lemma continuousAt_Gammaℝ_z1it (z : ℂ) (hz : 0 < z.re) (t0 : ℝ) :
    ContinuousAt (fun t : ℝ => Complex.Gammaℝ (z + 1 + I * (t : ℂ))) t0 := by
  refine ContinuousAt.comp (g := Complex.Gammaℝ) (f := fun t : ℝ => z + 1 + I * (t : ℂ)) (x := t0) ?_ ?_
  · refine continuousAt_Gammaℝ_of_ne (z + 1 + I * (t0 : ℂ)) ?_
    intro m hmeq
    have hre := congrArg Complex.re hmeq
    simp at hre
    have hm : 0 ≤ (m : ℝ) := by exact_mod_cast (Nat.zero_le m)
    nlinarith [hz, hm]
  · have hc : Continuous (fun t : ℝ => z + 1 + I * (t : ℂ)) := by fun_prop
    exact hc.continuousAt

/-- `|x^(-(1 + I t))| = x⁻¹` for `x > 0`. -/
lemma norm_cpow_real (x : ℝ) (hx : 0 < x) (t : ℝ) :
    ‖(x : ℂ) ^ (-(1 + I * (t : ℂ)))‖ = x⁻¹ := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp
  rw [Real.rpow_neg_one]

/-- `|exp ((1 + I t)^2)| = exp (1 - t^2)`. -/
lemma norm_cexp_sq (t : ℝ) : ‖cexp ((1 + I * (t : ℂ)) ^ 2)‖ = Real.exp (1 - t ^ 2) := by
  rw [Complex.norm_exp]
  congr 1
  rw [pow_two]
  simp
  ring

/-- `|(1 + I t)⁻¹| ≤ 1`, i.e. the vertical-line denominator never shrinks the norm. -/
lemma norm_inv_one_add_mul_I_le (t : ℝ) : ‖(1 + I * (t : ℂ))⁻¹‖ ≤ 1 := by
  rw [norm_inv]
  have hsq : ‖1 + I * (t : ℂ)‖ ^ 2 = 1 + t ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq]
    simpa [pow_two, mul_comm, add_comm, add_left_comm, add_assoc] using
      (Complex.normSq_add_mul_I (1 : ℝ) t)
  have hnn : 0 ≤ ‖1 + I * (t : ℂ)‖ := norm_nonneg _
  have hbig : 1 ≤ ‖1 + I * (t : ℂ)‖ := by
    rw [← sq_le_sq₀ (by norm_num) hnn]
    nlinarith [hsq, sq_nonneg t]
  exact (inv_le_one₀ (lt_of_lt_of_le (by norm_num) hbig)).mpr hbig

/-- Pointwise domination of the integrand's modulus by a multiple of `exp (-t²)`. -/
lemma weightIntegrand_norm_le (z : ℂ) (hz : 0 < z.re) {x : ℝ} (hx : 0 < x) :
    ∃ A : ℝ, 0 < A ∧ ∀ t : ℝ, ‖weightIntegrand z x t‖ ≤ A * Real.exp (-(t ^ 2)) := by
  rcases PL.GammaRatioEven.gammaRatio_even_vertical_bound z hz with ⟨C, hCpos, hCb⟩
  let A : ℝ := x⁻¹ * C * Real.exp 1
  refine ⟨A, ?_, ?_⟩
  · dsimp [A]
    positivity
  · intro t
    have hδle : ‖(1 + I * (t : ℂ))⁻¹‖ ≤ 1 := norm_inv_one_add_mul_I_le t
    have hα : ‖(x : ℂ) ^ (-(1 + I * (t : ℂ)))‖ = x⁻¹ := norm_cpow_real x hx t
    have hγ : ‖cexp ((1 + I * (t : ℂ)) ^ 2)‖ = Real.exp (1 - t ^ 2) := norm_cexp_sq t
    have hβ : ‖Complex.Gammaℝ (z + 1 + I * (t : ℂ)) / Complex.Gammaℝ z‖ ≤ C := hCb t
    calc
      ‖weightIntegrand z x t‖
          = ‖(x : ℂ) ^ (-(1 + I * (t : ℂ)))‖ *
              ‖(Complex.Gammaℝ (z + 1 + I * (t : ℂ)) / Complex.Gammaℝ z)‖ *
              ‖cexp ((1 + I * (t : ℂ)) ^ 2)‖ * ‖(1 + I * (t : ℂ))⁻¹‖ := by
              rw [weightIntegrand, div_eq_mul_inv]
              simp only [norm_mul]
      _ ≤ x⁻¹ * C * Real.exp (1 - t ^ 2) * 1 := by
              rw [hα, hγ]
              gcongr
      _ = x⁻¹ * C * Real.exp (1 - t ^ 2) := by ring
      _ = A * Real.exp (-(t ^ 2)) := by
              have he : Real.exp (1 - t ^ 2) = Real.exp 1 * Real.exp (-(t ^ 2)) := by
                rw [← Real.exp_add]
                rfl
              rw [he]
              dsimp [A]
              ring

/-- The weight integrand is continuous in `t` for fixed `z` (`0 < Re z`) and `x > 0`. -/
lemma continuous_weightIntegrand (z : ℂ) (hz : 0 < z.re) {x : ℝ} (hx : 0 < x) :
    Continuous (fun t : ℝ => weightIntegrand z x t) := by
  rw [continuous_iff_continuousAt]
  intro t0
  have hBnum : ContinuousAt (fun t : ℝ => Complex.Gammaℝ (z + 1 + I * (t : ℂ))) t0 :=
    continuousAt_Gammaℝ_z1it z hz t0
  have hB : ContinuousAt (fun t : ℝ =>
      Complex.Gammaℝ (z + 1 + I * (t : ℂ)) / Complex.Gammaℝ z) t0 := by
    refine ContinuousAt.div hBnum continuousAt_const ?_
    exact (Complex.Gammaℝ_ne_zero_of_re_pos (s := z) hz)
  have hA : ContinuousAt (fun t : ℝ => (x : ℂ) ^ (-(1 + I * (t : ℂ)))) t0 := by
    refine ContinuousAt.const_cpow (f := fun t : ℝ => -(1 + I * (t : ℂ))) (a := t0) (b := (x : ℂ)) ?_ ?_
    · fun_prop
    · left
      exact (ofReal_ne_zero.mpr (ne_of_gt hx))
  have hC : ContinuousAt (fun t : ℝ => cexp ((1 + I * (t : ℂ)) ^ 2)) t0 := by
    fun_prop
  have hD : ContinuousAt (fun t : ℝ => (1 : ℂ) + I * (t : ℂ)) t0 := by fun_prop
  have hz0 : (1 : ℂ) + I * (t0 : ℂ) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp at hre
  have hF : ContinuousAt (fun t : ℝ =>
      (x : ℂ) ^ (-(1 + I * (t : ℂ))) *
        (Complex.Gammaℝ (z + 1 + I * (t : ℂ)) / Complex.Gammaℝ z) *
        cexp ((1 + I * (t : ℂ)) ^ 2) / (1 + I * (t : ℂ))) t0 := by
    refine ContinuousAt.div ((hA.mul hB).mul hC) hD hz0
  convert hF using 1
  ext t
  rfl

/-- The integrand of the archimedean weight (even case) is integrable over `t : ℝ`,
for fixed `z` with `0 < Re z` and `x > 0`. -/
theorem weightIntegrand_integrable (z : ℂ) (hz : 0 < z.re) {x : ℝ} (hx : 0 < x) :
    Integrable (fun t : ℝ =>
      (x : ℂ) ^ (-(1 + I * t)) *
        (Complex.Gammaℝ (z + 1 + I * t) / Complex.Gammaℝ z) *
        cexp ((1 + I * t) ^ 2) / (1 + I * t)) := by
  rcases weightIntegrand_norm_le z hz hx with ⟨A, hApos, hAbound⟩
  have hg : Integrable (fun t : ℝ => A * Real.exp (-(t ^ 2))) := by
    have hbase : Integrable (fun t : ℝ => Real.exp (-(t ^ 2))) := by
      simpa using (integrable_exp_neg_mul_sq (b := (1 : ℝ)) (by norm_num) :
        Integrable fun t : ℝ => Real.exp (-(1 : ℝ) * t ^ 2))
    exact hbase.const_mul A
  have hmeas : AEStronglyMeasurable (fun t : ℝ => weightIntegrand z x t) :=
    (continuous_weightIntegrand z hz hx).aestronglyMeasurable
  have hle : ∀ᵐ t : ℝ ∂(volume : Measure ℝ), ‖weightIntegrand z x t‖ ≤ A * Real.exp (-(t ^ 2)) := by
    exact ae_of_all _ hAbound
  have hint : Integrable (fun t : ℝ => weightIntegrand z x t) :=
    Integrable.mono' hg hmeas hle
  convert hint using 1
  ext t
  rfl

end PL.WeightConvergesEven


/-!
# Absolute convergence of the archimedean weight integral (odd characters)

The archimedean smoothing weight of the approximate functional equation is the inverse
Mellin transform (vertical integral at `Re u = 1`)

`W_z(x) = (1 / (2π)) · ∫ (t : ℝ), x^(-(1 + I t)) · (γ(z + 1 + I t)/γ(z)) · g(1 + I t)/(1 + I t) dt`

(see `PL.AFE.afeWeight`), with `g(u) = exp(u²)` the smoothing function.  For an
**odd** character the archimedean gamma factor is `γ(s) = Complex.Gammaℝ (s + 1)`, so the
ratio in the weight is `γ(z + 1 + I t)/γ(z) = Gammaℝ (z + 2 + I t) / Gammaℝ (z + 1)`.

This file proves the integrand is (Bochner-)integrable in `t` for fixed `z` with
`0 < Re z` and fixed `x > 0`.  The proof mirrors `PL.WeightConvergesEven`, using
`PL.GammaRatioOdd.gammaRatio_odd_vertical_bound` for the uniform-in-`t` bound on
the gamma-factor ratio.
-/

open Complex Filter MeasureTheory Set
open scoped Real

set_option autoImplicit false

namespace PL.WeightConvergesOdd

/-- The integrand of the archimedean weight (odd case), as a function of `t`. -/
noncomputable def weightIntegrandOdd (z : ℂ) (x : ℝ) (t : ℝ) : ℂ :=
  (x : ℂ) ^ (-(1 + I * (t : ℂ))) *
    (Complex.Gammaℝ (z + 2 + I * (t : ℂ)) / Complex.Gammaℝ (z + 1)) *
    cexp ((1 + I * (t : ℂ)) ^ 2) / (1 + I * (t : ℂ))

/-- Continuity of `Complex.Gammaℝ` away from its poles at `0, -2, -4, ...`. -/
lemma continuousAt_Gammaℝ_of_ne (s : ℂ) (hs : ∀ m : ℕ, s ≠ (-2 : ℂ) * (m : ℂ)) :
    ContinuousAt Complex.Gammaℝ s := by
  have h2 : ∀ m : ℕ, (s / 2) ≠ - (m : ℂ) := by
    intro m hm
    apply hs m
    calc
      s = 2 * (s / 2) := by ring
      _ = 2 * (-(m : ℂ)) := by rw [hm]
      _ = (-2 : ℂ) * (m : ℂ) := by ring
  have h1 : ContinuousAt (fun u : ℂ => (Real.pi : ℂ) ^ (-u / 2)) s := by
    refine ContinuousAt.const_cpow (f := fun u : ℂ => -u / 2) (a := s) (b := (Real.pi : ℂ)) ?_ ?_
    · fun_prop
    · left
      exact (ofReal_ne_zero.mpr Real.pi_ne_zero)
  have hg : ContinuousAt (fun u : ℂ => Complex.Gamma (u / 2)) s := by
    refine ContinuousAt.comp (g := Complex.Gamma) (f := fun u : ℂ => u / 2) (x := s) ?_ ?_
    · exact continuousAt_Gamma (s / 2) h2
    · fun_prop
  change ContinuousAt (fun u : ℂ => (Real.pi : ℂ) ^ (-u / 2) * Complex.Gamma (u / 2)) s
  exact h1.mul hg

/-- The gamma-factor ratio is continuous in `t` along the vertical line through `z + 2`. -/
lemma continuousAt_Gammaℝ_z2it (z : ℂ) (hz : 0 < z.re) (t0 : ℝ) :
    ContinuousAt (fun t : ℝ => Complex.Gammaℝ (z + 2 + I * (t : ℂ))) t0 := by
  refine ContinuousAt.comp (g := Complex.Gammaℝ) (f := fun t : ℝ => z + 2 + I * (t : ℂ)) (x := t0) ?_ ?_
  · refine continuousAt_Gammaℝ_of_ne (z + 2 + I * (t0 : ℂ)) ?_
    intro m hmeq
    have hre := congrArg Complex.re hmeq
    simp at hre
    have hm : 0 ≤ (m : ℝ) := by exact_mod_cast (Nat.zero_le m)
    nlinarith [hz, hm]
  · have hc : Continuous (fun t : ℝ => z + 2 + I * (t : ℂ)) := by fun_prop
    exact hc.continuousAt

/-- `|x^(-(1 + I t))| = x⁻¹` for `x > 0`. -/
lemma norm_cpow_real (x : ℝ) (hx : 0 < x) (t : ℝ) :
    ‖(x : ℂ) ^ (-(1 + I * (t : ℂ)))‖ = x⁻¹ := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp
  rw [Real.rpow_neg_one]

/-- `|exp ((1 + I t)^2)| = exp (1 - t^2)`. -/
lemma norm_cexp_sq (t : ℝ) : ‖cexp ((1 + I * (t : ℂ)) ^ 2)‖ = Real.exp (1 - t ^ 2) := by
  rw [Complex.norm_exp]
  congr 1
  rw [pow_two]
  simp
  ring

/-- `|(1 + I t)⁻¹| ≤ 1`, i.e. the vertical-line denominator never shrinks the norm. -/
lemma norm_inv_one_add_mul_I_le (t : ℝ) : ‖(1 + I * (t : ℂ))⁻¹‖ ≤ 1 := by
  rw [norm_inv]
  have hsq : ‖1 + I * (t : ℂ)‖ ^ 2 = 1 + t ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq]
    simpa [pow_two, mul_comm, add_comm, add_left_comm, add_assoc] using
      (Complex.normSq_add_mul_I (1 : ℝ) t)
  have hnn : 0 ≤ ‖1 + I * (t : ℂ)‖ := norm_nonneg _
  have hbig : 1 ≤ ‖1 + I * (t : ℂ)‖ := by
    rw [← sq_le_sq₀ (by norm_num) hnn]
    nlinarith [hsq, sq_nonneg t]
  exact (inv_le_one₀ (lt_of_lt_of_le (by norm_num) hbig)).mpr hbig

/-- Pointwise domination of the integrand's modulus by a multiple of `exp (-t²)`. -/
lemma weightIntegrandOdd_norm_le (z : ℂ) (hz : 0 < z.re) {x : ℝ} (hx : 0 < x) :
    ∃ A : ℝ, 0 < A ∧ ∀ t : ℝ, ‖weightIntegrandOdd z x t‖ ≤ A * Real.exp (-(t ^ 2)) := by
  rcases PL.GammaRatioOdd.gammaRatio_odd_vertical_bound z hz with ⟨C, hCpos, hCb⟩
  let A : ℝ := x⁻¹ * C * Real.exp 1
  refine ⟨A, ?_, ?_⟩
  · dsimp [A]
    positivity
  · intro t
    have hδle : ‖(1 + I * (t : ℂ))⁻¹‖ ≤ 1 := norm_inv_one_add_mul_I_le t
    have hα : ‖(x : ℂ) ^ (-(1 + I * (t : ℂ)))‖ = x⁻¹ := norm_cpow_real x hx t
    have hγ : ‖cexp ((1 + I * (t : ℂ)) ^ 2)‖ = Real.exp (1 - t ^ 2) := norm_cexp_sq t
    have hβ : ‖Complex.Gammaℝ (z + 2 + I * (t : ℂ)) / Complex.Gammaℝ (z + 1)‖ ≤ C := hCb t
    calc
      ‖weightIntegrandOdd z x t‖
          = ‖(x : ℂ) ^ (-(1 + I * (t : ℂ)))‖ *
              ‖(Complex.Gammaℝ (z + 2 + I * (t : ℂ)) / Complex.Gammaℝ (z + 1))‖ *
              ‖cexp ((1 + I * (t : ℂ)) ^ 2)‖ * ‖(1 + I * (t : ℂ))⁻¹‖ := by
              rw [weightIntegrandOdd, div_eq_mul_inv]
              simp only [norm_mul]
      _ ≤ x⁻¹ * C * Real.exp (1 - t ^ 2) * 1 := by
              rw [hα, hγ]
              gcongr
      _ = x⁻¹ * C * Real.exp (1 - t ^ 2) := by ring
      _ = A * Real.exp (-(t ^ 2)) := by
              have he : Real.exp (1 - t ^ 2) = Real.exp 1 * Real.exp (-(t ^ 2)) := by
                rw [← Real.exp_add]
                rfl
              rw [he]
              dsimp [A]
              ring

/-- The weight integrand (odd case) is continuous in `t` for fixed `z` (`0 < Re z`)
and `x > 0`. -/
lemma continuous_weightIntegrandOdd (z : ℂ) (hz : 0 < z.re) {x : ℝ} (hx : 0 < x) :
    Continuous (fun t : ℝ => weightIntegrandOdd z x t) := by
  rw [continuous_iff_continuousAt]
  intro t0
  have hBnum : ContinuousAt (fun t : ℝ => Complex.Gammaℝ (z + 2 + I * (t : ℂ))) t0 :=
    continuousAt_Gammaℝ_z2it z hz t0
  have hz1 : 0 < (z + 1).re := by
    rw [Complex.add_re]
    simp
    linarith
  have hB : ContinuousAt (fun t : ℝ =>
      Complex.Gammaℝ (z + 2 + I * (t : ℂ)) / Complex.Gammaℝ (z + 1)) t0 := by
    refine ContinuousAt.div hBnum continuousAt_const ?_
    exact (Complex.Gammaℝ_ne_zero_of_re_pos (s := z + 1) hz1)
  have hA : ContinuousAt (fun t : ℝ => (x : ℂ) ^ (-(1 + I * (t : ℂ)))) t0 := by
    refine ContinuousAt.const_cpow (f := fun t : ℝ => -(1 + I * (t : ℂ))) (a := t0) (b := (x : ℂ)) ?_ ?_
    · fun_prop
    · left
      exact (ofReal_ne_zero.mpr (ne_of_gt hx))
  have hC : ContinuousAt (fun t : ℝ => cexp ((1 + I * (t : ℂ)) ^ 2)) t0 := by
    fun_prop
  have hD : ContinuousAt (fun t : ℝ => (1 : ℂ) + I * (t : ℂ)) t0 := by fun_prop
  have hz0 : (1 : ℂ) + I * (t0 : ℂ) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp at hre
  have hF : ContinuousAt (fun t : ℝ =>
      (x : ℂ) ^ (-(1 + I * (t : ℂ))) *
        (Complex.Gammaℝ (z + 2 + I * (t : ℂ)) / Complex.Gammaℝ (z + 1)) *
        cexp ((1 + I * (t : ℂ)) ^ 2) / (1 + I * (t : ℂ))) t0 := by
    refine ContinuousAt.div ((hA.mul hB).mul hC) hD hz0
  convert hF using 1
  ext t
  rfl

/-- The integrand of the archimedean weight (odd case) is integrable over `t : ℝ`,
for fixed `z` with `0 < Re z` and `x > 0`. -/
theorem weightIntegrandOdd_integrable (z : ℂ) (hz : 0 < z.re) {x : ℝ} (hx : 0 < x) :
    Integrable (fun t : ℝ =>
      (x : ℂ) ^ (-(1 + I * t)) *
        (Complex.Gammaℝ (z + 2 + I * t) / Complex.Gammaℝ (z + 1)) *
        cexp ((1 + I * t) ^ 2) / (1 + I * t)) := by
  rcases weightIntegrandOdd_norm_le z hz hx with ⟨A, hApos, hAbound⟩
  have hg : Integrable (fun t : ℝ => A * Real.exp (-(t ^ 2))) := by
    have hbase : Integrable (fun t : ℝ => Real.exp (-(t ^ 2))) := by
      simpa using (integrable_exp_neg_mul_sq (b := (1 : ℝ)) (by norm_num) :
        Integrable fun t : ℝ => Real.exp (-(1 : ℝ) * t ^ 2))
    exact hbase.const_mul A
  have hmeas : AEStronglyMeasurable (fun t : ℝ => weightIntegrandOdd z x t) :=
    (continuous_weightIntegrandOdd z hz hx).aestronglyMeasurable
  have hle : ∀ᵐ t : ℝ ∂(volume : Measure ℝ), ‖weightIntegrandOdd z x t‖ ≤ A * Real.exp (-(t ^ 2)) := by
    exact ae_of_all _ hAbound
  have hint : Integrable (fun t : ℝ => weightIntegrandOdd z x t) :=
    Integrable.mono' hg hmeas hle
  convert hint using 1
  ext t
  rfl

end PL.WeightConvergesOdd


open Complex DirichletCharacter Filter MeasureTheory Set
open scoped Real

set_option autoImplicit false

namespace PL.AFE

noncomputable section

variable {N : ℕ} [NeZero N]

/-- Bound on the Mellin-inverse vertical integral: for `x > 0`,
`‖mellinInv 1 F x‖ ≤ (1 / 2π) · ∫_ℝ ‖x^(-(1+It)) · F(1+It)‖ dt`. -/
lemma mellinInv_one_norm_le (F : ℂ → ℂ) {x : ℝ} :
    ‖mellinInv 1 F x‖ ≤ (1 / (2 * Real.pi)) * ∫ t : ℝ, ‖(x : ℂ) ^ (-(1 + I * (t : ℂ))) * F (1 + I * (t : ℂ))‖ := by
  rw [mellinInv]
  have hπ : (0 : ℝ) ≤ 1 / (2 * Real.pi) := by positivity
  have hle := MeasureTheory.norm_integral_le_integral_norm (μ := (volume : Measure ℝ))
    (f := fun y : ℝ => (x : ℂ) ^ (-(1 + y * I)) • F (1 + y * I))
  calc
    ‖(1 / (2 * Real.pi)) • (∫ y : ℝ, (x : ℂ) ^ (-(1 + y * I)) • F (1 + y * I))‖
        ≤ (1 / (2 * Real.pi)) * ‖(∫ y : ℝ, (x : ℂ) ^ (-(1 + y * I)) • F (1 + y * I))‖ := by
          rw [norm_smul, Real.norm_of_nonneg hπ]
    _ ≤ (1 / (2 * Real.pi)) * (∫ y : ℝ, ‖(x : ℂ) ^ (-(1 + y * I)) • F (1 + y * I)‖) := by
          exact mul_le_mul_of_nonneg_left hle hπ
    _ = (1 / (2 * Real.pi)) * ∫ t : ℝ, ‖(x : ℂ) ^ (-(1 + I * (t : ℂ))) * F (1 + I * (t : ℂ))‖ := by
          congr 1
          apply MeasureTheory.integral_congr_ae
          filter_upwards with t
          rw [show -(1 + (t : ℂ) * I) = -(1 + I * (t : ℂ)) by ring]
          rw [show 1 + (t : ℂ) * I = 1 + I * (t : ℂ) by ring]
          rw [norm_smul, norm_mul]

/-- The gamma-factor ratio appearing in the archimedean weight for an **even** character,
`γ(z + u)/γ(z) = Gammaℝ(z + u)/Gammaℝ z`, times the smoothing function and `u⁻¹`. -/
noncomputable def weightEven (z u : ℂ) : ℂ :=
  (Complex.Gammaℝ (z + u) / Complex.Gammaℝ z) * smoothingFunction u / u

/-- The gamma-factor ratio appearing in the archimedean weight for an **odd** character,
`γ(z + u)/γ(z) = Gammaℝ(z + 1 + u)/Gammaℝ(z + 1)`, times the smoothing function and `u⁻¹`. -/
noncomputable def weightOdd (z u : ℂ) : ℂ :=
  (Complex.Gammaℝ (z + 1 + u) / Complex.Gammaℝ (z + 1)) * smoothingFunction u / u

omit [NeZero N] in
/-- For an even character, the AFE weight equals the Mellin inverse of `weightEven z`. -/
lemma afeWeight_even (χ : DirichletCharacter ℂ N) (hχ : χ.Even) (z : ℂ) (x : ℝ) :
    afeWeight χ z x = mellinInv 1 (weightEven z) x := by
  unfold afeWeight
  rw [hχ.gammaFactor_def]
  congr 1
  funext u
  unfold weightEven
  rw [hχ.gammaFactor_def]

omit [NeZero N] in
/-- For an odd character, the AFE weight equals the Mellin inverse of `weightOdd z`. -/
lemma afeWeight_odd (χ : DirichletCharacter ℂ N) (hχ : χ.Odd) (z : ℂ) (x : ℝ) :
    afeWeight χ z x = mellinInv 1 (weightOdd z) x := by
  unfold afeWeight
  rw [hχ.gammaFactor_def]
  congr 1
  funext u
  unfold weightOdd
  rw [hχ.gammaFactor_def]
  rw [show z + u + 1 = z + 1 + u by ring]

/-- The integrand of the archimedean weight at `x = 1` (even case) is exactly
`weightEven z (1 + I·t)`. -/
lemma weightIntegrand_one_eq_weightEven (z : ℂ) (t : ℝ) :
    WeightConvergesEven.weightIntegrand z 1 t = weightEven z (1 + I * (t : ℂ)) := by
  rw [WeightConvergesEven.weightIntegrand, weightEven, smoothingFunction]
  norm_num
  rw [show z + 1 + I * (t : ℂ) = z + (1 + I * (t : ℂ)) by ring]

/-- The integrand of the archimedean weight at `x = 1` (odd case) is exactly
`weightOdd z (1 + I·t)`. -/
lemma weightIntegrand_one_eq_weightOdd (z : ℂ) (t : ℝ) :
    WeightConvergesOdd.weightIntegrandOdd z 1 t = weightOdd z (1 + I * (t : ℂ)) := by
  rw [WeightConvergesOdd.weightIntegrandOdd, weightOdd, smoothingFunction]
  norm_num
  rw [show z + 2 + I * (t : ℂ) = z + 1 + (1 + I * (t : ℂ)) by ring]

/-- Uniform vertical bound for `weightEven z` along the line `Re u = 1`, with Gaussian
decay in `t`. -/
lemma weightEven_vertical_bound (z : ℂ) (hz : 0 < z.re) :
    ∃ A : ℝ, 0 < A ∧ ∀ t : ℝ, ‖weightEven z (1 + I * (t : ℂ))‖ ≤ A * Real.exp (-(t ^ 2)) := by
  rcases WeightConvergesEven.weightIntegrand_norm_le z hz (x := (1 : ℝ)) (by norm_num) with ⟨A, hApos, hAb⟩
  refine ⟨A, hApos, ?_⟩
  intro t
  calc
    ‖weightEven z (1 + I * (t : ℂ))‖ = ‖WeightConvergesEven.weightIntegrand z 1 t‖ := by
      rw [weightIntegrand_one_eq_weightEven]
    _ ≤ A * Real.exp (-(t ^ 2)) := hAb t

/-- Uniform vertical bound for `weightOdd z` along the line `Re u = 1`, with Gaussian
decay in `t`. -/
lemma weightOdd_vertical_bound (z : ℂ) (hz : 0 < z.re) :
    ∃ A : ℝ, 0 < A ∧ ∀ t : ℝ, ‖weightOdd z (1 + I * (t : ℂ))‖ ≤ A * Real.exp (-(t ^ 2)) := by
  rcases WeightConvergesOdd.weightIntegrandOdd_norm_le z hz (x := (1 : ℝ)) (by norm_num) with ⟨A, hApos, hAb⟩
  refine ⟨A, hApos, ?_⟩
  intro t
  calc
    ‖weightOdd z (1 + I * (t : ℂ))‖ = ‖WeightConvergesOdd.weightIntegrandOdd z 1 t‖ := by
      rw [weightIntegrand_one_eq_weightOdd]
    _ ≤ A * Real.exp (-(t ^ 2)) := hAb t

/-- The function `t ↦ ‖weightEven z (1 + I·t)‖` is integrable. -/
lemma weightEven_vertical_abs_integrable (z : ℂ) (hz : 0 < z.re) :
    Integrable (fun t : ℝ => ‖weightEven z (1 + I * (t : ℂ))‖) := by
  have hI := WeightConvergesEven.weightIntegrand_integrable z hz (x := (1 : ℝ)) (by norm_num)
  have hIn := hI.norm
  rw [show (fun t : ℝ => ‖weightEven z (1 + I * (t : ℂ))‖) = (fun t : ℝ => ‖WeightConvergesEven.weightIntegrand z 1 t‖) by
    funext t
    rw [← weightIntegrand_one_eq_weightEven]]
  exact hIn

/-- The function `t ↦ ‖weightOdd z (1 + I·t)‖` is integrable. -/
lemma weightOdd_vertical_abs_integrable (z : ℂ) (hz : 0 < z.re) :
    Integrable (fun t : ℝ => ‖weightOdd z (1 + I * (t : ℂ))‖) := by
  have hI := WeightConvergesOdd.weightIntegrandOdd_integrable z hz (x := (1 : ℝ)) (by norm_num)
  have hIn := hI.norm
  rw [show (fun t : ℝ => ‖weightOdd z (1 + I * (t : ℂ))‖) = (fun t : ℝ => ‖WeightConvergesOdd.weightIntegrandOdd z 1 t‖) by
    funext t
    rw [← weightIntegrand_one_eq_weightOdd]]
  exact hIn

omit [NeZero N] in
/-- Pointwise identity `‖x^(-(1+It))‖ = x⁻¹` for `x > 0` (complex cpow norm). -/
lemma norm_cpow_neg_one_add_mul_I (x : ℝ) (hx : 0 < x) (t : ℝ) :
    ‖(x : ℂ) ^ (-(1 + I * (t : ℂ)))‖ = x⁻¹ := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp
  rw [Real.rpow_neg_one]

omit [NeZero N] in
/-- Bound for the even archimedean weight: `‖W_z(x)‖ ≤ C(z) · x⁻¹` for all `x > 0`. -/
theorem even_weight_afe_norm_le_exists (z : ℂ) (hz : 0 < z.re) :
    ∃ C : ℝ, 0 < C ∧ ∀ {x : ℝ}, 0 < x → ‖mellinInv 1 (weightEven z) x‖ ≤ C * x⁻¹ := by
  rcases weightEven_vertical_bound z hz with ⟨A, hApos, hAb⟩
  let C : ℝ := A * (1 / (2 * Real.pi)) * (∫ t : ℝ, Real.exp (-(t ^ 2)))
  have hCpos : 0 < C := by
    have hInt : 0 < ∫ t : ℝ, Real.exp (-(t ^ 2)) := by
      rw [show (fun t : ℝ => Real.exp (-(t ^ 2))) = (fun t : ℝ => Real.exp (-(1 : ℝ) * t ^ 2)) by
        funext t
        congr 1
        ring]
      rw [integral_gaussian (b := (1 : ℝ))]
      positivity
    dsimp [C]
    positivity
  refine ⟨C, hCpos, ?_⟩
  intro x hx
  have hf : Integrable (fun t : ℝ => ‖weightEven z (1 + I * (t : ℂ))‖) := weightEven_vertical_abs_integrable z hz
  have hg : Integrable (fun t : ℝ => A * Real.exp (-(t ^ 2))) := by
    have hbase : Integrable (fun t : ℝ => Real.exp (-(t ^ 2))) := by
      simpa using (integrable_exp_neg_mul_sq (b := (1 : ℝ)) (by norm_num) :
        Integrable fun t : ℝ => Real.exp (-(1 : ℝ) * t ^ 2))
    exact hbase.const_mul A
  have hle : ∀ᵐ t : ℝ ∂(volume : Measure ℝ), ‖weightEven z (1 + I * (t : ℂ))‖ ≤ A * Real.exp (-(t ^ 2)) := by
    exact ae_of_all _ hAb
  calc
    ‖mellinInv 1 (weightEven z) x‖
        ≤ (1 / (2 * Real.pi)) * ∫ t : ℝ, ‖(x : ℂ) ^ (-(1 + I * (t : ℂ))) * weightEven z (1 + I * (t : ℂ))‖ := by
          exact mellinInv_one_norm_le (weightEven z) (x := x)
    _ = (1 / (2 * Real.pi)) * ∫ t : ℝ, x⁻¹ * ‖weightEven z (1 + I * (t : ℂ))‖ := by
          congr 1
          apply MeasureTheory.integral_congr_ae
          filter_upwards with t
          rw [norm_mul, norm_cpow_neg_one_add_mul_I x hx t]
    _ = x⁻¹ * ((1 / (2 * Real.pi)) * ∫ t : ℝ, ‖weightEven z (1 + I * (t : ℂ))‖) := by
          rw [MeasureTheory.integral_const_mul]
          ring
    _ ≤ x⁻¹ * ((1 / (2 * Real.pi)) * ∫ t : ℝ, A * Real.exp (-(t ^ 2))) := by
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (integral_mono_ae hf hg hle) (by positivity)) (inv_nonneg.mpr (le_of_lt hx))
    _ = x⁻¹ * ((1 / (2 * Real.pi)) * (A * (∫ t : ℝ, Real.exp (-(t ^ 2))))) := by
          congr 1
          rw [MeasureTheory.integral_const_mul]
    _ = C * x⁻¹ := by
          dsimp [C]
          ring

omit [NeZero N] in
/-- Bound for the odd archimedean weight: `‖W_z(x)‖ ≤ C(z) · x⁻¹` for all `x > 0`. -/
theorem odd_weight_afe_norm_le_exists (z : ℂ) (hz : 0 < z.re) :
    ∃ C : ℝ, 0 < C ∧ ∀ {x : ℝ}, 0 < x → ‖mellinInv 1 (weightOdd z) x‖ ≤ C * x⁻¹ := by
  rcases weightOdd_vertical_bound z hz with ⟨A, hApos, hAb⟩
  let C : ℝ := A * (1 / (2 * Real.pi)) * (∫ t : ℝ, Real.exp (-(t ^ 2)))
  have hCpos : 0 < C := by
    have hInt : 0 < ∫ t : ℝ, Real.exp (-(t ^ 2)) := by
      rw [show (fun t : ℝ => Real.exp (-(t ^ 2))) = (fun t : ℝ => Real.exp (-(1 : ℝ) * t ^ 2)) by
        funext t
        congr 1
        ring]
      rw [integral_gaussian (b := (1 : ℝ))]
      positivity
    dsimp [C]
    positivity
  refine ⟨C, hCpos, ?_⟩
  intro x hx
  have hf : Integrable (fun t : ℝ => ‖weightOdd z (1 + I * (t : ℂ))‖) := weightOdd_vertical_abs_integrable z hz
  have hg : Integrable (fun t : ℝ => A * Real.exp (-(t ^ 2))) := by
    have hbase : Integrable (fun t : ℝ => Real.exp (-(t ^ 2))) := by
      simpa using (integrable_exp_neg_mul_sq (b := (1 : ℝ)) (by norm_num) :
        Integrable fun t : ℝ => Real.exp (-(1 : ℝ) * t ^ 2))
    exact hbase.const_mul A
  have hle : ∀ᵐ t : ℝ ∂(volume : Measure ℝ), ‖weightOdd z (1 + I * (t : ℂ))‖ ≤ A * Real.exp (-(t ^ 2)) := by
    exact ae_of_all _ hAb
  calc
    ‖mellinInv 1 (weightOdd z) x‖
        ≤ (1 / (2 * Real.pi)) * ∫ t : ℝ, ‖(x : ℂ) ^ (-(1 + I * (t : ℂ))) * weightOdd z (1 + I * (t : ℂ))‖ := by
          exact mellinInv_one_norm_le (weightOdd z) (x := x)
    _ = (1 / (2 * Real.pi)) * ∫ t : ℝ, x⁻¹ * ‖weightOdd z (1 + I * (t : ℂ))‖ := by
          congr 1
          apply MeasureTheory.integral_congr_ae
          filter_upwards with t
          rw [norm_mul, norm_cpow_neg_one_add_mul_I x hx t]
    _ = x⁻¹ * ((1 / (2 * Real.pi)) * ∫ t : ℝ, ‖weightOdd z (1 + I * (t : ℂ))‖) := by
          rw [MeasureTheory.integral_const_mul]
          ring
    _ ≤ x⁻¹ * ((1 / (2 * Real.pi)) * ∫ t : ℝ, A * Real.exp (-(t ^ 2))) := by
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (integral_mono_ae hf hg hle) (by positivity)) (inv_nonneg.mpr (le_of_lt hx))
    _ = x⁻¹ * ((1 / (2 * Real.pi)) * (A * (∫ t : ℝ, Real.exp (-(t ^ 2))))) := by
          congr 1
          rw [MeasureTheory.integral_const_mul]
    _ = C * x⁻¹ := by
          dsimp [C]
          ring


lemma sqrt_ne_zero_of_ne_zero {N : ℕ} (hN : N ≠ 0) : Real.sqrt (N : ℝ) ≠ 0 := by
  exact (Real.sqrt_pos.2 (by exact_mod_cast (Nat.pos_of_ne_zero hN))).ne'

/-- norm of the character at a natural. -/
lemma norm_char_nat_le_one (χ : DirichletCharacter ℂ N) (n : ℕ) : ‖χ n‖ ≤ 1 := by
  exact χ.norm_le_one (n : ZMod N)

/-- `‖(n : ℂ) ^ (-s)‖ = (n : ℝ) ^ (-s.re)` for positive `n`. -/
lemma norm_nat_cpow_neg (n : ℕ) (hn : n ≠ 0) (s : ℂ) :
    ‖(n : ℂ) ^ (-s)‖ = (n : ℝ) ^ (-s.re) := by
  rw [← Complex.ofReal_natCast]
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast (Nat.pos_of_ne_zero hn))]
  rw [Complex.neg_re]

/-- The inv of the AFE scale is `√N / n` for positive `n`. -/
lemma inv_afeScale (n : ℕ) (hn : n ≠ 0) :
    (afeScale N n)⁻¹ = Real.sqrt (N : ℝ) / (n : ℝ) := by
  dsimp [afeScale]
  field_simp [Nat.cast_ne_zero.mpr hn, sqrt_ne_zero_of_ne_zero (NeZero.ne N)]



/-- Algebraic identity for the summability bound:
`a^(-σ) · (a/√N)⁻¹ = √N · a^(-(1+σ))` for `a = m+1 > 0`. -/
lemma scale_pow_inv (σ : ℝ) (m : ℕ) (hN : N ≠ 0) :
    (((m + 1 : ℕ) : ℝ) ^ (-σ)) * (afeScale N (m + 1))⁻¹
      = Real.sqrt (N : ℝ) * (((m + 1 : ℕ) : ℝ) ^ (-(1 + σ))) := by
  have hnpos : 0 < ((m + 1 : ℕ) : ℝ) := by exact_mod_cast (Nat.succ_pos m)
  have hn0 : ((m + 1 : ℕ) : ℝ) ≠ 0 := hnpos.ne'
  have hsqrt0 : Real.sqrt (N : ℝ) ≠ 0 := (Real.sqrt_pos.2 (by exact_mod_cast (Nat.pos_of_ne_zero hN))).ne'
  dsimp [afeScale]
  calc
    (((m + 1 : ℕ) : ℝ) ^ (-σ)) * (((m + 1 : ℕ) : ℝ) / Real.sqrt (N : ℝ))⁻¹
        = (((m + 1 : ℕ) : ℝ) ^ (-σ)) * (Real.sqrt (N : ℝ) / ((m + 1 : ℕ) : ℝ)) := by
          congr 1
          field_simp [hn0, hsqrt0]
    _ = (((m + 1 : ℕ) : ℝ) ^ (-σ)) * (Real.sqrt (N : ℝ) * (((m + 1 : ℕ) : ℝ)⁻¹)) := by
          rw [div_eq_mul_inv]
    _ = Real.sqrt (N : ℝ) * (((m + 1 : ℕ) : ℝ) ^ (-σ) * (((m + 1 : ℕ) : ℝ)⁻¹)) := by ring
    _ = Real.sqrt (N : ℝ) * (((m + 1 : ℕ) : ℝ) ^ (-σ) * (((m + 1 : ℕ) : ℝ) ^ (-1 : ℝ))) := by
          congr 1
          rw [← Real.rpow_neg_one]
    _ = Real.sqrt (N : ℝ) * (((m + 1 : ℕ) : ℝ) ^ ((-σ) + (-1 : ℝ))) := by
          congr 1
          rw [← Real.rpow_add hnpos]
    _ = Real.sqrt (N : ℝ) * (((m + 1 : ℕ) : ℝ) ^ (-(1 + σ))) := by
          congr 2
          ring

/-- Core absolute-summability statement with a general bounded coefficient `g`, a smooth
even weight at base point `w` (`0 < Re w`), and exponent `s`. -/
theorem summable_smooth_evenWeight (g : ℕ → ℂ) (hg : ∀ n : ℕ, ‖g n‖ ≤ 1) (w : ℂ)
    (hw0 : 0 < w.re) (s : ℂ) (hs0 : 0 < s.re) :
    Summable (fun n : ℕ => g n * (n : ℂ) ^ (-s) * mellinInv 1 (weightEven w) (afeScale N n)) := by
  rcases even_weight_afe_norm_le_exists w hw0 with ⟨C, hCpos, hC⟩
  have hW : ∀ {x : ℝ}, 0 < x → ‖mellinInv 1 (weightEven w) x‖ ≤ C * x⁻¹ := by
    intro x hx
    exact hC hx
  let term : ℕ → ℂ := fun n => g n * (n : ℂ) ^ (-s) * mellinInv 1 (weightEven w) (afeScale N n)
  have htail : Summable (fun m : ℕ => ‖term (m + 1)‖) := by
    let b : ℕ → ℝ := fun m => C * Real.sqrt (N : ℝ) * (((m + 1 : ℕ) : ℝ) ^ (-(1 + s.re)))
    have hbs : Summable b := by
      have hbase : Summable (fun n : ℕ => (n : ℝ) ^ (-(1 + s.re))) := by
        exact Real.summable_nat_rpow.mpr (by linarith)
      have hbase' : Summable (fun m : ℕ => ((m + 1 : ℕ) : ℝ) ^ (-(1 + s.re))) := by
        exact (summable_nat_add_iff 1).2 hbase
      dsimp [b]
      exact hbase'.mul_left (C * Real.sqrt (N : ℝ))
    refine Summable.of_nonneg_of_le (fun m => norm_nonneg _) ?_ hbs
    intro m
    have hn0 : (m + 1 : ℕ) ≠ 0 := by omega
    have hpos : 0 < afeScale N (m + 1) := by
      dsimp [afeScale]
      exact div_pos (by exact_mod_cast (Nat.succ_pos m))
        (Real.sqrt_pos.2 (by exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne N))))
    calc
      ‖term (m + 1)‖
          = ‖g (m + 1)‖ * ‖((m + 1 : ℕ) : ℂ) ^ (-s)‖ * ‖mellinInv 1 (weightEven w) (afeScale N (m + 1))‖ := by
            dsimp [term]
            simp [norm_mul, mul_assoc]
      _ = ‖g (m + 1)‖ * (((m + 1 : ℕ) : ℝ) ^ (-s.re)) * ‖mellinInv 1 (weightEven w) (afeScale N (m + 1))‖ := by
            rw [norm_nat_cpow_neg (m + 1) hn0 s]
      _ ≤ 1 * (((m + 1 : ℕ) : ℝ) ^ (-s.re)) * (C * (afeScale N (m + 1))⁻¹) := by
            gcongr
            · exact hg (m + 1)
            · exact hW hpos
      _ = C * ((((m + 1 : ℕ) : ℝ) ^ (-s.re)) * ((afeScale N (m + 1))⁻¹)) := by ring
      _ = C * (Real.sqrt (N : ℝ) * (((m + 1 : ℕ) : ℝ) ^ (-(1 + s.re)))) := by
            rw [scale_pow_inv s.re m (NeZero.ne N)]
      _ ≤ C * Real.sqrt (N : ℝ) * (((m + 1 : ℕ) : ℝ) ^ (-(1 + s.re))) := by
            exact le_of_eq (by ring)
  exact Summable.of_norm ((summable_nat_add_iff 1).1 htail)

/-- The main smoothed Dirichlet series converges absolutely for `0 < Re s` (even characters). -/
theorem summable_main_even (χ : DirichletCharacter ℂ N) (hχ : χ.Even) {s : ℂ} (hs0 : 0 < s.re) :
    Summable (fun n : ℕ => χ n * (n : ℂ) ^ (-s) * afeWeight χ s (afeScale N n)) := by
  rw [show (fun n : ℕ => χ n * (n : ℂ) ^ (-s) * afeWeight χ s (afeScale N n)) =
            (fun n : ℕ => χ n * (n : ℂ) ^ (-s) * mellinInv 1 (weightEven s) (afeScale N n)) by
        funext n
        rw [afeWeight_even χ hχ s (afeScale N n)]]
  exact summable_smooth_evenWeight (N := N) (fun n : ℕ => χ n)
    (fun n => norm_char_nat_le_one χ n) s hs0 s hs0

/-- Core absolute-summability statement with a general bounded coefficient `g`, a smooth
odd weight at base point `w` (`0 < Re w`), and exponent `s`. -/
theorem summable_smooth_oddWeight (g : ℕ → ℂ) (hg : ∀ n : ℕ, ‖g n‖ ≤ 1) (w : ℂ)
    (hw0 : 0 < w.re) (s : ℂ) (hs0 : 0 < s.re) :
    Summable (fun n : ℕ => g n * (n : ℂ) ^ (-s) * mellinInv 1 (weightOdd w) (afeScale N n)) := by
  rcases odd_weight_afe_norm_le_exists w hw0 with ⟨C, hCpos, hC⟩
  have hW : ∀ {x : ℝ}, 0 < x → ‖mellinInv 1 (weightOdd w) x‖ ≤ C * x⁻¹ := by
    intro x hx
    exact hC hx
  let term : ℕ → ℂ := fun n => g n * (n : ℂ) ^ (-s) * mellinInv 1 (weightOdd w) (afeScale N n)
  have htail : Summable (fun m : ℕ => ‖term (m + 1)‖) := by
    let b : ℕ → ℝ := fun m => C * Real.sqrt (N : ℝ) * (((m + 1 : ℕ) : ℝ) ^ (-(1 + s.re)))
    have hbs : Summable b := by
      have hbase : Summable (fun n : ℕ => (n : ℝ) ^ (-(1 + s.re))) := by
        exact Real.summable_nat_rpow.mpr (by linarith)
      have hbase' : Summable (fun m : ℕ => ((m + 1 : ℕ) : ℝ) ^ (-(1 + s.re))) := by
        exact (summable_nat_add_iff 1).2 hbase
      dsimp [b]
      exact hbase'.mul_left (C * Real.sqrt (N : ℝ))
    refine Summable.of_nonneg_of_le (fun m => norm_nonneg _) ?_ hbs
    intro m
    have hn0 : (m + 1 : ℕ) ≠ 0 := by omega
    have hpos : 0 < afeScale N (m + 1) := by
      dsimp [afeScale]
      exact div_pos (by exact_mod_cast (Nat.succ_pos m))
        (Real.sqrt_pos.2 (by exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne N))))
    calc
      ‖term (m + 1)‖
          = ‖g (m + 1)‖ * ‖((m + 1 : ℕ) : ℂ) ^ (-s)‖ * ‖mellinInv 1 (weightOdd w) (afeScale N (m + 1))‖ := by
            dsimp [term]
            simp [norm_mul, mul_assoc]
      _ = ‖g (m + 1)‖ * (((m + 1 : ℕ) : ℝ) ^ (-s.re)) * ‖mellinInv 1 (weightOdd w) (afeScale N (m + 1))‖ := by
            rw [norm_nat_cpow_neg (m + 1) hn0 s]
      _ ≤ 1 * (((m + 1 : ℕ) : ℝ) ^ (-s.re)) * (C * (afeScale N (m + 1))⁻¹) := by
            gcongr
            · exact hg (m + 1)
            · exact hW hpos
      _ = C * ((((m + 1 : ℕ) : ℝ) ^ (-s.re)) * ((afeScale N (m + 1))⁻¹)) := by ring
      _ = C * (Real.sqrt (N : ℝ) * (((m + 1 : ℕ) : ℝ) ^ (-(1 + s.re)))) := by
            rw [scale_pow_inv s.re m (NeZero.ne N)]
      _ ≤ C * Real.sqrt (N : ℝ) * (((m + 1 : ℕ) : ℝ) ^ (-(1 + s.re))) := by
            exact le_of_eq (by ring)
  exact Summable.of_norm ((summable_nat_add_iff 1).1 htail)

/-- The main smoothed Dirichlet series converges absolutely for `0 < Re s` (odd characters). -/
theorem summable_main_odd (χ : DirichletCharacter ℂ N) (hχ : χ.Odd) {s : ℂ} (hs0 : 0 < s.re) :
    Summable (fun n : ℕ => χ n * (n : ℂ) ^ (-s) * afeWeight χ s (afeScale N n)) := by
  have hgen := summable_smooth_oddWeight (N := N) (fun n : ℕ => χ n)
    (fun n => norm_char_nat_le_one χ n) s hs0 s hs0
  convert hgen using 1
  ext n
  rw [afeWeight_odd χ hχ s (afeScale N n)]

/-- The main smoothed Dirichlet series converges absolutely for `0 < Re s`. -/
theorem summable_main (χ : DirichletCharacter ℂ N) {s : ℂ} (hs0 : 0 < s.re) :
    Summable (fun n : ℕ => χ n * (n : ℂ) ^ (-s) * afeWeight χ s (afeScale N n)) := by
  rcases χ.even_or_odd with hχ | hχ
  · exact summable_main_even χ hχ hs0
  · exact summable_main_odd χ hχ hs0

/-- The dual smoothed Dirichlet series converges absolutely for `Re s < 1` (even characters). -/
theorem summable_dual_even (χ : DirichletCharacter ℂ N) (hχ : χ.Even) {s : ℂ} (hs1 : s.re < 1) :
    Summable (fun n : ℕ => (χ⁻¹) n * (n : ℂ) ^ (-(1 - s)) * afeWeight χ (1 - s) (afeScale N n)) := by
  have hs1' : 0 < (1 - s).re := by
    rw [Complex.sub_re, Complex.one_re]
    linarith
  rw [show (fun n : ℕ => (χ⁻¹) n * (n : ℂ) ^ (-(1 - s)) * afeWeight χ (1 - s) (afeScale N n)) =
            (fun n : ℕ => (χ⁻¹) n * (n : ℂ) ^ (-(1 - s)) * mellinInv 1 (weightEven (1 - s)) (afeScale N n)) by
        funext n
        rw [afeWeight_even χ hχ (1 - s) (afeScale N n)]]
  exact summable_smooth_evenWeight (N := N) (fun n : ℕ => (χ⁻¹) n)
    (fun n => norm_char_nat_le_one (χ⁻¹) n) (1 - s) hs1' (1 - s) hs1'

/-- The dual smoothed Dirichlet series converges absolutely for `Re s < 1` (odd characters). -/
theorem summable_dual_odd (χ : DirichletCharacter ℂ N) (hχ : χ.Odd) {s : ℂ} (hs1 : s.re < 1) :
    Summable (fun n : ℕ => (χ⁻¹) n * (n : ℂ) ^ (-(1 - s)) * afeWeight χ (1 - s) (afeScale N n)) := by
  have hs1' : 0 < (1 - s).re := by
    rw [Complex.sub_re, Complex.one_re]
    linarith
  have hgen := summable_smooth_oddWeight (N := N) (fun n : ℕ => (χ⁻¹) n)
    (fun n => norm_char_nat_le_one (χ⁻¹) n) (1 - s) hs1' (1 - s) hs1'
  convert hgen using 1
  ext n
  rw [afeWeight_odd χ hχ (1 - s) (afeScale N n)]

/-- The dual smoothed Dirichlet series converges absolutely for `Re s < 1`. -/
theorem summable_dual (χ : DirichletCharacter ℂ N) {s : ℂ} (hs1 : s.re < 1) :
    Summable (fun n : ℕ => (χ⁻¹) n * (n : ℂ) ^ (-(1 - s)) * afeWeight χ (1 - s) (afeScale N n)) := by
  rcases χ.even_or_odd with hχ | hχ
  · exact summable_dual_even χ hχ hs1
  · exact summable_dual_odd χ hχ hs1

end
end PL.AFE


open Complex DirichletCharacter Filter MeasureTheory Set
open PL.AFE
open scoped Real

set_option autoImplicit false

namespace PL.AfeMellin

variable {N : ℕ} [NeZero N]

/-- `mellinInv 1 f 0 = 0`: the Mellin-inverse kernel vanishes at `x = 0`. -/
lemma mellinInv_one_apply_zero (f : ℂ → ℂ) : mellinInv 1 f 0 = 0 := by
  unfold mellinInv
  have hz : ∀ y : ℝ, (↑(0 : ℝ) : ℂ) ^ (-(((1 : ℝ) : ℂ) + (y : ℂ) * I)) • f (((1 : ℝ) : ℂ) + (y : ℂ) * I) = 0 := by
    intro y
    have hne : (((1 : ℝ) : ℂ) + (y : ℂ) * I) ≠ 0 := by
      intro h
      have hre := congrArg Complex.re h
      simp at hre
    rw [ofReal_zero]
    rw [zero_cpow (neg_ne_zero.mpr hne)]
    rw [smul_eq_mul, zero_mul]
  have hfun : (fun y : ℝ => (↑(0 : ℝ) : ℂ) ^ (-(((1 : ℝ) : ℂ) + (y : ℂ) * I)) • f (((1 : ℝ) : ℂ) + (y : ℂ) * I)) = 0 :=
    funext hz
  rw [hfun]
  simp

/-- The Dirichlet series of a character equals the L-function for `1 < Re z`
(tsum form, term `χ n * n^(-z)`, the `n = 0` term vanishes since `z ≠ 0`). -/
lemma inner_series_eq_LFunction (χ : DirichletCharacter ℂ N) {z : ℂ} (hz : 1 < z.re) :
    (∑' n : ℕ, χ n * (n : ℂ) ^ (-z)) = DirichletCharacter.LFunction χ z := by
  rw [DirichletCharacter.LFunction_eq_LSeries χ hz]
  unfold LSeries
  apply tsum_congr
  intro n
  by_cases hn : n = 0
  · subst n
    have hz0 : z ≠ 0 := by
      intro h
      rw [h] at hz
      norm_num at hz
    rw [LSeries.term]
    simp
    exact Or.inr hz0
  · rw [LSeries.term_of_ne_zero hn]
    rw [div_eq_mul_inv, ← cpow_neg]

/-- For `0 < Re s`, `DirichletCharacter.completedLFunction χ s = gammaFactor χ s * DirichletCharacter.LFunction χ s`. -/
lemma completedLFunction_eq_gamma_mul_L (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 0 < s.re) :
    DirichletCharacter.completedLFunction χ s = χ.gammaFactor s * DirichletCharacter.LFunction χ s := by
  have hL := Structural.LFunction_eq_completed_div_gammaFactor_of_zero_lt_re χ hs
  have hg : χ.gammaFactor s ≠ 0 := Structural.gammaFactor_ne_zero_of_zero_lt_re χ hs
  calc
    DirichletCharacter.completedLFunction χ s = DirichletCharacter.completedLFunction χ s / χ.gammaFactor s * χ.gammaFactor s := by
      field_simp [hg]
    _ = DirichletCharacter.LFunction χ s * χ.gammaFactor s := by rw [← hL]
    _ = χ.gammaFactor s * DirichletCharacter.LFunction χ s := by ring

/-- The `n = 0` term of the main smoothed sum vanishes (here `hs : s ≠ 0`; note
`0 < Re s` implies it). -/
lemma term_zero (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : s ≠ 0) :
    χ 0 * (0 : ℂ) ^ (-s) * afeWeight χ s (afeScale N 0) = 0 := by
  have hx : afeScale N 0 = 0 := by simp [afeScale]
  rw [hx]
  unfold afeWeight
  rw [mellinInv_one_apply_zero]
  simp

/-- Pointwise scale identity for the Mellin kernel: for `n ≠ 0` and real `y`,
`(n/√N)^(-(1+yI)) = n^(-(1+yI)) * (√N)^(1+yI)` (complex cpow). -/
lemma scale_cpow (n : ℕ) (hn : n ≠ 0) (y : ℝ) :
    ((afeScale N n : ℝ) : ℂ) ^ (-(1 + (y : ℂ) * I)) =
      (n : ℂ) ^ (-(1 + (y : ℂ) * I)) * ((Real.sqrt (N : ℝ) : ℂ) ^ (1 + (y : ℂ) * I)) := by
  have hN : 0 ≤ (Real.sqrt (N : ℝ)) := Real.sqrt_nonneg _
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hn)
  calc
    ((afeScale N n : ℝ) : ℂ) ^ (-(1 + (y : ℂ) * I))
        = (((n : ℝ) / Real.sqrt (N : ℝ) : ℝ) : ℂ) ^ (-(1 + (y : ℂ) * I)) := by
          simp [afeScale]
    _ = (((n : ℝ) : ℂ) / (Real.sqrt (N : ℝ) : ℂ)) ^ (-(1 + (y : ℂ) * I)) := by
          norm_cast
    _ = ((n : ℝ) : ℂ) ^ (-(1 + (y : ℂ) * I)) / ((Real.sqrt (N : ℝ) : ℂ) ^ (-(1 + (y : ℂ) * I))) := by
          rw [div_cpow_ofReal_nonneg (le_of_lt hnpos) hN]
    _ = (n : ℂ) ^ (-(1 + (y : ℂ) * I)) * ((Real.sqrt (N : ℝ) : ℂ) ^ (1 + (y : ℂ) * I)) := by
          rw [div_eq_mul_inv]
          congr 1
          rw [← cpow_neg]
          congr 1
          ring


/-- The scale-kernel series equals `(√N)^(1+yI) · L(χ, s+1+yI)` for `0 < Re s`. -/
lemma scale_series_eq (χ : DirichletCharacter ℂ N) {s : ℂ} (hs0 : 0 < s.re) (y : ℝ) :
    (∑' n : ℕ, χ n * (n : ℂ) ^ (-s) * ((afeScale N n : ℝ) : ℂ) ^ (-(1 + (y : ℂ) * I)))
      = ((Real.sqrt (N : ℝ) : ℂ) ^ (1 + (y : ℂ) * I)) * DirichletCharacter.LFunction χ (s + 1 + (y : ℂ) * I) := by
  let g : ℂ := (Real.sqrt (N : ℝ) : ℂ) ^ (1 + (y : ℂ) * I)
  let inner : ℕ → ℂ := fun n => χ n * (n : ℂ) ^ (-(s + 1 + (y : ℂ) * I))
  have hpt : ∀ n : ℕ,
      χ n * (n : ℂ) ^ (-s) * ((afeScale N n : ℝ) : ℂ) ^ (-(1 + (y : ℂ) * I)) = g * inner n := by
    intro n
    by_cases hn : n = 0
    · subst n
      dsimp [inner, g]
      have h1y : (1 + (y : ℂ) * I) ≠ 0 := by
        intro h
        have hre := congrArg Complex.re h
        simp at hre
      have hs' : s ≠ 0 := by
        intro h
        rw [h] at hs0
        norm_num at hs0
      have hk : ((0 : ℝ) : ℂ) ^ (-(1 + (y : ℂ) * I)) = 0 := by
        rw [ofReal_zero]
        exact zero_cpow (neg_ne_zero.mpr h1y)
      have hz2 : (↑(0 : ℕ) : ℂ) ^ (-(s + 1 + (y : ℂ) * I)) = 0 := by
        rw [Nat.cast_zero]
        apply zero_cpow
        apply neg_ne_zero.mpr
        intro h
        have hre := congrArg Complex.re h
        simp at hre
        linarith
      rw [show afeScale N 0 = 0 by simp [afeScale]]
      rw [hk, hz2]
      ring
    · have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn
      have hpow : (n : ℂ) ^ (-s) * (n : ℂ) ^ (-(1 + (y : ℂ) * I)) = (n : ℂ) ^ (-(s + 1 + (y : ℂ) * I)) := by
        rw [← cpow_add (x := (n : ℂ)) (-s) (-(1 + (y : ℂ) * I)) hn0]
        congr 1
        ring
      calc
        χ n * (n : ℂ) ^ (-s) * ((afeScale N n : ℝ) : ℂ) ^ (-(1 + (y : ℂ) * I))
            = χ n * (n : ℂ) ^ (-s) * ((n : ℂ) ^ (-(1 + (y : ℂ) * I)) * (Real.sqrt (N : ℝ) : ℂ) ^ (1 + (y : ℂ) * I)) := by
              rw [scale_cpow n hn y]
        _ = (χ n * (n : ℂ) ^ (-s) * (n : ℂ) ^ (-(1 + (y : ℂ) * I))) * (Real.sqrt (N : ℝ) : ℂ) ^ (1 + (y : ℂ) * I) := by
              ring
        _ = (χ n * ((n : ℂ) ^ (-s) * (n : ℂ) ^ (-(1 + (y : ℂ) * I)))) * (Real.sqrt (N : ℝ) : ℂ) ^ (1 + (y : ℂ) * I) := by
              ring
        _ = (χ n * (n : ℂ) ^ (-(s + 1 + (y : ℂ) * I))) * (Real.sqrt (N : ℝ) : ℂ) ^ (1 + (y : ℂ) * I) := by
              rw [hpow]
        _ = g * inner n := by
              dsimp [g, inner]
              ring
  calc
    (∑' n : ℕ, χ n * (n : ℂ) ^ (-s) * ((afeScale N n : ℝ) : ℂ) ^ (-(1 + (y : ℂ) * I)))
        = ∑' n : ℕ, g * inner n := tsum_congr (fun n => hpt n)
    _ = g * ∑' n : ℕ, inner n := by
          have h : (∑' n : ℕ, g • inner n) = g • (∑' n : ℕ, inner n) := tsum_const_smul'' (g := g) (f := inner)
          simpa [smul_eq_mul] using h
    _ = g * DirichletCharacter.LFunction χ (s + 1 + (y : ℂ) * I) := by
          congr 1
          unfold inner
          exact inner_series_eq_LFunction χ (z := s + 1 + (y : ℂ) * I) (by
            simp
            linarith)


/-- The gamma-ratio factor of the Mellin kernel along the vertical line `u = 1 + y·I`:
`W(s,y) = γ(s+1+yI)/γ(s) · g(1+yI)/(1+yI)`, where `γ = χ.gammaFactor` and `g` is the
smoothing function.  (This is `Q(1 + y·I)` for `Q(u) = γ(s+u)/γ(s)·g(u)/u`.) -/
noncomputable def W (χ : DirichletCharacter ℂ N) (s : ℂ) (y : ℝ) : ℂ :=
  χ.gammaFactor (s + 1 + I * (y : ℂ)) / χ.gammaFactor s * smoothingFunction (1 + I * (y : ℂ))
    / (1 + I * (y : ℂ))


/-- The real scalar action on `ℂ` is multiplication by the embedded scalar. -/
lemma real_smul_eq_mul (r : ℝ) (z : ℂ) : r • z = (r : ℂ) * z := by
  rw [Algebra.smul_def, Complex.coe_algebraMap]


end PL.AfeMellin


open Complex DirichletCharacter Filter MeasureTheory Set
open PL.AFE
open scoped Real

set_option autoImplicit false

/-!
# Weight analysis for the Mellin-inversion step (T1)

For a character `χ` of modulus `N`, a point `s` with `0 < Re s`, the vertical-line weight
`W χ s y = γ(s+1+Iy)/γ(s) · g(1+Iy)/(1+Iy)` (`γ = χ.gammaFactor`, `g(u) = exp(u²)`)
satisfies:

1. `exists_W_abs_bound`: `∃ A > 0, ∀ y, ‖W χ s y‖ ≤ A · exp(-y²)`  (Gaussian decay),
2. `continuous_W`: `y ↦ W χ s y` is continuous,
3. `W_abs_integrable`: `y ↦ ‖W χ s y‖` is Bochner-integrable.

## Proof strategy (parity branching)

`χ.Even ∨ χ.Odd` (`χ.even_or_odd`).

Even case: `χ.gammaFactor z = Gammaℝ z` (`DirichletCharacter.Even.gammaFactor_def`), so
`W χ s y = WeightConvergesEven.weightIntegrand s 1 y` (the integrand of the archimedean
weight at `x = 1`; unfold `weightIntegrand` and `smoothingFunction`, rewrite the two
gamma factors, then `simp`).  Then use

* `PL.WeightConvergesEven.weightIntegrand_norm_le` (Gaussian decay) for (1),
* `PL.WeightConvergesEven.continuous_weightIntegrand` for (2),
* `(1)` + measurability from (2) gives (3) via `MeasureTheory.Integrable.mono` against
  `A * Real.exp (-y^2)` (integrable via `integrable_exp_neg_mul_sq`).

Odd case: `χ.gammaFactor z = Gammaℝ (z+1)` (`DirichletCharacter.Odd.gammaFactor_def`), and
`W χ s y = WeightConvergesOdd.weightIntegrandOdd s 1 y` (`weightIntegrandOdd` has
`Gammaℝ (z+2+Iy)/Gammaℝ (z+1)`), using `PL.WeightConvergesOdd.weightIntegrandOdd_norm_le`
and `continuous_weightIntegrandOdd`.
-/

namespace PL.AfeMellin

variable {N : ℕ} [NeZero N]

/-- Gaussian decay of the vertical-line weight `W χ s y`. -/
theorem exists_W_abs_bound (χ : DirichletCharacter ℂ N) {s : ℂ} (hs0 : 0 < s.re) :
    ∃ A : ℝ, 0 < A ∧ ∀ y : ℝ, ‖W χ s y‖ ≤ A * Real.exp (-(y ^ 2)) := by
  rcases χ.even_or_odd with hχ | hχ
  · rcases WeightConvergesEven.weightIntegrand_norm_le s hs0 (x := (1 : ℝ)) (by norm_num) with ⟨A, hApos, hAb⟩
    refine ⟨A, hApos, ?_⟩
    intro y
    have hEq : W χ s y = WeightConvergesEven.weightIntegrand s 1 y := by
      unfold W WeightConvergesEven.weightIntegrand smoothingFunction
      rw [hχ.gammaFactor_def, hχ.gammaFactor_def]
      simp
    rw [hEq]
    exact hAb y
  · rcases WeightConvergesOdd.weightIntegrandOdd_norm_le s hs0 (x := (1 : ℝ)) (by norm_num) with ⟨A, hApos, hAb⟩
    refine ⟨A, hApos, ?_⟩
    intro y
    have hEq : W χ s y = WeightConvergesOdd.weightIntegrandOdd s 1 y := by
      unfold W WeightConvergesOdd.weightIntegrandOdd smoothingFunction
      rw [hχ.gammaFactor_def, hχ.gammaFactor_def]
      have hga : (s + 1 + I * (y : ℂ) + 1) = (s + 2 + I * (y : ℂ)) := by ring
      rw [hga]
      simp
    rw [hEq]
    exact hAb y

/-- Continuity of the vertical-line weight in `y`. -/
theorem continuous_W (χ : DirichletCharacter ℂ N) {s : ℂ} (hs0 : 0 < s.re) :
    Continuous (fun y : ℝ => W χ s y) := by
  rcases χ.even_or_odd with hχ | hχ
  · have hc : Continuous (fun y : ℝ => WeightConvergesEven.weightIntegrand s 1 y) :=
      WeightConvergesEven.continuous_weightIntegrand s hs0 (x := (1 : ℝ)) (by norm_num)
    have hEq : (fun y : ℝ => W χ s y) = fun y : ℝ => WeightConvergesEven.weightIntegrand s 1 y := by
      funext y
      unfold W WeightConvergesEven.weightIntegrand smoothingFunction
      rw [hχ.gammaFactor_def, hχ.gammaFactor_def]
      simp
    rw [hEq]
    exact hc
  · have hc : Continuous (fun y : ℝ => WeightConvergesOdd.weightIntegrandOdd s 1 y) :=
      WeightConvergesOdd.continuous_weightIntegrandOdd s hs0 (x := (1 : ℝ)) (by norm_num)
    have hEq : (fun y : ℝ => W χ s y) = fun y : ℝ => WeightConvergesOdd.weightIntegrandOdd s 1 y := by
      funext y
      unfold W WeightConvergesOdd.weightIntegrandOdd smoothingFunction
      rw [hχ.gammaFactor_def, hχ.gammaFactor_def]
      have hga : (s + 1 + I * (y : ℂ) + 1) = (s + 2 + I * (y : ℂ)) := by ring
      rw [hga]
      simp
    rw [hEq]
    exact hc

/-- `y ↦ ‖W χ s y‖` is integrable. -/
theorem W_abs_integrable (χ : DirichletCharacter ℂ N) {s : ℂ} (hs0 : 0 < s.re) :
    Integrable (fun y : ℝ => ‖W χ s y‖) := by
  rcases exists_W_abs_bound χ hs0 with ⟨A, hApos, hAb⟩
  have hg : Integrable (fun y : ℝ => A * Real.exp (-(y ^ 2))) := by
    have hbase : Integrable (fun y : ℝ => Real.exp (-(y ^ 2))) := by
      simpa using (integrable_exp_neg_mul_sq (b := (1 : ℝ)) (by norm_num) :
        Integrable fun y : ℝ => Real.exp (-(1 : ℝ) * y ^ 2))
    exact hbase.const_mul A
  refine Integrable.mono hg ?_ ?_
  · exact (continuous_W χ hs0).norm.aestronglyMeasurable
  · filter_upwards with y
    have hAe : 0 ≤ A * Real.exp (-(y ^ 2)) := by positivity
    calc
      ‖‖W χ s y‖‖ = ‖W χ s y‖ := by rw [Real.norm_of_nonneg (norm_nonneg _)]
      _ ≤ A * Real.exp (-(y ^ 2)) := hAb y
      _ = ‖A * Real.exp (-(y ^ 2))‖ := by rw [Real.norm_of_nonneg hAe]

end PL.AfeMellin


open Complex DirichletCharacter Filter MeasureTheory Set
open PL.AFE
open scoped Real

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PL.AfeMellin

variable {N : ℕ} [NeZero N]

/-- The complex Mellin-inverse normalisation constant `1 / (2π)`. -/
noncomputable def cTwoPi : ℂ := ((1 / (2 * Real.pi) : ℝ) : ℂ)

/-- Continuity of the Mellin kernel `y ↦ x^(-(1+Iy))` for `0 < x`. -/
lemma kernel_continuous {x : ℝ} (hx : 0 < x) :
    Continuous (fun y : ℝ => (x : ℂ) ^ (-(1 + I * (y : ℂ)))) := by
  exact Continuous.cpow continuous_const (by fun_prop) (fun _ => Complex.ofReal_mem_slitPlane.mpr hx)

/-- The per-`n` Mellin integrand of the main smoothed sum (with the `1/(2π)` factor). -/
noncomputable def F (χ : DirichletCharacter ℂ N) (s : ℂ) (n : ℕ) (y : ℝ) : ℂ :=
  cTwoPi * χ n * (n : ℂ) ^ (-s) * ((afeScale N n : ℝ) : ℂ) ^ (-(1 + I * (y : ℂ))) * W χ s y

/-- The `n = 0` integrand is identically zero. -/
lemma F_zero (χ : DirichletCharacter ℂ N) (s : ℂ) (y : ℝ) : F χ s 0 y = 0 := by
  unfold F
  have hne : (1 + I * (y : ℂ)) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp at hre
  have hk : ((afeScale N 0 : ℝ) : ℂ) ^ (-(1 + I * (y : ℂ))) = 0 := by
    rw [show afeScale N 0 = 0 by simp [afeScale]]
    rw [ofReal_zero]
    exact zero_cpow (neg_ne_zero.mpr hne)
  rw [hk]
  ring

/-- The integrand `F n` is continuous in `y` for every `n`. -/
lemma F_continuous (χ : DirichletCharacter ℂ N) {s : ℂ} (hs0 : 0 < s.re) (n : ℕ) :
    Continuous (fun y : ℝ => F χ s n y) := by
  by_cases hn : n = 0
  · subst n
    have hfun : (fun y : ℝ => F χ s 0 y) = 0 := funext (fun y => F_zero χ s y)
    rw [hfun]
    exact continuous_const
  · have hx : 0 < afeScale N n := by
      dsimp [afeScale]
      exact div_pos (by exact_mod_cast (Nat.pos_of_ne_zero hn))
        (Real.sqrt_pos.2 (by exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne N))))
    have hkc : Continuous (fun y : ℝ => ((afeScale N n : ℝ) : ℂ) ^ (-(1 + I * (y : ℂ)))) :=
      kernel_continuous hx
    have hwc : Continuous (fun y : ℝ => W χ s y) := continuous_W χ hs0
    have hcc : Continuous (fun y : ℝ => cTwoPi * χ n * (n : ℂ) ^ (-s)) := continuous_const
    have hprod : Continuous (fun y : ℝ =>
        cTwoPi * χ n * (n : ℂ) ^ (-s) * ((afeScale N n : ℝ) : ℂ) ^ (-(1 + I * (y : ℂ))) * W χ s y) := by
      exact (hcc.mul hkc).mul hwc
    simpa [F] using hprod

/-- `(n:ℝ)^(-σ) · (n/√N)⁻¹ = √N · (n:ℝ)^(-(1+σ))` for `n ≠ 0`. -/
lemma scale_pow_ident (σ : ℝ) (n : ℕ) (hn : n ≠ 0) :
    ((n : ℝ) ^ (-σ)) * (afeScale N n)⁻¹ = Real.sqrt (N : ℝ) * ((n : ℝ) ^ (-(1 + σ))) := by
  have hiv : (afeScale N n)⁻¹ = Real.sqrt (N : ℝ) / (n : ℝ) := inv_afeScale (N := N) n hn
  rw [hiv]
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hn)
  calc
    ((n : ℝ) ^ (-σ)) * (Real.sqrt (N : ℝ) / (n : ℝ))
        = Real.sqrt (N : ℝ) * (((n : ℝ) ^ (-σ)) * (n : ℝ)⁻¹) := by
          ring_nf
    _ = Real.sqrt (N : ℝ) * (((n : ℝ) ^ (-σ)) * ((n : ℝ) ^ (-1 : ℝ))) := by
          congr 1
          rw [← Real.rpow_neg_one]
    _ = Real.sqrt (N : ℝ) * ((n : ℝ) ^ ((-σ) + (-1 : ℝ))) := by
          congr 1
          rw [← Real.rpow_add hnpos]
    _ = Real.sqrt (N : ℝ) * ((n : ℝ) ^ (-(1 + σ))) := by
          congr 2
          ring

/-- Pointwise norm bound for `F n y` (`n ≥ 1`). -/
lemma F_norm_le (χ : DirichletCharacter ℂ N) {s : ℂ} (hs0 : 0 < s.re) {A : ℝ}
    (hA : ∀ y : ℝ, ‖W χ s y‖ ≤ A * Real.exp (-(y ^ 2))) (n : ℕ) (hn : n ≠ 0) (y : ℝ) :
    ‖F χ s n y‖ ≤ (1 / (2 * Real.pi)) * Real.sqrt (N : ℝ) * ((n : ℝ) ^ (-(1 + s.re)))
        * A * Real.exp (-(y ^ 2)) := by
  have hx : 0 < afeScale N n := by
    dsimp [afeScale]
    exact div_pos (by exact_mod_cast (Nat.pos_of_ne_zero hn))
      (Real.sqrt_pos.2 (by exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne N))))
  have hnormc : ‖cTwoPi‖ = (1 / (2 * Real.pi)) := by
    unfold cTwoPi
    calc
      ‖((1 / (2 * Real.pi) : ℝ) : ℂ)‖ = |(1 / (2 * Real.pi) : ℝ)| := RCLike.norm_ofReal _
      _ = 1 / (2 * Real.pi) := by rw [abs_of_nonneg]; positivity
  calc
    ‖F χ s n y‖
        = ‖cTwoPi‖ * ‖χ n‖ * ‖(n : ℂ) ^ (-s)‖
            * ‖((afeScale N n : ℝ) : ℂ) ^ (-(1 + I * (y : ℂ)))‖ * ‖W χ s y‖ := by
            unfold F
            rw [norm_mul, norm_mul, norm_mul, norm_mul]
    _ = (1 / (2 * Real.pi)) * ‖χ n‖ * ((n : ℝ) ^ (-s.re))
            * ((afeScale N n)⁻¹) * ‖W χ s y‖ := by
            rw [hnormc]
            rw [norm_nat_cpow_neg n hn s]
            rw [norm_cpow_neg_one_add_mul_I (afeScale N n) hx y]
    _ ≤ (1 / (2 * Real.pi)) * 1 * ((n : ℝ) ^ (-s.re))
            * ((afeScale N n)⁻¹) * (A * Real.exp (-(y ^ 2))) := by
            gcongr
            · exact norm_char_nat_le_one χ n
            · exact hA y
    _ = (1 / (2 * Real.pi)) * ((n : ℝ) ^ (-s.re)) * ((afeScale N n)⁻¹) * A * Real.exp (-(y ^ 2)) := by
            ring
    _ = (1 / (2 * Real.pi)) * (((n : ℝ) ^ (-s.re)) * (afeScale N n)⁻¹) * A * Real.exp (-(y ^ 2)) := by
            ring
    _ = (1 / (2 * Real.pi)) * (Real.sqrt (N : ℝ) * ((n : ℝ) ^ (-(1 + s.re)))) * A * Real.exp (-(y ^ 2)) := by
            rw [scale_pow_ident (N := N) (s.re) n hn]
    _ = (1 / (2 * Real.pi)) * Real.sqrt (N : ℝ) * ((n : ℝ) ^ (-(1 + s.re)))
            * A * Real.exp (-(y ^ 2)) := by
            ring

/-- Each `F n` is Bochner-integrable in `y`. -/
lemma F_integrable (χ : DirichletCharacter ℂ N) {s : ℂ} (hs0 : 0 < s.re) (n : ℕ) :
    Integrable (fun y : ℝ => F χ s n y) := by
  rcases exists_W_abs_bound χ hs0 with ⟨A, hApos, hAb⟩
  have hg : Integrable (fun y : ℝ => (1 / (2 * Real.pi)) * Real.sqrt (N : ℝ)
      * ((n : ℝ) ^ (-(1 + s.re))) * A * Real.exp (-(y ^ 2))) := by
    have hbase : Integrable (fun y : ℝ => Real.exp (-(y ^ 2))) := by
      simpa using (integrable_exp_neg_mul_sq (b := (1 : ℝ)) (by norm_num) :
        Integrable fun y : ℝ => Real.exp (-(1 : ℝ) * y ^ 2))
    exact hbase.const_mul ((1 / (2 * Real.pi)) * Real.sqrt (N : ℝ) * ((n : ℝ) ^ (-(1 + s.re))) * A)
  refine Integrable.mono hg ?_ ?_
  · exact (F_continuous χ hs0 n).aestronglyMeasurable
  · by_cases hn : n = 0
    · subst n
      filter_upwards with y
      rw [F_zero χ s y, norm_zero]
      exact norm_nonneg _
      
    · filter_upwards with y
      have hce : 0 ≤ (1 / (2 * Real.pi)) * Real.sqrt (N : ℝ) * ((n : ℝ) ^ (-(1 + s.re))) * A * Real.exp (-(y ^ 2)) := by
        positivity
      calc
        ‖F χ s n y‖ ≤ (1 / (2 * Real.pi)) * Real.sqrt (N : ℝ) * ((n : ℝ) ^ (-(1 + s.re))) * A * Real.exp (-(y ^ 2)) :=
              F_norm_le χ hs0 hAb n hn y
        _ = ‖(1 / (2 * Real.pi)) * Real.sqrt (N : ℝ) * ((n : ℝ) ^ (-(1 + s.re))) * A * Real.exp (-(y ^ 2))‖ := by
              rw [Real.norm_of_nonneg hce]


/-- Tail-summable integral-norm bound for the family `F`. -/
lemma F_int_norm_summable (χ : DirichletCharacter ℂ N) {s : ℂ} (hs0 : 0 < s.re) :
    Summable (fun n : ℕ => ∫ y : ℝ, ‖F χ s n y‖) := by
  rcases exists_W_abs_bound χ hs0 with ⟨A, hApos, hAb⟩
  have htail : Summable (fun m : ℕ => ∫ y : ℝ, ‖F χ s (m + 1) y‖) := by
    have hbase : Summable (fun n : ℕ => (n : ℝ) ^ (-(1 + s.re))) := by
      exact Real.summable_nat_rpow.mpr (by linarith)
    have hbase' : Summable (fun m : ℕ => ((m + 1 : ℕ) : ℝ) ^ (-(1 + s.re))) := by
      exact (summable_nat_add_iff 1).2 hbase
    have hbs : Summable (fun m : ℕ =>
        (1 / (2 * Real.pi)) * Real.sqrt (N : ℝ) * (((m + 1 : ℕ) : ℝ) ^ (-(1 + s.re))) * A
          * (∫ y : ℝ, Real.exp (-(y ^ 2)))) := by
      have hcong : (fun m : ℕ =>
          (1 / (2 * Real.pi)) * Real.sqrt (N : ℝ) * (((m + 1 : ℕ) : ℝ) ^ (-(1 + s.re))) * A
            * (∫ y : ℝ, Real.exp (-(y ^ 2))))
          = fun m : ℕ =>
            ((1 / (2 * Real.pi)) * Real.sqrt (N : ℝ) * A * (∫ y : ℝ, Real.exp (-(y ^ 2))))
              * (((m + 1 : ℕ) : ℝ) ^ (-(1 + s.re))) := by
        funext m
        ring
      rw [hcong]
      exact hbase'.mul_left ((1 / (2 * Real.pi)) * Real.sqrt (N : ℝ) * A * (∫ y : ℝ, Real.exp (-(y ^ 2))))
    refine Summable.of_nonneg_of_le (fun m => integral_nonneg (fun y => norm_nonneg _)) ?_ hbs
    intro m
    have hn0 : (m + 1 : ℕ) ≠ 0 := by omega
    have hg : Integrable (fun y : ℝ => ((1 / (2 * Real.pi)) * Real.sqrt (N : ℝ)
        * (((m + 1 : ℕ) : ℝ) ^ (-(1 + s.re))) * A * Real.exp (-(y ^ 2)))) := by
      have hbase : Integrable (fun y : ℝ => Real.exp (-(y ^ 2))) := by
        simpa using (integrable_exp_neg_mul_sq (b := (1 : ℝ)) (by norm_num) :
          Integrable fun y : ℝ => Real.exp (-(1 : ℝ) * y ^ 2))
      exact hbase.const_mul ((1 / (2 * Real.pi)) * Real.sqrt (N : ℝ) * (((m + 1 : ℕ) : ℝ) ^ (-(1 + s.re))) * A)
    have hpoint : ∀ᵐ y ∂(volume : Measure ℝ),
        ‖F χ s (m + 1) y‖ ≤ (1 / (2 * Real.pi)) * Real.sqrt (N : ℝ)
            * (((m + 1 : ℕ) : ℝ) ^ (-(1 + s.re))) * A * Real.exp (-(y ^ 2)) := by
      filter_upwards with y
      exact F_norm_le χ hs0 hAb (m + 1) hn0 y
    calc
      ∫ y : ℝ, ‖F χ s (m + 1) y‖
          ≤ ∫ y : ℝ, (1 / (2 * Real.pi)) * Real.sqrt (N : ℝ) * (((m + 1 : ℕ) : ℝ) ^ (-(1 + s.re))) * A * Real.exp (-(y ^ 2)) := by
            exact integral_mono_ae (F_integrable χ hs0 (m + 1)).norm hg hpoint
      _ = (1 / (2 * Real.pi)) * Real.sqrt (N : ℝ) * (((m + 1 : ℕ) : ℝ) ^ (-(1 + s.re))) * A
            * (∫ y : ℝ, Real.exp (-(y ^ 2))) := by
            rw [MeasureTheory.integral_const_mul]
  exact (summable_nat_add_iff 1).1 htail


/-- The Mellin inverse at `σ = 1` expanded along the vertical line, written with the
`1 + I·y` convention and complex normalisation `cTwoPi`. -/
lemma mellinInv_one_eq_integral (f : ℂ → ℂ) (x : ℝ) :
    mellinInv 1 f x = cTwoPi * ∫ y : ℝ, (x : ℂ) ^ (-(1 + I * (y : ℂ))) * f (1 + I * (y : ℂ)) := by
  unfold mellinInv cTwoPi
  rw [real_smul_eq_mul]
  congr 1
  apply MeasureTheory.integral_congr_ae
  filter_upwards with y
  rw [smul_eq_mul]
  have h1 : (x : ℂ) ^ (-(((1 : ℝ) : ℂ) + (y : ℂ) * I)) = (x : ℂ) ^ (-(1 + I * (y : ℂ))) := by
    congr 1
    norm_num
    ring
  have h2 : f (((1 : ℝ) : ℂ) + (y : ℂ) * I) = f (1 + I * (y : ℂ)) := by
    congr 1
    norm_num
    ring
  rw [h1, h2]


/-- The scale-series identity in the `1 + I·y` convention (bridge from `scale_series_eq`). -/
lemma scale_series_eq_Iy (χ : DirichletCharacter ℂ N) {s : ℂ} (hs0 : 0 < s.re) (y : ℝ) :
    (∑' n : ℕ, χ n * (n : ℂ) ^ (-s) * ((afeScale N n : ℝ) : ℂ) ^ (-(1 + I * (y : ℂ))))
      = ((Real.sqrt (N : ℝ) : ℂ) ^ (1 + I * (y : ℂ))) * DirichletCharacter.LFunction χ (s + 1 + I * (y : ℂ)) := by
  have h := scale_series_eq χ hs0 y
  calc
    (∑' n : ℕ, χ n * (n : ℂ) ^ (-s) * ((afeScale N n : ℝ) : ℂ) ^ (-(1 + I * (y : ℂ))))
        = (∑' n : ℕ, χ n * (n : ℂ) ^ (-s) * ((afeScale N n : ℝ) : ℂ) ^ (-(1 + (y : ℂ) * I))) := by
          apply tsum_congr
          intro n
          congr 1
          congr 2
          ring
    _ = ((Real.sqrt (N : ℝ) : ℂ) ^ (1 + (y : ℂ) * I)) * DirichletCharacter.LFunction χ (s + 1 + (y : ℂ) * I) := h
    _ = ((Real.sqrt (N : ℝ) : ℂ) ^ (1 + I * (y : ℂ))) * DirichletCharacter.LFunction χ (s + 1 + I * (y : ℂ)) := by
          congr 2
          · ring
          · ring

/-- Pointwise summability of the integrand family. -/
lemma F_summable_at_y (χ : DirichletCharacter ℂ N) {s : ℂ} (hs0 : 0 < s.re) (y : ℝ) :
    Summable (fun n : ℕ => F χ s n y) := by
  rcases exists_W_abs_bound χ hs0 with ⟨A, hApos, hAb⟩
  have htail : Summable (fun m : ℕ => F χ s (m + 1) y) := by
    refine Summable.of_norm ?_
    have hbase : Summable (fun n : ℕ => (n : ℝ) ^ (-(1 + s.re))) := by
      exact Real.summable_nat_rpow.mpr (by linarith)
    have hbase' : Summable (fun m : ℕ => ((m + 1 : ℕ) : ℝ) ^ (-(1 + s.re))) := by
      exact (summable_nat_add_iff 1).2 hbase
    have hbs : Summable (fun m : ℕ =>
        (1 / (2 * Real.pi)) * Real.sqrt (N : ℝ) * (((m + 1 : ℕ) : ℝ) ^ (-(1 + s.re))) * A * Real.exp (-(y ^ 2))) := by
      have hcong : (fun m : ℕ =>
          (1 / (2 * Real.pi)) * Real.sqrt (N : ℝ) * (((m + 1 : ℕ) : ℝ) ^ (-(1 + s.re))) * A * Real.exp (-(y ^ 2)))
          = fun m : ℕ =>
            ((1 / (2 * Real.pi)) * Real.sqrt (N : ℝ) * A * Real.exp (-(y ^ 2)))
              * (((m + 1 : ℕ) : ℝ) ^ (-(1 + s.re))) := by
        funext m
        ring
      rw [hcong]
      exact hbase'.mul_left ((1 / (2 * Real.pi)) * Real.sqrt (N : ℝ) * A * Real.exp (-(y ^ 2)))
    exact Summable.of_nonneg_of_le (fun m => norm_nonneg _)
      (fun m => F_norm_le χ hs0 hAb (m + 1) (by omega) y) hbs
  exact (summable_nat_add_iff 1).1 htail

/-- Pointwise sum of the integrands = `cTwoPi · W(s,y) · (√N)^(1+Iy) · L(s+1+Iy)`. -/
lemma sum_F_eq (χ : DirichletCharacter ℂ N) {s : ℂ} (hs0 : 0 < s.re) (y : ℝ) :
    (∑' n : ℕ, F χ s n y)
      = cTwoPi * W χ s y * ((Real.sqrt (N : ℝ) : ℂ) ^ (1 + I * (y : ℂ)))
          * DirichletCharacter.LFunction χ (s + 1 + I * (y : ℂ)) := by
  let f0 : ℕ → ℂ := fun n => χ (n : ZMod N) * (n : ℂ) ^ (-s) * ((afeScale N n : ℝ) : ℂ) ^ (-(1 + I * (y : ℂ)))
  have hfac : (∑' n : ℕ, cTwoPi * W χ s y * f0 n) = cTwoPi * W χ s y * (∑' n : ℕ, f0 n) := by
    have h1 : (∑' n : ℕ, (cTwoPi * W χ s y) • f0 n) = (cTwoPi * W χ s y) • (∑' n : ℕ, f0 n) :=
      tsum_const_smul'' (g := cTwoPi * W χ s y) (f := f0)
    simpa [smul_eq_mul] using h1
  calc
    (∑' n : ℕ, F χ s n y)
        = ∑' n : ℕ, cTwoPi * W χ s y * (χ n * (n : ℂ) ^ (-s) * ((afeScale N n : ℝ) : ℂ) ^ (-(1 + I * (y : ℂ)))) := by
          apply tsum_congr
          intro n
          unfold F
          ring
    _ = cTwoPi * W χ s y * (∑' n : ℕ, χ n * (n : ℂ) ^ (-s) * ((afeScale N n : ℝ) : ℂ) ^ (-(1 + I * (y : ℂ)))) := hfac
    _ = cTwoPi * W χ s y * (((Real.sqrt (N : ℝ) : ℂ) ^ (1 + I * (y : ℂ))) * DirichletCharacter.LFunction χ (s + 1 + I * (y : ℂ))) := by
          rw [scale_series_eq_Iy χ hs0 y]
    _ = cTwoPi * W χ s y * ((Real.sqrt (N : ℝ) : ℂ) ^ (1 + I * (y : ℂ))) * DirichletCharacter.LFunction χ (s + 1 + I * (y : ℂ)) := by
          ring



/-- `(√N)^(1+Iy) = ((√N:ℂ)⁻¹)^(-(1+Iy))`. -/
lemma sqrt_cpow_inv (y : ℝ) :
    ((Real.sqrt (N : ℝ) : ℂ) ^ (1 + I * (y : ℂ)))
      = (((Real.sqrt (N : ℝ) : ℂ)⁻¹) ^ (-(1 + I * (y : ℂ)))) := by
  rw [inv_cpow_ofReal_nonneg (Real.sqrt_nonneg N) (-(1 + I * (y : ℂ)))]
  rw [← cpow_neg (Real.sqrt (N : ℝ) : ℂ) (-(1 + I * (y : ℂ)))]
  congr 1
  ring

/-- Pointwise sum of the integrands in the form matching the Mellin-inverse integrand
of the completed L-function. -/
lemma sum_F_eq_completed (χ : DirichletCharacter ℂ N) {s : ℂ} (hs0 : 0 < s.re) (y : ℝ) :
    (∑' n : ℕ, F χ s n y)
      = cTwoPi * (χ.gammaFactor s)⁻¹
          * (((Real.sqrt (N : ℝ) : ℂ)⁻¹) ^ (-(1 + I * (y : ℂ))))
          * DirichletCharacter.completedLFunction χ (s + 1 + I * (y : ℂ)) * smoothingFunction (1 + I * (y : ℂ))
          / (1 + I * (y : ℂ)) := by
  have hz0 : 0 < (s + 1 + I * (y : ℂ)).re := by
    simp
    linarith
  have hc := completedLFunction_eq_gamma_mul_L χ (s := s + 1 + I * (y : ℂ)) hz0
  have hg : χ.gammaFactor s ≠ 0 := Structural.gammaFactor_ne_zero_of_zero_lt_re χ hs0
  calc
    (∑' n : ℕ, F χ s n y)
        = cTwoPi * W χ s y * ((Real.sqrt (N : ℝ) : ℂ) ^ (1 + I * (y : ℂ))) * DirichletCharacter.LFunction χ (s + 1 + I * (y : ℂ)) :=
          sum_F_eq χ hs0 y
    _ = cTwoPi * (χ.gammaFactor (s + 1 + I * (y : ℂ)) / χ.gammaFactor s * smoothingFunction (1 + I * (y : ℂ)) / (1 + I * (y : ℂ)))
          * ((Real.sqrt (N : ℝ) : ℂ) ^ (1 + I * (y : ℂ))) * DirichletCharacter.LFunction χ (s + 1 + I * (y : ℂ)) := by
          unfold W
          rfl
    _ = cTwoPi * (χ.gammaFactor (s + 1 + I * (y : ℂ)) / χ.gammaFactor s) * DirichletCharacter.LFunction χ (s + 1 + I * (y : ℂ))
          * ((Real.sqrt (N : ℝ) : ℂ) ^ (1 + I * (y : ℂ))) * smoothingFunction (1 + I * (y : ℂ)) / (1 + I * (y : ℂ)) := by
          ring
    _ = cTwoPi * (χ.gammaFactor s)⁻¹ * (χ.gammaFactor (s + 1 + I * (y : ℂ)) * DirichletCharacter.LFunction χ (s + 1 + I * (y : ℂ)))
          * ((Real.sqrt (N : ℝ) : ℂ) ^ (1 + I * (y : ℂ))) * smoothingFunction (1 + I * (y : ℂ)) / (1 + I * (y : ℂ)) := by
          field_simp [hg]
    _ = cTwoPi * (χ.gammaFactor s)⁻¹ * DirichletCharacter.completedLFunction χ (s + 1 + I * (y : ℂ))
          * ((Real.sqrt (N : ℝ) : ℂ) ^ (1 + I * (y : ℂ))) * smoothingFunction (1 + I * (y : ℂ)) / (1 + I * (y : ℂ)) := by
          rw [hc]
    _ = cTwoPi * (χ.gammaFactor s)⁻¹
          * (((Real.sqrt (N : ℝ) : ℂ)⁻¹) ^ (-(1 + I * (y : ℂ))))
          * DirichletCharacter.completedLFunction χ (s + 1 + I * (y : ℂ)) * smoothingFunction (1 + I * (y : ℂ)) / (1 + I * (y : ℂ)) := by
          rw [sqrt_cpow_inv y]
          ring

/-- Each term of the main smoothed sum is the integral of `F n`. -/
lemma term_integral (χ : DirichletCharacter ℂ N) {s : ℂ} (hs0 : 0 < s.re) (n : ℕ) :
    χ n * (n : ℂ) ^ (-s) * afeWeight χ s (afeScale N n) = ∫ y : ℝ, F χ s n y := by
  have hs' : s ≠ 0 := by
    intro h
    rw [h] at hs0
    norm_num at hs0
  unfold afeWeight
  rw [mellinInv_one_eq_integral]
  let Q : ℂ → ℂ := fun u => (χ.gammaFactor (s + u) / χ.gammaFactor s) * smoothingFunction u / u
  -- integrand factor equality: Q(1+Iy) = W y
  have hW : ∀ y : ℝ, Q (1 + I * (y : ℂ)) = W χ s y := by
    intro y
    unfold Q W
    have hg : χ.gammaFactor (s + (1 + I * (y : ℂ))) = χ.gammaFactor (s + 1 + I * (y : ℂ)) := by
      congr 1
      ring
    rw [hg]
  let g : ℝ → ℂ := fun y => χ n * (n : ℂ) ^ (-s) * (((afeScale N n : ℝ) : ℂ) ^ (-(1 + I * (y : ℂ))) * W χ s y)
  calc
    χ n * (n : ℂ) ^ (-s) * (cTwoPi * ∫ y : ℝ, ((afeScale N n : ℝ) : ℂ) ^ (-(1 + I * (y : ℂ))) * Q (1 + I * (y : ℂ)))
        = cTwoPi * (χ n * (n : ℂ) ^ (-s) * ∫ y : ℝ, ((afeScale N n : ℝ) : ℂ) ^ (-(1 + I * (y : ℂ))) * Q (1 + I * (y : ℂ))) := by
          ring
    _ = cTwoPi * ∫ y : ℝ, χ n * (n : ℂ) ^ (-s) * (((afeScale N n : ℝ) : ℂ) ^ (-(1 + I * (y : ℂ))) * Q (1 + I * (y : ℂ))) := by
          congr 1
          exact (MeasureTheory.integral_const_mul (L := ℂ) (r := χ n * (n : ℂ) ^ (-s))
            (f := fun y : ℝ => ((afeScale N n : ℝ) : ℂ) ^ (-(1 + I * (y : ℂ))) * Q (1 + I * (y : ℂ)))).symm
    _ = cTwoPi * ∫ y : ℝ, χ n * (n : ℂ) ^ (-s) * (((afeScale N n : ℝ) : ℂ) ^ (-(1 + I * (y : ℂ))) * W χ s y) := by
          congr 1
          apply MeasureTheory.integral_congr_ae
          filter_upwards with y
          rw [hW y]
    _ = cTwoPi * ∫ y : ℝ, g y := rfl
    _ = ∫ y : ℝ, cTwoPi * g y := by
          exact (MeasureTheory.integral_const_mul (L := ℂ) (r := cTwoPi) (f := g)).symm
    _ = ∫ y : ℝ, F χ s n y := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards with y
          unfold F g
          ring



/-- `((√N⁻¹:ℝ):ℂ) = (√N:ℂ)⁻¹`. -/
lemma sqrt_inv_ofReal (N : ℕ) : (((Real.sqrt (N : ℝ))⁻¹ : ℝ) : ℂ) = (Real.sqrt (N : ℝ) : ℂ)⁻¹ := by
  rw [← Complex.ofReal_inv]

/-- The Mellin-inversion identity for the main smoothed sum (T1). -/
theorem main_sum_eq_completed_integral_core (χ : DirichletCharacter ℂ N) {s : ℂ} (hs0 : 0 < s.re) :
    (∑' n : ℕ, χ n * (n : ℂ) ^ (-s) * afeWeight χ s (afeScale N n))
      = (χ.gammaFactor s)⁻¹ *
          mellinInv 1 (fun u : ℂ => DirichletCharacter.completedLFunction χ (s + u) * smoothingFunction u / u)
            ((Real.sqrt (N : ℝ))⁻¹) := by
  let H : ℂ → ℂ := fun u => DirichletCharacter.completedLFunction χ (s + u) * smoothingFunction u / u
  let J : ℝ → ℂ := fun y =>
    (χ.gammaFactor s)⁻¹ * (((Real.sqrt (N : ℝ) : ℂ)⁻¹) ^ (-(1 + I * (y : ℂ))))
      * DirichletCharacter.completedLFunction χ (s + 1 + I * (y : ℂ)) * smoothingFunction (1 + I * (y : ℂ)) / (1 + I * (y : ℂ))
  have hstep1 : (∑' n : ℕ, χ n * (n : ℂ) ^ (-s) * afeWeight χ s (afeScale N n))
      = ∑' n : ℕ, ∫ y : ℝ, F χ s n y := by
    apply tsum_congr
    intro n
    exact term_integral χ hs0 n
  have hstep2 : (∑' n : ℕ, ∫ y : ℝ, F χ s n y) = ∫ y : ℝ, (∑' n : ℕ, F χ s n y) :=
    integral_tsum_of_summable_integral_norm (fun n => F_integrable χ hs0 n) (F_int_norm_summable χ hs0)
  have hRHS : (χ.gammaFactor s)⁻¹ * mellinInv 1 H ((Real.sqrt (N : ℝ))⁻¹)
      = cTwoPi * ∫ y : ℝ, J y := by
    rw [mellinInv_one_eq_integral]
    -- goal: γ⁻¹ · (cTwoPi · ∫ y, ((√N⁻¹ : ℝ) : ℂ)^{-(1+Iy)} · H(1+Iy)) = cTwoPi · ∫ J
    have hJ : ∀ y : ℝ,
        (χ.gammaFactor s)⁻¹ * ((((Real.sqrt (N : ℝ))⁻¹ : ℝ) : ℂ) ^ (-(1 + I * (y : ℂ)))) * H (1 + I * (y : ℂ))
          = J y := by
      intro y
      unfold J H
      rw [sqrt_inv_ofReal N]
      have hc : DirichletCharacter.completedLFunction χ (s + (1 + I * (y : ℂ))) = DirichletCharacter.completedLFunction χ (s + 1 + I * (y : ℂ)) := by
        congr 1
        ring
      rw [hc]
      ring
    calc
      (χ.gammaFactor s)⁻¹ * (cTwoPi * ∫ y : ℝ, ((((Real.sqrt (N : ℝ))⁻¹ : ℝ) : ℂ) ^ (-(1 + I * (y : ℂ)))) * H (1 + I * (y : ℂ)))
          = cTwoPi * ((χ.gammaFactor s)⁻¹ * ∫ y : ℝ, ((((Real.sqrt (N : ℝ))⁻¹ : ℝ) : ℂ) ^ (-(1 + I * (y : ℂ)))) * H (1 + I * (y : ℂ))) := by
            ring
      _ = cTwoPi * ∫ y : ℝ, (χ.gammaFactor s)⁻¹ * ((((Real.sqrt (N : ℝ))⁻¹ : ℝ) : ℂ) ^ (-(1 + I * (y : ℂ)))) * H (1 + I * (y : ℂ)) := by
            congr 1
            simpa [mul_assoc] using (MeasureTheory.integral_const_mul (L := ℂ) (r := (χ.gammaFactor s)⁻¹)
              (f := fun y : ℝ => ((((Real.sqrt (N : ℝ))⁻¹ : ℝ) : ℂ) ^ (-(1 + I * (y : ℂ)))) * H (1 + I * (y : ℂ)))).symm
      _ = cTwoPi * ∫ y : ℝ, J y := by
            congr 1
            apply MeasureTheory.integral_congr_ae
            filter_upwards with y
            exact hJ y
  calc
    (∑' n : ℕ, χ n * (n : ℂ) ^ (-s) * afeWeight χ s (afeScale N n))
        = ∫ y : ℝ, (∑' n : ℕ, F χ s n y) := by
            rw [hstep1, hstep2]
    _ = cTwoPi * ∫ y : ℝ, J y := by
          calc
            ∫ y : ℝ, (∑' n : ℕ, F χ s n y) = ∫ y : ℝ, cTwoPi * J y := by
              apply MeasureTheory.integral_congr_ae
              filter_upwards with y
              rw [sum_F_eq_completed χ hs0 y]
              unfold J
              ring
            _ = cTwoPi * ∫ y : ℝ, J y := MeasureTheory.integral_const_mul (L := ℂ) (r := cTwoPi) (f := J)
    _ = (χ.gammaFactor s)⁻¹ * mellinInv 1 H ((Real.sqrt (N : ℝ))⁻¹) := by
          rw [hRHS]
    _ = (χ.gammaFactor s)⁻¹ * mellinInv 1 (fun u : ℂ => DirichletCharacter.completedLFunction χ (s + u) * smoothingFunction u / u)
            ((Real.sqrt (N : ℝ))⁻¹) := by
          rfl


end PL.AfeMellin



/-!
# Mellin-inversion step (T1) of the approximate functional equation

This file states and **proves** the first deep identity needed to prove
`PL.AFE.approx_functional_equation`: the **main smoothed sum** equals a vertical
integral of the *completed* L-function.

## STATUS: PROVEN (machine-verified)

`main_sum_eq_completed_integral` is proved in this file, with the machinery split across
* `Submission/T1dev.lean` (foundational lemmas: the character series equals the L-function on
  `Re > 1`, `completed = γ·L` on `Re > 0`, the scale-kernel series identity, the `W` weight
  definition),
* `Submission/T1Weight.lean` (parity-branched analysis of the vertical-line weight `W`:
  Gaussian decay, continuity, integrability),
* `Submission/T1asm.lean` (the integrand family `F`, its per-`n` integrability and
  summability, the term-as-integral identity, the pointwise sum identity, and the assembly
  theorem `main_sum_eq_completed_integral_core`).

The proof follows the 5-step roadmap below: unfold the AFE weight (a Mellin inverse on the
line `Re u = 1`), interchange the sum over `n` with the integral over `y` (justified by the
absolute-summability bounds and `integral_tsum_of_summable_integral_norm`), identify the
inner character series with `L(s+1+Iy, χ)` on `Re > 1`, use `completed = γ·L`, and
reassemble the Mellin inverse at `x = 1/√N`.

## Mathematical identity (T1)

For `0 < Re s` and a character `χ` of conductor `N`,

`Σₙ χ(n)·n^(-s)·W_s(n/√N)
   = (1/γ(s)) · mellinInv 1 (u ↦ Λ(s + u)·g(u)/u) (1/√N)`

where `γ = gammaFactor χ`, `Λ = DirichletCharacter.completedLFunction χ`, `g(u) = exp(u²)` is the smoothing
function, and `W_z(x) = mellinInv 1 (u ↦ (γ(z+u)/γ(z))·g(u)/u) x` is the archimedean
weight (`afeWeight χ z x`).  Unfolding the Mellin inverse on the vertical line `Re u = 1`
(`u = 1 + I·y`), the RHS is

`(1/γ(s)) · (1/2π) · ∫_ℝ N^((1+Iy)/2) · Λ(s + 1 + I·y) · g(1 + I·y)/(1 + I·y) dy`.

## Proof roadmap (all ingredients are machine-verified in `Submission/`)

1. Unfold `afeWeight`: each term is `χ(n)·n^(-s) · mellinInv 1 (u ↦ γ(s+u)/γ(s)·g(u)/u) (n/√N)`,
   i.e. `χ(n)·n^(-s) · (1/2π)∫_ℝ (n/√N)^(-(1+Iy)) · (γ(s+1+Iy)/γ(s)) · g(1+Iy)/(1+Iy) dy`.
2. Interchange the sum over `n` with the integral over `y`.  Justification: absolute
   summability of the terms is uniform in `y`, since for every `y`
   `‖χ(n)·n^(-s)·(n/√N)^(-(1+Iy))‖ ≤ √N · n^(-1-σ)` (`σ = Re s`, via
   `PL.AfeBounds`), and `Σ n^(-1-σ) < ∞`; plus integrability in `y` from
   `Submission/WeightConvergesEven.lean`, `Submission/WeightConvergesOdd.lean` and
   dominated convergence.  (Mathlib tooling: `MeasureTheory.integral_tsum` /
   `tendsto_integral_of_dominated_convergence`, `Summable` comparison via
   `PL.AfeBounds.summable_main`.)
3. The inner sum: `Σₙ χ(n)·n^(-s-(1+Iy)) = L(s + 1 + I·y)` by absolute convergence on
   `Re(s+u) = σ+1 > 1` (`DirichletCharacter.LFunction_eq_LSeries`,
   `LSeriesSummable_of_one_lt_re`), and
   `γ(s+1+Iy)·L(s+1+Iy) = DirichletCharacter.completedLFunction χ (s+1+Iy)` by
   `LFunction_eq_completed_div_gammaFactor` (valid on `Re z > 0`).
4. Multiply by `(n/√N)^(-(1+Iy)) = N^((1+Iy)/2)·n^(-(1+Iy))`, reassemble, and recognize
   `(1/2π)·∫_ℝ (N^(-1/2))^(-(1+Iy))·Λ(s+1+Iy)·g(1+Iy)/(1+Iy) dy` as the Mellin inverse at
   `x = 1/√N`.
5. Conclude with the `(1/γ(s))` prefactor.

Note: `γ(s) ≠ 0` since `0 < Re s` (`PL.AFE.Structural.gammaFactor_ne_zero_of_zero_lt_re`).

Once T1 is proved, the remaining steps T2–T5 (functional-equation substitution, contour
shift across the pole at `u = 0` collecting the residue `Λ(1-s)`-term, dual-series
expansion, and the cancellation with `ε·ε(χ⁻¹) = 1`) are described in the header of
`Submission/ApproxFunctionalEquation.lean` and use `Submission/AfeAssembly.lean` and
`Submission/RootNumber.lean`.
-/

open Complex DirichletCharacter Filter MeasureTheory Set
open PL.AFE
open scoped Real

set_option autoImplicit false

namespace PL.AfeMellin

variable {N : ℕ} [NeZero N]

/--
**T1.** For `0 < Re s`, the main smoothed sum equals a vertical Mellin-type integral of the
completed L-function:

`Σₙ χ(n)·n^(-s)·W_s(n/√N)
   = (1/γ(s)) · mellinInv 1 (u ↦ Λ(s+u)·g(u)/u) (1/√N)`.
-/
theorem main_sum_eq_completed_integral (χ : DirichletCharacter ℂ N) {s : ℂ} (hs0 : 0 < s.re) :
    (∑' n : ℕ, χ n * (n : ℂ) ^ (-s) * afeWeight χ s (afeScale N n))
      = (χ.gammaFactor s)⁻¹ *
          mellinInv 1 (fun u : ℂ => DirichletCharacter.completedLFunction χ (s + u) * smoothingFunction u / u)
            ((Real.sqrt (N : ℝ))⁻¹) := by
  exact main_sum_eq_completed_integral_core χ hs0

end PL.AfeMellin


/-!
# Assembly of the approximate functional equation (T2–T5)

The machine-verified vertical-line identity
`PL.AfeVerticalLine.vertical_line_identity` (`Λ(s) = (1/2π)·(∫ lineRight − ∫ lineLeft)`)
is combined here with the Mellin-inversion step `PL.AfeMellin.main_sum_eq_completed_integral`
(the main smoothed sum equals `(1/γ(s))·mellinInv₁ Λ`, i.e. `2π·γ(s)·main = ∫ lineRight`), its
mirror for the dual character `χ⁻¹` at `1 − s` (giving `∫ dualIntegrand = 2π·γ(1−s)·dual`), and the
functional-equation transformation of the left-line integral
(`∫ lineLeft = −ε(χ)·N^(1/2−s)·∫ dualIntegrand`, by the substitution `y ↦ −y` together with
`Λ(w) = N^(1/2−w)·ε·Λ̄(1−w)`, evenness of the smoothing function `g`, and the scale identity
`((√N)⁻¹)^(1+Iy) · N^(3/2−s+Iy) = N^(1/2−s) · ((√N)⁻¹)^(−(1+Iy))`), to yield

**`afe_identity`** (the two-sided smooth approximate functional equation):

`L(s,χ) = Σₙ χ(n)·n^(−s)·W_s(n/√N)
        + ε(χ)·N^(1/2−s)·(γ(1−s)/γ(s))·Σₙ χ̄(n)·n^(s−1)·W_{1−s}(n/√N)`

for a primitive `χ ≠ 1`, `0 < Re s < 1`, under the strip-growth hypothesis
`AfeVerticalLine.Λ_growth χ s` (instances of which are supplied separately from
`PL.CompletedStrip`).
-/

open Complex DirichletCharacter Filter MeasureTheory Set
open PL.AFE
open PL.AfeVerticalLine
open scoped Real

set_option autoImplicit false

namespace PL.AfeProof

noncomputable section

variable {N : ℕ} [NeZero N]

/-- The scale `1/√N` at which the AFE Mellin-inverse integrals are evaluated. -/
def scale (N : ℕ) : ℝ := (Real.sqrt (N : ℝ))⁻¹

lemma scale_pos (N : ℕ) [NeZero N] : 0 < scale N := by
  unfold scale
  exact inv_pos.mpr (Real.sqrt_pos.2 (by exact_mod_cast (NeZero.pos N)))

/-- `afeScale N 1 = scale N`. -/
lemma afeScale_one (N : ℕ) [NeZero N] : afeScale N 1 = scale N := by
  simp [afeScale, scale, one_div]

/-- The main smoothed sum of the AFE. -/
def afeMain (χ : DirichletCharacter ℂ N) (s : ℂ) : ℂ :=
  ∑' n : ℕ, χ n * (n : ℂ) ^ (-s) * afeWeight χ s (afeScale N n)

/-- The dual smoothed sum of the AFE. -/
def afeDual (χ : DirichletCharacter ℂ N) (s : ℂ) : ℂ :=
  ∑' n : ℕ, (χ⁻¹) n * (n : ℂ) ^ (-(1 - s)) * afeWeight χ (1 - s) (afeScale N n)

/-- The dual Mellin-integrand: the vertical-line integrand `x0^(-(1+Iv))·Λ̄(2-s+Iv)·g(1+Iv)/(1+Iv)`
that the functional equation turns the left line `Re u = −1` into. -/
def dualIntegrand (χ : DirichletCharacter ℂ N) (s : ℂ) (v : ℝ) : ℂ :=
  (scale N : ℂ) ^ (-(1 + I * (v : ℂ))) * DirichletCharacter.completedLFunction (χ⁻¹) (2 - s + I * (v : ℂ))
    * smoothingFunction (1 + I * (v : ℂ)) / (1 + I * (v : ℂ))

/-- The right vertical-line integral `R = ∫ lineRight`. -/
def rightInt (χ : DirichletCharacter ℂ N) (s : ℂ) : ℂ :=
  ∫ y : ℝ, lineRight χ s (scale N) y

/-- The left vertical-line integral `L = ∫ lineLeft`. -/
def leftInt (χ : DirichletCharacter ℂ N) (s : ℂ) : ℂ :=
  ∫ y : ℝ, lineLeft χ s (scale N) y

/-- The dual vertical-line integral `Ī = ∫ dualIntegrand`. -/
def dualInt (χ : DirichletCharacter ℂ N) (s : ℂ) : ℂ :=
  ∫ v : ℝ, dualIntegrand χ s v

/-- For a positive real `a`, the complex power is `exp (log a · z)`. -/
private lemma cpow_ofReal_pos_exp (a : ℝ) (ha : 0 < a) (z : ℂ) :
    (a : ℂ) ^ z = cexp ((Real.log a : ℂ) * z) := by
  rw [Complex.cpow_def_of_ne_zero (ofReal_ne_zero.mpr (ne_of_gt ha))]
  congr 1
  rw [← Complex.ofReal_log (le_of_lt ha)]

/-- Scale identity used in the dual transformation:
`x0^(1+Iv)·N^(3/2−s+Iv) = N^(1/2−s)·x0^(−(1+Iv))`, `x0 = (√N)⁻¹`. -/
lemma scale_cpow_identity (s v : ℂ) :
    (((Real.sqrt (N : ℝ))⁻¹ : ℝ) : ℂ) ^ (1 + I * v) * (N : ℂ) ^ (3 / 2 - s + I * v)
      = (N : ℂ) ^ (1 / 2 - s) * (((Real.sqrt (N : ℝ))⁻¹ : ℝ) : ℂ) ^ (-(1 + I * v)) := by
  let a : ℝ := (Real.sqrt (N : ℝ))⁻¹
  let b : ℝ := (N : ℝ)
  have ha : 0 < a := by
    dsimp [a]
    exact inv_pos.mpr (Real.sqrt_pos.2 (by exact_mod_cast (NeZero.pos N)))
  have hb : 0 < b := by
    dsimp [b]
    exact_mod_cast (NeZero.pos N)
  have hN : (N : ℂ) = (b : ℂ) := by simp [b]
  rw [hN]
  rw [cpow_ofReal_pos_exp a ha, cpow_ofReal_pos_exp a ha, cpow_ofReal_pos_exp b hb,
    cpow_ofReal_pos_exp b hb]
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  have hlog : Real.log a = -(Real.log b) / 2 := by
    dsimp [a, b]
    rw [Real.log_inv, Real.log_sqrt]
    · ring
    · exact_mod_cast (le_of_lt (NeZero.pos N))
  rw [hlog]
  norm_num
  ring

/-- The Mellin-inverse integral in `main_sum_eq_completed_integral` is exactly `∫ lineRight`
on the right vertical line. -/
private lemma mellinInv_eq_rightInt (χ : DirichletCharacter ℂ N) (s : ℂ) :
    mellinInv 1 (fun u : ℂ => DirichletCharacter.completedLFunction χ (s + u) * smoothingFunction u / u)
        ((Real.sqrt (N : ℝ))⁻¹)
      = (1 / (2 * Real.pi) : ℝ) • rightInt χ s := by
  unfold mellinInv rightInt
  congr 1
  apply congrArg (fun f : ℝ → ℂ => ∫ y : ℝ, f y)
  funext y
  change (scale N : ℂ) ^ (-(1 + (y : ℝ) * I)) •
      (DirichletCharacter.completedLFunction χ (s + (1 + (y : ℝ) * I)) * smoothingFunction (1 + (y : ℝ) * I)
        / (1 + (y : ℝ) * I)) = lineRight χ s (scale N) y
  rw [smul_eq_mul]
  unfold lineRight
  rw [show (1 + (y : ℝ) * I) = (1 + I * (y : ℂ)) by
    apply Complex.ext <;> simp <;> ring]
  rw [show s + (1 + I * (y : ℂ)) = s + 1 + I * (y : ℂ) by ring]
  ring_nf

/-- The main Mellin-inverse integral is `∫ lineRight` on the right vertical line:
`2π·γ(s)·(main smoothed sum) = ∫ lineRight`. -/
lemma main_sum_eq_rightInt (χ : DirichletCharacter ℂ N) {s : ℂ} (hs0 : 0 < s.re) :
    (2 * Real.pi : ℂ) * χ.gammaFactor s * afeMain χ s = rightInt χ s := by
  have hT1 := AfeMellin.main_sum_eq_completed_integral χ hs0
  have hm := mellinInv_eq_rightInt χ s
  have hg0 : χ.gammaFactor s ≠ 0 := Structural.gammaFactor_ne_zero_of_zero_lt_re χ hs0
  dsimp [afeMain]
  rw [hT1]
  rw [hm]
  simp
  field_simp [hg0]

/-- The dual smoothed sum is the Mellin-inverse integral of the dual completed function at
`1 − s`: `2π·γ(1−s)·(dual smoothed sum) = ∫ dualIntegrand`. -/
lemma dual_sum_eq_dualInt (χ : DirichletCharacter ℂ N) {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    (2 * Real.pi : ℂ) * χ.gammaFactor (1 - s) * afeDual χ s = dualInt χ s := by
  have hs1' : 0 < (1 - s).re := by
    rw [Complex.sub_re, Complex.one_re]
    linarith
  have hT := main_sum_eq_rightInt (χ := χ⁻¹) (s := 1 - s) hs1'
  have hdual_tsum : afeDual χ s =
      (∑' n : ℕ, (χ⁻¹) n * (n : ℂ) ^ (-(1 - s)) * afeWeight χ⁻¹ (1 - s) (afeScale N n)) := by
    unfold afeDual
    apply tsum_congr
    intro n
    rw [AfeAssembly.afeWeight_inv_eq]
  have hγ : χ⁻¹.gammaFactor (1 - s) = χ.gammaFactor (1 - s) :=
    AfeAssembly.gammaFactor_inv_eq χ (1 - s)
  have hri : rightInt χ⁻¹ (1 - s) = dualInt χ s := by
    unfold rightInt dualInt
    apply congrArg (fun f : ℝ → ℂ => ∫ y : ℝ, f y)
    funext y
    unfold lineRight dualIntegrand
    rw [show (1 - s) + 1 + I * (y : ℂ) = 2 - s + I * (y : ℂ) by ring]
  calc
    (2 * Real.pi : ℂ) * χ.gammaFactor (1 - s) * afeDual χ s
        = (2 * Real.pi : ℂ) * χ⁻¹.gammaFactor (1 - s)
            * (∑' n : ℕ, (χ⁻¹) n * (n : ℂ) ^ (-(1 - s)) * afeWeight χ⁻¹ (1 - s) (afeScale N n)) := by
          rw [hγ, hdual_tsum]
    _ = rightInt χ⁻¹ (1 - s) := hT
    _ = dualInt χ s := hri

/-- The vertical-line identity in complex form:
`(2π)·Λ(s) = ∫ lineRight − ∫ lineLeft`. -/
lemma vertical_identity_two_pi (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (hprim : χ.IsPrimitive) {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1)
    (hΛ : AfeVerticalLine.Λ_growth χ s) :
    (2 * Real.pi : ℂ) * DirichletCharacter.completedLFunction χ s = rightInt χ s - leftInt χ s := by
  have hvi := AfeVerticalLine.vertical_line_identity χ hχ hprim s hs0 hs1
    (x := scale N) (scale_pos N) hΛ
  dsimp [rightInt, leftInt] at hvi
  rw [hvi]
  dsimp [rightInt, leftInt]
  simp
  field_simp [Real.pi_ne_zero]

/-- Commuted version of the scale identity with a trailing factor `X`. -/
private lemma scale_cpow_mul (s v : ℂ) (X : ℂ) :
    (scale N : ℂ) ^ (1 + I * v) * ((N : ℂ) ^ (3 / 2 - s + I * v) * X)
      = (N : ℂ) ^ (1 / 2 - s) * ((scale N : ℂ) ^ (-(1 + I * v)) * X) := by
  have h := scale_cpow_identity (N := N) s v
  calc
    (scale N : ℂ) ^ (1 + I * v) * ((N : ℂ) ^ (3 / 2 - s + I * v) * X)
        = ((scale N : ℂ) ^ (1 + I * v) * (N : ℂ) ^ (3 / 2 - s + I * v)) * X := by
          rw [mul_assoc]
    _ = ((N : ℂ) ^ (1 / 2 - s) * (scale N : ℂ) ^ (-(1 + I * v))) * X := by
          unfold scale at *
          rw [h]
    _ = (N : ℂ) ^ (1 / 2 - s) * ((scale N : ℂ) ^ (-(1 + I * v)) * X) := by
          rw [mul_assoc]

/-- Pointwise transformation of the left-line integrand under `y ↦ −y`:
`lineLeft (−y) = −ε(χ)·N^(1/2−s)·dualIntegrand y` (with `ε = rootNumber χ`). -/
lemma lineLeft_neg (χ : DirichletCharacter ℂ N) (hprim : χ.IsPrimitive) (s : ℂ) (y : ℝ) :
    lineLeft χ s (scale N) (-y) =
      -(χ.rootNumber * (N : ℂ) ^ (1 / 2 - s) * dualIntegrand χ s y) := by
  unfold lineLeft dualIntegrand
  rw [show (-1 + I * ((-y : ℝ) : ℂ)) = -(1 + I * (y : ℂ)) by
    apply Complex.ext <;> simp <;> ring]
  rw [show (s - 1 + I * ((-y : ℝ) : ℂ)) = (s - 1 - I * (y : ℂ)) by
    apply Complex.ext <;> simp <;> ring]
  rw [show -(-(1 + I * (y : ℂ))) = (1 + I * (y : ℂ)) by ring]
  have hFE := Structural.completedLFunction_eq_rootNumber_mul χ hprim (s - 1 - I * (y : ℂ))
  rw [hFE]
  rw [show (1 / 2 : ℂ) - (s - 1 - I * (y : ℂ)) = 3 / 2 - s + I * (y : ℂ) by ring]
  rw [show 1 - (s - 1 - I * (y : ℂ)) = 2 - s + I * (y : ℂ) by ring]
  rw [Structural.smoothingFunction_even (1 + I * (y : ℂ))]
  rw [mul_assoc, mul_assoc, mul_assoc]
  rw [scale_cpow_mul s y
    (χ.rootNumber * (DirichletCharacter.completedLFunction (χ⁻¹) (2 - s + I * (y : ℂ)) * smoothingFunction (1 + I * (y : ℂ))))]
  field_simp

/-- The left-line integral transforms into the dual Mellin integral:
`∫ lineLeft = −ε(χ)·N^(1/2−s)·∫ dualIntegrand`. -/
lemma leftInt_eq_neg_root (χ : DirichletCharacter ℂ N) (hprim : χ.IsPrimitive) (s : ℂ) :
    leftInt χ s = -(χ.rootNumber * (N : ℂ) ^ (1 / 2 - s) * dualInt χ s) := by
  unfold leftInt dualInt
  have hsub : (∫ y : ℝ, lineLeft χ s (scale N) y) = ∫ v : ℝ, lineLeft χ s (scale N) (-v) := by
    simpa using (Measure.integral_comp_mul_left (g := fun x : ℝ => lineLeft χ s (scale N) x)
      (-1 : ℝ)).symm
  rw [hsub]
  have hpt : (fun v : ℝ => lineLeft χ s (scale N) (-v)) =
      fun v : ℝ => -(χ.rootNumber * (N : ℂ) ^ (1 / 2 - s) * dualIntegrand χ s v) := by
    funext v
    exact lineLeft_neg χ hprim s v
  rw [hpt]
  rw [show (fun v : ℝ => -(χ.rootNumber * (N : ℂ) ^ (1 / 2 - s) * dualIntegrand χ s v))
        = fun v : ℝ => (-(χ.rootNumber * (N : ℂ) ^ (1 / 2 - s))) * dualIntegrand χ s v by
        funext v; ring]
  rw [MeasureTheory.integral_const_mul]
  ring

/-- **The approximate functional equation** (two-sided, smoothed), under the strip-growth
hypothesis. -/
theorem afe_identity (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (hprim : χ.IsPrimitive)
    {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) (hΛ : AfeVerticalLine.Λ_growth χ s) :
    DirichletCharacter.LFunction χ s =
      afeMain χ s
        + χ.rootNumber * (N : ℂ) ^ (1 / 2 - s)
            * (χ.gammaFactor (1 - s) / χ.gammaFactor s) * afeDual χ s := by
  have hL := Structural.LFunction_eq_completed_div_gammaFactor_of_zero_lt_re χ hs0
  have hg0 : χ.gammaFactor s ≠ 0 := Structural.gammaFactor_ne_zero_of_zero_lt_re χ hs0
  have h2π0 : (2 * Real.pi : ℂ) ≠ 0 := by
    exact mul_ne_zero (by norm_num) (ofReal_ne_zero.mpr Real.pi_ne_zero)
  have hmain := main_sum_eq_rightInt χ hs0
  have hdual := dual_sum_eq_dualInt χ hs0 hs1
  have hleft := leftInt_eq_neg_root χ hprim s
  have hvert := vertical_identity_two_pi χ hχ hprim (s := s) hs0 hs1 hΛ
  rw [hL]
  have h1 : DirichletCharacter.completedLFunction χ s =
      χ.gammaFactor s * afeMain χ s
        + χ.rootNumber * (N : ℂ) ^ (1 / 2 - s) * χ.gammaFactor (1 - s) * afeDual χ s := by
    refine (mul_left_cancel₀ h2π0) ?_
    calc
      (2 * Real.pi : ℂ) * DirichletCharacter.completedLFunction χ s = rightInt χ s - leftInt χ s := hvert
      _ = (2 * Real.pi : ℂ) * (χ.gammaFactor s * afeMain χ s)
            + χ.rootNumber * (N : ℂ) ^ (1 / 2 - s)
                * ((2 * Real.pi : ℂ) * χ.gammaFactor (1 - s)) * afeDual χ s := by
          rw [← hmain, hleft, ← hdual]
          ring
      _ = (2 * Real.pi : ℂ) * (χ.gammaFactor s * afeMain χ s
            + χ.rootNumber * (N : ℂ) ^ (1 / 2 - s) * χ.gammaFactor (1 - s) * afeDual χ s) := by
          ring
  rw [h1]
  field_simp [hg0]

end
end PL.AfeProof


/-!
# The two-sided approximate functional equation (final theorem)

This file assembles the **exact smooth approximate functional equation** for the Dirichlet
L-function of a primitive non-trivial character `χ` of conductor `N`, for `0 < Re s < 1`:

`L(s, χ) = Σₙ χ(n)·n^(-s)·W_s(n/√N)
         + ε(χ)·N^(1/2-s)·(γ(1-s)/γ(s))·Σₙ χ̄(n)·n^(s-1)·W_{1-s}(n/√N)`.

The proof combines (see the headers of `Submission/AfeProof.lean` and
`Submission/AfeVerticalLine.lean` for details):
* the vertical-line identity `PL.AfeVerticalLine.vertical_line_identity`
  (`Λ(s) = (1/2π)(∫ lineRight − ∫ lineLeft)`, with the rectangle/Cauchy `T → ∞` passage,
  whose strip-growth hypothesis `Λ_growth` is supplied by
  `PL.AfeGrowth.lambda_growth` from the Mellin-representation bounds of
  `Submission/MellinGrowth.lean` + `Submission/CompletedStrip.lean`),
* the Mellin-inversion step `PL.AfeMellin.main_sum_eq_completed_integral`
  (`2π·γ(s)·main = ∫ lineRight`) and its dual mirror for `χ⁻¹` at `1 − s`
  (`2π·γ(1-s)·dual = ∫ dualIntegrand`),
* the functional-equation transformation of the left-line integral
  (`∫ lineLeft = −ε(χ)·N^(1/2-s)·∫ dualIntegrand`, via the substitution `y ↦ −y`).

The theorem is the Dirichlet-L-function instance of [Iwaniec--Kowalski, Theorem 5.3].
-/

open Complex DirichletCharacter Filter Topology
open scoped Real Topology BigOperators

set_option autoImplicit false

namespace PL.AFE

noncomputable section

variable {N : ℕ} [NeZero N]

/--
**Approximate functional equation** for the Dirichlet L-function of a primitive character
`χ` of conductor `N`, for `0 < Re s < 1`:

`L(s, χ) = Σₙ χ(n) n⁻ˢ Wₛ(n/√N)
         + ε(χ) · N^(1/2 - s) · (γ(1-s)/γ(s)) · Σₙ χ̄(n) n^(s-1) W₁₋ₛ(n/√N)`.

Both sums are over `n ≥ 1` and converge absolutely.
-/
theorem approx_functional_equation (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive)
    (hχne : χ ≠ 1) {s : ℂ} (hs₀ : 0 < s.re) (hs₁ : s.re < 1) :
    DirichletCharacter.LFunction χ s =
      (∑' n : ℕ, χ n * (n : ℂ) ^ (-s) * afeWeight χ s (afeScale N n))
        + χ.rootNumber * (N : ℂ) ^ (1 / 2 - s)
            * (χ.gammaFactor (1 - s) / χ.gammaFactor s)
            * (∑' n : ℕ, (χ⁻¹) n * (n : ℂ) ^ (-(1 - s)) * afeWeight χ (1 - s) (afeScale N n)) := by
  have hΛ : AfeVerticalLine.Λ_growth χ s :=
    AfeGrowth.lambda_growth χ hχ hχne hs₀ hs₁
  rw [AfeProof.afe_identity χ hχne hχ (s := s) hs₀ hs₁ hΛ]
  rfl

end
end PL.AFE


/-!
# Polynomial-in-`|Im z|` bounds for the AFE weights (roadmap item: [5a])

The AFE weights satisfy `‖W_z(x)‖ ≤ C(z)·x⁻¹` for `x > 0`
(`PL.AfeBounds.even_weight_afe_norm_le_exists`), but the constant `C(z)` arising
there (via `GammaRatioEven`-type *uniform-in-t* ratio bounds) hides a dependence on
`Im z` that is at best **exponential** in `|Im z|` (the denominator `|Gammaℝ z|` decays
like `e^{-π|Im z|/4}`).  For every later growth bound (t-aspect convexity growth,
truncation of the AFE) we need constants that are **polynomial in `(1 + |Im z|)`**.

The reason a polynomial constant is true is that the *Mellin integral* defining
`W_z(x)` is dominated in `t` by

`|Gammaℝ (z + 1 + I t) / Gammaℝ z| · e^{1 - t²} · |1 + I t|⁻¹`,

and the ratio is bounded, via the Stirling layer
(`PL.GammaℝPoly.gammaℝ_norm_upper` / `.gammaℝ_norm_lower`), by

`C · (1+|T+t|)^{(Re z+1)/2}·(1+|T|)^{1 - Re z/2} · e^{(π/4)(|T|-|T+t|)}`  (`T = Im z`),

whose *exponential part* `e^{(π/4)(|T|-|T+t|)} ≤ e^{(π/4)|t|}` is killed by the Gaussian
`e^{-t²}` (which stays integrable after multiplication by a polynomial in `|t|`), leaving
only a polynomial in `(1+|T|)` in front of the convergent `∫` over `t`.

## Main results

* `gammaℝ_ratio_poly_shift`:  for `0 < a` and a parameter `T`, a pointwise bound on
  `|Gammaℝ ((a:ℂ) + I·(T+t)) / Gammaℝ (a0:ℂ + I·T)|` for a fixed real-part `a0 ∈ (0, 1)`,
  that is polynomial in `(1+|T|)` times a function of `t` integrable against `e^{-t²}`.
* `weightEven_mellin_norm_poly` / `weightOdd_mellin_norm_poly`:
  `‖mellinInv 1 (weightEven (a0 + I·T)) x‖ ≤ C·(1+|T|)^k·x⁻¹` for `x > 0`, `T ∈ ℝ`,
  for a fixed `a0` with `0 < a0` (resp. `a0 + 1`), with `C, k` independent of `T`.

These give the **polynomial weight bounds** used by the growth/truncation layer.
-/

open Complex Filter MeasureTheory Set
open scoped Real
open PL.AFE
set_option autoImplicit false

namespace PL.WeightPoly
/-- The norm of `Gammaℝ` two units to the right is at least `a/(2π)` times the original,
for `Re = a > 0`. -/
lemma gammaℝ_norm_shift_two (a : ℝ) (ha : 0 < a) (T : ℝ) :
    (a / (2 * Real.pi)) * ‖Complex.Gammaℝ ((a : ℂ) + I * (T : ℂ))‖ ≤
      ‖Complex.Gammaℝ (((a : ℂ) + I * (T : ℂ)) + 2)‖ := by
  let s : ℂ := (a : ℂ) + I * (T : ℂ)
  have hs : s ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp [s] at hre
    linarith
  have hsre : s.re = a := by simp [s]
  have hle : a ≤ ‖s‖ := by
    have h := Complex.abs_re_le_norm s
    rw [hsre] at h
    exact le_of_abs_le h
  have h2 : ‖(((2 * Real.pi : ℝ) : ℂ))‖ = 2 * Real.pi := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_nonneg (by positivity : 0 ≤ 2 * Real.pi)]
  have hnorm_s : ‖s / (((2 * Real.pi : ℝ) : ℂ))‖ = ‖s‖ / (2 * Real.pi) := by
    rw [Complex.norm_div, h2]
  have hdiv : a / (2 * Real.pi) ≤ ‖s / (((2 * Real.pi : ℝ) : ℂ))‖ := by
    rw [hnorm_s]
    exact div_le_div_of_nonneg_right hle (by positivity : 0 ≤ 2 * Real.pi)
  have hmul : Complex.Gammaℝ (s + 2) = Complex.Gammaℝ s * (s / (((2 * Real.pi : ℝ) : ℂ))) := by
    have hg := Complex.Gammaℝ_add_two (s := s) hs
    rw [hg]
    rw [show (s / (((2 * Real.pi : ℝ) : ℂ))) = s / 2 / (Real.pi : ℂ) by
      field_simp [Real.pi_ne_zero]
      norm_num]
    ring
  calc
    (a / (2 * Real.pi)) * ‖Complex.Gammaℝ s‖
        ≤ ‖s / (((2 * Real.pi : ℝ) : ℂ))‖ * ‖Complex.Gammaℝ s‖ := by
          exact mul_le_mul_of_nonneg_right hdiv (norm_nonneg _)
    _ = ‖Complex.Gammaℝ s * (s / (((2 * Real.pi : ℝ) : ℂ)))‖ := by rw [norm_mul, mul_comm]
    _ = ‖Complex.Gammaℝ (s + 2)‖ := by rw [hmul]

/-- Any two-step shift of a polynomial lower bound stays a polynomial lower bound (at the
same exponent, with a worsened constant). -/
lemma gammaℝ_norm_lower_shift_iter (a : ℝ) (ha : 0 < a) {p c : ℝ} (hc : 0 < c)
    (hbase : ∀ T : ℝ,
      c * (1 + |T|) ^ p * Real.exp (-(Real.pi / 4) * |T|) ≤
        ‖Complex.Gammaℝ ((a : ℂ) + I * (T : ℂ))‖) :
    ∀ n : ℕ, ∃ c', 0 < c' ∧ ∀ T : ℝ,
      c' * (1 + |T|) ^ p * Real.exp (-(Real.pi / 4) * |T|) ≤
        ‖Complex.Gammaℝ (((a + 2 * (n : ℝ) : ℝ) : ℂ) + I * (T : ℂ))‖ := by
  intro n
  induction n with
  | zero =>
      refine ⟨c, hc, ?_⟩
      intro T
      simpa using hbase T
  | succ n ih =>
      obtain ⟨c₀, hc₀, hc₀body⟩ := ih
      let a₀ : ℝ := a + 2 * (n : ℝ)
      have ha₀ : 0 < a₀ := by
        dsimp [a₀]
        positivity
      refine ⟨c₀ * (a₀ / (2 * Real.pi)), mul_pos hc₀ (by positivity), ?_⟩
      intro T
      have hs := gammaℝ_norm_shift_two a₀ ha₀ T
      have harg : (((a₀ : ℂ) + I * (T : ℂ)) + 2) =
          ((a + 2 * ((n + 1 : ℕ) : ℝ) : ℝ) : ℂ) + I * (T : ℂ) := by
        apply Complex.ext <;> simp [a₀]
        ring
      calc
        (c₀ * (a₀ / (2 * Real.pi))) * (1 + |T|) ^ p
            * Real.exp (-(Real.pi / 4) * |T|)
            = (a₀ / (2 * Real.pi)) * (c₀ * (1 + |T|) ^ p
                * Real.exp (-(Real.pi / 4) * |T|)) := by ring
        _ ≤ (a₀ / (2 * Real.pi)) * ‖Complex.Gammaℝ ((a₀ : ℂ) + I * (T : ℂ))‖ := by
            exact mul_le_mul_of_nonneg_left (hc₀body T) (by positivity)
        _ ≤ ‖Complex.Gammaℝ (((a₀ : ℂ) + I * (T : ℂ)) + 2)‖ := hs
        _ = ‖Complex.Gammaℝ (((a + 2 * ((n + 1 : ℕ) : ℝ) : ℝ) : ℂ) + I * (T : ℂ))‖ := by
            rw [harg]

/-- Real-part decomposition: every positive real is `a' + 2n` with `0 < a' ≤ 2`. -/
lemma exists_real_part_reduce (a : ℝ) (ha : 0 < a) :
    ∃ (n : ℕ) (a' : ℝ), 0 < a' ∧ a' ≤ 2 ∧ a = a' + 2 * (n : ℝ) := by
  by_cases hle : a ≤ 2
  · refine ⟨0, a, ha, hle, ?_⟩
    ring
  · have hgt : 2 < a := lt_of_not_ge hle
    let m : ℕ := Nat.ceil (a / 2)
    have hpos : 0 < a / 2 := by positivity
    have hm_le : a / 2 ≤ (m : ℝ) := by
      exact (Nat.ceil_le (a := a / 2) (n := m)).1 le_rfl
    have hm_ge1 : 1 ≤ m := by
      have h1 : (1 : ℝ) < a / 2 := by nlinarith
      have hm1 : (1 : ℝ) < (m : ℝ) := lt_of_lt_of_le h1 hm_le
      exact_mod_cast (le_of_lt hm1)
    let n : ℕ := m - 1
    have hsub : (n : ℝ) + 1 = (m : ℝ) := by
      have hm_eq : m = n + 1 := by
        dsimp [n]
        omega
      exact_mod_cast hm_eq.symm
    let a' : ℝ := a - 2 * (n : ℝ)
    have ha'0 : 0 < a' := by
      dsimp [a']
      have hcl : (m : ℝ) < a / 2 + 1 := Nat.ceil_lt_add_one (le_of_lt hpos)
      have hn : (n : ℝ) < a / 2 := by linarith
      linarith
    have ha'2 : a' ≤ 2 := by
      dsimp [a']
      linarith
    refine ⟨n, a', ha'0, ha'2, ?_⟩
    dsimp [a']
    ring

/-- Lower bound for `‖Gammaℝ (a + I T)‖` for `0 < a ≤ 2`. -/
lemma gammaℝ_norm_lower_le_two (a : ℝ) (ha0 : 0 < a) (ha2 : a ≤ 2) :
    ∃ c p : ℝ, 0 < c ∧ p ≤ 0 ∧ ∀ T : ℝ,
      c * (1 + |T|) ^ p * Real.exp (-(Real.pi / 4) * |T|) ≤
        ‖Complex.Gammaℝ ((a : ℂ) + I * (T : ℂ))‖ := by
  by_cases hlt : a < 2
  · obtain ⟨c0, hc0, hb⟩ := PL.GammaℝPoly.gammaℝ_norm_lower a ha0 hlt
    refine ⟨c0, a / 2 - 1, hc0, by nlinarith, ?_⟩
    intro T
    exact hb T
  · have haeq : a = 2 := le_antisymm ha2 (le_of_not_gt hlt)
    obtain ⟨c, hcpos, hb⟩ := gamma_one_lower
    refine ⟨c / Real.pi, 0, div_pos hcpos Real.pi_pos, le_rfl, ?_⟩
    rw [haeq]
    intro T
    have hnorm : ‖Complex.Gammaℝ ((2 : ℂ) + I * (T : ℂ))‖
        = (Real.pi ^ (-1 : ℝ)) * ‖Complex.Gamma (((2 : ℂ) + I * (T : ℂ)) / 2)‖ := by
      rw [Complex.Gammaℝ_def, Complex.norm_mul]
      rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
      congr 1
      simp
    have harg : ((2 : ℂ) + I * (T : ℂ)) / 2 = (1 : ℂ) + I * ((T / 2 : ℝ) : ℂ) := by
      apply Complex.ext <;> simp
    have hb' : c * Real.exp (-(Real.pi / 4) * |T|) ≤
        ‖Complex.Gamma (((2 : ℂ) + I * (T : ℂ)) / 2)‖ := by
      have h2 := hb (T / 2)
      have hExp : -(Real.pi / 2) * |T / 2| = -(Real.pi / 4) * |T| := by
        rw [abs_div]
        norm_num
        ring
      rw [← harg] at h2
      rwa [hExp] at h2
    have hπ : Real.pi ^ (-1 : ℝ) = 1 / Real.pi := by
      rw [Real.rpow_neg_one]
      norm_num
    calc
      (c / Real.pi) * (1 + |T|) ^ (0 : ℝ) * Real.exp (-(Real.pi / 4) * |T|)
          = (c / Real.pi) * Real.exp (-(Real.pi / 4) * |T|) := by simp
      _ = (Real.pi ^ (-1 : ℝ)) * (c * Real.exp (-(Real.pi / 4) * |T|)) := by
            rw [hπ]
            ring
      _ ≤ (Real.pi ^ (-1 : ℝ)) * ‖Complex.Gamma (((2 : ℂ) + I * (T : ℂ)) / 2)‖ := by
            exact mul_le_mul_of_nonneg_left hb' (by positivity : 0 ≤ Real.pi ^ (-1 : ℝ))
      _ = ‖Complex.Gammaℝ ((2 : ℂ) + I * (T : ℂ))‖ := by exact hnorm.symm

/-- Lower bound for `‖Gammaℝ (a + I T)‖` with exponential decay `exp (-(π/4)|T|)` and an
arbitrary (non-positive) polynomial power `(1 + |T|)^p`, valid for every real part `a > 0`. -/
lemma gammaℝ_norm_lower_any (a : ℝ) (ha : 0 < a) :
    ∃ c p : ℝ, 0 < c ∧ p ≤ 0 ∧ ∀ T : ℝ,
      c * (1 + |T|) ^ p * Real.exp (-(Real.pi / 4) * |T|) ≤
        ‖Complex.Gammaℝ ((a : ℂ) + I * (T : ℂ))‖ := by
  obtain ⟨n, a', ha'0, ha'2, haeq⟩ := exists_real_part_reduce a ha
  obtain ⟨c0, p0, hc0, hp0, hb0⟩ := gammaℝ_norm_lower_le_two a' ha'0 ha'2
  obtain ⟨c, hc, hcbody⟩ := gammaℝ_norm_lower_shift_iter a' ha'0 hc0 hb0 n
  refine ⟨c, p0, hc, hp0, ?_⟩
  intro T
  have hT := hcbody T
  simpa [haeq] using hT

/-- Pointwise ratio bound for any real part `a > 0`. -/
lemma gammaℝ_ratio_poly_any (a : ℝ) (ha : 0 < a) :
    ∃ C k l : ℝ, 0 < C ∧ 0 ≤ k ∧ 0 ≤ l ∧ ∀ (T t : ℝ),
      ‖Complex.Gammaℝ (((a : ℂ) + 1) + I * ((T + t : ℝ) : ℂ)) /
          Complex.Gammaℝ ((a : ℂ) + I * (T : ℂ))‖ ≤
        C * (1 + |T|) ^ k * (1 + |t|) ^ l * Real.exp ((Real.pi / 4) * |t|) := by
  obtain ⟨Cu, hCu, hNu⟩ := PL.GammaℝPoly.gammaℝ_norm_upper (a + 1) (by linarith)
  obtain ⟨cl, q, hcl, hq0, hNl⟩ := gammaℝ_norm_lower_any a ha
  let p : ℝ := (a + 1) / 2
  have hp0 : 0 ≤ p := by dsimp [p]; positivity
  have hk0 : 0 ≤ p - q := by dsimp [p]; nlinarith
  refine ⟨Cu / cl, p - q, p, div_pos hCu hcl, hk0, hp0, ?_⟩
  intro T t
  let M : ℝ := 1 + |T + t|
  let B : ℝ := 1 + |T|
  let D : ℝ := 1 + |t|
  let eN : ℝ := Real.exp (-(Real.pi / 4) * |T + t|)
  let eD : ℝ := Real.exp (-(Real.pi / 4) * |T|)
  let J : ℝ := Real.exp ((Real.pi / 4) * |t|)
  have hBpos : 0 < B := by dsimp [B]; positivity
  have hDpos : 0 < D := by dsimp [D]; positivity
  have hMpos : 0 < M := by dsimp [M]; positivity
  have hBp : 0 ≤ B ^ p := Real.rpow_nonneg (le_of_lt hBpos) p
  have hBq : 0 ≤ B ^ q := Real.rpow_nonneg (le_of_lt hBpos) q
  have hnum_arg : ((a : ℂ) + 1) + I * ((T + t : ℝ) : ℂ) =
      ((a + 1 : ℝ) : ℂ) + I * ((T + t : ℝ) : ℂ) := by
    apply Complex.ext <;> simp
  have hNum : ‖Complex.Gammaℝ (((a : ℂ) + 1) + I * ((T + t : ℝ) : ℂ))‖ ≤
      Cu * M ^ p * eN := by
    have h := hNu (T + t)
    rw [← hnum_arg] at h
    simpa [M, p, eN] using h
  have hDen : cl * B ^ q * eD ≤ ‖Complex.Gammaℝ ((a : ℂ) + I * (T : ℂ))‖ := by
    have h := hNl T
    simpa [B, eD] using h
  have hnum_nonneg : 0 ≤ Cu * M ^ p * eN := by
    have hMp : 0 ≤ M ^ p := Real.rpow_nonneg (by positivity : 0 ≤ M) p
    positivity
  have hden_pos : 0 < cl * B ^ q * eD := by
    have hBqpos : 0 < B ^ q := Real.rpow_pos_of_pos hBpos q
    positivity
  have hAbs1 : |T| - |T + t| ≤ |t| := by
    have htri : |T| ≤ |T + t| + |t| := by
      have h := abs_add_le (T + t) (-t)
      simpa [abs_neg] using h
    linarith
  have hM : M ≤ B * D := by
    dsimp [M, B, D]
    have htri : |T + t| ≤ |T| + |t| := abs_add_le T t
    nlinarith [mul_nonneg (abs_nonneg T) (abs_nonneg t)]
  have hMp_le : M ^ p ≤ B ^ p * D ^ p := by
    have h1 : M ^ p ≤ (B * D) ^ p := Real.rpow_le_rpow (by positivity : 0 ≤ M) hM hp0
    have h2 : (B * D) ^ p = B ^ p * D ^ p := Real.mul_rpow (le_of_lt hBpos) (le_of_lt hDpos)
    rw [h2] at h1
    exact h1
  have hExp1 : eN / eD ≤ J := by
    have heq : eN / eD = Real.exp ((Real.pi / 4) * (|T| - |T + t|)) := by
      dsimp [eN, eD]
      rw [← Real.exp_sub]
      congr 1
      ring
    rw [heq]
    dsimp [J]
    exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hAbs1 (by positivity : 0 ≤ Real.pi / 4))
  have hfrac_le : (M ^ p * eN) / (B ^ q * eD) ≤ (B ^ p * D ^ p / B ^ q) * J := by
    have hMq : M ^ p / B ^ q ≤ B ^ p * D ^ p / B ^ q := by
      exact div_le_div_of_nonneg_right hMp_le hBq
    have hquad : (M ^ p / B ^ q) * (eN / eD) ≤ (B ^ p * D ^ p / B ^ q) * J := by
      exact mul_le_mul hMq hExp1 (by positivity : 0 ≤ eN / eD)
        (div_nonneg (mul_nonneg hBp (Real.rpow_nonneg (le_of_lt hDpos) p)) hBq)
    have hsplit : (M ^ p * eN) / (B ^ q * eD) = (M ^ p / B ^ q) * (eN / eD) := by
      field_simp [ne_of_gt (Real.rpow_pos_of_pos hBpos q), ne_of_gt (Real.exp_pos _)]
    rw [hsplit]
    exact hquad
  have hcomb : B ^ p * D ^ p / B ^ q = D ^ p * B ^ (p - q) := by
    have hr : B ^ p / B ^ q = B ^ (p - q) := (Real.rpow_sub hBpos p q).symm
    calc
      B ^ p * D ^ p / B ^ q = D ^ p * (B ^ p / B ^ q) := by ring
      _ = D ^ p * B ^ (p - q) := by rw [hr]
  have hfin_eq : (Cu / cl) * (((B ^ p * D ^ p) / B ^ q) * J) =
      (Cu / cl) * (1 + |T|) ^ (p - q) * (1 + |t|) ^ p * Real.exp ((Real.pi / 4) * |t|) := by
    rw [hcomb]
    rw [show B = 1 + |T| by rfl, show D = 1 + |t| by rfl,
        show J = Real.exp ((Real.pi / 4) * |t|) by rfl]
    ring
  calc
    ‖Complex.Gammaℝ (((a : ℂ) + 1) + I * ((T + t : ℝ) : ℂ)) /
        Complex.Gammaℝ ((a : ℂ) + I * (T : ℂ))‖
        = ‖Complex.Gammaℝ (((a : ℂ) + 1) + I * ((T + t : ℝ) : ℂ))‖ /
            ‖Complex.Gammaℝ ((a : ℂ) + I * (T : ℂ))‖ := by rw [norm_div]
    _ ≤ (Cu * M ^ p * eN) / ‖Complex.Gammaℝ ((a : ℂ) + I * (T : ℂ))‖ := by
          exact div_le_div_of_nonneg_right hNum (norm_nonneg _)
    _ ≤ (Cu * M ^ p * eN) / (cl * B ^ q * eD) := by
          exact div_le_div_of_nonneg_left hnum_nonneg hden_pos hDen
    _ = (Cu / cl) * ((M ^ p * eN) / (B ^ q * eD)) := by
          have hcq : (cl * B ^ q * eD) ≠ 0 := ne_of_gt hden_pos
          field_simp [hcl.ne', hcq]
    _ ≤ (Cu / cl) * (((B ^ p * D ^ p) / B ^ q) * J) := by
          exact mul_le_mul_of_nonneg_left hfrac_le (le_of_lt (div_pos hCu hcl))
    _ = (Cu / cl) * (1 + |T|) ^ (p - q) * (1 + |t|) ^ p * Real.exp ((Real.pi / 4) * |t|) := by
          exact hfin_eq

/-- Auxiliary pointwise domination by a Gaussian (non-negative `u` version). -/
lemma gauss_aux (s u : ℝ) (hs : 0 ≤ s) (hu : 0 ≤ u) :
    (1 + u) ^ s * Real.exp ((Real.pi / 4) * u - u ^ 2) ≤
      Real.exp ((s + Real.pi / 4) ^ 2 / 2) * Real.exp (-(1 / 2 : ℝ) * u ^ 2) := by
  have hlog : Real.log (1 + u) ≤ u := by
    have hle1 : 1 + u ≤ Real.exp u := by
      simpa [add_comm] using (Real.add_one_le_exp u)
    exact (Real.log_le_iff_le_exp (by positivity : 0 < 1 + u)).2 hle1
  have hmain : s * Real.log (1 + u) + (Real.pi / 4) * u - u ^ 2 / 2
      ≤ (s + Real.pi / 4) ^ 2 / 2 := by
    have h1 : s * Real.log (1 + u) ≤ s * u := mul_le_mul_of_nonneg_left hlog hs
    have h2 : s * u + (Real.pi / 4) * u - u ^ 2 / 2 ≤ (s + Real.pi / 4) ^ 2 / 2 := by
      have hsq : 0 ≤ (u - (s + Real.pi / 4)) ^ 2 := sq_nonneg _
      nlinarith
    linarith
  calc
    (1 + u) ^ s * Real.exp ((Real.pi / 4) * u - u ^ 2)
        = Real.exp (s * Real.log (1 + u) + (Real.pi / 4) * u - u ^ 2) := by
          rw [Real.rpow_def_of_pos (by positivity : 0 < 1 + u) s]
          rw [← Real.exp_add]
          congr 1
          ring
    _ = Real.exp (s * Real.log (1 + u) + (Real.pi / 4) * u - u ^ 2 / 2)
            * Real.exp (-(1 / 2 : ℝ) * u ^ 2) := by
          rw [← Real.exp_add]
          congr 1
          ring
    _ ≤ Real.exp ((s + Real.pi / 4) ^ 2 / 2) * Real.exp (-(1 / 2 : ℝ) * u ^ 2) := by
          exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 hmain) (Real.exp_pos _).le

/-- A polynomial factor times the exponential is dominated by a pure Gaussian:
for `0 ≤ s` there is a constant `A` with
`(1+|t|)^s · exp ((π/4)|t| − t²) ≤ A · exp (−t²/2)` for every real `t`. -/
lemma poly_gaussian_bound (s : ℝ) (hs : 0 ≤ s) :
    ∃ A : ℝ, 0 < A ∧ ∀ t : ℝ,
      (1 + |t|) ^ s * Real.exp ((Real.pi / 4) * |t| - t ^ 2) ≤
        A * Real.exp (-(1 / 2 : ℝ) * t ^ 2) := by
  refine ⟨Real.exp ((s + Real.pi / 4) ^ 2 / 2), Real.exp_pos _, ?_⟩
  intro t
  rw [← sq_abs]
  exact gauss_aux s |t| hs (abs_nonneg t)

/-- **Pointwise ratio bound with explicit polynomial-in-`T` and Gaussian-in-`t` structure.**
For `0 < a0`, real `T, t`, and with `z = a0 + I·T`:

`‖Gammaℝ (z + 1 + I·t) / Gammaℝ z‖ ≤ C · (1+|T|)^k · (1+|t|)^l · exp((π/4)·|t|)`.
-/
lemma gammaℝ_ratio_even_pointwise_poly (a0 : ℝ) (ha0 : 0 < a0) :
    ∃ C k l : ℝ, 0 < C ∧ 0 ≤ k ∧ 0 ≤ l ∧ ∀ (T t : ℝ),
      ‖Complex.Gammaℝ ((a0 : ℂ) + I * ((T + t : ℝ) : ℂ) + 1) /
          Complex.Gammaℝ ((a0 : ℂ) + I * (T : ℂ))‖ ≤
        C * (1 + |T|) ^ k * (1 + |t|) ^ l * Real.exp ((Real.pi / 4) * |t|) := by
  obtain ⟨C, k, l, hC, hk, hl, hb⟩ := gammaℝ_ratio_poly_any a0 ha0
  refine ⟨C, k, l, hC, hk, hl, ?_⟩
  intro T t
  have harg : ((a0 : ℂ) + I * ((T + t : ℝ) : ℂ)) + 1 =
      ((a0 : ℂ) + 1) + I * ((T + t : ℝ) : ℂ) := by
    apply Complex.ext <;> simp
  calc
    ‖Complex.Gammaℝ ((a0 : ℂ) + I * ((T + t : ℝ) : ℂ) + 1) /
        Complex.Gammaℝ ((a0 : ℂ) + I * (T : ℂ))‖
        = ‖Complex.Gammaℝ (((a0 : ℂ) + 1) + I * ((T + t : ℝ) : ℂ)) /
            Complex.Gammaℝ ((a0 : ℂ) + I * (T : ℂ))‖ := by
          congr 1
          rw [harg]
    _ ≤ C * (1 + |T|) ^ k * (1 + |t|) ^ l * Real.exp ((Real.pi / 4) * |t|) := hb T t

lemma weightEven_poly_vertical (a0 : ℝ) (ha0 : 0 < a0) :
    ∃ C k : ℝ, 0 < C ∧ 0 ≤ k ∧ ∀ (T t : ℝ),
      ‖weightEven ((a0 : ℂ) + I * (T : ℂ)) (1 + I * (t : ℂ))‖ ≤
        C * (1 + |T|) ^ k * Real.exp (-(1 / 2 : ℝ) * t ^ 2) := by
  obtain ⟨C0, k0, l0, hC0, hk0, hl0, hratio⟩ := gammaℝ_ratio_poly_any a0 ha0
  obtain ⟨A, hApos, hAb⟩ := poly_gaussian_bound l0 hl0
  refine ⟨C0 * Real.exp 1 * A, k0, mul_pos (mul_pos hC0 (Real.exp_pos _)) hApos, hk0, ?_⟩
  intro T t
  let z : ℂ := (a0 : ℂ) + I * (T : ℂ)
  let u : ℂ := 1 + I * (t : ℂ)
  let B : ℝ := 1 + |T|
  let D : ℝ := 1 + |t|
  let J : ℝ := Real.exp ((Real.pi / 4) * |t|)
  let G2 : ℝ := Real.exp (-(1 / 2 : ℝ) * t ^ 2)
  have harg : z + u = ((a0 : ℂ) + 1) + I * ((T + t : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [z, u]
  have hr : ‖Complex.Gammaℝ (z + u) / Complex.Gammaℝ z‖ ≤
      C0 * B ^ k0 * D ^ l0 * J := by
    rw [harg]
    simpa [B, D, J] using hratio T t
  have hB0 : 0 ≤ B := by dsimp [B]; positivity
  have hD0 : 0 ≤ D := by dsimp [D]; positivity
  have hBk : 0 ≤ B ^ k0 := Real.rpow_nonneg hB0 k0
  have hDl : 0 ≤ D ^ l0 := Real.rpow_nonneg hD0 l0
  have hc_le : ‖cexp (u ^ 2)‖ ≤ Real.exp (1 - t ^ 2) := by
    dsimp [u]
    rw [WeightConvergesEven.norm_cexp_sq t]
  have hinv : ‖u⁻¹‖ ≤ 1 := by
    dsimp [u]
    exact WeightConvergesEven.norm_inv_one_add_mul_I_le t
  have hA0pos : 0 ≤ C0 * B ^ k0 * D ^ l0 * J := by
    have h12 : 0 ≤ C0 * B ^ k0 := mul_nonneg (le_of_lt hC0) hBk
    have h123 : 0 ≤ C0 * B ^ k0 * D ^ l0 := mul_nonneg h12 hDl
    exact mul_nonneg h123 (le_of_lt (Real.exp_pos _))
  have hwe : ‖weightEven z u‖ ≤
      ‖Complex.Gammaℝ (z + u) / Complex.Gammaℝ z‖ * ‖cexp (u ^ 2)‖ * ‖u⁻¹‖ := by
    unfold weightEven
    rw [smoothingFunction]
    rw [div_eq_mul_inv]
    calc
      ‖Complex.Gammaℝ (z + u) / Complex.Gammaℝ z * cexp (u ^ 2) * u⁻¹‖
          = ‖Complex.Gammaℝ (z + u) / Complex.Gammaℝ z * cexp (u ^ 2)‖ * ‖u⁻¹‖ := by rw [norm_mul]
      _ ≤ (‖Complex.Gammaℝ (z + u) / Complex.Gammaℝ z‖ * ‖cexp (u ^ 2)‖) * ‖u⁻¹‖ := by rw [norm_mul]
  have hstep1 : (‖Complex.Gammaℝ (z + u) / Complex.Gammaℝ z‖ * ‖cexp (u ^ 2)‖) * ‖u⁻¹‖ ≤
      (C0 * B ^ k0 * D ^ l0 * J) * Real.exp (1 - t ^ 2) := by
    have hinner : ‖Complex.Gammaℝ (z + u) / Complex.Gammaℝ z‖ * ‖cexp (u ^ 2)‖ ≤
        (C0 * B ^ k0 * D ^ l0 * J) * Real.exp (1 - t ^ 2) := by
      exact mul_le_mul hr hc_le (norm_nonneg _) hA0pos
    calc
      (‖Complex.Gammaℝ (z + u) / Complex.Gammaℝ z‖ * ‖cexp (u ^ 2)‖) * ‖u⁻¹‖ ≤
          ((C0 * B ^ k0 * D ^ l0 * J) * Real.exp (1 - t ^ 2)) * ‖u⁻¹‖ := by
            exact mul_le_mul_of_nonneg_right hinner (norm_nonneg _)
      _ ≤ (C0 * B ^ k0 * D ^ l0 * J) * Real.exp (1 - t ^ 2) * 1 := by
            have hpos : 0 ≤ (C0 * B ^ k0 * D ^ l0 * J) * Real.exp (1 - t ^ 2) := by
              exact mul_nonneg hA0pos (le_of_lt (Real.exp_pos _))
            exact mul_le_mul_of_nonneg_left hinv hpos
      _ = (C0 * B ^ k0 * D ^ l0 * J) * Real.exp (1 - t ^ 2) := by ring
  have hJ : J * Real.exp (1 - t ^ 2) = Real.exp 1 * Real.exp ((Real.pi / 4) * |t| - t ^ 2) := by
    dsimp [J]
    rw [← Real.exp_add, ← Real.exp_add]
    ring
  have hpoly : D ^ l0 * Real.exp ((Real.pi / 4) * |t| - t ^ 2) ≤ A * G2 := by
    simpa [D, G2] using hAb t
  have htail : (C0 * B ^ k0 * D ^ l0 * J) * Real.exp (1 - t ^ 2) ≤
      (C0 * Real.exp 1 * A) * B ^ k0 * G2 := by
    have hm1 : (C0 * B ^ k0 * D ^ l0) * (J * Real.exp (1 - t ^ 2)) ≤
        (C0 * B ^ k0 * D ^ l0) * (Real.exp 1 * Real.exp ((Real.pi / 4) * |t| - t ^ 2)) := by
      exact mul_le_mul_of_nonneg_left (le_of_eq hJ) (mul_nonneg (mul_nonneg (le_of_lt hC0) hBk) hDl)
    calc
      (C0 * B ^ k0 * D ^ l0 * J) * Real.exp (1 - t ^ 2)
          = (C0 * B ^ k0 * D ^ l0) * (J * Real.exp (1 - t ^ 2)) := by ring
      _ ≤ (C0 * B ^ k0 * D ^ l0) * (Real.exp 1 * Real.exp ((Real.pi / 4) * |t| - t ^ 2)) := hm1
      _ = C0 * B ^ k0 * Real.exp 1 * (D ^ l0 * Real.exp ((Real.pi / 4) * |t| - t ^ 2)) := by ring
      _ ≤ C0 * B ^ k0 * Real.exp 1 * (A * G2) := by
            have hpos : 0 ≤ C0 * B ^ k0 * Real.exp 1 := by
              exact mul_nonneg (mul_nonneg (le_of_lt hC0) hBk) (le_of_lt (Real.exp_pos _))
            exact mul_le_mul_of_nonneg_left hpoly hpos
      _ = (C0 * Real.exp 1 * A) * B ^ k0 * G2 := by ring
  calc
    ‖weightEven z u‖
        ≤ ‖Complex.Gammaℝ (z + u) / Complex.Gammaℝ z‖ * ‖cexp (u ^ 2)‖ * ‖u⁻¹‖ := hwe
    _ ≤ (C0 * B ^ k0 * D ^ l0 * J) * Real.exp (1 - t ^ 2) := by
          exact hstep1
    _ ≤ (C0 * Real.exp 1 * A) * B ^ k0 * G2 := htail
    _ = (C0 * Real.exp 1 * A) * (1 + |T|) ^ k0 * Real.exp (-(1 / 2 : ℝ) * t ^ 2) := by
          simp [B, G2]

/-- Polynomial-in-`T` bound for the odd weight function on the vertical line. -/
lemma weightOdd_poly_vertical (a0 : ℝ) (ha0 : 0 < a0) :
    ∃ C k : ℝ, 0 < C ∧ 0 ≤ k ∧ ∀ (T t : ℝ),
      ‖weightOdd ((a0 : ℂ) + I * (T : ℂ)) (1 + I * (t : ℂ))‖ ≤
        C * (1 + |T|) ^ k * Real.exp (-(1 / 2 : ℝ) * t ^ 2) := by
  obtain ⟨C0, k0, l0, hC0, hk0, hl0, hratio⟩ := gammaℝ_ratio_poly_any (a0 + 1) (by linarith)
  obtain ⟨A, hApos, hAb⟩ := poly_gaussian_bound l0 hl0
  refine ⟨C0 * Real.exp 1 * A, k0, mul_pos (mul_pos hC0 (Real.exp_pos _)) hApos, hk0, ?_⟩
  intro T t
  let z : ℂ := (a0 : ℂ) + I * (T : ℂ)
  let u : ℂ := 1 + I * (t : ℂ)
  let B : ℝ := 1 + |T|
  let D : ℝ := 1 + |t|
  let J : ℝ := Real.exp ((Real.pi / 4) * |t|)
  let G2 : ℝ := Real.exp (-(1 / 2 : ℝ) * t ^ 2)
  have harg1 : z + 1 + u = ((a0 : ℂ) + 1) + 1 + I * ((T + t : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [z, u]
  have harg2 : ((a0 : ℂ) + 1) + 1 + I * ((T + t : ℝ) : ℂ) =
      (((a0 + 1 : ℝ) : ℂ) + 1) + I * ((T + t : ℝ) : ℂ) := by
    apply Complex.ext <;> simp
  have hr : ‖Complex.Gammaℝ (z + 1 + u) / Complex.Gammaℝ (z + 1)‖ ≤
      C0 * B ^ k0 * D ^ l0 * J := by
    rw [show z + 1 + u = (((a0 + 1 : ℝ) : ℂ) + 1) + I * ((T + t : ℝ) : ℂ) by
      calc
        z + 1 + u = ((a0 : ℂ) + 1) + 1 + I * ((T + t : ℝ) : ℂ) := by simpa [add_assoc] using harg1
        _ = (((a0 + 1 : ℝ) : ℂ) + 1) + I * ((T + t : ℝ) : ℂ) := harg2
      ]
    rw [show z + 1 = ((a0 + 1 : ℝ) : ℂ) + I * (T : ℂ) by
      apply Complex.ext <;> simp [z]]
    simpa [B, D, J] using hratio T t
  have hB0 : 0 ≤ B := by dsimp [B]; positivity
  have hD0 : 0 ≤ D := by dsimp [D]; positivity
  have hBk : 0 ≤ B ^ k0 := Real.rpow_nonneg hB0 k0
  have hDl : 0 ≤ D ^ l0 := Real.rpow_nonneg hD0 l0
  have hc_le : ‖cexp (u ^ 2)‖ ≤ Real.exp (1 - t ^ 2) := by
    dsimp [u]
    rw [WeightConvergesEven.norm_cexp_sq t]
  have hinv : ‖u⁻¹‖ ≤ 1 := by
    dsimp [u]
    exact WeightConvergesEven.norm_inv_one_add_mul_I_le t
  have hA0pos : 0 ≤ C0 * B ^ k0 * D ^ l0 * J := by
    have h12 : 0 ≤ C0 * B ^ k0 := mul_nonneg (le_of_lt hC0) hBk
    have h123 : 0 ≤ C0 * B ^ k0 * D ^ l0 := mul_nonneg h12 hDl
    exact mul_nonneg h123 (le_of_lt (Real.exp_pos _))
  have hwe : ‖weightOdd z u‖ ≤
      ‖Complex.Gammaℝ (z + 1 + u) / Complex.Gammaℝ (z + 1)‖ * ‖cexp (u ^ 2)‖ * ‖u⁻¹‖ := by
    unfold weightOdd
    rw [smoothingFunction]
    rw [div_eq_mul_inv]
    calc
      ‖Complex.Gammaℝ (z + 1 + u) / Complex.Gammaℝ (z + 1) * cexp (u ^ 2) * u⁻¹‖
          = ‖Complex.Gammaℝ (z + 1 + u) / Complex.Gammaℝ (z + 1) * cexp (u ^ 2)‖ * ‖u⁻¹‖ := by rw [norm_mul]
      _ ≤ (‖Complex.Gammaℝ (z + 1 + u) / Complex.Gammaℝ (z + 1)‖ * ‖cexp (u ^ 2)‖) * ‖u⁻¹‖ := by rw [norm_mul]
  have hstep1 : (‖Complex.Gammaℝ (z + 1 + u) / Complex.Gammaℝ (z + 1)‖ * ‖cexp (u ^ 2)‖) * ‖u⁻¹‖ ≤
      (C0 * B ^ k0 * D ^ l0 * J) * Real.exp (1 - t ^ 2) := by
    have hinner : ‖Complex.Gammaℝ (z + 1 + u) / Complex.Gammaℝ (z + 1)‖ * ‖cexp (u ^ 2)‖ ≤
        (C0 * B ^ k0 * D ^ l0 * J) * Real.exp (1 - t ^ 2) := by
      exact mul_le_mul hr hc_le (norm_nonneg _) hA0pos
    calc
      (‖Complex.Gammaℝ (z + 1 + u) / Complex.Gammaℝ (z + 1)‖ * ‖cexp (u ^ 2)‖) * ‖u⁻¹‖ ≤
          ((C0 * B ^ k0 * D ^ l0 * J) * Real.exp (1 - t ^ 2)) * ‖u⁻¹‖ := by
            exact mul_le_mul_of_nonneg_right hinner (norm_nonneg _)
      _ ≤ (C0 * B ^ k0 * D ^ l0 * J) * Real.exp (1 - t ^ 2) * 1 := by
            have hpos : 0 ≤ (C0 * B ^ k0 * D ^ l0 * J) * Real.exp (1 - t ^ 2) := by
              exact mul_nonneg hA0pos (le_of_lt (Real.exp_pos _))
            exact mul_le_mul_of_nonneg_left hinv hpos
      _ = (C0 * B ^ k0 * D ^ l0 * J) * Real.exp (1 - t ^ 2) := by ring
  have hJ : J * Real.exp (1 - t ^ 2) = Real.exp 1 * Real.exp ((Real.pi / 4) * |t| - t ^ 2) := by
    dsimp [J]
    rw [← Real.exp_add, ← Real.exp_add]
    ring
  have hpoly : D ^ l0 * Real.exp ((Real.pi / 4) * |t| - t ^ 2) ≤ A * G2 := by
    simpa [D, G2] using hAb t
  have htail : (C0 * B ^ k0 * D ^ l0 * J) * Real.exp (1 - t ^ 2) ≤
      (C0 * Real.exp 1 * A) * B ^ k0 * G2 := by
    have hm1 : (C0 * B ^ k0 * D ^ l0) * (J * Real.exp (1 - t ^ 2)) ≤
        (C0 * B ^ k0 * D ^ l0) * (Real.exp 1 * Real.exp ((Real.pi / 4) * |t| - t ^ 2)) := by
      exact mul_le_mul_of_nonneg_left (le_of_eq hJ) (mul_nonneg (mul_nonneg (le_of_lt hC0) hBk) hDl)
    calc
      (C0 * B ^ k0 * D ^ l0 * J) * Real.exp (1 - t ^ 2)
          = (C0 * B ^ k0 * D ^ l0) * (J * Real.exp (1 - t ^ 2)) := by ring
      _ ≤ (C0 * B ^ k0 * D ^ l0) * (Real.exp 1 * Real.exp ((Real.pi / 4) * |t| - t ^ 2)) := hm1
      _ = C0 * B ^ k0 * Real.exp 1 * (D ^ l0 * Real.exp ((Real.pi / 4) * |t| - t ^ 2)) := by ring
      _ ≤ C0 * B ^ k0 * Real.exp 1 * (A * G2) := by
            have hpos : 0 ≤ C0 * B ^ k0 * Real.exp 1 := by
              exact mul_nonneg (mul_nonneg (le_of_lt hC0) hBk) (le_of_lt (Real.exp_pos _))
            exact mul_le_mul_of_nonneg_left hpoly hpos
      _ = (C0 * Real.exp 1 * A) * B ^ k0 * G2 := by ring
  calc
    ‖weightOdd z u‖
        ≤ ‖Complex.Gammaℝ (z + 1 + u) / Complex.Gammaℝ (z + 1)‖ * ‖cexp (u ^ 2)‖ * ‖u⁻¹‖ := hwe
    _ ≤ (C0 * B ^ k0 * D ^ l0 * J) * Real.exp (1 - t ^ 2) := by
          exact hstep1
    _ ≤ (C0 * Real.exp 1 * A) * B ^ k0 * G2 := htail
    _ = (C0 * Real.exp 1 * A) * (1 + |T|) ^ k0 * Real.exp (-(1 / 2 : ℝ) * t ^ 2) := by
          simp [B, G2]

/-- Gaussian-weighted vertical bound implies the Mellin norm bound (used for both weights). -/
lemma mellinInv_gauss_bound {F : ℂ → ℂ} (z : ℂ) (hz : 0 < z.re)
    (hFint : Integrable (fun t : ℝ => ‖F (1 + I * (t : ℂ))‖)) {D k : ℝ} (hD : 0 < D) (hk : 0 ≤ k)
    (hpt : ∀ t : ℝ, ‖F (1 + I * (t : ℂ))‖ ≤ D * (1 + |z.im|) ^ k * Real.exp (-(1 / 2 : ℝ) * t ^ 2)) :
    ∀ {x : ℝ} (hx : 0 < x),
      ‖mellinInv 1 F x‖ ≤
        (D * (1 / (2 * Real.pi)) * (∫ t : ℝ, Real.exp (-(1 / 2 : ℝ) * t ^ 2)))
          * (1 + |z.im|) ^ k * x⁻¹ := by
  intro x hx
  have hg : Integrable (fun t : ℝ => D * (1 + |z.im|) ^ k * Real.exp (-(1 / 2 : ℝ) * t ^ 2)) := by
    have hbase : Integrable (fun t : ℝ => Real.exp (-(1 / 2 : ℝ) * t ^ 2)) := by
      exact integrable_exp_neg_mul_sq (b := (1 / 2 : ℝ)) (by norm_num)
    exact hbase.const_mul (D * (1 + |z.im|) ^ k)
  have hle : ∀ᵐ t : ℝ ∂(volume : Measure ℝ),
      ‖F (1 + I * (t : ℂ))‖ ≤ D * (1 + |z.im|) ^ k * Real.exp (-(1 / 2 : ℝ) * t ^ 2) := by
    exact ae_of_all _ hpt
  calc
    ‖mellinInv 1 F x‖
        ≤ (1 / (2 * Real.pi)) * ∫ t : ℝ, ‖(x : ℂ) ^ (-(1 + I * (t : ℂ))) * F (1 + I * (t : ℂ))‖ := by
          exact mellinInv_one_norm_le F (x := x)
    _ = (1 / (2 * Real.pi)) * ∫ t : ℝ, x⁻¹ * ‖F (1 + I * (t : ℂ))‖ := by
          congr 1
          apply MeasureTheory.integral_congr_ae
          filter_upwards with t
          rw [norm_mul, norm_cpow_neg_one_add_mul_I x hx t]
    _ = x⁻¹ * ((1 / (2 * Real.pi)) * ∫ t : ℝ, ‖F (1 + I * (t : ℂ))‖) := by
          rw [MeasureTheory.integral_const_mul]
          ring
    _ ≤ x⁻¹ * ((1 / (2 * Real.pi)) * ∫ t : ℝ, D * (1 + |z.im|) ^ k * Real.exp (-(1 / 2 : ℝ) * t ^ 2)) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (integral_mono_ae hFint hg hle) (by positivity))
            (inv_nonneg.mpr (le_of_lt hx))
    _ = x⁻¹ * (D * (1 + |z.im|) ^ k * (1 / (2 * Real.pi))
          * (∫ t : ℝ, Real.exp (-(1 / 2 : ℝ) * t ^ 2))) := by
          congr 1
          rw [MeasureTheory.integral_const_mul]
          ring
    _ = (D * (1 / (2 * Real.pi)) * (∫ t : ℝ, Real.exp (-(1 / 2 : ℝ) * t ^ 2)))
          * (1 + |z.im|) ^ k * x⁻¹ := by ring

/-- Polynomial-in-`T` bound for the even weight: for fixed `0 < a0` there are `C > 0, k ≥ 0`
with `‖mellinInv 1 (weightEven (a0 + I·T)) x‖ ≤ C·(1+|T|)^k·x⁻¹` for all `x > 0`, `T ∈ ℝ`. -/
theorem weightEven_mellin_norm_poly (a0 : ℝ) (ha0 : 0 < a0) :
    ∃ C k : ℝ, 0 < C ∧ 0 ≤ k ∧ ∀ (T : ℝ) {x : ℝ} (hx : 0 < x),
      ‖mellinInv 1 (weightEven ((a0 : ℂ) + I * (T : ℂ))) x‖ ≤ C * (1 + |T|) ^ k * x⁻¹ := by
  obtain ⟨Cw, k0, hCw, hk0, hpt⟩ := weightEven_poly_vertical a0 ha0
  have hGpos : 0 < ∫ t : ℝ, Real.exp (-(1 / 2 : ℝ) * t ^ 2) := by
    rw [integral_gaussian]
    positivity
  refine ⟨Cw * (1 / (2 * Real.pi)) * (∫ t : ℝ, Real.exp (-(1 / 2 : ℝ) * t ^ 2)), k0, by positivity, hk0, ?_⟩
  intro T x hx
  let z : ℂ := (a0 : ℂ) + I * (T : ℂ)
  have hz : 0 < z.re := by dsimp [z]; simp [ha0]
  have hptz : ∀ t : ℝ, ‖weightEven z (1 + I * (t : ℂ))‖ ≤
      Cw * (1 + |z.im|) ^ k0 * Real.exp (-(1 / 2 : ℝ) * t ^ 2) := by
    intro t
    have h := hpt T t
    simpa [z] using h
  have hb := mellinInv_gauss_bound (F := weightEven z) z hz
    (weightEven_vertical_abs_integrable z hz) hCw hk0 hptz hx
  simpa [z] using hb

/-- Polynomial-in-`T` bound for the odd weight: for fixed `0 < a0` there are `C > 0, k ≥ 0`
with `‖mellinInv 1 (weightOdd (a0 + I·T)) x‖ ≤ C·(1+|T|)^k·x⁻¹` for all `x > 0`, `T ∈ ℝ`. -/
theorem weightOdd_mellin_norm_poly (a0 : ℝ) (ha0 : 0 < a0) :
    ∃ C k : ℝ, 0 < C ∧ 0 ≤ k ∧ ∀ (T : ℝ) {x : ℝ} (hx : 0 < x),
      ‖mellinInv 1 (weightOdd ((a0 : ℂ) + I * (T : ℂ))) x‖ ≤ C * (1 + |T|) ^ k * x⁻¹ := by
  obtain ⟨Cw, k0, hCw, hk0, hpt⟩ := weightOdd_poly_vertical a0 ha0
  have hGpos : 0 < ∫ t : ℝ, Real.exp (-(1 / 2 : ℝ) * t ^ 2) := by
    rw [integral_gaussian]
    positivity
  refine ⟨Cw * (1 / (2 * Real.pi)) * (∫ t : ℝ, Real.exp (-(1 / 2 : ℝ) * t ^ 2)), k0, by positivity, hk0, ?_⟩
  intro T x hx
  let z : ℂ := (a0 : ℂ) + I * (T : ℂ)
  have hz : 0 < z.re := by dsimp [z]; simp [ha0]
  have hptz : ∀ t : ℝ, ‖weightOdd z (1 + I * (t : ℂ))‖ ≤
      Cw * (1 + |z.im|) ^ k0 * Real.exp (-(1 / 2 : ℝ) * t ^ 2) := by
    intro t
    have h := hpt T t
    simpa [z] using h
  have hb := mellinInv_gauss_bound (F := weightOdd z) z hz
    (weightOdd_vertical_abs_integrable z hz) hCw hk0 hptz hx
  simpa [z] using hb

end PL.WeightPoly


/-!
# Polynomial growth of the L-function on vertical lines (roadmap item [4])

**STATUS: machine-verified, no sorries.** The theorems `LFunction_critical_poly`
(`|L(1/2+iT,χ)| ≤ C·(1+|T|)^k·√N`) and `LFunction_strip_poly`
(`|L(σ+iT,χ)| ≤ C·(1+|T|)^k·N^(max σ (1-σ))` for `0<σ<1`) are proved. The
`q^{1/2}`-type growth in the conductor is the *trivial* AFE bound; the
subconvexity (Weyl) layer must upgrade it to `q^{1/6+ε}(1+|t|)^{1/6+ε}`.

With the exact smooth approximate functional equation
(`PL.AFE.approx_functional_equation`), the *polynomial-in-|Im z| weight bounds*
(`Submission/WeightPoly.lean`), and the *polynomial gamma-ratio bounds*
(`Submission/GammaℝRatio.lean`), one obtains **polynomial growth of the Dirichlet
L-function on the critical line**:

`|L(1/2 + I T, χ)| ≤ C · (1 + |T|)^k · q^{1/2 + ε}`

for a primitive `χ` of conductor `q` (here `N`), with `C, k` depending only on `ε`.

(The `q^{1/2}` is the size of the conductor-normalized sums; sharper bounds in `q`
are the subconvex layer built on top.)

## Strategy

1. `norm_rootNumber_le_one`: for a *primitive* character, `‖rootNumber χ‖ = 1`
   (classical: `|ε(χ)| = 1`).  We only need the upper bound `≤ 1`, and only up to an
   absolute constant, so it may be obtained either from the Gauss-sum identity or
   (falling back) from the functional equation at a point where both completed values
   are known nonzero; here we use the Gauss-sum formula
   (`gaussSum_mul_gaussSum_eq_card` with `stdAddChar` primitive, `N = q`).

2. `main_sum_poly_bound`:  for `0 < σ`, `|Σₙ χ(n)·n^{-s}·W_s(n/√N)| ≤ C(1+|T|)^k·√N·ζ(1+σ)`.
   This follows by applying the triangle inequality, the character bound `‖χ n‖ ≤ 1`,
   the polynomial weight bound `‖W_z(x)‖ ≤ C(1+|Im z|)^k·x⁻¹`
   (`PL.WeightPoly.weightEven_mellin_norm_poly` / `.weightOdd_mellin_norm_poly`
   via the parity expansion `afeWeight_even` / `afeWeight_odd`), and the convergence of
   `Σₙ n^{-(1+σ)}`.

3. `LFunction_critical_poly`: combine the AFE identity with the bounds for the main sum
   (at `s = 1/2 + I T`) and the dual sum (at `1 - s`, real part `1/2`), the bound
   `|γ(1-s)/γ(s)| ≤ C(1+|T|)^{3/2 - σ}` (`PL.GammaℝPoly.gammaFactor_ratio_poly`),
   and `‖rootNumber‖ ≤ 1`, `‖N^{1/2-s}‖ = N^{1/2-σ}` (`Complex.norm_cpow_eq_rpow_re_of_pos`).
-/

open Complex DirichletCharacter Filter MeasureTheory Set
open PL.AFE
open scoped Real BigOperators
set_option autoImplicit false

namespace PL.LGrowth

variable {N : ℕ} [NeZero N]

/-- **Polynomial weight bound for `afeWeight` directly** (both parities): for fixed
`0 < σ` there are `C > 0, k ≥ 0` with
`‖afeWeight χ (σ + I T) x‖ ≤ C · (1+|T|)^k · x⁻¹` for all `x > 0`, `T ∈ ℝ`. -/
theorem afeWeight_norm_poly (χ : DirichletCharacter ℂ N) {σ : ℝ} (hσ0 : 0 < σ) :
    ∃ C k : ℝ, 0 < C ∧ 0 ≤ k ∧ ∀ (T : ℝ) {x : ℝ} (hx : 0 < x),
      ‖afeWeight χ ((σ : ℂ) + I * (T : ℂ)) x‖ ≤ C * (1 + |T|) ^ k * x⁻¹ := by
  rcases χ.even_or_odd with hχe | hχo
  · obtain ⟨C, k, hC, hk, hb⟩ := PL.WeightPoly.weightEven_mellin_norm_poly σ hσ0
    refine ⟨C, k, hC, hk, ?_⟩
    intro T x hx
    simpa [afeWeight_even χ hχe ((σ : ℂ) + I * (T : ℂ)) x] using hb T hx
  · obtain ⟨C, k, hC, hk, hb⟩ := PL.WeightPoly.weightOdd_mellin_norm_poly σ hσ0
    refine ⟨C, k, hC, hk, ?_⟩
    intro T x hx
    simpa [afeWeight_odd χ hχo ((σ : ℂ) + I * (T : ℂ)) x] using hb T hx

/-- **Polynomial bound for a smoothed character sum with arbitrary bounded coefficients**
`g`: for `0 < σ`, `‖Σₙ g(n)·n⁻ˢ·W_s(n/√N)‖ ≤ C·(1+|T|)^k·√N` where `s = σ + I T`
and `W` is the weight of `χ`.  This is the engine behind both the main and the dual
term of the approximate functional equation. -/
theorem sum_g_poly_bound (χ : DirichletCharacter ℂ N) (g : ℕ → ℂ)
    (hg : ∀ n : ℕ, ‖g n‖ ≤ 1) {σ : ℝ} (hσ0 : 0 < σ) :
    ∃ C k : ℝ, 0 < C ∧ 0 ≤ k ∧ ∀ (T : ℝ),
      ‖∑' n : ℕ, g n * (n : ℂ) ^ (-((σ : ℂ) + I * (T : ℂ))) *
          afeWeight χ ((σ : ℂ) + I * (T : ℂ)) (afeScale N n)‖ ≤
        C * (1 + |T|) ^ k * Real.sqrt (N : ℝ) := by
  obtain ⟨Cw, kw, hCw, hkw, hw⟩ := afeWeight_norm_poly χ hσ0
  let ζ : ℝ := ∑' m : ℕ, (((m + 1 : ℕ) : ℝ) ^ (-(1 + σ)))
  have hζ_nonneg : 0 ≤ ζ := by
    dsimp [ζ]
    exact tsum_nonneg (fun m => Real.rpow_nonneg (by positivity : 0 ≤ ((m + 1 : ℕ) : ℝ)) _)
  have hZsum : Summable (fun m : ℕ => (((m + 1 : ℕ) : ℝ) ^ (-(1 + σ)))) := by
    have hbase : Summable (fun n : ℕ => (n : ℝ) ^ (-(1 + σ))) := by
      exact Real.summable_nat_rpow.mpr (by linarith)
    exact (summable_nat_add_iff 1).2 hbase
  refine ⟨Cw * (ζ + 1), kw, mul_pos hCw (by positivity), hkw, ?_⟩
  intro T
  let s : ℂ := (σ : ℂ) + I * (T : ℂ)
  have hs_re : s.re = σ := by dsimp [s]; simp
  have hs0 : 0 < s.re := by rw [hs_re]; exact hσ0
  let term : ℕ → ℂ := fun n => g n * (n : ℂ) ^ (-s) * afeWeight χ s (afeScale N n)
  have hpos (m : ℕ) : 0 < afeScale N (m + 1) := by
    dsimp [afeScale]
    exact div_pos (by exact_mod_cast (Nat.succ_pos m))
      (Real.sqrt_pos.2 (by exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne N))))
  have hterm_m (m : ℕ) :
      ‖term (m + 1)‖ ≤ Cw * (1 + |T|) ^ kw * Real.sqrt (N : ℝ) *
        (((m + 1 : ℕ) : ℝ) ^ (-(1 + σ))) := by
    have hn0 : (m + 1 : ℕ) ≠ 0 := by omega
    have hn2 : ‖((m + 1 : ℕ) : ℂ) ^ (-s)‖ = ((m + 1 : ℕ) : ℝ) ^ (-σ) := by
      simpa [s] using (norm_nat_cpow_neg (m + 1) hn0 s)
    calc
      ‖term (m + 1)‖
          = ‖g (m + 1)‖ * ‖((m + 1 : ℕ) : ℂ) ^ (-s)‖ *
              ‖afeWeight χ s (afeScale N (m + 1))‖ := by
            dsimp [term]
            simp [mul_assoc]
      _ = ‖g (m + 1)‖ * (((m + 1 : ℕ) : ℝ) ^ (-σ)) *
              ‖afeWeight χ s (afeScale N (m + 1))‖ := by rw [hn2]
      _ ≤ 1 * (((m + 1 : ℕ) : ℝ) ^ (-σ)) *
              (Cw * (1 + |T|) ^ kw * (afeScale N (m + 1))⁻¹) := by
            gcongr
            · exact hg (m + 1)
            · exact hw T (hpos m)
      _ = Cw * (1 + |T|) ^ kw * ((((m + 1 : ℕ) : ℝ) ^ (-σ)) * (afeScale N (m + 1))⁻¹) := by ring
      _ = Cw * (1 + |T|) ^ kw * (Real.sqrt (N : ℝ) * (((m + 1 : ℕ) : ℝ) ^ (-(1 + σ)))) := by
            rw [scale_pow_inv σ m (NeZero.ne N)]
      _ = Cw * (1 + |T|) ^ kw * Real.sqrt (N : ℝ) * (((m + 1 : ℕ) : ℝ) ^ (-(1 + σ))) := by ring
  have hNtail : Summable (fun m : ℕ => ‖term (m + 1)‖) := by
    refine Summable.of_nonneg_of_le (fun m => norm_nonneg _) ?_
      (Summable.mul_left (Cw * (1 + |T|) ^ kw * Real.sqrt (N : ℝ)) hZsum)
    intro m
    exact hterm_m m
  have hnormsum : Summable (fun n : ℕ => ‖term n‖) :=
    (summable_nat_add_iff 1).1 hNtail
  have hterm0 : term 0 = 0 := by
    dsimp [term]
    have hsne : -s ≠ 0 := by
      intro h
      have : s = 0 := neg_eq_zero.mp h
      rw [this] at hs0
      simp at hs0
    simp [Complex.zero_cpow hsne]
  have hsum_eq : (∑' n : ℕ, ‖term n‖) = ∑' m : ℕ, ‖term (m + 1)‖ := by
    have hsplit := Summable.sum_add_tsum_nat_add (f := fun n : ℕ => ‖term n‖) 1 hnormsum
    calc
      ∑' n : ℕ, ‖term n‖ = (∑ i ∈ Finset.range 1, ‖term i‖) + ∑' i : ℕ, ‖term (i + 1)‖ := by
        rw [← hsplit]
      _ = ∑' m : ℕ, ‖term (m + 1)‖ := by
        have hfin : (∑ i ∈ Finset.range 1, ‖term i‖) = 0 := by
          simp [hterm0]
        rw [hfin, zero_add]
  have hc_nonneg : 0 ≤ Cw * (1 + |T|) ^ kw * Real.sqrt (N : ℝ) := by
    have h1 : 0 ≤ (1 + |T|) ^ kw := Real.rpow_nonneg (by positivity) kw
    positivity
  calc
    ‖∑' n : ℕ, term n‖ ≤ ∑' n : ℕ, ‖term n‖ := norm_tsum_le_tsum_norm hnormsum
    _ = ∑' m : ℕ, ‖term (m + 1)‖ := hsum_eq
    _ ≤ ∑' m : ℕ, Cw * (1 + |T|) ^ kw * Real.sqrt (N : ℝ) *
          (((m + 1 : ℕ) : ℝ) ^ (-(1 + σ))) := by
          exact hNtail.tsum_le_tsum hterm_m
            (Summable.mul_left (Cw * (1 + |T|) ^ kw * Real.sqrt (N : ℝ)) hZsum)
    _ = (Cw * (1 + |T|) ^ kw * Real.sqrt (N : ℝ)) * ζ := by
          dsimp [ζ]
          rw [tsum_mul_left]
    _ ≤ (Cw * (1 + |T|) ^ kw * Real.sqrt (N : ℝ)) * (ζ + 1) := by
          exact mul_le_mul_of_nonneg_left (by linarith) hc_nonneg
    _ = (Cw * (ζ + 1)) * (1 + |T|) ^ kw * Real.sqrt (N : ℝ) := by ring

theorem afeMain_norm_poly (χ : DirichletCharacter ℂ N) {σ : ℝ} (hσ0 : 0 < σ)
    (hσ1 : σ < 1) :
    ∃ C k : ℝ, 0 < C ∧ 0 ≤ k ∧ ∀ (T : ℝ),
      ‖∑' n : ℕ, χ n * (n : ℂ) ^ (-((σ : ℂ) + I * (T : ℂ))) *
          afeWeight χ ((σ : ℂ) + I * (T : ℂ)) (afeScale N n)‖ ≤
        C * (1 + |T|) ^ k * Real.sqrt (N : ℝ) := by
  simpa using (sum_g_poly_bound χ (fun n : ℕ => χ n)
    (fun n => norm_char_nat_le_one χ n) hσ0)

/-- **Polynomial bound for the dual smoothed sum** (weight of `χ` at `1 - s`,
coefficients of `χ⁻¹`), used on the second line of the approximate functional equation. -/
theorem dual_poly_bound (χ : DirichletCharacter ℂ N) (hσ0 : 0 < (1 / 2 : ℝ)) :
    ∃ C k : ℝ, 0 < C ∧ 0 ≤ k ∧ ∀ (T : ℝ),
      ‖∑' n : ℕ, (χ⁻¹) n * (n : ℂ) ^ (-(1 - ((1 / 2 : ℂ) + I * (T : ℂ)))) *
          afeWeight χ (1 - ((1 / 2 : ℂ) + I * (T : ℂ))) (afeScale N n)‖ ≤
        C * (1 + |T|) ^ k * Real.sqrt (N : ℝ) := by
  obtain ⟨C, k, hC, hk, hb⟩ := sum_g_poly_bound χ (fun n : ℕ => (χ⁻¹) n)
    (fun n => norm_char_nat_le_one (χ⁻¹) n) (σ := (1 / 2 : ℝ)) hσ0
  refine ⟨C, k, hC, hk, ?_⟩
  intro T
  have hz : 1 - ((1 / 2 : ℂ) + I * (T : ℂ)) =
      ((1 / 2 : ℝ) : ℂ) + I * ((-T : ℝ) : ℂ) := by
    apply Complex.ext <;> simp <;> ring
  calc
    ‖∑' n : ℕ, (χ⁻¹) n * (n : ℂ) ^ (-(1 - ((1 / 2 : ℂ) + I * (T : ℂ)))) *
          afeWeight χ (1 - ((1 / 2 : ℂ) + I * (T : ℂ))) (afeScale N n)‖
        = ‖∑' n : ℕ, (χ⁻¹) n * (n : ℂ) ^ (-(((1 / 2 : ℝ) : ℂ) + I * ((-T : ℝ) : ℂ))) *
            afeWeight χ (((1 / 2 : ℝ) : ℂ) + I * ((-T : ℝ) : ℂ)) (afeScale N n)‖ := by
          congr 1
          apply tsum_congr
          intro n
          rw [hz]
    _ ≤ C * (1 + |T|) ^ k * Real.sqrt (N : ℝ) := by
          simpa [abs_neg] using hb (-T)

/-- **Polynomial growth on the critical line**: for a primitive non-trivial character `χ`
of conductor `N` there are `C > 0, k ≥ 0` with
`|L(1/2 + I T, χ)| ≤ C · (1+|T|)^k · √N` for all real `T`. -/
theorem LFunction_critical_poly_aux (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive)
    (hχne : χ ≠ 1) :
    ∃ C k : ℝ, 0 < C ∧ 0 ≤ k ∧ ∀ T : ℝ,
      ‖DirichletCharacter.LFunction χ (1 / 2 + I * (T : ℂ))‖ ≤ C * (1 + |T|) ^ k * Real.sqrt (N : ℝ) := by
  have hσ0 : 0 < (1 / 2 : ℝ) := by norm_num
  have hσ1 : (1 / 2 : ℝ) < 1 := by norm_num
  obtain ⟨C1, k1, hC1, hk1, hmain⟩ := afeMain_norm_poly χ hσ0 hσ1
  obtain ⟨C2, k2, hC2, hk2, hdual⟩ := dual_poly_bound χ hσ0
  obtain ⟨Cγ, hCγ, hγ⟩ := PL.GammaℝPoly.gammaFactor_ratio_poly χ hσ0 hσ1
  refine ⟨C1 + Cγ * C2, max k1 (1 + k2), ?_, ?_, ?_⟩
  · have h12 : 0 < Cγ * C2 := mul_pos hCγ hC2
    linarith
  · exact le_trans (by linarith) (le_max_right k1 (1 + k2))
  · intro T
    let s : ℂ := (1 / 2 : ℂ) + I * (T : ℂ)
    let b : ℝ := 1 + |T|
    let K : ℝ := max k1 (1 + k2)
    have hbge1 : 1 ≤ b := by dsimp [b]; linarith [abs_nonneg T]
    have hbpos : 0 < b := by dsimp [b]; positivity
    have hb1 : b ^ k1 ≤ b ^ K := Real.rpow_le_rpow_of_exponent_le hbge1 (le_max_left k1 (1 + k2))
    have hb2 : b ^ (1 + k2) ≤ b ^ K := Real.rpow_le_rpow_of_exponent_le hbge1 (le_max_right k1 (1 + k2))
    have hs0 : 0 < s.re := by
      dsimp [s]
      norm_num [Complex.add_re]
    have hs1 : s.re < 1 := by
      dsimp [s]
      norm_num [Complex.add_re]
    have hz0 : s = ((1 / 2 : ℝ) : ℂ) + I * (T : ℂ) := by
      dsimp [s]
      norm_num
    -- main term bound, rewritten to `s`
    have hmainS : ‖∑' n : ℕ, χ n * (n : ℂ) ^ (-s) *
          afeWeight χ s (afeScale N n)‖ ≤ C1 * b ^ k1 * Real.sqrt (N : ℝ) := by
      have h0 := hmain T
      rw [← hz0] at h0
      simpa [b] using h0
    -- gamma-ratio bound, rewritten to `s`
    have hgamma0 := hγ T
    rw [← hz0] at hgamma0
    have hgamma : ‖χ.gammaFactor (1 - s) / χ.gammaFactor s‖ ≤ Cγ * b := by
      have hE : ((3 / 2 : ℝ) - (2⁻¹ : ℝ)) = 1 := by norm_num
      simpa [b, hE] using hgamma0
    -- dual sum bound
    have hdualS : ‖∑' n : ℕ, (χ⁻¹) n * (n : ℂ) ^ (-(1 - s)) *
          afeWeight χ (1 - s) (afeScale N n)‖ ≤ C2 * b ^ k2 * Real.sqrt (N : ℝ) := by
      have h0 := hdual T
      simpa [s, b] using h0
    have hRN : ‖χ.rootNumber‖ ≤ 1 := (norm_rootNumber_of_isPrimitive χ hχ).le
    have hpw : ‖(N : ℂ) ^ (1 / 2 - s)‖ = 1 := by
      rw [← Complex.ofReal_natCast]
      rw [Complex.norm_cpow_eq_rpow_re_of_pos]
      · have hre : ((1 / 2 : ℂ) - s).re = 0 := by dsimp [s]; simp
        rw [hre, Real.rpow_zero]
      · exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne N))
    let dual : ℂ := ∑' n : ℕ, (χ⁻¹) n * (n : ℂ) ^ (-(1 - s)) *
        afeWeight χ (1 - s) (afeScale N n)
    let D2 : ℝ := C2 * b ^ k2 * Real.sqrt (N : ℝ)
    have hD2ge0 : 0 ≤ D2 := by
      dsimp [D2]
      have hb2 : 0 ≤ b ^ k2 := Real.rpow_nonneg (le_of_lt hbpos) k2
      have hsqrt : 0 ≤ Real.sqrt (N : ℝ) := Real.sqrt_nonneg _
      positivity
    have hdual' : ‖dual‖ ≤ D2 := by simpa [D2, dual] using hdualS
    have hCγb : 0 ≤ Cγ * b := by positivity
    have hbadd : b * b ^ k2 = b ^ (1 + k2) := by
      calc
        b * b ^ k2 = b ^ 1 * b ^ k2 := by rw [Real.rpow_one]
        _ = b ^ (1 + k2) := (Real.rpow_add hbpos 1 k2).symm
    have hrest : ‖χ.rootNumber * (N : ℂ) ^ (1 / 2 - s) *
        (χ.gammaFactor (1 - s) / χ.gammaFactor s) * dual‖ ≤
        (Cγ * C2) * b ^ (1 + k2) * Real.sqrt (N : ℝ) := by
      calc
        ‖χ.rootNumber * (N : ℂ) ^ (1 / 2 - s) *
            (χ.gammaFactor (1 - s) / χ.gammaFactor s) * dual‖
            = ‖χ.rootNumber‖ * ‖(N : ℂ) ^ (1 / 2 - s)‖ *
                ‖χ.gammaFactor (1 - s) / χ.gammaFactor s‖ * ‖dual‖ := by
              simp
        _ = ‖χ.rootNumber‖ * ‖χ.gammaFactor (1 - s) / χ.gammaFactor s‖ * ‖dual‖ := by
              rw [hpw]
              ring
        _ = ‖χ.rootNumber‖ * (‖χ.gammaFactor (1 - s) / χ.gammaFactor s‖ * ‖dual‖) := by ring
        _ ≤ ‖χ.rootNumber‖ * ((Cγ * b) * D2) := by
              exact mul_le_mul_of_nonneg_left
                (mul_le_mul hgamma hdual' (norm_nonneg _) hCγb) (norm_nonneg _)
        _ ≤ 1 * ((Cγ * b) * D2) := by
              exact mul_le_mul_of_nonneg_right hRN (mul_nonneg hCγb hD2ge0)
        _ = (Cγ * C2) * (b * b ^ k2) * Real.sqrt (N : ℝ) := by
              dsimp [D2]
              ring
        _ = (Cγ * C2) * b ^ (1 + k2) * Real.sqrt (N : ℝ) := by rw [hbadd]
    have hafeq := PL.AFE.approx_functional_equation χ hχ hχne (s := s) hs0 hs1
    have hmainK : C1 * b ^ k1 * Real.sqrt (N : ℝ) ≤ C1 * b ^ K * Real.sqrt (N : ℝ) := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb1 (le_of_lt hC1))
        (Real.sqrt_nonneg _)
    have hnorm_main : ‖∑' n : ℕ, χ n * (n : ℂ) ^ (-s) *
        afeWeight χ s (afeScale N n)‖ ≤ C1 * b ^ K * Real.sqrt (N : ℝ) :=
      hmainS.trans hmainK
    have hnorm_rest : (Cγ * C2) * b ^ (1 + k2) * Real.sqrt (N : ℝ) ≤
        (Cγ * C2) * b ^ K * Real.sqrt (N : ℝ) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hb2 (le_of_lt (mul_pos hCγ hC2))) (Real.sqrt_nonneg _)
    have hnorm_rest' : ‖χ.rootNumber * (N : ℂ) ^ (1 / 2 - s) *
        (χ.gammaFactor (1 - s) / χ.gammaFactor s) * dual‖ ≤
        (Cγ * C2) * b ^ K * Real.sqrt (N : ℝ) := hrest.trans hnorm_rest
    have hfinal : ‖DirichletCharacter.LFunction χ s‖ ≤ (C1 + Cγ * C2) * b ^ K * Real.sqrt (N : ℝ) := by
      calc
        ‖DirichletCharacter.LFunction χ s‖
            = ‖(∑' n : ℕ, χ n * (n : ℂ) ^ (-s) * afeWeight χ s (afeScale N n)) +
                χ.rootNumber * (N : ℂ) ^ (1 / 2 - s) *
                  (χ.gammaFactor (1 - s) / χ.gammaFactor s) * dual‖ := by
              rw [hafeq]
        _ ≤ ‖∑' n : ℕ, χ n * (n : ℂ) ^ (-s) * afeWeight χ s (afeScale N n)‖ +
              ‖χ.rootNumber * (N : ℂ) ^ (1 / 2 - s) *
                (χ.gammaFactor (1 - s) / χ.gammaFactor s) * dual‖ := norm_add_le _ _
        _ ≤ C1 * b ^ K * Real.sqrt (N : ℝ) + (Cγ * C2) * b ^ K * Real.sqrt (N : ℝ) := by
              exact add_le_add hnorm_main hnorm_rest'
        _ = (C1 + Cγ * C2) * b ^ K * Real.sqrt (N : ℝ) := by ring
    simpa [s, b, K] using hfinal




/-- **Polynomial growth on a general vertical line** in the critical strip: for a primitive
non-trivial character `χ` of conductor `N` and `0 < σ < 1` there are `C > 0, k ≥ 0` with
`|L(σ + I T, χ)| ≤ C · (1+|T|)^k · N^(max σ (1-σ))` for all real `T`.
(The `N`-power comes from the functional-equation factor `|N^{1/2 - s}| = N^{1/2-σ}` on the
dual side; both `σ` and `1-σ` powers are covered by the maximum.) -/
theorem LFunction_strip_poly (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive)
    (hχne : χ ≠ 1) {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    ∃ C k : ℝ, 0 < C ∧ 0 ≤ k ∧ ∀ T : ℝ,
      ‖DirichletCharacter.LFunction χ ((σ : ℂ) + I * (T : ℂ))‖ ≤
        C * (1 + |T|) ^ k * (N : ℝ) ^ (max σ (1 - σ)) := by
  have hσ' : 0 < 1 - σ := by linarith
  obtain ⟨C1, k1, hC1, hk1, hmain⟩ := afeMain_norm_poly χ hσ0 hσ1
  obtain ⟨C2, k2, hC2, hk2, hdual0⟩ := sum_g_poly_bound χ (fun n : ℕ => (χ⁻¹) n)
    (fun n => norm_char_nat_le_one (χ⁻¹) n) (σ := 1 - σ) hσ'
  obtain ⟨Cγ, hCγ, hγ⟩ := PL.GammaℝPoly.gammaFactor_ratio_poly χ hσ0 hσ1
  let e2 : ℝ := ((3 / 2 : ℝ) - σ) + k2
  refine ⟨C1 + Cγ * C2, max k1 e2, ?_, ?_, ?_⟩
  · have h12 : 0 < Cγ * C2 := mul_pos hCγ hC2
    linarith
  · exact le_trans hk1 (le_max_left k1 e2)
  · intro T
    let s : ℂ := (σ : ℂ) + I * (T : ℂ)
    let b : ℝ := 1 + |T|
    let M : ℝ := max σ (1 - σ)
    have hbge1 : 1 ≤ b := by
      dsimp [b]
      linarith [abs_nonneg T]
    have hbpos : 0 < b := by
      dsimp [b]
      positivity
    have hNpos : (0 : ℝ) < (N : ℝ) := by
      exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne N))
    have hN1 : (1 : ℝ) ≤ (N : ℝ) := by
      exact_mod_cast (Nat.succ_le_of_lt (Nat.pos_of_ne_zero (NeZero.ne N)))
    have hs0 : 0 < s.re := by
      dsimp [s]
      simp
      exact hσ0
    have hs1 : s.re < 1 := by
      dsimp [s]
      simp
      exact hσ1
    have hMhalf : (1 / 2 : ℝ) ≤ M := by
      dsimp [M]
      by_cases hle : σ ≤ (1 / 2 : ℝ)
      · have h : (1 / 2 : ℝ) ≤ 1 - σ := by linarith
        exact le_trans h (le_max_right σ (1 - σ))
      · have h : (1 / 2 : ℝ) ≤ σ := by linarith
        exact le_trans h (le_max_left σ (1 - σ))
    have homM : (1 : ℝ) - σ ≤ M := by
      dsimp [M]
      exact le_max_right σ (1 - σ)
    have hsqrtM : Real.sqrt (N : ℝ) ≤ (N : ℝ) ^ M := by
      rw [Real.sqrt_eq_rpow]
      exact Real.rpow_le_rpow_of_exponent_le hN1 hMhalf
    have hN1mM : (N : ℝ) ^ ((1 : ℝ) - σ) ≤ (N : ℝ) ^ M :=
      Real.rpow_le_rpow_of_exponent_le hN1 homM
    have hb1 : b ^ k1 ≤ b ^ (max k1 e2) :=
      Real.rpow_le_rpow_of_exponent_le hbge1 (le_max_left k1 e2)
    have hb2 : b ^ e2 ≤ b ^ (max k1 e2) :=
      Real.rpow_le_rpow_of_exponent_le hbge1 (le_max_right k1 e2)
    -- main term
    have hmainT : ‖∑' n : ℕ, χ n * (n : ℂ) ^ (-s) *
        afeWeight χ s (afeScale N n)‖ ≤ C1 * b ^ k1 * Real.sqrt (N : ℝ) := by
      simpa [s, b] using hmain T
    -- dual sum, rewritten to `1 - s`
    have hz : 1 - s = (((1 - σ : ℝ) : ℂ) + I * ((-T : ℝ) : ℂ)) := by
      apply Complex.ext
      · dsimp [s]
        simp
      · dsimp [s]
        simp
    have hdualT : ‖∑' n : ℕ, (χ⁻¹) n * (n : ℂ) ^ (-(1 - s)) *
        afeWeight χ (1 - s) (afeScale N n)‖ ≤ C2 * b ^ k2 * Real.sqrt (N : ℝ) := by
      have h0 := hdual0 (-T)
      calc
        ‖∑' n : ℕ, (χ⁻¹) n * (n : ℂ) ^ (-(1 - s)) *
            afeWeight χ (1 - s) (afeScale N n)‖
            = ‖∑' n : ℕ, (χ⁻¹) n *
                (n : ℂ) ^ (-(((1 - σ : ℝ) : ℂ) + I * ((-T : ℝ) : ℂ))) *
                afeWeight χ (((1 - σ : ℝ) : ℂ) + I * ((-T : ℝ) : ℂ)) (afeScale N n)‖ := by
              congr 1
              apply tsum_congr
              intro n
              rw [hz]
        _ ≤ C2 * b ^ k2 * Real.sqrt (N : ℝ) := by
              simpa [b, abs_neg] using h0
    -- gamma ratio
    have hγT : ‖χ.gammaFactor (1 - s) / χ.gammaFactor s‖ ≤
        Cγ * b ^ ((3 / 2 : ℝ) - σ) := by
      simpa [s, b] using hγ T
    -- norm of N^{1/2 - s}
    have hpwN : ‖(N : ℂ) ^ (1 / 2 - s)‖ = (N : ℝ) ^ ((1 / 2 : ℝ) - σ) := by
      rw [← Complex.ofReal_natCast]
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hNpos (1 / 2 - s)]
      rw [show (((1 / 2 : ℂ) - s).re) = ((1 / 2 : ℝ) - σ) by
        dsimp [s]
        simp]
    let dual : ℂ := ∑' n : ℕ, (χ⁻¹) n * (n : ℂ) ^ (-(1 - s)) *
        afeWeight χ (1 - s) (afeScale N n)
    let D2 : ℝ := C2 * b ^ k2 * Real.sqrt (N : ℝ)
    have hdual' : ‖dual‖ ≤ D2 := by
      simpa [D2, dual] using hdualT
    have hD2ge0 : 0 ≤ D2 := by
      dsimp [D2]
      positivity
    have hRN : ‖χ.rootNumber‖ ≤ 1 := (norm_rootNumber_of_isPrimitive χ hχ).le
    -- bound on the second (dual) term of the functional equation
    have hrest : ‖χ.rootNumber * (N : ℂ) ^ (1 / 2 - s) *
        (χ.gammaFactor (1 - s) / χ.gammaFactor s) * dual‖ ≤
        (Cγ * C2) * b ^ e2 * (N : ℝ) ^ ((1 : ℝ) - σ) := by
      calc
        ‖χ.rootNumber * (N : ℂ) ^ (1 / 2 - s) *
            (χ.gammaFactor (1 - s) / χ.gammaFactor s) * dual‖
            = ‖χ.rootNumber‖ * ‖(N : ℂ) ^ (1 / 2 - s)‖ *
                ‖χ.gammaFactor (1 - s) / χ.gammaFactor s‖ * ‖dual‖ := by
              simp
        _ = ‖χ.rootNumber‖ * ((N : ℝ) ^ ((1 / 2 : ℝ) - σ)) *
                ‖χ.gammaFactor (1 - s) / χ.gammaFactor s‖ * ‖dual‖ := by
              rw [hpwN]
        _ ≤ 1 * ((N : ℝ) ^ ((1 / 2 : ℝ) - σ)) * (Cγ * b ^ ((3 / 2 : ℝ) - σ)) *
                (C2 * b ^ k2 * Real.sqrt (N : ℝ)) := by
              gcongr
        _ = (Cγ * C2) * b ^ e2 * (N : ℝ) ^ ((1 : ℝ) - σ) := by
              dsimp [e2]
              calc
                1 * ((N : ℝ) ^ ((1 / 2 : ℝ) - σ)) * (Cγ * b ^ ((3 / 2 : ℝ) - σ)) *
                    (C2 * b ^ k2 * Real.sqrt (N : ℝ))
                    = Cγ * C2 * (b ^ ((3 / 2 : ℝ) - σ) * b ^ k2) *
                        ((N : ℝ) ^ ((1 / 2 : ℝ) - σ) * Real.sqrt (N : ℝ)) := by
                      ring
                _ = Cγ * C2 * b ^ (((3 / 2 : ℝ) - σ) + k2) *
                        ((N : ℝ) ^ ((1 / 2 : ℝ) - σ) * Real.sqrt (N : ℝ)) := by
                      congr 1
                      rw [Real.rpow_add hbpos ((3 / 2 : ℝ) - σ) k2]
                _ = Cγ * C2 * b ^ (((3 / 2 : ℝ) - σ) + k2) * (N : ℝ) ^ ((1 : ℝ) - σ) := by
                      congr 1
                      rw [Real.sqrt_eq_rpow]
                      rw [← Real.rpow_add hNpos ((1 / 2 : ℝ) - σ) ((1 / 2 : ℝ))]
                      congr 1
                      ring
    -- exponent and N-power comparisons to the chosen `C, k`
    have hmainM : C1 * b ^ k1 * Real.sqrt (N : ℝ) ≤
        C1 * b ^ (max k1 e2) * (N : ℝ) ^ M := by
      calc
        C1 * b ^ k1 * Real.sqrt (N : ℝ) ≤ C1 * b ^ (max k1 e2) * Real.sqrt (N : ℝ) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hb1 (le_of_lt hC1)) (Real.sqrt_nonneg _)
        _ ≤ C1 * b ^ (max k1 e2) * (N : ℝ) ^ M := by
          exact mul_le_mul_of_nonneg_left hsqrtM
            (mul_pos hC1 (Real.rpow_pos_of_pos hbpos (max k1 e2))).le
    have hrestM : (Cγ * C2) * b ^ e2 * (N : ℝ) ^ ((1 : ℝ) - σ) ≤
        (Cγ * C2) * b ^ (max k1 e2) * (N : ℝ) ^ M := by
      calc
        (Cγ * C2) * b ^ e2 * (N : ℝ) ^ ((1 : ℝ) - σ)
            ≤ (Cγ * C2) * b ^ (max k1 e2) * (N : ℝ) ^ ((1 : ℝ) - σ) := by
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hb2 (le_of_lt (mul_pos hCγ hC2)))
                (Real.rpow_nonneg (le_of_lt hNpos) ((1 : ℝ) - σ))
        _ ≤ (Cγ * C2) * b ^ (max k1 e2) * (N : ℝ) ^ M := by
              exact mul_le_mul_of_nonneg_left hN1mM
                (mul_pos (mul_pos hCγ hC2) (Real.rpow_pos_of_pos hbpos (max k1 e2))).le
    -- combine
    have hafeq := PL.AFE.approx_functional_equation χ hχ hχne (s := s) hs0 hs1
    have hnorm_main : ‖∑' n : ℕ, χ n * (n : ℂ) ^ (-s) *
        afeWeight χ s (afeScale N n)‖ ≤ C1 * b ^ (max k1 e2) * (N : ℝ) ^ M :=
      hmainT.trans hmainM
    have hnorm_rest : ‖χ.rootNumber * (N : ℂ) ^ (1 / 2 - s) *
        (χ.gammaFactor (1 - s) / χ.gammaFactor s) * dual‖ ≤
        (Cγ * C2) * b ^ (max k1 e2) * (N : ℝ) ^ M := hrest.trans hrestM
    have hfinal : ‖DirichletCharacter.LFunction χ s‖ ≤ (C1 + Cγ * C2) * b ^ (max k1 e2) * (N : ℝ) ^ M := by
      calc
        ‖DirichletCharacter.LFunction χ s‖
            = ‖(∑' n : ℕ, χ n * (n : ℂ) ^ (-s) * afeWeight χ s (afeScale N n)) +
                χ.rootNumber * (N : ℂ) ^ (1 / 2 - s) *
                  (χ.gammaFactor (1 - s) / χ.gammaFactor s) * dual‖ := by
              rw [hafeq]
        _ ≤ ‖∑' n : ℕ, χ n * (n : ℂ) ^ (-s) * afeWeight χ s (afeScale N n)‖ +
              ‖χ.rootNumber * (N : ℂ) ^ (1 / 2 - s) *
                (χ.gammaFactor (1 - s) / χ.gammaFactor s) * dual‖ := norm_add_le _ _
        _ ≤ C1 * b ^ (max k1 e2) * (N : ℝ) ^ M +
              (Cγ * C2) * b ^ (max k1 e2) * (N : ℝ) ^ M := by
              exact add_le_add hnorm_main hnorm_rest
        _ = (C1 + Cγ * C2) * b ^ (max k1 e2) * (N : ℝ) ^ M := by ring
    simpa [s, b, M, e2] using hfinal


end PL.LGrowth

namespace Commons.NumberTheory.DirichletCharacter

/-- Polynomial bound for the critical-line Dirichlet L-function of a primitive
non-trivial character of modulus `N`: for some `C > 0`, `k ≥ 0`,
`‖L(1/2 + iT, χ)‖ ≤ C · (1+|T|)^k · √N` for all real `T`. -/
theorem LFunction_critical_poly {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ.IsPrimitive) (hχne : χ ≠ 1) :
    ∃ C k : ℝ, 0 < C ∧ 0 ≤ k ∧ ∀ T : ℝ,
      ‖LFunction χ (1 / 2 + Complex.I * (T : ℂ))‖ ≤ C * (1 + |T|) ^ k * Real.sqrt (N : ℝ) := by
  exact PL.LGrowth.LFunction_critical_poly_aux χ hχ hχne

end Commons.NumberTheory.DirichletCharacter