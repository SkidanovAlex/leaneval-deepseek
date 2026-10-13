/-
Copyright: work module for the Elgindi finite-time singularity project.

# The weighted function spaces `H^k` and `W^{l,∞}`

This file sets up the basic vocabulary for the function spaces used in
T. M. Elgindi, *Finite-time singularity formation for `C^{1,α}` solutions to the
incompressible Euler equations on `ℝ³`*, Annals of Math. 194 (3) 2021.

See §Notation (lines 183–221) and §H2 (lines 1040–1315) of
`Papers/elgindi/Classical_Euler_arXiv_2.tex`.

A function of the self-similar variables `(z,θ)` is represented as a curried
function `f : ℝ → ℝ → ℝ` (so `f z θ` is the value at `(z,θ)`), and all
integrations are over the domain `[0,∞) × [0,π/2]` with the measure `dz dθ`
(**not** `r dr dθ`), as required by the Warning in §Notation of the paper.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Spaces

set_option autoImplicit false

/-! ## The domain and the fundamental parameters -/

/-- The half-line `[0,∞)` of the self-similar radial variable `z`. -/
def Iz : Set ℝ := Set.Ici 0

/-- The angular interval `[0,π/2]`. -/
def Iθ : Set ℝ := Set.Icc 0 (π/2)

/-- The domain `[0,∞) × [0,π/2]` of the self-similar variables `(z,θ)`. -/
def Dom : Set (ℝ × ℝ) := Iz ×ˢ Iθ

/-- The exponent `η = 99/100` of the paper. -/
def eta : ℝ := 99/100

/-- The exponent `γ = 1 + α/10` of the paper. -/
def gam (α : ℝ) : ℝ := 1 + α / 10

/-! ## Weights and angular data -/

/-- The radial weight `w(z) = (1+z)²/z²`.  (At `z = 0` Lean's totalised division
gives the value `0`, which is irrelevant since `{0}` is a null set.) -/
def w (z : ℝ) : ℝ := (1 + z) ^ 2 / z ^ 2

/-- The angular weight `w_θ(θ) = 1 / sin(2θ)^{γ/2}`. -/
def wTheta (α θ : ℝ) : ℝ := (Real.sin (2 * θ)) ^ (-(gam α / 2))

/-- The product weight `W = w · w_θ`. -/
def Wt (α : ℝ) (z θ : ℝ) : ℝ := w z * wTheta α θ

/-- `Γ(θ) = (sin θ · cos²θ)^{α/3}`. -/
def Gam (α θ : ℝ) : ℝ := (Real.sin θ * Real.cos θ ^ 2) ^ (α / 3)

/-- `K(θ) = 3 sin θ cos²θ`. -/
def K (θ : ℝ) : ℝ := 3 * Real.sin θ * Real.cos θ ^ 2

/-- The normalisation constant `c(α) = ∫₀^{π/2} Γ(θ) K(θ) dθ` of the paper.
The paper always uses it in the range `1/10 ≤ c ≤ 10`; this is proved in
`Work.Spaces.Weights.c_bounds` for `0 < α ≤ 1`. -/
def c (α : ℝ) : ℝ := ∫ θ in Iθ, Gam α θ * K θ

/-! ## The differential operators `D_z`, `D_θ` (and their plain counterparts) -/

/-- The plain partial derivative `∂_z f`. -/
def pz (f : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ => deriv (fun z' => f z' θ) z

/-- The plain partial derivative `∂_θ f`. -/
def pth (f : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ => deriv (fun θ' => f z θ') θ

/-- The operator `D_z f = z ∂_z f`. -/
def Dz (f : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ => z * pz f z θ

/-- The operator `D_θ f = sin(2θ) ∂_θ f`. -/
def Dth (f : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ => Real.sin (2 * θ) * pth f z θ

/-- Iterated `∂_z`. -/
def pzIter : ℕ → (ℝ → ℝ → ℝ) → (ℝ → ℝ → ℝ)
  | 0, f => f
  | n + 1, f => pz (pzIter n f)

/-- Iterated `∂_θ`. -/
def pthIter : ℕ → (ℝ → ℝ → ℝ) → (ℝ → ℝ → ℝ)
  | 0, f => f
  | n + 1, f => pth (pthIter n f)

/-- Iterated `D_z`. -/
def DzIter : ℕ → (ℝ → ℝ → ℝ) → (ℝ → ℝ → ℝ)
  | 0, f => f
  | n + 1, f => Dz (DzIter n f)

/-- Iterated `D_θ`. -/
def DthIter : ℕ → (ℝ → ℝ → ℝ) → (ℝ → ℝ → ℝ)
  | 0, f => f
  | n + 1, f => Dth (DthIter n f)

/-- The mixed operator `D_z^j D_θ^i f` of the paper. -/
def mixed (j i : ℕ) (f : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := DzIter j (DthIter i f)

@[simp] theorem pzIter_zero (f : ℝ → ℝ → ℝ) : pzIter 0 f = f := rfl
@[simp] theorem pzIter_succ (n : ℕ) (f : ℝ → ℝ → ℝ) : pzIter (n + 1) f = pz (pzIter n f) := rfl
@[simp] theorem pthIter_zero (f : ℝ → ℝ → ℝ) : pthIter 0 f = f := rfl
@[simp] theorem pthIter_succ (n : ℕ) (f : ℝ → ℝ → ℝ) : pthIter (n + 1) f = pth (pthIter n f) := rfl
@[simp] theorem DzIter_zero (f : ℝ → ℝ → ℝ) : DzIter 0 f = f := rfl
@[simp] theorem DzIter_succ (n : ℕ) (f : ℝ → ℝ → ℝ) : DzIter (n + 1) f = Dz (DzIter n f) := rfl
@[simp] theorem DthIter_zero (f : ℝ → ℝ → ℝ) : DthIter 0 f = f := rfl
@[simp] theorem DthIter_succ (n : ℕ) (f : ℝ → ℝ → ℝ) : DthIter (n + 1) f = Dth (DthIter n f) := rfl
@[simp] theorem mixed_zero_left (i : ℕ) (f : ℝ → ℝ → ℝ) : mixed 0 i f = DthIter i f := rfl
@[simp] theorem mixed_zero_right (j : ℕ) (f : ℝ → ℝ → ℝ) : mixed j 0 f = DzIter j f := rfl

/-! ## The squared `L²` functional, the `H^k` norm -/

/-- The squared `L²`-norm of `g` over `[0,∞) × [0,π/2]` w.r.t. `dz dθ`. -/
def L2Sq (g : ℝ → ℝ → ℝ) : ℝ := ∫ z in Iz, ∫ θ in Iθ, (g z θ) ^ 2

/-- The integrand whose (iterated) integral is the square of the `H^k` norm of `f`:
the sum of the squares of all the weighted derivatives appearing in `HkNorm` of the
paper.  Taking it as a single sum keeps the bookkeeping of the norm in one place. -/
def HkIntegrand (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) : ℝ :=
  (∑ i ∈ Finset.range (k + 1), (DzIter i f z θ * (w z / (Real.sin (2 * θ)) ^ (eta / 2))) ^ 2)
    + ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
        if 1 ≤ i ∧ i + j ≤ k then (mixed j i f z θ * Wt α z θ) ^ 2 else 0

/-- The square of the `H^k`-norm of `f`:
`|f|²_{H^k} = ∑_{i=0}^k |D_z^i f · w / sin(2θ)^{η/2}|²_{L²}
 + ∑_{0 ≤ i+j ≤ k, i ≥ 1} |D_z^j D_θ^i f · W|²_{L²}`. -/
def HkSq (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) : ℝ :=
  ∫ z in Iz, ∫ θ in Iθ, HkIntegrand α k f z θ

/-- The `H^k`-norm of the paper (the square root of `HkSq`). -/
def HkNorm (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) : ℝ := Real.sqrt (HkSq α k f)

/-- Membership in `H^k`: on the domain, all the weighted derivatives occurring in `HkSq`
give honest (integrable) iterated integrals.  Under this hypothesis `HkSq α k f` is the
sum of the squared `L²`-norms of the paper, and `HkNorm α k f` is finite.
(Only `z ∈ Iz` is required: nothing is assumed about `f` for `z < 0`.) -/
def HkMem (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) : Prop :=
  (∀ z ∈ Iz, IntegrableOn (fun θ => HkIntegrand α k f z θ) Iθ) ∧
    IntegrableOn (fun z => ∫ θ in Iθ, HkIntegrand α k f z θ) Iz

/-! ## Suprema on the domain, and the `W^{l,∞}`-norm -/

/-- The supremum of `g` over the domain `[0,∞) × [0,π/2]`. -/
def supN (g : ℝ → ℝ → ℝ) : ℝ := sSup {y : ℝ | ∃ z ∈ Iz, ∃ θ ∈ Iθ, y = g z θ}

/-- The supremum of `|g|` over the domain `[0,∞) × [0,π/2]`, i.e. the `L^∞`-norm of
`g` on the domain. -/
def supAbs (g : ℝ → ℝ → ℝ) : ℝ := sSup {y : ℝ | ∃ z ∈ Iz, ∃ θ ∈ Iθ, y = |g z θ|}

/-- `⟨|g|⟩` is bounded on the domain `[0,∞) × [0,π/2]`: the supremum `supAbs g` is then
the honest `L^∞`-norm of `g` rather than the junk value `0` attached to an unbounded set. -/
def SupFinite (g : ℝ → ℝ → ℝ) : Prop := BddAbove {y : ℝ | ∃ z ∈ Iz, ∃ θ ∈ Iθ, y = |g z θ|}

/-- The `W^{l,∞}`-norm of the paper:
`|f|_{𝒲^{l,∞}} = ∑_{0≤k≤l} |(z+1)^k ∂_z^k f|_{L∞}
 + ∑_{1≤k+j≤l, j≥1} |(z+1)^k ∂_z^k D_θ^j f · sin(2θ)^{-α/5}/(α+sin(2θ))|_{L∞}`. -/
def WlInf (α : ℝ) (l : ℕ) (f : ℝ → ℝ → ℝ) : ℝ :=
  (∑ k ∈ Finset.range (l + 1), supAbs (fun z θ => (z + 1) ^ k * pzIter k f z θ))
    + ∑ j ∈ Finset.range (l + 1), ∑ k ∈ Finset.range (l + 1),
        if 1 ≤ j ∧ k + j ≤ l then
          supAbs (fun z θ => (z + 1) ^ k * pzIter k (DthIter j f) z θ
            * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
        else 0

/-- Membership in `W^{l,∞}`: every one of the finitely many suprema occurring in
`WlInf` is that of a bounded function, so that `WlInf` is the honest sum of sup norms. -/
def WlInfMem (α : ℝ) (l : ℕ) (f : ℝ → ℝ → ℝ) : Prop :=
  (∀ k ≤ l, SupFinite (fun z θ => (z + 1) ^ k * pzIter k f z θ)) ∧
    ∀ j ≤ l, ∀ k ≤ l, 1 ≤ j → k + j ≤ l →
      SupFinite (fun z θ => (z + 1) ^ k * pzIter k (DthIter j f) z θ
        * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))

/-! ## Regularity and boundary hypotheses used by the estimates

Two smoothness classes are provided.  `SmoothNbhd` is the strongest and easiest to
use: `f` is smooth on an open set containing the closed quadrant, so all the
one-sided boundary conditions needed by the fundamental theorem of calculus are
automatic.  `SmoothInt` only requires smoothness on the open quadrant together with
smoothness in `z` down to `z = 0` at every angle; it contains the basic `W^{l,∞}`
function `Γ(θ)·z/(1+z)²`, which is *not* smooth at the angular boundary when
`α/3 ∉ ℕ`.  All Leibniz manipulations for `D_z`, `D_θ` are valid in `SmoothInt`,
because both operators carry a factor (`z` resp. `sin(2θ)`) which vanishes on the
boundary of the quadrant. -/

/-- `f` is smooth on an open neighbourhood of the closed quadrant `[0,∞) × [0,π/2]`. -/
def SmoothNbhd (f : ℝ → ℝ → ℝ) : Prop :=
  ContDiffOn ℝ ⊤ (Function.uncurry f) (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (π/2 + 1))

/-- `f` is smooth on the open strip `(-1,∞) × (0,π/2)` and, for every angle
`θ ∈ [0,π/2]`, smooth in `z` on a right-neighbourhood of `0`. -/
def SmoothInt (f : ℝ → ℝ → ℝ) : Prop :=
  ContDiffOn ℝ ⊤ (Function.uncurry f) (Set.Ioi (-1) ×ˢ Set.Ioo 0 (π/2)) ∧
    ∀ θ ∈ Iθ, ContDiffOn ℝ ⊤ (fun z => f z θ) (Set.Ioi (-1))

/-- `f` and all its iterated plain partial derivatives `∂_z^j ∂_θ^i f` with `i+j ≤ n`
tend to `0` as `z → ∞`, for each fixed angle `θ ∈ [0,π/2]`. -/
def DecayInZ (n : ℕ) (f : ℝ → ℝ → ℝ) : Prop :=
  ∀ j i : ℕ, i + j ≤ n → ∀ θ ∈ Iθ,
    Tendsto (fun z => pzIter j (pthIter i f) z θ) atTop (𝓝 0)

/-- Every mixed `D`-derivative `D_z^b D_θ^a f` with `a + b ≤ n` tends to `0` as `z → ∞`,
for every angle `θ ∈ [0,π/2]`.  This is the decay hypothesis needed by the Hardy
inequalities when they are applied to `D`-iterates of `f` (it is *not* implied by the
pointwise decay of the plain partial derivatives, since `D_z = z∂_z` carries a factor
`z`); it holds for every compactly supported function and for every function whose
partial derivatives decay at least like powers of `z`. -/
def DecayMixed (n : ℕ) (f : ℝ → ℝ → ℝ) : Prop :=
  ∀ a b : ℕ, a + b ≤ n → ∀ θ ∈ Iθ, Tendsto (fun z => mixed b a f z θ) atTop (𝓝 0)

/-- The decay hypotheses used by the product rules in `H^4` and `𝒲^{4,∞}`: all plain
partial derivatives `∂_z^j ∂_θ^i f` and all mixed `D`-derivatives `D_z^b D_θ^a f` with
`i + j ≤ n` resp. `a + b ≤ n` tend to `0` as `z → ∞`, for every angle `θ ∈ [0,π/2]`.
Compactly supported functions and functions whose derivatives decay like powers satisfy
this; it is exactly the decay needed by the Hardy inequalities of §H2. -/
def DecayAll (n : ℕ) (f : ℝ → ℝ → ℝ) : Prop := DecayInZ n f ∧ DecayMixed n f

/-- `f` vanishes identically on the two angular boundaries `θ = 0` and `θ = π/2`. -/
def VanishTheta (f : ℝ → ℝ → ℝ) : Prop := (∀ z : ℝ, f z 0 = 0) ∧ (∀ z : ℝ, f z (π / 2) = 0)

/-! ## Elementary consequences of the definitions -/

theorem eta_pos : 0 < eta := by norm_num [eta]
theorem eta_lt_one : eta < 1 := by norm_num [eta]
theorem eta_nonneg : 0 ≤ eta := le_of_lt eta_pos

theorem gam_sub_one (α : ℝ) : gam α - 1 = α / 10 := by simp [gam]
theorem one_lt_gam {α : ℝ} (hα : 0 < α) : 1 < gam α := by
  have : 0 < α / 10 := by linarith
  linarith [gam_sub_one α]
theorem gam_pos {α : ℝ} (hα : 0 < α) : 0 < gam α := by linarith [one_lt_gam hα]

theorem zero_mem_Iz : (0 : ℝ) ∈ Iz := by simp [Iz]
theorem zero_mem_Iθ : (0 : ℝ) ∈ Iθ := by
  refine ⟨le_refl 0, ?_⟩
  have := Real.pi_pos; linarith
theorem pi_half_mem_Iθ : (π / 2) ∈ Iθ := by
  refine ⟨?_, le_refl _⟩
  have := Real.pi_pos; linarith

/-- The `H^k` integrand is a sum of squares, hence nonnegative. -/
theorem HkIntegrand_nonneg (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    0 ≤ HkIntegrand α k f z θ := by
  rw [HkIntegrand]
  refine add_nonneg (Finset.sum_nonneg fun i _ => sq_nonneg _) ?_
  refine Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => ?_
  split_ifs with h
  · exact sq_nonneg _
  · exact le_refl 0

theorem HkSq_nonneg (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) : 0 ≤ HkSq α k f :=
  integral_nonneg fun z => integral_nonneg fun θ => HkIntegrand_nonneg α k f z θ

theorem HkNorm_nonneg (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) : 0 ≤ HkNorm α k f :=
  Real.sqrt_nonneg _

/-- Pointwise bound from the supremum on the domain. -/
theorem le_supN {g : ℝ → ℝ → ℝ} {z θ C : ℝ} (hz : z ∈ Iz) (hθ : θ ∈ Iθ)
    (h : ∀ z ∈ Iz, ∀ θ ∈ Iθ, g z θ ≤ C) : g z θ ≤ supN g :=
  le_csSup ⟨C, fun y hy => by rcases hy with ⟨z', hz', θ', hθ', rfl⟩; exact h z' hz' θ' hθ'⟩
    ⟨z, hz, θ, hθ, rfl⟩

theorem supN_le {g : ℝ → ℝ → ℝ} {C : ℝ} (h : ∀ z ∈ Iz, ∀ θ ∈ Iθ, g z θ ≤ C) :
    supN g ≤ C :=
  csSup_le ⟨g 0 0, 0, zero_mem_Iz, 0, zero_mem_Iθ, rfl⟩ fun y hy => by
    rcases hy with ⟨z, hz, θ, hθ, rfl⟩; exact h z hz θ hθ

theorem le_supAbs {g : ℝ → ℝ → ℝ} {z θ C : ℝ} (hz : z ∈ Iz) (hθ : θ ∈ Iθ)
    (h : ∀ z ∈ Iz, ∀ θ ∈ Iθ, |g z θ| ≤ C) : |g z θ| ≤ supAbs g :=
  le_csSup ⟨C, fun y hy => by rcases hy with ⟨z', hz', θ', hθ', rfl⟩; exact h z' hz' θ' hθ'⟩
    ⟨z, hz, θ, hθ, rfl⟩

theorem supAbs_le {g : ℝ → ℝ → ℝ} {C : ℝ} (h : ∀ z ∈ Iz, ∀ θ ∈ Iθ, |g z θ| ≤ C) :
    supAbs g ≤ C :=
  csSup_le ⟨|g 0 0|, 0, zero_mem_Iz, 0, zero_mem_Iθ, rfl⟩ fun y hy => by
    rcases hy with ⟨z, hz, θ, hθ, rfl⟩; exact h z hz θ hθ

/-- Pointwise bound from the `L^∞`-norm, assuming the latter is honest. -/
theorem abs_le_supAbs {g : ℝ → ℝ → ℝ} {z θ : ℝ} (hz : z ∈ Iz) (hθ : θ ∈ Iθ)
    (h : SupFinite g) : |g z θ| ≤ supAbs g :=
  le_csSup h ⟨z, hz, θ, hθ, rfl⟩

theorem supN_le_supAbs (g : ℝ → ℝ → ℝ) (h : SupFinite g) : supN g ≤ supAbs g := by
  refine supN_le fun z hz θ hθ => ?_
  exact le_trans (le_abs_self (g z θ)) (abs_le_supAbs hz hθ h)

end Work.Spaces
