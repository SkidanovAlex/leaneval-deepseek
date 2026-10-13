/-
# `FTS/GalFields` — the corrected Galerkin field lemmas (design `FTS_ELL_GALERKIN.md` §3)

This directory (`Submission/Work/FTS/GalFields/`, namespace `Work.FTS.GalFields`) is the chapter of
the corrected N4/N5 **compactness inputs** of the Galerkin existence theorem: the five fields
`hField_lip`, `hField_bound`, `hField_cont`, `hProfileSpace`, `hProfileTau` of
`Work.FTS.Galerkin.DynInputs` / `Work.FTS.OpenPkg.DynInputsOpen`, restated in their corrected
(provable) form.

## Why the delivered forms are false, and what is corrected here

The delivered `hField_lip`/`hField_bound` quantify the projected field
`c ↦ galField α (IP α) φ n (PsiCan Φs EllSol) τ c` on the ball

  `Metric.closedBall 0 (2R)` — the **sup-norm** ball `{c : |cₖ| ≤ 2R for all k}` of `Fin n → ℝ`.

That statement is FALSE for large `n`.  The a-priori bound controls the *energy*
`Σₖ cₖ² ≤ R²`; on the sup-norm ball the energy may reach `4nR²`, hence
`|gₙ|_{ℋ⁴} ≥ (Σcₖ²/clo)^{1/2}` can be as large as `2√n R/√clo = 2√n C₀α²`, which exceeds the
smallness threshold `α^{7/4}` of the nonlinear estimates as soon as
`n ≳ (C₀α)^{-2}`.  The two failure modes are

* the modulation constant `μ` of the projected right-hand side leaves the ball `|μ| ≤ 1/2`; and
* the *linear* coefficient `μ + λ + μλ` of `N_*` equals `-μ` for the paper's choice
  `λ = -2μ/(1+μ)`, which degenerates at `μ = -1` (where `λ` jumps from `+1` to `-1`).

The corrections are exactly those of design `FTS_ELL_GALERKIN.md` §3 and §"New defects":

* the ball is the **energy** (ℓ²) ball
  `EBall n (2R) = {c | Σₖ cₖ² ≤ (2R)²}`, which contains every Galerkin trajectory
  (`IsGalFam` gives `Σₖ cₖ² ≤ R²`) and on which `|gₙ|_{ℋ⁴} ≤ 2C₀α²` (`BallBound.lean`);
* the smallness hypothesis `α ≤ (2C₀)⁻⁴`, which turns `2C₀α² ≤ α^{7/4}` and hence puts every
  point of the ball inside the range of the nonlinear (row) estimates;
* `hField_cont` is kept but is *trivial*: `galField` does not depend on `τ`
  (`galField α (IP α) φ n (PsiCan Φs EllSol) τ c` is obtained from the profile `galFun φ c` alone,
  see `FieldBasic.lean`), so the `τ`-continuity is continuity of a constant;
* `hProfileTau` is reproved by the **tail route** (`BesselTail.lean`, `ProfileTau.lean`): the
  delivered route `Work.FTS.GalerkinFix.equicontTau_of_galFam_fieldBound` is *unsound* — it needs a
  uniform `ℋ²`-bound on `∂_τgₙ = Pₙ(galRHS)`, which the projection controls only by
  `|R|_{ℋ⁴} ≈ ℋ⁵` of `gₙ`, not uniformly in `n`.  The tail route instead uses
  (i) Bessel's inequality for the Galerkin basis (`Σⱼ φⱼ(p)² ≤ C`), whence the tails
  `T_m(p) = (Σ_{j≥m} φⱼ(p)²)^{1/2}` decrease to `0` pointwise, and Dini on boxes makes the
  convergence uniform, and (ii) the per-mode bound `|ċⱼ| ≤ Mⱼ`, uniform in `n` and `τ`, obtained by
  pairing the right-hand side against the *compactly supported* test function `φⱼ`.

## The standing hypotheses (design §3: "take `GalBasis` and linear `EllSol` as hypotheses")

Every theorem of this chapter takes

* `hIP : UnifIP IP α₂ cc clo Cup Ccs` — N2's coercive inner product (the frozen
  `Work.FTS.Nonlin.UnifIP`);
* `hφ : GalBasis α IP φ` — N6 step 2's Galerkin basis (the frozen `Work.FTS.Nonlin.GalBasis`),
  with `hCc : CcBasis φ` the compact-support refinement produced by `FTS/GalBasis`
  (`exists_galBasis`);
* `EllSol : Fn →ₗ[ℝ] Fn` — the **linear** elliptic solution operator of `FTS/EllSol`, with
  `hEll : ∀ g, GalClass α g → EllPkgGo α Ce g (EllSol g)`;
* `hStar : StarPkgo2 α Cs Φs` — the `Φ_*`-package;
* the a-priori radius `R = √clo · C₀ · α²` and the smallness `α ≤ (2C₀)⁻⁴`.

The only *analytic* input not supplied by those areas is the size/Lipschitz package of the
**dynamic right-hand side** `Fr` on the smallness ball (the structure `RHSData` below).  It is the
output of the N4 row chapter (`Work.FTS.NonlinRows`, `Work.FTS.Nonlinear.Open.n4Rows2`), which
bounds every monomial of the assembled right-hand side in the `ℋ⁴` metric; see
`Submission/Work/FTS/GalFields/README.md` for the exact shape in which it is consumed.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.Vocab
import Submission.Work.FTS.VocabO
import Submission.Work.FTS.VocabO2
import Submission.Work.FTS.GalerkinFix.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.GalFields

open Work.FTS.Nonlin (RegQ GalClass CoerAdm UnifIP GalBasis Xn PsiCan)
open Work.FTS.Galerkin (Fn Fam slice galFun galField galRHS coeffOf IsSolOn IsGalFam
  ConvLocUnif profileFam prof Slab dynLin dynRHS famOf gdot EquicontSpace EquicontTau)
open Work.FTS.VocabO (EllPkgGo)
open Work.FTS.VocabO2 (StarPkgo2)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The energy ball `EBall n r = {c | Σₖ cₖ² ≤ r²}` -/

/-- The **energy ball** of the corrected compactness inputs: the set of coefficient vectors whose
ℓ²-energy is at most `r²`.  It contains every Galerkin trajectory of the a-priori chapter
(`IsGalFam` gives `Σₖ cₖ² ≤ R²`), and it is the correct domain of the projected vector field: on it
the `ℋ⁴`-size of the profile is `≤ r/√clo`, uniformly in the truncation `n`. -/
def EBall (n : ℕ) (r : ℝ) : Set (Fin n → ℝ) := {c | ∑ k, c k ^ 2 ≤ r ^ 2}

@[simp] theorem mem_EBall {n : ℕ} {r : ℝ} {c : Fin n → ℝ} :
    c ∈ EBall n r ↔ ∑ k, c k ^ 2 ≤ r ^ 2 := Iff.rfl

theorem EBall_subset_EBall {n : ℕ} {r r' : ℝ} (hr : 0 ≤ r) (h : r ≤ r') :
    EBall n r ⊆ EBall n r' :=
  fun c hc => le_trans hc (pow_le_pow_left₀ hr h 2)

theorem zero_mem_EBall (n : ℕ) {r : ℝ} : (0 : Fin n → ℝ) ∈ EBall n r := by
  rw [mem_EBall]
  simpa using sq_nonneg r

/-- **The energy of a vector bounds each of its coordinates.**  On `EBall n r` with `r ≥ 0` the
sup-norm of `c` is at most `r`; this is what relates the corrected energy ball to the delivered
sup-norm ball (it is a *proper* subset of it). -/
theorem abs_le_of_mem_EBall {n : ℕ} {r : ℝ} (hr : 0 ≤ r) {c : Fin n → ℝ} (hc : c ∈ EBall n r)
    (k : Fin n) : |c k| ≤ r := by
  have h1 : (c k) ^ 2 ≤ ∑ j, (c j) ^ 2 :=
    Finset.single_le_sum (fun j _ => sq_nonneg (c j)) (Finset.mem_univ k)
  have h2 : (c k) ^ 2 ≤ r ^ 2 := le_trans h1 hc
  have h3 : |c k| ≤ |r| := by
    rw [← Real.sqrt_sq_eq_abs (c k), ← Real.sqrt_sq_eq_abs r]
    exact Real.sqrt_le_sqrt h2
  rwa [abs_of_nonneg hr] at h3

/-- The corrected energy ball is contained in the delivered sup-norm ball (the reverse inclusion
is false, and is the source of the defects recorded in the header). -/
theorem EBall_subset_closedBall {n : ℕ} {r : ℝ} (hr : 0 ≤ r) : EBall n r ⊆ Metric.closedBall 0 r :=
  fun c hc => by
    rw [Metric.mem_closedBall, dist_pi_le_iff hr]
    intro k
    simpa [Real.dist_eq] using abs_le_of_mem_EBall hr hc k

/-- **One coordinate is dominated by the sup-norm.** -/
theorem sq_le_norm_sq (n : ℕ) (c : Fin n → ℝ) (k : Fin n) : (c k) ^ 2 ≤ ‖c‖ ^ 2 := by
  have h1 : dist c 0 ≤ ‖c‖ := by rw [dist_eq_norm, sub_zero]
  have h2 : dist (c k) (0 : ℝ) ≤ ‖c‖ := (dist_pi_le_iff (norm_nonneg c)).mp h1 k
  rw [Real.dist_eq, sub_zero] at h2
  calc (c k) ^ 2 = |c k| ^ 2 := by rw [sq_abs]
    _ ≤ ‖c‖ ^ 2 := by
        have := mul_self_le_mul_self (abs_nonneg (c k)) h2
        simpa only [pow_two] using this

/-- The energy is bounded by the square of the sup-norm: for every vector of `Fin n → ℝ`,
`Σₖ cₖ² ≤ n · ‖c‖²`.  This is the (harmless for the corrected statements) direction in which the
two balls differ; it is the reason why `hField_lip'` below has truncation-dependent constants
`K n`. -/
theorem sum_sq_le_card_mul_norm_sq (n : ℕ) (c : Fin n → ℝ) :
    ∑ k, (c k) ^ 2 ≤ n * ‖c‖ ^ 2 := by
  calc ∑ k : Fin n, (c k) ^ 2 ≤ ∑ _k : Fin n, ‖c‖ ^ 2 :=
        Finset.sum_le_sum fun k _ => sq_le_norm_sq n c k
    _ = n * ‖c‖ ^ 2 := by simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-! ## The corrected field lemmas (statements)

These are the corrected forms of the fields of `Work.FTS.Galerkin.DynInputs`.  The statements of
`hField_lip'` (with the energy ball `EBall n (2 * R)` in place of `Metric.closedBall 0 (2 * R)`)
are the ones frozen in `Submission/Work/FTS/FTS_ELL_GALERKIN_STMTS.lean.txt`, namespace
`Work.FTS.ScratchC46`; they are copied here verbatim (modulo the namespace). -/

/-- **The corrected Lipschitz field**: the projected vector field is Lipschitz on the *energy* ball
of radius `2R`, with a truncation-dependent constant. -/
def hField_lip' (α : ℝ) (IP : ℝ → Fn → Fn → ℝ) (φ : ℕ → Fn) (Φs : Fn) (EllSol : Fn → Fn)
    (R : ℝ) (K : ℕ → ℝ) (hK : ∀ n, 0 ≤ K n) : Prop :=
  ∀ (n : ℕ) (τ : ℝ), 0 ≤ τ →
    LipschitzOnWith ⟨K n, hK n⟩ (galField α (IP α) φ n (PsiCan Φs EllSol) τ) (EBall n (2 * R))

/-- **The corrected bound field**: the projected vector field is bounded on the *energy* ball of
radius `2R`, with a truncation-dependent constant. -/
def hField_bound' (α : ℝ) (IP : ℝ → Fn → Fn → ℝ) (φ : ℕ → Fn) (Φs : Fn) (EllSol : Fn → Fn)
    (R : ℝ) (L : ℕ → ℝ) : Prop :=
  ∀ (n : ℕ) (τ : ℝ), 0 ≤ τ → ∀ c : Fin n → ℝ, c ∈ EBall n (2 * R) →
    ‖galField α (IP α) φ n (PsiCan Φs EllSol) τ c‖ ≤ L n

/-- **The fake-time continuity field**: `τ ↦ galField … τ c` is continuous on `[0,∞)` on the energy
ball.  Unlike the delivered version this is *unconditional* — the projected field does not depend on
`τ` at all (`FieldBasic.lean`), so continuity is continuity of a constant. -/
def hField_cont' (α : ℝ) (IP : ℝ → Fn → Fn → ℝ) (φ : ℕ → Fn) (Φs : Fn) (EllSol : Fn → Fn)
    (R : ℝ) : Prop :=
  ∀ (n : ℕ) (c : Fin n → ℝ), c ∈ EBall n (2 * R) →
    ContinuousOn (fun τ => galField α (IP α) φ n (PsiCan Φs EllSol) τ c) (Set.Ici 0)

/-- **Uniform spatial equicontinuity of the Galerkin profiles** (the `(z,θ)`-half of the corrected
compactness input), for every Galerkin family in the a-priori ball. -/
def hProfileSpace' (α : ℝ) (IP : ℝ → Fn → Fn → ℝ) (φ : ℕ → Fn) (Φs : Fn) (EllSol : Fn → Fn)
    (R : ℝ) : Prop :=
  ∀ c, IsGalFam α (IP α) φ (PsiCan Φs EllSol) R c → EquicontSpace (profileFam φ c)

/-- **Uniform equicontinuity in the fake time of the Galerkin profiles** (the `τ`-half of the
corrected compactness input), for every Galerkin family in the a-priori ball.  Its proof (the *tail
route*) is in `BesselTail.lean` + `ProfileTau.lean`. -/
def hProfileTau' (α : ℝ) (IP : ℝ → Fn → Fn → ℝ) (φ : ℕ → Fn) (Φs : Fn) (EllSol : Fn → Fn)
    (R : ℝ) : Prop :=
  ∀ c, IsGalFam α (IP α) φ (PsiCan Φs EllSol) R c → EquicontTau (profileFam φ c)

/-! ## The dynamic right-hand side as a function of the profile -/

/-- The **dynamic right-hand side of the projected Galerkin equation, as a function of the
profile**: with `g` the profile of the truncation and `Φs + EllSol g` its stream function,
`Fr α Φs EllSol g` is the right-hand side `-𝓛_Γ^T(g) + gRHS(μ̄,λ,F_*,Φ,g)` of the fake-time
equation.  It is the same object for every truncation `n` and every fake time `τ`
(`FieldBasic.galRHS_eq_Fr`), which is what makes the projected field `τ`-independent. -/
def Fr (α : ℝ) (Φs : Fn) (EllSol : Fn → Fn) (g : Fn) : Fn :=
  dynLin α (famOf fun _ => g) 0
    + dynRHS α (PsiCan Φs EllSol (famOf fun _ => g)) (famOf fun _ => g) 0

/-- The size `|g|_{ℋ⁵}` — the higher norm that the field bounds of this chapter consume; see
`RHSData` below for why `Xn` (order 4) is not enough. -/
abbrev Xn5 (α : ℝ) (g : Fn) : ℝ := Work.Spaces.HkNorm α 5 g

/-- **The size and Lipschitz package of the dynamic right-hand side on the smallness ball.**

This is the single analytic input of the chapter that is not supplied by `FTS/GalBasis` or
`FTS/EllSol`: `Fr` is a polynomial of degree `≤ 3` in the profile (with coefficients built from
`Γ`, `K`, `F_*`, `Φ_*` and the linear operator `EllSol`), and on the smallness ball
`{|g|_{ℋ⁴} ≤ α^{7/4}}` it is

* bounded in the `ℋ⁴` metric by a polynomial in the **`ℋ⁵`-size** of `g`, and
* Lipschitz in the `ℋ⁴` metric, with a Lipschitz constant controlled by the `ℋ⁵`-sizes,

with constants independent of `α` in the range of validity.

## Why the `ℋ⁵`-dependence is unavoidable (and the constant form `Cb` is false)

Three of the pieces of `N₀` and six of the pieces of `N` are bounded in the N4 row bundle
(`Work.FTS.NonlinRows.NData2`) only in **pairing** form `|IP (Nᵢ) g| ≤ …` — rows 4, 6, 7 of
`N0Rows` and rows 12, 14, 16, 18, 20, 22 of `NRows`
(`N04bF = (3/2α) sin 2θ L₁₂(g) ∂_θg`, `N05bF = -c₂m L₁₂(g) D_zg`, `N06F = -c₂m L₁₂(F_*) D_zg`, and
the six `Nᵢ^{g·}` pieces carrying `U(Φ̃)·∂_θF` and `V(Φ̃)·D_zF` with `F = F_* + g`).  The reason is
that those pieces contain `D_z g` or `∂_θg`, whose **`ℋ⁴`-norm is not controlled by `|g|_{ℋ⁴}`**:

  `HkSq α 4 (D_z g) ≤ HkSq α 5 g`  but **not**  `≤ C·HkSq α 4 g`,

because `HkIntegrand α 4 (D_zg)` is a sub-sum of `HkIntegrand α 5 g` (the slots `D_z^{i+1}g`,
`D_z^{j+1}D_θ^ig` with `i+j+1 ≤ 5`), so the constant `Cb` in the form
`∀ g, |g|_{ℋ⁴} ≤ α^{7/4} → |Fr g|_{ℋ⁴} ≤ Cb` is **false** for a general `GalBasis`: the ball
`{|g|_{ℋ⁴} ≤ α^{7/4}}` is not bounded in `ℋ⁵`.  (The failed constant form is exactly the same kind
of defect as the delivered `hField_lip`/`hField_bound` on the sup-norm ball, recorded in the
design's "New defects".)

The finite constant therefore has to be produced from the *basis*: for `c ∈ EBall n (2R)` one has
`|galFun φ c|_{ℋ⁵} ≤ (Σₖcₖ²)^{1/2}·(Σ_{k<n}|φ k|_{ℋ⁵}²)^{1/2}`, which is finite for every
truncation `n` and is the `M5`-hypothesis carried by `FieldBnd.hField_bound'_holds`,
`FieldLip.hField_lip'_holds` and `ProfileTau.hProfileTau'_holds`.  (For the `τ`-field the
`ℋ⁵`-bound has to be **uniform in `n`**, which is a property of the basis, not of `GalBasis` as an
abstract class; see `NOTES_RHSData.md`.)

Both clauses are stated *on the smallness ball*, which is exactly what the smallness hypothesis
`α ≤ (2C₀)⁻⁴` of the field lemmas guarantees for every `c ∈ EBall n (2R)`
(`BallBound.HkNorm_le_alpha_rpow_of_mem_EBall`).  Without that hypothesis the Lipschitz constant
degenerates in `α → 0`: the modulation constant `μ` may leave `|μ| ≤ 1/2` and the coefficient
`μ + λ + μλ = -μ` of `N_*` blows up — the defect recorded in the design under "New defects".

## The exact form of the two clauses (corrected 2026-10-09)

Both clauses are stated for profiles of the **Galerkin class** `GalClass α` (which supplies
`HkMem α 5`, the honesty needed to compare the `ℋ⁴`- and `ℋ⁵`-sizes, `L₁₂ g 0 = 0` and the
vanishing of the profile at `z = 0`), and for `α ≤ 1` (used only for `α^{7/4} ≤ α`-type
arithmetic):

  `bdd : ∃ Cb ≥ 0, ∀ g, GalClass α g → α ≤ 1 → Xn α g ≤ α^{7/4} → Xn α (Fr g) ≤ Cb(1 + Xn5 g)³`,
  `lip : ∃ Cl ≥ 0, ∀ g g', GalClass α g → GalClass α g' → GalClass α (g - g') → α ≤ 1 →
           Xn α g, Xn α g' ≤ α^{7/4} →
           Xn α (Fr g - Fr g') ≤ Cl(1 + Xn5 g + Xn5 g')² Xn5 α (g - g')`.

The right-hand side of `lip` carries the `ℋ⁵`-size of the **difference** — this is essential and
is *not* a defect: `Fr` contains the unbounded operators `D_z = z∂_z` and `D_θ`, and
`HkSq α 4 (D_z h) ≤ HkSq α 5 h` is all that is available (`Norm/Basic.lean`); an `ℋ⁴`-difference
bound `|Fr g - Fr g'|_{ℋ⁴} ≤ C|g-g'|_{ℋ⁴}` is **false** (take `g' = 0` and `g = εψ` with `ψ` a
narrow bump in `z`: the `D_z`-slot of `g - g'` is not controlled by its `ℋ⁴`-size).  In the
application both `g`, `g'` and `g - g'` are Galerkin combinations in the ball — `g = galFun φ c`,
`g' = galFun φ c'` with `c, c' ∈ EBall n (2R)`, so `g - g' = galFun φ (c - c')` — and
`Xn5 α (galFun φ (c-c')) ≤ √(n/clo)·‖c - c'‖` is what produces the truncation-dependent Lipschitz
constant `K n` of `hField_lip'`.

**The constants `Cb`, `Cl` may depend on `α` and on the fixed data `Φs`, `EllSol`** (they are
existentials inside `RHSData α Φs EllSol`, which is instantiated at a fixed `α`), but *not* on
`g`, `g'`; the factorials in `Xn5` are the only genuine uniformity in the profile.  In particular
the `α^{-1}`-losses of the two `(3/(2α))·L₁₂(·)` pieces and of the modulation gradient are
absorbed by `Cl`. -/
structure RHSData (α : ℝ) (Φs : Fn) (EllSol : Fn → Fn) : Prop where
  /-- the `ℋ⁴`-size of the right-hand side on the smallness ball, in terms of its `ℋ⁵`-size -/
  bdd : ∃ Cb : ℝ, 0 ≤ Cb ∧ ∀ g : Fn, GalClass α g → α ≤ 1 → Xn α g ≤ α ^ (7 / 4 : ℝ) →
    Xn α (Fr α Φs EllSol g) ≤ Cb * (1 + Xn5 α g) ^ 3
  /-- the Lipschitz continuity of the right-hand side in the `ℋ⁴` metric, on the smallness ball,
  with a Lipschitz constant controlled by the two `ℋ⁵`-sizes -/
  lip : ∃ Cl : ℝ, 0 ≤ Cl ∧ ∀ g g' : Fn, GalClass α g → GalClass α g' →
    GalClass α (fun z θ => g z θ - g' z θ) → α ≤ 1 →
    Xn α g ≤ α ^ (7 / 4 : ℝ) → Xn α g' ≤ α ^ (7 / 4 : ℝ) →
    Xn α (fun z θ => Fr α Φs EllSol g z θ - Fr α Φs EllSol g' z θ)
      ≤ Cl * (1 + Xn5 α g + Xn5 α g') ^ 2 * Xn5 α (fun z θ => g z θ - g' z θ)

/-! ## The bundle of the five corrected fields -/

/-- **The five corrected compactness fields of the Galerkin existence theorem**, bundled in the
shape of `Work.FTS.Galerkin.DynInputs` (fields `L`, `hL`, `K`, `hK`, `hField_lip`,
`hField_bound`, `hField_cont`, `hProfileSpace`, `hProfileTau`), so that a caller can use this
structure as the `N4/N5` block of the a-priori bundle. -/
structure CorrectedFields (α : ℝ) (IP : ℝ → Fn → Fn → ℝ) (φ : ℕ → Fn) (Φs : Fn) (EllSol : Fn → Fn)
    (R : ℝ) where
  /-- the bound constant of the projected field -/
  L : ℕ → ℝ
  /-- the Lipschitz constant of the projected field -/
  K : ℕ → ℝ
  /-- positivity of the bound constant (the shape consumed by the ODE layer) -/
  hL : ∀ n : ℕ, 0 < L n
  /-- nonnegativity of the Lipschitz constant -/
  hK : ∀ n : ℕ, 0 ≤ K n
  hField_lip : hField_lip' α IP φ Φs EllSol R K hK
  hField_bound : hField_bound' α IP φ Φs EllSol R L
  hField_cont : hField_cont' α IP φ Φs EllSol R
  hProfileSpace : hProfileSpace' α IP φ Φs EllSol R
  hProfileTau : hProfileTau' α IP φ Φs EllSol R

/-! ## The Hölder modulus of the `ℋ²`-class (the paper's Corollary `Linf_H2`) -/

/-- **The Hölder modulus of the `ℋ²`-class** — the paper's Corollary `Linf_H2`
(tex 1056–1057: `|g|_{C^β} ≤ C_β|g|_{ℋ²}` for `β < γ-1`), in the *uniform* form the compactness
input needs: one constant `C`, depending only on `α` and `β`, works for every profile `f` of the
interior class and every box `[0,Z] × [0,π/2]`.

This is the corrected form of the (refuted) statement of
`Submission/Work/FTS/GalerkinFix/LinfQ/holder_modulus_of_HkNorm_two.lean`: the extra hypothesis is
the *continuity* of `f` on the closed box, without which the boundary values at `θ = 0, π/2` and
`z = 0` are not tied to the limits and no Hölder bound at those points can hold.

The route is recorded in `Submission/Work/FTS/GalFields/Holder/NOTES_holder.md`; the node is proved
in `Holder/holder_uniform.lean`.  `hProfileSpace'` is derived from it (`ProfileSpace.lean`). -/
def HkTwoHolder (α β : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ f : Fn, Work.FTS.LocData.SmoothQuad f → Work.Spaces.VanishTheta f →
    Work.Spaces.DecayInZ 2 f → Work.Spaces.HkMem α 2 f →
    ∀ Z : ℝ, 0 ≤ Z → ContinuousOn (Function.uncurry f) (Set.Icc 0 Z ×ˢ Set.Icc 0 (π / 2)) →
      ∀ z ∈ Set.Icc 0 Z, ∀ θ ∈ Set.Icc 0 (π / 2),
      ∀ z' ∈ Set.Icc 0 Z, ∀ θ' ∈ Set.Icc 0 (π / 2),
        |f z θ - f z' θ'| ≤ C * Work.Spaces.HkNorm α 2 f
          * (max (|z - z'|) (|θ - θ'|)) ^ β

/-! ## The ideal generated by the two analytic inputs -/

end Work.FTS.GalFields
