/-
# The interface of the large-scale estimate (`Work.KMTAreas.A7.ModelLargeBound`)

This module fixes the vocabulary in which the analytic content of the large-scale estimate (the
paper's §8, "exploiting tensor product structure") of

* B. Krause, M. Mirek, T. Tao, *Pointwise ergodic theorems for non-conventional bilinear
  polynomial averages*, Annals of Math. 195 (3) 2022,

is decomposed.  The model tuple of `Work.KMTAreas.A7.Large/Defs.lean` is

  `modelTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
    = if core … n then ∫_{1/2}^1 Btwist ρ P l₁ l₂ m_* m̃_* (T^{l₁}_{φ_{N,t}}f) (T^{l₂}_{φ̃_{N,t}}g)(x) dt else 0`

with `N = ⌊a n⌋`.  The two ingredients isolated here are

* the **fiber factorisation** of the twisted bilinear multiplier: the kernel identity
  `arithKernel ρ P q l₁ l₂ j₁ j₂ = q⁻¹ ∑_{n₀ < q} arithChar ρ l₁ (n₀-j₁) · arithChar ρ l₂ (P(n₀)-j₂)`
  (`Work.KMTAreas.A7.arithKernel_eq_arithChar`) exhibits `Btwist` as the average over the residue
  `n₀` of products of the *twisted projections*
  `fiberOp ρ l m n₀ u = ∑_j arithChar ρ l (n₀-j) · (𝓕⁻m j) · u(·-j)`
  (the paper's `form-1`, the "fibers" of the adelic integers, here indexed by `ℤ/qℤ`);
* the **variational estimate for the fibers**: `E_{n₀}‖V^r(fiberOp n₀ u_•)‖_{ℓ^p}^p` is
  controlled by `‖f‖_{ℓ^p}` (the paper's `(lin-1)`,`(lin-2)` combined with the quantitative
  Shannon sampling theorem, which identifies the fiber with a translate of `u`).
-/
import Mathlib
import Submission.Work.KMTAreas.A7.Large.ArithFactor

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTAreas.A7

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.Analysis.IonescuWainger Work.KMTContract Work.Analysis.EndVar

/-! ## The core index condition of the model tuple -/

/-- The condition under which the model tuple is non-zero: admissibility (`inIndexSet`), the
large-scale cut (`splitCut ρ L < N`) and the main regime of the functional calculus
(`mainRegime`, i.e. `k + 2u ≤ Log N`).  It depends on `n` only through `N = ⌊a n⌋`, and is
*upward closed* in `N`. -/
def core (ρ : ℝ) (C₀ : ℕ) (l₁ l₂ k₁ k₂ : ℕ) (a : ℕ → NNReal) (n : ℕ) : Prop :=
  inIndexSet C₀ (max (l₁ : ℤ) (l₂ : ℤ)) (k₁ : ℤ) (k₂ : ℤ) (Nat.floor (a n)) ∧
    splitCut ρ (max (max l₁ l₂) (max k₁ k₂)) < Nat.floor (a n) ∧
    mainRegime ρ k₁ k₂ (Nat.floor (a n))

instance coreDecidable (ρ : ℝ) (C₀ : ℕ) (l₁ l₂ k₁ k₂ : ℕ) (a : ℕ → NNReal) (n : ℕ) :
    Decidable (core ρ C₀ l₁ l₂ k₁ k₂ a n) := by
  unfold core; infer_instance

/-- The scale `L = max (max l₁ l₂) (max k₁ k₂)` of the loss, as a natural number. -/
def Lnat (l₁ l₂ k₁ k₂ : ℕ) : ℕ := max (max l₁ l₂) (max k₁ k₂)

/-- The `f`-side family of the model tuple, clipped at `core`: the IW projection of `f` against
the modulated bump `φ_{N,t}`, at the scale `N = ⌊a n⌋`, zero off the core. -/
def Hcl (ρ : ℝ) (C₀ : ℕ) (a : ℕ → NNReal) (l₁ l₂ k₁ k₂ : ℕ) (t : ℝ) (f : ℤ → ℂ) :
    ℕ → ℤ → ℂ :=
  fun n => if core ρ C₀ l₁ l₂ k₁ k₂ a n then
    Tex ρ l₁ (varphiNt (Nat.floor (a n)) k₁ t) f else 0

/-- The `g`-side family of the model tuple, clipped at `core`. -/
def Gcl (ρ : ℝ) (P : ℤ[X]) (C₀ : ℕ) (a : ℕ → NNReal) (l₁ l₂ k₁ k₂ : ℕ) (t : ℝ)
    (g : ℤ → ℂ) : ℕ → ℤ → ℂ :=
  fun n => if core ρ C₀ l₁ l₂ k₁ k₂ a n then
    Tex ρ l₂ (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) g else 0

/-! ## The fibers of the twisted bilinear multiplier -/

/-- The fiber of the twisted projection at the residue `n₀` (first variable): the convolution with
the kernel `j ↦ arithChar ρ l (n₀-j) · (𝓕⁻m j)`.  It is the multiplier with symbol
`∑_{β ∈ (ℚ/ℤ)_{≤ l}} e(β n₀) m(ξ-β)`, i.e. the Fourier synthesis of the arithmetic frequency
pieces of the multiplier `m`, and it is the discrete shadow of the translate `u(· - n₀/q)` of the
adelic lift of `u` (paper's `form-1`). -/
def fiberOp (ρ : ℝ) (l : ℕ) (m : ℝ → ℂ) (n₀ : ℤ) (u : ℤ → ℂ) : ℤ → ℂ :=
  fun x => ∑' j : ℤ, (∑ α ∈ iwArithFreqsNew ρ l, fourier (T := 1) (n₀ - j) α)
    * cw m j * u (x - j)

/-- The fiber of the twisted projection at the residue `n₀` (second variable), with the polynomial
twist `P`: the convolution with the kernel `j ↦ arithChar ρ l (P(n₀)-j) · (𝓕⁻m j)`. -/
def fiberOpP (ρ : ℝ) (P : ℤ[X]) (l : ℕ) (m : ℝ → ℂ) (n₀ : ℤ) (v : ℤ → ℂ) : ℤ → ℂ :=
  fun x => ∑' j : ℤ, (∑ α ∈ iwArithFreqsNew ρ l, fourier (T := 1) (P.eval n₀ - j) α)
    * cw m j * v (x - j)

/-! ## The `ℓ^p` norm over the residues -/

/-- The `ℓ^p` norm over the residues `n₀ < q` of a family `W x n₀`, as a function of `x`:
`(q⁻¹ ∑_{n₀<q} W x n₀ ^ p)^{1/p}`.  This is the quantity that the Hölder inequality in the fiber
variable `n₀` produces. -/
def residueLp (p : ℝ) (q : ℕ) (W : ℤ → ℕ → ENNReal) : ℤ → ENNReal :=
  fun x => ENNReal.rpow (ENNReal.rpow (q : ENNReal) (-1) * ∑ n₀ ∈ Finset.range q,
    ENNReal.rpow (W x n₀) p) (1 / p)

/-! ## Elementary properties -/

/-- The supremum part of the variational norm: `sup_n ‖u n x‖ₑ ≤ variationalNorm r u` (pointwise
in `x`).  This lets the maximal function over the scale be read off from the variational norm. -/
theorem iSup_enorm_le_variationalNorm (r : NNReal) (u : ℕ → ℂ) (x : ℤ) :
    (⨆ n, ‖u n‖ₑ) ≤ PointwiseErgodicTheorems.variationalNorm r (fun n => u n) := by
  rw [PointwiseErgodicTheorems.variationalNorm, ← Submission.PointwiseErgodicTheorems.varPart]
  exact le_add_right le_rfl

/-- The variational norm dominates the values: `‖u n x‖ₑ ≤ variationalNorm r u`. -/
theorem enorm_apply_le_variationalNorm {r : NNReal} (u : ℕ → ℂ) (n : ℕ) :
    ‖u n‖ₑ ≤ PointwiseErgodicTheorems.variationalNorm r u :=
  le_trans (le_iSup (fun k => ‖u k‖ₑ) n) (iSup_enorm_le_variationalNorm r u n)

end

end Work.KMTAreas.A7
