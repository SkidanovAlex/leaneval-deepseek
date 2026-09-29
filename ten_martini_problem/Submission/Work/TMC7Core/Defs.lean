import ChallengeDeps

/-!
# TMC7Core: local copies of the TMPlan interface definitions (C7 scope)

Definitions are copied **verbatim** (same names, same argument order, same bodies) from
`Submission/Work/TMPlan/Interfaces.lean`, so that once `TMContract` freezes that file a
bridge `TMPlan.X = Work.TMC7Core.X` is `rfl`.

Only the definitions used by the Bourgain--Jitomirskaya component (C7, `P_BJ`) are copied.
-/

open MeasureTheory Filter Topology Set
open LeanEval.Analysis.TenMartini

noncomputable section

namespace Work.TMC7Core

/-! ## 1. The operator and its spectrum -/

/-- The potential `v_n = 2 λ cos 2π(θ + nα)`, written exactly as in the challenge. -/
def amoPot (α lam θ : ℝ) (n : ℤ) : ℝ :=
  2 * lam * Real.cos (2 * Real.pi * (θ + (n : ℝ) * α))

/-- The almost Mathieu difference expression acting on arbitrary sequences
(used for formal, non-`ℓ²` solutions). -/
def amoAct (α lam θ : ℝ) (u : ℤ → ℂ) (n : ℤ) : ℂ :=
  u (n + 1) + u (n - 1) + ((amoPot α lam θ n : ℝ) : ℂ) * u n

/-- `amoAct` with the real coercion pushed inside the product (the shape in which the
challenge's `IsAlmostMathieuOperator` elaborates). -/
theorem amoAct_eq (α lam θ : ℝ) (u : ℤ → ℂ) (n : ℤ) :
    amoAct α lam θ u n = u (n + 1) + u (n - 1) +
      ((2 : ℂ) * (lam : ℂ) * (Real.cos (2 * Real.pi * (θ + (n : ℝ) * α)) : ℂ)) * u n := by
  rw [amoAct, amoPot]
  push_cast
  ring

/-- The challenge predicate is `amoAct` applied coordinatewise (definitional). -/
theorem isAMO_iff (α lam θ : ℝ) (H : EllTwo →L[ℂ] EllTwo) :
    IsAlmostMathieuOperator α lam θ H ↔
      ∀ (u : EllTwo) (n : ℤ), H u n = amoAct α lam θ (fun m => u m) n := by
  unfold IsAlmostMathieuOperator
  constructor <;> intro h u n
  · simpa only [amoAct_eq] using h u n
  · simpa only [amoAct_eq] using h u n

/-- `Σ_{λ,α}` as a set of reals: the spectrum at phase `θ = 0`. -/
def amoSpec (α lam : ℝ) : Set ℝ :=
  {E | ∃ H : EllTwo →L[ℂ] EllTwo, IsAlmostMathieuOperator α lam 0 H ∧ (E : ℂ) ∈ spectrum ℂ H}

/-- `S` contains a nondegenerate open interval. -/
def HasInterval (S : Set ℝ) : Prop := ∃ a b : ℝ, a < b ∧ Ioo a b ⊆ S

/-- The whole problem: `Σ_{λ,α}` has empty interior. -/
def NoInterval (α lam : ℝ) : Prop := ¬ HasInterval (amoSpec α lam)

/-- Exponential decay of a sequence. -/
def ExpDecay (u : ℤ → ℂ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, ∀ n : ℤ, ‖u n‖ ≤ C * Real.exp (-(c * |(n : ℝ)|))

/-- AJ (9.2): a generalized eigenfunction (a nonzero, polynomially bounded formal solution). -/
def IsGenEigen (α lam θ E : ℝ) (u : ℤ → ℂ) : Prop :=
  u ≠ 0 ∧ (∀ n : ℤ, amoAct α lam θ u n = (E : ℂ) * u n) ∧
    ∃ C : ℝ, ∀ n : ℤ, ‖u n‖ ≤ C * (1 + |(n : ℝ)|)

/-- For almost every phase, every generalized eigenfunction decays exponentially. -/
def ExpLocAE (α lam : ℝ) : Prop :=
  ∀ᵐ θ ∂(volume : Measure ℝ), ∀ (E : ℝ) (u : ℤ → ℂ), IsGenEigen α lam θ E u → ExpDecay u

/-! ## 2. Arithmetic of `α` -/

/-- Distance to the nearest integer. -/
def fracDist (x : ℝ) : ℝ := |x - round x|

def LiouvilleAbove (α b : ℝ) : Prop :=
  ∃ᶠ k : ℕ in atTop, fracDist ((k : ℝ) * α) < Real.exp (-(b * k))

def DiophBelow (α b : ℝ) : Prop :=
  ∀ᶠ k : ℕ in atTop, Real.exp (-(b * k)) ≤ fracDist ((k : ℝ) * α)

/-! ## 3. Cocycles and the Lyapunov exponent -/

/-- The almost Mathieu transfer matrix `S_{λ,E}(x)` (AJ (2.8)) with complex energy. -/
def tmC (lam : ℝ) (E : ℂ) (x : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![E - ((2 * lam * Real.cos (2 * Real.pi * x) : ℝ) : ℂ), -1; 1, 0]

/-- `A_n(x) = S(x + (n-1)α) ⋯ S(x)` (AJ (2.2)). -/
def iterC (α lam : ℝ) (E : ℂ) : ℕ → ℝ → Matrix (Fin 2) (Fin 2) ℂ
  | 0, _ => 1
  | n + 1, x => tmC lam E (x + (n : ℝ) * α) * iterC α lam E n x

/-- Frobenius norm. -/
def frob (A : Matrix (Fin 2) (Fin 2) ℂ) : ℝ :=
  Real.sqrt (‖A 0 0‖ ^ 2 + ‖A 0 1‖ ^ 2 + ‖A 1 0‖ ^ 2 + ‖A 1 1‖ ^ 2)

/-- The Lyapunov exponent `L(E) = lim (1/n) ∫ ln ‖A_n‖ = inf_n (1/n) ∫ ln ‖A_n‖`. -/
def lyap (α lam : ℝ) (E : ℂ) : ℝ :=
  ⨅ n : ℕ, (∫ x in (0 : ℝ)..1, Real.log (frob (iterC α lam E (n + 1) x))) / ((n : ℝ) + 1)

/-- Real transfer matrix (real energy). -/
def tmR (lam E x : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![E - 2 * lam * Real.cos (2 * Real.pi * x), -1; 1, 0]

/-- AJ's rotation `R_c` (AJ (2.7)); `c` in turns. -/
def rot (c : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.cos (2 * Real.pi * c), -Real.sin (2 * Real.pi * c);
     Real.sin (2 * Real.pi * c), Real.cos (2 * Real.pi * c)]

/-! ## 6. Component `Prop`s needed by C7 -/

/-- **C0** Unique ergodicity of an irrational rotation, in its uniform form (Weyl). -/
def P_UniqErg : Prop :=
  ∀ α : ℝ, Irrational α → ∀ f : ℝ → ℝ, Continuous f → (∀ x, f (x + 1) = f x) →
    TendstoUniformly
      (fun (n : ℕ) (x : ℝ) => (∑ j ∈ Finset.range n, f (x + (j : ℝ) * α)) / (n : ℝ))
      (fun _ => ∫ x in (0 : ℝ)..1, f x) atTop

/-- **C1** Operator basics. -/
def P_OpBasics : Prop :=
  (∀ α lam θ : ℝ, ∃ H : EllTwo →L[ℂ] EllTwo, IsAlmostMathieuOperator α lam θ H) ∧
  (∀ (α lam θ : ℝ) (H : EllTwo →L[ℂ] EllTwo),
      IsAlmostMathieuOperator α lam θ H → IsSelfAdjoint H) ∧
  (∀ α lam θ θ' : ℝ, Irrational α → ∀ H H' : EllTwo →L[ℂ] EllTwo,
      IsAlmostMathieuOperator α lam θ H → IsAlmostMathieuOperator α lam θ' H' →
      spectrum ℂ H = spectrum ℂ H')

/-- **C4** Herman's bound and the locally uniform upper bound (Furman). -/
def P_LEBasics : Prop :=
  (∀ (α lam : ℝ) (E : ℂ), Real.log |lam| ≤ lyap α lam E) ∧
  (∀ α lam : ℝ, Irrational α → ∀ (E₀ : ℂ) (ε : ℝ), 0 < ε →
      ∃ r : ℝ, 0 < r ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ E : ℂ, ‖E - E₀‖ < r → ∀ x : ℝ,
        Real.log (frob (iterC α lam E n x)) ≤ (n : ℝ) * (lyap α lam E₀ + ε))

/-- **C7** Bourgain–Jitomirskaya (AJ Thm 2.1 = [BJ] Cor. 2). -/
def P_BJ : Prop :=
  ∀ α lam : ℝ, Irrational α → lam ≠ 0 → ∀ E ∈ amoSpec α lam,
    lyap α lam (E : ℂ) = max 0 (Real.log |lam|)

/-- **C15** Weak Schnol: every spectral point is a limit of generalized eigenvalues
(AJ §9, first paragraph, [Be]).  Copied verbatim from `TMPlan/Interfaces.lean`; C7 uses it as
an extra hypothesis (its only use is the Floquet direction for rational frequencies). -/
def P_Schnol : Prop :=
  ∀ (α lam θ : ℝ) (H : EllTwo →L[ℂ] EllTwo), IsAlmostMathieuOperator α lam θ H →
    ∀ E₀ : ℝ, (E₀ : ℂ) ∈ spectrum ℂ H → ∀ δ : ℝ, 0 < δ →
      ∃ E : ℝ, |E - E₀| < δ ∧ ∃ u : ℤ → ℂ, IsGenEigen α lam θ E u

end Work.TMC7Core

end
