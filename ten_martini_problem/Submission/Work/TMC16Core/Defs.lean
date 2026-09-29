/-
# TMC16Core: Anderson localisation for large coupling (AJ §9)

Local copy of the definitions needed to state and prove component C16 (`P_Loc`)
of the Ten Martini formalisation.  Everything here is copied VERBATIM from
`Submission/Work/TMPlan/Interfaces.lean` (same names, same argument order), with
`namespace TMPlan` replaced by `namespace Work.TMC16Core`, so that a bridge to
the frozen interface is `unfold`-and-`rfl`.  `EllTwo` and
`IsAlmostMathieuOperator` are taken from the trusted `ChallengeDeps`.
-/
import Mathlib
import ChallengeDeps

open MeasureTheory Filter Topology Set
open LeanEval.Analysis.TenMartini

noncomputable section

namespace Work.TMC16Core

/-! ## 1. Verbatim copies from `TMPlan/Interfaces.lean` -/

def amoPot (α lam θ : ℝ) (n : ℤ) : ℝ :=
  2 * lam * Real.cos (2 * Real.pi * (θ + (n : ℝ) * α))

def amoAct (α lam θ : ℝ) (u : ℤ → ℂ) (n : ℤ) : ℂ :=
  u (n + 1) + u (n - 1) + ((amoPot α lam θ n : ℝ) : ℂ) * u n

def amoSpec (α lam : ℝ) : Set ℝ :=
  {E | ∃ H : EllTwo →L[ℂ] EllTwo, IsAlmostMathieuOperator α lam 0 H ∧ (E : ℂ) ∈ spectrum ℂ H}

def HasInterval (S : Set ℝ) : Prop := ∃ a b : ℝ, a < b ∧ Ioo a b ⊆ S

def NoInterval (α lam : ℝ) : Prop := ¬ HasInterval (amoSpec α lam)

def IsGenEigen (α lam θ E : ℝ) (u : ℤ → ℂ) : Prop :=
  u ≠ 0 ∧ (∀ n : ℤ, amoAct α lam θ u n = (E : ℂ) * u n) ∧
    ∃ C : ℝ, ∀ n : ℤ, ‖u n‖ ≤ C * (1 + |(n : ℝ)|)

def ExpDecay (u : ℤ → ℂ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, ∀ n : ℤ, ‖u n‖ ≤ C * Real.exp (-(c * |(n : ℝ)|))

def ExpLocAE (α lam : ℝ) : Prop :=
  ∀ᵐ θ ∂(volume : Measure ℝ), ∀ (E : ℝ) (u : ℤ → ℂ), IsGenEigen α lam θ E u → ExpDecay u

def fracDist (x : ℝ) : ℝ := |x - round x|

def LiouvilleAbove (α b : ℝ) : Prop :=
  ∃ᶠ k : ℕ in atTop, fracDist ((k : ℝ) * α) < Real.exp (-(b * k))

def DiophBelow (α b : ℝ) : Prop :=
  ∀ᶠ k : ℕ in atTop, Real.exp (-(b * k)) ≤ fracDist ((k : ℝ) * α)

def tmC (lam : ℝ) (E : ℂ) (x : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![E - ((2 * lam * Real.cos (2 * Real.pi * x) : ℝ) : ℂ), -1; 1, 0]

def iterC (α lam : ℝ) (E : ℂ) : ℕ → ℝ → Matrix (Fin 2) (Fin 2) ℂ
  | 0, _ => 1
  | n + 1, x => tmC lam E (x + (n : ℝ) * α) * iterC α lam E n x

def frob (A : Matrix (Fin 2) (Fin 2) ℂ) : ℝ :=
  Real.sqrt (‖A 0 0‖ ^ 2 + ‖A 0 1‖ ^ 2 + ‖A 1 0‖ ^ 2 + ‖A 1 1‖ ^ 2)

def lyap (α lam : ℝ) (E : ℂ) : ℝ :=
  ⨅ n : ℕ, (∫ x in (0 : ℝ)..1, Real.log (frob (iterC α lam E (n + 1) x))) / ((n : ℝ) + 1)

def tmR (lam E x : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![E - 2 * lam * Real.cos (2 * Real.pi * x), -1; 1, 0]

def rot (c : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.cos (2 * Real.pi * c), -Real.sin (2 * Real.pi * c);
     Real.sin (2 * Real.pi * c), Real.cos (2 * Real.pi * c)]

def HasDegree (B : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (k : ℤ) : Prop :=
  Continuous B ∧ ∃ η : ℝ → ℝ, Continuous η ∧ (∀ x, η (x + 1) = η x + k) ∧
    ∀ x, ∃ r : ℝ, 0 < r ∧ B x 0 0 = r * Real.cos (2 * Real.pi * η x) ∧
      B x 1 0 = r * Real.sin (2 * Real.pi * η x)

def RedSet (α lam : ℝ) : Set ℝ :=
  {E | ∃ (B : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (c : ℝ),
      (∀ i j, AnalyticOnNhd ℝ (fun x => B x i j) univ) ∧ (∀ x, B (x + 1) = B x) ∧
      (∀ x, (B x).det = 1) ∧ HasDegree B 0 ∧
      ∀ x, B (x + α) * tmR lam E x = rot c * B x}

def pruferStep (a t : ℝ) : ℝ :=
  if t - (⌊t + 1 / 2⌋ : ℝ) = -1 / 2 then (⌊t + 1 / 2⌋ : ℝ)
  else (⌊t + 1 / 2⌋ : ℝ) + 1 / 2 +
    Real.arctan (Real.tan (Real.pi * (t - (⌊t + 1 / 2⌋ : ℝ))) - a) / Real.pi

def pruferIter (α lam E : ℝ) : ℕ → ℝ → ℝ → ℝ
  | 0, _, t => t
  | n + 1, x, t =>
      pruferStep (E - 2 * lam * Real.cos (2 * Real.pi * (x + (n : ℝ) * α)))
        (pruferIter α lam E n x t)

def rotLift (α lam E : ℝ) : ℝ :=
  limUnder atTop (fun n : ℕ => (∫ x in (0 : ℝ)..1, pruferIter α lam E n x 0) / (n : ℝ))

def ids (α lam E : ℝ) : ℝ := 1 - rotLift α lam E

def mob (M : Matrix (Fin 2) (Fin 2) ℂ) (z : ℂ) : ℂ :=
  (M 0 0 * z + M 0 1) / (M 1 0 * z + M 1 1)

def backIterC (α lam : ℝ) (E : ℂ) : ℕ → ℝ → Matrix (Fin 2) (Fin 2) ℂ
  | 0, _ => 1
  | n + 1, x => backIterC α lam E n x * tmC lam E (x - ((n : ℝ) + 1) * α)

def amoM (α lam : ℝ) (E : ℂ) (x : ℝ) : ℂ :=
  limUnder atTop (fun n : ℕ => mob (backIterC α lam E n x) Complex.I)

def kotaniDomain (a b : ℝ) : Set ℂ :=
  {z | z.im ≠ 0 ∨ (z.im = 0 ∧ a < z.re ∧ z.re < b)}

/-! ## 2. Component `Prop`s (verbatim) -/

def P_UniqErg : Prop :=
  ∀ α : ℝ, Irrational α → ∀ f : ℝ → ℝ, Continuous f → (∀ x, f (x + 1) = f x) →
    TendstoUniformly
      (fun (n : ℕ) (x : ℝ) => (∑ j ∈ Finset.range n, f (x + (j : ℝ) * α)) / (n : ℝ))
      (fun _ => ∫ x in (0 : ℝ)..1, f x) atTop

def P_OpBasics : Prop :=
  (∀ α lam θ : ℝ, ∃ H : EllTwo →L[ℂ] EllTwo, IsAlmostMathieuOperator α lam θ H) ∧
  (∀ (α lam θ : ℝ) (H : EllTwo →L[ℂ] EllTwo),
      IsAlmostMathieuOperator α lam θ H → IsSelfAdjoint H) ∧
  (∀ α lam θ θ' : ℝ, Irrational α → ∀ H H' : EllTwo →L[ℂ] EllTwo,
      IsAlmostMathieuOperator α lam θ H → IsAlmostMathieuOperator α lam θ' H' →
      spectrum ℂ H = spectrum ℂ H')

def P_Perfect : Prop :=
  ∀ α lam θ : ℝ, Irrational α → ∀ H : EllTwo →L[ℂ] EllTwo,
    IsAlmostMathieuOperator α lam θ H → Perfect (spectrum ℂ H)

def P_Duality : Prop :=
  ∀ α lam : ℝ, Irrational α → lam ≠ 0 → ∀ E : ℝ, E ∈ amoSpec α lam ↔ E / lam ∈ amoSpec α lam⁻¹

def P_LEBasics : Prop :=
  (∀ (α lam : ℝ) (E : ℂ), Real.log |lam| ≤ lyap α lam E) ∧
  (∀ α lam : ℝ, Irrational α → ∀ (E₀ : ℂ) (ε : ℝ), 0 < ε →
      ∃ r : ℝ, 0 < r ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ E : ℂ, ‖E - E₀‖ < r → ∀ x : ℝ,
        Real.log (frob (iterC α lam E n x)) ≤ (n : ℝ) * (lyap α lam E₀ + ε))

def P_RotBasics : Prop :=
  (∀ α lam E : ℝ, Tendsto (fun n : ℕ => (∫ x in (0 : ℝ)..1, pruferIter α lam E n x 0) / (n : ℝ))
      atTop (𝓝 (rotLift α lam E))) ∧
  (∀ α lam : ℝ, Monotone (ids α lam)) ∧
  (∀ lam : ℝ, Continuous (fun p : ℝ × ℝ => ids p.1 lam p.2)) ∧
  (∀ (α lam E : ℝ) (B : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (φ : ℝ → ℝ) (k : ℤ),
      HasDegree B k → (∀ x, B (x + 1) = B x) → (∀ x, (B x).det = 1) →
      Continuous φ → (∀ x, φ (x + 1) = φ x) →
      (∀ x, B (x + α) * tmR lam E x = rot (φ x) * B x) →
      ∃ j : ℤ, rotLift α lam E = 2 * (∫ x in (0 : ℝ)..1, φ x) - 2 * (k : ℝ) * α + 2 * (j : ℝ))

def P_IDSSpectrum : Prop :=
  ∀ α lam : ℝ, Irrational α → ∀ E ∈ amoSpec α lam, ∀ ε : ℝ, 0 < ε →
    ids α lam (E - ε) < ids α lam (E + ε)

def P_BJ : Prop :=
  ∀ α lam : ℝ, Irrational α → lam ≠ 0 → ∀ E ∈ amoSpec α lam,
    lyap α lam (E : ℂ) = max 0 (Real.log |lam|)

def P_Kotani : Prop :=
  ∀ α lam a b : ℝ, Irrational α → 0 ≤ lam → a < b →
    (∀ E ∈ Ioo a b, lyap α lam (E : ℂ) = 0) →
    ∃ M : ℂ → ℝ → ℂ,
      ContinuousOn (fun p : ℂ × ℝ => M p.1 p.2) (kotaniDomain a b ×ˢ univ) ∧
      (∀ x : ℝ, DifferentiableOn ℂ (fun z => M z x) (kotaniDomain a b)) ∧
      (∀ z ∈ kotaniDomain a b, ∀ x : ℝ, 0 < (M z x).im) ∧
      (∀ z : ℂ, 0 < z.im → ∀ x : ℝ, M z x = amoM α lam z x) ∧
      (∀ (z : ℂ) (x : ℝ), M z (x + 1) = M z x)

def P_mAnalytic : Prop :=
  ∀ α lam a b : ℝ, Irrational α → 0 < lam → lam ≤ 1 → a < b → Ioo a b ⊆ amoSpec α lam →
    ∃ (C : ℝ → ℝ → Matrix (Fin 2) (Fin 2) ℝ) (φ : ℝ → ℝ → ℝ),
      (∀ i j, AnalyticOnNhd ℝ (fun p : ℝ × ℝ => C p.1 p.2 i j) (Ioo a b ×ˢ univ)) ∧
      AnalyticOnNhd ℝ (fun p : ℝ × ℝ => φ p.1 p.2) (Ioo a b ×ˢ univ) ∧
      (∀ E x, C E (x + 1) = C E x) ∧ (∀ E x, φ E (x + 1) = φ E x) ∧
      (∀ E ∈ Ioo a b, ∀ x, (C E x).det = 1) ∧
      (∀ E ∈ Ioo a b, HasDegree (C E) 0) ∧
      (∀ E ∈ Ioo a b, ∀ x, C E (x + α) * tmR lam E x = rot (φ E x) * C E x)

def P_Schnol : Prop :=
  ∀ (α lam θ : ℝ) (H : EllTwo →L[ℂ] EllTwo), IsAlmostMathieuOperator α lam θ H →
    ∀ E₀ : ℝ, (E₀ : ℂ) ∈ spectrum ℂ H → ∀ δ : ℝ, 0 < δ →
      ∃ E : ℝ, |E - E₀| < δ ∧ ∃ u : ℤ → ℂ, IsGenEigen α lam θ E u

/-- **C7 at Diophantine frequencies only.**  This is the only form of C7 that C16 consumes:
`DiophBelow α b₀` with `0 < b₀` is exactly "`α` is Diophantine of exponent `b₀`".  (The full
`P_BJ`, needed for the Liouville case, is *not* required here; the frozen Diophantine case is
proved in `Submission/Work/TMComp/RedC7T/dbj_dioph_final.lean` as `D_BJ_dioph_uncond`.) -/
def P_BJ_dioph : Prop :=
  ∀ α lam b₀ : ℝ, Irrational α → 0 < b₀ → DiophBelow α b₀ → lam ≠ 0 →
    ∀ E : ℝ, E ∈ amoSpec α lam → lyap α lam (E : ℂ) = max 0 (Real.log |lam|)

def P_Loc : Prop :=
  ∀ α b₀ lam : ℝ, Irrational α → 0 ≤ b₀ → DiophBelow α b₀ →
    Real.exp (16 * b₀ / 9) < lam → ExpLocAE α lam

/-! ## 3. Finite-volume objects of AJ §9 (new definitions of this subproject) -/

/-- Phase-dependent version of `amoSpec`. -/
def amoSpecTh (α lam θ : ℝ) : Set ℝ :=
  {E | ∃ H : EllTwo →L[ℂ] EllTwo, IsAlmostMathieuOperator α lam θ H ∧ (E : ℂ) ∈ spectrum ℂ H}

/-- `H - E` restricted to `n` consecutive sites (positions `0,…,n-1`, phase `θ`) with zero
boundary conditions: the symmetric tridiagonal matrix with diagonal `amoPot α lam θ j - E`
and off-diagonal `1`. -/
def dirMat (α lam : ℝ) (θ : ℝ) (E : ℂ) (n : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j =>
    (if i = j then (((amoPot α lam θ ((i : ℕ) : ℤ) : ℝ) : ℂ) - E) else 0) +
      (if ((i : ℕ) : ℤ) + 1 = ((j : ℕ) : ℤ) then 1 else 0) +
      (if ((j : ℕ) : ℤ) + 1 = ((i : ℕ) : ℤ) then 1 else 0)

/-- AJ §9: `pd k = P_{k-1}(θ)`, the continuant of `(E - H)` with diagonal `E - v_j` and
off-diagonal `-1`, so that `P_k(θ) = det ((E - H)|_{[0,k-1]}) = pd (k+1)`.  Conventions
`P_0 = 1`, `P_{-1} = 0` (the latter is `pd 0`). -/
def pd (α lam : ℝ) (θ : ℝ) (E : ℂ) : ℕ → ℂ
  | 0 => 0
  | 1 => 1
  | n + 2 =>
      (E - (((amoPot α lam θ ((n : ℕ) : ℤ) : ℝ) : ℂ))) * pd α lam θ E (n + 1) - pd α lam θ E n

/-- The `(i,j)` element of the Dirichlet Green's function on `[0,k-1]`, i.e. of the inverse
of `dirMat`; junk (`0`) outside the range. -/
def greenEntry (α lam : ℝ) (θ : ℝ) (E : ℂ) (k : ℕ) (i j : ℕ) : ℂ :=
  if h : i < k ∧ j < k then (dirMat α lam θ E k)⁻¹ ⟨i, h.1⟩ ⟨j, h.2⟩ else 0

/-- Dirichlet Green's function `G_{[x₁,x₂]}(x,y)` of AJ §9: the inverse of the restriction
of `H - E` to `[x₁,x₂]`, phase parameter shifted by `x₁α`. -/
def G (α lam : ℝ) (θ : ℝ) (E : ℂ) (x₁ x₂ x y : ℤ) : ℂ :=
  greenEntry α lam (θ + (x₁ : ℝ) * α) E ((x₂ - x₁ + 1).toNat) ((x - x₁).toNat)
    ((y - x₁).toNat)

/-- `u` solves the almost Mathieu equation `H u = E u` at every site (a formal solution). -/
def IsFormalSol (α lam θ : ℝ) (E : ℂ) (u : ℤ → ℂ) : Prop :=
  ∀ n : ℤ, amoAct α lam θ u n = E * u n

/-- AJ §9, before (9.4): `y` is `(m,k)`-regular if some interval `[x₁,x₂]` of `k` sites
contains `y` at distance `≥ k/40` from both endpoints, the Dirichlet operator on the
interval is invertible (`det ≠ 0`; otherwise the Green's function is not defined) and the
Green's function at `y` against the two endpoints decays at rate `m`. -/
def IsRegular (α lam : ℝ) (θ : ℝ) (E : ℂ) (m : ℝ) (k : ℕ) (y : ℤ) : Prop :=
  ∃ x₁ x₂ : ℤ, x₂ = x₁ + (k : ℤ) - 1 ∧ x₁ ≤ y ∧ y ≤ x₂ ∧
    (k : ℤ) ≤ 40 * (y - x₁) ∧ (k : ℤ) ≤ 40 * (x₂ - y) ∧
    (dirMat α lam (θ + (x₁ : ℝ) * α) E k).det ≠ 0 ∧
    ‖G α lam θ E x₁ x₂ y x₁‖ < Real.exp (-(m * |((y - x₁ : ℤ) : ℝ)|)) ∧
    ‖G α lam θ E x₁ x₂ y x₂‖ < Real.exp (-(m * |((y - x₂ : ℤ) : ℝ)|))

/-- AJ §9: `y` is `(m,k)`-singular when it is not `(m,k)`-regular. -/
def IsSingular (α lam : ℝ) (θ : ℝ) (E : ℂ) (m : ℝ) (k : ℕ) (y : ℤ) : Prop :=
  ¬ IsRegular α lam θ E m k y

/-- Regularity with a prescribed *lower* bound `q` on the length of the witnessing interval
(this is the form used by the patching argument, where the scale is chosen at the end). -/
def IsRegularBig (α lam : ℝ) (θ : ℝ) (E : ℂ) (m q : ℝ) (y : ℤ) : Prop :=
  ∃ x₁ x₂ : ℤ, x₁ ≤ y ∧ y ≤ x₂ ∧ q ≤ ((x₂ - x₁ + 1 : ℤ) : ℝ) ∧
    (40 : ℝ) * ((y - x₁ : ℤ) : ℝ) ≥ ((x₂ - x₁ + 1 : ℤ) : ℝ) ∧
    (40 : ℝ) * ((x₂ - y : ℤ) : ℝ) ≥ ((x₂ - x₁ + 1 : ℤ) : ℝ) ∧
    (dirMat α lam (θ + (x₁ : ℝ) * α) E ((x₂ - x₁ + 1).toNat)).det ≠ 0 ∧
    ‖G α lam θ E x₁ x₂ y x₁‖ < Real.exp (-(m * ((y - x₁ : ℤ) : ℝ))) ∧
    ‖G α lam θ E x₁ x₂ y x₂‖ < Real.exp (-(m * ((x₂ - y : ℤ) : ℝ)))

/-- AJ §9: `A_{k,r} = {θ : |Q_k(cos 2πθ)| ≤ e^{(k+1)r}}`, written with the shift folded in:
`θ ∈ AkSet α lam E k r ↔ ‖P_k(θ - (k-1)α/2)‖ ≤ e^{(k+1)r}`. -/
def AkSet (α lam : ℝ) (E : ℂ) (k : ℕ) (r : ℝ) : Set ℝ :=
  {θ : ℝ | ‖pd α lam (θ - (((k : ℝ) - 1) / 2) * α) E (k + 1)‖ ≤
    Real.exp (((k : ℝ) + 1) * r)}

/-- AJ (9.8): a finite family of phases is `ε`-uniform if their cosines are pairwise
distinct (the Lagrange interpolation points are distinct) and all Lagrange products are
`< e^{(#ι-1)ε}`. -/
def Uniform {ι : Type*} [Fintype ι] [DecidableEq ι] (ε : ℝ) (z : ι → ℝ) : Prop :=
  (∀ i j : ι, i ≠ j → Real.cos (2 * Real.pi * z i) ≠ Real.cos (2 * Real.pi * z j)) ∧
    ∀ j : ι, ∀ x ∈ Icc (-1 : ℝ) 1,
      |∏ i ∈ Finset.univ.erase j,
          (x - Real.cos (2 * Real.pi * z i)) /
            (Real.cos (2 * Real.pi * z j) - Real.cos (2 * Real.pi * z i))|
        < Real.exp (((Fintype.card ι : ℝ) - 1) * ε)

/-- The null exceptional set of phases (AJ (9.1), with the collision index ranging over all of
`ℤ` -- the negative indices matter in the Lagrange denominators of AJ §9 -- together with the
exact-collision set `2θ + mα ∈ ℤ`). -/
def Theta (α : ℝ) : Set ℝ :=
  {θ : ℝ |
    (∃ᶠ k : ℤ in atTop,
        fracDist (2 * θ + (k : ℝ) * α) < (((k.natAbs : ℕ) : ℝ))⁻¹ ^ 2) ∨
      (∃ᶠ k : ℤ in atBot,
        fracDist (2 * θ + (k : ℝ) * α) < (((k.natAbs : ℕ) : ℝ))⁻¹ ^ 2) ∨
      ∃ m : ℤ, ∃ z : ℤ, 2 * θ + (m : ℝ) * α = (z : ℝ)}

theorem mem_AkSet_iff (α lam : ℝ) (E : ℂ) (k : ℕ) (r : ℝ) (θ : ℝ) :
    θ ∈ AkSet α lam E k r ↔
      ‖pd α lam (θ - (((k : ℝ) - 1) / 2) * α) E (k + 1)‖ ≤ Real.exp (((k : ℝ) + 1) * r) :=
  Iff.rfl

theorem mem_AkSet_iff_shift (α lam : ℝ) (E : ℂ) (k : ℕ) (r : ℝ) (θ : ℝ) (x : ℤ) :
    (θ + ((x : ℝ) + (((k : ℝ) - 1) / 2)) * α ∈ AkSet α lam E k r) ↔
      ‖pd α lam (θ + (x : ℝ) * α) E (k + 1)‖ ≤ Real.exp (((k : ℝ) + 1) * r) := by
  rw [mem_AkSet_iff]
  have h : θ + ((x : ℝ) + (((k : ℝ) - 1) / 2)) * α - (((k : ℝ) - 1) / 2) * α
      = θ + (x : ℝ) * α := by ring
  rw [h]

/-! ## 4. Interfaces for the AJ §9 core (this subproject) -/

/-- The multiscale regularity output of AJ §9 (Lemmas 9.4 and 9.5, ROUTE_LEAD 16e/16f), in
the form consumed by the patching argument (`patching`): there is a uniform rate `L₁ > 0`
such that for every prescribed lower bound `q > 0` on the length of the witnessing interval,
every sufficiently large site `y` is `(L₁, ≥q)`-regular. -/
def RegFamily (α lam : ℝ) (θ : ℝ) (E : ℝ) : Prop :=
  ∃ L₁ : ℝ, 0 < L₁ ∧ ∀ q : ℝ, 0 < q → ∃ b : ℝ, ∀ y : ℤ, b < (y : ℝ) →
    IsRegularBig α lam θ (E : ℂ) L₁ q y

/-- **C16, core input (AJ Thm 9.1 / 5.2).**  For `DiophBelow α b₀` and `λ > e^{16b₀/9}`:
outside the null set `Θ` of phases, every generalized eigenfunction with `u 0 ≠ 0` gives
rise to the regularity family.  (The proof is AJ §9: Lemmas 9.4 and 9.5, using the
singularity of `0` and the trigonometric-product estimates.) -/
def P_RegFamily : Prop :=
  ∀ α b₀ lam : ℝ, Irrational α → 0 ≤ b₀ → DiophBelow α b₀ →
    Real.exp (16 * b₀ / 9) < lam → ∀ E ∈ amoSpec α lam, ∀ θ : ℝ, θ ∉ Theta α →
      ∀ u : ℤ → ℂ, IsGenEigen α lam θ E u → u 0 ≠ 0 → RegFamily α lam θ E

/-- Positive-side exponential decay of every generalized eigenfunction, for a.e. phase. -/
def ExpLocAEpos (α lam : ℝ) : Prop :=
  ∀ᵐ θ ∂(volume : Measure ℝ), ∀ (E : ℝ) (u : ℤ → ℂ), IsGenEigen α lam θ E u →
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, ∀ k : ℤ, 0 ≤ k → ‖u k‖ ≤ C * Real.exp (-(c * (k : ℝ)))

end Work.TMC16Core

end
