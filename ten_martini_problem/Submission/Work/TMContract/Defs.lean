import ChallengeDeps

/-!
# Ten Martini contract: shared definitions

This file is the frozen vocabulary of the Ten Martini subproject.  It is a faithful copy
of the definitions in `Submission/Work/TMPlan/Interfaces.lean` (the lead's design; read
`Submission/Work/TMPlan/ROUTE_LEAD.md` first), with only elaboration repairs.  Nothing here
is a `sorry`: every declaration is a definition or an immediately true theorem.

Conventions (as in the design document):

* `lam` is AJ's `λ` (the challenge's `coupling`); `amoPot α lam θ n = 2 λ cos 2π(θ + nα)`.
* `EllTwo = lp (fun _ : ℤ => ℂ) 2` is the challenge's Hilbert space; the challenge predicate
  `IsAlmostMathieuOperator α λ θ H` is `amoAct` applied coordinatewise (`isAMO_iff`, `rfl`).
* `amoSpec α lam` is the real trace of the spectrum at phase `0` (a set of reals, defined
  with `∃ H` so that the definition is total).
* Angles in `rot`, `HasDegree` and `RedSet` are in *turns* (`2π` = one turn), as in AJ.
  The Prüfer lift `pruferStep` is in *half-turns* (`π` = one unit), so
  `rotLift = 2 ρ_AJ` and `ids = 1 - rotLift = N_AJ`.
* `LiouvilleAbove α b` / `DiophBelow α b` are the two one-sided formulations of AJ's
  `β ≥ b` / `β ≤ b` (AJ (4.24)); `¬ LiouvilleAbove α b ↔ DiophBelow α b`.
-/

open MeasureTheory Filter Topology Set
open LeanEval.Analysis.TenMartini

noncomputable section

namespace Work.TMContract

/-! ## 1. The operator and its spectrum -/

/-- The potential `v_n = 2 λ cos 2π(θ + nα)`, written exactly as in the challenge. -/
def amoPot (α lam θ : ℝ) (n : ℤ) : ℝ :=
  2 * lam * Real.cos (2 * Real.pi * (θ + (n : ℝ) * α))

/-- The almost Mathieu difference expression acting on arbitrary sequences
(used for formal, non-`ℓ²` solutions). -/
def amoAct (α lam θ : ℝ) (u : ℤ → ℂ) (n : ℤ) : ℂ :=
  u (n + 1) + u (n - 1) + ((amoPot α lam θ n : ℝ) : ℂ) * u n

/-- The challenge predicate is `amoAct` applied coordinatewise (by definition). -/
theorem isAMO_iff (α lam θ : ℝ) (H : EllTwo →L[ℂ] EllTwo) :
    IsAlmostMathieuOperator α lam θ H ↔
      ∀ (u : EllTwo) (n : ℤ), H u n = amoAct α lam θ (fun m => u m) n := by
  simp only [IsAlmostMathieuOperator, amoAct, amoPot]
  norm_num

/-- `Σ_{λ,α}` as a set of reals: the spectrum at phase `θ = 0`.  For irrational `α` it does
not depend on the phase (`P_OpBasics`, part 3).  DESIGN: `∃ H` (not a chosen `H`) keeps the
definition total; `P_OpBasics` gives existence, and uniqueness is immediate from the
coordinate formula. -/
def amoSpec (α lam : ℝ) : Set ℝ :=
  {E | ∃ H : EllTwo →L[ℂ] EllTwo, IsAlmostMathieuOperator α lam 0 H ∧ (E : ℂ) ∈ spectrum ℂ H}

/-- `EllTwo` is nontrivial: `δ₀` is a nonzero square-summable sequence.  This instance is
what lets `spectrum.nonempty` produce a spectral point for a bounded operator on `EllTwo`. -/
instance instNontrivialEllTwo : Nontrivial EllTwo := by
  have hmem : Memℓp (fun n : ℤ => if n = 0 then (1 : ℂ) else 0) (2 : ENNReal) := by
    refine memℓp_gen (p := (2 : ENNReal)) ?_
    apply summable_of_ne_finset_zero (s := ({0} : Finset ℤ))
    intro n hn
    rw [if_neg (by simpa using hn), norm_zero]
    exact Real.zero_rpow (by norm_num)
  refine ⟨0, ⟨fun n : ℤ => if n = 0 then (1 : ℂ) else 0, hmem⟩, ?_⟩
  intro h
  have h0 := congrArg (fun (u : EllTwo) => (u : ℤ → ℂ) 0) h
  simp at h0

/-- `S` contains a nondegenerate open interval. -/
def HasInterval (S : Set ℝ) : Prop := ∃ a b : ℝ, a < b ∧ Ioo a b ⊆ S

/-- The whole problem: `Σ_{λ,α}` has empty interior. -/
def NoInterval (α lam : ℝ) : Prop := ¬ HasInterval (amoSpec α lam)

/-- AJ (9.2): a generalized eigenfunction (a nonzero, polynomially bounded formal solution). -/
def IsGenEigen (α lam θ E : ℝ) (u : ℤ → ℂ) : Prop :=
  u ≠ 0 ∧ (∀ n : ℤ, amoAct α lam θ u n = (E : ℂ) * u n) ∧
    ∃ C : ℝ, ∀ n : ℤ, ‖u n‖ ≤ C * (1 + |(n : ℝ)|)

/-- Exponential decay of a sequence. -/
def ExpDecay (u : ℤ → ℂ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, ∀ n : ℤ, ‖u n‖ ≤ C * Real.exp (-(c * |(n : ℝ)|))

/-- For almost every phase, every generalized eigenfunction decays exponentially (this
implies Anderson localisation; it is all AJ Thm 5.1 uses). -/
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

/-- The almost Mathieu transfer matrix `S_{λ,E}(x)` (AJ (2.8)) with complex energy.
`S(θ + nα) (u_n, u_{n-1}) = (u_{n+1}, u_n)` for solutions of `H u = E u`. -/
def tmC (lam : ℝ) (E : ℂ) (x : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![E - ((2 * lam * Real.cos (2 * Real.pi * x) : ℝ) : ℂ), -1; 1, 0]

/-- `A_n(x) = S(x + (n-1)α) ⋯ S(x)` (AJ (2.2)). -/
def iterC (α lam : ℝ) (E : ℂ) : ℕ → ℝ → Matrix (Fin 2) (Fin 2) ℂ
  | 0, _ => 1
  | n + 1, x => tmC lam E (x + (n : ℝ) * α) * iterC α lam E n x

/-- Frobenius norm (any norm gives the same exponent; this one is explicit, submultiplicative,
and `≥ √2` on `SL(2,ℂ)`, so the logarithms below are `≥ 0`). -/
def frob (A : Matrix (Fin 2) (Fin 2) ℂ) : ℝ :=
  Real.sqrt (‖A 0 0‖ ^ 2 + ‖A 0 1‖ ^ 2 + ‖A 1 0‖ ^ 2 + ‖A 1 1‖ ^ 2)

/-- The Lyapunov exponent `L(E) = lim (1/n) ∫ ln ‖A_n‖ = inf_n (1/n) ∫ ln ‖A_n‖` (AJ (2.4);
subadditivity plus Fekete).  The family is bounded below by `0`, so `⨅` is meaningful. -/
def lyap (α lam : ℝ) (E : ℂ) : ℝ :=
  ⨅ n : ℕ, (∫ x in (0 : ℝ)..1, Real.log (frob (iterC α lam E (n + 1) x))) / ((n : ℝ) + 1)

/-- Real transfer matrix (real energy). -/
def tmR (lam E x : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![E - 2 * lam * Real.cos (2 * Real.pi * x), -1; 1, 0]

/-- AJ's rotation `R_c` (AJ (2.7)); `c` in turns. -/
def rot (c : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.cos (2 * Real.pi * c), -Real.sin (2 * Real.pi * c);
     Real.sin (2 * Real.pi * c), Real.cos (2 * Real.pi * c)]

/-- `B : ℝ → SL(2,ℝ)` (1-periodic in use) has degree `k`, i.e. is homotopic to `x ↦ R_{kx}`:
the first column `B(x) e₁` has a continuous angle `η` (in turns) with `η(x+1) = η(x) + k`.
(`B ↦ B e₁` is a homotopy equivalence `SL(2,ℝ) → ℝ² ∖ 0`, so this is the homotopy class.) -/
def HasDegree (B : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (k : ℤ) : Prop :=
  Continuous B ∧ ∃ η : ℝ → ℝ, Continuous η ∧ (∀ x, η (x + 1) = η x + k) ∧
    ∀ x, ∃ r : ℝ, 0 < r ∧ B x 0 0 = r * Real.cos (2 * Real.pi * η x) ∧
      B x 1 0 = r * Real.sin (2 * Real.pi * η x)

/-- AJ's set `Λ_{λ,α}` (defined just before AJ Thm 4.2): energies at which the cocycle is
analytically reducible to a constant rotation by a conjugacy homotopic to the identity. -/
def RedSet (α lam : ℝ) : Set ℝ :=
  {E | ∃ (B : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (c : ℝ),
      (∀ i j, AnalyticOnNhd ℝ (fun x => B x i j) univ) ∧ (∀ x, B (x + 1) = B x) ∧
      (∀ x, (B x).det = 1) ∧ HasDegree B 0 ∧
      ∀ x, B (x + α) * tmR lam E x = rot c * B x}

/-! ## 4. Fibered rotation number and integrated density of states -/

/-- The explicit Prüfer lift of the projective action of `[[a,-1],[1,0]]` on directions
`(cos πt, sin πt)` (see `Interfaces.lean` §4 for the derivation). -/
def pruferStep (a t : ℝ) : ℝ :=
  if t - (⌊t + 1 / 2⌋ : ℝ) = -1 / 2 then (⌊t + 1 / 2⌋ : ℝ)
  else (⌊t + 1 / 2⌋ : ℝ) + 1 / 2 +
    Real.arctan (Real.tan (Real.pi * (t - (⌊t + 1 / 2⌋ : ℝ))) - a) / Real.pi

/-- `F^n_x = F_{a(x+(n-1)α)} ∘ ⋯ ∘ F_{a(x)}`, `a(y) = E - 2λ cos 2πy`. -/
def pruferIter (α lam E : ℝ) : ℕ → ℝ → ℝ → ℝ
  | 0, _, t => t
  | n + 1, x, t =>
      pruferStep (E - 2 * lam * Real.cos (2 * Real.pi * (x + (n : ℝ) * α)))
        (pruferIter α lam E n x t)

/-- Lifted fibered rotation number in half-turns: `lim_n (1/n) ∫₀¹ F^n_x(0) dx`.  The limit
exists for every `(α, λ, E)` (almost additivity with error `≤ 1`; `P_RotBasics` part 1).
`rotLift = 2 ρ_AJ ∈ [0, 1]`. -/
def rotLift (α lam E : ℝ) : ℝ :=
  limUnder atTop (fun n : ℕ => (∫ x in (0 : ℝ)..1, pruferIter α lam E n x 0) / (n : ℝ))

/-- The integrated density of states `N_{λ,α}(E) = 1 - 2ρ_{λ,α}(E)` (AJ (2.10)). -/
def ids (α lam E : ℝ) : ℝ := 1 - rotLift α lam E

/-! ## 5. The m-function (AJ §2.3, (3.10)–(3.11)) -/

/-- Möbius action of a `2×2` matrix. -/
def mob (M : Matrix (Fin 2) (Fin 2) ℂ) (z : ℂ) : ℂ :=
  (M 0 0 * z + M 0 1) / (M 1 0 * z + M 1 1)

/-- `S(x-α) S(x-2α) ⋯ S(x-nα)`. -/
def backIterC (α lam : ℝ) (E : ℂ) : ℕ → ℝ → Matrix (Fin 2) (Fin 2) ℂ
  | 0, _ => 1
  | n + 1, x => backIterC α lam E n x * tmC lam E (x - ((n : ℝ) + 1) * α)

/-- AJ's `m(E, x) = lim_n S(x-α)⋯S(x-nα) · i` for `Im E > 0` (AJ (3.10)–(3.11)).  It satisfies
`S_E(x) · m(E,x) = m(E,x+α)`, and `m = -1/m_-` in Weyl notation.  The limit exists for
`Im E > 0`, `λ ≥ 0` (nested-disc argument of AJ Thm 3.1, proved inside C8). -/
def amoM (α lam : ℝ) (E : ℂ) (x : ℝ) : ℂ :=
  limUnder atTop (fun n : ℕ => mob (backIterC α lam E n x) Complex.I)

/-- `ℂ ∖ (ℝ ∖ (a,b))`, the domain of Kotani's continuation. -/
def kotaniDomain (a b : ℝ) : Set ℂ :=
  {z | z.im ≠ 0 ∨ (z.im = 0 ∧ a < z.re ∧ z.re < b)}

end Work.TMContract
