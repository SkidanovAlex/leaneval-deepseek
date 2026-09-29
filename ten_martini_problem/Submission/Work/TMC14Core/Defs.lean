import ChallengeDeps

/-!
# TMC14Core: local copies of the TMPlan interface definitions

Local, verbatim copies of the definitions of `Submission/Work/TMPlan/Interfaces.lean`
that component C14 (`P_GapBound`) needs, so that this subproject builds standalone.
Names and argument order are kept identical; the namespace is `Work.TMC14Core`
instead of `TMPlan`.  When `Submission/Work/TMContract/` freezes `Interfaces.lean`,
a bridge is a matter of re-stating with the frozen names.

Nothing here is modified relative to `Interfaces.lean`.
-/

open MeasureTheory Filter Topology Set
open LeanEval.Analysis.TenMartini

noncomputable section

namespace Work.TMC14Core

/-! ## 1. The operator and its spectrum -/

/-- The potential `v_n = 2 λ cos 2π(θ + nα)`, written exactly as in the challenge. -/
def amoPot (α lam θ : ℝ) (n : ℤ) : ℝ :=
  2 * lam * Real.cos (2 * Real.pi * (θ + (n : ℝ) * α))

/-- The almost Mathieu difference expression acting on arbitrary sequences. -/
def amoAct (α lam θ : ℝ) (u : ℤ → ℂ) (n : ℤ) : ℂ :=
  u (n + 1) + u (n - 1) + ((amoPot α lam θ n : ℝ) : ℂ) * u n

/-- The challenge predicate is `amoAct` applied coordinatewise (definitional).
NOTE (deviation): `Interfaces.lean` records this as `Iff.rfl`; the two sides are equal
only up to the coercion `↑(2 * λ * cos _) = 2 * ↑λ * ↑(cos _)`, so `rfl` does not
elaborate.  The statement is true; only the proof differs. -/
theorem isAMO_iff (α lam θ : ℝ) (H : EllTwo →L[ℂ] EllTwo) :
    IsAlmostMathieuOperator α lam θ H ↔
      ∀ (u : EllTwo) (n : ℤ), H u n = amoAct α lam θ (fun m => u m) n := by
  simp only [IsAlmostMathieuOperator, amoAct, amoPot]
  constructor <;> intro h u n <;> specialize h u n
  · rw [h]; push_cast; ring
  · rw [h]; push_cast; ring

/-- `Σ_{λ,α}` as a set of reals: the spectrum at phase `θ = 0`. -/
def amoSpec (α lam : ℝ) : Set ℝ :=
  {E | ∃ H : EllTwo →L[ℂ] EllTwo, IsAlmostMathieuOperator α lam 0 H ∧ (E : ℂ) ∈ spectrum ℂ H}

/-- `S` contains a nondegenerate open interval. -/
def HasInterval (S : Set ℝ) : Prop := ∃ a b : ℝ, a < b ∧ Ioo a b ⊆ S

/-- The whole problem: `Σ_{λ,α}` has empty interior. -/
def NoInterval (α lam : ℝ) : Prop := ¬ HasInterval (amoSpec α lam)

/-- AJ (9.2): a generalized eigenfunction. -/
def IsGenEigen (α lam θ E : ℝ) (u : ℤ → ℂ) : Prop :=
  u ≠ 0 ∧ (∀ n : ℤ, amoAct α lam θ u n = (E : ℂ) * u n) ∧
    ∃ C : ℝ, ∀ n : ℤ, ‖u n‖ ≤ C * (1 + |(n : ℝ)|)

/-- Exponential decay of a sequence. -/
def ExpDecay (u : ℤ → ℂ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, ∀ n : ℤ, ‖u n‖ ≤ C * Real.exp (-(c * |(n : ℝ)|))

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

/-- The Lyapunov exponent. -/
def lyap (α lam : ℝ) (E : ℂ) : ℝ :=
  ⨅ n : ℕ, (∫ x in (0 : ℝ)..1, Real.log (frob (iterC α lam E (n + 1) x))) / ((n : ℝ) + 1)

/-- Real transfer matrix (real energy). -/
def tmR (lam E x : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![E - 2 * lam * Real.cos (2 * Real.pi * x), -1; 1, 0]

/-- AJ's rotation `R_c` (AJ (2.7)); `c` in turns. -/
def rot (c : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.cos (2 * Real.pi * c), -Real.sin (2 * Real.pi * c);
     Real.sin (2 * Real.pi * c), Real.cos (2 * Real.pi * c)]

/-- `B : ℝ → SL(2,ℝ)` has degree `k`. -/
def HasDegree (B : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (k : ℤ) : Prop :=
  Continuous B ∧ ∃ η : ℝ → ℝ, Continuous η ∧ (∀ x, η (x + 1) = η x + k) ∧
    ∀ x, ∃ r : ℝ, 0 < r ∧ B x 0 0 = r * Real.cos (2 * Real.pi * η x) ∧
      B x 1 0 = r * Real.sin (2 * Real.pi * η x)

/-- AJ's set `Λ_{λ,α}`. -/
def RedSet (α lam : ℝ) : Set ℝ :=
  {E | ∃ (B : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (c : ℝ),
      (∀ i j, AnalyticOnNhd ℝ (fun x => B x i j) univ) ∧ (∀ x, B (x + 1) = B x) ∧
      (∀ x, (B x).det = 1) ∧ HasDegree B 0 ∧
      ∀ x, B (x + α) * tmR lam E x = rot c * B x}

/-! ## 4. Fibered rotation number and integrated density of states -/

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

/-- Lifted fibered rotation number in half-turns. -/
def rotLift (α lam E : ℝ) : ℝ :=
  limUnder atTop (fun n : ℕ => (∫ x in (0 : ℝ)..1, pruferIter α lam E n x 0) / (n : ℝ))

/-- The integrated density of states `N_{λ,α}(E) = 1 - 2ρ_{λ,α}(E)` (AJ (2.10)). -/
def ids (α lam E : ℝ) : ℝ := 1 - rotLift α lam E

/-! ## 5. The m-function (unused here, kept for a faithful copy) -/

/-- Möbius action of a `2×2` matrix. -/
def mob (M : Matrix (Fin 2) (Fin 2) ℂ) (z : ℂ) : ℂ :=
  (M 0 0 * z + M 0 1) / (M 1 0 * z + M 1 1)

/-- `S(x-α) S(x-2α) ⋯ S(x-nα)`. -/
def backIterC (α lam : ℝ) (E : ℂ) : ℕ → ℝ → Matrix (Fin 2) (Fin 2) ℂ
  | 0, _ => 1
  | n + 1, x => backIterC α lam E n x * tmC lam E (x - ((n : ℝ) + 1) * α)

/-- AJ's `m(E, x)`. -/
def amoM (α lam : ℝ) (E : ℂ) (x : ℝ) : ℂ :=
  limUnder atTop (fun n : ℕ => mob (backIterC α lam E n x) Complex.I)

/-- `ℂ ∖ (ℝ ∖ (a,b))`. -/
def kotaniDomain (a b : ℝ) : Set ℂ :=
  {z | z.im ≠ 0 ∨ (z.im = 0 ∧ a < z.re ∧ z.re < b)}

/-! ## 6. Component `Prop`s (verbatim from Interfaces) -/

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

def P_RealCartan : Prop :=
  ∀ (U : Set ℂ), IsOpen U → ∀ (f : ℕ → ℂ → ℂ) (w s : ℕ → ℝ),
    (∀ k, DifferentiableOn ℂ (f k) U) → (∀ k, 0 < w k) → (∀ k, 0 < s k) →
    (∀ K ⊆ U, IsCompact K → ∃ M : ℝ, ∀ k, ∀ z ∈ K, ‖f k z‖ ≤ w k * Real.exp (M * s k)) →
    volume {x : ℝ | (x : ℂ) ∈ U ∧
        ∃ η : ℝ, 0 < η ∧ ∀ᶠ k in atTop, ‖f k x‖ ≤ w k * Real.exp (-(η * s k))} = 0 ∨
      ∃ c d : ℝ, c < d ∧ Ioo c d ⊆ {x : ℝ | (x : ℂ) ∈ U ∧
        ∃ η : ℝ, 0 < η ∧ ∀ᶠ k in atTop, ‖f k x‖ ≤ w k * Real.exp (-(η * s k))}

def P_Reducibility : Prop :=
  (∀ α : ℝ, Irrational α → (∀ b : ℝ, 0 < b → DiophBelow α b) →
      ∀ lam : ℝ, 0 < lam → lam ≤ 1 → ∀ a b : ℝ, a < b → Ioo a b ⊆ amoSpec α lam →
        Ioo a b ⊆ RedSet α lam) ∧
  (∀ α b₀ : ℝ, Irrational α → DiophBelow α b₀ →
      ∀ lam : ℝ, 0 < lam → lam ≤ 1 → ∀ a b : ℝ, a < b → Ioo a b ⊆ amoSpec α lam →
        volume (RedSet α lam ∩ Ioo a b) = 0 ∨
          ∃ c d : ℝ, c < d ∧ Ioo c d ⊆ RedSet α lam ∩ Ioo a b)

def P_Puig : Prop :=
  ∀ α lam : ℝ, Irrational α → 0 < lam → lam ≤ 1 → ∀ c d : ℝ, c < d →
    Ioo c d ⊆ amoSpec α lam → ¬ Ioo c d ⊆ RedSet α lam

def P_FictLip : Prop :=
  ∀ α lam a b : ℝ, Irrational α → 0 < lam → lam ≤ 1 → a < b → Ioo a b ⊆ amoSpec α lam →
    ∀ c d : ℝ, a < c → d < b → ∃ K : ℝ, ∀ α' E : ℝ, E ∈ Icc c d →
      |ids α' lam E - ids α lam E| ≤ K * |α' - α|

/-- **C14** Large flat pieces of `N_{p/q}` inside a spectral interval. -/
def P_GapBound : Prop :=
  ∀ α lam c d : ℝ, Irrational α → 0 < lam → lam ≤ 1 → c < d → Icc c d ⊆ amoSpec α lam →
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∃ Q : ℕ, ∀ (p : ℤ) (q : ℕ), Q ≤ q →
      |α - (p : ℝ) / (q : ℝ)| < δ / (q : ℝ) →
      ∃ a' b' : ℝ, c ≤ a' ∧ a' < b' ∧ b' ≤ d ∧
        Real.exp (-(ε * q)) * lam ^ ((q : ℝ) / 2) ≤ b' - a' ∧
        ids ((p : ℝ) / (q : ℝ)) lam a' = ids ((p : ℝ) / (q : ℝ)) lam b'

def P_Schnol : Prop :=
  ∀ (α lam θ : ℝ) (H : EllTwo →L[ℂ] EllTwo), IsAlmostMathieuOperator α lam θ H →
    ∀ E₀ : ℝ, (E₀ : ℂ) ∈ spectrum ℂ H → ∀ δ : ℝ, 0 < δ →
      ∃ E : ℝ, |E - E₀| < δ ∧ ∃ u : ℤ → ℂ, IsGenEigen α lam θ E u

def P_Loc : Prop :=
  ∀ α b₀ lam : ℝ, Irrational α → 0 ≤ b₀ → DiophBelow α b₀ →
    Real.exp (16 * b₀ / 9) < lam → ExpLocAE α lam

def P_LocCantor : Prop :=
  ∀ α b₀ lam : ℝ, Irrational α → DiophBelow α b₀ → 1 ≤ lam → ExpLocAE α lam →
    NoInterval α lam

/-! ## 7. Derived case statements -/

def P_Beta0 : Prop :=
  ∀ α : ℝ, Irrational α → (∀ b : ℝ, 0 < b → DiophBelow α b) →
    ∀ lam : ℝ, 0 < lam → lam ≤ 1 → NoInterval α lam

def P_Liouville : Prop :=
  ∀ α b lam : ℝ, Irrational α → LiouvilleAbove α b → Real.exp (-(2 * b)) < lam → lam ≤ 1 →
    NoInterval α lam

def P_DiophSide : Prop :=
  ∀ α b lam : ℝ, Irrational α → 0 ≤ b → DiophBelow α b → Real.exp (16 * b / 9) < lam →
    NoInterval α lam

end Work.TMC14Core
