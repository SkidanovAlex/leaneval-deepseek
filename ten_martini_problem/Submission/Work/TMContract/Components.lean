import Submission.Work.TMContract.Defs

/-!
# Ten Martini contract: the eighteen component `Prop`s

One `def P_<C> : Prop` per component C0–C17, transcribed verbatim from the lead's
`Submission/Work/TMPlan/Interfaces.lean` §6 (proof routes in
`Submission/Work/TMPlan/ROUTE_LEAD.md` §4).  The derived case statements
`P_Beta0`, `P_Liouville`, `P_DiophSide` (Interfaces §7) are included as well, since the
glue and the satisfiability file need them.

`componentList` collects C0–C17 in order.  `derivedList` collects the derived statements.

Names and meanings are frozen; do not weaken, strengthen or "fix" a `P_*` without the lead.
-/

open MeasureTheory Filter Topology Set
open LeanEval.Analysis.TenMartini

noncomputable section

namespace Work.TMContract

/-! ## 6. Component `Prop`s (C0–C17) -/

/-- **C0** Unique ergodicity of an irrational rotation, in its uniform form (Weyl).  Shared
infrastructure for C4, C5, C6, C7, C14, C16. -/
def P_UniqErg : Prop :=
  ∀ α : ℝ, Irrational α → ∀ f : ℝ → ℝ, Continuous f → (∀ x, f (x + 1) = f x) →
    TendstoUniformly
      (fun (n : ℕ) (x : ℝ) => (∑ j ∈ Finset.range n, f (x + (j : ℝ) * α)) / (n : ℝ))
      (fun _ => ∫ x in (0 : ℝ)..1, f x) atTop

/-- **C1** Operator basics: existence, self-adjointness, phase independence of the spectrum
for irrational frequency. -/
def P_OpBasics : Prop :=
  (∀ α lam θ : ℝ, ∃ H : EllTwo →L[ℂ] EllTwo, IsAlmostMathieuOperator α lam θ H) ∧
  (∀ (α lam θ : ℝ) (H : EllTwo →L[ℂ] EllTwo),
      IsAlmostMathieuOperator α lam θ H → IsSelfAdjoint H) ∧
  (∀ α lam θ θ' : ℝ, Irrational α → ∀ H H' : EllTwo →L[ℂ] EllTwo,
      IsAlmostMathieuOperator α lam θ H → IsAlmostMathieuOperator α lam θ' H' →
      spectrum ℂ H = spectrum ℂ H')

/-- **C2** No isolated points (audit §2; CFC projection, simplicity, covariance averaging). -/
def P_Perfect : Prop :=
  ∀ α lam θ : ℝ, Irrational α → ∀ H : EllTwo →L[ℂ] EllTwo,
    IsAlmostMathieuOperator α lam θ H → Perfect (spectrum ℂ H)

/-- **C3** Aubry duality for spectra, `Σ_λ = λ Σ_{1/λ}` (AJ §1.1). -/
def P_Duality : Prop :=
  ∀ α lam : ℝ, Irrational α → lam ≠ 0 → ∀ E : ℝ, E ∈ amoSpec α lam ↔ E / lam ∈ amoSpec α lam⁻¹

/-- **C4** Herman's bound (AJ §9, [H]; any `α`, any complex `E`) and the locally uniform
upper bound (Furman [Fur], AJ (9.7)) for irrational `α`. -/
def P_LEBasics : Prop :=
  (∀ (α lam : ℝ) (E : ℂ), Real.log |lam| ≤ lyap α lam E) ∧
  (∀ α lam : ℝ, Irrational α → ∀ (E₀ : ℂ) (ε : ℝ), 0 < ε →
      ∃ r : ℝ, 0 < r ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ E : ℂ, ‖E - E₀‖ < r → ∀ x : ℝ,
        Real.log (frob (iterC α lam E n x)) ≤ (n : ℝ) * (lyap α lam E₀ + ε))

/-- **C5** Rotation number basics (AJ §2.1–2.2). -/
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

/-- **C6** Every point of the spectrum is a point of increase of `N` (AJ (2.11)). -/
def P_IDSSpectrum : Prop :=
  ∀ α lam : ℝ, Irrational α → ∀ E ∈ amoSpec α lam, ∀ ε : ℝ, 0 < ε →
    ids α lam (E - ε) < ids α lam (E + ε)

/-- **C7** Bourgain–Jitomirskaya (AJ Thm 2.1 = [BJ] Cor. 2). -/
def P_BJ : Prop :=
  ∀ α lam : ℝ, Irrational α → lam ≠ 0 → ∀ E ∈ amoSpec α lam,
    lyap α lam (E : ℂ) = max 0 (Real.log |lam|)

/-- **C8** Kotani theory (AJ Thm 2.2).  Stated for `λ ≥ 0` so that the free case `λ = 0`
(`L = 0` on `(-2,2)`) is a genuine instance; for `λ ≠ 0` the hypothesis is AJ's fictitious
one. -/
def P_Kotani : Prop :=
  ∀ α lam a b : ℝ, Irrational α → 0 ≤ lam → a < b →
    (∀ E ∈ Ioo a b, lyap α lam (E : ℂ) = 0) →
    ∃ M : ℂ → ℝ → ℂ,
      ContinuousOn (fun p : ℂ × ℝ => M p.1 p.2) (kotaniDomain a b ×ˢ univ) ∧
      (∀ x : ℝ, DifferentiableOn ℂ (fun z => M z x) (kotaniDomain a b)) ∧
      (∀ z ∈ kotaniDomain a b, ∀ x : ℝ, 0 < (M z x).im) ∧
      (∀ z : ℂ, 0 < z.im → ∀ x : ℝ, M z x = amoM α lam z x) ∧
      (∀ (z : ℂ) (x : ℝ), M z (x + 1) = M z x)

/-- **C9** Analytic conjugacy to rotations on a spectral interval (AJ Thm 3.1, Thm 3.2,
Lemma 2.3 (open-set case), and (4.11)–(4.13)). -/
def P_mAnalytic : Prop :=
  ∀ α lam a b : ℝ, Irrational α → 0 < lam → lam ≤ 1 → a < b → Ioo a b ⊆ amoSpec α lam →
    ∃ (C : ℝ → ℝ → Matrix (Fin 2) (Fin 2) ℝ) (φ : ℝ → ℝ → ℝ),
      (∀ i j, AnalyticOnNhd ℝ (fun p : ℝ × ℝ => C p.1 p.2 i j) (Ioo a b ×ˢ univ)) ∧
      AnalyticOnNhd ℝ (fun p : ℝ × ℝ => φ p.1 p.2) (Ioo a b ×ˢ univ) ∧
      (∀ E x, C E (x + 1) = C E x) ∧ (∀ E x, φ E (x + 1) = φ E x) ∧
      (∀ E ∈ Ioo a b, ∀ x, (C E x).det = 1) ∧
      (∀ E ∈ Ioo a b, HasDegree (C E) 0) ∧
      (∀ E ∈ Ioo a b, ∀ x, C E (x + α) * tmR lam E x = rot (φ E x) * C E x)

/-- **C10** Real-line Cartan lemma (replaces AJ §2.4 polar-set properties (1), (3), (4)). -/
def P_RealCartan : Prop :=
  ∀ (U : Set ℂ), IsOpen U → ∀ (f : ℕ → ℂ → ℂ) (w s : ℕ → ℝ),
    (∀ k, DifferentiableOn ℂ (f k) U) → (∀ k, 0 < w k) → (∀ k, 0 < s k) →
    (∀ K ⊆ U, IsCompact K → ∃ M : ℝ, ∀ k, ∀ z ∈ K, ‖f k z‖ ≤ w k * Real.exp (M * s k)) →
    volume {x : ℝ | (x : ℂ) ∈ U ∧
        ∃ η : ℝ, 0 < η ∧ ∀ᶠ k in atTop, ‖f k x‖ ≤ w k * Real.exp (-(η * s k))} = 0 ∨
      ∃ c d : ℝ, c < d ∧ Ioo c d ⊆ {x : ℝ | (x : ℂ) ∈ U ∧
        ∃ η : ℝ, 0 < η ∧ ∀ᶠ k in atTop, ‖f k x‖ ≤ w k * Real.exp (-(η * s k))}

/-- **C11** AJ Lemma 4.1 plus Thm 4.2. -/
def P_Reducibility : Prop :=
  (∀ α : ℝ, Irrational α → (∀ b : ℝ, 0 < b → DiophBelow α b) →
      ∀ lam : ℝ, 0 < lam → lam ≤ 1 → ∀ a b : ℝ, a < b → Ioo a b ⊆ amoSpec α lam →
        Ioo a b ⊆ RedSet α lam) ∧
  (∀ α b₀ : ℝ, Irrational α → DiophBelow α b₀ →
      ∀ lam : ℝ, 0 < lam → lam ≤ 1 → ∀ a b : ℝ, a < b → Ioo a b ⊆ amoSpec α lam →
        volume (RedSet α lam ∩ Ioo a b) = 0 ∨
          ∃ c d : ℝ, c < d ∧ Ioo c d ⊆ RedSet α lam ∩ Ioo a b)

/-- **C12** AJ Lemma 4.3 (Puig's argument): `Λ` contains no spectral interval. -/
def P_Puig : Prop :=
  ∀ α lam : ℝ, Irrational α → 0 < lam → lam ≤ 1 → ∀ c d : ℝ, c < d →
    Ioo c d ⊆ amoSpec α lam → ¬ Ioo c d ⊆ RedSet α lam

/-- **C13** AJ Thm 6.1 ("fictitious" Lipschitz continuity of `N` in `α`). -/
def P_FictLip : Prop :=
  ∀ α lam a b : ℝ, Irrational α → 0 < lam → lam ≤ 1 → a < b → Ioo a b ⊆ amoSpec α lam →
    ∀ c d : ℝ, a < c → d < b → ∃ K : ℝ, ∀ α' E : ℝ, E ∈ Icc c d →
      |ids α' lam E - ids α lam E| ≤ K * |α' - α|

/-- **C14** Large flat pieces of `N_{p/q}` inside a spectral interval (AJ Lemma 7.1 +
Thm 7.2 in the form used in the proof of Thm 8.1(2)). -/
def P_GapBound : Prop :=
  ∀ α lam c d : ℝ, Irrational α → 0 < lam → lam ≤ 1 → c < d → Icc c d ⊆ amoSpec α lam →
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∃ Q : ℕ, ∀ (p : ℤ) (q : ℕ), Q ≤ q →
      |α - (p : ℝ) / (q : ℝ)| < δ / (q : ℝ) →
      ∃ a' b' : ℝ, c ≤ a' ∧ a' < b' ∧ b' ≤ d ∧
        Real.exp (-(ε * q)) * lam ^ ((q : ℝ) / 2) ≤ b' - a' ∧
        ids ((p : ℝ) / (q : ℝ)) lam a' = ids ((p : ℝ) / (q : ℝ)) lam b'

/-- **C15** Weak Schnol: every spectral point is a limit of generalized eigenvalues. -/
def P_Schnol : Prop :=
  ∀ (α lam θ : ℝ) (H : EllTwo →L[ℂ] EllTwo), IsAlmostMathieuOperator α lam θ H →
    ∀ E₀ : ℝ, (E₀ : ℂ) ∈ spectrum ℂ H → ∀ δ : ℝ, 0 < δ →
      ∃ E : ℝ, |E - E₀| < δ ∧ ∃ u : ℤ → ℂ, IsGenEigen α lam θ E u

/-- **C16** Anderson localisation for `λ > e^{16β/9}` (AJ Thm 5.2 = Thm 9.1, §9). -/
def P_Loc : Prop :=
  ∀ α b₀ lam : ℝ, Irrational α → 0 ≤ b₀ → DiophBelow α b₀ →
    Real.exp (16 * b₀ / 9) < lam → ExpLocAE α lam

/-- **C17** Localisation implies Cantor spectrum (AJ Thm 5.1). -/
def P_LocCantor : Prop :=
  ∀ α b₀ lam : ℝ, Irrational α → DiophBelow α b₀ → 1 ≤ lam → ExpLocAE α lam →
    NoInterval α lam

/-! ## 7. Derived case statements (ROUTE_LEAD §7; proved from the components by the glue
theorems in `Glue.lean`) -/

/-- AJ Remark 4.1: `β = 0`, `0 < λ ≤ 1`. -/
def P_Beta0 : Prop :=
  ∀ α : ℝ, Irrational α → (∀ b : ℝ, 0 < b → DiophBelow α b) →
    ∀ lam : ℝ, 0 < lam → lam ≤ 1 → NoInterval α lam

/-- AJ Thm 8.1(2): `e^{-2β} < λ ≤ 1` (includes `β = ∞`). -/
def P_Liouville : Prop :=
  ∀ α b lam : ℝ, Irrational α → LiouvilleAbove α b → Real.exp (-(2 * b)) < lam → lam ≤ 1 →
    NoInterval α lam

/-- AJ Thm 8.1(1): `β < ∞`, `λ > e^{16β/9}`. -/
def P_DiophSide : Prop :=
  ∀ α b lam : ℝ, Irrational α → 0 ≤ b → DiophBelow α b → Real.exp (16 * b / 9) < lam →
    NoInterval α lam

/-! ## 8. The `P_*` index table (documentation only; see the `def`s above). -/

/-- The list of the eighteen component `Prop`s, in the order C0–C17. -/
def componentList : List Prop :=
  [P_UniqErg, P_OpBasics, P_Perfect, P_Duality, P_LEBasics, P_RotBasics, P_IDSSpectrum,
   P_BJ, P_Kotani, P_mAnalytic, P_RealCartan, P_Reducibility, P_Puig, P_FictLip, P_GapBound,
   P_Schnol, P_Loc, P_LocCantor]

/-- The three derived case statements (Interfaces §7). -/
def derivedList : List Prop := [P_Beta0, P_Liouville, P_DiophSide]

/-- The `P_*` that are *fictitious* by design: each assumes a nondegenerate interval inside
the spectrum `Σ_{λ,α}` with `0 < λ ≤ 1`.  By the Ten Martini theorem no such interval
exists, so these hypotheses are not satisfiable; that is intentional (AJ's fictitious
results, `ROUTE_LEAD.md` §6) and is documented in `Satisfiability.lean` and `README.md`.
The definitions are kept because the proof of the theorem *reasons from* them. -/
def fictitiousList : List Prop := [P_mAnalytic, P_Reducibility, P_Puig, P_FictLip, P_GapBound]

end Work.TMContract
