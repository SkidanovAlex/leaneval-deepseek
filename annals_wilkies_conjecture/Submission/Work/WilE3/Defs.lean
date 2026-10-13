/-
  annals_wilkies_conjecture, AREA E3 (`Submission.Work.WilE3`): multiplicity theory for
  exp-affine (EA) systems.

  This file fixes the vocabulary of area E3, i.e. of the holes `WilkiesDesign.E.E3_identity`
  and `WilkiesDesign.E.E3_taylor_closure` of `Submission/Work/Wilkies/E/Spec.lean`.

  The vocabulary has four layers.

  §1.  The *effectively smooth* data of GV survey Def. 4.6 / Cor. 4.7: `h : Fin j → EAPoly k r`
       with `h(x) = 0` and `det(∂_{ι b} h_a)(x) ≠ 0` (`EffSmooth`), the Jacobian determinant
       `jacDet c h ι` (`Δ`), the ordered reduced derivatives `opMono` (already in the frozen
       vocabulary) and the linear system `ReducedVanish ... N` of E3a's hypothesis.

  §2.  The complexified chain `eaEvalC`: the same EA polynomial evaluated at a complex point,
       with the chain functions `exp (∑ a_{ji} z_i + b_j)`.  The frozen derivative operators
       `eaD`, `detOp`, `opMono` are polynomial identities with real coefficients, so they are
       also the correct complex derivative operators (that is the content of `Basic.lean`'s
       complex correctness lemmas).

  §3.  `MultiplicityBound`: Khovanskii's degree bound for the *nondegenerate complex zeros* of a
       complexified EA system, i.e. Gabrielov's multiplicity bound (GV survey Thm. 4.3) in the
       form the realified-complex-system route of DESIGN §2 E3 delivers.  This is the analytic
       input of E3a and is stated here, not proved here.

  §4.  The Taylor-closure vocabulary of E3b: `taylorSet` (GV Cor. 4.5's `X_y`, which is the
       right-hand side of `E3_taylor_closure`) and the Łojasiewicz inequality `HasLoj` with an
       explicit exponent (GV Cor. 4.4).

  Conventions.  `opMono c h ι m f` is `∂_{h,ι,k-1}^{m (k-1)} ⋯ ∂_{h,ι,0}^{m 0} f`; the
  hypothesis of E3a involves only the multi-indices `m` with `m (ι a) = 0` for all `a`.
  `ReducedVanish c h ι x f N` says that all of these of order `< N` vanish at `x`, so E3a's
  hypothesis `∑ l, m l ≤ M.eval d` is `ReducedVanish c h ι x f (M.eval d + 1)`.
-/
import Submission.Work.Wilkies.E.Spec
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.MetricSpace.HausdorffDistance

set_option autoImplicit false
noncomputable section
open Classical Topology Filter
namespace Work.WilE3
open WilkiesConjecture WilkiesDesign WilkiesDesign.E

/-! ## §1. Effectively smooth EA data -/

/-- `Δ = det (∂_{ι b} h_a)`: the `ι`-Jacobian determinant of `h` (the matrix of GV Def. 4.6
without the `f` row).  `EffSmooth` says `Δ (x) ≠ 0`, and then the `k - j` operators
`detOp c h ι l` (`l ∉ range ι`) have linearly independent symbols which span the tangent space
of `{h = 0}` at `x`: they are its tangential frame. -/
def jacDet {k r j : ℕ} (c : EAChain k r) (h : Fin j → EAPoly k r)
    (ι : Fin j → Fin k) : EAPoly k r :=
  Matrix.det (Matrix.of fun a b => eaD c (ι b) (h a))

/-- The cofactor of `∂_{ι b} h_a` in the expansion of `detOp c h ι l f` along its last row: the
determinant of the matrix obtained from the `detOp` matrix by deleting the `f` row and the `b`-th
column.  With this, `detOp` expands as `Δ · ∂_l f + ∑ b, (±1) (∂_{ι b} f) · detCof b`, i.e.
`detOp` is a first-order differential operator whose coefficient of `∂_l` is `Δ`. -/
def detCof {k r j : ℕ} (c : EAChain k r) (h : Fin j → EAPoly k r) (ι : Fin j → Fin k)
    (l : Fin k) (b : Fin j) : EAPoly k r :=
  Matrix.det (Matrix.of fun (a b' : Fin j) =>
    eaD c (Fin.lastCases l ι ((Fin.castSucc b).succAbove b')) (h a))

/-- The hypotheses of E3a at `x`: `h (x) = 0` and the `ι`-Jacobian of `h` is invertible at `x`
(GV Cor. 4.7).  Note that if `ι` is not injective, or `j > k`, the second condition is
unsatisfiable, and E3a holds vacuously. -/
def EffSmooth {k r j : ℕ} (c : EAChain k r) (h : Fin j → EAPoly k r) (ι : Fin j → Fin k)
    (x : Fin k → ℝ) : Prop :=
  (∀ a, eaEval c (h a) x = 0) ∧
    (Matrix.of fun a b => eaEval c (eaD c (ι b) (h a)) x).det ≠ 0

/-! ## §2. The ordered reduced derivative system -/

/-- `ReducedVanish c h ι x f N`: every ordered reduced derivative of `f` of order `< N` vanishes
at `x`.  This is the hypothesis of E3a at order `N`. -/
def ReducedVanish {k r j : ℕ} (c : EAChain k r) (h : Fin j → EAPoly k r) (ι : Fin j → Fin k)
    (x : Fin k → ℝ) (f : EAPoly k r) (N : ℕ) : Prop :=
  ∀ m : Fin k → ℕ, (∀ a, m (ι a) = 0) → (∑ l, m l) < N → eaEval c (opMono c h ι m f) x = 0

/-- The conclusion of E3a: `f` vanishes identically on `{h = 0}` in a neighbourhood of `x`. -/
def VanishesOnNear {k r j : ℕ} (c : EAChain k r) (h : Fin j → EAPoly k r)
    (x : Fin k → ℝ) (f : EAPoly k r) : Prop :=
  ∀ᶠ y in 𝓝 x, (∀ a, eaEval c (h a) y = 0) → eaEval c f y = 0

/-! ## §3. The complexified chain and Gabrielov's multiplicity bound -/

/-- Evaluation of an EA polynomial at a complex point, with the complexified chain
`z ↦ exp (∑ i, a_{ji} z_i + b_j)`.  The frozen operators `eaD`, `detOp`, `opMono` are unchanged:
they are the correct complex derivative operators (`Basic.lean`). -/
def eaEvalC {k r : ℕ} (c : EAChain k r) (Q : EAPoly k r) (z : Fin k → ℂ) : ℂ :=
  MvPolynomial.eval₂ (algebraMap ℝ ℂ)
    (Sum.elim z fun j => Complex.exp (∑ i, (c.a j i : ℂ) * z i + (c.b j : ℂ))) Q

/-- The set of nondegenerate complex zeros of a complexified EA system `f`, i.e. of a finite
`s` all of whose points are zeros at which the complex Jacobian `(∂_j f_i)` is invertible. -/
def IsNondegZero {k r : ℕ} (c : EAChain k r) (f : Fin k → EAPoly k r)
    (s : Finset (Fin k → ℂ)) : Prop :=
  ∀ z ∈ s, (∀ i, eaEvalC c (f i) z = 0) ∧
    (Matrix.of fun i j => eaEvalC c (eaD c j (f i)) z).det ≠ 0

/-- **Khovanskii's bound for the complexified EA chain** = Gabrielov's multiplicity bound
(GV survey Thm. 4.3, from Gabrielov, Selecta Math. 1 (1995)), in the form the E3a route consumes:

the number of nondegenerate complex zeros of a perturbation `f + ε • g` of an EA system `f` which
*converge to* `x` as `ε → 0` is bounded by a polynomial in the degrees, uniformly in the chain.

"Converge to `x`" is made precise by letting the ball shrink: for every `ρ : ℂ → ℝ` with
`ρ ε → 0` as `ε → 0`, eventually in `ε ≠ 0` the `ρ ε`-ball around `x` contains at most
`M.eval (degrees)` nondegenerate zeros of `f + ε • g`.  Both weakenings are forced by the
mathematics and were found by counterexample:

* the **global** count is unbounded (`z ↦ z - e ^ z`, i.e. `k = r = 1`, `f 0 = X (Sum.inl 0) -
  X (Sum.inr 0)`, `a 0 0 = 1`, has the infinitely many simple zeros `-W_k (-1)`, `k ∈ ℤ`);
* a **fixed ball** is not enough either, because the bound must be uniform in the chain
  *coefficients*: `z - e ^ {a z}` (`f 0 = X (Sum.inl 0) - X (Sum.inr 0)`, `a 0 0 = a`) has the
  simple zeros `≈ 2 π i n / a`, so its unit ball carries `≈ a / π` of them while its degree (2) and
  format are fixed.  Both facts are consistent with GV Thm. 4.3, whose quantity is the
  *multiplicity at a point*, not a count in a ball.

This is the analytic input of `E3_identity`; it is *not* proved in this file.  Its proof is the
realification of `NOTES.md` §3/§5′ followed by Khovanskii's bound for separable chains (an internal
lemma of area E2, needed here in the local form `Work.WilE3.SepKhovanskiiLocal` of `Sep.lean`,
because `Real.tan` has poles and E2's `SepChain` requires a global derivative relation): the
half-angle chart `t_j = tan ((Im ℓ_j (z))/2)` is periodic with period `2π` in `Im ℓ_j (z)`, so the
zeros converging to `x` lie in a *shrinking* ball, over finitely many charts once the ball is small
enough — which is exactly why the radius has to shrink. -/
def MultiplicityBound : Prop :=
  ∀ F : ℕ, ∃ M : Polynomial ℕ, ∀ (k r : ℕ) (c : EAChain k r) (f g : Fin k → EAPoly k r)
      (x : Fin k → ℂ) (ρ : ℂ → ℝ),
    k + r ≤ F → (∀ i, eaEvalC c (f i) x = 0) → (∀ ε, 0 < ρ ε) →
      Tendsto ρ (𝓝[≠] (0 : ℂ)) (𝓝 0) →
    ∀ᶠ ε in 𝓝[≠] (0 : ℂ), ∀ s : Finset (Fin k → ℂ),
      (∀ z ∈ s, (∀ i, eaEvalC c (f i) z + ε * eaEvalC c (g i) z = 0) ∧
        (Matrix.of fun i j =>
          eaEvalC c (eaD c j (f i)) z + ε * eaEvalC c (eaD c j (g i)) z).det ≠ 0) →
      (∀ z ∈ s, ‖z - x‖ < ρ ε) →
      s.card ≤ M.eval (∑ i, atomDeg (f i) + ∑ i, atomDeg (g i))

/-! ## §4. The Taylor-closure vocabulary of E3b -/

/-- The semialgebraic Taylor set of GV Cor. 4.5 at `y` of order `κ`: the right-hand side of
`E3_taylor_closure`.  Its equations use the degree `κ ^ 2` Taylor polynomial of each equation
and the degree `κ` Taylor polynomial of each strict inequality. -/
def taylorSet {k r : ℕ} (c : EAChain k r) (B : Basic k r) (y : Fin k → ℝ) (κ : ℕ) :
    Set (Fin k → ℝ) :=
  {x | (∀ f ∈ B.eqs, |eaTaylor c f (κ ^ 2) y x| ≤ dist x y ^ (κ ^ 2)) ∧
       (∀ g ∈ B.pos, dist x y ^ κ < eaTaylor c g κ y x)}

/-- The Łojasiewicz inequality with exponent `q` on a neighbourhood of `Z`, at `x`
(GV survey Cor. 4.4): there is `C > 0` with `C · dist (·, Z) ^ q ≤ |F|` near `x`. -/
def HasLoj {n : ℕ} (F : (Fin n → ℝ) → ℝ) (Z : Set (Fin n → ℝ)) (x : Fin n → ℝ)
    (q : ℕ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ᶠ y in 𝓝 x, C * Metric.infDist y Z ^ q ≤ |F y|

end Work.WilE3
