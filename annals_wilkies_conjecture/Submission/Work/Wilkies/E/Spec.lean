/-
  annals_wilkies_conjecture, AREA E: sub-area interface statements
  (curric-46 E-design, 2026-10-08). Design text: the E-design report (lead to file it); sources in cbc/wilkiesE-src/.

  This file type-checks on 18.221 against the frozen `Submission.Work.Wilkies.Defs` (v4.35.0-rc3).
  Run it from the workspace dir with
    systemd-run --user --scope -q -p MemoryMax=12G -p CPUQuota=200% timeout 1200 lake env lean <file>
  Only the hole `sorry`s give warnings.

  Wiring that is PROVED in this file, modulo the holes:
    * `E_instance_from_parts` : the frozen `E_instance` statement, from E8_comps, E8_sharpCD, E9_sharpDeriv, E8_boxZero
    * `E0_from_parts`         : the frozen `E0_rexp_complement` statement, from E10a, E7_subpf_compl, E10b

  Sub-areas and their holes:
    E.V   vocabulary (this file, §0)                                lead-owned, frozen
    E1    E1_bezout              nondegenerate real zeros of polynomial systems
    E2    E2_khovanskii, E2_components                Khovanskii for exp-affine (EA) chains
    E3    E3_identity, E3_taylor_closure               Gabrielov multiplicity: bounded order + Taylor closure
    E4    E4_sa_fiber_closure     effective semialgebraic fibrewise closure (CAD)
    E5    E5_strat                fibrewise weak stratification (Gabrielov–Vorobjov)
    E6    E6_fiber_closure        fibrewise closure and frontier of EA sets (Gabrielov 1998)
    E7    E7_fiber_cut, E7_prop_main, E7_bv_main, E7_star_compl, E7_star_inter, E7_subpf_compl
                                  (Binyamini–Vorobjov, with a "SubPf" track for E0)
    E8    E8_reduce, E8_comps, E8_sharpCD, E8_boxZero  packaging into a `SOMin` on ℝⁿ
    E9    E9_sharpDeriv           sharp derivatives (BNZ §3)
    E10   E10_rexp_to_subpf, E10_subpf_to_rexp         rexp syntax <-> sub-Pfaffian (for E0)
-/
import Submission.Work.Wilkies.Defs
import Mathlib.Topology.Connected.Clopen
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt

set_option autoImplicit false
noncomputable section
open Classical Topology
namespace WilkiesDesign.E
open WilkiesConjecture WilkiesDesign

/-! ## §0. Vocabulary (lead-owned; frozen once dispatched) -/

/-- The closed cube `[-1,1]^k`. Every EA set lives inside it (this is "restricted"). -/
def cubeC (k : ℕ) : Set (Fin k → ℝ) := {x | ∀ i, |x i| ≤ 1}

/-- An exp-affine chain: `r` affine forms `ℓ_j(x) = ∑ᵢ a j i * x i + b j`. The chain functions
are `exp ∘ ℓ_j`. Every bound in area E is uniform in `a` and `b`. That uniformity is what makes
`boxZero M P` have format and degree independent of `M`. -/
structure EAChain (k r : ℕ) where
  a : Fin r → Fin k → ℝ
  b : Fin r → ℝ

def EAChain.ell {k r : ℕ} (c : EAChain k r) (j : Fin r) (x : Fin k → ℝ) : ℝ :=
  ∑ i, c.a j i * x i + c.b j

/-- The empty chain (semialgebraic case). -/
def EAChain.nil (k : ℕ) : EAChain k 0 := ⟨fun j => j.elim0, fun j => j.elim0⟩

/-- EA polynomials. Variable `Sum.inl i` is `x i` and variable `Sum.inr j` is `exp (ℓ_j x)`. -/
abbrev EAPoly (k r : ℕ) := MvPolynomial (Fin k ⊕ Fin r) ℝ

def eaEval {k r : ℕ} (c : EAChain k r) (Q : EAPoly k r) (x : Fin k → ℝ) : ℝ :=
  MvPolynomial.eval (Sum.elim x (fun j => Real.exp (c.ell j x))) Q

/-- The symbolic `∂/∂xᵢ`: `∂ᵢQ = Q_{xᵢ} + ∑ⱼ aⱼᵢ Eⱼ Q_{Eⱼ}`. It does not raise the total degree.
(Its correctness, `HasFDerivAt (eaEval c Q) … `, is a vocabulary lemma owned by E.V.) -/
def eaD {k r : ℕ} (c : EAChain k r) (i : Fin k) (Q : EAPoly k r) : EAPoly k r :=
  MvPolynomial.pderiv (Sum.inl i) Q +
    ∑ j, MvPolynomial.C (c.a j i) * MvPolynomial.X (Sum.inr j) * MvPolynomial.pderiv (Sum.inr j) Q

/-- Ordered mixed derivative `∂_{k-1}^{m (k-1)} ⋯ ∂_0^{m 0} Q`. -/
def eaDmulti {k r : ℕ} (c : EAChain k r) (m : Fin k → ℕ) (Q : EAPoly k r) : EAPoly k r :=
  (List.finRange k).foldr (fun i g => (eaD c i)^[m i] g) Q

/-- Degree of one atom. The `+1` makes the degree also bound the number of atoms (as in BV). -/
def atomDeg {k r : ℕ} (Q : EAPoly k r) : ℕ := Q.totalDegree + 1

/-- A basic EA set: equations `= 0` and strict inequalities `> 0`. -/
structure Basic (k r : ℕ) where
  eqs : List (EAPoly k r)
  pos : List (EAPoly k r)

def Basic.deg {k r : ℕ} (B : Basic k r) : ℕ := ((B.eqs ++ B.pos).map atomDeg).sum

def Basic.holds {k r : ℕ} (c : EAChain k r) (B : Basic k r) (x : Fin k → ℝ) : Prop :=
  (∀ f ∈ B.eqs, eaEval c f x = 0) ∧ (∀ g ∈ B.pos, 0 < eaEval c g x)

/-- A restricted semi-Pfaffian set over an EA chain, in DNF, intersected with the closed cube.
Format is `k + r`. Degree is the sum of the atom degrees. -/
structure SemiPf (k : ℕ) where
  r : ℕ
  c : EAChain k r
  basics : List (Basic k r)

def SemiPf.set {k : ℕ} (X : SemiPf k) : Set (Fin k → ℝ) :=
  {x | x ∈ cubeC k ∧ ∃ B ∈ X.basics, B.holds X.c x}

def SemiPf.deg {k : ℕ} (X : SemiPf k) : ℕ := (X.basics.map Basic.deg).sum
def SemiPf.fmt {k : ℕ} (X : SemiPf k) : ℕ := k + X.r

/-- Semialgebraic sets in DNF on all of `ℝ^m` (no cube). Used only by E4 and E6. -/
structure SA (m : ℕ) where
  basics : List (Basic m 0)

def SA.set {m : ℕ} (X : SA m) : Set (Fin m → ℝ) := {x | ∃ B ∈ X.basics, B.holds (EAChain.nil m) x}
def SA.deg {m : ℕ} (X : SA m) : ℕ := (X.basics.map Basic.deg).sum

/-- Projection to the first `n` coordinates. -/
def projFirst (n m : ℕ) (x : Fin (n + m) → ℝ) : Fin n → ℝ := fun i => x (Fin.castAdd m i)

/-- The last `m` coordinates. -/
def projSnd (n m : ℕ) (x : Fin (n + m) → ℝ) : Fin m → ℝ := fun i => x (Fin.natAdd n i)

/-- The fibre of `X ⊆ ℝ^{p+q}` over `x ∈ ℝ^p`. -/
def fiber {p q : ℕ} (X : Set (Fin (p + q) → ℝ)) (x : Fin p → ℝ) : Set (Fin q → ℝ) :=
  {y | Fin.append x y ∈ X}

/-- The fibrewise closure `{(x,y) | y ∈ closure (X_x)}`. -/
def fiberClosure {p q : ℕ} (X : Set (Fin (p + q) → ℝ)) : Set (Fin (p + q) → ℝ) :=
  {z | projSnd p q z ∈ closure (fiber X (projFirst p q z))}

/-- A BV *-piece: the projection of ONE connected component of an EA semi-Pfaffian set.
If `p ∉ X.set`, the piece is empty. -/
structure StarPiece (n : ℕ) where
  m : ℕ
  X : SemiPf (n + m)
  p : Fin (n + m) → ℝ

def StarPiece.set {n : ℕ} (P : StarPiece n) : Set (Fin n → ℝ) :=
  projFirst n P.m '' connectedComponentIn P.X.set P.p

/-- BV *-format `≤ F` and *-degree `≤ D` (BV Def. 2, with "≤" built in). -/
def Star (F D n : ℕ) (Y : Set (Fin n → ℝ)) : Prop :=
  ∃ L : List (StarPiece n), Y = (⋃ P ∈ L, P.set) ∧ (∀ P ∈ L, P.X.fmt ≤ F) ∧
    (L.map fun P => P.X.deg).sum ≤ D

/-- Restricted sub-Pfaffian (EA chain), with no complexity bound. Used for E0. -/
def SubPf (n : ℕ) (Y : Set (Fin n → ℝ)) : Prop :=
  ∃ (m : ℕ) (X : SemiPf (n + m)), Y = projFirst n m '' X.set

/-- The semialgebraic homeomorphism `ℝ → (-1,1)`, `x ↦ x/√(1+x²)`, applied coordinatewise. -/
def psi (x : ℝ) : ℝ := x / Real.sqrt (1 + x ^ 2)
def psiV {n : ℕ} (x : Fin n → ℝ) : Fin n → ℝ := fun i => psi (x i)

/-- *-sets transported to `ℝⁿ`. -/
def StarR (F D n : ℕ) (Y : Set (Fin n → ℝ)) : Prop :=
  ∃ Z : Set (Fin n → ℝ), Star F D n Z ∧ Y = psiV ⁻¹' Z

/-- The FD-filtration that area E delivers. It is the smallest family that contains the
transported *-sets and is closed under the `SOMin` axioms 1–3. Every closure axiom is a
constructor, so only `comps` (and SharpCD/SharpDeriv) need real proofs; these go through `E8_reduce`. -/
inductive Gen : ℕ → ℕ → (n : ℕ) → Set (Fin n → ℝ) → Prop
  | star {F D n : ℕ} {X : Set (Fin n → ℝ)} : StarR F D n X → Gen F D n X
  | mono_F {F D n : ℕ} {X : Set (Fin n → ℝ)} : Gen F D n X → Gen (F + 1) D n X
  | mono_D {F D n : ℕ} {X : Set (Fin n → ℝ)} : Gen F D n X → Gen F (D + 1) n X
  | compl {F D n : ℕ} {X : Set (Fin n → ℝ)} : Gen F D n X → Gen (F + 1) D n Xᶜ
  | proj {F D n : ℕ} {X : Set (Fin (n + 1) → ℝ)} : Gen F D (n + 1) X → Gen (F + 1) D n (projLast X)
  | prod_right {F D n : ℕ} {X : Set (Fin n → ℝ)} :
      Gen F D n X → Gen (F + 1) D (n + 1) {z | Fin.init z ∈ X}
  | prod_left {F D n : ℕ} {X : Set (Fin n → ℝ)} :
      Gen F D n X → Gen (F + 1) D (n + 1) {z | Fin.tail z ∈ X}
  | union {F n k : ℕ} (D : Fin k → ℕ) (A : Fin k → Set (Fin n → ℝ)) :
      (∀ i, Gen F (D i) n (A i)) → Gen F (∑ i, D i) n (⋃ i, A i)
  | inter {F n k : ℕ} (D : Fin k → ℕ) (A : Fin k → Set (Fin n → ℝ)) :
      (∀ i, Gen F (D i) n (A i)) → Gen (F + 1) (∑ i, D i) n (⋂ i, A i)
  | hyp (n : ℕ) (P : MvPolynomial (Fin n) ℝ) :
      Gen n P.totalDegree n {x | MvPolynomial.eval x P = 0}

/-- BV's cylindrical decomposition of a subset `A` (frozen `IsCell`; compare frozen `IsCylDecomp`). -/
def IsCylDecompOn : (n : ℕ) → Set (Fin n → ℝ) → Finset (Set (Fin n → ℝ)) → Prop
  | 0, A, C => (A = Set.univ ∧ C = {Set.univ}) ∨ (A = ∅ ∧ C = ∅)
  | n + 1, A, C => (∀ c ∈ C, IsCell (n + 1) c ∧ c.Nonempty) ∧
      (C : Set (Set (Fin (n + 1) → ℝ))).PairwiseDisjoint id ∧
      ⋃₀ (C : Set (Set (Fin (n + 1) → ℝ))) = A ∧
      IsCylDecompOn n (Fin.init '' A) (C.image (fun c => Fin.init '' c))

/-! ## E1. Bezout-type count (textbook; the r = 0 case of Khovanskii) -/

/-- **E1.** The number of nondegenerate real zeros of `k` polynomials in `k` variables is
polynomial in the degrees, for fixed `k`. Any polynomial will do; the sharp `∏ deg` is not needed. -/
theorem E1_bezout : ∀ k : ℕ, ∃ p : Polynomial ℕ, ∀ (f : Fin k → EAPoly k 0) (s : Finset (Fin k → ℝ)),
    (∀ x ∈ s, (∀ i, eaEval (EAChain.nil k) (f i) x = 0) ∧
      (Matrix.of fun i j => eaEval (EAChain.nil k) (eaD (EAChain.nil k) j (f i)) x).det ≠ 0) →
    s.card ≤ p.eval (∑ i, atomDeg (f i)) := by
  sorry

/-! ## E2. Khovanskii for EA chains (first-integral Rolle; RESEARCH-formalization) -/

/-- **E2a. Khovanskii.** Nondegenerate zeros of `k` EA functions on all of `ℝ^k`. The bound is
uniform in the chain coefficients. -/
theorem E2_khovanskii : ∀ F : ℕ, ∃ p : Polynomial ℕ, ∀ (k r : ℕ) (c : EAChain k r)
    (f : Fin k → EAPoly k r) (s : Finset (Fin k → ℝ)), k + r ≤ F →
    (∀ x ∈ s, (∀ i, eaEval c (f i) x = 0) ∧
      (Matrix.of fun i j => eaEval c (eaD c j (f i)) x).det ≠ 0) →
    s.card ≤ p.eval (∑ i, atomDeg (f i)) := by
  sorry

/-- **E2b. Components.** An EA semi-Pfaffian set has `poly_F(D)` connected components. Proof via
Morse/critical points, consistent sign conditions, and E2a (GV survey Cor. 3.3 and Thm. 3.7). -/
theorem E2_components : ∀ F : ℕ, ∃ p : Polynomial ℕ, ∀ (k : ℕ) (X : SemiPf k), X.fmt ≤ F →
    ∃ s : Finset (Fin k → ℝ), s.card ≤ p.eval X.deg ∧ ↑s ⊆ X.set ∧
      ∀ x ∈ X.set, ∃ y ∈ s, connectedComponentIn X.set x = connectedComponentIn X.set y := by
  sorry

/-! ## E3. Multiplicities (Gabrielov 1995; RESEARCH) -/

/-- `∂_{h,ι,l} f`: the `(j+1)×(j+1)` determinant whose rows are `h₁ … hⱼ, f` and whose columns
are the derivatives `∂_{ι 1} … ∂_{ι j}, ∂_l` (GV survey Def. 4.6). -/
def detOp {k r j : ℕ} (c : EAChain k r) (h : Fin j → EAPoly k r) (ι : Fin j → Fin k) (l : Fin k)
    (f : EAPoly k r) : EAPoly k r :=
  Matrix.det (Matrix.of fun (a b : Fin (j + 1)) =>
    eaD c (Fin.lastCases l ι b) (Fin.lastCases f h a))

/-- The ordered iterate `∂_{h,ι,k-1}^{m (k-1)} ⋯ ∂_{h,ι,0}^{m 0} f`. -/
def opMono {k r j : ℕ} (c : EAChain k r) (h : Fin j → EAPoly k r) (ι : Fin j → Fin k)
    (m : Fin k → ℕ) (f : EAPoly k r) : EAPoly k r :=
  (List.finRange k).foldr (fun l g => (detOp c h ι l)^[m l] g) f

/-- **E3a. Bounded-order identity theorem along an effectively smooth manifold** (GV survey
Cor. 4.7). If every ordered `∂_{h,ι,·}`-derivative of `f` of order `≤ M` vanishes at `x`, then
`f ≡ 0` on `{h = 0}` near `x`. For `j = 0` this is "a nonzero EA function vanishes to order
`≤ M`", which is Pólya's bound on a generic line. -/
theorem E3_identity : ∀ F : ℕ, ∃ M : Polynomial ℕ, ∀ (k r j : ℕ) (c : EAChain k r)
    (h : Fin j → EAPoly k r) (ι : Fin j → Fin k) (f : EAPoly k r) (x : Fin k → ℝ),
    k + r ≤ F → (∀ a, eaEval c (h a) x = 0) →
    (Matrix.of fun a b => eaEval c (eaD c (ι b) (h a)) x).det ≠ 0 →
    (∀ m : Fin k → ℕ, (∀ a, m (ι a) = 0) →
      ∑ l, m l ≤ M.eval (∑ a, atomDeg (h a) + atomDeg f) → eaEval c (opMono c h ι m f) x = 0) →
    ∀ᶠ y in 𝓝 x, (∀ a, eaEval c (h a) y = 0) → eaEval c f y = 0 := by
  sorry

/-- Taylor polynomial of order `N` of an EA function at `y`, evaluated at `x`. -/
def eaTaylor {k r : ℕ} (c : EAChain k r) (Q : EAPoly k r) (N : ℕ) (y x : Fin k → ℝ) : ℝ :=
  ∑ m ∈ ((Finset.univ : Finset (Fin k → Fin (N + 1))).image (fun m i => (m i : ℕ))).filter
      (fun m => ∑ i, m i ≤ N),
    eaEval c (eaDmulti c m Q) y * ∏ i, (x i - y i) ^ m i / ((m i).factorial : ℝ)

/-- **E3b. Taylor closure criterion** (GV survey Cor. 4.5, from Gabrielov 1998 §2). The closure
of a basic EA set at `y` is decided by the semialgebraic set of truncated Taylor conditions. -/
theorem E3_taylor_closure : ∀ F : ℕ, ∃ K : Polynomial ℕ, ∀ (k r : ℕ) (c : EAChain k r)
    (B : Basic k r) (y : Fin k → ℝ) (κ : ℕ), k + r ≤ F → K.eval B.deg < κ →
    (y ∈ closure {x | B.holds c x} ↔
      y ∈ closure {x | (∀ f ∈ B.eqs, |eaTaylor c f (κ ^ 2) y x| ≤ dist x y ^ (κ ^ 2)) ∧
                       (∀ g ∈ B.pos, dist x y ^ κ < eaTaylor c g κ y x)}) := by
  sorry

/-! ## E4. Effective semialgebraic fibrewise closure (CAD with degree bounds; textbook-large) -/

/-- **E4.** For fixed `p, q`, the fibrewise closure of a semialgebraic set is semialgebraic of
polynomial degree. (This is Collins CAD, or BPR ch. 5/14, restricted to one `∀∃` pattern.) -/
theorem E4_sa_fiber_closure : ∀ p q : ℕ, ∃ b : Polynomial ℕ, ∀ X : SA (p + q),
    ∃ Y : SA (p + q), Y.deg ≤ b.eval X.deg ∧ Y.set = fiberClosure X.set := by
  sorry

/-! ## E5. Fibrewise weak stratification (Gabrielov–Vorobjov 1995; RESEARCH) -/

/-- A fibrewise effectively smooth stratum over the first `p` coordinates: an EA set `X` together
with `j` equations `h`. At each point of `X`, the `h` vanish, their Jacobian in the last `q`
coordinates has rank `j`, and inside the fibre `X` coincides locally with `{h = 0}`. -/
structure Stratum (p q : ℕ) where
  X : SemiPf (p + q)
  j : ℕ
  h : Fin j → EAPoly (p + q) X.r

def Stratum.Good {p q : ℕ} (S : Stratum p q) : Prop :=
  ∀ z ∈ S.X.set, (∀ a, eaEval S.X.c (S.h a) z = 0) ∧
    (Matrix.of fun (a : Fin S.j) (l : Fin q) =>
        eaEval S.X.c (eaD S.X.c (Fin.natAdd p l) (S.h a)) z).rank = S.j ∧
    ∀ᶠ z' in 𝓝 z, projFirst p q z' = projFirst p q z → (∀ a, eaEval S.X.c (S.h a) z' = 0) →
      z' ∈ S.X.set

def Stratum.deg {p q : ℕ} (S : Stratum p q) : ℕ := S.X.deg + ∑ a, atomDeg (S.h a)

/-- **E5.** A fibrewise weak stratification with `poly_F(D)` strata of format `const(F)` and
degree `poly_F(D)` (BV Fact 3 + Remark 4). Taking `p = 0` gives the absolute version. -/
theorem E5_strat : ∀ F : ℕ, ∃ (a : ℕ) (b : Polynomial ℕ), ∀ (p q : ℕ) (X : SemiPf (p + q)),
    X.fmt ≤ F →
    ∃ L : List (Stratum p q), L.length ≤ b.eval X.deg ∧
      (∀ S ∈ L, S.X.fmt ≤ a ∧ S.deg ≤ b.eval X.deg ∧ S.Good) ∧
      X.set = (⋃ S ∈ L, S.X.set) ∧ L.Pairwise (fun S T => Disjoint S.X.set T.X.set) := by
  sorry

/-! ## E6. Fibrewise closure and frontier of EA sets (Gabrielov 1998, from E3b + E4) -/

/-- **E6.** The fibrewise closure and the fibrewise frontier of an EA semi-Pfaffian set are EA
semi-Pfaffian of format `const(F)` and degree `poly_F(D)` (BV Fact 5 + Remark 6). -/
theorem E6_fiber_closure : ∀ F : ℕ, ∃ (a : ℕ) (b : Polynomial ℕ), ∀ (p q : ℕ)
    (X : SemiPf (p + q)), X.fmt ≤ F →
    ∃ Y Y' : SemiPf (p + q), Y.fmt ≤ a ∧ Y.deg ≤ b.eval X.deg ∧ Y'.fmt ≤ a ∧
      Y'.deg ≤ b.eval X.deg ∧ Y.set = fiberClosure X.set ∧ Y'.set = fiberClosure X.set \ X.set := by
  sorry

/-! ## E7. Binyamini–Vorobjov sharp cell decomposition (RESEARCH; the paper's own content) -/

/-- **E7a. Fibre cutting** (BV Lemma 8), in list form: `poly_F(D)` pieces, each with its own
chain, of format `const(F)` and degree `poly_F(D)`, with finite fibres over `ℝⁿ`, whose projections
together are exactly `π_n(X)`. (BV's pieces come from `E5_strat`/`E6_fiber_closure`, which do not
share a chain, so they are kept apart, as `Star` does.) -/
theorem E7_fiber_cut : ∀ F : ℕ, ∃ (a : ℕ) (b : Polynomial ℕ), ∀ (n m : ℕ) (X : SemiPf (n + m)),
    X.fmt ≤ F →
    ∃ L : List (SemiPf (n + m)), L.length ≤ b.eval X.deg ∧
      (∀ Xh ∈ L, Xh.fmt ≤ a ∧ Xh.deg ≤ b.eval X.deg ∧ ∀ x, (fiber Xh.set x).Finite) ∧
      projFirst n m '' X.set = ⋃ Xh ∈ L, projFirst n m '' Xh.set := by
  sorry

/-- **E7b. BV Proposition 9**, with the extra SubPf track that E0 needs. -/
theorem E7_prop_main : ∀ F n : ℕ, ∃ (a : ℕ) (b : MvPolynomial (Fin 2) ℕ) (c : Polynomial ℕ),
    ∀ (D k m : ℕ) (X : Fin k → SemiPf (n + m)), (∀ i, (X i).fmt ≤ F ∧ (X i).deg ≤ D) →
    ∃ C : Finset (Set (Fin n → ℝ)), IsCylDecompOn n (cubeC n) C ∧
      (∀ i, ∀ κ ∈ C, κ ⊆ projFirst n m '' (X i).set ∨ Disjoint κ (projFirst n m '' (X i).set)) ∧
      C.card ≤ MvPolynomial.eval ![D, k] b ∧ ∀ κ ∈ C, Star a (c.eval D) n κ ∧ SubPf n κ := by
  sorry

/-- **E7c. BV Theorem 1** (sharp CD for *-sets), on the closed cube. -/
theorem E7_bv_main : ∀ F n : ℕ, ∃ (a : ℕ) (b : MvPolynomial (Fin 2) ℕ) (c : Polynomial ℕ),
    ∀ (D k : ℕ) (Y : Fin k → Set (Fin n → ℝ)), (∀ i, Star F D n (Y i)) →
    ∃ C : Finset (Set (Fin n → ℝ)), IsCylDecompOn n (cubeC n) C ∧
      (∀ i, ∀ κ ∈ C, κ ⊆ Y i ∨ Disjoint κ (Y i)) ∧
      C.card ≤ MvPolynomial.eval ![D, k] b ∧ ∀ κ ∈ C, Star a (c.eval D) n κ := by
  sorry

/-- **E7d. BV Theorem 2, the ¬ case**: effective complement of *-sets. -/
theorem E7_star_compl : ∀ F n : ℕ, ∃ (a : ℕ) (p : Polynomial ℕ), ∀ (D : ℕ) (Y : Set (Fin n → ℝ)),
    Star F D n Y → Star a (p.eval D) n (cubeC n \ Y) := by
  sorry

/-- **E7e. BV Theorem 2, the ∧ case.** Sets of *-degree 0 are `∅` or the cube, so `k` is
effectively at most `∑ D`. -/
theorem E7_star_inter : ∀ F n : ℕ, ∃ (a : ℕ) (p : Polynomial ℕ), ∀ (k : ℕ) (D : Fin k → ℕ)
    (Y : Fin k → Set (Fin n → ℝ)), (∀ i, Star F (D i) n (Y i)) →
    Star a (p.eval (∑ i, D i)) n (cubeC n ∩ ⋂ i, Y i) := by
  sorry

/-- **E7f. Gabrielov's complement theorem** (non-effective; from E7b's SubPf track). -/
theorem E7_subpf_compl {n : ℕ} (Y : Set (Fin n → ℝ)) (h : SubPf n Y) :
    SubPf n (cubeC n \ Y) := by
  sorry

/-! ## E8. Packaging into a `SOMin` on ℝⁿ (semi-mechanical) -/

/-- **E8a. Reduction** `Gen ≤ Star` (2209.10972 Def. 1.4 style). `p` has zero constant term,
because degree-0 `Gen` sets are exactly `∅` and `univ`. Use a superadditive `p = c·D^e`.
`a` MUST depend on `n`: `Gen.inter` with `k = 0` puts `univ ⊆ ℝⁿ` in `Gen 1 0 n` for every `n`.
The proof is an induction on the derivation, with `(A F n, P_{F,n})` defined by recursion on `F`
for all `n` at once (`proj` visits `n+1`, `prod_*` visit `n-1`). -/
theorem E8_reduce : ∀ F n : ℕ, ∃ (a : ℕ) (p : Polynomial ℕ), p.eval 0 = 0 ∧
    ∀ (D : ℕ) (X : Set (Fin n → ℝ)), Gen F D n X → StarR a (p.eval D) n X := by
  sorry

/-- **E8b.** SOMin axiom 4. -/
theorem E8_comps : ∀ F : ℕ, ∃ p : Polynomial ℕ, ∀ (D : ℕ) (A : Set (Fin 1 → ℝ)), Gen F D 1 A →
    ∃ s : Finset (Set (Fin 1 → ℝ)), s.card ≤ p.eval D ∧ (∀ c ∈ s, IsPreconnected c) ∧
      A = ⋃₀ (s : Set (Set (Fin 1 → ℝ))) := by
  sorry

/-- The sharply o-minimal structure of area E. Every axiom except `comps` is a constructor. -/
def genSOMin : SOMin where
  Ω := Gen
  mono_F := fun h => Gen.mono_F h
  mono_D := fun h => Gen.mono_D h
  compl := fun h => Gen.compl h
  proj := fun h => Gen.proj h
  prod_right := fun h => Gen.prod_right h
  prod_left := fun h => Gen.prod_left h
  union := fun D A h => Gen.union D A h
  inter := fun D A h => Gen.inter D A h
  hyp := fun n P => Gen.hyp n P
  comps := E8_comps

/-- **E8c.** Sharp cell decomposition, from E7c on the cube, restricted to the open cube and
transported by `psiV`. -/
theorem E8_sharpCD : genSOMin.SharpCD := by
  sorry

/-- **E8d.** The truncated exp-polynomial zero sets. Use `z = M • s` with `s ∈ [-1,1]^N`; the
chain is `exp (M * s i)`. -/
theorem E8_boxZero : ∀ N d : ℕ, ∃ F D : ℕ, ∀ (M : ℝ) (P : MvPolynomial (Fin N ⊕ Fin N) ℝ),
    P.totalDegree ≤ d → boxZero M P ∈ genSOMin.Ω F D N := by
  sorry

/-! ## E9. Sharp derivatives (BNZ §3) -/

/-- **E9.** -/
theorem E9_sharpDeriv : genSOMin.SharpDeriv := by
  sorry

/-! ## E10. rexp syntax ↔ sub-Pfaffian (mechanical; shares lemmas with area B) -/

/-- **E10a.** Split each variable into `|w| ≤ 1` (chain `exp w`) or `|w| > 1` (`rexp w = 0`). -/
theorem E10_rexp_to_subpf {n : ℕ} (X : Set (Fin n → ℝ)) (h : RExpExist X) :
    ∃ Z : Set (Fin n → ℝ), SubPf n Z ∧ X = psiV ⁻¹' Z := by
  sorry

/-- **E10b.** `exp (ℓ x) = (rexp (ℓ x / L))^L` on the cube, with `L ≥ ∑|a| + |b|`. -/
theorem E10_subpf_to_rexp {n : ℕ} (Z : Set (Fin n → ℝ)) (h : SubPf n Z) :
    RExpExist (psiV ⁻¹' Z) := by
  sorry

/-! ## Wiring (proved here, modulo the holes above) -/

theorem psi_abs_le_one (x : ℝ) : |psi x| ≤ 1 := by
  unfold psi
  rw [abs_div, abs_of_nonneg (Real.sqrt_nonneg _)]
  have hpos : 0 < Real.sqrt (1 + x ^ 2) := Real.sqrt_pos.mpr (by positivity)
  rw [div_le_one hpos]
  exact Real.abs_le_sqrt (by nlinarith)

theorem psiV_mem_cube {n : ℕ} (x : Fin n → ℝ) : psiV x ∈ cubeC n := fun i => psi_abs_le_one (x i)

/-- The frozen `E_instance`. -/
theorem E_instance_from_parts : ∃ S : SOMin, S.SharpCD ∧ S.SharpDeriv ∧
    ∀ N d : ℕ, ∃ F D : ℕ, ∀ (M : ℝ) (P : MvPolynomial (Fin N ⊕ Fin N) ℝ),
      P.totalDegree ≤ d → boxZero M P ∈ S.Ω F D N :=
  ⟨genSOMin, E8_sharpCD, E9_sharpDeriv, E8_boxZero⟩

/-- The frozen `E0_rexp_complement`. -/
theorem E0_from_parts {n : ℕ} (X : Set (Fin n → ℝ)) (h : RExpExist X) : RExpExist Xᶜ := by
  obtain ⟨Z, hZ, rfl⟩ := E10_rexp_to_subpf X h
  have key := E10_subpf_to_rexp _ (E7_subpf_compl Z hZ)
  have hset : (psiV ⁻¹' Z)ᶜ = psiV ⁻¹' (cubeC n \ Z) := by
    ext x
    simp only [Set.mem_compl_iff, Set.mem_preimage, Set.mem_sdiff]
    exact ⟨fun hx => ⟨psiV_mem_cube x, hx⟩, fun hx => hx.2⟩
  rw [hset]
  exact key

end WilkiesDesign.E
