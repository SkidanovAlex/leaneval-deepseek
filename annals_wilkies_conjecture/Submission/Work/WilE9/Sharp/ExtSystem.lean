/-
  WilE9 / Sharp — the *extended* system (definitions).

  Fix `n`, `m`, a stratum `S` with base `ℝⁿ` and fibre `ℝ^{1+m}` (`S.X : SemiPf (n + (1+m))`,
  `h : Fin (1+m) → EAPoly (n + (1+m)) r`, effectively smooth), and a list `L` of `n`-directions.
  The extended system lives in `ℝ^{Next n m} = ℝ^{2n+m+4}` with

  * the base `y : ℝⁿ` (the `ψ`-coordinates of `x`, so that the projection to the first `n+1`
    coordinates is inside the cube), and
  * the output `σ` (at position `n`, so that `projFirst (n+1) _` keeps `(y, σ)`), and
  * the fibre `(w, u, τ, aux, υ)`.

  Its equations are

  * `y i ^ 2 + w i ^ 2 = 1` (for each `i`), `τ ^ 2 + u ^ 2 = 1`, `σ ^ 2 + υ ^ 2 = 1`;
  * the stratum's own equations `h a` (reindexed), and the stratum's basic condition `B`;
  * the *cleared* form of `σ * Q ^ (2|L|) = υ * P_L`, where `Q = pbQ`, `P_L = pbP` are the
    pulled-back implicit-function polynomials of `Submission/Work/WilE9/Sharp/PbSystem.lean`
    and `clearPb` substitutes `xᵢ ↦ yᵢ/wᵢ`, `s ↦ τ/u` and clears the common denominator
    `∏ᵢ wᵢ^K · u^K`;

  together with the strict inequalities `w i > 0`, `u > 0`, `υ > 0`.  The point of the two
  square-root pairs is that `w i = psig (x i)` and `υ = psig (ζ)` are *positive* on the intended
  locus, so the system pins down `x`, `s = f x` and `ζ` uniquely; on the complement `w i = 0` or
  `u = 0` or `υ = 0` one has `y i = ±1` or `τ = ±1` or `σ = ±1`, i.e. the point is outside the
  open cube and therefore invisible to `psiV ⁻¹' ·`.

  The projection `projFirst (n+1) (Next n m - (n+1)) '' (exSemiPf S h L).set` is the `ψ`-image of
  the graph of `∂_L f` over the base of `S` (`WilE9/Sharp/exSemiPf_correct`), and it is a `Star`
  set of format `const` and degree `poly(D,|L|)` by `WilE8.StarOfSemipfLe.star_of_semipf_le`.
-/
import Mathlib
import Submission.Work.WilE9.Sharp.Layout
import Submission.Work.WilE9.Sharp.PbSystem
import Submission.Work.WilE9.Sharp.Clear

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace Work.WilE9.Sharp
open WilkiesDesign WilkiesDesign.E

/-! ## The clearing map from the pulled-back ambient to the extended one -/

/-- The pulled-back ambient, split into the substituted block `(x, s)` and the rest. -/
def pbEquiv (n m : ℕ) : Fin (Npb n m) ≃ (Fin (n + 1) ⊕ Fin (2 * n + m + 2)) :=
  (finCongr (by simp [Npb, qpb]; ring)).trans finSumFinEquiv.symm

/-- The numerators of the substitution: `x i ↦ y i`, `s ↦ τ`. -/
def sNum (n m : ℕ) : Fin (n + 1) → Fin (Next n m) := fun i =>
  if h : (i : ℕ) < n then exY n m ⟨i, h⟩ else exT n m

/-- The denominators of the substitution: `x i ↦ w i`, `s ↦ u`. -/
def sDen (n m : ℕ) : Fin (n + 1) → Fin (Next n m) := fun i =>
  if h : (i : ℕ) < n then exW n m ⟨i, h⟩ else exU n m

/-- The remaining coordinates of the pulled-back ambient, renamed. -/
def sRest (n m : ℕ) : Fin (2 * n + m + 2) → Fin (Next n m) := fun k =>
  if h1 : (k : ℕ) < n then exY n m ⟨k, h1⟩
  else if h2 : (k : ℕ) < 2 * n then exW n m ⟨(k : ℕ) - n, by omega⟩
  else if _ : (k : ℕ) = 2 * n then exT n m
  else if _ : (k : ℕ) = 2 * n + 1 then exU n m
  else exA n m ⟨(k : ℕ) - (2 * n + 2), by have := k.isLt; omega⟩

/-- Clearing the substitution `x i ↦ y i / w i`, `s ↦ τ / u` in a pulled-back polynomial: the
numerator of `∏ i w i ^ K · u ^ K` times the substituted polynomial (see
`Work.WilE9.Sharp.clearNumDen_eval`). -/
def clearPb (n m : ℕ) {r : ℕ} (K : ℕ) (P : EAPoly (Npb n m) r) : EAPoly (Next n m) r :=
  clearNumDen (β := Fin (n + 1)) (γ := Fin (2 * n + m + 2) ⊕ Fin r)
    (α := Fin (Next n m) ⊕ Fin r)
    (fun b => Sum.inl (sNum n m b)) (fun b => Sum.inl (sDen n m b))
    (Sum.elim (fun k => Sum.inl (sRest n m k)) (fun j => Sum.inr j)) K
    (P.rename ⇑((pbEquiv n m).sumCongr (Equiv.refl (Fin r)) |>.trans (Equiv.sumAssoc (Fin (n + 1)) (Fin (2 * n + m + 2)) (Fin r))))

/-! ## The reindexed stratum data -/

/-- An extended ambient point, read in the stratum's own coordinates `(y, τ, aux)`. -/
def exStrat {n m : ℕ} (z : Fin (Next n m) → ℝ) : Fin (n + (1 + m)) → ℝ :=
  fun i => z (sIdxE n m i)

/-- A stratum polynomial, reindexed into the extended ambient. -/
def exRaise {n m r : ℕ} (P : EAPoly (n + (1 + m)) r) : EAPoly (Next n m) r :=
  P.rename (Sum.map (sIdxE n m) id)

/-- The stratum's chain, reindexed into the extended ambient. -/
def exChain {n m r : ℕ} (c : EAChain (n + (1 + m)) r) : EAChain (Next n m) r where
  a j l := ∑ i : Fin (n + (1 + m)), if sIdxE n m i = l then c.a j i else 0
  b := c.b

/-! ## The equations -/

/-- The clearing exponent: a common upper bound for the degrees of `Q ^ (2|L|)` and `P_L`. -/
def exK {n m r : ℕ} (c : EAChain (n + (1 + m)) r)
    (h : Fin (1 + m) → EAPoly (n + (1 + m)) r) (L : List (Fin n)) : ℕ :=
  max ((pbQ c h ^ (2 * L.length)).totalDegree) ((pbP c h L).totalDegree) + 1

/-- The cleared numerator `∏ w^K u^K · Q^(2|L|)(x ↦ y/w, s ↦ τ/u)`. -/
def exQ {n m r : ℕ} (c : EAChain (n + (1 + m)) r)
    (h : Fin (1 + m) → EAPoly (n + (1 + m)) r) (L : List (Fin n)) : EAPoly (Next n m) r :=
  clearPb n m (exK c h L) ((pbQ c h) ^ (2 * L.length))

/-- The cleared numerator `∏ w^K u^K · P_L(x ↦ y/w, s ↦ τ/u)`. -/
def exP {n m r : ℕ} (c : EAChain (n + (1 + m)) r)
    (h : Fin (1 + m) → EAPoly (n + (1 + m)) r) (L : List (Fin n)) : EAPoly (Next n m) r :=
  clearPb n m (exK c h L) (pbP c h L)

/-- The equation `σ * Q^(2|L|) = υ * P_L`, cleared. -/
def exEq6 {n m r : ℕ} (c : EAChain (n + (1 + m)) r)
    (h : Fin (1 + m) → EAPoly (n + (1 + m)) r) (L : List (Fin n)) : EAPoly (Next n m) r :=
  MvPolynomial.X (Sum.inl (exSig n m)) * exQ c h L -
    MvPolynomial.X (Sum.inl (exV n m)) * exP c h L

/-- The list of the equations of the extended system other than the stratum's own basic
condition, i.e. `y²+w²=1`, `τ²+u²=1`, the equations `h`, `σ²+υ²=1` and the cleared equation. -/
def exEqList {n m r : ℕ} (c : EAChain (n + (1 + m)) r)
    (h : Fin (1 + m) → EAPoly (n + (1 + m)) r) (L : List (Fin n)) :
    List (EAPoly (Next n m) r) :=
  (List.finRange n).map (fun i =>
      MvPolynomial.X (Sum.inl (exY n m i)) ^ 2 + MvPolynomial.X (Sum.inl (exW n m i)) ^ 2 - 1)
    ++ [MvPolynomial.X (Sum.inl (exT n m)) ^ 2 +
        MvPolynomial.X (Sum.inl (exU n m)) ^ 2 - 1]
    ++ (List.finRange (1 + m)).map (fun a => exRaise (n := n) (m := m) (r := r) (h a))
    ++ [MvPolynomial.X (Sum.inl (exSig n m)) ^ 2 +
        MvPolynomial.X (Sum.inl (exV n m)) ^ 2 - 1]
    ++ [exEq6 c h L]

/-- The positivity conditions of the extended system (`w > 0`, `u > 0`, `υ > 0`) together with
those of the stratum's basic condition. -/
def exPosList {n m r : ℕ} (B : Basic (n + (1 + m)) r) : List (EAPoly (Next n m) r) :=
  (List.finRange n).map (fun i => MvPolynomial.X (Sum.inl (exW n m i)))
    ++ [MvPolynomial.X (Sum.inl (exU n m)), MvPolynomial.X (Sum.inl (exV n m))]
    ++ B.pos.map (exRaise (n := n) (m := m) (r := r))

/-- The extended counterpart of one basic condition of the stratum. -/
def exBasic {n m r : ℕ} (c : EAChain (n + (1 + m)) r)
    (h : Fin (1 + m) → EAPoly (n + (1 + m)) r) (L : List (Fin n))
    (B : Basic (n + (1 + m)) r) : Basic (Next n m) r :=
  ⟨exEqList c h L ++ B.eqs.map (exRaise (n := n) (m := m) (r := r)),
   exPosList (n := n) (m := m) (r := r) B⟩

/-- **The extended semi-Pfaffian set of a stratum.** -/
def exSemiPf (n m : ℕ) (E : EffStratum n m) (L : List (Fin n)) : SemiPf (Next n m) :=
  ⟨E.X.r, exChain E.X.c, E.X.basics.map (exBasic E.X.c E.h L)⟩

end Work.WilE9.Sharp
