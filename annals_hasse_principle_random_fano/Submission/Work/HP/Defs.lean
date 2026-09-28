import Mathlib
import ChallengeDeps

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Shared definitions for annals_hasse_principle_random_fano (namespace `Work.HP`)

Conventions:
* A degree-`d` form in `n+1` variables is a coefficient vector `a : Mon d n → ℤ`, indexed by
  exponent vectors (monomial basis, no multinomial weights), exactly as in the challenge's `height`.
* All norms are explicit Euclidean norms (`eNorm`, `rNorm`); Lean's `‖·‖` on `ι → ℝ` is the sup norm
  and must not be used for the paper's `||·||`.
* Counting is over primitive integer vectors `a` (both `±a`), so every count is twice the paper's
  count over `𝕍_{d,n}(A)`; ratios are unaffected.
-/

set_option autoImplicit false

noncomputable section

open MvPolynomial Finset

namespace Work.HP

/-! ## Monomials, Veronese map, forms -/

/-- Exponent vectors of degree-`d` monomials in `n+1` variables. -/
abbrev Mon (d n : ℕ) : Type := {m : Fin (n + 1) → Fin (d + 1) // ∑ i, (m i : ℕ) = d}

/-- The exponent vector as a finsupp. -/
def Mon.toFinsupp {d n : ℕ} (m : Mon d n) : Fin (n + 1) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => (m.1 i : ℕ))

/-- `N_{d,n}`, the number of degree-`d` monomials in `n+1` variables. -/
abbrev NN (d n : ℕ) : ℕ := Fintype.card (Mon d n)

/-- The Veronese map `ν_{d,n}`. -/
def veronese {R : Type*} [CommSemiring R] (d n : ℕ) (x : Fin (n + 1) → R) : Mon d n → R :=
  fun m => ∏ i, x i ^ (m.1 i : ℕ)

/-- `f_a(x) = ⟨a, ν(x)⟩`, evaluated in any commutative ring. -/
def formEval {R : Type*} [CommRing R] (d n : ℕ) (a : Mon d n → ℤ) (x : Fin (n + 1) → R) : R :=
  ∑ m, (a m : R) * veronese d n x m

/-- `f_a` for a real coefficient vector. -/
def formEvalR (d n : ℕ) (a : Mon d n → ℝ) (x : Fin (n + 1) → ℝ) : ℝ :=
  ∑ m, a m * veronese d n x m

/-- The rational polynomial with coefficient vector `a`. -/
def formOf (d n : ℕ) (a : Mon d n → ℤ) : MvPolynomial (Fin (n + 1)) ℚ :=
  ∑ m, monomial m.toFinsupp (a m : ℚ)

/-! ## Vectors, norms, primitivity -/

section vectors
variable {ι : Type*} [Fintype ι]

/-- Euclidean norm of an integer vector. -/
def eNorm (v : ι → ℤ) : ℝ := √(∑ i, ((v i : ℝ)) ^ 2)

/-- Euclidean norm of a real vector. -/
def rNorm (v : ι → ℝ) : ℝ := √(∑ i, (v i) ^ 2)

/-- Euclidean inner product of real vectors. -/
def dotR (v w : ι → ℝ) : ℝ := ∑ i, v i * w i

/-- Coercion of an integer vector to a real vector. -/
def toR (v : ι → ℤ) : ι → ℝ := fun i => (v i : ℝ)

/-- Primitive integer vector: coordinates have gcd one. -/
def IsPrim (v : ι → ℤ) : Prop := Finset.univ.gcd v = 1

/-- The cone `𝒞_v^{(γ)} = {t : |⟨v,t⟩| ≤ ‖v‖‖t‖/(2γ)}`. -/
def Cgam (v : ι → ℝ) (γ : ℝ) : Set (ι → ℝ) := {t | |dotR v t| ≤ rNorm v * rNorm t / (2 * γ)}

/-- `√(‖v‖²‖w‖² − ⟨v,w⟩²)`, the covolume of `ℤv ⊕ ℤw`. -/
def wedgeNorm (v w : ι → ℤ) : ℝ :=
  √(eNorm v ^ 2 * eNorm w ^ 2 - (dotR (toR v) (toR w)) ^ 2)

/-- `𝒢(x,y)`: gcd of the 2×2 minors of the matrix with columns `x, y`. -/
def gcdMinors2 (x y : ι → ℤ) : ℤ :=
  Finset.univ.gcd (fun ij : ι × ι => x ij.1 * y ij.2 - x ij.2 * y ij.1)

end vectors

/-! ## Integral lattices -/

section lattices
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `Λ_c = {y ∈ ℤ^ι : ⟨c,y⟩ = 0}`. -/
def latOrth (c : ι → ℤ) : Submodule ℤ (ι → ℤ) :=
  LinearMap.ker (Fintype.linearCombination ℤ c)

/-- `Λ_c^{(Q)} = {y ∈ ℤ^ι : ⟨c,y⟩ ≡ 0 mod Q}`. -/
def latMod (c : ι → ℤ) (Q : ℕ) : Submodule ℤ (ι → ℤ) :=
  Submodule.comap (Fintype.linearCombination ℤ c) (Submodule.span ℤ {(Q : ℤ)})

/-- The `i`-th successive minimum of an integral lattice for the Euclidean unit ball. -/
def lam (L : Submodule ℤ (ι → ℤ)) (i : ℕ) : ℝ :=
  sInf {r : ℝ | 0 ≤ r ∧ ∃ f : Fin i → ι → ℤ,
    (∀ j, f j ∈ L) ∧ LinearIndependent ℤ f ∧ ∀ j, eNorm (f j) ≤ r}

/-- The rank of an integral lattice. -/
def rk (L : Submodule ℤ (ι → ℤ)) : ℕ := Module.finrank ℤ L

/-- The determinant (covolume in its real span) of an integral lattice: `√det(Gram)` of a ℤ-basis. -/
def detL (L : Submodule ℤ (ι → ℤ)) : ℝ :=
  let b := (Submodule.basisOfPid (Pi.basisFun ℤ ι) L).2
  √(Matrix.det (Matrix.of fun i j => ∑ k, ((b i : ι → ℤ) k : ℝ) * ((b j : ι → ℤ) k : ℝ)))

/-- Number of lattice points of norm at most `T`. -/
def ballCount (L : Submodule ℤ (ι → ℤ)) (T : ℝ) : ℕ :=
  {v : ι → ℤ | v ∈ L ∧ eNorm v ≤ T}.ncard

/-- `𝔡_r(S)`: the least determinant of a rank-`r` sublattice of `ℤ^ι` containing `S`. -/
def dmin (r : ℕ) (S : Set (ι → ℤ)) : ℝ :=
  sInf {D : ℝ | ∃ L : Submodule ℤ (ι → ℤ), rk L = r ∧ S ⊆ L ∧ detL L = D}

end lattices

/-! ## Counting over the height ball -/

variable (d n : ℕ)

/-- Primitive coefficient vectors of norm at most `A` satisfying `P`. -/
def primSet (A : ℝ) (P : (Mon d n → ℤ) → Prop) : Set (Mon d n → ℤ) :=
  {a | IsPrim a ∧ eNorm a ≤ A ∧ P a}

/-- `#primSet` as a real number. -/
def primCount (A : ℝ) (P : (Mon d n → ℤ) → Prop) : ℝ := ((primSet d n A P).ncard : ℝ)

/-- Proportion of the height ball satisfying `P`. -/
def ratio (A : ℝ) (P : (Mon d n → ℤ) → Prop) : ℝ :=
  primCount d n A P / primCount d n A (fun _ => True)

/-! ## Solubility conditions -/

/-- `V(ℚ) ≠ ∅`, i.e. `f_a` has a nonzero integer zero. -/
def HasRatZero (a : Mon d n → ℤ) : Prop :=
  ∃ x : Fin (n + 1) → ℤ, x ≠ 0 ∧ formEval d n a x = 0

/-- `V(ℝ) ≠ ∅`. -/
def RealSol (a : Mon d n → ℤ) : Prop :=
  ∃ x : Fin (n + 1) → ℝ, x ≠ 0 ∧ formEval d n a x = 0

/-- `f_a` has a zero modulo `p^r` at a vector not divisible by `p`. -/
def PrimModZero (a : Mon d n → ℤ) (p r : ℕ) : Prop :=
  ∃ x : Fin (n + 1) → ℤ, (∃ i, ¬ (p : ℤ) ∣ x i) ∧ (p : ℤ) ^ r ∣ formEval d n a x

/-- Adelic solubility, in the exact form used by the challenge. -/
def AdelicSol (a : Mon d n → ℤ) : Prop :=
  HassePrincipleRandomFano.HasSolutionsIn (formOf d n a) HassePrincipleRandomFano.𝔸

/-- `r_p(w) = ⌈log w / log p⌉ + 1`. -/
def rOf (p : ℕ) (w : ℝ) : ℕ := Nat.clog p ⌈w⌉₊ + 1

/-- `w = log B / log log B`. -/
def wOf (B : ℝ) : ℝ := Real.log B / Real.log (Real.log B)

/-- `W = ∏_{p ≤ w} p^{r_p(w)}`. -/
def bigW (w : ℝ) : ℕ := ∏ p ∈ (Finset.range (⌊w⌋₊ + 1)).filter Nat.Prime, p ^ rOf p w

/-- `rad(W) = ∏_{p ≤ w} p`. -/
def radW (w : ℝ) : ℕ := ∏ p ∈ (Finset.range (⌊w⌋₊ + 1)).filter Nat.Prime, p

/-- Real solubility plus a primitive zero modulo `p^{r_p(w)}` for every `p ≤ w`
(equivalently `a mod W ∈ 𝔽^loc(W)`). -/
def LocSet (w : ℝ) (a : Mon d n → ℤ) : Prop :=
  RealSol d n a ∧ ∀ p : ℕ, p.Prime → (p : ℝ) ≤ w → PrimModZero d n a p (rOf p w)

/-! ## Counting functions of the paper -/

/-- `Ξ_{d,n}(B)`: primitive `x` with `‖x‖ ≤ B^{1/(n+1-d)}`. -/
def Xi (B : ℝ) : Set (Fin (n + 1) → ℤ) :=
  {x | IsPrim x ∧ eNorm x ≤ B ^ (1 / ((n : ℝ) + 1 - d))}

/-- `N_V(B)`, for `V` with coefficient vector `a`. -/
def NV (a : Mon d n → ℤ) (B : ℝ) : ℝ :=
  (1 / 2) * (({x ∈ Xi d n B | formEval d n a x = 0} : Set (Fin (n + 1) → ℤ)).ncard : ℝ)

/-- The localised counting function `N_V^loc(B)`. -/
def NVloc (a : Mon d n → ℤ) (B : ℝ) : ℝ :=
  (1 / 2) * (Real.log B * (bigW (wOf B) : ℝ) / eNorm a) *
    ∑ᶠ x ∈ ({x ∈ Xi d n B | ((bigW (wOf B) : ℕ) : ℤ) ∣ formEval d n a x ∧
        toR a ∈ Cgam (toR (veronese d n x)) (Real.log B)} : Set (Fin (n + 1) → ℤ)),
      1 / eNorm (veronese d n x)

/-- `σ(a;Q) = Q^{-n} #{b ∈ (ℤ/Q)^{n+1} unimodular : f_a(b) ≡ 0}`. -/
def sigmaLoc (a : Mon d n → ℤ) (Q : ℕ) : ℝ :=
  (({b : Fin (n + 1) → ZMod Q | Ideal.span (Set.range b) = ⊤ ∧ formEval d n a b = 0}.ncard : ℕ) : ℝ)
    / (Q : ℝ) ^ n

/-- `τ(a;γ) = γ · vol{u ∈ B_{n+1}(1) : a ∈ 𝒞_{ν(u)}^{(γ)}}`. -/
def tauArch (a : Mon d n → ℝ) (γ : ℝ) : ℝ :=
  γ * (MeasureTheory.volume {u : Fin (n + 1) → ℝ | rNorm u ≤ 1 ∧ a ∈ Cgam (veronese d n u) γ}).toReal

/-! ## Second-moment objects (§4) -/

/-- `Γ_{x,y} = Λ_{ν(x)} ∩ Λ_{ν(y)}`. -/
def Gam (x y : Fin (n + 1) → ℤ) : Submodule ℤ (Mon d n → ℤ) :=
  latOrth (veronese d n x) ⊓ latOrth (veronese d n y)

/-- `μ(x,y) = 3n² max(𝔡₂/𝔡₃, ‖x‖‖y‖/𝔡₂²)`. -/
def muXY (x y : Fin (n + 1) → ℤ) : ℝ :=
  3 * (n : ℝ) ^ 2 * max (dmin 2 {x, y} / dmin 3 {x, y}) (eNorm x * eNorm y / dmin 2 {x, y} ^ 2)

/-- `Ω_{d,n}(B)`: pairs of primitive vectors in the height range with `x ≠ ±y`. -/
def Omega (B : ℝ) : Set ((Fin (n + 1) → ℤ) × (Fin (n + 1) → ℤ)) :=
  {p | p.1 ∈ Xi d n B ∧ p.2 ∈ Xi d n B ∧ p.1 ≠ p.2 ∧ p.1 ≠ -p.2}

/-- `E_{d,n}(B) = Σ_{Ω(B)} 1/det Γ_{x,y}`. -/
def EE (B : ℝ) : ℝ := ∑ᶠ p ∈ Omega d n B, 1 / detL (Gam d n p.1 p.2)

/-- `Δ(x,y) = ‖ν(x)‖‖ν(y)‖ / det(ℤν(x) ⊕ ℤν(y))`. -/
def DeltaXY (x y : Fin (n + 1) → ℤ) : ℝ :=
  eNorm (veronese d n x) * eNorm (veronese d n y) / wedgeNorm (veronese d n x) (veronese d n y)

/-- `𝓔_{x,y}(B) = min(1, Δ²/α²) + 1_{𝒢(x,y) ∤ W/rad W}`. -/
def errXY (B : ℝ) (x y : Fin (n + 1) → ℤ) : ℝ :=
  min 1 (DeltaXY d n x y ^ 2 / Real.log B ^ 2) +
    if gcdMinors2 x y ∣ ((bigW (wOf B) / radW (wOf B) : ℕ) : ℤ) then 0 else 1

/-- `F_{d,n}(B)`. -/
def FF (B : ℝ) : ℝ := ∑ᶠ p ∈ Omega d n B, errXY d n B p.1 p.2 / detL (Gam d n p.1 p.2)

/-- Volume of the unit ball in `ℝ^k`. -/
def ballVol (k : ℕ) : ℝ :=
  (MeasureTheory.volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin k)) 1)).toReal

/-- `ι_{d,n} = V_{N-2} / (8 ζ(N-2))`. -/
def iotaDN : ℝ :=
  ballVol (NN d n - 2) / (8 * ∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ (NN d n - 2))

/-- The common main term of the three second moments, doubled for `±a`:
`2 ι_{d,n} A^{N-2} E_{d,n}(B)`. -/
def mainTerm (A B : ℝ) : ℝ := 2 * iotaDN d n * A ^ (NN d n - 2) * EE d n B

/-- `Δ_V^mix(B)`. -/
def DeltaMix (a : Mon d n → ℤ) (B : ℝ) : ℝ :=
  (1 / 2) * (Real.log B * (bigW (wOf B) : ℝ) / eNorm a) *
    ∑ᶠ x ∈ ({x ∈ Xi d n B | formEval d n a x = 0} : Set (Fin (n + 1) → ℤ)),
      1 / eNorm (veronese d n x)

/-- `Δ_V^loc(B)`. -/
def DeltaLoc (a : Mon d n → ℤ) (B : ℝ) : ℝ :=
  (1 / 2) * (Real.log B * (bigW (wOf B) : ℝ) / eNorm a) ^ 2 *
    ∑ᶠ x ∈ ({x ∈ Xi d n B | ((bigW (wOf B) : ℕ) : ℤ) ∣ formEval d n a x ∧
        toR a ∈ Cgam (toR (veronese d n x)) (Real.log B)} : Set (Fin (n + 1) → ℤ)),
      1 / eNorm (veronese d n x) ^ 2

/-- `D_{d,n}(A,B)` (over `±a`). -/
def Dglob (A B : ℝ) : ℝ :=
  ∑ᶠ a ∈ primSet d n A (fun _ => True), (NV d n a B ^ 2 - NV d n a B)

/-- `D^mix_{d,n}(A,B)` (over `±a`). -/
def Dmix (A B : ℝ) : ℝ :=
  ∑ᶠ a ∈ primSet d n A (fun _ => True), (NV d n a B * NVloc d n a B - DeltaMix d n a B)

/-- `D^loc_{d,n}(A,B)` (over `±a`). -/
def Dloc (A B : ℝ) : ℝ :=
  ∑ᶠ a ∈ primSet d n A (fun _ => True), (NVloc d n a B ^ 2 - DeltaLoc d n a B)

/-! ## Pair counts (§3.3–3.4) -/

/-- `ℓ_{r,n}(X,Y;Δ)`. -/
def ellXY (r : ℕ) (X Y Δ : ℝ) : ℕ :=
  {p : (Fin (n + 1) → ℤ) × (Fin (n + 1) → ℤ) | LinearIndependent ℤ ![p.1, p.2] ∧
    eNorm p.1 ≤ X ∧ eNorm p.2 ≤ Y ∧ dmin r {p.1, p.2} ≤ Δ}.ncard

/-- `ℓ^{(j)}(Z;Δ,M)` for quartic threefolds. -/
def ell44 (j : ℕ) (Z Δ M : ℝ) : ℕ :=
  {p : (Fin 5 → ℤ) × (Fin 5 → ℤ) | LinearIndependent ℤ ![p.1, p.2] ∧
    eNorm p.1 ≤ Z ∧ eNorm p.2 ≤ Z ∧ dmin 3 {p.1, p.2} ≤ Δ ∧ lam (Gam 4 4 p.1 p.2) j ≤ M}.ncard

end Work.HP
