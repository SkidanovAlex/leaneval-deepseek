import Submission.Work.RouteB.Final
import Submission.Work.RouteB.StarStructure

/-!
# PTCert — interfaces of the kernel-checked certificate pipeline

Design (see `FM3-DRIVE-annals_on_property_t.md`, `HANDOFF.md`):
a certificate is an element `Z = Σ star(ξ)ξ` built from *seeds* by a sign-character
Fourier construction (`FourierPrinciple`); `Z` and the target `T` are compared only after
averaging over the finite group `Sg` of signed-permutation automorphisms acting by
conjugation (`conjAvg`), and that comparison is reduced to *labelled sums*
(`LabelPrinciple`): every monomial carries a label and a conjugator in `Sg` mapping it to the
label's representative, and the coefficients of each label sum to zero.

This file contains only definitions and `Prop`s.
-/

open OnPropertyT Submission.FreeGroupAut Submission.RouteB Submission.RouteB.Edge
open scoped BigOperators

set_option autoImplicit false

namespace Submission.PTCert

/-! ## Generic group-ring notions -/

section Generic

variable {G : Type} [Group G]

/-- Conjugation-average over a finite set of group elements. -/
noncomputable def conjAvg (Sg : Finset G) (x : MonoidAlgebra ℝ G) : MonoidAlgebra ℝ G :=
  ∑ s ∈ Sg, MonoidAlgebra.of ℝ G s * x * MonoidAlgebra.of ℝ G s⁻¹

/-- A finset that is a subgroup: contains `1`, closed under products and inverses. -/
def IsFinSubgroup (Sg : Finset G) : Prop :=
  (1 : G) ∈ Sg ∧ (∀ s ∈ Sg, ∀ t ∈ Sg, s * t ∈ Sg) ∧ ∀ s ∈ Sg, s⁻¹ ∈ Sg

end Generic

/-- **(P1) Averaging principle.**  If `T` is `Sg`-conjugation invariant, `Z` is a sum of
hermitian squares, and the two have the same `Sg`-average, then `T` is a sum of hermitian
squares (`conjAvg Sg T = |Sg| • T`, and conjugates of squares are squares). -/
def AvgPrinciple : Prop :=
  ∀ (G : Type) [Group G] [DecidableEq G] (Sg : Finset G), IsFinSubgroup Sg →
    ∀ T Z : MonoidAlgebra ℝ G,
      (∀ s ∈ Sg, MonoidAlgebra.of ℝ G s * T * MonoidAlgebra.of ℝ G s⁻¹ = T) →
      IsSOS Z → conjAvg Sg Z = conjAvg Sg T → IsSOS T

/-- **(P2) Label principle.**  A finite linear combination of group elements whose terms
carry labels `lab t` and conjugators `s ∈ Sg` with `s * e t * s⁻¹ = r (lab t)`, and whose
coefficients sum to zero on every label, has zero `Sg`-average. -/
def LabelPrinciple : Prop :=
  ∀ (G : Type) [Group G] [DecidableEq G] (Sg : Finset G), IsFinSubgroup Sg →
    ∀ {ι : Type} (I : Finset ι) (c : ι → ℝ) (e : ι → G) (lab : ι → ℕ) (r : ℕ → G),
      (∀ t ∈ I, ∃ s ∈ Sg, s * e t * s⁻¹ = r (lab t)) →
      (∀ l : ℕ, ∑ t ∈ I.filter (fun t => lab t = l), c t = 0) →
      conjAvg Sg (∑ t ∈ I, c t • MonoidAlgebra.of ℝ G (e t)) = 0

/-- **(P3) Sign-character Fourier principle.**  `H ⊆ Sg` a finite subgroup, `χ k` functions
on `G` that are "characters on `H`" in the form `χ k h * χ k h' = χ k (h⁻¹ * h')`
(true for `±1`-valued characters of an elementary abelian 2-group), seeds `u x ∈ ℝG` and
positive semidefinite blocks `M k`.  Then the element
  `Σ_k Σ_{x,y} Σ_{g ∈ H} χ_k(g) M_k(x,y) • star(u x) * (g * u y * g⁻¹)`
has, up to the factor `|H|`, the same `Sg`-average as an explicit sum of hermitian squares
(namely `Σ_k Σ_v d • star ξ ξ` with `ξ = Σ_x v_x Σ_{h∈H} χ_k(h) • h u_x h⁻¹`). -/
def FourierPrinciple : Prop :=
  ∀ (G : Type) [Group G] [DecidableEq G] (Sg H : Finset G), IsFinSubgroup Sg →
    IsFinSubgroup H → H ⊆ Sg →
    ∀ {κ : Type} [Fintype κ] (χ : κ → G → ℝ),
      (∀ k, ∀ h ∈ H, ∀ h' ∈ H, χ k h * χ k h' = χ k (h⁻¹ * h')) →
    ∀ {n : ℕ} (u : Fin n → MonoidAlgebra ℝ G) (M : κ → Matrix (Fin n) (Fin n) ℝ),
      (∀ k, (M k).PosSemidef) →
      ∃ Z : MonoidAlgebra ℝ G, IsSOS Z ∧
        conjAvg Sg Z = (H.card : ℝ) • conjAvg Sg
          (∑ k, ∑ x, ∑ y, ∑ g ∈ H, (χ k g * M k x y) •
            (star (u x) * (MonoidAlgebra.of ℝ G g * u y * MonoidAlgebra.of ℝ G g⁻¹)))

/-- **(P4) Exact PSD certificate.**  `W = L · diag(d) · Lᵀ + R` with `d ≥ 0` and `R`
symmetric and diagonally dominant with nonnegative diagonal implies `W ⪰ 0`. -/
def LdlPrinciple : Prop :=
  ∀ {n : ℕ} (W L R : Matrix (Fin n) (Fin n) ℝ) (d : Fin n → ℝ),
    (∀ i, 0 ≤ d i) → R.transpose = R →
    (∀ i, ∑ j ∈ Finset.univ.erase i, |R i j| ≤ R i i) →
    W = L * Matrix.diagonal d * L.transpose + R → W.PosSemidef

/-! ## Signed permutations of `F_r` -/

/-- The product of the inversions `a_k ↦ a_k⁻¹` over the indices `k` with `s k = true`. -/
def signAut {r : ℕ} (s : Fin r → Bool) : MulAut (FreeGroup (Fin r)) :=
  (((List.finRange r).filter (fun k => s k)).map (fun k => sigma k)).prod

/-- The signed permutation `a_k ↦ a_{p k}^{±1}` (sign `-1` iff `s (p k)`). -/
def sigAut {r : ℕ} (p : Equiv.Perm (Fin r)) (s : Fin r → Bool) : MulAut (FreeGroup (Fin r)) :=
  signAut s * permAut p

/-- All signed permutations (the hyperoctahedral group, order `2^r r!`). -/
noncomputable def SigmaSet (r : ℕ) : Finset (MulAut (FreeGroup (Fin r))) := by
  classical
  exact Finset.univ.image (fun q : Equiv.Perm (Fin r) × (Fin r → Bool) => sigAut q.1 q.2)

/-- The sign flips (elementary abelian of order `2^r`). -/
noncomputable def SignSet (r : ℕ) : Finset (MulAut (FreeGroup (Fin r))) := by
  classical
  exact Finset.univ.image (fun s : Fin r → Bool => signAut s)

/-- **(S1)** Both are finite subgroups and `SignSet ⊆ SigmaSet`. -/
def SigmaGroupFacts (r : ℕ) : Prop :=
  IsFinSubgroup (SigmaSet r) ∧ IsFinSubgroup (SignSet r) ∧ SignSet r ⊆ SigmaSet r

/-! ## The letters: `B_1 = {1} ∪ SAutGen r`, indexed by natural numbers

Letter `0` is `1`; letter `1 + 4 * pairIdx i j + kind` is the Nielsen transvection of the
ordered pair `(i, j)`, `i ≠ j`, with `pairIdx i j = i * (r - 1) + (if j < i then j else j - 1)`
and `kind = 0,1,2,3` for `rho, rhoNeg, lam, lamNeg`.  `NB1 r = 1 + 4 r (r-1)` letters. -/

def NB1 (r : ℕ) : ℕ := 1 + 4 * r * (r - 1)

/-- Decoding of the ordered pair from `pairIdx`. -/
def pairOf (r q : ℕ) : ℕ × ℕ :=
  let i := q / (r - 1)
  let j' := q % (r - 1)
  (i, if j' < i then j' else j' + 1)

/-- The letter `k` as an element of `Aut(F_r)` (`1` for `k = 0` and out of range). -/
def b1 (r : ℕ) (k : ℕ) : MulAut (FreeGroup (Fin r)) :=
  if h0 : k = 0 then 1 else
  let q := (k - 1) / 4
  let kind := (k - 1) % 4
  let i := (pairOf r q).1
  let j := (pairOf r q).2
  if h : i < r ∧ j < r ∧ i ≠ j ∧ k < NB1 r then
    let fi : Fin r := ⟨i, h.1⟩
    let fj : Fin r := ⟨j, h.2.1⟩
    have hij : fi ≠ fj := fun e => h.2.2.1 (congrArg Fin.val e)
    if kind = 0 then rho fi fj hij else if kind = 1 then rhoNeg fi fj hij
    else if kind = 2 then lam fi fj hij else lamNeg fi fj hij
  else 1

/-- Letter of the inverse (flip the exponent bit). -/
def invL (k : ℕ) : ℕ := if k = 0 then 0 else ((k - 1) ^^^ 1) + 1

/-- Digit `i` (base 8) of a permutation code. -/
def pdig (pc i : ℕ) : ℕ := (pc >>> (3 * i)) % 8

/-- Bit `i` of a sign code. -/
def sbit (sc i : ℕ) : ℕ := (sc >>> i) % 2

/-- Action of the signed permutation with codes `(pc, sc)` on letter `k`:
pair `(i,j) ↦ (p i, p j)`; with `ti = sbit sc (p i)`, `tj = sbit sc (p j)` the kind bits
`(lamFlag, negFlag)` become `(lamFlag ^^^ ti, negFlag ^^^ ti ^^^ tj)`. -/
def actL (r pc sc k : ℕ) : ℕ :=
  if k = 0 then 0 else
  let q := (k - 1) / 4
  let kind := (k - 1) % 4
  let i := (pairOf r q).1
  let j := (pairOf r q).2
  let pi := pdig pc i
  let pj := pdig pc j
  let ti := sbit sc pi
  let tj := sbit sc pj
  let lf := (kind / 2) ^^^ ti
  let nf := (kind % 2) ^^^ ti ^^^ tj
  let q' := pi * (r - 1) + (if pj < pi then pj else pj - 1)
  1 + 4 * q' + 2 * lf + nf

/-- A valid permutation code: `r` base-8 digits, all `< r`, pairwise distinct. -/
def validPC (r pc : ℕ) : Bool :=
  (List.range r).all (fun i => decide (pdig pc i < r)) &&
  (List.range r).all (fun i => (List.range r).all (fun j => i == j || pdig pc i != pdig pc j)) &&
  decide (pc < 8 ^ r)

/-- **(S2) Letter action.**  Every valid code is realised by an element of `SigmaSet r`
acting on the letters by `actL`; letters invert by `invL`. -/
def LetterAction (r : ℕ) : Prop :=
  (∀ k < NB1 r, (b1 r k)⁻¹ = b1 r (invL k)) ∧
  ∀ pc sc : ℕ, validPC r pc = true → sc < 2 ^ r →
    ∃ g ∈ SigmaSet r, ∀ k < NB1 r, g * b1 r k * g⁻¹ = b1 r (actL r pc sc k)

/-- The sign flip with code `sc` lies in `SignSet r` and acts by `actL r (identity code) sc`. -/
def idPC (r : ℕ) : ℕ := ∑ i ∈ Finset.range r, i * 8 ^ i

/-- **(S3)** Sign flips as characters: the sign flip with code `sc` is in `SignSet`, and every
element of `SignSet` has a code. -/
def SignCodes (r : ℕ) : Prop :=
  ∀ g ∈ SignSet r, ∃ sc < 2 ^ r, ∀ k < NB1 r, g * b1 r k * g⁻¹ = b1 r (actL r (idPC r) sc k)

/-! ## Targets as Gram forms on the letters -/

/-- Laplacian coefficient vector on letters: `NB1 - 1` at `0`, `-1` elsewhere. -/
def cDelta (r : ℕ) (a : ℕ) : ℚ := if a = 0 then ((NB1 r : ℚ) - 1) else -1

/-- The edge `{i,j}` of a letter `a ≥ 1` (as an unordered pair `(min, max)`). -/
def edgeL (r a : ℕ) : ℕ × ℕ :=
  let ij := pairOf r ((a - 1) / 4)
  (min ij.1 ij.2, max ij.1 ij.2)

/-- Edge Laplacian coefficient vector: `8` at `0`, `-1` on the eight letters of edge `e`. -/
def cEdge (r : ℕ) (e : ℕ × ℕ) (a : ℕ) : ℚ := if a = 0 then 8 else if edgeL r a = e then -1 else 0

/-- `Q` of `Δ² - λΔ`: `c cᵀ - λ·(e₀ cᵀ + c e₀ᵀ)/2`. -/
def QDelta (r : ℕ) (lam : ℚ) (a b : ℕ) : ℚ :=
  cDelta r a * cDelta r b - lam * ((if a = 0 then cDelta r b else 0) + (if b = 0 then cDelta r a else 0)) / 2

/-- `Q` of `Adj + k·Op - μΔ`: sum over ordered pairs of distinct edges `(e,f)` of
`c_e c_fᵀ`, weighted `1` if `e,f` share a vertex and `k` otherwise, minus `μ`·(Laplacian part). -/
def QAdjOp (r : ℕ) (kop mu : ℚ) (a b : ℕ) : ℚ :=
  let edges := ((List.range r).flatMap (fun i => (List.range r).filterMap
    (fun j => if i < j then some (i, j) else none)))
  (edges.map (fun e => (edges.map (fun f =>
      if e = f then 0 else
      (if e.1 = f.1 ∨ e.1 = f.2 ∨ e.2 = f.1 ∨ e.2 = f.2 then 1 else kop) *
        cEdge r e a * cEdge r f b)).sum)).sum
  - mu * ((if a = 0 then cDelta r b else 0) + (if b = 0 then cDelta r a else 0)) / 2

/-- Gram form of a rational matrix on the letters `0 .. NB1-1`. -/
noncomputable def gramL (r : ℕ) (Q : ℕ → ℕ → ℚ) : MonoidAlgebra ℝ (MulAut (FreeGroup (Fin r))) :=
  ∑ a ∈ Finset.range (NB1 r), ∑ b ∈ Finset.range (NB1 r),
    ((Q a b : ℚ) : ℝ) • MonoidAlgebra.of ℝ _ ((b1 r a)⁻¹ * b1 r b)

/-- **(T1) Target expansions.** -/
def TargetExpansions (r : ℕ) : Prop :=
  (∀ lam : ℚ, deltaSub r r ^ 2 - (lam : ℝ) • deltaSub r r = gramL r (QDelta r lam)) ∧
  (∀ kop mu : ℚ, AdjPair r r + (kop : ℝ) • OpPair r r - (mu : ℝ) • deltaSub r r
      = gramL r (QAdjOp r kop mu))

/-- **(T2) Invariance of the targets** under conjugation by signed permutations. -/
def TargetInvariance (r : ℕ) : Prop :=
  ∀ g ∈ SigmaSet r,
    MonoidAlgebra.of ℝ _ g * deltaSub r r * MonoidAlgebra.of ℝ _ g⁻¹ = deltaSub r r ∧
    MonoidAlgebra.of ℝ _ g * AdjPair r r * MonoidAlgebra.of ℝ _ g⁻¹ = AdjPair r r ∧
    MonoidAlgebra.of ℝ _ g * OpPair r r * MonoidAlgebra.of ℝ _ g⁻¹ = OpPair r r

end Submission.PTCert
