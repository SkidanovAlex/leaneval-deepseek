import Submission.Work.ZASS.Defs

/-!
# Area ZASS: step Z6 leaf contracts (design pass 9, HB XI 1.8–1.12)

The leaf contracts of step Z6, copied verbatim from `Submission/Work/_design_gw/Core9Zass.lean`
(namespace `Work.GW2`, also used by `Submission/Work/CORE4/Defs.lean`, hence kept in its own
module here).  See `Submission/Work/NOTES_LEAD_gw_design9.md` §2 and `NOTES_ZASS.md` §3.4.

Main finding. `c₊ = c₋` (Z6.5′) does **not** come from the functional equation 1.9–1.10. It
comes from three facts:
* the involution law `S ∘ S = id`, which rules out `c₊` a non-square;
* for `d` odd, the absence of fixed points of an involution (two-point stabilizers have odd
  order `d`);
* for `d` even, the three-point rule applied to `g = f ∘ (h s)`, where `f : x ↦ x + 1` and
  `h s` is normalised so that `1 ↦ -1`. Then `g` permutes `0 ↦ ∞ ↦ 1 ↦ 0`, so `g³` fixes three
  points and `g³ = 1`. This is HB 1.11, p. 179 ("`(s₀f)³ = 1`"; `k = -1`), and HB 1.12 for `d`
  odd.

HB 1.9–1.10 *are* needed, but for a different step: the inversion `h^s = h⁻¹` when `d` is even
(Z6.4, i.e. `ZassInvertProp` for even `d`), which Z5 needs before any field exists.
-/

open scoped MatrixGroups LinearAlgebra.Projectivization

namespace Work.GW2

open Work.ZASS Work.Zassenhaus

/-! ## 0. Shared data -/

/-- The Z2–Z4 output (`Work.ZASS.exists_unipotent_structure`), minus the bijection `U ≃ X∖{∞}`.
-/
def ZassUData (G X : Type) [Group G] [MulAction G X] (p k : ℕ) (inf zero : X)
    (U : Subgroup G) : Prop :=
  U ≤ borel G inf ∧ Nat.card U = p ^ k ∧ (U.subgroupOf (borel G inf)).Normal ∧
    IsDirectDecomp (borel G inf) U (pairStab G inf zero) ∧
    FixedPointFreeConj U (pairStab G inf zero) ∧ IsMulCommutative U ∧ (∀ u ∈ U, u ^ p = 1)

/-! ## 1. Z6.4: inversion for even `d` (HB 1.8b/c, 1.9, 1.10, 1.11 first half)

`d := (p^k - 1)/2 = |G_{∞0}|`. Below, `H = pairStab G inf zero`. HB writes right actions:
HB's word `a b c` is Lean's `c * b * a`. -/

/-- HB 1.8(b)(c). If `d` is even, `H` has a unique involution `t`. It inverts `U`, is central in
`H`, and commutes with every `s` interchanging `∞` and `0`. Proof:
* `t` exists by Cauchy.
* `t` inverts `U` (HB V 8.18): `u ↦ u⁻¹ t u t⁻¹` is injective on `U` by fixed-point-freeness,
  hence onto.
* Two involutions `t, t'` of `H` both invert `U`, so `t t'` centralizes `U`, so `t t' = 1`.
* `h t h⁻¹` and `s t s⁻¹` are involutions of `H` (use `conjBy_mem_pairStab`), hence equal `t`. -/
def ZassCentralInvProp : Prop :=
  ∀ (G X : Type) [Group G] [Finite G] [MulAction G X] [Finite X] (p k : ℕ) [Fact p.Prime],
    Odd p → 5 ≤ p ^ k → ZassHyps2 G X (p ^ k) → Even ((p ^ k - 1) / 2) →
    ∀ (inf zero : X), inf ≠ zero → ∀ U : Subgroup G, ZassUData G X p k inf zero U →
      ∃ t ∈ pairStab G inf zero, orderOf t = 2 ∧ (∀ u ∈ U, t * u * t⁻¹ = u⁻¹) ∧
        (∀ t' ∈ pairStab G inf zero, orderOf t' = 2 → t' = t) ∧
        (∀ h ∈ pairStab G inf zero, h * t = t * h) ∧
        ∀ s : G, s • inf = zero → s • zero = inf → s * t = t * s

/-- HB 1.9 (functional equation), in Lean's left-action form. HB:
`(xs + k)s = (xh_k − k)s + ks`, i.e. `s f s = h_k f⁻¹ s f₂` (right actions), with
`k = 0f` and `0f₂ = ks`. Proof: by Z6.1 (`bruhat_decomposition`), `s u s = u₂ s u₁ h`. Evaluate
at `∞` to get `u₂ • 0 = s • (u • 0)`. Evaluate at `0` and use 1.8c to get `u₁ = u⁻¹`.
Brute-force checked in `PSL(2,p)`, `p = 5, 7, 11, 13, 17`. -/
def ZassBruhatFEProp : Prop :=
  ∀ (G X : Type) [Group G] [Finite G] [MulAction G X] [Finite X] (p k : ℕ) [Fact p.Prime],
    Odd p → 5 ≤ p ^ k → ZassHyps2 G X (p ^ k) → Even ((p ^ k - 1) / 2) →
    ∀ (inf zero : X), inf ≠ zero → ∀ U : Subgroup G, ZassUData G X p k inf zero U →
    ∀ s : G, orderOf s = 2 → s • inf = zero → s • zero = inf →
    ∀ u ∈ U, u ≠ 1 → ∃ h ∈ pairStab G inf zero, ∃ u₂ ∈ U,
      u₂ • zero = s • (u • zero) ∧ s * u * s = u₂ * s * u⁻¹ * h

/-- HB 1.10. The `h` of 1.9 is unique, by the unique expression in Z6.1; call it `h_u`.
* (a) `h_u = h_{u'}` iff `u' = u^{±1}`.
* `k s h_k = −k`, i.e. `h_u • (s • (u • 0)) = u⁻¹ • 0`.
* (c) Every `h ∈ H` is some `h_u`: by (a) the map `u ↦ h_u` takes `(q−1)/2 = |H|` values.

Brute-force checked in `PSL(2,p)`, `p = 5, 7, 11, 13, 17`. -/
def ZassHkProp : Prop :=
  ∀ (G X : Type) [Group G] [Finite G] [MulAction G X] [Finite X] (p k : ℕ) [Fact p.Prime],
    Odd p → 5 ≤ p ^ k → ZassHyps2 G X (p ^ k) → Even ((p ^ k - 1) / 2) →
    ∀ (inf zero : X), inf ≠ zero → ∀ U : Subgroup G, ZassUData G X p k inf zero U →
    ∀ s : G, orderOf s = 2 → s • inf = zero → s • zero = inf →
      (∀ u ∈ U, ∀ u' ∈ U, ∀ h ∈ pairStab G inf zero, ∀ u₂ ∈ U, ∀ u₂' ∈ U,
          u ≠ 1 → u' ≠ 1 →
          s * u * s = u₂ * s * u⁻¹ * h → s * u' * s = u₂' * s * u'⁻¹ * h →
          u' = u ∨ u' = u⁻¹) ∧
      (∀ u ∈ U, ∀ h ∈ pairStab G inf zero, ∀ u₂ ∈ U, u ≠ 1 →
          s * u * s = u₂ * s * u⁻¹ * h → h • (s • (u • zero)) = u⁻¹ • zero) ∧
      (∀ h ∈ pairStab G inf zero, ∃ u ∈ U, u ≠ 1 ∧ h • (s • (u • zero)) = u⁻¹ • zero)

/-- HB 1.11, first half. For `d` even, every `s` interchanging `a, b` inverts `G_{a,b}`.
* For an involution `s` and `h ∈ H`, pick `k` with `k s h = −k` (1.10c). By 1.8c,
  `(hs)(hs)` fixes `k`, `0` and `∞`, so `(hs)² = 1`, i.e. `s h s = h⁻¹`.
* A general `s` is `h₀ s₁` with `s₁` an involution (`ZassInvolutionSwapProp`). `H` is abelian
  (it is inverted by `s₁`), so `s` inverts `H` too.

The conclusion matches `ZassInvertProp` for even `d`. Together with `ZassCyclicOfCommProp` it
gives the cyclicity clause. -/
def ZassInvertEvenProp : Prop :=
  ∀ (G X : Type) [Group G] [Finite G] [MulAction G X] [Finite X] (p k : ℕ) [Fact p.Prime],
    Odd p → 5 ≤ p ^ k → ZassHyps2 G X (p ^ k) → Even ((p ^ k - 1) / 2) →
    ∀ a b : X, a ≠ b → ∀ s : G, s • a = b → s • b = a →
      Inverts s (MulAction.stabilizer G a ⊓ MulAction.stabilizer G b)

/-- An abelian two-point stabilizer is cyclic. It is an abelian Frobenius complement, so its
Sylow subgroups are cyclic (no `C_r × C_r` acts fixed-point-freely). Alternatively, `U` is an
irreducible faithful `𝔽_p H`-module (`eq_top_of_isConjInvariant`), so by Schur and Wedderburn
`H` embeds in the units of a finite field. Not true without commutativity (NOTES_ZASS §3,
`SL(2,3)` on `𝔽₇²`). -/
def ZassCyclicOfCommProp : Prop :=
  ∀ (G X : Type) [Group G] [Finite G] [MulAction G X] [Finite X] (p k : ℕ) [Fact p.Prime],
    Odd p → 5 ≤ p ^ k → ZassHyps2 G X (p ^ k) → ∀ a b : X, a ≠ b →
      IsMulCommutative (MulAction.stabilizer G a ⊓ MulAction.stabilizer G b : Subgroup G) →
      IsCyclic (MulAction.stabilizer G a ⊓ MulAction.stabilizer G b : Subgroup G)

/-- HB 1.5 (d odd), unchanged from `ZassInvertProp` but restricted to odd `d`: Burnside transfer
plus simplicity. This is the existing Z6.3 plan. -/
def ZassInvertOddProp : Prop :=
  ∀ (G X : Type) [Group G] [Finite G] [MulAction G X] [Finite X] (p k : ℕ) [Fact p.Prime],
    Odd p → 5 ≤ p ^ k → IsSimpleGroup G → ZassHyps2 G X (p ^ k) → Odd ((p ^ k - 1) / 2) →
    ∀ a b : X, a ≠ b →
      IsCyclic (MulAction.stabilizer G a ⊓ MulAction.stabilizer G b : Subgroup G) ∧
      ∀ s : G, s • a = b → s • b = a →
        Inverts s (MulAction.stabilizer G a ⊓ MulAction.stabilizer G b)

/-- `ZassInvertProp` at `q = p^k`. This is the only instance Z5 (`isCyclic_pairStab_of_zassInvert`)
uses. -/
def ZassInvertPKProp : Prop :=
  ∀ (G X : Type) [Group G] [Finite G] [MulAction G X] [Finite X] (p k : ℕ) [Fact p.Prime],
    Odd p → 5 ≤ p ^ k → IsSimpleGroup G → ZassHyps2 G X (p ^ k) → ∀ a b : X, a ≠ b →
      IsCyclic (MulAction.stabilizer G a ⊓ MulAction.stabilizer G b : Subgroup G) ∧
      ∀ s : G, s • a = b → s • b = a →
        Inverts s (MulAction.stabilizer G a ⊓ MulAction.stabilizer G b)

/-- Inverted by `s` implies commutative. -/
theorem isMulCommutative_of_inverts {G : Type} [Group G] {H : Subgroup G} {s : G}
    (hs : Inverts s H) : IsMulCommutative H := by
  refine ⟨⟨fun x y => ?_⟩⟩
  have hx := hs x x.2
  have hy := hs y y.2
  have hxy := hs (x * y) (H.mul_mem x.2 y.2)
  have key : (x : G)⁻¹ * (y : G)⁻¹ = (y : G)⁻¹ * (x : G)⁻¹ := by
    have : s * ((x : G) * y) * s⁻¹ = (s * x * s⁻¹) * (s * y * s⁻¹) := by group
    rw [this, hx, hy, mul_inv_rev] at hxy
    exact hxy
  apply Subtype.ext
  have := congrArg (fun z => z⁻¹) key
  simpa [mul_inv_rev] using this.symm

/-- Assembly of Z6.3/Z6.4: `ZassInvertPKProp` from the odd and even halves. -/
theorem zassInvertPK_of_parts (hOdd : ZassInvertOddProp) (hEven : ZassInvertEvenProp)
    (hCyc : ZassCyclicOfCommProp) (hSwap : ZassInvolutionSwapProp) : ZassInvertPKProp := by
  intro G X _ _ _ _ p k _ hp hq hs h a b hab
  rcases Nat.even_or_odd ((p ^ k - 1) / 2) with hd | hd
  · have hinv := hEven G X p k hp hq h hd a b hab
    obtain ⟨s, -, hsa, hsb⟩ := hSwap G X (p ^ k) (hp.pow) h a b hab
    exact ⟨hCyc G X p k hp hq h a b hab (isMulCommutative_of_inverts (hinv s hsa hsb)), hinv⟩
  · exact hOdd G X p k hp hq hs h hd a b hab

/-! ## 2. Coordinates (Z6.0) -/

/-- Field coordinates on `X` (from Z5, `exists_field_coordinates`). `Θ : X ≃ Option E`, with
`∞ ↦ none` and `0 ↦ some 0`. `U` acts by translations `y ↦ y + τ u` (`τ` bijective). `H` acts
by `y ↦ α h * y`, and the image of `α` is the set of nonzero squares. -/
structure ZassCoords (G X : Type) [Group G] [MulAction G X] (inf zero : X) (U : Subgroup G) where
  E : Type
  [fld : Field E]
  [fin : Fintype E]
  Θ : X ≃ Option E
  Θ_inf : Θ inf = none
  Θ_zero : Θ zero = some 0
  τ : U → E
  τ_bij : Function.Bijective τ
  trans : ∀ (u : U) (x : X), Θ ((u : G) • x) = (Θ x).map (· + τ u)
  α : pairStab G inf zero → E
  scale : ∀ (h : pairStab G inf zero) (x : X), Θ ((h : G) • x) = (Θ x).map (α h * ·)
  α_range : ∀ e : E, e ≠ 0 → ((∃ h, α h = e) ↔ IsSquare e)

attribute [instance] ZassCoords.fld ZassCoords.fin

/-- Z6.0: Z2–Z5 packaged as coordinates. Inputs: `exists_unipotent_structure` (`U ≃ X∖{∞}`
via `u ↦ u • 0`) and `exists_field_coordinates` (`Φ`, `φ`). Put `Θ (u • 0) := some (toAdd (Φ u))`
and `α h := φ h`. -/
def ZassCoordProp : Prop :=
  ∀ (G X : Type) [Group G] [Finite G] [MulAction G X] [Finite X] (p k : ℕ) [Fact p.Prime],
    Odd p → 5 ≤ p ^ k → ZassHyps2 G X (p ^ k) → ∀ (inf zero : X), inf ≠ zero →
      IsCyclic (pairStab G inf zero) →
      ∃ U : Subgroup G, ZassUData G X p k inf zero U ∧ Nonempty (ZassCoords G X inf zero U)

/-! ## 3. Z6.5′: reciprocity, `c₊ = c₋` -/

open Classical in
/-- `S` extended to `ℙ¹ = Option E`: `∞ ↦ 0`, `0 ↦ ∞`, `x ↦ S x`. -/
noncomputable def ZassSbar {E : Type} [Field E] (S : E → E) : Option E → Option E
  | none => some 0
  | some x => if x = 0 then none else some (S x)

/-- `g = f ∘ (h_a s)`: `y ↦ a² S(y) + 1` on `ℙ¹`. -/
noncomputable def ZassStep {E : Type} [Field E] (S : E → E) (a : E) (y : Option E) :
    Option E :=
  (ZassSbar S y).map (fun z => a ^ 2 * z + 1)

/-- **Z6.5′, pure field form.** Let `S : E∖0 → E∖0` satisfy:
* `S ∘ S = id`;
* `H`-equivariance, `S (a² x) = S x / a²`;
* (d odd) `S` has no fixed point;
* (three-point rule) for every `a ≠ 0`, the map `g = ZassStep S a`, if `g³` fixes `∞, 0, 1`,
  is the identity;
* (d even) `S` has a fixed point (choose `s` with two fixed points, `exists_swap_two_fixed`).

Then `S x = c / x` for one constant `c` with `-c` a square, so that `x ↦ c/x` is
`[[0, β], [-β⁻¹, 0]] ∈ PSL(2,E)` for `-c = β²`.

Proof. Equivariance gives `S x = c₊/x` on squares and `c₋/x` on non-squares.
1. If `c₊` is a non-square, `S (S x) = x` at a square `x` gives `c₋ = c₊`. Likewise for `c₋`.
   So `c₊` and `c₋` are in the same square class.
2. (d odd) If `c₊ = r²`, then one of `±r` is a square and is fixed by `S`, which is excluded.
   So `c₊` is a non-square; use 1.
3. (d even) If both are squares, scale by `a² = −1/c₊`: now `S₀ 1 = −1`, and `g = ZassStep S a`
   maps `0 ↦ ∞ ↦ 1 ↦ 0`, so `g³ = id`. Pick a square `e` with `e − 1` a non-square (such `e`
   exists: otherwise `E² ∪ {0}` is closed under `−1` and under square scaling, hence additive, but
   `(q+1)/2 ∤ q`). Then `g³ e = e` gives `S₀ (e − 1) = (k e + e − 1)/(e − 1)` with
   `k = −c₋/c₊`, and also `S₀ (e − 1) = k/(e − 1)`. Hence `k = −1`, i.e. `c₋ = c₊` (HB p. 179).
4. `−c` is a square: for d even `c = x₀²` (fixed point) and `−1` is a square; for d odd both
   `c` and `−1` are non-squares.

Model-checked exhaustively (all `(c₊, c₋)`) for `q = 5, 7, 9, 11, 13, 17, 19, 23, 25, 27, 29, 49`.
Without the three-point hypothesis it fails at `q = 5` (owner's order-720 example
`(c₊, c₋) = (1, 4)`). -/
def ZassReciprocityFieldProp : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] (S : E → E), (2 : E) ≠ 0 →
    (∀ x, x ≠ 0 → S x ≠ 0) → (∀ x, x ≠ 0 → S (S x) = x) →
    (∀ a x, a ≠ 0 → x ≠ 0 → S (a ^ 2 * x) = S x / a ^ 2) →
    (¬ IsSquare (-1 : E) → ∀ x, x ≠ 0 → S x ≠ x) →
    (∀ a : E, a ≠ 0 → (ZassStep S a)^[3] none = none →
      (ZassStep S a)^[3] (some 0) = some 0 → (ZassStep S a)^[3] (some 1) = some 1 →
      ∀ y, (ZassStep S a)^[3] y = y) →
    (IsSquare (-1 : E) → ∃ x, x ≠ 0 ∧ S x = x) →
    ∃ c : E, c ≠ 0 ∧ IsSquare (-c) ∧ ∀ x, x ≠ 0 → S x = c / x

/-- **Z6.5′, group form.** Transport `s` through `C.Θ`. Each hypothesis of the field form comes
from the following source:
* `S ∘ S = id`: `s² = 1`.
* Equivariance: `Inverts s H` and `C.scale`, `C.α_range`.
* No fixed point for d odd: a fixed point of the involution `s` gives two (`q + 1` even), so
  `s ∈ G_{x,y}`, which has odd order `d`.
* Three-point rule: `ZassStep S a` is the action of `u₁ * h * s`, where `τ u₁ = 1` and
  `α h = a²`. `ZassHyps2` (≤ 2 fixed points) gives `(u₁ h s)³ = 1`.
* Fixed point for d even: the hypothesis `hfix`. -/
def ZassReciprocityProp : Prop :=
  ∀ (G X : Type) [Group G] [Finite G] [MulAction G X] [Finite X] (p k : ℕ) [Fact p.Prime],
    Odd p → 5 ≤ p ^ k → ZassHyps2 G X (p ^ k) → ∀ (inf zero : X), inf ≠ zero →
    ∀ U : Subgroup G, ZassUData G X p k inf zero U → ∀ C : ZassCoords G X inf zero U,
    ∀ s : G, orderOf s = 2 → s • inf = zero → s • zero = inf →
      Inverts s (pairStab G inf zero) →
      (Even ((p ^ k - 1) / 2) → ∃ x : X, s • x = x) →
      ∃ c : C.E, c ≠ 0 ∧ IsSquare (-c) ∧
        ∀ (x : X) (y : C.E), y ≠ 0 → C.Θ x = some y → C.Θ (s • x) = some (c / y)

/-- Choice of `s`: `ZassInvolutionSwapProp` (proved), plus `exists_swap_two_fixed` (proved) for
`d` even. -/
def ZassGoodSwapProp : Prop :=
  ∀ (G X : Type) [Group G] [Finite G] [MulAction G X] [Finite X] (p k : ℕ) [Fact p.Prime],
    Odd p → 5 ≤ p ^ k → ZassHyps2 G X (p ^ k) → ∀ (inf zero : X), inf ≠ zero →
      ∃ s : G, orderOf s = 2 ∧ s • inf = zero ∧ s • zero = inf ∧
        (Even ((p ^ k - 1) / 2) → ∃ x : X, s • x = x)

/-! ## 4. Endgame (Z6.6) -/

/-- With `s` acting as `y ↦ c/y` (`-c = β²`), the image of `G` in `Sym(ℙ¹(E))` is generated by
the images of `G_∞ = U ⋊ H` and of `s` (Z6.1). Those images are images of PSL elements:
* `pslUnipotent`, `pslDiag` and `[[0, β], [-β⁻¹, 0]]`;
* the action formulas are in `psl_smul_ptOf.lean`;
* identify `E ≃+* GaloisField p k` by `FiniteField.ringEquivOfCardEq`.

`PSL(2,E)` acts faithfully on `ℙ¹`, so `G → Sym(ℙ¹)` factors through `PSL(2, GaloisField p k)`;
this factorisation is `Ψ`, and `Φ := Θ` composed with that identification. No order comparison is
needed for `ZassWeylProp` itself; `zassOdd2_of_weyl` does the orders. -/
def ZassEndgameProp : Prop :=
  ∀ (G X : Type) [Group G] [Finite G] [MulAction G X] [Finite X] (p k : ℕ) [Fact p.Prime],
    Odd p → 5 ≤ p ^ k → ZassHyps2 G X (p ^ k) → ∀ (inf zero : X), inf ≠ zero →
    ∀ U : Subgroup G, ZassUData G X p k inf zero U → ∀ C : ZassCoords G X inf zero U,
    ∀ s : G, s • inf = zero → s • zero = inf → ∀ c : C.E, c ≠ 0 → IsSquare (-c) →
      (∀ (x : X) (y : C.E), y ≠ 0 → C.Θ x = some y → C.Θ (s • x) = some (c / y)) →
      ∃ (Φ : X ≃ ℙ (GaloisField p k) (Fin 2 → GaloisField p k))
        (Ψ : G →* PSL(2, GaloisField p k)), ∀ (g : G) (x : X), Φ (g • x) = Ψ g • Φ x

/-! ## 5. Assembly (proved): `ZassWeylProp` from the leaves -/

theorem pairStab_eq_inf_stabilizer {G X : Type} [Group G] [MulAction G X] (a b : X) :
    pairStab G a b = MulAction.stabilizer G a ⊓ MulAction.stabilizer G b := by
  rw [pairStab, inf_comm]

theorem zassWeyl_of_parts (hInv : ZassInvertPKProp) (hCoord : ZassCoordProp)
    (hGood : ZassGoodSwapProp) (hRec : ZassReciprocityProp) (hEnd : ZassEndgameProp) :
    ZassWeylProp := by
  intro G X _ _ _ _ p k _ hp hq hs h
  have hcardX : Nat.card X = p ^ k + 1 := h.2.1
  have : Nontrivial X := by
    rw [← Finite.one_lt_card_iff_nontrivial, hcardX]; omega
  obtain ⟨inf, zero, hne⟩ := exists_pair_ne X
  obtain ⟨hcyc, hinvAll⟩ := hInv G X p k hp hq hs h inf zero hne
  have hcyc' : IsCyclic (pairStab G inf zero) := by
    rw [pairStab_eq_inf_stabilizer]; exact hcyc
  obtain ⟨U, hU, ⟨C⟩⟩ := hCoord G X p k hp hq h inf zero hne hcyc'
  obtain ⟨s, hs2, hsi, hsz, hfix⟩ := hGood G X p k hp hq h inf zero hne
  have hinvS : Inverts s (pairStab G inf zero) := by
    rw [pairStab_eq_inf_stabilizer]; exact hinvAll s hsi hsz
  obtain ⟨c, hc0, hcsq, hform⟩ := hRec G X p k hp hq h inf zero hne U hU C s hs2 hsi hsz
    hinvS hfix
  exact hEnd G X p k hp hq h inf zero hne U hU C s hsi hsz c hc0 hcsq hform

end Work.GW2
