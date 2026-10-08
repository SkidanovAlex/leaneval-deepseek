import Mathlib
import Submission.Work.ZassenhausSuzuki.CoreV2
import Submission.Work.ZassenhausSuzuki.twoPoint_inverted
import Submission.Work.ZassenhausSuzuki.twoPoint_card_eq_involutions
import Submission.Work.ZassenhausSuzuki.SzA.sq_eq
import Submission.Work.ZassenhausSuzuki.structure_equation
import Submission.Work.ZassenhausSuzuki.frel_product
import Submission.Work.ZassenhausSuzuki.frel_torus_all
import Submission.Work.ZassenhausSuzuki.ncard_involutions_of_mulEquiv

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `suzukiTitsOfFix`: reduction to Suzuki 1962 §4–5 / HB III XI §11.10–11.14

The requested statement

```
suzukiTitsOfFix (hsplit : IsSplitRankOne H Q t) (hzass : IsZassenhaus H) (hG : IsSimpleGroup G)
  (hθ1 : θ ≠ 1) (hθodd : Odd (orderOf θ)) (e : Q ≃* A(K,θ)) (htorus : …) 
  (hfix : ∀ x, θ x = x → x = 0 ∨ x = 1) : IsTitsTheta θ ∨ IsTitsTheta θ.symm
```

is **true**: a finite simple group with a split rank-one Zassenhaus configuration whose root
group is coordinatised by Higman's `A(K,θ)`, `K = GF(2^m)`, with the two-point stabiliser
acting through the torus `Λ`, is Suzuki's group `Sz(2^m)`; equivalently (Higman's Theorem 2,
`A(n,θ) ≅ A(n,φ)` only for `φ = θ^{±1}`) θ or θ⁻¹ is a Tits endomorphism.  The proof is
Suzuki 1962 §4–5, organised in Huppert–Blackburn III XI §11.10–11.14; `hfix` is HB 11.9
(`Fix θ = {0,1}`), the hard global step, and is *not* an extra assumption here (it is implied
by the conclusion, `hfix_of_conclusion`), but it is the input that the β/γ-computations use.

## What is established in this file (machine-checked)

1. **`hfix` is a consequence of the conclusion** (`hfix_of_conclusion`): the extra hypothesis
   cannot supply the missing content.
2. **Elementary (ZT)-facts**: `t² = 1` (`t_mul_self`), the book's map `f`
   (`FRel H t x y` ⟺ `t x t = m t y`, `m ∈ H`) is an involution (`frel_symm`), `Q` is a
   2-group (`isPGroup_two_of_mulEquiv`), and `f` intertwines the torus action with inversion
   (`Work.ZassenhausSuzuki.frel_torus_inv`).
3. **The σ-lemma** (`isTitsTheta_of_frel_sigma`, sharpened as `isTitsTheta_of_frel_center`):
   if in the `e`-coordinates `f` *is* the Suzuki map `σ = SzA.sigma θ`, then `IsTitsTheta θ`;
   the proof is a short computation from `frel_unique` and `σ(σ(0,b)) = (0, θ²b/b)`.  This is
   the last step of the road (HB 11.14's conclusion, obtained without its elimination).
4. **The field kernel** of the crux (HB III XI 11.12): `x ↦ x·θx` is a bijection of `Kˣ` when
   `orderOf θ` is odd (needed to normalise `e(g) = (1,d)` from `g² = (0,1)`), `ν ↦ θν/ν` is a
   bijection of `Kˣ` when `Fix θ = {0,1}`, and consequently
   `yν + (y+1)θν ≠ 0` for all `ν ∉ {0,1}` forces `y ∈ {0,1}`
   (`eq_zero_or_eq_one_of_forall`) — HB 11.12.
5. **The two coordinate computations of HB 11.11**: `commutator_coords` computes
   `(1,d)⁻¹·h_{λ⁻¹}(1,d) = (1+λ⁻¹, d+1+dλ⁻¹(θλ)⁻¹+(θλ)⁻¹)` in `A(K,θ)`, and
   `orbit_invariant` classifies the `Λ`-orbits of the non-central elements by `b/(a·θa)`.
   Combining 5 with 4: for the structure element `g = (1,d)` and `h ∈ D ∖ {1}` with torus
   parameter `λ`, the element `g⁻¹h⁻¹gh` is `D`-conjugate to `g` **unless** `d ∈ {0,1}`
   (the inequality of HB 11.11 collapses to `ν^{θ-1} = d/(d+1)` with `ν = μ+1`).

## The remaining crux, stated precisely

Let `g ∈ Q`, `j = g² ∈ Z(Q)^#` with `FRel H t j (g⁻¹)` be the **structure equation**
(Suzuki 1962 Prop. 9 = HB III 10.6 (a)–(d) plus 10.7b; the exclusion of `ord g = 2` uses
`3 ∤ |G|`, available since `|G| = (q²+1)q²(q-1)` with `q = 2^m`, `m` odd).  After a torus twist
`e ↦ h_μ ∘ e` (which preserves `htorus`) we may take `e(j) = (0,1)`, whence `e(g) = (1,d)`
by 4, and `e(f(j)) = (1,d+1)`.

The **terminal step** is the general computation HB 11.13(b) + 11.14: the functional equation
(Suzuki Prop. 5 = HB 11.10, the six relations among `α = f`, `β`, `γ`) evaluated at suitable
elements produces `θ(θ x) = x²` for a generator `x` of `K` over `𝔽₂`.  Equivalently, and this
is the shape used in this file: the configuration admits **σ-normalised coordinates**, i.e.
some admissible coordinatisation in which `f = σ`; the σ-lemma (3) then concludes.

Two facts limit what can be short-cut.  (a) The equivariance alone does *not* normalise `f`
to `σ`: from `f (0,1) = (1,0)` it gives `f (0,c) = (λ⁻¹, 0)` for `c = λ^{1+θ}`, whereas
`σ (0,c) = (λ/θ²λ, 0)` — the two agree precisely when `θ² =` Frobenius, i.e. the input and
the conclusion are equivalent, so the genuinely missing input is the *product* relation
(`f(xy)` vs `f(x)`, `f(y)`, HB 11.10 (6)), not the value of `f` at one point.
(b) The admissible coordinate systems (those satisfying `htorus`) are related by
`e ↦ Φ ∘ e` with `Φ ∈ Aut(A(K,θ))` normalising `Λ`; the corresponding maps `F = e f e⁻¹`
differ by `Φ σ Φ⁻¹`, so "`f = σ`" is not a statement about the configuration alone — it is
exactly the statement that the configuration is the Suzuki one.

**The road from here, and what is already available.**

* **The structure equation** (Suzuki Prop. 9 = HB III 10.6 (a)–(d) + 10.7b) is *proved* in
  `Submission/Work/ZassenhausSuzuki/structure_equation.lean` (module
  `Submission.Work.ZassenhausSuzuki.structure_equation`), imported here:

  `Work.ZassenhausSuzuki.structure_equation (hsplit) (hzass) (h2) (hexp4) (hcentral) (h3)` ⟹
  `∃ g : Q, g² ∈ Z(Q) ∧ g² ≠ 1 ∧ t · g² · t = g · t · g⁻¹`.

  Its hypotheses `hexp4` (`∀ x : Q, x⁴ = 1`), `hcentral` (involutions are central) and
  `h3` (`¬ 3 ∣ Nat.card G`) are supplied by the configuration: `hexp4`/`hcentral` come from
  `e : Q ≃* A(K,θ)` (Higman's group has exponent `4` and central involutions), and
  `¬ 3 ∣ Nat.card G` follows from `|G| = (q²+1)q²(q-1)`, `q = 2^m` with `m` odd
  (`|Ω| = |Q| + 1` via `qPt_surjective`, `|H| = |Q|·|D|` via `fact_exists`/`fact_unique`).
* **The torus is realised by `D`** (`exists_torus_action` below): every `λ ∈ Kˣ` is realised by
  some `d ∈ twoPoint H t`, so the coordinatisation can be twisted by `h_μ` at will; this is the
  step that normalises `e (g²) = (0,1)` in the reduction recorded in
  `NOTES_suzukiTitsOfFix.md` (which also records the two traps: the equivariance does not
  normalise `f` to `σ`, and admissible coordinate systems are only unique up to `Λ`-normalising
  automorphisms of `A(K,θ)`).
* **The product relation** of the functional equation (Suzuki Prop. 5 (11) = HB 11.10 b)(6))
  is *proved* in `Submission/Work/ZassenhausSuzuki/frel_product.lean`, imported here.
* **The `β`-relation** (Suzuki Prop. 5 (10) = HB 11.10 b)(5)) is delegated as
  `Work.ZassenhausSuzuki.frel_beta_image` (`frel_beta_image.lean`).  With it, the structure
  equation immediately gives the three special values of HB 11.13 (a):
  `f (g²) = g⁻¹` (the structure equation), `f g = g` (apply (5) at `x = g²`, whose `γ`-component
  is `1` because the `m` of the structure equation is `g ∈ Q`), and `f (g⁻¹) = g²` (`f² = id`).
* **What remains** is the terminal computation HB 11.13(b) + 11.14: the general value of `α = f`
  on `Q^#` (from HB 11.11's partition of `Q^#` into the `q+1` `D`-orbits, whose coordinate half
  is `commutator_coords` + `orbit_invariant` here) followed by evaluating the product relation
  at a generator of `K` over `𝔽₂` to get `θ² =` Frobenius; equivalently, the existence of
  *σ-normalised coordinates* (an admissible `e'` with `f = σ`, which by the σ-lemma (3) forces
  `IsTitsTheta`).  The disjunction in the conclusion comes from the `θ ↔ θ⁻¹` freedom of the
  admissible coordinate system (Higman's Theorem 2: `A(n,θ) ≅ A(n,φ)` only for `φ = θ^{±1}`),
  i.e. from HB 11.12's "replacing `θ` by `θ⁻¹` if necessary", whose field content is (4).-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.ZassenhausSuzuki

open LeanEval.GroupTheory.Defs
open Submission.Blueprint
open Work.RankOneUniqueness

/-! ## 1.  `hfix` follows from the conclusion -/

/-- In a field, `x² = x` forces `x = 0` or `x = 1`. -/
theorem eq_zero_or_eq_one_of_sq_eq_self {K : Type*} [Field K] {x : K} (h : x ^ 2 = x) :
    x = 0 ∨ x = 1 := by
  have h1 : x * (x - 1) = 0 := by
    have h2 : x ^ 2 - x = 0 := sub_eq_zero.mpr h
    calc x * (x - 1) = x ^ 2 - x := by ring
      _ = 0 := h2
  rcases mul_eq_zero.mp h1 with h2 | h2
  · exact Or.inl h2
  · exact Or.inr (sub_eq_zero.mp h2)

/-- A Tits endomorphism of a field fixes only `0` and `1`. -/
theorem fix_of_isTitsTheta {K : Type*} [Field K] (θ : K ≃+* K) (hθ : IsTitsTheta θ) :
    ∀ x : K, θ x = x → x = 0 ∨ x = 1 := by
  intro x hx
  refine eq_zero_or_eq_one_of_sq_eq_self ?_
  rw [← hθ.2 x, hx, hx]

/-- The inverse of a Tits endomorphism also fixes only `0` and `1`. -/
theorem fix_of_isTitsTheta_symm {K : Type*} [Field K] (θ : K ≃+* K)
    (hθ : IsTitsTheta θ.symm) : ∀ x : K, θ x = x → x = 0 ∨ x = 1 := by
  intro x hx
  have hx' : θ.symm x = x := by
    have h := congrArg (fun y => θ.symm y) hx
    simpa using h.symm
  refine eq_zero_or_eq_one_of_sq_eq_self ?_
  rw [← hθ.2 x, hx', hx']

/-- **`hfix` is a consequence of the conclusion of `suzukiTitsOfFix`.**  Hence the extra
hypothesis `hfix` of that statement is derivable from its conclusion and cannot help to prove
it: the statement is a restatement of the disjunction of `SuzukiTitsProp`. -/
theorem hfix_of_conclusion {K : Type*} [Field K] (θ : K ≃+* K)
    (h : IsTitsTheta θ ∨ IsTitsTheta θ.symm) :
    ∀ x : K, θ x = x → x = 0 ∨ x = 1 :=
  h.elim (fix_of_isTitsTheta θ) (fix_of_isTitsTheta_symm θ)

/-! ## 2.  With the `τ`-relation the conclusion is a short computation -/

section Main

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}

/-- `t` is an involution. -/
theorem t_mul_self (hsplit : IsSplitRankOne H Q t) : t * t = 1 := by
  have h : t ^ orderOf t = 1 := pow_orderOf_eq_one t
  rw [hsplit.invol, pow_two] at h
  exact h

/-- **The book's map `f` is an involution** (BG 3.2: `μ_a` is an involution).

If `t * x * t = m * t * y` with `m ∈ H`, then `t * y * t = m⁻¹ * t * x`: the relation `FRel`
is symmetric.  With `frel_unique` this says that the map `f` defined by `FRel` satisfies
`f (f x) = x`. -/
theorem frel_symm (hsplit : IsSplitRankOne H Q t) {x y : G} (h : FRel H t x y) :
    FRel H t y x := by
  have ht2 : t * t = 1 := t_mul_self hsplit
  obtain ⟨m, hmH, hm⟩ := h
  refine ⟨m⁻¹, Subgroup.inv_mem H hmH, ?_⟩
  have hm' : t * y = m⁻¹ * (t * x * t) := by rw [hm]; group
  calc t * y * t = (m⁻¹ * (t * x * t)) * t := by rw [hm']
    _ = m⁻¹ * t * x := by simp only [mul_assoc, ht2, mul_one]

/-- `A(K,θ)` is a `2`-group of exponent `4` in characteristic two (Higman: a Suzuki 2-group
has exponent `4`; here this is immediate from `x * x = ⟨0, a·θ a⟩`). -/
theorem isPGroup_two_szA {K : Type*} [Field K] [CharP K 2] (θ : K ≃+* K) :
    IsPGroup 2 (SzA K θ) := by
  intro x
  have h3 : (⟨0, x.a * θ x.a⟩ : SzA K θ) ^ 2 = 1 := by
    rw [pow_two]
    apply SzA.ext <;>
      simp [SzA.mul_a, SzA.mul_b, SzA.one_a, SzA.one_b, CharTwo.add_self_eq_zero]
  have h4 : x ^ 4 = 1 := by
    have h2 : x ^ 2 = (⟨0, x.a * θ x.a⟩ : SzA K θ) := by
      rw [pow_two]
      exact SzA.sq_eq θ x
    rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, h2]
    exact h3
  have hdvd : orderOf x ∣ 2 ^ 2 := by
    rw [pow_two]
    exact orderOf_dvd_iff_pow_eq_one.mpr h4
  obtain ⟨k, _, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  exact ⟨k, by rw [← hk]; exact pow_orderOf_eq_one x⟩

/-- The root group of a Suzuki configuration is a `2`-group: transport
`isPGroup_two_szA` along the coordinatisation `e`. -/
theorem isPGroup_two_of_mulEquiv {Q : Type*} [Group Q] {K : Type*} [Field K] [CharP K 2]
    (θ : K ≃+* K) (e : Q ≃* SzA K θ) : IsPGroup 2 Q :=
  IsPGroup.of_equiv (isPGroup_two_szA θ) e.symm

/-- Auxiliary field identity: `c / (c · c · θ c) = (c · θ c)⁻¹` for `c ≠ 0`. -/
private theorem div_self_mul_self_mul {K : Type*} [Field K] (θ : K ≃+* K) {c : K}
    (hc : c ≠ 0) (hθc : θ c ≠ 0) : c / (c * c * θ c) = (c * θ c)⁻¹ := by
  field_simp

/-- Auxiliary field identity: `(b / θ b) * θ (b / θ b) = b / θ (θ b)` for `b ≠ 0`. -/
private theorem div_mul_map_div {K : Type*} [Field K] (θ : K ≃+* K) {b : K} (hb : b ≠ 0)
    (hθb : θ b ≠ 0) (hθθb : θ (θ b) ≠ 0) :
    (b / θ b) * θ (b / θ b) = b / θ (θ b) := by
  have hmap : θ (b / θ b) = θ b / θ (θ b) := map_div₀ θ b (θ b)
  rw [hmap]
  field_simp

/-- **The corrected form of `suzukiTitsOfFix`.**

Suppose the book's map `f` — determined by `FRel H t x y`, i.e. `t x t = m · t · y` with
`m ∈ H` — is, in the coordinates `e : Q ≃* A(K,θ)`, the Suzuki map `σ = SzA.sigma θ` (this is
exactly the `frel` field of `IsSuzukiConfiguration`, Suzuki 1962 §4–5 / BG 5.15–5.21).
Then `θ` is a Tits endomorphism.

No Zassenhaus hypothesis, no torus hypothesis and no `hfix` is needed: the whole content is in
the `τ`-relation. -/
theorem isTitsTheta_of_frel_sigma (hsplit : IsSplitRankOne H Q t)
    (m : ℕ) (θ : GaloisField 2 m ≃+* GaloisField 2 m) (hθ1 : θ ≠ 1)
    (e : Q ≃* SzA (GaloisField 2 m) θ)
    (hrel : ∀ x : Q, x ≠ 1 → FRel H t (x : G) (((e.symm (SzA.sigma θ (e x)) : Q) : G))) :
    IsTitsTheta θ := by
  refine ⟨hθ1, ?_⟩
  -- `t` is an involution
  have ht2 : t * t = 1 := by
    have h : t ^ orderOf t = 1 := pow_orderOf_eq_one t
    rw [hsplit.invol, pow_two] at h
    exact h
  intro b
  by_cases hb : b = 0
  · rw [hb]; simp
  · set x : Q := e.symm (⟨0, b⟩ : SzA (GaloisField 2 m) θ) with hxdef
    set c : GaloisField 2 m := b / θ b with hcdef
    set y : Q := e.symm (⟨c, 0⟩ : SzA (GaloisField 2 m) θ) with hydef
    have hθb : θ b ≠ 0 := fun h => hb (θ.injective (by rw [h, map_zero]))
    have hθθb : θ (θ b) ≠ 0 := fun h => hθb (θ.injective (by rw [h, map_zero]))
    have hc : c ≠ 0 := by rw [hcdef]; exact div_ne_zero hb hθb
    have hθc : θ c ≠ 0 := fun h => hc (θ.injective (by rw [h, map_zero]))
    have hex : e x = (⟨0, b⟩ : SzA (GaloisField 2 m) θ) := by
      rw [hxdef, MulEquiv.apply_symm_apply]
    have hey : e y = (⟨c, 0⟩ : SzA (GaloisField 2 m) θ) := by
      rw [hydef, MulEquiv.apply_symm_apply]
    have hx1 : x ≠ 1 := by
      intro h
      have h1 : e x = 1 := by rw [h, map_one]
      rw [hex] at h1
      exact hb (by simpa using congrArg SzA.b h1)
    have hy1 : y ≠ 1 := by
      intro h
      have h1 : e y = 1 := by rw [h, map_one]
      rw [hey] at h1
      exact hc (by simpa using congrArg SzA.a h1)
    -- the value of `σ` at `(0,b)`
    have hsig : SzA.sigma θ (e x) = (⟨c, 0⟩ : SzA (GaloisField 2 m) θ) := by
      rw [hex, hcdef]
      ext
      · simp [SzA.sigma_a, SzA.N_mk]
      · simp [SzA.sigma_b, SzA.N_mk]
    have h1 : FRel H t (x : G) (y : G) := by
      have hxy : e.symm (SzA.sigma θ (e x)) = y := by rw [hsig, hydef]
      simpa [hxy] using hrel x hx1
    -- `f` is an involution, so `FRel H t y x`
    have h2 : FRel H t (y : G) (x : G) := by
      obtain ⟨mm, hmmH, hmm⟩ := h1
      refine ⟨mm⁻¹, Subgroup.inv_mem H hmmH, ?_⟩
      have hmm' : t * (y : G) = mm⁻¹ * (t * (x : G) * t) := by rw [hmm]; group
      calc t * (y : G) * t = (mm⁻¹ * (t * (x : G) * t)) * t := by rw [hmm']
        _ = mm⁻¹ * t * (x : G) := by simp only [mul_assoc, ht2, mul_one]
    -- the value of `σ` at `(c,0)`
    have hsig2 : SzA.sigma θ (e y) = (⟨0, (c * θ c)⁻¹⟩ : SzA (GaloisField 2 m) θ) := by
      rw [hey]
      ext
      · simp [SzA.sigma_a, SzA.N_mk]
      · simp only [SzA.sigma_b, SzA.N_mk, mul_zero, add_zero, map_zero]
        field_simp
    -- uniqueness of the book's map `f`
    have h4 : SzA.sigma θ (e y) = e x := by
      have hz : ((e.symm (SzA.sigma θ (e y)) : Q) : G) = (x : G) :=
        frel_unique hsplit (hrel y hy1) h2 (Subtype.coe_prop _) x.2
      have hz' : (e.symm (SzA.sigma θ (e y)) : Q) = x := Subtype.ext hz
      have := congrArg e hz'
      simpa using this
    -- the equation `b = (c·θ c)⁻¹`
    have hb_eq : (c * θ c)⁻¹ = b := by
      have h5 : (⟨0, (c * θ c)⁻¹⟩ : SzA (GaloisField 2 m) θ)
          = (⟨0, b⟩ : SzA (GaloisField 2 m) θ) := by
        rw [← hsig2, h4, hex]
      exact congrArg SzA.b h5
    -- `c·θ c = b/θ²b`
    have hcc : c * θ c = b / θ (θ b) := by
      rw [hcdef]
      exact div_mul_map_div θ hb hθb hθθb
    -- conclude `θ (θ b) = b²`
    have h5 : b / θ (θ b) = b⁻¹ := by
      have hb_eq' : c * θ c = b⁻¹ := by rw [← hb_eq, inv_inv]
      rw [← hcc]; exact hb_eq'
    have h6 : b * b = θ (θ b) := by
      have h7 : b = b⁻¹ * θ (θ b) := (div_eq_iff hθθb).mp h5
      have h8 := congrArg (fun z => b * z) h7
      rw [← mul_assoc, mul_inv_cancel₀ hb, one_mul] at h8
      exact h8
    rw [eq_comm, pow_two]
    exact h6

/-- **The reduced form: the crux is a statement about two `Λ`-orbits.**

The same conclusion as `isTitsTheta_of_frel_sigma`, but with the `σ`-relation assumed only on
`Z(Q)^# = A(K,θ)`-centre and on its `σ`-image — i.e. precisely BG 5.20 (a) and (b):
`f` maps the central involutions `(0,b)`, `b ≠ 0`, as `σ` does, and likewise their images.
This is the input that the hypotheses of `suzukiTitsOfFix` do *not* supply (no information
about the book's map `f` is available from `hsplit`, `hzass`, `e`, `htorus`, `hfix` alone);
producing it is the Suzuki partition computation (BG 5.15–5.20), the area's open `SuzukiFProp`.

The proof is the same computation as in `isTitsTheta_of_frel_sigma`: the two assumptions
instantiated at `b` give `FRel H t x (σ x)` and `FRel H t (σ x) (σ (σ x))` for
`x = e.symm (0,b)`, whence `σ (σ (0,b)) = (0,b)` and hence `θ (θ b) = b²`. -/
theorem isTitsTheta_of_frel_center (hsplit : IsSplitRankOne H Q t)
    (m : ℕ) (θ : GaloisField 2 m ≃+* GaloisField 2 m) (hθ1 : θ ≠ 1)
    (e : Q ≃* SzA (GaloisField 2 m) θ)
    (hcen : ∀ b : GaloisField 2 m, b ≠ 0 →
      FRel H t ((((e.symm (⟨0, b⟩ : SzA (GaloisField 2 m) θ)) : Q)) : G)
        ((((e.symm (⟨b / θ b, 0⟩ : SzA (GaloisField 2 m) θ)) : Q)) : G) ∧
      FRel H t ((((e.symm (⟨b / θ b, 0⟩ : SzA (GaloisField 2 m) θ)) : Q)) : G)
        ((((e.symm (⟨0, ((b / θ b) * θ (b / θ b))⁻¹⟩ : SzA (GaloisField 2 m) θ)) : Q)) : G)) :
    IsTitsTheta θ := by
  refine ⟨hθ1, ?_⟩
  have ht2 : t * t = 1 := t_mul_self hsplit
  intro b
  by_cases hb : b = 0
  · rw [hb]; simp
  · set x : Q := e.symm (⟨0, b⟩ : SzA (GaloisField 2 m) θ) with hxdef
    set c : GaloisField 2 m := b / θ b with hcdef
    set y : Q := e.symm (⟨c, 0⟩ : SzA (GaloisField 2 m) θ) with hydef
    have hθb : θ b ≠ 0 := fun h => hb (θ.injective (by rw [h, map_zero]))
    have hθθb : θ (θ b) ≠ 0 := fun h => hθb (θ.injective (by rw [h, map_zero]))
    have hc : c ≠ 0 := by rw [hcdef]; exact div_ne_zero hb hθb
    have hex : e x = (⟨0, b⟩ : SzA (GaloisField 2 m) θ) := by
      rw [hxdef, MulEquiv.apply_symm_apply]
    have hey : e y = (⟨c, 0⟩ : SzA (GaloisField 2 m) θ) := by
      rw [hydef, MulEquiv.apply_symm_apply]
    -- BG 5.20 (a): `f` on the central involutions
    have h1 : FRel H t (x : G) (y : G) := by
      simpa only [hxdef, hydef, hcdef] using (hcen b hb).1
    -- the value of `σ` at `(c,0)`
    have hsig2 : SzA.sigma θ (e y) = (⟨0, (c * θ c)⁻¹⟩ : SzA (GaloisField 2 m) θ) := by
      rw [hey]
      ext
      · simp [SzA.sigma_a, SzA.N_mk]
      · simp only [SzA.sigma_b, SzA.N_mk, mul_zero, add_zero, map_zero]
        field_simp
    -- BG 5.20 (b): `f` on the image of the central involutions
    have h3 : FRel H t (y : G) (((e.symm (SzA.sigma θ (e y)) : Q)) : G) := by
      have h := (hcen b hb).2
      have hz : e.symm (SzA.sigma θ (e y))
          = e.symm (⟨0, ((b / θ b) * θ (b / θ b))⁻¹⟩ : SzA (GaloisField 2 m) θ) := by
        rw [hsig2]
      rw [hz]
      simpa only [hydef, hcdef] using h
    -- `f` is an involution, so `FRel H t y x`
    have h2 : FRel H t (y : G) (x : G) := by
      obtain ⟨mm, hmmH, hmm⟩ := h1
      refine ⟨mm⁻¹, Subgroup.inv_mem H hmmH, ?_⟩
      have hmm' : t * (y : G) = mm⁻¹ * (t * (x : G) * t) := by rw [hmm]; group
      calc t * (y : G) * t = (mm⁻¹ * (t * (x : G) * t)) * t := by rw [hmm']
        _ = mm⁻¹ * t * (x : G) := by simp only [mul_assoc, ht2, mul_one]
    -- uniqueness of the book's map `f`
    have h4 : SzA.sigma θ (e y) = e x := by
      have hz : ((e.symm (SzA.sigma θ (e y)) : Q) : G) = (x : G) :=
        frel_unique hsplit h3 h2 (Subtype.coe_prop _) x.2
      have hz' : (e.symm (SzA.sigma θ (e y)) : Q) = x := Subtype.ext hz
      have h5 := congrArg e hz'
      simpa using h5
    -- the equation `(c·θ c)⁻¹ = b`
    have hb_eq : (c * θ c)⁻¹ = b := by
      have h5 : (⟨0, (c * θ c)⁻¹⟩ : SzA (GaloisField 2 m) θ)
          = (⟨0, b⟩ : SzA (GaloisField 2 m) θ) := by
        rw [← hsig2, h4, hex]
      exact congrArg SzA.b h5
    -- `c·θ c = b/θ²b`
    have hcc : c * θ c = b / θ (θ b) := by
      rw [hcdef]
      exact div_mul_map_div θ hb hθb hθθb
    have h5 : b / θ (θ b) = b⁻¹ := by
      have hb_eq' : c * θ c = b⁻¹ := by rw [← hb_eq, inv_inv]
      rw [← hcc]; exact hb_eq'
    have h6 : b * b = θ (θ b) := by
      have h7 : b = b⁻¹ * θ (θ b) := (div_eq_iff hθθb).mp h5
      have h8 := congrArg (fun z => b * z) h7
      rw [← mul_assoc, mul_inv_cancel₀ hb, one_mul] at h8
      exact h8
    rw [eq_comm, pow_two]
    exact h6

end Main

/-! ## 3.  The field kernel of the crux (HB III XI 11.12 and its prerequisites)

The route to `suzukiTitsOfFix` that this file documents and prepares runs through

* the **structure equation** of the rank-one configuration (Suzuki 1962 Prop. 9 = HB III 10.6):
  there are `g ∈ Q` and a central involution `j = g²` with `FRel H t j (g⁻¹)`, i.e.
  `t · g² · t = g · t · g⁻¹`;
* its **normalization** by a torus twist: `e(g²) = (0,1)`, whence `e(g) = (1,d)` and
  `e(f(g²)) = (1,d+1)`;
* the **non-conjugacy** of the commutator `g⁻¹d⁻¹gd` from `g` for every `d ∈ D ∖ {1}`
  (HB III XI 11.11), which in the coordinates reads
  `1 + d·μ + (d+1)·μ^θ ≠ 0` for all `μ ∈ K ∖ {0,1}`;
* the **field lemma** below (`eq_zero_or_eq_one_of_forall`), which converts that inequality into
  `d ∈ {0,1}`, i.e. `f` sends the central involution `(0,1)` to `(1,0)` (or, after the
  `θ ↦ θ⁻¹` transport `szA_symm_equiv`, to the corresponding value in the inverse coordinates).

The last two facts, together with the equivariance `frel_torus_inv` and the Suzuki map, are
what the assembly needs; the present file provides the field dictionary

* `units_mul_map_injective` / `units_mul_map_surjective` (`x ↦ x·θx` is a bijection of `Kˣ`
  for `θ` of odd order) — used to normalize `e(g) = (1,d)` from `g² = (0,1)`;
* `units_div_map_injective` / `units_div_map_surjective` (`ν ↦ θν/ν` is a bijection of `Kˣ`
  when `Fix θ = {0,1}`) — the engine of HB 11.12;
* `eq_zero_or_eq_one_of_forall` — HB III XI 11.12 in field form;
* `commutator_coords` and `orbit_invariant` — the two coordinate computations of HB 11.11. -/

section Field

variable {K : Type*} [Field K]

/-- Iterating the automorphism `θ` is the same as applying its `n`-th power. -/
private lemma coe_pow_apply (θ : K ≃+* K) (n : ℕ) (x : K) :
    (θ ^ n) x = (⇑θ)^[n] x := by
  induction n generalizing x with
  | zero => rfl
  | succ j ih =>
      show (θ ^ j) (θ x) = (⇑θ)^[j+1] x
      rw [Function.iterate_succ_apply]
      exact ih (θ x)

/-- **`x ↦ x · θ x` is injective on `Kˣ` when `θ` has odd order** (HB III, VIII 6.9).

If `x·θx = y·θy` then `t := x/y` satisfies `t·θt = 1`, hence `θt = t⁻¹` and then
`θ^{2j}(t) = t`, `θ^{2j+1}(t) = t⁻¹` by induction; for `d = orderOf θ` odd this gives
`t = θ^{d}(t) = t⁻¹`, i.e. `t² = 1`, and `t = 1` in characteristic two. -/
theorem units_mul_map_injective [CharP K 2] (θ : K ≃+* K) (hodd : Odd (orderOf θ)) :
    Function.Injective (fun x : Kˣ => x * Units.map θ.toMonoidHom x) := by
  intro x y hxy
  have hxyK : (x : K) * θ (x : K) = (y : K) * θ (y : K) := by
    have h := congrArg (fun u : Kˣ => (u : K)) hxy
    simpa [Units.val_mul] using h
  have hx0 : (x : K) ≠ 0 := Units.ne_zero x
  have hy0 : (y : K) ≠ 0 := Units.ne_zero y
  have hθy0 : θ (y : K) ≠ 0 := fun h => hy0 (θ.injective (by rw [h, map_zero]))
  set t : K := (x : K) / (y : K) with ht_def
  have ht0 : t ≠ 0 := ht_def ▸ div_ne_zero hx0 hy0
  have ht : t * θ t = 1 := by
    rw [ht_def, map_div₀, div_mul_div_comm, hxyK]
    exact div_self (mul_ne_zero hy0 hθy0)
  have hθt : θ t = t⁻¹ := eq_inv_of_mul_eq_one_right ht
  have hiter : ∀ j : ℕ, (⇑θ)^[2 * j] t = t ∧ (⇑θ)^[2 * j + 1] t = t⁻¹ := by
    intro j
    induction j with
    | zero => exact ⟨rfl, hθt⟩
    | succ k ih =>
        obtain ⟨h1, h2⟩ := ih
        have h3 : θ t⁻¹ = t := by rw [map_inv₀, hθt, inv_inv]
        constructor
        · rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring, Function.iterate_succ_apply', h2, h3]
        · rw [show 2 * (k + 1) + 1 = 2 * (k + 1) + 1 by ring,
              Function.iterate_succ_apply', show 2 * (k + 1) = 2 * k + 1 + 1 by ring,
              Function.iterate_succ_apply', h2, h3, hθt]
  obtain ⟨k, hk⟩ := hodd
  have hpow : (⇑θ)^[2 * k + 1] t = t := by
    rw [← coe_pow_apply θ (2 * k + 1) t, ← hk, pow_orderOf_eq_one]
    rfl
  have htinv : t = t⁻¹ := by
    have h2 := (hiter k).2
    rw [hpow] at h2
    exact h2
  have hsq : t * t = 1 := by
    have h := congrArg (fun u => t * u) htinv
    rw [mul_inv_cancel₀ ht0] at h
    exact h
  have ht1 : t = 1 := by
    have hsq' : (t + 1) * (t + 1) = 0 := by
      have h1 : (t + 1) * (t + 1) = t * t + (t + t) + 1 := by ring
      rw [h1, hsq, CharTwo.add_self_eq_zero t, add_zero, CharTwo.add_self_eq_zero 1]
    have h2 : t + 1 = 0 := mul_self_eq_zero.mp hsq'
    have h3 : t = -1 := by linear_combination h2
    rw [h3, neg_eq_iff_add_eq_zero]
    exact CharTwo.add_self_eq_zero 1
  have hdiv1 : (x : K) / (y : K) = 1 := by
    rw [← ht_def]
    exact ht1
  exact Units.ext ((div_eq_one_iff_eq hy0).mp hdiv1)

/-- **`x ↦ x · θ x` is surjective on `Kˣ`** when `θ` has odd order and `K` is finite. -/
theorem units_mul_map_surjective [CharP K 2] [Finite K] (θ : K ≃+* K)
    (hodd : Odd (orderOf θ)) :
    Function.Surjective (fun x : Kˣ => x * Units.map θ.toMonoidHom x) :=
  Finite.injective_iff_surjective.mp (units_mul_map_injective θ hodd)

/-- In characteristic two with `θ` of odd order, `a · θ a = 1` forces `a = 1`. -/
theorem eq_one_of_mul_map_eq_one [CharP K 2] (θ : K ≃+* K) (hodd : Odd (orderOf θ))
    {a : K} (ha : a ≠ 0) (h : a * θ a = 1) : a = 1 := by
  have h1 : (Units.mk0 a ha) * Units.map θ.toMonoidHom (Units.mk0 a ha)
      = (1 : Kˣ) * Units.map θ.toMonoidHom (1 : Kˣ) := by
    ext
    simpa [Units.val_mul] using h
  have h2 := units_mul_map_injective θ hodd h1
  simpa using congrArg (fun u : Kˣ => (u : K)) h2

/-- **`ν ↦ θ ν / ν` is injective on `Kˣ` when `Fix θ = {0,1}`** (HB III XI 11.12).

The map is a homomorphism `Kˣ → Kˣ` whose kernel is `Fix θ ∩ Kˣ = {1}`. -/
theorem units_div_map_injective (θ : K ≃+* K)
    (hfix : ∀ x : K, θ x = x → x = 0 ∨ x = 1) :
    Function.Injective (fun v : Kˣ => Units.map θ.toMonoidHom v / v) := by
  intro x y hxy
  have hxyK : θ (x : K) / (x : K) = θ (y : K) / (y : K) := by
    have h := congrArg (fun u : Kˣ => (u : K)) hxy
    simpa [Units.val_div_eq_div_val] using h
  have hx0 : (x : K) ≠ 0 := Units.ne_zero x
  have hy0 : (y : K) ≠ 0 := Units.ne_zero y
  have hθy0 : θ (y : K) ≠ 0 := fun h => hy0 (θ.injective (by rw [h, map_zero]))
  have hdiv : θ ((x : K) / (y : K)) = (x : K) / (y : K) := by
    rw [map_div₀, div_eq_div_iff hθy0 hy0]
    rw [div_eq_div_iff hx0 hy0] at hxyK
    rw [mul_comm (x : K) (θ (y : K))]
    exact hxyK
  rcases hfix ((x : K) / (y : K)) hdiv with h | h
  · exact absurd h (div_ne_zero hx0 hy0)
  · exact Units.ext ((div_eq_one_iff_eq hy0).mp h)

/-- **`ν ↦ θ ν / ν` is surjective on `Kˣ`** when `Fix θ = {0,1}` and `K` is finite. -/
theorem units_div_map_surjective [Finite K] (θ : K ≃+* K)
    (hfix : ∀ x : K, θ x = x → x = 0 ∨ x = 1) :
    Function.Surjective (fun v : Kˣ => Units.map θ.toMonoidHom v / v) :=
  Finite.injective_iff_surjective.mp (units_div_map_injective θ hfix)

/-- **HB III XI 11.12, field form.**  Let `θ` be an automorphism of the finite field `K` with
`Fix θ = {0,1}`.  If `y ν + (y+1) θ ν ≠ 0` for every `ν ∉ {0,1}`, then `y ∈ {0,1}`.

This is the counting/algebra step of HB 11.12: for `y ∉ {0,1}` the equation
`θ ν / ν = y/(y+1)` has a solution `ν ∈ Kˣ`, and `ν = 1` is excluded because `y ≠ y+1`;
substituting it into `y ν + (y+1) θ ν` gives `y ν + y ν = 0`, a contradiction. -/
theorem eq_zero_or_eq_one_of_forall [CharP K 2] (θ : K ≃+* K) [Finite K]
    (hfix : ∀ x : K, θ x = x → x = 0 ∨ x = 1) {y : K}
    (h : ∀ ν : K, ν ≠ 0 → ν ≠ 1 → y * ν + (y + 1) * θ ν ≠ 0) : y = 0 ∨ y = 1 := by
  by_contra hy
  push_neg at hy
  obtain ⟨hy0, hy1⟩ := hy
  have hy10 : y + 1 ≠ 0 := by
    intro h1
    have h2 : y = -1 := by linear_combination h1
    refine hy1 ?_
    rw [h2, neg_eq_iff_add_eq_zero]
    exact CharTwo.add_self_eq_zero 1
  obtain ⟨v, hv⟩ := units_div_map_surjective θ hfix
    (Units.mk0 (y / (y + 1)) (div_ne_zero hy0 hy10))
  have hvK : θ (v : K) / (v : K) = y / (y + 1) := by
    have hc := congrArg (fun u : Kˣ => (u : K)) hv
    simpa [Units.val_div_eq_div_val] using hc
  have hv0 : (v : K) ≠ 0 := Units.ne_zero v
  have hθv : θ (v : K) * (y + 1) = y * (v : K) := by
    rw [div_eq_div_iff hv0 hy10] at hvK
    exact hvK
  have hv1 : (v : K) ≠ 1 := by
    intro h1
    have h2 : θ (v : K) * (y + 1) = y * (v : K) := hθv
    rw [h1, map_one, mul_one] at h2
    have h3 : y + 1 = y := by linear_combination h2
    have h4 : (1 : K) = 0 := by linear_combination h3
    exact one_ne_zero h4
  refine h (v : K) hv0 hv1 ?_
  have h' : (y + 1) * θ (v : K) = y * (v : K) := by
    rw [mul_comm (y + 1), hθv]
  rw [h']
  exact CharTwo.add_self_eq_zero _

end Field

/-! ## 3b.  The generic representative and value of HB III XI 11.13 (b)

`Xrep θ ν = ⟨1+ν, θν·(1+ν)⟩` is the generic `D`-orbit representative (the coordinate form of
`g⁻¹·d⁻¹·g·d` for `d ∈ D` realising `h_ν`, `ν ≠ 1`), and `Xval θ ν ξ` is the value of the book's
map `f` at it that HB 11.13 (b) forces (proved as `Work.ZassenhausSuzuki.frel_generic_value_eps`),
where `ξ` is the auxiliary unit with `ξ·θξ = 1 + ν⁻¹·θ(ν⁻¹)`. -/

/-- The generic `D`-orbit representative `X_ν = (1+ν, θν·(1+ν))` of HB 11.13 (b). -/
def Xrep {K : Type*} [Field K] (θ : K ≃+* K) (nu : K) : SzA K θ :=
  ⟨1 + nu, θ nu * (1 + nu)⟩

/-- The value of the book's map `f` at `X_ν` forced by HB 11.13 (b). -/
def Xval {K : Type*} [Field K] (θ : K ≃+* K) (nu xi : K) : SzA K θ :=
  ⟨nu⁻¹ ^ 2 * xi⁻¹ + nu⁻¹, θ nu⁻¹ * (nu⁻¹ ^ 2 * xi⁻¹ + nu⁻¹)⟩

@[simp] theorem Xrep_a {K : Type*} [Field K] (θ : K ≃+* K) (nu : K) :
    (Xrep θ nu).a = 1 + nu := rfl

@[simp] theorem Xrep_b {K : Type*} [Field K] (θ : K ≃+* K) (nu : K) :
    (Xrep θ nu).b = θ nu * (1 + nu) := rfl

@[simp] theorem Xval_a {K : Type*} [Field K] (θ : K ≃+* K) (nu xi : K) :
    (Xval θ nu xi).a = nu⁻¹ ^ 2 * xi⁻¹ + nu⁻¹ := rfl

@[simp] theorem Xval_b {K : Type*} [Field K] (θ : K ≃+* K) (nu xi : K) :
    (Xval θ nu xi).b = θ nu⁻¹ * (nu⁻¹ ^ 2 * xi⁻¹ + nu⁻¹) := rfl

/-! ## 4.  The two coordinate computations of HB III XI 11.11

`commutator_coords` is the group-theoretic computation `(1,d)⁻¹ · h_{λ⁻¹}(1,d)` in `A(K,θ)`;
`orbit_invariant` is the classification of the `Λ`-orbits on the non-central elements of
`A(K,θ)` by the invariant `b/(a·θa)`.  Together they turn HB 11.11's non-conjugacy statement
into the field inequality of `eq_zero_or_eq_one_of_forall`. -/

/-- **Coordinate form of the commutator `g⁻¹·d⁻¹·g·d`** for `g = (1,d)` and the torus element
`h_λ` (HB III XI 11.11/11.12); characteristic two is essential (`(1,d)⁻¹ = (-1,1-d)`). -/
theorem commutator_coords {K : Type*} [Field K] [CharP K 2] (θ : K ≃+* K) (d lam : K)
    (hlam : lam ≠ 0) :
    (⟨1, d⟩ : SzA K θ)⁻¹ * SzA.hLam θ lam⁻¹ ⟨1, d⟩
      = ⟨1 + lam⁻¹, d + 1 + d * lam⁻¹ * θ lam⁻¹ + θ lam⁻¹⟩ := by
  have hneg : ∀ x : K, -x = x := fun x => by
    rw [neg_eq_iff_add_eq_zero]
    exact CharTwo.add_self_eq_zero x
  ext
  · simp only [SzA.mul_a, SzA.inv_a, SzA.hLam_a, hneg]
    ring
  · simp only [SzA.mul_a, SzA.mul_b, SzA.inv_a, SzA.inv_b, SzA.hLam_a, SzA.hLam_b, hneg,
      map_one]
    ring

/-- **The `Λ`-orbits of the non-central elements of `A(K,θ)`** are classified by the invariant
`b/(a·θ a)` (the `h_λ`-orbits of `A(K,θ) ∖ Z(A(K,θ))`). -/
theorem orbit_invariant {K : Type*} [Field K] (θ : K ≃+* K) {a b a' b' : K}
    (ha : a ≠ 0) (ha' : a' ≠ 0) :
    (∃ lam : K, lam ≠ 0 ∧ a' = lam * a ∧ b' = lam * θ lam * b) ↔
      b / (a * θ a) = b' / (a' * θ a') := by
  have hθa : θ a ≠ 0 := fun hh => ha (θ.injective (by rw [hh, map_zero]))
  have hθa' : θ a' ≠ 0 := fun hh => ha' (θ.injective (by rw [hh, map_zero]))
  constructor
  · rintro ⟨lam, hlam, rfl, rfl⟩
    have hθlam : θ lam ≠ 0 := fun hh => hlam (θ.injective (by rw [hh, map_zero]))
    rw [map_mul]
    field_simp
  · intro h
    refine ⟨a' / a, div_ne_zero ha' ha, by field_simp, ?_⟩
    rw [map_div₀]
    field_simp at h ⊢
    rw [h]


/-! ## 5.  The torus `Λ` is realised by `D = twoPoint H t`

The hypothesis `htorus` only says that each `d ∈ D` acts on `Q` through *some* torus element.
The converse — every `λ` is realised — is what a coordinatisation change `e ↦ h_μ ∘ e` uses,
and it is the content of `torusLambda_surjective` (`frel_torus_all.lean`), whose two extra
hypotheses (`Q ≠ ⊥`, `|D| = |Kˣ|`) are supplied here by `e : Q ≃* A(K,θ)`. -/

/-- **Every torus element is realised by an element of `D = twoPoint H t`.** -/
theorem exists_torus_action {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (hsplit : IsSplitRankOne H Q t) (hzass : IsZassenhaus H)
    {m : ℕ} {θ : GaloisField 2 m ≃+* GaloisField 2 m} {e : Q ≃* SzA (GaloisField 2 m) θ}
    (htorus : ∀ d : G, d ∈ twoPoint H t → ∃ lam : (GaloisField 2 m)ˣ, ∀ x : Q,
      ∃ y : Q, (y : G) = d * (x : G) * d⁻¹ ∧
        e y = SzA.hLam θ (lam : GaloisField 2 m) (e x)) :
    ∀ lam : (GaloisField 2 m)ˣ, ∃ d : G, d ∈ twoPoint H t ∧
      ∀ x : Q, (((e.symm (SzA.hLam θ (lam : GaloisField 2 m) (e x)) : Q)) : G)
        = d * (x : G) * d⁻¹ := by
  classical
  haveI : Finite ↥Q := Subtype.finite
  haveI hSzA : Finite (SzA (GaloisField 2 m) θ) := Finite.of_equiv ↥Q e.toEquiv
  haveI hK : Finite (GaloisField 2 m) :=
    Finite.of_injective (fun k : GaloisField 2 m => (⟨k, 0⟩ : SzA (GaloisField 2 m) θ))
      (fun a b hab => by simpa using congrArg SzA.a hab)
  haveI hKunits : Finite (GaloisField 2 m)ˣ :=
    Finite.of_injective (fun u : (GaloisField 2 m)ˣ => (u : GaloisField 2 m))
      (fun a b hab => Units.ext hab)
  have hQ : Q ≠ ⊥ := by
    intro hbot
    have h1 : (e.symm (⟨1, 0⟩ : SzA (GaloisField 2 m) θ) : Q) = 1 :=
      Subtype.ext (Subgroup.mem_bot.mp (hbot ▸ (e.symm (⟨1, 0⟩ : SzA _ θ)).2))
    have h2 : (⟨1, 0⟩ : SzA (GaloisField 2 m) θ) = 1 := by
      have := congrArg (fun q : Q => e q) h1
      simpa using this
    exact (one_ne_zero : (1 : GaloisField 2 m) ≠ 0) (by simpa using congrArg SzA.a h2)
  have hcard : Nat.card ↥(twoPoint H t) = Nat.card (GaloisField 2 m)ˣ := by
    have h2grp : IsPGroup 2 Q := isPGroup_two_of_mulEquiv θ e
    rw [twoPoint_card_eq_involutions hsplit hzass h2grp]
    rw [show (involutions (Q : Set G)) = {x : G | x ∈ Q ∧ orderOf x = 2} from rfl]
    rw [ncard_involutions_of_mulEquiv (Q := Q) e]
    rw [SzA.ncard_orderOf_eq_two θ, Nat.card_units (GaloisField 2 m)]
  exact fun lam => torusLambda_surjective hsplit hzass htorus hQ hcard lam


/-! ## 6.  The three special values of HB III XI 11.13 (a)

Given the structure equation `t · g² · t = g · t · g⁻¹` (with `j = g² ∈ Q`), the book's map `f`
takes the three canonical values `f (g²) = g⁻¹`, `f g = g`, `f (g⁻¹) = g²`.  The first is the
structure equation itself, the second is the computation `t g t = j t g` — obtained by
multiplying `t (g²) t = g t g⁻¹` by `t` on the left and by `g` on the right, using `t² = 1` —
with witness `j ∈ Q ≤ H`, and the third is `f (f (g²)) = g²`. -/

/-- **HB III XI 11.13 (a).**  If `t · g² · t = g · t · g⁻¹` (the structure equation, with
`g² ∈ Q`), then the book's map `f` takes the three canonical values
`f (g²) = g⁻¹`, `f g = g`, `f (g⁻¹) = g²`.

The second value is the computation `t g t = (g²) t g`: multiply `t (g²) t = g t g⁻¹` on the
left by `t` (using `t² = 1`) and on the right by `g`; the witness `g² ∈ Q ≤ H` is legal.  The
third is the involution property of `f` (`frel_symm`) applied to the first. -/
theorem frel_structure_values {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (hsplit : IsSplitRankOne H Q t) {g : Q} (hg2 : g ^ 2 ≠ 1)
    (hstruct : t * (((g ^ 2 : Q)) : G) * t = (g : G) * t * (((g⁻¹ : Q)) : G)) :
    RankOneUniqueness.FRel H t (((g ^ 2 : Q)) : G) (((g⁻¹ : Q)) : G) ∧
    RankOneUniqueness.FRel H t ((g : G)) ((g : G)) ∧
    RankOneUniqueness.FRel H t (((g⁻¹ : Q)) : G) (((g ^ 2 : Q)) : G) := by
  have ht2 : t * t = 1 := RankOneUniqueness.mul_self_eq_one hsplit
  have hgQ' : (((g ^ 2 : Q)) : G) ∈ Q := by
    rw [Subgroup.coe_pow]
    exact Q.pow_mem g.2 2
  -- `f (g²) = g⁻¹`, with witness `g ∈ Q ≤ H`
  have h1 : RankOneUniqueness.FRel H t (((g ^ 2 : Q)) : G) (((g⁻¹ : Q)) : G) :=
    ⟨(g : G), hsplit.le g.2, hstruct⟩
  -- `f g = g`: `t g t = (g²) · t · g`, with witness `g² ∈ Q ≤ H`
  have hkey : (((g ^ 2 : Q)) : G) * t = t * (g : G) * t * (((g⁻¹ : Q)) : G) := by
    have h := congrArg (fun z => t * z) hstruct
    rw [show t * (t * (((g ^ 2 : Q)) : G) * t) = (((g ^ 2 : Q)) : G) * t by
      rw [show t * (t * (((g ^ 2 : Q)) : G) * t)
          = (t * t) * (((g ^ 2 : Q)) : G) * t by group, ht2, one_mul]] at h
    rw [show t * ((g : G) * t * (((g⁻¹ : Q)) : G))
        = t * (g : G) * t * (((g⁻¹ : Q)) : G) by group] at h
    exact h
  have hgt : t * (g : G) * t = (((g ^ 2 : Q)) : G) * t * (g : G) := by
    have key2 : (((g ^ 2 : Q)) : G) * t * (g : G) = t * (g : G) * t := by
      rw [hkey, Subgroup.coe_inv]
      group
    exact key2.symm
  have h2 : RankOneUniqueness.FRel H t ((g : G)) ((g : G)) :=
    ⟨(((g ^ 2 : Q)) : G), hsplit.le hgQ', hgt⟩
  exact ⟨h1, h2, frel_symm hsplit h1⟩

end Work.ZassenhausSuzuki
