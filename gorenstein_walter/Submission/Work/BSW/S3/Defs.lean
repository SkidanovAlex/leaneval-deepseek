/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gorenstein–Walter formalisation team (area BSW)

# Area BSW: Bender §3 (`bswCompletionProp`), leaf contracts

The statements below are copied verbatim from the lead's design file
`Submission/Work/_design_gw/Core8.lean` §2 (design pass 8, `NOTES_LEAD_gw_design8.md` §2), with the
`C8`-prefixed helper names replaced by the area's own (`Work.GW2.BSWHyps2`, `Work.BSW.iFn`,
`Work.GW2.conjSub`, `Work.GW2.Inverts`, `Work.BSW.IsBSWData`).  They decompose Bender's §3
(`REFS/bender1974_bsw.txt`, pp. 232–235), the completion of the proof, into

```
BSWExistsXProp (3.0) ─┐
BSWS31Prop (3.1) ─────┼─> BSWS34ArithProp (3.2–3.4, pure) ─┬─ ε=+1 ─> BSWCase1Prop (3.3)
BSWS32Prop (3.2) ─────┘                                    └─ ε=−1 ─> BSWS35Prop ─> BSWCase2
                                                              ─> BSWS36Prop ─> BSWS37Prop ─> BSWS38Prop
```

and `Work.BSW.BSWCompletionProp` is the assembly `bswCompletionProp_of_leaves` at the end.
-/
import Mathlib
import Submission.Work.BSW.Concl
import Submission.Work.BSW.Vocab

open scoped BigOperators

namespace Work.BSW

open Subgroup Work.GW2

variable {G : Type} [Group G] [Finite G] {t s : G} {K : Subgroup G}

/-- `H^G`, the union of the conjugates of `H = C_G(t)`.  It equals `K^G`. -/
def HG (t : G) : Set G := {y | ∃ g : G, g * y * g⁻¹ ∈ Subgroup.centralizer ({t} : Set G)}

/-- **§3 opening (3.0)**: an element `x ∉ H^G`, inverted by `t`, with `i(x)` large.
* `Σ_G i = I² + I` (proved: `Work.BSW.Cases.sum_iFn`).
* On `H^G`: `i(1) = I`, `i = k+1` on the `I` involutions, and `i = k` on the other `I(k−2)`
  elements.  So the sum over `H^G` is `I(k² − k + 2)`, and `|H^G| = 1 + I(k−1)`.
* Hence the average of `i` over `G − H^G` is
  `I(I − k² + k − 1)/(I(k+1) − 1) > (I − k² + k − 1)/(k+1) = k + 3εk/(k+1)`.
* Conjugate so that `t` inverts `x`. -/
def BSWExistsXProp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t s : G) (K : Subgroup G) (ε : ℤ),
    BSWHyps2 G t s K → 4 < Nat.card K → (ε = 1 ∨ ε = -1) →
    (Nat.card G : ℤ) = (2 * Nat.card K + ε) * (Nat.card K + ε) * (2 * Nat.card K) →
    ∃ x : G, x ∉ HG t ∧ t⁻¹ * x * t = x⁻¹ ∧
      (Nat.card K : ℤ) * (Nat.card K + 1 + 3 * ε) < (Nat.card K + 1) * (iFn G x : ℤ)

/-- **3.1**, for any `x ∉ H^G` inverted by `t`.  Write `F = C(x)`, `M = N(F)`.
* (a) `F ∩ H^G = 1`, so `|F|` is odd.  Each involution of `M` acts on `F` fixed-point-freely,
  hence inverts it.  So `F` is abelian, and `C(a) = F` for every `a ∈ F#`.
* (b) `F` is TI, with normalizer `M`.
* (c) The involutions of `M` are exactly `tF`, and `i(x) = |F|`.
* (d) `M = F(K ∩ M)` with `F ∩ K = 1`, and `K ∩ M` acts fixed-point-freely on `F`.
* (e) `F ∩ M^g = 1` for `g ∉ M`.
* (f) `F` is a Hall subgroup coprime to `2k` (this uses `BSWOddHallProp` from design7). -/
def BSWS31Prop : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t s : G) (K : Subgroup G) (x : G),
    BSWHyps2 G t s K → x ∉ HG t → t⁻¹ * x * t = x⁻¹ →
    IsMulCommutative (Subgroup.centralizer ({x} : Set G)) ∧
    Odd (Nat.card (Subgroup.centralizer ({x} : Set G))) ∧
    (∀ a ∈ Subgroup.centralizer ({x} : Set G), a ≠ 1 →
      Subgroup.centralizer ({a} : Set G) = Subgroup.centralizer ({x} : Set G)) ∧
    (∀ g : G, g ∉ Subgroup.normalizer (Subgroup.centralizer ({x} : Set G) : Set G) →
      Subgroup.centralizer ({x} : Set G) ⊓
        conjSub g (Subgroup.normalizer (Subgroup.centralizer ({x} : Set G) : Set G)) = ⊥) ∧
    Subgroup.centralizer ({x} : Set G) ⊓ K = ⊥ ∧
    Subgroup.normalizer (Subgroup.centralizer ({x} : Set G) : Set G) =
      Subgroup.centralizer ({x} : Set G) ⊔
        (K ⊓ Subgroup.normalizer (Subgroup.centralizer ({x} : Set G) : Set G)) ∧
    (∀ c ∈ K ⊓ Subgroup.normalizer (Subgroup.centralizer ({x} : Set G) : Set G), c ≠ 1 →
      ∀ a ∈ Subgroup.centralizer ({x} : Set G), c * a * c⁻¹ = a → a = 1) ∧
    {u : G | orderOf u = 2 ∧
        u ∈ Subgroup.normalizer (Subgroup.centralizer ({x} : Set G) : Set G)} =
      {u : G | ∃ c ∈ Subgroup.centralizer ({x} : Set G), u = t * c} ∧
    iFn G x = Nat.card (Subgroup.centralizer ({x} : Set G)) ∧
    Nat.Coprime (Nat.card (Subgroup.centralizer ({x} : Set G)))
      (Subgroup.centralizer ({x} : Set G)).index ∧
    Nat.Coprime (Nat.card (Subgroup.centralizer ({x} : Set G))) (2 * Nat.card K)

/-- **3.2** (coset counting).  Let `f = |F|`, `n = |K ∩ M|`, `m = |G:M|`, `I = |G:H|`, `a = 2k/n`.
* Each involution of `M` fixes exactly `a` cosets of `M`, and distinct involutions of `M` share
  only the coset `M` itself.  This gives `f(a−1)` *special* cosets.
* `F` acts semiregularly on the cosets other than `M` and preserves the special ones.
* A non-special coset contains at most one involution (the `InvertM` lemma, design8 §2.3).

Conclusion: `1 + f(a−1) ≤ m`, `f ∣ m − (1 + f(a−1))`, `f(k+1) ≤ I`, and
`I − f(k+1) ≤ m − (1 + f(a−1))`. -/
def BSWS32Prop : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t s : G) (K : Subgroup G) (x : G),
    BSWHyps2 G t s K → x ∉ HG t → t⁻¹ * x * t = x⁻¹ →
    1 + Nat.card (Subgroup.centralizer ({x} : Set G)) *
        (2 * Nat.card K /
          Nat.card (K ⊓ Subgroup.normalizer (Subgroup.centralizer ({x} : Set G) : Set G) :
            Subgroup G) - 1) ≤
      (Subgroup.normalizer (Subgroup.centralizer ({x} : Set G) : Set G)).index ∧
    Nat.card (Subgroup.centralizer ({x} : Set G)) ∣
      (Subgroup.normalizer (Subgroup.centralizer ({x} : Set G) : Set G)).index -
        (1 + Nat.card (Subgroup.centralizer ({x} : Set G)) *
          (2 * Nat.card K /
            Nat.card (K ⊓ Subgroup.normalizer (Subgroup.centralizer ({x} : Set G) : Set G) :
              Subgroup G) - 1)) ∧
    Nat.card (Subgroup.centralizer ({x} : Set G)) * (Nat.card K + 1) ≤
      (Subgroup.centralizer ({t} : Set G)).index ∧
    (Subgroup.centralizer ({t} : Set G)).index -
        Nat.card (Subgroup.centralizer ({x} : Set G)) * (Nat.card K + 1) ≤
      (Subgroup.normalizer (Subgroup.centralizer ({x} : Set G) : Set G)).index -
        (1 + Nat.card (Subgroup.centralizer ({x} : Set G)) *
          (2 * Nat.card K /
            Nat.card (K ⊓ Subgroup.normalizer (Subgroup.centralizer ({x} : Set G) : Set G) :
              Subgroup G) - 1))

/-- **3.3/3.4 arithmetic** (pure).  Inputs:
* `I = (2k+ε)(k+ε)`, with `f` odd, `n` even, `n ∣ k`, `n ∣ f − 1`;
* `fnm = 2kI`, `f ∣ I` (from 3.1), and the choice inequality `k(k+1+3ε) < (k+1)f`;
* the four 3.2 inequalities.

Output: either `ε = 1` with `f = 2k+1`, `n = k` and `I = f(k+1)` (case (i)), or `ε = −1`
with `f = k−1` and `n = 2` (case (ii)). -/
def BSWS34ArithProp : Prop :=
  ∀ (k f n m I : ℕ) (ε : ℤ), 4 < k → Even k → (ε = 1 ∨ ε = -1) →
    (I : ℤ) = (2 * k + ε) * (k + ε) → Odd f → Even n → 0 < n → n ∣ k → n ∣ f - 1 →
    f * n * m = 2 * k * I → f ∣ I →
    (k : ℤ) * (k + 1 + 3 * ε) < (k + 1) * f →
    1 + f * (2 * k / n - 1) ≤ m → f ∣ m - (1 + f * (2 * k / n - 1)) →
    f * (k + 1) ≤ I → I - f * (k + 1) ≤ m - (1 + f * (2 * k / n - 1)) →
    (ε = 1 ∧ f = 2 * k + 1 ∧ n = k ∧ I = f * (k + 1)) ∨ (ε = -1 ∧ f = k - 1 ∧ n = 2)

/-- `F` is a `p`-group: a group `D` of order `(f−1)/2` acts freely on `F#`, so there are
exactly two orbits.  With two primes there would be at least three invariant pieces:
`F_p#`, `F_{p'}#` and the mixed elements. -/
def BSWTwoOrbitPrimePowerProp : Prop :=
  ∀ (F D : Type) [CommGroup F] [Finite F] [Group D] [Finite D] [MulDistribMulAction D F],
    Odd (Nat.card F) → 2 * Nat.card D + 1 = Nat.card F →
    (∀ d : D, d ≠ 1 → ∀ a : F, d • a = a → a = 1) →
    ∃ p e : ℕ, p.Prime ∧ Nat.card F = p ^ e

/-- **3.3**: in case (i), Bender's conclusion holds with `Q = F` and `D = K`. -/
def BSWCase1Prop : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t s : G) (K : Subgroup G) (x : G),
    BSWHyps2 G t s K → 4 < Nat.card K → x ∉ HG t → t⁻¹ * x * t = x⁻¹ →
    Nat.card (Subgroup.centralizer ({x} : Set G)) = 2 * Nat.card K + 1 →
    K ≤ Subgroup.normalizer (Subgroup.centralizer ({x} : Set G) : Set G) →
    Nat.card G = (2 * Nat.card K + 1) * (Nat.card K + 1) * (2 * Nat.card K) →
    IsBSWData G (2 * Nat.card K + 1)

/-- The case-(ii) bundle, valid after 3.4 + 3.5.  Write `Y = G − H^G − F^G`.  Every `y ∈ Y` has
`|C(y)| = 2k − 1`, has prime order `p`, and is not conjugate to `y⁻¹`. -/
def BSWCase2 (G : Type) [Group G] [Finite G] (t s : G) (K : Subgroup G) (x : G) (p : ℕ) :
    Prop :=
  BSWHyps2 G t s K ∧ 4 < Nat.card K ∧
  Nat.card G = (2 * Nat.card K - 1) * (Nat.card K - 1) * (2 * Nat.card K) ∧
  x ∉ HG t ∧ t⁻¹ * x * t = x⁻¹ ∧
  Nat.card (Subgroup.centralizer ({x} : Set G)) = Nat.card K - 1 ∧
  Nat.card (Subgroup.normalizer (Subgroup.centralizer ({x} : Set G) : Set G)) =
    2 * (Nat.card K - 1) ∧
  p.Prime ∧ (∃ e : ℕ, 2 * Nat.card K - 1 = p ^ e) ∧
  ∀ y : G, y ≠ 1 → y ∉ HG t →
    (∀ g : G, g * y * g⁻¹ ∉ Subgroup.centralizer ({x} : Set G)) →
    Nat.card (Subgroup.centralizer ({y} : Set G)) = 2 * Nat.card K - 1 ∧
      orderOf y = p ∧ ¬ IsConj y y⁻¹

/-- **3.5**.  The argument:
* `|Y| = 4k(k−1)`;
* `|C(y)|` is coprime to `2k(k−1)`, by Hall-ness of `K` (odd primes) and of `F`.  So it divides
  `2k−1`, and `|y^G| = 2k(k−1)·odd`;
* so `Y` is exactly two classes, with `|C(y)| = 2k−1`;
* all elements of `C(y)#` lie in `Y`, so they all have the same order, which is therefore a
  prime `p`;
* if `y ~ y⁻¹`, then an involution inverts `y`.  Then 3.1–3.4, applied to `y`, give
  `|C(y)| = k−1`, a contradiction. -/
def BSWS35Prop : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t s : G) (K : Subgroup G) (x : G),
    BSWHyps2 G t s K → 4 < Nat.card K →
    Nat.card G = (2 * Nat.card K - 1) * (Nat.card K - 1) * (2 * Nat.card K) →
    x ∉ HG t → t⁻¹ * x * t = x⁻¹ →
    Nat.card (Subgroup.centralizer ({x} : Set G)) = Nat.card K - 1 →
    Nat.card (Subgroup.normalizer (Subgroup.centralizer ({x} : Set G) : Set G)) =
      2 * (Nat.card K - 1) →
    ∃ p : ℕ, BSWCase2 G t s K x p

/-- **3.6**.  For a `p`-subgroup `X ≠ 1`, `N(X) = P ⋊ D`, where `P` is a normal Sylow
`p`-subgroup of `N(X)` and `D` is conjugate into `F` or `K`.
* `N(X)` has odd order.  An involution normalizing `X` would centralize or invert some `y ∈ X#`.
* For each prime `r ≠ p`, `N_N(R)` is abelian.  It lies in `C(R)`'s normalizer, which is `M` or
  `H` (up to conjugacy); since it has odd order, it lies in `F` or `K`.
* Burnside: Mathlib's `ker_transferSylow_isComplement'`.
* Frattini. -/
def BSWS36Prop : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t s : G) (K : Subgroup G) (x : G) (p : ℕ),
    BSWCase2 G t s K x p → ∀ X : Subgroup G, X ≠ ⊥ → IsPGroup p X →
    ∃ P D : Subgroup G, P ≤ Subgroup.normalizer (X : Set G) ∧
      D ≤ Subgroup.normalizer (X : Set G) ∧
      IsPGroup p P ∧ ¬ p ∣ (P.subgroupOf (Subgroup.normalizer (X : Set G))).index ∧
      (P.subgroupOf (Subgroup.normalizer (X : Set G))).Normal ∧
      P ⊔ D = Subgroup.normalizer (X : Set G) ∧ P ⊓ D = ⊥ ∧
      ∃ g : G, conjSub g D ≤ Subgroup.centralizer ({x} : Set G) ∨ conjSub g D ≤ K

/-- **3.7**.  A Sylow `p`-subgroup is TI.  Take `X` maximal among the intersections of two
distinct Sylows; `N(X)` has a normal Sylow `p`-subgroup by 3.6. -/
def BSWS37Prop : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t s : G) (K : Subgroup G) (x : G) (p : ℕ),
    BSWCase2 G t s K x p → ∀ (Q : Sylow p G) (g : G),
      g ∉ Subgroup.normalizer ((Q : Subgroup G) : Set G) →
      (Q : Subgroup G) ⊓ conjSub g (Q : Subgroup G) = ⊥

/-- **3.8**.  `IsBSWData G (2k − 1)`, with `Q` a Sylow `p`-subgroup and `D = F^g`.
* `|Q| = 2k−1`.
* `N(Q) = QD` (3.6), and `G`-fusion in `Q` is `N(Q)`-fusion (3.7).
* `Q#` is two classes, so `C(a) = Q` for every `a ∈ Q#`; hence `Q` is abelian and `C(Q) = Q`.
* `2|D| = q−1`, so `|D| = k−1`.  Thus `D` is conjugate onto `F`, since `k−1 ∤ k`.
* (4) holds because `C(X) = F` for every `1 ≠ X ≤ F`, and `M = F⟨t⟩` with `t` inverting `F`. -/
def BSWS38Prop : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t s : G) (K : Subgroup G) (x : G) (p : ℕ),
    BSWCase2 G t s K x p → IsBSWData G (2 * Nat.card K - 1)

end Work.BSW
