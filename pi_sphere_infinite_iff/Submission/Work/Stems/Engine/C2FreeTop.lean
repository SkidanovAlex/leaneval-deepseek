import Submission.Work.Stems.Engine.C2Range
import Submission.Work.Serre.Models
import Submission.Work.Serre.Engine
import Submission.Work.RatHurewicz.RelHomotopy

/-!
# The `K(ℤ,n)` layer with a **free top** (`SERRE_BLUEPRINT.md` ADDENDUM 3 (B), (C))

`Submission/Work/Stems/C2ODD_PLAN.md` and `EM_C2_RANGE_FINDING.md` record that the *range-form* `C2`
statements (`Work.Stems.Engine.C2evenRange`/`C2oddRange` of `C2Range.lean`) have no producer from
the range-form engine: they quantify over **genuine** models and **fix** the connective range at
`2n-1` throughout the induction, so each level loses a constant number of *degrees* and the deficit
grows linearly in `n`.  `SERRE_BLUEPRINT.md` ADDENDUM 3 (B), (C) gives the fix:

* **(B) the Gysin's range is given by the FIBRE, not by the base's connectivity.**  If the fibre of
  a fibration with rationally acyclic total space is a rational `r`-sphere *through degree `N`*,
  then `⌣e : H^m(B;ℚ) ≅ H^{m+r+1}(B;ℚ)` for `m + r ≤ N` — **no** `m < b`.  This is
  `Work.Stems.Engine.GysinRangeFree` below (the range-form `GysinRange` of `C2Range.lean` carries
  the extra, unusable hypothesis `m < b`, which makes it vacuous: in the range `m < b` both sides of
  `⌣e` vanish by connectivity, so `SerreE3b` as stated only supplies `H^{r+1}(B;ℚ) ≅ ℚ`).
  With the fibre-given range the even step reaches `N' + 1` degrees, where `N'` is the fibre's
  knowledge — instead of the transgression's `b + f - 1`.
* **(C) state `C2` with a FREE top.**  The *range models* are built to **any** degree `N`
  (`Work.Serre.SerreC0Range`, RATHUREWICZ's finite truncations), so the deficit — which is *linear*
  in `n` — is absorbed by choosing `N ≥ target + c·n` at the start of the induction, and one must
  **not** keep the range fixed across levels.  This gives `C2evenFree` / `C2oddFree` below, whose
  conclusions are capped only by `N - c·n`, with **no** structural cap such as `4j-1` or `2n+1`.

With both, the mutual induction closes **with `c = 1`**: the even step at level `2j` uses the Gysin
with the fibre `L_{2j-1}` (a range model through `N-1`, known through `(N-1) - c(2j-1)`) and
reaches `N - c(2j-1) + 1 ≥ N - c·2j` degrees; the odd step at level `n` uses the cover
`Eₙ = hofib(Sⁿ → Lₙ)` (fibre `ΩLₙ = L_{n-1}`, a range model through `N-1`), whose rational
acyclicity is `(N-1) - c(n-1) = N - c·n + (c-1) ≥ N - c·n` degrees, and `E3a` (`Work.Serre.SerreE3a`
— the mapping theorem, whose conclusion range is the *acyclicity* bound `N` and not `b+f`) then
gives `Lₙ` the rational cohomology of `Sⁿ` in the same range.

Both steps are *degree-lossless* in the free top; the only losses are the `c·n` written into the
statements.  This is the corrected interface; `C2Range.lean`'s fixed-range statements remain as the
record of what the range-form engine can do (and of why it is not enough).
-/

open CategoryTheory CategoryTheory.Limits
open scoped Topology

namespace Work.Stems.Engine

noncomputable section

/-- **E3b with the range given by the fibre** (`SERRE_BLUEPRINT.md` ADDENDUM 3 (B)): for a Serre
fibration with rationally acyclic total space whose fibre is a rational `r`-sphere **through degree
`N`** (`H_t(F;ℚ) = 0` for `0 < t ≤ N`, `t ≠ r`, and `H_r(F;ℚ) ≅ ℚ`), the cup product with the
Euler class is an isomorphism `H^m(B;ℚ) ≅ H^{m+r+1}(B;ℚ)` for `m + r ≤ N` — with **no** hypothesis
on the connectivity of the base. -/
def GysinRangeFree : Prop :=
  ∀ (E B : Type) [TopologicalSpace E] [TopologicalSpace B] (p : C(E, B)) (e₀ : E) (b₀ : B)
      (r N : ℕ),
    1 ≤ r → Work.StemsB.IsSerreFibration p → PathConnectedSpace B →
      Work.Serre.RatAcyclic E →
      (∀ t : ℕ, 0 < t → t ≠ r → t ≤ N →
        IsZero (Work.Serre.ratH (TopCat.of (Work.RatHurewicz.homotopyFibre p e₀)) t)) →
      Nonempty (Work.Serre.ratH (TopCat.of (Work.RatHurewicz.homotopyFibre p e₀)) r ≅
        ModuleCat.of ℚ ℚ) →
      ∀ m : ℕ, m + r ≤ N →
        ∃ e : Work.Serre.ratCoh (TopCat.of B) (r + 1),
          IsIso (ModuleCat.ofHom (Work.Serre.cupWith (TopCat.of B) (r + 1) e m))

/-- **`C2` for `K(ℤ,2j)`-models, free top** (`SERRE_BLUEPRINT.md` ADDENDUM 3 (C)): a *range model*
of `K(ℤ,2j)` through degree `N` has the rational homology of `ℂP^∞` rescaled by `2j` through
degree `N - c·(2j)`: `H_{2jk} ≅ ℚ` and `H_d = 0` for `2j ∤ d`, below that bound.

The bound is the **free top minus `c·level`**; there is no structural cap such as `4j-1`.  (The
generator conjunct is in fact automatic for `2jk < 4j-1`, hence unconditionally true —
`Work.Stems.c2evenRange_generator` — so only the vanishing conjunct has content.) -/
def C2evenFree (c : ℕ) : Prop :=
  ∀ (j : ℕ) (hj : 1 ≤ j) (N : ℕ),
    ∀ (X : Type) [TopologicalSpace X] (pt : X),
      Work.Serre.IsEMSpaceUpTo ℤ (2 * j) (by omega) N X pt →
      (∀ k : ℕ, 2 * j * k < N - c * (2 * j) →
        Nonempty (Work.Serre.ratH (TopCat.of X) (2 * j * k) ≅ ModuleCat.of ℚ ℚ)) ∧
      (∀ d : ℕ, d < N - c * (2 * j) → (∀ k : ℕ, d ≠ 2 * j * k) →
        IsZero (Work.Serre.ratH (TopCat.of X) d))

/-- **`C2` for `K(ℤ,n)`-models, `n` odd, free top** (`SERRE_BLUEPRINT.md` ADDENDUM 3 (C)): a range
model of `K(ℤ,n)` through degree `N` (`n` odd) has the rational homology of `Sⁿ` through degree
`N - c·n`: `H_n ≅ ℚ` and `H_d = 0` for `0 < d ≠ n`. -/
def C2oddFree (c : ℕ) : Prop :=
  ∀ (n : ℕ) (hn : 1 ≤ n), Odd n → ∀ (N : ℕ),
    ∀ (X : Type) [TopologicalSpace X] (pt : X),
      Work.Serre.IsEMSpaceUpTo ℤ n (by omega) N X pt →
      Nonempty (Work.Serre.ratH (TopCat.of X) n ≅ ModuleCat.of ℚ ℚ) ∧
      (∀ d : ℕ, 0 < d → d < N - c * n → d ≠ n →
        IsZero (Work.Serre.ratH (TopCat.of X) d))

end

end Work.Stems.Engine
