import Mathlib
import Submission.Work.EKLContract.Interfaces
import Submission.Work.EKLContract.Lemmas.Gamma3Facts
import Submission.Work.EKLContract.Lemmas.V_open_one
import Submission.Work.EKLContract.Lemmas.mkX_mul

/-!
# C9 — no exceptional returns for `SL₃(ℤ)`: shared vocabulary

This module fixes the definitions used by the proof of the frozen component
`Work.EKLContract.P_NonExc` (ROUTE_LEAD §4.C9), and records here the proof recipes for the lemmas
delegated to the fleet.  Everything is stated for pairwise distinct indices `a b c : Fin 3` with
`hab : a ≠ b`, `hac : a ≠ c`, `hcb : c ≠ b`; `c` is the "third" index.  (The paper's
`(a,b,c) = (1,2,3)` is `(0,1,2)` here.)

## Objects

* `P_NonExc μ hab c` says: there is a `μ`-null set `N` such that every compact `K` disjoint from
  `N` with `μ K > 0` has, for every `δ > 0`, a return `aPrime c s • z ∈ K` with
  `aPrime c s • z = g • z`, `g ∈ V δ`, `g ∉ Lset hab`.
* `Dinj δ` = the set of `x` at which the orbit map `g ↦ g • x` is injective on `V δ` (EKL's
  `D_ℓ` with `δ = 1/ℓ`).  `⋃_{δ>0} Dinj δ = X₃`, and every compact set is contained in `Dinj δ`
  for some `δ > 0` (EKL p.9, "for every compact set `K`, `K ⊂ D_ℓ` for some `ℓ`").
* `clBox δ` = the *closed* box `{g : |g_ij - δ_ij| ≤ δ}` (`V δ` is the open box).  The closed box
  is compact; it is used for the (closed, hence measurable) "bad return" sets.
* `uvec a b c` = the vector with `-1` at `a`, `1` at `b`, `0` at `c`; `bconj a b c = aDiag (uvec …)`
  is EKL's `α^{t}` with `t = (-1,1,0)` (their `α^β`).  It *contracts* the `(a,b)`, `(a,c)`, `(c,b)`
  entries (by `e^{-2}`, `e^{-1}`, `e^{-1}`) and *expands* the `(b,a)`, `(c,a)`, `(b,c)` entries
  (by `e^{2}`, `e`, `e`); the latter three entries vanish for `g ∈ Lset hab`.
* `fmax a b c g = max (max |g a b| |g a c|) |g c b|`: the three entries which, together with
  `g ∈ Lset hab`, force `g` to be the diagonal matrix `diag(λ,λ,λ⁻²)`.
* `Bad a b c hab ℓ ℓu n ε`: points of `Dinj (1/ℓu)` carrying an `Lset`-return under
  `aPrime c n` with displacement in `clBox (1/(2ℓ))` and `fmax ≥ ε`.  These are the sets whose
  measure is zero (EKL Lemma 4.2, L9.2 below).

## Recipes for the delegated lemmas

### `Dinj` (file `NonExcDinj`)

* `∀ x, ∃ δ > 0, x ∈ Dinj δ`: write `x = mkX k`; the stabiliser of `x` is `k Γ₃ k⁻¹`, which is
  discrete (conjugate of the discrete `Γ₃`); take an open neighbourhood `W ∋ 1` with
  `W ∩ k Γ₃ k⁻¹ = {1}` and then `δ > 0` with `(V δ)⁻¹ * V δ ⊆ W`.
* `IsClosed (Dinj δ)`: `x ∉ Dinj δ` iff there are `g h ∈ V δ` with `g ≠ h` and `h⁻¹ g ∈ Stab x`,
  i.e. (using `x = mkX k` and `QuotientGroup.eq`) iff there are `k` with `mkX k = x` and
  `γ ∈ Γ₃`, `γ ≠ 1` with `k * γ * k⁻¹ ∈ (V δ)⁻¹ * V δ`.  Hence
  `(Dinj δ)ᶜ = mkX '' ⋃ (γ : Γ₃) (_ : γ ≠ 1), {k : k * γ * k⁻¹ ∈ (V δ)⁻¹ * V δ}`
  is the image under the *open* quotient map `mkX` (`QuotientGroup.isOpenMap_coe`) of an open set
  (a countable union of opens, as `Γ₃` is countable — `Gamma3Facts`), hence open.
* `IsCompact K → ∃ δ > 0, K ⊆ Dinj δ` (EKL L9.1): `Dinj` is closed and decreasing and covers `K`
  pointwise, so if no `Dinj (1/n)` contained `K` the family `K ∩ (Dinj (1/n))ᶜ` of nonempty compact
  sets would have the finite intersection property, giving a point of `K` in no `Dinj δ`.

### `V`-arithmetic and open orbit images (file `NonExcV`)

* `∀ δ > 0, ∃ ε > 0, ∀ g h ∈ V ε, h * g⁻¹ ∈ V δ`: from continuity of multiplication and inversion
  at `(1,1)` together with the fact that the sets `V r` form a neighbourhood basis of `1 ∈ SL₃(ℝ)`
  (`∀ W ∈ 𝓝 1, ∃ r > 0, V r ⊆ W` — prove by passing to a basic open set of the product topology on
  matrices, i.e. intervals around each entry of the identity).
* `IsOpen {y : X₃ | ∃ g ∈ V δ, y = g • x}` and `x` in it: `mkX '' V δ ∈ 𝓝 (mkX 1)` because `V δ`
  is a neighbourhood of `1` on which `mkX` is injective and `mkX` is an open map, then translate by
  `x`.  (Equivalent to clause 5 of `P_X3`; derive it directly.)

### `Lset` and the conjugation (file `NonExcLset`)

* `mem_Lset_iff`: `g ∈ Lset hab ↔ g a a = g b b ∧ (∀ i, i ≠ a → g i a = 0) ∧
  (∀ j, j ≠ b → g b j = 0)`, from `g * u_ab(1) = u_ab(1) * g` with `u_ab(s) = 1 + s E_ab`.
* `fmax_eq_zero_of_mem_Lset`: if `g ∈ Lset hab` and `fmax a b c g = 0` then `g a a = g b b` and
  every off-diagonal entry of `g` vanishes.
* `conj_mem_clBox`: for `g ∈ Lset hab`, `g ∈ clBox δ` (`0 ≤ δ`) and all `m : ℕ`,
  `bconj a b c ^ m * g * (bconj a b c ^ m)⁻¹ ∈ clBox δ` (the `L`-zeros stay zero, the diagonal is
  fixed, and the three `fmax` entries are contracted).
* `fmax_conj_le`: for `g ∈ Lset hab`, `fmax (bconj^m * g * (bconj^m)⁻¹) ≤ e^{-m} fmax g`.
* `aPrime_commute_bconj`: `bconj a b c * aPrime c s = aPrime c s * bconj a b c`
  (both are `aDiag` of explicit vectors, and `aDiag_add` plus commutativity of `+` gives it).

### `Bad` nullity (file `NonExcBad`) — EKL Lemma 4.2 / ROUTE_LEAD L9.2

`μ (Bad a b c hab ℓ ℓu n ε) = 0` whenever `3 * ℓu < ℓ`, `0 < ε`, `μ` a probability and
`IsAInvariant μ` (given `IsClosed (Dinj δ)` for all `δ` and `IsCompact (clBox δ)` for all `δ`).

Measurability: `Bad = Dinj (1/ℓu) ∩ Bad'` where
`Bad' = {x | ∃ g ∈ clBox ((2*ℓ)⁻¹) ∩ Lset hab, aPrime c n • x = g • x ∧ ε ≤ fmax g}` is *closed*:
if `x_k → x` with witnesses `g_k` in the compact `clBox`, pass to a convergent subsequence
(`IsCompact.tendsto_subseq`) and use continuity of the action.  (Equivalently: `Bad'` is the
projection of the closed set of witnesses inside `X₃ × clBox`, and the projection along a compact
factor is a closed map: if `(x, g) ∉ R` for all `g ∈ C` with `C` compact and `R` closed, the
product neighbourhoods of the points `(x,g)` cover `{x} × C` and finitely many of them give
`∃ U ∈ 𝓝 x, U ×ˢ C ⊆ Rᶜ`.)  With `Dinj` closed, `Bad` is measurable.  Proof: `Bad ⊆ Dinj (1/ℓu) ∩ (closed set)`, so `Bad` is measurable; let `T` be the
action of `bconj a b c` (measure preserving).  If `μ Bad ≠ 0`, Poincaré recurrence
(`MeasureTheory.Conservative.ae_mem_imp_frequently_image_mem`, via
`MeasureTheory.MeasurePreserving.conservative`) gives `y ∈ Bad` with `T^[m] y ∈ Bad` for arbitrarily
large `m`.  Let `g`, `g'` be the two displacements.  Then
`aPrime c n • (T^[m] y) = T^[m] • (aPrime c n • y) = (bconj^m * g * (bconj^m)⁻¹) • (T^[m] y)`
(commutativity + associativity), so by uniqueness at `T^[m] y ∈ Dinj (1/ℓu)` — both elements lie in
`clBox (1/(2ℓ)) ⊆ V (1/ℓu)`, using `3 * ℓu < ℓ` — the two displacements agree:
`g' = bconj^m * g * (bconj^m)⁻¹`.  Hence `ε ≤ fmax g' = fmax (bconj^m g bconj^{-m}) ≤ e^{-m} fmax g`,
and `fmax g ≤ (2 * ℓ : ℝ)⁻¹` because `g ∈ clBox (1/(2ℓ))`; for `m` large this contradicts `ε > 0`.

### `no_diag_fixed` (file `NonExcNoDiag`) — ROUTE_LEAD L9.3

No `h ∈ SL₃(ℝ)` whose matrix is `diag(λ,λ,λ⁻²)` (in the slots `a,b,c`), with `λ > 0`, `λ ≠ 1`,
fixes any point of `X₃ = SL₃(ℝ)/SL₃(ℤ)`.
Proof: write `x = mkX k` and put `γ = k⁻¹ h k ∈ Γ₃` (from `h • x = x` and `QuotientGroup.eq`).
`γ` is conjugate to `h`, so its characteristic polynomial is `X³ - a X² + b X - 1` over `ℝ` with
`a = 2λ + λ⁻²`, `b = λ² + 2λ⁻¹` (roots `λ, λ, λ⁻²`), while `γ` has integer entries, so
`a, b ∈ ℤ`.  From `2λ + λ⁻² = a` and `λ² + 2λ⁻¹ = b`:
`2λ³ - aλ² + 1 = 0` and `λ³ - bλ + 2 = 0`, hence `aλ² - 2bλ + 3 = 0`, hence (multiply by `λ` and
substitute `λ³ = bλ - 2`) `-2bλ² + (ab+3)λ - 2a = 0`; eliminating `λ²` between the last two gives
`λ * (a²b + 3a - 4b²) = 2a² - 6b`.  If the bracket is nonzero then `λ ∈ ℚ`.  If it vanishes then
`3b = a²` and `a (a³ - 27) = 0`; `a = 0` contradicts `aλ² - 2bλ + 3 = 0`, and `a = 3` gives
`3(λ-1)² = 0`, i.e. `λ = 1 ∈ ℚ`.  So always `λ ∈ ℚ`; by the integral root theorem
(`Polynomial.isInteger_of_is_root_of_monic`, applied to the monic integer polynomial which is the
characteristic polynomial of the integral matrix `γ`) both `λ` and `λ⁻²` are integers, and
`λ² * λ⁻² = 1` with `λ > 0` forces `λ = 1`, contradiction.

### Assembly (my file `prove_NonExc`)

Given compact `K`, `μ K > 0`, `δ > 0`: choose `ℓu` with `K ⊆ Dinj (1/ℓu)`.  Take a finite cover of
`K` by the open sets `W(z_i) = {y : ∃ h ∈ V ε, y = h • z_i}` (`ε` small), pick `i` with
`μ (K ∩ W(z_i)) > 0`, and apply Poincaré recurrence to this set and the measure-preserving map
`α' = aPrime c 1`: get `z ∈ K`, `m ≥ 1` with `α'^m z ∈ K ∩ W(z_i)`, i.e. `α'^m z = g • z` with
`g ∈ V (small)` (compose the two witnesses through `V ε * (V ε)⁻¹ ⊆ V δ'`).  If the conclusion
failed, `g ∈ Lset hab`; taking `ℓ` large (`3ℓu < ℓ`, `1/(2ℓ) ≤ δ`) gives
`z ∈ Bad a b c hab ℓ ℓu m (1/(k+1))` whenever `fmax g ≥ 1/(k+1)`; since `μ Bad = 0` this forces
`fmax g = 0`, so `g` is diagonal with `g a a = g b b = λ`, `g c c = λ⁻²` and
`|λ - 1| ≤ 1/(2ℓ) ≤ 1/2`.  With `W = diag(e^m/λ, e^m/λ, (e^m/λ)⁻²) ∈ SL₃(ℝ)` one has
`g * W = aPrime c m`, whence `W • z = g⁻¹ • (aPrime c m • z) = z`, contradicting `no_diag_fixed`
because `e^m/λ ≠ 1` (`e^m ≥ e > 3/2 ≥ λ`).
-/

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace Work.EKLNonExc

open MeasureTheory Filter Topology
open Work.EKLContract

noncomputable section

/-- The closed box of matrices whose entries are within `δ` of the identity.  (`V δ` is the open
box; `clBox δ` is compact, which is what makes the "bad return" sets closed.) -/
def clBox (δ : ℝ) : Set SL3 := {g | ∀ i j, |g i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ δ}

/-- `x` has unique displacements of size `< δ`: the orbit map `g ↦ g • x` is injective on `V δ`.
This is EKL's `D_ℓ` with `δ = 1/ℓ`. -/
def Dinj (δ : ℝ) : Set X3 := {x | ∀ g h : SL3, g ∈ V δ → h ∈ V δ → g • x = h • x → g = h}

/-- The diagonal vector of `bconj a b c`: `-1` at `a`, `1` at `b`, `0` at `c`. -/
def uvec (a b c : Fin 3) : Fin 3 → ℝ := fun i => if i = a then -1 else if i = b then 1 else 0

/-- EKL's `α^β` with `β = (-1,1,0)`: conjugation by it contracts the `(a,b)`, `(a,c)`, `(c,b)`
entries and expands (hence keeps zero, for `g ∈ Lset hab`) the `(b,a)`, `(c,a)`, `(b,c)` entries. -/
def bconj (a b c : Fin 3) : SL3 := aDiag (uvec a b c)

/-- The three entries whose vanishing, together with `g ∈ Lset hab`, forces `g` to be diagonal:
the `(a,b)`, `(a,c)` and `(c,b)` entries. -/
def fmax (a b c : Fin 3) (g : SL3) : ℝ := max (max |g a b| |g a c|) |g c b|

/-- The closed set of points of `Dinj (1/ℓu)` carrying a `Lset hab`-return under `aPrime c n` with
displacement in the closed box `clBox (1/(2ℓ))` and `fmax ≥ ε`.  EKL Lemma 4.2 (L9.2): these have
measure zero as soon as `3 * ℓu < ℓ`. -/
def Bad (a b c : Fin 3) (hab : a ≠ b) (ℓ ℓu n : ℕ) (ε : ℝ) : Set X3 :=
  {x | x ∈ Dinj ((ℓu : ℝ)⁻¹) ∧
    ∃ g : SL3, g ∈ clBox ((2 * (ℓ : ℝ))⁻¹) ∧ g ∈ Lset hab ∧
      aPrime c (n : ℝ) • x = g • x ∧ ε ≤ fmax a b c g}

/-- The conclusion of `NonExceptional` at a fixed compact set and a fixed `δ`. -/
def HasNonExcReturn (a b c : Fin 3) (hab : a ≠ b) (δ : ℝ) (K : Set X3) : Prop :=
  ∃ z ∈ K, ∃ s : ℝ, ∃ g ∈ V δ, aPrime c s • z ∈ K ∧ aPrime c s • z = g • z ∧ g ∉ Lset hab

lemma mem_clBox {δ : ℝ} {g : SL3} :
    g ∈ clBox δ ↔ ∀ i j, |g i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ δ := Iff.rfl

lemma mem_Dinj {δ : ℝ} {x : X3} :
    x ∈ Dinj δ ↔ ∀ g h : SL3, g ∈ V δ → h ∈ V δ → g • x = h • x → g = h := Iff.rfl

lemma bconj_eq_aDiag (a b c : Fin 3) : bconj a b c = aDiag (uvec a b c) := rfl

lemma clBox_mono {δ δ' : ℝ} (h : δ ≤ δ') : clBox δ ⊆ clBox δ' :=
  fun g hg i j => le_trans (hg i j) h

lemma Dinj_anti {δ δ' : ℝ} (h : δ ≤ δ') : Dinj δ' ⊆ Dinj δ := by
  intro x hx g h₂ hg hh₂
  exact hx g h₂ (fun i j => lt_of_lt_of_le (hg i j) h) (fun i j => lt_of_lt_of_le (hh₂ i j) h)

end

end Work.EKLNonExc
