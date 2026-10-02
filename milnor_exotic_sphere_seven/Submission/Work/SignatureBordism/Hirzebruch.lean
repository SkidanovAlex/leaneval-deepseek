import Mathlib
import Submission.Work.Milnor.EndgameArith

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The dimension-`4` and dimension-`8` Hirzebruch statements, as interfaces

The endgame of `Submission/NOTES.md` §14.8 needs three inputs: (i) Poincaré duality (`m = ±1`) —
`Work.Cohomology.capped_cupSquare_generates`, consumed here through
`Work.SignatureBordism.sigma_capped_eq_pm_one`; (ii) the characteristic-class value
`p₁(X) = ±6·x` (parallel subproject); and (iii) **the dimension-`8` Hirzebruch identity**

  `45 σ(M) = 7 p₂(M) - p₁(M)²`

for a closed oriented smooth `8`-manifold `M` — the hard core of §8.4.

This file provides the *interface* of (iii): the identity as a predicate on the three numbers
`σ`, `p₁² = ⟨p₁ ⌣ p₁, [M]⟩`, `p₂ = ⟨p₂(TM), [M]⟩` of a closed oriented smooth `8`-manifold, the
arithmetic consequences which the endgame uses, and the check on the two generators of
`Ω^SO_8 ⊗ ℚ`.  What is **not** proved here (and cannot be, with the present library) is that the
numbers of an actual manifold satisfy the identity: the bordism-theoretic proof needs
`Ω^SO_8 ⊗ ℚ = ℚ{ℂP⁴, ℂP² × ℂP²}` (Thom's theorem, or surgery down to `3`-connected
`8`-manifolds) together with multiplicativity of the `L`-genus, and the index-theoretic proof needs
the Dirac operator and the Atiyah–Singer index theorem.  Neither is available; the bordism relation
itself (a compact oriented smooth `9`-manifold with boundary `M ⊔ -N`) is not formalised either,
since the workspace has no manifolds-with-boundary chapter.

The geometry-independent consequence we *can* state and prove is the *reduction*: the identity is
one linear equation in the three numbers, and each of the three is a bordism invariant, so as soon
as one knows that the bordism group is spanned by the classes of `ℂP⁴` and `ℂP² × ℂP²` — where the
numbers are `(σ, p₁², p₂) = (1, 25, 10)` and `(1, 18, 9)` — the identity follows for every closed
oriented smooth `8`-manifold.  Both triples do satisfy it (`hirzebruchEight_generators`), and this
is the whole arithmetic content of the bordism computation.  The same applies in dimension `4`,
where the generator is `ℂP²` (`p₁ = 3σ`).

## Main definitions

* `Work.SignatureBordism.HirzebruchEight σ p₁sq p₂` — the identity `45 σ = 7 p₂ - p₁²`;
* `Work.SignatureBordism.HirzebruchFour σ p₁` — the identity `p₁ = 3 σ`.

## Main results

* `Work.SignatureBordism.hirzebruchEight_congruence` — `45 σ = 7 p₂ - p₁²` implies the congruence
  `p₁² ≡ 4 σ (mod 7)` (the form in which the endgame uses the identity);
* `Work.SignatureBordism.hirzebruchEight_endgame` — the endgame: `m = ±1` (unimodularity, i.e.
  `σ(M) = m`) and `p₁² = c² m` together with the identity force `7 ∣ c² - 4`;
* `Work.SignatureBordism.hirzebruchEight_endgame_six` — the contradiction for Milnor's value
  `p₁(X) = ±6 x`, where `36 ≢ 4 (mod 7)`;
* `Work.SignatureBordism.hirzebruchEight_generators`,
  `Work.SignatureBordism.hirzebruchFour_generator` — the arithmetic check on the generators.
-/

set_option backward.isDefEq.respectTransparency false

namespace Work.SignatureBordism

/-! ## The two Hirzebruch statements as predicates -/

/-- **The dimension-`8` Hirzebruch identity** `45 σ = 7 p₂ - p₁²`, as a predicate on the three
numbers of a closed oriented smooth `8`-manifold `M`: the signature `σ = σ(M)`, the number
`p₁sq = ⟨p₁(TM) ⌣ p₁(TM), [M]⟩` and the number `p₂ = ⟨p₂(TM), [M]⟩`. -/
def HirzebruchEight (σ p₁sq p₂ : ℤ) : Prop := 45 * σ = 7 * p₂ - p₁sq

/-- **The dimension-`4` Hirzebruch (signature) theorem** `p₁(TM) = 3 σ(M)`, as a predicate on the
two numbers of a closed oriented smooth `4`-manifold. -/
def HirzebruchFour (σ p₁ : ℤ) : Prop := p₁ = 3 * σ

/-! ## Arithmetic consequences -/

/-- **The congruence form of the dimension-`8` identity**: `45 σ = 7 p₂ - p₁²` implies
`p₁² ≡ 4 σ (mod 7)`.

This is the form of Hirzebruch's theorem which the endgame of the exotic-`7`-sphere project uses
(`Work.Milnor.endgame_congruence_route'`). -/
theorem hirzebruchEight_congruence (σ p₁sq p₂ : ℤ) (h : HirzebruchEight σ p₁sq p₂) :
    p₁sq ≡ 4 * σ [ZMOD 7] := by
  unfold HirzebruchEight at h
  rw [Int.modEq_iff_dvd]
  exact ⟨7 * σ - p₂, by linarith [h]⟩

/-- **Integrality of Milnor's `λ`-invariant.**  The identity `45 σ = 7 p₂ - p₁²` implies
`7 ∣ p₁² - 4σ`, i.e. the `λ`-invariant `λ = (p₁² - 4σ)/7` of a closed oriented `8`-manifold (Milnor's
form of the obstruction, `Submission/NOTES.md` §8.4) is an integer. -/
theorem hirzebruchEight_lambda_integral (σ p₁sq p₂ : ℤ) (h : HirzebruchEight σ p₁sq p₂) :
    7 ∣ p₁sq - 4 * σ := by
  have h' := hirzebruchEight_congruence σ p₁sq p₂ h
  rw [Int.modEq_iff_dvd] at h'
  exact dvd_neg.mp (by simpa using h')

/-- **The consistency check of `Submission/NOTES.md` §14.7.**  The numbers of `ℍP² = D(L) ∪ D⁸`
(where `L` is the tautological quaternionic line bundle over `S⁴`) are `(σ, p₁², p₂) = (1, 4, 7)`
with `m = ⟨x ⌣ x, [ℍP²]⟩ = 1` and `p₁ = 2x`, and they satisfy *both* the dimension-`8` Hirzebruch
identity (`45·1 = 7·7 - 4`) *and* the spin integrality `5760 ∣ 7 p₁² - 4 p₂` (`28 - 28 = 0`).

Consequently no purely arithmetic argument can rule out the `ℍP²`-like case `c = ±2`: the endgame
genuinely needs the value `p₁(ξ) = ±6` (`c² ≢ 4 mod 7`) or the vanishing of `p₂(X)`, as
`endgame_arithmetic_general` and `endgame_congruence_route'` in `Work.Milnor.EndgameArith` record. -/
theorem hirzebruchEight_hP2_consistency :
    HirzebruchEight 1 (2 ^ 2 * 1) 7 ∧ (5760 : ℤ) ∣ 7 * (2 ^ 2 * 1) - 4 * 7 := by
  refine ⟨by unfold HirzebruchEight; norm_num, by norm_num⟩

/-- **The endgame, geometrically packaged.**  Let `X` be a closed oriented smooth `8`-manifold with
a class `x` generating `H⁴(X;ℤ)` with self-intersection `⟨x ⌣ x, [X]⟩ = m = ±1` (so that
`σ(X) = m`, `Work.SignatureBordism.sigma_of_span_singleton`) and with `p₁(X) = c · x`, so that
`⟨p₁(X)², [X]⟩ = c² m`.  Then the dimension-`8` Hirzebruch identity forces `7 ∣ c² - 4`.

For Milnor's bundle `c = ±6` and `36 ≡ 1 (mod 7)`, so the identity cannot hold — that is
`hirzebruchEight_endgame_six`. -/
theorem hirzebruchEight_endgame (c m p₂ : ℤ) (hm : m = 1 ∨ m = -1)
    (h : HirzebruchEight m (c ^ 2 * m) p₂) : 7 ∣ c ^ 2 - 4 := by
  unfold HirzebruchEight at h
  rcases hm with rfl | rfl
  · have hc : c ^ 2 = 7 * p₂ - 45 := by linarith [h]
    exact ⟨p₂ - 7, by rw [hc]; ring⟩
  · have hc : c ^ 2 = -45 - 7 * p₂ := by linarith [h]
    exact ⟨-7 - p₂, by rw [hc]; ring⟩

/-- **The endgame for Milnor's value `p₁(X) = ±6·x`.**  Unimodularity of the intersection form
(`m = ±1`, so `σ(X) = m`, `p₁² = 36 m` when `p₁ = ±6 x`) is incompatible with the dimension-`8`
Hirzebruch identity: `36 ≢ 4 (mod 7)`. -/
theorem hirzebruchEight_endgame_six (m p₂ : ℤ) (hm : m = 1 ∨ m = -1)
    (h : HirzebruchEight m (36 * m) p₂) : False := by
  unfold HirzebruchEight at h
  have h36 : 36 * m = 6 ^ 2 * m := by ring
  rw [h36] at h
  exact Work.Milnor.six_sq_not_dvd 6 (Or.inl rfl) (hirzebruchEight_endgame 6 m p₂ hm h)

/-! ## The generators of rational oriented bordism -/

/-- **`ℂP⁴` satisfies the identity**: `(σ, p₁², p₂) = (1, 25, 10)`
(`p(TℂP⁴) = (1+x)⁵`, so `p₁ = 5x`, `p₂ = 10x²`, and `σ(ℂP⁴) = 1`). -/
theorem hirzebruchEight_cp4 : HirzebruchEight 1 25 10 := by
  unfold HirzebruchEight; norm_num

/-- **`ℂP² × ℂP²` satisfies the identity**: `(σ, p₁², p₂) = (1, 18, 9)`
(with `H²` spanned by `a`, `b` with `a² = b² = 0` as classes in `H⁴` but `a ⌣ b` the generator of
`H⁴`, the intersection form is `[[1,1],[1,1]]` of signature `1`; `p(T) = (1 + 3a²)(1 + 3b²)`, so
`p₁ = 3(a² + b²)`, `p₂ = 9 a²b²`, `p₁² = 18 a²b²`). -/
theorem hirzebruchEight_cp2cp2 : HirzebruchEight 1 18 9 := by
  unfold HirzebruchEight; norm_num

/-- **The identity holds on both generators of `Ω^SO_8 ⊗ ℚ`.** -/
theorem hirzebruchEight_generators : HirzebruchEight 1 25 10 ∧ HirzebruchEight 1 18 9 :=
  ⟨hirzebruchEight_cp4, hirzebruchEight_cp2cp2⟩

/-- **`ℂP²` satisfies the dimension-`4` identity**: `p₁(TℂP²) = 3x²` against `[ℂP²]`, and
`σ(ℂP²) = 1`. -/
theorem hirzebruchFour_generator : HirzebruchFour 1 3 := by
  unfold HirzebruchFour; norm_num

end Work.SignatureBordism
