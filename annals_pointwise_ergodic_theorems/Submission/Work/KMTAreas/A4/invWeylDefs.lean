/-
# The inverse-Weyl vocabulary of `Work.KMTAreas.A4.invWeylWindow`

This module fixes the statement-shapes used by the proof of the inverse Weyl estimate
`Work.KMTAreas.A4.invWeylWindow` (the estimate cited as "the inverse form of Weyl's exponential
sum estimate, see GT, Lemma A.11" in the proof of Proposition `lip-2` of Krause--Mirek--Tao) and
by the lemmas delegated for it.

## The vocabulary

* `ph Q ξ : ℤ → ℂ` --- the phase sequence `n ↦ e (ξ · Q n)` of an integer polynomial `Q`;
  `ph_norm` records `‖ph Q ξ n‖ = 1`, and `ph_mul_conj_ph` the differencing identity
  `ph Q ξ n * conj (ph Q ξ (n+h)) = ph (Q - Q (X+h)) ξ n`;
* `ovl a b h` --- the overlap window `[a,b] ∩ ([a,b] - h)`, i.e. the `n` with `n ∈ [a,b]` and
  `n + h ∈ [a,b]` (`mem_ovl`); the differenced (correlation) sums of `VdcStatement` are taken over
  `ovl a b h`;
* `VdcStatement` --- **one step of van der Corput** (with the mild length hypothesis
  `8 ≤ ε²L`, which the caller satisfies by choosing `K ≥ 2`): the exact second-moment identity
  `‖∑_{n∈[a,b]} u n‖² = ∑_h ∑_{n ∈ ovl a b h} u n conj (u (n+h))`, followed by the pigeonhole that
  selects the shifts `h` whose correlation sum is large *relative to its own length*;
* `DenseStatement C` --- **GT Lemma 3.1(i)**: a `δ₂`-dense set `T ⊆ [-N,N]` on which
  `‖β n‖ ≤ δ₁`, with `δ₁ ≤ δ₂/4`, forces a rational approximation of `β` with denominator `≤ 8/δ₂`
  and accuracy `C/(δ₂²N)` (Erdős--Turán inequality + the geometric-series bound);
* `AmplifyStatement` --- **GT Lemma 3.1(ii)**: the amplification of `DenseStatement` by the
  `k`-fold-sumset argument, which allows an accuracy `δ₁` much smaller than `δ₂`;
* `IWP d C K` --- **the inverse Weyl estimate at degree `d` with constants `C, K`** (for an
  *integer* polynomial, matching `Work.KMTAreas.A4.invWeyl_one`): if a Weyl sum of a degree-`d`
  phase has amplitude `ε` and the interval is at least `C ε^{-K}` long, then the leading
  coefficient of the phase has a rational approximation with denominator at most `C ε^{-K}` and
  error at most `C ε^{-K}/L^d`, in the integral form `‖q · ξ · Q.coeff d‖ ≤ …`.
-/
import Mathlib
import Submission.Work.KMTAreas.A4.lip2Defs

set_option autoImplicit false

open scoped BigOperators
open Polynomial

namespace Work.KMTAreas.A4

/-- The phase sequence `n ↦ e (ξ · Q n)` of the integer polynomial `Q`. -/
noncomputable def ph (Q : Polynomial ℤ) (ξ : ℝ) : ℤ → ℂ :=
  fun n => Complex.exp (2 * Real.pi * Complex.I * ((ξ * ((Q.eval n : ℤ) : ℝ) : ℝ) : ℂ))

theorem ph_norm (Q : Polynomial ℤ) (ξ : ℝ) (n : ℤ) : ‖ph Q ξ n‖ = 1 := by
  rw [ph, Complex.norm_exp]
  norm_num

/-- The differencing identity: the correlation of the phases of `Q` at the shift `h` is the phase
of the differenced polynomial `Q - Q (X + h)`. -/
theorem ph_mul_conj_ph (Q : Polynomial ℤ) (ξ : ℝ) (n h : ℤ) :
    ph Q ξ n * star (ph Q ξ (n + h)) =
      ph (Q - Q.comp (Polynomial.X + Polynomial.C h)) ξ n := by
  have hstar : ∀ m : ℤ, star (ph Q ξ m) =
      Complex.exp (-(2 * Real.pi * Complex.I * ((ξ * ((Q.eval m : ℤ) : ℝ) : ℝ) : ℂ))) := by
    intro m
    rw [ph, Complex.star_def, ← Complex.exp_conj]
    congr 1
    simp only [map_mul, Complex.conj_I, Complex.conj_ofReal, Complex.conj_ofNat]
    ring
  rw [hstar, ph, ph, ← Complex.exp_add]
  congr 1
  rw [Polynomial.eval_sub, Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X,
    Polynomial.eval_C]
  push_cast
  ring

/-- The overlap window `[a,b] ∩ ([a,b] - h)`: the `n` with `n ∈ [a,b]` and `n + h ∈ [a,b]`. -/
noncomputable def ovl (a b h : ℤ) : Finset ℤ :=
  Finset.Icc (max a (a - h)) (min b (b - h))

theorem mem_ovl {a b h n : ℤ} :
    n ∈ ovl a b h ↔ a ≤ n ∧ n ≤ b ∧ a ≤ n + h ∧ n + h ≤ b := by
  simp only [ovl, Finset.mem_Icc]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨le_trans (le_max_left _ _) h1, le_trans h2 (min_le_left _ _),
      by have := le_trans (le_max_right a (a - h)) h1; omega,
      by have := le_trans h2 (min_le_right b (b - h)); omega⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨max_le h1 (by omega), le_min h2 (by omega)⟩

theorem ovl_subset (a b h : ℤ) : ovl a b h ⊆ Finset.Icc a b := by
  intro n hn
  rw [mem_ovl] at hn
  exact Finset.mem_Icc.mpr ⟨hn.1, hn.2.1⟩

/-- **One van der Corput step** (with the pigeonhole that extracts the good shifts `h`): if the
sum of a unimodular sequence `u` over `[a,b]` has amplitude `ε`, then there is a set `H` of
non-zero shifts with `∑_{h∈H} |ovl a b h| ≥ (ε²/64) L²`, every `h ∈ H` having
`|ovl a b h| ≥ (ε²/64) L`, and the correlation sums over the *overlap* windows large relative to
those lengths: `(ε²/64) |ovl a b h| ≤ ‖∑_{n ∈ ovl a b h} u n * conj (u (n+h))‖`. -/
def VdcStatement : Prop :=
  ∀ (a b : ℤ) (u : ℤ → ℂ) (ε : ℝ), a ≤ b → 0 < ε → ε ≤ 1 →
    8 ≤ ε ^ 2 * (((b - a : ℤ) : ℝ) + 1) → (∀ n : ℤ, ‖u n‖ = 1) →
    ε * (((b - a : ℤ) : ℝ) + 1) ≤ ‖∑ n ∈ Finset.Icc a b, u n‖ →
    ∃ H : Finset ℤ, (∀ h ∈ H, h ≠ 0) ∧ (∀ h ∈ H, -(b - a) ≤ h ∧ h ≤ b - a) ∧
      (∀ h ∈ H, ε ^ 2 / 64 * (((b - a : ℤ) : ℝ) + 1) ≤ ((ovl a b h).card : ℝ)) ∧
      (ε ^ 2 / 64 * (((b - a : ℤ) : ℝ) + 1) ^ 2 ≤ ∑ h ∈ H, ((ovl a b h).card : ℝ)) ∧
      (∀ h ∈ H, ε ^ 2 / 64 * ((ovl a b h).card : ℝ)
        ≤ ‖∑ n ∈ ovl a b h, u n * star (u (n + h))‖)

/-- **Green--Tao Lemma 3.1(i)** with an explicit constant: a dense set of good multiples of `β`
forces a rational approximation of `β`. -/
def DenseStatement (C : ℝ) : Prop :=
  ∀ (β δ₁ δ₂ : ℝ) (N : ℕ) (T : Finset ℤ), 1 ≤ N → 0 < δ₁ → 0 < δ₂ → δ₂ ≤ 1 →
    δ₁ ≤ δ₂ / 4 →
    (∀ n ∈ T, -(N : ℤ) ≤ n ∧ n ≤ (N : ℤ)) →
    δ₂ * (2 * (N : ℝ) + 1) ≤ (T.card : ℝ) →
    (∀ n ∈ T, ∃ m : ℤ, |β * (n : ℝ) - (m : ℝ)| ≤ δ₁) →
    ∃ q : ℕ, 1 ≤ q ∧ (q : ℝ) ≤ 8 / δ₂ ∧
      ∃ a : ℤ, |β - (a : ℝ) / (q : ℝ)| ≤ C / (δ₂ ^ 2 * (N : ℝ))

/-- `DenseStatement` for some positive constant. -/
def DenseExists : Prop := ∃ C : ℝ, 0 < C ∧ DenseStatement C

/-- **Green--Tao Lemma 3.1(ii)**: the amplification of `DenseStatement` by the `k`-fold-sumset
argument, which upgrades a very small accuracy `δ₁ ≤ δ₂²/16` to a rational approximation of
accuracy `δ₁/(δ₂³N)`. -/
def AmplifyStatement : Prop :=
  ∃ C₂ : ℝ, 0 < C₂ ∧ DenseExists →
    ∀ (β δ₁ δ₂ : ℝ) (N : ℕ) (T : Finset ℤ), 2 ≤ N → 0 < δ₁ → 0 < δ₂ → δ₂ ≤ 1 / 2 →
      16 * δ₁ ≤ δ₂ ^ 2 → 2 / δ₂ ≤ (N : ℝ) →
      (∀ n ∈ T, -(N : ℤ) ≤ n ∧ n ≤ (N : ℤ)) →
      δ₂ * (2 * (N : ℝ) + 1) ≤ (T.card : ℝ) →
      (∀ n ∈ T, ∃ m : ℤ, |β * (n : ℝ) - (m : ℝ)| ≤ δ₁) →
      ∃ q : ℕ, 1 ≤ q ∧ (q : ℝ) ≤ C₂ / δ₂ ∧
        ∃ a : ℤ, |β - (a : ℝ) / (q : ℝ)| ≤ C₂ * δ₁ / (δ₂ ^ 3 * (N : ℝ))

/-- **The inverse Weyl estimate at degree `d` with constants `C, K`, for an integer polynomial.** -/
def IWP (d : ℕ) (C K : ℝ) : Prop :=
  ∀ (Q : Polynomial ℤ) (ξ : ℝ) (c : ℂ), Q.natDegree = d → ‖c‖ = 1 → ∀ (a b : ℤ) (ε : ℝ),
    a ≤ b → 0 < ε → ε ≤ 1 → C * ε ^ (-K) ≤ (((b - a : ℤ) : ℝ) + 1) →
    ε * (((b - a : ℤ) : ℝ) + 1) ≤ ‖∑ n ∈ Finset.Icc a b, c * ph Q ξ n‖ →
    ∃ q : ℕ, 1 ≤ q ∧ (q : ℝ) ≤ C * ε ^ (-K) ∧
      ∃ m : ℤ, |(q : ℝ) * ξ * ((Q.coeff d : ℤ) : ℝ) - (m : ℝ)|
        ≤ C * ε ^ (-K) / ((((b - a : ℤ) : ℝ) + 1) ^ d)

end Work.KMTAreas.A4
