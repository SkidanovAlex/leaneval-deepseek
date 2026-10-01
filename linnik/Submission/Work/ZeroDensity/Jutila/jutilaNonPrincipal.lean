import Mathlib
import Submission.Work.LinnikAreas.Setup
import Submission.Work.ZeroDensity.Defs
import Submission.Commons.NumberTheory.DirichletCharacter.zerosInStrip
import Submission.Work.LinnikAreas.boxMaxZero
import Submission.Work.ZeroDensity.Jutila.linnikDensityLemmaReal

open DirichletCharacter
open scoped Classical BigOperators

namespace Work.ZeroDensity.Jutila

/-!
# Jutila's log-free family zero-density bound for the non-principal characters

## The statement and its source

`jutilaNonPrincipal` is

  `Σ_{χ mod q, χ ≠ 1} N(σ,T,χ) ≤ C (qT)^{(2+ε)(1-σ)}`   for `4/5 ≤ σ ≤ 1`, `T ≥ 1`, `q ≥ 2`,

where `N(σ,T,χ) = Work.LinnikAreas.zeroCountIn χ σ T` is the multiplicity-weighted number of zeros
of the completed `L`-function of the primitive character inducing `χ` with `σ ≤ Re ρ ≤ 1` and
`|Im ρ| ≤ T`.

This is **Jutila, *On Linnik's constant*, Math. Scand. 41 (1977) 45-62, Theorem 1, estimate (1.7)**,
in the form quoted by Heath-Brown (1992) as the source of his (1.4):

  (1.7)  `N(σ,T,q) := Σ_{χ mod q} N(σ,T,χ) ≪_ε (qT)^{(2+ε)(1-σ)}`,  `4/5 ≤ σ ≤ 1`, `T ≥ 1`.

Jutila's proof of (1.7) (op. cit., §3, p. 51) restricts to the non-principal characters
("In view of known results about the zeros of `ζ(s)`, we may restrict ourselves to the zeros of
`L(s,χ)` with `χ ≠ χ₀`"), which is precisely the statement proved here; the principal character is
handled there by separate (different) results about `ζ`.
-/

/-!  The proof route of Jutila (Thm. 1), for reference.

* **Far range** `4/5 ≤ σ ≤ 1-ε`: follows from Huxley-Jutila, *Large values of Dirichlet polynomials
  IV*, Acta Arith. 33 (1977) (reference `[6]` of Jutila's paper): the Halasz-Montgomery
  large-values method.
* **Near-line** `σ ≥ 1-ε` (i.e. `λ = (1-σ) log q ≤ ε log q`): Selberg's *pseudocharacters* together
  with **Halasz's inequality**, via the lemmas of Jutila §2:

  1. Lemma 1 - the generating function / Euler product of the pseudocharacter `f_r(n) = f((r,n))`;
  2. Lemmas 2, 3 - the orthogonality relations of pseudocharacters for `f = μ·φ`;
  3. Lemma 4 - the Barban-Vehov/Graham asymptotic for the extremal quadratic form
     `S = Σ_{n≤x} (Σ_{d|n} μ(d) log(z₂/d))²`;
  4. Lemma 5 - `Σ_{r≤R,(r,q)=1} μ(r)²/φ(r) ≫ log R`;
  5. Lemma 6 - the **zero detector**: for a non-principal `χ` and a zero `ρ ∈ R(σ,T)`,
     `|g(ρ,χ)| ≫_ε (φ(q)/q) log R`, estimated by a Mellin/contour argument;
  6. Lemma 7 - **Halasz's inequality** for Dirichlet polynomials;
  7. Lemma 8 - **Linnik's density lemma**: a square of side `(1-σ)` at height `T` contains fewer
     than `(1-σ) log(q(T+1)) + 1` zeros of `L(s,χ)`;
  8. §3 - assembly: split `R(σ,T)` into boxes of height `1/log D` (`D = qT`), choose one zero in
     each box for each character (a `Δ`-well-spaced system of size `J`), apply Halasz's inequality
     to `f(s,χ) = g(s+σ,χ)`, integrate over the parameters `M = e^ξ`, `N = e^η`, and evaluate the
     resulting bilinear forms by Lemma 4 (diagonal) and Lemma 3 (residues), to get
     `J² (φ(q)/q) log²D ≪ J (φ(q)/q)^{2-2σ} log²D + J²`, i.e. (1.7).

The last two steps in particular are heavy (contour integrals, Halasz's inequality); the file
below records the *interface*: the statement, its relation to the all-character form
`FamDensityEpsRange (4/5) 1 2`, and the elementary reduction steps.
-/

/-! ## 1. Elementary facts about the counting function -/

lemma zeroCountIn_nonneg {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (σ T : ℝ) :
    0 ≤ Work.LinnikAreas.zeroCountIn χ σ T := by
  rw [Work.LinnikAreas.zeroCountIn]
  refine finsum_nonneg (fun ρ => ?_)
  by_cases h : σ ≤ ρ.re ∧ ρ.re ≤ 1 ∧ |ρ.im| ≤ T
  · rw [if_pos h]; exact Nat.cast_nonneg _
  · rw [if_neg h]

/-- The non-principal part of a family sum is at most the full family sum (all terms are
non-negative). -/
lemma erase_sum_le_family {q : ℕ} [NeZero q] (σ T : ℝ) :
    (∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
        Work.LinnikAreas.zeroCountIn χ σ T)
      ≤ ∑ χ : DirichletCharacter ℂ q, Work.LinnikAreas.zeroCountIn χ σ T :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
    (fun x _ _ => zeroCountIn_nonneg x σ T)

/-- The sum over the non-principal characters is non-negative. -/
lemma erase_sum_nonneg {q : ℕ} [NeZero q] (σ T : ℝ) :
    0 ≤ ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
        Work.LinnikAreas.zeroCountIn χ σ T :=
  Finset.sum_nonneg (fun χ _ => zeroCountIn_nonneg χ σ T)

/-! ## 2. The relation to the all-character form used by the chapter -/

/-- **`jutilaNonPrincipal` follows from the all-character version.**  If the family estimate
`Σ_{χ mod q} N(σ,T,χ) ≤ C (qT)^{(2+ε)(1-σ)}` (`4/5 ≤ σ ≤ 1`, `T ≥ 1`) is known for *all*
characters - this is exactly the chapter's `FamDensityEpsRange (4/5) 1 2` - then the same bound
holds for the non-principal characters, because the summands are non-negative.  This is the precise
sense in which the requested statement is *weaker* than `Work.LinnikAreas.FamilyZeroDensityJutila`
(Heath-Brown's (1.4) with exponent `2`): Jutila's Theorem 1 supplies the non-principal part of it,
while the principal character `χ = 1` needs separate input about `ζ` (whence the request for the
non-principal form). -/
theorem jutilaNonPrincipal_of_famDensityEpsRange
    (h : Work.ZeroDensity.FamDensityEpsRange (4/5) 1 2) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ q : ℕ, 2 ≤ q → ∀ [NeZero q] (σ T : ℝ), (4 : ℝ) / 5 ≤ σ → σ ≤ 1 → 1 ≤ T →
        (∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
            Work.LinnikAreas.zeroCountIn χ σ T)
          ≤ C * ((q : ℝ) * T) ^ ((2 + ε) * (1 - σ)) := by
  intro ε hε
  obtain ⟨C, hC, hh⟩ := h ε hε
  exact ⟨C, hC, fun q hq _ σ T hσ hσ1 hT =>
    le_trans (erase_sum_le_family σ T) (hh q hq σ T hσ hσ1 hT)⟩

/-- The same reduction, with the all-character hypothesis spelled out. -/
theorem jutilaNonPrincipal_of_allCharacterBound
    (h : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ q : ℕ, 2 ≤ q → ∀ [NeZero q] (σ T : ℝ), (4 : ℝ) / 5 ≤ σ → σ ≤ 1 → 1 ≤ T →
        (∑ χ : DirichletCharacter ℂ q, Work.LinnikAreas.zeroCountIn χ σ T)
          ≤ C * ((q : ℝ) * T) ^ ((2 + ε) * (1 - σ))) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ q : ℕ, 2 ≤ q → ∀ [NeZero q] (σ T : ℝ), (4 : ℝ) / 5 ≤ σ → σ ≤ 1 → 1 ≤ T →
        (∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
            Work.LinnikAreas.zeroCountIn χ σ T)
          ≤ C * ((q : ℝ) * T) ^ ((2 + ε) * (1 - σ)) := by
  intro ε hε
  obtain ⟨C, hC, hh⟩ := h ε hε
  exact ⟨C, hC, fun q hq _ σ T hσ hσ1 hT =>
    le_trans (erase_sum_le_family σ T) (hh q hq σ T hσ hσ1 hT)⟩

/-! ## 3. Monotonicity of the requested statement in `ε` -/

/-- The requested bound is monotone in `ε` (the base `qT` is `≥ 1`). -/
theorem erase_sum_bound_mono_eps {ε₁ ε₂ : ℝ} (hε : ε₁ ≤ ε₂)
    (h : ∀ q : ℕ, 2 ≤ q → ∀ [NeZero q] (σ T : ℝ), (4 : ℝ) / 5 ≤ σ → σ ≤ 1 → 1 ≤ T →
        ∃ C : ℝ, 0 < C ∧
          (∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
              Work.LinnikAreas.zeroCountIn χ σ T)
            ≤ C * ((q : ℝ) * T) ^ ((2 + ε₁) * (1 - σ))) :
    ∀ q : ℕ, 2 ≤ q → ∀ [NeZero q] (σ T : ℝ), (4 : ℝ) / 5 ≤ σ → σ ≤ 1 → 1 ≤ T →
        ∃ C : ℝ, 0 < C ∧
          (∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
              Work.LinnikAreas.zeroCountIn χ σ T)
            ≤ C * ((q : ℝ) * T) ^ ((2 + ε₂) * (1 - σ)) := by
  intro q hq _ σ T hσ hσ1 hT
  obtain ⟨C, hC, hle⟩ := h q hq σ T hσ hσ1 hT
  refine ⟨C, hC, le_trans hle (mul_le_mul_of_nonneg_left ?_ hC.le)⟩
  have hbase : (1 : ℝ) ≤ (q : ℝ) * T := by
    have h2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    nlinarith
  refine Real.rpow_le_rpow_of_exponent_le hbase ?_
  have h1σ : 0 ≤ 1 - σ := by linarith
  nlinarith

/-! ## 4. The statement -/

/-- Jutila's 1977 log-free family zero-density bound, non-principal characters (Math. Scand. 41
(1977) 45-62, Theorem 1, (1.7), non-principal part; the form quoted by Heath-Brown 1992 as the
source of his (1.4)): for every `eps > 0` there is `C > 0` such that for all `q >= 2`, all
`sigma` in `[4/5, 1]` and all `T >= 1`,

  `sum over non-principal chi mod q of N(sigma,T,chi) <= C * (q*T)^((2+eps)*(1-sigma))`,

where `N(sigma,T,chi)` is the multiplicity-weighted number of zeros of the completed L-function of
the *primitive* character inducing `chi` with `sigma <= Re rho <= 1` and `|Im rho| <= T` (this is
`Work.LinnikAreas.zeroCountIn`), and the sum runs over all `chi : DirichletCharacter ℂ q` with
`chi ≠ 1`.

Notes for the prover. (a) The estimate is *log-free*: no power of `log qT` is allowed
(Heath-Brown needs this on the near-line shells of his far-zero decomposition). (b) The principal
character is **excluded**: at `sigma = 4/5` its L-function is essentially `zeta`, and the
corresponding density statement for `zeta` with exponent `2(1-sigma)` is *not known* at
`sigma = 4/5` (Guth-Maynard 2024 give the density hypothesis for `zeta` only down to
`sigma >= 9/10`; Huxley 1971 gives `A(sigma) = 3/(3*sigma-1)`, which is `<= 2` only for
`sigma >= 5/6`). So this statement is strictly weaker than the chapter's
`FamDensityEpsRange (4/5) 1 2`, which sums over all characters. (c) The induction map from
primitive characters of conductor `d | q` to characters mod `q` is injective (one inducing
character per primitive conductor), so the sum over all non-principal `chi` mod `q` is the sum
over primitive characters of conductor dividing `q`; it therefore suffices to prove Jutila's bound
in its primitive-character form and sum over the divisors. (d) A route: zero detector with a
`mu`-mollifier, Cauchy-Schwarz/duality, then the multiplicative large sieve
(`Submission.Work.LinnikAreas.LargeSieve`); the range `sigma >= 4/5` is what makes the
diagonal/off-diagonal split close log-free. -/
theorem jutilaNonPrincipal : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ q : ℕ, 2 ≤ q → ∀ [NeZero q] (σ T : ℝ), (4 : ℝ) / 5 ≤ σ → σ ≤ 1 → 1 ≤ T →
      (∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q), Work.LinnikAreas.zeroCountIn χ σ T)
        ≤ C * ((q : ℝ) * T) ^ ((2 + ε) * (1 - σ)) := by sorry

/-! ## 5. The conductor-fibre decomposition of the non-principal family -/

/-- The non-principal characters mod `q` split into the fibres of the conductor map.  Each
non-empty fibre over a divisor `d ≠ 1` of `q` is, by `Work.ZeroDensity.Jutila.conductorFiber`
(file `Submission/Work/ZeroDensity/Jutila/conductorFiber.lean`), exactly the set of inductions
`changeLevel hd ψ` of the primitive characters `ψ` mod `d`; this is the point (c) of the task
statement. -/
theorem sum_erase_eq_sum_conductorFibers {q : ℕ} [NeZero q] (F : DirichletCharacter ℂ q → ℝ) :
    (∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q), F χ)
      = ∑ d ∈ q.divisors.erase 1,
          ∑ χ ∈ (Finset.univ.erase (1 : DirichletCharacter ℂ q)).filter
              (fun χ => χ.conductor = d), F χ := by
  refine (Finset.sum_fiberwise_of_maps_to ?_ F).symm
  intro χ hχ
  obtain ⟨hχ1, -⟩ := Finset.mem_erase.mp hχ
  refine Finset.mem_erase.mpr ⟨?_, ?_⟩
  · intro hc
    exact hχ1 ((DirichletCharacter.eq_one_iff_conductor_eq_one).mpr hc)
  · exact Nat.mem_divisors.mpr ⟨DirichletCharacter.conductor_dvd_level χ, NeZero.ne q⟩

/-! ## 6. The two halves of the statement (Jutila's own split) -/

/-- **`jutilaNonPrincipal` from its two halves at a split point `σ₀ ∈ [4/5, 1]`.**

Jutila's proof of `(1.7)` splits the range exactly like this: on `4/5 ≤ σ ≤ 1-ε` the far range is
handled by the large-values method (his reference `[6]`, Huxley–Jutila IV), and on `σ ≥ 1-ε` the
near line by Selberg's pseudocharacters together with Halász's inequality.  This lemma records the
(trivial) gluing: the requested statement follows from the two restricted statements with the same
exponent, with the constant being the larger of the two. -/
theorem jutilaNonPrincipal_of_nearLine_and_far {σ₀ : ℝ} (h₀ : (4:ℝ)/5 ≤ σ₀) (h₀1 : σ₀ ≤ 1)
    (hnear : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ q : ℕ, 2 ≤ q → ∀ [NeZero q] (σ T : ℝ), σ₀ ≤ σ → σ ≤ 1 → 1 ≤ T →
        (∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
            Work.LinnikAreas.zeroCountIn χ σ T)
          ≤ C * ((q : ℝ) * T) ^ ((2 + ε) * (1 - σ)))
    (hfar : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ q : ℕ, 2 ≤ q → ∀ [NeZero q] (σ T : ℝ), (4:ℝ)/5 ≤ σ → σ ≤ σ₀ → 1 ≤ T →
        (∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
            Work.LinnikAreas.zeroCountIn χ σ T)
          ≤ C * ((q : ℝ) * T) ^ ((2 + ε) * (1 - σ))) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ q : ℕ, 2 ≤ q → ∀ [NeZero q] (σ T : ℝ), (4 : ℝ) / 5 ≤ σ → σ ≤ 1 → 1 ≤ T →
        (∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
            Work.LinnikAreas.zeroCountIn χ σ T)
          ≤ C * ((q : ℝ) * T) ^ ((2 + ε) * (1 - σ)) := by
  intro ε hε
  obtain ⟨C₁, hC₁, h₁⟩ := hnear ε hε
  obtain ⟨C₂, hC₂, h₂⟩ := hfar ε hε
  refine ⟨max C₁ C₂, lt_max_of_lt_left hC₁, ?_⟩
  intro q hq _ σ T h45 hσ1 hT
  have hbase : (0 : ℝ) ≤ (q : ℝ) * T := by
    have h2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    nlinarith
  have hpow : (0 : ℝ) ≤ ((q : ℝ) * T) ^ ((2 + ε) * (1 - σ)) := Real.rpow_nonneg hbase _
  rcases le_total σ σ₀ with h | h
  · exact le_trans (h₂ q hq σ T h45 h hT)
      (mul_le_mul_of_nonneg_right (le_max_right _ _) hpow)
  · exact le_trans (h₁ q hq σ T h hσ1 hT)
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hpow)


/-! ## 7. The box→zero-count upgrade of Jutila §3 (Lemma 8's application)

Jutila splits the rectangle `R(σ,T)` into boxes of height `Δ = 1/log D` (`D = qT`), selects one
zero in each *occupied* box of each `L(s,χ)`, and proves his estimate for the number `J` of
selected zeros before converting it into the zero count.  The conversion uses Linnik's density
lemma (his Lemma 8, the workspace node `Work.ZeroDensity.Jutila.linnikDensityLemma`): *every*
box contains at most `B` zeros of each `L(s,χ)`, with `B ≪ (1-σ)log(q(T+1)) + 1`.  Hence

  `Σ_{χ ≠ 1} N(σ,T,χ) ≤ B · #{occupied (χ,box) pairs}`,

which is the estimate below.  In §3 the number `J` of the `Δ`-well-spaced system of selected zeros
satisfies `2J ≥ #{occupied pairs}` (split the occupied boxes of each character by the parity of
the box index and keep the larger half), so this lemma is exactly the "sufficient to prove (1.7)
for `J`" step of Jutila's §3 (p. 52).

Nothing here is `L`-function-specific: the per-box bound is an explicit hypothesis, so the lemma
can be instantiated either with the sharp `O(1)` bound (near line, at boxes of height
`Δ ≪ (1-σ)/2`) or with the `(1-σ)log(q(T+1)) + 1` bound of `linnikDensityLemma`. -/

noncomputable section

/-- The **box index** of `ρ` at scale `Δ`: the index `k` of the box
`[kΔ,(k+1)Δ)` containing `Im ρ`. -/
def boxIdx (Δ : ℝ) (ρ : ℂ) : ℤ := ⌊ρ.im / Δ⌋

/-- **The counting lemma of the box upgrade.**  Let `S` be a finite set of points, `f : α → ℝ` a
non-negative weight and `g : α → ι` any map to a decidable set `ι` (here the box index).  If every
one of the fibres `S ∩ g⁻¹{k}` carries mass at most `B`, then the total mass of `S` is at most
`B` times the number of *occupied* fibres. -/
lemma finset_sum_le_card_image_mul {α ι : Type*} [DecidableEq ι] (S : Finset α) (f : α → ℝ)
    (g : α → ι) {B : ℝ}
    (hbox : ∀ k : ι, ∑ a ∈ S.filter (fun a => g a = k), f a ≤ B) :
    ∑ a ∈ S, f a ≤ B * (S.image g).card := by
  rw [← Finset.sum_fiberwise_of_maps_to (s := S) (t := S.image g) (g := g) (f := f)
      (fun i hi => Finset.mem_image_of_mem g hi)]
  calc ∑ j ∈ S.image g, ∑ i ∈ S.filter (fun i => g i = j), f i
      ≤ ∑ j ∈ S.image g, B := Finset.sum_le_sum (fun j _ => hbox j)
    _ = B * (S.image g).card := by
        rw [Finset.sum_const, nsmul_eq_mul]; ring

/-- **The box upgrade for a single character.**  If `S` contains the support of the `zeroCountIn`
summand of `χ` and every box carries at most `B` units of zero mass, then the multiplicity-weighted
zero count of `χ` in the rectangle `σ ≤ Re ρ ≤ 1`, `|Im ρ| ≤ T` is at most `B` times the number of
boxes of `S` that are occupied. -/
theorem zeroCountIn_le_boxCount_mul {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (σ T Δ B : ℝ) (S : Finset ℂ)
    (hS : ∀ ρ : ℂ, (if σ ≤ ρ.re ∧ ρ.re ≤ 1 ∧ |ρ.im| ≤ T
        then (Work.LinnikContract.zeroMult χ ρ : ℝ) else 0) ≠ 0 → ρ ∈ S)
    (hbox : ∀ k : ℤ, ∑ ρ ∈ S.filter (fun ρ => boxIdx Δ ρ = k),
        (if σ ≤ ρ.re ∧ ρ.re ≤ 1 ∧ |ρ.im| ≤ T
          then (Work.LinnikContract.zeroMult χ ρ : ℝ) else 0) ≤ B) :
    Work.LinnikAreas.zeroCountIn χ σ T ≤ B * ((S.image (boxIdx Δ)).card : ℝ) := by
  have h1 : Work.LinnikAreas.zeroCountIn χ σ T
      = ∑ ρ ∈ S, (if σ ≤ ρ.re ∧ ρ.re ≤ 1 ∧ |ρ.im| ≤ T
          then (Work.LinnikContract.zeroMult χ ρ : ℝ) else 0) := by
    rw [Work.LinnikAreas.zeroCountIn]
    refine finsum_eq_sum_of_support_subset _ ?_
    intro x hx
    exact hS x hx
  rw [h1]
  exact finset_sum_le_card_image_mul S _ (boxIdx Δ) hbox

/-- **The box upgrade for the non-principal family** (Jutila §3, p. 52): with the same per-box
bound `B` uniformly in `χ ≠ 1`, the family zero count is at most `B` times the total number of
occupied `(χ, box)` pairs. -/
theorem sum_erase_zeroCountIn_le_boxCount_mul {q : ℕ} [NeZero q] (σ T Δ B : ℝ)
    (S : DirichletCharacter ℂ q → Finset ℂ)
    (hS : ∀ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q), ∀ ρ : ℂ,
      (if σ ≤ ρ.re ∧ ρ.re ≤ 1 ∧ |ρ.im| ≤ T
        then (Work.LinnikContract.zeroMult χ ρ : ℝ) else 0) ≠ 0 → ρ ∈ S χ)
    (hbox : ∀ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q), ∀ k : ℤ,
      ∑ ρ ∈ (S χ).filter (fun ρ => boxIdx Δ ρ = k),
        (if σ ≤ ρ.re ∧ ρ.re ≤ 1 ∧ |ρ.im| ≤ T
          then (Work.LinnikContract.zeroMult χ ρ : ℝ) else 0) ≤ B) :
    (∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
        Work.LinnikAreas.zeroCountIn χ σ T)
      ≤ B * ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
          (((S χ).image (boxIdx Δ)).card : ℝ) := by
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum (fun χ hχ =>
    zeroCountIn_le_boxCount_mul χ σ T Δ B (S χ) (hS χ hχ) (hbox χ hχ))

/-- **The parity bookkeeping of Jutila §3.**  Splitting the occupied boxes of a character by the
parity of the box index and keeping the larger half leaves at least half of them:
`#even + #odd ≤ 2·max #even #odd`.  This is why it suffices to bound the size `J` of the
well-spaced system (Jutila's sentence "let `J` denote the cardinality of the system containing at
least a half of the selected zeros"): `#{occupied (χ,box) pairs} ≤ 2J`. -/
lemma add_le_two_mul_max (m n : ℕ) : m + n ≤ 2 * max m n := by
  rcases le_total m n with h | h
  · rw [max_eq_right h]; omega
  · rw [max_eq_left h]; omega

end

/-- **The parity-split form of the box upgrade.**  Combining the two preceding lemmas: if every
box of the scale-`Δ` partition of `R(σ,T)` carries zero mass at most `B` for every non-principal
`χ`, then the family zero count is at most `2B` times the number of occupied boxes whose index has
a *fixed parity* (the larger of the two parity classes, character by character).

This is the exact sense of Jutila's §3 sentence (p. 52): *"Considering the even and odd numbers
`k` separately, we get two `Δ`-well-spaced systems.  Let `J` denote the cardinality of the system
containing at least a half of the selected zeros.  In view of lemma 8, it is sufficient to prove an
estimate of the type (1.7) for the number `J`."*  The two parity classes are `Δ`-separated inside
each character precisely by `jutila_box_gap` (`Submission/Work/ZeroDensity/Jutila/
wellSpacedExtraction.lean`), so the number occurring on the right is the size of the well-spaced
system to which Halász's inequality (Lemma 7) is applied. -/
theorem erase_zeroCountIn_le_two_mul_paritySplit {q : ℕ} [NeZero q] (σ T Δ B : ℝ) (hB : 0 ≤ B)
    (S : DirichletCharacter ℂ q → Finset ℂ)
    (hS : ∀ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q), ∀ ρ : ℂ,
      (if σ ≤ ρ.re ∧ ρ.re ≤ 1 ∧ |ρ.im| ≤ T
        then (Work.LinnikContract.zeroMult χ ρ : ℝ) else 0) ≠ 0 → ρ ∈ S χ)
    (hbox : ∀ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q), ∀ k : ℤ,
      ∑ ρ ∈ (S χ).filter (fun ρ => boxIdx Δ ρ = k),
        (if σ ≤ ρ.re ∧ ρ.re ≤ 1 ∧ |ρ.im| ≤ T
          then (Work.LinnikContract.zeroMult χ ρ : ℝ) else 0) ≤ B) :
    (∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
        Work.LinnikAreas.zeroCountIn χ σ T)
      ≤ 2 * B * ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
          ((max (((S χ).image (boxIdx Δ)).filter (fun k => _root_.Even k)).card
                (((S χ).image (boxIdx Δ)).filter (fun k => ¬ _root_.Even k)).card : ℕ) : ℝ) := by
  have hmain := sum_erase_zeroCountIn_le_boxCount_mul σ T Δ B S hS hbox
  have hcard : ∀ χ : DirichletCharacter ℂ q,
      (((S χ).image (boxIdx Δ)).card : ℝ)
        ≤ 2 * ((max (((S χ).image (boxIdx Δ)).filter (fun k => _root_.Even k)).card
                (((S χ).image (boxIdx Δ)).filter (fun k => ¬ _root_.Even k)).card : ℕ) : ℝ) := by
    intro χ
    have h := Finset.card_filter_add_card_filter_not (s := (S χ).image (boxIdx Δ)) (p := fun k : ℤ => _root_.Even k)
    have h2 := add_le_two_mul_max
      (((S χ).image (boxIdx Δ)).filter (fun k => _root_.Even k)).card
      (((S χ).image (boxIdx Δ)).filter (fun k => ¬ _root_.Even k)).card
    have : (((S χ).image (boxIdx Δ)).card : ℕ)
        ≤ 2 * max (((S χ).image (boxIdx Δ)).filter (fun k => _root_.Even k)).card
              (((S χ).image (boxIdx Δ)).filter (fun k => ¬ _root_.Even k)).card := by omega
    exact_mod_cast this
  calc (∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
        Work.LinnikAreas.zeroCountIn χ σ T)
      ≤ B * ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
          (((S χ).image (boxIdx Δ)).card : ℝ) := hmain
    _ ≤ B * ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
          2 * ((max (((S χ).image (boxIdx Δ)).filter (fun k => _root_.Even k)).card
                (((S χ).image (boxIdx Δ)).filter (fun k => ¬ _root_.Even k)).card : ℕ) : ℝ) := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun χ _ => hcard χ)) hB
    _ = 2 * B * ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
          ((max (((S χ).image (boxIdx Δ)).filter (fun k => _root_.Even k)).card
                (((S χ).image (boxIdx Δ)).filter (fun k => ¬ _root_.Even k)).card : ℕ) : ℝ) := by
        rw [← Finset.mul_sum]; ring

/-! ## 8. The σ = 1 edge, the per-box bound, and the reduction to the `J`-bound of §3

The chain is: the box partition of the rectangle at scale `Δ = 1/log(qT)` (or any `Δ ≤ 1-σ`,
chosen by the `J`-bound), the per-box bound from Jutila's Lemma 8 at real heights, the parity split
which turns the family zero count into `2B·J`, and finally the `J`-bound itself — the Halász step
of Jutila §3.  Everything except the last is proved here; `JutilaJBound` below is the single
remaining input, and `jutilaNonPrincipal_of_jBound` turns it into the node. -/

/-- **There are no zeros with `Re ρ ≥ 1`** (for a non-principal `χ`): the zeros of the completed
`L`-function of the primitive character inducing `χ` lie in the *open* strip `0 < Re < 1`
(`Commons.NumberTheory.DirichletCharacter.zerosInStrip`), so the rectangle
`σ ≤ Re ρ ≤ 1`, `|Im ρ| ≤ T` is empty of zeros as soon as `σ ≥ 1`.  In particular the target
estimate is trivial at `σ = 1`. -/
theorem zeroCountIn_eq_zero_of_one_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) {σ T : ℝ} (hσ : 1 ≤ σ) : Work.LinnikAreas.zeroCountIn χ σ T = 0 := by
  rw [Work.LinnikAreas.zeroCountIn]
  have hzero : ∀ ρ : ℂ,
      (if σ ≤ ρ.re ∧ ρ.re ≤ 1 ∧ |ρ.im| ≤ T
        then (Work.LinnikContract.zeroMult χ ρ : ℝ) else 0) = 0 := by
    intro ρ
    by_cases h : σ ≤ ρ.re ∧ ρ.re ≤ 1 ∧ |ρ.im| ≤ T
    · rw [if_pos h]
      have hzm : Work.LinnikContract.zeroMult χ ρ = 0 := by
        by_contra hne
        haveI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
        have hψ1 : χ.primitiveCharacter ≠ (1 : DirichletCharacter ℂ χ.conductor) := by
          intro h1
          have hh := DirichletCharacter.changeLevel_primitiveCharacter χ
          rw [h1, DirichletCharacter.changeLevel_one χ.conductor_dvd_level] at hh
          exact hχ hh.symm
        have hprim : χ.primitiveCharacter.IsPrimitive :=
          DirichletCharacter.primitiveCharacter_isPrimitive χ
        have hord : analyticOrderNatAt
            (DirichletCharacter.completedLFunction χ.primitiveCharacter) ρ ≠ 0 := by
          simpa only [Work.LinnikContract.zeroMult] using hne
        have hz : DirichletCharacter.completedLFunction χ.primitiveCharacter ρ = 0 :=
          apply_eq_zero_of_analyticOrderNatAt_ne_zero hord
        have hstrip := Commons.NumberTheory.DirichletCharacter.zerosInStrip
          χ.primitiveCharacter hψ1 hprim ρ hz
        have hlt : ρ.re < 1 := hstrip.2
        have heq : ρ.re = 1 := le_antisymm h.2.1 (le_trans hσ h.1)
        linarith
      rw [hzm]; simp
    · rw [if_neg h]
  rw [show (∑ᶠ ρ : ℂ, (if σ ≤ ρ.re ∧ ρ.re ≤ 1 ∧ |ρ.im| ≤ T
        then (Work.LinnikContract.zeroMult χ ρ : ℝ) else 0))
      = ∑ᶠ _ : ℂ, (0 : ℝ) from finsum_congr hzero]
  simp

/-- **Finiteness of the zero support of `zeroCountIn`.**  For every character `χ` (principal
included) the set of zeros counted by `zeroCountIn` is finite. -/
lemma zeroSupport_finite {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (σ T : ℝ) :
    Function.HasFiniteSupport (fun ρ : ℂ =>
      if σ ≤ ρ.re ∧ ρ.re ≤ 1 ∧ |ρ.im| ≤ T
        then (Work.LinnikContract.zeroMult χ ρ : ℝ) else 0) := by
  rw [Function.HasFiniteSupport]
  refine (Work.LinnikAreas.boxMaxZeroAux.finite_zeroMult_box χ σ T).subset ?_
  intro ρ hρ
  rw [Function.mem_support] at hρ
  by_cases h : σ ≤ ρ.re ∧ ρ.re ≤ 1 ∧ |ρ.im| ≤ T
  · rw [if_pos h] at hρ
    exact ⟨fun h0 => hρ (by exact_mod_cast h0), h.1, h.2.1, h.2.2⟩
  · rw [if_neg h] at hρ
    exact absurd rfl hρ

/-- **The `S`-restricted box sum is at most the global box mass.** -/
lemma sum_filter_boxIdx_le_boxMass {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (σ T Δ : ℝ)
    (S : Finset ℂ)
    (hS : ∀ ρ : ℂ, (if σ ≤ ρ.re ∧ ρ.re ≤ 1 ∧ |ρ.im| ≤ T
        then (Work.LinnikContract.zeroMult χ ρ : ℝ) else 0) ≠ 0 → ρ ∈ S) (k : ℤ) :
    ∑ ρ ∈ S.filter (fun ρ => boxIdx Δ ρ = k),
      (if σ ≤ ρ.re ∧ ρ.re ≤ 1 ∧ |ρ.im| ≤ T
        then (Work.LinnikContract.zeroMult χ ρ : ℝ) else 0)
      ≤ ∑ᶠ ρ : ℂ, if σ ≤ ρ.re ∧ ρ.re ≤ 1 ∧ |ρ.im| ≤ T ∧ boxIdx Δ ρ = k
          then (Work.LinnikContract.zeroMult χ ρ : ℝ) else 0 := by
  have h1 : ∑ ρ ∈ S.filter (fun ρ => boxIdx Δ ρ = k),
        (if σ ≤ ρ.re ∧ ρ.re ≤ 1 ∧ |ρ.im| ≤ T
          then (Work.LinnikContract.zeroMult χ ρ : ℝ) else 0)
      = ∑ ρ ∈ S.filter (fun ρ => boxIdx Δ ρ = k),
        (if σ ≤ ρ.re ∧ ρ.re ≤ 1 ∧ |ρ.im| ≤ T ∧ boxIdx Δ ρ = k
          then (Work.LinnikContract.zeroMult χ ρ : ℝ) else 0) := by
    refine Finset.sum_congr rfl (fun ρ hρ => ?_)
    rw [Finset.mem_filter] at hρ
    by_cases h : σ ≤ ρ.re ∧ ρ.re ≤ 1 ∧ |ρ.im| ≤ T
    · rw [if_pos h, if_pos ⟨h.1, h.2.1, h.2.2, hρ.2⟩]
    · rw [if_neg h, if_neg (fun hc => h ⟨hc.1, hc.2.1, hc.2.2.1⟩)]
  rw [h1]
  refine le_of_eq ?_
  refine (finsum_eq_sum_of_support_subset _ ?_).symm
  intro ρ hρ
  rw [Function.mem_support] at hρ
  simp only [Finset.mem_coe, Finset.mem_filter]
  by_cases h : σ ≤ ρ.re ∧ ρ.re ≤ 1 ∧ |ρ.im| ≤ T ∧ boxIdx Δ ρ = k
  · rw [if_pos h] at hρ
    exact ⟨hS ρ (by rw [if_pos ⟨h.1, h.2.1, h.2.2.1⟩]; exact hρ), h.2.2.2⟩
  · rw [if_neg h] at hρ
    exact absurd rfl hρ

/-- Finiteness of the support of a square-zero summand. -/
lemma zeroMult_boxSupport_finite {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (a t R : ℝ) :
    Function.HasFiniteSupport (fun ρ : ℂ =>
      if Work.LinnikContract.zeroMult χ ρ ≠ 0 ∧ a ≤ ρ.re ∧ ρ.re ≤ 1 ∧ |ρ.im - t| ≤ R
        then (Work.LinnikContract.zeroMult χ ρ : ℝ) else 0) := by
  rw [Function.HasFiniteSupport]
  refine (Work.LinnikAreas.boxMaxZeroAux.finite_zeroMult_box χ a (|t| + R)).subset ?_
  intro ρ hρ
  rw [Function.mem_support] at hρ
  by_cases h : Work.LinnikContract.zeroMult χ ρ ≠ 0 ∧ a ≤ ρ.re ∧ ρ.re ≤ 1 ∧ |ρ.im - t| ≤ R
  · rw [if_pos h] at hρ
    refine ⟨fun h0 => hρ (by exact_mod_cast h0), h.2.1, h.2.2.1, ?_⟩
    calc |ρ.im| = |t + (ρ.im - t)| := by rw [show t + (ρ.im - t) = ρ.im by ring]
      _ ≤ |t| + |ρ.im - t| := abs_add_le t (ρ.im - t)
      _ ≤ |t| + R := by linarith [h.2.2.2]
  · rw [if_neg h] at hρ
    exact absurd rfl hρ

/-- **The per-box bound.**  Every box of the scale-`Δ` partition of `σ ≤ Re ρ ≤ 1`,
`|Im ρ| ≤ T` (`Δ ≤ 1-σ`, `4/5 ≤ σ ≤ 1`, `T ≥ 1`) carries at most
`≪ (1-σ)log(q(T+1)) + 1` units of multiplicity-weighted zero mass, uniformly in `χ ≠ 1`; this is
Jutila's Lemma 8 (`Work.ZeroDensity.Jutila.linnikDensityLemmaReal`) applied to the square of side
`(1-σ)` attached to `Re = 1` at the centre `(k+1/2)Δ` of the box. -/
theorem boxMass_le_linnik_real :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ q : ℕ, 2 ≤ q → ∀ [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ∀ σ T Δ : ℝ, (4 : ℝ) / 5 ≤ σ → σ ≤ 1 → 1 ≤ T → 0 < Δ → Δ ≤ 1 - σ → ∀ k : ℤ,
        (∑ᶠ ρ : ℂ, if σ ≤ ρ.re ∧ ρ.re ≤ 1 ∧ |ρ.im| ≤ T ∧ boxIdx Δ ρ = k
          then (Work.LinnikContract.zeroMult χ ρ : ℝ) else 0)
        ≤ C₀ * ((1 - σ) * Real.log ((q : ℝ) * (T + 1)) + 1) := by
  obtain ⟨C, hC, hCb⟩ := linnikDensityLemmaReal
  refine ⟨3 * C, by positivity, ?_⟩
  intro q hq _inst χ hχ σ T Δ h45 hσ1 hT hΔpos hΔle k
  have hσ0 : (0 : ℝ) ≤ σ := by linarith
  have hΔhalf : Δ / 2 ≤ (1 - σ) / 2 := by linarith [hΔle]
  have hF : (0 : ℝ) ≤ 1 - σ := by linarith
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast (by omega : 1 ≤ q)
  have hL : (0 : ℝ) ≤ Real.log ((q : ℝ) * (T + 1)) := by
    refine Real.log_nonneg ?_
    nlinarith
  set t : ℝ := ((k : ℝ) + 1 / 2) * Δ with ht
  have hfinR : Function.HasFiniteSupport (fun ρ : ℂ =>
      if Work.LinnikContract.zeroMult χ ρ ≠ 0 ∧ σ ≤ ρ.re ∧ ρ.re ≤ 1 ∧ |ρ.im - t| ≤ (1 - σ) / 2
        then (Work.LinnikContract.zeroMult χ ρ : ℝ) else 0) :=
    zeroMult_boxSupport_finite χ σ t ((1 - σ) / 2)
  have hfinL : Function.HasFiniteSupport (fun ρ : ℂ =>
      if σ ≤ ρ.re ∧ ρ.re ≤ 1 ∧ |ρ.im| ≤ T ∧ boxIdx Δ ρ = k
        then (Work.LinnikContract.zeroMult χ ρ : ℝ) else 0) := by
    rw [Function.HasFiniteSupport]
    refine (zeroSupport_finite χ σ T).subset ?_
    intro ρ hρ
    rw [Function.mem_support] at hρ
    by_cases hc : σ ≤ ρ.re ∧ ρ.re ≤ 1 ∧ |ρ.im| ≤ T ∧ boxIdx Δ ρ = k
    · rw [if_pos hc] at hρ
      rw [Function.mem_support, if_pos ⟨hc.1, hc.2.1, hc.2.2.1⟩]
      exact hρ
    · rw [if_neg hc] at hρ
      exact absurd rfl hρ
  have hboxest : ∀ ρ : ℂ, boxIdx Δ ρ = k → |ρ.im - t| ≤ (1 - σ) / 2 := by
    intro ρ hb
    have hfl : ((k : ℝ)) ≤ ρ.im / Δ ∧ ρ.im / Δ < (k : ℝ) + 1 := Int.floor_eq_iff.mp hb
    have h1 : (k : ℝ) * Δ ≤ ρ.im := (le_div_iff₀ hΔpos).mp hfl.1
    have h2 : ρ.im < ((k : ℝ) + 1) * Δ := (div_lt_iff₀ hΔpos).mp hfl.2
    have h3 : |ρ.im - t| ≤ Δ / 2 := by
      rw [abs_le]
      constructor
      · rw [ht]; nlinarith
      · rw [ht]; nlinarith
    linarith
  have hpt : (fun ρ : ℂ => (if σ ≤ ρ.re ∧ ρ.re ≤ 1 ∧ |ρ.im| ≤ T ∧ boxIdx Δ ρ = k
        then (Work.LinnikContract.zeroMult χ ρ : ℝ) else 0))
      ≤ (fun ρ : ℂ => (if Work.LinnikContract.zeroMult χ ρ ≠ 0 ∧ σ ≤ ρ.re ∧ ρ.re ≤ 1 ∧
          |ρ.im - t| ≤ (1 - σ) / 2
        then (Work.LinnikContract.zeroMult χ ρ : ℝ) else 0)) := by
    intro ρ
    dsimp only
    by_cases h : σ ≤ ρ.re ∧ ρ.re ≤ 1 ∧ |ρ.im| ≤ T ∧ boxIdx Δ ρ = k
    · rw [if_pos h]
      by_cases hz : Work.LinnikContract.zeroMult χ ρ = 0
      · simp [hz]
      · rw [if_pos ⟨hz, h.1, h.2.1, hboxest ρ h.2.2.2⟩]
    · rw [if_neg h]
      by_cases hR : Work.LinnikContract.zeroMult χ ρ ≠ 0 ∧ σ ≤ ρ.re ∧ ρ.re ≤ 1 ∧
          |ρ.im - t| ≤ (1 - σ) / 2
      · rw [if_pos hR]; exact Nat.cast_nonneg _
      · rw [if_neg hR]
  have hcmp : (∑ᶠ ρ : ℂ, if σ ≤ ρ.re ∧ ρ.re ≤ 1 ∧ |ρ.im| ≤ T ∧ boxIdx Δ ρ = k
        then (Work.LinnikContract.zeroMult χ ρ : ℝ) else 0)
      ≤ (∑ᶠ ρ : ℂ, if Work.LinnikContract.zeroMult χ ρ ≠ 0 ∧ σ ≤ ρ.re ∧ ρ.re ≤ 1 ∧
          |ρ.im - t| ≤ (1 - σ) / 2
        then (Work.LinnikContract.zeroMult χ ρ : ℝ) else 0) :=
    finsum_le_finsum' hfinL hfinR hpt
  have hlin := hCb q hq χ hχ σ t hσ0 hσ1
  have htarget : (0 : ℝ) ≤ 3 * C * ((1 - σ) * Real.log ((q : ℝ) * (T + 1)) + 1) := by
    have hprod : (0 : ℝ) ≤ (1 - σ) * Real.log ((q : ℝ) * (T + 1)) := mul_nonneg hF hL
    have h1 : (0 : ℝ) < (1 - σ) * Real.log ((q : ℝ) * (T + 1)) + 1 := by linarith
    have h2 : (0 : ℝ) < 3 * C := by linarith [hC]
    exact le_of_lt (mul_pos h2 h1)
  by_cases hlarge : T + 1 < |t|
  · have hzero : ∀ ρ : ℂ, (if σ ≤ ρ.re ∧ ρ.re ≤ 1 ∧ |ρ.im| ≤ T ∧ boxIdx Δ ρ = k
        then (Work.LinnikContract.zeroMult χ ρ : ℝ) else 0) = 0 := by
      intro ρ
      by_cases hc : σ ≤ ρ.re ∧ ρ.re ≤ 1 ∧ |ρ.im| ≤ T ∧ boxIdx Δ ρ = k
      · rw [if_pos hc]
        by_cases hz : Work.LinnikContract.zeroMult χ ρ = 0
        · simp [hz]
        · exfalso
          have h3 : |ρ.im - t| ≤ Δ / 2 := by
            have hfl : ((k : ℝ)) ≤ ρ.im / Δ ∧ ρ.im / Δ < (k : ℝ) + 1 :=
              Int.floor_eq_iff.mp hc.2.2.2
            have h1 : (k : ℝ) * Δ ≤ ρ.im := (le_div_iff₀ hΔpos).mp hfl.1
            have h2 : ρ.im < ((k : ℝ) + 1) * Δ := (div_lt_iff₀ hΔpos).mp hfl.2
            rw [abs_le]
            exact ⟨by rw [ht]; nlinarith, by rw [ht]; nlinarith⟩
          have h5 : |t - ρ.im| ≤ Δ / 2 := by rwa [abs_sub_comm] at h3
          have h4 : |t| ≤ T + Δ / 2 := by
            calc |t| = |ρ.im + (t - ρ.im)| := by
                  rw [show ρ.im + (t - ρ.im) = t by ring]
              _ ≤ |ρ.im| + |t - ρ.im| := abs_add_le ρ.im (t - ρ.im)
              _ ≤ T + Δ / 2 := by linarith [hc.2.2.1, h5]
          have h6 : Δ / 2 < 1 := by linarith [hΔle, h45]
          linarith [h4, h6, hlarge]
      · rw [if_neg hc]
    have hsum0 : (∑ᶠ ρ : ℂ, if σ ≤ ρ.re ∧ ρ.re ≤ 1 ∧ |ρ.im| ≤ T ∧ boxIdx Δ ρ = k
        then (Work.LinnikContract.zeroMult χ ρ : ℝ) else 0) = 0 := by
      rw [show (∑ᶠ ρ : ℂ, (if σ ≤ ρ.re ∧ ρ.re ≤ 1 ∧ |ρ.im| ≤ T ∧ boxIdx Δ ρ = k
          then (Work.LinnikContract.zeroMult χ ρ : ℝ) else 0))
          = ∑ᶠ _ : ℂ, (0 : ℝ) from finsum_congr hzero]
      simp
    rw [hsum0]
    exact htarget
  · push Not at hlarge
    have hlog : Real.log ((q : ℝ) * (|t| + 2)) ≤ Real.log ((q : ℝ) * (T + 1)) + Real.log 3 := by
      rw [← Real.log_mul (x := (q : ℝ) * (T + 1)) (y := 3)
        (ne_of_gt (by positivity : (0 : ℝ) < (q : ℝ) * (T + 1)))
        (by norm_num : (3 : ℝ) ≠ 0)]
      refine Real.log_le_log (by positivity) ?_
      have h1 : |t| + 2 ≤ 3 * (T + 1) := by linarith
      nlinarith
    have hlog3 : Real.log 3 ≤ 2 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num)
      linarith
    have hinner : (1 - σ) * (Real.log ((q : ℝ) * (T + 1)) + Real.log 3) + 1
        ≤ 3 * ((1 - σ) * Real.log ((q : ℝ) * (T + 1)) + 1) := by
      have h1 : (1 - σ) * Real.log 3 ≤ 2 * (1 - σ) := by
        have := mul_le_mul_of_nonneg_left hlog3 hF
        linarith
      have hPL : 0 ≤ (1 - σ) * Real.log ((q : ℝ) * (T + 1)) := mul_nonneg hF hL
      nlinarith
    calc (∑ᶠ ρ : ℂ, if σ ≤ ρ.re ∧ ρ.re ≤ 1 ∧ |ρ.im| ≤ T ∧ boxIdx Δ ρ = k
          then (Work.LinnikContract.zeroMult χ ρ : ℝ) else 0)
        ≤ (∑ᶠ ρ : ℂ, if Work.LinnikContract.zeroMult χ ρ ≠ 0 ∧ σ ≤ ρ.re ∧ ρ.re ≤ 1 ∧
            |ρ.im - t| ≤ (1 - σ) / 2
          then (Work.LinnikContract.zeroMult χ ρ : ℝ) else 0) := hcmp
      _ ≤ C * ((1 - σ) * Real.log ((q : ℝ) * (|t| + 2)) + 1) := hlin
      _ ≤ C * ((1 - σ) * (Real.log ((q : ℝ) * (T + 1)) + Real.log 3) + 1) := by
          have h := mul_le_mul_of_nonneg_left hlog hF
          have := mul_le_mul_of_nonneg_left
            (by linarith : (1 - σ) * Real.log ((q : ℝ) * (|t| + 2)) + 1
              ≤ (1 - σ) * (Real.log ((q : ℝ) * (T + 1)) + Real.log 3) + 1) hC.le
          exact this
      _ ≤ 3 * C * ((1 - σ) * Real.log ((q : ℝ) * (T + 1)) + 1) := by
          calc C * ((1 - σ) * (Real.log ((q : ℝ) * (T + 1)) + Real.log 3) + 1)
              ≤ C * (3 * ((1 - σ) * Real.log ((q : ℝ) * (T + 1)) + 1)) :=
                mul_le_mul_of_nonneg_left hinner hC.le
            _ = 3 * C * ((1 - σ) * Real.log ((q : ℝ) * (T + 1)) + 1) := by ring

/-- The **occupied box indices** of one character: the image of the zero support (at scale `Δ`). -/
noncomputable def zeroBoxes {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (σ T Δ : ℝ) :
    Finset ℤ :=
  (Set.Finite.toFinset (zeroSupport_finite χ σ T)).image (boxIdx Δ)

/-- **The `J`-bound of Jutila §3** — the single remaining deep input of `jutilaNonPrincipal`.
For every `ε > 0` there is `C > 0` such that for all `q ≥ 2`, all `σ` with `4/5 ≤ σ < 1`, all
`T ≥ 1`, there is a box scale `Δ ∈ (0, 1-σ]` for which the number `J` of the *larger parity class*
of occupied boxes (`⌊Im ρ/Δ⌋`, one box per occupied index, split by the parity of the index) is at
most `C·(qT)^{(2+ε)(1-σ)}/((1-σ)log(q(T+1)) + 1)`.

The logarithmic factor is the per-box mass of Lemma 8: the parity split gives
`Σ_{χ≠1} N(σ,T,χ) ≤ 2·B·J` with `B ≍ (1-σ)log(q(T+1)) + 1` (`boxMass_le_linnik_real` +
`erase_zeroCountIn_le_two_mul_paritySplit`), so `J` has to carry that saving.  The boxes of one
parity class are `Δ`-separated inside each character (`jutila_box_gap`), so `J` is the size of the
`Δ`-well-spaced system to which Jutila applies Halász's inequality (Lemma 7,
`Commons.NumberTheory.DirichletCharacter.halasz_inequality`); the lemma is proved by the duality
frame `Work.ZeroDensity.Jutila.halaszDualityFrame`, whose two slots are the detector (Jutila's
Lemma 6) and the evaluation of the bilinear form `B(s,χ) = Σ_m b_m χ(m)m^{-s}` (Lemmas 2, 3 and
Graham's Lemma 4). -/
def JutilaJBound : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ q : ℕ, 2 ≤ q → ∀ [NeZero q] (σ T : ℝ), (4 : ℝ) / 5 ≤ σ → σ < 1 → 1 ≤ T →
      ∃ Δ : ℝ, 0 < Δ ∧ Δ ≤ 1 - σ ∧
        (∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
            ((max ((zeroBoxes χ σ T Δ).filter (fun k => _root_.Even k)).card
                  ((zeroBoxes χ σ T Δ).filter (fun k => ¬ _root_.Even k)).card : ℕ) : ℝ))
          ≤ C * ((q : ℝ) * T) ^ ((2 + ε) * (1 - σ))
              / ((1 - σ) * Real.log ((q : ℝ) * (T + 1)) + 1)

/-- **`jutilaNonPrincipal` from the `J`-bound alone.**  Everything else (the box upgrade, the
per-box bound from Linnik's density lemma at real heights, and the `σ = 1` edge) is proved in this
file. -/
theorem jutilaNonPrincipal_of_jBound (hJ : JutilaJBound) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ q : ℕ, 2 ≤ q → ∀ [NeZero q] (σ T : ℝ), (4 : ℝ) / 5 ≤ σ → σ ≤ 1 → 1 ≤ T →
        (∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
            Work.LinnikAreas.zeroCountIn χ σ T)
          ≤ C * ((q : ℝ) * T) ^ ((2 + ε) * (1 - σ)) := by
  obtain ⟨C₀, hC₀, hbox⟩ := boxMass_le_linnik_real
  intro ε hε
  obtain ⟨C, hC, hh⟩ := hJ ε hε
  refine ⟨2 * C₀ * C, by positivity, ?_⟩
  intro q hq _inst σ T h45 hσ1 hT
  rcases lt_or_eq_of_le hσ1 with hσlt | hσeq
  · obtain ⟨Δ, hΔpos, hΔle, hJb⟩ := hh q hq σ T h45 hσlt hT
    have hFpos : 0 < (1 - σ) * Real.log ((q : ℝ) * (T + 1)) + 1 := by
      have h1 : (1 : ℝ) < (q : ℝ) * (T + 1) := by
        have h2 : (1 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 1 < q)
        nlinarith
      have h2 : (0 : ℝ) ≤ 1 - σ := by linarith
      have h3 : (0 : ℝ) < Real.log ((q : ℝ) * (T + 1)) := Real.log_pos h1
      nlinarith [mul_nonneg h2 h3.le]
    have hFne : ((1 - σ) * Real.log ((q : ℝ) * (T + 1)) + 1) ≠ 0 := ne_of_gt hFpos
    have hS : ∀ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q), ∀ ρ : ℂ,
        (if σ ≤ ρ.re ∧ ρ.re ≤ 1 ∧ |ρ.im| ≤ T
          then (Work.LinnikContract.zeroMult χ ρ : ℝ) else 0) ≠ 0 →
        ρ ∈ Set.Finite.toFinset (zeroSupport_finite χ σ T) := by
      intro χ _ ρ hρ
      exact (Set.Finite.mem_toFinset (hs := zeroSupport_finite χ σ T)).mpr
        (Function.mem_support.mpr hρ)
    have hboxΔ : ∀ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q), ∀ k : ℤ,
        ∑ ρ ∈ (Set.Finite.toFinset (zeroSupport_finite χ σ T)).filter
            (fun ρ => boxIdx Δ ρ = k),
          (if σ ≤ ρ.re ∧ ρ.re ≤ 1 ∧ |ρ.im| ≤ T
            then (Work.LinnikContract.zeroMult χ ρ : ℝ) else 0)
          ≤ C₀ * ((1 - σ) * Real.log ((q : ℝ) * (T + 1)) + 1) := by
      intro χ hχ k
      refine le_trans (sum_filter_boxIdx_le_boxMass χ σ T Δ _ (hS χ hχ) k) ?_
      exact hbox q hq χ (Finset.mem_erase.mp hχ).1 σ T Δ h45 (le_of_lt hσlt) hT hΔpos hΔle k
    have hsplit := erase_zeroCountIn_le_two_mul_paritySplit σ T Δ
      (C₀ * ((1 - σ) * Real.log ((q : ℝ) * (T + 1)) + 1))
      (mul_nonneg hC₀.le hFpos.le)
      (fun χ => Set.Finite.toFinset (zeroSupport_finite χ σ T)) hS hboxΔ
    have hb0 : (0 : ℝ) ≤ 2 * (C₀ * ((1 - σ) * Real.log ((q : ℝ) * (T + 1)) + 1)) :=
      mul_nonneg (by norm_num) (mul_nonneg hC₀.le hFpos.le)
    have heq : 2 * (C₀ * ((1 - σ) * Real.log ((q : ℝ) * (T + 1)) + 1))
          * (C * ((q : ℝ) * T) ^ ((2 + ε) * (1 - σ))
              / ((1 - σ) * Real.log ((q : ℝ) * (T + 1)) + 1))
        = 2 * C₀ * C * ((q : ℝ) * T) ^ ((2 + ε) * (1 - σ)) := by
      have h1 : ((1 - σ) * Real.log ((q : ℝ) * (T + 1)) + 1)
          * (C * ((q : ℝ) * T) ^ ((2 + ε) * (1 - σ))
              / ((1 - σ) * Real.log ((q : ℝ) * (T + 1)) + 1))
          = C * ((q : ℝ) * T) ^ ((2 + ε) * (1 - σ)) := by
        rw [mul_div_assoc', mul_div_cancel_left₀ _ hFne]
      calc 2 * (C₀ * ((1 - σ) * Real.log ((q : ℝ) * (T + 1)) + 1))
            * (C * ((q : ℝ) * T) ^ ((2 + ε) * (1 - σ))
                / ((1 - σ) * Real.log ((q : ℝ) * (T + 1)) + 1))
          = 2 * C₀ * (((1 - σ) * Real.log ((q : ℝ) * (T + 1)) + 1)
              * (C * ((q : ℝ) * T) ^ ((2 + ε) * (1 - σ))
                  / ((1 - σ) * Real.log ((q : ℝ) * (T + 1)) + 1))) := by ring
        _ = 2 * C₀ * (C * ((q : ℝ) * T) ^ ((2 + ε) * (1 - σ))) := by rw [h1]
        _ = 2 * C₀ * C * ((q : ℝ) * T) ^ ((2 + ε) * (1 - σ)) := by ring
    calc (∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
            Work.LinnikAreas.zeroCountIn χ σ T)
        ≤ 2 * (C₀ * ((1 - σ) * Real.log ((q : ℝ) * (T + 1)) + 1))
            * ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
              ((max (((Set.Finite.toFinset (zeroSupport_finite χ σ T)).image (boxIdx Δ)).filter
                      (fun k => _root_.Even k)).card
                    (((Set.Finite.toFinset (zeroSupport_finite χ σ T)).image (boxIdx Δ)).filter
                      (fun k => ¬ _root_.Even k)).card : ℕ) : ℝ) := hsplit
      _ ≤ 2 * (C₀ * ((1 - σ) * Real.log ((q : ℝ) * (T + 1)) + 1))
            * (C * ((q : ℝ) * T) ^ ((2 + ε) * (1 - σ))
                / ((1 - σ) * Real.log ((q : ℝ) * (T + 1)) + 1)) :=
          mul_le_mul_of_nonneg_left hJb hb0
      _ = 2 * C₀ * C * ((q : ℝ) * T) ^ ((2 + ε) * (1 - σ)) := heq
  · rw [hσeq, Finset.sum_eq_zero (fun χ hχ =>
        zeroCountIn_eq_zero_of_one_le χ (Finset.mem_erase.mp hχ).1 le_rfl)]
    rw [sub_self, mul_zero, Real.rpow_zero, mul_one]
    have hfin : (0 : ℝ) ≤ 2 * C₀ * C := by
      have := mul_nonneg hC₀.le hC.le
      linarith
    simpa using hfin

/-! ## 11. Jutila's own split of the `J`-bound: near line (`σ ≥ 1-ε`) and far range

Jutila proves the far range `4/5 ≤ σ ≤ 1-ε` from his reference `[6]` (Huxley–Jutila, *Large values
of Dirichlet polynomials IV*) and the near line `σ ≥ 1-ε` from Selberg's pseudocharacters together
with Halász's inequality (§3 of his paper).  The two halves of `JutilaJBound` below are exactly
those two statements, at the level of the `J`-bound; `jutilaJBound_of_nearLine_and_far` glues
them. -/

/-- The near-line half of `JutilaJBound`: the `J`-bound on `1-ε ≤ σ < 1`, i.e. where the
pseudocharacter/Halász argument (§3 of Jutila's paper) applies. -/
def JutilaJBoundNear : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ q : ℕ, 2 ≤ q → ∀ [NeZero q] (σ T : ℝ), 1 - ε ≤ σ → σ < 1 → 1 ≤ T →
      ∃ Δ : ℝ, 0 < Δ ∧ Δ ≤ 1 - σ ∧
        (∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
            ((max ((zeroBoxes χ σ T Δ).filter (fun k => _root_.Even k)).card
                  ((zeroBoxes χ σ T Δ).filter (fun k => ¬ _root_.Even k)).card : ℕ) : ℝ))
          ≤ C * ((q : ℝ) * T) ^ ((2 + ε) * (1 - σ))
              / ((1 - σ) * Real.log ((q : ℝ) * (T + 1)) + 1)

/-- The far half of `JutilaJBound`: the `J`-bound on `4/5 ≤ σ ≤ 1-ε`, i.e. where the large-values
argument of Huxley–Jutila IV (Jutila's `[6]`) applies. -/
def JutilaJBoundFar : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ q : ℕ, 2 ≤ q → ∀ [NeZero q] (σ T : ℝ), (4 : ℝ) / 5 ≤ σ → σ ≤ 1 - ε → 1 ≤ T →
      ∃ Δ : ℝ, 0 < Δ ∧ Δ ≤ 1 - σ ∧
        (∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
            ((max ((zeroBoxes χ σ T Δ).filter (fun k => _root_.Even k)).card
                  ((zeroBoxes χ σ T Δ).filter (fun k => ¬ _root_.Even k)).card : ℕ) : ℝ))
          ≤ C * ((q : ℝ) * T) ^ ((2 + ε) * (1 - σ))
              / ((1 - σ) * Real.log ((q : ℝ) * (T + 1)) + 1)

/-- **The two halves of Jutila's §3 give the whole `J`-bound.** -/
theorem jutilaJBound_of_nearLine_and_far (hN : JutilaJBoundNear) (hF : JutilaJBoundFar) :
    JutilaJBound := by
  intro ε hε
  obtain ⟨C₁, hC₁, h₁⟩ := hN ε hε
  obtain ⟨C₂, hC₂, h₂⟩ := hF ε hε
  refine ⟨max C₁ C₂, lt_max_of_lt_left hC₁, ?_⟩
  intro q hq _inst σ T h45 hσ1 hT
  have hX : (0 : ℝ) ≤ ((q : ℝ) * T) ^ ((2 + ε) * (1 - σ))
      / ((1 - σ) * Real.log ((q : ℝ) * (T + 1)) + 1) := by
    have h1 : (0 : ℝ) ≤ 1 - σ := by linarith
    have h2 : (0 : ℝ) < (q : ℝ) * T := by
      have h3 : (1 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 1 < q)
      nlinarith
    have h3 : (1 : ℝ) < (q : ℝ) * (T + 1) := by
      have h4 : (1 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 1 < q)
      nlinarith
    have h4 : (0 : ℝ) < Real.log ((q : ℝ) * (T + 1)) := Real.log_pos h3
    refine div_nonneg (Real.rpow_nonneg h2.le _) ?_
    nlinarith [mul_nonneg h1 h4.le]
  rcases le_total σ (1 - ε) with h | h
  · obtain ⟨Δ, hΔp, hΔl, hb⟩ := h₂ q hq σ T h45 h hT
    have hle : C₂ * (((q : ℝ) * T) ^ ((2 + ε) * (1 - σ)))
          / ((1 - σ) * Real.log ((q : ℝ) * (T + 1)) + 1)
        ≤ max C₁ C₂ * (((q : ℝ) * T) ^ ((2 + ε) * (1 - σ)))
          / ((1 - σ) * Real.log ((q : ℝ) * (T + 1)) + 1) := by
      rw [← mul_div_assoc', ← mul_div_assoc']
      exact mul_le_mul_of_nonneg_right (le_max_right C₁ C₂) hX
    exact ⟨Δ, hΔp, hΔl, le_trans hb hle⟩
  · obtain ⟨Δ, hΔp, hΔl, hb⟩ := h₁ q hq σ T h hσ1 hT
    have hle : C₁ * (((q : ℝ) * T) ^ ((2 + ε) * (1 - σ)))
          / ((1 - σ) * Real.log ((q : ℝ) * (T + 1)) + 1)
        ≤ max C₁ C₂ * (((q : ℝ) * T) ^ ((2 + ε) * (1 - σ)))
          / ((1 - σ) * Real.log ((q : ℝ) * (T + 1)) + 1) := by
      rw [← mul_div_assoc', ← mul_div_assoc']
      exact mul_le_mul_of_nonneg_right (le_max_left C₁ C₂) hX
    exact ⟨Δ, hΔp, hΔl, le_trans hb hle⟩

/-- The node from the near-line and far halves of the `J`-bound. -/
theorem jutilaNonPrincipal_of_nearLineJBound_and_farJBound
    (hN : JutilaJBoundNear) (hF : JutilaJBoundFar) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ q : ℕ, 2 ≤ q → ∀ [NeZero q] (σ T : ℝ), (4 : ℝ) / 5 ≤ σ → σ ≤ 1 → 1 ≤ T →
        (∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
            Work.LinnikAreas.zeroCountIn χ σ T)
          ≤ C * ((q : ℝ) * T) ^ ((2 + ε) * (1 - σ)) :=
  jutilaNonPrincipal_of_jBound (jutilaJBound_of_nearLine_and_far hN hF)


end Work.ZeroDensity.Jutila
