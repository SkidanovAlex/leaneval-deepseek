import ChallengeDeps
import Mathlib.Tactic.Have
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Submission.KernelRel
import Submission.KernelSym
import Submission.Q0Ren
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Layer 5 — the corpus-native potential splitting (`lem:potsplit`, `eq:potsplit`)

FS decompose the potential part of the analysis-box Hamiltonian

    −μ·Σᵢ∫w₁(xᵢ,y)dy + ½·Σ_{i≠j} w(xᵢ,xⱼ)          (qLHSword)

into the five corpus expectation words `q0word`..`q4word` (FS
`eq:DefQ0`..`eq:DefQ4`), for every continuous state `Φ` over the centred box
`abox N ℓ`, using the per-slot condensate/excited projections
`Pᵢ := aP ℓ i`, `Qᵢ := aQ ℓ i`.  The words are the quadratic-form
transcriptions `⟨Φ, 𝒬ₖᵣₑₙ Φ⟩` (real states, kernels evaluated at `(xᵢ,xⱼ)`):

* `q0word` — the all-condensate term `½Σ PᵢPⱼw₂PⱼPᵢ − μΣ Pᵢ(∫w₁)Pᵢ` (already
  evaluated in `Q0Ren.q0_chosen_*`);
* `q1word` — `Σ_{i≠j} PⱼQᵢw₂PᵢPⱼ − μΣ Qᵢ(∫w₁)Pᵢ` + h.c. (one `Q` on one side);
* `q2word` — the two-`Q` terms
  `Σ PᵢQⱼw₂PⱼQᵢ + Σ PᵢQⱼw₂QⱼPᵢ − μΣ Qᵢ(∫w₁)Qᵢ + ½Σ(PᵢPⱼw₁QⱼQᵢ+h.c.)`;
* `q3word` — `Σ_{i≠j} PᵢQⱼw₁QⱼQᵢ + h.c.`;
* `q4word` — the positive square
  `½Σ [QⱼQᵢ + ω(xᵢ−xⱼ)(PⱼPᵢ+PⱼQᵢ+QⱼPᵢ)]·w·[QⱼQᵢ + ω(xᵢ−xⱼ)(PⱼPᵢ+PⱼQᵢ+QⱼPᵢ)]`,
  which is `≥ 0` whenever `w ≥ 0` pointwise (`q4_nonneg`).

The identities are stated for **abstract kernels** `w w1 w2 ω` with the
pointwise relations `w1 = w·(1−ω)`, `w2 = w·(1−ω²)` (`hw1rel`, `hw2rel`), so
that the algebra is self-contained; the chosen-branch instantiation
(`w := wPair(v)`, `w1 := wPair(g₀)`, `w2 := wPair(g₂)`, `ω(x,y) := w₀(x−y)`)
is provided at the bottom, where the relations follow from `KernelRel`.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators

namespace Submission

open _root_.BoseGases
set_option autoImplicit false

namespace BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

abbrev XN (N : ℕ) := Fin N → ℝ³

/-- The one-body fibre function of `w1`: `x ↦ ∫_y w1(x,y)dy` over the box. -/
noncomputable def w1Fibre (ℓ : ℝ) (w1 : ℝ³ → ℝ³ → ℝ) (x : ℝ³) : ℝ :=
  ∫ y in acube ℓ, w1 x y

/-- Q0-word (expectation) — FS `eq:DefQ0`:
`⟨Φ, [½Σ_{i≠j} PᵢPⱼ·w2(xᵢ,xⱼ)·PⱼPᵢ − μΣᵢ Pᵢ·(∫w1(xᵢ,·))·Pᵢ] Φ⟩`. -/
noncomputable def q0word {N : ℕ} (ℓ : ℝ) (μ : ℝ) (w1 w2 : ℝ³ → ℝ³ → ℝ)
    (Φ : XN N → ℝ) : ℝ :=
  (1 / 2) * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        (aP ℓ p.1 (aP ℓ p.2 Φ) x) ^ 2 * w2 (x p.1) (x p.2))
    - μ * (∑ i : Fin N, ∫ x in abox N ℓ,
        (aP ℓ i Φ x) ^ 2 * (w1Fibre ℓ w1 (x i)))

/-- Q1-word — FS `eq:DefQ1` (the displayed operator plus its Hermitian
conjugate, which doubles the quadratic form). -/
noncomputable def q1word {N : ℕ} (ℓ : ℝ) (μ : ℝ) (w1 w2 : ℝ³ → ℝ³ → ℝ)
    (Φ : XN N → ℝ) : ℝ :=
  2 * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aP ℓ p.1 (aP ℓ p.2 Φ) x) * w2 (x p.1) (x p.2))
    - 2 * μ * (∑ i : Fin N, ∫ x in abox N ℓ,
        (aQ ℓ i Φ x) * (aP ℓ i Φ x) * (w1Fibre ℓ w1 (x i)))

/-- Q2-word — FS `eq:DefQ2` (all displayed terms; the `½(PᵢPⱼw₁QⱼQᵢ+h.c.)`
term doubles to the plain integral). -/
noncomputable def q2word {N : ℕ} (ℓ : ℝ) (μ : ℝ) (w1 w2 : ℝ³ → ℝ³ → ℝ)
    (Φ : XN N → ℝ) : ℝ :=
  (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aP ℓ p.2 (aQ ℓ p.1 Φ) x) * w2 (x p.1) (x p.2))
  + (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aQ ℓ p.2 (aP ℓ p.1 Φ) x) * w2 (x p.1) (x p.2))
  - μ * (∑ i : Fin N, ∫ x in abox N ℓ,
        (aQ ℓ i Φ x) ^ 2 * (w1Fibre ℓ w1 (x i)))
  + (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        (aP ℓ p.1 (aP ℓ p.2 Φ) x) * (aQ ℓ p.2 (aQ ℓ p.1 Φ) x) * w1 (x p.1) (x p.2))

/-- Q3-word — FS `eq:DefQ3` (plus Hermitian conjugate, doubled). -/
noncomputable def q3word {N : ℕ} (ℓ : ℝ) (w1 : ℝ³ → ℝ³ → ℝ) (Φ : XN N → ℝ) : ℝ :=
  2 * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
        (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aQ ℓ p.2 (aQ ℓ p.1 Φ) x) * w1 (x p.1) (x p.2))

/-- The second bracket of FS `eq:DefQ4` applied to `Φ` (the operator acting on
`Φ` in the quadratic form `⟨Φ, 𝒬₄ Φ⟩ = ½Σ∫(BΦ)²·w`). -/
noncomputable def q4B {N : ℕ} (ℓ : ℝ) (om : ℝ³ → ℝ³ → ℝ) (Φ : XN N → ℝ)
    (p : Fin N × Fin N) (x : XN N) : ℝ :=
  aQ ℓ p.2 (aQ ℓ p.1 Φ) x
    + om (x p.1) (x p.2) * ((aP ℓ p.2 (aP ℓ p.1 Φ) x)
        + (aP ℓ p.2 (aQ ℓ p.1 Φ) x) + (aQ ℓ p.2 (aP ℓ p.1 Φ) x))

/-- Q4-word — FS `eq:DefQ4` as a manifest square. -/
noncomputable def q4word {N : ℕ} (ℓ : ℝ) (w om : ℝ³ → ℝ³ → ℝ) (Φ : XN N → ℝ) : ℝ :=
  (1 / 2) * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
      (q4B ℓ om Φ p x) ^ 2 * w (x p.1) (x p.2))

/-- The potential part of the analysis-box Hamiltonian (`eq:potsplit` LHS), as
an expectation over the box. -/
noncomputable def qLHSword {N : ℕ} (ℓ : ℝ) (μ : ℝ) (w w1 : ℝ³ → ℝ³ → ℝ)
    (Φ : XN N → ℝ) : ℝ :=
  ∫ x in abox N ℓ, (Φ x) ^ 2 *
    (- μ * (∑ i : Fin N, w1Fibre ℓ w1 (x i))
      + (1 / 2) * (∑ p ∈ pairSet N, w (x p.1) (x p.2)))

/-! ## Projection algebra over the centred box, pointwise (used by `potsplit_expect`)

Pure algebra: `Qᵢ = 1 − Pᵢ` pointwise, projections on different slots commute,
idempotence.  All statements are pointwise in `x : XN N` for continuous `Φ`.
-/

/-- `Pᵢ` is additive pointwise (for continuous arguments). -/
lemma aP_add {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i : Fin N) {Φ Ψ : XN N → ℝ}
    (hΦc : Continuous Φ) (hΨc : Continuous Ψ) (x : XN N) :
    aP ℓ i (Φ + Ψ) x = aP ℓ i Φ x + aP ℓ i Ψ x := by
  unfold aP
  have hiΦ : IntegrableOn (fun y : ℝ³ => Φ (Function.update x i y)) (acube ℓ) volume :=
    integrableOn_acube_of_continuous hℓ (hΦc.comp (by fun_prop : Continuous (fun y : ℝ³ => Function.update x i y)))
  have hiΨ : IntegrableOn (fun y : ℝ³ => Ψ (Function.update x i y)) (acube ℓ) volume :=
    integrableOn_acube_of_continuous hℓ (hΨc.comp (by fun_prop : Continuous (fun y : ℝ³ => Function.update x i y)))
  have hsplit : (∫ y in acube ℓ, Φ (Function.update x i y) + Ψ (Function.update x i y)) =
      (∫ y in acube ℓ, Φ (Function.update x i y)) + (∫ y in acube ℓ, Ψ (Function.update x i y)) :=
    integral_add hiΦ hiΨ
  calc
    (1 / ℓ ^ 3) * (∫ y in acube ℓ, (Φ + Ψ) (Function.update x i y))
        = (1 / ℓ ^ 3) * ((∫ y in acube ℓ, Φ (Function.update x i y)) + (∫ y in acube ℓ, Ψ (Function.update x i y))) := by
          change (1 / ℓ ^ 3) * (∫ y in acube ℓ, Φ (Function.update x i y) + Ψ (Function.update x i y))
            = (1 / ℓ ^ 3) * ((∫ y in acube ℓ, Φ (Function.update x i y)) + (∫ y in acube ℓ, Ψ (Function.update x i y)))
          rw [hsplit]
    _ = (1 / ℓ ^ 3) * (∫ y in acube ℓ, Φ (Function.update x i y)) + (1 / ℓ ^ 3) * (∫ y in acube ℓ, Ψ (Function.update x i y)) := by
          ring

/-- `Pᵢ` is subtractive pointwise (for continuous arguments). -/
lemma aP_sub {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i : Fin N) {Φ Ψ : XN N → ℝ}
    (hΦc : Continuous Φ) (hΨc : Continuous Ψ) (x : XN N) :
    aP ℓ i (Φ - Ψ) x = aP ℓ i Φ x - aP ℓ i Ψ x := by
  unfold aP
  have hiΦ : IntegrableOn (fun y : ℝ³ => Φ (Function.update x i y)) (acube ℓ) volume :=
    integrableOn_acube_of_continuous hℓ (hΦc.comp (by fun_prop : Continuous (fun y : ℝ³ => Function.update x i y)))
  have hiΨ : IntegrableOn (fun y : ℝ³ => Ψ (Function.update x i y)) (acube ℓ) volume :=
    integrableOn_acube_of_continuous hℓ (hΨc.comp (by fun_prop : Continuous (fun y : ℝ³ => Function.update x i y)))
  have hsplit : (∫ y in acube ℓ, Φ (Function.update x i y) - Ψ (Function.update x i y)) =
      (∫ y in acube ℓ, Φ (Function.update x i y)) - (∫ y in acube ℓ, Ψ (Function.update x i y)) :=
    integral_sub hiΦ hiΨ
  calc
    (1 / ℓ ^ 3) * (∫ y in acube ℓ, (Φ - Ψ) (Function.update x i y))
        = (1 / ℓ ^ 3) * ((∫ y in acube ℓ, Φ (Function.update x i y)) - (∫ y in acube ℓ, Ψ (Function.update x i y))) := by
          change (1 / ℓ ^ 3) * (∫ y in acube ℓ, Φ (Function.update x i y) - Ψ (Function.update x i y))
            = (1 / ℓ ^ 3) * ((∫ y in acube ℓ, Φ (Function.update x i y)) - (∫ y in acube ℓ, Ψ (Function.update x i y)))
          rw [hsplit]
    _ = (1 / ℓ ^ 3) * (∫ y in acube ℓ, Φ (Function.update x i y)) - (1 / ℓ ^ 3) * (∫ y in acube ℓ, Ψ (Function.update x i y)) := by
          ring

/-- `Qⱼ` of a continuous function is continuous. -/
lemma aQ_continuous {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i : Fin N) {Φ : XN N → ℝ}
    (hΦc : Continuous Φ) : Continuous (aQ ℓ i Φ) := by
  change Continuous (Φ - aP ℓ i Φ)
  exact hΦc.sub (aP_continuous hℓ i hΦc)

/-- `Pᵢ` commutes with `Qⱼ` across distinct slots (pointwise). -/
lemma aP_aQ_comm {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {i j : Fin N} (hij : i ≠ j)
    {Φ : XN N → ℝ} (hΦc : Continuous Φ) (x : XN N) :
    aP ℓ i (aQ ℓ j Φ) x = aQ ℓ j (aP ℓ i Φ) x := by
  have hcj : Continuous (aP ℓ j Φ) := aP_continuous hℓ j hΦc
  calc
    aP ℓ i (aQ ℓ j Φ) x = aP ℓ i (Φ - aP ℓ j Φ) x := by rfl
    _ = aP ℓ i Φ x - aP ℓ i (aP ℓ j Φ) x := aP_sub hℓ i hΦc hcj x
    _ = aP ℓ i Φ x - aP ℓ j (aP ℓ i Φ) x := by rw [aP_comm hℓ i j hΦc x]
    _ = aQ ℓ j (aP ℓ i Φ) x := by rfl

/-- `Qᵢ` commutes with `Qⱼ` across distinct slots (pointwise). -/
lemma aQ_comm {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {i j : Fin N} (hij : i ≠ j)
    {Φ : XN N → ℝ} (hΦc : Continuous Φ) (x : XN N) :
    aQ ℓ i (aQ ℓ j Φ) x = aQ ℓ j (aQ ℓ i Φ) x := by
  have hA : aP ℓ i (aQ ℓ j Φ) x = aP ℓ i Φ x - aP ℓ i (aP ℓ j Φ) x := by
    calc
      aP ℓ i (aQ ℓ j Φ) x = aQ ℓ j (aP ℓ i Φ) x := aP_aQ_comm hℓ hij hΦc x
      _ = aP ℓ i Φ x - aP ℓ j (aP ℓ i Φ) x := by rfl
      _ = aP ℓ i Φ x - aP ℓ i (aP ℓ j Φ) x := by rw [aP_comm hℓ i j hΦc x]
  have hB : aP ℓ j (aQ ℓ i Φ) x = aP ℓ j Φ x - aP ℓ i (aP ℓ j Φ) x := by
    calc
      aP ℓ j (aQ ℓ i Φ) x = aQ ℓ i (aP ℓ j Φ) x := aP_aQ_comm hℓ hij.symm hΦc x
      _ = aP ℓ j Φ x - aP ℓ i (aP ℓ j Φ) x := by rfl
  have hL : aQ ℓ i (aQ ℓ j Φ) x = Φ x - aP ℓ j Φ x - aP ℓ i Φ x + aP ℓ i (aP ℓ j Φ) x := by
    calc
      aQ ℓ i (aQ ℓ j Φ) x = aQ ℓ j Φ x - aP ℓ i (aQ ℓ j Φ) x := by rfl
      _ = aQ ℓ j Φ x - (aP ℓ i Φ x - aP ℓ i (aP ℓ j Φ) x) := by rw [hA]
      _ = (Φ x - aP ℓ j Φ x) - (aP ℓ i Φ x - aP ℓ i (aP ℓ j Φ) x) := by rfl
      _ = Φ x - aP ℓ j Φ x - aP ℓ i Φ x + aP ℓ i (aP ℓ j Φ) x := by ring
  have hR : aQ ℓ j (aQ ℓ i Φ) x = Φ x - aP ℓ i Φ x - aP ℓ j Φ x + aP ℓ i (aP ℓ j Φ) x := by
    calc
      aQ ℓ j (aQ ℓ i Φ) x = aQ ℓ i Φ x - aP ℓ j (aQ ℓ i Φ) x := by rfl
      _ = aQ ℓ i Φ x - (aP ℓ j Φ x - aP ℓ i (aP ℓ j Φ) x) := by rw [hB]
      _ = (Φ x - aP ℓ i Φ x) - (aP ℓ j Φ x - aP ℓ i (aP ℓ j Φ) x) := by rfl
      _ = Φ x - aP ℓ i Φ x - aP ℓ j Φ x + aP ℓ i (aP ℓ j Φ) x := by ring
  rw [hL, hR]
  ring

/-- Completeness of the four `{P,Q}`-patterns on the two slots `i,j` (pointwise):
`(PᵢPⱼ+PᵢQⱼ+QᵢPⱼ+QᵢQⱼ)Φ = Φ`. -/
lemma pattern_sum {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {i j : Fin N} (hij : i ≠ j)
    {Φ : XN N → ℝ} (hΦc : Continuous Φ) (x : XN N) :
    aP ℓ i (aP ℓ j Φ) x + aP ℓ i (aQ ℓ j Φ) x + aQ ℓ i (aP ℓ j Φ) x + aQ ℓ i (aQ ℓ j Φ) x = Φ x := by
  have h1 : aP ℓ i (aP ℓ j Φ) x + aQ ℓ i (aP ℓ j Φ) x = aP ℓ j Φ x := by
    change aP ℓ i (aP ℓ j Φ) x + (aP ℓ j Φ x - aP ℓ i (aP ℓ j Φ) x) = aP ℓ j Φ x
    ring
  have h2 : aP ℓ i (aQ ℓ j Φ) x + aQ ℓ i (aQ ℓ j Φ) x = aQ ℓ j Φ x := by
    change aP ℓ i (aQ ℓ j Φ) x + (aQ ℓ j Φ x - aP ℓ i (aQ ℓ j Φ) x) = aQ ℓ j Φ x
    ring
  calc
    aP ℓ i (aP ℓ j Φ) x + aP ℓ i (aQ ℓ j Φ) x + aQ ℓ i (aP ℓ j Φ) x + aQ ℓ i (aQ ℓ j Φ) x
        = (aP ℓ i (aP ℓ j Φ) x + aQ ℓ i (aP ℓ j Φ) x) + (aP ℓ i (aQ ℓ j Φ) x + aQ ℓ i (aQ ℓ j Φ) x) := by
          ring
    _ = aP ℓ j Φ x + aQ ℓ j Φ x := by rw [h1, h2]
    _ = Φ x := by
          change aP ℓ j Φ x + (Φ x - aP ℓ j Φ x) = Φ x
          ring

/-! ## Kernel symmetry and continuity derived from the pointwise relations -/

/-- `w1 = w(1−ω)` is symmetric. -/
lemma w1_sym {w w1 om : ℝ³ → ℝ³ → ℝ}
    (hwsym : ∀ x y : ℝ³, w x y = w y x) (homsym : ∀ x y : ℝ³, om x y = om y x)
    (hw1rel : ∀ x y : ℝ³, w1 x y = w x y * (1 - om x y)) (x y : ℝ³) :
    w1 x y = w1 y x := by
  rw [hw1rel x y, hw1rel y x, hwsym, homsym]

/-- `w2 = w(1−ω²)` is symmetric. -/
lemma w2_sym {w w2 om : ℝ³ → ℝ³ → ℝ}
    (hwsym : ∀ x y : ℝ³, w x y = w y x) (homsym : ∀ x y : ℝ³, om x y = om y x)
    (hw2rel : ∀ x y : ℝ³, w2 x y = w x y * (1 - om x y ^ 2)) (x y : ℝ³) :
    w2 x y = w2 y x := by
  rw [hw2rel x y, hw2rel y x, hwsym, homsym]

/-- `w1` is continuous as a function on `ℝ³ × ℝ³`. -/
lemma w1_continuous {w w1 om : ℝ³ → ℝ³ → ℝ}
    (hwc : Continuous (fun p : ℝ³ × ℝ³ => w p.1 p.2))
    (homc : Continuous (fun p : ℝ³ × ℝ³ => om p.1 p.2))
    (hw1rel : ∀ x y : ℝ³, w1 x y = w x y * (1 - om x y)) :
    Continuous (fun p : ℝ³ × ℝ³ => w1 p.1 p.2) := by
  have h : (fun p : ℝ³ × ℝ³ => w1 p.1 p.2) = fun p : ℝ³ × ℝ³ => w p.1 p.2 * (1 - om p.1 p.2) := by
    funext p
    exact hw1rel p.1 p.2
  rw [h]
  fun_prop

/-- `w2` is continuous as a function on `ℝ³ × ℝ³`. -/
lemma w2_continuous {w w2 om : ℝ³ → ℝ³ → ℝ}
    (hwc : Continuous (fun p : ℝ³ × ℝ³ => w p.1 p.2))
    (homc : Continuous (fun p : ℝ³ × ℝ³ => om p.1 p.2))
    (hw2rel : ∀ x y : ℝ³, w2 x y = w x y * (1 - om x y ^ 2)) :
    Continuous (fun p : ℝ³ × ℝ³ => w2 p.1 p.2) := by
  have h : (fun p : ℝ³ × ℝ³ => w2 p.1 p.2) = fun p : ℝ³ × ℝ³ => w p.1 p.2 * (1 - om p.1 p.2 ^ 2) := by
    funext p
    exact hw2rel p.1 p.2
  rw [h]
  fun_prop


/-! ## The `w1`-fibre mean is continuous -/

/-- The fibre mean `x ↦ ∫_y w1(x,y)` is continuous (for continuous `w1`, `0 < ℓ`). -/
lemma w1Fibre_continuous {ℓ : ℝ} (hℓ : 0 < ℓ) {w1 : ℝ³ → ℝ³ → ℝ}
    (hw1c : Continuous (fun p : ℝ³ × ℝ³ => w1 p.1 p.2)) :
    Continuous (fun x : ℝ³ => w1Fibre ℓ w1 x) := by
  unfold w1Fibre
  refine continuous_parametric_integral_of_continuous
      (f := fun (x : ℝ³) (y : ℝ³) => w1 x y) ?_ ?_
  · simpa [Function.uncurry_def] using hw1c
  · exact acube_compact hℓ

/-! ## The one-slot `μ` terms -/

/-- μ-weight integrand value for slot `i`: `(aP i Φ x)^2 · (∫_y w1(xᵢ,y))`. -/
noncomputable def muP {N : ℕ} (ℓ : ℝ) (w1 : ℝ³ → ℝ³ → ℝ) (Φ : XN N → ℝ) (i : Fin N) : ℝ :=
  (∫ x in abox N ℓ, (aP ℓ i Φ x) ^ 2 * w1Fibre ℓ w1 (x i))

/-- μ-weight integrand value: `(aQ i Φ x)·(aP i Φ x)·(∫_y w1(xᵢ,y))`. -/
noncomputable def muQP {N : ℕ} (ℓ : ℝ) (w1 : ℝ³ → ℝ³ → ℝ) (Φ : XN N → ℝ) (i : Fin N) : ℝ :=
  (∫ x in abox N ℓ, (aQ ℓ i Φ x) * (aP ℓ i Φ x) * w1Fibre ℓ w1 (x i))

/-- μ-weight integrand value: `(aQ i Φ x)^2 · (∫_y w1(xᵢ,y))`. -/
noncomputable def muQ {N : ℕ} (ℓ : ℝ) (w1 : ℝ³ → ℝ³ → ℝ) (Φ : XN N → ℝ) (i : Fin N) : ℝ :=
  (∫ x in abox N ℓ, (aQ ℓ i Φ x) ^ 2 * w1Fibre ℓ w1 (x i))

/-- The LHS μ-weight: `Φ(x)^2 · (∫_y w1(xᵢ,y))`. -/
noncomputable def muPhi {N : ℕ} (ℓ : ℝ) (w1 : ℝ³ → ℝ³ → ℝ) (Φ : XN N → ℝ) (i : Fin N) : ℝ :=
  (∫ x in abox N ℓ, (Φ x) ^ 2 * w1Fibre ℓ w1 (x i))
/-- Per-slot μ identity (un-doubled form): `muP + muQP + muQP + muQ = muPhi`. -/
lemma potsplit_mu_agree {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {i : Fin N}
    {w1 : ℝ³ → ℝ³ → ℝ} (hw1c : Continuous (fun p : ℝ³ × ℝ³ => w1 p.1 p.2))
    {Φ : XN N → ℝ} (hΦc : Continuous Φ) :
    muP ℓ w1 Φ i + muQP ℓ w1 Φ i + muQP ℓ w1 Φ i + muQ ℓ w1 Φ i = muPhi ℓ w1 Φ i := by
  let f : XN N → ℝ := fun x => w1Fibre ℓ w1 (x i)
  have hfc : Continuous f := by
    unfold f
    exact (w1Fibre_continuous hℓ hw1c).comp (by fun_prop : Continuous (fun x : XN N => x i))
  have hPc : Continuous (aP ℓ i Φ) := aP_continuous hℓ i hΦc
  have hQc : Continuous (aQ ℓ i Φ) := by
    change Continuous (Φ - aP ℓ i Φ)
    exact hΦc.sub hPc
  have g0c : Continuous (fun x : XN N => (aP ℓ i Φ x) ^ 2 * f x) := by fun_prop
  have g1c : Continuous (fun x : XN N => (aQ ℓ i Φ x) * (aP ℓ i Φ x) * f x) := by fun_prop
  have g2c : Continuous (fun x : XN N => (aQ ℓ i Φ x) ^ 2 * f x) := by fun_prop
  have s1c : Continuous (fun x : XN N => (aP ℓ i Φ x) ^ 2 * f x + (aQ ℓ i Φ x) * (aP ℓ i Φ x) * f x) := by fun_prop
  have s2c : Continuous (fun x : XN N => (aP ℓ i Φ x) ^ 2 * f x + (aQ ℓ i Φ x) * (aP ℓ i Φ x) * f x
      + (aQ ℓ i Φ x) * (aP ℓ i Φ x) * f x) := by fun_prop
  have i0 : IntegrableOn (fun x : XN N => (aP ℓ i Φ x) ^ 2 * f x) (abox N ℓ) volume := integrableOn_abox_of_continuous hℓ g0c
  have i1 : IntegrableOn (fun x : XN N => (aQ ℓ i Φ x) * (aP ℓ i Φ x) * f x) (abox N ℓ) volume := integrableOn_abox_of_continuous hℓ g1c
  have i2 : IntegrableOn (fun x : XN N => (aQ ℓ i Φ x) ^ 2 * f x) (abox N ℓ) volume := integrableOn_abox_of_continuous hℓ g2c
  have is1 : IntegrableOn (fun x : XN N => (aP ℓ i Φ x) ^ 2 * f x + (aQ ℓ i Φ x) * (aP ℓ i Φ x) * f x) (abox N ℓ) volume := integrableOn_abox_of_continuous hℓ s1c
  have is2 : IntegrableOn (fun x : XN N => (aP ℓ i Φ x) ^ 2 * f x + (aQ ℓ i Φ x) * (aP ℓ i Φ x) * f x
      + (aQ ℓ i Φ x) * (aP ℓ i Φ x) * f x) (abox N ℓ) volume := integrableOn_abox_of_continuous hℓ s2c
  have hpoint : (fun x : XN N => (aP ℓ i Φ x) ^ 2 * f x + (aQ ℓ i Φ x) * (aP ℓ i Φ x) * f x
      + (aQ ℓ i Φ x) * (aP ℓ i Φ x) * f x + (aQ ℓ i Φ x) ^ 2 * f x)
      = fun x : XN N => (Φ x) ^ 2 * f x := by
    funext x
    have hlin : aP ℓ i Φ x + aQ ℓ i Φ x = Φ x := by
      unfold aQ
      ring
    have hb : (aP ℓ i Φ x) ^ 2 + 2 * (aQ ℓ i Φ x) * (aP ℓ i Φ x) + (aQ ℓ i Φ x) ^ 2 = (Φ x) ^ 2 := by
      rw [← hlin]
      ring
    calc
      (aP ℓ i Φ x) ^ 2 * f x + (aQ ℓ i Φ x) * (aP ℓ i Φ x) * f x
          + (aQ ℓ i Φ x) * (aP ℓ i Φ x) * f x + (aQ ℓ i Φ x) ^ 2 * f x
          = ((aP ℓ i Φ x) ^ 2 + 2 * (aQ ℓ i Φ x) * (aP ℓ i Φ x) + (aQ ℓ i Φ x) ^ 2) * f x := by
            ring
      _ = (Φ x) ^ 2 * f x := by rw [hb]
  calc
    muP ℓ w1 Φ i + muQP ℓ w1 Φ i + muQP ℓ w1 Φ i + muQ ℓ w1 Φ i
        = (∫ x in abox N ℓ, (aP ℓ i Φ x) ^ 2 * f x) + (∫ x in abox N ℓ, (aQ ℓ i Φ x) * (aP ℓ i Φ x) * f x)
            + (∫ x in abox N ℓ, (aQ ℓ i Φ x) * (aP ℓ i Φ x) * f x)
            + (∫ x in abox N ℓ, (aQ ℓ i Φ x) ^ 2 * f x) := by
          unfold muP muQP muQ
          rfl
    _ = (∫ x in abox N ℓ, (aP ℓ i Φ x) ^ 2 * f x + (aQ ℓ i Φ x) * (aP ℓ i Φ x) * f x
        + (aQ ℓ i Φ x) * (aP ℓ i Φ x) * f x + (aQ ℓ i Φ x) ^ 2 * f x) := by
          rw [← integral_add i0 i1]
          rw [← integral_add is1 i1]
          rw [← integral_add is2 i2]
    _ = muPhi ℓ w1 Φ i := by
          unfold muPhi
          rw [← hpoint]
/-! ## Fragment value functions (per pair, per word)

For an ordered pair `(i,j)` these are the pointwise integrands of the
`pairSet`-summands of the five words (`fg0`..`fg4` matching `q0word`..`q4word`).
-/
/-- Q0 pair-summand integrand. -/
noncomputable def fg0 {N : ℕ} (ℓ : ℝ) (w2 : ℝ³ → ℝ³ → ℝ) (Φ : XN N → ℝ)
    (i j : Fin N) (x : XN N) : ℝ :=
  (1 / 2) * (aP ℓ i (aP ℓ j Φ) x) ^ 2 * w2 (x i) (x j)
/-- Q1 pair-summand integrand (the doubled h.c. term). -/
noncomputable def fg1 {N : ℕ} (ℓ : ℝ) (w2 : ℝ³ → ℝ³ → ℝ) (Φ : XN N → ℝ)
    (i j : Fin N) (x : XN N) : ℝ :=
  2 * (aP ℓ i (aQ ℓ j Φ) x) * (aP ℓ i (aP ℓ j Φ) x) * w2 (x i) (x j)
/-- Q2 first pair-summand integrand. -/
noncomputable def fg2a {N : ℕ} (ℓ : ℝ) (w2 : ℝ³ → ℝ³ → ℝ) (Φ : XN N → ℝ)
    (i j : Fin N) (x : XN N) : ℝ :=
  (aP ℓ i (aQ ℓ j Φ) x) * (aP ℓ j (aQ ℓ i Φ) x) * w2 (x i) (x j)
/-- Q2 second pair-summand integrand. -/
noncomputable def fg2b {N : ℕ} (ℓ : ℝ) (w2 : ℝ³ → ℝ³ → ℝ) (Φ : XN N → ℝ)
    (i j : Fin N) (x : XN N) : ℝ :=
  (aP ℓ i (aQ ℓ j Φ) x) * (aQ ℓ j (aP ℓ i Φ) x) * w2 (x i) (x j)
/-- Q2 third pair-summand integrand. -/
noncomputable def fg2c {N : ℕ} (ℓ : ℝ) (w1 : ℝ³ → ℝ³ → ℝ) (Φ : XN N → ℝ)
    (i j : Fin N) (x : XN N) : ℝ :=
  (aP ℓ i (aP ℓ j Φ) x) * (aQ ℓ j (aQ ℓ i Φ) x) * w1 (x i) (x j)
/-- Q3 pair-summand integrand. -/
noncomputable def fg3 {N : ℕ} (ℓ : ℝ) (w1 : ℝ³ → ℝ³ → ℝ) (Φ : XN N → ℝ)
    (i j : Fin N) (x : XN N) : ℝ :=
  2 * (aP ℓ i (aQ ℓ j Φ) x) * (aQ ℓ j (aQ ℓ i Φ) x) * w1 (x i) (x j)
/-- Q4 pair-summand integrand. -/
noncomputable def fg4 {N : ℕ} (ℓ : ℝ) (w om : ℝ³ → ℝ³ → ℝ) (Φ : XN N → ℝ)
    (i j : Fin N) (x : XN N) : ℝ :=
  (1 / 2) * (q4B ℓ om Φ (i, j) x) ^ 2 * w (x i) (x j)
/-- The combined pointwise value of the five words' pair summands at the two
orientations `(i,j)` and `(j,i)`. -/
noncomputable def fgsum {N : ℕ} (ℓ : ℝ) (w w1 w2 om : ℝ³ → ℝ³ → ℝ)
    (Φ : XN N → ℝ) (i j : Fin N) (x : XN N) : ℝ :=
  fg0 ℓ w2 Φ i j x + fg1 ℓ w2 Φ i j x + fg2a ℓ w2 Φ i j x + fg2b ℓ w2 Φ i j x
    + fg2c ℓ w1 Φ i j x + fg3 ℓ w1 Φ i j x + fg4 ℓ w om Φ i j x
    + fg0 ℓ w2 Φ j i x + fg1 ℓ w2 Φ j i x + fg2a ℓ w2 Φ j i x + fg2b ℓ w2 Φ j i x
    + fg2c ℓ w1 Φ j i x + fg3 ℓ w1 Φ j i x + fg4 ℓ w om Φ j i x

/-- The seven word-fragment integrals at one orientation `(i,j)` (the
`pairSet`-summands of `q0word`..`q4word` restricted to the pair `(i,j)`). -/
noncomputable def pairInts {N : ℕ} (ℓ : ℝ) (w w1 w2 om : ℝ³ → ℝ³ → ℝ)
    (Φ : XN N → ℝ) (i j : Fin N) : ℝ :=
  (∫ x in abox N ℓ, fg0 ℓ w2 Φ i j x) + (∫ x in abox N ℓ, fg1 ℓ w2 Φ i j x)
    + (∫ x in abox N ℓ, fg2a ℓ w2 Φ i j x) + (∫ x in abox N ℓ, fg2b ℓ w2 Φ i j x)
    + (∫ x in abox N ℓ, fg2c ℓ w1 Φ i j x) + (∫ x in abox N ℓ, fg3 ℓ w1 Φ i j x)
    + (∫ x in abox N ℓ, fg4 ℓ w om Φ i j x)

/-! ## Continuity of the fragment integrands -/
lemma fg0_continuous {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {i j : Fin N}
    {w2 : ℝ³ → ℝ³ → ℝ} (hw2c : Continuous (fun p : ℝ³ × ℝ³ => w2 p.1 p.2))
    {Φ : XN N → ℝ} (hΦc : Continuous Φ) :
    Continuous (fun x : XN N => fg0 ℓ w2 Φ i j x) := by
  unfold fg0
  have hcPP : Continuous (aP ℓ i (aP ℓ j Φ)) := aP_continuous hℓ i (aP_continuous hℓ j hΦc)
  have hw2c' : Continuous (fun x : XN N => w2 (x i) (x j)) :=
    hw2c.comp (by fun_prop : Continuous (fun x : XN N => (x i, x j)))
  fun_prop

lemma fg1_continuous {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {i j : Fin N}
    {w2 : ℝ³ → ℝ³ → ℝ} (hw2c : Continuous (fun p : ℝ³ × ℝ³ => w2 p.1 p.2))
    {Φ : XN N → ℝ} (hΦc : Continuous Φ) :
    Continuous (fun x : XN N => fg1 ℓ w2 Φ i j x) := by
  unfold fg1
  have hcPQ : Continuous (aP ℓ i (aQ ℓ j Φ)) := aP_continuous hℓ i (aQ_continuous hℓ j hΦc)
  have hcPP : Continuous (aP ℓ i (aP ℓ j Φ)) := aP_continuous hℓ i (aP_continuous hℓ j hΦc)
  have hw2c' : Continuous (fun x : XN N => w2 (x i) (x j)) :=
    hw2c.comp (by fun_prop : Continuous (fun x : XN N => (x i, x j)))
  fun_prop

lemma fg2a_continuous {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {i j : Fin N}
    {w2 : ℝ³ → ℝ³ → ℝ} (hw2c : Continuous (fun p : ℝ³ × ℝ³ => w2 p.1 p.2))
    {Φ : XN N → ℝ} (hΦc : Continuous Φ) :
    Continuous (fun x : XN N => fg2a ℓ w2 Φ i j x) := by
  unfold fg2a
  have hcPQ : Continuous (aP ℓ i (aQ ℓ j Φ)) := aP_continuous hℓ i (aQ_continuous hℓ j hΦc)
  have hcQP : Continuous (aP ℓ j (aQ ℓ i Φ)) := aP_continuous hℓ j (aQ_continuous hℓ i hΦc)
  have hw2c' : Continuous (fun x : XN N => w2 (x i) (x j)) :=
    hw2c.comp (by fun_prop : Continuous (fun x : XN N => (x i, x j)))
  fun_prop

lemma fg2b_continuous {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {i j : Fin N}
    {w2 : ℝ³ → ℝ³ → ℝ} (hw2c : Continuous (fun p : ℝ³ × ℝ³ => w2 p.1 p.2))
    {Φ : XN N → ℝ} (hΦc : Continuous Φ) :
    Continuous (fun x : XN N => fg2b ℓ w2 Φ i j x) := by
  unfold fg2b
  have hcPQ : Continuous (aP ℓ i (aQ ℓ j Φ)) := aP_continuous hℓ i (aQ_continuous hℓ j hΦc)
  have hcQP : Continuous (aQ ℓ j (aP ℓ i Φ)) := aQ_continuous hℓ j (aP_continuous hℓ i hΦc)
  have hw2c' : Continuous (fun x : XN N => w2 (x i) (x j)) :=
    hw2c.comp (by fun_prop : Continuous (fun x : XN N => (x i, x j)))
  fun_prop

lemma fg2c_continuous {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {i j : Fin N}
    {w1 : ℝ³ → ℝ³ → ℝ} (hw1c : Continuous (fun p : ℝ³ × ℝ³ => w1 p.1 p.2))
    {Φ : XN N → ℝ} (hΦc : Continuous Φ) :
    Continuous (fun x : XN N => fg2c ℓ w1 Φ i j x) := by
  unfold fg2c
  have hcPP : Continuous (aP ℓ i (aP ℓ j Φ)) := aP_continuous hℓ i (aP_continuous hℓ j hΦc)
  have hcQQ : Continuous (aQ ℓ j (aQ ℓ i Φ)) := aQ_continuous hℓ j (aQ_continuous hℓ i hΦc)
  have hw1c' : Continuous (fun x : XN N => w1 (x i) (x j)) :=
    hw1c.comp (by fun_prop : Continuous (fun x : XN N => (x i, x j)))
  fun_prop

lemma fg3_continuous {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {i j : Fin N}
    {w1 : ℝ³ → ℝ³ → ℝ} (hw1c : Continuous (fun p : ℝ³ × ℝ³ => w1 p.1 p.2))
    {Φ : XN N → ℝ} (hΦc : Continuous Φ) :
    Continuous (fun x : XN N => fg3 ℓ w1 Φ i j x) := by
  unfold fg3
  have hcPQ : Continuous (aP ℓ i (aQ ℓ j Φ)) := aP_continuous hℓ i (aQ_continuous hℓ j hΦc)
  have hcQQ : Continuous (aQ ℓ j (aQ ℓ i Φ)) := aQ_continuous hℓ j (aQ_continuous hℓ i hΦc)
  have hw1c' : Continuous (fun x : XN N => w1 (x i) (x j)) :=
    hw1c.comp (by fun_prop : Continuous (fun x : XN N => (x i, x j)))
  fun_prop

lemma fg4_continuous {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {i j : Fin N}
    {w om : ℝ³ → ℝ³ → ℝ} (hwc : Continuous (fun p : ℝ³ × ℝ³ => w p.1 p.2))
    (homc : Continuous (fun p : ℝ³ × ℝ³ => om p.1 p.2))
    {Φ : XN N → ℝ} (hΦc : Continuous Φ) :
    Continuous (fun x : XN N => fg4 ℓ w om Φ i j x) := by
  unfold fg4
  have hcQ : Continuous (fun x : XN N => q4B ℓ om Φ (i, j) x) := by
    have hcQQ : Continuous (aQ ℓ j (aQ ℓ i Φ)) := aQ_continuous hℓ j (aQ_continuous hℓ i hΦc)
    have hcPP : Continuous (aP ℓ j (aP ℓ i Φ)) := aP_continuous hℓ j (aP_continuous hℓ i hΦc)
    have hcPQ : Continuous (aP ℓ j (aQ ℓ i Φ)) := aP_continuous hℓ j (aQ_continuous hℓ i hΦc)
    have hcQP : Continuous (aQ ℓ j (aP ℓ i Φ)) := aQ_continuous hℓ j (aP_continuous hℓ i hΦc)
    have homc' : Continuous (fun x : XN N => om (x i) (x j)) :=
      homc.comp (by fun_prop : Continuous (fun x : XN N => (x i, x j)))
    unfold q4B
    fun_prop
  have hwc' : Continuous (fun x : XN N => w (x i) (x j)) :=
    hwc.comp (by fun_prop : Continuous (fun x : XN N => (x i, x j)))
  fun_prop
/-- Pointwise form of the pair identity: for every `x` the combined
two-orientation word fragments at `(xᵢ,xⱼ)` equal `Φ(x)²·w(xᵢ,xⱼ)`. -/
lemma potsplit_pair_pointwise {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {i j : Fin N} (hij : i ≠ j)
    {w w1 w2 om : ℝ³ → ℝ³ → ℝ}
    (hwsym : ∀ x y : ℝ³, w x y = w y x) (homsym : ∀ x y : ℝ³, om x y = om y x)
    (hw1rel : ∀ x y : ℝ³, w1 x y = w x y * (1 - om x y))
    (hw2rel : ∀ x y : ℝ³, w2 x y = w x y * (1 - om x y ^ 2))
    {Φ : XN N → ℝ} (hΦc : Continuous Φ) (x : XN N) :
    fgsum ℓ w w1 w2 om Φ i j x = (Φ x) ^ 2 * w (x i) (x j) := by
  let A : ℝ := aP ℓ i (aP ℓ j Φ) x
  let B : ℝ := aP ℓ i (aQ ℓ j Φ) x
  let C : ℝ := aQ ℓ i (aP ℓ j Φ) x
  let D : ℝ := aQ ℓ i (aQ ℓ j Φ) x
  let W : ℝ := w (x i) (x j)
  let O : ℝ := om (x i) (x j)
  let W1 : ℝ := w1 (x i) (x j)
  let W2 : ℝ := w2 (x i) (x j)
  have hW1 : W1 = W * (1 - O) := by
    simpa [W, O, W1] using hw1rel (x i) (x j)
  have hW2 : W2 = W * (1 - O ^ 2) := by
    simpa [W, O, W2] using hw2rel (x i) (x j)
  have hpat : A + B + C + D = Φ x := by
    simpa [A, B, C, D] using pattern_sum hℓ hij hΦc x
  unfold fgsum fg0 fg1 fg2a fg2b fg2c fg3 fg4
  have hPPji : aP ℓ j (aP ℓ i Φ) x = A := by simpa [A] using (aP_comm hℓ i j hΦc x).symm
  have hPQji : aP ℓ j (aQ ℓ i Φ) x = C := by
    simpa [C] using aP_aQ_comm hℓ hij.symm hΦc x
  have hQPji : aQ ℓ j (aP ℓ i Φ) x = B := by
    simpa [B] using (aP_aQ_comm hℓ hij hΦc x).symm
  have hQQji : aQ ℓ j (aQ ℓ i Φ) x = D := by
    simpa [D] using (aQ_comm hℓ hij hΦc x).symm
  have hW2sym : w2 (x j) (x i) = W2 := by
    simpa [W2] using (w2_sym hwsym homsym hw2rel (x i) (x j)).symm
  have hW1sym : w1 (x j) (x i) = W1 := by
    simpa [W1] using (w1_sym hwsym homsym hw1rel (x i) (x j)).symm
  have hWsym : w (x j) (x i) = W := by
    simpa [W] using (hwsym (x i) (x j)).symm
  have hOsym : om (x j) (x i) = O := by
    simpa [O] using (homsym (x i) (x j)).symm
  have h0ij : (1 / 2) * (aP ℓ i (aP ℓ j Φ) x) ^ 2 * w2 (x i) (x j) = (1 / 2) * A ^ 2 * W2 := by
    simp [A, W2]
  have h0ji : (1 / 2) * (aP ℓ j (aP ℓ i Φ) x) ^ 2 * w2 (x j) (x i) = (1 / 2) * A ^ 2 * W2 := by
    simp [hPPji, hW2sym]
  have h1ij : 2 * (aP ℓ i (aQ ℓ j Φ) x) * (aP ℓ i (aP ℓ j Φ) x) * w2 (x i) (x j)
      = 2 * B * A * W2 := by
    simp [B, A, W2]
  have h1ji : 2 * (aP ℓ j (aQ ℓ i Φ) x) * (aP ℓ j (aP ℓ i Φ) x) * w2 (x j) (x i)
      = 2 * C * A * W2 := by
    simp [hPQji, hPPji, hW2sym]
  have h2aij : (aP ℓ i (aQ ℓ j Φ) x) * (aP ℓ j (aQ ℓ i Φ) x) * w2 (x i) (x j)
      = B * C * W2 := by
    simp [B, hPQji, W2]
  have h2aji : (aP ℓ j (aQ ℓ i Φ) x) * (aP ℓ i (aQ ℓ j Φ) x) * w2 (x j) (x i)
      = C * B * W2 := by
    simp [hPQji, B, hW2sym]
  have h2bij : (aP ℓ i (aQ ℓ j Φ) x) * (aQ ℓ j (aP ℓ i Φ) x) * w2 (x i) (x j)
      = B * B * W2 := by
    simp [B, hQPji, W2]
  have h2bji : (aP ℓ j (aQ ℓ i Φ) x) * (aQ ℓ i (aP ℓ j Φ) x) * w2 (x j) (x i)
      = C * C * W2 := by
    simp [hPQji, C, hW2sym]
  have h2cij : (aP ℓ i (aP ℓ j Φ) x) * (aQ ℓ j (aQ ℓ i Φ) x) * w1 (x i) (x j)
      = A * D * W1 := by
    simp [A, hQQji, W1]
  have h2cji : (aP ℓ j (aP ℓ i Φ) x) * (aQ ℓ i (aQ ℓ j Φ) x) * w1 (x j) (x i)
      = A * D * W1 := by
    simp [hPPji, D, hW1sym]
  have h3ij : 2 * (aP ℓ i (aQ ℓ j Φ) x) * (aQ ℓ j (aQ ℓ i Φ) x) * w1 (x i) (x j)
      = 2 * B * D * W1 := by
    simp [B, hQQji, W1]
  have h3ji : 2 * (aP ℓ j (aQ ℓ i Φ) x) * (aQ ℓ i (aQ ℓ j Φ) x) * w1 (x j) (x i)
      = 2 * C * D * W1 := by
    simp [hPQji, D, hW1sym]
  have hB4ij : q4B ℓ om Φ (i, j) x = D + O * (A + B + C) := by
    unfold q4B
    rw [hQQji, hPPji, hPQji, hQPji]
    ring
  have hB4ji : q4B ℓ om Φ (j, i) x = D + O * (A + B + C) := by
    unfold q4B
    rw [aQ_comm hℓ hij hΦc x, hQQji, hOsym]
  have h4ij : (1 / 2) * (q4B ℓ om Φ (i, j) x) ^ 2 * w (x i) (x j)
      = (1 / 2) * (D + O * (A + B + C)) ^ 2 * W := by
    simp [hB4ij, W]
  have h4ji : (1 / 2) * (q4B ℓ om Φ (j, i) x) ^ 2 * w (x j) (x i)
      = (1 / 2) * (D + O * (A + B + C)) ^ 2 * W := by
    simp [hB4ji, hWsym]
  rw [h0ij, h1ij, h2aij, h2bij, h2cij, h3ij, h4ij, h0ji, h1ji, h2aji, h2bji, h2cji, h3ji, h4ji]
  rw [hW1, hW2, ← hpat]
  ring

/-- The pair lemma: the two orientations of the word fragments together give
the full `w`-expectation over the pair: for `i ≠ j`,
`pairInts(i,j) + pairInts(j,i) = ∫ (Φ²·w(xᵢ,xⱼ))`. -/
lemma potsplit_pair_agree {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {i j : Fin N} (hij : i ≠ j)
    {w w1 w2 om : ℝ³ → ℝ³ → ℝ}
    (hwc : Continuous (fun p : ℝ³ × ℝ³ => w p.1 p.2))
    (homc : Continuous (fun p : ℝ³ × ℝ³ => om p.1 p.2))
    (hwsym : ∀ x y : ℝ³, w x y = w y x) (homsym : ∀ x y : ℝ³, om x y = om y x)
    (hw1rel : ∀ x y : ℝ³, w1 x y = w x y * (1 - om x y))
    (hw2rel : ∀ x y : ℝ³, w2 x y = w x y * (1 - om x y ^ 2))
    {Φ : XN N → ℝ} (hΦc : Continuous Φ) :
    pairInts ℓ w w1 w2 om Φ i j + pairInts ℓ w w1 w2 om Φ j i =
      (∫ x in abox N ℓ, (Φ x) ^ 2 * w (x i) (x j)) := by
  have hw1c : Continuous (fun p : ℝ³ × ℝ³ => w1 p.1 p.2) := w1_continuous hwc homc hw1rel
  have hw2c : Continuous (fun p : ℝ³ × ℝ³ => w2 p.1 p.2) := w2_continuous hwc homc hw2rel
  have c0c : Continuous (fun x : XN N => fg0 ℓ w2 Φ i j x) := fg0_continuous hℓ hw2c hΦc
  have i0 : IntegrableOn (fun x : XN N => fg0 ℓ w2 Φ i j x) (abox N ℓ) volume := integrableOn_abox_of_continuous hℓ c0c
  have c1c : Continuous (fun x : XN N => fg1 ℓ w2 Φ i j x) := fg1_continuous hℓ hw2c hΦc
  have i1 : IntegrableOn (fun x : XN N => fg1 ℓ w2 Φ i j x) (abox N ℓ) volume := integrableOn_abox_of_continuous hℓ c1c
  have c2c : Continuous (fun x : XN N => fg2a ℓ w2 Φ i j x) := fg2a_continuous hℓ hw2c hΦc
  have i2 : IntegrableOn (fun x : XN N => fg2a ℓ w2 Φ i j x) (abox N ℓ) volume := integrableOn_abox_of_continuous hℓ c2c
  have c3c : Continuous (fun x : XN N => fg2b ℓ w2 Φ i j x) := fg2b_continuous hℓ hw2c hΦc
  have i3 : IntegrableOn (fun x : XN N => fg2b ℓ w2 Φ i j x) (abox N ℓ) volume := integrableOn_abox_of_continuous hℓ c3c
  have c4c : Continuous (fun x : XN N => fg2c ℓ w1 Φ i j x) := fg2c_continuous hℓ hw1c hΦc
  have i4 : IntegrableOn (fun x : XN N => fg2c ℓ w1 Φ i j x) (abox N ℓ) volume := integrableOn_abox_of_continuous hℓ c4c
  have c5c : Continuous (fun x : XN N => fg3 ℓ w1 Φ i j x) := fg3_continuous hℓ hw1c hΦc
  have i5 : IntegrableOn (fun x : XN N => fg3 ℓ w1 Φ i j x) (abox N ℓ) volume := integrableOn_abox_of_continuous hℓ c5c
  have c6c : Continuous (fun x : XN N => fg4 ℓ w om Φ i j x) := fg4_continuous hℓ hwc homc hΦc
  have i6 : IntegrableOn (fun x : XN N => fg4 ℓ w om Φ i j x) (abox N ℓ) volume := integrableOn_abox_of_continuous hℓ c6c
  have c7c : Continuous (fun x : XN N => fg0 ℓ w2 Φ j i x) := fg0_continuous hℓ hw2c hΦc
  have i7 : IntegrableOn (fun x : XN N => fg0 ℓ w2 Φ j i x) (abox N ℓ) volume := integrableOn_abox_of_continuous hℓ c7c
  have c8c : Continuous (fun x : XN N => fg1 ℓ w2 Φ j i x) := fg1_continuous hℓ hw2c hΦc
  have i8 : IntegrableOn (fun x : XN N => fg1 ℓ w2 Φ j i x) (abox N ℓ) volume := integrableOn_abox_of_continuous hℓ c8c
  have c9c : Continuous (fun x : XN N => fg2a ℓ w2 Φ j i x) := fg2a_continuous hℓ hw2c hΦc
  have i9 : IntegrableOn (fun x : XN N => fg2a ℓ w2 Φ j i x) (abox N ℓ) volume := integrableOn_abox_of_continuous hℓ c9c
  have c10c : Continuous (fun x : XN N => fg2b ℓ w2 Φ j i x) := fg2b_continuous hℓ hw2c hΦc
  have i10 : IntegrableOn (fun x : XN N => fg2b ℓ w2 Φ j i x) (abox N ℓ) volume := integrableOn_abox_of_continuous hℓ c10c
  have c11c : Continuous (fun x : XN N => fg2c ℓ w1 Φ j i x) := fg2c_continuous hℓ hw1c hΦc
  have i11 : IntegrableOn (fun x : XN N => fg2c ℓ w1 Φ j i x) (abox N ℓ) volume := integrableOn_abox_of_continuous hℓ c11c
  have c12c : Continuous (fun x : XN N => fg3 ℓ w1 Φ j i x) := fg3_continuous hℓ hw1c hΦc
  have i12 : IntegrableOn (fun x : XN N => fg3 ℓ w1 Φ j i x) (abox N ℓ) volume := integrableOn_abox_of_continuous hℓ c12c
  have c13c : Continuous (fun x : XN N => fg4 ℓ w om Φ j i x) := fg4_continuous hℓ hwc homc hΦc
  have i13 : IntegrableOn (fun x : XN N => fg4 ℓ w om Φ j i x) (abox N ℓ) volume := integrableOn_abox_of_continuous hℓ c13c
  have p1c : Continuous (fun x : XN N => fg0 ℓ w2 Φ i j x + fg1 ℓ w2 Φ i j x) := by fun_prop
  have ip1 : IntegrableOn (fun x : XN N => fg0 ℓ w2 Φ i j x + fg1 ℓ w2 Φ i j x) (abox N ℓ) volume := integrableOn_abox_of_continuous hℓ p1c
  have p2c : Continuous (fun x : XN N => fg0 ℓ w2 Φ i j x + fg1 ℓ w2 Φ i j x + fg2a ℓ w2 Φ i j x) := by fun_prop
  have ip2 : IntegrableOn (fun x : XN N => fg0 ℓ w2 Φ i j x + fg1 ℓ w2 Φ i j x + fg2a ℓ w2 Φ i j x) (abox N ℓ) volume := integrableOn_abox_of_continuous hℓ p2c
  have p3c : Continuous (fun x : XN N => fg0 ℓ w2 Φ i j x + fg1 ℓ w2 Φ i j x + fg2a ℓ w2 Φ i j x + fg2b ℓ w2 Φ i j x) := by fun_prop
  have ip3 : IntegrableOn (fun x : XN N => fg0 ℓ w2 Φ i j x + fg1 ℓ w2 Φ i j x + fg2a ℓ w2 Φ i j x + fg2b ℓ w2 Φ i j x) (abox N ℓ) volume := integrableOn_abox_of_continuous hℓ p3c
  have p4c : Continuous (fun x : XN N => fg0 ℓ w2 Φ i j x + fg1 ℓ w2 Φ i j x + fg2a ℓ w2 Φ i j x + fg2b ℓ w2 Φ i j x + fg2c ℓ w1 Φ i j x) := by fun_prop
  have ip4 : IntegrableOn (fun x : XN N => fg0 ℓ w2 Φ i j x + fg1 ℓ w2 Φ i j x + fg2a ℓ w2 Φ i j x + fg2b ℓ w2 Φ i j x + fg2c ℓ w1 Φ i j x) (abox N ℓ) volume := integrableOn_abox_of_continuous hℓ p4c
  have p5c : Continuous (fun x : XN N => fg0 ℓ w2 Φ i j x + fg1 ℓ w2 Φ i j x + fg2a ℓ w2 Φ i j x + fg2b ℓ w2 Φ i j x + fg2c ℓ w1 Φ i j x + fg3 ℓ w1 Φ i j x) := by fun_prop
  have ip5 : IntegrableOn (fun x : XN N => fg0 ℓ w2 Φ i j x + fg1 ℓ w2 Φ i j x + fg2a ℓ w2 Φ i j x + fg2b ℓ w2 Φ i j x + fg2c ℓ w1 Φ i j x + fg3 ℓ w1 Φ i j x) (abox N ℓ) volume := integrableOn_abox_of_continuous hℓ p5c
  have p6c : Continuous (fun x : XN N => fg0 ℓ w2 Φ i j x + fg1 ℓ w2 Φ i j x + fg2a ℓ w2 Φ i j x + fg2b ℓ w2 Φ i j x + fg2c ℓ w1 Φ i j x + fg3 ℓ w1 Φ i j x + fg4 ℓ w om Φ i j x) := by fun_prop
  have ip6 : IntegrableOn (fun x : XN N => fg0 ℓ w2 Φ i j x + fg1 ℓ w2 Φ i j x + fg2a ℓ w2 Φ i j x + fg2b ℓ w2 Φ i j x + fg2c ℓ w1 Φ i j x + fg3 ℓ w1 Φ i j x + fg4 ℓ w om Φ i j x) (abox N ℓ) volume := integrableOn_abox_of_continuous hℓ p6c
  have q1c : Continuous (fun x : XN N => fg0 ℓ w2 Φ j i x + fg1 ℓ w2 Φ j i x) := by fun_prop
  have iq1 : IntegrableOn (fun x : XN N => fg0 ℓ w2 Φ j i x + fg1 ℓ w2 Φ j i x) (abox N ℓ) volume := integrableOn_abox_of_continuous hℓ q1c
  have q2c : Continuous (fun x : XN N => fg0 ℓ w2 Φ j i x + fg1 ℓ w2 Φ j i x + fg2a ℓ w2 Φ j i x) := by fun_prop
  have iq2 : IntegrableOn (fun x : XN N => fg0 ℓ w2 Φ j i x + fg1 ℓ w2 Φ j i x + fg2a ℓ w2 Φ j i x) (abox N ℓ) volume := integrableOn_abox_of_continuous hℓ q2c
  have q3c : Continuous (fun x : XN N => fg0 ℓ w2 Φ j i x + fg1 ℓ w2 Φ j i x + fg2a ℓ w2 Φ j i x + fg2b ℓ w2 Φ j i x) := by fun_prop
  have iq3 : IntegrableOn (fun x : XN N => fg0 ℓ w2 Φ j i x + fg1 ℓ w2 Φ j i x + fg2a ℓ w2 Φ j i x + fg2b ℓ w2 Φ j i x) (abox N ℓ) volume := integrableOn_abox_of_continuous hℓ q3c
  have q4c : Continuous (fun x : XN N => fg0 ℓ w2 Φ j i x + fg1 ℓ w2 Φ j i x + fg2a ℓ w2 Φ j i x + fg2b ℓ w2 Φ j i x + fg2c ℓ w1 Φ j i x) := by fun_prop
  have iq4 : IntegrableOn (fun x : XN N => fg0 ℓ w2 Φ j i x + fg1 ℓ w2 Φ j i x + fg2a ℓ w2 Φ j i x + fg2b ℓ w2 Φ j i x + fg2c ℓ w1 Φ j i x) (abox N ℓ) volume := integrableOn_abox_of_continuous hℓ q4c
  have q5c : Continuous (fun x : XN N => fg0 ℓ w2 Φ j i x + fg1 ℓ w2 Φ j i x + fg2a ℓ w2 Φ j i x + fg2b ℓ w2 Φ j i x + fg2c ℓ w1 Φ j i x + fg3 ℓ w1 Φ j i x) := by fun_prop
  have iq5 : IntegrableOn (fun x : XN N => fg0 ℓ w2 Φ j i x + fg1 ℓ w2 Φ j i x + fg2a ℓ w2 Φ j i x + fg2b ℓ w2 Φ j i x + fg2c ℓ w1 Φ j i x + fg3 ℓ w1 Φ j i x) (abox N ℓ) volume := integrableOn_abox_of_continuous hℓ q5c
  have q6c : Continuous (fun x : XN N => fg0 ℓ w2 Φ j i x + fg1 ℓ w2 Φ j i x + fg2a ℓ w2 Φ j i x + fg2b ℓ w2 Φ j i x + fg2c ℓ w1 Φ j i x + fg3 ℓ w1 Φ j i x + fg4 ℓ w om Φ j i x) := by fun_prop
  have iq6 : IntegrableOn (fun x : XN N => fg0 ℓ w2 Φ j i x + fg1 ℓ w2 Φ j i x + fg2a ℓ w2 Φ j i x + fg2b ℓ w2 Φ j i x + fg2c ℓ w1 Φ j i x + fg3 ℓ w1 Φ j i x + fg4 ℓ w om Φ j i x) (abox N ℓ) volume := integrableOn_abox_of_continuous hℓ q6c
  have hA : pairInts ℓ w w1 w2 om Φ i j = (∫ x in abox N ℓ, fg0 ℓ w2 Φ i j x + fg1 ℓ w2 Φ i j x + fg2a ℓ w2 Φ i j x + fg2b ℓ w2 Φ i j x + fg2c ℓ w1 Φ i j x + fg3 ℓ w1 Φ i j x + fg4 ℓ w om Φ i j x) := by
    unfold pairInts
    rw [← integral_add i0 i1]
    rw [← integral_add ip1 i2]
    rw [← integral_add ip2 i3]
    rw [← integral_add ip3 i4]
    rw [← integral_add ip4 i5]
    rw [← integral_add ip5 i6]
  have hB : pairInts ℓ w w1 w2 om Φ j i = (∫ x in abox N ℓ, fg0 ℓ w2 Φ j i x + fg1 ℓ w2 Φ j i x + fg2a ℓ w2 Φ j i x + fg2b ℓ w2 Φ j i x + fg2c ℓ w1 Φ j i x + fg3 ℓ w1 Φ j i x + fg4 ℓ w om Φ j i x) := by
    unfold pairInts
    rw [← integral_add i7 i8]
    rw [← integral_add iq1 i9]
    rw [← integral_add iq2 i10]
    rw [← integral_add iq3 i11]
    rw [← integral_add iq4 i12]
    rw [← integral_add iq5 i13]
  have iA : IntegrableOn (fun x : XN N => fg0 ℓ w2 Φ i j x + fg1 ℓ w2 Φ i j x + fg2a ℓ w2 Φ i j x + fg2b ℓ w2 Φ i j x + fg2c ℓ w1 Φ i j x + fg3 ℓ w1 Φ i j x + fg4 ℓ w om Φ i j x) (abox N ℓ) volume := integrableOn_abox_of_continuous hℓ (by fun_prop)
  have iB : IntegrableOn (fun x : XN N => fg0 ℓ w2 Φ j i x + fg1 ℓ w2 Φ j i x + fg2a ℓ w2 Φ j i x + fg2b ℓ w2 Φ j i x + fg2c ℓ w1 Φ j i x + fg3 ℓ w1 Φ j i x + fg4 ℓ w om Φ j i x) (abox N ℓ) volume := integrableOn_abox_of_continuous hℓ (by fun_prop)
  have hkey : (fun x : XN N => fg0 ℓ w2 Φ i j x + fg1 ℓ w2 Φ i j x + fg2a ℓ w2 Φ i j x + fg2b ℓ w2 Φ i j x + fg2c ℓ w1 Φ i j x + fg3 ℓ w1 Φ i j x + fg4 ℓ w om Φ i j x + (fg0 ℓ w2 Φ j i x + fg1 ℓ w2 Φ j i x + fg2a ℓ w2 Φ j i x + fg2b ℓ w2 Φ j i x + fg2c ℓ w1 Φ j i x + fg3 ℓ w1 Φ j i x + fg4 ℓ w om Φ j i x)) = fun x : XN N => (Φ x) ^ 2 * w (x i) (x j) := by
    funext x
    have h1 := potsplit_pair_pointwise hℓ hij hwsym homsym hw1rel hw2rel hΦc x
    unfold fgsum at h1
    rw [← h1]
    ring
  calc
    pairInts ℓ w w1 w2 om Φ i j + pairInts ℓ w w1 w2 om Φ j i
        = (∫ x in abox N ℓ, fg0 ℓ w2 Φ i j x + fg1 ℓ w2 Φ i j x + fg2a ℓ w2 Φ i j x + fg2b ℓ w2 Φ i j x + fg2c ℓ w1 Φ i j x + fg3 ℓ w1 Φ i j x + fg4 ℓ w om Φ i j x) + (∫ x in abox N ℓ, fg0 ℓ w2 Φ j i x + fg1 ℓ w2 Φ j i x + fg2a ℓ w2 Φ j i x + fg2b ℓ w2 Φ j i x + fg2c ℓ w1 Φ j i x + fg3 ℓ w1 Φ j i x + fg4 ℓ w om Φ j i x) := by
          rw [hA, hB]
    _ = (∫ x in abox N ℓ, fg0 ℓ w2 Φ i j x + fg1 ℓ w2 Φ i j x + fg2a ℓ w2 Φ i j x + fg2b ℓ w2 Φ i j x + fg2c ℓ w1 Φ i j x + fg3 ℓ w1 Φ i j x + fg4 ℓ w om Φ i j x + (fg0 ℓ w2 Φ j i x + fg1 ℓ w2 Φ j i x + fg2a ℓ w2 Φ j i x + fg2b ℓ w2 Φ j i x + fg2c ℓ w1 Φ j i x + fg3 ℓ w1 Φ j i x + fg4 ℓ w om Φ j i x)) := by
          rw [← integral_add iA iB]
    _ = (∫ x in abox N ℓ, (Φ x) ^ 2 * w (x i) (x j)) := by
          rw [hkey]

/-- The sum of the seven word pair-parts over `pairSet` equals the sum over
pairs of `pairInts` (fragment re-assembly; each `∫fg*` carries its word
coefficient already). -/
lemma pair_part_sum_eq {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {w w1 w2 om : ℝ³ → ℝ³ → ℝ}
    (hwc : Continuous (fun p : ℝ³ × ℝ³ => w p.1 p.2))
    (homc : Continuous (fun p : ℝ³ × ℝ³ => om p.1 p.2))
    {Φ : XN N → ℝ} (hΦc : Continuous Φ) :
    (1 / 2) * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
          (aP ℓ p.1 (aP ℓ p.2 Φ) x) ^ 2 * w2 (x p.1) (x p.2))
      + 2 * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
          (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aP ℓ p.1 (aP ℓ p.2 Φ) x) * w2 (x p.1) (x p.2))
      + (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
          (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aP ℓ p.2 (aQ ℓ p.1 Φ) x) * w2 (x p.1) (x p.2))
      + (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
          (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aQ ℓ p.2 (aP ℓ p.1 Φ) x) * w2 (x p.1) (x p.2))
      + (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
          (aP ℓ p.1 (aP ℓ p.2 Φ) x) * (aQ ℓ p.2 (aQ ℓ p.1 Φ) x) * w1 (x p.1) (x p.2))
      + 2 * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
          (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aQ ℓ p.2 (aQ ℓ p.1 Φ) x) * w1 (x p.1) (x p.2))
      + (1 / 2) * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
          (q4B ℓ om Φ p x) ^ 2 * w (x p.1) (x p.2))
    = ∑ p ∈ pairSet N, pairInts ℓ w w1 w2 om Φ p.1 p.2 := by
  unfold pairInts
  -- expand each sum over pairSet with the fragment form and collect by p
  -- helper: for a function F on pairSet, c * (∑ F) = ∑ (c * F) and constants pass through integrals
  have h0 : (1 / 2) * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
          (aP ℓ p.1 (aP ℓ p.2 Φ) x) ^ 2 * w2 (x p.1) (x p.2))
      = ∑ p ∈ pairSet N, (∫ x in abox N ℓ, fg0 ℓ w2 Φ p.1 p.2 x) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    rw [← integral_const_mul (1 / 2 : ℝ) (fun x : XN N => (aP ℓ p.1 (aP ℓ p.2 Φ) x) ^ 2 * w2 (x p.1) (x p.2))]
    apply integral_congr_ae
    filter_upwards with x
    unfold fg0
    ring
  have h1 : 2 * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
          (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aP ℓ p.1 (aP ℓ p.2 Φ) x) * w2 (x p.1) (x p.2))
      = ∑ p ∈ pairSet N, (∫ x in abox N ℓ, fg1 ℓ w2 Φ p.1 p.2 x) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    rw [← integral_const_mul (2 : ℝ) (fun x : XN N => (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aP ℓ p.1 (aP ℓ p.2 Φ) x) * w2 (x p.1) (x p.2))]
    apply integral_congr_ae
    filter_upwards with x
    unfold fg1
    ring
  have h2a : (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
          (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aP ℓ p.2 (aQ ℓ p.1 Φ) x) * w2 (x p.1) (x p.2))
      = ∑ p ∈ pairSet N, (∫ x in abox N ℓ, fg2a ℓ w2 Φ p.1 p.2 x) := by
    apply Finset.sum_congr rfl
    intro p hp
    rfl
  have h2b : (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
          (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aQ ℓ p.2 (aP ℓ p.1 Φ) x) * w2 (x p.1) (x p.2))
      = ∑ p ∈ pairSet N, (∫ x in abox N ℓ, fg2b ℓ w2 Φ p.1 p.2 x) := by
    apply Finset.sum_congr rfl
    intro p hp
    rfl
  have h2c : (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
          (aP ℓ p.1 (aP ℓ p.2 Φ) x) * (aQ ℓ p.2 (aQ ℓ p.1 Φ) x) * w1 (x p.1) (x p.2))
      = ∑ p ∈ pairSet N, (∫ x in abox N ℓ, fg2c ℓ w1 Φ p.1 p.2 x) := by
    apply Finset.sum_congr rfl
    intro p hp
    rfl
  have h3 : 2 * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
          (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aQ ℓ p.2 (aQ ℓ p.1 Φ) x) * w1 (x p.1) (x p.2))
      = ∑ p ∈ pairSet N, (∫ x in abox N ℓ, fg3 ℓ w1 Φ p.1 p.2 x) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    rw [← integral_const_mul (2 : ℝ) (fun x : XN N => (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aQ ℓ p.2 (aQ ℓ p.1 Φ) x) * w1 (x p.1) (x p.2))]
    apply integral_congr_ae
    filter_upwards with x
    unfold fg3
    ring
  have h4 : (1 / 2) * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
          (q4B ℓ om Φ p x) ^ 2 * w (x p.1) (x p.2))
      = ∑ p ∈ pairSet N, (∫ x in abox N ℓ, fg4 ℓ w om Φ p.1 p.2 x) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    rw [← integral_const_mul (1 / 2 : ℝ) (fun x : XN N => (q4B ℓ om Φ p x) ^ 2 * w (x p.1) (x p.2))]
    apply integral_congr_ae
    filter_upwards with x
    unfold fg4
    ring
  rw [h0, h1, h2a, h2b, h2c, h3, h4]
  -- now the LHS is the sum over the seven fragment-sum lists; merge by p
  rw [← Finset.sum_add_distrib]
  rw [← Finset.sum_add_distrib]
  rw [← Finset.sum_add_distrib]
  rw [← Finset.sum_add_distrib]
  rw [← Finset.sum_add_distrib]
  rw [← Finset.sum_add_distrib]

noncomputable def pairrawSum {N : ℕ} (ℓ : ℝ) (w w1 w2 om : ℝ³ → ℝ³ → ℝ)
    (Φ : XN N → ℝ) : ℝ :=
  (1 / 2) * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
  (aP ℓ p.1 (aP ℓ p.2 Φ) x) ^ 2 * w2 (x p.1) (x p.2))
  + 2 * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
  (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aP ℓ p.1 (aP ℓ p.2 Φ) x) * w2 (x p.1) (x p.2))
  + (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
  (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aP ℓ p.2 (aQ ℓ p.1 Φ) x) * w2 (x p.1) (x p.2))
  + (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
  (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aQ ℓ p.2 (aP ℓ p.1 Φ) x) * w2 (x p.1) (x p.2))
  + (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
  (aP ℓ p.1 (aP ℓ p.2 Φ) x) * (aQ ℓ p.2 (aQ ℓ p.1 Φ) x) * w1 (x p.1) (x p.2))
  + 2 * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
  (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aQ ℓ p.2 (aQ ℓ p.1 Φ) x) * w1 (x p.1) (x p.2))
  + (1 / 2) * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
  (q4B ℓ om Φ p x) ^ 2 * w (x p.1) (x p.2))

/-- `pairrawSum` equals the sum of the `pairInts`. -/
lemma pairrawSum_eq {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {w w1 w2 om : ℝ³ → ℝ³ → ℝ}
    (hwc : Continuous (fun p : ℝ³ × ℝ³ => w p.1 p.2))
    (homc : Continuous (fun p : ℝ³ × ℝ³ => om p.1 p.2))
    {Φ : XN N → ℝ} (hΦc : Continuous Φ) :
    pairrawSum ℓ w w1 w2 om Φ = ∑ p ∈ pairSet N, pairInts ℓ w w1 w2 om Φ p.1 p.2 := by
  unfold pairrawSum
  exact pair_part_sum_eq hℓ hwc homc hΦc

/-- Reindexing by the coordinate swap over `pairSet`: `∑ₚ g(p.2,p.1) = ∑ₚ g p`. -/
lemma pairSet_swap_sum {N : ℕ} (g : Fin N × Fin N → ℝ) :
    (∑ p ∈ pairSet N, g (p.2, p.1)) = ∑ p ∈ pairSet N, g p := by
  refine Finset.sum_bij' (i := fun p hp => (p.2, p.1)) (j := fun p hp => (p.2, p.1)) ?_ ?_ ?_ ?_ ?_
  · intro p hp
    simp [pairSet] at hp ⊢
    intro h
    exact hp (by simpa using h.symm)
  · intro p hp
    simp [pairSet] at hp ⊢
    intro h
    exact hp (by simpa using h.symm)
  · intro p hp
    rfl
  · intro p hp
    rfl
  · intro p hp
    rfl

/-- The μ-sums of the five words combine into the full-`Φ²` slot sums. -/
lemma mu_sum_agree {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {w1 : ℝ³ → ℝ³ → ℝ} (hw1c : Continuous (fun p : ℝ³ × ℝ³ => w1 p.1 p.2))
    {Φ : XN N → ℝ} (hΦc : Continuous Φ) :
    (∑ i : Fin N, muP ℓ w1 Φ i) + 2 * (∑ i : Fin N, muQP ℓ w1 Φ i)
      + (∑ i : Fin N, muQ ℓ w1 Φ i)
    = ∑ i : Fin N, muPhi ℓ w1 Φ i := by
  calc
    (∑ i : Fin N, muP ℓ w1 Φ i) + 2 * (∑ i : Fin N, muQP ℓ w1 Φ i)
        + (∑ i : Fin N, muQ ℓ w1 Φ i)
        = (∑ i : Fin N, muP ℓ w1 Φ i) + (∑ i : Fin N, 2 * muQP ℓ w1 Φ i)
            + (∑ i : Fin N, muQ ℓ w1 Φ i) := by
          rw [Finset.mul_sum]
    _ = ∑ i : Fin N, ((muP ℓ w1 Φ i + 2 * muQP ℓ w1 Φ i) + muQ ℓ w1 Φ i) := by
          rw [← Finset.sum_add_distrib]
          rw [← Finset.sum_add_distrib]
    _ = ∑ i : Fin N, muPhi ℓ w1 Φ i := by
          apply Finset.sum_congr rfl
          intro i hi
          have h := potsplit_mu_agree hℓ (i := i) hw1c hΦc
          rw [← h]
          ring


/-- The corpus-native potential splitting (`lem:potsplit eq:potsplit`): for any
kernels `w w1 w2 ω` with `w1 = w(1−ω)`, `w2 = w(1−ω²)` pointwise, the
potential word equals the sum of the five `𝒬`-words, for every continuous `Φ`
over the centred box.  (Pure algebra: `Pᵢ+Qᵢ = 1` pointwise, the kernel
relations, and the self-adjointness/idempotence of the per-slot projections.) -/
theorem potsplit_expect {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (μ : ℝ)
    {w w1 w2 om : ℝ³ → ℝ³ → ℝ}
    (hwc : Continuous (fun p : ℝ³ × ℝ³ => w p.1 p.2))
    (homc : Continuous (fun p : ℝ³ × ℝ³ => om p.1 p.2))
    (hwsym : ∀ x y : ℝ³, w x y = w y x)
    (homsym : ∀ x y : ℝ³, om x y = om y x)
    (hw1rel : ∀ x y : ℝ³, w1 x y = w x y * (1 - om x y))
    (hw2rel : ∀ x y : ℝ³, w2 x y = w x y * (1 - om x y ^ 2))
    {Φ : XN N → ℝ} (hΦc : Continuous Φ) :
    qLHSword (N := N) ℓ μ w w1 Φ =
      q0word (N := N) ℓ μ w1 w2 Φ + q1word (N := N) ℓ μ w1 w2 Φ
        + q2word (N := N) ℓ μ w1 w2 Φ + q3word (N := N) ℓ w1 Φ
        + q4word (N := N) ℓ w om Φ := by
  have hw1c : Continuous (fun p : ℝ³ × ℝ³ => w1 p.1 p.2) := w1_continuous hwc homc hw1rel
  have hw2c : Continuous (fun p : ℝ³ × ℝ³ => w2 p.1 p.2) := w2_continuous hwc homc hw2rel
  -- continuity / integrability of the building blocks
  have hfibc : ∀ i : Fin N, Continuous (fun x : XN N => w1Fibre ℓ w1 (x i)) := by
    intro i
    exact (w1Fibre_continuous hℓ hw1c).comp (by fun_prop : Continuous (fun x : XN N => x i))
  have hfibsumc : Continuous (fun x : XN N => ∑ i : Fin N, w1Fibre ℓ w1 (x i)) := by
    refine continuous_finset_sum (Finset.univ : Finset (Fin N)) (fun i hi => ?_)
    exact hfibc i
  have hWsumc : Continuous (fun x : XN N => ∑ p ∈ pairSet N, w (x p.1) (x p.2)) := by
    refine continuous_finset_sum (pairSet N) (fun p hp => ?_)
    exact hwc.comp (by fun_prop : Continuous (fun x : XN N => (x p.1, x p.2)))
  have hint1 : IntegrableOn (fun x : XN N => (Φ x) ^ 2 * (- μ * (∑ i : Fin N, w1Fibre ℓ w1 (x i)))) (abox N ℓ) volume :=
    integrableOn_abox_of_continuous hℓ (by fun_prop)
  have hint2 : IntegrableOn (fun x : XN N => (Φ x) ^ 2 * ((1 / 2) * (∑ p ∈ pairSet N, w (x p.1) (x p.2)))) (abox N ℓ) volume :=
    integrableOn_abox_of_continuous hℓ (by fun_prop)
  have hfi : ∀ i : Fin N, IntegrableOn (fun x : XN N => (Φ x) ^ 2 * w1Fibre ℓ w1 (x i)) (abox N ℓ) volume := by
    intro i
    refine integrableOn_abox_of_continuous hℓ ?_
    exact (hΦc.pow 2).mul (hfibc i)
  have hWi : ∀ p ∈ pairSet N, IntegrableOn (fun x : XN N => (Φ x) ^ 2 * w (x p.1) (x p.2)) (abox N ℓ) volume := by
    intro p hp
    refine integrableOn_abox_of_continuous hℓ ?_
    exact (hΦc.pow 2).mul (hwc.comp (by fun_prop : Continuous (fun x : XN N => (x p.1, x p.2))))
  -- the μ part of the LHS (pull the slot-sum out of the integral)
  have hmu : (∫ x in abox N ℓ, (Φ x) ^ 2 * (- μ * (∑ i : Fin N, w1Fibre ℓ w1 (x i)))) =
      - μ * (∑ i : Fin N, muPhi ℓ w1 Φ i) := by
    calc
      (∫ x in abox N ℓ, (Φ x) ^ 2 * (- μ * (∑ i : Fin N, w1Fibre ℓ w1 (x i))))
          = (∫ x in abox N ℓ, (- μ) * ((Φ x) ^ 2 * (∑ i : Fin N, w1Fibre ℓ w1 (x i)))) := by
            apply integral_congr_ae
            filter_upwards with x
            ring
      _ = - μ * (∫ x in abox N ℓ, (Φ x) ^ 2 * (∑ i : Fin N, w1Fibre ℓ w1 (x i))) := by
            rw [← integral_const_mul (- μ) (fun x : XN N => (Φ x) ^ 2 * (∑ i : Fin N, w1Fibre ℓ w1 (x i)))]
      _ = - μ * (∑ i : Fin N, (∫ x in abox N ℓ, (Φ x) ^ 2 * w1Fibre ℓ w1 (x i))) := by
            congr 1
            calc
              (∫ x in abox N ℓ, (Φ x) ^ 2 * (∑ i : Fin N, w1Fibre ℓ w1 (x i)))
                  = ∫ x in abox N ℓ, (∑ i : Fin N, (Φ x) ^ 2 * w1Fibre ℓ w1 (x i)) := by
                    apply integral_congr_ae
                    filter_upwards with x
                    rw [Finset.mul_sum]
              _ = ∑ i : Fin N, (∫ x in abox N ℓ, (Φ x) ^ 2 * w1Fibre ℓ w1 (x i)) := by
                    exact integral_finsetSum (Finset.univ : Finset (Fin N)) (fun i hi => by simpa [IntegrableOn] using hfi i)
      _ = - μ * (∑ i : Fin N, muPhi ℓ w1 Φ i) := by
            simp [muPhi]
  -- the pair part of the LHS (pull the pair-sum out of the integral)
  have hpair : (∫ x in abox N ℓ, (Φ x) ^ 2 * ((1 / 2) * (∑ p ∈ pairSet N, w (x p.1) (x p.2)))) =
      (1 / 2) * (∑ p ∈ pairSet N, ∫ x in abox N ℓ, (Φ x) ^ 2 * w (x p.1) (x p.2)) := by
    calc
      (∫ x in abox N ℓ, (Φ x) ^ 2 * ((1 / 2) * (∑ p ∈ pairSet N, w (x p.1) (x p.2))))
          = (∫ x in abox N ℓ, (1 / 2) * ((Φ x) ^ 2 * (∑ p ∈ pairSet N, w (x p.1) (x p.2)))) := by
            apply integral_congr_ae
            filter_upwards with x
            ring
      _ = (1 / 2) * (∫ x in abox N ℓ, (Φ x) ^ 2 * (∑ p ∈ pairSet N, w (x p.1) (x p.2))) := by
            rw [← integral_const_mul (1 / 2 : ℝ) (fun x : XN N => (Φ x) ^ 2 * (∑ p ∈ pairSet N, w (x p.1) (x p.2)))]
      _ = (1 / 2) * (∑ p ∈ pairSet N, ∫ x in abox N ℓ, (Φ x) ^ 2 * w (x p.1) (x p.2)) := by
            congr 1
            calc
              (∫ x in abox N ℓ, (Φ x) ^ 2 * (∑ p ∈ pairSet N, w (x p.1) (x p.2)))
                  = ∫ x in abox N ℓ, (∑ p ∈ pairSet N, (Φ x) ^ 2 * w (x p.1) (x p.2)) := by
                    apply integral_congr_ae
                    filter_upwards with x
                    rw [Finset.mul_sum]
              _ = ∑ p ∈ pairSet N, (∫ x in abox N ℓ, (Φ x) ^ 2 * w (x p.1) (x p.2)) := by
                    exact integral_finsetSum (pairSet N) (fun p hp => by simpa [IntegrableOn] using hWi p hp)
  -- (i) the LHS is the μ-term plus the pair term
  have hLHS : qLHSword ℓ μ w w1 Φ =
      - μ * (∑ i : Fin N, muPhi ℓ w1 Φ i)
        + (1 / 2) * (∑ p ∈ pairSet N, ∫ x in abox N ℓ, (Φ x) ^ 2 * w (x p.1) (x p.2)) := by
    calc
      qLHSword ℓ μ w w1 Φ = ∫ x in abox N ℓ, (Φ x) ^ 2 * (- μ * (∑ i : Fin N, w1Fibre ℓ w1 (x i))
          + (1 / 2) * (∑ p ∈ pairSet N, w (x p.1) (x p.2))) := by
            rfl
      _ = (∫ x in abox N ℓ, (Φ x) ^ 2 * (- μ * (∑ i : Fin N, w1Fibre ℓ w1 (x i))))
          + (∫ x in abox N ℓ, (Φ x) ^ 2 * ((1 / 2) * (∑ p ∈ pairSet N, w (x p.1) (x p.2)))) := by
            rw [← integral_add hint1 hint2]
            apply integral_congr_ae
            filter_upwards with x
            ring
      _ = - μ * (∑ i : Fin N, muPhi ℓ w1 Φ i)
          + (1 / 2) * (∑ p ∈ pairSet N, ∫ x in abox N ℓ, (Φ x) ^ 2 * w (x p.1) (x p.2)) := by
            rw [hmu, hpair]
  -- (ii) the five words: pair parts (the raw seven sums) + μ parts
  have hwords : q0word ℓ μ w1 w2 Φ + q1word ℓ μ w1 w2 Φ + q2word ℓ μ w1 w2 Φ
      + q3word ℓ w1 Φ + q4word ℓ w om Φ
      = pairrawSum ℓ w w1 w2 om Φ
        - μ * ((∑ i : Fin N, muP ℓ w1 Φ i) + 2 * (∑ i : Fin N, muQP ℓ w1 Φ i)
          + (∑ i : Fin N, muQ ℓ w1 Φ i)) := by
    unfold q0word q1word q2word q3word q4word
    simp [muP, muQP, muQ, pairrawSum]
    ring
  -- (iii) the pair-claim: pair sums telescope into half the `Φ²`-sums
  have hpairsum : pairrawSum ℓ w w1 w2 om Φ
      = (1 / 2) * (∑ p ∈ pairSet N, ∫ x in abox N ℓ, (Φ x) ^ 2 * w (x p.1) (x p.2)) := by
    calc
      pairrawSum ℓ w w1 w2 om Φ
          = (1 / 2) * (pairrawSum ℓ w w1 w2 om Φ + (∑ p ∈ pairSet N, pairInts ℓ w w1 w2 om Φ p.2 p.1)) := by
            rw [pairrawSum_eq hℓ hwc homc hΦc]
            have hswap : (∑ p ∈ pairSet N, pairInts ℓ w w1 w2 om Φ p.2 p.1)
                = ∑ p ∈ pairSet N, pairInts ℓ w w1 w2 om Φ p.1 p.2 := by
              exact pairSet_swap_sum (fun p : Fin N × Fin N => pairInts ℓ w w1 w2 om Φ p.1 p.2)
            rw [hswap]
            ring
      _ = (1 / 2) * (∑ p ∈ pairSet N, ∫ x in abox N ℓ, (Φ x) ^ 2 * w (x p.1) (x p.2)) := by
            congr 1
            rw [pairrawSum_eq hℓ hwc homc hΦc]
            rw [← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro p hp
            have hpne : p.1 ≠ p.2 := by
              simpa [pairSet] using hp
            exact potsplit_pair_agree hℓ hpne hwc homc hwsym homsym hw1rel hw2rel hΦc
  -- (iv) μ sums
  have hmusum : (∑ i : Fin N, muP ℓ w1 Φ i) + 2 * (∑ i : Fin N, muQP ℓ w1 Φ i)
      + (∑ i : Fin N, muQ ℓ w1 Φ i) = ∑ i : Fin N, muPhi ℓ w1 Φ i :=
    mu_sum_agree hℓ hw1c hΦc
  calc
    qLHSword ℓ μ w w1 Φ = - μ * (∑ i : Fin N, muPhi ℓ w1 Φ i)
        + (1 / 2) * (∑ p ∈ pairSet N, ∫ x in abox N ℓ, (Φ x) ^ 2 * w (x p.1) (x p.2)) := by
          rw [hLHS]
    _ = - μ * (∑ i : Fin N, muPhi ℓ w1 Φ i) + pairrawSum ℓ w w1 w2 om Φ := by
          rw [hpairsum]
    _ = q0word ℓ μ w1 w2 Φ + q1word ℓ μ w1 w2 Φ + q2word ℓ μ w1 w2 Φ
        + q3word ℓ w1 Φ + q4word ℓ w om Φ := by
          rw [hwords]
          rw [← hmusum]
          ring

/-- Q4 is nonnegative whenever the kernel `w` is pointwise nonnegative on the
box (then `q4word = ½Σ∫(BΦ)²·w ≥ 0`). -/
lemma q4_nonneg {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {w om : ℝ³ → ℝ³ → ℝ}
    (hw : ∀ x y : ℝ³, 0 ≤ w x y) {Φ : XN N → ℝ} :
    0 ≤ q4word (N := N) ℓ w om Φ := by
  unfold q4word
  apply mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)
  exact Finset.sum_nonneg (fun p hp => by
    apply integral_nonneg
    intro x
    exact mul_nonneg (sq_nonneg (q4B ℓ om Φ p x)) (hw (x p.1) (x p.2)))

/-! ## Chosen-branch instantiation

With the chosen scattering solution `w₀` of the radial potential `v`
(`h : ∃w, IsRadial w ∧ IsScatteringSolution w v`) and the χ-renormalized
kernels `wPair`, the relations `w1 = w(1−ω)`, `w2 = w(1−ω²)` hold pointwise
(`KernelRel.w1_eq_w_mul_one_sub` / `w2_eq_w_mul_one_sub_sq`).
-/

/-- Nonnegativity of the `wPair` kernel under `0 ≤ v` (pointwise; division by
zero gives `0`). -/
lemma wPairC_nonneg {v : ℝ³ → ℝ} (hv : 0 ≤ v) (ℓ : ℝ) : ∀ x y : ℝ³, 0 ≤ wPairC ℓ v x y := by
  intro x y
  have h1 : 0 ≤ chiScale ℓ x := chiScale_nonneg ℓ x
  have h2 : 0 ≤ chiScale ℓ y := chiScale_nonneg ℓ y
  have h3 : 0 ≤ v (x - y) / convScale ℓ (x - y) := by
    by_cases hz : convScale ℓ (x - y) = 0
    · rw [hz]
      simp
    · have hc : 0 < convScale ℓ (x - y) := lt_of_le_of_ne (convScale_nonneg ℓ (x - y)) (Ne.symm hz)
      exact div_nonneg (hv (x - y)) hc.le
  unfold wPairC wPair wScaled
  positivity

/-- Pointwise relation `w₁ = w·(1−ω)` in the chosen branch. -/
lemma w1rel_chosen {v : ℝ³ → ℝ}
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v) (ℓ : ℝ) :
    ∀ x y : ℝ³, wPairC ℓ (g0 v h) x y =
      wPairC ℓ v x y * (1 - omC (Classical.choose h) x y) := by
  intro x y
  exact w1_eq_w_mul_one_sub h ℓ x y

/-- Pointwise relation `w₂ = w·(1−ω²)` in the chosen branch. -/
lemma w2rel_chosen {v : ℝ³ → ℝ}
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v) (ℓ : ℝ) :
    ∀ x y : ℝ³, wPairC ℓ (g2 v h) x y =
      wPairC ℓ v x y * (1 - (omC (Classical.choose h) x y) ^ 2) := by
  intro x y
  exact w2_eq_w_mul_one_sub_sq h ℓ x y


end BoseGases

end Submission
