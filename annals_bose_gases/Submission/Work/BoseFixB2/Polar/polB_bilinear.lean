import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB2.Polar.boxFormB_parallelogram
import Submission.Work.BoseFixB2.Polar.polB_symm
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB2.Polar.polB_bilinear` — `polB` is bilinear

FS §6's polarised box word

    `4·polB v h μ n Φ Ψ = wordB v h μ n (Φ+Ψ) − wordB v h μ n (Φ−Ψ)`

is `ℝ`-bilinear:

    `polB (Φ₁+Φ₂) Ψ = polB Φ₁ Ψ + polB Φ₂ Ψ`,   `polB Ψ (Φ₁+Φ₂) = polB Ψ Φ₁ + polB Ψ Φ₂`.

The proof splits in three independent layers.

## 1. The abstract layer (`polB_par_three`, `polB_add_left_par`)

For **any** function `Q : V → ℝ` on an additive commutative group which

* satisfies the parallelogram law `Q (x+y) + Q (x-y) = 2Q x + 2Q y`, and
* is **even**, `Q (-x) = Q x`,

the polarisation `(Q (x+y) − Q (x-y))` is additive in each variable.  This is the classical
computation: the three-term identity

`(Q (u+v+w) − Q (u+v−w)) + (Q (u−v+w) − Q (u−v−w)) = 2 (Q (u+w) − Q (u−w))`

is the parallelogram law at the five pairs `(u, v+w)`, `(u, v−w)`, `(u−w, v)`, `(v, w)`,
`(u, w)`; applying it once at `(x, y, z)` and once at `(y, x, z)` — where the second is turned
into the first by evenness — gives additivity after one `linarith`.

The hypotheses are carried over a predicate `G` (the "admissible states"), because the
parallelogram law for `wordB` below is proved only for *smooth* states.

**Remark (why the parallelogram law cannot be dropped).**  Sibling module
`Polar.par_polarisation` records the explicit counterexample: for a function which is only
`2`-homogeneous and satisfies the parallelogram law, the defect
`t ↦ (Q (t•x+y) − Q (t•x−y)) − t (Q (x+y) − Q (x−y))` is a *derivation* of `ℝ`, and non-zero
derivations of `ℝ` exist (the Wronskian form of `∂/∂π`).  Consequently bilinearity of the
polarisation is *not* formal, and the concrete geometry of `wordB` must enter — which is what
the next two layers do.

## 2. The degenerate box (`wordB_eq_zero_of_side_nonpos`)

`wordB v h μ n = boxFormB n v (g0 v h) (fsSide v μ) μ d s ε_T b`.  If the box side is
non-positive, then the configuration box `abox n ℓ` is contained in the single point `0` and
hence is null for `n ≥ 1` (`abox_volume` plus `Measure.pi_nullSingletonClass`), so both the
kinetic and the potential integrals vanish; for `n = 0` the kinetic sum is empty and
`potWordU 0 = 0`.  Hence `wordB` vanishes identically, and the parallelogram law is `0 = 0`.

This case is not vacuous: the box side is `fsSide v μ = K_ℓ (μ · a v)^{-1/2}` and Mathlib's
`Real.rpow` vanishes on a negative base at the exponent `-1/2` (`Work.BoseBox.rpow_neg_half_of_neg`,
`cos (-π/2) = 0`), so e.g. `μ < 0 < a v` gives `fsSide v μ = 0`.

## 3. The positive box (`wordB_parallelogram`)

If `fsSide v μ > 0`, then `Kl · (μ·a v)^{-1/2} = ℓ > 0` forces `μ·a v > 0` (the negative- and
zero-base branches of `Real.rpow` give `ℓ = 0`), whence `μ·(a v)³ > 0` and the parameter block
is positive: `d = t^{6/323}`, `s = t^{1/323}`, `ε_T = t^{23/1292}`, `b = 1/16`.  The parallelogram
law is then exactly `Polar.boxFormB_parallelogram`, applied at the parameters
`(fsSide v μ, d, s, ε_T, b)`, with smoothness of the two states and the integrability of
`potWordU` on the box as its remaining inputs.

## 4. Assembly

With `Q := wordB v h μ n` and `G` the smooth states, layer 1 gives the additivity of the
polarisation in the first variable; the second variable follows from the symmetry
`Polar.polB_symm`.
-/

noncomputable section

open scoped Real Topology BigOperators
open MeasureTheory

namespace Work.BoseFixB2.Polar

open Submission.BoseGases Work.BoseKinLoc Work.BoseBox Work.BoseBoxFix

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 1. The abstract polarisation algebra -/

/-- **The three-term identity.**  For a function `Q` satisfying the parallelogram law (on a
predicate `G` of admissible elements),

`(Q (u+v+w) − Q (u+v−w)) + (Q (u−v+w) − Q (u−v−w)) = 2 (Q (u+w) − Q (u−w))`.

It is the parallelogram law at the five pairs `(u, v+w)`, `(u, v−w)`, `(u−w, v)`, `(v, w)`,
`(u, w)`, combined by linear arithmetic; `G` is closed under `+` and `−`. -/
lemma polB_par_three {V : Type*} [AddCommGroup V] (Q : V → ℝ) (G : Set V)
    (hGadd : ∀ a b : V, G a → G b → G (a + b))
    (hGneg : ∀ a : V, G a → G (-a))
    (hpar : ∀ a b : V, G a → G b → Q (a + b) + Q (a - b) = 2 * Q a + 2 * Q b)
    (u v w : V) (hu : G u) (hv : G v) (hw : G w) :
    (Q (u + v + w) - Q (u + v - w)) + (Q (u - v + w) - Q (u - v - w))
      = 2 * (Q (u + w) - Q (u - w)) := by
  have hGsub : ∀ a b : V, G a → G b → G (a - b) := by
    intro a b ha hb
    have h := hGadd a (-b) ha (hGneg b hb)
    simpa only [sub_eq_add_neg] using h
  have E1 := hpar u (v + w) hu (hGadd v w hv hw)
  have E2 := hpar u (v - w) hu (hGsub v w hv hw)
  have E4 := hpar (u - w) v (hGsub u w hu hw) hv
  have Pvw := hpar v w hv hw
  have Puw := hpar u w hu hw
  rw [show u + (v + w) = u + v + w by abel, show u - (v + w) = u - v - w by abel] at E1
  rw [show u + (v - w) = u + v - w by abel, show u - (v - w) = u - v + w by abel] at E2
  rw [show (u - w) + v = u + v - w by abel, show (u - w) - v = u - v - w by abel] at E4
  linarith

/-- **Additivity of the polarisation in the first variable.**  From the parallelogram law and
evenness of `Q` (both restricted to `G`) one gets

`Q (x+y+z) − Q (x+y−z) = (Q (x+z) − Q (x−z)) + (Q (y+z) − Q (y−z))`.

The three-term identity at `(x,y,z)` gives the sum, the one at `(y,x,z)` (with `y−x = −(x−y)`
and evenness) gives the difference; adding the two yields the claim. -/
lemma polB_add_left_par {V : Type*} [AddCommGroup V] (Q : V → ℝ) (G : Set V)
    (hGadd : ∀ a b : V, G a → G b → G (a + b))
    (hGneg : ∀ a : V, G a → G (-a))
    (hpar : ∀ a b : V, G a → G b → Q (a + b) + Q (a - b) = 2 * Q a + 2 * Q b)
    (hneg : ∀ a : V, G a → Q (-a) = Q a)
    (x y z : V) (hx : G x) (hy : G y) (hz : G z) :
    Q (x + y + z) - Q (x + y - z)
      = (Q (x + z) - Q (x - z)) + (Q (y + z) - Q (y - z)) := by
  have hGsub : ∀ a b : V, G a → G b → G (a - b) := by
    intro a b ha hb
    have h := hGadd a (-b) ha (hGneg b hb)
    simpa only [sub_eq_add_neg] using h
  have hA := polB_par_three Q G hGadd hGneg hpar x y z hx hy hz
  have key : Q (x + y + z) - Q (x + y - z) - (Q (x - y + z) - Q (x - y - z))
      = 2 * (Q (y + z) - Q (y - z)) := by
    have h := polB_par_three Q G hGadd hGneg hpar y x z hy hx hz
    rw [show y + x = x + y by abel] at h
    have h2 : Q (y - x + z) - Q (y - x - z) = -(Q (x - y + z) - Q (x - y - z)) := by
      have hyx : y - x = -(x - y) := by abel
      rw [hyx]
      have e1 : -(x - y) + z = -((x - y) - z) := by abel
      have e2 : -(x - y) - z = -((x - y) + z) := by abel
      rw [e1, e2, hneg ((x - y) - z) (hGsub (x - y) z (hGsub x y hx hy) hz),
        hneg ((x - y) + z) (hGadd (x - y) z (hGsub x y hx hy) hz)]
      ring
    rw [h2] at h
    linarith
  linarith

/-! ## 2. The degenerate box: `abox n ℓ` for `ℓ ≤ 0` is a null set -/

/-- For a non-positive side length the centred cube `acube ℓ` is contained in `{0}`. -/
lemma acube_subset_zero_of_nonpos {ℓ : ℝ} (hℓ : ℓ ≤ 0) :
    acube ℓ ⊆ ({(0 : EuclideanSpace ℝ (Fin 3))} : Set (EuclideanSpace ℝ (Fin 3))) := by
  intro y hy
  rw [Set.mem_singleton_iff]
  rw [mem_acube_iff] at hy
  apply WithLp.ofLp_injective
  funext m
  have h := hy m
  rw [Set.mem_Icc] at h
  simp only [WithLp.ofLp_zero, Pi.zero_apply]
  linarith [h.1, h.2]

/-- For a non-positive side length the `N`-particle box `abox N ℓ` is contained in `{0}`. -/
lemma abox_subset_singleton_of_nonpos {N : ℕ} {ℓ : ℝ} (hℓ : ℓ ≤ 0) :
    abox N ℓ ⊆ ({(0 : X N)} : Set (X N)) := by
  intro x hx
  rw [Set.mem_singleton_iff]
  rw [mem_abox_iff] at hx
  funext i
  exact Set.mem_singleton_iff.mp (acube_subset_zero_of_nonpos hℓ (hx i))

/-- For `ℓ ≤ 0` and `N ≥ 1` the box `abox N ℓ` is a null set (it is contained in the singleton
`{0}`, and the product measure on `X N = Fin N → ℝ³` has no atoms when `N ≥ 1`). -/
lemma volume_abox_eq_zero_of_nonpos {N : ℕ} (i : Fin N) {ℓ : ℝ} (hℓ : ℓ ≤ 0) :
    (volume : Measure (X N)) (abox N ℓ) = 0 :=
  measure_mono_null (abox_subset_singleton_of_nonpos hℓ)
    ((MeasureTheory.Measure.pi_nullSingletonClass
        (μ := fun _ : Fin N => (volume : Measure (EuclideanSpace ℝ (Fin 3)))) i).measure_singleton
      (0 : X N))

/-- The box form of a state vanishes when the box side is non-positive and there is at least one
particle: the configuration box is null, so both the kinetic and the potential integrals
vanish. -/
lemma boxFormB_eq_zero_of_side_nonpos {n : ℕ} (hn : 0 < n) {v g : ℝ³ → ℝ} {ℓ μ d s eT b : ℝ}
    (hℓ : ℓ ≤ 0) (Ξ : X n → ℝ) : boxFormB n v g ℓ μ d s eT b Ξ = 0 := by
  simp only [boxFormB, kinFormB]
  rw [Finset.sum_eq_zero
      (fun i _ => setIntegral_measure_zero _ (volume_abox_eq_zero_of_nonpos i hℓ)),
    mul_zero, zero_add]
  exact setIntegral_measure_zero _ (volume_abox_eq_zero_of_nonpos ⟨0, hn⟩ hℓ)

/-- `potWordU` of a zero-particle configuration vanishes (both the chemical-potential sum and
the pair sum are empty). -/
lemma potWordU_zero_particles (v g : ℝ³ → ℝ) (ℓ μ : ℝ) (u : ℝ³) (x : X 0) :
    potWordU 0 v g ℓ μ u x = 0 := by
  simp [potWordU]

/-- The box form of a zero-particle state vanishes, for any box side and any parameter block. -/
lemma boxFormB_eq_zero_zero_particles {v g : ℝ³ → ℝ} {ℓ μ d s eT b : ℝ} (Ξ : X 0 → ℝ) :
    boxFormB 0 v g ℓ μ d s eT b Ξ = 0 := by
  simp [boxFormB, kinFormB, potWordU]

/-- **The box word vanishes identically when the box side is non-positive.** -/
lemma wordB_eq_zero_of_side_nonpos {v : ℝ³ → ℝ} {h : Work.UBB.ScatSol v} {μ : ℝ} {n : ℕ}
    (hℓ : Work.BoseFixB2.fsSide v μ ≤ 0) (Ξ : X n → ℝ) :
    wordB v h μ n Ξ = 0 := by
  cases n with
  | zero =>
      exact boxFormB_eq_zero_zero_particles (v := v) (g := g0 v h)
        (ℓ := Work.BoseFixB2.fsSide v μ) Ξ
  | succ k =>
      exact boxFormB_eq_zero_of_side_nonpos (n := k + 1) (Nat.succ_pos k) (v := v)
        (g := g0 v h) (ℓ := Work.BoseFixB2.fsSide v μ) hℓ Ξ

/-! ## 3. Positivity of the parameter block from a positive box side -/

/-- **The box side can only be positive if `μ · a v > 0`.**  Indeed
`fsSide v μ = K_ℓ · (μ·a v)^{-1/2}`, and for a non-positive base the factor
`(μ·a v)^{-1/2}` vanishes: on a negative base `Real.rpow` is
`exp (log x · y) · cos (y · π)` (`Real.rpow_def_of_neg`) and `cos (-π/2) = 0`
(`Work.BoseBox.rpow_neg_half_of_neg`), while at the base `0` it is `Real.zero_rpow`. -/
lemma fsSide_pos_imp_mul_pos {v : EuclideanSpace ℝ (Fin 3) → ℝ} {μ : ℝ}
    (h : 0 < Work.BoseFixB2.fsSide v μ) : 0 < μ * _root_.BoseGases.a v := by
  by_contra hc
  have hp0 : μ * _root_.BoseGases.a v ≤ 0 := not_lt.mp hc
  rcases lt_or_eq_of_le hp0 with hp' | hp'
  · have hz : (μ * _root_.BoseGases.a v) ^ (-(1 / 2 : ℝ)) = 0 := rpow_neg_half_of_neg hp'
    rw [Work.BoseFixB2.fsSide, sideAt, boxSide, hz, mul_zero] at h
    exact lt_irrefl 0 h
  · have hz : (μ * _root_.BoseGases.a v) ^ (-(1 / 2 : ℝ)) = 0 := by
      rw [hp']; exact Real.zero_rpow (by norm_num)
    rw [Work.BoseFixB2.fsSide, sideAt, boxSide, hz, mul_zero] at h
    exact lt_irrefl 0 h

/-- **The parameter block `(d, s, ε_T)` is positive as soon as the box side is positive**: with
`t = μ · (a v)³ > 0` one has `d = t^{6/323}`, `s = t^{1/323}`, `ε_T = t^{23/1292}`. -/
lemma fsSide_pos_imp_params_pos {v : EuclideanSpace ℝ (Fin 3) → ℝ} {μ : ℝ}
    (h : 0 < Work.BoseFixB2.fsSide v μ) :
    0 < (paramsAt μ (_root_.BoseGases.a v)).d ∧
    0 < (paramsAt μ (_root_.BoseGases.a v)).s ∧
    0 < (paramsAt μ (_root_.BoseGases.a v)).eT := by
  have hp := fsSide_pos_imp_mul_pos h
  have hav : _root_.BoseGases.a v ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hp
    exact lt_irrefl 0 hp
  have ha2 : 0 < (_root_.BoseGases.a v) ^ 2 := by
    rw [sq]
    exact mul_self_pos.mpr hav
  have ht : 0 < μ * (_root_.BoseGases.a v) ^ 3 := by
    have hEq : μ * (_root_.BoseGases.a v) ^ 3
        = (μ * _root_.BoseGases.a v) * (_root_.BoseGases.a v) ^ 2 := by ring
    rw [hEq]
    exact mul_pos hp ha2
  refine ⟨?_, ?_, ?_⟩ <;>
    · simp only [paramsAt, fsParams, fsXp]
      exact Real.rpow_pos_of_pos ht _

/-- The gap coefficient `b = 1/16` is positive (it is a fixed universal constant). -/
lemma paramsAt_b_pos' (μ a : ℝ) : 0 < (paramsAt μ a).b := by
  have h : (paramsAt μ a).b = (1 : ℝ) / 16 := by simp [paramsAt, fsParams, bValue]
  rw [h]; norm_num

/-! ## 4. The parallelogram law for the box word -/

/-- **`wordB` satisfies the parallelogram law on smooth states.**  Either the box side is
positive — and the claim is `Polar.boxFormB_parallelogram` at the parameters
`(fsSide v μ, d, s, ε_T, b)`, whose positivity comes from §3 — or the box side is non-positive
and `wordB` vanishes identically by §2, so the identity is `0 = 0`. -/
lemma wordB_parallelogram {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v} {μ : ℝ}
    {n : ℕ} {Φ Ψ : X n → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ)
    (hw : MeasureTheory.IntegrableOn
      (fun x : X n => potWordU n v (g0 v h) (Work.BoseFixB2.fsSide v μ) μ 0 x)
      (abox n (Work.BoseFixB2.fsSide v μ))) :
    wordB v h μ n (Φ + Ψ) + wordB v h μ n (Φ - Ψ)
      = 2 * wordB v h μ n Φ + 2 * wordB v h μ n Ψ := by
  by_cases hℓ : 0 < Work.BoseFixB2.fsSide v μ
  · obtain ⟨hd, hs, heT⟩ := fsSide_pos_imp_params_pos hℓ
    have hb : 0 < (paramsAt μ (_root_.BoseGases.a v)).b := paramsAt_b_pos' μ (_root_.BoseGases.a v)
    exact boxFormB_parallelogram (v := v) (g := g0 v h) (ℓ := Work.BoseFixB2.fsSide v μ)
      (μ := μ) (d := (paramsAt μ (_root_.BoseGases.a v)).d)
      (s := (paramsAt μ (_root_.BoseGases.a v)).s) (εT := (paramsAt μ (_root_.BoseGases.a v)).eT)
      (b := (paramsAt μ (_root_.BoseGases.a v)).b) hℓ hd hs heT hb (n := n) (Φ := Φ) (Ψ := Ψ)
      hΦ hΨ hw
  · have hℓ' : Work.BoseFixB2.fsSide v μ ≤ 0 := not_lt.mp hℓ
    rw [wordB_eq_zero_of_side_nonpos hℓ' (Φ + Ψ), wordB_eq_zero_of_side_nonpos hℓ' (Φ - Ψ),
      wordB_eq_zero_of_side_nonpos hℓ' Φ, wordB_eq_zero_of_side_nonpos hℓ' Ψ]
    ring

/-! ## 5. The bilinearity of `polB` -/

theorem polB_bilinear {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v} {μ : ℝ} {n : ℕ} {Φ₁ Φ₂ Ψ : Submission.BoseGases.X n → ℝ} (h₁ : ContDiff ℝ (⊤ : ℕ∞) Φ₁) (h₂ : ContDiff ℝ (⊤ : ℕ∞) Φ₂) (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ) (hw : MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X n => Work.BoseKinLoc.potWordU n v (Submission.BoseGases.g0 v h) (Work.BoseFixB2.fsSide v μ) μ 0 x) (Submission.BoseGases.abox n (Work.BoseFixB2.fsSide v μ))) : Work.BoseFixB2.polB v h μ n (fun x => Φ₁ x + Φ₂ x) Ψ = Work.BoseFixB2.polB v h μ n Φ₁ Ψ + Work.BoseFixB2.polB v h μ n Φ₂ Ψ ∧ Work.BoseFixB2.polB v h μ n Ψ (fun x => Φ₁ x + Φ₂ x) = Work.BoseFixB2.polB v h μ n Ψ Φ₁ + Work.BoseFixB2.polB v h μ n Ψ Φ₂ := by
  -- the parallelogram law and evenness of `wordB` on the smooth states
  have hpar : ∀ a b : Submission.BoseGases.X n → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) a → ContDiff ℝ (⊤ : ℕ∞) b →
      wordB v h μ n (a + b) + wordB v h μ n (a - b)
        = 2 * wordB v h μ n a + 2 * wordB v h μ n b :=
    fun a b ha hb => wordB_parallelogram (v := v) (h := h) (μ := μ) (n := n) ha hb hw
  have hneg : ∀ a : Submission.BoseGases.X n → ℝ, ContDiff ℝ (⊤ : ℕ∞) a →
      wordB v h μ n (-a) = wordB v h μ n a :=
    fun a _ => PolB.wordB_neg v h μ n a
  -- the abstract additivity of the polarisation, in the first variable
  have key := polB_add_left_par (fun Ξ : Submission.BoseGases.X n → ℝ => wordB v h μ n Ξ)
    {Ξ | ContDiff ℝ (⊤ : ℕ∞) Ξ}
    (fun a b (ha : ContDiff ℝ (⊤ : ℕ∞) a) (hb : ContDiff ℝ (⊤ : ℕ∞) b) => ha.add hb)
    (fun a (ha : ContDiff ℝ (⊤ : ℕ∞) a) => ha.neg)
    hpar hneg Φ₁ Φ₂ Ψ h₁ h₂ hΨ
  have key1 : polB v h μ n (fun x => Φ₁ x + Φ₂ x) Ψ
      = polB v h μ n Φ₁ Ψ + polB v h μ n Φ₂ Ψ := by
    have hgoal : wordB v h μ n (fun x => Φ₁ x + Φ₂ x + Ψ x)
        - wordB v h μ n (fun x => Φ₁ x + Φ₂ x - Ψ x)
        = (wordB v h μ n (fun x => Φ₁ x + Ψ x) - wordB v h μ n (fun x => Φ₁ x - Ψ x))
          + (wordB v h μ n (fun x => Φ₂ x + Ψ x) - wordB v h μ n (fun x => Φ₂ x - Ψ x)) := key
    show (wordB v h μ n (fun x => Φ₁ x + Φ₂ x + Ψ x)
        - wordB v h μ n (fun x => Φ₁ x + Φ₂ x - Ψ x)) / 4
        = (wordB v h μ n (fun x => Φ₁ x + Ψ x) - wordB v h μ n (fun x => Φ₁ x - Ψ x)) / 4
          + (wordB v h μ n (fun x => Φ₂ x + Ψ x) - wordB v h μ n (fun x => Φ₂ x - Ψ x)) / 4
    rw [hgoal]
    ring
  refine ⟨key1, ?_⟩
  rw [polB_symm (hΦ := hΨ) (hΨ := h₁.add h₂), polB_symm (hΦ := hΨ) (hΨ := h₁),
    polB_symm (hΦ := hΨ) (hΨ := h₂), key1]

end Work.BoseFixB2.Polar
