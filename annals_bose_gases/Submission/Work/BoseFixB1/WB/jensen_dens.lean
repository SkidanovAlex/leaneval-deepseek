import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB1.WB.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.WB.jensen_dens` — FS step 4, the pointwise Jensen/Jensen-density inequality

FS `final_v2.tex` step 4 of `thm:aprioriHLambda` (the vocabulary is in `WB/Defs.lean`):
for a box state `Φ`, a small-box centre `u` and the *local density*

  `dens u = (∫_{abox n ℓ} Φ² · nCountB u)/(‖Φ‖² · chiMass u)`,

the convex weight `F = psiWeight 1 μ` satisfies

  `‖Φ‖² · F(dens u) ≤ ∫_{abox n ℓ} Φ² · F(nCountB u / chiMass u)`,

i.e. Jensen's inequality for the probability density `Φ²/‖Φ‖²`.

The proof here uses the Cauchy–Schwarz form of that Jensen inequality: with
`a = Φ²`, `f = nCountB u`, `C = chiMass u`, `N = ∫a`, `I = ∫a f` one has the
pointwise identity `F(t/C) = (μ/C)·(t − μC)²/(t + μC)` (valid for `C ≠ 0`), and
weighted Cauchy–Schwarz applied to the split
`(f − μC)² = (f + μC)·((f − μC)²/(f + μC))` gives
`(I − μCN)² ≤ (I + μCN)·∫ a ((f − μC)²/(f + μC))`, which is the claim after two
algebraic rearrangements.  The degenerate cases `N = 0` and `C = 0` are handled
separately (both sides vanish, respectively coincide).
-/

noncomputable section
open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BoseFixB1.WB

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 1. Weighted Cauchy–Schwarz -/

/-- **Weighted Cauchy–Schwarz**: for `a ≥ 0`, `p > 0` and `g² = p·q` pointwise,
`(∫ a g)² ≤ (∫ a p)·(∫ a q)`.

Proof by the discriminant of the pointwise nonnegative quadratic
`λ ↦ ∫ a (g + λp)²/p`: expanding gives `K + 2λB + λ²A ≥ 0` for every real `λ`,
which forces `B² ≤ A K`. -/
theorem jd_weighted_cs {α : Type*} [MeasurableSpace α] (ν : MeasureTheory.Measure α)
    {a g p q : α → ℝ}
    (ha : ∀ x, 0 ≤ a x) (hp : ∀ x, 0 < p x) (hgq : ∀ x, g x ^ 2 = p x * q x)
    (hin_g : MeasureTheory.Integrable (fun x => a x * g x) ν)
    (hin_p : MeasureTheory.Integrable (fun x => a x * p x) ν)
    (hin_q : MeasureTheory.Integrable (fun x => a x * q x) ν) :
    (∫ x, a x * g x ∂ν) ^ 2 ≤ (∫ x, a x * p x ∂ν) * (∫ x, a x * q x ∂ν) := by
  set A : ℝ := ∫ x, a x * p x ∂ν with hA
  set B : ℝ := ∫ x, a x * g x ∂ν with hB
  set K : ℝ := ∫ x, a x * q x ∂ν with hK
  have hA_nonneg : 0 ≤ A := by
    rw [hA]
    exact integral_nonneg (fun x => mul_nonneg (ha x) (le_of_lt (hp x)))
  have hQ : ∀ lam : ℝ, 0 ≤ K + 2 * lam * B + lam ^ 2 * A := by
    intro lam
    have hpt : ∀ x, a x * ((g x + lam * p x) ^ 2 / p x)
        = a x * q x + 2 * lam * (a x * g x) + lam ^ 2 * (a x * p x) := by
      intro x
      have hgoal : (g x + lam * p x) ^ 2 / p x = q x + 2 * lam * g x + lam ^ 2 * p x := by
        rw [div_eq_iff (ne_of_gt (hp x))]
        nlinarith [hgq x]
      calc a x * ((g x + lam * p x) ^ 2 / p x)
          = a x * (q x + 2 * lam * g x + lam ^ 2 * p x) := by rw [hgoal]
        _ = a x * q x + 2 * lam * (a x * g x) + lam ^ 2 * (a x * p x) := by ring
    have hnonneg : 0 ≤ ∫ x, a x * ((g x + lam * p x) ^ 2 / p x) ∂ν :=
      integral_nonneg (fun x => mul_nonneg (ha x) (div_nonneg (sq_nonneg _) (le_of_lt (hp x))))
    have h1 : (∫ x, a x * ((g x + lam * p x) ^ 2 / p x) ∂ν) = K + 2 * lam * B + lam ^ 2 * A := by
      rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
      have h12 : MeasureTheory.Integrable (fun x => a x * q x + 2 * lam * (a x * g x)) ν :=
        hin_q.add (hin_g.const_mul (2 * lam))
      have h3 : MeasureTheory.Integrable (fun x => lam ^ 2 * (a x * p x)) ν :=
        hin_p.const_mul (lam ^ 2)
      have h1' : MeasureTheory.Integrable (fun x => a x * q x) ν := hin_q
      have h2' : MeasureTheory.Integrable (fun x => 2 * lam * (a x * g x)) ν :=
        hin_g.const_mul (2 * lam)
      simp only [integral_add h12 h3, integral_add h1' h2', integral_const_mul, hK, hB, hA]
    linarith [hnonneg, h1]
  rcases lt_or_ge (0 : ℝ) A with hApos | hAle
  · have hAne : A ≠ 0 := ne_of_gt hApos
    have hq := hQ (-B / A)
    have hD : B ^ 2 / A ≤ K := by
      have h3 : 2 * (-B / A) * B + (-B / A) ^ 2 * A = -(B ^ 2 / A) := by
        field_simp; ring
      linarith [hq, h3]
    have hmul : (B ^ 2 / A) * A = B ^ 2 := by field_simp
    nlinarith [hD, hmul, hApos]
  · have hA0 : A = 0 := le_antisymm hAle hA_nonneg
    have hB0 : B = 0 := by
      by_contra hBne
      have hq := hQ (-(K + 1) / (2 * B))
      have h4 : K + 2 * (-(K + 1) / (2 * B)) * B + (-(K + 1) / (2 * B)) ^ 2 * A = -1 := by
        rw [hA0]; field_simp; ring
      linarith [hq, h4]
    simp [hA0, hB0]

/-! ## 2. Two algebraic forms of `F = psiWeight 1 μ` -/

/-- `F(t) = μ(t−μ)²/(t+μ)` for `μ ≠ 0` (the `t = −μ` case is `0 = 0`). -/
theorem jd_psiWeight_eq {μ t : ℝ} (hμ : μ ≠ 0) :
    Work.SmallBoxSliding.psiWeight 1 μ t = μ * (t - μ) ^ 2 / (t + μ) := by
  rw [Work.SmallBoxSliding.psiWeight, one_mul]
  have hμ1 : 1 + t * μ⁻¹ = (t + μ) / μ := by
    rw [eq_div_iff hμ]; field_simp; ring
  rw [hμ1]
  by_cases h : t + μ = 0
  · rw [h]; simp
  · field_simp

/-- `F(f/C) = (μ/C)·(f−μC)²/(f+μC)` for `μ ≠ 0`, `C ≠ 0`. -/
theorem jd_psiWeight_div_eq {μ C f : ℝ} (hμ : μ ≠ 0) (hC : C ≠ 0) :
    Work.SmallBoxSliding.psiWeight 1 μ (f / C)
      = (μ / C) * ((f - μ * C) ^ 2 / (f + μ * C)) := by
  rw [jd_psiWeight_eq hμ]
  by_cases h : f + μ * C = 0
  · have hf : f = -μ * C := by linarith
    rw [hf]
    have hden : (-μ * C) / C + μ = 0 := by field_simp; ring
    have hden2 : -μ * C + μ * C = 0 := by ring
    rw [hden, hden2]
    simp
  · field_simp

/-- `F(0) = μ²`. -/
theorem jd_psiWeight_zero {μ : ℝ} : Work.SmallBoxSliding.psiWeight 1 μ 0 = μ ^ 2 := by
  rw [Work.SmallBoxSliding.psiWeight, one_mul, zero_sub, zero_mul, add_zero, div_one]
  ring

/-! ## 3. Continuity of the local particle count -/

/-- `x ↦ Σᵢ χ_{B(u)}(xᵢ)²` is continuous (a finite sum of squares of the smooth
two-factor cutoff `chiSmallB`). -/
theorem jd_continuous_nCountB {M : ℕ} (hM : 1 ≤ M) (ℓ d : ℝ) (u : EuclideanSpace ℝ (Fin 3))
    {n : ℕ} :
    Continuous (fun x : Submission.BoseGases.X n => Work.BoseFixB1.nCountB M ℓ d u x) := by
  simp only [Work.BoseFixB1.nCountB]
  refine continuous_finsetSum _ (fun i _ => ?_)
  simp only [Submission.BoseGases.chiSmallB]
  exact (((Submission.BoseGases.chiScale_continuous ℓ).comp
        (continuous_apply i)).mul
      ((Submission.BoseGases.chiSmall_continuous hM).comp
        (((continuous_apply i).const_smul ((ℓ * d)⁻¹)).sub continuous_const))).pow 2

/-! ## 4. The abstract core inequality -/

/-- **The core inequality** (Jensen for `F`, in Cauchy–Schwarz form).  For a measure `ν`,
`a ≥ 0`, `f ≥ 0`, `μ > 0`, `C > 0`:

  `(∫ a) · F((∫ a f)/((∫ a)·C)) ≤ ∫ a · F(f/C)`.

This is the abstract content of `jensen_dens`; the target theorem is its
instantiation at `a = Φ²`, `f = nCountB u`, `C = chiMass u`, `ν = volume|_{abox n ℓ}`. -/
theorem jd_jensen_core {α : Type*} [MeasurableSpace α] {ν : MeasureTheory.Measure α}
    {a f : α → ℝ} {μ C : ℝ}
    (hμ : 0 < μ) (hC : 0 < C) (ha : ∀ x, 0 ≤ a x) (hf : ∀ x, 0 ≤ f x)
    (hint_a : MeasureTheory.Integrable a ν)
    (hint_af : MeasureTheory.Integrable (fun x => a x * f x) ν)
    (hint_q : MeasureTheory.Integrable (fun x => a x * ((f x - μ * C) ^ 2 / (f x + μ * C))) ν) :
    (∫ x, a x ∂ν) * Work.SmallBoxSliding.psiWeight 1 μ
        ((∫ x, a x * f x ∂ν) / ((∫ x, a x ∂ν) * C))
      ≤ ∫ x, a x * Work.SmallBoxSliding.psiWeight 1 μ (f x / C) ∂ν := by
  have hμne : μ ≠ 0 := ne_of_gt hμ
  have hCne : C ≠ 0 := ne_of_gt hC
  have hp : ∀ x, 0 < f x + μ * C := fun x => by nlinarith [hf x, mul_pos hμ hC]
  set N : ℝ := ∫ x, a x ∂ν with hN
  set I : ℝ := ∫ x, a x * f x ∂ν with hI
  set K : ℝ := ∫ x, a x * ((f x - μ * C) ^ 2 / (f x + μ * C)) ∂ν with hK
  have hNnonneg : 0 ≤ N := by rw [hN]; exact integral_nonneg ha
  have hInonneg : 0 ≤ I := by
    rw [hI]; exact integral_nonneg (fun x => mul_nonneg (ha x) (hf x))
  have hKnonneg : 0 ≤ K := by
    rw [hK]
    exact integral_nonneg (fun x => mul_nonneg (ha x) (div_nonneg (sq_nonneg _) (le_of_lt (hp x))))
  -- the right-hand side equals `(μ/C)·K`
  have hRHS : (∫ x, a x * Work.SmallBoxSliding.psiWeight 1 μ (f x / C) ∂ν) = (μ / C) * K := by
    rw [hK]
    rw [show (fun x => a x * Work.SmallBoxSliding.psiWeight 1 μ (f x / C))
        = (fun x => (μ / C) * (a x * ((f x - μ * C) ^ 2 / (f x + μ * C)))) from
      funext fun x => by rw [jd_psiWeight_div_eq hμne hCne]; ring]
    rw [integral_const_mul]
  -- integrability of `a·(f ∓ μC)`
  have hin_g : MeasureTheory.Integrable (fun x => a x * (f x - μ * C)) ν := by
    have h : MeasureTheory.Integrable (fun x => a x * f x - (μ * C) * a x) ν :=
      hint_af.sub (hint_a.const_mul (μ * C))
    exact h.congr (Filter.Eventually.of_forall (fun x => by ring))
  have hin_p : MeasureTheory.Integrable (fun x => a x * (f x + μ * C)) ν := by
    have h : MeasureTheory.Integrable (fun x => a x * f x + (μ * C) * a x) ν :=
      hint_af.add (hint_a.const_mul (μ * C))
    exact h.congr (Filter.Eventually.of_forall (fun x => by ring))
  have hIg : (∫ x, a x * (f x - μ * C) ∂ν) = I - μ * C * N := by
    have e : (∫ x, a x * (f x - μ * C) ∂ν)
        = (∫ x, a x * f x ∂ν) - (μ * C) * (∫ x, a x ∂ν) := by
      rw [show (fun x => a x * (f x - μ * C)) = (fun x => a x * f x - (μ * C) * a x) from
        funext (fun x => by ring)]
      rw [integral_sub hint_af (hint_a.const_mul (μ * C)), integral_const_mul]
    rw [e, ← hI, ← hN]
  have hIp : (∫ x, a x * (f x + μ * C) ∂ν) = I + μ * C * N := by
    have e : (∫ x, a x * (f x + μ * C) ∂ν)
        = (∫ x, a x * f x ∂ν) + (μ * C) * (∫ x, a x ∂ν) := by
      rw [show (fun x => a x * (f x + μ * C)) = (fun x => a x * f x + (μ * C) * a x) from
        funext (fun x => by ring)]
      rw [integral_add hint_af (hint_a.const_mul (μ * C)), integral_const_mul]
    rw [e, ← hI, ← hN]
  have hCS : (I - μ * C * N) ^ 2 ≤ (I + μ * C * N) * K := by
    have hw := jd_weighted_cs ν (a := a) (g := fun x => f x - μ * C) (p := fun x => f x + μ * C)
      (q := fun x => (f x - μ * C) ^ 2 / (f x + μ * C)) ha hp
      (fun x => by rw [eq_comm, mul_comm]; exact div_mul_cancel₀ _ (ne_of_gt (hp x)))
      hin_g hin_p hint_q
    rw [hIg, hIp, ← hK] at hw
    exact hw
  by_cases hN0 : N = 0
  · rw [hRHS, hN0, zero_mul]
    exact mul_nonneg (div_nonneg (le_of_lt hμ) (le_of_lt hC)) hKnonneg
  · have hNpos : 0 < N := lt_of_le_of_ne hNnonneg (Ne.symm hN0)
    have hden_pos : 0 < I + μ * C * N := by nlinarith [hInonneg, mul_pos hμ hC, hNpos]
    have hLHS : N * Work.SmallBoxSliding.psiWeight 1 μ (I / (N * C))
        = μ * (I - μ * C * N) ^ 2 / (C * (I + μ * C * N)) := by
      rw [jd_psiWeight_eq hμne]
      field_simp
    rw [hLHS, hRHS]
    have h2 : (I - μ * C * N) ^ 2 / (I + μ * C * N) ≤ K := by
      rw [div_le_iff₀ hden_pos]
      nlinarith [hCS, mul_comm (I + μ * C * N) K]
    have h3 : (μ / C) * ((I - μ * C * N) ^ 2 / (I + μ * C * N)) ≤ (μ / C) * K :=
      mul_le_mul_of_nonneg_left h2 (div_nonneg (le_of_lt hμ) (le_of_lt hC))
    have h4 : μ * (I - μ * C * N) ^ 2 / (C * (I + μ * C * N))
        = (μ / C) * ((I - μ * C * N) ^ 2 / (I + μ * C * N)) := by
      field_simp
    rw [h4]
    exact h3

/-! ## 5. FS step 4 at the small-box parameters -/

theorem jensen_dens {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v} {μ : ℝ} {n : ℕ}
    (hμ : 0 < μ)
    (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))
    (u : EuclideanSpace ℝ (Fin 3)) :
    Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
        * Work.SmallBoxSliding.psiWeight 1 μ
            (Work.BoseFixB1.wbDens v h μ n (Φ : Submission.BoseGases.X n → ℝ) u)
      ≤ ∫ x in Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
          (Φ x) ^ 2 * Work.SmallBoxSliding.psiWeight 1 μ
            (Work.BoseFixB1.nCountB (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u x
              / Work.SmallBoxSliding.chiMass (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) := by
  rw [Work.BoseFixB1.wbDens, Work.BoseBoxFix.normB, Work.BoseKinLoc.sqNormB]
  have hM1 : 1 ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M := by
    rw [Work.BoseBox.paramsAt, Work.BoseBox.fsParams]
    norm_num [Work.BoseBox.mValue]
  have hCnonneg : 0 ≤ Work.SmallBoxSliding.chiMass
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
      (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u :=
    Work.SmallBoxSliding.chiMass_nonneg _ _ _ _
  by_cases hC0 : Work.SmallBoxSliding.chiMass
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
      (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u = 0
  · -- degenerate case `chiMass = 0`: both sides are `‖Φ‖²·F(0) = ‖Φ‖²·μ²`
    rw [hC0]
    simp only [mul_zero, div_zero, jd_psiWeight_zero]
    rw [integral_mul_const (μ ^ 2)]
  · have hCpos : 0 < Work.SmallBoxSliding.chiMass
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
        (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u :=
      lt_of_le_of_ne hCnonneg (Ne.symm hC0)
    refine jd_jensen_core
      (ν := volume.restrict
        (Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))))
      (a := fun x : Submission.BoseGases.X n => (Φ : Submission.BoseGases.X n → ℝ) x ^ 2)
      (f := fun x : Submission.BoseGases.X n => Work.BoseFixB1.nCountB
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
        (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u x)
      (C := Work.SmallBoxSliding.chiMass
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
        (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
      hμ hCpos ?_ ?_ ?_ ?_ ?_
    · intro x
      exact sq_nonneg _
    · intro x
      simp only [Work.BoseFixB1.nCountB]
      exact Finset.sum_nonneg (fun i _ => sq_nonneg _)
    · exact Work.UBBInputs9.B.integrableOn_abox_of_continuous'
        ((Φ.contDiff.continuous).pow 2)
    · have hcontF : Continuous (fun x : Submission.BoseGases.X n => Work.BoseFixB1.nCountB
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
          (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u x) :=
        jd_continuous_nCountB hM1 _ _ u
      exact Work.UBBInputs9.B.integrableOn_abox_of_continuous'
        (((Φ.contDiff.continuous).pow 2).mul hcontF)
    · have hcontF : Continuous (fun x : Submission.BoseGases.X n => Work.BoseFixB1.nCountB
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
          (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u x) :=
        jd_continuous_nCountB hM1 _ _ u
      have hpos : ∀ x : Submission.BoseGases.X n, 0 < Work.BoseFixB1.nCountB
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
          (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u x +
            μ * Work.SmallBoxSliding.chiMass
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
              (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u := by
        intro x
        have hx : 0 ≤ Work.BoseFixB1.nCountB
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
            (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u x := by
          simp only [Work.BoseFixB1.nCountB]
          exact Finset.sum_nonneg (fun i _ => sq_nonneg _)
        nlinarith [hx, mul_pos hμ hCpos]
      refine Work.UBBInputs9.B.integrableOn_abox_of_continuous'
        (((Φ.contDiff.continuous).pow 2).mul ?_)
      exact ((hcontF.sub continuous_const).pow 2).div (hcontF.add continuous_const)
        (fun x => ne_of_gt (hpos x))

end Work.BoseFixB1.WB
