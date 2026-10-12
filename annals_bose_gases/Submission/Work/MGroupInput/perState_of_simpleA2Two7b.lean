import ChallengeDeps
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Submission.Work.MGroupInput.perState_of_simpleA2Two
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.MGroupInput

/-! ## The `w ≥ 10` arithmetic certificate

`arithSimpleA2Two7` proves the per-state arithmetic core under the `μ s³ ≥ 40`
regime.  Here we sharpen the regime to the tight integer threshold `μ s³ ≥ 10`,
which is what `perState_of_simpleA2Two7b` needs.

The polynomial certificate is the same one, but with the slack variable
`Y = w - 10` in place of `Y = w - 40`: both `C` and `3.14 C + D` are
polynomials in `X = x - 7w ≥ 0`, `Y = w - 10 ≥ 0` with nonnegative
coefficients. -/

/-- Arithmetic core of the `7μ`-window variant of the per-state assembly, at the
tight regime `μ s³ ≥ 10`.

With `x := P`, `w := μ s³` the claim is: under `w ≥ 10` and `7w ≤ x ≤ 9w`,

`(1/9)(x−w)² 8π ≤ (1/4)(x−w)² 8π − 4π w² + 4π(x+1)(1−x/20) − (1/40)x(x+1)
   − (x−7w)x − 272π w`.

The difference of the two sides equals `π C + D` with

* `C = (10/9)(x-w)^2 - 4w^2 + 4(x+1)(1 - x/20) - 272w`,
* `D = -(1/40)x(x+1) - (x-7w)x`.

Both `C` and `3.14 C + D` are polynomials in `X = x - 7w ≥ 0` and `Y = w - 10 ≥ 0`
with nonnegative coefficients; hence `C ≥ 0` and, since `π ≥ 3.14`,
`π C + D ≥ 3.14 C + D ≥ 0`. -/
lemma arithSimpleA2Two7bQuad {x w : ℝ} (hw : 10 ≤ w) (hl : 7 * w ≤ x) (hu : x ≤ 9 * w) :
    (1 / 9) * (x - w) ^ 2 * (8 * Real.pi)
      ≤ (1 / 4) * (x - w) ^ 2 * (8 * Real.pi) - 4 * Real.pi * w ^ 2
        + 4 * Real.pi * (x + 1) * (1 - x / 20)
        - (1 / 40) * x * (x + 1) - (x - 7 * w) * x - 272 * Real.pi * w := by
  have hπ : (3.14 : ℝ) < Real.pi := Real.pi_gt_d2
  have hX : 0 ≤ x - 7 * w := by linarith
  have hY : 0 ≤ w - 10 := by linarith
  have hC : 0 ≤ (10 / 9 : ℝ) * (x - w) ^ 2 - 4 * w ^ 2
      + 4 * (x + 1) * (1 - x / 20) - 272 * w := by
    nlinarith [sq_nonneg (x - 7 * w), sq_nonneg (w - 10), mul_nonneg hX hY]
  have hF : 0 ≤ (3.14 : ℝ) * ((10 / 9 : ℝ) * (x - w) ^ 2 - 4 * w ^ 2
        + 4 * (x + 1) * (1 - x / 20) - 272 * w)
      - (1 / 40) * x * (x + 1) - (x - 7 * w) * x := by
    nlinarith [sq_nonneg (x - 7 * w), sq_nonneg (w - 10), mul_nonneg hX hY]
  have hπC := mul_le_mul_of_nonneg_right hπ.le hC
  nlinarith [hπC, hF, hu]

/-- The `10`-regime version of `Work.MGroupInput.arithSimpleA2Two7`: the same
arithmetic core, from `μ s³ ≥ 10` (instead of `40`). -/
theorem arithSimpleA2Two7b {P : ℕ} {s μ av D E₁ : ℝ} (hs : 0 < s) (hμ : 0 < μ)
    (hav : 0 < av) (hD0 : 0 ≤ D) (hD1 : D ≤ 8 * Real.pi * av) (hE₁ : 0 ≤ E₁)
    (hP : 1 ≤ P) (hμs : 10 ≤ μ * s ^ 3) (hwin : (P : ℝ) / s ^ 3 ≤ 9 * μ)
    (hCn : 7 * μ + E₁ ≤ (P : ℝ) / s ^ 3) :
    (1 / 9) * (μ - (P : ℝ) / s ^ 3) ^ 2 * (8 * Real.pi * av * s ^ 3)
      ≤ (1 / 4) * ((P : ℝ) / s ^ 3 - μ) ^ 2 * (8 * Real.pi * av * s ^ 3)
        - (1 / 2) * μ ^ 2 * (8 * Real.pi * av * s ^ 3)
        + (1 / 2) * D * (((P : ℝ) + 1) ^ 2) * (s ^ 3)⁻¹
        - (1 / 2) * ((1 + 1 / 20) * D + (1 / 20) * av)
            * ((((P : ℝ) + 1) * (P : ℝ)) * (s ^ 3)⁻¹)
        - E₁ * av * (P : ℝ) - 272 * Real.pi * av * μ := by
  set V : ℝ := s ^ 3 with hVdef
  set x : ℝ := (P : ℝ) with hxdef
  set w : ℝ := μ * V with hwdef
  have hVpos : 0 < V := by rw [hVdef]; positivity
  have hx0 : 0 ≤ x := by rw [hxdef]; positivity
  have hw10 : 10 ≤ w := by rw [hwdef]; exact hμs
  -- Rewrite the window hypotheses after multiplying by `V > 0`.
  have h1 : (7 * μ + E₁) * V ≤ x := (le_div_iff₀ hVpos).mp hCn
  have h2 : x ≤ 9 * μ * V := (div_le_iff₀ hVpos).mp hwin
  have hE1Vnn : 0 ≤ E₁ * V := mul_nonneg hE₁ (le_of_lt hVpos)
  have h7w : 7 * w ≤ x := by rw [hwdef]; nlinarith [h1, hE1Vnn]
  have hxup : x ≤ 9 * w := by rw [hwdef]; nlinarith [h2]
  have hx20 : 20 ≤ x := by nlinarith [h7w, hw10]
  have hE1V : E₁ * V ≤ x - 7 * (μ * V) := by nlinarith [h1]
  -- The polynomial core in `x = P` and `w = μ V`.
  have hkey := arithSimpleA2Two7bQuad hw10 h7w hxup
  rw [hwdef] at hkey
  -- The `D`-slot bound.
  have hDbound := arithSimpleA2TwoDslot hav hVpos hD0 hD1 hx20
  -- The `E₁`-slot bound.
  have hEslot : E₁ * av * x ≤ ((x - 7 * (μ * V)) * x) * (av * V⁻¹) := by
    have h3 : E₁ * V * x ≤ (x - 7 * (μ * V)) * x := mul_le_mul_of_nonneg_right hE1V hx0
    have hnn : 0 ≤ av * V⁻¹ := by positivity
    have h4 := mul_le_mul_of_nonneg_right h3 hnn
    have h5 : (E₁ * V * x) * (av * V⁻¹) = E₁ * av * x := by field_simp
    linarith [h4, h5]
  have hnn : 0 ≤ av * V⁻¹ := by positivity
  -- Assemble: multiply the target by `V/av` (up to the notation `⁻¹`).
  have hscale : (1 / 9) * (x - μ * V) ^ 2 * (8 * Real.pi) * (av * V⁻¹)
      ≤ ((1 / 4) * (x * V⁻¹ - μ) ^ 2 * (8 * Real.pi * av * V)
          - (1 / 2) * μ ^ 2 * (8 * Real.pi * av * V))
        + ((1 / 2) * D * (x + 1) ^ 2 * V⁻¹
          - (1 / 2) * ((1 + 1 / 20) * D + (1 / 20) * av) * ((x + 1) * x * V⁻¹))
        + (- E₁ * av * x) + (- 272 * Real.pi * av * μ) := by
    have hk := mul_le_mul_of_nonneg_right hkey hnn
    have hC1 : ((1 / 4) * (x - μ * V) ^ 2 * (8 * Real.pi) - 4 * Real.pi * (μ * V) ^ 2) * (av * V⁻¹)
        = (1 / 4) * (x * V⁻¹ - μ) ^ 2 * (8 * Real.pi * av * V)
          - (1 / 2) * μ ^ 2 * (8 * Real.pi * av * V) := by
      field_simp; ring
    have hT6 : (- 272 * Real.pi * (μ * V)) * (av * V⁻¹) = - 272 * Real.pi * av * μ := by
      field_simp
    nlinarith [hk, hC1, hDbound, hEslot, hT6]
  have hA : (1 / 9) * (μ - x / V) ^ 2 * (8 * Real.pi * av * V)
      = (1 / 9) * (x - μ * V) ^ 2 * (8 * Real.pi) * (av * V⁻¹) := by
    field_simp
    ring
  rw [hA]
  convert hscale using 1; ring

theorem perState_of_simpleA2Two7b {P : ℕ} {s μ c₀ cgap E₁ E₂ : ℝ}
    {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R : ℝ} (hR : 0 < R) (hv_nonneg : 0 ≤ v)
    (hvrad : BoseGases.IsRadial v) (hv_memL1 : MeasureTheory.MemLp v 1)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (h : ∃ w : EuclideanSpace ℝ (Fin 3) → ℝ,
      BoseGases.IsRadial w ∧ BoseGases.IsScatteringSolution w v)
    (hRs : R ≤ s * Submission.BoseGases.chiR0) (hav : 0 < BoseGases.a v)
    (hs : 0 < s) (hμ : 0 < μ) (hμs : 10 ≤ μ * s ^ 3)
    (hcgap : 0 ≤ cgap)
    (hD : Submission.BoseGases.g0w0Mass (v := v) h ≤ 8 * Real.pi * (BoseGases.a v))
    (hE₁ : 0 ≤ E₁) (hP : 1 ≤ P) (hwin : (P : ℝ) / s ^ 3 ≤ 9 * μ)
    (hCn : 7 * μ + E₁ ≤ (P : ℝ) / s ^ 3)
    (hA2 : Work.MGroupInput.SimpleA2Two E₁ E₂ s c₀ v h)
    (hab : Work.SmallBoxA0.totNCoeff s μ v + E₂ * (BoseGases.a v) * (((P : ℝ) + 1) / s ^ 3) ≤ cgap)
    (Φ : Submission.BoseGases.X P → ℝ) (hΦc : ContDiff ℝ (⊤ : ℕ∞) Φ)
    (hnorm : (∫ x in Submission.BoseGases.abox P s, (Φ x) ^ 2) = 1)
    (hSc1 : 0 < Submission.BoseGases.cS1 s Φ)
    (hcorr : 2 * (s ^ 3)⁻¹ * Work.SmallBoxA0.CorrWord s h Φ
      ≤ (1 / (72 * s ^ 2)) * Submission.BoseGases.cnPlus s Φ + 36 * Real.pi * (BoseGases.a v) * μ) :
    (1 / 9) * (μ - (P : ℝ) / s ^ 3) ^ 2 * (8 * Real.pi * (BoseGases.a v) * s ^ 3)
      ≤ Work.KinPSuperadd.blockE s μ (Submission.BoseGases.wPairC s v)
          (Submission.BoseGases.wPairC s (Submission.BoseGases.g0 v h))
          (Work.KinPSuperadd.diagSlotWord s c₀ cgap) P Φ := by
  -- `P ≥ 1`, so write `P = n + 1`: the simple Bogoliubov payment `SimpleA2Two`
  -- is stated on `X (N+1)`, and this puts the very state `Φ` in its range.
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero (by omega : P ≠ 0)
  have hnn : (0 : ℝ) ≤ Submission.BoseGases.cnPlus s Φ := Submission.BoseGases.cnPlus_nonneg
  have hDnn : (0 : ℝ) ≤ Submission.BoseGases.g0w0Mass (v := v) h :=
    Submission.BoseGases.g0w0Mass_nonneg (v := v) (R := R) hR hv_nonneg hvrad hv_supp h
  -- ---------- the corpus chain, at `n+1` particles ----------
  -- (1) the pure-real `m`-arm arithmetic (the split constants `E₁`/`E₂`),
  --     with the relaxed window `7μ + E₁ ≤ u` at `μ s³ ≥ 10`
  have harith := Work.MGroupInput.arithSimpleA2Two7b (P := n + 1)
    (av := BoseGases.a v) (D := Submission.BoseGases.g0w0Mass (v := v) h) (E₁ := E₁)
    hs hμ hav hDnn hD hE₁ hP hμs hwin hCn
  -- (2) `lm:appinteractionestimate` (`A₀` + the `A₂` pairing + the residues)
  have hA0 := Work.SmallBoxA0.pot_sharp_summary (N := n + 1) (ℓ := s) (μ := μ)
    (v := v) (R := R) hs hμ hv_nonneg hvrad hv_memL1 hR hv_supp h hRs
    hΦc.continuous hnorm hwin hSc1
  -- (3) the `cS2`-square cancellation (the `ĝω(0)`-mass slack)
  have hDsq := Work.SmallBoxA0.DSquare_cancellation' (N := n + 1) (ℓ := s) (μ := μ)
    (R := R) (v := v) (Nat.succ_le_succ (Nat.zero_le n)) hs hμ hR hv_nonneg hvrad
    hv_supp h hΦc.continuous hnorm hwin hD
  -- (4) the Corr residue bound, in the summed form of the summary
  have hcorr' : 2 * (s ^ 3)⁻¹ *
        (∑ i : Fin (n + 1), ∫ x in Submission.BoseGases.abox (n + 1) s,
          Submission.BoseGases.aP s i Φ x *
            Submission.BoseGases.w1Fibre s
              (Submission.BoseGases.wPairC s (Submission.BoseGases.g0 v h)) (x i) *
            (∑ k : Fin (n + 1), Submission.BoseGases.aQ s k (Submission.BoseGases.aQ s i Φ) x))
      ≤ (1 / (72 * s ^ 2)) * Submission.BoseGases.cnPlus s Φ
        + 36 * Real.pi * (BoseGases.a v) * μ := by
    simpa only [Work.SmallBoxA0.CorrWord] using hcorr
  -- (5) the simple Bogoliubov payment at the very state `Φ` (with `N = n`)
  have hA2' := hA2 n Φ hΦc hnorm
  unfold Work.BlockBound4.d4MassCoeff at hA2'
  -- normalise all the `↑(n+1)`-casts to the canonical shape `↑n + 1`
  simp only [Nat.cast_add, Nat.cast_one] at *
  -- ---------- the `n₊`-coefficient bookkeeping ----------
  -- `totNCoeff = potNCoeff + 72π(av)μ + 1/(72s²)`, expanded against `n₊`
  have htot : Work.SmallBoxA0.totNCoeff s μ v * Submission.BoseGases.cnPlus s Φ
      = Work.SmallBoxA0.potNCoeff μ (BoseGases.a v) * Submission.BoseGases.cnPlus s Φ
        + 72 * Real.pi * (BoseGases.a v) * μ * Submission.BoseGases.cnPlus s Φ
        + (1 / (72 * s ^ 2)) * Submission.BoseGases.cnPlus s Φ := by
    rw [Work.SmallBoxA0.totNCoeff]; ring
  -- hypothesis `hab` in the shape of the payment's `n₊`-coefficient
  have hhab : Work.SmallBoxA0.totNCoeff s μ v
      + E₂ * (BoseGases.a v) * (((n : ℝ) + 2) / s ^ 3) ≤ cgap := by
    have hcast : (((n : ℝ) + 2) / s ^ 3) = ((((n : ℝ) + 1) + 1) / s ^ 3) := by ring
    rw [hcast]
    exact hab
  have hX : 0 ≤ cgap - Work.SmallBoxA0.totNCoeff s μ v
      - E₂ * (BoseGases.a v) * (((n : ℝ) + 2) / s ^ 3) := by linarith
  -- the whole `n₊`-group is nonnegative, hence may be dropped
  have hnslack : (0 : ℝ) ≤ cgap * Submission.BoseGases.cnPlus s Φ
      - Work.SmallBoxA0.potNCoeff μ (BoseGases.a v) * Submission.BoseGases.cnPlus s Φ
      - 72 * Real.pi * (BoseGases.a v) * μ * Submission.BoseGases.cnPlus s Φ
      - (1 / (72 * s ^ 2)) * Submission.BoseGases.cnPlus s Φ
      - E₂ * (BoseGases.a v) * (((n : ℝ) + 2) / s ^ 3) * Submission.BoseGases.cnPlus s Φ := by
    have h1 : (0 : ℝ) ≤ (cgap - Work.SmallBoxA0.totNCoeff s μ v
        - E₂ * (BoseGases.a v) * (((n : ℝ) + 2) / s ^ 3)) * Submission.BoseGases.cnPlus s Φ :=
      mul_nonneg hX hnn
    have h2 : (cgap - Work.SmallBoxA0.totNCoeff s μ v
          - E₂ * (BoseGases.a v) * (((n : ℝ) + 2) / s ^ 3)) * Submission.BoseGases.cnPlus s Φ
        = cgap * Submission.BoseGases.cnPlus s Φ
          - Work.SmallBoxA0.totNCoeff s μ v * Submission.BoseGases.cnPlus s Φ
          - E₂ * (BoseGases.a v) * (((n : ℝ) + 2) / s ^ 3)
              * Submission.BoseGases.cnPlus s Φ := by ring
    rw [h2] at h1
    rw [htot] at h1
    linarith [h1]
  -- ---------- the assembly ----------
  rw [Work.KinPSuperadd.blockE_eq]
  simp only [Work.KinPSuperadd.diagSlotWord]
  linarith [hA0, hDsq, hA2', hcorr', harith, hnslack]

end Work.MGroupInput
