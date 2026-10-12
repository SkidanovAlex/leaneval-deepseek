import ChallengeDeps
import Submission.Work.MGroupInput.Residual
import Submission.Work.MGroupInput.arithSimpleA2Two
import Submission.Work.MGroupInput.newtonianSharp
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.MGroupInput

theorem perState_of_simpleA2Two {P : ℕ} {s μ c₀ cgap E₁ E₂ : ℝ}
    {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R : ℝ} (hR : 0 < R) (hv_nonneg : 0 ≤ v)
    (hvrad : BoseGases.IsRadial v) (hv_memL1 : MeasureTheory.MemLp v 1)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (h : ∃ w : EuclideanSpace ℝ (Fin 3) → ℝ,
      BoseGases.IsRadial w ∧ BoseGases.IsScatteringSolution w v)
    (hRs : R ≤ s * Submission.BoseGases.chiR0) (hav : 0 < BoseGases.a v)
    (hs : 0 < s) (hμ : 0 < μ) (hμs : 20 ≤ μ * s ^ 3)
    (hcgap : 0 ≤ cgap)
    (hD : Submission.BoseGases.g0w0Mass (v := v) h ≤ 8 * Real.pi * (BoseGases.a v))
    (hE₁ : 0 ≤ E₁) (hP : 1 ≤ P) (hwin : (P : ℝ) / s ^ 3 ≤ 9 * μ)
    (hCn : 8 * μ + E₁ ≤ (P : ℝ) / s ^ 3)
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
  -- (1) the pure-real `m`-arm arithmetic (the split constants `E₁`/`E₂`)
  have harith := Work.MGroupInput.arithSimpleA2Two (P := n + 1)
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
