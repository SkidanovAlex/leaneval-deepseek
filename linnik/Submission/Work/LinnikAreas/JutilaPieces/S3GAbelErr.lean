import Mathlib
import Submission.Work.ZeroDensity.Jutila.S3GSharpDefs
import Submission.Work.LinnikAreas.JutilaPieces.S3G_weight_increment_bound
import Submission.Work.LinnikAreas.JutilaPieces.S3GWfunPointwise

namespace Work.LinnikAreas.JutilaPieces

open Finset

/-- **Sharp Abel error term of the `S₃` assembly** (re-homing of
`Work.ZeroDensity.Jutila.S3GAbelErr`, importable from here).  With
`Δ(M) = s3Delta c M = s3Count c M − s3c c·M` (the discrepancy of the count of the squarefree
integers coprime to `c` from its density `s3c c = ζ(2)⁻¹∏_{p|c}p/(p+1)`), `s3Sig c = Σ_{d|c}d^{-1/2}`
and `wfun α β m = (log m − α)(log m − β)`, the Abel-summation combination

  `Δ(X)·wfun α β X + Σ_{m≤X−1} (wfun α β m − wfun α β (m+1))·Δ(m)`

is `O(s3Sig c · √X · (1+|log(2X)−α|)·(1+|log(2X)−β|))`.

**Route — this exact claim is already proved, just not exportable.**  The same statement appears as
the `private` lemma `abel_error_sharp_local` in
`Submission/Work/ZeroDensity/Jutila/S3GAbelSharp.lean` (around line 760), discharged there from the
discrepancy bound `s3Delta_bound` of `Work/ZeroDensity/Jutila/S3GSharpDefs` (imported here).  Since
`private` lemmas cannot be referenced across modules, the task is to **transcribe that proof here**
(reading `S3GAbelSharp.lean` for the exact argument) and to re-derive or import the small helper
bounds it uses (`wfun_abs_le`, `wfun_diff_le`, the `Σ m^{-1/2}` and `log`-comparison bounds — the
last of these are the five inequalities of `Work.LinnikAreas.JutilaPieces.S3GSumBounds`).
Mathematically this is Abel/partial summation: the bracketed combination is
`Σ_{m≤X} w_m(Δ(m) − Δ(m−1))` with `Δ(0) = 0`, i.e. the error after removing the main term
`s3c c·Σ w_m`; bound term 1 by `Cσ√X·|w_X|`, term 2 by `Cσ√m·|w_m − w_{m+1}|` with
`|w_m − w_{m+1}| ≪ (1+|L−α|)(1+|L−β|)/m`, `L = log(2X)`, and sum `Σ_{m≤X} m^{-1/2} ≪ √X`. -/
theorem S3GAbelErr :
    ∃ K : ℝ, 0 < K ∧ ∀ (c X : ℕ) (α β : ℝ),
      1 ≤ c → 2 ≤ X → 0 ≤ α → 0 ≤ β →
      |Work.ZeroDensity.Jutila.s3Delta c X * Work.LinnikAreas.Density4.BzS3.wfun α β X
        + ∑ m ∈ Finset.Icc 1 (X - 1),
            (Work.LinnikAreas.Density4.BzS3.wfun α β m
                - Work.LinnikAreas.Density4.BzS3.wfun α β (m + 1))
              * Work.ZeroDensity.Jutila.s3Delta c m|
      ≤ K * Work.ZeroDensity.Jutila.s3Sig c * Real.sqrt (X : ℝ)
          * (1 + |Real.log (2 * (X : ℝ)) - α|) * (1 + |Real.log (2 * (X : ℝ)) - β|) := by
  obtain ⟨C₀, hC₀pos, hDelta⟩ := Work.ZeroDensity.Jutila.s3Delta_bound
  obtain ⟨Cw, hCwpos, hW⟩ := S3G_weight_increment_bound
  refine ⟨(4 + Cw) * C₀, by positivity, ?_⟩
  intro c X α β hc hX hα hβ
  have hX1 : 1 ≤ X := by omega
  -- the discrepancy bound at `m` (for `m ≥ 1`)
  have hcnt : ∀ m : ℕ, 1 ≤ m →
      |Work.ZeroDensity.Jutila.s3Delta c m|
        ≤ C₀ * Work.ZeroDensity.Jutila.s3Sig c * Real.sqrt (m : ℝ) :=
    fun m hm => hDelta c m hc hm
  have hsgnn : (0 : ℝ) ≤ Work.ZeroDensity.Jutila.s3Sig c :=
    Work.ZeroDensity.Jutila.s3Sig_nonneg c
  have hC₀nn : (0 : ℝ) ≤ C₀ := le_of_lt hC₀pos
  have hsXnn : (0 : ℝ) ≤ Real.sqrt (X : ℝ) := Real.sqrt_nonneg _
  -- ## term 1: the boundary term `Δ(X)·w(X)`
  have ht1 : |Work.ZeroDensity.Jutila.s3Delta c X * Work.LinnikAreas.Density4.BzS3.wfun α β X|
      ≤ C₀ * Work.ZeroDensity.Jutila.s3Sig c * Real.sqrt (X : ℝ)
          * (4 * (1 + |Real.log (2 * (X : ℝ)) - α|)
              * (1 + |Real.log (2 * (X : ℝ)) - β|)) := by
    rw [abs_mul]
    exact mul_le_mul (hcnt X hX1) (S3GWfunPointwise.2.1 X α β) (abs_nonneg _)
      (by positivity)
  -- ## the weight-increment sum, in the orientation of the `S₃` weight-increment bound
  have hWsum : (∑ m ∈ Finset.Icc 1 (X - 1),
        |Work.LinnikAreas.Density4.BzS3.wfun α β m
            - Work.LinnikAreas.Density4.BzS3.wfun α β (m + 1)| * Real.sqrt (m : ℝ))
      ≤ Cw * Real.sqrt (X : ℝ) * (1 + |Real.log (2 * (X : ℝ)) - α|)
          * (1 + |Real.log (2 * (X : ℝ)) - β|) := by
    have hstep : (∑ m ∈ Finset.Icc 1 (X - 1),
          |Work.LinnikAreas.Density4.BzS3.wfun α β m
              - Work.LinnikAreas.Density4.BzS3.wfun α β (m + 1)| * Real.sqrt (m : ℝ))
        = ∑ m ∈ Finset.Icc 1 (X - 1),
          |Work.LinnikAreas.Density4.BzS3.wfun α β (m + 1)
              - Work.LinnikAreas.Density4.BzS3.wfun α β m| * Real.sqrt (m : ℝ) := by
      apply Finset.sum_congr rfl
      intro m _
      rw [abs_sub_comm]
    rw [hstep]
    simpa only [Work.LinnikAreas.Density4.BzS3.wfun] using hW X α β hX hα hβ
  -- ## term 2: the Abel sum, via `|Δ(m)| ≤ C₀σ√m`
  have hterm : ∀ m ∈ Finset.Icc 1 (X - 1),
      |(Work.LinnikAreas.Density4.BzS3.wfun α β m
          - Work.LinnikAreas.Density4.BzS3.wfun α β (m + 1))
          * Work.ZeroDensity.Jutila.s3Delta c m|
        ≤ |Work.LinnikAreas.Density4.BzS3.wfun α β m
            - Work.LinnikAreas.Density4.BzS3.wfun α β (m + 1)|
          * (C₀ * Work.ZeroDensity.Jutila.s3Sig c * Real.sqrt (m : ℝ)) := by
    intro m hm
    obtain ⟨hm1, _⟩ := Finset.mem_Icc.mp hm
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hcnt m hm1) (abs_nonneg _)
  have ht2 : |∑ m ∈ Finset.Icc 1 (X - 1),
        (Work.LinnikAreas.Density4.BzS3.wfun α β m
            - Work.LinnikAreas.Density4.BzS3.wfun α β (m + 1))
          * Work.ZeroDensity.Jutila.s3Delta c m|
      ≤ C₀ * Work.ZeroDensity.Jutila.s3Sig c
          * (Cw * Real.sqrt (X : ℝ) * (1 + |Real.log (2 * (X : ℝ)) - α|)
              * (1 + |Real.log (2 * (X : ℝ)) - β|)) := by
    calc |∑ m ∈ Finset.Icc 1 (X - 1),
          (Work.LinnikAreas.Density4.BzS3.wfun α β m
              - Work.LinnikAreas.Density4.BzS3.wfun α β (m + 1))
            * Work.ZeroDensity.Jutila.s3Delta c m|
        ≤ ∑ m ∈ Finset.Icc 1 (X - 1),
            |(Work.LinnikAreas.Density4.BzS3.wfun α β m
                - Work.LinnikAreas.Density4.BzS3.wfun α β (m + 1))
              * Work.ZeroDensity.Jutila.s3Delta c m| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ m ∈ Finset.Icc 1 (X - 1),
            |Work.LinnikAreas.Density4.BzS3.wfun α β m
                - Work.LinnikAreas.Density4.BzS3.wfun α β (m + 1)|
              * (C₀ * Work.ZeroDensity.Jutila.s3Sig c * Real.sqrt (m : ℝ)) :=
          Finset.sum_le_sum hterm
      _ = C₀ * Work.ZeroDensity.Jutila.s3Sig c
            * ∑ m ∈ Finset.Icc 1 (X - 1),
                |Work.LinnikAreas.Density4.BzS3.wfun α β m
                    - Work.LinnikAreas.Density4.BzS3.wfun α β (m + 1)|
                  * Real.sqrt (m : ℝ) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro m _
          ring
      _ ≤ C₀ * Work.ZeroDensity.Jutila.s3Sig c
            * (Cw * Real.sqrt (X : ℝ) * (1 + |Real.log (2 * (X : ℝ)) - α|)
                * (1 + |Real.log (2 * (X : ℝ)) - β|)) :=
          mul_le_mul_of_nonneg_left hWsum (mul_nonneg hC₀nn hsgnn)
  -- ## bookkeeping
  have hfin : C₀ * Work.ZeroDensity.Jutila.s3Sig c * Real.sqrt (X : ℝ)
        * (4 * (1 + |Real.log (2 * (X : ℝ)) - α|)
            * (1 + |Real.log (2 * (X : ℝ)) - β|))
      + C₀ * Work.ZeroDensity.Jutila.s3Sig c
        * (Cw * Real.sqrt (X : ℝ) * (1 + |Real.log (2 * (X : ℝ)) - α|)
            * (1 + |Real.log (2 * (X : ℝ)) - β|))
      ≤ ((4 + Cw) * C₀) * Work.ZeroDensity.Jutila.s3Sig c * Real.sqrt (X : ℝ)
          * (1 + |Real.log (2 * (X : ℝ)) - α|) * (1 + |Real.log (2 * (X : ℝ)) - β|) :=
    le_of_eq (by ring)
  calc |Work.ZeroDensity.Jutila.s3Delta c X * Work.LinnikAreas.Density4.BzS3.wfun α β X
        + ∑ m ∈ Finset.Icc 1 (X - 1),
            (Work.LinnikAreas.Density4.BzS3.wfun α β m
                - Work.LinnikAreas.Density4.BzS3.wfun α β (m + 1))
              * Work.ZeroDensity.Jutila.s3Delta c m|
      ≤ |Work.ZeroDensity.Jutila.s3Delta c X * Work.LinnikAreas.Density4.BzS3.wfun α β X|
        + |∑ m ∈ Finset.Icc 1 (X - 1),
            (Work.LinnikAreas.Density4.BzS3.wfun α β m
                - Work.LinnikAreas.Density4.BzS3.wfun α β (m + 1))
              * Work.ZeroDensity.Jutila.s3Delta c m| := abs_add_le _ _
    _ ≤ C₀ * Work.ZeroDensity.Jutila.s3Sig c * Real.sqrt (X : ℝ)
          * (4 * (1 + |Real.log (2 * (X : ℝ)) - α|)
              * (1 + |Real.log (2 * (X : ℝ)) - β|))
        + C₀ * Work.ZeroDensity.Jutila.s3Sig c
            * (Cw * Real.sqrt (X : ℝ) * (1 + |Real.log (2 * (X : ℝ)) - α|)
                * (1 + |Real.log (2 * (X : ℝ)) - β|)) := add_le_add ht1 ht2
    _ ≤ ((4 + Cw) * C₀) * Work.ZeroDensity.Jutila.s3Sig c * Real.sqrt (X : ℝ)
          * (1 + |Real.log (2 * (X : ℝ)) - α|) * (1 + |Real.log (2 * (X : ℝ)) - β|) := hfin

end Work.LinnikAreas.JutilaPieces
