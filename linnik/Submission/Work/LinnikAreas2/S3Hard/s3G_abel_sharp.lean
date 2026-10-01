import Mathlib
import Submission.Work.LinnikAreas.Density4.BzS3.S3InnerDefs
import Submission.Work.LinnikAreas.Density4.BzS3.S3GAuxDefs
import Submission.Work.LinnikAreas.Density4.BzBilin.sqfree_weighted_abel
import Submission.Work.ZeroDensity.Jutila.S3GSharpDefs
import Submission.Work.LinnikAreas.JutilaPieces.S3GSmoothSharp
import Submission.Work.LinnikAreas.JutilaPieces.S3GAbelErr
import Submission.Work.LinnikAreas.Density4.BzS3.sqfree_coprime_count_main

namespace Work.LinnikAreas2.S3Hard

open Finset

open Work.LinnikAreas.Density4.BzS3

open Work.ZeroDensity.Jutila (s3Delta s3Sig s3Count s3Count_eq_sum_ite s3Sig_one_le s3Sig_nonneg)

noncomputable section

/-!
## Aim of this file

We prove `s3G_abel_sharp`.  The estimate is an *assembly of two Abel summations*, and the two
halves are available as proved, sorry-free lemmas in the workspace:

* `Work.LinnikAreas.JutilaPieces.S3GSmoothSharp` bounds the *unweighted* weight sum against its
  main term in exactly the sharp shape `K*sqrt X*(1+|log(2X)-a|)*(1+|log(2X)-b|)`;
* `Work.LinnikAreas.JutilaPieces.S3GAbelErr` bounds the Abel sum of the *count discrepancy*
  `s3Delta c m = sum_{k <= m, (k,c)=1} mu^2(k) - s3c c*m` against the weight increments, again in
  the sharp shape `K*sigma_{-1/2}(c)*sqrt X*(1+|log(2X)-a|)*(1+|log(2X)-b|)`
  (it is proved from `sqfree_coprime_count_main`).

What this file contributes is (i) the weight-indicator form of the sum, (ii) the two-weight Abel
identity `s3G - s3c*(sum_m wfun m) = Delta X * wfun X + sum_{m<X}(wfun m - wfun (m+1))*Delta m`
(`s3G_sub_s3main_decomp` below), and (iii) the final bookkeeping using `s3c c <= 1` and
`sigma_{-1/2}(c) >= 1`.
-/

/-- `s3G` is the Abel product of the weight `wfun α β` against the indicator `sqfreeCop c`
(of the squarefree integers coprime to `c`). -/
lemma s3G_eq_weighted_sum (c : ℕ) (α β : ℝ) (X : ℕ) :
    s3G c α β X = ∑ m ∈ Finset.Icc 1 X, wfun α β m * sqfreeCop c m := by
  unfold s3G
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [wfun]
  by_cases h1 : Nat.Coprime m c
  · by_cases h2 : Squarefree m
    · rw [if_pos ⟨h1, h2⟩, sqfreeCop_eq_ite, if_pos h1, moebius_sq_eq_indicator, if_pos h2]
      ring
    · rw [if_neg (fun h => h2 h.2), sqfreeCop_eq_ite, if_pos h1, moebius_sq_eq_indicator,
        if_neg h2]
      ring
  · rw [if_neg (fun h => h1 h.1), sqfreeCop_eq_ite, if_neg h1]
    ring

/-- The finite sum of the squarefree-coprime indicator is the counting function `s3Count`. -/
lemma sum_sqfreeCop_eq_s3Count (c m : ℕ) :
    (∑ k ∈ Finset.Icc 1 m, sqfreeCop c k) = s3Count c m := by
  rw [s3Count_eq_sum_ite]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  by_cases h : Nat.Coprime k c <;> simp [sqfreeCop_eq_ite, h]

/-- **Two-weight Abel decomposition of `s3G - s3main`.**  Subtracting the density `s3c c` times
the plain weight sum and splitting `s3main = s3c c*X*Omega` off leaves exactly the Abel sum of the
count discrepancy `s3Delta c`:

`Σ_{m ≤ X} wfun m*sqfreeCop c m − s3c c*X*Ω
   = s3c c*(Σ_{m ≤ X} wfun m − X*Ω) + (Δ(X)*wfun X + Σ_{m<X}(wfun m − wfun (m+1))*Δ(m))`. -/
lemma s3G_sub_s3main_decomp (c : ℕ) (X : ℕ) (α β : ℝ) :
    s3G c α β X - s3main c α β X
      = s3c c * ((∑ m ∈ Finset.Icc 1 X, wfun α β m)
            - (X : ℝ) * ((Real.log (X : ℝ) - α - 1) * (Real.log (X : ℝ) - β - 1) + 1))
        + (s3Delta c X * wfun α β X
            + ∑ m ∈ Finset.Icc 1 (X - 1),
                (wfun α β m - wfun α β (m + 1)) * s3Delta c m) := by
  have hab := Work.LinnikAreas.Density4.BzBilin.abel_two_weights (sqfreeCop c) (wfun α β) (s3c c) X
  have hcomm : (∑ m ∈ Finset.Icc 1 X, wfun α β m * sqfreeCop c m)
      = ∑ m ∈ Finset.Icc 1 X, sqfreeCop c m * wfun α β m :=
    Finset.sum_congr rfl (fun m _ => mul_comm _ _)
  have hDelta : ∀ m : ℕ,
      (∑ k ∈ Finset.Icc 1 m, sqfreeCop c k) - s3c c * (m : ℝ) = s3Delta c m := by
    intro m
    rw [sum_sqfreeCop_eq_s3Count, s3Delta]
  have hmain : s3main c α β X
      = s3c c * ((X : ℝ) * ((Real.log (X : ℝ) - α - 1) * (Real.log (X : ℝ) - β - 1) + 1)) := by
    rw [s3main]; ring
  have hkey : (∑ m ∈ Finset.Icc 1 X, wfun α β m * sqfreeCop c m)
        - s3c c * ((X : ℝ) * ((Real.log (X : ℝ) - α - 1) * (Real.log (X : ℝ) - β - 1) + 1))
      = ((∑ m ∈ Finset.Icc 1 X, sqfreeCop c m * wfun α β m)
            - s3c c * (∑ m ∈ Finset.Icc 1 X, wfun α β m))
        + s3c c * ((∑ m ∈ Finset.Icc 1 X, wfun α β m)
            - (X : ℝ) * ((Real.log (X : ℝ) - α - 1) * (Real.log (X : ℝ) - β - 1) + 1)) := by
    rw [hcomm]; ring
  rw [s3G_eq_weighted_sum, hmain, hkey, hab]
  simp only [hDelta]
  ring

/-- **Sharp two-Abel estimate for the squarefree-coprime sum `s3G`** (Graham 1978 / An
arXiv:2206.10104, Lemma 0108 + two partial summations; the `k = ℚ`, `w = y = z` case).

There is `K > 0` with, for all `c ≥ 1`, `X ≥ 2` and `α, β ≥ 0`,
`|s3G c α β X − s3main c α β X| ≤ K·σ_{-1/2}(c)·√X·(1+|log(2X) − α|)·(1+|log(2X) − β|)`,
where `s3G c α β X = Σ_{m ≤ X, (m,c)=1, m squarefree}(log m − α)(log m − β)`,
`s3main c α β X = s3c c·X·((log X − α − 1)(log X − β − 1) + 1)` and
`s3c c = ζ(2)^{-1}·∏_{p|c} p/(p+1)` (all three in
`Submission/Work/LinnikAreas/Density4/BzS3/S3InnerDefs.lean`), and
`σ_{-1/2}(c) = Σ_{d|c} d^{-1/2}`.

ROUTE (all ingredients available; numerically the max ratio is ≈ 0.81):
1. `Work.LinnikAreas.Density4.BzS3.sqfree_coprime_count_main` is PROVED, sorry-free and
axiom-clean (verify with `#print axioms`): `|Σ_{m ≤ M, (m,c)=1} μ²(m) − s3c c·M| ≤ C₀·√M·σ_{-1/2}(c)`
for `M, c ≥ 1`; its main term is displayed as `(M:ℝ)*(∏_{p|c} p/(p+1))/(π²/6)` which equals
`s3c c * M`.
2. Abel summation in the two-element form
`Σ_{m≤X} w(m)·a(m) = w(X)·A(X) + Σ_{m<X} (w(m) − w(m+1))·A(m)`, `A(m) = Σ_{k≤m} a(k)`, with
`w = wfun α β`, `a = sqfreeCop c` (`Submission/Work/LinnikAreas/Density4/BzS3/S3GAuxDefs.lean`).
The proved lemmas `s3G_eq_sum` and `s3G_abel_decomp` in
`Submission/Work/LinnikAreas/Density4/BzS3/S3G_abel_sharp.lean` already perform this reduction;
that file's own `S3G_abel_sharp` has `sorry`s and TIMES OUT on `whnf` at the default heartbeat
limit, so do not copy it verbatim.
3. The three elementary inputs (prove them yourself, or import the sibling files if
`#print axioms` shows them clean):
   (a) `|Σ_{m≤X} wfun α β m − X·((log X − α − 1)(log X − β − 1) + 1)|
        ≤ C·((1+log X)² + (α+β)(1+log X))` for `α, β ≥ 0`;
   (b) `Σ_{m ≤ X−1} |wfun α β (m+1) − wfun α β m|·√m
        ≤ C·√X·(1+|log(2X) − α|)·(1+|log(2X) − β|)` for `α, β ≥ 0`;
   (c) `(1 + log(2X))² ≤ C·√X` for `X ≥ 2`
   (routes are written out in the docstrings of the files `S3G_logpair_sum_bound.lean`,
   `S3G_weight_increment_bound.lean`, `S3G_log_twoX_bound.lean`).
4. `X = 1` is excluded by `2 ≤ X`; the caller handles `X = 1` separately. -/
theorem s3G_abel_sharp : ∃ K : ℝ, 0 < K ∧ ∀ (c X : ℕ) (α β : ℝ),
    1 ≤ c → 2 ≤ X → 0 ≤ α → 0 ≤ β →
    |Work.LinnikAreas.Density4.BzS3.s3G c α β X - Work.LinnikAreas.Density4.BzS3.s3main c α β X|
      ≤ (K * ∑ d ∈ c.divisors, 1 / Real.sqrt (d : ℝ)) * Real.sqrt (X : ℝ)
        * (1 + |Real.log (2 * (X : ℝ)) - α|) * (1 + |Real.log (2 * (X : ℝ)) - β|) := by
  obtain ⟨K₁, hK₁, hsmooth⟩ := Work.LinnikAreas.JutilaPieces.S3GSmoothSharp
  obtain ⟨K₂, hK₂, habel⟩ := Work.LinnikAreas.JutilaPieces.S3GAbelErr
  refine ⟨K₁ + K₂, by linarith, ?_⟩
  intro c X α β hc hX hα hβ
  set A : ℝ := 1 + |Real.log (2 * (X : ℝ)) - α| with hAdef
  set B : ℝ := 1 + |Real.log (2 * (X : ℝ)) - β| with hBdef
  have hsg1 : 1 ≤ s3Sig c := s3Sig_one_le c hc
  have hCnn : 0 ≤ s3c c := s3c_nonneg c
  have hC1 : s3c c ≤ 1 := s3c_le_one c
  have hs : |(∑ m ∈ Finset.Icc 1 X, wfun α β m)
      - (X : ℝ) * ((Real.log (X : ℝ) - α - 1) * (Real.log (X : ℝ) - β - 1) + 1)|
      ≤ K₁ * A * B * Real.sqrt (X : ℝ) := by
    have h := hsmooth X α β hX hα hβ
    have hsum : (∑ m ∈ Finset.Icc 1 X, wfun α β m)
        = ∑ m ∈ Finset.Icc 1 X, (Real.log (m : ℝ) - α) * (Real.log (m : ℝ) - β) := by
      refine Finset.sum_congr rfl (fun m _ => ?_)
      rw [wfun]
    rw [hsum, hAdef, hBdef]
    exact h
  have he : |s3Delta c X * wfun α β X
      + ∑ m ∈ Finset.Icc 1 (X - 1), (wfun α β m - wfun α β (m + 1)) * s3Delta c m|
      ≤ K₂ * s3Sig c * Real.sqrt (X : ℝ) * A * B := by
    have h := habel c X α β hc hX hα hβ
    rw [← hAdef, ← hBdef] at h
    exact h
  have hRnn : (0 : ℝ) ≤ A * B * Real.sqrt (X : ℝ) := by positivity
  have hstep1 : K₁ * (A * B * Real.sqrt (X : ℝ))
      ≤ K₁ * (s3Sig c * (A * B * Real.sqrt (X : ℝ))) := by
    refine mul_le_mul_of_nonneg_left ?_ hK₁.le
    calc A * B * Real.sqrt (X : ℝ) = 1 * (A * B * Real.sqrt (X : ℝ)) := by ring
      _ ≤ s3Sig c * (A * B * Real.sqrt (X : ℝ)) :=
          mul_le_mul_of_nonneg_right hsg1 hRnn
  rw [s3G_sub_s3main_decomp c X α β]
  calc |s3c c * ((∑ m ∈ Finset.Icc 1 X, wfun α β m)
          - (X : ℝ) * ((Real.log (X : ℝ) - α - 1) * (Real.log (X : ℝ) - β - 1) + 1))
        + (s3Delta c X * wfun α β X
            + ∑ m ∈ Finset.Icc 1 (X - 1),
                (wfun α β m - wfun α β (m + 1)) * s3Delta c m)|
      ≤ |s3c c * ((∑ m ∈ Finset.Icc 1 X, wfun α β m)
            - (X : ℝ) * ((Real.log (X : ℝ) - α - 1) * (Real.log (X : ℝ) - β - 1) + 1))|
          + |s3Delta c X * wfun α β X
            + ∑ m ∈ Finset.Icc 1 (X - 1),
                (wfun α β m - wfun α β (m + 1)) * s3Delta c m| := abs_add_le _ _
    _ ≤ K₁ * A * B * Real.sqrt (X : ℝ) + K₂ * s3Sig c * Real.sqrt (X : ℝ) * A * B := by
        refine add_le_add ?_ he
        rw [abs_mul, abs_of_nonneg hCnn]
        calc s3c c * |(∑ m ∈ Finset.Icc 1 X, wfun α β m)
              - (X : ℝ) * ((Real.log (X : ℝ) - α - 1) * (Real.log (X : ℝ) - β - 1) + 1)|
            ≤ 1 * |(∑ m ∈ Finset.Icc 1 X, wfun α β m)
              - (X : ℝ) * ((Real.log (X : ℝ) - α - 1) * (Real.log (X : ℝ) - β - 1) + 1)| :=
              mul_le_mul_of_nonneg_right hC1 (abs_nonneg _)
          _ = |(∑ m ∈ Finset.Icc 1 X, wfun α β m)
              - (X : ℝ) * ((Real.log (X : ℝ) - α - 1) * (Real.log (X : ℝ) - β - 1) + 1)| :=
              one_mul _
          _ ≤ K₁ * A * B * Real.sqrt (X : ℝ) := hs
    _ ≤ (K₁ + K₂) * s3Sig c * Real.sqrt (X : ℝ) * A * B := by
        calc K₁ * A * B * Real.sqrt (X : ℝ) + K₂ * s3Sig c * Real.sqrt (X : ℝ) * A * B
            = K₁ * (A * B * Real.sqrt (X : ℝ))
                + K₂ * s3Sig c * Real.sqrt (X : ℝ) * A * B := by ring
          _ ≤ K₁ * (s3Sig c * (A * B * Real.sqrt (X : ℝ)))
                + K₂ * s3Sig c * Real.sqrt (X : ℝ) * A * B := by linarith [hstep1]
          _ = (K₁ + K₂) * s3Sig c * Real.sqrt (X : ℝ) * A * B := by ring
    _ = ((K₁ + K₂) * ∑ d ∈ c.divisors, 1 / Real.sqrt (d : ℝ)) * Real.sqrt (X : ℝ)
          * (1 + |Real.log (2 * (X : ℝ)) - α|) * (1 + |Real.log (2 * (X : ℝ)) - β|) := by
        rw [hAdef, hBdef, s3Sig]

end

end Work.LinnikAreas2.S3Hard
