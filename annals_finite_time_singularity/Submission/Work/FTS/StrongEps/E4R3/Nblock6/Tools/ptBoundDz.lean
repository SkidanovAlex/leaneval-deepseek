/-
Copyright: work module for the Elgindi finite-time singularity project.

# `ptBoundDz` — the pointwise level-six bound for the product `A · D_z f`

The pointwise companion of the level-six product rule of
`Work.FTS.StrongPersist.N6.prod_majorant6`, for the *derivative* factor `D_z f` of a datum
`f ∈ ℋ⁷` rather than for a second `ℋ⁶`-datum.  For `A, f` smooth on the open quadrant
(`SmoothOpen`), `A ∈ ℋ⁶`, `f ∈ ℋ⁶ ∩ ℋ⁷`, `|A| ≤ MA`, `|∂_θA| ≤ KA` on the open quadrant and
every `(z,θ)` in the open quadrant,

`HkIntegrand α 6 (A · D_z f)(z,θ) ≤ K·MA²·I⁷_f + K·(1+(γ-1)⁻¹(|A|²_{ℋ⁶}+|f|²_{ℋ⁶}))·(I⁶_A+I⁶_f)
   + K·KA²·I⁶_f + (the four exceptional slots)`.

## Route

`HkIntegrand` of the product is split into its `7` pure `D_z`-slots and its (at most) `49`
mixed slots.  Each slot is expanded by Leibniz (`leibniz_open_Dz`, `leibniz_open_mixed`,
together with the shifts `D_z^i (D_z f) = D_z^{i+1} f` and
`D_z^j D_θ^i (D_z f) = D_z^{j+1} D_θ^i f` on the open quadrant, the latter from
`ThetaU.OpenSliceAux.DthIter_DzIter_eqOn_of_isOpen`), then estimated by
Cauchy–Schwarz (`sq_sum_le_card_mul_sum_sq`) term by term.  In each Leibniz summand `X·Y`
(an `A`-slot times an `f`-slot) one of the two factors is priced *pointwise* by the Agmon
bound `Work.FTS.StrongPersist.N6.PwAny6` (orders `≤ 4`, i.e. `k-2`) and the other by the
single-slot domination `sq_le_HkIntegrand_z` / `sq_le_HkIntegrand_mixed`; the split is chosen
so that the surviving slot of `f` always has order `≤ 6` — only the *undifferentiated*
coefficient `A` can be paired with the order-`7` slot of `f`, which is where the `MA²·I⁷_f`
term comes from.

The borderline configurations not covered by that pattern are exactly the four exceptional
terms of the statement: a pure `D_z`-slot of order `5` of `A` (no pointwise Agmon bound exists
at that order, cf. `N6Trans.SixAux.NOTES_supDzSix_REFUTED.md`) paired with a mixed slot of `f`
(`D_z⁵A·D_θ²f`), the symmetric configurations `D_zD_θA·D_z⁵f`, `D_θA·D_z⁵f`, `D_θ²A·D_z⁵f`,
and the configuration `D_θA·D_z⁶f`, which is closed by the hypothesis `|∂_θA| ≤ KA`
(`D_θA = sin(2θ)·∂_θA` and `sin(2θ)^{2-γ+η} ≤ 1`).

The supporting development lives in `Tools/PtBAux/{Basic,Close,Slots,SlotsM}.lean`.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.OpenPkg.ProdOpen.leibniz_open_mixed
import Submission.Work.FTS.StrongPersist.N6.PwOpen6
import Submission.Work.FTS.TransportS.sup_dz_le_hk
import Submission.Work.FTS.StrongEps.H5.LevelShift
import Submission.Work.FTS.StrongEps.E4R3.Nblock6.Tools.PtBAux.SlotsM

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E4R3.Nblock6.Tools

open Function Set

noncomputable section

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

theorem ptBoundDz (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ (A f : ℝ → ℝ → ℝ) (MA KA : ℝ),
      Work.FTS.EllipticEst.SmoothOpen A → Work.FTS.EllipticEst.SmoothOpen f →
      Work.Spaces.HkMem α 6 A → Work.Spaces.HkMem α 6 f → Work.Spaces.HkMem α 7 f →
      (∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → |A z θ| ≤ MA) →
      (∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → |Work.Spaces.pth A z θ| ≤ KA) →
      ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        Work.Spaces.HkIntegrand α 6 (fun z θ => A z θ * Work.Spaces.Dz f z θ) z θ
          ≤ K * MA ^ 2 * Work.Spaces.HkIntegrand α 7 f z θ
            + K * (1 + (Work.Spaces.gam α - 1)⁻¹
                * (Work.Spaces.HkSq α 6 A + Work.Spaces.HkSq α 6 f))
              * (Work.Spaces.HkIntegrand α 6 A z θ + Work.Spaces.HkIntegrand α 6 f z θ)
            + K * KA ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ
            + K * (Work.Spaces.DzIter 5 A z θ * Work.Spaces.mixed 1 1 f z θ
                * Work.Spaces.Wt α z θ) ^ 2
            + K * (Work.Spaces.mixed 1 1 A z θ * Work.Spaces.DzIter 5 f z θ
                * Work.Spaces.Wt α z θ) ^ 2
            + K * (Work.Spaces.Dth A z θ * Work.Spaces.DzIter 5 f z θ
                * Work.Spaces.Wt α z θ) ^ 2
            + K * (Work.Spaces.DthIter 2 A z θ * Work.Spaces.DzIter 5 f z θ
                * Work.Spaces.Wt α z θ) ^ 2 := by
  obtain ⟨CPw, hCPwpos, hPwAny⟩ := Work.FTS.StrongPersist.N6.PwAny6
  refine ⟨10 ^ 13 * max CPw 1, by positivity, ?_⟩
  intro A f MA KA hAO hfO hA6 hf6 hf7 hMA hKA z θ hz hθ0 hθ1
  have hθ : θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨hθ0, hθ1⟩
  have hPwA : PtB.SupPw α CPw A := fun b a hab z θ hz hθ =>
    hPwAny α A b a hα hα1 hAO hA6 hab z hz θ hθ
  have hPwf : PtB.SupPw α CPw f := fun b a hab z θ hz hθ =>
    hPwAny α f b a hα hα1 hfO hf6 hab z hz θ hθ
  have hMnn : 0 ≤ PtB.Maj α A f MA KA z θ := PtB.Maj_nonneg hα A f MA KA z θ
  have hCMpos : 0 < max CPw 1 := lt_of_lt_of_le hCPwpos (le_max_left _ _)
  -- the pure `D_z`-sum
  have hzsum : ∑ i ∈ Finset.range 7,
      (Work.Spaces.DzIter i (fun z θ => A z θ * Work.Spaces.Dz f z θ) z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      ≤ 7 * (10 ^ 11 * max CPw 1 * PtB.Maj α A f MA KA z θ) := by
    have hstep : ∀ i ∈ Finset.range 7,
        (Work.Spaces.DzIter i (fun z θ => A z θ * Work.Spaces.Dz f z θ) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
        ≤ 10 ^ 11 * max CPw 1 * PtB.Maj α A f MA KA z θ :=
      fun i hi => PtB.zslot_le hα hα1 hAO hfO hMA hPwA hPwf hCPwpos i
        (Nat.le_of_lt_succ (Finset.mem_range.mp hi)) z θ hz hθ0 hθ1
    calc ∑ i ∈ Finset.range 7,
          (Work.Spaces.DzIter i (fun z θ => A z θ * Work.Spaces.Dz f z θ) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
        ≤ ∑ _i ∈ Finset.range 7, (10 ^ 11 * max CPw 1 * PtB.Maj α A f MA KA z θ) :=
          Finset.sum_le_sum hstep
      _ = 7 * (10 ^ 11 * max CPw 1 * PtB.Maj α A f MA KA z θ) := by
          simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          ring
  -- the mixed sum
  have hmsum : ∑ i ∈ Finset.range 7, ∑ j ∈ Finset.range 7,
      (if 1 ≤ i ∧ i + j ≤ 6 then
        (Work.Spaces.mixed j i (fun z θ => A z θ * Work.Spaces.Dz f z θ) z θ
          * Work.Spaces.Wt α z θ) ^ 2 else 0)
      ≤ 49 * (10 ^ 11 * max CPw 1 * PtB.Maj α A f MA KA z θ) := by
    have hper : ∀ i ∈ Finset.range 7, ∀ j ∈ Finset.range 7,
        (if 1 ≤ i ∧ i + j ≤ 6 then
          (Work.Spaces.mixed j i (fun z θ => A z θ * Work.Spaces.Dz f z θ) z θ
            * Work.Spaces.Wt α z θ) ^ 2 else 0)
        ≤ 10 ^ 11 * max CPw 1 * PtB.Maj α A f MA KA z θ := by
      intro i hi j hj
      by_cases hc : 1 ≤ i ∧ i + j ≤ 6
      · rw [if_pos hc]
        exact PtB.mslot_le hα hα1 hAO hfO hMA hKA hPwA hPwf hCPwpos i j hc.1 hc.2
          z θ hz hθ0 hθ1
      · rw [if_neg hc]
        exact mul_nonneg (by positivity) hMnn
    have hsum2 : ∑ i ∈ Finset.range 7, ∑ j ∈ Finset.range 7,
        (if 1 ≤ i ∧ i + j ≤ 6 then
          (Work.Spaces.mixed j i (fun z θ => A z θ * Work.Spaces.Dz f z θ) z θ
            * Work.Spaces.Wt α z θ) ^ 2 else 0)
        ≤ ∑ _i ∈ Finset.range 7, ∑ _j ∈ Finset.range 7,
            (10 ^ 11 * max CPw 1 * PtB.Maj α A f MA KA z θ) :=
      Finset.sum_le_sum (fun i hi => Finset.sum_le_sum (fun j hj => hper i hi j hj))
    calc ∑ i ∈ Finset.range 7, ∑ j ∈ Finset.range 7,
          (if 1 ≤ i ∧ i + j ≤ 6 then
            (Work.Spaces.mixed j i (fun z θ => A z θ * Work.Spaces.Dz f z θ) z θ
              * Work.Spaces.Wt α z θ) ^ 2 else 0)
        ≤ ∑ _i ∈ Finset.range 7, ∑ _j ∈ Finset.range 7,
            (10 ^ 11 * max CPw 1 * PtB.Maj α A f MA KA z θ) := hsum2
      _ = 49 * (10 ^ 11 * max CPw 1 * PtB.Maj α A f MA KA z θ) := by
          simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          ring
  rw [Work.Spaces.HkIntegrand]
  refine le_trans (add_le_add hzsum hmsum) ?_
  have hXnn : 0 ≤ max CPw 1 * PtB.Maj α A f MA KA z θ :=
    mul_nonneg (le_of_lt hCMpos) hMnn
  have hfin : 7 * (10 ^ 11 * max CPw 1 * PtB.Maj α A f MA KA z θ)
      + 49 * (10 ^ 11 * max CPw 1 * PtB.Maj α A f MA KA z θ)
      ≤ 10 ^ 13 * max CPw 1 * PtB.Maj α A f MA KA z θ := by
    nlinarith [hXnn]
  refine le_trans hfin (le_of_eq ?_)
  simp only [PtB.Maj, PtB.Maj1, PtB.Maj2, PtB.Maj3, PtB.Maj4, PtB.Maj5, PtB.Maj6, PtB.Maj7]
  ring

end

end Work.FTS.StrongEps.E4R3.Nblock6.Tools
