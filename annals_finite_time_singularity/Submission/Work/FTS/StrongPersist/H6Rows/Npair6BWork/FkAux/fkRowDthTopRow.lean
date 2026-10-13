import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkRowDthShiftLow
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkRowDthShiftHigh
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkRowDthZeroSlot
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkThetaIbpPiece
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkRowsAux
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkRowDth6
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.contDiffOn6_FK

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux

set_option maxHeartbeats 1600000

/-- **Fubini for a radial coefficient.**  For a product-integrable `p ↦ r p.1 · G p.1 p.2` with
`r` depending on `z` alone, the product integral is the iterated integral with `r z` pulled out of
the angular integral.  (`integral_const_mul` is unconditional, so no integrability of the slices
is needed.) -/
private lemma integral_prod_radial {r : ℝ → ℝ} {G : ℝ → ℝ → ℝ}
    (hInt : MeasureTheory.Integrable (fun p : ℝ × ℝ => r p.1 * G p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ))) :
    (∫ p, r p.1 * G p.1 p.2
        ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
      = ∫ z in Work.Spaces.Iz, r z * (∫ θ in Work.Spaces.Iθ, G z θ) := by
  rw [MeasureTheory.integral_prod _ hInt]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  exact MeasureTheory.integral_const_mul (r z) (fun θ => G z θ)

/-- Elementary arithmetic: `(7)·(64·(A·X)) ≤ (448(A+1)+1)·a·X` for `A, X ≥ 0` and `a ≥ 1`
(the factor `64 = 2^6` bounds the binomial coefficients of the Leibniz expansion, and
`a = α^{-3} ≥ 1` is the `α`-power price). -/
private lemma final_arith {A X a : ℝ} (hA : 0 ≤ A) (hX : 0 ≤ X) (ha : 1 ≤ a) :
    (7 : ℝ) * (64 * (A * X)) ≤ (448 * (A + 1) + 1) * a * X := by
  nlinarith [mul_nonneg hA hX, mul_nonneg (mul_nonneg hA hX) (sub_nonneg.mpr ha),
    sq_nonneg X]

/-- **The assembly of `fkRowDthTopRow`** (the `(a,b) = (0,6)` angular-moment slot), with the three
per-summand inputs (the shifted slots for `1 ≤ b₁ ≤ 3` and `4 ≤ b₁ ≤ 6`, and the
product-integrability of the `b₁ = 0` slot) as explicit hypotheses.  This is the (private)
`fkRowDth6_core` of `FkAux/fkRowDth6.lean`, re-created here because "private" is not importable. -/
theorem fkRowDthTopRow_core
    (hLow : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1,
      ∀ (f : Work.FTS.Galerkin.Fn) (M : ℝ) (ρ : ℝ → ℝ → ℝ) (b₁ : ℕ),
        Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.DatData α f M →
        1 ≤ b₁ → b₁ ≤ 3 → Work.FTS.TransportS.IsLeafW α 0 ρ →
        (MeasureTheory.Integrable (fun p : ℝ × ℝ =>
            Work.Elliptic.DzdIter b₁ (fun z => Work.Construction.FK f z) p.1
              * (ρ p.1 p.2 * Work.Spaces.mixed (6 - b₁) 1 f p.1 p.2
                  * Work.Spaces.mixed 6 0 f p.1 p.2))
          ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ)) ∧
          |∫ p, Work.Elliptic.DzdIter b₁ (fun z => Work.Construction.FK f z) p.1
                * (ρ p.1 p.2 * Work.Spaces.mixed (6 - b₁) 1 f p.1 p.2
                    * Work.Spaces.mixed 6 0 f p.1 p.2)
              ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
                (MeasureTheory.volume.restrict Work.Spaces.Iθ))|
            ≤ C * (1 + M) * (1 + M) * (1 + Work.Spaces.HkSq α 6 f)))
    (hHigh : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1,
      ∀ (f : Work.FTS.Galerkin.Fn) (M : ℝ) (ρ : ℝ → ℝ → ℝ) (b₁ : ℕ),
        Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.DatData α f M →
        4 ≤ b₁ → b₁ ≤ 6 → Work.FTS.TransportS.IsLeafW α 0 ρ →
        (MeasureTheory.Integrable (fun p : ℝ × ℝ =>
            Work.Elliptic.DzdIter b₁ (fun z => Work.Construction.FK f z) p.1
              * (ρ p.1 p.2 * Work.Spaces.mixed (6 - b₁) 1 f p.1 p.2
                  * Work.Spaces.mixed 6 0 f p.1 p.2))
          ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ)) ∧
          |∫ p, Work.Elliptic.DzdIter b₁ (fun z => Work.Construction.FK f z) p.1
                * (ρ p.1 p.2 * Work.Spaces.mixed (6 - b₁) 1 f p.1 p.2
                    * Work.Spaces.mixed 6 0 f p.1 p.2)
              ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
                (MeasureTheory.volume.restrict Work.Spaces.Iθ))|
            ≤ C * (1 + M) * (1 + M) * (1 + Work.Spaces.HkSq α 6 f)))
    (hZero : ∀ α ∈ Set.Ioc 0 1,
      ∀ (f : Work.FTS.Galerkin.Fn) (M : ℝ) (ρ : ℝ → ℝ → ℝ),
        Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.DatData α f M →
        Work.FTS.TransportS.IsLeafW α 0 ρ →
        MeasureTheory.Integrable (fun p : ℝ × ℝ =>
            Work.Construction.FK f p.1
              * (ρ p.1 p.2 * Work.Spaces.mixed 6 1 f p.1 p.2
                  * Work.Spaces.mixed 6 0 f p.1 p.2))
          ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ))) :
    ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1,
      ∀ (f : Work.FTS.Galerkin.Fn) (M : ℝ) (ρ : ℝ → ℝ → ℝ),
        Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.DatData α f M →
        Work.FTS.TransportS.IsLeafW α 0 ρ →
        |Work.FTS.TransportS.slotPairing ρ 0 6
            (fun z θ => Work.Construction.FK f z * Work.Spaces.Dth f z θ) f|
          ≤ C * α ^ (-(3 : ℝ)) * (1 + M) * (1 + M)
              * (1 + Work.Spaces.HkSq α 6 f) := by
  obtain ⟨CL, hCLpos, hLow⟩ := hLow
  obtain ⟨CH, _hCHpos, hHigh⟩ := hHigh
  obtain ⟨CZ, hCZpos, hCZ⟩ := Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkThetaIbpPiece
  refine ⟨448 * (max (max CL CH) CZ + 1) + 1, by positivity, ?_⟩
  intro α hαmem f M ρ hdat hρ
  obtain ⟨hα0, hα1⟩ := Set.mem_Ioc.mp hαmem
  have hM0 : 0 ≤ M := le_trans (Work.Spaces.HkNorm_nonneg α 4 f) hdat.bdd
  have hS0 : 0 ≤ Work.Spaces.HkSq α 6 f := Work.Spaces.HkSq_nonneg α 6 f
  -- ## the smoothness of the two factors of the coefficient
  have hFKcd : ContDiffOn ℝ 6
      (Function.uncurry (fun z (_ : ℝ) => Work.Construction.FK f z))
      Work.FTS.EllipticEst.Q0 :=
    Work.FTS.StrongPersist.H6Rows.Npair6BWork.contDiffOn6_FK α hαmem f M hdat
  have hdthcd : ContDiffOn ℝ 6 (Function.uncurry (Work.Spaces.Dth f))
      Work.FTS.EllipticEst.Q0 := hdat.sm.Dth.forall 6
  -- ## the pointwise Leibniz identity on the open quadrant
  have hpt : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      ρ z θ * Work.Spaces.mixed 6 0
          (fun z θ => Work.Construction.FK f z * Work.Spaces.Dth f z θ) z θ
        * Work.Spaces.mixed 6 0 f z θ
      = ∑ b₁ ∈ Finset.range 7, (Nat.choose 6 b₁ : ℝ) *
          (Work.Elliptic.DzdIter b₁ (fun z => Work.Construction.FK f z) z
            * (ρ z θ * Work.Spaces.mixed (6 - b₁) 1 f z θ
                * Work.Spaces.mixed 6 0 f z θ)) := by
    intro z θ hz hθ0 hθ1
    have h := Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.leibniz_rad_any
      (r := fun z => Work.Construction.FK f z) (g := Work.Spaces.Dth f)
      hFKcd hdthcd (j := 6) (i := 0) (by norm_num) z θ hz hθ0 hθ1
    rw [h, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun b₁ _ => ?_
    rw [Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.mixed_Dth_one]
    ring
  -- ## the same identity almost everywhere on the product measure
  have hae : (fun p : ℝ × ℝ =>
        ρ p.1 p.2 * Work.Spaces.mixed 6 0
            (fun z θ => Work.Construction.FK f z * Work.Spaces.Dth f z θ) p.1 p.2
          * Work.Spaces.mixed 6 0 f p.1 p.2)
      =ᵐ[((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ))]
      (fun p : ℝ × ℝ => ∑ b₁ ∈ Finset.range 7, (Nat.choose 6 b₁ : ℝ) *
          (Work.Elliptic.DzdIter b₁ (fun z => Work.Construction.FK f z) p.1
            * (ρ p.1 p.2 * Work.Spaces.mixed (6 - b₁) 1 f p.1 p.2
                * Work.Spaces.mixed 6 0 f p.1 p.2))) :=
    Work.FTS.TransportS.ae_of_forall_Qd (fun z θ hz hθ0 hθ1 => hpt z θ hz hθ0 hθ1)
  -- ## the product-integrability of every summand
  have hsum_int : ∀ b₁ ∈ Finset.range 7, MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      (Nat.choose 6 b₁ : ℝ) *
        (Work.Elliptic.DzdIter b₁ (fun z => Work.Construction.FK f z) p.1
          * (ρ p.1 p.2 * Work.Spaces.mixed (6 - b₁) 1 f p.1 p.2
              * Work.Spaces.mixed 6 0 f p.1 p.2)))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    intro b₁ hb₁
    have hb : b₁ ≤ 6 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb₁)
    have hbase : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
        Work.Elliptic.DzdIter b₁ (fun z => Work.Construction.FK f z) p.1
          * (ρ p.1 p.2 * Work.Spaces.mixed (6 - b₁) 1 f p.1 p.2
              * Work.Spaces.mixed 6 0 f p.1 p.2))
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
      -- ## the `b₁ = 0` slot: the angular integration by parts
      rcases Nat.eq_zero_or_pos b₁ with h0 | hpos
      · subst h0
        simpa using hZero α hαmem f M ρ hdat hρ
      · rcases lt_or_ge b₁ 4 with h4 | h4
        · exact (hLow α hαmem f M ρ b₁ hdat (by omega) (by omega) hρ).1
        · exact (hHigh α hαmem f M ρ b₁ hdat (by omega) (by omega) hρ).1
    exact (hbase.const_mul ((Nat.choose 6 b₁ : ℝ))).congr
      (Filter.Eventually.of_forall fun p => by ring)
  have hIntSum : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      ∑ b₁ ∈ Finset.range 7, (Nat.choose 6 b₁ : ℝ) *
        (Work.Elliptic.DzdIter b₁ (fun z => Work.Construction.FK f z) p.1
          * (ρ p.1 p.2 * Work.Spaces.mixed (6 - b₁) 1 f p.1 p.2
              * Work.Spaces.mixed 6 0 f p.1 p.2)))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    MeasureTheory.integrable_finsetSum _ hsum_int
  have hIntFull : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      ρ p.1 p.2 * Work.Spaces.mixed 6 0
          (fun z θ => Work.Construction.FK f z * Work.Spaces.Dth f z θ) p.1 p.2
        * Work.Spaces.mixed 6 0 f p.1 p.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    hIntSum.congr hae.symm
  -- ## the product-measure form of the slot pairing
  have hprod : Work.FTS.TransportS.slotPairing ρ 0 6
      (fun z θ => Work.Construction.FK f z * Work.Spaces.Dth f z θ) f
      = ∫ p, ρ p.1 p.2 * Work.Spaces.mixed 6 0
            (fun z θ => Work.Construction.FK f z * Work.Spaces.Dth f z θ) p.1 p.2
          * Work.Spaces.mixed 6 0 f p.1 p.2
        ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    (MeasureTheory.integral_prod _ hIntFull).symm
  -- ## the Leibniz expansion of the product integral
  have hexp : (∫ p, ρ p.1 p.2 * Work.Spaces.mixed 6 0
            (fun z θ => Work.Construction.FK f z * Work.Spaces.Dth f z θ) p.1 p.2
          * Work.Spaces.mixed 6 0 f p.1 p.2
        ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
      = ∑ b₁ ∈ Finset.range 7, (Nat.choose 6 b₁ : ℝ) *
          (∫ p, Work.Elliptic.DzdIter b₁ (fun z => Work.Construction.FK f z) p.1
                * (ρ p.1 p.2 * Work.Spaces.mixed (6 - b₁) 1 f p.1 p.2
                    * Work.Spaces.mixed 6 0 f p.1 p.2)
              ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
                (MeasureTheory.volume.restrict Work.Spaces.Iθ))) := by
    rw [MeasureTheory.integral_congr_ae hae]
    rw [MeasureTheory.integral_finsetSum]
    · refine Finset.sum_congr rfl fun b₁ _ => ?_
      exact MeasureTheory.integral_const_mul _ _
    · intro b₁ hb₁
      exact hsum_int b₁ hb₁
  -- ## the per-summand bounds
  have hterm : ∀ b₁ ∈ Finset.range 7,
      |∫ p, Work.Elliptic.DzdIter b₁ (fun z => Work.Construction.FK f z) p.1
            * (ρ p.1 p.2 * Work.Spaces.mixed (6 - b₁) 1 f p.1 p.2
                * Work.Spaces.mixed 6 0 f p.1 p.2)
          ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ))|
        ≤ max (max CL CH) CZ * (1 + M) * (1 + M) * (1 + Work.Spaces.HkSq α 6 f) := by
    intro b₁ hb₁
    have hb : b₁ ≤ 6 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb₁)
    have hCBnn : (0 : ℝ) ≤ (1 + M) * (1 + M) * (1 + Work.Spaces.HkSq α 6 f) :=
      mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
    have hCL_le : CL ≤ max (max CL CH) CZ :=
      le_trans (le_max_left CL CH) (le_max_left (max CL CH) CZ)
    have hCH_le : CH ≤ max (max CL CH) CZ :=
      le_trans (le_max_right CL CH) (le_max_left (max CL CH) CZ)
    have hCZ_le : CZ ≤ max (max CL CH) CZ := le_max_right (max CL CH) CZ
    have hscale : ∀ c : ℝ, c ≤ max (max CL CH) CZ →
        c * (1 + M) * (1 + M) * (1 + Work.Spaces.HkSq α 6 f)
          ≤ max (max CL CH) CZ * (1 + M) * (1 + M)
            * (1 + Work.Spaces.HkSq α 6 f) := by
      intro c hc
      refine mul_le_mul_of_nonneg_right ?_ (by linarith)
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hc (by linarith)) (by linarith)
    rcases Nat.eq_zero_or_pos b₁ with h0 | hpos
    · -- ## the `b₁ = 0` slot: the angular integration by parts
      subst h0
      have hcase : (∫ p, Work.Elliptic.DzdIter 0 (fun z => Work.Construction.FK f z) p.1
            * (ρ p.1 p.2 * Work.Spaces.mixed (6 - 0) 1 f p.1 p.2
                * Work.Spaces.mixed 6 0 f p.1 p.2)
          ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
          = ∫ z in Work.Spaces.Iz, Work.Construction.FK f z *
              (∫ θ in Work.Spaces.Iθ, ρ z θ * Work.Spaces.mixed 6 1 f z θ
                * Work.Spaces.mixed 6 0 f z θ) := by
        simpa using integral_prod_radial (r := fun z => Work.Construction.FK f z)
          (G := fun z θ => ρ z θ * Work.Spaces.mixed 6 1 f z θ
            * Work.Spaces.mixed 6 0 f z θ)
          (hZero α hαmem f M ρ hdat hρ)
      rw [hcase]
      exact le_trans (hCZ hα0 hα1 hdat 0 6 ρ (by norm_num) hρ) (hscale CZ hCZ_le)
    · rcases lt_or_ge b₁ 4 with h4 | h4
      · exact le_trans (hLow α hαmem f M ρ b₁ hdat (by omega) (by omega) hρ).2
          (hscale CL hCL_le)
      · exact le_trans (hHigh α hαmem f M ρ b₁ hdat h4 hb hρ).2
          (hscale CH hCH_le)
  -- ## the final arithmetic
  rw [hprod, hexp]
  have hsum_bound : |∑ b₁ ∈ Finset.range 7, (Nat.choose 6 b₁ : ℝ) *
        (∫ p, Work.Elliptic.DzdIter b₁ (fun z => Work.Construction.FK f z) p.1
              * (ρ p.1 p.2 * Work.Spaces.mixed (6 - b₁) 1 f p.1 p.2
                  * Work.Spaces.mixed 6 0 f p.1 p.2)
            ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
              (MeasureTheory.volume.restrict Work.Spaces.Iθ)))|
      ≤ ∑ b₁ ∈ Finset.range 7, (64 : ℝ) *
          (max (max CL CH) CZ * (1 + M) * (1 + M)
            * (1 + Work.Spaces.HkSq α 6 f)) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun b₁ hb₁ => ?_)
    have hch : |(Nat.choose 6 b₁ : ℝ)| ≤ 64 := by
      have h1 : Nat.choose 6 b₁ ≤ 64 := by
        have h2 := Nat.choose_le_two_pow 6 b₁
        norm_num at h2 ⊢
        exact h2
      rw [abs_of_nonneg (by positivity)]
      exact_mod_cast h1
    have hb := hterm b₁ hb₁
    rw [abs_mul]
    exact (mul_le_mul hch hb (abs_nonneg _) (by norm_num)).trans_eq (by ring)
  refine le_trans hsum_bound ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hα3 : (1 : ℝ) ≤ α ^ (-(3 : ℝ)) := one_le_alpha_rpow hα0 hα1
  have hCmax0 : (0 : ℝ) ≤ max (max CL CH) CZ :=
    le_trans hCZpos.le (le_max_right (max CL CH) CZ)
  have hX0 : (0 : ℝ) ≤ (1 + M) * (1 + M) * (1 + Work.Spaces.HkSq α 6 f) :=
    mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
  calc (7 : ℝ) * (64 * (max (max CL CH) CZ * (1 + M) * (1 + M)
          * (1 + Work.Spaces.HkSq α 6 f)))
      = (7 : ℝ) * (64 * (max (max CL CH) CZ
            * ((1 + M) * (1 + M) * (1 + Work.Spaces.HkSq α 6 f)))) := by ring
    _ ≤ (448 * (max (max CL CH) CZ + 1) + 1) * α ^ (-(3 : ℝ))
          * ((1 + M) * (1 + M) * (1 + Work.Spaces.HkSq α 6 f)) :=
        final_arith hCmax0 hX0 hα3
    _ = (448 * (max (max CL CH) CZ + 1) + 1) * α ^ (-(3 : ℝ)) * (1 + M) * (1 + M)
          * (1 + Work.Spaces.HkSq α 6 f) := by ring

/-- **The top `z`-slot `(a,b) = (0,6)` of the angular-moment row `(FK f)·D_θf`** (the same
statement as the `sorry` left at the top level of `FkAux/fkRowDth6.lean`, whose private
`fkRowDth6_core` is already proved).

`|slotPairing ρ 0 6 (fun z θ => FK f z * D_θ f z θ) f| ≤ C α^{-3}(1+M)²(1 + HkSq α 6 f)` for a
datum `DatData α f M` and a leaf weight `ρ` of the slot `a = 0`.

Route (all ingredients PROVED in the tree; only the assembly is new):
* the radial Leibniz `FkAux.leibniz_rad_any` with `r := fun z => FK f z`, `g := Work.Spaces.Dth f`,
  `j := 6`, `i := 0` (radial factor `C⁶` by `contDiffOn6_FK`), plus `mixed_Dth_one`;
* product-integrability from `fkRowDthZeroSlot` (`b₁ = 0`) and `fkRowDthShiftLow` /
  `fkRowDthShiftHigh` (`1 ≤ b₁ ≤ 3` resp. `4 ≤ b₁ ≤ 6`), which also give
  `|∫_p ·| ≤ C(1+M)²(1+HkSq α 6 f)` for each summand (as product integrals over
  `(volume.restrict Iz).prod (volume.restrict Iθ)`);
* the `b₁ = 0` value is `FkAux.fkThetaIbpPiece`;
* `Finset.abs_sum_le_sum_abs` + `Σ_{b₁≤6} C(6,b₁) = 64` + finite arithmetic.
The template to copy is the private `fkRowDth6_core` in `FkAux/fkRowDth6.lean` (it must be
re-created: it is `private`, hence not importable). -/
theorem fkRowDthTopRow : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1,
    ∀ (f : Work.FTS.Galerkin.Fn) (M : ℝ) (ρ : ℝ → ℝ → ℝ),
      Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.DatData α f M →
      Work.FTS.TransportS.IsLeafW α 0 ρ →
      |Work.FTS.TransportS.slotPairing ρ 0 6
          (fun z θ => Work.Construction.FK f z * Work.Spaces.Dth f z θ) f|
        ≤ C * α ^ (-(3 : ℝ)) * (1 + M) * (1 + M)
            * (1 + Work.Spaces.HkSq α 6 f) := fkRowDthTopRow_core fkRowDthShiftLow fkRowDthShiftHigh fkRowDthZeroSlot

end Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux
