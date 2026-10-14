import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.EpsE4Thr.Leaves.regFromVolterra
import Submission.Work.FTS.StrongEps.EpsRHSP_slotSup
import Submission.Work.FTS.StrongEps.PZeroScheme
import Submission.Work.FTS.StrongEps.SmoothOpen_Jeps
import Submission.Work.FTS.StrongEps.wtZ_shift_le
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.FTS.StrongPersist.DthFstar_W6
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.RowDth.perTermDthMine
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.RowDth.zeroTermDth
import Submission.Work.FTS.StrongPersist.N6Trans.Hon.SmainHon
import Submission.Work.FTS.StrongPersist.N6Trans.T1SixAux.AuxProof
import Submission.Work.FTS.StrongPersist.N6Trans.T1SixAux.leibnizRem6
import Submission.Work.FTS.StrongPersist.SupOpenH2
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.FTS.TransportS.T3SlotAux.Remainder
import Submission.Work.FTS_MuLamOK.Conversion
import Submission.Work.FTS_MuLamOK.RowReduction
import Submission.Work.FTS_RegExport.RXR5.R5PiecesF
import Submission.Work.FTS_RegExport.RXT.Sys.hasDerivAt_mixed_z
import Submission.Work.FTS_StreamBdry.Inputs.theta_part_theta
import Submission.Work.FTS_StreamBdry.SB4.DzEpartEq
import Submission.Work.H6Pair6Aux.T6Fix.mixed_sinGain_of_pthFlat
import Submission.Work.PhiStar.Honesty.sqrt_weight_mul_eq_of_mem_Ioo
-- ===== merged: Submission.Work.FTS.StrongEps.EpsConvAllTau =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsConvTau

set_option autoImplicit false

/-! ## The sub-subsequence principle -/

/-- **A sequence converges to a limit as soon as every subsequence has a further subsequence
converging to that limit.**  Stated for `ℝ`-valued functions with the uniformity of uniform
convergence on a set `s`; the index map `u` only has to tend to infinity (repetitions are
allowed, which is what an extraction lemma produces).

Proof: if the conclusion failed, then `ε ≤ dist (f x) (F n x)` would hold *frequently* (with a
witness `x ∈ s`); `Filter.exists_seq_forall_of_frequently` turns that into a sequence `ns → ∞` of
bad indices, and the hypothesis applied to `ns` contradicts badness at a large index. -/
theorem tendstoUniformlyOn_of_subseq {X : Type*} {s : Set X} {F : ℕ → X → ℝ} {f : X → ℝ}
    (h : ∀ u : ℕ → ℕ, Tendsto u atTop atTop → ∃ ψ : ℕ → ℕ, Tendsto ψ atTop atTop ∧
      TendstoUniformlyOn (fun n => F ((u ∘ ψ) n)) f atTop s) :
    TendstoUniformlyOn F f atTop s := by
  by_contra hc
  rw [Metric.tendstoUniformlyOn_iff] at hc
  have hbad : ∃ ε > 0, ∃ᶠ n in atTop, ∃ x ∈ s, ε ≤ dist (f x) (F n x) := by
    by_contra hcon
    refine hc fun ε hε => ?_
    by_contra hnot
    refine hcon ⟨ε, hε, (Filter.not_eventually.mp hnot).mono ?_⟩
    intro n hn
    push Not at hn
    exact ⟨hn.choose, hn.choose_spec.1, hn.choose_spec.2⟩
  obtain ⟨ε, hε, hfreq⟩ := hbad
  obtain ⟨ns, hns, hbad'⟩ := Filter.exists_seq_forall_of_frequently hfreq
  obtain ⟨ψ, _, hconv⟩ := h ns hns
  rw [Metric.tendstoUniformlyOn_iff] at hconv
  obtain ⟨n, hn⟩ := (hconv ε hε).exists
  exact not_lt.mpr (hbad' (ψ n)).choose_spec.2 (hn _ (hbad' (ψ n)).choose_spec.1)

/-! ## Locality of the mixed derivatives on the open quadrant -/

/-- Two functions agreeing on the open quadrant have the same iterated mixed derivatives there
(no smoothness needed: this is the locality of `deriv`).  The `D_θ`-analogue of
`Work.FTS.EllipticEst.SmoothOpen.DzIter_congr`. -/
theorem mixed_congr_of_quad {f g : ℝ → ℝ → ℝ}
    (h : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → f z θ = g z θ) (j i : ℕ) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.mixed j i f z θ = Work.Spaces.mixed j i g z θ := by
  have hDth : ∀ i : ℕ, ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.DthIter i f z θ = Work.Spaces.DthIter i g z θ := by
    intro i
    induction i with
    | zero => exact fun z θ hz h1 h2 => h z θ hz h1 h2
    | succ n ih =>
      intro z θ hz h1 h2
      have heq : (fun θ' => Work.Spaces.DthIter n f z θ')
          =ᶠ[𝓝 θ] (fun θ' => Work.Spaces.DthIter n g z θ') := by
        filter_upwards [isOpen_Ioo.mem_nhds (show θ ∈ Set.Ioo 0 (Real.pi / 2) from ⟨h1, h2⟩)]
          with θ' hθ'
        exact ih z θ' hz hθ'.1 hθ'.2
      simp only [Work.Spaces.DthIter_succ, Work.Spaces.Dth, Work.Spaces.pth]
      rw [heq.deriv_eq]
  intro z θ hz h1 h2
  simp only [Work.Spaces.mixed]
  exact Work.FTS.EllipticEst.SmoothOpen.DzIter_congr
    (F := Work.Spaces.DthIter i f) (G := Work.Spaces.DthIter i g)
    (fun z θ hz h1 h2 => hDth i z θ hz h1 h2) j z θ hz h1 h2

end Work.FTS.StrongEps.EpsConvTau

namespace Work.FTS.StrongEps

open Work.FTS.Galerkin (Fn Fam slice)

-- the statement carries the hypothesis `hφ`, which the proof does not need
set_option linter.unusedVariables false in
theorem EpsConvAllTau {α B T : ℝ} (hα : 0 < α) {G : ℕ → Work.FTS.Galerkin.Fam}
    {F : ℝ → Work.FTS.Galerkin.Fn} {φ : ℕ → ℕ}
    (hφ : StrictMono φ)
    (hsm : ∀ n : ℕ, ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ k : ℕ,
      ContDiffOn ℝ k (Function.uncurry (Work.FTS.Galerkin.slice (G n) τ))
        Work.FTS.EllipticEst.Q0)
    (hhon : ∀ n : ℕ, ∀ τ ∈ Set.Icc (0 : ℝ) T,
      Work.Spaces.HkMem α 6 (Work.FTS.Galerkin.slice (G n) τ))
    (hb : ∀ n : ℕ, ∀ τ ∈ Set.Icc (0 : ℝ) T,
      Work.Spaces.HkNorm α 6 (Work.FTS.Galerkin.slice (G n) τ) ≤ B)
    (hconv : ∀ τ ∈ Set.Icc (0 : ℝ) T ∩ Set.range (fun q : ℚ => (q : ℝ)),
      Work.FTS.StrongEps.ConvLev0H6 α B (fun n => Work.FTS.Galerkin.slice (G (φ n)) τ)
        (F τ))
    (hequi : ∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ Work.FTS.EllipticEst.Q0 →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, ∀ p ∈ K, ∀ τ ∈ Set.Icc (0 : ℝ) T,
        ∀ τ' ∈ Set.Icc (0 : ℝ) T,
          |Work.FTS.Galerkin.slice (G n) τ p.1 p.2
            - Work.FTS.Galerkin.slice (G n) τ' p.1 p.2| ≤ C * |τ - τ'|) :
    ∀ τ ∈ Set.Icc (0 : ℝ) T, ∃ f : Work.FTS.Galerkin.Fn,
      Work.FTS.StrongEps.ConvLocUnifH6 α B (fun n => Work.FTS.Galerkin.slice (G (φ n)) τ)
        f := by
  intro τ hτ
  -- **Step 1.** the profiles at `τ` are uniformly Cauchy on every compact subset of `Q0`:
  -- `hequi` compares them with the profiles at a rational time, where `hconv` gives convergence.
  have hcau : ∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ Work.FTS.EllipticEst.Q0 →
      ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N, ∀ p ∈ K,
        |slice (G (φ m)) τ p.1 p.2 - slice (G (φ n)) τ p.1 p.2| < ε := by
    intro K hK hKQ ε hε
    obtain ⟨C, hC, hCe⟩ := hequi K hK hKQ
    exact EpsConvH.uniform_cauchy_of_dense_lipschitz (X := ℝ × ℝ) (s := K) (T := T)
      (D := Set.range (fun q : ℚ => (q : ℝ)))
      (u := fun σ n p => slice (G (φ n)) σ p.1 p.2) (C := C) hC
      (fun τ' hτ' δ hδ => EpsConvH.exists_rat_mem_Icc_close hτ' hδ)
      (fun σ hσ σ' hσ' n p hp => hCe (φ n) p hp σ hσ σ' hσ')
      (fun σ hσ => by
        refine ⟨fun p => F σ p.1 p.2, fun ε' hε' => ?_⟩
        have h := (Metric.tendstoUniformlyOn_iff.mp ((hconv σ hσ).1 K hK hKQ)) ε' hε'
        filter_upwards [h] with n hn p hp
        have hn' := hn p hp
        rw [Real.dist_eq, abs_sub_comm] at hn'
        exact hn')
      τ hτ ε hε
  -- **Step 2.** the extraction at the given time `τ` (this is where the honesty hypotheses are
  -- consumed); it produces the candidate limit `g` and its `C⁴`- and `ℋ⁶`-clauses.
  obtain ⟨ψ, g, hψ, hg⟩ := Work.FTS.StrongEps.EpsConvSubseq (α := α) (B := B) hα
    (G := fun n => slice (G (φ n)) τ)
    (fun n k => hsm (φ n) τ hτ k)
    (fun n => hhon (φ n) τ hτ)
    (fun n => hb (φ n) τ hτ)
  refine ⟨g, ?_, hg.2.1, hg.2.2⟩
  -- the profiles of the *full* sequence converge to `g` (Cauchy + convergent subsequence)
  have hfullAll : ∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ Work.FTS.EllipticEst.Q0 →
      TendstoUniformlyOn (fun n (p : ℝ × ℝ) => slice (G (φ n)) τ p.1 p.2)
        (fun p => g p.1 p.2) atTop K := by
    intro K hK hKQ
    refine EpsConvH.of_uniform_cauchy hψ.tendsto_atTop ?_ ?_
    · intro ε hε
      obtain ⟨N, hN⟩ := hcau K hK hKQ ε hε
      exact ⟨N, fun m hm n hn x hx => by rw [Real.dist_eq]; exact hN m hm n hn x hx⟩
    · have h := hg.1 K hK hKQ 0 0 (by norm_num)
      simpa only [Function.comp_def, Work.Spaces.mixed_zero_right, Work.Spaces.DzIter_zero]
        using h
  -- **Steps 3 and 4.** every subsequence has a further subsequence with the *same* limit; the
  -- sub-subsequence principle then gives the slot convergence of the full sequence.
  intro K hK hKQ j i hji
  refine EpsConvTau.tendstoUniformlyOn_of_subseq ?_
  intro u hu
  obtain ⟨ψ', g', hψ', hg'⟩ := Work.FTS.StrongEps.EpsConvSubseq (α := α) (B := B) hα
    (G := fun n => slice (G (φ (u n))) τ)
    (fun n k => hsm (φ (u n)) τ hτ k)
    (fun n => hhon (φ (u n)) τ hτ)
    (fun n => hb (φ (u n)) τ hτ)
  refine ⟨ψ', hψ'.tendsto_atTop, ?_⟩
  -- the further extraction has the same profile limit as the extraction of step 2
  have hfullAll' : ∀ K' : Set (ℝ × ℝ), IsCompact K' → K' ⊆ Work.FTS.EllipticEst.Q0 →
      TendstoUniformlyOn (fun n (p : ℝ × ℝ) => slice (G (φ n)) τ p.1 p.2)
        (fun p => g' p.1 p.2) atTop K' := by
    intro K' hK' hK'Q
    refine EpsConvH.of_uniform_cauchy (hu.comp hψ'.tendsto_atTop) ?_ ?_
    · intro ε hε
      obtain ⟨N, hN⟩ := hcau K' hK' hK'Q ε hε
      exact ⟨N, fun m hm n hn x hx => by rw [Real.dist_eq]; exact hN m hm n hn x hx⟩
    · have h := hg'.1 K' hK' hK'Q 0 0 (by norm_num)
      simpa only [Function.comp_def, Work.Spaces.mixed_zero_right, Work.Spaces.DzIter_zero]
        using h
  have hEqOn : ∀ p ∈ Work.FTS.EllipticEst.Q0, g' p.1 p.2 = g p.1 p.2 := by
    intro p hp
    have hsub : ({p} : Set (ℝ × ℝ)) ⊆ Work.FTS.EllipticEst.Q0 := by
      intro q hq
      rw [Set.mem_singleton_iff] at hq
      rwa [hq]
    exact tendsto_nhds_unique
      ((hfullAll' {p} isCompact_singleton hsub).tendsto_at (Set.mem_singleton p))
      ((hfullAll {p} isCompact_singleton hsub).tendsto_at (Set.mem_singleton p))
  -- on the open quadrant the two limits have the same slots, hence so do they on `K`
  have hslotEq : ∀ p ∈ K,
      Work.Spaces.mixed j i g' p.1 p.2 = Work.Spaces.mixed j i g p.1 p.2 := by
    intro p hp
    obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp (hKQ hp)
    exact EpsConvTau.mixed_congr_of_quad
      (fun z θ hz hθ0 hθ1 => hEqOn (z, θ) (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ0, hθ1⟩))
      j i p.1 p.2 hz hθ0 hθ1
  exact (hg'.1 K hK hKQ j i hji).congr_right hslotEq

end Work.FTS.StrongEps
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsRHSPBound =====
section

set_option synthInstance.maxHeartbeats 400000 -- v435-synth

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000


/-! ## The correction bound -/


end Work.FTS.StrongEps
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsRHSP_slotSup_corr =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ContDiff
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps


end Work.FTS.StrongEps
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsRHSP_slotSup_fam =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ContDiff
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps


end Work.FTS.StrongEps
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.rowDthCoef =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Pair6Aux.T6Coef

set_option maxHeartbeats 1600000

theorem rowDthCoef : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1,
    ∀ (A f : Work.FTS.Galerkin.Fn) (K0 K4 K6 M : ℝ) (a b : ℕ) (ρ : ℝ → ℝ → ℝ),
      Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.CoefData α A K0 K4 K6 →
      Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.DatData α f M →
      a + b ≤ 6 → Work.FTS.TransportS.IsLeafW α a ρ →
      |Work.FTS.TransportS.slotPairing ρ a b (fun z θ => A z θ * Work.Spaces.Dth f z θ) f|
        ≤ C * α ^ (-(3 : ℝ))
            * ((1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f)
               + (K4 + K6) * (1 + M) * (1 + Work.Spaces.HkNorm α 6 f)) := by
  obtain ⟨C1, hC1pos, hper⟩ := RowDth.perTermDthMine
  obtain ⟨C2, hC2pos, hzer⟩ := RowDth.zeroTermDth
  refine ⟨C2 + 64 * C1, by positivity, ?_⟩
  intro α hαmem A f K0 K4 K6 M a b ρ hcoef hdat hab hleaf
  have hα0 : 0 < α := hαmem.1
  have hα1 : α ≤ 1 := hαmem.2
  have hK0nn : 0 ≤ K0 :=
    le_trans (abs_nonneg (A 1 (Real.pi / 4)))
      (hcoef.val 1 (Real.pi / 4) (by norm_num) (by positivity)
        (by linarith [Real.pi_pos]))
  have hK4nn : 0 ≤ K4 := le_trans (Work.Spaces.HkNorm_nonneg α 4 A) hcoef.n4
  have hK6nn : 0 ≤ K6 := le_trans (Work.Spaces.HkNorm_nonneg α 6 A) hcoef.n6
  have hMnn : 0 ≤ M := le_trans (Work.Spaces.HkNorm_nonneg α 4 f) hdat.bdd
  have hSq6nn : 0 ≤ Work.Spaces.HkSq α 6 f := Work.Spaces.HkSq_nonneg α 6 f
  have hX6nn : 0 ≤ Work.Spaces.HkNorm α 6 f := Work.Spaces.HkNorm_nonneg α 6 f
  have hC1nn : 0 ≤ C1 := hC1pos.le
  have hC2nn : 0 ≤ C2 := hC2pos.le
  have hzer' := hzer α hαmem A f K0 K4 K6 M a b ρ hcoef hdat hab hleaf
  -- ## the pointwise Leibniz expansion on the open quadrant
  have hpt : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.mixed b a (fun z θ => A z θ * Work.Spaces.Dth f z θ) z θ
        = A z θ * Work.Spaces.Dth (Work.Spaces.mixed b a f) z θ
          + ∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1),
              (if i = 0 ∧ j = 0 then 0
                else ((a.choose i : ℝ) * (b.choose j : ℝ))
                  * (Work.Spaces.mixed j i A z θ
                      * Work.Spaces.mixed (b - j) (a - i + 1) f z θ)) := by
    intro z θ hz hθ0 hθ1
    have h := Work.FTS.StrongPersist.N6Trans.T1SixAux.leibnizRem6 (f := A) (g := f)
      hcoef.sm hdat.sm a b z θ hz hθ0 hθ1
    linarith
  -- ## the pointwise identity for the full integrand
  have hfull : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      ρ z θ * Work.Spaces.mixed b a (fun z θ => A z θ * Work.Spaces.Dth f z θ) z θ
          * Work.Spaces.mixed b a f z θ
        = ρ z θ * A z θ * Work.Spaces.Dth (Work.Spaces.mixed b a f) z θ
            * Work.Spaces.mixed b a f z θ
          + ∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1),
              (if i = 0 ∧ j = 0 then 0
                else ((a.choose i : ℝ) * (b.choose j : ℝ))
                  * (ρ z θ * Work.Spaces.mixed j i A z θ
                      * Work.Spaces.mixed (b - j) (a - i + 1) f z θ
                      * Work.Spaces.mixed b a f z θ)) := by
    intro z θ hz hθ0 hθ1
    rw [hpt z θ hz hθ0 hθ1]
    rw [show ρ z θ * (A z θ * Work.Spaces.Dth (Work.Spaces.mixed b a f) z θ
            + ∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1),
                (if i = 0 ∧ j = 0 then 0
                  else ((a.choose i : ℝ) * (b.choose j : ℝ))
                    * (Work.Spaces.mixed j i A z θ
                        * Work.Spaces.mixed (b - j) (a - i + 1) f z θ)))
          * Work.Spaces.mixed b a f z θ
        = ρ z θ * A z θ * Work.Spaces.Dth (Work.Spaces.mixed b a f) z θ
            * Work.Spaces.mixed b a f z θ
          + ρ z θ * (∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1),
                (if i = 0 ∧ j = 0 then 0
                  else ((a.choose i : ℝ) * (b.choose j : ℝ))
                    * (Work.Spaces.mixed j i A z θ
                        * Work.Spaces.mixed (b - j) (a - i + 1) f z θ)))
            * Work.Spaces.mixed b a f z θ from by ring]
    congr 1
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    by_cases h : i = 0 ∧ j = 0
    · rw [if_pos h, if_pos h]; ring
    · rw [if_neg h, if_neg h]; ring
  -- ## the θ-slice identity for z > 0
  have hslice : ∀ z ∈ Set.Ioi (0 : ℝ),
      (∫ θ in Work.Spaces.Iθ, ρ z θ * Work.Spaces.mixed b a
            (fun z θ => A z θ * Work.Spaces.Dth f z θ) z θ
          * Work.Spaces.mixed b a f z θ)
        = (∫ θ in Work.Spaces.Iθ, ρ z θ * A z θ
              * Work.Spaces.Dth (Work.Spaces.mixed b a f) z θ
              * Work.Spaces.mixed b a f z θ)
          + ∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1),
              (if i = 0 ∧ j = 0 then 0
                else ((a.choose i : ℝ) * (b.choose j : ℝ))
                  * (∫ θ in Work.Spaces.Iθ, ρ z θ * Work.Spaces.mixed j i A z θ
                      * Work.Spaces.mixed (b - j) (a - i + 1) f z θ
                      * Work.Spaces.mixed b a f z θ)) := by
    intro z hz
    have hzIz : z ∈ Work.Spaces.Iz := by
      simp only [Work.Spaces.Iz, Set.mem_Ici]; exact le_of_lt hz
    have hae : (fun θ : ℝ => ρ z θ * Work.Spaces.mixed b a
            (fun z θ => A z θ * Work.Spaces.Dth f z θ) z θ
          * Work.Spaces.mixed b a f z θ)
        =ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
        (fun θ : ℝ => ρ z θ * A z θ * Work.Spaces.Dth (Work.Spaces.mixed b a f) z θ
              * Work.Spaces.mixed b a f z θ
            + ∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1),
                (if i = 0 ∧ j = 0 then 0
                  else ((a.choose i : ℝ) * (b.choose j : ℝ))
                    * (ρ z θ * Work.Spaces.mixed j i A z θ
                        * Work.Spaces.mixed (b - j) (a - i + 1) f z θ
                        * Work.Spaces.mixed b a f z θ))) := by
      rw [RowDth.restrict_Iθ_eq_Ioo]
      refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
      exact hfull z θ hz hθ.1 hθ.2
    rw [MeasureTheory.integral_congr_ae hae]
    have h2int : MeasureTheory.IntegrableOn (fun θ : ℝ =>
          ∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1),
            (if i = 0 ∧ j = 0 then 0
              else ((a.choose i : ℝ) * (b.choose j : ℝ))
                * (ρ z θ * Work.Spaces.mixed j i A z θ
                    * Work.Spaces.mixed (b - j) (a - i + 1) f z θ
                    * Work.Spaces.mixed b a f z θ))) Work.Spaces.Iθ := by
      refine MeasureTheory.integrable_finsetSum _ (fun i hi => ?_)
      refine MeasureTheory.integrable_finsetSum _ (fun j hj => ?_)
      by_cases h : i = 0 ∧ j = 0
      · simp only [if_pos h]; exact MeasureTheory.integrableOn_zero
      · simp only [if_neg h]
        have hi' : i ≤ a := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        have hj' : j ≤ b := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
        exact ((hper α hαmem A f K0 K4 K6 M a b i j ρ hcoef hdat hab hleaf hi' hj' h).1
          z hzIz).const_mul _
    rw [MeasureTheory.integral_add (hzer'.1 z hzIz) h2int]
    congr 1
    rw [MeasureTheory.integral_finsetSum]
    · refine Finset.sum_congr rfl (fun i hi => ?_)
      rw [MeasureTheory.integral_finsetSum]
      · refine Finset.sum_congr rfl (fun j hj => ?_)
        by_cases h : i = 0 ∧ j = 0
        · simp only [if_pos h, MeasureTheory.integral_zero]
        · simp only [if_neg h]
          rw [MeasureTheory.integral_const_mul]
      · intro j hj
        by_cases h : i = 0 ∧ j = 0
        · simp only [if_pos h]; exact MeasureTheory.integrableOn_zero
        · simp only [if_neg h]
          have hi' : i ≤ a := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
          have hj' : j ≤ b := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
          exact ((hper α hαmem A f K0 K4 K6 M a b i j ρ hcoef hdat hab hleaf hi' hj' h).1
            z hzIz).const_mul _
    · intro i hi
      refine MeasureTheory.integrable_finsetSum _ (fun j hj => ?_)
      by_cases h : i = 0 ∧ j = 0
      · simp only [if_pos h]; exact MeasureTheory.integrableOn_zero
      · simp only [if_neg h]
        have hi' : i ≤ a := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        have hj' : j ≤ b := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
        exact ((hper α hαmem A f K0 K4 K6 M a b i j ρ hcoef hdat hab hleaf hi' hj' h).1
          z hzIz).const_mul _
  -- ## the double-integral identity
  have hdouble : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, ρ z θ
        * Work.Spaces.mixed b a (fun z θ => A z θ * Work.Spaces.Dth f z θ) z θ
        * Work.Spaces.mixed b a f z θ)
      = (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, ρ z θ * A z θ
            * Work.Spaces.Dth (Work.Spaces.mixed b a f) z θ
            * Work.Spaces.mixed b a f z θ)
        + ∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1),
            (if i = 0 ∧ j = 0 then 0
              else ((a.choose i : ℝ) * (b.choose j : ℝ))
                * (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, ρ z θ
                    * Work.Spaces.mixed j i A z θ
                    * Work.Spaces.mixed (b - j) (a - i + 1) f z θ
                    * Work.Spaces.mixed b a f z θ)) := by
    have hzae : (fun z : ℝ => ∫ θ in Work.Spaces.Iθ, ρ z θ
          * Work.Spaces.mixed b a (fun z θ => A z θ * Work.Spaces.Dth f z θ) z θ
          * Work.Spaces.mixed b a f z θ)
        =ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iz]
        (fun z : ℝ => (∫ θ in Work.Spaces.Iθ, ρ z θ * A z θ
              * Work.Spaces.Dth (Work.Spaces.mixed b a f) z θ
              * Work.Spaces.mixed b a f z θ)
            + ∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1),
                (if i = 0 ∧ j = 0 then 0
                  else ((a.choose i : ℝ) * (b.choose j : ℝ))
                    * (∫ θ in Work.Spaces.Iθ, ρ z θ * Work.Spaces.mixed j i A z θ
                        * Work.Spaces.mixed (b - j) (a - i + 1) f z θ
                        * Work.Spaces.mixed b a f z θ))) := by
      rw [RowDth.restrict_Iz_eq_Ioi]
      exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi
        (fun z hz => hslice z hz)
    rw [MeasureTheory.integral_congr_ae hzae]
    have hSint : MeasureTheory.IntegrableOn (fun z : ℝ => ∑ i ∈ Finset.range (a + 1),
          ∑ j ∈ Finset.range (b + 1),
                (if i = 0 ∧ j = 0 then 0
                  else ((a.choose i : ℝ) * (b.choose j : ℝ))
                    * (∫ θ in Work.Spaces.Iθ, ρ z θ * Work.Spaces.mixed j i A z θ
                        * Work.Spaces.mixed (b - j) (a - i + 1) f z θ
                        * Work.Spaces.mixed b a f z θ))) Work.Spaces.Iz := by
      refine MeasureTheory.integrable_finsetSum _ (fun i hi => ?_)
      refine MeasureTheory.integrable_finsetSum _ (fun j hj => ?_)
      by_cases h : i = 0 ∧ j = 0
      · simp only [if_pos h]; exact MeasureTheory.integrableOn_zero
      · simp only [if_neg h]
        have hi' : i ≤ a := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        have hj' : j ≤ b := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
        exact ((hper α hαmem A f K0 K4 K6 M a b i j ρ hcoef hdat hab hleaf hi' hj' h).2.1).const_mul _
    rw [MeasureTheory.integral_add hzer'.2.1 hSint]
    congr 1
    rw [MeasureTheory.integral_finsetSum]
    · refine Finset.sum_congr rfl (fun i hi => ?_)
      rw [MeasureTheory.integral_finsetSum]
      · refine Finset.sum_congr rfl (fun j hj => ?_)
        by_cases h : i = 0 ∧ j = 0
        · simp only [if_pos h, MeasureTheory.integral_zero]
        · simp only [if_neg h]
          rw [MeasureTheory.integral_const_mul]
      · intro j hj
        by_cases h : i = 0 ∧ j = 0
        · simp only [if_pos h]; exact MeasureTheory.integrableOn_zero
        · simp only [if_neg h]
          have hi' : i ≤ a := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
          have hj' : j ≤ b := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
          exact ((hper α hαmem A f K0 K4 K6 M a b i j ρ hcoef hdat hab hleaf hi' hj' h).2.1).const_mul _
    · intro i hi
      refine MeasureTheory.integrable_finsetSum _ (fun j hj => ?_)
      by_cases h : i = 0 ∧ j = 0
      · simp only [if_pos h]; exact MeasureTheory.integrableOn_zero
      · simp only [if_neg h]
        have hi' : i ≤ a := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        have hj' : j ≤ b := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
        exact ((hper α hαmem A f K0 K4 K6 M a b i j ρ hcoef hdat hab hleaf hi' hj' h).2.1).const_mul _
  -- ## the bound on the remainder sum
  have hsumBound : (∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1),
          (if i = 0 ∧ j = 0 then 0
            else ((a.choose i : ℝ) * (b.choose j : ℝ))
              * |∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, ρ z θ
                  * Work.Spaces.mixed j i A z θ
                  * Work.Spaces.mixed (b - j) (a - i + 1) f z θ
                  * Work.Spaces.mixed b a f z θ|))
      ≤ 64 * C1 * (α ^ (-(1 / 2 : ℝ))
          * ((1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f)
              + (K4 + K6) * (1 + M) * (1 + Work.Spaces.HkNorm α 6 f))) := by
    have hQ0 : 0 ≤ (1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f)
        + (K4 + K6) * (1 + M) * (1 + Work.Spaces.HkNorm α 6 f) := by positivity
    have hP0 : 0 ≤ C1 * α ^ (-(1 / 2 : ℝ))
        * ((1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f)
            + (K4 + K6) * (1 + M) * (1 + Work.Spaces.HkNorm α 6 f)) :=
      mul_nonneg (mul_nonneg hC1nn (Real.rpow_nonneg hα0.le _)) hQ0
    have hstep : (∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1),
          (if i = 0 ∧ j = 0 then 0
            else ((a.choose i : ℝ) * (b.choose j : ℝ))
              * |∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, ρ z θ
                  * Work.Spaces.mixed j i A z θ
                  * Work.Spaces.mixed (b - j) (a - i + 1) f z θ
                  * Work.Spaces.mixed b a f z θ|))
        ≤ ∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1),
            ((a.choose i : ℝ) * (b.choose j : ℝ)) * (C1 * α ^ (-(1 / 2 : ℝ))
                * ((1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f)
                    + (K4 + K6) * (1 + M) * (1 + Work.Spaces.HkNorm α 6 f))) := by
      refine Finset.sum_le_sum (fun i hi => Finset.sum_le_sum (fun j hj => ?_))
      by_cases h : i = 0 ∧ j = 0
      · rw [if_pos h]
        exact mul_nonneg (by positivity) hP0
      · rw [if_neg h]
        have hi' : i ≤ a := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        have hj' : j ≤ b := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact (hper α hαmem A f K0 K4 K6 M a b i j ρ hcoef hdat hab hleaf hi' hj' h).2.2
    refine le_trans hstep ?_
    have hbinom : (∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1),
        ((a.choose i : ℝ) * (b.choose j : ℝ))) = (2 : ℝ) ^ a * (2 : ℝ) ^ b := by
      rw [← Finset.sum_mul_sum]
      congr 1
      · exact_mod_cast Nat.sum_range_choose a
      · exact_mod_cast Nat.sum_range_choose b
    have hpow : (2 : ℝ) ^ a * (2 : ℝ) ^ b ≤ 64 := by
      rw [← pow_add]
      calc (2 : ℝ) ^ (a + b) ≤ (2 : ℝ) ^ 6 :=
            pow_le_pow_right₀ (by norm_num) hab
        _ = 64 := by norm_num
    have hsum_eq : (∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1),
            ((a.choose i : ℝ) * (b.choose j : ℝ)) * (C1 * α ^ (-(1 / 2 : ℝ))
                * ((1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f)
                    + (K4 + K6) * (1 + M) * (1 + Work.Spaces.HkNorm α 6 f))))
        = ((2 : ℝ) ^ a * (2 : ℝ) ^ b) * (C1 * α ^ (-(1 / 2 : ℝ))
              * ((1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f)
                  + (K4 + K6) * (1 + M) * (1 + Work.Spaces.HkNorm α 6 f))) := by
      rw [← hbinom]
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun i hi => ?_)
      rw [Finset.sum_mul]
    rw [hsum_eq]
    calc ((2 : ℝ) ^ a * (2 : ℝ) ^ b) * (C1 * α ^ (-(1 / 2 : ℝ))
            * ((1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f)
                + (K4 + K6) * (1 + M) * (1 + Work.Spaces.HkNorm α 6 f)))
        ≤ 64 * (C1 * α ^ (-(1 / 2 : ℝ))
            * ((1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f)
                + (K4 + K6) * (1 + M) * (1 + Work.Spaces.HkNorm α 6 f))) :=
          mul_le_mul_of_nonneg_right hpow hP0
      _ = 64 * C1 * (α ^ (-(1 / 2 : ℝ))
            * ((1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f)
                + (K4 + K6) * (1 + M) * (1 + Work.Spaces.HkNorm α 6 f))) := by ring
  -- ## the bound on the hard term plus the remainder
  have hmain : |(∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, ρ z θ * A z θ
            * Work.Spaces.Dth (Work.Spaces.mixed b a f) z θ
            * Work.Spaces.mixed b a f z θ)
        + ∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1),
            (if i = 0 ∧ j = 0 then 0
              else ((a.choose i : ℝ) * (b.choose j : ℝ))
                * (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, ρ z θ
                    * Work.Spaces.mixed j i A z θ
                    * Work.Spaces.mixed (b - j) (a - i + 1) f z θ
                    * Work.Spaces.mixed b a f z θ))|
      ≤ C2 * α ^ (-(1 / 2 : ℝ)) * (K0 + K4) * (1 + Work.Spaces.HkSq α 6 f)
        + ∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1),
            (if i = 0 ∧ j = 0 then 0
              else ((a.choose i : ℝ) * (b.choose j : ℝ))
                * |∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, ρ z θ
                    * Work.Spaces.mixed j i A z θ
                    * Work.Spaces.mixed (b - j) (a - i + 1) f z θ
                    * Work.Spaces.mixed b a f z θ|) := by
    refine le_trans (abs_add_le _ _) (add_le_add ?_ ?_)
    · exact hzer'.2.2
    · refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      refine Finset.sum_le_sum (fun i hi => ?_)
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      refine Finset.sum_le_sum (fun j hj => ?_)
      by_cases h : i = 0 ∧ j = 0
      · simp only [if_pos h, abs_zero]
        exact le_refl 0
      · simp only [if_neg h]
        rw [abs_mul, abs_mul,
          abs_of_nonneg (by positivity : (0 : ℝ) ≤ (a.choose i : ℝ)),
          abs_of_nonneg (by positivity : (0 : ℝ) ≤ (b.choose j : ℝ))]
  -- ## assembly
  rw [Work.FTS.TransportS.slotPairing]
  rw [hdouble]
  refine le_trans hmain (le_trans (add_le_add le_rfl hsumBound) ?_)
  -- ## the arithmetic
  have hα3 : (1 : ℝ) ≤ α ^ (-(3 : ℝ)) := by
    have h := Real.rpow_le_rpow_of_exponent_ge hα0 hα1 (show -(3 : ℝ) ≤ 0 by norm_num)
    rwa [Real.rpow_zero] at h
  have hαle : α ^ (-(1 / 2 : ℝ)) ≤ α ^ (-(3 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_ge hα0 hα1 (by norm_num)
  have hBnn : 0 ≤ (1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f)
              + (K4 + K6) * (1 + M) * (1 + Work.Spaces.HkNorm α 6 f) := by positivity
  have hKle : (K0 + K4) * (1 + Work.Spaces.HkSq α 6 f)
      ≤ (1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f)
              + (K4 + K6) * (1 + M) * (1 + Work.Spaces.HkNorm α 6 f) := by
    have h1 : (K0 + K4) * (1 + Work.Spaces.HkSq α 6 f)
        ≤ (1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f) :=
      mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    have h2 : (0 : ℝ) ≤ (K4 + K6) * (1 + M) * (1 + Work.Spaces.HkNorm α 6 f) := by positivity
    linarith
  have hterm1 : C2 * α ^ (-(1 / 2 : ℝ)) * (K0 + K4) * (1 + Work.Spaces.HkSq α 6 f)
      ≤ C2 * (α ^ (-(3 : ℝ)) * ((1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f)
              + (K4 + K6) * (1 + M) * (1 + Work.Spaces.HkNorm α 6 f))) := by
    have h3 : α ^ (-(1 / 2 : ℝ)) * ((K0 + K4) * (1 + Work.Spaces.HkSq α 6 f))
        ≤ α ^ (-(3 : ℝ)) * ((1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f)
              + (K4 + K6) * (1 + M) * (1 + Work.Spaces.HkNorm α 6 f)) := by
      calc α ^ (-(1 / 2 : ℝ)) * ((K0 + K4) * (1 + Work.Spaces.HkSq α 6 f))
          ≤ α ^ (-(3 : ℝ)) * ((K0 + K4) * (1 + Work.Spaces.HkSq α 6 f)) :=
            mul_le_mul_of_nonneg_right hαle (by positivity)
        _ ≤ α ^ (-(3 : ℝ)) * ((1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f)
              + (K4 + K6) * (1 + M) * (1 + Work.Spaces.HkNorm α 6 f)) :=
            mul_le_mul_of_nonneg_left hKle (Real.rpow_nonneg hα0.le _)
    calc C2 * α ^ (-(1 / 2 : ℝ)) * (K0 + K4) * (1 + Work.Spaces.HkSq α 6 f)
        = C2 * (α ^ (-(1 / 2 : ℝ)) * ((K0 + K4) * (1 + Work.Spaces.HkSq α 6 f))) := by ring
      _ ≤ C2 * (α ^ (-(3 : ℝ)) * ((1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f)
              + (K4 + K6) * (1 + M) * (1 + Work.Spaces.HkNorm α 6 f))) := mul_le_mul_of_nonneg_left h3 hC2nn
  have hterm2 : 64 * C1 * (α ^ (-(1 / 2 : ℝ)) * ((1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f)
              + (K4 + K6) * (1 + M) * (1 + Work.Spaces.HkNorm α 6 f)))
      ≤ 64 * C1 * (α ^ (-(3 : ℝ)) * ((1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f)
              + (K4 + K6) * (1 + M) * (1 + Work.Spaces.HkNorm α 6 f))) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hαle hBnn) (by positivity)
  have hsplit : (C2 + 64 * C1) * α ^ (-(3 : ℝ)) * ((1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f)
              + (K4 + K6) * (1 + M) * (1 + Work.Spaces.HkNorm α 6 f))
      = C2 * (α ^ (-(3 : ℝ)) * ((1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f)
              + (K4 + K6) * (1 + M) * (1 + Work.Spaces.HkNorm α 6 f)))
        + 64 * C1 * (α ^ (-(3 : ℝ)) * ((1 + K0 + K4) * (1 + Work.Spaces.HkSq α 6 f)
              + (K4 + K6) * (1 + M) * (1 + Work.Spaces.HkNorm α 6 f))) := by ring
  linarith [hterm1, hterm2, hsplit]

end Work.FTS.StrongPersist.H6Pair6Aux.T6Coef
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Row6.Basic =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Row6

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false


end Work.FTS.StrongPersist.H6Row6
end
end
