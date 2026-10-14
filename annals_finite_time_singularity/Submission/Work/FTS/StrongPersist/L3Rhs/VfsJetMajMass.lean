import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.H2.hard_sq_prod_z
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc
import Submission.Work.FTS.OpenPkg.ProdOpen.leibniz_open_Dz
import Submission.Work.FTS.StrongEps.EpsZero.slice_facts_of_classC
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.L12Sup6
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.DzIter_FK_eq_ae
import Submission.Work.FTS.StrongPersist.L3Rhs.VfsRadAux.aestronglyMeasurable_slotSum
import Submission.Work.FTS.StrongPersist.N6.PwOpen6
import Submission.Work.FTS.TransportS.sup_dz_le_hk
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.FTS_MuLamOK.Rows.Rl1Defs
import Submission.Work.FTS_StreamBdry.Inputs.theta_part_alt_l12fstar
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.T1Q.SliceIntQ
import Submission.Work.H2.WPQ.m_term_le_smoothQuad
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.SmoothStripDefs
import Submission.Work.Spaces.factor_bound
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0Aux.radBlk5 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0Aux

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

-- The level-four weighted radial block for the product `ρ · L₁₂(f)` with a radial multiplier
-- `ρ : ℝ → ℝ` whose `Zop`-jets (`Zop u = z·u'`) of order `≤ 4` are bounded by `Kρ`.
-- `SlotSum4 B z = Σ_{q ≤ 4} (D_z^q (fun z' _ => B z') z 0)² w(z)²` is defined in
-- `...blocks/N0Aux/B4SepDefs.lean`.  This is `Work.FTS.StrongPersist.L3Rhs.VfsRadSlotBound`
-- (orders `q ≤ 3`, jet bound the fixed `24000`) with `range 4 → range 5` and the jet bound
-- generalised to `Kρ`; the level-four slot bound `L3Aux.L12f_slot_le` (orders `≤ 4`) and the
-- Leibniz rule `FinalClock.DzIter_mul_of_contDiffOn` are already available, so the one-variable
-- Cauchy–Schwarz `(Σ_b C(q,b) X_b Y_{q-b})² ≤ (q+1)·Σ_b C(q,b)² X_b² Y_{q-b}²`
-- (`L3Rhs/VfsRadAux/sum_sq_binom_le`, capped at `q ≤ 3`; a general version exists at level six
-- as `sum_sq_binom_le_gen` in `H6N0Aux/radBlk_le7`'s cone) and the identification
-- `Zop^[b] (fun z => φ z) = DzIter b (fun z _ => φ z) · 0` (`Spaces.Zop_slice`) have to be
-- redone with one further slot; `ContDiffOn ℝ 4 (L₁₂ f) (Ioi 0)` comes from
-- `EllipticEst.UopHk.contDiffOn_L12_k` at `k = 4` (needs `SmoothOpen f`, `HkMem α 4 f`).

/-!
## Route of the proof

Everything is the level-six development `H6Pair6Aux/H6N0Aux/radBlk_le7` (`ρ · L₁₂ f`, order `6`)
shrunk to order `4`, with the general slot bound `L3Aux.L12f_slot_le` (orders `≤ 4`) in place of
its level-six analogue `L12slotLe7`:

* the product `z ↦ ρ z · L₁₂(f)(z)` is `θ`-independent, so `Zop_slice` identifies its `q`-th
  `D_z`-slot with the one-dimensional `Zop`-iterate of the radial profile, and the one-variable
  Leibniz rule `DzIter_mul_of_contDiffOn` expands
  `D_z^q (ρ · L₁₂f)(z) = ∑_{b ≤ q} C(q,b) (Zop^[b] ρ)(z) (Zop^[q-b] L₁₂f)(z)`;
* one-variable Cauchy–Schwarz in `b` against the multiplier coefficients gives
  `(D_z^q (ρ · L₁₂f)(z))² ≤ 6400 Kρ² ∑_{b ≤ 4} (Zop^[b] L₁₂f)(z)²`, hence
  `SlotSum4 (ρ·L₁₂f)(z) ≤ 32000 Kρ² ∑_{b ≤ 4} (Zop^[b] L₁₂f)(z)² w(z)²`;
* each of the five slots of `L₁₂ f` is integrable on `Iz` with integral `≤ C₁ · HkSq α 4 f`
  (`L12f_slot_le`), and `Kρ² ≤ (1 + Kρ)²`.

The two auxiliary one-variable facts used here are also available as public lemmas at
`blocks/N0Aux/radBlk5Aux/sum_sq_binom_le_gen.lean` and
`blocks/N0Aux/radBlk5Aux/aestronglyMeasurable_Zop_slotSum.lean`; they are reproduced below in
`private` form so that this module is self-contained.
-/

/-! ## One-variable facts about `Zop u = z u'` on the open half-line -/

/-- A `C^{n+1}` function on `(0,∞)` has `C^n` derivative there. -/
private theorem contDiffOn_deriv_of_succ {n : ℕ} {u : ℝ → ℝ}
    (hu : ContDiffOn ℝ (n + 1) u (Set.Ioi (0 : ℝ))) :
    ContDiffOn ℝ n (deriv u) (Set.Ioi (0 : ℝ)) := by
  have hfd : ContDiffOn ℝ n (fderiv ℝ u) (Set.Ioi (0 : ℝ)) :=
    hu.fderiv_of_isOpen isOpen_Ioi (by simp)
  have hev : ContDiffOn ℝ n (fun z : ℝ => (fderiv ℝ u z) 1) (Set.Ioi (0 : ℝ)) :=
    hfd.clm_apply contDiffOn_const
  refine hev.congr (fun z _ => ?_)
  rw [fderiv_apply_one_eq_deriv]

/-- A `C^{b+k}` function on `(0,∞)` has `C^k` `Zop`-iterates of order `b`. -/
private theorem contDiffOn_Zop_iter {u : ℝ → ℝ} (b k : ℕ)
    (hu : ContDiffOn ℝ (b + k) u (Set.Ioi (0 : ℝ))) :
    ContDiffOn ℝ k (Work.Spaces.Zop^[b] u) (Set.Ioi (0 : ℝ)) := by
  induction b generalizing k with
  | zero => simpa using hu
  | succ b ih =>
      have hu' : ContDiffOn ℝ (b + (k + 1)) u (Set.Ioi (0 : ℝ)) :=
        hu.of_le (by exact_mod_cast (by omega : b + (k + 1) ≤ (b + 1) + k))
      have h1 : ContDiffOn ℝ (k + 1) (Work.Spaces.Zop^[b] u) (Set.Ioi (0 : ℝ)) :=
        ih (k + 1) hu'
      have h2 : ContDiffOn ℝ k (deriv (Work.Spaces.Zop^[b] u)) (Set.Ioi (0 : ℝ)) :=
        contDiffOn_deriv_of_succ h1
      have h3 : ContDiffOn ℝ k (fun z : ℝ => z * deriv (Work.Spaces.Zop^[b] u) z)
          (Set.Ioi (0 : ℝ)) := (contDiff_id.contDiffOn).mul h2
      rw [Function.iterate_succ_apply']
      exact h3

/-- A `C^m` function on `(0,∞)` has a `C^{m-q}` `Zop`-iterate of order `q ≤ m`. -/
private theorem contDiffOn_Zop_iter_le {u : ℝ → ℝ} {m q : ℕ}
    (hu : ContDiffOn ℝ m u (Set.Ioi (0 : ℝ))) (hq : q ≤ m) :
    ContDiffOn ℝ (m - q) (Work.Spaces.Zop^[q] u) (Set.Ioi (0 : ℝ)) := by
  refine contDiffOn_Zop_iter q (m - q) ?_
  refine hu.of_le ?_
  exact_mod_cast (by omega : q + (m - q) ≤ m)

/-- The weighted slot sum `∑_{q ≤ m} (Zop^[q] G · w)²` of a `C^m` radial profile `G` is
a.e. strongly measurable for the restricted Lebesgue measure on `Iz = [0,∞)`. -/
private theorem aestronglyMeasurable_Zop_slotSum_gen (m : ℕ) {G : ℝ → ℝ}
    (hG : ContDiffOn ℝ m G (Set.Ioi (0 : ℝ))) :
    MeasureTheory.AEStronglyMeasurable (fun z => ∑ q ∈ Finset.range (m + 1),
        (Work.Spaces.Zop^[q] G z) ^ 2 * (Work.Spaces.w z) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
  have hw : Measurable (Work.Spaces.w) := by
    unfold Work.Spaces.w
    fun_prop
  have hZcont : ∀ q ≤ m, ContinuousOn (Work.Spaces.Zop^[q] G) (Set.Ioi (0 : ℝ)) :=
    fun q hq => (contDiffOn_Zop_iter_le (u := G) (m := m) hG hq).continuousOn
  have haesmZop : MeasureTheory.AEStronglyMeasurable (fun z => ∑ q ∈ Finset.range (m + 1),
        (Work.Spaces.Zop^[q] G z) ^ 2 * (Work.Spaces.w z) ^ 2)
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by
    have h' : MeasureTheory.AEStronglyMeasurable (∑ q ∈ Finset.range (m + 1),
        fun z : ℝ => (Work.Spaces.Zop^[q] G z) ^ 2 * (Work.Spaces.w z) ^ 2)
        (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
      Finset.aestronglyMeasurable_sum (Finset.range (m + 1))
        (f := fun q z => (Work.Spaces.Zop^[q] G z) ^ 2 * (Work.Spaces.w z) ^ 2)
        (fun q hq => by
          have hqm : q ≤ m := by
            have := Finset.mem_range.mp hq
            omega
          exact (((hZcont q hqm).aestronglyMeasurable measurableSet_Ioi).pow 2).mul
            (hw.aestronglyMeasurable.pow 2))
    refine h'.congr (Filter.Eventually.of_forall (fun z => ?_))
    simp only [Finset.sum_apply]
  have hIoi : MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))
      = MeasureTheory.volume.restrict Work.Spaces.Iz := by
    show MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))
      = MeasureTheory.volume.restrict (Set.Ici (0 : ℝ))
    exact Measure.restrict_congr_set Ioi_ae_eq_Ici
  rw [← hIoi]
  exact haesmZop

/-! ## The binomial Cauchy–Schwarz bound -/

/-- Cauchy–Schwarz for the Leibniz expansion in the order produced by the rule, i.e.
`∑_{b ≤ q} C(q,b) Y_b X_{q-b}`: with `|Y j| ≤ K` for `j ≤ n` and `q ≤ n`,

  `(∑_{b ≤ q} C(q,b) Y_b X_{q-b})² ≤ ((n+1)² 4^n K²) · ∑_{b ≤ n} X_b²`. -/
private theorem sum_sq_binom_le_gen (n : ℕ) (Y X : ℕ → ℝ) {K : ℝ} (hK : 0 ≤ K)
    (hY : ∀ j ≤ n, |Y j| ≤ K) {q : ℕ} (hq : q ≤ n) :
    (∑ b ∈ Finset.range (q + 1), (q.choose b : ℝ) * (Y b * X (q - b))) ^ 2
      ≤ (((n + 1 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ) * 4 ^ n * K ^ 2)
          * ∑ b ∈ Finset.range (n + 1), (X b) ^ 2 := by
  have hsum_eq : (∑ b ∈ Finset.range (q + 1), (q.choose b : ℝ) * (Y b * X (q - b)))
      = ∑ b ∈ Finset.range (q + 1), ((q.choose b : ℝ) * Y b) * X (q - b) := by
    refine Finset.sum_congr rfl (fun b _ => ?_)
    ring
  rw [hsum_eq]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range (q + 1))
      (fun b => (q.choose b : ℝ) * Y b) (fun b => X (q - b))
  have hf2 : ∑ b ∈ Finset.range (q + 1), ((q.choose b : ℝ) * Y b) ^ 2
      ≤ ((n + 1 : ℕ) : ℝ) * 4 ^ n * K ^ 2 := by
    have hterm : ∀ b ∈ Finset.range (q + 1),
        ((q.choose b : ℝ) * Y b) ^ 2 ≤ 4 ^ n * K ^ 2 := by
      intro b hb
      have hbq : b ≤ q := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)
      have hc0 : (0 : ℝ) ≤ (q.choose b : ℝ) := by positivity
      have hcoef : ((q.choose b : ℝ)) ^ 2 ≤ 4 ^ n := by
        have h1 : q.choose b ≤ 2 ^ q := Nat.choose_le_two_pow q b
        have h2 : 2 ^ q ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hq
        have h3 : ((q.choose b : ℕ) : ℝ) ≤ (2 : ℝ) ^ n := by
          calc ((q.choose b : ℕ) : ℝ) ≤ ((2 ^ n : ℕ) : ℝ) := by
                exact_mod_cast le_trans h1 h2
            _ = (2 : ℝ) ^ n := by push_cast; ring
        have h4 : (2 : ℝ) ^ n * (2 : ℝ) ^ n = 4 ^ n := by
          rw [← mul_pow]
          norm_num
        calc ((q.choose b : ℝ)) ^ 2 = (q.choose b : ℝ) * (q.choose b : ℝ) := by ring
          _ ≤ (2 : ℝ) ^ n * (2 : ℝ) ^ n := mul_self_le_mul_self hc0 h3
          _ = 4 ^ n := h4
      have hy : (Y b) ^ 2 ≤ K ^ 2 := by
        have h := hY b (by omega)
        exact sq_le_sq' (abs_le.mp h).1 (abs_le.mp h).2
      calc ((q.choose b : ℝ) * Y b) ^ 2
          = ((q.choose b : ℝ)) ^ 2 * (Y b) ^ 2 := by ring
        _ ≤ 4 ^ n * K ^ 2 := mul_le_mul hcoef hy (sq_nonneg _) (by positivity)
    calc ∑ b ∈ Finset.range (q + 1), ((q.choose b : ℝ) * Y b) ^ 2
        ≤ (Finset.range (q + 1)).card • (4 ^ n * K ^ 2) :=
          Finset.sum_le_card_nsmul _ _ _ hterm
      _ = ((q + 1 : ℕ) : ℝ) * (4 ^ n * K ^ 2) := by
          simp [Finset.card_range, nsmul_eq_mul]
      _ ≤ ((n + 1 : ℕ) : ℝ) * (4 ^ n * K ^ 2) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          exact_mod_cast (by omega : q + 1 ≤ n + 1)
      _ = ((n + 1 : ℕ) : ℝ) * 4 ^ n * K ^ 2 := by ring
  have hg2 : ∑ b ∈ Finset.range (q + 1), (X (q - b)) ^ 2
      ≤ ((n + 1 : ℕ) : ℝ) * ∑ b ∈ Finset.range (n + 1), (X b) ^ 2 := by
    have hterm : ∀ b ∈ Finset.range (q + 1),
        (X (q - b)) ^ 2 ≤ ∑ i ∈ Finset.range (n + 1), (X i) ^ 2 := by
      intro b hb
      have hbq : b ≤ q := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)
      refine Finset.single_le_sum (fun i _ => sq_nonneg _) ?_
      simp only [Finset.mem_range]
      omega
    calc ∑ b ∈ Finset.range (q + 1), (X (q - b)) ^ 2
        ≤ (Finset.range (q + 1)).card • (∑ i ∈ Finset.range (n + 1), (X i) ^ 2) :=
          Finset.sum_le_card_nsmul _ _ _ hterm
      _ = ((q + 1 : ℕ) : ℝ) * (∑ i ∈ Finset.range (n + 1), (X i) ^ 2) := by
          simp [Finset.card_range, nsmul_eq_mul]
      _ ≤ ((n + 1 : ℕ) : ℝ) * (∑ i ∈ Finset.range (n + 1), (X i) ^ 2) := by
          refine mul_le_mul_of_nonneg_right ?_ (Finset.sum_nonneg fun i _ => sq_nonneg _)
          exact_mod_cast (by omega : q + 1 ≤ n + 1)
  calc (∑ b ∈ Finset.range (q + 1), ((q.choose b : ℝ) * Y b) * X (q - b)) ^ 2
      ≤ (∑ b ∈ Finset.range (q + 1), ((q.choose b : ℝ) * Y b) ^ 2)
          * ∑ b ∈ Finset.range (q + 1), (X (q - b)) ^ 2 := hcs
    _ ≤ (((n + 1 : ℕ) : ℝ) * 4 ^ n * K ^ 2)
          * (((n + 1 : ℕ) : ℝ) * ∑ b ∈ Finset.range (n + 1), (X b) ^ 2) :=
        mul_le_mul hf2 hg2 (Finset.sum_nonneg fun b _ => sq_nonneg _) (by positivity)
    _ = (((n + 1 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ) * 4 ^ n * K ^ 2)
          * ∑ b ∈ Finset.range (n + 1), (X b) ^ 2 := by ring

/-! ## The main theorem -/

theorem radBlk5 : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc (0 : ℝ) 1,
    ∀ (ρ : ℝ → ℝ) (f : ℝ → ℝ → ℝ) (Kρ : ℝ),
    0 ≤ Kρ → ContDiffOn ℝ 5 ρ (Set.Ioi 0) →
    (∀ b ≤ 4, ∀ z ∈ Set.Ioi (0 : ℝ), |Work.Spaces.Zop^[b] ρ z| ≤ Kρ) →
    Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 4 f →
    Work.Construction.L12 f 0 = 0 →
    MeasureTheory.IntegrableOn
        (Work.FTS.StrongEps.E4R3.Apriori4Proofs.N0Aux.SlotSum4
          (fun z => ρ z * Work.Construction.L12 f z)) Work.Spaces.Iz ∧
    (∫ z in Work.Spaces.Iz,
        Work.FTS.StrongEps.E4R3.Apriori4Proofs.N0Aux.SlotSum4
          (fun z => ρ z * Work.Construction.L12 f z) z)
      ≤ C * (1 + Kρ) ^ 2 * Work.Spaces.HkSq α 4 f := by
  obtain ⟨C₁, hC₁pos, hC₁⟩ := Work.FTS.StrongPersist.L3Aux.L12f_slot_le
  refine ⟨32000 * (5 * C₁) + 1, by positivity, ?_⟩
  intro α hαIoc ρ f Kρ hKρ hρ5 hρbound hsm hmem h0
  have hα : 0 < α := hαIoc.1
  have hα1 : α ≤ 1 := hαIoc.2
  -- smoothness of the two factors
  have hρ4 : ContDiffOn ℝ 4 ρ (Set.Ioi (0 : ℝ)) :=
    hρ5.of_le (by exact_mod_cast (by norm_num : (4 : ℕ) ≤ 5))
  have hL4 : ContDiffOn ℝ 4 (Work.Construction.L12 f) (Set.Ioi (0 : ℝ)) :=
    Work.FTS.EllipticEst.UopHk.contDiffOn_L12_k α 4 f hα hα1 hsm hmem (by norm_num)
  -- the five weighted slots of `L₁₂ f`
  have hslot := hC₁ α hα hα1 f hsm hmem h0
  -- ## the Leibniz expansion of the slots of the product
  have hexp : ∀ q ≤ 4, ∀ z ∈ Set.Ioi (0 : ℝ),
      Work.Spaces.DzIter q (fun z _ => ρ z * Work.Construction.L12 f z) z 0
        = ∑ b ∈ Finset.range (q + 1), (q.choose b : ℝ)
            * (Work.Spaces.Zop^[b] ρ z
                * Work.Spaces.Zop^[q - b] (fun z => Work.Construction.L12 f z) z) := by
    intro q hq z hz
    have hρq : ContDiffOn ℝ q ρ (Set.Ioi (0 : ℝ)) :=
      hρ5.of_le (by exact_mod_cast (by omega : q ≤ 5))
    have hLq : ContDiffOn ℝ q (fun z' => Work.Construction.L12 f z') (Set.Ioi (0 : ℝ)) :=
      hL4.of_le (by exact_mod_cast hq)
    have h1 := Work.FTS.FinalClock.DzIter_mul_of_contDiffOn q ρ
      (fun z _ => Work.Construction.L12 f z) isOpen_Ioi (θ := 0) hρq hLq z hz
    rw [h1]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [congrFun (Work.Spaces.Zop_slice (q - b) (fun z _ => Work.Construction.L12 f z) 0) z]
  -- ## the pointwise Cauchy–Schwarz bound
  have hpt : ∀ (X Y : ℕ → ℝ) (z : ℝ), z ∈ Set.Ioi (0 : ℝ) → (∀ j ≤ 4, |Y j| ≤ Kρ) →
      (∀ q ≤ 4, Work.Spaces.DzIter q (fun z _ => ρ z * Work.Construction.L12 f z) z 0
        = ∑ b ∈ Finset.range (q + 1), (q.choose b : ℝ) * (Y b * X (q - b))) →
      (∑ q ∈ Finset.range 5,
          (Work.Spaces.DzIter q (fun z _ => ρ z * Work.Construction.L12 f z) z 0) ^ 2
            * (Work.Spaces.w z) ^ 2)
        ≤ 32000 * Kρ ^ 2 * ∑ b ∈ Finset.range 5, (X b) ^ 2 * (Work.Spaces.w z) ^ 2 := by
    intro X Y z _ hY hex
    have hsq : ∀ q ≤ 4,
        (Work.Spaces.DzIter q (fun z _ => ρ z * Work.Construction.L12 f z) z 0) ^ 2
          ≤ 6400 * Kρ ^ 2 * ∑ b ∈ Finset.range 5, (X b) ^ 2 := by
      intro q hq
      have hgen := sum_sq_binom_le_gen 4 Y X hKρ hY hq
      have hconst : (((4 + 1 : ℕ) : ℝ) * ((4 + 1 : ℕ) : ℝ) * 4 ^ 4 * Kρ ^ 2)
            * ∑ b ∈ Finset.range (4 + 1), (X b) ^ 2
          = 6400 * Kρ ^ 2 * ∑ b ∈ Finset.range 5, (X b) ^ 2 := by
        rw [show (((4 + 1 : ℕ) : ℝ) * ((4 + 1 : ℕ) : ℝ) * 4 ^ 4 * Kρ ^ 2)
            = 6400 * Kρ ^ 2 from by norm_num]
      calc (Work.Spaces.DzIter q (fun z _ => ρ z * Work.Construction.L12 f z) z 0) ^ 2
          = (∑ b ∈ Finset.range (q + 1), (q.choose b : ℝ) * (Y b * X (q - b))) ^ 2 := by
            rw [hex q hq]
        _ ≤ (((4 + 1 : ℕ) : ℝ) * ((4 + 1 : ℕ) : ℝ) * 4 ^ 4 * Kρ ^ 2)
              * ∑ b ∈ Finset.range (4 + 1), (X b) ^ 2 := hgen
        _ = 6400 * Kρ ^ 2 * ∑ b ∈ Finset.range 5, (X b) ^ 2 := hconst
    have hsum : (∑ q ∈ Finset.range 5,
        (Work.Spaces.DzIter q (fun z _ => ρ z * Work.Construction.L12 f z) z 0) ^ 2)
        ≤ 32000 * Kρ ^ 2 * ∑ b ∈ Finset.range 5, (X b) ^ 2 := by
      calc (∑ q ∈ Finset.range 5,
            (Work.Spaces.DzIter q (fun z _ => ρ z * Work.Construction.L12 f z) z 0) ^ 2)
          ≤ ∑ _q ∈ Finset.range 5,
              (6400 * Kρ ^ 2 * ∑ b ∈ Finset.range 5, (X b) ^ 2) :=
            Finset.sum_le_sum
              (fun q hq => hsq q (by rw [Finset.mem_range] at hq; omega))
        _ = 5 * (6400 * Kρ ^ 2 * ∑ b ∈ Finset.range 5, (X b) ^ 2) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
            norm_num
        _ = 32000 * Kρ ^ 2 * ∑ b ∈ Finset.range 5, (X b) ^ 2 := by ring
    calc (∑ q ∈ Finset.range 5,
            (Work.Spaces.DzIter q (fun z _ => ρ z * Work.Construction.L12 f z) z 0) ^ 2
              * (Work.Spaces.w z) ^ 2)
        = (∑ q ∈ Finset.range 5,
            (Work.Spaces.DzIter q (fun z _ => ρ z * Work.Construction.L12 f z) z 0) ^ 2)
              * (Work.Spaces.w z) ^ 2 := by rw [Finset.sum_mul]
      _ ≤ (32000 * Kρ ^ 2 * ∑ b ∈ Finset.range 5, (X b) ^ 2) * (Work.Spaces.w z) ^ 2 :=
          mul_le_mul_of_nonneg_right hsum (sq_nonneg _)
      _ = 32000 * Kρ ^ 2 * ∑ b ∈ Finset.range 5, (X b) ^ 2 * (Work.Spaces.w z) ^ 2 := by
          rw [← Finset.sum_mul]
          ring
  -- ## abbreviations for the majorant and the slot sum
  let X : ℕ → ℝ → ℝ := fun b z => Work.Spaces.Zop^[b] (fun z => Work.Construction.L12 f z) z
  let Y : ℕ → ℝ → ℝ := fun j z => Work.Spaces.Zop^[j] ρ z
  let G : ℝ → ℝ := fun z => ∑ b ∈ Finset.range 5, (X b z) ^ 2 * (Work.Spaces.w z) ^ 2
  let A : ℝ → ℝ := fun z => ∑ q ∈ Finset.range 5,
      (Work.Spaces.DzIter q (fun z _ => ρ z * Work.Construction.L12 f z) z 0) ^ 2
        * (Work.Spaces.w z) ^ 2
  have hAnn : ∀ z, 0 ≤ A z := fun z =>
    Finset.sum_nonneg (fun q _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
  have hApt : ∀ z ∈ Set.Ioi (0 : ℝ), A z ≤ 32000 * Kρ ^ 2 * G z := by
    intro z hz
    exact hpt (fun b => X b z) (fun j => Y j z) z hz
      (fun j hj => hρbound j hj z hz)
      (fun q hq => hexp q hq z hz)
  -- ## integrability of the majorant `G`
  have hGint : MeasureTheory.IntegrableOn G Work.Spaces.Iz := by
    refine MeasureTheory.integrable_finsetSum (Finset.range 5)
      (f := fun b z => (X b z) ^ 2 * (Work.Spaces.w z) ^ 2) (fun b hb => ?_)
    have hb4 : b ≤ 4 := by rw [Finset.mem_range] at hb; omega
    refine MeasureTheory.IntegrableOn.congr_fun (hslot b hb4).1 (fun z _ => ?_)
      measurableSet_Ici
    show (Work.Spaces.DzIter b (fun z _ => Work.Construction.L12 f z) z 0) ^ 2
          * (Work.Spaces.w z) ^ 2
        = (Work.Spaces.Zop^[b] (fun z => Work.Construction.L12 f z) z) ^ 2
          * (Work.Spaces.w z) ^ 2
    rw [congrFun (Work.Spaces.Zop_slice b (fun z _ => Work.Construction.L12 f z) 0) z]
  -- ## the value of the majorant integral
  have hGval : (∫ z in Work.Spaces.Iz, G z) ≤ 5 * (C₁ * Work.Spaces.HkSq α 4 f) := by
    have hfun : G = fun z => ∑ b ∈ Finset.range 5,
        (Work.Spaces.DzIter b (fun z _ => Work.Construction.L12 f z) z 0) ^ 2
          * (Work.Spaces.w z) ^ 2 := by
      funext z
      show (∑ b ∈ Finset.range 5, (Work.Spaces.Zop^[b]
              (fun z => Work.Construction.L12 f z) z) ^ 2 * (Work.Spaces.w z) ^ 2)
          = ∑ b ∈ Finset.range 5, (Work.Spaces.DzIter b
              (fun z _ => Work.Construction.L12 f z) z 0) ^ 2 * (Work.Spaces.w z) ^ 2
      refine Finset.sum_congr rfl (fun b _ => ?_)
      rw [← congrFun (Work.Spaces.Zop_slice b (fun z _ => Work.Construction.L12 f z) 0) z]
    rw [hfun]
    calc (∫ z in Work.Spaces.Iz, ∑ b ∈ Finset.range 5,
            (Work.Spaces.DzIter b (fun z _ => Work.Construction.L12 f z) z 0) ^ 2
              * (Work.Spaces.w z) ^ 2)
        = ∑ b ∈ Finset.range 5,
            (∫ z in Work.Spaces.Iz,
              (Work.Spaces.DzIter b (fun z _ => Work.Construction.L12 f z) z 0) ^ 2
                * (Work.Spaces.w z) ^ 2) :=
          MeasureTheory.integral_finsetSum (Finset.range 5)
            (fun b hb => (hslot b (by rw [Finset.mem_range] at hb; omega)).1)
      _ ≤ ∑ _b ∈ Finset.range 5, (C₁ * Work.Spaces.HkSq α 4 f) :=
          Finset.sum_le_sum
            (fun b hb => (hslot b (by rw [Finset.mem_range] at hb; omega)).2)
      _ = 5 * (C₁ * Work.Spaces.HkSq α 4 f) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          norm_num
  -- ## the a.e. statements and integrability of the slot sum
  have hIzcongr : MeasureTheory.volume.restrict Work.Spaces.Iz
      = MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)) := by
    rw [show Work.Spaces.Iz = Set.Ici (0 : ℝ) from rfl]
    exact (MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := (0 : ℝ)))).symm
  have hae_le : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      A z ≤ 32000 * Kρ ^ 2 * G z := by
    rw [hIzcongr]
    exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (fun z hz => hApt z hz)
  have hae_norm : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      ‖A z‖ ≤ 32000 * Kρ ^ 2 * G z := by
    rw [hIzcongr]
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (fun z hz => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hAnn z)]
    exact hApt z hz
  have hAesm : MeasureTheory.AEStronglyMeasurable A
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    have hProdc4 : ContDiffOn ℝ 4 (fun z => ρ z * Work.Construction.L12 f z)
        (Set.Ioi (0 : ℝ)) := hρ4.mul hL4
    have hbase := aestronglyMeasurable_Zop_slotSum_gen 4
      (G := fun z => ρ z * Work.Construction.L12 f z) hProdc4
    have hptZ : ∀ q : ℕ, ∀ z : ℝ,
        Work.Spaces.DzIter q (fun z _ => ρ z * Work.Construction.L12 f z) z 0
          = Work.Spaces.Zop^[q] (fun z => ρ z * Work.Construction.L12 f z) z := by
      intro q z
      exact congrFun
        (Work.Spaces.Zop_slice q (fun z _ => ρ z * Work.Construction.L12 f z) 0) z
    refine hbase.congr (Filter.Eventually.of_forall (fun z => ?_))
    have hAz : A z = ∑ q ∈ Finset.range 5,
        (Work.Spaces.Zop^[q] (fun z => ρ z * Work.Construction.L12 f z) z) ^ 2
          * (Work.Spaces.w z) ^ 2 := by
      show (∑ q ∈ Finset.range 5,
            (Work.Spaces.DzIter q (fun z _ => ρ z * Work.Construction.L12 f z) z 0) ^ 2
              * (Work.Spaces.w z) ^ 2) = _
      exact Finset.sum_congr rfl (fun q _ => by rw [hptZ q z])
    rw [hAz]
  have hAint : MeasureTheory.IntegrableOn A Work.Spaces.Iz :=
    MeasureTheory.Integrable.mono' (hGint.const_mul (32000 * Kρ ^ 2)) hAesm hae_norm
  have hAle : (∫ z in Work.Spaces.Iz, A z)
      ≤ 32000 * Kρ ^ 2 * (∫ z in Work.Spaces.Iz, G z) := by
    have hmono := MeasureTheory.integral_mono_of_nonneg
      (g := fun z => 32000 * Kρ ^ 2 * G z)
      (Filter.Eventually.of_forall hAnn) (hGint.const_mul (32000 * Kρ ^ 2)) hae_le
    rwa [MeasureTheory.integral_const_mul] at hmono
  refine ⟨?_, ?_⟩
  · exact hAint
  · have hS := Work.Spaces.HkSq_nonneg α 4 f
    have hA2 : 0 ≤ 32000 * (5 * C₁) := by positivity
    have hK2 : Kρ ^ 2 ≤ (1 + Kρ) ^ 2 := by nlinarith [hKρ]
    have hstep1 : 32000 * (5 * C₁) * Kρ ^ 2 * Work.Spaces.HkSq α 4 f
        ≤ 32000 * (5 * C₁) * ((1 + Kρ) ^ 2 * Work.Spaces.HkSq α 4 f) := by
      rw [show 32000 * (5 * C₁) * Kρ ^ 2 * Work.Spaces.HkSq α 4 f
          = 32000 * (5 * C₁) * (Kρ ^ 2 * Work.Spaces.HkSq α 4 f) from by ring]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hK2 hS) hA2
    have hstep2 : 32000 * (5 * C₁) * ((1 + Kρ) ^ 2 * Work.Spaces.HkSq α 4 f)
        ≤ (32000 * (5 * C₁) + 1) * ((1 + Kρ) ^ 2 * Work.Spaces.HkSq α 4 f) :=
      mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg (sq_nonneg _) hS)
    calc (∫ z in Work.Spaces.Iz, A z)
        ≤ 32000 * Kρ ^ 2 * (∫ z in Work.Spaces.Iz, G z) := hAle
      _ ≤ 32000 * Kρ ^ 2 * (5 * (C₁ * Work.Spaces.HkSq α 4 f)) :=
          mul_le_mul_of_nonneg_left hGval (by positivity)
      _ = 32000 * (5 * C₁) * Kρ ^ 2 * Work.Spaces.HkSq α 4 f := by ring
      _ ≤ 32000 * (5 * C₁) * ((1 + Kρ) ^ 2 * Work.Spaces.HkSq α 4 f) := hstep1
      _ ≤ (32000 * (5 * C₁) + 1) * ((1 + Kρ) ^ 2 * Work.Spaces.HkSq α 4 f) := hstep2
      _ = (32000 * (5 * C₁) + 1) * (1 + Kρ) ^ 2 * Work.Spaces.HkSq α 4 f := by ring

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0Aux
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.Nblock6.Tools.PtBAux.Basic =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E4R3.Nblock6.Tools
namespace PtB

open Function Set

noncomputable section

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000
/-! ## The majorant and elementary facts about it -/

/-- The weight `w z / sin(2θ)^{η/2}` carried by the pure `D_z`-slots of `HkIntegrand`. -/
abbrev Hv (z θ : ℝ) : ℝ := Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)

/-- The `MA²·I⁷_f` block: the undifferentiated coefficient paired with the top slot of `f`. -/
def Maj1 (α : ℝ) (f : ℝ → ℝ → ℝ) (MA z θ : ℝ) : ℝ :=
  MA ^ 2 * Work.Spaces.HkIntegrand α 7 f z θ

/-- The `(γ-1)⁻¹`-block: the two factors priced by the two `ℋ⁶`-norms. -/
def Maj2 (α : ℝ) (A f : ℝ → ℝ → ℝ) (z θ : ℝ) : ℝ :=
  (1 + (Work.Spaces.gam α - 1)⁻¹ * (Work.Spaces.HkSq α 6 A + Work.Spaces.HkSq α 6 f))
    * (Work.Spaces.HkIntegrand α 6 A z θ + Work.Spaces.HkIntegrand α 6 f z θ)

/-- The `KA²·I⁶_f` block: the `∂_θA`-bound paired with the order-`6` slot of `f`. -/
def Maj3 (α : ℝ) (f : ℝ → ℝ → ℝ) (KA z θ : ℝ) : ℝ :=
  KA ^ 2 * Work.Spaces.HkIntegrand α 6 f z θ

/-- The exceptional slot `D_z⁵A · D_θ²f`. -/
def Maj4 (α : ℝ) (A f : ℝ → ℝ → ℝ) (z θ : ℝ) : ℝ :=
  (Work.Spaces.DzIter 5 A z θ * Work.Spaces.mixed 1 1 f z θ * Work.Spaces.Wt α z θ) ^ 2

/-- The exceptional slot `D_zD_θA · D_z⁵f`. -/
def Maj5 (α : ℝ) (A f : ℝ → ℝ → ℝ) (z θ : ℝ) : ℝ :=
  (Work.Spaces.mixed 1 1 A z θ * Work.Spaces.DzIter 5 f z θ * Work.Spaces.Wt α z θ) ^ 2

/-- The exceptional slot `D_θA · D_z⁵f`. -/
def Maj6 (α : ℝ) (A f : ℝ → ℝ → ℝ) (z θ : ℝ) : ℝ :=
  (Work.Spaces.Dth A z θ * Work.Spaces.DzIter 5 f z θ * Work.Spaces.Wt α z θ) ^ 2

/-- The exceptional slot `D_θ²A · D_z⁵f`. -/
def Maj7 (α : ℝ) (A f : ℝ → ℝ → ℝ) (z θ : ℝ) : ℝ :=
  (Work.Spaces.DthIter 2 A z θ * Work.Spaces.DzIter 5 f z θ * Work.Spaces.Wt α z θ) ^ 2

/-- The majorant of the statement (without the constant). -/
def Maj (α : ℝ) (A f : ℝ → ℝ → ℝ) (MA KA z θ : ℝ) : ℝ :=
  Maj1 α f MA z θ + Maj2 α A f z θ + Maj3 α f KA z θ + Maj4 α A f z θ
    + Maj5 α A f z θ + Maj6 α A f z θ + Maj7 α A f z θ

theorem w_nonneg (z : ℝ) : 0 ≤ Work.Spaces.w z := by
  rw [Work.Spaces.w]; positivity

theorem gam_sub_one_pos_ptb {α : ℝ} (hα : 0 < α) : 0 < Work.Spaces.gam α - 1 := by
  rw [Work.Spaces.gam_sub_one]; linarith

theorem gam_sub_one_nonneg_ptb {α : ℝ} (hα : 0 < α) : 0 ≤ (Work.Spaces.gam α - 1)⁻¹ :=
  inv_nonneg.mpr (gam_sub_one_pos_ptb hα).le


theorem gam_le_two_add_eta {α : ℝ} (hα1 : α ≤ 1) :
    Work.Spaces.gam α ≤ 2 + Work.Spaces.eta := by
  rw [Work.Spaces.gam, Work.Spaces.eta]; linarith

/-- The square of the angular weight of the mixed slots. -/
theorem Wt_sq_eq {α z θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    (Work.Spaces.Wt α z θ) ^ 2
      = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
  have hs : 0 < Real.sin (2 * θ) := Work.FTS.OpenPkg.ProdOpen.sin_two_pos hθ
  have key : ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) ^ 2
      = (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
    rw [pow_two, ← Real.rpow_add hs]
    congr 1
    ring
  rw [Work.Spaces.Wt, Work.Spaces.wTheta, mul_pow, key]

/-- The square of the angular weight of the pure `D_z`-slots. -/
theorem Hv_sq_eq {z θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    (Hv z θ) ^ 2 = (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
  have hs : 0 < Real.sin (2 * θ) := Work.FTS.OpenPkg.ProdOpen.sin_two_pos hθ
  have hHv : Hv z θ = Work.Spaces.w z * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta / 2)) := by
    rw [Hv, div_eq_mul_inv, ← Real.rpow_neg hs.le]
  rw [hHv, mul_pow]
  congr 1
  rw [pow_two, ← Real.rpow_add hs]
  congr 1
  ring

theorem Maj1_nonneg (α : ℝ) (f : ℝ → ℝ → ℝ) (MA z θ : ℝ) : 0 ≤ Maj1 α f MA z θ := by
  rw [Maj1]; exact mul_nonneg (sq_nonneg _) (Work.Spaces.HkIntegrand_nonneg α 7 f z θ)

theorem Maj2_nonneg {α : ℝ} (hα : 0 < α) (A f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    0 ≤ Maj2 α A f z θ := by
  rw [Maj2]
  refine mul_nonneg (add_nonneg zero_le_one (mul_nonneg (gam_sub_one_nonneg_ptb hα) ?_)) ?_
  · exact add_nonneg (Work.Spaces.HkSq_nonneg α 6 A) (Work.Spaces.HkSq_nonneg α 6 f)
  · exact add_nonneg (Work.Spaces.HkIntegrand_nonneg α 6 A z θ)
      (Work.Spaces.HkIntegrand_nonneg α 6 f z θ)

theorem Maj3_nonneg (α : ℝ) (f : ℝ → ℝ → ℝ) (KA z θ : ℝ) : 0 ≤ Maj3 α f KA z θ := by
  rw [Maj3]; exact mul_nonneg (sq_nonneg _) (Work.Spaces.HkIntegrand_nonneg α 6 f z θ)

theorem Maj4_nonneg (α : ℝ) (A f : ℝ → ℝ → ℝ) (z θ : ℝ) : 0 ≤ Maj4 α A f z θ := by
  rw [Maj4]; exact sq_nonneg _

theorem Maj5_nonneg (α : ℝ) (A f : ℝ → ℝ → ℝ) (z θ : ℝ) : 0 ≤ Maj5 α A f z θ := by
  rw [Maj5]; exact sq_nonneg _

theorem Maj6_nonneg (α : ℝ) (A f : ℝ → ℝ → ℝ) (z θ : ℝ) : 0 ≤ Maj6 α A f z θ := by
  rw [Maj6]; exact sq_nonneg _

theorem Maj7_nonneg (α : ℝ) (A f : ℝ → ℝ → ℝ) (z θ : ℝ) : 0 ≤ Maj7 α A f z θ := by
  rw [Maj7]; exact sq_nonneg _

theorem Maj_nonneg {α : ℝ} (hα : 0 < α) (A f : ℝ → ℝ → ℝ) (MA KA z θ : ℝ) :
    0 ≤ Maj α A f MA KA z θ := by
  have h1 := Maj1_nonneg α f MA z θ
  have h2 := Maj2_nonneg hα A f z θ
  have h3 := Maj3_nonneg α f KA z θ
  have h4 := Maj4_nonneg α A f z θ
  have h5 := Maj5_nonneg α A f z θ
  have h6 := Maj6_nonneg α A f z θ
  have h7 := Maj7_nonneg α A f z θ
  simp only [Maj]; linarith

theorem Maj1_le_Maj {α : ℝ} (hα : 0 < α) (A f : ℝ → ℝ → ℝ) (MA KA z θ : ℝ) :
    Maj1 α f MA z θ ≤ Maj α A f MA KA z θ := by
  have h2 := Maj2_nonneg hα A f z θ
  have h3 := Maj3_nonneg α f KA z θ
  have h4 := Maj4_nonneg α A f z θ
  have h5 := Maj5_nonneg α A f z θ
  have h6 := Maj6_nonneg α A f z θ
  have h7 := Maj7_nonneg α A f z θ
  simp only [Maj]; linarith

theorem Maj2_le_Maj {α : ℝ} (hα : 0 < α) (A f : ℝ → ℝ → ℝ) (MA KA z θ : ℝ) :
    Maj2 α A f z θ ≤ Maj α A f MA KA z θ := by
  have h1 := Maj1_nonneg α f MA z θ
  have h3 := Maj3_nonneg α f KA z θ
  have h4 := Maj4_nonneg α A f z θ
  have h5 := Maj5_nonneg α A f z θ
  have h6 := Maj6_nonneg α A f z θ
  have h7 := Maj7_nonneg α A f z θ
  simp only [Maj]; linarith

theorem Maj3_le_Maj {α : ℝ} (hα : 0 < α) (A f : ℝ → ℝ → ℝ) (MA KA z θ : ℝ) :
    Maj3 α f KA z θ ≤ Maj α A f MA KA z θ := by
  have h1 := Maj1_nonneg α f MA z θ
  have h2 := Maj2_nonneg hα A f z θ
  have h4 := Maj4_nonneg α A f z θ
  have h5 := Maj5_nonneg α A f z θ
  have h6 := Maj6_nonneg α A f z θ
  have h7 := Maj7_nonneg α A f z θ
  simp only [Maj]; linarith

theorem Maj4_le_Maj {α : ℝ} (hα : 0 < α) (A f : ℝ → ℝ → ℝ) (MA KA z θ : ℝ) :
    Maj4 α A f z θ ≤ Maj α A f MA KA z θ := by
  have h1 := Maj1_nonneg α f MA z θ
  have h2 := Maj2_nonneg hα A f z θ
  have h3 := Maj3_nonneg α f KA z θ
  have h5 := Maj5_nonneg α A f z θ
  have h6 := Maj6_nonneg α A f z θ
  have h7 := Maj7_nonneg α A f z θ
  simp only [Maj]; linarith

theorem Maj5_le_Maj {α : ℝ} (hα : 0 < α) (A f : ℝ → ℝ → ℝ) (MA KA z θ : ℝ) :
    Maj5 α A f z θ ≤ Maj α A f MA KA z θ := by
  have h1 := Maj1_nonneg α f MA z θ
  have h2 := Maj2_nonneg hα A f z θ
  have h3 := Maj3_nonneg α f KA z θ
  have h4 := Maj4_nonneg α A f z θ
  have h6 := Maj6_nonneg α A f z θ
  have h7 := Maj7_nonneg α A f z θ
  simp only [Maj]; linarith

theorem Maj6_le_Maj {α : ℝ} (hα : 0 < α) (A f : ℝ → ℝ → ℝ) (MA KA z θ : ℝ) :
    Maj6 α A f z θ ≤ Maj α A f MA KA z θ := by
  have h1 := Maj1_nonneg α f MA z θ
  have h2 := Maj2_nonneg hα A f z θ
  have h3 := Maj3_nonneg α f KA z θ
  have h4 := Maj4_nonneg α A f z θ
  have h5 := Maj5_nonneg α A f z θ
  have h7 := Maj7_nonneg α A f z θ
  simp only [Maj]; linarith

theorem Maj7_le_Maj {α : ℝ} (hα : 0 < α) (A f : ℝ → ℝ → ℝ) (MA KA z θ : ℝ) :
    Maj7 α A f z θ ≤ Maj α A f MA KA z θ := by
  have h1 := Maj1_nonneg α f MA z θ
  have h2 := Maj2_nonneg hα A f z θ
  have h3 := Maj3_nonneg α f KA z θ
  have h4 := Maj4_nonneg α A f z θ
  have h5 := Maj5_nonneg α A f z θ
  have h6 := Maj6_nonneg α A f z θ
  simp only [Maj]; linarith

/-- The pointwise Agmon bound of `PwAny6` for mixed derivatives of order `≤ 4`, bundled. -/
def SupPw (α CPw : ℝ) (u : ℝ → ℝ → ℝ) : Prop :=
  ∀ b a : ℕ, a + b ≤ 4 → ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (Real.pi / 2) →
    (Work.Spaces.mixed b a u z θ) ^ 2 ≤ CPw / (Work.Spaces.gam α - 1) * Work.Spaces.HkSq α 6 u


end

end PtB

end Work.FTS.StrongEps.E4R3.Nblock6.Tools
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.FkTileAux.fkMomentAe =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Almost-everywhere strong measurability of the `D_z`-iterates of the angular moment `FK f`

`Work.Construction.FK f z = ∫_θ K(θ)·f(z,θ) dθ` is the zeroth angular moment of `f`, i.e. a
function of `z` alone (`FK_eq_Qang_apply`: `FK f = Qang f 0`).  The claim of this file is that
for `f` in the honest open-quadrant class `Work.FTS.EllipticEst.SmoothOpen` with weighted energy
`Work.Spaces.HkMem α 6 f`, and for every `b₁ ≤ 6`, the `b₁`-th radial iterate
`DzdIter b₁ (FK f) = (z∂_z)^{b₁}(FK f)` — pushed forward to the square `ℝ × ℝ` by the first
projection — is almost everywhere strongly measurable for the product of the restrictions of
Lebesgue measure to `Iz = [0,∞)` and `Iθ = [0,π/2]`.

There is no analysis here beyond two identifications.

* **The a.e. identity on the half-line.**  `FK f` and `Qang f 0` are the *same* function of `z`
  (`FK_eq_Qang_apply`), so their `z∂_z`-iterates agree at every `z > 0`
  (`DzdIter_congr_Ioi`); and the level-six `z`-calculus of the angular moments
  (`QangAe6`) identifies those iterates with the higher moments `Qang f b₁` almost everywhere.
  Hence `DzdIter b₁ (FK f) = Qang f b₁` a.e. on the half-line, and since `Iz \ (0,∞) = {0}` is
  null the `0 < z` proviso can be dropped after restricting to `Iz`.

* **Strong measurability of the moments.**  `Qang f b₁ z = ∫_θ Ktheta θ · D_z^{b₁}f(z,θ) dθ`
  is the `θ`-integral of a function which is *continuous* on the open quadrant
  (`continuousOn_Ktheta_DzIter_open`, from `SmoothOpen f` alone, at any level `b₁`), hence —
  by `aesm_of_continuousOn_Qd` + `AEStronglyMeasurable.integral_prod_right'` — an almost
  everywhere strongly measurable function of `z` on `Iz`.  No `HkMem` hypothesis is needed for
  this half (only the a.e. identity above consumes it).

* **Push-forward.**  A function of `z` alone which is a.e. strongly measurable on `Iz` is a.e.
  strongly measurable for `(volume.restrict Iz).prod (volume.restrict Iθ)`: the first projection
  is quasi-measure-preserving (`Measure.quasiMeasurePreserving_fst`), so
  `AEStronglyMeasurable.comp_quasiMeasurePreserving` applies.  (Note the product measure is
  *not* finite, so this step genuinely uses the quasi-measure-preserving form rather than a
  Fubini statement.)

The proof is complete and rests on `[propext, Classical.choice, Quot.sound]`.
-/

namespace Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.FkTileAux

open MeasureTheory Set Filter
open scoped Real Topology

theorem fkMomentAe : ∀ (α : ℝ) (f : ℝ → ℝ → ℝ) (b₁ : ℕ),
    Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 6 f → b₁ ≤ 6 →
    MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => Work.Elliptic.DzdIter b₁ (fun z => Work.Construction.FK f z) p.1)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
  intro α f b₁ hsm hmem hb
  -- ## the a.e. identity `D_z^{b₁}(FK f) = Qang f b₁` on the open half-line
  have hpoint : ∀ᵐ z ∂(MeasureTheory.volume),
      0 < z → Work.Elliptic.DzdIter b₁ (fun z => Work.Construction.FK f z) z
        = Work.Elliptic.Qang f b₁ z := by
    filter_upwards [Work.FTS.StrongPersist.QangAe6 (α := α) (g := f) hsm hmem] with z hz
    intro hzpos
    calc Work.Elliptic.DzdIter b₁ (fun z => Work.Construction.FK f z) z
        = Work.Elliptic.DzdIter b₁ (fun z => Work.Elliptic.Qang f 0 z) z :=
          Work.FTS.StrongPersist.DzdIter_congr_Ioi
            (fun y _ => Work.FTS.StrongPersist.H6Rows.Npair6SupAux.FK_eq_Qang_apply f y)
            b₁ z hzpos
      _ = Work.Elliptic.Qang f b₁ z := hz hzpos b₁ (Finset.mem_range.mpr (by omega))
  -- ## the same identity restricted to `Iz` (where `z = 0` may be discarded),
  -- in the direction needed for `AEStronglyMeasurable.congr`
  have hrest : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      Work.Elliptic.Qang f b₁ z
        = Work.Elliptic.DzdIter b₁ (fun z => Work.Construction.FK f z) z := by
    have hIz : MeasurableSet Work.Spaces.Iz := measurableSet_Ici
    rw [MeasureTheory.ae_restrict_iff' hIz]
    filter_upwards [hpoint, MeasureTheory.Measure.ae_ne volume (0 : ℝ)] with z hz hne hzI
    exact (hz (lt_of_le_of_ne hzI (Ne.symm hne))).symm
  -- ## `z ↦ Qang f b₁ z` is a.e. strongly measurable on `Iz`
  have hQ : MeasureTheory.AEStronglyMeasurable (fun z => Work.Elliptic.Qang f b₁ z)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    have h := (Work.Spaces.aesm_of_continuousOn_Qd
        (fun p : ℝ × ℝ => Work.Elliptic.Ktheta p.2 * Work.Spaces.DzIter b₁ f p.1 p.2)
        (Work.FTS.OpenPkg.QangOpen.continuousOn_Ktheta_DzIter_open hsm b₁)).integral_prod_right'
    simpa only [Work.Elliptic.Qang] using h
  -- ## so is `z ↦ D_z^{b₁}(FK f) z`
  have hF : MeasureTheory.AEStronglyMeasurable
      (fun z => Work.Elliptic.DzdIter b₁ (fun z => Work.Construction.FK f z) z)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    hQ.congr hrest
  -- ## push forward along the (quasi-measure-preserving) first projection
  exact hF.comp_quasiMeasurePreserving
    (Measure.quasiMeasurePreserving_fst
      (μ := MeasureTheory.volume.restrict Work.Spaces.Iz)
      (ν := MeasureTheory.volume.restrict Work.Spaces.Iθ))

end Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.FkTileAux
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Row6.fkH6_norm_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Row6

open scoped Real Topology
open MeasureTheory Set Filter

set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-- **The sharp form of the `FK`-bound.**  The angular average
`FK f z = ∫_θ f z θ · K(θ) dθ` is a radial function whose `ℋ⁶`-norm is controlled by the
`ℋ⁶`-norm of `f` with the *universal* constant `√(7 · ∫_θ K(θ)² · ∫_θ sin(2θ)^{-η})` —
no additive `1` (this is the estimate the sibling `fkSq_le` proves and then deliberately
weakens to the shape `C(1 + |f|)`).

The proof is the Cauchy–Schwarz argument in `θ` (via `QangSq6Full`), summed over the
levels `i ≤ 6` (via `HkSq_rad`). -/
private theorem fkH6_norm_le_sqrt (α : ℝ) (hα : α ∈ Set.Ioc 0 1) (f : ℝ → ℝ → ℝ)
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 6 f) :
    Work.Spaces.HkNorm α 6 (fun z _ => Work.Construction.FK f z)
      ≤ Real.sqrt (7 * (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
          * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))))
        * Work.Spaces.HkNorm α 6 f := by
  have hαpos : 0 < α := hα.1
  have hαle : α ≤ 1 := hα.2
  -- the two universal angular constants
  set AK : ℝ := ∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2 with hAKdef
  set Cθ : ℝ := ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) with hCθdef
  have hAKnn : 0 ≤ AK := by
    rw [hAKdef]
    exact setIntegral_nonneg measurableSet_Icc (fun θ _ => sq_nonneg _)
  have hCθnn : 0 ≤ Cθ := by
    rw [hCθdef]
    exact setIntegral_nonneg measurableSet_Icc
      (fun θ hθ => Real.rpow_nonneg (Work.Elliptic.sin_two_nonneg_of_mem hθ) _)
  -- the angular moment is the radial function `u := Qang f 0`
  set u : ℝ → ℝ := fun z => Work.Elliptic.Qang f 0 z with hudef
  -- ## the a.e. identity `D_z^i (Qang f 0) = Qang f i` on `Iz`, `i ≤ 6`
  have hae : ∀ᵐ z ∂(MeasureTheory.volume), z ∈ Work.Spaces.Iz → ∀ i ∈ Finset.range 7,
      Work.Elliptic.DzdIter i u z = Work.Elliptic.Qang f i z := by
    filter_upwards [QangAe6 hsm hmem, MeasureTheory.Measure.ae_ne volume (0 : ℝ)]
      with z hz hne hzI
    exact hz (lt_of_le_of_ne hzI (Ne.symm hne))
  have htransfer : ∀ i : ℕ, i ≤ 6 → ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      (Work.Elliptic.Qang f i z) ^ 2 * (Work.Spaces.w z) ^ 2
        = (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2 := by
    intro i hi
    rw [MeasureTheory.ae_restrict_iff' (s := Work.Spaces.Iz) measurableSet_Ici]
    filter_upwards [hae] with z hz hzI
    rw [← hz hzI i (Finset.mem_range.mpr (by omega : i < 7))]
  -- ## the per-slot integrability and the weighted `L²`-bound
  have hInt : ∀ i : ℕ, i ≤ 6 → MeasureTheory.IntegrableOn
      (fun z => (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz :=
    fun i hi => (QangSq6Full (α := α) hsm hmem i hi).1.congr (htransfer i hi)
  have hBnd : ∀ i : ℕ, i ≤ 6 → (∫ z in Work.Spaces.Iz,
      (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2)
        ≤ AK * Work.Spaces.HkSq α 6 f := by
    intro i hi
    rw [hAKdef, ← MeasureTheory.integral_congr_ae (htransfer i hi)]
    exact (QangSq6Full (α := α) hsm hmem i hi).2
  have hsum_int : ∀ i ∈ Finset.range 7, MeasureTheory.IntegrableOn
      (fun z => (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz :=
    fun i hi => hInt i (Nat.le_of_lt_succ (Finset.mem_range.mp hi))
  have hsum_le : (∫ z in Work.Spaces.Iz, ∑ i ∈ Finset.range 7,
        (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2)
      ≤ 7 * (AK * Work.Spaces.HkSq α 6 f) := by
    rw [MeasureTheory.integral_finsetSum (Finset.range 7) hsum_int]
    calc ∑ i ∈ Finset.range 7, (∫ z in Work.Spaces.Iz,
            (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2)
        ≤ ∑ _i ∈ Finset.range 7, (AK * Work.Spaces.HkSq α 6 f) :=
          Finset.sum_le_sum fun i hi =>
            hBnd i (Nat.le_of_lt_succ (Finset.mem_range.mp hi))
      _ = 7 * (AK * Work.Spaces.HkSq α 6 f) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          norm_num
  -- ## the `ℋ⁶`-energy of the radial function
  have hHkSq : Work.Spaces.HkSq α 6 (fun z θ => u z) = (∫ z in Work.Spaces.Iz,
        ∑ i ∈ Finset.range 7,
          (Work.Elliptic.DzdIter i u z) ^ 2 * (Work.Spaces.w z) ^ 2) * Cθ := by
    rw [Work.Elliptic.HkSq_rad, hCθdef]
  have hbound : Work.Spaces.HkSq α 6 (fun z θ => u z)
      ≤ (7 * AK * Cθ) * Work.Spaces.HkSq α 6 f := by
    rw [hHkSq]
    refine le_trans (mul_le_mul_of_nonneg_right hsum_le hCθnn) (le_of_eq ?_)
    ring
  -- ## `FK f` is the radial function `u`
  have hfun : (fun z (_ : ℝ) => Work.Construction.FK f z) = (fun z (_ : ℝ) => u z) := by
    funext z θ
    rw [hudef]
    simp only [Work.Construction.FK, Work.Elliptic.Qang, Work.Spaces.DzIter_zero]
    rw [← Work.Elliptic.Ktheta_eq_K]
    exact setIntegral_congr_fun measurableSet_Icc (fun θ _ => mul_comm _ _)
  rw [hfun]
  -- ## the norm bound
  have h7nn : 0 ≤ 7 * AK * Cθ := by nlinarith
  calc Work.Spaces.HkNorm α 6 (fun z θ => u z)
      = Real.sqrt (Work.Spaces.HkSq α 6 (fun z θ => u z)) := rfl
    _ ≤ Real.sqrt ((7 * AK * Cθ) * Work.Spaces.HkSq α 6 f) := Real.sqrt_le_sqrt hbound
    _ = Real.sqrt (7 * AK * Cθ) * Work.Spaces.HkNorm α 6 f := by
        rw [Real.sqrt_mul h7nn]
        rfl

theorem fkH6_norm_le : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ f : ℝ → ℝ → ℝ,
    Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 6 f →
    Work.Spaces.HkNorm α 6 (fun z _ => Work.Construction.FK f z)
      ≤ C * Work.Spaces.HkNorm α 6 f := by
  refine ⟨Real.sqrt (7 * (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
      * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))) + 1, ?_, ?_⟩
  · have h := Real.sqrt_nonneg (7 * (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
      * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))))
    linarith
  intro α hα0 hα1 f hsm hmem
  refine le_trans (fkH6_norm_le_sqrt α ⟨hα0, hα1⟩ f hsm hmem) ?_
  exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one)
    (Work.Spaces.HkNorm_nonneg α 6 f)

end Work.FTS.StrongPersist.H6Row6
end
-- ===== merged: Submission.Work.FTS.StrongPersist.L3Rhs.VfsJetMajMass =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.L3Rhs

set_option autoImplicit false

/-! ## The `η`-weighted mass of the profile `VfsGc α = Γ/c`

This is the `m = 0` term of `VfsJetMaj`.  It is the easy one: on `Iθ` we have `(Γ/c)² ≤ 100`
(because `0 ≤ Γ ≤ 1` and `1/10 ≤ c ≤ 10`), so the integrand is dominated by `100·sin(2θ)^{-η}`
whose integral is at most `100·10000 = 10^6`. -/

/-- On `Iθ`, `(Γ/c)² ≤ 100` for `0 < α ≤ 1`. -/
private lemma gamGc_sq_le (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) : (VfsGc α θ) ^ 2 ≤ 100 := by
  obtain ⟨hG0, hG1⟩ := Work.Spaces.Gam_bounds α θ hα hθ
  obtain ⟨hc1, hc2⟩ := Work.Spaces.c_bounds α hα hα1
  have hcpos : 0 < Work.Spaces.c α := by linarith
  have hdiv : VfsGc α θ ≤ 10 := by
    simp only [VfsGc]
    rw [div_le_iff₀ hcpos]
    nlinarith
  have hdiv0 : 0 ≤ VfsGc α θ := by
    simp only [VfsGc]
    exact div_nonneg hG0 hcpos.le
  nlinarith

/-- **The `η`-weighted mass of `Γ/c`.**  For `0 < α ≤ 1`,
`∫_{Iθ} (Γ/c)² sin(2θ)^{-η} ≤ 10⁶` and the integrand is integrable. -/
private lemma gamGc_eta_mass (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    MeasureTheory.IntegrableOn
      (fun θ : ℝ => (VfsGc α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      Work.Spaces.Iθ ∧
    (∫ θ in Work.Spaces.Iθ, (VfsGc α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      ≤ 10 ^ 6 := by
  have hmeasIθ : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  have hη1 : -1 < -(Work.Spaces.eta) := by simp only [Work.Spaces.eta]; norm_num
  have hη0 : -(Work.Spaces.eta) ≤ 0 := by simp only [Work.Spaces.eta]; norm_num
  obtain ⟨hIntS, hBdS⟩ := Work.Spaces.sin_two_rpow (-(Work.Spaces.eta)) hη1 hη0
  have hBdS' : ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) ≤ 10000 := by
    have heq : 100 / (-(Work.Spaces.eta) + 1) = 10000 := by
      simp only [Work.Spaces.eta]; norm_num
    rwa [heq] at hBdS
  have h100 : MeasureTheory.IntegrableOn
      (fun θ => 100 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Work.Spaces.Iθ :=
    hIntS.const_mul 100
  have hpt : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      (VfsGc α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
        ≤ 100 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
    filter_upwards [MeasureTheory.ae_restrict_mem hmeasIθ] with θ hθ
    have hX : 0 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
      Real.rpow_nonneg (sin_two_nonneg_Iθ hθ) _
    have h2 := gamGc_sq_le α hα hα1 hθ
    nlinarith [h2, hX]
  have hmeas : AEStronglyMeasurable
      (fun θ : ℝ => (VfsGc α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      (volume.restrict Work.Spaces.Iθ) := by
    apply Measurable.aestronglyMeasurable
    simp only [VfsGc, Work.Spaces.Gam]
    fun_prop
  have hIntf : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (VfsGc α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      Work.Spaces.Iθ :=
    h100.mono' hmeas (by
      filter_upwards [hpt, MeasureTheory.ae_restrict_mem hmeasIθ] with θ h1 h2
      rw [Real.norm_of_nonneg
        (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (sin_two_nonneg_Iθ h2) _))]
      exact h1)
  refine ⟨hIntf, ?_⟩
  have hmono := MeasureTheory.integral_mono_ae hIntf h100 hpt
  calc ∫ θ in Work.Spaces.Iθ, (VfsGc α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
      ≤ ∫ θ in Work.Spaces.Iθ, 100 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := hmono
    _ = 100 * ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
        rw [MeasureTheory.integral_const_mul]
    _ ≤ 100 * 10000 := by linarith [hBdS']
    _ = 10 ^ 6 := by norm_num

/-! ## The `α²`-weighted mass of the profile

The middle summand `α²·(Γ/c)²·sin(2θ)^{-γ}` of `VfsJetMaj`.  Here the crude bound
`∫ sin(2θ)^{-γ} = ∞` is fatal, but the vanishing of `Γ` at the endpoints saves it: the
factor `α²` exactly compensates the `1/α` of `∫ sin(2θ)^{17α/30-1} = 3000/(17α)`. -/

/-- On `Iθ` (indeed everywhere), `(Γ/c)² ≤ 100Γ²` for `0 < α ≤ 1`: this is the lower bound
`1/10 ≤ c` of `Work.Spaces.c_bounds`. -/
private lemma gamGc_sq_le_gamSq (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (θ : ℝ) :
    (VfsGc α θ) ^ 2 ≤ 100 * (Work.Spaces.Gam α θ) ^ 2 := by
  obtain ⟨hc1, _⟩ := Work.Spaces.c_bounds α hα hα1
  have hcpos : 0 < Work.Spaces.c α := by linarith
  have hc2 : (1 / 100 : ℝ) ≤ (Work.Spaces.c α) ^ 2 := by nlinarith [hc1]
  have hmain : (Work.Spaces.Gam α θ / Work.Spaces.c α) ^ 2
      ≤ 100 * (Work.Spaces.Gam α θ) ^ 2 := by
    rw [div_pow, div_le_iff₀ (by positivity : (0 : ℝ) < (Work.Spaces.c α) ^ 2)]
    nlinarith [hc2, sq_nonneg (Work.Spaces.Gam α θ)]
  simpa only [VfsGc] using hmain

/-- `100·α²·2^{-2α/3}·(3000/(17α)) ≤ 300000/17` for `0 < α ≤ 1`. -/
private lemma alphaMass_arith (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    100 * α ^ 2 * 2 ^ (-(2 * α / 3)) * (3000 / (17 * α)) ≤ 300000 / 17 := by
  have hpow1 : (2 : ℝ) ^ (-(2 * α / 3)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith : -(2 * α / 3) ≤ 0)
  have hαpow : α * 2 ^ (-(2 * α / 3)) ≤ 1 := by
    have h := mul_le_mul_of_nonneg_left hpow1 hα.le
    rw [mul_one] at h
    linarith [h, hα1]
  have hrew : 100 * α ^ 2 * 2 ^ (-(2 * α / 3)) * (3000 / (17 * α))
      = (300000 / 17) * (α * 2 ^ (-(2 * α / 3))) := by
    field_simp
    ring
  rw [hrew]
  have := mul_le_mul_of_nonneg_left hαpow (by norm_num : (0 : ℝ) ≤ 300000 / 17)
  simpa using this

/-- **The `α²`-weighted `γ`-mass of `Γ/c`.**  For `0 < α ≤ 1` the integrand
`α²(Γ/c)²sin(2θ)^{-γ}` is integrable on `Iθ` with integral at most `300000/17`. -/
private lemma alphaGc_mass (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    MeasureTheory.IntegrableOn
      (fun θ : ℝ => α ^ 2 * (VfsGc α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
      Work.Spaces.Iθ ∧
    (∫ θ in Work.Spaces.Iθ,
        α ^ 2 * (VfsGc α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
      ≤ 300000 / 17 := by
  have hmeasIθ : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  have hp1 : -1 < 17 * α / 30 - 1 := by linarith
  have hp2 : 17 * α / 30 - 1 ≤ 0 := by linarith
  obtain ⟨hIntS, hBdS⟩ := Work.Spaces.sin_two_rpow (17 * α / 30 - 1) hp1 hp2
  have hBdS' : ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (17 * α / 30 - 1)
      ≤ 3000 / (17 * α) := by
    have heq : 100 / ((17 * α / 30 - 1) + 1) = 3000 / (17 * α) := by field_simp; ring
    rwa [heq] at hBdS
  have hpt : ∀ θ ∈ Work.Spaces.Iθ,
      α ^ 2 * (VfsGc α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
        ≤ 100 * α ^ 2 * 2 ^ (-(2 * α / 3))
          * (Real.sin (2 * θ)) ^ (17 * α / 30 - 1) := by
    intro θ hθ
    have hT0 := sin_two_nonneg_Iθ hθ
    have hTg : 0 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := Real.rpow_nonneg hT0 _
    have hX2 := gamGc_sq_le_gamSq α hα hα1 θ
    have hG2 := Work.FTS.LocData.GamSq_sin_neg_gam_le α hα hα1 hθ
    calc α ^ 2 * (VfsGc α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
        ≤ α ^ 2 * (100 * (Work.Spaces.Gam α θ) ^ 2)
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hX2 (sq_nonneg α)) hTg
      _ = (100 * α ^ 2) * ((Work.Spaces.Gam α θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by ring
      _ ≤ (100 * α ^ 2) * (2 ^ (-(2 * α / 3))
            * (Real.sin (2 * θ)) ^ (17 * α / 30 - 1)) :=
          mul_le_mul_of_nonneg_left hG2 (by positivity)
      _ = 100 * α ^ 2 * 2 ^ (-(2 * α / 3)) * (Real.sin (2 * θ)) ^ (17 * α / 30 - 1) := by ring
  have hMajInt : MeasureTheory.IntegrableOn
      (fun θ : ℝ => 100 * α ^ 2 * 2 ^ (-(2 * α / 3))
        * (Real.sin (2 * θ)) ^ (17 * α / 30 - 1)) Work.Spaces.Iθ := hIntS.const_mul _
  have hmeas : AEStronglyMeasurable
      (fun θ : ℝ => α ^ 2 * (VfsGc α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
      (volume.restrict Work.Spaces.Iθ) := by
    apply Measurable.aestronglyMeasurable
    simp only [VfsGc, Work.Spaces.Gam]
    fun_prop
  have hae : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      α ^ 2 * (VfsGc α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
        ≤ 100 * α ^ 2 * 2 ^ (-(2 * α / 3))
          * (Real.sin (2 * θ)) ^ (17 * α / 30 - 1) := by
    filter_upwards [MeasureTheory.ae_restrict_mem hmeasIθ] with θ hθ
    exact hpt θ hθ
  have hf : MeasureTheory.IntegrableOn
      (fun θ : ℝ => α ^ 2 * (VfsGc α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
      Work.Spaces.Iθ := by
    refine hMajInt.mono' hmeas ?_
    filter_upwards [MeasureTheory.ae_restrict_mem hmeasIθ] with θ hθ
    rw [Real.norm_of_nonneg (mul_nonneg (mul_nonneg (sq_nonneg α) (sq_nonneg _))
      (Real.rpow_nonneg (sin_two_nonneg_Iθ hθ) _))]
    exact hpt θ hθ
  refine ⟨hf, ?_⟩
  calc ∫ θ in Work.Spaces.Iθ,
        α ^ 2 * (VfsGc α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
      ≤ ∫ θ in Work.Spaces.Iθ, 100 * α ^ 2 * 2 ^ (-(2 * α / 3))
          * (Real.sin (2 * θ)) ^ (17 * α / 30 - 1) :=
        MeasureTheory.integral_mono_ae hf hMajInt hae
    _ = (100 * α ^ 2 * 2 ^ (-(2 * α / 3)))
          * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (17 * α / 30 - 1)) := by
        rw [MeasureTheory.integral_const_mul]
    _ ≤ (100 * α ^ 2 * 2 ^ (-(2 * α / 3))) * (3000 / (17 * α)) :=
        mul_le_mul_of_nonneg_left hBdS' (by positivity)
    _ ≤ 300000 / 17 := alphaMass_arith α hα hα1

/-! ## The `γ`-weighted jet sum -/

/-- The `γ`-weighted jet sum `VfsJetSum α` is integrable and its integral is at most
`4·10^15`, given the four individual mass bounds. -/
private lemma jetSum_mass (α : ℝ)
    (hGam : ∀ i : ℕ, 1 ≤ i → i ≤ 4 →
      MeasureTheory.IntegrableOn
        (fun θ : ℝ => (Work.Spaces.dthU^[i] (VfsGc α) θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) Work.Spaces.Iθ ∧
      (∫ θ in Work.Spaces.Iθ, (Work.Spaces.dthU^[i] (VfsGc α) θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) ≤ 10 ^ 15) :
    MeasureTheory.IntegrableOn (VfsJetSum α) Work.Spaces.Iθ ∧
      (∫ θ in Work.Spaces.Iθ, VfsJetSum α θ) ≤ 4 * 10 ^ 15 := by
  have hmem : ∀ i ∈ Finset.Icc 1 4, 1 ≤ i ∧ i ≤ 4 := fun i hi => Finset.mem_Icc.mp hi
  have hInt : MeasureTheory.IntegrableOn (VfsJetSum α) Work.Spaces.Iθ :=
    integrable_finsetSum (Finset.Icc 1 4)
      (fun i hi => (hGam i (hmem i hi).1 (hmem i hi).2).1)
  refine ⟨hInt, ?_⟩
  have hsum : (∫ θ in Work.Spaces.Iθ, VfsJetSum α θ)
      = ∑ i ∈ Finset.Icc 1 4,
          ∫ θ in Work.Spaces.Iθ, (Work.Spaces.dthU^[i] (VfsGc α) θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
    integral_finsetSum (Finset.Icc 1 4)
      (fun i hi => (hGam i (hmem i hi).1 (hmem i hi).2).1)
  rw [hsum]
  calc ∑ i ∈ Finset.Icc 1 4,
        (∫ θ in Work.Spaces.Iθ, (Work.Spaces.dthU^[i] (VfsGc α) θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
      ≤ ∑ _i ∈ Finset.Icc 1 4, (10 ^ 15 : ℝ) :=
        Finset.sum_le_sum (fun i hi => (hGam i (hmem i hi).1 (hmem i hi).2).2)
    _ = 4 * 10 ^ 15 := by
        rw [Finset.sum_const, Nat.card_Icc]
        norm_num

/-! ## The target -/

-- `VfsJetMajMass`: the `α`-uniform angular mass of the extended majorant `VfsJetMaj` of `Γ/c`.
-- Intended namespace `Work.FTS.StrongPersist.L3Rhs`
-- (file `Submission/Work/FTS/StrongPersist/L3Rhs/VfsJetMajMass.lean`).
-- Route: `VfsJetMaj α θ = (X θ)²T^{-η} + α²(X θ)²T^{-γ} + Σ_{1≤m≤4}(dthU^[m]X θ)²T^{-γ}` with
-- `X = VfsGc α = Γ/c`, `T θ = sin(2θ)`.  The first and third groups are bounded (as
-- `IntegrableOn` and as integrals) by `10^15` via `Work.FTS.StrongPersist.L3Aux.GamJetBounds`
-- (bridge with `Work.FTS.LocData.DthIter_rad_eq`); the middle group satisfies
-- `α²X²T^{-γ} ≤ 100α²Γ²T^{-γ} ≤ 100α²2^{-2α/3}T^{17α/30-1}` and its integral is at most
-- `100·α²·3000/(17α) = 300000α/17 ≤ 300000/17` (`Work.Spaces.c_bounds`,
-- `Work.FTS.LocData.GamSq_sin_neg_gam_le`, `Work.Spaces.sin_two_rpow`).
theorem VfsJetMajMass (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    MeasureTheory.IntegrableOn (Work.FTS.StrongPersist.L3Rhs.VfsJetMaj α) Work.Spaces.Iθ ∧
      (∫ θ in Work.Spaces.Iθ, Work.FTS.StrongPersist.L3Rhs.VfsJetMaj α θ) ≤ 10 ^ 16 := by
  obtain ⟨hEtaInt, hEtaBd⟩ := gamGc_eta_mass α hα hα1
  -- `Work.FTS.StrongPersist.L3Rhs.VfsJetMassAux.gamJetMass`
  have hGam : ∀ i : ℕ, 1 ≤ i → i ≤ 4 →
      MeasureTheory.IntegrableOn
        (fun θ : ℝ => (Work.Spaces.dthU^[i] (VfsGc α) θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) Work.Spaces.Iθ ∧
      (∫ θ in Work.Spaces.Iθ, (Work.Spaces.dthU^[i] (VfsGc α) θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) ≤ 10 ^ 15 :=
    fun i hi1 hi4 => VfsJetMassAux.gamJetMass α hα hα1 i hi1 hi4
  -- `Work.FTS.StrongPersist.L3Rhs.VfsJetMassAux.alphaJetMass` is *not* imported: that module
  -- defines a helper `VfsGc_sq_le` clashing with the sibling `gamJetMass` module's helper of
  -- the same name (both live in `Work.FTS.StrongPersist.L3Rhs.VfsJetMassAux`), so the two
  -- cannot be imported into one environment.  The `α²`-mass is proved locally instead
  -- (`alphaGc_mass`).
  obtain ⟨hAlInt, hAlBd⟩ := alphaGc_mass α hα hα1
  obtain ⟨hJsInt, hJsBd⟩ := jetSum_mass α hGam
  refine ⟨?_, ?_⟩
  · show MeasureTheory.IntegrableOn
      (fun θ : ℝ => (VfsGc α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
        + α ^ 2 * (VfsGc α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
        + VfsJetSum α θ) Work.Spaces.Iθ
    exact (hEtaInt.add hAlInt).add hJsInt
  · have hSplit : (∫ θ in Work.Spaces.Iθ, VfsJetMaj α θ)
        = (∫ θ in Work.Spaces.Iθ, (VfsGc α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
          + (∫ θ in Work.Spaces.Iθ,
              α ^ 2 * (VfsGc α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
          + (∫ θ in Work.Spaces.Iθ, VfsJetSum α θ) := by
      have hfun : ((fun θ : ℝ => (VfsGc α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
            + α ^ 2 * (VfsGc α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))))
          = (fun θ : ℝ => (VfsGc α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
            + fun θ : ℝ => α ^ 2 * (VfsGc α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
        funext θ; rfl
      have hAB : MeasureTheory.IntegrableOn
          (fun θ : ℝ => (VfsGc α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
            + α ^ 2 * (VfsGc α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
          Work.Spaces.Iθ := by
        simpa only [hfun] using hEtaInt.add hAlInt
      have h1 : (∫ θ in Work.Spaces.Iθ, VfsJetMaj α θ)
          = (∫ θ in Work.Spaces.Iθ, (VfsGc α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
              + α ^ 2 * (VfsGc α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
            + (∫ θ in Work.Spaces.Iθ, VfsJetSum α θ) :=
        MeasureTheory.integral_add hAB hJsInt
      have h2 : (∫ θ in Work.Spaces.Iθ, (VfsGc α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
              + α ^ 2 * (VfsGc α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
          = (∫ θ in Work.Spaces.Iθ, (VfsGc α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
            + (∫ θ in Work.Spaces.Iθ,
                α ^ 2 * (VfsGc α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) :=
        MeasureTheory.integral_add hEtaInt hAlInt
      rw [h1, h2]
    rw [hSplit]
    have harith : (10 : ℝ) ^ 6 + 300000 / 17 + 4 * 10 ^ 15 ≤ 10 ^ 16 := by norm_num
    linarith [hEtaBd, hAlBd, hJsBd, harith]

end Work.FTS.StrongPersist.L3Rhs
end
end
