import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0Aux.B4SepDefs
import Submission.Work.FTS.StrongPersist.L3Rhs.VfsRadSlotBound
import Submission.Work.FTS.StrongPersist.L3Aux.L12f_slot_le

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
