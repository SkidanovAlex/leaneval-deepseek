import ChallengeDeps
import Mathlib.MeasureTheory.Function.L2Space
import Submission.Work.BoseSym.Bridge.ae_eq_zero_off_box
import Submission.Work.BoseSym.Bridge.aemeas_indicator_of_aesm_on_box
import Submission.Work.BoseSym.Bridge.boxEnergyTrunc_eq_iInf
import Submission.Work.BoseSym.Bridge.integrableOn_Vpot_box
import Submission.Work.BoseSym.Bridge.integrable_and_integral_le_of_tendsto_monotone
import Submission.Work.BoseSym.Bridge.potSq_le_of_le
import Submission.Work.BoseSym.Minimiser.cauchySeq_of_excess_family
import Submission.Work.BoseSym.Minimiser.exists_minimiser_of_unit
import Submission.Work.BoseSym.Minimiser.hSq_sub_le_of_dirForm_min
import Submission.Work.BoseSym.Minimiser.iInf_le_dirForm_unit
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# BoseSym.Bridge — the liminf of the Dirichlet energies along a bounded sequence

Given a sequence `p n` in the energy space `Hsub N L` with `l2Sq (p n) = 1` and
`gSq (p n) ≤ C`, a nonnegative monotone sequence of potentials `W n ↑ Wlim` with
`W n · (p n)²` integrable on the box with integral at most `C'`, one can extract a
strictly increasing subsequence `φ` and a unit vector `q ∈ Hsub N L` whose full
Dirichlet energy against the limit potential `Wlim` is at most the liminf of the
energies `gSq (p (φ n)) + ∫_box W (φ n) (p (φ n))²`.

The proof does not use weak compactness: it minimises the (bounded, nonnegative)
truncated potentials `V k = 1_box · min (W k, k)` on the unit sphere of `Hsub`,
for which minimisers exist by `Minimiser.exists_minimiser_of_unit`, and shows that
the resulting minimising sequence is Cauchy in the ambient norm.  The key point is
that the *excess* of the minimiser of level `k` for the functional of level `j`
(`j ≤ k`) is bounded by `Mstar - m j`, where `m j` is the minimal value at level
`j` and `Mstar = ⨆ j, m j`; the Cauchy–Schwarz inequality for the shifted
Dirichlet form (`Minimiser.hSq_sub_le_of_dirForm_min`) then yields
`hSq (r k - r l) ≤ 4 (Mstar - m j) + (m j + 1) l2Sq (r k - r l)`, and the right
hand side tends to `0` because `m j → Mstar` and the function parts converge in
`L²`.
-/

namespace Work.BoseSym.Bridge

open MeasureTheory Filter
open Work.BoseSym

set_option maxHeartbeats 1000000

theorem hsub_liminf_energy {N : ℕ} {L : ℝ} {C C' : ℝ}
    (p : ℕ → Work.BoseSym.Hsub N L) (hp1 : ∀ n, Work.BoseSym.l2Sq ((p n : Work.BoseSym.Amb N)) = 1)
    (hC : ∀ n, Work.BoseSym.gSq ((p n : Work.BoseSym.Amb N)) ≤ C)
    {W : ℕ → Work.BoseSym.Conf N → ℝ} {Wlim : Work.BoseSym.Conf N → ℝ}
    (hW0 : ∀ n, 0 ≤ W n) (hWlim0 : 0 ≤ Wlim)
    (hWm : ∀ n, MeasureTheory.AEStronglyMeasurable (W n)
      (MeasureTheory.volume.restrict (BoseGases.box N L)))
    (hWlimm : MeasureTheory.AEStronglyMeasurable Wlim
      (MeasureTheory.volume.restrict (BoseGases.box N L)))
    (hWmono : ∀ n x, W n x ≤ W (n + 1) x)
    (hWtend : ∀ x, Filter.Tendsto (fun n => W n x) Filter.atTop (nhds (Wlim x)))
    (hC'i : ∀ n, MeasureTheory.IntegrableOn
      (fun x => W n x * (((p n : Work.BoseSym.Amb N).1 : Work.BoseSym.Conf N → ℝ) x) ^ 2)
      (BoseGases.box N L) MeasureTheory.volume)
    (hC'b : ∀ n, ∫ x in BoseGases.box N L,
        W n x * (((p n : Work.BoseSym.Amb N).1 : Work.BoseSym.Conf N → ℝ) x) ^ 2 ≤ C') :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ q : Work.BoseSym.Hsub N L,
      Work.BoseSym.l2Sq (q : Work.BoseSym.Amb N) = 1 ∧
      MeasureTheory.IntegrableOn
        (fun x => Wlim x * (((q : Work.BoseSym.Amb N).1 : Work.BoseSym.Conf N → ℝ) x) ^ 2)
        (BoseGases.box N L) MeasureTheory.volume ∧
      Work.BoseSym.gSq (q : Work.BoseSym.Amb N) + ∫ x in BoseGases.box N L,
          Wlim x * (((q : Work.BoseSym.Amb N).1 : Work.BoseSym.Conf N → ℝ) x) ^ 2
        ≤ Filter.liminf (fun n => Work.BoseSym.gSq ((p (φ n) : Work.BoseSym.Amb N))
            + ∫ x in BoseGases.box N L,
                W (φ n) x * (((p (φ n) : Work.BoseSym.Amb N).1 : Work.BoseSym.Conf N → ℝ) x) ^ 2)
            Filter.atTop := by
  classical
  -- ## 1. The truncated potentials `V k = 1_box · min (W k, k)`
  set Vf : ℕ → Conf N → ℝ :=
    fun k => (BoseGases.box N L).indicator (fun x => min (W k x) ((k : ℝ))) with hVf
  have hV0 : ∀ k x, 0 ≤ Vf k x := by
    intro k x
    by_cases hx : x ∈ BoseGases.box N L
    · simp only [hVf, Set.indicator_of_mem hx]
      exact le_min (hW0 k x) (Nat.cast_nonneg k)
    · simp [hVf, Set.indicator_of_notMem hx]
  have hVbdd : ∀ k, BddBy N (Vf k) (k : ℝ) := by
    intro k x
    by_cases hx : x ∈ BoseGases.box N L
    · simp only [hVf, Set.indicator_of_mem hx]
      rw [abs_of_nonneg (le_min (hW0 k x) (Nat.cast_nonneg k))]
      exact min_le_right _ _
    · simp [hVf, Set.indicator_of_notMem hx]
  have hVleW : ∀ k x, Vf k x ≤ W k x := by
    intro k x
    by_cases hx : x ∈ BoseGases.box N L
    · simp only [hVf, Set.indicator_of_mem hx]
      exact min_le_left _ _
    · simp only [hVf, Set.indicator_of_notMem hx]
      exact hW0 k x
  have hVmono : ∀ k x, Vf k x ≤ Vf (k + 1) x := by
    intro k x
    by_cases hx : x ∈ BoseGases.box N L
    · simp only [hVf, Set.indicator_of_mem hx]
      exact min_le_min (hWmono k x) (by push_cast; linarith)
    · have h0 : Vf k x = 0 := by simp [hVf, Set.indicator_of_notMem hx]
      rw [h0]
      exact hV0 (k + 1) x
  have hVmono' : ∀ j k, j ≤ k → ∀ x, Vf j x ≤ Vf k x := fun j k hjk x =>
    (monotone_nat_of_le_succ (fun i => hVmono i x)) hjk
  have hVmeas : ∀ k, AEMeas N (Vf k) := by
    intro k
    have hmin : AEStronglyMeasurable (fun x => min (W k x) ((k : ℝ)))
        (MeasureTheory.volume.restrict (BoseGases.box N L)) :=
      continuous_min.comp_aestronglyMeasurable₂ (g := fun a b : ℝ => min a b)
        (hWm k) aestronglyMeasurable_const
    have h := aemeas_indicator_of_aesm_on_box (N := N) (L := L)
      (W := fun x => min (W k x) ((k : ℝ))) hmin
    rw [hVf]
    exact h.congr (Filter.Eventually.of_forall fun x => rfl)
  have hVnn : ∀ k, AENonneg N (Vf k) := fun k => Filter.Eventually.of_forall (hV0 k)
  have hVtend : ∀ x, Filter.Tendsto (fun k => Vf k x) Filter.atTop
      (nhds ((BoseGases.box N L).indicator Wlim x)) := by
    intro x
    by_cases hx : x ∈ BoseGases.box N L
    · simp only [hVf, Set.indicator_of_mem hx]
      have hWle : ∀ k, W k x ≤ Wlim x := fun k =>
        le_of_tendsto_of_tendsto tendsto_const_nhds (hWtend x) (Filter.eventually_atTop.mpr
          ⟨k, fun n hn => (monotone_nat_of_le_succ (fun i => hWmono i x)) hn⟩)
      have hge : ∀ᶠ k in Filter.atTop, W k x = min (W k x) ((k : ℝ)) := by
        obtain ⟨K, hK⟩ := exists_nat_ge (max (Wlim x) 0)
        filter_upwards [Filter.eventually_ge_atTop K] with k hk
        have h1 : W k x ≤ Wlim x := hWle k
        have h2 : Wlim x ≤ (k : ℝ) :=
          le_trans (le_max_left _ _) (le_trans hK (by exact_mod_cast hk))
        exact (min_eq_left (le_trans h1 h2)).symm
      exact (hWtend x).congr' hge
    · simp only [hVf, Set.indicator_of_notMem hx]
      exact tendsto_const_nhds
  -- ## 2. The minimisers of the truncated problems
  have hunit : ∃ z : Hsub N L, l2Sq (z : Amb N) = 1 := ⟨p 0, hp1 0⟩
  have hmin : ∀ k, ∃ q : {q : Hsub N L // l2Sq (q : Amb N) = 1},
      dirForm (Vf k) (q : Amb N) = ⨅ q' : {q' : Hsub N L // l2Sq (q' : Amb N) = 1},
        dirForm (Vf k) (q' : Amb N) := fun k =>
    Minimiser.exists_minimiser_of_unit (k : ℝ) (Vf k) (hVbdd k) (hVnn k) (hVmeas k) hunit
  choose rr hrr using hmin
  set r : ℕ → Hsub N L := fun k => (rr k : Hsub N L) with hr
  have hrl2 : ∀ k, l2Sq (r k : Amb N) = 1 := fun k => (rr k).2
  have hrmin : ∀ k, dirForm (Vf k) (r k : Amb N)
      = ⨅ q' : {q' : Hsub N L // l2Sq (q' : Amb N) = 1}, dirForm (Vf k) (q' : Amb N) := hrr
  set m : ℕ → ℝ := fun k => dirForm (Vf k) (r k : Amb N) with hm
  have hmmin : ∀ k, m k = ⨅ q' : {q' : Hsub N L // l2Sq (q' : Amb N) = 1},
      dirForm (Vf k) (q' : Amb N) := fun k => by
    simp only [hm]
    exact hrmin k
  -- ## 3. The Rayleigh bound
  have hray : ∀ k (x : Hsub N L), m k * l2Sq (x : Amb N) ≤ dirForm (Vf k) (x : Amb N) := by
    intro k x
    by_cases hx : l2Sq (x : Amb N) = 0
    · rw [hx, mul_zero]
      have hgsq : 0 ≤ gSq (x : Amb N) := Finset.sum_nonneg fun j _ => sq_nonneg _
      have hpot : 0 ≤ potSq (Vf k) (x : Amb N) :=
        integral_nonneg_of_ae (Filter.Eventually.of_forall fun y =>
          mul_nonneg (hV0 k y) (sq_nonneg _))
      simp only [dirForm]
      linarith
    · have hpos : 0 < l2Sq (x : Amb N) :=
        lt_of_le_of_ne (by simp only [l2Sq]; positivity) (Ne.symm hx)
      set c : ℝ := (Real.sqrt (l2Sq (x : Amb N)))⁻¹ with hc
      have hcl2 : l2Sq ((c • x : Hsub N L) : Amb N) = 1 := by
        rw [show ((c • x : Hsub N L) : Amb N) = c • (x : Amb N) from rfl, l2Sq_smul, hc,
          inv_pow, Real.sq_sqrt hpos.le]
        field_simp
      have hinf := Minimiser.iInf_le_dirForm_unit (L := L) (W := Vf k) (hVnn k) hcl2
      rw [← hmmin k] at hinf
      have hdir : dirForm (Vf k) ((c • x : Hsub N L) : Amb N)
          = c ^ 2 * dirForm (Vf k) (x : Amb N) := by
        rw [show ((c • x : Hsub N L) : Amb N) = c • (x : Amb N) from rfl, dirForm_smul]
      rw [hdir] at hinf
      have hc2 : c ^ 2 = (l2Sq (x : Amb N))⁻¹ := by
        rw [hc, inv_pow, Real.sq_sqrt hpos.le]
      have h1 : m k * l2Sq (x : Amb N)
          ≤ (c ^ 2 * dirForm (Vf k) (x : Amb N)) * l2Sq (x : Amb N) :=
        mul_le_mul_of_nonneg_right hinf hpos.le
      have h2 : (c ^ 2 * dirForm (Vf k) (x : Amb N)) * l2Sq (x : Amb N)
          = dirForm (Vf k) (x : Amb N) := by
        rw [hc2]
        field_simp
      linarith [h1, h2.le, h2.ge]
  -- ## 4. Integrability and the potential comparison on the box
  have hbox_le : ∀ n, ∫ x in BoseGases.box N L,
        Vf n x * (((p n : Amb N).1 : Conf N → ℝ) x) ^ 2
      ≤ ∫ x in BoseGases.box N L,
        W n x * (((p n : Amb N).1 : Conf N → ℝ) x) ^ 2 := by
    intro n
    refine integral_mono_ae ?_ (hC'i n) ?_
    · refine Integrable.mono' (hC'i n) ?_ ?_
      · exact (((hVmeas n).aestronglyMeasurable.mono_measure Measure.restrict_le_self).mul
          (((Lp.aestronglyMeasurable (p n : Amb N).1).mono_measure
            Measure.restrict_le_self).pow 2))
      · filter_upwards with x
        have h1 : 0 ≤ Vf n x := hV0 n x
        have h2 : 0 ≤ (((p n : Amb N).1 : Conf N → ℝ) x) ^ 2 := sq_nonneg _
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg h1 h2)]
        exact mul_le_mul_of_nonneg_right (hVleW n x) h2
    · filter_upwards with x
      exact mul_le_mul_of_nonneg_right (hVleW n x) (sq_nonneg _)
  have hpot_box : ∀ n, potSq (Vf n) (p n : Amb N)
      = ∫ x in BoseGases.box N L, Vf n x * (((p n : Amb N).1 : Conf N → ℝ) x) ^ 2 := by
    intro n
    rw [potSq]
    have hae : (fun y => Vf n y * ((p n : Amb N).1 : Conf N → ℝ) y ^ 2) =ᵐ[volC N]
        (BoseGases.box N L).indicator
          (fun y => Vf n y * ((p n : Amb N).1 : Conf N → ℝ) y ^ 2) := by
      filter_upwards [ae_eq_zero_off_box (N := N) (L := L) (p n)] with y hy
      by_cases hy' : y ∈ BoseGases.box N L
      · rw [Set.indicator_of_mem hy']
      · rw [Set.indicator_of_notMem hy', hy hy']
        ring
    rw [integral_congr_ae hae,
      integral_indicator (Submission.BoseGases.box_closed L).measurableSet]
  -- ## 5. `m` is bounded above; `Mstar` is its supremum
  have hm_le : ∀ k, m k ≤ C + C' := by
    intro k
    have h1 : m k ≤ dirForm (Vf k) (p k : Amb N) := by
      rw [hmmin k]
      exact Minimiser.iInf_le_dirForm_unit (L := L) (hVnn k) (hp1 k)
    have h2 : dirForm (Vf k) (p k : Amb N)
        = gSq (p k : Amb N) + potSq (Vf k) (p k : Amb N) := rfl
    rw [h2] at h1
    linarith [h1, hpot_box k, hbox_le k, hC'b k, hC k]
  have hmbdd : BddAbove (Set.range m) := ⟨C + C', by rintro _ ⟨k, rfl⟩; exact hm_le k⟩
  set Mstar : ℝ := ⨆ k, m k with hM
  have hmleM : ∀ k, m k ≤ Mstar := fun k => le_ciSup hmbdd k
  have hmmono : Monotone m := by
    intro j k hjk
    have h1 : m j ≤ dirForm (Vf j) (r k : Amb N) := by
      rw [hmmin j]
      exact Minimiser.iInf_le_dirForm_unit (L := L) (hVnn j) (hrl2 k)
    have h2 : dirForm (Vf j) (r k : Amb N) ≤ dirForm (Vf k) (r k : Amb N) := by
      rw [dirForm, dirForm]
      gcongr
      exact potSq_le_of_le (hle := hVmono' j k hjk) (h0 := hV0 j)
        (hc0 := Nat.cast_nonneg k)
        (hb := fun x => le_trans (le_abs_self _) (hVbdd k x))
        (hVm := hVmeas j) (hV'm := hVmeas k) ((r k : Amb N))
    exact le_trans h1 h2
  have hMtend : Filter.Tendsto (fun k => Mstar - m k) Filter.atTop (nhds 0) := by
    have h2 : Filter.Tendsto m Filter.atTop (nhds Mstar) := by
      rw [hM]
      exact tendsto_atTop_ciSup hmmono hmbdd
    simpa using h2.const_sub Mstar
  -- ## 6. The excess bound
  have hExcess : ∀ j n, j ≤ n → dirForm (Vf j) (r n : Amb N) ≤ Mstar := by
    intro j n hjn
    have h2 : dirForm (Vf j) (r n : Amb N) ≤ dirForm (Vf n) (r n : Amb N) := by
      rw [dirForm, dirForm]
      gcongr
      exact potSq_le_of_le (hle := hVmono' j n hjn) (h0 := hV0 j)
        (hc0 := Nat.cast_nonneg n)
        (hb := fun x => le_trans (le_abs_self _) (hVbdd n x))
        (hVm := hVmeas j) (hV'm := hVmeas n) ((r n : Amb N))
    exact le_trans h2 (hmleM n)
  -- ## 7. Rellich compactness and the Cauchy estimate
  have hsqbdd : ∀ k, hSq (r k : Amb N) ≤ Mstar + 1 := by
    intro k
    have hrk : ‖((r k : Amb N).1)‖ ^ 2 = 1 := by simpa only [l2Sq] using hrl2 k
    have hmk : m k = gSq (r k : Amb N) + potSq (Vf k) (r k : Amb N) := by
      simp only [hm, dirForm]
    have h2 : 0 ≤ potSq (Vf k) (r k : Amb N) :=
      integral_nonneg_of_ae (Filter.Eventually.of_forall fun y =>
        mul_nonneg (hV0 k y) (sq_nonneg _))
    have h1 : gSq (r k : Amb N) ≤ m k := by linarith [hmk, h2]
    simp only [hSq, l2Sq]
    linarith [hrk, h1, hmleM k]
  obtain ⟨φ, hφ, w, hw⟩ := Minimiser.rellich_subseq N L (Mstar + 1) r hsqbdd
  have hcauchy : CauchySeq (fun n => (r (φ n) : Amb N)) := by
    refine Minimiser.cauchySeq_of_excess_family
      (δ := fun j => 4 * (Mstar - m (φ j))) (κ := fun j => m (φ j) + 1) ?_ ?_ ?_ ?_
    · simpa only [Function.comp_apply, mul_zero] using
        (hMtend.comp hφ.tendsto_atTop).const_mul 4
    · exact fun n => hrl2 (φ n)
    · intro j k l hjk hjl
      have hAr : dirForm (Vf (φ j)) (r (φ k) : Amb N) - m (φ j) ≤ Mstar - m (φ j) :=
        by linarith [hExcess (φ j) (φ k) (hφ.monotone hjk)]
      have hAs : dirForm (Vf (φ j)) (r (φ l) : Amb N) - m (φ j) ≤ Mstar - m (φ j) :=
        by linarith [hExcess (φ j) (φ l) (hφ.monotone hjl)]
      have h1 := Minimiser.hSq_sub_le_of_dirForm_min (V := Vf (φ j)) (C := ((φ j : ℕ) : ℝ))
        (K := 1) (m := m (φ j)) (hVbdd (φ j)) (hVnn (φ j)) (hVmeas (φ j)) (hray (φ j))
        (hrl2 (φ k)) (hrl2 (φ l)) hAr hAs
        (by linarith [hmleM (φ j)]) (by linarith [hmleM (φ j)]) le_rfl
      have hsq : Real.sqrt ((Mstar - m (φ j)) * (Mstar - m (φ j))) = Mstar - m (φ j) := by
        rw [← sq, Real.sqrt_sq (by linarith [hmleM (φ j)])]
      rw [hsq] at h1
      linarith [h1]
    · exact ⟨w, hw⟩
  -- ## 8. The limit point in `Hsub`
  obtain ⟨v, hv⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hvHsub : v ∈ Hsub N L := by
    have hcl : IsClosed (((Hsub N L : Submodule ℝ (Amb N))) : Set (Amb N)) := by
      rw [Hsub, Submodule.topologicalClosure_coe]
      exact isClosed_closure
    exact hcl.mem_of_tendsto hv (Filter.Eventually.of_forall fun n => (r (φ n)).2)
  set q : Hsub N L := ⟨v, hvHsub⟩ with hq
  have hqv : Filter.Tendsto (fun n => (r (φ n) : Amb N)) Filter.atTop (nhds (q : Amb N)) := hv
  have hq1 : l2Sq (q : Amb N) = 1 := by
    have h2 : Filter.Tendsto (fun n => l2Sq (r (φ n) : Amb N)) Filter.atTop
        (nhds (l2Sq (q : Amb N))) :=
      (Work.BoseSym.Bridge.continuous_l2Sq.tendsto (q : Amb N)).comp hqv
    have h3 : (fun n => l2Sq (r (φ n) : Amb N)) = fun _ => (1 : ℝ) :=
      funext fun n => hrl2 (φ n)
    rw [h3] at h2
    exact tendsto_nhds_unique h2 tendsto_const_nhds
  -- ## 9. The energy of the limit against each truncated potential
  have hdirM : ∀ j, dirForm (Vf j) (q : Amb N) ≤ Mstar := by
    intro j
    have h1 : Filter.Tendsto (fun n => dirForm (Vf j) (r (φ n) : Amb N)) Filter.atTop
        (nhds (dirForm (Vf j) (q : Amb N))) :=
      tendsto_dirForm (hVbdd j) (hVmeas j) hqv
    refine le_of_tendsto h1 ?_
    filter_upwards [Filter.eventually_ge_atTop j] with n hn
    exact hExcess j (φ n) (le_trans hn (hφ.id_le n))
  have hpotM : ∀ j, gSq (q : Amb N) + potSq (Vf j) (q : Amb N) ≤ Mstar := fun j => by
    simpa only [dirForm] using hdirM j
  -- ## 10. `Mstar` is at most the liminf of the energies
  set E : ℕ → ℝ := fun n =>
    gSq (p n : Amb N) + ∫ x in BoseGases.box N L,
      W n x * (((p n : Amb N).1 : Conf N → ℝ) x) ^ 2 with hE
  have hEn : ∀ n, m n ≤ E n := by
    intro n
    have h1 : m n ≤ gSq (p n : Amb N) + potSq (Vf n) (p n : Amb N) := by
      rw [hmmin n]
      exact le_trans (Minimiser.iInf_le_dirForm_unit (L := L) (hVnn n) (hp1 n)) (le_of_eq rfl)
    rw [hE]
    linarith [h1, hpot_box n, hbox_le n]
  have hMle : Mstar ≤ Filter.liminf (fun n => E (φ n)) Filter.atTop := by
    rw [hM]
    refine ciSup_le fun k => ?_
    refine le_liminf_of_le ?_ ?_
    · refine ⟨C + C', fun a ha => ?_⟩
      have ha' : ∀ᶠ n in Filter.atTop, a ≤ E (φ n) := Filter.mem_map.mp ha
      rw [Filter.eventually_atTop] at ha'
      obtain ⟨K, hK⟩ := ha'
      refine le_trans (hK K le_rfl) ?_
      rw [hE]
      linarith [hC (φ K), hC'b (φ K)]
    · refine Filter.eventually_atTop.mpr ⟨k, fun n hn => ?_⟩
      calc m k ≤ m (φ n) := hmmono (le_trans hn (hφ.id_le n))
        _ ≤ E (φ n) := hEn (φ n)
  -- ## 11. Monotone convergence in the level `j`
  set Wb : Conf N → ℝ := (BoseGases.box N L).indicator Wlim with hWb
  have hWbmeas : AEMeas N (fun x => Wb x) := by
    have h := aemeas_indicator_of_aesm_on_box (N := N) (L := L) (W := Wlim) hWlimm
    have h' : AEMeas N (fun x => (BoseGases.box N L).indicator Wlim x) := h
    simpa only [hWb] using h'
  have hgmeas : AEMeas N (fun x => Wb x * (((q : Amb N).1 : Conf N → ℝ) x) ^ 2) :=
    (AEMeasurable.mul hWbmeas
      (((Lp.aestronglyMeasurable (q : Amb N).1).pow 2).aemeasurable)).congr
      (Filter.Eventually.of_forall fun x => by simp only [Pi.mul_apply, Pi.pow_apply])
  have hMCT := integrable_and_integral_le_of_tendsto_monotone (N := N)
      (f := fun j x => Vf j x * (((q : Amb N).1 : Conf N → ℝ) x) ^ 2)
      (g := fun x => Wb x * (((q : Amb N).1 : Conf N → ℝ) x) ^ 2)
      (c := Filter.liminf (fun n => E (φ n)) Filter.atTop - gSq (q : Amb N))
      (fun j => Filter.Eventually.of_forall fun x => mul_nonneg (hV0 j x) (sq_nonneg _))
      (fun j x => mul_le_mul_of_nonneg_right (hVmono j x) (sq_nonneg _))
      hgmeas
      (fun x => (hVtend x).mul_const ((((q : Amb N).1 : Conf N → ℝ) x) ^ 2))
      (fun j => by
        have hb : Integrable (fun x => (j : ℝ) * (((q : Amb N).1 : Conf N → ℝ) x) ^ 2) (volC N) :=
          ((Lp.memLp (q : Amb N).1).integrable_sq).const_mul (j : ℝ)
        refine Integrable.mono' hb ?_ ?_
        · exact ((hVmeas j).aestronglyMeasurable.mul
            ((Lp.aestronglyMeasurable (q : Amb N).1).pow 2))
        · filter_upwards with x
          have h1 : 0 ≤ Vf j x := hV0 j x
          have h2 : 0 ≤ (((q : Amb N).1 : Conf N → ℝ) x) ^ 2 := sq_nonneg _
          rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg h1 h2)]
          exact mul_le_mul_of_nonneg_right
            (le_trans (le_abs_self _) (hVbdd j x)) h2)
      (fun j => by
        have h2 : potSq (Vf j) (q : Amb N) ≤ Mstar - gSq (q : Amb N) := by
          linarith [hpotM j]
        have h3 : Mstar - gSq (q : Amb N)
            ≤ Filter.liminf (fun n => E (φ n)) Filter.atTop - gSq (q : Amb N) :=
          by linarith [hMle]
        calc ∫ x, Vf j x * (((q : Amb N).1 : Conf N → ℝ) x) ^ 2
            = potSq (Vf j) (q : Amb N) := rfl
          _ ≤ Filter.liminf (fun n => E (φ n)) Filter.atTop - gSq (q : Amb N) :=
              le_trans h2 h3)
  obtain ⟨hIntg, hIntle⟩ := hMCT
  -- ## 12. Transfer from the indicator potential to `Wlim` on the box
  have hWb_pt : ∀ x, Wb x * (((q : Amb N).1 : Conf N → ℝ) x) ^ 2
      = (BoseGases.box N L).indicator
          (fun x => Wlim x * (((q : Amb N).1 : Conf N → ℝ) x) ^ 2) x := by
    intro x
    by_cases hx : x ∈ BoseGases.box N L
    · simp only [hWb, Set.indicator_of_mem hx]
    · simp only [hWb, Set.indicator_of_notMem hx, zero_mul]
  have hIntOn : IntegrableOn
      (fun x => Wlim x * (((q : Amb N).1 : Conf N → ℝ) x) ^ 2)
      (BoseGases.box N L) MeasureTheory.volume := by
    rw [← integrable_indicator_iff (Submission.BoseGases.box_closed L).measurableSet]
    exact hIntg.congr (Filter.Eventually.of_forall fun x => hWb_pt x)
  have hIntval : ∫ x in BoseGases.box N L,
        Wlim x * (((q : Amb N).1 : Conf N → ℝ) x) ^ 2
      = ∫ x, Wb x * (((q : Amb N).1 : Conf N → ℝ) x) ^ 2 := by
    rw [← integral_indicator (Submission.BoseGases.box_closed L).measurableSet]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => (hWb_pt x).symm)
  -- ## 13. Assembly
  refine ⟨φ, hφ, q, hq1, hIntOn, ?_⟩
  have hmain : gSq (q : Amb N) + ∫ x in BoseGases.box N L,
        Wlim x * (((q : Amb N).1 : Conf N → ℝ) x) ^ 2
      ≤ Filter.liminf (fun n => E (φ n)) Filter.atTop := by
    rw [hIntval]
    linarith [hIntle]
  simpa only [hE] using hmain

end Work.BoseSym.Bridge
