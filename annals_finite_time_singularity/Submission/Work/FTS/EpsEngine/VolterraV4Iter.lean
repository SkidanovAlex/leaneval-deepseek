/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/EpsEngine/VolterraV4Iter.lean` — the a-priori bounds of the *applicable*
# Volterra–Picard engine

The sibling engine `Work.FTS.StrongEps.EpsLocalPStar.exists_volterra_v3` (with its a-priori bounds
`iter_bounds`) is mathematically sound but **cannot be instantiated**: three of its hypotheses are
quantified over *arbitrary* curves `v : ℝ → Fn` of `P`-profiles,

* `hcont : ∀ v, (∀ s ∈ Icc 0 δ, P (v s)) → ContinuousOn (fun s => F (v s) z θ) (Icc 0 δ)`,
* `hmeas : ∀ v, (∀ s ∈ Icc 0 δ, P (v s)) → AEStronglyMeasurable (fun p => F (v p.1) p.2.1 p.2.2)`,
* `hident : ∀ v x, (∀ n, P (v n)) → … → Tendsto (fun n => F (v n) z θ) …`,

and a curve may be chosen *discontinuously* in `s` (if `P` has two elements, take `v s := h₀` for
`s < δ/2` and `v s := u` afterwards): such a curve satisfies `P (v s)` for every `s` but its
`F`-image is *not* continuous, so `hcont` is *false* for every non-degenerate `P` (and `hmeas`,
`hident` are unprovable for the same reason).  The engine's proof, however, uses these hypotheses
only for the curves it constructs itself — the Picard iterates `s ↦ slice (iter F h₀ n) s` and
their limit.  This file (and its companion `VolterraV4Main.lean`) is the resulting **applicable**
engine: the curve-level hypotheses are replaced by their iterate-indexed forms (which mention only
the explicit iterates of `VolterraAux/Iter.lean`, hence are stateable and provable by the
consumer), and the identification of the limit of `F` with `F` of the limit is *derived* from the
pointwise control `hpt` together with the membership `hlimP` of the limit profile.

The proof is a verbatim adaptation of `VolterraAux/IterBounds.lean` +
`EpsLocalPStar/exists_volterra_v3.lean`; only the hypothesis names and the three application sites
change.  Everything here is `sorry`-free.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.StrongEps.EpsSpace
import Submission.Work.FTS.Galerkin.Defs
import Submission.Work.FTS.StrongEps.EpsLocalPStar.VolterraAux.Defs
import Submission.Work.FTS.StrongEps.EpsLocalPStar.VolterraAux.Iter
import Submission.Work.FTS.StrongEps.EpsLocalPStar.VolterraAux.EpsMem_and_EpsSq_intervalIntegral_le
import Submission.Work.FTS.StrongEps.EpsLocalPStar.VolterraAux.EpsMem_and_EpsSq_le_of_tendsto_ae
import Submission.Work.FTS.EpsEngine.IterContMeas
import Submission.Work.FTS.EpsEngine.AK2_sections_restrict

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter
open Work.FTS.Galerkin (Fn Fam slice)
open Work.FTS.StrongEps
open Work.FTS.StrongEps.EpsLocalPStar

namespace Work.FTS.EpsEngine

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## The a priori bounds for the Picard iterates (iterate-indexed hypotheses) -/

/-- A difference of two Picard iterates is the parametric integral of the difference of the
right-hand sides. -/
theorem diff_eq_integral_v4 {F : Fn → Fn} {h₀ : Fn} {P : Fn → Prop} {δ : ℝ}
    (hP : ∀ n τ, τ ∈ Set.Icc 0 δ → P (slice (iter F h₀ n) τ))
    (hcontIter : ∀ n : ℕ, ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      ContinuousOn (fun s => F (slice (iter F h₀ n) s) z θ) (Set.Icc 0 δ))
    {N₁ N₂ : ℕ} {τ z θ : ℝ} (hτ : τ ∈ Set.Icc 0 δ) (h1 : 1 ≤ N₁) (h2 : 1 ≤ N₂)
    (hz : 0 < z) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) :
    slice (iter F h₀ N₁) τ z θ - slice (iter F h₀ N₂) τ z θ
      = ∫ s in (0 : ℝ)..τ,
          (F (slice (iter F h₀ (N₁ - 1)) s) z θ - F (slice (iter F h₀ (N₂ - 1)) s) z θ) := by
  have hint : ∀ k : ℕ, IntervalIntegrable (fun s => F (slice (iter F h₀ k) s) z θ) volume 0 τ :=
    fun k => ContinuousOn.intervalIntegrable_of_Icc hτ.1
      ((hcontIter k z θ hz hθ0 hθ1).mono
        (Set.Icc_subset_Icc_right hτ.2))
  obtain ⟨N₁', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : N₁ ≠ 0)
  obtain ⟨N₂', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : N₂ ≠ 0)
  rw [show N₁' + 1 - 1 = N₁' from by omega, show N₂' + 1 - 1 = N₂' from by omega]
  rw [iter_succ F h₀ N₁', iter_succ F h₀ N₂']
  simp only [Work.FTS.Galerkin.slice_apply]
  rw [intervalIntegral.integral_sub (hint N₁') (hint N₂')]
  ring

/-- The a priori bounds of the Picard iteration of the Volterra map: `P` is preserved, the
increments (`wseq`) and the differences of iterates are bounded in `EpsSq` by the geometric
sequence `q ^ (n+1)`, and they are bounded pointwise. -/
theorem iter_bounds_v4 {α : ℝ} {F : Fn → Fn} {h₀ : Fn} {P : Fn → Prop} {Cpt L δ q r : ℝ}
    (hδ : 0 < δ) (hL : 0 < L) (hδL : δ * Real.sqrt L < 1)
    (hq : q = δ ^ 2 * L) (hr : r = Real.sqrt q) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hr0 : 0 ≤ r) (hrpow : ∀ n : ℕ, Real.sqrt (q ^ n) = r ^ n)
    (hCpt : 0 ≤ Cpt) (hP₀ : P h₀)
    (hbd : ∀ u : Fn, P u → EpsMem α (F u) ∧ EpsSq α (F u) ≤ L)
    (hlip : ∀ u v : Fn, P u → P v → EpsMem α (fun z θ => u z θ - v z θ) →
      EpsSq α (fun z θ => F u z θ - F v z θ) ≤ L * EpsSq α (fun z θ => u z θ - v z θ))
    (hpt : ∀ u v : Fn, P u → P v → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |F u z θ - F v z θ| ≤ Cpt * Real.sqrt (EpsSq α (fun z θ => u z θ - v z θ)))
    (hcontP : ∀ u : Fn, P u → ContinuousOn (fun q : ℝ × ℝ => F u q.1 q.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hzeroP : ∀ u : Fn, P u → ∀ q : ℝ × ℝ,
      q ∉ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) → F u q.1 q.2 = 0)
    (hkeepIter : ∀ n : ℕ, ∀ τ : ℝ, τ ∈ Set.Icc 0 δ →
      P (fun z θ => h₀ z θ + ∫ s in (0 : ℝ)..τ, F (slice (iter F h₀ n) s) z θ)) :
    (∀ n τ, τ ∈ Set.Icc 0 δ → P (slice (iter F h₀ n) τ)) ∧
    (∀ M τ, τ ∈ Set.Icc 0 δ → 1 ≤ M →
      EpsMem α (fun z θ => slice (iter F h₀ M) τ z θ - h₀ z θ) ∧
      EpsSq α (fun z θ => slice (iter F h₀ M) τ z θ - h₀ z θ) ≤ q) ∧
    (∀ M K, 1 ≤ K → K ≤ M → ∀ τ ∈ Set.Icc 0 δ,
      EpsMem α (fun z θ => slice (iter F h₀ M) τ z θ - slice (iter F h₀ K) τ z θ) ∧
      EpsSq α (fun z θ => slice (iter F h₀ M) τ z θ - slice (iter F h₀ K) τ z θ)
        ≤ q ^ (K + 1)) ∧
    (∀ n τ, τ ∈ Set.Icc 0 δ → EpsSq α (wseq F h₀ n τ) ≤ q ^ (n + 1)) ∧
    (∀ n τ, τ ∈ Set.Icc 0 δ → 1 ≤ n → ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |wseq F h₀ n τ z θ| ≤ δ * Cpt * r ^ n) := by
  have hδ0 : 0 ≤ δ := hδ.le
  have hL0 : 0 ≤ L := hL.le
  have hqdef : q = δ ^ 2 * L := hq
  -- ## 1. `P` is preserved along the iteration (the iterate-indexed hypothesis `hkeepIter`)
  have hP : ∀ n τ, τ ∈ Set.Icc 0 δ → P (slice (iter F h₀ n) τ) := by
    intro n
    induction n with
    | zero =>
      intro τ _
      exact hP₀
    | succ m ih =>
      intro τ hτ
      exact hkeepIter m τ hτ
  -- ## 1'. continuity in the fake time and joint measurability of the Picard curves, *derived*
  -- from the class data (`IterContMeas.iter_cont_meas`)
  obtain ⟨hcontIter, hmeasIter⟩ :=
    iter_cont_meas (α := α) (Cpt := Cpt) (L := L) (δ := δ) (F := F) (h₀ := h₀) (P := P)
      hδ hL0 hCpt hP hcontP hzeroP hbd hpt
  have hrestr : ∀ τ ∈ Set.Icc 0 δ,
      (MeasureTheory.volume.restrict (Set.uIoc 0 τ)) ≤
        (MeasureTheory.volume.restrict (Set.Icc 0 δ)) :=
    fun τ hτ => restrict_uIoc_le_Icc hτ
  -- ## 2. a.e. sections of jointly measurable families are `AK2`
  have hAKsec : ∀ n : ℕ, ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.Icc 0 δ)),
      AK2 α (F (slice (iter F h₀ n) s)) :=
    fun n => AK2_sections_restrict (hmeasIter n)
  -- ## 3. a difference of two iterates is a parametric integral of the `F`-difference
  have hdiff_eq : ∀ (N₁ N₂ : ℕ) (τ z θ : ℝ), τ ∈ Set.Icc 0 δ → 1 ≤ N₁ → 1 ≤ N₂ →
      0 < z → 0 < θ → θ < Real.pi / 2 →
      slice (iter F h₀ N₁) τ z θ - slice (iter F h₀ N₂) τ z θ
        = ∫ s in (0 : ℝ)..τ,
            (F (slice (iter F h₀ (N₁ - 1)) s) z θ - F (slice (iter F h₀ (N₂ - 1)) s) z θ) := by
    intro N₁ N₂ τ z θ hτ h1 h2 hz hθ0 hθ1
    have hint : ∀ k : ℕ, IntervalIntegrable (fun s => F (slice (iter F h₀ k) s) z θ) volume 0 τ :=
      fun k => ContinuousOn.intervalIntegrable_of_Icc hτ.1
        ((hcontIter k z θ hz hθ0 hθ1).mono
          (Set.Icc_subset_Icc_right hτ.2))
    obtain ⟨N₁', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : N₁ ≠ 0)
    obtain ⟨N₂', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : N₂ ≠ 0)
    rw [show N₁' + 1 - 1 = N₁' from by omega, show N₂' + 1 - 1 = N₂' from by omega]
    rw [iter_succ F h₀ N₁', iter_succ F h₀ N₂']
    simp only [Work.FTS.Galerkin.slice_apply]
    rw [intervalIntegral.integral_sub (hint N₁') (hint N₂')]
    ring
  -- ## 4. a priori bounds for the iterates
  have hBmain : ∀ M : ℕ,
      (∀ τ ∈ Set.Icc 0 δ, 1 ≤ M →
        EpsMem α (fun z θ => slice (iter F h₀ M) τ z θ - h₀ z θ) ∧
        EpsSq α (fun z θ => slice (iter F h₀ M) τ z θ - h₀ z θ) ≤ q) ∧
      (∀ K : ℕ, 1 ≤ K → K ≤ M → ∀ τ ∈ Set.Icc 0 δ,
        EpsMem α (fun z θ => slice (iter F h₀ M) τ z θ - slice (iter F h₀ K) τ z θ) ∧
        EpsSq α (fun z θ => slice (iter F h₀ M) τ z θ - slice (iter F h₀ K) τ z θ)
          ≤ q ^ (K + 1)) := by
    intro M
    induction M with
    | zero =>
      exact ⟨fun τ hτ h1 => absurd h1 (by omega),
        fun K hK hKM τ hτ => absurd hKM (by omega)⟩
    | succ M ih =>
      obtain ⟨ih0, ihK⟩ := ih
      refine ⟨?_, ?_⟩
      · -- (i) the `h₀`-difference
        intro τ hτ _
        have hdiff : (fun z θ => slice (iter F h₀ (M + 1)) τ z θ - h₀ z θ)
            = fun z θ => ∫ s in (0 : ℝ)..τ, F (slice (iter F h₀ M) s) z θ := by
          funext z θ
          show h₀ z θ + (∫ s in (0 : ℝ)..τ, F (slice (iter F h₀ M) s) z θ) - h₀ z θ
            = ∫ s in (0 : ℝ)..τ, F (slice (iter F h₀ M) s) z θ
          ring
        rw [hdiff]
        have hm : MeasureTheory.AEStronglyMeasurable
            (fun p : ℝ × ℝ × ℝ =>
              F (slice (iter F h₀ M) p.1) p.2.1 p.2.2 * epsW α p.2.1 p.2.2)
            ((MeasureTheory.volume.restrict (Set.uIoc 0 τ)).prod DomM) :=
          aesm_weighted_uIoc_of_restrict (α := α) (Φ := fun s => F (slice (iter F h₀ M) s)) hτ (hmeasIter M)
        have hmono : (MeasureTheory.volume.restrict (Set.uIoc 0 τ)) ≤
            (MeasureTheory.volume.restrict (Set.Icc 0 τ)) := by
          refine MeasureTheory.Measure.restrict_mono (s := Set.uIoc 0 τ)
            (s' := Set.Icc 0 τ) ?_ le_rfl
          rw [Set.uIoc_of_le hτ.1]
          exact Set.Ioc_subset_Icc_self
        have hb : ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.uIoc 0 τ)),
            epsL2 α (F (slice (iter F h₀ M) s)) ≤ ENNReal.ofReal L := by
          refine (ae_mono hmono) ?_
          refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc ?_
          intro s hs
          exact epsL2_le_ofReal_of_mem (hbd _ (hP M s ⟨hs.1, le_trans hs.2 hτ.2⟩)).1
            (hbd _ (hP M s ⟨hs.1, le_trans hs.2 hτ.2⟩)).2
        obtain ⟨hmem, hbd'⟩ :=
          Work.FTS.StrongEps.EpsLocalPStar.VolterraAux.EpsMem_and_EpsSq_intervalIntegral_le (α := α) (τ := τ) (B := L)
            hτ.1 hL0 hm hb
        exact ⟨hmem, le_trans hbd' (by
          rw [hqdef]
          have h1 : τ * τ ≤ δ ^ 2 := by nlinarith [hτ.1, hτ.2]
          have h2 : τ * (τ * L) = τ * τ * L := by ring
          rw [h2]
          exact mul_le_mul_of_nonneg_right h1 hL0)⟩
      · -- (ii) the differences of two iterates
        intro K hK hKM τ hτ
        rcases eq_or_lt_of_le hKM with hEq | hLt
        · -- K = M+1: the difference vanishes
          subst hEq
          have hz : (fun z θ => slice (iter F h₀ (M + 1)) τ z θ - slice (iter F h₀ (M + 1)) τ z θ)
              = fun _ _ => (0 : ℝ) := by funext z θ; ring
          rw [hz]
          exact ⟨EpsMem_zero2 α, by rw [EpsSq_zero]; exact pow_nonneg hq0 _⟩
        · have hKM' : K ≤ M := Nat.lt_succ_iff.mp hLt
          have heq : ∀ᵐ p ∂DomM,
              (slice (iter F h₀ (M + 1)) τ p.1 p.2 - slice (iter F h₀ K) τ p.1 p.2)
              = ∫ s in (0 : ℝ)..τ,
                  (F (slice (iter F h₀ M) s) p.1 p.2
                    - F (slice (iter F h₀ (K - 1)) s) p.1 p.2) :=
            ae_of_forall_open (fun z hz θ hθ0 hθ1 =>
              hdiff_eq (M + 1) K τ z θ hτ (by omega) hK hz hθ0 hθ1)
          have hm : MeasureTheory.AEStronglyMeasurable
              (fun p : ℝ × ℝ × ℝ =>
                (F (slice (iter F h₀ M) p.1) p.2.1 p.2.2
                  - F (slice (iter F h₀ (K - 1)) p.1) p.2.1 p.2.2) * epsW α p.2.1 p.2.2)
              ((MeasureTheory.volume.restrict (Set.uIoc 0 τ)).prod DomM) := by
            have h1 := aesm_weighted_uIoc_of_restrict (α := α) (Φ := fun s => F (slice (iter F h₀ M) s)) hτ (hmeasIter M)
            have h2 := aesm_weighted_uIoc_of_restrict (α := α) (Φ := fun s => F (slice (iter F h₀ (K - 1)) s)) hτ (hmeasIter (K - 1))
            exact (h1.sub h2).congr (by filter_upwards with p; simp only [Pi.sub_apply]; ring)
          have hb : ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.uIoc 0 τ)),
              epsL2 α (fun z θ => F (slice (iter F h₀ M) s) z θ
                - F (slice (iter F h₀ (K - 1)) s) z θ) ≤ ENNReal.ofReal (L * q ^ K) := by
            have hsec : ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.uIoc 0 τ)),
                AK2 α (F (slice (iter F h₀ M) s)) ∧ AK2 α (F (slice (iter F h₀ (K - 1)) s)) :=
              (ae_mono (hrestr τ hτ)) ((hAKsec M).and (hAKsec (K - 1)))
            filter_upwards [hsec, MeasureTheory.ae_restrict_mem measurableSet_uIoc]
              with s hAKs hs
            have hsIcc : s ∈ Set.Icc 0 δ := by
              rw [Set.uIoc_of_le hτ.1] at hs
              exact ⟨le_of_lt hs.1, le_trans hs.2 hτ.2⟩
            have hmemD : EpsMem α (fun z θ => slice (iter F h₀ M) s z θ
                - slice (iter F h₀ (K - 1)) s z θ) := by
              rcases eq_or_lt_of_le hK with hK1 | hK2
              · subst hK1
                have := (ih0 s hsIcc (by omega : 1 ≤ M)).1
                simpa using this
              · exact (ihK (K - 1) (by omega) (by omega) s hsIcc).1
            have hsqD : EpsSq α (fun z θ => slice (iter F h₀ M) s z θ
                - slice (iter F h₀ (K - 1)) s z θ) ≤ q ^ K := by
              rcases eq_or_lt_of_le hK with hK1 | hK2
              · subst hK1
                have := (ih0 s hsIcc (by omega : 1 ≤ M)).2
                simpa using this
              · have h := (ihK (K - 1) (by omega) (by omega) s hsIcc).2
                rwa [Nat.sub_add_cancel hK] at h
            have hmemG : EpsMem α (fun z θ => F (slice (iter F h₀ M) s) z θ
                - F (slice (iter F h₀ (K - 1)) s) z θ) :=
              EpsMem_sub2 hAKs.1 hAKs.2 (hbd _ (hP M s hsIcc)).1 (hbd _ (hP (K - 1) s hsIcc)).1
            have hsqG : EpsSq α (fun z θ => F (slice (iter F h₀ M) s) z θ
                - F (slice (iter F h₀ (K - 1)) s) z θ) ≤ L * q ^ K :=
              le_trans (hlip _ _ (hP M s hsIcc) (hP (K - 1) s hsIcc) hmemD)
                (mul_le_mul_of_nonneg_left hsqD hL0)
            exact epsL2_le_ofReal_of_mem hmemG hsqG
          obtain ⟨hmemI, hbdI⟩ :=
            Work.FTS.StrongEps.EpsLocalPStar.VolterraAux.EpsMem_and_EpsSq_intervalIntegral_le (α := α) (τ := τ) (B := L * q ^ K)
              hτ.1 (mul_nonneg hL0 (pow_nonneg hq0 K)) hm hb
          refine ⟨EpsMem_congr_ae (heq.mono fun p hp => hp.symm) hmemI, ?_⟩
          have hEps : EpsSq α (fun z θ => slice (iter F h₀ (M + 1)) τ z θ - slice (iter F h₀ K) τ z θ)
              = EpsSq α (fun z θ => ∫ s in (0 : ℝ)..τ,
                  (F (slice (iter F h₀ M) s) z θ - F (slice (iter F h₀ (K - 1)) s) z θ)) :=
            EpsSq_congr_ae heq
          rw [hEps]
          refine le_trans hbdI ?_
          calc τ * (τ * (L * q ^ K)) = τ * τ * (L * q ^ K) := by ring
            _ ≤ δ ^ 2 * (L * q ^ K) :=
                mul_le_mul_of_nonneg_right (by nlinarith [hτ.1, hτ.2])
                  (mul_nonneg hL0 (pow_nonneg hq0 K))
            _ = q ^ (K + 1) := by
                rw [show δ ^ 2 * (L * q ^ K) = q * q ^ K by rw [hqdef]; ring, pow_succ']
  -- ## 5. the increments are bounded
  have hwsq : ∀ n τ, τ ∈ Set.Icc 0 δ → EpsSq α (wseq F h₀ n τ) ≤ q ^ (n + 1) := by
    intro n τ hτ
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      have h := (hBmain 1).1 τ hτ (le_refl 1)
      show EpsSq α (fun z θ => slice (iter F h₀ 1) τ z θ - h₀ z θ) ≤ q ^ (0 + 1)
      rw [pow_one]
      exact h.2
    · have h := (hBmain (n + 1)).2 n hn (by omega) τ hτ
      show EpsSq α (fun z θ => slice (iter F h₀ (n + 1)) τ z θ - slice (iter F h₀ n) τ z θ)
        ≤ q ^ (n + 1)
      exact h.2
  have hwpt : ∀ n τ, τ ∈ Set.Icc 0 δ → 1 ≤ n → ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |wseq F h₀ n τ z θ| ≤ δ * Cpt * r ^ n := by
    intro n τ hτ hn z θ hz hθ0 hθ1
    have hint : ∀ k : ℕ,
        IntervalIntegrable (fun s => F (slice (iter F h₀ k) s) z θ) volume 0 τ :=
      fun k => ContinuousOn.intervalIntegrable_of_Icc hτ.1
        ((hcontIter k z θ hz hθ0 hθ1).mono
          (Set.Icc_subset_Icc_right hτ.2))
    have hiter : wseq F h₀ n τ z θ
        = ∫ s in (0 : ℝ)..τ,
            (F (slice (iter F h₀ n) s) z θ - F (slice (iter F h₀ (n - 1)) s) z θ) := by
      obtain ⟨n', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
      have h1 : slice (iter F h₀ (n' + 1 + 1)) τ z θ
          = h₀ z θ + ∫ s in (0 : ℝ)..τ, F (slice (iter F h₀ (n' + 1)) s) z θ := by
        rw [iter_succ F h₀ (n' + 1)]
        simp only [Work.FTS.Galerkin.slice_apply]
      have h2 : slice (iter F h₀ (n' + 1)) τ z θ
          = h₀ z θ + ∫ s in (0 : ℝ)..τ, F (slice (iter F h₀ n') s) z θ := by
        rw [iter_succ F h₀ n']
        simp only [Work.FTS.Galerkin.slice_apply]
      have h3 : n' + 1 - 1 = n' := by omega
      show slice (iter F h₀ (n' + 1 + 1)) τ z θ - slice (iter F h₀ (n' + 1)) τ z θ = _
      rw [h3, h1, h2]
      rw [intervalIntegral.integral_sub (hint (n' + 1)) (hint n')]
      ring
    rw [hiter, ← Real.norm_eq_abs]
    have h2 : ∀ s ∈ Set.uIoc (0 : ℝ) τ,
        ‖F (slice (iter F h₀ n) s) z θ - F (slice (iter F h₀ (n - 1)) s) z θ‖ ≤ Cpt * r ^ n := by
      intro s hs
      rw [Real.norm_eq_abs]
      have hsIcc : s ∈ Set.Icc 0 δ := by
        rw [Set.uIoc_of_le hτ.1] at hs
        exact ⟨le_of_lt hs.1, le_trans hs.2 hτ.2⟩
      have hwseq : wseq F h₀ (n - 1) s
          = fun z θ => slice (iter F h₀ n) s z θ - slice (iter F h₀ (n - 1)) s z θ := by
        funext z θ
        simp only [wseq, Nat.sub_add_cancel hn]
      have hsq : EpsSq α (fun z θ => slice (iter F h₀ n) s z θ
          - slice (iter F h₀ (n - 1)) s z θ) ≤ q ^ n := by
        have h := hwsq (n - 1) s hsIcc
        rw [Nat.sub_add_cancel hn] at h
        rwa [hwseq] at h
      calc |F (slice (iter F h₀ n) s) z θ - F (slice (iter F h₀ (n - 1)) s) z θ|
          ≤ Cpt * Real.sqrt (EpsSq α (fun z θ => slice (iter F h₀ n) s z θ
              - slice (iter F h₀ (n - 1)) s z θ)) :=
            hpt _ _ (hP n s hsIcc) (hP (n - 1) s hsIcc) z θ hz hθ0 hθ1
        _ ≤ Cpt * r ^ n := by
            rw [← hrpow n]
            exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hsq) hCpt
    have h3 := intervalIntegral.norm_integral_le_of_norm_le_const (C := Cpt * r ^ n)
      (a := (0 : ℝ)) (b := τ) h2
    rw [sub_zero, abs_of_nonneg hτ.1] at h3
    refine h3.trans ?_
    nlinarith [hτ.1, hτ.2, mul_nonneg hCpt (pow_nonneg hr0 n)]
  exact ⟨hP, (fun M τ hτ hM => (hBmain M).1 τ hτ hM),
    (fun M K hK hKM τ hτ => (hBmain M).2 K hK hKM τ hτ), hwsq, hwpt⟩

end Work.FTS.EpsEngine
