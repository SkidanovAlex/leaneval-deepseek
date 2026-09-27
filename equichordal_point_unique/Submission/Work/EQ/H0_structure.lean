import Mathlib
import Submission.Work.EQ.DefsCore
import Submission.Work.EQ.HeteroAlgebra
import Submission.Work.EQ.H0_section_local

/-! Guidance from the project lead (the requester): see the header kept below.

# `H0_structure`

`⁰H` is a spread over the `ψ₁`-plane: `ψ₁` is a local homeomorphism, the local sections are
analytic, and `σ = hShift a` is a bijection of `H0`.

This file proceeds as follows.
* `hShiftInv`, and the fact that `hShift a` and `hShiftInv a` are inverse homeomorphisms of
  `ChainData` (the shift is just a reindexing plus the scalings `λ`, `1/λ`).
* `IsChain` is invariant under both, hence `H0` is invariant under both.
* The reduction of the "local homeomorphism" clause to the local section clause.
-/

namespace Work.EQ

open Filter _root_.Topology

/-- The inverse of the shift `hShift a` on chain data: `Pₙ ↦ Pₙ₋₁`, `ψ₁ ↦ ψ₁/λ`,
`ψ₂ ↦ λψ₂`. -/
noncomputable def hShiftInv (a : ℝ) (p : ChainData) : ChainData :=
  (fun n => p.1 (n - 1), p.2.1 / (eqLam a : ℂ), (eqLam a : ℂ) * p.2.2)

lemma eqLam_pos_of {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) : 0 < eqLam a := by
  rw [eqLam]; exact div_pos (by linarith) (by linarith)

lemma eqLam_ne_zero_of {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) : eqLam a ≠ 0 :=
  ne_of_gt (eqLam_pos_of ha0 ha1)

lemma eqLam_lt_one_of {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) : eqLam a < 1 := by
  rw [eqLam, div_lt_one (by linarith)]; linarith

lemma continuous_hShift (a : ℝ) : Continuous (hShift a) := by
  unfold hShift
  refine Continuous.prodMk (continuous_pi fun n => ?_) (Continuous.prodMk ?_ ?_)
  · exact (continuous_apply (n + 1)).comp continuous_fst
  · exact continuous_const.mul (continuous_fst.comp continuous_snd)
  · exact (continuous_snd.comp continuous_snd).div_const _

lemma continuous_hShiftInv (a : ℝ) : Continuous (hShiftInv a) := by
  unfold hShiftInv
  refine Continuous.prodMk (continuous_pi fun n => ?_) (Continuous.prodMk ?_ ?_)
  · exact (continuous_apply (n - 1)).comp continuous_fst
  · exact (continuous_fst.comp continuous_snd).div_const _
  · exact continuous_const.mul (continuous_snd.comp continuous_snd)

lemma hShift_hShiftInv {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) : hShift a ∘ hShiftInv a = id := by
  have hlam : (eqLam a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (eqLam_ne_zero_of ha0 ha1)
  funext q
  ext n <;> simp only [hShift, hShiftInv, Function.comp_apply, id_eq] <;> ring_nf
  · rw [mul_comm ((eqLam a : ℂ)) q.2.1]; exact mul_inv_cancel_right₀ hlam q.2.1
  · rw [mul_comm ((eqLam a : ℂ)) q.2.2]; exact mul_inv_cancel_right₀ hlam q.2.2

lemma hShiftInv_hShift {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) : hShiftInv a ∘ hShift a = id := by
  have hlam : (eqLam a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (eqLam_ne_zero_of ha0 ha1)
  funext q
  ext n <;> simp only [hShift, hShiftInv, Function.comp_apply, id_eq] <;> ring_nf
  · rw [mul_comm ((eqLam a : ℂ)) q.2.1]; exact mul_inv_cancel_right₀ hlam q.2.1
  · rw [mul_comm ((eqLam a : ℂ)) q.2.2]; exact mul_inv_cancel_right₀ hlam q.2.2

lemma hShift_inv_eq {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (q : ChainData) :
    hShiftInv a (hShift a q) = q := congrFun (hShiftInv_hShift ha0 ha1) q

lemma hShift_inv_eq' {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (q : ChainData) :
    hShift a (hShiftInv a q) = q := congrFun (hShift_hShiftInv ha0 ha1) q

lemma isChain_hShift {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {p : ChainData}
    (hp : IsChain a h p) : IsChain a h (hShift a p) := by
  have hlam : (eqLam a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (eqLam_ne_zero_of ha0 ha1)
  obtain ⟨hreg, hpsi1, hpsi2, hfwd, hbwd⟩ := hp
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro n; exact hreg (n + 1)
  · exact mul_ne_zero hlam hpsi1
  · exact div_ne_zero hpsi2 hlam
  · have h1 : ∀ᶠ n : ℕ in atTop,
        p.1 ((n : ℤ) + 1) = germC a h ((eqLam a : ℂ) ^ (n + 1) * p.2.1) :=
      (tendsto_add_atTop_nat 1).eventually hfwd
    filter_upwards [h1] with n hn
    simp only [hShift]
    rw [hn, pow_succ]
    ring_nf
  · have h2 : ∀ᶠ n : ℕ in atTop,
        p.1 (-(((n - 1 : ℕ)) : ℤ)) = ugermC a h ((eqLam a : ℂ) ^ (n - 1) * p.2.2) :=
      (tendsto_sub_atTop_nat 1).eventually hbwd
    filter_upwards [h2, eventually_ge_atTop 1] with n hn hn1
    simp only [hShift]
    have hcast : -((n : ℤ)) + 1 = -(((n - 1 : ℕ)) : ℤ) := by omega
    rw [hcast, hn]
    congr 1
    have hpow : (eqLam a : ℂ) ^ n = (eqLam a : ℂ) ^ (n - 1) * (eqLam a : ℂ) := by
      conv_lhs => rw [show n = (n - 1) + 1 by omega]
      rw [pow_succ]
    rw [hpow, mul_assoc, mul_div_cancel₀ p.2.2 hlam]

lemma isChain_hShiftInv {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {p : ChainData}
    (hp : IsChain a h p) : IsChain a h (hShiftInv a p) := by
  have hlam : (eqLam a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (eqLam_ne_zero_of ha0 ha1)
  obtain ⟨hreg, hpsi1, hpsi2, hfwd, hbwd⟩ := hp
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro n
    simp only [hShiftInv]
    rw [show (n : ℤ) + 1 - 1 = n by ring]
    simpa [sub_add_cancel] using hreg (n - 1)
  · exact div_ne_zero hpsi1 hlam
  · exact mul_ne_zero hlam hpsi2
  · have h1 : ∀ᶠ n : ℕ in atTop,
        p.1 (((n - 1 : ℕ)) : ℤ) = germC a h ((eqLam a : ℂ) ^ (n - 1) * p.2.1) :=
      (tendsto_sub_atTop_nat 1).eventually hfwd
    filter_upwards [h1, eventually_ge_atTop 1] with n hn hn1
    simp only [hShiftInv]
    have hcast : ((n : ℤ)) - 1 = (((n - 1 : ℕ)) : ℤ) := by omega
    rw [hcast, hn]
    congr 1
    have hpow : (eqLam a : ℂ) ^ n = (eqLam a : ℂ) ^ (n - 1) * (eqLam a : ℂ) := by
      conv_lhs => rw [show n = (n - 1) + 1 by omega]
      rw [pow_succ]
    rw [hpow, mul_assoc, mul_div_cancel₀ p.2.1 hlam]
  · have h2 : ∀ᶠ n : ℕ in atTop,
        p.1 (-(((n + 1 : ℕ)) : ℤ)) = ugermC a h ((eqLam a : ℂ) ^ (n + 1) * p.2.2) :=
      (tendsto_add_atTop_nat 1).eventually hbwd
    filter_upwards [h2] with n hn
    simp only [hShiftInv]
    rw [show -((n : ℤ)) - 1 = -(((n + 1 : ℕ)) : ℤ) by push_cast; ring, hn, pow_succ]
    congr 1
    ring

lemma hShift_mem_H0 {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {p : ChainData}
    (hp : p ∈ H0 a h) : hShift a p ∈ H0 a h := by
  obtain ⟨e, he, f, hfcont, hf0, hf⟩ := hp
  have hlam : 0 < eqLam a := eqLam_pos_of ha0 ha1
  have hlam' : (eqLam a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (eqLam_ne_zero_of ha0 ha1)
  have key : ∀ u : ℂ, u ∈ Metric.ball (hShift a p).2.1 (eqLam a * e) →
      u / (eqLam a : ℂ) ∈ Metric.ball p.2.1 e := by
    intro u hu
    simp only [Metric.mem_ball, dist_eq_norm] at hu ⊢
    have hu' : ‖u - (eqLam a : ℂ) * p.2.1‖ < eqLam a * e := by simpa only [hShift] using hu
    have h1 : u / (eqLam a : ℂ) - p.2.1 =
        (u - (eqLam a : ℂ) * p.2.1) / (eqLam a : ℂ) := by
      rw [sub_div, mul_div_cancel_left₀ p.2.1 hlam']
    have h2 : ‖u / (eqLam a : ℂ) - p.2.1‖ = ‖u - (eqLam a : ℂ) * p.2.1‖ / eqLam a := by
      rw [h1, norm_div, Complex.norm_of_nonneg (le_of_lt hlam)]
    have h3 : ‖u - (eqLam a : ℂ) * p.2.1‖ / eqLam a < e := by
      rw [div_lt_iff₀ hlam]
      exact lt_of_lt_of_eq hu' (mul_comm (eqLam a) e)
    linarith [h2, h3]
  refine ⟨eqLam a * e, mul_pos hlam he, (fun u => hShift a (f (u / (eqLam a : ℂ)))), ?_, ?_, ?_⟩
  · exact (continuous_hShift a).comp_continuousOn (hfcont.comp (continuousOn_id.div_const _) key)
  · have hbase : (eqLam a : ℂ) * p.2.1 / (eqLam a : ℂ) = p.2.1 :=
      mul_div_cancel_left₀ p.2.1 hlam'
    simp only [hShift, hbase, hf0]
  · intro u hu
    obtain ⟨hc, hpsi⟩ := hf _ (key u hu)
    refine ⟨isChain_hShift ha0 ha1 hc, ?_⟩
    simp only [hShift]
    rw [hpsi]
    exact mul_div_cancel₀ u hlam'

lemma hShiftInv_mem_H0 {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {p : ChainData}
    (hp : p ∈ H0 a h) : hShiftInv a p ∈ H0 a h := by
  obtain ⟨e, he, f, hfcont, hf0, hf⟩ := hp
  have hlam : 0 < eqLam a := eqLam_pos_of ha0 ha1
  have hlam' : (eqLam a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (eqLam_ne_zero_of ha0 ha1)
  have key : ∀ u : ℂ, u ∈ Metric.ball (p.2.1 / (eqLam a : ℂ)) (e / eqLam a) →
      (eqLam a : ℂ) * u ∈ Metric.ball p.2.1 e := by
    intro u hu
    simp only [Metric.mem_ball, dist_eq_norm] at hu ⊢
    have h1 : (eqLam a : ℂ) * u - p.2.1 =
        (eqLam a : ℂ) * (u - p.2.1 / (eqLam a : ℂ)) := by
      rw [mul_sub, mul_div_cancel₀ p.2.1 hlam']
    have h2 : ‖(eqLam a : ℂ) * u - p.2.1‖ = eqLam a * ‖u - p.2.1 / (eqLam a : ℂ)‖ := by
      rw [h1, norm_mul, Complex.norm_of_nonneg (le_of_lt hlam)]
    have h3 : eqLam a * ‖u - p.2.1 / (eqLam a : ℂ)‖ < eqLam a * (e / eqLam a) :=
      mul_lt_mul_of_pos_left hu hlam
    have h4 : eqLam a * (e / eqLam a) = e := mul_div_cancel₀ e (eqLam_ne_zero_of ha0 ha1)
    linarith [h2, h3, h4]
  refine ⟨e / eqLam a, div_pos he hlam, (fun u => hShiftInv a (f ((eqLam a : ℂ) * u))), ?_, ?_, ?_⟩
  · exact (continuous_hShiftInv a).comp_continuousOn
      (hfcont.comp (continuousOn_const.mul continuousOn_id) key)
  · have hbase : (eqLam a : ℂ) * (p.2.1 / (eqLam a : ℂ)) = p.2.1 :=
      mul_div_cancel₀ p.2.1 hlam'
    simp only [hShiftInv, hbase, hf0]
  · intro u hu
    obtain ⟨hc, hpsi⟩ := hf _ (key u hu)
    refine ⟨isChain_hShiftInv ha0 ha1 hc, ?_⟩
    simp only [hShiftInv]
    rw [hpsi]
    exact mul_div_cancel_left₀ u hlam'



/-! ### Elementary facts about the relation, used by the local structure -/

lemma eq_false_of_ne_true {a : ℝ} {P Q : ℂ × ℂ} (h : EqRelC a P Q)
    (hQ : bsq (subO1 a Q) ≠ 0) (hne : P ≠ invBranch a true Q) : P = invBranch a false Q := by
  rcases eqRelC_solutions h hQ with h' | h'
  · exact absurd h' hne
  · exact h'

/-! ### Reduction of the local-homeomorphism clause to the local-section clause -/

open Classical in
/-- A local section of `H0` over the `ψ₁`-plane whose image is a neighbourhood of `p` gives a
partial homeomorphism at `p` for the projection `ψ₁`.  This is the reduction of the
`IsLocalHomeomorph` clause of `H0_structure` to its local-section clause. -/
lemma isLocalHomeomorph_pi_of_section {a : ℝ} {h : ℂ → ℂ}
    (H : ∀ p ∈ H0 a h, ∃ ρ : ℝ, 0 < ρ ∧ ∃ f : ℂ → ChainData, f p.2.1 = p ∧
      (∀ u ∈ Metric.ball p.2.1 ρ, f u ∈ H0 a h ∧ (f u).2.1 = u) ∧
      (∀ n : ℤ, ContinuousOn (fun u => (f u).1 n) (Metric.ball p.2.1 ρ)) ∧
      ContinuousOn (fun u => (f u).2.2) (Metric.ball p.2.1 ρ) ∧
      f '' Metric.ball p.2.1 ρ ∈ 𝓝[H0 a h] p) :
    IsLocalHomeomorph (fun q : H0 a h => (q : ChainData).2.1) := by
  intro q
  obtain ⟨ρ, hρ, f, hf0, hfmem, hfcont, hfcont2, hfnbhd⟩ := H (q : ChainData) q.2
  -- continuity of the section `f` on its ball
  have hpsi1_cont : ContinuousOn (fun u : ℂ => (f u).2.1) (Metric.ball (q : ChainData).2.1 ρ) :=
    continuousOn_id.congr (fun u hu => (hfmem u hu).2)
  have hfc : ContinuousOn f (Metric.ball (q : ChainData).2.1 ρ) :=
    ContinuousOn.prodMk (continuousOn_pi' fun n => hfcont n)
      (ContinuousOn.prodMk hpsi1_cont hfcont2)
  -- an open neighbourhood `W` of `p` with `W ∩ H0 ⊆ f '' ball`
  obtain ⟨V, hVnhds, hVsub⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hfnbhd
  obtain ⟨W, hWV, hWopen, hWp⟩ := mem_nhds_iff.mp hVnhds
  -- the source `S = W ∩ H0` and the target `T = ball ∩ f ⁻¹' W` of the partial homeomorphism
  set S : Set (H0 a h) := {x | (x : ChainData) ∈ W} with hSdef
  set T : Set ℂ := {u | u ∈ Metric.ball (q : ChainData).2.1 ρ ∧ f u ∈ W} with hTdef
  have hSopen : IsOpen S := IsOpen.preimage continuous_subtype_val hWopen
  have hTopen : IsOpen T := by
    rw [hTdef]
    exact ContinuousOn.isOpen_inter_preimage hfc Metric.isOpen_ball hWopen
  have hmem_f : ∀ x : H0 a h, x ∈ S → (x : ChainData) ∈ f '' Metric.ball (q : ChainData).2.1 ρ :=
    fun x hx => hVsub ⟨hWV hx, x.2⟩
  have hkey : ∀ x : H0 a h, x ∈ S → (f ((x : ChainData).2.1) : ChainData) = (x : ChainData) := by
    intro x hx
    obtain ⟨u, hu, hfu⟩ := hmem_f x hx
    have hpsi : (x : ChainData).2.1 = u := by rw [← hfu]; exact (hfmem u hu).2
    rw [hpsi, hfu]
  have hball_mem : ∀ x : H0 a h, x ∈ S → (x : ChainData).2.1 ∈ Metric.ball (q : ChainData).2.1 ρ := by
    intro x hx
    obtain ⟨u, hu, hfu⟩ := hmem_f x hx
    have hpsi : (x : ChainData).2.1 = u := by rw [← hfu]; exact (hfmem u hu).2
    rw [hpsi]; exact hu
  -- the section, as a total function into the subtype
  set g : ℂ → H0 a h := fun y =>
    if hy : y ∈ Metric.ball (q : ChainData).2.1 ρ then ⟨f y, (hfmem y hy).1⟩ else q with hgdef
  have hgval : ∀ y ∈ Metric.ball (q : ChainData).2.1 ρ, (g y : ChainData) = f y := by
    intro y hy
    rw [hgdef]
    simp only [dif_pos hy]
  have hgval' : ∀ y ∈ T, (g y : ChainData) = f y := fun y hy => hgval y hy.1
  have hcont_g : ContinuousOn g (Metric.ball (q : ChainData).2.1 ρ) := by
    refine (IsInducing.continuousOn_iff IsInducing.subtypeVal).mpr ?_
    exact hfc.congr (fun y hy => hgval y hy)
  -- the partial equivalence
  let hpe : PartialEquiv (H0 a h) ℂ :=
    { toFun := fun x : H0 a h => (x : ChainData).2.1
      invFun := g
      source := S
      target := T
      map_source' := by
        intro x hx
        exact ⟨hball_mem x hx, by rw [hkey x hx]; exact hx⟩
      map_target' := by
        intro y hy
        rw [hgdef]
        simp only [dif_pos hy.1]
        exact hy.2
      left_inv' := by
        intro x hx
        have hbx := hball_mem x hx
        show g ((x : ChainData).2.1) = x
        exact Subtype.ext (by rw [hgval _ hbx, hkey x hx])
      right_inv' := by
        intro y hy
        show (g y : ChainData).2.1 = y
        rw [hgval y hy.1]
        exact (hfmem y hy.1).2 }
  have hc1 : ContinuousOn (⇑hpe) hpe.source :=
    ((continuous_fst.comp continuous_snd).comp continuous_subtype_val).continuousOn
  have hc2 : ContinuousOn hpe.invFun hpe.target := hcont_g.mono (fun y hy => hy.1)
  exact ⟨OpenPartialHomeomorph.mk (PartialHomeomorph.mk hpe hc1 hc2) hSopen hTopen, hWp, rfl⟩

/-- **`⁰H` is a Riemann surface spread over the `ψ₁`-plane (Rychlik §5.9, §6.2).** `ψ₁` is
a local homeomorphism on `H0` (subspace topology), the local sections are analytic in every
chain coordinate and in `ψ₂`, and the shift is a bijection of `H0`. -/
theorem H0_structure {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) :
    IsLocalHomeomorph (fun q : H0 a h => (q : ChainData).2.1) ∧
    (∀ p ∈ H0 a h, ∃ ρ : ℝ, 0 < ρ ∧ ∃ f : ℂ → ChainData, f p.2.1 = p ∧
      (∀ u ∈ Metric.ball p.2.1 ρ, f u ∈ H0 a h ∧ (f u).2.1 = u) ∧
      (∀ n : ℤ, AnalyticOnNhd ℂ (fun u => (f u).1 n) (Metric.ball p.2.1 ρ)) ∧
      AnalyticOnNhd ℂ (fun u => (f u).2.2) (Metric.ball p.2.1 ρ) ∧
      f '' Metric.ball p.2.1 ρ ∈ 𝓝[H0 a h] p) ∧
    (∀ p ∈ H0 a h, hShift a p ∈ H0 a h) ∧ (∀ q ∈ H0 a h, ∃ p ∈ H0 a h, hShift a p = q) := by
  have hloc := H0_section_local ha0 ha1 hh
  have hcont : ∀ p ∈ H0 a h, ∃ ρ : ℝ, 0 < ρ ∧ ∃ f : ℂ → ChainData, f p.2.1 = p ∧
      (∀ u ∈ Metric.ball p.2.1 ρ, f u ∈ H0 a h ∧ (f u).2.1 = u) ∧
      (∀ n : ℤ, ContinuousOn (fun u => (f u).1 n) (Metric.ball p.2.1 ρ)) ∧
      ContinuousOn (fun u => (f u).2.2) (Metric.ball p.2.1 ρ) ∧
      f '' Metric.ball p.2.1 ρ ∈ 𝓝[H0 a h] p := by
    intro p hp
    obtain ⟨ρ, hρ, f, hf0, hfmem, hfan, hfan2, hnbhd⟩ := hloc p hp
    exact ⟨ρ, hρ, f, hf0, hfmem, fun n => (hfan n).continuousOn,
      hfan2.continuousOn, Filter.le_principal_iff.mp hnbhd⟩
  refine ⟨isLocalHomeomorph_pi_of_section hcont, fun p hp => ?_, fun p hp => ?_, fun q hq => ?_⟩
  · obtain ⟨ρ, hρ, f, hf0, hfmem, hfan, hfan2, hnbhd⟩ := hloc p hp
    exact ⟨ρ, hρ, f, hf0, hfmem, hfan, hfan2, Filter.le_principal_iff.mp hnbhd⟩
  · exact hShift_mem_H0 ha0 ha1 hp
  · exact ⟨hShiftInv a q, hShiftInv_mem_H0 ha0 ha1 hq, hShift_inv_eq' ha0 ha1 q⟩

end Work.EQ
