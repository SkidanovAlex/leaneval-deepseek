import Mathlib
import Submission.Work.FeitSibley.Coherence.engine
import Submission.Work.FeitSibley.Coherence.sum_deg_sq_scriptSR_of_le_S
import Submission.Work.FeitSibley.Coherence.relIndex_sup_Q1_eq
import Submission.Work.FeitSibley.Coherence.exists_chi_not_coherent
import Submission.Work.LocalPrelim.pgroup_commutator_ne_self
import Submission.Work.FeitSibley.Coherence.deg_sq_le_of_mem_scriptSR_center
import Submission.Work.FeitSibley.Coherence.scriptSR_Qcomm_nonempty
import Submission.Work.FeitSibley.Coherence.two_mul_card_D_sq_le_card_Q1_sub_two_mul_card_centerQ1
import Submission.Work.FeitSibley.Coherence.Q1_isNilpotent_of_D_ne_bot
import Submission.Work.FeitSibley.Coherence.exists_nontrivial_linear_irr

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.FeitSibley.Coherence.step2`

Peterfalvi II, Appendice XII, step (2): the passage from coherence of `𝒮(S')` to coherence of
`𝒮`.  The proof walks up the lower central series of `S`, adjoining terms with Feit's criterion
(`coherent_of_feit_step`); the arithmetic of each step is the numerical lemma
`numeric_contradiction`.

The main theorem `coherent_scriptS_of_coherent_scriptSR` reduces the target to three hypotheses:

* `hlin` — `Q₁` has a nontrivial *linear* character.  This is what supplies the degree-`|D|`
  element of `𝒮(Q') ⊆ 𝒮(S')` that Feit's inequality `2·χ₀(1)·ψ(1) < ∑ ξ(1)²` needs.
  It holds whenever `D ≠ ⊥` (then `Q₁ ⋊ ⟨d⟩` is a Frobenius group with cyclic complement `⟨d⟩`
  of prime order, `d` acts fixed-point-freely, and **Thompson's theorem** makes `Q₁` nilpotent,
  so `Q₁' < Q₁`); for `D = ⊥` with `Q₁` perfect it *fails*, and the printed proof of App. XII
  does not cover that case either (it tacitly assumes `Z(Q₁) ≠ 1`).  Deriving it from
  `D ≠ ⊥` is the remaining gap of this module (Thompson's theorem, i.e. the parked
  `Work.NPC.thompson_npc`).
* the numerical input `2·|D|² ≤ (|Q₁| - 2)·|Z(Q₁)|` is now *proved*
  (`two_mul_card_D_sq_le_card_Q1_sub_two_mul_card_centerQ1`) from
  `two_mul_card_D_add_one_le_card_Q1` (`2|D|+1 ≤ |Q₁|`) and `D_dvd_card_sub_one`
  (`|D| ∣ |Z(Q₁)| - 1`), so it is no longer a hypothesis.
* `hcoh` — coherence of `𝒮(S')`, the output of Peterfalvi's steps (1), (3) and (4)–(8).

The degree bound `deg_sq_le_of_mem_scriptSR_center`
(`Coherence/deg_sq_le_of_mem_scriptSR_center.lean`) and the non-emptiness
`scriptSR_Qcomm_nonempty` (`Coherence/scriptSR_Qcomm_nonempty.lean`) are imported and used
directly.  Note that the degree bound must use the **full centre** `Z(Q₁) = h.centerQ1`, not
Peterfalvi's `FSZ h = [Q₁,Q₁] ∩ Z(Q₁)`: for abelian `Q₁` the latter is trivial and the numerical
input `2·|D|² ≤ (|Q₁|-2)·|Z|` fails (e.g. `G = PSL(2,7)`, `Q = Q₁ = C₇`, `D = C₃`).
-/

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

noncomputable section
open Classical

namespace Work.FeitSibley.Coherence

variable {G : Type} [Group G] [Fintype G]

theorem indLin_apply_one (H : Subgroup G) (α : ↥H → ℂ) :
    Work.FeitSibley.indLin H α 1 = (H.index : ℂ) * (α 1) :=
  Work.Induction.indFun_apply_one H α

theorem isVChar_indLin_zSpan_scriptS {G : Type} [Group G] [Fintype G]
    (h : Work.FeitSibley.FSData G) {α : ↥h.H → ℂ}
    (hα : α ∈ Work.Coherence.ZSpan (Work.FeitSibley.scriptS h.H h.Q1)) :
    Work.Coherence.IsVChar (Work.FeitSibley.indLin h.H α) := by
  have hle : Work.Coherence.ZSpan (Work.FeitSibley.scriptS h.H h.Q1) ≤
      AddSubgroup.comap (Work.FeitSibley.indLin h.H)
        (AddSubgroup.closure (Work.Coherence.Irr G)) := by
    rw [Work.Coherence.zSpan_le_iff]
    intro x hx
    exact isVChar_indLin_scriptS h hx
  exact hle hα

theorem isVChar_indLin_zSpan0_scriptS {G : Type} [Group G] [Fintype G]
    (h : Work.FeitSibley.FSData G) {α : ↥h.H → ℂ}
    (hα : α ∈ Work.Coherence.ZSpan0 (Work.FeitSibley.scriptS h.H h.Q1)) :
    Work.Coherence.IsVChar (Work.FeitSibley.indLin h.H α) ∧
      Work.FeitSibley.indLin h.H α 1 = 0 :=
  ⟨isVChar_indLin_zSpan_scriptS h ((Work.Coherence.mem_zSpan0.mp hα).1),
    by rw [indLin_apply_one, (Work.Coherence.mem_zSpan0.mp hα).2, mul_zero]⟩

/-- The numerical contradiction underlying Peterfalvi II, App. XII, step (2). -/
theorem numeric_contradiction {D I Q Z c : ℝ} (hD : 0 < D) (hQ : 0 < Q) (hZ : 0 < Z)
    (hI : 2 ≤ I) (hQ1 : 1 ≤ Q) (hcnn : 0 ≤ c)
    (h1 : D * I * (Q - 1) ≤ 2 * D * c)
    (h2 : c ^ 2 ≤ D ^ 2 * I * (Q / Z))
    (hnum : 2 * D ^ 2 ≤ (Q - 2) * Z) : False := by
  have h2' : c ^ 2 * Z ≤ D ^ 2 * I * Q := by
    have h := mul_le_mul_of_nonneg_right h2 (le_of_lt hZ)
    have hzz : D ^ 2 * I * (Q / Z) * Z = D ^ 2 * I * Q := by
      rw [mul_assoc (D ^ 2 * I), div_mul_cancel₀ Q (ne_of_gt hZ)]
    rwa [hzz] at h
  have hc1 : I * (Q - 1) ≤ 2 * c := by nlinarith [h1, hD]
  have hcge : Q - 1 ≤ c := by nlinarith [hc1, hI]
  have hA : I * (Q - 1) ^ 2 ≤ 2 * c ^ 2 := by nlinarith [hc1, hcge, hQ1, hcnn]
  have hB : I * ((Q - 1) ^ 2 * Z) ≤ I * (2 * D ^ 2 * Q) := by
    nlinarith [hA, h2', hZ, hD, hQ]
  have hC : (Q - 1) ^ 2 * Z ≤ 2 * D ^ 2 * Q :=
    le_of_mul_le_mul_left hB (by linarith)
  nlinarith [hC, hnum, hZ, hQ]

/-- `⁅S,S⁆ < S` for a nontrivial nilpotent `S`. -/
theorem commutator_lt_self_of_ne_bot {G : Type} [Group G] (S : Subgroup G)
    [Group.IsNilpotent ↥S] (hS : S ≠ ⊥) : ⁅S, S⁆ < S := by
  obtain ⟨x, hxS, hxcomm⟩ :=
    Work.LocalPrelim.exists_notMem_commutator_of_isNilpotent_le (P := S) (N := S) le_rfl hS
  refine lt_of_le_of_ne ?_ fun heq => hxcomm ?_
  · exact (Subgroup.commutator_le_sup S S).trans (le_of_eq (sup_idem S))
  · exact heq.symm ▸ hxS

/-- **Peterfalvi II, App. XII, step (2).**  If `𝒮(Q')` is non-empty (so `𝒮(S')` contains a
character of degree `|D|`) and the numerical input `2·|D|² ≤ (|Q₁| - 2)·|Z|` holds, then
coherence of `𝒮(S')` implies coherence of `𝒮`. -/
theorem coherent_scriptS_of_coherent_scriptSR {G : Type} [Group G] [Fintype G]
    (h : Work.FeitSibley.FSData G)
    (hlin : ∃ theta ∈ Work.CharCore.Irr ↥h.Q1,
      theta 1 = 1 ∧ theta ≠ (fun _ : ↥h.Q1 => (1 : ℂ)))
    (hcoh : Work.Coherence.Coherent (Work.FeitSibley.scriptSR h.H h.Q1 (FSScomm h))
      (Work.FeitSibley.indLin h.H)) :
    Work.Coherence.Coherent (Work.FeitSibley.scriptS h.H h.Q1)
      (Work.FeitSibley.indLin h.H) := by
  classical
  have hQ := scriptSR_Qcomm_nonempty h hlin
  have hnum := two_mul_card_D_sq_le_card_Q1_sub_two_mul_card_centerQ1 h
  by_cases hSbot : h.S = ⊥
  · have hF : FSScomm h = ⊥ := by
      rw [FSScomm, hSbot]
      exact le_bot_iff.mp ((Subgroup.commutator_le_sup (⊥ : Subgroup G) ⊥).trans
        (le_of_eq (sup_idem ⊥)))
    rw [hF, scriptSR_bot] at hcoh
    exact hcoh
  · let γ : ℕ → Subgroup G := fun i => (h.S).lowerCentralSeries i
    have hγ1 : γ 1 = FSScomm h := by
      show (h.S).lowerCentralSeries 1 = FSScomm h
      rw [Subgroup.lowerCentralSeries_succ, Subgroup.lowerCentralSeries_zero]
    have hγsucc : ∀ k, γ (k+1) = ⁅γ k, h.S⁆ := fun k => by
      show (h.S).lowerCentralSeries (k+1) = ⁅(h.S).lowerCentralSeries k, h.S⁆
      rw [Subgroup.lowerCentralSeries_succ]
    have hγleS : ∀ i, γ i ≤ h.S := fun i => by
      have := Subgroup.lowerCentralSeries_antitone h.S (Nat.zero_le i)
      rwa [Subgroup.lowerCentralSeries_zero] at this
    have hγanti : ∀ k, γ (k+1) ≤ γ k := fun k =>
      Subgroup.lowerCentralSeries_antitone h.S (Nat.le_succ k)
    have hγHn : ∀ i, h.H ≤ Subgroup.normalizer ((γ i : Subgroup G) : Set G) :=
      fun i => H_le_normalizer_lowerCentralSeries h i
    have hS'lt : FSScomm h < h.S := by
      haveI := h.S_nilpotent
      rw [FSScomm]; exact commutator_lt_self_of_ne_bot h.S hSbot
    obtain ⟨m, hm⟩ := (Subgroup.isNilpotent_iff_lowerCentralSeries h.S).mp h.S_nilpotent
    have hbase : Work.Coherence.Coherent (Work.FeitSibley.scriptSR h.H h.Q1 (γ 1))
        (Work.FeitSibley.indLin h.H) := by rw [hγ1]; exact hcoh
    obtain ⟨ψ₀, hψ₀Q⟩ := hQ
    have hψ₀S : ψ₀ ∈ Work.FeitSibley.scriptS h.H h.Q1 := (Finset.mem_filter.mp hψ₀Q).1
    have hψ₀irr : ψ₀ ∈ Work.CharCore.Irr ↥h.H := (Finset.mem_filter.mp hψ₀S).1
    have hψ₀deg1 : ψ₀ 1 = (Nat.card h.D : ℂ) :=
      scriptSR_deg_Qcomm h (scriptSR_Qcomm_le_Q h) le_rfl hψ₀Q
    have hψ₀deg : Work.CharCore.irrDeg ψ₀ = Nat.card h.D := by
      have h2 := Work.CharCore.irrDeg_spec hψ₀irr
      have : (Work.CharCore.irrDeg ψ₀ : ℂ) = (Nat.card h.D : ℂ) := by rw [← h2]; exact hψ₀deg1
      exact_mod_cast this
    have hDpos : (0:ℝ) < Nat.card h.D := by exact_mod_cast Nat.card_pos
    have hQpos : (0:ℝ) < Nat.card h.Q1 := by exact_mod_cast Nat.card_pos
    have hZpos : (0:ℝ) < Nat.card h.centerQ1 := by exact_mod_cast Nat.card_pos
    have hQ1 : (1:ℝ) ≤ Nat.card h.Q1 := by exact_mod_cast Nat.card_pos
    have hS'leQ' : FSScomm h ≤ FSQcomm h := by
      rw [FSScomm, FSQcomm]
      exact Subgroup.commutator_mono h.S_le_Q h.S_le_Q
    have step : ∀ k, 1 ≤ k →
        Work.Coherence.Coherent (Work.FeitSibley.scriptSR h.H h.Q1 (γ k))
          (Work.FeitSibley.indLin h.H) →
        Work.Coherence.Coherent (Work.FeitSibley.scriptSR h.H h.Q1 (γ (k+1)))
          (Work.FeitSibley.indLin h.H) := by
      intro k hk ih
      by_cases heq : γ k = γ (k+1)
      · rw [← heq]; exact ih
      have hγk_le_S' : γ k ≤ FSScomm h := by
        have h : γ k ≤ γ 1 := by
          show (h.S).lowerCentralSeries k ≤ (h.S).lowerCentralSeries 1
          exact Subgroup.lowerCentralSeries_antitone h.S hk
        rwa [hγ1] at h
      have hγk_le_Q' : γ k ≤ FSQcomm h := hγk_le_S'.trans hS'leQ'
      have hklt : γ k < h.S := lt_of_le_of_lt hγk_le_S' hS'lt
      have hkne : (γ k).subgroupOf h.S ≠ ⊤ := by
        intro htop
        have hle : h.S ≤ γ k := fun x hx => by
          have hx' : (⟨x, hx⟩ : ↥h.S) ∈ (γ k).subgroupOf h.S := by rw [htop]; trivial
          exact Subgroup.mem_subgroupOf.mp hx'
        exact (ne_of_lt hklt) (le_antisymm (hγleS k) hle)
      have hI2 : (2:ℝ) ≤ (((γ k).subgroupOf h.S).index : ℝ) := by
        haveI : Finite (↥h.S ⧸ (γ k).subgroupOf h.S) := inferInstance
        have h1 := Subgroup.one_lt_index_of_ne_top hkne
        exact_mod_cast h1
      refine coherent_of_feit_step (S0 := Work.FeitSibley.scriptSR h.H h.Q1 (γ k))
        (S := Work.FeitSibley.scriptSR h.H h.Q1 (γ (k+1))) (τ := Work.FeitSibley.indLin h.H)
        ?_ ?_ ?_ ?_ ih ?_
      · exact scriptSR_subset_of_le h (hγanti k)
      · intro x hx
        exact (Finset.mem_filter.mp (scriptSR_subset_scriptS h _ hx)).1
      · exact (Work.FeitSibley.CharQ.isometry_indLin h).mono (scriptSR_subset_scriptS h _)
      · intro α hα
        exact isVChar_indLin_zSpan0_scriptS h
          (Work.Coherence.zSpan0_mono (scriptSR_subset_scriptS h _) hα)
      · intro χ hχS hχS0 hall
        have hχS' : χ ∈ Work.FeitSibley.scriptS h.H h.Q1 := scriptSR_subset_scriptS h _ hχS
        have hχirr : χ ∈ Work.CharCore.Irr ↥h.H := (Finset.mem_filter.mp hχS').1
        have hψ₀S0 : ψ₀ ∈ Work.FeitSibley.scriptSR h.H h.Q1 (γ k) :=
          scriptSR_subset_of_le h hγk_le_Q' hψ₀Q
        obtain ⟨φ, hφirr, -, hχeq⟩ :=
          (Work.FeitSibley.CharQ.scriptS_eq_image h).mp hχS'
        have hind : χ 1 = Work.Induction.indFun (h.Q.subgroupOf h.H)
            (Work.FeitSibley.CharQ.pull h φ) 1 := by
          rw [hχeq, Work.FeitSibley.CharQ.indQH_eq_indFun]
          rfl
        have hχ1 : χ 1 = (Work.CharCore.irrDeg φ : ℂ) * (ψ₀ 1) := by
          rw [hind, Work.Induction.indFun_apply_one,
            Work.FeitSibley.Coherence.index_subgroupOf_Q, Work.FeitSibley.CharQ.pull_one,
            Work.CharCore.irrDeg_spec hφirr, hψ₀deg1]
          ring
        have hineq := hall ψ₀ hψ₀S0 (Work.CharCore.irrDeg φ) hχ1
        -- real-number consequences
        have hsum := sum_deg_sq_scriptSR_of_le_S h (γ k) (hγleS k) (hγHn k)
        have h1 : (Nat.card h.D : ℝ) * ((((γ k).subgroupOf h.S).index : ℕ) : ℝ) *
              ((Nat.card h.Q1 : ℝ) - 1)
            ≤ 2 * (Nat.card h.D : ℝ) * (Work.CharCore.irrDeg χ : ℝ) := by
          rw [← hsum]
          have hcast : ((∑ ξ ∈ Work.FeitSibley.scriptSR h.H h.Q1 (γ k),
              (Work.CharCore.irrDeg ξ) ^ 2 : ℕ) : ℝ)
              = ∑ ξ ∈ Work.FeitSibley.scriptSR h.H h.Q1 (γ k),
                  ((Work.CharCore.irrDeg ξ : ℝ)) ^ 2 := by push_cast; ring
          rw [← hcast]
          have h2 : ((∑ ξ ∈ Work.FeitSibley.scriptSR h.H h.Q1 (γ k),
              (Work.CharCore.irrDeg ξ) ^ 2 : ℕ) : ℝ)
              ≤ ((2 * Work.CharCore.irrDeg ψ₀ * Work.CharCore.irrDeg χ : ℕ) : ℝ) :=
            by exact_mod_cast hineq
          refine h2.trans (le_of_eq ?_)
          rw [hψ₀deg]; push_cast; ring
        have h2 : (Work.CharCore.irrDeg χ : ℝ) ^ 2 ≤ (Nat.card h.D : ℝ) ^ 2 *
              ((((γ k).subgroupOf h.S).index : ℕ) : ℝ) *
              ((Nat.card h.Q1 : ℝ) / (Nat.card h.centerQ1 : ℝ)) :=
          deg_sq_le_of_mem_scriptSR_center h (γ (k+1)) (γ k) (hγleS _) (hγleS k) (hγanti k)
            (by rw [hγsucc k, Subgroup.commutator_comm]) hχS
        -- numeric contradiction
        refine numeric_contradiction (D := (Nat.card h.D : ℝ))
          (I := ((((γ k).subgroupOf h.S).index : ℕ) : ℝ)) (Q := (Nat.card h.Q1 : ℝ))
          (Z := (Nat.card h.centerQ1 : ℝ)) (c := (Work.CharCore.irrDeg χ : ℝ))
          hDpos hQpos hZpos hI2 hQ1 (Nat.cast_nonneg _) h1 h2 hnum
    have key : ∀ n, 1 ≤ n → n ≤ m → Work.Coherence.Coherent
        (Work.FeitSibley.scriptSR h.H h.Q1 (γ n)) (Work.FeitSibley.indLin h.H) := by
      intro n
      induction n with
      | zero => intro hn; omega
      | succ j ihj =>
          intro hj1 hjm
          rcases Nat.eq_zero_or_pos j with hj0 | hjpos
          · subst hj0; exact hbase
          · exact step j hjpos (ihj hjpos (by omega))
    have hm1 : 1 ≤ m := by
      rcases Nat.eq_zero_or_pos m with h0 | h
      · subst h0
        exact absurd hm (by rw [Subgroup.lowerCentralSeries_zero]; exact hSbot)
      · exact h
    have hmc := key m hm1 le_rfl
    have hbot : γ m = ⊥ := by
      show (h.S).lowerCentralSeries m = ⊥
      exact hm
    rw [hbot, scriptSR_bot] at hmc
    exact hmc

/-- For `D ≠ ⊥`, the Frobenius kernel `Q₁` is nilpotent (Thompson), hence has a nontrivial
linear character; this is the hypothesis `hlin` of `coherent_scriptS_of_coherent_scriptSR`. -/
theorem exists_nontrivial_linear_of_D_ne_bot {G : Type} [Group G] [Fintype G]
    (h : Work.FeitSibley.FSData G) (hD : h.D ≠ ⊥) :
    ∃ theta ∈ Work.CharCore.Irr ↥h.Q1,
      theta 1 = 1 ∧ theta ≠ (fun _ : ↥h.Q1 => (1 : ℂ)) := by
  haveI : Group.IsNilpotent ↥h.Q1 := Q1_isNilpotent_of_D_ne_bot h hD
  haveI : Nontrivial ↥h.Q1 := (Subgroup.nontrivial_iff_ne_bot h.Q1).mpr h.Q1_ne_bot
  exact exists_nontrivial_linear_irr ↥h.Q1

/-- **Step (2) for `D ≠ ⊥`.**  With `hlin` discharged by Thompson's theorem (`Q₁` nilpotent)
and the numerical input proved, the only remaining hypothesis is coherence of `𝒮(S')`. -/
theorem coherent_scriptS_of_coherent_scriptSR_of_D_ne_bot {G : Type} [Group G] [Fintype G]
    (h : Work.FeitSibley.FSData G) (hD : h.D ≠ ⊥)
    (hcoh : Work.Coherence.Coherent (Work.FeitSibley.scriptSR h.H h.Q1 (FSScomm h))
      (Work.FeitSibley.indLin h.H)) :
    Work.Coherence.Coherent (Work.FeitSibley.scriptS h.H h.Q1)
      (Work.FeitSibley.indLin h.H) :=
  coherent_scriptS_of_coherent_scriptSR h (exists_nontrivial_linear_of_D_ne_bot h hD) hcoh

end Work.FeitSibley.Coherence
