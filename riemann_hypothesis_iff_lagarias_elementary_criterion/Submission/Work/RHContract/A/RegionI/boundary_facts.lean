import Mathlib
import Submission.Work.RHContract.A.RegionI.Defs
import Submission.Work.RHContract.A.RegionI.cF_basic
import Submission.Work.RHContract.A.ca_margin_lower

/-!
# Region I: the boundary facts of the block certificate

The Region I certificate (`Work.RHContract.A.RegionI.robinBound_of_levels`) covers the range
of parameters `ε` whose largest prime factor `ξ(ε)` lies in `[1530, 30000)`.  This file
supplies the two *boundary facts* that translate the hypothesis `1530 ≤ ξ(ε)` (resp.
`ξ(ε) < 30000`) into an explicit rational bracket for `ε`:

* `1530 ≤ ξ(ε) → ε ≤ F(1531,1)`;
* `ξ(ε) < 30000 → F(30011,1) < ε`,

where `F(p,k) = log((p^{k+1}−1)/(p^{k+1}−p))/log p` is the Nicolas level function.

Both facts rest on the defining equivalence `1 ≤ ⌊μ(p,ε)⌋₊ ↔ ε ≤ F(p,1)`
(`Commons.NumberTheory.Robin.caMu_ge_iff_caF`): the support of `N_ε` consists of those primes
`p < ⌈e^{2/ε}⌉+2` with `μ(p,ε) ≥ 1`.
-/

open scoped BigOperators

namespace Work.RHContract.A.RegionI

namespace boundaryFacts

noncomputable section

/-- `F(p,1) = log(1 + 1/p)/log p` for `p ≥ 2`. -/
lemma cF_one (p : ℕ) (hp : 2 ≤ p) :
    Work.RHContract.RegionI.cF p 1 = Real.log (1 + 1 / (p : ℝ)) / Real.log (p : ℝ) := by
  have h := cFBasic.ratio_eq_one_add_inv_caS (p := p) (k := 1) hp (le_refl 1)
  have hS : (Work.RHContract.RegionI.caS p 1 : ℝ) = (p : ℝ) := by
    simp [Work.RHContract.RegionI.caS]
  unfold Work.RHContract.RegionI.cF
  rw [h, hS]

/-- `p ↦ F(p,1)` is non-increasing for `p ≥ 2`. -/
lemma cF_one_anti {p q : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) (h : p ≤ q) :
    Work.RHContract.RegionI.cF q 1 ≤ Work.RHContract.RegionI.cF p 1 := by
  rcases eq_or_lt_of_le h with hh | hh
  · subst hh; exact le_rfl
  · exact le_of_lt (cFBasic.cF_anti_p (p := p) (q := q) (k := 1) hp hq (le_refl 1) hh)

/-- The exponent of `p` in `N_ε` is at least `1` iff `ε ≤ F(p,1)`. -/
lemma one_le_floor_caMu_iff {p : ℕ} {ε : ℝ} (hp : 2 ≤ p) (hε : 0 < ε) :
    1 ≤ ⌊Work.RHPlan.caMu p ε⌋₊ ↔ ε ≤ Work.RHContract.RegionI.cF p 1 := by
  rw [Nat.one_le_floor_iff]
  simpa only [Work.RHPlan.caMu, Work.RHContract.RegionI.cF, Nat.cast_one] using
    (Commons.NumberTheory.Robin.caMu_ge_iff_caF p ε 1 hp hε (le_refl 1))

/-- The numeric boundary at the bottom of Region I: `F(30011,1) < 2/log 30009`. -/
lemma cF_30011_lt : Work.RHContract.RegionI.cF 30011 1 < 2 / Real.log 30009 := by
  have h11 : (0 : ℝ) < Real.log 30011 := Real.log_pos (by norm_num)
  have h09 : (0 : ℝ) < Real.log 30009 := Real.log_pos (by norm_num)
  have hlt : Real.log 30009 < Real.log 30011 := Real.log_lt_log (by norm_num) (by norm_num)
  have hA : Work.RHContract.RegionI.cF 30011 1 < (1 / 30011) / Real.log 30011 := by
    rw [cF_one 30011 (by norm_num)]
    have hlog : Real.log (1 + 1 / (30011 : ℝ)) < 1 / 30011 := by
      have h := Real.log_lt_sub_one_of_pos (x := 1 + 1 / (30011 : ℝ)) (by norm_num) (by norm_num)
      linarith
    exact div_lt_div_of_pos_right hlog h11
  have hB : (1 / 30011) / Real.log 30011 < 2 / Real.log 30009 := by
    rw [div_lt_div_iff₀ h11 h09]
    have h1 : (1 / 30011 : ℝ) * Real.log 30009 < (1 / 30011 : ℝ) * Real.log 30011 :=
      mul_lt_mul_of_pos_left hlt (by norm_num)
    have h2 : (1 / 30011 : ℝ) * Real.log 30011 ≤ 2 * Real.log 30011 :=
      mul_le_mul_of_nonneg_right (by norm_num) (le_of_lt h11)
    linarith
  linarith

/-- If `ε < 2/log 30009` then `e^{2/ε} > 30009`. -/
lemma exp_two_div_gt {ε : ℝ} (hε : 0 < ε) (h : ε < 2 / Real.log 30009) :
    (30009 : ℝ) < Real.exp (2 / ε) := by
  have hL : (0 : ℝ) < Real.log 30009 := Real.log_pos (by norm_num)
  have hLε : Real.log 30009 * ε < 2 := by
    have h2 : (2 / Real.log 30009) * Real.log 30009 = 2 := by field_simp
    have h' := mul_lt_mul_of_pos_right h hL
    rw [h2] at h'
    linarith [h']
  have hlt : Real.log 30009 < 2 / ε := (lt_div_iff₀ hε).mpr hLε
  calc (30009 : ℝ) = Real.exp (Real.log 30009) := (Real.exp_log (by norm_num)).symm
    _ < Real.exp (2 / ε) := Real.exp_lt_exp.mpr hlt

end

end boundaryFacts

open boundaryFacts

theorem boundary_facts (ε : ℝ) (hε : 0 < ε) :
    (((1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ)) → ε ≤ Work.RHContract.RegionI.cF 1531 1) ∧
    (((Work.RHPlan.caXi ε : ℝ) < 30000) → Work.RHContract.RegionI.cF 30011 1 < ε) := by
  refine ⟨?_, ?_⟩
  · -- `1530 ≤ ξ(ε)`: `ξ(ε)` is a prime of the support, hence `≥ 1531`, and `ε ≤ F(ξ(ε),1) ≤ F(1531,1)`.
    intro h
    have hξ : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ) := h
    have hne : (Work.RHPlan.caSupport ε).Nonempty :=
      Work.RHContract.A.caSupport_nonempty ε hξ
    have hmem : Work.RHPlan.caXi ε ∈ Work.RHPlan.caSupport ε := by
      rw [Work.RHContract.A.caXi_eq_max' ε hξ]
      exact Finset.max'_mem _ hne
    have hprime : Nat.Prime (Work.RHPlan.caXi ε) :=
      Work.RHContract.A.prime_of_mem_caSupport hmem
    have hfloor : 1 ≤ ⌊Work.RHPlan.caMu (Work.RHPlan.caXi ε) ε⌋₊ :=
      (Finset.mem_filter.mp hmem).2
    have hcF : ε ≤ Work.RHContract.RegionI.cF (Work.RHPlan.caXi ε) 1 :=
      (one_le_floor_caMu_iff hprime.two_le hε).mp hfloor
    have hne1530 : Work.RHPlan.caXi ε ≠ 1530 := by
      intro hh
      rw [hh] at hprime
      exact (by norm_num : ¬ Nat.Prime 1530) hprime
    have hge1530 : 1530 ≤ Work.RHPlan.caXi ε := by exact_mod_cast h
    have hge : 1531 ≤ Work.RHPlan.caXi ε := by omega
    exact le_trans hcF (cF_one_anti (by norm_num) hprime.two_le hge)
  · -- `ξ(ε) < 30000`: contrapositively, `ε ≤ F(30011,1)` puts the prime `30011` in the support.
    intro h
    by_contra hcon
    have hcon : ε ≤ Work.RHContract.RegionI.cF 30011 1 := not_lt.mp hcon
    have hε' : ε < 2 / Real.log 30009 := lt_of_le_of_lt hcon cF_30011_lt
    have hexp : (30009 : ℝ) < Real.exp (2 / ε) := exp_two_div_gt hε hε'
    have hceil : 30009 < Nat.ceil (Real.exp (2 / ε)) := Nat.lt_ceil.mpr hexp
    have hrange : 30011 < Nat.ceil (Real.exp (2 / ε)) + 2 := by omega
    have hfloor : 1 ≤ ⌊Work.RHPlan.caMu 30011 ε⌋₊ :=
      (one_le_floor_caMu_iff (p := 30011) (ε := ε) (by norm_num) hε).mpr hcon
    have hmem : 30011 ∈ Work.RHPlan.caSupport ε :=
      Finset.mem_filter.mpr
        ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hrange, by norm_num⟩, hfloor⟩
    have hle : 30011 ≤ Work.RHPlan.caXi ε := by
      have hsup := Finset.le_sup (f := id) hmem
      simpa only [Work.RHPlan.caXi, Function.id_def] using hsup
    have : (30011 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ) := by exact_mod_cast hle
    linarith

end Work.RHContract.A.RegionI
