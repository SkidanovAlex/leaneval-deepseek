import Mathlib
import Submission.Work.KMTContract.etaCutRegular
import Submission.Work.KMTContract.periodizeCoeEqTsum

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTAreas.A5

open MeasureTheory AddCircle
open Work.Analysis.IonescuWainger Work.KMTContract
open scoped BigOperators

/-! ## Analytic support for the cutoff `η_{≤k}` at the level of the periodisation

Elementary facts about `periodize (etaCut kmtEta k)`, the `1`-periodisation of the rescaled
cutoff `η_{≤k}(θ) = η(θ/2^k)`.  Since `η = kmtEta` is `1` on `[-1/2,1/2]` and vanishes off
`(-1,1)`, the support of `η_{≤k}` is contained in `(-2^k, 2^k)` and the periodisation is trivial
there. -/

/-- `η_{≤k}` vanishes as soon as `2^k ≤ |y|`. -/
private lemma etaCut_kmtEta_eq_zero {k : ℤ} {y : ℝ} (h : (2 : ℝ) ^ k ≤ |y|) :
    etaCut kmtEta k y = 0 := by
  rw [etaCut]
  refine kmtEta_zero ?_
  rw [abs_div, abs_of_pos (zpow_pos (by norm_num : (0 : ℝ) < 2) k)]
  rw [one_le_div (zpow_pos (by norm_num : (0 : ℝ) < 2) k)]
  exact h

/-- `η_{≤k} = 1` on the arc of half the radius: `2|y| < 2^k` implies `|y/2^k| < 1/2`. -/
private lemma etaCut_kmtEta_eq_one {k : ℤ} {y : ℝ} (h : 2 * |y| < (2 : ℝ) ^ k) :
    etaCut kmtEta k y = 1 := by
  rw [etaCut]
  refine kmtEta_one (le_of_lt ?_)
  rw [abs_div, abs_of_pos (zpow_pos (by norm_num : (0 : ℝ) < 2) k)]
  rw [div_lt_iff₀ (zpow_pos (by norm_num : (0 : ℝ) < 2) k)]
  linarith

/-- **The periodisation is trivial on the support of the cutoff.**  For `k ≤ -1` and
`|x| ≤ 1/2`, the periodised cutoff `periodize (η_{≤k})` at `(x : ℝ/ℤ)` is `η_{≤k}(x)`: every
other integer translate of `x` lies at distance `≥ 1/2 ≥ 2^k` from the origin, where the cutoff
vanishes. -/
private lemma periodize_etaCut_coe_eq {k : ℤ} (hk : k ≤ -1) {x : ℝ} (hx : |x| ≤ 1 / 2) :
    periodize (etaCut kmtEta k) (x : Work.Analysis.IonescuWainger.Circle)
      = etaCut kmtEta k x := by
  have hterm : ∀ n : ℤ, n ≠ 0 → etaCut kmtEta k (x + (n : ℝ)) = 0 := by
    intro n hn
    refine etaCut_kmtEta_eq_zero ?_
    have hk2 : (2 : ℝ) ^ k ≤ 1 / 2 := by
      have h := zpow_le_zpow_right₀ (show (1 : ℝ) ≤ 2 by norm_num) hk
      norm_num at h
      linarith
    have hcases : (n : ℝ) ≤ -1 ∨ 1 ≤ (n : ℝ) := by
      have h : n ≤ -1 ∨ 1 ≤ n := by omega
      rcases h with h | h
      · exact Or.inl (by exact_mod_cast h)
      · exact Or.inr (by exact_mod_cast h)
    have hxle : x ≤ 1 / 2 := (abs_le.mp hx).2
    have hxge : -(1 / 2) ≤ x := (abs_le.mp hx).1
    have hpos : (1 : ℝ) / 2 ≤ |x + (n : ℝ)| := by
      rcases hcases with h | h
      · rw [abs_of_nonpos (by linarith : x + (n : ℝ) ≤ 0)]
        linarith
      · rw [abs_of_nonneg (by linarith : 0 ≤ x + (n : ℝ))]
        linarith
    linarith
  calc periodize (etaCut kmtEta k) (x : Work.Analysis.IonescuWainger.Circle)
      = ∑' n : ℤ, etaCut kmtEta k (x + (n : ℝ)) := periodizeCoeEqTsum _ _
    _ = etaCut kmtEta k (x + ((0 : ℤ) : ℝ)) :=
        tsum_eq_single (f := fun n : ℤ => etaCut kmtEta k (x + (n : ℝ))) 0 hterm
    _ = etaCut kmtEta k x := by simp

/-- **Every point of the support of the periodised cutoff is a translate of a real point of
`(-2^k, 2^k)`.**  If `periodize (η_{≤k})` does not vanish at `ξ`, then `ξ = (θ : ℝ/ℤ)` for a
real `θ` with `|θ| < 2^k`. -/
private lemma exists_coe_eq_periodize_etaCut_ne_zero {k : ℤ} {ξ : Work.Analysis.IonescuWainger.Circle}
    (h : periodize (etaCut kmtEta k) ξ ≠ 0) :
    ∃ θ : ℝ, (θ : Work.Analysis.IonescuWainger.Circle) = ξ ∧ |θ| < (2 : ℝ) ^ k := by
  set x : ℝ := (AddCircle.equivIco (1 : ℝ) 0 ξ).val with hxdef
  have hxeq : (x : Work.Analysis.IonescuWainger.Circle) = ξ := by rw [hxdef]; exact AddCircle.coe_equivIco
  have hne : ∃ n : ℤ, etaCut kmtEta k (x + (n : ℝ)) ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    refine h ?_
    have hper : periodize (etaCut kmtEta k) ξ
        = ∑' n : ℤ, etaCut kmtEta k (x + (n : ℝ)) := by
      rw [← hxeq]
      exact periodizeCoeEqTsum _ _
    rw [hper]
    have h0 : (fun n : ℤ => etaCut kmtEta k (x + (n : ℝ))) = fun _ => (0 : ℂ) :=
      funext fun n => hcon n
    rw [h0, tsum_zero]
  obtain ⟨n, hn⟩ := hne
  refine ⟨x + (n : ℝ), ?_, ?_⟩
  · have hnc : (((n : ℝ)) : Work.Analysis.IonescuWainger.Circle) = 0 := by
      rw [AddCircle.coe_eq_zero_iff]
      exact ⟨n, by simp⟩
    rw [AddCircle.coe_add, hxeq, hnc, add_zero]
  · by_contra hcon
    push_neg at hcon
    exact hn (etaCut_kmtEta_eq_zero hcon)

/-! ## The multiplicativity of the two Ionescu–Wainger symbols -/

/-- **The product of the two IW symbols is the finer one.**  Both sides are symbols over the
same frequency set `(ℚ/ℤ)_{≤l'}`; the coarser symbol `∑_{β ∈ (ℚ/ℤ)_{≤l}} η_{≤k}(ξ - β)` equals
`1` wherever the finer symbol `∑_{α ∈ (ℚ/ℤ)_{≤l'}} η_{≤k'}(ξ - α)` does not vanish, because then
`ξ` lies in the major arc `α + ℝ_{≤k'}` of some `α ∈ (ℚ/ℤ)_{≤l'}`, on which all the other terms
`η_{≤k}(ξ - β)` vanish by non-aliasing at scale `k`. -/
theorem iwSymbolSet_prod_kmtEta (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    {l l' : ℕ} {k k' : ℤ} (hl : l' ≤ l) (hk : k' < k) (hk1 : k ≤ -1)
    (hNA : Work.Analysis.IonescuWainger.NonAliasing k
      (Work.Analysis.IonescuWainger.iwArithFreqs ρ l)) :
    Work.Analysis.IonescuWainger.iwSymbolSet (Work.Analysis.IonescuWainger.iwArithFreqs ρ l')
        (Work.Analysis.IonescuWainger.periodize
          (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta k'))
      * Work.Analysis.IonescuWainger.iwSymbolSet (Work.Analysis.IonescuWainger.iwArithFreqs ρ l)
        (Work.Analysis.IonescuWainger.periodize
          (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta k))
      = Work.Analysis.IonescuWainger.iwSymbolSet (Work.Analysis.IonescuWainger.iwArithFreqs ρ l')
        (Work.Analysis.IonescuWainger.periodize
          (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta k')) := by
  have hsub : iwArithFreqs ρ l' ⊆ iwArithFreqs ρ l := iwArithFreqs_mono hρ hρ1 hl
  have hmono : (2 : ℝ) ^ k' ≤ (2 : ℝ) ^ k :=
    zpow_le_zpow_right₀ (show (1 : ℝ) ≤ 2 by norm_num) (by omega)
  have hpow : 2 * (2 : ℝ) ^ k' ≤ (2 : ℝ) ^ k := by
    have h3 : (2 : ℝ) ^ (k' + 1) ≤ (2 : ℝ) ^ k :=
      zpow_le_zpow_right₀ (show (1 : ℝ) ≤ 2 by norm_num) (by omega)
    have h4 : (2 : ℝ) ^ (k' + 1) = 2 * (2 : ℝ) ^ k' := by
      rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_one]
      ring
    linarith
  funext ξ
  simp only [iwSymbolSet_apply, Pi.mul_apply]
  have hkey : ∀ α₀ ∈ iwArithFreqs ρ l',
      periodize (etaCut kmtEta k') (ξ - α₀) ≠ 0 →
      ∑ β ∈ iwArithFreqs ρ l, periodize (etaCut kmtEta k) (ξ - β) = 1 := by
    intro α₀ hα₀ hα₀ne
    have hα₀' : α₀ ∈ iwArithFreqs ρ l := hsub hα₀
    obtain ⟨θ, hθeq, hθlt⟩ := exists_coe_eq_periodize_etaCut_ne_zero hα₀ne
    have hθhalf : |θ| ≤ 1 / 2 := by
      have h4 : (2 : ℝ) ^ k' ≤ 1 / 4 := by
        have h := zpow_le_zpow_right₀ (show (1 : ℝ) ≤ 2 by norm_num) (show k' ≤ -2 by omega)
        norm_num at h
        linarith
      linarith
    have hθ2 : 2 * |θ| < (2 : ℝ) ^ k := by
      have h1 : 2 * |θ| < 2 * (2 : ℝ) ^ k' := by linarith
      linarith
    have hval : periodize (etaCut kmtEta k) (ξ - α₀) = 1 := by
      have h1 : periodize (etaCut kmtEta k) (ξ - α₀)
          = periodize (etaCut kmtEta k) ((θ : ℝ) : Work.Analysis.IonescuWainger.Circle) := by
        rw [hθeq]
      rw [h1, periodize_etaCut_coe_eq hk1 hθhalf, etaCut_kmtEta_eq_one hθ2]
    have hzero : ∀ β ∈ iwArithFreqs ρ l, β ≠ α₀ →
        periodize (etaCut kmtEta k) (ξ - β) = 0 := by
      intro β hβ hβne
      by_contra hbne
      obtain ⟨θ', hθ'eq, hθ'lt⟩ := exists_coe_eq_periodize_etaCut_ne_zero hbne
      have hθmem : θ ∈ realArc k := by
        have hle : |θ| ≤ (2 : ℝ) ^ k := le_of_lt (lt_of_lt_of_le hθlt hmono)
        rw [realArc, Set.mem_Icc]
        exact ⟨(abs_le.mp hle).1, (abs_le.mp hle).2⟩
      have hθ'mem : θ' ∈ realArc k := by
        have hle : |θ'| ≤ (2 : ℝ) ^ k := le_of_lt hθ'lt
        rw [realArc, Set.mem_Icc]
        exact ⟨(abs_le.mp hle).1, (abs_le.mp hle).2⟩
      have heq : β + ((θ' : ℝ) : Work.Analysis.IonescuWainger.Circle)
          = α₀ + ((θ : ℝ) : Work.Analysis.IonescuWainger.Circle) := by
        rw [hθ'eq, hθeq]
        abel
      exact hβne (hNA β hβ α₀ hα₀' θ' hθ'mem θ hθmem heq).1
    calc ∑ β ∈ iwArithFreqs ρ l, periodize (etaCut kmtEta k) (ξ - β)
        = ∑ β ∈ iwArithFreqs ρ l,
            (if α₀ = β then periodize (etaCut kmtEta k) (ξ - β) else 0) := by
          refine Finset.sum_congr rfl (fun β hβ => ?_)
          by_cases hb : α₀ = β
          · rw [if_pos hb]
          · rw [if_neg hb]
            exact hzero β hβ (fun h => hb h.symm)
      _ = (if α₀ ∈ iwArithFreqs ρ l
            then periodize (etaCut kmtEta k) (ξ - α₀) else 0) :=
          Finset.sum_ite_eq _ _ _
      _ = 1 := by rw [if_pos hα₀', hval]
  by_cases h : (∑ α ∈ iwArithFreqs ρ l', periodize (etaCut kmtEta k') (ξ - α)) = 0
  · rw [h, zero_mul]
  · obtain ⟨α₀, hα₀, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
    rw [hkey α₀ hα₀ hne, mul_one]

end Work.KMTAreas.A5
