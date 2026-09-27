import Mathlib
import Submission.Work.Drive.seeleyDefs
import Submission.Work.Drive.momentSequences
import Submission.Work.Drive.seeleySum_bounds

/-!
# Localized bounds for the scaled Seeley series

`Work.Drive.seeleySum_bounds` assumes the flat jet bounds for `R` on the whole space; the proof,
however, only ever evaluates these bounds at points `(x, -(b j) * s)` whose first coordinate is
the first coordinate `x` of the point at which the conclusion is required.  This file records the
resulting localized statement, which is what the (local) construction of Seeley's extension
actually needs.
-/

set_option linter.unusedSectionVars false

namespace Work.Drive

open scoped ContDiff Topology
open Filter

variable {X E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Pointwise bound for one summand of the Seeley series, in the localized form where the jet
bounds for `R` are only assumed in a ball around `x₀`.  This is the localized analogue of
`seeleyTerm_norm_bound`: the only place where the hypothesis on `R` is used is at the point
`(p.1, -(b j) * p.2)`, whose first coordinate is that of `p` itself. -/
theorem seeleyTerm_norm_bound_local {a b : ℕ → ℝ} (hb : ∀ j : ℕ, 0 < b j)
    {R : X × ℝ → E}
    (hRsmooth : ∀ z : X × ℝ, 0 < z.2 → ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) R z)
    {N : ℕ} {C : ℝ} (hC : 0 ≤ C) (x0 : X) {r : ℝ}
    (hR : ∀ x σ, ‖x - x0‖ < r → 0 < σ → σ < 1 → ∀ k ≤ N,
      ‖iteratedFDeriv ℝ k R (x, σ)‖ ≤ C * σ ^ (N + 1 - k))
    {K : ℕ → ℝ} (hK : ∀ i t, |iteratedDeriv i seeleyRho t| ≤ K i)
    {j : ℕ} {k : ℕ} (hk : k ≤ N) {p : X × ℝ} (hp : p.2 < 0) (hp0 : ‖p.1 - x0‖ < r) :
    ‖iteratedFDeriv ℝ k (seeleyTerm a b R j) p‖
      ≤ seeleyWeight a b N j
        * (C * ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * K i)
        * |p.2| ^ (N + 1 - k) := by
  have hbj : 0 < b j := hb j
  have hK0 : ∀ i, 0 ≤ K i := fun i => (abs_nonneg _).trans (hK i 0)
  have hinf : ∀ k : ℕ, (↑k : ℕ∞ω) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) :=
    fun k => WithTop.coe_le_coe.mpr le_top
  have hUopen : IsOpen {q : X × ℝ | q.2 < 0} := isOpen_lt continuous_snd continuous_const
  have hVopen : IsOpen {z : X × ℝ | 0 < z.2} := isOpen_lt continuous_const continuous_snd
  have hpU : p ∈ {q : X × ℝ | q.2 < 0} := hp
  have hc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun q : X × ℝ => seeleyRho (b j * q.2)) := by
    have h : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (seeleyRho ∘ (b j • ContinuousLinearMap.snd ℝ X ℝ)) :=
      seeleyRho_contDiff.comp ((b j • ContinuousLinearMap.snd ℝ X ℝ).contDiff)
    convert h using 1
    ext q
    simp [Function.comp_def]
  have hRm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) R {z : X × ℝ | 0 < z.2} :=
    fun z hz => (hRsmooth z hz).contDiffWithinAt
  have hmap : Set.MapsTo (seeleyL (X := X) (b j)) {q : X × ℝ | q.2 < 0}
      {z : X × ℝ | 0 < z.2} := by
    intro q hq
    simp only [Set.mem_setOf_eq] at hq ⊢
    rw [seeleyL_snd]
    nlinarith
  have hRj : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : X × ℝ => R (seeleyL (X := X) (b j) q)) {q : X × ℝ | q.2 < 0} :=
    hRm.comp (seeleyL (X := X) (b j)).contDiff.contDiffOn hmap
  have hsmul := norm_iteratedFDerivWithin_smul_le (𝕜 := ℝ) (𝕜' := ℝ)
    (f := fun q : X × ℝ => seeleyRho (b j * q.2))
    (g := fun q : X × ℝ => R (seeleyL (X := X) (b j) q))
    (s := {q : X × ℝ | q.2 < 0}) (N := (k : ℕ∞ω))
    ((contDiff_infty.mp hc) k).contDiffOn ((contDiffOn_infty.mp hRj) k)
    hUopen.uniqueDiffOn hpU (n := k) le_rfl
  have hsummand : ∀ i ∈ Finset.range (k + 1),
      (k.choose i : ℝ)
          * ‖iteratedFDerivWithin ℝ i (fun q : X × ℝ => seeleyRho (b j * q.2))
              {q : X × ℝ | q.2 < 0} p‖
          * ‖iteratedFDerivWithin ℝ (k - i)
              (fun q : X × ℝ => R (seeleyL (X := X) (b j) q)) {q : X × ℝ | q.2 < 0} p‖
      ≤ ((k.choose i : ℝ) * K i)
        * (C * (1 + b j) ^ (2 * N + 1) * |p.2| ^ (N + 1 - k)) := by
    intro i hi
    have hik : i ≤ k := by
      simp only [Finset.mem_range] at hi
      omega
    rw [(iteratedFDerivWithin_of_isOpen i hUopen) hpU,
      (iteratedFDerivWithin_of_isOpen (k - i) hUopen) hpU]
    by_cases hσ : -b j * p.2 < 1
    · have hσpos : 0 < -b j * p.2 := by nlinarith
      have h1 : ‖iteratedFDeriv ℝ i (fun q : X × ℝ => seeleyRho (b j * q.2)) p‖
          ≤ (b j) ^ i * K i := norm_iteratedFDeriv_seeleyRho_comp_le hbj hK i p
      have h2 : ‖iteratedFDeriv ℝ (k - i)
            (fun q : X × ℝ => R (seeleyL (X := X) (b j) q)) p‖
          ≤ C * (-b j * p.2) ^ (N + 1 - (k - i)) * (1 + b j) ^ (k - i) := by
        have hx' : seeleyL (X := X) (b j) p ∈ {z : X × ℝ | 0 < z.2} := by
          simp only [Set.mem_setOf_eq]
          rw [seeleyL_snd]
          exact hσpos
        refine (norm_iteratedFDeriv_comp_clm_le (seeleyL (X := X) (b j)) hVopen hRm hx'
          (k - i)).trans ?_
        have hstep : ‖iteratedFDeriv ℝ (k - i) R (seeleyL (X := X) (b j) p)‖
            ≤ C * (-b j * p.2) ^ (N + 1 - (k - i)) := by
          rw [seeleyL_apply]
          exact hR p.1 (-b j * p.2) hp0 hσpos hσ (k - i) (by omega)
        calc ‖iteratedFDeriv ℝ (k - i) R (seeleyL (X := X) (b j) p)‖
              * ‖seeleyL (X := X) (b j)‖ ^ (k - i)
            ≤ (C * (-b j * p.2) ^ (N + 1 - (k - i))) * (1 + b j) ^ (k - i) := by
              apply mul_le_mul hstep (pow_le_pow_left₀ (norm_nonneg _) (norm_seeleyL_le _ hbj) _)
              · positivity
              · positivity
          _ = C * (-b j * p.2) ^ (N + 1 - (k - i)) * (1 + b j) ^ (k - i) := by ring
      have hfac : (0:ℝ) ≤ (k.choose i : ℝ) * K i * C :=
        mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hK0 i)) hC
      calc (k.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun q : X × ℝ => seeleyRho (b j * q.2)) p‖
              * ‖iteratedFDeriv ℝ (k - i) (fun q : X × ℝ => R (seeleyL (X := X) (b j) q)) p‖
          ≤ (k.choose i : ℝ) * ((b j) ^ i * K i)
              * (C * (-b j * p.2) ^ (N + 1 - (k - i)) * (1 + b j) ^ (k - i)) := by
              apply mul_le_mul
              · exact mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _)
              · exact h2
              · exact norm_nonneg _
              · exact mul_nonneg (Nat.cast_nonneg _)
                  (mul_nonneg (pow_nonneg hbj.le _) (hK0 i))
        _ ≤ ((k.choose i : ℝ) * K i)
              * (C * (1 + b j) ^ (2 * N + 1) * |p.2| ^ (N + 1 - k)) := by
              have hpw := seeley_pow_le hbj hp hσ hik hk
              calc (k.choose i : ℝ) * ((b j) ^ i * K i)
                    * (C * (-b j * p.2) ^ (N + 1 - (k - i)) * (1 + b j) ^ (k - i))
                  = ((k.choose i : ℝ) * K i * C)
                      * (b j ^ i * (-b j * p.2) ^ (N + 1 - (k - i))
                          * (1 + b j) ^ (k - i)) := by ring
                _ ≤ ((k.choose i : ℝ) * K i * C)
                      * ((1 + b j) ^ (2 * N + 1) * |p.2| ^ (N + 1 - k)) :=
                    mul_le_mul_of_nonneg_left hpw hfac
                _ = ((k.choose i : ℝ) * K i)
                      * (C * (1 + b j) ^ (2 * N + 1) * |p.2| ^ (N + 1 - k)) := by ring
    · have hle : b j * p.2 ≤ -1 := by linarith [not_lt.mp hσ]
      have hzero : ‖iteratedFDeriv ℝ i (fun q : X × ℝ => seeleyRho (b j * q.2)) p‖ = 0 := by
        rw [iteratedFDeriv_seeleyRho_comp_eq_zero i hle, norm_zero]
      rw [hzero, mul_zero, zero_mul]
      exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hK0 i))
        (mul_nonneg (mul_nonneg hC (pow_nonneg (by linarith [hbj]) _))
          (pow_nonneg (abs_nonneg _) _))
  have hmain : ‖iteratedFDerivWithin ℝ k
        (fun q : X × ℝ => seeleyRho (b j * q.2) • R (seeleyL (X := X) (b j) q))
        {q : X × ℝ | q.2 < 0} p‖
      ≤ (∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * K i)
        * (C * (1 + b j) ^ (2 * N + 1) * |p.2| ^ (N + 1 - k)) := by
    refine hsmul.trans ?_
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum hsummand
  have hprodOn : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : X × ℝ => seeleyRho (b j * q.2) • R (seeleyL (X := X) (b j) q))
      {q : X × ℝ | q.2 < 0} := hc.contDiffOn.smul hRj
  have hprodAt : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : X × ℝ => seeleyRho (b j * q.2) • R (seeleyL (X := X) (b j) q)) p :=
    hprodOn.contDiffAt (hUopen.mem_nhds hpU)
  have hterm : seeleyTerm a b R j
      = a j • (fun q : X × ℝ => seeleyRho (b j * q.2) • R (seeleyL (X := X) (b j) q)) := by
    funext q
    show a j • (seeleyRho (b j * q.2) • R (q.1, -(b j * q.2)))
      = a j • (seeleyRho (b j * q.2) • R (seeleyL (X := X) (b j) q))
    rw [seeleyL_apply, ← neg_mul]
  have hnorm : ‖iteratedFDeriv ℝ k (seeleyTerm a b R j) p‖
      = |a j| * ‖iteratedFDeriv ℝ k
          (fun q : X × ℝ => seeleyRho (b j * q.2) • R (seeleyL (X := X) (b j) q)) p‖ := by
    rw [hterm, iteratedFDeriv_const_smul_apply (hprodAt.of_le (hinf k)), norm_smul,
      Real.norm_eq_abs]
  rw [hnorm, ← (iteratedFDerivWithin_of_isOpen k hUopen) hpU]
  calc |a j| * ‖iteratedFDerivWithin ℝ k
          (fun q : X × ℝ => seeleyRho (b j * q.2) • R (seeleyL (X := X) (b j) q))
          {q : X × ℝ | q.2 < 0} p‖
      ≤ |a j| * ((∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * K i)
            * (C * (1 + b j) ^ (2 * N + 1) * |p.2| ^ (N + 1 - k))) :=
        mul_le_mul_of_nonneg_left hmain (abs_nonneg _)
    _ = seeleyWeight a b N j * (C * ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * K i)
          * |p.2| ^ (N + 1 - k) := by
        unfold seeleyWeight
        ring

/-- Localized form of `seeleySum_bounds`: the jet bounds for `R` are only needed in a ball around `x₀`, which is all the (local) proof uses: every summand `a_j • (ρ (b_j s) • R (x, -b_j s))` is evaluated at the same first coordinate `x` as the conclusion. -/
theorem seeleySum_bounds_local {X E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {a b : ℕ → ℝ}
    (hb : ∀ j : ℕ, 0 < b j) (hbtend : Filter.Tendsto b Filter.atTop Filter.atTop)
    (hsum : ∀ q : ℕ, Summable (fun j : ℕ => |a j| * (b j) ^ q))
    {R : X × ℝ → E} (hRsmooth : ∀ z : X × ℝ, 0 < z.2 → ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) R z)
    {N : ℕ} {C : ℝ} (hC : 0 ≤ C) (x₀ : X) {r : ℝ} (hr : 0 < r)
    (hR : ∀ x σ, ‖x - x₀‖ < r → 0 < σ → σ < 1 → ∀ k ≤ N,
      ‖iteratedFDeriv ℝ k R (x, σ)‖ ≤ C * σ ^ (N + 1 - k)) :
    ∃ C' r' : ℝ, 0 < r' ∧ r' ≤ 1 ∧ r' ≤ r ∧ ∀ x s, ‖x - x₀‖ < r' → s < 0 → -r' < s → ∀ k ≤ N,
      ‖iteratedFDeriv ℝ k (Work.Drive.seeleySum a b R) (x, s)‖ ≤ C' * |s| ^ (N + 1 - k) := by
  obtain ⟨K, hK0, hKb⟩ := exists_iteratedDeriv_seeleyRho_bound
  set Λ : ℝ := ∑ i ∈ Finset.range (N + 1), (N.choose i : ℝ) * K i with hΛ
  have hΛnn : 0 ≤ Λ := by
    rw [hΛ]
    exact Finset.sum_nonneg fun i _ => mul_nonneg (Nat.cast_nonneg _) (hK0 i)
  have hWsum : Summable (fun j : ℕ => seeleyWeight a b N j) := summable_seeleyWeight hsum hb N
  refine ⟨(∑' j, seeleyWeight a b N j) * (C * Λ), min 1 r, lt_min one_pos hr,
    min_le_left _ _, min_le_right _ _, ?_⟩
  intro x s hx hs0 _ k hk
  have hxr : ‖x - x₀‖ < r := lt_of_lt_of_le hx (min_le_right _ _)
  obtain ⟨F, hF⟩ := exists_finset_eventually_seeleyRho_eq_zero hb hbtend hs0
  have hev : ∀ᶠ q in 𝓝 (x, s), seeleySum a b R q = ∑ j ∈ F, seeleyTerm a b R j q := by
    filter_upwards [(continuous_snd.tendsto (x, s)).eventually hF] with q hq
    change (∑' j, seeleyTerm a b R j q) = ∑ j ∈ F, seeleyTerm a b R j q
    rw [tsum_eq_sum (s := F)]
    intro j hj
    rw [seeleyTerm_apply, hq j hj, zero_smul, smul_zero]
  have heq : iteratedFDeriv ℝ k (seeleySum a b R) (x, s)
      = ∑ j ∈ F, iteratedFDeriv ℝ k (seeleyTerm a b R j) (x, s) := by
    rw [(Filter.EventuallyEq.iteratedFDeriv ℝ hev k).eq_of_nhds]
    exact iteratedFDeriv_fun_sum_apply
      (fun j _ => (contDiffAt_seeleyTerm hb hRsmooth j (p := (x, s)) hs0).of_le
        (show (↑k : ℕ∞ω) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) from WithTop.coe_le_coe.mpr le_top))
  rw [heq]
  have hbound : ∀ j ∈ F, ‖iteratedFDeriv ℝ k (seeleyTerm a b R j) (x, s)‖
      ≤ seeleyWeight a b N j * (C * Λ) * |s| ^ (N + 1 - k) := by
    intro j _
    have h1 := seeleyTerm_norm_bound_local (X := X) (E := E) (a := a) (b := b) hb hRsmooth hC x₀ hR
      hKb hk (p := (x, s)) hs0 hxr (j := j)
    have h2 : (∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * K i) ≤ Λ := by
      rw [hΛ]; exact seeley_choose_sum_mono hK0 hk
    have hw : 0 ≤ seeleyWeight a b N j :=
      mul_nonneg (abs_nonneg _) (pow_nonneg (by linarith [hb j]) _)
    have hz : 0 ≤ |s| ^ (N + 1 - k) := pow_nonneg (abs_nonneg _) _
    have h3 : seeleyWeight a b N j
          * (C * ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * K i)
        ≤ seeleyWeight a b N j * (C * Λ) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 hC) hw
    exact h1.trans (mul_le_mul_of_nonneg_right h3 hz)
  calc ‖∑ j ∈ F, iteratedFDeriv ℝ k (seeleyTerm a b R j) (x, s)‖
      ≤ ∑ j ∈ F, ‖iteratedFDeriv ℝ k (seeleyTerm a b R j) (x, s)‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ F, seeleyWeight a b N j * (C * Λ) * |s| ^ (N + 1 - k) := Finset.sum_le_sum hbound
    _ = (∑ j ∈ F, seeleyWeight a b N j) * (C * Λ) * |s| ^ (N + 1 - k) := by
          rw [Finset.sum_mul, Finset.sum_mul]
    _ ≤ (∑' j, seeleyWeight a b N j) * (C * Λ) * |s| ^ (N + 1 - k) := by
          apply mul_le_mul_of_nonneg_right _ (pow_nonneg (abs_nonneg _) _)
          apply mul_le_mul_of_nonneg_right _ (mul_nonneg hC hΛnn)
          exact Summable.sum_le_tsum F (fun i _ => mul_nonneg (abs_nonneg _)
            (pow_nonneg (by linarith [hb i]) _)) hWsum

end Work.Drive
