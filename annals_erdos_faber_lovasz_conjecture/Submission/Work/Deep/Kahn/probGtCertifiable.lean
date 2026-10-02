import Submission.Work.ConeSwitch.MathlibNoHG
import Submission.Work.Deep.Conc.BruhnJoos.reed_adapter
import Submission.Work.Deep.Conc.BruhnJoos.talagrand_certified

/-!
# `Work.Deep.Kahn.probGtCertifiable`

A Talagrand-type tail bound for a certifiable, `1`-Lipschitz function `X` on a uniform
product space, in the form required by the Kahn subproject: under the mean/variance
hypotheses `E X ≤ θ - ηΛ` and `2 Var X + 2 ≤ (ηΛ)²/4`, the certificate hypothesis at levels
`≥ 1`, and the side condition `D^{1/4} + log 2 ≤ (ηΛ)²/(32θ)`, one gets

  `P(X > θ) ≤ exp(-D^{1/4})`.

The proof combines three ingredients already in the workspace:

* one-sided Chebyshev (`Work.Deep.Conc.prob_le_expect_div`) turns `E X ≤ θ - ηΛ` and
  `Var X ≤ (ηΛ)²/8` into `P(X ≤ θ - ηΛ/2) ≥ 1/2`;
* the certificate hypothesis and `1`-Lipschitzness show that every point of `{θ ≤ X}`
  disagrees with every point of `{X ≤ θ - ηΛ/2}` in at least `ηΛ/2` coordinates of a
  certificate of size `≤ 2θ`
  (`Work.Deep.Reed.Prob.abs_X_sub_le_of_agree_outside`);
* the certified two-set form of Talagrand's convex distance inequality
  (`Work.Deep.Conc.BruhnJoos.talagrand_certified`) then yields
  `P(X ≥ θ) ≤ 2 exp(-(ηΛ)²/(32θ))`.
-/

set_option autoImplicit false

namespace Work.Deep.Kahn

open Work.Deep.Conc

/-- **One-sided Chebyshev.**  If `E Y + τ ≤ a` with `τ > 0`, then `P(Y > a) ≤ Var(Y)/τ²`. -/
private lemma prob_gt_le_var {Ω : Type*} [Fintype Ω] (Y : Ω → ℝ) {a τ : ℝ} (hτ : 0 < τ)
    (h : Work.Deep.Conc.expect Y + τ ≤ a) :
    Work.Deep.Conc.prob {ω | a < Y ω}
      ≤ Work.Deep.Conc.expect (fun ω => (Y ω - Work.Deep.Conc.expect Y) ^ 2) / τ ^ 2 := by
  refine le_trans (Work.Deep.Conc.prob_mono ?_)
    (Work.Deep.Conc.prob_le_expect_div (f := fun ω => (Y ω - Work.Deep.Conc.expect Y) ^ 2)
      (fun ω => sq_nonneg _) (by positivity))
  intro ω hω
  have hω' : a < Y ω := hω
  have h1 : τ < Y ω - Work.Deep.Conc.expect Y := by linarith
  have hsq : τ ^ 2 ≤ (Y ω - Work.Deep.Conc.expect Y) ^ 2 := by
    have := mul_self_le_mul_self hτ.le h1.le
    simpa [pow_two] using this
  exact hsq

/-- **Certificate to disagreement.**  Let `X` be `1`-Lipschitz on the product space and let
`S` be a certificate that `X ≥ s` at `y`.  Then every `z` with `X z ≤ a` disagrees with `y`
on at least `s - a` coordinates of `S`. -/
private lemma cert_disagreement {ι : Type*} [Fintype ι] [DecidableEq ι] {π : ι → Type*}
    [∀ i, Fintype (π i)] [∀ i, DecidableEq (π i)] (X : (∀ i, π i) → ℝ)
    (hlip : ∀ (i : ι) (f : ∀ i, π i) (x : π i), |X (Function.update f i x) - X f| ≤ 1)
    {y z : ∀ i, π i} {s a : ℝ} (hza : X z ≤ a)
    {S : Finset ι} (hcert : ∀ g : ∀ i, π i, (∀ i ∈ S, g i = y i) → s ≤ X g) :
    s - a ≤ ∑ i ∈ S, (if y i ≠ z i then (1 : ℝ) else 0) := by
  classical
  set T : Finset ι := S.filter (fun i => y i ≠ z i) with hT
  set g : ∀ i, π i := fun i => if i ∈ T then y i else z i with hg
  have hagree : ∀ i ∈ S, g i = y i := by
    intro i hi
    by_cases hiT : i ∈ T
    · simp only [hg, hiT, if_true]
    · have hyz : y i = z i := by
        by_contra hne
        exact hiT (Finset.mem_filter.mpr ⟨hi, hne⟩)
      simp only [hg, hiT, if_false]
      exact hyz.symm
  have hXg : s ≤ X g := hcert g hagree
  have hout : ∀ i, i ∉ T → g i = z i := by
    intro i hi
    simp only [hg, hi, if_false]
  have hlipT : |X g - X z| ≤ 1 * (T.card : ℝ) :=
    Work.Deep.Reed.Prob.abs_X_sub_le_of_agree_outside X hlip (f := z) (g := g) (T := T) hout
  have hcardT : (T.card : ℝ) = ∑ i ∈ S, (if y i ≠ z i then (1 : ℝ) else 0) := by
    have h1 : (T.card : ℝ) = ∑ _i ∈ T, (1 : ℝ) := by
      rw [Finset.card_eq_sum_ones, Nat.cast_sum]
      exact Finset.sum_congr rfl (fun i _ => Nat.cast_one)
    rw [h1, hT, Finset.sum_filter]
  have h2 : s - a ≤ (T.card : ℝ) := by
    have h3 : X g - X z ≤ |X g - X z| := le_abs_self _
    linarith
  rw [← hcardT]
  exact h2

theorem probGtCertifiable {ι : Type*} [Fintype ι] [DecidableEq ι]
    {π : ι → Type*} [∀ i, Fintype (π i)] (hne : ∀ i, Nonempty (π i))
    (X : (∀ i, π i) → ℝ) {θ η Λ D : ℝ}
    (hη : 0 < η) (hΛ0 : 0 ≤ Λ) (hθ1 : 1 ≤ θ)
    (hmean : Work.Deep.Conc.expect X ≤ θ - η * Λ)
    (hvar : 2 * Work.Deep.Conc.expect (fun f => (X f - Work.Deep.Conc.expect X) ^ 2) + 2
      ≤ (η * Λ) ^ 2 / 4)
    (hlip : ∀ (i : ι) (f : ∀ i, π i) (x : π i), |X (Function.update f i x) - X f| ≤ 1)
    (hcert : ∀ (f : ∀ i, π i) (w : ℝ), 1 ≤ w → w ≤ X f →
      ∃ S : Finset ι, (S.card : ℝ) ≤ 2 * w ∧
        ∀ g : ∀ i, π i, (∀ i ∈ S, g i = f i) → w ≤ X g)
    (hbig : D ^ ((1:ℝ)/4) + Real.log 2 ≤ (η * Λ) ^ 2 / (32 * θ)) :
    Work.Deep.Conc.prob {f : ∀ i, π i | θ < X f} ≤ Real.exp (-(D ^ ((1:ℝ)/4))) := by
  classical
  haveI : Nonempty (∀ i, π i) := ⟨fun i => Classical.choice (hne i)⟩
  set t : ℝ := η * Λ with htdef
  have ht_nonneg : 0 ≤ t := by rw [htdef]; exact mul_nonneg hη.le hΛ0
  have hVar_nonneg :
      0 ≤ Work.Deep.Conc.expect (fun f : ∀ i, π i => (X f - Work.Deep.Conc.expect X) ^ 2) :=
    Work.Deep.Conc.expect_nonneg (fun f => sq_nonneg _)
  have ht_sq : 8 ≤ t ^ 2 := by nlinarith [hvar, hVar_nonneg]
  have ht_pos : 0 < t := by
    rcases eq_or_lt_of_le ht_nonneg with h0 | hpos
    · rw [← h0] at ht_sq; norm_num at ht_sq
    · exact hpos
  have hVar_le :
      Work.Deep.Conc.expect (fun f : ∀ i, π i => (X f - Work.Deep.Conc.expect X) ^ 2)
        ≤ t ^ 2 / 8 := by
    nlinarith [hvar, hVar_nonneg]
  set A : Set (∀ i, π i) := {f | X f ≤ θ - t / 2} with hAdef
  set B : Set (∀ i, π i) := {f | θ ≤ X f} with hBdef
  -- Chebyshev: at least half of the mass lies in `A`
  have hcheb :=
    prob_gt_le_var X (a := θ - t / 2) (τ := t / 2) (by linarith) (by linarith [hmean])
  have hdiv :
      Work.Deep.Conc.expect (fun f : ∀ i, π i => (X f - Work.Deep.Conc.expect X) ^ 2)
          / (t / 2) ^ 2 ≤ 1 / 2 := by
    rw [div_le_iff₀ (by positivity : (0:ℝ) < (t / 2) ^ 2)]
    nlinarith [hVar_le, ht_sq]
  have hprobAc_le : Work.Deep.Conc.prob {f : ∀ i, π i | θ - t / 2 < X f} ≤ 1 / 2 :=
    le_trans hcheb hdiv
  have hcompl : Aᶜ = {f : ∀ i, π i | θ - t / 2 < X f} := by
    ext f; simp only [hAdef, Set.mem_compl_iff, Set.mem_ofPred_eq, not_le]
  have hprobA : 1 / 2 ≤ Work.Deep.Conc.prob A := by
    have h := Work.Deep.Conc.prob_compl A
    rw [hcompl] at h
    linarith
  -- the certificates give many disagreements
  have hcert2 : ∀ ω ∈ B, ∃ I : Finset ι, I.card ≤ ⌊2 * θ⌋₊ ∧
      ∀ ω' ∈ A, t / 2 ≤ ∑ i ∈ I, (if ω i ≠ ω' i then (1 : ℝ) else 0) := by
    intro ω hω
    have hωθ : θ ≤ X ω := by
      simp only [hBdef, Set.mem_ofPred_eq] at hω; exact hω
    obtain ⟨S, hScard, hScert⟩ := hcert ω θ hθ1 hωθ
    refine ⟨S, Nat.le_floor hScard, ?_⟩
    intro ω' hω'
    have hω'a : X ω' ≤ θ - t / 2 := by
      simp only [hAdef, Set.mem_ofPred_eq] at hω'; exact hω'
    have h := cert_disagreement (X := X) (hlip := hlip) (y := ω) (z := ω') (s := θ)
      (a := θ - t / 2) hω'a hScert
    linarith
  have hs1 : 1 ≤ ⌊2 * θ⌋₊ := by
    apply Nat.le_floor
    push_cast
    linarith
  have htwo := Work.Deep.Conc.BruhnJoos.talagrand_certified hne A B (t / 2) (by linarith)
    ⌊2 * θ⌋₊ hs1 hcert2
  have hexp : Real.exp (-(t / 2) ^ 2 / (4 * (⌊2 * θ⌋₊ : ℝ)))
      ≤ Real.exp (-(t ^ 2 / (32 * θ))) := by
    apply Real.exp_le_exp.mpr
    have hθ_pos : 0 < θ := by linarith
    have hs_pos : (0:ℝ) < (⌊2 * θ⌋₊ : ℝ) := by exact_mod_cast hs1
    have hfloor : ((⌊2 * θ⌋₊ : ℕ) : ℝ) ≤ 2 * θ := Nat.floor_le (by linarith)
    have hkey : t ^ 2 / (32 * θ) ≤ (t / 2) ^ 2 / (4 * (⌊2 * θ⌋₊ : ℝ)) := by
      rw [div_le_div_iff₀ (by linarith : (0:ℝ) < 32 * θ)
        (by positivity : (0:ℝ) < 4 * (⌊2 * θ⌋₊ : ℝ))]
      have h := mul_le_mul_of_nonneg_left hfloor (sq_nonneg t)
      nlinarith [h]
    simpa only [neg_div] using neg_le_neg hkey
  have hprobB : Work.Deep.Conc.prob B ≤ 2 * Real.exp (-(t ^ 2 / (32 * θ))) := by
    have h1 : Work.Deep.Conc.prob A * Work.Deep.Conc.prob B ≤ Real.exp (-(t ^ 2 / (32 * θ))) :=
      le_trans htwo hexp
    have h2 : Work.Deep.Conc.prob B ≤ 2 * (Work.Deep.Conc.prob A * Work.Deep.Conc.prob B) := by
      have h := mul_le_mul_of_nonneg_right hprobA (Work.Deep.Conc.prob_nonneg B)
      linarith
    have h3 : 2 * (Work.Deep.Conc.prob A * Work.Deep.Conc.prob B)
        ≤ 2 * Real.exp (-(t ^ 2 / (32 * θ))) :=
      mul_le_mul_of_nonneg_left h1 (by norm_num)
    linarith [h2, h3]
  have hlog : 2 * Real.exp (-(t ^ 2 / (32 * θ)))
      = Real.exp (Real.log 2 - t ^ 2 / (32 * θ)) := by
    rw [Real.exp_sub, Real.exp_log (by norm_num : (0:ℝ) < 2), Real.exp_neg]
    ring
  have hlast : Real.exp (Real.log 2 - t ^ 2 / (32 * θ)) ≤ Real.exp (-(D ^ ((1:ℝ)/4))) :=
    Real.exp_le_exp.mpr (by linarith [hbig])
  calc Work.Deep.Conc.prob {f : ∀ i, π i | θ < X f}
      ≤ Work.Deep.Conc.prob B := by
        refine Work.Deep.Conc.prob_mono (fun f hf => ?_)
        simp only [hBdef, Set.mem_ofPred_eq]
        exact le_of_lt hf
    _ ≤ 2 * Real.exp (-(t ^ 2 / (32 * θ))) := hprobB
    _ = Real.exp (Real.log 2 - t ^ 2 / (32 * θ)) := hlog
    _ ≤ Real.exp (-(D ^ ((1:ℝ)/4))) := hlast

end Work.Deep.Kahn
