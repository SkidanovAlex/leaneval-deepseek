import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Topology.UniformSpace.Uniformizable

namespace Commons.Analysis.TensorApprox

open scoped BigOperators
open Finset

private noncomputable def cut (s : ℝ) (x : ℕ → ℝ) (n : ℕ) (u : ℝ) : ℝ :=
  Real.smoothTransition ((u - x n) / s) - Real.smoothTransition ((u - x (n + 1)) / s)

private lemma cut_contDiff (s : ℝ) (x : ℕ → ℝ) (n : ℕ) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (cut s x n) := by
  unfold cut
  fun_prop

private lemma cut_nonneg {s : ℝ} (hs : 0 < s) {x : ℕ → ℝ} {n : ℕ} (hx : x n ≤ x (n+1)) (u : ℝ) :
    0 ≤ cut s x n u := by
  unfold cut
  have h : (u - x (n+1))/s ≤ (u - x n)/s := by
    gcongr
  have hm := Real.smoothTransition.monotone h
  have h0 := Real.smoothTransition.nonneg ((u - x (n+1))/s)
  linarith

private lemma cut_eq_zero_of_le {s : ℝ} (hs : 0 < s) {x : ℕ → ℝ} {n : ℕ} (hx : x n ≤ x (n+1))
    {u : ℝ} (h : u ≤ x n) : cut s x n u = 0 := by
  unfold cut
  have h1 : (u - x n)/s ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) (le_of_lt hs)
  have h2 : (u - x (n+1))/s ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) (le_of_lt hs)
  rw [Real.smoothTransition.zero_of_nonpos h1, Real.smoothTransition.zero_of_nonpos h2, sub_zero]

private lemma cut_eq_zero_of_ge {s : ℝ} (hs : 0 < s) {x : ℕ → ℝ} {n : ℕ} (hx : x n ≤ x (n+1))
    {u : ℝ} (h : x (n+1) + s ≤ u) : cut s x n u = 0 := by
  unfold cut
  have h1 : 1 ≤ (u - x (n+1))/s := by rw [le_div_iff₀ hs]; linarith
  have h2 : 1 ≤ (u - x n)/s := by rw [le_div_iff₀ hs]; linarith
  rw [Real.smoothTransition.one_of_one_le h1, Real.smoothTransition.one_of_one_le h2, sub_self]

private lemma cut_ne_zero_bounds {s : ℝ} (hs : 0 < s) {x : ℕ → ℝ} {n : ℕ} (hx : x n ≤ x (n+1))
    {u : ℝ} (h : cut s x n u ≠ 0) : x n < u ∧ u < x (n+1) + s := by
  constructor
  · by_contra hle
    push Not at hle
    exact h (cut_eq_zero_of_le hs hx hle)
  · by_contra hge
    push Not at hge
    exact h (cut_eq_zero_of_ge hs hx hge)

private lemma cut_sum_range (s : ℝ) (x : ℕ → ℝ) (u : ℝ) (N : ℕ) :
    ∑ n ∈ range N, cut s x n u =
      Real.smoothTransition ((u - x 0)/s) - Real.smoothTransition ((u - x N)/s) := by
  have := Finset.sum_range_sub' (fun n => Real.smoothTransition ((u - x n)/s)) N
  simpa [cut] using this

private lemma cut_sum_range_eq_one {s : ℝ} (hs : 0 < s) {x : ℕ → ℝ} {u : ℝ} {N : ℕ}
    (h0 : x 0 + s ≤ u) (hN : u ≤ x N) : ∑ n ∈ range N, cut s x n u = 1 := by
  rw [cut_sum_range]
  have ha : Real.smoothTransition ((u - x 0)/s) = 1 := by
    apply Real.smoothTransition.one_of_one_le
    rw [le_div_iff₀ hs]; linarith
  have hb : Real.smoothTransition ((u - x N)/s) = 0 := by
    apply Real.smoothTransition.zero_of_nonpos
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) (le_of_lt hs)
  rw [ha, hb, sub_zero]

private lemma cut_sum_range_le_one (s : ℝ) (x : ℕ → ℝ) (u : ℝ) (N : ℕ) :
    ∑ n ∈ range N, cut s x n u ≤ 1 := by
  rw [cut_sum_range]
  have h1 := Real.smoothTransition.le_one ((u - x 0)/s)
  have h2 := Real.smoothTransition.nonneg ((u - x N)/s)
  linarith

private lemma cut_hasCompactSupport {s : ℝ} (hs : 0 < s) {x : ℕ → ℝ} {n : ℕ}
    (hx : x n ≤ x (n+1)) : HasCompactSupport (cut s x n) := by
  apply HasCompactSupport.of_support_subset_isCompact (K := Set.Icc (x n) (x (n+1) + s))
    isCompact_Icc
  intro u hu
  rw [Function.mem_support] at hu
  rw [Set.mem_Icc]
  exact ⟨le_of_lt (cut_ne_zero_bounds hs hx hu).1, le_of_lt (cut_ne_zero_bounds hs hx hu).2⟩

/-- The set of multi-indices whose associated tensor box is admissible, i.e. whose side lengths
add up to at most `R + 12 * k * η`. -/
private def goodIdx (k N : ℕ) (x : ℕ → ℝ) (s R η : ℝ) (j : Fin k → Fin N) : Prop :=
  ∑ i, max (x ((j i : ℕ) + 1) + s) 0 ≤ R + 12 * (k : ℝ) * η

/-- Localised tensor approximation with a nonnegative support bound.  A continuous compactly
supported `g` on `Fin k → ℝ` whose support lies in the orthant and in `{∑ i, t i ≤ R}` is
uniformly approximated by a finite tensor sum `∑ j, c j * ∏ i, h j i (t i)` whose one-variable
components `h j i` are smooth, compactly supported, vanish for `u > β j i` and for `u < -(12*η)`,
with `0 ≤ β j i ≤ R + 12 * k * η` for every `j i` and `∑ i, β j i ≤ R + 12 * k * η`. -/
theorem exists_tensor_localization_orthant {k : ℕ} {g : (Fin k → ℝ) → ℝ} (hg : Continuous g)
    (hcs : HasCompactSupport g) {R : ℝ}
    (hR : ∀ t, g t ≠ 0 → (∀ i, 0 ≤ t i) ∧ ∑ i, t i ≤ R)
    {η ε : ℝ} (hη : 0 < η) (hε : 0 < ε) :
    ∃ (ι : Type) (_ : Fintype ι) (c : ι → ℝ) (β : ι → Fin k → ℝ) (h : ι → Fin k → ℝ → ℝ),
      (∀ j i, ContDiff ℝ (↑(⊤ : ℕ∞)) (h j i)) ∧
      (∀ j i, HasCompactSupport (h j i)) ∧
      (∀ j i u, β j i < u → h j i u = 0) ∧
      (∀ j i u, u < -(12 * η) → h j i u = 0) ∧
      (∀ j i, 0 ≤ β j i) ∧
      (∀ j i, β j i ≤ R + 12 * (k : ℝ) * η) ∧
      (∀ j, ∑ i, β j i ≤ R + 12 * (k : ℝ) * η) ∧
      (∀ t, |g t - ∑ j, c j * ∏ i, h j i (t i)| < ε) := by
  classical
  by_cases htriv : ∀ t, g t = 0
  · refine ⟨Fin 0, inferInstance, fun _ => 0, fun _ => 0, fun _ => 0,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact fun j => Fin.elim0 j
    · exact fun j => Fin.elim0 j
    · exact fun j => Fin.elim0 j
    · exact fun j => Fin.elim0 j
    · exact fun j => Fin.elim0 j
    · exact fun j => Fin.elim0 j
    · exact fun j => Fin.elim0 j
    · intro t
      have h0 : (∑ j : Fin 0, (fun _ : Fin 0 => (0 : ℝ)) j *
          ∏ i : Fin k, ((fun _ : Fin 0 => (0 : Fin k → ℝ → ℝ)) j) i (t i)) = 0 := by simp
      rw [h0, htriv t, sub_zero, abs_zero]
      exact hε
  · push Not at htriv
    obtain ⟨t₀, ht₀⟩ := htriv
    have hR0 : 0 ≤ R := by
      have h2 := (hR t₀ ht₀).2
      have h1 : 0 ≤ ∑ i, t₀ i := Finset.sum_nonneg fun i _ => (hR t₀ ht₀).1 i
      linarith
    have huc : UniformContinuous g :=
      hg.uniformContinuous_of_tendsto_cocompact hcs.is_zero_at_infty
    obtain ⟨δ, hδpos, hδ⟩ := Metric.uniformContinuous_iff.mp huc (ε/2) (by linarith)
    set s : ℝ := min (3*η) (δ/4) with hsdef
    have hspos : 0 < s := lt_min (by linarith) (by linarith)
    have hs3 : s ≤ 3*η := min_le_left _ _
    have hsd : s ≤ δ/4 := min_le_right _ _
    have hs2δ : 2*s < δ := by linarith
    have hslt : s < 12*η := by linarith
    obtain ⟨N, hN⟩ : ∃ N : ℕ, R + 12*η ≤ N*s := by
      obtain ⟨N, hN⟩ := exists_nat_ge ((R + 12*η)/s)
      exact ⟨N, by rw [div_le_iff₀ hspos] at hN; linarith⟩
    set x : ℕ → ℝ := fun n => -12*η + n*s with hxdef
    have hx0 : x 0 = -12*η := by simp [hxdef]
    have hxsucc : ∀ n, x (n+1) = x n + s := by
      intro n; simp only [hxdef]; push_cast; ring
    have hxmono : ∀ n, x n ≤ x (n+1) := fun n => by rw [hxsucc n]; linarith
    have hxN : R ≤ x N := by
      have h : x N = -12*η + N*s := by simp [hxdef]
      nlinarith
    have hxlow : ∀ n, -12*η ≤ x n := by
      intro n
      have h : x n = -12*η + n*s := by simp [hxdef]
      have hn : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
      have hns : 0 ≤ (n:ℝ) * s := mul_nonneg hn (le_of_lt hspos)
      linarith
    refine ⟨Fin k → Fin N, inferInstance,
      fun j => if goodIdx k N x s R η j then g (fun i => x (j i : ℕ)) else (0 : ℝ),
      fun j i => if goodIdx k N x s R η j then max (x ((j i : ℕ) + 1) + s) 0 else (0 : ℝ),
      fun j i => if goodIdx k N x s R η j then cut s x (j i : ℕ) else (0 : ℝ → ℝ),
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro j i
      simp only []
      split_ifs with hj
      · exact cut_contDiff s x (j i : ℕ)
      · exact contDiff_const
    · intro j i
      simp only []
      split_ifs with hj
      · exact cut_hasCompactSupport hspos (hxmono (j i : ℕ))
      · exact HasCompactSupport.zero
    · intro j i u hu
      simp only [] at hu ⊢
      by_cases hj : goodIdx k N x s R η j
      · simp only [hj, if_true] at hu ⊢
        refine cut_eq_zero_of_ge hspos (hxmono (j i : ℕ)) ?_
        exact le_trans (le_max_left _ _) (le_of_lt hu)
      · simp only [hj, if_false] at hu ⊢
        rfl
    · intro j i u hu
      simp only [] at hu ⊢
      by_cases hj : goodIdx k N x s R η j
      · simp only [hj, if_true] at hu ⊢
        refine cut_eq_zero_of_le hspos (hxmono (j i : ℕ)) ?_
        have h1 := hxlow (j i : ℕ)
        linarith
      · simp only [hj, if_false] at hu ⊢
        rfl
    · intro j i
      simp only []
      split_ifs with hj
      · exact le_max_right _ _
      · norm_num
    · intro j i
      simp only []
      split_ifs with hj
      · have h := Finset.single_le_sum
          (f := fun i' : Fin k => max (x ((j i' : ℕ) + 1) + s) 0)
          (fun i' (_ : i' ∈ Finset.univ) => le_max_right (x ((j i' : ℕ) + 1) + s) 0)
          (Finset.mem_univ i)
        simp only [goodIdx] at hj
        linarith
      · have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
        have : (0 : ℝ) ≤ R + 12 * (k : ℝ) * η := by nlinarith
        linarith
    · intro j
      simp only []
      split_ifs with hj
      · simpa only [goodIdx] using hj
      · have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
        have h1 : (0 : ℝ) ≤ R + 12 * (k : ℝ) * η := by nlinarith
        simpa using h1
    · intro t
      have h1 : (∑ j : Fin k → Fin N,
            (if goodIdx k N x s R η j then g (fun i => x (j i : ℕ)) else 0) *
              ∏ i, (if goodIdx k N x s R η j then cut s x (j i : ℕ) else 0) (t i))
          = ∑ j : Fin k → Fin N,
              (if goodIdx k N x s R η j then ∏ i, cut s x (j i : ℕ) (t i) else 0)
                * g (fun i => x (j i : ℕ)) := by
        refine Finset.sum_congr rfl (fun j _ => ?_)
        by_cases hj : goodIdx k N x s R η j
        · simp only [hj, if_true]
          ring
        · simp only [hj, if_false]
          simp
      rw [h1]
      set w : (Fin k → Fin N) → ℝ := fun j => ∏ i, cut s x (j i : ℕ) (t i) with hw
      set w' : (Fin k → Fin N) → ℝ := fun j => if goodIdx k N x s R η j then w j else 0 with hw'
      have h2 : (∑ j : Fin k → Fin N,
              (if goodIdx k N x s R η j then ∏ i, cut s x (j i : ℕ) (t i) else 0)
                * g (fun i => x (j i : ℕ)))
          = ∑ j : Fin k → Fin N, w' j * g (fun i => x (j i : ℕ)) := by
        refine Finset.sum_congr rfl (fun j _ => ?_)
        simp only [hw', hw]
      rw [h2]
      have hwnn : ∀ j : Fin k → Fin N, 0 ≤ w j := by
        intro j
        rw [hw]
        exact Finset.prod_nonneg (fun i _ => cut_nonneg hspos (hxmono (j i : ℕ)) (t i))
      have hw'nn : ∀ j : Fin k → Fin N, 0 ≤ w' j := by
        intro j
        by_cases hj : goodIdx k N x s R η j
        · rw [hw']; simp only [hj, if_true]; exact hwnn j
        · rw [hw']; simp only [hj, if_false]; norm_num
      have hfac : (∑ j : Fin k → Fin N, w j)
          = ∏ i, ∑ n : Fin N, cut s x (n : ℕ) (t i) := by
        rw [hw]
        rw [← Fintype.piFinset_univ]
        exact Finset.sum_prod_piFinset Finset.univ
          (fun (i : Fin k) (n : Fin N) => cut s x (n : ℕ) (t i))
      have hfac_le : ∑ j : Fin k → Fin N, w j ≤ 1 := by
        rw [hfac]
        refine Finset.prod_le_one₀ (fun i _ => ?_) (fun i _ => ?_)
        · exact Finset.sum_nonneg (fun n _ => cut_nonneg hspos (hxmono (n : ℕ)) (t i))
        · have hrange : (∑ n : Fin N, cut s x (n : ℕ) (t i))
              = ∑ n ∈ range N, cut s x n (t i) :=
            Fin.sum_univ_eq_sum_range (fun n => cut s x n (t i)) N
          rw [hrange]
          exact cut_sum_range_le_one s x (t i) N
      have hsum_le_one : ∑ j : Fin k → Fin N, w' j ≤ 1 := by
        calc ∑ j : Fin k → Fin N, w' j ≤ ∑ j : Fin k → Fin N, w j := by
              refine Finset.sum_le_sum (fun j _ => ?_)
              by_cases hj : goodIdx k N x s R η j
              · simp only [hw', hj, if_true]
                exact le_rfl
              · simp only [hw', hj, if_false]
                exact hwnn j
          _ ≤ 1 := hfac_le
      have hdist_close : ∀ j : Fin k → Fin N,
          (∏ i, cut s x (j i : ℕ) (t i)) ≠ 0 → dist t (fun i => x (j i : ℕ)) < δ := by
        intro j hjnz
        have hne : ∀ i : Fin k, cut s x (j i : ℕ) (t i) ≠ 0 := by
          intro i h0
          exact hjnz (Finset.prod_eq_zero (Finset.mem_univ i) h0)
        have hti : ∀ i : Fin k, dist (t i) (x (j i : ℕ)) ≤ 2*s := by
          intro i
          have h1 : x (j i : ℕ) < t i := (cut_ne_zero_bounds hspos (hxmono (j i : ℕ)) (hne i)).1
          have h2 : t i < x (j i : ℕ) + 2*s := by
            have h2' := (cut_ne_zero_bounds hspos (hxmono (j i : ℕ)) (hne i)).2
            have hxs := hxsucc (j i : ℕ)
            linarith
          have h3 : dist (t i) (x (j i : ℕ)) < 2*s := by
            rw [Real.dist_eq, abs_lt]
            constructor <;> linarith
          exact le_of_lt h3
        have h2 : dist t (fun i => x (j i : ℕ)) ≤ 2*s :=
          (dist_pi_le_iff (by linarith)).2 hti
        linarith
      have hgen : ∀ j : Fin k → Fin N,
          w' j * |g t - g (fun i => x (j i : ℕ))| ≤ (ε/2) * w' j := by
        intro j
        by_cases hj : goodIdx k N x s R η j
        · have hw'j : w' j = w j := by rw [hw']; simp only [hj, if_true]
          rw [hw'j]
          by_cases hw0 : w j = 0
          · rw [hw0]; simp
          · have hclose : |g t - g (fun i => x (j i : ℕ))| ≤ ε/2 := by
              have hh := hδ (hdist_close j (by rwa [hw] at hw0))
              rw [Real.dist_eq] at hh
              exact le_of_lt hh
            calc w j * |g t - g (fun i => x (j i : ℕ))| ≤ w j * (ε/2) :=
                  mul_le_mul_of_nonneg_left hclose (hwnn j)
              _ = (ε/2) * w j := by ring
        · have h0 : w' j = 0 := by rw [hw']; simp only [hj, if_false]
          rw [h0]; simp
      have hb : |∑ j : Fin k → Fin N, w' j * (g t - g (fun i => x (j i : ℕ)))|
          ≤ (ε/2) * ∑ j : Fin k → Fin N, w' j := by
        calc |∑ j : Fin k → Fin N, w' j * (g t - g (fun i => x (j i : ℕ)))|
            ≤ ∑ j : Fin k → Fin N, |w' j * (g t - g (fun i => x (j i : ℕ)))| :=
              Finset.abs_sum_le_sum_abs _ _
          _ = ∑ j : Fin k → Fin N, w' j * |g t - g (fun i => x (j i : ℕ))| := by
              refine Finset.sum_congr rfl (fun j _ => ?_)
              rw [abs_mul, abs_of_nonneg (hw'nn j)]
          _ ≤ ∑ j : Fin k → Fin N, (ε/2) * w' j := Finset.sum_le_sum (fun j _ => hgen j)
          _ = (ε/2) * ∑ j : Fin k → Fin N, w' j := by rw [Finset.mul_sum]
      have hid : g t - ∑ j : Fin k → Fin N, w' j * g (fun i => x (j i : ℕ))
          = (∑ j : Fin k → Fin N, w' j * (g t - g (fun i => x (j i : ℕ))))
            + g t * (1 - ∑ j : Fin k → Fin N, w' j) := by
        have h3 : (∑ j : Fin k → Fin N, w' j * (g t - g (fun i => x (j i : ℕ))))
            = (∑ j : Fin k → Fin N, w' j) * g t
              - ∑ j : Fin k → Fin N, w' j * g (fun i => x (j i : ℕ)) := by
          rw [Finset.sum_mul]
          rw [← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl (fun j _ => ?_)
          ring
        rw [h3]; ring
      have hfinal : |g t - ∑ j : Fin k → Fin N, w' j * g (fun i => x (j i : ℕ))|
          ≤ (ε/2) * ∑ j : Fin k → Fin N, w' j
            + |g t| * |1 - ∑ j : Fin k → Fin N, w' j| := by
        rw [hid]
        refine le_trans (abs_add_le _ _) ?_
        rw [abs_mul]
        exact add_le_add hb le_rfl
      by_cases hgt : g t = 0
      · calc |g t - ∑ j : Fin k → Fin N, w' j * g (fun i => x (j i : ℕ))|
            ≤ (ε/2) * ∑ j : Fin k → Fin N, w' j
              + |g t| * |1 - ∑ j : Fin k → Fin N, w' j| := hfinal
          _ = (ε/2) * ∑ j : Fin k → Fin N, w' j := by rw [hgt]; ring
          _ ≤ (ε/2) * 1 := by nlinarith [hsum_le_one]
          _ < ε := by linarith
      · have hti : ∀ i : Fin k, 0 ≤ t i := (hR t hgt).1
        have hst : ∑ i : Fin k, t i ≤ R := (hR t hgt).2
        have hgood_nz : ∀ j : Fin k → Fin N,
            (∏ i, cut s x (j i : ℕ) (t i)) ≠ 0 → goodIdx k N x s R η j := by
          intro j hjnz
          simp only [goodIdx]
          have hbdd : ∀ i : Fin k, max (x ((j i : ℕ) + 1) + s) 0 ≤ t i + 2*s := by
            intro i
            have hne : cut s x (j i : ℕ) (t i) ≠ 0 :=
              fun h0 => hjnz (Finset.prod_eq_zero (Finset.mem_univ i) h0)
            have h1 := (cut_ne_zero_bounds hspos (hxmono (j i : ℕ)) hne).1
            have hxs := hxsucc (j i : ℕ)
            have h2 : x ((j i : ℕ) + 1) + s ≤ t i + 2*s := by rw [hxs]; linarith
            exact max_le h2 (by linarith [hti i])
          calc ∑ i : Fin k, max (x ((j i : ℕ) + 1) + s) 0 ≤ ∑ i : Fin k, (t i + 2*s) :=
                Finset.sum_le_sum (fun i _ => hbdd i)
            _ = (∑ i : Fin k, t i) + (k : ℝ) * (2*s) := by
                rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
                  Fintype.card_fin, nsmul_eq_mul]
            _ ≤ R + 12 * (k : ℝ) * η := by
                have h1 : (k : ℝ) * (2*s) ≤ (k : ℝ) * (12*η) := by
                  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg k)
                  linarith
                linarith
        have hw'eq : ∀ j : Fin k → Fin N, w' j = w j := by
          intro j
          by_cases hj : goodIdx k N x s R η j
          · rw [hw']; simp only [hj, if_true]
          · have hw0 : w j = 0 := by
              rw [hw]
              by_contra h
              exact hj (hgood_nz j h)
            rw [hw']; simp only [hj, if_false, hw0]
        have hone : ∀ i : Fin k, ∑ n : Fin N, cut s x (n : ℕ) (t i) = 1 := by
          intro i
          have hrange : (∑ n : Fin N, cut s x (n : ℕ) (t i))
              = ∑ n ∈ range N, cut s x n (t i) :=
            Fin.sum_univ_eq_sum_range (fun n => cut s x n (t i)) N
          rw [hrange]
          refine cut_sum_range_eq_one hspos ?_ ?_
          · rw [hx0]; linarith [hti i]
          · calc t i ≤ ∑ i' : Fin k, t i' :=
                  Finset.single_le_sum (fun i' _ => hti i') (Finset.mem_univ i)
              _ ≤ R := hst
              _ ≤ x N := hxN
        have hsum_one : ∑ j : Fin k → Fin N, w' j = 1 := by
          have h4 : ∑ j : Fin k → Fin N, w' j = ∑ j : Fin k → Fin N, w j :=
            Finset.sum_congr rfl (fun j _ => hw'eq j)
          rw [h4, hfac]
          rw [Finset.prod_congr rfl (fun i _ => hone i)]
          simp
        calc |g t - ∑ j : Fin k → Fin N, w' j * g (fun i => x (j i : ℕ))|
            ≤ (ε/2) * ∑ j : Fin k → Fin N, w' j
              + |g t| * |1 - ∑ j : Fin k → Fin N, w' j| := hfinal
          _ = ε/2 := by rw [hsum_one]; ring
          _ < ε := by linarith

end Commons.Analysis.TensorApprox