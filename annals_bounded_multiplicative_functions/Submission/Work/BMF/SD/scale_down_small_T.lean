import Mathlib
import Submission.Work.BMF.Defs
import Submission.Work.BMF.interfaces
import Submission.Work.BMF.polyrel_basic
import Submission.Work.BMF.SD.sd3_defs
import Submission.Work.BMF.SD.tk_bad_weight_sub
import Submission.Work.BMF.SD.good_window_pairs_sub
import Submission.Work.BMF.SD.cell_center
import Submission.Work.BMF.SD.window_helpers

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-! Guidance from the project lead (the requester):

LEAD 09-30: new scale_down decomposition (read _NOTE_BMF_SD_0930_VERDICT.md at the workspace root; your node's route and constants are in its docstring). Narrow the prime window AFTER counting (pigeonhole into sub-windows of ratio 1+ρ), then split on T = X/H at a threshold T₁ depending only on c₀. No new analytic number theory is needed.
Assembly: the single centre-anchored cell {y/a}, via the proved cell_center, after a small correlation-shift estimate. When the siblings land, add imports Submission.Work.BMF.SD.goodPairs_narrow and Submission.Work.BMF.SD.corr_anchor_shift.
-/

namespace Work.BMF.SD

open Classical Polynomial Finset Real Complex
open BoundedMultiplicativeFunctions

set_option maxHeartbeats 4000000

/-! ## Elementary leaves

Two self-contained inputs of the assembly below: the modulus of `eC` is `1` (so every summand of a
`corr` has modulus `≤ 1`), the difference of two sums of a `1`-bounded sequence over two finsets is
controlled by the sizes of the two set-differences, and the symmetric difference of two integer
windows `natIcc x (x+L)`, `natIcc x' (x'+L)` is contained in two half-open intervals each holding at
most `|x - x'| + 1` integers.  These give `corr_anchor_shift_aux`, the anchor shift used in step 4 of
the route, and `goodPairs_narrow_aux`, the pigeonhole of step 3. -/

lemma sdt_norm_eC (t : ℝ) : ‖Work.BMF.eC t‖ = 1 := by
  unfold Work.BMF.eC
  rw [Complex.norm_exp]; simp

/-- The difference of two sums of a `1`-bounded sequence over two finsets is bounded by the sizes of
the two set-differences. -/
lemma sdt_norm_sum_sub_le (A B : Finset ℕ) (g : ℕ → ℂ) (hg : ∀ n, ‖g n‖ ≤ 1) :
    ‖∑ n ∈ A, g n - ∑ n ∈ B, g n‖ ≤ (((A \ B).card : ℝ) + ((B \ A).card : ℝ)) := by
  have hA : A = (A \ B) ∪ (A ∩ B) := by
    ext n; by_cases h : n ∈ B <;> simp [Finset.mem_sdiff, Finset.mem_inter, h]
  have hB : B = (B \ A) ∪ (A ∩ B) := by
    ext n; by_cases h : n ∈ A <;> simp [Finset.mem_sdiff, Finset.mem_inter, h]
  have hd1 : Disjoint (A \ B) (A ∩ B) := by
    rw [Finset.disjoint_left]; intro n hn1 hn2
    exact (Finset.mem_sdiff.mp hn1).2 (Finset.mem_inter.mp hn2).2
  have hd2 : Disjoint (B \ A) (A ∩ B) := by
    rw [Finset.disjoint_left]; intro n hn1 hn2
    exact (Finset.mem_sdiff.mp hn1).2 (Finset.mem_inter.mp hn2).1
  have e1 : ∑ n ∈ A, g n = ∑ n ∈ A \ B, g n + ∑ n ∈ A ∩ B, g n := by
    conv_lhs => rw [hA]
    rw [Finset.sum_union hd1]
  have e2 : ∑ n ∈ B, g n = ∑ n ∈ B \ A, g n + ∑ n ∈ A ∩ B, g n := by
    conv_lhs => rw [hB]
    rw [Finset.sum_union hd2]
  rw [e1, e2]
  have hgoal : (∑ n ∈ A \ B, g n + ∑ n ∈ A ∩ B, g n) - (∑ n ∈ B \ A, g n + ∑ n ∈ A ∩ B, g n)
      = ∑ n ∈ A \ B, g n - ∑ n ∈ B \ A, g n := by ring
  rw [hgoal]
  have h3 : ‖∑ n ∈ A \ B, g n‖ ≤ ((A \ B).card : ℝ) := by
    calc ‖∑ n ∈ A \ B, g n‖ ≤ ∑ n ∈ A \ B, ‖g n‖ := norm_sum_le _ _
      _ ≤ ∑ _n ∈ A \ B, (1:ℝ) := Finset.sum_le_sum (fun n _ => hg n)
      _ = ((A \ B).card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
  have h4 : ‖∑ n ∈ B \ A, g n‖ ≤ ((B \ A).card : ℝ) := by
    calc ‖∑ n ∈ B \ A, g n‖ ≤ ∑ n ∈ B \ A, ‖g n‖ := norm_sum_le _ _
      _ ≤ ∑ _n ∈ B \ A, (1:ℝ) := Finset.sum_le_sum (fun n _ => hg n)
      _ = ((B \ A).card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
  calc ‖∑ n ∈ A \ B, g n - ∑ n ∈ B \ A, g n‖
      ≤ ‖∑ n ∈ A \ B, g n‖ + ‖∑ n ∈ B \ A, g n‖ := norm_sub_le _ _
    _ ≤ _ := by linarith

/-- The symmetric difference of two integer windows `natIcc x (x+L)`, `natIcc x' (x'+L)` (with
`x, x' ≥ 0`, `L ≥ 0`) is contained in the two half-open intervals `[min x x', max x x')` and
`(min x x' + L, max x x' + L]`, each holding at most `|x - x'| + 1` integers. -/
lemma sdt_card_diff_bound (x x' L : ℝ) (hx : 0 ≤ x) (hx' : 0 ≤ x') (hL : 0 ≤ L) :
    (((Work.BMF.natIcc x (x + L) \ Work.BMF.natIcc x' (x' + L)).card : ℝ)
      + ((Work.BMF.natIcc x' (x' + L) \ Work.BMF.natIcc x (x + L)).card : ℝ))
      ≤ 2 * |x - x'| + 2 := by
  set A := Work.BMF.natIcc x (x + L) with hA
  set B := Work.BMF.natIcc x' (x' + L) with hB
  set mn : ℝ := min x x' with hmn
  set Mx : ℝ := max x x' with hMx
  have hmn_le : mn ≤ Mx := min_le_max
  have hmn_x : mn ≤ x := min_le_left _ _
  have hmn_x' : mn ≤ x' := min_le_right _ _
  have hx_Mx : x ≤ Mx := le_max_left _ _
  have hx'_Mx : x' ≤ Mx := le_max_right _ _
  have hMxnn : 0 ≤ Mx := le_trans hx hx_Mx
  have hmn0 : 0 ≤ mn := by rw [hmn]; exact le_min hx hx'
  have hmnLnn : 0 ≤ mn + L := by linarith
  have hmemA : ∀ n, n ∈ A → x ≤ (n:ℝ) ∧ (n:ℝ) ≤ x + L := by
    intro n hn
    rw [hA, Work.BMF.natIcc, Finset.mem_Icc] at hn
    exact ⟨le_trans (Nat.le_ceil x) (by exact_mod_cast hn.1),
      le_trans (by exact_mod_cast hn.2) (Nat.floor_le (by linarith))⟩
  have hmemB : ∀ n, n ∈ B → x' ≤ (n:ℝ) ∧ (n:ℝ) ≤ x' + L := by
    intro n hn
    rw [hB, Work.BMF.natIcc, Finset.mem_Icc] at hn
    exact ⟨le_trans (Nat.le_ceil x') (by exact_mod_cast hn.1),
      le_trans (by exact_mod_cast hn.2) (Nat.floor_le (by linarith))⟩
  have hsub : (A \ B) ∪ (B \ A) ⊆
      Finset.Ico ⌈mn⌉₊ ⌈Mx⌉₊ ∪ Finset.Ioc ⌊mn + L⌋₊ ⌊Mx + L⌋₊ := by
    intro n hn
    rcases Finset.mem_union.mp hn with hn | hn
    · obtain ⟨hnA, hnB⟩ := Finset.mem_sdiff.mp hn
      obtain ⟨h1, h2⟩ := hmemA n hnA
      have hcase : (n:ℝ) < Mx ∨ mn + L < (n:ℝ) := by
        by_contra hc
        push_neg at hc
        obtain ⟨hc1, hc2⟩ := hc
        exact hnB (by
          rw [hB, Work.BMF.natIcc, Finset.mem_Icc]
          exact ⟨Nat.ceil_le.mpr (le_trans hx'_Mx hc1),
            Nat.le_floor (by linarith)⟩)
      rcases hcase with hcase | hcase
      · have hlt : n < ⌈Mx⌉₊ := by
          have hc : (n:ℝ) < ((⌈Mx⌉₊ : ℕ) : ℝ) := lt_of_lt_of_le hcase (Nat.le_ceil Mx)
          exact_mod_cast hc
        exact Finset.mem_union.mpr (Or.inl
          (Finset.mem_Ico.mpr ⟨Nat.ceil_le.mpr (le_trans hmn_x h1), hlt⟩))
      · have hlt : ⌊mn + L⌋₊ < n := by
          have hf : ((⌊mn + L⌋₊ : ℕ) : ℝ) ≤ mn + L := Nat.floor_le hmnLnn
          have hc : ((⌊mn + L⌋₊ : ℕ) : ℝ) < (n:ℝ) := lt_of_le_of_lt hf hcase
          exact_mod_cast hc
        exact Finset.mem_union.mpr (Or.inr (Finset.mem_Ioc.mpr
          ⟨hlt, Nat.le_floor (by linarith)⟩))
    · obtain ⟨hnB, hnA⟩ := Finset.mem_sdiff.mp hn
      obtain ⟨h1, h2⟩ := hmemB n hnB
      have hcase : (n:ℝ) < Mx ∨ mn + L < (n:ℝ) := by
        by_contra hc
        push_neg at hc
        obtain ⟨hc1, hc2⟩ := hc
        exact hnA (by
          rw [hA, Work.BMF.natIcc, Finset.mem_Icc]
          exact ⟨Nat.ceil_le.mpr (le_trans hx_Mx hc1),
            Nat.le_floor (by linarith)⟩)
      rcases hcase with hcase | hcase
      · have hlt : n < ⌈Mx⌉₊ := by
          have hc : (n:ℝ) < ((⌈Mx⌉₊ : ℕ) : ℝ) := lt_of_lt_of_le hcase (Nat.le_ceil Mx)
          exact_mod_cast hc
        exact Finset.mem_union.mpr (Or.inl
          (Finset.mem_Ico.mpr ⟨Nat.ceil_le.mpr (le_trans hmn_x' h1), hlt⟩))
      · have hlt : ⌊mn + L⌋₊ < n := by
          have hf : ((⌊mn + L⌋₊ : ℕ) : ℝ) ≤ mn + L := Nat.floor_le hmnLnn
          have hc : ((⌊mn + L⌋₊ : ℕ) : ℝ) < (n:ℝ) := lt_of_le_of_lt hf hcase
          exact_mod_cast hc
        exact Finset.mem_union.mpr (Or.inr (Finset.mem_Ioc.mpr
          ⟨hlt, Nat.le_floor (by linarith)⟩))
  have hdisj : Disjoint (A \ B) (B \ A) := by
    rw [Finset.disjoint_left]; intro n hn1 hn2
    exact (Finset.mem_sdiff.mp hn1).2 (Finset.mem_sdiff.mp hn2).1
  have hcard : ((A \ B).card : ℝ) + ((B \ A).card : ℝ) = (((A \ B) ∪ (B \ A)).card : ℝ) := by
    rw [Finset.card_union_of_disjoint hdisj]; push_cast; ring
  rw [hcard]
  have h1 : (((A \ B) ∪ (B \ A)).card : ℝ)
      ≤ ((Finset.Ico ⌈mn⌉₊ ⌈Mx⌉₊ ∪ Finset.Ioc ⌊mn + L⌋₊ ⌊Mx + L⌋₊).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  have h2 : ((Finset.Ico ⌈mn⌉₊ ⌈Mx⌉₊ ∪ Finset.Ioc ⌊mn + L⌋₊ ⌊Mx + L⌋₊).card : ℝ)
      ≤ ((Finset.Ico ⌈mn⌉₊ ⌈Mx⌉₊).card : ℝ) + ((Finset.Ioc ⌊mn + L⌋₊ ⌊Mx + L⌋₊).card : ℝ) := by
    have hh := Finset.card_union_le (Finset.Ico ⌈mn⌉₊ ⌈Mx⌉₊) (Finset.Ioc ⌊mn + L⌋₊ ⌊Mx + L⌋₊)
    push_cast
    exact_mod_cast hh
  have h3 : ((Finset.Ico ⌈mn⌉₊ ⌈Mx⌉₊).card : ℝ) ≤ |x - x'| + 1 := by
    rw [Nat.card_Ico, Nat.cast_sub (Nat.ceil_mono hmn_le)]
    push_cast
    have hu : ((⌈Mx⌉₊ : ℕ) : ℝ) ≤ Mx + 1 :=
      le_of_lt (Nat.ceil_lt_add_one hMxnn)
    have hv : mn ≤ ((⌈mn⌉₊ : ℕ) : ℝ) := Nat.le_ceil mn
    have habs : Mx - mn = |x - x'| := by
      rw [hMx, hmn, abs_sub_comm]; exact max_sub_min_eq_abs x x'
    linarith
  have h4 : ((Finset.Ioc ⌊mn + L⌋₊ ⌊Mx + L⌋₊).card : ℝ) ≤ |x - x'| + 1 := by
    rw [Nat.card_Ioc, Nat.cast_sub (Nat.floor_mono (by linarith : mn + L ≤ Mx + L))]
    push_cast
    have hu : ((⌊Mx + L⌋₊ : ℕ) : ℝ) ≤ Mx + L := Nat.floor_le (by linarith)
    have hv : mn + L ≤ ((⌊mn + L⌋₊ : ℕ) : ℝ) + 1 := le_of_lt (Nat.lt_floor_add_one (mn + L))
    have habs : Mx - mn = |x - x'| := by
      rw [hMx, hmn, abs_sub_comm]; exact max_sub_min_eq_abs x x'
    linarith
  linarith

/-- Moving the left end of a correlation window (step 4 of the route).  For a `1`-bounded `f`, the
correlations of the same phase `P` on `[x, x+L]` and on `[x', x'+L]` differ by at most
`2|x - x'| + 2`. -/
theorem corr_anchor_shift_aux (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1) (P : Polynomial ℝ)
    (x x' L : ℝ) (hx : 0 ≤ x) (hx' : 0 ≤ x') (hL : 0 ≤ L) :
    ‖Work.BMF.corr f P x L‖ ≤ ‖Work.BMF.corr f P x' L‖ + 2 * |x - x'| + 2 := by
  have hg : ∀ n, ‖f n * Work.BMF.eC (-(P.eval (n:ℝ)))‖ ≤ 1 := by
    intro n; rw [norm_mul, sdt_norm_eC, mul_one]; exact hf n
  have h1 : ‖∑ n ∈ Work.BMF.natIcc x (x+L), f n * Work.BMF.eC (-(P.eval (n:ℝ)))
      - ∑ n ∈ Work.BMF.natIcc x' (x'+L), f n * Work.BMF.eC (-(P.eval (n:ℝ)))‖
      ≤ (((Work.BMF.natIcc x (x+L) \ Work.BMF.natIcc x' (x'+L)).card : ℝ)
        + ((Work.BMF.natIcc x' (x'+L) \ Work.BMF.natIcc x (x+L)).card : ℝ)) :=
    sdt_norm_sum_sub_le _ _ _ hg
  have h3 : ‖Work.BMF.corr f P x L - Work.BMF.corr f P x' L‖ ≤ 2 * |x - x'| + 2 := by
    simp only [Work.BMF.corr]
    linarith [h1, sdt_card_diff_bound x x' L hx hx' hL]
  have h4 := norm_le_norm_add_norm_sub (Work.BMF.corr f P x' L) (Work.BMF.corr f P x L)
  have h5 : ‖Work.BMF.corr f P x' L - Work.BMF.corr f P x L‖
      = ‖Work.BMF.corr f P x L - Work.BMF.corr f P x' L‖ := by
    rw [← norm_neg]; ring_nf
  rw [h5] at h4
  linarith

/-- Pigeonholing a prime window into sub-windows of ratio `1 + ρ` (step 3 of the route, no analytic
input): if the good pairs of `[a,b]` (`2 ≤ a ≤ b ≤ 7a/5`) number at least `κ π₀(a)`, then some
sub-window `[a', b'] ⊆ [a, b]` with `b' ≤ (1+ρ) a'` carries at least `c κ π₀(a')` of them. -/
theorem goodPairs_narrow_aux (ρ : ℝ) (hρ : 0 < ρ) (hρ' : ρ ≤ 2 / 5) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (f : ℕ → ℂ) (pol : ℝ → Polynomial ℝ) (η H a b κ : ℝ) (S : Finset ℝ),
        2 ≤ a → a ≤ b → 5 * b ≤ 7 * a → 0 ≤ κ →
        κ * Work.BMF.pi0 a ≤ ((Work.BMF.goodPairs f pol η H a b S).card : ℝ) →
        ∃ a' b' : ℝ, a ≤ a' ∧ a' ≤ b' ∧ b' ≤ b ∧ b' ≤ (1 + ρ) * a' ∧
          c * κ * Work.BMF.pi0 a' ≤ ((Work.BMF.goodPairs f pol η H a' b' S).card : ℝ) := by
  set M : ℕ := ⌈1 / ρ⌉₊ with hMdef
  have hMpos : 0 < M := by
    rw [hMdef]
    have h1 : (1:ℝ) ≤ 1 / ρ := by rw [le_div_iff₀ hρ]; linarith
    have h2 : (1:ℝ) ≤ ((⌈1 / ρ⌉₊ : ℕ) : ℝ) := le_trans h1 (Nat.le_ceil (1/ρ))
    exact_mod_cast h2
  have hceil : 1 / ρ ≤ (M : ℝ) := by rw [hMdef]; exact Nat.le_ceil _
  have hMrho : 1 ≤ (M : ℝ) * ρ := by
    have h := mul_le_mul_of_nonneg_right hceil hρ.le
    rw [div_mul_cancel₀ _ (ne_of_gt hρ)] at h
    linarith
  have hpow2 : 2 ≤ (1 + ρ) ^ M := by
    have hbern := one_add_mul_le_pow (by linarith : (-2:ℝ) ≤ ρ) M
    nlinarith [hMrho, hbern]
  refine ⟨5 / (7 * ((M : ℝ) + 1)), by positivity, ?_⟩
  intro f pol η H a b κ S ha2 hab h5b hκ hcard
  rcases eq_or_lt_of_le hκ with h0 | hpos
  · refine ⟨a, a, le_rfl, le_rfl, hab, ?_, ?_⟩
    · nlinarith [hρ.le, ha2]
    · rw [← h0]; simp
  · have ha0 : 0 < a := by linarith
    have ha1 : 1 < a := by linarith
    have halog : 0 < Real.log a := Real.log_pos ha1
    have hpia : 0 < Work.BMF.pi0 a := by rw [Work.BMF.pi0]; positivity
    have hbnn : 0 ≤ b := by linarith
    set aj : ℕ → ℝ := fun j => a * (1 + ρ) ^ j with haj
    set bj : ℕ → ℝ := fun j => min b (aj (j+1)) with hbj
    have haj0 : aj 0 = a := by simp [haj]
    have hpow1 : (1:ℝ) ≤ 1 + ρ := by linarith
    have hajpos : ∀ j, 0 < aj j := by intro j; rw [haj]; positivity
    have hbjpos : ∀ j, 0 ≤ bj j := by
      intro j
      rw [hbj]
      exact le_min hbnn (by rw [haj]; positivity)
    have hcover : Work.BMF.goodPairs f pol η H a b S ⊆
        (Finset.range M).biUnion (fun j => Work.BMF.goodPairs f pol η H (aj j) (bj j) S) := by
      intro q hq
      rw [Work.BMF.mem_goodPairs] at hq
      obtain ⟨hqS, hqp, hqlvl⟩ := hq
      have hpa : a ≤ (q.2 : ℝ) := Work.BMF.SD.primesIn_lower ha0 hqp
      have hpb : (q.2 : ℝ) ≤ b := Work.BMF.SD.primesIn_upper hbnn hqp
      set Jn := (Finset.range M).filter (fun j => aj j ≤ (q.2:ℝ)) with hJn
      have hJnne : Jn.Nonempty := by
        refine ⟨0, ?_⟩
        rw [hJn, Finset.mem_filter, Finset.mem_range]
        exact ⟨hMpos, by rw [haj0]; exact hpa⟩
      set j := Jn.max' hJnne with hj
      have hjmem : j ∈ Jn := Finset.max'_mem _ _
      have hjlt : j < M := Finset.mem_range.mp (Finset.mem_filter.mp hjmem).1
      have hjle : aj j ≤ (q.2:ℝ) := (Finset.mem_filter.mp hjmem).2
      have hp_le_bj : (q.2:ℝ) ≤ bj j := by
        rw [hbj]
        refine le_min hpb ?_
        rcases lt_or_eq_of_le (Nat.succ_le_iff.mpr hjlt) with hlt | heq
        · by_contra hcon
          have hmem : j + 1 ∈ Jn := by
            rw [hJn, Finset.mem_filter, Finset.mem_range]
            exact ⟨hlt, le_of_lt (not_le.mp hcon)⟩
          have := Finset.le_max' Jn (j+1) hmem
          omega
        · have hje : j + 1 = M := heq
          rw [hje]
          have hpowM : aj M = a * (1 + ρ) ^ M := by rw [haj]
          rw [hpowM]
          nlinarith [hpow2, ha0, hpb, h5b]
      refine Finset.mem_biUnion.mpr ⟨j, Finset.mem_range.mpr hjlt, ?_⟩
      rw [Work.BMF.mem_goodPairs]
      exact ⟨hqS, by
        rw [Work.BMF.primesIn, Work.BMF.natIcc, Finset.mem_filter, Finset.mem_Icc]
        exact ⟨⟨Nat.ceil_le.mpr hjle, Nat.le_floor hp_le_bj⟩,
          Work.BMF.SD.primesIn_prime hqp⟩, hqlvl⟩
    have hsum_le : ((Work.BMF.goodPairs f pol η H a b S).card : ℝ) ≤
        ∑ j ∈ Finset.range M,
          ((Work.BMF.goodPairs f pol η H (aj j) (bj j) S).card : ℝ) := by
      have h1 : ((Work.BMF.goodPairs f pol η H a b S).card : ℝ) ≤
          (((Finset.range M).biUnion
            (fun j => Work.BMF.goodPairs f pol η H (aj j) (bj j) S)).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hcover
      have h2 : (((Finset.range M).biUnion
            (fun j => Work.BMF.goodPairs f pol η H (aj j) (bj j) S)).card : ℝ) ≤
          ∑ j ∈ Finset.range M,
            ((Work.BMF.goodPairs f pol η H (aj j) (bj j) S).card : ℝ) := by
        have hh := Finset.card_biUnion_le (s := Finset.range M)
          (t := fun j => Work.BMF.goodPairs f pol η H (aj j) (bj j) S)
        push_cast
        exact_mod_cast hh
      linarith
    have hMcast : (0:ℝ) < (M : ℝ) := by exact_mod_cast hMpos
    have hne : ∃ j ∈ Finset.range M, κ * Work.BMF.pi0 a / (M:ℝ) ≤
        ((Work.BMF.goodPairs f pol η H (aj j) (bj j) S).card : ℝ) := by
      by_contra hc
      push_neg at hc
      have hlt : ∑ j ∈ Finset.range M,
            ((Work.BMF.goodPairs f pol η H (aj j) (bj j) S).card : ℝ) <
          ∑ _j ∈ Finset.range M, κ * Work.BMF.pi0 a / (M:ℝ) := by
        apply Finset.sum_lt_sum_of_nonempty
        · exact ⟨0, Finset.mem_range.mpr hMpos⟩
        · intro j hj; exact hc j hj
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hlt
      rw [mul_div_cancel₀ _ (ne_of_gt hMcast)] at hlt
      linarith
    obtain ⟨j, hjM, hjcard⟩ := hne
    have hposcard : 0 < ((Work.BMF.goodPairs f pol η H (aj j) (bj j) S).card : ℝ) := by
      have h1 : 0 < κ * Work.BMF.pi0 a / (M:ℝ) := by positivity
      linarith
    have hnonempty : (Work.BMF.goodPairs f pol η H (aj j) (bj j) S).Nonempty := by
      rw [← Finset.card_pos]
      exact_mod_cast hposcard
    obtain ⟨q, hq⟩ := hnonempty
    rw [Work.BMF.mem_goodPairs] at hq
    obtain ⟨hqS, hqp, hqlvl⟩ := hq
    have hajbj : aj j ≤ bj j :=
      le_trans (Work.BMF.SD.primesIn_lower (hajpos j) hqp)
        (Work.BMF.SD.primesIn_upper (hbjpos j) hqp)
    have hle_a : a ≤ aj j := by
      rw [haj]
      have h := pow_le_pow_right₀ hpow1 (Nat.zero_le j)
      nlinarith [h, ha0]
    have hle_b'b : bj j ≤ b := by rw [hbj]; exact min_le_left _ _
    have hle_ratio : bj j ≤ (1 + ρ) * aj j := by
      rw [hbj, haj]
      calc min b (a * (1 + ρ) ^ (j + 1)) ≤ a * (1 + ρ) ^ (j + 1) := min_le_right _ _
        _ = a * (1 + ρ) ^ j * (1 + ρ) := by rw [pow_succ]; ring
        _ = (1 + ρ) * (a * (1 + ρ) ^ j) := by ring
    have hrpi : 5 / (7 * ((M : ℝ) + 1)) * Work.BMF.pi0 (aj j) ≤ Work.BMF.pi0 a / (M:ℝ) := by
      have hlogaj : Real.log a ≤ Real.log (aj j) := Real.log_le_log ha0 hle_a
      have hajle : aj j ≤ 7 * a / 5 := le_trans hajbj (le_trans hle_b'b (by linarith))
      have hlogpos : 0 < Real.log (aj j) := Real.log_pos (by linarith)
      have h1 : Work.BMF.pi0 (aj j) ≤ (7 * a / 5) / Real.log a := by
        have hA : aj j / Real.log (aj j) ≤ (7 * a / 5) / Real.log (aj j) :=
          div_le_div_of_nonneg_right hajle hlogpos.le
        have hB : (7 * a / 5) / Real.log (aj j) ≤ (7 * a / 5) / Real.log a :=
          div_le_div_of_nonneg_left (by linarith) halog hlogaj
        simpa [Work.BMF.pi0] using le_trans hA hB
      have h2 : (7 * a / 5) / Real.log a = 7 / 5 * Work.BMF.pi0 a := by
        rw [Work.BMF.pi0]; ring
      calc 5 / (7 * ((M : ℝ) + 1)) * Work.BMF.pi0 (aj j)
          ≤ 5 / (7 * ((M : ℝ) + 1)) * (7 / 5 * Work.BMF.pi0 a) :=
            mul_le_mul_of_nonneg_left (le_trans h1 (le_of_eq h2)) (by positivity)
        _ = Work.BMF.pi0 a / ((M:ℝ) + 1) := by field_simp
        _ ≤ Work.BMF.pi0 a / (M:ℝ) :=
            div_le_div_of_nonneg_left hpia.le hMcast (by linarith)
    refine ⟨aj j, bj j, hle_a, hajbj, hle_b'b, hle_ratio, ?_⟩
    calc 5 / (7 * ((M : ℝ) + 1)) * κ * Work.BMF.pi0 (aj j)
        = κ * (5 / (7 * ((M : ℝ) + 1)) * Work.BMF.pi0 (aj j)) := by ring
      _ ≤ κ * (Work.BMF.pi0 a / (M:ℝ)) := mul_le_mul_of_nonneg_left hrpi hpos.le
      _ ≤ ((Work.BMF.goodPairs f pol η H (aj j) (bj j) S).card : ℝ) := by
          have heq : κ * (Work.BMF.pi0 a / (M:ℝ)) = κ * Work.BMF.pi0 a / (M:ℝ) := by ring
          rw [heq]; exact hjcard

/-- Scaling down in the bounded-aspect regime `X/H ≤ T₁` (`T₁` arbitrary, supplied by the
caller): the new family is ONE centre-anchored cell `{y/a}`.  This is the regime where the old
decomposition needed the missing "thin-window" input (e.g. a single source at `y = X/10`); here
the centre `y/a ≥ X/(10a)` is admissible by construction and no pair position has to be.

Route (inputs proved except the siblings `Work.BMF.SD.goodPairs_narrow` and
`Work.BMF.SD.corr_anchor_shift`; add their imports).  `T := X/H ∈ [1, T₁]`.
1. `F.fam` is non-empty (`0 < c₀ T ≤ #F.fam`); pick `y ∈ F.fam`, `S := {y}`; `1 ≥ (1/T₁) T`.
2. `tk_bad_weight_sub k c₀` (bad weight of `S` `≤ K`), then `good_window_pairs_sub k c₀ K` with
   `c'' := 1/T₁`: a thick window `[a,b]` with `≥ (c₁₂/T₁) π₀(a)` good primes `p` for `y`
   (`T ≥ 1`), goodness `(c₀/2)(H/p) ≤ ‖corr f (dil p φ_y) (y/p) (H/p)‖`.
3. `goodPairs_narrow ρ₁` with `ρ₁ := min (2/5) (min c₀ 1 / (80 T₁))`: a window
   `[a',b'] ⊆ [a,b]`, `b' ≤ (1+ρ₁)a'`, with `≥ c_ρ₁ (c₁₂/T₁) π₀(a')` good pairs `(y,p)`.
4. Centre `x₀ := y/a'`.  For those `p`: `0 ≤ x₀ - y/p = y(p-a')/(a'p) ≤ ρ₁ y/p ≤ 10 ρ₁ T (H/p)
   ≤ (min c₀ 1 / 8)(H/p) ≤ H/a'` (`y ≤ 10X`).  By `corr_anchor_shift`,
   `‖corr f (dil p φ_y) x₀ (H/p)‖ ≥ (c₀/2 - c₀/4)(H/p) - 2 ≥ (c₀/8)(H/p)` once
   `H/p ≥ H/Q ≥ Q² ≥ P₀² ≥ 16/c₀`.
5. `cell_center k hk (c₀/8)` (constants `C₃ c₃ K₃`) on `S_y := goodPairs .. a' b' {y}` at `x₀`
   (`1 ≤ H/a'`, `1 ≤ x₀`, positions `≥ 1`: all from `Q³ ≤ H ≤ X`, `Q ≥ P₀ ≥ 4`; degrees by
   `Work.BMF.dil_mem_degreeLE`): `pol'`, `S' ⊆ S_y`, `#S' ≥ #S_y/(2K₃)`,
   `c₃ (H/a') ≤ ‖corr f pol' x₀ (H/a')‖`, and for `q ∈ S'`: `|q.pos - x₀| ≤ 3H/a'` and
   `PolyRel k C₃ 1 (q.pos) (H/q.2) (dil q.2 φ_y) x₀ (H/a') pol'`.
6. `F' := ⟨{x₀}, fun _ => pol', ..⟩`: `IsFam` from `X/10 ≤ y`, `y + H ≤ 10X`; `card_ge` from
   `c T ≤ c T₁ ≤ 1`; `corr_ge` from `c ≤ c₃`; `S' ⊆ incPairs k C₃ F.fam a' b' H (3H/a') (H/a')
   F.pol pol' x₀`.  Constants: `C := C₃`, `A := A₁₂`, `P₀ := max 4 (16/c₀ + 4)`,
   `c := min (min c₀ c₃) (min (1/T₁) (c_ρ₁ c₁₂ / (2 K₃ T₁)))`. -/
theorem scale_down_small_T (k : ℕ) (hk : 1 ≤ k) (c₀ : ℝ) (hc₀ : 0 < c₀) (T₁ : ℝ)
    (hT₁ : 1 ≤ T₁) :
    ∃ c C A P₀ : ℝ, 0 < c ∧ 0 < C ∧ 0 < A ∧ 0 < P₀ ∧ c ≤ c₀ ∧
      ∀ (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1)
        (hmul : ∀ m n, Nat.Coprime m n → f (m * n) = f m * f n)
        (X H P Q : ℝ), 2 ≤ P → P ≤ Q → Q ^ 3 ≤ H → H ≤ X → P₀ ≤ P →
        A ≤ Real.log Q / Real.log P → X / H ≤ T₁ →
        ∀ (F : Work.BMF.PhaseFamily k f c₀ X H),
        ∃ (a b : ℝ) (F' : Work.BMF.PhaseFamily k f c (X / a) (H / a)),
          P ≤ a ∧ a ≤ b ∧ b ≤ Q ∧ 5 * b ≤ 7 * a ∧
            ∀ x' ∈ F'.fam, c * Work.BMF.pi0 a ≤
              ((Work.BMF.incPairs k C F.fam a b H (3 * H / a) (H / a) F.pol (F'.pol x')
                x').card : ℝ) := by
  classical
  obtain ⟨K, hKpos, _hKle, hKbad⟩ := Work.BMF.SD.tk_bad_weight_sub k c₀ hc₀
  obtain ⟨c12, A12, hc12pos, hA12pos, hgwps⟩ :=
    Work.BMF.SD.good_window_pairs_sub k c₀ K hc₀ hKpos
  obtain ⟨C3, c3, K3, hC3pos, hc3pos, hK3pos, hcell⟩ :=
    Work.BMF.SD.cell_center k hk (c₀ / 8) (by positivity)
  set ρ₁ : ℝ := min (2 / 5) (min c₀ 1 / (80 * T₁)) with hρ₁def
  have hρ₁pos : 0 < ρ₁ := by
    rw [hρ₁def]
    exact lt_min (by norm_num) (div_pos (lt_min hc₀ one_pos) (by linarith))
  have hρ₁le : ρ₁ ≤ 2 / 5 := by rw [hρ₁def]; exact min_le_left _ _
  have hρ₁le' : ρ₁ ≤ min c₀ 1 / (80 * T₁) := by rw [hρ₁def]; exact min_le_right _ _
  obtain ⟨crho, hcrhorhopos, hgn⟩ := goodPairs_narrow_aux ρ₁ hρ₁pos hρ₁le
  set cconst : ℝ := min (min c₀ c3) (min (1 / T₁) (crho * c12 / (2 * K3 * T₁))) with hcdef
  have hcpos : 0 < cconst := by
    rw [hcdef]
    exact lt_min (lt_min hc₀ hc3pos)
      (lt_min (by positivity) (div_pos (mul_pos hcrhorhopos hc12pos) (by positivity)))
  have hcc0 : cconst ≤ c₀ := le_trans (min_le_left _ _) (min_le_left _ _)
  have hcc3 : cconst ≤ c3 := le_trans (min_le_left _ _) (min_le_right _ _)
  have hcT : cconst ≤ 1 / T₁ := le_trans (min_le_right _ _) (min_le_left _ _)
  have hcmain : cconst ≤ crho * c12 / (2 * K3 * T₁) :=
    le_trans (min_le_right _ _) (min_le_right _ _)
  have hT1pos : 0 < T₁ := lt_of_lt_of_le zero_lt_one hT₁
  have hP0pos : 0 < max 4 (16 / c₀ + 4) := by
    refine lt_max_of_lt_left ?_
    norm_num
  refine ⟨cconst, C3, A12, max 4 (16 / c₀ + 4), hcpos, hC3pos, hA12pos, hP0pos, hcc0, ?_⟩
  intro f hf hmul X H P Q hP2 hPQ hQ3 hHX hP0leP hAlog hT F
  have hPpos : 0 < P := by linarith
  have hQpos : 0 < Q := by linarith
  have hP0P : (4 : ℝ) ≤ P := le_trans (le_max_left _ _) hP0leP
  have h16P : 16 / c₀ + 4 ≤ P := le_trans (le_max_right _ _) hP0leP
  have hQ4 : (4 : ℝ) ≤ Q := le_trans hP0P hPQ
  have hQ1 : (1 : ℝ) ≤ Q := by linarith
  have hQ2 : (2 : ℝ) ≤ Q := by linarith
  have hHpos : 0 < H := by
    have h8 : (8 : ℝ) ≤ Q ^ 3 := by
      have h2 : (2:ℝ) * 2 ≤ Q * Q := mul_le_mul hQ2 hQ2 (by norm_num) hQpos.le
      have h3 : ((2:ℝ) * 2) * 2 ≤ (Q * Q) * Q :=
        mul_le_mul h2 hQ2 (by norm_num) (by positivity)
      have h5 : (Q * Q) * Q = Q ^ 3 := by ring
      rw [h5] at h3
      norm_num at h3
      exact h3
    linarith
  have hXpos : 0 < X := lt_of_lt_of_le hHpos hHX
  have hTpos : 0 < X / H := div_pos hXpos hHpos
  have hTge1 : 1 ≤ X / H := (one_le_div hHpos).mpr hHX
  have hQleQ3 : Q ≤ Q ^ 3 := by
    have hqq : (1:ℝ) ≤ Q * Q := by
      simpa using mul_le_mul hQ1 hQ1 (by norm_num : (0:ℝ) ≤ 1) hQpos.le
    have h2 : Q * 1 ≤ Q * (Q * Q) := mul_le_mul_of_nonneg_left hqq hQpos.le
    have h3 : Q * 1 = Q := by ring
    have h4 : Q * (Q * Q) = Q ^ 3 := by ring
    linarith
  have hQleH : Q ≤ H := le_trans hQleQ3 hQ3
  have hQ_le_X : Q ≤ X / 10 := by
    have h1 : (10 : ℝ) ≤ Q * Q := by nlinarith [hQ4]
    have h2 : Q ≤ Q ^ 3 / 10 := by nlinarith [hQpos, h1]
    have h3 : Q ^ 3 / 10 ≤ X / 10 := by linarith
    linarith
  -- Step 1: a source
  have hfampos : 0 < F.fam.card := by
    have h1 : (0:ℝ) < (F.fam.card : ℝ) := lt_of_lt_of_le (mul_pos hc₀ hTpos) F.card_ge
    exact_mod_cast h1
  obtain ⟨y, hyfam⟩ := Finset.card_pos.mp hfampos
  have hy_lo : X / 10 ≤ y := (F.isFam.1 y hyfam).1
  have hy_hi : y + H ≤ 10 * X := (F.isFam.1 y hyfam).2
  have hypos : 0 < y := by linarith
  have hy_le : y ≤ 10 * X := by linarith
  -- Step 2: the thick window
  have hSsub : ({y} : Finset ℝ) ⊆ F.fam := by
    intro z hz
    rw [Finset.mem_singleton] at hz
    rw [hz]; exact hyfam
  have hcardS : (1 / T₁) * (X / H) ≤ (({y} : Finset ℝ).card : ℝ) := by
    rw [Finset.card_singleton]
    have h1 : (1 / T₁) * (X / H) ≤ (1 / T₁) * T₁ :=
      mul_le_mul_of_nonneg_left hT (by positivity)
    have h2 : (1 / T₁) * T₁ = 1 := by field_simp
    linarith
  have hbad := hKbad f hf hmul X H P Q hP2 hPQ hQ3 hHX F {y} hSsub
  obtain ⟨a, b, hPa, hab, h5b, hbQ, hgw⟩ :=
    hgwps f hf hmul X H P Q (1 / T₁) (by positivity) hP2 hPQ hQ3 hHX hAlog F {y} hSsub
      hcardS hbad
  -- Step 3: the narrow window
  have h2a : (2 : ℝ) ≤ a := le_trans hP2 hPa
  have hkappa_nn : 0 ≤ c12 * (1 / T₁) * (X / H) := by
    have := mul_pos hc12pos (by positivity : (0:ℝ) < 1 / T₁)
    exact le_of_lt (mul_pos this hTpos)
  obtain ⟨a', b', haa', ha'b', hb'b, hb'ra', hgn'⟩ :=
    hgn f F.pol (c₀ / 2) H a b (c12 * (1 / T₁) * (X / H)) {y} h2a hab h5b hkappa_nn hgw
  -- basic facts about the narrow window
  have ha'pos : 0 < a' := by linarith
  have ha'Q : a' ≤ Q := le_trans (le_trans ha'b' hb'b) hbQ
  have ha'H : a' ≤ H := le_trans ha'Q hQleH
  have ha'X : a' ≤ X / 10 := le_trans ha'Q hQ_le_X
  have ha'y : a' ≤ y := le_trans ha'X hy_lo
  have hb'pos : 0 < b' := lt_of_lt_of_le ha'pos ha'b'
  have hb'1 : (1 : ℝ) ≤ b' := by linarith
  have h5b' : 5 * b' ≤ 7 * a' := by
    have h1 : (1 + ρ₁) ≤ 7 / 5 := by linarith
    calc 5 * b' ≤ 5 * ((1 + ρ₁) * a') := by linarith
      _ = (5 * (1 + ρ₁)) * a' := by ring
      _ ≤ (5 * (7 / 5)) * a' := mul_le_mul_of_nonneg_right (by linarith) ha'pos.le
      _ = 7 * a' := by norm_num
  have hHa' : 1 ≤ H / a' := (one_le_div ha'pos).mpr ha'H
  have hx0 : 1 ≤ y / a' := by
    rw [one_le_div ha'pos]
    linarith
  have hlogpa : 0 < Real.log a' := Real.log_pos (by linarith)
  have hpi0a' : 0 < Work.BMF.pi0 a' := by rw [Work.BMF.pi0]; positivity
  -- the set of good pairs of the narrow window
  set Sy : Finset (ℝ × ℕ) := Work.BMF.goodPairs f F.pol (c₀ / 2) H a' b' {y} with hSy
  have hposSy : 0 < (Sy.card : ℝ) := by
    have h1 : 0 < crho * (c12 * (1 / T₁) * (X / H)) * Work.BMF.pi0 a' := by
      have h2 : 0 < c12 * (1 / T₁) * (X / H) := by
        have := mul_pos hc12pos (by positivity : (0:ℝ) < 1 / T₁)
        exact mul_pos this hTpos
      exact mul_pos (mul_pos hcrhorhopos h2) hpi0a'
    exact lt_of_lt_of_le h1 (by rw [hSy]; exact hgn')
  have hSyne : Sy.Nonempty := by
    have h1 : 0 < Sy.card := by exact_mod_cast hposSy
    exact Finset.card_pos.mp h1
  have hmemSy : ∀ q, q ∈ Sy ↔ q.1 ∈ ({y} : Finset ℝ) ∧ q.2 ∈ Work.BMF.primesIn a' b' ∧
      (c₀ / 2) * (H / (q.2 : ℝ)) ≤
        ‖Work.BMF.corr f (Work.BMF.dil (q.2 : ℝ) (F.pol q.1)) (q.1 / (q.2 : ℝ))
          (H / (q.2 : ℝ))‖ := by
    intro q
    rw [hSy, Work.BMF.mem_goodPairs]
  have hpos1 : ∀ q ∈ Sy, 1 ≤ q.1 / (q.2 : ℝ) := by
    intro q hq
    obtain ⟨hq1, hq2, _⟩ := (hmemSy q).mp hq
    rw [Finset.mem_singleton] at hq1
    have hppos : (0 : ℝ) < (q.2 : ℝ) := by
      have := Work.BMF.SD.primesIn_pos hq2
      exact_mod_cast this
    have hpQ : (q.2 : ℝ) ≤ Q :=
      le_trans (Work.BMF.SD.primesIn_upper hb'pos.le hq2) (le_trans hb'b hbQ)
    rw [hq1]
    exact (le_div_iff₀ hppos).mpr (by linarith)
  have hpc : ∀ q ∈ Sy, a' ≤ (q.2 : ℝ) ∧ (q.2 : ℝ) ≤ b' := by
    intro q hq
    obtain ⟨_, hq2, _⟩ := (hmemSy q).mp hq
    exact ⟨Work.BMF.SD.primesIn_lower ha'pos hq2,
      Work.BMF.SD.primesIn_upper hb'pos.le hq2⟩
  have hdistStrong : ∀ q ∈ Sy,
      |q.1 / (q.2 : ℝ) - y / a'| ≤ (min c₀ 1) / 8 * (H / (q.2 : ℝ)) := by
    intro q hq
    obtain ⟨hq1, hq2, _⟩ := (hmemSy q).mp hq
    rw [Finset.mem_singleton] at hq1
    have hp1 : a' ≤ (q.2 : ℝ) := Work.BMF.SD.primesIn_lower ha'pos hq2
    have hppos : 0 < (q.2 : ℝ) := lt_of_lt_of_le ha'pos hp1
    have hp2 : (q.2 : ℝ) ≤ b' := Work.BMF.SD.primesIn_upper hb'pos.le hq2
    have hpa_le : (q.2 : ℝ) - a' ≤ ρ₁ * a' := by
      have h : (q.2 : ℝ) ≤ (1 + ρ₁) * a' := le_trans hp2 hb'ra'
      nlinarith [h]
    have hA : y / a' - y / (q.2 : ℝ) ≤ ρ₁ * (y / (q.2 : ℝ)) := by
      have h1 : y / (q.2 : ℝ) ≤ y / a' := div_le_div_of_nonneg_left hypos.le ha'pos hp1
      rw [show y / a' - y / (q.2 : ℝ) = y * ((q.2 : ℝ) - a') / ((q.2 : ℝ) * a') by
            field_simp <;> ring]
      rw [show ρ₁ * (y / (q.2 : ℝ)) = ρ₁ * y / (q.2 : ℝ) by ring]
      rw [div_le_iff₀ (by positivity : (0:ℝ) < (q.2 : ℝ) * a')]
      have hrhs : (ρ₁ * y / (q.2 : ℝ)) * ((q.2 : ℝ) * a') = ρ₁ * y * a' := by
        field_simp <;> ring
      rw [hrhs]
      nlinarith [hpa_le, hypos.le, ha'pos.le]
    have hstep1 : y / (q.2 : ℝ) ≤ 10 * T₁ * (H / (q.2 : ℝ)) := by
      have h1 : y / (q.2 : ℝ) ≤ 10 * X / (q.2 : ℝ) :=
        div_le_div_of_nonneg_right hy_le hppos.le
      have h2 : 10 * X / (q.2 : ℝ) = 10 * (X / H) * (H / (q.2 : ℝ)) := by
        field_simp <;> ring
      have h3 : 10 * (X / H) * (H / (q.2 : ℝ)) ≤ 10 * T₁ * (H / (q.2 : ℝ)) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        linarith
      linarith
    have hstep2 : ρ₁ * (10 * T₁ * (H / (q.2 : ℝ))) ≤
        (min c₀ 1) / 8 * (H / (q.2 : ℝ)) := by
      have h1 : ρ₁ * (10 * T₁) ≤ (min c₀ 1) / (80 * T₁) * (10 * T₁) :=
        mul_le_mul_of_nonneg_right hρ₁le' (by positivity)
      have h2 : (min c₀ 1) / (80 * T₁) * (10 * T₁) = (min c₀ 1) / 8 := by
        field_simp <;> ring
      calc ρ₁ * (10 * T₁ * (H / (q.2 : ℝ)))
          = (ρ₁ * (10 * T₁)) * (H / (q.2 : ℝ)) := by ring
        _ ≤ ((min c₀ 1) / 8) * (H / (q.2 : ℝ)) := by
            rw [← h2]; exact mul_le_mul_of_nonneg_right h1 (by positivity)
    have h4 := mul_le_mul_of_nonneg_left hstep1 hρ₁pos.le
    have hmono : q.1 / (q.2 : ℝ) ≤ y / a' := by
      rw [hq1]; exact div_le_div_of_nonneg_left hypos.le ha'pos hp1
    have habs : |q.1 / (q.2 : ℝ) - y / a'| = y / a' - y / (q.2 : ℝ) := by
      rw [hq1,
        abs_of_nonpos (by linarith [div_le_div_of_nonneg_left hypos.le ha'pos hp1])]
      ring
    rw [habs]
    linarith [hA, h4, hstep2]
  have hdistSy : ∀ q ∈ Sy, |q.1 / (q.2 : ℝ) - y / a'| ≤ H / a' := by
    intro q hq
    obtain ⟨_, hq2, _⟩ := (hmemSy q).mp hq
    have hp1 : a' ≤ (q.2 : ℝ) := Work.BMF.SD.primesIn_lower ha'pos hq2
    have h1 : H / (q.2 : ℝ) ≤ H / a' := div_le_div_of_nonneg_left hHpos.le ha'pos hp1
    have h2 : (min c₀ 1) / 8 * (H / (q.2 : ℝ)) ≤ H / a' := by
      calc (min c₀ 1) / 8 * (H / (q.2 : ℝ)) ≤ 1 * (H / a') :=
            mul_le_mul (by linarith [min_le_right (a := c₀) (b := (1:ℝ))]) h1
              (by positivity) (by positivity)
        _ = H / a' := by ring
    linarith [hdistStrong q hq]
  have hdeg : ∀ q ∈ Sy, Work.BMF.dil (q.2 : ℝ) (F.pol q.1) ∈
      Polynomial.degreeLE ℝ (k : WithBot ℕ) := by
    intro q hq
    obtain ⟨hq1, _, _⟩ := (hmemSy q).mp hq
    rw [Finset.mem_singleton] at hq1
    rw [hq1]
    exact Work.BMF.dil_mem_degreeLE (F.deg y hyfam)
  have hgood : ∀ q ∈ Sy, (c₀ / 8) * (H / (q.2 : ℝ)) ≤
      ‖Work.BMF.corr f (Work.BMF.dil (q.2 : ℝ) (F.pol q.1)) (y / a') (H / (q.2 : ℝ))‖ := by
    intro q hq
    obtain ⟨hq1, hq2, hlvl⟩ := (hmemSy q).mp hq
    have hp1 : a' ≤ (q.2 : ℝ) := Work.BMF.SD.primesIn_lower ha'pos hq2
    have hp2 : (q.2 : ℝ) ≤ b' := Work.BMF.SD.primesIn_upper hb'pos.le hq2
    have hppos : 0 < (q.2 : ℝ) := lt_of_lt_of_le ha'pos hp1
    have hpn : 0 ≤ H / (q.2 : ℝ) := by positivity
    -- the centre is close to the pair's position
    have hclose := hdistStrong q hq
    -- hence the shifted correlation
    have hx1 : 0 ≤ q.1 / (q.2 : ℝ) := by
      rw [Finset.mem_singleton] at hq1; rw [hq1]; positivity
    have hx2 : 0 ≤ y / a' := by positivity
    have hshift :=
      corr_anchor_shift_aux f hf (Work.BMF.dil (q.2 : ℝ) (F.pol q.1)) (q.1 / (q.2 : ℝ))
        (y / a') (H / (q.2 : ℝ)) hx1 hx2 hpn
    -- `H/p ≥ Q² ≥ 16/c₀`
    have hHp : 16 / c₀ ≤ H / (q.2 : ℝ) := by
      have h1 : Q * Q ≤ H / Q := by
        rw [le_div_iff₀ hQpos]
        nlinarith [hQ3, hQpos]
      have h2 : H / Q ≤ H / (q.2 : ℝ) :=
        div_le_div_of_nonneg_left hHpos.le hppos (le_trans hp2 (le_trans hb'b hbQ))
      have h3 : 16 / c₀ ≤ Q * Q := by
        have h4 : 16 / c₀ + 4 ≤ Q := le_trans h16P hPQ
        have h5 : 16 / c₀ ≤ Q := by linarith
        have h6 : Q ≤ Q * Q := by
          have := mul_le_mul_of_nonneg_left hQ1 hQpos.le
          linarith
        linarith
      linarith
    -- the shift costs at most `(3c₀/8)(H/p)`
    have hm_le : min c₀ 1 ≤ c₀ := min_le_left _ _
    have hcoef : 0 ≤ 3 * c₀ / 8 - min c₀ 1 / 4 := by linarith
    have hδ1 : 2 * |q.1 / (q.2 : ℝ) - y / a'| ≤ (min c₀ 1) / 4 * (H / (q.2 : ℝ)) := by
      have h1 := mul_le_mul_of_nonneg_left hclose (by norm_num : (0:ℝ) ≤ 2)
      have h2 : 2 * ((min c₀ 1) / 8 * (H / (q.2 : ℝ))) =
          (min c₀ 1) / 4 * (H / (q.2 : ℝ)) := by ring
      linarith
    have hδ2 : 2 ≤ (3 * c₀ / 8 - min c₀ 1 / 4) * (H / (q.2 : ℝ)) := by
      have hkey : (3 * c₀ / 8 - min c₀ 1 / 4) * (16 / c₀) ≥ 2 := by
        have heq : (3 * c₀ / 8 - min c₀ 1 / 4) * (16 / c₀)
            = 6 - 4 * ((min c₀ 1) / c₀) := by
          field_simp <;> ring
        rw [heq]
        have hm : min c₀ 1 / c₀ ≤ 1 := by
          rw [div_le_one hc₀]; exact min_le_left _ _
        linarith
      calc (2 : ℝ) ≤ (3 * c₀ / 8 - min c₀ 1 / 4) * (16 / c₀) := hkey
        _ ≤ (3 * c₀ / 8 - min c₀ 1 / 4) * (H / (q.2 : ℝ)) :=
            mul_le_mul_of_nonneg_left hHp hcoef
    have hδ : 2 * |q.1 / (q.2 : ℝ) - y / a'| + 2 ≤ (3 * c₀ / 8) * (H / (q.2 : ℝ)) := by
      have hsum : (min c₀ 1) / 4 * (H / (q.2 : ℝ)) +
          (3 * c₀ / 8 - min c₀ 1 / 4) * (H / (q.2 : ℝ)) =
          (3 * c₀ / 8) * (H / (q.2 : ℝ)) := by ring
      linarith [hδ1, hδ2, hsum]
    linarith [hlvl, hshift]
  obtain ⟨pol', S', hS'sub, hpol'corr, hpol'deg, hS'card, hS'inc⟩ :=
    hcell f hf F.pol H a' b' (y / a') Sy ha'pos ha'b' h5b' hHa' hx0 hb'1 hSyne hpos1 hpc
      hdistSy hgood hdeg
  -- Step 6: the new family
  have hIsFam : Work.BMF.IsFam (X / a') (H / a') ({y / a'} : Finset ℝ) := by
    constructor
    · intro x hx
      rw [Finset.mem_singleton] at hx
      rw [hx]
      constructor
      · have h1 : X / a' / 10 = X / (10 * a') := by ring
        rw [h1]
        calc X / (10 * a') = (X / 10) / a' := by ring
          _ ≤ y / a' := div_le_div_of_nonneg_right hy_lo ha'pos.le
      · have h1 : y / a' + H / a' = (y + H) / a' := by ring
        rw [h1]
        calc (y + H) / a' ≤ (10 * X) / a' := div_le_div_of_nonneg_right hy_hi ha'pos.le
          _ = 10 * (X / a') := by ring
    · intro x hx z hz hne
      rw [Finset.mem_singleton] at hx hz
      exact absurd (by rw [hx, hz]) hne
  have hcardge' : cconst * ((X / a') / (H / a')) ≤ (({y / a'} : Finset ℝ).card : ℝ) := by
    rw [Finset.card_singleton]
    have h1 : (X / a') / (H / a') = X / H := by field_simp
    rw [h1]
    have h2 : cconst * (X / H) ≤ (1 / T₁) * T₁ :=
      mul_le_mul hcT hT hTpos.le (by positivity)
    have h3 : (1 / T₁) * T₁ = 1 := by field_simp
    linarith
  have hdeg' : ∀ x ∈ ({y / a'} : Finset ℝ),
      (fun _ => pol') x ∈ Polynomial.degreeLE ℝ (k : WithBot ℕ) := by
    intro x hx; exact hpol'deg
  have hcorr' : ∀ x ∈ ({y / a'} : Finset ℝ), cconst * (H / a') ≤
      ‖Work.BMF.corr f ((fun _ => pol') x) x (H / a')‖ := by
    intro x hx
    rw [Finset.mem_singleton] at hx
    rw [hx]
    exact le_trans (mul_le_mul_of_nonneg_right hcc3 (by positivity)) hpol'corr
  refine ⟨a', b', ⟨{y / a'}, (fun _ => pol'), hIsFam, hcardge', hdeg', hcorr'⟩,
    le_trans hPa haa', ha'b', le_trans hb'b hbQ, h5b', ?_⟩
  intro x' hx'
  rw [Finset.mem_singleton] at hx'
  rw [hx']
  have hsub : S' ⊆ Work.BMF.incPairs k C3 F.fam a' b' H (3 * H / a') (H / a') F.pol pol'
      (y / a') := by
    intro q hq
    obtain ⟨hqx, hqrel⟩ := hS'inc q hq
    have hqSy : q ∈ Sy := hS'sub hq
    obtain ⟨hq1, hq2, _⟩ := (hmemSy q).mp hqSy
    rw [Finset.mem_singleton] at hq1
    rw [Work.BMF.incPairs, Finset.mem_filter, Finset.mem_product]
    exact ⟨⟨by rw [hq1]; exact hyfam, hq2⟩, hqx, hqrel⟩
  have hfinal : crho * c12 / (2 * K3 * T₁) * Work.BMF.pi0 a' ≤ (S'.card : ℝ) := by
    have hcoef : 0 ≤ crho * c12 / (2 * K3 * T₁) := by positivity
    have hstep1 : crho * c12 / (2 * K3 * T₁) * Work.BMF.pi0 a' ≤
        crho * c12 / (2 * K3 * T₁) * (X / H) * Work.BMF.pi0 a' := by
      have h1 := mul_le_mul_of_nonneg_right hTge1 hcoef
      nlinarith [hpi0a'.le]
    have hstep2 : crho * c12 / (2 * K3 * T₁) * (X / H) * Work.BMF.pi0 a' ≤
        (Sy.card : ℝ) / (2 * K3) := by
      have heq : crho * c12 / (2 * K3 * T₁) * (X / H) * Work.BMF.pi0 a' =
          crho * (c12 * (1 / T₁) * (X / H)) * Work.BMF.pi0 a' / (2 * K3) := by
        field_simp <;> ring
      rw [heq]
      exact div_le_div_of_nonneg_right hgn' (by positivity)
    linarith [hstep1, hstep2, hS'card]
  calc cconst * Work.BMF.pi0 a'
      ≤ crho * c12 / (2 * K3 * T₁) * Work.BMF.pi0 a' :=
        mul_le_mul_of_nonneg_right hcmain hpi0a'.le
    _ ≤ (S'.card : ℝ) := hfinal
    _ ≤ ((Work.BMF.incPairs k C3 F.fam a' b' H (3 * H / a') (H / a') F.pol pol'
          (y / a')).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub

end Work.BMF.SD
