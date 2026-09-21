import Mathlib
import Submission.Work.OddVolterra.Defs

/-!
# Faà di Bruno bounds for composites `u ↦ Φ (u, h u)`

This file provides the elementary "jet" machinery used to prove that the odd transition-slope
data (`Godd`, `Theta`, `Xi`) of `Work.OddVolterra` is continuous at `h = 0` in the
`C^{n+2}` topology.

The engine is Mathlib's Faà di Bruno formula
`iteratedDeriv_vcomp_eq_sum_orderedFinpartition`, applied to the graph curve
`u ↦ (u, h u)`.  It expresses `iteratedDeriv i (fun u => Φ (u, h u)) x` as a finite sum over set
partitions of `{1,…,i}` of products of (i) `iteratedFDeriv`'s of `Φ` at `(x, h x)` and
(ii) the jet `(h x, h' x, …, h^{(i)} x)`.  Bounding the `iteratedFDeriv`'s of `Φ` on a compact
box then gives uniform bounds, independent of the perturbation `h`; and telescoping the two
sums (for `h` and for `0`) produces an explicit factor `δ` in the smallness bound.
-/

namespace Work.OddVolterra.Existence

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

noncomputable section

/-! ## The Faà di Bruno formula on the graph curve -/

/-- `(k : ℕ∞ω) ≤ ∞`: the side condition of Mathlib's Faà di Bruno formula for a `C^∞` function. -/
lemma coe_nat_le_infty (k : ℕ) : (k : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω) := by
  exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤)

/-- The `k`-th iterated derivative of a pair-valued function is componentwise. -/
lemma iteratedDeriv_pair (k : ℕ) (f g : ℝ → ℝ) (x : ℝ)
    (hf : ContDiffAt ℝ ((⊤ : ℕ∞) : ℕ∞ω) f x) (hg : ContDiffAt ℝ ((⊤ : ℕ∞) : ℕ∞ω) g x) :
    iteratedDeriv k (fun u : ℝ => (f u, g u)) x = (iteratedDeriv k f x, iteratedDeriv k g x) := by
  simp only [iteratedDeriv]
  rw [iteratedFDeriv_prodMk hf hg (i := k) (coe_nat_le_infty k)]
  rfl

/-- **Faà di Bruno for the graph curve** `u ↦ (u, h u)`. -/
theorem iteratedDeriv_comp_pair (i : ℕ) (Φ : ℝ × ℝ → ℝ) (h : ℝ → ℝ) (x : ℝ)
    (hΦ : ContDiffAt ℝ ((⊤ : ℕ∞) : ℕ∞ω) Φ (x, h x))
    (hh : ContDiffAt ℝ ((⊤ : ℕ∞) : ℕ∞ω) h x) :
    iteratedDeriv i (fun u : ℝ => Φ (u, h u)) x =
      ∑ c : OrderedFinpartition i,
        (iteratedFDeriv ℝ c.length Φ (x, h x))
          (fun j => (iteratedDeriv (c.partSize j) (fun u : ℝ => u) x,
                     iteratedDeriv (c.partSize j) h x)) := by
  have h1 := iteratedDeriv_vcomp_eq_sum_orderedFinpartition (𝕜 := ℝ)
    (g := fun p : ℝ × ℝ => Φ p) (f := fun u : ℝ => (u, h u)) (x := x) (i := i)
    (n := ((⊤ : ℕ∞) : ℕ∞ω)) hΦ (contDiffAt_id.prodMk hh) (coe_nat_le_infty i)
  show iteratedDeriv i ((fun p : ℝ × ℝ => Φ p) ∘ (fun u : ℝ => (u, h u))) x = _
  rw [h1]
  congr 1
  funext c
  congr 1
  funext j
  exact iteratedDeriv_pair (c.partSize j) (fun u : ℝ => u) h x contDiffAt_id hh

/-! ## The box and the bounds -/

/-- The (compact) box of the graph curve. -/
def jetBox (c d R : ℝ) : Set (ℝ × ℝ) := Set.Icc c d ×ˢ Set.Icc (-R) R

/-- An open thickening of the box, on which smoothness of `Φ` is required. -/
def jetBoxOpen (c d R : ℝ) : Set (ℝ × ℝ) :=
  Set.Ioo (c - 1) (d + 1) ×ˢ Set.Ioo (-R - 1) (R + 1)

lemma jetBox_subset_jetBoxOpen {c d R : ℝ} : jetBox c d R ⊆ jetBoxOpen c d R := by
  rintro ⟨x, y⟩ ⟨hx, hy⟩
  exact ⟨⟨by linarith [hx.1], by linarith [hx.2]⟩, ⟨by linarith [hy.1], by linarith [hy.2]⟩⟩

lemma isOpen_jetBoxOpen (c d R : ℝ) : IsOpen (jetBoxOpen c d R) :=
  isOpen_Ioo.prod isOpen_Ioo

lemma isCompact_jetBox (c d R : ℝ) : IsCompact (jetBox c d R) :=
  isCompact_Icc.prod isCompact_Icc

/-- The supremum-type bounds on the `iteratedFDeriv`'s of `Φ` over the box. -/
theorem exists_bound_iteratedFDeriv (Φ : ℝ × ℝ → ℝ) {c d R : ℝ} (hcd : c ≤ d) (hR : 0 ≤ R)
    (hΦ : ContDiffOn ℝ ((⊤ : ℕ∞) : ℕ∞ω) Φ (jetBoxOpen c d R)) :
    ∃ M : ℕ → ℝ, (∀ k, 0 ≤ M k) ∧ ∀ k, ∀ p ∈ jetBox c d R, ‖iteratedFDeriv ℝ k Φ p‖ ≤ M k := by
  have hcont : ∀ k : ℕ, ContinuousOn (fun p : ℝ × ℝ => iteratedFDeriv ℝ k Φ p)
      (jetBoxOpen c d R) := fun k =>
    ContinuousOn.continuousOn_iteratedFDeriv hΦ (isOpen_jetBoxOpen c d R) (coe_nat_le_infty k)
  choose M hM using fun k : ℕ =>
    (isCompact_jetBox c d R).exists_bound_of_continuousOn ((hcont k).mono jetBox_subset_jetBoxOpen)
  have hmem : (c, (0:ℝ)) ∈ jetBox c d R := ⟨⟨le_rfl, hcd⟩, ⟨by linarith, by linarith⟩⟩
  exact ⟨M, fun k => le_trans (norm_nonneg _) (hM k (c, 0) hmem), fun k p hp => hM k p hp⟩

/-- The Lipschitz bound on `p ↦ iteratedFDeriv ℝ k Φ p` over the box, with constant given by the
`(k+1)`-st `iteratedFDeriv` bound. -/
theorem norm_iteratedFDeriv_sub_le (Φ : ℝ × ℝ → ℝ) {c d R : ℝ}
    (hΦ : ContDiffOn ℝ ((⊤ : ℕ∞) : ℕ∞ω) Φ (jetBoxOpen c d R))
    {M : ℕ → ℝ} (hM : ∀ k, ∀ p ∈ jetBox c d R, ‖iteratedFDeriv ℝ k Φ p‖ ≤ M k)
    (k : ℕ) {p p' : ℝ × ℝ} (hp : p ∈ jetBox c d R) (hp' : p' ∈ jetBox c d R) :
    ‖iteratedFDeriv ℝ k Φ p - iteratedFDeriv ℝ k Φ p'‖ ≤ M (k + 1) * ‖p - p'‖ := by
  have hconv : Convex ℝ (jetBox c d R) := (convex_Icc _ _).prod (convex_Icc _ _)
  refine Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (s := jetBox c d R)
    (f := fun p : ℝ × ℝ => iteratedFDeriv ℝ k Φ p) (C := M (k + 1)) (x := p') (y := p)
    (fun q hq => ?_) (fun q hq => ?_) hconv hp' hp
  · have hqmem : q ∈ jetBoxOpen c d R := jetBox_subset_jetBoxOpen hq
    have hmm : (1 : ℕ∞ω) + (↑k : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω) := by
      have hcast : (1 : ℕ∞ω) + (↑k : ℕ∞ω) = ((k + 1 : ℕ) : ℕ∞ω) := by push_cast; ring
      rw [hcast]; exact coe_nat_le_infty (k + 1)
    have hcd : ContDiffAt ℝ (1 : ℕ∞ω) (fun p : ℝ × ℝ => iteratedFDeriv ℝ k Φ p) q :=
      (hΦ.contDiffAt ((isOpen_jetBoxOpen c d R).mem_nhds hqmem)).iteratedFDeriv_right
        (i := k) (m := 1) hmm
    exact hcd.differentiableAt one_ne_zero
  · simpa only [norm_fderiv_iteratedFDeriv (𝕜 := ℝ) (f := Φ) (n := k) (x := q)]
      using hM (k + 1) q hq

/-- The identity part of the jet is bounded by `max |x| 1`. -/
lemma abs_iteratedDeriv_id_le (k : ℕ) (x : ℝ) :
    |iteratedDeriv k (fun u : ℝ => u) x| ≤ max |x| 1 := by
  rcases Nat.eq_zero_or_pos k with h0 | h0
  · subst h0; simp only [iteratedDeriv_zero]; exact le_max_left _ _
  · rcases eq_or_lt_of_le (show 1 ≤ k by omega) with h1 | h1
    · subst h1
      rw [show (fun u : ℝ => u) = id from rfl, iteratedDeriv_id]
      norm_num
    · have h2 : 2 ≤ k := h1
      rw [show (fun u : ℝ => u) = id from rfl, iteratedDeriv_id]
      simp only [if_neg (by omega : ¬ k = 0), if_neg (by omega : ¬ k = 1), abs_zero]
      exact le_trans (by norm_num : (0:ℝ) ≤ 1) (le_max_right |x| 1)

/-- The jet coordinate at `x` is bounded by `J`, whenever `J` dominates `|c|`, `|d|`, `1`, `R`,
`x ∈ [c,d]`, `δ ≤ R` and the jet of `h` up to order `i` is bounded by `δ`. -/
lemma jet_pair_bound {c d R δ J x : ℝ} {h : ℝ → ℝ} {i k : ℕ}
    (hx : x ∈ Set.Icc c d) (hcJ : |c| ≤ J) (hdJ : |d| ≤ J) (h1J : 1 ≤ J) (hRJ : R ≤ J)
    (hδR : δ ≤ R) (hjet : ∀ j ≤ i, ∀ u ∈ Set.Icc c d, |iteratedDeriv j h u| ≤ δ)
    (hk : k ≤ i) :
    ‖(iteratedDeriv k (fun u : ℝ => u) x, iteratedDeriv k h x)‖ ≤ J := by
  have hxmax : |x| ≤ max |c| |d| := by
    refine abs_le.mpr ⟨?_, ?_⟩
    · have h1 : -(|c|) ≤ c := neg_abs_le c
      have h3 : -(max |c| |d|) ≤ -|c| := neg_le_neg (le_max_left |c| |d|)
      linarith [hx.1]
    · have h2 : d ≤ max |c| |d| := le_trans (le_abs_self d) (le_max_right _ _)
      linarith [hx.2]
  have hxJ : |x| ≤ J := le_trans hxmax (max_le hcJ hdJ)
  rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
  refine max_le ?_ ?_
  · refine le_trans (abs_iteratedDeriv_id_le k x) ?_
    exact max_le hxJ h1J
  · exact le_trans (hjet k hk x hx) (le_trans hδR hRJ)

/-! ## Uniform bounds for the composite -/

/-- **Basic uniform bound.**  If `Φ` is smooth on a neighbourhood of the box, and `h` maps `[c,d]`
into `[-R,R]` with all its derivatives up to order `i` bounded by `δ ≤ R` there, then the `i`-th
derivative of the composite `u ↦ Φ (u, h u)` on `[c,d]` is bounded by a constant depending only on
`Φ`, `i` and the box. -/
theorem exists_bound_comp_pair (i : ℕ) {Φ : ℝ × ℝ → ℝ} {c d R : ℝ} (hcd : c ≤ d) (hR : 0 < R)
    (hΦ : ContDiffOn ℝ ((⊤ : ℕ∞) : ℕ∞ω) Φ (jetBoxOpen c d R)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (h : ℝ → ℝ) (δ : ℝ), 0 ≤ δ → δ ≤ R →
      ContDiff ℝ (⊤ : ℕ∞) h →
      (∀ j ≤ i, ∀ u ∈ Set.Icc c d, |iteratedDeriv j h u| ≤ δ) →
      ∀ x ∈ Set.Icc c d, |iteratedDeriv i (fun u : ℝ => Φ (u, h u)) x| ≤ C := by
  obtain ⟨M, hM0, hM⟩ := exists_bound_iteratedFDeriv Φ hcd hR.le hΦ
  set J := max (max |c| |d|) (max 1 R) with hJ
  have hJ0 : 0 ≤ J := le_trans (by norm_num : (0:ℝ) ≤ 1)
    (le_trans (le_max_left 1 R) (le_max_right (max |c| |d|) (max 1 R)))
  have hcJ : |c| ≤ J := le_trans (le_max_left |c| |d|) (le_max_left _ _)
  have hdJ : |d| ≤ J := le_trans (le_max_right |c| |d|) (le_max_left _ _)
  have h1J : 1 ≤ J := le_trans (le_max_left 1 R) (le_max_right _ _)
  have hRJ : R ≤ J := le_trans (le_max_right 1 R) (le_max_right _ _)
  refine ⟨∑ c' : OrderedFinpartition i, M c'.length * J ^ c'.length, ?_, ?_⟩
  · exact Finset.sum_nonneg fun c' _ => mul_nonneg (hM0 _) (pow_nonneg hJ0 _)
  · intro h δ hδ hδR hh hjet x hx
    have hδR' : |h x| ≤ R := by
      have h1 := hjet 0 (Nat.zero_le i) x hx
      simp only [iteratedDeriv_zero] at h1
      exact le_trans h1 hδR
    have hxbox : (x, h x) ∈ jetBox c d R := ⟨hx, abs_le.mp hδR'⟩
    rw [iteratedDeriv_comp_pair i Φ h x
      (hΦ.contDiffAt ((isOpen_jetBoxOpen c d R).mem_nhds (jetBox_subset_jetBoxOpen hxbox)))
      (hh.contDiffAt)]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine Finset.sum_le_sum fun c' _ => ?_
    have hpart : ∀ j : Fin c'.length, c'.partSize j ≤ i := fun j => c'.partSize_le j
    calc |(iteratedFDeriv ℝ c'.length Φ (x, h x))
            (fun j => (iteratedDeriv (c'.partSize j) (fun u : ℝ => u) x,
                       iteratedDeriv (c'.partSize j) h x))|
        ≤ ‖iteratedFDeriv ℝ c'.length Φ (x, h x)‖ *
            ∏ j, ‖(iteratedDeriv (c'.partSize j) (fun u : ℝ => u) x,
                   iteratedDeriv (c'.partSize j) h x)‖ := by
          simpa only [Real.norm_eq_abs] using
            ContinuousMultilinearMap.le_opNorm (iteratedFDeriv ℝ c'.length Φ (x, h x))
              (fun j => (iteratedDeriv (c'.partSize j) (fun u : ℝ => u) x,
                         iteratedDeriv (c'.partSize j) h x))
      _ ≤ M c'.length * ∏ _j : Fin c'.length, J := by
          refine mul_le_mul (hM c'.length (x, h x) hxbox)
            (Finset.prod_le_prod₀ (fun j _ => norm_nonneg _) (fun j _ => ?_))
            (Finset.prod_nonneg fun j _ => norm_nonneg _) (hM0 _)
          exact jet_pair_bound hx hcJ hdJ h1J hRJ hδR hjet (hpart j)
      _ = M c'.length * J ^ c'.length := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- **Uniform smallness of the difference.**  Under the same hypotheses, the `i`-th derivative of
the composite `u ↦ Φ (u, h u)` differs from that of `u ↦ Φ (u, 0)` by at most `C δ`, with `C`
depending only on `Φ`, `i` and the box. -/
theorem exists_bound_comp_pair_sub (i : ℕ) {Φ : ℝ × ℝ → ℝ} {c d R : ℝ} (hcd : c ≤ d) (hR : 0 < R)
    (hΦ : ContDiffOn ℝ ((⊤ : ℕ∞) : ℕ∞ω) Φ (jetBoxOpen c d R)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (h : ℝ → ℝ) (δ : ℝ), 0 ≤ δ → δ ≤ 1 → δ ≤ R →
      ContDiff ℝ (⊤ : ℕ∞) h →
      (∀ j ≤ i, ∀ u ∈ Set.Icc c d, |iteratedDeriv j h u| ≤ δ) →
      ∀ x ∈ Set.Icc c d,
        |iteratedDeriv i (fun u : ℝ => Φ (u, h u)) x -
          iteratedDeriv i (fun u : ℝ => Φ (u, 0)) x| ≤ C * δ := by
  obtain ⟨M, hM0, hM⟩ := exists_bound_iteratedFDeriv Φ hcd hR.le hΦ
  set J := max (max |c| |d|) (max 1 R) with hJ
  have hJ0 : 0 ≤ J := le_trans (by norm_num : (0:ℝ) ≤ 1)
    (le_trans (le_max_left 1 R) (le_max_right (max |c| |d|) (max 1 R)))
  have hJ1 : 1 ≤ J := le_trans (le_max_left 1 R) (le_max_right _ _)
  have hcJ : |c| ≤ J := le_trans (le_max_left |c| |d|) (le_max_left _ _)
  have hdJ : |d| ≤ J := le_trans (le_max_right |c| |d|) (le_max_left _ _)
  have hRJ : R ≤ J := le_trans (le_max_right 1 R) (le_max_right _ _)
  refine ⟨∑ c' : OrderedFinpartition i,
      (M (c'.length + 1) * J ^ c'.length + M c'.length * (c'.length : ℝ) * J ^ (c'.length - 1)),
    ?_, ?_⟩
  · refine Finset.sum_nonneg fun c' _ => add_nonneg ?_ ?_
    · exact mul_nonneg (hM0 _) (pow_nonneg hJ0 _)
    · exact mul_nonneg (mul_nonneg (hM0 _) (Nat.cast_nonneg _)) (pow_nonneg hJ0 _)
  · intro h δ hδ hδ1 hδR hh hjet x hx
    have hδR' : |h x| ≤ R := by
      have h1 := hjet 0 (Nat.zero_le i) x hx
      simp only [iteratedDeriv_zero] at h1
      exact le_trans h1 hδR
    have hxbox : (x, h x) ∈ jetBox c d R := ⟨hx, abs_le.mp hδR'⟩
    have hxbox0 : (x, (0:ℝ)) ∈ jetBox c d R := ⟨hx, ⟨by linarith, by linarith⟩⟩
    rw [iteratedDeriv_comp_pair i Φ h x
        (hΦ.contDiffAt ((isOpen_jetBoxOpen c d R).mem_nhds (jetBox_subset_jetBoxOpen hxbox)))
        (hh.contDiffAt),
      iteratedDeriv_comp_pair i Φ (fun _ => 0) x
        (hΦ.contDiffAt ((isOpen_jetBoxOpen c d R).mem_nhds (jetBox_subset_jetBoxOpen hxbox0)))
        contDiffAt_const]
    rw [← Finset.sum_sub_distrib]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun c' _ => ?_
    set k := c'.length with hk
    have hpart : ∀ j : Fin c'.length, c'.partSize j ≤ i := fun j => c'.partSize_le j
    -- the two jets
    set v : Fin c'.length → ℝ × ℝ := fun j =>
      (iteratedDeriv (c'.partSize j) (fun u : ℝ => u) x, iteratedDeriv (c'.partSize j) h x) with hv
    set w : Fin c'.length → ℝ × ℝ := fun j =>
      (iteratedDeriv (c'.partSize j) (fun u : ℝ => u) x,
        iteratedDeriv (c'.partSize j) (fun _ => (0:ℝ)) x) with hw
    have hzero : ∀ (j : ℕ) (u : ℝ), iteratedDeriv j (fun _ : ℝ => (0:ℝ)) u = 0 := by
      intro j u
      rcases Nat.eq_zero_or_pos j with h0 | h0
      · subst h0; simp
      · rw [iteratedDeriv_const]; simp [ne_of_gt h0]
    have hvJ : ‖v‖ ≤ J := (pi_norm_le_iff_of_nonneg hJ0).mpr fun j =>
      jet_pair_bound hx hcJ hdJ hJ1 hRJ hδR hjet (hpart j)
    have hwJ : ‖w‖ ≤ J := (pi_norm_le_iff_of_nonneg hJ0).mpr fun j => by
      have hcomp : w j = (iteratedDeriv (c'.partSize j) (fun u : ℝ => u) x,
          iteratedDeriv (c'.partSize j) (fun _ : ℝ => (0:ℝ)) x) := by
        simp only [hw]
      have hxmax : |x| ≤ max |c| |d| := by
        refine abs_le.mpr ⟨?_, ?_⟩
        · have h1 : -(|c|) ≤ c := neg_abs_le c
          have h3 : -(max |c| |d|) ≤ -|c| := neg_le_neg (le_max_left |c| |d|)
          linarith [hx.1]
        · have h2 : d ≤ max |c| |d| := le_trans (le_abs_self d) (le_max_right _ _)
          linarith [hx.2]
      have hid : |iteratedDeriv (c'.partSize j) (fun u : ℝ => u) x| ≤ J :=
        le_trans (abs_iteratedDeriv_id_le _ x) (max_le (le_trans hxmax (max_le hcJ hdJ)) hJ1)
      rw [hcomp, Prod.norm_def, hzero, norm_zero, Real.norm_eq_abs]
      exact max_le hid hJ0
    have hvw : ‖v - w‖ ≤ δ := (pi_norm_le_iff_of_nonneg hδ).mpr fun j => by
      have hcomp : (v - w) j = (0, iteratedDeriv (c'.partSize j) h x) := by
        simp only [Pi.sub_apply, hv, hw, hzero, sub_zero, Prod.mk_sub_mk, sub_self]
      rw [hcomp, Prod.norm_def, norm_zero, max_eq_right (norm_nonneg _), Real.norm_eq_abs]
      exact hjet (c'.partSize j) (hpart j) x hx
    have hA0 : ‖iteratedFDeriv ℝ c'.length Φ (x, (0:ℝ))‖ ≤ M c'.length := hM _ _ hxbox0
    have hAh : ‖iteratedFDeriv ℝ c'.length Φ (x, h x)‖ ≤ M c'.length := hM _ _ hxbox
    have hlip : ‖iteratedFDeriv ℝ c'.length Φ (x, h x) -
        iteratedFDeriv ℝ c'.length Φ (x, (0:ℝ))‖ ≤ M (c'.length + 1) * |h x| := by
      have h1 := norm_iteratedFDeriv_sub_le Φ hΦ hM c'.length hxbox hxbox0
      have hdist : ‖(x, h x) - (x, (0:ℝ))‖ = |h x| := by
        rw [Prod.norm_def, Prod.mk_sub_mk, sub_self, norm_zero, max_eq_right (norm_nonneg _),
          Real.norm_eq_abs, sub_zero]
      simpa only [hdist] using h1
    have hhxδ : |h x| ≤ δ := hjet 0 (Nat.zero_le i) x hx
    have hAh : ‖iteratedFDeriv ℝ c'.length Φ (x, h x)‖ ≤ M c'.length := hM _ _ hxbox
    have hk0 : (0 : ℝ) ≤ (c'.length : ℝ) := Nat.cast_nonneg _
    have hmax : max ‖v‖ ‖w‖ ≤ J := max_le hvJ hwJ
    have hp : (max ‖v‖ ‖w‖) ^ (c'.length - 1) ≤ J ^ (c'.length - 1) :=
      pow_le_pow_left₀ (le_max_of_le_left (norm_nonneg v)) hmax _
    -- split the difference
    have hsplit : (iteratedFDeriv ℝ c'.length Φ (x, h x)) v -
          (iteratedFDeriv ℝ c'.length Φ (x, (0:ℝ))) w =
        ((iteratedFDeriv ℝ c'.length Φ (x, h x)) v -
          (iteratedFDeriv ℝ c'.length Φ (x, (0:ℝ))) v) +
        ((iteratedFDeriv ℝ c'.length Φ (x, (0:ℝ))) v -
          (iteratedFDeriv ℝ c'.length Φ (x, (0:ℝ))) w) := by abel
    rw [hsplit]
    refine le_trans (abs_add_le _ _) ?_
    have ht1 : ‖(iteratedFDeriv ℝ c'.length Φ (x, h x)) v -
        (iteratedFDeriv ℝ c'.length Φ (x, (0:ℝ))) v‖ ≤
        M (c'.length + 1) * J ^ c'.length * δ := by
      have h1 : (iteratedFDeriv ℝ c'.length Φ (x, h x)) v -
          (iteratedFDeriv ℝ c'.length Φ (x, (0:ℝ))) v =
          (iteratedFDeriv ℝ c'.length Φ (x, h x) -
            iteratedFDeriv ℝ c'.length Φ (x, (0:ℝ))) v := by
        rw [ContinuousMultilinearMap.sub_apply]
      rw [h1]
      calc ‖(iteratedFDeriv ℝ c'.length Φ (x, h x) -
              iteratedFDeriv ℝ c'.length Φ (x, (0:ℝ))) v‖
          ≤ ‖iteratedFDeriv ℝ c'.length Φ (x, h x) -
              iteratedFDeriv ℝ c'.length Φ (x, (0:ℝ))‖ * ∏ j, ‖v j‖ :=
            ContinuousMultilinearMap.le_opNorm _ _
        _ ≤ (M (c'.length + 1) * |h x|) * J ^ c'.length := by
            refine mul_le_mul hlip ?_ (Finset.prod_nonneg fun j _ => norm_nonneg _)
              (mul_nonneg (hM0 _) (abs_nonneg _))
            calc ∏ j, ‖v j‖ ≤ ∏ _j : Fin c'.length, J :=
                  Finset.prod_le_prod₀ (fun j _ => norm_nonneg _)
                    (fun j _ => (pi_norm_le_iff_of_nonneg hJ0).mp hvJ j)
              _ = J ^ c'.length := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        _ ≤ (M (c'.length + 1) * δ) * J ^ c'.length :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hhxδ (hM0 _)) (pow_nonneg hJ0 _)
        _ = M (c'.length + 1) * J ^ c'.length * δ := by ring
    have ht2 : ‖(iteratedFDeriv ℝ c'.length Φ (x, (0:ℝ))) v -
        (iteratedFDeriv ℝ c'.length Φ (x, (0:ℝ))) w‖ ≤
        M c'.length * (c'.length : ℝ) * J ^ (c'.length - 1) * δ := by
      have h2 : ‖(iteratedFDeriv ℝ c'.length Φ (x, (0:ℝ))) v -
          (iteratedFDeriv ℝ c'.length Φ (x, (0:ℝ))) w‖ ≤
          ‖iteratedFDeriv ℝ c'.length Φ (x, (0:ℝ))‖ * (c'.length : ℝ) *
            (max ‖v‖ ‖w‖) ^ (c'.length - 1) * ‖v - w‖ := by
        simpa only [Fintype.card_fin] using
          (iteratedFDeriv ℝ c'.length Φ (x, (0:ℝ))).norm_image_sub_le v w
      refine le_trans h2 ?_
      calc ‖iteratedFDeriv ℝ c'.length Φ (x, (0:ℝ))‖ * (c'.length : ℝ) *
            (max ‖v‖ ‖w‖) ^ (c'.length - 1) * ‖v - w‖
          ≤ M c'.length * (c'.length : ℝ) * J ^ (c'.length - 1) * δ := by
            refine mul_le_mul ?_ hvw (norm_nonneg _)
              (mul_nonneg (mul_nonneg (hM0 _) hk0) (pow_nonneg hJ0 _))
            exact mul_le_mul (mul_le_mul hA0 le_rfl hk0 (hM0 _)) hp
              (pow_nonneg (le_max_of_le_left (norm_nonneg v)) _) (mul_nonneg (hM0 _) hk0)
        _ = M c'.length * (c'.length : ℝ) * J ^ (c'.length - 1) * δ := rfl
    refine le_trans (add_le_add ht1 ht2) (le_of_eq ?_)
    ring

end

end Work.OddVolterra.Existence
