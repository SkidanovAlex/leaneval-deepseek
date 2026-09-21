import Mathlib
import Submission.Work.OddVolterra.Existence.JetBound

/-!
# Uniform smallness of `∂^i_u Φ (u, h u, t)` versus `∂^i_u Φ (u, 0, t)`

Given a `C^∞` function `Φ` on an open set `U ⊆ ℝ³` which contains the box
`[c,d] × [-R,R] × [-p,p]`, we produce a constant `C ≥ 0` such that for every
`C^∞` function `h : ℝ → ℝ` whose derivatives up to order `i` are bounded by `δ`
on `[c,d]` (with `0 ≤ δ`, `δ ≤ 1`, `δ ≤ R`), the difference of the `i`-th
`u`-derivatives of `u ↦ Φ (u, h u, t)` and `u ↦ Φ (u, 0, t)` is bounded by
`C * δ`, uniformly in `x ∈ [c,d]` and `t ∈ [-p,p]`.

The proof follows the pattern of `JetBound.lean`: Faà di Bruno's formula expands
the `i`-th derivative of the composite `u ↦ Φ (u, h u, t)` as a finite sum over
ordered set partitions of `{1,…,i}`, involving the `iteratedFDeriv`'s of `Φ` at
`(x, h x, t)` and the jet of the graph curve `u ↦ (u, h u, t)`.  Bounding the
`iteratedFDeriv`'s of `Φ` on the compact box and telescoping the two expansions
(for `h` and for `0`) produces the explicit factor `δ`.
-/

namespace Work.OddVolterra.Existence

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

noncomputable section

/-! ## The box and its compactness -/

/-- The compact box `[c,d] × [-R,R] × [-p,p] ⊆ ℝ³` on which everything is uniform. -/
def box3 (c d R p : ℝ) : Set (ℝ × ℝ × ℝ) :=
  Set.Icc c d ×ˢ Set.Icc (-R) R ×ˢ Set.Icc (-p) p

lemma isCompact_box3 (c d R p : ℝ) : IsCompact (box3 c d R p) :=
  isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)

/-! ## Componentwise jets of the graph curve `u ↦ (u, h u, t)` -/

/-- The `k`-th iterated derivative of a pair-valued function is componentwise. -/
lemma iteratedDeriv_pair_curry {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (k : ℕ) (f : ℝ → F) (g : ℝ → G) (x : ℝ)
    (hf : ContDiffAt ℝ ((⊤ : ℕ∞) : ℕ∞ω) f x) (hg : ContDiffAt ℝ ((⊤ : ℕ∞) : ℕ∞ω) g x) :
    iteratedDeriv k (fun u : ℝ => (f u, g u)) x = (iteratedDeriv k f x, iteratedDeriv k g x) := by
  simp only [iteratedDeriv]
  rw [iteratedFDeriv_prodMk hf hg (coe_nat_le_infty k)]
  rfl

/-- The `k`-th iterated derivative of the graph curve `u ↦ (u, h u, t)` is componentwise. -/
lemma iteratedDeriv_triple (k : ℕ) {h : ℝ → ℝ} {t x : ℝ}
    (hh : ContDiffAt ℝ ((⊤ : ℕ∞) : ℕ∞ω) h x) :
    iteratedDeriv k (fun u : ℝ => (u, h u, t)) x =
      (iteratedDeriv k (fun u : ℝ => u) x,
        (iteratedDeriv k h x, iteratedDeriv k (fun _ : ℝ => t) x)) := by
  rw [iteratedDeriv_pair_curry k (fun u : ℝ => u) (fun u : ℝ => (h u, t)) x contDiffAt_id
    (hh.prodMk contDiffAt_const)]
  congr 1
  exact iteratedDeriv_pair_curry k h (fun _ : ℝ => t) x hh contDiffAt_const

/-- Faà di Bruno's formula for the composite `u ↦ Φ (u, h u, t)`. -/
theorem iteratedDeriv_comp_triple (i : ℕ) (Φ : ℝ × ℝ × ℝ → ℝ) (h : ℝ → ℝ) (t x : ℝ)
    (hΦ : ContDiffAt ℝ ((⊤ : ℕ∞) : ℕ∞ω) Φ (x, h x, t))
    (hh : ContDiffAt ℝ ((⊤ : ℕ∞) : ℕ∞ω) h x) :
    iteratedDeriv i (fun u : ℝ => Φ (u, h u, t)) x =
      ∑ c : OrderedFinpartition i,
        (iteratedFDeriv ℝ c.length Φ (x, h x, t))
          (fun j => (iteratedDeriv (c.partSize j) (fun u : ℝ => u) x,
            (iteratedDeriv (c.partSize j) h x,
              iteratedDeriv (c.partSize j) (fun _ : ℝ => t) x))) := by
  have h1 := iteratedDeriv_vcomp_eq_sum_orderedFinpartition (𝕜 := ℝ)
    (g := fun p : ℝ × ℝ × ℝ => Φ p) (f := fun u : ℝ => (u, h u, t)) (x := x) (i := i)
    (n := ((⊤ : ℕ∞) : ℕ∞ω)) hΦ (contDiffAt_id.prodMk (hh.prodMk contDiffAt_const))
    (coe_nat_le_infty i)
  show iteratedDeriv i (Φ ∘ (fun u : ℝ => (u, h u, t))) x = _
  rw [h1]
  refine Finset.sum_congr rfl fun c _ => ?_
  congr 1
  funext j
  exact iteratedDeriv_triple (c.partSize j) hh

/-! ## Elementary jet bounds -/

/-- A triple of reals, each bounded in absolute value by `J`, has norm at most `J`. -/
lemma norm_prod_three_le {a b e J : ℝ} (ha : |a| ≤ J) (hb : |b| ≤ J) (he : |e| ≤ J) :
    ‖(a, b, e)‖ ≤ J := by
  rw [Prod.norm_def, Real.norm_eq_abs, Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
  exact max_le ha (max_le hb he)

/-- The jet of a constant is bounded by `max |t| 1`. -/
lemma abs_iteratedDeriv_const_le (k : ℕ) (t x : ℝ) :
    |iteratedDeriv k (fun _ : ℝ => t) x| ≤ max |t| 1 := by
  rw [iteratedDeriv_const]
  split_ifs with hk
  · exact le_max_left _ _
  · simp only [abs_zero]
    exact le_trans (by norm_num : (0 : ℝ) ≤ 1) (le_max_right _ _)

/-! ## Uniform bounds for the `iteratedFDeriv`'s of `Φ` on the box -/

/-- Supremum-type bounds for the `iteratedFDeriv`'s of `Φ` over the compact box. -/
lemma exists_bound_iteratedFDeriv3 (Φ : ℝ × ℝ × ℝ → ℝ) {c d R p : ℝ} {U : Set (ℝ × ℝ × ℝ)}
    (hU : IsOpen U) (hboxU : box3 c d R p ⊆ U)
    (hΦ : ContDiffOn ℝ ((⊤ : ℕ∞) : ℕ∞ω) Φ U) :
    ∃ M : ℕ → ℝ, (∀ k, 0 ≤ M k) ∧ ∀ k, ∀ q ∈ box3 c d R p, ‖iteratedFDeriv ℝ k Φ q‖ ≤ M k := by
  have hcont : ∀ k : ℕ, ContinuousOn (fun q : ℝ × ℝ × ℝ => iteratedFDeriv ℝ k Φ q) U := fun k =>
    ContinuousOn.continuousOn_iteratedFDeriv hΦ hU (coe_nat_le_infty k)
  choose M0 hM0 using fun k : ℕ =>
    (isCompact_box3 c d R p).exists_bound_of_continuousOn ((hcont k).mono hboxU)
  exact ⟨fun k => max (M0 k) 0, fun k => le_max_right _ _,
    fun k q hq => le_trans (hM0 k q hq) (le_max_left _ _)⟩

/-- The Lipschitz bound for `q ↦ iteratedFDeriv ℝ k Φ q` over the convex box. -/
lemma norm_iteratedFDeriv_sub_le3 (Φ : ℝ × ℝ × ℝ → ℝ) {c d R p : ℝ} {U : Set (ℝ × ℝ × ℝ)}
    (hU : IsOpen U) (hboxU : box3 c d R p ⊆ U)
    (hΦ : ContDiffOn ℝ ((⊤ : ℕ∞) : ℕ∞ω) Φ U)
    {M : ℕ → ℝ} (hM : ∀ k, ∀ q ∈ box3 c d R p, ‖iteratedFDeriv ℝ k Φ q‖ ≤ M k)
    (k : ℕ) {q q' : ℝ × ℝ × ℝ} (hq : q ∈ box3 c d R p) (hq' : q' ∈ box3 c d R p) :
    ‖iteratedFDeriv ℝ k Φ q - iteratedFDeriv ℝ k Φ q'‖ ≤ M (k + 1) * ‖q - q'‖ := by
  have hconv : Convex ℝ (box3 c d R p) :=
    (convex_Icc _ _).prod ((convex_Icc _ _).prod (convex_Icc _ _))
  refine Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (s := box3 c d R p)
    (f := fun q : ℝ × ℝ × ℝ => iteratedFDeriv ℝ k Φ q) (C := M (k + 1)) (x := q') (y := q)
    (fun q hq => ?_) (fun q hq => ?_) hconv hq' hq
  · have hqU : q ∈ U := hboxU hq
    have hmm : (1 : ℕ∞ω) + (↑k : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω) := by
      have hcast : (1 : ℕ∞ω) + (↑k : ℕ∞ω) = ((k + 1 : ℕ) : ℕ∞ω) := by push_cast; ring
      rw [hcast]; exact coe_nat_le_infty (k + 1)
    have hcd : ContDiffAt ℝ (1 : ℕ∞ω) (fun q : ℝ × ℝ × ℝ => iteratedFDeriv ℝ k Φ q) q :=
      (hΦ.contDiffAt (hU.mem_nhds hqU)).iteratedFDeriv_right (i := k) (m := 1) hmm
    exact hcd.differentiableAt one_ne_zero
  · simpa only [norm_fderiv_iteratedFDeriv (𝕜 := ℝ) (f := Φ) (n := k) (x := q)]
      using hM (k + 1) q hq

/-! ## The main estimate -/

theorem exists_bound_comp_pair_sub_param (i : ℕ) {Φ : ℝ × ℝ × ℝ → ℝ} {c d R p : ℝ}
    {U : Set (ℝ × ℝ × ℝ)} (hU : IsOpen U)
    (hboxU : Set.Icc c d ×ˢ Set.Icc (-R) R ×ˢ Set.Icc (-p) p ⊆ U)
    (hΦ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ U)
    (hcd : c ≤ d) (hR : 0 < R) (hp : 0 ≤ p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (h : ℝ → ℝ) (δ : ℝ), 0 ≤ δ → δ ≤ 1 → δ ≤ R →
      ContDiff ℝ (⊤ : ℕ∞) h →
      (∀ j ≤ i, ∀ u ∈ Set.Icc c d, |iteratedDeriv j h u| ≤ δ) →
      ∀ x ∈ Set.Icc c d, ∀ t ∈ Set.Icc (-p) p,
        |iteratedDeriv i (fun u : ℝ => Φ (u, h u, t)) x -
         iteratedDeriv i (fun u : ℝ => Φ (u, 0, t)) x| ≤ C * δ := by
  have hbox : box3 c d R p ⊆ U := hboxU
  obtain ⟨M, hM0, hM⟩ := exists_bound_iteratedFDeriv3 Φ hU hbox hΦ
  set J := max (max |c| |d|) (max (max 1 R) (max 1 p)) with hJ
  have hJ1 : 1 ≤ J := by
    rw [hJ]
    exact le_trans (le_max_left 1 R)
      (le_trans (le_max_left (max 1 R) (max 1 p)) (le_max_right _ _))
  have hJ0 : 0 ≤ J := le_trans (by norm_num : (0 : ℝ) ≤ 1) hJ1
  have hcJ : |c| ≤ J := by rw [hJ]; exact le_trans (le_max_left |c| |d|) (le_max_left _ _)
  have hdJ : |d| ≤ J := by rw [hJ]; exact le_trans (le_max_right |c| |d|) (le_max_left _ _)
  have hRJ : R ≤ J := by
    rw [hJ]
    exact le_trans (le_max_right 1 R)
      (le_trans (le_max_left (max 1 R) (max 1 p)) (le_max_right _ _))
  have hpJ : p ≤ J := by
    rw [hJ]
    exact le_trans (le_max_right 1 p)
      (le_trans (le_max_right (max 1 R) (max 1 p)) (le_max_right _ _))
  refine ⟨∑ c' : OrderedFinpartition i,
      (M (c'.length + 1) * J ^ c'.length + M c'.length * (c'.length : ℝ) * J ^ (c'.length - 1)),
    ?_, ?_⟩
  · refine Finset.sum_nonneg fun c' _ => add_nonneg ?_ ?_
    · exact mul_nonneg (hM0 _) (pow_nonneg hJ0 _)
    · exact mul_nonneg (mul_nonneg (hM0 _) (Nat.cast_nonneg _)) (pow_nonneg hJ0 _)
  · intro h δ hδ hδ1 hδR hh hjet x hx t ht
    have hht : |h x| ≤ δ := by
      have h1 := hjet 0 (Nat.zero_le i) x hx
      simpa only [iteratedDeriv_zero] using h1
    have hhR : |h x| ≤ R := le_trans hht hδR
    have hxbox : (x, h x, t) ∈ box3 c d R p := ⟨hx, abs_le.mp hhR, ht⟩
    have hxbox0 : (x, (0 : ℝ), t) ∈ box3 c d R p := ⟨hx, ⟨by linarith, by linarith⟩, ht⟩
    have hxmax : |x| ≤ max |c| |d| := by
      refine abs_le.mpr ⟨?_, ?_⟩
      · have h1 : -(|c|) ≤ c := neg_abs_le c
        have h3 : -(max |c| |d|) ≤ -|c| := neg_le_neg (le_max_left |c| |d|)
        linarith [hx.1]
      · have h2 : d ≤ max |c| |d| := le_trans (le_abs_self d) (le_max_right _ _)
        linarith [hx.2]
    have hxJ : |x| ≤ J := by rw [hJ]; exact le_trans hxmax (le_max_left _ _)
    have htJ : |t| ≤ J := le_trans (abs_le.mpr ⟨ht.1, ht.2⟩) hpJ
    have hδJ : δ ≤ J := le_trans hδR hRJ
    have hΦat : ContDiffAt ℝ ((⊤ : ℕ∞) : ℕ∞ω) Φ (x, h x, t) :=
      hΦ.contDiffAt (hU.mem_nhds (hbox hxbox))
    have hΦat0 : ContDiffAt ℝ ((⊤ : ℕ∞) : ℕ∞ω) Φ (x, (0 : ℝ), t) :=
      hΦ.contDiffAt (hU.mem_nhds (hbox hxbox0))
    rw [iteratedDeriv_comp_triple i Φ h t x hΦat hh.contDiffAt,
      iteratedDeriv_comp_triple i Φ (fun _ : ℝ => (0 : ℝ)) t x hΦat0 contDiffAt_const]
    rw [← Finset.sum_sub_distrib]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun c' _ => ?_
    have hpart : ∀ j : Fin c'.length, c'.partSize j ≤ i := fun j => c'.partSize_le j
    have hzero : ∀ (j : ℕ) (u : ℝ), iteratedDeriv j (fun _ : ℝ => (0 : ℝ)) u = 0 := by
      intro j u
      rw [iteratedDeriv_const]
      split_ifs <;> simp
    set v : Fin c'.length → ℝ × ℝ × ℝ := fun j =>
      (iteratedDeriv (c'.partSize j) (fun u : ℝ => u) x,
        (iteratedDeriv (c'.partSize j) h x,
          iteratedDeriv (c'.partSize j) (fun _ : ℝ => t) x)) with hv
    set w : Fin c'.length → ℝ × ℝ × ℝ := fun j =>
      (iteratedDeriv (c'.partSize j) (fun u : ℝ => u) x,
        (iteratedDeriv (c'.partSize j) (fun _ : ℝ => (0 : ℝ)) x,
          iteratedDeriv (c'.partSize j) (fun _ : ℝ => t) x)) with hw
    have hvJ : ‖v‖ ≤ J := (pi_norm_le_iff_of_nonneg hJ0).mpr fun j =>
      norm_prod_three_le
        (le_trans (abs_iteratedDeriv_id_le _ x) (max_le hxJ hJ1))
        (le_trans (hjet (c'.partSize j) (hpart j) x hx) hδJ)
        (le_trans (abs_iteratedDeriv_const_le _ t x) (max_le htJ hJ1))
    have hwJ : ‖w‖ ≤ J := (pi_norm_le_iff_of_nonneg hJ0).mpr fun j =>
      norm_prod_three_le
        (le_trans (abs_iteratedDeriv_id_le _ x) (max_le hxJ hJ1))
        (by rw [hzero]; simpa using hJ0)
        (le_trans (abs_iteratedDeriv_const_le _ t x) (max_le htJ hJ1))
    have hvw : ‖v - w‖ ≤ δ := by
      rw [pi_norm_le_iff_of_nonneg hδ]
      intro j
      have hcomp : (v - w) j = (0, (iteratedDeriv (c'.partSize j) h x, (0 : ℝ))) := by
        rw [Pi.sub_apply, hv, hw]
        simp only [Prod.mk_sub_mk, sub_self, hzero, sub_zero]
      have hnorm : ‖(v - w) j‖ = |iteratedDeriv (c'.partSize j) h x| := by
        rw [hcomp, Prod.norm_def, norm_zero, Prod.norm_def, Real.norm_eq_abs, norm_zero]
        simp
      rw [hnorm]
      exact hjet (c'.partSize j) (hpart j) x hx
    have hA0 : ‖iteratedFDeriv ℝ c'.length Φ (x, (0 : ℝ), t)‖ ≤ M c'.length :=
      hM _ _ hxbox0
    have hAh : ‖iteratedFDeriv ℝ c'.length Φ (x, h x, t)‖ ≤ M c'.length := hM _ _ hxbox
    have hlip : ‖iteratedFDeriv ℝ c'.length Φ (x, h x, t) -
        iteratedFDeriv ℝ c'.length Φ (x, (0 : ℝ), t)‖ ≤ M (c'.length + 1) * |h x| := by
      have h1 := norm_iteratedFDeriv_sub_le3 Φ hU hbox hΦ hM c'.length hxbox hxbox0
      have hdist : ‖(x, h x, t) - (x, (0 : ℝ), t)‖ = |h x| := by
        have hsub : (x, h x, t) - (x, (0 : ℝ), t) = (0, (h x, (0 : ℝ))) := by
          simp only [Prod.mk_sub_mk, sub_self, hzero, sub_zero]
        rw [hsub, Prod.norm_def, norm_zero, Prod.norm_def, Real.norm_eq_abs, norm_zero]
        simp
      simpa only [hdist] using h1
    have hk0 : (0 : ℝ) ≤ (c'.length : ℝ) := Nat.cast_nonneg _
    have hmax : max ‖v‖ ‖w‖ ≤ J := max_le hvJ hwJ
    have hp : (max ‖v‖ ‖w‖) ^ (c'.length - 1) ≤ J ^ (c'.length - 1) :=
      pow_le_pow_left₀ (le_max_of_le_left (norm_nonneg v)) hmax _
    have hsplit : (iteratedFDeriv ℝ c'.length Φ (x, h x, t)) v -
          (iteratedFDeriv ℝ c'.length Φ (x, (0 : ℝ), t)) w =
        ((iteratedFDeriv ℝ c'.length Φ (x, h x, t)) v -
          (iteratedFDeriv ℝ c'.length Φ (x, (0 : ℝ), t)) v) +
        ((iteratedFDeriv ℝ c'.length Φ (x, (0 : ℝ), t)) v -
          (iteratedFDeriv ℝ c'.length Φ (x, (0 : ℝ), t)) w) := by abel
    rw [hsplit]
    refine le_trans (abs_add_le _ _) ?_
    have ht1 : ‖(iteratedFDeriv ℝ c'.length Φ (x, h x, t)) v -
        (iteratedFDeriv ℝ c'.length Φ (x, (0 : ℝ), t)) v‖ ≤
        M (c'.length + 1) * J ^ c'.length * δ := by
      have h1 : (iteratedFDeriv ℝ c'.length Φ (x, h x, t)) v -
          (iteratedFDeriv ℝ c'.length Φ (x, (0 : ℝ), t)) v =
          (iteratedFDeriv ℝ c'.length Φ (x, h x, t) -
            iteratedFDeriv ℝ c'.length Φ (x, (0 : ℝ), t)) v := by
        rw [ContinuousMultilinearMap.sub_apply]
      rw [h1]
      calc ‖(iteratedFDeriv ℝ c'.length Φ (x, h x, t) -
              iteratedFDeriv ℝ c'.length Φ (x, (0 : ℝ), t)) v‖
          ≤ ‖iteratedFDeriv ℝ c'.length Φ (x, h x, t) -
              iteratedFDeriv ℝ c'.length Φ (x, (0 : ℝ), t)‖ * ∏ j, ‖v j‖ :=
            ContinuousMultilinearMap.le_opNorm _ _
        _ ≤ (M (c'.length + 1) * |h x|) * J ^ c'.length := by
            refine mul_le_mul hlip ?_ (Finset.prod_nonneg fun j _ => norm_nonneg _)
              (mul_nonneg (hM0 _) (abs_nonneg _))
            calc ∏ j, ‖v j‖ ≤ ∏ _j : Fin c'.length, J :=
                  Finset.prod_le_prod₀ (fun j _ => norm_nonneg _)
                    (fun j _ => (pi_norm_le_iff_of_nonneg hJ0).mp hvJ j)
              _ = J ^ c'.length := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        _ ≤ (M (c'.length + 1) * δ) * J ^ c'.length :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hht (hM0 _)) (pow_nonneg hJ0 _)
        _ = M (c'.length + 1) * J ^ c'.length * δ := by ring
    have ht2 : ‖(iteratedFDeriv ℝ c'.length Φ (x, (0 : ℝ), t)) v -
        (iteratedFDeriv ℝ c'.length Φ (x, (0 : ℝ), t)) w‖ ≤
        M c'.length * (c'.length : ℝ) * J ^ (c'.length - 1) * δ := by
      have h2 : ‖(iteratedFDeriv ℝ c'.length Φ (x, (0 : ℝ), t)) v -
          (iteratedFDeriv ℝ c'.length Φ (x, (0 : ℝ), t)) w‖ ≤
          ‖iteratedFDeriv ℝ c'.length Φ (x, (0 : ℝ), t)‖ * (c'.length : ℝ) *
            (max ‖v‖ ‖w‖) ^ (c'.length - 1) * ‖v - w‖ := by
        simpa only [Fintype.card_fin] using
          (iteratedFDeriv ℝ c'.length Φ (x, (0 : ℝ), t)).norm_image_sub_le v w
      refine le_trans h2 ?_
      calc ‖iteratedFDeriv ℝ c'.length Φ (x, (0 : ℝ), t)‖ * (c'.length : ℝ) *
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
