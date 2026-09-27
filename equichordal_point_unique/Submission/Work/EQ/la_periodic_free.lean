import Mathlib
import Submission.Work.EQ.CycleDefs
import Submission.Work.EQ.DefsCore
import Submission.Work.EQ.StableTailDefs
import Submission.Work.EQ.component_shiftZ_invariant
import Submission.Work.EQ.LAFree
import Submission.Work.EQ.regComp_psi1_cocountable
import Submission.Work.EQ.chain_eq_candChain_of_tails
import Submission.Work.EQ.la_tail_bounds_free
import Submission.Work.EQ.la_datum_finite

/-! # Periodicity of the components of a descendant-free value, cycle-free

This is the statement `hP` required by `Work.EQ.LAFree.limit_analysis_of` (and by
`Work.EQ.la_regular_periodic`): every regular component of a value `c` with `‖c‖ ≤ 2ρ*` and no
descendant value is periodic under the shift `σ`.

The route here avoids `Work.EQ.regComp_finite` (which is stated in a file that imports
`limit_analysis`, and `Work.EQ.la_periodic_no_desc`, which imports
`Submission.Work.EQ.exists_compact_regular_cycle` — both would create import cycles):

* `Work.EQ.la_comp_finite_free`: **global** finiteness of the regular components of value `c`,
  obtained from `Work.EQ.la_annulus_components_finite` (finitely many components *meeting a given
  annulus*) together with `Work.EQ.regComp_psi1_cocountable` (every regular component projects onto
  `ℂ*` minus a countable set, hence meets every annulus of positive width);
* then the same finite-orbit argument as `Work.EQ.la_regular_periodic`: an injective self-map of a
  finite set has finite orbits. -/

namespace Work.EQ

open Complex Filter _root_.Topology

open scoped Topology

noncomputable section

/-- **A regular component meets every annulus of positive width.** -/
theorem la_meets_ann_of_countable {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (hr₁₂ : r₁ < r₂)
    {S : Set ChainData} {c : ℂ} (hS : IsRegComp a h S c) :
    ∃ q ∈ S, q.2.1 ∈ Ann r₁ r₂ := by
  obtain ⟨P, hPcount, hP⟩ := regComp_psi1_cocountable (a := a) (h := h) (r := r) ha0 ha1 hh
  have hdense : Dense (Pᶜ) := hPcount.dense_compl ℂ
  have hρ : (0 : ℝ) < (r₂ - r₁) / 2 := by linarith
  have hsub : Metric.ball (((r₁ + r₂) / 2 : ℝ) : ℂ) ((r₂ - r₁) / 2) ⊆ Ann r₁ r₂ := by
    intro z hz
    rw [Metric.mem_ball, dist_eq_norm] at hz
    have hmid : ‖(((r₁ + r₂) / 2 : ℝ) : ℂ)‖ = (r₁ + r₂) / 2 := by
      rw [Complex.norm_of_nonneg (by linarith)]
    have hlow : (r₁ + r₂) / 2 - ‖z‖ ≤ ‖z - (((r₁ + r₂) / 2 : ℝ) : ℂ)‖ := by
      have h := abs_norm_sub_norm_le (((r₁ + r₂) / 2 : ℝ) : ℂ) z
      rw [norm_sub_rev, hmid] at h
      exact le_trans (le_abs_self _) h
    have hup : ‖z‖ - (r₁ + r₂) / 2 ≤ ‖z - (((r₁ + r₂) / 2 : ℝ) : ℂ)‖ := by
      have h := abs_norm_sub_norm_le z (((r₁ + r₂) / 2 : ℝ) : ℂ)
      rw [hmid] at h
      exact le_trans (le_abs_self _) h
    exact ⟨by linarith, by linarith⟩
  obtain ⟨z, hzP, hzball⟩ := hdense.exists_mem_open Metric.isOpen_ball ⟨_, Metric.mem_ball_self hρ⟩
  have hzann : z ∈ Ann r₁ r₂ := hsub hzball
  have hz0 : z ≠ 0 := by
    intro hz
    have h1 := hzann.1
    rw [hz] at h1
    simp at h1
    linarith
  obtain ⟨q, hqS, hq⟩ := hP hS z hz0 hzP
  exact ⟨q, hqS, hq ▸ hzann⟩

/-- **Finitely many regular components of a descendant-free value meeting an annulus.**

The counting argument of `Work.EQ.LAFree.la_B_core` (B), with the tail bound applied to the constant
family of components and the datum-finiteness `Work.EQ.la_datum_finite`; the tail bound used is the
*value* form `Work.EQ.la_tail_bound_value_free`. -/
theorem la_finite_meeting_ann {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) (hpos : 0 < rhoStar a h) {c : ℂ} (hc : ‖c‖ ≤ 2 * rhoStar a h)
    (hnd : ∀ μ₁ ∈ CharSet a h, ∀ μ₂ ∈ CharSet a h, (μ₁ ≠ 1 ∨ μ₂ ≠ 1) →
      ∀ T : Set ChainData, ¬ IsRegComp a h T (c * μ₁ * μ₂)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (r₁ r₂ : ℝ), 0 < r₁ → r₁ < r₂ → r₂ < r → r₂ < δ →
      1 / eqLam a < r₂ / r₁ →
      {S : Set ChainData | IsRegComp a h S c ∧ ∃ q ∈ S, q.2.1 ∈ Ann r₁ r₂}.Finite := by
  obtain ⟨δ₁, hδ₁, hT⟩ := la_tail_bound_value_free (a := a) (h := h) (r := r) ha0 ha1 hh
  obtain ⟨δ₂, hδ₂, hD⟩ := la_datum_finite (a := a) (h := h) (r := r) ha0 ha1 hh hpos
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, ?_⟩
  intro r₁ r₂ hr₁ hr₁₂ hr₂r hr₂m hratio
  have hr₂δ₁ : r₂ < δ₁ := lt_of_lt_of_le hr₂m (min_le_left _ _)
  have hr₂δ₂ : r₂ < δ₂ := lt_of_lt_of_le hr₂m (min_le_right _ _)
  have hlam0 : 0 < eqLam a := div_pos (by linarith) (by linarith)
  have hlam1 : eqLam a < 1 := by rw [eqLam, div_lt_one (by linarith)]; linarith
  have hr₂ : 0 < r₂ := lt_trans hr₁ hr₁₂
  -- a depth `N` making the two smallness conditions of the datum input hold
  obtain ⟨N, hN₁, hN₂⟩ : ∃ N : ℕ, (eqLam a : ℝ) ^ N * r₂ < δ₂ ∧
      (eqLam a : ℝ) ^ N * (2 * rhoStar a h) / r₁ < δ₂ := by
    have hz : Tendsto (fun N : ℕ => (eqLam a) ^ N * max r₂ ((2 * rhoStar a h) / r₁)) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hlam0.le hlam1).mul_const
        (max r₂ ((2 * rhoStar a h) / r₁))
    have hpos2 : 0 < δ₂ := hδ₂
    obtain ⟨N, hN⟩ := (hz.eventually (isOpen_Iio.mem_nhds hpos2)).exists
    refine ⟨N, ?_, ?_⟩
    · exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left (le_max_left _ _) (pow_nonneg hlam0.le N)) hN
    · have h2 : (eqLam a) ^ N * ((2 * rhoStar a h) / r₁)
          ≤ (eqLam a) ^ N * max r₂ ((2 * rhoStar a h) / r₁) :=
        mul_le_mul_of_nonneg_left (le_max_right _ _) (pow_nonneg hlam0.le N)
      rw [mul_div_assoc]
      exact lt_of_le_of_lt h2 hN
  by_contra hnf
  have hinf : Set.Infinite {S : Set ChainData | IsRegComp a h S c ∧ ∃ q ∈ S, q.2.1 ∈ Ann r₁ r₂} :=
    hnf
  let g : ℕ ↪ {S // S ∈ {S : Set ChainData | IsRegComp a h S c ∧ ∃ q ∈ S, q.2.1 ∈ Ann r₁ r₂}} :=
    Set.Infinite.natEmbedding _ hinf
  let S' : ℕ → Set ChainData := fun n => (g n : Set ChainData)
  have hS'reg : ∀ n, IsRegComp a h (S' n) c := fun n => (g n).2.1
  have hS'ann : ∀ n, ∃ q ∈ S' n, q.2.1 ∈ Ann r₁ r₂ := fun n => (g n).2.2
  have hS'inj : Function.Injective S' := fun i j hij => g.injective (Subtype.ext hij)
  obtain ⟨M₀, hM₀⟩ := hT r₁ r₂ hr₁ hr₁₂ hr₂δ₁ hratio c S' hS'reg hnd
  choose q hqmem hqann using hS'ann
  set M : ℕ := max M₀ N with hMdef
  have hM₀M : M₀ ≤ M := le_max_left _ _
  have hNM : N ≤ M := le_max_right _ _
  have hM₁ : (eqLam a : ℝ) ^ M * r₂ < δ₂ := by
    have hle : (eqLam a : ℝ) ^ M ≤ (eqLam a : ℝ) ^ N :=
      pow_le_pow_of_le_one hlam0.le hlam1.le hNM
    calc (eqLam a : ℝ) ^ M * r₂ ≤ (eqLam a : ℝ) ^ N * r₂ :=
          mul_le_mul_of_nonneg_right hle (le_of_lt hr₂)
      _ < δ₂ := hN₁
  have hM₂ : (eqLam a : ℝ) ^ M * (2 * rhoStar a h) / r₁ < δ₂ := by
    have hle : (eqLam a : ℝ) ^ M ≤ (eqLam a : ℝ) ^ N :=
      pow_le_pow_of_le_one hlam0.le hlam1.le hNM
    have hnn : 0 ≤ (2 * rhoStar a h) / r₁ := by positivity
    calc (eqLam a : ℝ) ^ M * (2 * rhoStar a h) / r₁
        = (eqLam a : ℝ) ^ M * ((2 * rhoStar a h) / r₁) := by ring
      _ ≤ (eqLam a : ℝ) ^ N * ((2 * rhoStar a h) / r₁) := mul_le_mul_of_nonneg_right hle hnn
      _ = (eqLam a : ℝ) ^ N * (2 * rhoStar a h) / r₁ := by ring
      _ < δ₂ := hN₂
  have hUnionFin : (⋃ f ∈ (LAFree.laWords M : Set (List Bool)), ⋃ b ∈ (LAFree.laWords M : Set (List Bool)),
      LAFree.DatumSet a h r₁ r₂ M f b).Finite := by
    refine Set.Finite.biUnion (LAFree.laWords M).finite_toSet (fun f hf => ?_)
    refine Set.Finite.biUnion (LAFree.laWords M).finite_toSet (fun b hb => ?_)
    exact hD r₁ r₂ hr₁ hr₁₂ hr₂δ₂ hratio M f b (LAFree.laWords_mem.mp (Finset.mem_coe.mp hf))
      (LAFree.laWords_mem.mp (Finset.mem_coe.mp hb)) hM₁ hM₂
  have hmem : ∀ n, (c, S' n) ∈ (⋃ f ∈ (LAFree.laWords M : Set (List Bool)),
      ⋃ b ∈ (LAFree.laWords M : Set (List Bool)), LAFree.DatumSet a h r₁ r₂ M f b) := by
    intro n
    have hfn : (fwdW a M (q n)).length = M := fwdW_length a M _
    have hbn : (bwdW a M (q n)).length = M := bwdW_length a M _
    refine Set.mem_biUnion (Finset.mem_coe.mpr (LAFree.laWords_mem.mpr hfn)) ?_
    refine Set.mem_biUnion (Finset.mem_coe.mpr (LAFree.laWords_mem.mpr hbn)) ?_
    have hqchain : IsChain a h (q n) := isChain_of_mem_H0 ((hS'reg n).1 (hqmem n))
    have hqval : (q n).2.1 * (q n).2.2 = c := (hS'reg n).2.2 (q n) (hqmem n)
    have htail := hM₀ n (q n) (hqmem n) (hqann n)
    exact ⟨hS'reg n, hc, q n, hqmem n, hqann n,
      LAFree.chain_eq_candChain_canonical ha0 ha1 hqchain hqval
        (fun k hk => htail.1 k (le_trans hM₀M hk)) (fun k hk => htail.2 k (le_trans hM₀M hk)),
      (fun k hk => htail.1 k (le_trans hM₀M hk)), (fun k hk => htail.2 k (le_trans hM₀M hk))⟩
  have hrange : Set.Finite (Set.range S') :=
    (hUnionFin.image (fun x : ℂ × Set ChainData => x.2)).subset (t := Set.range S') (fun x hx => by
      obtain ⟨n, rfl⟩ := hx
      exact ⟨(c, S' n), hmem n, rfl⟩)
  exact Set.infinite_range_of_injective hS'inj hrange

/-- **Global finiteness of the regular components of a descendant-free value.** -/
theorem la_comp_finite_free {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) (hpos : 0 < rhoStar a h) {c : ℂ}
    (hc : ‖c‖ ≤ 2 * rhoStar a h)
    (hnd : ∀ μ₁ ∈ CharSet a h, ∀ μ₂ ∈ CharSet a h, (μ₁ ≠ 1 ∨ μ₂ ≠ 1) →
      ∀ T : Set ChainData, ¬ IsRegComp a h T (c * μ₁ * μ₂)) :
    {S : Set ChainData | IsRegComp a h S c}.Finite := by
  obtain ⟨δ, hδ, hfin⟩ := la_finite_meeting_ann ha0 ha1 hh hpos hc hnd
  have hlam : 0 < eqLam a := div_pos (by linarith) (by linarith)
  have hlam1 : eqLam a < 1 := by rw [eqLam, div_lt_one (by linarith)]; linarith
  have hmin : 0 < min r δ := lt_min hh.1 hδ
  set r₂ : ℝ := min r δ / 4 with hr₂def
  set r₁ : ℝ := r₂ * eqLam a / 2 with hr₁def
  have hr₂0 : 0 < r₂ := by rw [hr₂def]; positivity
  have hr₂r : r₂ < r := by rw [hr₂def]; have := min_le_left r δ; linarith
  have hr₂δ : r₂ < δ := by rw [hr₂def]; have := min_le_right r δ; linarith
  have hr₁0 : 0 < r₁ := by rw [hr₁def]; positivity
  have hr₁₂ : r₁ < r₂ := by
    rw [hr₁def]
    have h2 : eqLam a / 2 < 1 := by linarith
    nlinarith [hr₂0]
  have hratio : 1 / eqLam a < r₂ / r₁ := by
    have heq : r₂ / r₁ = 2 / eqLam a := by rw [hr₁def]; field_simp
    rw [heq]
    exact div_lt_div_of_pos_right (by norm_num) hlam
  refine (hfin r₁ r₂ hr₁0 hr₁₂ hr₂r hr₂δ hratio).subset ?_
  rintro S hS
  exact ⟨hS, la_meets_ann_of_countable ha0 ha1 hh hr₁0 hr₁₂ hS⟩

open Classical in
/-- **A regular component of a descendant-free value is periodic under the shift.** -/
theorem la_periodic_free {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) (hpos : 0 < rhoStar a h) {c : ℂ}
    (hc : ‖c‖ ≤ 2 * rhoStar a h)
    (hnd : ∀ μ₁ ∈ CharSet a h, ∀ μ₂ ∈ CharSet a h, (μ₁ ≠ 1 ∨ μ₂ ≠ 1) →
      ∀ T : Set ChainData, ¬ IsRegComp a h T (c * μ₁ * μ₂)) :
    ∀ S : Set ChainData, IsRegComp a h S c →
      ∃ d : ℕ, 0 < d ∧ ∀ q ∈ S, (hShift a)^[d] q ∈ S := by
  have hfin : {S : Set ChainData | IsRegComp a h S c}.Finite :=
    la_comp_finite_free ha0 ha1 hh hpos hc hnd
  intro S hS
  have horb : ∀ k : ℕ, shiftZ a (k : ℤ) '' S ∈ {S' : Set ChainData | IsRegComp a h S' c} :=
    fun k => LAFree.isRegComp_shiftZ ha0 ha1 hS (k : ℤ)
  let T : Set (Set ChainData) := {S' : Set ChainData | IsRegComp a h S' c}
  have hTfin : T.Finite := hfin
  letI : Fintype ↥T := hTfin.fintype
  set n : ℕ := Fintype.card ↥T with hn
  let g : Fin (n + 1) → ↥T := fun k => ⟨shiftZ a ((k.val : ℤ)) '' S, horb k.val⟩
  have hcard : Fintype.card ↥T < Fintype.card (Fin (n + 1)) := by
    rw [Fintype.card_fin]; omega
  obtain ⟨i, j, hij, hgij⟩ := Fintype.exists_ne_map_eq_of_card_lt g hcard
  have hsets : shiftZ a (i.val : ℤ) '' S = shiftZ a (j.val : ℤ) '' S := by
    have := congrArg Subtype.val hgij
    simpa [g] using this
  have hne : i.val ≠ j.val := fun h => hij (Fin.ext h)
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · refine ⟨j.val - i.val, Nat.sub_pos_of_lt hlt, ?_⟩
    have hd_eq : ((j.val - i.val : ℕ) : ℤ) = (j.val : ℤ) - (i.val : ℤ) := by
      rw [Nat.cast_sub (le_of_lt hlt)]
    have hL : shiftZ a (-(i.val : ℤ)) '' (shiftZ a (i.val : ℤ) '' S) = S := by
      rw [← Set.image_comp]
      have : (shiftZ a (-(i.val : ℤ))) ∘ (shiftZ a (i.val : ℤ)) = id :=
        funext (fun p => (shiftZ_neg_apply ha0 ha1 (i.val : ℤ) p).2)
      rw [this, Set.image_id]
    have hR : shiftZ a (-(i.val : ℤ)) '' (shiftZ a (j.val : ℤ) '' S)
        = shiftZ a ((j.val : ℤ) - (i.val : ℤ)) '' S := by
      rw [← Set.image_comp]
      have hcomp : (shiftZ a (-(i.val : ℤ))) ∘ (shiftZ a (j.val : ℤ))
          = shiftZ a ((j.val : ℤ) - (i.val : ℤ)) := by
        funext p
        simp only [Function.comp_apply]
        rw [shiftZ_shiftZ ha0 ha1 (-(i.val : ℤ)) (j.val : ℤ) p,
          show -(i.val : ℤ) + (j.val : ℤ) = (j.val : ℤ) - (i.val : ℤ) by ring]
      rw [hcomp]
    have hset : shiftZ a ((j.val : ℤ) - (i.val : ℤ)) '' S = S := by
      rw [← hR, ← hsets, hL]
    have hsetd : shiftZ a ((j.val - i.val : ℕ) : ℤ) '' S = S := by
      rw [hd_eq]; exact hset
    intro q hq
    rw [hShift_iterate_eq_shiftZ ha0 ha1]
    rw [← hsetd]
    exact ⟨q, hq, rfl⟩
  · refine ⟨i.val - j.val, Nat.sub_pos_of_lt hgt, ?_⟩
    have hd_eq : ((i.val - j.val : ℕ) : ℤ) = (i.val : ℤ) - (j.val : ℤ) := by
      rw [Nat.cast_sub (le_of_lt hgt)]
    have hL : shiftZ a (-(j.val : ℤ)) '' (shiftZ a (j.val : ℤ) '' S) = S := by
      rw [← Set.image_comp]
      have : (shiftZ a (-(j.val : ℤ))) ∘ (shiftZ a (j.val : ℤ)) = id :=
        funext (fun p => (shiftZ_neg_apply ha0 ha1 (j.val : ℤ) p).2)
      rw [this, Set.image_id]
    have hR : shiftZ a (-(j.val : ℤ)) '' (shiftZ a (i.val : ℤ) '' S)
        = shiftZ a ((i.val : ℤ) - (j.val : ℤ)) '' S := by
      rw [← Set.image_comp]
      have hcomp : (shiftZ a (-(j.val : ℤ))) ∘ (shiftZ a (i.val : ℤ))
          = shiftZ a ((i.val : ℤ) - (j.val : ℤ)) := by
        funext p
        simp only [Function.comp_apply]
        rw [shiftZ_shiftZ ha0 ha1 (-(j.val : ℤ)) (i.val : ℤ) p,
          show -(j.val : ℤ) + (i.val : ℤ) = (i.val : ℤ) - (j.val : ℤ) by ring]
      rw [hcomp]
    have hset : shiftZ a ((i.val : ℤ) - (j.val : ℤ)) '' S = S := by
      rw [← hR, hsets, hL]
    have hsetd : shiftZ a ((i.val - j.val : ℕ) : ℤ) '' S = S := by
      rw [hd_eq]; exact hset
    intro q hq
    rw [hShift_iterate_eq_shiftZ ha0 ha1]
    rw [← hsetd]
    exact ⟨q, hq, rfl⟩

end

end Work.EQ
