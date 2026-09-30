import Mathlib
import Submission.Work.BMF.adi_all_defs
import Submission.Work.BMF.prime_tuple_count
import Submission.Work.BMF.degen_step_all

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The near-degenerate closed walks of the full quadruple graph

`Work.BMF.degen_closedWalkAll_le`: the number of closed walks of length `ℓ` of the full
graph `GAdjAll` whose source- and target-prime products differ by at most `C₀ P₁^{ℓ} / N` is
`≪ C₀ π₀(P₁)^{2ℓ} / N`, uniformly in the quadruple graph.

Two ingredients:

* `card_closedWalkAll_le_labelPairs` below: the labels `(stepV, stepU)` of a walk determine
  the walk (`step_unique_all`, from `Submission.Work.BMF.degen_step_all`), so the walks are at
  most as numerous as the label pairs, i.e. the pairs of `ℓ`-tuples of primes in `[P₁, 2P₁]`;
* `labelPairs_count`: the counting of pairs of prime tuples with nearby products, which is the
  `q = 1`, `m = 1` case of `Work.BMF.prime_tuple_count` (MRT Lemma 2.6 / MRTTZ (3.12)).
-/

namespace Work.BMF

open Finset Real

/-! ## The labels of a walk are its two prime products -/

private lemma walkLabels_prod_fst {k : ℕ} {f : ℕ → ℂ} {c C X L P₁ P₂ : ℝ}
    (D : QuadData k f c C X L P₁ P₂) (ℓ : ℕ) (W : Fin (ℓ + 1) → GVert D) :
    (∏ i, (walkLabels D ℓ W).1 i) = walkProdV D ℓ W := rfl

private lemma walkLabels_prod_snd {k : ℕ} {f : ℕ → ℂ} {c C X L P₁ P₂ : ℝ}
    (D : QuadData k f c C X L P₁ P₂) (ℓ : ℕ) (W : Fin (ℓ + 1) → GVert D) :
    (∏ i, (walkLabels D ℓ W).2 i) = walkProdU D ℓ W := rfl

/-! ## Labels of walks of the full graph lie in `labelPairs` -/

private lemma walkLabels_mem_labelPairs_all {k : ℕ} {f : ℕ → ℂ} {c C X L P₁ P₂ : ℝ}
    (D : QuadData k f c C X L P₁ P₂) (hP : 0 < P₁) {ℓ : ℕ} {W : Fin (ℓ + 1) → GVert D}
    (hW : W ∈ walkSetAll D ℓ) : walkLabels D ℓ W ∈ labelPairs P₁ ℓ := by
  have hadj : ∀ j : Fin ℓ, GAdjAll D (W j.castSucc) (W j.succ) :=
    fun j => (Finset.mem_filter.mp hW).2 j
  rw [labelPairs, Finset.mem_product, Fintype.mem_piFinset, Fintype.mem_piFinset]
  refine ⟨fun j => ?_, fun j => ?_⟩
  · rw [mem_primesIn_iff (by positivity)]
    exact stepV_prime_all D (hadj j)
  · rw [mem_primesIn_iff (by positivity)]
    exact stepU_prime_all D (hadj j)

/-! ## The labels determine the walk -/

private theorem walk_eq_of_labels_all {k : ℕ} {f : ℕ → ℂ} {c C X L P₁ P₂ : ℝ}
    (D : QuadData k f c C X L P₁ P₂) (hP : 0 < P₁) (hL : 0 < L) {ℓ : ℕ}
    {W W' : Fin (ℓ + 1) → GVert D} (hW : W ∈ walkSetAll D ℓ) (hW' : W' ∈ walkSetAll D ℓ)
    (h0 : W 0 = W' 0) : walkLabels D ℓ W = walkLabels D ℓ W' → W = W' := by
  intro hlab
  have hV : ∀ j : Fin ℓ,
      stepV D (W j.castSucc) (W j.succ) = stepV D (W' j.castSucc) (W' j.succ) :=
    fun j => congrFun (congrArg Prod.fst hlab) j
  have hU : ∀ j : Fin ℓ,
      stepU D (W j.castSucc) (W j.succ) = stepU D (W' j.castSucc) (W' j.succ) :=
    fun j => congrFun (congrArg Prod.snd hlab) j
  have hadjW : ∀ j : Fin ℓ, GAdjAll D (W j.castSucc) (W j.succ) :=
    fun j => (Finset.mem_filter.mp hW).2 j
  have hadjW' : ∀ j : Fin ℓ, GAdjAll D (W' j.castSucc) (W' j.succ) :=
    fun j => (Finset.mem_filter.mp hW').2 j
  funext i
  induction i using Fin.induction with
  | zero => exact h0
  | succ j ih =>
      have h1 : stepV D (W j.castSucc) (W j.succ) = stepV D (W j.castSucc) (W' j.succ) := by
        have hh := hV j
        rw [← ih] at hh
        exact hh
      have h2 : stepU D (W j.castSucc) (W j.succ) = stepU D (W j.castSucc) (W' j.succ) := by
        have hh := hU j
        rw [← ih] at hh
        exact hh
      have hxy' : GAdjAll D (W j.castSucc) (W' j.succ) := by
        have hh := hadjW' j
        rw [← ih] at hh
        exact hh
      exact step_unique_all D hP hL (hadjW j) hxy' h1 h2

/-- **Closed walks are at most as numerous as label pairs.**  For a fixed starting point
(recorded by the left endpoint `x`) and any property of the labels, the closed walks of the
full graph of length `ℓ` satisfying it are no more numerous than the label pairs satisfying
the same property. -/
private theorem card_closedWalkAll_le_labelPairs {k : ℕ} {f : ℕ → ℂ} {c C X L P₁ P₂ : ℝ}
    (D : QuadData k f c C X L P₁ P₂) (hP : 0 < P₁) (hL : 0 < L) (ℓ : ℕ) (x : ℝ)
    (P : ((Fin ℓ → ℕ) × (Fin ℓ → ℕ)) → Prop) [DecidablePred P] :
    ((closedWalkAll D ℓ x).filter (fun W => P (walkLabels D ℓ W))).card ≤
      ((labelPairs P₁ ℓ).filter P).card := by
  classical
  have hinj : Set.InjOn (walkLabels D ℓ)
      ↑((closedWalkAll D ℓ x).filter (fun W => P (walkLabels D ℓ W))) := by
    intro W hW W' hW' heq
    rw [Finset.mem_coe, Finset.mem_filter] at hW hW'
    obtain ⟨hWc, _⟩ := hW
    obtain ⟨hWc', _⟩ := hW'
    rw [closedWalkAll, Finset.mem_filter] at hWc hWc'
    refine walk_eq_of_labels_all D hP hL hWc.1 hWc'.1 ?_ heq
    exact Subtype.ext (by rw [hWc.2.2, hWc'.2.2])
  calc ((closedWalkAll D ℓ x).filter (fun W => P (walkLabels D ℓ W))).card
      = (((closedWalkAll D ℓ x).filter (fun W => P (walkLabels D ℓ W))).image
          (walkLabels D ℓ)).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ ((labelPairs P₁ ℓ).filter P).card := by
        refine Finset.card_le_card ?_
        intro p hp
        rw [Finset.mem_image] at hp
        obtain ⟨W, hW, rfl⟩ := hp
        rw [Finset.mem_filter] at hW ⊢
        refine ⟨?_, hW.2⟩
        rw [closedWalkAll, Finset.mem_filter] at hW
        exact walkLabels_mem_labelPairs_all D hP hW.1.1

/-! ## Counting nearby products of prime tuples -/

/-- The `q = 1`, `m = 1` case of `Work.BMF.prime_tuple_count`: the pairs of `ℓ`-tuples of
primes in `[P, 2P]` whose products differ by at most `C₀ P^ℓ / N` number
`≪ C₀ π₀(P)^{2ℓ} / N`. -/
private theorem labelPairs_count (ℓ : ℕ) (hℓ : 1 ≤ ℓ) :
    ∃ C P₀ : ℝ, 0 < C ∧ ∀ (P N C₀ : ℝ), P₀ ≤ P → 3 ≤ N → N ≤ P ^ (ℓ - 1) →
      1 / Real.log P ≤ C₀ →
      (((labelPairs P ℓ).filter (fun p =>
        |((∏ i, p.1 i : ℕ) : ℝ) - ((∏ i, p.2 i : ℕ) : ℝ)| ≤ C₀ * P ^ ℓ / N)).card : ℝ)
        ≤ C * C₀ * pi0 P ^ (2 * ℓ) / N := by
  classical
  obtain ⟨CN, PN, hCN, hN4⟩ := prime_tuple_count ℓ 1 hℓ le_rfl
  refine ⟨2 * CN, max PN 3, by linarith, ?_⟩
  intro P N C₀ hP₀ hN3 hNle hC₀
  have hPN : PN ≤ P := le_trans (le_max_left _ _) hP₀
  have hP3 : (3 : ℝ) ≤ P := le_trans (le_max_right _ _) hP₀
  have hPpos : (0 : ℝ) < P := by linarith
  have hlogP : (0 : ℝ) < Real.log P := Real.log_pos (by linarith)
  have hNpos : (0 : ℝ) < N := by linarith
  have hlog3 : (1 : ℝ) < Real.log 3 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 3)]
    exact Real.exp_one_lt_three
  have hlogN : (1 : ℝ) ≤ Real.log N :=
    le_trans hlog3.le (Real.log_le_log (by norm_num : (0 : ℝ) < 3) hN3)
  have hlogNpos : (0 : ℝ) < Real.log N := lt_of_lt_of_le one_pos hlogN
  have hdiv : 1 / Real.log N ≤ 1 := (div_le_one hlogNpos).mpr hlogN
  -- the N4 count, with the admissible primes (those not dividing `1`) made explicit
  have hkey := hN4 P N C₀ 1 hPN hN3 hNle hC₀ (le_rfl : 1 ≤ 1)
  have hpi : Fintype.piFinset (fun _ : Fin ℓ => (primesIn P (2 * P)).filter (fun p => ¬ p ∣ 1))
      = Fintype.piFinset (fun _ : Fin ℓ => primesIn P (2 * P)) := by
    ext v
    simp only [Fintype.mem_piFinset]
    constructor
    · intro h i
      exact (Finset.mem_filter.mp (h i)).1
    · intro h i
      refine Finset.mem_filter.mpr ⟨h i, ?_⟩
      exact ((mem_primesIn_iff (by linarith : (0 : ℝ) ≤ 2 * P)).mp (h i)).1.not_dvd_one
  rw [hpi] at hkey
  -- the label pairs form a subset of the counted set
  have hsub : ((labelPairs P ℓ).filter (fun p =>
        |((∏ i, p.1 i : ℕ) : ℝ) - ((∏ i, p.2 i : ℕ) : ℝ)| ≤ C₀ * P ^ ℓ / N))
      ⊆ ((Fintype.piFinset (fun _ : Fin ℓ => primesIn P (2 * P)) ×ˢ
          Fintype.piFinset (fun _ : Fin ℓ => primesIn P (2 * P))).filter (fun v =>
        |((∏ i, v.2 i : ℕ) : ℝ) - ((∏ i, v.1 i : ℕ) : ℝ)| ≤ C₀ * P ^ ℓ / N ∧
          (∏ i, v.2 i) ^ 1 ≡ (∏ i, v.1 i) ^ 1 [MOD 1])) := by
    intro p hp
    rw [Finset.mem_filter] at hp ⊢
    refine ⟨by simpa only [labelPairs] using hp.1, ?_, ?_⟩
    · rw [abs_sub_comm]
      exact hp.2
    · exact Nat.modEq_one
  have hcard := Finset.card_le_card hsub
  have hbr : ((2 * 1 : ℕ) : ℝ) ^ (1 : ℕ).primeFactors.card / ((1 : ℕ).totient : ℝ)
      + 1 / Real.log N = 1 + 1 / Real.log N := by
    simp [Nat.primeFactors_one, Nat.totient_one]
  have hC₀pos : 0 < C₀ := by
    have : 0 < 1 / Real.log P := one_div_pos.mpr hlogP
    linarith
  have hpi0 : 0 ≤ pi0 P := by
    rw [pi0]
    exact div_nonneg hPpos.le hlogP.le
  have hA : 0 ≤ CN * C₀ * pi0 P ^ (2 * ℓ) / N :=
    div_nonneg (mul_nonneg (mul_nonneg hCN.le hC₀pos.le) (pow_nonneg hpi0 _)) hNpos.le
  calc (((labelPairs P ℓ).filter (fun p =>
        |((∏ i, p.1 i : ℕ) : ℝ) - ((∏ i, p.2 i : ℕ) : ℝ)| ≤ C₀ * P ^ ℓ / N)).card : ℝ)
      ≤ (((Fintype.piFinset (fun _ : Fin ℓ => primesIn P (2 * P)) ×ˢ
          Fintype.piFinset (fun _ : Fin ℓ => primesIn P (2 * P))).filter (fun v =>
        |((∏ i, v.2 i : ℕ) : ℝ) - ((∏ i, v.1 i : ℕ) : ℝ)| ≤ C₀ * P ^ ℓ / N ∧
          (∏ i, v.2 i) ^ 1 ≡ (∏ i, v.1 i) ^ 1 [MOD 1])).card : ℝ) := by
        exact_mod_cast hcard
    _ ≤ CN * C₀ * pi0 P ^ (2 * ℓ) / N * (1 + 1 / Real.log N) := by
        simpa [hbr] using hkey
    _ ≤ 2 * CN * C₀ * pi0 P ^ (2 * ℓ) / N := by
        have h1 : 1 + 1 / Real.log N ≤ 2 := by linarith
        have h2 := mul_le_mul_of_nonneg_left h1 hA
        calc CN * C₀ * pi0 P ^ (2 * ℓ) / N * (1 + 1 / Real.log N)
            ≤ CN * C₀ * pi0 P ^ (2 * ℓ) / N * 2 := h2
          _ = 2 * CN * C₀ * pi0 P ^ (2 * ℓ) / N := by ring

/-! ## The main lemma -/

theorem degen_closedWalkAll_le (k : ℕ) (ℓ : ℕ) (hℓ : 1 ≤ ℓ) :
    ∃ C P₀ : ℝ, 0 < C ∧ ∀ (f : ℕ → ℂ) (c Cq X L P₁ P₂ N C₀ : ℝ)
      (D : Work.BMF.QuadData k f c Cq X L P₁ P₂) (x : ℝ),
      P₀ ≤ P₁ → 0 < P₁ → 0 < L → 3 ≤ N → N ≤ P₁ ^ (ℓ - 1) → 1 / Real.log P₁ ≤ C₀ →
      (((Work.BMF.closedWalkAll D ℓ x).filter (fun W =>
        |((Work.BMF.walkProdV D ℓ W : ℕ) : ℝ) - ((Work.BMF.walkProdU D ℓ W : ℕ) : ℝ)|
          ≤ C₀ * P₁ ^ ℓ / N)).card : ℝ) ≤ C * C₀ * Work.BMF.pi0 P₁ ^ (2 * ℓ) / N := by
  obtain ⟨C₁, P₁₀, hC₁, hcnt⟩ := labelPairs_count ℓ hℓ
  refine ⟨C₁, max P₁₀ 3, hC₁, ?_⟩
  intro f c Cq X L P₁ P₂ N C₀ D x hP₀ hPpos hL hN hNle hC₀
  have hcnt' := hcnt P₁ N C₀ (le_trans (le_max_left _ _) hP₀) hN hNle hC₀
  have hfilter : (closedWalkAll D ℓ x).filter (fun W =>
        |((walkProdV D ℓ W : ℕ) : ℝ) - ((walkProdU D ℓ W : ℕ) : ℝ)| ≤ C₀ * P₁ ^ ℓ / N)
      = (closedWalkAll D ℓ x).filter (fun W =>
        (fun p : (Fin ℓ → ℕ) × (Fin ℓ → ℕ) =>
          |((∏ i, p.1 i : ℕ) : ℝ) - ((∏ i, p.2 i : ℕ) : ℝ)| ≤ C₀ * P₁ ^ ℓ / N)
          (walkLabels D ℓ W)) := by
    apply Finset.filter_congr
    intro W _
    simp only [walkLabels_prod_fst, walkLabels_prod_snd]
  have hA : (((closedWalkAll D ℓ x).filter (fun W =>
        (fun p : (Fin ℓ → ℕ) × (Fin ℓ → ℕ) =>
          |((∏ i, p.1 i : ℕ) : ℝ) - ((∏ i, p.2 i : ℕ) : ℝ)| ≤ C₀ * P₁ ^ ℓ / N)
          (walkLabels D ℓ W))).card : ℝ)
      ≤ (((labelPairs P₁ ℓ).filter (fun p : (Fin ℓ → ℕ) × (Fin ℓ → ℕ) =>
          |((∏ i, p.1 i : ℕ) : ℝ) - ((∏ i, p.2 i : ℕ) : ℝ)| ≤ C₀ * P₁ ^ ℓ / N)).card : ℝ) := by
    exact_mod_cast card_closedWalkAll_le_labelPairs D hPpos hL ℓ x
      (fun p : (Fin ℓ → ℕ) × (Fin ℓ → ℕ) =>
        |((∏ i, p.1 i : ℕ) : ℝ) - ((∏ i, p.2 i : ℕ) : ℝ)| ≤ C₀ * P₁ ^ ℓ / N)
  rw [hfilter]
  exact le_trans hA hcnt'

end Work.BMF
