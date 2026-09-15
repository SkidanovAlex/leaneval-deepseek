/-
Copyright: the formalization team of the Vinogradov mean value theorem project.
-/
import Submission.Vinogradov.UncertaintyBlock
import Submission.Commons.Analysis.Inequalities.sum_rpow_le_card_rpow_mul_sum_rpow
import Submission.Commons.Analysis.Inequalities.sum_fiber_rpow_le_of_disjoint
import Submission.Commons.Analysis.Inequalities.sum_rpow_inv_le_sum_rpow_inv
import Submission.Commons.Measure.Integral.lintegral_rpow_split_le
import Submission.Commons.Measure.Integral.lintegral_finsetSum_mul_finsetSum_measurable

/-!
# GLYZ Lemma 3.4: the symmetric constants are bounded by the asymmetric ones

The last ingredient of §3 of Guo–Li–Yung–Zorin-Kranich is the passage from the *asymmetric*
bilinear constants `AsymDec k hk l N m m' C` (Definition 3.1) to the *symmetric* one
`SymDec k N C'` (the bilinear constant of Definition 2.1, in the glued dyadic form used by
`SymBilinear.lean`).

* `subBlk m a` — the level-`m` blocks contained in the `a`-th quarter of `[0,1]`, with
  `subBlkIdx`, `subBlk_card`, `biUnion_subBlk` and the reindexing identity `sum_blkFin_two`;
* `sepLevel_of_subBlk` (and the transposed `sepLevel_of_subBlk'`) — the separation condition
  `dist ≥ 1/4` is inherited by the sub-blocks of two distinct quarters;
* `sum_l2Of_subBlk_le` — the `ℓ² ↪ ℓ^s` embedding over the blocks of a quarter;
* `quarter_pointwise` — the uncertainty principle (GLYZ Lemma 3.3) applied to one quarter;
* `asymConst₁`, `asymConst₂`, `symDecConst` — the constants;
* **`symDec_of_asymDec`** — GLYZ Lemma 3.4.

The proof follows the paper, with one point worth recording: the second factor of the Hölder
step `(3.5)` requires the asymmetric inequality with the exponent `p_k - p_l` on the level-`m`
blocks and `p_l` on the level-`m'` ones.  This is *not* a different instance of `AsymDec`
(as one might fear: `p_k - p_l` is not of the form `p_{l'}` in general).  Instead one decomposes
the *first* quarter at level `m'` and the *second* at level `m` — the "crossed" decomposition —
so that `AsymDec` applies with the level-`m` blocks (of the second quarter) in its first slot.
This is `pair_pointwise_swap` below, and it is the reason no second hypothesis on `AsymDec` is
needed.
-/

noncomputable section
open MeasureTheory Complex Classical Filter
open scoped Real BigOperators Topology RealInnerProductSpace ENNReal NNReal

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.style.emptyLine false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000

namespace Submission.Vinogradov



/-! ## 1. The level-`m` blocks inside a quarter -/

/-- The level-`m` blocks contained in the `a`-th quarter of `[0,1]`. -/
def subBlk (m a : ℕ) : Finset (Fin (2 ^ m)) :=
  Finset.univ.filter (fun q : Fin (2 ^ m) => (q : ℕ) / 2 ^ (m - 2) = a)

lemma mem_subBlk {m a : ℕ} {q : Fin (2 ^ m)} :
    q ∈ subBlk m a ↔ (q : ℕ) / 2 ^ (m - 2) = a := by
  simp [subBlk]

lemma pieceCenter_cast (m : ℕ) (q : Fin (2 ^ m)) :
    pieceCenter (2 ^ m) q = (((q : ℕ) : ℝ) + 1 / 2) / (2 : ℝ) ^ m := by
  rw [pieceCenter]
  push_cast
  ring

lemma subBlk_lt {m a q : ℕ} (h : q / 2 ^ (m - 2) = a) : a * 2 ^ (m - 2) ≤ q := by
  have hdec := Nat.div_add_mod q (2 ^ (m - 2))
  rw [h, Nat.mul_comm] at hdec
  omega

lemma subBlk_lt' {m a q : ℕ} (h : q / 2 ^ (m - 2) = a) : q < (a + 1) * 2 ^ (m - 2) := by
  have hlt : q % 2 ^ (m - 2) < 2 ^ (m - 2) := Nat.mod_lt _ (pow_pos (by norm_num) _)
  have hdec := Nat.div_add_mod q (2 ^ (m - 2))
  rw [h, Nat.mul_comm] at hdec
  rw [Nat.succ_mul]
  omega

/-- The level-`m` blocks inside the `a`-th quarter, parametrised by their position. -/
def subBlkIdx {m : ℕ} (hm : 2 ≤ m) (a : ℕ) (ha : a ≤ 3) (j : Fin (2 ^ (m - 2))) : Fin (2 ^ m) :=
  ⟨a * 2 ^ (m - 2) + (j : ℕ), by
    have h1 : a * 2 ^ (m - 2) + (j : ℕ) < (a + 1) * 2 ^ (m - 2) := by
      rw [Nat.succ_mul]; omega
    have h2 : (a + 1) * 2 ^ (m - 2) ≤ 4 * 2 ^ (m - 2) :=
      Nat.mul_le_mul_right _ (by omega)
    have h3 : (4 : ℕ) * 2 ^ (m - 2) = 2 ^ m := by
      rw [show (4 : ℕ) = 2 ^ 2 from rfl, ← pow_add,
        show 2 + (m - 2) = m from by omega]
    omega⟩

lemma subBlkIdx_val {m a : ℕ} (hm : 2 ≤ m) (ha : a ≤ 3) (j : Fin (2 ^ (m - 2))) :
    (subBlkIdx hm a ha j : ℕ) = a * 2 ^ (m - 2) + (j : ℕ) := rfl

lemma subBlkIdx_mem {m a : ℕ} (hm : 2 ≤ m) (ha : a ≤ 3) (j : Fin (2 ^ (m - 2))) :
    subBlkIdx hm a ha j ∈ subBlk m a := by
  rw [mem_subBlk, subBlkIdx_val hm ha]
  exact Nat.div_eq_of_lt_le (Nat.le_add_right _ _) (by rw [Nat.succ_mul]; omega)

lemma subBlkIdx_injective {m a : ℕ} (hm : 2 ≤ m) (ha : a ≤ 3) :
    Function.Injective (subBlkIdx hm a ha : Fin (2 ^ (m - 2)) → Fin (2 ^ m)) := by
  intro j₁ j₂ h
  have h1 : (subBlkIdx hm a ha j₁ : ℕ) = (subBlkIdx hm a ha j₂ : ℕ) := Fin.ext_iff.mp h
  rw [subBlkIdx_val hm ha, subBlkIdx_val hm ha] at h1
  exact Fin.ext (by omega)

lemma subBlk_card {m a : ℕ} (hm : 2 ≤ m) (ha : a ≤ 3) : (subBlk m a).card = 2 ^ (m - 2) := by
  suffices h : (subBlk m a).card = (Finset.univ : Finset (Fin (2 ^ (m - 2)))).card by
    rw [h, Finset.card_univ, Fintype.card_fin]
  refine Finset.card_bij (t := (Finset.univ : Finset (Fin (2 ^ (m - 2)))))
    (fun (q : Fin (2 ^ m)) (_ : q ∈ subBlk m a) =>
      (⟨(q : ℕ) % 2 ^ (m - 2), Nat.mod_lt _ (pow_pos (by norm_num) _)⟩ : Fin (2 ^ (m - 2))))
    ?_ ?_ ?_
  · intro q _
    exact Finset.mem_univ _
  · intro q₁ hq₁ q₂ hq₂ heq
    have h₁ := mem_subBlk.mp hq₁
    have h₂ := mem_subBlk.mp hq₂
    have h₃ : (q₁ : ℕ) % 2 ^ (m - 2) = (q₂ : ℕ) % 2 ^ (m - 2) := Fin.ext_iff.mp heq
    have hd₁ := Nat.div_add_mod (q₁ : ℕ) (2 ^ (m - 2))
    have hd₂ := Nat.div_add_mod (q₂ : ℕ) (2 ^ (m - 2))
    rw [h₁, Nat.mul_comm] at hd₁
    rw [h₂, Nat.mul_comm] at hd₂
    exact Fin.ext (by omega)
  · intro j _
    refine ⟨subBlkIdx hm a ha j, subBlkIdx_mem hm ha j, ?_⟩
    refine Fin.ext ?_
    show (subBlkIdx hm a ha j : ℕ) % 2 ^ (m - 2) = (j : ℕ)
    rw [subBlkIdx_val hm ha, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt j.2]

/-! ## 2. The block decomposition of a quarter -/

lemma powTwo_mul {m N : ℕ} (hmN : m ≤ N) (hm : 2 ≤ m) :
    2 ^ (m - 2) * 2 ^ (N - m) = 2 ^ (N - 2) := by
  rw [← pow_add, show m - 2 + (N - m) = N - 2 from by omega]

lemma blkFin_subset_two {N m a : ℕ} (hm : 2 ≤ m) (hmN : m ≤ N) {q : ℕ}
    (hq : q / 2 ^ (m - 2) = a) : blkFin N m q ⊆ blkFin N 2 a := by
  intro i hi
  rw [mem_blkFin] at hi ⊢
  have hpow := powTwo_mul hmN hm
  have hN : 0 < 2 ^ (N - m) := pow_pos (by norm_num) _
  have hup : (i : ℕ) < (a + 1) * 2 ^ (N - 2) := by
    have h1 : (i : ℕ) / 2 ^ (N - m) < (a + 1) * 2 ^ (m - 2) := by
      rw [hi]; exact subBlk_lt' hq
    have h2 := (Nat.div_lt_iff_lt_mul hN).mp h1
    calc (i : ℕ) < ((a + 1) * 2 ^ (m - 2)) * 2 ^ (N - m) := h2
      _ = (a + 1) * (2 ^ (m - 2) * 2 ^ (N - m)) := by ring
      _ = (a + 1) * 2 ^ (N - 2) := by rw [hpow]
  have hlo : a * 2 ^ (N - 2) ≤ (i : ℕ) := by
    have h1 : a * 2 ^ (m - 2) ≤ (i : ℕ) / 2 ^ (N - m) := by rw [hi]; exact subBlk_lt hq
    have h2 := (Nat.le_div_iff_mul_le hN).mp h1
    calc a * 2 ^ (N - 2) = a * (2 ^ (m - 2) * 2 ^ (N - m)) := by rw [hpow]
      _ = a * 2 ^ (m - 2) * 2 ^ (N - m) := by ring
      _ ≤ (i : ℕ) := h2
  exact Nat.div_eq_of_lt_le hlo hup

lemma subBlk_pairwiseDisjoint {N m a : ℕ} :
    (subBlk m a : Set (Fin (2 ^ m))).PairwiseDisjoint (fun q => blkFin N m q) := by
  intro q _ q' _ hne
  change Disjoint (blkFin N m q) (blkFin N m q')
  rw [Finset.disjoint_iff_ne]
  intro i hi i' hi' heq
  exact hne (Fin.ext (by rw [← mem_blkFin.mp hi, ← mem_blkFin.mp hi', heq]))

lemma biUnion_subBlk {N m a : ℕ} (hm : 2 ≤ m) (hmN : m ≤ N) (ha : a ≤ 3) :
    (subBlk m a).biUnion (fun q => blkFin N m q) = blkFin N 2 a := by
  ext i
  rw [Finset.mem_biUnion]
  constructor
  · rintro ⟨q, hq, hiq⟩
    exact blkFin_subset_two hm hmN (mem_subBlk.mp hq) hiq
  · intro hi
    have hdiv : (i : ℕ) / 2 ^ (N - 2) = a := mem_blkFin.mp hi
    have hlt : (i : ℕ) / 2 ^ (N - m) < 2 ^ m := by
      have hN : 0 < 2 ^ (N - m) := pow_pos (by norm_num) _
      rw [Nat.div_lt_iff_lt_mul hN]
      have h2 : 2 ^ m * 2 ^ (N - m) = 2 ^ N := by
        rw [← pow_add, show m + (N - m) = N from by omega]
      rw [h2]
      exact i.isLt
    refine ⟨⟨(i : ℕ) / 2 ^ (N - m), hlt⟩, ?_, ?_⟩
    · rw [mem_subBlk, Nat.div_div_eq_div_mul,
        show 2 ^ (N - m) * 2 ^ (m - 2) = 2 ^ (N - 2) from by
          rw [mul_comm, powTwo_mul hmN hm]]
      exact hdiv
    · rw [mem_blkFin]

lemma sum_blkFin_two {N m a : ℕ} (hm : 2 ≤ m) (hmN : m ≤ N) (ha : a ≤ 3)
    {α : Type*} [AddCommMonoid α] (G : Fin (2 ^ N) → α) :
    ∑ i ∈ blkFin N 2 a, G i = ∑ q ∈ subBlk m a, ∑ i ∈ blkFin N m q, G i := by
  rw [← Finset.sum_biUnion (subBlk_pairwiseDisjoint (N := N) (m := m) (a := a)),
    biUnion_subBlk hm hmN ha]

/-! ## 3. The separation condition -/

lemma sepLevel_of_subBlk {m m' a' : ℕ} (hm : 2 ≤ m) (hm' : 2 ≤ m') (ha' : 2 ≤ a')
    (ha'4 : a' ≤ 3)
    (q : Fin (2 ^ m)) (hq : q ∈ subBlk m 0) (q' : Fin (2 ^ m')) (hq' : q' ∈ subBlk m' a') :
    sepLevel m m' q q' := by
  have hcastm : ((2 ^ (m - 2) : ℕ) : ℝ) = (2 : ℝ) ^ (m - 2) := by push_cast; ring
  have hcastm' : ((2 ^ (m' - 2) : ℕ) : ℝ) = (2 : ℝ) ^ (m' - 2) := by push_cast; ring
  have hqN : (q : ℕ) / 2 ^ (m - 2) = 0 := mem_subBlk.mp hq
  have hqN' : (q' : ℕ) / 2 ^ (m' - 2) = a' := mem_subBlk.mp hq'
  have hqlt : (q : ℕ) < 2 ^ (m - 2) := (Nat.div_eq_zero_iff_lt (pow_pos (by norm_num) _)).mp hqN
  have hpowm : (2 : ℝ) ^ (m - 2) * 4 = (2 : ℝ) ^ m := by
    rw [show (4 : ℝ) = 2 ^ 2 from by norm_num, ← pow_add, Nat.sub_add_cancel hm]
  have hpowm' : (2 : ℝ) ^ (m' - 2) * 4 = (2 : ℝ) ^ m' := by
    rw [show (4 : ℝ) = 2 ^ 2 from by norm_num, ← pow_add, Nat.sub_add_cancel hm']
  have h2m : (0 : ℝ) < (2 : ℝ) ^ m := by positivity
  have h2m' : (0 : ℝ) < (2 : ℝ) ^ m' := by positivity
  have hle : ((q : ℕ) : ℝ) ≤ (2 : ℝ) ^ (m - 2) - 1 := by
    have h2 : (q : ℕ) ≤ 2 ^ (m - 2) - 1 := Nat.le_sub_one_of_lt hqlt
    have h3 : ((q : ℕ) : ℝ) ≤ ((2 ^ (m - 2) - 1 : ℕ) : ℝ) := by exact_mod_cast h2
    have h4 : ((2 ^ (m - 2) - 1 : ℕ) : ℝ) = (2 : ℝ) ^ (m - 2) - 1 := by
      rw [Nat.cast_sub (Nat.one_le_two_pow), hcastm]
      norm_num
    linarith
  have hc : (((q : ℕ) : ℝ) + 1 / 2) / (2 : ℝ) ^ m ≤ 1 / 4 - 1 / (2 : ℝ) ^ (m + 1) := by
    have h1 : (1 : ℝ) / 4 = (2 : ℝ) ^ (m - 2) / (2 : ℝ) ^ m := by
      rw [eq_div_iff (ne_of_gt h2m), ← hpowm]
      ring
    have h2 : 1 / (2 : ℝ) ^ (m + 1) = (1 / 2) / (2 : ℝ) ^ m := by
      rw [pow_succ]; field_simp
    rw [h1, h2, ← sub_div]
    exact div_le_div_of_nonneg_right (by linarith) (le_of_lt h2m)
  have hc' : (a' : ℝ) / 4 + 1 / (2 : ℝ) ^ (m' + 1)
      ≤ (((q' : ℕ) : ℝ) + 1 / 2) / (2 : ℝ) ^ m' := by
    have h1 : ((a' : ℝ) * (2 : ℝ) ^ (m' - 2)) ≤ ((q' : ℕ) : ℝ) := by
      rw [← hcastm']
      exact_mod_cast subBlk_lt hqN'
    have h2 : (a' : ℝ) / 4
        = (a' : ℝ) * (2 : ℝ) ^ (m' - 2) / (2 : ℝ) ^ m' := by
      rw [eq_div_iff (ne_of_gt h2m'), ← hpowm']
      ring
    have h3 : 1 / (2 : ℝ) ^ (m' + 1) = (1 / 2) / (2 : ℝ) ^ m' := by
      rw [pow_succ]; field_simp
    rw [h2, h3, ← add_div]
    exact div_le_div_of_nonneg_right (by linarith) (le_of_lt h2m')
  have hle' : (((q : ℕ) : ℝ) + 1 / 2) / (2 : ℝ) ^ m
      ≤ (((q' : ℕ) : ℝ) + 1 / 2) / (2 : ℝ) ^ m' := by
    refine hc.trans ?_
    have h1 : (1 : ℝ) / 4 ≤ (a' : ℝ) / 4 := by
      have : (1 : ℝ) ≤ (a' : ℝ) := by exact_mod_cast (by omega : 1 ≤ a')
      linarith
    have h2 : (0 : ℝ) < 1 / (2 : ℝ) ^ (m + 1) := by positivity
    have h3 : (0 : ℝ) < 1 / (2 : ℝ) ^ (m' + 1) := by positivity
    linarith
  have ha'R : (2 : ℝ) ≤ (a' : ℝ) := by exact_mod_cast ha'
  have h2 : (0 : ℝ) < 1 / (2 : ℝ) ^ (m + 1) := by positivity
  have h3 : (0 : ℝ) < 1 / (2 : ℝ) ^ (m' + 1) := by positivity
  have hpos : (0 : ℝ) ≤ (((q' : ℕ) : ℝ) + 1 / 2) / (2 : ℝ) ^ m'
      - (((q : ℕ) : ℝ) + 1 / 2) / (2 : ℝ) ^ m := by linarith
  rw [sepLevel, pieceCenter_cast, pieceCenter_cast, abs_sub_comm, abs_of_nonneg hpos]
  linarith

lemma coe_nnnorm_eq_ofReal (a : ℂ) :
    ((‖a‖₊ : NNReal) : ℝ≥0∞) = ENNReal.ofReal ‖a‖ := by
  simp [ENNReal.ofReal]

/-! ## 4. Integrability and measurability of the objects involved -/

lemma continuous_gauge (k : ℕ) (hk : 1 ≤ k) : Continuous (gauge k hk) := by
  unfold gauge
  fun_prop

lemma continuous_plateGaugeLin (k : ℕ) (δ c : ℝ) : Continuous (plateGaugeLin k δ c) := by
  fun_prop

lemma continuous_phiPlate (k : ℕ) (hk : 1 ≤ k) (δ c A Cφ : ℝ) :
    Continuous (phiPlate k hk δ c A Cφ) := by
  unfold phiPlate
  refine continuous_const.mul ?_
  refine (continuous_const.max
    ((continuous_gauge k hk).comp (continuous_plateGaugeLin k δ c))).rpow_const ?_
  intro x
  exact Or.inl (by positivity)

lemma continuous_platePhi (k : ℕ) (hk : 1 ≤ k) (δ c : ℝ) : Continuous (platePhi k hk δ c) :=
  ENNReal.continuous_ofReal.comp (continuous_phiPlate k hk δ c (gaugeExp k) (gaugeAmp k hk))

lemma measurable_convPow (k : ℕ) (r : ℝ) {g : E k → ℂ} (hg : Measurable g)
    {Ψ : E k → ℝ≥0∞} (hΨ : Measurable Ψ) : Measurable (convPow k r g Ψ) := by
  refine Measurable.lintegral_prod_right (ν := (volume : Measure (E k))) ?_
  show Measurable (fun p : E k × E k => (‖g (p.1 - p.2)‖₊ : ℝ≥0∞) ^ r * Ψ p.2)
  have h1 : Measurable (fun p : E k × E k => (‖g (p.1 - p.2)‖₊ : NNReal)) :=
    (hg.comp (measurable_fst.sub measurable_snd)).nnnorm
  exact ((h1.coe_nnreal_ennreal).pow_const r).mul (hΨ.comp measurable_snd)

/-! ## 5. The `ℓ²` embedding over the blocks of a quarter -/

lemma sum_sqSum_subBlk_le {N m a : ℕ} (hm : 2 ≤ m) (hmN : m ≤ N) (ha : a ≤ 3)
    (A : Fin (2 ^ N) → ℝ≥0∞) {r : ℝ} (hr : 1 ≤ r) :
    ∑ q ∈ subBlk m a, (sqSum (blkFin N m q) A) ^ r ≤ (sqSum (blkFin N 2 a) A) ^ r := by
  simp only [sqSum]
  exact Commons.Analysis.Inequalities.sum_fiber_rpow_le_of_disjoint (subBlk m a)
    (fun q => blkFin N m q) (blkFin N 2 a)
    ((Finset.pairwiseDisjoint_coe).mpr
      (subBlk_pairwiseDisjoint (N := N) (m := m) (a := a)))
    (fun q hq => blkFin_subset_two hm hmN (mem_subBlk.mp hq))
    (fun i => A i ^ (2 : ℝ)) hr

lemma sum_l2Of_subBlk_le {N m a : ℕ} (hm : 2 ≤ m) (hmN : m ≤ N) (ha : a ≤ 3)
    (A : Fin (2 ^ N) → ℝ≥0∞) {s : ℝ} (hs : 2 ≤ s) :
    ∑ q ∈ subBlk m a, (l2Of (blkFin N m q) A) ^ s ≤ (l2Of (blkFin N 2 a) A) ^ s := by
  have hr : (1 : ℝ) ≤ s / 2 := by linarith
  have hcongr : ∀ q : Fin (2 ^ m),
      (l2Of (blkFin N m q) A) ^ s = (sqSum (blkFin N m q) A) ^ (s / 2) := by
    intro q
    rw [l2Of, ← ENNReal.rpow_mul]
    congr 1
    ring
  have hcongr2 : (l2Of (blkFin N 2 a) A) ^ s = (sqSum (blkFin N 2 a) A) ^ (s / 2) := by
    rw [l2Of, ← ENNReal.rpow_mul]
    congr 1
    ring
  rw [Finset.sum_congr rfl fun q _ => hcongr q, hcongr2]
  exact sum_sqSum_subBlk_le hm hmN ha A hr

/-! ## 6. The transport of a bilinear decoupling inequality -/

lemma sepLevel_of_subBlk' {m m' a' : ℕ} (hm : 2 ≤ m) (hm' : 2 ≤ m') (ha' : 2 ≤ a')
    (ha'4 : a' ≤ 3) (q : Fin (2 ^ m)) (hq : q ∈ subBlk m a') (q' : Fin (2 ^ m'))
    (hq' : q' ∈ subBlk m' 0) : sepLevel m m' q q' := by
  have h := sepLevel_of_subBlk hm' hm ha' ha'4 q' hq' q hq
  unfold sepLevel at h ⊢
  rw [abs_sub_comm] at h
  linarith

/-! ## 7. The pointwise uncertainty bound for one quarter -/

lemma quarter_pointwise {k N m : ℕ} (hk : 1 ≤ k) (hm : 2 ≤ m) (hmN : m ≤ N)
    (a : ℕ) (ha : a ≤ 3) (f : Fin (2 ^ N) → E k → ℂ)
    (hf : ∀ i, IsFourierRep k (piecePlate k (2 ^ N) i) (f i))
    {r : ℝ} (hr : 1 ≤ r) (x : E k) :
    ((‖∑ i ∈ blkFin N 2 a, f i x‖₊ : NNReal) : ℝ≥0∞) ^ r
      ≤ (((2 ^ (m - 2) : ℕ) : ℝ≥0∞) ^ (r - 1))
        * ((uncConst k hk) ^ (r - 1)
          * (ENNReal.ofReal ((8 : ℝ) ^ (k * (k + 1) / 2))
            * ∑ q ∈ subBlk m a,
                convPow k r (fun y => ∑ i ∈ blkFin N m q, f i y)
                  (platePhi k hk (plateHalf m) (pieceCenter (2 ^ m) q)) x)) := by
  have hr0 : 0 ≤ r := le_trans zero_le_one hr
  have hsum : (∑ i ∈ blkFin N 2 a, f i x)
      = ∑ q ∈ subBlk m a, ∑ i ∈ blkFin N m q, f i x :=
    sum_blkFin_two hm hmN ha (fun i => f i x)
  have h2 : ((‖∑ i ∈ blkFin N 2 a, f i x‖₊ : NNReal) : ℝ≥0∞)
      ≤ ∑ q ∈ subBlk m a, ((‖∑ i ∈ blkFin N m q, f i x‖₊ : NNReal) : ℝ≥0∞) := by
    simp only [coe_nnnorm_eq_ofReal]
    rw [hsum]
    exact (ENNReal.ofReal_le_ofReal (norm_sum_le (subBlk m a)
        (fun q => (∑ i ∈ blkFin N m q, f i x : ℂ)))).trans
      (le_of_eq (ENNReal.ofReal_sum_of_nonneg (fun q _ => norm_nonneg _)))
  refine (ENNReal.rpow_le_rpow h2 hr0).trans ?_
  refine (Commons.Analysis.Inequalities.sum_rpow_le_card_rpow_mul_sum_rpow (subBlk m a)
    (fun q => ((‖∑ i ∈ blkFin N m q, f i x‖₊ : NNReal) : ℝ≥0∞)) hr).trans ?_
  rw [subBlk_card hm ha]
  have hkey : ∑ q ∈ subBlk m a, ((‖∑ i ∈ blkFin N m q, f i x‖₊ : NNReal) : ℝ≥0∞) ^ r
      ≤ (uncConst k hk) ^ (r - 1)
        * (ENNReal.ofReal ((8 : ℝ) ^ (k * (k + 1) / 2))
          * ∑ q ∈ subBlk m a,
              convPow k r (fun y => ∑ i ∈ blkFin N m q, f i y)
                (platePhi k hk (plateHalf m) (pieceCenter (2 ^ m) q)) x) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun q _ => ?_
    refine (norm_rpow_le_convPow_blocks hk hm hmN q f hf hr x).trans ?_
    exact le_of_eq (by ring)
  calc (((2 ^ (m - 2) : ℕ) : ℝ≥0∞) ^ (r - 1))
        * ∑ q ∈ subBlk m a, ((‖∑ i ∈ blkFin N m q, f i x‖₊ : NNReal) : ℝ≥0∞) ^ r
      ≤ (((2 ^ (m - 2) : ℕ) : ℝ≥0∞) ^ (r - 1))
        * ((uncConst k hk) ^ (r - 1)
          * (ENNReal.ofReal ((8 : ℝ) ^ (k * (k + 1) / 2))
            * ∑ q ∈ subBlk m a,
                convPow k r (fun y => ∑ i ∈ blkFin N m q, f i y)
                  (platePhi k hk (plateHalf m) (pieceCenter (2 ^ m) q)) x)) :=
        mul_le_mul_right hkey _


/-! ## 8. GLYZ Lemma 3.4: the symmetric constants are bounded by the asymmetric ones -/

lemma pkExp_pos {k : ℕ} (hk : 1 ≤ k) : 0 < pkExp k := by
  rw [pkExp]
  have h : (1 : ℝ) ≤ k := by exact_mod_cast hk
  nlinarith

lemma cast_le_sub_one {k l : ℕ} (hk : 1 ≤ k) (hlk : l ≤ k - 1) : (l : ℝ) ≤ (k : ℝ) - 1 := by
  have h4 : (l : ℝ) ≤ ((k - 1 : ℕ) : ℝ) := by exact_mod_cast hlk
  rw [Nat.cast_sub hk] at h4
  push_cast at h4
  exact h4

/-- The constant attached to the first (level-`m`) family in the uncertainty step. -/
noncomputable def asymConst₁ (k l m : ℕ) (hk : 1 ≤ k) : ℝ≥0∞ :=
  ((2 ^ (m - 2) : ℕ) : ℝ≥0∞) ^ (plExp l - 1) * (uncConst k hk) ^ (plExp l - 1)
    * ENNReal.ofReal ((8 : ℝ) ^ (k * (k + 1) / 2))

/-- The constant attached to the second (level-`m'`) family in the uncertainty step. -/
noncomputable def asymConst₂ (k l m' : ℕ) (hk : 1 ≤ k) : ℝ≥0∞ :=
  ((2 ^ (m' - 2) : ℕ) : ℝ≥0∞) ^ (pkExp k - plExp l - 1)
    * (uncConst k hk) ^ (pkExp k - plExp l - 1)
    * ENNReal.ofReal ((8 : ℝ) ^ (k * (k + 1) / 2))

/-- **GLYZ Lemma 3.4.**  The symmetric bilinear decoupling constant at coarse scale `1/4` is
bounded by the asymmetric one at the intermediate levels `m`, `m'`. -/
noncomputable def symDecConst (k l m m' : ℕ) (hk : 1 ≤ k) (C : ℝ≥0∞) : ℝ≥0∞ :=
  (asymConst₁ k l m hk * asymConst₂ k l m' hk * C ^ (pkExp k)) ^ (1 / pkExp k)

lemma symDecConst_pow {k l m m' : ℕ} (hk : 1 ≤ k) (C : ℝ≥0∞) :
    (symDecConst k l m m' hk C) ^ ((k : ℝ) * ((k : ℝ) + 1))
      = asymConst₁ k l m hk * asymConst₂ k l m' hk * C ^ ((k : ℝ) * ((k : ℝ) + 1)) := by
  rw [symDecConst, ← ENNReal.rpow_mul]
  rw [show (1 / pkExp k) * ((k : ℝ) * ((k : ℝ) + 1)) = 1 by
    rw [one_div, show ((k : ℝ) * ((k : ℝ) + 1)) = pkExp k from rfl,
      inv_mul_cancel₀ (ne_of_gt (pkExp_pos hk))]]
  rw [ENNReal.rpow_one]
  rfl

lemma pair_pointwise {k l N m m' : ℕ} (hk : 1 ≤ k) (hl : 1 ≤ l) (hlk : l ≤ k - 1)
    (hm : 2 ≤ m) (hmN : m ≤ N) (hm' : 2 ≤ m') (hm'N : m' ≤ N)
    (a a' : ℕ) (ha : a ≤ 3) (ha' : a' ≤ 3)
    (f : Fin (2 ^ N) → E k → ℂ) (hf : ∀ i, IsFourierRep k (piecePlate k (2 ^ N) i) (f i))
    (x : E k) :
    ((((‖∑ i ∈ blkFin N 2 a, f i x‖₊ : NNReal) : ℝ≥0∞) ^ (plExp l))
        * (((‖∑ i ∈ blkFin N 2 a', f i x‖₊ : NNReal) : ℝ≥0∞) ^ (pkExp k - plExp l)))
      ≤ (asymConst₁ k l m hk
            * (∑ q ∈ subBlk m a,
                convPow k (plExp l) (fun y => ∑ i ∈ blkFin N m q, f i y)
                  (platePhi k hk (plateHalf m) (pieceCenter (2 ^ m) q)) x))
        * (asymConst₂ k l m' hk
            * (∑ q' ∈ subBlk m' a',
                convPow k (pkExp k - plExp l) (fun y => ∑ i ∈ blkFin N m' q', f i y)
                  (platePhi k hk (plateHalf m') (pieceCenter (2 ^ m') q')) x)) := by
  have hr1 : 1 ≤ plExp l := by
    rw [plExp]
    have h : (1 : ℝ) ≤ l := by exact_mod_cast hl
    nlinarith
  have hrs : 1 ≤ pkExp k - plExp l := by
    have h1 : pkExp k - plExp l = ((k : ℝ) - l) * ((k : ℝ) + l + 1) := by
      rw [pkExp, plExp]; ring
    rw [h1]
    have hlkR := cast_le_sub_one hk hlk
    have hl0' : (0 : ℝ) ≤ l := Nat.cast_nonneg l
    nlinarith
  refine mul_le_mul' ?_ ?_
  · refine (quarter_pointwise hk hm hmN a ha f hf hr1 x).trans (le_of_eq ?_)
    rw [asymConst₁]
    ring
  · refine (quarter_pointwise hk hm' hm'N a' ha' f hf hrs x).trans (le_of_eq ?_)
    rw [asymConst₂]
    ring

lemma pair_pointwise_swap {k l N m₁ m₂ : ℕ} (hk : 1 ≤ k) (hl : 1 ≤ l) (hlk : l ≤ k - 1)
    (hm₁ : 2 ≤ m₁) (hm₁N : m₁ ≤ N) (hm₂ : 2 ≤ m₂) (hm₂N : m₂ ≤ N)
    (a₁ a₂ : ℕ) (ha₁ : a₁ ≤ 3) (ha₂ : a₂ ≤ 3)
    (f : Fin (2 ^ N) → E k → ℂ) (hf : ∀ i, IsFourierRep k (piecePlate k (2 ^ N) i) (f i))
    (x : E k) :
    ((((‖∑ i ∈ blkFin N 2 a₁, f i x‖₊ : NNReal) : ℝ≥0∞) ^ (pkExp k - plExp l))
        * (((‖∑ i ∈ blkFin N 2 a₂, f i x‖₊ : NNReal) : ℝ≥0∞) ^ (plExp l)))
      ≤ (asymConst₂ k l m₁ hk
            * (∑ q ∈ subBlk m₁ a₁,
                convPow k (pkExp k - plExp l) (fun y => ∑ i ∈ blkFin N m₁ q, f i y)
                  (platePhi k hk (plateHalf m₁) (pieceCenter (2 ^ m₁) q)) x))
        * (asymConst₁ k l m₂ hk
            * (∑ q' ∈ subBlk m₂ a₂,
                convPow k (plExp l) (fun y => ∑ i ∈ blkFin N m₂ q', f i y)
                  (platePhi k hk (plateHalf m₂) (pieceCenter (2 ^ m₂) q')) x)) := by
  have hr1 : 1 ≤ plExp l := by
    rw [plExp]
    have h : (1 : ℝ) ≤ l := by exact_mod_cast hl
    nlinarith
  have hrs : 1 ≤ pkExp k - plExp l := by
    have h1 : pkExp k - plExp l = ((k : ℝ) - l) * ((k : ℝ) + l + 1) := by
      rw [pkExp, plExp]; ring
    rw [h1]
    have hlkR := cast_le_sub_one hk hlk
    have hl0' : (0 : ℝ) ≤ l := Nat.cast_nonneg l
    nlinarith
  refine mul_le_mul' ?_ ?_
  · refine (quarter_pointwise hk hm₁ hm₁N a₁ ha₁ f hf hrs x).trans (le_of_eq ?_)
    rw [asymConst₂]
    ring
  · refine (quarter_pointwise hk hm₂ hm₂N a₂ ha₂ f hf hr1 x).trans (le_of_eq ?_)
    rw [asymConst₁]
    ring

lemma rpow_half_mul_rpow_half (A X Y : ℝ≥0∞) {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) :
    (A * (X ^ p * Y ^ q)) ^ (1/2:ℝ) * (A * (X ^ q * Y ^ p)) ^ (1/2:ℝ)
      = A * (X ^ ((p+q)/2) * Y ^ ((p+q)/2)) := by
  rw [← ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 1/2)]
  rw [show (A * (X ^ p * Y ^ q)) * (A * (X ^ q * Y ^ p))
      = (A ^ (2:ℝ)) * (X ^ (p + q)) * (Y ^ (p + q)) from by
    rw [show (A ^ (2:ℝ)) = A * A from by rw [ENNReal.rpow_two]; ring]
    rw [show X ^ (p + q) = X ^ p * X ^ q from ENNReal.rpow_add_of_nonneg _ _ hp hq,
      show Y ^ (p + q) = Y ^ q * Y ^ p from by
        rw [show p + q = q + p from by ring, ENNReal.rpow_add_of_nonneg _ _ hq hp]]
    ring]
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 1/2),
    ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 1/2)]
  rw [← ENNReal.rpow_mul, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
  rw [show (2:ℝ) * (1/2) = 1 by norm_num, ENNReal.rpow_one]
  rw [show (p + q) * (1/2) = (p + q) / 2 from by ring]
  rw [mul_assoc]

theorem symDec_of_asymDec {k l N m m' : ℕ} (hk : 1 ≤ k) (hl : 1 ≤ l) (hlk : l ≤ k - 1)
    (hm : 2 ≤ m) (hmN : m ≤ N) (hm' : 2 ≤ m') (hm'N : m' ≤ N) {C : ℝ≥0∞}
    (hA : AsymDec k hk l N m m' C) :
    SymDec k N (symDecConst k l m m' hk C) := by
  intro a' ha' f hf
  have ha'3 : (a' : ℕ) ≤ 3 := by have := a'.isLt; omega
  have hl0 : (0 : ℝ) ≤ plExp l := plExp_nonneg l
  have hr0 : (0 : ℝ) ≤ pkExp k - plExp l := pkExp_sub_plExp_nonneg (by omega : l ≤ k)
  have hpl2 : 2 ≤ plExp l := by
    rw [plExp]
    have h : (1 : ℝ) ≤ l := by exact_mod_cast hl
    nlinarith
  have hpkpl2 : 2 ≤ pkExp k - plExp l := by
    have h1 : pkExp k - plExp l = ((k : ℝ) - l) * ((k : ℝ) + l + 1) := by
      rw [pkExp, plExp]; ring
    rw [h1]
    have hlkR := cast_le_sub_one hk hlk
    have hl0' : (0 : ℝ) ≤ l := Nat.cast_nonneg l
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
    nlinarith
  have hpk1 : 1 ≤ pkExp k - plExp l := le_trans (by norm_num) hpkpl2
  set Aa : Fin (2 ^ N) → ℝ≥0∞ := fun i => lpNorm k (pE k) (f i) with hAa
  set L0 := l2Of (blkFin N 2 0) Aa with hL0
  set La := l2Of (blkFin N 2 (a' : ℕ)) Aa with hLa
  set A0 : E k → ℝ≥0∞ := fun x => ((‖∑ i ∈ blkFin N 2 0, f i x‖₊ : NNReal) : ℝ≥0∞) with hA0
  set Ba : E k → ℝ≥0∞ := fun x => ((‖∑ i ∈ blkFin N 2 (a' : ℕ), f i x‖₊ : NNReal) : ℝ≥0∞) with hBa
  rw [symDecConst_pow hk C]
  have hcont0 : Continuous (fun y : E k => ∑ i ∈ blkFin N 2 0, f i y) :=
    continuous_finsetSum _ (fun i _ => (hf i).continuous)
  have hconta : Continuous (fun y : E k => ∑ i ∈ blkFin N 2 (a' : ℕ), f i y) :=
    continuous_finsetSum _ (fun i _ => (hf i).continuous)
  have hme0 : AEMeasurable A0 volume :=
    ((hcont0.nnnorm.measurable).coe_nnreal_ennreal).aemeasurable
  have hmea : AEMeasurable Ba volume :=
    ((hconta.nnnorm.measurable).coe_nnreal_ennreal).aemeasurable
  have hcontblk : ∀ (mm : ℕ) (q : ℕ), Continuous (fun y : E k => ∑ i ∈ blkFin N mm q, f i y) :=
    fun mm q => continuous_finsetSum _ (fun i _ => (hf i).continuous)
  have hkey1 : ∫⁻ x, A0 x ^ (plExp l) * Ba x ^ (pkExp k - plExp l)
      ≤ (asymConst₁ k l m hk * asymConst₂ k l m' hk * C ^ (pkExp k))
        * (L0 ^ (plExp l) * La ^ (pkExp k - plExp l)) := by
    have hpt : (fun x : E k => A0 x ^ (plExp l) * Ba x ^ (pkExp k - plExp l))
        ≤ fun x : E k => (asymConst₁ k l m hk
              * (∑ q ∈ subBlk m 0,
                  convPow k (plExp l) (fun y => ∑ i ∈ blkFin N m q, f i y)
                    (platePhi k hk (plateHalf m) (pieceCenter (2 ^ m) q)) x))
            * (asymConst₂ k l m' hk
              * (∑ q' ∈ subBlk m' (a' : ℕ),
                  convPow k (pkExp k - plExp l) (fun y => ∑ i ∈ blkFin N m' q', f i y)
                    (platePhi k hk (plateHalf m') (pieceCenter (2 ^ m') q')) x)) :=
      fun x => pair_pointwise hk hl hlk hm hmN hm' hm'N 0 (a' : ℕ) (by norm_num) ha'3 f hf x
    have hmeasU : ∀ q ∈ subBlk m 0, Measurable (fun x : E k =>
        convPow k (plExp l) (fun y => ∑ i ∈ blkFin N m q, f i y)
          (platePhi k hk (plateHalf m) (pieceCenter (2 ^ m) q)) x) :=
      fun q _ => measurable_convPow k (plExp l) (hcontblk m q).measurable
        (continuous_platePhi k hk (plateHalf m) (pieceCenter (2 ^ m) q)).measurable
    have hmeasV : ∀ q' ∈ subBlk m' (a' : ℕ), Measurable (fun x : E k =>
        convPow k (pkExp k - plExp l) (fun y => ∑ i ∈ blkFin N m' q', f i y)
          (platePhi k hk (plateHalf m') (pieceCenter (2 ^ m') q')) x) :=
      fun q' _ => measurable_convPow k (pkExp k - plExp l) (hcontblk m' q').measurable
        (continuous_platePhi k hk (plateHalf m') (pieceCenter (2 ^ m') q')).measurable
    have hmeasW : Measurable (fun x : E k =>
        (∑ q ∈ subBlk m 0,
            convPow k (plExp l) (fun y => ∑ i ∈ blkFin N m q, f i y)
              (platePhi k hk (plateHalf m) (pieceCenter (2 ^ m) q)) x)
          * (∑ q' ∈ subBlk m' (a' : ℕ),
              convPow k (pkExp k - plExp l) (fun y => ∑ i ∈ blkFin N m' q', f i y)
                (platePhi k hk (plateHalf m') (pieceCenter (2 ^ m') q')) x)) :=
      (Finset.measurable_sum _ hmeasU).mul (Finset.measurable_sum _ hmeasV)
    have hpair : ∑ q ∈ subBlk m 0, ∑ q' ∈ subBlk m' (a' : ℕ),
          ∫⁻ x, (convPow k (plExp l) (fun y => ∑ i ∈ blkFin N m q, f i y)
                (platePhi k hk (plateHalf m) (pieceCenter (2 ^ m) q)) x)
            * (convPow k (pkExp k - plExp l) (fun y => ∑ i ∈ blkFin N m' q', f i y)
                (platePhi k hk (plateHalf m') (pieceCenter (2 ^ m') q')) x)
        ≤ C ^ (pkExp k) * (L0 ^ (plExp l) * La ^ (pkExp k - plExp l)) := by
      have hstep1 : ∑ q ∈ subBlk m 0, ∑ q' ∈ subBlk m' (a' : ℕ),
            ∫⁻ x, (convPow k (plExp l) (fun y => ∑ i ∈ blkFin N m q, f i y)
                  (platePhi k hk (plateHalf m) (pieceCenter (2 ^ m) q)) x)
              * (convPow k (pkExp k - plExp l) (fun y => ∑ i ∈ blkFin N m' q', f i y)
                  (platePhi k hk (plateHalf m') (pieceCenter (2 ^ m') q')) x)
          ≤ ∑ q ∈ subBlk m 0, ∑ q' ∈ subBlk m' (a' : ℕ),
              C ^ (pkExp k) * ((l2Of (blkFin N m q) Aa) ^ (plExp l)
                * (l2Of (blkFin N m' q') Aa) ^ (pkExp k - plExp l)) := by
        refine Finset.sum_le_sum fun q hq => Finset.sum_le_sum fun q' hq' => ?_
        exact (hA q q' (sepLevel_of_subBlk hm hm' ha' ha'3 q hq q' hq') f hf).trans
          (le_of_eq (by ring))
      have hstep2 : ∑ q ∈ subBlk m 0, ∑ q' ∈ subBlk m' (a' : ℕ),
              C ^ (pkExp k) * ((l2Of (blkFin N m q) Aa) ^ (plExp l)
                * (l2Of (blkFin N m' q') Aa) ^ (pkExp k - plExp l))
          = C ^ (pkExp k) * ((∑ q ∈ subBlk m 0, (l2Of (blkFin N m q) Aa) ^ (plExp l))
              * (∑ q' ∈ subBlk m' (a' : ℕ),
                  (l2Of (blkFin N m' q') Aa) ^ (pkExp k - plExp l))) := by
        rw [Finset.sum_mul_sum]
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [Finset.mul_sum]
      have hstep3 : (∑ q ∈ subBlk m 0, (l2Of (blkFin N m q) Aa) ^ (plExp l))
            * (∑ q' ∈ subBlk m' (a' : ℕ),
                (l2Of (blkFin N m' q') Aa) ^ (pkExp k - plExp l))
          ≤ L0 ^ (plExp l) * La ^ (pkExp k - plExp l) :=
        mul_le_mul' (sum_l2Of_subBlk_le hm hmN (by norm_num) Aa hpl2)
          (sum_l2Of_subBlk_le hm' hm'N ha'3 Aa hpkpl2)
      exact hstep1.trans ((le_of_eq hstep2).trans (mul_le_mul_right hstep3 _))
    refine (lintegral_mono hpt).trans ?_
    calc ∫⁻ x, (asymConst₁ k l m hk
              * (∑ q ∈ subBlk m 0,
                  convPow k (plExp l) (fun y => ∑ i ∈ blkFin N m q, f i y)
                    (platePhi k hk (plateHalf m) (pieceCenter (2 ^ m) q)) x))
            * (asymConst₂ k l m' hk
              * (∑ q' ∈ subBlk m' (a' : ℕ),
                  convPow k (pkExp k - plExp l) (fun y => ∑ i ∈ blkFin N m' q', f i y)
                    (platePhi k hk (plateHalf m') (pieceCenter (2 ^ m') q')) x))
        = ∫⁻ x, (asymConst₁ k l m hk * asymConst₂ k l m' hk)
            * ((∑ q ∈ subBlk m 0,
                  convPow k (plExp l) (fun y => ∑ i ∈ blkFin N m q, f i y)
                    (platePhi k hk (plateHalf m) (pieceCenter (2 ^ m) q)) x)
              * (∑ q' ∈ subBlk m' (a' : ℕ),
                  convPow k (pkExp k - plExp l) (fun y => ∑ i ∈ blkFin N m' q', f i y)
                    (platePhi k hk (plateHalf m') (pieceCenter (2 ^ m') q')) x)) := by
          refine lintegral_congr fun x => ?_
          ring
      _ = (asymConst₁ k l m hk * asymConst₂ k l m' hk)
            * ∫⁻ x, ((∑ q ∈ subBlk m 0,
                  convPow k (plExp l) (fun y => ∑ i ∈ blkFin N m q, f i y)
                    (platePhi k hk (plateHalf m) (pieceCenter (2 ^ m) q)) x)
              * (∑ q' ∈ subBlk m' (a' : ℕ),
                  convPow k (pkExp k - plExp l) (fun y => ∑ i ∈ blkFin N m' q', f i y)
                    (platePhi k hk (plateHalf m') (pieceCenter (2 ^ m') q')) x)) :=
          lintegral_const_mul _ hmeasW
      _ = (asymConst₁ k l m hk * asymConst₂ k l m' hk)
            * (∑ q ∈ subBlk m 0, ∑ q' ∈ subBlk m' (a' : ℕ),
                ∫⁻ x, (convPow k (plExp l) (fun y => ∑ i ∈ blkFin N m q, f i y)
                      (platePhi k hk (plateHalf m) (pieceCenter (2 ^ m) q)) x)
                  * (convPow k (pkExp k - plExp l) (fun y => ∑ i ∈ blkFin N m' q', f i y)
                      (platePhi k hk (plateHalf m') (pieceCenter (2 ^ m') q')) x)) := by
          rw [Commons.Measure.Integral.lintegral_finsetSum_mul_finsetSum_measurable
            volume _ _ _ _ hmeasU hmeasV]
      _ ≤ (asymConst₁ k l m hk * asymConst₂ k l m' hk)
            * (C ^ (pkExp k) * (L0 ^ (plExp l) * La ^ (pkExp k - plExp l))) :=
          mul_le_mul_right hpair _
      _ = (asymConst₁ k l m hk * asymConst₂ k l m' hk * C ^ (pkExp k))
            * (L0 ^ (plExp l) * La ^ (pkExp k - plExp l)) := by ring
  have hkey2 : ∫⁻ x, A0 x ^ (pkExp k - plExp l) * Ba x ^ (plExp l)
      ≤ (asymConst₁ k l m hk * asymConst₂ k l m' hk * C ^ (pkExp k))
        * (L0 ^ (pkExp k - plExp l) * La ^ (plExp l)) := by
    have hpt : (fun x : E k => A0 x ^ (pkExp k - plExp l) * Ba x ^ (plExp l))
        ≤ fun x : E k => (asymConst₂ k l m' hk
              * (∑ q ∈ subBlk m' 0,
                  convPow k (pkExp k - plExp l) (fun y => ∑ i ∈ blkFin N m' q, f i y)
                    (platePhi k hk (plateHalf m') (pieceCenter (2 ^ m') q)) x))
            * (asymConst₁ k l m hk
              * (∑ q' ∈ subBlk m (a' : ℕ),
                  convPow k (plExp l) (fun y => ∑ i ∈ blkFin N m q', f i y)
                    (platePhi k hk (plateHalf m) (pieceCenter (2 ^ m) q')) x)) :=
      fun x => pair_pointwise_swap hk hl hlk hm' hm'N hm hmN 0 (a' : ℕ) (by norm_num) ha'3
        f hf x
    have hmeasU : ∀ q ∈ subBlk m' 0, Measurable (fun x : E k =>
        convPow k (pkExp k - plExp l) (fun y => ∑ i ∈ blkFin N m' q, f i y)
          (platePhi k hk (plateHalf m') (pieceCenter (2 ^ m') q)) x) :=
      fun q _ => measurable_convPow k (pkExp k - plExp l) (hcontblk m' q).measurable
        (continuous_platePhi k hk (plateHalf m') (pieceCenter (2 ^ m') q)).measurable
    have hmeasV : ∀ q' ∈ subBlk m (a' : ℕ), Measurable (fun x : E k =>
        convPow k (plExp l) (fun y => ∑ i ∈ blkFin N m q', f i y)
          (platePhi k hk (plateHalf m) (pieceCenter (2 ^ m) q')) x) :=
      fun q' _ => measurable_convPow k (plExp l) (hcontblk m q').measurable
        (continuous_platePhi k hk (plateHalf m) (pieceCenter (2 ^ m) q')).measurable
    have hmeasW : Measurable (fun x : E k =>
        (∑ q ∈ subBlk m' 0,
            convPow k (pkExp k - plExp l) (fun y => ∑ i ∈ blkFin N m' q, f i y)
              (platePhi k hk (plateHalf m') (pieceCenter (2 ^ m') q)) x)
          * (∑ q' ∈ subBlk m (a' : ℕ),
              convPow k (plExp l) (fun y => ∑ i ∈ blkFin N m q', f i y)
                (platePhi k hk (plateHalf m) (pieceCenter (2 ^ m) q')) x)) :=
      (Finset.measurable_sum _ hmeasU).mul (Finset.measurable_sum _ hmeasV)
    have hpair : ∑ q ∈ subBlk m' 0, ∑ q' ∈ subBlk m (a' : ℕ),
          ∫⁻ x, (convPow k (pkExp k - plExp l) (fun y => ∑ i ∈ blkFin N m' q, f i y)
                (platePhi k hk (plateHalf m') (pieceCenter (2 ^ m') q)) x)
            * (convPow k (plExp l) (fun y => ∑ i ∈ blkFin N m q', f i y)
                (platePhi k hk (plateHalf m) (pieceCenter (2 ^ m) q')) x)
        ≤ C ^ (pkExp k) * (L0 ^ (pkExp k - plExp l) * La ^ (plExp l)) := by
      have hstep1 : ∑ q ∈ subBlk m' 0, ∑ q' ∈ subBlk m (a' : ℕ),
            ∫⁻ x, (convPow k (pkExp k - plExp l) (fun y => ∑ i ∈ blkFin N m' q, f i y)
                  (platePhi k hk (plateHalf m') (pieceCenter (2 ^ m') q)) x)
              * (convPow k (plExp l) (fun y => ∑ i ∈ blkFin N m q', f i y)
                  (platePhi k hk (plateHalf m) (pieceCenter (2 ^ m) q')) x)
          ≤ ∑ q ∈ subBlk m' 0, ∑ q' ∈ subBlk m (a' : ℕ),
              C ^ (pkExp k) * ((l2Of (blkFin N m' q) Aa) ^ (pkExp k - plExp l)
                * (l2Of (blkFin N m q') Aa) ^ (plExp l)) := by
        refine Finset.sum_le_sum fun q hq => Finset.sum_le_sum fun q' hq' => ?_
        have h1 : (∫⁻ x, (convPow k (pkExp k - plExp l) (fun y => ∑ i ∈ blkFin N m' q, f i y)
                  (platePhi k hk (plateHalf m') (pieceCenter (2 ^ m') q)) x)
              * (convPow k (plExp l) (fun y => ∑ i ∈ blkFin N m q', f i y)
                  (platePhi k hk (plateHalf m) (pieceCenter (2 ^ m) q')) x))
            = ∫⁻ x, (convPow k (plExp l) (fun y => ∑ i ∈ blkFin N m q', f i y)
                  (platePhi k hk (plateHalf m) (pieceCenter (2 ^ m) q')) x)
              * (convPow k (pkExp k - plExp l) (fun y => ∑ i ∈ blkFin N m' q, f i y)
                  (platePhi k hk (plateHalf m') (pieceCenter (2 ^ m') q)) x) :=
          lintegral_congr fun x => mul_comm _ _
        rw [h1]
        exact (hA q' q (sepLevel_of_subBlk' hm hm' ha' ha'3 q' hq' q hq) f hf).trans
          (le_of_eq (by ring))
      have hstep2 : ∑ q ∈ subBlk m' 0, ∑ q' ∈ subBlk m (a' : ℕ),
              C ^ (pkExp k) * ((l2Of (blkFin N m' q) Aa) ^ (pkExp k - plExp l)
                * (l2Of (blkFin N m q') Aa) ^ (plExp l))
          = C ^ (pkExp k) * ((∑ q ∈ subBlk m' 0,
                (l2Of (blkFin N m' q) Aa) ^ (pkExp k - plExp l))
              * (∑ q' ∈ subBlk m (a' : ℕ),
                  (l2Of (blkFin N m q') Aa) ^ (plExp l))) := by
        rw [Finset.sum_mul_sum]
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [Finset.mul_sum]
      have hstep3 : (∑ q ∈ subBlk m' 0, (l2Of (blkFin N m' q) Aa) ^ (pkExp k - plExp l))
            * (∑ q' ∈ subBlk m (a' : ℕ), (l2Of (blkFin N m q') Aa) ^ (plExp l))
          ≤ L0 ^ (pkExp k - plExp l) * La ^ (plExp l) :=
        mul_le_mul' (sum_l2Of_subBlk_le hm' hm'N (by norm_num) Aa hpkpl2)
          (sum_l2Of_subBlk_le hm hmN ha'3 Aa hpl2)
      exact hstep1.trans ((le_of_eq hstep2).trans (mul_le_mul_right hstep3 _))
    refine (lintegral_mono hpt).trans ?_
    calc ∫⁻ x, (asymConst₂ k l m' hk
              * (∑ q ∈ subBlk m' 0,
                  convPow k (pkExp k - plExp l) (fun y => ∑ i ∈ blkFin N m' q, f i y)
                    (platePhi k hk (plateHalf m') (pieceCenter (2 ^ m') q)) x))
            * (asymConst₁ k l m hk
              * (∑ q' ∈ subBlk m (a' : ℕ),
                  convPow k (plExp l) (fun y => ∑ i ∈ blkFin N m q', f i y)
                    (platePhi k hk (plateHalf m) (pieceCenter (2 ^ m) q')) x))
        = ∫⁻ x, (asymConst₂ k l m' hk * asymConst₁ k l m hk)
            * ((∑ q ∈ subBlk m' 0,
                  convPow k (pkExp k - plExp l) (fun y => ∑ i ∈ blkFin N m' q, f i y)
                    (platePhi k hk (plateHalf m') (pieceCenter (2 ^ m') q)) x)
              * (∑ q' ∈ subBlk m (a' : ℕ),
                  convPow k (plExp l) (fun y => ∑ i ∈ blkFin N m q', f i y)
                    (platePhi k hk (plateHalf m) (pieceCenter (2 ^ m) q')) x)) := by
          refine lintegral_congr fun x => ?_
          ring
      _ = (asymConst₂ k l m' hk * asymConst₁ k l m hk)
            * ∫⁻ x, ((∑ q ∈ subBlk m' 0,
                  convPow k (pkExp k - plExp l) (fun y => ∑ i ∈ blkFin N m' q, f i y)
                    (platePhi k hk (plateHalf m') (pieceCenter (2 ^ m') q)) x)
              * (∑ q' ∈ subBlk m (a' : ℕ),
                  convPow k (plExp l) (fun y => ∑ i ∈ blkFin N m q', f i y)
                    (platePhi k hk (plateHalf m) (pieceCenter (2 ^ m) q')) x)) :=
          lintegral_const_mul _ hmeasW
      _ = (asymConst₂ k l m' hk * asymConst₁ k l m hk)
            * (∑ q ∈ subBlk m' 0, ∑ q' ∈ subBlk m (a' : ℕ),
                ∫⁻ x, (convPow k (pkExp k - plExp l) (fun y => ∑ i ∈ blkFin N m' q, f i y)
                      (platePhi k hk (plateHalf m') (pieceCenter (2 ^ m') q)) x)
                  * (convPow k (plExp l) (fun y => ∑ i ∈ blkFin N m q', f i y)
                      (platePhi k hk (plateHalf m) (pieceCenter (2 ^ m) q')) x)) := by
          rw [Commons.Measure.Integral.lintegral_finsetSum_mul_finsetSum_measurable
            volume _ _ _ _ hmeasU hmeasV]
      _ ≤ (asymConst₂ k l m' hk * asymConst₁ k l m hk)
            * (C ^ (pkExp k) * (L0 ^ (pkExp k - plExp l) * La ^ (plExp l))) :=
          mul_le_mul_right hpair _
      _ = (asymConst₁ k l m hk * asymConst₂ k l m' hk * C ^ (pkExp k))
            * (L0 ^ (pkExp k - plExp l) * La ^ (plExp l)) := by ring
  have hHol := Commons.Measure.Integral.lintegral_rpow_split_le (μ := (volume : Measure (E k)))
    (A := A0) (B := Ba) hme0 hmea (a := plExp l) (b := pkExp k - plExp l) hl0 hr0
  rw [show plExp l + (pkExp k - plExp l) = pkExp k from by ring] at hHol
  refine hHol.trans ?_
  have hZ1 := ENNReal.rpow_le_rpow hkey1 (by norm_num : (0:ℝ) ≤ 1/2)
  have hZ2 := ENNReal.rpow_le_rpow hkey2 (by norm_num : (0:ℝ) ≤ 1/2)
  refine (mul_le_mul' hZ1 hZ2).trans (le_of_eq ?_)
  rw [rpow_half_mul_rpow_half
    (asymConst₁ k l m hk * asymConst₂ k l m' hk * C ^ (pkExp k)) L0 La hl0 hr0]
  rw [show plExp l + (pkExp k - plExp l) = pkExp k from by ring]
  simp only [pkExp]
  ring

end Submission.Vinogradov