import Mathlib
import Submission.Work.BMF.adi_all_defs
import Submission.Work.BMF.bike_adi_side
import Submission.Work.BMF.adi_crt
import Submission.Work.BMF.walk_closure
import Submission.Work.BMF.walk_closure_all
import Submission.Work.BMF.bikeSetAll_bridge
import Submission.Work.BMF.GAdjQ_iff_stepS_or
import Submission.Work.BMF.polyrel_walk_maxmin
import Submission.Work.BMF.walk_prod_bounds

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `Work.BMF.good_bike_adi`

The bridge from a *good bicycle* of the quadruple graph (MRTTZ, MRT §4) to the approximate
dilation invariance data `ADIEdge` of the graph-theoretic stage (MRTTZ Prop. 3.7).

A good bicycle consists of an arc `e = t.1` of `D.edges` together with a closed walk `t.2.1`
through `e.x₁` and a closed walk `t.2.2` through `e.x₂`, such that

* both walks are non-degenerate: the source- and target-products along the walk differ by
  `≫ P₁^ℓ/N` (`¬ degenerateAt`),
* the bicycle is very good: the set `S = bikePrimesQ D ℓ t` of primes in `[P₂/2, P₂]` carried by
  every arc of the bicycle has `#S ≫ π₀(P₂)`.

For such a bicycle, the pair `(aᵢ, bᵢ) = (max, min)` of the source- and target-products of the
`i`-th walk satisfies `aᵢ - bᵢ ≍ aᵢ/N`: the lower bound is the non-degeneracy hypothesis, the
upper bound is the closure estimate `walk_closure_all` for walks of the quadruple graph.  The
approximate dilation invariance `P_{xᵢ}(aᵢ ·) ~_{1/∏S} P_{xᵢ}(bᵢ ·)` is `bike_adi_side` applied
to the closed walk, and the edge relation of `e` modulo `1/∏S` comes from the Chinese remainder
property `polyRel_crt` applied to the `(1/p)`-relations supplied by `D.rel` for the primes
`p ∈ S ⊆ edgeS D e`.

Note that `S ⊆ edgeS D e` holds by construction of `bikePrimesQ`, so the *same* prime set works
for all three relations of `ADIEdge`, which is what `ADIEdge` requires.
-/

namespace Work.BMF

open Polynomial Finset Real

/-! ## Auxiliary lemmas -/

/-- `IsPrimeIn a b p` from membership in the explicit finset `primesIn a b`. -/
lemma isPrimeIn_of_mem_primesIn {a b : ℝ} {p : ℕ} (h : p ∈ primesIn a b) : IsPrimeIn a b p := by
  rw [primesIn, Finset.mem_filter] at h
  obtain ⟨hmem, hp⟩ := h
  rw [natIcc, Finset.mem_Icc] at hmem
  exact ⟨hp, Nat.le_of_ceil_le hmem.1, (Nat.le_floor_iff' hp.ne_zero).mp hmem.2⟩

/-- `π₀(P) = P / log P` is positive for `P ≥ 2`. -/
lemma pi0_pos_of_two_le {P : ℝ} (hP : 2 ≤ P) : 0 < pi0 P := by
  rw [pi0]
  exact div_pos (by linarith) (Real.log_pos (by linarith))

/-- `max v u - min v u = |v - u|` for real numbers. -/
lemma max_sub_min_eq_abs (v u : ℝ) : max v u - min v u = |v - u| := by
  rcases le_total u v with h | h
  · rw [max_eq_left h, min_eq_right h, abs_of_nonneg (sub_nonneg.mpr h)]
  · rw [max_eq_right h, min_eq_left h, abs_of_nonpos (sub_nonpos.mpr h)]
    ring

/-- The gap between the maximum and the minimum of two naturals is their absolute difference. -/
lemma max_cast_sub_min_cast_eq_abs (v u : ℕ) :
    ((max v u : ℕ) : ℝ) - ((min v u : ℕ) : ℝ) = |((v : ℕ) : ℝ) - ((u : ℕ) : ℝ)| := by
  rw [Nat.cast_max, Nat.cast_min]
  exact max_sub_min_eq_abs v u

/-- The main auxiliary step: a non-degenerate closed walk of the `q`-subgraph together with a
prime set `S` carried by all of its steps produces the dilation pair `(a,b) = (max, min)` of the
walk's source- and target-products, with all the properties required by `ADIEdge`. -/
private theorem walk_adi_pair {k ℓ : ℕ} {f : ℕ → ℂ} {c C X L P₁ P₂ c₅ : ℝ}
    (D : QuadData k f c C X L P₁ P₂) (hC : 0 < C) (hP : 0 < P₁) (hL : 0 < L)
    (hX : 0 < X) (hbig : 8000 * P₁ ^ 2 < X / L) (hL1 : 1 ≤ L / (2 * P₁))
    (hLbig : 2 * symmConst k (max C (symmConst k C)) * ((k : ℝ) + 1) * (k : ℝ) ^ k *
      (k.factorial : ℝ) < L / (2 * P₁))
    (hc₅ : 0 < c₅) {q : ℕ} {x : ℝ} {W : Fin (ℓ + 1) → GVert D}
    (hW : W ∈ closedWalkVal D q ℓ x)
    (hnd : ¬ degenerateAt (X / L) c₅ P₁ D ℓ W)
    {S : Finset ℕ} (hSne : S.Nonempty) (hSprime : ∀ p ∈ S, p.Prime)
    (hstep : ∀ p ∈ S, ∀ j : Fin ℓ,
      p ∈ stepS D (W j.castSucc) (W j.succ) ∨ p ∈ stepS D (W j.succ) (W j.castSucc))
    {C' : ℝ}
    (hC'big : max (max (cycConst k (symmConst k (max C (symmConst k C))) ℓ)
        (symmConst k (cycConst k (symmConst k (max C (symmConst k C))) ℓ)))
      (max ((2 : ℝ) ^ ℓ / c₅) ((10 : ℝ) ^ 5 * (4 : ℝ) ^ ℓ)) ≤ C') :
    ∃ a b : ℕ, P₁ ^ ℓ ≤ (b : ℝ) ∧ b < a ∧ (a : ℝ) ≤ (2 * P₁) ^ ℓ ∧
      (a : ℝ) ≤ C' * (X / L) * ((a : ℝ) - b) ∧ (X / L) * ((a : ℝ) - b) ≤ C' * a ∧
      PolyRel k C' (1 / ((S.prod (fun p => p) : ℕ) : ℝ))
        (x / (a : ℝ)) (L / (a : ℝ)) (dil (a : ℝ) (D.pol x))
        (x / (b : ℝ)) (L / (b : ℝ)) (dil (b : ℝ) (D.pol x)) := by
  classical
  have hNpos : (0 : ℝ) < X / L := div_pos hX hL
  set d : ℝ := |((walkProdV D ℓ W : ℕ) : ℝ) - ((walkProdU D ℓ W : ℕ) : ℝ)| with hddef
  obtain ⟨hVlo, hVhi, hUlo, hUhi, hVpos, hUpos⟩ := walk_prod_bounds D hP hW
  -- non-degeneracy: `d` is bounded below
  have hd_low : c₅ * P₁ ^ ℓ / (X / L) < d := by
    rw [hddef]
    rw [degenerateAt] at hnd
    exact not_le.mp hnd
  have hd_pos : 0 < d := lt_of_lt_of_le (by positivity) hd_low.le
  have hVU : walkProdV D ℓ W ≠ walkProdU D ℓ W := by
    rw [hddef] at hd_pos
    intro h
    rw [h, sub_self, abs_zero] at hd_pos
    exact lt_irrefl 0 hd_pos
  have hb_lt_a : min (walkProdV D ℓ W) (walkProdU D ℓ W) <
      max (walkProdV D ℓ W) (walkProdU D ℓ W) := by
    rcases lt_or_gt_of_ne hVU with h | h
    · exact lt_of_le_of_lt (min_le_left _ _) (lt_of_lt_of_le h (le_max_right _ _))
    · exact lt_of_le_of_lt (min_le_right _ _) (lt_of_lt_of_le h (le_max_left _ _))
  -- closure: `d` is bounded above
  obtain ⟨hWset, hWlast, -⟩ := Finset.mem_filter.mp hW
  obtain ⟨-, hadj⟩ := Finset.mem_filter.mp hWset
  have hclos : d ≤ (10 : ℝ) ^ 5 * (4 : ℝ) ^ ℓ * P₁ ^ ℓ / (X / L) := by
    rw [hddef]
    exact walk_closure k f c C X L P₁ P₂ D hP hL hX q ℓ hWlast.symm hadj
  have hgeo : (X / L) * d ≤ (10 : ℝ) ^ 5 * (4 : ℝ) ^ ℓ * P₁ ^ ℓ := by
    have h1 : (X / L) * d ≤ (X / L) * ((10 : ℝ) ^ 5 * (4 : ℝ) ^ ℓ * P₁ ^ ℓ / (X / L)) :=
      mul_le_mul_of_nonneg_left hclos hNpos.le
    have h2 : (X / L) * ((10 : ℝ) ^ 5 * (4 : ℝ) ^ ℓ * P₁ ^ ℓ / (X / L))
        = (10 : ℝ) ^ 5 * (4 : ℝ) ^ ℓ * P₁ ^ ℓ := by
      field_simp
    linarith [h1, h2.le, h2.ge]
  -- the two constant bounds
  have hC'div : (2 : ℝ) ^ ℓ / c₅ ≤ C' :=
    le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hC'big)
  have hC'geo : (10 : ℝ) ^ 5 * (4 : ℝ) ^ ℓ ≤ C' :=
    le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hC'big)
  have hC'mid : max (cycConst k (symmConst k (max C (symmConst k C))) ℓ)
      (symmConst k (cycConst k (symmConst k (max C (symmConst k C))) ℓ)) ≤ C' :=
    le_trans (le_max_left _ _) hC'big
  have hC'nn : 0 ≤ C' :=
    le_trans (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ ℓ / c₅) hC'div
  refine ⟨max (walkProdV D ℓ W) (walkProdU D ℓ W),
    min (walkProdV D ℓ W) (walkProdU D ℓ W), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Nat.cast_min]
    exact le_min hVlo hUlo
  · exact hb_lt_a
  · rw [Nat.cast_max]
    exact max_le hVhi hUhi
  · -- lower bound for the gap
    have hdiff : ((max (walkProdV D ℓ W) (walkProdU D ℓ W) : ℕ) : ℝ) -
        ((min (walkProdV D ℓ W) (walkProdU D ℓ W) : ℕ) : ℝ) = d := by
      rw [hddef]
      rw [Nat.cast_max, Nat.cast_min]
      exact max_sub_min_eq_abs _ _
    have hd_low' : c₅ * P₁ ^ ℓ < d * (X / L) := by
      have h := (div_lt_iff₀ hNpos).mp hd_low
      linarith [h]
    have ha_le : ((max (walkProdV D ℓ W) (walkProdU D ℓ W) : ℕ) : ℝ) ≤ (2 * P₁) ^ ℓ := by
      rw [Nat.cast_max]
      exact max_le hVhi hUhi
    have hkey : (2 * P₁) ^ ℓ ≤ C' * (X / L) * d := by
      calc (2 * P₁) ^ ℓ = (2 : ℝ) ^ ℓ * P₁ ^ ℓ := by rw [mul_pow]
        _ = ((2 : ℝ) ^ ℓ / c₅) * (c₅ * P₁ ^ ℓ) := by
              field_simp
        _ ≤ ((2 : ℝ) ^ ℓ / c₅) * (d * (X / L)) :=
              mul_le_mul_of_nonneg_left hd_low'.le (by positivity)
        _ ≤ C' * (d * (X / L)) := mul_le_mul_of_nonneg_right hC'div (by positivity)
        _ = C' * (X / L) * d := by ring
    rw [hdiff]
    exact le_trans ha_le hkey
  · -- upper bound for the gap
    have hdiff : ((max (walkProdV D ℓ W) (walkProdU D ℓ W) : ℕ) : ℝ) -
        ((min (walkProdV D ℓ W) (walkProdU D ℓ W) : ℕ) : ℝ) = d := by
      rw [hddef]
      rw [Nat.cast_max, Nat.cast_min]
      exact max_sub_min_eq_abs _ _
    have ha_ge : P₁ ^ ℓ ≤ ((max (walkProdV D ℓ W) (walkProdU D ℓ W) : ℕ) : ℝ) := by
      rw [Nat.cast_max]
      exact le_trans hVlo (le_max_left _ _)
    rw [hdiff]
    calc (X / L) * d ≤ (10 : ℝ) ^ 5 * (4 : ℝ) ^ ℓ * P₁ ^ ℓ := hgeo
      _ ≤ C' * P₁ ^ ℓ := mul_le_mul_of_nonneg_right hC'geo (by positivity)
      _ ≤ C' * ((max (walkProdV D ℓ W) (walkProdU D ℓ W) : ℕ) : ℝ) :=
            mul_le_mul_of_nonneg_left ha_ge hC'nn
  · -- the dilation-invariance relation
    have hpl := polyrel_walk_maxmin D hC hP hL hbig hL1 hLbig hW hSne hSprime hstep
    exact PolyRel.mono hpl hC'mid (by positivity) (by positivity)

/-- **From a good bicycle to `ADIEdge`.**  A good bicycle of the quadruple graph -- an arc of
`D.edges` together with two non-degenerate closed walks through its endpoints, carrying a prime
set `S ⊆ [P₂/2, P₂]` of size `≫ π₀(P₂)` on every arc -- yields the approximate dilation
invariance data required by `ADIEdge` for that arc. -/
theorem good_bike_adi (k : ℕ) (ℓ : ℕ) (c C c₅ δ c' : ℝ) (hc : 0 < c) (hC : 0 < C)
    (hc₅ : 0 < c₅) (hδ : 0 < δ) (hc' : 0 < c') (hc'δ : c' ≤ δ) :
    ∃ C' : ℝ, 0 < C' ∧ ∀ (f : ℕ → ℂ) (X L P₁ P₂ : ℝ)
      (D : Work.BMF.QuadData k f c C X L P₁ P₂) (q : ℕ)
      (t : Sigma fun _e : Work.BMF.Edge =>
        (Fin (ℓ + 1) → Work.BMF.GVert D) × (Fin (ℓ + 1) → Work.BMF.GVert D)),
      0 < P₁ → 2 ≤ P₂ → 0 < L → 8000 * P₁ ^ 2 < X / L →
      1 ≤ L / (2 * P₁) →
      2 * Work.BMF.symmConst k (max C (Work.BMF.symmConst k C)) * ((k : ℝ) + 1) *
        (k : ℝ) ^ k * (k.factorial : ℝ) < L / (2 * P₁) →
      t ∈ Work.BMF.goodBikeSet D q ℓ (X / L) c₅ δ →
      Work.BMF.ADIEdge k c' C' (X / L) L P₁ P₂ ℓ D.pol t.1 := by
  classical
  set C' : ℝ := max (max (max (cycConst k (symmConst k (max C (symmConst k C))) ℓ)
        (symmConst k (cycConst k (symmConst k (max C (symmConst k C))) ℓ)))
      (max ((2 : ℝ) ^ ℓ / c₅) ((10 : ℝ) ^ 5 * (4 : ℝ) ^ ℓ))) (C + 1) with hC'def
  have hC'pos : 0 < C' := by
    rw [hC'def]
    exact lt_of_lt_of_le (by linarith) (le_max_right _ _)
  have hC'big : max (max (cycConst k (symmConst k (max C (symmConst k C))) ℓ)
        (symmConst k (cycConst k (symmConst k (max C (symmConst k C))) ℓ)))
      (max ((2 : ℝ) ^ ℓ / c₅) ((10 : ℝ) ^ 5 * (4 : ℝ) ^ ℓ)) ≤ C' := by
    rw [hC'def]
    exact le_max_left _ _
  have hC_le : C ≤ C' := by
    rw [hC'def]
    exact le_trans (by linarith) (le_max_right _ _)
  refine ⟨C', hC'pos, ?_⟩
  intro f X L P₁ P₂ D q t hP₁ hP₂ hL hbig hL1 hLbig hmem
  -- the scale and its positivity
  have hX : 0 < X := by
    have h0 : 0 < 8000 * P₁ ^ 2 := by positivity
    have h1 : 0 < X / L := lt_of_lt_of_le h0 hbig.le
    exact (div_pos_iff_of_pos_right hL).mp h1
  have hNpos : (0 : ℝ) < X / L := div_pos hX hL
  have hpi0 : 0 < pi0 P₂ := pi0_pos_of_two_le hP₂
  -- unpack the good bicycle
  have hmem1 : t ∈ (bikeSet D q ℓ).filter (fun t => goodBikeQ (X / L) c₅ δ D ℓ t) := hmem
  rw [Finset.mem_filter] at hmem1
  obtain ⟨htbike, hgood⟩ := hmem1
  simp only [goodBikeQ] at hgood
  obtain ⟨hnd₁, hnd₂, hvg⟩ := hgood
  rw [bikeSet, Finset.mem_sigma] at htbike
  obtain ⟨heF, ht2⟩ := htbike
  obtain ⟨he_edges, -⟩ := Finset.mem_filter.mp heF
  obtain ⟨hW₁, hW₂⟩ := bike_mem_product.mp ht2
  -- the prime set
  set S : Finset ℕ := bikePrimesQ D ℓ t with hSdef
  have hSsplit : ∀ p ∈ S, p ∈ primesIn (P₂ / 2) P₂ ∧ p ∈ edgeS D t.1 ∧
      (∀ j : Fin ℓ, GAdjQ D p (t.2.1 j.castSucc) (t.2.1 j.succ)) ∧
      (∀ j : Fin ℓ, GAdjQ D p (t.2.2 j.castSucc) (t.2.2 j.succ)) := by
    intro p hp
    rw [hSdef] at hp
    rw [bikePrimesQ, Finset.mem_filter] at hp
    exact ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2⟩
  have hSp : ∀ p ∈ S, p.Prime := fun p hp => (isPrimeIn_of_mem_primesIn (hSsplit p hp).1).1
  have hSIn : ∀ p ∈ S, IsPrimeIn (P₂ / 2) P₂ p :=
    fun p hp => isPrimeIn_of_mem_primesIn (hSsplit p hp).1
  have hSeq : ∀ p ∈ S, p ∈ edgeS D t.1 := fun p hp => (hSsplit p hp).2.1
  have hcardS : δ * pi0 P₂ < ((S.card : ℕ) : ℝ) := by
    rw [hSdef]
    simpa only [veryGoodQ] using hvg
  have hcard : c' * pi0 P₂ ≤ ((S.card : ℕ) : ℝ) :=
    le_of_lt (lt_of_le_of_lt (mul_le_mul_of_nonneg_right hc'δ hpi0.le) hcardS)
  have hSne : S.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hemp
    rw [hemp] at hcardS
    simp at hcardS
    have : (0 : ℝ) < δ * pi0 P₂ := mul_pos hδ hpi0
    linarith
  have hstep₁ : ∀ p ∈ S, ∀ j : Fin ℓ,
      p ∈ stepS D (t.2.1 j.castSucc) (t.2.1 j.succ) ∨
      p ∈ stepS D (t.2.1 j.succ) (t.2.1 j.castSucc) := by
    intro p hp j
    exact (GAdjQ_iff_stepS_or D hP₁ hL hbig _ _ p).mp ((hSsplit p hp).2.2.1 j)
  have hstep₂ : ∀ p ∈ S, ∀ j : Fin ℓ,
      p ∈ stepS D (t.2.2 j.castSucc) (t.2.2 j.succ) ∨
      p ∈ stepS D (t.2.2 j.succ) (t.2.2 j.castSucc) := by
    intro p hp j
    exact (GAdjQ_iff_stepS_or D hP₁ hL hbig _ _ p).mp ((hSsplit p hp).2.2.2 j)
  -- the two dilation pairs
  obtain ⟨a₁, b₁, hb₁lo, hb₁lt, ha₁hi, ha₁lb, ha₁ub, hpl₁⟩ :=
    walk_adi_pair D hC hP₁ hL hX hbig hL1 hLbig hc₅ hW₁ hnd₁ hSne hSp hstep₁ hC'big
  obtain ⟨a₂, b₂, hb₂lo, hb₂lt, ha₂hi, ha₂lb, ha₂ub, hpl₂⟩ :=
    walk_adi_pair D hC hP₁ hL hX hbig hL1 hLbig hc₅ hW₂ hnd₂ hSne hSp hstep₂ hC'big
  -- the edge relation of the middle edge, modulo `1/∏S`
  have hp₂pos : (0 : ℝ) < (t.1.p₂ : ℝ) := by
    have h := (EdgeGeom.prime_p₂ (D.geom t.1 he_edges)).1.pos
    exact_mod_cast h
  have hp₂le : (t.1.p₂ : ℝ) ≤ 2 * P₁ := (EdgeGeom.prime_p₂ (D.geom t.1 he_edges)).2.2
  have hL1' : 1 ≤ L / (t.1.p₂ : ℝ) := by
    have h2P : (0 : ℝ) < 2 * P₁ := by linarith
    calc (1 : ℝ) ≤ L / (2 * P₁) := hL1
      _ ≤ L / (t.1.p₂ : ℝ) := div_le_div_of_nonneg_left hL.le hp₂pos hp₂le
  have hLbig' : 2 * C * ((k : ℝ) + 1) * (k : ℝ) ^ k * (k.factorial : ℝ) < L / (t.1.p₂ : ℝ) := by
    have hCsymm : C ≤ symmConst k (max C (symmConst k C)) :=
      le_trans (le_max_left _ _) (symmConst_ge_self (lt_of_lt_of_le hC (le_max_left _ _)))
    have hmono : 2 * C * ((k : ℝ) + 1) * (k : ℝ) ^ k * (k.factorial : ℝ) ≤
        2 * symmConst k (max C (symmConst k C)) * ((k : ℝ) + 1) * (k : ℝ) ^ k *
          (k.factorial : ℝ) := by
      have h1 : 2 * C ≤ 2 * symmConst k (max C (symmConst k C)) := by linarith
      have h2 : (0 : ℝ) ≤ ((k : ℝ) + 1) * (k : ℝ) ^ k * (k.factorial : ℝ) := by positivity
      nlinarith [h1, h2, hC]
    calc 2 * C * ((k : ℝ) + 1) * (k : ℝ) ^ k * (k.factorial : ℝ)
        ≤ 2 * symmConst k (max C (symmConst k C)) * ((k : ℝ) + 1) * (k : ℝ) ^ k *
            (k.factorial : ℝ) := hmono
      _ < L / (2 * P₁) := hLbig
      _ ≤ L / (t.1.p₂ : ℝ) := div_le_div_of_nonneg_left hL.le hp₂pos hp₂le
  have hp₁pos : (0 : ℝ) < (t.1.p₁ : ℝ) := by
    have h := (EdgeGeom.prime_p₁ (D.geom t.1 he_edges)).1.pos
    exact_mod_cast h
  have hpoly : ∀ p ∈ S,
      PolyRel k C (1 / (p : ℝ)) (t.1.x₁ / (t.1.p₂ : ℝ)) (L / (t.1.p₂ : ℝ))
        (dil (t.1.p₂ : ℝ) (D.pol t.1.x₁)) (t.1.x₂ / (t.1.p₁ : ℝ)) (L / (t.1.p₁ : ℝ))
        (dil (t.1.p₁ : ℝ) (D.pol t.1.x₂)) := by
    intro p hp
    exact edgeS_rel D he_edges (hSeq p hp)
  have hcrt := polyRel_crt hC hSne hSp hL1' hLbig' hpoly
  have hEdgeRel : EdgeRel k C (1 / ((S.prod (fun p => p) : ℕ) : ℝ)) L D.pol t.1 := hcrt
  have hEdgeRel' : EdgeRel k C' (1 / ((S.prod (fun p => p) : ℕ) : ℝ)) L D.pol t.1 :=
    PolyRel.mono hEdgeRel hC_le (by positivity) (by positivity)
  exact ⟨a₁, b₁, a₂, b₂, S, hSIn, hcard, hb₁lo, hb₁lt, ha₁hi, hb₂lo, hb₂lt, ha₂hi,
    ha₁lb, ha₁ub, ha₂lb, ha₂ub, hEdgeRel', hpl₁, hpl₂⟩

end Work.BMF
