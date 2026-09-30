import Mathlib
import Submission.Work.BMF.adi_all_defs
import Submission.Work.BMF.adi_count
import Submission.Work.BMF.degen_closedWalkAll_le
import Submission.Work.BMF.edges_card_le
import Submission.Work.BMF.bikeSetAll_bridge
import Submission.Work.BMF.walk_closure
import Submission.Work.BMF.walk_closure_all
import Submission.Work.BMF.primesIn_half_card_le_all

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Auxiliary counting lemmas for `Work.BMF.good_bike_exists`

Bookkeeping lemmas about the quadruple graph `D` used by the `good_bike_exists` counting:

* the vertex count of the graph is the size of the family, and `#fam ≤ X/L`;
* the Chebyshev bound `#edges ≤ C π₀(P₁)² X/L` (uniform in `f`);
* the number of closed walks of the *full* graph at a base point is `≪ π₀(P₁)^{2ℓ}/(X/L)`
  (and the same for the `q`-subgraph, and for the degenerate walks);
* the upper bound `#bikeSetAll ≪ (π₀(P₁)²)^{2ℓ+1}/(X/L)` for all bicycles of the full graph;
* the summation identity `∑_q #(bikeSet_q with property p) = ∑_{t, p} #bikePrimesQ t`.
-/

namespace Work.BMF

open Finset Real

attribute [local instance] Classical.propDecidable

/-- Membership in a `Finset.product` (the `.product` form of `Finset.mem_product`). -/
lemma mem_product_iff {α β : Type*} {s : Finset α} {t : Finset β} {p : α × β} :
    p ∈ s.product t ↔ p.1 ∈ s ∧ p.2 ∈ t := Finset.mem_product

/-- Cardinality of a `Finset.product` (the `.product` form of `Finset.card_product`). -/
lemma card_product_iff {α β : Type*} (s : Finset α) (t : Finset β) :
    (s.product t).card = s.card * t.card := Finset.card_product s t


variable {k : ℕ} {f : ℕ → ℂ} {c C X L P₁ P₂ : ℝ}

/-- The number of vertices of the quadruple graph is the size of the family. -/
lemma fintype_card_GVert (D : QuadData k f c C X L P₁ P₂) :
    Fintype.card (GVert D) = D.fam.card := Fintype.card_coe D.fam

/-- The family has at most `X / L` elements (when `3 ≤ X / L`). -/
lemma fam_card_le_NR (D : QuadData k f c C X L P₁ P₂) (hX : 0 < X) (hL : 0 < L)
    (hN : 3 ≤ X / L) : (D.fam.card : ℝ) ≤ X / L := by
  have h := fam_card_le_N D hX hL
  have h1 : (10:ℝ) * X / (500 * L) = X / (50 * L) := by ring
  rw [h1] at h
  have h2 : X / (50 * L) = (X / L) / 50 := by ring
  rw [h2] at h
  linarith

/-- `π₀(P)` is positive for `P ≥ 2`. -/
lemma pi0_pos {P : ℝ} (hP : 2 ≤ P) : 0 < pi0 P := by
  rw [pi0]
  exact div_pos (by linarith) (Real.log_pos (by linarith))

/-- Chebyshev bound for the number of edges, uniform in `f`: `#edges ≤ C π₀(P₁)² X/L`. -/
theorem edges_card_le_NR (k : ℕ) :
    ∃ C P₀ : ℝ, 0 < C ∧ 0 < P₀ ∧ ∀ (f : ℕ → ℂ) (c Cq X L P₁ P₂ : ℝ)
      (D : QuadData k f c Cq X L P₁ P₂),
      P₀ ≤ P₁ → 0 < P₁ → 0 < L → 0 < X → 8000 * P₁ ^ 2 < X / L → 3 ≤ X / L →
      (D.edges.card : ℝ) ≤ C * pi0 P₁ ^ 2 * (X / L) := by
  obtain ⟨C', P₀', hC', hprimes⟩ := primesIn_card_le_pi0
  refine ⟨2 * C' ^ 2, max P₀' 3, by positivity, lt_max_of_lt_right (by norm_num), ?_⟩
  intro f c Cq X L P₁ P₂ D hP₀ hP₁ hL hX hbig hN
  have hleP₀' : P₀' ≤ P₁ := le_trans (le_max_left _ _) hP₀
  have hge3 : (3 : ℝ) ≤ P₁ := le_trans (le_max_right _ _) hP₀
  have hP₁1 : (1 : ℝ) < P₁ := by linarith
  have hpi0nn : 0 ≤ pi0 P₁ := by
    rw [pi0]; exact div_nonneg (by linarith) (Real.log_pos hP₁1).le
  set n : ℕ := (primesIn P₁ (2 * P₁)).card with hn
  have hnR : (n : ℝ) ≤ C' * pi0 P₁ := by
    simpa only [hn] using hprimes P₁ hleP₀'
  have hinj : Set.InjOn (fun e : Edge => (e.p₁, e.p₂, e.x₂)) ↑D.edges := by
    intro e he e' he' h
    have hp₁ : e.p₁ = e'.p₁ := by simpa using congrArg (fun t : ℕ × ℕ × ℝ => t.1) h
    have hp₂ : e.p₂ = e'.p₂ := by simpa using congrArg (fun t : ℕ × ℕ × ℝ => t.2.1) h
    have hx₂ : e.x₂ = e'.x₂ := by simpa using congrArg (fun t : ℕ × ℕ × ℝ => t.2.2) h
    have hge := D.geom e he
    have hge' := D.geom e' he'
    unfold EdgeGeom at hge hge'
    obtain ⟨hx₁S, _, _, _, _, _, habs⟩ := hge
    obtain ⟨hx₁S', _, _, _, _, _, habs'⟩ := hge'
    have h1 : |e.x₁ - ((e'.p₂ : ℝ) / e'.p₁) * e'.x₂| ≤ 100 * L := by
      rw [← hp₁, ← hp₂, ← hx₂]; exact habs
    have h2 : |e'.x₁ - ((e'.p₂ : ℝ) / e'.p₁) * e'.x₂| ≤ 100 * L := habs'
    have htri := abs_sub_le e.x₁ (((e'.p₂ : ℝ) / e'.p₁) * e'.x₂) e'.x₁
    have h3 : |(((e'.p₂ : ℝ) / e'.p₁) * e'.x₂) - e'.x₁| ≤ 100 * L := by
      rw [abs_sub_comm]; exact h2
    have hsep : |e.x₁ - e'.x₁| ≤ 200 * L := by linarith
    by_cases hx₁ : e.x₁ = e'.x₁
    · cases e; cases e'; simp_all
    · exfalso
      have hsep' := D.isFam.2 e.x₁ hx₁S e'.x₁ hx₁S' hx₁
      have : (200 : ℝ) * L < 500 * L := by linarith
      linarith [abs_nonneg (e.x₁ - e'.x₁)]
  have hsub : D.edges.image (fun e : Edge => (e.p₁, e.p₂, e.x₂)) ⊆
      (primesIn P₁ (2 * P₁)) ×ˢ ((primesIn P₁ (2 * P₁)) ×ˢ D.fam) := by
    intro q hq
    rw [Finset.mem_image] at hq
    obtain ⟨e, he, rfl⟩ := hq
    have hge := D.geom e he
    unfold EdgeGeom at hge
    obtain ⟨_, hx₂S, _, _, hpr1, hpr2, _⟩ := hge
    exact Finset.mem_product.mpr ⟨mem_primesIn_of_isPrimeIn hpr1,
      Finset.mem_product.mpr ⟨mem_primesIn_of_isPrimeIn hpr2, hx₂S⟩⟩
  have hcard2 : (D.edges.image (fun e : Edge => (e.p₁, e.p₂, e.x₂))).card ≤
      n * n * D.fam.card := by
    calc (D.edges.image (fun e : Edge => (e.p₁, e.p₂, e.x₂))).card
        ≤ ((primesIn P₁ (2 * P₁)) ×ˢ ((primesIn P₁ (2 * P₁)) ×ˢ D.fam)).card :=
          Finset.card_le_card hsub
      _ = (primesIn P₁ (2 * P₁)).card * ((primesIn P₁ (2 * P₁)).card * D.fam.card) := by
          rw [Finset.card_product, Finset.card_product]
      _ = n * n * D.fam.card := by rw [hn, mul_assoc]
  have hcardR : (D.edges.card : ℝ) ≤ (n : ℝ) * (n : ℝ) * (D.fam.card : ℝ) := by
    have hcard1 : (D.edges.image (fun e : Edge => (e.p₁, e.p₂, e.x₂))).card = D.edges.card :=
      Finset.card_image_of_injOn hinj
    have h : D.edges.card ≤ n * n * D.fam.card := by rw [← hcard1]; exact hcard2
    calc (D.edges.card : ℝ) ≤ ((n * n * D.fam.card : ℕ) : ℝ) := by exact_mod_cast h
      _ = (n : ℝ) * (n : ℝ) * (D.fam.card : ℝ) := by push_cast; ring
  have hfam := fam_card_le_N D hX hL
  have hfamN : (D.fam.card : ℝ) ≤ 2 * (X / L) := by
    have h1 : (10:ℝ) * X / (500 * L) = X / (50 * L) := by ring
    have h2 : X / (50 * L) = (X / L) / 50 := by ring
    rw [h1, h2] at hfam
    linarith
  have hstep : (n : ℝ) * (n : ℝ) * (D.fam.card : ℝ) ≤
      (C' * pi0 P₁) * (C' * pi0 P₁) * (2 * (X / L)) := by
    have h1 : (n : ℝ) * (n : ℝ) ≤ (C' * pi0 P₁) * (C' * pi0 P₁) :=
      mul_le_mul hnR hnR (by positivity) (mul_nonneg hC'.le hpi0nn)
    exact mul_le_mul h1 hfamN (by positivity) (by positivity)
  calc (D.edges.card : ℝ) ≤ (n : ℝ) * (n : ℝ) * (D.fam.card : ℝ) := hcardR
    _ ≤ (C' * pi0 P₁) * (C' * pi0 P₁) * (2 * (X / L)) := hstep
    _ = 2 * C' ^ 2 * pi0 P₁ ^ 2 * (X / L) := by ring

/-- Summation of the `q`-edge counts over the primes `q ∈ [P₂/2, P₂]`. -/
theorem sum_edgesS_le (D : QuadData k f c C X L P₁ P₂) :
    ∑ q ∈ primesIn (P₂ / 2) P₂, ((D.edges.filter (fun e => q ∈ edgeS D e)).card : ℝ)
      ≤ (D.edges.card : ℝ) * ((primesIn (P₂ / 2) P₂).card : ℝ) := by
  classical
  have h1 : ∀ q : ℕ, ((D.edges.filter (fun e => q ∈ edgeS D e)).card : ℝ)
      ≤ (D.edges.card : ℝ) := by
    intro q
    exact_mod_cast Finset.card_filter_le (D.edges) (fun e => q ∈ edgeS D e)
  calc ∑ q ∈ primesIn (P₂ / 2) P₂, ((D.edges.filter (fun e => q ∈ edgeS D e)).card : ℝ)
      ≤ ∑ _q ∈ primesIn (P₂ / 2) P₂, (D.edges.card : ℝ) := Finset.sum_le_sum (fun q _ => h1 q)
    _ = (D.edges.card : ℝ) * ((primesIn (P₂ / 2) P₂).card : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul]; ring

/-- Failing to be very good bounds the number of supporting primes. -/
lemma card_bikePrimesQ_le_of_not_veryGoodQ {D : QuadData k f c C X L P₁ P₂} {ℓ : ℕ} {δ : ℝ}
    {t : (Σ _e : Edge, (Fin (ℓ + 1) → GVert D) × (Fin (ℓ + 1) → GVert D))}
    (h : ¬ veryGoodQ D ℓ δ t) : ((bikePrimesQ D ℓ t).card : ℝ) ≤ δ * pi0 P₂ :=
  not_lt.mp (by simpa only [veryGoodQ] using h)

/-- Summation identity: summing the `q`-bicycle sets over the primes `q ∈ [P₂/2, P₂]`
amounts to summing the number of supporting primes `#bikePrimesQ t` over the bicycles `t`
of the full graph satisfying the predicate `p`. -/
theorem sum_bikeSet_eq_sum_bikePrimesQ (D : QuadData k f c C X L P₁ P₂) (ℓ : ℕ)
    (p : (Σ _e : Edge, (Fin (ℓ + 1) → GVert D) × (Fin (ℓ + 1) → GVert D)) → Prop)
    [DecidablePred p] :
    ∑ q ∈ primesIn (P₂ / 2) P₂, (((bikeSet D q ℓ).filter p).card : ℝ)
      = ∑ t ∈ (bikeSetAll D ℓ).filter p, ((bikePrimesQ D ℓ t).card : ℝ) := by
  classical
  have hcard : ∀ q : ℕ, (((bikeSet D q ℓ).filter p).card : ℝ)
      = ∑ t ∈ bikeSetAll D ℓ, (if q ∈ bikePrimesQ D ℓ t ∧ p t then (1:ℝ) else 0) := by
    intro q
    have hset : (bikeSet D q ℓ).filter p
        = (bikeSetAll D ℓ).filter (fun t => q ∈ bikePrimesQ D ℓ t ∧ p t) := by
      rw [bikeSetAll_bridge, Finset.filter_filter]
    rw [hset, Finset.card_filter, Nat.cast_sum]
    exact Finset.sum_congr rfl (fun t _ => by
      by_cases h : q ∈ bikePrimesQ D ℓ t ∧ p t <;> simp [h])
  calc ∑ q ∈ primesIn (P₂ / 2) P₂, (((bikeSet D q ℓ).filter p).card : ℝ)
      = ∑ q ∈ primesIn (P₂ / 2) P₂, ∑ t ∈ bikeSetAll D ℓ,
          (if q ∈ bikePrimesQ D ℓ t ∧ p t then (1:ℝ) else 0) :=
        Finset.sum_congr rfl (fun q _ => hcard q)
    _ = ∑ t ∈ bikeSetAll D ℓ, ∑ q ∈ primesIn (P₂ / 2) P₂,
          (if q ∈ bikePrimesQ D ℓ t ∧ p t then (1:ℝ) else 0) := Finset.sum_comm
    _ = ∑ t ∈ bikeSetAll D ℓ, (if p t then ((bikePrimesQ D ℓ t).card : ℝ) else 0) := by
        refine Finset.sum_congr rfl (fun t _ => ?_)
        have hsub : bikePrimesQ D ℓ t ⊆ primesIn (P₂ / 2) P₂ := by
          intro q hq
          rw [bikePrimesQ] at hq
          exact (Finset.mem_filter.mp hq).1
        have hstep : ∀ q : ℕ, (if q ∈ bikePrimesQ D ℓ t ∧ p t then (1:ℝ) else 0)
            = (if q ∈ bikePrimesQ D ℓ t then (if p t then (1:ℝ) else 0) else 0) := by
          intro q
          by_cases hq : q ∈ bikePrimesQ D ℓ t <;> by_cases hp : p t <;> simp [hq, hp]
        rw [Finset.sum_congr rfl (fun q _ => hstep q), Finset.sum_ite_mem,
          Finset.inter_eq_right.mpr hsub]
        by_cases hp : p t <;> simp [hp]
    _ = ∑ t ∈ (bikeSetAll D ℓ).filter p, ((bikePrimesQ D ℓ t).card : ℝ) := by
        rw [Finset.sum_filter]

/-- **The number of closed walks of the full graph at a base point.**  Every closed walk of
`GAdjAll` of length `ℓ` is within `10^5 · 4^ℓ · P₁^ℓ/(X/L)` of being closed up to the label
products (`walk_closure_all`), and the walks with that near-degeneracy number
`≪ π₀(P₁)^{2ℓ}/(X/L)` (`degen_closedWalkAll_le`). -/
theorem closedWalkAll_card_le (k ℓ : ℕ) (hℓ : 2 ≤ ℓ) :
    ∃ C P₀ : ℝ, 0 < C ∧ 0 < P₀ ∧ ∀ (f : ℕ → ℂ) (c Cq X L P₁ P₂ : ℝ)
      (D : QuadData k f c Cq X L P₁ P₂) (x : ℝ),
      P₀ ≤ P₁ → 0 < P₁ → 0 < L → 0 < X → 3 ≤ X / L → X / L ≤ P₁ ^ (ℓ - 1) →
      ((closedWalkAll D ℓ x).card : ℝ) ≤ C * pi0 P₁ ^ (2 * ℓ) / (X / L) := by
  obtain ⟨C₁, P₁₀, hC₁, hb⟩ := degen_closedWalkAll_le k ℓ (by omega)
  refine ⟨C₁ * (10 ^ 5 * (4:ℝ) ^ ℓ), max P₁₀ 3, by positivity,
    lt_max_of_lt_right (by norm_num), ?_⟩
  intro f c Cq X L P₁ P₂ D x hP₀ hP hL hX hN3 hNle
  have hP₀' : P₁₀ ≤ P₁ := le_trans (le_max_left _ _) hP₀
  have h3 : (3:ℝ) ≤ P₁ := le_trans (le_max_right _ _) hP₀
  have hlog3 : (1:ℝ) < Real.log 3 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0:ℝ) < 3)]
    exact Real.exp_one_lt_three
  have hlogP : 0 < Real.log P₁ := Real.log_pos (by linarith)
  have hlog3le : Real.log 3 ≤ Real.log P₁ := Real.log_le_log (by norm_num) h3
  have hC0 : 1 / Real.log P₁ ≤ 10 ^ 5 * (4:ℝ) ^ ℓ := by
    have h1 : 1 / Real.log P₁ ≤ 1 := by
      rw [div_le_one hlogP]; linarith
    have h2 : (1:ℝ) ≤ 10 ^ 5 * (4:ℝ) ^ ℓ := by
      calc (1:ℝ) = 1 * 1 := by ring
        _ ≤ 10 ^ 5 * (4:ℝ) ^ ℓ :=
            mul_le_mul (by norm_num) (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 4)) (by norm_num)
              (by norm_num)
    linarith
  have hb' := hb f c Cq X L P₁ P₂ (X / L) (10 ^ 5 * (4:ℝ) ^ ℓ) D x hP₀' hP hL hN3 hNle hC0
  have hfilter : (closedWalkAll D ℓ x).filter (fun W =>
      |((walkProdV D ℓ W : ℕ) : ℝ) - ((walkProdU D ℓ W : ℕ) : ℝ)|
        ≤ (10 ^ 5 * (4:ℝ) ^ ℓ) * P₁ ^ ℓ / (X / L)) = closedWalkAll D ℓ x := by
    refine Finset.filter_true_of_mem (fun W hW => ?_)
    rw [closedWalkAll] at hW
    obtain ⟨hWa, hcyc, _⟩ := Finset.mem_filter.mp hW
    obtain ⟨_, hadj⟩ := Finset.mem_filter.mp hWa
    exact walk_closure_all k f c Cq X L P₁ P₂ D hP hL hX ℓ hcyc hadj
  rw [hfilter] at hb'
  exact hb'

/-- The number of closed walks of the `q`-subgraph based at a point. -/
theorem closedWalkVal_card_le (k ℓ : ℕ) (hℓ : 2 ≤ ℓ) :
    ∃ C P₀ : ℝ, 0 < C ∧ 0 < P₀ ∧ ∀ (f : ℕ → ℂ) (c Cq X L P₁ P₂ : ℝ)
      (D : QuadData k f c Cq X L P₁ P₂) (q : ℕ) (x : ℝ),
      P₀ ≤ P₁ → 0 < P₁ → 0 < L → 0 < X → 3 ≤ X / L → X / L ≤ P₁ ^ (ℓ - 1) →
      ((closedWalkVal D q ℓ x).card : ℝ) ≤ C * pi0 P₁ ^ (2 * ℓ) / (X / L) := by
  obtain ⟨C, P₀, hC, hP₀, hb⟩ := closedWalkAll_card_le k ℓ hℓ
  refine ⟨C, P₀, hC, hP₀, ?_⟩
  intro f c Cq X L P₁ P₂ D q x h1 h2 h3 h4 h5 h6
  rw [closedWalkAll_filter_eq]
  calc (((closedWalkAll D ℓ x).filter
        (fun W => ∀ j : Fin ℓ, GAdjQ D q (W j.castSucc) (W j.succ))).card : ℝ)
      ≤ ((closedWalkAll D ℓ x).card : ℝ) := by
        exact_mod_cast Finset.card_filter_le _ _
    _ ≤ C * pi0 P₁ ^ (2 * ℓ) / (X / L) := hb f c Cq X L P₁ P₂ D x h1 h2 h3 h4 h5 h6

/-- The closed walks of the `q`-subgraph based at `x` that are degenerate with constants
`N`, `c₅` (packaged as a definition so that the statements below need no decidability data). -/
noncomputable def degenWalks (D : QuadData k f c C X L P₁ P₂) (ℓ : ℕ) (N c₅ : ℝ) (q : ℕ)
    (x : ℝ) : Finset (Fin (ℓ + 1) → GVert D) :=
  (closedWalkVal D q ℓ x).filter (fun W => degenerateAt N c₅ P₁ D ℓ W)

lemma degenWalks_def (D : QuadData k f c C X L P₁ P₂) (ℓ : ℕ) (N c₅ : ℝ) (q : ℕ) (x : ℝ) :
    degenWalks D ℓ N c₅ q x
      = (closedWalkVal D q ℓ x).filter (fun W => degenerateAt N c₅ P₁ D ℓ W) := rfl

/-- The bicycles of the `q`-subgraph one of whose two cycles is degenerate. -/
noncomputable def degenBikes (D : QuadData k f c C X L P₁ P₂) (ℓ : ℕ) (N c₅ : ℝ) (q : ℕ) :
    Finset (Σ _e : Edge, (Fin (ℓ + 1) → GVert D) × (Fin (ℓ + 1) → GVert D)) :=
  (bikeSet D q ℓ).filter (fun t =>
    degenerateAt N c₅ P₁ D ℓ t.2.1 ∨ degenerateAt N c₅ P₁ D ℓ t.2.2)

lemma degenBikes_def (D : QuadData k f c C X L P₁ P₂) (ℓ : ℕ) (N c₅ : ℝ) (q : ℕ) :
    degenBikes D ℓ N c₅ q = (bikeSet D q ℓ).filter (fun t =>
      degenerateAt N c₅ P₁ D ℓ t.2.1 ∨ degenerateAt N c₅ P₁ D ℓ t.2.2) := rfl

/-- The bicycles of the `q`-subgraph that are not very good. -/
noncomputable def notVeryGoodBikes (D : QuadData k f c C X L P₁ P₂) (ℓ : ℕ) (δ : ℝ) (q : ℕ) :
    Finset (Σ _e : Edge, (Fin (ℓ + 1) → GVert D) × (Fin (ℓ + 1) → GVert D)) :=
  (bikeSet D q ℓ).filter (fun t => ¬ veryGoodQ D ℓ δ t)

lemma notVeryGoodBikes_def (D : QuadData k f c C X L P₁ P₂) (ℓ : ℕ) (δ : ℝ) (q : ℕ) :
    notVeryGoodBikes D ℓ δ q
      = (bikeSet D q ℓ).filter (fun t => ¬ veryGoodQ D ℓ δ t) := rfl

/-- The number of *degenerate* closed walks of the `q`-subgraph based at a point. -/
theorem degenWalks_card_le (k ℓ : ℕ) (hℓ : 2 ≤ ℓ) :
    ∃ C P₀ : ℝ, 0 < C ∧ 0 < P₀ ∧ ∀ (f : ℕ → ℂ) (c Cq X L P₁ P₂ c₅ : ℝ)
      (D : QuadData k f c Cq X L P₁ P₂) (q : ℕ) (x : ℝ),
      P₀ ≤ P₁ → 0 < P₁ → 0 < L → 0 < X → 3 ≤ X / L → X / L ≤ P₁ ^ (ℓ - 1) →
      1 / Real.log P₁ ≤ c₅ →
      ((degenWalks D ℓ (X / L) c₅ q x).card : ℝ) ≤ C * c₅ * pi0 P₁ ^ (2 * ℓ) / (X / L) := by
  classical
  obtain ⟨C₁, P₁₀, hC₁, hb⟩ := degen_closedWalkAll_le k ℓ (by omega)
  refine ⟨C₁, max P₁₀ 3, hC₁, lt_max_of_lt_right (by norm_num), ?_⟩
  intro f c Cq X L P₁ P₂ c₅ D q x hP₀ hP hL hX hN3 hNle hc₅
  have hb' := hb f c Cq X L P₁ P₂ (X / L) c₅ D x (le_trans (le_max_left _ _) hP₀) hP hL hN3
    hNle hc₅
  rw [degenWalks_def, closedWalkAll_filter_eq]
  refine le_trans (Nat.cast_le.mpr (Finset.card_le_card ?_)) hb'
  intro W hW
  rw [Finset.mem_filter] at hW
  obtain ⟨hW1, hW2⟩ := hW
  rw [Finset.mem_filter] at hW1
  rw [Finset.mem_filter]
  exact ⟨hW1.1, hW2⟩

/-- The degenerate bicycles decompose over the arcs: the `q`-arc, a (degenerate or arbitrary)
closed walk at one endpoint and an arbitrary closed walk at the other. -/
theorem card_degenBikes_le (D : QuadData k f c C X L P₁ P₂) (ℓ : ℕ) (N c₅ : ℝ) (q : ℕ) :
    (degenBikes D ℓ N c₅ q).card ≤
      ∑ e ∈ D.edges.filter (fun e => q ∈ edgeS D e),
        ((degenWalks D ℓ N c₅ q e.x₁).card * (closedWalkVal D q ℓ e.x₂).card +
         (closedWalkVal D q ℓ e.x₁).card * (degenWalks D ℓ N c₅ q e.x₂).card) := by
  classical
  set QE : Finset Edge := D.edges.filter (fun e => q ∈ edgeS D e) with hQE
  set T : Finset (Σ _e : Edge, (Fin (ℓ + 1) → GVert D) × (Fin (ℓ + 1) → GVert D)) :=
    QE.sigma (fun e =>
      ((degenWalks D ℓ N c₅ q e.x₁).product (closedWalkVal D q ℓ e.x₂)) ∪
      ((closedWalkVal D q ℓ e.x₁).product (degenWalks D ℓ N c₅ q e.x₂))) with hT
  have hsub : degenBikes D ℓ N c₅ q ⊆ T := by
    rintro ⟨e, W₁, W₂⟩ ht
    rw [degenBikes_def, Finset.mem_filter] at ht
    obtain ⟨ht1, hdeg⟩ := ht
    rw [bikeSet] at ht1
    obtain ⟨he, hp⟩ := Finset.mem_sigma.mp ht1
    rw [mem_product_iff] at hp
    obtain ⟨hW1, hW2⟩ := hp
    rw [hT, hQE, Finset.mem_sigma]
    refine ⟨he, ?_⟩
    simp only [Finset.mem_union, mem_product_iff, degenWalks_def, Finset.mem_filter]
    rcases hdeg with h | h
    · exact Or.inl ⟨⟨hW1, h⟩, hW2⟩
    · exact Or.inr ⟨hW1, ⟨hW2, h⟩⟩
  calc (degenBikes D ℓ N c₅ q).card ≤ T.card := Finset.card_le_card hsub
    _ = ∑ e ∈ QE, (((degenWalks D ℓ N c₅ q e.x₁).product
            (closedWalkVal D q ℓ e.x₂)) ∪
          ((closedWalkVal D q ℓ e.x₁).product (degenWalks D ℓ N c₅ q e.x₂))).card := by
        rw [hT, Finset.card_sigma]
    _ ≤ ∑ e ∈ QE, ((degenWalks D ℓ N c₅ q e.x₁).card * (closedWalkVal D q ℓ e.x₂).card +
          (closedWalkVal D q ℓ e.x₁).card * (degenWalks D ℓ N c₅ q e.x₂).card) := by
        refine Finset.sum_le_sum (fun e _ => ?_)
        calc (((degenWalks D ℓ N c₅ q e.x₁).product (closedWalkVal D q ℓ e.x₂)) ∪
              ((closedWalkVal D q ℓ e.x₁).product (degenWalks D ℓ N c₅ q e.x₂))).card
            ≤ ((degenWalks D ℓ N c₅ q e.x₁).product (closedWalkVal D q ℓ e.x₂)).card +
              ((closedWalkVal D q ℓ e.x₁).product (degenWalks D ℓ N c₅ q e.x₂)).card :=
              Finset.card_union_le _ _
          _ = ((degenWalks D ℓ N c₅ q e.x₁).card * (closedWalkVal D q ℓ e.x₂).card +
              (closedWalkVal D q ℓ e.x₁).card * (degenWalks D ℓ N c₅ q e.x₂).card) := by
              rw [card_product_iff, card_product_iff]

/-- **All bicycles of the full graph.**  The number of bicycles (an edge with a closed walk
through each endpoint) of `GAdjAll` is `≪ (π₀(P₁)²)^{2ℓ+1}/(X/L)`: the edge count is
`≪ π₀(P₁)² X/L` and the number of closed walks at a point is `≪ π₀(P₁)^{2ℓ}/(X/L)`. -/
theorem bikeSetAll_card_le (k ℓ : ℕ) (hℓ : 2 ≤ ℓ) :
    ∃ C P₀ : ℝ, 0 < C ∧ 0 < P₀ ∧ ∀ (f : ℕ → ℂ) (c Cq X L P₁ P₂ : ℝ)
      (D : QuadData k f c Cq X L P₁ P₂),
      P₀ ≤ P₁ → 0 < P₁ → 0 < L → 0 < X → 8000 * P₁ ^ 2 < X / L → 3 ≤ X / L →
      X / L ≤ P₁ ^ (ℓ - 1) →
      ((bikeSetAll D ℓ).card : ℝ) ≤ C * (pi0 P₁ ^ 2) ^ (2 * ℓ + 1) / (X / L) := by
  obtain ⟨C_w, P₀w, hCw, hP₀w, hbw⟩ := closedWalkAll_card_le k ℓ hℓ
  obtain ⟨C_e, P₀e, hCe, hP₀e, hbe⟩ := edges_card_le_NR k
  refine ⟨C_e * C_w ^ 2, max P₀w (max P₀e 3), by positivity, ?_, ?_⟩
  · exact lt_max_of_lt_left hP₀w
  intro f c Cq X L P₁ P₂ D hP₀ hP hL hX hbig hN3 hNle
  have hP₀w' : P₀w ≤ P₁ := le_trans (le_max_left _ _) hP₀
  have hP₀e' : P₀e ≤ P₁ := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hP₀)
  have hbwc : ∀ x : ℝ, ((closedWalkAll D ℓ x).card : ℝ)
      ≤ C_w * pi0 P₁ ^ (2 * ℓ) / (X / L) :=
    fun x => hbw f c Cq X L P₁ P₂ D x hP₀w' hP hL hX hN3 hNle
  have hE := hbe f c Cq X L P₁ P₂ D hP₀e' hP hL hX hbig hN3
  have hnn : 0 ≤ C_w * pi0 P₁ ^ (2 * ℓ) / (X / L) := by
    have := hbwc 0
    have h0 : (0:ℝ) ≤ ((closedWalkAll D ℓ 0).card : ℝ) := Nat.cast_nonneg _
    linarith
  calc ((bikeSetAll D ℓ).card : ℝ)
      = ∑ e ∈ D.edges, ((closedWalkAll D ℓ e.x₁).card : ℝ) * ((closedWalkAll D ℓ e.x₂).card : ℝ) := by
        rw [card_bikeSetAll, Nat.cast_sum]
        exact Finset.sum_congr rfl (fun e _ => by push_cast; ring)
    _ ≤ ∑ _e ∈ D.edges, (C_w * pi0 P₁ ^ (2 * ℓ) / (X / L)) * (C_w * pi0 P₁ ^ (2 * ℓ) / (X / L)) := by
        refine Finset.sum_le_sum (fun e _ => ?_)
        exact mul_le_mul (hbwc e.x₁) (hbwc e.x₂) (Nat.cast_nonneg _) hnn
    _ = (D.edges.card : ℝ) * ((C_w * pi0 P₁ ^ (2 * ℓ) / (X / L)) * (C_w * pi0 P₁ ^ (2 * ℓ) / (X / L))) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (C_e * pi0 P₁ ^ 2 * (X / L)) * ((C_w * pi0 P₁ ^ (2 * ℓ) / (X / L)) * (C_w * pi0 P₁ ^ (2 * ℓ) / (X / L))) := by
        refine mul_le_mul_of_nonneg_right hE ?_
        positivity
    _ = C_e * C_w ^ 2 * (pi0 P₁ ^ 2) ^ (2 * ℓ + 1) / (X / L) := by
        have hXL : X / L ≠ 0 := by
          have : (0:ℝ) < X / L := by positivity
          exact ne_of_gt this
        field_simp
        ring

/-- Summation of the not-very-good bicycles over the primes: each of them is counted only by
the at most `δ π₀(P₂)` supporting primes. -/
theorem sum_notVeryGoodBikes_le (D : QuadData k f c C X L P₁ P₂) (ℓ : ℕ) (δ : ℝ)
    (hP₂ : 2 ≤ P₂) (hδ : 0 ≤ δ) :
    ∑ q ∈ primesIn (P₂ / 2) P₂, ((notVeryGoodBikes D ℓ δ q).card : ℝ)
      ≤ δ * pi0 P₂ * ((bikeSetAll D ℓ).card : ℝ) := by
  classical
  have h := sum_bikeSet_eq_sum_bikePrimesQ D ℓ (fun t => ¬ veryGoodQ D ℓ δ t)
  have hL : ∑ q ∈ primesIn (P₂ / 2) P₂, ((notVeryGoodBikes D ℓ δ q).card : ℝ)
      = ∑ q ∈ primesIn (P₂ / 2) P₂,
          (((bikeSet D q ℓ).filter (fun t => ¬ veryGoodQ D ℓ δ t)).card : ℝ) := by
    refine Finset.sum_congr rfl (fun q _ => ?_)
    rw [notVeryGoodBikes_def]
  rw [hL, h]
  have hterm : ∀ t ∈ (bikeSetAll D ℓ).filter (fun t => ¬ veryGoodQ D ℓ δ t),
      ((bikePrimesQ D ℓ t).card : ℝ) ≤ δ * pi0 P₂ := by
    intro t ht
    rw [Finset.mem_filter] at ht
    exact card_bikePrimesQ_le_of_not_veryGoodQ ht.2
  calc ∑ t ∈ (bikeSetAll D ℓ).filter (fun t => ¬ veryGoodQ D ℓ δ t),
        ((bikePrimesQ D ℓ t).card : ℝ)
      ≤ ∑ _t ∈ (bikeSetAll D ℓ).filter (fun t => ¬ veryGoodQ D ℓ δ t), (δ * pi0 P₂) :=
        Finset.sum_le_sum hterm
    _ = δ * pi0 P₂ * (((bikeSetAll D ℓ).filter (fun t => ¬ veryGoodQ D ℓ δ t)).card : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul]; ring
    _ ≤ δ * pi0 P₂ * ((bikeSetAll D ℓ).card : ℝ) := by
        have h0 : (0:ℝ) ≤ δ * pi0 P₂ := mul_nonneg hδ (pi0_pos hP₂).le
        exact mul_le_mul_of_nonneg_left (by exact_mod_cast Finset.card_filter_le _ _) h0

end Work.BMF
