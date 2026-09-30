import Mathlib
import Submission.Work.BMF.Defs
import Submission.Work.BMF.n8_defs
import Submission.Work.N8.net_exists
import Submission.Work.N8.pair_fiber_card
import Submission.Work.N8.sum_ball_card
import Submission.Work.N8.sum_sqrt_mul_sqrt_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option maxHeartbeats 8000000

/-!
# The uniform-constant form of `Work.N8.approx_ergodicity`

`Work.N8.approx_ergodicity` is the statement requested by the N8 node.  As written it quantifies
its constant `cst` *after* all the parameters, i.e. inside the second disjunct, so it permits
`cst` to depend on `X`, `H`, `δ`, `M`, `K`, `ρ`, … ; it is therefore an unconditional statement
(the second disjunct follows from `S ≠ ∅` alone) and its intended content -- the mixing bound
`Work.BMF.quadCount` -- is not used.

The present file provides the paper's Corollary 5.2 (MRT, *Fourier uniformity of bounded
multiplicative functions in short intervals on average*, arXiv:1812.01224, §5) in the form the
downstream argument actually needs: the constants are **uniform** in the parameters (indeed
explicit absolute constants), so it applies with a fixed `c'` when `X → ∞`.

Two hypotheses on the data are necessary for this and are missing from the requested statement:

* `hS` must record that the witnesses `p₁, p₂` of `Gq` are primes of `[Pp, 2Pp]` (in the
  application `Gq` is the *geometric quadruple* relation, which contains that condition, so this
  is automatic there);
* `ρ * (X/H) ≤ 1`: the mixing hypothesis of the requested statement has the free factor `ρ` in
  place of the paper's density factor `H/X` (`hS`'s analogue of MRT Lemma 5.1), so the two only
  coincide in the regime of the application, where `ρ ≍ H/X`.  Without it the conclusion with a
  uniform constant is false.

The proof follows the paper line by line: refine the degree of each pair, take a maximal
`r`-separated net `Ω` of the `z`-coordinates occurring, sum the mixing bound over `z₀ ∈ Ω`
between `A₁(z₀)` and `A₂(z₀)`, use `Σ_{z₀} #A_j(z₀) ≤ M · #D` (bounded doubling) and
Cauchy--Schwarz, and finally extract the cluster and the pairs inside it.
-/



namespace Work.N8

open Finset

theorem approx_ergodicity_strong {ι Z : Type} [DecidableEq ι] [DecidableEq Z]
    (Is : Finset ι) (F : ι → Finset Z) (K : ℕ) (hK : 0 < K) (hF : ∀ i, (F i).card ≤ K)
    (d : Z → Z → ℝ) (r : ℝ) (hr : 0 < r)
    (hd_nn : ∀ a b, 0 ≤ d a b) (hd_symm : ∀ a b, d a b = d b a)
    (hd_tri : ∀ a b c, d a c ≤ d a b + d b c) (hd_refl : ∀ a, d a a = 0)
    (M : ℝ) (hM : 0 < M)
    (hdoub : ∀ z : Z, ∀ s : Finset Z, (∀ w ∈ s, d w z ≤ 5 * r / 2) →
      (∀ w ∈ s, ∀ w' ∈ s, w ≠ w' → r / 2 ≤ d w w') → (s.card : ℝ) ≤ M)
    (Gq : ι → ι → ℕ → ℕ → Prop) [∀ (i i' : ι) (p p' : ℕ), Decidable (Gq i i' p p')]
    (Pp X H ρ π0 logP δ Cmix : ℝ) (hX : 0 < X) (hH : 0 < H) (hρ : 0 < ρ)
    (hπ0 : 0 < π0) (hlogP : 0 < logP) (hδ : 0 < δ) (hCmix : 0 < Cmix)
    (hρXH : ρ * (X / H) ≤ 1)
    (hIs : (Is.card : ℝ) ≤ 100 * (X / H))
    (hmix : ∀ A₁ A₂ : Finset ι, A₁ ⊆ Is → A₂ ⊆ Is →
      (Work.BMF.quadCount Gq Pp A₁ A₂ : ℝ) ≤
        Cmix * ((A₁.card : ℝ) * (A₂.card : ℝ) * ρ * π0 ^ 2 +
          Real.sqrt ((A₁.card : ℝ) * (A₂.card : ℝ)) * π0 ^ 2 / logP))
    (S : Finset ((ι × Z) × (ι × Z)))
    (hS : ∀ p ∈ S, p.1.1 ∈ Is ∧ p.2.1 ∈ Is ∧ p.1.2 ∈ F p.1.1 ∧ p.2.2 ∈ F p.2.1 ∧
      (∃ p1 p2 : ℕ, p1 ∈ Work.BMF.primesIn Pp (2 * Pp) ∧ p2 ∈ Work.BMF.primesIn Pp (2 * Pp) ∧
        Gq p.1.1 p.2.1 p1 p2) ∧ d p.1.2 p.2.2 ≤ r)
    (hScard : δ * (X / H) * π0 ^ 2 ≤ (S.card : ℝ))
  : 10 ^ 7 * Cmix * M * (K : ℝ) ^ 3 / δ ≥ logP ∨
    ∃ z₀ : Z, ∃ T : Finset (ι × Z),
      (∀ p ∈ T, p.1 ∈ Is ∧ p.2 ∈ F p.1 ∧ d p.2 z₀ ≤ 2 * r) ∧
      (1 / 10 ^ 7) * (δ / (Cmix * M * (K : ℝ) ^ 3)) * (X / H) ≤ (T.card : ℝ) ∧
      ∃ S' ⊆ S, (∀ p ∈ S', p.1 ∈ T ∧ p.2 ∈ T) ∧
        (1 / 10 ^ 7) * (δ ^ 2 / (Cmix * M * (K : ℝ) ^ 4)) * (X / H) * π0 ^ 2 ≤ (S'.card : ℝ) := by
  classical
  by_cases hfirst : logP ≤ 10 ^ 7 * Cmix * M * (K : ℝ) ^ 3 / δ
  · exact Or.inl hfirst
  · push_neg at hfirst
    have hKpos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
    have hlog : 1 / logP < δ / (10 ^ 7 * Cmix * M * (K : ℝ) ^ 3) := by
      have hApos : 0 < 10 ^ 7 * Cmix * M * (K : ℝ) ^ 3 / δ := by positivity
      have := one_div_lt_one_div_of_lt hApos hfirst
      rwa [one_div_div] at this
    -- ### step 1: the ambient set `D` of structures and the refinement `T1 ⊆ D`
    set N : ℝ := X / H with hN
    have hNpos : 0 < N := by rw [hN]; exact div_pos hX hH
    set D : Finset (ι × Z) := Is.biUnion (fun i => (F i).image (fun z => (i, z))) with hD
    have hDmem : ∀ q : ι × Z, q ∈ D ↔ q.1 ∈ Is ∧ q.2 ∈ F q.1 := by
      intro q
      rw [hD, Finset.mem_biUnion]
      constructor
      · rintro ⟨i, hi, hq⟩
        obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hq
        exact ⟨hi, hz⟩
      · rintro ⟨h1, h2⟩
        exact ⟨q.1, h1, Finset.mem_image.mpr ⟨q.2, h2, rfl⟩⟩
    have hDcard : (D.card : ℝ) ≤ 100 * (K : ℝ) * N := by
      have hdc : D.card ≤ K * Is.card := by
        rw [hD]
        calc (Is.biUnion fun i => (F i).image fun z => (i, z)).card
            ≤ ∑ i ∈ Is, ((F i).image (fun z => (i, z))).card := Finset.card_biUnion_le
          _ ≤ ∑ i ∈ Is, (F i).card := Finset.sum_le_sum (fun i _ => Finset.card_image_le)
          _ ≤ ∑ _i ∈ Is, K := Finset.sum_le_sum (fun i _ => hF i)
          _ = K * Is.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
      have hcast : ((D.card : ℕ) : ℝ) ≤ ((K * Is.card : ℕ) : ℝ) := by exact_mod_cast hdc
      have hcast' : (D.card : ℝ) ≤ (K : ℝ) * (Is.card : ℝ) := by simpa using hcast
      calc (D.card : ℝ) ≤ (K : ℝ) * (Is.card : ℝ) := hcast'
        _ ≤ (K : ℝ) * (100 * (X / H)) := by
            apply mul_le_mul_of_nonneg_left hIs; positivity
        _ = 100 * (K : ℝ) * (X / H) := by ring
        _ = 100 * (K : ℝ) * N := by rw [hN]
    set deg : ι × Z → ℕ := fun q => (S.filter (fun p => p.1 = q)).card with hdeg
    have hS_D : ∀ p ∈ S, p.1 ∈ D := by
      intro p hp
      exact (hDmem p.1).mpr ⟨(hS p hp).1, (hS p hp).2.2.1⟩
    have hSsum : ∑ q ∈ D, (deg q : ℝ) = (S.card : ℝ) := by
      have hmap : Set.MapsTo (fun p : (ι × Z) × (ι × Z) => p.1) (↑S : Set ((ι × Z) × (ι × Z)))
          (↑D : Set (ι × Z)) := fun p hp => hS_D p hp
      have h := Finset.card_eq_sum_card_fiberwise hmap
      have h2 : (∑ q ∈ D, (deg q : ℝ)) =
          ((∑ q ∈ D, (S.filter (fun p => p.1 = q)).card : ℕ) : ℝ) := by
        simp only [hdeg]
        push_cast
        rfl
      rw [h2, h]
    set t0 : ℝ := δ * π0 ^ 2 / (200 * (K : ℝ)) with ht0
    have ht0pos : 0 < t0 := by rw [ht0]; positivity
    set T1 : Finset (ι × Z) := D.filter (fun q => t0 ≤ (deg q : ℝ)) with hT1
    have hT1le : T1 ⊆ D := by rw [hT1]; exact Finset.filter_subset _ _
    have hT1mem : ∀ q, q ∈ T1 ↔ q ∈ D ∧ t0 ≤ (deg q : ℝ) := by
      intro q; rw [hT1, Finset.mem_filter]
    have hsplit : ∑ q ∈ D, (deg q : ℝ) =
        ∑ q ∈ T1, (deg q : ℝ) + ∑ q ∈ D \ T1, (deg q : ℝ) := by
      have hs : D \ T1 = D.filter (fun q => ¬ (t0 ≤ (deg q : ℝ))) := by
        rw [hT1]
        ext q
        simp only [Finset.mem_sdiff, Finset.mem_filter]
        tauto
      rw [hs, hT1]
      exact (Finset.sum_filter_add_sum_filter_not (s := D)
        (p := fun q => t0 ≤ (deg q : ℝ)) (f := fun q => (deg q : ℝ))).symm
    have hsmall : ∑ q ∈ D \ T1, (deg q : ℝ) ≤ δ * N * π0 ^ 2 / 2 := by
      have h1 : ∀ q ∈ D \ T1, (deg q : ℝ) ≤ t0 := by
        intro q hq
        obtain ⟨hqD, hqT⟩ := Finset.mem_sdiff.mp hq
        have hnot : ¬ (q ∈ D ∧ t0 ≤ (deg q : ℝ)) := fun h => hqT ((hT1mem q).mpr h)
        exact le_of_lt (not_le.mp (fun hc => hnot ⟨hqD, hc⟩))
      calc ∑ q ∈ D \ T1, (deg q : ℝ) ≤ ∑ _q ∈ D \ T1, t0 := Finset.sum_le_sum h1
        _ = ((D \ T1).card : ℝ) * t0 := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (D.card : ℝ) * t0 := by
            apply mul_le_mul_of_nonneg_right _ (le_of_lt ht0pos)
            exact_mod_cast Finset.card_le_card Finset.sdiff_subset
        _ ≤ (100 * (K : ℝ) * N) * t0 := mul_le_mul_of_nonneg_right hDcard (le_of_lt ht0pos)
        _ = δ * N * π0 ^ 2 / 2 := by
            rw [ht0]
            have hKnz : (K : ℝ) ≠ 0 := by positivity
            field_simp
            try ring
    have hS1bound : δ * N * π0 ^ 2 / 2 ≤ ∑ q ∈ T1, (deg q : ℝ) := by
      have hSR : δ * N * π0 ^ 2 ≤ (S.card : ℝ) := by rw [hN]; exact hScard
      have h1 : δ * N * π0 ^ 2 ≤ ∑ q ∈ D, (deg q : ℝ) := by rw [hSsum]; exact hSR
      linarith [hsplit, h1, hsmall]
    set S1 : Finset ((ι × Z) × (ι × Z)) := S.filter (fun p => p.1 ∈ T1) with hS1
    have hS1card : δ * N * π0 ^ 2 / 2 ≤ (S1.card : ℝ) := by
      have hmap : Set.MapsTo (fun p : (ι × Z) × (ι × Z) => p.1) (↑S1 : Set _) (↑T1 : Set _) := by
        intro p hp
        rw [hS1] at hp
        exact (Finset.mem_filter.mp hp).2
      have hcard := Finset.card_eq_sum_card_fiberwise hmap
      have hfib : ∀ q ∈ T1, (S1.filter (fun p => p.1 = q)).card =
          (S.filter (fun p => p.1 = q)).card := by
        intro q hq
        congr 1
        rw [hS1, Finset.filter_filter]
        exact Finset.filter_congr
          (fun p _ => ⟨fun h => h.2, fun h => ⟨by rw [h]; exact hq, h⟩⟩)
      have h2 : ((S1.card : ℕ) : ℝ) = ∑ q ∈ T1, (deg q : ℝ) := by
        rw [hcard]
        push_cast
        apply Finset.sum_congr rfl
        intro q hq
        rw [hfib q hq, hdeg]
      linarith [hS1bound]
    -- ### step 2: a maximal `r`-separated net of the points of `T1`
    set ZD : Finset Z := T1.image (fun q => q.2) with hZD
    obtain ⟨Om, hOmZD, hOmsep, hOmcov⟩ := net_exists d r (le_of_lt hr) hd_symm hd_refl ZD
    set A1 : Z → Finset ι := fun z₀ => (T1.filter (fun q => d q.2 z₀ ≤ r)).image (fun q => q.1) with hA1
    set A2 : Z → Finset ι := fun z₀ => (D.filter (fun q => d q.2 z₀ ≤ 2 * r)).image (fun q => q.1) with hA2
    set U : Z → ℕ := fun z₀ => (S1.filter (fun p => d p.1.2 z₀ ≤ r)).card with hU
    have hA1sub : ∀ z₀, A1 z₀ ⊆ Is := by
      intro z₀ i hi
      rw [hA1, Finset.mem_image] at hi
      obtain ⟨q, hq, rfl⟩ := hi
      exact ((hDmem q).mp (hT1le (Finset.mem_filter.mp hq).1)).1
    have hA2sub : ∀ z₀, A2 z₀ ⊆ Is := by
      intro z₀ i hi
      rw [hA2, Finset.mem_image] at hi
      obtain ⟨q, hq, rfl⟩ := hi
      exact ((hDmem q).mp (Finset.mem_filter.mp hq).1).1
    have hlow : (S1.card : ℝ) ≤ ∑ z₀ ∈ Om, (U z₀ : ℝ) := by
      have hsub : S1 ⊆ Om.biUnion (fun z₀ => S1.filter (fun p => d p.1.2 z₀ ≤ r)) := by
        intro p hp
        rw [hS1] at hp
        obtain ⟨hpS, hpT1⟩ := Finset.mem_filter.mp hp
        have hz : p.1.2 ∈ ZD := by rw [hZD]; exact Finset.mem_image.mpr ⟨p.1, hpT1, rfl⟩
        obtain ⟨z₀, hz₀Om, hz₀⟩ := hOmcov p.1.2 hz
        rw [Finset.mem_biUnion]
        exact ⟨z₀, hz₀Om, Finset.mem_filter.mpr ⟨hp, hz₀⟩⟩
      calc (S1.card : ℝ) ≤ ((Om.biUnion (fun z₀ => S1.filter (fun p => d p.1.2 z₀ ≤ r))).card : ℝ) := by
            exact_mod_cast Finset.card_le_card hsub
        _ ≤ ((∑ z₀ ∈ Om, (S1.filter (fun p => d p.1.2 z₀ ≤ r)).card : ℕ) : ℝ) := by
            exact_mod_cast Finset.card_biUnion_le
        _ = ∑ z₀ ∈ Om, (U z₀ : ℝ) := by
            simp only [hU]
            push_cast
            rfl
    -- ### step 3: for each net point, the refined pairs contribute to the mixing count
    have hup : ∀ z₀ ∈ Om, (U z₀ : ℝ) ≤
        (K : ℝ) ^ 2 * (Work.BMF.quadCount Gq Pp (A1 z₀) (A2 z₀) : ℝ) := by
      intro z₀ hz₀
      set E : Finset (ι × ι) := ((A1 z₀).product (A2 z₀)).filter
          (fun v => ∃ p1 p2 : ℕ, p1 ∈ Work.BMF.primesIn Pp (2 * Pp) ∧
            p2 ∈ Work.BMF.primesIn Pp (2 * Pp) ∧ Gq v.1 v.2 p1 p2) with hE
      have step1 : U z₀ ≤ K ^ 2 * E.card := by
        set Uf : Finset ((ι × Z) × (ι × Z)) := S1.filter (fun p => d p.1.2 z₀ ≤ r) with hUf
        have hUfeq : U z₀ = Uf.card := by rw [hU, hUf]
        have hmap : Set.MapsTo (fun p : (ι × Z) × (ι × Z) => (p.1.1, p.2.1))
            (↑Uf : Set _) (↑E : Set _) := by
          intro p hp
          rw [hUf] at hp
          obtain ⟨hpS1, hpd⟩ := Finset.mem_filter.mp hp
          rw [hS1] at hpS1
          obtain ⟨hpS, hpT1⟩ := Finset.mem_filter.mp hpS1
          obtain ⟨hh1, hh2, hh3, hh4, hwit, hh6⟩ := hS p hpS
          change (p.1.1, p.2.1) ∈ E
          rw [hE, Finset.mem_filter]
          refine ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, hwit⟩
          · rw [hA1, Finset.mem_image]
            exact ⟨p.1, Finset.mem_filter.mpr ⟨hpT1, hpd⟩, rfl⟩
          · rw [hA2, Finset.mem_image]
            refine ⟨p.2, Finset.mem_filter.mpr ⟨(hDmem p.2).mpr ⟨hh2, hh4⟩, ?_⟩, rfl⟩
            have htri := hd_tri p.2.2 p.1.2 z₀
            have hsym : d p.2.2 p.1.2 = d p.1.2 p.2.2 := hd_symm _ _
            linarith
        have hcard := Finset.card_eq_sum_card_fiberwise hmap
        have hfib : ∀ v ∈ E, (Uf.filter (fun p => (p.1.1, p.2.1) = v)).card ≤ K ^ 2 := by
          intro v hv
          obtain ⟨i, i'⟩ := v
          have hsub : Uf.filter (fun p => (p.1.1, p.2.1) = (i, i')) ⊆
              S.filter (fun p => p.1.1 = i ∧ p.2.1 = i') := by
            intro p hp
            rw [Finset.mem_filter] at hp
            obtain ⟨hpu, hpe⟩ := hp
            rw [hUf] at hpu
            obtain ⟨hpS1, -⟩ := Finset.mem_filter.mp hpu
            rw [hS1] at hpS1
            obtain ⟨hpS, -⟩ := Finset.mem_filter.mp hpS1
            rw [Finset.mem_filter]
            exact ⟨hpS, by simpa using hpe⟩
          calc (Uf.filter (fun p => (p.1.1, p.2.1) = (i, i'))).card
              ≤ (S.filter (fun p => p.1.1 = i ∧ p.2.1 = i')).card := Finset.card_le_card hsub
            _ ≤ (F i).card * (F i').card :=
                pair_fiber_card F S (fun p hp => ⟨(hS p hp).2.2.1, (hS p hp).2.2.2.1⟩) i i'
            _ ≤ K * K := Nat.mul_le_mul (hF i) (hF i')
            _ = K ^ 2 := by ring
        calc U z₀ = Uf.card := hUfeq
          _ = ∑ v ∈ E, (Uf.filter (fun p => (p.1.1, p.2.1) = v)).card := hcard
          _ ≤ ∑ _v ∈ E, K ^ 2 := Finset.sum_le_sum hfib
          _ = E.card * K ^ 2 := by rw [Finset.sum_const, smul_eq_mul]
          _ = K ^ 2 * E.card := by ring
      have step2 : E.card ≤ Work.BMF.quadCount Gq Pp (A1 z₀) (A2 z₀) := by
        set Q : Finset ((ι × ι) × (ℕ × ℕ)) := (((A1 z₀).product (A2 z₀)).product
            ((Work.BMF.primesIn Pp (2 * Pp)).product (Work.BMF.primesIn Pp (2 * Pp)))).filter
            (fun w => Gq w.1.1 w.1.2 w.2.1 w.2.2) with hQ
        have hquad : Work.BMF.quadCount Gq Pp (A1 z₀) (A2 z₀) = Q.card := by
          rw [Work.BMF.quadCount, hQ]
        rw [hquad]
        have hsub : E ⊆ Q.image (fun w => (w.1.1, w.1.2)) := by
          intro v hv
          rw [hE, Finset.mem_filter] at hv
          obtain ⟨hvA, p1, p2, hp1, hp2, hg⟩ := hv
          rw [Finset.mem_image]
          refine ⟨((v.1, v.2), (p1, p2)), ?_, rfl⟩
          rw [hQ, Finset.mem_filter]
          exact ⟨Finset.mem_product.mpr ⟨hvA, Finset.mem_product.mpr ⟨hp1, hp2⟩⟩, hg⟩
        calc E.card ≤ (Q.image (fun w => (w.1.1, w.1.2))).card := Finset.card_le_card hsub
          _ ≤ Q.card := Finset.card_image_le
      calc (U z₀ : ℝ) ≤ (K : ℝ) ^ 2 * (E.card : ℝ) := by exact_mod_cast step1
        _ ≤ (K : ℝ) ^ 2 * (Work.BMF.quadCount Gq Pp (A1 z₀) (A2 z₀) : ℝ) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact_mod_cast step2
    have hquad_sum : δ * N * π0 ^ 2 / 2 ≤ (K : ℝ) ^ 2 *
        ∑ z₀ ∈ Om, (Work.BMF.quadCount Gq Pp (A1 z₀) (A2 z₀) : ℝ) := by
      calc δ * N * π0 ^ 2 / 2 ≤ (S1.card : ℝ) := hS1card
        _ ≤ ∑ z₀ ∈ Om, (U z₀ : ℝ) := hlow
        _ ≤ ∑ z₀ ∈ Om, (K : ℝ) ^ 2 * (Work.BMF.quadCount Gq Pp (A1 z₀) (A2 z₀) : ℝ) :=
            Finset.sum_le_sum hup
        _ = (K : ℝ) ^ 2 * ∑ z₀ ∈ Om, (Work.BMF.quadCount Gq Pp (A1 z₀) (A2 z₀) : ℝ) := by
            rw [Finset.mul_sum]
    have hmixsum : ∑ z₀ ∈ Om, (Work.BMF.quadCount Gq Pp (A1 z₀) (A2 z₀) : ℝ) ≤
        Cmix * ((∑ z₀ ∈ Om, ((A1 z₀).card : ℝ) * ((A2 z₀).card : ℝ)) * (ρ * π0 ^ 2)
          + (∑ z₀ ∈ Om, Real.sqrt ((A1 z₀).card) * Real.sqrt ((A2 z₀).card)) * (π0 ^ 2 / logP)) := by
      calc ∑ z₀ ∈ Om, (Work.BMF.quadCount Gq Pp (A1 z₀) (A2 z₀) : ℝ)
          ≤ ∑ z₀ ∈ Om, Cmix * (((A1 z₀).card : ℝ) * ((A2 z₀).card : ℝ) * ρ * π0 ^ 2 +
              Real.sqrt (((A1 z₀).card : ℝ) * ((A2 z₀).card : ℝ)) * π0 ^ 2 / logP) :=
            Finset.sum_le_sum (fun z₀ hz₀ => hmix (A1 z₀) (A2 z₀) (hA1sub z₀) (hA2sub z₀))
        _ = Cmix * (∑ z₀ ∈ Om, (((A1 z₀).card : ℝ) * ((A2 z₀).card : ℝ) * ρ * π0 ^ 2 +
              Real.sqrt (((A1 z₀).card : ℝ) * ((A2 z₀).card : ℝ)) * π0 ^ 2 / logP)) := by
            rw [Finset.mul_sum]
        _ = Cmix * ((∑ z₀ ∈ Om, ((A1 z₀).card : ℝ) * ((A2 z₀).card : ℝ)) * (ρ * π0 ^ 2)
              + (∑ z₀ ∈ Om, Real.sqrt ((A1 z₀).card) * Real.sqrt ((A2 z₀).card)) * (π0 ^ 2 / logP)) := by
            congr 1
            rw [Finset.sum_add_distrib]
            congr 1
            · rw [Finset.sum_mul]
              apply Finset.sum_congr rfl
              intro z₀ _
              ring
            · rw [Finset.sum_mul]
              apply Finset.sum_congr rfl
              intro z₀ _
              rw [Real.sqrt_mul (by positivity)]
              ring
    have hA2ball : (∑ z₀ ∈ Om, ((A2 z₀).card : ℝ)) ≤ M * (D.card : ℝ) := by
      calc ∑ z₀ ∈ Om, ((A2 z₀).card : ℝ)
          ≤ ∑ z₀ ∈ Om, ((D.filter (fun q => d q.2 z₀ ≤ 2 * r)).card : ℝ) := by
            apply Finset.sum_le_sum
            intro z₀ hz₀
            rw [hA2]
            exact_mod_cast Finset.card_image_le
        _ ≤ M * (D.card : ℝ) :=
            sum_ball_card d r M (2 * r) hr (by linarith) hd_symm hdoub Om hOmsep D
    have hA1ball : (∑ z₀ ∈ Om, ((A1 z₀).card : ℝ)) ≤ M * (D.card : ℝ) := by
      calc ∑ z₀ ∈ Om, ((A1 z₀).card : ℝ)
          ≤ ∑ z₀ ∈ Om, ((T1.filter (fun q => d q.2 z₀ ≤ r)).card : ℝ) := by
            apply Finset.sum_le_sum
            intro z₀ hz₀
            rw [hA1]
            exact_mod_cast Finset.card_image_le
        _ ≤ M * (T1.card : ℝ) :=
            sum_ball_card d r M r hr (by linarith) hd_symm hdoub Om hOmsep T1
        _ ≤ M * (D.card : ℝ) := by
            apply mul_le_mul_of_nonneg_left _ (le_of_lt hM)
            exact_mod_cast Finset.card_le_card hT1le
    have hcs : (∑ z₀ ∈ Om, Real.sqrt ((A1 z₀).card) * Real.sqrt ((A2 z₀).card)) ≤
        M * (D.card : ℝ) := by
      have h1 : (∑ z₀ ∈ Om, Real.sqrt ((A1 z₀).card) * Real.sqrt ((A2 z₀).card)) ≤
          Real.sqrt (∑ z₀ ∈ Om, ((A1 z₀).card : ℝ)) * Real.sqrt (∑ z₀ ∈ Om, ((A2 z₀).card : ℝ)) :=
        sum_sqrt_mul_sqrt_le Om (fun z₀ => ((A1 z₀).card : ℝ)) (fun z₀ => ((A2 z₀).card : ℝ))
          (fun z₀ _ => by positivity) (fun z₀ _ => by positivity)
      have h2 : Real.sqrt (M * (D.card : ℝ)) * Real.sqrt (M * (D.card : ℝ)) = M * (D.card : ℝ) := by
        rw [← sq, Real.sq_sqrt]
        positivity
      calc (∑ z₀ ∈ Om, Real.sqrt ((A1 z₀).card) * Real.sqrt ((A2 z₀).card))
          ≤ Real.sqrt (∑ z₀ ∈ Om, ((A1 z₀).card : ℝ)) * Real.sqrt (∑ z₀ ∈ Om, ((A2 z₀).card : ℝ)) := h1
        _ ≤ Real.sqrt (M * (D.card : ℝ)) * Real.sqrt (M * (D.card : ℝ)) :=
            mul_le_mul (Real.sqrt_le_sqrt hA1ball) (Real.sqrt_le_sqrt hA2ball)
              (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
        _ = M * (D.card : ℝ) := h2
    set supA : ℝ := ((Om.sup (fun z₀ => (A1 z₀).card) : ℕ) : ℝ) with hsupA
    have hsupA_nn : 0 ≤ supA := by rw [hsupA]; positivity
    have hsup_le : ∀ z₀ ∈ Om, ((A1 z₀).card : ℝ) ≤ supA := by
      intro z₀ hz₀
      rw [hsupA]
      exact_mod_cast (Finset.le_sup (s := Om) (f := fun z₀ => (A1 z₀).card) hz₀)
    have hprod : (∑ z₀ ∈ Om, ((A1 z₀).card : ℝ) * ((A2 z₀).card : ℝ)) ≤
        supA * (M * (D.card : ℝ)) := by
      calc ∑ z₀ ∈ Om, ((A1 z₀).card : ℝ) * ((A2 z₀).card : ℝ)
          ≤ ∑ z₀ ∈ Om, supA * ((A2 z₀).card : ℝ) := by
            apply Finset.sum_le_sum
            intro z₀ hz₀
            exact mul_le_mul_of_nonneg_right (hsup_le z₀ hz₀) (by positivity)
        _ = supA * ∑ z₀ ∈ Om, ((A2 z₀).card : ℝ) := by rw [Finset.mul_sum]
        _ ≤ supA * (M * (D.card : ℝ)) := mul_le_mul_of_nonneg_left hA2ball hsupA_nn
    have hP : (∑ z₀ ∈ Om, ((A1 z₀).card : ℝ) * ((A2 z₀).card : ℝ)) * (ρ * π0 ^ 2) +
          (∑ z₀ ∈ Om, Real.sqrt ((A1 z₀).card) * Real.sqrt ((A2 z₀).card)) * (π0 ^ 2 / logP) ≤
          M * (D.card : ℝ) * π0 ^ 2 * (ρ * supA + 1 / logP) := by
      have h1 : (∑ z₀ ∈ Om, ((A1 z₀).card : ℝ) * ((A2 z₀).card : ℝ)) * (ρ * π0 ^ 2) ≤
          supA * (M * (D.card : ℝ)) * (ρ * π0 ^ 2) :=
        mul_le_mul_of_nonneg_right hprod (by positivity)
      have h2 : (∑ z₀ ∈ Om, Real.sqrt ((A1 z₀).card) * Real.sqrt ((A2 z₀).card)) * (π0 ^ 2 / logP) ≤
          M * (D.card : ℝ) * (π0 ^ 2 / logP) :=
        mul_le_mul_of_nonneg_right hcs (by positivity)
      have h3 : supA * (M * (D.card : ℝ)) * (ρ * π0 ^ 2)
          = M * (D.card : ℝ) * π0 ^ 2 * (ρ * supA) := by ring
      have h4 : M * (D.card : ℝ) * (π0 ^ 2 / logP) = M * (D.card : ℝ) * π0 ^ 2 * (1 / logP) := by ring
      calc (∑ z₀ ∈ Om, ((A1 z₀).card : ℝ) * ((A2 z₀).card : ℝ)) * (ρ * π0 ^ 2) +
            (∑ z₀ ∈ Om, Real.sqrt ((A1 z₀).card) * Real.sqrt ((A2 z₀).card)) * (π0 ^ 2 / logP)
          ≤ supA * (M * (D.card : ℝ)) * (ρ * π0 ^ 2) + M * (D.card : ℝ) * (π0 ^ 2 / logP) :=
            add_le_add h1 h2
        _ = M * (D.card : ℝ) * π0 ^ 2 * (ρ * supA + 1 / logP) := by rw [h3, h4]; ring
    have hkey : δ / 2 ≤ 100 * (K : ℝ) ^ 3 * Cmix * M * (ρ * supA + 1 / logP) := by
      have hsum2 : δ * N * π0 ^ 2 / 2 ≤
          (K : ℝ) ^ 2 * (Cmix * (M * (D.card : ℝ) * π0 ^ 2 * (ρ * supA + 1 / logP))) := by
        calc δ * N * π0 ^ 2 / 2 ≤ (K : ℝ) ^ 2 *
              ∑ z₀ ∈ Om, (Work.BMF.quadCount Gq Pp (A1 z₀) (A2 z₀) : ℝ) := hquad_sum
          _ ≤ (K : ℝ) ^ 2 * (Cmix * (M * (D.card : ℝ) * π0 ^ 2 * (ρ * supA + 1 / logP))) := by
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              calc ∑ z₀ ∈ Om, (Work.BMF.quadCount Gq Pp (A1 z₀) (A2 z₀) : ℝ)
                  ≤ Cmix * ((∑ z₀ ∈ Om, ((A1 z₀).card : ℝ) * ((A2 z₀).card : ℝ)) * (ρ * π0 ^ 2)
                    + (∑ z₀ ∈ Om, Real.sqrt ((A1 z₀).card) * Real.sqrt ((A2 z₀).card))
                      * (π0 ^ 2 / logP)) := hmixsum
                _ ≤ Cmix * (M * (D.card : ℝ) * π0 ^ 2 * (ρ * supA + 1 / logP)) :=
                    mul_le_mul_of_nonneg_left hP (le_of_lt hCmix)
      have hfin : δ * N * π0 ^ 2 / 2 ≤
          100 * (K : ℝ) ^ 3 * Cmix * M * (N * π0 ^ 2) * (ρ * supA + 1 / logP) := by
        calc δ * N * π0 ^ 2 / 2 ≤
              (K : ℝ) ^ 2 * (Cmix * (M * (D.card : ℝ) * π0 ^ 2 * (ρ * supA + 1 / logP))) := hsum2
          _ ≤ (K : ℝ) ^ 2 * (Cmix * (M * (100 * (K : ℝ) * N) * π0 ^ 2 * (ρ * supA + 1 / logP))) := by
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              apply mul_le_mul_of_nonneg_left _ (le_of_lt hCmix)
              have hfac : (0 : ℝ) ≤ π0 ^ 2 * (ρ * supA + 1 / logP) := by positivity
              have hmid : (D.card : ℝ) * (π0 ^ 2 * (ρ * supA + 1 / logP))
                  ≤ (100 * (K : ℝ) * N) * (π0 ^ 2 * (ρ * supA + 1 / logP)) :=
                mul_le_mul_of_nonneg_right hDcard hfac
              calc M * (D.card : ℝ) * π0 ^ 2 * (ρ * supA + 1 / logP)
                  = M * ((D.card : ℝ) * (π0 ^ 2 * (ρ * supA + 1 / logP))) := by ring
                _ ≤ M * ((100 * (K : ℝ) * N) * (π0 ^ 2 * (ρ * supA + 1 / logP))) :=
                    mul_le_mul_of_nonneg_left hmid (le_of_lt hM)
                _ = M * (100 * (K : ℝ) * N) * π0 ^ 2 * (ρ * supA + 1 / logP) := by ring
          _ = 100 * (K : ℝ) ^ 3 * Cmix * M * (N * π0 ^ 2) * (ρ * supA + 1 / logP) := by ring
      have hNπ : 0 < N * π0 ^ 2 := by positivity
      have h3 : δ * (N * π0 ^ 2) ≤
          (2 * (100 * (K : ℝ) ^ 3 * Cmix * M * (ρ * supA + 1 / logP))) * (N * π0 ^ 2) := by
        have := hfin
        ring_nf at this ⊢
        linarith
      have h4 := le_of_mul_le_mul_right h3 hNπ
      linarith
    -- ### step 4: the doubly-counted inequality forces a large cluster
    have hcase : δ / (400 * (K : ℝ) ^ 3 * Cmix * M) ≤ ρ * supA := by
      by_contra hc
      push_neg at hc
      have hpos : 0 < 100 * (K : ℝ) ^ 3 * Cmix * M := by positivity
      have hδ1 : 100 * (K : ℝ) ^ 3 * Cmix * M * (δ / (400 * (K : ℝ) ^ 3 * Cmix * M)) = δ / 4 := by
        field_simp
        try ring
      have hδ2 : 100 * (K : ℝ) ^ 3 * Cmix * M * (δ / (10 ^ 7 * Cmix * M * (K : ℝ) ^ 3)) = δ / 10 ^ 5 := by
        field_simp
        try ring
      have hm1 : 100 * (K : ℝ) ^ 3 * Cmix * M * (ρ * supA) < δ / 4 := by
        rw [← hδ1]
        exact mul_lt_mul_of_pos_left hc hpos
      have hm2 : 100 * (K : ℝ) ^ 3 * Cmix * M * (1 / logP) < δ / 10 ^ 5 := by
        rw [← hδ2]
        exact mul_lt_mul_of_pos_left hlog hpos
      have hexp : 100 * (K : ℝ) ^ 3 * Cmix * M * (ρ * supA + 1 / logP)
          = 100 * (K : ℝ) ^ 3 * Cmix * M * (ρ * supA)
            + 100 * (K : ℝ) ^ 3 * Cmix * M * (1 / logP) := by ring
      linarith [hkey, hm1, hm2, hexp]
    have hsup_ge : δ / (400 * (K : ℝ) ^ 3 * Cmix * M) * (X / H) ≤ supA := by
      have h1 : δ / (400 * (K : ℝ) ^ 3 * Cmix * M) * (1 / ρ) ≤ supA := by
        have h2 : δ / (400 * (K : ℝ) ^ 3 * Cmix * M) * (1 / ρ) ≤ (ρ * supA) * (1 / ρ) :=
          mul_le_mul_of_nonneg_right hcase (by positivity)
        have h3 : (ρ * supA) * (1 / ρ) = supA := by field_simp
        linarith [h2, h3.le, h3.ge]
      have h4 : (X / H) ≤ 1 / ρ := by
        have h5 : (X / H) * ρ ≤ 1 := by rw [mul_comm]; exact hρXH
        exact (le_div_iff₀ hρ).mpr h5
      calc δ / (400 * (K : ℝ) ^ 3 * Cmix * M) * (X / H)
          ≤ δ / (400 * (K : ℝ) ^ 3 * Cmix * M) * (1 / ρ) := by
            apply mul_le_mul_of_nonneg_left h4; positivity
        _ ≤ supA := h1
    have hOmne : Om.Nonempty := by
      by_contra h
      rw [Finset.not_nonempty_iff_eq_empty] at h
      have hzero : (∑ z₀ ∈ Om, (U z₀ : ℝ)) = 0 := by rw [h]; simp
      have hpos : 0 < δ * N * π0 ^ 2 / 2 := by positivity
      linarith [hS1card, hlow, hzero]
    obtain ⟨zstar, hzstarOm, hzstar⟩ := Finset.exists_mem_eq_sup Om hOmne (fun z₀ => (A1 z₀).card)
    have hA1star : supA = ((A1 zstar).card : ℝ) := by
      rw [hsupA, hzstar]
    -- ### step 5: the cluster and the pairs inside it
    set T : Finset (ι × Z) := D.filter (fun q => d q.2 zstar ≤ 2 * r) with hT
    set S' : Finset ((ι × Z) × (ι × Z)) := S.filter (fun p => p.1 ∈ T ∧ p.2 ∈ T) with hS'
    refine Or.inr ⟨zstar, T, ?_, ?_, S', ?_, ?_, ?_⟩
    · intro p hp
      rw [hT] at hp
      obtain ⟨hpD, hpd⟩ := Finset.mem_filter.mp hp
      exact ⟨((hDmem p).mp hpD).1, ((hDmem p).mp hpD).2, hpd⟩
    · have hcardT : ((A2 zstar).card : ℝ) ≤ (T.card : ℝ) := by
        rw [hA2, hT]
        exact_mod_cast Finset.card_image_le
      have hA1leA2 : (A1 zstar).card ≤ (A2 zstar).card := by
        apply Finset.card_le_card
        intro i hi
        rw [hA1, Finset.mem_image] at hi
        obtain ⟨q, hq, hqi⟩ := hi
        rw [Finset.mem_filter] at hq
        obtain ⟨hqT1, hqd⟩ := hq
        rw [hA2, Finset.mem_image]
        refine ⟨q, Finset.mem_filter.mpr ⟨hT1le hqT1, ?_⟩, hqi⟩
        linarith
      have hconst : (1 / 10 ^ 7) * (δ / (Cmix * M * (K : ℝ) ^ 3)) ≤
          δ / (400 * (K : ℝ) ^ 3 * Cmix * M) := by
        have hn : (1 : ℝ) / 10 ^ 7 ≤ 1 / 400 := by norm_num
        calc (1 / 10 ^ 7) * (δ / (Cmix * M * (K : ℝ) ^ 3))
            = ((1 : ℝ) / 10 ^ 7) * (δ / (Cmix * M * (K : ℝ) ^ 3)) := rfl
          _ ≤ (1 / 400) * (δ / (Cmix * M * (K : ℝ) ^ 3)) := by
              apply mul_le_mul_of_nonneg_right hn; positivity
          _ = δ / (400 * (K : ℝ) ^ 3 * Cmix * M) := by field_simp; try ring
      calc (1 / 10 ^ 7) * (δ / (Cmix * M * (K : ℝ) ^ 3)) * (X / H)
          ≤ δ / (400 * (K : ℝ) ^ 3 * Cmix * M) * (X / H) := by
            apply mul_le_mul_of_nonneg_right hconst; positivity
        _ ≤ supA := hsup_ge
        _ = ((A1 zstar).card : ℝ) := hA1star
        _ ≤ ((A2 zstar).card : ℝ) := by exact_mod_cast hA1leA2
        _ ≤ (T.card : ℝ) := hcardT
    · rw [hS']; exact Finset.filter_subset _ _
    · intro p hp
      rw [hS'] at hp
      exact (Finset.mem_filter.mp hp).2
    · set T2 : Finset (ι × Z) := T1.filter (fun q => q.1 ∈ A1 zstar ∧ d q.2 zstar ≤ r) with hT2
      have hA1leT2 : (A1 zstar).card ≤ T2.card := by
        have himg : A1 zstar ⊆ T2.image (fun q => q.1) := by
          intro i hi
          rw [hA1, Finset.mem_image] at hi
          obtain ⟨q, hq, hqi⟩ := hi
          rw [Finset.mem_filter] at hq
          obtain ⟨hqT1, hqd⟩ := hq
          have hqA1 : q.1 ∈ A1 zstar := by
            rw [hA1, Finset.mem_image]
            exact ⟨q, Finset.mem_filter.mpr ⟨hqT1, hqd⟩, rfl⟩
          rw [Finset.mem_image]
          exact ⟨q, Finset.mem_filter.mpr ⟨hqT1, ⟨hqA1, hqd⟩⟩, hqi⟩
        calc (A1 zstar).card ≤ (T2.image (fun q => q.1)).card := Finset.card_le_card himg
          _ ≤ T2.card := Finset.card_image_le
      have hsub' : S.filter (fun p => p.1 ∈ T2) ⊆ S' := by
        intro p hp
        obtain ⟨hpS, hpT2⟩ := Finset.mem_filter.mp hp
        obtain ⟨hh1, hh2, hh3, hh4, hhwit, hh6⟩ := hS p hpS
        rw [hT2] at hpT2
        obtain ⟨hpT1, hpA1, hpd⟩ := Finset.mem_filter.mp hpT2
        rw [hS', Finset.mem_filter]
        refine ⟨hpS, ?_, ?_⟩
        · rw [hT, Finset.mem_filter]
          exact ⟨hT1le hpT1, by linarith⟩
        · rw [hT, Finset.mem_filter]
          refine ⟨(hDmem p.2).mpr ⟨hh2, hh4⟩, ?_⟩
          have htri := hd_tri p.2.2 p.1.2 zstar
          have hsym : d p.2.2 p.1.2 = d p.1.2 p.2.2 := hd_symm _ _
          linarith
      have hfiber2 : ((S.filter (fun p => p.1 ∈ T2)).card : ℝ) = ∑ q ∈ T2, (deg q : ℝ) := by
        have hmap : Set.MapsTo (fun p : (ι × Z) × (ι × Z) => p.1)
            (↑(S.filter (fun p => p.1 ∈ T2)) : Set _) (↑T2 : Set _) :=
          fun p hp => (Finset.mem_filter.mp hp).2
        have h := Finset.card_eq_sum_card_fiberwise hmap
        rw [h]
        push_cast
        apply Finset.sum_congr rfl
        intro q hq
        rw [hdeg]
        have hfe : (S.filter (fun p => p.1 ∈ T2)).filter (fun p => p.1 = q) =
            S.filter (fun p => p.1 = q) := by
          rw [Finset.filter_filter]
          exact Finset.filter_congr (fun p _ => ⟨fun h => h.2, fun h => ⟨by rw [h]; exact hq, h⟩⟩)
        rw [hfe]
      have hge : (T2.card : ℝ) * t0 ≤ (S'.card : ℝ) := by
        have h1 : ∀ q ∈ T2, t0 ≤ (deg q : ℝ) := by
          intro q hq
          rw [hT2, Finset.mem_filter] at hq
          exact ((hT1mem q).mp hq.1).2
        calc (T2.card : ℝ) * t0 = ∑ _q ∈ T2, t0 := by rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ ∑ q ∈ T2, (deg q : ℝ) := Finset.sum_le_sum h1
          _ = ((S.filter (fun p => p.1 ∈ T2)).card : ℝ) := hfiber2.symm
          _ ≤ (S'.card : ℝ) := by exact_mod_cast Finset.card_le_card hsub'
      have hmono : (1 / 10 ^ 7) * (δ ^ 2 / (Cmix * M * (K : ℝ) ^ 4)) * (X / H) * π0 ^ 2
          ≤ δ / (400 * (K : ℝ) ^ 3 * Cmix * M) * (X / H) * t0 := by
        have hCn : (1 / 10 ^ 7) * (δ ^ 2 / (Cmix * M * (K : ℝ) ^ 4))
            ≤ (δ / (400 * (K : ℝ) ^ 3 * Cmix * M)) * (δ / (200 * (K : ℝ))) := by
          have hn : (1 : ℝ) / 10 ^ 7 ≤ 1 / 80000 := by norm_num
          calc (1 / 10 ^ 7) * (δ ^ 2 / (Cmix * M * (K : ℝ) ^ 4))
              = ((1 : ℝ) / 10 ^ 7) * (δ ^ 2 / (Cmix * M * (K : ℝ) ^ 4)) := rfl
            _ ≤ (1 / 80000) * (δ ^ 2 / (Cmix * M * (K : ℝ) ^ 4)) := by
                apply mul_le_mul_of_nonneg_right hn; positivity
            _ = (δ / (400 * (K : ℝ) ^ 3 * Cmix * M)) * (δ / (200 * (K : ℝ))) := by
                field_simp; try ring
        calc (1 / 10 ^ 7) * (δ ^ 2 / (Cmix * M * (K : ℝ) ^ 4)) * (X / H) * π0 ^ 2
            = ((1 / 10 ^ 7) * (δ ^ 2 / (Cmix * M * (K : ℝ) ^ 4))) * ((X / H) * π0 ^ 2) := by ring
          _ ≤ ((δ / (400 * (K : ℝ) ^ 3 * Cmix * M)) * (δ / (200 * (K : ℝ)))) * ((X / H) * π0 ^ 2) := by
              apply mul_le_mul_of_nonneg_right hCn; positivity
          _ = δ / (400 * (K : ℝ) ^ 3 * Cmix * M) * (X / H) * t0 := by rw [ht0]; ring
      calc (1 / 10 ^ 7) * (δ ^ 2 / (Cmix * M * (K : ℝ) ^ 4)) * (X / H) * π0 ^ 2
          ≤ δ / (400 * (K : ℝ) ^ 3 * Cmix * M) * (X / H) * t0 := hmono
        _ ≤ supA * t0 := by
            apply mul_le_mul_of_nonneg_right hsup_ge (le_of_lt ht0pos)
        _ = ((A1 zstar).card : ℝ) * t0 := by rw [hA1star]
        _ ≤ (T2.card : ℝ) * t0 := by
            apply mul_le_mul_of_nonneg_right _ (le_of_lt ht0pos)
            exact_mod_cast hA1leT2
        _ ≤ (S'.card : ℝ) := hge

end Work.N8
