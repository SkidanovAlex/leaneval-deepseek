import Submission.EFL.S12Step8
import Submission.EFL.S12Step9
import Submission.EFL.LowerReg
import Submission.EFL.OptCol
import Submission.Commons.Combinatorics.Set.ncard_biUnion_le

/-!
# §12, Step 8 (`step:step8`), continued: `stat:r_rem`

This module formalises the remaining part of **Step 8** of the proof of
Theorem 1.1 (the paper's `stat:r_rem`): the analysis of the leftover graph
`G_final = (V(𝓗), R_final)` in the Type A₂ case.

* **`(eqn:deficit)`** (`s12_deficit`): for every vertex `w`,
  `d_{R_res ∖ R_final}(w) ≤ |𝓜_diff ∪ 𝓜_hm ∪ 𝓜_buff| + 2γD ≤ 15γ^{1/2}n`.
  The first term counts the matchings of `𝓜_prev` other than `𝓜_main` (each
  contributes at most one edge through `w`), and the second is MA2(i).

* **`stat:r_rem`, first half** (`s12_delta_le`): if `R_res` is a Type A₂
  reservoir (so `(ρ - 20ε)n ≤ d_{R_res}(w) ≤ (ρ + ξ)n` for every `w`) then
  `Δ(G_final) - d_{G_final}(v) ≤ 22εn` for every `v` -- the form in which
  Corollary 10.13 (`optcol_corollary`) consumes it.

* **`stat:r_rem`, second half** (the lower `(ρ/4, ε^{1/3})`-regularity of
  `G_final`): the counting lemmas `fibreCount_ge`, `edgeCount_ge_sum` and
  `edgeCount_ge_of_deg` give `e_{G'}(A,B) ≥ (|A| - εn)|B|` for `A,B ⊆ U`, which
  combined with the lower `(ρ/2, ξ, G')`-regularity of `R_abs` and the
  robustness `lowerRegular_of_delete`/`selfLowerRegular_mono` (Proposition
  10.3) yields the claimed lower regularity.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open scoped BigOperators

namespace ErdosFaberLovaszConjecture

noncomputable section

variable {n : ℕ}

/-! ## `(eqn:deficit)`: the number of deleted reservoir edges -/

/-- The edge set of a family of graphs indexed by a finite type. -/
theorem iUnion_eq_biUnion_finset {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : ι → Hypergraph (Fin n)) (t : Finset ι) :
    (⋃ i ∈ (t : Set ι), S i) ∪ (⋃ i ∈ ((tᶜ : Finset ι) : Set ι), S i) = ⋃ i, S i := by
  ext e
  simp only [Set.mem_union, Set.mem_iUnion]
  constructor
  · rintro (⟨i, -, hi⟩ | ⟨i, hi, hii⟩)
    · exact ⟨i, hi⟩
    · exact ⟨i, hii⟩
  · rintro ⟨i, hi⟩
    by_cases hit : i ∈ t
    · exact Or.inl ⟨i, hit, hi⟩
    · exact Or.inr ⟨i, Finset.mem_compl.mpr hit, hi⟩

/-- **§12, Step 8, `(eqn:deficit)`.**  If `R_final = R_res ∖ ⋃_i S i`, the
families `S i` for `i ∈ t` are matchings (each contributing at most one edge
through any vertex) and the remaining ones contribute at most `C` edges
through any vertex (after intersecting with `R_res`), then
`d_{R_res ∖ R_final}(w) ≤ |t| + C`. -/
theorem s12_deficit {R_res R_final : Hypergraph (Fin n)} {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : ι → Hypergraph (Fin n)} (t : Finset ι) {C : ℝ}
    (hRfin : R_final = R_res \ (⋃ i, S i))
    (hmatch : ∀ i ∈ t, ∀ w : Fin n, degAt (S i) w ≤ 1)
    (hmain : ∀ w : Fin n, (degAt (R_res ∩ (⋃ i ∈ ((tᶜ : Finset ι) : Set ι), S i)) w : ℝ) ≤ C)
    (w : Fin n) :
    (degAt (R_res \ R_final) w : ℝ) ≤ (t.card : ℝ) + C := by
  classical
  have hEq : R_res \ R_final = R_res ∩ (⋃ i, S i) := by
    rw [hRfin]
    ext e
    simp only [Set.mem_sdiff, Set.mem_inter_iff, Set.mem_iUnion]
    tauto
  rw [hEq]
  have hsplit : R_res ∩ (⋃ i, S i) =
      (R_res ∩ (⋃ i ∈ (t : Set ι), S i)) ∪
        (R_res ∩ (⋃ i ∈ ((tᶜ : Finset ι) : Set ι), S i)) := by
    rw [← iUnion_eq_biUnion_finset S t, Set.inter_union_distrib_left]
  rw [hsplit]
  -- the first part contributes at most `|t|`
  have hA : (degAt (R_res ∩ (⋃ i ∈ (t : Set ι), S i)) w : ℝ) ≤ (t.card : ℝ) := by
    have h1 : degAt (R_res ∩ (⋃ i ∈ (t : Set ι), S i)) w ≤ degAt (⋃ i ∈ (t : Set ι), S i) w :=
      degAt_mono Set.inter_subset_right w
    have hnbr : nbrs (⋃ i ∈ (t : Set ι), S i) w = ⋃ i ∈ t, nbrs (S i) w := by
      ext x
      simp only [nbrs, Set.mem_ofPred_eq, Set.mem_iUnion]
      constructor
      · rintro ⟨i, hi, hx⟩
        exact ⟨i, hi, hx⟩
      · rintro ⟨i, hi, hx⟩
        exact ⟨i, hi, hx⟩
    have h2 : degAt (⋃ i ∈ (t : Set ι), S i) w ≤ ∑ i ∈ t, degAt (S i) w := by
      show (nbrs (⋃ i ∈ (t : Set ι), S i) w).ncard ≤ _
      rw [hnbr]
      exact Commons.Combinatorics.Set.ncard_biUnion_le t (fun i => nbrs (S i) w)
        (fun i _ => Set.toFinite _)
    have h3 : ∑ i ∈ t, degAt (S i) w ≤ t.card := by
      have h4 : ∑ i ∈ t, degAt (S i) w ≤ ∑ _i ∈ t, 1 :=
        Finset.sum_le_sum (fun i hi => hmatch i hi w)
      have h5 : ∑ _i ∈ t, (1 : ℕ) = t.card := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_one]
        norm_num
      omega
    have := le_trans h1 (le_trans h2 h3)
    exact_mod_cast this
  have hB := hmain w
  have h3 : (degAt ((R_res ∩ (⋃ i ∈ (t : Set ι), S i)) ∪
      (R_res ∩ (⋃ i ∈ ((tᶜ : Finset ι) : Set ι), S i))) w : ℝ) ≤
      (degAt (R_res ∩ (⋃ i ∈ (t : Set ι), S i)) w : ℝ) +
        (degAt (R_res ∩ (⋃ i ∈ ((tᶜ : Finset ι) : Set ι), S i)) w : ℝ) := by
    have h4 : degAt ((R_res ∩ (⋃ i ∈ (t : Set ι), S i)) ∪
        (R_res ∩ (⋃ i ∈ ((tᶜ : Finset ι) : Set ι), S i))) w ≤
        degAt (R_res ∩ (⋃ i ∈ (t : Set ι), S i)) w +
          degAt (R_res ∩ (⋃ i ∈ ((tᶜ : Finset ι) : Set ι), S i)) w := by
      show (nbrs _ w).ncard ≤ _
      rw [nbrs_union]
      exact Set.ncard_union_le _ _
    exact_mod_cast h4
  linarith


/-! ## `stat:r_rem`, first half: `Δ(G_final) - d_{G_final}(v) ≤ 22εn` -/

/-- `Δ(𝓖) ≤ M` from a real upper bound on all the degrees. -/
theorem hypergraphMaxDegree_le_of_le {𝓖 : Hypergraph (Fin n)}
    (h2 : ∀ e ∈ 𝓖, edgeSize e = 2) {M : ℝ} (hM0 : 0 ≤ M)
    (h : ∀ v : Fin n, (degAt 𝓖 v : ℝ) ≤ M) : (hypergraphMaxDegree 𝓖 : ℝ) ≤ M := by
  rw [hypergraphMaxDegree_eq_sup 𝓖 h2]
  have h1 : (Finset.univ : Finset (Fin n)).sup (fun v => degAt 𝓖 v) ≤ ⌊M⌋₊ :=
    Finset.sup_le (fun v _ => Nat.le_floor (h v))
  have h3 : ((⌊M⌋₊ : ℕ) : ℝ) ≤ M := Nat.floor_le hM0
  calc (((Finset.univ : Finset (Fin n)).sup (fun v => degAt 𝓖 v) : ℕ) : ℝ)
      ≤ ((⌊M⌋₊ : ℕ) : ℝ) := by exact_mod_cast h1
    _ ≤ M := h3

/-- **§12, Step 8, `stat:r_rem` (first half).**  If `R_res` is a Type A₂
reservoir (so `(ρ-20ε)n ≤ d_{R_res}(w) ≤ (ρ+ξ)n` for every `w`) and at most
`15γ^{1/2}n` reservoir edges through any vertex are deleted, then

`Δ(G_final) - d_{G_final}(v) ≤ 22εn`

for every vertex `v` -- the hypothesis of Corollary 10.13. -/
theorem s12_delta_le {R_res R_final : Hypergraph (Fin n)} {ρ ξ ε γ : ℝ}
    (hRfin : R_final ⊆ R_res)
    (h2 : ∀ e ∈ R_final, edgeSize e = 2)
    (hM0 : 0 ≤ (ρ + ξ) * (n : ℝ))
    (hub : ∀ w : Fin n, (degAt R_res w : ℝ) ≤ (ρ + ξ) * (n : ℝ))
    (hlb : ∀ w : Fin n, (ρ - 20 * ε) * (n : ℝ) ≤ (degAt R_res w : ℝ))
    (hdeficit : ∀ w : Fin n, (degAt (R_res \ R_final) w : ℝ) ≤ 15 * Real.sqrt γ * (n : ℝ))
    (hnum : ξ + 20 * ε + 15 * Real.sqrt γ ≤ 22 * ε) :
    ∀ v : Fin n, (hypergraphMaxDegree R_final : ℝ) - (degAt R_final v : ℝ) ≤
      22 * ε * (n : ℝ) := by
  intro v
  have hsplit : (degAt R_res v : ℝ) ≤
      (degAt R_final v : ℝ) + (degAt (R_res \ R_final) v : ℝ) := by
    have h2' : R_final ∪ (R_res \ R_final) = R_res := union_sdiff_eq hRfin
    have h5 : degAt (R_final ∪ (R_res \ R_final)) v =
        (nbrs R_final v ∪ nbrs (R_res \ R_final) v).ncard := by
      show (nbrs (R_final ∪ (R_res \ R_final)) v).ncard = _
      rw [nbrs_union]
    have h1 : degAt R_res v ≤ degAt R_final v + degAt (R_res \ R_final) v :=
      calc degAt R_res v = degAt (R_final ∪ (R_res \ R_final)) v := by rw [h2']
        _ = (nbrs R_final v ∪ nbrs (R_res \ R_final) v).ncard := h5
        _ ≤ (nbrs R_final v).ncard + (nbrs (R_res \ R_final) v).ncard :=
            Set.ncard_union_le _ _
        _ = degAt R_final v + degAt (R_res \ R_final) v := rfl
    exact_mod_cast h1
  have hmax : (hypergraphMaxDegree R_final : ℝ) ≤ (ρ + ξ) * (n : ℝ) := by
    refine hypergraphMaxDegree_le_of_le h2 hM0 (fun w => ?_)
    exact le_trans (by exact_mod_cast degAt_mono hRfin w) (hub w)
  have hv : (ρ - 20 * ε) * (n : ℝ) - 15 * Real.sqrt γ * (n : ℝ) ≤ (degAt R_final v : ℝ) := by
    linarith [hsplit, hlb v, hdeficit v]
  have hnum' : (ρ + ξ) * (n : ℝ) - ((ρ - 20 * ε) * (n : ℝ) - 15 * Real.sqrt γ * (n : ℝ)) ≤
      22 * ε * (n : ℝ) := by
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    nlinarith
  linarith


/-! ## Counting the edges between `A` and `B` from below -/

/-- `edgeCount` is unchanged on pairs inside `U` when the family is restricted
to the edges contained in `U`. -/
theorem edgeCount_induce (R : Hypergraph (Fin n)) (U : Set (Fin n)) (A B : Finset (Fin n))
    (hA : ∀ a ∈ A, a ∈ U) (hB : ∀ b ∈ B, b ∈ U) :
    edgeCount {e ∈ R | e ⊆ U} A B = edgeCount R A B := by
  classical
  rw [edgeCount_eq_ncard, edgeCount_eq_ncard]
  congr 1
  ext p
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hp1, hp2, hp3, -⟩
    exact ⟨hp1, hp2, hp3⟩
  · rintro ⟨hp1, hp2, hp3⟩
    exact ⟨hp1, hp2, hp3, by
      intro x hx
      rcases hx with rfl | rfl
      · exact hA p.1 hp1
      · exact hB p.2 hp2⟩

/-- The number of neighbours of `b` inside `A` is at least
`|A| - (n - d_R(b))`. -/
theorem fibreCount_ge_real (R : Hypergraph (Fin n)) (A : Finset (Fin n)) (b : Fin n) :
    (A.card : ℝ) - ((n - degAt R b : ℕ) : ℝ) ≤ (fibreCount R A b : ℝ) := by
  classical
  have hsplit := Finset.card_filter_add_card_filter_not (s := A)
    (p := fun a => ({a, b} : Set (Fin n)) ∈ R)
  have hsplitR : ((A.filter (fun a => ({a, b} : Set (Fin n)) ∈ R)).card : ℝ) +
      ((A.filter (fun a => ({a, b} : Set (Fin n)) ∉ R)).card : ℝ) = (A.card : ℝ) := by
    rw [← Nat.cast_add, hsplit]
  have hle : (A.filter (fun a => ({a, b} : Set (Fin n)) ∉ R)).card ≤ n - degAt R b := by
    have hsub : ((A.filter (fun a => ({a, b} : Set (Fin n)) ∉ R) : Finset (Fin n)) :
        Set (Fin n)) ⊆ (nbrs R b)ᶜ := by
      intro a ha
      rw [Finset.mem_coe, Finset.mem_filter] at ha
      simp only [nbrs]
      intro h
      exact ha.2 (by
        have h' : ({b, a} : Set (Fin n)) ∈ R := h
        rwa [Set.pair_comm] at h')
    have h1 : (A.filter (fun a => ({a, b} : Set (Fin n)) ∉ R)).card ≤
        ((nbrs R b)ᶜ).ncard := by
      rw [← Set.ncard_coe_finset]
      exact Set.ncard_le_ncard hsub (Set.toFinite _)
    have h2 : ((nbrs R b)ᶜ).ncard + degAt R b = n := by
      have h3 := Set.ncard_compl_add_ncard (nbrs R b)
      rwa [Nat.card_eq_fintype_card, Fintype.card_fin] at h3
    omega
  have hleR : ((A.filter (fun a => ({a, b} : Set (Fin n)) ∉ R)).card : ℝ) ≤
      ((n - degAt R b : ℕ) : ℝ) := by exact_mod_cast hle
  unfold fibreCount
  linarith

/-- **The lower bound on `e_R(A,B)`.**  If every vertex of `B` has degree at
least `(1-ε)n` in `R`, then `e_R(A,B) ≥ (|A| - εn)|B|`. -/
theorem edgeCount_ge_of_deg (R : Hypergraph (Fin n)) (A B : Finset (Fin n)) {ε : ℝ}
    (hε0 : 0 ≤ ε) (hB : ∀ b ∈ B, (1 - ε) * (n : ℝ) ≤ (degAt R b : ℝ)) :
    ((A.card : ℝ) - ε * (n : ℝ)) * (B.card : ℝ) ≤ (edgeCount R A B : ℝ) := by
  classical
  rw [edgeCount_eq_sum_fiber, Nat.cast_sum]
  have h1 : ∑ b ∈ B, ((A.card : ℝ) - ε * (n : ℝ)) ≤
      ∑ b ∈ B, (fibreCount R A b : ℝ) := by
    apply Finset.sum_le_sum
    intro b hb
    have h2 : ((n - degAt R b : ℕ) : ℝ) ≤ ε * (n : ℝ) := by
      by_cases h5 : degAt R b ≤ n
      · rw [Nat.cast_sub h5]
        linarith [hB b hb]
      · have h6 : n - degAt R b = 0 := by omega
        rw [h6, Nat.cast_zero]
        exact mul_nonneg hε0 (Nat.cast_nonneg n)
    have h3 := fibreCount_ge_real R A b
    linarith
  have h4 : ∑ b ∈ B, ((A.card : ℝ) - ε * (n : ℝ)) =
      ((A.card : ℝ) - ε * (n : ℝ)) * (B.card : ℝ) := by
    rw [Finset.sum_const, nsmul_eq_mul]
    ring
  rw [← h4]
  exact h1

/-- The vertices of `U` have degree at least `(1-ε)n` in `G' = incidentTwo 𝓗 U`,
so `e_{G'}(A,B) ≥ (|A| - εn)|B|` for `A, B ⊆ U`. -/
theorem edgeCount_incidentTwo_ge (𝓗 : Hypergraph (Fin n)) {U : Set (Fin n)} {ε : ℝ}
    (hε0 : 0 ≤ ε) (hU : U ⊆ Vplus 𝓗 (1 - ε)) (A B : Finset (Fin n))
    (hA : ∀ a ∈ A, a ∈ U) (hB : ∀ b ∈ B, b ∈ U) :
    ((A.card : ℝ) - ε * (n : ℝ)) * (B.card : ℝ) ≤
      (edgeCount (incidentTwo 𝓗 U) A B : ℝ) := by
  refine edgeCount_ge_of_deg (incidentTwo 𝓗 U) A B hε0 (fun b hb => ?_)
  rw [degAt_incidentTwo_eq 𝓗 (hB b hb)]
  exact hU (hB b hb)


/-! ## `stat:r_rem`, second half: the lower regularity of `G_final` -/

/-- Monotonicity of `SelfLowerRegular` in the parameters. -/
theorem SelfLowerRegular.mono {𝓖 : Hypergraph (Fin n)} {X : Set (Fin n)} {ρ ξ ρ' ξ' : ℝ}
    (h : SelfLowerRegular 𝓖 X ρ ξ) (hξ : ξ ≤ ξ') (hρξ : ρ' - ξ' ≤ ρ - ξ) :
    SelfLowerRegular 𝓖 X ρ' ξ' := by
  intro A B hAX hBX hdisj hA hB
  have hA' : ξ * (X.ncard : ℝ) ≤ (A.card : ℝ) := by
    have h1 : ξ * (X.ncard : ℝ) ≤ ξ' * (X.ncard : ℝ) :=
      mul_le_mul_of_nonneg_right hξ (Nat.cast_nonneg _)
    linarith
  have hB' : ξ * (X.ncard : ℝ) ≤ (B.card : ℝ) := by
    have h1 : ξ * (X.ncard : ℝ) ≤ ξ' * (X.ncard : ℝ) :=
      mul_le_mul_of_nonneg_right hξ (Nat.cast_nonneg _)
    linarith
  have h1 := h A B hAX hBX hdisj hA' hB'
  have h2 : (ρ' - ξ') * (A.card : ℝ) * (B.card : ℝ) ≤ (ρ - ξ) * (A.card : ℝ) * (B.card : ℝ) := by
    have h3 : (0 : ℝ) ≤ (A.card : ℝ) * (B.card : ℝ) :=
      mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    nlinarith [hρξ, h3]
  linarith

/-- The induced family on `U`. -/
abbrev induceU (R : Hypergraph (Fin n)) (U : Set (Fin n)) : Hypergraph (Fin n) :=
  {e ∈ R | e ⊆ U}

/-- **§12, Step 8, `stat:r_rem` (second half), the graph on `U`.**  If `R_abs` is
lower `(ρ/2, ξ)`-regular with respect to `G' = incidentTwo 𝓗 U`, the vertices
of `U` have `G'`-degree at least `(1-ε)n`, and deleting `R_final` from `R_abs`
removes at most `αn` edges at every vertex, then the induced family
`G_final[U] = {e ∈ R_final : e ⊆ U}` is lower `(ρ/3, ξ')`-regular on `U`. -/
theorem s12_selfLowerRegular_U {𝓗 R_abs R_final : Hypergraph (Fin n)} {U : Set (Fin n)}
    {ρ ξ α ξ' ε : ℝ}
    (hU : U ⊆ Vplus 𝓗 (1 - ε)) (hε0 : 0 ≤ ε)
    (hRabs : LowerRegular (incidentTwo 𝓗 U) R_abs (ρ / 2) ξ)
    (hdef : ∀ w : Fin n, (degAt (R_abs \ R_final) w : ℝ) ≤ α * (n : ℝ))
    (hα0 : 0 ≤ α) (hUbig : (n : ℝ) ≤ 2 * (U.ncard : ℝ))
    (hξ0 : 0 ≤ ξ) (hξ'0 : 0 ≤ ξ') (hρ0 : 0 ≤ ρ)
    (hth : (ξ + Real.sqrt α) * (n : ℝ) ≤ ξ' * (U.ncard : ℝ))
    (hnumε : Real.sqrt ε ≤ ξ')
    (hnum : ρ / 2 * (1 - 2 * Real.sqrt ε) ≥ (ξ + Real.sqrt α) + (ρ / 3 - ξ')) :
    SelfLowerRegular (induceU R_final U) U (ρ / 3) ξ' := by
  classical
  -- the lower regularity of `R_abs ∩ R_final`
  have hdef' : ∀ w : Fin n, (degAt (R_abs \ (R_abs ∩ R_final)) w : ℝ) ≤ α * (n : ℝ) := by
    intro w
    have hEq : R_abs \ (R_abs ∩ R_final) = R_abs \ R_final := by
      ext e
      simp only [Set.mem_sdiff, Set.mem_inter_iff]
      tauto
    rw [hEq]
    exact hdef w
  have hlrDel := lowerRegular_of_delete (incidentTwo 𝓗 U) R_abs (R_abs ∩ R_final)
    Set.inter_subset_left hRabs hα0 hξ0 hdef'
  intro A B hAX hBX hdisj hA hB
  have hA' : ((ξ + Real.sqrt α) * (n : ℝ)) ≤ (A.card : ℝ) := by
    have h1 : ξ' * (U.ncard : ℝ) ≤ (A.card : ℝ) := hA
    linarith
  have hB' : ((ξ + Real.sqrt α) * (n : ℝ)) ≤ (B.card : ℝ) := by
    have h1 : ξ' * (U.ncard : ℝ) ≤ (B.card : ℝ) := hB
    linarith
  have hlr := hlrDel A B hdisj hA' hB'
  -- the `G'`-count
  have hG' := edgeCount_incidentTwo_ge 𝓗 hε0 hU A B hAX hBX
  have hAε : ξ' * (U.ncard : ℝ) ≤ (A.card : ℝ) := hA
  have h5 : ε * (n : ℝ) ≤ 2 * Real.sqrt ε * (A.card : ℝ) := by
    have hs' : Real.sqrt ε * Real.sqrt ε = ε := by
      simpa [pow_two] using Real.sq_sqrt hε0
    have hb : Real.sqrt ε * ξ' * (n : ℝ) ≤ 2 * Real.sqrt ε * ξ' * (U.ncard : ℝ) :=
      calc Real.sqrt ε * ξ' * (n : ℝ) ≤ Real.sqrt ε * ξ' * (2 * (U.ncard : ℝ)) :=
            mul_le_mul_of_nonneg_left hUbig (mul_nonneg (Real.sqrt_nonneg ε) hξ'0)
        _ = 2 * Real.sqrt ε * ξ' * (U.ncard : ℝ) := by ring
    have hc : 2 * Real.sqrt ε * ξ' * (U.ncard : ℝ) ≤ 2 * Real.sqrt ε * (A.card : ℝ) :=
      calc 2 * Real.sqrt ε * ξ' * (U.ncard : ℝ) =
            2 * Real.sqrt ε * (ξ' * (U.ncard : ℝ)) := by ring
        _ ≤ 2 * Real.sqrt ε * (A.card : ℝ) :=
            mul_le_mul_of_nonneg_left hAε (by positivity)
    have hd : Real.sqrt ε * Real.sqrt ε * (n : ℝ) ≤ Real.sqrt ε * ξ' * (n : ℝ) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hnumε (Real.sqrt_nonneg ε))
        (Nat.cast_nonneg n)
    calc ε * (n : ℝ) = (Real.sqrt ε * Real.sqrt ε) * (n : ℝ) := by rw [hs']
      _ ≤ Real.sqrt ε * ξ' * (n : ℝ) := hd
      _ ≤ 2 * Real.sqrt ε * ξ' * (U.ncard : ℝ) := hb
      _ ≤ 2 * Real.sqrt ε * (A.card : ℝ) := hc
  have hcount : (1 - 2 * Real.sqrt ε) * (A.card : ℝ) * (B.card : ℝ) ≤
      (edgeCount (incidentTwo 𝓗 U) A B : ℝ) := by
    have h8 : (1 - 2 * Real.sqrt ε) * (A.card : ℝ) * (B.card : ℝ) ≤
        ((A.card : ℝ) - ε * (n : ℝ)) * (B.card : ℝ) := by
      have h9 : (0 : ℝ) ≤ (B.card : ℝ) := Nat.cast_nonneg _
      nlinarith
    linarith
  -- monotonicity to `G_final[U]`
  have hmono : (edgeCount (R_abs ∩ R_final) A B : ℝ) ≤ (edgeCount (induceU R_final U) A B : ℝ) := by
    have h1 : edgeCount (R_abs ∩ R_final) A B ≤ edgeCount R_final A B :=
      edgeCount_mono_fam Set.inter_subset_right A B
    have h2 : edgeCount (induceU R_final U) A B = edgeCount R_final A B :=
      edgeCount_induce R_final U A B hAX hBX
    rw [h2]
    exact_mod_cast h1
  -- combine
  have hcomb : (ρ / 2) * (edgeCount (incidentTwo 𝓗 U) A B : ℝ) -
      (ξ + Real.sqrt α) * (A.card : ℝ) * (B.card : ℝ) ≤
      (edgeCount (induceU R_final U) A B : ℝ) := le_trans hlr hmono
  have hzz : (0 : ℝ) ≤ (A.card : ℝ) * (B.card : ℝ) :=
    mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have h1 : (ρ / 2) * ((1 - 2 * Real.sqrt ε) * (A.card : ℝ) * (B.card : ℝ)) ≤
      (ρ / 2) * (edgeCount (incidentTwo 𝓗 U) A B : ℝ) :=
    mul_le_mul_of_nonneg_left hcount (by linarith)
  have hnum' : (ρ / 3 - ξ') * ((A.card : ℝ) * (B.card : ℝ)) ≤
      ((ρ / 2) * (1 - 2 * Real.sqrt ε) - (ξ + Real.sqrt α)) *
        ((A.card : ℝ) * (B.card : ℝ)) :=
    mul_le_mul_of_nonneg_right (by linarith) hzz
  have hcomb' : ((ρ / 2) * (1 - 2 * Real.sqrt ε) - (ξ + Real.sqrt α)) *
        ((A.card : ℝ) * (B.card : ℝ)) ≤
      (edgeCount (induceU R_final U) A B : ℝ) := by
    have h2 : (ρ / 2) * ((1 - 2 * Real.sqrt ε) * (A.card : ℝ) * (B.card : ℝ)) -
        (ξ + Real.sqrt α) * (A.card : ℝ) * (B.card : ℝ) ≤
        (edgeCount (induceU R_final U) A B : ℝ) := by linarith [hcomb, h1]
    have h3 : ((ρ / 2) * (1 - 2 * Real.sqrt ε) - (ξ + Real.sqrt α)) *
        ((A.card : ℝ) * (B.card : ℝ)) =
        (ρ / 2) * ((1 - 2 * Real.sqrt ε) * (A.card : ℝ) * (B.card : ℝ)) -
          (ξ + Real.sqrt α) * (A.card : ℝ) * (B.card : ℝ) := by ring
    rw [h3]
    exact h2
  calc (ρ / 3 - ξ') * (A.card : ℝ) * (B.card : ℝ)
      = (ρ / 3 - ξ') * ((A.card : ℝ) * (B.card : ℝ)) := by ring
    _ ≤ ((ρ / 2) * (1 - 2 * Real.sqrt ε) - (ξ + Real.sqrt α)) *
        ((A.card : ℝ) * (B.card : ℝ)) := hnum'
    _ ≤ (edgeCount (induceU R_final U) A B : ℝ) := hcomb'


/-- **§12, Step 8, `stat:r_rem` (second half, conclusion).**  Passing from
`G_final[U]` (lower `(ρ/3, η)`-regular on `U`) to `G_final` (lower
`(ρ/4, ε^{1/3})`-regular) by the robustness Lemma 10.3(2)
(`selfLowerRegular_mono`), using `|V(𝓗) ∖ U| ≤ 10εn`. -/
theorem s12_lowerRegular_final {R_final : Hypergraph (Fin n)} {U : Set (Fin n)}
    {ρ η αt ε : ℝ}
    (hcard : ((Set.univ : Set (Fin n)).ncard : ℝ) ≤ (1 + αt * η) * (U.ncard : ℝ))
    (hlr : SelfLowerRegular (induceU R_final U) U (ρ / 3) η)
    (hα0 : 0 ≤ αt) (hα1 : αt < 1) (hη : 0 < η)
    (hnum1 : ρ / 4 - ε ^ (1 / 3 : ℝ) ≤ ρ / 3 * (1 - αt) ^ 2 - η / (1 - αt))
    (hnum2 : η / (1 - αt) ≤ ε ^ (1 / 3 : ℝ)) :
    SelfLowerRegular R_final Set.univ (ρ / 4) (ε ^ (1 / 3 : ℝ)) := by
  have h1 : SelfLowerRegular R_final Set.univ (ρ / 3 * (1 - αt) ^ 2) (η / (1 - αt)) :=
    selfLowerRegular_mono (induceU R_final U) R_final (X := U) (Y := Set.univ)
      (α := αt) (ρ := ρ / 3) (ξ := η)
      (fun _ _ => Set.mem_univ _) (fun _ he => he.2) (fun _ he => he.1)
      hcard hlr hα0 hα1 hη
  exact h1.mono hnum2 hnum1

end

end ErdosFaberLovaszConjecture
