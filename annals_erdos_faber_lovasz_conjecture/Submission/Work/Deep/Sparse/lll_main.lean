import Submission.Work.Deep.Sparse.Prelude
import Submission.Work.Deep.Sparse.ProbBasic

/-!
# The (lopsided) symmetric Lovász Local Lemma for `FinSpace`

This file proves `Work.Deep.Sparse.lll_main`: the symmetric Lovász Local Lemma in the form
used by the locally-sparse / naive-colouring argument of this directory.

* `FinSpace.prob_compl_inter` — `P(Aᶜ ∩ B) = P(B) - P(A ∩ B)`.
* `biInter_compl_mono` — a larger index set gives a smaller intersection of complements.
* `lll_aux` — the strengthened induction behind the local lemma: for disjoint `U`, `V`,
  `P(⋂_{U ∪ V} A jᶜ) ≥ (∏_{j ∈ U} (1 - x j)) · P(⋂_{V} A jᶜ)`.
* `lll_general` — the general (asymmetric) local lemma: if `x i ∈ [0,1)` and
  `P(A i) ≤ x i · ∏_{j ∈ Dep i} (1 - x j)` for every `i`, and every `A i` is independent of
  every intersection of complements of events with index outside `Dep i`, then
  `∏ i (1 - x i) ≤ P(⋂ i, A iᶜ)`.
* `witness_le` — the elementary arithmetic of the symmetric specialisation at the uniform
  witness `x = 1/(2D)`: `1/(4D) ≤ x (1 - x)^n` whenever `n ≤ D`.
* `lll_main` — the symmetric lemma with the uniform witness, in the form stated by the
  requester: `4 p |Dep i| ≤ 1` gives `P(⋂ i, A iᶜ) > 0`.
-/

set_option linter.unusedVariables false

namespace Work.Deep.Sparse

open scoped BigOperators

/-! ## Two auxiliary probability facts -/

/-- `P(Aᶜ ∩ B) = P(B) - P(A ∩ B)`. -/
theorem FinSpace.prob_compl_inter {Ω : Type*} [Fintype Ω] (P : FinSpace Ω) (A B : Set Ω) :
    P.prob (Aᶜ ∩ B) = P.prob B - P.prob (A ∩ B) := by
  have h : Aᶜ ∩ B = B \ (A ∩ B) := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_sdiff]
    tauto
  rw [h, FinSpace.prob_sdiff P Set.inter_subset_right]

/-- A larger index set gives a smaller intersection of complements. -/
theorem biInter_compl_mono {Ω ι : Type*} (A : ι → Set Ω) {S T : Finset ι}
    (h : S ⊆ T) : (⋂ j ∈ T, (A j)ᶜ) ⊆ (⋂ j ∈ S, (A j)ᶜ) := by
  intro x hx
  rw [Set.mem_iInter₂] at hx ⊢
  exact fun j hj => hx j (h hj)

/-! ## The general local lemma -/

/-- **The inductive step of the local lemma.**  For disjoint `U`, `V` of total size at most
`N`,
`P(⋂_{j ∈ U ∪ V} A jᶜ) ≥ (∏_{j ∈ U} (1 - x j)) · P(⋂_{j ∈ V} A jᶜ)`.

The induction is on `N`.  In the step one peels an index `i` from `U`: the rest of
`(U \ {i}) ∪ V` is split into the part inside `Dep i`, which is peeled by the induction
hypothesis, and the part outside `Dep i`, on which `A i` is independent of the complement
events. -/
theorem lll_aux {Ω : Type*} [Fintype Ω] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : FinSpace Ω) (A : ι → Set Ω) (Dep : ι → Finset ι) (x : ι → ℝ)
    (hx0 : ∀ i, 0 ≤ x i) (hx1 : ∀ i, x i < 1)
    (hindep : ∀ i (S : Finset ι), Disjoint S (Dep i) →
      P.prob (A i ∩ ⋂ j ∈ S, (A j)ᶜ) = P.prob (A i) * P.prob (⋂ j ∈ S, (A j)ᶜ))
    (hbound : ∀ i, P.prob (A i) ≤ x i * ∏ j ∈ Dep i, (1 - x j)) :
    ∀ (N : ℕ) (U V : Finset ι), Disjoint U V → U.card + V.card ≤ N →
      (∏ j ∈ U, (1 - x j)) * P.prob (⋂ j ∈ V, (A j)ᶜ)
        ≤ P.prob (⋂ j ∈ U ∪ V, (A j)ᶜ) := by
  intro N
  induction N with
  | zero =>
    intro U V _ hc
    have hU : U = ∅ := Finset.card_eq_zero.mp (by omega)
    have hV : V = ∅ := Finset.card_eq_zero.mp (by omega)
    subst hU; subst hV
    simp
  | succ N ih =>
    intro U V hUV hc
    rcases eq_or_ne U ∅ with hU | hU
    · subst hU
      rw [Finset.prod_empty, Finset.empty_union]
      simp
    · obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hU
      have hnotin : i ∉ U.erase i := Finset.notMem_erase i U
      have hUeq : U = insert i (U.erase i) := (Finset.insert_erase hi).symm
      have hU'card : (U.erase i).card + 1 = U.card := Finset.card_erase_add_one hi
      have hUV' : Disjoint (insert i (U.erase i)) V := by rw [← hUeq]; exact hUV
      have hU'V : Disjoint (U.erase i) V := Finset.disjoint_left.mpr fun a ha =>
        (Finset.disjoint_left.mp hUV') (Finset.mem_insert_of_mem ha)
      have hcardUV' : ((U.erase i) ∪ V).card ≤ N := by
        rw [Finset.card_union_of_disjoint hU'V]; omega
      -- the key estimate for the single event `A i`
      have hkey : P.prob (A i ∩ ⋂ j ∈ (U.erase i) ∪ V, (A j)ᶜ)
          ≤ x i * P.prob (⋂ j ∈ (U.erase i) ∪ V, (A j)ᶜ) := by
        have hind : P.prob (A i ∩ ⋂ j ∈ ((U.erase i) ∪ V) \ Dep i, (A j)ᶜ)
            = P.prob (A i) * P.prob (⋂ j ∈ ((U.erase i) ∪ V) \ Dep i, (A j)ᶜ) :=
          hindep i _ Finset.disjoint_sdiff.symm
        have hmono : P.prob (A i ∩ ⋂ j ∈ (U.erase i) ∪ V, (A j)ᶜ)
            ≤ P.prob (A i ∩ ⋂ j ∈ ((U.erase i) ∪ V) \ Dep i, (A j)ᶜ) :=
          FinSpace.prob_mono P (Set.inter_subset_inter (Set.Subset.refl _)
            (biInter_compl_mono A Finset.sdiff_subset))
        have hprod : (∏ j ∈ Dep i, (1 - x j))
            ≤ ∏ j ∈ ((U.erase i) ∪ V) ∩ Dep i, (1 - x j) :=
          Finset.prod_le_prod_of_subset_of_le_one₀ Finset.inter_subset_right
            (fun j _ => by linarith [hx1 j]) (fun j _ _ => by linarith [hx0 j])
        have hdis : Disjoint (((U.erase i) ∪ V) ∩ Dep i) (((U.erase i) ∪ V) \ Dep i) :=
          Finset.disjoint_left.mpr fun _ ha hb =>
            (Finset.mem_sdiff.mp hb).2 (Finset.mem_inter.mp ha).2
        have huni : ((U.erase i) ∪ V) ∩ Dep i ∪ ((U.erase i) ∪ V) \ Dep i
            = (U.erase i) ∪ V := by
          rw [Finset.union_comm, Finset.sdiff_union_inter]
        have hcardIH : (((U.erase i) ∪ V) ∩ Dep i).card
            + (((U.erase i) ∪ V) \ Dep i).card ≤ N := by
          have h1 : (((U.erase i) ∪ V) ∩ Dep i).card
              + (((U.erase i) ∪ V) \ Dep i).card = ((U.erase i) ∪ V).card := by
            rw [← Finset.card_union_of_disjoint hdis, huni]
          omega
        have hIHkey : (∏ j ∈ ((U.erase i) ∪ V) ∩ Dep i, (1 - x j))
              * P.prob (⋂ j ∈ ((U.erase i) ∪ V) \ Dep i, (A j)ᶜ)
            ≤ P.prob (⋂ j ∈ (U.erase i) ∪ V, (A j)ᶜ) := by
          have h := ih (((U.erase i) ∪ V) ∩ Dep i) (((U.erase i) ∪ V) \ Dep i) hdis hcardIH
          rwa [huni] at h
        calc P.prob (A i ∩ ⋂ j ∈ (U.erase i) ∪ V, (A j)ᶜ)
            ≤ P.prob (A i ∩ ⋂ j ∈ ((U.erase i) ∪ V) \ Dep i, (A j)ᶜ) := hmono
          _ = P.prob (A i) * P.prob (⋂ j ∈ ((U.erase i) ∪ V) \ Dep i, (A j)ᶜ) := hind
          _ ≤ (x i * ∏ j ∈ Dep i, (1 - x j))
                * P.prob (⋂ j ∈ ((U.erase i) ∪ V) \ Dep i, (A j)ᶜ) :=
                mul_le_mul_of_nonneg_right (hbound i) (FinSpace.prob_nonneg P _)
          _ ≤ (x i * ∏ j ∈ ((U.erase i) ∪ V) ∩ Dep i, (1 - x j))
                * P.prob (⋂ j ∈ ((U.erase i) ∪ V) \ Dep i, (A j)ᶜ) :=
                mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hprod (hx0 i))
                  (FinSpace.prob_nonneg P _)
          _ = x i * ((∏ j ∈ ((U.erase i) ∪ V) ∩ Dep i, (1 - x j))
                * P.prob (⋂ j ∈ ((U.erase i) ∪ V) \ Dep i, (A j)ᶜ)) := by ring
          _ ≤ x i * P.prob (⋂ j ∈ (U.erase i) ∪ V, (A j)ᶜ) :=
                mul_le_mul_of_nonneg_left hIHkey (hx0 i)
      have hIHmain : (∏ j ∈ U.erase i, (1 - x j)) * P.prob (⋂ j ∈ V, (A j)ᶜ)
          ≤ P.prob (⋂ j ∈ (U.erase i) ∪ V, (A j)ᶜ) :=
        ih (U.erase i) V hU'V (by omega)
      have hUVu : U ∪ V = insert i ((U.erase i) ∪ V) :=
        (congrArg (fun s => s ∪ V) hUeq).trans (Finset.insert_union i (U.erase i) V)
      have hinter : (⋂ j ∈ U ∪ V, (A j)ᶜ) = (A i)ᶜ ∩ ⋂ j ∈ (U.erase i) ∪ V, (A j)ᶜ := by
        rw [hUVu, Finset.set_biInter_insert]
      have hpc := FinSpace.prob_compl_inter P (A i) (⋂ j ∈ (U.erase i) ∪ V, (A j)ᶜ)
      have hprodU : (∏ j ∈ U, (1 - x j)) = (1 - x i) * (∏ j ∈ U.erase i, (1 - x j)) := by
        conv_lhs => rw [hUeq]
        exact Finset.prod_insert hnotin
      calc (∏ j ∈ U, (1 - x j)) * P.prob (⋂ j ∈ V, (A j)ᶜ)
          = (1 - x i) * ((∏ j ∈ U.erase i, (1 - x j)) * P.prob (⋂ j ∈ V, (A j)ᶜ)) := by
            rw [hprodU]; ring
        _ ≤ (1 - x i) * P.prob (⋂ j ∈ (U.erase i) ∪ V, (A j)ᶜ) :=
            mul_le_mul_of_nonneg_left hIHmain (by linarith [hx1 i])
        _ ≤ P.prob (⋂ j ∈ U ∪ V, (A j)ᶜ) := by
            rw [hinter, hpc]
            linarith [hkey]

/-- **The general (asymmetric) Lovász Local Lemma.**  If `x i ∈ [0,1)` and
`P(A i) ≤ x i · ∏_{j ∈ Dep i} (1 - x j)` for every `i`, and each `A i` is independent of
every intersection of complements of events whose indices avoid `Dep i`, then
`∏ i (1 - x i) ≤ P(⋂ i, A iᶜ)`. -/
theorem lll_general {Ω : Type*} [Fintype Ω] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : FinSpace Ω) (A : ι → Set Ω) (Dep : ι → Finset ι) (x : ι → ℝ)
    (hx0 : ∀ i, 0 ≤ x i) (hx1 : ∀ i, x i < 1)
    (hindep : ∀ i (S : Finset ι), Disjoint S (Dep i) →
      P.prob (A i ∩ ⋂ j ∈ S, (A j)ᶜ) = P.prob (A i) * P.prob (⋂ j ∈ S, (A j)ᶜ))
    (hbound : ∀ i, P.prob (A i) ≤ x i * ∏ j ∈ Dep i, (1 - x j)) :
    ∏ i, (1 - x i) ≤ P.prob (⋂ i, (A i)ᶜ) := by
  have h1 : (∏ j ∈ (Finset.univ : Finset ι), (1 - x j))
        * P.prob (⋂ j ∈ (∅ : Finset ι), (A j)ᶜ)
      ≤ P.prob (⋂ j ∈ (Finset.univ : Finset ι) ∪ ∅, (A j)ᶜ) :=
    lll_aux P A Dep x hx0 hx1 hindep hbound (Fintype.card ι) Finset.univ ∅
      (by rw [Finset.disjoint_iff_inter_eq_empty]; simp) (by simp)
  have h2 : P.prob (⋂ j ∈ (∅ : Finset ι), (A j)ᶜ) = 1 := by
    have hb : (⋂ j ∈ (∅ : Finset ι), (A j)ᶜ) = Set.univ := by ext x; simp
    rw [hb, FinSpace.prob_univ]
  have h3 : (⋂ j ∈ (Finset.univ : Finset ι), (A j)ᶜ) = ⋂ j, (A j)ᶜ := by ext x; simp
  rw [Finset.union_empty, h2, mul_one, h3] at h1
  exact h1

/-! ## The symmetric specialisation -/

/-- The elementary arithmetic of the symmetric local lemma at the uniform witness
`x = 1/(2D)`: if `n ≤ D` then `1/(4D) ≤ x·(1 - x)^n`. -/
theorem witness_le {D : ℝ} (hD1 : 1 ≤ D) {n : ℕ} (hn : (n : ℝ) ≤ D) :
    1 / (4 * D) ≤ (1 / (2 * D)) * (1 - 1 / (2 * D)) ^ n := by
  have hD : 0 < D := by linarith
  have hbern : 1 - (n : ℝ) * (1 / (2 * D)) ≤ (1 - 1 / (2 * D)) ^ n := by
    have hhalf : 1 / (2 * D) ≤ 2 := by
      rw [div_le_iff₀ (by linarith : (0 : ℝ) < 2 * D)]
      linarith
    have h := one_add_mul_le_pow (a := -(1 / (2 * D))) (by linarith) n
    have h1 : (1 : ℝ) + (n : ℝ) * (-(1 / (2 * D)))
        = 1 - (n : ℝ) * (1 / (2 * D)) := by ring
    have h2 : (1 : ℝ) + -(1 / (2 * D)) = 1 - 1 / (2 * D) := by ring
    calc (1 : ℝ) - (n : ℝ) * (1 / (2 * D))
        = 1 + (n : ℝ) * (-(1 / (2 * D))) := h1.symm
      _ ≤ (1 + -(1 / (2 * D))) ^ n := h
      _ = (1 - 1 / (2 * D)) ^ n := by rw [h2]
  refine le_trans ?_ (mul_le_mul_of_nonneg_left hbern (by positivity))
  have h4D : (0 : ℝ) < 4 * D := by linarith
  rw [div_le_iff₀ h4D]
  have hDne : (2 : ℝ) * D ≠ 0 := ne_of_gt (by linarith : (0 : ℝ) < 2 * D)
  field_simp
  nlinarith [hn, hD]

/-- **Symmetric Lovász Local Lemma.**  Let `A i` be events of a finite probability space, each
of probability at most `p`, and let `Dep i ∋ i` be a dependency set for `A i`: `A i` is
independent of every intersection of complements of events with indices outside `Dep i`.
If `4 p |Dep i| ≤ 1` for every `i`, then with positive probability none of the events occur.

This is the form of the local lemma used by the naive colouring procedure: for the colouring
events of a vertex `v`, `Dep v` consists of `v` together with the events of its neighbours, and
`4 p (deg v + 1) ≤ 1` is the smallness condition of the sparse-graph case. -/
theorem lll_main {Ω : Type*} [Fintype Ω] (P : Work.Deep.Sparse.FinSpace Ω)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (A : ι → Set Ω) (Dep : ι → Finset ι) (p : ℝ)
    (hself : ∀ i, i ∈ Dep i) (hp0 : 0 ≤ p) (hprob : ∀ i, P.prob (A i) ≤ p)
    (hindep : ∀ i (T : Finset ι), Disjoint T (Dep i) →
      P.prob (A i ∩ ⋂ j ∈ T, (A j)ᶜ) = P.prob (A i) * P.prob (⋂ j ∈ T, (A j)ᶜ))
    (hsmall : ∀ i, 4 * p * ((Dep i).card : ℝ) ≤ 1) :
    0 < P.prob (⋂ i, (A i)ᶜ) := by
  classical
  by_cases hι : Nonempty ι
  · -- choose an index whose dependency set is maximal; the uniform witness is `1/(2D)`
    obtain ⟨i₀, -, hi₀⟩ := Finset.exists_max_image (Finset.univ : Finset ι)
      (fun i => (Dep i).card) ⟨hι.some, Finset.mem_univ _⟩
    have hD1 : 1 ≤ (Dep i₀).card := Finset.card_pos.mpr ⟨i₀, hself i₀⟩
    have hDr : (0 : ℝ) < ((Dep i₀).card : ℝ) := by exact_mod_cast hD1
    have hx0 : 0 ≤ 1 / (2 * ((Dep i₀).card : ℝ)) := by positivity
    have hD1R : (1 : ℝ) ≤ ((Dep i₀).card : ℝ) := by exact_mod_cast hD1
    have hx1 : 1 / (2 * ((Dep i₀).card : ℝ)) < 1 := by
      rw [div_lt_one (by linarith)]
      linarith
    have hbound : ∀ i, P.prob (A i)
        ≤ (1 / (2 * ((Dep i₀).card : ℝ)))
            * ∏ j ∈ Dep i, (1 - 1 / (2 * ((Dep i₀).card : ℝ))) := by
      intro i
      have hDi : ((Dep i).card : ℝ) ≤ ((Dep i₀).card : ℝ) := by
        exact_mod_cast hi₀ i (Finset.mem_univ i)
      have hpD : p ≤ 1 / (4 * ((Dep i₀).card : ℝ)) := by
        have h4 : 4 * p * ((Dep i₀).card : ℝ) ≤ 1 := hsmall i₀
        rw [le_div_iff₀ (by positivity)]
        linarith
      calc P.prob (A i) ≤ p := hprob i
        _ ≤ 1 / (4 * ((Dep i₀).card : ℝ)) := hpD
        _ ≤ (1 / (2 * ((Dep i₀).card : ℝ)))
              * (1 - 1 / (2 * ((Dep i₀).card : ℝ))) ^ ((Dep i).card) :=
            witness_le hD1R hDi
        _ = (1 / (2 * ((Dep i₀).card : ℝ)))
              * ∏ j ∈ Dep i, (1 - 1 / (2 * ((Dep i₀).card : ℝ))) := by
            rw [Finset.prod_const]
    have hgen := lll_general P A Dep (fun _ => 1 / (2 * ((Dep i₀).card : ℝ)))
      (fun _ => hx0) (fun _ => hx1) hindep hbound
    have hpos : 0 < ∏ _i : ι, (1 - 1 / (2 * ((Dep i₀).card : ℝ))) :=
      Finset.prod_pos fun _ _ => by linarith
    exact lt_of_lt_of_le hpos hgen
  · -- `ι` is empty: the intersection is the whole space
    have hset : (⋂ i, (A i)ᶜ) = (Set.univ : Set Ω) := by
      refine Set.eq_univ_of_forall fun x => ?_
      simp only [Set.mem_iInter, Set.mem_compl_iff]
      intro i
      exact (hι ⟨i⟩).elim
    rw [hset, FinSpace.prob_univ]
    norm_num

end Work.Deep.Sparse
