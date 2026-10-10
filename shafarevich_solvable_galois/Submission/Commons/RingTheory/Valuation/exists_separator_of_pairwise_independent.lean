import Mathlib.RingTheory.Valuation.ValuationSubring
import Submission.Commons.RingTheory.Valuation.exists_val_lt_gt_of_independent
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.RingTheory.Valuation

/-- A valuation subring different from `⊤` has elements of value `> 1`. -/
lemma exists_valuation_gt_one {F : Type*} [Field F] (A : ValuationSubring F) (hA : A ≠ ⊤) :
    ∃ x : F, A.valuation x > 1 := by
  have hnt : A.valuation.IsNontrivial := by
    by_contra h
    exact hA ((ValuationSubring.eq_top_iff A).mpr h)
  rwa [Valuation.IsNontrivial_iff_exists_one_lt] at hnt

/-- A valuation subring different from `⊤` has a positive value `< 1`. -/
lemma exists_value_pos_lt_one {F : Type*} [Field F] (A : ValuationSubring F) (hA : A ≠ ⊤) :
    ∃ δ : A.ValueGroup, 0 < δ ∧ δ < 1 := by
  obtain ⟨x, hx⟩ := exists_valuation_gt_one A hA
  exact ⟨(A.valuation x)⁻¹, inv_pos.mpr (lt_trans zero_lt_one hx),
    inv_lt_one_of_one_lt₀ hx⟩

/-- A valuation subring different from `⊤` attains values arbitrarily large in its value group. -/
lemma exists_valuation_gt {F : Type*} [Field F] (A : ValuationSubring F) (hA : A ≠ ⊤)
    (β : A.ValueGroup) (hβ : 0 < β) : ∃ x : F, β < A.valuation x := by
  obtain ⟨u, hu⟩ := exists_valuation_gt_one A hA
  obtain ⟨x, hx⟩ := A.valuation_surjective (β * A.valuation u)
  refine ⟨x, ?_⟩
  rw [hx]
  calc β = β * 1 := (mul_one β).symm
    _ < β * A.valuation u := mul_lt_mul_of_pos_left hu hβ

/-- **Separator construction.**  For a pairwise independent family of valuation subrings `A`, a
distinguished index `k`, a finite set `s` of further indices (with `k ∉ s`), a positive value
`β` in the value group of `A k`, and positive radii `γ j` in the value groups of `A j`, there is
`x` with `(A k).valuation x > β` and `(A j).valuation x < γ j` for all `j ∈ s`.

This is the weak-approximation heart of the separator theorem.  The induction is on the finite set
`s` of "other" indices; each step multiplies the inductive solution `b` by an element `c` that is
arbitrarily large at `A k` and small at the new index.  The radii are prescribed (a priori small
enough), which is what makes the argument insensitive to the algebraic structure of the value
groups. -/
theorem separator_aux {F : Type*} [Field F] {ι : Type*} [DecidableEq ι]
    (A : ι → ValuationSubring F) (hnt : ∀ i, A i ≠ ⊤)
    (hind : ∀ i j, i ≠ j → A i ⊔ A j = ⊤) (k : ι) :
    ∀ s : Finset ι, k ∉ s → ∀ (β : (A k).ValueGroup), 0 < β →
      ∀ (γ : (j : ι) → (A j).ValueGroup), (∀ j ∈ s, 0 < γ j) →
      ∃ x : F, (A k).valuation x > β ∧ ∀ j ∈ s, (A j).valuation x < γ j := by
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro _ β hβ _ _
    obtain ⟨x, hx⟩ := exists_valuation_gt (A k) (hnt k) β hβ
    exact ⟨x, hx, fun j hj => absurd hj (Finset.notMem_empty j)⟩
  | insert j s' hj ih =>
    intro hk β hβ γ hγ
    rw [Finset.mem_insert, not_or] at hk
    obtain ⟨hkj, hks⟩ := hk
    -- a value `β'' > 1` dominating `β`
    obtain ⟨u, hu⟩ := exists_valuation_gt_one (A k) (hnt k)
    set β'' : (A k).ValueGroup := max β ((A k).valuation u) with hβ''def
    have hβ''1 : 1 < β'' := lt_of_lt_of_le hu (le_max_right _ _)
    have hβ''pos : 0 < β'' := lt_trans zero_lt_one hβ''1
    have hβ_le : β ≤ β'' := le_max_left _ _
    -- `c` is large at `k` and small at the new index `j`
    have hjk : j ≠ k := fun h => hkj h.symm
    have hsup : (A j) ⊔ (A k) = ⊤ := by rw [sup_comm]; exact hind k j hkj
    have hγj : 0 < γ j := hγ j (Finset.mem_insert_self j s')
    obtain ⟨c, hcj, hck⟩ :=
      exists_val_lt_gt_of_independent (A j) (A k) hsup (hnt j) (hnt k)
        (γ j) β'' hγj hβ''pos
    have hcpos_k : 0 < (A k).valuation c := lt_trans hβ''pos hck
    have hcne : c ≠ 0 := by
      intro h; rw [h, Valuation.map_zero] at hcpos_k; exact lt_irrefl _ hcpos_k
    -- a small positive value in every value group
    have hδ : ∀ i : ι, ∃ δ : (A i).ValueGroup, 0 < δ ∧ δ < 1 :=
      fun i => exists_value_pos_lt_one (A i) (hnt i)
    let δ : (i : ι) → (A i).ValueGroup := fun i => Classical.choose (hδ i)
    have hδspec : ∀ i, 0 < δ i ∧ δ i < 1 := fun i => Classical.choose_spec (hδ i)
    -- radii for the inductive hypothesis, tamed against `c` and against `1`
    let γ' : (i : ι) → (A i).ValueGroup := fun i =>
      if i ∈ s' then min (γ i) (min (γ i / (A i).valuation c) (δ i)) else 1
    have hγ'pos : ∀ i ∈ s', 0 < γ' i := by
      intro i hi
      rw [show γ' i = min (γ i) (min (γ i / (A i).valuation c) (δ i)) from by
        simp only [γ']; rw [if_pos hi]]
      have hci : 0 < (A i).valuation c := (Valuation.pos_iff _).mpr hcne
      exact lt_min (hγ i (Finset.mem_insert_of_mem hi))
        (lt_min (div_pos (hγ i (Finset.mem_insert_of_mem hi)) hci) (hδspec i).1)
    have hγ'i_le : ∀ i ∈ s', γ' i ≤ γ i := by
      intro i hi
      rw [show γ' i = min (γ i) (min (γ i / (A i).valuation c) (δ i)) from by
        simp only [γ']; rw [if_pos hi]]
      exact min_le_left _ _
    have hγ'i_lt : ∀ i ∈ s', γ' i < 1 := by
      intro i hi
      rw [show γ' i = min (γ i) (min (γ i / (A i).valuation c) (δ i)) from by
        simp only [γ']; rw [if_pos hi]]
      exact lt_of_le_of_lt (le_trans (min_le_right _ _) (min_le_right _ _)) (hδspec i).2
    have hγ'i_le_div : ∀ i ∈ s', γ' i ≤ γ i / (A i).valuation c := by
      intro i hi
      rw [show γ' i = min (γ i) (min (γ i / (A i).valuation c) (δ i)) from by
        simp only [γ']; rw [if_pos hi]]
      exact le_trans (min_le_right _ _) (min_le_left _ _)
    obtain ⟨b, hbk, hb⟩ := ih hks β'' hβ''pos γ' hγ'pos
    have hcjpos : 0 < (A j).valuation c := (Valuation.pos_iff _).mpr hcne
    -- key bounds
    have hbk1 : 1 < (A k).valuation b := lt_trans hβ''1 hbk
    have hck1 : 1 < (A k).valuation c := lt_trans hβ''1 hck
    -- the `k`-estimate for `c * b`
    have hcbk : β < (A k).valuation (c * b) := by
      rw [Valuation.map_mul]
      calc β ≤ β'' := hβ_le
        _ < β'' * β'' := lt_mul_of_one_lt_right hβ''pos hβ''1
        _ < (A k).valuation c * (A k).valuation b := by
            calc β'' * β'' < (A k).valuation c * β'' := mul_lt_mul_of_pos_right hck hβ''pos
              _ < (A k).valuation c * (A k).valuation b :=
                  mul_lt_mul_of_pos_left hbk (lt_trans zero_lt_one hck1)
    -- the `s'`-estimate for `c * b`
    have hcbi : ∀ i ∈ s', (A i).valuation (c * b) < γ i := by
      intro i hi
      rw [Valuation.map_mul]
      have hci : 0 < (A i).valuation c := (Valuation.pos_iff _).mpr hcne
      calc (A i).valuation c * (A i).valuation b
          < (A i).valuation c * (γ' i) := mul_lt_mul_of_pos_left (hb i hi) hci
        _ ≤ (A i).valuation c * (γ i / (A i).valuation c) :=
              mul_le_mul_of_nonneg_left (hγ'i_le_div i hi) hci.le
        _ = γ i := mul_div_cancel₀ _ (ne_of_gt hci)
    rcases lt_trichotomy ((A j).valuation b) 1 with hlt | heq | hgt
    · -- `(A j).valuation b < 1`
      refine ⟨c * b, hcbk, ?_⟩
      intro i hi
      rw [Finset.mem_insert] at hi
      rcases hi with hEq | hi'
      · rw [hEq]
        rw [Valuation.map_mul]
        calc (A j).valuation c * (A j).valuation b
            < (A j).valuation c * 1 := mul_lt_mul_of_pos_left hlt hcjpos
          _ = (A j).valuation c := mul_one _
          _ < γ j := hcj
      · exact hcbi i hi'
    · -- `(A j).valuation b = 1`
      refine ⟨c * b, hcbk, ?_⟩
      intro i hi
      rw [Finset.mem_insert] at hi
      rcases hi with hEq | hi'
      · rw [hEq, Valuation.map_mul, heq, mul_one]; exact hcj
      · exact hcbi i hi'
    · -- `(A j).valuation b > 1`
      refine ⟨c * b / (1 + b), ?_, ?_⟩
      · rw [Valuation.map_div, Valuation.map_mul,
          Valuation.map_add_eq_of_lt_right ((A k).valuation)
            (by rw [Valuation.map_one]; exact hbk1)]
        rw [mul_div_assoc, div_self (ne_of_gt (lt_trans zero_lt_one hbk1)), mul_one]
        exact lt_of_le_of_lt hβ_le hck
      · intro i hi
        rw [Finset.mem_insert] at hi
        rcases hi with hEq | hi'
        · rw [hEq, Valuation.map_div, Valuation.map_mul,
            Valuation.map_add_eq_of_lt_right ((A j).valuation)
              (by rw [Valuation.map_one]; exact hgt)]
          rw [mul_div_assoc, div_self (ne_of_gt (lt_trans zero_lt_one hgt)), mul_one]
          exact hcj
        · rw [Valuation.map_div, Valuation.map_mul]
          have hi1 : (A i).valuation (1 + b) = 1 :=
            Valuation.map_one_add_of_lt ((A i).valuation)
              (lt_of_lt_of_le (hb i hi') (hγ'i_lt i hi').le)
          rw [hi1, div_one]
          have hci : 0 < (A i).valuation c := (Valuation.pos_iff _).mpr hcne
          calc (A i).valuation c * (A i).valuation b
              < (A i).valuation c * (γ' i) := mul_lt_mul_of_pos_left (hb i hi') hci
            _ ≤ (A i).valuation c * (γ i / (A i).valuation c) :=
                  mul_le_mul_of_nonneg_left (hγ'i_le_div i hi') hci.le
            _ = γ i := mul_div_cancel₀ _ (ne_of_gt hci)

theorem exists_separator_of_pairwise_independent {F : Type*} [Field F] {ι : Type*} [Fintype ι]
    (A : ι → ValuationSubring F) (hnt : ∀ i, A i ≠ ⊤)
    (hind : ∀ i j, i ≠ j → A i ⊔ A j = ⊤) (k : ι) :
    ∃ x : F, (A k).valuation x > 1 ∧ ∀ j, j ≠ k → (A j).valuation x < 1 := by
  classical
  obtain ⟨x, hx1, hx2⟩ :=
    separator_aux A hnt hind k (Finset.univ.erase k) (Finset.notMem_erase k Finset.univ)
      1 zero_lt_one (fun _ => 1) (fun j _ => zero_lt_one)
  exact ⟨x, hx1, fun j hj => hx2 j (Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩)⟩

end Commons.RingTheory.Valuation
