import Mathlib
import Submission.Work.LinnikBurgess.frame_count_prov_defs
import Submission.Work.LinnikBurgess.frame_count_prov_aux.sum_box3_eq_iterate

namespace Work.LinnikBurgess

open scoped BigOperators

/-- The third index of `Fin 3`, i.e. the unique element different from `l1` and `l2` when
`l1 ≠ l2`.  Defined by a decision tree on the three possible values of `l1`. -/
def caseT_nth3 (l1 l2 : Fin 3) : Fin 3 :=
  if l1 = 0 then (if l2 = 1 then 2 else 1)
  else if l1 = 1 then (if l2 = 0 then 2 else 0)
  else (if l2 = 0 then 1 else 0)

lemma caseT_nth3_ne_left (l1 l2 : Fin 3) : caseT_nth3 l1 l2 ≠ l1 := by
  fin_cases l1 <;> fin_cases l2 <;> decide

lemma caseT_nth3_ne_right (l1 l2 : Fin 3) : caseT_nth3 l1 l2 ≠ l2 := by
  fin_cases l1 <;> fin_cases l2 <;> decide

lemma univ_eq_caseT_nth3 {l1 l2 : Fin 3} (h : l1 ≠ l2) :
    ({l1, l2, caseT_nth3 l1 l2} : Finset (Fin 3)) = Finset.univ := by
  ext k
  fin_cases k <;> fin_cases l1 <;> fin_cases l2 <;> simp_all [caseT_nth3]

/-- Splitting a product over `Fin 3` at the three distinct indices `l1, l2, k3`. -/
lemma prod_univ_three_split {M : Type*} [CommMonoid M] (f : Fin 3 → M)
    {l1 l2 k3 : Fin 3} (h12 : l1 ≠ l2) (h1 : k3 ≠ l1) (h2 : k3 ≠ l2)
    (huniv : ({l1, l2, k3} : Finset (Fin 3)) = Finset.univ) :
    ∏ k : Fin 3, f k = f l1 * f l2 * f k3 := by
  have h1' : l1 ≠ k3 := Ne.symm h1
  have h2' : l2 ≠ k3 := Ne.symm h2
  have key : ∏ k : Fin 3, f k = ∏ k ∈ ({l1, l2, k3} : Finset (Fin 3)), f k := by rw [huniv]
  rw [key, Finset.prod_insert, Finset.prod_insert, Finset.prod_singleton]
  · rw [mul_assoc]
  · simp only [Finset.mem_singleton]; exact h2'
  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨h12, h1'⟩

/-- **Per-slot bound of Case T.**  If two distinct slots `l1 ≠ l2` of the triple `b` are pinned to
`x1` resp. `x2` (with `x1, x2 ≠ x0`), then the corresponding part of the `b`-sum of the frame
count is at most the sum over the free slot value `γ ∈ [1,H]` of the product
`wg x0 x1 * wg x0 x2 * wg x0 γ`, restricted to `γ ≠ x0` and
`g ∣ |x0-x1| * |x0-x2| * |x0-γ|`.

Indeed, the pinned coordinates determine `b` uniquely from its free coordinate `γ = b k3`;
the divisibility `g ∣ ∏_k |x0 - b k|` becomes `g ∣ |x0-x1| |x0-x2| |x0-γ|` and the weight
`∏_k [b k ≠ x0] wg x0 (b k)` becomes `wg x0 x1 · wg x0 x2 · [γ ≠ x0] wg x0 γ`, and a coordinate
equal to `x0` contributes `0` on both sides. -/
theorem caseT_slot_le {H m g x0 x1 x2 : ℕ} (l1 l2 : Fin 3) (h12 : l1 ≠ l2)
    (hx1 : x1 ≠ x0) (hx2 : x2 ≠ x0) :
    (∑ b ∈ Work.LinnikBurgess.box3 H,
        (if b l1 = x1 ∧ b l2 = x2 ∧ g ∣ ∏ k : Fin 3, Work.LinnikBurgess.del x0 (b k)
          then ∏ k : Fin 3, (if b k ≠ x0 then Work.LinnikBurgess.wg m x0 (b k) else 0) else 0))
      ≤ ∑ γ ∈ Finset.Icc 1 H,
          (if γ ≠ x0 ∧ g ∣ Work.LinnikBurgess.del x0 x1 * Work.LinnikBurgess.del x0 x2
              * Work.LinnikBurgess.del x0 γ
            then Work.LinnikBurgess.wg m x0 x1 * Work.LinnikBurgess.wg m x0 x2
              * Work.LinnikBurgess.wg m x0 γ else 0) := by
  classical
  set k3 : Fin 3 := caseT_nth3 l1 l2 with _hk3
  have hk3l1 : k3 ≠ l1 := caseT_nth3_ne_left l1 l2
  have hk3l2 : k3 ≠ l2 := caseT_nth3_ne_right l1 l2
  have huniv : ({l1, l2, k3} : Finset (Fin 3)) = Finset.univ := univ_eq_caseT_nth3 h12
  set R : ℕ → ℝ := fun γ => (if γ ≠ x0 ∧ g ∣ del x0 x1 * del x0 x2 * del x0 γ
      then wg m x0 x1 * wg m x0 x2 * wg m x0 γ else 0) with _hR
  change (∑ b ∈ Work.LinnikBurgess.box3 H,
        (if b l1 = x1 ∧ b l2 = x2 ∧ g ∣ ∏ k : Fin 3, Work.LinnikBurgess.del x0 (b k)
          then ∏ k : Fin 3, (if b k ≠ x0 then Work.LinnikBurgess.wg m x0 (b k) else 0) else 0))
      ≤ ∑ γ ∈ Finset.Icc 1 H, R γ
  set T : Finset (Fin 3 → ℕ) := (box3 H).filter (fun b => b l1 = x1 ∧ b l2 = x2) with hT
  have hmem : ∀ b : Fin 3 → ℕ, b ∈ T ↔ b ∈ box3 H ∧ b l1 = x1 ∧ b l2 = x2 := by
    intro b
    simp only [hT, Finset.mem_filter]
  -- decomposition of the box-sum into a sum over `T`
  have hL : (∑ b ∈ box3 H,
        (if b l1 = x1 ∧ b l2 = x2 ∧ g ∣ ∏ k : Fin 3, del x0 (b k)
          then ∏ k : Fin 3, (if b k ≠ x0 then wg m x0 (b k) else 0) else 0))
      = ∑ b ∈ T, (if g ∣ ∏ k : Fin 3, del x0 (b k)
          then ∏ k : Fin 3, (if b k ≠ x0 then wg m x0 (b k) else 0) else 0) := by
    rw [hT, Finset.sum_filter]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    by_cases hp : b l1 = x1 ∧ b l2 = x2
    · by_cases hc : g ∣ ∏ k : Fin 3, del x0 (b k)
      · rw [if_pos ⟨hp.1, hp.2, hc⟩, if_pos hp, if_pos hc]
      · rw [if_neg (fun h => hc h.2.2), if_pos hp, if_neg hc]
    · rw [if_neg (fun h => hp ⟨h.1, h.2.1⟩), if_neg (fun h => hp h)]
  -- pointwise bound: each `b ∈ T` is controlled by the term at its free coordinate
  have hpt : ∀ b ∈ T, (if g ∣ ∏ k : Fin 3, del x0 (b k)
        then ∏ k : Fin 3, (if b k ≠ x0 then wg m x0 (b k) else 0) else 0) ≤ R (b k3) := by
    intro b hb
    have hb1 : b l1 = x1 := ((hmem b).mp hb).2.1
    have hb2 : b l2 = x2 := ((hmem b).mp hb).2.2
    have hP : (∏ k : Fin 3, del x0 (b k)) = del x0 x1 * del x0 x2 * del x0 (b k3) := by
      rw [prod_univ_three_split (f := fun k => del x0 (b k)) h12 hk3l1 hk3l2 huniv, hb1, hb2]
    have hQ : (∏ k : Fin 3, (if b k ≠ x0 then wg m x0 (b k) else 0))
        = wg m x0 x1 * wg m x0 x2 * (if b k3 ≠ x0 then wg m x0 (b k3) else 0) := by
      rw [prod_univ_three_split (f := fun k => (if b k ≠ x0 then wg m x0 (b k) else 0))
        h12 hk3l1 hk3l2 huniv, hb1, hb2, if_pos hx1, if_pos hx2]
    show (if g ∣ ∏ k : Fin 3, del x0 (b k)
          then ∏ k : Fin 3, (if b k ≠ x0 then wg m x0 (b k) else 0) else 0)
        ≤ (if b k3 ≠ x0 ∧ g ∣ del x0 x1 * del x0 x2 * del x0 (b k3)
            then wg m x0 x1 * wg m x0 x2 * wg m x0 (b k3) else 0)
    rw [hP, hQ]
    by_cases hc : g ∣ del x0 x1 * del x0 x2 * del x0 (b k3)
    · rw [if_pos hc]
      by_cases hk : b k3 ≠ x0
      · rw [if_pos hk, if_pos ⟨hk, hc⟩]
      · rw [if_neg hk, if_neg (fun h => hk h.1)]; simp
    · rw [if_neg hc, if_neg (fun h => hc h.2)]
  -- the free-coordinate map is injective on `T` and lands in `[1,H]`
  have hinj : Set.InjOn (fun b : Fin 3 → ℕ => b k3) ↑T := by
    intro b hb b' hb' hk
    have hb1 : b l1 = x1 := ((hmem b).mp hb).2.1
    have hb2 : b l2 = x2 := ((hmem b).mp hb).2.2
    have hb1' : b' l1 = x1 := ((hmem b').mp hb').2.1
    have hb2' : b' l2 = x2 := ((hmem b').mp hb').2.2
    funext i
    have hi : i ∈ ({l1, l2, k3} : Finset (Fin 3)) := by rw [huniv]; exact Finset.mem_univ i
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with h | h | h
    · rw [h, hb1, hb1']
    · rw [h, hb2, hb2']
    · rw [h]; exact hk
  have hsub : T.image (fun b => b k3) ⊆ Finset.Icc 1 H := by
    intro γ hγ
    rw [Finset.mem_image] at hγ
    obtain ⟨b, hb, hbk⟩ := hγ
    rw [← hbk]
    exact (Fintype.mem_piFinset.mp ((hmem b).mp hb).1) k3
  have hRnn : ∀ γ : ℕ, 0 ≤ R γ := by
    intro γ
    show 0 ≤ (if γ ≠ x0 ∧ g ∣ del x0 x1 * del x0 x2 * del x0 γ
        then wg m x0 x1 * wg m x0 x2 * wg m x0 γ else 0)
    split_ifs with h
    · exact mul_nonneg (mul_nonneg (wg_nonneg m x0 x1) (wg_nonneg m x0 x2)) (wg_nonneg m x0 γ)
    · exact le_refl 0
  calc (∑ b ∈ box3 H,
        (if b l1 = x1 ∧ b l2 = x2 ∧ g ∣ ∏ k : Fin 3, del x0 (b k)
          then ∏ k : Fin 3, (if b k ≠ x0 then wg m x0 (b k) else 0) else 0))
      = ∑ b ∈ T, (if g ∣ ∏ k : Fin 3, del x0 (b k)
          then ∏ k : Fin 3, (if b k ≠ x0 then wg m x0 (b k) else 0) else 0) := hL
    _ ≤ ∑ b ∈ T, R (b k3) := Finset.sum_le_sum hpt
    _ = ∑ γ ∈ T.image (fun b => b k3), R γ := (Finset.sum_image hinj).symm
    _ ≤ ∑ γ ∈ Finset.Icc 1 H, R γ :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun γ _ _ => hRnn γ)

end Work.LinnikBurgess
