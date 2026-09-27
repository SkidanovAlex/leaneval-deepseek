/-
`Work.Geo.DualStretch.massOf_combination`

The layer-cake ("coarea") identity behind the barycentric-subdivision splitting of a point:
for a finite vertex set `s` and nonnegative weights `μ` on `s`,

  `∑_{τ ⊆ s} massOf s μ τ • bary τ = ∑_{v ∈ s} μ v • v`.

The proof goes through the auxiliary real-valued weight

  `dOf s μ τ = max 0 (minVal τ μ - maxVal (s \ τ) μ)`

for which `massOf s μ τ • bary τ = dOf s μ τ • (∑ v ∈ τ, v)`.  Both the identity above and
the companion "total mass" identity `∑_{τ ⊆ s} dOf s μ τ = maxVal s μ` are proved by a single
induction over the maximiser of `μ` (peeling the vertex of largest value).

The remaining term `τ = ∅` contributes nothing, and every subset `τ ⊆ s` which is not an
initial segment of the descending order of `μ` on `s` has `dOf s μ τ = 0`.
-/
import Mathlib
import Submission.Work.Geo.DualStretch.Defs

open Set Metric
open scoped Classical

namespace Work.Geo.DualStretch

open PL (E Cx)

variable {n : ℕ}

/-! ## API for `minVal` and `maxVal` -/

private lemma minVal_empty {μ : E n → ℝ} : minVal (∅ : Finset (E n)) μ = 0 := by
  simp [minVal]

private lemma maxVal_empty {μ : E n → ℝ} : maxVal (∅ : Finset (E n)) μ = 0 := by
  simp [maxVal]

private lemma minVal_of_nonempty {s : Finset (E n)} {μ : E n → ℝ} (h : s.Nonempty) :
    minVal s μ = (s.image μ).min' (h.image μ) := dite_eq_left h

private lemma maxVal_of_nonempty {s : Finset (E n)} {μ : E n → ℝ} (h : s.Nonempty) :
    maxVal s μ = (s.image μ).max' (h.image μ) := dite_eq_left h

private lemma minVal_le {s : Finset (E n)} {μ : E n → ℝ} {v : E n} (hv : v ∈ s) :
    minVal s μ ≤ μ v := by
  have hne : s.Nonempty := ⟨v, hv⟩
  rw [minVal_of_nonempty hne]
  exact Finset.min'_le (s.image μ) (μ v) (Finset.mem_image_of_mem μ hv)

private lemma le_maxVal {s : Finset (E n)} {μ : E n → ℝ} {v : E n} (hv : v ∈ s) :
    μ v ≤ maxVal s μ := by
  have hne : s.Nonempty := ⟨v, hv⟩
  rw [maxVal_of_nonempty hne]
  exact Finset.le_max' (s.image μ) (μ v) (Finset.mem_image_of_mem μ hv)

private lemma le_minVal {s : Finset (E n)} {μ : E n → ℝ} {c : ℝ} (hne : s.Nonempty)
    (h : ∀ v ∈ s, c ≤ μ v) : c ≤ minVal s μ := by
  rw [minVal_of_nonempty hne]
  exact Finset.le_min' (s.image μ) (hne.image μ) c (fun x hx => by
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
    exact h v hv)

private lemma maxVal_le {s : Finset (E n)} {μ : E n → ℝ} {c : ℝ}
    (h : ∀ v ∈ s, μ v ≤ c) (h0 : 0 ≤ c) : maxVal s μ ≤ c := by
  by_cases hne : s.Nonempty
  · rw [maxVal_of_nonempty hne]
    exact Finset.max'_le (s.image μ) (hne.image μ) c (fun x hx => by
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
      exact h v hv)
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne, maxVal_empty]
    exact h0

private lemma minVal_le_of_forall_le {s : Finset (E n)} {μ : E n → ℝ} {c : ℝ}
    (h : ∀ v ∈ s, μ v ≤ c) (h0 : 0 ≤ c) : minVal s μ ≤ c := by
  by_cases hne : s.Nonempty
  · obtain ⟨v, hv⟩ := hne
    exact le_trans (minVal_le hv) (h v hv)
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne, minVal_empty]
    exact h0

private lemma zero_le_maxVal {s : Finset (E n)} {μ : E n → ℝ} (hμ : ∀ v ∈ s, 0 ≤ μ v) :
    0 ≤ maxVal s μ := by
  by_cases hne : s.Nonempty
  · obtain ⟨v, hv⟩ := hne
    exact le_trans (hμ v hv) (le_maxVal hv)
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne, maxVal_empty]

private lemma minVal_singleton {μ : E n → ℝ} (w : E n) :
    minVal ({w} : Finset (E n)) μ = μ w := by
  apply le_antisymm
  · exact minVal_le (Finset.mem_singleton_self w)
  · refine le_minVal (Finset.singleton_nonempty w) ?_
    intro v hv
    rw [Finset.mem_singleton] at hv
    subst hv; exact le_refl _

private lemma minVal_insert {μ : E n → ℝ} {w : E n} {τ : Finset (E n)} (hne : τ.Nonempty) :
    minVal (insert w τ) μ = min (μ w) (minVal τ μ) := by
  apply le_antisymm
  · rw [le_min_iff]
    constructor
    · exact minVal_le (Finset.mem_insert_self w τ)
    · exact le_minVal hne (fun v hv => minVal_le (Finset.mem_insert_of_mem hv))
  · refine le_minVal (Finset.insert_nonempty w τ) ?_
    intro v hv
    rw [Finset.mem_insert] at hv
    rcases hv with rfl | hv
    · exact min_le_left _ _
    · exact le_trans (min_le_right _ _) (minVal_le hv)

/-! ## The auxiliary layer-cake weight -/

private noncomputable def dOf (s : Finset (E n)) (μ : E n → ℝ) (τ : Finset (E n)) : ℝ :=
  max 0 (minVal τ μ - maxVal (s \ τ) μ)

private lemma massOf_smul_bary_eq_dOf (s : Finset (E n)) (μ : E n → ℝ) (τ : Finset (E n)) :
    massOf s μ τ • bary τ = dOf s μ τ • (∑ v ∈ τ, v) := by
  by_cases hcard : τ.card = 0
  · rw [Finset.card_eq_zero.mp hcard]
    simp [massOf, bary, dOf]
  · have hc : massOf s μ τ = (τ.card : ℝ) * dOf s μ τ := by
      unfold massOf dOf
      have h := mul_max_of_nonneg (0 : ℝ) (minVal τ μ - maxVal (s \ τ) μ) (Nat.cast_nonneg τ.card)
      simp only [mul_zero] at h
      exact h.symm
    rw [hc, bary, smul_smul]
    have hcne : (τ.card : ℝ) ≠ 0 := by exact_mod_cast hcard
    have hscalar : (τ.card : ℝ) * dOf s μ τ * (τ.card : ℝ)⁻¹ = dOf s μ τ := by
      rw [mul_assoc, mul_comm (dOf s μ τ), ← mul_assoc, mul_inv_cancel₀ hcne, one_mul]
    rw [hscalar]

/-! ## The induction -/

private theorem aux_and_main (μ : E n → ℝ) :
    ∀ s : Finset (E n), (∀ v ∈ s, 0 ≤ μ v) →
      ((∑ τ ∈ s.powerset, dOf s μ τ = maxVal s μ) ∧
       (∑ τ ∈ s.powerset, dOf s μ τ • (∑ v ∈ τ, v) = ∑ v ∈ s, μ v • v)) := by
  intro s
  refine Finset.induction_on_max_value (f := μ)
    (motive := fun u => (∀ v ∈ u, 0 ≤ μ v) →
      ((∑ τ ∈ u.powerset, dOf u μ τ = maxVal u μ) ∧
       (∑ τ ∈ u.powerset, dOf u μ τ • (∑ v ∈ τ, v) = ∑ v ∈ u, μ v • v))) s ?_ ?_
  · intro _
    constructor
    · rw [Finset.powerset_empty, Finset.sum_singleton]
      simp [dOf, minVal, maxVal]
    · rw [Finset.powerset_empty, Finset.sum_singleton]
      simp [dOf, minVal, maxVal]
  · intro a s ha hle ih hμ
    have hμs : ∀ v ∈ s, 0 ≤ μ v := fun v hv => hμ v (Finset.mem_insert_of_mem hv)
    have hwa : 0 ≤ μ a := hμ a (Finset.mem_insert_self a s)
    obtain ⟨ihAux, ihMain⟩ := ih hμs
    -- every subset of the small set has vanishing weight
    have hd0 : ∀ τ ∈ s.powerset, dOf (insert a s) μ τ = 0 := by
      intro τ hτ
      rw [Finset.mem_powerset] at hτ
      have ha_notin : a ∉ τ := fun h => ha (hτ h)
      have h1 : minVal τ μ ≤ μ a := minVal_le_of_forall_le (fun v hv => hle v (hτ hv)) hwa
      have h2 : μ a ≤ maxVal ((insert a s) \ τ) μ :=
        le_maxVal (Finset.mem_sdiff.mpr ⟨Finset.mem_insert_self a s, ha_notin⟩)
      unfold dOf
      exact max_eq_left (by linarith)
    -- adding the maximal vertex to a nonempty subset does not change the weight
    have hd1 : ∀ τ ∈ s.powerset, τ ≠ ∅ → dOf (insert a s) μ (insert a τ) = dOf s μ τ := by
      intro τ hτ hne
      rw [Finset.mem_powerset] at hτ
      have hτne : τ.Nonempty := Finset.nonempty_iff_ne_empty.mpr hne
      have hmv : minVal (insert a τ) μ = minVal τ μ := by
        rw [minVal_insert hτne]
        exact min_eq_right (minVal_le_of_forall_le (fun v hv => hle v (hτ hv)) hwa)
      have hmx : (insert a s) \ insert a τ = s \ τ := by
        ext x
        simp only [Finset.mem_sdiff, Finset.mem_insert, not_or]
        constructor
        · rintro ⟨hxs, hxna, hxτ⟩
          rcases hxs with h | h
          · exact absurd h hxna
          · exact ⟨h, hxτ⟩
        · rintro ⟨hxs, hxτ⟩
          exact ⟨Or.inr hxs, fun h => ha (h ▸ hxs), hxτ⟩
      unfold dOf
      rw [hmv, hmx]
    -- the singleton of the maximal vertex
    have hd2 : dOf (insert a s) μ {a} = μ a - maxVal s μ := by
      unfold dOf
      have hsd : (insert a s) \ ({a} : Finset (E n)) = s := by
        rw [Finset.sdiff_singleton_eq_erase, Finset.erase_insert ha]
      rw [minVal_singleton, hsd]
      exact max_eq_right (sub_nonneg.mpr (maxVal_le hle hwa))
    -- the empty set
    have hd3 : dOf s μ (∅ : Finset (E n)) = 0 := by
      unfold dOf
      rw [minVal_empty, Finset.sdiff_empty]
      exact max_eq_left (by linarith [zero_le_maxVal hμs])
    have hmem0 : (∅ : Finset (E n)) ∈ s.powerset :=
      Finset.mem_powerset.mpr (Finset.empty_subset s)
    have hdisj : Disjoint s.powerset (s.powerset.image (insert a)) := by
      rw [Finset.disjoint_left]
      intro x hx hxim
      obtain ⟨y, hy, hyx⟩ := Finset.mem_image.mp hxim
      rw [Finset.mem_powerset] at hx
      exact ha (hx (hyx ▸ Finset.mem_insert_self a y))
    have hinj : Set.InjOn (insert a) (↑s.powerset : Set (Finset (E n))) := by
      intro x hx y hy hxy
      rw [Finset.mem_coe, Finset.mem_powerset] at hx hy
      have hxw : a ∉ x := fun h => ha (hx h)
      have hyw : a ∉ y := fun h => ha (hy h)
      calc x = (insert a x).erase a := (Finset.erase_insert hxw).symm
           _ = (insert a y).erase a := by rw [hxy]
           _ = y := Finset.erase_insert hyw
    have hpow : (insert a s).powerset = s.powerset ∪ s.powerset.image (insert a) :=
      Finset.powerset_insert s a
    have hsums : ∑ x ∈ s.powerset.erase ∅, dOf s μ x = maxVal s μ := by
      have h2 := Finset.sum_erase_add s.powerset (fun τ => dOf s μ τ) hmem0
      rw [hd3, add_zero, ihAux] at h2
      exact h2
    have hsumv : ∑ x ∈ s.powerset.erase ∅, dOf s μ x • (∑ v ∈ x, v) = ∑ v ∈ s, μ v • v := by
      have h2 := Finset.sum_erase_add s.powerset (fun τ => dOf s μ τ • (∑ v ∈ τ, v)) hmem0
      rw [Finset.sum_empty, smul_zero, add_zero, ihMain] at h2
      exact h2
    constructor
    · have hmax : maxVal (insert a s) μ = μ a := by
        refine le_antisymm ?_ (le_maxVal (Finset.mem_insert_self a s))
        refine maxVal_le ?_ hwa
        intro v hv
        rw [Finset.mem_insert] at hv
        rcases hv with rfl | hv
        · exact le_refl _
        · exact hle v hv
      rw [hmax, hpow, Finset.sum_union hdisj, Finset.sum_eq_zero hd0, zero_add,
          Finset.sum_image hinj, ← Finset.sum_erase_add s.powerset
            (fun τ => dOf (insert a s) μ (insert a τ)) hmem0]
      have hcong : ∑ x ∈ s.powerset.erase ∅, dOf (insert a s) μ (insert a x)
          = ∑ x ∈ s.powerset.erase ∅, dOf s μ x := by
        refine Finset.sum_congr rfl ?_
        intro x hx
        rw [Finset.mem_erase] at hx
        exact hd1 x hx.2 hx.1
      rw [hcong, hsums, Finset.insert_empty, hd2]
      ring
    · rw [hpow, Finset.sum_union hdisj,
          Finset.sum_eq_zero (fun τ hτ => by rw [hd0 τ hτ, zero_smul]), zero_add,
          Finset.sum_image hinj, ← Finset.sum_erase_add s.powerset
            (fun τ => dOf (insert a s) μ (insert a τ) • (∑ v ∈ insert a τ, v)) hmem0]
      have hcong : ∑ x ∈ s.powerset.erase ∅,
            dOf (insert a s) μ (insert a x) • (∑ v ∈ insert a x, v)
          = ∑ x ∈ s.powerset.erase ∅, dOf s μ x • (a + ∑ v ∈ x, v) := by
        refine Finset.sum_congr rfl ?_
        intro x hx
        rw [Finset.mem_erase] at hx
        have hxsub : x ⊆ s := Finset.mem_powerset.mp hx.2
        have hax : a ∉ x := fun h => ha (hxsub h)
        rw [hd1 x hx.2 hx.1, Finset.sum_insert hax]
      rw [hcong]
      have hdecomp : ∑ x ∈ s.powerset.erase ∅, dOf s μ x • (a + ∑ v ∈ x, v)
          = (∑ x ∈ s.powerset.erase ∅, dOf s μ x) • a
            + ∑ x ∈ s.powerset.erase ∅, dOf s μ x • (∑ v ∈ x, v) := by
        have h1 : ∑ x ∈ s.powerset.erase ∅, dOf s μ x • (a + ∑ v ∈ x, v)
            = ∑ x ∈ s.powerset.erase ∅, (dOf s μ x • a + dOf s μ x • (∑ v ∈ x, v)) :=
          Finset.sum_congr rfl (fun x _ => smul_add (dOf s μ x) a (∑ v ∈ x, v))
        rw [h1, Finset.sum_add_distrib, ← Finset.sum_smul]
      rw [hdecomp, hsums, hsumv]
      have hg0 : dOf (insert a s) μ (insert a ∅) • (∑ v ∈ insert a ∅, v)
          = (μ a - maxVal s μ) • a := by
        rw [Finset.insert_empty, Finset.sum_singleton, hd2]
      rw [hg0, Finset.sum_insert ha, sub_smul]
      abel

/-! ## The target -/

theorem massOf_combination {n : ℕ} {s : Finset (PL.E n)} {μ : PL.E n → ℝ} (hμ : ∀ v ∈ s, 0 ≤ μ v) :
    ∑ τ ∈ s.powerset, Work.Geo.DualStretch.massOf s μ τ • Work.Geo.DualStretch.bary τ =
      ∑ v ∈ s, μ v • v := by
  have h := (aux_and_main μ s hμ).2
  rw [← h]
  exact Finset.sum_congr rfl (fun τ _ => massOf_smul_bary_eq_dOf s μ τ)

end Work.Geo.DualStretch
