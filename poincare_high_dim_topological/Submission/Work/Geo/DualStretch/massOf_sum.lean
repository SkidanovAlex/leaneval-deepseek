/-
A6 `Geo/DualStretch` — the total-mass identity for `massOf`.

`massOf σ μ τ = max 0 (card τ * (minVal τ μ - maxVal (σ \ τ) μ))` is the mass that the
barycentric-subdivision simplex indexed by the level set `τ` receives.  The lemma proved here says
that these masses add up to the total mass `∑ v ∈ s, μ v`: the subdivision of the simplex spanned by
`s` is a genuine partition of it, so the sum of the masses of the level sets is the total.

The proof is an induction on `card s` which removes a vertex `a` of maximal value.  Write
`s = insert a s'`.  Two sums are controlled simultaneously:

* `Gmass (card) s μ = ∑ v ∈ s, μ v`   (the wanted identity), and
* `Gmass 1 s μ = maxVal s μ`           (the "unit weight" companion).

A single recursion `Gmass_rec` (pure bookkeeping, the partition of `s.powerset` into the subsets
containing `a` and those not containing it) reduces both to their counterparts for `s'`: for level
sets `τ' ⊆ s'` one has `minVal τ' μ ≤ μ a ≤ maxVal (s \ τ') μ` (so the terms not containing `a`
vanish), while `insert a τ'` has the level value `minVal τ'` and the complementary level value
`maxVal (s' \ τ')`, so `card (insert a τ') = card τ' + 1` produces exactly one extra unit-weight
term — whence the companion identity is what is needed for the telescoping.
-/
import Mathlib
import Submission.Work.Geo.DualStretch.Defs

namespace Work.Geo.DualStretch

open PL (E)

variable {n : ℕ}

/-! ### API for `minVal` and `maxVal` -/

lemma minVal_image (s : Finset (E n)) (μ : E n → ℝ) (h : s.Nonempty) :
    minVal s μ = (s.image μ).min' (h.image μ) := by
  rw [minVal]; exact dite_eq_left h

lemma maxVal_image (s : Finset (E n)) (μ : E n → ℝ) (h : s.Nonempty) :
    maxVal s μ = (s.image μ).max' (h.image μ) := by
  rw [maxVal]; exact dite_eq_left h

lemma minVal_empty (μ : E n → ℝ) : minVal (∅ : Finset (E n)) μ = 0 := by
  rw [minVal]; exact dite_eq_right (Finset.not_nonempty_empty)

lemma maxVal_empty (μ : E n → ℝ) : maxVal (∅ : Finset (E n)) μ = 0 := by
  rw [maxVal]; exact dite_eq_right (Finset.not_nonempty_empty)

lemma minVal_le {s : Finset (E n)} {μ : E n → ℝ} {v : E n} (hv : v ∈ s) : minVal s μ ≤ μ v := by
  rw [minVal_image s μ ⟨v, hv⟩]
  exact Finset.min'_le _ _ (Finset.mem_image_of_mem μ hv)

lemma le_maxVal {s : Finset (E n)} {μ : E n → ℝ} {v : E n} (hv : v ∈ s) : μ v ≤ maxVal s μ := by
  rw [maxVal_image s μ ⟨v, hv⟩]
  exact Finset.le_max' _ _ (Finset.mem_image_of_mem μ hv)

lemma minVal_mem {s : Finset (E n)} {μ : E n → ℝ} (h : s.Nonempty) :
    ∃ v ∈ s, μ v = minVal s μ := by
  have hmem : (s.image μ).min' (h.image μ) ∈ s.image μ := Finset.min'_mem _ _
  obtain ⟨v, hv, hve⟩ := Finset.mem_image.mp hmem
  exact ⟨v, hv, by rw [minVal_image s μ h, hve]⟩

lemma maxVal_mem {s : Finset (E n)} {μ : E n → ℝ} (h : s.Nonempty) :
    ∃ v ∈ s, μ v = maxVal s μ := by
  have hmem : (s.image μ).max' (h.image μ) ∈ s.image μ := Finset.max'_mem _ _
  obtain ⟨v, hv, hve⟩ := Finset.mem_image.mp hmem
  exact ⟨v, hv, by rw [maxVal_image s μ h, hve]⟩

lemma maxVal_le {s : Finset (E n)} {μ : E n → ℝ} {C : ℝ} (hne : s.Nonempty)
    (h : ∀ v ∈ s, μ v ≤ C) : maxVal s μ ≤ C := by
  obtain ⟨v, hv, hv'⟩ := maxVal_mem (s := s) (μ := μ) hne
  rw [← hv']; exact h v hv

lemma minVal_le_of_le {s : Finset (E n)} {μ : E n → ℝ} {C : ℝ} (hne : s.Nonempty)
    (h : ∀ v ∈ s, C ≤ μ v) : C ≤ minVal s μ := by
  obtain ⟨v, hv, hv'⟩ := minVal_mem (s := s) (μ := μ) hne
  rw [← hv']; exact h v hv

lemma minVal_nonneg {s : Finset (E n)} {μ : E n → ℝ} (h : ∀ v ∈ s, 0 ≤ μ v) : 0 ≤ minVal s μ := by
  rcases s.eq_empty_or_nonempty with rfl | hne
  · rw [minVal_empty]
  · exact minVal_le_of_le hne h

lemma maxVal_nonneg {s : Finset (E n)} {μ : E n → ℝ} (h : ∀ v ∈ s, 0 ≤ μ v) : 0 ≤ maxVal s μ := by
  rcases s.eq_empty_or_nonempty with rfl | hne
  · rw [maxVal_empty]
  · obtain ⟨v, hv, hv'⟩ := maxVal_mem (s := s) (μ := μ) hne
    rw [← hv']; exact h v hv

lemma minVal_singleton (a : E n) (μ : E n → ℝ) : minVal {a} μ = μ a := by
  obtain ⟨v, hv, hv'⟩ := minVal_mem (s := {a}) (μ := μ) (Finset.singleton_nonempty a)
  rw [Finset.mem_singleton] at hv
  rw [← hv', hv]

lemma maxVal_singleton (a : E n) (μ : E n → ℝ) : maxVal {a} μ = μ a := by
  obtain ⟨v, hv, hv'⟩ := maxVal_mem (s := {a}) (μ := μ) (Finset.singleton_nonempty a)
  rw [Finset.mem_singleton] at hv
  rw [← hv', hv]

lemma minVal_insert_of_forall_le {a : E n} {t : Finset (E n)} {μ : E n → ℝ}
    (hne : t.Nonempty) (h : ∀ v ∈ t, μ v ≤ μ a) : minVal (insert a t) μ = minVal t μ := by
  refine le_antisymm ?_ ?_
  · obtain ⟨w, hw, hw'⟩ := minVal_mem (s := t) (μ := μ) hne
    rw [← hw']
    exact minVal_le (Finset.mem_insert_of_mem hw)
  · obtain ⟨v, hv, hv'⟩ := minVal_mem (s := insert a t) (μ := μ) (Finset.insert_nonempty a t)
    rw [← hv']
    rcases Finset.mem_insert.mp hv with rfl | hvt
    · obtain ⟨w, hw⟩ := hne
      exact (minVal_le hw).trans (h w hw)
    · exact minVal_le hvt

lemma maxVal_insert_eq_of_forall_le {a : E n} {t : Finset (E n)} {μ : E n → ℝ}
    (h : ∀ v ∈ t, μ v ≤ μ a) : maxVal (insert a t) μ = μ a := by
  refine le_antisymm ?_ (le_maxVal (Finset.mem_insert_self a t))
  exact maxVal_le (Finset.insert_nonempty a t) (fun v hv => by
    rcases Finset.mem_insert.mp hv with rfl | hvt
    · exact le_rfl
    · exact h v hvt)

/-! ### Two elementary `sdiff` identities -/

lemma sdiff_singleton_eq (a : E n) (s : Finset (E n)) (ha : a ∉ s) : insert a s \ {a} = s := by
  ext x
  by_cases hx : x = a
  · subst hx
    simp [Finset.mem_sdiff, ha]
  · simp [Finset.mem_sdiff, Finset.mem_insert, hx]

lemma sdiff_insert_eq (a : E n) (s t : Finset (E n)) (ha : a ∉ s) (ht : a ∉ t) :
    insert a s \ insert a t = s \ t := by
  ext x
  by_cases hx : x = a
  · subst hx
    simp [Finset.mem_sdiff, ha, ht]
  · simp [Finset.mem_sdiff, Finset.mem_insert, hx]

/-! ### The auxiliary weighted sum -/

/-- The total mass of the level sets of `s`, weighted by `w`. -/
noncomputable def Gmass (w : Finset (E n) → ℝ) (s : Finset (E n)) (μ : E n → ℝ) : ℝ :=
  ∑ τ ∈ s.powerset, w τ * max 0 (minVal τ μ - maxVal (s \ τ) μ)

lemma Gmass_def (w : Finset (E n) → ℝ) (s : Finset (E n)) (μ : E n → ℝ) :
    Gmass w s μ = ∑ τ ∈ s.powerset, w τ * max 0 (minVal τ μ - maxVal (s \ τ) μ) := rfl

lemma Gmass_congr {w₁ w₂ : Finset (E n) → ℝ} {s : Finset (E n)} {μ : E n → ℝ}
    (h : ∀ τ ∈ s.powerset, w₁ τ = w₂ τ) : Gmass w₁ s μ = Gmass w₂ s μ := by
  rw [Gmass_def, Gmass_def]
  exact Finset.sum_congr rfl (fun τ hτ => by rw [h τ hτ])

lemma Gmass_add (w₁ w₂ : Finset (E n) → ℝ) (s : Finset (E n)) (μ : E n → ℝ) :
    Gmass (fun τ => w₁ τ + w₂ τ) s μ = Gmass w₁ s μ + Gmass w₂ s μ := by
  rw [Gmass_def, Gmass_def, Gmass_def, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun τ _ => by rw [add_mul])

/-- The one-step recursion: removing a vertex `a` of maximal value from `s`. -/
lemma Gmass_rec {s : Finset (E n)} {μ : E n → ℝ} {a : E n} (w : Finset (E n) → ℝ)
    (ha : a ∉ s) (hamax : ∀ v ∈ s, μ v ≤ μ a) (hμa : 0 ≤ μ a) (hM : 0 ≤ maxVal s μ) :
    Gmass w (insert a s) μ = w {a} * max 0 (μ a - maxVal s μ)
      + Gmass (fun τ => w (insert a τ)) s μ := by
  conv_lhs => rw [Gmass_def]
  rw [Finset.sum_powerset_insert ha]
  have h1 : (∑ t ∈ s.powerset, w t * max 0 (minVal t μ - maxVal (insert a s \ t) μ)) = 0 := by
    refine Finset.sum_eq_zero (fun t ht => ?_)
    have hts : t ⊆ s := Finset.mem_powerset.mp ht
    have hat : a ∉ t := fun h => ha (hts h)
    have hle : minVal t μ ≤ μ a := by
      rcases t.eq_empty_or_nonempty with rfl | hne
      · rw [minVal_empty]; exact hμa
      · obtain ⟨v, hv, hv'⟩ := minVal_mem (s := t) (μ := μ) hne
        rw [← hv']; exact hamax v (hts hv)
    have hge : μ a ≤ maxVal (insert a s \ t) μ :=
      le_maxVal (Finset.mem_sdiff.mpr ⟨Finset.mem_insert_self a s, hat⟩)
    rw [max_eq_left (by linarith : minVal t μ - maxVal (insert a s \ t) μ ≤ 0), mul_zero]
  have h2 : (∑ t ∈ s.powerset,
        w (insert a t) * max 0 (minVal (insert a t) μ - maxVal (insert a s \ insert a t) μ))
      = w {a} * max 0 (μ a - maxVal s μ) + Gmass (fun τ => w (insert a τ)) s μ := by
    rw [Gmass_def]
    rw [← Finset.sum_erase_add (s.powerset)
          (fun t => w (insert a t) * max 0 (minVal t μ - maxVal (s \ t) μ))
          (Finset.empty_mem_powerset s)]
    have h0 : w (insert a ∅) * max 0 (minVal ∅ μ - maxVal (s \ ∅) μ) = 0 := by
      rw [Finset.insert_empty, minVal_empty, Finset.sdiff_empty]
      rw [max_eq_left (by linarith : (0 : ℝ) - maxVal s μ ≤ 0), mul_zero]
    rw [h0, add_zero]
    rw [← Finset.sum_erase_add (s.powerset)
          (fun t => w (insert a t) * max 0 (minVal (insert a t) μ - maxVal (insert a s \ insert a t) μ))
          (Finset.empty_mem_powerset s)]
    have hg0 : w (insert a ∅) * max 0 (minVal (insert a ∅) μ - maxVal (insert a s \ insert a ∅) μ)
        = w {a} * max 0 (μ a - maxVal s μ) := by
      rw [Finset.insert_empty, minVal_singleton, sdiff_singleton_eq a s ha]
    rw [hg0]
    have hsum : (∑ t ∈ s.powerset.erase ∅,
          w (insert a t) * max 0 (minVal (insert a t) μ - maxVal (insert a s \ insert a t) μ))
        = ∑ t ∈ s.powerset.erase ∅,
            w (insert a t) * max 0 (minVal t μ - maxVal (s \ t) μ) := by
      refine Finset.sum_congr rfl (fun t ht => ?_)
      obtain ⟨htne, htpow⟩ := Finset.mem_erase.mp ht
      have hts : t ⊆ s := Finset.mem_powerset.mp htpow
      have hne : t.Nonempty := Finset.nonempty_iff_ne_empty.mpr htne
      rw [minVal_insert_of_forall_le hne (fun v hv => hamax v (hts hv)),
          sdiff_insert_eq a s t ha (fun h => ha (hts h))]
    rw [hsum, add_comm]
  rw [h1, h2, zero_add]

lemma Gmass_card_insert (s : Finset (E n)) (μ : E n → ℝ) (a : E n) (ha : a ∉ s) :
    Gmass (fun τ => ((insert a τ).card : ℝ)) s μ
      = Gmass (fun τ => (τ.card : ℝ)) s μ + Gmass (fun _ => (1 : ℝ)) s μ := by
  rw [← Gmass_add (fun τ => (τ.card : ℝ)) (fun _ => (1 : ℝ)) s μ]
  refine Gmass_congr (fun τ hτ => ?_)
  rw [Finset.card_insert_of_notMem (fun h => ha (Finset.mem_powerset.mp hτ h))]
  push_cast
  ring

/-- The total mass of the level sets of `s` is the total mass, and the companion identity with
unit weights gives the maximal value. -/
theorem Gmass_total (m : ℕ) : ∀ (s : Finset (E n)) (μ : E n → ℝ), s.card = m →
    (∀ v ∈ s, 0 ≤ μ v) →
    (Gmass (fun τ => (τ.card : ℝ)) s μ = ∑ v ∈ s, μ v) ∧
    (Gmass (fun _ => (1 : ℝ)) s μ = maxVal s μ) := by
  induction m with
  | zero =>
    intro s μ hcard hμ
    have hs : s = ∅ := Finset.card_eq_zero.mp hcard
    subst hs
    constructor
    · rw [Gmass_def]; simp
    · rw [Gmass_def]; simp [minVal_empty, maxVal_empty]
  | succ m ih =>
    intro s μ hcard hμ
    have hne : s.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨a, ha, haval⟩ := maxVal_mem (s := s) (μ := μ) hne
    set s' := s.erase a with hs'
    have ha' : a ∉ s' := by rw [hs']; exact Finset.notMem_erase a s
    have hses : insert a s' = s := by rw [hs']; exact Finset.insert_erase ha
    have hcard' : s'.card = m := by
      have h1 : s'.card + 1 = s.card := by rw [hs']; exact Finset.card_erase_add_one ha
      omega
    have hμ' : ∀ v ∈ s', 0 ≤ μ v := by
      intro v hv
      exact hμ v (by rw [← hses]; exact Finset.mem_insert_of_mem hv)
    have hμa : 0 ≤ μ a := hμ a ha
    have hamax' : ∀ v ∈ s', μ v ≤ μ a := by
      intro v hv
      rw [haval]
      exact le_maxVal (by rw [← hses]; exact Finset.mem_insert_of_mem hv)
    obtain ⟨ihP, ihQ⟩ := ih s' μ hcard' hμ'
    have hM'le : maxVal s' μ ≤ μ a := by
      by_cases hs'e : s' = ∅
      · rw [hs'e, maxVal_empty]; exact hμa
      · exact maxVal_le (Finset.nonempty_iff_ne_empty.mpr hs'e) hamax'
    have haval' : μ a = maxVal (insert a s') μ := by rw [hses]; exact haval
    constructor
    · rw [← hses]
      rw [Gmass_rec (s := s') (a := a) (w := fun τ => (τ.card : ℝ)) ha' hamax' hμa (maxVal_nonneg hμ')]
      rw [Finset.card_singleton, Nat.cast_one, one_mul]
      rw [Gmass_card_insert s' μ a ha', ihP, ihQ]
      rw [max_eq_right (by linarith : (0 : ℝ) ≤ μ a - maxVal s' μ), Finset.sum_insert ha']
      ring
    · rw [← hses]
      rw [Gmass_rec (s := s') (a := a) (w := fun _ => (1 : ℝ)) ha' hamax' hμa (maxVal_nonneg hμ')]
      rw [one_mul, ihQ]
      rw [max_eq_right (by linarith : (0 : ℝ) ≤ μ a - maxVal s' μ), ← haval']
      ring

/-! ### The mass identity -/

/-- `massOf` as a weighted level value. -/
lemma massOf_eq (s : Finset (E n)) (μ : E n → ℝ) (τ : Finset (E n)) :
    massOf s μ τ = (τ.card : ℝ) * max 0 (minVal τ μ - maxVal (s \ τ) μ) := by
  have hc : (0 : ℝ) ≤ (τ.card : ℝ) := Nat.cast_nonneg _
  have h := mul_max_of_nonneg (a := (τ.card : ℝ)) (0 : ℝ)
    (minVal τ μ - maxVal (s \ τ) μ) hc
  rw [massOf, h, mul_zero]

theorem massOf_sum {n : ℕ} {s : Finset (PL.E n)} {μ : PL.E n → ℝ} (hμ : ∀ v ∈ s, 0 ≤ μ v) :
    ∑ τ ∈ s.powerset, Work.Geo.DualStretch.massOf s μ τ = ∑ v ∈ s, μ v := by
  have hP := (Gmass_total (n := n) s.card s μ rfl hμ).1
  rw [← hP, Gmass_def]
  exact Finset.sum_congr rfl (fun τ _ => massOf_eq s μ τ)

end Work.Geo.DualStretch
