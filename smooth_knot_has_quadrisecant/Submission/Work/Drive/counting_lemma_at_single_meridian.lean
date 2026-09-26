import Mathlib
import Submission.Work.Drive.strip_crosscut_tools

namespace Work.Drive

/-- **Counting lemma at a single meridian.**

Let `K ⊆ ℝ²` be invariant under the shift `(x,y) ↦ (x+p,y)` (`p > 0`) and suppose that the
vertical line `x = 0` meets `K` in finitely many points.  Then any preconnected set `C ⊆ K` which
avoids all its translates by positive multiples of `(p,0)` has bounded `x`-coordinates.

The argument is elementary.  `S = fst '' C` is preconnected in `ℝ`, hence an interval; if it were
unbounded above it would contain a ray `[a,∞)`, and for every large natural `k` there would be a point
`(k p, y_k) ∈ C`.  These points are pairwise distinct (a coincidence would put two points of `C`
on a common positive `p`-translate) and each of them, shifted back by `k p` in the `x`-direction,
lands on the finite set `K ∩ {x = 0}`, a contradiction.  The unbounded-below case is the mirror
image. -/
theorem counting_lemma_at_single_meridian {p : ℝ} (hp : 0 < p) {K : Set (ℝ × ℝ)}
    (hper : ∀ q : ℝ × ℝ, q ∈ K ↔ (q.1 + p, q.2) ∈ K)
    (hfin : (K ∩ {q : ℝ × ℝ | q.1 = 0}).Finite)
    {C : Set (ℝ × ℝ)} (hCsub : C ⊆ K) (hCpc : IsPreconnected C)
    (hdisj : ∀ m : ℕ, 0 < m →
      (C ∩ (fun q : ℝ × ℝ => (q.1 + (m : ℝ) * p, q.2)) '' C) = ∅) :
    Bornology.IsBounded (Prod.fst '' C) := by
  -- ## 1. Invariance of `K` under integral shifts in the `x`-direction.
  have hKadd : ∀ (n : ℕ) (q : ℝ × ℝ), q ∈ K → (q.1 + (n : ℝ) * p, q.2) ∈ K := by
    intro n
    induction n with
    | zero => intro q hq; simpa using hq
    | succ n ih =>
      intro q hq
      have h1 : (q.1 + (n : ℝ) * p, q.2) ∈ K := ih q hq
      have h2 := (hper (q.1 + (n : ℝ) * p, q.2)).mp h1
      simpa [Nat.cast_succ, add_mul, one_mul, add_assoc] using h2
  have hKsub : ∀ (n : ℕ) (q : ℝ × ℝ), q ∈ K → (q.1 - (n : ℝ) * p, q.2) ∈ K := by
    have hstep : ∀ q : ℝ × ℝ, q ∈ K → (q.1 - p, q.2) ∈ K := by
      intro q hq
      refine (hper (q.1 - p, q.2)).mpr ?_
      simpa using hq
    intro n
    induction n with
    | zero => intro q hq; simpa using hq
    | succ n ih =>
      intro q hq
      have h1 : (q.1 - (n : ℝ) * p, q.2) ∈ K := ih q hq
      have h2 := hstep (q.1 - (n : ℝ) * p, q.2) h1
      have hgoal : q.1 - ((n + 1 : ℕ) : ℝ) * p = q.1 - (n : ℝ) * p - p := by
        push_cast; ring
      rw [hgoal]
      exact h2
  -- ## 2. `Prod.fst '' C` is preconnected.
  have hSpre : IsPreconnected (Prod.fst '' C) :=
    hCpc.image Prod.fst continuous_fst.continuousOn
  -- ## 3. There is no ray of `x`-values above (resp. below) the set.
  have key_above : ∀ a : ℝ, (∀ t : ℝ, a ≤ t → ∃ y : ℝ, (t, y) ∈ C) → False := by
    intro a hray
    obtain ⟨k0, hk0⟩ := exists_nat_ge (a / p)
    have hk0p : a ≤ (k0 : ℝ) * p := by
      rw [div_le_iff₀ hp] at hk0
      exact hk0
    have ht_ge : ∀ k : ℕ, a ≤ ((k0 + k : ℕ) : ℝ) * p := by
      intro k
      have hle : (k0 : ℝ) * p ≤ ((k0 + k : ℕ) : ℝ) * p := by
        apply mul_le_mul_of_nonneg_right _ (le_of_lt hp)
        push_cast
        exact le_add_of_nonneg_right (Nat.cast_nonneg k)
      linarith
    choose y hy using fun k : ℕ => hray (((k0 + k : ℕ) : ℝ) * p) (ht_ge k)
    have hrK : ∀ k : ℕ, ((0 : ℝ), y k) ∈ K := by
      intro k
      have h1 : (((↑(k0 + k) : ℝ) * p - (↑(k0 + k) : ℝ) * p), y k) ∈ K :=
        hKsub (k0 + k) _ (hCsub (hy k))
      simpa using h1
    have hyinj : Function.Injective y := by
      intro k j hyj
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hlt
      · have hd : 0 < j - k := Nat.sub_pos_of_lt hlt
        have hmem : (((↑(k0 + j) : ℝ) * p), y j) ∈
            C ∩ (fun q : ℝ × ℝ => (q.1 + ((j - k : ℕ) : ℝ) * p, q.2)) '' C := by
          refine ⟨hy j, ?_⟩
          refine ⟨(((↑(k0 + k) : ℝ) * p), y k), hy k, ?_⟩
          ext
          · rw [Nat.cast_sub (le_of_lt hlt)]; push_cast; ring_nf
          · simp [hyj]
        rw [hdisj (j - k) hd] at hmem
        exact hmem
      · have hd : 0 < k - j := Nat.sub_pos_of_lt hlt
        have hmem : (((↑(k0 + k) : ℝ) * p), y k) ∈
            C ∩ (fun q : ℝ × ℝ => (q.1 + ((k - j : ℕ) : ℝ) * p, q.2)) '' C := by
          refine ⟨hy k, ?_⟩
          refine ⟨(((↑(k0 + j) : ℝ) * p), y j), hy j, ?_⟩
          ext
          · rw [Nat.cast_sub (le_of_lt hlt)]; push_cast; ring_nf
          · simp [hyj]
        rw [hdisj (k - j) hd] at hmem
        exact hmem
    have hinj : Function.Injective (fun k : ℕ => ((0 : ℝ), y k)) := by
      intro k j h
      exact hyinj (Prod.ext_iff.mp h).2
    have hrange : Set.range (fun k : ℕ => ((0 : ℝ), y k)) ⊆ K ∩ {q : ℝ × ℝ | q.1 = 0} := by
      rintro _ ⟨k, rfl⟩
      exact ⟨hrK k, rfl⟩
    exact (hfin.subset hrange).not_infinite (Set.infinite_range_of_injective hinj)
  have key_below : ∀ a : ℝ, (∀ t : ℝ, t ≤ a → ∃ y : ℝ, (t, y) ∈ C) → False := by
    intro a hray
    obtain ⟨k0, hk0⟩ := exists_nat_ge (-a / p)
    have hk0p : -a ≤ (k0 : ℝ) * p := by
      rw [div_le_iff₀ hp] at hk0
      exact hk0
    have ht_le : ∀ k : ℕ, -(((k0 + k : ℕ) : ℝ) * p) ≤ a := by
      intro k
      have hle : (k0 : ℝ) * p ≤ ((k0 + k : ℕ) : ℝ) * p := by
        apply mul_le_mul_of_nonneg_right _ (le_of_lt hp)
        push_cast
        exact le_add_of_nonneg_right (Nat.cast_nonneg k)
      linarith
    choose y hy using fun k : ℕ => hray (-(((k0 + k : ℕ) : ℝ) * p)) (ht_le k)
    have hrK : ∀ k : ℕ, ((0 : ℝ), y k) ∈ K := by
      intro k
      have h1 : ((-(((k0 + k : ℕ) : ℝ) * p) + ((k0 + k : ℕ) : ℝ) * p), y k) ∈ K :=
        hKadd (k0 + k) _ (hCsub (hy k))
      simpa using h1
    have hyinj : Function.Injective y := by
      intro k j hyj
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hlt
      · have hd : 0 < j - k := Nat.sub_pos_of_lt hlt
        have hmem : ((-(((k0 + k : ℕ) : ℝ) * p)), y k) ∈
            C ∩ (fun q : ℝ × ℝ => (q.1 + ((j - k : ℕ) : ℝ) * p, q.2)) '' C := by
          refine ⟨hy k, ?_⟩
          refine ⟨((-(((k0 + j : ℕ) : ℝ) * p)), y j), hy j, ?_⟩
          ext
          · rw [Nat.cast_sub (le_of_lt hlt)]; push_cast; ring_nf
          · simp [hyj]
        rw [hdisj (j - k) hd] at hmem
        exact hmem
      · have hd : 0 < k - j := Nat.sub_pos_of_lt hlt
        have hmem : ((-(((k0 + j : ℕ) : ℝ) * p)), y j) ∈
            C ∩ (fun q : ℝ × ℝ => (q.1 + ((k - j : ℕ) : ℝ) * p, q.2)) '' C := by
          refine ⟨hy j, ?_⟩
          refine ⟨((-(((k0 + k : ℕ) : ℝ) * p)), y k), hy k, ?_⟩
          ext
          · rw [Nat.cast_sub (le_of_lt hlt)]; push_cast; ring_nf
          · simp [hyj]
        rw [hdisj (k - j) hd] at hmem
        exact hmem
    have hinj : Function.Injective (fun k : ℕ => ((0 : ℝ), y k)) := by
      intro k j h
      exact hyinj (Prod.ext_iff.mp h).2
    have hrange : Set.range (fun k : ℕ => ((0 : ℝ), y k)) ⊆ K ∩ {q : ℝ × ℝ | q.1 = 0} := by
      rintro _ ⟨k, rfl⟩
      exact ⟨hrK k, rfl⟩
    exact (hfin.subset hrange).not_infinite (Set.infinite_range_of_injective hinj)
  -- ## 4. Conclude.
  rw [isBounded_iff_bddBelow_bddAbove]
  constructor
  · by_contra hb
    obtain ⟨x, hxS, -⟩ := (not_bddBelow_iff.mp hb) 0
    obtain ⟨q0, hq0C, -⟩ := hxS
    refine key_below q0.1 ?_
    intro t ht
    obtain ⟨x', hx'S, hx'⟩ := (not_bddBelow_iff.mp hb) t
    have htS : t ∈ Prod.fst '' C :=
      hSpre.Icc_subset hx'S ⟨q0, hq0C, rfl⟩ ⟨le_of_lt hx', ht⟩
    obtain ⟨q, hqC, hq1⟩ := htS
    exact ⟨q.2, by rw [← hq1]; exact hqC⟩
  · by_contra hb
    obtain ⟨x, hxS, -⟩ := (not_bddAbove_iff.mp hb) 0
    obtain ⟨q0, hq0C, -⟩ := hxS
    refine key_above q0.1 ?_
    intro t ht
    obtain ⟨x', hx'S, hx'⟩ := (not_bddAbove_iff.mp hb) t
    have htS : t ∈ Prod.fst '' C :=
      hSpre.Icc_subset ⟨q0, hq0C, rfl⟩ hx'S ⟨ht, le_of_lt hx'⟩
    obtain ⟨q, hqC, hq1⟩ := htS
    exact ⟨q.2, by rw [← hq1]; exact hqC⟩

end Work.Drive
