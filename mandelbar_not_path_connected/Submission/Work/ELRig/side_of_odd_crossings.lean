import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Parity of crossings

A continuous path `σ : ℝ → ℂ` which off a finite set `T ⊂ (0, b)` of "crossing times" runs inside
`A ∪ B` (`A`, `B` open and disjoint), and which at every crossing `t ∈ T` swaps sides between
`σ (t - δ)` and `σ (t + δ)`, has `σ 0` and `σ b` on *opposite* sides exactly when `#T` is odd.

The proof is the obvious one, made explicit: the sorted crossing times
`a 0 < a 1 < … < a (n-1)` (`n = #T`, obtained from `Finset.orderEmbOfFin`) cut `[0, b]` into
`n + 1` pieces; choosing one sample point `p j` in each piece (`Work.ELRig.p`), the side of `σ`
at `p j` is well defined (connectedness of `σ '' Icc` inside the disjoint open sets `A`, `B`),
consecutive sample points sit on opposite sides (the flip hypothesis at `a j`), and `σ b` sits on
the side of `p n`.  Tracking the propagation of `¬` along the finite sequence gives the parity.
-/

set_option maxHeartbeats 1000000

noncomputable section

open Set

namespace Work.ELRig

/-! ## The basic connectedness step -/

/-- **The side is constant on a crossing-free interval.**  If `s ≤ t` lie in `[0, b]` and no
point of `[s, t]` belongs to `T`, then `σ s ∈ A ↔ σ t ∈ A`. -/
lemma side_iff_of_Icc {A B : Set ℂ} {σ : ℝ → ℂ} {b : ℝ} {T : Finset ℝ}
    (hA : IsOpen A) (hB : IsOpen B) (hdisj : Disjoint A B) (hσ : Continuous σ)
    (hoff : ∀ t ∈ Set.Icc (0:ℝ) b, t ∉ T → σ t ∈ A ∪ B)
    {s t : ℝ} (hs : s ∈ Set.Icc (0:ℝ) b) (ht : t ∈ Set.Icc (0:ℝ) b) (hst : s ≤ t)
    (hnoT : ∀ u ∈ Set.Icc s t, u ∉ T) :
    (σ s ∈ A) ↔ (σ t ∈ A) := by
  have hsub : Set.Icc s t ⊆ Set.Icc (0:ℝ) b :=
    fun u hu => ⟨le_trans hs.1 hu.1, le_trans hu.2 ht.2⟩
  have himg : σ '' Set.Icc s t ⊆ A ∪ B := by
    rintro z ⟨u, hu, rfl⟩; exact hoff u (hsub hu) (hnoT u hu)
  have hpre : IsPreconnected (σ '' Set.Icc s t) :=
    (isPreconnected_Icc (a := s) (b := t)).image σ hσ.continuousOn
  rcases hpre.subset_or_subset hA hB hdisj himg with h | h
  · exact ⟨fun _ => h ⟨t, ⟨hst, le_rfl⟩, rfl⟩, fun _ => h ⟨s, ⟨le_rfl, hst⟩, rfl⟩⟩
  · constructor
    · intro hsA
      exact absurd (h ⟨s, ⟨le_rfl, hst⟩, rfl⟩) (Set.disjoint_left.mp hdisj hsA)
    · intro htA
      exact absurd (h ⟨t, ⟨hst, le_rfl⟩, rfl⟩) (Set.disjoint_left.mp hdisj htA)

/-! ## The break points of the sorted crossing times -/

/-- `q n a b` is the sequence `0, a 0, a 1, …, a (n-1), b, b, …`. -/
def q (n : ℕ) (a : Fin n → ℝ) (b : ℝ) : ℕ → ℝ
  | 0 => 0
  | (k+1) => if h : k < n then a ⟨k, h⟩ else b

/-- The sample point `p j = (q j + q (j+1)) / 2` in the `j`-th gap between consecutive
crossings (`j = 0, …, n`). -/
def p (n : ℕ) (a : Fin n → ℝ) (b : ℝ) (j : ℕ) : ℝ := (q n a b j + q n a b (j+1)) / 2

lemma q_zero (n : ℕ) (a : Fin n → ℝ) (b : ℝ) : q n a b 0 = 0 := rfl

lemma q_succ_of_lt {n : ℕ} {a : Fin n → ℝ} {b : ℝ} {k : ℕ} (hk : k < n) :
    q n a b (k+1) = a ⟨k, hk⟩ := by
  rw [show q n a b (k+1) = (if h : k < n then a ⟨k, h⟩ else b) from rfl, dite_eq_left hk]

lemma q_succ_of_le {n : ℕ} {a : Fin n → ℝ} {b : ℝ} {k : ℕ} (hk : n ≤ k) :
    q n a b (k+1) = b := by
  rw [show q n a b (k+1) = (if h : k < n then a ⟨k, h⟩ else b) from rfl,
      dite_eq_right (by omega)]

lemma q_lt_succ {n : ℕ} {a : Fin n → ℝ} {b : ℝ}
    (ha : StrictMono a) (h0 : ∀ i, 0 < a i) (hb : ∀ i, a i < b) (hn : 0 < n) :
    ∀ k, k ≤ n → q n a b k < q n a b (k+1) := by
  intro k hk
  rcases k with _ | j
  · have h1 : q n a b (0+1) = a ⟨0, hn⟩ := q_succ_of_lt (k := 0) hn
    rw [q_zero, h1]; exact h0 _
  · have hj : j < n := by omega
    rw [q_succ_of_lt (k := j) hj]
    by_cases hj1 : j + 1 < n
    · rw [q_succ_of_lt (k := j+1) hj1]; exact ha (by simp [Fin.lt_def])
    · rw [q_succ_of_le (k := j+1) (by omega)]; exact hb _

lemma q_mono {n : ℕ} {a : Fin n → ℝ} {b : ℝ}
    (ha : StrictMono a) (h0 : ∀ i, 0 < a i) (hb : ∀ i, a i < b) (hn : 0 < n)
    (i : ℕ) : ∀ j, i < j → j ≤ n+1 → q n a b i < q n a b j := by
  intro j
  induction j with
  | zero => intro h; omega
  | succ j ih =>
      intro hij hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hij with h | h
      · exact lt_trans (ih h (by omega)) (q_lt_succ ha h0 hb hn j (by omega))
      · rw [h]; exact q_lt_succ ha h0 hb hn j (by omega)

lemma q_mono_le {n : ℕ} {a : Fin n → ℝ} {b : ℝ}
    (ha : StrictMono a) (h0 : ∀ i, 0 < a i) (hb : ∀ i, a i < b) (hn : 0 < n) :
    ∀ i j, i ≤ j → j ≤ n+1 → q n a b i ≤ q n a b j := by
  intro i j hij hj
  rcases eq_or_lt_of_le hij with h | h
  · rw [h]
  · exact le_of_lt (q_mono ha h0 hb hn i j h hj)

lemma q_ge_zero {n : ℕ} {a : Fin n → ℝ} {b : ℝ}
    (h0 : ∀ i, 0 < a i) (hbpos : 0 < b) : ∀ j, 0 ≤ q n a b j := by
  intro j; rcases j with _ | k
  · rw [q_zero]
  · by_cases hk : k < n
    · rw [q_succ_of_lt hk]; exact le_of_lt (h0 _)
    · rw [q_succ_of_le (k := k) (by omega)]; exact le_of_lt hbpos

lemma q_le_b {n : ℕ} {a : Fin n → ℝ} {b : ℝ}
    (hb : ∀ i, a i < b) (hbpos : 0 < b) : ∀ j, q n a b j ≤ b := by
  intro j; rcases j with _ | k
  · rw [q_zero]; exact le_of_lt hbpos
  · by_cases hk : k < n
    · rw [q_succ_of_lt hk]; exact le_of_lt (hb _)
    · rw [q_succ_of_le (k := k) (by omega)]

lemma p_mem {n : ℕ} {a : Fin n → ℝ} {b : ℝ}
    (ha : StrictMono a) (h0 : ∀ i, 0 < a i) (hb : ∀ i, a i < b) (hn : 0 < n)
    {j : ℕ} (hj : j ≤ n) : q n a b j < p n a b j ∧ p n a b j < q n a b (j+1) := by
  have h1 := q_lt_succ ha h0 hb hn j hj
  simp only [p]
  constructor <;> linarith

/-! ## The main theorem -/

/-- **Parity of crossings.**  Let `σ : ℝ → ℂ` be a continuous path, `A` and `B` two open disjoint
subsets of `ℂ`, and `T` a finite set of "crossing times" in `(0, b)`.  Assume

* `σ t ∈ A ∪ B` for every `t ∈ [0, b]` off `T`,
* at every crossing `t ∈ T` the two nearby points `σ (t + δ)` and `σ (t - δ)` (for small `δ > 0`,
  both off `T` and in `[0, b]`) lie in *opposite* sides,
* `σ b ∈ A`.

Then an **odd** number of crossings forces `σ 0 ∈ B`. -/
theorem side_of_odd_crossings {A B : Set ℂ} {σ : ℝ → ℂ} {b : ℝ} {T : Finset ℝ}
    (hA : IsOpen A) (hB : IsOpen B) (hdisj : Disjoint A B)
    (hσ : Continuous σ)
    (hT0 : ∀ t ∈ T, 0 < t) (hTb : ∀ t ∈ T, t < b)
    (hodd : Odd T.card)
    (hoff : ∀ t ∈ Set.Icc (0 : ℝ) b, t ∉ T → σ t ∈ A ∪ B)
    (hflip : ∀ t ∈ T, ∃ ε > 0, ∀ δ : ℝ, 0 < δ → δ < ε → t + δ ∈ Set.Icc (0 : ℝ) b →
      t - δ ∈ Set.Icc (0 : ℝ) b → t + δ ∉ T → t - δ ∉ T →
      (σ (t + δ) ∈ A ∧ σ (t - δ) ∈ B) ∨ (σ (t + δ) ∈ B ∧ σ (t - δ) ∈ A))
    (htop : σ b ∈ A) : σ 0 ∈ B := by
  classical
  set n := T.card with hn
  obtain ⟨mm, hmm⟩ := hodd
  have hnpos : 0 < n := by omega
  let a : Fin n ↪o ℝ := T.orderEmbOfFin hn.symm
  have ha_mono : StrictMono (a : Fin n → ℝ) := a.strictMono
  have ha_mem : ∀ i : Fin n, a i ∈ T := fun i => Finset.orderEmbOfFin_mem T hn.symm i
  have ha_range : Set.range (a : Fin n → ℝ) = (T : Set ℝ) := Finset.range_orderEmbOfFin T hn.symm
  have ha0 : ∀ i : Fin n, 0 < a i := fun i => hT0 _ (ha_mem i)
  have hab : ∀ i : Fin n, a i < b := fun i => hTb _ (ha_mem i)
  have hbpos : 0 < b := lt_trans (ha0 ⟨0, hnpos⟩) (hab ⟨0, hnpos⟩)
  -- every element of `T` is some `a i`
  have ht_range : ∀ t ∈ T, ∃ i : Fin n, a i = t := by
    intro t ht
    have hmem : t ∈ Set.range (a : Fin n → ℝ) := by rw [ha_range]; exact ht
    exact hmem
  -- basic size facts about the sample points
  have hp_ge0 : ∀ j, j ≤ n → 0 ≤ p n a b j := by
    intro j hj
    have h1 := (p_mem ha_mono ha0 hab hnpos hj).1
    have h2 := q_ge_zero ha0 hbpos j
    linarith
  have hp_le_b : ∀ j, j ≤ n → p n a b j ≤ b := by
    intro j hj
    have h1 := (p_mem ha_mono ha0 hab hnpos hj).2
    have h2 := q_le_b hab hbpos (j+1)
    linarith
  have hpI : ∀ j, j ≤ n → p n a b j ∈ Set.Icc (0:ℝ) b :=
    fun j hj => ⟨hp_ge0 j hj, hp_le_b j hj⟩
  -- the unique crossing in the `j`-th gap
  have hTmid : ∀ {j : ℕ} (hj : j < n) {u : ℝ},
      u ∈ Set.Icc (p n a b j) (p n a b (j+1)) → u ∈ T → u = a ⟨j, hj⟩ := by
    intro j hj u hu huT
    obtain ⟨i, hi⟩ := ht_range u huT
    have hqi : q n a b (i.val + 1) = u := (q_succ_of_lt i.isLt).trans hi
    have hpj : q n a b j < p n a b j := (p_mem ha_mono ha0 hab hnpos (le_of_lt hj)).1
    have hpj1 : p n a b (j+1) < q n a b (j+2) :=
      (p_mem ha_mono ha0 hab hnpos (by omega : j+1 ≤ n)).2
    have hlt1 : q n a b j < q n a b (i.val+1) := by rw [hqi]; exact lt_of_lt_of_le hpj hu.1
    have hlt2 : q n a b (i.val+1) < q n a b (j+2) := by rw [hqi]; exact lt_of_le_of_lt hu.2 hpj1
    have hji : j < i.val + 1 := by
      by_contra h
      push_neg at h
      exact absurd (q_mono_le ha_mono ha0 hab hnpos (i.val+1) j h (by omega)) (not_le.mpr hlt1)
    have hi2 : i.val + 1 < j + 2 := by
      by_contra h
      push_neg at h
      exact absurd (q_mono_le ha_mono ha0 hab hnpos (j+2) (i.val+1) h (by omega)) (not_le.mpr hlt2)
    have hiv : i.val = j := by omega
    have hfin : i = ⟨j, hj⟩ := Fin.ext hiv
    rw [hfin] at hi
    exact hi.symm
  -- everything in `T` is `> p 0`
  have hTle0 : ∀ t ∈ T, p n a b 0 < t := by
    intro t ht
    obtain ⟨i, hi⟩ := ht_range t ht
    have hqi : q n a b (i.val + 1) = t := (q_succ_of_lt i.isLt).trans hi
    have hle : q n a b 1 ≤ q n a b (i.val + 1) :=
      q_mono_le ha_mono ha0 hab hnpos 1 (i.val+1) (by omega) (by omega)
    have hpq : p n a b 0 < q n a b 1 := (p_mem ha_mono ha0 hab hnpos (by omega : 0 ≤ n)).2
    rw [hqi] at hle
    linarith
  -- everything in `T` is `< p n`
  have hTltn : ∀ t ∈ T, t < p n a b n := by
    intro t ht
    obtain ⟨i, hi⟩ := ht_range t ht
    have hqi : q n a b (i.val + 1) = t := (q_succ_of_lt i.isLt).trans hi
    have hle : q n a b (i.val + 1) ≤ q n a b n :=
      q_mono_le ha_mono ha0 hab hnpos (i.val+1) n (by omega) (by omega)
    have hqn : q n a b n < p n a b n := (p_mem ha_mono ha0 hab hnpos le_rfl).1
    rw [hqi] at hle
    linarith
  -- `P j` : the side of `σ` at the `j`-th sample point
  let P : ℕ → Prop := fun j => σ (p n a b j) ∈ A
  -- `σ b` is on the `A`-side, hence so is `p n`
  have hPn : P n := by
    have hbI : b ∈ Set.Icc (0:ℝ) b := ⟨le_of_lt hbpos, le_rfl⟩
    have hnoT : ∀ u ∈ Set.Icc (p n a b n) b, u ∉ T := by
      intro u hu huT
      exact absurd hu.1 (not_le.mpr (hTltn u huT))
    have := side_iff_of_Icc hA hB hdisj hσ hoff (hpI n le_rfl) hbI (hp_le_b n le_rfl) hnoT
    exact this.mpr htop
  -- `σ 0` is on the side of `p 0`
  have hP0 : (σ 0 ∈ A) ↔ P 0 := by
    have h0I : (0:ℝ) ∈ Set.Icc (0:ℝ) b := ⟨le_rfl, le_of_lt hbpos⟩
    have hnoT : ∀ u ∈ Set.Icc (0:ℝ) (p n a b 0), u ∉ T := by
      intro u hu huT
      exact absurd hu.2 (not_le.mpr (hTle0 u huT))
    exact side_iff_of_Icc hA hB hdisj hσ hoff h0I (hpI 0 (by omega)) (hp_ge0 0 (by omega)) hnoT
  -- consecutive sample points sit on opposite sides
  have hstep : ∀ j, j < n → (P j ↔ ¬ P (j+1)) := by
    intro j hj
    obtain ⟨ε, hεpos, hεflip⟩ := hflip (a ⟨j, hj⟩) (ha_mem ⟨j, hj⟩)
    set δ : ℝ := min (ε/2) (min ((q n a b (j+1) - p n a b j)/2)
                                   ((p n a b (j+1) - q n a b (j+1))/2)) with hδdef
    have hajq : a ⟨j, hj⟩ = q n a b (j+1) := (q_succ_of_lt hj).symm
    have hpj_qj : q n a b j < p n a b j := (p_mem ha_mono ha0 hab hnpos (le_of_lt hj)).1
    have hpj_qj1 : p n a b j < q n a b (j+1) := (p_mem ha_mono ha0 hab hnpos (le_of_lt hj)).2
    have hqj1_pj1 : q n a b (j+1) < p n a b (j+1) :=
      (p_mem ha_mono ha0 hab hnpos (by omega : j+1 ≤ n)).1
    have hδpos : 0 < δ := by
      rw [hδdef]; exact lt_min (by linarith) (lt_min (by linarith) (by linarith))
    have hδε : δ < ε := by
      rw [hδdef]; exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have hδA : δ < q n a b (j+1) - p n a b j := by
      rw [hδdef]
      exact lt_of_le_of_lt (le_trans (min_le_right _ _) (min_le_left _ _)) (by linarith)
    have hδB : δ < p n a b (j+1) - q n a b (j+1) := by
      rw [hδdef]
      exact lt_of_le_of_lt (le_trans (min_le_right _ _) (min_le_right _ _)) (by linarith)
    have hleft : p n a b j < a ⟨j, hj⟩ - δ := by rw [hajq]; linarith
    have hright : a ⟨j, hj⟩ + δ < p n a b (j+1) := by rw [hajq]; linarith
    have hIJ1 : a ⟨j, hj⟩ + δ ∈ Set.Icc (0:ℝ) b :=
      ⟨le_of_lt (by linarith [ha0 ⟨j, hj⟩, hδpos]),
       le_of_lt (lt_of_lt_of_le hright (hp_le_b (j+1) (by omega)))⟩
    have hIJ2 : a ⟨j, hj⟩ - δ ∈ Set.Icc (0:ℝ) b :=
      ⟨le_of_lt (lt_of_le_of_lt (hp_ge0 j (le_of_lt hj)) hleft),
       le_of_lt (lt_trans (by linarith [hδpos]) (hab ⟨j, hj⟩))⟩
    have hnotT1 : a ⟨j, hj⟩ + δ ∉ T := by
      intro hT
      have hmem : a ⟨j, hj⟩ + δ ∈ Set.Icc (p n a b j) (p n a b (j+1)) :=
        ⟨le_of_lt (by rw [hajq]; linarith), le_of_lt hright⟩
      have hthis := hTmid hj hmem hT
      linarith [hδpos]
    have hnotT2 : a ⟨j, hj⟩ - δ ∉ T := by
      intro hT
      have hmem : a ⟨j, hj⟩ - δ ∈ Set.Icc (p n a b j) (p n a b (j+1)) :=
        ⟨le_of_lt hleft, le_of_lt (by rw [hajq]; linarith)⟩
      have hthis := hTmid hj hmem hT
      linarith [hδpos]
    have hfl := hεflip δ hδpos hδε hIJ1 hIJ2 hnotT1 hnotT2
    have hsideL : (σ (a ⟨j, hj⟩ - δ) ∈ A) ↔ P j := by
      have hnoT : ∀ u ∈ Set.Icc (p n a b j) (a ⟨j, hj⟩ - δ), u ∉ T := by
        intro u hu huT
        have hmem : u ∈ Set.Icc (p n a b j) (p n a b (j+1)) :=
          ⟨hu.1, le_of_lt (lt_of_le_of_lt hu.2 (by linarith [hright, hδpos]))⟩
        have hthis := hTmid hj hmem huT
        rw [hthis] at hu
        linarith [hu.2, hδpos]
      exact (side_iff_of_Icc hA hB hdisj hσ hoff (hpI j (le_of_lt hj)) hIJ2
        (le_of_lt hleft) hnoT).symm
    have hsideR : (σ (a ⟨j, hj⟩ + δ) ∈ A) ↔ P (j+1) := by
      have hnoT : ∀ u ∈ Set.Icc (a ⟨j, hj⟩ + δ) (p n a b (j+1)), u ∉ T := by
        intro u hu huT
        have hmem : u ∈ Set.Icc (p n a b j) (p n a b (j+1)) :=
          ⟨le_of_lt (lt_of_lt_of_le hleft (le_trans (by linarith [hδpos]) hu.1)), hu.2⟩
        have hthis := hTmid hj hmem huT
        rw [hthis] at hu
        linarith [hu.1, hδpos]
      exact side_iff_of_Icc hA hB hdisj hσ hoff hIJ1 (hpI (j+1) (by omega))
        (le_of_lt hright) hnoT
    rcases hfl with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · constructor
      · intro hPj hPj1
        exact absurd (hsideL.mpr hPj) (Set.disjoint_right.mp hdisj h2)
      · intro hneg
        exact absurd (hsideR.mp h1) hneg
    · constructor
      · intro _ hPj1
        exact absurd (hsideR.mpr hPj1) (Set.disjoint_right.mp hdisj h1)
      · intro _
        exact hsideL.mp h2
  -- the parity propagation
  have hpar : ∀ j, j ≤ n → (P j ↔ (P 0 ↔ Even j)) := by
    intro j hj
    induction j with
    | zero => simp
    | succ j ih =>
        have hj' : j < n := by omega
        have hih : P j ↔ (P 0 ↔ Even j) := ih (by omega)
        have hsj : P (j+1) ↔ ¬ P j := by rw [hstep j hj']; tauto
        rw [hsj, hih, Nat.even_add_one]
        tauto
  have hnEven : ¬ Even n := by rintro ⟨kk, hkk⟩; omega
  have hP0n : ¬ P 0 := by
    intro hP0'
    exact hnEven (((hpar n le_rfl).mp hPn).mp hP0')
  have h0notA : σ 0 ∉ A := fun h => hP0n (hP0.mp h)
  have h0mem : σ 0 ∈ A ∪ B :=
    hoff 0 ⟨le_rfl, le_of_lt hbpos⟩ (fun h0T => absurd (hT0 0 h0T) (lt_irrefl 0))
  rcases h0mem with h | h
  · exact absurd h h0notA
  · exact h

end Work.ELRig
