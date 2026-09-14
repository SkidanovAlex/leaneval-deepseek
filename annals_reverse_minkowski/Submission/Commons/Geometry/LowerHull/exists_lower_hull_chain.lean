import Mathlib
set_option autoImplicit false

open scoped BigOperators

namespace Commons.Geometry.LowerHull

noncomputable def chord (p q : ℝ × ℝ) (x : ℝ) : ℝ :=
  p.2 + (q.2 - p.2) * ((x - p.1) / (q.1 - p.1))

lemma chord_self_left (p q : ℝ × ℝ) : chord p q p.1 = p.2 := by
  unfold chord
  simp

lemma chord_self_right (p q : ℝ × ℝ) (h : q.1 - p.1 ≠ 0) : chord p q q.1 = q.2 := by
  unfold chord
  field_simp [h]
  ring

-- ---------------------------------------------------------------------------
-- Chain predicates over Fin indices
-- ---------------------------------------------------------------------------

/-- The segment from `a` to `b` (a.val < b.val) lies below all data points between. -/
def segBelow {N : ℕ} (y : Fin (N + 1) → ℝ) (a b : Fin (N + 1)) : Prop :=
  a.val < b.val ∧
    ∀ i : Fin (N + 1),
      a.val ≤ i.val → i.val ≤ b.val →
        y a + (y b - y a) * (((i.val : ℝ) - (a.val : ℝ)) / ((b.val : ℝ) - (a.val : ℝ))) ≤ y i

/-- slope of the segment from a to b (a < b) -/
noncomputable def slope {N : ℕ} (y : Fin (N + 1) → ℝ) (a b : Fin (N + 1)) : ℝ :=
  (y b - y a) / (((b.val : ℝ) - (a.val : ℝ)))

/-- A weak lower chain: passes through 0 and N, strictly increasing, and each
segment lies below the data between its endpoints. (No slope convexity required.) -/
def chainProp {N : ℕ} (y : Fin (N + 1) → ℝ) (k : ℕ) (v : Fin (k + 1) → Fin (N + 1)) : Prop :=
  v 0 = 0 ∧
    v ⟨k, Nat.lt_succ_self k⟩ = ⟨N, Nat.lt_succ_self N⟩ ∧
      ∀ j : Fin k, segBelow y (v (Fin.castSucc j)) (v (Fin.succ j))

-- ---------------------------------------------------------------------------
-- Below-ness of a unit segment between consecutive integers is automatic.
-- ---------------------------------------------------------------------------

lemma segBelow_consecutive {N : ℕ} (y : Fin (N + 1) → ℝ) {a : Fin (N + 1)}
    (ha1 : a.val + 1 < N + 1) : segBelow y a ⟨a.val + 1, ha1⟩ := by
  constructor
  · exact Nat.lt_succ_self a.val
  · intro i hia hib
    have hib' : i.val ≤ a.val + 1 := by simpa using hib
    have hc : i.val = a.val ∨ i.val = a.val + 1 := by omega
    rcases hc with hi | hi
    · have hi' : i = a := Fin.ext hi
      rw [hi']
      change chord (a.val, y a) ((⟨a.val + 1, ha1⟩ : Fin (N + 1)).val, y ⟨a.val + 1, ha1⟩)
        ((a.val : ℝ)) ≤ y a
      rw [chord_self_left]
    · have hi' : i = ⟨a.val + 1, ha1⟩ := by
        apply Fin.ext
        simpa using hi
      rw [hi']
      have hbv : (⟨a.val + 1, ha1⟩ : Fin (N + 1)).val = a.val + 1 := rfl
      have hne : ((⟨a.val + 1, ha1⟩ : Fin (N + 1)).val : ℝ) - (a.val : ℝ) ≠ 0 := by
        rw [hbv]
        norm_num
      change chord (a.val, y a) ((⟨a.val + 1, ha1⟩ : Fin (N + 1)).val, y ⟨a.val + 1, ha1⟩)
        ((⟨a.val + 1, ha1⟩ : Fin (N + 1)).val : ℝ) ≤ y ⟨a.val + 1, ha1⟩
      rw [chord_self_right (a.val, y a) ((⟨a.val + 1, ha1⟩ : Fin (N + 1)).val, y ⟨a.val + 1, ha1⟩) hne]

-- ---------------------------------------------------------------------------
-- The full chain: every integer is a vertex (k = N, v = identity)
-- ---------------------------------------------------------------------------

lemma chainProp_full (N : ℕ) (y : Fin (N + 1) → ℝ) :
    chainProp y N (fun i : Fin (N + 1) => i) := by
  constructor
  · rfl
  constructor
  · rfl
  · intro j
    have hj1 : j.val + 1 < N + 1 := by omega
    have hcast : Fin.castSucc j = ⟨j.val, by omega⟩ := by
      apply Fin.ext
      simp
    have hsucc : Fin.succ j = ⟨j.val + 1, hj1⟩ := by
      apply Fin.ext
      simp
    rw [hcast, hsucc]
    exact segBelow_consecutive y (a := ⟨j.val, by omega⟩) hj1

-- ---------------------------------------------------------------------------
-- Chord comparison under slope ordering (all ℝ)
-- ---------------------------------------------------------------------------

lemma slope_mid_le_left {a b c ya yb yc : ℝ}
    (hab : a < b) (hbc : b < c)
    (hsl : (yb - ya) / (b - a) ≥ (yc - yb) / (c - b)) :
    (yc - ya) / (c - a) ≤ (yb - ya) / (b - a) := by
  have hbpa : 0 < b - a := sub_pos.mpr hab
  have hcpb : 0 < c - b := sub_pos.mpr hbc
  have hcpa : 0 < c - a := by nlinarith
  field_simp [ne_of_gt hcpb, ne_of_gt hbpa] at hsl
  field_simp [ne_of_gt hcpa, ne_of_gt hbpa]
  nlinarith

lemma slope_mid_le_right {a b c ya yb yc : ℝ}
    (hab : a < b) (hbc : b < c)
    (hsl : (yb - ya) / (b - a) ≥ (yc - yb) / (c - b)) :
    (yc - yb) / (c - b) ≤ (yc - ya) / (c - a) := by
  have hbpa : 0 < b - a := sub_pos.mpr hab
  have hcpb : 0 < c - b := sub_pos.mpr hbc
  have hcpa : 0 < c - a := by nlinarith
  field_simp [ne_of_gt hcpb, ne_of_gt hbpa] at hsl
  field_simp [ne_of_gt hcpb, ne_of_gt hcpa]
  nlinarith

lemma chord_sub_chord_left (a b c ya yb yc x : ℝ) (hb : b - a ≠ 0) (hc : c - a ≠ 0) :
    chord (a, ya) (b, yb) x - chord (a, ya) (c, yc) x =
      (x - a) * ((yb - ya) / (b - a) - (yc - ya) / (c - a)) := by
  unfold chord
  field_simp [hb, hc]
  ring

lemma chord_sub_chord_right (a b c ya yb yc x : ℝ) (hc : c - b ≠ 0) (hc2 : c - a ≠ 0) :
    chord (b, yb) (c, yc) x - chord (a, ya) (c, yc) x =
      (c - x) * ((yc - ya) / (c - a) - (yc - yb) / (c - b)) := by
  unfold chord
  field_simp [hc, hc2]
  ring

-- chord_ac(x) <= chord_ab(x) on [a,b] when slopes satisfy sab >= sbc
lemma chord_le_chord_left {a b c ya yb yc x : ℝ}
    (hab : a < b) (hbc : b < c) (hxa : a ≤ x) (hxb : x ≤ b)
    (hsl : (yb - ya) / (b - a) ≥ (yc - yb) / (c - b)) :
    chord (a, ya) (c, yc) x ≤ chord (a, ya) (b, yb) x := by
  have hbpa : 0 < b - a := sub_pos.mpr hab
  have hcpa : 0 < c - a := by nlinarith
  have hdif : 0 ≤ x - a := sub_nonneg.mpr hxa
  have hs : (yc - ya) / (c - a) ≤ (yb - ya) / (b - a) := slope_mid_le_left hab hbc hsl
  have hnon : 0 ≤ (x - a) * ((yb - ya) / (b - a) - (yc - ya) / (c - a)) := by
    exact mul_nonneg hdif (sub_nonneg.mpr hs)
  have hdiff := chord_sub_chord_left a b c ya yb yc x (ne_of_gt hbpa) (ne_of_gt hcpa)
  linarith

lemma chord_le_chord_right {a b c ya yb yc x : ℝ}
    (hab : a < b) (hbc : b < c) (hxb : b ≤ x) (hxc : x ≤ c)
    (hsl : (yb - ya) / (b - a) ≥ (yc - yb) / (c - b)) :
    chord (a, ya) (c, yc) x ≤ chord (b, yb) (c, yc) x := by
  have hcpb : 0 < c - b := sub_pos.mpr hbc
  have hcpa : 0 < c - a := by nlinarith
  have hdc : 0 ≤ c - x := sub_nonneg.mpr hxc
  have hs : (yc - yb) / (c - b) ≤ (yc - ya) / (c - a) := slope_mid_le_right hab hbc hsl
  have hnon : 0 ≤ (c - x) * ((yc - ya) / (c - a) - (yc - yb) / (c - b)) := by
    exact mul_nonneg hdc (sub_nonneg.mpr hs)
  have hdiff := chord_sub_chord_right a b c ya yb yc x (ne_of_gt hcpb) (ne_of_gt hcpa)
  linarith

-- ---------------------------------------------------------------------------
-- Merging two segments with non-increasing slopes keeps below-ness
-- ---------------------------------------------------------------------------

lemma segBelow_merge {N : ℕ} {y : Fin (N + 1) → ℝ} {a b c : Fin (N + 1)}
    (hl : segBelow y a b) (hr : segBelow y b c)
    (hsl : slope y b c ≤ slope y a b) : segBelow y a c := by
  rcases hl with ⟨hab, hbelow_l⟩
  rcases hr with ⟨hbc, hbelow_r⟩
  constructor
  · exact lt_trans hab hbc
  · intro i hia hic
    by_cases hib : i.val ≤ b.val
    · have h1 : chord (a.val, y a) (c.val, y c) (i.val : ℝ) ≤
                chord (a.val, y a) (b.val, y b) (i.val : ℝ) := by
        exact chord_le_chord_left (a := (a.val : ℝ)) (b := (b.val : ℝ)) (c := (c.val : ℝ))
          (ya := y a) (yb := y b) (yc := y c) (x := (i.val : ℝ))
          (by exact_mod_cast hab) (by exact_mod_cast hbc) (by exact_mod_cast hia) (by exact_mod_cast hib) hsl
      have h2 : chord (a.val, y a) (b.val, y b) (i.val : ℝ) ≤ y i := hbelow_l i hia hib
      exact le_trans h1 h2
    · have hbi : b.val < i.val := by omega
      have h1 : chord (a.val, y a) (c.val, y c) (i.val : ℝ) ≤
                chord (b.val, y b) (c.val, y c) (i.val : ℝ) := by
        exact chord_le_chord_right (a := (a.val : ℝ)) (b := (b.val : ℝ)) (c := (c.val : ℝ))
          (ya := y a) (yb := y b) (yc := y c) (x := (i.val : ℝ))
          (by exact_mod_cast hab) (by exact_mod_cast hbc) (by exact_mod_cast (le_of_lt hbi)) (by exact_mod_cast hic) hsl
      have h2 : chord (b.val, y b) (c.val, y c) (i.val : ℝ) ≤ y i := hbelow_r i (le_of_lt hbi) hic
      exact le_trans h1 h2

-- ---------------------------------------------------------------------------
-- Deleting an interior vertex of a chain (the merge construction)
-- ---------------------------------------------------------------------------

/-- Delete the vertex at natural index `r` (1 ≤ r ≤ k-1) of a chain with vertices
indexed 0..k. The new chain has vertices 0..k-1. -/
noncomputable def delChain {N k : ℕ} (v : Fin (k + 1) → Fin (N + 1)) (r : ℕ)
    (hr1 : 1 ≤ r) (hrk : r ≤ k - 1) : Fin (k - 1 + 1) → Fin (N + 1) := fun t =>
  if ht : t.val < r then
    v ⟨t.val, by
      have h : t.val < k - 1 + 1 := t.isLt
      omega⟩
  else
    v ⟨t.val + 1, by
      have h : t.val < k - 1 + 1 := t.isLt
      omega⟩

lemma delChain_lt {N k : ℕ} (v : Fin (k + 1) → Fin (N + 1)) (r : ℕ)
    (hr1 : 1 ≤ r) (hrk : r ≤ k - 1) (t : Fin (k - 1 + 1)) (ht : t.val < r) :
    delChain v r hr1 hrk t = v (⟨t.val, by
      have h : t.val < k - 1 + 1 := t.isLt
      omega⟩ : Fin (k + 1)) := by
  unfold delChain
  simp [ht]

lemma delChain_ge {N k : ℕ} (v : Fin (k + 1) → Fin (N + 1)) (r : ℕ)
    (hr1 : 1 ≤ r) (hrk : r ≤ k - 1) (t : Fin (k - 1 + 1)) (ht : ¬ t.val < r) :
    delChain v r hr1 hrk t = v (⟨t.val + 1, by
      have h : t.val < k - 1 + 1 := t.isLt
      omega⟩ : Fin (k + 1)) := by
  unfold delChain
  simp [ht]

-- if a chain satisfies below-ness for all old segments then the deleted chain
-- satisfies it for the segment ending just before the deleted vertex.
lemma segBelow_del_before {N k : ℕ} {y : Fin (N + 1) → ℝ} {v : Fin (k + 1) → Fin (N + 1)} {r : ℕ}
    (hr1 : 1 ≤ r) (hrk : r ≤ k - 1)
    (hseg : ∀ s : Fin k, segBelow y (v (Fin.castSucc s)) (v (Fin.succ s)))
    {s : Fin (k - 1)} (hs : s.val + 1 < r) :
    segBelow y (delChain v r hr1 hrk (Fin.castSucc s)) (delChain v r hr1 hrk (Fin.succ s)) := by
  let o : Fin k := ⟨s.val, by omega⟩
  have h1 : delChain v r hr1 hrk (Fin.castSucc s) = v (Fin.castSucc o) := by
    rw [delChain_lt v r hr1 hrk (Fin.castSucc s) (by simp; omega)]
    all_goals try (congr 1 <;> apply Fin.ext <;> dsimp [o] <;> omega)
  have h2 : delChain v r hr1 hrk (Fin.succ s) = v (Fin.succ o) := by
    rw [delChain_lt v r hr1 hrk (Fin.succ s) (by simp; omega)]
    all_goals try (congr 1 <;> apply Fin.ext <;> dsimp [o] <;> omega)
  rw [h1, h2]
  exact hseg o

-- ... for the segment starting just after the deleted vertex.
lemma segBelow_del_after {N k : ℕ} {y : Fin (N + 1) → ℝ} {v : Fin (k + 1) → Fin (N + 1)} {r : ℕ}
    (hr1 : 1 ≤ r) (hrk : r ≤ k - 1)
    (hseg : ∀ s : Fin k, segBelow y (v (Fin.castSucc s)) (v (Fin.succ s)))
    {s : Fin (k - 1)} (hs : r ≤ s.val) :
    segBelow y (delChain v r hr1 hrk (Fin.castSucc s)) (delChain v r hr1 hrk (Fin.succ s)) := by
  let o : Fin k := ⟨s.val + 1, by omega⟩
  have h1 : delChain v r hr1 hrk (Fin.castSucc s) = v (Fin.castSucc o) := by
    rw [delChain_ge v r hr1 hrk (Fin.castSucc s) (by simp; omega)]
    all_goals try (congr 1 <;> apply Fin.ext <;> dsimp [o] <;> omega)
  have h2 : delChain v r hr1 hrk (Fin.succ s) = v (Fin.succ o) := by
    rw [delChain_ge v r hr1 hrk (Fin.succ s) (by simp; omega)]
    all_goals try (congr 1 <;> apply Fin.ext <;> dsimp [o] <;> omega)
  rw [h1, h2]
  exact hseg o

-- merged segment: the segment of the deleted chain that spans old segments j and j+1
-- (here s.val = j.val)
lemma segBelow_del_merge {N k : ℕ} {y : Fin (N + 1) → ℝ} {v : Fin (k + 1) → Fin (N + 1)}
    {j : Fin k} (hj : j.val + 1 < k)
    (hsegL : segBelow y (v (Fin.castSucc j)) (v (Fin.succ j)))
    (hsegR : segBelow y (v (Fin.castSucc (⟨j.val + 1, hj⟩ : Fin k))) (v (Fin.succ (⟨j.val + 1, hj⟩ : Fin k))))
    (hsl : slope y (v (Fin.succ j)) (v (Fin.succ (⟨j.val + 1, hj⟩ : Fin k))) ≤
           slope y (v (Fin.castSucc j)) (v (Fin.succ j)))
    {s : Fin (k - 1)} (hs : s.val = j.val) :
    segBelow y (delChain v (j.val + 1) (by omega) (by omega) (Fin.castSucc s))
              (delChain v (j.val + 1) (by omega) (by omega) (Fin.succ s)) := by
  let r : ℕ := j.val + 1
  have hr1 : 1 ≤ r := by omega
  have hrk : r ≤ k - 1 := by omega
  have h1 : delChain v r hr1 hrk (Fin.castSucc s) = v (Fin.castSucc j) := by
    have hlt : (Fin.castSucc s).val < r := by
      have hv : (Fin.castSucc s).val = s.val := rfl
      rw [hv, hs]
      dsimp [r]
      omega
    rw [delChain_lt v r hr1 hrk (Fin.castSucc s) hlt]
    congr 1
    apply Fin.ext
    all_goals simpa [hs]
  have h2 : delChain v r hr1 hrk (Fin.succ s) = v (Fin.succ (⟨j.val + 1, hj⟩ : Fin k)) := by
    have hge : ¬ (Fin.succ s).val < r := by
      have hv : (Fin.succ s).val = s.val + 1 := rfl
      rw [hv, hs]
      dsimp [r]
      omega
    rw [delChain_ge v r hr1 hrk (Fin.succ s) hge]
    congr 1
    apply Fin.ext
    all_goals simpa [hs]
  rw [h1, h2]
  have hm : Fin.succ j = Fin.castSucc (⟨j.val + 1, hj⟩ : Fin k) := by
    apply Fin.ext
    all_goals simp
  have hsegR' : segBelow y (v (Fin.succ j)) (v (Fin.succ (⟨j.val + 1, hj⟩ : Fin k))) := by
    rw [← hm] at hsegR
    exact hsegR
  exact segBelow_merge hsegL hsegR' hsl


-- Delete the interior vertex between two segments with non-increasing slopes:
-- the resulting chain is again a weak chain (with one fewer vertex).
lemma chainProp_del {N k : ℕ} {y : Fin (N + 1) → ℝ} {v : Fin (k + 1) → Fin (N + 1)}
    (hv : chainProp y k v) (j : Fin k) (hj : j.val + 1 < k)
    (hsl : slope y (v (Fin.succ j)) (v (Fin.succ (⟨j.val + 1, hj⟩ : Fin k))) ≤
           slope y (v (Fin.castSucc j)) (v (Fin.succ j))) :
    ∃ w : Fin ((k - 1) + 1) → Fin (N + 1), chainProp y (k - 1) w := by
  let r : ℕ := j.val + 1
  have hr1 : 1 ≤ r := by omega
  have hrk : r ≤ k - 1 := by omega
  let w : Fin ((k - 1) + 1) → Fin (N + 1) := delChain v r hr1 hrk
  refine ⟨w, ?_⟩
  rcases hv with ⟨hstart, hend, hseg⟩
  constructor
  · have hz : (0 : Fin ((k - 1) + 1)).val < r := by
      simpa [r]
    have hw : w (0 : Fin ((k - 1) + 1)) = v (⟨0, by omega⟩ : Fin (k + 1)) := by
      dsimp [w]
      rw [delChain_lt v r hr1 hrk (0 : Fin ((k - 1) + 1)) hz]
      all_goals try (congr 1 <;> apply Fin.ext <;> rfl)
    rw [hw]
    convert hstart using 1
    all_goals try (apply Fin.ext <;> rfl)
  constructor
  · have ht : ¬ (⟨k - 1, Nat.lt_succ_self (k - 1)⟩ : Fin ((k - 1) + 1)).val < r := by
      dsimp
      omega
    have hw : w (⟨k - 1, Nat.lt_succ_self (k - 1)⟩ : Fin ((k - 1) + 1)) =
        v (⟨k, by omega⟩ : Fin (k + 1)) := by
      dsimp [w]
      rw [delChain_ge v r hr1 hrk (⟨k - 1, Nat.lt_succ_self (k - 1)⟩ : Fin ((k - 1) + 1)) ht]
      congr 1
      apply Fin.ext
      all_goals try (change k - 1 + 1 = k <;> omega)
    rw [hw]
    convert hend using 1
    all_goals try (apply Fin.ext <;> rfl)
  · intro s
    by_cases h1 : s.val + 1 < r
    · exact segBelow_del_before hr1 hrk hseg h1
    · by_cases h2 : r ≤ s.val
      · exact segBelow_del_after hr1 hrk hseg h2
      · have hmid : s.val = j.val := by
          dsimp [r] at h1 h2 ⊢
          omega
        exact segBelow_del_merge hj (hseg j) (hseg (⟨j.val + 1, hj⟩ : Fin k)) hsl hmid

-- ---------------------------------------------------------------------------
-- Main theorem: take a weak chain with the minimal number of vertices. Then the
-- slopes must be strictly increasing (else merge two adjacent segments).
-- ---------------------------------------------------------------------------

theorem exists_lower_hull_chain {N : ℕ} (y : Fin (N + 1) → ℝ) :
    ∃ (k : ℕ) (v : Fin (k + 1) → Fin (N + 1)),
      v 0 = 0 ∧
      v ⟨k, Nat.lt_succ_self k⟩ = ⟨N, Nat.lt_succ_self N⟩ ∧
      (∀ j : Fin k, (v (Fin.castSucc j)).val < (v (Fin.succ j)).val) ∧
      (∀ (j : Fin k) (i : Fin (N + 1)),
        (v (Fin.castSucc j)).val ≤ i.val → i.val ≤ (v (Fin.succ j)).val →
          y (v (Fin.castSucc j)) +
              (y (v (Fin.succ j)) - y (v (Fin.castSucc j))) *
                (((i.val : ℝ) - ((v (Fin.castSucc j)).val : ℝ)) /
                  (((v (Fin.succ j)).val : ℝ) - ((v (Fin.castSucc j)).val : ℝ))) ≤
            y i) ∧
      (∀ (j : Fin k) (hj : j.val + 1 < k),
        ((y (v (Fin.succ j)) - y (v (Fin.castSucc j))) /
            (((v (Fin.succ j)).val : ℝ) - ((v (Fin.castSucc j)).val : ℝ))) <
          ((y (v ⟨j.val + 2, by omega⟩) - y (v (Fin.succ j))) /
            (((v ⟨j.val + 2, by omega⟩).val : ℝ) - ((v (Fin.succ j)).val : ℝ)))) := by
  classical
  let Weak : ℕ → Prop := fun k => ∃ v : Fin (k + 1) → Fin (N + 1), chainProp y k v
  have hfull : Weak N := ⟨(fun i : Fin (N + 1) => i), chainProp_full N y⟩
  let k0 : ℕ := Nat.find (p := Weak) ⟨N, hfull⟩
  have hmin : ∀ m : ℕ, m < k0 → ¬ Weak m := by
    intro m hm
    exact Nat.find_min (p := Weak) ⟨N, hfull⟩ hm
  have hk0 : Weak k0 := Nat.find_spec (p := Weak) ⟨N, hfull⟩
  rcases hk0 with ⟨v0, hv0⟩
  have hstrict : (∀ (j : Fin k0) (hj : j.val + 1 < k0),
        ((y (v0 (Fin.succ j)) - y (v0 (Fin.castSucc j))) /
            (((v0 (Fin.succ j)).val : ℝ) - ((v0 (Fin.castSucc j)).val : ℝ))) <
          ((y (v0 ⟨j.val + 2, by omega⟩) - y (v0 (Fin.succ j))) /
            (((v0 ⟨j.val + 2, by omega⟩).val : ℝ) - ((v0 (Fin.succ j)).val : ℝ)))) := by
    intro j hj
    by_contra hle0
    have hle1 : slope y (v0 (Fin.succ j)) (v0 (⟨j.val + 2, by omega⟩ : Fin (k0 + 1))) ≤
                slope y (v0 (Fin.castSucc j)) (v0 (Fin.succ j)) := by
      -- hle0 : ¬ (slope castSucc..succ < slope succ..(j.val+2))
      simpa [slope] using (le_of_not_gt hle0)
    have harg : v0 (Fin.succ (⟨j.val + 1, hj⟩ : Fin k0)) =
        v0 (⟨j.val + 2, by omega⟩ : Fin (k0 + 1)) := by
      congr 1
    have hle : slope y (v0 (Fin.succ j)) (v0 (Fin.succ (⟨j.val + 1, hj⟩ : Fin k0))) ≤
               slope y (v0 (Fin.castSucc j)) (v0 (Fin.succ j)) := by
      rw [harg]
      exact hle1
    rcases chainProp_del (k := k0) hv0 j hj hle with ⟨w, hw⟩
    have hless : k0 - 1 < k0 := by omega
    exact (hmin (k0 - 1) hless ⟨w, hw⟩)
  refine ⟨k0, v0, hv0.1, hv0.2.1, ?_, ?_, ?_⟩
  · intro j
    exact (hv0.2.2 j).1
  · intro j i hia hib
    exact (hv0.2.2 j).2 i hia hib
  · exact hstrict

end Commons.Geometry.LowerHull
