/-
  Subproject WilE9G — G4a: normalising the list of disjuncts of a semi-Pfaffian set.

  A `Basic` with no equations and no inequalities holds at every point and has degree `0`
  (`atomDeg Q = Q.totalDegree + 1 ≥ 1`).  Hence the *number of disjuncts* of a `SemiPf` set is
  NOT bounded by its degree: a set equal to the whole cube can be presented with an empty basic
  repeated arbitrarily often.  This is FIX-3 of the design review: before any length bound of the
  form "`basics.length ≤ b X.deg`" one must collapse the presentation.

  `semiPf_normalize X` replaces the list of disjuncts by the single empty disjunct exactly when
  some disjunct is empty (in which case the set is the whole cube); it preserves the set, never
  increases the degree, and its list of disjuncts has length `≤ max 1 X.deg`.  `stratum_normalize`
  and `effStratum_normalize` do the same for the `X` underlying a stratum, keeping `Good` (which
  only sees `X.set`, `X.c` and the equations).
-/
import Submission.Work.WilE9G.Basic

set_option autoImplicit false
noncomputable section
open Classical Topology Filter MeasureTheory
namespace Work.WilE9G
open WilkiesDesign WilkiesDesign.E Work.WilE9.Sharp

/-! ## 1. The empty basic -/

/-- The basic set with no equations and no inequalities: it holds everywhere. -/
def Basic.unit {k r : ℕ} : Basic k r := ⟨[], []⟩

theorem Basic.deg_unit (k r : ℕ) : (Basic.unit : Basic k r).deg = 0 := rfl

theorem Basic.holds_unit {k r : ℕ} (c : EAChain k r) (x : Fin k → ℝ) :
    (Basic.unit : Basic k r).holds c x := by
  simp [Basic.holds, Basic.unit]

/-- A basic has degree zero exactly when it has no equations and no inequalities. -/
theorem Basic.deg_eq_zero_iff {k r : ℕ} {B : Basic k r} :
    B.deg = 0 ↔ B.eqs = [] ∧ B.pos = [] := by
  constructor
  · intro h
    have h' : ∀ Q ∈ B.eqs ++ B.pos, atomDeg Q = 0 := fun Q hQ =>
      List.sum_eq_zero_iff.mp h (atomDeg Q) (List.mem_map_of_mem hQ)
    have hnil : B.eqs ++ B.pos = [] := by
      by_contra hne
      obtain ⟨Q, hQ⟩ := List.exists_mem_of_ne_nil _ hne
      have hpos : 0 < atomDeg Q := Nat.lt_succ_of_le (Nat.zero_le _)
      exact absurd (h' Q hQ) (by omega)
    simpa using hnil
  · rintro ⟨h1, h2⟩
    simp only [Basic.deg]
    rw [h1, h2]
    rfl

theorem Basic.holds_of_deg_zero {k r : ℕ} {B : Basic k r} (h : B.deg = 0) (c : EAChain k r)
    (x : Fin k → ℝ) : B.holds c x := by
  obtain ⟨h1, h2⟩ := Basic.deg_eq_zero_iff.mp h
  simp only [Basic.holds]
  rw [h1, h2]
  exact ⟨fun f hf => absurd hf List.not_mem_nil, fun g hg => absurd hg List.not_mem_nil⟩

/-! ## 2. A set with an empty disjunct is the whole cube -/

theorem SemiPf.set_eq_cubeC_of_deg_zero {k : ℕ} (X : SemiPf k)
    (h : ∃ B ∈ X.basics, B.deg = 0) : X.set = cubeC k := by
  obtain ⟨B, hB, hdeg⟩ := h
  ext x
  exact ⟨fun hx => hx.1, fun hx => ⟨hx, B, hB, Basic.holds_of_deg_zero hdeg X.c x⟩⟩

/-- **The disjunct bound for a presentation without an empty disjunct.**  If every disjunct has
positive degree then their number is at most the degree. -/
theorem semiPf_basics_length_le_deg_of_no_empty {k : ℕ} (X : SemiPf k)
    (h : ∀ B ∈ X.basics, B.deg ≠ 0) : X.basics.length ≤ max 1 X.deg := by
  have hpos : ∀ B ∈ X.basics, 1 ≤ B.deg := by
    intro B hB
    rcases Nat.eq_zero_or_pos B.deg with h0 | h0
    · exact absurd h0 (h B hB)
    · exact h0
  have hlen : (X.basics.map Basic.deg).length ≤ (X.basics.map Basic.deg).sum :=
    List.length_le_sum_of_one_le _ (by
      intro i hi
      obtain ⟨B, hB, rfl⟩ := List.mem_map.mp hi
      exact hpos B hB)
  rw [List.length_map] at hlen
  have hsum : (X.basics.map Basic.deg).sum = X.deg := rfl
  rw [hsum] at hlen
  exact le_trans hlen (le_max_right _ _)

/-! ## 3. The normalised presentation of a semi-Pfaffian set -/

/-- The normalised presentation of a semi-Pfaffian set: if some disjunct is empty, the set is the
whole cube and we keep a single empty disjunct with the *same* chain and number of chain
functions; otherwise the presentation is unchanged. -/
def semiPf_normalize {k : ℕ} (X : SemiPf k) : SemiPf k :=
  if _h : ∃ B ∈ X.basics, B.deg = 0 then ⟨X.r, X.c, [Basic.unit]⟩ else X

theorem semiPf_normalize_of_pos {k : ℕ} (X : SemiPf k) (h : ∃ B ∈ X.basics, B.deg = 0) :
    semiPf_normalize X = ⟨X.r, X.c, [Basic.unit]⟩ := dif_pos h

theorem semiPf_normalize_of_neg {k : ℕ} (X : SemiPf k) (h : ¬ ∃ B ∈ X.basics, B.deg = 0) :
    semiPf_normalize X = X := dif_neg h

@[simp] theorem semiPf_normalize_r {k : ℕ} (X : SemiPf k) : (semiPf_normalize X).r = X.r := by
  unfold semiPf_normalize
  split_ifs <;> rfl

/-- The chain of `semiPf_normalize X` is the chain of `X`: `semiPf_normalize_of_pos` and
`semiPf_normalize_of_neg` are the two case splits under which this is visible. -/
theorem semiPf_normalize_eq_self_or_singleton {k : ℕ} (X : SemiPf k) :
    semiPf_normalize X = ⟨X.r, X.c, [Basic.unit]⟩ ∨ semiPf_normalize X = X := by
  by_cases h : ∃ B ∈ X.basics, B.deg = 0
  · exact Or.inl (semiPf_normalize_of_pos X h)
  · exact Or.inr (semiPf_normalize_of_neg X h)

@[simp] theorem semiPf_normalize_fmt {k : ℕ} (X : SemiPf k) :
    (semiPf_normalize X).fmt = X.fmt := by
  unfold semiPf_normalize
  split_ifs <;> rfl

theorem semiPf_normalize_singleton_set {k : ℕ} (X : SemiPf k)
    (h : ∃ B ∈ X.basics, B.deg = 0) :
    (⟨X.r, X.c, [Basic.unit]⟩ : SemiPf k).set = X.set := by
  rw [SemiPf.set_eq_cubeC_of_deg_zero X h]
  ext x
  exact ⟨fun hx => hx.1, fun hx => ⟨hx, Basic.unit, List.mem_singleton_self _,
    Basic.holds_unit X.c x⟩⟩

theorem semiPf_normalize_singleton_deg {k : ℕ} (X : SemiPf k) :
    (⟨X.r, X.c, [Basic.unit]⟩ : SemiPf k).deg = 0 := by
  simp [SemiPf.deg, Basic.deg, Basic.unit]

@[simp] theorem semiPf_normalize_set {k : ℕ} (X : SemiPf k) :
    (semiPf_normalize X).set = X.set := by
  by_cases h : ∃ B ∈ X.basics, B.deg = 0
  · rw [semiPf_normalize_of_pos X h]; exact semiPf_normalize_singleton_set X h
  · rw [semiPf_normalize_of_neg X h]

theorem semiPf_normalize_deg_le {k : ℕ} (X : SemiPf k) :
    (semiPf_normalize X).deg ≤ X.deg := by
  by_cases h : ∃ B ∈ X.basics, B.deg = 0
  · rw [semiPf_normalize_of_pos X h, semiPf_normalize_singleton_deg X]
    exact Nat.zero_le _
  · rw [semiPf_normalize_of_neg X h]

/-- **The disjunct bound.**  After normalisation the number of disjuncts is at most the degree
(or `1`, in the degenerate case of the whole cube). -/
theorem semiPf_normalize_basics_length_le {k : ℕ} (X : SemiPf k) :
    (semiPf_normalize X).basics.length ≤ max 1 X.deg := by
  by_cases h : ∃ B ∈ X.basics, B.deg = 0
  · rw [semiPf_normalize_of_pos X h]; simp [Basic.unit]
  · rw [semiPf_normalize_of_neg X h]
    exact semiPf_basics_length_le_deg_of_no_empty X (fun B hB h0 => h ⟨B, hB, h0⟩)

/-! ## 4. The same normalisation for the `X` underlying a stratum -/

/-- Normalise the `X` of a stratum; `Good` only sees `X.set`, `X.c` and the equations, so it is
preserved. -/
def stratum_normalize {p q : ℕ} (S : Stratum p q) : Stratum p q :=
  if _h : ∃ B ∈ S.X.basics, B.deg = 0 then
    ⟨⟨S.X.r, S.X.c, [Basic.unit]⟩, S.j, S.h⟩ else S

theorem stratum_normalize_of_pos {p q : ℕ} (S : Stratum p q)
    (h : ∃ B ∈ S.X.basics, B.deg = 0) :
    stratum_normalize S = ⟨⟨S.X.r, S.X.c, [Basic.unit]⟩, S.j, S.h⟩ := dif_pos h

theorem stratum_normalize_of_neg {p q : ℕ} (S : Stratum p q)
    (h : ¬ ∃ B ∈ S.X.basics, B.deg = 0) : stratum_normalize S = S := dif_neg h

@[simp] theorem stratum_normalize_set {p q : ℕ} (S : Stratum p q) :
    (stratum_normalize S).X.set = S.X.set := by
  by_cases h : ∃ B ∈ S.X.basics, B.deg = 0
  · rw [stratum_normalize_of_pos S h]; exact semiPf_normalize_singleton_set S.X h
  · rw [stratum_normalize_of_neg S h]

theorem stratum_normalize_good {p q : ℕ} {S : Stratum p q} (hS : S.Good) :
    (stratum_normalize S).Good := by
  by_cases h : ∃ B ∈ S.X.basics, B.deg = 0
  · rw [stratum_normalize_of_pos S h]
    intro z hz
    rw [semiPf_normalize_singleton_set S.X h] at hz ⊢
    exact hS z hz
  · rw [stratum_normalize_of_neg S h]; exact hS

@[simp] theorem stratum_normalize_fmt {p q : ℕ} (S : Stratum p q) :
    (stratum_normalize S).X.fmt = S.X.fmt := by
  by_cases h : ∃ B ∈ S.X.basics, B.deg = 0
  · rw [stratum_normalize_of_pos S h]
    rfl
  · rw [stratum_normalize_of_neg S h]

theorem stratum_normalize_deg_le {p q : ℕ} (S : Stratum p q) :
    (stratum_normalize S).deg ≤ S.deg := by
  by_cases h : ∃ B ∈ S.X.basics, B.deg = 0
  · rw [stratum_normalize_of_pos S h]
    simp only [Stratum.deg, semiPf_normalize_singleton_deg]
    exact Nat.add_le_add_right (Nat.zero_le _) _
  · rw [stratum_normalize_of_neg S h]

theorem stratum_normalize_basics_length_le {p q : ℕ} (S : Stratum p q) :
    (stratum_normalize S).X.basics.length ≤ max 1 S.X.deg := by
  by_cases h : ∃ B ∈ S.X.basics, B.deg = 0
  · rw [stratum_normalize_of_pos S h]; simp [Basic.unit]
  · rw [stratum_normalize_of_neg S h]
    exact semiPf_basics_length_le_deg_of_no_empty S.X (fun B hB h0 => h ⟨B, hB, h0⟩)

/-- An `EffStratum`'s `X` normalised: the same collapse, in the `(n, 1+m)` split of E9. -/
def effStratum_normalize {n m : ℕ} (E : EffStratum n m) : EffStratum n m :=
  if _h : ∃ B ∈ E.X.basics, B.deg = 0 then ⟨⟨E.X.r, E.X.c, [Basic.unit]⟩, E.h⟩ else E

theorem effStratum_normalize_of_pos {n m : ℕ} (E : EffStratum n m)
    (h : ∃ B ∈ E.X.basics, B.deg = 0) :
    effStratum_normalize E = ⟨⟨E.X.r, E.X.c, [Basic.unit]⟩, E.h⟩ := dif_pos h

theorem effStratum_normalize_of_neg {n m : ℕ} (E : EffStratum n m)
    (h : ¬ ∃ B ∈ E.X.basics, B.deg = 0) : effStratum_normalize E = E := dif_neg h

@[simp] theorem effStratum_normalize_set {n m : ℕ} (E : EffStratum n m) :
    (effStratum_normalize E).X.set = E.X.set := by
  by_cases h : ∃ B ∈ E.X.basics, B.deg = 0
  · rw [effStratum_normalize_of_pos E h]; exact semiPf_normalize_singleton_set E.X h
  · rw [effStratum_normalize_of_neg E h]

theorem effStratum_normalize_good {n m : ℕ} {E : EffStratum n m} (hE : E.Good) :
    (effStratum_normalize E).Good := by
  by_cases h : ∃ B ∈ E.X.basics, B.deg = 0
  · rw [effStratum_normalize_of_pos E h]
    intro z hz
    rw [semiPf_normalize_singleton_set E.X h] at hz ⊢
    exact hE z hz
  · rw [effStratum_normalize_of_neg E h]; exact hE

theorem effStratum_normalize_deg_le {n m : ℕ} (E : EffStratum n m) :
    (effStratum_normalize E).deg ≤ E.deg := by
  by_cases h : ∃ B ∈ E.X.basics, B.deg = 0
  · rw [effStratum_normalize_of_pos E h]
    simp only [EffStratum.deg, semiPf_normalize_singleton_deg]
    exact Nat.add_le_add_right (Nat.zero_le _) _
  · rw [effStratum_normalize_of_neg E h]

theorem effStratum_normalize_basics_length_le {n m : ℕ} (E : EffStratum n m) :
    (effStratum_normalize E).X.basics.length ≤ max 1 E.X.deg := by
  by_cases h : ∃ B ∈ E.X.basics, B.deg = 0
  · rw [effStratum_normalize_of_pos E h]; simp [Basic.unit]
  · rw [effStratum_normalize_of_neg E h]
    exact semiPf_basics_length_le_deg_of_no_empty E.X (fun B hB h0 => h ⟨B, hB, h0⟩)

theorem effStratum_normalize_fmt {n m : ℕ} (E : EffStratum n m) :
    (effStratum_normalize E).X.fmt = E.X.fmt := by
  unfold effStratum_normalize
  split_ifs <;> rfl

end Work.WilE9G
