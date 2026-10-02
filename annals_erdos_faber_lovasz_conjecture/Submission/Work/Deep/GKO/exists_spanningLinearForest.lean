import Submission.Work.Deep.GKO.NarrowImports
import Submission.Work.Deep.GKO.Defs
import Submission.Work.Deep.GKO.spanningDefs
import Submission.Work.Deep.GKO.exists_spanningPath_subset
import Submission.Work.Deep.GKO.exists_linearForest_of_walks

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

open scoped BigOperators
open SimpleGraph

namespace Work.Deep.GKO

noncomputable section

variable {n : ℕ}

/-! ## A path of length at most three avoiding a vertex set -/

/-- **A path of length at most three avoiding a vertex set, inside a fixed vertex set.**

`U` is a vertex set containing `a` and `b`, and `X` a set of "forbidden" vertices; if `a` and
`b` have no common neighbour in `U \ X`, `a` is not adjacent to `b`, and each of `a`, `b` has
at least `εn` neighbours in `U \ X`, then `a` and `b` are joined by a path of length at most
three using only vertices of `U` and avoiding `X`. -/
theorem exists_shortPath {n : ℕ} (G : SimpleGraph (Fin n)) {p ε : ℝ}
    (hlr : LowerReg G p ε) (hεp : ε < p) (hε : 0 < ε)
    (U X : Finset (Fin n)) {a b : Fin n} (ha : a ∈ U) (hb : b ∈ U)
    (haX : a ∉ X) (hbX : b ∉ X) (hab : a ≠ b)
    (hnot : ¬ G.Adj a b)
    (hdisj : ∀ w, w ∈ U → w ∉ X → ¬ (G.Adj a w ∧ G.Adj b w))
    (hAsz : ε * (n : ℝ) ≤ (nbrIn G (U \ X) a : ℝ))
    (hBsz : ε * (n : ℝ) ≤ (nbrIn G (U \ X) b : ℝ)) :
    ∃ w : G.Walk a b, w.IsPath ∧ w.length ≤ 3 ∧ (∀ v ∈ w.support, v ∈ U) ∧
      (∀ v ∈ w.support, v ∉ X) := by
  classical
  set A : Finset (Fin n) := (U \ X).filter (fun w => G.Adj a w) with hA
  set B : Finset (Fin n) := (U \ X).filter (fun w => G.Adj b w) with hB
  have hmemA : ∀ y : Fin n, y ∈ A ↔ y ∈ U ∧ y ∉ X ∧ G.Adj a y := by
    intro y
    simp only [hA, Finset.mem_filter, Finset.mem_sdiff]
    tauto
  have hmemB : ∀ y : Fin n, y ∈ B ↔ y ∈ U ∧ y ∉ X ∧ G.Adj b y := by
    intro y
    simp only [hB, Finset.mem_filter, Finset.mem_sdiff]
    tauto
  have hAcard : (A.card : ℝ) = (nbrIn G (U \ X) a : ℝ) := by
    rw [hA, nbrIn_eq_filter_card]
  have hBcard : (B.card : ℝ) = (nbrIn G (U \ X) b : ℝ) := by
    rw [hB, nbrIn_eq_filter_card]
  have hAge : ε * (n : ℝ) ≤ (A.card : ℝ) := by rw [hAcard]; exact hAsz
  have hBge : ε * (n : ℝ) ≤ (B.card : ℝ) := by rw [hBcard]; exact hBsz
  have hdisjAB : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro w hwA hwB
    have h1 := (hmemA w).1 hwA
    have h2 := (hmemB w).1 hwB
    exact hdisj w h1.1 h1.2.1 ⟨h1.2.2, h2.2.2⟩
  have hreg := hlr A B hdisjAB hAge hBge
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (fun h => by subst h; exact Fin.elim0 a)
  have hApos : 0 < A.card := by
    have h1 : (0:ℝ) < ε * (n:ℝ) := by positivity
    exact_mod_cast (lt_of_lt_of_le h1 hAge)
  have hBpos : 0 < B.card := by
    have h1 : (0:ℝ) < ε * (n:ℝ) := by positivity
    exact_mod_cast (lt_of_lt_of_le h1 hBge)
  have hpos : 0 < (p - ε) * (A.card : ℝ) * (B.card : ℝ) := by
    have h1 : 0 < p - ε := sub_pos.mpr hεp
    positivity
  have hcross : 0 < crossEdges G A B := by
    have : (0:ℝ) < (crossEdges G A B : ℝ) := lt_of_lt_of_le hpos hreg
    exact_mod_cast this
  obtain ⟨u, w, huA, hwB, huw⟩ : ∃ u w : Fin n, u ∈ A ∧ w ∈ B ∧ G.Adj u w := by
    obtain ⟨p, hp⟩ := Finset.card_pos.mp hcross
    have hp' : (p.1 ∈ A ∧ p.2 ∈ B) ∧ G.Adj p.1 p.2 := by
      simpa [crossEdges] using hp
    exact ⟨p.1, p.2, hp'.1.1, hp'.1.2, hp'.2⟩
  have hAu := (hmemA u).1 huA
  have hBw := (hmemB w).1 hwB
  have hau : G.Adj a u := hAu.2.2
  have hwb : G.Adj w b := hBw.2.2.symm
  have huU : u ∈ U := hAu.1
  have hwU : w ∈ U := hBw.1
  have huX : u ∉ X := hAu.2.1
  have hwX : w ∉ X := hBw.2.1
  have hub : u ≠ b := fun h => hnot (h ▸ hau)
  have haw : a ≠ w := fun h => hnot (h.symm ▸ hwb)
  have hw_in : w ∉ (Walk.nil : G.Walk b b).support := by
    rw [Walk.support_nil]
    intro h
    exact hwb.ne (List.mem_singleton.mp h)
  have hu_in : u ∉ (Walk.cons hwb (Walk.nil : G.Walk b b)).support := by
    rw [Walk.support_cons, Walk.support_nil]
    intro h
    rcases List.mem_cons.mp h with h' | h'
    · exact huw.ne h'
    · exact hub (List.mem_singleton.mp h')
  have ha_in : a ∉ (Walk.cons huw (Walk.cons hwb (Walk.nil : G.Walk b b))).support := by
    rw [Walk.support_cons, Walk.support_cons, Walk.support_nil]
    intro h
    rcases List.mem_cons.mp h with h' | h'
    · exact hau.ne h'
    · rcases List.mem_cons.mp h' with h'' | h''
      · exact haw h''
      · exact hab (List.mem_singleton.mp h'')
  refine ⟨Walk.cons hau (Walk.cons huw (Walk.cons hwb (Walk.nil : G.Walk b b))),
    Walk.IsPath.cons (Walk.IsPath.cons (Walk.IsPath.cons Walk.IsPath.nil hw_in) hu_in) ha_in,
    ?_, ?_, ?_⟩
  · rw [Walk.length_cons, Walk.length_cons, Walk.length_cons, Walk.length_nil]
  · intro v hv
    rw [Walk.support_cons, Walk.support_cons, Walk.support_cons, Walk.support_nil] at hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl
    · exact ha
    · exact huU
    · exact hwU
    · exact hb
  · intro v hv
    rw [Walk.support_cons, Walk.support_cons, Walk.support_cons, Walk.support_nil] at hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl
    · exact haX
    · exact huX
    · exact hwX
    · exact hbX


/-! ## Short paths between two vertices with large neighbourhoods -/

lemma mem_support_cons_iff {G : SimpleGraph (Fin n)} {u v w : Fin n} {h : G.Adj u v}
    {p : G.Walk v w} {x : Fin n} :
    x ∈ (Walk.cons h p).support ↔ x = u ∨ x ∈ p.support := by
  rw [Walk.support_cons, List.mem_cons]

lemma mem_support_nil_iff {G : SimpleGraph (Fin n)} {u x : Fin n} :
    x ∈ (Walk.nil : G.Walk u u).support ↔ x = u := by
  rw [Walk.support_nil, List.mem_singleton]

/-- **A path of length at most three inside `U \ X`.**  If both endpoints have at least `εn`
neighbours in `U \ X`, then they are joined by a path of length at most three using only
vertices of `U \ X`. -/
lemma exists_shortPath' (G : SimpleGraph (Fin n)) {p ε : ℝ}
    (hlr : LowerReg G p ε) (hεp : ε < p) (hε : 0 < ε)
    (U X : Finset (Fin n)) {a b : Fin n} (haU : a ∈ U) (hbU : b ∈ U)
    (haX : a ∉ X) (hbX : b ∉ X) (hab : a ≠ b)
    (hAsz : ε * (n : ℝ) ≤ (nbrIn G (U \ X) a : ℝ))
    (hBsz : ε * (n : ℝ) ≤ (nbrIn G (U \ X) b : ℝ)) :
    ∃ P : G.Walk a b, P.IsPath ∧ P.length ≤ 3 ∧ (∀ v ∈ P.support, v ∈ U \ X) := by
  classical
  have haUX : a ∈ U \ X := Finset.mem_sdiff.mpr ⟨haU, haX⟩
  have hbUX : b ∈ U \ X := Finset.mem_sdiff.mpr ⟨hbU, hbX⟩
  by_cases hadj : G.Adj a b
  · refine ⟨Walk.cons hadj Walk.nil, ?_, ?_, ?_⟩
    · refine Walk.IsPath.cons Walk.IsPath.nil ?_
      rw [mem_support_nil_iff]
      exact hadj.ne
    · simp [Walk.length_cons]
    · intro v hv
      rw [mem_support_cons_iff] at hv
      rcases hv with h | h
      · rw [h]; exact haUX
      · rw [mem_support_nil_iff.mp h]; exact hbUX
  · by_cases hcom : ∃ y, y ∈ U ∧ y ∉ X ∧ G.Adj a y ∧ G.Adj b y
    · obtain ⟨y, hyU, hyX, hya, hyb⟩ := hcom
      have hyUX : y ∈ U \ X := Finset.mem_sdiff.mpr ⟨hyU, hyX⟩
      refine ⟨Walk.cons hya (Walk.cons hyb.symm (Walk.nil : G.Walk b b)), ?_, ?_, ?_⟩
      · refine Walk.IsPath.cons ?_ ?_
        · refine Walk.IsPath.cons ?_ ?_
          · exact Walk.IsPath.nil
          · rw [mem_support_nil_iff]
            exact fun h => hyb.ne h.symm
        · rw [mem_support_cons_iff, mem_support_nil_iff]
          rintro (h | h)
          · exact hya.ne h
          · exact hab h
      · simp [Walk.length_cons]
      · intro v hv
        rw [mem_support_cons_iff, mem_support_cons_iff, mem_support_nil_iff] at hv
        rcases hv with h | h | h
        · rw [h]; exact haUX
        · rw [h]; exact hyUX
        · rw [h]; exact hbUX
    · push_neg at hcom
      obtain ⟨P, hPpath, hPlen, hPU, hPX⟩ :=
        exists_shortPath G hlr hεp hε U X haU hbU haX hbX hab hadj
          (fun w hwU hwX h => hcom w hwU hwX h.1 h.2) hAsz hBsz
      exact ⟨P, hPpath, hPlen, fun v hv => Finset.mem_sdiff.mpr ⟨hPU v hv, hPX v hv⟩⟩

/-! ## Degree bookkeeping for the deletion of a few vertices -/

lemma nbrIn_le_nbrIn_sdiff_add (G : SimpleGraph (Fin n)) (U K : Finset (Fin n)) (v : Fin n) :
    nbrIn G U v ≤ nbrIn G (U \ K) v + K.card := by
  classical
  rw [nbrIn_eq_filter_card, nbrIn_eq_filter_card]
  have h : (U.filter (fun w => G.Adj v w)) ⊆ ((U \ K).filter (fun w => G.Adj v w)) ∪ K := by
    intro w hw
    rw [Finset.mem_filter] at hw
    by_cases hwK : w ∈ K
    · exact Finset.mem_union_right _ hwK
    · exact Finset.mem_union_left _
        (Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨hw.1, hwK⟩, hw.2⟩)
  calc (U.filter (fun w => G.Adj v w)).card
      ≤ (((U \ K).filter (fun w => G.Adj v w)) ∪ K).card := Finset.card_le_card h
    _ ≤ ((U \ K).filter (fun w => G.Adj v w)).card + K.card := Finset.card_union_le _ _

/-! ## Prepending to a `Fin`-indexed family -/

/-- `prepend x f : Fin (m+1) → α` is the family obtained from `f : Fin m → α` by putting
`x` in front. -/
def prepend {α : Sort*} {m : ℕ} (x : α) (f : Fin m → α) : Fin (m+1) → α :=
  fun i => Fin.cases x f i

@[simp] lemma prepend_zero {α : Sort*} {m : ℕ} (x : α) (f : Fin m → α) :
    prepend x f 0 = x := rfl

@[simp] lemma prepend_succ {α : Sort*} {m : ℕ} (x : α) (f : Fin m → α) (i : Fin m) :
    prepend x f i.succ = f i := rfl

/-- Dependent version of `prepend`: for a family of types `α` over `Fin (m+1)`, put `x : α 0`
in front of `f : (i : Fin m) → α i.succ`. -/
def prependD {m : ℕ} {α : Fin (m+1) → Sort*} (x : α 0) (f : (i : Fin m) → α i.succ) :
    (i : Fin (m+1)) → α i :=
  fun i => Fin.cases x f i

@[simp] lemma prependD_zero {m : ℕ} {α : Fin (m+1) → Sort*} (x : α 0)
    (f : (i : Fin m) → α i.succ) : prependD x f 0 = x := rfl

@[simp] lemma prependD_succ {m : ℕ} {α : Fin (m+1) → Sort*} (x : α 0)
    (f : (i : Fin m) → α i.succ) (i : Fin m) : prependD x f i.succ = f i := rfl

/-! ## The recursive construction of the path family -/

open Classical in
/-- **The recursive construction.**  Given `k` pairs of leaves in `L` inside a vertex set `U`,
build `k` vertex-disjoint paths covering `U` whose endpoints are `L`. -/
lemma exists_path_family (G : SimpleGraph (Fin n)) {p ε α : ℝ} (m : ℕ)
    (hlr : LowerReg G p ε) (hεp : ε ≤ p / 100) (hε : 0 < ε) (hm : 5 * (m : ℝ) ≤ α * (n : ℝ))
    (hα1 : 4 * α ≤ 1) (hεα : ε ≤ α / 100) (hεn : 1 ≤ ε * (n : ℝ)) :
    ∀ k : ℕ, 1 ≤ k → k ≤ m → ∀ (U L : Finset (Fin n)),
      L ⊆ U → L.card = 2 * k →
      (∀ v ∈ U, α * (n : ℝ) - 4 * ((m : ℝ) - (k : ℝ)) ≤ (nbrIn G U v : ℝ)) →
      (n : ℝ) - 4 * ((m : ℝ) - (k : ℝ)) ≤ (U.card : ℝ) →
      ∃ (a b : Fin k → Fin n) (w : ∀ i, G.Walk (a i) (b i)),
        (∀ i, (w i).IsPath) ∧ (∀ i, a i ≠ b i) ∧
        (∀ i j, i ≠ j → ∀ v, v ∈ (w i).support → v ∈ (w j).support → False) ∧
        (∀ v, (∃ i, v ∈ (w i).support) ↔ v ∈ U) ∧
        (∀ v, v ∈ L ↔ ∃ i, v = a i ∨ v = b i) ∧
        (∀ i, ∀ v ∈ (w i).support, v ∈ L → v = a i ∨ v = b i) := by
  intro k
  induction k with
  | zero => intro hk; omega
  | succ k ih =>
      intro hk hkm U L hLU hcard hdeg hsize
      rcases Nat.eq_zero_or_pos k with hk0 | hkpos
      · subst hk0
        obtain ⟨a, b, hab, hLab⟩ := Finset.card_eq_two.mp (by simpa using hcard : L.card = 2)
        have haL : a ∈ L := by rw [hLab]; exact Finset.mem_insert_self _ _
        have hbL : b ∈ L := by
          rw [hLab]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
        have haU : a ∈ U := hLU haL
        have hbU : b ∈ U := hLU hbL
        have hUpos : 0 < U.card := Finset.card_pos.mpr ⟨a, haU⟩
        have hUne : (0 : ℝ) < (U.card : ℝ) := by exact_mod_cast hUpos
        have hnn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        have hnpos : (0 : ℝ) < (n : ℝ) := by nlinarith [hεn, hε]
        have hUlen : (U.card : ℝ) ≤ (n : ℝ) := by
          have := Finset.card_le_univ U
          simp only [Finset.card_univ, Fintype.card_fin] at this
          exact_mod_cast this
        have hUlow : (n : ℝ) - 4 * ((m : ℝ) - 1) ≤ (U.card : ℝ) := by simpa using hsize
        have hm1 : ((m : ℝ) - 1) ≤ (m : ℝ) := by linarith
        have hαn : 0 < α * (n : ℝ) := by
          have h1 : 0 < ε * (n : ℝ) := by nlinarith [hεn]
          nlinarith [hεα, h1]
        -- lower regularity inside `U` with the relative parameter
        have hε'pos : 0 < ε * (n : ℝ) / (U.card : ℝ) := by positivity
        have hUge : (n : ℝ) - 4 * ((m : ℝ) - 1) ≤ (U.card : ℝ) := hUlow
        have hUbig : 3 * (n : ℝ) / 4 ≤ (U.card : ℝ) := by
          have h4 : 4 * ((m : ℝ) - 1) ≤ (n : ℝ) / 4 := by
            have hαn1 : α * (n : ℝ) ≤ (n : ℝ) / 4 := by
              nlinarith [hα1, hnn, hαn]
            have h4m : 4 * (m : ℝ) ≤ 4 * (α * (n : ℝ)) / 5 := by linarith
            linarith [hm1, h4m, hαn1]
          linarith
        have hε'ltp : ε * (n : ℝ) / (U.card : ℝ) < p := by
          have h1 : ε * (n : ℝ) / (U.card : ℝ) ≤ ε * 4 / 3 := by
            rw [div_le_iff₀ hUne]
            nlinarith [hε, hUbig, hnpos]
          have h2 : 2 * ε ≤ p := by nlinarith [hεp, hε]
          nlinarith [h1, h2, hε, hεp, hnn, hnpos]
        have hε'N : (ε * (n : ℝ) / (U.card : ℝ)) * (U.card : ℝ) = ε * (n : ℝ) := by
          field_simp
        have hε'8 : 8 * (ε * (n : ℝ) / (U.card : ℝ)) ≤ (α * (n : ℝ) - 4 * ((m : ℝ) - 1)) / (U.card : ℝ) := by
          rw [le_div_iff₀ hUne]
          have h8 : 8 * (ε * (n : ℝ)) ≤ α * (n : ℝ) / 5 := by
            nlinarith [hεα, hnn, hαn]
          calc 8 * (ε * (n : ℝ) / (U.card : ℝ)) * (U.card : ℝ) = 8 * (ε * (n : ℝ)) := by field_simp
            _ ≤ α * (n : ℝ) - 4 * (m : ℝ) := by
              have h4m : 4 * (m : ℝ) ≤ 4 * (α * (n : ℝ)) / 5 := by linarith
              linarith [h4m]
            _ ≤ α * (n : ℝ) - 4 * ((m : ℝ) - 1) := by linarith [hm1]
        have hMinOn : MinDegOn G U ((α * (n : ℝ) - 4 * ((m : ℝ) - 1)) / (U.card : ℝ)) := by
          intro v hv
          have h1 := hdeg v hv
          rw [div_mul_cancel₀ _ (ne_of_gt hUne)]
          simpa using h1
        have hlrOn : LowerRegOn G U p (ε * (n : ℝ) / (U.card : ℝ)) := by
          intro A B hAU hBU hdisj hA hB
          have hAcard : ε * (n : ℝ) ≤ (A.card : ℝ) := le_trans (le_of_eq hε'N.symm) hA
          have hBcard : ε * (n : ℝ) ≤ (B.card : ℝ) := le_trans (le_of_eq hε'N.symm) hB
          have hreg := hlr A B hdisj hAcard hBcard
          have hε'ge : ε ≤ ε * (n : ℝ) / (U.card : ℝ) := by
            rw [le_div_iff₀ hUne]
            have : ε * (U.card : ℝ) ≤ ε * (n : ℝ) := by
              exact mul_le_mul_of_nonneg_left hUlen (le_of_lt hε)
            linarith
          have hnn2 : (0 : ℝ) ≤ (A.card : ℝ) * (B.card : ℝ) := by positivity
          nlinarith [hreg, hε'ge, hnn2]
        obtain ⟨-, -, -, w, hwpath, hwsupp⟩ :=
          exists_spanningPath_subset G U hlrOn hε'ltp hε'pos (by rw [hε'N]; exact hεn) hε'8 hMinOn a b haU hbU hab
        refine ⟨fun _ => a, fun _ => b, fun _ => w, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro i; exact hwpath
        · intro i; exact hab
        · intro i j hij
          exact absurd (Fin.ext (by omega)) hij
        · intro v
          constructor
          · rintro ⟨i, hv⟩; exact (hwsupp v).1 (by simpa using hv)
          · intro hv; exact ⟨0, by simpa using (hwsupp v).2 hv⟩
        · intro v
          constructor
          · intro hv
            rw [hLab] at hv
            rcases Finset.mem_insert.mp hv with rfl | hv'
            · exact ⟨0, Or.inl rfl⟩
            · rw [Finset.mem_singleton] at hv'
              exact ⟨0, Or.inr hv'⟩
          · rintro ⟨i, h | h⟩
            · rw [h]; exact haL
            · rw [h]; exact hbL
        · intro i v hv hvL
          rw [hLab] at hvL
          rcases Finset.mem_insert.mp hvL with hva | hvL'
          · exact Or.inl hva
          · rw [Finset.mem_singleton] at hvL'
            exact Or.inr hvL'
      · -- peel off one pair and recurse
        have hdegk : ∀ v ∈ U, α * (n : ℝ) - 4 * ((m : ℝ) - ((k : ℝ) + 1)) ≤ (nbrIn G U v : ℝ) := by
          intro v hv
          have h1 := hdeg v hv
          rw [Nat.cast_add, Nat.cast_one] at h1
          exact h1
        have hsizek : (n : ℝ) - 4 * ((m : ℝ) - ((k : ℝ) + 1)) ≤ (U.card : ℝ) := by
          have h1 := hsize
          rw [Nat.cast_add, Nat.cast_one] at h1
          exact h1
        have hLpos : 0 < L.card := by omega
        obtain ⟨a, haL⟩ := Finset.card_pos.mp hLpos
        have herase_card : (L.erase a).card = 2 * (k+1) - 1 := by
          rw [Finset.card_erase_of_mem haL, hcard]
        have herase_pos : 0 < (L.erase a).card := by omega
        obtain ⟨b, hb⟩ := Finset.card_pos.mp herase_pos
        have hbne : b ≠ a := (Finset.mem_erase.mp hb).1
        have hbL : b ∈ L := Finset.mem_of_mem_erase hb
        have hab : a ≠ b := fun h => hbne h.symm
        set L' : Finset (Fin n) := (L.erase a).erase b with hL'def
        have hb_mem : b ∈ L.erase a := hb
        have hL'card : L'.card = 2 * k := by
          rw [hL'def, Finset.card_erase_of_mem hb_mem, herase_card]
          omega
        have hL'sub : L' ⊆ L := by
          intro x hx
          rw [hL'def] at hx
          exact Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hx)
        have haL' : a ∉ L' := by
          intro h
          rw [hL'def] at h
          exact (Finset.mem_erase.mp (Finset.mem_erase.mp h).2).1 rfl
        have hbL' : b ∉ L' := by
          intro h
          rw [hL'def] at h
          exact (Finset.mem_erase.mp h).1 rfl
        have haU : a ∈ U := hLU haL
        have hbU : b ∈ U := hLU hbL
        -- each of `a`, `b` has at least `ε n` neighbours in `U \ L'`
        have hcard'' : ((L'.card : ℕ) : ℝ) = 2 * (k : ℝ) := by rw [hL'card]; simp only [Nat.cast_mul, Nat.cast_ofNat]
        have hmk : ((m : ℝ) - ((k : ℝ) + 1)) ≤ (m : ℝ) := by
          have hkk : (0 : ℝ) ≤ (k : ℝ) + 1 := by positivity
          linarith
        have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
        have hm5 : 4 * (m : ℝ) ≤ 4 * (α * (n : ℝ)) / 5 := by
          have := hm; linarith
        have hεαn : ε * (n : ℝ) ≤ α * (n : ℝ) / (100 : ℝ) := by
          have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
          nlinarith [hεα, hn]
        have hεa : ε * (n : ℝ) ≤ (nbrIn G (U \ L') a : ℝ) := by
          have h1 := hdegk a haU
          have h5' : (nbrIn G U a : ℝ) ≤ (nbrIn G (U \ L') a : ℝ) + (L'.card : ℝ) := by
            exact_mod_cast nbrIn_le_nbrIn_sdiff_add G U L' a
          have h6 : α * (n : ℝ) - 4 * ((m : ℝ) - ((k : ℝ) + 1)) - 2 * (k : ℝ) ≤
              (nbrIn G (U \ L') a : ℝ) := by
            linarith [h1, h5', hcard'']
          have h9 : ε * (n : ℝ) ≤ α * (n : ℝ) - 4 * ((m : ℝ) - ((k : ℝ) + 1)) - 2 * (k : ℝ) := by
            nlinarith [hmk, hm5, hεαn, hk0]
          linarith
        have hεb : ε * (n : ℝ) ≤ (nbrIn G (U \ L') b : ℝ) := by
          have h1 := hdegk b hbU
          have h5' : (nbrIn G U b : ℝ) ≤ (nbrIn G (U \ L') b : ℝ) + (L'.card : ℝ) := by
            exact_mod_cast nbrIn_le_nbrIn_sdiff_add G U L' b
          have h6 : α * (n : ℝ) - 4 * ((m : ℝ) - ((k : ℝ) + 1)) - 2 * (k : ℝ) ≤
              (nbrIn G (U \ L') b : ℝ) := by
            linarith [h1, h5', hcard'']
          have h9 : ε * (n : ℝ) ≤ α * (n : ℝ) - 4 * ((m : ℝ) - ((k : ℝ) + 1)) - 2 * (k : ℝ) := by
            nlinarith [hmk, hm5, hεαn, hk0]
          linarith
        have hεp' : ε < p := by nlinarith [hεp, hε]
        -- find the short path joining `a` and `b` inside `U`, avoiding `L'`
        obtain ⟨P, hPpath, hPlen, hPUX⟩ :=
          exists_shortPath' G hlr hεp' hε U L' haU hbU haL' hbL' hab hεa hεb
        have hPU : ∀ v ∈ P.support, v ∈ U := fun v hv => (Finset.mem_sdiff.mp (hPUX v hv)).1
        have hPL' : ∀ v ∈ P.support, v ∉ L' := fun v hv => (Finset.mem_sdiff.mp (hPUX v hv)).2
        set U' : Finset (Fin n) := U \ P.support.toFinset with hU'def
        have hU'sub : U' ⊆ U := by rw [hU'def]; exact Finset.sdiff_subset
        have hPU' : ∀ v ∈ P.support, v ∉ U' := by
          intro v hv
          rw [hU'def, Finset.mem_sdiff]
          exact fun h => h.2 (by simpa using hv)
        have hL'U' : L' ⊆ U' := by
          intro x hx
          rw [hU'def, Finset.mem_sdiff]
          exact ⟨hLU (hL'sub hx), fun hxP => hPL' x (by simpa using hxP) hx⟩
        have hPcard : (P.support.toFinset.card : ℝ) ≤ 4 := by
          have h1 : (P.support.toFinset.card : ℕ) = P.support.length :=
            List.toFinset_card_of_nodup hPpath.support_nodup
          have h2 : (P.support.toFinset.card : ℝ) = (P.support.length : ℝ) := by
            rw [h1]
          have h3 : (P.support.length : ℝ) = (P.length : ℝ) + 1 := by
            rw [Walk.length_support]; push_cast; ring
          have h4 : (P.length : ℝ) ≤ 3 := by exact_mod_cast hPlen
          linarith
        have hmk' : ((m : ℝ) - (k : ℝ)) = ((m : ℝ) - ((k : ℝ) + 1)) + 1 := by ring
        have hdeg' : ∀ v ∈ U', α * (n : ℝ) - 4 * ((m : ℝ) - (k : ℝ)) ≤ (nbrIn G U' v : ℝ) := by
          intro v hv
          have hvU : v ∈ U := hU'sub hv
          have h1 := hdegk v hvU
          have h2 : (nbrIn G U v : ℝ) ≤ (nbrIn G U' v : ℝ) + (P.support.toFinset.card : ℝ) := by
            exact_mod_cast nbrIn_le_nbrIn_sdiff_add G U P.support.toFinset v
          have h3 : (nbrIn G U v : ℝ) - 4 ≤ (nbrIn G U' v : ℝ) := by linarith
          rw [hmk']
          linarith [h1, h3]
        have hsize' : (n : ℝ) - 4 * ((m : ℝ) - (k : ℝ)) ≤ (U'.card : ℝ) := by
          have h1 := hsizek
          have h2 : (U.card : ℝ) - (P.support.toFinset.card : ℝ) ≤ (U'.card : ℝ) := by
            rw [hU'def, Finset.card_sdiff]
            have hle : (P.support.toFinset ∩ U).card ≤ U.card :=
              Finset.card_le_card Finset.inter_subset_right
            rw [Nat.cast_sub hle]
            have h2' : ((P.support.toFinset ∩ U).card : ℝ) ≤ (P.support.toFinset.card : ℝ) := by
              exact_mod_cast Finset.card_le_card Finset.inter_subset_left
            linarith
          have h3 : (U.card : ℝ) - 4 ≤ (U'.card : ℝ) := by linarith
          rw [hmk']
          linarith [h1, h3]
        obtain ⟨a', b', w', hpath', hend', hdisj', hcov', hLend', havoid'⟩ :=
          ih hkpos (by omega) U' L' hL'U' hL'card hdeg' hsize'
        refine ⟨prepend a a', prepend b b',
          prependD (α := fun i => G.Walk (prepend a a' i) (prepend b b' i))
            (P.copy (prepend_zero a a').symm (prepend_zero b b').symm)
            (fun j => (w' j).copy (prepend_succ a a' j).symm (prepend_succ b b' j).symm),
          ?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro i
          refine Fin.cases ?_ ?_ i
          · rw [prependD_zero, Walk.isPath_copy]; exact hPpath
          · intro j
            rw [prependD_succ, Walk.isPath_copy]; exact hpath' j
        · intro i
          refine Fin.cases ?_ ?_ i
          · rw [prepend_zero]; exact hab
          · intro j
            rw [prepend_succ]; exact hend' j
        · intro i j hij v hv hw
          revert hv hw hij
          refine Fin.cases ?_ ?_ i
          · intro hij hv hw
            revert hv hw hij
            refine Fin.cases ?_ ?_ j
            · intro hij hv hw
              exact absurd rfl hij
            · intro j' hij hv hw
              rw [prependD_zero, Walk.support_copy] at hv
              rw [prependD_succ, Walk.support_copy] at hw
              exact hPU' v hv ((hcov' v).1 ⟨j', hw⟩)
          · intro i' hij hv hw
            revert hv hw hij
            refine Fin.cases ?_ ?_ j
            · intro hij hv hw
              rw [prependD_succ, Walk.support_copy] at hv
              rw [prependD_zero, Walk.support_copy] at hw
              exact hPU' v hw ((hcov' v).1 ⟨i', hv⟩)
            · intro j' hij hv hw
              rw [prependD_succ, Walk.support_copy] at hv
              rw [prependD_succ, Walk.support_copy] at hw
              exact hdisj' i' j' (by simpa using hij) v hv hw
        · intro v
          constructor
          · rintro ⟨i, hv⟩
            revert hv
            refine Fin.cases ?_ ?_ i
            · intro hv
              rw [prependD_zero, Walk.support_copy] at hv
              exact hPU v hv
            · intro j hv
              rw [prependD_succ, Walk.support_copy] at hv
              exact hU'sub ((hcov' v).1 ⟨j, hv⟩)
          · intro hv
            by_cases hvU' : v ∈ U'
            · obtain ⟨j, hj⟩ := (hcov' v).2 hvU'
              exact ⟨Fin.succ j, by
                rw [prependD_succ, Walk.support_copy]
                exact hj⟩
            · have hvP : v ∈ P.support := by
                by_contra hcon
                exact hvU' (by
                  rw [hU'def, Finset.mem_sdiff]
                  exact ⟨hv, fun h => hcon (by simpa using h)⟩)
              exact ⟨0, by
                rw [prependD_zero, Walk.support_copy]
                exact hvP⟩
        · intro v
          constructor
          · intro hv
            by_cases hvL' : v ∈ L'
            · obtain ⟨j, hj⟩ := (hLend' v).1 hvL'
              exact ⟨Fin.succ j, by
                rw [prepend_succ]
                exact hj⟩
            · have hvab : v = a ∨ v = b := by
                rcases eq_or_ne v a with hva | hva
                · exact Or.inl hva
                · by_cases hvb : v = b
                  · exact Or.inr hvb
                  · exfalso
                    exact hvL' (Finset.mem_erase.mpr ⟨hvb,
                      Finset.mem_erase.mpr ⟨hva, hv⟩⟩)
              rcases hvab with rfl | rfl
              · exact ⟨0, Or.inl (by rw [prepend_zero])⟩
              · exact ⟨0, Or.inr (by rw [prepend_zero])⟩
          · rintro ⟨i, h | h⟩ <;> revert h
            · refine Fin.cases ?_ ?_ i
              · intro h
                rw [prepend_zero] at h
                rw [h]; exact haL
              · intro j h
                rw [prepend_succ] at h
                exact hL'sub ((hLend' v).2 ⟨j, Or.inl h⟩)
            · refine Fin.cases ?_ ?_ i
              · intro h
                rw [prepend_zero] at h
                rw [h]; exact hbL
              · intro j h
                rw [prepend_succ] at h
                exact hL'sub ((hLend' v).2 ⟨j, Or.inr h⟩)
        · intro i v hv hvL
          revert hv hvL
          refine Fin.cases ?_ ?_ i
          · intro hv hvL
            rw [prependD_zero, Walk.support_copy] at hv
            by_cases hva : v = a
            · exact Or.inl hva
            · right
              by_cases hvb : v = b
              · exact hvb
              · exfalso
                exact hPL' v hv (Finset.mem_erase.mpr ⟨hvb, Finset.mem_erase.mpr ⟨hva, hvL⟩⟩)
          · intro j hv hvL
            rw [prependD_succ, Walk.support_copy] at hv
            have hvU' : v ∈ U' := (hcov' v).1 ⟨j, hv⟩
            have hvL' : v ∈ L' := by
              by_contra hvL''
              rcases eq_or_ne v a with hva | hva
              · rw [hva] at hvU'
                exact hPU' a (Walk.start_mem_support P) hvU'
              · by_cases hvb : v = b
                · rw [hvb] at hvU'
                  exact hPU' b (Walk.end_mem_support P) hvU'
                · exact hvL'' (Finset.mem_erase.mpr ⟨hvb,
                    Finset.mem_erase.mpr ⟨hva, hvL⟩⟩)
            exact havoid' j v hv hvL'


/-! ## The spanning-linkage lemma -/

/-- **Spanning linkage** (Lemma 3.3 / `lem:pathcontrol` of Glock–Kühn–Osthus): if `G` is lower `(p,ε)`-regular with minimum degree at least `αn` (`ε ≪ α ≪ p`) and `L ⊆ V(G)` has even size with `2 ≤ |L| ≤ 2αn/5`, then there is a spanning linear forest in `G` whose set of leaves is exactly `L`.  Equivalently, the vertices of `L` can be paired up into `|L|/2` pairs and joined by vertex-disjoint paths covering all of `V(G)`.

The source pairs the vertices of `L`, joins all but one of the pairs by paths of length at most three (using lower regularity between the two neighbourhoods, each of size `≥ αn/5 − n`), and then takes a spanning path in the remaining graph, which still has minimum degree `≥ αn/5` and is lower regular with parameter `ε'` proportional to `ε`; `Work.Deep.GKO.exists_spanningPath_of_lowerReg` supplies that path. -/
theorem exists_spanningLinearForest {n : ℕ} (G : SimpleGraph (Fin n)) {p ε α : ℝ}
    (hlr : Work.Deep.GKO.LowerReg G p ε) (hα : 0 < α) (hα1 : α ≤ 1 / 10)
    (hεα : ε ≤ α / 100) (hεp : ε ≤ p / 100) (hεn : 1 ≤ ε * (n : ℝ))
    (hdeg : α * (n : ℝ) ≤ (Work.Deep.GKO.minDeg G : ℝ))
    (L : Finset (Fin n)) (hLeven : Even L.card) (hL2 : 2 ≤ L.card)
    (hL : (L.card : ℝ) ≤ 2 * α * (n : ℝ) / 5) :
    ∃ F : SimpleGraph (Fin n), F ≤ G ∧ Work.Deep.GKO.IsSpanningLinearForestWithLeaves F L := by
  classical
  -- Write `L.card = 2 * m` and record the two numeric consequences of `hL`.
  obtain ⟨m, hm2⟩ := hLeven
  have hcard2 : L.card = 2 * m := by omega
  have hm1 : 1 ≤ m := by omega
  have hnR : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hm5 : 5 * (m : ℝ) ≤ α * (n : ℝ) := by
    rw [hm2] at hL
    simp only [Nat.cast_add] at hL
    field_simp at hL
    linarith
  have hα1' : 4 * α ≤ 1 := by linarith
  have hεpos : 0 < ε := by
    by_contra hcon
    push_neg at hcon
    have hle : ε * (n : ℝ) ≤ 0 := by nlinarith [hnR]
    linarith
  -- The invariants of the recursion at `k = m`, `U = univ`.
  have hncard : ∀ v : Fin n, nbrIn G Finset.univ v = Nat.card (G.neighborSet v) := by
    intro v
    rw [nbrIn]
    simp only [Finset.coe_univ, Set.inter_univ]
    exact Eq.symm (Nat.card_coe_set_eq _)
  have hmin : ∀ v : Fin n, (minDeg G : ℝ) ≤ (Nat.card (G.neighborSet v) : ℝ) := by
    intro v
    have hmem : Nat.card (G.neighborSet v) ∈
        Set.range (fun v : Fin n => Nat.card (G.neighborSet v)) := ⟨v, rfl⟩
    have h := Nat.sInf_le hmem
    exact_mod_cast h
  have hdeginv : ∀ v ∈ (Finset.univ : Finset (Fin n)),
      α * (n : ℝ) - 4 * ((m : ℝ) - (m : ℝ)) ≤ (nbrIn G Finset.univ v : ℝ) := by
    intro v _
    rw [hncard v]
    have h0 : α * (n : ℝ) - 4 * ((m : ℝ) - (m : ℝ)) = α * (n : ℝ) := by ring
    rw [h0]
    exact le_trans hdeg (hmin v)
  have hunivcard : (n : ℝ) - 4 * ((m : ℝ) - (m : ℝ)) ≤
      ((Finset.univ : Finset (Fin n)).card : ℝ) := by
    have hucard : (Finset.univ : Finset (Fin n)).card = n := by simp
    have h0 : (m : ℝ) - (m : ℝ) = 0 := sub_self (m : ℝ)
    rw [h0, hucard]
    norm_num
  -- Run the recursion at `k = m` on the whole vertex set.
  obtain ⟨a, b, w, hpath, hend, hdisj, hcov, hLend, _⟩ :=
    exists_path_family G m hlr hεp hεpos hm5 hα1' hεα hεn m hm1 (le_refl m) Finset.univ L
      (Finset.subset_univ L) hcard2 hdeginv hunivcard
  -- Assemble the union of the paths into a spanning linear forest.
  refine exists_linearForest_of_walks G L a b w hpath hend hdisj ?_ hLend
  intro v
  exact (hcov v).2 (Finset.mem_univ v)

end
end Work.Deep.GKO
