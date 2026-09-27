import Mathlib
import Submission.Work.EQ.FanTri.fan_split_defs

namespace Work.EQ.FanTri

open Work.EQ

noncomputable section
open Classical

/-! ## Basic facts about `takeWhile`/`dropWhile` on `List Bool` -/

/-- `takeWhile (fun c => c)` keeps a block of `true`s. -/
lemma takeWhile_id_replicate (u : List Bool) :
    u.takeWhile (fun c => c) = List.replicate (u.takeWhile (fun c => c)).length true := by
  induction u with
  | nil => rfl
  | cons c u ih =>
      cases c with
      | false =>
          rw [List.takeWhile_cons_of_neg (by simp)]
          simp
      | true =>
          rw [List.takeWhile_cons_of_pos (by simp), ih]
          simp [List.replicate_succ]

/-- The first letter of `u.dropWhile (fun c => c)` (when nonempty) is `false`. -/
lemma dropWhile_id_get (u : List Bool) (h : 0 < (u.dropWhile (fun c => c)).length) :
    (u.dropWhile (fun c => c)).get ⟨0, h⟩ = false := by
  have := List.dropWhile_get_zero_not (p := fun c : Bool => c) u h
  simpa using this

/-- The walk of `u.dropWhile (fun c => c)` (when nonempty) starts by going to state `1`. -/
lemma wstate_dropWhile_one (u : List Bool) (h : u.dropWhile (fun c => c) ≠ []) :
    wstate (u.dropWhile (fun c => c)) 1 = 1 := by
  have hlen : 0 < (u.dropWhile (fun c => c)).length := List.length_pos_iff.mpr h
  rw [wstate_succ (u := u.dropWhile (fun c => c)) (t := 0) hlen, wstate_zero,
    dropWhile_id_get u hlen]
  rfl

/-! ## Facts about `tripLen` -/

/-- A trip does not return to `0` before its last letter. -/
lemma wstate_lt_tripLen_ne_zero (r : List Bool) {t : ℕ} (h1 : 1 ≤ t) (h2 : t < tripLen r) :
    wstate r t ≠ 0 := by
  intro hc
  by_cases hret : ∃ s, 1 ≤ s ∧ wstate r s = 0
  · have ht : tripLen r = Nat.find hret := by simp [tripLen, dite_eq_left hret]
    rw [ht] at h2
    exact Nat.find_min hret h2 ⟨h1, hc⟩
  · exact hret ⟨t, h1, hc⟩

/-- `tripLen r` is either a genuine return time of the walk of `r`, or the whole length. -/
lemma wstate_tripLen_eq_zero_or (r : List Bool) :
    wstate r (tripLen r) = 0 ∨ tripLen r = r.length := by
  by_cases hret : ∃ s, 1 ≤ s ∧ wstate r s = 0
  · left
    have ht : tripLen r = Nat.find hret := by simp [tripLen, dite_eq_left hret]
    rw [ht]; exact (Nat.find_spec hret).2
  · right
    simp [tripLen, dite_eq_right hret]

/-! ## `asm` of nonempty trips -/

lemma asm_cons_eq (g : ℕ) (gs : List ℕ) (τ : List Bool) (ts : List (List Bool)) :
    asm (g :: gs) (τ :: ts) = List.replicate g true ++ τ ++ asm gs ts := rfl

lemma append_ne_nil {τ x y : List Bool} (h : τ ≠ []) : x ++ τ ++ y ≠ [] := by
  intro hc
  have hl := congrArg List.length hc
  have hτ : 0 < τ.length := List.length_pos_iff.mpr h
  simp only [List.length_append, List.length_nil] at hl
  omega

lemma asm_ne_nil {a : List ℕ} {σ : List (List Bool)} (ha : a ≠ []) (hσ : σ ≠ [])
    (htrip : ∀ τ ∈ σ, τ ≠ []) : asm a σ ≠ [] := by
  cases a with
  | nil => exact absurd rfl ha
  | cons g gs =>
      cases σ with
      | nil => exact absurd rfl hσ
      | cons τ ts =>
          rw [asm_cons_eq]
          exact append_ne_nil (htrip τ (by simp))

/-- If every trip of `σ` starts with a non-stationary step then every trip is nonempty. -/
lemma trips_ne_nil {σ : List (List Bool)}
    (h : ∀ (i : ℕ) (τ : List Bool), σ[i]? = some τ → wstate τ 1 ≠ 0) :
    ∀ τ ∈ σ, τ ≠ [] := by
  intro τ hτ hnil
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hτ
  subst hnil
  exact (h i [] hi) (by simp [wstate])

/-! ## The specification of `decomp` -/

theorem decomp_spec (u : List Bool) :
    Work.EQ.FanTri.DecSpec u (Work.EQ.FanTri.decomp u).1 (Work.EQ.FanTri.decomp u).2 := by
  suffices h : ∀ n (u : List Bool), u.length ≤ n →
      DecSpec u (decomp u).1 (decomp u).2 from h u.length u le_rfl
  intro n
  induction n with
  | zero =>
      intro u hu
      have hu0 : u = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp hu)
      subst hu0
      rw [decomp.eq_def]
      simp [DecSpec, asm]
  | succ n ih =>
      intro u hu
      rw [decomp.eq_def]
      by_cases hR : List.dropWhile (fun c => c) u = []
      · simp only [hR, dite_true]
        have hu' : u.takeWhile (fun c => c) = u := by
          have h := List.takeWhile_append_dropWhile (p := fun c => c) (l := u)
          rw [hR, List.append_nil] at h
          exact h
        refine ⟨by simp, ?_, ?_, ?_, ?_, ?_⟩
        · show u = asm [(List.takeWhile (fun c => c) u).length] []
          rw [show asm [(List.takeWhile (fun c => c) u).length] []
                = List.replicate (List.takeWhile (fun c => c) u).length true from rfl,
            ← takeWhile_id_replicate u, hu']
        · intro i τ hmem; simp at hmem
        · intro i τ hmem; simp at hmem
        · intro i τ hmem; simp at hmem
        · intro i τ g' hmem; simp at hmem
      · simp only [hR, dite_false]
        set r := List.dropWhile (fun c => c) u with _hr
        set g := (List.takeWhile (fun c => c) u).length with _hg
        set l := tripLen r with hl
        set d := decomp (List.drop l r) with _hd
        have hR' : r ≠ [] := hR
        have hvlen : (List.drop l r).length ≤ n := by
          rw [List.length_drop]
          have h1 : 1 ≤ l := tripLen_pos r
          have h2 : r.length ≤ u.length := List.length_dropWhile_le (fun c : Bool => c) u
          omega
        have ih_d : DecSpec (List.drop l r) d.1 d.2 := ih (List.drop l r) hvlen
        obtain ⟨hd1, hd2, hd3, hd4, hd5, hd6⟩ := ih_d
        have htrips : ∀ τ ∈ d.2, τ ≠ [] := trips_ne_nil hd3
        have hl1 : 1 ≤ l := tripLen_pos r
        have hl_le : l ≤ r.length := tripLen_le hR'
        have hτlen : (List.take l r).length = l := by
          rw [List.length_take, min_eq_left hl_le]
        have husplit : u = u.takeWhile (fun c => c) ++ r := by
          conv_lhs => rw [← List.takeWhile_append_dropWhile (p := fun c => c) (l := u)]
        have htw : u.takeWhile (fun c => c) = List.replicate g true := takeWhile_id_replicate u
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
        · -- lengths
          simp only [List.length_cons]
          omega
        · -- assembly
          rw [asm_cons_eq, ← hd2, List.append_assoc, List.take_append_drop, husplit, htw]
        · -- trips start off centre
          intro i τ hmem
          cases i with
          | zero =>
              rw [List.getElem?_cons_zero] at hmem
              have hτ : List.take l r = τ := by simpa using hmem
              subst hτ
              rw [wstate_take_le hl1]
              rw [show wstate r 1 = 1 from wstate_dropWhile_one u hR]
              omega
          | succ i =>
              rw [List.getElem?_cons_succ] at hmem
              exact hd3 i τ hmem
        · -- trips do not return early
          intro i τ hmem t ht1 ht2
          cases i with
          | zero =>
              rw [List.getElem?_cons_zero] at hmem
              have hτ : List.take l r = τ := by simpa using hmem
              subst hτ
              rw [List.length_take] at ht2
              have htl : t < l := lt_of_lt_of_le ht2 (min_le_left l r.length)
              rw [wstate_take_le (le_of_lt htl)]
              exact wstate_lt_tripLen_ne_zero r ht1 htl
          | succ i =>
              rw [List.getElem?_cons_succ] at hmem
              exact hd4 i τ hmem t ht1 ht2
        · -- non-last trips return to `0`
          intro i τ hmem hlt
          cases i with
          | zero =>
              rw [List.getElem?_cons_zero] at hmem
              have hτ : List.take l r = τ := by simpa using hmem
              subst hτ
              have hne : d.2 ≠ [] := by
                intro hnil
                rw [hnil] at hlt
                simp only [List.length_cons, List.length_nil] at hlt
                omega
              have hvne : List.drop l r ≠ [] := by
                intro hcon
                have ha : d.1 ≠ [] := by
                  intro hcon2
                  have hh := hd1
                  rw [hcon2] at hh
                  simp only [List.length_nil] at hh
                  omega
                exact asm_ne_nil ha hne htrips (by rw [← hd2]; exact hcon)
              have hlt2 : l < r.length := by
                by_contra hle
                rw [not_lt] at hle
                exact hvne (List.drop_eq_nil_iff.mpr hle)
              rw [hτlen, wstate_take_le le_rfl]
              rcases wstate_tripLen_eq_zero_or r with h0 | h0
              · exact h0
              · omega
          | succ i =>
              rw [List.getElem?_cons_succ] at hmem
              have hlt' : i + 1 < d.2.length := by
                simp only [List.length_cons] at hlt
                omega
              exact hd5 i τ hmem hlt'
        · -- last trip and last gap
          intro i τ g' hmem hag heq
          cases i with
          | zero =>
              rw [List.getElem?_cons_zero] at hmem
              have hτ : List.take l r = τ := by simpa using hmem
              subst hτ
              rw [List.getElem?_cons_succ] at hag
              have hd2nil : d.2 = [] := by
                have h0 : d.2.length = 0 := by
                  simp only [List.length_cons] at heq
                  omega
                exact List.length_eq_zero_iff.mp h0
              rcases wstate_tripLen_eq_zero_or r with h0 | h0
              · left
                rw [hτlen, wstate_take_le le_rfl]
                exact h0
              · right
                have hl0 : l = r.length := by rw [hl]; exact h0
                have hv0 : List.drop l r = [] := by rw [hl0, List.drop_length]
                rw [hv0, hd2nil] at hd2
                have hd1len : d.1.length = 1 := by
                  rw [hd1, hd2nil]; simp
                have hd1ne : d.1 ≠ [] := by
                  intro hcon
                  rw [hcon] at hd1len
                  simp at hd1len
                obtain ⟨x, hx⟩ := List.length_eq_one_iff.mp hd1len
                rw [hx] at hd2 hag
                rw [show asm [x] [] = List.replicate x true from rfl] at hd2
                have hx0 : x = 0 := (List.replicate_eq_nil_iff true).mp hd2.symm
                rw [List.getElem?_cons_zero] at hag
                simp only [Option.some.injEq] at hag
                omega
          | succ i =>
              rw [List.getElem?_cons_succ] at hmem
              rw [List.getElem?_cons_succ] at hag
              have heq' : i + 1 = d.2.length := by
                simp only [List.length_cons] at heq
                omega
              exact hd6 i τ g' hmem hag heq'

end

end Work.EQ.FanTri
