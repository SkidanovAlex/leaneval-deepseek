import Mathlib.Data.List.Lex
import Mathlib.Algebra.Order.Ring.Nat
import Submission.Work.SSGRoute.prop5.witt.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.prop5.witt

/-- A word `w` is *Lyndon-like* if it is strictly smaller (lexicographically) than each of its
proper nonempty suffixes, i.e. `w < s` whenever `w = p ++ s` with `p` and `s` both nonempty. -/
def LyndonLike {X : Type*} [LinearOrder X] (w : List X) : Prop :=
  ∀ p s : List X, w = p ++ s → p ≠ [] → s ≠ [] → w < s

/-- If `u < v` and `u` is not a prefix of `v`, then `u ++ w < v` for **any** word `w`.
(The two words differ at their first point of divergence, which lies inside `u`.) -/
lemma lex_append_of_not_prefix {X : Type*} [LinearOrder X] :
    ∀ (u v w : List X), u < v → ¬ u <+: v → u ++ w < v := by
  intro u
  induction u with
  | nil => intro v w h hpre; exact absurd (List.prefix_append [] v) hpre
  | cons a l ih =>
      intro v w h hpre
      cases v with
      | nil => exact absurd h (by simp)
      | cons b m =>
          cases h with
          | rel hab => exact List.Lex.rel hab
          | cons hlm =>
              exact List.Lex.cons (ih m w hlm (by
                intro hpm
                exact hpre (List.cons_prefix_cons.mpr ⟨rfl, hpm⟩)))

/-- If `u < v` and `v` is no longer than `u`, then `u ++ w < v ++ w`.  (Again the first
point of divergence lies inside `v`, so the common suffix `w` is irrelevant.) -/
lemma lex_append_append_of_length_le {X : Type*} [LinearOrder X] :
    ∀ (u v w : List X), u < v → v.length ≤ u.length → u ++ w < v ++ w := by
  intro u
  induction u with
  | nil =>
      intro v w h hlen
      cases v with
      | nil => exact absurd h (lt_irrefl _)
      | cons b m => exact absurd hlen (by simp)
  | cons a l ih =>
      intro v w h hlen
      cases v with
      | nil => exact absurd h (by simp)
      | cons b m =>
          cases h with
          | rel hab => exact List.Lex.rel hab
          | cons hlm =>
              exact List.Lex.cons (ih m w hlm (by simp at hlen; omega))

/-- For a Lyndon-like word `v` and a nonempty word `u < v`, the concatenation `u ++ v` is still
smaller than `v`. -/
lemma lyndon_like_append {X : Type*} [LinearOrder X] {u v : List X}
    (hu : u ≠ []) (hv : LyndonLike v) (huv : u < v) : u ++ v < v := by
  by_cases hpre : u <+: v
  · -- `v = u ++ s`: cancel the common prefix `u`, and use that `s` is a proper suffix of `v`.
    rcases hpre with ⟨s, rfl⟩
    rcases eq_or_ne s [] with rfl | hs
    · rw [List.append_nil] at huv; exact absurd huv (lt_irrefl _)
    · exact List.Lex.append_left (· < ·) (hv u s rfl hu hs) u
  · exact lex_append_of_not_prefix u v v huv hpre

/-- **The foliage of a Hall tree is Lyndon-like.** -/
lemma hall_lyndonLike {X : Type*} [LinearOrder X] (x : Magma X) :
    IsHall x → LyndonLike (Magma.foliage x) := by
  induction x with
  | gen a =>
      intro hx p s he hp hs
      rw [Magma.foliage_gen] at he
      have hlen : p.length + s.length = 1 := by
        have := congrArg List.length he
        simpa [List.length_append, eq_comm] using this
      have hp1 : 1 ≤ p.length := List.length_pos_iff.mpr hp
      have hs1 : 1 ≤ s.length := List.length_pos_iff.mpr hs
      omega
  | mul a b iha ihb =>
      intro hx
      show LyndonLike (Magma.foliage a ++ Magma.foliage b)
      have ha : IsHall a := IsHall.left hx
      have hb : IsHall b := IsHall.right hx
      have hla : LyndonLike (Magma.foliage a) := iha ha
      have hlb : LyndonLike (Magma.foliage b) := ihb hb
      have hab : Magma.foliage a < Magma.foliage b := IsHall.foliage_lt hx
      -- The suffix `foliage b` of `foliage a ++ foliage b`.
      have hT : Magma.foliage a ++ Magma.foliage b < Magma.foliage b :=
        lyndon_like_append (Magma.foliage_ne_nil a) hlb hab
      intro p s he hp hs
      -- Write `p = fa.take k ++ fb.take (k - |fa|)` and
      -- `s = fa.drop k ++ fb.drop (k - |fa|)` where `k = |p|`.
      set k := p.length with hkp
      have hp1 : p = (Magma.foliage a).take k ++ (Magma.foliage b).take (k - (Magma.foliage a).length) := by
        calc p = (p ++ s).take p.length := (List.take_left (l₁ := p) (l₂ := s)).symm
          _ = (Magma.foliage a ++ Magma.foliage b).take p.length := by rw [← he]
          _ = (Magma.foliage a).take p.length ++ (Magma.foliage b).take (p.length - (Magma.foliage a).length) := List.take_append
          _ = (Magma.foliage a).take k ++ (Magma.foliage b).take (k - (Magma.foliage a).length) := by rw [← hkp]
      have hs1 : s = (Magma.foliage a).drop k ++ (Magma.foliage b).drop (k - (Magma.foliage a).length) := by
        calc s = (p ++ s).drop p.length := (List.drop_left (l₁ := p) (l₂ := s)).symm
          _ = (Magma.foliage a ++ Magma.foliage b).drop p.length := by rw [← he]
          _ = (Magma.foliage a).drop p.length ++ (Magma.foliage b).drop (p.length - (Magma.foliage a).length) := List.drop_append
          _ = (Magma.foliage a).drop k ++ (Magma.foliage b).drop (k - (Magma.foliage a).length) := by rw [← hkp]
      by_cases hk : k ≤ (Magma.foliage a).length
      · -- the split point lies inside `foliage a`
        have hpk : p = (Magma.foliage a).take k := by
          rw [hp1, Nat.sub_eq_zero_of_le hk, List.take_zero, List.append_nil]
        have hsk : s = (Magma.foliage a).drop k ++ Magma.foliage b := by
          rw [hs1, Nat.sub_eq_zero_of_le hk, List.drop_zero]
        rcases eq_or_lt_of_le hk with hk' | hk'
        · -- `p = foliage a`, so `s = foliage b`
          have hpfa : p = Magma.foliage a := by rw [hpk, hk', List.take_length]
          have hsfa : s = Magma.foliage b := by rw [hsk, hk', List.drop_length, List.nil_append]
          rw [hsfa]; exact hT
        · -- `p` is a proper prefix of `foliage a`: `foliage a < foliage a.drop k`
          have hdr : (Magma.foliage a).drop k ≠ [] := by
            intro h; rw [List.drop_eq_nil_iff] at h; omega
          have hEq : Magma.foliage a = p ++ (Magma.foliage a).drop k := by
            rw [hpk]; exact (List.take_append_drop k (Magma.foliage a)).symm
          have hlt : Magma.foliage a < (Magma.foliage a).drop k := hla p _ hEq hp hdr
          have hlen : ((Magma.foliage a).drop k).length ≤ (Magma.foliage a).length := by
            rw [List.length_drop]; exact Nat.sub_le _ _
          have hstep := lex_append_append_of_length_le (Magma.foliage a) ((Magma.foliage a).drop k) (Magma.foliage b) hlt hlen
          rw [hsk]; exact hstep
      · -- the split point lies inside `foliage b`: `s` is a proper suffix of `foliage b`
        have hklt : (Magma.foliage a).length < k := not_le.mp hk
        have hpk : p = Magma.foliage a ++ (Magma.foliage b).take (k - (Magma.foliage a).length) := by
          rw [hp1, List.take_of_length_le (le_of_lt hklt)]
        have hq_ne : (Magma.foliage b).take (k - (Magma.foliage a).length) ≠ [] := by
          intro h; rw [List.take_eq_nil_iff] at h
          rcases h with h | h
          · omega
          · exact Magma.foliage_ne_nil b h
        have hfb : Magma.foliage b = (Magma.foliage b).take (k - (Magma.foliage a).length) ++ s := by
          have h := he
          rw [hpk, List.append_assoc] at h
          exact List.append_cancel_left h
        exact lt_trans hT (hlb _ s hfb hq_ne hs)

lemma hall_foliage_lt_right {X : Type*} [LinearOrder X] {a b : Magma X} (h : IsHall (Magma.mul a b)) : Magma.foliage (Magma.mul a b) < Magma.foliage b := by
  have hb : IsHall b := IsHall.right h
  have hab : Magma.foliage a < Magma.foliage b := IsHall.foliage_lt h
  have hlb : LyndonLike (Magma.foliage b) := hall_lyndonLike b hb
  have hmm := lyndon_like_append (Magma.foliage_ne_nil a) hlb hab
  simpa using hmm

end Work.SSGRoute.prop5.witt
