import Mathlib
import Submission.Work.Resample.auConvDefs

namespace Work.Resample

set_option autoImplicit false

/-!
# Indexing of the extended input array (paper Remark 4.10, Lemma 4.9 setup)

`Work.Resample.auExt p α s u` is `auCop p α s` copies of `u` glued together and dropped by
`auOff p α s`.  Its entry `auK s t k + i` is therefore the input entry `auJ p α s t k i`:

* the index `auOff + (auK + i)` really lies inside the glued list (needs `auK s t k ≤ s`, which
  holds because `k < t`, and `i < auL p α = 2·auM p α + 1`);
* modulo `s` the offset `auOff = s·⌈auM/s⌉ − auM` is congruent to `−auM`, so the residue of
  `auOff + (auK + i)` is the residue of `auK + i − auM`, which is exactly `auJ`.
-/

/-- `(n - k) % k = n % k` for `k ≤ n`. -/
lemma auIdx_aux_subModSelf (k n : ℕ) (h : k ≤ n) : (n - k) % k = n % k := by
  have hsub : n = (n - k) + k * 1 := by omega
  conv_rhs => rw [hsub]
  exact (Nat.add_mul_mod_self_left _ _ _).symm

/-- The `n`-th entry of a list glued from `c` copies of `l` is the `(n % l.length)`-th entry of
`l`, for every `n` that actually lies in the glued list. -/
lemma auIdx_aux_flattenReplicate {α : Type*} (l : List α) :
    ∀ c n, n < c * l.length →
      (List.flatten (List.replicate c l))[n]? = l[n % l.length]? := by
  intro c
  induction c with
  | zero => intro n h; simp at h
  | succ c ih =>
    intro n h
    rw [List.replicate_succ, List.flatten_cons, List.getElem?_append]
    split_ifs with hlt
    · rw [Nat.mod_eq_of_lt hlt]
    · rw [ih (n - l.length) ?_]
      · congr 1
        exact auIdx_aux_subModSelf l.length n (by omega)
      · rw [Nat.succ_mul] at h
        have hsub : n = (n - l.length) + l.length := by omega
        have : (n - l.length) + l.length < c * l.length + l.length := by
          rw [← hsub]; exact h
        exact Nat.add_lt_add_iff_right.mp this

/-- For `k < t` the window centre `auK s t k` is at most `s`. -/
lemma auIdx_aux_auK_le_s (s t k : ℕ) (hk : k < t) : auK s t k ≤ s := by
  have hstep : 2 * (k + 1) * s ≤ 2 * t * s :=
    Nat.mul_le_mul_right s (Nat.mul_le_mul_left 2 (by omega : k + 1 ≤ t))
  have h1 : 2 * k * s + 2 * s ≤ 2 * t * s := by nlinarith
  have h3 : 2 * k * s + t ≤ 2 * t * s + t :=
    Nat.add_le_add_right (le_trans (Nat.le_add_right _ _) h1) t
  rw [auK, ← Nat.lt_succ_iff, Nat.div_lt_iff_lt_mul (by omega : 0 < 2 * t)]
  calc 2 * k * s + t < 2 * t * s + 2 * t := by omega
    _ = (s + 1) * (2 * t) := by ring

/-- `auOff p α s + (auK s t k + i)` is a valid index of the extended input array. -/
lemma auIdx_aux_bound (p α s t k i : ℕ) (hs : 2 ≤ s) (hk : k < t) (hi : i < auL p α) :
    auOff p α s + (auK s t k + i) < auCop p α s * s := by
  have hK : auK s t k ≤ s := auIdx_aux_auK_le_s s t k hk
  have hi' : i ≤ 2 * auM p α := by simp [auL] at hi; omega
  simp only [auCop, auOff]
  set X : ℕ := s * ((auM p α + s - 1) / s) - auM p α + 2 * s + 2 * auM p α with hXdef
  set y : ℕ := X / s * s with hy
  have hmod : X % s < s := Nat.mod_lt X (by omega)
  have hX : X = y + X % s := by
    rw [hy, mul_comm (X / s) s]
    exact (Nat.div_add_mod X s).symm
  omega

/-- The offset `auOff = s·⌈auM/s⌉ − auM` is congruent to `−auM` modulo `s`. -/
lemma auIdx_aux_auOff_mod (p α s x : ℕ) (hs : 2 ≤ s) :
    ((auOff p α s + x) % s : ℤ) = ((x : ℤ) - (auM p α : ℤ)) % (s : ℤ) := by
  set h := (auM p α + s - 1) / s with hh
  have hs0 : 0 < s := by omega
  have hd : s * h + (auM p α + s - 1) % s = auM p α + s - 1 := by
    rw [hh]; exact Nat.div_add_mod (auM p α + s - 1) s
  have hmle : auM p α ≤ s * h := by
    have hm : (auM p α + s - 1) % s ≤ s - 1 := by
      have := Nat.mod_lt (auM p α + s - 1) hs0; omega
    have hkey : auM p α + (auM p α + s - 1) % s ≤ s * h + (auM p α + s - 1) % s := by
      calc auM p α + (auM p α + s - 1) % s ≤ auM p α + (s - 1) := by omega
        _ = auM p α + s - 1 := by omega
        _ = s * h + (auM p α + s - 1) % s := hd.symm
    exact Nat.le_of_add_le_add_right hkey
  have hoff : auOff p α s = s * h - auM p α := by rw [auOff, ← hh]
  calc ((auOff p α s + x) % s : ℤ)
      = ((auOff p α s : ℤ) + (x : ℤ)) % (s : ℤ) := Int.natCast_emod _ _
    _ = ((s : ℤ) * (h : ℤ) - (auM p α : ℤ) + (x : ℤ)) % (s : ℤ) := by
          rw [hoff, Nat.cast_sub hmle, Nat.cast_mul]
    _ = (((x : ℤ) - (auM p α : ℤ)) + (s : ℤ) * (h : ℤ)) % (s : ℤ) := by
          congr 1; ring
    _ = ((x : ℤ) - (auM p α : ℤ)) % (s : ℤ) :=
          Int.add_mul_emod_self_left _ _ _

/-- The residue modulo `s` of the extended-array index of the `(k,i)`-th retained term is
the input index `auJ p α s t k i`. -/
lemma auIdx_aux_mod (p α s t k i : ℕ) (hs : 2 ≤ s) :
    (auOff p α s + (auK s t k + i)) % s = auJ p α s t k i := by
  apply Nat.cast_injective (R := ℤ)
  rw [auJ_cast p α s t k i hs]
  have h := auIdx_aux_auOff_mod p α s (auK s t k + i) hs
  rw [Nat.cast_add] at h
  exact h

-- Indexing of the extended input array: auExt p α s u is auCop p α s copies of u (length s)
-- dropped by auOff p α s, so its entry auK s t k + i is the input entry auJ p α s t k i.
-- Needs auK s t k ≤ s (so auOff + auK k + i < auCop * s, from the definition of auCop)
-- and auOff + auK k + i ≡ auK k + i - auM p α (mod s) (since auOff = s*⌈auM/s⌉ - auM).
theorem auIdx (p α s t : ℕ) (hs : 2 ≤ s) (hst : s < t) (hα : 2 ≤ α) (hp : 100 ≤ p) (hαp : α ^ 2 < p)
    (u : List (ℤ × ℤ)) (hu : u.length = s) (k : ℕ) (hk : k < t) (i : ℕ) (hi : i < Work.Resample.auL p α) :
    (Work.Resample.auExt p α s u).getD (Work.Resample.auK s t k + i) (0, 0)
      = u.getD (Work.Resample.auJ p α s t k i) (0, 0) := by
  have hbnd : auOff p α s + (auK s t k + i) < auCop p α s * u.length := by
    rw [hu]; exact auIdx_aux_bound p α s t k i hs hk hi
  have hmod : (auOff p α s + (auK s t k + i)) % u.length = auJ p α s t k i := by
    rw [hu]; exact auIdx_aux_mod p α s t k i hs
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  congr 1
  rw [auExt, List.getElem?_drop]
  exact (auIdx_aux_flattenReplicate u (auCop p α s) (auOff p α s + (auK s t k + i)) hbnd).trans
    (by rw [hmod])

end Work.Resample
