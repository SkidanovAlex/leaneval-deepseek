import Mathlib
import Submission.Work.SynFFT.kit2

/-!
# `lvlAllGetD`: reading the level pass of a slice at a position gives `lvlN`

`lvlAll r t m sgn l` is the level-`m` butterfly pass on a whole slice of length `t` (`m ∣ t`):
it cuts the slice into `t / m` consecutive blocks of `m` elements and applies `blkLvl r m sgn`
to each of them (`blkLvl` being the *list-level* version of `lvlN`).

This file proves `LvlAllGetDProp`, i.e. that the slicing is invisible to a *reader* of the
result: for every `p < t` the `p`-th entry of `lvlAll r t m sgn l` is exactly the `p`-th entry of
the global operator `lvlN r m sgn` applied to the array `q ↦ l.getD q 0`.  This is what lets the
slice word be specified (`HasLvlPass`, `HasBlkLvl` in `kit2`) block-by-block while the *math*
side (`dft1Math`, `levels`) works with the global `lvlN`.

The proof is pure list plumbing:

* `getD_map_range` / `getD_flatten_eq`: general index lemmas for `(List.range n).map f` and for
  the flatten of a list of equal-length blocks;
* `blkLvl_getD`: unfold `blkLvl` at a position `< m` of its input (`blkLvl` is a `List.range`
  followed by a `map`, so the computation is definitional once the index is in range);
* the assembly: write `p = b * m + j` with `j < m`, read the flattened slice at `b * m + j`
  (block `b`), unfold `blkLvl` there, and observe that both branches (the `(u₁+u₂)/2` branch and
  the twiddled `(u₁-u₂)/2` branch) agree term by term with `lvlN`, the block-local offsets
  `p`, `p + m/2`, `p - m/2` of `lvlN` being `b * m + j`, `b * m + (j + m/2)`,
  `b * m + (j - m/2)`.
-/

set_option maxHeartbeats 800000

namespace Work.SynFFT

open HvdH

/-! ## Two general list index lemmas -/

/-- The `j`-th entry of `(List.range n).map f`, for `j < n`, is `f j`. -/
theorem getD_map_range {α : Type*} (f : ℕ → α) (d : α) {n j : ℕ} (hj : j < n) :
    ((List.range n).map f).getD j d = f j := by
  rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_map, List.getElem_range]

/-- Reading the concatenation of blocks that all have length `n`: the entry of flat index
`b * n + j` is the entry `j` of block `b`.  No bound on `b` is needed -- beyond the end both
sides are the default `d`. -/
theorem getD_flatten_eq {α : Type*} (L : List (List α)) (d : α) {n : ℕ}
    (hn : ∀ l ∈ L, l.length = n) (b j : ℕ) (hj : j < n) :
    L.flatten.getD (b * n + j) d = (L.getD b []).getD j d := by
  induction L generalizing b with
  | nil => simp
  | cons l L' ih =>
    have hl : l.length = n := hn l (by simp)
    have hl' : ∀ x ∈ L', x.length = n := fun x hx => hn x (by simp [hx])
    cases b with
    | zero =>
      simp only [Nat.zero_mul, Nat.zero_add]
      rw [List.flatten_cons, List.getD_cons_zero,
        List.getD_append l L'.flatten d j (by rw [hl]; exact hj)]
    | succ b' =>
      have hle : l.length ≤ (b' + 1) * n + j := by
        rw [hl]; rw [Nat.succ_mul]; omega
      rw [List.flatten_cons, List.getD_append_right l L'.flatten d ((b' + 1) * n + j) hle,
        hl, List.getD_cons_succ]
      have hidx : (b' + 1) * n + j - n = b' * n + j := by
        rw [Nat.succ_mul]; omega
      rw [hidx]
      exact ih hl' b'

/-! ## Unfolding `blkLvl` at a position of the input -/

/-- `blkLvl` at an index inside its input: since `blkLvl` is `(List.range l.length).map ⋯`, this
is definitional once `j < L.length`. -/
theorem blkLvl_getD (r m : ℕ) (sgn : ℤ) (L : List (Fin r → ℂ)) (j : ℕ) (hj : j < L.length) :
    (blkLvl r m sgn L).getD j 0 =
      (if j % m < m / 2 then
          (fun c => (L.getD j 0 c + L.getD (j + m / 2) 0 c) / 2)
        else
          yMul r (sgn * (((2 * r / m) * (j % m - m / 2) : ℕ) : ℤ))
            (fun c' => (L.getD (j - m / 2) 0 c' - L.getD j 0 c') / 2)) := by
  simp only [blkLvl]
  rw [getD_map_range _ (0 : Fin r → ℂ) hj]

/-! ## The main statement -/

theorem lvlAllGetD : Work.SynFFT.LvlAllGetDProp := by
  intro r t m sgn l hmt hm p hp
  -- write `p = b * m + j` with `b < t / m` the block and `j < m` the offset inside the block
  obtain ⟨b, j, hb, hj, hpj⟩ : ∃ b j, b < t / m ∧ j < m ∧ p = b * m + j :=
    ⟨p / m, p % m, Nat.div_lt_div_of_lt_of_dvd hmt hp, Nat.mod_lt _ hm, by
      rw [mul_comm]; exact (Nat.div_add_mod p m).symm⟩
  subst hpj
  simp only [lvlAll]
  -- the blocks all have length `m`, so the flattened slice is read block by block
  have hlen : ∀ L ∈ (List.range (t / m)).map
      (fun b => blkLvl r m sgn ((List.range m).map fun j => l.getD (b * m + j) 0)),
      L.length = m := by
    intro L hL
    obtain ⟨b', -, rfl⟩ := List.mem_map.mp hL
    simp [blkLvl]
  rw [getD_flatten_eq _ _ hlen b j hj,
    getD_map_range _ ([] : List (Fin r → ℂ)) hb]
  -- now unfold the block word at the offset `j`
  have hLlen : ((List.range m).map fun c => l.getD (b * m + c) 0).length = m := by simp
  rw [blkLvl_getD r m sgn _ j (by rw [hLlen]; exact hj)]
  -- and read the block's entries back as entries of `l`
  have hq : ∀ q < m, ((List.range m).map fun c => l.getD (b * m + c) 0).getD q 0
      = l.getD (b * m + q) 0 := by
    intro q hq
    simpa using getD_map_range (fun c => l.getD (b * m + c) 0) (0 : Fin r → ℂ) hq
  have hjmod : j % m = j := Nat.mod_eq_of_lt hj
  have hmod : (b * m + j) % m = j := by
    rw [mul_comm b m, Nat.mul_add_mod, Nat.mod_eq_of_lt hj]
  -- both sides are `if ⋯ then ⋯ else ⋯`; the two conditions become the same, and then so do the
  -- two branches, since the block-local offsets are the global ones shifted by `b * m`
  funext c
  rw [ite_apply]
  simp only [lvlN]
  rw [hjmod, hmod]
  by_cases hlt : j < m / 2
  · rw [ite_eq_left hlt, ite_eq_left hlt, hq j hj, hq (j + m / 2) (by omega), Nat.add_assoc]
  · rw [ite_eq_right hlt, ite_eq_right hlt, hq j hj, hq (j - m / 2) (by omega)]
    rw [Nat.add_sub_assoc (by omega : m / 2 ≤ j) (b * m)]

end Work.SynFFT
