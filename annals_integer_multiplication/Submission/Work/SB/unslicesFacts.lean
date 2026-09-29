import Mathlib
import Submission.Work.Layout.SB.Specs
import Submission.Work.Layout.Shared
import Submission.Work.Layout.unslicesIdx

/-!
# Facts about `unslices` (the second sort of the sort-based `applyAlong`)

The file proves `Work.SB.unslicesFacts`, the statement needed to turn the sorted,
key-labelled flat list produced by the pipeline

```
flatten ; enumerate ; mapList kw2 ; sortByKey ; strip
```

back into the `A × n × B` slice layout `unslices A n B outs`.

Two independent ingredients are used:

* `flatten_getD_block`: indexing a flattened list of equal-length rows;
* `mapUnlab_of_perm_sorted`: a list of key-labelled records which is a *sorted*
  permutation of `(range N).map (fun f => cons (int (σ f)) (F f))`, where `σ` is a
  bijection of `range N` with inverse `ρ`, has `unlab`-image `(range N).map (F ∘ ρ)`.

The number-theoretic input (`tgtIdx`/`invIdx2` are inverse bijections) is
`Work.Layout.unslicesIdx`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.SB

open HvdH
open Work.Layout

/-- Indexing into the flattening of a list of rows that all have length `n`:
position `s * n + j` (with `s` a valid row and `j < n`) is the `j`-th entry of row `s`. -/
private lemma flatten_getD_block {α : Type} : ∀ (xss : List (List α)) (n : ℕ) (d₁ d₂ : α),
    (∀ s, s < xss.length → (xss.getD s []).length = n) →
    ∀ s j, s < xss.length → j < n →
      xss.flatten.getD (s * n + j) d₁ = (xss.getD s []).getD j d₂
  | [], n, d₁, d₂, _, s, j, hs, _ => absurd hs (Nat.not_lt_zero s)
  | x :: xs, n, d₁, d₂, hn, s, j, hs, hj => by
      have hx : x.length = n := by simpa using hn 0 (Nat.zero_lt_succ xs.length)
      cases s with
      | zero =>
          have hjx : j < x.length := by omega
          rw [List.flatten_cons]
          simp only [Nat.zero_mul, Nat.zero_add]
          rw [List.getD_append _ _ _ _ hjx, List.getD_cons_zero,
            List.getD_eq_getElem x d₁ hjx, List.getD_eq_getElem x d₂ hjx]
      | succ s' =>
          have hs' : s' < xs.length := by simpa using hs
          have hn' : ∀ t, t < xs.length → (xs.getD t []).length = n := by
            intro t ht
            have h := hn (t + 1) (by simpa using ht)
            simpa using h
          have hidx : (s' + 1) * n + j = x.length + (s' * n + j) := by
            rw [Nat.succ_mul, hx]; ring
          rw [List.flatten_cons, hidx, List.getD_append_right _ _ _ _ (by omega),
            Nat.add_sub_cancel_left, List.getD_cons_succ]
          exact flatten_getD_block xs n d₁ d₂ hn' s' j hs' hj

/-- The `tgtIdx` key of the element at flat index `f` of the slice-major listing is a bijection
of `range (A * B * n)`, with inverse given by `invIdx2`. -/
private lemma tgtIdx_invIdx2_facts (A n B : ℕ) (hn : 0 < n) (hB : 0 < B) :
    (∀ f, f < A * B * n → tgtIdx n B (f / n) (f % n) < A * B * n) ∧
    (∀ r, r < A * B * n → (invIdx2 n B r).1 < A * B) ∧
    (∀ r, r < A * B * n → (invIdx2 n B r).2 < n) ∧
    (∀ r, r < A * B * n → (invIdx2 n B r).1 * n + (invIdx2 n B r).2 < A * B * n) ∧
    (∀ f, f < A * B * n → (invIdx2 n B (tgtIdx n B (f / n) (f % n))).1 * n +
        (invIdx2 n B (tgtIdx n B (f / n) (f % n))).2 = f) ∧
    (∀ r, r < A * B * n → tgtIdx n B (((invIdx2 n B r).1 * n + (invIdx2 n B r).2) / n)
        (((invIdx2 n B r).1 * n + (invIdx2 n B r).2) % n) = r) := by
  obtain ⟨u1, u2, u3, u4⟩ := unslicesIdx A n B hn hB
  have hA : A * n * B = A * B * n := by ring
  have hdiv : ∀ f, f < A * B * n → f / n < A * B := by
    intro f hf
    rw [Nat.div_lt_iff_lt_mul hn]
    exact hf
  have hb : ∀ r, r < A * B * n → (invIdx2 n B r).1 < A * B ∧ (invIdx2 n B r).2 < n := by
    intro r hr
    exact u4 r (by rwa [hA])
  refine ⟨?_, fun r hr => (hb r hr).1, fun r hr => (hb r hr).2, ?_, ?_, ?_⟩
  · intro f hf
    have h := u1 (f / n) (f % n) (hdiv f hf) (Nat.mod_lt f hn)
    rwa [hA] at h
  · intro r hr
    obtain ⟨hs, hj⟩ := hb r hr
    have h2 : (invIdx2 n B r).1 * n + (invIdx2 n B r).2 < ((invIdx2 n B r).1 + 1) * n := by
      have h3 : (invIdx2 n B r).1 * n + (invIdx2 n B r).2 < (invIdx2 n B r).1 * n + n := by omega
      simpa [Nat.succ_mul] using h3
    calc (invIdx2 n B r).1 * n + (invIdx2 n B r).2 < ((invIdx2 n B r).1 + 1) * n := h2
      _ ≤ A * B * n := Nat.mul_le_mul_right n (Nat.succ_le_of_lt hs)
  · intro f hf
    have hj : f % n < n := Nat.mod_lt f hn
    have h2 := u2 (f / n) (f % n) (hdiv f hf) hj
    rw [h2]
    show (f / n) * n + f % n = f
    rw [Nat.mul_comm (f / n) n]
    exact Nat.div_add_mod f n
  · intro r hr
    obtain ⟨hs, hj⟩ := hb r hr
    have hdn : ((invIdx2 n B r).1 * n + (invIdx2 n B r).2) / n = (invIdx2 n B r).1 := by
      rw [Nat.mul_comm (invIdx2 n B r).1 n, Nat.mul_add_div hn, Nat.div_eq_of_lt hj, Nat.add_zero]
    have hmn : ((invIdx2 n B r).1 * n + (invIdx2 n B r).2) % n = (invIdx2 n B r).2 := by
      rw [Nat.mul_comm (invIdx2 n B r).1 n, Nat.mul_add_mod, Nat.mod_eq_of_lt hj]
    rw [hdn, hmn]
    exact u3 r (by rwa [hA])

/-- Sorting a key-labelled list by key and stripping the keys: if `σ` is a bijection of
`range N` (inverse `ρ` on the range) then a *sorted* permutation `ys` of
`(range N).map (fun f => cons (int (σ f)) (F f))` has `unlab`-image `(range N).map (F ∘ ρ)`. -/
private theorem mapUnlab_of_perm_sorted (N : ℕ) (F : ℕ → Val) (σ ρ : ℕ → ℕ) (ys : List Val)
    (hσ : ∀ f, f < N → σ f < N) (hρ : ∀ r, r < N → ρ r < N)
    (hρσ : ∀ f, f < N → ρ (σ f) = f) (hσρ : ∀ r, r < N → σ (ρ r) = r)
    (hperm : ys.Perm ((List.range N).map (fun f => Val.cons (.int ((σ f : ℕ) : ℤ)) (F f))))
    (hsort : ys.Pairwise (fun a b => pairKey a < pairKey b)) :
    ys.map unlab = (List.range N).map (fun r => F (ρ r)) := by
  -- `σ` is injective on `range N`
  have hnodup_mp : ((List.range N).map σ).Nodup := by
    rw [List.nodup_map_iff_inj_on List.nodup_range]
    intro x hx y hy hxy
    have hxN : x < N := List.mem_range.mp hx
    have hyN : y < N := List.mem_range.mp hy
    have h1 : x = ρ (σ x) := (hρσ x hxN).symm
    have h2 : ρ (σ x) = ρ (σ y) := by rw [hxy]
    exact (h1.trans h2).trans (hρσ y hyN)
  -- hence it is a bijection of `range N`
  have hperm_range : ((List.range N).map σ).Perm (List.range N) :=
    (List.subperm_of_subset hnodup_mp (fun a ha => by
        obtain ⟨f, hf, rfl⟩ := List.mem_map.mp ha
        exact List.mem_range.mpr (hσ f (List.mem_range.mp hf)))).antisymm
      (List.subperm_of_subset List.nodup_range (fun a ha => by
        have haN : a < N := List.mem_range.mp ha
        exact List.mem_map.mpr ⟨ρ a, List.mem_range.mpr (hρ a haN), hσρ a haN⟩))
  -- the labelled list is the image of the permuted range
  have hl_eq : (List.range N).map (fun f => Val.cons (.int ((σ f : ℕ) : ℤ)) (F f))
      = ((List.range N).map σ).map (fun r => Val.cons (.int ((r : ℕ) : ℤ)) (F (ρ r))) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro f hfmem
    have hfN : f < N := List.mem_range.mp hfmem
    show Val.cons (.int ((σ f : ℕ) : ℤ)) (F f)
      = Val.cons (.int ((σ f : ℕ) : ℤ)) (F (ρ (σ f)))
    exact (congrArg (fun y => Val.cons (.int ((σ f : ℕ) : ℤ)) (F y)) (hρσ f hfN)).symm
  have hperm_lc : ys.Perm
      ((List.range N).map (fun r => Val.cons (.int ((r : ℕ) : ℤ)) (F (ρ r)))) := by
    refine hperm.trans ?_
    rw [hl_eq]
    exact hperm_range.map (fun r => Val.cons (.int ((r : ℕ) : ℤ)) (F (ρ r)))
  -- the canonical list is sorted
  have hlc_pw : ((List.range N).map (fun r => Val.cons (.int ((r : ℕ) : ℤ)) (F (ρ r)))).Pairwise
      (fun a b => pairKey a < pairKey b) := by
    refine List.Pairwise.map (fun r => Val.cons (.int ((r : ℕ) : ℤ)) (F (ρ r))) ?_
      List.pairwise_lt_range
    intro a b hab
    have h : ((a : ℕ) : ℤ) < ((b : ℕ) : ℤ) := by exact_mod_cast hab
    simpa only [pairKey] using h
  -- sortedness pins `ys`
  have hys : ys = (List.range N).map (fun r => Val.cons (.int ((r : ℕ) : ℤ)) (F (ρ r))) :=
    hperm_lc.eq_of_pairwise' hsort hlc_pw
  rw [hys, List.map_map]
  apply List.map_congr_left
  intro r _
  show unlab (Val.cons (.int ((r : ℕ) : ℤ)) (F (ρ r))) = F (ρ r)
  rfl

theorem unslicesFacts (A n B : ℕ) (outs : List (List Val)) :
    (unslices A n B outs).length = A * n * B ∧
    (∀ (_hn : 0 < n) (_hB : 0 < B) (hlen : outs.length = A * B)
      (hsl : ∀ s, s < A * B → (outs.getD s []).length = n) (ys : List Val),
      ys.Perm ((List.range (A * B * n)).map
        (fun f => Val.cons (.int ((tgtIdx n B (f / n) (f % n) : ℕ) : ℤ)) ((outs.flatten).getD f .nil))) →
      ys.Pairwise (fun a b => pairKey a < pairKey b) → ys.map unlab = unslices A n B outs) := by
  refine ⟨by simp [HvdH.unslices], ?_⟩
  intro hn hB hlen hsl ys hperm hsort
  obtain ⟨hσ, hb1, hb2, hρ, hρσ, hσρ⟩ := tgtIdx_invIdx2_facts A n B hn hB
  have hmaster := mapUnlab_of_perm_sorted (A * B * n) (fun f => (outs.flatten).getD f .nil)
    (fun f => tgtIdx n B (f / n) (f % n))
    (fun r => (invIdx2 n B r).1 * n + (invIdx2 n B r).2) ys hσ hρ hρσ hσρ hperm hsort
  rw [hmaster]
  have hn' : ∀ s, s < outs.length → (outs.getD s []).length = n := by
    intro s hs'
    exact hsl s (by rw [← hlen]; exact hs')
  have hstep : (List.range (A * n * B)).map
      (fun r => (outs.flatten).getD ((invIdx2 n B r).1 * n + (invIdx2 n B r).2) .nil)
      = (List.range (A * n * B)).map
      (fun idx => (outs.getD (idx / (n * B) * B + idx % B) []).getD (idx / B % n) default) := by
    apply List.map_congr_left
    intro r hr
    have hrN : r < A * B * n := by
      have h : r < A * n * B := List.mem_range.mp hr
      rwa [show A * n * B = A * B * n by ring] at h
    have hblk := flatten_getD_block outs n .nil default hn' (invIdx2 n B r).1 (invIdx2 n B r).2
      (by rw [hlen]; exact hb1 r hrN) (hb2 r hrN)
    simpa only [Work.Layout.invIdx2] using hblk
  rw [show A * B * n = A * n * B by ring]
  exact hstep.trans rfl

end Work.SB
