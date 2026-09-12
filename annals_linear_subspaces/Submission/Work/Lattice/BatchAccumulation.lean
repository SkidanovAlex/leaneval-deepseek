import Mathlib
import Submission.Work.Lattice.Prop5Iteration
import Submission.Work.Lattice.Lemma5Extension

/-!
# Batch accumulation: the cumulative `π₊`-dominance of the Prop-5 construction

Prop. 5 of de Saxcé builds the family `v₁, …, v_ℓ` by accumulating *batches* from the members
`V_{j₁} ⊂ … ⊂ V_{j_r} < Λ_t` of the Harder–Narasimhan flag.  The counts are the capacities
`k_n := j_n − u_n` (`u_n` the first active block of the member), which the accounting bounds by
`effPos_n`; the members form a chain, so the batches are added by *extending* the orthonormal
family inside the next member, keeping the `π₊`-dominance of the accumulated wedge
(`Lemma5Extension.exists_orthonormal_cone_family`, i.e. the second assertion of Lemma 5).

This module records the accumulation abstractly:

* `exists_dominated_extension` — the one-step extension with an explicit positive level:
  an orthonormal `e : Fin m` in `W` with `lev ≤ ‖⋀^m P (ιMulti e)‖` is extended, using an
  orthonormal `u : Fin i` in `W` with `c ≤ ‖⋀^i P (ιMulti u)‖` and `m < i`, to an orthonormal
  `e' : Fin i` in `W` whose first `m` entries are `e` and with
  `lev' ≤ ‖⋀^i P (ιMulti e')‖` for some `0 < lev' ≤ c`;
* **`exists_dominated_family_through_chain`** — the accumulation along a chain
  `W 0 ≤ W 1 ≤ … ≤ W N` with strictly increasing counts `k n` and a level-`c` dominated
  orthonormal family of size `k n` in `W n` for every stage: there is a single orthonormal family
  `w : Fin (k N) → ℝᵈ` which is dominated at a positive level, lies in `W N`, and whose first
  `k n` entries lie in `W n` for every `n ≤ N` (the cumulative structure).

Module `Submission.Work.Lattice.BatchAccumulation`, namespace `Submission.BatchAccumulation`.
-/

noncomputable section

open Module exteriorPower InnerProductGeometry Real
open scoped BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

namespace Submission.BatchAccumulation

open Submission.ExteriorCoordinates
open Submission.Lemma5Extension
open Submission.Prop5Iteration

variable {d : ℕ}

/-- `Fin.castLE` is compatible with the composition of the bounds. -/
lemma castLE_trans {a b c : ℕ} (h1 : a ≤ b) (h2 : b ≤ c) (j : Fin a) :
    Fin.castLE (le_trans h1 h2) j = Fin.castLE h2 (Fin.castLE h1 j) := by
  ext
  rfl

/-- **One-step batch accumulation.**  An orthonormal family `e` of size `m` with `π₊`-dominance at
level `lev` is extended to size `i > m` using an orthonormal family `u` of size `i` (with
dominance at level `c ≥ lev`), keeping the dominance at a positive level `lev' ≤ c`. -/
theorem exists_dominated_extension {m i : ℕ} (hmi : m < i) (hm0 : 1 ≤ m)
    (P : RD d →ₗ[ℝ] RD d) (hP : ∀ x, ‖P x‖ ≤ ‖x‖) {W : Submodule ℝ (RD d)}
    {e : Fin m → RD d} (he : Orthonormal ℝ e) (heW : ∀ k, e k ∈ W) {lev c : ℝ}
    (hlev : 0 < lev) (hlevc : lev ≤ c)
    (hdom : lev ≤ ‖exteriorPower.map m P (exteriorPower.ιMulti ℝ m e)‖)
    {u : Fin i → RD d} (hu : Orthonormal ℝ u) (huW : ∀ k, u k ∈ W)
    (hbig : c ≤ ‖exteriorPower.map i P (exteriorPower.ιMulti ℝ i u)‖) :
    ∃ (e' : Fin i → RD d) (lev' : ℝ), 0 < lev' ∧ lev' ≤ c ∧ Orthonormal ℝ e' ∧
      (∀ k, e' k ∈ W) ∧ (∀ k : Fin m, e' (Fin.castLE (le_of_lt hmi) k) = e k) ∧
      lev' ≤ ‖exteriorPower.map i P (exteriorPower.ιMulti ℝ i e')‖ := by
  classical
  set e₀ : ℝ := min (min lev c) 1 with he₀
  have he₀pos : 0 < e₀ := lt_min (lt_min hlev (lt_of_lt_of_le hlev hlevc)) one_pos
  have he₀le1 : e₀ ≤ 1 := min_le_right _ _
  have he₀lelev : e₀ ≤ lev := le_trans (min_le_left _ _) (min_le_left _ _)
  have he₀lec : e₀ ≤ c := le_trans (min_le_left _ _) (min_le_right _ _)
  obtain ⟨εseq, γ, hεpos, hεle, hεm, hγ0, hγ1, hstep⟩ :=
    exists_epsSeq (i := i) (m := m) hmi he₀pos he₀le1
  obtain ⟨e', he'ON, he'W, he'ext, he'cone⟩ :=
    exists_orthonormal_cone_family (d := d) P hP (le_of_lt hmi) hm0 W e he heW u hu huW
      εseq hεpos hεle (by rw [hεm]; exact le_trans he₀lelev hdom)
      (by rw [hεm]; exact le_trans he₀lec hbig) γ hγ0 hγ1 hstep
  exact ⟨e', εseq i, hεpos i, le_trans (hεle i) (hεm ▸ he₀lec), he'ON, he'W, he'ext, he'cone⟩

/-- **Batch accumulation along the flag.**  Let `W 0 ≤ W 1 ≤ …` be a chain of subspaces, `k` a
strictly increasing sequence of counts, and suppose that for every stage `n` the subspace `W n`
contains an orthonormal family of size `k n` whose `π₊`-wedge is at least `c > 0`.  Then there is a
single orthonormal family `w` of size `k N`, dominated at a positive level `lev ≤ c`, lying in
`W N`, and *filtered through the chain*: its first `k n` entries lie in `W n` for every `n ≤ N`. -/
theorem exists_dominated_family_through_chain (P : RD d →ₗ[ℝ] RD d) (hP : ∀ x, ‖P x‖ ≤ ‖x‖)
    (W : ℕ → Submodule ℝ (RD d)) (hmono : ∀ n m, n ≤ m → W n ≤ W m)
    (k : ℕ → ℕ) (hkmono : ∀ n m, n ≤ m → k n ≤ k m) (hstrict : ∀ n, k n < k (n + 1))
    {c : ℝ} (hc : 0 < c) :
    ∀ N, (hfam : ∀ n ≤ N, ∃ a : Fin (k n) → RD d, Orthonormal ℝ a ∧ (∀ j, a j ∈ W n) ∧
        c ≤ ‖exteriorPower.map (k n) P (exteriorPower.ιMulti ℝ (k n) a)‖) →
      (hpos : 0 < k 0) →
      ∃ (w : Fin (k N) → RD d) (lev : ℝ), 0 < lev ∧ lev ≤ c ∧ Orthonormal ℝ w ∧
        (∀ j, w j ∈ W N) ∧
        (∀ n (hn : n ≤ N) (j : Fin (k n)), w (Fin.castLE (hkmono n N hn) j) ∈ W n) ∧
        lev ≤ ‖exteriorPower.map (k N) P (exteriorPower.ιMulti ℝ (k N) w)‖ := by
  intro N
  induction N with
  | zero =>
    intro hfam hpos
    obtain ⟨a, hON, hW, hdom⟩ := hfam 0 le_rfl
    refine ⟨a, c, hc, le_rfl, hON, hW, ?_, hdom⟩
    intro n hn j
    have hn0 : n = 0 := Nat.le_zero.mp hn
    subst hn0
    simpa using hW j
  | succ N ih =>
    intro hfam hpos
    have hfamN : ∀ n ≤ N, ∃ a : Fin (k n) → RD d, Orthonormal ℝ a ∧ (∀ j, a j ∈ W n) ∧
        c ≤ ‖exteriorPower.map (k n) P (exteriorPower.ιMulti ℝ (k n) a)‖ :=
      fun n hn => hfam n (le_trans hn (Nat.le_succ N))
    obtain ⟨w, lev, hlevpos, hlevc, hON, hW, hfilter, hdom⟩ := ih hfamN hpos
    obtain ⟨u, huON, huW, hudom⟩ := hfam (N + 1) le_rfl
    have heW : ∀ j : Fin (k N), w j ∈ W (N + 1) :=
      fun j => hmono N (N + 1) (Nat.le_succ N) (hW j)
    have hm0 : 1 ≤ k N := le_trans hpos (hkmono 0 N (Nat.zero_le N))
    obtain ⟨e', lev', hlev'pos, hlev'c, he'ON, he'W, he'ext, he'dom⟩ :=
      exists_dominated_extension (hstrict N) hm0 P hP hON heW hlevpos hlevc hdom huON huW hudom
    refine ⟨e', lev', hlev'pos, hlev'c, he'ON, he'W, ?_, he'dom⟩
    intro n hn j
    rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le hn) with hlt | heq
    · have hlt' : n ≤ N := Nat.lt_succ_iff.mp hlt
      have hcast : Fin.castLE (hkmono n (N + 1) hn) j =
          Fin.castLE (hkmono N (N + 1) (Nat.le_succ N))
            (Fin.castLE (hkmono n N hlt') j) :=
        castLE_trans (hkmono n N hlt') (hkmono N (N + 1) (Nat.le_succ N)) j
      rw [hcast, he'ext]
      exact hfilter n hlt' j
    · subst heq
      exact he'W j

end Submission.BatchAccumulation

end
