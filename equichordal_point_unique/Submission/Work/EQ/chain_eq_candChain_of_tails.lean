import Mathlib
import Submission.Work.EQ.DefsCore
import Submission.Work.EQ.CycleDefs
import Submission.Work.EQ.H0_invParam_ge
import Submission.Work.EQ.HeteroAlgebra

namespace Work.EQ

open Complex Filter _root_.Topology

noncomputable section

/-!
## Reading a chain off its two tails

The pieces the assembly below needs: the branch letters of the forward word of a chain, the
description of the index-`m` point by the `m`-th suffix of that word, and the same description
for the *unstable* tail, which is read through the mirror chain.  These are the elementary
combinatorial facts (the analytic content of Rychlik's reading step is `fan` itself).

The vocabulary is kept local (`bltr`/`fwdW`/`bwdW` here are the `bLetter`/`fanWord`/`bwdWord` of
`Submission/Work/EQ/limit_analysis.lean`) so that this file rests only on the stable core
(`DefsCore`, `CycleDefs`, `H0_invParam_ge`, `HeteroAlgebra`).
-/

/-! ### The fan restated one letter at a time -/

/-- The stable fan at the empty word: the germ (definitional unfolding). -/
theorem fan_nil' (a : ℝ) (h : ℂ → ℂ) (u : ℂ) : fan a h [] u = germC a h u := rfl

/-- The stable fan one letter at a time (definitional unfolding). -/
theorem fan_cons' (a : ℝ) (h : ℂ → ℂ) (s : Bool) (ε : List Bool) (u : ℂ) :
    fan a h (s :: ε) u = invBranch a s (fan a h ε ((eqLam a : ℂ) * u)) := rfl

/-! ### Branch letters and words -/

/-- The branch letter of a pair `(P,Q)`: `true` when `P` is the principal backward image of
`Q`, `false` when it is the other one. -/
noncomputable def bltr (a : ℝ) (P Q : ℂ × ℂ) : Bool :=
  if _ : P = invBranch a true Q then true
  else if _ : P = invBranch a false Q then false
  else true

/-- On a regular pair the letter names the branch. -/
theorem bltr_spec {a : ℝ} {P Q : ℂ × ℂ}
    (h : P = invBranch a true Q ∨ P = invBranch a false Q) :
    P = invBranch a (bltr a P Q) Q := by
  rcases h with h' | h'
  · unfold bltr
    rw [dif_pos h']
    exact h'
  · unfold bltr
    by_cases h1 : P = invBranch a true Q
    · rw [dif_pos h1]; exact h1
    · rw [dif_neg h1, dif_pos h']; exact h'

/-- **The forward word** of length `N` of a chain: the branch letters of its first `N` steps. -/
noncomputable def fwdW (a : ℝ) : ℕ → ChainData → List Bool
  | 0, _ => []
  | n + 1, p => bltr a (p.1 0) (p.1 1) :: fwdW a n (shiftZ a 1 p)

theorem fwdW_length (a : ℝ) : ∀ (N : ℕ) (p : ChainData), (fwdW a N p).length = N := by
  intro N
  induction N with
  | zero => intro p; simp [fwdW]
  | succ N ih => intro p; simp [fwdW, ih]

/-- The `j`-th backward letter of a chain. -/
noncomputable def bwdL (a : ℝ) (p : ChainData) (j : ℕ) : Bool :=
  bltr a (p.1 (-((j : ℤ) + 1))) (p.1 (-(j : ℤ)))

/-- **The backward word** of length `N` of a chain: the branch letters of its first `N` backward
steps. -/
noncomputable def bwdW (a : ℝ) (N : ℕ) (p : ChainData) : List Bool :=
  (List.range N).map (bwdL a p)

theorem bwdW_length (a : ℝ) (N : ℕ) (p : ChainData) : (bwdW a N p).length = N := by
  simp [bwdW]

theorem bwdP_singleton' (a : ℝ) (t : Bool) (P : ℂ × ℂ) : bwdP a [t] P = invBranch a t P := by
  simp [bwdP]

theorem bwdW_take_succ (a : ℝ) (N : ℕ) (p : ChainData) {j : ℕ} (hj : j < N) :
    (bwdW a N p).take (j + 1) = (bwdW a N p).take j ++
      [bltr a (p.1 (-((j : ℤ) + 1))) (p.1 (-(j : ℤ)))] := by
  have hlen : j < (bwdW a N p).length := by rw [bwdW_length]; exact hj
  rw [(List.take_append_getElem (l := bwdW a N p) (i := j) hlen).symm]
  congr 1
  simp only [bwdW, bwdL, List.getElem_map, List.getElem_range]

/-- **The unstable word of a chain.** The index `-j` point of a chain is the iterated backward
image of its index-`0` point along its backward word of length `N`. -/
theorem bwdP_bwdW_take {a : ℝ} {h : ℂ → ℂ} {N : ℕ} {p : ChainData} (hp : IsChain a h p) :
    ∀ j : ℕ, j ≤ N → p.1 (-(j : ℤ)) = bwdP a ((bwdW a N p).take j) (p.1 0) := by
  intro j
  induction j with
  | zero => intro _; simp
  | succ j ih =>
    intro hj
    have hj' : j ≤ N := le_of_lt (Nat.lt_of_succ_le hj)
    have hlt : j < N := Nat.lt_of_succ_le hj
    have hpair : RegPair a (p.1 (-((j : ℤ) + 1))) (p.1 (-(j : ℤ))) := by
      have h := hp.1 (-((j : ℤ) + 1))
      have hidx : -((j : ℤ) + 1) + 1 = -(j : ℤ) := by ring
      rwa [hidx] at h
    rw [show (-(↑(j + 1) : ℤ)) = -((j : ℤ) + 1) by push_cast; ring]
    rw [bwdW_take_succ a N p hlt, bwdP_append, bwdP_singleton', ← ih hj']
    exact bltr_spec (eqRelC_solutions hpair.1 hpair.2.2)

/-! ### Reading the forward tail -/

/-- `(x :: l).drop (n+1) = l.drop n` (definitional). -/
theorem drop_succ_cons' {α : Type*} (x : α) (l : List α) (n : ℕ) :
    (x :: l).drop (n + 1) = l.drop n := rfl

/-- The `j`-th letter of the forward word splits the word at `j` (for `j < N`): the `j`-th step
letter is the head of the `j`-th suffix. -/
theorem fwdW_drop_cons (a : ℝ) : ∀ (N : ℕ) (p : ChainData) (j : ℕ), j < N →
    (fwdW a N p).drop j =
      bltr a (p.1 (j : ℤ)) (p.1 ((j : ℤ) + 1)) :: (fwdW a N p).drop (j + 1) := by
  intro N
  induction N with
  | zero => intro p j hj; omega
  | succ N ih =>
    intro p j hj
    have hf : fwdW a (N + 1) p =
        bltr a (p.1 0) (p.1 1) :: fwdW a N (shiftZ a 1 p) := rfl
    rcases Nat.eq_zero_or_pos j with h0 | hpos
    · subst h0
      rw [List.drop_zero, hf, drop_succ_cons']
      congr 1
    · obtain ⟨j', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
      have hj' : j' < N := by omega
      rw [hf, drop_succ_cons', ih (shiftZ a 1 p) j' hj']
      congr 1 <;> simp only [shiftZ_fst] <;> push_cast <;> ring

/-- **Reading a chain from its tail.**  If the index-`N` point of a chain is the germ value
`germC a h (λ^N ψ₁)`, then for every `m ≤ N` the index-`m` point is the fan value of the `m`-th
suffix of the forward word: `p.1 m = fan a h ((fwdW a N p).drop m) (λ^m ψ₁)`. -/
theorem chain_reading_of_tail {a : ℝ} {h : ℂ → ℂ} {N : ℕ} {p : ChainData}
    (hp : IsChain a h p)
    (htail : p.1 (N : ℤ) = germC a h (((eqLam a : ℝ) : ℂ) ^ N * p.2.1)) :
    ∀ m : ℕ, m ≤ N →
      p.1 (m : ℤ) = fan a h ((fwdW a N p).drop m) (((eqLam a : ℝ) : ℂ) ^ m * p.2.1) := by
  have hlen : (fwdW a N p).length = N := fwdW_length a N p
  have key : ∀ k m : ℕ, m + k = N →
      p.1 (m : ℤ) = fan a h ((fwdW a N p).drop m)
        (((eqLam a : ℝ) : ℂ) ^ m * p.2.1) := by
    intro k
    induction k with
    | zero =>
      intro m hm
      have hmN : m = N := by omega
      subst hmN
      rw [htail, List.drop_eq_nil_of_le (by rw [hlen]), fan_nil']
    | succ k ih =>
      intro m hm
      have hmN : m < N := by omega
      have hih := ih (m + 1) (by omega)
      have hidx : ((m + 1 : ℕ) : ℤ) = (m : ℤ) + 1 := by push_cast; ring
      rw [hidx] at hih
      have hspec := bltr_spec (eqRelC_solutions (hp.1 (m : ℤ)).1 (hp.1 (m : ℤ)).2.2)
      have hdrop := fwdW_drop_cons a N p m hmN
      have hpow : (eqLam a : ℂ) * (((eqLam a : ℝ) : ℂ) ^ m * p.2.1)
          = (((eqLam a : ℝ) : ℂ) ^ (m + 1)) * p.2.1 := by
        rw [pow_succ]; ring
      have hih' : p.1 ((m : ℤ) + 1) = fan a h ((fwdW a N p).drop (m + 1))
          ((eqLam a : ℂ) * (((eqLam a : ℝ) : ℂ) ^ m * p.2.1)) := by
        rw [hpow]
        exact hih
      rw [hdrop, fan_cons']
      conv_lhs => rw [hspec]
      rw [← hih']
  intro m hm
  exact key (N - m) m (by omega)

/-! ### Reading the unstable tail -/

/-- The bisector reflection is an involution. -/
theorem eqMirror_invol (P : ℂ × ℂ) : eqMirror (eqMirror P) = P := by
  ext <;> simp [eqMirror]

/-- **Reading the unstable tail.**  Let `p` be a chain whose backward tail is the unstable germ
from depth `N` on, and put `q := shiftZ a N (mirrorChain p)` (the mirror of `p` shifted by `N`: a
chain whose forward tail is the stable germ from depth `0` on, with `ψ₁ = λ^N ψ₂`).  Then for
every `m ≤ N` the index-`m` point of `q`, namely `germC a h (λ^{N+m} ψ₂)`, is the fan value of
the `m`-th suffix of the forward word of `q`:
`fan a h ((fwdW a N q).drop m) (λ^{N+m} ψ₂) = germC a h (λ^{N+m} ψ₂)`. -/
theorem unstable_reading {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {N : ℕ}
    {p : ChainData} (hp : IsChain a h p)
    (hbwd : ∀ n : ℕ, N ≤ n → p.1 (-(n : ℤ)) = ugermC a h (((eqLam a : ℝ) : ℂ) ^ n * p.2.2)) :
    ∀ m : ℕ, m ≤ N →
      fan a h ((fwdW a N (shiftZ a N (mirrorChain p))).drop m)
          (((eqLam a : ℝ) : ℂ) ^ (N + m) * p.2.2) =
        germC a h (((eqLam a : ℝ) : ℂ) ^ (N + m) * p.2.2) := by
  have hqchain : IsChain a h (shiftZ a N (mirrorChain p)) :=
    isChain_shiftZ ha0 ha1 (isChain_mirrorChain hp) (N : ℤ)
  have htail : (shiftZ a N (mirrorChain p)).1 (N : ℤ)
      = germC a h (((eqLam a : ℝ) : ℂ) ^ N * (shiftZ a N (mirrorChain p)).2.1) := by
    have h1 : (shiftZ a N (mirrorChain p)).1 (N : ℤ)
        = germC a h (((eqLam a : ℝ) : ℂ) ^ (N + N) * p.2.2) := by
      rw [shiftZ_fst, mirrorChain_fst]
      have hidx : -((N : ℤ) + (N : ℤ)) = -(((N + N : ℕ)) : ℤ) := by push_cast; ring
      rw [hidx, hbwd (N + N) (by omega)]
      simp only [ugermC]
      rw [eqMirror_invol]
    have h2 : (((eqLam a : ℝ) : ℂ) ^ N * (shiftZ a N (mirrorChain p)).2.1)
        = (((eqLam a : ℝ) : ℂ) ^ (N + N) * p.2.2) := by
      rw [shiftZ_psi1, mirrorChain_psi1, zpow_natCast, ← mul_assoc, ← pow_add]
    rw [h1, h2]
  have hread := chain_reading_of_tail hqchain htail
  intro m hm
  have h1 := hread m hm
  have h2 : (shiftZ a N (mirrorChain p)).1 (m : ℤ)
      = germC a h (((eqLam a : ℝ) : ℂ) ^ (N + m) * p.2.2) := by
    rw [shiftZ_fst, mirrorChain_fst]
    have hidx : -((m : ℤ) + (N : ℤ)) = -(((N + m : ℕ)) : ℤ) := by push_cast; ring
    rw [hidx, hbwd (N + m) (by omega)]
    simp only [ugermC]
    rw [eqMirror_invol]
  have h3 : (((eqLam a : ℝ) : ℂ) ^ m * (shiftZ a N (mirrorChain p)).2.1)
      = (((eqLam a : ℝ) : ℂ) ^ (N + m) * p.2.2) := by
    rw [shiftZ_psi1, mirrorChain_psi1, zpow_natCast, ← mul_assoc, ← pow_add]
    rw [Nat.add_comm]
  rw [h3] at h1
  exact h1.symm.trans h2

/-! ### The assembly -/

/-- The first component of `candChain` at an index `j`, unfolded. -/
theorem candChain_fst_apply (a : ℝ) (h : ℂ → ℂ) (ε η s : List Bool) (N : ℕ) (c z : ℂ) (j : ℤ) :
    (candChain a h ε η s N c z).1 j =
      (if 0 ≤ j then
        (if j.toNat ≤ N then fan a h (ε.drop j.toNat) (((eqLam a : ℝ) : ℂ) ^ j * z)
         else germC a h (((eqLam a : ℝ) : ℂ) ^ j * z))
      else
        (if (-j).toNat ≤ N then bwdP a (s.take (-j).toNat) (fan a h ε z)
         else eqMirror (fan a h (η.drop ((-j).toNat - N))
                (((eqLam a : ℝ) : ℂ) ^ ((-j).toNat : ℤ) * (c / z))))) := rfl

/-- **A chain whose two tails are the principal leaves is a candidate chain.**

`p` is a chain of the equichordal relation (`DefsCore.IsChain`), the product `ψ = ψ₁ψ₂` of its
two linearising parameters equals `c`, and from depth `N` on both of its tails are the principal
leaves: `p.1 n = germC a h (λⁿ ψ₁)` and `p.1 (-n) = ugermC a h (λⁿ ψ₂)` for `n ≥ N`
(`ugermC = eqMirror ∘ germC`).

Claim: `p` is one of the explicit candidate chains `CycleDefs.candChain a h ε η s N c ψ₁ p` for
some words `ε, η, s` of length `N`, where `s` is the list of backward letters read off the `N`
steps from index `0` to index `-N`.

This is the purely combinatorial half of the "reading" step of Rychlik Theorem 8: the forward
word `ε` (resp. unstable word `η`) and the backward letters `s` are built by peeling one step at a
time from the tails (`H0_invParam_ge_exists_invBranch`), and the three pieces — the fan forward of
index `0`, the `bwdP` middle on `[-N,0]`, and the mirrored unstable fan below `-N` — are then
exactly `candChain`'s definition. -/
theorem chain_eq_candChain_of_tails {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {N : ℕ}
    {p : ChainData} (hp : IsChain a h p) {c : ℂ} (hval : p.2.1 * p.2.2 = c)
    (hfwd : ∀ n : ℕ, N ≤ n → p.1 (n : ℤ) = germC a h (((eqLam a : ℝ) : ℂ) ^ n * p.2.1))
    (hbwd : ∀ n : ℕ, N ≤ n → p.1 (-(n : ℤ)) = ugermC a h (((eqLam a : ℝ) : ℂ) ^ n * p.2.2)) :
    ∃ (ε η s : List Bool), ε.length = N ∧ η.length = N ∧ s.length = N ∧
      p = candChain a h ε η s N c p.2.1 := by
  refine ⟨fwdW a N p, fwdW a N (shiftZ a N (mirrorChain p)), bwdW a N p,
    fwdW_length a N p, fwdW_length a N _, bwdW_length a N p, ?_⟩
  have hz : p.2.1 ≠ 0 := hp.2.1
  have hpsi2 : c / p.2.1 = p.2.2 := by
    rw [← hval]
    exact mul_div_cancel_left₀ _ hz
  have hread := chain_reading_of_tail hp (hfwd N le_rfl)
  have hunst := unstable_reading ha0 ha1 hp hbwd
  have h0 : p.1 0 = fan a h (fwdW a N p) p.2.1 := by
    simpa using hread 0 (Nat.zero_le N)
  refine Prod.ext ?_ ?_
  · funext j
    rw [candChain_fst_apply]
    by_cases hj : 0 ≤ j
    · rw [if_pos hj]
      set m := j.toNat with hm
      have hjm : j = (m : ℤ) := by
        rw [hm]
        exact (Int.toNat_of_nonneg hj).symm
      by_cases hjc : m ≤ N
      · rw [if_pos hjc]
        have hr : p.1 (m : ℤ) = fan a h ((fwdW a N p).drop m)
            (((eqLam a : ℝ) : ℂ) ^ (m : ℤ) * p.2.1) := by
          rw [zpow_natCast]
          exact hread m hjc
        rw [hjm, hr]
      · rw [if_neg hjc]
        have hmN : N ≤ m := by omega
        have hf : p.1 (m : ℤ) = germC a h
            (((eqLam a : ℝ) : ℂ) ^ (m : ℤ) * p.2.1) := by
          rw [zpow_natCast]
          exact hfwd m hmN
        rw [hjm, hf]
    · rw [if_neg hj]
      set k := (-j).toNat with hk
      have h2 : ((k : ℕ) : ℤ) = -j := by
        rw [hk]
        exact Int.toNat_of_nonneg (by omega)
      have hjk : j = -((k : ℕ) : ℤ) := by
        rw [h2]; ring
      by_cases hkc : k ≤ N
      · rw [if_pos hkc]
        rw [hjk, bwdP_bwdW_take hp k hkc, h0]
      · rw [if_neg hkc]
        have hkN : N ≤ k := by omega
        have hb := hbwd k hkN
        have heta : eqMirror (fan a h ((fwdW a N (shiftZ a N (mirrorChain p))).drop (k - N))
            (((eqLam a : ℝ) : ℂ) ^ (k : ℤ) * (c / p.2.1)))
            = eqMirror (germC a h (((eqLam a : ℝ) : ℂ) ^ k * p.2.2)) := by
          rw [hpsi2, zpow_natCast]
          congr 1
          by_cases hle : k - N ≤ N
          · have h := hunst (k - N) hle
            rwa [show N + (k - N) = k from by omega] at h
          · rw [List.drop_eq_nil_of_le (by rw [fwdW_length]; omega), fan_nil']
        rw [hjk, hb]
        simp only [ugermC]
        rw [heta]
  · refine Prod.ext ?_ ?_
    · rfl
    · exact hpsi2.symm

end

end Work.EQ
