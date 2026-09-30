import Mathlib
import Submission.Work.BMF.recursion.LinnikDefs
import Submission.Work.BMF.N4chain.newton_eval
import Submission.Work.BMF.N4chain.linnik_newton_defs
import Submission.Work.BMF.N4chain.psumEval_eq_of_dvd
import Submission.Work.BMF.N4chain.perm_of_esymmEval

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.recursion

open Finset

/-! ### Two elementary auxiliary facts -/

/-- The map sending a residue `x : Fin N` to `(x.val : ZMod p)` is injective on the residues
`< p`. -/
theorem fin_val_zmod_inj_of_lt {p N : ℕ} {x y : Fin N} (hx : x.val < p) (hy : y.val < p)
    (h : ((x.val : ℕ) : ZMod p) = ((y.val : ℕ) : ZMod p)) : x = y := by
  apply Fin.ext
  have h' := (ZMod.natCast_eq_natCast_iff' x.val y.val p).mp h
  rwa [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at h'

/-- **Newton's identities determine the elementary symmetric functions from the power sums.**
If two tuples of residues modulo a prime `p` have the same power sums of orders `1, …, k`
(with `k < p`, so that every `1 ≤ m ≤ k` is invertible mod `p`), then they have the same
elementary symmetric functions of orders `0, …, k`. -/
theorem esymmEval_eq_of_psumEval_eq {p k : ℕ} (hp : p.Prime) (hk : k < p)
    {v w : Fin k → ZMod p}
    (h : ∀ j, 1 ≤ j → j ≤ k →
      Work.BMF.N4chain.psumEval v j = Work.BMF.N4chain.psumEval w j) :
    ∀ m, m ≤ k → Work.BMF.N4chain.esymmEval v m = Work.BMF.N4chain.esymmEval w m := by
  haveI : Fact p.Prime := ⟨hp⟩
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm
    rcases Nat.eq_zero_or_pos m with hm0 | hmpos
    · subst hm0
      rw [Work.BMF.N4chain.esymmEval, Work.BMF.N4chain.esymmEval,
        MvPolynomial.aeval_esymm_eq_multiset_esymm, MvPolynomial.aeval_esymm_eq_multiset_esymm]
      simp
    · -- `(m : ZMod p) ≠ 0`, as `1 ≤ m ≤ k < p`
      have hmne : (m : ZMod p) ≠ 0 := by
        intro hcon
        have hcon' : ((m : ℕ) : ZMod p) = ((0 : ℕ) : ZMod p) := by rw [hcon, Nat.cast_zero]
        have h' := (ZMod.natCast_eq_natCast_iff' m 0 p).mp hcon'
        simp only [Nat.zero_mod] at h'
        have hlt : m < p := lt_of_le_of_lt hm hk
        rw [Nat.mod_eq_of_lt hlt] at h'
        omega
      -- the right hand sides of Newton's identity agree
      have hsum : ∑ i ∈ Finset.range m,
            (-1) ^ i * Work.BMF.N4chain.esymmEval v i * Work.BMF.N4chain.psumEval v (m - i)
          = ∑ i ∈ Finset.range m,
            (-1) ^ i * Work.BMF.N4chain.esymmEval w i * Work.BMF.N4chain.psumEval w (m - i) := by
        refine Finset.sum_congr rfl fun i hi => ?_
        have hi_lt : i < m := Finset.mem_range.mp hi
        have hik : i ≤ k := le_trans (le_of_lt hi_lt) hm
        have he : Work.BMF.N4chain.esymmEval v i = Work.BMF.N4chain.esymmEval w i :=
          ih i hi_lt hik
        have h1 : 1 ≤ m - i := by omega
        have h2 : m - i ≤ k := by omega
        rw [he, h (m - i) h1 h2]
      have hv := Work.BMF.N4chain.newton_eval v m
      have hw := Work.BMF.N4chain.newton_eval w m
      have hmul : (m : ZMod p) * Work.BMF.N4chain.esymmEval v m
          = (m : ZMod p) * Work.BMF.N4chain.esymmEval w m := by
        rw [hv, hw, hsum]
      exact mul_left_cancel₀ hmne hmul

/-- The tuple of residues modulo `p` attached to a tuple `b : Fin k → Fin (p^1)`. -/
private def vz {p k : ℕ} (b : Fin k → Fin (p ^ 1)) : Fin k → ZMod p :=
  fun i => ((b i).val : ZMod p)

/-- **Linnik: the residue count at level one.**  `Lvl p k 1 H` (see
`Submission/Work/BMF/recursion/LinnikDefs.lean`) is the set of `b : Fin k → Fin p` whose entries
are pairwise distinct modulo `p` and whose power sums satisfy `p ∣ ∑ᵢ bᵢ^j - H j` for every
`1 ≤ j ≤ k`.  Its cardinality is at most `k!`.

Route (work in the field `ZMod p`, `haveI : Fact p.Prime := ⟨hp⟩`).

1. For `b` in the set and `1 ≤ j ≤ k`, the divisibility hypothesis gives
   `psumEval (v b) j = (H j : ZMod p)` in `ZMod p`, where `v b : Fin k → ZMod p` is
   `fun i => (b i).val` (use `ZMod.intCast_zmod_eq_zero_iff_dvd`; `Work.BMF.N4chain.psumEval`
   is `∑ i, (v i)^j`).  Hence all elements of the set have the same `psumEval` values.

2. Newton's identity modulo `p` (`Work.BMF.N4chain.newton_eval`, in
   `Submission/Work/BMF/N4chain/newton_eval.lean`) says
   `(m : ZMod p) * esymmEval v m = (-1)^(m+1) * ∑ i ∈ Finset.range m, (-1)^i * esymmEval v i * psumEval v (m - i)`
   (`Work.BMF.N4chain.esymmEval v m = MvPolynomial.aeval v (MvPolynomial.esymm (Fin k) (ZMod p) m)`).
   Induct on `m` up to `k`: the factor `(m : ZMod p)` is nonzero (indeed invertible) because
   `1 ≤ m ≤ k < p` and `p` is prime, so all `esymmEval` values up to `k` are the same for any
   two elements of the set (also `esymmEval · 0 = 1` on both sides).

3. If `v, v' : Fin k → ZMod p` have equal `esymmEval · m` for all `m ≤ k`, then they are
   permutations of each other: with `polyOf v = ∏ i, (X - C (v i))`
   (`Work.BMF.N4chain.polyOf`) and Vieta's formula
   (`Multiset.prod_X_sub_X_eq_sum_esymm`, together with
   `MvPolynomial.aeval_esymm_eq_multiset_esymm` to identify `esymmEval v m` with the multiset
   `esymm` of `Finset.univ.val.map v`), the two polynomials `polyOf v` and `polyOf v'` are equal;
   evaluating at `v' i` gives `∏ r, (v' i - v r) = 0`, and `ZMod p` being a domain
   (`Finset.prod_eq_zero_iff`) yields `r` with `v' i = v r`.  Since `val` is injective on
   `Fin p`, this gives `σ : Fin k → Fin k` with `b' i = b (σ i)`; `σ` is injective because `b'`
   has pairwise distinct entries, hence a bijection.

4. Consequently, if the set is nonempty with element `b₀`, every element is `b₀ ∘ σ` for some
   `σ : Equiv.Perm (Fin k)`, so the set has at most `Fintype.card (Equiv.Perm (Fin k)) =
   k.factorial` elements; if it is empty, its cardinality is `0`. -/
theorem linnik_lvl_one (p k : ℕ) (hp : p.Prime) (hk : k < p) (H : ℕ → ℕ) :
    (Work.BMF.recursion.Lvl p k 1 H).card ≤ k.factorial := by
  classical
  by_cases hne : (Lvl p k 1 H).Nonempty
  · obtain ⟨b₀, hb₀⟩ := hne
    -- the residue tuples of elements of `Lvl` are injective
    have vz_inj : ∀ b ∈ Lvl p k 1 H, Function.Injective (vz b) := by
      intro b hb i j hij
      by_contra hne'
      exact (Finset.mem_filter.mp hb).2.1 i j hne' hij
    -- the modulus in the defining congruence
    have hdiv : ∀ (c : Fin k → Fin (p^1)) (hc : c ∈ Lvl p k 1 H) (j : ℕ), 1 ≤ j → j ≤ k →
        (p : ℤ) ∣ ((∑ i, ((c i).val : ℤ) ^ j) - (H j : ℤ)) := by
      intro c hc j hj1 hjk
      have hd := (Finset.mem_filter.mp hc).2.2 j hj1 hjk
      rw [min_eq_right hj1] at hd
      simpa using hd
    -- every element is a permutation of `b₀`
    have hperm : ∀ b ∈ Lvl p k 1 H, ∃ σ : Equiv.Perm (Fin k), ∀ i, vz b i = vz b₀ (σ i) := by
      intro b hb
      have hpsum : ∀ j, 1 ≤ j → j ≤ k →
          Work.BMF.N4chain.psumEval (vz b₀) j = Work.BMF.N4chain.psumEval (vz b) j := by
        intro j hj1 hjk
        show Work.BMF.N4chain.psumEval (fun i => ((b₀ i).val : ZMod p)) j
          = Work.BMF.N4chain.psumEval (fun i => ((b i).val : ZMod p)) j
        rw [Work.BMF.N4chain.psumEval_eq_of_dvd b₀ H j (hdiv b₀ hb₀ j hj1 hjk),
          Work.BMF.N4chain.psumEval_eq_of_dvd b H j (hdiv b hb j hj1 hjk)]
      exact Work.BMF.N4chain.perm_of_esymmEval hp (vz_inj b hb)
        (esymmEval_eq_of_psumEval_eq hp hk hpsum)
    have hlt : ∀ (b : Fin k → Fin (p^1)) (i : Fin k), (b i).val < p := by
      intro b i
      exact lt_of_lt_of_eq (b i).isLt (pow_one p)
    -- the injection into `Equiv.Perm (Fin k)`
    let Φ : (Lvl p k 1 H) → Equiv.Perm (Fin k) := fun b => Classical.choose (hperm b.1 b.2)
    have hΦ : ∀ b : (Lvl p k 1 H), ∀ i, vz b.1 i = vz b₀ (Φ b i) :=
      fun b => Classical.choose_spec (hperm b.1 b.2)
    have hinj : Function.Injective Φ := by
      intro b b' hbb'
      have h1 : ∀ i, vz b.1 i = vz b'.1 i := by
        intro i; rw [hΦ b i, hΦ b' i, hbb']
      have h2 : b.1 = b'.1 := by
        funext i
        exact fin_val_zmod_inj_of_lt (hlt b.1 i) (hlt b'.1 i) (h1 i)
      exact Subtype.ext h2
    have hcard := Fintype.card_le_of_injective Φ hinj
    rw [Fintype.card_coe, Fintype.card_perm, Fintype.card_fin] at hcard
    exact hcard
  · have h0 : (Lvl p k 1 H).card = 0 :=
      Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hne)
    rw [h0]; exact Nat.zero_le _

end Work.BMF.recursion
