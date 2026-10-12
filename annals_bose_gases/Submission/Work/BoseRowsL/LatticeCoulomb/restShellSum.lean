import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Star
import Mathlib.Data.Real.Basic
import Mathlib.Order.Lattice.Nat
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Algebra.Order.Ring.Star
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseRowsL.LatticeCoulomb.restShellSum`

The shell sum over the two "rest" coordinates of a lattice vector of `ℤ³`.

For `j : Fin 3` consider the functions `q : {i : Fin 3 // i ≠ j} → ℤ` whose two values lie in
the interval `[-N,N]`, and sum a function `φ` of the `ℓ^∞`-norm `max_i |q i|` over all of them.
Grouping the terms by the value `M` of that maximum gives

`∑_q φ (max_i |q i|) = φ 0 + ∑_{M=1}^{N} 8M φ M`,

because the number of pairs `(a,b)` with `max(|a|,|b|) = M ≥ 1` is
`(2M+1)² − (2M−1)² = 8M`, and exactly one pair (the zero one) has maximum `0`.

The counting is carried out for an arbitrary finite index type `α` (with `card α = 2`),
in the shells `SF`; the theorem `restShellSum` is then the case `α = {i : Fin 3 // i ≠ j}`.
-/

namespace Work.BoseRowsL.LatticeCoulomb

open Finset

noncomputable section

section Shell

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- `SF k` is the set of functions `q : α → ℤ` all of whose values lie in `[-k,k]`. -/
private def SF (k : ℕ) : Finset (α → ℤ) :=
  Fintype.piFinset fun _ : α => Finset.Icc (-(k : ℤ)) (k : ℤ)

private lemma mem_SF {k : ℕ} {q : α → ℤ} :
    q ∈ SF k ↔ ∀ i, q i ∈ Finset.Icc (-(k : ℤ)) (k : ℤ) :=
  Fintype.mem_piFinset

private lemma natAbs_le_iff_nat (a : ℤ) (m : ℕ) :
    a.natAbs ≤ m ↔ -(m : ℤ) ≤ a ∧ a ≤ (m : ℤ) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have h' : (a.natAbs : ℤ) ≤ (m : ℤ) := by exact_mod_cast h
    refine ⟨?_, le_trans Int.le_natAbs h'⟩
    have h2 : ((-a).natAbs : ℤ) ≤ (m : ℤ) := by rw [Int.natAbs_neg]; exact h'
    have h3 := Int.le_natAbs (a := -a)
    rw [Int.natAbs_neg] at h3
    linarith
  · have h' : (|a| : ℤ) ≤ (m : ℤ) := abs_le.mpr h
    rwa [Int.abs_eq_natAbs, Nat.cast_le] at h'

/-- The `ℓ^∞`-norm of `q` is at most `k` exactly on the shell `SF k`. -/
private lemma sup_le_iff_mem_SF {k : ℕ} {q : α → ℤ} :
    (Finset.univ.sup fun i => (q i).natAbs) ≤ k ↔ q ∈ SF k := by
  rw [mem_SF, Finset.sup_le_iff]
  constructor
  · intro h i
    exact Finset.mem_Icc.mpr ((natAbs_le_iff_nat (q i) k).mp (h i (Finset.mem_univ i)))
  · intro h b _
    exact (natAbs_le_iff_nat (q b) k).mpr (Finset.mem_Icc.mp (h b))

/-- The shells are nested. -/
private lemma SF_mono {k N : ℕ} (h : k ≤ N) : SF (α := α) k ⊆ SF (α := α) N := by
  intro q hq
  simp only [mem_SF, Finset.mem_Icc] at hq
  simp only [mem_SF, Finset.mem_Icc]
  intro i
  have hk : (k : ℤ) ≤ (N : ℤ) := by exact_mod_cast h
  obtain ⟨h1, h2⟩ := hq i
  exact ⟨by linarith, by linarith⟩

private lemma card_SF (hα : Fintype.card α = 2) (k : ℕ) :
    (SF (α := α) k).card = (2 * k + 1) ^ 2 := by
  rw [SF, Fintype.card_piFinset]
  have h1 : ∀ i : α, (Finset.Icc (-(k : ℤ)) (k : ℤ)).card = 2 * k + 1 := by
    intro i
    rw [Int.card_Icc]
    have : (k : ℤ) + 1 - (-(k : ℤ)) = ((2 * k + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [this, Int.toNat_natCast]
  rw [Finset.prod_congr rfl (fun i _ => h1 i), Finset.prod_const, Finset.card_univ, hα]

/-- The number of `q ∈ SF N` whose `ℓ^∞`-norm is `M`, for `1 ≤ M ≤ N`. -/
private lemma card_filter_sup_eq (hα : Fintype.card α = 2) {N M : ℕ} (hM : 1 ≤ M)
    (hMN : M ≤ N) :
    (((SF (α := α) N).filter
        (fun q => (Finset.univ.sup fun i => (q i).natAbs) = M)).card) = 8 * M := by
  have hset : (SF (α := α) N).filter (fun q => (Finset.univ.sup fun i => (q i).natAbs) = M)
      = SF (α := α) M \ SF (α := α) (M - 1) := by
    ext q
    constructor
    · intro hq
      rw [Finset.mem_filter] at hq
      obtain ⟨hqN, hqM⟩ := hq
      rw [Finset.mem_sdiff]
      refine ⟨(sup_le_iff_mem_SF).mp ?_, fun h => ?_⟩
      · rw [hqM]
      · have hle := (sup_le_iff_mem_SF).mpr h
        omega
    · intro hq
      rw [Finset.mem_sdiff] at hq
      obtain ⟨hqM, hqnot⟩ := hq
      rw [Finset.mem_filter]
      refine ⟨SF_mono hMN hqM, ?_⟩
      have h1 : (Finset.univ.sup fun i => (q i).natAbs) ≤ M := (sup_le_iff_mem_SF).mpr hqM
      have h2 : ¬ ((Finset.univ.sup fun i => (q i).natAbs) ≤ M - 1) :=
        fun h => hqnot ((sup_le_iff_mem_SF).mp h)
      omega
  rw [hset, Finset.card_sdiff_of_subset (SF_mono (Nat.sub_le M 1)), card_SF hα M,
    card_SF hα (M - 1)]
  obtain ⟨M', rfl⟩ := Nat.exists_eq_add_of_le hM
  have hMm : 1 + M' - 1 = M' := by omega
  rw [hMm]
  have hsq : (2 * M' + 1) ^ 2 + 8 * (1 + M') = (2 * (1 + M') + 1) ^ 2 := by ring
  omega

/-- The number of `q ∈ SF N` whose `ℓ^∞`-norm is `0` is one: the zero function. -/
private lemma card_filter_sup_eq_zero (hα : Fintype.card α = 2) (N : ℕ) :
    ((SF (α := α) N).filter (fun q => (Finset.univ.sup fun i => (q i).natAbs) = 0)).card = 1 := by
  have hset : (SF (α := α) N).filter (fun q => (Finset.univ.sup fun i => (q i).natAbs) = 0)
      = SF (α := α) 0 := by
    ext q
    rw [Finset.mem_filter]
    constructor
    · rintro ⟨-, h⟩
      exact (sup_le_iff_mem_SF).mp (by omega)
    · intro h
      refine ⟨SF_mono (Nat.zero_le N) h, ?_⟩
      have := (sup_le_iff_mem_SF).mpr h
      omega
  rw [hset, card_SF hα 0]
  norm_num

/-- **The shell sum.**  For an index type `α` with `card α = 2`, summing `φ` of the
`ℓ^∞`-norm over the box `[-N,N]^α` groups the terms by the value of that norm. -/
private lemma sum_sup_shell (hα : Fintype.card α = 2) (N : ℕ) (φ : ℤ → ℝ) :
    (∑ q ∈ SF (α := α) N, φ ((Finset.univ.sup fun i => (q i).natAbs : ℕ)))
      = φ 0 + ∑ M ∈ Finset.Icc 1 N, (8 * (M : ℝ)) * φ (M : ℤ) := by
  classical
  have hmap : ∀ q ∈ SF (α := α) N,
      (Finset.univ.sup fun i => (q i).natAbs) ∈ Finset.Icc 0 N := by
    intro q hq
    rw [Finset.mem_Icc]
    exact ⟨Nat.zero_le _, (sup_le_iff_mem_SF).mpr hq⟩
  have key := Finset.sum_fiberwise_of_maps_to (s := SF (α := α) N) (t := Finset.Icc 0 N)
    (g := fun q : α → ℤ => Finset.univ.sup fun i => (q i).natAbs) hmap
    (fun q : α → ℤ => φ ((Finset.univ.sup fun i => (q i).natAbs : ℕ)))
  rw [← key]
  have hinner : ∀ M ∈ Finset.Icc 0 N,
      (∑ q ∈ SF (α := α) N with (Finset.univ.sup fun i => (q i).natAbs) = M,
          φ ((Finset.univ.sup fun i => (q i).natAbs : ℕ)))
        = ((((SF (α := α) N).filter
              (fun q => (Finset.univ.sup fun i => (q i).natAbs) = M)).card : ℝ) * φ (M : ℤ)) := by
    intro M _
    have hstep : ∀ q ∈ (SF (α := α) N).filter
        (fun q => (Finset.univ.sup fun i => (q i).natAbs) = M),
        φ ((Finset.univ.sup fun i => (q i).natAbs : ℕ)) = φ (M : ℤ) := by
      intro q hq
      rw [Finset.mem_filter] at hq
      rw [hq.2]
    rw [Finset.sum_congr rfl hstep, Finset.sum_const, nsmul_eq_mul]
  rw [Finset.sum_congr rfl hinner]
  have hsplit : Finset.Icc 0 N = insert 0 (Finset.Icc 1 N) := by
    ext M
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  rw [hsplit, Finset.sum_insert (by simp)]
  rw [card_filter_sup_eq_zero hα N]
  have hstep2 : ∀ M ∈ Finset.Icc 1 N,
      ((((SF (α := α) N).filter
            (fun q => (Finset.univ.sup fun i => (q i).natAbs) = M)).card : ℝ) * φ (M : ℤ))
        = (8 * (M : ℝ)) * φ (M : ℤ) := by
    intro M hM
    rw [Finset.mem_Icc] at hM
    rw [card_filter_sup_eq hα hM.1 hM.2]
    push_cast
    ring
  rw [Finset.sum_congr rfl hstep2]
  norm_num

end Shell

/-- For `j : Fin 3` there are exactly two *other* coordinates. -/
private lemma card_compl_singleton (j : Fin 3) : Fintype.card {i : Fin 3 // i ≠ j} = 2 := by
  rw [Fintype.card_subtype, Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ j),
    Finset.card_univ, Fintype.card_fin]

/-- **The rest-coordinate shell sum of `ℤ³`**: summing `φ` of the `ℓ^∞`-norm over a pair of
coordinates ranging over `[-N,N]²` collects the terms in shells of size `8M`. -/
theorem restShellSum (j : Fin 3) (N : ℕ) (φ : ℤ → ℝ) :
    (∑ q ∈ Fintype.piFinset (fun _ : {i : Fin 3 // i ≠ j} => Finset.Icc (-(N : ℤ)) (N : ℤ)),
        φ ((Finset.univ.sup fun i => (q i).natAbs : ℕ)))
      = φ 0 + ∑ M ∈ Finset.Icc 1 N, (8 * (M : ℝ)) * φ (M : ℤ) :=
  sum_sup_shell (α := {i : Fin 3 // i ≠ j}) (card_compl_singleton j) N φ

end

end Work.BoseRowsL.LatticeCoulomb
