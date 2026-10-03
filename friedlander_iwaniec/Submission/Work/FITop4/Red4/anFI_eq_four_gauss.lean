import Mathlib
import Submission.Work.FITop4.Defs4
import Submission.Work.FITop4.Red4.gauss_factorization

namespace Work.FITop4.Red4

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## Counting the integer square roots of `b` with `Zint`

`Zint b` is (`0` for `b < 0` and) the number of integer `c` with `c² = b`; the two lemmas below
make this identification, first for the underlying `Zb` on `ℕ` and then for `Zint` on `ℤ`. -/

/-- `Nat.sqrt` recognises perfect squares. -/
lemma sqrt_sq_eq_of_exists_sq {k : ℕ} (h : ∃ d, d ^ 2 = k) : Nat.sqrt k ^ 2 = k := by
  obtain ⟨d, rfl⟩ := h
  rw [Nat.sqrt_eq']

/-- `Zb k` counts the integer square roots of `k`. -/
lemma Zb_eq_ncard (k : ℕ) : Work.FIPlan.Zb k = ({c : ℤ | c ^ 2 = (k : ℤ)}).ncard := by
  rw [Work.FIPlan.Zb]
  by_cases hk : k = 0
  · subst hk
    rw [if_pos rfl]
    have : ({c : ℤ | c ^ 2 = ((0:ℕ):ℤ)} : Set ℤ) = {0} := by
      ext c; simp
    rw [this, Set.ncard_singleton]
  · rw [if_neg hk]
    by_cases hsq : Nat.sqrt k ^ 2 = k
    · rw [if_pos hsq]
      set d : ℤ := (Nat.sqrt k : ℤ) with hd
      have hdk : d ^ 2 = (k : ℤ) := by rw [hd]; exact_mod_cast hsq
      have hd0 : d ≠ 0 := by
        intro h
        have h1 : Nat.sqrt k = 0 := by rw [hd] at h; exact_mod_cast h
        rw [h1] at hsq; exact hk hsq.symm
      have hset : ({c : ℤ | c ^ 2 = (k : ℤ)} : Set ℤ) = {d, -d} := by
        ext c
        simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
        rw [← hdk]
        exact sq_eq_sq_iff_eq_or_eq_neg
      rw [hset, Set.ncard_pair (by omega)]
    · rw [if_neg hsq]
      have hset : ({c : ℤ | c ^ 2 = (k : ℤ)} : Set ℤ) = ∅ := by
        ext c
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        intro hc
        apply hsq
        apply sqrt_sq_eq_of_exists_sq
        refine ⟨c.natAbs, ?_⟩
        have := congrArg Int.natAbs hc
        rw [Int.natAbs_pow, Int.natAbs_natCast] at this
        exact this
      rw [hset, Set.ncard_empty]

/-- `Zint b` counts the integer square roots of `b` (with `Zint b = 0` for `b < 0`, where there
are none). -/
lemma Zint_eq_ncard (b : ℤ) : Work.FIPlan.Zint b = ({c : ℤ | c ^ 2 = b}).ncard := by
  rw [Work.FIPlan.Zint]
  by_cases hb : b < 0
  · rw [if_pos hb]
    have hset : ({c : ℤ | c ^ 2 = b} : Set ℤ) = ∅ := by
      ext c
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      intro hc
      have hnn : (0:ℤ) ≤ c ^ 2 := by positivity
      rw [hc] at hnn; linarith
    rw [hset, Set.ncard_empty]
  · rw [if_neg hb]
    have hb0 : 0 ≤ b := not_lt.mp hb
    rw [Zb_eq_ncard b.natAbs]
    have hset : ({c : ℤ | c ^ 2 = ((b.natAbs : ℕ) : ℤ)} : Set ℤ) = {c : ℤ | c ^ 2 = b} := by
      rw [Int.natAbs_of_nonneg hb0]
    rw [hset]

/-! ## The box truncation of `Zint` -/

/-- `|z| ≤ z ^ 2` for an integer. -/
lemma int_abs_le_sq (z : ℤ) : |z| ≤ z ^ 2 := by
  rcases eq_or_ne z 0 with h | h
  · simp [h]
  · have h1 : 1 ≤ |z| := Int.one_le_abs h
    have h2 : |z| ^ 2 = z ^ 2 := sq_abs z
    nlinarith [h1, h2, abs_nonneg z]

/-- `|z| ≤ z ^ 4` for an integer. -/
lemma int_abs_le_pow_four (z : ℤ) : |z| ≤ z ^ 4 := by
  rcases eq_or_ne z 0 with h | h
  · simp [h]
  · have h1 : 1 ≤ |z| := Int.one_le_abs h
    have h2 : |z| ^ 4 = z ^ 4 := by
      have hs : |z| ^ 2 = z ^ 2 := sq_abs z
      calc |z| ^ 4 = (|z| ^ 2) ^ 2 := by ring
        _ = (z ^ 2) ^ 2 := by rw [hs]
        _ = z ^ 4 := by ring
    have h3 : |z| ^ 1 ≤ |z| ^ 4 := pow_le_pow_right₀ h1 (by norm_num)
    rw [pow_one] at h3
    linarith [h2, h3]

/-- If `b ≤ N` then every integer square root of `b` lies in the interval `[-N, N]`, so that
`Zint b` is the number of roots found in that box. -/
lemma Zint_eq_card_roots {N : ℕ} {b : ℤ} (hb : b ≤ (N : ℤ)) :
    Work.FIPlan.Zint b = ((Finset.Icc (-(N : ℤ)) (N : ℤ)).filter (fun c => c ^ 2 = b)).card := by
  rw [Zint_eq_ncard]
  have hset : ({c : ℤ | c ^ 2 = b} : Set ℤ)
      = ↑(((Finset.Icc (-(N : ℤ)) (N : ℤ)).filter (fun c => c ^ 2 = b)) : Finset ℤ) := by
    ext c
    simp only [Set.mem_ofPred_eq, Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · intro hc
      have hc2 : c ^ 2 ≤ (N : ℤ) := hc ▸ hb
      have habs : |c| ≤ (N : ℤ) := le_trans (int_abs_le_sq c) hc2
      exact ⟨⟨(abs_le.mp habs).1, (abs_le.mp habs).2⟩, hc⟩
    · rintro ⟨-, hc⟩; exact hc
  rw [hset, Set.ncard_coe_finset]

/-! ## The lattice count for `a ^ 2 + c ^ 4 = N` -/

/-- The lattice points of the box `[-N,N]²` satisfying `a² + c⁴ = N`. -/
def F4 (N : ℕ) : Finset (ℤ × ℤ) :=
  ((Finset.Icc (-(N:ℤ)) (N:ℤ)) ×ˢ (Finset.Icc (-(N:ℤ)) (N:ℤ))).filter
    (fun x => x.1 ^ 2 + x.2 ^ 4 = (N:ℤ))

/-- `anFI N` is the cardinality of `F4 N`: every solution of `a² + c⁴ = N` has `|a|, |c| ≤ N`. -/
lemma anFI_eq_card_F4 (N : ℕ) : Work.FIPlan.anFI N = (F4 N).card := by
  unfold Work.FIPlan.anFI
  rw [← Set.ncard_coe_finset (F4 N)]
  congr 1
  ext x
  simp only [Set.mem_ofPred_eq, Finset.mem_coe]
  constructor
  · intro hx
    refine Finset.mem_filter.mpr ⟨?_, hx⟩
    rw [Finset.mem_product]
    have h1 : x.1 ^ 2 ≤ (N:ℤ) := by linarith [show (0:ℤ) ≤ x.2 ^ 4 by positivity, hx]
    have h2 : x.2 ^ 4 ≤ (N:ℤ) := by linarith [show (0:ℤ) ≤ x.1 ^ 2 by positivity, hx]
    exact ⟨Finset.mem_Icc.mpr (abs_le.mp (le_trans (int_abs_le_sq x.1) h1)),
           Finset.mem_Icc.mpr (abs_le.mp (le_trans (int_abs_le_pow_four x.2) h2))⟩
  · intro hx
    exact (Finset.mem_filter.mp hx).2

/-- Counting the points `(a, c)` of `F4 N` by the pair `p = (a, c²)` in `targetF N`: the fibre
of `p` is the set of square roots of `p.2`, of cardinality `Zint p.2` (paper (5.2)). -/
lemma F4_card_eq_sum {N : ℕ} (hN : 1 ≤ N) :
    (F4 N).card = ∑ p ∈ Commons.NumberTheory.GaussianInt.targetF N, Work.FIPlan.Zint p.2 := by
  have hmap : Set.MapsTo (fun x : ℤ × ℤ => (x.1, x.2 ^ 2)) ↑(F4 N)
      ↑(Commons.NumberTheory.GaussianInt.targetF N) := by
    intro x hx
    rw [Finset.mem_coe] at hx
    rw [Finset.mem_coe, Commons.NumberTheory.GaussianInt.mem_targetF hN]
    have h := (Finset.mem_filter.mp hx).2
    have : x.2 ^ 4 = (x.2 ^ 2) ^ 2 := by ring
    linarith [h, this]
  rw [Finset.card_eq_sum_card_fiberwise hmap]
  apply Finset.sum_congr rfl
  intro p hp
  have hp' : p.1 ^ 2 + p.2 ^ 2 = (N:ℤ) :=
    (Commons.NumberTheory.GaussianInt.mem_targetF hN p).mp hp
  have hp2 : |p.2| ≤ (N:ℤ) :=
    le_trans (int_abs_le_sq p.2) (by linarith [show (0:ℤ) ≤ p.1^2 by positivity, hp'])
  have hp1 : |p.1| ≤ (N:ℤ) :=
    le_trans (int_abs_le_sq p.1) (by linarith [show (0:ℤ) ≤ p.2^2 by positivity, hp'])
  rw [Zint_eq_card_roots (b := p.2) (by linarith [abs_le.mp hp2])]
  refine Finset.card_bij (fun x _ => x.2) ?_ ?_ ?_
  · intro x hx
    obtain ⟨hxF, hxeq⟩ := Finset.mem_filter.mp hx
    rw [Finset.mem_filter]
    exact ⟨(Finset.mem_product.mp (Finset.mem_filter.mp hxF).1).2, congrArg Prod.snd hxeq⟩
  · intro x₁ hx₁ x₂ hx₂ heq
    obtain ⟨_, heq₁⟩ := Finset.mem_filter.mp hx₁
    obtain ⟨_, heq₂⟩ := Finset.mem_filter.mp hx₂
    have h1 : x₁.1 = x₂.1 := by rw [congrArg Prod.fst heq₁, congrArg Prod.fst heq₂]
    exact Prod.ext h1 heq
  · intro c hc
    obtain ⟨hcb, hceq⟩ := Finset.mem_filter.mp hc
    refine ⟨(p.1, c), ?_, rfl⟩
    rw [Finset.mem_filter]
    refine ⟨?_, ?_⟩
    · refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ?_, ?_⟩
      · exact ⟨Finset.mem_Icc.mpr (abs_le.mp hp1), hcb⟩
      · show p.1 ^ 2 + c ^ 4 = (N : ℤ)
        have h4 : c ^ 4 = (c ^ 2) ^ 2 := by ring
        have h5 : (c ^ 2) ^ 2 = p.2 ^ 2 := by rw [hceq]
        linarith [h4, h5, hp']
    · rw [hceq]

/-- `anFI N` is the sum of `Zint` over the lattice points `p` with `p.1² + p.2² = N`. -/
lemma anFI_eq_sum_Zint {N : ℕ} (hN : 1 ≤ N) :
    (Work.FIPlan.anFI N : ℝ)
      = ∑ p ∈ Commons.NumberTheory.GaussianInt.targetF N, (Work.FIPlan.Zint p.2 : ℝ) := by
  have hnat : Work.FIPlan.anFI N
      = ∑ p ∈ Commons.NumberTheory.GaussianInt.targetF N, Work.FIPlan.Zint p.2 := by
    rw [anFI_eq_card_F4, F4_card_eq_sum hN]
  rw [hnat]
  push_cast
  rfl

/-! ## The paper's (5.2) -/

theorem anFI_eq_four_gauss {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) (hcop : Nat.Coprime m n) :
    (Work.FIPlan.anFI (m * n) : ℝ)
      = (1 / 4) * (∑ w ∈ (Work.FIPlan.gBox ((m : ℕ) : ℤ)).filter (fun w => Work.FIPlan.gnorm w = m),
          ∑ z ∈ (Work.FIPlan.gBox ((n : ℕ) : ℤ)).filter (fun z => Work.FIPlan.gnorm z = n),
            (Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℝ)) := by
  have hmn : 1 ≤ m * n := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have hkey := gauss_factorization hm hn hcop (fun b : ℤ => (Work.FIPlan.Zint b : ℝ))
  have hsum : (∑ w ∈ (Work.FIPlan.gBox ((m : ℕ) : ℤ)).filter (fun w => Work.FIPlan.gnorm w = m),
          ∑ z ∈ (Work.FIPlan.gBox ((n : ℕ) : ℤ)).filter (fun z => Work.FIPlan.gnorm z = n),
            (Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℝ))
      = 4 * ∑ p ∈ Commons.NumberTheory.GaussianInt.targetF (m * n),
            (Work.FIPlan.Zint p.2 : ℝ) := by
    simpa [Commons.NumberTheory.GaussianInt.targetF] using hkey
  rw [anFI_eq_sum_Zint hmn, hsum]
  ring

end

end Work.FITop4.Red4
