import Mathlib
import Submission.Work.Peluse.SwapE.slotDensityAux

/-!
# `SwapE` — the two-line count from the slot points to the difference box

`slotCount q₁ q₂ M n` counts the pairs of slot points `(m, m') ∈ ([0,M))⁴` whose slot difference
is `n`, while `slotDiffCount q₁ q₂ K n` counts the pairs of *differences* `(X, Y) = (m₁ - m₁',
m₂ - m₂')` with `|X|, |Y| ≤ K` solving `q₁ X - q₂ Y = n`.  Each solution `(X, Y)` of the linear
equation arises from at most `M²` pairs of slot points (the first coordinates `m₁` and `m₂`
determine the pair), and every slot difference has `|m_i - m_i'| ≤ M - 1`, so

`slotCount q₁ q₂ M n ≤ M² · slotDiffCount q₁ q₂ (M - 1) n`.

This is the first half of the slot-density estimate (`SlotDensity`, KKL Corollary 7.2 at `ℓ = 2`):
combining it with the coset bound on the number of solutions of `q₁ X - q₂ Y = n` gives the bound
on the slot law.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Work.Peluse.SwapE

open Work.Peluse.LadderP.Swap

/-- The fibre of the pair-difference map `p ↦ (p.1.1 - p.2.1, p.1.2 - p.2.2)` has at most `M * M`
elements: the first coordinates `p.1.1` and `p.1.2` of a pair determine it. -/
private lemma card_pairDiffFiber_le (M : ℕ) (b : ℤ × ℤ) :
    ((Finset.univ : Finset ((Fin M × Fin M) × (Fin M × Fin M))).filter
      (fun p => (((p.1.1 : ℤ) - (p.2.1 : ℤ)), ((p.1.2 : ℤ) - (p.2.2 : ℤ))) = b)).card
      ≤ M * M := by
  classical
  set s : Finset ((Fin M × Fin M) × (Fin M × Fin M)) :=
    (Finset.univ : Finset ((Fin M × Fin M) × (Fin M × Fin M))).filter
      (fun p => (((p.1.1 : ℤ) - (p.2.1 : ℤ)), ((p.1.2 : ℤ) - (p.2.2 : ℤ))) = b) with hs
  have hmaps : Set.MapsTo (fun p : (Fin M × Fin M) × (Fin M × Fin M) => (p.1.1, p.1.2))
      ↑s ↑(Finset.univ : Finset (Fin M × Fin M)) := fun _ _ => Finset.mem_univ _
  have hinj : Set.InjOn (fun p : (Fin M × Fin M) × (Fin M × Fin M) => (p.1.1, p.1.2)) ↑s := by
    intro p hp q hq heq
    rw [hs] at hp hq
    have hp' := (Finset.mem_filter.mp hp).2
    have hq' := (Finset.mem_filter.mp hq).2
    obtain ⟨h11, h12⟩ := Prod.ext_iff.mp heq
    have hpf : (p.1.1 : ℤ) - (p.2.1 : ℤ) = b.1 := by
      simpa using congrArg Prod.fst hp'
    have hqf : (q.1.1 : ℤ) - (q.2.1 : ℤ) = b.1 := by
      simpa using congrArg Prod.fst hq'
    have hps : (p.1.2 : ℤ) - (p.2.2 : ℤ) = b.2 := by
      simpa using congrArg Prod.snd hp'
    have hqs : (q.1.2 : ℤ) - (q.2.2 : ℤ) = b.2 := by
      simpa using congrArg Prod.snd hq'
    have hfst : (p.1.1 : ℤ) - (p.2.1 : ℤ) = (q.1.1 : ℤ) - (q.2.1 : ℤ) := by linarith
    have hsnd : (p.1.2 : ℤ) - (p.2.2 : ℤ) = (q.1.2 : ℤ) - (q.2.2 : ℤ) := by linarith
    have h21 : p.2.1 = q.2.1 := by
      refine Fin.ext ?_
      have h1 : ((p.1.1 : ℕ) : ℤ) = ((q.1.1 : ℕ) : ℤ) := by rw [h11]
      have : ((p.2.1 : ℕ) : ℤ) = ((q.2.1 : ℕ) : ℤ) := by linarith
      exact_mod_cast this
    have h22 : p.2.2 = q.2.2 := by
      refine Fin.ext ?_
      have h1 : ((p.1.2 : ℕ) : ℤ) = ((q.1.2 : ℕ) : ℤ) := by rw [h12]
      have : ((p.2.2 : ℕ) : ℤ) = ((q.2.2 : ℕ) : ℤ) := by linarith
      exact_mod_cast this
    exact Prod.ext (Prod.ext h11 h12) (Prod.ext h21 h22)
  calc s.card ≤ (Finset.univ : Finset (Fin M × Fin M)).card :=
        Finset.card_le_card_of_injOn _ hmaps hinj
    _ = M * M := by simp [Fintype.card_prod]

theorem slotCount_le (q₁ q₂ : ℤ) (M : ℕ) (n : ℤ) :
    slotCount q₁ q₂ M n ≤ M ^ 2 * slotDiffCount q₁ q₂ (M - 1) n := by
  classical
  rw [slotCount, Finset.univ_product_univ]
  set T : Finset ((Fin M × Fin M) × (Fin M × Fin M)) :=
    (Finset.univ : Finset ((Fin M × Fin M) × (Fin M × Fin M))).filter
      (fun p => pdir q₁ q₂ p.1 - pdir q₁ q₂ p.2 = n) with hT
  set S : Finset (ℤ × ℤ) := slotDiffSet q₁ q₂ (M - 1) n with hS
  have hmaps : Set.MapsTo (fun p : (Fin M × Fin M) × (Fin M × Fin M) =>
      (((p.1.1 : ℤ) - (p.2.1 : ℤ)), ((p.1.2 : ℤ) - (p.2.2 : ℤ)))) ↑T ↑S := by
    intro p hp
    rw [hT] at hp
    obtain ⟨-, hp⟩ := Finset.mem_filter.mp hp
    rw [hS]
    simp only [Finset.mem_coe]
    rw [mem_slotDiffSet]
    simp only [Finset.mem_Icc]
    have hpdir : pdir q₁ q₂ p.1 - pdir q₁ q₂ p.2
        = q₁ * ((p.1.1 : ℤ) - (p.2.1 : ℤ)) - q₂ * ((p.1.2 : ℤ) - (p.2.2 : ℤ)) := by
      simp only [pdir]; ring
    have heq : q₁ * ((p.1.1 : ℤ) - (p.2.1 : ℤ)) - q₂ * ((p.1.2 : ℤ) - (p.2.2 : ℤ)) = n := by
      rw [← hpdir]; exact hp
    have h1 : ((p.1.1 : ℕ) : ℤ) < (M : ℤ) := by exact_mod_cast p.1.1.isLt
    have h2 : ((p.1.2 : ℕ) : ℤ) < (M : ℤ) := by exact_mod_cast p.1.2.isLt
    have h3 : ((p.2.1 : ℕ) : ℤ) < (M : ℤ) := by exact_mod_cast p.2.1.isLt
    have h4 : ((p.2.2 : ℕ) : ℤ) < (M : ℤ) := by exact_mod_cast p.2.2.isLt
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, heq⟩ <;> omega
  have hcard := Finset.card_eq_sum_card_fiberwise (s := T) (t := S)
    (f := fun p : (Fin M × Fin M) × (Fin M × Fin M) =>
      (((p.1.1 : ℤ) - (p.2.1 : ℤ)), ((p.1.2 : ℤ) - (p.2.2 : ℤ)))) hmaps
  rw [hcard]
  calc ∑ b ∈ S,
        (T.filter (fun p => (((p.1.1 : ℤ) - (p.2.1 : ℤ)),
          ((p.1.2 : ℤ) - (p.2.2 : ℤ))) = b)).card
      ≤ ∑ _b ∈ S, M * M := by
        apply Finset.sum_le_sum
        intro b _
        refine le_trans (Finset.card_le_card ?_) (card_pairDiffFiber_le M b)
        intro p hp
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hp).2⟩
    _ = S.card * (M * M) := by simp [Finset.sum_const]
    _ = M ^ 2 * slotDiffCount q₁ q₂ (M - 1) n := by
        rw [hS, pow_two]
        simp only [slotDiffCount]
        exact Nat.mul_comm _ _

end Work.Peluse.SwapE
