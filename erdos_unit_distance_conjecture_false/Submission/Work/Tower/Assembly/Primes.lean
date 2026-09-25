import Submission.Work.Tower.Assembly.Setup
import Submission.Work.Tower.Chebotarev.Exists

/-!
# Assembly: choosing the split primes

For a finite Galois extension `N/ℚ` and every `t`, there are `t` distinct primes `≡ 1 (mod 4)`
splitting completely in `N` (the Chebotarev-lite area, iterated).
-/

open NumberField
open scoped Classical nonZeroDivisors

namespace Work
namespace Tower
namespace Assembly

/-- `t` distinct primes `≡ 1 (mod 4)` splitting completely in a finite Galois extension `N/ℚ`. -/
theorem exists_primes_split (N : Type) [Field N] [NumberField N] [IsGalois ℚ N] (t : ℕ) :
    ∃ q : Fin t → ℕ, (∀ b, Nat.Prime (q b)) ∧ Function.Injective q ∧
      (∀ b, q b % 4 = 1) ∧ (∀ b, Work.Defs.SplitsCompletely (q b) N) := by
  induction t with
  | zero => exact ⟨Fin.elim0, fun b => b.elim0, fun a => a.elim0, fun b => b.elim0,
      fun b => b.elim0⟩
  | succ t ih =>
      obtain ⟨q, hq, hqi, hq4, hsplit⟩ := ih
      obtain ⟨qnew, hqnew, hgt, hmem, h4, hsplitnew⟩ :=
        Work.Tower.exists_prime_split_completely_mod4 N ((Finset.univ.image q) ∪ {2})
          ((Finset.univ.sup q) + 1)
      have hne : ∀ c, qnew ≠ q c := by
        intro c hc
        have : qnew ∈ (Finset.univ.image q : Finset ℕ) :=
          Finset.mem_image.mpr ⟨c, Finset.mem_univ c, hc.symm⟩
        exact hmem (Finset.mem_union_left _ this)
      refine ⟨Fin.snoc q qnew, ?_, ?_, ?_, ?_⟩
      · intro b
        rcases Fin.eq_castSucc_or_eq_last b with ⟨c, rfl⟩ | hb
        · rw [Fin.snoc_castSucc]; exact hq c
        · rw [hb, Fin.snoc_last]; exact hqnew
      · intro a b hab
        rcases Fin.eq_castSucc_or_eq_last a with ⟨c, rfl⟩ | ha
        · rcases Fin.eq_castSucc_or_eq_last b with ⟨d, rfl⟩ | hb
          · rw [Fin.snoc_castSucc, Fin.snoc_castSucc] at hab
            rw [hqi hab]
          · rw [hb, Fin.snoc_last, Fin.snoc_castSucc] at hab
            exact absurd hab.symm (hne c)
        · rcases Fin.eq_castSucc_or_eq_last b with ⟨d, rfl⟩ | hb
          · rw [ha, Fin.snoc_last, Fin.snoc_castSucc] at hab
            exact absurd hab (hne d)
          · rw [ha, hb]
      · intro b
        rcases Fin.eq_castSucc_or_eq_last b with ⟨c, rfl⟩ | hb
        · rw [Fin.snoc_castSucc]; exact hq4 c
        · rw [hb, Fin.snoc_last]; exact h4
      · intro b
        rcases Fin.eq_castSucc_or_eq_last b with ⟨c, rfl⟩ | hb
        · rw [Fin.snoc_castSucc]; exact hsplit c
        · rw [hb, Fin.snoc_last]; exact hsplitnew

end Assembly
end Tower
end Work
