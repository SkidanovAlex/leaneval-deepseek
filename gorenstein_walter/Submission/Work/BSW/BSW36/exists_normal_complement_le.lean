import Mathlib
import Submission.Work.BSW.BSW36.sylow_le_of_coprime_index

namespace Work.BSW.BSW36

theorem exists_normal_complement_le {N : Type} [Group N] [Finite N] {p : ℕ} [Fact p.Prime]
    (h : ∀ (r : ℕ) (hr : r.Prime), r ≠ p → ∀ (R : Sylow r N),
        (Subgroup.normalizer ((R : Subgroup N) : Set N) : Subgroup N) ≤
          Subgroup.centralizer ((R : Subgroup N) : Set N))
    {q : ℕ} (hq : q.Prime) (hqp : q ≠ p) :
    ∃ M : Subgroup N, M.Normal ∧ ¬ q ∣ Nat.card M ∧
      (∀ P : Sylow p N, (P : Subgroup N) ≤ M) := by
  -- Burnside's normal `p`-complement theorem (`MonoidHom.ker_transferSylow_isComplement'`)
  -- applied to the prime `q`: the hypothesis `N(R) ≤ C(R)` for `R ∈ Sylow q N` produces a
  -- normal complement `M` of `R`.  Since `R` is the full `q`-part of `|N|`, `M` is a normal
  -- Hall `q'`-subgroup; in particular `q ∤ |M|`, and every Sylow `p`-subgroup with `p ≠ q` is a
  -- `q'`-group, hence lies in `M`.
  haveI : Fact q.Prime := ⟨hq⟩
  -- choose a Sylow `q`-subgroup of `N`
  let R : Sylow q N := default
  haveI hRfi : (R : Subgroup N).FiniteIndex := inferInstance
  haveI hSylFin : Finite (Sylow q N) := Sylow.finite_of_finiteIndex R
  have hR : Subgroup.normalizer ((R : Subgroup N) : Set N) ≤
      Subgroup.centralizer ((R : Subgroup N) : Set N) := h q hq hqp R
  -- the normal `q`-complement, i.e. the kernel of Burnside's transfer homomorphism
  let M : Subgroup N := (MonoidHom.transferSylow R hR).ker
  have hcomp : M.IsComplement' (R : Subgroup N) :=
    MonoidHom.ker_transferSylow_isComplement' R hR
  haveI hMnormal : M.Normal := MonoidHom.normal_ker _
  refine ⟨M, hMnormal, ?_, ?_⟩
  · -- `q ∤ |M|`: `|M| · |R| = |N|` and `|R|` is the full power of `q` dividing `|N|`.
    have hRcard : Nat.card (R : Subgroup N) = q ^ (Nat.card N).factorization q :=
      Sylow.card_eq_multiplicity R
    have hmul : Nat.card M * Nat.card (R : Subgroup N) = Nat.card N := hcomp.card_mul_card
    let a := (Nat.card N).factorization q
    have hRa : Nat.card (R : Subgroup N) = q ^ a := hRcard
    rintro ⟨k, hk⟩
    have hN : Nat.card N = Nat.card M * q ^ a := by
      conv_lhs => rw [← hmul, hRa]
    have hdvd : q ^ (a + 1) ∣ Nat.card N := by
      rw [hN, hk]
      exact ⟨k, by rw [pow_succ]; ring⟩
    exact Nat.pow_succ_factorization_not_dvd Nat.card_pos.ne' hq hdvd
  · -- every Sylow `p`-subgroup (`p ≠ q`) lies in the normal Hall `q'`-subgroup `M`
    intro P
    have hPcard : Nat.card P = p ^ (Nat.card N).factorization p := Sylow.card_eq_multiplicity P
    have hMindex : M.index = Nat.card (R : Subgroup N) := hcomp.symm.index_eq_card
    have hRcard : Nat.card (R : Subgroup N) = q ^ (Nat.card N).factorization q :=
      Sylow.card_eq_multiplicity R
    refine sylow_le_of_coprime_index P ?_
    rw [hPcard, hMindex, hRcard]
    exact Nat.Coprime.pow _ _ ((Nat.coprime_primes Fact.out hq).mpr (Ne.symm hqp))

end Work.BSW.BSW36
