import Mathlib
import Submission.Work.Higman.Defs
import Submission.Work.PSU3.StageA.sq_fiber_card_of_card_sq

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.style.haveILetI false

namespace Work.PSU3.StageA

/-- Arithmetic for the `q ^ 3` case: `(q - 1) * (q * (q + 1)) = q ^ 3 - q`.  This is the identity
`q ^ 3 - q = q (q - 1) (q + 1)` read backwards; it is what turns the counting equation
`q ^ 3 = q + (q - 1) f` of the `|P| = |Z(P)| ^ 3` case into `f = q * (q + 1)`. -/
theorem sub_one_mul_self_mul_succ (q : ℕ) : (q - 1) * (q * (q + 1)) = q ^ 3 - q := by
  rcases q with _ | _ | m
  · decide
  · decide
  · have h : (m + 2) ^ 3 = (m + 2) + (m + 1) * ((m + 2) * ((m + 2) + 1)) := by ring
    rw [show (m + 2 : ℕ) - 1 = m + 1 from rfl, h, Nat.add_sub_cancel_left]

/-- Higman 1963, Suzuki 2-groups: in a Suzuki 2-group `P` of order `q ^ 3` (`q = |Z(P)|`), every
fibre of the squaring map `x ↦ x ^ 2` over a non-identity central element has `q * (q + 1)`
elements.  (The proof is the same counting argument as `Work.PSU3.StageA.sq_fiber_card_of_card_sq`
for the `q ^ 2` case: `hHig`'s clauses `Z(P) = {z | z ^ 2 = 1}` and `x ^ 2 ∈ Z(P)` partition `P`
into the fibres over the elements of `Z(P)`, the fibre over `1` is `Z(P)` itself, and `hSuz.trans`
makes all the other `q - 1` fibres equal; `|P| = q ^ 3` then forces that common value to be
`q * (q + 1)`.) -/
theorem sq_fiber_card_of_card_cube {P : Type} [Group P] [Finite P]
    (hHig : Submission.Blueprint.HigmanProp) (hSuz : Work.Higman.IsSuzuki2Grp P)
    (hcard : Nat.card P = Nat.card ↥(Subgroup.center P) ^ 3)
    {z : P} (hz : z ∈ Subgroup.center P) (hz1 : z ≠ 1) :
    Nat.card {x : P // x ^ 2 = z} =
      Nat.card ↥(Subgroup.center P) * (Nat.card ↥(Subgroup.center P) + 1) := by
  classical
  haveI : Fintype ↥(Subgroup.center P) := Fintype.ofFinite _
  -- Higman's classification, in the form of the two clauses used below.
  have hsuz2 : Submission.Blueprint.IsSuzukiTwoGroup P :=
    Work.Higman.isSuzukiTwoGroup_iff_nonempty_isSuzuki2Grp.mpr ⟨hSuz⟩
  obtain ⟨hA1, hA2, -, -, -⟩ := hHig P hsuz2
  -- The fibres over the centre partition `P`.
  have hsum := card_eq_sum_card_sqFiber (Subgroup.center P) hA2
  -- The fibre over `1` is the centre.
  have hF1 : Nat.card {x : P // x ^ 2 = ((1 : ↥(Subgroup.center P)) : P)} =
      Nat.card ↥(Subgroup.center P) :=
    card_sqFiber_one_eq_card_of_iff (Subgroup.center P) hA1
  -- All the fibres over non-identity central elements have the same size.
  have hconst : ∀ w : ↥(Subgroup.center P), w ≠ 1 →
      Nat.card {x : P // x ^ 2 = (w : P)} = Nat.card {x : P // x ^ 2 = z} := by
    intro w hw
    have hw1 : (w : P) ≠ 1 := fun h => hw (Subtype.ext h)
    have hwo : orderOf (w : P) = 2 := by
      rw [orderOf_eq_prime_iff]
      exact ⟨(hA1 (w : P)).mp w.2, hw1⟩
    have hzo : orderOf z = 2 := by
      rw [orderOf_eq_prime_iff]
      exact ⟨(hA1 z).mp hz, hz1⟩
    obtain ⟨k, hk⟩ := hSuz.trans (w : P) z hwo hzo
    exact card_sqFiber_eq_of_map_eq hSuz.xi k hk
  have herase : (∑ w ∈ Finset.univ.erase (1 : ↥(Subgroup.center P)),
        Nat.card {x : P // x ^ 2 = (w : P)}) =
      (Nat.card ↥(Subgroup.center P) - 1) * Nat.card {x : P // x ^ 2 = z} := by
    rw [Finset.sum_congr rfl (fun w hw => hconst w (Finset.mem_erase.mp hw).1), Finset.sum_const,
      Finset.card_erase_of_mem (Finset.mem_univ (1 : ↥(Subgroup.center P))), Finset.card_univ,
      ← Nat.card_eq_fintype_card, nsmul_eq_mul, Nat.cast_id]
  have hsplit : (∑ w : ↥(Subgroup.center P), Nat.card {x : P // x ^ 2 = (w : P)})
      = Nat.card ↥(Subgroup.center P) +
        (Nat.card ↥(Subgroup.center P) - 1) * Nat.card {x : P // x ^ 2 = z} := by
    have h1 := Finset.sum_erase_add (Finset.univ : Finset ↥(Subgroup.center P))
      (fun w : ↥(Subgroup.center P) => Nat.card {x : P // x ^ 2 = (w : P)})
      (Finset.mem_univ (1 : ↥(Subgroup.center P)))
    rw [← h1, hF1, herase, Nat.add_comm]
  have hmain : Nat.card ↥(Subgroup.center P) ^ 3
      = Nat.card ↥(Subgroup.center P) +
        (Nat.card ↥(Subgroup.center P) - 1) * Nat.card {x : P // x ^ 2 = z} := by
    rw [← hcard, hsum, hsplit]
  -- The centre has at least two elements (`1` and `z`), so `q - 1 ≠ 0` and we may cancel.
  have hq2 : 2 ≤ Nat.card ↥(Subgroup.center P) := by
    have hZne1 : Nat.card ↥(Subgroup.center P) ≠ 1 := by
      intro h
      have hsub : Subsingleton ↥(Subgroup.center P) := (Nat.card_eq_one_iff_unique.mp h).1
      exact hz1 (congrArg Subtype.val
        (Subsingleton.elim (⟨z, hz⟩ : ↥(Subgroup.center P)) ⟨1, Subgroup.one_mem _⟩))
    have hZne0 : Nat.card ↥(Subgroup.center P) ≠ 0 :=
      Nat.card_ne_zero.mpr ⟨⟨1, Subgroup.one_mem _⟩, inferInstance⟩
    omega
  have h4 : Nat.card ↥(Subgroup.center P) ^ 3 - Nat.card ↥(Subgroup.center P) =
      (Nat.card ↥(Subgroup.center P) - 1) * Nat.card {x : P // x ^ 2 = z} := by
    rw [hmain, Nat.add_sub_cancel_left]
  have hkey : (Nat.card ↥(Subgroup.center P) - 1) *
      (Nat.card ↥(Subgroup.center P) * (Nat.card ↥(Subgroup.center P) + 1))
      = Nat.card ↥(Subgroup.center P) ^ 3 - Nat.card ↥(Subgroup.center P) :=
    sub_one_mul_self_mul_succ _
  have hd : 0 < Nat.card ↥(Subgroup.center P) - 1 := by omega
  exact (Nat.mul_left_cancel hd (by rw [hkey, h4])).symm

end Work.PSU3.StageA
