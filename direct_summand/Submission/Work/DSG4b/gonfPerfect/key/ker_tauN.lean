import Mathlib
import Submission.Work.DSG4b.gonfPerfect.Basic
import Submission.Work.DSG4b.pBasis.pBasis_pow_basis
import Submission.Work.DSG4b.gonfPerfect.keyAux.tauN_sum_pow
import Submission.Work.DSG4b.gonfPerfect.key.exists_sum_mon

namespace Work.DSG4b.gonfPerfect.key

/-- `PerfectClosure.of` is injective when the base ring is a field. -/
lemma of_injective' (K : Type*) [Field K] (p : ℕ) [Fact p.Prime] [CharP K p] :
    Function.Injective (PerfectClosure.of K p) := by
  intro x y h
  rw [PerfectClosure.of_apply, PerfectClosure.of_apply] at h
  have h2 := (PerfectClosure.eq_iff K p (0, x) (0, y)).mp h
  simpa using h2

theorem ker_tauN (R : Type*) [CommRing R] [IsLocalRing R] (p : ℕ) [Fact p.Prime]
    [CharP (IsLocalRing.ResidueField R) p] (D : PData R p) (N : ℕ) :
    RingHom.ker (D.tauN N) = Ideal.map (algebraMap R (D.AN N)) (IsLocalRing.maximalIdeal R) := by
  have hp0 : p ≠ 0 := (Fact.out : Nat.Prime p).ne_zero
  have hpN : p ^ N ≠ 0 := pow_ne_zero N hp0
  have hspan : ∀ a : D.AN N, ∃ (s : Finset (D.Idx N)) (r : D.Idx N → R),
      ∑ e ∈ s, algebraMap R (D.AN N) (r e) * D.mon N e = a :=
    fun a => exists_sum_mon R p D N a
  have hpw : ∀ (s : Finset (D.Idx N)) (r : D.Idx N → R),
      (D.tauN N (∑ e ∈ s, algebraMap R (D.AN N) (r e) * D.mon N e)) ^ p ^ N =
        PerfectClosure.of (IsLocalRing.ResidueField R) p
          (∑ e ∈ s, (IsLocalRing.residue R (r e)) ^ p ^ N *
            (e.1.prod (fun b m => ((b : IsLocalRing.ResidueField R) ^ m)))) :=
    fun s r => Work.DSG4b.gonfPerfect.keyAux.tauN_sum_pow R p D N s r
  refine le_antisymm ?_ ?_
  · rintro a ha
    rw [RingHom.mem_ker] at ha
    obtain ⟨s, r, hsr⟩ := hspan a
    have hpow := hpw s r
    rw [hsr, ha, zero_pow hpN] at hpow
    have hrel : ∑ e ∈ s, (IsLocalRing.residue R (r e)) ^ p ^ N *
        (e.1.prod (fun b m => ((b : IsLocalRing.ResidueField R) ^ m))) = 0 := by
      apply of_injective' _ p
      rw [map_zero]
      exact hpow.symm
    obtain ⟨b', hb'⟩ := Work.DSG4b.pBasis.pBasis_pow_basis
      (IsLocalRing.ResidueField R) p D.pB D.basis D.basis_apply N
    have hlin := b'.linearIndependent
    let c : D.Idx N → (iterateFrobenius (IsLocalRing.ResidueField R) p N).fieldRange :=
      fun e => ⟨(IsLocalRing.residue R (r e)) ^ p ^ N,
        (Work.DSG4b.pBasis.mem_K (L := IsLocalRing.ResidueField R) (p := p) N _).mpr
          ⟨IsLocalRing.residue R (r e), rfl⟩⟩
    have hrel' : ∑ e ∈ s, c e • (b' e) = 0 := by
      rw [← hrel]
      refine Finset.sum_congr rfl fun e _ => ?_
      rw [hb' e]
      show c e • (e.1.prod (fun b m => ((b : IsLocalRing.ResidueField R) ^ m))) = _
      rw [Algebra.smul_def, Subfield.algebraMap_ofSubfield, Subfield.subtype_apply]
    have hzero := (linearIndependent_iff'.mp hlin) s c hrel'
    rw [← hsr]
    refine Ideal.sum_mem _ fun e he => ?_
    refine Ideal.mul_mem_right _ _ ?_
    refine Ideal.mem_map_of_mem _ ?_
    rw [← IsLocalRing.residue_eq_zero_iff]
    refine (pow_eq_zero_iff hpN).mp ?_
    have h1 := congrArg Subtype.val (hzero e he)
    exact h1
  · rw [Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap, RingHom.mem_ker, ← D.toAN_eq_algebraMap, D.tauN_toAN,
      (IsLocalRing.residue_eq_zero_iff x).mpr hx, map_zero]

end Work.DSG4b.gonfPerfect.key
