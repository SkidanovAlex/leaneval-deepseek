/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Submission.Work.L2F.Defs
import Submission.Work.L2F.Props.Count.Defs
import Submission.Work.L2F.Props.Count.Basic
import Submission.Work.L2F.Props.Count.Assembly
import Submission.Work.L2F.Conic.ncard_squares

open scoped MatrixGroups
open Matrix

namespace Work.L2F.Props

/-- A small number-theoretic fact: if `r` divides the integer `(q + ε)/2`, with `q` odd and
`ε = ±1`, then `ε = 1` and `r ∣ q + 1`, or `ε = -1` and `r ∣ q - 1`. -/
theorem int_dvd_half {q r : ℕ} {ε : ℤ} (hq : Odd q) (hε : ε = 1 ∨ ε = -1)
    (hdvd : (r : ℤ) ∣ ((q : ℤ) + ε) / 2) :
    (ε = 1 ∧ r ∣ q + 1) ∨ (ε = -1 ∧ r ∣ q - 1) := by
  rcases hε with rfl | rfl
  · left
    refine ⟨rfl, ?_⟩
    have heven : (2 : ℤ) ∣ (q : ℤ) + 1 := by
      obtain ⟨m, hm⟩ := hq
      exact ⟨m + 1, by push_cast [hm]; ring⟩
    have h2 : 2 * (((q : ℤ) + 1) / 2) = (q : ℤ) + 1 := by
      rw [mul_comm, Int.ediv_mul_cancel heven]
    have hdiv : (r : ℤ) ∣ (q : ℤ) + 1 := by
      obtain ⟨c, hc⟩ := hdvd
      exact ⟨2 * c, by rw [← h2, hc]; ring⟩
    rw [show (q : ℤ) + 1 = ((q + 1 : ℕ) : ℤ) by push_cast; ring] at hdiv
    exact Int.ofNat_dvd.mp hdiv
  · right
    refine ⟨rfl, ?_⟩
    have heven : (2 : ℤ) ∣ (q : ℤ) + (-1) := by
      obtain ⟨m, hm⟩ := hq
      exact ⟨m, by push_cast [hm]; ring⟩
    have h2 : 2 * (((q : ℤ) + (-1)) / 2) = (q : ℤ) + (-1) := by
      rw [mul_comm, Int.ediv_mul_cancel heven]
    have hdiv : (r : ℤ) ∣ (q : ℤ) + (-1) := by
      obtain ⟨c, hc⟩ := hdvd
      exact ⟨2 * c, by rw [← h2, hc]; ring⟩
    have hq1 : 1 ≤ q := by obtain ⟨m, hm⟩ := hq; omega
    rw [show (q : ℤ) + (-1) = ((q - 1 : ℕ) : ℤ) by push_cast; omega] at hdiv
    exact Int.ofNat_dvd.mp hdiv

/-- `L2PrimeSubgroupCountProp`: for an odd prime `r ∣ (q+ε)/2`, `ε = ±1`, the number of subgroups
of order `r` in `L₂(q)` is `q(q-ε)/2`.
Proof: each such subgroup is contained in a unique torus of order `(q+ε)/2` (its centralizer,
`L2TorusNormalizerProp`), and each cyclic torus of order `(q+ε)/2` contains exactly one subgroup of
order `r` (`r` prime); the number of such tori is `|PSL|/|N(T)| = q(q-ε)/2`
(`Work.PSL2.card_PSL2_of_odd` and `2|C(Y)| = 2|T| = q+ε`, `L2TorusNormalizerProp`). -/
theorem L2PrimeSubgroupCount : Work.L2F.L2PrimeSubgroupCountProp := by
  intro p k hpprime hp hk r hr hr2 hrp ε hε hdvd
  classical
  have hk0 : k ≠ 0 := by rintro rfl; simp at hk
  haveI : Fintype (GaloisField p k) := Fintype.ofFinite _
  have hcard : Nat.card (GaloisField p k) = p ^ k := GaloisField.card p k hk0
  have hodd : Odd (Nat.card (GaloisField p k)) := by rw [hcard]; exact hp.pow
  have hq1 : 1 ≤ Nat.card (GaloisField p k) := by omega
  have h2 : (2 : GaloisField p k) ≠ 0 := by
    intro h
    haveI : CharP (GaloisField p k) p := inferInstance
    have hd : p ∣ 2 := (CharP.cast_eq_zero_iff (GaloisField p k) p 2).mp h
    have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) hd
    have hge : 2 ≤ p := hpprime.out.two_le
    have hp2 : p = 2 := le_antisymm hle hge
    obtain ⟨m, hm⟩ := hp
    omega
  have hrc : (r : GaloisField p k) ≠ 0 := by
    intro h
    haveI : CharP (GaloisField p k) p := inferInstance
    have hd : p ∣ r := (CharP.cast_eq_zero_iff (GaloisField p k) p r).mp h
    have hpr : p = r := (Nat.prime_dvd_prime_iff_eq hpprime.out hr).mp hd
    exact hrp hpr.symm
  have hnsq : ∃ d : GaloisField p k, d ≠ 0 ∧ ∀ a : GaloisField p k, a * a ≠ d := by
    haveI : Finite (GaloisField p k) := Finite.of_fintype _
    have hsquares := Work.L2F.Conic.ncard_squares (GaloisField p k) h2
    have hex : ∃ d : GaloisField p k, ¬ IsSquare d := by
      by_contra hcon
      push Not at hcon
      have hall : {x : GaloisField p k | IsSquare x} = Set.univ := Set.eq_univ_of_forall hcon
      rw [hall, Set.ncard_univ] at hsquares
      have heven : Even (Nat.card (GaloisField p k) + 1) := by
        obtain ⟨m, hm⟩ := hodd
        exact ⟨m + 1, by omega⟩
      have h2' : 2 * ((Nat.card (GaloisField p k) + 1) / 2) = Nat.card (GaloisField p k) + 1 :=
        Nat.two_mul_div_two_of_even heven
      have h5 : 5 ≤ Nat.card (GaloisField p k) := by rw [hcard]; exact hk
      omega
    obtain ⟨d, hd⟩ := hex
    refine ⟨d, fun h0 => hd ?_, fun a ha => hd ?_⟩
    · rw [h0]; exact ⟨0, by simp⟩
    · exact ⟨a, ha.symm⟩
  obtain ⟨hε1, hdvd1⟩ | ⟨hεm, hdvdm⟩ := int_dvd_half hodd hε (by rw [hcard]; exact hdvd)
  · -- the case `ε = 1`, i.e. `r ∣ q + 1`
    have h := Work.L2F.Count.prime_subgroup_count_add (GaloisField p k) h2 hnsq r hr hr2 hrc hdvd1
    rw [hε1]
    have hL : ({Y : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k)) |
        Nat.card Y = r}.ncard : ℤ)
        = (Nat.card {Y : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k)) //
            Nat.card Y = r} : ℤ) := by
      rw [Nat.cast_inj]
      exact Work.L2F.Count.set_ncard_eq_natCard _
    rw [hL]
    have h1 : (2 : ℤ) * (Nat.card {Y : Subgroup
          (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k)) // Nat.card Y = r} : ℤ)
        = ((2 * Nat.card {Y : Subgroup
          (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k)) // Nat.card Y = r} : ℕ)
            : ℤ) := by
      push_cast; ring
    rw [h1, h, Nat.cast_mul, Nat.cast_sub hq1, hcard]
    ring
  · -- the case `ε = -1`, i.e. `r ∣ q - 1`
    have h := Work.L2F.Count.prime_subgroup_count_sub (GaloisField p k) h2 hnsq r hr hr2 hrc hdvdm
    rw [hεm]
    have hL : ({Y : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k)) |
        Nat.card Y = r}.ncard : ℤ)
        = (Nat.card {Y : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k)) //
            Nat.card Y = r} : ℤ) := by
      rw [Nat.cast_inj]
      exact Work.L2F.Count.set_ncard_eq_natCard _
    rw [hL]
    have h1 : (2 : ℤ) * (Nat.card {Y : Subgroup
          (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k)) // Nat.card Y = r} : ℤ)
        = ((2 * Nat.card {Y : Subgroup
          (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k)) // Nat.card Y = r} : ℕ)
            : ℤ) := by
      push_cast; ring
    rw [h1, h, Nat.cast_mul, Nat.cast_add, hcard]
    ring

end Work.L2F.Props
