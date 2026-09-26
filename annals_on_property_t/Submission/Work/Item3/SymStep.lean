import Submission.Work.Item3.DegenerateEven

open Submission.Nielsen
open Submission.FreeGroupAut
open Commons.GroupTheory.FreeGroup
open FreeGroup
open scoped BigOperators
set_option autoImplicit false

/-!
# SymStep: the generic numeric core of a one-coordinate symmetric-energy step

`sym_energy_step_left_rho` / `sym_energy_step_right_lam` are the two
neighbour-orientation `= true` cases of the balanced-side step for the symmetric
energy.  The eight cases (four transvection orientations times the two
orientations of the balanced coordinate) share a single *numeric* core: a
transvection changing exactly one coordinate word, from `W` to `W'`, changes

    eEnergySym = Σ_i (E (coordWord α i) + E (invRev (coordWord α i)))

by `(E W' + E (invRev W')) − (E W + E (invRev W))`.  This module isolates that
core (`eEnergySym_eq_sum_erase`, `eEnergySym_single_update`,
`sym_energy_step_of_single`), together with the two combined update lemmas
`eEnergySym_mul_rho` / `eEnergySym_mul_lam`, so that any further cut-slide case
only has to supply its word identity `W'`, its "other coordinates unchanged"
fact, and its `N`-preservation.

All lemmas kernel-checked; axioms `[propext, Classical.choice, Quot.sound]`.
-/

namespace Submission.Nielsen

/-- Splitting the symmetric energy at a coordinate. -/
lemma eEnergySym_eq_sum_erase {n : ℕ} (α : MulAut (FreeGroup (Fin n))) (v : Fin n) :
    eEnergySym α =
      (∑ i ∈ (Finset.univ.erase v : Finset (Fin n)),
          (wordEnergy (ebase n) (lweight) (coordWord α i)
            + wordEnergy (ebase n) (lweight) (coordWordStar α i))) +
        (wordEnergy (ebase n) (lweight) (coordWord α v)
          + wordEnergy (ebase n) (lweight) (coordWordStar α v)) := by
  unfold eEnergySym
  rw [eEnergy_eq_sum_erase α v, eEnergyStar_eq_sum_erase α v, Finset.sum_add_distrib]
  omega

/-- **The generic single-coordinate update.**  If the state `α * γ` differs from
`α` only in the `v`-th coordinate word, then the symmetric energy of `α * γ`
plus the *old* `v`-contribution equals the symmetric energy of `α` plus the
*new* `v`-contribution. -/
lemma eEnergySym_single_update {n : ℕ} (α γ : MulAut (FreeGroup (Fin n))) {v : Fin n}
    (hother : ∀ k : Fin n, k ≠ v → coordWord (α * γ) k = coordWord α k) :
    eEnergySym (α * γ)
        + (wordEnergy (ebase n) (lweight) (coordWord α v)
            + wordEnergy (ebase n) (lweight) (coordWordStar α v)) =
      eEnergySym α
        + (wordEnergy (ebase n) (lweight) (coordWord (α * γ) v)
            + wordEnergy (ebase n) (lweight) (coordWordStar (α * γ) v)) := by
  rw [eEnergySym_eq_sum_erase (α * γ) v, eEnergySym_eq_sum_erase α v]
  have hrest : (∑ i ∈ (Finset.univ.erase v : Finset (Fin n)),
      (wordEnergy (ebase n) (lweight) (coordWord (α * γ) i)
        + wordEnergy (ebase n) (lweight) (coordWordStar (α * γ) i))) =
      (∑ i ∈ (Finset.univ.erase v : Finset (Fin n)),
        (wordEnergy (ebase n) (lweight) (coordWord α i)
          + wordEnergy (ebase n) (lweight) (coordWordStar α i))) := by
    apply Finset.sum_congr rfl
    intro k hk
    have hkv : k ≠ v := (Finset.mem_erase.mp hk).1
    rw [coordWordStar, coordWordStar, hother k hkv]
  rw [hrest]
  omega

/-- **The symmetric-energy step from a single-coordinate word change.**  In a
state where a move `γ` preserves `N`, changes only the `v`-th coordinate word
(from `W` to `W'`) and strictly decreases the two-term contribution
`E · + E (invRev ·)`, the symmetric energy strictly decreases. -/
theorem sym_energy_step_of_single {n : ℕ} (α γ : MulAut (FreeGroup (Fin n))) {v : Fin n}
    {W W' : List (Fin n × Bool)}
    (hW : coordWord α v = W) (hW' : coordWord (α * γ) v = W')
    (hother : ∀ k : Fin n, k ≠ v → coordWord (α * γ) k = coordWord α k)
    (hN : N (α * γ) = N α)
    (hlt : wordEnergy (ebase n) (lweight) W'
            + wordEnergy (ebase n) (lweight) (FreeGroup.invRev W')
          < wordEnergy (ebase n) (lweight) W
            + wordEnergy (ebase n) (lweight) (FreeGroup.invRev W)) :
    N (α * γ) = N α ∧ eEnergySym (α * γ) < eEnergySym α := by
  refine ⟨hN, ?_⟩
  have hupd := eEnergySym_single_update α γ hother
  rw [hW, hW'] at hupd
  have hstar_old : coordWordStar α v = FreeGroup.invRev W := by
    unfold coordWordStar; rw [hW]
  have hstar_new : coordWordStar (α * γ) v = FreeGroup.invRev W' := by
    unfold coordWordStar; rw [hW']
  rw [hstar_old, hstar_new] at hupd
  omega

/-- Combined plain + star update for a `rho` transvection. -/
lemma eEnergySym_mul_rho {n : ℕ} (α : MulAut (FreeGroup (Fin n))) (i j : Fin n)
    (hij : i ≠ j) (W W' : List (Fin n × Bool))
    (hW : coordWord (α * rho i j hij) i = W)
    (hW' : coordWordStar (α * rho i j hij) i = W') :
    eEnergySym (α * rho i j hij)
        + (wordEnergy (ebase n) (lweight) (coordWord α i)
            + wordEnergy (ebase n) (lweight) (coordWordStar α i)) =
      eEnergySym α
        + (wordEnergy (ebase n) (lweight) W
            + wordEnergy (ebase n) (lweight) W') := by
  have h1 := eEnergy_mul_rho α i j hij W hW
  have h2 := eEnergyStar_mul_rho α i j hij W' hW'
  unfold eEnergySym
  omega

/-- Combined plain + star update for a `lam` transvection. -/
lemma eEnergySym_mul_lam {n : ℕ} (α : MulAut (FreeGroup (Fin n))) (i j : Fin n)
    (hij : i ≠ j) (W W' : List (Fin n × Bool))
    (hW : coordWord (α * lam i j hij) i = W)
    (hW' : coordWordStar (α * lam i j hij) i = W') :
    eEnergySym (α * lam i j hij)
        + (wordEnergy (ebase n) (lweight) (coordWord α i)
            + wordEnergy (ebase n) (lweight) (coordWordStar α i)) =
      eEnergySym α
        + (wordEnergy (ebase n) (lweight) W
            + wordEnergy (ebase n) (lweight) W') := by
  have h1 := eEnergy_mul_lam α i j hij W hW
  have h2 := eEnergyStar_mul_lam α i j hij W' hW'
  unfold eEnergySym
  omega

/-! ## The two-term comparisons for the four cut-slides -/

/-- Left slide, plus-oriented neighbour: the two-term comparison is exactly the
classical `Δ_L < C^{|X|} Δ_R`. -/
lemma left_two_term_lt {n : ℕ} (A B X : List (Fin n × Bool)) (hAB : A.length = B.length)
    (hE : wordEnergy (ebase n) (lweight) B
            + (ebase n) ^ X.length * wordEnergy (ebase n) (lweight) (FreeGroup.invRev B)
          < (ebase n) ^ X.length * wordEnergy (ebase n) (lweight) A
            + wordEnergy (ebase n) (lweight) (FreeGroup.invRev A)) :
    wordEnergy (ebase n) (lweight) (X ++ B)
        + wordEnergy (ebase n) (lweight) (FreeGroup.invRev (X ++ B))
      < wordEnergy (ebase n) (lweight) (X ++ FreeGroup.invRev A)
        + wordEnergy (ebase n) (lweight) (FreeGroup.invRev (X ++ FreeGroup.invRev A)) := by
  simp only [wordEnergy_append'', wordEnergy_invRev_append, FreeGroup.invRev_invRev,
    FreeGroup.invRev_length, hAB]
  omega

/-- Left slide, minus-oriented neighbour: the same comparison with the two words
exchanged. -/
lemma left_two_term_lt_minus {n : ℕ} (A B X : List (Fin n × Bool)) (hAB : A.length = B.length)
    (hE : wordEnergy (ebase n) (lweight) B
            + (ebase n) ^ X.length * wordEnergy (ebase n) (lweight) (FreeGroup.invRev B)
          < (ebase n) ^ X.length * wordEnergy (ebase n) (lweight) A
            + wordEnergy (ebase n) (lweight) (FreeGroup.invRev A)) :
    wordEnergy (ebase n) (lweight) (FreeGroup.invRev B ++ FreeGroup.invRev X)
        + wordEnergy (ebase n) (lweight)
            (FreeGroup.invRev (FreeGroup.invRev B ++ FreeGroup.invRev X))
      < wordEnergy (ebase n) (lweight) (A ++ FreeGroup.invRev X)
        + wordEnergy (ebase n) (lweight) (FreeGroup.invRev (A ++ FreeGroup.invRev X)) := by
  simp only [wordEnergy_append'', wordEnergy_append'', FreeGroup.invRev_length,
    wordEnergy_invRev_append, FreeGroup.invRev_invRev, hAB]
  omega

/-- Right slide, plus-oriented neighbour: the two-term comparison is exactly
`C^{|Z|} Δ_R < Δ_L`. -/
lemma right_two_term_lt {n : ℕ} (A B Z : List (Fin n × Bool)) (hAB : A.length = B.length)
    (hE : (ebase n) ^ Z.length * wordEnergy (ebase n) (lweight) A
            + wordEnergy (ebase n) (lweight) (FreeGroup.invRev A)
          < (ebase n) ^ Z.length * wordEnergy (ebase n) (lweight) (FreeGroup.invRev B)
            + wordEnergy (ebase n) (lweight) B) :
    wordEnergy (ebase n) (lweight) (A ++ Z)
        + wordEnergy (ebase n) (lweight) (FreeGroup.invRev (A ++ Z))
      < wordEnergy (ebase n) (lweight) (FreeGroup.invRev B ++ Z)
        + wordEnergy (ebase n) (lweight) (FreeGroup.invRev (FreeGroup.invRev B ++ Z)) := by
  simp only [wordEnergy_append'', wordEnergy_append'',
    wordEnergy_invRev_append, FreeGroup.invRev_invRev, FreeGroup.invRev_length]
  rw [hAB]
  omega

/-- Right slide, minus-oriented neighbour: the same comparison with the two
words exchanged. -/
lemma right_two_term_lt_minus {n : ℕ} (A B Z : List (Fin n × Bool)) (hAB : A.length = B.length)
    (hE : (ebase n) ^ Z.length * wordEnergy (ebase n) (lweight) A
            + wordEnergy (ebase n) (lweight) (FreeGroup.invRev A)
          < (ebase n) ^ Z.length * wordEnergy (ebase n) (lweight) (FreeGroup.invRev B)
            + wordEnergy (ebase n) (lweight) B) :
    wordEnergy (ebase n) (lweight) (FreeGroup.invRev Z ++ FreeGroup.invRev A)
        + wordEnergy (ebase n) (lweight)
            (FreeGroup.invRev (FreeGroup.invRev Z ++ FreeGroup.invRev A))
      < wordEnergy (ebase n) (lweight) (FreeGroup.invRev Z ++ B)
        + wordEnergy (ebase n) (lweight) (FreeGroup.invRev (FreeGroup.invRev Z ++ B)) := by
  simp only [wordEnergy_append'', wordEnergy_append'',
    wordEnergy_invRev_append, FreeGroup.invRev_invRev, FreeGroup.invRev_length]
  rw [hAB]
  omega

/-! ## The four cut-slide steps -/

/-- **Left cut-slide, minus-oriented neighbour, positive balanced row.** -/
theorem sym_energy_step_left_lam {n : ℕ} (α : MulAut (FreeGroup (Fin n)))
    (hres : NoEndCancel n α) {p v : Fin n} (hvp : v ≠ p)
    (A B X : List (Fin n × Bool)) (hAB : A.length = B.length)
    (hp : coordWord α p = A ++ B)
    (hv : coordWord α v = A ++ FreeGroup.invRev X)
    (hE : wordEnergy (ebase n) (lweight) B
            + (ebase n) ^ X.length * wordEnergy (ebase n) (lweight) (FreeGroup.invRev B)
          < (ebase n) ^ X.length * wordEnergy (ebase n) (lweight) A
            + wordEnergy (ebase n) (lweight) (FreeGroup.invRev A)) :
    N (α * lamNeg v p hvp) = N α ∧ eEnergySym (α * lamNeg v p hvp) < eEnergySym α := by
  have hp' : (α (FreeGroup.of p)).toWord = A ++ B := hp
  have hv' : (α (FreeGroup.of v)).toWord = A ++ FreeGroup.invRev X := hv
  have hel : (α * lamNeg v p hvp) (FreeGroup.of v) =
      FreeGroup.mk (FreeGroup.invRev B ++ FreeGroup.invRev X) := by
    rw [mul_lamNeg_apply_self]
    rw [← FreeGroup.mk_toWord (x := α (FreeGroup.of p)), hp',
      ← FreeGroup.mk_toWord (x := α (FreeGroup.of v)), hv']
    exact mk_lamNeg_general A B X
  have hW : coordWord (α * lamNeg v p hvp) v =
      FreeGroup.reduce (FreeGroup.invRev B ++ FreeGroup.invRev X) := by
    show ((α * lamNeg v p hvp) (FreeGroup.of v)).toWord = _
    rw [hel, FreeGroup.toWord_mk]
  have hlen1 : (coordWord (α * lamNeg v p hvp) v).length ≤ B.length + X.length := by
    rw [hW]
    calc (FreeGroup.reduce (FreeGroup.invRev B ++ FreeGroup.invRev X)).length
        ≤ (FreeGroup.invRev B ++ FreeGroup.invRev X).length := reduce_length_le _
      _ = B.length + X.length := by rw [length_invRev_invRev]
  have hlen0 : (coordWord α v).length = A.length + X.length := by
    rw [hv, length_append_invRev']
  have hmin := (noEndCancel_iff_local_min n α).mp hres
  have hNle : N α ≤ N (α * lamNeg v p hvp) := hmin.2.2.2 v p hvp
  have hNform := N_mul_lamNeg α v p hvp
  have habs : FreeGroup.norm (α (FreeGroup.of v)) ≤
      FreeGroup.norm ((α (FreeGroup.of p))⁻¹ * α (FreeGroup.of v)) :=
    (N_le_N_mul_lamNeg_iff α v p hvp).mp hNle
  have hge : A.length + X.length ≤ (coordWord (α * lamNeg v p hvp) v).length := by
    have h1 : FreeGroup.norm (α (FreeGroup.of v)) = A.length + X.length := hlen0
    have h2 : FreeGroup.norm ((α (FreeGroup.of p))⁻¹ * (α (FreeGroup.of v))) =
        (coordWord (α * lamNeg v p hvp) v).length := by
      rw [← mul_lamNeg_apply_self α v p hvp]
      rfl
    omega
  have hlen_eq : (coordWord (α * lamNeg v p hvp) v).length = A.length + X.length :=
    le_antisymm (by omega) hge
  have hWeq : coordWord (α * lamNeg v p hvp) v =
      FreeGroup.invRev B ++ FreeGroup.invRev X := by
    rw [hW]
    refine reduce_eq_of_length_eq _ ?_
    rw [← hW, hlen_eq, hAB]
    exact (length_invRev_invRev B X).symm
  have hNeq : N (α * lamNeg v p hvp) = N α := by
    have h1 : FreeGroup.norm (α (FreeGroup.of v)) = A.length + X.length := hlen0
    have h2 : FreeGroup.norm ((α (FreeGroup.of p))⁻¹ * (α (FreeGroup.of v))) =
        A.length + X.length := by
      have hh : FreeGroup.norm ((α (FreeGroup.of p))⁻¹ * (α (FreeGroup.of v))) =
          (coordWord (α * lamNeg v p hvp) v).length := by
        rw [← mul_lamNeg_apply_self α v p hvp]
        rfl
      rw [hh, hlen_eq]
    have h3 : FreeGroup.norm ((α (FreeGroup.of p))⁻¹ * (α (FreeGroup.of v))) =
        FreeGroup.norm (α (FreeGroup.of v)) := by rw [h1, h2]
    rw [hNform, h3]
    exact Nat.sub_add_cancel (norm_le_N α v)
  refine sym_energy_step_of_single α (lamNeg v p hvp) hv hWeq ?_ hNeq
    (left_two_term_lt_minus A B X hAB hE)
  intro k hk
  exact congrArg FreeGroup.toWord (mul_lamNeg_apply_other (α := α) hvp hk)

theorem sym_energy_step_left_lam_balminus {n : ℕ} (α : MulAut (FreeGroup (Fin n)))
    (hres : NoEndCancel n α) {p v : Fin n} (hvp : v ≠ p)
    (A B X : List (Fin n × Bool)) (hAB : A.length = B.length)
        (hE : wordEnergy (ebase n) (lweight) B
            + (ebase n) ^ X.length * wordEnergy (ebase n) (lweight) (FreeGroup.invRev B)
          < (ebase n) ^ X.length * wordEnergy (ebase n) (lweight) A
            + wordEnergy (ebase n) (lweight) (FreeGroup.invRev A))
    (hp : coordWord α p = FreeGroup.invRev B ++ FreeGroup.invRev A)
    (hv : coordWord α v = A ++ FreeGroup.invRev X) :
    N (α * lam v p hvp) = N α ∧ eEnergySym (α * lam v p hvp) < eEnergySym α := by

  have hp' : (α (FreeGroup.of p)).toWord =
      FreeGroup.invRev B ++ FreeGroup.invRev A := hp
  have hv' : (α (FreeGroup.of v)).toWord = A ++ FreeGroup.invRev X := hv
  have hel : (α * lam v p hvp) (FreeGroup.of v) =
      FreeGroup.mk (FreeGroup.invRev B ++ FreeGroup.invRev X) := by
    rw [mul_lam_apply_self]
    rw [← FreeGroup.mk_toWord (x := α (FreeGroup.of p)), hp',
      ← FreeGroup.mk_toWord (x := α (FreeGroup.of v)), hv']
    exact mk_lam_general A B X
  have hW : coordWord (α * lam v p hvp) v =
      FreeGroup.reduce (FreeGroup.invRev B ++ FreeGroup.invRev X) := by
    show ((α * lam v p hvp) (FreeGroup.of v)).toWord = _
    rw [hel, FreeGroup.toWord_mk]
  have hlen1 : (coordWord (α * lam v p hvp) v).length ≤ B.length + X.length := by
    rw [hW]
    calc (FreeGroup.reduce (FreeGroup.invRev B ++ FreeGroup.invRev X)).length
        ≤ (FreeGroup.invRev B ++ FreeGroup.invRev X).length := reduce_length_le _
      _ = B.length + X.length := by rw [length_invRev_invRev]
  have hlen0 : (coordWord α v).length = A.length + X.length := by
    rw [hv, length_append_invRev']
  have hmin := (noEndCancel_iff_local_min n α).mp hres
  have hNle : N α ≤ N (α * lam v p hvp) := hmin.2.2.1 v p hvp
  have hNform := N_mul_lam α v p hvp
  have habs : FreeGroup.norm (α (FreeGroup.of v)) ≤
      FreeGroup.norm ((α (FreeGroup.of p)) * α (FreeGroup.of v)) :=
    (N_le_N_mul_lam_iff α v p hvp).mp hNle
  have hge : A.length + X.length ≤ (coordWord (α * lam v p hvp) v).length := by
    have h1 : FreeGroup.norm (α (FreeGroup.of v)) = A.length + X.length := hlen0
    have h2 : FreeGroup.norm ((α (FreeGroup.of p)) * (α (FreeGroup.of v))) =
        (coordWord (α * lam v p hvp) v).length := by
      rw [← mul_lam_apply_self α v p hvp]
      rfl
    omega
  have hlen_eq : (coordWord (α * lam v p hvp) v).length = A.length + X.length :=
    le_antisymm (by omega) hge
  have hWeq : coordWord (α * lam v p hvp) v =
      FreeGroup.invRev B ++ FreeGroup.invRev X := by
    rw [hW]
    refine reduce_eq_of_length_eq _ ?_
    rw [← hW, hlen_eq, hAB]
    exact (length_invRev_invRev B X).symm
  have hNeq : N (α * lam v p hvp) = N α := by
    have h1 : FreeGroup.norm (α (FreeGroup.of v)) = A.length + X.length := hlen0
    have h2 : FreeGroup.norm ((α (FreeGroup.of p)) * (α (FreeGroup.of v))) =
        A.length + X.length := by
      have hh : FreeGroup.norm ((α (FreeGroup.of p)) * (α (FreeGroup.of v))) =
          (coordWord (α * lam v p hvp) v).length := by
        rw [← mul_lam_apply_self α v p hvp]
        rfl
      rw [hh, hlen_eq]
    have h3 : FreeGroup.norm ((α (FreeGroup.of p)) * (α (FreeGroup.of v))) =
        FreeGroup.norm (α (FreeGroup.of v)) := by rw [h1, h2]
    rw [hNform, h3]
    exact Nat.sub_add_cancel (norm_le_N α v)
  refine sym_energy_step_of_single α (lam v p hvp) hv hWeq ?_ hNeq
    (left_two_term_lt_minus A B X hAB hE)
  intro k hk
  exact congrArg FreeGroup.toWord (mul_lam_apply_other (α := α) hvp hk)

theorem sym_energy_step_right_rho {n : ℕ} (α : MulAut (FreeGroup (Fin n)))
    (hres : NoEndCancel n α) {p u : Fin n} (hup : u ≠ p)
    (A B Z : List (Fin n × Bool)) (hAB : A.length = B.length)
        (hE : (ebase n) ^ Z.length * wordEnergy (ebase n) (lweight) A
            + wordEnergy (ebase n) (lweight) (FreeGroup.invRev A)
          < (ebase n) ^ Z.length * wordEnergy (ebase n) (lweight) (FreeGroup.invRev B)
            + wordEnergy (ebase n) (lweight) B)
    (hp : coordWord α p = A ++ B)
    (hu : coordWord α u = FreeGroup.invRev Z ++ B) :
    N (α * rhoNeg u p hup) = N α ∧ eEnergySym (α * rhoNeg u p hup) < eEnergySym α := by

  have hp' : (α (FreeGroup.of p)).toWord = A ++ B := hp
  have hu' : (α (FreeGroup.of u)).toWord = FreeGroup.invRev Z ++ B := hu
  have hel : (α * rhoNeg u p hup) (FreeGroup.of u) =
      FreeGroup.mk (FreeGroup.invRev Z ++ FreeGroup.invRev A) := by
    rw [mul_rhoNeg_apply_self]
    rw [← FreeGroup.mk_toWord (x := α (FreeGroup.of u)), hu',
      ← FreeGroup.mk_toWord (x := α (FreeGroup.of p)), hp']
    exact mk_rhoNeg_general A B Z
  have hW : coordWord (α * rhoNeg u p hup) u =
      FreeGroup.reduce (FreeGroup.invRev Z ++ FreeGroup.invRev A) := by
    show ((α * rhoNeg u p hup) (FreeGroup.of u)).toWord = _
    rw [hel, FreeGroup.toWord_mk]
  have hlen1 : (coordWord (α * rhoNeg u p hup) u).length ≤ Z.length + A.length := by
    rw [hW]
    calc (FreeGroup.reduce (FreeGroup.invRev Z ++ FreeGroup.invRev A)).length
        ≤ (FreeGroup.invRev Z ++ FreeGroup.invRev A).length := reduce_length_le _
      _ = Z.length + A.length := by rw [length_invRev_invRev]
  have hlen0 : (coordWord α u).length = Z.length + B.length := by
    rw [hu, length_invRev_append]
  have hmin := (noEndCancel_iff_local_min n α).mp hres
  have hNle : N α ≤ N (α * rhoNeg u p hup) := hmin.2.1 u p hup
  have hNform := N_mul_rhoNeg α u p hup
  have habs : FreeGroup.norm (α (FreeGroup.of u)) ≤
      FreeGroup.norm (α (FreeGroup.of u) * (α (FreeGroup.of p))⁻¹) :=
    (N_le_N_mul_rhoNeg_iff α u p hup).mp hNle
  have hge : Z.length + B.length ≤ (coordWord (α * rhoNeg u p hup) u).length := by
    have h1 : FreeGroup.norm (α (FreeGroup.of u)) = Z.length + B.length := hlen0
    have h2 : FreeGroup.norm ((α (FreeGroup.of u)) * (α (FreeGroup.of p))⁻¹) =
        (coordWord (α * rhoNeg u p hup) u).length := by
      rw [← mul_rhoNeg_apply_self α u p hup]
      rfl
    omega
  have hlen_eq : (coordWord (α * rhoNeg u p hup) u).length = Z.length + B.length :=
    le_antisymm (by omega) hge
  have hWeq : coordWord (α * rhoNeg u p hup) u =
      FreeGroup.invRev Z ++ FreeGroup.invRev A := by
    rw [hW]
    refine reduce_eq_of_length_eq _ ?_
    rw [← hW, hlen_eq, length_invRev_invRev, hAB]
  have hNeq : N (α * rhoNeg u p hup) = N α := by
    have h1 : FreeGroup.norm (α (FreeGroup.of u)) = Z.length + B.length := hlen0
    have h2 : FreeGroup.norm ((α (FreeGroup.of u)) * (α (FreeGroup.of p))⁻¹) =
        Z.length + B.length := by
      have hh : FreeGroup.norm ((α (FreeGroup.of u)) * (α (FreeGroup.of p))⁻¹) =
          (coordWord (α * rhoNeg u p hup) u).length := by
        rw [← mul_rhoNeg_apply_self α u p hup]
        rfl
      rw [hh, hlen_eq]
    have h3 : FreeGroup.norm ((α (FreeGroup.of u)) * (α (FreeGroup.of p))⁻¹) =
        FreeGroup.norm (α (FreeGroup.of u)) := by rw [h1, h2]
    rw [hNform, h3]
    exact Nat.sub_add_cancel (norm_le_N α u)
  refine sym_energy_step_of_single α (rhoNeg u p hup) hu hWeq ?_ hNeq
    (right_two_term_lt_minus A B Z hAB hE)
  intro k hk
  exact congrArg FreeGroup.toWord (mul_rhoNeg_apply_other (α := α) hup hk)

theorem sym_energy_step_right_rho_balminus {n : ℕ} (α : MulAut (FreeGroup (Fin n)))
    (hres : NoEndCancel n α) {p u : Fin n} (hup : u ≠ p)
    (A B Z : List (Fin n × Bool)) (hAB : A.length = B.length)
        (hE : (ebase n) ^ Z.length * wordEnergy (ebase n) (lweight) A
            + wordEnergy (ebase n) (lweight) (FreeGroup.invRev A)
          < (ebase n) ^ Z.length * wordEnergy (ebase n) (lweight) (FreeGroup.invRev B)
            + wordEnergy (ebase n) (lweight) B)
    (hp : coordWord α p = FreeGroup.invRev B ++ FreeGroup.invRev A)
    (hu : coordWord α u = FreeGroup.invRev Z ++ B) :
    N (α * rho u p hup) = N α ∧ eEnergySym (α * rho u p hup) < eEnergySym α := by

  have hp' : (α (FreeGroup.of p)).toWord =
      FreeGroup.invRev B ++ FreeGroup.invRev A := hp
  have hu' : (α (FreeGroup.of u)).toWord = FreeGroup.invRev Z ++ B := hu
  have hel : (α * rho u p hup) (FreeGroup.of u) =
      FreeGroup.mk (FreeGroup.invRev Z ++ FreeGroup.invRev A) := by
    rw [mul_rho_apply_self]
    rw [← FreeGroup.mk_toWord (x := α (FreeGroup.of u)), hu',
      ← FreeGroup.mk_toWord (x := α (FreeGroup.of p)), hp']
    exact mk_rho_general A B Z
  have hW : coordWord (α * rho u p hup) u =
      FreeGroup.reduce (FreeGroup.invRev Z ++ FreeGroup.invRev A) := by
    show ((α * rho u p hup) (FreeGroup.of u)).toWord = _
    rw [hel, FreeGroup.toWord_mk]
  have hlen1 : (coordWord (α * rho u p hup) u).length ≤ Z.length + A.length := by
    rw [hW]
    calc (FreeGroup.reduce (FreeGroup.invRev Z ++ FreeGroup.invRev A)).length
        ≤ (FreeGroup.invRev Z ++ FreeGroup.invRev A).length := reduce_length_le _
      _ = Z.length + A.length := by rw [length_invRev_invRev]
  have hlen0 : (coordWord α u).length = Z.length + B.length := by
    rw [hu, length_invRev_append]
  have hmin := (noEndCancel_iff_local_min n α).mp hres
  have hNle : N α ≤ N (α * rho u p hup) := hmin.1 u p hup
  have hNform := N_mul_rho α u p hup
  have habs : FreeGroup.norm (α (FreeGroup.of u)) ≤
      FreeGroup.norm (α (FreeGroup.of u) * α (FreeGroup.of p)) :=
    (N_le_N_mul_rho_iff α u p hup).mp hNle
  have hge : Z.length + B.length ≤ (coordWord (α * rho u p hup) u).length := by
    have h1 : FreeGroup.norm (α (FreeGroup.of u)) = Z.length + B.length := hlen0
    have h2 : FreeGroup.norm ((α (FreeGroup.of u)) * (α (FreeGroup.of p))) =
        (coordWord (α * rho u p hup) u).length := by
      rw [← mul_rho_apply_self α u p hup]
      rfl
    omega
  have hlen_eq : (coordWord (α * rho u p hup) u).length = Z.length + B.length :=
    le_antisymm (by omega) hge
  have hWeq : coordWord (α * rho u p hup) u =
      FreeGroup.invRev Z ++ FreeGroup.invRev A := by
    rw [hW]
    refine reduce_eq_of_length_eq _ ?_
    rw [← hW, hlen_eq, length_invRev_invRev, hAB]
  have hNeq : N (α * rho u p hup) = N α := by
    have h1 : FreeGroup.norm (α (FreeGroup.of u)) = Z.length + B.length := hlen0
    have h2 : FreeGroup.norm ((α (FreeGroup.of u)) * (α (FreeGroup.of p))) =
        Z.length + B.length := by
      have hh : FreeGroup.norm ((α (FreeGroup.of u)) * (α (FreeGroup.of p))) =
          (coordWord (α * rho u p hup) u).length := by
        rw [← mul_rho_apply_self α u p hup]
        rfl
      rw [hh, hlen_eq]
    have h3 : FreeGroup.norm ((α (FreeGroup.of u)) * (α (FreeGroup.of p))) =
        FreeGroup.norm (α (FreeGroup.of u)) := by rw [h1, h2]
    rw [hNform, h3]
    exact Nat.sub_add_cancel (norm_le_N α u)
  refine sym_energy_step_of_single α (rho u p hup) hu hWeq ?_ hNeq
    (right_two_term_lt_minus A B Z hAB hE)
  intro k hk
  exact congrArg FreeGroup.toWord (mul_rho_apply_other (α := α) hup hk)

theorem sym_energy_step_left_rho_balminus {n : ℕ} (α : MulAut (FreeGroup (Fin n)))
    (hres : NoEndCancel n α) {p v : Fin n} (hvp : v ≠ p)
    (A B X : List (Fin n × Bool)) (hAB : A.length = B.length)
        (hE : wordEnergy (ebase n) (lweight) B
            + (ebase n) ^ X.length * wordEnergy (ebase n) (lweight) (FreeGroup.invRev B)
          < (ebase n) ^ X.length * wordEnergy (ebase n) (lweight) A
            + wordEnergy (ebase n) (lweight) (FreeGroup.invRev A))
    (hp : coordWord α p = FreeGroup.invRev B ++ FreeGroup.invRev A)
    (hv : coordWord α v = X ++ FreeGroup.invRev A) :
    N (α * rhoNeg v p hvp) = N α ∧ eEnergySym (α * rhoNeg v p hvp) < eEnergySym α := by

  have hp' : (α (FreeGroup.of p)).toWord =
      FreeGroup.invRev B ++ FreeGroup.invRev A := hp
  have hwp : (α (FreeGroup.of p))⁻¹ = FreeGroup.mk (A ++ B) := by
    rw [← FreeGroup.mk_toWord (x := α (FreeGroup.of p)), hp']
    rw [mk_invRev_pair_general, inv_inv]
  have hv' : (α (FreeGroup.of v)).toWord = X ++ FreeGroup.invRev A := hv
  -- the new word of the moved row
  have hel : (α * rhoNeg v p hvp) (FreeGroup.of v) = FreeGroup.mk (X ++ B) := by
    rw [mul_rhoNeg_apply_self]
    rw [← FreeGroup.mk_toWord (x := α (FreeGroup.of v)), hv', hwp]
    exact mk_invRev_append_mul X A B
  have hW : coordWord (α * rhoNeg v p hvp) v = FreeGroup.reduce (X ++ B) := by
    show ((α * rhoNeg v p hvp) (FreeGroup.of v)).toWord = _
    rw [hel, FreeGroup.toWord_mk]
  have hlen1' : (coordWord (α * rhoNeg v p hvp) v).length ≤ X.length + B.length := by
    rw [hW]
    calc (FreeGroup.reduce (X ++ B)).length ≤ (X ++ B).length := reduce_length_le _
      _ = X.length + B.length := List.length_append (as := X) (bs := B)
  have hlen0 : (coordWord α v).length = X.length + A.length := by
    rw [hv, length_append_invRev]
  have hmin := (noEndCancel_iff_local_min n α).mp hres
  have hNle : N α ≤ N (α * rhoNeg v p hvp) := hmin.2.1 v p hvp
  have hNform := N_mul_rhoNeg α v p hvp
  have habs : FreeGroup.norm (α (FreeGroup.of v)) ≤
      FreeGroup.norm ((α (FreeGroup.of v)) * (α (FreeGroup.of p))⁻¹) :=
    (N_le_N_mul_rhoNeg_iff α v p hvp).mp hNle
  have hge : X.length + A.length ≤ (coordWord (α * rhoNeg v p hvp) v).length := by
    have h1 : FreeGroup.norm (α (FreeGroup.of v)) = X.length + A.length := hlen0
    have h2 : FreeGroup.norm ((α (FreeGroup.of v)) * (α (FreeGroup.of p))⁻¹) =
        (coordWord (α * rhoNeg v p hvp) v).length := by
      rw [← mul_rhoNeg_apply_self α v p hvp]
      rfl
    omega
  have hlen_eq : (coordWord (α * rhoNeg v p hvp) v).length = X.length + A.length :=
    le_antisymm (by omega) hge
  have hWeq : coordWord (α * rhoNeg v p hvp) v = X ++ B := by
    rw [hW]
    refine reduce_eq_of_length_eq (X ++ B) ?_
    rw [← hW, hlen_eq, List.length_append, hAB]
  have hNeq : N (α * rhoNeg v p hvp) = N α := by
    have h1 : FreeGroup.norm (α (FreeGroup.of v)) = X.length + A.length := hlen0
    have h2 : FreeGroup.norm ((α (FreeGroup.of v)) * (α (FreeGroup.of p))⁻¹) =
        X.length + A.length := by
      have hh : FreeGroup.norm ((α (FreeGroup.of v)) * (α (FreeGroup.of p))⁻¹) =
          (coordWord (α * rhoNeg v p hvp) v).length := by
        rw [← mul_rhoNeg_apply_self α v p hvp]
        rfl
      rw [hh, hlen_eq]
    have h3 : FreeGroup.norm ((α (FreeGroup.of v)) * (α (FreeGroup.of p))⁻¹) =
        FreeGroup.norm (α (FreeGroup.of v)) := by rw [h1, h2]
    rw [hNform, h3]
    exact Nat.sub_add_cancel (norm_le_N α v)
  refine sym_energy_step_of_single α (rhoNeg v p hvp) hv hWeq ?_ hNeq
    (left_two_term_lt A B X hAB hE)
  intro k hk
  exact congrArg FreeGroup.toWord (mul_rhoNeg_apply_other (α := α) hvp hk)

theorem sym_energy_step_right_lam_balminus {n : ℕ} (α : MulAut (FreeGroup (Fin n)))
    (hres : NoEndCancel n α) {p u : Fin n} (hup : u ≠ p)
    (A B Z : List (Fin n × Bool)) (hAB : A.length = B.length)
        (hE : (ebase n) ^ Z.length * wordEnergy (ebase n) (lweight) A
            + wordEnergy (ebase n) (lweight) (FreeGroup.invRev A)
          < (ebase n) ^ Z.length * wordEnergy (ebase n) (lweight) (FreeGroup.invRev B)
            + wordEnergy (ebase n) (lweight) B)
    (hp : coordWord α p = FreeGroup.invRev B ++ FreeGroup.invRev A)
    (hu : coordWord α u = FreeGroup.invRev B ++ Z) :
    N (α * lamNeg u p hup) = N α ∧ eEnergySym (α * lamNeg u p hup) < eEnergySym α := by

  have hp' : (α (FreeGroup.of p)).toWord =
      FreeGroup.invRev B ++ FreeGroup.invRev A := hp
  have hwp : (α (FreeGroup.of p))⁻¹ = FreeGroup.mk (A ++ B) := by
    rw [← FreeGroup.mk_toWord (x := α (FreeGroup.of p)), hp']
    rw [mk_invRev_pair_general, inv_inv]
  have hu' : (α (FreeGroup.of u)).toWord = FreeGroup.invRev B ++ Z := hu
  have hel : (α * lamNeg u p hup) (FreeGroup.of u) = FreeGroup.mk (A ++ Z) := by
    rw [mul_lamNeg_apply_self]
    rw [← FreeGroup.mk_toWord (x := α (FreeGroup.of u)), hu', hwp]
    exact mk_app_invRev_mul A B Z
  have hW : coordWord (α * lamNeg u p hup) u = FreeGroup.reduce (A ++ Z) := by
    show ((α * lamNeg u p hup) (FreeGroup.of u)).toWord = _
    rw [hel, FreeGroup.toWord_mk]
  have hlen1' : (coordWord (α * lamNeg u p hup) u).length ≤ A.length + Z.length := by
    rw [hW]
    calc (FreeGroup.reduce (A ++ Z)).length ≤ (A ++ Z).length := reduce_length_le _
      _ = A.length + Z.length := List.length_append (as := A) (bs := Z)
  have hlen0 : (coordWord α u).length = B.length + Z.length := by
    rw [hu, List.length_append, FreeGroup.invRev_length]
  have hmin := (noEndCancel_iff_local_min n α).mp hres
  have hNle : N α ≤ N (α * lamNeg u p hup) := hmin.2.2.2 u p hup
  have hNform := N_mul_lamNeg α u p hup
  have habs : FreeGroup.norm (α (FreeGroup.of u)) ≤
      FreeGroup.norm ((α (FreeGroup.of p))⁻¹ * (α (FreeGroup.of u))) :=
    (N_le_N_mul_lamNeg_iff α u p hup).mp hNle
  have hge : B.length + Z.length ≤ (coordWord (α * lamNeg u p hup) u).length := by
    have h1 : FreeGroup.norm (α (FreeGroup.of u)) = B.length + Z.length := hlen0
    have h2 : FreeGroup.norm ((α (FreeGroup.of p))⁻¹ * (α (FreeGroup.of u))) =
        (coordWord (α * lamNeg u p hup) u).length := by
      rw [← mul_lamNeg_apply_self α u p hup]
      rfl
    omega
  have hlen_eq : (coordWord (α * lamNeg u p hup) u).length = B.length + Z.length :=
    le_antisymm (by omega) hge
  have hWeq : coordWord (α * lamNeg u p hup) u = A ++ Z := by
    rw [hW]
    refine reduce_eq_of_length_eq (A ++ Z) ?_
    rw [← hW, hlen_eq, List.length_append, hAB]
  have hNeq : N (α * lamNeg u p hup) = N α := by
    have h1 : FreeGroup.norm (α (FreeGroup.of u)) = B.length + Z.length := hlen0
    have h2 : FreeGroup.norm ((α (FreeGroup.of p))⁻¹ * (α (FreeGroup.of u))) =
        B.length + Z.length := by
      have hh : FreeGroup.norm ((α (FreeGroup.of p))⁻¹ * (α (FreeGroup.of u))) =
          (coordWord (α * lamNeg u p hup) u).length := by
        rw [← mul_lamNeg_apply_self α u p hup]
        rfl
      rw [hh, hlen_eq]
    have h3 : FreeGroup.norm ((α (FreeGroup.of p))⁻¹ * (α (FreeGroup.of u))) =
        FreeGroup.norm (α (FreeGroup.of u)) := by rw [h1, h2]
    rw [hNform, h3]
    exact Nat.sub_add_cancel (norm_le_N α u)
  refine sym_energy_step_of_single α (lamNeg u p hup) hu hWeq ?_ hNeq
    (right_two_term_lt A B Z hAB hE)
  intro k hk
  exact congrArg FreeGroup.toWord (mul_lamNeg_apply_other (α := α) hup hk)

end Submission.Nielsen
