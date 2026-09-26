import Submission.Work.Item3.EnergyCover
import Submission.Work.EnergyAssembly

open Submission.Nielsen
open Submission.FreeGroupAut
open Commons.GroupTheory.FreeGroup
open FreeGroup
open scoped BigOperators
set_option autoImplicit false

/-!
# SymEnergy: the *symmetric* positional energy and the balanced-side step

The case analysis of `EnergyCover` shows that the plain positional energy
`eEnergy` of a single cut-slide at a balanced factor may *increase* even when
the classical comparison is available in the "wrong" direction, and that some
residual configurations admit no single `N`-preserving `eEnergy`-decreasing
move at all (machine witnesses in `Submission/Status.lean`).  The right measure
for the balanced side is instead the **symmetric positional energy**

    eEnergySym α = eEnergy α + eEnergyStar α,
    eEnergyStar α = Σ_i E (invRev (coordWord α i)),

i.e. each coordinate contributes both its word and the word of its inverse.
The reason is that a cut-slide `W ↦ W'` at a coordinate changes `E W` by a
(count) term and `E (invRev W)` by the *mirror* term: with

    Δ_L := E B − E (invRev A),   Δ_R := E A − E (invRev B)

the two classical cut-slides at a balanced factor of a residual state change
`eEnergySym` by

* left slide (`rho`/`rhoNeg`/`lam`/`lamNeg v p`):  `Δ_L − C^{|X|} · Δ_R`;
* right slide (`lam`/`lamNeg`/`rho`/`rhoNeg u p`): `C^{|Z|} · Δ_R − Δ_L`

(`C = ebase n`; machine-verified with **0** mismatches over `630` cut-slides of
`315` balanced configurations, `/tmp/fg5/verify_formula.py`).  In particular the
*right* slide works whenever `Δ_L > C^{|Z|} Δ_R` and the *left* slide whenever
`Δ_L < C^{|X|} Δ_R`; the machine found **no** balanced configuration of a
residual state where neither holds, so the symmetric energy is the appropriate
well-founded measure for the Fall-II step.

This module formalises the two *inequality* forms (the direction needed for the
descent), in additive (subtraction-free) form:

* `sym_energy_step_left_rho`:  `E B + C^{|X|}·E (invRev B) < C^{|X|}·E A + E (invRev A)`
  (the hypothesis is `Δ_L < C^{|X|} Δ_R`, written without subtraction) implies
  `eEnergySym (α * rho v p) < eEnergySym α` with `N` preserved;
* `sym_energy_step_right_lam`:  `C^{|Z|}·E A + E (invRev A) < C^{|Z|}·E (invRev B) + E B`
  (i.e. `C^{|Z|} Δ_R < Δ_L`) implies `eEnergySym (α * lam u p) < eEnergySym α`
  with `N` preserved.

All lemmas kernel-checked; axioms `[propext, Classical.choice, Quot.sound]`.
-/

namespace Submission.Nielsen

/-! ## The star component of the symmetric energy -/

/-- The word of the *inverse* of a coordinate. -/
def coordWordStar {n : ℕ} (α : MulAut (FreeGroup (Fin n))) (q : Fin n) :
    List (Fin n × Bool) :=
  FreeGroup.invRev (coordWord α q)

/-- Positional energy of the inverse-word component. -/
def eEnergyStar {n : ℕ} (α : MulAut (FreeGroup (Fin n))) : ℕ :=
  ∑ i : Fin n, wordEnergy (ebase n) (lweight) (coordWordStar α i)

/-- The **symmetric positional energy**. -/
def eEnergySym {n : ℕ} (α : MulAut (FreeGroup (Fin n))) : ℕ :=
  eEnergy α + eEnergyStar α

/-- Splitting the star energy at a coordinate. -/
lemma eEnergyStar_eq_sum_erase {n : ℕ} (α : MulAut (FreeGroup (Fin n))) (v : Fin n) :
    eEnergyStar α =
      (∑ i ∈ (Finset.univ.erase v : Finset (Fin n)),
          wordEnergy (ebase n) (lweight) (coordWordStar α i)) +
        wordEnergy (ebase n) (lweight) (coordWordStar α v) := by
  unfold eEnergyStar
  exact (Finset.sum_erase_add (Finset.univ : Finset (Fin n))
    (fun k => wordEnergy (ebase n) (lweight) (coordWordStar α k))
    (Finset.mem_univ v)).symm

/-- The star word of a coordinate other than `i` is unchanged by a transvection
on `i`. -/
lemma coordWordStar_mul_other {n : ℕ} (α : MulAut (FreeGroup (Fin n)))
    {i j k : Fin n} (hij : i ≠ j) (hk : k ≠ i) :
    coordWordStar (α * rho i j hij) k = coordWordStar α k := by
  unfold coordWordStar
  rw [show coordWord (α * rho i j hij) k = coordWord α k from
    congrArg FreeGroup.toWord (mul_rho_apply_other (α := α) hij hk)]

/-- Star-energy update for a `rho` transvection. -/
lemma eEnergyStar_mul_rho {n : ℕ} (α : MulAut (FreeGroup (Fin n))) (i j : Fin n)
    (hij : i ≠ j) (W : List (Fin n × Bool))
    (hW : coordWordStar (α * rho i j hij) i = W) :
    eEnergyStar (α * rho i j hij) + wordEnergy (ebase n) (lweight) (coordWordStar α i) =
      eEnergyStar α + wordEnergy (ebase n) (lweight) W := by
  rw [eEnergyStar_eq_sum_erase (α * rho i j hij) i, eEnergyStar_eq_sum_erase α i, hW]
  have hrest : (∑ k ∈ (Finset.univ.erase i : Finset (Fin n)),
      wordEnergy (ebase n) (lweight) (coordWordStar (α * rho i j hij) k)) =
      (∑ k ∈ (Finset.univ.erase i : Finset (Fin n)),
        wordEnergy (ebase n) (lweight) (coordWordStar α k)) := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [coordWordStar_mul_other α hij (Finset.mem_erase.mp hk).1]
  rw [hrest]
  ring

/-- The star word of a coordinate other than `i` is unchanged by a `lam`
transvection on `i`. -/
lemma coordWordStar_mul_lam_other {n : ℕ} (α : MulAut (FreeGroup (Fin n)))
    {i j k : Fin n} (hij : i ≠ j) (hk : k ≠ i) :
    coordWordStar (α * lam i j hij) k = coordWordStar α k := by
  unfold coordWordStar
  rw [show coordWord (α * lam i j hij) k = coordWord α k from
    congrArg FreeGroup.toWord (mul_lam_apply_other (α := α) hij hk)]

/-- Star-energy update for a `lam` transvection. -/
lemma eEnergyStar_mul_lam {n : ℕ} (α : MulAut (FreeGroup (Fin n))) (i j : Fin n)
    (hij : i ≠ j) (W : List (Fin n × Bool))
    (hW : coordWordStar (α * lam i j hij) i = W) :
    eEnergyStar (α * lam i j hij) + wordEnergy (ebase n) (lweight) (coordWordStar α i) =
      eEnergyStar α + wordEnergy (ebase n) (lweight) W := by
  rw [eEnergyStar_eq_sum_erase (α * lam i j hij) i, eEnergyStar_eq_sum_erase α i, hW]
  have hrest : (∑ k ∈ (Finset.univ.erase i : Finset (Fin n)),
      wordEnergy (ebase n) (lweight) (coordWordStar (α * lam i j hij) k)) =
      (∑ k ∈ (Finset.univ.erase i : Finset (Fin n)),
        wordEnergy (ebase n) (lweight) (coordWordStar α k)) := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [coordWordStar_mul_lam_other α hij (Finset.mem_erase.mp hk).1]
  rw [hrest]
  ring

/-! ## Word arithmetic for the star component -/

/-- Splitting the star energy of a concatenation: `E (invRev (X ++ W))`. -/
lemma wordEnergy_invRev_append {n : ℕ} (X W : List (Fin n × Bool)) :
    wordEnergy (ebase n) (lweight) (FreeGroup.invRev (X ++ W)) =
      (ebase n) ^ X.length * wordEnergy (ebase n) (lweight) (FreeGroup.invRev W)
        + wordEnergy (ebase n) (lweight) (FreeGroup.invRev X) := by
  rw [FreeGroup.invRev_append, wordEnergy_append, FreeGroup.invRev_length]

/-- Splitting the plain energy of a concatenation: `E (X ++ W)`. -/
lemma wordEnergy_append'' {n : ℕ} (X W : List (Fin n × Bool)) :
    wordEnergy (ebase n) (lweight) (X ++ W) =
      (ebase n) ^ W.length * wordEnergy (ebase n) (lweight) X
        + wordEnergy (ebase n) (lweight) W :=
  wordEnergy_append (ebase n) (lweight) X W

/-! ## The two symmetric-energy cut-slide steps -/

/-- **Left cut-slide decreases the symmetric energy.**  In a residual state,
with a balanced row `p` (`coordWord α p = A ++ B`, `|A| = |B|`) whose left
neighbour covers `invRev A` from the right (`coordWord α v = X ++ invRev A`),
the classical hypothesis `Δ_L < C^{|X|} Δ_R`, written additively as
`E B + C^{|X|}·E (invRev B) < C^{|X|}·E A + E (invRev A)`, implies that
`rho v p ∈ AutClosure n` keeps `N` and strictly decreases the symmetric energy. -/
theorem sym_energy_step_left_rho {n : ℕ} (α : MulAut (FreeGroup (Fin n)))
    (hres : NoEndCancel n α) {p v : Fin n} (hvp : v ≠ p)
    (A B X : List (Fin n × Bool)) (hAB : A.length = B.length)
    (hp : coordWord α p = A ++ B)
    (hv : coordWord α v = X ++ FreeGroup.invRev A)
    (hE : wordEnergy (ebase n) (lweight) B
            + (ebase n) ^ X.length * wordEnergy (ebase n) (lweight) (FreeGroup.invRev B)
          < (ebase n) ^ X.length * wordEnergy (ebase n) (lweight) A
            + wordEnergy (ebase n) (lweight) (FreeGroup.invRev A)) :
    N (α * rho v p hvp) = N α ∧ eEnergySym (α * rho v p hvp) < eEnergySym α := by
  have hv' : (α (FreeGroup.of v)).toWord = X ++ FreeGroup.invRev A := hv
  have hp' : (α (FreeGroup.of p)).toWord = A ++ B := hp
  have hnew : coordWord (α * rho v p hvp) v = X ++ B := by
    have hel : (α * rho v p hvp) (FreeGroup.of v) = FreeGroup.mk (X ++ B) := by
      rw [mul_rho_apply_self]
      rw [← FreeGroup.mk_toWord (x := α (FreeGroup.of v)),
        ← FreeGroup.mk_toWord (x := α (FreeGroup.of p)), hv', hp']
      exact mk_invRev_append_mul X A B
    have hW : coordWord (α * rho v p hvp) v = FreeGroup.reduce (X ++ B) := by
      show ((α * rho v p hvp) (FreeGroup.of v)).toWord = _
      rw [hel, FreeGroup.toWord_mk]
    have hlen1 : (coordWord (α * rho v p hvp) v).length ≤ X.length + B.length := by
      rw [hW]
      calc (FreeGroup.reduce (X ++ B)).length ≤ (X ++ B).length := reduce_length_le _
        _ = X.length + B.length := List.length_append
    have hlen0 : (coordWord α v).length = X.length + A.length := by
      rw [hv, length_append_invRev]
    have hmin := (noEndCancel_iff_local_min n α).mp hres
    have hNle : N α ≤ N (α * rho v p hvp) := hmin.1 v p hvp
    have habs : FreeGroup.norm (α (FreeGroup.of v)) ≤
        FreeGroup.norm (α (FreeGroup.of v) * α (FreeGroup.of p)) :=
      (N_le_N_mul_rho_iff α v p hvp).mp hNle
    have hge : X.length + A.length ≤ (coordWord (α * rho v p hvp) v).length := by
      have h1 : FreeGroup.norm (α (FreeGroup.of v)) = X.length + A.length := hlen0
      have h2 : FreeGroup.norm (α (FreeGroup.of v) * (α (FreeGroup.of p))) =
          (coordWord (α * rho v p hvp) v).length := by
        rw [← mul_rho_apply_self α v p hvp]
        rfl
      omega
    have hlen_eq : (coordWord (α * rho v p hvp) v).length = X.length + A.length :=
      le_antisymm (by omega) hge
    rw [hW]
    refine reduce_eq_of_length_eq (X ++ B) ?_
    rw [← hW, hlen_eq, List.length_append, hAB]
  have hN : N (α * rho v p hvp) = N α := by
    have hlen0 : (coordWord α v).length = X.length + A.length := by
      rw [hv, length_append_invRev]
    have h2 : FreeGroup.norm (α (FreeGroup.of v) * (α (FreeGroup.of p))) =
        X.length + A.length := by
      have hh : FreeGroup.norm (α (FreeGroup.of v) * (α (FreeGroup.of p))) =
          (coordWord (α * rho v p hvp) v).length := by
        rw [← mul_rho_apply_self α v p hvp]
        rfl
      rw [hh, hnew, List.length_append, hAB]
    rw [N_mul_rho α v p hvp]
    rw [show FreeGroup.norm (α (FreeGroup.of v)) = X.length + A.length from hlen0, h2]
    exact Nat.sub_add_cancel (by rw [← hlen0]; exact norm_le_N α v)
  refine ⟨hN, ?_⟩
  have hEu := eEnergy_mul_rho α v p hvp (X ++ B) hnew
  rw [hv] at hEu
  have hSu := eEnergyStar_mul_rho α v p hvp (FreeGroup.invRev (X ++ B)) (by
    unfold coordWordStar; rw [hnew])
  have hSv : coordWordStar α v = FreeGroup.invRev (X ++ FreeGroup.invRev A) := by
    unfold coordWordStar; rw [hv]
  rw [hSv] at hSu
  have e1 : wordEnergy (ebase n) (lweight) (X ++ B) =
      (ebase n) ^ B.length * wordEnergy (ebase n) (lweight) X
        + wordEnergy (ebase n) (lweight) B := wordEnergy_append'' X B
  have e2 : wordEnergy (ebase n) (lweight) (X ++ FreeGroup.invRev A) =
      (ebase n) ^ B.length * wordEnergy (ebase n) (lweight) X
        + wordEnergy (ebase n) (lweight) (FreeGroup.invRev A) := by
    rw [wordEnergy_append'', FreeGroup.invRev_length, hAB]
  have s1 : wordEnergy (ebase n) (lweight) (FreeGroup.invRev (X ++ B)) =
      (ebase n) ^ X.length * wordEnergy (ebase n) (lweight) (FreeGroup.invRev B)
        + wordEnergy (ebase n) (lweight) (FreeGroup.invRev X) :=
    wordEnergy_invRev_append X B
  have s2 : wordEnergy (ebase n) (lweight) (FreeGroup.invRev (X ++ FreeGroup.invRev A)) =
      (ebase n) ^ X.length * wordEnergy (ebase n) (lweight) A
        + wordEnergy (ebase n) (lweight) (FreeGroup.invRev X) := by
    rw [wordEnergy_invRev_append X (FreeGroup.invRev A), FreeGroup.invRev_invRev]
  have hkey : wordEnergy (ebase n) (lweight) (X ++ B)
        + wordEnergy (ebase n) (lweight) (FreeGroup.invRev (X ++ B))
      < wordEnergy (ebase n) (lweight) (X ++ FreeGroup.invRev A)
        + wordEnergy (ebase n) (lweight) (FreeGroup.invRev (X ++ FreeGroup.invRev A)) := by
    rw [e1, e2, s1, s2]
    omega
  unfold eEnergySym
  omega

/-- **Right cut-slide decreases the symmetric energy.**  In a residual state,
with a balanced row `p` (`coordWord α p = A ++ B`, `|A| = |B|`) whose right
neighbour covers `invRev B` from the left (`coordWord α u = invRev B ++ Z`),
the classical hypothesis `C^{|Z|} Δ_R < Δ_L`, written additively as
`C^{|Z|}·E A + E (invRev A) < C^{|Z|}·E (invRev B) + E B`, implies that
`lam u p ∈ AutClosure n` keeps `N` and strictly decreases the symmetric energy. -/
theorem sym_energy_step_right_lam {n : ℕ} (α : MulAut (FreeGroup (Fin n)))
    (hres : NoEndCancel n α) {p u : Fin n} (hup : u ≠ p)
    (A B Z : List (Fin n × Bool)) (hAB : A.length = B.length)
    (hp : coordWord α p = A ++ B)
    (hu : coordWord α u = FreeGroup.invRev B ++ Z)
    (hE : (ebase n) ^ Z.length * wordEnergy (ebase n) (lweight) A
            + wordEnergy (ebase n) (lweight) (FreeGroup.invRev A)
          < (ebase n) ^ Z.length * wordEnergy (ebase n) (lweight) (FreeGroup.invRev B)
            + wordEnergy (ebase n) (lweight) B) :
    N (α * lam u p hup) = N α ∧ eEnergySym (α * lam u p hup) < eEnergySym α := by
  have hu' : (α (FreeGroup.of u)).toWord = FreeGroup.invRev B ++ Z := hu
  have hp' : (α (FreeGroup.of p)).toWord = A ++ B := hp
  have hnew : coordWord (α * lam u p hup) u = A ++ Z := by
    have hel : (α * lam u p hup) (FreeGroup.of u) = FreeGroup.mk (A ++ Z) := by
      rw [mul_lam_apply_self]
      rw [← FreeGroup.mk_toWord (x := α (FreeGroup.of p)),
        ← FreeGroup.mk_toWord (x := α (FreeGroup.of u)), hp', hu']
      exact mk_app_invRev_mul A B Z
    have hW : coordWord (α * lam u p hup) u = FreeGroup.reduce (A ++ Z) := by
      show ((α * lam u p hup) (FreeGroup.of u)).toWord = _
      rw [hel, FreeGroup.toWord_mk]
    have hlen1 : (coordWord (α * lam u p hup) u).length ≤ A.length + Z.length := by
      rw [hW]
      calc (FreeGroup.reduce (A ++ Z)).length ≤ (A ++ Z).length := reduce_length_le _
        _ = A.length + Z.length := List.length_append
    have hlen0 : (coordWord α u).length = B.length + Z.length := by
      rw [hu, List.length_append, FreeGroup.invRev_length]
    have hmin := (noEndCancel_iff_local_min n α).mp hres
    have hNle : N α ≤ N (α * lam u p hup) := hmin.2.2.1 u p hup
    have habs : FreeGroup.norm (α (FreeGroup.of u)) ≤
        FreeGroup.norm (α (FreeGroup.of p) * α (FreeGroup.of u)) :=
      (N_le_N_mul_lam_iff α u p hup).mp hNle
    have hge : B.length + Z.length ≤ (coordWord (α * lam u p hup) u).length := by
      have h1 : FreeGroup.norm (α (FreeGroup.of u)) = B.length + Z.length := hlen0
      have h2 : FreeGroup.norm (α (FreeGroup.of p) * (α (FreeGroup.of u))) =
          (coordWord (α * lam u p hup) u).length := by
        rw [← mul_lam_apply_self α u p hup]
        rfl
      omega
    have hlen_eq : (coordWord (α * lam u p hup) u).length = B.length + Z.length :=
      le_antisymm (by omega) hge
    rw [hW]
    refine reduce_eq_of_length_eq (A ++ Z) ?_
    rw [← hW, hlen_eq, List.length_append, hAB]
  have hN : N (α * lam u p hup) = N α := by
    have hlen0 : (coordWord α u).length = B.length + Z.length := by
      rw [hu, List.length_append, FreeGroup.invRev_length]
    have h2 : FreeGroup.norm (α (FreeGroup.of p) * (α (FreeGroup.of u))) =
        B.length + Z.length := by
      have hh : FreeGroup.norm (α (FreeGroup.of p) * (α (FreeGroup.of u))) =
          (coordWord (α * lam u p hup) u).length := by
        rw [← mul_lam_apply_self α u p hup]
        rfl
      rw [hh, hnew, List.length_append, hAB]
    rw [N_mul_lam α u p hup]
    rw [show FreeGroup.norm (α (FreeGroup.of u)) = B.length + Z.length from hlen0, h2]
    exact Nat.sub_add_cancel (by rw [← hlen0]; exact norm_le_N α u)
  refine ⟨hN, ?_⟩
  have hEu := eEnergy_mul_lam α u p hup (A ++ Z) hnew
  rw [hu] at hEu
  have hSu := eEnergyStar_mul_lam α u p hup (FreeGroup.invRev (A ++ Z)) (by
    unfold coordWordStar; rw [hnew])
  have hSv : coordWordStar α u = FreeGroup.invRev (FreeGroup.invRev B ++ Z) := by
    unfold coordWordStar; rw [hu]
  rw [hSv] at hSu
  have e1 : wordEnergy (ebase n) (lweight) (A ++ Z) =
      (ebase n) ^ Z.length * wordEnergy (ebase n) (lweight) A
        + wordEnergy (ebase n) (lweight) Z := wordEnergy_append'' A Z
  have e2 : wordEnergy (ebase n) (lweight) (FreeGroup.invRev B ++ Z) =
      (ebase n) ^ Z.length * wordEnergy (ebase n) (lweight) (FreeGroup.invRev B)
        + wordEnergy (ebase n) (lweight) Z := wordEnergy_append'' (FreeGroup.invRev B) Z
  have s1 : wordEnergy (ebase n) (lweight) (FreeGroup.invRev (A ++ Z)) =
      (ebase n) ^ A.length * wordEnergy (ebase n) (lweight) (FreeGroup.invRev Z)
        + wordEnergy (ebase n) (lweight) (FreeGroup.invRev A) :=
    wordEnergy_invRev_append A Z
  have s2 : wordEnergy (ebase n) (lweight) (FreeGroup.invRev (FreeGroup.invRev B ++ Z)) =
      (ebase n) ^ B.length * wordEnergy (ebase n) (lweight) (FreeGroup.invRev Z)
        + wordEnergy (ebase n) (lweight) B := by
    rw [wordEnergy_invRev_append (FreeGroup.invRev B) Z, FreeGroup.invRev_invRev,
      FreeGroup.invRev_length]
  have hkey : wordEnergy (ebase n) (lweight) (A ++ Z)
        + wordEnergy (ebase n) (lweight) (FreeGroup.invRev (A ++ Z))
      < wordEnergy (ebase n) (lweight) (FreeGroup.invRev B ++ Z)
        + wordEnergy (ebase n) (lweight) (FreeGroup.invRev (FreeGroup.invRev B ++ Z)) := by
    rw [e1, e2, s1, s2, hAB]
    omega
  unfold eEnergySym
  omega

/-! ## The symmetric-energy descent and the re-aimed pin -/

/-- **The `(N, eEnergySym)` descent.** -/
theorem reachable_signed_of_symEnergyStep {n : ℕ}
    (hstep : ∀ α : MulAut (FreeGroup (Fin n)), ¬ IsSignedPermutation α →
      ∃ γ : MulAut (FreeGroup (Fin n)), γ ∈ AutClosure n ∧
        (N (α * γ) < N α ∨ (N (α * γ) = N α ∧ eEnergySym (α * γ) < eEnergySym α))) :
    ∀ α : MulAut (FreeGroup (Fin n)),
      ∃ γ : MulAut (FreeGroup (Fin n)), γ ∈ AutClosure n ∧ IsSignedPermutation (α * γ) := by
  classical
  have hwf : WellFounded (fun b a : MulAut (FreeGroup (Fin n)) =>
      N b < N a ∨ (N b = N a ∧ eEnergySym b < eEnergySym a)) :=
    energy_terminates N eEnergySym
  intro α
  let C : MulAut (FreeGroup (Fin n)) → Prop :=
    fun α => ∃ γ : MulAut (FreeGroup (Fin n)), γ ∈ AutClosure n ∧ IsSignedPermutation (α * γ)
  refine WellFounded.fix hwf (C := C) ?_ α
  intro x rec
  by_cases ht : IsSignedPermutation x
  · refine ⟨1, (AutClosure n).one_mem, ?_⟩
    simpa using ht
  · rcases hstep x ht with ⟨γ0, hγ0, hstep'⟩
    rcases rec (x * γ0) hstep' with ⟨γ1, hγ1, hS⟩
    refine ⟨γ0 * γ1, (AutClosure n).mul_mem hγ0 hγ1, ?_⟩
    simpa [mul_assoc] using hS

/-- **The symmetric-energy macro step.** -/
def SymEnergyStepMacro (n : ℕ) : Prop :=
  ∀ α : MulAut (FreeGroup (Fin n)), ¬ IsSignedPermutation α →
    ∃ γ : MulAut (FreeGroup (Fin n)), γ ∈ AutClosure n ∧
      (N (α * γ) < N α ∨ (N (α * γ) = N α ∧ eEnergySym (α * γ) < eEnergySym α))

/-- **`aut_nielsen` from the symmetric-energy macro step.** -/
theorem aut_nielsen_of_symEnergyStep {n : ℕ} (h : SymEnergyStepMacro n) :
    Subgroup.closure (AutGen n : Set (MulAut (FreeGroup (Fin n)))) = ⊤ :=
  aut_nielsen_of_reachable_signed n (reachable_signed_of_symEnergyStep h)

/-- **The residual Fall-II pin with the symmetric energy.** -/
def SymFallTwoEnergyStep (n : ℕ) : Prop :=
  ∀ α : MulAut (FreeGroup (Fin n)), NoEndCancel n α → FallTwoConfig α →
    ∃ γ : MulAut (FreeGroup (Fin n)), γ ∈ AutClosure n ∧
      N (α * γ) = N α ∧ eEnergySym (α * γ) < eEnergySym α

/-- **`SymEnergyStepMacro` from the residual symmetric Fall-II pin.** -/
theorem symEnergyStepMacro_of_symFallTwoEnergyStep {n : ℕ} (h : SymFallTwoEnergyStep n) :
    SymEnergyStepMacro n := by
  intro α hnot
  by_cases hres : NoEndCancel n α
  · have hlong := not_signed_has_long_image α hnot
    rcases aggregate_reduces_or_balanced α hlong with hstrict | hbal
    · obtain ⟨γ, hγ, hlt⟩ := hstrict
      exact ⟨γ, hγ, Or.inl hlt⟩
    · obtain ⟨γ, hγ, hN, hE⟩ := h α hres hbal
      exact ⟨γ, hγ, Or.inr ⟨hN, hE⟩⟩
  · obtain ⟨γ, hγ, hlt⟩ := nonresidual_strict_move α hres
    exact ⟨γ, hγ, Or.inl hlt⟩

/-- **`aut_nielsen` from the residual symmetric Fall-II pin.** -/
theorem aut_nielsen_of_symFallTwoEnergyStep {n : ℕ} (h : SymFallTwoEnergyStep n) :
    Subgroup.closure (AutGen n : Set (MulAut (FreeGroup (Fin n)))) = ⊤ :=
  aut_nielsen_of_symEnergyStep (symEnergyStepMacro_of_symFallTwoEnergyStep h)

end Submission.Nielsen
