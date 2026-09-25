/-
# The last mile of the Golod--Shafarevich route: an infinite unramified pro-3 extension of a
totally real number field yields Martinet's asymptotically-good totally real tower

**STATUS: in progress.**  CHAIN C (the Golod--Shafarevich / pro-`p` route).  Off the
`Submission.lean` proof path.

## What this module adds

The Golod--Shafarevich route to Martinet's theorem has exactly three parts:

1. a TOTALLY REAL number field `F` whose class group has a large 3-rank;
2. the maximal unramified pro-3 extension `K` of `F` is INFINITE (Golod--Shafarevich:
   a finite pro-`p` group presented with `d` generators and `r` relators satisfies
   `d ^ 2 < 4 * r`, while the arithmetic relation rank of an unramified pro-`p` group is
   bounded by `d + C`);
3. the extraction of an infinite tower of unramified steps from `K`.

This module provides part 3 in its general form: from ANY infinite Galois extension
`K / F` of a totally real number field all of whose finite Galois subextensions are
unramified at every finite prime with pro-3 (indeed any odd prime `p`) Galois group, it
builds a family `Fam : ℕ → Type` of number fields with

    `rootDiscr (Fam (n + 1)) = rootDiscr (Fam n)`   and   `2 ≤ [Fam (n + 1) : Fam n]`

(all levels totally real), hence Martinet's asymptotically-good totally real tower -- via
the shared-commons `totallyReal_rootDiscr_bounded_of_tower`.

MATHEMATICS.  Total reality is FREE for odd `p`: at a real place `v`, the local degree
`[K_w : F_v]` divides both `2` (the local degree of a real place) and `p ^ k` (the
`p`-group order), hence is `1`; so every finite pro-`p` unramified subextension is totally
real (`Commons.NumberTheory.NumberField.isTotallyReal_of_finite_galois_unramified_pGroup_odd`).
The tower is built by recursion: each level is enlarged by the normal closure
(`Mathlib.` `normalClosure`, which is finite-dimensional over `F` and Galois over `F`) of
the previous level composed with a finite Galois subextension of degree at least twice the
previous level's degree; the factor `2` gives a genuinely increasing chain, and the
unramifiedness of each step follows from the tower formula for the different
(`differentIdeal_eq_differentIdeal_mul_differentIdeal`) plus `𝓞`-level unramifiedness of
each level over `F`.
-/

import Mathlib
import Submission.TowerToFamily
import Submission.Commons.FieldTheory.Galois.exists_finite_galois_finrank_ge_of_infinite_gal
import Submission.Commons.NumberTheory.NumberField.differentIdeal_eq_top_of_rootDiscr_eq
import Submission.Commons.NumberTheory.NumberField.isTotallyReal_of_finite_galois_unramified_pGroup_odd
import Submission.Commons.NumberTheory.NumberField.rootDiscr_eq_of_different_eq_top
import Submission.Commons.NumberTheory.NumberField.totallyReal_rootDiscr_bounded_of_tower
import Submission.Commons.NumberTheory.NumberField.abs_discr_le_of_rootDiscr_le

open scoped NumberField
open NumberField
open IntermediateField

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 400000

namespace Submission.NumberField

noncomputable section

variable {F K : Type} [Field F] [NumberField F] [NumberField.IsTotallyReal F] [Field K]
  [Algebra F K] [IsGalois F K]

/-- **The one-step engine.**  If `K / F` is an infinite Galois extension, every finite
dimensional Galois intermediate field `E` can be enlarged to a finite dimensional Galois
intermediate field `E'` whose `F`-degree is at least twice that of `E`: take the normal
closure over `F` (inside `K`) of `E` composed with a finite Galois subextension of large
degree, which is finite dimensional and Galois over `F`. -/
theorem exists_galois_step (hinf : Infinite (K ≃ₐ[F] K)) (E : IntermediateField F K)
    [FiniteDimensional F E] [IsGalois F E] :
    ∃ E' : IntermediateField F K, FiniteDimensional F E' ∧ IsGalois F E' ∧ E ≤ E' ∧
      2 * Module.finrank F ↥E ≤ Module.finrank F ↥E' := by
  classical
  obtain ⟨M, hMfd, hMgal, hMdeg⟩ :=
    Commons.FieldTheory.Galois.exists_finite_galois_finrank_ge_of_infinite_gal
      (F := F) (K := K) hinf (2 * Module.finrank F ↥E)
  haveI : FiniteDimensional F M := hMfd
  haveI : IsGalois F M := hMgal
  refine ⟨normalClosure F ↥(E ⊔ M) K, ?_, ?_, ?_, ?_⟩
  · haveI : FiniteDimensional F ↥(E ⊔ M) := finiteDimensional_sup E M
    exact normalClosure.is_finiteDimensional F ↥(E ⊔ M) K
  · haveI : FiniteDimensional F ↥(E ⊔ M) := finiteDimensional_sup E M
    exact IsGalois.normalClosure F ↥(E ⊔ M) K
  · exact le_trans le_sup_left (le_normalClosure (E ⊔ M))
  · haveI : FiniteDimensional F ↥(E ⊔ M) := finiteDimensional_sup E M
    haveI : FiniteDimensional F ↥(normalClosure F ↥(E ⊔ M) K) :=
      normalClosure.is_finiteDimensional F ↥(E ⊔ M) K
    calc 2 * Module.finrank F ↥E ≤ Module.finrank F M := hMdeg
      _ = Module.finrank F ↥(M : IntermediateField F K) := rfl
      _ ≤ Module.finrank F ↥(E ⊔ M) := finrank_le_of_le_right le_sup_right
      _ ≤ Module.finrank F ↥(normalClosure F ↥(E ⊔ M) K) :=
          finrank_le_of_le_right (le_normalClosure (E ⊔ M))

/-- The state of the recursion: a finite dimensional Galois intermediate field. -/
abbrev GaloisState (F K : Type*) [Field F] [Field K] [Algebra F K] :=
  { E : IntermediateField F K // FiniteDimensional F E ∧ IsGalois F E }

/-- The recursion step. -/
noncomputable def galoisNext (hinf : Infinite (K ≃ₐ[F] K)) (s : GaloisState F K) :
    GaloisState F K :=
  haveI : FiniteDimensional F s.1 := s.2.1
  haveI : IsGalois F s.1 := s.2.2
  ⟨Classical.choose (exists_galois_step (F := F) (K := K) hinf s.1),
    (Classical.choose_spec (exists_galois_step (F := F) (K := K) hinf s.1)).1,
    (Classical.choose_spec (exists_galois_step (F := F) (K := K) hinf s.1)).2.1⟩

theorem galoisNext_le (hinf : Infinite (K ≃ₐ[F] K)) (s : GaloisState F K) :
    s.1 ≤ (galoisNext hinf s).1 := by
  haveI : FiniteDimensional F s.1 := s.2.1
  haveI : IsGalois F s.1 := s.2.2
  exact (Classical.choose_spec (exists_galois_step (F := F) (K := K) hinf s.1)).2.2.1

theorem galoisNext_deg (hinf : Infinite (K ≃ₐ[F] K)) (s : GaloisState F K) :
    2 * Module.finrank F ↥(s.1) ≤ Module.finrank F ↥((galoisNext hinf s).1) := by
  haveI : FiniteDimensional F s.1 := s.2.1
  haveI : IsGalois F s.1 := s.2.2
  exact (Classical.choose_spec (exists_galois_step (F := F) (K := K) hinf s.1)).2.2.2

/-- The chain of finite dimensional Galois levels. -/
noncomputable def galoisChain (hinf : Infinite (K ≃ₐ[F] K)) : ℕ → GaloisState F K :=
  Nat.rec (motive := fun _ => GaloisState F K)
    ⟨⊥, inferInstance, inferInstance⟩ (fun _ s => galoisNext hinf s)

theorem galoisChain_succ (hinf : Infinite (K ≃ₐ[F] K)) (n : ℕ) :
    galoisChain hinf (n + 1) = galoisNext hinf (galoisChain hinf n) := rfl

theorem galoisChain_le_succ (hinf : Infinite (K ≃ₐ[F] K)) (n : ℕ) :
    (galoisChain hinf n).1 ≤ (galoisChain hinf (n + 1)).1 := by
  rw [galoisChain_succ]
  exact galoisNext_le hinf _

theorem galoisChain_deg (hinf : Infinite (K ≃ₐ[F] K)) (n : ℕ) :
    2 * Module.finrank F ↥((galoisChain hinf n).1) ≤
      Module.finrank F ↥((galoisChain hinf (n + 1)).1) := by
  rw [galoisChain_succ]
  exact galoisNext_deg hinf _

/-- The tower family attached to the chain. -/
abbrev proTowerFam (hinf : Infinite (K ≃ₐ[F] K)) (n : ℕ) : Type :=
  ↥((galoisChain hinf n).1)

theorem proTowerFam_finite (hinf : Infinite (K ≃ₐ[F] K)) (n : ℕ) :
    FiniteDimensional F ((proTowerFam hinf) n) := (galoisChain hinf n).2.1

theorem proTowerFam_galois (hinf : Infinite (K ≃ₐ[F] K)) (n : ℕ) :
    IsGalois F ((proTowerFam hinf) n) := (galoisChain hinf n).2.2

theorem proTowerFam_numberField (hinf : Infinite (K ≃ₐ[F] K)) (n : ℕ) :
    NumberField ((proTowerFam hinf) n) := by
  haveI : FiniteDimensional F ((proTowerFam hinf) n) := proTowerFam_finite hinf n
  exact NumberField.of_module_finite F _

/-- **Every level of the tower is totally real.**  For an odd prime `p` the total reality is
free: a real place of `F` has local degree dividing both `2` and a power of `p`. -/
theorem proTowerFam_totallyReal (hinf : Infinite (K ≃ₐ[F] K))
    (hunr : ∀ (L : IntermediateField F K) [NumberField ↥L], FiniteDimensional F L →
      IsGalois F L → differentIdeal (𝓞 F) (𝓞 ↥L) = ⊤)
    (hpro : ∀ (L : IntermediateField F K) [NumberField ↥L], FiniteDimensional F L →
      IsGalois F L → IsPGroup 3 (L ≃ₐ[F] L))
    (n : ℕ) : NumberField.IsTotallyReal ((proTowerFam hinf) n) := by
  haveI : FiniteDimensional F ((proTowerFam hinf) n) := proTowerFam_finite hinf n
  haveI : IsGalois F ((proTowerFam hinf) n) := proTowerFam_galois hinf n
  haveI : NumberField ((proTowerFam hinf) n) := proTowerFam_numberField hinf n
  exact Commons.NumberTheory.NumberField.isTotallyReal_of_finite_galois_unramified_pGroup_odd
    (hpro _ (proTowerFam_finite hinf n) (proTowerFam_galois hinf n))
    (hunr _ (proTowerFam_finite hinf n) (proTowerFam_galois hinf n))

/-- **The degree of a step, from the degree over the base.**  If a finite extension `E'/E` of
intermediate fields satisfies `2 * [E : F] ≤ [E' : F]`, then it has degree at least two. -/
theorem step_deg {E E' : IntermediateField F K} (h : E ≤ E') [FiniteDimensional F E]
    [FiniteDimensional F E'] [Algebra ↥E ↥E'] [IsScalarTower F ↥E ↥E']
    (hdeg : 2 * Module.finrank F ↥E ≤ Module.finrank F ↥E') :
    2 ≤ Module.finrank ↥E ↥E' := by
  haveI hFD : Module.Finite ↥E ↥E' := Module.Finite.right F ↥E ↥E'
  have hmul := Module.finrank_mul_finrank F ↥E ↥E'
  have hpos : 0 < Module.finrank F ↥E := Module.finrank_pos
  have hkey : Module.finrank F ↥E * 2 ≤ Module.finrank F ↥E * Module.finrank ↥E ↥E' := by
    rw [hmul]
    simpa [Nat.mul_comm] using hdeg
  exact Nat.le_of_mul_le_mul_left hkey hpos

/-- The algebra structure on consecutive levels of the tower. -/
abbrev proTowerAlg (hinf : Infinite (K ≃ₐ[F] K)) (n : ℕ) :
    Algebra ((proTowerFam hinf) n) ((proTowerFam hinf) (n+1)) :=
  (IntermediateField.inclusion (galoisChain_le_succ hinf n)).toAlgebra

/-- The scalar tower `F ⊆ E n ⊆ E (n+1)` for the canonical algebra structure. -/
theorem proTowerFam_scalarTower (hinf : Infinite (K ≃ₐ[F] K)) (n : ℕ) :
    letI : Algebra ((proTowerFam hinf) n) ((proTowerFam hinf) (n+1)) := proTowerAlg hinf n
    IsScalarTower F ((proTowerFam hinf) n) ((proTowerFam hinf) (n+1)) := by
  letI : Algebra ((proTowerFam hinf) n) ((proTowerFam hinf) (n+1)) :=
    (IntermediateField.inclusion (galoisChain_le_succ hinf n)).toAlgebra
  exact IsScalarTower.of_algebraMap_eq' rfl

/-- **Root discriminant is constant along the tower.**  Each level is unramified over the base
`F`, so it has the same root discriminant as `F`. -/
theorem proTowerFam_rootDiscr_base (hinf : Infinite (K ≃ₐ[F] K))
    (hunr : ∀ (L : IntermediateField F K) [NumberField ↥L], FiniteDimensional F L →
      IsGalois F L → differentIdeal (𝓞 F) (𝓞 ↥L) = ⊤) (n : ℕ)
    [NumberField ((proTowerFam hinf) n)] :
    rootDiscr ((proTowerFam hinf) n) = rootDiscr F := by
  haveI hfdn : FiniteDimensional F ((proTowerFam hinf) n) := proTowerFam_finite hinf n
  exact Commons.NumberTheory.NumberField.rootDiscr_eq_of_different_eq_top
    (hunr _ hfdn (proTowerFam_galois hinf n))

/-- **The Golod--Shafarevich assembly.**  An infinite unramified pro-3 Galois extension of a
totally real number field yields an infinite everywhere-unramified tower of totally real number
fields with steps of degree at least two -- exactly the `UnramifiedTowerData` interface consumed
by `Submission.Towers.milestone_unramified_tower`. -/
theorem exists_unramifiedTowerData_of_infinite_unramified_prothree (hinf : Infinite (K ≃ₐ[F] K))
    (hunr : ∀ (L : IntermediateField F K) [NumberField ↥L], FiniteDimensional F L →
      IsGalois F L → differentIdeal (𝓞 F) (𝓞 ↥L) = ⊤)
    (hpro : ∀ (L : IntermediateField F K) [NumberField ↥L], FiniteDimensional F L →
      IsGalois F L → IsPGroup 3 (L ≃ₐ[F] L)) :
    ∃ Fam : ℕ → Type, Nonempty (Submission.Towers.UnramifiedTowerData Fam) := by
  haveI hfd : ∀ n : ℕ, FiniteDimensional F ((proTowerFam hinf) n) := proTowerFam_finite hinf
  haveI hnf : ∀ n : ℕ, NumberField ((proTowerFam hinf) n) := proTowerFam_numberField hinf
  haveI htr : ∀ n : ℕ, NumberField.IsTotallyReal ((proTowerFam hinf) n) :=
    proTowerFam_totallyReal hinf hunr hpro
  letI halg : ∀ n : ℕ, Algebra ((proTowerFam hinf) n) ((proTowerFam hinf) (n+1)) :=
    proTowerAlg hinf
  letI hmod : ∀ n : ℕ, Module ((proTowerFam hinf) n) ((proTowerFam hinf) (n+1)) := fun n => by
    letI := proTowerAlg hinf n
    infer_instance
  refine ⟨fun n => proTowerFam hinf n,
    ⟨{ alg := halg, unram_step := ?_, deg := ?_ }⟩⟩
  · intro n
    haveI hNFn : NumberField ((proTowerFam hinf) n) := proTowerFam_numberField hinf n
    haveI hNF1 : NumberField ((proTowerFam hinf) (n+1)) := proTowerFam_numberField hinf (n+1)
    have hmid : rootDiscr ((proTowerFam hinf) n) = rootDiscr F :=
      proTowerFam_rootDiscr_base hinf hunr n
    have htop : rootDiscr ((proTowerFam hinf) (n+1)) = rootDiscr F :=
      proTowerFam_rootDiscr_base hinf hunr (n+1)
    exact Commons.NumberTheory.NumberField.differentIdeal_eq_top_of_rootDiscr_eq
      (htop.trans hmid.symm)
  · intro n
    haveI hst : IsScalarTower F ((proTowerFam hinf) n) ((proTowerFam hinf) (n+1)) :=
      proTowerFam_scalarTower hinf n
    exact step_deg (galoisChain_le_succ hinf n) (galoisChain_deg hinf n)

/-- **Martinet's theorem from an infinite unramified pro-3 extension of a totally real field.** -/
theorem exists_totallyReal_discr_le_of_infinite_unramified_prothree (hinf : Infinite (K ≃ₐ[F] K))
    (hunr : ∀ (L : IntermediateField F K) [NumberField ↥L], FiniteDimensional F L →
      IsGalois F L → differentIdeal (𝓞 F) (𝓞 ↥L) = ⊤)
    (hpro : ∀ (L : IntermediateField F K) [NumberField ↥L], FiniteDimensional F L →
      IsGalois F L → IsPGroup 3 (L ≃ₐ[F] L)) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, ∃ d : ℕ, N ≤ d ∧
      ∃ (K' : Type) (_ : Field K') (_ : NumberField K') (_ : NumberField.IsTotallyReal K'),
        Module.finrank ℚ K' = d ∧ |(NumberField.discr K' : ℝ)| ≤ C ^ d := by
  obtain ⟨Fam, hT⟩ := exists_unramifiedTowerData_of_infinite_unramified_prothree hinf hunr hpro
  exact Submission.Towers.exists_totallyReal_discr_le_of_unramified_tower hT.some

end

end Submission.NumberField
