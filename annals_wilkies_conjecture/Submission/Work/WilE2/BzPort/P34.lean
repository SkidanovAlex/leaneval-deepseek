/-
  Ported (mechanically) from the lead-supplied reuse file
  `sources/reuse/ours/annals_van_der_waerden_conjecture/Submission/Commons/RingTheory/Ideal/card_minimalPrimes_quotient_le_univ.lean`
  section `mission.Commons.Algebra.MvPolynomial.exists_pow_idealOfVars_le_of_homogeneousComponent_mem` (piece 0).
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Data.Finsupp.PWO
import Mathlib.Data.Int.Star
import Mathlib.Data.Rat.Star
import Mathlib.Data.Sym.NatCard
import Mathlib.GroupTheory.CosetCover
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.NumberTheory.BernoulliPolynomials
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.GradedAlgebra.Radical
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Ideal.HasGoingUp
import Mathlib.RingTheory.IntegralClosure.GoingDown
import Mathlib.RingTheory.Jacobson.Artinian
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.MvPolynomial.Groebner
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Polynomial.HilbertPoly
import Mathlib.RingTheory.Regular.IsSMulRegular
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Submission.Work.WilE2.BzPort.P33

set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option warn.classDefReducibility false



set_option autoImplicit true

-- ==== from Submission.Commons.Algebra.MvPolynomial.exists_pow_idealOfVars_le_of_homogeneousComponent_mem ====
section

/-!
# `idealOfVars ^ N ≤ I` for a graded finite-codimensional ideal

Let `R = MvPolynomial σ ℂ` with `σ` finite, and let `I ⊆ R` be an ideal that is closed under
taking homogeneous components (i.e. `I` is a *homogeneous* / graded ideal for the total-degree
grading).  If the quotient `R ⧸ I` is finite dimensional over `ℂ`, then `I` contains a power
of the irrelevant ideal `idealOfVars = ⟨X i⟩`.

The proof is the standard graded argument.  Write `A = R ⧸ I` and let
`S j = map (mkQ I) (homogeneousSubmodule σ ℂ j) ⊆ A` be the image of the degree-`j` part.
Because `I` is homogeneous, the map
`(j : Fin M) → S j → A`, `x ↦ ∑ j, x j`
is injective (degree reasons), so `∑_{j < M} finrank S j ≤ finrank A` for every `M`.  A sum of
natural numbers with all partial sums bounded by the fixed integer `finrank A` has only finitely
many nonzero terms, whence `S j = ⊥` for `j ≥ N`.  Thus every homogeneous polynomial of degree
`≥ N` lies in `I`; in particular the degree-`N` monomials do, and since these generate
`idealOfVars ^ N` we get `idealOfVars ^ N ≤ I`.
-/

namespace Commons.Algebra.MvPolynomial

open _root_.MvPolynomial

set_option linter.style.haveILetI false

/-- If all partial sums `∑_{j < M} c j` are bounded by `d`, then only finitely many `c j` are
nonzero. -/
lemma exists_forall_eq_zero_of_sum_range_le {c : ℕ → ℕ} {d : ℕ}
    (h : ∀ M, ∑ j ∈ Finset.range M, c j ≤ d) : ∃ N, ∀ j ≥ N, c j = 0 := by
  by_contra hcon
  push_neg at hcon
  -- `hcon : ∀ N, ∃ j, N ≤ j ∧ c j ≠ 0`, so `{j | c j ≠ 0}` is infinite.
  have hinf : (Set.Infinite {j : ℕ | c j ≠ 0}) := by
    rw [Set.infinite_iff_exists_gt]
    intro N
    obtain ⟨j, hj, hjc⟩ := hcon (N + 1)
    exact ⟨j, hjc, hj⟩
  obtain ⟨t, ht_sub, ht_card⟩ := hinf.exists_subset_card_eq (d + 1)
  have ht_ne : ∀ j ∈ t, c j ≠ 0 := fun j hj => ht_sub hj
  have h1 : d + 1 ≤ ∑ j ∈ t, c j := by
    calc d + 1 = t.card := ht_card.symm
      _ = ∑ _j ∈ t, 1 := by simp
      _ ≤ ∑ j ∈ t, c j :=
          Finset.sum_le_sum (fun j hj => Nat.one_le_iff_ne_zero.mpr (ht_ne j hj))
  have h2 : ∑ j ∈ t, c j ≤ d := by
    have hsub : t ⊆ Finset.range (t.sup id + 1) := by
      intro j hj
      rw [Finset.mem_range]
      exact Nat.lt_succ_of_le (Finset.le_sup (f := id) hj)
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub ?_) (h _)
    intro j _ _
    exact Nat.zero_le _
  omega

/-- The images of the homogeneous pieces of `R` in `A = R ⧸ I` are linearly `ℂ`-independent in
the strong sense that the summation map out of a finite product is injective. -/
lemma finrank_sum_map_le {σ K : Type*} [Field K] [Fintype σ] [DecidableEq σ]
    (I : Ideal (MvPolynomial σ K))
    (hI : ∀ (j : ℕ) (p : MvPolynomial σ K),
      p ∈ I → MvPolynomial.homogeneousComponent j p ∈ I)
    (hfin : Module.Finite K (MvPolynomial σ K ⧸ I)) (M : ℕ) :
    ∑ j : Fin M, Module.finrank K ↥(Submodule.map ((I.mkQ).restrictScalars K)
        (MvPolynomial.homogeneousSubmodule σ K j.val)) ≤
      Module.finrank K (MvPolynomial σ K ⧸ I) := by
  classical
  let S : ℕ → Submodule K (MvPolynomial σ K ⧸ I) := fun j =>
    Submodule.map ((I.mkQ).restrictScalars K) (MvPolynomial.homogeneousSubmodule σ K j)
  have hker : ∀ p : MvPolynomial σ K, (I.mkQ.restrictScalars K) p = 0 ↔ p ∈ I := by
    intro p
    rw [LinearMap.restrictScalars_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  let F : ((j : Fin M) → ↥(S j.val)) →ₗ[K] (MvPolynomial σ K ⧸ I) :=
    { toFun := fun x => ∑ j : Fin M, ((x j : ↥(S j.val)) : MvPolynomial σ K ⧸ I)
      map_add' := fun x y => by
        simp only [Pi.add_apply, Submodule.coe_add, Finset.sum_add_distrib]
      map_smul' := fun c x => by
        simp only [Pi.smul_apply, Submodule.coe_smul, Finset.smul_sum, RingHom.id_apply] }
  have hF_apply : ∀ x, F x = ∑ j : Fin M, ((x j : ↥(S j.val)) : MvPolynomial σ K ⧸ I) :=
    fun x => rfl
  have hzero : ∀ z : (j : Fin M) → ↥(S j.val), F z = 0 → z = 0 := by
    intro z hz0
    choose t ht_mem ht_eq using fun j : Fin M => Submodule.mem_map.mp (z j).property
    have hqP : (I.mkQ.restrictScalars K) (∑ j : Fin M, t j) = 0 := by
      rw [map_sum]
      have hsum : (∑ j : Fin M, (I.mkQ.restrictScalars K) (t j))
          = ∑ j : Fin M, ((z j : ↥(S j.val)) : MvPolynomial σ K ⧸ I) :=
        Finset.sum_congr rfl (fun j _ => ht_eq j)
      rw [hsum, ← hF_apply z]; exact hz0
    have hP : (∑ j : Fin M, t j) ∈ I := (hker _).mp hqP
    funext i
    apply Subtype.ext
    show ((z i : ↥(S i.val)) : MvPolynomial σ K ⧸ I) = 0
    rw [← ht_eq i]
    apply (hker (t i)).mpr
    have h1 : (∑ j : Fin M, MvPolynomial.homogeneousComponent i.val (t j)) ∈ I := by
      have hh := hI i.val (∑ j : Fin M, t j) hP
      rwa [map_sum] at hh
    have heq : (∑ j : Fin M, MvPolynomial.homogeneousComponent i.val (t j))
        = ∑ j : Fin M, (if i.val = j.val then t j else 0) :=
      Finset.sum_congr rfl (fun j _ =>
        MvPolynomial.homogeneousComponent_of_mem (ht_mem j))
    have hsum2 : (∑ j : Fin M, (if i.val = j.val then t j else 0)) = t i := by
      rw [Fintype.sum_eq_single i]
      · simp
      · intro j hj
        rw [if_neg (fun h => hj (Fin.ext h).symm)]
    rw [heq, hsum2] at h1
    exact h1
  have hinj : Function.Injective F := by
    intro x y hxy
    have h0 : F (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    have hres := hzero (x - y) h0
    exact sub_eq_zero.mp hres
  haveI : ∀ j : Fin M, Module.Finite K ↥(S j.val) := fun j =>
    Module.Finite.of_fg (Submodule.FG.map ((I.mkQ).restrictScalars K)
      (MvPolynomial.homogeneousSubmodule_fg σ K j.val))
  have hle := LinearMap.finrank_le_finrank_of_injective (f := F) hinj
  rwa [Module.finrank_pi_fintype] at hle

theorem exists_pow_idealOfVars_le_of_homogeneousComponent_mem {σ : Type*} [Fintype σ] [DecidableEq σ]
    (I : Ideal (MvPolynomial σ ℂ))
    (hI : ∀ (j : ℕ) (p : MvPolynomial σ ℂ), p ∈ I → MvPolynomial.homogeneousComponent j p ∈ I)
    (hfin : Module.Finite ℂ (MvPolynomial σ ℂ ⧸ I)) :
    ∃ N : ℕ, MvPolynomial.idealOfVars σ ℂ ^ N ≤ I := by
  classical
  let A := MvPolynomial σ ℂ ⧸ I
  let q : MvPolynomial σ ℂ →ₗ[ℂ] A := (I.mkQ).restrictScalars ℂ
  let S : ℕ → Submodule ℂ A := fun j => Submodule.map q (MvPolynomial.homogeneousSubmodule σ ℂ j)
  have hker : ∀ p : MvPolynomial σ ℂ, q p = 0 ↔ p ∈ I := by
    intro p
    change (I.mkQ.restrictScalars ℂ) p = 0 ↔ p ∈ I
    rw [LinearMap.restrictScalars_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  -- Partial sums of `finrank ℂ (S j)` are bounded by `finrank ℂ A`.
  have hbound : ∀ M, ∑ j ∈ Finset.range M, Module.finrank ℂ (S j) ≤ Module.finrank ℂ A := by
    intro M
    rw [← Fin.sum_univ_eq_sum_range (fun j => Module.finrank ℂ (S j)) M]
    have h := finrank_sum_map_le (K := ℂ) I hI hfin M
    simpa only [S, A, q] using h
  obtain ⟨N, hN⟩ :=
    exists_forall_eq_zero_of_sum_range_le (c := fun j => Module.finrank ℂ (S j)) hbound
  refine ⟨N, ?_⟩
  -- Every homogeneous polynomial of degree `≥ N` lies in `I`.
  have hmem : ∀ j ≥ N, ∀ p ∈ MvPolynomial.homogeneousSubmodule σ ℂ j, p ∈ I := by
    intro j hj p hp
    haveI : Module.Finite ℂ ↥(S j) :=
      Module.Finite.of_fg (Submodule.FG.map q (MvPolynomial.homogeneousSubmodule_fg σ ℂ j))
    have hbot : S j = ⊥ := (Submodule.finrank_eq_zero).mp (hN j hj)
    have hmemS : q p ∈ S j := Submodule.mem_map.mpr ⟨p, hp, rfl⟩
    rw [hbot, Submodule.mem_bot] at hmemS
    exact (hker p).mp hmemS
  rw [MvPolynomial.pow_idealOfVars_eq_span]
  rw [Ideal.span_le]
  rintro y ⟨d, hd, rfl⟩
  exact hmem N le_rfl (MvPolynomial.monomial d 1) (by
    rw [MvPolynomial.mem_homogeneousSubmodule]
    exact MvPolynomial.isHomogeneous_monomial 1 hd)

end Commons.Algebra.MvPolynomial
end


