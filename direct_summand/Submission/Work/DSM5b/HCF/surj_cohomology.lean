import Mathlib
import Submission.Work.DSM5b.HCF.Surj
import Submission.Work.DSM5b.HCF.SurjSign
import Submission.Work.DSM5b.HCF.surjD_exact_high
import Submission.Work.DSM5b.HCF.surjD_top_injective
import Submission.Work.DSM5b.HCF.surjD_secFun

universe u

namespace Work.DSM5b.HCF

open Classical Finset

/-- `SurjIdx S₀ q` is empty whenever the tuples are too short to cover `S₀`. -/
theorem surjIdx_isEmpty {n : ℕ} {S₀ : Finset (Fin n)} {q : ℕ} (h : q + 1 < S₀.card) :
    IsEmpty (Work.DSM5b.SurjIdx S₀ q) := by
  refine ⟨fun τ => ?_⟩
  have h1 : (Work.DSM5b.tupRng τ.1).card ≤ q + 1 := by
    rw [Work.DSM5b.tupRng]
    calc (Finset.univ.image τ.1).card ≤ (Finset.univ : Finset (Fin (q + 1))).card :=
          Finset.card_image_le
      _ = q + 1 := Finset.card_fin _
  rw [τ.2] at h1
  omega

/-- The cohomology of the "surjection complex": for a subset `S₀ ⊆ Fin n` and an `R`-module `N`,
the complex `C^q = (SurjIdx S₀ q → N)` with differential `Work.DSM5b.surjD S₀ N` (dropping the
deletions which lose surjectivity onto `S₀`) is exact in every degree `p+1 ≠ ♯S₀ - 1`, and in the
top degree `p+1 = ♯S₀ - 1` (i.e. when `p + 2 = ♯S₀`, for `♯S₀ ≥ 2`) evaluation at the increasing
enumeration `Work.DSM5b.incTupleE S₀ (p+1) hp` admits a linear section by cocycles with prescribed
value at that tuple, and every cocycle differs from the section of its value by a coboundary.

This is the honest (tuple-indexed) Čech complex of the coefficient system supported on the single
subset `S₀`; it is the crux of the honest-vs-sorted comparison needed for
`Work.DSM5b.honestCohomologyFinite`.  Route: for a coefficient system `M`, the collapsed system
`M⁺(S) = M (S ∪ {j₀})` has a contractible honest complex (insertion homotopy `h y τ = y (tupIns j₀ τ)`,
using `tupDel_ins_zero`/`tupDel_ins_succ` of `Submission.Work.DSM5b.PerfComplexDefs`), which gives a
recursion on `♯S₀` with the vertex set shrinking by one; the base cases are immediate.  In the top
degree the section can be given explicitly as `y ↦ (τ ↦ sign(τ) • y)` on the bijections onto `S₀`.

Do NOT use `sorry` in the proof and do NOT use any frozen `DSMap`/`area_*` declaration. -/
theorem surj_cohomology {R : Type u} [CommRing R] {n : ℕ} (S₀ : Finset (Fin n)) (N : Type u) [AddCommGroup N] [Module R N] : (∀ p : ℕ, p + 2 ≠ S₀.card → ∀ z : Work.DSM5b.SurjTerm S₀ N (p + 1), Work.DSM5b.surjD (R := R) S₀ N (p + 1) z = 0 → z ∈ LinearMap.range (Work.DSM5b.surjD (R := R) S₀ N p)) ∧ (∀ (p : ℕ) (hp : p + 2 = S₀.card), 2 ≤ S₀.card → ∃ sec : N →ₗ[R] ↥(LinearMap.ker (Work.DSM5b.surjD (R := R) S₀ N (p + 1))), (∀ y : N, (sec y).1 (Work.DSM5b.incTupleE S₀ (p + 1) hp) = y) ∧ ∀ z : ↥(LinearMap.ker (Work.DSM5b.surjD (R := R) S₀ N (p + 1))), (z.1 - (sec (z.1 (Work.DSM5b.incTupleE S₀ (p + 1) hp))).1) ∈ LinearMap.range (Work.DSM5b.surjD (R := R) S₀ N p)) := by
  constructor
  · -- Exactness in every degree `p+1 ≠ ♯S₀ - 1`.
    intro p hpne z hz
    rcases lt_or_gt_of_ne hpne with hlt | hgt
    · -- `p + 2 < ♯S₀`: there are no surjective tuples, so the term is a zero module.
      haveI : IsEmpty (Work.DSM5b.SurjIdx S₀ (p + 1)) := surjIdx_isEmpty hlt
      have : z = 0 := funext fun τ => (IsEmpty.false τ).elim
      rw [this]
      exact Submodule.zero_mem _
    · -- `♯S₀ < p + 2`: vanishing above the top degree.
      exact surjD_exact_high S₀ N p (by omega) z hz
  · -- The top degree `p + 1 = ♯S₀ - 1`.
    intro p hp hcard
    -- The candidate section `y ↦ (τ ↦ sign τ • y)`.
    let secLin : N →ₗ[R] Work.DSM5b.SurjTerm S₀ N (p + 1) :=
      { toFun := fun y => fun τ => signOfR (R := R) τ hp • y
        map_add' := by
          intro y y'
          funext τ
          simp only [Pi.add_apply, smul_add]
        map_smul' := by
          intro r y
          funext τ
          simp only [Pi.smul_apply, RingHom.id_apply, smul_comm (signOfR (R := R) τ hp) r y] }
    have hsecLin : ∀ y : N, secLin y = fun τ => signOfR (R := R) τ hp • y := fun _ => rfl
    let sec : N →ₗ[R] ↥(LinearMap.ker (Work.DSM5b.surjD (R := R) S₀ N (p + 1))) :=
      LinearMap.codRestrict (LinearMap.ker (Work.DSM5b.surjD (R := R) S₀ N (p + 1))) secLin
        (fun y => by
          rw [LinearMap.mem_ker, hsecLin]
          exact surjD_secFun S₀ N p hp y)
    refine ⟨sec, ?_, ?_⟩
    · -- The section has the prescribed value at the increasing enumeration.
      intro y
      show (secLin y) (Work.DSM5b.incTupleE S₀ (p + 1) hp) = y
      rw [hsecLin]
      simp only [signOfR_incTupleE, one_smul]
    · -- Every cocycle equals the section of its value, since the top term below is the zero
      -- module and evaluation at the increasing enumeration is injective on cocycles.
      intro z
      have hsec_apply : ∀ y : N, (sec y).1 = secLin y := fun _ => rfl
      have hval : (sec (z.1 (Work.DSM5b.incTupleE S₀ (p + 1) hp))).1
            (Work.DSM5b.incTupleE S₀ (p + 1) hp) = z.1 (Work.DSM5b.incTupleE S₀ (p + 1) hp) := by
        rw [hsec_apply, hsecLin]
        simp only [signOfR_incTupleE, one_smul]
      have hz' : Work.DSM5b.surjD (R := R) S₀ N (p + 1)
          (sec (z.1 (Work.DSM5b.incTupleE S₀ (p + 1) hp))).1 = 0 :=
        (sec (z.1 (Work.DSM5b.incTupleE S₀ (p + 1) hp))).2
      have heq := surjD_top_injective S₀ N p hp z.1
        (sec (z.1 (Work.DSM5b.incTupleE S₀ (p + 1) hp))).1 z.2 hz' hval.symm
      have hzero : z.1 - (sec (z.1 (Work.DSM5b.incTupleE S₀ (p + 1) hp))).1 = 0 :=
        sub_eq_zero.mpr heq
      rw [hzero]
      exact Submodule.zero_mem _

end Work.DSM5b.HCF
