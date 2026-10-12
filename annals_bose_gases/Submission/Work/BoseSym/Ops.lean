import Mathlib.Order.CompletePartialOrder
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseSym.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# BoseSym — operations on the energy space

This module collects the pointwise operations on `L²` elements and on elements
of the energy space `Hsub N L` that the bosonic reduction needs:

* `absLp`, `sgnLp`, `absPoint` — the absolute value of a function and the
  corresponding "signed gradient", which together implement the pointwise map
  `u ↦ |u|` (Kato's inequality at the level of the Dirichlet form);
* `tauPerm`, `permLp`, `permAmb`, `symAvgAmb` — the action of a permutation of
  the particles on configuration space and on the energy space, together with
  the symmetrisation average.
-/

namespace Work.BoseSym

open MeasureTheory Filter
open BoseGases
open Submission.BoseGases
open scoped Topology Real ContDiff ENNReal

noncomputable section

set_option autoImplicit false

/-! ## The sign function and the absolute value of an `L²` element -/

/-- The sign function: `1` on `(0,∞)`, `-1` on `(-∞,0)` and `0` at `0`. -/
def sgnZ (t : ℝ) : ℝ := if 0 < t then 1 else if t < 0 then -1 else 0

lemma measurable_sgnZ : Measurable sgnZ := by
  unfold sgnZ
  exact Measurable.ite measurableSet_Ioi measurable_const
    (Measurable.ite measurableSet_Iio measurable_const measurable_const)

lemma abs_sgnZ_le (t : ℝ) : |sgnZ t| ≤ 1 := by
  unfold sgnZ
  split_ifs <;> norm_num

lemma sgnZ_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ sgnZ t := by
  unfold sgnZ
  split_ifs with h1 h2
  · norm_num
  · exact absurd h2 (not_lt.mpr ht)
  · norm_num

lemma sgnZ_mul_self (t : ℝ) : sgnZ t * t = |t| := by
  unfold sgnZ
  split_ifs with h1 h2
  · rw [one_mul, abs_of_pos h1]
  · rw [neg_mul, abs_of_neg h2]
    ring
  · have h0 : t = 0 := le_antisymm (not_lt.mp h1) (not_lt.mp h2)
    rw [h0, mul_zero, abs_zero]

/-! ## The permutation action -/

/-- The permutation of the particles acting on configuration space. -/
def tauPerm (N : ℕ) (σ : Equiv.Perm (Fin N)) : Conf N → Conf N := fun x i => x (σ i)

lemma tauPerm_measurable (N : ℕ) (σ : Equiv.Perm (Fin N)) : Measurable (tauPerm N σ) := by
  have h : tauPerm N σ = fun x : Conf N => x ∘ σ := rfl
  rw [h]
  exact measurable_pi_iff.2 fun i => measurable_pi_apply (σ i)

/-- Lebesgue measure on configuration space is invariant under the permutation
action. -/
theorem measurePreserving_tauPerm (N : ℕ) (σ : Equiv.Perm (Fin N)) :
    MeasurePreserving (tauPerm N σ) (volC N) (volC N) := by
  have h := volume_measurePreserving_piCongrLeft (fun _ : Fin N => E3) σ.symm
  have hfun : ((MeasurableEquiv.piCongrLeft (fun _ : Fin N => E3) σ.symm : Conf N ≃ᵐ Conf N) :
      Conf N → Conf N) = tauPerm N σ := by
    funext x i
    simp [MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft, Equiv.piCongrLeft_symm_apply, tauPerm]
  rwa [hfun] at h

/-- The permutation action on test functions. -/
noncomputable def permTest (N : ℕ) (L : ℝ) (σ : Equiv.Perm (Fin N)) (F : testSub N L) :
    testSub N L :=
  ⟨fun x => (F : Conf N → ℝ) (tauPerm N σ x), permComp_contDiff σ F.2.1,
    perm_tsupport_openBox σ F.2.2⟩

/-- The permutation action on `L²`, as a composition with `tauPerm`. -/
noncomputable def permLp (N : ℕ) (σ : Equiv.Perm (Fin N)) : L2 N →+ L2 N :=
  Lp.compMeasurePreserving (tauPerm N σ) (measurePreserving_tauPerm N σ)

/-- The permutation action on the ambient space: the function part is composed
with `tauPerm`, and the gradient components are permuted accordingly. -/
noncomputable def permAmb (N : ℕ) (σ : Equiv.Perm (Fin N)) (p : Amb N) : Amb N :=
  (permLp N σ p.1, fun j => permLp N σ (p.2 (σ.symm j.1, j.2)))

@[simp] lemma permAmb_fst {N : ℕ} (σ : Equiv.Perm (Fin N)) (p : Amb N) :
    (permAmb N σ p).1 = permLp N σ p.1 := rfl

@[simp] lemma permAmb_snd {N : ℕ} (σ : Equiv.Perm (Fin N)) (p : Amb N) (j : GIdx N) :
    (permAmb N σ p).2 j = permLp N σ (p.2 (σ.symm j.1, j.2)) := rfl

lemma permLp_coeFn {N : ℕ} (σ : Equiv.Perm (Fin N)) (u : L2 N) :
    (permLp N σ u : Conf N → ℝ) =ᵐ[volC N] fun x => (u : Conf N → ℝ) (tauPerm N σ x) :=
  Lp.coeFn_compMeasurePreserving u _

lemma norm_permLp {N : ℕ} (σ : Equiv.Perm (Fin N)) (u : L2 N) :
    ‖permLp N σ u‖ = ‖u‖ :=
  Lp.norm_compMeasurePreserving u _

lemma l2Sq_permAmb {N : ℕ} (σ : Equiv.Perm (Fin N)) (p : Amb N) :
    l2Sq (permAmb N σ p) = l2Sq p := by
  simp only [l2Sq, permAmb_fst]
  rw [norm_permLp]

lemma gSq_permAmb {N : ℕ} (σ : Equiv.Perm (Fin N)) (p : Amb N) :
    gSq (permAmb N σ p) = gSq p := by
  simp only [gSq, permAmb_snd]
  have h1 : ∀ j : GIdx N, ‖permLp N σ (p.2 (σ.symm j.1, j.2))‖ ^ 2 = ‖p.2 (σ.symm j.1, j.2)‖ ^ 2 :=
    fun j => by rw [norm_permLp]
  rw [Finset.sum_congr rfl (fun j _ => h1 j)]
  exact Equiv.sum_comp (σ.symm.prodCongr (Equiv.refl (Fin 3))) (fun j => ‖p.2 j‖ ^ 2)

/-- The symmetrisation of a test function (its average over the permutation
group). -/
noncomputable def symTest (N : ℕ) (L : ℝ) (F : testSub N L) : testSub N L :=
  ⟨symAvg N (F : Conf N → ℝ), symAvg_contDiff F.2.1, by
    have hsup : Function.support (symAvg N (F : Conf N → ℝ)) ⊆
        tsupport fun x => ∑ σ : Equiv.Perm (Fin N), (F : Conf N → ℝ) (actPerm N σ x) := by
      intro x hx
      simp only [Function.mem_support] at hx
      refine subset_tsupport _ ?_
      simp only [Function.mem_support]
      intro hsum
      exact hx (by simp only [symAvg, hsum, mul_zero])
    exact (closure_minimal hsup (isClosed_tsupport _)).trans (permSum_tsupport_openBox F.2.2)⟩

/-- An element of the ambient space is permutation invariant if it is fixed by
every permutation of the particles. -/
def IsSym (N : ℕ) (p : Amb N) : Prop := ∀ σ : Equiv.Perm (Fin N), permAmb N σ p = p

/-- The symmetrisation average of an element of the ambient space. -/
noncomputable def symAvgAmb (N : ℕ) (p : Amb N) : Amb N :=
  (Nat.factorial N : ℝ)⁻¹ • ∑ σ : Equiv.Perm (Fin N), permAmb N σ p

end

end Work.BoseSym
