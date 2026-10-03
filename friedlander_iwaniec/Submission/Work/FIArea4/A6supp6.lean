/-
# Area 4 (round 6): a self-contained copy of the support bookkeeping of the frozen §15 chain

The round-6 separation step (`Submission/Work/FIArea4/A6psi/psiSum6_le_expLog6`) and the round-6
log-sine step (`.../A6psi/expLog6_le_expSum6`) are, like the frozen `S15psi_relaxed` chain, proved
by cutting the index set `S15ixSet` down to the support of `β` and then running the Fourier–Mellin
separation of variables there.  The frozen module carrying that bookkeeping,
`Submission.Work.FIArea4.S15_psi_cut_reduction`, sits *above* the frozen §15 variance chain
(`S15expSum_bound` and its dependencies), which is currently not built; importing it therefore
costs the round-6 chain a stale dependency that has nothing to do with the round-6 arguments.

This module re-states, verbatim, the five frozen items that the round-6 chain actually uses —
under fresh names, so that it may coexist with the frozen module once that is restored:

* `A6supp` = the frozen `S15supp`: the triples of `S15ixSet` where `2β_{z₁}\barβ_{z₂} ≠ 0`;
* `A6sum_S15ixSet_eq_sum_supp` = the frozen `sum_S15ixSet_eq_sum_supp`: sums over `S15ixSet` may
  be restricted to the support;
* `A6sum_eq_sum_univ` = the frozen `sum_eq_sum_univ`: a `Finset` sum as a sum over the subtype;
* `A6supp_bounds` = the frozen `S15supp_bounds`: on the support, `1/(4N) ≤ |x| ≤ 2N` and `y > 0`
  (with its auxiliary estimates `A6S15x_abs_bounds`, `A6absDelta_le_two_N`, …);
* `A6summable_S15theta` = the frozen `summable_S15theta`: the log-sine series twisted by the
  angular character `S15theta` is summable.

Nothing here is new mathematics: the round-6 arguments use only these *estimates* on the support
(which are symbol-agnostic — they involve `S15x`, `S15y` and the polar box only, never the
coefficient), so reproducing them in a module free of the frozen §15 variance chain removes that
dependency without weakening anything.
-/
import Mathlib
import Submission.Work.FIArea4.S15cutDefs
import Submission.Work.FIArea4.S15prim_defs
import Submission.Work.FIArea4.S15delta
import Submission.Work.FIArea4.S15box
import Submission.Work.FIArea4.VcutMod_le_pair_crude

namespace Work.FIArea4

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

set_option maxHeartbeats 1000000

/-! ## 1. The support of the round-6 coefficient, and the elementary polar-box estimates -/
lemma A6natAbs_cast (m : ℤ) : ((m.natAbs : ℕ) : ℝ) = |(m : ℝ)| := by
  rw [Nat.cast_natAbs, Int.cast_abs]

lemma A6abs_S15x_mul_S15y {X j d : ℕ} {z1 z2 : GaussianInt} (h1 : z1.re ≠ 0) (h2 : z2.re ≠ 0)
    (hX : 0 < X) (hd : 0 < d) :
    |S15x z1 z2| * S15y X j d z1 z2
      = (Work.FIPlan.absDelta z1 z2 : ℝ) / (4 * (X : ℝ) * (2 : ℝ) ^ j * (d : ℝ)) := by
  have hr1 : (z1.re : ℝ) ≠ 0 := by exact_mod_cast h1
  have hr2 : (z2.re : ℝ) ≠ 0 := by exact_mod_cast h2
  have hB : ((z1.re : ℝ) * (z2.re : ℝ)) ≠ 0 := mul_ne_zero hr1 hr2
  have h4 : (0:ℝ) < 4 * (X : ℝ) * (2:ℝ)^j * (d:ℝ) := by
    have hX' : (0:ℝ) < (X:ℝ) := by exact_mod_cast hX
    have hd' : (0:ℝ) < (d:ℝ) := by exact_mod_cast hd
    positivity
  have hnum : S15x z1 z2 = ((z1.im : ℝ) * (z2.re : ℝ) - (z1.re : ℝ) * (z2.im : ℝ))
      / ((z1.re : ℝ) * (z2.re : ℝ)) := by
    rw [S15x, div_sub_div _ _ hr1 hr2]
  have habs : (Work.FIPlan.absDelta z1 z2 : ℝ)
      = |(z1.im : ℝ) * (z2.re : ℝ) - (z1.re : ℝ) * (z2.im : ℝ)| := by
    rw [Work.FIPlan.absDelta, A6natAbs_cast]
    have hD : ((Work.FIPlan.Delta z1 z2 : ℤ) : ℝ)
        = -((z1.im : ℝ) * (z2.re : ℝ) - (z1.re : ℝ) * (z2.im : ℝ)) := by
      rw [Work.FIArea4.Delta_eq]; push_cast; ring
    rw [hD, abs_neg]
  have habsr : ((z1.re * z2.re).natAbs : ℝ) = |(z1.re : ℝ) * (z2.re : ℝ)| := by
    rw [A6natAbs_cast]; push_cast; ring_nf
  simp only [S15y]
  rw [hnum, abs_div, habsr, habs]
  field_simp

lemma A6abs_re_le_sqrt_gnorm (z : GaussianInt) :
    |(z.re : ℝ)| ≤ Real.sqrt ((Work.FIPlan.gnorm z : ℕ) : ℝ) := by
  have h1 : ‖(z : ℂ)‖ = Real.sqrt ((Work.FIPlan.gnorm z : ℕ) : ℝ) := crude_norm_toComplex_eq_sqrt z
  have h2 : |(z.re : ℝ)| ≤ ‖(z : ℂ)‖ := by
    simpa using Complex.abs_re_le_norm (z : ℂ)
  rw [h1] at h2; exact h2

lemma A6abs_re_le_sqrt_two_N (Pa : Work.FITop.Params) {φ : ℝ} {z : GaussianInt}
    (hz : Work.FITop3.InPolarBox Pa φ z) :
    |(z.re : ℝ)| ≤ Real.sqrt (2 * Pa.N) := by
  have hθ1 : Pa.θ ≤ 1 := theta_le_one Pa
  have hg : ((Work.FIPlan.gnorm z : ℕ) : ℝ) ≤ 2 * Pa.N := by
    nlinarith [hz.2.2.1, Pa.hN1]
  exact le_trans (A6abs_re_le_sqrt_gnorm z) (Real.sqrt_le_sqrt hg)

/-- `|Δ| ≤ 2N` for a pair of the polar box. -/
lemma A6absDelta_le_two_N (Pa : Work.FITop.Params) {φ : ℝ} {z1 z2 : GaussianInt}
    (h1 : Work.FITop3.InPolarBox Pa φ z1) (h2 : Work.FITop3.InPolarBox Pa φ z2) :
    ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ) ≤ 2 * Pa.N := by
  have hθ1 : Pa.θ ≤ 1 := theta_le_one Pa
  have hg1 : ((Work.FIPlan.gnorm z1 : ℕ) : ℝ) ≤ 2 * Pa.N := by
    nlinarith [h1.2.2.1, Pa.hN1]
  have hg2 : ((Work.FIPlan.gnorm z2 : ℕ) : ℝ) ≤ 2 * Pa.N := by
    nlinarith [h2.2.2.1, Pa.hN1]
  calc ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ)
      ≤ Real.sqrt (((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ)) := crude_absDelta_le_sqrt_gnorm z1 z2
    _ ≤ 2 * Pa.N := crude_sqrt_gnorm_mul_le Pa.N z1 z2 hg1 hg2

/-- `|r₁r₂| ≤ 2N` for a pair of the polar box. -/
lemma A6abs_re_mul_le_two_N (Pa : Work.FITop.Params) {φ : ℝ} {z1 z2 : GaussianInt}
    (h1 : Work.FITop3.InPolarBox Pa φ z1) (h2 : Work.FITop3.InPolarBox Pa φ z2) :
    |(z1.re : ℝ) * (z2.re : ℝ)| ≤ 2 * Pa.N := by
  have hN1 : (1:ℝ) ≤ Pa.N := by linarith [Pa.hN1]
  have h1' := A6abs_re_le_sqrt_two_N Pa h1
  have h2' := A6abs_re_le_sqrt_two_N Pa h2
  rw [abs_mul]
  calc |(z1.re : ℝ)| * |(z2.re : ℝ)| ≤ Real.sqrt (2*Pa.N) * Real.sqrt (2*Pa.N) :=
        mul_le_mul h1' h2' (abs_nonneg _) (Real.sqrt_nonneg _)
    _ = 2 * Pa.N := by
        rw [← Real.sqrt_mul (by linarith : (0:ℝ) ≤ 2*Pa.N),
          show 2 * Pa.N * (2 * Pa.N) = (2*Pa.N)^2 by ring, Real.sqrt_sq (by linarith)]


/-- The triples of `S15ixSet` on which the coefficient `2 β_{z₁} \barβ_{z₂}` does not vanish. -/
def A6supp (Pa : Work.FITop.Params) (X j : ℕ) (β : GaussianInt → ℂ) : Finset S15Id :=
  (S15ixSet Pa X j).filter (fun i => β i.1.1 ≠ 0 ∧ β i.1.2 ≠ 0)


/-- Sums over `S15ixSet` may be restricted to the support of `β`. -/
lemma A6sum_S15ixSet_eq_sum_supp (Pa : Work.FITop.Params) (X j : ℕ) (β : GaussianInt → ℂ)
    (f : GaussianInt → GaussianInt → ℕ → ℂ)
    (hf : ∀ z1 z2 d, (β z1 = 0 ∨ β z2 = 0) → f z1 z2 d = 0) :
    (∑ i ∈ S15ixSet Pa X j, f i.1.1 i.1.2 i.2)
      = ∑ i ∈ A6supp Pa X j β, f i.1.1 i.1.2 i.2 := by
  refine (Finset.sum_subset (Finset.filter_subset _ _) (fun i hi hni => ?_)).symm
  have hβ : β i.1.1 = 0 ∨ β i.1.2 = 0 := by
    by_contra hcon
    push_neg at hcon
    exact hni (Finset.mem_filter.mpr ⟨hi, hcon.1, hcon.2⟩)
  exact hf _ _ _ hβ


/-- On the polar box the separating variable `x = s₁/r₁ - s₂/r₂` satisfies `1/(2N) ≤ |x| ≤ 2N`. -/
lemma A6S15x_abs_bounds (Pa : Work.FITop.Params) {φ : ℝ} {z1 z2 : GaussianInt}
    (h1 : Work.FITop3.InPolarBox Pa φ z1) (h2 : Work.FITop3.InPolarBox Pa φ z2)
    (hΔ : 0 < Work.FIPlan.absDelta z1 z2) :
    1 / (2 * Pa.N) ≤ |S15x z1 z2| ∧ |S15x z1 z2| ≤ 2 * Pa.N := by
  have hN1 : (1 : ℝ) ≤ Pa.N := Pa.hN1
  have hr1 : z1.re ≠ 0 := fun h => by
    have hodd := h1.1.1
    rw [h] at hodd
    exact absurd hodd (by decide)
  have hr2 : z2.re ≠ 0 := fun h => by
    have hodd := h2.1.1
    rw [h] at hodd
    exact absurd hodd (by decide)
  have hr1' : (z1.re : ℝ) ≠ 0 := by exact_mod_cast hr1
  have hr2' : (z2.re : ℝ) ≠ 0 := by exact_mod_cast hr2
  have hA : ((z1.re * z2.re).natAbs : ℝ) ≠ 0 := by
    rw [A6natAbs_cast]
    push_cast
    exact abs_ne_zero.mpr (mul_ne_zero hr1' hr2')
  have hprod := A6abs_S15x_mul_S15y (X := 1) (j := 0) (d := 1) hr1 hr2
    (by norm_num) (by norm_num)
  simp only [S15y, Nat.cast_one, mul_one] at hprod
  have hx_eq : |S15x z1 z2| = (Work.FIPlan.absDelta z1 z2 : ℝ)
      / ((z1.re * z2.re).natAbs : ℝ) := by
    refine (eq_div_iff hA).mpr ?_
    have h4 : ((z1.re * z2.re).natAbs : ℝ) / 4 * 4 = ((z1.re * z2.re).natAbs : ℝ) := by
      field_simp
    nlinarith [hprod, h4]
  have hAle : ((z1.re * z2.re).natAbs : ℝ) ≤ 2 * Pa.N := by
    have h := A6abs_re_mul_le_two_N Pa h1 h2
    have hcast : ((z1.re * z2.re).natAbs : ℝ) = |(z1.re : ℝ) * (z2.re : ℝ)| := by
      rw [A6natAbs_cast]; push_cast; ring_nf
    rwa [hcast]
  have hAge : (1 : ℝ) ≤ ((z1.re * z2.re).natAbs : ℝ) := by
    have hnat : 1 ≤ (z1.re * z2.re).natAbs := by
      rw [Nat.one_le_iff_ne_zero]
      intro h
      exact mul_ne_zero hr1 hr2 (Int.natAbs_eq_zero.mp h)
    exact_mod_cast hnat
  have hApos : (0 : ℝ) < ((z1.re * z2.re).natAbs : ℝ) := by linarith
  have hΔle : (Work.FIPlan.absDelta z1 z2 : ℝ) ≤ 2 * Pa.N := A6absDelta_le_two_N Pa h1 h2
  have hΔge : (1 : ℝ) ≤ (Work.FIPlan.absDelta z1 z2 : ℝ) := by
    have : 1 ≤ Work.FIPlan.absDelta z1 z2 := hΔ
    exact_mod_cast this
  constructor
  · rw [hx_eq]
    have step1 : 1 / (2 * Pa.N) ≤ 1 / ((z1.re * z2.re).natAbs : ℝ) :=
      one_div_le_one_div_of_le hApos hAle
    have step2 : 1 / ((z1.re * z2.re).natAbs : ℝ)
        ≤ (Work.FIPlan.absDelta z1 z2 : ℝ) / ((z1.re * z2.re).natAbs : ℝ) :=
      div_le_div_of_nonneg_right (by linarith [hΔge]) hApos.le
    linarith
  · rw [hx_eq, div_le_iff₀ hApos]
    nlinarith [hΔle, hAge]

/-- On the support, the two separating variables satisfy `1/(4N) ≤ |x| ≤ 2N` and `y > 0`. -/
lemma A6supp_bounds (Pa : Work.FITop.Params) (X j : ℕ) {φ : ℝ} {β : GaussianInt → ℂ}
    (hβ : IsPrimBoxCoeff Pa φ β) (hX : 1 ≤ X) {i : S15Id} (hi : i ∈ A6supp Pa X j β) :
    1 / (4 * Pa.N) ≤ |S15x i.1.1 i.1.2| ∧ |S15x i.1.1 i.1.2| ≤ 2 * Pa.N ∧
      0 < S15y X j i.2 i.1.1 i.1.2 := by
  rw [A6supp, Finset.mem_filter] at hi
  obtain ⟨hix, hb1, hb2⟩ := hi
  rw [S15ixSet, Finset.mem_filter] at hix
  obtain ⟨hix0, hcond⟩ := hix
  have hd1 : 1 ≤ i.2 := (Finset.mem_Icc.mp (Finset.mem_product.mp hix0).2).1
  have hΔpos : 0 < Work.FIPlan.absDelta i.1.1 i.1.2 := hcond.2.2.2
  have hpo1 := hβ.inPolarBox hb1
  have hpo2 := hβ.inPolarBox hb2
  obtain ⟨hbnd1, hbnd2⟩ := A6S15x_abs_bounds Pa hpo1 hpo2 hΔpos
  have hN1 : (1 : ℝ) ≤ Pa.N := Pa.hN1
  have hr1 : i.1.1.re ≠ 0 := fun h => by
    have hodd := hpo1.1.1
    rw [h] at hodd
    exact absurd hodd (by decide)
  have hr2 : i.1.2.re ≠ 0 := fun h => by
    have hodd := hpo2.1.1
    rw [h] at hodd
    exact absurd hodd (by decide)
  refine ⟨?_, hbnd2, ?_⟩
  · have h4 : (0 : ℝ) < 4 * Pa.N := by linarith
    have h2N : (0 : ℝ) < 2 * Pa.N := by linarith
    rw [div_le_iff₀ h4]
    have h := hbnd1
    rw [div_le_iff₀ h2N] at h
    nlinarith [h, hN1]
  · rw [S15y]
    apply div_pos
    · rw [A6natAbs_cast]
      push_cast
      exact abs_pos.mpr (mul_ne_zero (by exact_mod_cast hr1) (by exact_mod_cast hr2))
    · have hX' : (0 : ℝ) < (X : ℝ) := by exact_mod_cast (by omega : 0 < X)
      have hd1' : (1 : ℝ) ≤ (i.2 : ℝ) := by exact_mod_cast hd1
      positivity


/-- A sum over a `Finset` as a sum over its subtype. -/
lemma A6sum_eq_sum_univ {α M : Type} [AddCommMonoid M] (s : Finset α) (f : α → M) :
    (∑ i ∈ s, f i) = ∑ i : ↥s, f i := by
  rw [Finset.univ_eq_attach, ← Finset.sum_attach]

/-! ## 3. Summability of the log-sine series twisted by the angular character -/

/-- The angular character `S15theta` has modulus one. -/
lemma A6norm_S15theta (ℓ : ℤ) (z1 z2 : GaussianInt) : ‖S15theta ℓ z1 z2‖ = 1 := by
  rw [S15theta, Complex.norm_exp]
  simp

/-- Summability of the log-sine series twisted by the angular character. -/
lemma A6summable_S15theta (c : ℤ → ℂ) (hcnorm : Summable (fun ℓ : ℤ => ‖c ℓ‖))
    (z1 z2 : GaussianInt) : Summable (fun ℓ : ℤ => c ℓ * S15theta ℓ z1 z2) :=
  Summable.of_norm_bounded hcnorm (fun ℓ => by rw [norm_mul, A6norm_S15theta, mul_one])


end

end Work.FIArea4
