import Mathlib
import Submission.Work.FIArea4.Vflip.Vfd.FarSepDefs
import Submission.Work.FIArea4.Vflip.Vfd.FarExpSum_le_crude

/-!
# The uniform crude bound for the far exponential sum of a `(m,c,Q)`-piece

`FarExpSum_le_crude` bounds, for each *fixed* triple `D R S` with `1 ≤ D`, `1 ≤ R`, `1 ≤ S`, the far
exponential sum `farExpSum D R S a b α m c 0 1 u t` of a `(m,c,Q)`-piece with flipped modulus `q' = 1`
by `(4·Rred c R·S/m + 2·min (Rred c R) S) · p14L2 (Rred c R) S (redA c α)`, with a constant that a
priori depends on `D R S`.

Downstream (in the assembly of the far part, `Vflip_far_bound_of_sep`) the constant is needed
*before* `D R S` are introduced, so this module restates the bound with the existential constant in
front.  The proof is the same computation as in `FarExpSum_le_crude`, whose constant is literally
`1`; hence the uniform constant is `1`.
-/

namespace Work.FIArea4.Vflip.Vfd

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- **The crude bound for the far exponential sum, uniform in `D`, `R`, `S`** (constant `1`):
away from the sharp large-sieve input, the far exponential sum of modulus `m` and reduced box
`Rred c R × S` is bounded by `(4·Rred·S/m + 2·min(Rred,S))` times the energy `p14L2` of the reduced
coefficient array. -/
theorem FarExpSum_le_crude_unif :
    ∃ C : ℝ, 0 < C ∧
      ∀ (D R S : ℕ), 1 ≤ D → 1 ≤ R → 1 ≤ S →
      ∀ (a b : ℝ) (α : ℕ → ℕ → ℂ) (m c : ℕ) (u t : ℝ),
        1 ≤ c → 1 ≤ m →
        (∀ r s, α r s ≠ 0 → Nat.Coprime r (2 * s)) →
        (∀ r s, α r s ≠ 0 → R < r ∧ r ≤ 2 * R ∧ S < s ∧ s ≤ 2 * S) →
        ‖Work.FIArea4.Vflip.Vfd.farExpSum D R S a b α m c 0 1 u t‖
          ≤ C * (4 * ((Work.FIArea4.Vflip.Vfd.Rred c R : ℝ)) * S / m
                  + 2 * min ((Work.FIArea4.Vflip.Vfd.Rred c R : ℝ)) S)
              * Work.FIArea4.p14L2 (Work.FIArea4.Vflip.Vfd.Rred c R) S
                  (Work.FIArea4.Vflip.Vfd.redA c α) := by
  refine ⟨1, one_pos, ?_⟩
  intro D R S hD hR hS a b α m c u t hc hm hsupp hbox
  -- coprimality of a reduced point follows from the support hypothesis
  have hcopf : ∀ p ∈ farRedBox (Rred c R) S,
      Complex.normSq (α (c * p.1) p.2) ≠ 0 → Nat.Coprime p.1 p.2 := by
    intro p hp h0
    exact coprime_reduced_of_support hsupp p (fun hz => h0 (by rw [hz, Complex.normSq_zero]))
  -- Step A: take absolute values inside the sum.
  have hnorm : ‖farExpSum D R S a b α m c 0 1 u t‖
      ≤ ∑ i ∈ farSet D R S a b m c 0 1,
          ‖α (c * i.1.2.1) i.1.2.2‖ * ‖α (c * i.2.1) i.2.2‖ := by
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum (fun i _ => ?_))
    calc ‖farCoef m c α i * Complex.exp (2 * Real.pi * Complex.I * (u * xOrig c i)) *
          ((ySep c D i : ℝ) : ℂ) ^ (Complex.I * (t : ℂ))‖
        = ‖farCoef m c α i‖ * ‖Complex.exp (2 * Real.pi * Complex.I * (u * xOrig c i))‖ *
            ‖((ySep c D i : ℝ) : ℂ) ^ (Complex.I * (t : ℂ))‖ := by rw [norm_mul, norm_mul]
      _ = ‖farCoef m c α i‖ * 1 * ‖((ySep c D i : ℝ) : ℂ) ^ (Complex.I * (t : ℂ))‖ := by
            rw [norm_exp_two_pi_I_mul_prod]
      _ ≤ ‖farCoef m c α i‖ * 1 * 1 := by
            gcongr
            exact norm_cpow_I_mul_le_one (ySep_nonneg c D i) t
      _ = ‖farCoef m c α i‖ := by ring
      _ ≤ ‖α (c * i.1.2.1) i.1.2.2‖ * ‖α (c * i.2.1) i.2.2‖ := norm_farCoef_le m c α i
  -- Step B: the image of `farSet` under the projection lands in the reduced box and preserves
  -- the congruence.
  have hproj : ∀ x ∈ (farSet D R S a b m c 0 1).image (fun i : FarIx => (i.1.2, i.2)),
      x ∈ (farRedBox (Rred c R) S ×ˢ farRedBox (Rred c R) S).filter
        (fun x : (ℕ × ℕ) × (ℕ × ℕ) => farPairCongr m x.1 x.2) := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨i, hi, rfl⟩
    obtain ⟨hq0, hq1le, _, _, _, _, _, hfc⟩ := mem_farSet.mp hi
    obtain ⟨hcpos, hcopr, ha1, ha2, hb1, hb2, hsa1, hsa2, hsb1, hsb2, hmdvd, hmq⟩ := hfc
    have hq1 : i.1.1 = 1 := by omega
    -- bounds on the reduced coordinates
    have hρ1ge : 1 ≤ i.1.2.1 := by
      have hpos : 0 < i.1.2.1 := Nat.pos_of_mul_pos_left
        (lt_of_lt_of_le (by omega : 0 < R) (le_of_lt ha1))
      omega
    have hρ1le : i.1.2.1 ≤ 2 * Rred c R := by
      have h : i.1.2.1 ≤ Rred c R := by
        rw [Rred]
        exact (Nat.le_div_iff_mul_le hcpos).mpr (by simpa [Nat.mul_comm] using ha2)
      omega
    have hρ2ge : 1 ≤ i.2.1 := by
      have hpos : 0 < i.2.1 := Nat.pos_of_mul_pos_left
        (lt_of_lt_of_le (by omega : 0 < R) (le_of_lt hb1))
      omega
    have hρ2le : i.2.1 ≤ 2 * Rred c R := by
      have h : i.2.1 ≤ Rred c R := by
        rw [Rred]
        exact (Nat.le_div_iff_mul_le hcpos).mpr (by simpa [Nat.mul_comm] using hb2)
      omega
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · refine Finset.mem_product.mpr ⟨?_, ?_⟩
      · exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨hρ1ge, hρ1le⟩,
          Finset.mem_Icc.mpr ⟨le_trans hS (le_of_lt hsa1), hsa2⟩⟩
      · exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨hρ2ge, hρ2le⟩,
          Finset.mem_Icc.mpr ⟨le_trans hS (le_of_lt hsb1), hsb2⟩⟩
    · -- the congruence
      have hdvd : m ∣ iAbs c i := by rwa [hq1, mul_one] at hmq
      rw [iAbs_eq_natAbs hcpos hcopr] at hdvd
      have h2 : (m : ℤ) ∣ (((i.1.2.1 : ℤ) * (i.2.2 : ℤ) - (i.2.1 : ℤ) * (i.1.2.2 : ℤ)).natAbs : ℤ) := by
        exact_mod_cast hdvd
      exact (Int.dvd_natAbs.mp h2)
  -- Step C: injectivity of the projection on `farSet`.
  have hinj : Set.InjOn (fun i : FarIx => (i.1.2, i.2)) ↑(farSet D R S a b m c 0 1) := by
    intro i hi j hj heq
    have hi1 : i.1.1 = 1 := by
      obtain ⟨hq0, hq1le, _, _, _, _, _, _⟩ := mem_farSet.mp hi; omega
    have hj1 : j.1.1 = 1 := by
      obtain ⟨hq0, hq1le, _, _, _, _, _, _⟩ := mem_farSet.mp hj; omega
    have hfst : i.1.2 = j.1.2 := congrArg (fun p : (ℕ × ℕ) × (ℕ × ℕ) => p.1) heq
    have hsnd : i.2 = j.2 := congrArg (fun p : (ℕ × ℕ) × (ℕ × ℕ) => p.2) heq
    refine Prod.ext ?_ hsnd
    exact Prod.ext (by rw [hi1, hj1]) hfst
  have hsumcmp : (∑ i ∈ farSet D R S a b m c 0 1,
          ‖α (c * i.1.2.1) i.1.2.2‖ * ‖α (c * i.2.1) i.2.2‖)
      ≤ ∑ x ∈ (farRedBox (Rred c R) S ×ˢ farRedBox (Rred c R) S).filter
          (fun x : (ℕ × ℕ) × (ℕ × ℕ) => farPairCongr m x.1 x.2),
          ‖α (c * x.1.1) x.1.2‖ * ‖α (c * x.2.1) x.2.2‖ := by
    calc ∑ i ∈ farSet D R S a b m c 0 1,
            ‖α (c * i.1.2.1) i.1.2.2‖ * ‖α (c * i.2.1) i.2.2‖
        = ∑ x ∈ (farSet D R S a b m c 0 1).image (fun i : FarIx => (i.1.2, i.2)),
            ‖α (c * x.1.1) x.1.2‖ * ‖α (c * x.2.1) x.2.2‖ := by
          rw [Finset.sum_image hinj]
      _ ≤ ∑ x ∈ (farRedBox (Rred c R) S ×ˢ farRedBox (Rred c R) S).filter
            (fun x : (ℕ × ℕ) × (ℕ × ℕ) => farPairCongr m x.1 x.2),
            ‖α (c * x.1.1) x.1.2‖ * ‖α (c * x.2.1) x.2.2‖ :=
          Finset.sum_le_sum_of_subset_of_nonneg hproj (fun x _ _ => by positivity)
  -- Step D: the counting-to-energy lemma.
  have hbound := far_reduced_sum_bound (Rred c R) S m c hm α
    (fun a' b' hab => card_congr_crude (Rred c R) S m a' b' hm hab) hcopf
  rw [one_mul]
  exact le_trans (le_trans hnorm hsumcmp) hbound

end

end Work.FIArea4.Vflip.Vfd
