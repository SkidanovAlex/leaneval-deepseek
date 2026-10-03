import Mathlib
import Submission.Work.FIArea4.Vflip.Vfd.NearKernelDefs
import Submission.Work.FIArea4.Vflip.Vfd.near_count_multi_exp
import Submission.Work.FIArea4.Vflip.Vfd.Vvar_near_pointwise
import Submission.Work.FIArea4.Vflip.Vfd.amgm_double_sum
import Submission.Work.FIArea4.A4varbounds

/-!
# The uniform near-diagonal bound for the local variance (FI §12)

This module proves `Vvar_near_bound`: the *near-diagonal* part

`Σ_{p,q ∈ boxF R S} α_p conj(α_q) (1 - nearCut a b (xPair p q)) · pairWeight D p q`

of the bilinear form that appears after the "flipping of moduli" is bounded by
`C · ((RS/H)(log(2RS/(DH)) + 2) + (RS)^{3/2}/(DH)) · p14Ener R S α`, uniformly in the
parameters `D R S H a b` and the coefficient array `α`, where `H = (RS/D)^{1/3}` and
`a = 2S/(HR)`, `b = 2S/R` are the near/far cutoffs of the paper.

The proof has three ingredients:

* `Vvar_near_pointwise`: for each pair `(p,q)` of box points the term is bounded by
  `‖α_p‖‖α_q‖ · nearKernel D R S H p q`, where `nearKernel` is the indicator of the near
  condition `|Δ_{pq}| H ≤ 8RS` times the number of divisors of `Δ_{pq}` in `(D/2, 3D]`
  (the analytic point: `1 - nearCut ≠ 0` forces `|Δ_{pq}| H ≤ 8RS`, and `‖pairWeight‖` is a
  divisor count);
* `amgm_double_sum`: the symmetrisation
  `Σ_{p,q} a_p a_q N_{pq} ≤ Σ_p a_p² (Σ_q N_{pq})` for a symmetric nonnegative kernel `N`;
* `near_count_multi_exp`: Friedlander–Iwaniec (12.7), the uniform bound
  `Σ_q nearKernel D R S H p q ≤ 1000 · ((RS/H)(log(2RS/(DH)) + 2) + (RS)^{3/2}/(DH))`
  for `p` in the box.

Together with `Σ_{p ∈ boxF} ‖α_p‖² ≤ p14Ener R S α` this gives the statement with `C = 1000`.
-/

namespace Work.FIArea4.Vflip.Vfd

open Finset

private lemma nearKernel_sum_eq (D R S : ℕ) (H : ℝ) (p : ℕ × ℕ) :
    ∑ q ∈ Work.FIArea4.Vflip.boxF R S, nearKernel D R S H p q
      = ∑ q ∈ ((Finset.Ioc R (2 * R)) ×ˢ (Finset.Ioc S (2 * S))).filter
          (fun q => (((p.1 : ℤ) * (q.2 : ℤ) - (q.1 : ℤ) * (p.2 : ℤ)).natAbs : ℝ) * H
              ≤ 8 * (R : ℝ) * (S : ℝ)),
        ((((Finset.Ioc (D / 2) (3 * D)).filter
            (fun d => d ∣ ((p.1 : ℤ) * (q.2 : ℤ) - (q.1 : ℤ) * (p.2 : ℤ)).natAbs)).card : ℕ) : ℝ) := by
  simp only [Work.FIArea4.Vflip.boxF, nearKernel, nearDelta]
  rw [Finset.sum_filter]
  rfl

private lemma nearKernel_sum_le {R S D : ℕ} (hR : 1 ≤ R) (hS : 1 ≤ S) (hD : 1 ≤ D)
    (hDsq : R * S < D * D) (H : ℝ) (hH : 1 ≤ H)
    (hHup : H ≤ (R : ℝ) * (S : ℝ) / (D : ℝ))
    (p : ℕ × ℕ) (hp1 : p.1 ∈ Finset.Ioc R (2 * R)) (hp2 : p.2 ∈ Finset.Ioc S (2 * S))
    (hcop : Nat.Coprime p.1 p.2) :
    ∑ q ∈ Work.FIArea4.Vflip.boxF R S, nearKernel D R S H p q
      ≤ 1000 * ((R : ℝ) * (S : ℝ) / H * (Real.log (2 * (R : ℝ) * (S : ℝ) / ((D : ℝ) * H)) + 2)
          + ((R : ℝ) * (S : ℝ)) ^ ((3 : ℝ) / 2) / ((D : ℝ) * H)) := by
  rw [nearKernel_sum_eq]
  exact near_count_multi_exp hR hS hD hDsq H hH hHup p.1 p.2 hp1 hp2 hcop

theorem Vvar_near_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (D R S : ℕ) (H a b : ℝ) (α : ℕ → ℕ → ℂ),
      1 ≤ D → 1 ≤ R → 1 ≤ S → D ≤ R * S → R * S < D * D →
      H = ((R : ℝ) * (S : ℝ) / (D : ℝ)) ^ ((1 : ℝ) / 3) →
      a = 2 * (S : ℝ) / (H * (R : ℝ)) → b = 2 * (S : ℝ) / (R : ℝ) →
      (∀ r s, α r s ≠ 0 → Nat.Coprime r (2 * s)) →
      (∀ r s, α r s ≠ 0 → R < r ∧ r ≤ 2 * R ∧ S < s ∧ s ≤ 2 * S) →
      ‖∑ p ∈ Work.FIArea4.Vflip.boxF R S, ∑ q ∈ Work.FIArea4.Vflip.boxF R S,
          α p.1 p.2 * star (α q.1 q.2) *
            (((1 - Work.FIArea4.Vflip.nearCut a b (Work.FIArea4.Vflip.xPair p q)) : ℝ)
              * Work.FIArea4.Vflip.pairWeight D p q)‖
        ≤ C * (((R : ℝ) * (S : ℝ) / H)
                * (Real.log (2 * (R : ℝ) * (S : ℝ) / ((D : ℝ) * H)) + 2)
              + ((R : ℝ) * (S : ℝ)) ^ ((3 : ℝ) / 2) / ((D : ℝ) * H))
            * Work.FIArea4.p14Ener R S α := by
  refine ⟨1000, by norm_num, ?_⟩
  intro D R S H a b α hD hR hS hDRS hDsq hH ha hb hsupp hbox
  have hDpos : (0:ℝ) < (D:ℝ) := by exact_mod_cast (by omega : 0 < D)
  have hRpos : (0:ℝ) < (R:ℝ) := by exact_mod_cast (by omega : 0 < R)
  have hSpos : (0:ℝ) < (S:ℝ) := by exact_mod_cast (by omega : 0 < S)
  have hX0 : (0:ℝ) ≤ (R:ℝ)*(S:ℝ) := by positivity
  have hXD1 : (1:ℝ) ≤ (R:ℝ)*(S:ℝ)/(D:ℝ) := by
    rw [le_div_iff₀ hDpos]
    have hh : (D:ℝ) ≤ (R:ℝ)*(S:ℝ) := by exact_mod_cast hDRS
    linarith
  have hHpos : (0:ℝ) < H := by
    rw [hH]; exact Real.rpow_pos_of_pos (by positivity) _
  have hH1 : (1:ℝ) ≤ H := by
    rw [hH]
    calc (1:ℝ) = (1:ℝ) ^ ((1:ℝ)/3) := by norm_num
      _ ≤ ((R:ℝ)*(S:ℝ)/(D:ℝ)) ^ ((1:ℝ)/3) :=
          Real.rpow_le_rpow (by norm_num) hXD1 (by norm_num)
  have hHup : H ≤ (R:ℝ)*(S:ℝ)/(D:ℝ) := by
    rw [hH]; exact Real.rpow_le_self_of_one_le hXD1 (by norm_num)
  set Br : ℝ := (R:ℝ)*(S:ℝ)/H * (Real.log (2*(R:ℝ)*(S:ℝ)/((D:ℝ)*H)) + 2)
      + ((R:ℝ)*(S:ℝ))^((3:ℝ)/2)/((D:ℝ)*H) with hBr
  have hDHle : (D:ℝ)*H ≤ (R:ℝ)*(S:ℝ) := by
    have h1 : H * (D:ℝ) ≤ (R:ℝ)*(S:ℝ) := by
      have h2 := mul_le_mul_of_nonneg_right hHup (le_of_lt hDpos)
      rwa [div_mul_cancel₀ _ (ne_of_gt hDpos)] at h2
    linarith
  have hDHpos : (0:ℝ) < (D:ℝ)*H := mul_pos hDpos hHpos
  have hBrnn : 0 ≤ Br := by
    rw [hBr]
    have h2X : (1:ℝ) ≤ 2*(R:ℝ)*(S:ℝ)/((D:ℝ)*H) := by
      rw [le_div_iff₀ hDHpos]; nlinarith [hDHle]
    have hlog : 0 ≤ Real.log (2*(R:ℝ)*(S:ℝ)/((D:ℝ)*H)) := Real.log_nonneg h2X
    have h1 : 0 ≤ (R:ℝ)*(S:ℝ)/H * (Real.log (2*(R:ℝ)*(S:ℝ)/((D:ℝ)*H)) + 2) :=
      mul_nonneg (div_nonneg hX0 (le_of_lt hHpos)) (by linarith)
    have h2 : 0 ≤ ((R:ℝ)*(S:ℝ))^((3:ℝ)/2)/((D:ℝ)*H) :=
      div_nonneg (Real.rpow_nonneg hX0 _) (le_of_lt hDHpos)
    linarith
  have hstep1 : ‖∑ p ∈ Work.FIArea4.Vflip.boxF R S, ∑ q ∈ Work.FIArea4.Vflip.boxF R S,
        α p.1 p.2 * star (α q.1 q.2) *
          (((1 - Work.FIArea4.Vflip.nearCut a b (Work.FIArea4.Vflip.xPair p q)) : ℝ) *
            Work.FIArea4.Vflip.pairWeight D p q)‖
      ≤ ∑ p ∈ Work.FIArea4.Vflip.boxF R S, ∑ q ∈ Work.FIArea4.Vflip.boxF R S,
          ‖α p.1 p.2‖ * ‖α q.1 q.2‖ * nearKernel D R S H p q := by
    refine (norm_sum_le _ _).trans ?_
    refine Finset.sum_le_sum (fun p hp => ?_)
    refine (norm_sum_le _ _).trans ?_
    refine Finset.sum_le_sum (fun q hq => ?_)
    exact Vvar_near_pointwise D R S H a b α p q hD hR hS hDRS hDsq hH ha hb hp hq
  have hstep2 : (∑ p ∈ Work.FIArea4.Vflip.boxF R S, ∑ q ∈ Work.FIArea4.Vflip.boxF R S,
          ‖α p.1 p.2‖ * ‖α q.1 q.2‖ * nearKernel D R S H p q)
      ≤ ∑ p ∈ Work.FIArea4.Vflip.boxF R S,
          ‖α p.1 p.2‖^2 * (∑ q ∈ Work.FIArea4.Vflip.boxF R S, nearKernel D R S H p q) :=
    amgm_double_sum (Work.FIArea4.Vflip.boxF R S) (fun p => ‖α p.1 p.2‖)
      (fun p q => nearKernel D R S H p q)
      (fun p q => nearKernel_symm D R S H p q) (fun p => norm_nonneg _)
      (fun p q => nearKernel_nonneg D R S H p q)
  have hstep3 : (∑ p ∈ Work.FIArea4.Vflip.boxF R S,
          ‖α p.1 p.2‖^2 * (∑ q ∈ Work.FIArea4.Vflip.boxF R S, nearKernel D R S H p q))
      ≤ ∑ p ∈ Work.FIArea4.Vflip.boxF R S, ‖α p.1 p.2‖^2 * (1000 * Br) := by
    refine Finset.sum_le_sum (fun p hp => ?_)
    have hp' : p.1 ∈ Finset.Ioc R (2*R) ∧ p.2 ∈ Finset.Ioc S (2*S) := by
      rw [Work.FIArea4.Vflip.boxF, Finset.mem_product] at hp; exact hp
    by_cases hα : α p.1 p.2 = 0
    · rw [hα]; simp
    · refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
      have hcop : Nat.Coprime p.1 p.2 :=
        Nat.Coprime.coprime_dvd_right (dvd_mul_left p.2 2) (hsupp p.1 p.2 hα)
      rw [hBr]
      exact nearKernel_sum_le hR hS hD hDsq H hH1 hHup p hp'.1 hp'.2 hcop
  have hstep4 : (∑ p ∈ Work.FIArea4.Vflip.boxF R S, ‖α p.1 p.2‖^2 * (1000 * Br))
      = (1000 * Br) * ∑ p ∈ Work.FIArea4.Vflip.boxF R S, ‖α p.1 p.2‖^2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun p _ => by ring)
  have hstep5 : (∑ p ∈ Work.FIArea4.Vflip.boxF R S, ‖α p.1 p.2‖^2)
      ≤ Work.FIArea4.p14Ener R S α := by
    rw [Work.FIArea4.p14Ener]
    have hbox : (∑ p ∈ Work.FIArea4.Vflip.boxF R S, ‖α p.1 p.2‖^2)
        = ∑ p ∈ Finset.Ioc R (2*R) ×ˢ Finset.Ioc S (2*S), ‖α p.1 p.2‖^2 := by
      rw [Work.FIArea4.Vflip.boxF]
    rw [hbox]
    calc ∑ x ∈ Finset.Ioc R (2*R) ×ˢ Finset.Ioc S (2*S), ‖α x.1 x.2‖^2
      _ ≤ ∑ x ∈ Finset.Icc 1 (2*R) ×ˢ Finset.Icc 1 (2*S), ‖α x.1 x.2‖^2 := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
          · intro x hx
            simp only [Finset.mem_product, Finset.mem_Ioc, Finset.mem_Icc] at hx ⊢
            exact ⟨⟨by omega, hx.1.2⟩, ⟨by omega, hx.2.2⟩⟩
          · intro x _ _; exact sq_nonneg _
      _ = ∑ r ∈ Finset.Icc 1 (2*R), ∑ s ∈ Finset.Icc 1 (2*S), ‖α r s‖^2 := by
          rw [Finset.sum_product]
      _ ≤ ∑ r ∈ Finset.Icc 1 (2*R), ∑ s ∈ Finset.Icc 1 (2*S),
            ((r.divisors.card : ℕ):ℝ) * Complex.normSq (α r s) := by
          refine Finset.sum_le_sum (fun r hr => Finset.sum_le_sum (fun s _ => ?_))
          rw [Finset.mem_Icc] at hr
          have hcard : (1:ℝ) ≤ ((r.divisors.card : ℕ):ℝ) := by
            have hr1 : r ≠ 0 := by omega
            have h1 : 1 ∈ r.divisors := by rw [Nat.mem_divisors]; exact ⟨one_dvd r, hr1⟩
            have : 1 ≤ r.divisors.card := Finset.card_pos.mpr ⟨1, h1⟩
            exact_mod_cast this
          rw [Complex.sq_norm]
          nlinarith [Complex.normSq_nonneg (α r s)]
  rw [show (1000:ℝ) * (((R:ℝ)*(S:ℝ)/H) * (Real.log (2*(R:ℝ)*(S:ℝ)/((D:ℝ)*H)) + 2)
        + ((R:ℝ)*(S:ℝ))^((3:ℝ)/2)/((D:ℝ)*H)) * Work.FIArea4.p14Ener R S α
      = 1000 * Br * Work.FIArea4.p14Ener R S α from by rw [hBr]]
  calc ‖∑ p ∈ Work.FIArea4.Vflip.boxF R S, ∑ q ∈ Work.FIArea4.Vflip.boxF R S,
        α p.1 p.2 * star (α q.1 q.2) *
          (((1 - Work.FIArea4.Vflip.nearCut a b (Work.FIArea4.Vflip.xPair p q)) : ℝ) *
            Work.FIArea4.Vflip.pairWeight D p q)‖
      ≤ ∑ p ∈ Work.FIArea4.Vflip.boxF R S, ∑ q ∈ Work.FIArea4.Vflip.boxF R S,
          ‖α p.1 p.2‖ * ‖α q.1 q.2‖ * nearKernel D R S H p q := hstep1
    _ ≤ ∑ p ∈ Work.FIArea4.Vflip.boxF R S,
          ‖α p.1 p.2‖^2 * (∑ q ∈ Work.FIArea4.Vflip.boxF R S, nearKernel D R S H p q) := hstep2
    _ ≤ ∑ p ∈ Work.FIArea4.Vflip.boxF R S, ‖α p.1 p.2‖^2 * (1000 * Br) := hstep3
    _ = (1000 * Br) * ∑ p ∈ Work.FIArea4.Vflip.boxF R S, ‖α p.1 p.2‖^2 := hstep4
    _ ≤ (1000 * Br) * Work.FIArea4.p14Ener R S α :=
        mul_le_mul_of_nonneg_left hstep5 (mul_nonneg (by norm_num) hBrnn)
    _ = 1000 * Br * Work.FIArea4.p14Ener R S α := by ring

end Work.FIArea4.Vflip.Vfd
