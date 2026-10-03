/-
# `Submission.Work.FIArea6.S16ErrTwo.ncMass_le` — the non-coprime mass of §16

The coprimality removal of *FI* (16.4), in the form used by the §16 error analysis: with
`1 ≤ X` and `4X ≤ Pz`, the `φ(d)/d`-weighted non-coprime pair mass is

  `Σ_{d ≤ X} (φ(d)/d)·ncMass d β ≤ C·N²·(1+log(2+N))^14·X/Pz`.

The `Pz⁻¹` saving is the one of (5.8): every non-coprime pair `z₁, z₂` of the support shares a
Gaussian prime `π` with `|π|² > Pz` (`Work.FIArea1.gauss_prime_common_divisor`); writing `z = π w`
and summing over the possible `π` produces the `Pz⁻¹`.

Structure of the proof:

* `ncMass_mono_one` — the mass at the modulus `4d` is at most the mass at `4` (`4d ∣ |Δ| ⟹ 4 ∣ |Δ|`),
  and `Σ_{d ≤ X} φ(d)/d ≤ X`, so the whole sum is at most `X·ncMass Pa 1 β`;
* `ncMass_one_le_pair` — `ncMass Pa 1 β ≤ Σ_{z₁,z₂ ∈ polarSupp} ncPairW z₁ z₂`: drop the modulus
  condition, use `‖βz‖ ≤ τ(|z|²)` (`Work.FIArea4.IsBetaCoeff6_norm_le`) and the fact that `β`
  vanishes off its support (which lies in `polarSupp`);
* `Work.FIArea6.S16ErrTwo.ncPairTau_le_sum` (imported) — that pair sum is dominated by
  `Σ_{π ∈ ncPi} (ncS Pa φ π)²` (union bound over the common primes);
* `ncS_le_box_self` (proved in this file) — for `π ∈ ncPi`,
  `ncS Pa φ π ≤ τ(|π|²)·Σ_{w ∈ gBox (ncRad Pa π)} τ(|w|²)` (factoring out `π`, by reindexing the
  multiples of `π` as `π·w` with `w` in the scaled box);
* `Work.FIArea6.S16ErrTwo.ncMass_arith` (imported) — the arithmetic endgame
  `Σ_{π ∈ ncPi} (τ(|π|²)·Σ_{w ∈ gBox (ncRad Pa π)} τ(|w|²))² ≤ 10^20·N²(1+log(2+N))^14/Pz`.
-/
import Mathlib
import Submission.Work.FIArea6.S16ErrTwo.Defs
import Submission.Work.FIArea6.S16UDefs
import Submission.Work.FIArea6.S16Assembly
import Submission.Work.FIArea7.UniMollify6
import Submission.Work.FIArea6.S16ErrTwo.Decomp
import Submission.Work.FIArea6.S16ErrTwo.diagMass_le
import Submission.Work.FIArea6.S16_masses
import Submission.Work.FIArea6.S16_beta_mass6
import Submission.Work.FIArea6.S16_far_point
import Submission.Work.FIArea6.logFac6_sub_gtrunc_le
import Submission.Work.FIArea4.polarBox_card_le
import Submission.Work.FIArea6.omegaDet_eq_ratioSym
import Submission.Work.FIArea7.card_gBox_filter_dvd_absDelta
import Submission.Work.FIArea6b.sector_tau_sum
import Submission.Work.FIArea6.S16ErrTwo.NcDefs
import Submission.Work.FIArea4.A6Ener3_le
import Submission.Work.FIArea6.S16ErrTwo.ncMass_arith
import Submission.Work.FIArea6.S16ErrTwo.ncPairTau_le_sum
import Submission.Work.FIArea6.ncCount
import Submission.Work.FIArea1.l51_arith_bound

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.FIArea6.S16ErrTwo

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## 1. Elementary properties of `ncMass` -/

/-- The non-coprime mass is non-negative. -/
lemma ncMass_nonneg (Pa : Work.FITop.Params) (d : ℕ) (β : GaussianInt → ℂ) :
    0 ≤ ncMass Pa d β := by
  unfold ncMass
  refine Finset.sum_nonneg (fun z1 _ => Finset.sum_nonneg (fun z2 _ => ?_))
  split_ifs with h
  · positivity
  · exact le_refl 0

/-- **Monotonicity in the modulus**: `4d ∣ |Δ|` implies `4 ∣ |Δ|`, so the mass at the modulus `4d`
is at most the mass at the modulus `4`. -/
lemma ncMass_mono_one (Pa : Work.FITop.Params) (d : ℕ) (β : GaussianInt → ℂ) :
    ncMass Pa d β ≤ ncMass Pa 1 β := by
  unfold ncMass
  refine Finset.sum_le_sum (fun z1 _ => Finset.sum_le_sum (fun z2 _ => ?_))
  by_cases h : ¬ Work.FIPlan.GaussCoprime z1 z2 ∧ 4 * d ∣ Work.FIPlan.absDelta z1 z2
  · rw [if_pos h]
    have hdvd : 4 * 1 ∣ Work.FIPlan.absDelta z1 z2 :=
      dvd_trans (⟨d, by ring⟩ : 4 * 1 ∣ 4 * d) h.2
    rw [if_pos ⟨h.1, hdvd⟩]
  · rw [if_neg h]
    split_ifs <;> positivity

/-! ## 2. The reduction to the polar support -/

/-- The pair term of the reduction: `‖βz₁‖‖βz₂‖` for a non-coprime pair and `0` for a coprime
pair. -/
def ncPairB (β : GaussianInt → ℂ) (z1 z2 : GaussianInt) : ℝ :=
  if Work.FIPlan.GaussCoprime z1 z2 then 0 else ‖β z1‖ * ‖β z2‖

/-- **The reduction to the polar support.**  Dropping the modulus condition, bounding the
coefficients by `τ(|z|²)` (`Work.FIArea4.IsBetaCoeff6_norm_le`) and using that `β` vanishes off its
support — which lies in `polarSupp Pa φ` (`IsBetaCoeff6.support`, `.noSmallPrimes`,
`.squarefree_gnorm`) — the mass at the modulus `4` is at most the `τ`-weighted non-coprime pair sum
over the polar support. -/
lemma ncMass_one_le_pair (Pa : Work.FITop.Params) (φ : ℝ) (z0 : GaussianInt)
    (β : GaussianInt → ℂ) (hβ : Work.FITop4.IsBetaCoeff6 Pa φ z0 β) :
    ncMass Pa 1 β ≤ ∑ z1 ∈ Work.FIArea1.polarSupp Pa φ,
        ∑ z2 ∈ Work.FIArea1.polarSupp Pa φ, ncPairW z1 z2 := by
  classical
  have ha : ncMass Pa 1 β ≤ ∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
      ncPairB β z1 z2 := by
    unfold ncMass ncPairB
    refine Finset.sum_le_sum (fun z1 _ => Finset.sum_le_sum (fun z2 _ => ?_))
    by_cases hc : Work.FIPlan.GaussCoprime z1 z2
    · rw [if_pos hc]
      have hnot : ¬ (¬ Work.FIPlan.GaussCoprime z1 z2
          ∧ 4 * 1 ∣ Work.FIPlan.absDelta z1 z2) := fun h => h.1 hc
      rw [if_neg hnot]
    · rw [if_neg hc]
      split_ifs with h
      · exact le_rfl
      · positivity
  have hb : (∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa, ncPairB β z1 z2)
      = ∑ z1 ∈ (Work.FITop.boxN Pa).filter (fun z => β z ≠ 0),
          ∑ z2 ∈ (Work.FITop.boxN Pa).filter (fun z => β z ≠ 0), ncPairB β z1 z2 := by
    have hinner : ∀ z1 : GaussianInt,
        (∑ z2 ∈ (Work.FITop.boxN Pa).filter (fun z => β z ≠ 0), ncPairB β z1 z2)
          = ∑ z2 ∈ Work.FITop.boxN Pa, ncPairB β z1 z2 := by
      intro z1
      exact Finset.sum_subset (Finset.filter_subset _ _) (fun z2 hz2 hz2not => by
        have hβz2 : β z2 = 0 := by
          by_contra h
          exact hz2not (Finset.mem_filter.mpr ⟨hz2, h⟩)
        simp [ncPairB, hβz2])
    calc (∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa, ncPairB β z1 z2)
        = ∑ z1 ∈ Work.FITop.boxN Pa,
            ∑ z2 ∈ (Work.FITop.boxN Pa).filter (fun z => β z ≠ 0), ncPairB β z1 z2 := by
          refine Finset.sum_congr rfl (fun z1 _ => ?_)
          exact (hinner z1).symm
      _ = ∑ z1 ∈ (Work.FITop.boxN Pa).filter (fun z => β z ≠ 0),
            ∑ z2 ∈ (Work.FITop.boxN Pa).filter (fun z => β z ≠ 0), ncPairB β z1 z2 :=
          (Finset.sum_subset (Finset.filter_subset _ _) (fun z1 hz1 hz1not => by
            have hβz1 : β z1 = 0 := by
              by_contra h
              exact hz1not (Finset.mem_filter.mpr ⟨hz1, h⟩)
            refine Finset.sum_eq_zero (fun z2 _ => ?_)
            simp [ncPairB, hβz1])).symm
  have hc : (∑ z1 ∈ (Work.FITop.boxN Pa).filter (fun z => β z ≠ 0),
        ∑ z2 ∈ (Work.FITop.boxN Pa).filter (fun z => β z ≠ 0), ncPairB β z1 z2)
      ≤ ∑ z1 ∈ (Work.FITop.boxN Pa).filter (fun z => β z ≠ 0),
          ∑ z2 ∈ (Work.FITop.boxN Pa).filter (fun z => β z ≠ 0), ncPairW z1 z2 := by
    refine Finset.sum_le_sum (fun z1 _ => Finset.sum_le_sum (fun z2 _ => ?_))
    by_cases hcop : Work.FIPlan.GaussCoprime z1 z2
    · simp only [ncPairB, ncPairW, if_pos hcop]
      exact le_rfl
    · rw [ncPairB, ncPairW, if_neg hcop, if_neg hcop]
      exact mul_le_mul (Work.FIArea4.IsBetaCoeff6_norm_le Pa φ z0 β hβ z1)
        (Work.FIArea4.IsBetaCoeff6_norm_le Pa φ z0 β hβ z2) (norm_nonneg _) (tauG_nonneg z1)
  have hsub : (Work.FITop.boxN Pa).filter (fun z => β z ≠ 0) ⊆ Work.FIArea1.polarSupp Pa φ := by
    intro z hz
    obtain ⟨hzb, hzβ⟩ := Finset.mem_filter.mp hz
    rw [Work.FIArea1.mem_polarSupp]
    exact ⟨hzb, hβ.support hzβ, hβ.squarefree_gnorm hzβ, hβ.noSmallPrimes hzβ⟩
  have hd : (∑ z1 ∈ (Work.FITop.boxN Pa).filter (fun z => β z ≠ 0),
        ∑ z2 ∈ (Work.FITop.boxN Pa).filter (fun z => β z ≠ 0), ncPairW z1 z2)
      ≤ ∑ z1 ∈ Work.FIArea1.polarSupp Pa φ,
          ∑ z2 ∈ Work.FIArea1.polarSupp Pa φ, ncPairW z1 z2 := by
    refine le_trans (Finset.sum_le_sum (fun z1 _ =>
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun z2 _ _ => ncPairW_nonneg z1 z2))) ?_
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun z1 _ _ => Finset.sum_nonneg (fun z2 _ => ncPairW_nonneg z1 z2))
  exact le_trans ha (le_trans (le_of_eq hb) (le_trans hc hd))

/-! ## 4. Fallback: the factoring-out estimate, proved here as well -/

/-- The factoring-out estimate of the non-coprime mass (an independent proof of the statement also
requested as `Work.FIArea6.S16ErrTwo.ncS_le_box`). -/
lemma ncS_le_box_self (Pa : Work.FITop.Params) (φ : ℝ) (π : GaussianInt)
    (hπ : π ∈ ncPi Pa) :
    ncS Pa φ π ≤ tauG π * (∑ w ∈ Work.FIPlan.gBox (ncRad Pa π), tauG w) := by
  classical
  have hprime := prime_of_mem_ncPi hπ
  have hπne : π ≠ 0 := hprime.ne_zero
  have hπgn : Work.FIPlan.gnorm π ≠ 0 := by
    intro h
    exact hπne (by
      have hnorm : π.norm = 0 := by
        rw [Work.FIPlan.gnorm] at h; exact Int.natAbs_eq_zero.mp h
      exact (Zsqrtd.norm_eq_zero_iff (by norm_num : (-1 : ℤ) < 0) π).mp hnorm)
  have hπgnpos : (0 : ℝ) < ((Work.FIPlan.gnorm π : ℕ) : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero hπgn
  set T : Finset GaussianInt := (Work.FIArea1.polarSupp Pa φ).filter (fun z => π ∣ z) with hT
  let W : GaussianInt → GaussianInt := fun z => if h : π ∣ z then Classical.choose h else 0
  have hW : ∀ z : GaussianInt, π ∣ z → z = π * W z := by
    intro z hz
    simp only [W, dif_pos hz]
    exact Classical.choose_spec hz
  have hinj : ∀ z1 ∈ T, ∀ z2 ∈ T, W z1 = W z2 → z1 = z2 := by
    intro z1 hz1 z2 hz2 h12
    have h1 : π ∣ z1 := (Finset.mem_filter.mp hz1).2
    have h2 : π ∣ z2 := (Finset.mem_filter.mp hz2).2
    rw [hW z1 h1, hW z2 h2, h12]
  have hmem : ∀ z ∈ T, W z ∈ Work.FIPlan.gBox (ncRad Pa π) := by
    intro z hz
    have hzp : z ∈ Work.FIArea1.polarSupp Pa φ := (Finset.mem_filter.mp hz).1
    obtain ⟨-, hpol, -, -⟩ := Work.FIArea1.mem_polarSupp.mp hzp
    have hθ1 : Pa.θ ≤ 1 := Work.FIArea6.ncTheta_le_one Pa
    have hN0 : (0 : ℝ) ≤ Pa.N := by linarith [Pa.hN1]
    have hzN : ((Work.FIPlan.gnorm z : ℕ) : ℝ) ≤ 2 * Pa.N := by
      calc ((Work.FIPlan.gnorm z : ℕ) : ℝ) ≤ (1 + Pa.θ) * Pa.N := hpol.2.2.1
        _ ≤ 2 * Pa.N := by nlinarith
    have hgn : Work.FIPlan.gnorm z
        = Work.FIPlan.gnorm π * Work.FIPlan.gnorm (W z) := by
      conv_lhs => rw [hW z (Finset.mem_filter.mp hz).2]
      rw [Work.FIArea6.ncga_gnorm_mul]
    have hzR : ((Work.FIPlan.gnorm z : ℕ) : ℝ)
        = ((Work.FIPlan.gnorm π : ℕ) : ℝ) * ((Work.FIPlan.gnorm (W z) : ℕ) : ℝ) := by
      rw [hgn]; push_cast; ring
    have h2 : ((Work.FIPlan.gnorm π : ℕ) : ℝ) * ((Work.FIPlan.gnorm (W z) : ℕ) : ℝ)
        ≤ 2 * Pa.N := by rw [← hzR]; exact hzN
    have h3 : ((Work.FIPlan.gnorm (W z) : ℕ) : ℝ)
        ≤ 2 * Pa.N / ((Work.FIPlan.gnorm π : ℕ) : ℝ) := by
      rw [le_div_iff₀ hπgnpos]
      linarith [h2]
    have hr : ((Work.FIPlan.gnorm (W z) : ℕ) : ℝ)
        ≤ 8 * Pa.N / ((Work.FIPlan.gnorm π : ℕ) : ℝ) := by
      refine le_trans h3 (div_le_div_of_nonneg_right ?_ hπgnpos.le)
      linarith [Pa.hN1]
    exact Work.FIArea6.ncMem_gBox_sqrt (r := 8 * Pa.N / ((Work.FIPlan.gnorm π : ℕ) : ℝ)) hr
  have hTsum : ncS Pa φ π = ∑ z ∈ T, tauG z := by
    rw [ncS, hT, Finset.sum_filter]
  have hτ : ∀ w : GaussianInt, tauG (π * w) ≤ tauG π * tauG w := by
    intro w
    have h := Work.FIArea1.card_divisors_mul_le (Work.FIPlan.gnorm π) (Work.FIPlan.gnorm w)
    simp only [tauG, Work.FIArea6.ncga_gnorm_mul]
    exact_mod_cast h
  calc ncS Pa φ π
      = ∑ z ∈ T, tauG z := hTsum
    _ = ∑ z ∈ T, tauG (π * W z) := by
        refine Finset.sum_congr rfl (fun z hz => ?_)
        conv_lhs => rw [hW z (Finset.mem_filter.mp hz).2]
    _ = ∑ w ∈ T.image W, tauG (π * w) :=
        (Finset.sum_image (f := fun w => tauG (π * w)) (g := W) hinj).symm
    _ ≤ ∑ w ∈ Work.FIPlan.gBox (ncRad Pa π), tauG (π * w) :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (fun w hw => by
            obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hw
            exact hmem z hz)
          (fun w _ _ => tauG_nonneg _)
    _ ≤ tauG π * ∑ w ∈ Work.FIPlan.gBox (ncRad Pa π), tauG w := by
        rw [Finset.mul_sum]
        exact Finset.sum_le_sum (fun w _ => hτ w)

/-! ## 3. The target -/

/-- **The non-coprime mass of §16.**  With `1 ≤ X`, `4X ≤ Pz`, the pairs that are *not* coprime
(`¬ GaussCoprime z₁ z₂`, `4d ∣ |Δ|`) satisfy

`Σ_{d ≤ X} (φ(d)/d)·ncMass d β ≤ C·N²·(1+log(2+N))^14·X/Pz`.

*Route.*  On the support `‖βz‖ ≤ τ(gnorm z)` (`abs_gammaTrunc_le` plus `|q|,|p|,|μ| ≤ 1` in
`IsBetaCoeff6`), and `τ(N(gw)) ≤ τ(Ng)τ(Nw)`.

1. *The common divisor.*  If `z₁,z₂ ∈ supp β` are not coprime they share a Gaussian prime `π`, and
`NoSmallPrimes` (a conjunct of `IsBetaCoeff6`) gives `N(π) > Pz` (else the rational prime factor of
`N π` is `≤ Pz` and divides `gnorm z₁`).  Hence for each non-coprime pair there is a Gaussian
divisor `g` (up to units — over-counting is harmless) with `N(g) > Pz`, `g ∣ z₁`, `g ∣ z₂`.
2. *Factoring out `g`.*  Write `z = g w`; then `w` lies in the box of radius `≤ radN/|g|` and
`Σ_{z: g∣z, βz≠0} ‖βz‖ ≤ τ(Ng)·Σ_{|w| ≤ 2√N/|g|} τ(Nw) ≤ τ(Ng)·C·(N/N(g))·(1+log(2+N))²`
(the τ-sum over a disc: `Σ_{|w|≤R}τ(gnorm w) = Σ_{n≤R²} r₂(n)τ(n) ≪ R²(1+log R)²`).
3. *Summing over `g`.*  Dropping the `4d ∣ |Δ|` condition and using `Σ_{d≤X}φ(d)/d ≤ X`,
`Σ_{d≤X}(φ(d)/d)ncMass(d) ≤ X·Σ_{g: N(g)>Pz} (Σ_{z: g∣z}‖βz‖)²
  ≤ C²·X·N²(1+log(2+N))⁴·Σ_{N(g)>Pz} τ(N(g))²/N(g)²`,
and the last sum is a tail of `Σ_g r₂(N g)τ(N g)²/N(g)²`, whose partial sums are
`≪ Y(1+log Y)^4` (the Dirichlet series is `4ζ⁵L`, so `Σ_{n≤Y}r₂(n)τ(n)² ≪ Y(1+log Y)^4`; see
`Work.FIArea3.tau_sq_rho_div_sq_sum_le`, `rho_density_sum_sharp`, `dsum_bounds`), giving
`Σ_{N(g)>Pz}τ(N(g))²/N(g)² ≪ (1+log(2+N))^4/Pz`. -/
theorem ncMass_le :
    ∃ C : ℝ, 0 < C ∧
    ∀ (Pa : Work.FITop.Params) (X : ℕ) (φ : ℝ) (z0 : GaussianInt) (β : GaussianInt → ℂ),
      Work.FITop4.IsBetaCoeff6 Pa φ z0 β → 1 ≤ X → 4 * X ≤ Pa.Pz →
      (∑ d ∈ Finset.Icc 1 X, ((Nat.totient d : ℝ) / (d : ℝ)) * ncMass Pa d β)
        ≤ C * Pa.N ^ (2 : ℕ) * (1 + Real.log (2 + Pa.N)) ^ (14 : ℕ) * (X : ℝ)
            / (Pa.Pz : ℝ) := by
  refine ⟨10 ^ 20, by norm_num, ?_⟩
  intro Pa X φ z0 β hβ hX hP
  have hsum_le : (∑ d ∈ Finset.Icc 1 X, ((Nat.totient d : ℝ) / (d : ℝ)) * ncMass Pa d β)
      ≤ (X : ℝ) * ncMass Pa 1 β := by
    have hpt : ∀ d ∈ Finset.Icc 1 X, ((Nat.totient d : ℝ) / (d : ℝ)) * ncMass Pa d β
        ≤ (1 : ℝ) * ncMass Pa 1 β := by
      intro d hd
      have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
      have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd1
      have hφ : (Nat.totient d : ℝ) / (d : ℝ) ≤ 1 := by
        rw [div_le_iff₀ hd0, one_mul]
        exact_mod_cast Nat.totient_le d
      exact mul_le_mul hφ (ncMass_mono_one Pa d β) (ncMass_nonneg Pa d β) (by norm_num)
    calc (∑ d ∈ Finset.Icc 1 X, ((Nat.totient d : ℝ) / (d : ℝ)) * ncMass Pa d β)
        ≤ ∑ d ∈ Finset.Icc 1 X, (1 : ℝ) * ncMass Pa 1 β := Finset.sum_le_sum hpt
      _ = (X : ℝ) * ncMass Pa 1 β := by
          rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
          simp
  have hp := ncMass_one_le_pair Pa φ z0 β hβ
  have hA : (∑ z1 ∈ Work.FIArea1.polarSupp Pa φ,
        ∑ z2 ∈ Work.FIArea1.polarSupp Pa φ, ncPairW z1 z2)
      ≤ ∑ π ∈ ncPi Pa, (ncS Pa φ π) ^ 2 := ncPairTau_le_sum Pa φ
  have hB : (∑ π ∈ ncPi Pa, (ncS Pa φ π) ^ 2)
      ≤ ∑ π ∈ ncPi Pa,
          (tauG π * (∑ w ∈ Work.FIPlan.gBox (ncRad Pa π), tauG w)) ^ 2 := by
    refine Finset.sum_le_sum (fun π hπ => ?_)
    exact pow_le_pow_left₀ (ncS_nonneg Pa φ π) (ncS_le_box_self Pa φ π hπ) 2
  have hC := ncMass_arith Pa
  calc (∑ d ∈ Finset.Icc 1 X, ((Nat.totient d : ℝ) / (d : ℝ)) * ncMass Pa d β)
      ≤ (X : ℝ) * ncMass Pa 1 β := hsum_le
    _ ≤ (X : ℝ) * (∑ z1 ∈ Work.FIArea1.polarSupp Pa φ,
          ∑ z2 ∈ Work.FIArea1.polarSupp Pa φ, ncPairW z1 z2) :=
        mul_le_mul_of_nonneg_left hp (by positivity)
    _ ≤ (X : ℝ) * (∑ π ∈ ncPi Pa, (ncS Pa φ π) ^ 2) := mul_le_mul_of_nonneg_left hA (by positivity)
    _ ≤ (X : ℝ) * (∑ π ∈ ncPi Pa,
          (tauG π * (∑ w ∈ Work.FIPlan.gBox (ncRad Pa π), tauG w)) ^ 2) :=
        mul_le_mul_of_nonneg_left hB (by positivity)
    _ ≤ (X : ℝ) * (10 ^ 20 * Pa.N ^ (2 : ℕ) * (1 + Real.log (2 + Pa.N)) ^ (14 : ℕ)
          / (Pa.Pz : ℝ)) := mul_le_mul_of_nonneg_left hC (by positivity)
    _ = 10 ^ 20 * Pa.N ^ (2 : ℕ) * (1 + Real.log (2 + Pa.N)) ^ (14 : ℕ) * (X : ℝ)
          / (Pa.Pz : ℝ) := by ring


end

end Work.FIArea6.S16ErrTwo
