/-
# The Möbius/Ramanujan (sieve) decomposition of the Ionescu--Wainger comb

This module fixes the vocabulary of the **sieve decomposition** of the Ionescu--Wainger arithmetic
character

  `arithChar ρ l y = Σ_{q ∈ iwP ρ l} c_q y = Σ_{d ∣ y} d · sieveCoeff ρ l d`

(`c_q` = the Ramanujan sum, `sieveCoeff ρ l d = Σ_{q ∈ iwP ρ l, d ∣ q} μ (q/d)`), i.e. of the
decomposition of the low-pass IW walk `m ↦ lpf ρ l₁ m₀ m` into a finite linear combination of
**decimated pure dilation families**

  `lpf ρ l₁ m₀ m f x = Σ_{d ∈ iwDivs ρ l₁} (d · sieveCoeff ρ l₁ d) ·
      decimDilFam m₀ kmtPhiSch d f m x`.

The interest of this form is that every summand is a *pure dilation family* whose kernel is
supported on the sublattice `dℤ`, hence has total mass equal to `1/d` times the mass of the bump;
the variational norm of each summand is therefore `≤ (C/d)‖f‖` by the arithmetic-free lacunary
dilation estimate (`DilVarRealScale`, the real-scale form of `A7Hi.DilVarClean` / JSW), and the
triangle inequality for the variation gives

  `‖Vʳ(lpf walk f)‖_{ℓᵖ} ≤ C · (Σ_{d} |sieveCoeff ρ l₁ d|) · ‖f‖_{ℓᵖ}`.

The resulting constant `Σ_d |sieveCoeff ρ l₁ d|` is *strictly smaller* than the `1 + #A_l` of
`A7Hi.eLpNorm_chainPart_le_uniform`: in the "deep" regime `l₁ > iwC0 ρ` the coefficient vanishes
unless the whole `N₀`-smooth part of `d` equals `Q₀ = iwQ0 ρ l₁`, and then
`sieveCoeff ρ l₁ (Q₀ d₁) = ± C(m - 1 - k, D - k)`, so that
`Σ_d |sieveCoeff ρ l₁ d| ≍ 2^D m^D / D!` with `m = #(iwPrimeRange ρ l₁)`, whereas
`#A_l = Q₀ · Σ_{w ∈ iwW} φ w ≍ Q₀ · C(m,D) · p^{D²}`.  Both are exponential in `l₁`; the target
`(1 + l₁)²` therefore *cannot* be reached by any accounting of the kernel - it needs the
operator-level super-orthogonality of the Ionescu--Wainger multiplier theorem.
-/
import Mathlib
import Submission.Work.KMTAreas.A7Hi.lpfChainPartDefs

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.A7Hi2

open MeasureTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

/-- The finite set of "sieve divisors": every `d` that divides some element of `iwP ρ l`. -/
noncomputable def iwDivs (ρ : ℝ) (l : ℕ) : Finset ℕ :=
  (∏ q ∈ Work.Analysis.IonescuWainger.iwP ρ l, q).divisors

/-- **The sieve (Möbius) coefficient** of the IW arithmetic character at the divisor `d`:
`Σ_{q ∈ iwP ρ l, d ∣ q} μ (q / d)`. -/
noncomputable def sieveCoeff (ρ : ℝ) (l : ℕ) (d : ℕ) : ℤ :=
  ∑ q ∈ (Work.Analysis.IonescuWainger.iwP ρ l).filter (fun q => d ∣ q),
    ArithmeticFunction.moebius (q / d)

/-- **The decimated dilation family**: the `m`-th member is the convolution with the bump
`j ↦ (1/σ_m)·K(d j/σ_m)` of scale `σ_m = 2^{m₀+m}` restricted to the sublattice `dℤ`. -/
noncomputable def decimDilFam (m₀ : ℕ) (K : SchwartzMap ℝ ℂ) (d : ℕ) (f : ℤ → ℂ) (m : ℕ)
    (x : ℤ) : ℂ :=
  ∑' j : ℤ, (1 / (Work.KMTAreas.A7Hi.lpfScale m₀ m : ℝ))
    * K (((d : ℤ) * j : ℝ) / (Work.KMTAreas.A7Hi.lpfScale m₀ m : ℝ))
    * f (x - (d : ℤ) * j)

/-- The total (absolute) mass of the sieve coefficients. -/
noncomputable def sieveMass (ρ : ℝ) (l : ℕ) : ℝ :=
  ∑ d ∈ iwDivs ρ l, |(sieveCoeff ρ l d : ℝ)|

/-- **The real-scale lacunary dilation variational estimate** (the real-scale form of the proved
`Work.KMTAreas.A7Hi.DilVarClean`, i.e. of JSW Theorem 1.1): for `1 < p`, `2 < r` and a Schwartz
kernel `K` there is `C > 0` with, for *every* real lacunary sequence `σ` (`1 ≤ σ n`,
`2 σ n ≤ σ (n+1)`),

  `‖ Vʳ (n ↦ Σ'_j (1/σ n) K (j/σ n) · f (x - j)) ‖_{ℓᵖ(ℤ)} ≤ C ‖f‖_{ℓᵖ(ℤ)}`,

the constant depending only on `p, r, K`. -/
def DilVarRealScale : Prop :=
  ∀ (p : ℝ) (hp : 1 < p) (r : NNReal) (hr : 2 < r) (K : SchwartzMap ℝ ℂ),
    ∃ C : ℝ, 0 < C ∧ ∀ (σ : ℕ → ℝ) (hσ1 : ∀ n : ℕ, 1 ≤ σ n)
      (hσ2 : ∀ n : ℕ, 2 * σ n ≤ σ (n + 1)) (f : ℤ → ℂ),
      MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => ∑' j : ℤ, (1 / σ n) * K ((j : ℝ) / (σ n)) * f (x - j)))
        (ENNReal.ofReal p) MeasureTheory.Measure.count
        ≤ ENNReal.ofReal C * MeasureTheory.eLpNorm f (ENNReal.ofReal p)
            MeasureTheory.Measure.count

/-! ## The coset decomposition of a sum over `ℤ`

The `ℓᵖ`-norm of the decimated dilation family splits over the residue classes modulo `d`; the
following elementary decomposition of a `ℝ≥0∞`-valued sum over `ℤ` is the bookkeeping step. -/

/-- The map `(r, s) ↦ d * s + r` is a bijection from `Fin d × ℤ` to `ℤ` for `d ≥ 1`. -/
theorem bijective_cosetMap (d : ℕ) (hd : 1 ≤ d) :
    Function.Bijective (fun p : Fin d × ℤ => (d : ℤ) * p.2 + (p.1 : ℤ)) := by
  have hdZ : (0 : ℤ) < (d : ℤ) := by exact_mod_cast hd
  have hdne : (d : ℤ) ≠ 0 := ne_of_gt hdZ
  constructor
  · rintro ⟨rp, sp⟩ ⟨rq, sq⟩ hpq
    simp only at hpq
    have hp1 : (0 : ℤ) ≤ (rp : ℤ) := Int.natCast_nonneg _
    have hp2 : (rp : ℤ) < (d : ℤ) := by exact_mod_cast rp.isLt
    have hq1 : (0 : ℤ) ≤ (rq : ℤ) := Int.natCast_nonneg _
    have hq2 : (rq : ℤ) < (d : ℤ) := by exact_mod_cast rq.isLt
    have hkey : (d : ℤ) * (sp - sq) = (rq : ℤ) - (rp : ℤ) := by linarith
    have habs : (d : ℤ) * |sp - sq| = |(rq : ℤ) - (rp : ℤ)| := by
      rw [← hkey, abs_mul, abs_of_nonneg (show (0 : ℤ) ≤ (d : ℤ) by omega)]
    have hlt : |(rq : ℤ) - (rp : ℤ)| < (d : ℤ) := by
      rw [abs_lt]; constructor <;> linarith
    have hzero : |sp - sq| = 0 := by
      have hlt' : (d : ℤ) * |sp - sq| < (d : ℤ) := by rw [habs]; exact hlt
      nlinarith [abs_nonneg (sp - sq)]
    have hsp : sp = sq := sub_eq_zero.mp (abs_eq_zero.mp hzero)
    have hrp : rp = rq := by
      have h : (rp : ℤ) = (rq : ℤ) := by
        have h' := hkey
        rw [hsp, sub_self, mul_zero] at h'
        linarith
      exact Fin.ext (by exact_mod_cast h)
    simp [hsp, hrp]
  · intro x
    have h0 : 0 ≤ x % (d : ℤ) := Int.emod_nonneg x hdne
    have h1 : x % (d : ℤ) < (d : ℤ) := Int.emod_lt_of_pos x hdZ
    refine ⟨(⟨(x % (d : ℤ)).toNat, by omega⟩, x / (d : ℤ)), ?_⟩
    have h2 : ((x % (d : ℤ)).toNat : ℤ) = x % (d : ℤ) := Int.toNat_of_nonneg h0
    show (d : ℤ) * (x / (d : ℤ)) + ((x % (d : ℤ)).toNat : ℤ) = x
    rw [h2]
    have h3 := Int.emod_add_mul_ediv x (d : ℤ)
    linarith

/-- **The coset decomposition of a sum over `ℤ`.** -/
theorem tsum_coset_decomp (d : ℕ) (hd : 1 ≤ d) (F : ℤ → ℝ≥0∞) :
    (∑' x : ℤ, F x) = ∑ r ∈ Finset.range d, ∑' s : ℤ, F (((d : ℤ) * s) + (r : ℤ)) := by
  classical
  let e : Fin d × ℤ ≃ ℤ := Equiv.ofBijective _ (bijective_cosetMap d hd)
  have he : ∀ p : Fin d × ℤ, e p = (d : ℤ) * p.2 + (p.1 : ℤ) := fun p => rfl
  have step1 : (∑' x : ℤ, F x)
      = ∑' p : Fin d × ℤ, F ((d : ℤ) * p.2 + (p.1 : ℤ)) := by
    rw [← Equiv.tsum_eq e F]
    exact tsum_congr fun p => by rw [he]
  rw [step1, ENNReal.tsum_prod', tsum_fintype]
  exact Fin.sum_univ_eq_sum_range (fun r => ∑' s : ℤ, F ((d : ℤ) * s + (r : ℤ))) d

end

end Work.A7Hi2
