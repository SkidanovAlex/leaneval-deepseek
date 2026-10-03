/-
# The integration-by-parts identity `MdlBumpIntegIdent` (area A6, §6)

Krause--Mirek--Tao's Lemma `integ-ident`, applied to the *product* of the two modulated bumps
`φ_{N,t,k₁}(ξ₁) · φ̃_{N,t,k₂}(ξ₂)` and written in terms of the *modified* bumps
`φ_{N,t,k₁,j}`, `φ̃_{N,t,k₂,j}` of (pntj)/(tpntj), with `j = -1` on the `φ̃`-side and `j = 1`
on the `φ`-side.  Precisely, with `d = P.natDegree`, the identity asserted here is

```
∫_{1/2}^1 φ_{N,t,k₁}(ξ₁) φ̃_{N,t,k₂}(ξ₂) dt
  = 2^{-dk₂}(2πi)^{-1} [ φ_{N,t,k₁}(ξ₁) φ̃_{N,t,k₂,-1}(ξ₂) N^{d-1}/P'(Nt) ]_{t=1/2}^{t=1}
    - 2^{k₁-dk₂} ∫_{1/2}^1 φ_{N,t,k₁,1}(ξ₁) φ̃_{N,t,k₂,-1}(ξ₂) N^{d-1}/P'(Nt) dt
    + 2^{-dk₂}(2πi)^{-1} ∫_{1/2}^1 φ_{N,t,k₁}(ξ₁) φ̃_{N,t,k₂,-1}(ξ₂) N^d P''(Nt)/P'(Nt)² dt,
```

which is exactly the paper's second integration-by-parts identity

```
∫_{1/2}^1 Φ dt = [Φ/(2πi ξ₂ N P'(Nt))]_{1/2}^1 - (ξ₁/ξ₂) ∫ Φ/P' dt
                  + (1/(2πiξ₂)) ∫ Φ P''/P'² dt
```

(`Φ(t) = e(ξ₁Nt + ξ₂P(Nt))`, `e(x) = exp(2πix)`, and `P'`, `P''` evaluated at `Nt`), multiplied
by the `t`-independent factor `φ_N^{k₁}(ξ₁) φ̃_N^{k₂}(ξ₂)` and with the singular factors `1/ξ`
absorbed into the modified bumps:

* `φ_{N,t,k₁,1}(ξ) = (2^{-k₁}Nξ) φ_{N,t,k₁}(ξ)` cancels the `1/ξ₂` produced by the `ξ₁/ξ₂` term
  (together with the `N^{d-1}` of the weight `W₁`);
* `φ̃_{N,t,k₂,-1}(ξ) = (2^{-dk₂}N^dξ)^{-1} φ̃_{N,t,k₂}(ξ)` cancels the `1/ξ₂` produced by the
  endpoint term and by the `1/(2πiξ₂)` of the last term (together with the `N^d` of `W₂`).

The three `t`-dependent weights are `mdlW1 P N t = N^{d-1}/P'(Nt)` and
`mdlW2 P N t = N^d P''(Nt)/P'(Nt)²` (`MdlDefs.lean`); `mdlScale P k₂ = 2^{-dk₂}`,
`mdlScaleFe P k₁ k₂ = 2^{k₁-dk₂}`, `mdlIota = (2πi)^{-1}`.

## Shape of the proof

The identity is the previously proved `integIdent_ii_corrected` (`integIdent_ii_core.lean`)
multiplied by the constant `φ_N^{k₁}(ξ₁) φ̃_N^{k₂}(ξ₂)`:

1. `∫_{1/2}^1 φ_{N,t,k₁}(ξ₁) φ̃_{N,t,k₂}(ξ₂) dt = φ_N^{k₁}(ξ₁) φ̃_N^{k₂}(ξ₂) ∫_{1/2}^1 Φ dt`,
   because the two modulations multiply to `e(ξ₁Nt + ξ₂P(Nt))` (`ee` is a character), and the
   `t`-independent factors are constant;
2. apply `integIdent_ii_corrected` to `∫ Φ dt`;
3. identify each of the three resulting terms with the corresponding term of the statement —
   the endpoint terms are `mdlW1_integrand_eq` at `t = 1` and `t = 1/2`, the middle term is
   `mdlScaleFe_integrand_eq` integrated, and the last term is `mdlW2_integrand_eq` integrated.

The whole content is the algebraic cancellation of the powers of `2` and `N`
(`2^{k₁-dk₂}·2^{-k₁}·2^{dk₂} = 1`, `N^{d-1}·(N^d)^{-1} = N^{-1}`, which uses `d ≥ 1`, i.e. that
`P'` does not vanish identically).

## Note on the shared dependency (read if the build of `MdlDefs` breaks)

While proving this lemma, `Submission/Work/KMTPlan/A6/MdlDefs.lean` was temporarily unbuildable:
`lowLargeScaled.lean` had changed the signature of the §6 model inputs to
`mdlF ρ u l f = piExact (kmtPj ρ) l (-(u:ℤ)) f` (and added the companion
`mdlG ρ P u l g = piExact (kmtPj ρ) l (-(d·u:ℤ)) g`), while `MdlDefs.lean` still called `mdlF ρ l f`
(8 call sites in `mdlPart_eq`, `mdlPartJ`, `mdlSliceJ`, `mdlSliceJ_apply`).  That broke the build of
every module importing `MdlDefs`.  Because the `:= rfl` proof of `mdlPart_eq` pins the arguments
down uniquely, the repair was forced: the calls now read
`mdlF ρ (uScale ρ (max (max l₁ l₂) (max k₁ k₂))) l₁ f` and
`mdlG ρ P (uScale ρ (max (max l₁ l₂) (max k₁ k₂))) l₂ g`, matching `lowLargeScaled.lean`'s
`mdlPart` verbatim.  The pre-repair file is kept at `.scratch/mine/MdlDefs.lean.bak`.
This repair does not affect the statement or the proof below (which never mentions `mdlF`/`mdlG`).
-/
import Mathlib
import Submission.Work.KMTPlan.A6.MdlDefs
import Submission.Work.KMTPlan.A6.integIdent_ii_core

set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

namespace Work.KMTPlan.A6

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators Interval
open Work.KMTAreas.A7

/-! ## The character `ee` and the modulation product -/

/-- `ee` is a character: `e(x+y) = e(x)e(y)`.  (This is `Work.KMTPlan.A6.ee_add` of
`EeModulation.lean`; it is reproved here under a distinct name so that this module does not
depend on that one.) -/
theorem ee_add_mul_char (x y : ℝ) : ee (x + y) = ee x * ee y := by
  simp only [ee]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The two modulations of the bumps multiply to the phase `Φ(t) = e(ξ₁Nt + ξ₂P(Nt))`. -/
theorem varphiNt_mul_varphitildeNt (P : ℤ[X]) (N : ℕ) (ξ₁ ξ₂ : ℝ) (t : ℝ) :
    ee ((N:ℝ)*t*ξ₁) * ee (PevalR P ((N:ℝ)*t) * ξ₂) = Phi P N ξ₁ ξ₂ t := by
  rw [← ee_add_mul_char, Phi_apply, phase_apply]
  congr 1
  ring

/-! ## The three pointwise identities

Each of them unwraps the definitions and is a computation in `ℂ`: cancel the powers of `2` and
`N` introduced by the modified bumps against the weights `W₁`, `W₂` and the constants
`mdlScale`, `mdlScaleFe`.  The hypothesis `P'(Nt) ≠ 0` (and `ξ₂ ≠ 0`, `N ≠ 0`) makes all the
divisions legitimate; `1 ≤ P.natDegree` (which follows from the non-vanishing of `P'`) is needed
to reduce `N^{d-1}·N = N^d`.
-/

/-- **The endpoint term.**  `mdlScale · mdlIota · φ_{N,t,k₁}(ξ₁) φ̃_{N,t,k₂,-1}(ξ₂) W₁(t)`
equals `φ_N^{k₁}(ξ₁) φ̃_N^{k₂}(ξ₂) · Φ(t)/cnorm₂(t)`. -/
theorem mdlW1_integrand_eq (P : ℤ[X]) (N k₁ k₂ : ℕ) (hN : 1 ≤ N) (ξ₁ ξ₂ : ℝ)
    (hξ₂ : ξ₂ ≠ 0) (hd1 : 1 ≤ P.natDegree) (t : ℝ) (hP : PderivR P ((N:ℝ)*t) ≠ 0) :
    (mdlScale P k₂ : ℂ) * mdlIota
        * (varphiNt N k₁ t ξ₁ * varphitildeNtj P N k₂ (-1) t ξ₂ * mdlW1 P N t)
      = (varphiN N k₁ ξ₁ * varphitildeN P.natDegree N k₂ ξ₂)
          * (Phi P N ξ₁ ξ₂ t / cnorm₂ P N ξ₂ t) := by
  have hcoef : (mdlScale P k₂ : ℂ) * mdlIota
        * ((((2:ℝ)^(-((P.natDegree:ℝ)*(k₂:ℝ))) * ((N:ℝ))^P.natDegree * ξ₂ : ℝ) : ℂ)⁻¹
            * mdlW1 P N t) = (cnorm₂ P N ξ₂ t)⁻¹ := by
    rw [mdlScale, mdlIota, mdlW1, cnorm₂_apply]
    push_cast
    have hNc : ((N:ℝ) : ℂ) ≠ 0 := by
      rw [Ne, Complex.ofReal_eq_zero]
      exact_mod_cast (ne_of_gt (Nat.lt_of_lt_of_le Nat.zero_lt_one hN))
    have hNc2 : (N : ℂ) ≠ 0 := by
      exact_mod_cast (ne_of_gt (Nat.lt_of_lt_of_le Nat.zero_lt_one hN))
    have hξ₂c : ((ξ₂:ℝ) : ℂ) ≠ 0 := by rw [Ne, Complex.ofReal_eq_zero]; exact hξ₂
    have hP'c : ((PderivR P ((N:ℝ)*t):ℝ) : ℂ) ≠ 0 := by
      rw [Ne, Complex.ofReal_eq_zero]; exact hP
    have hpi : (2 * (Real.pi:ℂ) * Complex.I) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero
    have ha : (((2:ℝ)^(-((P.natDegree:ℝ)*(k₂:ℝ))) : ℝ) : ℂ) ≠ 0 := by
      rw [Ne, Complex.ofReal_eq_zero]
      exact ne_of_gt (Real.rpow_pos_of_pos (by norm_num) _)
    field_simp
    rw [← pow_succ]
    congr 1
    omega
  calc (mdlScale P k₂ : ℂ) * mdlIota
          * (varphiNt N k₁ t ξ₁ * varphitildeNtj P N k₂ (-1) t ξ₂ * mdlW1 P N t)
      = (varphiN N k₁ ξ₁ * varphitildeN P.natDegree N k₂ ξ₂)
          * (ee ((N:ℝ)*t*ξ₁) * ee (PevalR P ((N:ℝ)*t) * ξ₂))
          * ((mdlScale P k₂ : ℂ) * mdlIota
              * ((((2:ℝ)^(-((P.natDegree:ℝ)*(k₂:ℝ))) * ((N:ℝ))^P.natDegree * ξ₂ : ℝ) : ℂ)⁻¹
                  * mdlW1 P N t)) := by
        rw [varphiNt, varphitildeNtj, varphitildeNt]
        simp only [zpow_neg_one]
        ring
    _ = (varphiN N k₁ ξ₁ * varphitildeN P.natDegree N k₂ ξ₂) * Phi P N ξ₁ ξ₂ t
          * ((mdlScale P k₂ : ℂ) * mdlIota
              * ((((2:ℝ)^(-((P.natDegree:ℝ)*(k₂:ℝ))) * ((N:ℝ))^P.natDegree * ξ₂ : ℝ) : ℂ)⁻¹
                  * mdlW1 P N t)) := by
        rw [varphiNt_mul_varphitildeNt P N ξ₁ ξ₂ t]
    _ = (varphiN N k₁ ξ₁ * varphitildeN P.natDegree N k₂ ξ₂) * Phi P N ξ₁ ξ₂ t
          * (cnorm₂ P N ξ₂ t)⁻¹ := by
        rw [hcoef]
    _ = (varphiN N k₁ ξ₁ * varphitildeN P.natDegree N k₂ ξ₂)
          * (Phi P N ξ₁ ξ₂ t / cnorm₂ P N ξ₂ t) := by
        rw [div_eq_mul_inv]; ring

/-- **The middle term.**  `mdlScaleFe · φ_{N,t,k₁,1}(ξ₁) φ̃_{N,t,k₂,-1}(ξ₂) W₁(t)` equals
`φ_N^{k₁}(ξ₁) φ̃_N^{k₂}(ξ₂) · (ξ₁/ξ₂) · Φ(t)/P'(Nt)`. -/
theorem mdlScaleFe_integrand_eq (P : ℤ[X]) (N k₁ k₂ : ℕ) (hN : 1 ≤ N) (ξ₁ ξ₂ : ℝ)
    (hξ₂ : ξ₂ ≠ 0) (hd1 : 1 ≤ P.natDegree) (t : ℝ) (hP : PderivR P ((N:ℝ)*t) ≠ 0) :
    (mdlScaleFe P k₁ k₂ : ℂ)
      * (varphiNtj N k₁ 1 t ξ₁ * varphitildeNtj P N k₂ (-1) t ξ₂ * mdlW1 P N t)
    = (varphiN N k₁ ξ₁ * varphitildeN P.natDegree N k₂ ξ₂)
        * ((((ξ₁/ξ₂:ℝ)) : ℂ) * Ffac P (N:ℝ) ξ₁ ξ₂ t) := by
  rw [mdlScaleFe, varphiNtj, varphitildeNtj, varphiNt, varphitildeNt, mdlW1, Ffac]
  simp only [zpow_one, zpow_neg_one]
  rw [← varphiNt_mul_varphitildeNt P N ξ₁ ξ₂ t]
  rw [Real.rpow_sub (by norm_num) (k₁:ℝ) ((P.natDegree:ℝ)*(k₂:ℝ)),
      Real.rpow_neg (x := 2) (by norm_num) (k₁:ℝ),
      Real.rpow_neg (x := 2) (by norm_num) ((P.natDegree:ℝ)*(k₂:ℝ))]
  push_cast
  have hNc : ((N:ℝ) : ℂ) ≠ 0 := by
    rw [Ne, Complex.ofReal_eq_zero]
    exact_mod_cast (ne_of_gt (Nat.lt_of_lt_of_le Nat.zero_lt_one hN))
  have hNc2 : (N : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Nat.lt_of_lt_of_le Nat.zero_lt_one hN))
  have hξ₂c : ((ξ₂:ℝ) : ℂ) ≠ 0 := by rw [Ne, Complex.ofReal_eq_zero]; exact hξ₂
  have hP'c : ((PderivR P ((N:ℝ)*t):ℝ) : ℂ) ≠ 0 := by
    rw [Ne, Complex.ofReal_eq_zero]; exact hP
  have h2a : ((((2:ℝ)^(k₁:ℝ) : ℝ)) : ℂ) ≠ 0 := by
    rw [Ne, Complex.ofReal_eq_zero]
    exact ne_of_gt (Real.rpow_pos_of_pos (by norm_num) _)
  have h2b : ((((2:ℝ)^((P.natDegree:ℝ)*(k₂:ℝ)) : ℝ)) : ℂ) ≠ 0 := by
    rw [Ne, Complex.ofReal_eq_zero]
    exact ne_of_gt (Real.rpow_pos_of_pos (by norm_num) _)
  have hpowmul : ((N:ℂ))^(P.natDegree - 1) * (N:ℂ) = (N:ℂ)^P.natDegree := by
    rw [← pow_succ]; congr 1; omega
  field_simp
  rw [← hpowmul]
  ring

/-- **The last term.**  `mdlScale · mdlIota · φ_{N,t,k₁}(ξ₁) φ̃_{N,t,k₂,-1}(ξ₂) W₂(t)` equals
`φ_N^{k₁}(ξ₁) φ̃_N^{k₂}(ξ₂) · (1/(2πiξ₂)) · Φ(t) P''(Nt)/P'(Nt)²`. -/
theorem mdlW2_integrand_eq (P : ℤ[X]) (N k₁ k₂ : ℕ) (hN : 1 ≤ N) (ξ₁ ξ₂ : ℝ)
    (hξ₂ : ξ₂ ≠ 0) (t : ℝ) (hP : PderivR P ((N:ℝ)*t) ≠ 0) :
    (mdlScale P k₂ : ℂ) * mdlIota
        * (varphiNt N k₁ t ξ₁ * varphitildeNtj P N k₂ (-1) t ξ₂ * mdlW2 P N t)
      = (varphiN N k₁ ξ₁ * varphitildeN P.natDegree N k₂ ξ₂)
          * ((1 / (2 * (Real.pi:ℂ) * Complex.I * (ξ₂:ℂ))) * Gfac P (N:ℝ) ξ₁ ξ₂ t) := by
  have hcoef : (mdlScale P k₂ : ℂ) * mdlIota
        * ((((2:ℝ)^(-((P.natDegree:ℝ)*(k₂:ℝ))) * ((N:ℝ))^P.natDegree * ξ₂ : ℝ) : ℂ)⁻¹
            * mdlW2 P N t)
      = (1 / (2 * (Real.pi:ℂ) * Complex.I * (ξ₂:ℂ)))
          * ((Pderiv2R P ((N:ℝ)*t) / (PderivR P ((N:ℝ)*t))^2 : ℝ) : ℂ) := by
    rw [mdlScale, mdlIota, mdlW2]
    push_cast
    have hNc : ((N:ℝ) : ℂ) ≠ 0 := by
      rw [Ne, Complex.ofReal_eq_zero]
      exact_mod_cast (ne_of_gt (Nat.lt_of_lt_of_le Nat.zero_lt_one hN))
    have hNc2 : (N : ℂ) ≠ 0 := by
      exact_mod_cast (ne_of_gt (Nat.lt_of_lt_of_le Nat.zero_lt_one hN))
    have hξ₂c : ((ξ₂:ℝ) : ℂ) ≠ 0 := by rw [Ne, Complex.ofReal_eq_zero]; exact hξ₂
    have hP'c : ((PderivR P ((N:ℝ)*t):ℝ) : ℂ) ≠ 0 := by
      rw [Ne, Complex.ofReal_eq_zero]; exact hP
    have hpi : (2 * (Real.pi:ℂ) * Complex.I) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero
    have ha : (((2:ℝ)^(-((P.natDegree:ℝ)*(k₂:ℝ))) : ℝ) : ℂ) ≠ 0 := by
      rw [Ne, Complex.ofReal_eq_zero]
      exact ne_of_gt (Real.rpow_pos_of_pos (by norm_num) _)
    field_simp
  calc (mdlScale P k₂ : ℂ) * mdlIota
          * (varphiNt N k₁ t ξ₁ * varphitildeNtj P N k₂ (-1) t ξ₂ * mdlW2 P N t)
      = (varphiN N k₁ ξ₁ * varphitildeN P.natDegree N k₂ ξ₂)
          * (ee ((N:ℝ)*t*ξ₁) * ee (PevalR P ((N:ℝ)*t) * ξ₂))
          * ((mdlScale P k₂ : ℂ) * mdlIota
              * ((((2:ℝ)^(-((P.natDegree:ℝ)*(k₂:ℝ))) * ((N:ℝ))^P.natDegree * ξ₂ : ℝ) : ℂ)⁻¹
                  * mdlW2 P N t)) := by
        rw [varphiNt, varphitildeNtj, varphitildeNt]
        simp only [zpow_neg_one]
        ring
    _ = (varphiN N k₁ ξ₁ * varphitildeN P.natDegree N k₂ ξ₂)
          * (ee ((N:ℝ)*t*ξ₁) * ee (PevalR P ((N:ℝ)*t) * ξ₂))
          * ((1 / (2 * (Real.pi:ℂ) * Complex.I * (ξ₂:ℂ)))
              * ((Pderiv2R P ((N:ℝ)*t) / (PderivR P ((N:ℝ)*t))^2 : ℝ) : ℂ)) := by
        rw [hcoef]
    _ = (varphiN N k₁ ξ₁ * varphitildeN P.natDegree N k₂ ξ₂)
          * ((1 / (2 * (Real.pi:ℂ) * Complex.I * (ξ₂:ℂ))) * Gfac P (N:ℝ) ξ₁ ξ₂ t) := by
        rw [Gfac]
        rw [varphiNt_mul_varphitildeNt P N ξ₁ ξ₂ t]
        ring

/-! ## The identity -/

theorem MdlBumpIntegIdent (P : Polynomial ℤ) (N k₁ k₂ : ℕ) (hN : 1 ≤ N) (hk₂ : 1 ≤ k₂)
    (hP : ∀ t ∈ Set.Icc (1 / 2 : ℝ) 1, Work.KMTPlan.A6.PderivR P ((N : ℝ) * t) ≠ 0) :
    ∀ ξ₁ ξ₂ : ℝ, ξ₂ ≠ 0 →
      (∫ t in (1 / 2 : ℝ)..1,
          Work.KMTAreas.A7.varphiNt N k₁ t ξ₁ * Work.KMTAreas.A7.varphitildeNt P P.natDegree N k₂ t ξ₂)
        = (Work.KMTPlan.A6.mdlScale P k₂ : ℂ) * Work.KMTPlan.A6.mdlIota
            * (Work.KMTAreas.A7.varphiNt N k₁ 1 ξ₁
                * Work.KMTPlan.A6.varphitildeNtj P N k₂ (-1) 1 ξ₂ * Work.KMTPlan.A6.mdlW1 P N 1
              - Work.KMTAreas.A7.varphiNt N k₁ (1 / 2) ξ₁
                * Work.KMTPlan.A6.varphitildeNtj P N k₂ (-1) (1 / 2) ξ₂ * Work.KMTPlan.A6.mdlW1 P N (1 / 2))
          - (Work.KMTPlan.A6.mdlScaleFe P k₁ k₂ : ℂ)
              * (∫ t in (1 / 2 : ℝ)..1, Work.KMTPlan.A6.varphiNtj N k₁ 1 t ξ₁
                  * Work.KMTPlan.A6.varphitildeNtj P N k₂ (-1) t ξ₂ * Work.KMTPlan.A6.mdlW1 P N t)
          + (Work.KMTPlan.A6.mdlScale P k₂ : ℂ) * Work.KMTPlan.A6.mdlIota
              * (∫ t in (1 / 2 : ℝ)..1, Work.KMTAreas.A7.varphiNt N k₁ t ξ₁
                  * Work.KMTPlan.A6.varphitildeNtj P N k₂ (-1) t ξ₂ * Work.KMTPlan.A6.mdlW2 P N t) := by
  intro ξ₁ ξ₂ hξ₂
  have hN' : (N:ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Nat.lt_of_lt_of_le Nat.zero_lt_one hN))
  have hP'' : ∀ t ∈ Set.uIcc (1/2:ℝ) 1, PderivR P ((N:ℝ)*t) ≠ 0 := by
    intro t ht
    rw [Set.uIcc_of_le (by norm_num)] at ht
    exact hP t ht
  -- `P'` does not vanish on the interval, hence `P` is not constant
  have hd1 : 1 ≤ P.natDegree := by
    by_contra h
    have hd0 : P.natDegree = 0 := by omega
    have hder : P.derivative = 0 := Polynomial.derivative_eq_zero.mpr hd0
    have hz : PderivR P ((N:ℝ) * (1/2)) = 0 := by simp [PderivR, hder]
    exact hP (1/2) (by norm_num [Set.mem_Icc]) hz
  -- Step 1: pull the `t`-independent factor out of the integral
  have hA : (∫ t in (1/2:ℝ)..1,
        varphiNt N k₁ t ξ₁ * varphitildeNt P P.natDegree N k₂ t ξ₂)
      = (varphiN N k₁ ξ₁ * varphitildeN P.natDegree N k₂ ξ₂)
          * (∫ t in (1/2:ℝ)..1, Phi P N ξ₁ ξ₂ t) := by
    have hpt : ∀ t : ℝ, varphiNt N k₁ t ξ₁ * varphitildeNt P P.natDegree N k₂ t ξ₂
        = (varphiN N k₁ ξ₁ * varphitildeN P.natDegree N k₂ ξ₂) * Phi P N ξ₁ ξ₂ t := by
      intro t
      rw [varphiNt, varphitildeNt, ← varphiNt_mul_varphitildeNt P N ξ₁ ξ₂ t]
      ring
    rw [show (∫ t in (1/2:ℝ)..1,
          varphiNt N k₁ t ξ₁ * varphitildeNt P P.natDegree N k₂ t ξ₂)
        = ∫ t in (1/2:ℝ)..1,
            (varphiN N k₁ ξ₁ * varphitildeN P.natDegree N k₂ ξ₂) * Phi P N ξ₁ ξ₂ t
        from intervalIntegral.integral_congr (fun t _ => hpt t)]
    rw [intervalIntegral.integral_const_mul]
  -- Step 2: the three terms of the identity
  have hT1 : (mdlScale P k₂ : ℂ) * mdlIota
        * (varphiNt N k₁ 1 ξ₁ * varphitildeNtj P N k₂ (-1) 1 ξ₂ * mdlW1 P N 1
          - varphiNt N k₁ (1 / 2) ξ₁ * varphitildeNtj P N k₂ (-1) (1 / 2) ξ₂ * mdlW1 P N (1 / 2))
      = (varphiN N k₁ ξ₁ * varphitildeN P.natDegree N k₂ ξ₂)
          * (Phi P N ξ₁ ξ₂ 1 / cnorm₂ P N ξ₂ 1)
        - (varphiN N k₁ ξ₁ * varphitildeN P.natDegree N k₂ ξ₂)
          * (Phi P N ξ₁ ξ₂ (1 / 2) / cnorm₂ P N ξ₂ (1 / 2)) := by
    rw [mul_sub]
    rw [mdlW1_integrand_eq P N k₁ k₂ hN ξ₁ ξ₂ hξ₂ hd1 1
          (by simpa using hP 1 (by norm_num [Set.mem_Icc])),
        mdlW1_integrand_eq P N k₁ k₂ hN ξ₁ ξ₂ hξ₂ hd1 (1/2)
          (hP (1/2) (by norm_num [Set.mem_Icc]))]
  have hT2 : (mdlScaleFe P k₁ k₂ : ℂ)
      * (∫ t in (1 / 2 : ℝ)..1, varphiNtj N k₁ 1 t ξ₁
          * varphitildeNtj P N k₂ (-1) t ξ₂ * mdlW1 P N t)
      = (varphiN N k₁ ξ₁ * varphitildeN P.natDegree N k₂ ξ₂)
          * ((((ξ₁ / ξ₂ : ℝ) : ℂ))
              * (∫ t in (1 / 2 : ℝ)..1, Ffac P (N:ℝ) ξ₁ ξ₂ t)) := by
    have h1 : (∫ t in (1 / 2 : ℝ)..1, (mdlScaleFe P k₁ k₂ : ℂ)
          * (varphiNtj N k₁ 1 t ξ₁ * varphitildeNtj P N k₂ (-1) t ξ₂ * mdlW1 P N t))
        = (mdlScaleFe P k₁ k₂ : ℂ)
          * (∫ t in (1 / 2 : ℝ)..1, varphiNtj N k₁ 1 t ξ₁
              * varphitildeNtj P N k₂ (-1) t ξ₂ * mdlW1 P N t) :=
      intervalIntegral.integral_const_mul _ _
    rw [← h1]
    rw [show (∫ t in (1 / 2 : ℝ)..1, (mdlScaleFe P k₁ k₂ : ℂ)
          * (varphiNtj N k₁ 1 t ξ₁ * varphitildeNtj P N k₂ (-1) t ξ₂ * mdlW1 P N t))
        = ∫ t in (1 / 2 : ℝ)..1, (varphiN N k₁ ξ₁ * varphitildeN P.natDegree N k₂ ξ₂)
            * ((((ξ₁/ξ₂:ℝ)) : ℂ) * Ffac P (N:ℝ) ξ₁ ξ₂ t) from
        intervalIntegral.integral_congr
          (fun t ht => mdlScaleFe_integrand_eq P N k₁ k₂ hN ξ₁ ξ₂ hξ₂ hd1 t (hP'' t ht))]
    rw [intervalIntegral.integral_const_mul]
    rw [intervalIntegral.integral_const_mul]
  have hT3 : (mdlScale P k₂ : ℂ) * mdlIota
      * (∫ t in (1 / 2 : ℝ)..1, varphiNt N k₁ t ξ₁
          * varphitildeNtj P N k₂ (-1) t ξ₂ * mdlW2 P N t)
      = (varphiN N k₁ ξ₁ * varphitildeN P.natDegree N k₂ ξ₂)
          * ((1 / (2 * (Real.pi:ℂ) * Complex.I * (ξ₂:ℂ)))
              * (∫ t in (1 / 2 : ℝ)..1, Gfac P (N:ℝ) ξ₁ ξ₂ t)) := by
    have h1 : (∫ t in (1 / 2 : ℝ)..1, (mdlScale P k₂ : ℂ) * mdlIota
          * (varphiNt N k₁ t ξ₁ * varphitildeNtj P N k₂ (-1) t ξ₂ * mdlW2 P N t))
        = ((mdlScale P k₂ : ℂ) * mdlIota)
          * (∫ t in (1 / 2 : ℝ)..1, varphiNt N k₁ t ξ₁
              * varphitildeNtj P N k₂ (-1) t ξ₂ * mdlW2 P N t) :=
      intervalIntegral.integral_const_mul _ _
    rw [← h1]
    rw [show (∫ t in (1 / 2 : ℝ)..1, (mdlScale P k₂ : ℂ) * mdlIota
          * (varphiNt N k₁ t ξ₁ * varphitildeNtj P N k₂ (-1) t ξ₂ * mdlW2 P N t))
        = ∫ t in (1 / 2 : ℝ)..1, (varphiN N k₁ ξ₁ * varphitildeN P.natDegree N k₂ ξ₂)
            * ((1 / (2 * (Real.pi:ℂ) * Complex.I * (ξ₂:ℂ))) * Gfac P (N:ℝ) ξ₁ ξ₂ t) from
        intervalIntegral.integral_congr
          (fun t ht => mdlW2_integrand_eq P N k₁ k₂ hN ξ₁ ξ₂ hξ₂ t (hP'' t ht))]
    rw [intervalIntegral.integral_const_mul]
    rw [intervalIntegral.integral_const_mul]
  -- Step 3: the two integrals produced by `integ-ident`(ii), written as `Ffac`/`Gfac`
  have hF : (∫ t in (1 / 2 : ℝ)..1,
        Phi P (N:ℝ) ξ₁ ξ₂ t / ((PderivR P ((N:ℝ) * t) : ℝ) : ℂ))
      = ∫ t in (1 / 2 : ℝ)..1, Ffac P (N:ℝ) ξ₁ ξ₂ t := by simp only [Ffac]
  have hG : (∫ t in (1 / 2 : ℝ)..1, Phi P (N:ℝ) ξ₁ ξ₂ t
        * (((Pderiv2R P ((N:ℝ) * t) / (PderivR P ((N:ℝ) * t)) ^ 2 : ℝ)) : ℂ))
      = ∫ t in (1 / 2 : ℝ)..1, Gfac P (N:ℝ) ξ₁ ξ₂ t := by simp only [Gfac]
  rw [hA]
  rw [integIdent_ii_corrected P (N := (N:ℝ)) (ξ₁ := ξ₁) (ξ₂ := ξ₂) hN' hξ₂ hP'']
  rw [hF, hG, hT1, hT2, hT3]
  ring

end

end Work.KMTPlan.A6
