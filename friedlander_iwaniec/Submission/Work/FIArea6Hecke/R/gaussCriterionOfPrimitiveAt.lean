/-
# `gaussCriterionOfPrimitiveAt`: the Gauss-sum criterion for a character primitive at `4D`

The classical criterion "`‖G(χ)‖² = N(4D)` if and only if `χ` is primitive at the level `4D`",
proved here in the form needed by the conductor reduction (`Work.FIArea6Hecke.R`):
`IsPrimitiveUnitAt (4D) χ₀` (primitivity witnessed by *units*) together with strictness forces the
Gauss sum to have the maximal size.

The proof is the standard one:

* `Fhat d χ θ` is the finite Fourier transform of the periodic weight `FR d χ` on
  `R = ℤ[i]/(4D) = (ZMod (4D))²` (`Work.FIArea5.S16Hecke.GaussBasic`);
* a primitive character has no Fourier coefficient at a **non-unit** class
  (`gcp_Fhat_eq_zero_of_witness`): the witness `z ≡ 1 (mod c)`, `χ z ≠ 1` lets one shift the
  summation variable `x ↦ x·z`, which permutes the units and leaves the additive character
  `x ↦ e(Re(xξ̄)/4D)` unchanged because `4D ∣ (z-1)·ξ̄`;
* Parseval (`Work.FIArea5.S16Hecke.GaussBasic.parseval`) then gives
  `16D²·#U = ∑_θ ‖Fhat θ‖² = #U·‖G‖²`, whence `‖G‖² = 16D²`.
-/
import Mathlib
import Submission.Work.FIArea6Hecke.R.StrictConductorDefs
import Submission.Work.FIArea5.S16Hecke.ThetaDefs
import Submission.Work.FIArea5.S16Hecke.GaussBasic
import Submission.Work.FIArea5.S16Hecke.GaussFourier
import Submission.Work.FIArea5.S16Hecke.GaussChi
import Submission.Work.FIArea6Hecke.R.gaussSum_zero_of_nontrivial

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

namespace Work.FIArea6Hecke.R

open Finset
open scoped BigOperators
open Work.FIArea5.S16Hecke
open Work.FIArea5.S16Hecke.GaussBasic

noncomputable section

/-- **Primitivity of `χ₀` at the level `M` with *unit* witnesses**: for every non-unit proper
divisor `M' ∣ M` there is a **unit** `z` mod `M` with `z ≡ 1 (mod M')` and `χ₀ z ≠ 1`.

(Adding `IsUnitMod M z` to `Work.FIArea6Hecke.R.IsPrimitiveAt` is necessary: without it the
condition is satisfied by *any* strict character at every `M'` — a non-unit `z` gives `χ₀ z = 0`,
which is `≠ 1` for free.  Recorded after a reviewer found the counterexample `D = 3`, `4D = 12`,
`χ₀` the lift of a quadratic character of `(ℤ[i]/4)^*`: `IsPrimitiveAt 12 χ₀` holds but
`‖gaussSum 3 χ₀ 1‖² = 16 ≠ 144`.) -/
def IsPrimitiveUnitAt (M : GaussianInt) (chi₀ : GaussianInt → ℂ) : Prop :=
  ∀ M' : GaussianInt, M' ∣ M → ¬ (M ∣ M') → ¬ IsUnit M' →
    ∃ z : GaussianInt, IsUnitMod M z ∧ M' ∣ (z - 1) ∧ chi₀ z ≠ 1

section RingAux

variable {d : ℕ} [NeZero (4 * d)]

/-- Gaussian multiplication is additive in the second variable. -/
private lemma gcp_gmul_add_right (x y z : ZMod (4 * d) × ZMod (4 * d)) :
    gmul d x (y + z) = gmul d x y + gmul d x z := by
  ext <;> simp only [gmul, Prod.fst_add, Prod.snd_add] <;> ring

/-- Gaussian multiplication is additive in the first variable. -/
private lemma gcp_gmul_add_left (x y z : ZMod (4 * d) × ZMod (4 * d)) :
    gmul d (x + y) z = gmul d x z + gmul d y z := by
  ext <;> simp only [gmul, Prod.fst_add, Prod.snd_add] <;> ring

/-- Gaussian multiplication is subtractive in the first variable. -/
private lemma gcp_gmul_sub_left (x y z : ZMod (4 * d) × ZMod (4 * d)) :
    gmul d (x - y) z = gmul d x z - gmul d y z := by
  ext <;> simp only [gmul, Prod.fst_sub, Prod.snd_sub] <;> ring

private lemma gcp_gmul_zero_left (x : ZMod (4 * d) × ZMod (4 * d)) : gmul d 0 x = 0 := by
  ext <;> simp [gmul]

private lemma gcp_gmul_zero_right (x : ZMod (4 * d) × ZMod (4 * d)) : gmul d x 0 = 0 := by
  ext <;> simp [gmul]

/-- `gOfZI` is subtractive. -/
private lemma gcp_gOfZI_sub (a b : GaussianInt) :
    gOfZI d (a - b) = gOfZI d a - gOfZI d b := by
  ext <;> simp [gOfZI]

/-- `gOfZI` commutes with conjugation. -/
private lemma gcp_gOfZI_star (z : GaussianInt) : gOfZI d (star z) = gconj d (gOfZI d z) := by
  ext <;> simp [gOfZI, gconj]

private lemma gcp_gOfZI_fourD : gOfZI d ((((4 * d : ℕ) : ℤ)) : GaussianInt) = 0 := by
  have h2 : ((4 * d : ℕ) : ZMod (4 * d)) = 0 := ZMod.natCast_self (4 * d)
  ext
  · show ((((4 * d : ℕ) : ℤ) : ZMod (4 * d))) = 0
    simpa only [Int.cast_natCast] using h2
  · show ((0 : ℤ) : ZMod (4 * d)) = 0
    simp

/-- A multiple of `4d` has vanishing residue class. -/
private lemma gcp_gOfZI_eq_zero_of_dvd {ζ : GaussianInt}
    (h : ((((4 * d : ℕ) : ℤ)) : GaussianInt) ∣ ζ) : gOfZI d ζ = 0 := by
  obtain ⟨u, rfl⟩ := h
  rw [gOfZI_mul, gcp_gOfZI_fourD, gcp_gmul_zero_left]

/-- Multiplication by a unit permutes the Gaussian residue ring. -/
private lemma gcp_sum_gmul_right_unit (y : ZMod (4 * d) × ZMod (4 * d)) (hy : IsUnitR d y)
    (f : ZMod (4 * d) × ZMod (4 * d) → ℂ) :
    (∑ γ, f (gmul d γ y)) = ∑ x, f x := by
  obtain ⟨y', hy'⟩ := hy
  have hy'' : gmul d y' y = gone d := by rw [gmul_comm]; exact hy'
  let e : ZMod (4 * d) × ZMod (4 * d) ≃ ZMod (4 * d) × ZMod (4 * d) :=
    { toFun := fun γ => gmul d γ y
      invFun := fun γ => gmul d γ y'
      left_inv := fun γ => by
        show gmul d (gmul d γ y) y' = γ
        rw [gmul_assoc, hy', gmul_gone_right]
      right_inv := fun γ => by
        show gmul d (gmul d γ y') y = γ
        rw [gmul_assoc, hy'', gmul_gone_right] }
  exact Equiv.sum_comp e f

end RingAux

/-! ## Norms in `ℤ[i]`, conjugation, and the star-invariance of `IsUnitMod4d` -/

section NormAux

/-- The norm of `ℤ[i]` in coordinates. -/
private lemma gcp_norm_eq (z : GaussianInt) : z.norm = z.re ^ 2 + z.im ^ 2 := by
  rw [Zsqrtd.norm_def]; ring

/-- The norm of an integer is its square. -/
private lemma gcp_norm_intCast (n : ℤ) : ((n : GaussianInt)).norm = n ^ 2 := by
  rw [gcp_norm_eq]; simp

private lemma gcp_norm_nonneg (z : GaussianInt) : 0 ≤ z.norm := by
  rw [gcp_norm_eq]; positivity

/-- An element of norm `≠ 1` is not a unit. -/
private lemma gcp_not_isUnit_of_norm_ne_one {z : GaussianInt} (h : z.norm ≠ 1) :
    ¬ IsUnit z := by
  rintro ⟨u, hu⟩
  have h2 : (↑u : GaussianInt).norm * (↑u⁻¹ : GaussianInt).norm = 1 := by
    rw [← Zsqrtd.norm_mul, Units.mul_inv]
    rw [show (1 : GaussianInt) = (((1 : ℕ) : ℤ) : GaussianInt) from by norm_num,
      gcp_norm_intCast]
    norm_num
  have h5 : (↑u : GaussianInt).norm = 1 :=
    Int.eq_one_of_mul_eq_one_right (gcp_norm_nonneg _) h2
  rw [hu] at h5
  exact h h5

/-- `2` is not a unit of `ℤ[i]`. -/
private lemma gcp_not_isUnit_two : ¬ IsUnit (2 : GaussianInt) := by
  refine gcp_not_isUnit_of_norm_ne_one ?_
  rw [show (2 : GaussianInt) = (((2 : ℕ) : ℤ) : GaussianInt) from by norm_num]
  rw [gcp_norm_intCast]; norm_num

/-- `2D` is not a unit of `ℤ[i]` for `D ≥ 1`. -/
private lemma gcp_not_isUnit_twoD {D : ℕ} (hD : 1 ≤ D) :
    ¬ IsUnit (((2 * D : ℕ) : ℤ) : GaussianInt) := by
  refine gcp_not_isUnit_of_norm_ne_one ?_
  rw [gcp_norm_intCast]
  intro hc
  push_cast at hc
  have h1 : (1 : ℤ) ≤ (D : ℤ) := by exact_mod_cast hD
  nlinarith

/-- A nonzero natural number is a nonzero Gaussian integer. -/
private lemma gcp_intCast_ne_zero {n : ℕ} (hn : n ≠ 0) :
    ((((n : ℕ) : ℤ)) : GaussianInt) ≠ 0 := by
  intro h0
  have hnorm : ((((n : ℕ) : ℤ) : GaussianInt)).norm = 0 := by
    rw [h0]
    rw [show (0 : GaussianInt) = (((0 : ℕ) : ℤ) : GaussianInt) from by norm_num,
      gcp_norm_intCast]
    norm_num
  rw [gcp_norm_intCast] at hnorm
  push_cast at hnorm
  have h1 : (0 : ℤ) < (n : ℤ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  nlinarith

/-- `4D` as a Gaussian integer does not vanish (`D ≥ 1`). -/
private lemma gcp_fourD_ne_zero {D : ℕ} (hD : 1 ≤ D) :
    ((((4 * D : ℕ) : ℤ)) : GaussianInt) ≠ 0 :=
  gcp_intCast_ne_zero (n := 4 * D) (by omega)

/-- `4D ∤ 2D` in `ℤ[i]` for `D ≥ 1`. -/
private lemma gcp_not_dvd_twoD {D : ℕ} (hD : 1 ≤ D) :
    ¬ ((((4 * D : ℕ) : ℤ)) : GaussianInt) ∣ (((2 * D : ℕ) : ℤ) : GaussianInt) := by
  rintro ⟨k, hk⟩
  have hMne := gcp_fourD_ne_zero hD
  have h2D : (((2 * D : ℕ) : ℤ) : GaussianInt) ≠ 0 :=
    gcp_intCast_ne_zero (n := 2 * D) (by omega)
  have h1 : (((2 * D : ℕ) : ℤ) : GaussianInt) * 1
      = (((2 * D : ℕ) : ℤ) : GaussianInt) * (2 * k) := by
    rw [mul_one]
    conv_lhs => rw [hk]
    push_cast
    ring
  have h2 : (1 : GaussianInt) = 2 * k := mul_left_cancel₀ h2D h1
  exact gcp_not_isUnit_two ((isUnit_iff_exists_inv).mpr ⟨k, h2.symm⟩)

/-- Conjugation preserves `IsUnitMod4d`. -/
private lemma gcp_isUnitMod4d_star_aux {d : ℕ} (z : GaussianInt) :
    IsUnitMod4d d (star z) → IsUnitMod4d d z := by
  rintro ⟨w, t, ht⟩
  refine ⟨star w, star t, ?_⟩
  have h := congrArg star ht
  rw [star_sub, star_mul, star_star, star_one, star_mul, star_intCast] at h
  rw [mul_comm (star w) z, mul_comm (star t) ((((4 * d : ℕ) : ℤ)) : GaussianInt)] at h
  exact h

private lemma gcp_isUnitMod4d_star {d : ℕ} (z : GaussianInt) :
    IsUnitMod4d d (star z) ↔ IsUnitMod4d d z :=
  ⟨gcp_isUnitMod4d_star_aux z,
    fun h => gcp_isUnitMod4d_star_aux (star z) (by rw [star_star]; exact h)⟩

end NormAux

/-! ## A proper non-unit divisor of the modulus adapted to a non-unit `η` -/

section Divisor

/-- **A proper non-unit divisor of `M` adapted to `η`.**  If `M ≠ 0` is not invertible in the
quotient ring of `η`... precisely: if `η` is not a unit modulo `M`, then there is a divisor `c ∣ M`
of `M` which is neither `M` nor a unit, and such that `M ∣ c·η`.

If `M ∣ η` one may take the given fallback divisor `c₀`; otherwise `c := M / gcd(M,η)` works:
`gcd(M,η) ∣ η` gives `M ∣ c·η`, `gcd(M,η)` is not a unit (Bézout's identity: otherwise `η` would
be a unit modulo `M`), which gives `¬ (M ∣ c)`, and `¬ IsUnit c` is equivalent to `¬ (M ∣ η)`. -/
private lemma gcp_divisor_general {M η : GaussianInt} (hMne : M ≠ 0)
    (hη : ¬ IsUnitMod M η) {c₀ : GaussianInt} (hc₀dvd : c₀ ∣ M) (hc₀notdvd : ¬ M ∣ c₀)
    (hc₀notunit : ¬ IsUnit c₀) :
    ∃ c : GaussianInt, c ∣ M ∧ ¬ M ∣ c ∧ ¬ IsUnit c ∧ M ∣ c * η := by
  classical
  by_cases hMη : M ∣ η
  · exact ⟨c₀, hc₀dvd, hc₀notdvd, hc₀notunit, dvd_mul_of_dvd_right hMη c₀⟩
  · obtain ⟨c, hc⟩ := EuclideanDomain.gcd_dvd_left M η
    have hgnonunit : ¬ IsUnit (EuclideanDomain.gcd M η) := by
      intro hgunit
      obtain ⟨g', hg'⟩ := (isUnit_iff_exists_inv).mp hgunit
      have hbez := EuclideanDomain.gcd_eq_gcd_ab M η
      have h1 : M * (EuclideanDomain.gcdA M η * g')
          + η * (EuclideanDomain.gcdB M η * g') = 1 := by
        calc M * (EuclideanDomain.gcdA M η * g') + η * (EuclideanDomain.gcdB M η * g')
            = (M * EuclideanDomain.gcdA M η
                + η * EuclideanDomain.gcdB M η) * g' := by ring
          _ = EuclideanDomain.gcd M η * g' := by rw [← hbez]
          _ = 1 := hg'
      refine hη ⟨EuclideanDomain.gcdB M η * g', ?_⟩
      refine ⟨-(EuclideanDomain.gcdA M η * g'), ?_⟩
      have h2 : η * (EuclideanDomain.gcdB M η * g')
          = 1 - M * (EuclideanDomain.gcdA M η * g') :=
        eq_sub_of_add_eq (by rw [add_comm]; exact h1)
      rw [h2]
      ring
    refine ⟨c, ?_, ?_, ?_, ?_⟩
    · refine ⟨EuclideanDomain.gcd M η, ?_⟩
      conv_lhs => rw [hc]
      ring
    · intro hMc
      obtain ⟨h, hh⟩ := hMc
      have hcancel : (1 : GaussianInt) = EuclideanDomain.gcd M η * h := by
        have h1 : M * 1 = M * (EuclideanDomain.gcd M η * h) := by
          calc M * 1 = M := by rw [mul_one]
            _ = EuclideanDomain.gcd M η * c := hc
            _ = EuclideanDomain.gcd M η * (M * h) := by rw [hh]
            _ = M * (EuclideanDomain.gcd M η * h) := by ring
        exact mul_left_cancel₀ hMne h1
      exact hgnonunit ((isUnit_iff_exists_inv).mpr ⟨h, hcancel.symm⟩)
    · intro hcunit
      apply hMη
      obtain ⟨c', hc'⟩ := (isUnit_iff_exists_inv).mp hcunit
      obtain ⟨η', hη'⟩ := EuclideanDomain.gcd_dvd_right M η
      have hgM : EuclideanDomain.gcd M η = M * c' := by
        calc EuclideanDomain.gcd M η = EuclideanDomain.gcd M η * 1 := by rw [mul_one]
          _ = EuclideanDomain.gcd M η * (c * c') := by rw [hc']
          _ = (EuclideanDomain.gcd M η * c) * c' := by ring
          _ = M * c' := by rw [← hc]
      refine ⟨c' * η', ?_⟩
      calc η = EuclideanDomain.gcd M η * η' := hη'
        _ = (M * c') * η' := by rw [hgM]
        _ = M * (c' * η') := by ring
    · obtain ⟨η', hη'⟩ := EuclideanDomain.gcd_dvd_right M η
      refine ⟨η', ?_⟩
      calc c * η = c * (EuclideanDomain.gcd M η * η') := by
            conv_lhs => rw [hη']
        _ = (EuclideanDomain.gcd M η * c) * η' := by ring
        _ = M * η' := by rw [← hc]

/-- The divisor lemma at the modulus `M = 4D`: a non-unit `η` modulo `4D` admits a divisor
`c ∣ 4D` which is neither `4D` nor a unit of `ℤ[i]`, with `4D ∣ c·η`. -/
private lemma gcp_divisorOfNotUnitMod {D : ℕ} (hD : 1 ≤ D) (η : GaussianInt)
    (hη : ¬ IsUnitMod4d D η) :
    ∃ c : GaussianInt,
      c ∣ ((((4 * D : ℕ) : ℤ)) : GaussianInt) ∧
      ¬ ((((4 * D : ℕ) : ℤ)) : GaussianInt) ∣ c ∧
      ¬ IsUnit c ∧
      ((((4 * D : ℕ) : ℤ)) : GaussianInt) ∣ c * η := by
  have hη' : ¬ IsUnitMod ((((4 * D : ℕ) : ℤ)) : GaussianInt) η := hη
  exact gcp_divisor_general (gcp_fourD_ne_zero hD) hη'
    (c₀ := (((2 * D : ℕ) : ℤ) : GaussianInt)) ⟨2, by push_cast; ring⟩
    (gcp_not_dvd_twoD hD) (gcp_not_isUnit_twoD hD)

end Divisor

/-! ## Vanishing of the Fourier transform at a non-unit class -/

section Vanishing

variable {d : ℕ} [NeZero (4 * d)]

/-- **`Fhat` vanishes at a class admitting a "witness".**  If there is a unit `z` modulo `4d`, with
`4d ∣ (z-1)·ξ̄` for a Gaussian integer `ξ` representing the class `θ` (`θ = gOfZI d ξ`), and
`χ z ≠ 1`, then the finite Fourier transform of `FR d χ` at `θ` vanishes.

Indeed the change of variables `x ↦ x·z` permutes `ℤ[i]/(4d)` (`z` is a unit), multiplies the
weight by `χ(z)` and leaves the additive character `x ↦ e(Re(x ξ̄)/4d)` unchanged, because
`4d ∣ ξ̄(z-1)`. -/
private lemma gcp_Fhat_eq_zero_of_witness {χ : GaussianInt → ℂ}
    (hchi : Work.FITop3.IsCharMod4d d χ) {ξ : GaussianInt}
    (h : ∃ z : GaussianInt, IsUnitMod4d d z ∧
      ((((4 * d : ℕ) : ℤ)) : GaussianInt) ∣ (z - 1) * star ξ ∧ χ z ≠ 1) :
    Fhat d χ (gOfZI d ξ) = 0 := by
  classical
  obtain ⟨z, hzunit, hzdvd, hzchi⟩ := h
  have hw : IsUnitR d (gOfZI d z) := isUnitR_gOfZI_of_isUnitMod4d d hzunit
  have hchiw : chiR d χ (gOfZI d z) ≠ 1 := by
    rw [chiR_gOfZI d hchi z]; exact hzchi
  -- the additive character is invariant under the shift
  have hpair : gmul d (gOfZI d z) (gconj d (gOfZI d ξ)) = gconj d (gOfZI d ξ) := by
    have hsplit : gOfZI d z = gone d + gOfZI d (z - 1) := by
      rw [gcp_gOfZI_sub, gOfZI_one]
      abel
    have hzero : gmul d (gOfZI d (z - 1)) (gconj d (gOfZI d ξ)) = 0 := by
      rw [← gcp_gOfZI_star ξ, ← gOfZI_mul]
      exact gcp_gOfZI_eq_zero_of_dvd hzdvd
    have hgain : gmul d (gOfZI d z) (gconj d (gOfZI d ξ)) - gconj d (gOfZI d ξ)
        = gmul d (gOfZI d (z - 1)) (gconj d (gOfZI d ξ)) := by
      rw [hsplit, gcp_gmul_add_left, gmul_gone_left]
      ring
    exact sub_eq_zero.mp (hgain.trans hzero)
  have hshift : ∀ x : ZMod (4 * d) × ZMod (4 * d),
      pairG d (gOfZI d ξ) (gmul d x (gOfZI d z)) = pairG d (gOfZI d ξ) x := by
    intro x
    rw [pairG_eq_fst_gmul, pairG_eq_fst_gmul, gmul_assoc, hpair]
  -- the substitution
  have hperm : (∑ x, FR d χ x * ZMod.stdAddChar (pairG d (gOfZI d ξ) x))
      = ∑ x, FR d χ (gmul d x (gOfZI d z))
          * ZMod.stdAddChar (pairG d (gOfZI d ξ) (gmul d x (gOfZI d z))) :=
    (gcp_sum_gmul_right_unit (gOfZI d z) hw
      (fun x => FR d χ x * ZMod.stdAddChar (pairG d (gOfZI d ξ) x))).symm
  have key : Fhat d χ (gOfZI d ξ) = chiR d χ (gOfZI d z) * Fhat d χ (gOfZI d ξ) := by
    calc Fhat d χ (gOfZI d ξ)
        = ∑ x, FR d χ x * ZMod.stdAddChar (pairG d (gOfZI d ξ) x) := rfl
      _ = ∑ x, FR d χ (gmul d x (gOfZI d z))
            * ZMod.stdAddChar (pairG d (gOfZI d ξ) (gmul d x (gOfZI d z))) := hperm
      _ = ∑ x, chiR d χ (gOfZI d z)
            * (FR d χ x * ZMod.stdAddChar (pairG d (gOfZI d ξ) x)) := by
          refine Finset.sum_congr rfl (fun x _ => ?_)
          rw [hshift x, FR_mul_unit hchi hw x]
          ring
      _ = chiR d χ (gOfZI d z) * ∑ x, FR d χ x * ZMod.stdAddChar (pairG d (gOfZI d ξ) x) := by
          rw [Finset.mul_sum]
      _ = chiR d χ (gOfZI d z) * Fhat d χ (gOfZI d ξ) := rfl
  have h0 : (1 - chiR d χ (gOfZI d z)) * Fhat d χ (gOfZI d ξ) = 0 := by
    have h3 : (1 - chiR d χ (gOfZI d z)) * Fhat d χ (gOfZI d ξ)
        = Fhat d χ (gOfZI d ξ) - chiR d χ (gOfZI d z) * Fhat d χ (gOfZI d ξ) := by
      rw [sub_mul, one_mul]
    exact h3.trans (sub_eq_zero.mpr key)
  rcases mul_eq_zero.mp h0 with h | h
  · exact absurd h (sub_ne_zero.mpr (Ne.symm hchiw))
  · exact h

/-- **The witness of primitivity.**  For every class `θ` that is not a unit modulo `4D` there is a
Gaussian integer `z` which is a unit modulo `4D`, is `1` modulo a suitable divisor of `4D`, has
`4D ∣ (z-1)·ξ̄` (where `ξ` represents `θ`), and satisfies `χ z ≠ 1`.

Indeed, `IsPrimitiveUnitAt` applied to the divisor `c` produced by `gcp_divisorOfNotUnitMod` for
`η = ξ̄` supplies such a `z`, and `M ∣ c·ξ̄` together with `c ∣ z - 1` gives `M ∣ (z-1)·ξ̄`. -/
private lemma gcp_witness_of_not_isUnitR {D : ℕ} [NeZero (4 * D)] (hD : 1 ≤ D)
    {χ : GaussianInt → ℂ}
    (hprim : IsPrimitiveUnitAt ((((4 * D : ℕ) : ℤ)) : GaussianInt) χ)
    {θ : ZMod (4 * D) × ZMod (4 * D)} (hθ : ¬ IsUnitR D θ) :
    ∃ z : GaussianInt, IsUnitMod4d D z ∧
      ((((4 * D : ℕ) : ℤ)) : GaussianInt) ∣ (z - 1) * star (zOfG D θ) ∧ χ z ≠ 1 := by
  have hξ : ¬ IsUnitMod4d D (zOfG D θ) := fun h => hθ (IsUnitR_iff_IsUnitMod4d.mpr h)
  have hη : ¬ IsUnitMod4d D (star (zOfG D θ)) :=
    fun h => hξ ((gcp_isUnitMod4d_star (zOfG D θ)).mp h)
  obtain ⟨c, hcdvd, hcnotdvd, hcnotunit, hcdvdη⟩ := gcp_divisorOfNotUnitMod hD _ hη
  obtain ⟨z, hzunit, hzsub, hzchi⟩ := hprim c hcdvd hcnotdvd hcnotunit
  refine ⟨z, hzunit, ?_, hzchi⟩
  obtain ⟨m, hm⟩ := hzsub
  obtain ⟨k, hk⟩ := hcdvdη
  refine ⟨k * m, ?_⟩
  calc (z - 1) * star (zOfG D θ) = (c * star (zOfG D θ)) * m := by rw [hm]; ring
    _ = ((((4 * D : ℕ) : ℤ)) : GaussianInt) * k * m := by rw [hk]
    _ = ((((4 * D : ℕ) : ℤ)) : GaussianInt) * (k * m) := by ring

end Vanishing

/-! ## Parseval, and the Gauss sum of a primitive character -/

section Parseval

variable {d : ℕ} [NeZero (4 * d)]

/-- `z * star z = 1` for a complex number of modulus `1`. -/
private lemma gcp_mul_star_eq_one_of_norm_eq_one {z : ℂ} (hz : ‖z‖ = 1) : z * star z = 1 := by
  rw [show star z = (starRingEnd ℂ) z from rfl, Complex.mul_conj, Complex.normSq_eq_norm_sq, hz]
  norm_num

/-- Every unit has squared modulus `1` under `χ`. -/
private lemma gcp_chiR_mul_star_eq_one {χ : GaussianInt → ℂ}
    (hchi : Work.FITop3.IsCharMod4d d χ) {x : ZMod (4 * d) × ZMod (4 * d)} (hx : IsUnitR d x) :
    chiR d χ x * star (chiR d χ x) = 1 :=
  gcp_mul_star_eq_one_of_norm_eq_one (norm_chiR_eq_one_of_unit hchi hx)

/-- **Parseval for the Gauss sum.**  If every Fourier coefficient of `FR d χ` at a non-unit class
vanishes, then the Gauss sum of `χ` is maximal. -/
private lemma gcp_gaussSumNormSqOfVanishing {D : ℕ} [NeZero (4 * D)] (χ : GaussianInt → ℂ)
    (hchi : IsCharMod4dStrict D χ)
    (hvan : ∀ θ : ZMod (4 * D) × ZMod (4 * D), ¬ IsUnitR D θ → Fhat D χ θ = 0) :
    ‖gaussSum D χ 1‖ ^ 2 = (((16 * D ^ 2 : ℕ)) : ℝ) := by
  classical
  have hchiC : Work.FITop3.IsCharMod4d D χ := hchi.1
  -- the squared norms of the weight `FR`
  have hFR : ∀ y : ZMod (4 * D) × ZMod (4 * D),
      FR D χ y * star (FR D χ y) = (if IsUnitR D y then (1 : ℂ) else 0) := by
    intro y
    by_cases hy : IsUnitR D y
    · rw [FR, if_pos (isOddR_of_IsUnitR hy), if_pos hy]
      exact gcp_chiR_mul_star_eq_one hchiC hy
    · rw [if_neg hy]
      have hy0 : FR D χ y = 0 := by
        rw [FR]
        by_cases ho : isOddR D y
        · rw [if_pos ho, chiR_eq_zero_of_not_unit hchi hy]
        · rw [if_neg ho]
      rw [hy0, zero_mul]
  -- Parseval
  have hparse : (∑ θ : ZMod (4 * D) × ZMod (4 * D), Fhat D χ θ * star (Fhat D χ θ))
      = (((4 * D : ℕ) : ℂ) * ((4 * D : ℕ) : ℂ))
        * ∑ y : ZMod (4 * D) × ZMod (4 * D), (if IsUnitR D y then (1 : ℂ) else 0) := by
    have h := parseval (d := D) (fun y => FR D χ y)
    rw [Finset.sum_congr rfl (fun y _ => hFR y)] at h
    exact h
  -- at a unit the transform is `G` up to a unit character value
  have hpt : ∀ θ : ZMod (4 * D) × ZMod (4 * D),
      Fhat D χ θ * star (Fhat D χ θ)
        = (if IsUnitR D θ
            then Fhat D χ (gone D) * star (Fhat D χ (gone D)) else 0) := by
    intro θ
    by_cases hθ : IsUnitR D θ
    · rw [if_pos hθ]
      obtain ⟨v, hv⟩ := exists_gmul_gconj_eq_gone hθ
      have hvunit : IsUnitR D v := ⟨gconj D θ, hv⟩
      have hv1 : chiR D χ v * star (chiR D χ v) = 1 := gcp_chiR_mul_star_eq_one hchiC hvunit
      calc Fhat D χ θ * star (Fhat D χ θ)
          = (chiR D χ v * Fhat D χ (gone D))
              * star (chiR D χ v * Fhat D χ (gone D)) := by
            rw [Fhat_eq_of_gmul_eq_one hchiC hv]
        _ = (chiR D χ v * star (chiR D χ v))
              * (Fhat D χ (gone D) * star (Fhat D χ (gone D))) := by
            rw [star_mul]; ring
        _ = Fhat D χ (gone D) * star (Fhat D χ (gone D)) := by rw [hv1, one_mul]
    · rw [if_neg hθ, hvan θ hθ, zero_mul]
  have hsum_units : (∑ θ : ZMod (4 * D) × ZMod (4 * D), Fhat D χ θ * star (Fhat D χ θ))
      = (Fhat D χ (gone D) * star (Fhat D χ (gone D)))
        * ∑ y : ZMod (4 * D) × ZMod (4 * D), (if IsUnitR D y then (1 : ℂ) else 0) := by
    rw [Finset.sum_congr rfl (fun θ _ => hpt θ), Finset.mul_sum]
    refine Finset.sum_congr rfl (fun θ _ => ?_)
    by_cases hθ : IsUnitR D θ <;> simp [hθ]
  -- the number of units is nonzero
  have hSne : (∑ y : ZMod (4 * D) × ZMod (4 * D),
      (if IsUnitR D y then (1 : ℂ) else 0)) ≠ 0 := by
    rw [← Finset.sum_filter]
    have hmem : gone D ∈ Finset.univ.filter
        (fun y : ZMod (4 * D) × ZMod (4 * D) => IsUnitR D y) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨gone D, gmul_gone_right (gone D)⟩
    have hpos : 0 < (Finset.univ.filter
        (fun y : ZMod (4 * D) × ZMod (4 * D) => IsUnitR D y)).card :=
      Finset.card_pos.mpr ⟨gone D, hmem⟩
    rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    exact Nat.cast_ne_zero.mpr (ne_of_gt hpos)
  -- cancel
  have hmain : (Fhat D χ (gone D) * star (Fhat D χ (gone D)))
      * (∑ y : ZMod (4 * D) × ZMod (4 * D), (if IsUnitR D y then (1 : ℂ) else 0))
      = (((4 * D : ℕ) : ℂ) * ((4 * D : ℕ) : ℂ))
        * ∑ y : ZMod (4 * D) × ZMod (4 * D), (if IsUnitR D y then (1 : ℂ) else 0) := by
    rw [← hsum_units, hparse]
  have hGG : Fhat D χ (gone D) * star (Fhat D χ (gone D))
      = (((4 * D : ℕ) : ℂ) * ((4 * D : ℕ) : ℂ)) :=
    mul_right_cancel₀ hSne hmain
  have hg : Fhat D χ (gone D) = gaussSum D χ 1 := by
    rw [gaussSum_eq_Fhat χ 1, gOfZI_one]
  rw [hg] at hGG
  have h1 : gaussSum D χ 1 * star (gaussSum D χ 1) = (((16 * D ^ 2 : ℕ)) : ℂ) := by
    rw [hGG]; push_cast; ring
  have h2 : (((‖gaussSum D χ 1‖ ^ 2 : ℝ)) : ℂ) = gaussSum D χ 1 * star (gaussSum D χ 1) := by
    rw [show star (gaussSum D χ 1) = (starRingEnd ℂ) (gaussSum D χ 1) from rfl,
      Complex.mul_conj, Complex.normSq_eq_norm_sq]
  refine Complex.ofReal_inj.mp ?_
  rw [Complex.ofReal_natCast]
  exact h2.trans h1

end Parseval

/-- **The classical Gauss-sum criterion from primitivity at the conductor.**

If `χ₀` is a strict character modulo `4D` which does not factor through `(ℤ[i]/M')^*` for any
non-unit proper divisor `M' ∣ (4D)` (witnessed by *units*, `IsPrimitiveUnitAt (4D) χ₀`), then its
Gauss sum has the maximal size

  `‖gaussSum D χ₀ 1‖² = 16·D² = N(4D)`.

This is the (classical, Parseval/DFT) converse of `IsPrimitive4d`, and it is the missing link that
lets `HeckeCompletionAll`/`heckeFE_primitive_full` be applied to the primitive *partner* `χ₀` of a
strict character whose Hecke conductor is divisible by `4` (the "even conductor" case of the
conductor-normalised functional equation). -/
theorem gaussCriterionOfPrimitiveAt (D : ℕ) (hD : 1 ≤ D) (χ₀ : GaussianInt → ℂ)
    (hchi : Work.FIArea5.S16Hecke.IsCharMod4dStrict D χ₀)
    (hprim : IsPrimitiveUnitAt (((4 * D : ℕ) : ℤ) : GaussianInt) χ₀) :
    ‖Work.FIArea5.S16Hecke.gaussSum D χ₀ 1‖ ^ 2 = (((16 * D ^ 2 : ℕ)) : ℝ) := by
  haveI : NeZero (4 * D) := ⟨by omega⟩
  refine gcp_gaussSumNormSqOfVanishing χ₀ hchi (fun θ hθ => ?_)
  rw [show θ = gOfZI D (zOfG D θ) from (gOfZI_zOfG θ).symm]
  exact gcp_Fhat_eq_zero_of_witness hchi.1 (gcp_witness_of_not_isUnitR hD hprim hθ)

end

end Work.FIArea6Hecke.R
