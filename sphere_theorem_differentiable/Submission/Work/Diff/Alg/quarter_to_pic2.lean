import Mathlib
import Submission.Diff.Interfaces
import Submission.Work.Diff.Alg.q2p_defs
import Submission.Work.Diff.Alg.q2p_berger
import Submission.Work.Diff.Alg.q2p_berger_orth
import Submission.Work.Diff.Alg.q2p_transform
import Submission.Work.Diff.Alg.q2p_reduce
import Submission.Work.Diff.Alg.q2p_minsec
import Submission.Work.Diff.Alg.q2p_secK_Iso
import Submission.Work.Diff.Alg.q2p_EFun_Iso
import Submission.Work.Diff.Alg.q2p_diag
import Submission.Work.Diff.Alg.q2p_estimate

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# CONTRACT A0: strictly quarter-pinched algebraic curvature tensors lie in the interior of `PIC2`

Brendle–Schoen, *Manifolds with 1/4-pinched curvature are space forms*, Cor. 22 (with Prop. 21):
if all sectional curvatures of an algebraic curvature tensor `R` lie in `[1,4]`, then `R` has
nonnegative isotropic curvature.  We prove the slightly stronger statement with an explicit
margin: if `c < secK R u v` and `secK R u v ≤ 4 c` for all orthonormal pairs `u,v`, then
`InPIC2 (R - ε • Iso n)` for some `ε > 0`.

Route.  Write `E_R(x,y,z,w) = R(x,z,x,z)+R(x,w,x,w)+R(y,z,y,z)+R(y,w,y,w)-2R(x,y,z,w)`
(`EFun`), which is the isotropic curvature of the complex pair `ζ = x+iy`, `η = z+iw`.
* `EFunC` is a Hermitian form in the pair: changing the pair by `A ∈ GL(2,ℂ)` scales the value
  by `|det A|²` (`q2p_transform`).
* Any pair can be brought, by such a change of basis, to a position in which the four real vectors
  `Re ζ, Im ζ, Re η, Im η` are mutually orthogonal (`q2p_reduce`); the dependent case is degenerate.
* On a mutually orthogonal four-tuple the value is bounded below by `((4a-b)/3)` times the value
  for the round sphere (`q2p_diag` + `q2p_berger_orth` + `q2p_estimate`), which is the
  classical Berger inequality plus the AM–GM estimate.
* The uniform gap `a > c` comes from compactness of the set of orthonormal pairs (`q2p_minsec`).
-/

namespace Work.Diff.Alg.Q2P

open Submission.Diff.Alg

variable {n : ℕ}

/-- Linearity of `R4` in the tensor argument. -/
theorem q2pMain_R4_sub_smul (R S : Curv4 n) (t : ℝ) (a b c d : Fin n → ℝ) :
    R4 (R - t • S) a b c d = R4 R a b c d - t * R4 S a b c d := by
  have key : ∀ i j k l : Fin n,
      (R i j k l - t * S i j k l) * a i * b j * c k * d l
        = R i j k l * a i * b j * c k * d l - t * (S i j k l * a i * b j * c k * d l) := by
    intro i j k l; ring
  simp only [R4, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, key]
  simp only [Finset.sum_sub_distrib, Finset.mul_sum]

/-- Linearity of `EFun` in the tensor argument. -/
theorem q2pMain_EFun_sub_smul (R : Curv4 n) (t : ℝ) (x y z w : Fin n → ℝ) :
    EFun (R - t • Iso n) x y z w = EFun R x y z w - t * EFun (Iso n) x y z w := by
  simp only [EFun]
  rw [q2pMain_R4_sub_smul, q2pMain_R4_sub_smul, q2pMain_R4_sub_smul, q2pMain_R4_sub_smul,
    q2pMain_R4_sub_smul]
  ring

/-- `EFunC` vanishes when one of the two vectors is zero. -/
theorem q2pMain_EFunC_zero_left (R : Curv4 n) (w : Fin n → ℂ) : EFunC R 0 w = 0 := by
  simp only [EFunC, EFun]
  simp only [cRe, cIm, Pi.zero_apply, Complex.zero_re, Complex.zero_im, R4]
  simp

/-- `comb 1 0` is the projection on the first vector. -/
@[simp] theorem q2pMain_comb_one_zero (z w : Fin n → ℂ) : comb 1 0 z w = z := by
  ext i; simp [comb]

/-- A pair of the form `(z, t z)` is isotropic-flat. -/
theorem q2pMain_EFunC_dep (R : Curv4 n) (hR : IsAlgCurv R) (z : Fin n → ℂ) (t : ℂ) :
    EFunC R z (comb t 0 z z) = 0 := by
  have h := q2p_transform R hR z z 1 0 t 0
  simpa using h

theorem q2pMain_cRe_of (x y : Fin n → ℝ) :
    cRe (fun i => (x i : ℂ) + (y i : ℂ) * Complex.I) = x := by
  ext i; simp [cRe]

theorem q2pMain_cIm_of (x y : Fin n → ℝ) :
    cIm (fun i => (x i : ℂ) + (y i : ℂ) * Complex.I) = y := by
  ext i; simp [cIm]

/-- `Iso n` is an algebraic curvature tensor (the curvature tensor of the unit round sphere). -/
theorem Iso_isAlgCurv (n : ℕ) : IsAlgCurv (Iso n) :=
  ⟨fun i j k l => by
     simp only [Iso]
     by_cases h1 : i = k <;> by_cases h2 : i = l <;> by_cases h3 : j = k <;>
       by_cases h4 : j = l <;> by_cases h5 : i = j <;> by_cases h6 : k = l <;>
       simp_all [eq_comm],
   fun i j k l => by
     simp only [Iso]
     by_cases h1 : i = k <;> by_cases h2 : i = l <;> by_cases h3 : j = k <;>
       by_cases h4 : j = l <;> by_cases h5 : i = j <;> by_cases h6 : k = l <;>
       simp_all [eq_comm],
   fun i j k l => by
     simp only [Iso]
     by_cases h1 : i = k <;> by_cases h2 : i = l <;> by_cases h3 : j = k <;>
       by_cases h4 : j = l <;> by_cases h5 : i = j <;> by_cases h6 : k = l <;>
       simp_all [eq_comm]⟩

/-- The main pointwise inequality: if the sectional curvatures of `R` lie in `[a,b]` (with
`a ≤ b`), then for mutually orthogonal `x,y,z,w` the isotropic curvature of `R` dominates
`(4a-b)/3` times that of the round sphere. -/
theorem q2pMain_EFun_ge_Iso (R : Curv4 n) (hR : IsAlgCurv R) {a b : ℝ} (hab : a ≤ b)
    (hsec : ∀ u v : Fin n → ℝ, IsONPair u v → a ≤ secK R u v ∧ secK R u v ≤ b)
    (x y z w : Fin n → ℝ) :
    ((4 * a - b) / 3) * EFun (Iso n) x y z w ≤ EFun R x y z w := by
  set ζ : Fin n → ℂ := fun i => (x i : ℂ) + (y i : ℂ) * Complex.I with hζ
  set η : Fin n → ℂ := fun i => (z i : ℂ) + (w i : ℂ) * Complex.I with hη
  have hζre : cRe ζ = x := by rw [hζ]; exact q2pMain_cRe_of x y
  have hζim : cIm ζ = y := by rw [hζ]; exact q2pMain_cIm_of x y
  have hηre : cRe η = z := by rw [hη]; exact q2pMain_cRe_of z w
  have hηim : cIm η = w := by rw [hη]; exact q2pMain_cIm_of z w
  have hEF : EFunC R ζ η = EFun R x y z w := by
    simp only [EFunC, hζre, hζim, hηre, hηim]
  have hEFi : EFunC (Iso n) ζ η = EFun (Iso n) x y z w := by
    simp only [EFunC, hζre, hζim, hηre, hηim]
  by_cases hdep : ∃ p q : ℂ, (∀ i, p * ζ i + q * η i = 0) ∧ ¬ (p = 0 ∧ q = 0)
  · obtain ⟨p, q, hrel, hpq⟩ := hdep
    have hpq' : p ≠ 0 ∨ q ≠ 0 := by
      rcases Classical.em (p = 0) with hp | hp
      · right; intro hq0; exact hpq ⟨hp, hq0⟩
      · left; exact hp
    have hη_of : η = comb (-(p / q)) 0 ζ ζ → EFunC R ζ η = 0 := by
      intro hηeq
      rw [hηeq]; exact q2pMain_EFunC_dep R hR ζ (-(p / q))
    have hη_of' : η = comb (-(p / q)) 0 ζ ζ → EFunC (Iso n) ζ η = 0 := by
      intro hηeq
      rw [hηeq]; exact q2pMain_EFunC_dep (Iso n) (Iso_isAlgCurv n) ζ (-(p / q))
    have hζ0_of : p ≠ 0 → q = 0 → ζ = 0 := by
      intro hp hq
      ext i
      have hi := hrel i
      rw [hq, zero_mul, add_zero] at hi
      exact (mul_eq_zero.mp hi).resolve_left hp
    have hηeq_of : q ≠ 0 → η = comb (-(p / q)) 0 ζ ζ := by
      intro hq
      ext i
      have hi := hrel i
      have h1 : η i = -(p / q) * ζ i := by
        have key : q * η i = q * (-(p / q) * ζ i) := by
          rw [show q * (-(p / q) * ζ i) = -(p * ζ i) from by
            rw [neg_mul, mul_neg, ← mul_assoc, mul_div_cancel₀ p hq]]
          linear_combination hi
        exact mul_left_cancel₀ hq key
      simpa [comb] using h1
    have hz : EFunC R ζ η = 0 := by
      by_cases hq : q = 0
      · have hp : p ≠ 0 := by
          rcases hpq' with hp | hq0
          · exact hp
          · exact absurd hq hq0
        rw [hζ0_of hp hq]; exact q2pMain_EFunC_zero_left R η
      · exact hη_of (hηeq_of hq)
    have hzI : EFunC (Iso n) ζ η = 0 := by
      by_cases hq : q = 0
      · have hp : p ≠ 0 := by
          rcases hpq' with hp | hq0
          · exact hp
          · exact absurd hq hq0
        rw [hζ0_of hp hq]; exact q2pMain_EFunC_zero_left (Iso n) η
      · exact hη_of' (hηeq_of hq)
    rw [← hEF, ← hEFi, hz, hzI]
    simp
  · have hind : ∀ p q : ℂ, (∀ i, p * ζ i + q * η i = 0) → p = 0 ∧ q = 0 := by
      intro p q hpq
      by_contra hc
      exact hdep ⟨p, q, hpq, hc⟩
    obtain ⟨p, q, r, s, hdet, h1, h2, h3, h4⟩ := q2p_reduce ζ η hind
    set ζ' : Fin n → ℂ := comb p q ζ η with hζ'
    set η' : Fin n → ℂ := comb r s ζ η with hη'
    have h1' : cHerm ζ' η' = 0 := by rw [hζ', hη']; exact h1
    have h2' : cBil ζ' η' = 0 := by rw [hζ', hη']; exact h2
    have h3' : (cBil ζ' ζ').im = 0 := by rw [hζ']; exact h3
    have h4' : (cBil η' η').im = 0 := by rw [hη']; exact h4
    have hcr := (cross_iff ζ' η').mp ⟨h1', h2'⟩
    have hxy : dot (cRe ζ') (cIm ζ') = 0 := by
      have h := cBil_self_im ζ'
      rw [h3'] at h; linarith
    have hzw : dot (cRe η') (cIm η') = 0 := by
      have h := cBil_self_im η'
      rw [h4'] at h; linarith
    have horth : PairwiseOrth (cRe ζ') (cIm ζ') (cRe η') (cIm η') :=
      ⟨hxy, hcr.1, hcr.2.2.2, hcr.2.2.1, hcr.2.1, hzw⟩
    have hσ : 0 < Complex.normSq (p * s - q * r) := Complex.normSq_pos.mpr hdet
    have hF : EFun R (cRe ζ') (cIm ζ') (cRe η') (cIm η')
        = Complex.normSq (p * s - q * r) * EFun R x y z w := by
      have h := q2p_transform R hR ζ η p q r s
      rw [hEF] at h
      have he : EFunC R ζ' η' = EFun R (cRe ζ') (cIm ζ') (cRe η') (cIm η') := rfl
      rw [he] at h
      exact h
    have hJ : EFun (Iso n) (cRe ζ') (cIm ζ') (cRe η') (cIm η')
        = Complex.normSq (p * s - q * r) * EFun (Iso n) x y z w := by
      have h := q2p_transform (Iso n) (Iso_isAlgCurv n) ζ η p q r s
      rw [hEFi] at h
      have he : EFunC (Iso n) ζ' η'
        = EFun (Iso n) (cRe ζ') (cIm ζ') (cRe η') (cIm η') := rfl
      rw [he] at h
      exact h
    have hPI : EFun (Iso n) (cRe ζ') (cIm ζ') (cRe η') (cIm η')
        = (dot (cRe ζ') (cRe ζ') + dot (cIm ζ') (cIm ζ')) *
          (dot (cRe η') (cRe η') + dot (cIm η') (cIm η')) := q2p_EFun_Iso horth
    have hest := q2p_estimate R hab
      (fun u v huv => q2p_diag R (fun u v h => (hsec u v h).1) huv)
      (fun x y z w h => q2p_berger_orth R hR a b hsec h) horth
    have hm : ((4 * a - b) / 3) * EFun (Iso n) (cRe ζ') (cIm ζ') (cRe η') (cIm η')
        ≤ EFun R (cRe ζ') (cIm ζ') (cRe η') (cIm η') := by
      rw [hPI]; exact hest
    have hkey : Complex.normSq (p * s - q * r) * (((4 * a - b) / 3) * EFun (Iso n) x y z w)
        ≤ Complex.normSq (p * s - q * r) * EFun R x y z w := by
      calc Complex.normSq (p * s - q * r) * (((4 * a - b) / 3) * EFun (Iso n) x y z w)
          = ((4 * a - b) / 3) * (Complex.normSq (p * s - q * r) * EFun (Iso n) x y z w) := by
            ring
        _ = ((4 * a - b) / 3) * EFun (Iso n) (cRe ζ') (cIm ζ') (cRe η') (cIm η') := by
            rw [hJ]
        _ ≤ Complex.normSq (p * s - q * r) * EFun R x y z w := by
            rw [← hF]; exact hm
    exact le_of_mul_le_mul_left hkey hσ

end Work.Diff.Alg.Q2P

namespace Work.Diff.Alg

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

/-- CONTRACT A0: strictly quarter-pinched algebraic curvature tensors lie in the interior of
`PIC2`. -/
theorem quarter_to_pic2 (n : ℕ) : QuarterToPIC2 n := by
  intro R hR c hc hpinch
  obtain ⟨a₀, ha₀, ha₀le⟩ := q2p_minsec R c (fun u v h => (hpinch u v h).1)
  set a := min a₀ (4 * c) with ha_def
  have hagt : c < a := lt_min ha₀ (by linarith)
  have hale : ∀ u v : Fin n → ℝ, IsONPair u v → a ≤ secK R u v :=
    fun u v h => le_trans (min_le_left _ _) (ha₀le u v h)
  have hab : a ≤ 4 * c := min_le_right _ _
  have hsec : ∀ u v : Fin n → ℝ, IsONPair u v → a ≤ secK R u v ∧ secK R u v ≤ 4 * c :=
    fun u v h => ⟨hale u v h, (hpinch u v h).2⟩
  have hκ : 0 < (4 * a - 4 * c) / 3 := by linarith
  refine ⟨(4 * a - 4 * c) / 3, hκ, ?_⟩
  rw [Q2P.inPIC2_iff]
  intro x y z w
  have hmain := Q2P.q2pMain_EFun_ge_Iso R hR (a := a) (b := 4 * c) hab hsec x y z w
  rw [Q2P.q2pMain_EFun_sub_smul]
  linarith [hmain]

end Work.Diff.Alg
