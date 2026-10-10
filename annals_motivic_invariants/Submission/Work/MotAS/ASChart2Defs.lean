import Mathlib
import Submission.Work.MotAS.AK
import Submission.Work.MotAS.CensusAS2
import Submission.Work.MotAS.CensusASFalse
import Submission.Work.MotAS.ASChartGeo
import Submission.Work.MotAS.KleinTwScalarAS
import Submission.Work.MotV5.ASChart.Stereo
import Submission.Work.MotK.TGen.TwPoly
import Submission.Work.Reflect.PolyId

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotAS.ASChart2Defs` — the definition layer of the corrected AS chart isomorphism

This file is the `AS` (characteristic `5`) analogue of `Submission/Work/MotK/TGen/ChartDefs.lean`
for the *corrected* AS chart of `Submission/Work/MotAS/CensusAS2.lean`:

* the source hyperplane is `{v₀ = 0}` with chart vector `chart3 = ![0,X₀,X₁,X₂,1]` and normaliser
  `fwVecAS2 · 0`;
* the target hyperplane is `{ẑ₄ = 0}` with chart vector `tchart = ![1,X₀,X₁,X₂,0]` and normaliser
  `bwVecAS2 · 4`.

The two divisors of the certificate are

* `FdivAS2 a b g = GambAS2 a b g * fwVecAS2 a b g 0`   (source),
* `GdivAS2 a b g = FambAS2 a b g * bwVecAS2 a b g 4`   (target),

and this file provides the two `K`-algebra homomorphisms

* `Phi0AS2 a b g = aeval (psiAS2 a b g) : A →ₐ[K] A[1/GdivAS2]`, `psiAS2 j = ǧ_{j+1}/ǧ₄`
  (pullback of the inverse chart map `χ = π_p ∘ R^AS`), and
* `Psi0AS2 a b g = aeval (phiAS2 a b g) : A →ₐ[K] A[1/FdivAS2]`, `phiAS2 j = f̂_{j+1}/f̂₀`
  (pullback of the forward chart map `f = P^AS ∘ Stereo^AS`),

together with the bookkeeping lemmas that the sibling value lemmas
(`Phi0FwVecAS2`, `Psi0BwVecAS2`, `Phi0GambAS2`, `Psi0FambAS2`) use:

* the chart points `chartPt3 (psiAS2) = (1/ǧ₄) • ǧ`, `tchartPt (phiAS2) = (1/f̂₀) • f̂`;
* `fwVecAS2 · 4 = 0`, `bwVecAS2 · 0 = 0` and `kleinQAS · pAS0 = 0`;
* naturality of every AS link datum under a ring homomorphism;
* homogeneity of every AS link datum in its coordinate vector;
* `KleinFhomPiAS`: the source equation is unchanged by the projection `π_p` on the quadric.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000

namespace Work.MotAS

open MvPolynomial

variable {K : Type*} [Field K]

/-! ## The index shift and the two chart points -/

/-- The index shift `Fin 3 → Fin 5`, `j ↦ j + 1`. -/
def ch3 (j : Fin 3) : Fin 5 := ⟨j.val + 1, by omega⟩

@[simp] theorem ch3_zero : ch3 0 = 1 := rfl
@[simp] theorem ch3_one : ch3 1 = 2 := rfl
@[simp] theorem ch3_two : ch3 2 = 3 := rfl

theorem tchart_ch3 {K : Type*} [CommRing K] (j : Fin 3) :
    tchart K (ch3 j) = MvPolynomial.X j := by
  fin_cases j <;> rfl

@[simp] theorem chart3_zero {K : Type*} [CommRing K] : Work.MotK.chart3 K 0 = 0 := rfl

@[simp] theorem chart3_four {K : Type*} [CommRing K] : Work.MotK.chart3 K 4 = 1 := rfl

theorem chart3_ch3 {K : Type*} [CommRing K] (j : Fin 3) :
    Work.MotK.chart3 K (ch3 j) = MvPolynomial.X j := by
  fin_cases j <;> rfl

/-- The affine chart point `(1, z₀, z₁, z₂, 0)` of the target hyperplane `{ẑ₄ = 0}`. -/
def tchartPt {A : Type*} [CommRing A] (z : Fin 3 → A) : Fin 5 → A := ![1, z 0, z 1, z 2, 0]

@[simp] theorem tchartPt_zero {A : Type*} [CommRing A] (z : Fin 3 → A) : tchartPt z 0 = 1 := rfl
@[simp] theorem tchartPt_one {A : Type*} [CommRing A] (z : Fin 3 → A) : tchartPt z 1 = z 0 := rfl
@[simp] theorem tchartPt_two {A : Type*} [CommRing A] (z : Fin 3 → A) : tchartPt z 2 = z 1 := rfl
@[simp] theorem tchartPt_three {A : Type*} [CommRing A] (z : Fin 3 → A) : tchartPt z 3 = z 2 := rfl
@[simp] theorem tchartPt_four {A : Type*} [CommRing A] (z : Fin 3 → A) : tchartPt z 4 = 0 := rfl

/-! ## The two divisors and the two unit denominators -/

/-- `1/ǧ₄ ∈ A[1/GdivAS2]`, written as `FambAS2/(FambAS2 · bwVecAS2 4)`. -/
noncomputable def invG4AS2 (a b g : K) : Localization.Away (GdivAS2 a b g) :=
  IsLocalization.mk' (Localization.Away (GdivAS2 a b g)) (FambAS2 a b g)
    ⟨GdivAS2 a b g,
      (Submonoid.mem_powers_iff (GdivAS2 a b g) (GdivAS2 a b g)).mpr ⟨1, pow_one _⟩⟩

/-- `1/f̂₀ ∈ A[1/FdivAS2]`, written as `GambAS2/(GambAS2 · fwVecAS2 0)`. -/
noncomputable def invF0AS2 (a b g : K) : Localization.Away (FdivAS2 a b g) :=
  IsLocalization.mk' (Localization.Away (FdivAS2 a b g)) (GambAS2 a b g)
    ⟨FdivAS2 a b g,
      (Submonoid.mem_powers_iff (FdivAS2 a b g) (FdivAS2 a b g)).mpr ⟨1, pow_one _⟩⟩

theorem invG4AS2_spec (a b g : K) :
    invG4AS2 a b g
        * algebraMap (MvPolynomial (Fin 3) K) (Localization.Away (GdivAS2 a b g))
            (GdivAS2 a b g)
      = algebraMap (MvPolynomial (Fin 3) K) (Localization.Away (GdivAS2 a b g))
          (FambAS2 a b g) :=
  IsLocalization.mk'_spec _ _ _

theorem invF0AS2_spec (a b g : K) :
    invF0AS2 a b g
        * algebraMap (MvPolynomial (Fin 3) K) (Localization.Away (FdivAS2 a b g))
            (FdivAS2 a b g)
      = algebraMap (MvPolynomial (Fin 3) K) (Localization.Away (FdivAS2 a b g))
          (GambAS2 a b g) :=
  IsLocalization.mk'_spec _ _ _

/-- `1/ǧ₄ · ǧ₄ = 1` in `A[1/GdivAS2]`. -/
theorem invG4AS2_mul_bw4 (a b g : K) :
    invG4AS2 a b g
      * algebraMap (MvPolynomial (Fin 3) K) (Localization.Away (GdivAS2 a b g))
          (bwVecAS2 a b g 4)
      = 1 := by
  have hunit : IsUnit (algebraMap (MvPolynomial (Fin 3) K) (Localization.Away (GdivAS2 a b g))
      (FambAS2 a b g)) :=
    IsLocalization.Away.isUnit_of_dvd (GdivAS2 a b g) (dvd_mul_right _ _)
  have hG : algebraMap (MvPolynomial (Fin 3) K) (Localization.Away (GdivAS2 a b g))
        (GdivAS2 a b g)
      = algebraMap _ _ (FambAS2 a b g)
        * algebraMap _ _ (bwVecAS2 a b g 4) := by
    change algebraMap _ _ (FambAS2 a b g * bwVecAS2 a b g 4) = _
    rw [map_mul]
  have hs := invG4AS2_spec a b g
  rw [hG] at hs
  refine hunit.mul_left_cancel ?_
  rw [mul_one, ← mul_assoc, mul_comm (algebraMap _ _ (FambAS2 a b g)) (invG4AS2 a b g)]
  simpa only [← mul_assoc] using hs

/-- `1/f̂₀ · f̂₀ = 1` in `A[1/FdivAS2]`. -/
theorem invF0AS2_mul_fw0 (a b g : K) :
    invF0AS2 a b g
      * algebraMap (MvPolynomial (Fin 3) K) (Localization.Away (FdivAS2 a b g))
          (fwVecAS2 a b g 0)
      = 1 := by
  have hunit : IsUnit (algebraMap (MvPolynomial (Fin 3) K) (Localization.Away (FdivAS2 a b g))
      (GambAS2 a b g)) :=
    IsLocalization.Away.isUnit_of_dvd (FdivAS2 a b g) (dvd_mul_right _ _)
  have hF : algebraMap (MvPolynomial (Fin 3) K) (Localization.Away (FdivAS2 a b g))
        (FdivAS2 a b g)
      = algebraMap _ _ (GambAS2 a b g)
        * algebraMap _ _ (fwVecAS2 a b g 0) := by
    change algebraMap _ _ (linAS2 a b * sAS2 a b g * fwVecAS2 a b g 0) = _
    rw [show linAS2 a b * sAS2 a b g = GambAS2 a b g from rfl, map_mul]
  have hs := invF0AS2_spec a b g
  rw [hF] at hs
  refine hunit.mul_left_cancel ?_
  rw [mul_one, ← mul_assoc, mul_comm (algebraMap _ _ (GambAS2 a b g)) (invF0AS2 a b g)]
  simpa only [← mul_assoc] using hs

/-! ## The two `K`-algebra homomorphisms of the chart rings -/

/-- The chart coordinates of the inverse chart map `χ`, in `A[1/GdivAS2]`. -/
noncomputable def psiAS2 (a b g : K) : Fin 3 → Localization.Away (GdivAS2 a b g) :=
  ![invG4AS2 a b g * algebraMap _ _ (bwVecAS2 a b g 1),
    invG4AS2 a b g * algebraMap _ _ (bwVecAS2 a b g 2),
    invG4AS2 a b g * algebraMap _ _ (bwVecAS2 a b g 3)]

/-- The chart coordinates of the forward chart map `f`, in `A[1/FdivAS2]`. -/
noncomputable def phiAS2 (a b g : K) : Fin 3 → Localization.Away (FdivAS2 a b g) :=
  ![invF0AS2 a b g * algebraMap _ _ (fwVecAS2 a b g 1),
    invF0AS2 a b g * algebraMap _ _ (fwVecAS2 a b g 2),
    invF0AS2 a b g * algebraMap _ _ (fwVecAS2 a b g 3)]

theorem psiAS2_apply (a b g : K) (j : Fin 3) :
    psiAS2 a b g j = invG4AS2 a b g * algebraMap _ _ (bwVecAS2 a b g (ch3 j)) := by
  fin_cases j <;> simp [psiAS2, ch3]

theorem phiAS2_apply (a b g : K) (j : Fin 3) :
    phiAS2 a b g j = invF0AS2 a b g * algebraMap _ _ (fwVecAS2 a b g (ch3 j)) := by
  fin_cases j <;> simp [phiAS2, ch3]

/-- The pullback `χ^*` of the inverse chart map, as a `K`-algebra homomorphism
`A →ₐ[K] A[1/GdivAS2]`. -/
noncomputable def Phi0AS2 (a b g : K) :
    MvPolynomial (Fin 3) K →ₐ[K] Localization.Away (GdivAS2 a b g) :=
  MvPolynomial.aeval (psiAS2 a b g)

/-- The pullback `f^*` of the forward chart map, as a `K`-algebra homomorphism
`A →ₐ[K] A[1/FdivAS2]`. -/
noncomputable def Psi0AS2 (a b g : K) :
    MvPolynomial (Fin 3) K →ₐ[K] Localization.Away (FdivAS2 a b g) :=
  MvPolynomial.aeval (phiAS2 a b g)

/-! ## The quadric and the vanishing of the two chart denominators -/

/-- `ǧ₀ = 0` in the corrected chart ring. -/
theorem bwVecAS2_zero {K : Type*} [CommRing K] (a b g : K) : bwVecAS2 a b g 0 = 0 := by
  simp only [bwVecAS2, Work.MotK.kleinTwPi, Pi.sub_apply, Pi.mul_apply, pAS0_zero,
    mul_one, sub_self]

/-- `kleinQAS · pAS0 = 0`: the stereographic point `p = e₀` lies on the AS quadric. -/
theorem kleinQAS_pAS0 {K : Type*} [CommRing K] (a b : K) :
    kleinQAS (MvPolynomial.C a : MvPolynomial (Fin 3) K) (MvPolynomial.C b) (pAS0 K) = 0 := by
  have h0 : (pAS0 K) 0 = 1 := rfl
  have h1 : (pAS0 K) 1 = 0 := rfl
  have h2 : (pAS0 K) 2 = 0 := rfl
  have h3 : (pAS0 K) 3 = 0 := rfl
  have h4 : (pAS0 K) 4 = 0 := rfl
  simp only [kleinQAS, h0, h1, h2, h3, h4]
  refl_ring1

/-- **The fourth component of the forward chart map vanishes identically** (the forward map lands
in the target hyperplane `{ẑ₄ = 0}`). -/
theorem fwVecAS2_four_zero (a b g : K) : fwVecAS2 a b g 4 = 0 := by
  have hst := Work.MotV5.ASChart.kleinQAS_stereoAS (MvPolynomial.C a : MvPolynomial (Fin 3) K)
    (MvPolynomial.C b) (pAS0 K) (Work.MotK.chart3 K)
  have hp : kleinQAS (MvPolynomial.C a : MvPolynomial (Fin 3) K) (MvPolynomial.C b) (pAS0 K) = 0 :=
    kleinQAS_pAS0 a b
  have h4 : fwVecAS2 a b g 4
      = -kleinQAS (MvPolynomial.C a : MvPolynomial (Fin 3) K) (MvPolynomial.C b)
          (kleinStereoAS (MvPolynomial.C a) (MvPolynomial.C b) (pAS0 K) (Work.MotK.chart3 K)) :=
    kleinPAS_four_eq_neg (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C g) _
  rw [h4, hst, hp, mul_zero, neg_zero]

/-! ## The two chart points -/

/-- The chart point of `χ`: `(0, ǧ₁/ǧ₄, ǧ₂/ǧ₄, ǧ₃/ǧ₄, 1) = (1/ǧ₄) • ǧ`. -/
theorem chartPt3_psiAS2 (a b g : K) :
    Work.MotK.chartPt3 (psiAS2 a b g)
      = fun i => invG4AS2 a b g
          * algebraMap (MvPolynomial (Fin 3) K) (Localization.Away (GdivAS2 a b g))
              (bwVecAS2 a b g i) := by
  funext i
  fin_cases i <;>
    simp [Work.MotK.chartPt3, psiAS2, bwVecAS2_zero a b g, invG4AS2_mul_bw4 a b g]

/-- The chart point of `f`: `(1, f̂₁/f̂₀, f̂₂/f̂₀, f̂₃/f̂₀, 0) = (1/f̂₀) • f̂`. -/
theorem tchartPt_phiAS2 (a b g : K) :
    tchartPt (phiAS2 a b g)
      = fun i => invF0AS2 a b g
          * algebraMap (MvPolynomial (Fin 3) K) (Localization.Away (FdivAS2 a b g))
              (fwVecAS2 a b g i) := by
  funext i
  fin_cases i <;>
    simp [tchartPt, phiAS2, fwVecAS2_four_zero a b g, invF0AS2_mul_fw0 a b g]

theorem Phi0AS2_X (a b g : K) (j : Fin 3) : Phi0AS2 a b g (MvPolynomial.X j) = psiAS2 a b g j := by
  fin_cases j <;> simp [Phi0AS2, psiAS2, MvPolynomial.aeval_X]

theorem Psi0AS2_X (a b g : K) (j : Fin 3) : Psi0AS2 a b g (MvPolynomial.X j) = phiAS2 a b g j := by
  fin_cases j <;> simp [Psi0AS2, phiAS2, MvPolynomial.aeval_X]

theorem Phi0AS2_C (a b g : K) (c : K) :
    Phi0AS2 a b g (MvPolynomial.C c)
      = algebraMap (MvPolynomial (Fin 3) K) (Localization.Away (GdivAS2 a b g))
          (MvPolynomial.C c) := by
  rw [Phi0AS2, MvPolynomial.aeval_C, ← MvPolynomial.algebraMap_eq]
  exact IsScalarTower.algebraMap_apply K (MvPolynomial (Fin 3) K)
    (Localization.Away (GdivAS2 a b g)) c

theorem Psi0AS2_C (a b g : K) (c : K) :
    Psi0AS2 a b g (MvPolynomial.C c)
      = algebraMap (MvPolynomial (Fin 3) K) (Localization.Away (FdivAS2 a b g))
          (MvPolynomial.C c) := by
  rw [Psi0AS2, MvPolynomial.aeval_C, ← MvPolynomial.algebraMap_eq]
  exact IsScalarTower.algebraMap_apply K (MvPolynomial (Fin 3) K)
    (Localization.Away (FdivAS2 a b g)) c

theorem Phi0AS2_chart3 (a b g : K) :
    (fun i => Phi0AS2 a b g (Work.MotK.chart3 K i)) = Work.MotK.chartPt3 (psiAS2 a b g) := by
  funext i
  fin_cases i <;> simp [Work.MotK.chart3, Work.MotK.chartPt3, Phi0AS2, psiAS2,
    MvPolynomial.aeval_X]

theorem Psi0AS2_tchart (a b g : K) :
    (fun i => Psi0AS2 a b g (tchart K i)) = tchartPt (phiAS2 a b g) := by
  funext i
  fin_cases i <;> simp [tchart, tchartPt, Psi0AS2, phiAS2, MvPolynomial.aeval_X]

/-! ## Naturality of the AS link data under a ring homomorphism

Every AS coordinate is a polynomial in its arguments with integer coefficients, so it commutes with
any ring homomorphism.  (`kleinPAS`, `kleinRAS` and `kleinSecAS` are
`Work.MotAS.map_kleinPAS`, `Work.MotAS.map_kleinRAS`
(`Submission/Work/MotAS/kleinRAS_kleinPAS_mul_comm.lean`) and
`Work.MotAS.KleinTwScalarAS_map_kleinSecAS` (`Submission/Work/MotAS/KleinTwScalarAS.lean`).) -/

section Map

variable {A B : Type*} [CommRing A] [CommRing B]

theorem map_kleinQAS (φ : A →+* B) (a b : A) (y : Fin 5 → A) :
    kleinQAS (φ a) (φ b) (fun i => φ (y i)) = φ (kleinQAS a b y) := by
  simp only [kleinQAS, map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, map_natCast]

theorem map_kleinBilinAS (φ : A →+* B) (a b : A) (u v : Fin 5 → A) :
    kleinBilinAS (φ a) (φ b) (fun i => φ (u i)) (fun i => φ (v i))
      = φ (kleinBilinAS a b u v) := by
  simp only [kleinBilinAS, kleinQAS, Pi.add_apply, map_add, map_sub, map_mul, map_pow, map_neg,
    map_ofNat, map_natCast]

theorem map_kleinStereoAS (φ : A →+* B) (a b : A) (p v : Fin 5 → A) :
    kleinStereoAS (φ a) (φ b) (fun i => φ (p i)) (fun i => φ (v i))
      = fun i => φ (kleinStereoAS a b p v i) := by
  funext i
  simp only [kleinStereoAS, kleinBilinAS, kleinQAS, Pi.sub_apply, Pi.mul_apply, Pi.add_apply,
    map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat]

theorem map_kleinSecDualAS (φ : A →+* B) (a b g : A) (z : Fin 5 → A) :
    φ (kleinSecDualAS a b g z) = kleinSecDualAS (φ a) (φ b) (φ g) (fun i => φ (z i)) := by
  simp only [kleinSecDualAS]
  simp only [map_add, map_mul, map_sub, map_neg, map_pow, map_ofNat, map_natCast]

theorem map_kleinFhomAS (φ : A →+* B) (a b g : A) (p v : Fin 5 → A) :
    φ (kleinFhomAS a b g p v)
      = kleinFhomAS (φ a) (φ b) (φ g) (fun i => φ (p i)) (fun i => φ (v i)) := by
  rw [kleinFhomAS, kleinFhomAS, map_mul, map_kleinBilinAS φ a b p v,
    map_kleinStereoAS φ a b p v,
    ← KleinTwScalarAS_map_kleinSecAS φ a b g (kleinStereoAS a b p v)]

/-- Naturality of the components of the AS inverse quadro-cubic map under a ring homomorphism. -/
theorem map_kleinRAS_defs {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B)
    (a b g : A) (z : Fin 5 → A) :
    (fun i => φ (kleinRAS a b g z i)) = kleinRAS (φ a) (φ b) (φ g) (fun i => φ (z i)) := by
  funext i
  fin_cases i <;>
    simp [kleinRAS, kleinRAS0, kleinRAS1, kleinRAS2, kleinRAS3, kleinRAS4, map_ofNat]

theorem map_kleinGhomAS (φ : A →+* B) (a b g : A) (p w : Fin 5 → A) :
    φ (kleinGhomAS a b g p w)
      = kleinGhomAS (φ a) (φ b) (φ g) (fun i => φ (p i)) (fun i => φ (w i)) := by
  rw [kleinGhomAS, kleinGhomAS, map_mul, ← map_kleinRAS_defs φ a b g w,
    map_kleinBilinAS φ a b p (kleinRAS a b g w), map_kleinSecDualAS φ a b g w]

theorem map_kleinTwPi (φ : A →+* B) (p x : Fin 5 → A) :
    (fun i => φ (Work.MotK.kleinTwPi p x i))
      = Work.MotK.kleinTwPi (fun i => φ (p i)) (fun i => φ (x i)) := by
  funext i
  simp only [Work.MotK.kleinTwPi, Pi.sub_apply, Pi.mul_apply, map_sub, map_mul]

end Map

/-! ## Homogeneity of the AS link data in the coordinate vector -/

section Homog

variable {A : Type*} [CommRing A]

/-- The AS secant quintic is homogeneous of degree `5`. -/
theorem kleinSecAS_smul (a b g c : A) (y : Fin 5 → A) :
    kleinSecAS a b g (fun i => c * y i) = c ^ 5 * kleinSecAS a b g y := by
  simp only [kleinSecAS, Pi.mul_apply]
  refl_ring1

/-- The projection `π_p` is linear. -/
theorem kleinTwPi_smul (p x : Fin 5 → A) (c : A) :
    Work.MotK.kleinTwPi p (fun i => c * x i) = fun i => c * Work.MotK.kleinTwPi p x i := by
  funext i
  simp only [Work.MotK.kleinTwPi, Pi.sub_apply, Pi.mul_apply]
  refl_ring1

/-- The source equation of the link is homogeneous of degree `11` in the coordinate vector. -/
theorem kleinFhomAS_smul (a b g c : A) (p v : Fin 5 → A) :
    kleinFhomAS a b g p (fun i => c * v i) = c ^ 11 * kleinFhomAS a b g p v := by
  rw [kleinFhomAS, kleinFhomAS, kleinBilinAS_smul_right, kleinStereoAS_smul, kleinSecAS_smul]
  refl_ring1

/-- The target equation of the link is homogeneous of degree `8` in the coordinate vector. -/
theorem kleinGhomAS_smul (a b g c : A) (p w : Fin 5 → A) :
    kleinGhomAS a b g p (fun i => c * w i) = c ^ 8 * kleinGhomAS a b g p w := by
  rw [kleinGhomAS, kleinGhomAS, kleinRAS_smul, kleinBilinAS_smul_right, kleinSecDualAS_smul]
  refl_ring1

end Homog

/-! ## The projection fixes the source equation on the quadric -/

/-- **`π_p` does not change the source equation on the quadric**: `F^AS(p, x - x₀·p) = F^AS(p, x)`
for `q(p) = 0` (both the polar form and the stereographic image are unchanged). -/
theorem KleinFhomPiAS {A : Type*} [CommRing A] (a b g : A) (p x : Fin 5 → A)
    (hp : kleinQAS a b p = 0) :
    kleinFhomAS a b g p (Work.MotK.kleinTwPi p x) = kleinFhomAS a b g p x := by
  rw [kleinFhomAS, kleinFhomAS, kleinBilinAS_pi_eq a b p x hp]
  congr 1
  have h : kleinStereoAS a b p (Work.MotK.kleinTwPi p x)
      = fun i => kleinQAS a b x * p i - kleinBilinAS a b p x * x i :=
    kleinStereoAS_pi a b p x hp
  have h2 : kleinStereoAS a b p x = fun i => kleinQAS a b x * p i - kleinBilinAS a b p x * x i :=
    rfl
  rw [h, h2]

end Work.MotAS
