import Mathlib
import Submission.Work.MotAS.Nodes.ASCertGen.P3Kernel
import Submission.Work.MotAS.Nodes.ASrulChartIdFibre
import Submission.Work.MotAS.ASRul.kernel_basis
import Submission.Work.MotAS.ASRul.kleinMAS_fibre
import Submission.Work.MotAS.ASResidual
import Submission.Work.MotAS.CensusAS2
import Submission.Work.MotAS.ASChartGeo
import Submission.Work.MotAS.KleinTwScalarAS
import Submission.Work.MotAS.ASRulingMainAux
import Submission.Work.MotAS.ASRulV2.Defs

import Submission.Work.MotAS.Nodes.ASrulChartIdPre
import Submission.Work.MotAS.Nodes.ASrulChartIdAT
import Submission.Work.MotAS.Nodes.ASCertGen.P2Line

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option autoImplicit false

namespace Work.MotAS.Nodes

open MvPolynomial

/-! ## §4  The ruling presentation `θ` in `S = A[T][1/ε]` -/

/-- The normalising element `ε` in `S`. -/
noncomputable def epsU (K : Type) [Field K] [CharP K 5] (a b g : K) : SQ K a b g :=
  Work.MotAS.Nodes.ASGen.toS a b g (Polynomial.C (Work.MotC5N3.ASrulEpsA a b g))

/-- `ε` is a unit of `S`. -/
theorem epsU_isUnit (K : Type) [Field K] [CharP K 5] (a b g : K) : IsUnit (epsU K a b g) := by
  letI : Semiring (AQ K a b g) := (inferInstance : CommSemiring (AQ K a b g)).toSemiring
  letI : CommSemiring (AQ K a b g) := inferInstance
  letI : CommRing (AQ K a b g) := inferInstance
  letI : Algebra (PQ K a b g) (SQ K a b g) := OreLocalization.instAlgebra
  have h : epsU K a b g = algebraMap (PQ K a b g) (SQ K a b g)
      (Polynomial.C (Work.MotC5N3.ASrulEpsA a b g)) := rfl
  rw [h]
  exact IsLocalization.map_units _ ⟨Polynomial.C (Work.MotC5N3.ASrulEpsA a b g),
    Submonoid.mem_powers _⟩

/-- The inverse of `ε` in `S`. -/
noncomputable def epsUi (K : Type) [Field K] [CharP K 5] (a b g : K) : SQ K a b g :=
  ↑((epsU_isUnit K a b g).unit)⁻¹

/-- `ε⁻¹ · ε = 1`. -/
theorem epsUi_mul_epsU (K : Type) [Field K] [CharP K 5] (a b g : K) :
    epsUi K a b g * epsU K a b g = 1 := by
  rw [show epsU K a b g = ↑((epsU_isUnit K a b g).unit) from
    IsUnit.unit_spec (epsU_isUnit K a b g)]
  exact Units.inv_mul _

/-- `toL` on the constants. -/
theorem toS_const (K : Type) [Field K] [CharP K 5] (a b g : K) (x : K) :
    Work.MotAS.Nodes.ASGen.toS a b g (algebraMap K (PQ K a b g) x) = algebraMap K (SQ K a b g) x := by
  letI : Semiring (AQ K a b g) := (inferInstance : CommSemiring (AQ K a b g)).toSemiring
  letI : CommSemiring (AQ K a b g) := inferInstance
  letI : CommRing (AQ K a b g) := inferInstance
  letI : Algebra (PQ K a b g) (SQ K a b g) := OreLocalization.instAlgebra
  rw [show Work.MotAS.Nodes.ASGen.toS a b g = algebraMap (PQ K a b g) (SQ K a b g) from rfl]
  exact (IsScalarTower.algebraMap_apply K (PQ K a b g) (SQ K a b g) x).symm

/-- `θ` fixes the constants. -/
theorem theta_C (K : Type) [Field K] [CharP K 5] (a b g : K)
    (hDZ : IsDomain (AQ K a b g)) (x : K) :
    Work.MotC5N3.ASrulTheta a b g hDZ (MvPolynomial.C x) = algebraMap K (SQ K a b g) x := by
  rw [Work.MotC5N3.ASrulTheta]
  exact MvPolynomial.aeval_C _ _

/-- `θ` fixes the constants (ring-hom form). -/
theorem theta_C' (K : Type) [Field K] [CharP K 5] (a b g : K)
    (hDZ : IsDomain (AQ K a b g)) (x : K) :
    ((Work.MotC5N3.ASrulTheta a b g hDZ).toRingHom) (MvPolynomial.C x)
      = algebraMap K (SQ K a b g) x :=
  theta_C K a b g hDZ x

/-- **The `θ`-relation for the chart coordinates**: `θ (X j) · ε = zvS (j+1)`. -/
theorem theta_X_mul (K : Type) [Field K] [CharP K 5] (a b g : K)
    (hDZ : IsDomain (AQ K a b g)) (j : Fin 3) :
    Work.MotC5N3.ASrulTheta a b g hDZ (MvPolynomial.X j) * epsU K a b g
      = Work.MotAS.Nodes.ASGen.toS a b g (Work.MotAS.Nodes.ASGen.zvT a b g (Work.MotAS.asCh3 j)) := by
  letI : Semiring (AQ K a b g) := (inferInstance : CommSemiring (AQ K a b g)).toSemiring
  letI : CommSemiring (AQ K a b g) := inferInstance
  letI : CommRing (AQ K a b g) := inferInstance
  letI : Algebra (PQ K a b g) (SQ K a b g) := OreLocalization.instAlgebra
  have hθ : Work.MotC5N3.ASrulTheta a b g hDZ (MvPolynomial.X j)
      = IsLocalization.mk' (SQ K a b g) (Work.MotAS.Nodes.ASGen.zvT a b g (Work.MotAS.asCh3 j))
          ⟨Polynomial.C (Work.MotC5N3.ASrulEpsA a b g), Submonoid.mem_powers _⟩ := by
    rw [Work.MotC5N3.ASrulTheta]
    exact MvPolynomial.aeval_X _ _
  have hspec := IsLocalization.mk'_spec (S := SQ K a b g)
    (M := Submonoid.powers (Polynomial.C (Work.MotC5N3.ASrulEpsA a b g)))
    (Work.MotAS.Nodes.ASGen.zvT a b g (Work.MotAS.asCh3 j))
    ⟨Polynomial.C (Work.MotC5N3.ASrulEpsA a b g), Submonoid.mem_powers _⟩
  rw [hθ, show epsU K a b g = algebraMap (PQ K a b g) (SQ K a b g)
      (Polynomial.C (Work.MotC5N3.ASrulEpsA a b g)) from rfl,
    show Work.MotAS.Nodes.ASGen.toS a b g (Work.MotAS.Nodes.ASGen.zvT a b g (Work.MotAS.asCh3 j))
      = algebraMap (PQ K a b g) (SQ K a b g)
          (Work.MotAS.Nodes.ASGen.zvT a b g (Work.MotAS.asCh3 j)) from rfl]
  exact hspec

/-- `θ (X 0) · ε = zvS 1`. -/
theorem theta_X0 (K : Type) [Field K] [CharP K 5] (a b g : K)
    (hDZ : IsDomain (AQ K a b g)) :
    Work.MotC5N3.ASrulTheta a b g hDZ (MvPolynomial.X 0) * epsU K a b g
      = Work.MotAS.Nodes.ASGen.toS a b g (Work.MotAS.Nodes.ASGen.zvT a b g 1) := by
  simpa using theta_X_mul K a b g hDZ (0 : Fin 3)

/-- `θ (X 1) · ε = zvS 2`. -/
theorem theta_X1 (K : Type) [Field K] [CharP K 5] (a b g : K)
    (hDZ : IsDomain (AQ K a b g)) :
    Work.MotC5N3.ASrulTheta a b g hDZ (MvPolynomial.X 1) * epsU K a b g
      = Work.MotAS.Nodes.ASGen.toS a b g (Work.MotAS.Nodes.ASGen.zvT a b g 2) := by
  simpa using theta_X_mul K a b g hDZ (1 : Fin 3)

/-- `θ (X 2) · ε = zvS 3`. -/
theorem theta_X2 (K : Type) [Field K] [CharP K 5] (a b g : K)
    (hDZ : IsDomain (AQ K a b g)) :
    Work.MotC5N3.ASrulTheta a b g hDZ (MvPolynomial.X 2) * epsU K a b g
      = Work.MotAS.Nodes.ASGen.toS a b g (Work.MotAS.Nodes.ASGen.zvT a b g 3) := by
  simpa using theta_X_mul K a b g hDZ (2 : Fin 3)

theorem piV_one (K : Type) [Field K] (a b g : K) :
    piV K a b g 1 = Work.MotAS.Nodes.ASGen.zvT a b g 1 := by
  rw [piV, Work.MotK.kleinTwPi, e0v_one, mul_zero, sub_zero]

theorem piV_two (K : Type) [Field K] (a b g : K) :
    piV K a b g 2 = Work.MotAS.Nodes.ASGen.zvT a b g 2 := by
  rw [piV, Work.MotK.kleinTwPi, e0v_two, mul_zero, sub_zero]

theorem piV_three (K : Type) [Field K] (a b g : K) :
    piV K a b g 3 = Work.MotAS.Nodes.ASGen.zvT a b g 3 := by
  rw [piV, Work.MotK.kleinTwPi, e0v_three, mul_zero, sub_zero]

theorem piV_four (K : Type) [Field K] (a b g : K) :
    piV K a b g 4 = Work.MotAS.Nodes.ASGen.zvT a b g 4 := by
  rw [piV, Work.MotK.kleinTwPi, e0v_four, mul_zero, sub_zero]

/-- `θ ∘ chart3 = ε⁻¹ • π_{e₀}(zvT)`. -/
theorem theta_chart (K : Type) [Field K] [CharP K 5] (a b g : K)
    (hDZ : IsDomain (AQ K a b g)) :
    (fun k : Fin 5 => Work.MotC5N3.ASrulTheta a b g hDZ (Work.MotK.chart3 K k))
      = fun k => epsUi K a b g * Work.MotAS.Nodes.ASGen.toS a b g (piV K a b g k) := by
  funext k
  fin_cases k
  · show Work.MotC5N3.ASrulTheta a b g hDZ (Work.MotK.chart3 K (0 : Fin 5))
        = epsUi K a b g * Work.MotAS.Nodes.ASGen.toS a b g (piV K a b g (0 : Fin 5))
    rw [show Work.MotK.chart3 K (0 : Fin 5) = (0 : MvPolynomial (Fin 3) K) from rfl, map_zero,
      piV_zero, map_zero, mul_zero]
  · show Work.MotC5N3.ASrulTheta a b g hDZ (Work.MotK.chart3 K (1 : Fin 5))
        = epsUi K a b g * Work.MotAS.Nodes.ASGen.toS a b g (piV K a b g (1 : Fin 5))
    have h := theta_X0 K a b g hDZ
    rw [show Work.MotK.chart3 K (1 : Fin 5) = MvPolynomial.X 0 from rfl, piV_one, ← h]
    rw [show epsUi K a b g * (Work.MotC5N3.ASrulTheta a b g hDZ (MvPolynomial.X 0)
          * epsU K a b g)
        = Work.MotC5N3.ASrulTheta a b g hDZ (MvPolynomial.X 0) * (epsUi K a b g * epsU K a b g)
        from by ring, epsUi_mul_epsU, mul_one]
  · show Work.MotC5N3.ASrulTheta a b g hDZ (Work.MotK.chart3 K (2 : Fin 5))
        = epsUi K a b g * Work.MotAS.Nodes.ASGen.toS a b g (piV K a b g (2 : Fin 5))
    have h := theta_X1 K a b g hDZ
    rw [show Work.MotK.chart3 K (2 : Fin 5) = MvPolynomial.X 1 from rfl, piV_two, ← h]
    rw [show epsUi K a b g * (Work.MotC5N3.ASrulTheta a b g hDZ (MvPolynomial.X 1)
          * epsU K a b g)
        = Work.MotC5N3.ASrulTheta a b g hDZ (MvPolynomial.X 1) * (epsUi K a b g * epsU K a b g)
        from by ring, epsUi_mul_epsU, mul_one]
  · show Work.MotC5N3.ASrulTheta a b g hDZ (Work.MotK.chart3 K (3 : Fin 5))
        = epsUi K a b g * Work.MotAS.Nodes.ASGen.toS a b g (piV K a b g (3 : Fin 5))
    have h := theta_X2 K a b g hDZ
    rw [show Work.MotK.chart3 K (3 : Fin 5) = MvPolynomial.X 2 from rfl, piV_three, ← h]
    rw [show epsUi K a b g * (Work.MotC5N3.ASrulTheta a b g hDZ (MvPolynomial.X 2)
          * epsU K a b g)
        = Work.MotC5N3.ASrulTheta a b g hDZ (MvPolynomial.X 2) * (epsUi K a b g * epsU K a b g)
        from by ring, epsUi_mul_epsU, mul_one]
  · show Work.MotC5N3.ASrulTheta a b g hDZ (Work.MotK.chart3 K (4 : Fin 5))
        = epsUi K a b g * Work.MotAS.Nodes.ASGen.toS a b g (piV K a b g (4 : Fin 5))
    rw [show Work.MotK.chart3 K (4 : Fin 5) = (1 : MvPolynomial (Fin 3) K) from rfl, map_one,
      piV_four, Work.MotAS.Nodes.ASGen.zvT_four]
    rw [show Work.MotAS.Nodes.ASGen.toS a b g
          (Polynomial.C (Work.MotC5N3.ASrulEpsA a b g)) = epsU K a b g from rfl,
      epsUi_mul_epsU]

/-- `θ ∘ pAS0 = e₀`. -/
theorem theta_e0 (K : Type) [Field K] [CharP K 5] (a b g : K)
    (hDZ : IsDomain (AQ K a b g)) :
    (fun i : Fin 5 => Work.MotC5N3.ASrulTheta a b g hDZ (Work.MotAS.pAS0 K i))
      = e0v (SQ K a b g) := by
  funext i
  fin_cases i
  · show Work.MotC5N3.ASrulTheta a b g hDZ (Work.MotAS.pAS0 K (0 : Fin 5)) = e0v (SQ K a b g) 0
    rw [Work.MotAS.pAS0_zero, e0v_zero, map_one]
  · show Work.MotC5N3.ASrulTheta a b g hDZ (Work.MotAS.pAS0 K (1 : Fin 5)) = e0v (SQ K a b g) 1
    rw [show Work.MotAS.pAS0 K (1 : Fin 5) = (0 : MvPolynomial (Fin 3) K) from rfl,
      e0v_one, map_zero]
  · show Work.MotC5N3.ASrulTheta a b g hDZ (Work.MotAS.pAS0 K (2 : Fin 5)) = e0v (SQ K a b g) 2
    rw [show Work.MotAS.pAS0 K (2 : Fin 5) = (0 : MvPolynomial (Fin 3) K) from rfl,
      e0v_two, map_zero]
  · show Work.MotC5N3.ASrulTheta a b g hDZ (Work.MotAS.pAS0 K (3 : Fin 5)) = e0v (SQ K a b g) 3
    rw [show Work.MotAS.pAS0 K (3 : Fin 5) = (0 : MvPolynomial (Fin 3) K) from rfl,
      e0v_three, map_zero]
  · show Work.MotC5N3.ASrulTheta a b g hDZ (Work.MotAS.pAS0 K (4 : Fin 5)) = e0v (SQ K a b g) 4
    rw [Work.MotAS.pAS0_four, e0v_four, map_zero]

/-- `θ ∘ pAS0 = e₀` (ring-hom form). -/
theorem theta_e0' (K : Type) [Field K] [CharP K 5] (a b g : K) (hDZ : IsDomain (AQ K a b g)) :
    (fun i : Fin 5 => ((Work.MotC5N3.ASrulTheta a b g hDZ).toRingHom) (Work.MotAS.pAS0 K i))
      = e0v (SQ K a b g) :=
  theta_e0 K a b g hDZ

/-- `θ ∘ chart3 = ε⁻¹ • π_{e₀}(zvT)` (ring-hom form). -/
theorem theta_chart' (K : Type) [Field K] [CharP K 5] (a b g : K)
    (hDZ : IsDomain (AQ K a b g)) :
    (fun k : Fin 5 => ((Work.MotC5N3.ASrulTheta a b g hDZ).toRingHom) (Work.MotK.chart3 K k))
      = fun k => epsUi K a b g * Work.MotAS.Nodes.ASGen.toS a b g (piV K a b g k) :=
  theta_chart K a b g hDZ

/-- `toS` sends `e₀` to `e₀`. -/
theorem map_e0v_toL (K : Type) [Field K] [CharP K 5] (a b g : K) :
    (fun j : Fin 5 => Work.MotAS.Nodes.ASGen.toS a b g (e0v (PQ K a b g) j))
      = e0v (SQ K a b g) := by
  funext j
  fin_cases j <;> simp

/-- The stereographic step: `θ (y^AS(chart3)) = ε⁻² · Ψ y`. -/
theorem theta_stereo (K : Type) [Field K] [CharP K 5] (a b g : K)
    (hDZ : IsDomain (AQ K a b g)) :
    (fun i : Fin 5 => Work.MotC5N3.ASrulTheta a b g hDZ
        (Work.MotAS.kleinStereoAS (MvPolynomial.C a) (MvPolynomial.C b) (Work.MotAS.pAS0 K)
          (Work.MotK.chart3 K) i))
      = fun i => (epsUi K a b g) ^ 2 * Work.MotAS.Nodes.ASGen.toS a b g (yV K a b g i) := by
  have h1 : (fun i : Fin 5 => Work.MotC5N3.ASrulTheta a b g hDZ
        (Work.MotAS.kleinStereoAS (MvPolynomial.C a) (MvPolynomial.C b) (Work.MotAS.pAS0 K)
          (Work.MotK.chart3 K) i))
      = Work.MotAS.kleinStereoAS (algebraMap K (SQ K a b g) a) (algebraMap K (SQ K a b g) b)
          (e0v (SQ K a b g))
          (fun k => epsUi K a b g * Work.MotAS.Nodes.ASGen.toS a b g (piV K a b g k)) := by
    change (fun i : Fin 5 => ((Work.MotC5N3.ASrulTheta a b g hDZ).toRingHom)
        (Work.MotAS.kleinStereoAS (MvPolynomial.C a) (MvPolynomial.C b) (Work.MotAS.pAS0 K)
          (Work.MotK.chart3 K) i))
      = Work.MotAS.kleinStereoAS (algebraMap K (SQ K a b g) a) (algebraMap K (SQ K a b g) b)
          (e0v (SQ K a b g))
          (fun k => epsUi K a b g * Work.MotAS.Nodes.ASGen.toS a b g (piV K a b g k))
    rw [map_kleinStereoAS_vec (φ := (Work.MotC5N3.ASrulTheta a b g hDZ).toRingHom)
      (MvPolynomial.C a) (MvPolynomial.C b) (Work.MotAS.pAS0 K) (Work.MotK.chart3 K)]
    rw [theta_C' K a b g hDZ a, theta_C' K a b g hDZ b, theta_e0' K a b g hDZ,
      theta_chart' K a b g hDZ]
  have h2 : Work.MotAS.kleinStereoAS (algebraMap K (SQ K a b g) a)
        (algebraMap K (SQ K a b g) b) (e0v (SQ K a b g))
        (fun j => Work.MotAS.Nodes.ASGen.toS a b g (piV K a b g j))
      = fun i => Work.MotAS.Nodes.ASGen.toS a b g (yV K a b g i) := by
    funext i
    have hmapv := map_kleinStereoAS_vec (φ := Work.MotAS.Nodes.ASGen.toS a b g)
      (algebraMap K (PQ K a b g) a) (algebraMap K (PQ K a b g) b) (e0v (PQ K a b g))
      (piV K a b g)
    rw [toS_const K a b g a, toS_const K a b g b, map_e0v_toL K a b g] at hmapv
    rw [← congrFun hmapv i]
    rfl
  rw [h1]
  rw [show (fun k : Fin 5 => epsUi K a b g * Work.MotAS.Nodes.ASGen.toS a b g (piV K a b g k))
      = fun k => epsUi K a b g
          * (fun j => Work.MotAS.Nodes.ASGen.toS a b g (piV K a b g j)) k from rfl]
  rw [Work.MotAS.kleinStereoAS_smul]
  exact congrArg (fun w : Fin 5 → SQ K a b g => fun i => (epsUi K a b g) ^ 2 * w i) h2

/-- **The `θ`-computation**: `θ (fwVecAS2 · j) = ε⁻⁴ · Ψ (P j)`. -/
theorem theta_fwVec (K : Type) [Field K] [CharP K 5] (a b g : K)
    (hDZ : IsDomain (AQ K a b g)) (j : Fin 5) :
    Work.MotC5N3.ASrulTheta a b g hDZ (Work.MotAS.fwVecAS2 a b g j)
      = (epsUi K a b g) ^ 4 * Work.MotAS.Nodes.ASGen.toS a b g (PV K a b g j) := by
  have hnat1 := Work.MotAS.KleinTwScalarAS_map_kleinPAS
    (φ := (Work.MotC5N3.ASrulTheta a b g hDZ).toRingHom) (MvPolynomial.C a) (MvPolynomial.C b)
    (MvPolynomial.C g)
    (Work.MotAS.kleinStereoAS (MvPolynomial.C a) (MvPolynomial.C b) (Work.MotAS.pAS0 K)
      (Work.MotK.chart3 K))
  have step1 : Work.MotC5N3.ASrulTheta a b g hDZ (Work.MotAS.fwVecAS2 a b g j)
      = Work.MotAS.kleinPAS (algebraMap K (SQ K a b g) a) (algebraMap K (SQ K a b g) b)
          (algebraMap K (SQ K a b g) g)
          (fun i => Work.MotC5N3.ASrulTheta a b g hDZ
            (Work.MotAS.kleinStereoAS (MvPolynomial.C a) (MvPolynomial.C b)
              (Work.MotAS.pAS0 K) (Work.MotK.chart3 K) i)) j := by
    have h := (congrFun hnat1 j).symm
    rw [theta_C' K a b g hDZ a, theta_C' K a b g hDZ b, theta_C' K a b g hDZ g] at h
    exact h
  have step4 : Work.MotAS.kleinPAS (algebraMap K (SQ K a b g) a) (algebraMap K (SQ K a b g) b)
        (algebraMap K (SQ K a b g) g) (fun i => Work.MotAS.Nodes.ASGen.toS a b g (yV K a b g i))
        j
      = Work.MotAS.Nodes.ASGen.toS a b g (PV K a b g j) := by
    have h := Work.MotAS.KleinTwScalarAS_map_kleinPAS (φ := Work.MotAS.Nodes.ASGen.toS a b g)
      (algebraMap K (PQ K a b g) a) (algebraMap K (PQ K a b g) b) (algebraMap K (PQ K a b g) g)
      (yV K a b g)
    rw [toS_const K a b g a, toS_const K a b g b, toS_const K a b g g] at h
    exact (congrFun h j).trans rfl
  calc Work.MotC5N3.ASrulTheta a b g hDZ (Work.MotAS.fwVecAS2 a b g j)
      = Work.MotAS.kleinPAS (algebraMap K (SQ K a b g) a) (algebraMap K (SQ K a b g) b)
          (algebraMap K (SQ K a b g) g)
          (fun i => Work.MotC5N3.ASrulTheta a b g hDZ
            (Work.MotAS.kleinStereoAS (MvPolynomial.C a) (MvPolynomial.C b)
              (Work.MotAS.pAS0 K) (Work.MotK.chart3 K) i)) j := step1
    _ = Work.MotAS.kleinPAS (algebraMap K (SQ K a b g) a) (algebraMap K (SQ K a b g) b)
          (algebraMap K (SQ K a b g) g)
          (fun i => (epsUi K a b g) ^ 2 * Work.MotAS.Nodes.ASGen.toS a b g (yV K a b g i)) j := by
        rw [theta_stereo K a b g hDZ]
    _ = ((epsUi K a b g) ^ 2) ^ 2 * Work.MotAS.kleinPAS (algebraMap K (SQ K a b g) a)
          (algebraMap K (SQ K a b g) b) (algebraMap K (SQ K a b g) g)
          (fun i => Work.MotAS.Nodes.ASGen.toS a b g (yV K a b g i)) j :=
        congrFun (Work.MotAS.kleinPAS_smul (algebraMap K (SQ K a b g) a)
          (algebraMap K (SQ K a b g) b) (algebraMap K (SQ K a b g) g) ((epsUi K a b g) ^ 2)
          (fun i => Work.MotAS.Nodes.ASGen.toS a b g (yV K a b g i))) j
    _ = ((epsUi K a b g) ^ 2) ^ 2 * Work.MotAS.Nodes.ASGen.toS a b g (PV K a b g j) := by
        rw [step4]
    _ = (epsUi K a b g) ^ 4 * Work.MotAS.Nodes.ASGen.toS a b g (PV K a b g j) := by ring

/-- **The chart identity of the AS ruling presentation** (for the original `ASrulTheta`). -/
theorem ASrulTheta_chart (K : Type) [Field K] [CharP K 5] (a b g : K)
    (hDZ : IsDomain (AQ K a b g)) (i : Fin 3) :
    Work.MotC5N3.ASrulTheta a b g hDZ (Work.MotAS.fwVecAS2 a b g 0)
      * Work.MotAS.Nodes.ASGen.toS a b g
          (Polynomial.C (Ideal.Quotient.mk (Ideal.radical (Work.MotAS.ZIAS a b g))
            (MvPolynomial.X i)))
      = Work.MotC5N3.ASrulTheta a b g hDZ
          (Work.MotAS.fwVecAS2 a b g (Work.MotAS.asCh3 i)) := by
  have hmain := PV_chart K a b g hDZ i
  have hf : Work.MotAS.Nodes.ASGen.toS a b g (PV K a b g 0)
        * Work.MotAS.Nodes.ASGen.toS a b g
          (Polynomial.C (Ideal.Quotient.mk (Ideal.radical (Work.MotAS.ZIAS a b g))
            (MvPolynomial.X i)))
      = Work.MotAS.Nodes.ASGen.toS a b g (PV K a b g (Work.MotAS.asCh3 i)) := by
    rw [← map_mul, hmain]
  calc Work.MotC5N3.ASrulTheta a b g hDZ (Work.MotAS.fwVecAS2 a b g 0)
        * Work.MotAS.Nodes.ASGen.toS a b g
          (Polynomial.C (Ideal.Quotient.mk (Ideal.radical (Work.MotAS.ZIAS a b g))
            (MvPolynomial.X i)))
      = (epsUi K a b g) ^ 4 * Work.MotAS.Nodes.ASGen.toS a b g (PV K a b g 0)
        * Work.MotAS.Nodes.ASGen.toS a b g
          (Polynomial.C (Ideal.Quotient.mk (Ideal.radical (Work.MotAS.ZIAS a b g))
            (MvPolynomial.X i))) := by
        rw [theta_fwVec K a b g hDZ 0]
    _ = (epsUi K a b g) ^ 4 * (Work.MotAS.Nodes.ASGen.toS a b g (PV K a b g 0)
        * Work.MotAS.Nodes.ASGen.toS a b g
          (Polynomial.C (Ideal.Quotient.mk (Ideal.radical (Work.MotAS.ZIAS a b g))
            (MvPolynomial.X i)))) := by ring
    _ = (epsUi K a b g) ^ 4 * Work.MotAS.Nodes.ASGen.toS a b g (PV K a b g (Work.MotAS.asCh3 i)) := by
        rw [hf]
    _ = Work.MotC5N3.ASrulTheta a b g hDZ (Work.MotAS.fwVecAS2 a b g (Work.MotAS.asCh3 i)) := by
        rw [theta_fwVec K a b g hDZ (Work.MotAS.asCh3 i)]

end Work.MotAS.Nodes
