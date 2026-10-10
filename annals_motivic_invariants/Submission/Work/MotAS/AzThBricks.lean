import Mathlib
import Submission.Work.MotAS.azThetaDefs
import Submission.Work.MotAS.CensusASFalse
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotAS.AzTh` — bricks for the AS chart composite identity

The lemmas assembled here are the geometric/elementary inputs of the proof of
`Work.MotAS.azTheta_fwVecAS2` (`Submission/Work/MotAS/azTheta_fwVecAS2.lean`):

* `Evec` — the stereographic point `e₀ = (1,0,0,0,0)` of the AS chart as a constant vector of
  `K[x,y]` (the vector version `Work.MotAS.azE` lives in another file, hence the different name);
* `PAS_smul`, `QAS_smul`, `Bilin_smul_right`, `stereo_smul` — homogeneity of the AS link data;
* `stereo_pi_aux`, `stereo_pi` — the inverse-stereographic identity
  `Stereo_p(π_p x) = q(x)p − b(p,x)x` (restated under a name that does not clash with the copies
  in the census files);
* `q_Evec` — `q(e₀) = 0`;
* `azChi_eq_twPi` — `azChi` is the projection `π_{e₀}` of `azZ`;
* `comp`/`comp_apply` — the geometric identity `P^AS(R^AS w) = b(e₀,R^AS w)² s'(w) · w`
  specialised to the plane `w = azP`, i.e. exactly the shape of the hypothesis `hI2` of
  `azTheta_fwVecAS2`;
* `algebraMap_C` — the coefficient bridge `K → K[u,v] → K(u,v)`;
* `param_chart3` — the chart substitution `θ(X_i) = χ_{i+1}/χ₄` as a vector identity (with the
  nonvanishing of `χ₄` as an explicit hypothesis).

Every component identity is stated with *numeral* indices and proved directly (so that the simp
lemmas for `![...]`-literals fire); the vector statements are assembled by `funext` + `fin_cases` +
`show` (the `fin_cases` index `⟨n, ⋯⟩` is definitionally the numeral `n`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3200000

namespace Work.MotAS.AzTh

open MvPolynomial

variable {R : Type*} [CommRing R]

/-- The stereographic point `e₀ = (1,0,0,0,0)` of the AS chart, as a constant vector of `K[x,y]`. -/
noncomputable abbrev Evec (K : Type*) [Field K] : Fin 5 → MvPolynomial (Fin 2) K :=
  fun i => MvPolynomial.C ((![1, 0, 0, 0, 0] : Fin 5 → K) i)


/-- The AS quadric is homogeneous of degree two. -/
theorem QAS_smul (a b c : R) (v : Fin 5 → R) :
    kleinQAS a b (fun i => c * v i) = c ^ 2 * kleinQAS a b v := by
  simp only [kleinQAS, Pi.mul_apply]
  first | refl_ring1 | ring

/-- The polar form is linear in its second argument. -/
theorem Bilin_smul_right (a b c : R) (u v : Fin 5 → R) :
    kleinBilinAS a b u (fun i => c * v i) = c * kleinBilinAS a b u v := by
  simp only [kleinBilinAS, kleinQAS, Pi.add_apply, Pi.mul_apply]
  first | refl_ring1 | ring

theorem PAS_smul_0 (a b g c : R) (v : Fin 5 → R) :
    kleinPAS a b g (fun i => c * v i) (0 : Fin 5) = c ^ 2 * kleinPAS a b g v (0 : Fin 5) := by
  simp only [kleinPAS, kleinPAS0, Matrix.cons_val_zero, Matrix.head_cons, Matrix.tail_cons]
  first | refl_ring1 | ring

theorem PAS_smul_1 (a b g c : R) (v : Fin 5 → R) :
    kleinPAS a b g (fun i => c * v i) (1 : Fin 5) = c ^ 2 * kleinPAS a b g v (1 : Fin 5) := by
  simp only [kleinPAS, kleinPAS1, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.tail_cons]
  first | refl_ring1 | ring

theorem PAS_smul_2 (a b g c : R) (v : Fin 5 → R) :
    kleinPAS a b g (fun i => c * v i) (2 : Fin 5) = c ^ 2 * kleinPAS a b g v (2 : Fin 5) := by
  simp only [kleinPAS, kleinPAS2, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  first | refl_ring1 | ring

theorem PAS_smul_3 (a b g c : R) (v : Fin 5 → R) :
    kleinPAS a b g (fun i => c * v i) (3 : Fin 5) = c ^ 2 * kleinPAS a b g v (3 : Fin 5) := by
  simp only [kleinPAS, kleinPAS3, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  first | refl_ring1 | ring

theorem PAS_smul_4 (a b g c : R) (v : Fin 5 → R) :
    kleinPAS a b g (fun i => c * v i) (4 : Fin 5) = c ^ 2 * kleinPAS a b g v (4 : Fin 5) := by
  simp only [kleinPAS, kleinPAS4, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons]
  first | refl_ring1 | ring

/-- The AS Pfaffians are homogeneous of degree two (pointwise form). -/
theorem PAS_smul (a b g c : R) (v : Fin 5 → R) (k : Fin 5) :
    kleinPAS a b g (fun i => c * v i) k = c ^ 2 * kleinPAS a b g v k := by
  fin_cases k
  · show kleinPAS a b g (fun i => c * v i) (0 : Fin 5)
        = c ^ 2 * kleinPAS a b g v (0 : Fin 5)
    exact PAS_smul_0 a b g c v
  · show kleinPAS a b g (fun i => c * v i) (1 : Fin 5)
        = c ^ 2 * kleinPAS a b g v (1 : Fin 5)
    exact PAS_smul_1 a b g c v
  · show kleinPAS a b g (fun i => c * v i) (2 : Fin 5)
        = c ^ 2 * kleinPAS a b g v (2 : Fin 5)
    exact PAS_smul_2 a b g c v
  · show kleinPAS a b g (fun i => c * v i) (3 : Fin 5)
        = c ^ 2 * kleinPAS a b g v (3 : Fin 5)
    exact PAS_smul_3 a b g c v
  · show kleinPAS a b g (fun i => c * v i) (4 : Fin 5)
        = c ^ 2 * kleinPAS a b g v (4 : Fin 5)
    exact PAS_smul_4 a b g c v

/-- The stereographic parametrisation is homogeneous of degree two. -/
theorem stereo_smul (a b c : R) (p v : Fin 5 → R) :
    kleinStereoAS a b p (fun i => c * v i) = fun i => c ^ 2 * kleinStereoAS a b p v i := by
  funext i
  simp only [kleinStereoAS, Pi.mul_apply, QAS_smul, Bilin_smul_right]
  first | refl_ring1 | ring

/-- The unconditional inverse-stereographic identity. -/
theorem stereo_pi_aux (a b : R) (p x : Fin 5 → R) :
    kleinStereoAS a b p (Work.MotK.kleinTwPi p x)
      = fun i => kleinQAS a b x * p i - kleinBilinAS a b p x * x i
          - kleinQAS a b p * (x 0) ^ 2 * p i + 2 * kleinQAS a b p * x 0 * x i := by
  funext i
  simp only [kleinStereoAS, kleinBilinAS, kleinQAS, Work.MotK.kleinTwPi, Pi.add_apply,
    Pi.sub_apply]
  first | refl_ring1 | ring

/-- The inverse-stereographic identity: for `p` on the quadric, `Stereo_p(π_p x) = q(x)p − b(p,x)x`. -/
theorem stereo_pi (a b : R) (p x : Fin 5 → R) (hp : kleinQAS a b p = 0) :
    kleinStereoAS a b p (Work.MotK.kleinTwPi p x)
      = fun i => kleinQAS a b x * p i - kleinBilinAS a b p x * x i := by
  rw [stereo_pi_aux, hp]
  funext i
  first | refl_ring1 | ring

section Field

variable {K : Type*} [Field K]

/-- `e₀` lies on the AS quadric. -/
theorem q_Evec (a b : K) : kleinQAS (MvPolynomial.C a) (MvPolynomial.C b) (Evec K) = 0 := by
  simp only [kleinQAS, Evec, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons,
    MvPolynomial.C_1, MvPolynomial.C_0]
  first | refl_ring1 | ring

theorem azChiT_0 (a b g : K) :
    azChi a b g (0 : Fin 5) = Work.MotK.kleinTwPi (Evec K) (azZ a b g) (0 : Fin 5) := by
  simp only [azChi, Work.MotK.kleinTwPi, Evec, Matrix.cons_val_zero, Matrix.head_cons,
    Matrix.tail_cons, MvPolynomial.C_1, mul_one, sub_self]

theorem azChiT_1 (a b g : K) :
    azChi a b g (1 : Fin 5) = Work.MotK.kleinTwPi (Evec K) (azZ a b g) (1 : Fin 5) := by
  simp only [azChi, Work.MotK.kleinTwPi, Evec, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.tail_cons, MvPolynomial.C_0, mul_zero, sub_zero]

theorem azChiT_2 (a b g : K) :
    azChi a b g (2 : Fin 5) = Work.MotK.kleinTwPi (Evec K) (azZ a b g) (2 : Fin 5) := by
  simp only [azChi, Work.MotK.kleinTwPi, Evec, Matrix.cons_val_zero, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, MvPolynomial.C_0, mul_zero, sub_zero]

theorem azChiT_3 (a b g : K) :
    azChi a b g (3 : Fin 5) = Work.MotK.kleinTwPi (Evec K) (azZ a b g) (3 : Fin 5) := by
  simp only [azChi, Work.MotK.kleinTwPi, Evec, Matrix.cons_val_zero, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons, MvPolynomial.C_0, mul_zero, sub_zero]

theorem azChiT_4 (a b g : K) :
    azChi a b g (4 : Fin 5) = Work.MotK.kleinTwPi (Evec K) (azZ a b g) (4 : Fin 5) := by
  simp only [azChi, Work.MotK.kleinTwPi, Evec, Matrix.cons_val_zero, Matrix.cons_val_four,
    Matrix.head_cons, Matrix.tail_cons, MvPolynomial.C_0, mul_zero, sub_zero]

/-- `azChi` is the projection `π_{e₀}` of `azZ`. -/
theorem azChi_eq_twPi (a b g : K) :
    azChi a b g = Work.MotK.kleinTwPi (Evec K) (azZ a b g) := by
  funext k
  fin_cases k
  · show azChi a b g (0 : Fin 5) = Work.MotK.kleinTwPi (Evec K) (azZ a b g) (0 : Fin 5)
    exact azChiT_0 a b g
  · show azChi a b g (1 : Fin 5) = Work.MotK.kleinTwPi (Evec K) (azZ a b g) (1 : Fin 5)
    exact azChiT_1 a b g
  · show azChi a b g (2 : Fin 5) = Work.MotK.kleinTwPi (Evec K) (azZ a b g) (2 : Fin 5)
    exact azChiT_2 a b g
  · show azChi a b g (3 : Fin 5) = Work.MotK.kleinTwPi (Evec K) (azZ a b g) (3 : Fin 5)
    exact azChiT_3 a b g
  · show azChi a b g (4 : Fin 5) = Work.MotK.kleinTwPi (Evec K) (azZ a b g) (4 : Fin 5)
    exact azChiT_4 a b g

end Field

/-- **The geometric composite identity at the plane `azP`.**  For `w = (0,u,v,1,0)`, the forward
link map `P^AS` at the stereographic point `e₀` and the source point `χ = π_{e₀}(R^AS w)` returns
`b(e₀,R^AS w)² · s'(w) · w` (recall `azZ a b g = R^AS(azP)`). -/
theorem comp {K : Type*} [Field K] (a b g : K)
    (hI2 : ∀ k : Fin 5,
      Work.MotAS.kleinPAS (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C g)
          (azZ a b g) k
        = Work.MotAS.kleinSecDualAS (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C g)
            (azP K) * azP K k) :
    Work.MotAS.kleinPAS (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C g)
        (kleinStereoAS (MvPolynomial.C a) (MvPolynomial.C b) (Evec K) (azChi a b g))
      = fun k =>
          (kleinBilinAS (MvPolynomial.C a) (MvPolynomial.C b) (Evec K) (azZ a b g)) ^ 2
            * Work.MotAS.kleinSecDualAS (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C g)
                (azP K)
            * azP K k := by
  have hq : kleinQAS (MvPolynomial.C a) (MvPolynomial.C b) (azZ a b g) = 0 := by
    rw [← neg_eq_zero, ← kleinPAS_four_eq_neg (MvPolynomial.C a) (MvPolynomial.C b)
      (MvPolynomial.C g) (azZ a b g)]
    rw [hI2 4]
    simp
  have hp : kleinQAS (MvPolynomial.C a) (MvPolynomial.C b) (Evec K) = 0 := q_Evec a b
  rw [azChi_eq_twPi]
  rw [stereo_pi (MvPolynomial.C a) (MvPolynomial.C b) (Evec K) (azZ a b g) hp]
  rw [show (fun i => kleinQAS (MvPolynomial.C a) (MvPolynomial.C b) (azZ a b g) * (Evec K) i
        - kleinBilinAS (MvPolynomial.C a) (MvPolynomial.C b) (Evec K) (azZ a b g)
            * (azZ a b g) i)
      = fun i => (-(kleinBilinAS (MvPolynomial.C a) (MvPolynomial.C b) (Evec K)
            (azZ a b g))) * (azZ a b g) i from by
    funext i
    rw [hq]
    ring]
  funext k
  rw [PAS_smul (c := -(kleinBilinAS (MvPolynomial.C a) (MvPolynomial.C b) (Evec K)
      (azZ a b g)))]
  rw [hI2 k]
  first | refl_ring1 | ring

/-- The pointwise form of `AzTh.comp`. -/
theorem comp_apply {K : Type*} [Field K] (a b g : K)
    (hI2 : ∀ k : Fin 5,
      Work.MotAS.kleinPAS (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C g)
          (azZ a b g) k
        = Work.MotAS.kleinSecDualAS (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C g)
            (azP K) * azP K k) (k : Fin 5) :
    Work.MotAS.kleinPAS (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C g)
        (kleinStereoAS (MvPolynomial.C a) (MvPolynomial.C b) (Evec K) (azChi a b g)) k
      = (kleinBilinAS (MvPolynomial.C a) (MvPolynomial.C b) (Evec K) (azZ a b g)) ^ 2
        * Work.MotAS.kleinSecDualAS (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C g)
            (azP K)
        * azP K k :=
  congrFun (comp a b g hI2) k

/-- The coefficient bridge `K → K[x,y] → K(x,y)`: a scalar of `K` is the image of the
corresponding constant polynomial. -/
theorem algebraMap_C (K : Type*) [Field K] (x : K) :
    algebraMap K (FractionRing (MvPolynomial (Fin 2) K)) x
      = algebraMap (MvPolynomial (Fin 2) K) (FractionRing (MvPolynomial (Fin 2) K))
          (MvPolynomial.C x) := by
  rw [IsScalarTower.algebraMap_apply K (MvPolynomial (Fin 2) K)
    (FractionRing (MvPolynomial (Fin 2) K)), MvPolynomial.algebraMap_eq]

section ParamChart

variable {K : Type*} [Field K]

theorem param_0 (a b g : K) :
    azTheta a b g (Work.MotK.chart3 K (0 : Fin 5))
      = (algebraMap (MvPolynomial (Fin 2) K) (FractionRing (MvPolynomial (Fin 2) K))
            (azChi a b g 4))⁻¹
        * algebraMap (MvPolynomial (Fin 2) K) (FractionRing (MvPolynomial (Fin 2) K))
            (azChi a b g (0 : Fin 5)) := by
  have h1 : azTheta a b g (Work.MotK.chart3 K (0 : Fin 5)) = 0 := by
    simp only [Work.MotK.chart3, Matrix.cons_val_zero, Matrix.head_cons, Matrix.tail_cons,
      azTheta, map_zero]
  have h2 : azChi a b g (0 : Fin 5) = 0 := by
    simp only [azChi, Matrix.cons_val_zero, Matrix.head_cons, Matrix.tail_cons]
  rw [h1, h2, map_zero, mul_zero]

theorem param_1 (a b g : K) :
    azTheta a b g (Work.MotK.chart3 K (1 : Fin 5))
      = (algebraMap (MvPolynomial (Fin 2) K) (FractionRing (MvPolynomial (Fin 2) K))
            (azChi a b g 4))⁻¹
        * algebraMap (MvPolynomial (Fin 2) K) (FractionRing (MvPolynomial (Fin 2) K))
            (azChi a b g (1 : Fin 5)) := by
  have h1 : azTheta a b g (Work.MotK.chart3 K (1 : Fin 5))
      = algebraMap (MvPolynomial (Fin 2) K) (FractionRing (MvPolynomial (Fin 2) K))
            (azChi a b g 1)
          * (algebraMap (MvPolynomial (Fin 2) K) (FractionRing (MvPolynomial (Fin 2) K))
              (azChi a b g 4))⁻¹ := by
    simp only [Work.MotK.chart3, Matrix.cons_val_one, Matrix.head_cons, azTheta_X, azParam,
      azChi, Matrix.cons_val_zero, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_four, Matrix.tail_cons]
  have h2 : azChi a b g (1 : Fin 5) = azChi a b g 1 := rfl
  rw [h1, h2]
  first | refl_ring1 | ring

theorem param_2 (a b g : K) :
    azTheta a b g (Work.MotK.chart3 K (2 : Fin 5))
      = (algebraMap (MvPolynomial (Fin 2) K) (FractionRing (MvPolynomial (Fin 2) K))
            (azChi a b g 4))⁻¹
        * algebraMap (MvPolynomial (Fin 2) K) (FractionRing (MvPolynomial (Fin 2) K))
            (azChi a b g (2 : Fin 5)) := by
  have h1 : azTheta a b g (Work.MotK.chart3 K (2 : Fin 5))
      = algebraMap (MvPolynomial (Fin 2) K) (FractionRing (MvPolynomial (Fin 2) K))
            (azChi a b g 2)
          * (algebraMap (MvPolynomial (Fin 2) K) (FractionRing (MvPolynomial (Fin 2) K))
              (azChi a b g 4))⁻¹ := by
    simp only [Work.MotK.chart3, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
      azTheta_X, azParam, azChi, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_three, Matrix.cons_val_four]
  have h2 : azChi a b g (2 : Fin 5) = azChi a b g 2 := rfl
  rw [h1, h2]
  first | refl_ring1 | ring

theorem param_3 (a b g : K) :
    azTheta a b g (Work.MotK.chart3 K (3 : Fin 5))
      = (algebraMap (MvPolynomial (Fin 2) K) (FractionRing (MvPolynomial (Fin 2) K))
            (azChi a b g 4))⁻¹
        * algebraMap (MvPolynomial (Fin 2) K) (FractionRing (MvPolynomial (Fin 2) K))
            (azChi a b g (3 : Fin 5)) := by
  have h1 : azTheta a b g (Work.MotK.chart3 K (3 : Fin 5))
      = algebraMap (MvPolynomial (Fin 2) K) (FractionRing (MvPolynomial (Fin 2) K))
            (azChi a b g 3)
          * (algebraMap (MvPolynomial (Fin 2) K) (FractionRing (MvPolynomial (Fin 2) K))
              (azChi a b g 4))⁻¹ := by
    simp only [Work.MotK.chart3, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
      azTheta_X, azParam, azChi, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_four]
  have h2 : azChi a b g (3 : Fin 5) = azChi a b g 3 := rfl
  rw [h1, h2]
  first | refl_ring1 | ring

theorem param_4 (a b g : K)
    (h4 : algebraMap (MvPolynomial (Fin 2) K) (FractionRing (MvPolynomial (Fin 2) K))
        (azChi a b g 4) ≠ 0) :
    azTheta a b g (Work.MotK.chart3 K (4 : Fin 5))
      = (algebraMap (MvPolynomial (Fin 2) K) (FractionRing (MvPolynomial (Fin 2) K))
            (azChi a b g 4))⁻¹
        * algebraMap (MvPolynomial (Fin 2) K) (FractionRing (MvPolynomial (Fin 2) K))
            (azChi a b g (4 : Fin 5)) := by
  have h1 : azTheta a b g (Work.MotK.chart3 K (4 : Fin 5)) = 1 := by
    simp only [Work.MotK.chart3, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons,
      azTheta, map_one]
  have h2 : azChi a b g (4 : Fin 5) = azChi a b g 4 := rfl
  rw [h1, h2, inv_mul_cancel₀ h4]

/-- **The chart substitution** of `azTheta`: the vector `chart3 = (0,X₀,X₁,X₂,1)` is sent to
`χ₄⁻¹ • χ` (the inverse chart map evaluated at the affine chart `χ/χ₄`). -/
theorem param_chart3 (a b g : K)
    (h4 : algebraMap (MvPolynomial (Fin 2) K) (FractionRing (MvPolynomial (Fin 2) K))
        (azChi a b g 4) ≠ 0) :
    (fun i => azTheta a b g (Work.MotK.chart3 K i))
      = (algebraMap (MvPolynomial (Fin 2) K) (FractionRing (MvPolynomial (Fin 2) K))
            (azChi a b g 4))⁻¹
        • (fun i => algebraMap (MvPolynomial (Fin 2) K) (FractionRing (MvPolynomial (Fin 2) K))
            (azChi a b g i)) := by
  funext k
  fin_cases k
  · show azTheta a b g (Work.MotK.chart3 K (0 : Fin 5))
        = (algebraMap (MvPolynomial (Fin 2) K) (FractionRing (MvPolynomial (Fin 2) K))
              (azChi a b g 4))⁻¹
          * algebraMap (MvPolynomial (Fin 2) K) (FractionRing (MvPolynomial (Fin 2) K))
              (azChi a b g (0 : Fin 5))
    exact param_0 a b g
  · show azTheta a b g (Work.MotK.chart3 K (1 : Fin 5))
        = (algebraMap (MvPolynomial (Fin 2) K) (FractionRing (MvPolynomial (Fin 2) K))
              (azChi a b g 4))⁻¹
          * algebraMap (MvPolynomial (Fin 2) K) (FractionRing (MvPolynomial (Fin 2) K))
              (azChi a b g (1 : Fin 5))
    exact param_1 a b g
  · show azTheta a b g (Work.MotK.chart3 K (2 : Fin 5))
        = (algebraMap (MvPolynomial (Fin 2) K) (FractionRing (MvPolynomial (Fin 2) K))
              (azChi a b g 4))⁻¹
          * algebraMap (MvPolynomial (Fin 2) K) (FractionRing (MvPolynomial (Fin 2) K))
              (azChi a b g (2 : Fin 5))
    exact param_2 a b g
  · show azTheta a b g (Work.MotK.chart3 K (3 : Fin 5))
        = (algebraMap (MvPolynomial (Fin 2) K) (FractionRing (MvPolynomial (Fin 2) K))
              (azChi a b g 4))⁻¹
          * algebraMap (MvPolynomial (Fin 2) K) (FractionRing (MvPolynomial (Fin 2) K))
              (azChi a b g (3 : Fin 5))
    exact param_3 a b g
  · show azTheta a b g (Work.MotK.chart3 K (4 : Fin 5))
        = (algebraMap (MvPolynomial (Fin 2) K) (FractionRing (MvPolynomial (Fin 2) K))
              (azChi a b g 4))⁻¹
          * algebraMap (MvPolynomial (Fin 2) K) (FractionRing (MvPolynomial (Fin 2) K))
              (azChi a b g (4 : Fin 5))
    exact param_4 a b g h4

end ParamChart

end Work.MotAS.AzTh
