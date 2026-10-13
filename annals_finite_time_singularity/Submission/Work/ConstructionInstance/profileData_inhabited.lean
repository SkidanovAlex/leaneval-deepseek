import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.ConstructionInstance.ProfileData
import Submission.Work.ConstructionInstance.hasDerivAt_profile_zero
import Submission.Work.ConstructionInstance.ConcreteData

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Set Filter Topology
open scoped Topology NNReal ENNReal

namespace Work.ConstructionInstance

/-! ## Elementary facts about the zero perturbation

We collect here the (elementary) facts that the zero perturbation `gZero` lies in all the
function classes asked for by `ProfileData`, together with the measurability of the scalar
profile `x ↦ profile p gZero (ρ(x)^p) (θ(x))`. -/

/-- `∂_z` of the zero perturbation vanishes. -/
theorem pz_zeroF : Work.Spaces.pz (fun _ _ : ℝ => (0 : ℝ)) = fun _ _ => 0 := by
  funext z θ; simp [Work.Spaces.pz]

/-- `∂_θ` of the zero perturbation vanishes. -/
theorem pth_zeroF : Work.Spaces.pth (fun _ _ : ℝ => (0 : ℝ)) = fun _ _ => 0 := by
  funext z θ; simp [Work.Spaces.pth]

/-- Every iterated `∂_z` of the zero function is zero. -/
theorem pzIter_zeroF (j : ℕ) :
    Work.Spaces.pzIter j (fun _ _ : ℝ => (0 : ℝ)) = fun _ _ => 0 := by
  induction j with
  | zero => rfl
  | succ n ih => rw [Work.Spaces.pzIter_succ, ih]; funext z θ; simp [Work.Spaces.pz]

/-- Every iterated `∂_θ` of the zero function is zero. -/
theorem pthIter_zeroF (i : ℕ) :
    Work.Spaces.pthIter i (fun _ _ : ℝ => (0 : ℝ)) = fun _ _ => 0 := by
  induction i with
  | zero => rfl
  | succ n ih => rw [Work.Spaces.pthIter_succ, ih]; funext z θ; simp [Work.Spaces.pth]

/-- Every iterated `D_z` of the zero function is zero. -/
theorem DzIter_zeroF (i : ℕ) :
    Work.Spaces.DzIter i (fun _ _ : ℝ => (0 : ℝ)) = fun _ _ => 0 := by
  induction i with
  | zero => rfl
  | succ n ih => rw [Work.Spaces.DzIter_succ, ih]; funext z θ; simp [Work.Spaces.Dz, Work.Spaces.pz]

/-- Every iterated `D_θ` of the zero function is zero. -/
theorem DthIter_zeroF (i : ℕ) :
    Work.Spaces.DthIter i (fun _ _ : ℝ => (0 : ℝ)) = fun _ _ => 0 := by
  induction i with
  | zero => rfl
  | succ n ih => rw [Work.Spaces.DthIter_succ, ih]; funext z θ; simp [Work.Spaces.Dth, Work.Spaces.pth]

/-- Every mixed derivative `D_z^j D_θ^i` of the zero function is zero. -/
theorem mixed_zeroF (j i : ℕ) :
    Work.Spaces.mixed j i (fun _ _ : ℝ => (0 : ℝ)) = fun _ _ => 0 := by
  rw [Work.Spaces.mixed, DthIter_zeroF i]
  induction j with
  | zero => rfl
  | succ n ih => rw [Work.Spaces.DzIter_succ, ih]; funext z θ; simp [Work.Spaces.Dz, Work.Spaces.pz]

/-- The `H^k`-integrand of the zero function vanishes. -/
theorem HkIntegrand_zeroF (α : ℝ) (k : ℕ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α k (fun _ _ : ℝ => (0 : ℝ)) z θ = 0 := by
  simp [Work.Spaces.HkIntegrand, DzIter_zeroF, mixed_zeroF]

/-- The squared `H^k`-norm of the zero function vanishes. -/
theorem HkSq_zeroF (α : ℝ) (k : ℕ) :
    Work.Spaces.HkSq α k (fun _ _ : ℝ => (0 : ℝ)) = 0 := by
  simp [Work.Spaces.HkSq, HkIntegrand_zeroF]

/-- The `H^k`-norm of the zero function vanishes. -/
theorem HkNorm_zeroF (α : ℝ) (k : ℕ) :
    Work.Spaces.HkNorm α k (fun _ _ : ℝ => (0 : ℝ)) = 0 := by
  simp [Work.Spaces.HkNorm, HkSq_zeroF]

/-- The zero function lies in `ℋ^k`. -/
theorem HkMem_zeroF (α : ℝ) (k : ℕ) : Work.Spaces.HkMem α k (fun _ _ : ℝ => (0 : ℝ)) := by
  constructor
  · intro z hz
    refine IntegrableOn.congr_fun integrableOn_zero (fun θ hθ => ?_) measurableSet_Icc
    exact (HkIntegrand_zeroF α k z θ).symm
  · have hzero : (fun z => ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α k (fun _ _ : ℝ => (0 : ℝ)) z θ) = fun _ => 0 := by
      funext z; simp [HkIntegrand_zeroF]
    rw [hzero]
    exact integrableOn_zero

/-- The zero function satisfies the `z`-decay hypothesis. -/
theorem decayInZ_zeroF (n : ℕ) : Work.Spaces.DecayInZ n (fun _ _ : ℝ => (0 : ℝ)) := by
  intro j i hij θ hθ
  have h : Work.Spaces.pzIter j (Work.Spaces.pthIter i (fun _ _ : ℝ => (0 : ℝ)))
      = fun _ _ => 0 := by rw [pthIter_zeroF i, pzIter_zeroF j]
  rw [h]
  exact tendsto_const_nhds

/-- The zero function is smooth on a neighbourhood of the closed quadrant. -/
theorem smoothNbhd_zeroF : Work.Spaces.SmoothNbhd (fun _ _ : ℝ => (0 : ℝ)) := by
  show ContDiffOn ℝ ⊤ (Function.uncurry (fun _ _ : ℝ => (0 : ℝ))) _
  exact contDiffOn_const


/-! ## The same facts for the concrete zero perturbation `gZero` -/

theorem pzIter_gZero (j : ℕ) : Work.Spaces.pzIter j gZero = fun _ _ => 0 := by
  have h : gZero = (fun _ _ : ℝ => (0 : ℝ)) := rfl
  rw [h]; exact pzIter_zeroF j

theorem pthIter_gZero (i : ℕ) : Work.Spaces.pthIter i gZero = fun _ _ => 0 := by
  have h : gZero = (fun _ _ : ℝ => (0 : ℝ)) := rfl
  rw [h]; exact pthIter_zeroF i

theorem DzIter_gZero (i : ℕ) : Work.Spaces.DzIter i gZero = fun _ _ => 0 := by
  have h : gZero = (fun _ _ : ℝ => (0 : ℝ)) := rfl
  rw [h]; exact DzIter_zeroF i

theorem DthIter_gZero (i : ℕ) : Work.Spaces.DthIter i gZero = fun _ _ => 0 := by
  have h : gZero = (fun _ _ : ℝ => (0 : ℝ)) := rfl
  rw [h]; exact DthIter_zeroF i

theorem mixed_gZero (j i : ℕ) : Work.Spaces.mixed j i gZero = fun _ _ => 0 := by
  have h : gZero = (fun _ _ : ℝ => (0 : ℝ)) := rfl
  rw [h]; exact mixed_zeroF j i

theorem HkIntegrand_gZero (α : ℝ) (k : ℕ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α k gZero z θ = 0 := by
  have h : gZero = (fun _ _ : ℝ => (0 : ℝ)) := rfl
  rw [h]; exact HkIntegrand_zeroF α k z θ

theorem HkSq_gZero (α : ℝ) (k : ℕ) : Work.Spaces.HkSq α k gZero = 0 := by
  have h : gZero = (fun _ _ : ℝ => (0 : ℝ)) := rfl
  rw [h]; exact HkSq_zeroF α k

theorem HkNorm_gZero (α : ℝ) (k : ℕ) : Work.Spaces.HkNorm α k gZero = 0 := by
  have h : gZero = (fun _ _ : ℝ => (0 : ℝ)) := rfl
  rw [h]; exact HkNorm_zeroF α k

theorem HkMem_gZero (α : ℝ) (k : ℕ) : Work.Spaces.HkMem α k gZero := by
  have h : gZero = (fun _ _ : ℝ => (0 : ℝ)) := rfl
  rw [h]; exact HkMem_zeroF α k

theorem decayInZ_gZero (n : ℕ) : Work.Spaces.DecayInZ n gZero := by
  have h : gZero = (fun _ _ : ℝ => (0 : ℝ)) := rfl
  rw [h]; exact decayInZ_zeroF n

theorem smoothNbhd_gZero : Work.Spaces.SmoothNbhd gZero := by
  have h : gZero = (fun _ _ : ℝ => (0 : ℝ)) := rfl
  rw [h]; exact smoothNbhd_zeroF

/-! ## Measurability of the scalar profile with zero perturbation -/

/-- **The scalar profile with zero perturbation is a.e. strongly measurable**: it is an odd
extension (in `θ`) of `F_*(ρ(x)^p, θ(x))`, a composition of measurable functions of `x`. -/
theorem aestronglyMeasurable_profile_gZero {p : ℝ} (hp : 0 ≤ p) :
    AEStronglyMeasurable
      (fun x : R3 => profile p gZero (Work.Cyl.Rc p x) (Work.Cyl.theta x)) volume := by
  have hGam : Measurable (fun θ : ℝ => Work.Spaces.Gam p θ) := by
    show Measurable fun θ : ℝ => (Real.sin θ * Real.cos θ ^ 2) ^ (p / 3)
    exact (Continuous.rpow_const (by fun_prop) (fun θ => Or.inr (by linarith))).measurable
  have hFstarm : Measurable (fun z : ℝ => Work.FM.Fstar z) := by
    show Measurable fun z : ℝ => 2 * z / (1 + z) ^ 2
    fun_prop
  have hRc : Measurable (fun x : R3 => Work.Cyl.Rc p x) := by
    show Measurable (fun x : Work.Cyl.R3 => Work.Cyl.rho x ^ p)
    refine (Continuous.rpow_const ?_ (fun x => Or.inr hp)).measurable
    show Continuous fun x : Work.Cyl.R3 => Real.sqrt (Work.Cyl.radSq x + Work.Cyl.axial x ^ 2)
    have h1 : Continuous fun x : Work.Cyl.R3 => Work.Cyl.radSq x := by
      show Continuous fun x : Work.Cyl.R3 => x 0 ^ 2 + x 1 ^ 2
      fun_prop
    have h2 : Continuous fun x : Work.Cyl.R3 => Work.Cyl.axial x ^ 2 := by
      show Continuous fun x : Work.Cyl.R3 => x 2 ^ 2
      fun_prop
    exact (h1.add h2).sqrt
  have htheta : Measurable (fun x : R3 => Work.Cyl.theta x) := by
    show Measurable fun x : Work.Cyl.R3 => Real.arctan (Work.Cyl.axial x / Work.Cyl.radial x)
    have hax : Measurable fun x : Work.Cyl.R3 => Work.Cyl.axial x := by
      show Measurable fun x : Work.Cyl.R3 => x 2
      fun_prop
    have hr : Measurable fun x : Work.Cyl.R3 => Work.Cyl.radial x := by
      show Measurable fun x : Work.Cyl.R3 => Real.sqrt (Work.Cyl.radSq x)
      have : Continuous fun x : Work.Cyl.R3 => Work.Cyl.radSq x := by
        show Continuous fun x : Work.Cyl.R3 => x 0 ^ 2 + x 1 ^ 2
        fun_prop
      exact this.measurable.sqrt
    exact Real.continuous_arctan.measurable.comp (hax.div hr)
  have hpos : Measurable
      (fun x : R3 => Work.Construction.Fstar p (Work.Cyl.Rc p x) (Work.Cyl.theta x)) := by
    show Measurable fun x : R3 =>
      p * (Work.Spaces.Gam p (Work.Cyl.theta x) / Work.Spaces.c p)
        * Work.FM.Fstar (Work.Cyl.Rc p x)
    have h1 : Measurable (fun x : R3 => Work.Spaces.Gam p (Work.Cyl.theta x)) :=
      hGam.comp htheta
    have h2 : Measurable (fun x : R3 => Work.FM.Fstar (Work.Cyl.Rc p x)) :=
      hFstarm.comp hRc
    fun_prop
  have hneg : Measurable
      (fun x : R3 => Work.Construction.Fstar p (Work.Cyl.Rc p x) (-(Work.Cyl.theta x))) := by
    show Measurable fun x : R3 =>
      p * (Work.Spaces.Gam p (-(Work.Cyl.theta x)) / Work.Spaces.c p)
        * Work.FM.Fstar (Work.Cyl.Rc p x)
    have h1 : Measurable (fun x : R3 => Work.Spaces.Gam p (-(Work.Cyl.theta x))) :=
      hGam.comp htheta.neg
    have h2 : Measurable (fun x : R3 => Work.FM.Fstar (Work.Cyl.Rc p x)) :=
      hFstarm.comp hRc
    fun_prop
  have hite : Measurable (fun x : R3 =>
      if 0 ≤ Work.Cyl.theta x then
        Work.Construction.Fstar p (Work.Cyl.Rc p x) (Work.Cyl.theta x)
      else -(Work.Construction.Fstar p (Work.Cyl.Rc p x) (-(Work.Cyl.theta x)))) :=
    Measurable.ite (measurableSet_le measurable_const htheta) hpos hneg.neg
  have hEq : (fun x : R3 => profile p gZero (Work.Cyl.Rc p x) (Work.Cyl.theta x))
      = (fun x : R3 =>
      if 0 ≤ Work.Cyl.theta x then
        Work.Construction.Fstar p (Work.Cyl.Rc p x) (Work.Cyl.theta x)
      else -(Work.Construction.Fstar p (Work.Cyl.Rc p x) (-(Work.Cyl.theta x)))) := by
    funext x
    rcases le_or_gt 0 (Work.Cyl.theta x) with h | h
    · rw [profile_of_nonneg h, ite_eq_left h]; simp
    · rw [profile_of_neg (not_le.mpr h), ite_eq_right (not_le.mpr h)]; simp
  rw [hEq]
  exact hite.aestronglyMeasurable

/-! ## The inhabitant of `ProfileData` -/

/-- The affine function `1 - t/2` written in the normal form `1 + m·t` is differentiable with
derivative `m = -1/2`. -/
theorem hasDerivAt_affine (t : ℝ) :
    HasDerivAt (fun s : ℝ => 1 + (-(1 / 2)) * s) (-(1 / 2)) t := by
  have h0 : HasDerivAt (fun s : ℝ => (-(1 / 2)) * s) (-(1 / 2)) t := by
    have h := (hasDerivAt_id t).const_mul (-(1 / 2))
    simpa using h
  have h1 := h0.const_add 1
  simpa using h1

/-- `deriv (λ̄) = -1/2` for `λ̄(t) = 1 - t/2`. -/
theorem hderivval (t : ℝ) : deriv (fun s : ℝ => 1 - s / 2) t = -(1 / 2) := by
  have hf : (fun s : ℝ => 1 - s / 2) = (fun s : ℝ => 1 + (-(1 / 2)) * s) := by
    funext s; ring
  rw [hf]
  exact (hasDerivAt_affine t).deriv

/-- Differentiability in `t` of the normalised modulation `λ̄(t) = 1 - t/2` (finding G:
`λ̄(0) = 1`). -/
theorem hasDerivAt_lamStd (t : ℝ) :
    HasDerivAt (fun s : ℝ => 1 - s / 2) (deriv (fun s : ℝ => 1 - s / 2) t) t := by
  rw [hderivval t]
  have hf : (fun s : ℝ => 1 - s / 2) = (fun s : ℝ => 1 + (-(1 / 2)) * s) := by
    funext s; ring
  rw [hf]
  exact hasDerivAt_affine t

/-- **The profile/modulation interface is inhabited** by the explicit self-similar data with the
zero perturbation, `T = 2`, `λ̄(t) = 1 - t/2` (so `λ̄(0) = 1`, the design's normalisation and
finding G's consistency condition for the datum), `M = 20·profExp α`, `M₁ = 10·profExp α`,
`K = 1/2`, `Cg = Cg' = 0` and `L = 4^{1/profExp α} + 1`. -/
theorem profileData_inhabited {α : NNReal} (hα : 0 < (α : ℝ)) (hα13 : (α : ℝ) ≤ 1 / 3) :
    ∃ D : Work.ConstructionInstance.ProfileData α,
      D.g = (fun _ _ => (0 : ℝ)) ∧ D.T = 2 ∧
        D.M = 20 * Work.ConstructionInstance.profExp α ∧
          D.M₁ = 10 * Work.ConstructionInstance.profExp α ∧ D.K = 1 / 2 ∧ D.Cg = 0 ∧ D.Cg' = 0 ∧
            D.L = (4 : ℝ) ^ (1 / Work.ConstructionInstance.profExp α) + 1 ∧
              (∀ t : ℝ, D.lam t = 1 - t / 2) := by
  have hp : 0 < profExp α := profExp_pos hα
  have hp1 : profExp α ≤ 1 := by rw [profExp]; linarith
  have hc : (1 : ℝ) / 10 ≤ Work.Spaces.c (profExp α) := (Work.Spaces.c_bounds (profExp α) hp hp1).1
  have hGamnn : 0 ≤ Work.Spaces.Gam (profExp α) (Real.pi / 4) := by
    rw [← Gamma_div_three]
    exact Gamma_nonneg ⟨by positivity, by linarith [Real.pi_pos]⟩
  have hsmall' : (0 : ℝ) ≤ profExp α * Work.Spaces.Gam (profExp α) (Real.pi / 4)
      / (4 * Work.Spaces.c (profExp α)) :=
    div_nonneg (mul_nonneg hp.le hGamnn) (by linarith)
  have hrpowpos : 0 < (4 : ℝ) ^ (1 / profExp α) :=
    Real.rpow_pos_of_pos (by norm_num) _
  refine ⟨{ hα := hα
            g := gZero
            hvt := ⟨fun z => rfl, fun z => rfl⟩
            hsmooth := smoothNbhd_gZero
            hquad0 := fun θ => rfl
            hquad := fun θ => pz_gZero 0 θ
            Cg := 0
            hCg := le_refl 0
            hdec := decayInZ_gZero 2
            hmem := HkMem_gZero (profExp α) 2
            hCgbig := by rw [HkNorm_gZero]; simp
            Cv := 0
            hCv := le_refl 0
            hvan := by intro z θ hz hθ; simp
            Lg := 0
            hLg := le_refl 0
            hzk := by intro z z' θ hz hz' hθ; simp
            Lθ := 0
            hLθ := le_refl 0
            hzth := by intro z θ θ' hz hθ hθ'; simp
            Cg' := 0
            hg2 := by intro z θ hz hθ; rw [pz_gZero]; simp
            hgdiff := fun z θ hz => hasDerivAt_profile_zero (p := profExp α) hz
            hsmall := hsmall'
            hmeasP := aestronglyMeasurable_profile_gZero hp.le
            hα13 := hα13
            T := 2
            hT := by norm_num
            lam := fun t : ℝ => 1 - t / 2
            hlam := fun t ht => by linarith [ht.2]
            hlam0 := by norm_num
            K := 1 / 2
            hK := by norm_num
            hK12 := le_refl (1 / 2)
            hlamdif := fun t _ => hasDerivAt_lamStd t
            hlamd := fun t _ => by rw [hderivval t]; norm_num
            hlam_le := fun t ht => by linarith [ht.2]
            hlam_low := fun t ht => le_of_eq (by ring)
            L := (4 : ℝ) ^ (1 / profExp α) + 1
            hL := by linarith
            hLbig := by
              have h : (2 * (2 : ℝ)) = 4 := by norm_num
              rw [h]
              exact le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 1)
            M := 20 * profExp α
            hM := mul_nonneg (by norm_num) hp.le
            hMprof := by simp
            M₁ := 10 * profExp α
            hM₁ := mul_nonneg (by norm_num) hp.le
            hM₁big := by linarith
            R := 2 * ((4 : ℝ) ^ (1 / profExp α) + 1)
            hR := by linarith
            hRbig := le_refl _ },
          rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun t => rfl⟩

end Work.ConstructionInstance
