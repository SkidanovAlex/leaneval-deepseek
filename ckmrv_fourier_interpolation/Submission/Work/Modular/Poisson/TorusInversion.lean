import Mathlib
import Submission.Work.Modular.Poisson.Std

/-!
# Fourier inversion on the torus for periodic functions on `ℝ^ι`

If `F : (ι → ℝ) → ℂ` is continuous and periodic under the integer lattice `ℤ^ι`, then `F`
descends to a continuous function on `UnitAddTorus ι`, and the Fourier inversion theorem for
Fourier series on the torus gives

`F 0 = ∑' k : ι → ℤ, ∫ x in (0,1]^ι, mFourier (-k) (projTorus x) • F x`.
-/

noncomputable section

open scoped FourierTransform SchwartzMap
open MeasureTheory

namespace Work.Modular

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A representative of a point of the torus in the cube `(0,1]^ι`. -/
def torusLift (t : UnitAddTorus ι) : ι → ℝ := fun i => (AddCircle.equivIoc (1:ℝ) 0 (t i)).1

lemma projTorus_torusLift (t : UnitAddTorus ι) : projTorus (torusLift t) = t := by
  funext i
  simp [projTorus, torusLift]

lemma isOpenQuotientMap_projTorus : IsOpenQuotientMap (projTorus (ι := ι)) := by
  have h : projTorus (ι := ι) = Pi.map (fun _ : ι => ((↑) : ℝ → UnitAddCircle)) := rfl
  rw [h]
  exact IsOpenQuotientMap.piMap fun _ => QuotientAddGroup.isOpenQuotientMap_mk

/-- Two points of `ℝ^ι` with the same image in the torus differ by an integer vector. -/
lemma exists_intVec_eq_of_projTorus_eq {x y : ι → ℝ}
    (h : projTorus x = projTorus y) : ∃ m : ι → ℤ, y = x + intVec m := by
  have hi : ∀ i, ∃ k : ℤ, y i = x i + k := fun i => by
    have h1 : ((y i : UnitAddCircle)) = ((x i : UnitAddCircle)) := by
      have := congrFun h i
      simpa [projTorus] using this.symm
    rw [QuotientAddGroup.eq_iff_sub_mem] at h1
    obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp h1
    refine ⟨k, ?_⟩
    have hk' : (k : ℝ) = y i - x i := by
      rw [← hk]; simp
    rw [hk']; ring
  choose m hm using hi
  exact ⟨m, funext fun i => by rw [hm i]; simp [intVec]⟩

variable {F : (ι → ℝ) → ℂ}

/-- **Fourier inversion on the torus** for a continuous `ℤ^ι`-periodic function. -/
theorem hasSum_mFourier_series_of_periodic (hF : Continuous F)
    (hper : ∀ (x : ι → ℝ) (m : ι → ℤ), F (x + intVec m) = F x)
    (hsum : Summable fun k : ι → ℤ =>
      ∫ x in unitCube, UnitAddTorus.mFourier (-k) (projTorus x) • F x) :
    F 0 = ∑' k : ι → ℤ, ∫ x in unitCube, UnitAddTorus.mFourier (-k) (projTorus x) • F x := by
  set Q : UnitAddTorus ι → ℂ := fun t => F (torusLift t) with hQdef
  have hQF : ∀ x, Q (projTorus x) = F x := by
    intro x
    obtain ⟨m, hm⟩ := exists_intVec_eq_of_projTorus_eq (projTorus_torusLift (projTorus x))
    simp only [hQdef]
    conv_rhs => rw [hm]
    rw [hper]
  have hQcont : Continuous Q := by
    refine (isOpenQuotientMap_projTorus.isQuotientMap.continuous_iff).mpr ?_
    have : Q ∘ projTorus = F := funext hQF
    rw [this]
    exact hF
  let Qc : C(UnitAddTorus ι, ℂ) := ⟨Q, hQcont⟩
  have hcoeff : ∀ k : ι → ℤ, UnitAddTorus.mFourierCoeff (Qc : UnitAddTorus ι → ℂ) k =
      ∫ x in unitCube, UnitAddTorus.mFourier (-k) (projTorus x) • F x := by
    intro k
    rw [UnitAddTorus.mFourierCoeff_eq_integral Qc k (fun _ => (0:ℝ))]
    rw [show {x : ι → ℝ | ∀ i, x i ∈ Set.Ioc ((fun _ => (0:ℝ)) i) ((fun _ => (0:ℝ)) i + 1)}
        = unitCube from by
      ext x; simp [unitCube]]
    refine setIntegral_congr_fun (measurableSet_unitCube) ?_
    intro x _
    change UnitAddTorus.mFourier (-k) (fun i => (x i : UnitAddCircle)) •
        Q (fun i => (x i : UnitAddCircle))
      = UnitAddTorus.mFourier (-k) (projTorus x) • F x
    rw [show (fun i => (x i : UnitAddCircle)) = projTorus x from rfl]
    exact congrArg (fun z => UnitAddTorus.mFourier (-k) (projTorus x) • z) (hQF x)
  have hsum' : Summable (UnitAddTorus.mFourierCoeff (Qc : UnitAddTorus ι → ℂ)) := by
    rw [show (UnitAddTorus.mFourierCoeff (Qc : UnitAddTorus ι → ℂ)) =
      (fun k : ι → ℤ => ∫ x in unitCube, UnitAddTorus.mFourier (-k) (projTorus x) • F x)
      from funext hcoeff]
    exact hsum
  have hser := UnitAddTorus.hasSum_mFourier_series_apply_of_summable hsum' (0 : UnitAddTorus ι)
  have hzero : ∀ k : ι → ℤ, (UnitAddTorus.mFourier k) (0 : UnitAddTorus ι) = 1 := by
    intro k
    simp [UnitAddTorus.mFourier, fourier_eval_zero]
  rw [show (fun k : ι → ℤ => UnitAddTorus.mFourierCoeff (Qc : UnitAddTorus ι → ℂ) k •
        (UnitAddTorus.mFourier k) (0 : UnitAddTorus ι)) =
      (fun k : ι → ℤ => UnitAddTorus.mFourierCoeff (Qc : UnitAddTorus ι → ℂ) k) from
    funext fun k => by rw [hzero k, smul_eq_mul, mul_one]] at hser
  have h1 : (∑' k : ι → ℤ, UnitAddTorus.mFourierCoeff (Qc : UnitAddTorus ι → ℂ) k) = Qc 0 :=
    hser.tsum_eq
  have h2 : Qc 0 = F 0 := by
    have h00 : (0 : UnitAddTorus ι) = projTorus (0 : ι → ℝ) := by
      funext i; simp [projTorus]
    have : Qc (projTorus (0 : ι → ℝ)) = F 0 := hQF 0
    rw [← h00] at this
    exact this
  rw [h2] at h1
  rw [← h1]
  exact tsum_congr fun k => hcoeff k

end Work.Modular
