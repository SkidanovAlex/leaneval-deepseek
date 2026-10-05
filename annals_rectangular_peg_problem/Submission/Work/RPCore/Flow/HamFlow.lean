import Submission.Work.RPCore.Defs
import Submission.Work.RPCore.Flow.Basic
import Submission.Work.RPCore.Flow.clampedField_bounds
import Submission.Work.RPCore.Flow.contDiff_flow_timeSlice_le
import Submission.Work.RPCore.Flow.flow_variational_eq
import Submission.Work.RPCore.Flow.symp_hamVF_fderiv
import Submission.Work.RPCore.Flow.exists_clamp

/-!
# C0: the Hamiltonian flow of a compactly supported periodic Hamiltonian

The Hamiltonian `H : ℝ → PS → ℝ` of `CptPerHam` is `C⁴` in `(t,x)`, `2π`-periodic in `q₂` and
supported in the slab `{|q₁|+|p₁|+|p₂| ≥ R}`, but its bounds may depend on `t` in an uncontrolled
way.  To obtain a flow with uniform bounds we clamp the time variable: `ψ` is a smooth clamp
(`ψ t = t` on `[-1,2]`, `ψ` and `deriv ψ` bounded — `exists_clamp`), and `clampHam H = H ∘ ψ`.  The
autonomous field `clampedField H = autoVF (clampHam H)` on `ℝ × PS` then has global bounds, and its
flow, read in the second factor, agrees with the genuine time-dependent flow of `H` on `[-1,2]`.

Main contents:

* `clampPsi`, `clampHam`, `clampedField`, `clampedData`, `clampFlow` (the flow of the clamped
  field),
* `Phi` : the two-time flow `Φ a b x` of `H` (for `a,b ∈ [-1,2]` this is the genuine flow),
* `Phi_self`, `Phi_add`, `Phi_isFlow`, and the companion statements `Phi_contDiff`,
  `Phi_symplectic`, `Phi_nearId`, `Phi_slab`, `Phi_Tk` (in `Flow/HamFlowProps.lean`).
-/

open RectangularPegProblem Manifold Complex Real
open scoped ContDiff

set_option autoImplicit false

noncomputable section

namespace Work.RPCore

open Work.RPV

/-! ## The time clamp -/

/-- A smooth clamp: the identity on `[-1,2]`, with bounded value and bounded derivative. -/
noncomputable def clampPsi : ℝ → ℝ := Classical.choose Work.RPCore.Flow.exists_clamp

theorem clampPsi_contDiff : ContDiff ℝ 4 clampPsi := (Classical.choose_spec Work.RPCore.Flow.exists_clamp).1

theorem clampPsi_self {t : ℝ} (ht : t ∈ Set.Icc (-1 : ℝ) 2) : clampPsi t = t :=
  (Classical.choose_spec Work.RPCore.Flow.exists_clamp).2.1 t ht

theorem clampPsi_bound : ∃ B : ℝ, ∀ t, |clampPsi t| ≤ B :=
  (Classical.choose_spec Work.RPCore.Flow.exists_clamp).2.2.1

theorem clampPsi_deriv_bound : ∃ B' : ℝ, ∀ t, |deriv clampPsi t| ≤ B' :=
  (Classical.choose_spec Work.RPCore.Flow.exists_clamp).2.2.2

/-- The time-clamped Hamiltonian: it agrees with `H` on `[-1,2]` and has uniform bounds. -/
noncomputable def clampHam (Hh : CptPerHam) : ℝ → PS → ℝ := fun t x => Hh.H (clampPsi t) x

/-- The autonomous vector field `(1, X_H)` of the time-clamped Hamiltonian. -/
noncomputable def clampedField (Hh : CptPerHam) : ℝ × PS → ℝ × PS := autoVF (clampHam Hh)

theorem clampedField_contDiff_three (Hh : CptPerHam) : ContDiff ℝ 3 (clampedField Hh) :=
  (Work.RPCore.Flow.clampedField_bounds Hh clampPsi clampPsi_contDiff clampPsi_bound clampPsi_deriv_bound).1

theorem clampedField_bound_exists (Hh : CptPerHam) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z, ‖clampedField Hh z‖ ≤ M :=
  (Work.RPCore.Flow.clampedField_bounds Hh clampPsi clampPsi_contDiff clampPsi_bound clampPsi_deriv_bound).2.1

theorem clampedField_fderiv_bound_exists (Hh : CptPerHam) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ z, ‖fderiv ℝ (clampedField Hh) z‖ ≤ K :=
  (Work.RPCore.Flow.clampedField_bounds Hh clampPsi clampPsi_contDiff clampPsi_bound clampPsi_deriv_bound).2.2

/-- The bounds of the clamped field, chosen once and for all. -/
structure ClampedData (Hh : CptPerHam) where
  M : ℝ
  hM₀ : 0 ≤ M
  hM : ∀ z, ‖clampedField Hh z‖ ≤ M
  K : ℝ
  hK₀ : 0 ≤ K
  hK : ∀ z, ‖fderiv ℝ (clampedField Hh) z‖ ≤ K

theorem clampedData_exists (Hh : CptPerHam) : Nonempty (ClampedData Hh) :=
  let ⟨M, hM⟩ := clampedField_bound_exists Hh
  let ⟨K, hK⟩ := clampedField_fderiv_bound_exists Hh
  ⟨⟨M, hM.1, hM.2, K, hK.1, hK.2⟩⟩

/-- Canonical choice of the bounds. -/
noncomputable def clampedData (Hh : CptPerHam) : ClampedData Hh :=
  Classical.choice (clampedData_exists Hh)

theorem clampedField_lipschitz (Hh : CptPerHam) :
    LipschitzWith (clampedData Hh).K.toNNReal (clampedField Hh) :=
  lipschitzWith_of_nnnorm_fderiv_le
    ((clampedField_contDiff_three Hh).differentiable (by norm_num)) (fun z => by
      rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ (clampedData Hh).hK₀]
      exact (clampedData Hh).hK z)

/-- The global flow of the clamped field (an autonomous flow on `ℝ × PS`). -/
noncomputable def clampFlow (Hh : CptPerHam) : ℝ → (ℝ × PS) → (ℝ × PS) :=
  flowOf (clampedField Hh) (clampedField_lipschitz Hh) (clampedData Hh).hM

theorem clampFlow_zero (Hh : CptPerHam) (z : ℝ × PS) : clampFlow Hh 0 z = z :=
  flowOf_zero (clampedField Hh) (clampedField_lipschitz Hh) (clampedData Hh).hM z

theorem clampFlow_add (Hh : CptPerHam) (s t : ℝ) (z : ℝ × PS) :
    clampFlow Hh (s + t) z = clampFlow Hh s (clampFlow Hh t z) :=
  flowOf_add (clampedField Hh) (clampedField_lipschitz Hh) (clampedData Hh).hM s t z

theorem clampFlow_curve (Hh : CptPerHam) (z : ℝ × PS) :
    IsIntegralCurve (fun t => clampFlow Hh t z) (fun _ y => clampedField Hh y) :=
  flowOf_isIntegralCurve (clampedField Hh) (clampedField_lipschitz Hh) (clampedData Hh).hM z

/-- The first coordinate of a derivative into a product. -/
lemma hasDerivAt_fst {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → ℝ × E} {d : ℝ × E} {t : ℝ} (h : HasDerivAt f d t) :
    HasDerivAt (fun s => (f s).1) d.1 t := by
  have hfd : HasFDerivAt f (ContinuousLinearMap.toSpanSingleton ℝ d) t := h.hasFDerivAt
  have := (hasFDerivAt_iff_hasDerivAt).mp hfd.fst
  simpa using this

/-- The second coordinate of a derivative into a product. -/
lemma hasDerivAt_snd {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → ℝ × E} {d : ℝ × E} {t : ℝ} (h : HasDerivAt f d t) :
    HasDerivAt (fun s => (f s).2) d.2 t := by
  have hfd : HasFDerivAt f (ContinuousLinearMap.toSpanSingleton ℝ d) t := h.hasFDerivAt
  have := (hasFDerivAt_iff_hasDerivAt).mp hfd.snd
  simpa using this

theorem clampFlow_fst (Hh : CptPerHam) (t : ℝ) (z : ℝ × PS) : (clampFlow Hh t z).1 = z.1 + t := by
  have h₁ : IsIntegralCurve (fun r : ℝ => (clampFlow Hh r z).1) (fun _ y : ℝ => 1) := fun s =>
    hasDerivAt_fst (clampFlow_curve Hh z s)
  have h₂ : IsIntegralCurve (fun r : ℝ => z.1 + r) (fun _ y : ℝ => 1) := fun s =>
    (hasDerivAt_id s).const_add z.1
  have h := Port.ODE.eq_of_isIntegralCurve (X := fun _ : ℝ => 1) (L := 0)
    (LipschitzWith.const (1 : ℝ)) h₁ h₂ (t := 0) (by simp [clampFlow_zero])
  exact congrFun h t

/-- The two-time flow of `H`: `Φ a b x` is the value at time `b` of the solution starting from `x`
at time `a`.  For `a, b ∈ [-1,2]` this is the genuine time-dependent Hamiltonian flow of `H`. -/
noncomputable def Phi (Hh : CptPerHam) (a b : ℝ) (x : PS) : PS :=
  (clampFlow Hh (b - a) (a, x)).2

theorem Phi_self (Hh : CptPerHam) (a : ℝ) (x : PS) : Phi Hh a a x = x := by
  simp [Phi, clampFlow_zero, sub_self]

/-- On the clamp interval the clamped Hamiltonian is the original one. -/
theorem clampHam_self (Hh : CptPerHam) {t : ℝ} (ht : t ∈ Set.Icc (-1 : ℝ) 2) :
    clampHam Hh t = Hh.H t := by
  funext x
  simp [clampHam, clampPsi_self ht]

theorem Phi_add (Hh : CptPerHam) (a b c : ℝ) (x : PS) :
    Phi Hh b c (Phi Hh a b x) = Phi Hh a c x := by
  have h1 : (clampFlow Hh (b - a) (a, x)).1 = b := by
    rw [clampFlow_fst]; ring
  have hZm : clampFlow Hh (b - a) (a, x)
      = (b, (clampFlow Hh (b - a) (a, x)).2) := Prod.ext h1 rfl
  simp only [Phi]
  rw [← hZm, ← clampFlow_add Hh (c - b) (b - a) (a, x),
    show (c - b) + (b - a) = c - a by ring]

theorem Phi_isFlow (Hh : CptPerHam) (a : ℝ) (x : PS) :
    ∀ t ∈ Set.Icc (-1 : ℝ) 2,
      HasDerivAt (fun s => Phi Hh a s x) (hamVF (Hh.H t) (Phi Hh a t x)) t := by
  intro t ht
  have hcomp : HasDerivAt (fun s : ℝ => clampFlow Hh (s - a) (a, x))
      (clampedField Hh (clampFlow Hh (t - a) (a, x))) t :=
    (clampFlow_curve Hh (a, x)).comp_add (-a) t
  have hsnd := hasDerivAt_snd hcomp
  have hval : (clampedField Hh (clampFlow Hh (t - a) (a, x))).2
      = hamVF (Hh.H t) (Phi Hh a t x) := by
    have h1 : (clampFlow Hh (t - a) (a, x)).1 = t := by
      rw [clampFlow_fst]; ring
    show hamVF (clampHam Hh (clampFlow Hh (t - a) (a, x)).1)
        (clampFlow Hh (t - a) (a, x)).2 = hamVF (Hh.H t) (Phi Hh a t x)
    rw [h1, clampHam_self Hh ht]
    rfl
  rw [hval] at hsnd
  simpa only [Phi] using hsnd

end Work.RPCore
