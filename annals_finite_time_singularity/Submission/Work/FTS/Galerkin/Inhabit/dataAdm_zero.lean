import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.GalerkinFix.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Galerkin.Inhabit

/-! ## Elementary facts about the identically zero profile

Every operator occurring in `Work.Spaces.HkIntegrand`, `Work.Spaces.DecayInZ`,
`Work.Spaces.DecayMixed` and in the `L₁₂`-clause of `Work.Coercivity.HkAdm` is built from
`∂_z`, `∂_θ` and multiplications by functions of the variables alone, hence maps the zero
profile to itself; consequently all the required integrands vanish identically, all the
required iterated derivatives are the zero function (whose integrals along `z → ∞` tend to
`0` trivially), and `L₁₂(0) = 0`.  The helpers below record this, and the target theorem is
then immediate. -/

/-- `∂_z 0 = 0`. -/
private theorem zeroF_pz : Work.Spaces.pz (fun _ _ : ℝ => (0 : ℝ)) = fun _ _ => 0 := by
  funext z θ; simp [Work.Spaces.pz]

/-- `∂_θ 0 = 0`. -/
private theorem zeroF_pth : Work.Spaces.pth (fun _ _ : ℝ => (0 : ℝ)) = fun _ _ => 0 := by
  funext z θ; simp [Work.Spaces.pth]

/-- Every iterated `∂_z` of the zero profile vanishes. -/
private theorem zeroF_pzIter (j : ℕ) :
    Work.Spaces.pzIter j (fun _ _ : ℝ => (0 : ℝ)) = fun _ _ => 0 := by
  induction j with
  | zero => rfl
  | succ n ih => rw [Work.Spaces.pzIter_succ, ih]; funext z θ; simp [Work.Spaces.pz]

/-- Every iterated `∂_θ` of the zero profile vanishes. -/
private theorem zeroF_pthIter (i : ℕ) :
    Work.Spaces.pthIter i (fun _ _ : ℝ => (0 : ℝ)) = fun _ _ => 0 := by
  induction i with
  | zero => rfl
  | succ n ih => rw [Work.Spaces.pthIter_succ, ih]; funext z θ; simp [Work.Spaces.pth]

/-- Every iterated `D_z` of the zero profile vanishes. -/
private theorem zeroF_DzIter (i : ℕ) :
    Work.Spaces.DzIter i (fun _ _ : ℝ => (0 : ℝ)) = fun _ _ => 0 := by
  induction i with
  | zero => rfl
  | succ n ih =>
      rw [Work.Spaces.DzIter_succ, ih]
      funext z θ
      simp [Work.Spaces.Dz, Work.Spaces.pz]

/-- Every iterated `D_θ` of the zero profile vanishes. -/
private theorem zeroF_DthIter (i : ℕ) :
    Work.Spaces.DthIter i (fun _ _ : ℝ => (0 : ℝ)) = fun _ _ => 0 := by
  induction i with
  | zero => rfl
  | succ n ih =>
      rw [Work.Spaces.DthIter_succ, ih]
      funext z θ
      simp [Work.Spaces.Dth, Work.Spaces.pth]

/-- Every mixed `D`-derivative of the zero profile vanishes. -/
private theorem zeroF_mixed (j i : ℕ) :
    Work.Spaces.mixed j i (fun _ _ : ℝ => (0 : ℝ)) = fun _ _ => 0 := by
  simp only [Work.Spaces.mixed, zeroF_DthIter, zeroF_DzIter]

/-- The `ℋ^k`-integrand of the zero profile vanishes identically. -/
private theorem zeroF_HkIntegrand (α : ℝ) (k : ℕ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α k (fun _ _ : ℝ => (0 : ℝ)) z θ = 0 := by
  rw [Work.Spaces.HkIntegrand]
  simp [zeroF_DzIter, zeroF_mixed]

/-- The zero profile lies in `ℋ^k` for every `k`: its integrand is the zero function, which is
integrable on every set. -/
private theorem zeroF_HkMem (α : ℝ) (k : ℕ) :
    Work.Spaces.HkMem α k (fun _ _ : ℝ => (0 : ℝ)) := by
  constructor
  · intro z _
    have h : (fun θ : ℝ => Work.Spaces.HkIntegrand α k (fun _ _ : ℝ => (0 : ℝ)) z θ)
        = fun _ => (0 : ℝ) := by
      funext θ; exact zeroF_HkIntegrand α k z θ
    rw [h]
    exact MeasureTheory.integrableOn_zero
  · have h : (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α k (fun _ _ : ℝ => (0 : ℝ)) z θ) = fun _ => (0 : ℝ) := by
      funext z; simp [zeroF_HkIntegrand]
    rw [h]
    exact MeasureTheory.integrableOn_zero

/-- `L₁₂` of the zero profile vanishes. -/
private theorem zeroF_L12f (z : ℝ) :
    Work.Coercivity.L12f (fun _ _ : ℝ => (0 : ℝ)) z = 0 := by
  simp [Work.Coercivity.L12f, Work.FM.L12, Work.FM.L12dens]

/-- The zero profile is smooth on a neighbourhood of the closed quadrant. -/
private theorem zeroF_SmoothNbhd : Work.Spaces.SmoothNbhd (fun _ _ : ℝ => (0 : ℝ)) := by
  show ContDiffOn ℝ ⊤ (Function.uncurry (fun _ _ : ℝ => (0 : ℝ))) _
  exact contDiffOn_const

/-- The zero profile is admissible of every order `k`: it is smooth, every mixed
`D`-derivative of it lies in `ℋ^k` (it is the zero profile) and has vanishing `L₁₂`-zero-mode. -/
private theorem zeroF_HkAdm (α : ℝ) (k : ℕ) :
    Work.Coercivity.HkAdm α k (fun _ _ : ℝ => (0 : ℝ)) := by
  refine ⟨zeroF_SmoothNbhd, ?_, ?_⟩
  · intro a b _
    rw [zeroF_mixed b a]
    exact zeroF_HkMem α k
  · intro a b _
    rw [zeroF_mixed b a]
    exact zeroF_L12f 0

/-- All plain iterated derivatives of the zero profile decay at `z = ∞`. -/
private theorem zeroF_DecayInZ (n : ℕ) :
    Work.Spaces.DecayInZ n (fun _ _ : ℝ => (0 : ℝ)) := by
  intro j i _ θ _
  have h : Work.Spaces.pzIter j (Work.Spaces.pthIter i (fun _ _ : ℝ => (0 : ℝ)))
      = fun _ _ => 0 := by
    rw [zeroF_pthIter i, zeroF_pzIter j]
  rw [h]
  exact tendsto_const_nhds

/-- All mixed `D`-derivatives of the zero profile decay at `z = ∞`. -/
private theorem zeroF_DecayMixed (n : ℕ) :
    Work.Spaces.DecayMixed n (fun _ _ : ℝ => (0 : ℝ)) := by
  intro a b _ θ _
  have h : Work.Spaces.mixed b a (fun _ _ : ℝ => (0 : ℝ)) = fun _ _ => 0 :=
    zeroF_mixed b a
  rw [h]
  exact tendsto_const_nhds

/-- The zero profile vanishes on the two angular boundaries. -/
private theorem zeroF_VanishTheta : Work.Spaces.VanishTheta (fun _ _ : ℝ => (0 : ℝ)) :=
  ⟨fun _ => rfl, fun _ => rfl⟩

/-- The zero profile is `C^∞` on the open quadrant (indeed analytic on a neighbourhood). -/
private theorem zeroF_SmoothQuad : Work.FTS.LocData.SmoothQuad (fun _ _ : ℝ => (0 : ℝ)) := by
  show ContDiffOn ℝ _ (Function.uncurry (fun _ _ : ℝ => (0 : ℝ))) _
  exact contDiffOn_const

/-- The axis conditions of the zero profile. -/
private theorem zeroF_axis :
    ∀ θ ∈ Work.Spaces.Iθ, (fun _ _ : ℝ => (0 : ℝ)) 0 θ = 0 ∧
      Work.Spaces.pz (fun _ _ : ℝ => (0 : ℝ)) 0 θ = 0 := by
  intro θ _
  refine ⟨rfl, ?_⟩
  rw [zeroF_pz]

/-- `L₁₂` of the zero profile vanishes in the `Construction` convention. -/
private theorem zeroF_L12C (z : ℝ) :
    Work.Construction.L12 (fun _ _ : ℝ => (0 : ℝ)) z = 0 := by
  simp [Work.Construction.L12, Work.Construction.L12dens, Work.FM.L12, Work.FM.L12dens]

/-- The boundary traces of the zero profile vanish. -/
private theorem zeroF_BdryTraces (α : ℝ) (k : ℕ) :
    Work.FTS.Nonlin.BdryTraces α k (fun _ _ : ℝ => (0 : ℝ)) := by
  intro a b _
  constructor
  · intro θ _
    constructor
    · have h : (fun z : ℝ => z * (Work.Spaces.mixed b a (fun _ _ : ℝ => (0 : ℝ)) z θ
          * Work.Spaces.w z) ^ 2) = fun _ => (0 : ℝ) := by
        funext z
        rw [zeroF_mixed b a]
        ring
      rw [h]; exact tendsto_const_nhds
    · have h : (fun z : ℝ => z * (Work.Spaces.mixed b a (fun _ _ : ℝ => (0 : ℝ)) z θ
          * Work.Spaces.w z) ^ 2) = fun _ => (0 : ℝ) := by
        funext z
        rw [zeroF_mixed b a]
        ring
      rw [h]; exact tendsto_const_nhds
  · intro z _
    constructor
    · have h : (fun θ : ℝ => Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
          * (Work.Spaces.mixed b a (fun _ _ : ℝ => (0 : ℝ)) z θ) ^ 2) = fun _ => (0 : ℝ) := by
        funext θ
        rw [zeroF_mixed b a]
        ring
      rw [h]; exact tendsto_const_nhds
    · have h : (fun θ : ℝ => Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
          * (Work.Spaces.mixed b a (fun _ _ : ℝ => (0 : ℝ)) z θ) ^ 2) = fun _ => (0 : ℝ) := by
        funext θ
        rw [zeroF_mixed b a]
        ring
      rw [h]; exact tendsto_const_nhds

/-- **Inhabitation of the corrected `DataAdm`** (design §1.2): the identically zero datum is
admissible for every `α`.  The class is
`LocData.DataAdm α g₀ ∧ L₁₂(g₀)(0) = 0 ∧ RegQ α 5 g₀`, all four components of which hold for the
zero profile (its `ℋ^k`-integrands, its mixed derivatives and its boundary traces all vanish). -/
theorem dataAdm_zero (α : ℝ) : Work.FTS.Galerkin.DataAdm α (fun _ _ => 0) := by
  refine ⟨⟨zeroF_SmoothQuad, zeroF_VanishTheta, zeroF_axis, zeroF_HkMem α 4⟩, zeroF_L12C 0,
    zeroF_SmoothQuad, zeroF_HkMem α 5, zeroF_BdryTraces α 5⟩

end Work.FTS.Galerkin.Inhabit
