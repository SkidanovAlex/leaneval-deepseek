import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.Construction.Defs
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Jet convergence of the singular part `Θ = (1/(4α)) sin(2θ) L₁₂(F)`

The function `Θ` (`Work.Construction.Theta`) is a product of a function of `z` alone,
`L₁₂ F`, and a function of `θ` alone, `(1/(4α)) sin(2θ)`.  The operators `D_z = z ∂_z` and
`D_θ = sin(2θ) ∂_θ` respect this splitting: `D_z` differentiates only the `z`-factor and `D_θ`
only the `θ`-factor.  Hence for every `j, i`

  `mixed j i (Θ α F) z θ = (D_θ^i ((1/(4α)) sin(2·))) θ · (D_z^j (L₁₂ F)) (z, 0)`,

the angular factor being independent of the family `F`.  Consequently, if the `j`-th `D_z`-jets
of `L₁₂ (F n)` converge to those of `L₁₂ G` for `j ≤ 3` (the hypothesis `hL12`), then all mixed
jets `mixed j i (Θ α (F n)) z θ` with `j + i ≤ 3` converge as well: the `n`-dependence sits
entirely in the second factor.

The proof of the factorisation goes through the one-variable iterates `DzIter1`, `DthIter1` of
`z ∂_z` and `sin(2θ) ∂_θ` (the type of a one-variable function is enough once the other variable
is known to be untouched), exactly as in `GalBasis/cc/psiCut_mixed_factor.lean`.
-/

namespace Work.FTS_RegExport.RXT.velPertAux

open Filter

noncomputable section

/-! ## The one-variable operators `z ∂_z` and `sin(2θ) ∂_θ` -/

/-- The `j`-th iterate of the one-variable operator `f ↦ (z ↦ z f'(z))`, the `z`-part of `D_z`. -/
def DzIter1 : ℕ → (ℝ → ℝ) → (ℝ → ℝ)
  | 0, f => f
  | n + 1, f => fun z => z * deriv (DzIter1 n f) z

/-- The `i`-th iterate of the one-variable operator `f ↦ (θ ↦ sin(2θ) f'(θ))`, the `θ`-part of
`D_θ`. -/
def DthIter1 : ℕ → (ℝ → ℝ) → (ℝ → ℝ)
  | 0, f => f
  | n + 1, f => fun θ => Real.sin (2 * θ) * deriv (DthIter1 n f) θ

/-! ## `D_z^j` and `D_θ^i` of a function of a single variable -/

/-- `D_z^j` applied to a function of `z` alone is the one-variable iterate `DzIter1`. -/
theorem DzIter_const (j : ℕ) (a : ℝ → ℝ) :
    Work.Spaces.DzIter j (fun z' (_ : ℝ) => a z') = fun z _ => DzIter1 j a z := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [Work.Spaces.DzIter_succ, ih]
    funext z θ
    simp only [Work.Spaces.Dz, Work.Spaces.pz]
    rfl

/-- `D_θ^i` applied to a function of `θ` alone is the one-variable iterate `DthIter1`. -/
theorem DthIter_const (i : ℕ) (b : ℝ → ℝ) :
    Work.Spaces.DthIter i (fun (_ : ℝ) θ' => b θ') = fun _ θ => DthIter1 i b θ := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [Work.Spaces.DthIter_succ, ih]
    funext z θ
    simp only [Work.Spaces.Dth, Work.Spaces.pth]
    rfl

/-! ## `D_z^j` and `D_θ^i` of a separated product -/

/-- `D_z^j` of a separated product only differentiates the `z`-factor. -/
theorem DzIter_mul_sep (j : ℕ) (a b : ℝ → ℝ) :
    Work.Spaces.DzIter j (fun z θ => a z * b θ) = fun z θ => DzIter1 j a z * b θ := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [Work.Spaces.DzIter_succ, ih]
    funext z θ
    simp only [Work.Spaces.Dz, Work.Spaces.pz]
    rw [deriv_mul_const_field]
    simp only [DzIter1]
    ring

/-- `D_θ^i` of a separated product only differentiates the `θ`-factor. -/
theorem DthIter_mul_sep (i : ℕ) (a b : ℝ → ℝ) :
    Work.Spaces.DthIter i (fun z θ => a z * b θ) = fun z θ => a z * DthIter1 i b θ := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [Work.Spaces.DthIter_succ, ih]
    funext z θ
    simp only [Work.Spaces.Dth, Work.Spaces.pth]
    rw [deriv_const_mul_field]
    simp only [DthIter1]
    ring

/-- The mixed jets of a separated product `(z,θ) ↦ a z * b θ` factorise. -/
theorem mixed_mul_sep (j i : ℕ) (a b : ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.mixed j i (fun z θ => a z * b θ) z θ
      = DthIter1 i b θ * Work.Spaces.DzIter j (fun z' (_ : ℝ) => a z') z 0 := by
  have h4 : Work.Spaces.DthIter i (fun z θ => a z * b θ) = fun z θ => a z * DthIter1 i b θ :=
    DthIter_mul_sep i a b
  have h3 : Work.Spaces.DzIter j (fun z θ => a z * DthIter1 i b θ)
      = fun z θ => DzIter1 j a z * DthIter1 i b θ := DzIter_mul_sep j a (DthIter1 i b)
  have h1 : Work.Spaces.DzIter j (fun z' (_ : ℝ) => a z') z 0 = DzIter1 j a z :=
    congrFun (congrFun (DzIter_const j a) z) 0
  change Work.Spaces.DzIter j (Work.Spaces.DthIter i (fun z θ => a z * b θ)) z θ = _
  rw [h4, h3, h1]
  ring

/-- `Θ α F` is the separated product of `L₁₂ F` (in `z`) and `(1/(4α)) sin(2θ)` (in `θ`). -/
theorem theta_eq_sep (α : ℝ) (F : ℝ → ℝ → ℝ) :
    Work.Construction.Theta α F
      = fun z θ => Work.Construction.L12 F z * ((1 / (4 * α)) * Work.Construction.s2 θ) := by
  funext z θ
  simp only [Work.Construction.Theta]
  ring

/-- The factorisation of the mixed jets of `Θ`: the angular factor is `F`-independent and the
`F`-dependence is the pure radial jet of `L₁₂ F`. -/
theorem theta_mixed_factor (α : ℝ) (F : ℝ → ℝ → ℝ) (j i : ℕ) (z θ : ℝ) :
    Work.Spaces.mixed j i (Work.Construction.Theta α F) z θ
      = DthIter1 i (fun θ => (1 / (4 * α)) * Work.Construction.s2 θ) θ
        * Work.Spaces.DzIter j (fun z' (_ : ℝ) => Work.Construction.L12 F z') z 0 := by
  rw [theta_eq_sep α F,
    mixed_mul_sep j i (fun z => Work.Construction.L12 F z)
      (fun θ => (1 / (4 * α)) * Work.Construction.s2 θ)]

/-! ## The convergence theorem -/

theorem thetaJetsTendsto {α : ℝ} {F : ℕ → ℝ → ℝ → ℝ} {G : ℝ → ℝ → ℝ}
    (hL12 : ∀ j : ℕ, j ≤ 3 → ∀ z : ℝ, 0 < z →
      Filter.Tendsto (fun n : ℕ =>
          Work.Spaces.DzIter j (fun z _ => Work.Construction.L12 (F n) z) z 0)
        Filter.atTop
        (nhds (Work.Spaces.DzIter j (fun z _ => Work.Construction.L12 G z) z 0))) :
    ∀ (j i : ℕ), j + i ≤ 3 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Filter.Tendsto (fun n : ℕ => Work.Spaces.mixed j i (Work.Construction.Theta α (F n)) z θ)
        Filter.atTop
        (nhds (Work.Spaces.mixed j i (Work.Construction.Theta α G) z θ)) := by
  intro j i hji z θ hz hθ hθ2
  have hj : j ≤ 3 := by omega
  have hfac : ∀ H : ℝ → ℝ → ℝ,
      Work.Spaces.mixed j i (Work.Construction.Theta α H) z θ
        = DthIter1 i (fun θ => (1 / (4 * α)) * Work.Construction.s2 θ) θ
          * Work.Spaces.DzIter j (fun z' _ => Work.Construction.L12 H z') z 0 :=
    fun H => theta_mixed_factor α H j i z θ
  have h := (hL12 j hj z hz).const_mul
    (DthIter1 i (fun θ => (1 / (4 * α)) * Work.Construction.s2 θ) θ)
  simpa only [hfac] using h

end

end Work.FTS_RegExport.RXT.velPertAux
