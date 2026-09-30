import Mathlib
import Submission.Work.BW.DefsMult

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- Determinant of the square submatrix of `M` whose columns are the (distinct) columns `c b` of
`J`: it equals `± minorJ M J hJ`. -/
theorem det_cols_eq_sign_minorJ {ρ r : ℕ} (M : Fin ρ → Fin r → ℤ) {J : Finset (Fin r)}
    (hJ : J.card = ρ) {c : Fin ρ → Fin r} (hc : Function.Injective c) (hcJ : ∀ b, c b ∈ J) :
    ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧
      Matrix.det (fun a b => (M a (c b) : ℝ)) = ε * ((minorJ M J hJ : ℤ) : ℝ) := by
  classical
  -- `c` is an injection from `Fin ρ` into `J`, hence (finite equal cardinals) a bijection onto `J`.
  let f : Fin ρ → ↥J := fun b => ⟨c b, hcJ b⟩
  have hf_inj : Function.Injective f := fun a b h => hc (Subtype.ext_iff.mp h)
  -- the permutation of `Fin ρ` that reorders the increasing enumeration of `J` into `c`.
  let σ : Equiv.Perm (Fin ρ) :=
    Equiv.ofBijective (fun b => (J.orderIsoOfFin hJ).symm (f b))
      ⟨fun a b h => hf_inj ((J.orderIsoOfFin hJ).symm.injective h),
        Finite.injective_iff_surjective.mp
          (fun a b h => hf_inj ((J.orderIsoOfFin hJ).symm.injective h))⟩
  have hσ : ∀ b, J.orderEmbOfFin hJ (σ b) = c b := by
    intro b
    have h1 : (J.orderIsoOfFin hJ) (σ b) = f b := by
      show (J.orderIsoOfFin hJ) ((J.orderIsoOfFin hJ).symm (f b)) = f b
      exact OrderIso.apply_symm_apply _ _
    have h2 := congrArg Subtype.val h1
    simpa [f] using h2
  -- the matrix of the `J.orderEmbOfFin`-indexed columns, over `ℤ` and over `ℝ`.
  let M' : Matrix (Fin ρ) (Fin ρ) ℤ := fun a b => M a (J.orderEmbOfFin hJ b)
  let A : Matrix (Fin ρ) (Fin ρ) ℝ := fun a b => (M a (J.orderEmbOfFin hJ b) : ℝ)
  have hB : (fun a b => (M a (c b) : ℝ)) = A.submatrix id σ := by
    ext a b
    rw [Matrix.submatrix_apply]
    show (M a (c b) : ℝ) = (M a (J.orderEmbOfFin hJ (σ b)) : ℝ)
    rw [hσ b]
  have hmin : minorJ M J hJ = M'.det := rfl
  have hA : A.det = ((minorJ M J hJ : ℤ) : ℝ) := by
    rw [hmin, Int.cast_det]
    rfl
  refine ⟨(Equiv.Perm.sign σ : ℝ), ?_, ?_⟩
  · -- the sign of a permutation of `ℤ` is `±1`.
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
    · left; rw [h]; simp
    · right; rw [h]; norm_num
  · rw [hB, Matrix.det_permute', hA]

end Work.BW
