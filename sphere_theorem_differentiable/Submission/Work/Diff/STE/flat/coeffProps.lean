import Mathlib
import Submission.Work.Diff.STE.flat.coeffDefs
import Submission.Work.Diff.STE.flat.coeffA_elliptic
import Submission.Work.Diff.STE.flat.coeffA_deriv_bound
import Submission.Work.Diff.STE.flat.coeffA_smooth_periodic
import Submission.Work.Diff.STE.flat.uniqueness_energy_ineq

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.flat

/-!
## Roadmap (for the prover)

Package the properties of the *symmetrised inverse metric matrix* needed by the linear energy
argument.  `u` is (the matrix of) a solution: `reMat (u t x) =: B (t,x)` satisfies the uniform
quadratic-form lower bound `hell` with constant `lam`, so
`B.det ≠ 0` everywhere on `Ico 0 T × univ` by `Work.Diff.STE.flat.det_ne_zero_of_quadForm_le`,
and `B⁻¹` is well defined.  The coefficient of the DeTurck principal part has to be *symmetric*
(the Gårding estimate `Work.Diff.STE.flat.garding_param` requires it), so take

  `a t x c d := ((B t x)⁻¹ c d + (B t x)⁻¹ d c) / 2`.

Prove, with `tstar < T`:
* entrywise joint smoothness of `a` on `Ico 0 T ×ˢ univ`: combine `hmat` (from `hu` and
  `contDiffOn_reMat_entry`), `hdet` (from `hell`) and
  `Work.Diff.STE.flat.contDiffOn_matrixInv_entry` (all in `torus_uniqueness.lean`).
* `Periodic1 (a t)`: from `huper` by transporting `(reMat (u t ·))⁻¹` through
  `Periodic1.matrixInv_entry` and the pointwise `reMat`.
* symmetry `a t x c d = a t x d c`: by `ring`.
* the identification `a t x c d = (((reMat (u t x))⁻¹) c d + ((reMat (u t x))⁻¹) d c)/2`: `rfl`.
* ellipticity: bound the entries `‖(reMat (u t x)) i j‖ ≤ M` for `(t,x)` in the compact
  `[0,tstar] × cubeBox` (continuity on a compact set), then, for `ξ : Fin n → ℝ` and
  `v := (reMat (u t x))⁻¹ *ᵥ ξ` (so `u = B⁻¹ ξ`), use `hell` at `v`:
  `⟨B v, v⟩ = ⟨ξ, v⟩ ≥ lam * ‖v‖²`, and `‖ξ‖ = ‖B v‖ ≤ (n * M) * ‖v‖` (because
  `‖(B *ᵥ v) i‖ ≤ Σ_j ‖B i j‖ ‖v j‖ ≤ M * √n * ‖v‖`), hence
  `⟨a ξ, ξ⟩ = ⟨B⁻¹ ξ, ξ⟩ ≥ lam/(n*M)² * ‖ξ‖²`.  Note that the quadratic form of the inverse
  equals that of its symmetrisation (the antisymmetric part contributes nothing), so the bound for
  `a` follows.  Take `lam' := lam/((n:ℝ)^2 * M^2)` (any positive value works); if `M = 0` the
  hypotheses are contradictory unless `n = 0`, handle that (the `n = 0` case is trivial since all
  sums are empty).  Useful: `Work.Diff.STE.flat.sum_sum_mul_eq_dotProduct`,
  `Work.Diff.STE.flat.posSemidef_cauchy_schwarz`, `Work.Diff.STE.flat.quadForm_le_of_sphere`.
* the derivative bound `K₁`: `(t,x) ↦ pdR i (fun y => a t y c d) x` is continuous on the compact
  `[0,tstar] × cubeBox` and `1`-periodic in `x`; copy the argument of `sol_bounds`
  (`torus_uniqueness.lean`, last bullet) which does exactly this for `(reMat (u t ·))⁻¹`:
  joint smoothness via `contDiffOn_pd_slice`, the bridge
  `Work.Diff.STE.ga_pd_ofReal`, `Work.Diff.STE.cm_periodicIn_pdR`,
  `Work.Diff.STE.flat.abs_le_of_periodic1_of_cube` and
  `IsCompact.exists_bound_of_continuousOn`.
-/

theorem coeffProps {n : ℕ} (hn : 1 ≤ n)
    {T tstar : ℝ} (htstarT : tstar < T)
    (u : ℝ → Work.Diff.STE.Flat.Torus n)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × (Fin n → ℝ) => u p.1 p.2)
      (Set.Ico (0:ℝ) T ×ˢ Set.univ))
    (huper : ∀ t ∈ Set.Ico (0:ℝ) T, Work.Diff.STE.Periodic1 (u t))
    (lam : ℝ) (hlam : 0 < lam)
    (hell : ∀ t ∈ Set.Ico (0:ℝ) T, ∀ x : Fin n → ℝ, ∀ ξ : Fin n → ℝ,
      lam * ∑ i, (ξ i) ^ 2 ≤ ∑ i, ∑ j, Work.Diff.STE.Flat.reMat (u t x) i j * ξ i * ξ j) :
    ∃ (a : ℝ → (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (lam' K₁ : ℝ), 0 < lam' ∧ 0 ≤ K₁ ∧
      (∀ c d, ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × (Fin n → ℝ) => a p.1 p.2 c d)
        (Set.Ico (0:ℝ) T ×ˢ Set.univ)) ∧
      (∀ t ∈ Set.Ico (0:ℝ) T, Work.Diff.STE.Periodic1 (a t)) ∧
      (∀ t ∈ Set.Ico (0:ℝ) T, ∀ x (c d : Fin n), a t x c d = a t x d c) ∧
      (∀ t ∈ Set.Ico (0:ℝ) T, ∀ x c d,
        a t x c d = (((Work.Diff.STE.Flat.reMat (u t x))⁻¹) c d
          + ((Work.Diff.STE.Flat.reMat (u t x))⁻¹) d c) / 2) ∧
      (∀ t ∈ Set.Ico (0:ℝ) tstar, ∀ x : Fin n → ℝ, ∀ ξ : Fin n → ℝ,
        lam' * ∑ i, (ξ i) ^ 2 ≤ ∑ c, ∑ d, a t x c d * ξ c * ξ d) ∧
      (∀ t ∈ Set.Ico (0:ℝ) tstar, ∀ (c d i : Fin n) (x : Fin n → ℝ),
        |Work.Diff.STE.pdR i (fun y => a t y c d) x| ≤ K₁) := by
  obtain ⟨hsm, hper⟩ := coeffA_smooth_periodic u hu huper lam hlam hell
  obtain ⟨lam', hlam', hellA⟩ := coeffA_elliptic htstarT u hu huper lam hlam hell
  obtain ⟨K₁, hK₁, hKb⟩ := coeffA_deriv_bound htstarT u hu huper lam hlam hell
  exact ⟨coeffA u, lam', K₁, hlam', hK₁, hsm, hper,
    (fun t _ x c d => coeffA_symm u t x c d),
    (fun t _ x c d => coeffA_apply u t x c d),
    hellA, hKb⟩

end Work.Diff.STE.flat
