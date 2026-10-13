/-
  `Work.CoreStep.stratReindex_good_fwd`

  Reindexing the coordinates of a stratum along an equivalence `e : Fin (0 + N) ≃ Fin (0 + N')`
  turns a good stratum into a good stratum -- this file proves the *forward* direction:
  `Good (Stratum.reindex e S) → Good S` for a stratum `S` with no base coordinates (`p = 0`).

  The three components of `Good S` at a point `z ∈ S.X.set` are transported from the
  corresponding components of `Good (Stratum.reindex e S)` at the point
  `y := fun j => z (e.symm j)` of the reindexed stratum (note `(fun i => y (e i)) = z`):

  * the equations: `Stratum.reindex_h_eval` says that `h` of the reindexed stratum evaluated
    at `y` is `h` of `S` evaluated at `y ∘ e = z`;

  * the rank of the Jacobian: since `p = 0`, the columns of the `j × q` matrix of `Good` are
    indexed by *all* the coordinate directions `Fin.natAdd 0 l`, `l : Fin q`.  Reindexing
    permutes these columns -- the direction `Fin.natAdd 0 l` of `S` corresponds to the
    direction `Fin.natAdd 0 (coordPermEquiv e l)` of the reindexed stratum, where
    `coordPermEquiv e : Fin N ≃ Fin N'` is chosen so that
    `Fin.natAdd 0 (coordPermEquiv e l) = e (Fin.natAdd 0 l)`.  Hence the two matrices are
    `Matrix.submatrix`-relatives of one another and have the same rank
    (`Matrix.rank_submatrix`);

  * the local persistence: `Good` of the reindexed stratum says that, near `y`, the zero set
    of the reindexed equations is contained in the reindexed set.  Pulling this back along the
    homeomorphism `pullHomeo e : (Fin (0+N') → ℝ) ≃ₜ (Fin (0+N) → ℝ)`, `y' ↦ y' ∘ e`
    (which is continuous and maps `y` to `z`), gives the required local persistence of `S`.
    Note that the fibre condition `projFirst 0 q z' = projFirst 0 q z` is automatic since
    `Fin 0 → ℝ` is a subsingleton.
-/
import Mathlib
import Submission.Work.CoreStep.StratReindexDefs

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.CoreStep

open WilkiesDesign WilkiesDesign.E

/-! ## The coordinate permutation induced by `e` -/

/-- `Fin.natAdd 0` as an equivalence `Fin n ≃ Fin (0 + n)`. -/
def nAddZeroEquiv (n : ℕ) : Fin n ≃ Fin (0 + n) :=
  Equiv.ofBijective (fun i : Fin n => Fin.natAdd 0 i)
    ⟨Fin.natAdd_injective n 0, fun j => ⟨⟨j.val, by omega⟩, by ext; simp [Fin.natAdd]⟩⟩

theorem nAddZeroEquiv_apply (n : ℕ) (i : Fin n) : nAddZeroEquiv n i = Fin.natAdd 0 i := rfl

/-- The permutation `Fin N ≃ Fin N'` of the last-coordinate indices induced by an equivalence
`e` of the two coordinate sets, normalised so that the coordinate direction of `S` with index
`l` corresponds to the coordinate direction of `Stratum.reindex e S` with index
`coordPermEquiv e l`. -/
def coordPermEquiv {N N' : ℕ} (e : Fin (0 + N) ≃ Fin (0 + N')) : Fin N ≃ Fin N' where
  toFun l := (nAddZeroEquiv N').symm (e (nAddZeroEquiv N l))
  invFun l' := (nAddZeroEquiv N).symm (e.symm (nAddZeroEquiv N' l'))
  left_inv l := by simp
  right_inv l' := by simp

theorem coordPermEquiv_spec {N N' : ℕ} (e : Fin (0 + N) ≃ Fin (0 + N')) (l : Fin N) :
    Fin.natAdd 0 (coordPermEquiv e l) = e (Fin.natAdd 0 l) := by
  rw [← nAddZeroEquiv_apply N' (coordPermEquiv e l), coordPermEquiv]
  simp [nAddZeroEquiv_apply]

/-! ## The transport of `Good` -/

theorem stratReindex_good_fwd {N N' : ℕ} (e : Fin (0 + N) ≃ Fin (0 + N'))
    (S : WilkiesDesign.E.Stratum 0 N) :
    WilkiesDesign.E.Stratum.Good (Work.CoreStep.Stratum.reindex e S) →
      WilkiesDesign.E.Stratum.Good S := by
  intro hG
  intro z hz
  -- the point of the reindexed stratum corresponding to `z`
  set y : Fin (0 + N') → ℝ := fun j => z (e.symm j) with hy_def
  have hy_comp : (fun i : Fin (0 + N) => y (e i)) = z := by
    funext i; simp [hy_def]
  have hy : y ∈ (Work.CoreStep.Stratum.reindex e S).X.set := by
    rw [Stratum.reindex_mem]
    rw [hy_comp]
    exact hz
  obtain ⟨hG1, hG2, hG3⟩ := hG y hy
  -- the fibre condition `projFirst 0 N' _ = projFirst 0 N' y` of `Good` is automatic
  have hG3' : ∀ᶠ y' in nhds y,
      (∀ a, eaEval (Work.CoreStep.Stratum.reindex e S).X.c
        ((Work.CoreStep.Stratum.reindex e S).h a) y' = 0) →
      y' ∈ (Work.CoreStep.Stratum.reindex e S).X.set :=
    hG3.mono fun _ hy' => hy' (Subsingleton.elim _ _)
  refine ⟨?_, ?_, ?_⟩
  · -- the equations
    intro a
    have h := hG1 a
    rw [Stratum.reindex_h_eval e S y a, hy_comp] at h
    exact h
  · -- the rank of the Jacobian
    set M₁ : Matrix (Fin S.j) (Fin N') ℝ :=
      Matrix.of fun (a : Fin S.j) (l : Fin N') => eaEval (Work.CoreStep.Stratum.reindex e S).X.c
        (eaD (Work.CoreStep.Stratum.reindex e S).X.c (Fin.natAdd 0 l)
          ((Work.CoreStep.Stratum.reindex e S).h a)) y with hM₁
    set M₂ : Matrix (Fin S.j) (Fin N) ℝ :=
      Matrix.of fun (a : Fin S.j) (l : Fin N) =>
        eaEval S.X.c (eaD S.X.c (Fin.natAdd 0 l) (S.h a)) z with hM₂
    have hM₁rank : M₁.rank = S.j := hG2
    -- the columns of `M₂` are the columns of `M₁`, permuted by `coordPermEquiv e`
    have hcols : ∀ (a : Fin S.j) (l : Fin N), M₂ a l = M₁ a (coordPermEquiv e l) := by
      intro a l
      rw [hM₂, hM₁]
      simp only [Matrix.of_apply]
      have hC : eaEval S.X.c (eaD S.X.c (Fin.natAdd 0 l) (S.h a)) z
          = eaEval S.X.c (eaD S.X.c (e.symm (Fin.natAdd 0 (coordPermEquiv e l))) (S.h a))
              (fun i => y (e i)) := by
        rw [coordPermEquiv_spec e l, e.symm_apply_apply, hy_comp]
      exact hC.trans
        (Stratum.reindex_jac_entry e S y a (Fin.natAdd 0 (coordPermEquiv e l))).symm
    have hM₂eq : M₂ = M₁.submatrix id (coordPermEquiv e) := by
      ext a l
      rw [Matrix.submatrix_apply, id_eq]
      exact hcols a l
    have hrank : M₂.rank = M₁.rank := by
      rw [hM₂eq]
      have h := Matrix.rank_submatrix M₁ (Equiv.refl (Fin S.j)) (coordPermEquiv e)
      simpa using h
    rw [hrank, hM₁rank]
  · -- the local persistence, pulled back along the homeomorphism `y' ↦ y' ∘ e`
    have htend : Filter.Tendsto (Work.WilE7.pullHomeo e).symm (nhds z) (nhds y) := by
      have hc : Filter.Tendsto (Work.WilE7.pullHomeo e).symm (nhds z)
          (nhds ((Work.WilE7.pullHomeo e).symm z)) :=
        (Work.WilE7.pullHomeo e).symm.continuous.continuousAt
      have hyz : (Work.WilE7.pullHomeo e).symm z = y := rfl
      simpa [hyz] using hc
    refine (htend.eventually hG3').mono ?_
    intro z' hz'
    intro _ hz''
    have hcomp : (fun i : Fin (0 + N) => (Work.WilE7.pullHomeo e).symm z' (e i)) = z' := by
      funext i
      rw [Work.WilE7.pullHomeo_symm_apply]
      simp
    have hmem : (Work.WilE7.pullHomeo e).symm z' ∈ (Work.CoreStep.Stratum.reindex e S).X.set :=
      hz' (fun a => by
        rw [Stratum.reindex_h_eval e S ((Work.WilE7.pullHomeo e).symm z') a, hcomp]
        exact hz'' a)
    rw [Stratum.reindex_mem] at hmem
    rwa [hcomp] at hmem

end Work.CoreStep
