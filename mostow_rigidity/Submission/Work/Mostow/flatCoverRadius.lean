import Mathlib
import Submission.Work.Mostow.flatActBasic
import Submission.Work.Mostow.horSpec

/-!
# The flat action of a cocompact horospherical stabiliser has bounded orbits

Let `ξ ∈ Sph n`, and `Γ ≤ PO n 1` a subgroup such that

* every `γ ∈ Γ` fixing `ξ` (i.e. `bd γ ξ = ξ`) preserves the Busemann level `lev ξ ·`
  (`hlev`), and
* every point of the level-one horosphere of `ξ` is moved into a fixed compact set `K` by an
  element of `Γ` fixing `ξ` (`hcpt`).

Then the orbit of the origin of the flat space `ξ^⊥` under the flat action `flatAct ξ · (0)` is
uniformly close to every point of `ξ^⊥`: there is `R > 0` such that every `x ⊥ ξ` is within
distance `R` of `flatAct ξ γ 0` for some `γ ∈ Γ_ξ`.

This is the "horospherical cocompactness gives a flat net" step: the point `horoPt ξ x` of the
level-one horosphere is sent by `γ` into the compact `K`, so its flat coordinate
`flatAct ξ γ x = yc ξ (γ • horoPt ξ x)` is bounded by the norm bound `M` for `K` (via
`yc_norm_le_norm`); applying the same to `γ⁻¹` and using that `flatAct ξ γ` is a Euclidean
isometry of `ξ^⊥` with inverse `flatAct ξ γ⁻¹` places `flatAct ξ γ⁻¹ 0` within `M` of `x`.
-/

set_option linter.unusedVariables false

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity

variable {n : ℕ}

/-- The Busemann level of the base point is one. -/
theorem lev_zero_eq_one (ξ : E n) : lev ξ (0 : E n) = 1 := by
  simp [lev, tpart]

/-- If `γ` fixes `ξ` and preserves the level function `lev ξ`, then it preserves the level of the
base point: `lev ξ (γ • 0) = 1`. -/
theorem lev_smul_zero_eq_one_flatCoverRadius {ξ : E n} (hξ : ξ ∈ Sph n) (hA : POBasic n) (hI : HypIsoData n)
    {γ : PO n 1} (hbd : bd γ ξ = ξ) (hlev : ∀ u : E n, lev ξ (γ • u) = lev ξ u) :
    lev ξ (γ • (0 : E n)) = 1 := by
  have h := hlev (0 : E n)
  rw [lev_smul_self hI hA ξ hξ γ (0 : E n) hbd, lev_zero_eq_one ξ] at h
  simpa using h

theorem flatCoverRadius {n : ℕ} (hA : Work.Mostow.POBasic n) (hI : Work.Mostow.HypIsoData n)
    {Γ : Subgroup (LeanEval.Geometry.MostowRigidity.PO n 1)} {ξ : Submission.Mostow.E n}
    (hξ : ξ ∈ Submission.Mostow.Sph n)
    (hlev : ∀ γ : Γ,
      Submission.Mostow.bd ((γ : Γ) : LeanEval.Geometry.MostowRigidity.PO n 1) ξ = ξ →
      ∀ u : Submission.Mostow.E n,
        Work.Mostow.lev ξ (((γ : Γ) : LeanEval.Geometry.MostowRigidity.PO n 1) • u)
          = Work.Mostow.lev ξ u)
    (hcpt : ∃ K : Set (Submission.Mostow.E n), IsCompact K ∧ ∀ u : Submission.Mostow.E n,
      Work.Mostow.lev ξ u = 1 → ∃ γ : Γ,
        Submission.Mostow.bd ((γ : Γ) : LeanEval.Geometry.MostowRigidity.PO n 1) ξ = ξ ∧
        ((γ : Γ) : LeanEval.Geometry.MostowRigidity.PO n 1) • u ∈ K) :
    ∃ R : ℝ, 0 < R ∧ ∀ x : Submission.Mostow.E n, inner ℝ x ξ = 0 → ∃ γ : Γ,
      Submission.Mostow.bd ((γ : Γ) : LeanEval.Geometry.MostowRigidity.PO n 1) ξ = ξ ∧
      ‖Work.Mostow.flatAct ξ (((γ : Γ) : LeanEval.Geometry.MostowRigidity.PO n 1))
        (0 : Submission.Mostow.E n) - x‖ ≤ R := by
  obtain ⟨K, hKc, hK⟩ := hcpt
  -- `K` is non-empty, since the base point has level one.
  obtain ⟨γ₀, -, hK₀⟩ := hK (0 : Submission.Mostow.E n) (lev_zero_eq_one ξ)
  -- the norm is bounded on the compact set `K`.
  obtain ⟨M, hM⟩ := hKc.exists_bound_of_continuousOn
    (f := fun v : Submission.Mostow.E n => v) continuous_id.continuousOn
  have hMnn : 0 ≤ M := le_trans (norm_nonneg _) (by simpa using hM _ hK₀)
  -- every `ξ`-stabilising element of `Γ` has level-one base point.
  have h0 : ∀ (γ : Γ) (hbd : Submission.Mostow.bd
      ((γ : Γ) : LeanEval.Geometry.MostowRigidity.PO n 1) ξ = ξ),
      Work.Mostow.lev ξ (((γ : Γ) : LeanEval.Geometry.MostowRigidity.PO n 1)
        • (0 : Submission.Mostow.E n)) = 1 :=
    fun γ hbd => lev_smul_zero_eq_one_flatCoverRadius hξ hA hI hbd (hlev γ hbd)
  refine ⟨M + 1, by linarith, ?_⟩
  intro x hx
  -- `horoPt ξ x` has level one, so some `γ ∈ Γ_ξ` moves it into `K`.
  obtain ⟨γ, hbd, hKmem⟩ := hK (horoPt ξ x) (lev_horoPt hξ x hx)
  have hlevx : Work.Mostow.lev ξ (((γ : Γ) : LeanEval.Geometry.MostowRigidity.PO n 1)
      • horoPt ξ x) = 1 := by
    rw [hlev γ hbd (horoPt ξ x), lev_horoPt hξ x hx]
  -- hence the flat coordinate of `γ • horoPt ξ x` is bounded by `M`.
  have hbnd : ‖flatAct ξ ((γ : Γ) : LeanEval.Geometry.MostowRigidity.PO n 1) x‖ ≤ M := by
    have h1 := yc_norm_le_norm hξ hlevx
    have h2 : ‖((γ : Γ) : LeanEval.Geometry.MostowRigidity.PO n 1)
        • horoPt ξ x‖ ≤ M := by simpa using hM _ hKmem
    show ‖yc ξ (((γ : Γ) : LeanEval.Geometry.MostowRigidity.PO n 1) • horoPt ξ x)‖ ≤ M
    linarith
  -- the inverse element of `Γ` brings the origin of `ξ^⊥` within `M` of `x`.
  have hmeminv : ((γ : Γ) : LeanEval.Geometry.MostowRigidity.PO n 1)⁻¹ ∈ Γ := Γ.inv_mem γ.property
  have hbdinv : Submission.Mostow.bd
      (((γ : Γ) : LeanEval.Geometry.MostowRigidity.PO n 1)⁻¹) ξ = ξ := bd_inv_of hξ hA hbd
  refine ⟨⟨((γ : Γ) : LeanEval.Geometry.MostowRigidity.PO n 1)⁻¹, hmeminv⟩, hbdinv, ?_⟩
  have h0inv : Work.Mostow.lev ξ (((γ : Γ) : LeanEval.Geometry.MostowRigidity.PO n 1)⁻¹
      • (0 : Submission.Mostow.E n)) = 1 :=
    h0 ⟨_, hmeminv⟩ hbdinv
  -- `flatAct ξ γ⁻¹` inverts `flatAct ξ γ` on `ξ^⊥`.
  have hcomp : flatAct ξ (((γ : Γ) : LeanEval.Geometry.MostowRigidity.PO n 1)⁻¹)
      (flatAct ξ ((γ : Γ) : LeanEval.Geometry.MostowRigidity.PO n 1) x) = x := by
    have h1 : flatAct ξ (((γ : Γ) : LeanEval.Geometry.MostowRigidity.PO n 1)⁻¹
          * ((γ : Γ) : LeanEval.Geometry.MostowRigidity.PO n 1)) x
        = flatAct ξ (((γ : Γ) : LeanEval.Geometry.MostowRigidity.PO n 1)⁻¹)
            (flatAct ξ ((γ : Γ) : LeanEval.Geometry.MostowRigidity.PO n 1) x) :=
      flatAct_comp hξ hA hI hbdinv hbd h0inv (h0 γ hbd) hx
    rw [← h1, inv_mul_cancel, flatAct_one hξ hA hx]
  -- and `flatAct ξ γ⁻¹` is an isometry of `ξ^⊥`.
  have hiso : ‖flatAct ξ (((γ : Γ) : LeanEval.Geometry.MostowRigidity.PO n 1)⁻¹)
        (0 : Submission.Mostow.E n) - x‖
      = ‖flatAct ξ ((γ : Γ) : LeanEval.Geometry.MostowRigidity.PO n 1) x‖ := by
    have h := flatAct_isometry (ξ := ξ) hξ hA hI
      (g := ((γ : Γ) : LeanEval.Geometry.MostowRigidity.PO n 1)⁻¹) hbdinv h0inv
      (y := (0 : Submission.Mostow.E n))
      (y' := flatAct ξ ((γ : Γ) : LeanEval.Geometry.MostowRigidity.PO n 1) x)
      (by simp) (flatAct_mem hξ _ _)
    rw [hcomp] at h
    simpa using h
  rw [hiso]
  linarith

end Work.Mostow
