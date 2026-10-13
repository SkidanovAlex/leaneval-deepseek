/-
  CoreStep / `fibreProd_sigma_lem`.

  Given an absolute stratum `T : Stratum 0 ((n+1)+m)` and a semi-Pfaffian set
  `S : SemiPf (n+s)` whose base projection `π_n(S.set)` has null dimension `< K`, one needs a
  single semi-Pfaffian set `Z ⊆ ℝ^{(n+1)+(m+s)}` whose `π_{n+1}`-projection is

    `π_{n+1}(absSet T) ∩ {y : ℝ^{n+1} | Fin.init y ∈ π_n(S.set)}`

  and whose own base projection `π_n(Z.set)` is again of null dimension `< K`, with the usual
  format/degree bookkeeping (format bounded by a constant depending only on `F`, degree bounded
  by a polynomial in `T.deg + S.deg` depending only on `F`).

  The construction is the fibre product of the two descriptions over the common first `n+1`
  coordinates:

  * `X1 := absSub T : SemiPf ((n+1)+m)`, whose point set is `absSet T`;
  * `X2 := SemiPf.extend (skipInj n s) S : SemiPf ((n+1)+s)`, the cylinder over `S` with a new
    free coordinate inserted at position `n`;
  * `Z := interSet (extend (castLE ·) (tidy X1)) (extend (midInj (n+1) m s) (tidy X2))`, i.e. the
    gluing of the two descriptions along the common first `n+1` coordinates, with the two unused
    blocks `Fin m`, `Fin s` kept apart (`projFirst_inter_extend` computes its `π_{n+1}`).

  The cube `cubeC (n+1)` appearing in `projFirst_extend_skipInj` is harmless: `π_{n+1}(absSet T)`
  is already inside the cube (`proj_absSet_subset_cube` below), so intersecting with it changes
  nothing.

  Everything reduces to the two independently proved bookkeeping lemmas

  * `Work.CoreStep.interSet_deg_le` — the degree of `interSet`;
  * `Work.CoreStep.nullDimLT_basePr_of_proj` — the measure of `basePr '' Z.set` from the
    `π_{n+1}`-description of `Z.set`.
-/
import Mathlib
import Submission.Work.WilE7.MainDesignDefs
import Submission.Work.WilE7.fiberProduct_semiPf
import Submission.Work.WilE7.CoreStep.subPf_inter
import Submission.Work.WilE7.Defs
import Submission.Work.WilE7.PadAux.tidy_bounds
import Submission.Work.WilE7.DimAPI.nullDimLT_basics
import Submission.Work.WilE7.sumProduct
import Submission.Work.CoreStep.SigmaFamDefs
import Submission.Work.WilE8.Star.projFirst_cyl
import Submission.Work.WilE8.Star.LiftDef
import Submission.Work.CoreStep.interSet_deg_le
import Submission.Work.CoreStep.nullDimLT_basePr_of_proj

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.CoreStep

open WilkiesDesign WilkiesDesign.E

/-! ## Two elementary facts about the pieces -/

/-- **The `π_{n+1}`-projection of the cylinder over `S`.**  Extending `S : SemiPf (n+s)` along
`skipInj n s` (the insertion of a new coordinate at position `n`) and projecting to the first
`n+1` coordinates gives the cylinder over `π_n(S.set)` in the first `n` coordinates, cut by the
cube (the new coordinate is free inside `[-1,1]`). -/
theorem projFirst_extend_skipInj (n s : ℕ) (S : SemiPf (n + s)) :
    projFirst (n + 1) s '' (Work.WilE8.SemiPf.extend (Work.WilE8.skipInj n s) S).set
      = {z : Fin (n + 1) → ℝ | Fin.init z ∈ projFirst n s '' S.set} ∩ cubeC (n + 1) := by
  rw [Work.WilE8.Extend.semipf_set_extend (Work.WilE8.Star.skipInj_injective n s) S,
    Set.ofPred_and, Set.ofPred_mem_eq, Set.inter_comm]
  exact Work.WilE8.Star.projFirst_cyl (n := n) (m := s) (C := S.set)
    (Work.WilE8.SemiPf.set_subset_cube S)

/-- `absSet T` lies in the cube. -/
theorem absSet_subset_cube (N : ℕ) (T : Stratum 0 N) :
    Work.WilE7.MainDesign.absSet T ⊆ cubeC N := by
  rintro w ⟨z, hz, rfl⟩
  intro i
  exact Work.WilE8.SemiPf.set_subset_cube T.X hz _

/-- The base projection of `absSet T` lies in the cube. -/
theorem proj_absSet_subset_cube (n m : ℕ) (T : Stratum 0 ((n + 1) + m)) :
    projFirst (n + 1) m '' Work.WilE7.MainDesign.absSet T ⊆ cubeC (n + 1) := by
  rintro y ⟨w, hw, rfl⟩
  intro i
  exact absSet_subset_cube _ T hw _

/-! ## The lemma -/

theorem fibreProd_sigma_lem (F : ℕ) :
    ∃ (A : ℕ) (B : Polynomial ℕ),
      ∀ (n m s K : ℕ) (T : WilkiesDesign.E.Stratum 0 ((n + 1) + m))
        (S : WilkiesDesign.E.SemiPf (n + s)),
        T.X.fmt ≤ F → S.fmt ≤ F →
        Work.WilE7.MainDesign.NullDimLT (WilkiesDesign.E.projFirst n s '' S.set) K →
        ∃ Z : WilkiesDesign.E.SemiPf ((n + 1) + (m + s)),
          Z.fmt ≤ A ∧ Z.deg ≤ B.eval (T.deg + S.deg) ∧
          WilkiesDesign.E.projFirst (n + 1) (m + s) '' Z.set =
            (WilkiesDesign.E.projFirst (n + 1) m '' (Work.WilE7.MainDesign.absSet T)) ∩
              {y : Fin (n + 1) → ℝ |
                Fin.init y ∈ WilkiesDesign.E.projFirst n s '' S.set} ∧
          Work.WilE7.MainDesign.NullDimLT
            (Work.WilE7.MainDesign.basePr n (m + s) '' Z.set) K := by
  refine ⟨4 * F, Polynomial.C 2 * (1 + Polynomial.X) ^ 2, ?_⟩
  intro n m s K T S hT hS hnd
  -- the two format hypotheses bound all the dimensions involved
  have hTfmt : (0 + ((n + 1) + m)) + T.X.r ≤ F := hT
  have hSfmt : (n + s) + S.r ≤ F := hS
  -- the two descriptions glued along the common first `n+1` coordinates
  let X1 : SemiPf ((n + 1) + m) := Work.CoreStep.absSub T
  let X2 : SemiPf ((n + 1) + s) := Work.WilE8.SemiPf.extend (Work.WilE8.skipInj n s) S
  let A1 : SemiPf ((n + 1) + (m + s)) :=
    Work.WilE8.SemiPf.extend (Fin.castLE (Nat.add_le_add_left (Nat.le_add_right m s) (n + 1)))
      (Work.WilE7.tidy X1)
  let A2 : SemiPf ((n + 1) + (m + s)) :=
    Work.WilE8.SemiPf.extend (Work.WilE7.midInj (n + 1) m s) (Work.WilE7.tidy X2)
  let Z : SemiPf ((n + 1) + (m + s)) := Work.WilE7.interSet A1 A2
  -- format: `(n+1) + m ≤ F`, `n + s ≤ F`, `T.X.r ≤ F`, `S.r ≤ F`
  have hfmt : Z.fmt ≤ 4 * F := by
    show ((n + 1) + (m + s)) + (T.X.r + S.r) ≤ 4 * F
    omega
  -- degree: `2 (1 + (T.deg + S.deg))²`
  have hX1deg : X1.deg ≤ T.deg := by
    show (Work.CoreStep.absSub T).deg ≤ T.deg
    rw [Work.CoreStep.absSub_deg]
    show T.X.deg ≤ T.deg
    rw [show T.deg = T.X.deg + ∑ a, atomDeg (T.h a) from rfl]
    omega
  have htX1deg : (Work.WilE7.tidy X1).deg ≤ T.deg :=
    le_trans (Work.WilE7.PadAux.tidy_bounds ((n + 1) + m) X1).1 hX1deg
  have htX1len : (Work.WilE7.tidy X1).basics.length ≤ 1 + T.deg := by
    have h := (Work.WilE7.PadAux.tidy_bounds ((n + 1) + m) X1).2
    omega
  have htX2deg : (Work.WilE7.tidy X2).deg ≤ S.deg := by
    have h := (Work.WilE7.PadAux.tidy_bounds ((n + 1) + s) X2).1
    dsimp only [X2] at h
    rwa [Work.WilE8.Extend.semipf_deg_extend (Work.WilE8.Star.skipInj_injective n s) S] at h
  have htX2len : (Work.WilE7.tidy X2).basics.length ≤ 1 + S.deg := by
    have h := (Work.WilE7.PadAux.tidy_bounds ((n + 1) + s) X2).2
    dsimp only [X2] at h
    rwa [Work.WilE8.Extend.semipf_deg_extend (Work.WilE8.Star.skipInj_injective n s) S] at h
  have hA1deg : A1.deg = (Work.WilE7.tidy X1).deg := by
    dsimp only [A1]
    exact Work.WilE8.Extend.semipf_deg_extend (Fin.castLE_injective _) _
  have hA2deg : A2.deg = (Work.WilE7.tidy X2).deg := by
    dsimp only [A2]
    exact Work.WilE8.Extend.semipf_deg_extend (Work.WilE7.midInj_injective (n + 1) m s) _
  have hA1len : A1.basics.length = (Work.WilE7.tidy X1).basics.length := by
    simp only [A1, Work.WilE8.SemiPf.extend, List.length_map]
  have hA2len : A2.basics.length = (Work.WilE7.tidy X2).basics.length := by
    simp only [A2, Work.WilE8.SemiPf.extend, List.length_map]
  have hdeg : Z.deg ≤ (Polynomial.C 2 * (1 + Polynomial.X) ^ 2).eval (T.deg + S.deg) := by
    have hmain : Z.deg ≤ A2.basics.length * A1.deg + A1.basics.length * A2.deg := by
      dsimp only [Z]
      exact Work.CoreStep.interSet_deg_le A1 A2
    rw [hA1deg, hA2deg, hA1len, hA2len] at hmain
    have h2 : (Work.WilE7.tidy X2).basics.length * (Work.WilE7.tidy X1).deg +
        (Work.WilE7.tidy X1).basics.length * (Work.WilE7.tidy X2).deg
        ≤ (1 + S.deg) * T.deg + (1 + T.deg) * S.deg :=
      Nat.add_le_add (Nat.mul_le_mul htX2len htX1deg) (Nat.mul_le_mul htX1len htX2deg)
    have h3 : (1 + S.deg) * T.deg + (1 + T.deg) * S.deg ≤ 2 * (1 + (T.deg + S.deg)) ^ 2 := by
      nlinarith [sq_nonneg (T.deg - S.deg : ℤ)]
    have h4 : 2 * (1 + (T.deg + S.deg)) ^ 2 =
        (Polynomial.C 2 * (1 + Polynomial.X) ^ 2).eval (T.deg + S.deg) := by simp
    exact le_trans hmain (le_trans h2 (le_trans h3 (le_of_eq h4)))
  -- the projection of `Z`: the fibre product over the first `n+1` coordinates
  have hproj : projFirst (n + 1) (m + s) '' Z.set =
      (projFirst (n + 1) m '' Work.WilE7.MainDesign.absSet T) ∩
        {y : Fin (n + 1) → ℝ | Fin.init y ∈ projFirst n s '' S.set} := by
    dsimp only [Z, A1, A2]
    rw [Work.WilE7.CoreStep.projFirst_inter_extend (n := n + 1) (m1 := m) (m2 := s)
      (Work.WilE7.tidy X1) (Work.WilE7.tidy X2)]
    rw [Work.WilE7.tidy_set, Work.WilE7.tidy_set]
    dsimp only [X1, X2]
    rw [Work.CoreStep.absSub_set, projFirst_extend_skipInj n s S]
    -- the cube factor is absorbed by `π_{n+1}(absSet T) ⊆ cubeC (n+1)`
    have hcube := proj_absSet_subset_cube n m T
    ext y
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨h1, h2, -⟩
      exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, h2, hcube h1⟩
  -- the measure: `π_n(Z.set) ⊆ π_n(S.set)`
  have hndZ : Work.WilE7.MainDesign.NullDimLT
      (Work.WilE7.MainDesign.basePr n (m + s) '' Z.set) K :=
    Work.CoreStep.nullDimLT_basePr_of_proj
      (A := projFirst (n + 1) m '' Work.WilE7.MainDesign.absSet T)
      (B := projFirst n s '' S.set) hproj hnd
  exact ⟨Z, hfmt, hdeg, hproj, hndZ⟩

end Work.CoreStep
