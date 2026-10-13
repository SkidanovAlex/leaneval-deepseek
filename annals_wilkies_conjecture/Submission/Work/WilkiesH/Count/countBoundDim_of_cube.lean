import Mathlib
import Submission.Work.WilkiesH.Count.Interface
import Submission.Work.WilkiesH.Norm.Defs
import Submission.Work.WilkiesH.Norm.JointDefs
import Submission.Work.WilkiesH.Norm.normSet_mem
import Submission.Work.WilkiesH.Norm.normPiece_mem_alt
import Submission.Work.WilkiesH.Norm.normJointGraph_mem_alt
import Submission.Work.WilkiesH.Norm.mem_degreeHeightLE_normMap
import Submission.Work.WilkiesH.Norm.normSet_trans
import Submission.Work.WilkiesH.Norm.exists_normPiece
import Submission.Work.WilkiesH.Norm.normMap_mem_cube01_and_injOn
import Submission.Work.WilkiesH.Norm.dimLE_normSet
import Submission.Work.WilkiesH.Count.dominateSum
import Submission.Work.WilG0.API
import Submission.Work.WilG5.Basic
import Submission.Work.WilG5.Count.dominate

/-!
# Area H (counting) — the normalisation removes the cube hypothesis

`CountBoundDimCube S F n μ` is `CountBoundDim S F n μ` with the extra hypothesis
`X ⊆ cube01 n`; the induction step of BNZ §6 (`countBoundDimCube_step`) is only proved in
that restricted form.  This file performs the normalisation that removes it, i.e. it derives
the unrestricted counting statement from the cube-restricted one (for *all* formats `F'`,
since normalising `X` changes its format and degree by a constant amount).

The argument is the one designed in `WilkiesH/Norm/Defs.lean`:

* the finitely many pieces `normPiece σ` (`σ : Fin n → NormShape`) cover `ℝⁿ`
  (`exists_normPiece`);
* on a piece, the coordinatewise map `normMap σ` is injective (`normMap_mem_cube01_and_injOn`)
  and maps the piece into the unit cube, so the points `T ∩ normPiece σ` of height/degree
  `(g,H)` are transported *bijectively* into `degreeHeightLE (normSet σ X).trans g H`
  (`normSet_trans`, `mem_degreeHeightLE_normMap`);
* `normSet σ X` is `Ω`-definable with format `F + na σ` and degree `D + nb σ` and still has
  dimension `≤ μ` (`dimLE_normSet`);
* hence the cube-restricted counting statement at format `F + na σ` bounds each piece;
* summing over the `4ⁿ` shapes and dominating the resulting finite family of shifted
  polynomials by a single polynomial in `(D, g, log H)` (`dominateSum`) gives the bound.
-/

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilkiesH.Count

open WilkiesDesign WilkiesConjecture
open Work.WilkiesH.Norm
open Work.WilG5

/-- The normalised image of an `Ω`-set is again `Ω`-definable, with format and degree shifted by
constants depending only on `n` and `σ`.

This is `Work.WilkiesH.Norm.normSet_mem`, re-derived here on top of self-contained proofs of the
two ingredient lemmas `normPiece_mem_alt` and `normJointGraph_mem_alt` (the two `Ω`-membership
facts the `normSet_mem` proof of `Norm/normSet_mem.lean` consumes).  The joint set
`normJoint σ A = liftLast n A ∩ liftLast n (normPiece σ) ∩ normJointGraph σ` is `Ω`-definable by
`liftLast_mem` + `normPiece_mem_alt` + `normJointGraph_mem_alt` and two `Omega_inter2`s, and its
projection `projN n` is `normSet σ A` by `projN_normJoint_eq`. -/
theorem normSet_mem_local {n : ℕ} {S : WilkiesDesign.SOMin} (σ : Fin n → NormShape) :
    ∃ a b : ℕ, ∀ {F D : ℕ} {A : Set (Fin n → ℝ)}, A ∈ S.Ω F D n →
      normSet σ A ∈ S.Ω (F + a) (D + b) n := by
  obtain ⟨Fa, Da, hPiece⟩ := Work.WilkiesH.Norm.normPiece_mem_alt σ
  obtain ⟨Fb, Db, hGraph⟩ := Work.WilkiesH.Norm.normJointGraph_mem_alt σ
  refine ⟨max n (max (Fa + n) Fb) + 1 + 1 + n, Da + Db, ?_⟩
  intro F D A hA
  have h1 : liftLast n A ∈ S.Ω (F + max n (max (Fa + n) Fb)) D (n + n) :=
    mem_mono (liftLast_mem (S := S) n F D hA) _ _ (by omega) le_rfl
  have h2 : liftLast n (normPiece σ) ∈ S.Ω (F + max n (max (Fa + n) Fb)) Da (n + n) :=
    mem_mono (liftLast_mem (S := S) n Fa Da (hPiece S)) _ _ (by omega) le_rfl
  have h3 : normJointGraph σ ∈ S.Ω (F + max n (max (Fa + n) Fb)) Db (n + n) :=
    mem_mono (hGraph S) _ _ (by omega) le_rfl
  have h12 := Work.WilG0.Omega_inter2 (S := S) h1 h2
  have h3' : normJointGraph σ ∈ S.Ω (F + max n (max (Fa + n) Fb) + 1) Db (n + n) :=
    mem_mono h3 _ _ (by omega) le_rfl
  have h123 := Work.WilG0.Omega_inter2 (S := S) h12 h3'
  have hproj := projN_mem (S := S) n _ _ h123
  rw [show projN n (liftLast n A ∩ liftLast n (normPiece σ) ∩ normJointGraph σ)
      = normSet σ A from projN_normJoint_eq σ A] at hproj
  exact mem_mono hproj _ _ (by omega) (by omega)

theorem countBoundDim_of_cube {S : WilkiesDesign.SOMin} {F n μ : ℕ} (h : ∀ F' : ℕ, Work.WilkiesH.CountBoundDimCube S F' n μ) : Work.WilkiesH.CountBoundDim S F n μ := by
  classical
  -- the cube-restricted statement for every format
  choose f hf using h
  -- the normalisation constants attached to each shape
  have hnorm : ∀ σ : Fin n → NormShape, ∃ a b : ℕ,
      ∀ {F' D : ℕ} {A : Set (Fin n → ℝ)}, A ∈ S.Ω F' D n →
        normSet σ A ∈ S.Ω (F' + a) (D + b) n :=
    fun σ => normSet_mem_local (S := S) σ
  choose na nb hnab using hnorm
  -- a single polynomial dominating the whole finite family of shifted polynomials
  obtain ⟨p, hp⟩ := dominateSum (fun σ : Fin n → NormShape => f (F + na σ)) nb
  refine ⟨p, fun D X hX hdim g H T hT => ?_⟩
  have hlog : (0 : ℝ) ≤ Real.log H := Real.log_natCast_nonneg H
  have hTtrans : (↑T : Set (Fin n → ℝ)) ⊆ X.trans := fun x hx => (hT hx).1
  -- the cube statement bounds each normalised piece
  have hpiece : ∀ σ : Fin n → NormShape,
      (((T.filter (fun x => x ∈ normPiece σ)).image (normMap σ)).card : ℝ)
        ≤ (f (F + na σ)).eval ![((D + nb σ : ℕ) : ℝ), (g : ℝ), Real.log H] := by
    intro σ
    obtain ⟨hcubeMap, _hinjMap⟩ := Work.WilkiesH.Norm.normMap_mem_cube01_and_injOn σ
    have hmem : normSet σ X ∈ S.Ω (F + na σ) (D + nb σ) n := hnab σ hX
    have hcubesub : normSet σ X ⊆ cube01 n := by
      rintro y ⟨x, ⟨-, hxp⟩, rfl⟩
      exact hcubeMap x hxp
    have hdim' : DimLE (normSet σ X) μ := Work.WilkiesH.Norm.dimLE_normSet σ X hdim
    refine hf (F + na σ) (D + nb σ) (normSet σ X) hmem hcubesub hdim' g H
      ((T.filter (fun x => x ∈ normPiece σ)).image (normMap σ)) ?_
    intro y hy
    rw [Finset.mem_coe, Finset.mem_image] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    have hxT : x ∈ (↑T : Set (Fin n → ℝ)) := (Finset.mem_filter.mp hx).1
    have hxpiece : x ∈ normPiece σ := (Finset.mem_filter.mp hx).2
    have htrans : normMap σ x ∈ (normSet σ X).trans :=
      Work.WilkiesH.Norm.normSet_trans (σ := σ) (X := X) (T := (↑T : Set (Fin n → ℝ)))
        hTtrans ⟨x, ⟨hxT, hxpiece⟩, rfl⟩
    have hdh := Work.WilkiesH.Norm.mem_degreeHeightLE_normMap (σ := σ) (X := X.trans)
      hxpiece (hT hxT)
    exact ⟨htrans, (Work.WilkiesH.mem_degreeHeightLE_iff.mp hdh).2⟩
  -- the pieces cover `T`, and the maps are injective on them
  have hcard_le : (T.card : ℝ) ≤ ∑ σ : Fin n → NormShape,
      (((T.filter (fun x => x ∈ normPiece σ)).image (normMap σ)).card : ℝ) := by
    have hcover : T ⊆ Finset.univ.biUnion
        (fun σ : Fin n → NormShape => T.filter (fun x => x ∈ normPiece σ)) := by
      intro x hx
      rw [Finset.mem_biUnion]
      exact ⟨fun i => shapeOf (x i), Finset.mem_univ _,
        Finset.mem_filter.mpr ⟨hx, fun i => mem_shapeSet_shapeOf (x i)⟩⟩
    calc (T.card : ℝ)
        ≤ ↑((Finset.univ.biUnion (fun σ : Fin n → NormShape =>
            T.filter (fun x => x ∈ normPiece σ))).card) :=
          Nat.cast_le.mpr (Finset.card_le_card hcover)
      _ ≤ ↑(∑ σ : Fin n → NormShape, (T.filter (fun x => x ∈ normPiece σ)).card) :=
          Nat.cast_le.mpr Finset.card_biUnion_le
      _ = ∑ σ : Fin n → NormShape,
            ((T.filter (fun x => x ∈ normPiece σ)).card : ℝ) := by
          rw [Nat.cast_sum]
      _ ≤ ∑ σ : Fin n → NormShape,
            (((T.filter (fun x => x ∈ normPiece σ)).image (normMap σ)).card : ℝ) := by
          apply Finset.sum_le_sum
          intro σ _
          have hinj : Set.InjOn (normMap σ)
              (↑(T.filter (fun x => x ∈ normPiece σ)) : Set (Fin n → ℝ)) :=
            Set.InjOn.mono (fun x hx => (Finset.mem_filter.mp hx).2)
              (Work.WilkiesH.Norm.normMap_mem_cube01_and_injOn σ).2
          rw [Finset.card_image_of_injOn hinj]
  calc (T.card : ℝ)
      ≤ ∑ σ : Fin n → NormShape,
          (((T.filter (fun x => x ∈ normPiece σ)).image (normMap σ)).card : ℝ) := hcard_le
    _ ≤ ∑ σ : Fin n → NormShape,
          (f (F + na σ)).eval ![((D + nb σ : ℕ) : ℝ), (g : ℝ), Real.log H] :=
        Finset.sum_le_sum (fun σ _ => hpiece σ)
    _ ≤ MvPolynomial.eval ![(D : ℝ), (g : ℝ), Real.log H] p := hp D g (Real.log H) hlog

end Work.WilkiesH.Count
