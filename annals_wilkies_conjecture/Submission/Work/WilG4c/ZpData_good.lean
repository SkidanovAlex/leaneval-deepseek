/-
  `ZpData_good`: the data of the pointwise fibre continuity shape `ZpShape p n` is good as soon
  as the underlying `famGraph f` lies in `S.Ω F0 D (Ng p n)`.

  `OShape.Good` for a `poly` atom is `True`, for `neg` and `ex` it is the identity, and for
  `and` it is the conjunction, so the whole shape is good exactly when its two `mem` atoms (both
  carrying the graph of `f`) are.  The block of universal quantifiers `forallIter` cannot be
  unfolded when its length is a variable; `good_forallIter` handles it by induction.

  The `Data` type of `OShape` is a recursive (`brecOn`) definition, so the various intermediate
  goals are only *definitionally* well typed; the proof below therefore works with `exact`/`have`
  (default transparency) rather than `rw`/`simp only` (implicit transparency).
-/
import Mathlib
import Submission.Work.WilG4c.SliceNilDefs

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Classical

namespace Work.WilkG4c

open WilkiesDesign WilkiesDesign.CG

/-! ## Unfolding lemmas for `OShape.Good` -/

theorem good_poly {S : SOMin} {F n : ℕ} (P : MvPolynomial (Fin n) ℝ) :
    (OShape.poly n).Good S F P ↔ True := Iff.rfl

theorem good_mem {S : SOMin} {F n m : ℕ} (ι : Fin m → Fin n) (d : Set (Fin m → ℝ) × ℕ) :
    (OShape.mem n m ι).Good S F d ↔ d.1 ∈ S.Ω F d.2 m := Iff.rfl

theorem good_neg {S : SOMin} {F n : ℕ} (s : OShape n) (d : (OShape.neg s).Data) :
    (OShape.neg s).Good S F d ↔ s.Good S F d := Iff.rfl

theorem good_ex {S : SOMin} {F n : ℕ} (s : OShape (n + 1)) (d : (OShape.ex s).Data) :
    (OShape.ex s).Good S F d ↔ s.Good S F d := Iff.rfl

theorem good_and {S : SOMin} {F n : ℕ} (s t : OShape n) (d : (OShape.and s t).Data) :
    (OShape.and s t).Good S F d ↔ s.Good S F d.1 ∧ t.Good S F d.2 := Iff.rfl

/-- The iterated universal quantification `forallIter` does not change `Good`. -/
theorem good_forallIter {S : SOMin} {F : ℕ} (m : ℕ) :
    (k : ℕ) → (σ : OShape (m + k)) → (d : σ.Data) →
      (forallIter m k σ).Good S F (forallIterData m k σ d) ↔ σ.Good S F d
  | 0, σ, d => Iff.rfl
  | k + 1, σ, d => by
      have ih := good_forallIter (S := S) (F := F) m k
        (OShape.neg (OShape.ex (OShape.neg σ))) d
      exact ih.trans
        ((good_neg (S := S) (F := F) (OShape.ex (OShape.neg σ)) d).trans
          ((good_ex (S := S) (F := F) (OShape.neg σ) d).trans
            (good_neg (S := S) (F := F) σ d)))

end Work.WilkG4c

namespace Work.WilG4c

open WilkiesDesign WilkiesDesign.CG Work.WilkG4c

theorem ZpData_good {S : WilkiesDesign.SOMin} (p n F0 D : ℕ)
    (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ)
    (hf : WilkiesDesign.CG.famGraph f ∈ S.Ω F0 D (Work.WilkG4c.Ng p n)) :
    (Work.WilkG4c.ZpShape p n).Good S F0 (Work.WilkG4c.ZpData p n f D) := by
  -- the outer `mem` atom, carrying `(famGraph f, D)`
  have hmem1 : (OShape.mem (Nc p n + 1) (Ng p n) id).Good S F0 (famGraph f, D) :=
    (good_mem (S := S) (F := F0) (n := Nc p n + 1) (m := Ng p n) id
      (famGraph f, D)).mpr hf
  -- `zpInner`: the second `mem` atom together with a trivial polynomial atom
  have hinner : (zpInner p n).Good S F0 (zpInnerData p n f D) :=
    (good_and (S := S) (F := F0) (OShape.mem (Kz p n + 2) (Ng p n) (iotaVp p n))
        (OShape.ex (OShape.poly (Kz p n + 3))) (zpInnerData p n f D)).mpr
      ⟨(good_mem (S := S) (F := F0) (n := Kz p n + 2) (m := Ng p n) (iotaVp p n)
          (famGraph f, D)).mpr hf,
       (good_ex (S := S) (F := F0) (OShape.poly (Kz p n + 3))
          (zpInnerData p n f D).2).mpr
        ((good_poly (S := S) (F := F0) (n := Kz p n + 3)
            (zpInnerData p n f D).2).mpr trivial)⟩
  have hve : (zpVexists p n).Good S F0 (zpVexistsData p n f D) :=
    (good_ex (S := S) (F := F0) (zpInner p n) (zpVexistsData p n f D)).mpr hinner
  have hball : (zpBallImp p n).Good S F0 (zpBallImpData p n f D) :=
    (good_neg (S := S) (F := F0)
        (OShape.ex (OShape.and (OShape.poly (Kz p n + 1)) (OShape.neg (zpVexists p n))))
        (zpBallImpData p n f D)).mpr
      ((good_ex (S := S) (F := F0)
          (OShape.and (OShape.poly (Kz p n + 1)) (OShape.neg (zpVexists p n)))
          (zpBallImpData p n f D)).mpr
        ((good_and (S := S) (F := F0) (OShape.poly (Kz p n + 1))
            (OShape.neg (zpVexists p n)) (zpBallImpData p n f D)).mpr
          ⟨(good_poly (S := S) (F := F0) (n := Kz p n + 1)
              (zpBallImpData p n f D).1).mpr trivial,
           (good_neg (S := S) (F := F0) (zpVexists p n)
              (zpBallImpData p n f D).2).mpr hve⟩))
  have hyblock : (zpYBlock p n).Good S F0 (zpYBlockData p n f D) :=
    (good_forallIter (S := S) (F := F0) (Nc p n + 5) (n + 1) (zpBallImp p n)
        (zpBallImpData p n f D)).mpr hball
  have hdelta : (zpDelta p n).Good S F0 (zpDeltaData p n f D) :=
    (good_and (S := S) (F := F0) (OShape.poly (Nc p n + 5)) (zpYBlock p n)
        (zpDeltaData p n f D)).mpr
      ⟨(good_poly (S := S) (F := F0) (n := Nc p n + 5)
          (zpDeltaData p n f D).1).mpr trivial,
       hyblock⟩
  have hdeltaEx : (zpDeltaEx p n).Good S F0 (zpDeltaExData p n f D) :=
    (good_ex (S := S) (F := F0) (OShape.ex (zpDelta p n)) (zpDeltaExData p n f D)).mpr
      ((good_ex (S := S) (F := F0) (zpDelta p n) (zpDeltaData p n f D)).mpr hdelta)
  have heps : (zpEps p n).Good S F0 (zpEpsData p n f D) :=
    (good_and (S := S) (F := F0) (OShape.poly (Nc p n + 3)) (OShape.neg (zpDeltaEx p n))
        (zpEpsData p n f D)).mpr
      ⟨(good_poly (S := S) (F := F0) (n := Nc p n + 3)
          (zpEpsData p n f D).1).mpr trivial,
       (good_neg (S := S) (F := F0) (zpDeltaEx p n) (zpDeltaExData p n f D)).mpr hdeltaEx⟩
  have hepsEx : (zpEpsEx p n).Good S F0 (zpEpsData p n f D) :=
    (good_ex (S := S) (F := F0) (zpEps p n) (zpEpsData p n f D)).mpr heps
  have hcont : (zpCont p n).Good S F0 (zpContData p n f D) :=
    (good_neg (S := S) (F := F0) (OShape.ex (zpEpsEx p n)) (zpEpsData p n f D)).mpr
      ((good_ex (S := S) (F := F0) (zpEpsEx p n) (zpEpsData p n f D)).mpr hepsEx)
  exact (good_and (S := S) (F := F0) (OShape.mem (Nc p n + 1) (Ng p n) id) (zpCont p n)
      ((famGraph f, D), zpContData p n f D)).mpr ⟨hmem1, hcont⟩

end Work.WilG4c
