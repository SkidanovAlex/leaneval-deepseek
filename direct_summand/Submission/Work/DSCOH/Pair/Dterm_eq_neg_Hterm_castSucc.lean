import Mathlib
import Submission.Work.DSCOH.Norm.HomoAssembly
import Submission.Work.DSCOH.Norm.HomoStruct
import Submission.Work.DSCOH.Norm.strictMono_del_apply_eq
import Submission.Work.DSCOH.Struct.readD_lt

namespace Work.DSCOH.Pair

open CategoryTheory Limits Opposite TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

/-- `frA` only depends on the tuple, not on the particular proof that it is nondecreasing. -/
private lemma frA_congr_monotone {k : Nat} {ι : Type*} [LinearOrder ι] (y : Fin (k + 2) → ι)
    (hy hz : Monotone y) (hh : ¬ StrictMono y) :
    Work.DSCOH.Norm.frA y hy hh = Work.DSCOH.Norm.frA y hz hh := by
  unfold Work.DSCOH.Norm.frA Work.DSCOH.Norm.firstRepeat
  exact le_antisymm (Finset.min'_le _ _ (Finset.min'_mem _ _))
    (Finset.min'_le _ _ (Finset.min'_mem _ _))

/-- Two canonical composites whose read indices agree (up to the corresponding transport of the
index) are equal.  This is `Work.DSCOH.Norm.canonical_comp_eq` without the unused `Fintype ι`
hypothesis that the surrounding file carries as a section variable. -/
private lemma canonical_comp_eq_of_eq {X : Type*} [TopologicalSpace X] {A : Type*} [CommRing A]
    {ι : Type*} [LinearOrder ι] {P : (Opens X)ᵒᵖ ⥤ ModuleCat A} {U : ι → Opens X} {k : ℕ}
    {u₁ u₂ : Work.DSCOH.Norm.SemiIdx ι k} (hu : u₁ = u₂) {W : (Opens X)ᵒᵖ}
    {α₁ : op (Work.DSCOH.Norm.tupleOp U u₁.val) ⟶ W}
    {α₂ : op (Work.DSCOH.Norm.tupleOp U u₂.val) ⟶ W} :
    P.map α₁ = eqToHom (congrArg (fun v : Work.DSCOH.Norm.SemiIdx ι k => Work.DSCOH.Norm.tupleMod P U v.val) hu)
      ≫ P.map α₂ := by
  rw [← eqToHom_map P (p := congrArg
    (fun v : Work.DSCOH.Norm.SemiIdx ι k => op (Work.DSCOH.Norm.tupleOp U v.val)) hu)]
  rw [← P.map_comp]
  exact Work.DSCOH.Norm.tupleMod_map_eq α₁ (eqToHom _ ≫ α₂)

theorem Dterm_eq_neg_Hterm_castSucc {k : Nat} {ι : Type*} [LinearOrder ι] {X : Type*}
    [TopologicalSpace X] {A : Type*} [CommRing A]
    [CategoryTheory.Limits.HasProducts (ModuleCat A)]
    (P : CategoryTheory.Functor (Opposite (TopologicalSpace.Opens X)) (ModuleCat A))
    (U : ι → TopologicalSpace.Opens X)
    (y : Work.DSCOH.Norm.SemiIdx ι (k + 1)) (hy : Monotone y.val) (hh : Not (StrictMono y.val))
    (b : Fin (k + 2)) (hb : (b : Nat) < (Work.DSCOH.Norm.frA y.val hy hh : Nat)) :
    Work.DSCOH.Norm.Dterm P U k y b = - Work.DSCOH.Norm.Hterm P U k y b.castSucc := by
  -- The statement's monotonicity proof may be replaced by the canonical one.
  rw [frA_congr_monotone y.val hy y.property hh] at hb
  -- `del y b` still has the repeat of `y` at `frA y`, so it is not strictly increasing.
  have hz : ¬ StrictMono (Work.DSCOH.Norm.del y.val b) := by
    intro hsm
    have hspec : y.val (Work.DSCOH.Norm.frA y.val y.property hh).castSucc
        = y.val (Work.DSCOH.Norm.frA y.val y.property hh).succ := by
      unfold Work.DSCOH.Norm.frA
      exact Work.DSCOH.Norm.firstRepeat_spec y.val y.property hh
    have hne : (Work.DSCOH.Norm.frA y.val y.property hh).castSucc
        ≠ (Work.DSCOH.Norm.frA y.val y.property hh).succ := Fin.castSucc_lt_succ.ne
    rcases Work.DSCOH.Norm.strictMono_del_apply_eq hsm hne hspec with h | h
    · rw [h] at hb; simp only [Fin.val_castSucc] at hb; omega
    · rw [h] at hb; simp only [Fin.val_succ] at hb; omega
  -- Expand both terms.
  unfold Work.DSCOH.Norm.Hterm
  rw [dite_eq_right hh]
  unfold Work.DSCOH.Norm.Dterm
  rw [Work.DSCOH.Norm.semiHomComp_of_not_strictMono P U hz]
  simp only [Linear.smul_comp, Category.assoc, smul_smul]
  set fr := Work.DSCOH.Norm.firstRepeat (Work.DSCOH.Norm.del y.val b)
    (Work.DSCOH.Norm.monotone_del y.val b y.property) hz with hfr
  -- The read index of the `b`-th term of the first differential is the deletion of the
  -- `(b+1)`-st position of the tuple obtained by duplicating the first repeat of `y`.
  have hreadD1 : Work.DSCOH.Norm.readD y.val y.property hh b
      = Work.DSCOH.Norm.dup (Work.DSCOH.Norm.del y.val b) fr.castSucc := by
    unfold Work.DSCOH.Norm.readD
    rw [dite_eq_right hz]
  have hreadD2 : Work.DSCOH.Norm.readD y.val y.property hh b
      = Work.DSCOH.Norm.del (Work.DSCOH.Norm.dup y.val
          (Work.DSCOH.Norm.frA y.val y.property hh).castSucc) b.castSucc :=
    (Work.DSCOH.Struct.readD_lt y.val y.property hh b hb).1
  have hreadD : Work.DSCOH.Norm.dup (Work.DSCOH.Norm.del y.val b) fr.castSucc
      = Work.DSCOH.Norm.del (Work.DSCOH.Norm.dup y.val
          (Work.DSCOH.Norm.frA y.val y.property hh).castSucc) b.castSucc := hreadD1 ▸ hreadD2
  -- The two signs agree: `(-1)^(b + firstRepeat (del y b)) = -(-1)^(frA y + b)`.
  have hsign1 : (-1 : ℤ) ^ (b : ℕ) * (-1 : ℤ) ^ (fr : ℕ)
      = (-1 : ℤ) ^ ((b : ℕ) + (fr : ℕ)) := by rw [pow_add]
  have hsign2 : (-1 : ℤ) ^ ((b : ℕ) + (fr : ℕ)) = Work.DSCOH.Norm.signD y.val y.property hh b := by
    rw [Work.DSCOH.Norm.signD, dite_eq_right hz]
  have hsign3 : Work.DSCOH.Norm.signD y.val y.property hh b
      = -(-1 : ℤ) ^ ((Work.DSCOH.Norm.frA y.val y.property hh : ℕ) + (b : ℕ)) :=
    (Work.DSCOH.Struct.readD_lt y.val y.property hh b hb).2
  have hsign : (-1 : ℤ) ^ (b : ℕ) * (-1 : ℤ) ^ (fr : ℕ)
      = -(-1 : ℤ) ^ ((Work.DSCOH.Norm.frA y.val y.property hh : ℕ) + (b : ℕ)) :=
    hsign1.trans (hsign2.trans hsign3)
  -- Both tails are canonical composites at the same read index.
  have hX1 : Work.DSCOH.Norm.isoDup P U (Work.DSCOH.Norm.del y.val b) fr.castSucc
        ≫ Work.DSCOH.Norm.resDel P U y.val b
      = P.map ((Work.DSCOH.Norm.opDup U (Work.DSCOH.Norm.del y.val b) fr.castSucc).op
          ≫ (homOfLE (leOfHom (Work.DSCOH.Norm.opDel U y.val b))).op) := by
    rw [Work.DSCOH.Norm.isoDup, Work.DSCOH.Norm.resDel, ← P.map_comp]
  have hX2 : Work.DSCOH.Norm.resDel P U
          (Work.DSCOH.Norm.dup y.val (Work.DSCOH.Norm.frA y.val y.property hh).castSucc) b.castSucc
        ≫ Work.DSCOH.Norm.isoDup P U y.val (Work.DSCOH.Norm.frA y.val y.property hh).castSucc
      = P.map ((homOfLE (leOfHom (Work.DSCOH.Norm.opDel U
            (Work.DSCOH.Norm.dup y.val (Work.DSCOH.Norm.frA y.val y.property hh).castSucc) b.castSucc))).op
          ≫ (Work.DSCOH.Norm.opDup U y.val (Work.DSCOH.Norm.frA y.val y.property hh).castSucc).op) := by
    rw [Work.DSCOH.Norm.isoDup, Work.DSCOH.Norm.resDel, ← P.map_comp]
  have hSemi : (⟨Work.DSCOH.Norm.dup (Work.DSCOH.Norm.del y.val b) fr.castSucc,
        Work.DSCOH.Norm.monotone_dup (Work.DSCOH.Norm.monotone_del y.val b y.property) _⟩
        : Work.DSCOH.Norm.SemiIdx ι (k + 1))
      = ⟨Work.DSCOH.Norm.del (Work.DSCOH.Norm.dup y.val
            (Work.DSCOH.Norm.frA y.val y.property hh).castSucc) b.castSucc,
          Work.DSCOH.Norm.monotone_del _ _ (Work.DSCOH.Norm.monotone_dup y.property _)⟩ :=
    Subtype.ext hreadD
  have hkey := canonical_comp_eq_of_eq (P := P) (U := U) hSemi
      (α₁ := (Work.DSCOH.Norm.opDup U (Work.DSCOH.Norm.del y.val b) fr.castSucc).op
          ≫ (homOfLE (leOfHom (Work.DSCOH.Norm.opDel U y.val b))).op)
      (α₂ := (homOfLE (leOfHom (Work.DSCOH.Norm.opDel U
            (Work.DSCOH.Norm.dup y.val (Work.DSCOH.Norm.frA y.val y.property hh).castSucc) b.castSucc))).op
          ≫ (Work.DSCOH.Norm.opDup U y.val (Work.DSCOH.Norm.frA y.val y.property hh).castSucc).op)
  -- The two morphism parts coincide.
  have hXY : (Pi.π (fun w : Work.DSCOH.Norm.SemiIdx ι (k + 1) => Work.DSCOH.Norm.tupleMod P U w.val)
          ⟨Work.DSCOH.Norm.dup (Work.DSCOH.Norm.del y.val b) fr.castSucc,
            Work.DSCOH.Norm.monotone_dup (Work.DSCOH.Norm.monotone_del y.val b y.property) _⟩
        ≫ (Work.DSCOH.Norm.isoDup P U (Work.DSCOH.Norm.del y.val b) fr.castSucc
            ≫ Work.DSCOH.Norm.resDel P U y.val b))
      = (Pi.π (fun w : Work.DSCOH.Norm.SemiIdx ι (k + 1) => Work.DSCOH.Norm.tupleMod P U w.val)
          ⟨Work.DSCOH.Norm.del (Work.DSCOH.Norm.dup y.val
              (Work.DSCOH.Norm.frA y.val y.property hh).castSucc) b.castSucc,
            Work.DSCOH.Norm.monotone_del _ _ (Work.DSCOH.Norm.monotone_dup y.property _)⟩
        ≫ (Work.DSCOH.Norm.resDel P U
              (Work.DSCOH.Norm.dup y.val (Work.DSCOH.Norm.frA y.val y.property hh).castSucc) b.castSucc
            ≫ Work.DSCOH.Norm.isoDup P U y.val (Work.DSCOH.Norm.frA y.val y.property hh).castSucc)) := by
    rw [hX1, hX2, hkey, ← Category.assoc,
        Pi.π_comp_eqToHom
          (f := fun v : Work.DSCOH.Norm.SemiIdx ι (k + 1) => Work.DSCOH.Norm.tupleMod P U v.val) hSemi]
  rw [Fin.val_castSucc, hsign, neg_smul, hXY]

end Work.DSCOH.Pair
