/-
Area DSCOH (curric-46) — the normalization comparison: the pairing of the `b`-th term of the first
differential with the `(b+1)`-st term of the second differential, in the case `frA y + 2 ≤ b`.

For a nondecreasing but not strictly increasing tuple `y : Fin (k+2) → ι`, the `y`-component of
`dh + hd` expands as `∑_b Dterm b + ∑_c Hterm c` (`Work.DSCOH.Norm.lhs_eq_sum`), and the homotopy
identity is proved by pairing the individual terms.  The terms `Dterm b` for `b ≠ frA y, frA y + 1`
pair with `Hterm` at a shifted index; this file treats the "far right" range `frA y + 2 ≤ b`, where

* deleting `b` leaves the repeat of `y` at `frA y` in place, and the read index
  `readD y b = dup (del y b) (firstRepeat (del y b))⁺` of `Dterm b` equals `readH y b.succ`, the
  read index of `Hterm (b.succ)` (the middle case `b ≤ frA2 y` gives `readD y b = y = readH y b.succ`
  by `readD_mid`/`readH_eq`, the far case `frA2 y < b` gives both as
  `del (dup y (frA y)⁺) b.succ` by `readD_gt`); this is the delegated lemma
  `Work.DSCOH.Pair.readD_readH_far`;
* the signs satisfy `signD y b = -signH y (b.succ)` (delegated lemma
  `Work.DSCOH.Pair.signD_eq_neg_signH_far`), so `(-1)^b * (-1)^frA = -(-1)^(frA + (b+1))`.

Since the two read composites are built out of the canonical maps `opDup`/`opDel` of `Opens X`,
whose hom-sets are subsingletons, they agree as soon as their read indices do
(`Work.DSCOH.Norm.tupleMod_map_eq` / the helper `pi_π_map_eq` below).  Hence
`Dterm P U k y b = - Hterm P U k y b.succ`.
-/
import Mathlib
import Submission.Work.DSCOH.Norm.HomoAssembly
import Submission.Work.DSCOH.Norm.HomoStruct
import Submission.Work.DSCOH.Struct.readD_mid
import Submission.Work.DSCOH.Struct.readD_gt
import Submission.Work.DSCOH.Struct.readH_eq
import Submission.Work.DSCOH.Pair.readD_readH_far
import Submission.Work.DSCOH.Pair.signD_eq_neg_signH_far

namespace Work.DSCOH.Pair

open CategoryTheory Limits Opposite TopologicalSpace
open scoped BigOperators

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

/-- Two components of a product over the semi-ordered index set whose read indices agree (and whose
structure maps are canonical, i.e. live in a hom-set of `Opens X`) are equal: the only obstruction
is the read index, and `Opens X` has subsingleton hom-sets. -/
lemma pi_π_map_eq {ι : Type*} [LinearOrder ι] {X : Type*} [TopologicalSpace X] {A : Type*}
    [CommRing A] [CategoryTheory.Limits.HasProducts (ModuleCat A)]
    (P : (Opens X)ᵒᵖ ⥤ ModuleCat A) (U : ι → Opens X) {k : ℕ}
    {u₁ u₂ : Work.DSCOH.Norm.SemiIdx ι (k + 1)} (hu : u₁ = u₂) {W : (Opens X)ᵒᵖ}
    {β₁ : op (Work.DSCOH.Norm.tupleOp U u₁.val) ⟶ W}
    {β₂ : op (Work.DSCOH.Norm.tupleOp U u₂.val) ⟶ W} :
    Pi.π (fun x : Work.DSCOH.Norm.SemiIdx ι (k + 1) => Work.DSCOH.Norm.tupleMod P U x.val) u₁
        ≫ P.map β₁ =
      Pi.π (fun x : Work.DSCOH.Norm.SemiIdx ι (k + 1) => Work.DSCOH.Norm.tupleMod P U x.val) u₂
        ≫ P.map β₂ := by
  cases hu
  congr 1
  exact Work.DSCOH.Norm.tupleMod_map_eq β₁ β₂

theorem Dterm_eq_neg_Hterm_succ {k : Nat} {ι : Type*} [LinearOrder ι] {X : Type*}
    [TopologicalSpace X] {A : Type*} [CommRing A]
    [CategoryTheory.Limits.HasProducts (ModuleCat A)]
    (P : CategoryTheory.Functor (Opposite (TopologicalSpace.Opens X)) (ModuleCat A))
    (U : ι → TopologicalSpace.Opens X)
    (y : Work.DSCOH.Norm.SemiIdx ι (k + 1)) (hy : Monotone y.val) (hh : Not (StrictMono y.val))
    (b : Fin (k + 2)) (hb : (Work.DSCOH.Norm.frA y.val hy hh : Nat) + 2 ≤ (b : Nat)) :
    Work.DSCOH.Norm.Dterm P U k y b = - Work.DSCOH.Norm.Hterm P U k y b.succ := by
  -- `Dterm`/`Hterm` use the bundled monotonicity proof `y.property`; the given `hy` is only needed
  -- to state the hypothesis `hb`, and `frA` is insensitive to which proof it is fed.
  have hb' : (Work.DSCOH.Norm.frA y.val y.property hh : Nat) + 2 ≤ (b : Nat) := hb
  obtain ⟨hz, hRD⟩ := readD_readH_far y.val y.property hh b hb'
  have hSD := signD_eq_neg_signH_far y.val y.property hh b hb'
  -- the read indices agree, in the unfolded form in which the goal uses them
  have hdup : Work.DSCOH.Norm.dup (Work.DSCOH.Norm.del y.val b)
      (Work.DSCOH.Norm.firstRepeat (Work.DSCOH.Norm.del y.val b)
        (Work.DSCOH.Norm.monotone_del y.val b y.property) hz).castSucc
      = Work.DSCOH.Norm.del
        (Work.DSCOH.Norm.dup y.val (Work.DSCOH.Norm.frA y.val y.property hh).castSucc)
        b.succ := by
    have h := hRD
    rw [Work.DSCOH.Norm.readD, dite_eq_right hz, Work.DSCOH.Norm.readH] at h
    exact h
  -- the signs agree, in the unfolded form in which the goal uses them
  have hSD' : (-1 : ℤ) ^ ((b : ℕ) + ((Work.DSCOH.Norm.firstRepeat (Work.DSCOH.Norm.del y.val b)
        (Work.DSCOH.Norm.monotone_del y.val b y.property) hz : Fin k) : ℕ))
      = - ((-1 : ℤ) ^ ((Work.DSCOH.Norm.frA y.val y.property hh : ℕ) + (b.succ : ℕ))) := by
    have h := hSD
    rw [Work.DSCOH.Norm.signD, dite_eq_right hz, Work.DSCOH.Norm.signH] at h
    exact h
  -- the two read composites agree: both are canonical maps into `tupleMod P U y.val`, and the two
  -- read indices coincide by `hdup`
  have hZ : (Pi.π (fun w : Work.DSCOH.Norm.SemiIdx ι (k + 1) => Work.DSCOH.Norm.tupleMod P U w.val)
          ⟨Work.DSCOH.Norm.dup (Work.DSCOH.Norm.del y.val b)
              (Work.DSCOH.Norm.firstRepeat (Work.DSCOH.Norm.del y.val b)
                (Work.DSCOH.Norm.monotone_del y.val b y.property) hz).castSucc,
            Work.DSCOH.Norm.monotone_dup (Work.DSCOH.Norm.monotone_del y.val b y.property) _⟩
        ≫ Work.DSCOH.Norm.isoDup P U (Work.DSCOH.Norm.del y.val b)
            (Work.DSCOH.Norm.firstRepeat (Work.DSCOH.Norm.del y.val b)
              (Work.DSCOH.Norm.monotone_del y.val b y.property) hz).castSucc)
      ≫ Work.DSCOH.Norm.resDel P U y.val b
    = Pi.π (fun w : Work.DSCOH.Norm.SemiIdx ι (k + 1) => Work.DSCOH.Norm.tupleMod P U w.val)
          ⟨Work.DSCOH.Norm.del (Work.DSCOH.Norm.dup y.val
              (Work.DSCOH.Norm.frA y.val y.property hh).castSucc) b.succ,
            Work.DSCOH.Norm.monotone_del _ _ (Work.DSCOH.Norm.monotone_dup y.property _)⟩
        ≫ (Work.DSCOH.Norm.resDel P U
              (Work.DSCOH.Norm.dup y.val (Work.DSCOH.Norm.frA y.val y.property hh).castSucc) b.succ
            ≫ Work.DSCOH.Norm.isoDup P U y.val
                (Work.DSCOH.Norm.frA y.val y.property hh).castSucc) := by
    rw [Category.assoc]
    rw [show Work.DSCOH.Norm.isoDup P U (Work.DSCOH.Norm.del y.val b)
          (Work.DSCOH.Norm.firstRepeat (Work.DSCOH.Norm.del y.val b)
            (Work.DSCOH.Norm.monotone_del y.val b y.property) hz).castSucc
          ≫ Work.DSCOH.Norm.resDel P U y.val b
        = P.map ((Work.DSCOH.Norm.opDup U (Work.DSCOH.Norm.del y.val b)
              (Work.DSCOH.Norm.firstRepeat (Work.DSCOH.Norm.del y.val b)
                (Work.DSCOH.Norm.monotone_del y.val b y.property) hz).castSucc).op
            ≫ (homOfLE (leOfHom (Work.DSCOH.Norm.opDel U y.val b))).op) from by
      rw [Work.DSCOH.Norm.isoDup, Work.DSCOH.Norm.resDel, ← P.map_comp]]
    rw [show Work.DSCOH.Norm.resDel P U
          (Work.DSCOH.Norm.dup y.val (Work.DSCOH.Norm.frA y.val y.property hh).castSucc) b.succ
          ≫ Work.DSCOH.Norm.isoDup P U y.val (Work.DSCOH.Norm.frA y.val y.property hh).castSucc
        = P.map (((homOfLE (leOfHom (Work.DSCOH.Norm.opDel U
                (Work.DSCOH.Norm.dup y.val (Work.DSCOH.Norm.frA y.val y.property hh).castSucc)
                b.succ))).op)
            ≫ (Work.DSCOH.Norm.opDup U y.val
                (Work.DSCOH.Norm.frA y.val y.property hh).castSucc).op)
        from by
      rw [Work.DSCOH.Norm.isoDup, Work.DSCOH.Norm.resDel, ← P.map_comp]]
    apply pi_π_map_eq (P := P) (U := U)
    exact Subtype.ext hdup
  -- unfold the two terms and compare
  rw [Work.DSCOH.Norm.Dterm, Work.DSCOH.Norm.Hterm, dite_eq_right hh,
    Work.DSCOH.Norm.semiHomComp_of_not_strictMono (P := P) (U := U) hz]
  rw [Linear.smul_comp]
  rw [hZ]
  rw [smul_smul, ← pow_add, hSD']
  rw [neg_smul]

end Work.DSCOH.Pair
