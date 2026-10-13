/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Gluing a compatible family into the coaugmentation of the perfected Čech complex (node PERF)

If `y a ∈ Γ(X, CechOp U 0 a)` is a family of sections of the structure sheaf compatible on the
pairwise intersections of the degree-`0` Čech opens, then the family
`a ↦ resTop (CechOp U 0 a) lam * y a` glues to a global section `t ∈ Γ(X, ⊤)`, and the value
of the coaugmentation on the perfection `w = Perf.of t` of `t` is exactly
`Wmap (CechOp U 0 a) (Perf.of lam) * Perf.of (y a)` on the `a`-th coordinate.
-/
import Mathlib
import Submission.Work.DSEQP.PerfAcyclic
import Submission.Work.DSEQP.glue_sections

open CategoryTheory AlgebraicGeometry Limits Opposite
open scoped Simplicial BigOperators

namespace Work.DSEQP

universe u

theorem Wmap_eq_of_compat (A : Type u) [CommRing A] (p : ℕ) [Fact p.Prime]
    (X : AlgebraicGeometry.Scheme.{u})
    (f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of A))
    (S : Work.DSEQP.PerfSetup A p X f) {ι : Type u} (U : ι → X.Opens)
    (hcov : iSup (fun a : (PerfSetup.CechIdx U 0).I => PerfSetup.CechOp U 0 a) = ⊤)
    (N : ℕ) (lam : ↑(X.presheaf.obj (Opposite.op (⊤ : X.Opens))))
    (y : ∀ a : (PerfSetup.CechIdx U 0).I,
      ↑(X.presheaf.obj (Opposite.op (PerfSetup.CechOp U 0 a))))
    (hcompat : ∀ a b, (X.presheaf.map (CategoryTheory.homOfLE
        (inf_le_left : PerfSetup.CechOp U 0 a ⊓ PerfSetup.CechOp U 0 b ≤
          PerfSetup.CechOp U 0 a)).op).hom (y a)
      = (X.presheaf.map (CategoryTheory.homOfLE
        (inf_le_right : PerfSetup.CechOp U 0 a ⊓ PerfSetup.CechOp U 0 b ≤
          PerfSetup.CechOp U 0 b)).op).hom (y b)) :
    ∃ w : S.W, ∀ a : (PerfSetup.CechIdx U 0).I,
      S.Wmap (PerfSetup.CechOp U 0 a) w
        = S.Wmap (PerfSetup.CechOp U 0 a)
            (Work.DSEQP.Perf.of (↑(X.presheaf.obj (Opposite.op (⊤ : X.Opens)))) p
              (S.hpU ⊤) N lam)
          * Work.DSEQP.Perf.of (↑(X.presheaf.obj (Opposite.op (PerfSetup.CechOp U 0 a)))) p
              (S.hpU (PerfSetup.CechOp U 0 a)) N (y a) := by
  -- the family `resTop _ lam * y _` is compatible
  have hglue : ∀ a b, (X.presheaf.map (CategoryTheory.homOfLE
        (inf_le_left : PerfSetup.CechOp U 0 a ⊓ PerfSetup.CechOp U 0 b ≤
          PerfSetup.CechOp U 0 a)).op).hom
        (S.resTop (PerfSetup.CechOp U 0 a) lam * y a)
      = (X.presheaf.map (CategoryTheory.homOfLE
        (inf_le_right : PerfSetup.CechOp U 0 a ⊓ PerfSetup.CechOp U 0 b ≤
          PerfSetup.CechOp U 0 b)).op).hom
        (S.resTop (PerfSetup.CechOp U 0 b) lam * y b) := by
    intro a b
    rw [map_mul, map_mul]
    have ha : (X.presheaf.map (CategoryTheory.homOfLE
          (inf_le_left : PerfSetup.CechOp U 0 a ⊓ PerfSetup.CechOp U 0 b ≤
            PerfSetup.CechOp U 0 a)).op).hom (S.resTop (PerfSetup.CechOp U 0 a) lam)
        = S.resTop (PerfSetup.CechOp U 0 a ⊓ PerfSetup.CechOp U 0 b) lam :=
      (DFunLike.congr_fun (S.resTop_comp
        (inf_le_left : PerfSetup.CechOp U 0 a ⊓ PerfSetup.CechOp U 0 b ≤
          PerfSetup.CechOp U 0 a)) lam).symm
    have hb : (X.presheaf.map (CategoryTheory.homOfLE
          (inf_le_right : PerfSetup.CechOp U 0 a ⊓ PerfSetup.CechOp U 0 b ≤
            PerfSetup.CechOp U 0 b)).op).hom (S.resTop (PerfSetup.CechOp U 0 b) lam)
        = S.resTop (PerfSetup.CechOp U 0 a ⊓ PerfSetup.CechOp U 0 b) lam :=
      (DFunLike.congr_fun (S.resTop_comp
        (inf_le_right : PerfSetup.CechOp U 0 a ⊓ PerfSetup.CechOp U 0 b ≤
          PerfSetup.CechOp U 0 b)) lam).symm
    rw [ha, hb, hcompat a b]
  obtain ⟨t, ht⟩ := glue_sections (fun a : (PerfSetup.CechIdx U 0).I => PerfSetup.CechOp U 0 a)
    hcov (fun a => S.resTop (PerfSetup.CechOp U 0 a) lam * y a) hglue
  refine ⟨Work.DSEQP.Perf.of (↑(X.presheaf.obj (Opposite.op (⊤ : X.Opens)))) p (S.hpU ⊤) N t,
    fun a => ?_⟩
  have hWa : S.Wmap (PerfSetup.CechOp U 0 a)
      (Work.DSEQP.Perf.of (↑(X.presheaf.obj (Opposite.op (⊤ : X.Opens)))) p (S.hpU ⊤) N t)
      = Work.DSEQP.Perf.of (↑(X.presheaf.obj (Opposite.op (PerfSetup.CechOp U 0 a)))) p
          (S.hpU (PerfSetup.CechOp U 0 a)) N (S.resTop (PerfSetup.CechOp U 0 a) t) := by
    rw [PerfSetup.Wmap]
    exact Work.DSEQP.Perf.map_of (S.hpU ⊤) (S.hpU (PerfSetup.CechOp U 0 a))
      (S.resTop (PerfSetup.CechOp U 0 a)) N t
  have hWa' : Work.DSEQP.Perf.of (↑(X.presheaf.obj (Opposite.op (PerfSetup.CechOp U 0 a)))) p
        (S.hpU (PerfSetup.CechOp U 0 a)) N (S.resTop (PerfSetup.CechOp U 0 a) t)
      = Work.DSEQP.Perf.of (↑(X.presheaf.obj (Opposite.op (PerfSetup.CechOp U 0 a)))) p
          (S.hpU (PerfSetup.CechOp U 0 a)) N
            (S.resTop (PerfSetup.CechOp U 0 a) lam * y a) := by
    rw [show S.resTop (PerfSetup.CechOp U 0 a) t
        = S.resTop (PerfSetup.CechOp U 0 a) lam * y a from ht a]
  rw [hWa, hWa']
  rw [PerfSetup.Wmap]
  rw [Work.DSEQP.Perf.map_of (S.hpU ⊤) (S.hpU (PerfSetup.CechOp U 0 a))
    (S.resTop (PerfSetup.CechOp U 0 a)) N lam]
  exact map_mul _ _ _

end Work.DSEQP
