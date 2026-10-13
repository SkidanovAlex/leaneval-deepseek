import Mathlib
import Submission.Work.DSEQP.PerfAcyclic
import Submission.Work.DSEQP.PerfRing
import Submission.Work.DSEQP.PerfCech
import Submission.Work.DSEQP.AcInj

namespace Work.DSEQP.PerfCechZero

open CategoryTheory AlgebraicGeometry Limits Opposite

universe u

set_option maxHeartbeats 4000000

theorem exists_level_compat (A : Type u) [CommRing A] (p : ℕ) [Fact p.Prime]
    (X : AlgebraicGeometry.Scheme.{u}) [AlgebraicGeometry.IsIntegral X]
    (f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of A))
    (S : Work.DSEQP.PerfSetup A p X f) {ι : Type u} [Finite ι] (U : ι → X.Opens)
    (z : (S.K U).X 0) (ϖ : S.W)
    (hcompat : ∀ a b : (PerfSetup.CechIdx U 0).I,
      Work.DSEQP.Perf.map (S.hpU (PerfSetup.CechOp U 0 a))
          (S.hpU (PerfSetup.CechOp U 0 a ⊓ PerfSetup.CechOp U 0 b))
          ((X.presheaf.map (CategoryTheory.homOfLE
            (inf_le_left : PerfSetup.CechOp U 0 a ⊓ PerfSetup.CechOp U 0 b ≤
              PerfSetup.CechOp U 0 a)).op).hom)
          ((CategoryTheory.Limits.Pi.π (S.Kobj U 0) a).hom z)
        = Work.DSEQP.Perf.map (S.hpU (PerfSetup.CechOp U 0 b))
          (S.hpU (PerfSetup.CechOp U 0 a ⊓ PerfSetup.CechOp U 0 b))
          ((X.presheaf.map (CategoryTheory.homOfLE
            (inf_le_right : PerfSetup.CechOp U 0 a ⊓ PerfSetup.CechOp U 0 b ≤
              PerfSetup.CechOp U 0 b)).op).hom)
          ((CategoryTheory.Limits.Pi.π (S.Kobj U 0) b).hom z)) :
    ∃ (N : ℕ) (lam : ↑(X.presheaf.obj (Opposite.op (⊤ : X.Opens))))
      (y : ∀ a : (PerfSetup.CechIdx U 0).I,
        ↑(X.presheaf.obj (Opposite.op (PerfSetup.CechOp U 0 a)))),
      Work.DSEQP.Perf.of (↑(X.presheaf.obj (Opposite.op (⊤ : X.Opens)))) p
          (S.hpU ⊤) N lam = ϖ ∧
      (∀ a, Work.DSEQP.Perf.of (↑(X.presheaf.obj (Opposite.op (PerfSetup.CechOp U 0 a)))) p
          (S.hpU (PerfSetup.CechOp U 0 a)) N (y a)
        = (CategoryTheory.Limits.Pi.π (S.Kobj U 0) a).hom z) ∧
      (∀ a b, (X.presheaf.map (CategoryTheory.homOfLE
          (inf_le_left : PerfSetup.CechOp U 0 a ⊓ PerfSetup.CechOp U 0 b ≤
            PerfSetup.CechOp U 0 a)).op).hom (y a)
        = (X.presheaf.map (CategoryTheory.homOfLE
          (inf_le_right : PerfSetup.CechOp U 0 a ⊓ PerfSetup.CechOp U 0 b ≤
            PerfSetup.CechOp U 0 b)).op).hom (y b)) := by
  classical
  -- the degree-`0` Čech index type is finite, so the family of component levels has a maximum
  haveI : Fintype (PerfSetup.CechIdx U 0).I := Fintype.ofFinite (Fin 1 → ι)
  -- a representative of each component of `z`
  choose e xe hxe using fun a : (PerfSetup.CechIdx U 0).I =>
    Perf.exists_of (R := Γ(X, PerfSetup.CechOp U 0 a)) (p := p) (hp := S.hpU _)
      ((CategoryTheory.Limits.Pi.π (S.Kobj U 0) a).hom z)
  -- a representative of `ϖ`
  obtain ⟨ew, lamw, hw⟩ := Perf.exists_of (R := Γ(X, ⊤)) (p := p) (hp := S.hpU ⊤) ϖ
  -- common level `E` for the components, and the raised representatives `Y`
  set E : ℕ := Finset.univ.sup e with hE
  have hsup : ∀ a, e a ≤ E := fun a => by rw [hE]; exact Finset.le_sup (Finset.mem_univ a)
  set Y : ∀ a : (PerfSetup.CechIdx U 0).I, Γ(X, PerfSetup.CechOp U 0 a) :=
    fun a => xe a ^ p ^ (E - e a) with hYdef
  have hY : ∀ a, Perf.of (Γ(X, PerfSetup.CechOp U 0 a)) p (S.hpU _) E (Y a)
      = (CategoryTheory.Limits.Pi.π (S.Kobj U 0) a).hom z := by
    intro a
    rw [hYdef]
    exact (Perf.of_f (R := Γ(X, PerfSetup.CechOp U 0 a)) (p := p) (hp := S.hpU _)
      (hsup a) (xe a)).trans (hxe a)
  -- the raised representatives are compatible on intersections, by injectivity of `Perf.of`
  -- on the reduced sections over the intersection and the compatibility hypothesis on `z`
  have hYcompat : ∀ a b, (X.presheaf.map (CategoryTheory.homOfLE
      (inf_le_left : PerfSetup.CechOp U 0 a ⊓ PerfSetup.CechOp U 0 b ≤
        PerfSetup.CechOp U 0 a)).op).hom (Y a)
      = (X.presheaf.map (CategoryTheory.homOfLE
      (inf_le_right : PerfSetup.CechOp U 0 a ⊓ PerfSetup.CechOp U 0 b ≤
        PerfSetup.CechOp U 0 b)).op).hom (Y b) := by
    intro a b
    haveI : IsReduced Γ(X, PerfSetup.CechOp U 0 a ⊓ PerfSetup.CechOp U 0 b) :=
      PerfSetup.isReduced_gamma _
    refine Perf.of_injective_of_isReduced
      (R := Γ(X, PerfSetup.CechOp U 0 a ⊓ PerfSetup.CechOp U 0 b)) (p := p)
      (S.hpU (PerfSetup.CechOp U 0 a ⊓ PerfSetup.CechOp U 0 b)) E ?_
    rw [← Perf.map_of (hp := S.hpU (PerfSetup.CechOp U 0 a))
          (hpS := S.hpU (PerfSetup.CechOp U 0 a ⊓ PerfSetup.CechOp U 0 b))
          ((X.presheaf.map (homOfLE (inf_le_left : PerfSetup.CechOp U 0 a ⊓
            PerfSetup.CechOp U 0 b ≤ PerfSetup.CechOp U 0 a)).op).hom) E (Y a),
        ← Perf.map_of (hp := S.hpU (PerfSetup.CechOp U 0 b))
          (hpS := S.hpU (PerfSetup.CechOp U 0 a ⊓ PerfSetup.CechOp U 0 b))
          ((X.presheaf.map (homOfLE (inf_le_right : PerfSetup.CechOp U 0 a ⊓
            PerfSetup.CechOp U 0 b ≤ PerfSetup.CechOp U 0 b)).op).hom) E (Y b),
        hY a, hY b]
    exact hcompat a b
  -- raise the level of both `ϖ` and the components to the common level `N`
  set N : ℕ := max E ew with hN
  refine ⟨N, lamw ^ p ^ (N - ew), (fun a => Y a ^ p ^ (N - E)), ?_, ?_, ?_⟩
  · rw [hN]
    exact (Perf.of_f (R := Γ(X, ⊤)) (p := p) (hp := S.hpU ⊤) (le_max_right E ew) lamw).trans hw
  · intro a
    rw [hN]
    exact (Perf.of_f (R := Γ(X, PerfSetup.CechOp U 0 a)) (p := p) (hp := S.hpU _)
      (le_max_left E ew) (Y a)).trans (hY a)
  · intro a b
    simp only [map_pow, hYcompat a b]

end Work.DSEQP.PerfCechZero
