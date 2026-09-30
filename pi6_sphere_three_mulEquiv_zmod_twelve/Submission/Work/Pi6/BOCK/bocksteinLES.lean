import Mathlib
import Submission.Work.Pi6.Interfaces
import Submission.Work.Pi6.EMZ.BocksteinCore
import Submission.Work.Pi6.BOCK.Defs
import Submission.Work.Pi6.BOCK.CoeffIso
import Submission.Work.Pi6.BOCK.BockMaps
import Submission.Work.Pi6.BOCK.BockExact
import Submission.Work.Pi6.BOCK.BockNatural
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-! Guidance from the project lead (the requester):

AREA BOCK — the ONE shared homology Bockstein module for the pi6 fleet (lead decision 2026-09-28: areas EMZ, SQASM,
HALG each started their own; those three children were cancelled and the areas will import THIS). Statement: for a
prime p, the Bockstein long exact sequence H_{n+1}(X;ℤ) →·p H_{n+1}(X;ℤ) →red H_{n+1}(X;ℤ/p) →del H_n(X;ℤ) →·p H_n(X;ℤ),
natural in continuous maps (red and del commute with hmap).
Route: coefficient short exact sequence 0 → ℤ →·p ℤ → ℤ/p → 0, tensored with the degreewise-free singular chains
(Work.SSS.expTens / expTensShort / expTensShort_shortExact, Work.SSS.ExpTensLES) gives a short exact sequence of chain
complexes; HomologicalComplex.HomologySequence gives exactness (ShortComplex.ShortExact.homology_exact₁/₂/₃) and
δ_naturality gives naturality of del; identify H_n(C_*(X;ℤ)⊗ℤ/p) with HR (ZMod p) X n (Work.SSS.chainCoeffExpIso,
restriction of scalars, Work.StemsB.SphRat.homologyMapBaseChange).
REUSE: Submission/Work/Pi6/EMZ/BocksteinCore.lean is sorry-free and has exactly this setup for general p (coeffSES,
bockSES_shortExact, expTensUnitHomologyIso, chainBaseChangeHomology, expTensCoeffAddEquiv) — import it. The cancelled
drafts are in REFS/bock_drafts/ (EMZ_bocksteinLES = most advanced, 190 lines; SQASM_bocksteinDefs has the naturality
setup; HALG_bockstein_draft). Put helpers under Pi6/BOCK/. Build each ModuleCat diagram chase in its own small lemma
(heartbeat timeouts hit SRANGE on large chases).
-/

namespace Work.Pi6.BOCK

theorem bocksteinLES (p : ℕ) (hp : p.Prime) :
    ∃ (red : ∀ {X : Type} [TopologicalSpace X] (n : ℕ), Work.Pi6.HR ℤ X n →+ Work.Pi6.HR (ZMod p) X n)
      (del : ∀ {X : Type} [TopologicalSpace X] (n : ℕ),
        Work.Pi6.HR (ZMod p) X (n + 1) →+ Work.Pi6.HR ℤ X n),
      (∀ (X : Type) [TopologicalSpace X] (n : ℕ),
        Function.Exact (fun x : Work.Pi6.HR ℤ X n => (p : ℤ) • x) ⇑(red (X := X) n)) ∧
      (∀ (X : Type) [TopologicalSpace X] (n : ℕ),
        Function.Exact ⇑(red (X := X) (n + 1)) ⇑(del (X := X) n)) ∧
      (∀ (X : Type) [TopologicalSpace X] (n : ℕ),
        Function.Exact ⇑(del (X := X) n) (fun x : Work.Pi6.HR ℤ X n => (p : ℤ) • x)) ∧
      (∀ (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) (n : ℕ)
        (x : Work.Pi6.HR ℤ X n),
        red (X := Y) n ((Work.Pi6.hmap ℤ f n).hom x) =
          (Work.Pi6.hmap (ZMod p) f n).hom (red (X := X) n x)) ∧
      (∀ (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) (n : ℕ)
        (x : Work.Pi6.HR (ZMod p) X (n + 1)),
        del (X := Y) n ((Work.Pi6.hmap (ZMod p) f (n + 1)).hom x) =
          (Work.Pi6.hmap ℤ f n).hom (del (X := X) n x)) :=
  ⟨fun {X} _ n => redHom p hp X n, fun {X} _ n => delHom p hp X n,
   fun X _ n => redHom_exact p hp X n,
   fun X _ n => redHom_delHom_exact p hp X n,
   fun X _ n => delHom_exact p hp X n,
   fun X Y _ _ f n x => redHom_natural p hp f n x,
   fun X Y _ _ f n y => delHom_natural p hp f n y⟩

end Work.Pi6.BOCK
