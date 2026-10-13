/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Almost acyclicity, degree `0` (node PERF)

Clause (1) of `DSMap.Mix2.AlmostAcyc` for the perfected Čech complex: an element of `W` whose
image under the coaugmentation vanishes is annihilated by the whole root tower.
-/
import Mathlib
import Submission.Work.DSEQP.PerfAlmost
import Submission.Work.DSEQP.glue_sections
import Submission.Work.DSEQP.sections_eq_zero_of_restrict_eq_zero

open CategoryTheory AlgebraicGeometry Limits Opposite
open scoped Simplicial BigOperators

namespace Work.DSEQP

universe u

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000

namespace PerfSetup

variable {A : Type u} [CommRing A] {p : ℕ} [Fact p.Prime] {X : Scheme.{u}} [IsIntegral X]
  {f : X ⟶ Spec (.of A)} {ι : Type u}

/-- The sections of an integral scheme over any open are reduced. -/
theorem isReduced_gamma (V : X.Opens) : IsReduced Γ(X, V) := by
  rcases V.1.eq_empty_or_nonempty with h | h
  · have hbot : V = ⊥ := SetLike.ext' h
    have : Subsingleton Γ(X, V) :=
      CommRingCat.subsingleton_of_isTerminal (X.sheaf.isTerminalOfEqEmpty hbot)
    infer_instance
  · have : Nonempty V := by simpa using h
    infer_instance

/-- The product of the single-index family of opens `U i` over `Fin 1 → ι` is `U i`. -/
theorem piObj_const_eq (U : ι → X.Opens) (i : ι) :
    (∏ᶜ (fun _ : Fin 1 => U i) : X.Opens) = U i := by
  refine le_antisymm ?_ ?_
  · exact leOfHom (Pi.π (fun _ : Fin 1 => U i) ⟨0, by omega⟩)
  · exact leOfHom (Pi.lift (fun _ : Fin 1 => homOfLE (le_refl (U i))))


/-- **Clause (1) of almost acyclicity.** An element of `W` whose image under the coaugmentation
`eK` vanishes is annihilated by the whole root tower. -/
theorem almostAcyc_one (S : PerfSetup A p X f) [CharP S.W p] [PerfectRing S.W p]
    (U : ι → X.Opens) (hcov : ⨆ i, U i = ⊤)
    (g : A) (w : S.W) (h : (S.eK U).hom w = 0) (k : ℕ) : S.varpi g k * w = 0 := by
  obtain ⟨n, x, hx⟩ := Perf.exists_of (Γ(X, ⊤)) p (S.hpU ⊤) w
  rw [← hx] at h ⊢
  -- every component of the coaugmentation vanishes
  have hcomp : ∀ a : (CechIdx U 0).I, S.resTop (CechOp U 0 a) x = 0 := by
    intro a
    have h2 := eK_π S U a (Perf.of (Γ(X, ⊤)) p (S.hpU ⊤) n x)
    have h3 : (Pi.π (S.Kobj U 0) a)
        ((S.eK U).hom (Perf.of (Γ(X, ⊤)) p (S.hpU ⊤) n x) : ↥(∏ᶜ S.Kobj U 0)) = 0 := by
      rw [show ((S.eK U).hom (Perf.of (Γ(X, ⊤)) p (S.hpU ⊤) n x) :
          ↥(∏ᶜ S.Kobj U 0)) = 0 from h]
      exact map_zero _
    have h4 : S.Wmap (CechOp U 0 a) (Perf.of (Γ(X, ⊤)) p (S.hpU ⊤) n x) = 0 := by
      rw [← h2]; exact h3
    rw [Wmap] at h4
    rw [Perf.map_of] at h4
    exact Perf.of_eq_zero (R := Γ(X, CechOp U 0 a)) (p := p)
      (hp := S.hpU (CechOp U 0 a)) h4
  -- restrict to the cover `U` and use separatedness
  have hone : ∀ i : ι, S.resTop (U i) x = 0 := by
    intro i
    have h1 := hcomp (fun _ : Fin 1 => i)
    have h2 : CechOp U 0 (fun _ : Fin 1 => i) = U i := piObj_const_eq U i
    rwa [h2] at h1
  have hx0 : x = 0 :=
    sections_eq_zero_of_restrict_eq_zero U hcov x hone
  rw [hx0, map_zero, mul_zero]

end PerfSetup

end Work.DSEQP
