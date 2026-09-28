import Mathlib
import Submission.Work.SSS.Packet
import Submission.Work.SSS.fg_range_of_ker_le
import Submission.Work.SSS.gfDefs
import Submission.Work.SSS.GradedKer.ker_e2MapG_le
import Submission.Work.SSS.GradedZero.graded_zero

/-!
# The graded pieces of the image filtration are subquotients of the `E²` page

`Work.SSS.gradedField` is the `graded` field of `Work.SSS.SSPacket`: for a saturated filtration `ξ`
of a chain complex of `ℤ`-modules, if `E²_{s,n-s}` is finitely generated and `Φ_{s-1}` is finitely
generated, then so is `Φ_s = im(H_n(F_s) → H_n(C))`.

The proof is the standard one: the canonical map `H_n(F_s) → E²_{s,n-s}` (whose kernel is
`ker(jF) + ker(H_n(incl s))`) exhibits `Φ_s/Φ_{s-1}` as a quotient of a submodule of `E²_{s,n-s}`;
we phrase the finiteness bookkeeping as `Work.SSS.fg_range_of_ker_le`.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace Work.SSS

open CategoryTheory CategoryTheory.Limits

noncomputable section

variable {C : ChainComplex (ModuleCat ℤ) ℕ}

/-- The successor step: `Φ_k` finitely generated and `E²_{k+1,n-k-1}` finitely generated imply
`Φ_{k+1}` finitely generated. -/
theorem graded_succ (ξ : Filtration C) (n k : ℕ) (hk : k + 1 ≤ n)
    (hE : Module.Finite ℤ (E2 ξ (k+1) (n - (k+1))))
    (hP : (Phi ξ n (k : ℤ)).FG) :
    (Phi ξ n (((k+1 : ℕ) : ℤ))).FG := by
  let t := n - (k+1)
  have ht : (k+1) + t = n := by dsimp only [t]; exact Nat.add_sub_of_le hk
  -- finiteness of the target of `e2MapG`
  have hES : Module.Finite ℤ ↥(((E1Complex ξ t).sc' (k+2) (k+1) k).homology) := by
    have e : (E1Complex ξ t).homology (k+1) ≅
        ((E1Complex ξ t).sc' (k+2) (k+1) k).homology :=
      HomologicalComplex.homologyIsoSc' (E1Complex ξ t) (k+2) (k+1) k (by simp) (by simp)
    haveI : Module.Finite ℤ ↥((E1Complex ξ t).homology (k+1)) := hE
    exact Module.Finite.equiv e.toLinearEquiv
  have hφfin : ((e2MapG ξ k t).hom.range).FG :=
    Submodule.FG.of_le (Module.finite_def.mp hES) le_top
  have hker := GradedKer.ker_e2MapG_le C ξ k t
  -- `γ(im β) = Φ_k`
  have hM : (Submodule.map (HomologicalComplex.homologyMap (ξ.incl (k+1)) ((k+1)+t)).hom
      (HomologicalComplex.homologyMap (incF ξ.F k) ((k+1)+t)).hom.range).FG := by
    have hcomp : (HomologicalComplex.homologyMap (ξ.incl (k+1)) ((k+1)+t)).hom.comp
        (HomologicalComplex.homologyMap (incF ξ.F k) ((k+1)+t)).hom =
        (HomologicalComplex.homologyMap (ξ.incl k) ((k+1)+t)).hom := by
      have h1 : ξ.incl k = incF ξ.F k ≫ ξ.incl (k+1) := (ξ.compat (Nat.le_succ k)).symm
      rw [h1, HomologicalComplex.homologyMap_comp, ModuleCat.hom_comp]
    rw [← LinearMap.range_comp
      (HomologicalComplex.homologyMap (incF ξ.F k) ((k+1)+t)).hom
      (HomologicalComplex.homologyMap (ξ.incl (k+1)) ((k+1)+t)).hom, hcomp]
    exact FGrng (ξ.incl k) ht.symm hP
  have hmain := fg_range_of_ker_le
    (HomologicalComplex.homologyMap (ξ.incl (k+1)) ((k+1)+t)).hom (e2MapG ξ k t).hom
    (HomologicalComplex.homologyMap (incF ξ.F k) ((k+1)+t)).hom.range hker hφfin hM
  -- transport from degree `(k+1)+t` to degree `n`
  have hPhi : Phi ξ n (((k+1 : ℕ) : ℤ)) =
      LinearMap.range (HomologicalComplex.homologyMap (ξ.incl (k+1)) n).hom := by
    simp only [Phi, Int.toNat_natCast, if_neg (show ¬ (((k+1 : ℕ) : ℤ) < 0) by omega)]
  rw [hPhi]
  exact FGrng (ξ.incl (k+1)) ht hmain

end

section Zero

variable {C : ChainComplex (ModuleCat ℤ) ℕ}

theorem gradedField (C : ChainComplex (ModuleCat ℤ) ℕ) (ξ : Work.SSS.Filtration C) (n s : ℕ)
    (hs : (s : ℤ) ≤ n) (hE : Module.Finite ℤ (Work.SSS.E2 ξ s (n - s)))
    (hP : (Work.SSS.Phi ξ n ((s : ℤ) - 1)).FG) :
    (Work.SSS.Phi ξ n (s : ℤ)).FG := by
  rcases Nat.eq_zero_or_pos s with hs0 | hspos
  · subst hs0
    exact GradedZero.graded_zero C ξ n (by simpa using hE)
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : s ≠ 0)
    have hk : k + 1 ≤ n := by omega
    have hP' : (Phi ξ n (k : ℤ)).FG := by
      have hc : (((k + 1 : ℕ) : ℤ) - 1) = (k : ℤ) := by omega
      rwa [hc] at hP
    exact graded_succ ξ n k hk hE hP'

end Zero

end Work.SSS
