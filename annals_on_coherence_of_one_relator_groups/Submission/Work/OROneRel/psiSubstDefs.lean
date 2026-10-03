/-
Copyright: subproject `OROneRel` -- one-relator combinatorics (node N2).

# The substitutions used in the "all exponent sums nonzero" case of the Freiheitssatz

This file contains definitions only (no `sorry`), so that lemma requests may import it without
depending on any unproved statement.

* `powSubst t p : F(T) →* F(T)` is the **Nielsen substitution** `t ↦ t ^ p`, all other generators
  fixed.  For `p ≠ 0` it is injective (the set `{t^p} ∪ {s : s ≠ t}` is another free basis of
  `F(T)`), see `Submission.Work.OROneRel.powSubst_injective`.

* `Psi r t x : F(α) →* F(α)` is the substitution of Magnus/Putman used to reduce the case in which
  no letter of the relator has vanishing exponent sum to the case in which one does: with
  `p = σ_x(r)` and `q = σ_t(r)` (which are both nonzero in that situation) it sends
  `t ↦ t^p`, `x ↦ x * t^(-q)` and fixes every other generator.  It has the effect of making the
  exponent sum in `t` vanish: `σ_t (Psi r t x r) = 1`.

Both substitutions are injective (the images of the generators are again a free basis of the free
group they generate), which is what makes the reduction work.
-/
import Mathlib
import Submission.Work.OROneRel.Interface
import Submission.Work.OROneRel.FreiheitssatzDefs
import Submission.Work.OROneRel.exists_cyclicallyReduced_conjugate

namespace Work.OROneRel

universe u

variable {α : Type u}

/-- The Nielsen substitution `t ↦ t ^ p` of the free group `F(T)`, all other generators fixed. -/
noncomputable def powSubstFun (t : α) (p : ℤ) : α → FreeGroup α := by
  classical
  exact fun a => if a = t then FreeGroup.of t ^ p else FreeGroup.of a

/-- The Nielsen substitution `t ↦ t ^ p` as a homomorphism `F(α) →* F(α)`. -/
noncomputable def powSubst (t : α) (p : ℤ) : FreeGroup α →* FreeGroup α :=
  FreeGroup.lift (powSubstFun t p)

/-- The Magnus/Putman substitution: `t ↦ t^(σ_x r)`, `x ↦ x * t^(-σ_t r)`, all other generators
fixed.  It arranges for the exponent sum in `t` of the substituted relator to vanish. -/
noncomputable def PsiFun (r : FreeGroup α) (t x : α) : α → FreeGroup α := by
  classical
  exact fun s =>
    if s = t then FreeGroup.of t ^ (sigma x r).toAdd
    else if s = x then FreeGroup.of x * FreeGroup.of t ^ (-(sigma t r).toAdd)
    else FreeGroup.of s

/-- The Magnus/Putman substitution as a homomorphism `F(α) →* F(α)`. -/
noncomputable def Psi (r : FreeGroup α) (t x : α) : FreeGroup α →* FreeGroup α :=
  FreeGroup.lift (PsiFun r t x)

@[simp] theorem powSubst_of_eq {t : α} (p : ℤ) : powSubst t p (FreeGroup.of t) = FreeGroup.of t ^ p := by
  classical
  rw [powSubst, FreeGroup.lift_apply_of]
  simp [powSubstFun]

theorem powSubst_of_ne {t a : α} (h : a ≠ t) (p : ℤ) :
    powSubst t p (FreeGroup.of a) = FreeGroup.of a := by
  classical
  rw [powSubst, FreeGroup.lift_apply_of]
  simp [powSubstFun, h]

@[simp] theorem Psi_of_eq {r : FreeGroup α} {t x : α} (s : α) (h : s = t) :
    Psi r t x (FreeGroup.of s) = FreeGroup.of t ^ (sigma x r).toAdd := by
  classical
  subst h
  rw [Psi, FreeGroup.lift_apply_of]
  simp [PsiFun]

theorem Psi_of_eq_t {r : FreeGroup α} (t x : α) :
    Psi r t x (FreeGroup.of t) = FreeGroup.of t ^ (sigma x r).toAdd := by
  classical
  rw [Psi, FreeGroup.lift_apply_of]
  simp [PsiFun]

theorem Psi_of_eq_x {r : FreeGroup α} {t x : α} (htx : x ≠ t) :
    Psi r t x (FreeGroup.of x) = FreeGroup.of x * FreeGroup.of t ^ (-(sigma t r).toAdd) := by
  classical
  rw [Psi, FreeGroup.lift_apply_of]
  simp [PsiFun, htx]

theorem Psi_of_ne {r : FreeGroup α} {t x s : α} (hst : s ≠ t) (hsx : s ≠ x) :
    Psi r t x (FreeGroup.of s) = FreeGroup.of s := by
  classical
  rw [Psi, FreeGroup.lift_apply_of]
  simp [PsiFun, hst, hsx]

/-- The number of letters of the reduced word of `w` that are different from `t`.  This is the
length of the Magnus rewriting of `w` with respect to `t`. -/
noncomputable def nonTLetters (t : α) (w : FreeGroup α) : ℕ := by
  classical
  exact (FreeGroup.toWord w).countP (fun p => p.1 ≠ t)

/-- The Magnus rewriting of a relator `r` with respect to the letter `t`, as an element of the free
group on the decorated letters `({a // a ≠ t} × ℤ)`.  Its length is the number of letters of `r`
different from `t`, and its `zeta`-image is `r` up to a power of `t`
(`mk_eq_expand_rewriteAux`, `zeta_mk_eq_expand`). -/
noncomputable def magnusRelator (t : α) (r : FreeGroup α) : FreeGroup ({a : α // a ≠ t} × ℤ) := by
  classical
  exact FreeGroup.mk (rewrite t r.toWord)

/-- The Magnus rewriting (with respect to `y`) of the cyclic reduction of the substituted relator
`Psi r y x r` of Case 2 of the Freiheitssatz.  This is the relator of the exponent-sum-zero case
that Case 2 is reduced to. -/
noncomputable def substRewRel (r : FreeGroup α) (y x : α) : FreeGroup ({a : α // a ≠ y} × ℤ) := by
  classical
  exact FreeGroup.mk (rewrite y (cyclicReduction (Psi r y x r)).toWord)

end Work.OROneRel
