import Mathlib
import Submission.Work.SSGRoute.gradedStep_diagonal
import Submission.Work.SSGRoute.two_torsion_assembly
import Submission.Work.SSGRoute.lcs_inter_pCentralSeries_eq
import Submission.Work.SSGRoute.tt_fixed_decomp
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The `(3,3)` diagonal graded step for `G = ℤ/2`: the linear-algebra base

Setup for `Work.SSGRoute.gradedStep_diagonal_zmodTwo_three`.

The graded piece `E(3,3)` of the refined `2`-central filtration of `F(n)` at `G = Multiplicative
(ZMod 2)` is a free module over `𝔽₂[C₂]` (the involution being induced by the fixed-point-free
permutation `(i,g) ↦ (i, δ g)` of the free generators).  The proof routes through the left-nested
bracket map `Λ` on the degree-`3` part `T` of the free associative algebra: `T` is a free
`𝔽₂[C₂]`-module (the word basis is permuted without fixed points), and `Λ` is an equivariant
idempotent retraction onto the degree-`3` Lie part.

* `TT n = (Fin 3 → XX n) → ZMod 2` is the degree-`3` part of `FreeAssoc (XX n)` reduced mod `2`,
  with word basis `w ↦ wordEl (List.ofFn w)`;
* `dTT n` is the induced involution; `dTT_decomp` shows every fixed element is a `(1+dTT)`-value;
* `LamT n` is `Λ` (the transpose of `w ↦ lnMon (List.ofFn w)`);
* `thetaFun n` is the "product of left-nested commutators" map `TT n → Q_{(4,1)}`.
-/

open scoped commutatorElement
open Work.CohomologicalShrinking

namespace Work.SSGRoute
namespace ZZ3

noncomputable section

open Classical

abbrev Gm : Type := Multiplicative (ZMod 2)

abbrev dm : Gm := Multiplicative.ofAdd (1 : ZMod 2)

abbrev XX (n : ℕ) : Type := Fin n × Gm

abbrev sg (n : ℕ) : XX n ≃ XX n := Work.Shrinking.freeOperatorGenPerm n dm

theorem dm_mul_dm : dm * dm = 1 := by
  show Multiplicative.ofAdd (1 : ZMod 2) * Multiplicative.ofAdd (1 : ZMod 2) = 1
  rw [← ofAdd_add, show (1 : ZMod 2) + 1 = 0 from by decide, ofAdd_zero]

theorem sg_sg (n : ℕ) (x : XX n) : sg n (sg n x) = x := by
  rcases x with ⟨i, g⟩
  change ((i, dm * (dm * g)) : Fin n × Gm) = (i, g)
  rw [← mul_assoc, dm_mul_dm, one_mul]

theorem sg_ne (n : ℕ) (x : XX n) : sg n x ≠ x := by
  rcases x with ⟨i, g⟩
  intro h
  have h2 : dm * g = g := by
    have := congrArg Prod.snd h
    simpa [sg, Work.Shrinking.freeOperatorGenPerm] using this
  exact (by decide : dm ≠ 1) (mul_right_cancel (by rw [h2, one_mul]))

/-! ## The module `TT` and its involution -/

abbrev TT (n : ℕ) : Type := (Fin 3 → XX n) → ZMod 2

def dTT (n : ℕ) (f : TT n) : TT n := fun w => f (fun i => sg n (w i))

theorem dTT_apply (n : ℕ) (f : TT n) (w : Fin 3 → XX n) :
    dTT n f w = f (fun i => sg n (w i)) := rfl

theorem dTT_dTT (n : ℕ) (f : TT n) : dTT n (dTT n f) = f := by
  funext w
  show f (fun i => sg n (sg n (w i))) = f w
  rw [show (fun i => sg n (sg n (w i))) = w from by
    funext i; exact sg_sg n (w i)]

def sigP (n : ℕ) : (Fin 3 → XX n) → (Fin 3 → XX n) := fun w i => sg n (w i)

theorem sigP_invol (n : ℕ) (w : Fin 3 → XX n) : sigP n (sigP n w) = w := by
  funext i
  exact sg_sg n (w i)

theorem sigP_fixed_free (n : ℕ) (w : Fin 3 → XX n) : sigP n w ≠ w := by
  intro h
  have h0 := congrFun h (0 : Fin 3)
  exact sg_ne n (w 0) h0

theorem dTT_eq_sigP (n : ℕ) (f : TT n) : dTT n f = fun w => f (sigP n w) := rfl

/-- **Every fixed point of the involution is a `(1+δ)`-value** (the `𝔽₂[C₂]`-freeness of `TT n`,
in the form used below): the word basis is permuted without fixed points, so a fixed coefficient
function is a coboundary. -/
theorem dTT_decomp (n : ℕ) (f : TT n) (hf : dTT n f = f) : ∃ g : TT n, f = g + dTT n g := by
  classical
  haveI hdec : DecidableRel (α := Fin 3 → XX n) WellOrderingRel := fun _ _ => Classical.propDecidable _
  letI : LinearOrder (Fin 3 → XX n) := linearOrderOfSTO WellOrderingRel
  have hfix : ∀ w, f (sigP n w) = f w := by
    intro w
    have h := congrFun hf w
    rw [dTT_eq_sigP] at h
    exact h
  obtain ⟨lam, s, hs, hdec'⟩ := tt_fixed_decomp (sigP n) (sigP_invol n) f hfix
  refine ⟨lam, ?_⟩
  funext w
  have hsw : s w = 0 := hs w (sigP_fixed_free n w)
  have h := hdec' w
  rw [hsw, add_zero] at h
  rw [h]
  rfl

/-! ## The left-nested bracket map `Λ` -/

def sw01 : Fin 3 → Fin 3 := ![1, 0, 2]

def swcyc : Fin 3 → Fin 3 := ![1, 2, 0]

def sw02 : Fin 3 → Fin 3 := ![2, 1, 0]

/-- `Λ` on the degree-`3` part mod `2`: the transpose of `w ↦ lnMon w`, i.e.
`(Λ g)(x,y,z) = g(x,y,z) + g(y,x,z) + g(y,z,x) + g(z,y,x)`. -/
def LamT (n : ℕ) (g : TT n) : TT n :=
  fun w => g w + g (w ∘ sw01) + g (w ∘ swcyc) + g (w ∘ sw02)

theorem LamT_apply (n : ℕ) (g : TT n) (w : Fin 3 → XX n) :
    LamT n g w = g w + g (w ∘ sw01) + g (w ∘ swcyc) + g (w ∘ sw02) := rfl

/-! ## The commutator class map `θ` -/

/-- The index type of `TT n`. -/
abbrev Idx (n : ℕ) : Type := Fin 3 → XX n

/-- The left-nested commutator `[[x,y],z]` of a triple of generators. -/
def lcF (n : ℕ) (w : Idx n) : FreeGroup (XX n) :=
  Work.SSGRoute.prop5.lc (List.ofFn w)

/-- The class of a group element in `Q_{(4,1)} = F(n)^{(4,1)}`. -/
def mkQ (n : ℕ) (y : FreeGroup (XX n)) :
    flowQuotient 2 Gm n (tauSucc 3 3).1 (tauSucc 3 3).2 :=
  QuotientGroup.mk'
    ((flowTerm 2 Gm n (tauSucc 3 3).1 (tauSucc 3 3).2).subgroupOf
      (⊤ : Subgroup (FreeGroup (XX n)))) ⟨y, Subgroup.mem_top y⟩

/-- The "product of left-nested commutators" map `TT n → Q_{(4,1)}`.  (The index type is finite,
so this is a finite product; no commutativity of the target is used.) -/
def thetaFun (n : ℕ) (g : TT n) :
    flowQuotient 2 Gm n (tauSucc 3 3).1 (tauSucc 3 3).2 :=
  letI : DecidableRel (α := Idx n) WellOrderingRel := Classical.decRel _
  letI : LinearOrder (Idx n) := linearOrderOfSTO WellOrderingRel
  (((Finset.univ : Finset (Idx n)).sort (· ≤ ·)).map
    (fun w => (mkQ n (lcF n w)) ^ ((g w).val))).prod

end

end ZZ3
end Work.SSGRoute
