import Mathlib
import Submission.Work.ORHughesFree.Epic
import Submission.Work.ORHughesFree.StarRegular
import Submission.Work.ORHughesFree.StarRegular.vonNeumannRegularRing_matrix
import Submission.Work.ORHughesFree.Epic.BalancedTensor


set_option autoImplicit false
set_option maxHeartbeats 1000000

universe u

namespace Work.Section3.UniverseStenstrom

open Work.ORHughesFree
open Work.ORHughesFree.Epic

/-!
# Epimorphisms out of a von Neumann regular ring are surjective

The classical theorem (Stenström, *Rings of quotients*, XI.1.4; Gardner, *Epimorphisms of
regular rings*) that an epic ring homomorphism `f : R →+* S` with `R` von Neumann regular is
surjective.

The proof has three ingredients.

* **Silver's step.**  If `f` is epic and `m` is an element of an `(S,S)`-bimodule fixed by the
  image of `R`, then `m` is fixed by all of `S`.  This is proved with the trivial extension
  `S ⋉ M` of `M` (Mathlib's `TrivSqZeroExt`): the two ring homomorphisms
  `s ↦ (s, 0)` and `s ↦ (s, s • m - m • s)` agree on `f(R)`, hence on all of `S` by epicity.
* **The Mazet presentation** (Isbell–Silver–Mazet): every `d : S` can be written as
  `d = X · f(P) · Y` with `X` a row over `S`, `P` a square matrix over `R`, `Y` a column over
  `S`, and `X · f(P)`, `f(P) · Y` matrices over `f(R)`.  This is recorded in the module
  `Submission.Work.ORHughesFree.Section3.mazetPresentation`, whose hypothesis is exactly Silver's
  conclusion applied to `m = 1 ⊗ 1` in the `R`-balanced tensor product `S ⊗[R] S`.
* **The von Neumann regular step.**  Since `Mat n R` is von Neumann regular, `P = P T P` for
  some `T`, so `d = (X f(P)) · f(T) · (f(P) Y)`, a `1 × 1` matrix over `f(R)`; hence `d = f r`.
-/

/-- **Silver's step.**  Let `M` be an `(S,S)`-bimodule and `m ∈ M` an element fixed by the image
of `f : R →+* S` (`f r • m = m • f r`).  If `f` is epic then `d • m = m • d` for every `d : S`.

The proof uses the trivial extension `S ⋉ M`: `s ↦ (s, 0)` and `s ↦ (s, s • m - m • s)` are ring
homomorphisms `S → TrivSqZeroExt S M` which agree on `f(R)`, hence are equal by epicity. -/
theorem mul_eq_of_isEpic {R S M : Type u} [Ring R] [Ring S] [AddCommGroup M]
    [Module S M] [Module Sᵐᵒᵖ M] [SMulCommClass S Sᵐᵒᵖ M]
    (f : R →+* S) (hf : IsEpic f) (m : M)
    (hm : ∀ r : R, f r • m = MulOpposite.op (f r) • m) (d : S) :
    d • m = MulOpposite.op d • m := by
  let δ : S → M := fun s => s • m - MulOpposite.op s • m
  have hδ : ∀ s s' : S, δ (s * s') = s • δ s' + MulOpposite.op s' • δ s := by
    intro s s'
    show (s * s') • m - MulOpposite.op (s * s') • m
      = s • (s' • m - MulOpposite.op s' • m)
        + MulOpposite.op s' • (s • m - MulOpposite.op s • m)
    rw [smul_sub, smul_sub, MulOpposite.op_mul]
    simp only [mul_smul, smul_comm s (MulOpposite.op s') m]
    abel
  have hδone : δ 1 = 0 := by
    show (1 : S) • m - MulOpposite.op (1 : S) • m = 0
    rw [one_smul, MulOpposite.op_one, one_smul, sub_self]
  have hδadd : ∀ s s' : S, δ (s + s') = δ s + δ s' := by
    intro s s'
    show (s + s') • m - MulOpposite.op (s + s') • m
      = (s • m - MulOpposite.op s • m) + (s' • m - MulOpposite.op s' • m)
    rw [add_smul, MulOpposite.op_add, add_smul]
    abel
  have hδzero : δ 0 = 0 := by
    show (0 : S) • m - MulOpposite.op (0 : S) • m = 0
    rw [zero_smul, MulOpposite.op_zero, zero_smul, sub_self]
  let F : S → TrivSqZeroExt S M := fun s => (s, δ s)
  let h : S →+* TrivSqZeroExt S M :=
  { toFun := F
    map_one' := by
      show F 1 = 1
      rw [show F 1 = ((1 : S), δ 1) from rfl, hδone]
      rfl
    map_mul' := fun s s' => by
      show F (s * s') = F s * F s'
      apply TrivSqZeroExt.ext
      · rw [TrivSqZeroExt.fst_mul]; rfl
      · rw [TrivSqZeroExt.snd_mul]; exact hδ s s'
    map_zero' := by
      show F 0 = 0
      rw [show F 0 = ((0 : S), δ 0) from rfl, hδzero]
      rfl
    map_add' := fun s s' => by
      show F (s + s') = F s + F s'
      apply TrivSqZeroExt.ext
      · rw [TrivSqZeroExt.fst_add]; rfl
      · rw [TrivSqZeroExt.snd_add]; exact hδadd s s' }
  have hgf : (TrivSqZeroExt.inlHom S M).comp f = h.comp f := by
    apply RingHom.ext; intro r
    apply TrivSqZeroExt.ext
    · rw [RingHom.comp_apply, RingHom.comp_apply, TrivSqZeroExt.inlHom_apply,
        TrivSqZeroExt.fst_inl]
      rw [show (h (f r)).fst = f r from rfl]
    · rw [RingHom.comp_apply, RingHom.comp_apply, TrivSqZeroExt.inlHom_apply,
        TrivSqZeroExt.snd_inl]
      rw [show (h (f r)).snd = δ (f r) from rfl]
      have hfr : δ (f r) = 0 := by
        show f r • m - MulOpposite.op (f r) • m = 0
        rw [hm r]; simp
      rw [hfr]
  have key := hf (TrivSqZeroExt.inlHom S M) h hgf
  have h2 : ((TrivSqZeroExt.inlHom S M) d).snd = (h d).snd :=
    congrArg (fun φ : S →+* TrivSqZeroExt S M => (φ d).snd) key
  rw [TrivSqZeroExt.inlHom_apply, TrivSqZeroExt.snd_inl,
    show (h d).snd = δ d from rfl] at h2
  exact eq_of_sub_eq_zero (by simpa [δ] using h2.symm)

/-- Silver's step applied inside the `R`-balanced tensor product `S ⊗[R] S` with `m = 1 ⊗ 1`,
which is fixed by the image of `R`.  This is the hypothesis of the Mazet presentation. -/
theorem tmul_eq_of_isEpic {R S : Type u} [Ring R] [Ring S] (f : R →+* S)
    (hf : IsEpic f) (d : S) :
    BalancedTensor.tmul f d 1 = BalancedTensor.tmul f 1 d := by
  letI : SMul S (BalancedTensor f) := ⟨fun s m => BalancedTensor.smulLeft f s m⟩
  letI : Module S (BalancedTensor f) := {
    smul := fun s m => BalancedTensor.smulLeft f s m
    one_smul := fun m => by
      show BalancedTensor.smulLeft f 1 m = m
      rw [BalancedTensor.smulLeft_one]; rfl
    mul_smul := fun s t m => by
      show BalancedTensor.smulLeft f (s * t) m
        = BalancedTensor.smulLeft f s (BalancedTensor.smulLeft f t m)
      rw [BalancedTensor.smulLeft_mul]; rfl
    smul_zero := fun s => map_zero _
    smul_add := fun s x y => map_add _ x y
    add_smul := fun s t m => by
      show BalancedTensor.smulLeft f (s + t) m
        = BalancedTensor.smulLeft f s m + BalancedTensor.smulLeft f t m
      rw [BalancedTensor.smulLeft_add]; rfl
    zero_smul := fun m => by
      show BalancedTensor.smulLeft f 0 m = 0
      have h0 : BalancedTensor.smulLeft f 0
          = (0 : BalancedTensor f →+ BalancedTensor f) := by
        have h : BalancedTensor.smulLeft f 0
            = BalancedTensor.smulLeft f 0 + BalancedTensor.smulLeft f 0 := by
          rw [← BalancedTensor.smulLeft_add, add_zero]
        exact (add_left_cancel (show BalancedTensor.smulLeft f 0 + 0
          = BalancedTensor.smulLeft f 0 + BalancedTensor.smulLeft f 0 by
            rw [add_zero]; exact h)).symm
      rw [h0]; rfl }
  letI : SMul Sᵐᵒᵖ (BalancedTensor f) :=
    ⟨fun s m => BalancedTensor.smulRight f (MulOpposite.unop s) m⟩
  letI : Module Sᵐᵒᵖ (BalancedTensor f) := {
    smul := fun s m => BalancedTensor.smulRight f (MulOpposite.unop s) m
    one_smul := fun m => by
      show BalancedTensor.smulRight f (MulOpposite.unop (1 : Sᵐᵒᵖ)) m = m
      rw [MulOpposite.unop_one, BalancedTensor.smulRight_one]; rfl
    mul_smul := fun s t m => by
      show BalancedTensor.smulRight f (MulOpposite.unop (s * t)) m
        = BalancedTensor.smulRight f (MulOpposite.unop s)
            (BalancedTensor.smulRight f (MulOpposite.unop t) m)
      rw [MulOpposite.unop_mul, BalancedTensor.smulRight_mul]; rfl
    smul_zero := fun s => map_zero _
    smul_add := fun s x y => map_add _ x y
    add_smul := fun s t m => by
      show BalancedTensor.smulRight f (MulOpposite.unop (s + t)) m
        = BalancedTensor.smulRight f (MulOpposite.unop s) m
          + BalancedTensor.smulRight f (MulOpposite.unop t) m
      rw [MulOpposite.unop_add, BalancedTensor.smulRight_add]; rfl
    zero_smul := fun m => by
      show BalancedTensor.smulRight f (MulOpposite.unop (0 : Sᵐᵒᵖ)) m = 0
      have h0 : BalancedTensor.smulRight f 0
          = (0 : BalancedTensor f →+ BalancedTensor f) := by
        have h : BalancedTensor.smulRight f 0
            = BalancedTensor.smulRight f 0 + BalancedTensor.smulRight f 0 := by
          rw [← BalancedTensor.smulRight_add, add_zero]
        exact (add_left_cancel (show BalancedTensor.smulRight f 0 + 0
          = BalancedTensor.smulRight f 0 + BalancedTensor.smulRight f 0 by
            rw [add_zero]; exact h)).symm
      rw [MulOpposite.unop_zero, h0]; rfl }
  letI : SMulCommClass S Sᵐᵒᵖ (BalancedTensor f) := {
    smul_comm := fun s s' m =>
      congrArg (fun φ : BalancedTensor f →+ BalancedTensor f => φ m)
        (BalancedTensor.smulLeft_smulRight f s (MulOpposite.unop s')) }
  have hm : ∀ r : R, f r • (BalancedTensor.tmul f 1 1)
      = MulOpposite.op (f r) • (BalancedTensor.tmul f 1 1) := fun r =>
    BalancedTensor.smulLeft_eq_smulRight_tmul_one_one f r
  have h := mul_eq_of_isEpic (M := BalancedTensor f) f hf (BalancedTensor.tmul f 1 1) hm d
  have h1 : BalancedTensor.tmul f d 1 = d • BalancedTensor.tmul f 1 1 := by
    show BalancedTensor.tmul f d 1 = BalancedTensor.smulLeft f d (BalancedTensor.tmul f 1 1)
    rw [BalancedTensor.smulLeft_tmul, mul_one]
  have h2 : MulOpposite.op d • BalancedTensor.tmul f 1 1 = BalancedTensor.tmul f 1 d := by
    show BalancedTensor.smulRight f d (BalancedTensor.tmul f 1 1) = BalancedTensor.tmul f 1 d
    rw [BalancedTensor.smulRight_tmul, one_mul]
  rw [h1, h, h2]

end Work.Section3.UniverseStenstrom
