import Mathlib
import Submission.Work.SSGRoute.two_two_graded_pieces
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The "two-two" detector group

The graded step at `σ = (2,2)` of the `p = 2` correction of Shafarevich's theorem is the statement
that every `δ`-anti-fixed element of the graded piece `E(2,2) = F(n)^{(2,2)}/F(n)^{(3,1)}` is a
`δ`-difference in the ambient group `Q_{(3,1)} = F(n)/F(n)^{(3,1)}`.

This file provides a *detector* for the relevant commutator subgroup: a group `TTModel ι` together
with a homomorphism `FreeGroup ι →* TTModel ι` which

* kills the third term `P₃ = F₂²[F₂,F]` of the descending `2`-central series of the free group
  `FreeGroup ι` (the group `TTModel ι` is nilpotent of class `2` of exponent `4`, and the
  subgroups `M²` and `[M,M]` are central of exponent `2`), and
* separates the basic commutators `⁅x_i, x_j⁆` (`i ≠ j`) — indeed `⁅of i, of j⁆` maps to the
  "matrix" `E_{ij} + E_{ji}`, and these are linearly independent in `(ℤ/2)^{ι×ι}`.

Consequently the commutator subgroup of `F(n)/P₃` is freely generated (over `ℤ/2`) by the images of
the basic commutators, and the linear algebra of `δ`-orbits can be carried out in coordinates.

## The group

`TTModel ι = (ι → ℤ/4) × ((ι × ι) → ℤ/2)` with multiplication

  `(a, κ) * (a', κ') = (a + a', κ + κ' + coc a a')`,   `coc a a' (i,j) = (a i : ℤ/2) * (a' j : ℤ/2)`.

The cocycle identity `coc a a' + coc (a+a') a'' = coc a' a'' + coc a (a'+a'')` holds because `coc`
is `ℤ`-bilinear, so the multiplication is associative.  The commutator of two elements depends only
on their `a`-parts: `⁅(a,κ), (a',κ')⁆ = (0, coc a a' + coc a' a)`.
-/

namespace Work.SSGRoute

open scoped commutatorElement

/-- Reduction `ℤ/4 → ℤ/2`. -/
def ttChi : ZMod 4 →+* ZMod 2 := ZMod.castHom (by norm_num : 2 ∣ 4) (ZMod 2)

theorem ttChi_apply (a : ZMod 4) : ttChi a = a.cast := by
  simp [ttChi, ZMod.castHom_apply]

/-- The "two-two" detector group. -/
structure TTModel (ι : Type*) where
  /-- the `ℤ/4`-valued part -/
  fst : ι → ZMod 4
  /-- the `ℤ/2`-valued part, indexed by ordered pairs of generators -/
  snd : ι × ι → ZMod 2

namespace TTModel

variable {ι : Type*}

/-- The cocycle `coc a a' (i,j) = (a i : ℤ/2) * (a' j : ℤ/2)`. -/
def coc (a a' : ι → ZMod 4) : ι × ι → ZMod 2 := fun p => ttChi (a p.1) * ttChi (a' p.2)

theorem coc_add_left (a a' b : ι → ZMod 4) : coc (a + a') b = coc a b + coc a' b := by
  funext p
  simp only [coc, Pi.add_apply, map_add, add_mul]

theorem coc_add_right (a b b' : ι → ZMod 4) : coc a (b + b') = coc a b + coc a b' := by
  funext p
  simp only [coc, Pi.add_apply, map_add, mul_add]

theorem coc_zero_left (b : ι → ZMod 4) : coc 0 b = 0 := by
  funext p; simp [coc]

theorem coc_zero_right (a : ι → ZMod 4) : coc a 0 = 0 := by
  funext p; simp [coc]

theorem coc_neg (a b : ι → ZMod 4) : coc (-a) b = -coc a b := by
  funext p; simp only [coc, Pi.neg_apply, map_neg]; ring

theorem coc_neg_right (a b : ι → ZMod 4) : coc a (-b) = -coc a b := by
  funext p; simp only [coc, Pi.neg_apply, map_neg]; ring

instance : Mul (TTModel ι) where
  mul x y := ⟨x.fst + y.fst, x.snd + y.snd + coc x.fst y.fst⟩

instance : One (TTModel ι) := ⟨⟨0, 0⟩⟩

instance : Inv (TTModel ι) where
  inv x := ⟨-x.fst, -x.snd - coc x.fst (-x.fst)⟩

@[simp] theorem fst_mul (x y : TTModel ι) : (x * y).fst = x.fst + y.fst := rfl
@[simp] theorem snd_mul (x y : TTModel ι) : (x * y).snd = x.snd + y.snd + coc x.fst y.fst := rfl
@[simp] theorem fst_one : (1 : TTModel ι).fst = 0 := rfl
@[simp] theorem snd_one : (1 : TTModel ι).snd = 0 := rfl
@[simp] theorem fst_inv (x : TTModel ι) : x⁻¹.fst = -x.fst := rfl
@[simp] theorem snd_inv (x : TTModel ι) : x⁻¹.snd = -x.snd - coc x.fst (-x.fst) := rfl

/-- Extensionality for the detector group. -/
theorem ext' {x y : TTModel ι} (h1 : ∀ i, x.fst i = y.fst i) (h2 : ∀ p, x.snd p = y.snd p) :
    x = y := by
  obtain ⟨a, k⟩ := x
  obtain ⟨a', k'⟩ := y
  simp only [mk.injEq]
  exact ⟨funext h1, funext h2⟩

theorem fst_mul_apply (x y : TTModel ι) (i : ι) : (x * y).fst i = x.fst i + y.fst i := rfl
theorem snd_mul_apply (x y : TTModel ι) (i j : ι) :
    (x * y).snd (i, j) = x.snd (i, j) + y.snd (i, j) + ttChi (x.fst i) * ttChi (y.fst j) := rfl

instance : Group (TTModel ι) := Group.ofLeftAxioms
  (by
    intro a b c
    refine TTModel.ext' ?_ ?_
    · intro i; simp only [fst_mul, Pi.add_apply]; abel
    · rintro ⟨i, j⟩
      simp only [snd_mul, coc, fst_mul, Pi.add_apply, map_add]
      ring)
  (by
    intro a
    refine TTModel.ext' ?_ ?_
    · intro i; simp
    · rintro ⟨i, j⟩
      simp [coc])
  (by
    intro a
    refine TTModel.ext' ?_ ?_
    · intro i; simp
    · rintro ⟨i, j⟩
      simp only [snd_mul, snd_inv, fst_inv, snd_one, coc, Pi.add_apply, Pi.sub_apply,
        Pi.zero_apply, Pi.neg_apply, map_neg]
      ring)

/-- The `i`-th generalised generator `x_i`, with `a = e_i` and vanishing `κ`. -/
def of [DecidableEq ι] (i : ι) : TTModel ι := ⟨Pi.single i 1, 0⟩

@[simp] theorem of_fst [DecidableEq ι] (i : ι) : (of i).fst = Pi.single i 1 := rfl
@[simp] theorem of_snd [DecidableEq ι] (i : ι) : (of i).snd = 0 := rfl

/-- The "matrix" `E_{ij} + E_{ji}`, the expected value of `⁅of i, of j⁆`. -/
def pairElt [DecidableEq ι] (i j : ι) : TTModel ι := ⟨0, Pi.single (i, j) 1 + Pi.single (j, i) 1⟩

@[simp] theorem pairElt_fst [DecidableEq ι] (i j : ι) : (pairElt i j).fst = 0 := rfl
@[simp] theorem pairElt_snd [DecidableEq ι] (i j : ι) :
    (pairElt i j).snd = Pi.single (i, j) 1 + Pi.single (j, i) 1 := rfl

/-- The automorphism of `TTModel ι` induced by a permutation of `ι`. -/
def permAut (σ : ι ≃ ι) : TTModel ι ≃* TTModel ι where
  toFun x := ⟨fun i => x.fst (σ.symm i), fun p => x.snd (σ.symm p.1, σ.symm p.2)⟩
  invFun x := ⟨fun i => x.fst (σ i), fun p => x.snd (σ p.1, σ p.2)⟩
  left_inv x := by
    refine TTModel.ext' ?_ ?_ <;> intro y <;> simp
  right_inv x := by
    refine TTModel.ext' ?_ ?_ <;> intro y <;> simp
  map_mul' x y := by
    refine TTModel.ext' ?_ ?_
    · intro i; simp
    · rintro ⟨i, j⟩
      simp only [snd_mul, coc, fst_mul, Pi.add_apply]

end TTModel

/-- The **detector**: the homomorphism `FreeGroup ι →* TTModel ι` sending the generator `x_i`
to the generalised generator `TTModel.of i`.  It kills the third term `P₃` of the descending
`2`-central series of `FreeGroup ι` (because `TTModel ι` is nilpotent of class `2` of exponent
`4` with `M²` and `[M,M]` central of exponent `2`) and it separates the basic commutators. -/
noncomputable def ttDetector (ι : Type*) [DecidableEq ι] : FreeGroup ι →* TTModel ι :=
  FreeGroup.lift TTModel.of

theorem ttDetector_of {ι : Type*} [DecidableEq ι] (i : ι) :
    ttDetector ι (FreeGroup.of i) = TTModel.of i :=
  FreeGroup.lift_apply_of

end Work.SSGRoute
