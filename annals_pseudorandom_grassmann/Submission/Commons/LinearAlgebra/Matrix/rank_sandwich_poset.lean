import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.RingTheory.Finiteness.Prod
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Commons.LinearAlgebra.finrank_map_eq

/-
# The rank sandwich identity for matrices over `ZMod 2`

This file proves `Commons.LinearAlgebra.Matrix.rank_sandwich_poset`: for matrices
`Q : Matrix (Fin n') (Fin n) (ZMod 2)`, `ι : Matrix (Fin m) (Fin m') (ZMod 2)` and
`X Y : Matrix (Fin n) (Fin m) (ZMod 2)` satisfying

* `ker Q = range X`,
* `range ι = ker X`,
* `rank Y = rank X + rank (Y - X)`

we have `rank (Q * Y * ι) = rank Y - rank X`.

The mathematical content is the following elementary (but non-obvious) linear algebra
fact.  Write `A = X.mulVecLin`, `D = (Y - X).mulVecLin`, `B = A + D = Y.mulVecLin`.  The
condition `rank B = rank A + rank D` is equivalent to

* `range A ⊓ range D = ⊥`, and
* `range D = D '' ker A`  (equivalently `ker A ⊔ ker D = ⊤`).

Given these, `Q` is injective on `range D` (its kernel is `range A`), and `ι` maps onto
`ker A`, so `range (Q * Y * ι) = Q '' range D` has dimension `rank D = rank Y - rank X`.

The general linear-algebra lemmas are proved first, then the matrix statement.
-/

namespace Commons.LinearAlgebra

open Module

/-- The product `S.prod T` of two submodules is linearly equivalent to the product
`S × T` of the submodules themselves. -/
def submoduleProdEquiv {K M M' : Type*} [Semiring K] [AddCommMonoid M] [Module K M]
    [AddCommMonoid M'] [Module K M'] (S : Submodule K M) (T : Submodule K M') :
    ↥(S.prod T) ≃ₗ[K] ↥S × ↥T where
  toFun x := (⟨x.1.1, (Submodule.mem_prod.mp x.2).1⟩, ⟨x.1.2, (Submodule.mem_prod.mp x.2).2⟩)
  invFun y := ⟨(y.1.1, y.2.1), Submodule.mem_prod.mpr ⟨y.1.2, y.2.2⟩⟩
  map_add' x y := by ext <;> rfl
  map_smul' c x := by ext <;> rfl
  left_inv x := by ext <;> rfl
  right_inv y := by ext <;> rfl

/-- **Structure of maps satisfying `rank (f + g) = rank f + rank g`.**

Let `f g : V →ₗ[K] W` be linear maps between finite-dimensional `K`-vector spaces.  If
`rank (f + g) = rank f + rank g`, then

* `range f ⊓ range g = ⊥`, and
* `range g = g '' ker f`, i.e. `g` maps the kernel of `f` onto its whole range
  (equivalently `ker f ⊔ ker g = ⊤`).

Proof.  For the first claim, `range (f + g) ≤ range f ⊔ range g` together with the
dimension formula `dim (S ⊔ T) + dim (S ⊓ T) = dim S + dim T` forces
`dim (range f ⊓ range g) = 0`.

For the second claim, consider `G := range (f.prod g) ≤ W × W`.  On one hand
`range (f + g) = G.map (fst + snd)`, so `rank (f + g) ≤ dim G`; on the other hand
`G ≤ (range f).prod (range g)` whose dimension is `rank f + rank g`.  Hence
`dim G = rank f + rank g`.  Rank–nullity for `f.prod g` then gives
`dim (ker f ⊓ ker g) = dim V - dim G`, while rank–nullity for `f` gives
`dim (ker f) = dim V - rank f`; restricting `g` to `ker f` (via `finrank_map_eq`) yields
`dim (g '' ker f) = dim (ker f) - dim (ker f ⊓ ker g) = rank g`, and `g '' ker f ≤ range g`
is an equality of submodules. -/
theorem range_inf_bot_and_map_ker_eq_range_of_finrank_range_add
    {K : Type*} [Field K] {V W : Type*} [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K V] [FiniteDimensional K W]
    (f g : V →ₗ[K] W)
    (h : Module.finrank K (LinearMap.range (f + g)) =
      Module.finrank K (LinearMap.range f) + Module.finrank K (LinearMap.range g)) :
    LinearMap.range f ⊓ LinearMap.range g = ⊥ ∧
      Submodule.map g (LinearMap.ker f) = LinearMap.range g := by
  classical
  -- `dim (range (f.prod g)) = rank f + rank g`.
  have hG_ge : Module.finrank K (LinearMap.range f) + Module.finrank K (LinearMap.range g) ≤
      Module.finrank K (LinearMap.range (f.prod g)) := by
    have hcomp : (LinearMap.fst K W W + LinearMap.snd K W W).comp (f.prod g) = f + g := by
      ext x; simp [LinearMap.prod_apply, LinearMap.add_apply]
    have hrange : LinearMap.range (f + g) =
        Submodule.map (LinearMap.fst K W W + LinearMap.snd K W W)
          (LinearMap.range (f.prod g)) := by
      rw [← hcomp, LinearMap.range_comp]
    have hmap := Submodule.finrank_map_le (LinearMap.fst K W W + LinearMap.snd K W W)
      (LinearMap.range (f.prod g))
    rw [← hrange, h] at hmap
    exact hmap
  have hG_le : Module.finrank K (LinearMap.range (f.prod g)) ≤
      Module.finrank K (LinearMap.range f) + Module.finrank K (LinearMap.range g) := by
    have hle : LinearMap.range (f.prod g) ≤
        (LinearMap.range f).prod (LinearMap.range g) := LinearMap.range_prod_le f g
    have hmono := Submodule.finrank_mono hle
    have hprod : Module.finrank K ↥((LinearMap.range f).prod (LinearMap.range g)) =
        Module.finrank K (LinearMap.range f) + Module.finrank K (LinearMap.range g) := by
      rw [LinearEquiv.finrank_eq (submoduleProdEquiv (LinearMap.range f) (LinearMap.range g)),
        Module.finrank_prod]
    rwa [hprod] at hmono
  have hG_eq : Module.finrank K (LinearMap.range (f.prod g)) =
      Module.finrank K (LinearMap.range f) + Module.finrank K (LinearMap.range g) :=
    le_antisymm hG_le hG_ge
  -- `range f ⊓ range g = ⊥`.
  have h3 : Module.finrank K ↥(LinearMap.range f ⊓ LinearMap.range g) = 0 := by
    have hsup := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.range f) (LinearMap.range g)
    have hle : Module.finrank K (LinearMap.range (f + g)) ≤
        Module.finrank K ↥(LinearMap.range f ⊔ LinearMap.range g) :=
      Submodule.finrank_mono (LinearMap.range_add_le f g)
    omega
  -- `g '' ker f = range g`.
  have h4 : Module.finrank K ↥(Submodule.map g (LinearMap.ker f)) =
      Module.finrank K (LinearMap.range g) := by
    have h1 : Module.finrank K (LinearMap.range f) + Module.finrank K ↥(LinearMap.ker f) =
        Module.finrank K V := LinearMap.finrank_range_add_finrank_ker f
    have h2 : Module.finrank K (LinearMap.range (f.prod g)) +
        Module.finrank K ↥(LinearMap.ker f ⊓ LinearMap.ker g) = Module.finrank K V := by
      rw [← LinearMap.ker_prod f g]
      exact LinearMap.finrank_range_add_finrank_ker (f.prod g)
    have h5 := Commons.LinearAlgebra.finrank_map_eq g (LinearMap.ker f)
    omega
  refine ⟨Submodule.finrank_eq_zero.mp h3, ?_⟩
  exact Submodule.eq_of_le_of_finrank_le
    (by rintro y ⟨x, hx, rfl⟩; exact ⟨x, rfl⟩) h4.ge

/-- **The rank sandwich identity for linear maps.**

Let `A B D : V →ₗ[K] W`, `q : W →ₗ[K] W'`, `i : U →ₗ[K] V` be linear maps between
finite-dimensional `K`-vector spaces, with `A + D = B`, `ker q = range A`,
`range i = ker A` and `rank B = rank A + rank D`.  Then
`rank (q ∘ B ∘ i) = rank B - rank A`.

This is a pure linear-algebra statement underlying `rank_sandwich_poset`. -/
theorem rank_mul_rank_sandwich
    {K : Type*} [Field K] {V W W' U : Type*}
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [AddCommGroup W'] [Module K W'] [AddCommGroup U] [Module K U]
    [FiniteDimensional K V] [FiniteDimensional K W]
    (A B D : V →ₗ[K] W) (q : W →ₗ[K] W') (i : U →ₗ[K] V)
    (hAD : A + D = B)
    (hkerq : LinearMap.ker q = LinearMap.range A)
    (hrangei : LinearMap.range i = LinearMap.ker A)
    (hrank : Module.finrank K (LinearMap.range B) =
      Module.finrank K (LinearMap.range A) + Module.finrank K (LinearMap.range D)) :
    Module.finrank K (LinearMap.range (q.comp (B.comp i))) =
      Module.finrank K (LinearMap.range B) - Module.finrank K (LinearMap.range A) := by
  obtain ⟨hinf, hmap⟩ :=
    range_inf_bot_and_map_ker_eq_range_of_finrank_range_add A D (by rw [hAD]; exact hrank)
  -- `B` and `D` agree on `ker A`, hence `B ∘ i = D ∘ i` since `range i = ker A`.
  have hBcomp : B.comp i = D.comp i := by
    have hAi : A.comp i = 0 := by
      ext u
      have : i u ∈ LinearMap.ker A := by
        rw [← hrangei]; exact LinearMap.mem_range_self i u
      simpa [LinearMap.mem_ker] using this
    calc B.comp i = (A + D).comp i := by rw [hAD]
      _ = A.comp i + D.comp i := by ext u; simp [LinearMap.add_apply]
      _ = D.comp i := by rw [hAi, zero_add]
  -- The range of `q ∘ B ∘ i` is `q '' range D`.
  have hr : LinearMap.range (q.comp (B.comp i)) = Submodule.map q (LinearMap.range D) := by
    rw [hBcomp, LinearMap.range_comp (D.comp i) q, LinearMap.range_comp i D, hrangei, hmap]
  -- `q` is injective on `range D`, since `range D ⊓ ker q = range D ⊓ range A = ⊥`.
  have hfin : Module.finrank K ↥(Submodule.map q (LinearMap.range D)) =
      Module.finrank K (LinearMap.range D) := by
    have hfme := Commons.LinearAlgebra.finrank_map_eq q (LinearMap.range D)
    have hker : LinearMap.range D ⊓ LinearMap.ker q = ⊥ := by
      rw [hkerq, inf_comm]; exact hinf
    rw [hker, finrank_bot, Nat.sub_zero] at hfme
    exact hfme
  rw [hr, hfin]
  omega

end Commons.LinearAlgebra

namespace Commons.LinearAlgebra.Matrix

open Module

theorem rank_sandwich_poset {m n m' n' : ℕ} (Q : Matrix (Fin n') (Fin n) (ZMod 2))
    (ι : Matrix (Fin m) (Fin m') (ZMod 2)) (X Y : Matrix (Fin n) (Fin m) (ZMod 2))
    (hQ : LinearMap.ker Q.mulVecLin = LinearMap.range X.mulVecLin)
    (hι : LinearMap.range ι.mulVecLin = LinearMap.ker X.mulVecLin)
    (hYX : Y.rank = X.rank + (Y - X).rank) :
    (Q * Y * ι).rank = Y.rank - X.rank := by
  -- `X.mulVecLin + (Y - X).mulVecLin = Y.mulVecLin`.
  have hAD : X.mulVecLin + (Y - X).mulVecLin = Y.mulVecLin := by
    rw [← Matrix.mulVecLin_add]
    congr 1
    abel
  -- `(Q * Y * ι).mulVecLin = Q.mulVecLin ∘ Y.mulVecLin ∘ ι.mulVecLin`.
  have hmul : (Q * Y * ι).mulVecLin = Q.mulVecLin.comp (Y.mulVecLin.comp ι.mulVecLin) := by
    rw [Matrix.mulVecLin_mul, Matrix.mulVecLin_mul, LinearMap.comp_assoc]
  -- Translate the rank hypothesis to the language of linear maps.
  have hrank : Module.finrank (ZMod 2) (LinearMap.range Y.mulVecLin) =
      Module.finrank (ZMod 2) (LinearMap.range X.mulVecLin) +
      Module.finrank (ZMod 2) (LinearMap.range (Y - X).mulVecLin) := by
    simpa only [Matrix.rank] using hYX
  have hmain := rank_mul_rank_sandwich X.mulVecLin Y.mulVecLin (Y - X).mulVecLin Q.mulVecLin
    ι.mulVecLin hAD hQ hι hrank
  rw [Matrix.rank, Matrix.rank, Matrix.rank, hmul]
  exact hmain

end Commons.LinearAlgebra.Matrix