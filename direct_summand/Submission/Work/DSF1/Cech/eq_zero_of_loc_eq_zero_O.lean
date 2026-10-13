import Mathlib
import Submission.Work.DSF1.Cech.CechOLocal
import Submission.Work.DSF1.Cech.CechQo
import Submission.Work.DSF1.Cech.cechComplexFunctor_map_pi
import Submission.Work.DSF1.Cech.eq_zero_of_loc_eq_zero

/-!
# Injectivity of `locO` up to powers of a single element

Let `R` be a commutative ring, `U : ι → Opens (Spec R)` a finite family of opens of
`X = Spec R` and `V` a further open.  The chain map
`locO R U V : cechO R U ⟶ cechOQ R U V` is induced componentwise by the restriction
`𝒪 (W) ⟶ 𝒪 (W ⊓ V)`.  If for every simplex `x` and every section over `Eobj U n x`
the vanishing of its restriction to `Eobj U n x ⊓ V` implies that it is killed by a
power of a fixed element `g`, then the same holds for an arbitrary element `t` of
`(cechO R U).X n` with `(locO R U V).f n t = 0`.

The proof is componentwise, exactly as in `eq_zero_of_loc_eq_zero`: in degree `n` the
complex is the (finite) product over the simplices `x` of `Γ (Eobj U n x)`, the chain
map acts componentwise by restriction, and one clears the finitely many denominators
at once with a supremum.
-/

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000
set_option linter.style.haveILetI false

open CategoryTheory AlgebraicGeometry Opposite Limits
open scoped Simplicial BigOperators

namespace Work.DSF1.Cech

universe u

theorem eq_zero_of_loc_eq_zero_O (R : Type u) [CommRing R] {ι : Type u} [Finite ι]
    (U : ι → (AlgebraicGeometry.Spec (CommRingCat.of R)).Opens)
    (V : (AlgebraicGeometry.Spec (CommRingCat.of R)).Opens) (g : R)
    (hker : ∀ (n : ℕ)
      (x : (Work.DSF1.Cech.E U).obj (Opposite.op (SimplexCategory.mk n)) |>.I)
      (t : (Work.DSF1.Cech.specPresheaf R).obj
        (Opposite.op (Work.DSF1.Cech.Eobj U n x))),
      ((Work.DSF1.Cech.specPresheaf R).map
        (homOfLE (inf_le_left : Work.DSF1.Cech.Eobj U n x ⊓ V ≤
          Work.DSF1.Cech.Eobj U n x)).op).hom t = 0 → ∃ k : ℕ, g ^ k • t = 0)
    (n : ℕ) (t : (Work.DSF1.Cech.cechO R U).X n)
    (h : (Work.DSF1.Cech.locO R U V).f n t = 0) :
    ∃ k : ℕ, g ^ k • t = 0 := by
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  let F : ((FormalCoproduct.mk ι U).cech.obj (op ⦋n⦌)).I → ModuleCat.{u} R :=
    fun y => (specPresheaf R).obj (op (Eobj U n y))
  -- For each simplex `x`, some power of `g` kills the `x`-component of `t`.
  have hstep : ∀ x, ∃ k : ℕ, g ^ k • ((Pi.π F x).hom t) = 0 := by
    intro x
    -- The `x`-component of `(locO R U V).f n t` is the restriction of that component
    -- to `Eobj U n x ⊓ V`.
    have hA : ((etaO (specPresheaf R) V).app (op (Eobj U n x))).hom
        ((Pi.π F x).hom t) = 0 := by
      have hmap := cechComplexFunctor_map_pi U (etaO (specPresheaf R) V) n x
      have key := congrArg (fun m => ModuleCat.Hom.hom m t) hmap
      rw [ModuleCat.comp_apply, ModuleCat.comp_apply] at key
      have hl : (((cechComplexFunctor U).map (etaO (specPresheaf R) V)).f n).hom t = 0 := h
      rw [hl, map_zero] at key
      exact key.symm
    exact hker n x _ hA
  choose K hK using hstep
  letI : Fintype ((FormalCoproduct.mk ι U).cech.obj (op ⦋n⦌)).I :=
    inferInstanceAs (Fintype (Fin (n+1) → ι))
  -- Clear all denominators at once.
  refine ⟨Finset.univ.sup K, ?_⟩
  apply pi_ext (F := F)
  intro x
  rw [map_smul, map_zero]
  have hle : K x ≤ Finset.univ.sup K := Finset.le_sup (Finset.mem_univ x)
  have hp : g ^ (Finset.univ.sup K) = g ^ (Finset.univ.sup K - K x) * g ^ (K x) := by
    rw [← pow_add, Nat.sub_add_cancel hle]
  rw [hp, mul_smul, hK x, smul_zero]

end Work.DSF1.Cech
