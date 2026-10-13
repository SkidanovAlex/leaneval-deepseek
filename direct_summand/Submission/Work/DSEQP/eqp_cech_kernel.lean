import Mathlib
import Submission.Work.DSEQP.EqpCechSetup
import Submission.Work.DSF1.Cech.cechComplexFunctor_map_pi
import Submission.Work.DSF1.Cech.eq_zero_of_loc_eq_zero_O

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false
-- `DSMap.cech` is a plain `def` while its affine counterpart (`Work.DSF1.Cech.cechO`) is an
-- `abbrev`.  The componentwise argument below identifies `(DSMap.cech A X f U).X n` with the
-- product of its components, which requires this definition to unfold during unification;
-- we make it locally reducible.
set_option allowUnsafeReducibility true
attribute [local reducible] DSMap.cech

open CategoryTheory AlgebraicGeometry Opposite Limits
open scoped Simplicial BigOperators

namespace Work.DSEQP

universe u

/-- The comparison map of Čech complexes
`locCech A X f U g : DSMap.cech A X f U ⟶ cechLoc A X f U g` is injective up to powers of `g`.

If every *component* of the comparison map has kernel killed by a power of `g` (hypothesis `hker`:
for every simplex `x`, a section of `Γ(X, Eobj U n x)` whose restriction to `Eobj U n x ⊓ X_g`
vanishes is killed by a power of `g`), then the same holds in every degree.

The proof is componentwise, exactly as for `Work.DSF1.Cech.eq_zero_of_loc_eq_zero_O`
(`Submission/Work/DSF1/Cech/eq_zero_of_loc_eq_zero_O.lean`), which proves precisely this argument in
the affine case `X = Spec R`, `X_g = D(g)`: use `Work.DSF1.Cech.cechComplexFunctor_map_pi` to
identify the `x`-component of `(locCech …).f n t`, apply `hker`, and clear the finitely many
denominators at once with `pi_ext` and `Finset.sup`. -/
theorem eqp_cech_kernel (A : Type u) [CommRing A] (X : AlgebraicGeometry.Scheme.{u})
    (f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of A)) {ι : Type u} [Finite ι] (U : ι → X.Opens)
    (g : A)
    (hker : ∀ (n : ℕ) (x : ((Work.DSF1.Cech.E U).obj (Opposite.op (SimplexCategory.mk n))).I),
      ∀ t : (DSMap.cechPresheaf A X f).obj (Opposite.op (Work.DSF1.Cech.Eobj U n x)),
        ((DSMap.cechPresheaf A X f).map
          (CategoryTheory.homOfLE
            (inf_le_left : Work.DSF1.Cech.Eobj U n x ⊓ Work.DSEQP.Xg A X f g ≤
              Work.DSF1.Cech.Eobj U n x)).op).hom t = 0 → ∃ k : ℕ, g ^ k • t = 0)
    (n : ℕ) (t : (DSMap.cech A X f U).X n)
    (h : (Work.DSEQP.locCech A X f U g).f n t = 0) :
    ∃ k : ℕ, g ^ k • t = 0 := by
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  let F : ((FormalCoproduct.mk ι U).cech.obj (op ⦋n⦌)).I → ModuleCat.{u} A :=
    fun y => (DSMap.cechPresheaf A X f).obj (op (Work.DSF1.Cech.Eobj U n y))
  -- For each simplex `x`, some power of `g` kills the `x`-component of `t`.
  have hstep : ∀ x, ∃ k : ℕ, g ^ k • ((Pi.π F x).hom t) = 0 := by
    intro x
    -- The `x`-component of `(locCech …).f n t` is the restriction of that component to
    -- `Eobj U n x ⊓ X_g`.
    have hA : ((Work.DSF1.Cech.etaO (DSMap.cechPresheaf A X f)
          (Xg A X f g)).app (op (Work.DSF1.Cech.Eobj U n x))).hom
        ((Pi.π F x).hom t) = 0 := by
      have hmap := Work.DSF1.Cech.cechComplexFunctor_map_pi U
        (Work.DSF1.Cech.etaO (DSMap.cechPresheaf A X f) (Xg A X f g)) n x
      have key := congrArg (fun m => ModuleCat.Hom.hom m t) hmap
      rw [ModuleCat.comp_apply, ModuleCat.comp_apply] at key
      have hl : (((cechComplexFunctor U).map
          (Work.DSF1.Cech.etaO (DSMap.cechPresheaf A X f) (Xg A X f g))).f n).hom t = 0 := h
      rw [hl, map_zero] at key
      exact key.symm
    exact hker n x _ hA
  choose K hK using hstep
  letI : Fintype ((FormalCoproduct.mk ι U).cech.obj (op ⦋n⦌)).I :=
    inferInstanceAs (Fintype (Fin (n+1) → ι))
  -- Clear all denominators at once.
  refine ⟨Finset.univ.sup K, ?_⟩
  apply Work.DSF1.Cech.pi_ext (F := F)
  intro x
  rw [map_smul, map_zero]
  have hle : K x ≤ Finset.univ.sup K := Finset.le_sup (Finset.mem_univ x)
  have hp : g ^ (Finset.univ.sup K) = g ^ (Finset.univ.sup K - K x) * g ^ (K x) := by
    rw [← pow_add, Nat.sub_add_cancel hle]
  rw [hp, mul_smul, hK x, smul_zero]

end Work.DSEQP
