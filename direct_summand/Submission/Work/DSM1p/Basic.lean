import Submission.Work.DSMap.Mix

/-!
# DSM1p — the mixed-characteristic perfectoid cover (Bhatt, Prop. 4.2)

This is the base module of the subproject `DSM1p`, whose deliverable is

`DSMap.Mix.area_M1'_proved`

with the same type as the frozen interface `DSMap.Mix.area_M1'` of
`Submission/Work/DSMap/Mix.lean` (node `M1'` of
`sources/dsmap/direct_summand_mix_design.md`):

> a complete regular local ring `A` of mixed characteristic `(0, p)` with algebraically
> closed residue field admits a *faithfully flat* `A`-algebra `B` which is perfectoid in the
> sense of `DSMap.PerfectoidData` (`ϖ ^ p = p * unit` and a compatible system of `p`-power
> roots; no almost purity is needed).

## The mathematics

Bhatt (arXiv:1608.08882, §4, Prop. 4.2 and its proof) produces `B` as the `p`-adic completion
of the ring obtained from `A` by adjoining `p`-power roots of a *system of parameters* of the
maximal ideal (`p` itself may be adjoined as well; then `ϖ := (p.unit)^{1/p}`).  Formally
flatness is then a consequence of Bhatt's criterion (l.c., Prop. 4.1): for Noetherian `A`, if
`A` and `B` are `π`-torsion-free and `π`-adically complete and `A/π → B/π` is flat, then
`A → B` is flat; faithfulness is detected modulo the maximal ideal.

Two features make this construction formalisable without any theory of power series rings:
* adjoining a `p`-th root of a *single* element `a` is a *free* extension of rank `p`
  (`AdjoinRoot (X ^ p - C a)` has the basis `1, x, …, x^{p-1}`), so the whole tower and its
  filtered colimit are flat by construction — one never needs to know what `A/p` looks like;
* consequently `A/p → B/p` is flat for *every* choice of generators, and only the
  *perfectness* of `B/p`, the *pseudo-uniformizer* `ϖ` and the *Frobenius-kernel* condition
  depend on the choice of the generator system.

## Contents

* `Work.DSM1p.RootExt` — `R[x]/(x^p - a)`, the `p`-th root extension of a single element, with
  its module structure (free of rank `p` for `0 < p`);
* `Work.DSM1p.RootTower` — the tower `R[x_m]/(x_m^{p^m} - a)` with transition `x_m ↦ x_{m+1}^p`;
* `Work.DSM1p.RootClosure` — the filtered colimit `R[a^{1/p^∞}]` of the tower, together with
  the compatible system of `p`-power roots `varpi`;
* `Work.DSM1p.PerfectoidAPI` — the API of `DSMap.PerfectoidData`;
* `Work.DSM1p.Criterion` — Bhatt's flatness criterion (Prop. 4.1);
* `Work.DSM1p.Presentation` / `Work.DSM1p.Main` — the assembly of `area_M1'`.
-/

namespace Work.DSM1p

universe u

open Polynomial

/-! ## The `p`-th root extension of a single element -/

/-- **The `p`-th root extension** of `R` in `a`: `R[x]/(x ^ p - a)`. -/
noncomputable abbrev RootExt (R : Type u) [CommRing R] (p : ℕ) (a : R) : Type u :=
  AdjoinRoot (X ^ p - C a)

/-- The adjoined `p`-th root of `a`. -/
noncomputable abbrev RootExt.root (R : Type u) [CommRing R] (p : ℕ) (a : R) : RootExt R p a :=
  AdjoinRoot.root (X ^ p - C a)

/-- `X ^ p - C a` is monic (for `p ≠ 0`), so that the extension is free. -/
theorem RootExt.monic {R : Type u} [CommRing R] (p : ℕ) (a : R) (hp : p ≠ 0) :
    (X ^ p - C a : R[X]).Monic :=
  monic_X_pow_sub_C a hp

/-- **The defining relation** of the root extension: `root ^ p = a`. -/
theorem RootExt.root_pow (R : Type u) [CommRing R] (p : ℕ) (a : R) :
    RootExt.root R p a ^ p = AdjoinRoot.of _ a := by
  have h := AdjoinRoot.eval₂_root (X ^ p - C a : R[X])
  simp only [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
    Polynomial.eval₂_C] at h
  exact sub_eq_zero.mp h

/-- The root extension is a free `R`-module. -/
theorem RootExt.free (R : Type u) [CommRing R] (p : ℕ) (a : R) (hp : p ≠ 0) :
    Module.Free R (RootExt R p a) :=
  (RootExt.monic p a hp).free_adjoinRoot

/-- The root extension is a finite `R`-module. -/
theorem RootExt.finite (R : Type u) [CommRing R] (p : ℕ) (a : R) (hp : p ≠ 0) :
    Module.Finite R (RootExt R p a) :=
  (RootExt.monic p a hp).finite_adjoinRoot

/-- The root extension is a flat `R`-module. -/
theorem RootExt.flat (R : Type u) [CommRing R] (p : ℕ) (a : R) (hp : p ≠ 0) :
    Module.Flat R (RootExt R p a) :=
  haveI := RootExt.free R p a hp
  Module.Flat.of_free

/-- The natural map `R → R[x]/(x^p - a)` is injective. -/
theorem RootExt.algebraMap_injective (R : Type u) [CommRing R] [Nontrivial R] (p : ℕ) (a : R)
    (hp : 0 < p) : Function.Injective (algebraMap R (RootExt R p a)) := by
  rw [AdjoinRoot.algebraMap_eq]
  refine AdjoinRoot.of.injective_of_monic_of_degree_pos (RootExt.monic p a hp.ne') ?_
  rw [degree_X_pow_sub_C hp a]
  exact_mod_cast hp

/-! ## The root tower and its colimit -/

/-- The `m`-th stage of the root tower: `R[x]/(x ^ p^m - a)`. -/
noncomputable abbrev RootTower (R : Type u) [CommRing R] (p : ℕ) (a : R) (m : ℕ) : Type u :=
  AdjoinRoot (X ^ (p ^ m) - C a)

/-- The adjoined root at stage `m`. -/
noncomputable abbrev RootTower.root (R : Type u) [CommRing R] (p : ℕ) (a : R) (m : ℕ) :
    RootTower R p a m :=
  AdjoinRoot.root (X ^ (p ^ m) - C a)

/-- `X ^ p^m - C a` is monic. -/
theorem RootTower.monic {R : Type u} [CommRing R] (p : ℕ) (a : R) (hp : p ≠ 0) (m : ℕ) :
    (X ^ (p ^ m) - C a : R[X]).Monic :=
  monic_X_pow_sub_C a (pow_ne_zero m hp)

/-- The defining relation at stage `m`: `root ^ p^m = a`. -/
theorem RootTower.root_pow (R : Type u) [CommRing R] (p : ℕ) (a : R) (m : ℕ) :
    RootTower.root R p a m ^ (p ^ m) = AdjoinRoot.of _ a := by
  have h := AdjoinRoot.eval₂_root (X ^ (p ^ m) - C a : R[X])
  simp only [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
    Polynomial.eval₂_C] at h
  exact sub_eq_zero.mp h

/-- The transition map of the tower: the `m`-th root is the `p`-th power of the `(m+1)`-st. -/
noncomputable def RootTower.step (R : Type u) [CommRing R] (p : ℕ) (a : R) (m : ℕ) :
    RootTower R p a m →+* RootTower R p a (m + 1) :=
  AdjoinRoot.lift (AdjoinRoot.of _) (RootTower.root R p a (m + 1) ^ p) (by
    simp only [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
      Polynomial.eval₂_C, sub_eq_zero]
    rw [← pow_mul, ← pow_succ', RootTower.root_pow])

/-- The transition map sends the `m`-th root to the `p`-th power of the `(m+1)`-st root. -/
theorem RootTower.step_root (R : Type u) [CommRing R] (p : ℕ) (a : R) (m : ℕ) :
    RootTower.step R p a m (RootTower.root R p a m) = RootTower.root R p a (m + 1) ^ p :=
  AdjoinRoot.lift_root _

/-- The iterated transition map `R[x_m]/(x_m^{p^m}-a) → R[x_{m+k}]/(x_{m+k}^{p^{m+k}}-a)`. -/
noncomputable def RootTower.stepIter (R : Type u) [CommRing R] (p : ℕ) (a : R) (m : ℕ) :
    ∀ k, RootTower R p a m →+* RootTower R p a (m + k)
  | 0 => RingHom.id _
  | k + 1 => (RootTower.step R p a (m + k)).comp (RootTower.stepIter R p a m k)

/-- The transition maps of the tower, in the form required by a filtered colimit. -/
noncomputable def RootTower.stepMap (R : Type u) [CommRing R] (p : ℕ) (a : R) (i j : ℕ)
    (h : i ≤ j) : RootTower R p a i →+* RootTower R p a j :=
  (Nat.add_sub_cancel' h) ▸ RootTower.stepIter R p a i (j - i)

/-- **The root closure** `R[a^{1/p^∞}]` of `a`: the filtered colimit of the tower. -/
noncomputable abbrev RootClosure (R : Type u) [CommRing R] (p : ℕ) (a : R) : Type u :=
  Ring.DirectLimit (RootTower R p a) fun i j h => ⇑(RootTower.stepMap R p a i j h)

/-- The canonical map from the `m`-th stage to the root closure. -/
noncomputable abbrev RootClosure.of (R : Type u) [CommRing R] (p : ℕ) (a : R) (m : ℕ) :
    RootTower R p a m →+* RootClosure R p a :=
  Ring.DirectLimit.of (RootTower R p a) (fun i j h => ⇑(RootTower.stepMap R p a i j h)) m

/-- **The pseudo-uniformizer data of the root closure**: `varpi k` is the `p^k`-th root of `a`
coming from the `(k+1)`-st stage. -/
noncomputable def RootClosure.varpi (R : Type u) [CommRing R] (p : ℕ) (a : R) (k : ℕ) :
    RootClosure R p a :=
  RootClosure.of R p a (k + 1) (RootTower.root R p a (k + 1))

/-- The root closure carries the structure map `R → R[a^{1/p^∞}]` from the zeroth stage. -/
noncomputable abbrev RootClosure.algebraMap' (R : Type u) [CommRing R] (p : ℕ) (a : R) :
    R →+* RootClosure R p a :=
  (RootClosure.of R p a 0).comp (AdjoinRoot.of _)



/-! ## The `p`-adic completion of the root closure -/

/-- The `R`-algebra structure on the root closure, from the zeroth stage. -/
noncomputable instance RootClosure.instAlgebra (R : Type u) [CommRing R] (p : ℕ) (a : R) :
    Algebra R (RootClosure R p a) :=
  (RootClosure.algebraMap' R p a).toAlgebra

/-- **The `p`-adic completion** of the root closure `R[a^{1/p^∞}]`.  This is the ring that
Bhatt's construction produces: it is `p`-adically complete by construction. -/
noncomputable abbrev RootClosureCompletion (R : Type u) [CommRing R] (p : ℕ) (a : R) : Type u :=
  AdicCompletion (Ideal.span {(p : RootClosure R p a)}) (RootClosure R p a)

/-- The structure map `R[a^{1/p^∞}] → (R[a^{1/p^∞}])^` into the `p`-adic completion. -/
noncomputable abbrev RootClosureCompletion.of (R : Type u) [CommRing R] (p : ℕ) (a : R) :
    RootClosure R p a →+* RootClosureCompletion R p a :=
  algebraMap (RootClosure R p a) (RootClosureCompletion R p a)

/-- The structure map `R → (R[a^{1/p^∞}])^`. -/
noncomputable abbrev RootClosureCompletion.algebraMap' (R : Type u) [CommRing R] (p : ℕ) (a : R) :
    R →+* RootClosureCompletion R p a :=
  (RootClosureCompletion.of R p a).comp (RootClosure.algebraMap' R p a)


/-! ## Algebra structures on the completion and on its reduction mod `p` -/

/-- The `R`-algebra structure on the `p`-adic completion of the root closure. -/
noncomputable instance RootClosureCompletion.instAlgebra (R : Type u) [CommRing R] (p : ℕ) (a : R) :
    Algebra R (RootClosureCompletion R p a) :=
  (RootClosureCompletion.algebraMap' R p a).toAlgebra

/-- The `R ⧸ (p)`-algebra structure on the reduction of the root closure modulo `p`. -/
noncomputable instance RootClosure.modPAlgebra (R : Type u) [CommRing R] (p : ℕ) (a : R) :
    Algebra (R ⧸ Ideal.span {(p : R)})
      (RootClosure R p a ⧸ Ideal.span {(p : RootClosure R p a)}) :=
  Ideal.Quotient.algebraQuotientOfLEComap (by
    rw [Ideal.span_le]
    rintro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact Ideal.mem_comap.mpr (by
      rw [map_natCast]
      exact Ideal.subset_span (Set.mem_singleton _)))

/-- The `R ⧸ (p)`-algebra structure on the reduction of the completion modulo `p`. -/
noncomputable instance RootClosureCompletion.modPAlgebra (R : Type u) [CommRing R] (p : ℕ)
    (a : R) : Algebra (R ⧸ Ideal.span {(p : R)})
      (RootClosureCompletion R p a ⧸ Ideal.span {(p : RootClosureCompletion R p a)}) :=
  Ideal.Quotient.algebraQuotientOfLEComap (by
    rw [Ideal.span_le]
    rintro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact Ideal.mem_comap.mpr (by
      rw [map_natCast]
      exact Ideal.subset_span (Set.mem_singleton _)))

end Work.DSM1p
