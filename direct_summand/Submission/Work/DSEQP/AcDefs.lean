import Mathlib
import Submission.Work.DSEQP.PerfAlmost
import Submission.Work.DSF1.Cech.CechComponents

open CategoryTheory AlgebraicGeometry Limits Opposite
open scoped Simplicial BigOperators

namespace Work.DSEQP

universe u

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000

namespace PerfSetup

variable {A : Type u} [CommRing A] {p : ℕ} [Fact p.Prime] {X : Scheme.{u}}
  {f : X ⟶ Spec (.of A)} {ι : Type u}

/-- The `a`-th term of the ordinary Čech complex of `𝒪_X` in degree `n`. -/
noncomputable abbrev cobj (U : ι → X.Opens) (n : ℕ) (a : (CechIdx U n).I) : ModuleCat.{u} A :=
  (DSMap.cechPresheaf A X f).obj (op (CechOp U n a))

/-- The `a`-th term of the perfected Čech complex in degree `n`. -/
noncomputable abbrev kobj (S : PerfSetup A p X f) (U : ι → X.Opens) (n : ℕ)
    (a : (CechIdx U n).I) : ModuleCat.{u} S.W :=
  S.perfPresheaf.obj (op (CechOp U n a))

/-- Decompose an element of an ordinary Čech term into its coordinates. -/
noncomputable def cunpack (U : ι → X.Opens) (n : ℕ) (x : (DSMap.cech A X f U).X n) :
    ∀ a, Γ(X, CechOp U n a) :=
  fun a => (ModuleCat.piIsoPi (cobj (A := A) (X := X) (f := f) U n)).hom x a

/-- Recompose an element of an ordinary Čech term from its coordinates. -/
noncomputable def cpack (U : ι → X.Opens) (n : ℕ)
    (x : ∀ a, Γ(X, CechOp U n a)) : (DSMap.cech A X f U).X n :=
  (ModuleCat.piIsoPi (cobj (A := A) (X := X) (f := f) U n)).inv x

/-- Decompose an element of a perfected Čech term into its coordinates. -/
noncomputable def kunpack (S : PerfSetup A p X f) (U : ι → X.Opens) (n : ℕ)
    (x : (S.K U).X n) : ∀ a, S.Psec (CechOp U n a) :=
  fun a => (ModuleCat.piIsoPi (kobj S U n)).hom x a

/-- Recompose an element of a perfected Čech term from its coordinates. -/
noncomputable def kpack (S : PerfSetup A p X f) (U : ι → X.Opens) (n : ℕ)
    (x : ∀ a, S.Psec (CechOp U n a)) : (S.K U).X n :=
  (ModuleCat.piIsoPi (kobj S U n)).inv x

/-- The component formula for `kpack`. -/
theorem kpack_apply (S : PerfSetup A p X f) (U : ι → X.Opens) (n : ℕ)
    (x : ∀ a, S.Psec (CechOp U n a)) (a : (CechIdx U n).I) :
    (Pi.π (kobj S U n) a).hom (S.kpack U n x) = x a :=
  ModuleCat.piIsoPi_inv_kernel_ι_apply (kobj S U n) a x

/-- The component formula for `cpack`. -/
theorem cpack_apply (U : ι → X.Opens) (n : ℕ)
    (x : ∀ a, Γ(X, CechOp U n a)) (a : (CechIdx U n).I) :
    (Pi.π (cobj (A := A) (X := X) (f := f) U n) a).hom (cpack U n x) = x a :=
  ModuleCat.piIsoPi_inv_kernel_ι_apply (cobj (A := A) (X := X) (f := f) U n) a x

theorem kunpack_apply (S : PerfSetup A p X f) (U : ι → X.Opens) (n : ℕ)
    (x : (S.K U).X n) (a : (CechIdx U n).I) :
    S.kunpack U n x a = (Pi.π (kobj S U n) a).hom x :=
  ModuleCat.piIsoPi_hom_ker_subtype_apply (kobj S U n) a x

theorem cunpack_apply (U : ι → X.Opens) (n : ℕ)
    (x : (DSMap.cech A X f U).X n) (a : (CechIdx U n).I) :
    cunpack U n x a = (Pi.π (cobj (A := A) (X := X) (f := f) U n) a).hom x :=
  ModuleCat.piIsoPi_hom_ker_subtype_apply (cobj (A := A) (X := X) (f := f) U n) a x

theorem kunpack_kpack (S : PerfSetup A p X f) (U : ι → X.Opens) (n : ℕ)
    (x : ∀ a, S.Psec (CechOp U n a)) : S.kunpack U n (S.kpack U n x) = x := by
  funext a
  rw [kunpack_apply, kpack_apply]

theorem cunpack_cpack (U : ι → X.Opens) (n : ℕ)
    (x : ∀ a, Γ(X, CechOp U n a)) :
    cunpack U n (cpack (A := A) (X := X) (f := f) U n x) = x := by
  funext a
  rw [cunpack_apply, cpack_apply]

theorem kpack_kunpack (S : PerfSetup A p X f) (U : ι → X.Opens) (n : ℕ)
    (x : (S.K U).X n) : S.kpack U n (S.kunpack U n x) = x :=
  Iso.hom_inv_id_apply (ModuleCat.piIsoPi (kobj S U n)) x

theorem cpack_cunpack (U : ι → X.Opens) (n : ℕ)
    (x : (DSMap.cech A X f U).X n) :
    cpack (A := A) (X := X) (f := f) U n (cunpack U n x) = x :=
  Iso.hom_inv_id_apply (ModuleCat.piIsoPi (cobj (A := A) (X := X) (f := f) U n)) x

theorem kpack_inj (S : PerfSetup A p X f) (U : ι → X.Opens) (n : ℕ)
    {x y : ∀ a, S.Psec (CechOp U n a)} (h : S.kpack U n x = S.kpack U n y) : x = y := by
  have h2 : S.kunpack U n (S.kpack U n x) = S.kunpack U n (S.kpack U n y) := congrArg _ h
  rwa [kunpack_kpack S U n x, kunpack_kpack S U n y] at h2

theorem cpack_inj (U : ι → X.Opens) (n : ℕ)
    {x y : ∀ a, Γ(X, CechOp U n a)}
    (h : cpack (A := A) (X := X) (f := f) U n x = cpack (A := A) (X := X) (f := f) U n y) :
    x = y := by
  have h2 : cunpack U n (cpack (A := A) (X := X) (f := f) U n x) =
      cunpack U n (cpack (A := A) (X := X) (f := f) U n y) := congrArg _ h
  rwa [cunpack_cpack U n x, cunpack_cpack U n y] at h2

/-- The componentwise Frobenius transition `x ↦ x ^ p` on the ordinary Čech term. -/
noncomputable def frobC (p : ℕ) (U : ι → X.Opens) (n : ℕ) (x : (DSMap.cech A X f U).X n) :
    (DSMap.cech A X f U).X n :=
  cpack (A := A) (X := X) (f := f) U n (fun a => (cunpack U n x a) ^ p)

theorem cunpack_frobC (U : ι → X.Opens) (n : ℕ) (x : (DSMap.cech A X f U).X n) :
    cunpack U n (frobC p U n x) = fun a => (cunpack U n x a) ^ p :=
  cunpack_cpack U n _

theorem cunpack_frobC_iter (U : ι → X.Opens) (n : ℕ) (m : ℕ)
    (x : (DSMap.cech A X f U).X n) :
    cunpack U n ((frobC p U n)^[m] x) = fun a => (cunpack U n x a) ^ p ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply', cunpack_frobC, ih]
    funext a
    rw [← pow_mul, pow_succ]

/-- The level-`e` map from the ordinary Čech term to the perfected one. -/
noncomputable def ofLvl (S : PerfSetup A p X f) (U : ι → X.Opens) (n e : ℕ)
    (x : (DSMap.cech A X f U).X n) : (S.K U).X n :=
  S.kpack U n (fun a => Perf.of (Γ(X, CechOp U n a)) p (S.hpU _) e (cunpack U n x a))

theorem kunpack_ofLvl (S : PerfSetup A p X f) (U : ι → X.Opens) (n e : ℕ)
    (x : (DSMap.cech A X f U).X n) :
    S.kunpack U n (S.ofLvl U n e x) =
      fun a => Perf.of (Γ(X, CechOp U n a)) p (S.hpU _) e (cunpack U n x a) := by
  rw [ofLvl, kunpack_kpack]

end PerfSetup

end Work.DSEQP
