import Mathlib
import Submission.Work.DSEQP.AcDefs

/-!
# The root tower acts on the level maps `ofLvl` of the perfected Čech complex (node EQP)

The perfected Čech complex `K = Č(U, 𝒪_X^{1/p^∞})` of `Submission/Work/DSEQP/PerfCech.lean` is a
complex of `W`-modules, `W = Γ(X,⊤)^{1/p^∞}`, and the level-`e` maps
`ofLvl U n e : Č(U, 𝒪_X) ⟶ Kⁿ` (`Submission/Work/DSEQP/AcDefs.lean`) are the structural maps from
the ordinary Čech complex.  The root tower `varpi g k = g^{1/p^k} ∈ W`
(`Submission/Work/DSEQP/PerfAlmost.lean`) is the element by which the almost-acyclicity argument
kills cohomology classes.

This file computes the interaction of the two: **`varpi g k` acts on `ofLvl U n E x` by the
`p^(E-k)`-th power of `g`**, i.e.

`S.varpi g k • S.ofLvl U n E x = S.ofLvl U n E (g ^ p ^ (E - k) • x)`   (`AcSmul`)

for `k ≤ E`.  This is the "strict `p`-semilinearity" of the level maps, and it is the input that
feeds the ordinary Čech differential of `Work.DSEQP.asm_test`
(`Submission/Work/DSEQP/_asm_ac.lean`).

The proof is componentwise.  Writing `V = CechOp U n a` for the `a`-th Čech index in degree `n`:

* `S.ofLvl U n E x` has `a`-th component `Perf.of E (cunpack U n x a)`;
* `S.Wmap V (S.varpi g k) = Perf.of k (phiU g)`, so the `a`-th component of the left hand side is
  `Perf.of k (phiU g) * Perf.of E (cunpack U n x a)`;
* multiplication in a perfection of representatives at levels `k ≤ E` is computed by
  `Perf.of_mul`, giving `Perf.of E ((phiU g) ^ p ^ (E-k) * cunpack U n x a)`;
* the right hand side is `Perf.of E (cunpack U n (g ^ p ^ (E-k) • x) a)`, and `cunpack` is
  `A`-linear, with the `A`-action on the sections over `V` given by multiplication by `phiU`
  (`cunpack_smul` below, which is `rfl` at the level of the `A`-module structure installed by
  `DSMap.cechPresheaf`).
-/

open CategoryTheory AlgebraicGeometry Limits Opposite
open scoped Simplicial BigOperators

namespace Work.DSEQP

universe u

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000

namespace PerfSetup

variable {A : Type u} [CommRing A] {p : ℕ} [Fact p.Prime] {X : Scheme.{u}} [IsIntegral X]
  {f : X ⟶ Spec (.of A)} {ι : Type u}

omit [IsIntegral X] in
/-- The `W`-action on `Psec V` is multiplication by the structure map `Wmap V`.  (This is the
unfolding of the `Algebra` instance `instAlgebraPsec`; it is stated separately so that the
`Algebra.smul_def` rewrite below is applied at the *unfolded* type `S.Psec V` rather than at
`↥(S.kobj U n a)`, where the instance is only found by unfolding.) -/
theorem Psec_smul (S : PerfSetup A p X f) (V : X.Opens) (c : S.W) (y : S.Psec V) :
    c • y = S.Wmap V c * y := by
  rw [Algebra.smul_def, RingHom.algebraMap_toAlgebra]

omit [IsIntegral X] in
/-- The `a`-th component of the ordinary Čech term is `A`-linearly decomposed by `cunpack`: the
`A`-action on the sections `Γ(X, CechOp U n a)` is multiplication by `phiU`. -/
theorem cunpack_smul (U : ι → X.Opens) (n : ℕ) (a : (CechIdx U n).I)
    (h : A) (x : (DSMap.cech A X f U).X n) :
    cunpack U n (h • x) a = DSMap.phiU A X f (CechOp U n a) h * cunpack U n x a := by
  rw [cunpack_apply, map_smul, ← cunpack_apply U n x a]
  rfl

/-- The `V`-component of `S.varpi g k` is the level-`k` representative of `phiU g` in the
perfection of the sections over `V`. -/
theorem Wmap_varpi (S : PerfSetup A p X f) [CharP S.W p] [PerfectRing S.W p]
    (V : X.Opens) (g : A) (k : ℕ) :
    S.Wmap V (S.varpi g k) = Perf.of (Γ(X,V)) p (S.hpU V) k (DSMap.phiU A X f V g) := by
  rw [S.varpi_eq]
  have hφ : DSMap.phiU A X f V g = S.resTop V (DSMap.phi A X f g) := by
    have h2 : DSMap.phiU A X f ⊤ = DSMap.phi A X f := by
      ext b
      show (X.presheaf.map (homOfLE le_top).op).hom (DSMap.phi A X f b) = _
      rw [Subsingleton.elim (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)) (𝟙 ⊤), op_id,
        X.presheaf.map_id]
      rfl
    have h1 := DSMap.phiU_res A X f (homOfLE (le_top : V ≤ ⊤)) g
    rw [h2] at h1
    exact h1.symm
  rw [hφ]
  exact Perf.map_of (hp := S.hpU ⊤) (hpS := S.hpU V) (f := S.resTop V) k
    (DSMap.phi A X f g)

omit [IsIntegral X] in
/-- Two elements of a Čech term of the perfected complex agree if all their components do
(the product projections `Pi.π (S.kobj U n) a` are jointly injective). -/
theorem kobj_ext (S : PerfSetup A p X f) (U : ι → X.Opens) (n : ℕ) {z w : (S.K U).X n}
    (h : ∀ a, (Pi.π (S.kobj U n) a).hom z = (Pi.π (S.kobj U n) a).hom w) : z = w := by
  have h1 : S.kunpack U n z = S.kunpack U n w := by
    funext a
    rw [S.kunpack_apply, S.kunpack_apply]
    exact h a
  calc z = S.kpack U n (S.kunpack U n z) := (S.kpack_kunpack U n z).symm
    _ = S.kpack U n (S.kunpack U n w) := by rw [h1]
    _ = w := S.kpack_kunpack U n w

/-- **The componentwise statement of `AcSmul`.**  The `a`-th component of
`varpi g k • ofLvl U n E x` is the `a`-th component of `ofLvl U n E (g ^ p ^ (E - k) • x)`. -/
theorem kobj_π_smul_ofLvl (S : PerfSetup A p X f) [CharP S.W p] [PerfectRing S.W p]
    (U : ι → X.Opens) (n k E : ℕ) (hk : k ≤ E) (g : A) (x : (DSMap.cech A X f U).X n)
    (a : (CechIdx U n).I) :
    (Pi.π (S.kobj U n) a).hom (S.varpi g k • S.ofLvl U n E x) =
      (Pi.π (S.kobj U n) a).hom (S.ofLvl U n E (g ^ p ^ (E - k) • x)) := by
  have hπ : ∀ (m : ℕ) (z : (DSMap.cech A X f U).X n),
      (Pi.π (S.kobj U n) a).hom (S.ofLvl U n m z) =
        Perf.of (Γ(X,CechOp U n a)) p (S.hpU _) m (cunpack U n z a) := by
    intro m z
    rw [← S.kunpack_apply U n (S.ofLvl U n m z) a, S.kunpack_ofLvl]
  rw [map_smul, Psec_smul S (CechOp U n a) (S.varpi g k), hπ E x, hπ E _,
    cunpack_smul U n a (g ^ p ^ (E - k)) x,
    Wmap_varpi S (CechOp U n a) g k,
    Perf.of_mul (R := Γ(X, CechOp U n a)) (p := p) (hp := S.hpU _) (i := k) (j := E) (c := E)
      hk le_rfl]
  congr 1
  rw [show E - E = 0 by omega, pow_zero, pow_one, map_pow]

end PerfSetup

theorem AcSmul {A : Type} [CommRing A] {p : ℕ} [Fact p.Prime] {X : AlgebraicGeometry.Scheme}
    [AlgebraicGeometry.IsIntegral X] {f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of A)}
    {ι : Type} [Finite ι] (S : Work.DSEQP.PerfSetup A p X f) [CharP S.W p] [PerfectRing S.W p]
    (U : ι → X.Opens) (n k E : ℕ) (hk : k ≤ E) (g : A) (x : (DSMap.cech A X f U).X n) :
    S.varpi g k • S.ofLvl U n E x = S.ofLvl U n E (g ^ p ^ (E - k) • x) := by
  refine PerfSetup.kobj_ext S U n (fun a => ?_)
  exact PerfSetup.kobj_π_smul_ofLvl S U n k E hk g x a

end Work.DSEQP
