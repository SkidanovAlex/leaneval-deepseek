import Mathlib
import Submission.Work.SSGRoute.EulerSymm.finrank_invariants_diagTensor_regular
import Submission.Work.SSGRoute.EulerSymm.finrank_invariants_diagTensor_of_addEquiv
import Submission.Work.SSGRoute.E7Fin.pullbackRegularInvariants
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The invariant-dimension engine for the uniformity of the level Euler characteristic

Lane `Work.SSGRoute.coker_obstruction_pt`.  This file isolates the *linear algebra* that converts
a **structure statement** about the trivial-coefficient local cohomology `A₁ = H¹_loc(U, 𝔽_p)`,
`A₂ = H²_loc(U, 𝔽_p)` into the **uniformity** of the level Euler characteristic
(`Work.SSGRoute.E7Fin.IsUniformDC`, Milne *ADT* I.2.8), i.e. into the existence of a constant `e`
with

  `dim (A₁ ⊗ N)^G = dim (A₂ ⊗ N)^G + dim N^G + e · dim N`

for every finite `𝔽_p[G]`-module `N`.

The arithmetic content of Milne I.2.11 is the `𝔽_p[G]`-module isomorphism

  `A₁ ≅ A₂ × 𝔽_p × 𝔽_p[G]^{[L:ℚ_p]}`      (`G` the cyclic prime-to-`p` level group, `𝔽_p` the
  trivial module, `𝔽_p[G]` the regular module),

equivalently `A₁ ≅ A₂ ⊕ 𝔽_p ⊕ 𝔽_p[G]^c`.  The present file proves the *consequence* of that
isomorphism that the Euler characteristic needs, from the three elementary facts about the
diagonal invariant dimension (the existing `EulerSymm.finrank_invariants_diagTensor_regular` for
the regular module, the additivity over products, and the trivial summand).

## Main results

* `E7Fin.diagTensorInvariants_eq_of_equiv` — transport of the invariant dimension along a
  `G`-equivariant linear equivalence.
* `E7Fin.diagTensorInvariants_prod` — additivity in the first tensor factor.
* `E7Fin.diagTensorInvariants_triv` — the trivial summand `𝔽_p`.
* `E7Fin.diagTensorInvariants_regular_pow` — `c` copies of the regular module.
* **`E7Fin.diagTensorInvariants_of_structure`** — the headline: the dimension identity above from
  an equivariant isomorphism `A₁ ≅ 𝔽_p[G]^c × A₂ × 𝔽_p`.
-/

open scoped TensorProduct

namespace Work.SSGRoute.E7Fin

set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

variable {p : ℕ} {G : Type}

section Transport

/-- **Transport of the invariant dimension along an equivariant linear equivalence.**  For finite
`𝔽_p[G]`-modules `A`, `B`, `N` and a `G`-equivariant `e : A ≃ₗ B`, the `G`-invariants of `A ⊗ N`
and of `B ⊗ N` have the same `𝔽_p`-dimension. -/
theorem diagTensorInvariants_eq_of_equiv [Fact p.Prime] [Group G]
    {A B N : Type}
    [AddCommGroup A] [Module (ZMod p) A] [DistribMulAction G A] [SMulCommClass G (ZMod p) A]
    [AddCommGroup B] [Module (ZMod p) B] [DistribMulAction G B] [SMulCommClass G (ZMod p) B]
    [AddCommGroup N] [Module (ZMod p) N] [DistribMulAction G N] [SMulCommClass G (ZMod p) N]
    [Finite A] [Finite B] [Finite N]
    (e : A ≃ₗ[ZMod p] B) (he : ∀ (g : G) (x : A), e (g • x) = g • e x) :
    Module.finrank (ZMod p)
        ↥(Work.SSGRoute.PTCore.invariantsSubmodule G (ZMod p)
          (TensorProduct (ZMod p) A N)) =
      Module.finrank (ZMod p)
        ↥(Work.SSGRoute.PTCore.invariantsSubmodule G (ZMod p)
          (TensorProduct (ZMod p) B N)) :=
  Work.SSGRoute.PTCore.finrank_invariants_equivariant
    (TensorProduct.congr e (LinearEquiv.refl (ZMod p) N))
    (Work.SSGRoute.PTCore.tensorProduct_congr_equivariant p e (LinearEquiv.refl (ZMod p) N)
      he (fun _ _ => rfl))

end Transport

section Prod

/-- **Additivity of the invariant dimension in the first tensor factor.**  For finite
`𝔽_p[G]`-modules `X`, `Y`, `N`,

  `dim ((X × Y) ⊗ N)^G = dim (X ⊗ N)^G + dim (Y ⊗ N)^G`. -/
theorem diagTensorInvariants_prod [Fact p.Prime] [Group G]
    (X Y N : Type)
    [AddCommGroup X] [Module (ZMod p) X] [DistribMulAction G X] [SMulCommClass G (ZMod p) X]
    [AddCommGroup Y] [Module (ZMod p) Y] [DistribMulAction G Y] [SMulCommClass G (ZMod p) Y]
    [AddCommGroup N] [Module (ZMod p) N] [DistribMulAction G N] [SMulCommClass G (ZMod p) N]
    [Finite X] [Finite Y] [Finite N] :
    Module.finrank (ZMod p)
        ↥(Work.SSGRoute.PTCore.invariantsSubmodule G (ZMod p)
          (TensorProduct (ZMod p) (X × Y) N)) =
      Module.finrank (ZMod p)
          ↥(Work.SSGRoute.PTCore.invariantsSubmodule G (ZMod p)
            (TensorProduct (ZMod p) X N)) +
        Module.finrank (ZMod p)
          ↥(Work.SSGRoute.PTCore.invariantsSubmodule G (ZMod p)
            (TensorProduct (ZMod p) Y N)) := by
  have h₁ : Module.finrank (ZMod p)
        ↥(Work.SSGRoute.PTCore.invariantsSubmodule G (ZMod p)
          (TensorProduct (ZMod p) (X × Y) N)) =
      Module.finrank (ZMod p)
        ↥(Work.SSGRoute.PTCore.invariantsSubmodule G (ZMod p)
          ((TensorProduct (ZMod p) X N) × (TensorProduct (ZMod p) Y N))) :=
    Work.SSGRoute.PTCore.finrank_invariants_equivariant
      (TensorProduct.prodLeft (ZMod p) (ZMod p) X Y N)
      (fun g x =>
        Work.SSGRoute.EulerSymm.tensorProduct_prodLeft_equivariant_aux (p := p) (G := G)
          (M₁ := X) (M₂ := Y) (N := N) g x)
  haveI : Finite (TensorProduct (ZMod p) X N) :=
    Work.Shrinking.finite_tensorProduct_of_finite (ZMod p) X N
  haveI : Finite (TensorProduct (ZMod p) Y N) :=
    Work.Shrinking.finite_tensorProduct_of_finite (ZMod p) Y N
  rw [h₁, Work.SSGRoute.EulerSymm.finrank_invariants_prod_aux (p := p) (G := G)
    (V := TensorProduct (ZMod p) X N) (W := TensorProduct (ZMod p) Y N)]

end Prod

section Triv

/-- **The trivial summand.**  If the `G`-action on `𝔽_p` is trivial, then
`dim (𝔽_p ⊗ N)^G = dim N^G`. -/
theorem diagTensorInvariants_triv [Fact p.Prime] [Group G]
    [DistribMulAction G (ZMod p)] [SMulCommClass G (ZMod p) (ZMod p)]
    (hpt : ∀ (g : G) (z : ZMod p), g • z = z)
    (N : Type) [AddCommGroup N] [Module (ZMod p) N] [DistribMulAction G N]
    [SMulCommClass G (ZMod p) N] [Finite N] :
    Module.finrank (ZMod p)
        ↥(Work.SSGRoute.PTCore.invariantsSubmodule G (ZMod p)
          (TensorProduct (ZMod p) (ZMod p) N)) =
      Module.finrank (ZMod p)
        ↥(Work.SSGRoute.PTCore.invariantsSubmodule G (ZMod p) N) := by
  refine Work.SSGRoute.PTCore.finrank_invariants_equivariant
    (TensorProduct.lid (ZMod p) N) ?_
  intro g x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a n =>
    rw [Work.Shrinking.diagTensor_smul_tmul, hpt g a, TensorProduct.lid_tmul,
      TensorProduct.lid_tmul]
    exact (smul_comm g a n).symm
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]

end Triv

section Pow

/-- The linear equivalence `(Fin (c+1) → X) ≃ X × (Fin c → X)` (head and tail). -/
noncomputable def finSuccEquiv (R : Type) [Semiring R] (X : Type) [AddCommMonoid X]
    [Module R X] (c : ℕ) : (Fin (c + 1) → X) ≃ₗ[R] X × (Fin c → X) where
  toFun f := (f 0, fun i => f i.succ)
  invFun q := fun j => Fin.cases q.1 q.2 j
  left_inv f := by
    funext j
    cases j using Fin.cases with
    | zero => simp
    | succ i => simp
  right_inv q := by
    refine Prod.ext ?_ ?_
    · simp
    · funext i; simp
  map_add' f f' := by
    refine Prod.ext ?_ ?_
    · simp [Pi.add_apply]
    · funext i; simp [Pi.add_apply]
  map_smul' r f := by
    refine Prod.ext ?_ ?_
    · simp [Pi.smul_apply]
    · funext i; simp [Pi.smul_apply]

/-- `finSuccEquiv` is `G`-equivariant for the pointwise actions. -/
theorem finSuccEquiv_equivariant {G : Type} [Group G] {R : Type} [Semiring R]
    (X : Type) [AddCommMonoid X] [Module R X] [DistribMulAction G X]
    [SMulCommClass G R X] (c : ℕ) (g : G) (f : Fin (c + 1) → X) :
    finSuccEquiv R X c (g • f) = g • finSuccEquiv R X c f := by
  refine Prod.ext ?_ ?_
  · simp [finSuccEquiv]
  · funext i; simp [finSuccEquiv]

/-- **`c` copies of the regular module**: `dim ((𝔽_p[G]^c) ⊗ N)^G = c · dim ((𝔽_p[G]) ⊗ N)^G`.

The proof is the induction on `c` using the head/tail decomposition
`Fin (c+1) → X ≃ X × (Fin c → X)` and the additivity `diagTensorInvariants_prod`. -/
theorem diagTensorInvariants_regular_pow [Fact p.Prime] [Group G] [Fintype G] [DecidableEq G]
    (c : ℕ) (N : Type) [AddCommGroup N] [Module (ZMod p) N] [DistribMulAction G N]
    [SMulCommClass G (ZMod p) N] [Finite N] :
    Module.finrank (ZMod p)
        ↥(Work.SSGRoute.PTCore.invariantsSubmodule G (ZMod p)
          (TensorProduct (ZMod p) (Fin c → MonoidAlgebra (ZMod p) G) N)) =
      c * Module.finrank (ZMod p)
        ↥(Work.SSGRoute.PTCore.invariantsSubmodule G (ZMod p)
          (TensorProduct (ZMod p) (MonoidAlgebra (ZMod p) G) N)) := by
  haveI : Fintype (MonoidAlgebra (ZMod p) G) :=
    Fintype.ofEquiv (G →₀ ZMod p)
      (MonoidAlgebra.coeffLinearEquiv (ZMod p) (S := ZMod p) (M := G)).symm.toEquiv
  induction c with
  | zero =>
    -- `Fin 0 → X` is the zero module: the invariants of `0 ⊗ N` are trivial
    have hzero : ∀ x : TensorProduct (ZMod p) (Fin 0 → MonoidAlgebra (ZMod p) G) N, x = 0 := by
      intro x
      induction x using TensorProduct.induction_on with
      | zero => rfl
      | tmul f n =>
        rw [show f = 0 from funext (fun i => Fin.elim0 i), TensorProduct.zero_tmul]
      | add x y hx hy => rw [hx, hy, add_zero]
    have h0 : Module.finrank (ZMod p)
        ↥(Work.SSGRoute.PTCore.invariantsSubmodule G (ZMod p)
          (TensorProduct (ZMod p) (Fin 0 → MonoidAlgebra (ZMod p) G) N)) = 0 := by
      haveI : Subsingleton
          (TensorProduct (ZMod p) (Fin 0 → MonoidAlgebra (ZMod p) G) N) :=
        ⟨fun a b => by rw [hzero a, hzero b]⟩
      exact Module.finrank_zero_of_subsingleton
    rw [h0, zero_mul]
  | succ c ih =>
    -- head/tail decomposition
    have h₁ : Module.finrank (ZMod p)
        ↥(Work.SSGRoute.PTCore.invariantsSubmodule G (ZMod p)
          (TensorProduct (ZMod p) (Fin (c + 1) → MonoidAlgebra (ZMod p) G) N)) =
        Module.finrank (ZMod p)
          ↥(Work.SSGRoute.PTCore.invariantsSubmodule G (ZMod p)
            (TensorProduct (ZMod p)
              (MonoidAlgebra (ZMod p) G × (Fin c → MonoidAlgebra (ZMod p) G)) N)) :=
      diagTensorInvariants_eq_of_equiv (N := N)
        (finSuccEquiv (ZMod p) (MonoidAlgebra (ZMod p) G) c)
        (finSuccEquiv_equivariant (R := ZMod p) (MonoidAlgebra (ZMod p) G) c)
    rw [h₁, diagTensorInvariants_prod (MonoidAlgebra (ZMod p) G)
      (Fin c → MonoidAlgebra (ZMod p) G) N, ih]
    ring

/-- **Additivity in the number of copies of an arbitrary first factor**:
`dim ((X^c) ⊗ N)^G = c · dim (X ⊗ N)^G`.

The proof is the induction on `c` using the head/tail decomposition
`Fin (c+1) → X ≃ X × (Fin c → X)` (`finSuccEquiv`) and the additivity
`diagTensorInvariants_prod`. -/
theorem diagTensorInvariants_pow [Fact p.Prime] [Group G]
    (c : ℕ) (X N : Type)
    [AddCommGroup X] [Module (ZMod p) X] [DistribMulAction G X] [SMulCommClass G (ZMod p) X]
    [AddCommGroup N] [Module (ZMod p) N] [DistribMulAction G N] [SMulCommClass G (ZMod p) N]
    [Finite X] [Finite N] :
    Module.finrank (ZMod p)
        ↥(Work.SSGRoute.PTCore.invariantsSubmodule G (ZMod p)
          (TensorProduct (ZMod p) (Fin c → X) N)) =
      c * Module.finrank (ZMod p)
        ↥(Work.SSGRoute.PTCore.invariantsSubmodule G (ZMod p)
          (TensorProduct (ZMod p) X N)) := by
  induction c with
  | zero =>
    have hzero : ∀ x : TensorProduct (ZMod p) (Fin 0 → X) N, x = 0 := by
      intro x
      induction x using TensorProduct.induction_on with
      | zero => rfl
      | tmul f n =>
        rw [show f = 0 from funext (fun i => Fin.elim0 i), TensorProduct.zero_tmul]
      | add x y hx hy => rw [hx, hy, add_zero]
    have h0 : Module.finrank (ZMod p)
        ↥(Work.SSGRoute.PTCore.invariantsSubmodule G (ZMod p)
          (TensorProduct (ZMod p) (Fin 0 → X) N)) = 0 := by
      haveI : Subsingleton (TensorProduct (ZMod p) (Fin 0 → X) N) :=
        ⟨fun a b => by rw [hzero a, hzero b]⟩
      exact Module.finrank_zero_of_subsingleton
    rw [h0, zero_mul]
  | succ c ih =>
    have h₁ : Module.finrank (ZMod p)
        ↥(Work.SSGRoute.PTCore.invariantsSubmodule G (ZMod p)
          (TensorProduct (ZMod p) (Fin (c + 1) → X) N)) =
        Module.finrank (ZMod p)
          ↥(Work.SSGRoute.PTCore.invariantsSubmodule G (ZMod p)
            (TensorProduct (ZMod p) (X × (Fin c → X)) N)) :=
      diagTensorInvariants_eq_of_equiv (N := N)
        (finSuccEquiv (ZMod p) X c)
        (finSuccEquiv_equivariant (R := ZMod p) X c)
    rw [h₁, diagTensorInvariants_prod X (Fin c → X) N, ih]
    ring

/-- **The regular summand contributes `dim N`.**  This is
`EulerSymm.finrank_invariants_diagTensor_regular`, restated in the vocabulary of this file. -/
theorem diagTensorInvariants_regular [Fact p.Prime] [Group G] [Fintype G]
    (N : Type) [AddCommGroup N] [Module (ZMod p) N] [DistribMulAction G N]
    [SMulCommClass G (ZMod p) N] [Finite N] :
    Module.finrank (ZMod p)
        ↥(Work.SSGRoute.PTCore.invariantsSubmodule G (ZMod p)
          (TensorProduct (ZMod p) (MonoidAlgebra (ZMod p) G) N)) =
      Module.finrank (ZMod p) N :=
  Work.SSGRoute.EulerSymm.finrank_invariants_diagTensor_regular p G N

end Pow

section Structure

open scoped TensorProduct in
/-- **The structure engine.**  If a finite `𝔽_p[G]`-module `A` is `G`-equivariantly isomorphic to
`𝔽_p[G]^c × B × D`, where `D` is a `G`-module whose diagonal tensor with `N` has invariants of
dimension `dim N^G`, then

  `dim (A ⊗ N)^G = c · dim N + dim (B ⊗ N)^G + dim N^G`.

Applied with `A = A₁ = H¹_loc(U, 𝔽_p)`, `B = A₂ = H²_loc(U, 𝔽_p)`, `D = 𝔽_p` (trivial) this is the
dimension identity underlying the uniformity of the level Euler characteristic. -/
theorem diagTensorInvariants_of_structure [Fact p.Prime] [Group G] [Fintype G] [DecidableEq G]
    (c : ℕ) {A B D N : Type}
    [AddCommGroup A] [Module (ZMod p) A] [DistribMulAction G A] [SMulCommClass G (ZMod p) A]
    [AddCommGroup B] [Module (ZMod p) B] [DistribMulAction G B] [SMulCommClass G (ZMod p) B]
    [AddCommGroup D] [Module (ZMod p) D] [DistribMulAction G D] [SMulCommClass G (ZMod p) D]
    [AddCommGroup N] [Module (ZMod p) N] [DistribMulAction G N] [SMulCommClass G (ZMod p) N]
    [Finite A] [Finite B] [Finite D] [Finite N]
    (e : A ≃ₗ[ZMod p] ((Fin c → MonoidAlgebra (ZMod p) G) × B × D))
    (he : ∀ (g : G) (x : A), e (g • x) = g • e x)
    (hD : Module.finrank (ZMod p)
        ↥(Work.SSGRoute.PTCore.invariantsSubmodule G (ZMod p)
          (TensorProduct (ZMod p) D N)) =
      Module.finrank (ZMod p) ↥(Work.SSGRoute.PTCore.invariantsSubmodule G (ZMod p) N)) :
    Module.finrank (ZMod p)
        ↥(Work.SSGRoute.PTCore.invariantsSubmodule G (ZMod p)
          (TensorProduct (ZMod p) A N)) =
      c * Module.finrank (ZMod p) N +
        Module.finrank (ZMod p)
          ↥(Work.SSGRoute.PTCore.invariantsSubmodule G (ZMod p)
            (TensorProduct (ZMod p) B N)) +
        Module.finrank (ZMod p)
          ↥(Work.SSGRoute.PTCore.invariantsSubmodule G (ZMod p) N) := by
  haveI : Fintype (MonoidAlgebra (ZMod p) G) :=
    Fintype.ofEquiv (G →₀ ZMod p)
      (MonoidAlgebra.coeffLinearEquiv (ZMod p) (S := ZMod p) (M := G)).symm.toEquiv
  -- transport along `e`
  have h₁ := diagTensorInvariants_eq_of_equiv (N := N) e he
  -- split the two products off, in the first tensor factor
  rw [h₁]
  rw [diagTensorInvariants_prod (Fin c → MonoidAlgebra (ZMod p) G) (B × D) N]
  rw [diagTensorInvariants_prod B D N]
  rw [diagTensorInvariants_regular_pow c N, diagTensorInvariants_regular N, hD]
  ring

end Structure

/-- **The structure engine with abstract summands.**  If `A ≅ P × B × E₀` `G`-equivariantly, the
`P`-summand contributes `c · dim N` (the *regular* case: `dim (𝔽_p[G] ⊗ N)^G = dim N`) and the
`E₀`-summand contributes `dim N^G`, then

  `dim (A ⊗ N)^G = c · dim N + dim (B ⊗ N)^G + dim N^G`.

This is the abstract form of `diagTensorInvariants_of_structure` (there `P = 𝔽_p[G]^c` and
`E₀ = 𝔽_p`); it is the form in which the pullback (`G` infinite through a finite quotient) case is
consumed, the two dimension properties being supplied by `diagTensorInvariants_pow` together with
`diagTensorInvariants_pullback_regular` (for `P`) and by `diagTensorInvariants_triv` (for `E₀`). -/
theorem diagTensorInvariants_of_summands [Fact p.Prime] [Group G]
    (c : ℕ) {A P B E₀ N : Type}
    [AddCommGroup A] [Module (ZMod p) A] [DistribMulAction G A] [SMulCommClass G (ZMod p) A]
    [AddCommGroup P] [Module (ZMod p) P] [DistribMulAction G P] [SMulCommClass G (ZMod p) P]
    [AddCommGroup B] [Module (ZMod p) B] [DistribMulAction G B] [SMulCommClass G (ZMod p) B]
    [AddCommGroup E₀] [Module (ZMod p) E₀] [DistribMulAction G E₀] [SMulCommClass G (ZMod p) E₀]
    [AddCommGroup N] [Module (ZMod p) N] [DistribMulAction G N] [SMulCommClass G (ZMod p) N]
    [Finite A] [Finite P] [Finite B] [Finite E₀] [Finite N]
    (e : A ≃ₗ[ZMod p] (P × B × E₀))
    (he : ∀ (g : G) (x : A), e (g • x) = g • e x)
    (hP : Module.finrank (ZMod p)
        ↥(Work.SSGRoute.PTCore.invariantsSubmodule G (ZMod p)
          (TensorProduct (ZMod p) P N)) =
      c * Module.finrank (ZMod p) N)
    (hE₀ : Module.finrank (ZMod p)
        ↥(Work.SSGRoute.PTCore.invariantsSubmodule G (ZMod p)
          (TensorProduct (ZMod p) E₀ N)) =
      Module.finrank (ZMod p) ↥(Work.SSGRoute.PTCore.invariantsSubmodule G (ZMod p) N)) :
    Module.finrank (ZMod p)
        ↥(Work.SSGRoute.PTCore.invariantsSubmodule G (ZMod p)
          (TensorProduct (ZMod p) A N)) =
      c * Module.finrank (ZMod p) N +
        Module.finrank (ZMod p)
          ↥(Work.SSGRoute.PTCore.invariantsSubmodule G (ZMod p)
            (TensorProduct (ZMod p) B N)) +
        Module.finrank (ZMod p)
          ↥(Work.SSGRoute.PTCore.invariantsSubmodule G (ZMod p) N) := by
  have h₁ := diagTensorInvariants_eq_of_equiv (N := N) e he
  rw [h₁]
  rw [diagTensorInvariants_prod P (B × E₀) N]
  rw [diagTensorInvariants_prod B E₀ N]
  rw [hP, hE₀]
  ring

section PullbackStructure

open scoped TensorProduct in
/-- **The structure engine in the pulled-back form.**  This is the form used for the local Galois
group `D_C = decomp k A ⊓ res⁻¹C`, which is infinite but acts on the trivial-coefficient local
cohomology through the finite quotient `↥((res k K) '' D_C)`.

If `A ≅ 𝔽_p[Q]^c × B × D` `G`-equivariantly, `ker φ` acts trivially on `N`, and the `D`-summand
contributes `dim N^G`, then

  `dim (A ⊗ N)^G = c · dim N + dim (B ⊗ N)^G + dim N^G`. -/
theorem diagTensorInvariants_pullback_structure
    (p : ℕ) [Fact p.Prime] {G Q : Type} [Group G] [Group Q] [Fintype Q] [DecidableEq Q]
    (φ : G →* Q) (hφ : Function.Surjective φ)
    [DistribMulAction G (MonoidAlgebra (ZMod p) Q)]
    [SMulCommClass G (ZMod p) (MonoidAlgebra (ZMod p) Q)]
    (hact : ∀ (g : G) (a : MonoidAlgebra (ZMod p) Q), g • a = (φ g) • a)
    (c : ℕ) {A B D N : Type}
    [AddCommGroup A] [Module (ZMod p) A] [DistribMulAction G A] [SMulCommClass G (ZMod p) A]
    [AddCommGroup B] [Module (ZMod p) B] [DistribMulAction G B] [SMulCommClass G (ZMod p) B]
    [AddCommGroup D] [Module (ZMod p) D] [DistribMulAction G D] [SMulCommClass G (ZMod p) D]
    [AddCommGroup N] [Module (ZMod p) N] [DistribMulAction G N] [SMulCommClass G (ZMod p) N]
    [Finite A] [Finite B] [Finite D] [Finite N]
    (e : A ≃ₗ[ZMod p] ((Fin c → MonoidAlgebra (ZMod p) Q) × B × D))
    (he : ∀ (g : G) (x : A), e (g • x) = g • e x)
    (hkerN : ∀ (g : G), φ g = 1 → ∀ n : N, g • n = n)
    (hD : Module.finrank (ZMod p)
        ↥(Work.SSGRoute.PTCore.invariantsSubmodule G (ZMod p)
          (TensorProduct (ZMod p) D N)) =
      Module.finrank (ZMod p) ↥(Work.SSGRoute.PTCore.invariantsSubmodule G (ZMod p) N)) :
    Module.finrank (ZMod p)
        ↥(Work.SSGRoute.PTCore.invariantsSubmodule G (ZMod p)
          (TensorProduct (ZMod p) A N)) =
      c * Module.finrank (ZMod p) N +
        Module.finrank (ZMod p)
          ↥(Work.SSGRoute.PTCore.invariantsSubmodule G (ZMod p)
            (TensorProduct (ZMod p) B N)) +
        Module.finrank (ZMod p)
          ↥(Work.SSGRoute.PTCore.invariantsSubmodule G (ZMod p) N) := by
  haveI : Fintype (MonoidAlgebra (ZMod p) Q) :=
    Fintype.ofEquiv (Q →₀ ZMod p)
      (MonoidAlgebra.coeffLinearEquiv (ZMod p) (S := ZMod p) (M := Q)).symm.toEquiv
  have h₁ := diagTensorInvariants_eq_of_equiv (N := N) e he
  rw [h₁]
  rw [diagTensorInvariants_prod (Fin c → MonoidAlgebra (ZMod p) Q) (B × D) N]
  rw [diagTensorInvariants_prod B D N]
  rw [diagTensorInvariants_pow c (MonoidAlgebra (ZMod p) Q) N,
    diagTensorInvariants_pullback_regular p φ hφ hact N hkerN, hD]
  ring

end PullbackStructure

end Work.SSGRoute.E7Fin
