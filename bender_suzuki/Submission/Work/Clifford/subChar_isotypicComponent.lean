import Mathlib
import Submission.Work.Clifford.ResSetup
import Submission.Work.Trace.pi_trace

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

noncomputable section

open Classical
open scoped MonoidAlgebra

namespace Work.Clifford

/-!
# `Work.Clifford.subChar_isotypicComponent`

Let `N ⊴ G` be a normal subgroup, `V : FDRep ℂ G`, and `S ≤ ResMod N V` a simple
`ℂ[N]`-submodule.  If the isotypic component `W = isotypicComponent ℂ[N] (ResMod N V) S`
is isomorphic, as a `ℂ[N]`-module, to `e` copies of `S`, then for every `n : N` the
character of `n` on `W` (the trace of the action of `n` on `W`) is `e` times its
character on `S`.

The mathematical content is that a `ℂ[N]`-linear isomorphism preserves traces
(`LinearMap.trace_conj'`), that on the direct power `Fin e → S` the action of `n` is
the componentwise action `pi (fun i => φ ∘ proj i)`, and that the trace of such a
componentwise endomorphism is `e` times the trace of `φ` (`trace_piMap_const`).
-/

/-! ### Auxiliary lemmas -/

/-- `Representation.ofModule'` acts by multiplication by `MonoidAlgebra.of ℂ G g`. -/
theorem ofModule'_apply_of_monoidAlgebra {G : Type*} [Group G] {M : Type*} [AddCommGroup M]
    [Module ℂ M] [Module ℂ[G] M] [IsScalarTower ℂ ℂ[G] M] (g : G) (v : M) :
    (Representation.ofModule' (k := ℂ) (G := G) M) g v = MonoidAlgebra.of ℂ G g • v := by
  show (MonoidAlgebra.lift ℂ (M →ₗ[ℂ] M) G).symm (Algebra.lsmul ℂ (B := ℂ) (M := M)) g v = _
  rw [MonoidAlgebra.lift_symm_apply, MonoidAlgebra.of_apply, Algebra.lsmul_apply]

/-- The trace of a componentwise ("block diagonal") endomorphism of a direct power
`ι → S` is `#ι` times the trace of the endomorphism `φ` of `S`. -/
theorem trace_piMap_const {k : Type*} [Field k] {ι S : Type*} [Fintype ι] [AddCommGroup S]
    [Module k S] [Module.Finite k S] [Module.Free k S] (φ : S →ₗ[k] S) :
    LinearMap.trace k (ι → S) (LinearMap.pi fun i => φ.comp (LinearMap.proj i)) =
      (Fintype.card ι : k) • LinearMap.trace k S φ := by
  classical
  have hdecomp : LinearMap.pi (fun i : ι => φ.comp (LinearMap.proj i))
      = ∑ i : ι, (LinearMap.single k (fun _ : ι => S) i).comp (φ.comp (LinearMap.proj i)) := by
    apply LinearMap.ext
    intro v
    apply funext
    intro j
    rw [LinearMap.pi_apply, LinearMap.sum_apply]
    simp only [LinearMap.comp_apply, LinearMap.single_apply, LinearMap.proj_apply]
    have h := congrFun (LinearMap.sum_single_apply (fun _ : ι => S) (fun i => φ (v i))) j
    simpa using h.symm
  rw [hdecomp, map_sum]
  have hterm : ∀ i : ι, LinearMap.trace k (ι → S)
      ((LinearMap.single k (fun _ : ι => S) i).comp (φ.comp (LinearMap.proj i)))
      = LinearMap.trace k S φ := by
    intro i
    rw [LinearMap.trace_comp_comm']
    rw [LinearMap.comp_assoc, LinearMap.proj_comp_single_same, LinearMap.comp_id]
  simp_rw [hterm]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, smul_eq_mul]

/-- The character `subChar V W n` of a `ℂ[N]`-submodule `W ≤ ResMod N V` is the trace of the
action of `n` on `W` given by multiplying by `MonoidAlgebra.of ℂ N n`. -/
theorem subChar_eq_trace_ofAct {G : Type*} [Group G] [Fintype G] {N : Subgroup G} [N.Normal]
    (V : FDRep ℂ G) (W : Submodule (MonoidAlgebra ℂ ↥N) (ResMod N V)) (n : N) :
    subChar V W n =
      LinearMap.trace ℂ ↥W ((Representation.ofModule' (k := ℂ) (G := ↥N) ↥W) n) := by
  rw [subChar_apply]
  congr 1
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  rw [subAct_apply, ofModule'_apply_of_monoidAlgebra, Submodule.coe_smul, of_smul]

/-! ### The main result -/

theorem subChar_isotypicComponent {G : Type*} [Group G] [Fintype G] {N : Subgroup G} [N.Normal]
    (V : FDRep ℂ G) (S : Submodule (MonoidAlgebra ℂ ↥N) (ResMod N V))
    [IsSimpleModule (MonoidAlgebra ℂ ↥N) ↥S] (e : ℕ)
    (hE : Nonempty (↥(isotypicComponent (MonoidAlgebra ℂ ↥N) (ResMod N V) ↥S) ≃ₗ[MonoidAlgebra ℂ ↥N]
      (Fin e → ↥S))) (n : N) :
    subChar V (isotypicComponent (MonoidAlgebra ℂ ↥N) (ResMod N V) ↥S) n
      = (e : ℂ) * subChar V S n := by
  classical
  obtain ⟨E⟩ := hE
  set W : Submodule (MonoidAlgebra ℂ ↥N) (ResMod N V) :=
    isotypicComponent (MonoidAlgebra ℂ ↥N) (ResMod N V) ↥S with hW
  -- `S` is a subspace of the finite dimensional space `ResMod N V`; provide finiteness over `ℂ`.
  haveI : Module.Finite ℂ ↥S :=
    FiniteDimensional.finiteDimensional_submodule (K := ℂ) (V := ResMod N V) (S.restrictScalars ℂ)
  rw [subChar_eq_trace_ofAct]
  -- transport the trace along the `ℂ[N]`-linear (hence `ℂ`-linear) isomorphism `E`
  rw [← LinearMap.trace_conj' (f := (Representation.ofModule' (k := ℂ) (G := ↥N) ↥W) n)
        (e := E.restrictScalars ℂ)]
  have hconj : (E.restrictScalars ℂ).conj ((Representation.ofModule' (k := ℂ) (G := ↥N) ↥W) n)
      = LinearMap.pi (fun i : Fin e =>
          ((Representation.ofModule' (k := ℂ) (G := ↥N) ↥S) n).comp (LinearMap.proj i)) := by
    apply LinearMap.ext
    intro y
    apply funext
    intro i
    rw [LinearEquiv.conj_apply_apply, LinearMap.pi_apply]
    change E ((Representation.ofModule' (k := ℂ) (G := ↥N) ↥W) n (E.symm y)) i
      = ((Representation.ofModule' (k := ℂ) (G := ↥N) ↥S) n) (y i)
    rw [ofModule'_apply_of_monoidAlgebra, E.map_smul, E.apply_symm_apply,
      ofModule'_apply_of_monoidAlgebra]
    rfl
  rw [hconj, trace_piMap_const (φ := (Representation.ofModule' (k := ℂ) (G := ↥N) ↥S) n)]
  rw [subChar_eq_trace_ofAct, Fintype.card_fin]
  rw [smul_eq_mul]

end Work.Clifford

-- The same statement, recorded at the namespace produced by the original file's doubled
-- `namespace Work.Clifford` header.
namespace Work.Clifford

namespace Work.Clifford

theorem subChar_isotypicComponent {G : Type*} [Group G] [Fintype G] {N : Subgroup G} [N.Normal]
    (V : FDRep ℂ G) (S : Submodule (MonoidAlgebra ℂ ↥N) (ResMod N V))
    [IsSimpleModule (MonoidAlgebra ℂ ↥N) ↥S] (e : ℕ)
    (hE : Nonempty (↥(isotypicComponent (MonoidAlgebra ℂ ↥N) (ResMod N V) ↥S) ≃ₗ[MonoidAlgebra ℂ ↥N]
      (Fin e → ↥S))) (n : N) :
    subChar V (isotypicComponent (MonoidAlgebra ℂ ↥N) (ResMod N V) ↥S) n
      = (e : ℂ) * subChar V S n :=
  _root_.Work.Clifford.subChar_isotypicComponent V S e hE n

end Work.Clifford

end Work.Clifford
