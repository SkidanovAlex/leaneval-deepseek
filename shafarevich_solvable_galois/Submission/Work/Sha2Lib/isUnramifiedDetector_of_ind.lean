import Mathlib
import Submission.Work.SSGRoute.Sha2Lib.detectorInterface
import Submission.Work.SSGRoute.Sha2Lib.detectsAt_of_coeff_surjection
import Submission.Work.Sha2Lib.ext_comp_mk0_ne_zero_of_surjective
import Submission.Work.Sha2Lib.indRes_counit_surjective
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.Sha2Lib

open CategoryTheory

set_option linter.style.haveILetI false

/-! ## Two facts about the induced module `Ind_N^G(A)`

They are proved in the abstract setting of a commutative ring `k`, a group `G` and a `k`-linear
`N`-representation `A`, where instance search for the `k`-module structure on the carrier of `A`
is unambiguous.  (In the application `k = Coeff = ULift ℤ` and the carrier of `A` also carries the
`ℤ`-module structure transported along `ULift`, so an *unpinned* `Module Coeff ↥A` search inside
`Representation.IndV` picks up a non-definitionally-equal instance; phrasing the lemmas generically
avoids this entirely.) -/

/-- **The exponent-`p` condition passes to the induced module.**

If a `k`-linear `N`-module `A` is killed by `p`, then so is `Ind_N^G(A)`: the scalar `p` can be
moved across the tensor product `k[G] ⊗[k] A` (`TensorProduct.smul_tmul`) onto the second factor,
where it kills everything, and the coinvariants quotient of `k[G] ⊗[k] A` is a quotient of that
tensor product. -/
private lemma ind_smul_eq_zero {k G : Type} [CommRing k] [Group G] (N : Subgroup G) (p : ℕ)
    (A : Rep.{0} k N) (hA : ∀ a : A, p • a = 0) :
    ∀ m : Rep.ind N.subtype A, p • m = 0 := by
  intro m
  show p • (m : Representation.IndV N.subtype A.ρ) = 0
  obtain ⟨t, rfl⟩ := Representation.Coinvariants.mk_surjective
    (Representation.tprod ((Representation.leftRegular k G).comp N.subtype) A.ρ) m
  have ht : (p : k) • t = 0 := by
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul x a =>
        rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul]
        have hpa : (p : k) • a = 0 := by
          rw [Nat.cast_smul_eq_nsmul]
          exact hA a
        rw [hpa, TensorProduct.tmul_zero]
    | add x y hx hy => rw [smul_add, hx, hy, add_zero]
  have hm : (p : k) •
      (Representation.Coinvariants.mk (Representation.tprod ((Representation.leftRegular
        k G).comp N.subtype) A.ρ) t) = 0 := by
    rw [← map_smul, ht, map_zero]
  rwa [Nat.cast_smul_eq_nsmul] at hm

/-- **Finiteness of the induced module.**

For a finite index subgroup `N` of a finite group `G` and a finite `k`-linear `N`-module `A`, the
induced module `Ind_N^G(A)` is finite.  Indeed `Rep.indCoindIso` identifies it with the coinduced
module `Coind_N^G(A)`, which is a submodule of the finite type `G → A`. -/
private lemma finite_ind {k G : Type} [CommRing k] [Group G] [Finite G] (N : Subgroup G)
    [N.FiniteIndex] (A : Rep.{0} k N) [Finite A] : Finite (Rep.ind N.subtype A) := by
  classical
  haveI : DecidableRel (QuotientGroup.rightRel N) := Classical.decRel _
  haveI hc : Finite ↥(Representation.coindV N.subtype A.ρ) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  haveI : Finite (Rep.coind N.subtype A) := hc
  refine Finite.of_injective
    (fun x : ↥(Rep.ind N.subtype A) => (Rep.indCoindIso A).hom.hom x) ?_
  haveI : Mono (Rep.indCoindIso A).hom := inferInstance
  exact (Rep.mono_iff_injective _).1 inferInstance

/-- **The unramified detector transfers from `Ind_N^G(res_N M)` to `M`, for _any_ subgroup `N`.**

`k ⊆ K` number fields with `K/k` finite Galois, `q` a place of `K`, `N ≤ Gal(K/k)` of finite index,
`M` a finite `p`-torsion `Gal(K/k)`-module.  If `Ind_N^{Gal(K/k)}(res_N M)` satisfies the unramified
detector (`IsUnramifiedDetector`), then so does `M`.

Assembly step §2.2 of the C6 route (`_lead_design/ssg_pt_design_1002/DESIGN.md`): detection on the
cover `Ind_N^Γ(res_N M)` transfers to `M` along the counit `ε : Ind_N^Γ (res_N M) ⟶ M` of the
adjunction `Ind_N^Γ ⊣ res_N`.

Proof skeleton (verified by reviewer 1 to elaborate; all three ingredients are proved on disk):

    let ε : M' ⟶ M := (Rep.indResAdjunction Coeff N.subtype).counit.app M
    have hc := Work.Sha2Lib.indRes_counit_surjective N M
    have hne := Work.Sha2Lib.ext_comp_mk0_ne_zero_of_surjective p D M M' hM hM' ε hc φ hφ
    exact Work.SSGRoute.Sha2Lib.detectsAt_of_coeff_surjection p k K Ω w q hwq M M' ε hc φ (h _ hne)

with `D = SSGRoute.PTExt.decompK (k := k) (K := K) w` and
`M' = Rep.ind N.subtype (Rep.res N.subtype M)`.  This *replaces* the unit/section argument used in
the `N = D_w` case (where the unit of the adjunction is a section of `res ε`): for general `N` the
counit is surjective but **not** split, so the pullback-nonvanishing brick is what makes the transfer
work.  With `N = decompK w` this subsumes the proved
`Work.SSGRoute.Sha2Lib.isUnramifiedDetector_of_induced`; with `N` = the normal closure of the inertia
at `q` it is the step consuming the dispatched `Work.Sha2Lib.unramifiedDetector_indNormal`.

**Caveat from both reviewers (this is the real work, do not under-budget it).**
`ext_comp_mk0_ne_zero_of_surjective` as on disk carries `[Finite M] [Finite M']`, and
`Finite (Rep.ind N.subtype (Rep.res N.subtype M))` is *not* found by `inferInstance` (Mathlib's
`IndV` is a quotient of a `TensorProduct`, and `MonoidAlgebra ℤ N` is infinite).  It is true under
`[N.FiniteIndex]` — use `Rep.indCoindIso` and `finite_coind`, or the explicit
`Ind ≅ (res_N M)^{[G:N]}` — and the exponent-`p` fact for `M'` is pointwise (hence immediate).  You
may also simply prove the same transfer with a local restatement of the pullback brick that drops the
two `[Finite]` hypotheses (reviewers of that brick confirmed they are unused). -/
theorem isUnramifiedDetector_of_ind (p : ℕ) [Fact p.Prime] (k K : Type) [Field k] [NumberField k]
    [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
    (w : NK.GlobalCFT.Place K)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hwq : w = NK.GlobalCFT.Place.ofFinite q)
    (N : Subgroup (K ≃ₐ[k] K)) [N.FiniteIndex]
    (M : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) [Finite M] (hM : ∀ m : M, p • m = 0)
    (h : Work.SSGRoute.Sha2Lib.IsUnramifiedDetector p k K Ω w q hwq
      (Rep.ind N.subtype (Rep.res N.subtype M))) :
    Work.SSGRoute.Sha2Lib.IsUnramifiedDetector p k K Ω w q hwq M := by
  intro φ hφ
  haveI : Finite (K ≃ₐ[k] K) := inferInstance
  -- The cover of the detector: `M' = Ind_N^{Gal(K/k)}(res_N M)`.
  let M' : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K) := Rep.ind N.subtype (Rep.res N.subtype M)
  haveI hM'fin : Finite M' := finite_ind (G := K ≃ₐ[k] K) N (Rep.res N.subtype M)
  have hM' : ∀ m : M', p • m = 0 :=
    ind_smul_eq_zero (G := K ≃ₐ[k] K) N p (Rep.res N.subtype M) hM
  -- The counit `ε : M' ⟶ M` of the adjunction `Ind_N^G ⊣ res_N` is surjective.
  refine Work.SSGRoute.Sha2Lib.detectsAt_of_coeff_surjection p k K Ω w q hwq M M'
    ((Rep.indResAdjunction SSGRoute.PTExt.Coeff N.subtype).counit.app M)
    (indRes_counit_surjective N M) φ ?_
  -- Push `φ` forward along the (surjective) counit and apply the detector for the cover.
  exact h _ (ext_comp_mk0_ne_zero_of_surjective p
    (SSGRoute.PTExt.decompK (k := k) (K := K) w) M M' hM hM'
    ((Rep.indResAdjunction SSGRoute.PTExt.Coeff N.subtype).counit.app M)
    (indRes_counit_surjective N M) φ hφ)

end Work.Sha2Lib
