import Mathlib
import Submission.Work.SSGRoute.LTDDefs.Basic
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.kummerBase_euler_h3loc
import Submission.Work.SSGRoute.LTDDefs.H3locEquivH3
import Submission.Work.SSGRoute.LTDDefs.DecompAction
import Submission.Work.SSGRoute.HS.Setup
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false

/-!
# `H³` of the decomposition group at a finite place: the reduction to the standard model,
and the precise gap

The requested statement

`∀ M [..], Subsingleton (H3loc p k Ω K M (decomp k A))`

is, by the model bridge `LTDDefs.H3locEquivH3`, *exactly* the vanishing of the third
continuous cohomology `H³(D_A, M)` of the decomposition group `D_A = decomp k A` of a finite
place `A` of `Ω` over `k`, with coefficients in a finite `𝔽_p[Gal(K/k)]`-module `M`
(`D_A ≅ G_{k_v}` for the completion `k_v` of `k` at the place below `A`).

## Why the statement is true

The classical theorem behind it is that the absolute Galois group of a non-archimedean local
field has `p`-cohomological dimension `≤ 2` for every prime `p`
(Serre, *Cohomologie galoisienne*, II §5; Neukirch–Schmidt–Wingberg, *Cohomology of Number
Fields*, 7.1.8): a finite place has no `H³`.  Equivalently, with `M` finite of exponent `p`
and `D_A^{pro-p}` the maximal pro-`p` quotient (equivalently the `p`-Sylow subgroup) of
`D_A ≅ G_{k_v}`:

* if `p` is a unit at `A` (residue characteristic `≠ p`), then the wild inertia is
  pro-prime-to-`p`, `D_A = I ⋊ Ẑ` and `cd_p(D_A) = 1`;
* if `p` is the residue characteristic, then `cd_p(D_A) = 2`: the maximal pro-`p` quotient
  `G_{k_v}^{pro-p}` is *free* pro-`p` of rank `[k_v : ℚ_p] + 1` when `ζ_p ∉ k_v`
  (Shafarevich, *Dokl. Akad. Nauk SSSR* 128 (1959); Serre, *Séminaire Bourbaki* 252 (1963),
  Thm. 4.1) and a *Demushkin* group when `ζ_p ∈ k_v` (Serre, *ibid.*, Thm. 4.2; Labute,
  *Canad. J. Math.* 19 (1967)), and in both cases the `p`-Sylow subgroup of `D_A ≅ G_{k_v}`
  has cohomological dimension `2` (Serre, *Cohomologie galoisienne*, II §5.3).

One subtlety worth recording: the `p`-Sylow subgroup of `G_{k_v}` is *strictly larger* than the
maximal pro-`p` quotient `G_{k_v}^{pro-p}` — for `κ = ℚ_p` with `p` odd, `G_{ℚ_p}^{pro-p}` is
free of rank `2` (hence `H²(-, 𝔽_p) = 0`), while `H²(G_{ℚ_p}, μ_p) ≅ Br(ℚ_p)[p] ≅ ℤ/p ≠ 0`.
So a proof cannot replace `D_A` by `G_{k_v}^{pro-p}`; the structure of the *Sylow* subgroup is
what is needed, and that is exactly the Demushkin input.

## Why it cannot be proved in this repository as it stands

The statement is one of the *deep arithmetic inputs* of the local-Tate-duality lane, not a
lemma derivable from what is on disk: the project's own status note
`Submission/Work/SSGRoute/STATUS_atom_recipes.md` §2 records this node ("still open ... Its
proof is the Demushkin theory (`Work.LocalFields.DemushkinProPStructure` is only an input
`Prop`), not in the tree"), and `kummerBase_euler_residueChar.lean` says the same.  Concretely,
what is missing is

* local class field theory for `k_v` (the invariant map `Br(k_v) ≅ ℚ/ℤ`, which is an *unproved
  input* in this workspace: `Work.SSGRoute.PT.Milne18AtZero`, `local_tate_duality_02`,
  `local_tate_duality_euler`), and
* the structure theory of pro-`p` groups (presentations, relation rank, `cd` detected by
  `H^n(-, 𝔽_p)`), of which the workspace has none.

In particular the statement is **not** a consequence of the other inputs the lane uses: local
Tate duality in degrees `0, 1, 2` does not give vanishing in degree `3` (the degree-`3` case of
local duality *is* the `cd_p ≤ 2` statement).  For a pro-`p` group of cohomological dimension
`2`, dimension shifting alone cannot produce `H³ = 0` either, and passing to the maximal pro-`p`
quotient is *not* a formal reduction for non-trivial coefficient modules: the kernel of
`G ↠ G^{pro-p}` need not be pro-prime-to-`p` (for `G_{ℚ_p}`, `p` odd, its abelianisation has a
quotient of order `p - 1`, since `[ℚ_p^{pro-p}(ζ_p) : ℚ_p^{pro-p}] = p - 1`), and indeed
`H²(G_{ℚ_p}, μ_p) ≅ Br(ℚ_p)[p] ≅ ℤ/p ≠ 0` while `G_{ℚ_p}^{pro-p}` is *free* pro-`p` of rank 2.

## What is proved here (sorry-free)

Two reduction lemmas that make the target a *single* statement in the standard model, and which
the eventual proof (once the arithmetic input is in place) can use directly:

* `subsingleton_h3loc_iff_subsingleton_H3` — for a *closed* subgroup `H ≤ G_k` with an action of
  `↥H` on `M` compatible with `res k K`, the model `H3loc` is subsingleton iff the standard
  continuous-cohomology model `H³(↥H, M)` is;
* `h3loc_decomp_subsingleton_of_H3` — the target itself follows from the corresponding statement
  for `Work.SSGRoute.H3` at `D_A` (the form in which the input is consumed by
  `kummerBase_euler_assembly`, `kummerBase_euler_assembly.lean` lines 132–136).

The two regimes of the arithmetic input are independent.  The *tame* one (`p` a unit at `A`) is
within reach of the machinery already on disk (`InertiaDefs`, `inertiaStructureOfFinPlace_inf`
giving `D_A = I ⋊ Ẑ` with `H²(I, M) = 0` for every finite `M`, `LTDDefs/Herbrand`,
`H2loc_twoRow`) together with the Hochschild–Serre bookkeeping in degree `3`; the
*residue-characteristic* one is the Demushkin input and is not available.
-/

namespace Work.SSGRoute.PTCore

open Classical

noncomputable section

/-- **The model bridge, in `Subsingleton` form.**

For a closed subgroup `H ≤ G_k = Ω ≃ₐ[k] Ω` and an action of `↥H` on a finite
`𝔽_p[Gal(K/k)]`-module `M` compatible with the restriction `res k K` (the compatibility that
holds definitionally for the canonical action `decompDistribMulAction` on a decomposition
group), the locally constant model `H3loc` of `kummerBase_euler_h3loc.lean` is a subsingleton
if and only if the standard continuous-cohomology model `H³(↥H, M)` of
`kummerBase_euler_h3_absKummer.lean` is.

This is a transport of `LTDDefs.H3locEquivH3` (the proved additive equivalence
`H3loc ≃+ H³`) along `Subsingleton`. -/
theorem subsingleton_h3loc_iff_subsingleton_H3
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (H : Subgroup (Ω ≃ₐ[k] Ω)) [DistribMulAction ↥H M]
    (hH : IsClosed (H : Set (Ω ≃ₐ[k] Ω)))
    (hcompat : ∀ (h : ↥H) (m : M), h • m = SSGRoute.res k K (h : Ω ≃ₐ[k] Ω) • m) :
    Subsingleton (Work.SSGRoute.H3loc p k Ω K M H) ↔
      Subsingleton (Work.SSGRoute.H3 (M := M) ↥H) := by
  obtain ⟨e⟩ := Work.SSGRoute.LTDDefs.H3locEquivH3 p k Ω K M H hH hcompat
  constructor
  · intro hsub
    exact ⟨fun a b => e.symm.injective (hsub.elim (e.symm a) (e.symm b))⟩
  · intro hsub
    exact ⟨fun a b => e.injective (hsub.elim (e a) (e b))⟩

/-- **The target, reduced to the standard model at the decomposition group.**

If the third continuous cohomology of `D_A = decomp k A` vanishes on every finite
`𝔽_p[Gal(K/k)]`-module `M` (the form of the arithmetic input consumed by
`kummerBase_euler_assembly`), then `H3loc` is a subsingleton, i.e. the requested statement
holds.  The action of `↥(decomp k A)` on `M` is the canonical one through `res k K`
(`decompDistribMulAction`), for which the compatibility hypothesis of the model bridge holds
definitionally (`decomp_smul_eq_res`). -/
theorem h3loc_decomp_subsingleton_of_H3
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (h : ∀ (M : Type) [AddCommGroup M] [Module (ZMod p) M]
      [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
      [DistribMulAction ↥(SSGRoute.decomp k A) M],
      Subsingleton (Work.SSGRoute.H3 (M := M) ↥(SSGRoute.decomp k A))) :
    ∀ (M : Type) [AddCommGroup M] [Module (ZMod p) M]
      [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M],
      Subsingleton (Work.SSGRoute.H3loc p k Ω K M (SSGRoute.decomp k A)) := by
  intro M _ _ _ _ _
  letI : DistribMulAction ↥(SSGRoute.decomp k A) M :=
    Work.SSGRoute.decompDistribMulAction K M A
  have hcompat : ∀ (h : ↥(SSGRoute.decomp k A)) (m : M),
      h • m = SSGRoute.res k K (h : Ω ≃ₐ[k] Ω) • m :=
    fun h m => Work.SSGRoute.decomp_smul_eq_res K M A h m
  have hH : IsClosed ((SSGRoute.decomp k A : Subgroup (Ω ≃ₐ[k] Ω)) : Set (Ω ≃ₐ[k] Ω)) :=
    Work.SSGRoute.HS.isClosed_decomp (k := k) (Ω := Ω) A
  exact (subsingleton_h3loc_iff_subsingleton_H3 p k Ω K M (SSGRoute.decomp k A)
    hH hcompat).mpr (h M)

/-- **The target from its two regimes.**

It suffices to know the vanishing at places at which `p` is a *unit* and at places at which `p`
is the *residue characteristic*.  The first regime is within reach of the workspace: the
inertia/Frobenius decomposition `D_A = I ⋊ Ẑ` with `H²(I, M) = 0`
(`Work.SSGRoute.inertiaStructureOfFinPlace_zhat`) shows `cd_p(D_A) ≤ 1` there, hence `H³ = 0`;
that case is `PTCore.h3loc_decomp_subsingleton_of_unit`.  The second regime is the Demushkin /
local-class-field-theory input (`cd_p(G_{k_v}) = 2`) and is *not* available — see the module
docstring. -/
theorem h3loc_decomp_subsingleton_of_cases
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (h_unit : ¬ A.valuation ((p : ℚ) : Ω) < 1 →
      ∀ (M : Type) [AddCommGroup M] [Module (ZMod p) M]
        [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M],
        Subsingleton (Work.SSGRoute.H3loc p k Ω K M (SSGRoute.decomp k A)))
    (h_res : A.valuation ((p : ℚ) : Ω) < 1 →
      ∀ (M : Type) [AddCommGroup M] [Module (ZMod p) M]
        [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M],
        Subsingleton (Work.SSGRoute.H3loc p k Ω K M (SSGRoute.decomp k A))) :
    ∀ (M : Type) [AddCommGroup M] [Module (ZMod p) M]
      [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M],
      Subsingleton (Work.SSGRoute.H3loc p k Ω K M (SSGRoute.decomp k A)) := by
  intro M _ _ _ _ _
  by_cases hv : A.valuation ((p : ℚ) : Ω) < 1
  · exact h_res hv M
  · exact h_unit hv M

/-- **`H³` of the decomposition group at a finite place vanishes on finite coefficient
modules** (`cd_p(G_{k_v}) ≤ 2`; Serre, *Cohomologie galoisienne*, II §5;
Neukirch–Schmidt–Wingberg 7.1.8) — in the locally constant model `H3loc` of
`kummerBase_euler_h3loc.lean`.

This is the `h3` input of `Work.SSGRoute.kummerBase_euler_of_inputs` (Milne, *ADT*, I.2.8):
without it the long exact sequence of a short exact sequence of coefficient modules does not
terminate in degree `3`, so the local Euler characteristic cannot be assembled.  See the module
docstring above for the mathematics of the statement and for the precise reason why it is not
derivable from the material on disk (it needs the Demushkin / local-class-field-theory input). -/
theorem h3loc_decomp_subsingleton
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) :
    ∀ (M : Type) [AddCommGroup M] [Module (ZMod p) M]
      [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M],
      Subsingleton (Work.SSGRoute.H3loc p k Ω K M (SSGRoute.decomp k A)) := by
  sorry

end

end Work.SSGRoute.PTCore
