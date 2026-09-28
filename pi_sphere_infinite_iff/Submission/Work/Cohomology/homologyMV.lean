import Mathlib
import Submission.Work.Cohomology.MVSequence
import Submission.Work.Cohomology.mvLeft_zero_injective

/-!
# Extracting the homology of a two-cover from the Mayer–Vietoris sequence

Let `X` be a topological space and `U, V ⊆ X` open subsets with `U ∪ V = X`.  The
Mayer–Vietoris long exact sequence of `Submission/Work/Cohomology/MVSequence.lean` is

`⋯ ⟶ H_{n+1}(U ∩ V) → H_{n+1}(U) ⊕ H_{n+1}(V) → H_{n+1}(C^{U,V}) → H_n(U ∩ V) → ⋯`

where the third term is the homology of the small chains, isomorphic to `H_n(X)`
(`smallIso`).  This file records the elementary consequences of exactness that are used to read
off the homology of `X` from the homology of the pieces:

* `mvH_left_mono`, `mvH_right_mono`, `mvH_right_epi` — (co)monomorphisms of the maps of the
  sequence coming from vanishing of `H_*(U ∩ V)`;
* `mvH_delta_mono`, `mvH_delta_epi` — the connecting map is mono/epi when the corresponding
  `H_*(U) ⊕ H_*(V)` vanish;
* `mvH_isZero` — `H_n(X) = 0` for `n ≥ 1` when `H_n(U) = H_n(V) = H_{n-1}(U ∩ V) = 0`;
* `mvH_one_isZero` — `H_1(X) = 0` when `H_1(U) = H_1(V) = 0` and `H_0(U ∩ V) → H_0(U) ⊕ H_0(V)`
  is injective.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false

open CategoryTheory AlgebraicTopology Limits

namespace Work.Cohomology

noncomputable section

variable {X : TopCat}

/-- If `H_n(U ∩ V) = 0` then `H_n(U ∩ V) → H_n(U) ⊞ H_n(V)` is injective. -/
theorem mvH_left_mono (U V : Set X) (n : ℕ) (h : IsZero (HInter U V n)) :
    Mono (HomologicalComplex.homologyMap (mvLeft U V) n) := by
  have hf : mvδ U V n = 0 := IsZero.eq_zero_of_tgt h _
  exact (ShortComplex.exact_iff_mono _ hf).mp (mv_H_exact₁ U V n)

/-- If `H_n(U ∩ V) = 0` then `H_n(U) ⊞ H_n(V) → H_n(C^{U,V})` is injective. -/
theorem mvH_right_mono (U V : Set X) (n : ℕ) (h : IsZero (HInter U V n)) :
    Mono (HomologicalComplex.homologyMap (mvRight U V) n) := by
  have hf : HomologicalComplex.homologyMap (mvLeft U V) n = 0 :=
    IsZero.eq_zero_of_src h _
  exact (ShortComplex.exact_iff_mono _ hf).mp (mv_H_exact₂ U V n)

/-- If `H_n(U ∩ V) = 0` then `H_{n+1}(U) ⊞ H_{n+1}(V) → H_{n+1}(C^{U,V})` is surjective. -/
theorem mvH_right_epi (U V : Set X) (n : ℕ) (h : IsZero (HInter U V n)) :
    Epi (HomologicalComplex.homologyMap (mvRight U V) (n + 1)) := by
  have hg : mvδ U V n = 0 := IsZero.eq_zero_of_tgt h _
  exact (ShortComplex.exact_iff_epi _ hg).mp (mv_H_exact₃ U V n)

/-- If `H_{n+1}(U) ⊞ H_{n+1}(V) = 0` then the connecting map `H_{n+1}(C^{U,V}) → H_n(U ∩ V)` is
injective. -/
theorem mvH_delta_mono (U V : Set X) (n : ℕ) (h : IsZero (HBiprod U V (n + 1))) :
    Mono (mvδ U V n) := by
  have hf : HomologicalComplex.homologyMap (mvRight U V) (n + 1) = 0 :=
    IsZero.eq_zero_of_src h _
  exact (ShortComplex.exact_iff_mono _ hf).mp (mv_H_exact₃ U V n)

/-- If `H_n(U) ⊞ H_n(V) = 0` then the connecting map `H_{n+1}(C^{U,V}) → H_n(U ∩ V)` is
surjective. -/
theorem mvH_delta_epi (U V : Set X) (n : ℕ) (h : IsZero (HBiprod U V n)) :
    Epi (mvδ U V n) := by
  have hg : HomologicalComplex.homologyMap (mvLeft U V) n = 0 :=
    IsZero.eq_zero_of_tgt h _
  exact (ShortComplex.exact_iff_epi _ hg).mp (mv_H_exact₁ U V n)

/-- If `H_n(U)`, `H_n(V)` and `H_{n-1}(U ∩ V)` all vanish then so does `H_n(C^{U,V})`
(`n ≥ 1`). -/
theorem mvH_isZero (U V : Set X) (n : ℕ) (hn : 1 ≤ n)
    (hB : IsZero (HBiprod U V n)) (hA : IsZero (HInter U V (n - 1))) :
    IsZero (HSmall U V n) := by
  have hB' : IsZero (HBiprod U V ((n - 1) + 1)) := by rwa [Nat.sub_add_cancel hn]
  have hf : HomologicalComplex.homologyMap (mvRight U V) ((n - 1) + 1) = 0 :=
    IsZero.eq_zero_of_src hB' _
  haveI : Mono (mvδ U V (n - 1)) :=
    (ShortComplex.exact_iff_mono _ hf).mp (mv_H_exact₃ U V (n - 1))
  have hres : IsZero (HSmall U V ((n - 1) + 1)) := IsZero.of_mono (mvδ U V (n - 1)) hA
  rwa [Nat.sub_add_cancel hn] at hres

/-- If `H_1(U) = H_1(V) = 0` and `H_0(U ∩ V) → H_0(U) ⊞ H_0(V)` is injective, then
`H_1(C^{U,V}) = 0`. -/
theorem mvH_one_isZero (U V : Set X) (hB : IsZero (HBiprod U V 1))
    (hl : Mono (HomologicalComplex.homologyMap (mvLeft U V) 0)) :
    IsZero (HSmall U V 1) := by
  have hf : HomologicalComplex.homologyMap (mvRight U V) (0 + 1) = 0 :=
    IsZero.eq_zero_of_src hB _
  haveI : Mono (mvδ U V 0) :=
    (ShortComplex.exact_iff_mono _ hf).mp (mv_H_exact₃ U V 0)
  have hexact : (ShortComplex.mk (mvδ U V 0)
      (HomologicalComplex.homologyMap (mvLeft U V) 0) (mvδ_comp U V 0)).Exact :=
    mv_H_exact₁ U V 0
  have hrange : LinearMap.range (mvδ U V 0).hom
      = LinearMap.ker (HomologicalComplex.homologyMap (mvLeft U V) 0).hom :=
    (ShortComplex.moduleCat_exact_iff_range_eq_ker _).mp hexact
  have hker : LinearMap.ker (HomologicalComplex.homologyMap (mvLeft U V) 0).hom = ⊥ :=
    LinearMap.ker_eq_bot.mpr ((ModuleCat.mono_iff_injective _).mp hl)
  have hδ0 : mvδ U V 0 = 0 := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    have hx : (mvδ U V 0).hom x ∈ LinearMap.range (mvδ U V 0).hom := ⟨x, rfl⟩
    rw [hrange, hker] at hx
    simpa using hx
  rw [IsZero.iff_id_eq_zero]
  refine (cancel_mono (mvδ U V 0)).mp ?_
  rw [hδ0]
  simp

end

end Work.Cohomology
