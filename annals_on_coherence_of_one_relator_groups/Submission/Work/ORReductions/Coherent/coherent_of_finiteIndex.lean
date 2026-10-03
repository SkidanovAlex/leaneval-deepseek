import Mathlib
import Submission.Work.ORReductions.Basic
import Submission.Work.ORReductions.SubgroupAlg
import Submission.Work.ORReductions.Coherent.FiniteIndexSetup
import Submission.Work.ORReductions.Coherent.ker_fg_of_coherent_fintype
import Submission.Work.ORReductions.Coherent.sum_coord_mul_repr

set_option autoImplicit false

namespace Work.ORReductions.Coherent

open MonoidAlgebra

/-
# Coherence of `K[G]` for a subgroup `H ≤ G` of finite index

If `K[H]` is coherent, then so is `K[G]`.  The point is that `K[G]` is a finitely generated
free left module over `K[H]` (a transversal of the right cosets `H · cosetRep H q` is a basis,
see `FiniteIndexSetup`): hence

* for a `K[G]`-linear map `g` between finite free `K[G]`-modules, the kernel `ker g`, being
  also `K[H]`-linear and a submodule of a finitely generated free `K[H]`-module, is a finitely
  generated `K[H]`-module by Chase's criterion (`submodule_fg_ker_of_coherent`, in the
  `(ι → R)`-shaped form `ker_fg_of_coherent_fintype`);
* a finitely generated `K[H]`-submodule of `K[G]^n` is a fortiori finitely generated as a
  `K[G]`-module, so `ker g` is a finitely generated `K[G]`-module.

Thus every finitely generated left ideal of `K[G]` is finitely presented.
-/

theorem coherent_of_finiteIndex (G : Type*) [Group G] (K : Type*) [Field K]
    (H : Subgroup G) (hH : H.FiniteIndex) (h : Ring.Coherent (MonoidAlgebra K H)) :
    Ring.Coherent (MonoidAlgebra K G) := by
  classical
  intro I hI
  haveI : H.FiniteIndex := hH
  letI : Fintype (G ⧸ H) := H.fintypeQuotientOfFiniteIndex
  let φ : MonoidAlgebra K H →+* MonoidAlgebra K G := subgroupAlgMap H K
  letI : Module (MonoidAlgebra K H) (MonoidAlgebra K G) := Module.compHom (MonoidAlgebra K G) φ
  -- The decomposition map `K[H]^{(G ⧸ H)} → K[G]`.
  let Ψ : ((G ⧸ H) → MonoidAlgebra K H) →ₗ[MonoidAlgebra K H] MonoidAlgebra K G :=
    { toFun := fun a => ∑ q, φ (a q) * MonoidAlgebra.single (cosetRep H q) 1
      map_add' := by
        intro a b
        simp only [Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]
      map_smul' := by
        intro r a
        show (∑ q, φ (r * a q) * MonoidAlgebra.single (cosetRep H q) 1)
          = φ r * (∑ q, φ (a q) * MonoidAlgebra.single (cosetRep H q) 1)
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun q _ => by rw [map_mul, mul_assoc] }
  -- `coord` is `K[H]`-linear, and the decomposition is injective.
  have hS1 : ∀ (a : G ⧸ H → MonoidAlgebra K H) (q : G ⧸ H), coord H K q (Ψ a) = a q := by
    intro a q
    have hsingle : ∀ (h : H) (c : K) (x : MonoidAlgebra K G),
        coord H K q (MonoidAlgebra.single (h : G) c * x)
          = MonoidAlgebra.single h c * coord H K q x := by
      intro h c x
      ext h'
      rw [coeff_coord, MonoidAlgebra.coeff_single_mul_apply, MonoidAlgebra.coeff_single_mul_apply,
        coeff_coord]
      congr 2
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    have hmul : ∀ (r : MonoidAlgebra K H) (x : MonoidAlgebra K G),
        coord H K q (subgroupAlgMap H K r * x) = r * coord H K q x := by
      intro r x
      have hmain : ∀ (s : H →₀ K),
          coord H K q (subgroupAlgMap H K (MonoidAlgebra.ofCoeff s) * x)
            = MonoidAlgebra.ofCoeff s * coord H K q x := by
        intro s
        refine Finsupp.induction_linear s ?_ ?_ ?_
        · simp
        · intro f g hf hg
          simp only [MonoidAlgebra.ofCoeff_add, map_add, add_mul, coord_add, hf, hg]
        · intro h c
          show coord H K q (subgroupAlgMap H K (MonoidAlgebra.single h c) * x)
            = MonoidAlgebra.single h c * coord H K q x
          rw [subgroupAlgMap, MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapDomain_single]
          exact hsingle h c x
      simpa only [MonoidAlgebra.ofCoeff_coeff] using hmain r.coeff
    have h1 : coord H K q (Ψ a) = ∑ q' : G ⧸ H, coord H K q
        (subgroupAlgMap H K (a q') * MonoidAlgebra.single (cosetRep H q') 1) :=
      map_sum (coordLM H K q) _ Finset.univ
    rw [h1]
    have h2 : ∀ q' : G ⧸ H, coord H K q (subgroupAlgMap H K (a q')
        * MonoidAlgebra.single (cosetRep H q') 1) = if q' = q then a q' else 0 := by
      intro q'
      rw [hmul (a q') (MonoidAlgebra.single (cosetRep H q') 1)]
      by_cases hq : q' = q
      · rw [hq, if_pos rfl]
        have hc : coord H K q (MonoidAlgebra.single (cosetRep H q) 1) = 1 := by
          have h := coord_single_mul_repr H K q (1 : H) (1 : K)
          rw [show ((1 : H) : G) * cosetRep H q = cosetRep H q from by simp,
            ← MonoidAlgebra.one_def] at h
          exact h
        rw [hc, mul_one]
      · have hc : coord H K q (MonoidAlgebra.single (cosetRep H q') 1) = 0 := by
          have h := coord_single_mul_repr_eq_zero H K (q := q) (q' := q')
            (fun hh : q = q' => hq hh.symm) (1 : H) (1 : K)
          rwa [show ((1 : H) : G) * cosetRep H q' = cosetRep H q' from by simp] at h
        rw [hc, mul_zero, if_neg hq]
    rw [Finset.sum_congr rfl (fun q' _ => h2 q')]
    rw [Finset.sum_eq_single q (fun b _ hb => if_neg hb) (fun h => absurd (Finset.mem_univ q) h),
      if_pos rfl]
  have hS3 : ∀ x : MonoidAlgebra K G, Ψ (fun q => coord H K q x) = x :=
    fun x => sum_coord_mul_repr G K H x
  have hΨinj : Function.Injective Ψ := by
    intro a b hab
    funext q
    have h0 : Ψ (a - b) = 0 := by rw [map_sub, hab, sub_self]
    have h1 : (a - b) q = 0 := by
      have h2 := hS1 (a - b) q
      rw [h0] at h2
      simpa using h2.symm
    have h3 : a q - b q = 0 := by simpa using h1
    exact sub_eq_zero.mp h3
  have hΨsurj : Function.Surjective Ψ := fun x => ⟨fun q => coord H K q x, hS3 x⟩
  let e : MonoidAlgebra K G ≃ₗ[MonoidAlgebra K H] ((G ⧸ H) → MonoidAlgebra K H) :=
    (LinearEquiv.ofBijective Ψ ⟨hΨinj, hΨsurj⟩).symm
  haveI hfin : Module.Finite (MonoidAlgebra K H) (MonoidAlgebra K G) :=
    Module.Finite.of_surjective Ψ hΨsurj
  -- A f.g. left ideal of `K[G]` is the range of a linear map out of a finite free module.
  obtain ⟨m, g, hg⟩ :=
    (Submodule.fg_iff_exists_fin_linearMap (MonoidAlgebra K G) (MonoidAlgebra K G)).mp hI
  -- `g`, viewed as a `K[H]`-linear map.
  let gR : (Fin m → MonoidAlgebra K G) →ₗ[MonoidAlgebra K H] MonoidAlgebra K G :=
    { toFun := g
      map_add' := g.map_add
      map_smul' := by
        intro r c
        show g (r • c) = r • g c
        rw [show (r • c : Fin m → MonoidAlgebra K G) = (φ r) • c from rfl, map_smul]
        rfl }
  -- Chase: the kernel of `g`, viewed over `K[H]`, is finitely generated.
  have hkerR : (LinearMap.ker (e.toLinearMap ∘ₗ gR)).FG :=
    ker_fg_of_coherent_fintype (MonoidAlgebra K H) h (e.toLinearMap ∘ₗ gR)
  have hkerR' : (LinearMap.ker gR).FG := by
    have h2 : LinearMap.ker (e.toLinearMap ∘ₗ gR) = LinearMap.ker gR := by
      rw [LinearMap.ker_comp, LinearEquiv.ker, Submodule.comap_bot]
    rwa [h2] at hkerR
  -- Transfer: a `K[H]`-finitely generated submodule is `K[G]`-finitely generated.
  have hker : (LinearMap.ker g).FG := by
    obtain ⟨s, hs⟩ := hkerR'
    refine ⟨s, ?_⟩
    refine le_antisymm ?_ ?_
    · refine Submodule.span_le.mpr ?_
      intro x hx
      have h1 : x ∈ LinearMap.ker gR := by rw [← hs]; exact Submodule.subset_span hx
      exact h1
    · have hle : ∀ y ∈ Submodule.span (MonoidAlgebra K H)
            (↑s : Set (Fin m → MonoidAlgebra K G)),
          y ∈ Submodule.span (MonoidAlgebra K G) (↑s : Set (Fin m → MonoidAlgebra K G)) := by
        intro y hy
        exact Submodule.span_induction
          (p := fun z _ => z ∈ Submodule.span (MonoidAlgebra K G)
            (↑s : Set (Fin m → MonoidAlgebra K G)))
          (fun z hz => Submodule.subset_span hz) (Submodule.zero_mem _)
          (fun z w _ _ ihz ihw => Submodule.add_mem _ ihz ihw)
          (fun r z _ ihz => by
            rw [show (r • z : Fin m → MonoidAlgebra K G) = (φ r) • z from rfl]
            exact Submodule.smul_mem _ (φ r) ihz) hy
      intro x hx
      have h2 : x ∈ Submodule.span (MonoidAlgebra K H) (↑s : Set (Fin m → MonoidAlgebra K G)) := by
        rw [hs]; exact hx
      exact hle x h2
  -- Conclude: `I` is finitely presented over `K[G]`.
  have hkerg : (LinearMap.ker g.rangeRestrict).FG := by
    rw [LinearMap.ker_rangeRestrict]; exact hker
  have hfp : Module.FinitePresentation (MonoidAlgebra K G) (LinearMap.range g) :=
    (Module.FinitePresentation.fg_ker_iff g.rangeRestrict (LinearMap.surjective_rangeRestrict g)).mp
      hkerg
  rw [hg] at hfp
  exact hfp

end Work.ORReductions.Coherent
