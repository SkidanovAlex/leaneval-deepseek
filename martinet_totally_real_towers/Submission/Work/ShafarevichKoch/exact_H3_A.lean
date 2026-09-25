import Mathlib
import Submission.Work.ShafarevichKoch.Cohomology3Map

/-!
# Exactness of the long exact sequence at `H³(G,A)`

For a short exact sequence `0 → A → B → C → 0` of discrete `G`-modules (`CoeffSES`) and a map
`δ : H²(G,C) →+ H³(G,A)` which is computed on representatives by the connecting construction --
i.e. for every `2`-cocycle `z` with values in `C` and *every* `2`-cochain `u` in `B` lifting it
(`g ∘ u = z`), there is a `3`-cocycle `w` in `A` with `H3.mk w = δ z` and `f ∘ w = d²u`
(the hypothesis `hδ`) -- the induced sequence

`H²(G,C) --δ--> H³(G,A) --H³(f)--> H³(G,B)`

is exact at `H³(G,A)`: a class `x` dies under the coefficient map induced by `f` if and only if
it is the connecting image of a class in `H²(G,C)`.

The proof is the degree-`3` analogue of `Work.ConCohomology.exact_H2_A`.

* **`im δ ⊆ ker H³(f)`**: for `z : Z²(G,C)` take the canonical lift
  `u p = S.sect (z p)` of `z` along any set-theoretic section of `g`; the connecting cocycle `w`
  supplied by `hδ` satisfies `f ∘ w = d²u`, so the cochain `f ∘ w` is a coboundary, i.e.
  `H³(f)(δ z) = 0`.

* **`ker H³(f) ⊆ im δ`**: given a `3`-cocycle `w` in `A` whose image under `f` lies in
  `B³ = im d²`, choose `u` with `d²u = f ∘ w`.  Then `z = g ∘ u` is a `2`-cocycle (because
  `d²(g ∘ u) = g (d²u) = g (f ∘ w) = 0`) and `u` lifts `z`, so `hδ` produces `w'` with
  `H3.mk w' = δ(z)` and `f ∘ w' = d²u = f ∘ w`; injectivity of `f` gives `w' = w`, hence
  `x = H3.mk w = δ(z)`.

## Main declaration

* `Work.ShafarevichKoch.exact_H3_A`.
-/

open scoped Classical

noncomputable section

namespace Work.ShafarevichKoch

open Work.ConCohomology

theorem exact_H3_A {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [DistribMulAction G A] [DistribMulAction G B] [DistribMulAction G C]
    [Work.ConCohomology.IsDiscreteGModule G A] [Work.ConCohomology.IsDiscreteGModule G B]
    [Work.ConCohomology.IsDiscreteGModule G C]
    (S : Work.ConCohomology.CoeffSES G A B C)
    (δ : Work.ConCohomology.H2 G C →+ Work.ShafarevichKoch.H3 G A)
    (hδ : ∀ (z : Work.ConCohomology.Z2 G C) (u : Work.ConCohomology.Cochain2 G B),
      (∀ p : G × G, S.g (u p) = (z : Work.ConCohomology.Cochain2 G C) p) →
      ∃ w : Work.ShafarevichKoch.Z3 G A,
        Work.ShafarevichKoch.H3.mk w = δ (Work.ConCohomology.H2.mk z) ∧
        (∀ p : G × G × G, S.f ((w : G × G × G → A) p) =
          Work.ConCohomology.d2Fun (u : G × G → B) p)) :
    ∀ x : Work.ShafarevichKoch.H3 G A,
      Work.ShafarevichKoch.H3Map S.f x = 0 ↔
        ∃ y : Work.ConCohomology.H2 G C, δ y = x := by
  intro x
  constructor
  · -- `ker H³(f) ⊆ im δ`
    intro hx
    revert hx
    refine QuotientAddGroup.induction_on x ?_
    intro w hw
    change (H3Map S.f) (H3.mk w) = 0 at hw
    have hw1 : H3.mk (Z3Map S.f w) = 0 := by
      rw [← H3Map_mk]
      exact hw
    have hw2 : Z3Map S.f w ∈ B3' G B := (QuotientAddGroup.eq_zero_iff (Z3Map S.f w)).mp hw1
    rw [mem_B3', B3, AddMonoidHom.mem_range] at hw2
    obtain ⟨u, hu⟩ := hw2
    -- pointwise form of `d²u = f ∘ w`
    have hu_p : ∀ p : G × G × G, d2Fun (G := G) (M := B) (u : G × G → B) p
        = S.f ((w : G × G × G → A) p) := by
      intro p
      obtain ⟨σ, τ, ρ⟩ := p
      have h := congrFun (congrArg (fun v : Cochain3 G B => (v : G × G × G → B)) hu) (σ, τ, ρ)
      simpa only [Work.ConCohomology.d2Fun_apply, Work.ConCohomology.d2Hom_apply,
        Work.ShafarevichKoch.Z3Map_coe, Work.ShafarevichKoch.cochain3Map_apply] using h
    -- `z = g ∘ u` is a `2`-cocycle of `C` lifted by `u`
    let zco : Cochain2 G C := cochain2Map S.g u
    have hzcyc : IsCocycle2 (zco : G × G → C) := by
      rw [isCocycle2_iff_d2Fun]
      funext p
      obtain ⟨σ, τ, ρ⟩ := p
      have hnat := congrFun (d2Fun_comp (G := G) S.g (u : G × G → B)) (σ, τ, ρ)
      show d2Fun (G := G) (M := C) (fun q => S.g ((u : Cochain2 G B) q)) (σ, τ, ρ) = 0
      rw [hnat, hu_p (σ, τ, ρ)]
      exact (S.exact (S.f ((w : G × G × G → A) (σ, τ, ρ)))).mpr ⟨_, rfl⟩
    let zZ : Z2 G C := ⟨zco, mem_Z2.mpr hzcyc⟩
    have hz_lift : ∀ p : G × G, S.g ((u : Cochain2 G B) p) = (zZ : Cochain2 G C) p :=
      fun p => rfl
    obtain ⟨w', hw'1, hw'2⟩ := hδ zZ u hz_lift
    -- `w' = w`, since `f` is injective
    have hw'_eq : w' = w := by
      refine Subtype.ext ?_
      refine LocallyConstant.ext fun p => ?_
      refine S.injective_f ?_
      rw [hw'2 p, hu_p p]
    refine ⟨H2.mk zZ, ?_⟩
    rw [← hw'1, hw'_eq]
    rfl
  · -- `im δ ⊆ ker H³(f)`
    rintro ⟨y, rfl⟩
    refine QuotientAddGroup.induction_on y ?_
    intro z
    let u : Cochain2 G B := ⟨fun p => S.sect ((z : Cochain2 G C) p),
      (z : Cochain2 G C).isLocallyConstant.comp S.sect⟩
    have hu : ∀ p : G × G, S.g (u p) = (z : Cochain2 G C) p :=
      fun p => S.g_sect ((z : Cochain2 G C) p)
    obtain ⟨w, hw1, hw2⟩ := hδ z u hu
    change (H3Map S.f) (δ (H2.mk z)) = 0
    rw [← hw1, H3Map_mk]
    refine (QuotientAddGroup.eq_zero_iff (Z3Map S.f w)).mpr ?_
    rw [mem_B3', B3, AddMonoidHom.mem_range]
    refine ⟨u, ?_⟩
    refine LocallyConstant.ext fun p => ?_
    obtain ⟨σ, τ, ρ⟩ := p
    simpa only [Work.ConCohomology.d2Fun_apply, Work.ConCohomology.d2Hom_apply,
      Work.ShafarevichKoch.Z3Map_coe, Work.ShafarevichKoch.cochain3Map_apply]
      using (hw2 (σ, τ, ρ)).symm

end Work.ShafarevichKoch
