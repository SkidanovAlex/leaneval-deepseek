import Mathlib
import Submission.Work.SpecLin.Conventions
import Submission.Work.SpecLin.Points.Setup
import Submission.Work.SpecLin.Points.Basic
import Submission.Work.SpecLin.Content.exists_smul_notMem_maximalIdeal_map
import Submission.Work.SpecLin.Content.isPrincipal_of_fg_of_cyclic_map_quotient
import Submission.Work.CurveBasics.Basic.Sections
import Submission.Work.SpecLin.Chart.exists_isAffineOpen_containing
import Submission.Work.SpecLin.Core.range_base_subset_pair
import Submission.Work.SpecLin.Core.linEquiv_of_sections_of_chart

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


namespace Work.SpecLin.Core

universe u

open CategoryTheory Limits AlgebraicGeometry

variable {K : Type u} [Field K] {C : Work.CurveBasics.Curve K}

/-- The ring homomorphism `Γ(C, W) → R` induced by an `R`-point of `C` landing in the affine
open `W`, obtained by factoring `Spec R → C` through `Spec Γ(C, W) → C` and applying `Spec`. -/
noncomputable def rgMapHom (R : Type u) [CommRing R] [Algebra K R] (W : C.left.Opens)
    (hW : IsAffineOpen W) (s : Work.SpecLin.CurvePt C R)
    (hs : Set.range (s.left.base) ⊆ (W : Set C.left)) : Γ(C.left, W) →+* R :=
  (Spec.preimage
    (IsOpenImmersion.lift hW.fromSpec s.left
      (by rw [IsAffineOpen.range_fromSpec]; exact hs))).hom

/-- The `K`-algebra homomorphism `Γ(C, W) → R` induced by an `R`-point of `C` landing in the
affine open `W`. -/
noncomputable def rgMap (R : Type u) [CommRing R] [Algebra K R] (W : C.left.Opens)
    (hW : IsAffineOpen W) (s : Work.SpecLin.CurvePt C R)
    (hs : Set.range (s.left.base) ⊆ (W : Set C.left)) : Γ(C.left, W) →ₐ[K] R :=
  { toRingHom := rgMapHom R W hW s hs
    commutes' := by
      intro k
      have hfac : Spec.map (CommRingCat.ofHom (rgMapHom R W hW s hs)) ≫ hW.fromSpec = s.left := by
        rw [show Spec.map (CommRingCat.ofHom (rgMapHom R W hW s hs)) =
          IsOpenImmersion.lift hW.fromSpec s.left _ from Spec.map_preimage _]
        exact IsOpenImmersion.lift_fac _ _ _
      have h1 : Spec.map (CommRingCat.ofHom (rgMapHom R W hW s hs)) ≫ hW.fromSpec ≫ C.hom
          = s.left ≫ C.hom := by rw [← Category.assoc, hfac]
      rw [← Work.CurveBasics.Curve.specMap_algebraMap_sections C hW,
        show s.left ≫ C.hom = Spec.map (CommRingCat.ofHom (algebraMap K R))
          from Over.w s] at h1
      rw [← Spec.map_comp] at h1
      have h2 := Spec.map_injective h1
      have h3 : (rgMapHom R W hW s hs).comp (algebraMap K Γ(C.left, W)) = algebraMap K R := by
        have := congrArg CommRingCat.Hom.hom h2
        simpa using this
      exact DFunLike.congr_fun h3 k }


/-- **Specialisation of linear equivalence (the core of `Work.SpecLin.specLin`).**

Let `R` be a valuation ring which is a `K`-algebra, with fraction field `F` and residue field
`κ`, and let `s, t : Fin n → Spec R ⟶ C` be two `n`-tuples of `R`-points of a curve `C`.  If the
divisors `Σ_m [s_m]` and `Σ_m [t_m]` of the generic fibres on `C_F` are linearly equivalent
(witnessed by `h`), then the divisors `Σ_m [s̄_m]` and `Σ_m [t̄_m]` of the special fibres on
`C_κ` are linearly equivalent.

The point divisor `[p]` of an `F`-point of `C` is the *concrete* divisor `Work.SpecLin.ptDiv p`
of the closed point of `C_F` determined by `p` (`Submission/Work/SpecLin/Points/Basic.lean`,
built on `ptToPoint_isClosed`); no interface or opaque datum is involved.

Proof sketch (elementary; no Cartier divisors, no regularity, no Noetherian hypothesis on `R`):
1. *Chart.*  Choose a closed point `Q` of `C` whose preimage misses the images of all the
   finitely many points involved, with `C ∖ Q` affine, `A := Γ(C ∖ Q)` (this is `CB7`); every
   `R`-point of `C` involved factors through `Spec (A ⊗_K R)`.  Put `B := A ⊗_K R`; then `B` is
   a domain containing `R`, free over `R`, `P := m_R·B` is a prime of `B`, `B ⧸ P = A ⊗_K κ` is
   the coordinate ring of an affine chart of `C_κ`, and `ρ : B_P → Frac (B ⧸ P)` is the
   reduction.  Each section `s_m` gives a surjective `R`-algebra map `B → R` with kernel `I_m`;
   `I_m` is principal at every closed point of `Spec B` over `P` (Nakayama, since `B ⧸ I_m ≅ R`
   is flat and `B` is finitely presented over `R`).
2. *Content.*  Every element of `B` is `c·b'` with `c ∈ R` and `b' ∉ P`
   (`Work.SpecLin.Content.exists_smul_notMem_maximalIdeal_map`), so `h = c·h'` with
   `h' ∈ B_P^×`; multiplying by the scalar `c` does not change the divisor of `h`, and
   `h̄' := ρ(h')` is a well defined rational function on `C_κ`.
3. *Unit argument.*  With `f_m, g_m ∈ B` local equations of the sections `s_m` resp. the `t_m`,
   `u := h'·Π g_m/Π f_m` has trivial divisor on the generic fibre and is a unit both in `B_P` and
   in `O ⊗_R F` for every local ring `O` of `B` at a closed point of the special fibre; writing
   `u = α/(c·s)` and applying the content normalisation to `α` shows that the scalar involved
   lies in `B_P ∩ F = R` (a valuation ring), so that `u` and `u⁻¹` are integral, i.e. `u ∈ O`.
4. *Reduce.*  Reducing modulo `P` gives `h̄' = ū·Π f̄_m/Π ḡ_m` at every closed point of `C_κ`, so
   `div (h̄') = Σ_m [s̄_m] − Σ_m [t̄_m]` on `C_κ`, the required linear equivalence. -/
theorem linEquiv_of_sections {K : Type u} [Field K] {C : Work.CurveBasics.Curve K} {n : ℕ}
    (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R] [Algebra K R]
    (s t : Fin n → Work.SpecLin.CurvePt C R)
    (h : (C.baseChange (FractionRing R)).functionField) (hh : h ≠ 0)
    (hdiv : (C.baseChange (FractionRing R)).div h
      = (Finset.univ.sum fun m : Fin n => Work.SpecLin.ptDiv (Work.SpecLin.genPt R ≫ s m))
        - (Finset.univ.sum fun m : Fin n => Work.SpecLin.ptDiv (Work.SpecLin.genPt R ≫ t m))) :
    Work.SpecLin.LinEquiv C
      (Finset.univ.sum fun m : Fin n => Work.SpecLin.ptDiv (Work.SpecLin.closedPt R ≫ s m))
      (Finset.univ.sum fun m : Fin n => Work.SpecLin.ptDiv (Work.SpecLin.closedPt R ≫ t m)) := by
  classical
  -- The images of the finitely many sections lie in one affine chart.
  let S : Set C.left := (⋃ m, Set.range (s m).left.base) ∪ (⋃ m, Set.range (t m).left.base)
  have hsfin : ∀ m, (Set.range (s m).left.base).Finite := fun m =>
    ((Set.finite_singleton _).insert _).subset (range_base_subset_pair R (s m))
  have htfin : ∀ m, (Set.range (t m).left.base).Finite := fun m =>
    ((Set.finite_singleton _).insert _).subset (range_base_subset_pair R (t m))
  have hS : S.Finite :=
    (Set.finite_iUnion hsfin).union (Set.finite_iUnion htfin)
  obtain ⟨W, hW, hSW⟩ := Work.SpecLin.Chart.exists_isAffineOpen_containing C S hS
  -- Conclude with the affine-chart version of the statement.
  exact linEquiv_of_sections_of_chart R W hW s t
    (fun m => ((Set.subset_iUnion (fun m => Set.range (s m).left.base) m).trans
      (Set.subset_union_left)).trans hSW)
    (fun m => ((Set.subset_iUnion (fun m => Set.range (t m).left.base) m).trans
      (Set.subset_union_right)).trans hSW)
    h hh hdiv

end Work.SpecLin.Core