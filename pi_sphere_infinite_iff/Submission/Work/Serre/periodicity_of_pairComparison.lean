import Mathlib
import Submission.Work.Serre.Engine
import Submission.Work.StemsB.Fibrations
import Submission.Work.StemsB.SerreExact
import Submission.Work.Serre.serreE0Range
import Submission.Work.Cohomology.HomologyPairSequence
import Submission.Work.Cohomology.PairSequence
import Submission.Work.StemsB.RelChainsR
import Submission.Work.StemsB.RelChainsBaseChangeRat
import Submission.Work.StemsB.sphRatHomology
import Submission.Work.Serre.ratH_zero_of_pathConnected

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Periodicity of the pair comparison (the Gysin/periodicity reduction over `ℚ`)

`Work.Serre.periodicity_of_pairComparison` is the reduction step of Serre's Gysin/periodicity
theorem for a fibration with rationally acyclic total space and rationally spherical fibre
(`Submission/Work/Serre/periodicity_of_serreFibration.lean`): the two geometric inputs (the pair
comparison in the stable range together with its boundary surjectivity, and the comparison of the
strict and homotopy fibres) are *hypotheses* here, and the content of this file is the rational
long exact sequence bookkeeping which turns them into the periodicity of `H_*(B;ℚ)`.

The proof has three layers.

* The rational relative chains of a pair are `Work.StemsB.relChainsR ℚ X A`, and
  `Work.StemsB.RelChainsR` provides the long exact sequence of the pair over `ℚ`
  (`relChainsR_exact₁/₂/₃`).  `pp_relH_sphere_of_acyclic` computes `H_*(X,A;ℚ)` when `X` is
  rationally acyclic and `A` has the rational homology of `S^r`: `H_{r+1}(X,A;ℚ) ≅ ℚ` and
  `H_j(X,A;ℚ) = 0` for `j ≥ 2`, `j ≠ r+1`.
* `Work.StemsB.relChainsBaseChangeRat` (the base change `C_*(X,A;ℤ) ⊗ ℚ ≅ C_*(X,A;ℚ)`, natural in
  the pair) together with `Work.StemsB.SphRat.homologyMapBaseChange` transports the *integral*
  pair comparison of the hypotheses to the rational one
  (`pp_nonempty_relH_iso_of_isIso_relPairMap`, `pp_isZero_relH_of_surjective_relPairMap`).
* The long exact sequence of the pair `(B,{b₀})` converts the resulting vanishing of
  `H_*(B,{b₀};ℚ)` into the vanishing of `H_*(B;ℚ)`.

The argument only uses the *existence* of the base change isomorphism (not its naturality), because
the pair comparison is only ever used to transfer vanishing between the two relative homology
groups.
-/

namespace Work.Serre

open CategoryTheory CategoryTheory.Limits

noncomputable section

/-! ## Notation for the two homologies in play -/

/-- The singular homology of `X` with rational coefficients, in degree `n`. -/
abbrev ppAbsH (X : TopCat) (n : ℕ) : ModuleCat ℚ :=
  (Work.Cohomology.singularChains ℚ X).homology n

/-- The relative singular homology of the pair `(X,A)` with rational coefficients, in degree `n`. -/
abbrev ppRelH (X : TopCat) (A : Set X) (n : ℕ) : ModuleCat ℚ :=
  (Work.StemsB.relChainsR ℚ X A).homology n

/-! ## The long exact sequence of a pair over `ℚ`: three elementary chases -/

/-- **The homology of a one-point space vanishes in positive degrees.** -/
theorem pp_isZero_absH_singleton (X : Type) [TopologicalSpace X] (x₀ : X) {j : ℕ} (hj : 0 < j) :
    IsZero (ppAbsH (TopCat.of ↥({x₀} : Set X)) j) := by
  haveI : Nonempty ↥({x₀} : Set X) := ⟨⟨x₀, rfl⟩⟩
  haveI : Subsingleton ↥({x₀} : Set X) :=
    ⟨fun a b => Subtype.ext
      ((Set.mem_singleton_iff.mp a.2).trans (Set.mem_singleton_iff.mp b.2).symm)⟩
  exact (ratAcyclic_of_contractible ↥({x₀} : Set X)).isZero_ratH hj

/-- **If the subspace and the relative group vanish in a degree, so does the ambient group.**  This
is the exactness chase at `H_k(X)` in `H_k(A) → H_k(X) → H_k(X,A)`. -/
theorem pp_isZero_absH_of_isZero_rel (X : Type) [TopologicalSpace X] (A : Set X) (k : ℕ)
    (hA : IsZero (ppAbsH (TopCat.of ↥A) k)) (hrel : IsZero (ppRelH (TopCat.of X) A k)) :
    IsZero (ppAbsH (TopCat.of X) k) :=
  (Work.StemsB.relChainsR_exact₂ ℚ (TopCat.of X) A k).isZero_X₂
    (hA.eq_zero_of_src _) (hrel.eq_zero_of_tgt _)

/-- **If the subspace vanishes in degrees `n` and `n+1`, then `H_{n+1}(X) ≅ H_{n+1}(X,A)`.**  This
is the exactness chase at `H_{n+1}(X)` (injectivity, from `H_{n+1}(A) = 0`) and at `H_{n+1}(X,A)`
(surjectivity, from `H_n(A) = 0`). -/
theorem pp_nonempty_absH_iso_relH (X : Type) [TopologicalSpace X] (A : Set X) (n : ℕ)
    (hA1 : IsZero (ppAbsH (TopCat.of ↥A) (n + 1))) (hA0 : IsZero (ppAbsH (TopCat.of ↥A) n)) :
    Nonempty (ppAbsH (TopCat.of X) (n + 1) ≅ ppRelH (TopCat.of X) A (n + 1)) := by
  have hS2 := Work.StemsB.relChainsR_exact₂ ℚ (TopCat.of X) A (n + 1)
  have hS3 := Work.StemsB.relChainsR_exact₃ ℚ (TopCat.of X) A n
  let T : ppAbsH (TopCat.of X) (n + 1) ⟶ ppRelH (TopCat.of X) A (n + 1) :=
    HomologicalComplex.homologyMap
      (cokernel.π (Work.StemsB.relChainsRIncl ℚ (TopCat.of X) A)) (n + 1)
  haveI : Mono T := hS2.mono_g_iff.mpr (hA1.eq_zero_of_src
    (HomologicalComplex.homologyMap (Work.StemsB.relChainsRIncl ℚ (TopCat.of X) A) (n + 1)))
  haveI : Epi T := hS3.epi_f_iff.mpr (hA0.eq_zero_of_tgt
    (Work.StemsB.relChainsRδ ℚ (TopCat.of X) A n))
  haveI : IsIso T := isIso_of_mono_of_epi T
  exact ⟨asIso T⟩

/-- **The relative homology of a pair with a rationally acyclic total space and a rationally
spherical subspace.**  If `H_j(X;ℚ) = 0` for `j > 0`, `H_r(A;ℚ) ≅ ℚ` and `H_j(A;ℚ) = 0` for
`j > 0`, `j ≠ r` (`r ≥ 1`), then `H_{r+1}(X,A;ℚ) ≅ ℚ` and `H_j(X,A;ℚ) = 0` for `j ≥ 2`,
`j ≠ r+1`.

Both halves are the long exact sequence of the pair, in the form
`H_{j}(X) → H_{j}(X,A) → H_{j-1}(A)`: for `j = r+1` the two outer terms vanish and the connecting
map `H_{r+1}(X,A) → H_r(A) ≅ ℚ` is an isomorphism; for `j ≥ 2`, `j ≠ r+1` both outer terms vanish
and so does `H_j(X,A)`. -/
theorem pp_relH_sphere_of_acyclic (X : Type) [TopologicalSpace X] (A : Set X) (r : ℕ) (hr : 1 ≤ r)
    (hX : ∀ j : ℕ, 0 < j → IsZero (ppAbsH (TopCat.of X) j))
    (hAr : Nonempty (ppAbsH (TopCat.of ↥A) r ≅ ModuleCat.of ℚ ℚ))
    (hA : ∀ j : ℕ, 0 < j → j ≠ r → IsZero (ppAbsH (TopCat.of ↥A) j)) :
    Nonempty (ppRelH (TopCat.of X) A (r + 1) ≅ ModuleCat.of ℚ ℚ) ∧
      (∀ j : ℕ, 2 ≤ j → j ≠ r + 1 → IsZero (ppRelH (TopCat.of X) A j)) := by
  constructor
  · -- the line `H_{r+1}(X,A) ≅ H_r(A) ≅ ℚ`
    have hS3 := Work.StemsB.relChainsR_exact₃ ℚ (TopCat.of X) A r
    have hS1 := Work.StemsB.relChainsR_exact₁ ℚ (TopCat.of X) A r
    haveI : Mono (Work.StemsB.relChainsRδ ℚ (TopCat.of X) A r) :=
      hS3.mono_g_iff.mpr ((hX (r + 1) (by omega)).eq_zero_of_src
        (HomologicalComplex.homologyMap
          (cokernel.π (Work.StemsB.relChainsRIncl ℚ (TopCat.of X) A)) (r + 1)))
    haveI : Epi (Work.StemsB.relChainsRδ ℚ (TopCat.of X) A r) :=
      hS1.epi_f_iff.mpr ((hX r (by omega)).eq_zero_of_tgt
        (HomologicalComplex.homologyMap (Work.StemsB.relChainsRIncl ℚ (TopCat.of X) A) r))
    haveI : IsIso (Work.StemsB.relChainsRδ ℚ (TopCat.of X) A r) :=
      isIso_of_mono_of_epi _
    exact hAr.map (fun e => asIso (Work.StemsB.relChainsRδ ℚ (TopCat.of X) A r) ≪≫ e)
  · -- vanishing in the remaining degrees `≥ 2`
    intro j hj2 hjne
    have hS3 := Work.StemsB.relChainsR_exact₃ ℚ (TopCat.of X) A (j - 1)
    have hXj : IsZero ((Work.Cohomology.singularChains ℚ (TopCat.of X)).homology ((j - 1) + 1)) :=
      IsZero.of_iso (hX j (by omega))
        (eqToIso (congrArg
          (fun i => (Work.Cohomology.singularChains ℚ (TopCat.of X)).homology i)
          (Nat.sub_add_cancel (by omega : 1 ≤ j))))
    have hAj : IsZero ((Work.Cohomology.singularChains ℚ (TopCat.of ↥A)).homology (j - 1)) :=
      hA (j - 1) (by omega) (by omega)
    have hmid : IsZero ((Work.StemsB.relChainsR ℚ (TopCat.of X) A).homology ((j - 1) + 1)) :=
      hS3.isZero_X₂
        (hXj.eq_zero_of_src (HomologicalComplex.homologyMap
          (cokernel.π (Work.StemsB.relChainsRIncl ℚ (TopCat.of X) A)) ((j - 1) + 1)))
        (hAj.eq_zero_of_tgt (Work.StemsB.relChainsRδ ℚ (TopCat.of X) A (j - 1)))
    exact IsZero.of_iso hmid (eqToIso (congrArg
      (fun i => (Work.StemsB.relChainsR ℚ (TopCat.of X) A).homology i)
      (Nat.sub_add_cancel (by omega : 1 ≤ j)))).symm

/-! ## Base change `ℤ → ℚ` of the relative homology -/

/-- **Base change of the relative homology.**  The rational relative chain complex is the base
change of the integral one (`Work.StemsB.relChainsBaseChangeRat`), and an additive functor
preserving homology commutes with the passage to homology
(`Work.StemsB.SphRat.homologyMapBaseChange`). -/
theorem pp_relH_baseChange (X : TopCat) (A : Set X) (i : ℕ) :
    Nonempty (ppRelH X A i ≅
      Work.StemsB.IntRatF.obj ((Work.Cohomology.relChains X A).homology i)) := by
  haveI hflat : (Int.castRingHom ℚ).Flat := by rw [RingHom.Flat]; infer_instance
  haveI : PreservesFiniteLimits Work.StemsB.IntRatF :=
    ModuleCat.preservesFiniteLimits_extendScalars_of_flat hflat
  haveI : PreservesFiniteColimits Work.StemsB.IntRatF := inferInstance
  haveI : Work.StemsB.IntRatF.PreservesHomology := inferInstance
  obtain ⟨β⟩ := Work.StemsB.relChainsBaseChangeRat X A
  exact ⟨(HomologicalComplex.homologyMapIso β i).symm ≪≫
    (Work.StemsB.SphRat.homologyMapBaseChange Work.StemsB.IntRatF
      (Work.Cohomology.relChains X A) i).some⟩

/-- **Base change preserves surjectivity** for the extension of scalars `ℤ → ℚ`: on pure tensors
`a ⊗ n = a ⊗ f m`. -/
theorem pp_surjective_extendScalars_map {M N : ModuleCat ℤ} (f : M ⟶ N)
    (hf : Function.Surjective f.hom) :
    Function.Surjective (Work.StemsB.IntRatF.map f).hom := by
  haveI : Epi f := (ModuleCat.epi_iff_surjective f).mpr hf
  haveI : Epi (Work.StemsB.IntRatF.map f) := inferInstance
  exact (ModuleCat.epi_iff_surjective (Work.StemsB.IntRatF.map f)).mp inferInstance

/-- **The rational pair comparison is an isomorphism when the integral one is.** -/
theorem pp_nonempty_relH_iso_of_isIso_relPairMap {E B : Type} [TopologicalSpace E]
    [TopologicalSpace B] (p : C(E, B)) (b₀ : B) (i : ℕ)
    (h : IsIso (HomologicalComplex.homologyMap (Work.StemsB.relPairMap p b₀) i)) :
    Nonempty (ppRelH (TopCat.of E) (p ⁻¹' {b₀}) i ≅
      ppRelH (TopCat.of B) ({b₀} : Set B) i) := by
  obtain ⟨α₁⟩ := pp_relH_baseChange (TopCat.of E) (p ⁻¹' {b₀}) i
  obtain ⟨α₂⟩ := pp_relH_baseChange (TopCat.of B) ({b₀} : Set B) i
  exact ⟨α₁ ≪≫ Work.StemsB.IntRatF.mapIso
    (asIso (HomologicalComplex.homologyMap (Work.StemsB.relPairMap p b₀) i)) ≪≫ α₂.symm⟩

/-- **The rational relative homology of the target of the pair comparison vanishes if the source
does** (the comparison being surjective in that degree). -/
theorem pp_isZero_relH_of_surjective_relPairMap {E B : Type} [TopologicalSpace E]
    [TopologicalSpace B] (p : C(E, B)) (b₀ : B) (i : ℕ)
    (hs : Function.Surjective
      (HomologicalComplex.homologyMap (Work.StemsB.relPairMap p b₀) i).hom)
    (hE : IsZero (ppRelH (TopCat.of E) (p ⁻¹' {b₀}) i)) :
    IsZero (ppRelH (TopCat.of B) ({b₀} : Set B) i) := by
  obtain ⟨α₁⟩ := pp_relH_baseChange (TopCat.of E) (p ⁻¹' {b₀}) i
  obtain ⟨α₂⟩ := pp_relH_baseChange (TopCat.of B) ({b₀} : Set B) i
  haveI : Subsingleton ↥(Work.StemsB.IntRatF.obj
      ((Work.Cohomology.relChains (TopCat.of E) (p ⁻¹' {b₀})).homology i)) :=
    ModuleCat.isZero_iff_subsingleton.mp (IsZero.of_iso hE α₁.symm)
  have h2 : IsZero (Work.StemsB.IntRatF.obj
      ((Work.Cohomology.relChains (TopCat.of B) ({b₀} : Set B)).homology i)) :=
    ModuleCat.isZero_iff_subsingleton.mpr
      (pp_surjective_extendScalars_map
        (HomologicalComplex.homologyMap (Work.StemsB.relPairMap p b₀) i) hs).subsingleton
  exact IsZero.of_iso h2 α₂

/-! ## The reduction -/

theorem periodicity_of_pairComparison {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (hp : Work.StemsB.IsSerreFibration p) (e₀ : E) (b₀ : B)
    (hB : PathConnectedSpace B) (hE : Work.Serre.RatAcyclic E)
    (hsc : Subsingleton (HomotopyGroup (Fin 1) B b₀))
    (b r : ℕ) (hb : 2 ≤ b) (hr : 1 ≤ r) (hconn : Work.Serre.Conn B b₀ b)
    (hvan : ∀ t : ℕ, 0 < t → t ≠ r →
      CategoryTheory.Limits.IsZero (Work.Serre.ratH (TopCat.of (Work.RatHurewicz.homotopyFibre p e₀)) t))
    (hgen : Nonempty (Work.Serre.ratH (TopCat.of (Work.RatHurewicz.homotopyFibre p e₀)) r ≅
      ModuleCat.of ℚ ℚ))
    (hpair : (∀ i : ℕ, i < b + r → CategoryTheory.IsIso
        (HomologicalComplex.homologyMap (Work.StemsB.relPairMap p b₀) i)) ∧
      Function.Surjective
        (HomologicalComplex.homologyMap (Work.StemsB.relPairMap p b₀) (b + r)).hom)
    (hbridge : ∀ j : ℕ, Nonempty (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre p b₀)) j ≅
      Work.Serre.ratH (TopCat.of (Work.RatHurewicz.homotopyFibre p e₀)) j)) :
    (∀ s : ℕ, 1 ≤ s → s < b → Nonempty (Work.Serre.ratH (TopCat.of B) s ≅ Work.Serre.ratH (TopCat.of B) (s + r + 1))) ∧
      Nonempty (Work.Serre.ratH (TopCat.of B) 0 ≅ Work.Serre.ratH (TopCat.of B) (r + 1)) := by
  -- the rational homology of the (strict) fibre, read off from the homotopy fibre
  have hfib_r : Nonempty (ppAbsH (TopCat.of ↥(p ⁻¹' {b₀})) r ≅ ModuleCat.of ℚ ℚ) :=
    (hbridge r).map (fun e => e ≪≫ hgen.some)
  have hfib_zero : ∀ t : ℕ, 0 < t → t ≠ r →
      IsZero (ppAbsH (TopCat.of ↥(p ⁻¹' {b₀})) t) :=
    fun t ht htr => IsZero.of_iso (hvan t ht htr) (hbridge t).some
  -- the two relative homology groups of the pair `(E, p⁻¹{b₀})`
  obtain ⟨hEpair_iso, hEpair_zero⟩ :=
    pp_relH_sphere_of_acyclic E (p ⁻¹' {b₀}) r hr
      (fun j hj => hE.isZero_ratH hj) hfib_r hfib_zero
  -- the point `{b₀}` has the rational homology of a point
  have hpt_zero : ∀ k : ℕ, 0 < k → IsZero (ppAbsH (TopCat.of ↥({b₀} : Set B)) k) :=
    fun k hk => pp_isZero_absH_singleton B b₀ hk
  -- the vanishing of `H_k(B,b₀;ℚ)` for `r+1 < k ≤ b+r`
  have key : ∀ k : ℕ, r + 1 < k → k ≤ b + r → IsZero (ppAbsH (TopCat.of B) k) := by
    intro k hk1 hk2
    have hrelB : IsZero (ppRelH (TopCat.of B) ({b₀} : Set B) k) := by
      rcases lt_or_eq_of_le hk2 with hlt | heq
      · obtain ⟨e⟩ := pp_nonempty_relH_iso_of_isIso_relPairMap p b₀ k (hpair.1 k hlt)
        exact IsZero.of_iso (hEpair_zero k (by omega) (by omega)) e.symm
      · exact pp_isZero_relH_of_surjective_relPairMap p b₀ k (heq ▸ hpair.2)
          (hEpair_zero k (by omega) (by omega))
    exact pp_isZero_absH_of_isZero_rel B ({b₀} : Set B) k (hpt_zero k (by omega)) hrelB
  constructor
  · -- the periodicity in positive degrees below `b`
    intro s hs1 hsb
    have h1 : IsZero (ppAbsH (TopCat.of B) s) := by
      have hV : RatVanishingBelow B ((b - 1) + 1) :=
        serreE0Range B b₀ (b - 1) (fun i hi => hconn i (by omega))
      exact hV s hs1 (by omega)
    have h2 : IsZero (ppAbsH (TopCat.of B) (s + r + 1)) := key (s + r + 1) (by omega) (by omega)
    exact ⟨IsZero.iso h1 h2⟩
  · -- the degree-zero periodicity
    have h0 : Nonempty (ppAbsH (TopCat.of B) 0 ≅ ModuleCat.of ℚ ℚ) :=
      ratH_zero_of_pathConnected B
    have htop : Nonempty (ppAbsH (TopCat.of B) (r + 1) ≅ ModuleCat.of ℚ ℚ) := by
      obtain ⟨e1⟩ := pp_nonempty_absH_iso_relH B ({b₀} : Set B) r
        (hpt_zero (r + 1) (by omega)) (hpt_zero r (by omega))
      obtain ⟨e2⟩ := pp_nonempty_relH_iso_of_isIso_relPairMap p b₀ (r + 1)
        (hpair.1 (r + 1) (by omega))
      exact ⟨e1 ≪≫ e2.symm ≪≫ hEpair_iso.some⟩
    exact ⟨h0.some ≪≫ htop.some.symm⟩

end

end Work.Serre
