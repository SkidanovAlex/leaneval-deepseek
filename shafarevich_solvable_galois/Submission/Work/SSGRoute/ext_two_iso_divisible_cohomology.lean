import Mathlib
import Submission.Work.SSGRoute.ext_one_iso_divisible_cohomology
import Submission.Work.SSGRoute.local_ext_h1_bridge
import Submission.Work.SSGRoute.ext_one_homRepFree_subsingleton
import Submission.Work.SSGRoute.ext_coind_iso_proof
import Submission.Work.SSGRoute.homRep
import Submission.Work.GroupCohomology.Basic
import Submission.Work.SSGRoute.ext2_iso_cohomology
import Submission.Work.SSGRoute.ext_one_iso_lattice_cohomology
import Submission.Work.SSGRoute.ExtOneAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

open CategoryTheory SSGRoute.PTExt

noncomputable section

/-! ## Auxiliary lemmas

The proof of `ext_two_iso_divisible_cohomology` needs three ingredients that are *not* in the
workspace in the degree (or the generality) required:

* `ext_subsingleton_of_iso_second_deg`: the degree-`n` companion of
  `ext_subsingleton_of_iso_second` (`SSGRoute/ext_one_homRepFree_subsingleton.lean`), which is
  stated in degree `1`.  Same proof, `1` replaced by `n`.
* `ext_pos_homRepFree_subsingleton`: the degree-`n` (`n ≥ 1`) companion of
  `ext_one_homRepFree_subsingleton`, the vanishing of `H^n(G, Hom_ℤ(ℤ[G]^α, N))` for `n ≥ 1`.
  Used in degree `2`.
* `ext_one_iso_ext_two_of_covariant_acyclic`: the *covariant* dimension shift
  `Ext¹(X, C) ≅ Ext²(X, A)` for a short exact sequence `0 → A → B → C → 0` whose middle term is
  acyclic in degrees `1` and `2` for the fixed first variable `X`.  This is the covariant
  companion of `ext_shift_of_projective_presentation`.

Finally `ext_unitRep_iso_groupCohomology` (the canonical `H^n(G, X) ≅ Ext^n_G(ℤ, X)`, computed
from the bar resolution) and `ext_two_homRep_iso_H2` (the degree-two identification for the
internal hom `homRep`) assemble the dictionary with the explicit inhomogeneous `H²`. -/

/-- **Degree-`n` transport of `Ext` in the coefficient variable.**  If `A ≅ B` as `G`-modules and
`Ext X B n` is a subsingleton, then so is `Ext X A n`.  (Degree-`n` version of
`ext_subsingleton_of_iso_second`.) -/
theorem ext_subsingleton_of_iso_second_deg {G : Type} [Group G] {A B X : Rep.{0} Coeff G}
    (e : A ≅ B) (n : ℕ) (h : Subsingleton (Abelian.Ext X B n)) :
    Subsingleton (Abelian.Ext X A n) := by
  have key : ∀ a : Abelian.Ext X A n,
      (a.comp (Abelian.Ext.mk₀ e.hom) (add_zero n)).comp
        (Abelian.Ext.mk₀ e.inv) (add_zero n) = a := by
    intro a
    rw [Abelian.Ext.comp_assoc_of_second_deg_zero]
    rw [Abelian.Ext.mk₀_comp_mk₀, e.hom_inv_id]
    exact Abelian.Ext.comp_mk₀_id a
  refine ⟨fun a b => ?_⟩
  have h1 : (a.comp (Abelian.Ext.mk₀ e.hom) (add_zero n)) =
      (b.comp (Abelian.Ext.mk₀ e.hom) (add_zero n)) := Subsingleton.elim _ _
  have h2 := congrArg (fun z => z.comp (Abelian.Ext.mk₀ e.inv) (add_zero n)) h1
  rwa [key a, key b] at h2

/-- **`Ext^n_G(ℤ, Hom_ℤ(ℤ[G]^α, N)) = 0` for `n ≥ 1` when the coefficient module is coinduced from
`⊥`.**  Degree-`n` companion of `ext_one_homRepFree_subsingleton`: if
`Hom_ℤ(ℤ[G]^α, N) ≅ Coind_⊥^G X` (Shapiro's hypothesis, which holds by `homRepFree_coind_iso`),
then `Ext^n_G(ℤ, Hom_ℤ(ℤ[G]^α, N))` is a subsingleton for every `n ≥ 1`.  Shapiro for `Ext`
(`ext_coind_iso_proof`) moves this to `Ext^n_⊥(res_⊥ ℤ, X)`, which vanishes because `res_⊥ ℤ` is
projective over the trivial group. -/
theorem ext_pos_homRepFree_subsingleton (G : Type) [Group G] (α : Type)
    (N : Rep.{0} Coeff G)
    (X : Rep.{0} Coeff (⊥ : Subgroup G))
    (hX : Nonempty (homRep (Rep.free Coeff G α) N ≅ Rep.coind (⊥ : Subgroup G).subtype X))
    (n : ℕ) (hn : 1 ≤ n) :
    Subsingleton (Abelian.Ext (unitRep G) (homRep (Rep.free Coeff G α) N) n) := by
  obtain ⟨e⟩ := hX
  obtain ⟨sh⟩ := ext_coind_iso_proof G (⊥ : Subgroup G) (unitRep G) X n
  haveI : Projective (Rep.res (⊥ : Subgroup G).subtype (unitRep G)) :=
    projective_unitRep_of_subsingleton (⊥ : Subgroup G)
  have hsub : Subsingleton (Abelian.Ext (Rep.res (⊥ : Subgroup G).subtype (unitRep G)) X n) := by
    have h := Abelian.Ext.subsingleton_of_projective
      (Rep.res (⊥ : Subgroup G).subtype (unitRep G)) X (n - 1)
    rwa [Nat.sub_add_cancel hn] at h
  have h2 : Subsingleton (Abelian.Ext (unitRep G)
      (Rep.coind (⊥ : Subgroup G).subtype X) n) :=
    ⟨fun a b => sh.injective (hsub.elim _ _)⟩
  exact ext_subsingleton_of_iso_second_deg e n h2

/-- **The covariant dimension shift.**  For a short exact sequence `0 → S.X₁ → S.X₂ → S.X₃ → 0`
in `Rep Coeff G` and an object `A` whose `Ext¹` and `Ext²` out of `S.X₂` vanish, the connecting
map `Ext¹(A, S.X₃) → Ext²(A, S.X₁)` of the covariant long exact sequence is bijective:

`Ext¹_G(A, S.X₃) ≅ Ext²_G(A, S.X₁)`.

Covariant companion of `ext_shift_of_projective_presentation`; the two vanishing hypotheses are
supplied in the application by `ext_one_homRepFree_subsingleton` and
`ext_pos_homRepFree_subsingleton` in degrees `1` and `2`. -/
theorem ext_one_iso_ext_two_of_covariant_acyclic (G : Type) [Group G]
    (S : ShortComplex (Rep.{0} Coeff G)) (hS : S.ShortExact) (A : Rep.{0} Coeff G)
    [Subsingleton (Abelian.Ext A S.X₂ 1)] [Subsingleton (Abelian.Ext A S.X₂ 2)] :
    Nonempty (Abelian.Ext A S.X₃ 1 ≃+ Abelian.Ext A S.X₁ 2) := by
  classical
  have h21 : (1 : ℕ) + 1 = 2 := rfl
  refine ⟨AddEquiv.ofBijective (hS.extClass.postcomp A h21) ⟨?_, ?_⟩⟩
  · intro x y hxy
    have h0 : hS.extClass.postcomp A h21 (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    obtain ⟨x₂, hx₂⟩ := Abelian.Ext.covariant_sequence_exact₃ A hS (x - y) h21 h0
    have h2 : x₂ = 0 := Subsingleton.elim _ _
    rw [h2, Abelian.Ext.zero_comp] at hx₂
    exact sub_eq_zero.mp hx₂.symm
  · intro y
    have hy : y.comp (Abelian.Ext.mk₀ S.f) (add_zero 2) = 0 := Subsingleton.elim _ _
    obtain ⟨x₃, hx₃⟩ := Abelian.Ext.covariant_sequence_exact₁ A hS y hy h21
    exact ⟨x₃, hx₃⟩

/-- **`Ext^n_G(ℤ, X) ≅ H^n(G, X)`.**  For any `Rep Coeff G` `X`, the `Ext`-cohomology of the
trivial module `ℤ = unitRep G` is Mathlib's group cohomology of `X`.  Both are the `n`-th
homology of the `Hom`-complex of the bar resolution: Mathlib's `groupCohomologyIso` and the
`Ext`-computation `E0bCore.extHAddEquivHomology` alongside each other. -/
theorem ext_unitRep_iso_groupCohomology (G : Type) [Group G] (X : Rep.{0} Coeff G) (n : ℕ) :
    Nonempty (Abelian.Ext (unitRep G) X n ≃+ groupCohomology X n) := by
  obtain ⟨Φ, _⟩ := E0bCore.extHAddEquivHomology (C := Rep.{0} Coeff G)
    (k := Coeff) (X := unitRep G) (Y := X) (Rep.barResolution Coeff G) n
  exact ⟨Φ.symm.trans
    (groupCohomologyIso X n (Rep.barResolution Coeff G)).toLinearEquiv.toAddEquiv.symm⟩

/-- **Degree-two dictionary for the internal hom.**  For any `M N : Rep Coeff G`,
`Ext²_G(ℤ, Hom_ℤ(M,N)) ≅ H²(G, Hom_ℤ(M,N))` in the explicit inhomogeneous description
`Work.GroupCohomology.H2`, with the conjugation action of `homRep`.  This composes
`ext_unitRep_iso_groupCohomology` (`Ext²_G(ℤ, ·) ≅ H²(G, ·)`), the coefficient transfer along
`bridgeEquiv` (`homRep M N ≅ (Rep.ihom M).obj N` as `G`-modules) and
`groupCohomology_ihom_deg_two`. -/
theorem ext_two_homRep_iso_H2 (G : Type) [Group G] (M N : Rep.{0} Coeff G) :
    Nonempty (Abelian.Ext (unitRep G) (homRep M N) 2 ≃+
      Work.GroupCohomology.H2 G (M.V →ₗ[Coeff] N.V)) := by
  obtain ⟨e1⟩ := ext_unitRep_iso_groupCohomology G (homRep M N) 2
  obtain ⟨e2⟩ := H2_coeff_transfer (k := Coeff) (k' := Coeff) (G := G)
    ((Rep.ihom M).obj N) (homRep M N) (bridgeEquiv M N) (bridgeEquiv_rho M N)
  obtain ⟨e3⟩ := groupCohomology_ihom_deg_two G M N
  exact ⟨e1.trans (e2.symm.trans e3)⟩

/-- The degree-two companion of `Work.SSGRoute.ext_one_iso_divisible_cohomology`: for any group `G`,
any `Rep Coeff G` `M` and any `Rep Coeff G` `N` whose underlying abelian group is divisible,
`Ext²_{ℤ[G]}(M,N) ≅ H²(G, Hom_ℤ(M,N))` (the internal `Hom` with the conjugation action of
`Work.SSGRoute.homRep`).  Unlike `Work.SSGRoute.ext2_iso_cohomology` it needs no freeness of `M` over
`ℤ`; it is proved from that statement's lattice form plus the degree shift
`Ext²(M,N) ≅ Ext¹(R,N)` for a free presentation `0 → R → F → M → 0` (`F = Rep.free Coeff G M.V`) and
the degree-one divisible dictionary, the short exact sequence
`0 → Hom_ℤ(M,N) → Hom_ℤ(F,N) → Hom_ℤ(R,N) → 0` being exact because `N` is divisible, while
`H^i(G, Hom_ℤ(F,N)) = 0` for `i = 1, 2` because `Hom_ℤ(F,N)` is coinduced from the trivial subgroup
(`Work.SSGRoute.ext_one_homRepFree_subsingleton` is the degree-one case,
`Work.SSGRoute.ext_coind_iso_proof` is Shapiro's isomorphism in every degree).

Proof route, in order: `Rep.freeLift_id_epi` gives a free presentation `0 → R → F → M → 0`;
`Work.SSGRoute.ext_shift_of_projective_presentation` gives `Ext²(M,N) ≅ Ext¹(R,N)`;
`Work.SSGRoute.ext_one_iso_divisible_cohomology` (which allows an arbitrary first variable) gives
`Ext¹(R,N) ≅ H¹(G, Hom_ℤ(R,N))`; the long exact sequence of the (right-exact, since `N` is
divisible) sequence `0 → Hom(M,N) → Hom(F,N) → Hom(R,N) → 0` gives
`H¹(G, Hom_ℤ(R,N)) ≅ H²(G, Hom_ℤ(M,N))`. -/
theorem ext_two_iso_divisible_cohomology (G : Type) [Group G]
    (M N : Rep.{0} SSGRoute.PTExt.Coeff G)
    (hdiv : ∀ (n : ℕ), 0 < n → ∀ y : N.V, ∃ x : N.V, n • x = y) :
    Nonempty (CategoryTheory.Abelian.Ext M N 2 ≃+
      Work.GroupCohomology.H2 G (M.V →ₗ[SSGRoute.PTExt.Coeff] N.V)) := by
  classical
  -- `N` is injective (equivalently divisible) as a `ℤ`-module
  have hInj : Module.Injective Coeff N.V := moduleInjective_coeff_of_divisible N.V hdiv
  -- a free presentation `0 → R → F → M → 0`, `F = Rep.free Coeff G M.V` projective
  have hp : Epi (Rep.freeLift Coeff G M (fun m : M.V => m)) := freeLift_id_epi G M
  let p : Rep.free Coeff G M.V ⟶ M := Rep.freeLift Coeff G M (fun m : M.V => m)
  haveI hp' : Epi p := hp
  let S : ShortComplex (Rep.{0} Coeff G) :=
    ShortComplex.mk (Limits.kernel.ι p) p (Limits.kernel.condition p)
  have hS : S.ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.exact_kernel p) inferInstance inferInstance
  have hProj : Projective S.X₂ := Rep.free_projective
  haveI := hProj
  -- `Ext²(M,N) ≅ Ext¹(R,N)` (dimension shift along the free presentation)
  obtain ⟨ea⟩ := ext_shift_of_projective_presentation G S hS N 1 le_rfl
  -- `Ext¹(R,N) ≅ Ext¹_G(ℤ, Hom_ℤ(R,N))` (divisible-coefficient dictionary in degree one)
  obtain ⟨eb⟩ := ext_one_iso_divisible_cohomology G S.X₁ N hdiv
  -- the dual complex `0 → Hom(M,N) → Hom(F,N) → Hom(R,N) → 0` is short exact, `N` divisible
  have hS' : (homRepShortComplex S N).ShortExact := homRepShortComplex_shortExact G S hS N hInj
  obtain ⟨X, hXiso⟩ := homRepFree_coind_iso G M.V N
  -- the middle term `Hom_ℤ(F,N)` is acyclic in degrees `1` and `2`
  haveI hi1 : Subsingleton (Abelian.Ext (unitRep G) (homRepShortComplex S N).X₂ 1) :=
    ext_one_homRepFree_subsingleton G M.V N X hXiso
  haveI hi2 : Subsingleton (Abelian.Ext (unitRep G) (homRepShortComplex S N).X₂ 2) :=
    ext_pos_homRepFree_subsingleton G M.V N X hXiso 2 (by norm_num)
  -- hence the connecting map gives `Ext¹_G(ℤ, Hom_ℤ(R,N)) ≅ Ext²_G(ℤ, Hom_ℤ(M,N))`
  obtain ⟨ec⟩ := ext_one_iso_ext_two_of_covariant_acyclic G (homRepShortComplex S N) hS' (unitRep G)
  -- and `Ext²_G(ℤ, Hom_ℤ(M,N)) ≅ H²(G, Hom_ℤ(M,N))`
  obtain ⟨ed⟩ := ext_two_homRep_iso_H2 G M N
  exact ⟨ea.symm.trans (eb.trans (ec.trans ed))⟩

end

end Work.SSGRoute
