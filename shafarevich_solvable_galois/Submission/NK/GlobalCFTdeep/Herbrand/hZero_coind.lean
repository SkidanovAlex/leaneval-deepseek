import Mathlib
import Submission.NK.GlobalCFTdeep.Basic
import Submission.Commons.RepresentationTheory.GroupCohomology.natCard_groupCohomology_two_eq_natCard_tateCohomology_zero_of_cyclic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Shapiro's lemma in degree zero: `Ĥ⁰(G, Coind_H^G M) ≅ Ĥ⁰(H, M)`

For a finite group `G`, a subgroup `H ≤ G` and a `ℤ[H]`-module `M`, the degree-zero Tate
cohomology of the coinduced module coincides with that of `M`:

  `hZero (Rep.coind H.subtype M) = hZero M`.

Concretely `Ĥ⁰(G, N) = N^G ⧸ N_G(N)` and `Ĥ⁰(H, M) = M^H ⧸ N_H(M)`, so the statement is proved by
exhibiting the isomorphism

  `N^G ⧸ N_G(N) ≅ M^H ⧸ N_H(M)`,   `f ↦ f(1)`

where `N = Coind_H^G M = {f : G → M | f (h * g) = h • f g}`.  The two ingredients are

* `N.norm f` is the constant function with value `∑_{g : G} f g`
  (`coindRep_norm_val`), and
* for `f ∈ N` the sum `∑_{g : G} f g` equals `N_H (∑_{t : T} f t)` for any right transversal `T`
  of `H` in `G` (`coindRep_sum_eq_norm_sum`), which identifies the image of the norm with `N_H(M)`
  (`coindRep_exists_sum_eq_iff`).

The statement is first proved over an arbitrary commutative base ring `k`, where no diamond
between the two possible `ℤ`-module structures on a `Rep ℤ`-object can occur, and then specialised.

This is the degree-zero case of Shapiro's lemma for Tate cohomology (Neukirch–Schmidt–Wingberg,
*Cohomology of Number Fields*, Chapter I, §2; Milne, *Class Field Theory*, II.1.7), the input that
turns the local computations over decomposition groups into the global Herbrand-quotient
computation.
-/

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open CategoryTheory

namespace NK.GlobalCFTdeep.Herbrand

noncomputable section

variable {k : Type*} [CommRing k]

/-- `|Vᴳ ⧸ N(V)|`, the cardinality of the degree-zero Tate cohomology of a representation, in the
form in which it is used throughout the Herbrand development. -/
def hZeroGen {G : Type*} [Group G] [Fintype G] {V : Type*} [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) : ℕ :=
  Nat.card (ρ.invariants ⧸ (LinearMap.range ρ.norm).comap ρ.invariants.subtype)

section Coind

variable {G : Type*} [Group G] [Fintype G] {H : Subgroup G} [Fintype H]
variable {V : Type*} [AddCommGroup V] [Module k V]
variable (ρ : Representation k H V)

/-- The coinduction of `ρ` from `H` to `G`, as a representation of `G` on the `H`-equivariant
functions `G → V` (`h • f` is right translation of the argument). -/
abbrev coindRep : Representation k G ↥(Representation.coindV H.subtype ρ) :=
  Representation.coind H.subtype ρ

/-- The action on the coinduced representation is right translation of the argument. -/
lemma coindRep_apply_val (g x : G) (f : ↥(Representation.coindV H.subtype ρ)) :
    ((coindRep ρ g f).1 : G → V) x = (f.1 : G → V) (x * g) := rfl

/-- Membership in the coinduced module is `H`-equivariance. -/
lemma coindRep_equivariance (f : ↥(Representation.coindV H.subtype ρ)) (h : H) (g : G) :
    (f.1 : G → V) (↑h * g) = ρ h ((f.1 : G → V) g) :=
  (Representation.mem_coindV H.subtype ρ f.1).1 f.2 h g

/-- A `G`-invariant element of the coinduced module is a constant function. -/
lemma coindRep_const_of_mem_invariants (f : ↥(Representation.coindV H.subtype ρ))
    (hf : f ∈ (coindRep ρ).invariants) (g : G) :
    (f.1 : G → V) g = (f.1 : G → V) 1 := by
  have h : coindRep ρ g f = f := (Representation.mem_invariants _ f).1 hf g
  have h2 := congrArg (fun z : ↥(Representation.coindV H.subtype ρ) => (z.1 : G → V) 1) h
  rw [coindRep_apply_val, one_mul] at h2
  exact h2

/-- A constant function is `G`-invariant. -/
lemma coindRep_mem_invariants_of_const (f : ↥(Representation.coindV H.subtype ρ)) {c : V}
    (hf : ∀ x : G, (f.1 : G → V) x = c) : f ∈ (coindRep ρ).invariants := by
  rw [Representation.mem_invariants]
  intro g
  ext x
  rw [coindRep_apply_val, hf, hf]

/-- The value at `1` of a `G`-invariant element of the coinduced module is `H`-invariant. -/
lemma coindRep_invariants_val_mem (f : ↥(Representation.coindV H.subtype ρ))
    (hf : f ∈ (coindRep ρ).invariants) :
    (f.1 : G → V) 1 ∈ ρ.invariants := by
  rw [Representation.mem_invariants]
  intro h
  rw [← coindRep_equivariance ρ f h 1, mul_one,
    coindRep_const_of_mem_invariants ρ f hf (h : G)]

/-- The `k`-linear "evaluate at `1`" isomorphism from the `G`-invariants of the coinduced module
to the `H`-invariants of `V`.  Its inverse sends `c` to the constant function with value `c`. -/
noncomputable def coindInvEquiv : ↥(coindRep ρ).invariants ≃ₗ[k] ↥ρ.invariants where
  toFun f := ⟨(f.1.1 : G → V) 1, coindRep_invariants_val_mem ρ f.1 f.2⟩
  map_add' f g := by
    apply Subtype.ext
    rfl
  map_smul' a f := by
    apply Subtype.ext
    rfl
  invFun c := ⟨⟨fun _ : G => c.1, by
      rw [Representation.mem_coindV]
      intro h g
      exact ((Representation.mem_invariants _ c.1).1 c.2 h).symm⟩,
    coindRep_mem_invariants_of_const ρ _ (fun _ => rfl)⟩
  left_inv f := by
    apply Subtype.ext
    apply Subtype.ext
    funext g
    exact (coindRep_const_of_mem_invariants ρ f.1 f.2 g).symm
  right_inv c := by
    apply Subtype.ext
    rfl

/-- The norm of the coinduced representation is the constant function with value `∑_{g : G} f g`. -/
lemma coindRep_norm_val (f : ↥(Representation.coindV H.subtype ρ)) :
    (((coindRep ρ).norm f).1 : G → V) = fun _ : G => ∑ g : G, (f.1 : G → V) g := by
  funext x
  simp only [Representation.norm, LinearMap.sum_apply, Finset.sum_apply, Submodule.coe_sum,
    coindRep_apply_val]
  exact Fintype.sum_bijective (fun g : G => x * g) (Group.mulLeft_bijective x) _ _ (fun g => rfl)

/-- `H.norm v = ∑_{h : H} h • v`. -/
lemma coindRep_source_norm_apply (v : V) : ρ.norm v = ∑ h : ↥H, ρ h v := by
  simp only [Representation.norm, LinearMap.sum_apply]

/-- **The transversal formula.**  Writing `G` as the disjoint union of the right cosets `H * t`
for a right transversal `T` of `H`, the sum of the values of an `H`-equivariant `f : G → V`
over `G` is the `H`-norm of its sum over `T`. -/
lemma coindRep_sum_eq_norm_sum {T : Set G} [Fintype ↥T]
    (hT : Subgroup.IsComplement (H : Set G) T) (f : ↥(Representation.coindV H.subtype ρ)) :
    ∑ g : G, (f.1 : G → V) g = ρ.norm (∑ t : ↥T, (f.1 : G → V) (t : G)) := by
  have key : ∀ x : ↥H × ↥T, (f.1 : G → V) (↑x.1 * ↑x.2) = ρ x.1 ((f.1 : G → V) ↑x.2) :=
    fun x => coindRep_equivariance ρ f x.1 ↑x.2
  calc ∑ g : G, (f.1 : G → V) g
      = ∑ x : ↥H × ↥T, (f.1 : G → V) (↑x.1 * ↑x.2) := by
        refine Fintype.sum_equiv hT.equiv (fun g => (f.1 : G → V) g)
          (fun x : ↥H × ↥T => (f.1 : G → V) (↑x.1 * ↑x.2)) ?_
        intro g
        rw [Subgroup.IsComplement.equiv_fst_mul_equiv_snd hT g]
    _ = ∑ x : ↥H × ↥T, ρ x.1 ((f.1 : G → V) ↑x.2) := Finset.sum_congr rfl (fun x _ => key x)
    _ = ∑ h : ↥H, ∑ t : ↥T, ρ h ((f.1 : G → V) (t : G)) := Fintype.sum_prod_type _
    _ = ∑ t : ↥T, ∑ h : ↥H, ρ h ((f.1 : G → V) (t : G)) := Finset.sum_comm
    _ = ∑ t : ↥T, ρ.norm ((f.1 : G → V) (t : G)) := by
        refine Finset.sum_congr rfl (fun t _ => ?_)
        rw [coindRep_source_norm_apply]
    _ = ρ.norm (∑ t : ↥T, (f.1 : G → V) (t : G)) := by
        rw [map_sum]

/-- **The image of the norm.**  The set of sums `∑_{g : G} f g` over the `H`-equivariant
`f : G → V` is exactly the image of the norm `N_H : V → V`. -/
lemma coindRep_exists_sum_eq_iff {T : Set G} [Fintype ↥T]
    (hT : Subgroup.IsComplement (H : Set G) T) (h1T : 1 ∈ T) (c : V) :
    (∃ f : ↥(Representation.coindV H.subtype ρ), ∑ g : G, (f.1 : G → V) g = c) ↔
      c ∈ LinearMap.range ρ.norm := by
  classical
  constructor
  · rintro ⟨f, hf⟩
    exact ⟨∑ t : ↥T, (f.1 : G → V) (t : G),
      by rw [← coindRep_sum_eq_norm_sum ρ hT f]; exact hf⟩
  · intro hc
    obtain ⟨v, hv⟩ := hc
    let t₀ : ↥T := ⟨1, h1T⟩
    let w : ↥T → V := fun t => if t = t₀ then v else 0
    let f : G → V := fun g => ρ (hT.equiv g).1 (w (hT.equiv g).2)
    have hfmem : f ∈ Representation.coindV H.subtype ρ := by
      rw [Representation.mem_coindV]
      intro h g
      show ρ (hT.equiv (↑h * g)).1 (w (hT.equiv (↑h * g)).2)
        = ρ h (ρ (hT.equiv g).1 (w (hT.equiv g).2))
      rw [Subgroup.IsComplement.equiv_mul_left hT h g]
      simp only [map_mul, Module.End.mul_apply]
    refine ⟨⟨f, hfmem⟩, ?_⟩
    rw [coindRep_sum_eq_norm_sum ρ hT ⟨f, hfmem⟩]
    have hsum : ∑ t : ↥T, f t = v := by
      have hw : ∀ t : ↥T, f t = w t := by
        intro t
        have h1 : (hT.equiv (t : G)).2 = t :=
          Subgroup.IsComplement.equiv_snd_eq_self_of_mem_of_one_mem hT H.one_mem t.2
        have h2 : (hT.equiv (t : G)).1 = 1 := by
          have h := Subgroup.IsComplement.equiv_fst_mul_equiv_snd hT (t : G)
          rw [h1] at h
          exact Subtype.ext (mul_right_cancel (h.trans (one_mul (t : G)).symm))
        show ρ (hT.equiv (t : G)).1 (w (hT.equiv (t : G)).2) = w t
        rw [h1, h2]
        exact map_one ρ ▸ rfl
      calc ∑ t : ↥T, f t = ∑ t : ↥T, w t := Finset.sum_congr rfl (fun t _ => hw t)
        _ = v := by
            rw [Finset.sum_eq_single t₀]
            · simp [w, t₀]
            · intro b _ hb; simp [w, hb]
            · intro hh; exact absurd (Finset.mem_univ t₀) hh
    rw [hsum, hv]

/-- **The invariant quotients agree.**  The "evaluate at `1`" isomorphism carries the image of the
norm of the coinduced module onto the image of the norm of `V`. -/
lemma coindRep_map_comap_eq {T : Set G} [Fintype ↥T]
    (hT : Subgroup.IsComplement (H : Set G) T) (h1T : 1 ∈ T) :
    ((LinearMap.range (coindRep ρ).norm).comap (coindRep ρ).invariants.subtype).map
        (coindInvEquiv ρ : ↥(coindRep ρ).invariants →ₗ[k] ↥ρ.invariants) =
      (LinearMap.range ρ.norm).comap ρ.invariants.subtype := by
  classical
  ext y
  constructor
  · intro hy
    rw [Submodule.mem_map] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    rw [Submodule.mem_comap, LinearMap.mem_range] at hx ⊢
    obtain ⟨f, hf⟩ := hx
    have hxfun : (x.1.1 : G → V) = (((coindRep ρ).norm f).1 : G → V) :=
      congrArg (fun z : ↥(Representation.coindV H.subtype ρ) => (z.1 : G → V)) hf.symm
    have h1 : ((coindInvEquiv ρ) x).1 = ∑ g : G, (f.1 : G → V) g := by
      show (x.1.1 : G → V) 1 = _
      rw [hxfun, coindRep_norm_val]
    exact ⟨∑ t : ↥T, (f.1 : G → V) (t : G),
      by rw [← coindRep_sum_eq_norm_sum ρ hT f]; exact h1.symm⟩
  · intro hy
    rw [Submodule.mem_comap, LinearMap.mem_range] at hy
    obtain ⟨v, hv⟩ := hy
    rw [Submodule.mem_map]
    obtain ⟨f, hf⟩ := (coindRep_exists_sum_eq_iff ρ hT h1T (y : V)).2 ⟨v, hv⟩
    refine ⟨(coindInvEquiv ρ).symm y, ?_, (coindInvEquiv ρ).apply_symm_apply y⟩
    rw [Submodule.mem_comap, LinearMap.mem_range]
    refine ⟨f, ?_⟩
    apply Subtype.ext
    rw [coindRep_norm_val]
    funext x
    exact hf

/-- **Shapiro's lemma in degree zero, for an arbitrary commutative base ring.** -/
theorem hZeroGen_coind : hZeroGen (coindRep ρ) = hZeroGen ρ := by
  classical
  obtain ⟨T, hT, h1T⟩ := Subgroup.exists_isComplement_right H 1
  haveI : Fintype ↥T := Fintype.ofFinite _
  rw [hZeroGen, hZeroGen]
  exact Nat.card_congr
    (Submodule.Quotient.equiv _ _ (coindInvEquiv ρ) (coindRep_map_comap_eq ρ hT h1T)).toEquiv

end Coind

end

end NK.GlobalCFTdeep.Herbrand

namespace NK.GlobalCFTdeep.Herbrand

/-- **Shapiro's lemma in degree zero** for a finite group `G`, a subgroup `H ≤ G` and a
`ℤ[H]`-module `M`: the degree-zero Tate cohomology of the coinduced module `Coind_H^G M` is that
of `M`.

The proof reduces both sides, through
`Commons.RepresentationTheory.GroupCohomology.tateCohomology_zero_iso_general`, to the cardinality
of the invariants modulo the image of the norm, and then applies the generic Shapiro computation
`hZeroGen_coind`.  The local `Module ℤ` instances are pinned to the ones carried by the `Rep`
structures (`Rep.hV2`), because the `ℤ`-module structure on a `Rep ℤ`-object is a diamond
(`Rep.hV2` versus `AddCommGroup.toIntModule`). -/
theorem hZero_coind {G : Type} [Group G] [Fintype G] (H : Subgroup G) [Fintype H]
    (M : Rep ℤ H) :
    hZero (Rep.coind H.subtype M) = hZero M := by
  letI : Module ℤ M.V := M.hV2
  letI : Module ℤ ↥(Representation.coindV H.subtype M.ρ) :=
    (Representation.coindV H.subtype M.ρ).module
  letI : Module ℤ (Rep.coind H.subtype M).V := (Rep.coind H.subtype M).hV2
  have keyM : hZero M = hZeroGen M.ρ := by
    obtain ⟨e⟩ := Commons.RepresentationTheory.GroupCohomology.tateCohomology_zero_iso_general
      (k := ℤ) (G := ↥H) M.ρ
    have h : Nat.card (tateCohomology (Rep.of M.ρ) 0) = hZeroGen M.ρ := Nat.card_congr e.toEquiv
    have hrep : Rep.of M.ρ = M := rfl
    rw [hrep] at h
    rw [hZero]
    exact h
  have keyN : hZero (Rep.coind H.subtype M)
      = hZeroGen (Representation.coind H.subtype M.ρ) := by
    obtain ⟨e⟩ := Commons.RepresentationTheory.GroupCohomology.tateCohomology_zero_iso_general
      (k := ℤ) (G := G) (Rep.coind H.subtype M).ρ
    have h : Nat.card (tateCohomology (Rep.of (Rep.coind H.subtype M).ρ) 0)
        = hZeroGen (Representation.coind H.subtype M.ρ) := Nat.card_congr e.toEquiv
    have hrep : Rep.of (Rep.coind H.subtype M).ρ = Rep.coind H.subtype M := rfl
    rw [hrep] at h
    rw [hZero]
    exact h
  rw [keyN, keyM]
  exact hZeroGen_coind (H := H) M.ρ

end NK.GlobalCFTdeep.Herbrand
