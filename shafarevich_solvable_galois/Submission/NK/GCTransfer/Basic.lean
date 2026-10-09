/-
The general form of the restriction theorem for `H²`: for an injective group homomorphism
`f : Δ →* Γ` whose image has index prime to `p`, restriction of `H²(Γ, A)` to `H²(Δ, Res f A)` is
injective on `p`-torsion coefficient modules.

The proof is carried out at the level of `2`-cocycles: a coboundary on `Δ` witnessing the vanishing
of the restricted class is transported to a primitive of the restriction of the cocycle to the
image `S = range f` (using that `f` is injective, so that `Δ ≃* S`), and then the transfer identity
`NK.GCTransfer.exists_coboundary_index_nsmul` produces a primitive of `[Γ : S] • z`.
-/
import Submission.NK.GCTransfer.Transfer
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open CategoryTheory Representation Rep

set_option autoImplicit false
set_option maxHeartbeats 1600000

universe u

namespace NK.GCTransfer

variable {k : Type u} [CommRing k] {Γ : Type u} [Group Γ]

section CocyclesMap

variable {Δ : Type u} [Group Δ] (f : Δ →* Γ) {A : Rep.{u,u,u} k Γ} {N : Rep.{u,u,u} k Δ}
  (φ : Rep.res f A ⟶ N)

/-- The map on `2`-cocycles induced by a group homomorphism `f` and a coefficient morphism `φ`,
evaluated at a pair: it is the evident pullback `(a,b) ↦ φ (w (f a, f b))`. -/
lemma mapCocycles₂_apply (w : groupCohomology.cocycles₂ A) (a b : Δ) :
    (groupCohomology.mapCocycles₂ f φ w) (a, b) = φ (w (f a, f b)) := by
  rw [groupCohomology.coe_mapCocycles₂]
  have h : (groupCohomology.cochainsMap₂ f φ) ⇑w
      = fun q : Δ × Δ => φ (w (f q.1, f q.2)) := by
    funext q
    obtain ⟨a, b⟩ := q
    simp only [groupCohomology.cochainsMap₂, LinearMap.comp_apply, LinearMap.compLeft_apply,
      LinearMap.funLeft_apply, Prod.map_apply, Function.comp_apply, ModuleCat.hom_ofHom]
    rfl
  rw [h]

end CocyclesMap

/-- If the coefficient module is `p`-torsion then `p` acts as zero on `H²`. -/
theorem p_nsmul_eq_zero (p : ℕ) (A : Rep.{u,u,u} k Γ) (htor : ∀ m : A, p • m = 0)
    (x : groupCohomology A 2) : p • x = 0 := by
  refine groupCohomology.H2_induction_on (A := A) x ?_
  intro w
  have hpw : p • w = 0 := by
    refine groupCohomology.cocycles₂_ext (fun a b => ?_)
    show (p • w) (a, b) = (0 : groupCohomology.cocycles₂ A) (a, b)
    have h1 : ((p • w : groupCohomology.cocycles₂ A) : Γ × Γ → A) = p • ((w : Γ × Γ → A)) := rfl
    rw [h1, Pi.smul_apply, htor]
    rfl
  rw [← map_nsmul, hpw, map_zero]

/-- Two coprime integers which both annihilate an element annihilate it trivially. -/
theorem eq_zero_of_coprime_nsmul_eq_zero {M : Type u} [AddCommMonoid M] {m p : ℕ} {x : M}
    (hcop : Nat.Coprime m p) (h1 : m • x = 0) (h2 : p • x = 0) : x = 0 := by
  have h1' : addOrderOf x ∣ m := addOrderOf_dvd_iff_nsmul_eq_zero.mpr h1
  have h2' : addOrderOf x ∣ p := addOrderOf_dvd_iff_nsmul_eq_zero.mpr h2
  have h3 : addOrderOf x ∣ m.gcd p := Nat.dvd_gcd h1' h2'
  rw [hcop.gcd_eq_one] at h3
  exact AddMonoid.addOrderOf_eq_one_iff.mp (Nat.dvd_one.mp h3)

section Main

variable {Δ : Type u} [Group Δ] [Fintype Γ]

/-- **Restriction is injective on `H²` for an injective homomorphism of index prime to `p`.**

If `f : Δ →* Γ` is injective, the index of its image in `Γ` is prime to `p`, and the coefficients
`A` are `p`-torsion, then `H²(Γ, A) → H²(Δ, Res f A)` is injective.  (The coefficient morphism is
allowed to be an arbitrary isomorphism of representations.) -/
theorem map_injective_of_coprime_index (p : ℕ) (f : Δ →* Γ) (hf : Function.Injective f)
    (A : Rep.{u,u,u} k Γ) (N : Rep.{u,u,u} k Δ) (φ : Rep.res f A ⟶ N) [IsIso φ]
    (hcop : Nat.Coprime (Subgroup.index (MonoidHom.range f)) p)
    (htor : ∀ m : A, p • m = 0) :
    Function.Injective (fun x : groupCohomology A 2 => (groupCohomology.map f φ 2).hom x) := by
  have key : ∀ z : groupCohomology A 2, (groupCohomology.map f φ 2).hom z = 0 → z = 0 := by
    intro z hz
    revert hz
    refine groupCohomology.H2_induction_on (A := A) z ?_
    intro w hz
    have hz' : (groupCohomology.H2π N) ((groupCohomology.mapCocycles₂ f φ) w) = 0 := by
      rw [← groupCohomology.H2π_comp_map_apply f φ w]
      exact hz
    obtain ⟨β, hβ⟩ := LinearMap.mem_range.mp ((groupCohomology.H2π_eq_zero_iff _).mp hz')
    obtain ⟨ψ, hψ1, hψ2⟩ := CategoryTheory.IsIso.out (f := φ)
    have hψa : ∀ y : Rep.res f A, ψ (φ y) = y := by
      intro y
      have h := congrArg (fun (κ : Rep.res f A ⟶ Rep.res f A) => κ y) hψ1
      rwa [Rep.comp_apply, Rep.id_apply] at h
    have hφb : ∀ y : N, φ (ψ y) = y := by
      intro y
      have h := congrArg (fun (κ : N ⟶ N) => κ y) hψ2
      rwa [Rep.comp_apply, Rep.id_apply] at h
    have hψint : ∀ (a : Δ) (y : N), ψ (N.ρ a y) = A.ρ (f a) (ψ y) := by
      intro a y
      have h := Rep.hom_comm_apply ψ a y
      simpa using h
    let β' : Δ → A := fun a => ψ (β a)
    have hβ' : ∀ a b : Δ, A.ρ (f a) (β' b) - β' (a * b) + β' a = w (f a, f b) := by
      intro a b
      have h1 : N.ρ a (β b) - β (a * b) + β a = φ (w (f a, f b)) := by
        have h := congrFun hβ (a, b)
        rw [groupCohomology.d₁₂_hom_apply, mapCocycles₂_apply f φ w a b] at h
        exact h
      have h2 : ψ (N.ρ a (β b)) - ψ (β (a * b)) + ψ (β a) = ψ (φ (w (f a, f b))) := by
        have h := congrArg (fun t => ψ t) h1
        rwa [show ψ (N.ρ a (β b) - β (a * b) + β a) =
          ψ (N.ρ a (β b)) - ψ (β (a * b)) + ψ (β a) from by simp] at h
      rw [hψint a (β b), hψa] at h2
      simpa [β'] using h2
    have hbij : Function.Bijective f.rangeRestrict :=
      ⟨fun a b hab => hf (Subtype.ext_iff.mp hab), f.rangeRestrict_surjective⟩
    let e : Δ ≃* MonoidHom.range f := MulEquiv.ofBijective f.rangeRestrict hbij
    let b' : MonoidHom.range f → A := fun s => β' (e.symm s)
    have hb' : ∀ s t : MonoidHom.range f,
        w ((s : Γ), (t : Γ))
          = (groupCohomology.d₁₂ (Rep.res (MonoidHom.range f).subtype A)).hom b' (s, t) := by
      intro s t
      have hs : f (e.symm s) = (s : Γ) := by
        have h : e (e.symm s) = s := MulEquiv.apply_symm_apply e s
        have h2 := MulEquiv.ofBijective_apply f.rangeRestrict hbij (e.symm s)
        rw [h2] at h
        exact congrArg Subtype.val h
      have ht : f (e.symm t) = (t : Γ) := by
        have h : e (e.symm t) = t := MulEquiv.apply_symm_apply e t
        have h2 := MulEquiv.ofBijective_apply f.rangeRestrict hbij (e.symm t)
        rw [h2] at h
        exact congrArg Subtype.val h
      have hst : e.symm (s * t) = e.symm s * e.symm t := map_mul e.symm s t
      calc w ((s : Γ), (t : Γ))
          = w (f (e.symm s), f (e.symm t)) := by rw [hs, ht]
        _ = A.ρ (f (e.symm s)) (β' (e.symm t)) - β' (e.symm s * e.symm t) + β' (e.symm s) :=
              (hβ' (e.symm s) (e.symm t)).symm
        _ = A.ρ (s : Γ) (β' (e.symm t)) - β' (e.symm (s * t)) + β' (e.symm s) := by
              rw [hs, ← hst]
        _ = (groupCohomology.d₁₂ (Rep.res (MonoidHom.range f).subtype A)).hom b' (s, t) := by
              rw [groupCohomology.d₁₂_hom_apply, Rep.coe_res_obj_ρ']
              simp only [b', Subgroup.coe_subtype]
    obtain ⟨B, hB⟩ := exists_coboundary_index_nsmul (MonoidHom.range f) A w b' hb'
    have hmem : ⇑((Subgroup.index (MonoidHom.range f)) • w)
        ∈ groupCohomology.coboundaries₂ A := by
      refine LinearMap.mem_range.mpr ⟨B, ?_⟩
      funext q
      obtain ⟨σ, τ⟩ := q
      exact hB σ τ
    have hzero : (Subgroup.index (MonoidHom.range f)) • ((groupCohomology.H2π A) w) = 0 := by
      have h := (groupCohomology.H2π_eq_zero_iff (A := A) _).mpr hmem
      rwa [map_nsmul] at h
    exact eq_zero_of_coprime_nsmul_eq_zero hcop hzero (p_nsmul_eq_zero p A htor _)
  intro x y hxy
  have hxy' : (groupCohomology.map f φ 2).hom x = (groupCohomology.map f φ 2).hom y := hxy
  have h0 : (groupCohomology.map f φ 2).hom (x - y) = 0 := by
    rw [map_sub, hxy', sub_self]
  exact sub_eq_zero.mp (key (x - y) h0)

end Main

end NK.GCTransfer
