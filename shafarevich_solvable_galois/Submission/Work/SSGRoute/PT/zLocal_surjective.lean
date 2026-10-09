import Mathlib
import Submission.Work.SSGRoute.PT.archPairLocal
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.PT

set_option backward.isDefEq.respectTransparency false

/-- **The descent `PT.zLocal` is onto.**  Every class `z ∈ H¹(D_u, PT.zRep …)` is the class of a
descended cocycle: the pullback `b ↦ bDaux_b` identifies the `⟨c⟩`-cocycles with the `D_u`-cocycles
(`res_L : ⟨c⟩ → D_u` is injective because `hres`, and onto by `hDu`), and `H1π`/`eCoh` are additive
with `H1π` carrying cocycles to classes.  This is the hypothesis `(P3)` of the clause-(4)
perfectness assembly `PT.archPairLocal_perfect`.

Route (both reviewers confirmed).  `zLocal b = eCoh 1 (decompK u) zRep (H1π ⟨bDaux b, _⟩)`: `eCoh` is
an `AddEquiv` (hence onto) and `H1π : Z¹ → H¹` is `QuotientAddGroup.mk'`, hence onto, so it suffices
to hit every `f ∈ Z¹(D_u, zRep)`; for that take `b := f ∘ res k L` (a `⟨c⟩`-cocycle, the compatibility
`decompKRestrict ∘ res k L = res k K` being `rfl`-checkable) and use `bDaux_spec` — which pins
`bDaux b` on all of `D_u = (⟨c⟩).map (res k L)` (`hDu`) — to conclude `bDaux b = f`.  The
`⟨c⟩`-cocycle condition for `b` is the cocycle condition of `f` transported across that
compatibility; `hres` (injectivity of `res k L` on `{1,c}`) and `hDu` are used only here. -/
theorem zLocal_surjective
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (c : Ω ≃ₐ[k] Ω) (hc2 : c ^ 2 = 1)
    (L : IntermediateField k Ω) [NumberField ↥L] [FiniteDimensional k ↥L] [IsGalois k ↥L]
    (hKL : K ≤ L) [Algebra ↥K ↥L] [IsScalarTower k ↥K ↥L] [IsScalarTower ↥K ↥L Ω]
    (hres : SSGRoute.res k L c ≠ 1)
    (u : NK.GlobalCFT.Place ↥L)
    (hDu : SSGRoute.PTExt.decompK (k := k) u = (Subgroup.zpowers c).map (SSGRoute.res k L))
    (w : NK.GlobalCFT.Place ↥K) (hu : NK.GlobalCFT.Place.LiesOver u w) :
    ∀ z : SSGRoute.PTExt.extH (zRep p k Ω K T M L u w hu) 1,
      ∃ (b : (Ω ≃ₐ[k] Ω) → VFcoef p M T)
        (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b),
        zLocal p k Ω K T M c hc2 L hKL hres u hDu b hb w hu = z := by
  classical
  intro z
  -- A `D_{u_c}`-cocycle representative of `z` (surjectivity of `H1π`).
  obtain ⟨f, hf⟩ := groupCohomology.H1_induction_on
    (A := zRep p k Ω K T M L u w hu)
    (C := fun y => ∃ f : ↥(groupCohomology.cocycles₁ (zRep p k Ω K T M L u w hu)),
      (groupCohomology.H1π (zRep p k Ω K T M L u w hu)).hom f = y)
    ((SSGRoute.PTExt.eCoh 1 ↥(SSGRoute.PTExt.decompK (k := k) u)
        (zRep p k Ω K T M L u w hu)).symm z)
    (fun f => ⟨f, rfl⟩)
  -- The `⟨c⟩`-cocycle obtained by pulling `f` back along `res_L`.
  let b : (Ω ≃ₐ[k] Ω) → VFcoef p M T := fun σ =>
    if h : σ ∈ Subgroup.zpowers c
    then f ⟨SSGRoute.res k L σ, by rw [hDu]; exact Subgroup.mem_map_of_mem _ h⟩
    else 0
  have hbval : ∀ (σ : Ω ≃ₐ[k] Ω) (hσ : σ ∈ Subgroup.zpowers c),
      b σ = f ⟨SSGRoute.res k L σ, by rw [hDu]; exact Subgroup.mem_map_of_mem _ hσ⟩ := by
    intro σ hσ
    dsimp only [b]
    exact dif_pos hσ
  -- The `zRep`-action at `res_L σ` is the `res_K σ`-action on the coefficient module.
  have hact : ∀ (σ : Ω ≃ₐ[k] Ω) (hσ : σ ∈ Subgroup.zpowers c) (x : VFcoef p M T),
      (zRep p k Ω K T M L u w hu).ρ
          ⟨SSGRoute.res k L σ, by rw [hDu]; exact Subgroup.mem_map_of_mem _ hσ⟩ x
        = SSGRoute.res k K σ • x := by
    intro σ hσ x
    rw [show SSGRoute.res k K σ
          = SSGRoute.PTExt.galRes k (↥K) (↥L) (SSGRoute.res k L σ)
        from IsScalarTower.AlgEquiv.restrictNormalHom_comp_apply (↥K) (↥L) σ]
    rfl
  -- `b` is a `⟨c⟩`-cocycle, by transport of `f`'s cocycle condition along `res_L`.
  have hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b := by
    intro g hg h hh
    have h1 : b (g * h) = f ((⟨SSGRoute.res k L g,
            by rw [hDu]; exact Subgroup.mem_map_of_mem _ hg⟩ : ↥(SSGRoute.PTExt.decompK (k := k) u))
          * ⟨SSGRoute.res k L h, by rw [hDu]; exact Subgroup.mem_map_of_mem _ hh⟩) := by
      rw [hbval (g * h) (mul_mem hg hh)]
      congr 1
      exact Subtype.ext (map_mul (SSGRoute.res k L) g h)
    have h2 : (f ((⟨SSGRoute.res k L g,
            by rw [hDu]; exact Subgroup.mem_map_of_mem _ hg⟩ : ↥(SSGRoute.PTExt.decompK (k := k) u))
          * ⟨SSGRoute.res k L h, by rw [hDu]; exact Subgroup.mem_map_of_mem _ hh⟩) : VFcoef p M T)
        = (zRep p k Ω K T M L u w hu).ρ ⟨SSGRoute.res k L g,
              by rw [hDu]; exact Subgroup.mem_map_of_mem _ hg⟩
            (f ⟨SSGRoute.res k L h, by rw [hDu]; exact Subgroup.mem_map_of_mem _ hh⟩)
          + (f ⟨SSGRoute.res k L g, by rw [hDu]; exact Subgroup.mem_map_of_mem _ hg⟩
              : VFcoef p M T) :=
      (groupCohomology.mem_cocycles₁_iff (A := zRep p k Ω K T M L u w hu) f).1 f.2
        ⟨SSGRoute.res k L g, by rw [hDu]; exact Subgroup.mem_map_of_mem _ hg⟩
        ⟨SSGRoute.res k L h, by rw [hDu]; exact Subgroup.mem_map_of_mem _ hh⟩
    rw [h1, h2,
      hact g hg (f ⟨SSGRoute.res k L h, by rw [hDu]; exact Subgroup.mem_map_of_mem _ hh⟩),
      hbval g hg, hbval h hh]
    exact add_comm _ _
  -- `bDaux b` agrees with `f` on the image of `⟨c⟩`.
  have hkey : ∀ (σ : ↥(Subgroup.zpowers c)),
      (bDaux p k Ω K T M c hc2 L hKL hres u hDu b hb w hu
          ⟨SSGRoute.res k L σ.1, by rw [hDu]; exact Subgroup.mem_map_of_mem _ σ.2⟩ : VFcoef p M T)
        = f ⟨SSGRoute.res k L σ.1, by rw [hDu]; exact Subgroup.mem_map_of_mem _ σ.2⟩ := by
    intro σ
    rw [(bDaux_spec p k Ω K T M c hc2 L hKL hres u hDu b hb w hu).2 σ, hbval σ.1 σ.2]
  -- ... hence on all of `D_{u_c} = (⟨c⟩).map (res_L)`, so `bDaux b = f`.
  have hfun : ∀ g : ↥(SSGRoute.PTExt.decompK (k := k) u),
      bDaux p k Ω K T M c hc2 L hKL hres u hDu b hb w hu g = f g := by
    intro g
    obtain ⟨σ, hσ, hσeq⟩ := Subgroup.mem_map.mp (by rw [← hDu]; exact g.2)
    rw [show g = (⟨SSGRoute.res k L σ,
        by rw [hDu]; exact Subgroup.mem_map_of_mem _ hσ⟩ : ↥(SSGRoute.PTExt.decompK (k := k) u))
      from Subtype.ext hσeq.symm]
    exact hkey ⟨σ, hσ⟩
  refine ⟨b, hb, ?_⟩
  have h1 : (⟨bDaux p k Ω K T M c hc2 L hKL hres u hDu b hb w hu,
      bDaux_mem p k Ω K T M c hc2 L hKL hres u hDu b hb w hu⟩
      : ↥(groupCohomology.cocycles₁ (zRep p k Ω K T M L u w hu))) = f :=
    Subtype.ext (funext hfun)
  simp only [zLocal]
  rw [h1, hf]
  exact AddEquiv.apply_symm_apply _ z

end Work.SSGRoute.PT
