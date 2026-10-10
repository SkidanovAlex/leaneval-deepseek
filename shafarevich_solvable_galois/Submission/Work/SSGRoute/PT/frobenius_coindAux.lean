import Mathlib.GroupTheory.Index
import Mathlib.Tactic.Group
import Mathlib.Algebra.BigOperators.Pi
import Submission.Work.SSGRoute.PT.AlphaPairing
import Submission.Work.SSGRoute.PT.coindEquivFun
import Submission.Work.SSGRoute.PT.shapiro_H2_coind
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Frobenius reciprocity for the coinduced module, `G`-equivariantly

For a group `G`, a finite-index subgroup `U ≤ G`, a `U`-module `M` (written additively) and a
`G`-module `C`, the additive group of `ℤ`-linear maps out of the coinduced module
`Coind^G_U M` (with the conjugation action, packaged as `ConjHom`) is isomorphic, as a
`G`-module, to the coinduced module of the coefficient module `Hom_ℤ(M,C)`:

  `ConjHom (Coind^G_U M) C ≃+ Coind^G_U (ConjHom M C)`.

This is the `G`-equivariant refinement of `Work.SSGRoute.PT.coindHomEquiv`.  The isomorphism is
the classical Shapiro formula written on the group: the `g`-th coordinate of the image of `Φ` is
`m ↦ g⁻¹ • Φ(θ_{g,m})`, where `θ_{g,m} ∈ Coind^G_U M` is the "delta" element supported on the
coset `gU` with `θ_{g,m} g = m` (explicitly `θ_{g,m}(x) = (g⁻¹x)⁻¹ • m` if `g⁻¹x ∈ U` and `0`
otherwise).  The `θ_{g,m}`, for `g` running over a set of coset representatives and `m ∈ M`, span
the coinduced module, which is what makes the formula bijective.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

open Classical

namespace Work.SSGRoute.PT

noncomputable section

variable {G : Type*} [Group G] (U : Subgroup G)
  {M : Type*} [AddCommGroup M] [DistribMulAction U M]

/-! ## The delta elements of `Coind G U M` -/

/-- The function underlying the "delta" element of `Coind G U M` supported on the coset `gU`:
`θ_{g,m}(x) = (g⁻¹x)⁻¹ • m` if `g⁻¹x ∈ U`, and `0` otherwise. -/
def thetaAuxFun (g : G) (m : M) : G → M :=
  fun x => if h : g⁻¹ * x ∈ U then (⟨g⁻¹ * x, h⟩ : U)⁻¹ • m else 0

@[simp] theorem thetaAuxFun_apply (g : G) (m : M) (x : G) :
    thetaAuxFun U g m x = if h : g⁻¹ * x ∈ U then (⟨g⁻¹ * x, h⟩ : U)⁻¹ • m else 0 := rfl

theorem thetaAuxFun_add (g : G) (m₁ m₂ : M) :
    thetaAuxFun U g (m₁ + m₂) = thetaAuxFun U g m₁ + thetaAuxFun U g m₂ := by
  funext x
  simp only [thetaAuxFun_apply, Pi.add_apply]
  by_cases h : g⁻¹ * x ∈ U
  · rw [dif_pos h, dif_pos h, dif_pos h, smul_add]
  · rw [dif_neg h, dif_neg h, dif_neg h, add_zero]

theorem thetaAuxFun_zero (g : G) : thetaAuxFun U g (0 : M) = 0 := by
  funext x
  simp only [thetaAuxFun_apply]
  by_cases h : g⁻¹ * x ∈ U
  · rw [dif_pos h, smul_zero]; rfl
  · rw [dif_neg h]; rfl

theorem thetaAuxFun_mem (g : G) (m : M) : thetaAuxFun U g m ∈ coindSub G U M := by
  intro x u
  rw [thetaAuxFun_apply, thetaAuxFun_apply]
  by_cases h : g⁻¹ * x ∈ U
  · have h' : g⁻¹ * (x * (u : G)) ∈ U := by
      have : g⁻¹ * (x * (u : G)) = (g⁻¹ * x) * (u : G) := by group
      rw [this]; exact U.mul_mem h u.2
    rw [dif_pos h, dif_pos h']
    have hval : (⟨g⁻¹ * (x * (u : G)), h'⟩ : U) = (⟨g⁻¹ * x, h⟩ : U) * u := by
      refine Subtype.ext ?_
      show g⁻¹ * (x * (u : G)) = (g⁻¹ * x) * (u : G)
      group
    rw [hval, mul_inv_rev, mul_smul]
  · have h' : g⁻¹ * (x * (u : G)) ∉ U := by
      intro hh
      apply h
      have : g⁻¹ * x = (g⁻¹ * (x * (u : G))) * (u : G)⁻¹ := by group
      rw [this]; exact U.mul_mem hh (U.inv_mem u.2)
    rw [dif_neg h, dif_neg h', smul_zero]

/-- The delta elements, as an additive map in the value `m`. -/
def thetaAuxHom (g : G) : M →+ Coind G U M where
  toFun m := ⟨thetaAuxFun U g m, thetaAuxFun_mem U g m⟩
  map_zero' := by
    apply Subtype.ext
    change thetaAuxFun U g 0 = (0 : G → M)
    exact thetaAuxFun_zero U g
  map_add' m₁ m₂ := by
    apply Subtype.ext
    change thetaAuxFun U g (m₁ + m₂) = (thetaAuxFun U g m₁ + thetaAuxFun U g m₂)
    exact thetaAuxFun_add U g m₁ m₂

/-- The "delta" element of `Coind G U M` supported on the coset `gU` with `θ_{g,m} g = m`. -/
abbrev thetaAux (g : G) (m : M) : Coind G U M := thetaAuxHom U g m

@[simp] theorem thetaAux_apply (g : G) (m : M) (x : G) :
    thetaAux U g m x = if h : g⁻¹ * x ∈ U then (⟨g⁻¹ * x, h⟩ : U)⁻¹ • m else 0 := rfl

theorem thetaAux_add (g : G) (m₁ m₂ : M) :
    thetaAux U g (m₁ + m₂) = thetaAux U g m₁ + thetaAux U g m₂ := (thetaAuxHom U g).map_add m₁ m₂

theorem thetaAux_apply_eq_zero {g x : G} {m : M} (h : g⁻¹ * x ∉ U) : thetaAux U g m x = 0 := by
  rw [thetaAux_apply]; exact dif_neg h

/-- On the coset of `g`, the delta element `θ_{g,m}` evaluates to `u⁻¹ • m` at `g * u`. -/
theorem thetaAux_apply_mul_U (g : G) (m : M) (u : U) :
    thetaAux U g m (g * (u : G)) = u⁻¹ • m := by
  rw [thetaAux_apply]
  have h' : g⁻¹ * (g * (u : G)) ∈ U := by
    have : g⁻¹ * (g * (u : G)) = (u : G) := by group
    rw [this]; exact u.2
  rw [dif_pos h']
  have hval : (⟨g⁻¹ * (g * (u : G)), h'⟩ : U) = u := by
    refine Subtype.ext ?_
    show g⁻¹ * (g * (u : G)) = (u : G)
    group
  rw [hval]

/-- The delta elements are compatible with the `G`-action: `x • θ_{g,m} = θ_{xg,m}`. -/
theorem thetaAux_smul (x g : G) (m : M) : x • thetaAux U g m = thetaAux U (x * g) m := by
  refine Subtype.ext (funext fun y => ?_)
  rw [Coind.smul_apply, thetaAux_apply, thetaAux_apply]
  have hkey : (x * g)⁻¹ * y = g⁻¹ * (x⁻¹ * y) := by group
  rw [hkey]

/-- `θ_{gu,m} = θ_{g,u•m}`: the delta elements respect right translation by `U`. -/
theorem thetaAux_mul_U (g : G) (u : U) (m : M) : thetaAux U (g * (u : G)) m = thetaAux U g (u • m) := by
  refine Subtype.ext (funext fun x => ?_)
  rw [thetaAux_apply, thetaAux_apply]
  by_cases h : g⁻¹ * x ∈ U
  · have h' : (g * (u : G))⁻¹ * x ∈ U := by
      have : (g * (u : G))⁻¹ * x = u⁻¹ * (g⁻¹ * x) := by
        rw [Subgroup.coe_inv]; group
      rw [this]; exact U.mul_mem (U.inv_mem u.2) h
    rw [dif_pos h, dif_pos h']
    have hval : (⟨(g * (u : G))⁻¹ * x, h'⟩ : U) = u⁻¹ * (⟨g⁻¹ * x, h⟩ : U) := by
      refine Subtype.ext ?_
      show (g * (u : G))⁻¹ * x = (u⁻¹ : U) * (⟨g⁻¹ * x, h⟩ : U)
      rw [Subgroup.coe_inv]; group
    rw [hval, mul_inv_rev, inv_inv, mul_smul]
  · have h' : (g * (u : G))⁻¹ * x ∉ U := by
      intro hh
      apply h
      have : g⁻¹ * x = (u : G) * ((g * (u : G))⁻¹ * x) := by group
      rw [this]; exact U.mul_mem u.2 hh
    rw [dif_neg h, dif_neg h']

/-! ## The spanning identity -/

/-- Evaluation of the delta element at the chosen representative of `mk x`. -/
theorem thetaAux_apply_out (f : Coind G U M) (x : G) :
    thetaAux U ((QuotientGroup.mk x : G ⧸ U)).out (f ((QuotientGroup.mk x : G ⧸ U)).out) x = f x := by
  set q : G ⧸ U := QuotientGroup.mk x with hq
  set r : U := Coind.rep G U x with hr
  have hout : q.out = x * (r : G) := by
    rw [hq, hr]; exact Coind.rep_spec G U x
  have hx : x = q.out * ((r⁻¹ : U) : G) := by
    rw [hout, Subgroup.coe_inv]; group
  rw [hx, thetaAux_apply_mul_U, Coind.coe_mul]

section Spanning

variable [Fintype (G ⧸ U)]

/-- The delta elements span: a coinduced function is the sum of its "deltas" on coset
representatives. -/
theorem thetaAux_spanning (f : Coind G U M) :
    f = ∑ q : G ⧸ U, thetaAux U q.out (f q.out) := by
  refine Subtype.ext ?_
  have hsum : ((∑ q : G ⧸ U, thetaAux U q.out (f q.out) : Coind G U M) : G → M)
      = ∑ q : G ⧸ U, (thetaAux U q.out (f q.out) : G → M) :=
    map_sum (AddSubgroup.subtype (coindSub G U M)) _ Finset.univ
  rw [hsum]
  funext x
  rw [Finset.sum_apply]
  have h1 : ∀ b ∈ (Finset.univ : Finset (G ⧸ U)), b ≠ (QuotientGroup.mk x : G ⧸ U) →
      (↑(thetaAux U b.out (f b.out)) : G → M) x = 0 := by
    intro b _ hb
    show thetaAux U b.out (f b.out) x = 0
    apply thetaAux_apply_eq_zero
    intro hmem
    refine hb ?_
    have hx : x = b.out * ((⟨b.out⁻¹ * x, hmem⟩ : U) : G) := by
      show x = b.out * (b.out⁻¹ * x)
      group
    rw [← QuotientGroup.out_eq' b, hx, QuotientGroup.mk_mul_of_mem b.out hmem,
      QuotientGroup.out_eq']
  have h2 : (QuotientGroup.mk x : G ⧸ U) ∉ (Finset.univ : Finset (G ⧸ U)) →
      (↑(thetaAux U ((QuotientGroup.mk x : G ⧸ U)).out (f ((QuotientGroup.mk x : G ⧸ U)).out)) :
        G → M) x = 0 :=
    fun h => absurd (Finset.mem_univ _) h
  rw [Finset.sum_eq_single (QuotientGroup.mk x : G ⧸ U) h1 h2]
  simpa using (thetaAux_apply_out U f x).symm

end Spanning

/-! ## The `G`-equivariant map `ConjHom (Coind M) C → Coind (ConjHom M C)` -/

variable {C : Type*} [AddCommGroup C] [DistribMulAction G C]

/-- The `g`-th coordinate of the image of `Φ : Hom_ℤ(Coind^G_U M, C)`: the additive map
`m ↦ g⁻¹ • Φ (θ_{g,m})`. -/
def psiAuxFun (Φ : ConjHom (Coind G U M) C) (g : G) : ConjHom M C :=
  ⟨{ toFun := fun m => g⁻¹ • Φ (thetaAux U g m)
     map_zero' := by simp
     map_add' := by
       intro m₁ m₂
       simp only [map_add, smul_add] }⟩

@[simp] theorem psiAuxFun_apply (Φ : ConjHom (Coind G U M) C) (g : G) (m : M) :
    psiAuxFun U Φ g m = g⁻¹ • Φ (thetaAux U g m) := rfl

/-- The Shapiro/Frobenius map `Hom_ℤ(Coind^G_U M, C) → Coind^G_U Hom_ℤ(M,C)`. -/
def psiAux (Φ : ConjHom (Coind G U M) C) : Coind G U (ConjHom M C) :=
  ⟨fun g => psiAuxFun U Φ g, by
    intro g u
    refine ConjHom.ext_apply fun m => ?_
    rw [psiAuxFun_apply, ConjHom.smul_apply, psiAuxFun_apply, inv_inv, thetaAux_mul_U, mul_inv_rev,
      mul_smul, Subgroup.smul_def, Subgroup.coe_inv]⟩

@[simp] theorem psiAux_apply (Φ : ConjHom (Coind G U M) C) (g : G) :
    (psiAux U Φ) g = psiAuxFun U Φ g := rfl

/-- `psiAux` is `G`-equivariant. -/
theorem psiAux_smul (Φ : ConjHom (Coind G U M) C) (g : G) :
    psiAux U (g • Φ) = g • psiAux U Φ := by
  refine Subtype.ext (funext fun x => ?_)
  refine ConjHom.ext_apply fun m => ?_
  rw [psiAux_apply, psiAuxFun_apply, ConjHom.smul_apply, thetaAux_smul, Coind.smul_apply, psiAux_apply,
    psiAuxFun_apply, mul_inv_rev, inv_inv, mul_smul]

/-- `psiAux` is additive. -/
theorem psiAux_add (Φ₁ Φ₂ : ConjHom (Coind G U M) C) :
    psiAux U (Φ₁ + Φ₂) = psiAux U Φ₁ + psiAux U Φ₂ := by
  refine Subtype.ext (funext fun g => ?_)
  refine ConjHom.ext_apply fun m => ?_
  simp only [psiAux_apply, psiAuxFun_apply, AddSubgroup.coe_add, Pi.add_apply,
    ConjHom.add_apply, smul_add]

section Surjective

variable [Fintype (G ⧸ U)]

/-- The inverse of `psiAux` on a coinduced coefficient: `f ↦ ∑_q q.out • F q.out (f q.out)`. -/
def preimageAuxHom (F : Coind G U (ConjHom M C)) : Coind G U M →+ C where
  toFun f := ∑ q : G ⧸ U, q.out • F q.out (f q.out)
  map_zero' := by
    simp only [AddSubgroup.coe_zero, Pi.zero_apply, map_zero, smul_zero, Finset.sum_const_zero]
  map_add' f₁ f₂ := by
    simp only [AddSubgroup.coe_add, Pi.add_apply, map_add, smul_add, Finset.sum_add_distrib]

/-- The inverse of `psiAux`: `f ↦ ∑_q q.out • F q.out (f q.out)`. -/
def preimageAux (F : Coind G U (ConjHom M C)) : ConjHom (Coind G U M) C :=
  ⟨preimageAuxHom U F⟩

theorem psiAux_preimage (F : Coind G U (ConjHom M C)) : psiAux U (preimageAux U F) = F := by
  refine Subtype.ext (funext fun g => ?_)
  refine ConjHom.ext_apply fun m => ?_
  rw [psiAux_apply, psiAuxFun_apply]
  have hcomp : (preimageAux U F) (thetaAux U g m)
      = ∑ q : G ⧸ U, q.out • F q.out (thetaAux U g m q.out) := rfl
  rw [hcomp]
  have h1 : ∀ b ∈ (Finset.univ : Finset (G ⧸ U)), b ≠ (QuotientGroup.mk g : G ⧸ U) →
      b.out • F b.out (thetaAux U g m b.out) = 0 := by
    intro b _ hb
    have hz : thetaAux U g m b.out = 0 := by
      apply thetaAux_apply_eq_zero
      intro hmem
      refine hb ?_
      have hx : b.out = g * ((⟨g⁻¹ * b.out, hmem⟩ : U) : G) := by
        show b.out = g * (g⁻¹ * b.out)
        group
      rw [← QuotientGroup.out_eq' b, hx, QuotientGroup.mk_mul_of_mem g hmem]
    rw [hz, map_zero, smul_zero]
  have h2 : (QuotientGroup.mk g : G ⧸ U) ∉ (Finset.univ : Finset (G ⧸ U)) →
      ((QuotientGroup.mk g : G ⧸ U)).out • F ((QuotientGroup.mk g : G ⧸ U)).out
          (thetaAux U g m ((QuotientGroup.mk g : G ⧸ U)).out) = 0 :=
    fun h => absurd (Finset.mem_univ _) h
  rw [Finset.sum_eq_single (QuotientGroup.mk g : G ⧸ U) h1 h2]
  set r : U := Coind.rep G U g with hr
  have hout : ((QuotientGroup.mk g : G ⧸ U)).out = g * (r : G) := by
    rw [hr]; exact Coind.rep_spec G U g
  have htheta : thetaAux U g m ((QuotientGroup.mk g : G ⧸ U)).out = r⁻¹ • m := by
    rw [hout, thetaAux_apply_mul_U]
  have hF : F ((QuotientGroup.mk g : G ⧸ U)).out (r⁻¹ • m) = r⁻¹ • F g m := by
    rw [hout, Coind.coe_mul, ConjHom.smul_apply, inv_inv, smul_inv_smul]
  rw [htheta, hF, hout, mul_smul, ← mul_smul, inv_mul_cancel, one_smul, Subgroup.smul_def,
    ← mul_smul, Subgroup.coe_inv, mul_inv_cancel, one_smul]

/-- `psiAux` is injective: the delta elements span. -/
theorem psiAux_injective :
    Function.Injective (psiAux U : ConjHom (Coind G U M) C → Coind G U (ConjHom M C)) := by
  intro Φ₁ Φ₂ h
  have h1 : ∀ g, psiAuxFun U Φ₁ g = psiAuxFun U Φ₂ g := by
    intro g
    have hh := congrArg (fun F : Coind G U (ConjHom M C) => F g) h
    rw [psiAux_apply, psiAux_apply] at hh
    exact hh
  have key : ∀ g (m : M), Φ₁ (thetaAux U g m) = Φ₂ (thetaAux U g m) := by
    intro g m
    have hg : g⁻¹ • Φ₁ (thetaAux U g m) = g⁻¹ • Φ₂ (thetaAux U g m) := by
      have hh := congrArg (fun ψ : ConjHom M C => ψ m) (h1 g)
      rw [psiAuxFun_apply, psiAuxFun_apply] at hh
      exact hh
    have hfin := congrArg (fun x : C => g • x) hg
    simpa [smul_inv_smul] using hfin
  refine ConjHom.ext_apply fun f => ?_
  rw [thetaAux_spanning U f, map_sum, map_sum]
  exact Finset.sum_congr rfl fun q _ => key q.out (f q.out)

/-- `psiAux` is surjective. -/
theorem psiAux_surjective :
    Function.Surjective (psiAux U : ConjHom (Coind G U M) C → Coind G U (ConjHom M C)) :=
  fun F => ⟨preimageAux U F, psiAux_preimage U F⟩

end Surjective

end

/-- **Frobenius reciprocity for the coinduced module, `G`-equivariantly.**  For a subgroup `U ≤ G`
of finite index, an additive group `M` with a `U`-action and an additive group `C` with a
`G`-action (so that `U` acts on `C` by restriction), there is an additive isomorphism
`Hom_ℤ(Coind_U^G M , C) ≅ Coind_U^G (Hom_ℤ(M , C))` which is `G`-equivariant (the conjugation
action on the left, the coinduced action on the right).

The additive half is already available as `Work.SSGRoute.PT.coindHomEquiv`; what has to be added is
that the bijection can be chosen `G`-equivariant, e.g. by the classical Shapiro formula written on
the coset space `G ⧸ U` (see `Work.SSGRoute.PT.coindEquivFun` for `Coind G U M ≃+ (G ⧸ U → M)`). -/
theorem frobenius_coindAux {G : Type*} [Group G] (U : Subgroup G) [U.FiniteIndex]
    {M : Type*} [AddCommGroup M] [DistribMulAction U M]
    {C : Type*} [AddCommGroup C] [DistribMulAction G C] :
    ∃ Φ : Work.SSGRoute.PT.ConjHom (Work.SSGRoute.PT.Coind G U M) C ≃+
      Work.SSGRoute.PT.Coind G U (Work.SSGRoute.PT.ConjHom M C),
      ∀ (g : G) (φ : Work.SSGRoute.PT.ConjHom (Work.SSGRoute.PT.Coind G U M) C),
        Φ (g • φ) = g • Φ φ := by
  classical
  haveI : Fintype (G ⧸ U) := Fintype.ofFinite _
  refine ⟨⟨Equiv.ofBijective (psiAux U) ⟨psiAux_injective U, psiAux_surjective U⟩,
    fun x y => psiAux_add U x y⟩, ?_⟩
  intro g φ
  show psiAux U (g • φ) = g • psiAux U φ
  exact psiAux_smul U φ g

end Work.SSGRoute.PT
