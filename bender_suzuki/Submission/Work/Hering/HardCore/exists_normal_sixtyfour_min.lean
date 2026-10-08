import Mathlib
import Submission.Work.Hering.GL32.AppIXDefs
import Submission.Work.Hering.HardCore.Defs
import Submission.Work.Hering.Config
import Submission.Work.Hering.HardCore.aut_transitive
import Submission.Work.Hering.HardCore.SixtyfourSetup
import Submission.Work.Hering.HardCore.gl32_mulAut_V_iso
import Submission.Work.Hering.HardCore.no_normal_order_sixteen

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option warn.classDefReducibility false

open scoped IsMulCommutative

namespace Work.Hering.HardCore

/-- **Peterfalvi I §4, the minimal subgroup of order `64`.**  In the non-abelian configuration
`V ⊴ G` elementary abelian of order `8`, `C = C_G(V)` a `2`-group of order `512` with
`Ω₁(C) = V` and `G/C ≅ Aut(V)`, there is a normal subgroup `D` of `G` with `V ≤ D ≤ C`,
`|D| = 64`, minimal among the normal subgroups between `V` and `D`.

The proof picks `D` minimal among the normal subgroups `E` with `V < E ≤ C` (which exists as the
lattice is finite).  Then `D/V` is a simple `𝔽₂[GL(3,2)]`-module, so by Appendix IX
(`AppIXProp`) its `𝔽₂`-dimension is `1`, `3` or `8`; dimension `8` is impossible because
`|D| ≤ |C| = 512`, and dimension `1` would force `|D| = 16`, excluded by the transitivity of
`G` on `V#`.  Hence `|D| = 8 · 2³ = 64`. -/
theorem exists_normal_sixtyfour_min {G : Type} [Group G] [Finite G]
    (hIX : Work.Hering.AppIXProp) (V C : Subgroup G) (hV : V.Normal)
    (hcard : Nat.card V = 8) (hexp : ∀ x ∈ V, x * x = 1)
    (hC : C = Subgroup.centralizer ((V : Set G))) (hC2 : IsPGroup 2 ↥C)
    (hinv : ∀ x ∈ C, orderOf x = 2 → x ∈ V) (hAut : Work.Hering.ActsAsAut V hV)
    (hcardC : Nat.card ↥C = 512)
    (hsq : ∀ x ∈ C, x * x ∈ V)
    (hcomm : ∀ x ∈ C, ∀ y ∈ C, x * y * x⁻¹ * y⁻¹ ∈ V) :
    ∃ D : Subgroup G, D.Normal ∧ D ≤ C ∧ V ≤ D ∧ Nat.card D = 64 ∧
      (∀ E : Subgroup G, E.Normal → V ≤ E → E ≤ D → E ≠ D → E = V) := by
  classical
  -- ## 0.  Elementary facts
  have commV : ∀ {x y : G}, x ∈ V → y ∈ V → x * y = y * x := by
    intro x y hx hy
    have hx1 : x * x = 1 := hexp x hx
    have hxy : (x * y) * (x * y) = 1 := hexp (x * y) (V.mul_mem hx hy)
    have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx1
    have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right (hexp y hy)
    have h2 : x * y = (x * y)⁻¹ := (inv_eq_of_mul_eq_one_right hxy).symm
    rw [mul_inv_rev, hxinv, hyinv] at h2
    exact h2
  have hVC : V ≤ C := by
    intro x hx
    rw [hC, Subgroup.mem_centralizer_iff]
    intro v hv
    exact commV hv hx
  have hCn : C.Normal := hC.symm ▸ Subgroup.normal_centralizer
  have hVCne : V ≠ C := by
    intro h
    have h512 : Nat.card V = 512 := by rw [h]; exact hcardC
    rw [hcard] at h512
    norm_num at h512
  -- ## 1.  A minimal normal subgroup `D` with `V < D ≤ C`
  obtain ⟨D, hDmin⟩ := exists_minimalFor_of_wellFoundedLT (ι := Subgroup G)
    (fun E : Subgroup G => E.Normal ∧ V ≤ E ∧ E ≤ C ∧ V ≠ E) (fun E => Nat.card ↥E)
    ⟨C, hCn, hVC, le_rfl, hVCne⟩
  obtain ⟨hDn, hVD, hDleC, hDVne⟩ := hDmin.prop
  have hminclause : ∀ E : Subgroup G, E.Normal → V ≤ E → E ≤ D → E ≠ D → E = V := by
    intro E hEn hVE hED hEDne
    by_contra hEV
    have hEV' : V ≠ E := fun h => hEV h.symm
    have hPE : E.Normal ∧ V ≤ E ∧ E ≤ C ∧ V ≠ E := ⟨hEn, hVE, hED.trans hDleC, hEV'⟩
    have hge : Nat.card D ≤ Nat.card E := not_lt.mp (hDmin.not_lt hPE)
    exact hEDne (Subgroup.eq_of_le_of_card_ge hED hge)
  -- ## 2.  The elementary abelian group `Q = D/V`
  have hcommD : ∀ x ∈ D, ∀ y ∈ D, x * y * x⁻¹ * y⁻¹ ∈ V :=
    fun x hx y hy => hcomm x (hDleC hx) y (hDleC hy)
  have hQcomm' : ∀ a b : QV V D, a * b = b * a := by
    intro a b
    induction a using QuotientGroup.induction_on with
    | _ c =>
      induction b using QuotientGroup.induction_on with
      | _ d =>
        change QuotientGroup.mk' (V.subgroupOf D) (c * d) =
          QuotientGroup.mk' (V.subgroupOf D) (d * c)
        rw [QuotientGroup.mk'_eq_mk']
        refine ⟨(c * d)⁻¹ * (d * c), ?_, by group⟩
        rw [Subgroup.mem_subgroupOf]
        have hcoe : (((c * d)⁻¹ * (d * c) : ↥D) : G)
            = (d : G)⁻¹ * (c : G)⁻¹ * (d : G) * (c : G) := by
          simp only [Subgroup.coe_mul, Subgroup.coe_inv]
          group
        rw [hcoe]
        have key1 : (c : G)⁻¹ * (d : G) * (c : G) * (d : G)⁻¹ ∈ V := by
          have h := hV.conj_mem ((d : G) * (c : G) * (d : G)⁻¹ * (c : G)⁻¹)
            (by simpa only [mul_assoc] using hcommD d d.2 c c.2) ((c : G)⁻¹)
          have heq : (c : G)⁻¹ * ((d : G) * (c : G) * (d : G)⁻¹ * (c : G)⁻¹) * (c : G)⁻¹⁻¹
              = (c : G)⁻¹ * (d : G) * (c : G) * (d : G)⁻¹ := by group
          rwa [heq] at h
        have key2 : (d : G)⁻¹ * (c : G)⁻¹ * (d : G) * (c : G) ∈ V := by
          have h := hV.conj_mem ((c : G)⁻¹ * (d : G) * (c : G) * (d : G)⁻¹) key1
            ((d : G)⁻¹)
          have heq : (d : G)⁻¹ * ((c : G)⁻¹ * (d : G) * (c : G) * (d : G)⁻¹) * (d : G)⁻¹⁻¹
              = (d : G)⁻¹ * (c : G)⁻¹ * (d : G) * (c : G) := by group
          rwa [heq] at h
        exact key2
  haveI hQc : IsMulCommutative (QV V D) := IsMulCommutative.of_comm hQcomm'
  have hQexp : ∀ a : QV V D, a * a = 1 := by
    intro a
    induction a using QuotientGroup.induction_on with
    | _ c =>
      change QuotientGroup.mk' (V.subgroupOf D) c * QuotientGroup.mk' (V.subgroupOf D) c = 1
      rw [← map_mul, ← MonoidHom.mem_ker, QuotientGroup.ker_mk']
      exact Subgroup.mem_subgroupOf.mpr (by simpa using hsq (c : G) (hDleC c.2))
  haveI hmod : Module (ZMod 2) (Additive (QV V D)) :=
    AddCommGroup.zmodModule (fun x => by
      calc (2 : ℕ) • x = x + x := two_nsmul x
        _ = Additive.ofMul (x.toMul * x.toMul) := rfl
        _ = Additive.ofMul 1 := by rw [hQexp x.toMul]
        _ = 0 := ofMul_one)
  -- ## 3.  The conjugation representation of `G` on `D/V`
  let conjLin : G →* (Additive (QV V D) ≃ₗ[ZMod 2] Additive (QV V D)) :=
    linOfMulAutHom.comp (conjQ V D)
  have hkerL : C ≤ conjLin.ker := by
    intro c hc
    rw [MonoidHom.mem_ker]
    have hconjC : conjQ V D c = 1 := by
      ext m
      induction m using QuotientGroup.induction_on with
      | _ a =>
        change conjQ V D c (QuotientGroup.mk' (V.subgroupOf D) a) =
          QuotientGroup.mk' (V.subgroupOf D) a
        rw [conjQ_mk V D c a]
        show QuotientGroup.mk' (V.subgroupOf D) (MulAut.conjNormal (H := D) c a) =
          QuotientGroup.mk' (V.subgroupOf D) a
        rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_iff_div_mem,
          Subgroup.mem_subgroupOf]
        have hcoe : (((MulAut.conjNormal (H := D) c a) / a : ↥D) : G)
            = (c : G) * (a : G) * (c : G)⁻¹ * (a : G)⁻¹ := by
          simp only [Subgroup.coe_div, Subgroup.coe_mul, Subgroup.coe_inv,
            MulAut.conjNormal_apply, div_eq_mul_inv]
        rw [hcoe]
        exact hcomm c hc (a : G) (hDleC a.2)
    rw [show conjLin c = linOfMulAutHom (conjQ V D c) from rfl, hconjC, map_one]
  -- ## 4.  The isomorphism `G/C ≃ GL(3,2)`
  have hψker : (MulAut.conjNormal (H := V) : G →* MulAut ↥V).ker = C := by
    ext g
    rw [MonoidHom.mem_ker, hC, Subgroup.mem_centralizer_iff]
    constructor
    · intro hg v hv
      have h1 : (MulAut.conjNormal (H := V) g : MulAut ↥V) ⟨v, hv⟩ = ⟨v, hv⟩ := by rw [hg]; rfl
      have h2 := congrArg (fun w : ↥V => (w : G)) h1
      rw [MulAut.conjNormal_apply] at h2
      calc v * g = (g * v * g⁻¹) * g := by rw [h2]
        _ = g * v := by group
    · intro hg
      apply MulEquiv.ext
      intro v
      apply Subtype.ext
      rw [MulAut.conjNormal_apply]
      show g * (v : G) * g⁻¹ = (v : G)
      calc g * (v : G) * g⁻¹ = ((v : G) * g) * g⁻¹ := by rw [hg (v : G) v.2]
        _ = (v : G) := by group
  have hψsurj : Function.Surjective (MulAut.conjNormal (H := V) : G →* MulAut ↥V) := by
    intro φ
    obtain ⟨g, hg⟩ := hAut φ
    refine ⟨g, MulEquiv.ext fun v => ?_⟩
    apply Subtype.ext
    rw [MulAut.conjNormal_apply]
    exact (congrArg Subtype.val (hg v)).symm
  have e₂ : G ⧸ C ≃* MulAut ↥V :=
    (QuotientGroup.quotientMulEquivOfEq hψker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective (MulAut.conjNormal (H := V)) hψsurj)
  have hexp' : ∀ x : ↥V, x * x = 1 := fun x => Subtype.ext (by simpa using hexp x x.2)
  obtain ⟨e₁⟩ := gl32_mulAut_V_iso (V := ↥V) hcard hexp'
  let e : Work.Hering.GL32 ≃* G ⧸ C := e₁.trans e₂.symm
  let ρ : Work.Hering.GL32 →* (Additive (QV V D) ≃ₗ[ZMod 2] Additive (QV V D)) :=
    (QuotientGroup.lift C conjLin hkerL).comp (e : Work.Hering.GL32 →* G ⧸ C)
  have hρmk : ∀ g : G, ρ (e.symm (QuotientGroup.mk' C g)) = conjLin g := by
    intro g
    show QuotientGroup.lift C conjLin hkerL (e (e.symm (QuotientGroup.mk' C g))) = conjLin g
    rw [MulEquiv.apply_symm_apply]
    exact DFunLike.congr_fun (QuotientGroup.lift_comp_mk' C conjLin hkerL) g
  -- ## 5.  Applying Appendix IX
  have hnonzero : ∃ m : Additive (QV V D), m ≠ 0 := by
    have hDneV : D ≠ V := fun h => hDVne h.symm
    obtain ⟨x, hxD, hxV⟩ : ∃ x ∈ D, x ∉ V := by
      by_contra h
      push_neg at h
      exact hDneV (le_antisymm h hVD)
    refine ⟨Additive.ofMul (QuotientGroup.mk' (V.subgroupOf D) ⟨x, hxD⟩), ?_⟩
    intro h0
    rw [ofMul_eq_zero, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h0
    exact hxV (Subgroup.mem_subgroupOf.mp h0)
  have hsimple : ∀ W : Submodule (ZMod 2) (Additive (QV V D)),
      (∀ gl : Work.Hering.GL32, ∀ w ∈ W, ρ gl w ∈ W) → W = ⊥ ∨ W = ⊤ := by
    intro W hW
    have hW' : ∀ g : G, ∀ w ∈ W, linOfMulAut (conjQ V D g) w ∈ W := by
      intro g w hw
      have h1 := hW (e.symm (QuotientGroup.mk' C g)) w hw
      rwa [hρmk g] at h1
    have hEn : (EofW V D W).Normal := EofW_normal_of_invariant V D W hW'
    have hVE : V ≤ EofW V D W := V_le_EofW V D hVD W
    have hED : EofW V D W ≤ D := EofW_le_D V D W
    by_cases hDcase : EofW V D W = D
    · exact Or.inr (EofW_eq_D_imp V D W hDcase)
    · exact Or.inl (EofW_eq_V_imp V D W (hminclause _ hEn hVE hED hDcase))
  have hfr := hIX ρ hnonzero hsimple
  -- ## 6.  Cardinality bookkeeping
  have hcardVsub : Nat.card ↥(V.subgroupOf D) = 8 := by
    have h : Nat.card ↥(V.subgroupOf D) = Nat.card ↥V :=
      Nat.card_congr
        { toFun := fun x => ⟨((x : ↥D) : G), Subgroup.mem_subgroupOf.mp x.2⟩
          invFun := fun v => ⟨⟨(v : G), hVD v.2⟩, Subgroup.mem_subgroupOf.mpr v.2⟩
          left_inv := fun x => Subtype.ext rfl
          right_inv := fun v => Subtype.ext rfl }
    rw [h, hcard]
  have hsplit : Nat.card ↥D = Nat.card (QV V D) * 8 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (V.subgroupOf D)
    rwa [hcardVsub] at h
  haveI hfinM : Finite (Additive (QV V D)) := inferInstance
  haveI hfin : Module.Finite (ZMod 2) (Additive (QV V D)) :=
    Module.Finite.of_finite (R := ZMod 2)
  have hcardM : Nat.card (QV V D) = 2 ^ Module.finrank (ZMod 2) (Additive (QV V D)) := by
    have h1 : Nat.card (Additive (QV V D)) = Nat.card (ZMod 2) ^
        Module.finrank (ZMod 2) (Additive (QV V D)) :=
      Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive (QV V D))
    rw [Nat.card_congr (Additive.ofMul : QV V D ≃ Additive (QV V D)), h1, Nat.card_zmod]
  have hDleC' : Nat.card ↥D ≤ 512 := by
    have := Subgroup.card_le_of_le (G := G) hDleC
    rwa [hcardC] at this
  refine ⟨D, hDn, hDleC, hVD, ?_, hminclause⟩
  rcases hfr with h1 | h3 | h8
  · -- `finrank = 1` forces `|D| = 16`, impossible
    exfalso
    rw [h1] at hcardM
    norm_num at hcardM
    have h16 : Nat.card ↥D = 16 := by rw [hsplit, hcardM]
    exact no_normal_order_sixteen V C hV hcard hexp hC hinv hAut hsq D hDn hVD hDleC h16
  · -- `finrank = 3` gives `|D| = 64`
    rw [h3] at hcardM
    norm_num at hcardM
    rw [hsplit, hcardM]
  · -- `finrank = 8` is impossible as `|D| ≤ 512`
    rw [h8] at hcardM
    norm_num at hcardM
    rw [hcardM] at hsplit
    omega

end Work.Hering.HardCore
