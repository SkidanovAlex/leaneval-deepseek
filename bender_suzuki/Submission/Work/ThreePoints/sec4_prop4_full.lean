import Mathlib
import Submission.Work.ThreePoints.Omega
import Submission.Work.ThreePoints.Sec2b
import Submission.Work.ThreePoints.TwoPointTransitive
import Submission.Work.ThmF.Bender.cardKsetEqInv
import Submission.Work.DoubleTransitivity.App2.sylow_max_conj
import Submission.Work.ThmF.Bender.cardInvGeTwo
import Submission.Work.ThreePoints.exists_odd_sylow_sub_of_ne_bot
import Submission.Work.ThreePoints.centD_eq_centralizer_of_involution_brsz
import Submission.Work.ThreePoints.prop3b_normal_sylow
import Submission.Work.ThreePoints.prop4b_S_le_centralizer
import Submission.Work.ThreePoints.prop4b_X_sylow

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ThreePoints

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

variable {G : Type} [Group G] [Finite G]

/-! ## Conjugation by `K = J(D,t)` sweeps out `Inv(H)`

Peterfalvi I Ch. I §2 Prop. 2: for an involution `u ∈ H` the map `x ↦ x * u * x⁻¹` is a bijection
from `K = J(D,t)` onto `Inv(H)`.  Injectivity is Ch. I §2 Lemma 1 (`invertedBy_conj_injective`)
and `|K| = |Inv(H)|` is `Work.ThmF.Bender.cardKsetEqInv`, so the image, which lies in `Inv(H)`,
is all of `Inv(H)`. -/

theorem conj_image_invertedBy_eq_involutions {H : Subgroup G} (hH : IsStronglyEmbedded H)
    {t u : G} (ht : orderOf t = 2) (htH : t ∉ H) (hu : u ∈ involutions (H : Set G)) :
    (fun x => x * u * x⁻¹) '' (invertedBy (twoPoint H t) t) = involutions (H : Set G) := by
  have hK : (invertedBy (twoPoint H t) t).ncard = (involutions (H : Set G)).ncard :=
    Work.ThmF.Bender.cardKsetEqInv hH ht htH
  have hmaps : ∀ x ∈ invertedBy (twoPoint H t) t,
      x * u * x⁻¹ ∈ involutions (H : Set G) := by
    intro x hx
    have hxH : x ∈ H := (Subgroup.mem_inf.mp hx.1).1
    exact ⟨H.mul_mem (H.mul_mem hxH hu.1) (H.inv_mem hxH),
      by rw [Work.ThmF.Bender.orderOf_conj_eq, hu.2]⟩
  have hinj : Set.InjOn (fun x => x * u * x⁻¹) (invertedBy (twoPoint H t) t) :=
    invertedBy_conj_injective hH ht htH hu.1 hu.2
  have himg : ((fun x => x * u * x⁻¹) '' (invertedBy (twoPoint H t) t)).ncard =
      (involutions (H : Set G)).ncard := by
    rw [Set.InjOn.ncard_image hinj, hK]
  have hsub : (fun x => x * u * x⁻¹) '' (invertedBy (twoPoint H t) t) ⊆
      involutions (H : Set G) := by
    rintro _ ⟨x, hx, rfl⟩
    exact hmaps x hx
  exact Set.eq_of_subset_of_ncard_le hsub (le_of_eq himg.symm)

/-! ## Prop. 4 (a) from Prop. 2 (a)

If `V = C_D(t)` is the centraliser in `D` of a single involution `u ∈ Inv H`, then
`C_V(K) = C_D(Inv H)`.

`⊆`: for `w = x u x⁻¹` (with `x ∈ K`) and `c ∈ V ⊓ C(K)` one has
`c w c⁻¹ = (c x c⁻¹)·(c u c⁻¹)·(c x c⁻¹)⁻¹ = x u x⁻¹ = w`, since `c` commutes with `K ∋ x` and
with `u` (as `c ∈ V = C_D(u)`).

`⊇`: if `c ∈ D` centralises `Inv(H)` then `c ∈ C_D(u) = V`; moreover `c` commutes with `t`, so
for `x ∈ K` the conjugate `c x c⁻¹` still lies in `K` (as `t (c x c⁻¹) t = c (t x t) c⁻¹ =
(c x c⁻¹)⁻¹`), and `x ↦ x u x⁻¹` takes the same value at `c x c⁻¹` and at `x` (as `c` commutes
with `u` and with `x u x⁻¹ ∈ Inv H`); injectivity of that map on `K` gives `c x c⁻¹ = x`. -/

theorem centD_inf_centralizer_invertedBy_eq_of_prop2a {H : Subgroup G}
    (hH : IsStronglyEmbedded H) {t : G} (ht : orderOf t = 2) (htH : t ∉ H)
    (hu : ∃ u ∈ involutions (H : Set G),
      centD H t = twoPoint H t ⊓ Subgroup.centralizer ({u} : Set G)) :
    centD H t ⊓ Subgroup.centralizer (invertedBy (twoPoint H t) t) =
      twoPoint H t ⊓ Subgroup.centralizer (involutions (H : Set G)) := by
  obtain ⟨u, huInv, hVu⟩ := hu
  have ht2 : t * t = 1 := mul_self_eq_one_of_orderOf_eq_two ht
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have himg := conj_image_invertedBy_eq_involutions hH ht htH huInv
  have hsurj : ∀ w ∈ involutions (H : Set G),
      ∃ x ∈ invertedBy (twoPoint H t) t, x * u * x⁻¹ = w := by
    intro w hw
    have hw' : w ∈ (fun x => x * u * x⁻¹) '' (invertedBy (twoPoint H t) t) := by
      rw [himg]; exact hw
    obtain ⟨x, hx, hxw⟩ := hw'
    exact ⟨x, hx, hxw⟩
  refine le_antisymm ?_ ?_
  · -- `C_V(K) ⊆ C_D(Inv H)`
    intro c hc
    obtain ⟨hcV, hcK⟩ := Subgroup.mem_inf.mp hc
    have hcD : c ∈ twoPoint H t := (Subgroup.mem_inf.mp hcV).1
    have hcu : c * u = u * c := Subgroup.mem_centralizer_singleton_iff.mp
      (Subgroup.mem_inf.mp (hVu ▸ hcV)).2
    refine Subgroup.mem_inf.mpr ⟨hcD, Subgroup.mem_centralizer_iff.mpr ?_⟩
    intro w hw
    obtain ⟨x, hx, hxw⟩ := hsurj w hw
    have hxc : x * c = c * x := Subgroup.mem_centralizer_iff.mp hcK x hx
    have hxc' : x⁻¹ * c = c * x⁻¹ := by
      calc x⁻¹ * c = x⁻¹ * (c * x) * x⁻¹ := by group
        _ = x⁻¹ * (x * c) * x⁻¹ := by rw [hxc]
        _ = c * x⁻¹ := by group
    calc w * c = (x * u * x⁻¹) * c := by rw [hxw]
      _ = x * u * (x⁻¹ * c) := by group
      _ = x * u * (c * x⁻¹) := by rw [hxc']
      _ = x * (u * c) * x⁻¹ := by group
      _ = x * (c * u) * x⁻¹ := by rw [hcu]
      _ = (x * c) * u * x⁻¹ := by group
      _ = (c * x) * u * x⁻¹ := by rw [hxc]
      _ = c * (x * u * x⁻¹) := by group
      _ = c * w := by rw [hxw]
  · -- `C_D(Inv H) ⊆ C_V(K)`
    intro c hc
    obtain ⟨hcD, hcInv⟩ := Subgroup.mem_inf.mp hc
    have hcu : c * u = u * c := (Subgroup.mem_centralizer_iff.mp hcInv u huInv).symm
    have hcV : c ∈ centD H t := by
      rw [hVu]
      exact ⟨hcD, Subgroup.mem_centralizer_singleton_iff.mpr hcu⟩
    have hct : c * t = t * c := Subgroup.mem_centralizer_singleton_iff.mp
      (Subgroup.mem_inf.mp hcV).2
    have htct : t * c * t = c := by
      calc t * c * t = c * t * t := by rw [← hct]
        _ = c := by rw [mul_assoc, ht2, mul_one]
    have hcTw : c ∈ twoPoint H t := (Subgroup.mem_inf.mp hcV).1
    refine Subgroup.mem_inf.mpr ⟨hcV, Subgroup.mem_centralizer_iff.mpr ?_⟩
    intro k hk
    have hkD : k ∈ twoPoint H t := hk.1
    have hkt : t * k * t = k⁻¹ := by simpa only [htinv] using hk.2
    have hkH : k ∈ H := (Subgroup.mem_inf.mp hkD).1
    -- `c k c⁻¹ ∈ K`
    have hckK : c * k * c⁻¹ ∈ invertedBy (twoPoint H t) t := by
      refine ⟨(twoPoint H t).mul_mem ((twoPoint H t).mul_mem hcTw hkD)
        ((twoPoint H t).inv_mem hcTw), ?_⟩
      have hconjc : (MulAut.conj t) c = c := by
        rw [MulAut.conj_apply, htinv]; exact htct
      have hconjk : (MulAut.conj t) k = k⁻¹ := by
        rw [MulAut.conj_apply, htinv]; exact hkt
      have hcon : (MulAut.conj t) (c * k * c⁻¹) = c * k⁻¹ * c⁻¹ := by
        rw [map_mul, map_mul, map_inv, hconjc, hconjk]
      rw [MulAut.conj_apply, htinv] at hcon
      rw [htinv, hcon]
      group
    -- the two conjugates have the same image under `x ↦ x * u * x⁻¹`
    have hkuInv : k * u * k⁻¹ ∈ involutions (H : Set G) :=
      ⟨H.mul_mem (H.mul_mem hkH huInv.1) (H.inv_mem hkH),
        by rw [Work.ThmF.Bender.orderOf_conj_eq, huInv.2]⟩
    have hcuc : c⁻¹ * u * c = u := by
      rw [mul_assoc, ← hcu]
      group
    have hsame : (c * k * c⁻¹) * u * (c * k * c⁻¹)⁻¹ = k * u * k⁻¹ := by
      calc (c * k * c⁻¹) * u * (c * k * c⁻¹)⁻¹
          = c * k * (c⁻¹ * u * c) * k⁻¹ * c⁻¹ := by group
        _ = c * k * u * k⁻¹ * c⁻¹ := by rw [hcuc]
        _ = c * (k * u * k⁻¹) * c⁻¹ := by group
        _ = k * u * k⁻¹ := by
              have h := (Subgroup.mem_centralizer_iff.mp hcInv (k * u * k⁻¹) hkuInv).symm
              calc c * (k * u * k⁻¹) * c⁻¹ = (k * u * k⁻¹) * c * c⁻¹ := by rw [h]
                _ = k * u * k⁻¹ := by group
    have hinj := invertedBy_conj_injective hH ht htH huInv.1 huInv.2 hckK hk hsame
    calc k * c = (c * k * c⁻¹) * c := by rw [hinj]
      _ = c * k := by group

/-! ## Prop. 4 (b) from the rank-one structure of `N_H(X)` (Prop. 3 (b))

`D = H ∩ H^t`, `K = J(D,t)`, `V = C_D(t)`, `W = C_V(K) = C_D(Inv H)` (Prop. 4 (a)),
`C = C_H(Inv H)`.  If `W ≠ 1`, let `X ≤ W` be the Sylow `p`-subgroup of `W` for an odd prime `p`
(`X ≠ 1`, `X ≤ C`) and let `S ≤ H` be the `2`-subgroup of Ch. II §4 Prop. 3 (b) with
`N_H(X) = S ⋊ N_D(X)`, `S ⊴ N_H(X)`, `S ⊓ D = ⊥`, and (by the `Inv H`-orbit argument)
`S ≤ C`.  Then `H = C·D`:

* `sylow_max_conj` (Sylow conjugacy) gives `H = C ⊔ N_H(X)`: for `h ∈ H` the conjugate
  `X^h ≤ C` is a maximal `p`-subgroup of `C`, hence `X^h = X^c` for some `c ∈ C`, so
  `h = c·(c⁻¹h)` with `c⁻¹h ∈ N_H(X)` (Frattini's argument);
* `N_H(X) = S ⋊ N_D(X) ⊆ C·D` because `S ≤ C` and `N_D(X) ≤ D`;
* hence `H = C ⊔ D`. -/

theorem prop4b_of_structure {H : Subgroup G} {t : G} (S X : Subgroup G) {p : ℕ}
    (hci : centD H t ⊓ Subgroup.centralizer (invertedBy (twoPoint H t) t) =
      twoPoint H t ⊓ Subgroup.centralizer (involutions (H : Set G)))
    (hp : p.Prime) (hXp : IsPGroup p X)
    (hXC : X ≤ H ⊓ Subgroup.centralizer (involutions (H : Set G)))
    (hXsylC : ∀ Y : Subgroup G, X ≤ Y →
      Y ≤ H ⊓ Subgroup.centralizer (involutions (H : Set G)) → IsPGroup p Y → Y = X)
    (hSD : S ⊓ twoPoint H t = ⊥)
    (hA : S ⊔ (twoPoint H t ⊓ Subgroup.normalizer (X : Set G)) =
      H ⊓ Subgroup.normalizer (X : Set G))
    (hSleC : S ≤ H ⊓ Subgroup.centralizer (involutions (H : Set G))) :
    (H ⊓ Subgroup.centralizer (involutions (H : Set G))) ⊔ twoPoint H t = H := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  set C : Subgroup G := H ⊓ Subgroup.centralizer (involutions (H : Set G)) with hCdef
  set D : Subgroup G := twoPoint H t with hDdef
  set A : Subgroup G := H ⊓ Subgroup.normalizer (X : Set G) with hAdef
  have hcomp : ∀ g h : G,
      ((MulAut.conj h).toMonoidHom).comp ((MulAut.conj g).toMonoidHom)
        = (MulAut.conj (h * g)).toMonoidHom := by
    intro g h
    ext x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  -- conjugation by an element of `H` preserves `C`
  have hconjC : ∀ {h y : G}, h ∈ H → y ∈ C → h * y * h⁻¹ ∈ C := by
    intro h y hh hy
    have hy2 : y ∈ H ⊓ Subgroup.centralizer (involutions (H : Set G)) := hCdef ▸ hy
    obtain ⟨hyH, hyC⟩ := Subgroup.mem_inf.mp hy2
    refine Subgroup.mem_inf.mpr ⟨H.mul_mem (H.mul_mem hh hyH) (H.inv_mem hh), ?_⟩
    rw [Subgroup.mem_centralizer_iff] at hyC ⊢
    intro z hz
    have hz' : h⁻¹ * z * h ∈ involutions (H : Set G) := by
      refine ⟨H.mul_mem (H.mul_mem (H.inv_mem hh) hz.1) hh, ?_⟩
      have h1 := Work.ThmF.Bender.orderOf_conj_eq h⁻¹ z
      rw [inv_inv] at h1
      rw [h1, hz.2]
    have hkey := hyC (h⁻¹ * z * h) hz'
    calc z * (h * y * h⁻¹) = h * ((h⁻¹ * z * h) * y) * h⁻¹ := by group
      _ = h * (y * (h⁻¹ * z * h)) * h⁻¹ := by rw [hkey]
      _ = (h * y * h⁻¹) * z := by group
  have hmapC : ∀ {h : G}, h ∈ H → C.map (MulAut.conj h).toMonoidHom = C := by
    intro h hh
    refine le_antisymm ?_ ?_
    · rintro x ⟨y, hy, rfl⟩
      simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using hconjC hh hy
    · intro x hx
      refine Subgroup.mem_map.mpr ⟨h⁻¹ * x * h, ?_, ?_⟩
      · simpa using hconjC (H.inv_mem hh) hx
      · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
        group
  -- maximality of `X` in `C` transfers to conjugates by elements of `H`
  have hXsyl : ∀ {h : G}, h ∈ H → ∀ Y : Subgroup G, X.map (MulAut.conj h).toMonoidHom ≤ Y →
      Y ≤ C → IsPGroup p Y → Y = X.map (MulAut.conj h).toMonoidHom := by
    intro h hh Y hXY hYC hYp
    have hY' : Y.map (MulAut.conj h⁻¹).toMonoidHom ≤ C := by
      rw [← hmapC (H.inv_mem hh)]
      exact Subgroup.map_mono hYC
    have hXY' : X ≤ Y.map (MulAut.conj h⁻¹).toMonoidHom := by
      intro x hx
      refine Subgroup.mem_map.mpr ⟨(MulAut.conj h) x, hXY (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩), ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      group
    have hYp' : IsPGroup p (Y.map (MulAut.conj h⁻¹).toMonoidHom) := hYp.map _
    have h3 : Y.map (MulAut.conj h⁻¹).toMonoidHom = X := hXsylC _ hXY' hY' hYp'
    have hcomp1 : ((MulAut.conj h).toMonoidHom).comp ((MulAut.conj h⁻¹).toMonoidHom)
        = MonoidHom.id G := by
      rw [hcomp, mul_inv_cancel]
      ext x
      simp [MulAut.conj_apply]
    have h4 : (Y.map (MulAut.conj h⁻¹).toMonoidHom).map (MulAut.conj h).toMonoidHom = Y := by
      rw [Subgroup.map_map, hcomp1, Subgroup.map_id]
    rw [← h4, h3]
  -- Frattini's argument: `H = C ⊔ N_H(X)`
  have hFrat : H ≤ C ⊔ A := by
    intro h hh
    have hXh_le : X.map (MulAut.conj h).toMonoidHom ≤ C := by
      rw [← hmapC hh]
      exact Subgroup.map_mono hXC
    have hXh_max : ∀ T : Subgroup G, IsPGroup p T → X.map (MulAut.conj h).toMonoidHom ≤ T →
        T ≤ C → T = X.map (MulAut.conj h).toMonoidHom := fun T hT hle hTC => hXsyl hh T hle hTC hT
    obtain ⟨c, hcC, hcq⟩ := Work.DoubleTransitivity.App2.sylow_max_conj (Q := X.map (MulAut.conj h).toMonoidHom) (R := X)
      (K := C) (hXp.map _) hXh_le hXh_max hXp hXC
        (fun T hT hle hTC => hXsylC T hle hTC hT)
    have hmem : c⁻¹ * h ∈ Subgroup.normalizer (X : Set G) := by
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      show X.map (MulAut.conj (c⁻¹ * h)).toMonoidHom = X
      have h1 : (MulAut.conj (c⁻¹ * h)).toMonoidHom
          = ((MulAut.conj c⁻¹).toMonoidHom).comp ((MulAut.conj h).toMonoidHom) :=
        (hcomp h c⁻¹).symm
      have hcomp2 : ((MulAut.conj c⁻¹).toMonoidHom).comp ((MulAut.conj h).toMonoidHom)
          = (MulAut.conj (c⁻¹ * h)).toMonoidHom := hcomp h c⁻¹
      have hcomp3 : ((MulAut.conj c⁻¹).toMonoidHom).comp ((MulAut.conj c).toMonoidHom)
          = MonoidHom.id G := by
        rw [hcomp, inv_mul_cancel]
        ext x
        simp [MulAut.conj_apply]
      rw [h1, ← Subgroup.map_map, ← hcq, Subgroup.map_map, hcomp3, Subgroup.map_id]
    have hmemA : c⁻¹ * h ∈ A := by
      rw [hAdef]
      exact ⟨H.mul_mem (H.inv_mem (Subgroup.mem_inf.mp (hCdef ▸ hcC)).1) hh, hmem⟩
    have hmemCA : c * (c⁻¹ * h) ∈ C ⊔ A := Subgroup.mul_mem_sup hcC hmemA
    rwa [show c * (c⁻¹ * h) = h from by group] at hmemCA
  -- `N_H(X) = S ⋊ N_D(X) ⊆ C ⊔ D`
  have hAle : A ≤ C ⊔ D := by
    have hA' : A = S ⊔ (D ⊓ Subgroup.normalizer (X : Set G)) := hA.symm
    rw [hA']
    exact sup_le (le_trans hSleC le_sup_left) (le_trans inf_le_left le_sup_right)
  have hHD : H ≤ C ⊔ D := by
    have hHCA : H = C ⊔ A := le_antisymm hFrat (sup_le inf_le_left inf_le_left)
    rw [hHCA]
    exact sup_le le_sup_left hAle
  refine le_antisymm ?_ hHD
  refine sup_le inf_le_left ?_
  rw [hDdef]
  exact inf_le_left
theorem sec4_prop4_full {G : Type} [Group G] [Finite G] (hFT : Submission.Blueprint.FeitThompsonProp)
    (hC : Submission.Blueprint.ThmCProp) (hA : Submission.Blueprint.ThmAProp)
    (hZJ : Submission.Blueprint.GlaubermanZJProp) (hBrSz : Submission.Blueprint.BrauerSuzukiProp)
    (hMod : Submission.Blueprint.ModelFactsProp) (hS : Submission.Blueprint.Situation G)
    {H : Subgroup G} (hH : LeanEval.GroupTheory.Defs.IsStronglyEmbedded H) {t : G}
    (ht : orderOf t = 2) (htH : t ∉ H) :
    (Submission.Blueprint.centD H t ⊓
        Subgroup.centralizer (Submission.Blueprint.invertedBy (Submission.Blueprint.twoPoint H t) t) =
      Submission.Blueprint.twoPoint H t ⊓
        Subgroup.centralizer (Submission.Blueprint.involutions (H : Set G))) ∧
    (Submission.Blueprint.centD H t ⊓
        Subgroup.centralizer (Submission.Blueprint.invertedBy (Submission.Blueprint.twoPoint H t) t) ≠ ⊥ →
      (H ⊓ Subgroup.centralizer (Submission.Blueprint.involutions (H : Set G))) ⊔
        Submission.Blueprint.twoPoint H t = H) := by
  classical
  have h4a : Submission.Blueprint.centD H t ⊓
      Subgroup.centralizer (Submission.Blueprint.invertedBy (Submission.Blueprint.twoPoint H t) t) =
      Submission.Blueprint.twoPoint H t ⊓
        Subgroup.centralizer (Submission.Blueprint.involutions (H : Set G)) :=
    centD_inf_centralizer_invertedBy_eq_of_prop2a hH ht htH
      (centD_eq_centralizer_of_involution_brsz hFT hC hA hBrSz hS hH ht htH).1
  refine ⟨h4a, ?_⟩
  intro hWne
  set W : Subgroup G := Submission.Blueprint.centD H t ⊓
      Subgroup.centralizer (Submission.Blueprint.invertedBy (Submission.Blueprint.twoPoint H t) t) with hWdef
  have hWodd : Odd (Nat.card W) := by
    have hle : W ≤ twoPoint H t := by
      intro x hx
      exact (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hx).1).1
    exact Odd.of_dvd (Subgroup.card_dvd_of_le hle) (IsStronglyEmbedded.odd_card_inf_conj hH htH)
  obtain ⟨p, X, hp, hp2, hXp, hX0, hXW, hXsylW⟩ := exists_odd_sylow_sub_of_ne_bot hWne hWodd
  have hXW' : X ≤ twoPoint H t ⊓ Subgroup.centralizer (involutions (H : Set G)) := by
    rw [← h4a]
    exact hXW
  have hXsylW' : ∀ Y : Subgroup G, X ≤ Y → Y ≤ twoPoint H t ⊓
      Subgroup.centralizer (involutions (H : Set G)) → IsPGroup p Y → Y = X := by
    intro Y hXY hYW hYp
    exact hXsylW Y hXY (by rw [h4a]; exact hYW) hYp
  have hXC : X ≤ H ⊓ Subgroup.centralizer (involutions (H : Set G)) := by
    intro x hx
    obtain ⟨h1, h2⟩ := Subgroup.mem_inf.mp (hXW' hx)
    exact Subgroup.mem_inf.mpr ⟨h1.1, h2⟩
  have hXV : X ≤ Submission.Blueprint.centD H t := fun x hx => (Subgroup.mem_inf.mp (hXW hx)).1
  have hXK : X ≤ Subgroup.centralizer
      (Submission.Blueprint.invertedBy (Submission.Blueprint.twoPoint H t) t) :=
    fun x hx => (Subgroup.mem_inf.mp (hXW hx)).2
  have hKne : ∃ k ∈ Submission.Blueprint.invertedBy (Submission.Blueprint.twoPoint H t) t,
      k ≠ 1 := by
    have hKcard : (Submission.Blueprint.invertedBy (Submission.Blueprint.twoPoint H t) t).ncard =
        (involutions (H : Set G)).ncard := Work.ThmF.Bender.cardKsetEqInv hH ht htH
    have h2 : 2 ≤ (Submission.Blueprint.invertedBy (Submission.Blueprint.twoPoint H t) t).ncard := by
      rw [hKcard]
      exact Work.ThmF.Bender.cardInvGeTwo hH hS.1.1
    obtain ⟨k, hk1, hk2⟩ := Set.exists_ne_of_one_lt_ncard
      (show 1 < _ from lt_of_lt_of_le (by norm_num) h2) (1 : G)
    exact ⟨k, hk1, hk2⟩
  obtain ⟨S, hS2, hSH, hSN, hNS, hSD, hAsup⟩ :=
    prop3b_normal_sylow hFT hC hA hZJ hBrSz hMod hS hH ht htH X hXV hXK hX0 hKne
  have hSleC := prop4b_S_le_centralizer hH ht htH S X hS2 hSH hSN hNS hSD hAsup hXK
  have hXsylC := prop4b_X_sylow hH ht htH S X hp hp2 hS2 hSN hNS hSD hAsup hSleC hXp hXW' hXsylW'
  exact prop4b_of_structure S X h4a hp hXp hXC hXsylC hSD hAsup hSleC

end Work.ThreePoints
