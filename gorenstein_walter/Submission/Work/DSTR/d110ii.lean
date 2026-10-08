import Mathlib
import Submission.Work.DSTR.Defs
import Submission.Work.DSTR.map_fittingPiIn_le
import Submission.Work.DSTR.map_centralizer_eq_bot_and_equiv
import Submission.Work.DSTR.centralizes_of_mem_fittingPiIn
import Submission.Work.DSTR.fittingPiIn_subgroupOf
import Submission.Work.DSTR.oddCentralizerQuasisimple
import Submission.Work.DSTR.fittingPiIn_centralizer_transfer


/-! GW design 25, part D: `d110ii` with the hard case removed (copy of DSTR/d110ii.lean; new inputs h4, h6). -/

namespace Work.DSTR

open scoped MatrixGroups

open Subgroup

/-! ## Elementary preparatory lemmas -/

/-- `F_{2'}(K) ≤ K`. -/
theorem fittingPiIn_le_self {G : Type} [Group G] (K : Subgroup G) :
    Work.GW2.fittingPiIn {n : ℕ | n ≠ 2} K ≤ K := Subgroup.map_subtype_le _

/-- **Uniqueness of the layer.**  If `X` has a normal quasisimple subgroup `E`, then `E` *is* the
layer: by `LayerUniqueProp` all normal quasisimple subgroups agree, and the layer is the join of
that family. -/
theorem layer_eq_of_quasisimple {X : Type} [Group X] [Finite X] (h5 : Work.GW2.LayerUniqueProp)
    (hFT : Work.GW2.FeitThompsonProp) (hSyl : Work.GW2.DihOrCycSylow X)
    (E : Subgroup X) (hEn : E.Normal) (hEq : Work.GW2.IsQuasisimple E) :
    Work.GW2.layer X = E := by
  have h : ∀ F : Subgroup X, F.Normal → Work.GW2.IsQuasisimple F → F = E :=
    fun F hFn hFq => h5 X hFT hSyl F E hFn hEn hFq hEq
  rw [Work.GW2.layer]
  refine le_antisymm ?_ ?_
  · exact sSup_le (fun F hF => le_of_eq (h F hF.1 hF.2))
  · exact le_sSup (show E ∈ {F : Subgroup X | F.Normal ∧ Work.GW2.IsQuasisimple F} from ⟨hEn, hEq⟩)

/-- If the layer is not trivial, it is a (in fact *the*) normal quasisimple subgroup. -/
theorem exists_quasisimple_of_layer_ne_bot {X : Type} [Group X] [Finite X]
    (h5 : Work.GW2.LayerUniqueProp) (hFT : Work.GW2.FeitThompsonProp)
    (hSyl : Work.GW2.DihOrCycSylow X) (h : Work.GW2.layer X ≠ ⊥) :
    ∃ E : Subgroup X, E.Normal ∧ Work.GW2.IsQuasisimple E ∧ Work.GW2.layer X = E := by
  by_contra hc
  push_neg at hc
  apply h
  rw [Work.GW2.layer]
  have hempty : {N : Subgroup X | N.Normal ∧ Work.GW2.IsQuasisimple N} = ∅ := by
    ext N
    constructor
    · rintro ⟨hNn, hNq⟩
      exact absurd (layer_eq_of_quasisimple h5 hFT hSyl N hNn hNq) (hc N hNn hNq)
    · intro h; exact absurd h (by simp)
  rw [hempty]
  simp

/-- `h1` for subgroups. -/
theorem dihOrCyc_sub {X : Type} [Group X] [Finite X] (h1 : Work.GW2.DihOrCycHeredProp)
    (hSyl : Work.GW2.DihOrCycSylow X) (K : Subgroup X) : Work.GW2.DihOrCycSylow K :=
  (h1 X hSyl).1 K

/-- `h1` for quotients. -/
theorem dihOrCyc_quot {X : Type} [Group X] [Finite X] (h1 : Work.GW2.DihOrCycHeredProp)
    (hSyl : Work.GW2.DihOrCycSylow X) (N : Subgroup X) [N.Normal] :
    Work.GW2.DihOrCycSylow (X ⧸ N) :=
  (h1 X hSyl).2 N

/-! ## The main theorem -/

/-- **D110ii** (`Work.GW2.D110iiProp`, Bender 1981 1.10(ii)): for a D-group `X` and an involution
`t`, every element of `F_{2'}(C_X(t))` induces an inner automorphism of `E(X) = layer X`.

`h5` makes the layer a single quasisimple subgroup `E`; `h7` gives `E/Z(E) ≅ A_7` or `L_2(q)`.
If `t` centralizes `E`, then `x ∈ F(C_X(t))` has `[x,E] ≤ F(C_X(t)) ∩ E ≤ Z(E)`, and a central
cocycle on the perfect group `E` is trivial, so `x` centralizes `E`.  Otherwise apply `h10a`
(resp. `hautA7`) to `Q = Y/C` with `Y = E ⊔ C_X(t)`, `C = C_X(E)`, whose normal subgroup
`L = EC/C` is isomorphic to `E/Z(E)` (`C ∩ E = Z(E)`); `h1` gives `DihOrCycSylow Q`, and the
`F_{2'}`-membership transfers to `Q` by `map_fittingPiIn_centralizer_le`.  The conclusion
`x̄ ∈ L` means `x ∈ E·C_X(E)`, i.e. `x` induces an inner automorphism of `E`. -/
theorem d110ii (h10a : Work.GW2.D110iiModelProp) (h7 : Work.GW2.LayerShapeProp)
    (h5 : Work.GW2.LayerUniqueProp) (h1 : Work.GW2.DihOrCycHeredProp)
    (hautA7 : Work.GW2.AutA7Prop) (h4 : Work.GW2.QuasisimpleSylowProp)
    (h6 : Work.GW2.QuasisimpleCenterOddProp) : Work.GW2.D110iiProp := by
  intro X _ _ hFT hSyl hD t ht x hx
  have hxK : x ∈ Subgroup.centralizer ({t} : Set X) := fittingPiIn_le_self _ hx
  by_cases hbot : Work.GW2.layer X = ⊥
  · -- the layer is trivial: `e = 1`
    refine ⟨1, ?_, ?_⟩
    · rw [hbot]; exact Subgroup.mem_bot.mpr rfl
    · intro y hy
      have hy1 : y = 1 := by rw [hbot] at hy; simpa using hy
      rw [hy1]; simp
  · obtain ⟨E, hEn, hEq, hlay⟩ := exists_quasisimple_of_layer_ne_bot h5 hFT hSyl hbot
    haveI := hEn
    have hshape := h7 X hFT hSyl hD E hEn hEq
    by_cases htC : t ∈ Subgroup.centralizer (E : Set X)
    · -- Case (i): `t` centralizes `E`, hence `E ≤ C_X(t)`.
      have hEt : E ≤ Subgroup.centralizer ({t} : Set X) := by
        intro e he
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        rw [Set.mem_singleton_iff.mp hy]
        exact (Subgroup.mem_centralizer_iff.mp htC e he).symm
      have hxcen : x ∈ Subgroup.centralizer (E : Set X) :=
        centralizes_of_mem_fittingPiIn E hEq t x hEt hxK hx
      refine ⟨1, ?_, ?_⟩
      · rw [hlay]; exact E.one_mem
      · intro y hy
        rw [hlay] at hy
        have hcomm : y * x = x * y := Subgroup.mem_centralizer_iff.mp hxcen y hy
        simp only [one_mul, inv_one, mul_one]
        calc x * y * x⁻¹ = (x * y) * x⁻¹ := by rw [mul_assoc]
          _ = (y * x) * x⁻¹ := by rw [hcomm]
          _ = y := by rw [mul_assoc, mul_inv_cancel, mul_one]
    · -- Case (ii): `t ∉ C_X(E)`; quotient by `C_X(E)`.
      set Y : Subgroup X := E ⊔ Subgroup.centralizer ({t} : Set X) with hYdef
      set C : Subgroup X := Subgroup.centralizer (E : Set X) with hCdef
      have hEY : E ≤ Y := hYdef ▸ le_sup_left
      have htY : t ∈ Y := hYdef ▸ Subgroup.mem_sup_right
        (Subgroup.mem_centralizer_iff.mpr (by intro y hy; rw [Set.mem_singleton_iff.mp hy]))
      have hxY : x ∈ Y := hYdef ▸ Subgroup.mem_sup_right hxK
      have hCY : Subgroup.centralizer ({t} : Set X) ≤ Y := hYdef ▸ le_sup_right
      let tx : ↥Y := ⟨t, htY⟩
      let xY : ↥Y := ⟨x, hxY⟩
      haveI hCn : C.Normal := Subgroup.normal_centralizer
      haveI hNn : (C.subgroupOf Y).Normal := Subgroup.normal_subgroupOf
      -- the facts about the image of `E` in the quotient
      have hfacts := map_centralizer_eq_bot_and_equiv E Y hEY hEn hEq
      obtain ⟨hLnorm, hLcen, hLiso⟩ := hfacts
      -- `h1` for `Y` and for the quotient
      have hSylY : Work.GW2.DihOrCycSylow ↥Y := dihOrCyc_sub h1 hSyl Y
      have hSylQ : Work.GW2.DihOrCycSylow (↥Y ⧸ (C.subgroupOf Y)) :=
        dihOrCyc_quot h1 hSylY (C.subgroupOf Y)
      -- `tx = t` viewed in `Y`
      have htx2 : orderOf tx = 2 := (Subgroup.orderOf_coe tx).symm.trans ht
      have hxK' : xY ∈ Subgroup.centralizer ({tx} : Set ↥Y) := by
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        rw [Set.mem_singleton_iff.mp hy]
        apply Subtype.ext
        show t * x = x * t
        exact Subgroup.mem_centralizer_iff.mp hxK t (Set.mem_singleton t)
      have hcent : Subgroup.centralizer ({tx} : Set ↥Y) =
          (Subgroup.centralizer ({t} : Set X)).subgroupOf Y := by
        ext y
        rw [Subgroup.mem_centralizer_iff, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
        constructor
        · intro h s hs
          rw [Set.mem_singleton_iff.mp hs]
          have h1 := h tx (Set.mem_singleton tx)
          have h2 := congrArg (fun z : ↥Y => (z : X)) h1
          simpa [tx] using h2
        · intro h w hw
          rw [Set.mem_singleton_iff.mp hw]
          apply Subtype.ext
          have h1 := h t (Set.mem_singleton t)
          simpa [tx] using h1
      have hxYfit : xY ∈ Work.GW2.fittingPiIn {n : ℕ | n ≠ 2}
          (Subgroup.centralizer ({tx} : Set ↥Y)) := by
        rw [hcent]
        have h := fittingPiIn_subgroupOf (Subgroup.centralizer ({t} : Set X)) Y hCY x hxK hx
        simpa [xY] using h
      have htq : orderOf ((QuotientGroup.mk' (C.subgroupOf Y)) tx) = 2 := by
        have ht2 : tx ^ 2 = 1 := by
          have h := pow_orderOf_eq_one tx
          rw [htx2] at h
          simpa [pow_two] using h
        refine orderOf_eq_prime ?_ ?_
        · rw [← map_pow, ht2, map_one]
        · intro hcontra
          have hmem : tx ∈ (QuotientGroup.mk' (C.subgroupOf Y)).ker :=
            MonoidHom.mem_ker.mpr hcontra
          rw [QuotientGroup.ker_mk'] at hmem
          exact htC (by simpa [tx] using Subgroup.mem_subgroupOf.mp hmem)
      -- the `F_{2'}`-membership transfers to the quotient
      have hxq : (QuotientGroup.mk' (C.subgroupOf Y)) xY ∈
          Work.GW2.fittingPiIn {2}ᶜ
            (Subgroup.centralizer
              ({(QuotientGroup.mk' (C.subgroupOf Y)) tx} : Set (↥Y ⧸ (C.subgroupOf Y)))) := by
        rw [show ({2}ᶜ : Set ℕ) = {n : ℕ | n ≠ 2} from by ext m; simp]
        have hNodd : Odd (Nat.card ↥(C.subgroupOf Y)) := by
          have hCodd := odd_card_centralizer_of_quasisimple h4 h6 hFT hSyl E hEq
          have h1 : Nat.card ↥(C.subgroupOf Y) = Nat.card ↥(C ⊓ Y) := by
            rw [← Subgroup.subgroupOf_map_subtype]
            exact (Nat.card_congr (Subgroup.equivMapOfInjective _ _ Y.subtype_injective).toEquiv)
          rw [h1]
          exact Odd.of_dvd_nat hCodd (Subgroup.card_dvd_of_le inf_le_left)
        exact fittingPiIn_centralizer_transfer_odd (C.subgroupOf Y) hNodd tx xY htx2 hxK' hxYfit
      -- `h10a` / `hautA7` give `π x ∈ L`
      have hxL : (QuotientGroup.mk' (C.subgroupOf Y)) xY ∈
          (E.subgroupOf Y).map (QuotientGroup.mk' (C.subgroupOf Y)) := by
        rcases hshape with hA7 | ⟨p, k, hpF, hodd, hq, hisoE⟩
        · obtain ⟨φ⟩ := hLiso
          obtain ⟨ψ⟩ := hA7
          have htop := hautA7 (↥Y ⧸ (C.subgroupOf Y))
            ((E.subgroupOf Y).map (QuotientGroup.mk' (C.subgroupOf Y))) hLnorm ⟨φ.trans ψ⟩ hLcen hSylQ
          rw [htop]; exact Subgroup.mem_top _
        · haveI := hpF
          obtain ⟨φ⟩ := hLiso
          obtain ⟨ψ⟩ := hisoE
          have hle := h10a (↥Y ⧸ (C.subgroupOf Y))
            ((E.subgroupOf Y).map (QuotientGroup.mk' (C.subgroupOf Y))) p k hodd hq
            hLnorm ⟨φ.trans ψ⟩ hLcen hSylQ
            ((QuotientGroup.mk' (C.subgroupOf Y)) tx) htq
          exact hle hxq
      -- `π x ∈ π(E)`: `x` differs from an element of `E` by an element of `C_X(E)`
      obtain ⟨e, heE, heπ⟩ := Subgroup.mem_map.mp hxL
      have heE' : (e : X) ∈ E := Subgroup.mem_subgroupOf.mp heE
      have hcC : (e : X) * x⁻¹ ∈ C := by
        have hker : (QuotientGroup.mk' (C.subgroupOf Y))
            ⟨(e : X) * x⁻¹, Y.mul_mem (hEY heE') (Y.inv_mem hxY)⟩ = 1 := by
          rw [show (⟨(e : X) * x⁻¹, Y.mul_mem (hEY heE') (Y.inv_mem hxY)⟩ : ↥Y)
                = e * xY⁻¹ from Subtype.ext rfl, map_mul, map_inv, heπ, mul_inv_cancel]
        have hmem : (⟨(e : X) * x⁻¹, Y.mul_mem (hEY heE') (Y.inv_mem hxY)⟩ : ↥Y)
            ∈ C.subgroupOf Y := by
          rw [← QuotientGroup.ker_mk' (C.subgroupOf Y)]
          exact MonoidHom.mem_ker.mpr hker
        exact Subgroup.mem_subgroupOf.mp hmem
      refine ⟨(e : X), by rw [hlay]; exact heE', ?_⟩
      intro y hy
      rw [hlay] at hy
      have hx_eq : x = ((e : X) * x⁻¹)⁻¹ * (e : X) := by group
      have hcen : ∀ z ∈ E, ((e : X) * x⁻¹)⁻¹ * z * ((e : X) * x⁻¹) = z := by
        intro z hz
        have hcomm : z * ((e : X) * x⁻¹) = ((e : X) * x⁻¹) * z :=
          Subgroup.mem_centralizer_iff.mp hcC z hz
        calc ((e : X) * x⁻¹)⁻¹ * z * ((e : X) * x⁻¹)
            = ((e : X) * x⁻¹)⁻¹ * (z * ((e : X) * x⁻¹)) := by rw [mul_assoc]
          _ = ((e : X) * x⁻¹)⁻¹ * (((e : X) * x⁻¹) * z) := by rw [hcomm]
          _ = z := by group
      have hzE : (e : X) * y * (e : X)⁻¹ ∈ E := E.mul_mem (E.mul_mem heE' hy) (E.inv_mem heE')
      rw [hx_eq]
      calc ((e : X) * x⁻¹)⁻¹ * (e : X) * y * (((e : X) * x⁻¹)⁻¹ * (e : X))⁻¹
          = ((e : X) * x⁻¹)⁻¹ * ((e : X) * y * (e : X)⁻¹) * ((e : X) * x⁻¹) := by group
        _ = (e : X) * y * (e : X)⁻¹ := hcen _ hzE

end Work.DSTR
