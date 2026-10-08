import Mathlib
import Submission.Work.ThreePoints.P3Sub.Basic
import Submission.Work.ThreePoints.Basic
import Submission.Work.ThreePoints.Omega
import Submission.Work.ThreePoints.isStronglyEmbedded_map_quotient
import Submission.Work.ThreePoints.oddCore_le_of_stronglyEmbedded
import Submission.Work.Reductions.OddResidual
import Submission.Work.ThreePoints.P3NeBot.isStronglyEmbedded_map_of_ker_odd
import Submission.Work.ThreePoints.P3NeBot.exists_sylow_compl_of_isPGroup_image
import Submission.Work.BrauerSuzuki.OddCore.oddCard_oddCore
import Submission.Work.PGroup.card_sup_mul_card_inf_of_le_normalizer

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false

open LeanEval.GroupTheory.Defs

namespace Work.ThreePoints.P3Sub

/-- The rank-one model split: `hMod` transferred to a group `F` whose quotient by its centre is a simple Bender group.

Let `F` be finite, `H ≤ F` strongly embedded, `t ∈ F` an involution outside `H`, `O_{2'}(F) = Z(F)`, and `F/Z(F)` a simple Bender group (via a surjection `φ` with kernel `Subgroup.center F`). Then there is a `2`-subgroup `S ≤ H` with `2` not dividing `[H : S]`, normal in `H`, with `S ⊓ twoPoint H t = ⊥` and `S ⊔ twoPoint H t = H`.

Route: `Z := Subgroup.center F = O_{2'}(F)` has odd order; `Z ≤ H` (`Z` centralises `H`, so `Z ≤ N_F(H) = H`, using `Work.ThreePoints.IsStronglyEmbedded.normalizer_eq`); strong embeddedness passes to the image `H.map φ` (quotient by an odd normal subgroup), and `φ t` is an involution outside it; `hMod` at that image gives `S₀`, whose preimage in `F` is `Z × S` with `S` the unique Sylow `2`-subgroup; `S` is characteristic there and `H` normalises the preimage, so `S` is normal in `H`; the splitting transfers from `F/Z(F)`. -/
theorem model_split_b {F : Type} [Group F] [Finite F]
    (hMod : Submission.Blueprint.ModelFactsProp)
    {H : Subgroup F} (hH : LeanEval.GroupTheory.Defs.IsStronglyEmbedded H) {t : F}
    (ht : orderOf t = 2) (htH : t ∉ H)
    (hcenter : Submission.Blueprint.oddCore F = Subgroup.center F)
    (hmodel : ∃ (Y : Type) (_ : Group Y) (φ : F →* Y), Function.Surjective φ ∧
      φ.ker = Subgroup.center F ∧ LeanEval.GroupTheory.Defs.IsSimpleBenderGroup Y) :
    ∃ S : Subgroup F, IsPGroup 2 S ∧ S ≤ H ∧ ¬ 2 ∣ (S.subgroupOf H).index ∧
      H ≤ Subgroup.normalizer (S : Set F) ∧
      S ⊓ Submission.Blueprint.twoPoint H t = ⊥ ∧
      S ⊔ Submission.Blueprint.twoPoint H t = H := by
  classical
  obtain ⟨Y, hYG, φ, hφsurj, hφker, hBender⟩ := hmodel
  letI := hYG
  haveI : Finite Y := Finite.of_surjective φ hφsurj
  -- ## 0. The centre `Z(F) = O_{2'}(F)` has odd order and lies in `H`
  have hoddZ : Odd (Nat.card (Subgroup.center F)) := by
    rw [← hcenter]
    exact Work.BrauerSuzuki.OddCore.oddCard_oddCore
  have hZH : Subgroup.center F ≤ H := by
    have h1 : Subgroup.center F ≤ Subgroup.normalizer (H : Set F) :=
      Subgroup.center_le_normalizer _
    rw [Work.ThreePoints.IsStronglyEmbedded.normalizer_eq hH] at h1
    exact h1
  have hkerH : φ.ker ≤ H := by rw [hφker]; exact hZH
  have hoddKer : Odd (Nat.card ↥φ.ker) := by rw [hφker]; exact hoddZ
  have hcomapH : Subgroup.comap φ (H.map φ) = H :=
    Subgroup.comap_map_eq_self (f := φ) (H := H) hkerH
  -- ## 1. Strong embeddedness passes to the image `H.map φ`
  have hHφ : IsStronglyEmbedded (H.map φ) :=
    Work.ThreePoints.P3NeBot.isStronglyEmbedded_map_of_ker_odd φ hφsurj hoddKer hkerH hH
  -- ## 2. `φ t` is an involution outside `H.map φ`
  have htφ2 : orderOf (φ t) = 2 := by
    have hdvd0 : orderOf (φ t) ∣ orderOf t := orderOf_map_dvd φ t
    have hdvd : orderOf (φ t) ∣ 2 := by rwa [ht] at hdvd0
    have hne : orderOf (φ t) ≠ 1 := by
      intro h1
      have hmem : t ∈ φ.ker := by
        rw [MonoidHom.mem_ker]
        exact orderOf_eq_one_iff.mp h1
      exact htH (hZH (hφker ▸ hmem))
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact absurd h hne
    · exact h
  have htφH : φ t ∉ H.map φ := by
    intro hmem
    obtain ⟨h, hh, hhφ⟩ := Subgroup.mem_map.mp hmem
    have hmemker : h⁻¹ * t ∈ φ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hhφ, inv_mul_cancel]
    have htH' : h⁻¹ * t ∈ H := hZH (hφker ▸ hmemker)
    exact htH (by simpa [mul_assoc] using H.mul_mem hh htH')
  -- ## 3. The model facts in `Y`, applied to the image of `H` and `φ t`
  obtain ⟨-, -, -, hmain⟩ := hMod Y hBender
  obtain ⟨-, hsplit⟩ := hmain (H.map φ) hHφ
  obtain ⟨S₀, _K₀, hS0pg, hS0le, hHφN, hS0inf, hS0sup, -, -, -⟩ := hsplit (φ t) htφ2 htφH
  -- ## 4. `P := φ⁻¹(S₀)` is a subgroup of `H` with `P/Z` a `2`-group
  set P : Subgroup F := Subgroup.comap φ S₀ with hPdef
  have hPleH : P ≤ H := by
    have h1 : Subgroup.comap φ S₀ ≤ Subgroup.comap φ (H.map φ) := Subgroup.comap_mono hS0le
    rw [hcomapH] at h1
    rwa [hPdef]
  have hZleP : Subgroup.center F ≤ P := by
    intro z hz
    rw [hPdef, Subgroup.mem_comap]
    have hz1 : φ z = 1 := by
      rw [← MonoidHom.mem_ker, hφker]
      exact hz
    rw [hz1]
    exact S₀.one_mem
  have hmapP : Subgroup.map φ P = S₀ := by
    rw [hPdef, Subgroup.map_comap_eq, MonoidHom.range_eq_top_of_surjective φ hφsurj, top_inf_eq]
  have hP2 : IsPGroup 2 (Subgroup.map φ P) := by rw [hmapP]; exact hS0pg
  -- ## 5. The Sylow `2`-subgroup `S` of `P` complementary to `Z(F)`
  obtain ⟨S, hSP, hSpg, hZinfS, hZsupS, huniq⟩ :=
    Work.ThreePoints.P3NeBot.exists_sylow_compl_of_isPGroup_image (Subgroup.center F) P le_rfl hZleP hoddZ φ hφker hP2
  have hSleH : S ≤ H := hSP.trans hPleH
  -- ## 6. `H` normalises `P`, and `φ` carries `S` onto `S₀`
  have hhkP : ∀ h ∈ H, ∀ k ∈ P, h * k * h⁻¹ ∈ P := by
    intro h hh k hk
    rw [hPdef, Subgroup.mem_comap] at hk ⊢
    have hφh : φ h ∈ Subgroup.normalizer (S₀ : Set Y) :=
      hHφN (Subgroup.mem_map.mpr ⟨h, hh, rfl⟩)
    rw [Subgroup.mem_normalizer_iff] at hφh
    have h2 := (hφh (φ k)).mp hk
    simpa only [map_mul, map_inv] using h2
  have hHN_P : H ≤ Subgroup.normalizer (P : Set F) :=
    (Subgroup.le_normalizer_iff (H := H) (K := P)).mpr hhkP
  have hφS : Subgroup.map φ S = S₀ := by
    have h1 : Subgroup.map φ (Subgroup.center F ⊔ S) = Subgroup.map φ P := by rw [hZsupS]
    rw [Subgroup.map_sup] at h1
    have h2 : Subgroup.map φ (Subgroup.center F) = ⊥ := by
      rw [show Subgroup.center F = φ.ker from hφker.symm, Subgroup.map_ker_self]
    rw [h2, bot_sup_eq] at h1
    rwa [hmapP] at h1
  -- ## 7. `S` is the unique Sylow `2`-subgroup of `P`, hence normal in `H`
  have hleP : ∀ h ∈ H, Subgroup.map (MulAut.conj h).toMonoidHom S ≤ P := by
    intro h hh
    rintro x ⟨s, hs, hx⟩
    rw [← hx, Work.ThreePoints.mulAut_conj_toMonoidHom_apply]
    exact hhkP h hh s (hSP hs)
  have hHNS : H ≤ Subgroup.normalizer (S : Set F) := by
    intro h hh
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have hle := hleP h hh
    have hpg : IsPGroup 2 (Subgroup.map (MulAut.conj h).toMonoidHom S) := hSpg.map _
    have hle2 : Subgroup.map (MulAut.conj h).toMonoidHom S ≤ S := huniq _ hle hpg
    have hcard : Nat.card ↥(Subgroup.map (MulAut.conj h).toMonoidHom S) = Nat.card ↥S :=
      Subgroup.card_map_of_injective (MulAut.conj h).injective
    exact Subgroup.eq_of_le_of_card_ge hle2 (le_of_eq hcard.symm)
  -- ## 8. The two-point stabiliser `D = H ⊓ H^t`
  have hDleH : Submission.Blueprint.twoPoint H t ≤ H := inf_le_left
  have hDodd : Odd (Nat.card ↥(Submission.Blueprint.twoPoint H t)) := hH.2.2 t htH
  have hZleD : Subgroup.center F ≤ Submission.Blueprint.twoPoint H t := by
    refine le_inf hZH ?_
    intro z hz
    rw [Work.ThreePoints.mem_conj_iff]
    have hcomm : t⁻¹ * z * t = z := by
      have h1 : t * z = z * t := (Subgroup.mem_center_iff.mp hz) t
      calc t⁻¹ * z * t = t⁻¹ * (z * t) := by rw [mul_assoc]
        _ = t⁻¹ * (t * z) := by rw [h1]
        _ = z := by rw [← mul_assoc, inv_mul_cancel, one_mul]
    rw [hcomm]
    exact hZH hz
  have hφD : Subgroup.map φ (Submission.Blueprint.twoPoint H t)
      = Submission.Blueprint.twoPoint (H.map φ) (φ t) := by
    show Subgroup.map φ (H ⊓ Submission.Blueprint.conj t H)
      = H.map φ ⊓ Submission.Blueprint.conj (φ t) (H.map φ)
    rw [Commons.GroupTheory.Subgroup.map_inf_eq_of_ker_le φ H (Submission.Blueprint.conj t H) hkerH,
      Commons.GroupTheory.Subgroup.map_conj_map φ H t]
  -- ## 9. The splitting `H = S ⋊ D`
  have hSDbot : S ⊓ Submission.Blueprint.twoPoint H t = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_inf] at hx
    have hxS0 : φ x ∈ S₀ := by
      rw [← hφS]; exact Subgroup.mem_map.mpr ⟨x, hx.1, rfl⟩
    have hxD0 : φ x ∈ Submission.Blueprint.twoPoint (H.map φ) (φ t) := by
      rw [← hφD]; exact Subgroup.mem_map.mpr ⟨x, hx.2, rfl⟩
    have hxbot : φ x ∈ (⊥ : Subgroup Y) := by
      rw [← hS0inf]; exact Subgroup.mem_inf.mpr ⟨hxS0, hxD0⟩
    rw [Subgroup.mem_bot] at hxbot
    have hxker : x ∈ φ.ker := by rw [MonoidHom.mem_ker]; exact hxbot
    have hxc : x ∈ Subgroup.center F := by rwa [hφker] at hxker
    have hxi : x ∈ Subgroup.center F ⊓ S := Subgroup.mem_inf.mpr ⟨hxc, hx.1⟩
    rwa [hZinfS, Subgroup.mem_bot] at hxi
  have hSDsup : S ⊔ Submission.Blueprint.twoPoint H t = H := by
    have hmap : Subgroup.map φ (S ⊔ Submission.Blueprint.twoPoint H t) = H.map φ := by
      rw [Subgroup.map_sup, hφS, hφD, hS0sup]
    have hker_le : φ.ker ≤ S ⊔ Submission.Blueprint.twoPoint H t := by
      rw [hφker]
      exact hZleD.trans le_sup_right
    calc S ⊔ Submission.Blueprint.twoPoint H t
        = Subgroup.comap φ (Subgroup.map φ (S ⊔ Submission.Blueprint.twoPoint H t)) :=
          (Subgroup.comap_map_eq_self (f := φ) hker_le).symm
      _ = Subgroup.comap φ (H.map φ) := by rw [hmap]
      _ = H := hcomapH
  -- ## 10. The index `[H : S] = |D|` is odd
  have hDnormS : Submission.Blueprint.twoPoint H t ≤ Subgroup.normalizer (S : Set F) :=
    hDleH.trans hHNS
  have hcardH : Nat.card ↥H = Nat.card ↥S * Nat.card ↥(Submission.Blueprint.twoPoint H t) := by
    have h := Work.PGroup.card_sup_mul_card_inf_of_le_normalizer (H := S)
      (K := Submission.Blueprint.twoPoint H t) hDnormS
    rw [hSDsup, hSDbot, Subgroup.card_bot, mul_one] at h
    exact h
  have hIdx : Nat.card ↥S * (S.subgroupOf H).index = Nat.card ↥H := by
    have h1 := Subgroup.card_mul_index (S.subgroupOf H)
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSleH).toEquiv] at h1
  have hindex_eq : (S.subgroupOf H).index = Nat.card ↥(Submission.Blueprint.twoPoint H t) :=
    Nat.mul_left_cancel (Nat.card_pos (α := ↥S)) (hIdx.trans hcardH)
  exact ⟨S, hSpg, hSleH, by
      rw [hindex_eq]
      exact (Work.ThreePoints.odd_iff_not_two_dvd _).mp hDodd,
    hHNS, hSDbot, hSDsup⟩

end Work.ThreePoints.P3Sub
