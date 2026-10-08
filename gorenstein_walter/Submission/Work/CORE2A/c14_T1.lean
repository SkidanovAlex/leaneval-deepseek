import Mathlib
import Submission.Work.CORE2A.TorusDefs
import Submission.Work.CORE2A.Basic
import Submission.Work.CORE2A.Thm26bVocab
import Submission.Work.CORE2A.c14_card_CN
import Submission.Work.CORE2A.c14_card_cent_two
import Submission.Work.CORE2A.c14_conj_t
import Submission.Work.CORE2A.c14_oddIndex
import Submission.Work.CORE2A.c14_coprime_relIndex

/-!
# CORE2A, pass 14, leaf **T1** (`c14_T1`)

Bender 1981, p. 220: the step pass 13 could not derive.  If `x ∈ Ĥ` is centralized by `t`, inverted
by an element `u` of the Sylow `2`-subgroup `S`, and has order prime to `k = |C_E(t) : Z(E)|`, then
`x` centralizes the layer `E(Ĥ)`.

The proof is the "centralizer count" of the design note (`_design_gw/Core14.lean` §2) plus one
parity observation.  With `E := layerIn B.Hhat`, `C := cE B = C_Ĥ(E)`, `Z := zE B = Z(E)`,
`Ct := C_G(t)` and `Mt` the normal subgroup of odd index in `Ĥ` containing `E ⊔ C` with
`[Mt : E ⊔ C] = 2`:

* `u ∈ S ≤ Ĥ` is a `2`-element of `Ĥ`, so `u ∈ Mt` (`c14_oddIndex`); since `x*u*x = u` gives
  `(x * u) ^ 2 = u ^ 2 ∈ Mt`, the same odd-index argument gives `x * u ∈ Mt`, and then
  `x ∈ Mt`;
* `|C_{Mt}(t)| = 2 |C_{E ⊔ C}(t)|` (`c14_card_cent_two`, using that every `Mt`-conjugate of `t` is
  an `E`-conjugate, `c14_conj_t`), and the second isomorphism computation `c14_card_CN` turns this
  into `|C_{Mt}(t) : C| = 2 k`;
* `x ∈ C_{Mt}(t)` and `C ⊴ C_{Mt}(t)`, hence `x ^ (2k) ∈ C`; `gcd(o(x), k) = 1` together with
  `2 ∣ k` (`c14_T1_two_dvd_kE_aux`: `t ∈ C_E(t)` has order `2` while `|Z(E)|` is odd,
  `Work.CORE2A.zE_odd`) gives `gcd(o(x), 2k) = 1`, so `x ∈ C` (`c14_coprime_relIndex`).

The two pure group-theoretic leaves used here are the workspace lemmas `Work.CORE2A.c14_oddIndex`
(`2`-power elements lie in a normal subgroup of odd index) and `Work.CORE2A.c14_coprime_relIndex`
(coprimality to the index); the square case of the former, needed for `x * u`, is the private
`c14_T1_sq_mem_aux` below.
-/

set_option linter.style.haveILetI false

open scoped MatrixGroups

namespace Work.CORE2A

open Subgroup
open Work.GW2

/-- `g ∈ H` whenever `g ∈ K` has `g ^ 2 ∈ H` for a normal subgroup `H ⊴ K` of odd index: with
`[K : H] = 2d + 1` one has `g ^ [K:H] = (g ^ 2) ^ d * g`, and `g ^ [K:H] ∈ H`
(`Subgroup.pow_index_mem`). -/
private theorem c14_T1_sq_mem_aux {G : Type} [Group G] {H K : Subgroup G} (hHK : H ≤ K)
    (hnorm : ∀ k ∈ K, ∀ h ∈ H, k * h * k⁻¹ ∈ H) (hodd : Odd (H.relIndex K)) {g : G} (hg : g ∈ K)
    (hg2 : g ^ 2 ∈ H) : g ∈ H := by
  haveI hN : (H.subgroupOf K).Normal :=
    (Subgroup.normal_subgroupOf_iff hHK).mpr (fun h k hh hk => hnorm k hk h hh)
  have hgm : g ^ H.relIndex K ∈ H := by
    have h := Subgroup.mem_subgroupOf.mp (Subgroup.pow_index_mem (H.subgroupOf K) (⟨g, hg⟩ : ↥K))
    rwa [Subgroup.coe_pow] at h
  obtain ⟨d, hd⟩ := hodd
  have hsplit : g ^ H.relIndex K = (g ^ 2) ^ d * g := by rw [hd, pow_succ, pow_mul]
  have h2d : (g ^ 2) ^ d ∈ H := H.pow_mem hg2 d
  have hmul : ((g ^ 2) ^ d)⁻¹ * g ^ H.relIndex K ∈ H := H.mul_mem (H.inv_mem h2d) hgm
  rwa [hsplit, inv_mul_cancel_left] at hmul

/-- `Z(E) ≤ C_E(t)`: the centre of the layer is contained in `E` and centralizes `t ∈ E`. -/
private theorem c14_T1_zE_le_aux {G : Type} [Group G] [Finite G] {B : Work.GW2.BenderSetup G}
    (ht : B.t ∈ Work.GW2.layerIn B.Hhat) :
    Work.GW2.zE B ≤ Work.GW2.layerIn B.Hhat ⊓ Subgroup.centralizer ({B.t} : Set G) := by
  refine le_inf zE_le ?_
  intro z hz
  rw [Subgroup.mem_centralizer_singleton_iff]
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hz
  have h := congrArg Subtype.val (Subgroup.mem_center_iff.mp hy (⟨B.t, ht⟩ : ↥(layerIn B.Hhat)))
  simpa using h.symm

/-- `2 ∣ k = |C_E(t) : Z(E)|`: the involution `t` lies in `C_E(t)`, while `|Z(E)|` is odd
(`Work.CORE2A.zE_odd`), so `2 ∣ |C_E(t)| = k · |Z(E)|`. -/
private theorem c14_T1_two_dvd_kE_aux (T : Work.GW2.LocalToolkit) (hFT : Work.GW2.FeitThompsonProp)
    {G : Type} [Group G] [Finite G] (hbc : Work.GW2.BenderCtx G) (B : Work.GW2.BenderSetup G)
    (ht : B.t ∈ Work.GW2.layerIn B.Hhat) : 2 ∣ Work.GW2.kE B := by
  have hE : layerIn B.Hhat ≠ ⊥ := by
    intro hbot
    exact bSetup_t_ne_one B (Subgroup.mem_bot.mp (hbot ▸ ht))
  have hZodd : Odd (Nat.card (zE B)) := zE_odd T hFT hbc B hE
  have hZle := c14_T1_zE_le_aux ht
  have hkcard : kE B * Nat.card (zE B) =
      Nat.card ↥(layerIn B.Hhat ⊓ Subgroup.centralizer ({B.t} : Set G)) := by
    have h := Subgroup.relIndex_mul_card (zE B)
      (layerIn B.Hhat ⊓ Subgroup.centralizer ({B.t} : Set G))
    rw [inf_eq_left.mpr hZle] at h
    exact h
  have htmem : B.t ∈ layerIn B.Hhat ⊓ Subgroup.centralizer ({B.t} : Set G) :=
    ⟨ht, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  have h2card : 2 ∣ Nat.card ↥(layerIn B.Hhat ⊓ Subgroup.centralizer ({B.t} : Set G)) := by
    have h := Subgroup.orderOf_dvd_natCard
      (layerIn B.Hhat ⊓ Subgroup.centralizer ({B.t} : Set G)) htmem
    rwa [B.t_order] at h
  have h2 : 2 ∣ kE B * Nat.card (zE B) := by rw [hkcard]; exact h2card
  exact (Nat.coprime_two_right.mpr hZodd).symm.dvd_of_dvd_mul_right h2

theorem c14_T1 (T : Work.GW2.LocalToolkit) (hFT : Work.GW2.FeitThompsonProp) {G : Type} [Group G] [Finite G] (hbc : Work.GW2.BenderCtx G) {B : Work.GW2.BenderSetup G} (ht : B.t ∈ Work.GW2.layerIn B.Hhat) (Mt : Subgroup G) (hMtH : Mt ≤ B.Hhat) (hNMt : Work.GW2.layerIn B.Hhat ⊔ Work.GW2.cE B ≤ Mt) (hMtn : ∀ h ∈ B.Hhat, ∀ m ∈ Mt, h * m * h⁻¹ ∈ Mt) (hMtodd : Odd (Mt.relIndex B.Hhat)) (hMt2 : (Work.GW2.layerIn B.Hhat ⊔ Work.GW2.cE B).relIndex Mt = 2) {x u : G} (hx : x ∈ B.Hhat) (hxt : x * B.t = B.t * x) (huS : u ∈ (B.S : Subgroup G)) (hinv : u * x * u⁻¹ = x⁻¹) (hcop : Nat.Coprime (orderOf x) (Work.GW2.kE B)) : x ∈ Subgroup.centralizer (Work.GW2.layerIn B.Hhat : Set G) := by
  have hE : layerIn B.Hhat ≠ ⊥ := by
    intro hbot
    exact bSetup_t_ne_one B (Subgroup.mem_bot.mp (hbot ▸ ht))
  have huH : u ∈ B.Hhat := bSetup_S_le_Hhat B huS
  -- Step 1: the `2`-element `u` lies in the odd-index normal subgroup `Mt`.
  have huMt : u ∈ Mt := by
    obtain ⟨n, hn⟩ := (B.S).isPGroup' ⟨u, huS⟩
    exact c14_oddIndex hMtH hMtn hMtodd huH
      (by simpa [Subgroup.coe_pow] using congrArg Subtype.val hn)
  -- Step 2: `x * u ∈ Mt` (its square is `u ^ 2`) and hence `x ∈ Mt`.
  have hxux : x * u * x = u := by
    have h := congrArg (fun y => x * y) hinv
    have h2 : x * u * x * u⁻¹ = 1 := by simpa [mul_assoc] using h
    calc x * u * x = (x * u * x * u⁻¹) * u := by group
      _ = 1 * u := by rw [h2]
      _ = u := one_mul u
  have hxu2 : (x * u) ^ 2 = u ^ 2 := by
    rw [pow_two, pow_two]
    calc x * u * (x * u) = (x * u * x) * u := by group
      _ = u * u := by rw [hxux]
  have hxum : x * u ∈ Mt :=
    c14_T1_sq_mem_aux (H := Mt) (K := B.Hhat) hMtH hMtn hMtodd (B.Hhat.mul_mem hx huH)
      (by rw [hxu2]; exact Mt.pow_mem huMt 2)
  have hxMt : x ∈ Mt := by
    have h : (x * u) * u⁻¹ ∈ Mt := Mt.mul_mem hxum (Mt.inv_mem huMt)
    have h1 : (x * u) * u⁻¹ = x := by group
    rwa [h1] at h
  -- Step 3: `|C_{Mt}(t) : C| = 2k`, `C = C_Ĥ(E)`.
  have hcl : ∀ m ∈ Mt, ∃ n ∈ layerIn B.Hhat ⊔ cE B, m * B.t * m⁻¹ = n * B.t * n⁻¹ := by
    intro m hm
    obtain ⟨e, he, heq⟩ := c14_conj_t T hFT hbc B ht m (hMtH hm)
    exact ⟨e, Subgroup.mem_sup_left he, heq⟩
  have hcent : Nat.card ↥(Mt ⊓ Subgroup.centralizer ({B.t} : Set G)) =
      2 * Nat.card ↥((layerIn B.Hhat ⊔ cE B) ⊓ Subgroup.centralizer ({B.t} : Set G)) :=
    c14_card_cent_two B.t hNMt hMt2 hcl
  have hCN := c14_card_CN T hFT hbc B ht
  have hZle : zE B ≤ layerIn B.Hhat ⊓ Subgroup.centralizer ({B.t} : Set G) := c14_T1_zE_le_aux ht
  have hkcard : kE B * Nat.card (zE B) =
      Nat.card ↥(layerIn B.Hhat ⊓ Subgroup.centralizer ({B.t} : Set G)) := by
    have h := Subgroup.relIndex_mul_card (zE B)
      (layerIn B.Hhat ⊓ Subgroup.centralizer ({B.t} : Set G))
    rw [inf_eq_left.mpr hZle] at h
    exact h
  have hcleA : cE B ≤ Mt ⊓ Subgroup.centralizer ({B.t} : Set G) := by
    refine le_inf (fun c hc => hNMt (Subgroup.mem_sup_right hc)) ?_
    intro c hc
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact ((Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hc).2) B.t ht).symm
  have hrelA : (cE B).relIndex (Mt ⊓ Subgroup.centralizer ({B.t} : Set G)) = 2 * kE B := by
    have h1 := Subgroup.relIndex_mul_card (cE B) (Mt ⊓ Subgroup.centralizer ({B.t} : Set G))
    rw [inf_eq_left.mpr hcleA] at h1
    have h2 : Nat.card ↥(Mt ⊓ Subgroup.centralizer ({B.t} : Set G)) * Nat.card (zE B) =
        2 * kE B * (Nat.card (zE B) * Nat.card (cE B)) := by
      calc Nat.card ↥(Mt ⊓ Subgroup.centralizer ({B.t} : Set G)) * Nat.card (zE B)
          = (2 * Nat.card ↥((layerIn B.Hhat ⊔ cE B) ⊓ Subgroup.centralizer ({B.t} : Set G))) *
              Nat.card (zE B) := by rw [hcent]
        _ = 2 * (Nat.card ↥((layerIn B.Hhat ⊔ cE B) ⊓ Subgroup.centralizer ({B.t} : Set G)) *
              Nat.card (zE B)) := by ring
        _ = 2 * (Nat.card ↥(layerIn B.Hhat ⊓ Subgroup.centralizer ({B.t} : Set G)) *
              Nat.card (cE B)) := by rw [hCN]
        _ = 2 * (kE B * Nat.card (zE B) * Nat.card (cE B)) := by rw [← hkcard]
        _ = 2 * kE B * (Nat.card (zE B) * Nat.card (cE B)) := by ring
    have hZpos : 0 < Nat.card (zE B) := Nat.card_pos
    have hCpos : 0 < Nat.card (cE B) := Nat.card_pos
    have key : (cE B).relIndex (Mt ⊓ Subgroup.centralizer ({B.t} : Set G)) *
          (Nat.card (zE B) * Nat.card (cE B)) =
        (2 * kE B) * (Nat.card (zE B) * Nat.card (cE B)) := by
      calc (cE B).relIndex (Mt ⊓ Subgroup.centralizer ({B.t} : Set G)) *
            (Nat.card (zE B) * Nat.card (cE B))
          = ((cE B).relIndex (Mt ⊓ Subgroup.centralizer ({B.t} : Set G)) *
              Nat.card (cE B)) * Nat.card (zE B) := by ring
        _ = Nat.card ↥(Mt ⊓ Subgroup.centralizer ({B.t} : Set G)) * Nat.card (zE B) := by rw [h1]
        _ = (2 * kE B) * (Nat.card (zE B) * Nat.card (cE B)) := h2
    exact Nat.eq_of_mul_eq_mul_right (Nat.mul_pos hZpos hCpos) key
  -- Step 4: `C` is normalized by `C_{Mt}(t)`.
  have hnorm : ∀ k ∈ Mt ⊓ Subgroup.centralizer ({B.t} : Set G), ∀ h ∈ cE B, k * h * k⁻¹ ∈ cE B := by
    intro k hk h hh
    have hkH : k ∈ B.Hhat := hMtH (Subgroup.mem_inf.mp hk).1
    have hhH : h ∈ B.Hhat := (Subgroup.mem_inf.mp hh).1
    have hhcent : ∀ y ∈ layerIn B.Hhat, y * h = h * y :=
      Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hh).2
    refine Subgroup.mem_inf.mpr ⟨B.Hhat.mul_mem (B.Hhat.mul_mem hkH hhH) (B.Hhat.inv_mem hkH), ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    have hke : k⁻¹ * e * k ∈ layerIn B.Hhat := by
      simpa [inv_inv] using
        layerIn_normal T hFT hbc B hE k⁻¹ (B.Hhat.inv_mem hkH) e he
    have h1 : (k⁻¹ * e * k) * h = h * (k⁻¹ * e * k) := hhcent _ hke
    calc e * (k * h * k⁻¹) = k * ((k⁻¹ * e * k) * h) * k⁻¹ := by group
      _ = k * (h * (k⁻¹ * e * k)) * k⁻¹ := by rw [h1]
      _ = (k * h * k⁻¹) * e := by group
  -- Step 5: coprimality and conclusion.
  have htwo : 2 ∣ kE B := c14_T1_two_dvd_kE_aux T hFT hbc B ht
  have hnot2 : ¬ 2 ∣ orderOf x := by
    intro h2
    have hd : 2 ∣ Nat.gcd (orderOf x) (kE B) := Nat.dvd_gcd h2 htwo
    rw [hcop.gcd_eq_one] at hd
    exact absurd (Nat.dvd_one.mp hd) (by norm_num)
  have hoddord : Odd (orderOf x) := by
    rw [← Nat.not_even_iff_odd]
    exact fun he => hnot2 (even_iff_two_dvd.mp he)
  have hcop2 : Nat.Coprime (orderOf x)
      ((cE B).relIndex (Mt ⊓ Subgroup.centralizer ({B.t} : Set G))) := by
    rw [hrelA]
    have h := hcop.mul_right (Nat.coprime_two_right.mpr hoddord)
    rwa [mul_comm] at h
  have hxC : x ∈ cE B :=
    c14_coprime_relIndex hcleA hnorm
      (Subgroup.mem_inf.mpr ⟨hxMt, Subgroup.mem_centralizer_singleton_iff.mpr hxt⟩) hcop2
  exact (Subgroup.mem_inf.mp hxC).2

end Work.CORE2A
