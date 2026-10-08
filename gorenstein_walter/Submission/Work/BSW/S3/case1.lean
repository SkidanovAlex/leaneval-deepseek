/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gorenstein–Walter formalisation team (area BSW, `Work.BSW`)

# Bender §3.3, case (i): `Q = F = C_G(x)`, `D = K`

This file proves `Work.BSW.BSWCase1Prop` (`Submission/Work/BSW/S3/Defs.lean`), Bender's §3.3
(*The Brauer–Suzuki–Wall theorem*, Illinois J. Math. **18** (1974) 229–235, pp. 232–233):

in case (i) of §3.2, that is when `|C(x)| = 2|K| + 1` for an element `x ∉ H^G` inverted by `t`
and normalised by `K`, Bender's conclusion (1)–(4) holds with `Q = F = C_G(x)` and `D = K`, i.e.
`IsBSWData G (2 * |K| + 1)`.

The proof combines

* the already proved §3.1 (`Work.BSW.S3.s31`): `F` is abelian with `C_G(a) = F` for `a ∈ F#`,
  `F` is TI with respect to its normalizer, the normalizer of `F` is `F ⊔ (K ⊓ N_G(F))`, and the
  involutions of `N_G(F)` are the coset `tF`;
* the arithmetic `|G| = (2k+1)(k+1)(2k)` with `k = |K|`;
* the two-orbit prime power lemma `Work.BSW.S3.twoOrbitPrimePower` (applied to the conjugation
  action of `K` on `F = C_G(x)`, which is fixed-point-free on `F#` because `C_G(a) = F` for
  `a ∈ F#` and `F ⊓ K = 1`).

Everything is proved from Mathlib and the (sorry-free) workspace modules; no `sorry` remains.
-/
import Mathlib
import Submission.Work.BSW.S3.Defs
import Submission.Work.BSW.S3.twoOrbitPrimePower
import Submission.Work.BSW.S3.S31setup
import Submission.Work.BSW.S3.s31
import Submission.Work.BSW.S3.s36aux
import Submission.Work.BSW.Api.normalizer_K_eq
import Submission.Work.BSW.Api.card_sup_zpowers
import Submission.Work.BSW.Api.card_sup_of_le_normalizer_of_inf_eq_bot
import Submission.Work.BSW.Api.mem_centralizer_iff
import Submission.Work.BSW.Cases.S31core
import Submission.Work.BSW.Basic
import Submission.Work.BSW.Vocab

open scoped IsMulCommutative

namespace Work.BSW.S3

open Subgroup Work.GW2

/-! ## Two auxiliary facts

The first is the "`|F|` is a prime power" step of §3.3 (Bender's two-orbit argument of §3.8),
the second the statement that every non-trivial subgroup of `K` has the same normalizer as `K`
(Bender's condition (4) with `D = K`). -/

/-- **`|C_G(x)|` is a prime power.**  `K` acts on `F = C_G(x)` by conjugation (it normalises `F`),
fixed-point-freely on `F#` (`C_G(a) = F` for `a ∈ F#` and `F ⊓ K = 1`), and
`|F| = 2|K| + 1`, so `F#` is exactly two `K`-orbits; a two-orbit action on an abelian group of
odd order forces a prime power (`Work.BSW.S3.twoOrbitPrimePower`). -/
theorem primePowerAux {G : Type} [Group G] [Finite G] {t s x : G} {K : Subgroup G}
    (h : BSWHyps2 G t s K) (hx : x ∉ HG t) (hinv : t⁻¹ * x * t = x⁻¹)
    (hKn : K ≤ Subgroup.normalizer (Subgroup.centralizer ({x} : Set G) : Set G))
    (hcard : Nat.card (Subgroup.centralizer ({x} : Set G)) = 2 * Nat.card K + 1) :
    ∃ p e : ℕ, Nat.Prime p ∧ Nat.card (Subgroup.centralizer ({x} : Set G)) = p ^ e := by
  let F : Subgroup G := Subgroup.centralizer ({x} : Set G)
  haveI hcommF : IsMulCommutative ↥F := isMulCommutative_centralizer h hx hinv
  letI hmulact : MulDistribMulAction ↥K ↥F :=
    MulDistribMulAction.compHom ↥F
      ((Subgroup.normalizerMonoidHom F).comp (Subgroup.inclusion hKn))
  have hoddF : Odd (Nat.card ↥F) := odd_card_centralizer_of_notMem_HG h hx
  have hcard' : 2 * Nat.card ↥K + 1 = Nat.card ↥F := hcard.symm
  -- `K` acts fixed-point-freely on `F#`
  have hfree : ∀ d : ↥K, d ≠ 1 → ∀ a : ↥F, d • a = a → a = 1 := by
    intro d hd a ha
    by_contra ha1
    have hsm : ((d • a : ↥F) : G) = (d : G) * (a : G) * (d : G)⁻¹ := rfl
    have h1 : (d : G) * (a : G) * (d : G)⁻¹ = (a : G) := by
      rw [← hsm]
      exact congrArg Subtype.val ha
    have hC := centralizer_eq_of_mem_centralizer h hx hinv (a : G) a.2
      (fun h1 => ha1 (Subtype.ext h1))
    have hmem : (d : G) ∈ Subgroup.centralizer ({(a : G)} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc (d : G) * (a : G) = ((d : G) * (a : G) * (d : G)⁻¹) * (d : G) := by group
        _ = (a : G) * (d : G) := by rw [h1]
    rw [hC] at hmem
    have hmem2 : (d : G) ∈ Subgroup.centralizer ({x} : Set G) ⊓ K := ⟨hmem, d.2⟩
    rw [inf_K_centralizer_eq_bot h hx] at hmem2
    exact hd (Subtype.ext (Subgroup.mem_bot.mp hmem2))
  obtain ⟨p, e, hp, hpe⟩ := twoOrbitPrimePower (F := ↥F) (D := ↥K) hoddF hcard' hfree
  exact ⟨p, e, hp, hpe⟩

/-- **Every non-trivial subgroup of `K` has normalizer `N_G(K)`.**  Since `N_G(K) = C_G(t) = K⟨s⟩`
and `s` inverts `K`, the normalizer of `K` normalises every subgroup of `K`; conversely an element
normalising a non-trivial `X ≤ K` must lie in `N_G(K)` by the TI property of `K`. -/
theorem normalizerSubgroupKAux {G : Type} [Group G] [Finite G] {t s : G} {K : Subgroup G}
    (h : BSWHyps2 G t s K) :
    ∀ X : Subgroup G, X ≠ ⊥ → X ≤ K →
      Subgroup.normalizer (X : Set G) = Subgroup.normalizer (K : Set G) := by
  intro X hXne hXK
  haveI hKcomm : IsMulCommutative ↥K := Work.BSW.isMulCommutative_K h
  refine le_antisymm ?_ ?_
  · -- `N_G(X) ≤ N_G(K)`: otherwise `X ≤ K ⊓ K^g = ⊥` by the TI property.
    intro g hg
    by_contra hgK
    have hgK' : g ∉ Subgroup.centralizer ({t} : Set G) := by
      rw [← Work.BSW.Api.normalizer_K_eq h]
      exact hgK
    have hle : X ≤ K ⊓ conjSub g K := by
      intro z hz
      have hz' : g⁻¹ * z * g ∈ X := (Subgroup.mem_normalizer_iff''.mp hg z).mp hz
      refine ⟨hXK hz, ?_⟩
      change z ∈ conjSub g K
      rw [Work.BSW.S3.mem_conjSub_iff]
      exact hXK hz'
    rw [Work.BSW.TI h g hgK'] at hle
    exact hXne (le_bot_iff.mp hle)
  · -- `N_G(K) = C_G(t) = K⟨s⟩`, and both `K` and `s` normalise every `X ≤ K`.
    rw [Work.BSW.Api.normalizer_K_eq h, Work.BSW.centralizer_t_eq h]
    refine sup_le ?_ ?_
    · -- elements of `K` centralise `X` (K is abelian)
      intro k hk
      rw [Subgroup.mem_normalizer_iff]
      have key : ∀ y ∈ K, k * y * k⁻¹ = y := by
        intro y hy
        have hcomm := congrArg Subtype.val
          ((IsMulCommutative.is_comm (M := ↥K)).comm (⟨k, hk⟩ : ↥K) (⟨y, hy⟩ : ↥K))
        have hcomm' : k * y = y * k := hcomm
        rw [hcomm', mul_assoc, mul_inv_cancel, mul_one]
      intro z
      constructor
      · intro hz
        rw [key z (hXK hz)]
        exact hz
      · intro hz
        have hyK : k * z * k⁻¹ ∈ K := hXK hz
        have h2 : k⁻¹ * (k * z * k⁻¹) * k = k * z * k⁻¹ := by
          have hcomm := congrArg Subtype.val
            ((IsMulCommutative.is_comm (M := ↥K)).comm (⟨k⁻¹, K.inv_mem hk⟩ : ↥K)
              (⟨k * z * k⁻¹, hyK⟩ : ↥K))
          have hcomm' : k⁻¹ * (k * z * k⁻¹) = (k * z * k⁻¹) * k⁻¹ := hcomm
          rw [hcomm', mul_assoc, inv_mul_cancel, mul_one]
        have h3 : k⁻¹ * (k * z * k⁻¹) * k = z := by group
        rw [h2] at h3
        rwa [h3] at hz
    · -- `s` inverts `K`, hence setwise fixes every subgroup of `K`
      rw [Subgroup.zpowers_le]
      rw [Subgroup.mem_normalizer_iff]
      intro z
      constructor
      · intro hz
        have h1 : s * z * s⁻¹ = z⁻¹ := Work.BSW.inverts_s_K h z (hXK hz)
        rw [h1]
        exact X.inv_mem hz
      · intro hz
        have hyK : s * z * s⁻¹ ∈ K := hXK hz
        have h3 : s * (s * z * s⁻¹) * s⁻¹ = z := by
          have hss := Work.BSW.s_mul_self h
          have hssi : s⁻¹ * s⁻¹ = 1 := by rw [Work.BSW.s_inv h]; exact hss
          calc s * (s * z * s⁻¹) * s⁻¹ = (s * s) * z * (s⁻¹ * s⁻¹) := by group
            _ = z := by rw [hss, hssi, one_mul, mul_one]
        have h2 : s * (s * z * s⁻¹) * s⁻¹ = (s * z * s⁻¹)⁻¹ :=
          Work.BSW.inverts_s_K h (s * z * s⁻¹) hyK
        rw [h2] at h3
        rw [← h3]
        exact X.inv_mem hz

/-- **Bender §3.3, case (i)**: `Work.BSW.BSWCase1Prop`. -/
theorem case1 : Work.BSW.BSWCase1Prop := by
  intro G instG instFin t s K x h hk hx hinv hcard hKn hord
  let F : Subgroup G := Subgroup.centralizer ({x} : Set G)
  let M : Subgroup G := Subgroup.normalizer (F : Set G)
  -- §3.1, in the form of the contract `Work.BSW.BSWS31Prop`
  obtain ⟨hcommF, hoddF, hCa, hTI, hinfK, hnorm, hfree, hinvols, hiFn, hcop1, hcop2⟩ :=
    s31 G t s K x h hx hinv
  -- `|F| = 2|K| + 1` is a prime power
  obtain ⟨p, e, hp, hpe⟩ := primePowerAux h hx hinv hKn hcard
  have hFcard : Nat.card ↥F = 2 * Nat.card K + 1 := hcard
  have hpodd : Odd p := by
    refine hp.odd_of_ne_two ?_
    intro h2p
    subst h2p
    have he : 1 ≤ e := by
      by_contra h0
      have h0' : e = 0 := by omega
      rw [h0', pow_zero] at hpe
      omega
    have hdvd : 2 ∣ Nat.card ↥F := by
      rw [hpe]
      simpa using Nat.pow_dvd_pow 2 he
    exact (Nat.not_even_iff_odd.mpr hoddF) (even_iff_two_dvd.mpr hdvd)
  refine ⟨⟨p, e, ⟨hp⟩, hpodd, hFcard.symm.trans hpe⟩, ?_, F, ?_, ?_, ?_,
    ⟨K, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · -- `5 ≤ 2|K| + 1`
    omega
  · -- `|F| = q`
    exact hFcard
  · -- `C_G(F) = F`
    exact centralizer_centralizer_eq_self h hx hinv
  · -- `F` is TI with respect to its normalizer
    intro g hg
    have h1 := hTI g hg
    rw [eq_bot_iff] at h1 ⊢
    intro z hz
    exact h1 ⟨hz.1, Subgroup.map_mono (Subgroup.le_normalizer) hz.2⟩
  · -- `K` is abelian
    exact Work.BSW.isMulCommutative_K h
  · -- `|K| = (q - 1)/2`
    show Nat.card ↥K = (2 * Nat.card K + 1 - 1) / 2
    omega
  · -- `F ⊓ K = ⊥`
    exact hinfK
  · -- `N_G(F) = F ⊔ K`
    rw [hnorm, inf_eq_left.mpr hKn]
  · -- every non-trivial subgroup of `K` has normalizer `N_G(K)`
    intro X hXne hXK
    exact normalizerSubgroupKAux h X hXne hXK
  · -- `u = s` with `N_G(K) = K ⊔ ⟨s⟩`
    exact ⟨s, Work.BSW.orderOf_s h, Work.BSW.s_notMem_K h, Work.BSW.inverts_s_K h,
      by rw [Work.BSW.Api.normalizer_K_eq h, Work.BSW.centralizer_t_eq h]⟩
  · -- `|G| = q(q² - 1)/2`
    rw [hord]
    have hA : (2 * Nat.card K + 1) * (2 * Nat.card K + 1) - 1
        = 2 * (2 * Nat.card K * (Nat.card K + 1)) := by
      have h' : (2 * Nat.card K + 1) * (2 * Nat.card K + 1)
          = 2 * (2 * Nat.card K * (Nat.card K + 1)) + 1 := by ring
      omega
    rw [hA]
    have hdiv : (2 * Nat.card K + 1) * (2 * (2 * Nat.card K * (Nat.card K + 1))) / 2
        = (2 * Nat.card K + 1) * (2 * Nat.card K * (Nat.card K + 1)) := by
      rw [show (2 * Nat.card K + 1) * (2 * (2 * Nat.card K * (Nat.card K + 1)))
          = 2 * ((2 * Nat.card K + 1) * (2 * Nat.card K * (Nat.card K + 1))) by ring]
      exact Nat.mul_div_right _ (by norm_num : 0 < 2)
    rw [hdiv]
    ring

end Work.BSW.S3
