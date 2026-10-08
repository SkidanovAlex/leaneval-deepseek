import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.API
import Submission.Work.CORE4.Case2CountSetup
import Submission.Work.CORE4.Case2CountAssembly
import Submission.Work.CORE4.Case2CHs
import Submission.Work.CORE4.Case2KB0
import Submission.Work.CORE4.Case2BGData

namespace Work.CORE4

open Subgroup

/-! ## The single-reflection bound (Bender p. 227)

For a reflection `t ∈ S \ S₀` the centralizer of `t` in the dihedral Sylow 2-subgroup `S = S₀⟨s⟩`
has order `4`, so `Case2CHs` gives `2·|H : C_H(t)| = |S₀|·|U : C_U(t)|`.  Since §4 (5) says
`B₀ = C_U(s)` and the extra hypothesis of `Case2BGK` is `B₀ ≤ C_U(S)`, we have
`C_U(s) ≤ C_U(t)`, hence `|U : C_U(t)| ≤ |U : C_U(s)|`. -/
private theorem Case2BGK_term {G : Type} [Group G] [Finite G] (I : Work.GW2.C4Inputs)
    (B : Work.GW2.BenderSetup G) (h : Work.GW2.Case2Ctx B) (t : G)
    (htS : t ∈ (B.S : Subgroup G)) (ht0 : t ∉ B.S0)
    (htB0 : h.D.B0 ≤ Subgroup.centralizer ({t} : Set G)) :
    2 * ((Subgroup.centralizer ({t} : Set G)).relIndex B.H) ≤
      Nat.card ↥B.S0 * (B.U ⊓ Subgroup.centralizer ({h.D.s} : Set G)).relIndex B.U := by
  -- The index on the right is non-zero because everything is finite.
  have hne : (B.U ⊓ Subgroup.centralizer ({h.D.s} : Set G)).relIndex B.U ≠ 0 := by
    have hdvd := Subgroup.relIndex_dvd_card
      (H := B.U ⊓ Subgroup.centralizer ({h.D.s} : Set G)) (K := B.U)
    intro hz
    rw [hz] at hdvd
    exact Nat.card_pos.ne' (Nat.eq_zero_of_zero_dvd hdvd)
  -- `Case2CHs`: `2·|H : C_H(t)| = |S₀|·|U : C_U(t)|`.
  have hCH := Work.CORE4.Case2CHs G I B h t htS ht0
  -- `C_U(s) = B₀ ≤ C_U(t)`, hence `|U : C_U(t)| ≤ |U : C_U(s)|`.
  have hle : (B.U ⊓ Subgroup.centralizer ({t} : Set G)).relIndex B.U ≤
      (B.U ⊓ Subgroup.centralizer ({h.D.s} : Set G)).relIndex B.U := by
    refine Subgroup.relIndex_le_of_le_left (L := B.U) ?_ hne
    refine le_inf inf_le_left ?_
    rw [← Work.GW2.Case2Pre.B0_eq B h.D h.pre]
    exact htB0
  calc 2 * (Subgroup.centralizer ({t} : Set G)).relIndex B.H
      = 2 * (B.H ⊓ Subgroup.centralizer ({t} : Set G)).relIndex B.H := by
        rw [Subgroup.inf_relIndex_left]
    _ = Nat.card ↥B.S0 * (B.U ⊓ Subgroup.centralizer ({t} : Set G)).relIndex B.U := hCH
    _ ≤ Nat.card ↥B.S0 * (B.U ⊓ Subgroup.centralizer ({h.D.s} : Set G)).relIndex B.U :=
        Nat.mul_le_mul_left _ hle

/-- Bender–Glauberman's `k` for any `BGData` whose `S, S₀, t` are those of the §4 configuration
is at most `|S₀|·|U : C_U(s)|`: both reflections `t₁, t₂ ∈ S \ S₀` give index at most
`|S₀|·|U : C_U(s)|/2`. -/
private theorem Case2BGK_k_bound {G : Type} [Group G] [Finite G] (I : Work.GW2.C4Inputs)
    (B : Work.GW2.BenderSetup G) (h : Work.GW2.Case2Ctx B) (D : Work.GW2.BGData G)
    (hDS : (D.S : Subgroup G) = (B.S : Subgroup G)) (hDS0 : D.S0 = B.S0) (hDt : D.t = B.t)
    (hB0 : h.D.B0 ≤ Subgroup.centralizer ((B.S : Subgroup G) : Set G)) :
    D.k ≤ Nat.card ↥B.S0 * (B.U ⊓ Subgroup.centralizer ({h.D.s} : Set G)).relIndex B.U := by
  -- `D.H = B.H`.
  have hDH : D.H = B.H := by
    rw [Work.GW2.BGData.H, Work.GW2.BenderSetup.H, hDt]
  -- `t₁, t₂ ∈ S \ S₀` in the notation of `B`.
  have ht1S : D.t1 ∈ (B.S : Subgroup G) := hDS ▸ D.t1_mem
  have ht2S : D.t2 ∈ (B.S : Subgroup G) := hDS ▸ D.t2_mem
  have ht1n : D.t1 ∉ B.S0 := hDS0 ▸ D.t1_nmem
  have ht2n : D.t2 ∉ B.S0 := hDS0 ▸ D.t2_nmem
  -- `B₀ ≤ C_U(S) ≤ C_U(tᵢ)`.
  have ht1B0 : h.D.B0 ≤ Subgroup.centralizer ({D.t1} : Set G) :=
    le_trans hB0 (Subgroup.centralizer_le (by
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      rw [hx]; exact ht1S))
  have ht2B0 : h.D.B0 ≤ Subgroup.centralizer ({D.t2} : Set G) :=
    le_trans hB0 (Subgroup.centralizer_le (by
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      rw [hx]; exact ht2S))
  have hb1 := Case2BGK_term I B h D.t1 ht1S ht1n ht1B0
  have hb2 := Case2BGK_term I B h D.t2 ht2S ht2n ht2B0
  have hk1 : 2 * ((Subgroup.centralizer ({D.t1} : Set G)).relIndex D.H) ≤
      Nat.card ↥B.S0 * (B.U ⊓ Subgroup.centralizer ({h.D.s} : Set G)).relIndex B.U := by
    rw [hDH]; exact hb1
  have hk2 : 2 * ((Subgroup.centralizer ({D.t2} : Set G)).relIndex D.H) ≤
      Nat.card ↥B.S0 * (B.U ⊓ Subgroup.centralizer ({h.D.s} : Set G)).relIndex B.U := by
    rw [hDH]; exact hb2
  have hsum : 2 * D.k ≤
      2 * (Nat.card ↥B.S0 * (B.U ⊓ Subgroup.centralizer ({h.D.s} : Set G)).relIndex B.U) := by
    have e : D.k = (Subgroup.centralizer ({D.t1} : Set G)).relIndex D.H +
        (Subgroup.centralizer ({D.t2} : Set G)).relIndex D.H := rfl
    rw [e]
    omega
  omega

/-- Bender–Glauberman Theorem A applied in the §4 configuration, in the form needed for (10):
only the inequality `D.k ≤ k·u·p₀` is required, and the extra input is §4 (5) in the shape
`B₀ ≤ C_U(S)`, which gives `C_U(s) = B₀ ⊆ C_U(tᵢ)` for *any* `tᵢ ∈ S \ S₀`.

Bender–Glauberman's `k` is `|H : C_H(t₁)| + |H : C_H(t₂)|` for two `tᵢ ∈ S \ S₀`; for such a
reflection `|H : C_H(tᵢ)| = |S₀|·|U : C_U(tᵢ)|/2` (the centralizer of a reflection in the
dihedral `S = S₀⟨s⟩` has order `4`).  Since `C_U(s) ⊆ C_U(tᵢ)`, each term is at most
`|S₀|·|U : C_U(s)|/2`, so `D.k ≤ |S₀|·|U : C_U(s)|`.  And
`|S₀|·|U : C_U(s)| = |S₀|·|K|·|U : U ⊓ M| = k·|H : H ⊓ M| = k·u·p₀`
(using `k = |K|·|S₀|`, `B₀ = C_U(s)` and `|H : H ⊓ M| = |U : U ⊓ M|`). -/
theorem Case2BGK :
    ∀ (G : Type) [Group G] [Finite G] (I : Work.GW2.C4Inputs), Work.GW2.BenderCtx G →
      ∀ (B : Work.GW2.BenderSetup G) (h : Work.GW2.Case2Ctx B) (k u p0 : ℕ),
        k = Nat.card ↥h.D.K * Nat.card ↥B.S0 →
        (h.D.M ⊓ B.H).relIndex B.H = u * p0 →
        h.D.B0 ≤ Subgroup.centralizer ((B.S : Subgroup G) : Set G) →
        ∃ D : Work.GW2.BGData G,
          D.S = B.S ∧ D.S0 = B.S0 ∧ D.t = B.t ∧ D.k ≤ k * u * p0 := by
  intro G _ _ I hctx B h k u p0 hk huv hB0
  obtain ⟨D, hDS, hDS0, hDt⟩ := Work.CORE4.Case2BGData G I hctx B h
  refine ⟨D, Sylow.ext hDS, hDS0, hDt, ?_⟩
  have hbound := Case2BGK_k_bound I B h D hDS hDS0 hDt hB0
  have hkey : Nat.card ↥B.S0 * (B.U ⊓ Subgroup.centralizer ({h.D.s} : Set G)).relIndex B.U
      = k * u * p0 := by
    have hkb := Work.CORE4.Case2KB0_relIndex B h
    have hrim := Work.GW2.Case2Ctx.relIndex_H_inter_M I h
    calc Nat.card ↥B.S0 * (B.U ⊓ Subgroup.centralizer ({h.D.s} : Set G)).relIndex B.U
        = Nat.card ↥B.S0 * (Nat.card ↥h.D.K * (B.U ⊓ h.D.M).relIndex B.U) := by rw [hkb]
      _ = (Nat.card ↥h.D.K * Nat.card ↥B.S0) * (B.U ⊓ h.D.M).relIndex B.U := by ring
      _ = k * (h.D.M ⊓ B.H).relIndex B.H := by rw [← hk, ← hrim]
      _ = k * (u * p0) := by rw [huv]
      _ = k * u * p0 := by ring
  rw [hkey] at hbound
  exact hbound

end Work.CORE4
