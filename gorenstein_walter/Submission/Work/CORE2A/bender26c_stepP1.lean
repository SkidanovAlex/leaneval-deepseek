import Mathlib
import Submission.Work.CORE2A.Defs
import Submission.Work.CORE2A.Basic
import Submission.Work.CORE2A.bender26c_key
import Submission.Work.CORE2A.bender26c_stepA
import Submission.Work.CORE2A.P_eq_iSup_centralizer_conj

/-!
# CORE2A: Bender 1981, Theorem 2.6, step 3 — the `O_p` step for `P₁ = [t, C_P(s)]`

Bender 1981, p. 221 (proof of Theorem 2.6, third paragraph; printed page, lines 12–20):

> Lemma 2.1 yields a subgroup `V = (2,2)` of `S` such that `N_G(V) ⊄ Ĥ`.  By 1.1.iii,
> `C_P(s) ≰ C_P(t)` for some `s ∈ V#`.  Then `s = t^g`, `g ∈ G`, and
> `1 ≠ P₁ := [t, C_P(s)] ≤ C_P(s) = Ĥ^g ∩ P`.  Now 1.10.i comes into action and yields
> `P ≤ O_p(Ĥ)` and `P₁ ≤ O_p(Ĥ^g)`.  Lying in `O_p(Ĥ^g) = O_p(Ĥ)^g`, `P₁` centralizes `P^g`. …

This module formalises the *second* conclusion of 1.10.i, i.e.

`P₁ = ⁅⟨t⟩, P ⊓ C_G(s)⁆ ≤ O_p(M^g)`

for a coatom `M ≥ N_G(P)` (playing the role of `Ĥ`), `g ∈ N_G(V)`, `s = g t g⁻¹ ∈ V`.

**Proof.**  `1.10.i` (`LocalToolkit.d110i`) applies to a D-group `X`, an involution `t_X ∈ X` and
a `p`-subgroup `R ≤ X` normalised by `C_X(t_X)` and gives `⁅R, t_X⁆ ≤ O_p(X)`.  We apply it in
the D-group `X := M^g`, with the involution `t` *conjugated into* `M^g`:

* `g⁻¹ t g ∈ V ≤ S ≤ H ≤ N_G(P) ≤ M` because `g ∈ N_G(V)` and `t ∈ V`; hence `t ∈ M^g`
  (`conjSub`-membership), so `t` is an involution of `M^g` (its order is still `2`).
* Let `R := P ⊓ M^g` (a `p`-subgroup of `M^g`).  If `x ∈ M^g` commutes with `t`, then
  `x ∈ C_G(t) = H ≤ N_G(P)`, and `x ∈ M^g`; so conjugation by `x` preserves both `P` and `M^g`,
  i.e. it preserves `R = P ⊓ M^g`.  Hence `C_{M^g}(t) ≤ N_{M^g}(R)`.
* `1.10.i` therefore gives `⁅R, ⟨t⟩⁆ ≤ O_p(M^g)`.
* Finally `C_G(s) = C_G(t^g) = C_G(t)^g = H^g ≤ M^g` (conjugating `x ∈ C_G(s)`, one gets
  `g⁻¹ x g ∈ C_G(t) = H ≤ M`), so `P ⊓ C_G(s) ≤ R`, and by monotonicity of the commutator

  `⁅⟨t⟩, P ⊓ C_G(s)⁆ ≤ ⁅⟨t⟩, R⁆ = ⁅R, ⟨t⟩⁆ ≤ O_p(M^g)`.

Note that — as in the source — only `1.10.i` and the conjugation data are used here; the
minimality hypotheses `hmin`, `hnot` of `P` and the "`C_P(s) ≰ C_P(t)`" hypothesis `hbig`
enter only in the *other* half of Bender's sentence (`P ≤ O_p(Ĥ)`, see
`Work.CORE2A.bender26c_stepB_fixed`) and in the subsequent step `P₁` centralizes `P^g`.
-/

namespace Work.CORE2A

open Subgroup
open Work.GW2

theorem bender26c_stepP1 (T : Work.GW2.LocalToolkit) (hFT : Work.GW2.FeitThompsonProp)
    (G : Type) [Group G] [Finite G] (hctx : Work.GW2.BenderCtx G) (B : Work.GW2.BenderSetup G)
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (P : Subgroup G) (hP : IsPGroup p P)
    (hHN : B.H ≤ Subgroup.normalizer (P : Set G))
    (hmin : ∀ Q : Subgroup G, Q < P → IsPGroup p Q → B.H ≤ Subgroup.normalizer (Q : Set G) → Q ≤ Subgroup.centralizer ({B.t} : Set G))
    (hnot : ¬ P ≤ Subgroup.centralizer ({B.t} : Set G))
    (M : Subgroup G) (hM : IsCoatom M) (hNPM : Subgroup.normalizer (P : Set G) ≤ M)
    (V : Subgroup G) (hV4 : Work.GW2.IsFourGroup V) (hVS : V ≤ (B.S : Subgroup G)) (htV : B.t ∈ V)
    (g : G) (hgN : g ∈ Subgroup.normalizer (V : Set G)) (hgM : g ∉ M)
    (s : G) (hs : s = g * B.t * g⁻¹) (hsV : s ∈ V)
    (hbig : ¬ (P ⊓ Subgroup.centralizer ({s} : Set G) ≤ P ⊓ Subgroup.centralizer ({B.t} : Set G))) :
    ⁅Subgroup.zpowers B.t, P ⊓ Subgroup.centralizer ({s} : Set G)⁆ ≤
      Work.GW2.pCoreIn p (Work.GW2.conjSub g M) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  -- `K` is the conjugate `M^g = Ĥ^g` of the coatom `M`
  set K : Subgroup G := Work.GW2.conjSub g M with hK
  have hKM : ∀ x : G, x ∈ K ↔ g⁻¹ * x * g ∈ M := by
    intro x; rw [hK, Work.CORE2A.mem_conjSub_iff]
  -- `t ∈ M^g`: `g⁻¹ t g ∈ V ≤ S ≤ H ≤ N_G(P) ≤ M` (here `g ∈ N_G(V)`, `t ∈ V`)
  have htK : B.t ∈ K := by
    rw [hKM]
    have hg' : g⁻¹ ∈ Subgroup.normalizer (V : Set G) := Subgroup.inv_mem _ hgN
    have hV : g⁻¹ * B.t * g⁻¹⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hg' B.t).mp htV
    have hM' : g⁻¹ * B.t * g⁻¹⁻¹ ∈ M := hNPM (hHN (Work.CORE2A.bSetup_S_le_H B (hVS hV)))
    simpa using hM'
  -- `C_G(s) ≤ M^g`, since `C_G(s) = C_G(t)^g = H^g` and `H ≤ M`
  have hCsK : Subgroup.centralizer ({s} : Set G) ≤ K := by
    intro x hx
    rw [hKM]
    have hxs : s * x = x * s := (Subgroup.mem_centralizer_iff.mp hx) s (by simp)
    have hxs' : x * s * x⁻¹ = s := by rw [← hxs]; group
    have h2 : g⁻¹ * s * g = B.t := by rw [hs]; group
    have key : g⁻¹ * x * g * B.t * (g⁻¹ * x * g)⁻¹ = B.t := by
      calc g⁻¹ * x * g * B.t * (g⁻¹ * x * g)⁻¹
          = g⁻¹ * (x * (g * B.t * g⁻¹) * x⁻¹) * g := by group
        _ = g⁻¹ * (x * s * x⁻¹) * g := by rw [← hs]
        _ = g⁻¹ * s * g := by rw [hxs']
        _ = B.t := h2
    have hct : g⁻¹ * x * g ∈ Subgroup.centralizer ({B.t} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc (g⁻¹ * x * g) * B.t
          = (g⁻¹ * x * g * B.t * (g⁻¹ * x * g)⁻¹) * (g⁻¹ * x * g) := by group
        _ = B.t * (g⁻¹ * x * g) := by rw [key]
    exact hNPM (hHN hct)
  -- `R := P ⊓ M^g` is a `p`-subgroup of `M^g`
  have hP' : IsPGroup p ((P ⊓ K).subgroupOf K) :=
    (hP.to_le inf_le_left).of_equiv (Subgroup.subgroupOfEquivOfLe (inf_le_right : P ⊓ K ≤ K)).symm
  -- `t`, viewed as an element of `M^g`, is an involution
  set t' : ↥K := ⟨B.t, htK⟩ with ht'def
  have ht'2 : orderOf t' = 2 := by
    rw [ht'def, Subgroup.orderOf_mk]
    exact B.t_order
  -- `C_{M^g}(t) ≤ N_{M^g}(P ⊓ M^g)`: an element of `M^g` centralizing `t` lies in
  -- `C_G(t) = H ≤ N_G(P)`, and it lies in `M^g`, hence preserves `P ⊓ M^g`
  have hcen : Subgroup.centralizer ({t'} : Set ↥K) ≤
      Subgroup.normalizer ((P ⊓ K).subgroupOf K : Set ↥K) := by
    intro x hx
    have hxct : (x : G) ∈ Subgroup.centralizer ({B.t} : Set G) := by
      have h1 : t' * x = x * t' := (Subgroup.mem_centralizer_iff.mp hx) t' (by simp)
      have h3 := congrArg (Subtype.val) h1
      simp only [ht'def, Subgroup.coe_mul] at h3
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact h3.symm
    have hxN : (x : G) ∈ Subgroup.normalizer (P : Set G) := hHN hxct
    rw [Subgroup.mem_normalizer_iff] at hxN ⊢
    intro y
    constructor
    · intro hy
      rw [Subgroup.mem_subgroupOf] at hy
      rw [Subgroup.mem_subgroupOf]
      refine ⟨?_, ?_⟩
      · exact (hxN (y : G)).mp hy.1
      · change (x : G) * (y : G) * (x : G)⁻¹ ∈ K
        exact K.mul_mem (K.mul_mem x.2 hy.2) (K.inv_mem x.2)
    · intro hy
      rw [Subgroup.mem_subgroupOf] at hy
      rw [Subgroup.mem_subgroupOf]
      refine ⟨?_, ?_⟩
      · exact (hxN (y : G)).mpr hy.1
      · change (y : G) ∈ K
        have h5 : (x : G)⁻¹ * ((x : G) * (y : G) * (x : G)⁻¹) * (x : G) = (y : G) := by group
        rw [← h5]
        exact K.mul_mem (K.mul_mem (K.inv_mem x.2) hy.2) x.2
  -- `M^g` is a proper subgroup of `G`, hence a D-group
  have hD : Work.GW2.DihOrCycSylow ↥K := Work.CORE2A.dihOrCycSylow_subgroup hctx.sylow K
  have hKne : K ≠ ⊤ := by
    intro htop
    have h2 : Work.GW2.conjSub g⁻¹ (Work.GW2.conjSub g M) = ⊤ := by
      rw [← hK, htop, Work.CORE2A.conjSub_top]
    have hMt : M = ⊤ := by rwa [Work.CORE2A.conjSub_inv_conjSub g M] at h2
    exact hM.ne_top hMt
  have hlt : Nat.card ↥K < Nat.card G := Work.CORE2A.card_lt_card_of_ne_top hKne
  have hDG : IsDGroup ↥K := hctx.ih ↥K hlt hD
  -- Bender 1.10.i in `M^g`: `⁅P ⊓ M^g, ⟨t⟩⁆ ≤ O_p(M^g)`
  have hkey := T.d110i ↥K hFT hD hDG t' ht'2 p hp2 ((P ⊓ K).subgroupOf K) hP' hcen
  have hmap := Subgroup.map_mono (f := K.subtype) hkey
  rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le (inf_le_right : P ⊓ K ≤ K),
      MonoidHom.map_zpowers] at hmap
  -- `⁅⟨t⟩, P ⊓ C_G(s)⁆ ≤ ⁅⟨t⟩, P ⊓ M^g⁆ = ⁅P ⊓ M^g, ⟨t⟩⁆ ≤ O_p(M^g)`
  rw [Subgroup.commutator_comm (Subgroup.zpowers B.t) (P ⊓ Subgroup.centralizer ({s} : Set G))]
  refine le_trans (Subgroup.commutator_mono (inf_le_inf_left P hCsK) le_rfl) ?_
  simpa [Work.GW2.pCoreIn, hK] using hmap

end Work.CORE2A
