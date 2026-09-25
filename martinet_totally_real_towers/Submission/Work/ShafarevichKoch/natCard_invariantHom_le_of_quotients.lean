import Mathlib

/-!
# `Work.ShafarevichKoch.natCard_invariantHom_le_of_quotients`

The **invariant** analogue of `Work.ShafarevichKoch.natCard_contHom_le_of_quotients`: a uniform
bound on the `G`-invariant characters of the finite quotients `N ⧸ (N ⊓ U)` (by open normal
subgroups `U ⊴ G`) upgrades to the same bound on the `G`-invariant *continuous* characters of the
profinite group `N`.

This is the transgression / `H¹`-invariants half of the pro-finite passage of the
Shafarevich--Koch counting route (`README.md` §17.3(C)): the finite-level count
`Work.ShafarevichKoch.card_relFrattiniQuotient_fixingSubgroup_le` bounds the invariant characters
of each finite level, and this lemma passes to the limit `H_S = Gal(k_S/k_∅)`.

The finiteness clause in the hypothesis is automatic in the intended application (for open `U`,
`N ⧸ (N ⊓ U)` is finite, so the set of invariant characters of the quotient is finite); it is
spelled out because `Nat.card` of an infinite type is `0`.

The proof is the elementary one: a continuous character has open kernel in `N`, hence vanishes on
`N ⊓ U` for some open normal `U ⊴ G` (profiniteness); in the finite case the (finitely many)
kernels give one subgroup `U₀ := ⨅ U_φ` on which *every* character in the conclusion set vanishes,
so the conclusion set is contained in the hypothesis set for `U₀`; in the infinite case `Nat.card`
is `0`.
-/

set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open scoped Classical

noncomputable section

namespace Work.ShafarevichKoch

theorem natCard_invariantHom_le_of_quotients {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]
    (N : Subgroup G) [hN : N.Normal] (s : ℕ)
    (h : ∀ (U : Subgroup G) [U.Normal], IsOpen (U : Set G) →
      Finite {φ : N →* Multiplicative (ZMod 2) //
        (∀ (g : G) (n : N),
          φ ⟨g * (n : G) * g⁻¹, Subgroup.Normal.conj_mem hN (n : G) n.2 g⟩ = φ n) ∧
        (∀ n : N, (n : G) ∈ U → φ n = 1)} ∧
      Nat.card {φ : N →* Multiplicative (ZMod 2) //
        (∀ (g : G) (n : N),
          φ ⟨g * (n : G) * g⁻¹, Subgroup.Normal.conj_mem hN (n : G) n.2 g⟩ = φ n) ∧
        (∀ n : N, (n : G) ∈ U → φ n = 1)} ≤ 2 ^ s) :
    Nat.card {φ : N →* Multiplicative (ZMod 2) //
      Continuous (φ : N → Multiplicative (ZMod 2)) ∧
      ∀ (g : G) (n : N),
        φ ⟨g * (n : G) * g⁻¹, Subgroup.Normal.conj_mem hN (n : G) n.2 g⟩ = φ n} ≤ 2 ^ s := by
  classical
  set H : Set (N →* Multiplicative (ZMod 2)) :=
    {φ | Continuous (φ : N → Multiplicative (ZMod 2)) ∧
      ∀ (g : G) (n : N),
        φ ⟨g * (n : G) * g⁻¹, Subgroup.Normal.conj_mem hN (n : G) n.2 g⟩ = φ n} with hH
  change Nat.card ↥H ≤ 2 ^ s
  by_cases hfin : H.Finite
  · haveI : Finite ↥H := hfin.to_subtype
    -- for each character, an open normal `U` on whose `N`-part it vanishes
    have hex : ∀ φ : ↥H, ∃ U : OpenNormalSubgroup G, ∀ n : N, (n : G) ∈ (U : Set G) → φ.1 n = 1 := by
      intro φ
      have hker : IsOpen ((φ.1.ker : Subgroup N) : Set N) :=
        φ.2.1.isOpen_preimage ({1} : Set (Multiplicative (ZMod 2))) (isOpen_discrete _)
      obtain ⟨V, hVo, hV⟩ := isOpen_induced_iff.mp hker
      have h1V : (1 : G) ∈ V := by
        have : (1 : N) ∈ (Subtype.val : N → G) ⁻¹' V := by rw [hV]; exact φ.1.ker.one_mem
        simpa using this
      obtain ⟨U, hU⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hVo h1V
      refine ⟨U, fun n hn => ?_⟩
      have : n ∈ (Subtype.val : N → G) ⁻¹' V := hU hn
      rw [hV] at this
      exact MonoidHom.mem_ker.mp this
    choose U hU using hex
    let U₀ : Subgroup G := ⨅ φ : ↥H, (U φ).toSubgroup
    have hU₀open : IsOpen (U₀ : Set G) := by
      rw [show U₀ = ⨅ φ : ↥H, (U φ).toSubgroup from rfl, Subgroup.coe_iInf]
      exact isOpen_iInter_of_finite fun φ => (U φ).isOpen'
    haveI : U₀.Normal := Subgroup.normal_iInf_normal fun φ => inferInstance
    have hsub : ∀ φ : ↥H, ∀ n : N, (n : G) ∈ U₀ → φ.1 n = 1 := by
      intro φ n hn
      exact hU φ n (iInf_le (fun ψ : ↥H => (U ψ).toSubgroup) φ hn)
    have hsub' : H ⊆ {φ : N →* Multiplicative (ZMod 2) |
        (∀ (g : G) (n : N),
          φ ⟨g * (n : G) * g⁻¹, Subgroup.Normal.conj_mem hN (n : G) n.2 g⟩ = φ n) ∧
        (∀ n : N, (n : G) ∈ U₀ → φ n = 1)} := fun φ hφ => ⟨hφ.2, hsub ⟨φ, hφ⟩⟩
    have hfinS : ({φ : N →* Multiplicative (ZMod 2) |
        (∀ (g : G) (n : N),
          φ ⟨g * (n : G) * g⁻¹, Subgroup.Normal.conj_mem hN (n : G) n.2 g⟩ = φ n) ∧
        (∀ n : N, (n : G) ∈ U₀ → φ n = 1)} : Set (N →* Multiplicative (ZMod 2))).Finite :=
      (h U₀ hU₀open).1
    calc Nat.card ↥H ≤ H.ncard := le_of_eq rfl
      _ ≤ ({φ : N →* Multiplicative (ZMod 2) |
            (∀ (g : G) (n : N),
              φ ⟨g * (n : G) * g⁻¹, Subgroup.Normal.conj_mem hN (n : G) n.2 g⟩ = φ n) ∧
            (∀ n : N, (n : G) ∈ U₀ → φ n = 1)} : Set (N →* Multiplicative (ZMod 2))).ncard :=
          Set.ncard_le_ncard hsub' hfinS
      _ ≤ 2 ^ s := (h U₀ hU₀open).2
  · haveI : Infinite ↥H := Set.infinite_coe_iff.mpr hfin
    rw [Nat.card_eq_zero_of_infinite]
    exact Nat.zero_le _

end Work.ShafarevichKoch
