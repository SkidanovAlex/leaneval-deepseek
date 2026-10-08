/-
Area A10 of the Feit--Thompson (odd order theorem) drive:
the modular representation theory layer over `F_p = ZMod p`.

Contents:
* the kernel `repKernel ρ` of a representation (a normal subgroup of `G`), and its relation to
  faithfulness;
* a normal `p`-subgroup acts trivially on an irreducible module in characteristic `p`
  (`pCore_le_ker_of_isIrreducible`), hence `O_p(G) = 1` for faithful irreducible modules;
* the fixed space `fixedBy ρ P` of a subgroup, with its `G`-invariance when `P` is normal;
* functoriality of unipotency.

The external ingredients used here are
`Work.HallHigman.exists_ne_zero_fixed_of_isPGroup` (a `p`-group acting on a nontrivial finite
`F_p`-module has a nonzero fixed vector), `Work.HallHigman.map_invariants_le_of_normal`
(fixed points of a normal subgroup are `G`-stable) and `Work.HallHigman.piCore_isPiNat`
(`O_p(G)` is a `p`-group).
-/
import Mathlib
import Submission.Work.HallHigman.Basic
import Submission.Work.HallHigman.piCore_isPiNat
import Submission.Work.HallHigman.exists_ne_zero_fixed_of_isPGroup
import Submission.Work.HallHigman.map_invariants_le_of_normal

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

universe u v

namespace Work.HallHigman

open Polynomial

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

variable {p : ℕ} [Fact p.Prime] {G V : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod p) V]

/-! ### The kernel of a representation -/

/-- The subgroup of `G` acting trivially on `V` (the kernel of a representation). -/
abbrev repKernel (ρ : Representation (ZMod p) G V) : Subgroup G := ρ.ker

lemma repKernel_eq_bot_iff (ρ : Representation (ZMod p) G V) :
    repKernel ρ = ⊥ ↔ Function.Injective ρ :=
  MonoidHom.ker_eq_bot_iff ρ

lemma mem_repKernel_iff (ρ : Representation (ZMod p) G V) (g : G) :
    g ∈ repKernel ρ ↔ ∀ v : V, ρ g v = v := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro h v
    rw [LinearMap.congr_fun h v]
    rfl
  · intro h
    exact LinearMap.ext h

lemma repKernel_normal (ρ : Representation (ZMod p) G V) : (repKernel ρ).Normal :=
  MonoidHom.normal_ker ρ

/-! ### The fixed space of a subgroup -/

/-- The subspace of vectors fixed by a subgroup. -/
noncomputable def fixedBy (ρ : Representation (ZMod p) G V) (P : Subgroup G) : Submodule (ZMod p) V :=
  Representation.invariants (ρ.comp P.subtype)

lemma mem_fixedBy_iff (ρ : Representation (ZMod p) G V) (P : Subgroup G) (v : V) :
    v ∈ fixedBy ρ P ↔ ∀ g ∈ P, ρ g v = v := by
  rw [fixedBy, Representation.mem_invariants]
  exact ⟨fun h g hg => h ⟨g, hg⟩, fun h g => h g g.2⟩

/-- `O_p(G)` is a `p`-group. -/
lemma isPGroup_pCore : IsPGroup p ↥(pCore p G) := by
  have hp0 : p ≠ 0 := Nat.Prime.ne_zero Fact.out
  have hpprime : Nat.Prime p := Fact.out
  refine (isPGroup_iff_primeFactors_card_subset hp0).mpr ?_
  intro q hq
  obtain ⟨hqp, hqd, -⟩ := Nat.mem_primeFactors.mp hq
  have hqe : q = p := piCore_isPiNat (π := (· = p)) (G := G) q hqp hqd
  subst hqe
  exact Nat.mem_primeFactors.mpr ⟨hpprime, dvd_rfl, hp0⟩

/-! ### Normal `p`-subgroups act trivially on irreducible modules -/

/-- **A normal `p`-subgroup acts trivially on an irreducible representation in characteristic `p`.**
Its fixed space is a nonzero (fixed point lemma) `G`-invariant subspace, hence all of `V`. -/
theorem pCore_le_ker_of_isIrreducible (ρ : Representation (ZMod p) G V) [Finite V]
    [ρ.IsIrreducible] : pCore p G ≤ repKernel ρ := by
  intro g hg
  rw [mem_repKernel_iff]
  intro v
  by_cases hV : Nontrivial V
  · -- the fixed space of `O_p(G)` is a nonzero `G`-invariant subspace
    have hstable : ∀ h : G, (fixedBy ρ (pCore p G)).map (ρ h) ≤ fixedBy ρ (pCore p G) :=
      fun h => map_invariants_le_of_normal ρ (pCore p G) h
    let W : Subrepresentation ρ :=
      { toSubmodule := fixedBy ρ (pCore p G)
        apply_mem_toSubmodule := fun h w hw =>
          hstable h (Submodule.mem_map_of_mem hw) }
    have hWne : W ≠ ⊥ := by
      intro hbot
      obtain ⟨w, hw, hfix⟩ := exists_ne_zero_fixed_of_isPGroup ρ isPGroup_pCore hV
      have hwW : w ∈ W := (mem_fixedBy_iff ρ (pCore p G) w).mpr hfix
      have hbot' : W.toSubmodule = ⊥ := by
        have := congrArg Subrepresentation.toSubmodule hbot
        rwa [show (⊥ : Subrepresentation ρ).toSubmodule = ⊥ from rfl] at this
      have hmem : w ∈ (⊥ : Submodule (ZMod p) V) := hbot' ▸ hwW
      exact hw (by simpa using hmem)
    have hWtop : W = ⊤ := (IsSimpleOrder.eq_bot_or_eq_top W).resolve_left hWne
    have hv : v ∈ W := by rw [hWtop]; trivial
    exact (mem_fixedBy_iff ρ (pCore p G) v).mp hv g hg
  · haveI : Subsingleton V := not_nontrivial_iff_subsingleton.mp hV
    exact Subsingleton.elim _ _

/-- A normal `p`-subgroup is contained in `O_p(G)`. -/
theorem le_pCore_of_isPGroup {N : Subgroup G} (hN : N.Normal) (hPg : IsPGroup p N) :
    N ≤ pCore p G := by
  have hpi : IsPiNat (· = p) (Nat.card N) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hPg
    intro q hq hqd
    rw [hn] at hqd
    exact (Nat.prime_dvd_prime_iff_eq hq Fact.out).mp (hq.dvd_of_dvd_pow hqd)
  exact le_pCore hN hpi

/-- The same statement for an arbitrary normal `p`-subgroup (not necessarily the largest one). -/
theorem normal_isPGroup_le_ker_of_isIrreducible (ρ : Representation (ZMod p) G V) [Finite V]
    [ρ.IsIrreducible] {N : Subgroup G} (hN : N.Normal) (hPg : IsPGroup p N) :
    N ≤ repKernel ρ :=
  le_trans (le_pCore_of_isPGroup hN hPg) (pCore_le_ker_of_isIrreducible ρ)

/-- **A faithful irreducible `F_p[G]`-module forces `O_p(G) = 1`.** -/
theorem pCore_eq_bot_of_isIrreducible (ρ : Representation (ZMod p) G V) [Finite V]
    [ρ.IsIrreducible] (h : Function.Injective ρ) : pCore p G = ⊥ := by
  have hsub : pCore p G ≤ repKernel ρ := pCore_le_ker_of_isIrreducible ρ
  have hker : repKernel ρ = ⊥ := (repKernel_eq_bot_iff ρ).mpr h
  rw [eq_bot_iff]
  intro g hg
  rw [Subgroup.mem_bot]
  have hmem : g ∈ repKernel ρ := hsub hg
  rw [hker] at hmem
  simpa using hmem

end Work.HallHigman
