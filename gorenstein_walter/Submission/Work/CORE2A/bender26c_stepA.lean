import Mathlib
import Submission.Work.CORE2A.Defs
import Submission.Work.CORE2A.Basic
import Submission.Work.CORE2A.bender26c_key
import Submission.Work.CORE3.RelIndexCentralizerFourGroup

/-!
# CORE2A: Bender 1981, Theorem 2.6, step 3 — the conjugating involution outside `M`

Target: `Work.CORE2A.bender26c_stepA`, the "step A" of the construction of
`Work.CORE2A.bender26c_key` (Bender 1981, p. 221, proof of Theorem 2.6, third paragraph).

The input is a maximal subgroup `M ⊇ H = C_G(t)` which does *not* have a single class of
involutions (`h2`), together with an `H`-invariant odd `p`-subgroup `P` (`p ≠ 2`) that `t` does
not centralize.  The conclusion produces

* a four-group `V ≤ S` with `t ∈ V` and `N_G(V) ⊄ M` (Bender's Lemma 2.1 / the `LocalToolkit`
  fusion hypothesis `fus`, already available as `Work.CORE2A.b26c_fourGroup`);
* an element `s ∈ V#`, `s ≠ t`, with `C_P(s) ≰ C_P(t)` (Bender 1.1(iii), available as
  `Work.CORE2A.b26c_fourGroup_element`);
* an element `g ∈ N_G(V) \ M` with `g t g⁻¹ = s` (the orbit-stabilizer count of
  `N_G(V)` on `V#`, proved here).

The third item is the content of the present file.  Since `V` is a four-group, `N_G(V)` acts on
the three involutions `V# = V ∖ {1}` by conjugation, and `fus` says this action is transitive;
orbit-stabilizer (`Work.CORE3.RelIndexCentralizerFourGroup`) gives
`[N_G(V) : N_G(V) ∩ C_G(t)] = 3`.  As `C_G(t) = H ≤ M`, the subgroup `N_G(V) ∩ M` contains
`N_G(V) ∩ C_G(t)` and is proper (because `N_G(V) ⊄ M`), so by primality of `3` it equals it.  Any
`g ∈ N_G(V)` with `g t g⁻¹ = s ≠ t` therefore cannot lie in `M`.

## Main declarations

* `b26c_normalizer_inf_eq_centralizer`: `N_G(V) ∩ M = N_G(V) ∩ C_G(t)`.
* `b26c_conj_notMem`: the conjugating element outside `M`.
* `bender26c_stepA`: the target.
-/

namespace Work.CORE2A

open Subgroup
open Work.GW2

/-- `t ≠ 1`, from `orderOf t = 2`. -/
theorem b26c_t_ne_one {G : Type} [Group G] [Finite G] (B : Work.GW2.BenderSetup G) :
    B.t ≠ 1 := by
  intro h
  have h2 := B.t_order
  rw [h, orderOf_one] at h2
  exact absurd h2 (by norm_num)

/-- **The index-3 squeeze.**  Let `V` be a four-group with `t ∈ V`, and let `M` be a subgroup with
`C_G(t) = B.H ≤ M` but `N_G(V) ⊄ M`.  Then `N_G(V) ∩ M = N_G(V) ∩ C_G(t)`.

`N_G(V)` acts on `V#` by conjugation, and the `LocalToolkit` fusion hypothesis `fus` makes this
action transitive (the Sylow hypotheses it needs come from `hctx`).  Hence
`[N_G(V) : N_G(V) ∩ C_G(t)] = 3` (`Work.CORE3.RelIndexCentralizerFourGroup`), and any proper
subgroup of `N_G(V)` containing `N_G(V) ∩ C_G(t)` must equal it. -/
theorem b26c_normalizer_inf_eq_centralizer {G : Type} [Group G] [Finite G]
    (T : Work.GW2.LocalToolkit) (hctx : Work.GW2.BenderCtx G) (B : Work.GW2.BenderSetup G)
    (V : Subgroup G) (hV4 : Work.GW2.IsFourGroup V) (htV : B.t ∈ V)
    (M : Subgroup G) (hHM : B.H ≤ M)
    (hnotle : ¬ Subgroup.normalizer (V : Set G) ≤ M) :
    Subgroup.normalizer (V : Set G) ⊓ M =
      Subgroup.normalizer (V : Set G) ⊓ Subgroup.centralizer ({B.t} : Set G) := by
  classical
  obtain ⟨n, hn2, hiso⟩ := b26c_exists_dihedral hctx B
  have hno12 := b26c_no_index_two hctx
  have htrans := (T.fus G B.S n hn2 hiso hno12).2
  -- orbit-stabilizer count: `[N_G(V) : N_G(V) ∩ C_G(t)] = 3`
  have hidx : (Subgroup.centralizer ({B.t} : Set G) ⊓ Subgroup.normalizer (V : Set G)).relIndex
      (Subgroup.normalizer (V : Set G)) = 3 :=
    Work.CORE3.RelIndexCentralizerFourGroup V (Subgroup.normalizer (V : Set G)) hV4
      le_rfl (htrans V hV4) htV (b26c_t_ne_one B)
  have hCm : Subgroup.centralizer ({B.t} : Set G) ≤ M := hHM
  have hCle : Subgroup.centralizer ({B.t} : Set G) ⊓ Subgroup.normalizer (V : Set G) ≤
      M ⊓ Subgroup.normalizer (V : Set G) := inf_le_inf_right _ hCm
  have hprod : (Subgroup.centralizer ({B.t} : Set G) ⊓ Subgroup.normalizer (V : Set G)).relIndex
        (M ⊓ Subgroup.normalizer (V : Set G)) *
      (M ⊓ Subgroup.normalizer (V : Set G)).relIndex (Subgroup.normalizer (V : Set G)) = 3 := by
    rw [Subgroup.relIndex_mul_relIndex _ _ _ hCle inf_le_right, hidx]
  have hne1 : (M ⊓ Subgroup.normalizer (V : Set G)).relIndex
      (Subgroup.normalizer (V : Set G)) ≠ 1 := by
    intro h
    exact hnotle (le_trans (Subgroup.relIndex_eq_one.mp h) inf_le_left)
  have hdvd : (M ⊓ Subgroup.normalizer (V : Set G)).relIndex
      (Subgroup.normalizer (V : Set G)) ∣ 3 :=
    ⟨_, by rw [← hprod, mul_comm]⟩
  have h3 : (M ⊓ Subgroup.normalizer (V : Set G)).relIndex
      (Subgroup.normalizer (V : Set G)) = 3 :=
    (Nat.Prime.eq_one_or_self_of_dvd Nat.prime_three _ hdvd).resolve_left hne1
  have hone : (Subgroup.centralizer ({B.t} : Set G) ⊓ Subgroup.normalizer (V : Set G)).relIndex
      (M ⊓ Subgroup.normalizer (V : Set G)) = 1 := by
    have := hprod
    rw [h3] at this
    omega
  have heq : Subgroup.centralizer ({B.t} : Set G) ⊓ Subgroup.normalizer (V : Set G) =
      M ⊓ Subgroup.normalizer (V : Set G) :=
    le_antisymm hCle (Subgroup.relIndex_eq_one.mp hone)
  rw [inf_comm (Subgroup.normalizer (V : Set G)) M,
    inf_comm (Subgroup.normalizer (V : Set G)) (Subgroup.centralizer ({B.t} : Set G))]
  exact heq.symm

/-- **The conjugating element outside `M`.**  If `V` is a four-group with `t ∈ V`, `M ⊇ C_G(t)`
is a subgroup with `N_G(V) ⊄ M`, and `s ∈ V`, `s ≠ 1`, `s ≠ t`, then there is `g ∈ N_G(V) \ M`
with `g t g⁻¹ = s`.

Transitivity of `N_G(V)` on `V#` (`fus`) supplies some `g ∈ N_G(V)` with `g t g⁻¹ = s`; if that
`g` lay in `M`, then `g ∈ N_G(V) ∩ M = N_G(V) ∩ C_G(t)`, so `g t g⁻¹ = t ≠ s`. -/
theorem b26c_conj_notMem {G : Type} [Group G] [Finite G] (T : Work.GW2.LocalToolkit)
    (hctx : Work.GW2.BenderCtx G) (B : Work.GW2.BenderSetup G)
    (V : Subgroup G) (hV4 : Work.GW2.IsFourGroup V) (htV : B.t ∈ V)
    (M : Subgroup G) (hHM : B.H ≤ M) (hnotle : ¬ Subgroup.normalizer (V : Set G) ≤ M)
    (s : G) (hsV : s ∈ V) (hs1 : s ≠ 1) (hst : s ≠ B.t) :
    ∃ g ∈ Subgroup.normalizer (V : Set G), g ∉ M ∧ g * B.t * g⁻¹ = s := by
  classical
  obtain ⟨n, hn2, hiso⟩ := b26c_exists_dihedral hctx B
  have hno12 := b26c_no_index_two hctx
  have htrans := (T.fus G B.S n hn2 hiso hno12).2
  obtain ⟨g, hgN, hgconj⟩ :=
    htrans V hV4 B.t htV s hsV (b26c_t_ne_one B) hs1
  refine ⟨g, hgN, ?_, hgconj⟩
  intro hgM
  have heq := b26c_normalizer_inf_eq_centralizer T hctx B V hV4 htV M hHM hnotle
  have hmem : g ∈ Subgroup.normalizer (V : Set G) ⊓ M := ⟨hgN, hgM⟩
  rw [heq] at hmem
  have hct : g * B.t * g⁻¹ = B.t := by
    have h2 : g * B.t = B.t * g := Subgroup.mem_centralizer_singleton_iff.mp hmem.2
    rw [h2]
    group
  rw [hct] at hgconj
  exact hst hgconj.symm

theorem bender26c_stepA (T : Work.GW2.LocalToolkit) (hFT : Work.GW2.FeitThompsonProp)
    (G : Type) [Group G] [Finite G] (hctx : Work.GW2.BenderCtx G) (B : Work.GW2.BenderSetup G)
    (M : Subgroup G) (hM : IsCoatom M) (hHM : B.H ≤ M) (h2 : ¬ Work.GW2.OneInvClassIn M)
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (P : Subgroup G) (hP : IsPGroup p P)
    (hHN : B.H ≤ Subgroup.normalizer (P : Set G))
    (hnot : ¬ P ≤ Subgroup.centralizer ({B.t} : Set G)) :
    ∃ (V : Subgroup G) (s g : G),
      B.t ∈ V ∧ V ≤ (B.S : Subgroup G) ∧ Work.GW2.IsFourGroup V ∧
      ¬ Subgroup.normalizer (V : Set G) ≤ M ∧ s ∈ V ∧ s ≠ 1 ∧ s ≠ B.t ∧
      (¬ (P ⊓ Subgroup.centralizer ({s} : Set G) ≤ P ⊓ Subgroup.centralizer ({B.t} : Set G))) ∧
      g ∈ Subgroup.normalizer (V : Set G) ∧ g ∉ M ∧ g * B.t * g⁻¹ = s := by
  classical
  obtain ⟨V, htV, hVS, hV4, hnotle⟩ := b26c_fourGroup T hFT hctx B M hM hHM h2
  obtain ⟨s, hsV, hs1, hst, hcent⟩ :=
    b26c_fourGroup_element T B p hp hp2 P hP hHN V hV4 hVS htV hnot
  obtain ⟨g, hgN, hgM, hgconj⟩ :=
    b26c_conj_notMem T hctx B V hV4 htV M hHM hnotle s hsV hs1 hst
  exact ⟨V, s, g, htV, hVS, hV4, hnotle, hsV, hs1, hst, hcent, hgN, hgM, hgconj⟩

end Work.CORE2A
