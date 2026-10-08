import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.API
import Submission.Work.CORE4.LayerCtx6
import Submission.Work.CORE4.Case2CountSetup
import Submission.Work.CORE4.Case2Setup9Ecent

open scoped MatrixGroups

namespace Work.CORE4

open Subgroup

/-- **The order-parity step.**  In a finite group `H` whose centre has odd order, an element `e`
whose `m`-th power is central for an odd `m` has odd order.

Indeed `e ^ m ∈ Z(H)` and `|Z(H)|` is odd, so `(e ^ m) ^ |Z(H)| = 1`, i.e. `e ^ (m * |Z(H)|) = 1`;
since `m * |Z(H)|` is odd, `orderOf e` divides an odd number. -/
theorem odd_orderOf_of_pow_mem_center {H : Type} [Group H] [Finite H]
    (hZ : Odd (Nat.card (Subgroup.center H))) (e : H) (m : ℕ) (hm : Odd m)
    (he : e ^ m ∈ Subgroup.center H) : Odd (orderOf e) := by
  have hpow : (e ^ m) ^ (Nat.card (Subgroup.center H)) = 1 := by
    have h1 : (⟨e ^ m, he⟩ : ↥(Subgroup.center H)) ^ (Nat.card (Subgroup.center H)) = 1 :=
      pow_card_eq_one'
    exact congrArg (fun w : ↥(Subgroup.center H) => (w : H)) h1
  have hdvd : orderOf e ∣ m * Nat.card (Subgroup.center H) := by
    rw [orderOf_dvd_iff_pow_eq_one, pow_mul]
    exact hpow
  exact Odd.of_dvd_nat (hm.mul hZ) hdvd

/-- The structure fact behind Bender 1981 §4 (4) (`F` centralises `E(M)`), in the form the §4 (5)
argument consumes it.  (Easier variant of `Submission/Work/CORE4/Case2Setup9Ecent.lean`: the
hypothesis `Odd (orderOf e)` there implies this one, since `e^m ∈ C(E)` with `m` odd forces
`e^{m·|Z(E)|} = 1` and `|Z(E)|` is odd.)

Configuration: `BenderCtx G`, `B : BenderSetup G`, `M : Subgroup G` a coatom with `t = B.t ∈ E := layerIn M`,
and `P ≤ M ⊓ C_G(t)` a Sylow 2-subgroup of `M` (so `P ⊓ E ∈ Syl₂(E)`, because `E ⊴ M`).

Conclusion: if `e ∈ E`, `e^m` centralizes `E` for some *odd* `m` (equivalently: the image of `e` in
`E/Z(E)` has odd order), and `e` centralizes the Sylow `P ⊓ E` of `E`, then `e` centralizes `E`
(i.e. `e ∈ Z(E)`).

Proof route.  `E` is quasisimple with `Odd |Z(E)|` and `E/Z(E) ≅ A₇` or `≅ PSL(2,q)`
(`Work.CORE4.LayerCtx6`; as its readers noted, its proof body only uses `M ≠ ⊤`, `t ∈ layerIn M`,
`hbc.ih` and `Work.CORE4.DihOrCycSub hbc.sylow M`, so copy it, or `I.toolkit.lay` directly with
`E' := layer ↥M`), and `Z := Z(E)` has odd order.

* `P ⊓ E ∈ Syl₂(E)`: `E ⊴ M`, `P` is Sylow in `M`.
* `e ∈ C_E(P ⊓ E)` and `e^m ∈ Z` for odd `m` ⇒ `eZ ∈ C_{E/Z}((P⊓E)Z/Z)` has *odd* order
  (`(eZ)^m = 1`), and `(P⊓E)Z/Z ∈ Syl₂(E/Z)` because `|Z|` is odd.
* Structure of the simple quotient: the odd part of `C_{\bar E}(S̄)` is trivial —
  * `PSL(2,q)`: `I.toolkit.l2syl` gives `S ≅ D_n` (`n ≥ 2`), `S` contains the four-group `V`
    (`Ω₁(S)`), and `I.toolkit.l2four` gives `C(V) = V`, so `C_{\bar E}(S) ≤ C(V) = V` is a 2-group;
  * `A₇`: `C_{A₇}(D₈) = Z(D₈)`, a 2-group, in the workspace as
    `Work.AUTA7.A7.SylowFacts` (`Submission/Work/AUTA7/A7/SylowFacts.lean`, no `sorry`); the weaker
    `N_{A₇}(D) = D` there already gives `C(D) ≤ D`.
* A 2-group has no element of odd order `> 1`, so `eZ = 1`, i.e. `e ∈ Z(E) ≤ C_G(E)`.

Implementation.  The group-theoretic content above is available in the workspace as
`Work.CORE4.Case2Setup9Ecent` (whose hypothesis is `Odd (orderOf e)`) on top of the
`A₇`/`L₂(q)` model facts `Work.CORE4.Ecent.alt7_odd_centralizer_sylow` and
`Work.CORE4.Ecent.psl_odd_centralizer_sylow`; the only step needed here is the parity step
`odd_orderOf_of_pow_mem_center`, which converts the hypothesis of this lemma into that of
`Case2Setup9Ecent`.  (`|Z(E)|` is odd by `layer_facts_coatom`, i.e. Bender 1.6 via `I.toolkit.lay`.) -/
theorem Case2Setup9Ecent2 (I : Work.GW2.C4Inputs) :
    ∀ (G : Type) [Group G] [Finite G], Work.GW2.BenderCtx G →
      ∀ (B : Work.GW2.BenderSetup G) (M P : Subgroup G),
        IsCoatom M → B.t ∈ Work.GW2.layerIn M →
        IsPGroup 2 P → P ≤ M ⊓ B.H → ¬ 2 ∣ P.relIndex M →
        ∀ e ∈ Work.GW2.layerIn M,
          (∃ m : ℕ, Odd m ∧
            e ^ m ∈ Subgroup.centralizer ((Work.GW2.layerIn M : Subgroup G) : Set G)) →
          e ∈ Subgroup.centralizer (((P ⊓ Work.GW2.layerIn M : Subgroup G)) : Set G) →
          e ∈ Subgroup.centralizer ((Work.GW2.layerIn M : Subgroup G) : Set G) := by
  intro G _ _ hbc B M P hcoat ht hPp hPle hPidx e heE hexp hecen
  -- The layer of the coatom: `layer ↥M = E1`, normal quasisimple with odd centre.
  obtain ⟨E1, _hE1norm, hlayer, hZodd, _hshape⟩ := layer_facts_coatom I hbc hcoat ht
  have hlayerIn_eq : Work.GW2.layerIn M = E1.map (Subgroup.subtype M) := by
    rw [Work.GW2.layerIn, hlayer]
  -- The centre of `↥(layerIn M)` has odd order (transported along `E1 ≃* E1.map M.subtype`).
  have hZodd' : Odd (Nat.card (Subgroup.center ↥(Work.GW2.layerIn M))) := by
    rw [hlayerIn_eq]
    have eiso : ↥E1 ≃* ↥(E1.map (Subgroup.subtype M)) :=
      Subgroup.equivMapOfInjective E1 (Subgroup.subtype M) (Subgroup.subtype_injective M)
    rw [← map_center_mulEquiv eiso, Subgroup.card_map_of_injective eiso.injective]
    exact hZodd
  -- `e` as an element of the layer, and the image of `e^m` is central there.
  set xe : ↥(Work.GW2.layerIn M) := ⟨e, heE⟩ with hxedef
  obtain ⟨m, hmodd, hmem⟩ := hexp
  have hxem_center : xe ^ m ∈ Subgroup.center ↥(Work.GW2.layerIn M) := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    show ((g : G) * e ^ m : G) = (e ^ m * (g : G) : G)
    exact Subgroup.mem_centralizer_iff.mp hmem (g : G) g.2
  -- parity step: `e` has odd order.
  have hxeodd : Odd (orderOf xe) := odd_orderOf_of_pow_mem_center hZodd' xe m hmodd hxem_center
  have hxeord : orderOf xe = orderOf e := by
    rw [hxedef]
    exact (Subgroup.orderOf_coe (⟨e, heE⟩ : ↥(Work.GW2.layerIn M))).symm
  have heodd : Odd (orderOf e) := hxeord ▸ hxeodd
  -- the (proved) sibling statement now applies verbatim.
  have hcomm := Case2Setup9Ecent I G hbc B M P hcoat ht hPp hPle hPidx e heE heodd hecen
  exact Subgroup.mem_centralizer_iff.mpr (fun y hy => (hcomm y hy).symm)

end Work.CORE4
