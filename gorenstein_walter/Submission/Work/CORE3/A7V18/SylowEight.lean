import Mathlib
import Submission.Work.CORE3.Defs
import Submission.Work.CORE3.Case1aFrattini
import Submission.Work.CORE3.Case1aAbelian
import Submission.Work.CORE3.MDataAux
import Submission.Work.CORE2A.Basic
import Submission.Work.CORE3.A7V18.QuasisimpleMapOddCore
import Submission.Work.CORE3.A7V18.A7SylowTwoThreeShapes
import Submission.Work.CORE3.A7V18.NotA7QuotientPSL2PGL2
import Submission.Work.CORE3.A7V18.LayerInTransport
import Submission.Work.CORE3.A7V18.SylowCardTwoPow

namespace Work.CORE3.A7V18

open Subgroup

/-!
# CORE3 / A7V18: `|S| = 8` in the subcase `Ĥ = H` (Bender 1981, §3, p. 222–223)

Bender's paragraph (p. 223) reads

> Take a maximal subgroup `M` of `G` containing `N_G(P₂)`.  Then `S ≤ M` and `P₀ := P ∩ M ≠ 1`.
> … and `E/Z(E)` must be `A₇` … This gives … `|S| = 8` …

The formal proof of `|S| = 8` given below does *not* use the `p`-part analysis of the same
paragraph; it only uses the `A₇`-shape of the layer of `M` together with the following three
elementary facts.

* `S` centralizes `P₂` (hypothesis `P₂ ≤ B.U ⊓ C_G(S)`), hence `S ≤ N_G(P₂) ≤ M`; since `S` is a
  Sylow `2`-subgroup of `G` it is a Sylow `2`-subgroup of `M`, so `|S| = |M|₂`
  (`Work.CORE3.A7V18.SylowCardTwoPow`).
* The layer `E(M) = layerIn M` is quasisimple with odd centre
  (`Work.CORE3.mdata_layer_quasisimple`, from the `D`-group structure of `M`), and
  `E(M)/Z(E(M)) ≅ A₇` by hypothesis; hence `|E(M)|₂ = 8` and the image `Ē` of `E(M)` in
  `Q := M/O(M)` is a normal quasisimple subgroup of `Q` with `Ē/Z(Ē) ≅ A₇`
  (`Work.CORE3.A7V18.QuasisimpleMapOddCore`).
* `DShape Q` holds (`M` is a `D`-group, `BenderCtx.ih`), and among the four shapes only
  `Q ≅ A₇` is compatible with the existence of `Ē`: the `2`-group and the self-centralizing
  four-group shapes would make `Ē` perfect and solvable, and the `L₂(q)`/`PGL₂(q)` shape is
  excluded because `A₇` is not a section of `L₂(q)`
  (`Work.CORE3.A7V18.A7SylowTwoThreeShapes`, `Work.CORE3.A7V18.NotA7QuotientPSL2PGL2`).

Consequently `|S| = |M|₂ = |Q|₂ = 2 ^ 3 = 8`.
-/

theorem SylowEight (I : Work.CORE3.Case1Inputs) (hFr : Work.GW2.Case1aFrattiniProp)
    (hAb : Work.GW2.Case1aAbelianProp) :
    ∀ (G : Type) [Group G] [Finite G], Work.GW2.FeitThompsonProp → Work.GW2.BenderCtx G →
      ∀ B : Work.GW2.BenderSetup G,
      Work.GW2.Case1 B → B.Hhat = B.H → ∀ D : Work.GW2.Case1aData B, ∀ P2 M : Subgroup G,
        P2 ≤ B.U ⊓ Subgroup.centralizer ((B.S : Subgroup G) : Set G) → IsPGroup D.p P2 →
        ¬ D.p ∣ P2.relIndex (B.U ⊓ Subgroup.centralizer ((B.S : Subgroup G) : Set G)) →
        IsCoatom M → Subgroup.normalizer (P2 : Set G) ≤ M →
        (Subgroup.zpowers B.t ⊔ Subgroup.zpowers D.t2 : Subgroup G) ≤ Work.GW2.layerIn M →
        Nonempty ((↥(Work.GW2.layerIn M) ⧸ Subgroup.center ↥(Work.GW2.layerIn M)) ≃*
          alternatingGroup (Fin 7)) →
        Nat.card (B.S : Subgroup G) = 8 := by
  intro G _ _ hFT hCtx B _hCase _hHhat D P2 M hP2le _hP2grp _hP2ndvd hMcoat hNM hlayer hA7
  classical
  -- ### `S ≤ M`
  have hSleM : (B.S : Subgroup G) ≤ M := by
    have hP2le' : P2 ≤ Subgroup.centralizer ((B.S : Subgroup G) : Set G) := hP2le.trans inf_le_right
    have hSleC : (B.S : Subgroup G) ≤ Subgroup.centralizer (P2 : Set G) := by
      intro s hs
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      exact (Subgroup.mem_centralizer_iff.mp (hP2le' hx) s hs).symm
    exact hSleC.trans (le_trans (Subgroup.centralizer_le_normalizer (P2 : Set G)) hNM)
  -- ### the involution `t` lies in `E(M) = layerIn M`
  have ht_layer : B.t ∈ Work.GW2.layerIn M :=
    hlayer (Subgroup.mem_sup_left (Subgroup.mem_zpowers B.t))
  have ht_ne : B.t ≠ 1 := Work.CORE2A.bSetup_t_ne_one B
  -- ### `E(M)` is nontrivial, quasisimple, with `A₇` central quotient
  obtain ⟨hlayer_ne, hlayer_notle, hA7layer⟩ :=
    LayerInTransport M ht_layer ht_ne B.t_order hA7
  obtain ⟨hLayQ, hZodd⟩ := Work.CORE3.mdata_layer_quasisimple I hCtx B hMcoat hlayer_ne
  -- ### `M` is a `D`-group, i.e. `Q := M/O(M)` has one of the four `DShape` shapes
  have hcard_lt : Nat.card ↥M < Nat.card G := Subgroup.card_lt_card_of_ne_top hMcoat.ne_top
  have hDih : Work.GW2.DihOrCycSylow ↥M := Work.CORE2A.dihOrCycSylow_subgroup hCtx.sylow M
  have hD : Work.GW2.DShape (↥M ⧸ Work.GW2.oddCore ↥M) := hCtx.ih ↥M hcard_lt hDih
  -- ### the image of the layer in `Q`
  obtain ⟨_hEn, hEqQ, _hEne, hA7Q⟩ :=
    QuasisimpleMapOddCore (Work.GW2.layer ↥M) (Work.CORE3.mdata_layer_normal M)
      hLayQ hA7layer hlayer_notle
  set Ē : Subgroup (↥M ⧸ Work.GW2.oddCore ↥M) :=
    (Work.GW2.layer ↥M).map (QuotientGroup.mk' (Work.GW2.oddCore ↥M)) with hĒ
  -- ### `|Q|₂ = 8`
  have hQ8 : 2 ^ (Nat.card (↥M ⧸ Work.GW2.oddCore ↥M)).factorization 2 = 8 := by
    rcases hD with h2grp | hV4 | hA7iso | hLclause
    · exact A7SylowTwoThreeShapes (Or.inl h2grp) Ē hEqQ hA7Q
    · exact A7SylowTwoThreeShapes (Or.inr (Or.inl hV4)) Ē hEqQ hA7Q
    · exact A7SylowTwoThreeShapes (Or.inr (Or.inr hA7iso)) Ē hEqQ hA7Q
    · obtain ⟨L, hLn, hLodd, p, k, hpfact, hpodd, h5, hLiso⟩ := hLclause
      haveI : Fact p.Prime := hpfact
      exact (NotA7QuotientPSL2PGL2 hFT L hLn hLodd p k hpodd h5 hLiso Ē hEqQ hA7Q).elim
  -- ### assemble
  rw [SylowCardTwoPow B M hSleM, hQ8]

end Work.CORE3.A7V18
