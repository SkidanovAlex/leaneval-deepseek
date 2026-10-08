import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.API
import Submission.Work.CORE4.Case2CountSetup
import Submission.Work.CORE4.Case2CountAssembly
import Submission.Work.CORE4.Counting.EConjLayerIn

open scoped MatrixGroups

namespace Work.CORE4

/-! ## Auxiliary transport lemmas

The proof of `L2TorusNormE` needs the centralizer `C_G(Y) ⊓ E` of a subgroup `Y ≤ E = layerIn h.D.M`
of the ambient group `G` to be identified, cardinality- and cyclicity-preserving, with the
centralizer of the image of `Y` under the §4 (9) isomorphism `φ : E ≃* PSL(2, GF pF kF)`.

The three lemmas below perform that identification in the generality in which it is true.
`centralizer_inf_eq_map_centralizer_subgroupOf` is the statement `C_G(Y) ⊓ E = C_E(Y)`
(`Y ≤ E`) realized as a `Subgroup.map`; `map_centralizer_eq_centralizer_map` is the fact that a
multiplicative equivalence carries centralizers to centralizers (Mathlib only has the inclusion
`Subgroup.map_centralizer_le_centralizer_image`; surjectivity gives the reverse inclusion); and
`centralizer_transport` combines them into a single multiplicative equivalence. -/

namespace TorusTransport

open Subgroup

/-- For `Y ≤ L ≤ G`, the centralizer of `Y` in `G` intersected with `L` is the image under
`L.subtype` of the centralizer of `Y` inside `L` (i.e. `C_G(Y) ⊓ L = C_L(Y)`). -/
theorem centralizer_inf_eq_map_centralizer_subgroupOf {G : Type*} [Group G]
    {L Y : Subgroup G} (hY : Y ≤ L) :
    Subgroup.centralizer (Y : Set G) ⊓ L =
      (Subgroup.centralizer (Y.subgroupOf L : Set ↥L)).map L.subtype := by
  ext g
  constructor
  · intro hg
    obtain ⟨hgC, hgL⟩ := Subgroup.mem_inf.mp hg
    rw [Subgroup.mem_map]
    refine ⟨⟨g, hgL⟩, ?_, rfl⟩
    rw [Subgroup.mem_centralizer_iff] at hgC ⊢
    intro y hy
    exact Subtype.ext (hgC (y : G) hy)
  · intro hg
    rw [Subgroup.mem_map] at hg
    rcases hg with ⟨x, hx, rfl⟩
    refine Subgroup.mem_inf.mpr ⟨?_, x.2⟩
    rw [Subgroup.mem_centralizer_iff] at hx ⊢
    intro y hy
    exact congrArg Subtype.val (hx ⟨y, hY hy⟩ hy)

/-- A multiplicative equivalence carries the centralizer of a subgroup onto the centralizer of its
image.  (Mathlib has `Subgroup.map_centralizer_le_centralizer_image`; surjectivity of the
equivalence gives the reverse inclusion.) -/
theorem map_centralizer_eq_centralizer_map {M N : Type*} [Group M] [Group N] (φ : M ≃* N)
    (X : Subgroup M) :
    (Subgroup.centralizer (X : Set M)).map φ.toMonoidHom =
      Subgroup.centralizer ((X.map φ.toMonoidHom) : Set N) := by
  refine le_antisymm ?_ ?_
  · rw [Subgroup.coe_map]
    exact Subgroup.map_centralizer_le_centralizer_image (X : Set M) φ.toMonoidHom
  · intro x hx
    rw [Subgroup.mem_map]
    refine ⟨φ.symm x, Subgroup.mem_centralizer_iff.mpr (fun y hy => ?_), by simp⟩
    apply φ.injective
    simp only [map_mul, φ.apply_symm_apply]
    exact Subgroup.mem_centralizer_iff.mp hx (φ y) (Subgroup.mem_map.mpr ⟨y, hy, rfl⟩)

/-- Transport of the centralizer of a subgroup `Y ≤ L ≤ G` into `N` along an isomorphism
`φ : ↥L ≃* N`: `C_G(Y) ⊓ L` and the centralizer in `N` of the image of `Y` have the same
cardinality, and one is cyclic if and only if the other is. -/
theorem centralizer_transport {G N : Type*} [Group G] [Group N] (L : Subgroup G)
    (φ : ↥L ≃* N) (Y₀ : Subgroup ↥L) :
    Nat.card ↥((Subgroup.centralizer (Y₀ : Set ↥L)).map L.subtype) =
      Nat.card ↥(Subgroup.centralizer ((Y₀.map φ.toMonoidHom) : Set N)) ∧
    (IsCyclic ↥((Subgroup.centralizer (Y₀ : Set ↥L)).map L.subtype) ↔
      IsCyclic ↥(Subgroup.centralizer ((Y₀.map φ.toMonoidHom) : Set N))) := by
  have hmap : (Subgroup.centralizer (Y₀ : Set ↥L)).map φ.toMonoidHom =
      Subgroup.centralizer ((Y₀.map φ.toMonoidHom) : Set N) :=
    map_centralizer_eq_centralizer_map φ Y₀
  have e1 := Subgroup.equivMapOfInjective (Subgroup.centralizer (Y₀ : Set ↥L)) L.subtype
    L.subtype_injective
  have e2 := Subgroup.equivMapOfInjective (Subgroup.centralizer (Y₀ : Set ↥L)) φ.toMonoidHom
    φ.injective
  have e : ↥((Subgroup.centralizer (Y₀ : Set ↥L)).map L.subtype) ≃*
      ↥(Subgroup.centralizer ((Y₀.map φ.toMonoidHom) : Set N)) :=
    e1.symm.trans (e2.trans (MulEquiv.subgroupCongr hmap))
  exact ⟨Nat.card_congr e.toEquiv, MulEquiv.isCyclic e⟩

end TorusTransport

/-- **Bender 1981, §4, p. 227 (`I.l2torusNorm`, `L2TorusNormalizerProp`, transported along §4 (9)).**

Let `E := layerIn h.D.M ≅ PSL(2, pF^kF)` (§4 (9)), `q := qOf h = pF^kF`, and let `Y ≤ E` be a
subgroup of odd prime order `r ≠ pF` (equivalently `r ∤ q`).  Then the centralizer of `Y` in `E`
is cyclic of order `(q ± 1)/2`:

    IsCyclic (C_E(Y))  and  (2 |C_E(Y)| = q + 1 or 2 |C_E(Y)| = q − 1).

(The full `I.l2torusNorm` also gives `N_E(Y) ≃* DihedralGroup |C_E(Y)|`, which the statement
omits only to keep the `DihedralGroup` notation out of the statement; the prover may keep it as a
helper.)

Route: `I.l2torusNorm` applied to the image `φ Y` under the §4 (9) isomorphism
`φ : E ≃* PSL(2, pF^kF)`.  For `Y ≤ E`, `C_G(Y) ⊓ E = C_E(Y)`, and
`Subgroup.equivMapOfInjective` identifies `C_E(Y)` with `C_{PSL}(φ Y)` preserving cardinality and
cyclicity, the same transport pattern as `Work.CORE4.Counting.EConjLayerIn`,
`Work.CORE4.Counting.EConjPrime` and `Work.CORE4.ncard_subgroups_eq_of_mulEquiv`.

This is one of the two `L₂(q)` inputs of §4 (12) (the other being `I.l2normTwo`); Bender uses it
in the form "a subgroup of order `r ∤ q` has a cyclic centralizer of order `(q ± 1)/2`". -/
theorem L2TorusNormE (I : Work.GW2.C4Inputs) :
    ∀ (G : Type) [Group G] [Finite G], Work.GW2.BenderCtx G →
      ∀ (B : Work.GW2.BenderSetup G) (h : Work.GW2.Case2Ctx B) (r : ℕ) (Y : Subgroup G),
        r.Prime → r ≠ 2 → r ≠ Work.CORE4.nineP h → Y ≤ Work.GW2.layerIn h.D.M →
        Nat.card ↥Y = r →
        let C : Subgroup G := Subgroup.centralizer (Y : Set G) ⊓ Work.GW2.layerIn h.D.M
        IsCyclic ↥C ∧ (2 * Nat.card ↥C = Work.CORE4.qOf h + 1 ∨
          2 * Nat.card ↥C = Work.CORE4.qOf h - 1) := by
  intro G _ _ hbc B h r Y hr hr2 hrp hYL hYr
  dsimp only
  -- §4 (9): the isomorphism `φ : E(M) ≃* PSL(2, pF^kF)` of the layer onto `L₂(q)`; `pF` is
  -- odd and `q = pF^kF ≥ 7`.
  haveI : Fact (Work.CORE4.nineP h).Prime := ⟨Work.CORE4.nineP_prime h⟩
  obtain ⟨φ⟩ := Work.CORE4.nineP_iso h
  have h7 : 7 ≤ Work.CORE4.qOf h := Work.CORE4.nineP_seven h
  have h5 : 5 ≤ Work.CORE4.nineP h ^ Work.CORE4.nineK h :=
    lt_of_lt_of_le (by norm_num) h7
  let L : Subgroup G := Work.GW2.layerIn h.D.M
  let N : Type := PSL(2, GaloisField (Work.CORE4.nineP h) (Work.CORE4.nineK h))
  -- `Y` transported into `PSL(2, pF^kF)`.
  let Yq : Subgroup N := (Y.subgroupOf L).map φ.toMonoidHom
  have hYLE : Y ≤ L := hYL
  -- `C_G(Y) ⊓ E = C_E(Y)` as the image of `C_E(Y)` under `E.subtype`.
  have hCeq : Subgroup.centralizer (Y : Set G) ⊓ L =
      (Subgroup.centralizer (Y.subgroupOf L : Set ↥L)).map L.subtype :=
    TorusTransport.centralizer_inf_eq_map_centralizer_subgroupOf hYLE
  -- Transport across `φ` preserves the cardinality and the cyclicity of the centralizer.
  obtain ⟨hcardT, hcycT⟩ :=
    TorusTransport.centralizer_transport (G := G) (N := N) L φ (Y.subgroupOf L)
  have hcard : Nat.card ↥(Subgroup.centralizer (Y : Set G) ⊓ L) =
      Nat.card ↥(Subgroup.centralizer (Yq : Set N)) := by
    rw [hCeq]; exact hcardT
  have hcyc : IsCyclic ↥(Subgroup.centralizer (Y : Set G) ⊓ L) ↔
      IsCyclic ↥(Subgroup.centralizer (Yq : Set N)) := by
    rw [hCeq]; exact hcycT
  -- `Yq` still has cardinality `r`.
  have hY'card : Nat.card ↥Yq = r := by
    rw [Subgroup.card_map_of_injective φ.injective,
      ← Subgroup.card_map_of_injective L.subtype_injective,
      Subgroup.map_subgroupOf_eq_of_le hYLE, hYr]
  -- Bender's `L₂(q)` input for the image of `Y`.
  obtain ⟨hcycPSL, hcardPSL, -⟩ := I.l2torusNorm (Work.CORE4.nineP h) (Work.CORE4.nineK h)
    (Work.CORE4.nineP_odd h) h5 r hr hr2 hrp Yq hY'card
  refine ⟨hcyc.mpr hcycPSL, ?_⟩
  rw [hcard]
  exact hcardPSL

end Work.CORE4
