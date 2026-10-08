import Mathlib
import Submission.Work.CORE3.Defs
import Submission.Work.CORE2A.Basic
import Submission.Work.CORE2A.le_oddCoreIn_of_normal_of_odd
import Submission.Work.CORE2A.dihOrCycSylow_subgroup
import Submission.Work.BMAX.commutator_eq_bot_of_isQuasisimple_of_isQuasisimple
import Submission.Work.DSTR.layerShapeAux.isQuasisimple_inf_oddCore_le_center

/-!
# CORE3: auxiliary API for the §3 `M`-analysis (`Work.CORE3.Case1aMDataProp`)

Pieces of Bender 1981 §3, p. 222–223 that are needed for the `M`-analysis of the subcase
`Ĥ = H` and are proved from the shared vocabulary alone:

* `MdataB B = C_U(S)`, Bender's `B` (p. 222);
* `mdata_layer_quasisimple`: `E(M) = layerIn M` is quasisimple with odd centre for the maximal
  `M ⊇ N_G(P₂)` (Bender's 1.6/`LayerProp`, applied to the D-group `M`);
* `mdata_oddCore_commutator_layer`: `⁅O(M), E(M)⁆ = 1` — `E ∩ O(M)` is central in the
  quasisimple `E`, and the three-subgroups lemma with `E = ⁅E,E⁆` finishes.
-/

namespace Work.CORE3

open Subgroup
open Work.GW2

/-! ## Bender's `B = C_U(S)` and this leaf's auxiliary vocabulary -/

/-- Bender 1981 §3, p. 222: `B := C_U(S)`, where `U = O(H)`, `H = C_G(t)` and `S` is the fixed
Sylow 2-subgroup.  Since `B.U = O(H) ≤ H`, this is `B.U ⊓ C_G(S)`. -/
def MdataB {G : Type} [Group G] [Finite G] (B : BenderSetup G) : Subgroup G :=
  B.U ⊓ Subgroup.centralizer ((B.S : Subgroup G) : Set G)

/-- `B = C_U(S) ≤ U = O(H)`. -/
theorem MdataB_le_U {G : Type} [Group G] [Finite G] (B : BenderSetup G) : MdataB B ≤ B.U :=
  inf_le_left

/-- `B = C_U(S)` centralizes `S`. -/
theorem MdataB_le_centralizer {G : Type} [Group G] [Finite G] (B : BenderSetup G) :
    MdataB B ≤ Subgroup.centralizer ((B.S : Subgroup G) : Set G) := inf_le_right

/-- `B = C_U(S)` has odd order (`B ≤ U = O(H)`, and `U` is odd). -/
theorem MdataB_odd {G : Type} [Group G] [Finite G] (B : BenderSetup G) :
    Odd (Nat.card (MdataB B)) :=
  Odd.of_dvd_nat (Work.CORE2A.bSetup_U_odd B) (Subgroup.card_dvd_of_le (MdataB_le_U B))


/-! ## The layer of `M` is quasisimple with odd centre

Bender 1981 §3 (second paragraph, "`E/Z(E)` must be `A₇`"), via Bender's 1.6/`LayerProp`
(`I.T.lay`): `E(M) = layerIn M` is the unique normal quasisimple subgroup of the D-group `M`,
and its centre has odd order. -/

/-- `E(M) = E(↥M)` is quasisimple with odd centre, for the maximal subgroup `M` of the §3
`M`-analysis.  (The `A₇`-shape of `E(M)/Z(E(M))` is the hypothesis `hA7`; here we only extract
quasisimplicity and oddness of the centre, which `LayerProp` supplies for every D-group.) -/
theorem mdata_layer_quasisimple {G : Type} [Group G] [Finite G] (I : Case1Inputs)
    (hCtx : BenderCtx G) (B : BenderSetup G) {M : Subgroup G} (hMcoat : IsCoatom M)
    (hlayer_ne : Work.GW2.layer ↥M ≠ ⊥) :
    IsQuasisimple (Work.GW2.layer ↥M) ∧
      Odd (Nat.card (Subgroup.center ↥(Work.GW2.layer ↥M))) := by
  classical
  -- `M` is a proper subgroup, hence a D-group
  have hcard_lt : Nat.card ↥M < Nat.card G :=
    Subgroup.card_lt_card_of_ne_top hMcoat.ne_top
  have hDih : DihOrCycSylow ↥M := Work.CORE2A.dihOrCycSylow_subgroup hCtx.sylow M
  have hIsD : IsDGroup ↥M := hCtx.ih ↥M hcard_lt hDih
  -- `↥M` has a normal quasisimple subgroup
  obtain ⟨E', hE'norm, hE'q⟩ : ∃ E' : Subgroup ↥M, E'.Normal ∧ IsQuasisimple E' := by
    by_contra hcon
    apply hlayer_ne
    rw [Work.GW2.layer, sSup_eq_bot]
    intro F hF
    by_contra hFne
    exact hcon ⟨F, hF.1, hF.2⟩
  -- Bender 1.6 (`LayerProp`)
  obtain ⟨hlayer_eq, hodd, _⟩ := I.T.lay ↥M I.T.ft hDih hIsD E' hE'norm hE'q
  exact ⟨hlayer_eq ▸ hE'q, hlayer_eq ▸ hodd⟩

/-! ## `O(M)` centralizes `E(M)`

Bender 1981 §3, p. 223 (design pass 6, §3(a) step 1): `E ∩ O(M)` is a proper normal subgroup of
the quasisimple `E = E(M)`, hence central in `E`; the three-subgroups lemma with `E = ⁅E,E⁆`
then gives `⁅E, O(M)⁆ = 1`.  Everything here happens inside the carrier group `↥M`. -/

/-- `⁅O(M), E(M)⁆ = 1`: in the notation of the carrier `↥M`,
`⁅O, E⁆ = ⊥` for `O = O(↥M)`, `E = E(↥M)` quasisimple.

`E ∩ O` is normal in `E` (both are normal in `↥M`), so its image in the simple group `E/Z(E)`
is `⊥` or `⊤`: in the first case `E ∩ O ≤ Z(E)`, in the second `E ≤ O`, which is impossible
because `E` is perfect, non-trivial, and of odd order (Feit–Thompson). -/
theorem mdata_commutator_oddCore_layer {X : Type} [Group X] [Finite X] (hFT : FeitThompsonProp)
    {E : Subgroup X} (hEn : E.Normal) (hEq : IsQuasisimple E) {O : Subgroup X} (hOn : O.Normal)
    (hOodd : Odd (Nat.card O)) : ⁅O, E⁆ = ⊥ := by
  haveI := hEn
  haveI := hOn
  have hOE_le : ⁅O, E⁆ ≤ O ⊓ E :=
    le_inf (Subgroup.commutator_le_left O E) (Subgroup.commutator_le_right O E)
  have hME : O ⊓ E ≤ E := inf_le_right
  rcases Work.BMAX.QuasiComm.le_centralizer_or_le_of_isQuasisimple (M := O ⊓ E) (E := E)
      (Subgroup.normal_inf_normal O E) hME hEn hEq with hcen | hle
  · -- `O ⊓ E ≤ C(E)`: the three-subgroups lemma finishes
    have h1a : ⁅⁅O, E⁆, E⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (le_trans hOE_le hcen)
    have h1b : ⁅⁅E, O⁆, E⁆ = ⊥ := by
      rw [Subgroup.commutator_comm E O]
      exact h1a
    have hrot : ⁅⁅E, E⁆, O⁆ = ⊥ :=
      Subgroup.commutator_commutator_eq_bot_of_rotate (H₁ := E) (H₂ := E) (H₃ := O) h1b h1a
    have hEO : ⁅E, O⁆ = ⊥ := by
      rwa [hEq.1] at hrot
    rwa [Subgroup.commutator_comm O E]
  · -- `E ≤ O`: `E` is perfect, non-trivial and of odd order — impossible
    exfalso
    have hEO : E ≤ O := le_trans hle inf_le_left
    have hEodd : Odd (Nat.card ↥E) :=
      Odd.of_dvd_nat hOodd (Subgroup.card_dvd_of_le hEO)
    haveI hsol : Group.IsSolvable ↥E :=
      Work.DSTR.layerShapeAux.isSolvable_of_odd_of_feitThompson hFT hEodd
    haveI hnt : Nontrivial ↥E := by
      haveI := hEq.2
      exact Function.Surjective.nontrivial (QuotientGroup.mk'_surjective (Subgroup.center ↥E))
    have hmaptop : Subgroup.map E.subtype (⊤ : Subgroup ↥E) = E := by
      rw [← Subgroup.subgroupOf_self E, Subgroup.subgroupOf_map_subtype]
      simp
    have hcomm : commutator ↥E = ⊤ := by
      have h1 : Subgroup.map E.subtype ⁅(⊤ : Subgroup ↥E), ⊤⁆ =
          Subgroup.map E.subtype (⊤ : Subgroup ↥E) := by
        rw [Subgroup.map_commutator, hmaptop, hEq.1]
      exact Subgroup.map_injective E.subtype_injective h1
    exact absurd hcomm (ne_of_lt (Group.IsSolvable.commutator_lt_top_of_nontrivial ↥E))

/-- `layer ↥M` is normal in `↥M` (it is a `sSup` of normal subgroups). -/
theorem mdata_layer_normal {G : Type} [Group G] (M : Subgroup G) : (layer ↥M).Normal := by
  rw [Work.GW2.layer]
  exact Subgroup.sSup_normal {H : Subgroup ↥M | H.Normal ∧ IsQuasisimple H} fun H hH => hH.1

/-- Ambient form of the previous lemma: `O(M)` commutes with `E(M)`, where `E(M) = layerIn M`
is assumed quasisimple. -/
theorem mdata_oddCore_commutator_layer {G : Type} [Group G] [Finite G] (M : Subgroup G)
    (hFT : FeitThompsonProp) (hE : IsQuasisimple (layer ↥M)) :
    ⁅oddCoreIn M, layerIn M⁆ = ⊥ := by
  have h1 : ⁅Work.GW2.oddCore ↥M, Work.GW2.layer ↥M⁆ = ⊥ :=
    mdata_commutator_oddCore_layer (X := ↥M) hFT (mdata_layer_normal M) hE
      (Work.GW2.oddCore_normal ↥M) (Work.ASM.oddCore_odd ↥M)
  rw [Work.GW2.oddCoreIn, Work.GW2.layerIn, ← Subgroup.map_commutator, h1, Subgroup.map_bot]

/-- `O(M) ≤ C_G(E(M))`. -/
theorem mdata_oddCore_le_centralizer_layer {G : Type} [Group G] [Finite G] (M : Subgroup G)
    (hFT : FeitThompsonProp) (hE : IsQuasisimple (layer ↥M)) :
    oddCoreIn M ≤ Subgroup.centralizer ((layerIn M : Subgroup G) : Set G) :=
  Subgroup.commutator_eq_bot_iff_le_centralizer.mp (mdata_oddCore_commutator_layer M hFT hE)



/-- `O(K) ≤ K`. -/
theorem oddCoreIn_le_self {G : Type} [Group G] (K : Subgroup G) : oddCoreIn K ≤ K :=
  Subgroup.map_subtype_le _


/-- `O_p(K) ≤ K`. -/
theorem pCoreIn_le_self {G : Type} [Group G] (p : ℕ) (K : Subgroup G) : pCoreIn p K ≤ K :=
  Subgroup.map_subtype_le _

end Work.CORE3
