import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.Defs19
import Submission.Work.CORE4.LayerFactsProper
import Submission.Work.CORE4.API
import Submission.Work.CORE4.Case2Six9
import Submission.Work.CORE4.Case2Six9Aux.layerIn_eq_of_normal_quasisimple

namespace Work.CORE4

open Work.GW2 Subgroup

/-- **Design-19 leaf TI**: (★) ⟹ TI, i.e. `F ⊓ F^g = ⊥` for `g ∉ M`.

Statement (verbatim, `Work.GW2.C19.SixTIOfStarProp`): for `BenderCtx G`, `B`, `D` with
`Case2Pre B D` and `(★)` (`∀ X, X ≠ ⊥ → X ≤ D.F → normalizer (X : Set G) ≤ D.M`):
`∀ g ∉ D.M, D.F ⊓ conjSub g D.F = ⊥`.

Route (= `NOTES_CASE2SIX9.md` §3 (⇐)): suppose `X := D.F ⊓ conjSub g D.F ≠ ⊥`.  Then `X ≤ D.F` and
`X ≤ conjSub g D.F`, so
* `E := layerIn D.M ≤ C_G(D.F) ≤ C_G(X) ≤ N_G(X) ≤ D.M` by (★) (`Case2Pre.F_cent`);
* conjugin (★) at `conjSub g⁻¹ X ≤ D.F` gives `N_G(X) ≤ M^g`.
Hence `K := E ⊔ conjSub g E ≤ D.M ⊓ (D.M)^g < ⊤` (`D.M` a coatom, `D.M ≠ M^g` as `g ∉ M`), and both
`E` and `E^g` are normal quasisimple in the D-group `K`, so
`Work.CORE4.Case2Six9Aux.layerIn_eq_of_normal_quasisimple` gives `E = layerIn K = E^g`, i.e.
`g ∈ N_G(E) = D.M` (proved `Case2Six9.normalizer_layerIn_eq_data`) — contradiction. -/
theorem SixTIOfStar (I : Work.GW2.C4Inputs) : Work.GW2.C19.SixTIOfStarProp I := by
  intro G _ _ hbc B D hpre hstar g hgM
  by_contra hne
  -- `X := F ⊓ F^g`, assumed nontrivial
  set X : Subgroup G := D.F ⊓ conjSub g D.F with hX
  have hXne : X ≠ ⊥ := by rw [hX]; exact hne
  have hXF : X ≤ D.F := by rw [hX]; exact inf_le_left
  have hXFg : X ≤ conjSub g D.F := by rw [hX]; exact inf_le_right
  -- `E := E(M) = layerIn D.M`
  set E : Subgroup G := layerIn D.M with hE
  -- (★) at `X`: `N_G(X) ≤ M`
  have hTleM : normalizer (X : Set G) ≤ D.M := hstar X hXne hXF
  -- `X' := X^{g⁻¹} ≤ F`, so (★) at `X'` conjugates to `N_G(X) ≤ M^g`
  set X' : Subgroup G := conjSub g⁻¹ X with hX'
  have hX'F : X' ≤ D.F := by
    rw [hX']
    have h2 : conjSub g⁻¹ (conjSub g D.F) = D.F := by
      rw [conjSub_conjSub_six9, inv_mul_cancel, Work.CORE4.conjSub_one_six9]
    calc conjSub g⁻¹ X ≤ conjSub g⁻¹ (conjSub g D.F) := Subgroup.map_mono hXFg
      _ = D.F := h2
  have hX'ne : X' ≠ ⊥ := by
    rw [hX']
    intro h
    apply hXne
    have h1 : conjSub g (conjSub g⁻¹ X) = ⊥ := by
      rw [h]
      exact Subgroup.map_bot _
    rw [conjSub_conjSub_six9, mul_inv_cancel, Work.CORE4.conjSub_one_six9] at h1
    exact h1
  have hconj : conjSub g X' = X := by
    rw [hX', conjSub_conjSub_six9, mul_inv_cancel, Work.CORE4.conjSub_one_six9]
  have hTleMg : normalizer (X : Set G) ≤ conjSub g D.M := by
    have h2 : conjSub g (normalizer (X' : Set G)) ≤ conjSub g D.M :=
      Subgroup.map_mono (hstar X' hX'ne hX'F)
    have hN : normalizer (X : Set G) = conjSub g (normalizer (X' : Set G)) := by
      rw [← hconj]
      exact Work.CORE4.normalizer_conjSub g X'
    rw [hN]; exact h2
  -- `T := N_G(X)` is proper (it sits inside the coatom `M`)
  have hTtop : normalizer (X : Set G) ≠ ⊤ := by
    intro h
    exact Case2Data.M_ne_top B D (top_le_iff.mp (h ▸ hTleM))
  -- `E ≤ C_G(F) ≤ C_G(X) ≤ N_G(X)`
  have hEcentF : E ≤ Subgroup.centralizer (D.F : Set G) := by
    intro e he
    rw [Subgroup.mem_centralizer_iff]
    intro f hf
    have hfe : f ∈ Subgroup.centralizer (E : Set G) := by
      rw [hE]; exact Work.GW2.Case2Pre.F_cent B D hpre hf
    exact (Subgroup.mem_centralizer_iff.mp hfe e he).symm
  have hET : E ≤ normalizer (X : Set G) :=
    le_trans (le_trans hEcentF (Subgroup.centralizer_le hXF))
      (Subgroup.centralizer_le_normalizer (X : Set G))
  -- `E^g ≤ C_G(F^g) ≤ C_G(X) ≤ N_G(X)`
  have hEgcentFg : conjSub g E ≤ Subgroup.centralizer (conjSub g D.F : Set G) := by
    rw [← Work.CORE4.conjSub_centralizer g D.F]
    exact Subgroup.map_mono hEcentF
  have hEgT : conjSub g E ≤ normalizer (X : Set G) :=
    le_trans (le_trans hEgcentFg (Subgroup.centralizer_le hXFg))
      (Subgroup.centralizer_le_normalizer (X : Set G))
  -- sanity: `E` is quasisimple (Bender §4, p. 224)
  have hEq : IsQuasisimple E := by
    rw [hE]
    show IsQuasisimple ((Work.GW2.layer ↥D.M).map (D.M).subtype)
    obtain ⟨E1, _hE1norm, hlayer, hE1q, _hodd, _hshape⟩ :=
      Work.CORE4.layer_facts_proper_quasisimple I hbc D.M_coatom.ne_top D.t_mem
    rw [hlayer]
    exact Work.CORE4.isQuasisimple_map (D.M).subtype (Subgroup.subtype_injective D.M) hE1q
  -- `T ≤ N_G(E)`: `T ≤ M ≤ N_G(E)`
  have hT_NE : normalizer (X : Set G) ≤ Subgroup.normalizer (E : Set G) := by
    refine le_trans hTleM ?_
    rw [hE]; exact Work.CORE4.layerIn_le_normalizer D.M
  -- `T ≤ N_G(E^g)`: `T ≤ M^g ≤ N_G(E)^g = N_G(E^g)`
  have hT_NEg : normalizer (X : Set G) ≤
      Subgroup.normalizer ((conjSub g E : Subgroup G) : Set G) := by
    rw [Work.CORE4.normalizer_conjSub g E]
    refine le_trans hTleMg ?_
    have hME : D.M ≤ Subgroup.normalizer (E : Set G) := by
      rw [hE]; exact Work.CORE4.layerIn_le_normalizer D.M
    exact Subgroup.map_mono hME
  -- uniqueness of the normal quasisimple subgroup in the D-group `↥T`
  have hlayer1 : layerIn (normalizer (X : Set G)) = E :=
    Work.CORE4.Case2Six9Aux.layerIn_eq_of_normal_quasisimple I hbc hTtop hET hT_NE hEq
  have hlayer2 : layerIn (normalizer (X : Set G)) = conjSub g E :=
    Work.CORE4.Case2Six9Aux.layerIn_eq_of_normal_quasisimple I hbc hTtop hEgT hT_NEg
      (Work.CORE4.isQuasisimple_conjSub g hEq)
  have hEeq : E = conjSub g E := hlayer1.symm.trans hlayer2
  -- hence `g ∈ N_G(E) = M`
  have hgN : g ∈ Subgroup.normalizer (E : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    exact hEeq.symm
  have hgMg : g ∈ D.M := by
    rw [← Work.CORE4.normalizer_layerIn_eq_data hbc D]
    rw [← hE]
    exact hgN
  exact hgM hgMg

end Work.CORE4
