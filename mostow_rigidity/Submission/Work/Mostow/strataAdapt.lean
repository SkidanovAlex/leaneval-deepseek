import Mathlib
import Submission.Work.Mostow.euclid_block_normal_form
import Submission.Work.Mostow.vblk_add_smul
import Submission.Work.Mostow.conj_fundamentalDomain
import Submission.Work.Mostow.poAction_ge1
import Submission.Work.Mostow.hypIsometry_ge1
import Submission.Work.Mostow.normConjIsom
import Submission.Work.Mostow.blk_smul_fermi
import Submission.Work.Mostow.ellipticAux
import Submission.Work.Mostow.centralizer_acts_fermi
import Submission.Work.Mostow.resStd_hom_discrete
import Submission.Work.Mostow.nrmStdMulAndRotNConj
import Submission.Work.Mostow.fermiLineTwo
import Submission.Work.Mostow.centralizer_mem_SetStabStd
import Submission.Work.Mostow.geeBlkAdaptLtDim
import Submission.Work.Mostow.geeSVblkCastEq
import Submission.Work.Mostow.geeSVblkRotN
import Submission.Work.Mostow.rotCanonAux
import Submission.Work.Mostow.strataAdaptFold
import Submission.Work.Mostow.strataAdaptRotN

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

/-! ## Adapting the standard stratum to the fixed stratum of a block isometry (CHAPTER PIECE)

Setting: `k + m` is the ambient dimension, `2 ≤ k`, `1 ≤ m`, `Λ ≤ PO (k+m) 1` discrete with
fundamental domain `D`, and `b = blk k m 1 S ∈ Λ` where `S ∈ O(m)` has a *nonzero fixed vector*
(so `Fix b` is a stratum of dimension `k + d`, `d ≥ 1`, strictly bigger than `stdTG k m`, the fixed
stratum of a fixed-free block), and `S` is minimal: every non-identity `c ∈ Λ` fixing `stdTG k m`
pointwise has `rotN (nrmStd k m c) ≥ rotN S`.

Conclusion: an equivalent configuration in which that bigger stratum *is* the standard one:
`j' = k + d ≥ 2`, `m' = m - d ≥ 1`, `j' + m' = k + m`, a discrete `Λ' ≤ PO (k+m) 1` with
fundamental domain `D'` of the *same* volume, containing `hj'm' ▸ blk j' m' 1 R'` for some
*fixed-free* `R'` with `rotN R' ≤ rotN S`, and the separation hypothesis transferred:
every non-identity `c' ∈ Λ'` commuting with that element with trivial `resStd j' m'` has
`rotN (nrmStd j' m' c') ≥ rotN R'`.

A nearly complete route is written in the doc comment of the existing (still unproved) file
`Submission/Work/Mostow/geeBlkAdapt.lean`, whose statement is the same up to an extra cast of the
ambient `PO n 1`; the present statement keeps everything in the single ambient `PO (k+m) 1`.

Route.
* `Work.Mostow.euclid_block_normal_form m S` (proved) gives `d ≤ m`, `R' : E (m-d) ≃ₗᵢ E (m-d)`
  fixed-free and a linear isometry `P` of `E m` with `P (S (P.symm u)) = vblk d hd R' u`
  (`vblk` is the coordinate block map of `Submission/Work/Mostow/euclidBlockDefs.lean`, with
  coordinates `vblk_ofLp_of_lt`/`vblk_ofLp_of_ge`); `0 < rotN S` gives `d ≠ m`, so `m' ≥ 1`.  Also
  `rotN R' = rotN S`: `S = P.symm ∘ vblk d hd R' ∘ P` and the operator norm of `vblk d hd R' - 1`
  is that of `R' - 1` (block-diagonal operator norm, `opNorm_le_of_orthogonalBlocks_max` or an
  explicit-vector computation; isometric conjugacy via `Work.Mostow.normConjIsom`).
* `b` acts on the chart as `linBlk k m S` (`Work.Mostow.blk_smul_linBlk`).  Conjugating by the
  element `u ∈ PO (k+m) 1` realising the coordinate change `(t₁, y) ↦ (t₁, P y)` on
  `E (k+m) = E k × E m` (`HypIsometryProp`'s surjectivity clause; alternatively the block element
  `blk k m 1 P` together with `blk_hom`) turns `b` into the element acting as
  `vblk (k+d) hkd R'` (`hkd : k + d ≤ k + m`).  Prove the coordinate identity
  `vblk k hk (vblk d hd R) = vblk (k+d) hkd R` on `E (k+m)` (coordinate computation, cf.
  `vblk_ofLp_of_lt`/`vblk_ofLp_of_ge`), identify `vblk (k+d) hkd R'` with the chart action of
  `hj'm' ▸ blk j' m' 1 R'` via `Work.Mostow.vblk_cast_linBlk_chart` +
  `Work.Mostow.blk_smul_linBlk`, and conclude `u * b * u⁻¹ = hj'm' ▸ blk j' m' 1 R'` with
  `Work.Mostow.po_ext`.
* Transport group and domain: `Λ' := hj'm'.symm ▸ (Λ.map (MulAut.conj u))` and
  `D' := hj'm'.symm ▸ (u • D)`; `Work.Mostow.conj_fundamentalDomain` gives the fundamental-domain
  property for the conjugate, the measure-preserving clause of `HypIsometryProp` gives
  `volH (k+m) (u • D) = volH (k+m) D`, and discreteness follows from `IsDiscrete.image` with
  `Topology.IsInducing` of `x ↦ u * x * u⁻¹` (`Homeomorph.mulLeft`, `Homeomorph.mulRight`,
  `Homeomorph.isInducing`).  All casts along `hj'm'` collapse by `cases hj'm'` (prove once the
  four transport lemmas `volH b (e ▸ s) = volH a s`, and the `IsDiscrete`/`IsFundamentalDomain`/
  membership transports along `e : a = b`, each by `cases e; exact id`).
* Separation transfer: for `c' ∈ Λ'` commuting with the new block element with
  `resStd j' m' c' = 1`, the element `c = u⁻¹ * (hj'm' ▸ c') * u ∈ Λ` fixes `Fix b` pointwise,
  hence `stdTG k m`, and the minimality hypothesis gives `rotN S ≤ rotN (nrmStd k m c)`.  Moreover
  `nrmStd k m c` fixes the `d`-dimensional fixed space of `S` pointwise and its restriction to the
  orthogonal complement is `nrmStd j' m' c'`, so `rotN (nrmStd k m c) ≤ rotN (nrmStd j' m' c')`
  (block-diagonal operator norm).  With `rotN R' ≤ rotN S` this gives the transfer. -/


/-! ## Helper lemmas for the adaptation argument -/

private lemma cast_po_injective {a b : ℕ} (e : a = b) :
    Function.Injective (fun X : PO a 1 => (e ▸ X : PO b 1)) := by
  cases e
  intro x y h
  exact h

private lemma linBlk_one (k m : ℕ) (x : E (k + m)) :
    linBlk k m (1 : E m ≃ₗᵢ[ℝ] E m) x = x := by
  refine eq_of_tanC_nrmC' ?_ ?_
  · rw [linBlk_tanC]
  · rw [linBlk_nrmC, LinearIsometryEquiv.coe_one, id_eq]

private lemma linBlk_mul (k m : ℕ) (R1 R2 : E m ≃ₗᵢ[ℝ] E m) (x : E (k + m)) :
    linBlk k m (R1 * R2) x = linBlk k m R1 (linBlk k m R2 x) := by
  refine eq_of_tanC_nrmC' ?_ ?_
  · rw [linBlk_tanC, linBlk_tanC, linBlk_tanC]
  · rw [linBlk_nrmC, linBlk_nrmC, linBlk_nrmC]
    rfl

/-- `nrmC k m (coordEmb k m v) = 0`. -/
private lemma nrmC_coordEmb (k m : ℕ) (v : E k) : nrmC k m (coordEmb k m v) = 0 := by
  apply WithLp.ofLp_injective
  funext i
  simp [nrmC, coordEmb]

/-- A linear block map fixes the standard stratum pointwise. -/
private lemma linBlk_coordEmb (k m : ℕ) (T : E m ≃ₗᵢ[ℝ] E m) (v : E k) :
    linBlk k m T (coordEmb k m v) = coordEmb k m v := by
  refine eq_of_tanC_nrmC' ?_ ?_
  · rw [linBlk_tanC, rhd_tanC_coordEmb]
  · simp only [linBlk_nrmC, nrmC_coordEmb, map_zero]

/-- Points of the standard stratum have vanishing coordinates from `k` on. -/
private lemma coordEmb_ofLp_ge {k m : ℕ} (v : E k) (i : Fin (k + m)) (h : k ≤ (i : ℕ)) :
    (coordEmb k m v).ofLp i = 0 := by
  revert h
  refine Fin.addCases (motive := fun i => k ≤ (i : ℕ) → (coordEmb k m v).ofLp i = 0)
    (fun i => ?_) (fun i => ?_) i
  · intro hi
    have h1 : (i : ℕ) < k := i.isLt
    have h2 : k ≤ ((Fin.castAdd m i : Fin (k + m)) : ℕ) := hi
    rw [Fin.val_castAdd] at h2
    omega
  · intro _
    simp [coordEmb]

/-- A chart point with vanishing coordinates from `j` on lies in the standard stratum. -/
private lemma coordEmb_tanC_of_tail_zero {j m' : ℕ} {z : E (j + m')}
    (hz : ∀ i : Fin (j + m'), j ≤ (i : ℕ) → z.ofLp i = 0) :
    coordEmb j m' (tanC j m' z) = z := by
  apply WithLp.ofLp_injective
  funext i
  refine Fin.addCases (motive := fun i => (coordEmb j m' (tanC j m' z)).ofLp i = z.ofLp i)
    (fun i => ?_) (fun i => ?_) i
  · simp [coordEmb, tanC]
  · rw [coordEmb, WithLp.ofLp_toLp, Fin.append_right]
    simp only [Pi.zero_apply]
    exact (hz (Fin.natAdd j i) (by rw [Fin.val_natAdd]; exact Nat.le_add_right j i)).symm

theorem strataAdapt (k m : ℕ) (hk : 2 ≤ k) (hm : 1 ≤ m) :
    ∀ (Λ : Subgroup (PO (k + m) 1)) (D : Set (E (k + m))) (S : E m ≃ₗᵢ[ℝ] E m),
      IsDiscrete (Λ : Set (PO (k + m) 1)) → IsFundamentalDomain Λ D (volH (k + m)) →
      blk k m 1 S ∈ Λ → 0 < rotN S → (∃ w : E m, S w = w ∧ w ≠ 0) →
      (∀ c : PO (k + m) 1, c ∈ Λ → (∀ v : E k, c • coordEmb k m v = coordEmb k m v) → c ≠ 1 →
        rotN S ≤ rotN (nrmStd k m c)) →
      ∃ (j' m' : ℕ) (hj'm' : j' + m' = k + m) (Λ' : Subgroup (PO (k + m) 1))
        (D' : Set (E (k + m))) (R' : E m' ≃ₗᵢ[ℝ] E m'),
        2 ≤ j' ∧ 1 ≤ m' ∧
        IsDiscrete (Λ' : Set (PO (k + m) 1)) ∧
        IsFundamentalDomain Λ' D' (volH (k + m)) ∧
        volH (k + m) D' = volH (k + m) D ∧
        (hj'm' ▸ blk j' m' 1 R' : PO (k + m) 1) ∈ Λ' ∧
        (∀ w : E m', R' w = w → w = 0) ∧
        rotN R' ≤ rotN S ∧
        (∀ c' : PO (k + m) 1, c' ∈ Λ' →
          c' ∈ Subgroup.centralizer {(hj'm' ▸ blk j' m' 1 R' : PO (k + m) 1)} →
          resStd j' m' (hj'm'.symm ▸ c' : PO (j' + m') 1) = 1 → c' ≠ 1 →
          rotN R' ≤ rotN (nrmStd j' m' (hj'm'.symm ▸ c' : PO (j' + m') 1))) := by
  intro Λ D S hdisc hD hb hS hnfv hsep
  have hAkm : POActionProp (k + m) := rcPOActionProp (k + m)
  have hIkm : HypIsometryProp (k + m) := rcHypIsometryProp (k + m)
  have hAk : POActionProp k := rcPOActionProp k
  have hIk : HypIsometryProp k := rcHypIsometryProp k
  have hP := POBasic.ofProp hAkm
  -- Euclidean block normal form of `S`
  obtain ⟨r, hr, RS, PS, hRSfree, hPS⟩ := euclid_block_normal_form m S
  have hrlt : r < m := geeBlkAdaptLtDim m r hr S RS PS hPS hS
  have eeq : (k + r) + (m - r) = k + m := by omega
  have hAr : POActionProp (k + r) := rcPOActionProp (k + r)
  have hIr : HypIsometryProp (k + r) := rcHypIsometryProp (k + r)
  have hAn : POActionProp ((k + r) + (m - r)) := rcPOActionProp ((k + r) + (m - r))
  have hIn : HypIsometryProp ((k + r) + (m - r)) := rcHypIsometryProp ((k + r) + (m - r))
  -- the conjugate normal block
  set RB : E m ≃ₗᵢ[ℝ] E m := PS * S * PS⁻¹ with hRBdef
  have hRB : ∀ u : E m, RB u = vblk r hr RS u := by
    intro u
    have h2 : RB u = PS (S (PS.symm u)) := by
      rw [hRBdef,
        show (PS⁻¹ : E m ≃ₗᵢ[ℝ] E m) = PS.symm from LinearIsometryEquiv.inv_def PS]
      simp
    rw [h2]; exact hPS u
  have hrotRB : rotN RB = rotN S := by
    rw [hRBdef]; exact rhd_rotN_conj PS S
  have hRSleS : rotN RS ≤ rotN S := (geeSVblkRotN m r hr RS RB hRB).trans_eq hrotRB
  have hcast : (eeq ▸ (blk (k + r) (m - r) 1 RS : PO ((k + r) + (m - r)) 1) : PO (k + m) 1)
      = (blk k m 1 RB : PO (k + m) 1) := geeSVblkCastEq k m r hr eeq RB RS hRB
  -- the conjugating element is the block element with normal part `PS`
  set Th : PO (k + m) 1 := blk k m 1 PS with hTdef
  have hhom := blk_hom k m hAk hIk hAkm hIkm
  have hThinv : Th⁻¹ = blk k m 1 PS⁻¹ := by
    rw [hTdef]
    refine inv_eq_of_mul_eq_one_right ?_
    have h := hhom.1 1 1 PS PS⁻¹
    rw [one_mul, mul_inv_cancel, hhom.2.1] at h
    exact h.symm
  have hblkmul : ∀ N : E m ≃ₗᵢ[ℝ] E m,
      Th * blk k m 1 N * Th⁻¹ = blk k m 1 (PS * N * PS⁻¹) := by
    intro N
    rw [hTdef, hThinv]
    rw [show blk k m 1 PS * blk k m 1 N = blk k m 1 (PS * N) from by
          rw [← hhom.1 1 1 PS N]; simp]
    rw [show blk k m 1 (PS * N) * blk k m 1 PS⁻¹ = blk k m 1 (PS * N * PS⁻¹) from by
          rw [← hhom.1 1 1 (PS * N) PS⁻¹]; simp]
  have hconj : Th * blk k m 1 S * Th⁻¹
      = (eeq ▸ (blk (k + r) (m - r) 1 RS : PO ((k + r) + (m - r)) 1) : PO (k + m) 1) := by
    rw [hblkmul S, ← hRBdef]
    exact hcast.symm
  -- transport of discreteness
  have hdisc' : IsDiscrete ((Λ.map (MulAut.conj Th).toMonoidHom : Subgroup (PO (k + m) 1)) :
      Set (PO (k + m) 1)) := by
    have hcoe : ((Λ.map (MulAut.conj Th).toMonoidHom : Subgroup (PO (k + m) 1)) :
          Set (PO (k + m) 1))
        = (fun x : PO (k + m) 1 => Th * x * Th⁻¹) '' (Λ : Set (PO (k + m) 1)) := by
      ext x
      rw [SetLike.mem_coe, Subgroup.mem_map, Set.mem_image]
      constructor
      · rintro ⟨a, ha, hax⟩
        exact ⟨a, ha, (hax.symm.trans (MulAut.conj_apply Th a)).symm⟩
      · rintro ⟨a, ha, hax⟩
        exact ⟨a, ha, (MulAut.conj_apply Th a).trans hax⟩
    rw [hcoe]
    have hiso : (fun x : PO (k + m) 1 => Th * x * Th⁻¹)
        = ⇑((Homeomorph.mulRight Th⁻¹).trans (Homeomorph.mulLeft Th)) := by
      funext x
      simp only [Homeomorph.trans_apply, Homeomorph.coe_mulRight, Homeomorph.coe_mulLeft,
        mul_assoc]
    rw [hiso]
    exact IsDiscrete.image hdisc (Homeomorph.isInducing _)
  have hFD : IsFundamentalDomain (Λ.map (MulAut.conj Th).toMonoidHom)
      ((fun u : E (k + m) => Th • u) '' D) (volH (k + m)) :=
    conj_fundamentalDomain (k + m) hAkm hIkm Λ D hD Th
  have hvol : volH (k + m) ((fun u : E (k + m) => Th • u) '' D) = volH (k + m) D :=
    volH_smul_image hAkm hIkm Th D
  have hmem : ((eeq ▸ (blk (k + r) (m - r) 1 RS : PO ((k + r) + (m - r)) 1)) : PO (k + m) 1)
      ∈ Λ.map (MulAut.conj Th).toMonoidHom :=
    Subgroup.mem_map.mpr
      ⟨blk k m 1 S, hb, (MulAut.conj_apply Th (blk k m 1 S)).trans hconj⟩
  refine ⟨k + r, m - r, eeq, Λ.map (MulAut.conj Th).toMonoidHom,
    (fun u : E (k + m) => Th • u) '' D, RS, by omega, by omega, hdisc', hFD, hvol, hmem,
    hRSfree, hRSleS, ?_⟩
  -- the separation transfer
  intro c' hc'mem hcomm hres hc'ne
  set c'' : PO ((k + r) + (m - r)) 1 := (eeq.symm ▸ c' : PO ((k + r) + (m - r)) 1) with hc''def
  have hc''cast : (eeq ▸ c'' : PO (k + m) 1) = c' := by
    rw [hc''def]; exact cast_symm_cast_po eeq c'
  have hres'' : resStd (k + r) (m - r) c'' = 1 := by rw [hc''def]; exact hres
  -- the element of `Λ` corresponding to `c'`
  obtain ⟨c, hcΛ, hcmap⟩ := Subgroup.mem_map.mp hc'mem
  have hceq : Th * c * Th⁻¹ = c' := (MulAut.conj_apply Th c).symm.trans hcmap
  have hc''central : c'' ∈ Subgroup.centralizer
      ({blk (k + r) (m - r) 1 RS} : Set (PO ((k + r) + (m - r)) 1)) := by
    rw [Subgroup.mem_centralizer_iff] at hcomm ⊢
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    have h1 := hcomm (eeq ▸ (blk (k + r) (m - r) 1 RS) : PO (k + m) 1) (Set.mem_singleton _)
    have h2 : (eeq ▸ ((blk (k + r) (m - r) 1 RS : PO ((k + r) + (m - r)) 1) * c'') :
          PO (k + m) 1)
        = (eeq ▸ (c'' * (blk (k + r) (m - r) 1 RS : PO ((k + r) + (m - r)) 1)) :
          PO (k + m) 1) := by
      rw [cast_mul_po, cast_mul_po, hc''cast]
      exact h1
    exact cast_po_injective eeq h2
  have hstab'' : c'' ∈ SetStabStd (k + r) (m - r) :=
    centralizer_mem_SetStabStd (k + r) (m - r) hAr hIr hAn hIn RS hRSfree c'' hc''central
  have hc''blk : c'' = blk (k + r) (m - r) 1 (nrmStd (k + r) (m - r) c'') := by
    have hform := rhd_stab_form (k + r) (m - r) hAr hIr hAn hIn hstab''
    calc c'' = blk (k + r) (m - r) (resStd (k + r) (m - r) c'')
            (nrmStd (k + r) (m - r) c'') := hform
      _ = blk (k + r) (m - r) 1 (nrmStd (k + r) (m - r) c'') := by rw [hres'']
  -- `c'` fixes the transported stratum pointwise
  have hfixnew : ∀ y : E (k + m),
      (∀ i : Fin (k + m), k + r ≤ (i : ℕ) → y.ofLp i = 0) → c' • y = y := by
    intro y hy
    have hy' : ∀ i : Fin ((k + r) + (m - r)), (k + r) ≤ (i : ℕ) → (eeq.symm ▸ y).ofLp i = 0 := by
      intro i hi
      rw [cast_applyX']
      exact hy (finCongr eeq i) (by rw [cast_fin_valX]; exact hi)
    have hfixblk : (blk (k + r) (m - r) 1 (nrmStd (k + r) (m - r) c'')) • (eeq.symm ▸ y)
        = (eeq.symm ▸ y) := by
      rw [← coordEmb_tanC_of_tail_zero hy']
      rw [rhd_blk_smul_coordEmb (k + r) (m - r) hAr hIr hAn hIn 1
        (nrmStd (k + r) (m - r) c'') (tanC (k + r) (m - r) (eeq.symm ▸ y))]
      rw [(POBasic.ofProp hAr).one_smul]
    calc c' • y = (eeq ▸ c'') • y := by rw [hc''cast]
      _ = (eeq ▸ c'') • (eeq ▸ (eeq.symm ▸ y)) := by rw [cast_symm_cast]
      _ = eeq ▸ (c'' • (eeq.symm ▸ y)) := by rw [cast_smul_po]
      _ = eeq ▸ (eeq.symm ▸ y) := by rw [hc''blk, hfixblk]
      _ = y := cast_symm_cast eeq y
  -- `c` fixes the standard stratum pointwise
  have hcfix : ∀ v : E k, c • coordEmb k m v = coordEmb k m v := by
    intro v
    have hThx : Th • coordEmb k m v = coordEmb k m v := by
      rw [hTdef, blk_smul_linBlk k m hAk hAkm hIkm PS (coordEmb k m v), linBlk_coordEmb]
    have hy0 : ∀ i : Fin (k + m), k + r ≤ (i : ℕ) → (coordEmb k m v).ofLp i = 0 :=
      fun i _ => coordEmb_ofLp_ge v i (by have := i.isLt; omega)
    have hceqx : c = Th⁻¹ * c' * Th := by rw [← hceq]; group
    calc c • coordEmb k m v = (Th⁻¹ * c' * Th) • coordEmb k m v := by rw [hceqx]
      _ = Th⁻¹ • (c' • (Th • coordEmb k m v)) := by rw [hP.mul_smul, hP.mul_smul]
      _ = Th⁻¹ • (c' • coordEmb k m v) := by rw [hThx]
      _ = Th⁻¹ • coordEmb k m v := by rw [hfixnew _ hy0]
      _ = coordEmb k m v := by
            conv_lhs => rw [← hThx]
            rw [← hP.mul_smul, inv_mul_cancel, hP.one_smul]
  have hcne : c ≠ 1 := by
    intro h1
    apply hc'ne
    rw [← hceq, h1]
    group
  have hsepN : rotN S ≤ rotN (nrmStd k m c) := hsep c hcΛ hcfix hcne
  have hcstab : c ∈ SetStabStd k m := by
    rw [rhd_mem_stab_iff]
    intro y
    constructor
    · rintro ⟨v, rfl⟩
      exact ⟨v, (hcfix v).symm⟩
    · rintro ⟨v, hv⟩
      refine ⟨v, ?_⟩
      have h1 : c • y = c • coordEmb k m v := by rw [← hv, hcfix v]
      have h2 : c⁻¹ • (c • y) = c⁻¹ • (c • coordEmb k m v) := by rw [h1]
      have h3 : y = coordEmb k m v := by
        rw [← hP.mul_smul, inv_mul_cancel, hP.one_smul, ← hP.mul_smul, inv_mul_cancel,
          hP.one_smul] at h2
        exact h2
      exact h3.symm
  have hcblk : c = blk k m 1 (nrmStd k m c) := by
    have hform := rhd_stab_form k m hAk hIk hAkm hIkm hcstab
    have hres1 : resStd k m c = 1 := by
      apply (POBasic.ofProp hAk).faithful
      intro v
      have h1 := rhd_resStd_smul_coordEmb k m hAk hIk hAkm hIkm hcstab v
      rw [hcfix v] at h1
      exact (rhd_coordEmb_injective k m h1).symm
    calc c = blk k m (resStd k m c) (nrmStd k m c) := hform
      _ = blk k m 1 (nrmStd k m c) := by rw [hres1]
  -- the block decomposition of `c'`
  set N : E m ≃ₗᵢ[ℝ] E m := nrmStd k m c with hNdef
  set B : E m ≃ₗᵢ[ℝ] E m := PS * N * PS⁻¹ with hBdef
  set N' : E (m - r) ≃ₗᵢ[ℝ] E (m - r) := nrmStd (k + r) (m - r) c'' with hN'def
  have hcblk' : c = blk k m 1 N := by rw [hcblk, hNdef]
  have hBmul : Th * blk k m 1 N * Th⁻¹ = blk k m 1 B := by
    rw [hblkmul N, hBdef]
  have hBv : ∀ y : E m, B y = vblk r hr N' y := by
    refine (strataAdaptFold k r m hr eeq N' B).mp ?_
    intro x
    have h1 : c' • x = linBlk k m B x := by
      rw [← hceq, hcblk', hBmul]
      rw [blk_smul_linBlk k m hAk hAkm hIkm B x]
    have h2 : c' • x
        = (eeq ▸ (linBlk (k + r) (m - r) N' (eeq.symm ▸ x)) : E (k + m)) := by
      calc c' • x = (eeq ▸ c'') • x := by rw [hc''cast]
        _ = (eeq ▸ c'') • (eeq ▸ (eeq.symm ▸ x)) := by rw [cast_symm_cast]
        _ = eeq ▸ (c'' • (eeq.symm ▸ x)) := by rw [cast_smul_po]
        _ = eeq ▸ ((blk (k + r) (m - r) 1 N') • (eeq.symm ▸ x)) := by rw [hc''blk, hN'def]
        _ = eeq ▸ (linBlk (k + r) (m - r) N' (eeq.symm ▸ x)) := by
              rw [blk_smul_linBlk (k + r) (m - r) hAr hAn hIn N' (eeq.symm ▸ x)]
    exact h2.symm.trans h1
  have hrotNN' : rotN N = rotN N' := by
    have h1 : rotN N = rotN B := by
      rw [hBdef]; exact (rhd_rotN_conj PS N).symm
    exact h1.trans (strataAdaptRotN r m hr N' B hBv).symm
  have hNc : N = nrmStd k m c := hNdef
  have hN'c : N' = nrmStd (k + r) (m - r) c'' := hN'def
  rw [hNc, hN'c] at hrotNN'
  calc rotN RS ≤ rotN S := hRSleS
    _ ≤ rotN (nrmStd k m c) := hsepN
    _ = rotN (nrmStd (k + r) (m - r) c'') := hrotNN'

end Work.Mostow
