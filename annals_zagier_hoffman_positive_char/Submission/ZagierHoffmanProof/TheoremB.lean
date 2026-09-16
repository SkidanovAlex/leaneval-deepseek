import Submission.ZagierHoffmanProof.Step3Tuple
import Submission.ZagierHoffmanProof.AmbZeta
import Submission.ZagierHoffmanProof.Step3General
import Submission.ZagierHoffmanProof.AmbKEquiv
import Submission.ZagierHoffmanProof.ACMplDatum
import Submission.ZagierHoffmanProof.CountRank
import Submission.Commons.FieldTheory.RatFunc.num_mul_prod_erase_denom
import Submission.Commons.FieldTheory.RatFunc.num_mul_prod_erase_denom_ne_zero

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
open Polynomial PowerSeries Finset
open scoped WithZero Topology Classical

/-!
# Theorem B: the linear independence of the MZV's of `𝒯0 w` (Dac §5.3)

This file performs the induction on the weight of Dac's §5.3, in the *tuple-indexed* form
`P'(w)` discussed in `PLAN.md` (§ SESSION 345 §0): for every finite injective family of
exponent tuples of common weight `w` (all entries `< q`), the MZV's `ζ_A 𝔰` are
`RatFunc F`-independent.
-/

namespace ZagierHoffmanPositiveChar

universe u

variable {F : Type u} [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-! ## §1. Tuple-list helpers -/

lemma tupleList_get_fst {r : ℕ} (𝔰 : Fin r → ℕ+) (k : Fin (tupleList F 𝔰).length) :
    ((tupleList F 𝔰).get k).1 = ((𝔰 (Fin.cast (tupleList_length F 𝔰) k)) : ℕ) := by
  rw [tupleList_get]

lemma tupleList_reverse_get_fst {r : ℕ} (𝔰 : Fin r → ℕ+)
    (j : Fin ((tupleList F 𝔰).reverse).length) :
    (((tupleList F 𝔰).reverse).get j).1 = ((𝔰 (Fin.cast (tupleList_length F 𝔰)
      ⟨(tupleList F 𝔰).length - 1 - (j : ℕ), by
        have hj : (j : ℕ) < (tupleList F 𝔰).length :=
          lt_of_lt_of_eq j.isLt (List.length_reverse)
        omega⟩)) : ℕ) := by
  have hj : (j : ℕ) < (tupleList F 𝔰).length :=
    lt_of_lt_of_eq j.isLt (List.length_reverse)
  rw [List.get_reverse' (tupleList F 𝔰) j (by omega), tupleList_get_fst]

/-- `tmWeight` of the reversed list. -/
lemma tmWeight_reverse (l : List (ℕ × Polynomial (Ambient F))) :
    tmWeight (K := Ambient F) l.reverse = tmWeight (K := Ambient F) l := by
  simp only [tmWeight]
  rw [List.map_reverse, List.sum_reverse]

lemma tmWeight_tupleListP {r : ℕ} (𝔰 : Fin r → ℕ+) :
    tmWeight (K := Ambient F) (tupleListP F 𝔰) = ∑ j : Fin r, (𝔰 j : ℕ) := by
  rw [tmWeight, tupleListP, List.map_ofFn, List.sum_ofFn]
  rfl

/-- **The bridge for a `Fin`-indexed exponent tuple** (Dac (4.2) / AT09 (2.4.1), trivial
character): `π̃^{w}·𝓛(𝔰;1)(θ) = ζ_A(𝔰)` inside the ambient field. -/
theorem bridge_tuple {r : ℕ} (𝔰 : Fin r → ℕ+) (hr : 0 < r) (h𝔰 : EntriesOK F 𝔰) :
    (ambPiTilde F) ^ (∑ j : Fin r, (𝔰 j : ℕ))
      * evalSeriesGen (tmL (Nat.card F) (ambOmega F) (tupleListP F 𝔰)) (ambTheta F)
      = ambInfHom F (ζ_A F 𝔰) := by
  have hlen : ((tupleList F 𝔰).reverse).length = r := by
    rw [List.length_reverse, tupleList_length F 𝔰]
  have hmem : ∀ j : Fin ((tupleList F 𝔰).reverse).length, (j : ℕ) < r := by
    intro j
    exact lt_of_lt_of_eq (lt_of_lt_of_eq j.isLt (List.length_reverse))
      (tupleList_length F 𝔰)
  let 𝔰' : Fin ((tupleList F 𝔰).reverse).length → ℕ+ := fun j => 𝔰 ⟨j.1, hmem j⟩
  have hpos : ∀ j : Fin ((tupleList F 𝔰).reverse).length,
      1 ≤ (((tupleList F 𝔰).reverse).get j).1 := by
    intro j
    rw [tupleList_reverse_get_fst]
    exact (𝔰 _).pos
  have htwo : ∀ j : Fin ((tupleList F 𝔰).reverse).length,
      (((tupleList F 𝔰).reverse).get j).2 = 1 := by
    intro j
    have hj : (j : ℕ) < (tupleList F 𝔰).length :=
      lt_of_lt_of_eq j.isLt (List.length_reverse)
    rw [List.get_reverse' (tupleList F 𝔰) j (by omega), tupleList_get]
  have hne : (tupleList F 𝔰).reverse ≠ [] := by
    intro h
    have h1 : ((tupleList F 𝔰).reverse).length = 0 := by rw [h]; rfl
    rw [List.length_reverse, tupleList_length] at h1
    omega
  have h𝔰' : ∀ j : Fin ((tupleList F 𝔰).reverse).length,
      ((𝔰' j : ℕ)) = (((tupleList F 𝔰).reverse).get (Fin.rev j)).1 := by
    intro j
    show ((𝔰 ⟨j.1, hmem j⟩ : ℕ)) = _
    rw [tupleList_reverse_get_fst]
    congr 2
    apply Fin.ext
    simp only [Fin.val_cast, Fin.val_rev]
    have hj := hmem j
    have hj2 : (j : ℕ) < ((tupleList F 𝔰).reverse).length := j.isLt
    have hrev : ((tupleList F 𝔰).reverse).length = (tupleList F 𝔰).length := List.length_reverse
    omega
  have h𝔰'q : ∀ j : Fin ((tupleList F 𝔰).reverse).length, ((𝔰' j : ℕ)) ≤ Nat.card F := by
    intro j
    exact h𝔰 ⟨j.1, hmem j⟩
  have hb := bridge F ((tupleList F 𝔰).reverse) hne htwo hpos 𝔰' h𝔰' h𝔰'q
  have hsum : (∑ j : Fin ((tupleList F 𝔰).reverse).length, ((𝔰' j : ℕ)))
      = ∑ j : Fin r, ((𝔰 j : ℕ)) := by
    refine Fintype.sum_equiv (Fin.castOrderIso hlen).toEquiv
      (fun j : Fin ((tupleList F 𝔰).reverse).length => ((𝔰' j : ℕ)))
      (fun j : Fin r => ((𝔰 j : ℕ))) (fun j => ?_)
    rfl
  have hzeta : ζ_A F 𝔰' = ζ_A F 𝔰 := by
    refine ζ_A_eq_of_reindex F hlen 𝔰' 𝔰 (fun i => ?_)
    exact Subtype.ext rfl
  have htmL : tmL (Nat.card F) (ambOmega F) (tupleListP F 𝔰)
      = atLrGen (Nat.card F) (ambOmega F) ((tupleList F 𝔰).reverse) := by
    rw [tmL_eq_atLrGen_suffixList]
    simp only [suffixList, tmCoe_tupleListP]
  rw [hsum, hzeta] at hb
  rw [htmL, hb]

/-! ## §2. The exponent tuple read off a prefix list -/

section TmTup

variable {S : Finset (List (ℕ × Polynomial (Ambient F)))}

/-- The exponent tuple read off a prefix list `t ∈ tmI S`. -/
noncomputable def tmTup (hpos : ∀ s ∈ S, ∀ x ∈ s, 1 ≤ x.1) (t : ↥(tmI S)) :
    Σ r : ℕ, Fin r → ℕ+ :=
  ⟨t.1.length, fun j => ⟨(t.1.get j).1, by
    obtain ⟨s, hs, hx⟩ := mem_tmI_entry F t.2 (List.get_mem t.1 j)
    exact hpos s hs _ hx⟩⟩

lemma tmTup_weight (hpos : ∀ s ∈ S, ∀ x ∈ s, 1 ≤ x.1) (t : ↥(tmI S)) :
    (∑ j : Fin (tmTup (S := S) hpos t).1, ((tmTup (S := S) hpos t).2 j : ℕ))
      = tmWeight (K := Ambient F) t.1 := by
  rw [tmWeight]
  conv_rhs => rw [← List.ofFn_get (t.1), List.map_ofFn, List.sum_ofFn]
  rfl

lemma tmTup_entries_two (htwo : ∀ s ∈ S, ∀ x ∈ s, x.2 = 1) (hpos : ∀ s ∈ S, ∀ x ∈ s, 1 ≤ x.1)
    (t : ↥(tmI S)) :
    tupleListP F (tmTup (S := S) hpos t).2 = t.1 := by
  rw [tupleListP]
  conv_rhs => rw [← List.ofFn_get (t.1)]
  congr 1
  funext j
  have h2 : (1 : Polynomial (Ambient F)) = (t.1.get j).2 := by
    obtain ⟨s, hs, hx⟩ := mem_tmI_entry F t.2 (List.get_mem t.1 j)
    rw [htwo s hs _ hx]
  exact Prod.ext rfl h2

lemma tmTup_lt (hlt : ∀ s ∈ S, ∀ x ∈ s, x.1 < Nat.card F) (hpos : ∀ s ∈ S, ∀ x ∈ s, 1 ≤ x.1)
    (t : ↥(tmI S)) (j : Fin (tmTup (S := S) hpos t).1) :
    ((tmTup (S := S) hpos t).2 j : ℕ) < Nat.card F := by
  show (t.1.get j).1 < Nat.card F
  obtain ⟨s, hs, hx⟩ := mem_tmI_entry F t.2 (List.get_mem t.1 j)
  exact hlt s hs _ hx

lemma tmTup_inj (htwo : ∀ s ∈ S, ∀ x ∈ s, x.2 = 1) (hpos : ∀ s ∈ S, ∀ x ∈ s, 1 ≤ x.1)
    {t t' : ↥(tmI S)}
    (h : tupleListP F (tmTup (S := S) hpos t).2
      = tupleListP F (tmTup (S := S) hpos t').2) : t = t' := by
  refine Subtype.ext ?_
  rw [← tmTup_entries_two (F := F) (htwo := htwo) (hpos := hpos) (S := S)]
  rw [← tmTup_entries_two (F := F) (htwo := htwo) (hpos := hpos) (S := S)]
  exact h

end TmTup

/-! ## §3. Step 1 of the proof: a `K`-linear relation between MZV's transfers to the `L`-series
side (the input `f_∅(θ) = 0` of `LinearIndependence.linear_independence`). -/

section LD

/-- ★★★ **Step 1 of Dac §5.3**: a `RatFunc F`-linear relation between MZV's of a common weight
transports, via the bridge `bridge_tuple`, to the vanishing of the corresponding `L`-series
relation inside the ambient field. -/
theorem lseries_relation_vanishing {ι : Type*} [Fintype ι]
    (𝔰 : ι → Σ r : ℕ, Fin r → ℕ+)
    (hpos : ∀ i, 0 < (𝔰 i).1)
    (hq : ∀ i j, ((𝔰 i).2 j : ℕ) ≤ Nat.card F)
    (w : ℕ) (hwt : ∀ i, ∑ j : Fin (𝔰 i).1, ((𝔰 i).2 j : ℕ) = w)
    (c : ι → RatFunc F)
    (h : ∑ i, c i • ζ_A F ((𝔰 i).2) = 0) :
    ∑ i, ambKHomAmb F (c i)
        * evalSeriesGen (tmL (Nat.card F) (ambOmega F) (tupleListP F ((𝔰 i).2)))
            (ambTheta F) = 0 := by
  classical
  have hrel := ambInfHom_zeta_A_relation F (fun i => (𝔰 i).1) hpos
    (fun i => (𝔰 i).2) c h
  have hb : ∀ i, (ambPiTilde F) ^ w
      * evalSeriesGen (tmL (Nat.card F) (ambOmega F) (tupleListP F ((𝔰 i).2)))
          (ambTheta F) = ambInfHom F (ζ_A F ((𝔰 i).2)) := by
    intro i
    have h1 := bridge_tuple (F := F) (𝔰 i).2 (hpos i) (hq i)
    rwa [hwt i] at h1
  have hmain : (∑ i, ambKHomAmb F (c i)
        * evalSeriesGen (tmL (Nat.card F) (ambOmega F) (tupleListP F ((𝔰 i).2)))
            (ambTheta F))
      = ((ambPiTilde F) ^ w)⁻¹
        * ∑ i, ambKHomAmb F (c i) * ambInfHom F (ζ_A F ((𝔰 i).2)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← hb i]
    have h1 : ((ambPiTilde F) ^ w)⁻¹ * (ambKHomAmb F (c i)
          * ((ambPiTilde F) ^ w * evalSeriesGen
              (tmL (Nat.card F) (ambOmega F) (tupleListP F ((𝔰 i).2))) (ambTheta F)))
        = ((ambPiTilde F) ^ w)⁻¹ * (ambPiTilde F) ^ w
          * (ambKHomAmb F (c i) * evalSeriesGen
              (tmL (Nat.card F) (ambOmega F) (tupleListP F ((𝔰 i).2))) (ambTheta F)) := by
      ring
    rw [h1, inv_mul_cancel₀ (pow_ne_zero _ (ambPiTilde_ne_zero F)), one_mul]
  rw [hmain]
  have hzero : (∑ i, ambKHomAmb F (c i) * ambInfHom F (ζ_A F ((𝔰 i).2))) = 0 := by
    simpa only [ambKHomAmb_apply] using hrel
  rw [hzero, mul_zero]

end LD

/-! ## §4. Step 2's (LW) transport: independence of the `L`-series values from independence of the
MZV's, via the bridge. -/

section Transport

/-- ★★★ **The (LW) transport**: if the MZV's `ζ_A 𝔰_i` are `RatFunc F`-independent then the
corresponding `L`-series values are `ambK F`-independent. -/
theorem linearIndependent_of_bridge {ι : Type*} [Fintype ι] [DecidableEq ι]
    (𝔰 : ι → Σ r : ℕ, Fin r → ℕ+)
    (hpos : ∀ i, 0 < (𝔰 i).1) (hq : ∀ i j, ((𝔰 i).2 j : ℕ) ≤ Nat.card F)
    (w' : ℕ) (hwt : ∀ i, ∑ j : Fin (𝔰 i).1, ((𝔰 i).2 j : ℕ) = w')
    (h : LinearIndependent (RatFunc F) (fun i => ζ_A F ((𝔰 i).2))) :
    LinearIndependent (ambK F)
      (fun i => evalSeriesGen (tmL (Nat.card F) (ambOmega F) (tupleListP F ((𝔰 i).2)))
        (ambTheta F)) := by
  classical
  have hbr : ∀ i, (ambPiTilde F) ^ w'
      * evalSeriesGen (tmL (Nat.card F) (ambOmega F) (tupleListP F ((𝔰 i).2)))
          (ambTheta F) = ambInfHom F (ζ_A F ((𝔰 i).2)) := by
    intro i
    have h1 := bridge_tuple (F := F) (𝔰 i).2 (hpos i) (hq i)
    rwa [hwt i] at h1
  have hkey : ∀ (f g : ι → ↥(ambK F)),
      (∑ i, f i • evalSeriesGen (tmL (Nat.card F) (ambOmega F) (tupleListP F ((𝔰 i).2)))
          (ambTheta F))
        = ∑ i, g i • evalSeriesGen (tmL (Nat.card F) (ambOmega F) (tupleListP F ((𝔰 i).2)))
          (ambTheta F) →
      ∑ i, (f i : Ambient F) * ambInfHom F (ζ_A F ((𝔰 i).2))
        = ∑ i, (g i : Ambient F) * ambInfHom F (ζ_A F ((𝔰 i).2)) := by
    intro f g hfg
    have hfr : ∀ i, (f i : Ambient F)
        * ambInfHom F (ζ_A F ((𝔰 i).2))
        = (ambPiTilde F) ^ w' * ((f i : Ambient F) * evalSeriesGen
            (tmL (Nat.card F) (ambOmega F) (tupleListP F ((𝔰 i).2))) (ambTheta F)) := by
      intro i
      rw [← hbr i]
      ring
    have hgr : ∀ i, (g i : Ambient F)
        * ambInfHom F (ζ_A F ((𝔰 i).2))
        = (ambPiTilde F) ^ w' * ((g i : Ambient F) * evalSeriesGen
            (tmL (Nat.card F) (ambOmega F) (tupleListP F ((𝔰 i).2))) (ambTheta F)) := by
      intro i
      rw [← hbr i]
      ring
    have h3 : (∑ i, f i • evalSeriesGen
          (tmL (Nat.card F) (ambOmega F) (tupleListP F ((𝔰 i).2))) (ambTheta F))
        = ∑ i, (f i : Ambient F) * evalSeriesGen
            (tmL (Nat.card F) (ambOmega F) (tupleListP F ((𝔰 i).2))) (ambTheta F) := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Algebra.smul_def]
      rfl
    have h4 : (∑ i, g i • evalSeriesGen
          (tmL (Nat.card F) (ambOmega F) (tupleListP F ((𝔰 i).2))) (ambTheta F))
        = ∑ i, (g i : Ambient F) * evalSeriesGen
            (tmL (Nat.card F) (ambOmega F) (tupleListP F ((𝔰 i).2))) (ambTheta F) := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Algebra.smul_def]
      rfl
    have h1 : (∑ i, (f i : Ambient F) * ambInfHom F (ζ_A F ((𝔰 i).2)))
        = (ambPiTilde F) ^ w'
          * ∑ i, (f i : Ambient F) * evalSeriesGen
              (tmL (Nat.card F) (ambOmega F) (tupleListP F ((𝔰 i).2))) (ambTheta F) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => hfr i)
    have h2 : (∑ i, (g i : Ambient F) * ambInfHom F (ζ_A F ((𝔰 i).2)))
        = (ambPiTilde F) ^ w'
          * ∑ i, (g i : Ambient F) * evalSeriesGen
              (tmL (Nat.card F) (ambOmega F) (tupleListP F ((𝔰 i).2))) (ambTheta F) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => hgr i)
    rw [h1, ← h3, hfg, h4, ← h2]
  rw [Fintype.linearIndependent_iffₛ] at h ⊢
  intro f g hfg i
  have himg := hkey f g hfg
  have hzeta : ∑ i, ((ambKEquiv F).symm (f i)) • ζ_A F ((𝔰 i).2)
      = ∑ i, ((ambKEquiv F).symm (g i)) • ζ_A F ((𝔰 i).2) := by
    apply ambInfHom_injective
    have h1 : ambInfHom F (∑ i, ((ambKEquiv F).symm (f i)) • ζ_A F ((𝔰 i).2))
        = ∑ i, (f i : Ambient F) * ambInfHom F (ζ_A F ((𝔰 i).2)) := by
      rw [map_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Algebra.smul_def, map_mul]
      congr 1
      have hcoe : (algebraMap (RatFunc F) (RatFunc.CompletionAtInfty F))
          ((ambKEquiv F).symm (f i))
          = (((ambKEquiv F).symm (f i) : RatFunc F) : RatFunc.CompletionAtInfty F) := rfl
      rw [hcoe, ambInfHom_coe, ambKHomAmb_apply]
      simp
    have h2 : ambInfHom F (∑ i, ((ambKEquiv F).symm (g i)) • ζ_A F ((𝔰 i).2))
        = ∑ i, (g i : Ambient F) * ambInfHom F (ζ_A F ((𝔰 i).2)) := by
      rw [map_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Algebra.smul_def, map_mul]
      congr 1
      have hcoe : (algebraMap (RatFunc F) (RatFunc.CompletionAtInfty F))
          ((ambKEquiv F).symm (g i))
          = (((ambKEquiv F).symm (g i) : RatFunc F) : RatFunc.CompletionAtInfty F) := rfl
      rw [hcoe, ambInfHom_coe, ambKHomAmb_apply]
      simp
    rw [h1, h2, himg]
  have hci := h _ _ hzeta i
  rw [← RingEquiv.apply_symm_apply (ambKEquiv F) (f i), hci]
  exact RingEquiv.apply_symm_apply (ambKEquiv F) (g i)

end Transport

/-! ## §5. The tuple-indexed induction -/

section Aux

/-- `RatFunc.num` and `RatFunc.denom` clear denominators. -/
lemma num_eq_mul_denom (x : RatFunc F) :
    (RatFunc.num x : RatFunc F) = x * (RatFunc.denom x : RatFunc F) := by
  have h := RatFunc.num_div_denom x
  rw [div_eq_iff (RatFunc.algebraMap_ne_zero (RatFunc.denom_ne_zero x))] at h
  exact h

/-- The evaluation of the `ambCoeff`-mapped polynomial is the image of the rational function. -/
lemma eval_map_ambCoeff (p : Polynomial F) :
    (Polynomial.eval (ambTheta F) (p.map (ambCoeff F)))
      = ambKHomAmb F (algebraMap (Polynomial F) (RatFunc F) p) := by
  rw [Polynomial.eval_map, ambKHomAmb_eq, ambKEquiv_apply, ambKHom_algebraMap, ambKPolyHom_apply]
  rfl

lemma ambKHomAmb_injective : Function.Injective (ambKHomAmb F) :=
  fun x y h => (ambKEquiv F).injective (Subtype.ext h)

/-- The coefficient function attached to a family of exponent tuples. -/
noncomputable def mkCf {ι : Type*} (T : Finset ι) (𝔰 : ι → Σ r : ℕ, Fin r → ℕ+)
    (A : ι → Polynomial (Ambient F)) :
    List (ℕ × Polynomial (Ambient F)) → Polynomial (Ambient F) :=
  fun t => if h : ∃ i ∈ T, tupleListP F ((𝔰 i).2) = t then A (Classical.choose h) else 0

lemma mkCf_apply {ι : Type*} {T : Finset ι} {𝔰 : ι → Σ r : ℕ, Fin r → ℕ+}
    {A : ι → Polynomial (Ambient F)}
    (hlinj : ∀ i j, tupleListP F ((𝔰 i).2) = tupleListP F ((𝔰 j).2) → i = j)
    {i : ι} (hi : i ∈ T) : mkCf (F := F) T 𝔰 A (tupleListP F ((𝔰 i).2)) = A i := by
  have hex : ∃ j ∈ T, tupleListP F ((𝔰 j).2) = tupleListP F ((𝔰 i).2) := ⟨i, hi, rfl⟩
  have hch : A (Classical.choose hex) = A i := by
    refine congrArg A ?_
    obtain ⟨hj, heq⟩ := Classical.choose_spec hex
    exact hlinj _ i heq
  rw [mkCf, dif_pos hex]
  exact hch

end Aux

/-! ## §5. The tuple-indexed induction -/

section Main

/-- The tuple-indexed induction statement of Dac §5.3 (see `PLAN.md`, SESSION 345 §0): for every
finite injective family of exponent tuples of common weight `w` with all entries `< q`, the MZV's
`ζ_A 𝔰` are `RatFunc F`-independent. -/
def TupleInd (F : Type u) [Field F] [Finite F] [DecidableEq (RatFunc F)]
    (ι : Type u) (w : ℕ) : Prop :=
  ∀ (𝔰 : ι → Σ r : ℕ, Fin r → ℕ+),
    (∀ i j, ((𝔰 i).2 j : ℕ) < Nat.card F) →
    (∀ i, ∑ j : Fin (𝔰 i).1, ((𝔰 i).2 j : ℕ) = w) →
    (∀ i j, tupleListP F ((𝔰 i).2) = tupleListP F ((𝔰 j).2) → i = j) →
    LinearIndependent (RatFunc F) (fun i => ζ_A F ((𝔰 i).2))

end Main

/-! ## §6. The induction step -/

section Step

/-- The exponent tuple of a prefix list has `ζ_A ≠ 0` on the dropped tail. -/
lemma zeta_suffixExp_ne_zero {w : ℕ} (D : MZVD F w)
    {s : List (ℕ × Polynomial (Ambient F))} (hs : s ∈ D.S) {k : ℕ} (hkl : k < s.length) :
    ζ_A F (suffixExp F (s.drop k) (D.drop_pos hs k)) ≠ 0 := by
  refine zeta_entries_ne_zero F (List.length_pos_iff.mpr
    (suffixList_ne_nil F (drop_ne_nil_of_lt_length hkl))) _ (fun j => ?_)
  rw [suffixExp_apply]
  exact suffixList_mem_le F (D.drop_le hs k) _ (List.get_mem _ _)

/-- ★★★ **The induction step of Dac §5.3**: a nontrivial `RatFunc F`-linear relation between the
MZV's of a family of exponent tuples of common weight `w` is impossible, given the
(tuple-indexed) induction hypothesis at all smaller weights. -/
theorem tuple_independent_step (w : ℕ) (hw : 1 ≤ w)
    (ih : ∀ (w' : ℕ), w' < w → 1 ≤ w' → ∀ (ι : Type u) [Fintype ι] [DecidableEq ι],
      TupleInd (F := F) ι w')
    {ι : Type*} [Fintype ι] [DecidableEq ι] (𝔰 : ι → Σ r : ℕ, Fin r → ℕ+)
    (hlt : ∀ i j, ((𝔰 i).2 j : ℕ) < Nat.card F)
    (hwt : ∀ i, ∑ j : Fin (𝔰 i).1, ((𝔰 i).2 j : ℕ) = w)
    (hlinj : ∀ i j, tupleListP F ((𝔰 i).2) = tupleListP F ((𝔰 j).2) → i = j)
    (c : ι → RatFunc F) (hc : ∑ i, c i • ζ_A F ((𝔰 i).2) = 0) :
    ∀ i, c i = 0 := by
  classical
  intro i₀
  by_contra hi₀
  -- the tuples are nonempty
  have hpos_i : ∀ i, 0 < (𝔰 i).1 := by
    intro i
    rcases Nat.eq_zero_or_pos (𝔰 i).1 with h | h
    · exfalso
      haveI : IsEmpty (Fin (𝔰 i).1) := ⟨fun j => by have := j.isLt; omega⟩
      have h2 : (∑ j : Fin (𝔰 i).1, ((𝔰 i).2 j : ℕ)) = 0 := by
        rw [Finset.univ_eq_empty]
        exact Finset.sum_empty
      have h3 := hwt i
      rw [h2] at h3
      omega
    · exact h
  -- §A. the support and the clearing of denominators
  set T : Finset ι := Finset.univ.filter (fun i => c i ≠ 0) with hT
  have hTm : ∀ i, i ∈ T ↔ c i ≠ 0 := fun i => by
    simp only [hT, Finset.mem_filter, Finset.mem_univ, true_and]
  have hi₀T : i₀ ∈ T := (hTm i₀).mpr hi₀
  have hTne : T.Nonempty := ⟨i₀, hi₀T⟩
  have hout : ∀ i, i ∉ T → c i = 0 := fun i hi => by
    by_contra h; exact hi ((hTm i).mpr h)
  set Dp : Polynomial F := ∏ j ∈ T, RatFunc.denom (c j) with hDp
  set a : ι → Polynomial F :=
    fun i => RatFunc.num (c i) * ∏ j ∈ T.erase i, RatFunc.denom (c j) with ha
  have ha_eq : ∀ i ∈ T, (a i : RatFunc F) = c i * (Dp : RatFunc F) := by
    intro i hi
    simp only [ha, hDp]
    exact Commons.FieldTheory.RatFunc.num_mul_prod_erase_denom T c hi
  have ha_ne : ∀ i ∈ T, a i ≠ 0 := by
    intro i hi
    simp only [ha]
    exact Commons.FieldTheory.RatFunc.num_mul_prod_erase_denom_ne_zero T c hi ((hTm i).mp hi)
  have houta : ∀ i, i ∉ T → a i = 0 := by
    intro i hi
    simp only [ha]
    rw [hout i hi, RatFunc.num_zero, zero_mul]
  have hTrel : (∑ i ∈ T, (a i : RatFunc F) • ζ_A F ((𝔰 i).2)) = 0 := by
    have hcrel : (∑ i ∈ T, c i • ζ_A F ((𝔰 i).2)) = 0 := by
      refine (Finset.sum_subset (Finset.subset_univ T) ?_).trans hc
      intro i _ hi
      rw [hout i hi, zero_smul]
    have h1 : (∑ i ∈ T, (a i : RatFunc F) • ζ_A F ((𝔰 i).2))
        = (Dp : RatFunc F) • ∑ i ∈ T, c i • ζ_A F ((𝔰 i).2) := by
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl (fun i hi => ?_)
      rw [ha_eq i hi, mul_smul, smul_comm]
    rw [h1, hcrel, smul_zero]
  -- §B. the Ambient coefficients
  set A : ι → Polynomial (Ambient F) := fun i => (a i).map (ambCoeff F) with hA
  have hA_ne : ∀ i ∈ T, A i ≠ 0 := by
    intro i hi
    simp only [hA]
    exact (Polynomial.map_ne_zero_iff (ambCoeff F).injective).mpr (ha_ne i hi)
  have hA_coeff : ∀ i m, (A i).coeff m ∈ ambA F 0 := by
    intro i m
    simp only [hA, Polynomial.coeff_map]
    exact mem_ambA_zero_of_mem_ambF (ambCoeff_mem_ambF F _)
  have hA_eval : ∀ i, (A i).eval (ambTheta F)
      = ambKHomAmb F (algebraMap (Polynomial F) (RatFunc F) (a i)) := by
    intro i
    simp only [hA]
    exact eval_map_ambCoeff (a i)
  have hA_out : ∀ i, i ∉ T → A i = 0 := by
    intro i hi
    simp only [hA, houta i hi, Polynomial.map_zero]
  have hA_frob : ∀ i, frobTwist (R := Ambient F) (p := Nat.card F) 1
      ((A i : Polynomial (Ambient F)) : PowerSeries (Ambient F))
      = ((A i : Polynomial (Ambient F)) : PowerSeries (Ambient F)) := by
    intro i
    ext n
    rw [frobTwist_coeff, pow_one, Polynomial.coeff_coe]
    simp only [hA, Polynomial.coeff_map]
    exact (mem_ambF_iff F _).mp (ambCoeff_mem_ambF F _)
  -- §C. the tuple set, the coefficient function and the datum
  set S : Finset (List (ℕ × Polynomial (Ambient F))) :=
    T.image (fun i => tupleListP F ((𝔰 i).2)) with hS
  have hS_inj : Set.InjOn (fun i => tupleListP F ((𝔰 i).2)) (T : Set ι) :=
    fun i _ j _ h => hlinj i j h
  have hS_two : ∀ s ∈ S, ∀ x ∈ s, x.2 = 1 := by
    intro s hs x hx
    simp only [hS, Finset.mem_image] at hs
    obtain ⟨i, -, rfl⟩ := hs
    obtain ⟨j, rfl⟩ := List.mem_iff_get.mp hx
    rw [tupleListP_get]
  have hS_pos : ∀ s ∈ S, ∀ x ∈ s, 1 ≤ x.1 := by
    intro s hs x hx
    simp only [hS, Finset.mem_image] at hs
    obtain ⟨i, -, rfl⟩ := hs
    obtain ⟨j, rfl⟩ := List.mem_iff_get.mp hx
    rw [tupleListP_get]
    exact ((𝔰 i).2 _).pos
  have hS_lt : ∀ s ∈ S, ∀ x ∈ s, x.1 < Nat.card F := by
    intro s hs x hx
    simp only [hS, Finset.mem_image] at hs
    obtain ⟨i, -, rfl⟩ := hs
    obtain ⟨j, rfl⟩ := List.mem_iff_get.mp hx
    rw [tupleListP_get]
    exact hlt i _
  have hS_weight : ∀ s ∈ S, tmWeight s = w := by
    intro s hs
    simp only [hS, Finset.mem_image] at hs
    obtain ⟨i, -, rfl⟩ := hs
    rw [tmWeight_tupleListP]
    exact hwt i
  have hS_ne : ∀ s ∈ S, s ≠ [] := by
    intro s hs hnil
    have h1 := hS_weight s hs
    rw [hnil, tmWeight_nil] at h1
    omega
  have hcfmem : ∀ s ∈ S, ∀ m, (mkCf (F := F) T 𝔰 A s).coeff m ∈ ambA F 0 := by
    intro s hs m
    simp only [hS, Finset.mem_image] at hs
    obtain ⟨i, hi, rfl⟩ := hs
    rw [mkCf_apply hlinj hi]
    exact hA_coeff i m
  have hcf_frob : ∀ s ∈ S, frobTwist (R := Ambient F) (p := Nat.card F) 1
      (((mkCf (F := F) T 𝔰 A s : Polynomial (Ambient F))) : PowerSeries (Ambient F))
      = ((mkCf (F := F) T 𝔰 A s : Polynomial (Ambient F)) : PowerSeries (Ambient F)) := by
    intro s hs
    simp only [hS, Finset.mem_image] at hs
    obtain ⟨i, hi, rfl⟩ := hs
    rw [mkCf_apply hlinj hi]
    exact hA_frob i
  have hQmem : ∀ s ∈ S, ∀ y ∈ s, ∀ m, (y.2).coeff m ∈ ambA F 0 := by
    intro s hs y hy m
    rw [hS_two s hs y hy]
    rcases eq_or_ne m 0 with rfl | hm
    · rw [Polynomial.coeff_one, if_pos rfl]
      exact ambA_one_mem F 0
    · rw [Polynomial.coeff_one, if_neg hm]
      exact ambA_zero_mem 0
  have h0mem : ([] : List (ℕ × Polynomial (Ambient F))) ∈ tmI S := by
    refine mem_tmI.mpr ⟨tupleListP F ((𝔰 i₀).2),
      by simp only [hS, Finset.mem_image]; exact ⟨i₀, hi₀T, rfl⟩, 0, ?_, by simp⟩
    rw [List.length_pos_iff]
    exact hS_ne _ (by simp only [hS, Finset.mem_image]; exact ⟨i₀, hi₀T, rfl⟩)
  have hsm : ∀ s ∈ S, ∀ y ∈ s,
      GIsSmall ambGamma ((ambOmega F) ^ y.1 * (y.2 : PowerSeries (Ambient F))) := by
    intro s hs y hy
    rw [hS_two s hs y hy, Polynomial.coe_one, mul_one]
    have h1 : 1 ≤ y.1 := hS_pos s hs y hy
    rw [show y.1 = (y.1 - 1) + 1 by omega]
    exact (gIsSmall_ambOmega F).pow_add_one ambGamma_le_one (y.1 - 1)
  have hSse : ∀ s ∈ S, ∀ y ∈ s,
      GSuperEntire ambGamma (y.2 : PowerSeries (Ambient F)) := by
    intro s hs y hy
    rw [hS_two s hs y hy, Polynomial.coe_one]
    exact GSuperEntire.one ambGamma
  let hDD : MZVD F w :=
    ⟨S, hS_two, hS_pos, (fun s hs x hx => le_of_lt (hS_lt s hs x hx)), hS_weight⟩
  have hAcoeff : ∀ i j m,
      (tmAOpt (K := Ambient F) (Nat.card F) (ambTheta F) w S (mkCf (F := F) T 𝔰 A) i j).coeff m
        ∈ ambA F 0 :=
    tmAOpt_coeff_mem_ambA0 (F := F) w hQmem hcfmem
  -- §D. the (LD) input
  have hrel_all : (∑ i, (a i : RatFunc F) • ζ_A F ((𝔰 i).2)) = 0 := by
    refine (Finset.sum_subset (Finset.subset_univ T) ?_).symm.trans hTrel
    intro i _ hiT
    rw [houta i hiT]
    simp
  have hvan := lseries_relation_vanishing (F := F) 𝔰 hpos_i (fun i j => le_of_lt (hlt i j)) w hwt
    (fun i => (a i : RatFunc F)) hrel_all
  have hLD : (∑ i ∈ T, (A i).eval (ambTheta F)
      * evalSeriesGen (tmL (Nat.card F) (ambOmega F) (tupleListP F ((𝔰 i).2))) (ambTheta F)) = 0 := by
    rw [← hvan]
    refine (Finset.sum_subset (Finset.subset_univ T) ?_).trans ?_
    · intro i _ hiT
      rw [hA_out i hiT, Polynomial.eval_zero, zero_mul]
    · refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [hA_eval i]
      rfl
  have hstep1 : evalSeriesGen (∑ s ∈ S, (mkCf (F := F) T 𝔰 A s : PowerSeries (Ambient F))
        * tmL (Nat.card F) (ambOmega F) s) (ambTheta F)
      = ∑ s ∈ S, (mkCf (F := F) T 𝔰 A s).eval (ambTheta F)
          * evalSeriesGen (tmL (Nat.card F) (ambOmega F) s) (ambTheta F) := by
    rw [evalSeriesGen_finset_sum ambGamma_lt_one gammaArchimedean_rat S
      (fun s => (mkCf (F := F) T 𝔰 A s : PowerSeries (Ambient F))
        * tmL (Nat.card F) (ambOmega F) s)
      (fun s hs => GSuperEntire.mul ambGamma_le_one
        (GSuperEntire.polynomial ambGamma_pos ambGamma_le_one _)
        (gSuperEntire_tmL_unit F s (hS_two s hs) (hS_pos s hs))) (ambTheta F)]
    refine Finset.sum_congr rfl (fun s hs => ?_)
    rw [evalSeriesGen_mul ambGamma_lt_one gammaArchimedean_rat
      (GSuperEntire.polynomial ambGamma_pos ambGamma_le_one _)
      (gSuperEntire_tmL_unit F s (hS_two s hs) (hS_pos s hs)) (ambTheta F),
      evalSeriesGen_polynomial]
  have hstep2 : (∑ s ∈ S, (mkCf (F := F) T 𝔰 A s).eval (ambTheta F)
        * evalSeriesGen (tmL (Nat.card F) (ambOmega F) s) (ambTheta F))
      = ∑ i ∈ T, (A i).eval (ambTheta F)
          * evalSeriesGen (tmL (Nat.card F) (ambOmega F) (tupleListP F ((𝔰 i).2)))
              (ambTheta F) := by
    rw [hS, Finset.sum_image hS_inj]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [mkCf_apply hlinj hi]
  have hval : evalSeriesGen (tmF (Nat.card F) (ambOmega F) w S (mkCf (F := F) T 𝔰 A)
        ([] : List (ℕ × Polynomial (Ambient F)))) (ambTheta F)
      + (0 : Polynomial (Ambient F)).eval (ambTheta F) = 0 := by
    rw [Polynomial.eval_zero, add_zero, tmF_nil]
    exact hstep1.trans (hstep2.trans hLD)
  have ha0 : frobTwist (R := Ambient F) (p := Nat.card F) 1
      ((0 : Polynomial (Ambient F)) : PowerSeries (Ambient F))
      = ((0 : Polynomial (Ambient F)) : PowerSeries (Ambient F)) := by
    rw [Polynomial.coe_zero]
    ext n
    simp [frobTwist_coeff]
  -- §E. the (LW) input
  have hLW : ∀ w' : ℕ, w' ≤ w → LinearIndependent (ambK F)
      (fun t : {t : ↥(tmI S) // tmWeight (K := Ambient F) t.1 = w'} =>
        evalSeriesGen (tmL (Nat.card F) (ambOmega F) t.1.1) (ambTheta F)) := by
    intro w' hw'
    rcases eq_or_ne w' 0 with hw'0 | hw'0
    · subst w'
      have hnil : ∀ t : ↥(tmI S), tmWeight (K := Ambient F) t.1 = 0 → t.1 = [] := by
        intro t ht
        obtain ⟨s, hs, k, hk, htk⟩ := mem_tmI.mp t.2
        rw [← htk] at ht
        have h1 : (s.take k).length ≤ tmWeight (K := Ambient F) (s.take k) := by
          rw [tmWeight]
          conv_lhs => rw [← List.length_map (f := Prod.fst)]
          refine List.length_le_sum_of_one_le _ (fun x hx => ?_)
          rw [List.mem_map] at hx
          obtain ⟨y, hy, rfl⟩ := hx
          exact hS_pos s hs y (List.mem_of_mem_take hy)
        have h2 : (s.take k).length = k := by
          rw [List.length_take, Nat.min_eq_left (le_of_lt hk)]
        rw [h2] at h1
        have h3 : k = 0 := by omega
        rw [← htk, h3, List.take_zero]
      have hsub : Subsingleton {t : ↥(tmI S) // tmWeight (K := Ambient F) t.1 = 0} :=
        ⟨fun a b => Subtype.ext (Subtype.ext ((hnil a.1 a.2).trans (hnil b.1 b.2).symm))⟩
      rw [Fintype.linearIndependent_iffₛ]
      intro f g hfg i
      have huniv : (Finset.univ : Finset {t : ↥(tmI S) // tmWeight (K := Ambient F) t.1 = 0})
          = {i} :=
        Finset.eq_singleton_iff_unique_mem.mpr
          ⟨Finset.mem_univ i, fun b _ => Subsingleton.elim b i⟩
      have e1 : (∑ x : {t : ↥(tmI S) // tmWeight (K := Ambient F) t.1 = 0},
              f x • evalSeriesGen (tmL (Nat.card F) (ambOmega F) x.1.1) (ambTheta F))
            = f i • evalSeriesGen (tmL (Nat.card F) (ambOmega F) i.1.1) (ambTheta F) := by
        rw [huniv, Finset.sum_singleton]
      have e2 : (∑ x : {t : ↥(tmI S) // tmWeight (K := Ambient F) t.1 = 0},
              g x • evalSeriesGen (tmL (Nat.card F) (ambOmega F) x.1.1) (ambTheta F))
            = g i • evalSeriesGen (tmL (Nat.card F) (ambOmega F) i.1.1) (ambTheta F) := by
        rw [huniv, Finset.sum_singleton]
      have h1 : f i • evalSeriesGen (tmL (Nat.card F) (ambOmega F) i.1.1) (ambTheta F)
          = g i • evalSeriesGen (tmL (Nat.card F) (ambOmega F) i.1.1) (ambTheta F) := by
        rw [← e1, ← e2]
        exact hfg
      have hi0 : i.1.1 = [] := hnil i.1 i.2
      rw [hi0, tmL_nil, evalSeriesGen_one] at h1
      exact Subtype.ext (by simpa [Algebra.smul_def] using h1)
    · rcases eq_or_lt_of_le hw' with hww | hw'lt
      · subst w'
        have hempty : ∀ t : {t : ↥(tmI S) // tmWeight (K := Ambient F) t.1 = w}, False := by
          intro t
          obtain ⟨s, hs, k, hk, htk⟩ := mem_tmI.mp t.1.2
          have h1 : tmWeight (K := Ambient F) s = w := hS_weight s hs
          have h2 : tmWeight (K := Ambient F) t.1 = w := t.2
          have h3 : tmWeight (K := Ambient F) s = tmWeight (K := Ambient F) (s.take k)
              + tmWeight (K := Ambient F) (s.drop k) :=
            tmWeight_take_add_drop (K := Ambient F) s k
          have h4 : 1 ≤ tmWeight (K := Ambient F) (s.drop k) := by
            rw [tmWeight]
            refine le_trans ?_ (List.length_le_sum_of_one_le _ (fun x hx => ?_))
            · rw [List.length_map]
              exact List.length_pos_iff.mpr (drop_ne_nil_of_lt_length hk)
            · rw [List.mem_map] at hx
              obtain ⟨y, hy, rfl⟩ := hx
              exact hS_pos s hs y (List.mem_of_mem_drop hy)
          rw [← htk] at h2
          omega
        rw [Fintype.linearIndependent_iffₛ]
        exact fun f g _ t => (hempty t).elim
      · have hw'1 : 1 ≤ w' := by omega
        let 𝔰' : {t : ↥(tmI S) // tmWeight (K := Ambient F) t.1 = w'} → Σ r : ℕ, Fin r → ℕ+ :=
          fun t => tmTup (S := S) hS_pos t.1
        have hpos' : ∀ t, 0 < (𝔰' t).1 := by
          intro t
          show 0 < (t.1.1).length
          rw [List.length_pos_iff]
          intro hnil
          have h2 : tmWeight (K := Ambient F) t.1 = w' := t.2
          rw [show (t.1 : List (ℕ × Polynomial (Ambient F))) = [] from hnil, tmWeight_nil] at h2
          omega
        have hlt' : ∀ t j, ((𝔰' t).2 j : ℕ) < Nat.card F :=
          fun t j => tmTup_lt (S := S) hS_lt hS_pos t.1 j
        have hq' : ∀ t j, ((𝔰' t).2 j : ℕ) ≤ Nat.card F := fun t j => le_of_lt (hlt' t j)
        have hwt' : ∀ t, ∑ j : Fin (𝔰' t).1, ((𝔰' t).2 j : ℕ) = w' := by
          intro t
          rw [tmTup_weight (S := S) hS_pos t.1]
          exact t.2
        have hlinj' : ∀ t t', tupleListP F ((𝔰' t).2) = tupleListP F ((𝔰' t').2) → t = t' :=
          fun t t' h => Subtype.ext (tmTup_inj (S := S) hS_two hS_pos h)
        have hLI := (ih w' hw'lt hw'1 _ :
          TupleInd (F := F) {t : ↥(tmI S) // tmWeight (K := Ambient F) t.1 = w'} w')
          (fun t => tmTup (S := S) hS_pos t.1)
          (fun t j => tmTup_lt (S := S) hS_lt hS_pos t.1 j)
          (fun t => by rw [tmTup_weight (S := S) hS_pos t.1]; exact t.2)
          (fun t t' h => Subtype.ext (tmTup_inj (S := S) hS_two hS_pos h))
        have hLI2 := linearIndependent_of_bridge (F := F) 𝔰' hpos' hq' w' hwt' hLI
        have hfun : (fun t : {t : ↥(tmI S) // tmWeight (K := Ambient F) t.1 = w'} =>
              evalSeriesGen (tmL (Nat.card F) (ambOmega F) (tupleListP F ((𝔰' t).2)))
                (ambTheta F))
            = (fun t : {t : ↥(tmI S) // tmWeight (K := Ambient F) t.1 = w'} =>
              evalSeriesGen (tmL (Nat.card F) (ambOmega F) t.1.1) (ambTheta F)) := by
          funext t
          rw [tmTup_entries_two (F := F) (htwo := hS_two) (hpos := hS_pos) t.1]
        rwa [hfun] at hLI2
  -- §F. Dac's §3.3
  have hfK : ∀ t' : ↥(tmI S),
      evalSeriesGen (tmF (Nat.card F) (ambOmega F) w S (mkCf (F := F) T 𝔰 A) t'.1)
        (ambTheta F) ∈ ambK F :=
    linear_independence (F := F) ambGamma_pos ambGamma_lt_one gammaArchimedean_rat
      (two_le_ambCard F) (gIsSmall_ambOmega F) (gSuperEntire_ambOmega F)
      (coeff_zero_ambOmega F) (fun k hk => evalSeriesGen_ambOmega_frobenius_orbit F hk)
      (ambOmega_functional F) hS_weight hcf_frob hsm hSse hS_pos hQmem hS_ne h0mem hAcoeff
      ha0 hval hLW
  -- §G. the endgame
  rcases lt_or_ge T.card 2 with hT2 | hT2
  · -- the support has at most one element
    have hT1 : T.card = 1 := by
      have := Finset.card_pos.mpr hTne
      omega
    obtain ⟨i₁, hi₁⟩ := Finset.card_eq_one.mp hT1
    have hrel1 : (a i₁ : RatFunc F) • ζ_A F ((𝔰 i₁).2) = 0 := by
      have h := hTrel
      rw [hi₁, Finset.sum_singleton] at h
      exact h
    have ha1 : a i₁ ≠ 0 := ha_ne i₁ (by rw [hi₁]; exact Finset.mem_singleton_self i₁)
    have hz1 : ζ_A F ((𝔰 i₁).2) = 0 := by
      apply ambInfHom_injective
      rw [map_zero]
      have h3 := congrArg (ambInfHom F) hrel1
      rw [map_zero, Algebra.smul_def, map_mul] at h3
      have hcoe : ambInfHom F (algebraMap (RatFunc F) (RatFunc.CompletionAtInfty F) (a i₁))
          = ambKHomAmb F (a i₁) := by
        rw [show (algebraMap (RatFunc F) (RatFunc.CompletionAtInfty F) (a i₁))
            = ((a i₁ : RatFunc F) : RatFunc.CompletionAtInfty F) from rfl, ambInfHom_coe]
      rw [hcoe] at h3
      rcases mul_eq_zero.mp h3 with h | h
      · have h4 : (a i₁ : RatFunc F) = 0 :=
          ambKHomAmb_injective (show ambKHomAmb F (a i₁) = ambKHomAmb F 0 by simpa using h)
        exact absurd (RatFunc.algebraMap_injective (K := F) (by rw [map_zero]; exact h4)) ha1
      · exact h
    exact zeta_entries_ne_zero F (hpos_i i₁) ((𝔰 i₁).2)
      (fun j => le_of_lt (hlt i₁ j)) hz1
  · -- the support has at least two elements
    obtain ⟨u, hu, v, hv, huv, hK⟩ := exists_pair_maxAgreeT (𝔰 := 𝔰) (T := T) hT2
    have hlinjT : ∀ i j, i ∈ T → j ∈ T →
        tupleListP F ((𝔰 i).2) = tupleListP F ((𝔰 j).2) → i = j :=
      fun i j _ _ h => hlinj i j h
    have tupAgree_symm : ∀ {r₁ r₂ : ℕ} (𝔰₁ : Fin r₁ → ℕ+) (𝔰₂ : Fin r₂ → ℕ+),
        tupAgree 𝔰₁ 𝔰₂ = tupAgree 𝔰₂ 𝔰₁ := by
      intro r₁ r₂ 𝔰₁ 𝔰₂
      refine le_antisymm ?_ ?_
      · refine le_tupAgree (𝔰₁ := 𝔰₂) (𝔰₂ := 𝔰₁) (fun l hl => (tupAgree_spec 𝔰₁ 𝔰₂ l hl).symm) ?_
        rw [max_comm]
        exact tupAgree_le 𝔰₁ 𝔰₂
      · refine le_tupAgree (𝔰₁ := 𝔰₁) (𝔰₂ := 𝔰₂) (fun l hl => (tupAgree_spec 𝔰₂ 𝔰₁ l hl).symm) ?_
        rw [max_comm]
        exact tupAgree_le 𝔰₂ 𝔰₁
    have huniqL : tupleListP F ((𝔰 u).2) ≠ tupleListP F ((𝔰 v).2) :=
      fun h => huv (hlinj u v h)
    have huniqGen : ∀ (x y : ι), x ∈ T → y ∈ T → x ≠ y →
        maxAgreeT T 𝔰 = tupAgree (𝔰 x).2 (𝔰 y).2 →
        ∀ z ∈ T, (tupleListP F ((𝔰 z).2)).take (maxAgreeT T 𝔰 + 1)
          = (tupleListP F ((𝔰 x).2)).take (maxAgreeT T 𝔰 + 1) → z = x :=
      fun x y hx hy hxy hxyK => unique_take_of_maxAgreeT (F := F) (𝔰 := 𝔰) (T := T)
        hx hy hxy hlinjT hxyK
    have hdiv : ∀ (x y : ι), x ∈ T → y ∈ T → x ≠ y →
        maxAgreeT T 𝔰 = tupAgree (𝔰 x).2 (𝔰 y).2 → ∀ j : ℕ,
        maxAgreeT T 𝔰 + 1 ≤ j → j < (𝔰 x).1 → tupE (𝔰 x).2 j = Nat.card F - 1 := by
      intro x y hx hy hxy hxyK
      refine eq_pred_of_dvd (q := Nat.card F) (two_le_ambCard F) (r := (𝔰 x).1)
        (fun j hj => tupE_pos (𝔰 x).2 hj) (fun j hj => ?_)
        (fun j hj hjlt => ?_)
      · rw [tupE_of_lt (𝔰 x).2 hj]
        exact hlt x ⟨j, hj⟩
      · have hsx : tupleListP F ((𝔰 x).2) ∈ S := by
          simp only [hS, Finset.mem_image]; exact ⟨x, hx, rfl⟩
        have hlen : j < (tupleListP F ((𝔰 x).2)).length := by rwa [tupleListP_length]
        have huniqj : ∀ s ∈ S, s.take j = (tupleListP F ((𝔰 x).2)).take j →
            s = tupleListP F ((𝔰 x).2) := by
          intro s hs htake
          have h1 : s.take (maxAgreeT T 𝔰 + 1)
              = (tupleListP F ((𝔰 x).2)).take (maxAgreeT T 𝔰 + 1) := by
            rw [show s.take (maxAgreeT T 𝔰 + 1) = (s.take j).take (maxAgreeT T 𝔰 + 1) from by
              rw [List.take_take, Nat.min_eq_left hj],
              htake,
              show ((tupleListP F ((𝔰 x).2)).take j).take (maxAgreeT T 𝔰 + 1)
                = (tupleListP F ((𝔰 x).2)).take (maxAgreeT T 𝔰 + 1) from by
              rw [List.take_take, Nat.min_eq_left hj]]
          simp only [hS, Finset.mem_image] at hs
          obtain ⟨z, hz, rfl⟩ := hs
          have hz' := huniqGen x y hx hy hxy hxyK z hz h1
          rw [hz']
        have hζ : ζ_A F (suffixExp F ((tupleListP F ((𝔰 x).2)).drop j)
            (hDD.drop_pos hsx j)) ≠ 0 := zeta_suffixExp_ne_zero (F := F) hDD hsx hlen
        have hcf0 : (mkCf (F := F) T 𝔰 A (tupleListP F ((𝔰 x).2))).eval (ambTheta F) ≠ 0 := by
          rw [mkCf_apply hlinj hx, hA_eval x]
          intro h0
          have h4 : (a x : RatFunc F) = 0 :=
            ambKHomAmb_injective (show ambKHomAmb F (algebraMap (Polynomial F) (RatFunc F) (a x))
              = ambKHomAmb F 0 by simpa using h0)
          exact ha_ne x hx (RatFunc.algebraMap_injective (K := F)
            (by rw [map_zero]; exact h4))
        have hfKj : evalSeriesGen (tmF (Nat.card F) (ambOmega F) w S (mkCf (F := F) T 𝔰 A)
            ((tupleListP F ((𝔰 x).2)).take j)) (ambTheta F) ∈ ambK F :=
          hfK ⟨(tupleListP F ((𝔰 x).2)).take j, mem_tmI.mpr ⟨_, hsx, j, hlen, rfl⟩⟩
        have hf0j : evalSeriesGen (tmF (Nat.card F) (ambOmega F) w S (mkCf (F := F) T 𝔰 A)
            ((tupleListP F ((𝔰 x).2)).take j)) (ambTheta F) ≠ 0 := by
          have hsingle := evalSeriesGen_tmF_gen (F := F) (w := w) (S := S)
            (cf := mkCf (F := F) T 𝔰 A) hsx (le_of_lt hlen) huniqj rfl
            (gSuperEntire_tmL_drop hDD hsx j)
          rw [hsingle]
          refine mul_ne_zero hcf0 ?_
          intro hL0
          have hbr := bridge F (suffixList F ((tupleListP F ((𝔰 x).2)).drop j))
            (suffixList_ne_nil F (drop_ne_nil_of_lt_length hlen))
            (fun l => suffixList_mem_two F (hDD.drop_two hsx j) _ (List.get_mem _ l))
            (fun l => suffixList_mem_pos F (hDD.drop_pos hsx j) _ (List.get_mem _ l))
            (suffixExp F ((tupleListP F ((𝔰 x).2)).drop j) (hDD.drop_pos hsx j))
            (fun _ => rfl)
            (fun l => suffixList_mem_le F (hDD.drop_le hsx j) _
              (List.get_mem _ (Fin.rev l)))
          rw [← tmL_eq_atLrGen_suffixList] at hbr
          rw [hL0, mul_zero] at hbr
          refine hζ (ambInfHom_injective F ?_)
          simpa using hbr.symm
        have hd := dvd_pred_weight_gen (F := F) hw hDD hsx hlen huniqj rfl
          (fun m => hcfmem _ hsx m) hcf0 hζ hfKj hf0j
        rw [show w - tmWeight (K := Ambient F) ((tupleListP F ((𝔰 x).2)).take j)
              = tmWeight (K := Ambient F) ((tupleListP F ((𝔰 x).2)).drop j) from by
            have h := tmWeight_take_add_drop (K := Ambient F) (tupleListP F ((𝔰 x).2)) j
            have h2 := hS_weight _ hsx
            omega,
          tmWeight_drop_tupleListP (F := F) ((𝔰 x).2) j] at hd
        exact hd
    have hagree : ∀ l, l < maxAgreeT T 𝔰 → tupE (𝔰 u).2 l = tupE (𝔰 v).2 l :=
      tupE_eq_of_maxAgreeT (𝔰 := 𝔰) (T := T) (u := u) (v := v) hK
    have hnotagree : ¬ ∀ l, l < maxAgreeT T 𝔰 + 1 → tupE (𝔰 u).2 l = tupE (𝔰 v).2 l :=
      not_tupE_eq_succ_of_maxAgreeT (F := F) (𝔰 := 𝔰) (T := T) (u := u) (v := v)
        hu hv huv huniqL hK
    exact false_of_tupE (q := Nat.card F) (w := w) (K := maxAgreeT T 𝔰)
      (two_le_ambCard F) (fun j => hlt u j) (fun j => hlt v j) (hwt u) (hwt v)
      hagree hnotagree (fun j hj => hdiv u v hu hv huv hK j (by omega))
      (fun j hj => hdiv v u hv hu (Ne.symm huv)
        (hK.trans (tupAgree_symm (𝔰 u).2 (𝔰 v).2)) j (by omega))

end Step

/-! ## §7. The tuple-indexed induction, and Theorem B -/

section Final

/-- **Dac §5.3, the tuple-indexed induction**: for every `w ≥ 1` and every finite injective family
of exponent tuples of common weight `w` with all entries `< q`, the MZV's are `RatFunc F`-linearly
independent. -/
theorem tuple_independent : ∀ (w : ℕ), 1 ≤ w → ∀ (ι : Type u) [Fintype ι] [DecidableEq ι],
    TupleInd (F := F) ι w := by
  intro w
  refine Nat.strong_induction_on w ?_
  intro w ih hw ι _ _ 𝔰 hlt hwt hlinj
  have key : ∀ (c : ι → RatFunc F), (∑ i, c i • ζ_A F ((𝔰 i).2) = 0) → ∀ i, c i = 0 :=
    fun c hc => tuple_independent_step (F := F) w hw ih 𝔰 hlt hwt hlinj c hc
  rw [Fintype.linearIndependent_iffₛ]
  intro c g hcg i
  have hd : (∑ i, (c i - g i) • ζ_A F ((𝔰 i).2)) = 0 := by
    have h1 : (∑ i, (c i - g i) • ζ_A F ((𝔰 i).2))
        = ∑ i, (c i • ζ_A F ((𝔰 i).2) - g i • ζ_A F ((𝔰 i).2)) :=
      Finset.sum_congr rfl (fun i _ => sub_smul (c i) (g i) _)
    rw [h1, Finset.sum_sub_distrib, hcg, sub_self]
  exact sub_eq_zero.mp (key (fun i => c i - g i) hd i)

/-- **Theorem B**, in the ambient form: the MZV's of `𝒯0 w` are `RatFunc F`-linearly independent,
and consequently `|𝒯0 w| ≤ dim_K 𝒵 w`. -/
theorem theorem_B_amb (w : ℕ+) :
    LinearIndependent (RatFunc F) (Subtype.val : 𝒯0 F w → RatFunc.CompletionAtInfty F) ∧
    Module.rank (RatFunc F) (𝒵 F w) ≥ Set.ncard (𝒯0 F w) := by
  have hw : 1 ≤ (w : ℕ) := w.2
  haveI : Finite {x : RatFunc.CompletionAtInfty F // x ∈ 𝒯0 F (w : ℕ)} :=
    finiteT0 F (w : ℕ) hw
  haveI : Fintype {x : RatFunc.CompletionAtInfty F // x ∈ 𝒯0 F (w : ℕ)} :=
    Fintype.ofFinite _
  have hli : LinearIndependent (RatFunc F)
      (fun v : {x : RatFunc.CompletionAtInfty F // x ∈ 𝒯0 F w} =>
        ζ_A F (T0exp F (w : ℕ) hw v)) :=
    (tuple_independent (F := F) (w : ℕ) hw
      {x : RatFunc.CompletionAtInfty F // x ∈ 𝒯0 F w})
      (fun v => ⟨(T0list F (w : ℕ) hw v).length, T0exp F (w : ℕ) hw v⟩)
      (fun v j => by
        show (T0exp F (w : ℕ) hw v j : ℕ) < Nat.card F
        rw [T0exp_val F (w : ℕ) hw v j]
        exact T0tuple_lt F (w : ℕ) hw v ⟨j.val, by
          simpa [T0list_length F (w : ℕ) hw v] using j.isLt⟩)
      (fun v => T0exp_weight F (w : ℕ) hw v)
      (fun v v' hv => T0exp_listP_injective F hw hv)
  have hval : (fun v : {x : RatFunc.CompletionAtInfty F // x ∈ 𝒯0 F w} =>
        ζ_A F (T0exp F (w : ℕ) hw v))
      = (fun v : {x : RatFunc.CompletionAtInfty F // x ∈ 𝒯0 F w} => v.val) :=
    funext (fun v => T0exp_zeta F (w : ℕ) hw v)
  rw [hval] at hli
  exact ⟨hli, rank_ge_ncard_T0_of_linearIndependent F hw hli⟩

end Final

end ZagierHoffmanPositiveChar
