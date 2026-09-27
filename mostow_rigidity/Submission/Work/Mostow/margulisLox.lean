import Mathlib
import Submission.Mostow.HLDefs
import Submission.Work.Mostow.Hyper
import Submission.Work.Mostow.BaryBase
import Submission.Work.Mostow.poAux
import Submission.Work.Mostow.BoostTransitive
import Submission.Work.Mostow.margulisPair
import Submission.Work.Mostow.margulisCuspDefs
import Submission.Work.Mostow.finite_nearStab
import Submission.Work.Mostow.mlDefs
import Submission.Work.Mostow.mlPres
import Submission.Work.Mostow.loxPairInv
import Submission.Work.Mostow.loxPairConj
import Submission.Work.Mostow.loxPairTwoSet
import Submission.Work.Mostow.coeToO
import Submission.Work.Mostow.near1OfNearIdAtBall

/-!
# `Work.Mostow.margulisLox`

**Margulis' lemma, loxodromic form.**  For every `R` there is `η > 0` such that in any discrete
subgroup `Γ ≤ PO(n,1)`, if `a ∈ Γ` is loxodromic with fixed pair `{x,y}` and moves the unit ball
around a point `z` by less than `η`, then every `δ ∈ Γ` moving `z` by at most `R` preserves the
two-point set `{x,y}` setwise.

The proof: conjugate by a boost sending `z` to `0`, so that the sheet-preserving lift `ToO a` of the
conjugate `a'` of `a` is entrywise close to the identity (`near1OfNearIdAtBall`), while `ToO δ'` is
bounded (`Near1_ToO_of_hdist`).  The iterated commutators `ci a' δ' j` then have entrywise defect at
most `(1/2)^j b₀` (`toO_ci_shrink'`); they all stay in a bounded set, which meets `Γ'` in a finite
set (`finite_nearStab`), so the (finite) set of their lift matrices has a minimal entrywise defect,
which must be `0`: some `ci a' δ' j = 1` (`coeToO`).  Backwards induction over the recursion —
using that a loxodromic element permutes exactly one two-point set of the boundary
(`loxPairTwoSet`) — then gives that `δ'` preserves `{bd h⁻¹ x, bd h⁻¹ y}`, and conjugating back that
`δ` preserves `{x,y}`.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

noncomputable section

variable {n : ℕ}

/-- The induction step of the backward induction: if the commutator `[a,c]` of a loxodromic element
`a` (with fixed pair `x, y`) with `c` permutes the fixed pair, then `c` does. -/
lemma pres2_step (hA : POActionProp n) (hI : HypIsometryProp n) (hPS : PairStabProp n)
    {x y : E n} (hx : x ∈ Sph n) (hy : y ∈ Sph n) (hne : x ≠ y) {a c : PO n 1}
    (hax : bd a x = x) (hay : bd a y = y) (hL : LoxPair a⁻¹ x y)
    (hv : Pres2 (a * c * a⁻¹ * c⁻¹) x y) : Pres2 c x y := by
  have hv' : Pres2 (a * (c * (a⁻¹ * c⁻¹))) x y := by
    have h : a * (c * (a⁻¹ * c⁻¹)) = a * c * a⁻¹ * c⁻¹ := by group
    rw [h]; exact hv
  have ha : Pres2 a x y := Or.inl ⟨hax, hay⟩
  have h1 : Pres2 (c * (a⁻¹ * c⁻¹)) x y := ML.pres2_of_mul_left hA hx hy hv' ha
  have h2 : Pres2 (c⁻¹ * (c * (a⁻¹ * c⁻¹)) * c) (bd c⁻¹ x) (bd c⁻¹ y) :=
    ML.pres2_conj hA hx hy (g := c * (a⁻¹ * c⁻¹)) (t := c) h1
  have h2' : Pres2 a⁻¹ (bd c⁻¹ x) (bd c⁻¹ y) := by
    have h : c⁻¹ * (c * (a⁻¹ * c⁻¹)) * c = a⁻¹ := by group
    rw [h] at h2
    exact h2
  have hcx : bd c⁻¹ x ∈ Sph n := hA.2.2.2.2.2.2.2.1 c⁻¹ x hx
  have hcy : bd c⁻¹ y ∈ Sph n := hA.2.2.2.2.2.2.2.1 c⁻¹ y hy
  have hcne : bd c⁻¹ x ≠ bd c⁻¹ y := by
    intro hcon
    exact hne (ML.bd_inj_sph hA c⁻¹ hx hy hcon)
  have h3 : Pres2 c⁻¹ x y := by
    unfold Pres2 at h2' ⊢
    exact loxPairTwoSet n hA hI hPS hL hcx hcy hcne h2'
  simpa using ML.pres2_inv hA hx hy h3

theorem margulisLox (n : ℕ) (hn : 2 ≤ n) (hA : POActionProp n) (hI : HypIsometryProp n)
    (hPS : PairStabProp n) : MargulisLoxProp n := by
  intro R
  by_cases hR : 0 ≤ R
  ·
    obtain ⟨Cb, hCbpos, hCb⟩ := near1OfNearIdAtBall n hA hI
    set b₀ : ℝ := Real.cosh R + 1 with hb₀def
    have hb₀pos : 0 < b₀ := by rw [hb₀def]; have := Real.cosh_pos R; linarith
    have hb₀nn : 0 ≤ b₀ := le_of_lt hb₀pos
    have hmsz : 0 < msz n := lt_of_lt_of_le zero_lt_one (one_le_msz n)
    set η : ℝ := min 1 (1 / (Cb * (8 * (msz n) ^ 3 * (1 + b₀) + 1))) with hηdef
    have hDpos : 0 < 8 * (msz n) ^ 3 * (1 + b₀) + 1 := by positivity
    have hηpos : 0 < η := by
      rw [hηdef]
      exact lt_min one_pos (by positivity)
    have hηle1 : η ≤ 1 := by rw [hηdef]; exact min_le_left _ _
    refine ⟨η, hηpos, ?_⟩
    intro Γ hdisc z x y a δ hLox hNear hshort
    -- conjugate so that `z = 0`
    obtain ⟨h, hhz⟩ := (BoostTransitive n hA).1 z
    set a' : PO n 1 := h⁻¹ * (a : PO n 1) * h with ha'def
    set δ' : PO n 1 := h⁻¹ * (δ : PO n 1) * h with hδ'def
    set Γ' : Subgroup (PO n 1) := Γ.map (MulAut.conj h⁻¹).toMonoidHom with hΓ'def
    have hdisc' : IsDiscrete (SetLike.coe Γ') := isDiscrete_map_conj hdisc h
    have hmemconj : ∀ γ ∈ Γ, h⁻¹ * γ * h ∈ Γ' := by
      intro γ hγ
      refine Subgroup.mem_map.mpr ⟨γ, hγ, ?_⟩
      show MulAut.conj h⁻¹ γ = h⁻¹ * γ * h
      rw [MulAut.conj_apply]
      group
    have hmem_a : a' ∈ Γ' := hmemconj _ a.2
    have hmem_δ : δ' ∈ Γ' := hmemconj _ δ.2
    have hxS : x ∈ Sph n := hLox.1
    have hyS : y ∈ Sph n := hLox.2.1
    have hLox' : LoxPair a' (bd h⁻¹ x) (bd h⁻¹ y) := loxPairConj n hA hI hLox h
    have hLox'inv : LoxPair a'⁻¹ (bd h⁻¹ x) (bd h⁻¹ y) := loxPairInv n hA hI hLox'
    have hx' : bd h⁻¹ x ∈ Sph n := hA.2.2.2.2.2.2.2.1 h⁻¹ x hxS
    have hy' : bd h⁻¹ y ∈ Sph n := hA.2.2.2.2.2.2.2.1 h⁻¹ y hyS
    have hne' : bd h⁻¹ x ≠ bd h⁻¹ y := hLox'.2.2.1
    -- `a'` is near the identity at the origin
    have hNear' : NearIdAt a' 0 η := by
      intro u hu
      have hdist_hu : hdist z (h • u) = hdist (0 : E n) u := by
        rw [← hhz]
        exact hI.2.2.2.2.2.2.1 h 0 u
      have h1 : hdist (h • u) ((a : PO n 1) • (h • u)) < η :=
        hNear (h • u) (by rw [hdist_hu]; exact hu)
      have h2 : (a : PO n 1) • (h • u) = h • (a' • u) := by
        have h3 : (a : PO n 1) * h = h * a' := by rw [ha'def]; group
        calc (a : PO n 1) • (h • u) = ((a : PO n 1) * h) • u :=
              (hA.2.2.2.2.1 (a : PO n 1) h u).symm
          _ = (h * a') • u := by rw [h3]
          _ = h • (a' • u) := hA.2.2.2.2.1 h a' u
      rw [h2, hI.2.2.2.2.2.2.1 h u (a' • u)] at h1
      exact h1
    -- `δ'` is `R`-short at the origin
    have hδ'_short : hdist (0 : E n) (δ' • (0 : E n)) ≤ R := by
      have h2 : (δ : PO n 1) • z = h • (δ' • (0 : E n)) := by
        have h3 : (δ : PO n 1) * h = h * δ' := by rw [hδ'def]; group
        calc (δ : PO n 1) • z = (δ : PO n 1) • (h • (0 : E n)) := by rw [hhz]
          _ = ((δ : PO n 1) * h) • (0 : E n) :=
              (hA.2.2.2.2.1 (δ : PO n 1) h (0 : E n)).symm
          _ = (h * δ') • (0 : E n) := by rw [h3]
          _ = h • (δ' • (0 : E n)) := hA.2.2.2.2.1 h δ' (0 : E n)
      calc hdist (0 : E n) (δ' • (0 : E n))
          = hdist (h • (0 : E n)) (h • (δ' • (0 : E n))) :=
            (hI.2.2.2.2.2.2.1 h 0 (δ' • 0)).symm
        _ = hdist z (h • (δ' • (0 : E n))) := by rw [hhz]
        _ = hdist z ((δ : PO n 1) • z) := by rw [← h2]
        _ ≤ R := hshort
    -- the entrywise bounds
    have ha₀ : Near1 (ToO a') (Cb * η) := hCb η hηpos hηle1 a' hNear'
    have hb₀near : Near1 (ToO δ') b₀ := by
      have h := Near1_ToO_of_hdist (n := n) (R := R) hR (g := δ') hδ'_short
      rw [hb₀def]
      exact h
    have hsmall_a : Cb * η ≤ 1 / (8 * (msz n) ^ 3 * (1 + b₀) + 1) := by
      have h : η ≤ 1 / (Cb * (8 * (msz n) ^ 3 * (1 + b₀) + 1)) := by
        rw [hηdef]
        exact min_le_right _ _
      have hCbD : Cb * (1 / (Cb * (8 * (msz n) ^ 3 * (1 + b₀) + 1)))
          = 1 / (8 * (msz n) ^ 3 * (1 + b₀) + 1) := by
        field_simp
      calc Cb * η ≤ Cb * (1 / (Cb * (8 * (msz n) ^ 3 * (1 + b₀) + 1))) :=
            mul_le_mul_of_nonneg_left h (le_of_lt hCbpos)
        _ = 1 / (8 * (msz n) ^ 3 * (1 + b₀) + 1) := hCbD
    have ha_le_one : Cb * η ≤ 1 := by
      have hD : (0 : ℝ) < 8 * (msz n) ^ 3 * (1 + b₀) + 1 := by positivity
      have hnn : (0 : ℝ) ≤ 8 * (msz n) ^ 3 * (1 + b₀) := by positivity
      refine le_trans hsmall_a ?_
      rw [div_le_one hD]
      linarith
    have h8 : 8 * (msz n) ^ 3 * (1 + b₀) * (Cb * η) ≤ 1 := by
      have h1 : 8 * (msz n) ^ 3 * (1 + b₀) * (1 / (8 * (msz n) ^ 3 * (1 + b₀) + 1)) < 1 := by
        have hD : (0 : ℝ) < 8 * (msz n) ^ 3 * (1 + b₀) + 1 := by positivity
        have hnn : (0 : ℝ) ≤ 8 * (msz n) ^ 3 * (1 + b₀) := by positivity
        rw [mul_one_div]
        rw [div_lt_one hD]
        linarith
      calc 8 * (msz n) ^ 3 * (1 + b₀) * (Cb * η)
          ≤ 8 * (msz n) ^ 3 * (1 + b₀) * (1 / (8 * (msz n) ^ 3 * (1 + b₀) + 1)) :=
            mul_le_mul_of_nonneg_left hsmall_a (by positivity)
        _ ≤ 1 := le_of_lt h1
    have hsmall : 2 * (msz n) ^ 3 * (Cb * η) * (1 + Cb * η) * (1 + b₀) ≤ 1 / 2 := by
      have h3 : 0 ≤ 2 * (msz n) ^ 3 * (Cb * η) * (1 + b₀) := by positivity
      have h4 : 1 + Cb * η ≤ 2 := by linarith
      calc 2 * (msz n) ^ 3 * (Cb * η) * (1 + Cb * η) * (1 + b₀)
          = (2 * (msz n) ^ 3 * (Cb * η) * (1 + b₀)) * (1 + Cb * η) := by ring
        _ ≤ (2 * (msz n) ^ 3 * (Cb * η) * (1 + b₀)) * 2 :=
            mul_le_mul_of_nonneg_left h4 h3
        _ = 4 * (msz n) ^ 3 * (Cb * η) * (1 + b₀) := by ring
        _ ≤ 1 / 2 := by linarith [h8]
    have hiter : ∀ j : ℕ, Near1 (ToO (ci a' δ' j)) ((1 / 2 : ℝ) ^ j * b₀) :=
      toO_ci_shrink' n hA ha₀ (by positivity) hb₀near hb₀nn (le_refl b₀) hb₀nn hsmall
    -- the sequence of commutators lies in a finite set
    have hc_mem : ∀ j : ℕ, ci a' δ' j ∈ Γ' := by
      intro j
      induction j with
      | zero => simpa using hmem_δ
      | succ j ih =>
        rw [ci_succ]
        exact Γ'.mul_mem (Γ'.mul_mem (Γ'.mul_mem hmem_a ih) (Γ'.inv_mem hmem_a)) (Γ'.inv_mem ih)
    set Cseq : ℕ → Γ' := fun j => ⟨ci a' δ' j, hc_mem j⟩ with hCseq
    have hCseq_val : ∀ j : ℕ, ((Cseq j : Γ') : PO n 1) = ci a' δ' j := fun j => rfl
    have hc_dist : ∀ j : ℕ,
        hdist (0 : E n) (((Cseq j : Γ') : PO n 1) • (0 : E n)) ≤ Real.arcosh (1 + b₀) := by
      intro j
      have hq : 0 ≤ (1 / 2 : ℝ) ^ j * b₀ := by positivity
      have hb : (1 / 2 : ℝ) ^ j * b₀ ≤ b₀ := by
        have h1 : (1 / 2 : ℝ) ^ j ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
        nlinarith [hb₀nn]
      have h := hdist_le_of_Near1_ToO hA hq (hiter j)
      refine le_trans h ?_
      exact (Real.arcosh_le_arcosh (by linarith) (by linarith)).mpr (by linarith)
    have hfin : {γ : Γ' | hdist (0 : E n) ((γ : PO n 1) • (0 : E n)) ≤
        Real.arcosh (1 + b₀)}.Finite :=
      finite_nearStab (POBasic.ofProp hA) (HypIsoData.ofProp hI) hdisc' _
    obtain ⟨i, -, j, -, hij, hcij⟩ := Set.Infinite.exists_ne_map_eq_of_mapsTo
      (s := (Set.univ : Set ℕ))
      (t := {γ : Γ' | hdist (0 : E n) ((γ : PO n 1) • (0 : E n)) ≤ Real.arcosh (1 + b₀)})
      Set.infinite_univ (fun k _ => hc_dist k) hfin
    -- the set of values of the sequence is finite, and the defect is minimal on it
    have hsub : Set.range Cseq ⊆
        {γ : Γ' | hdist (0 : E n) ((γ : PO n 1) • (0 : E n)) ≤ Real.arcosh (1 + b₀)} :=
      fun γ ⟨k, hk⟩ => hk ▸ hc_dist k
    have hTfin : (Set.range Cseq).Finite := hfin.subset hsub
    have hFne : hTfin.toFinset.Nonempty :=
      ⟨Cseq 0, by rw [Set.Finite.mem_toFinset]; exact ⟨0, rfl⟩⟩
    obtain ⟨γ₀, hγ₀F, hγ₀min⟩ := Finset.exists_min_image hTfin.toFinset
      (fun γ : Γ' => ∑ p : (Fin n ⊕ Fin 1) × (Fin n ⊕ Fin 1),
        |mat (ToO ((γ : Γ') : PO n 1)) p.1 p.2 - dE n p.1 p.2|) hFne
    have hdefect_le : ∀ k : ℕ,
        (∑ p : (Fin n ⊕ Fin 1) × (Fin n ⊕ Fin 1),
          |mat (ToO ((Cseq k : Γ') : PO n 1)) p.1 p.2 - dE n p.1 p.2|)
          ≤ (msz n) * ((msz n) * ((1 / 2 : ℝ) ^ k * b₀)) := by
      intro k
      have h1 : ∀ p : (Fin n ⊕ Fin 1) × (Fin n ⊕ Fin 1),
          |mat (ToO ((Cseq k : Γ') : PO n 1)) p.1 p.2 - dE n p.1 p.2|
            ≤ (1 / 2 : ℝ) ^ k * b₀ := by
        intro p
        exact hiter k p.1 p.2
      calc (∑ p, |mat (ToO ((Cseq k : Γ') : PO n 1)) p.1 p.2 - dE n p.1 p.2|)
          ≤ ∑ _p : (Fin n ⊕ Fin 1) × (Fin n ⊕ Fin 1), ((1 / 2 : ℝ) ^ k * b₀) :=
            Finset.sum_le_sum (fun p _ => h1 p)
        _ = ((Fintype.card ((Fin n ⊕ Fin 1) × (Fin n ⊕ Fin 1)) : ℕ) : ℝ) *
              ((1 / 2 : ℝ) ^ k * b₀) := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        _ = (msz n) * ((msz n) * ((1 / 2 : ℝ) ^ k * b₀)) := by
            rw [Fintype.card_prod, card_sum_fin]
            simp only [msz]
            push_cast
            ring
    have hzero : (∑ p : (Fin n ⊕ Fin 1) × (Fin n ⊕ Fin 1),
        |mat (ToO ((γ₀ : Γ') : PO n 1)) p.1 p.2 - dE n p.1 p.2|) ≤ 0 := by
      by_contra hcon
      push_neg at hcon
      have hden : 0 < (msz n) * ((msz n) * b₀) := by positivity
      obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one
        (x := (∑ p : (Fin n ⊕ Fin 1) × (Fin n ⊕ Fin 1),
            |mat (ToO ((γ₀ : Γ') : PO n 1)) p.1 p.2 - dE n p.1 p.2|) /
            ((msz n) * ((msz n) * b₀)))
        (y := 1 / 2) (by positivity) (by norm_num)
      rw [lt_div_iff₀ hden] at hk
      have h1 : (msz n) * ((msz n) * ((1 / 2 : ℝ) ^ k * b₀))
          < ∑ p : (Fin n ⊕ Fin 1) × (Fin n ⊕ Fin 1),
              |mat (ToO ((γ₀ : Γ') : PO n 1)) p.1 p.2 - dE n p.1 p.2| := by
        nlinarith [hk]
      have h2 : (∑ p : (Fin n ⊕ Fin 1) × (Fin n ⊕ Fin 1),
            |mat (ToO ((γ₀ : Γ') : PO n 1)) p.1 p.2 - dE n p.1 p.2|)
          ≤ (∑ p : (Fin n ⊕ Fin 1) × (Fin n ⊕ Fin 1),
              |mat (ToO ((Cseq k : Γ') : PO n 1)) p.1 p.2 - dE n p.1 p.2|) :=
        hγ₀min (Cseq k) (by rw [Set.Finite.mem_toFinset]; exact ⟨k, rfl⟩)
      have h3 := hdefect_le k
      linarith
    have hφ0 : (∑ p : (Fin n ⊕ Fin 1) × (Fin n ⊕ Fin 1),
        |mat (ToO ((γ₀ : Γ') : PO n 1)) p.1 p.2 - dE n p.1 p.2|) = 0 :=
      le_antisymm hzero (Finset.sum_nonneg (fun p _ => abs_nonneg _))
    -- hence the corresponding lift is the identity matrix
    have hM1 : ToO ((γ₀ : Γ') : PO n 1) = 1 := by
      have hterm : ∀ p : (Fin n ⊕ Fin 1) × (Fin n ⊕ Fin 1),
          mat (ToO ((γ₀ : Γ') : PO n 1)) p.1 p.2 = dE n p.1 p.2 := by
        intro p
        have h := (Finset.sum_eq_zero_iff_of_nonneg (fun q (_ : q ∈ Finset.univ) =>
          abs_nonneg (mat (ToO ((γ₀ : Γ') : PO n 1)) q.1 q.2 - dE n q.1 q.2))).mp hφ0 p
          (Finset.mem_univ p)
        exact sub_eq_zero.mp (abs_eq_zero.mp h)
      apply O1.mat_injective
      ext i j
      rw [mat_one_entry]
      exact hterm (i, j)
    have hcoe : ((γ₀ : Γ') : PO n 1) = 1 := by
      rw [← coeToO n hA ((γ₀ : Γ') : PO n 1), hM1]
      rfl
    have hγ₀1 : γ₀ = 1 := Subtype.ext hcoe
    obtain ⟨m, hm⟩ : ∃ m : ℕ, Cseq m = 1 := by
      obtain ⟨m, hm⟩ : ∃ m : ℕ, Cseq m = γ₀ := (Set.Finite.mem_toFinset hTfin).mp hγ₀F
      exact ⟨m, by rw [hm, hγ₀1]⟩
    -- backward induction
    have hfinal : Pres2 δ' (bd h⁻¹ x) (bd h⁻¹ y) := by
      have hdown : ∀ k ≤ m, Pres2 (ci a' δ' (m - k)) (bd h⁻¹ x) (bd h⁻¹ y) := by
        intro k hk
        induction k with
        | zero =>
          have h0 : ci a' δ' (m - 0) = 1 := by
            rw [Nat.sub_zero]
            exact congrArg Subtype.val hm
          rw [h0]
          exact Or.inl ⟨hA.2.2.2.2.2.2.2.2.1 _ hx', hA.2.2.2.2.2.2.2.2.1 _ hy'⟩
        | succ k ih =>
          have hk' : k ≤ m := by omega
          have ih' := ih hk'
          have heq : ci a' δ' (m - (k + 1) + 1) = ci a' δ' (m - k) := by
            congr 1
            omega
          have ih'' : Pres2 (ci a' δ' (m - (k + 1) + 1)) (bd h⁻¹ x) (bd h⁻¹ y) := by
            rw [heq]
            exact ih'
          rw [ci_succ] at ih''
          exact pres2_step hA hI hPS hx' hy' hne' hLox'.2.2.2.1 hLox'.2.2.2.2.1
            hLox'inv ih''
      have h0 : m - m = 0 := Nat.sub_self m
      have h := hdown m le_rfl
      rw [h0, ci_zero] at h
      exact h
    -- conjugate back
    unfold Pres2 at hfinal
    have hδ_eq : (δ : PO n 1) = h * δ' * h⁻¹ := by
      rw [hδ'def]
      group
    have hbx : bd h (bd h⁻¹ x) = x := by
      rw [← hA.2.2.2.2.2.2.2.2.2.1 h h⁻¹ x hxS, mul_inv_cancel,
        hA.2.2.2.2.2.2.2.2.1 x hxS]
    have hby : bd h (bd h⁻¹ y) = y := by
      rw [← hA.2.2.2.2.2.2.2.2.2.1 h h⁻¹ y hyS, mul_inv_cancel,
        hA.2.2.2.2.2.2.2.2.1 y hyS]
    have hconj : ∀ w ∈ Sph n, bd (δ : PO n 1) w = bd h (bd δ' (bd h⁻¹ w)) := by
      intro w hw
      calc bd (δ : PO n 1) w = bd (h * δ' * h⁻¹) w := by rw [hδ_eq]
        _ = bd (h * δ') (bd h⁻¹ w) := hA.2.2.2.2.2.2.2.2.2.1 (h * δ') h⁻¹ w hw
        _ = bd h (bd δ' (bd h⁻¹ w)) :=
              hA.2.2.2.2.2.2.2.2.2.1 h δ' (bd h⁻¹ w) (hA.2.2.2.2.2.2.2.1 h⁻¹ w hw)
    rcases hfinal with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left
      exact ⟨by rw [hconj x hxS, h1, hbx], by rw [hconj y hyS, h2, hby]⟩
    · right
      exact ⟨by rw [hconj x hxS, h1, hby], by rw [hconj y hyS, h2, hbx]⟩
  · refine ⟨1, one_pos, ?_⟩
    intro Γ hdisc z x y a δ hLox hNear hshort
    exfalso
    have h0 : 0 ≤ hdist z ((δ : PO n 1) • z) := hI.1 z ((δ : PO n 1) • z)
    have hRneg : R < 0 := not_le.mp hR
    linarith

end

end Work.Mostow
