import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.PairsAux
import Submission.Work.HP.lam_basic
import Submission.Work.HP.MDBasic.finite_sets
import Submission.Work.HP.Lat.detL_ge_one
import Submission.Work.HP.FM.schmidt_bound
import Submission.Work.HP.numaux.Defs
import Submission.Work.HP.numaux.lam_le_iff
import Submission.Work.HP.numaux.rk_satLat
import Submission.Work.HP.numaux.castL_mem_spread_iff

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open Finset
open scoped BigOperators

namespace Work.HP.EE

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Elementary power identity used to clear the window denominators. -/
lemma two_mul_div_pow_mul {a b T : ℝ} {r : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (hr : 1 ≤ r) :
    (2 * (T / b)) ^ (r - 1) * (2 * (T / a)) = 2 ^ r * T ^ r / (a * b ^ (r - 1)) := by
  have h : r - 1 + 1 = r := by omega
  rw [show (2 : ℝ) ^ r = 2 ^ (r - 1) * 2 from by rw [← pow_succ, h],
      show T ^ r = T ^ (r - 1) * T from by rw [← pow_succ, h],
      mul_pow, div_pow]
  field_simp

/-! ## Ball-count bounds from Schmidt's bound -/

/-- For a lattice of rank `2`, Schmidt's bound reads
`#(L ∩ B(T)) ≤ K (T²/(λ₁λ₂) + T/λ₁ + 1)`. -/
theorem exists_ballCount_rank2 :
    ∃ K : ℝ, 0 < K ∧ ∀ (L : Submodule ℤ (ι → ℤ)) (T : ℝ), rk L = 2 → 1 ≤ T →
      (ballCount L T : ℝ) ≤ K * (T ^ 2 / (lam L 1 * lam L 2) + T / lam L 1 + 1) := by
  obtain ⟨Kc, hKc, hKc'⟩ := FM.schmidt_bound (ι := ι)
  refine ⟨2 * Kc, by positivity, ?_⟩
  intro L T h2 hT
  have hT0 : 0 ≤ T := le_trans zero_le_one hT
  have hmono : lam L 1 ≤ lam L 2 := lam_mono L (by norm_num) (by omega)
  have h1 : 0 < lam L 1 := lam_pos L le_rfl (by omega)
  have h2' : 0 < lam L 2 := lam_pos L (by norm_num) (by omega)
  have hss := hKc' L T hT
  have hprod : (∏ i ∈ Finset.range (rk L), (T / lam L (i + 1) + 1))
      = (T / lam L 1 + 1) * (T / lam L 2 + 1) := by
    rw [h2, Finset.prod_range_succ, Finset.prod_range_succ]
    simp
  rw [hprod] at hss
  have hdiv : T / lam L 2 ≤ T / lam L 1 := div_le_div_of_nonneg_left hT0 h1 hmono
  have hA : 0 ≤ T ^ 2 / (lam L 1 * lam L 2) := by positivity
  have hexp : (T / lam L 1 + 1) * (T / lam L 2 + 1)
      = T ^ 2 / (lam L 1 * lam L 2) + T / lam L 1 + T / lam L 2 + 1 := by
    field_simp
    ring
  have hmain : (T / lam L 1 + 1) * (T / lam L 2 + 1)
      ≤ 2 * (T ^ 2 / (lam L 1 * lam L 2) + T / lam L 1 + 1) := by
    rw [hexp]; linarith
  calc (ballCount L T : ℝ) ≤ Kc * ((T / lam L 1 + 1) * (T / lam L 2 + 1)) := hss
    _ ≤ Kc * (2 * (T ^ 2 / (lam L 1 * lam L 2) + T / lam L 1 + 1)) :=
        mul_le_mul_of_nonneg_left hmain hKc.le
    _ = 2 * Kc * (T ^ 2 / (lam L 1 * lam L 2) + T / lam L 1 + 1) := by ring

/-- For a lattice of rank `≥ 2` and `T ≥ λ₂`, Schmidt's bound gives
`#(L ∩ B(T)) ≤ K T^{rk L}/(λ₁ λ₂^{rk L - 1})`. -/
theorem exists_ballCount_rank_ge2 :
    ∃ K : ℝ, 0 < K ∧ ∀ (L : Submodule ℤ (ι → ℤ)) (T : ℝ), 1 ≤ T → 2 ≤ rk L → lam L 2 ≤ T →
      (ballCount L T : ℝ) ≤ K * T ^ rk L / (lam L 1 * lam L 2 ^ (rk L - 1)) := by
  obtain ⟨Kc, hKc, hKc'⟩ := FM.schmidt_bound (ι := ι)
  refine ⟨Kc * 2 ^ (Fintype.card ι), by positivity, ?_⟩
  intro L T hT hrk hlam2
  have hT0 : 0 ≤ T := le_trans zero_le_one hT
  have h1 : 0 < lam L 1 := lam_pos L le_rfl (by omega)
  have h2' : 0 < lam L 2 := lam_pos L (by norm_num) hrk
  have hmono : lam L 1 ≤ lam L 2 := lam_mono L (by norm_num) hrk
  have hss := hKc' L T hT
  have hpb : (∏ i ∈ Finset.range (rk L), (T / lam L (i + 1) + 1))
      ≤ 2 ^ (rk L) * T ^ (rk L) / (lam L 1 * lam L 2 ^ (rk L - 1)) := by
    have hsplit : (∏ i ∈ Finset.range (rk L), (T / lam L (i + 1) + 1))
        = (∏ i ∈ Finset.range (rk L - 1), (T / lam L (i + 1 + 1) + 1))
          * (T / lam L 1 + 1) := by
      have h := Finset.prod_range_succ' (fun i => T / lam L (i + 1) + 1) (rk L - 1)
      rw [show rk L - 1 + 1 = rk L from by omega] at h
      exact h
    have hstep : (∏ i ∈ Finset.range (rk L - 1), (T / lam L (i + 1 + 1) + 1))
        ≤ (∏ _i ∈ Finset.range (rk L - 1), (T / lam L 2 + 1)) := by
      refine Finset.prod_le_prod₀ (fun i hi => ?_) (fun i hi => ?_)
      · have hi' : i + 1 + 1 ≤ rk L := by
          have := Finset.mem_range.mp hi; omega
        have hpos : 0 < lam L (i + 1 + 1) := lam_pos L (by omega) hi'
        have : 0 ≤ T / lam L (i + 1 + 1) := div_nonneg hT0 hpos.le
        linarith
      · have hi' : i + 1 + 1 ≤ rk L := by
          have := Finset.mem_range.mp hi; omega
        have hle : lam L 2 ≤ lam L (i + 1 + 1) := lam_mono L (by omega) hi'
        have : T / lam L (i + 1 + 1) ≤ T / lam L 2 :=
          div_le_div_of_nonneg_left hT0 h2' hle
        linarith
    have hconst : (∏ _i ∈ Finset.range (rk L - 1), (T / lam L 2 + 1))
        = (T / lam L 2 + 1) ^ (rk L - 1) := by
      rw [Finset.prod_const, Finset.card_range]
    have hfin : (T / lam L 2 + 1) ≤ 2 * (T / lam L 2) := by
      have hge : 1 ≤ T / lam L 2 := (one_le_div h2').mpr hlam2
      linarith
    have hf0 : (T / lam L 1 + 1) ≤ 2 * (T / lam L 1) := by
      have hge : 1 ≤ T / lam L 1 := (one_le_div h1).mpr (le_trans hmono hlam2)
      linarith
    rw [hsplit]
    have hstep3 : (∏ i ∈ Finset.range (rk L - 1), (T / lam L (i + 1 + 1) + 1))
          * (T / lam L 1 + 1)
        ≤ (T / lam L 2 + 1) ^ (rk L - 1) * (T / lam L 1 + 1) := by
      rw [← hconst]
      exact mul_le_mul_of_nonneg_right hstep (by positivity)
    refine hstep3.trans ?_
    have hstep4 : (T / lam L 2 + 1) ^ (rk L - 1) * (T / lam L 1 + 1)
        ≤ (2 * (T / lam L 2)) ^ (rk L - 1) * (2 * (T / lam L 1)) :=
      mul_le_mul (pow_le_pow_left₀ (by positivity) hfin (rk L - 1)) hf0
        (by positivity) (by positivity)
    refine hstep4.trans (le_of_eq ?_)
    exact two_mul_div_pow_mul (ne_of_gt h1) (ne_of_gt h2') (by omega)
  have hpow : (2 : ℝ) ^ (rk L) ≤ 2 ^ (Fintype.card ι) :=
    pow_le_pow_right₀ (by norm_num) (rk_le_card L)
  have hDpos : 0 < lam L 1 * lam L 2 ^ (rk L - 1) := by positivity
  have hTr : 0 ≤ T ^ rk L := pow_nonneg hT0 _
  calc (ballCount L T : ℝ) ≤ Kc * (∏ i ∈ Finset.range (rk L), (T / lam L (i + 1) + 1)) := hss
    _ ≤ Kc * (2 ^ (rk L) * T ^ (rk L) / (lam L 1 * lam L 2 ^ (rk L - 1))) :=
        mul_le_mul_of_nonneg_left hpb hKc.le
    _ = Kc * 2 ^ (rk L) * (T ^ (rk L) / (lam L 1 * lam L 2 ^ (rk L - 1))) := by ring
    _ ≤ Kc * 2 ^ (Fintype.card ι) * (T ^ (rk L) / (lam L 1 * lam L 2 ^ (rk L - 1))) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        exact mul_le_mul_of_nonneg_left hpow hKc.le
    _ = Kc * 2 ^ (Fintype.card ι) * T ^ rk L / (lam L 1 * lam L 2 ^ (rk L - 1)) := by ring


/-! ## Finiteness of the sets of lattices, and the sharp lattice count for rank `2` -/

/-- Two linearly independent vectors of a primitive rank-`2` lattice span a sublattice whose
saturation is the whole lattice. -/
lemma satLat_span_of_witness {L : Submodule ℤ (ι → ℤ)} (hL : IsPrimLat L) (hrk : rk L = 2)
    {f : Fin 2 → (ι → ℤ)} (hfL : ∀ j, f j ∈ L) (hfI : LinearIndependent ℤ f) :
    L = satLat (Submodule.span ℤ (Set.range f)) := by
  classical
  set M : Submodule ℤ (ι → ℤ) := Submodule.span ℤ (Set.range f) with hM
  have hML : M ≤ L := Submodule.span_le.mpr (by rintro y ⟨j, rfl⟩; exact hfL j)
  set S : Set (ι → ℚ) := Set.range fun j : Fin 2 => numaux.castL (f j) with hSdef
  have hle : numaux.spread M ≤ Submodule.span ℚ S := by
    apply Submodule.span_le.mpr
    rintro y ⟨z, hz, rfl⟩
    refine Submodule.span_induction (R := ℤ) (s := Set.range f)
      (p := fun z _ => numaux.castL z ∈ Submodule.span ℚ S) ?_ ?_ ?_ ?_ hz
    · rintro z ⟨j, rfl⟩
      exact Submodule.subset_span ⟨j, rfl⟩
    · exact Submodule.zero_mem _
    · intro a b _ _ ha hb
      rw [map_add]
      exact Submodule.add_mem _ ha hb
    · intro c a _ ha
      rw [map_zsmul]
      rw [show c • numaux.castL a = ((c : ℚ)) • numaux.castL a from
        (Int.cast_smul_eq_zsmul (R := ℚ) c (numaux.castL a)).symm]
      exact Submodule.smul_mem _ _ ha
  have hge : Submodule.span ℚ S ≤ numaux.spread M := by
    apply Submodule.span_le.mpr
    refine Set.range_subset_iff.mpr ?_
    intro j
    exact numaux.castL_mem_spread (Submodule.subset_span ⟨j, rfl⟩)
  have hD : numaux.spread M = Submodule.span ℚ S := le_antisymm hle hge
  have hdimM : Module.finrank ℚ (numaux.spread M) = 2 := by
    rw [hD, finrank_span_eq_card]
    · simp
    · have h := (linearIndependent_algebraMap_comp_iff (R := ℤ) (S := ℚ) (v := f)).mpr hfI
      have h2 : (fun j : Fin 2 => numaux.castL (f j))
          = (fun j : Fin 2 => (algebraMap ℤ ℚ) ∘ f j) := by
        funext j i
        simp [numaux.castL]
      rw [h2]
      exact h
  have hdimL : Module.finrank ℚ (numaux.spread L) = 2 := by
    rw [← numaux.finrank_eq_finrank_spread L]
    exact hrk
  have hsp : numaux.spread M = numaux.spread L :=
    Submodule.eq_of_le_of_finrank_eq (numaux.spread_mono hML) (by rw [hdimM, hdimL])
  refine le_antisymm ?_ ?_
  · intro x hx
    have h1 : numaux.castL x ∈ numaux.spread M := by
      rw [hsp]
      exact numaux.castL_mem_spread hx
    exact (numaux.castL_mem_spread_iff M x).mp h1
  · calc satLat M ≤ satLat L := satLat_mono hML
      _ = L := satLat_eq_of_isPrimLat hL

/-- The set of primitive rank-`2` lattices whose first two successive minima are bounded by
`s 0`, `s 1` is finite. -/
lemma lattice_set_finite (s : Fin 2 → ℝ) :
    {L : Submodule ℤ (ι → ℤ) |
      IsPrimLat L ∧ rk L = 2 ∧ ∀ j : Fin 2, lam L (j.1 + 1) ≤ s j}.Finite := by
  classical
  set R : ℝ := max (s 0) (s 1) with hR
  set S : Set (Submodule ℤ (ι → ℤ)) :=
    {L | IsPrimLat L ∧ rk L = 2 ∧ ∀ j : Fin 2, lam L (j.1 + 1) ≤ s j} with hS
  have hWfin : {f : Fin 2 → (ι → ℤ) | LinearIndependent ℤ f ∧ ∀ j, eNorm (f j) ≤ R}.Finite :=
    (Set.Finite.pi (fun _ : Fin 2 => MDBasic.finite_eNorm_le (ι := ι) R)).subset
      (fun f hf => by rw [Set.mem_pi]; intro j _; exact hf.2 j)
  let Φ : Submodule ℤ (ι → ℤ) → (Fin 2 → (ι → ℤ)) := fun L =>
    if h : IsPrimLat L ∧ rk L = 2 ∧ ∀ j : Fin 2, lam L (j.1 + 1) ≤ s j then
      Classical.choose (numaux.lam_le_iff L 2 R (by omega)
        (le_trans (h.2.2 ⟨1, by norm_num⟩) (le_max_right _ _)))
    else fun _ => 0
  have hΦspec : ∀ L ∈ S, (∀ j, Φ L j ∈ L) ∧ LinearIndependent ℤ (Φ L) ∧ ∀ j, eNorm (Φ L j) ≤ R := by
    intro L hL
    have h : IsPrimLat L ∧ rk L = 2 ∧ ∀ j : Fin 2, lam L (j.1 + 1) ≤ s j := hL
    simp only [Φ, dif_pos h]
    exact Classical.choose_spec (numaux.lam_le_iff L 2 R (by omega)
      (le_trans (h.2.2 ⟨1, by norm_num⟩) (le_max_right _ _)))
  refine Set.Finite.of_injOn (f := Φ) ?_ ?_ hWfin
  · intro L hL
    exact ⟨(hΦspec L hL).2.1, (hΦspec L hL).2.2⟩
  · intro L hL L' hL' heq
    have h1 := hΦspec L hL
    have h2 := hΦspec L' hL'
    have e1 : L = satLat (Submodule.span ℤ (Set.range (Φ L))) :=
      satLat_span_of_witness hL.1 hL.2.1 h1.1 h1.2.1
    have e2 : L' = satLat (Submodule.span ℤ (Set.range (Φ L'))) :=
      satLat_span_of_witness hL'.1 hL'.2.1 h2.1 h2.2.1
    rw [e1, e2, heq]

/-- **Sharp lattice count, rank `2`, Finset form**, derived from the `ncard` form of the
"number lattices" lemma. -/
theorem numLattices_finset_of {K : ℝ}
    (hK : ∀ (s : Fin 2 → ℝ), (∀ j, 1 ≤ s j) →
      (({L : Submodule ℤ (ι → ℤ) | IsPrimLat L ∧ rk L = 2 ∧
        ∀ j : Fin 2, lam L (j.1 + 1) ≤ s j}.ncard : ℝ)
        ≤ K * ∏ j : Fin 2, s j ^ (Fintype.card ι + 3 - 2 * (j.1 + 1)))) :
    ∀ (s : Fin 2 → ℝ), (∀ j, 1 ≤ s j) →
      ∀ F : Finset (Submodule ℤ (ι → ℤ)),
      (∀ L ∈ F, IsPrimLat L ∧ rk L = 2 ∧ (∀ j : Fin 2, lam L (j.1 + 1) ≤ s j)) →
      (F.card : ℝ) ≤ K * ∏ j : Fin 2, s j ^ (Fintype.card ι + 3 - 2 * (j.1 + 1)) := by
  intro s hs F hF
  have hfin := lattice_set_finite (ι := ι) s
  have hsub : (F : Set (Submodule ℤ (ι → ℤ))) ⊆
      {L : Submodule ℤ (ι → ℤ) | IsPrimLat L ∧ rk L = 2 ∧ ∀ j : Fin 2, lam L (j.1 + 1) ≤ s j} :=
    fun L hL => hF L hL
  have h1 : ((F.card : ℕ) : ℝ) ≤
      (({L : Submodule ℤ (ι → ℤ) | IsPrimLat L ∧ rk L = 2 ∧
        ∀ j : Fin 2, lam L (j.1 + 1) ≤ s j} : Set (Submodule ℤ (ι → ℤ))).ncard : ℝ) := by
    have h := Set.ncard_le_ncard hsub hfin
    rw [Set.ncard_coe_finset] at h
    exact_mod_cast h
  refine h1.trans ?_
  have h2 := hK s hs
  refine le_trans h2 (le_of_eq ?_)
  refine congrArg (fun x => K * x) ?_
  refine Finset.prod_congr rfl (fun j _ => ?_)
  congr 1


end Work.HP.EE
