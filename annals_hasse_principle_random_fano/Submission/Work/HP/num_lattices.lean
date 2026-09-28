import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.PairsAux
import Submission.Work.HP.numaux.Defs
import Submission.Work.HP.MinkDefs
import Submission.Work.HP.box_card
import Submission.Work.HP.FM.minkowski_lower
import Submission.Work.HP.numaux.lam_le_iff
import Submission.Work.HP.numaux.detL_span_le_prod
import Submission.Work.HP.numaux.detL_le_of_le
import Submission.Work.HP.numaux.rk_span_eq
import Submission.Work.HP.numaux.rk_satLat
import Submission.Work.HP.numaux.rk_sup_span_one
import Submission.Work.HP.numaux.eq_satLat_sup_span
import Submission.Work.HP.numaux.satLat_span
import Submission.Work.HP.detgam_orthLat_detL
import Submission.Work.HP.numaux.orthLat_orthLat
import Submission.Work.HP.numaux.rk_orthLat
import Submission.Work.HP.numaux.mem_satLat_of_dot_eq_zero
import Submission.Work.HP.numaux.minkowski_prod

/-!
# `Work.HP.num_lattices`

The paper's "number lattices" lemma (Browning–Le Boudec–Sawin, §3.3): the number of primitive
rank-`r` sublattices of `ℤ^ι` whose successive minima satisfy `λ_j ≤ s_j` is
`≪ ∏_j s_j^{N+r+1-2j}`, where `N = card ι`.

The proof is an induction on `r` (see `num_lattices`), whose key input is the *fibre count*
`fiber_count` below: for a primitive `Λ` and `S ≥ 1`, the number of primitive
rank-`(rk Λ + 1)` lattices `L ⊇ Λ` with `λ_{rk Λ+1}(L) ≤ S` is at most
`16^N · K · S^{N-rk Λ} · detL Λ`.  The proof pairs each such `L` with a canonical short vector
`u_L ∈ L ∖ saturation(Λ)`, and injects `L ↦ (⟨u_L, a_j⟩)_j` into a box, where `a_1, …, a_m`
are the successive-minima vectors of the orthogonal lattice `orthLat Λ`, of rank `N - rk Λ`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

noncomputable section

open Finset

namespace Work.HP

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## Elementary estimates -/

/-- Every coordinate of an integer vector is bounded by its Euclidean norm. -/
lemma abs_coord_le_eNorm' (v : ι → ℤ) (i : ι) : |(v i : ℝ)| ≤ eNorm v := by
  have h1 : ((v i : ℝ)) ^ 2 ≤ ∑ j, ((v j : ℝ)) ^ 2 :=
    Finset.single_le_sum (fun j _ => sq_nonneg ((v j : ℝ))) (Finset.mem_univ i)
  calc |(v i : ℝ)| = Real.sqrt (((v i : ℝ)) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (∑ j, ((v j : ℝ)) ^ 2) := Real.sqrt_le_sqrt h1
    _ = eNorm v := rfl

/-- Membership in the coordinate box from a norm bound. -/
lemma mem_box_of_eNorm_le (S : ℝ) {v : ι → ℤ} (hv : eNorm v ≤ S) :
    v ∈ Fintype.piFinset (fun _ : ι => Finset.Icc (-(Nat.ceil S : ℤ)) (Nat.ceil S)) := by
  rw [Fintype.mem_piFinset]
  intro i
  rw [Finset.mem_Icc]
  have h := abs_coord_le_eNorm' v i
  have h2 : |((v i : ℤ) : ℝ)| ≤ ((Nat.ceil S : ℤ) : ℝ) :=
    le_trans h (le_trans hv (Nat.le_ceil S))
  have h4 := abs_le.mp h2
  exact ⟨by exact_mod_cast h4.1, by exact_mod_cast h4.2⟩

/-- A tuple of independent lattice vectors bounds the corresponding successive minimum. -/
lemma lam_le_of_tuple {M : Submodule ℤ (ι → ℤ)} {j : ℕ} {f : Fin j → (ι → ℤ)}
    (hf : ∀ k, f k ∈ M) (hind : LinearIndependent ℤ f) {x : ℝ} (hx0 : 0 ≤ x)
    (hx : ∀ k, eNorm (f k) ≤ x) : lam M j ≤ x := by
  rw [lam]
  refine csInf_le ⟨0, fun r hr => hr.1⟩ ⟨hx0, f, hf, hind, hx⟩

/-- The successive minima are monotone in the index. -/
lemma lam_mono_index (L : Submodule ℤ (ι → ℤ)) {j k : ℕ} (hjk : j ≤ k) (hk : k ≤ rk L) :
    lam L j ≤ lam L k := by
  have hsub : ∀ r : ℝ, (0 ≤ r ∧ ∃ f : Fin k → (ι → ℤ), (∀ i, f i ∈ L) ∧
      LinearIndependent ℤ f ∧ ∀ i, eNorm (f i) ≤ r) →
      (0 ≤ r ∧ ∃ f : Fin j → (ι → ℤ), (∀ i, f i ∈ L) ∧
      LinearIndependent ℤ f ∧ ∀ i, eNorm (f i) ≤ r) := by
    rintro r ⟨hr0, f, hf, hind, hfr⟩
    exact ⟨hr0, fun i => f (Fin.castLE hjk i), fun i => hf _,
      hind.comp (Fin.castLE hjk) (Fin.castLE_injective hjk), fun i => hfr _⟩
  have hbdd : BddBelow {r : ℝ | 0 ≤ r ∧ ∃ f : Fin j → (ι → ℤ), (∀ i, f i ∈ L) ∧
      LinearIndependent ℤ f ∧ ∀ i, eNorm (f i) ≤ r} :=
    ⟨0, fun r hr => hr.1⟩
  obtain ⟨g, hg, hgind⟩ := exists_linIndep_card L hk
  have hne : ({r : ℝ | 0 ≤ r ∧ ∃ f : Fin k → (ι → ℤ), (∀ i, f i ∈ L) ∧
      LinearIndependent ℤ f ∧ ∀ i, eNorm (f i) ≤ r}).Nonempty :=
    ⟨(∑ i, eNorm (g i)) + 1, by
        have h0 := Finset.sum_nonneg (s := Finset.univ) (fun i _ => eNorm_nonneg (g i))
        linarith, g, hg, hgind, fun i => by
      have h1 := Finset.single_le_sum (fun i _ => eNorm_nonneg (g i)) (Finset.mem_univ i)
      linarith⟩
  rw [lam, lam]
  exact le_csInf hne (fun r hr => csInf_le hbdd (hsub r hr))

/-- A non-zero lattice vector has norm at least one; hence so does every successive minimum. -/
lemma lam_ge_one (L : Submodule ℤ (ι → ℤ)) {j : ℕ} (hj : 1 ≤ j) (hjk : j ≤ rk L) :
    1 ≤ lam L j := by
  obtain ⟨g, hg, hgind⟩ := exists_linIndep_card L hjk
  have hne : ({r : ℝ | 0 ≤ r ∧ ∃ f : Fin j → (ι → ℤ), (∀ i, f i ∈ L) ∧
      LinearIndependent ℤ f ∧ ∀ i, eNorm (f i) ≤ r}).Nonempty :=
    ⟨(∑ i, eNorm (g i)) + 1, by
        have h0 := Finset.sum_nonneg (s := Finset.univ) (fun i _ => eNorm_nonneg (g i))
        linarith, g, hg, hgind, fun i => by
      have h1 := Finset.single_le_sum (fun i _ => eNorm_nonneg (g i)) (Finset.mem_univ i)
      linarith⟩
  rw [lam]
  refine le_csInf hne ?_
  rintro r ⟨hr0, f, hf, hind, hfr⟩
  exact le_trans (one_le_eNorm_of_ne_zero (hind.ne_zero ⟨0, by omega⟩)) (hfr ⟨0, by omega⟩)

/-- The number of integer vectors in the box `{|t j| ≤ T j}` is at most `∏ j, (2 T j + 3)`. -/
lemma ncard_box_le (m : ℕ) (T : Fin m → ℝ) (hT : ∀ j, 0 ≤ T j) :
    (({t : Fin m → ℤ | ∀ j, |(t j : ℝ)| ≤ T j}.ncard : ℕ) : ℝ)
      ≤ ∏ j : Fin m, (2 * T j + 3) := by
  set B : Finset (Fin m → ℤ) :=
    Fintype.piFinset (fun j : Fin m => Finset.Icc (-(Nat.ceil (T j) : ℤ)) (Nat.ceil (T j)))
    with hB
  have hsub : {t : Fin m → ℤ | ∀ j, |(t j : ℝ)| ≤ T j} ⊆ (B : Set (Fin m → ℤ)) := by
    intro t ht
    rw [Finset.mem_coe, Fintype.mem_piFinset]
    intro j
    rw [Finset.mem_Icc]
    have h := ht j
    have h2 : |((t j : ℤ) : ℝ)| ≤ ((Nat.ceil (T j) : ℤ) : ℝ) :=
      le_trans h (Nat.le_ceil (T j))
    have h4 := abs_le.mp h2
    exact ⟨by exact_mod_cast h4.1, by exact_mod_cast h4.2⟩
  have h1 : ({t : Fin m → ℤ | ∀ j, |(t j : ℝ)| ≤ T j} : Set (Fin m → ℤ)).ncard ≤ B.card := by
    have h2 := Set.ncard_le_ncard hsub (Finset.finite_toSet B)
    rwa [Set.ncard_coe_finset] at h2
  have hcard : (B.card : ℝ) = ∏ j : Fin m, (2 * (Nat.ceil (T j) : ℝ) + 1) := by
    rw [hB, Fintype.card_piFinset]
    push_cast
    refine Finset.prod_congr rfl ?_
    intro j _
    rw [Int.card_Icc]
    have htn : ((Nat.ceil (T j) : ℤ) + 1 - (-(Nat.ceil (T j) : ℤ))).toNat
        = 2 * Nat.ceil (T j) + 1 := by omega
    rw [htn]
    push_cast
    ring
  have h1R : ((({t : Fin m → ℤ | ∀ j, |(t j : ℝ)| ≤ T j}.ncard : ℕ)) : ℝ) ≤ (B.card : ℝ) := by
    exact_mod_cast h1
  rw [hcard] at h1R
  refine le_trans h1R ?_
  refine Finset.prod_le_prod₀ (f := fun j : Fin m => (2 * (Nat.ceil (T j) : ℝ) + 1))
    (g := fun j : Fin m => (2 * T j + 3)) (fun j _ => by positivity) (fun j _ => ?_)
  have h := Nat.ceil_lt_add_one (hT j)
  linarith

/-! ## The fibre count -/

/-- **Fibre count.**  For a primitive lattice `Λ ⊆ ℤ^ι` and `S ≥ 1`, the number of primitive
rank-`(rk Λ + 1)` lattices `L ⊇ Λ` with `λ_{rk Λ + 1}(L) ≤ S` is at most
`16^{card ι} · K · S^{card ι - rk Λ} · detL Λ`, where `K` is any constant with
`∏_{j < rk L} λ_{j+1}(L) ≤ K · detL L`. -/
theorem fiber_count (Kmk : ℝ) (hKmk0 : 0 ≤ Kmk) (Λ : Submodule ℤ (ι → ℤ))
    (hΛ : IsPrimLat Λ) (S : ℝ) (hS : 1 ≤ S)
    (hKmk : ∀ L : Submodule ℤ (ι → ℤ),
      (∏ j ∈ Finset.range (rk L), lam L (j + 1)) ≤ Kmk * detL L) :
    (({L : Submodule ℤ (ι → ℤ) | Λ ≤ L ∧ IsPrimLat L ∧ rk L = rk Λ + 1 ∧
        lam L (rk Λ + 1) ≤ S}.ncard : ℝ) ≤
      16 ^ (Fintype.card ι) * Kmk * S ^ (Fintype.card ι - rk Λ) * detL Λ) := by
  classical
  set m : ℕ := Fintype.card ι - rk Λ with hm
  have hrm : rk (orthLat Λ) = m := numaux.rk_orthLat Λ hΛ
  -- successive-minima vectors of the orthogonal lattice
  obtain ⟨b, hb_mem, hb_ind, hb_norm⟩ := FM.exists_indep_le_lam (orthLat Λ)
  set a : Fin m → (ι → ℤ) := fun j => b (Fin.cast hrm.symm j) with ha
  have ha_mem : ∀ j, a j ∈ orthLat Λ := fun j => hb_mem _
  have ha_ind : LinearIndependent ℤ a :=
    hb_ind.comp (Fin.cast hrm.symm) (Fin.cast_injective hrm.symm)
  have ha_norm : ∀ j, eNorm (a j) ≤ lam (orthLat Λ) (j.1 + 1) := by
    intro j
    have := hb_norm (Fin.cast hrm.symm j)
    simpa [ha] using this
  set F : Set (Submodule ℤ (ι → ℤ)) :=
    {L | Λ ≤ L ∧ IsPrimLat L ∧ rk L = rk Λ + 1 ∧ lam L (rk Λ + 1) ≤ S} with hF
  -- existence of a canonical witness
  have hex : ∀ L ∈ F, ∃ u : ι → ℤ, u ∈ L ∧ u ∉ satLat Λ ∧ eNorm u ≤ S := by
    intro L hL
    obtain ⟨hΛL, hLprim, hrkL, hlamL⟩ := hL
    obtain ⟨f, hf_mem, hf_ind, hf_norm⟩ := FM.exists_indep_le_lam L
    have hsome : ∃ k, f k ∉ satLat Λ := by
      by_contra hcon
      push_neg at hcon
      have hspan_le : Submodule.span ℤ (Set.range f) ≤ satLat Λ :=
        Submodule.span_le.mpr (by rintro x ⟨k, rfl⟩; exact hcon k)
      have h1 : rk (Submodule.span ℤ (Set.range f)) ≤ rk (satLat Λ) :=
        Submodule.finrank_mono hspan_le
      rw [numaux.rk_span_eq hf_ind, numaux.rk_satLat Λ, hrkL] at h1
      omega
    obtain ⟨k, hk⟩ := hsome
    refine ⟨f k, hf_mem k, hk, ?_⟩
    refine le_trans (hf_norm k) ?_
    calc lam L (k.1 + 1) ≤ lam L (rk L) :=
          lam_mono_index L (by omega) le_rfl
      _ = lam L (rk Λ + 1) := by rw [hrkL]
      _ ≤ S := hlamL
  let u : (Submodule ℤ (ι → ℤ)) → (ι → ℤ) :=
    fun L => if h : L ∈ F then Classical.choose (hex L h) else 0
  have hu_mem : ∀ L ∈ F, u L ∈ L := by
    intro L hL
    simp only [u, dif_pos hL]
    exact (Classical.choose_spec (hex L hL)).1
  have hu_not : ∀ L ∈ F, u L ∉ satLat Λ := by
    intro L hL
    simp only [u, dif_pos hL]
    exact (Classical.choose_spec (hex L hL)).2.1
  have hu_norm : ∀ L ∈ F, eNorm (u L) ≤ S := by
    intro L hL
    simp only [u, dif_pos hL]
    exact (Classical.choose_spec (hex L hL)).2.2
  -- the injection
  have hinj : Set.InjOn (fun L => fun j : Fin m => dotI (u L) (a j)) F := by
    intro L hL L' hL' heq
    have hw : ∀ j, dotI (u L - u L') (a j) = 0 := by
      intro j
      have h1 : dotI (u L) (a j) - dotI (u L') (a j) = 0 := by
        have h2 := congrFun heq j
        simp only at h2
        linarith
      rw [dotI_sub_left]
      exact h1
    have hmem : u L - u L' ∈ Λ :=
      numaux.mem_satLat_of_dot_eq_zero Λ hΛ hrm ha_mem ha_ind (u L - u L') hw
    have hspan : Λ ⊔ Submodule.span ℤ ({u L} : Set (ι → ℤ))
        = Λ ⊔ Submodule.span ℤ ({u L'} : Set (ι → ℤ)) := by
      have hsplit : u L = u L' + (u L - u L') := by abel
      refine le_antisymm ?_ ?_
      · refine sup_le le_sup_left ?_
        rw [Submodule.span_le]
        intro x hx
        rw [Set.mem_singleton_iff] at hx
        rw [hx, hsplit]
        exact Submodule.add_mem _ (Submodule.mem_sup_right (Submodule.subset_span (by simp)))
          (Submodule.mem_sup_left hmem)
      · refine sup_le le_sup_left ?_
        rw [Submodule.span_le]
        intro x hx
        rw [Set.mem_singleton_iff] at hx
        have hsplit' : u L' = u L - (u L - u L') := by abel
        rw [hx, hsplit']
        exact Submodule.sub_mem _ (Submodule.mem_sup_right (Submodule.subset_span (by simp)))
          (Submodule.mem_sup_left hmem)
    have h1 : L = satLat (Λ ⊔ Submodule.span ℤ ({u L} : Set (ι → ℤ))) :=
      (numaux.eq_satLat_sup_span (Λ := Λ) (L := L) hΛ hL.2.1 hL.1 hL.2.2.1 (hu_mem L hL)
        (hu_not L hL)).symm
    have h2 : L' = satLat (Λ ⊔ Submodule.span ℤ ({u L'} : Set (ι → ℤ))) :=
      (numaux.eq_satLat_sup_span (Λ := Λ) (L := L') hΛ hL'.2.1 hL'.1 hL'.2.2.1 (hu_mem L' hL')
        (hu_not L' hL')).symm
    rw [h1, h2, hspan]
  -- the image lies in a box
  have hbox : (fun L => fun j : Fin m => dotI (u L) (a j)) '' F ⊆
      {t : Fin m → ℤ | ∀ j, |(t j : ℝ)| ≤ S * lam (orthLat Λ) (j.1 + 1)} := by
    rintro t ⟨L, hL, rfl⟩
    intro j
    have h1 : |((dotI (u L) (a j) : ℤ) : ℝ)| ≤ eNorm (u L) * eNorm (a j) := abs_dotI_le _ _
    refine le_trans h1 ?_
    exact mul_le_mul (hu_norm L hL) (ha_norm j) (eNorm_nonneg _) (by linarith)
  have hboxfin : ({t : Fin m → ℤ | ∀ j, |(t j : ℝ)| ≤ S * lam (orthLat Λ) (j.1 + 1)}
      : Set (Fin m → ℤ)).Finite := by
    refine (Finset.finite_toSet (Fintype.piFinset (fun j : Fin m =>
      Finset.Icc (-(Nat.ceil (S * lam (orthLat Λ) (j.1 + 1)) : ℤ))
        (Nat.ceil (S * lam (orthLat Λ) (j.1 + 1)))))).subset ?_
    rintro t ht
    rw [Finset.mem_coe, Fintype.mem_piFinset]
    intro j
    rw [Finset.mem_Icc]
    have h := ht j
    have h2 : |((t j : ℤ) : ℝ)| ≤ ((Nat.ceil (S * lam (orthLat Λ) (j.1 + 1)) : ℤ) : ℝ) :=
      le_trans h (Nat.le_ceil _)
    have h4 := abs_le.mp h2
    exact ⟨by exact_mod_cast h4.1, by exact_mod_cast h4.2⟩
  have hcard1 : (F.ncard : ℝ) ≤
      (({t : Fin m → ℤ | ∀ j, |(t j : ℝ)| ≤ S * lam (orthLat Λ) (j.1 + 1)}.ncard : ℕ) : ℝ) := by
    have hmaps : ∀ L ∈ F, (fun j : Fin m => dotI (u L) (a j)) ∈
        {t : Fin m → ℤ | ∀ j, |(t j : ℝ)| ≤ S * lam (orthLat Λ) (j.1 + 1)} := by
      intro L hL j
      have h1 : |((dotI (u L) (a j) : ℤ) : ℝ)| ≤ eNorm (u L) * eNorm (a j) := abs_dotI_le _ _
      refine le_trans h1 ?_
      exact mul_le_mul (hu_norm L hL) (ha_norm j) (eNorm_nonneg _) (by linarith)
    have h := Set.ncard_le_ncard_of_injOn (fun L => fun j : Fin m => dotI (u L) (a j))
      hmaps hinj hboxfin
    exact_mod_cast h
  have hcard2 : (({t : Fin m → ℤ | ∀ j, |(t j : ℝ)| ≤ S * lam (orthLat Λ) (j.1 + 1)}.ncard
      : ℕ) : ℝ) ≤ ∏ j : Fin m, (2 * (S * lam (orthLat Λ) (j.1 + 1)) + 3) :=
    ncard_box_le m (fun j => S * lam (orthLat Λ) (j.1 + 1)) (fun j => by
      have h1 := lam_nonneg (orthLat Λ) (j.1 + 1)
      nlinarith [hS])
  -- bound the product
  have hprod : ∏ j : Fin m, (2 * (S * lam (orthLat Λ) (j.1 + 1)) + 3)
      ≤ 8 ^ m * S ^ m * (Kmk * detL (orthLat Λ)) := by
    have hstep : ∏ j : Fin m, (2 * (S * lam (orthLat Λ) (j.1 + 1)) + 3)
        ≤ ∏ j : Fin m, (8 * (S * lam (orthLat Λ) (j.1 + 1))) := by
      refine Finset.prod_le_prod₀ (f := fun j : Fin m => 2 * (S * lam (orthLat Λ) (j.1 + 1)) + 3)
        (g := fun j : Fin m => 8 * (S * lam (orthLat Λ) (j.1 + 1))) (fun j _ => by
          have h1 := lam_nonneg (orthLat Λ) (j.1 + 1)
          nlinarith [hS])
        (fun j _ => ?_)
      have h1 : 1 ≤ S * lam (orthLat Λ) (j.1 + 1) :=
        one_le_mul_of_one_le_of_one_le hS (lam_ge_one (orthLat Λ) (by omega) (by rw [hrm]; omega))
      linarith
    have hstep2 : ∏ j : Fin m, (8 * (S * lam (orthLat Λ) (j.1 + 1)))
        = 8 ^ m * (S ^ m * ∏ j : Fin m, lam (orthLat Λ) (j.1 + 1)) := by
      rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const,
        Finset.card_univ, Fintype.card_fin, Finset.prod_const, Finset.card_univ,
        Fintype.card_fin]
    have hstep3 : (∏ j : Fin m, lam (orthLat Λ) (j.1 + 1))
        ≤ Kmk * detL (orthLat Λ) := by
      have h := hKmk (orthLat Λ)
      rw [hrm] at h
      rwa [← Fin.prod_univ_eq_prod_range (fun j => lam (orthLat Λ) (j + 1)) m] at h
    rw [hstep2] at hstep
    refine hstep.trans ?_
    have h8 : (0:ℝ) ≤ 8 ^ m * S ^ m := by positivity
    calc 8 ^ m * (S ^ m * ∏ j : Fin m, lam (orthLat Λ) (j.1 + 1))
        = 8 ^ m * S ^ m * (∏ j : Fin m, lam (orthLat Λ) (j.1 + 1)) := by ring
      _ ≤ 8 ^ m * S ^ m * (Kmk * detL (orthLat Λ)) :=
          mul_le_mul_of_nonneg_left hstep3 h8
  -- final assembly
  refine le_trans hcard1 (le_trans hcard2 ?_)
  refine hprod.trans ?_
  rw [detgam_orthLat_detL Λ hΛ]
  have hmle : m ≤ Fintype.card ι := by omega
  have hdet : 0 ≤ detL Λ := detL_nonneg Λ
  have hS_nonneg : (0:ℝ) ≤ S ^ m := by positivity
  have h8m : (8:ℝ) ^ m ≤ 16 ^ Fintype.card ι := by
    calc (8:ℝ) ^ m ≤ 16 ^ m := pow_le_pow_left₀ (by norm_num) (by norm_num) m
      _ ≤ 16 ^ Fintype.card ι := pow_le_pow_right₀ (by norm_num) hmle
  have hbnd : 8 ^ m * S ^ m * (Kmk * detL Λ) ≤ 16 ^ Fintype.card ι * Kmk * S ^ m * detL Λ := by
    have h2 : (0:ℝ) ≤ S ^ m * (Kmk * detL Λ) := by
      have h3 : (0:ℝ) ≤ S ^ m := pow_nonneg (le_trans zero_le_one hS) m
      exact mul_nonneg h3 (mul_nonneg hKmk0 hdet)
    calc 8 ^ m * S ^ m * (Kmk * detL Λ) = 8 ^ m * (S ^ m * (Kmk * detL Λ)) := by ring
      _ ≤ 16 ^ Fintype.card ι * (S ^ m * (Kmk * detL Λ)) :=
          mul_le_mul_of_nonneg_right h8m h2
      _ = 16 ^ Fintype.card ι * Kmk * S ^ m * detL Λ := by ring
  have hSm : S ^ (Fintype.card ι - rk Λ) = S ^ m := by rw [hm]
  rw [hSm]
  exact hbnd

end Work.HP

namespace Work.HP

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The set of primitive rank-`r` sublattices of `ℤ^ι` with `λ_{j+1} ≤ s j`. -/
def Tset (r : ℕ) (s : Fin r → ℝ) : Set (Submodule ℤ (ι → ℤ)) :=
  {L | IsPrimLat L ∧ rk L = r ∧ ∀ j : Fin r, lam L (j.1 + 1) ≤ s j}

@[simp] lemma mem_Tset {r : ℕ} {s : Fin r → ℝ} {L : Submodule ℤ (ι → ℤ)} :
    L ∈ Tset r s ↔ IsPrimLat L ∧ rk L = r ∧ ∀ j : Fin r, lam L (j.1 + 1) ≤ s j :=
  Iff.rfl

/-- The cardinality of a finite union of sets is at most the sum of the cardinalities. -/
lemma ncard_biUnion_finset_le {α β : Type*} (F : Finset β) (A : β → Set α) :
    ((⋃ b ∈ (F : Set β), A b).ncard : ℕ) ≤ ∑ b ∈ F, (A b).ncard := by
  classical
  induction F using Finset.induction_on with
  | empty => simp
  | insert a F ha ih =>
      have hsum : (∑ b ∈ insert a F, (A b).ncard)
          = (A a).ncard + ∑ b ∈ F, (A b).ncard := Finset.sum_insert ha
      rw [hsum]
      have h1 : (⋃ b ∈ ((insert a F : Finset β) : Set β), A b)
          = A a ∪ (⋃ b ∈ (F : Set β), A b) := by
        rw [Finset.coe_insert, Set.biUnion_insert]
      rw [h1]
      exact (Set.ncard_union_le _ _).trans (Nat.add_le_add_left ih _)

/-- The successive minimum `λ_{j+1}(Λ)` of a sublattice is bounded by the `(j+1)`-st
successive minimum of the ambient lattice, provided the first `j+1` minimising vectors of the
ambient lattice lie in `Λ`. -/
lemma lam_le_of_lam_le {Λ L : Submodule ℤ (ι → ℤ)} {r : ℕ} (hr : rk L = r + 1)
    {b : Fin r → (ι → ℤ)} (hb_mem : ∀ j, b j ∈ Λ) (hb_ind : LinearIndependent ℤ b)
    (hb_norm : ∀ j, eNorm (b j) ≤ lam L (j.1 + 1))
    {j : Fin r} {x : ℝ} (hx0 : 0 ≤ x) (hx : lam L (j.1 + 1) ≤ x) :
    lam Λ (j.1 + 1) ≤ x := by
  set b' : Fin (j.1 + 1) → (ι → ℤ) := fun k => b ⟨k.1, by omega⟩ with hb'
  have hb'_mem : ∀ k, b' k ∈ Λ := fun k => hb_mem _
  have hb'_ind : LinearIndependent ℤ b' :=
    hb_ind.comp _ (fun a c hac => Fin.ext (by simpa using congrArg Fin.val hac))
  have hb'_norm : ∀ k, eNorm (b' k) ≤ x := by
    intro k
    refine le_trans (hb_norm _) ?_
    refine le_trans (lam_mono_index L (j := k.1 + 1) (k := j.1 + 1) (by omega) ?_) hx
    omega
  exact lam_le_of_tuple hb'_mem hb'_ind hx0 hb'_norm

end Work.HP

namespace Work.HP

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Fibrewise counting: a finite set whose `g`-values land in `F` has cardinality at most the
sum of the cardinalities of its fibres. -/
lemma ncard_le_sum_ncard_fibers {α β : Type*} {S : Set α} (F : Finset β) (g : α → β)
    (hSF : S.Finite) (hg : ∀ x ∈ S, g x ∈ F) :
    S.ncard ≤ ∑ b ∈ F, (S ∩ {x | g x = b}).ncard := by
  classical
  have hsub : S ⊆ (⋃ b ∈ (F : Set β), (S ∩ {x | g x = b})) := by
    intro x hx
    exact Set.mem_iUnion.mpr ⟨g x, Set.mem_iUnion.mpr ⟨hg x hx, hx, rfl⟩⟩
  have hfin : (⋃ b ∈ (F : Set β), (S ∩ {x | g x = b})).Finite :=
    F.finite_toSet.biUnion fun b _ => hSF.subset (Set.inter_subset_left)
  calc S.ncard ≤ (⋃ b ∈ (F : Set β), (S ∩ {x | g x = b})).ncard :=
        Set.ncard_le_ncard hsub hfin
    _ ≤ ∑ b ∈ F, (S ∩ {x | g x = b}).ncard := ncard_biUnion_finset_le F _

/-- For a primitive lattice `Λ`, there is a short vector of `L` outside the saturation of `Λ`,
whenever `L ⊇ Λ`, `L` is primitive, `rk L = rk Λ + 1` and `λ_{rk Λ + 1}(L) ≤ S`. -/
lemma exists_short_outside_satLat {Λ L : Submodule ℤ (ι → ℤ)} (hΛL : Λ ≤ L)
    (hLprim : IsPrimLat L) (hrk : rk L = rk Λ + 1) {S : ℝ} (hS : lam L (rk Λ + 1) ≤ S) :
    ∃ u : ι → ℤ, u ∈ L ∧ u ∉ satLat Λ ∧ eNorm u ≤ S := by
  classical
  obtain ⟨f, hf_mem, hf_ind, hf_norm⟩ := FM.exists_indep_le_lam L
  have hsome : ∃ k, f k ∉ satLat Λ := by
    by_contra hcon
    push_neg at hcon
    have hspan_le : Submodule.span ℤ (Set.range f) ≤ satLat Λ :=
      Submodule.span_le.mpr (by rintro x ⟨k, rfl⟩; exact hcon k)
    have h1 : rk (Submodule.span ℤ (Set.range f)) ≤ rk (satLat Λ) :=
      Submodule.finrank_mono hspan_le
    rw [numaux.rk_span_eq hf_ind, numaux.rk_satLat Λ, hrk] at h1
    omega
  obtain ⟨k, hk⟩ := hsome
  refine ⟨f k, hf_mem k, hk, ?_⟩
  refine le_trans (hf_norm k) ?_
  calc lam L (k.1 + 1) ≤ lam L (rk L) := lam_mono_index L (by omega) le_rfl
    _ = lam L (rk Λ + 1) := by rw [hrk]
    _ ≤ S := hS

/-- The fibre set of `fiber_count` is finite. -/
lemma fiber_finite (Λ : Submodule ℤ (ι → ℤ)) (hΛ : IsPrimLat Λ) (S : ℝ) :
    ({L : Submodule ℤ (ι → ℤ) | Λ ≤ L ∧ IsPrimLat L ∧ rk L = rk Λ + 1 ∧
        lam L (rk Λ + 1) ≤ S}).Finite := by
  classical
  set F : Set (Submodule ℤ (ι → ℤ)) :=
    {L | Λ ≤ L ∧ IsPrimLat L ∧ rk L = rk Λ + 1 ∧ lam L (rk Λ + 1) ≤ S} with hF
  have hex : ∀ L ∈ F, ∃ u : ι → ℤ, u ∈ L ∧ u ∉ satLat Λ ∧ eNorm u ≤ S :=
    fun L hL => exists_short_outside_satLat hL.1 hL.2.1 hL.2.2.1 hL.2.2.2
  let u : (Submodule ℤ (ι → ℤ)) → (ι → ℤ) :=
    fun L => if h : L ∈ F then Classical.choose (hex L h) else 0
  have hu_mem : ∀ L ∈ F, u L ∈ L := by
    intro L hL; simp only [u, dif_pos hL]; exact (Classical.choose_spec (hex L hL)).1
  have hu_not : ∀ L ∈ F, u L ∉ satLat Λ := by
    intro L hL; simp only [u, dif_pos hL]; exact (Classical.choose_spec (hex L hL)).2.1
  have hu_norm : ∀ L ∈ F, eNorm (u L) ≤ S := by
    intro L hL; simp only [u, dif_pos hL]; exact (Classical.choose_spec (hex L hL)).2.2
  have hinj : Set.InjOn u F := by
    intro L hL L' hL' huv
    have h1 := numaux.eq_satLat_sup_span (Λ := Λ) (L := L) hΛ hL.2.1 hL.1 hL.2.2.1
      (hu_mem L hL) (hu_not L hL)
    have h2 := numaux.eq_satLat_sup_span (Λ := Λ) (L := L') hΛ hL'.2.1 hL'.1 hL'.2.2.1
      (hu_mem L' hL') (hu_not L' hL')
    have hspan : Λ ⊔ Submodule.span ℤ ({u L} : Set (ι → ℤ))
        = Λ ⊔ Submodule.span ℤ ({u L'} : Set (ι → ℤ)) := by rw [huv]
    rw [← h1, ← h2, hspan]
  have hfin : ({v : ι → ℤ | eNorm v ≤ S} : Set (ι → ℤ)).Finite := by
    refine (Finset.finite_toSet (Fintype.piFinset
      (fun _ : ι => Finset.Icc (-(Nat.ceil S : ℤ)) (Nat.ceil S)))).subset ?_
    intro v hv
    rw [Finset.mem_coe]
    exact mem_box_of_eNorm_le S hv
  have himg : (u '' F).Finite := hfin.subset (by rintro x ⟨L, hL, rfl⟩; exact hu_norm L hL)
  exact himg.of_finite_image hinj

end Work.HP

namespace Work.HP

variable {ι : Type} [Fintype ι] [DecidableEq ι]

end Work.HP

namespace Work.HP

/-- **The paper's "number lattices" lemma.**  There is a constant `K`, depending only on the
finite type `ι`, such that for every `r` and every `s : Fin r → ℝ` with `s j ≥ 1`, the number of
primitive rank-`r` sublattices `L ⊆ ℤ^ι` with `λ_{j+1}(L) ≤ s j` for all `j` is at most
`K · ∏_j s_j^{N+r+1-2j}`, where `N = card ι`. -/
theorem num_lattices (ι : Type) [Fintype ι] [DecidableEq ι] :
    ∃ K : ℝ, 0 < K ∧ ∀ (r : ℕ) (s : Fin r → ℝ), (∀ j, 1 ≤ s j) →
      (({L : Submodule ℤ (ι → ℤ) | IsPrimLat L ∧ rk L = r ∧
          ∀ j : Fin r, lam L (j.1 + 1) ≤ s j}.ncard : ℝ)
        ≤ K * ∏ j : Fin r, s j ^ (Fintype.card ι + r + 1 - 2 * (j.1 + 1))) := by
  classical
  obtain ⟨Kmk₀, hKmk₀pos, hKmk₀⟩ := numaux.minkowski_prod (ι := ι)
  set Kmk : ℝ := max Kmk₀ 1 with hKmkdef
  have hKmk1 : 1 ≤ Kmk := le_max_right _ _
  have hKmk0 : 0 ≤ Kmk := le_trans zero_le_one hKmk1
  have hKmk : ∀ L : Submodule ℤ (ι → ℤ),
      (∏ j ∈ Finset.range (rk L), lam L (j + 1)) ≤ Kmk * detL L := by
    intro L
    exact le_trans (hKmk₀ L) (mul_le_mul_of_nonneg_right (le_max_left _ _) (detL_nonneg L))
  set c : ℝ := 16 ^ (Fintype.card ι) * Kmk with hcdef
  have hcpos : 0 < c := by
    have h16 : (0:ℝ) < 16 ^ Fintype.card ι := by positivity
    have hKmkpos : 0 < Kmk := lt_of_lt_of_le zero_lt_one hKmk1
    exact mul_pos h16 hKmkpos
  have hcge1 : 1 ≤ c := by
    rw [hcdef]
    have h16 : (1:ℝ) ≤ 16 ^ Fintype.card ι := one_le_pow₀ (by norm_num)
    nlinarith [h16, hKmk1]
  have key : ∀ r : ℕ, r ≤ Fintype.card ι → ∀ s : Fin r → ℝ, (∀ j, 1 ≤ s j) →
      (Tset (ι := ι) r s).Finite ∧ ((Tset (ι := ι) r s).ncard : ℝ) ≤
        c ^ r * ∏ j : Fin r, s j ^ (Fintype.card ι + r + 1 - 2 * (j.1 + 1)) := by
    intro r
    induction r with
    | zero =>
      intro _ s hs
      have hbot : Tset (ι := ι) 0 s ⊆ {⊥} := by
        intro L hL
        obtain ⟨-, hrk, -⟩ := (mem_Tset (ι := ι)).mp hL
        rw [Set.mem_singleton_iff]
        by_contra hne
        have hex : ∃ x : ι → ℤ, x ∈ L ∧ x ≠ 0 := by
          by_contra h
          push_neg at h
          exact hne (le_antisymm (fun x hx => by rw [Submodule.mem_bot]; exact h x hx) bot_le)
        obtain ⟨x, hxL, hx0⟩ := hex
        have hind : LinearIndependent ℤ (fun _ : Fin 1 => (⟨x, hxL⟩ : L)) := by
          rw [linearIndependent_unique_iff]
          simpa using hx0
        have hle := LinearIndependent.fintype_card_le_finrank hind
        simp only [Fintype.card_fin] at hle
        have hpos : 0 < rk L := by
          rw [rk]; omega
        omega
      refine ⟨(Set.finite_singleton ⊥).subset hbot, ?_⟩
      have h1 : (Tset (ι := ι) 0 s).ncard ≤ 1 := by
        have h2 := Set.ncard_le_ncard hbot (Set.finite_singleton ⊥)
        simpa using h2
      have h1R : (((Tset (ι := ι) 0 s).ncard : ℕ) : ℝ) ≤ 1 := by exact_mod_cast h1
      simpa using h1R
    | succ r ih =>
      intro hrN s hs
      set s' : Fin r → ℝ := fun j => s j.castSucc with hs'def
      have hs' : ∀ j : Fin r, 1 ≤ s' j := fun j => hs j.castSucc
      obtain ⟨hTfin, hTbnd⟩ := ih (by omega) s' hs'
      -- the predecessor lattice
      have hex : ∀ L ∈ Tset (ι := ι) (r + 1) s, ∃ Λ : Submodule ℤ (ι → ℤ), Λ ∈ Tset (ι := ι) r s' ∧ Λ ≤ L := by
        intro L hL
        obtain ⟨hLprim, hrkL, hlamL⟩ := (mem_Tset (ι := ι)).mp hL
        obtain ⟨f, hf_mem, hf_ind, hf_norm⟩ := FM.exists_indep_le_lam L
        set b : Fin r → (ι → ℤ) := fun j => f (Fin.castLE (by omega : r + 1 ≤ rk L) j.castSucc)
          with hbdef
        have hb_ind : LinearIndependent ℤ b := by
          rw [hbdef]
          refine hf_ind.comp
            (fun j : Fin r => Fin.castLE (by omega : r + 1 ≤ rk L) j.castSucc) ?_
          intro a c hac
          have h1 := congrArg Fin.val hac
          simp only [Fin.val_castLE, Fin.val_castSucc] at h1
          exact Fin.ext h1
        have hb_mem : ∀ j, b j ∈ L := fun j => hf_mem _
        have hb_norm : ∀ j, eNorm (b j) ≤ lam L (j.1 + 1) := fun j => hf_norm _
        set Λ : Submodule ℤ (ι → ℤ) := satLat (Submodule.span ℤ (Set.range b)) with hΛdef
        have hspan_le : Submodule.span ℤ (Set.range b) ≤ L :=
          Submodule.span_le.mpr (by rintro x ⟨j, rfl⟩; exact hb_mem j)
        have hΛL : Λ ≤ L := by
          rw [hΛdef]
          exact (satLat_mono hspan_le).trans (le_of_eq (satLat_eq_of_isPrimLat hLprim))
        have hΛprim : IsPrimLat Λ := isPrimLat_satLat _
        have hrkΛ : rk Λ = r := by
          rw [hΛdef, numaux.rk_satLat (Submodule.span ℤ (Set.range b)),
            numaux.rk_span_eq hb_ind]
        have hlamΛ : ∀ j : Fin r, lam Λ (j.1 + 1) ≤ s' j := by
          intro j
          refine lam_le_of_lam_le (Λ := Λ) (L := L) hrkL (b := b) (j := j) (x := s' j) ?_ hb_ind
            hb_norm (le_trans zero_le_one (hs' j)) (hlamL j.castSucc)
          intro k
          rw [hΛdef]
          exact le_satLat _ (Submodule.subset_span ⟨k, rfl⟩)
        exact ⟨Λ, ⟨hΛprim, hrkΛ, hlamΛ⟩, hΛL⟩
      let Φ : (Submodule ℤ (ι → ℤ)) → (Submodule ℤ (ι → ℤ)) :=
        fun L => if h : L ∈ Tset (ι := ι) (r + 1) s then Classical.choose (hex L h) else ⊥
      have hΦ : ∀ L ∈ Tset (ι := ι) (r + 1) s, Φ L ∈ Tset (ι := ι) r s' ∧ Φ L ≤ L := by
        intro L hL
        simp only [Φ, dif_pos hL]
        exact Classical.choose_spec (hex L hL)
      haveI hFintype : Fintype ↥(Tset (ι := ι) r s') := hTfin.fintype
      set F : Finset (Submodule ℤ (ι → ℤ)) := (Tset (ι := ι) r s').toFinset with hFdef
      -- finiteness of the top set, via the covering by fibres
      have hTfin' : (Tset (ι := ι) (r + 1) s).Finite := by
        have hcov : Tset (ι := ι) (r + 1) s ⊆ ⋃ Λ ∈ (F : Set (Submodule ℤ (ι → ℤ))),
            {L : Submodule ℤ (ι → ℤ) | Λ ≤ L ∧ IsPrimLat L ∧ rk L = rk Λ + 1 ∧
              lam L (rk Λ + 1) ≤ s (Fin.last r)} := by
          intro L hL
          obtain ⟨hLprim, hrkL, hlamL⟩ := (mem_Tset (ι := ι)).mp hL
          obtain ⟨hΦmem, hΦle⟩ := hΦ L hL
          obtain ⟨hΦprim, hrkΦ, -⟩ := (mem_Tset (ι := ι)).mp hΦmem
          refine Set.mem_iUnion.mpr ⟨Φ L, Set.mem_iUnion.mpr ⟨?_, hΦle, hLprim, ?_, ?_⟩⟩
          · rw [hFdef]; exact Set.mem_toFinset.mpr hΦmem
          · rw [hrkL, hrkΦ]
          · simpa [hrkΦ, Fin.val_last] using hlamL (Fin.last r)
        refine (F.finite_toSet.biUnion ?_).subset hcov
        intro Λ hΛ
        refine fiber_finite Λ ?_ (s (Fin.last r))
        have hΛmem : Λ ∈ Tset (ι := ι) r s' := Set.mem_toFinset.mp (by rwa [hFdef] at hΛ)
        exact hΛmem.1
      -- the fibre bound
      have hfib : ∀ Λ ∈ F, (((Tset (ι := ι) (r + 1) s ∩ {L | Φ L = Λ}).ncard : ℕ) : ℝ)
          ≤ 16 ^ Fintype.card ι * Kmk * (s (Fin.last r)) ^ (Fintype.card ι - r) * detL Λ := by
        intro Λ hΛ
        have hΛmem : Λ ∈ Tset (ι := ι) r s' := Set.mem_toFinset.mp (by rwa [hFdef] at hΛ)
        obtain ⟨hΛprim, hrkΛ, -⟩ := (mem_Tset (ι := ι)).mp hΛmem
        have hsub : Tset (ι := ι) (r + 1) s ∩ {L | Φ L = Λ} ⊆
            {L : Submodule ℤ (ι → ℤ) | Λ ≤ L ∧ IsPrimLat L ∧ rk L = r + 1 ∧
              lam L (r + 1) ≤ s (Fin.last r)} := by
          rintro L ⟨hL, hΦL⟩
          have h1 := hΦ L hL
          rw [hΦL] at h1
          obtain ⟨hLprim, hrkL, hlamL⟩ := (mem_Tset (ι := ι)).mp hL
          refine ⟨h1.2, hLprim, ?_, ?_⟩
          · rw [hrkL]
          · simpa [Fin.val_last] using hlamL (Fin.last r)
        have h1 : (Tset (ι := ι) (r + 1) s ∩ {L | Φ L = Λ}).ncard ≤
            ({L : Submodule ℤ (ι → ℤ) | Λ ≤ L ∧ IsPrimLat L ∧ rk L = r + 1 ∧
              lam L (r + 1) ≤ s (Fin.last r)}).ncard :=
          Set.ncard_le_ncard hsub (by simpa [hrkΛ] using fiber_finite Λ hΛprim (s (Fin.last r)))
        have h2 := fiber_count Kmk hKmk0 Λ hΛprim (s (Fin.last r)) (hs (Fin.last r)) hKmk
        rw [hrkΛ] at h2
        have h3 : (((Tset (ι := ι) (r + 1) s ∩ {L | Φ L = Λ}).ncard : ℕ) : ℝ) ≤
            (({L : Submodule ℤ (ι → ℤ) | Λ ≤ L ∧ IsPrimLat L ∧ rk L = r + 1 ∧
              lam L (r + 1) ≤ s (Fin.last r)}).ncard : ℝ) := by exact_mod_cast h1
        exact h3.trans h2
      have hstep1 : (((Tset (ι := ι) (r + 1) s).ncard : ℕ) : ℝ) ≤
          ∑ Λ ∈ F, (((Tset (ι := ι) (r + 1) s ∩ {L | Φ L = Λ}).ncard : ℕ) : ℝ) := by
        have hg : ∀ L ∈ Tset (ι := ι) (r + 1) s, Φ L ∈ F := by
          intro L hL; rw [hFdef]; exact Set.mem_toFinset.mpr (hΦ L hL).1
        have h1 := ncard_le_sum_ncard_fibers F Φ hTfin' hg
        exact_mod_cast h1
      have hstep2 : ∑ Λ ∈ F, (((Tset (ι := ι) (r + 1) s ∩ {L | Φ L = Λ}).ncard : ℕ) : ℝ)
          ≤ ∑ Λ ∈ F,
              (16 ^ Fintype.card ι * Kmk * (s (Fin.last r)) ^ (Fintype.card ι - r) * detL Λ) :=
        Finset.sum_le_sum hfib
      have hdet : ∀ Λ ∈ F, detL Λ ≤ ∏ j : Fin r, s' j := by
        intro Λ hΛ
        have hΛmem : Λ ∈ Tset (ι := ι) r s' := Set.mem_toFinset.mp (by rwa [hFdef] at hΛ)
        have hmink := FM.minkowski_lower Λ
        rw [hΛmem.2.1] at hmink
        refine hmink.trans ?_
        have hconv : (∏ j : Fin r, lam Λ (j.1 + 1)) = ∏ i ∈ Finset.range r, lam Λ (i + 1) :=
          Fin.prod_univ_eq_prod_range (fun i => lam Λ (i + 1)) r
        rw [← hconv]
        exact Finset.prod_le_prod₀ (fun j _ => lam_nonneg Λ (j.1 + 1)) (fun j _ => hΛmem.2.2 j)
      have hcardF : (F.card : ℝ) ≤
          c ^ r * ∏ j : Fin r, (s' j) ^ (Fintype.card ι + r + 1 - 2 * (j.1 + 1)) := by
        have h1 : (F.card : ℝ) = ((Tset (ι := ι) r s').ncard : ℝ) := by
          rw [hFdef, Set.ncard_eq_toFinset_card']
        rw [h1]; exact hTbnd
      have hstep3 : ∑ Λ ∈ F, (16 ^ Fintype.card ι * Kmk * (s (Fin.last r)) ^ (Fintype.card ι - r)
            * detL Λ)
          ≤ 16 ^ Fintype.card ι * Kmk * (s (Fin.last r)) ^ (Fintype.card ι - r)
            * (c ^ r * ((∏ j : Fin r, (s' j) ^ (Fintype.card ι + r + 1 - 2 * (j.1 + 1)))
                * (∏ j : Fin r, s' j))) := by
        rw [← Finset.mul_sum]
        have hsum : ∑ Λ ∈ F, detL Λ ≤ (F.card : ℝ) * ∏ j : Fin r, s' j := by
          calc ∑ Λ ∈ F, detL Λ ≤ ∑ Λ ∈ F, ∏ j : Fin r, s' j := Finset.sum_le_sum hdet
            _ = (F.card : ℝ) * ∏ j : Fin r, s' j := by
                rw [Finset.sum_const, nsmul_eq_mul]
        have hconst : (0:ℝ) ≤ 16 ^ Fintype.card ι * Kmk * (s (Fin.last r)) ^ (Fintype.card ι - r) :=
          mul_nonneg (mul_nonneg (by positivity) hKmk0)
            (pow_nonneg (le_trans zero_le_one (hs (Fin.last r))) _)
        calc 16 ^ Fintype.card ι * Kmk * (s (Fin.last r)) ^ (Fintype.card ι - r) * ∑ Λ ∈ F, detL Λ
            ≤ 16 ^ Fintype.card ι * Kmk * (s (Fin.last r)) ^ (Fintype.card ι - r)
              * ((F.card : ℝ) * ∏ j : Fin r, s' j) :=
              mul_le_mul_of_nonneg_left hsum hconst
          _ ≤ 16 ^ Fintype.card ι * Kmk * (s (Fin.last r)) ^ (Fintype.card ι - r)
              * ((c ^ r * ∏ j : Fin r, (s' j) ^ (Fintype.card ι + r + 1 - 2 * (j.1 + 1)))
                * ∏ j : Fin r, s' j) := by
              refine mul_le_mul_of_nonneg_left ?_ hconst
              exact mul_le_mul_of_nonneg_right hcardF
                (Finset.prod_nonneg fun j _ => le_trans zero_le_one (hs' j))
          _ = 16 ^ Fintype.card ι * Kmk * (s (Fin.last r)) ^ (Fintype.card ι - r)
              * (c ^ r * ((∏ j : Fin r, (s' j) ^ (Fintype.card ι + r + 1 - 2 * (j.1 + 1)))
                * (∏ j : Fin r, s' j))) := by ring
      -- assemble
      refine ⟨hTfin', ?_⟩
      have hexp : (∏ j : Fin (r + 1), s j ^ (Fintype.card ι + (r + 1) + 1 - 2 * (j.1 + 1)))
          = (∏ j : Fin r, (s' j) ^ (Fintype.card ι + r + 1 - 2 * (j.1 + 1)))
            * (∏ j : Fin r, s' j) * (s (Fin.last r)) ^ (Fintype.card ι - r) := by
        rw [Fin.prod_univ_castSucc]
        have h1 : (∏ j : Fin r,
              s j.castSucc ^ (Fintype.card ι + (r + 1) + 1 - 2 * ((j.castSucc).1 + 1)))
            = (∏ j : Fin r, (s' j) ^ (Fintype.card ι + r + 1 - 2 * (j.1 + 1)))
              * (∏ j : Fin r, s' j) := by
          rw [← Finset.prod_mul_distrib]
          refine Finset.prod_congr rfl ?_
          intro j _
          have h2 : (Fintype.card ι + (r + 1) + 1 - 2 * ((j.castSucc).1 + 1))
              = (Fintype.card ι + r + 1 - 2 * (j.1 + 1)) + 1 := by
            simp only [Fin.val_castSucc]; omega
          rw [h2, pow_succ]
        have h3 : (Fintype.card ι + (r + 1) + 1 - 2 * ((Fin.last r).1 + 1))
            = Fintype.card ι - r := by
          simp only [Fin.val_last]; omega
        rw [h1, h3]
      rw [hexp]
      calc (((Tset (ι := ι) (r + 1) s).ncard : ℕ) : ℝ)
          ≤ ∑ Λ ∈ F, (((Tset (ι := ι) (r + 1) s ∩ {L | Φ L = Λ}).ncard : ℕ) : ℝ) := hstep1
        _ ≤ ∑ Λ ∈ F, (16 ^ Fintype.card ι * Kmk * (s (Fin.last r)) ^ (Fintype.card ι - r)
              * detL Λ) := hstep2
        _ ≤ 16 ^ Fintype.card ι * Kmk * (s (Fin.last r)) ^ (Fintype.card ι - r)
            * (c ^ r * ((∏ j : Fin r, (s' j) ^ (Fintype.card ι + r + 1 - 2 * (j.1 + 1)))
              * (∏ j : Fin r, s' j))) := hstep3
        _ = c ^ (r + 1) * ((∏ j : Fin r, (s' j) ^ (Fintype.card ι + r + 1 - 2 * (j.1 + 1)))
              * (∏ j : Fin r, s' j) * (s (Fin.last r)) ^ (Fintype.card ι - r)) := by
            rw [hcdef, pow_succ]; ring
  refine ⟨max (c ^ Fintype.card ι) 1, ?_, ?_⟩
  · have h16 : (0:ℝ) < 16 ^ Fintype.card ι := by positivity
    have h1 : 0 < c ^ Fintype.card ι := pow_pos hcpos _
    exact lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  · intro r s hs
    change ((Tset (ι := ι) r s).ncard : ℝ) ≤ max (c ^ Fintype.card ι) 1 * ∏ j : Fin r,
      s j ^ (Fintype.card ι + r + 1 - 2 * (j.1 + 1))
    by_cases hr : r ≤ Fintype.card ι
    · have h1 := (key r hr s hs).2
      refine h1.trans ?_
      refine mul_le_mul_of_nonneg_right ?_ (Finset.prod_nonneg fun j _ => ?_)
      · calc c ^ r ≤ c ^ Fintype.card ι := pow_le_pow_right₀ hcge1 hr
          _ ≤ max (c ^ Fintype.card ι) 1 := le_max_left _ _
      · exact pow_nonneg (le_trans zero_le_one (hs j)) _
    · have hempty : Tset (ι := ι) r s = ∅ := by
        refine Set.subset_empty_iff.mp ?_
        intro L hL
        obtain ⟨-, hrk, -⟩ := (mem_Tset (ι := ι)).mp hL
        have := rk_le_card L
        omega
      rw [hempty]
      simp only [Set.ncard_empty, Nat.cast_zero]
      exact mul_nonneg (le_trans zero_le_one (le_max_right _ _))
        (Finset.prod_nonneg fun j _ => pow_nonneg (le_trans zero_le_one (hs j)) _)

end Work.HP
