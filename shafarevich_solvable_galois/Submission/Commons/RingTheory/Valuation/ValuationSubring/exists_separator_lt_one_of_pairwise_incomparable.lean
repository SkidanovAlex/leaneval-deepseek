import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.ValuationSubring
import Submission.Commons.RingTheory.Valuation.combine_clusters
import Submission.Commons.RingTheory.Valuation.exists_cluster_decomposition_nonempty
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.RingTheory.Valuation.ValuationSubring

open ValuationSubring

/-! ## Residue-field descent machinery -/

private noncomputable def resImage {L : Type*} [Field L] (C E : ValuationSubring L) (h : C ≤ E) :
    Subring (IsLocalRing.ResidueField E) :=
  Subring.map ((IsLocalRing.residue E).comp (Subring.inclusion h)) ⊤

private theorem resImage_mem_or_inv_mem {L : Type*} [Field L] (C E : ValuationSubring L) (h : C ≤ E) :
    ∀ y : IsLocalRing.ResidueField E, y ∈ resImage C E h ∨ y⁻¹ ∈ resImage C E h := by
  intro y
  obtain ⟨z, rfl⟩ := IsLocalRing.residue_surjective y
  rcases C.mem_or_inv_mem (z : L) with hz | hz
  · exact Or.inl (Subring.mem_map.mpr ⟨⟨(z:L), hz⟩, Subring.mem_top _, rfl⟩)
  · rcases eq_or_ne (z : L) 0 with hz0 | hz0
    · refine Or.inl ?_
      have hzE0 : z = 0 := Subtype.ext hz0
      rw [hzE0, map_zero]
      exact (resImage C E h).zero_mem
    · refine Or.inr ?_
      have hzE : ((z : L))⁻¹ ∈ E := h hz
      set w : E := ⟨(z:L)⁻¹, hzE⟩ with hw
      have hzw : z * w = 1 := by
        ext
        show (z:L) * (z:L)⁻¹ = (1:L)
        exact mul_inv_cancel₀ hz0
      have hyinv : (IsLocalRing.residue E z)⁻¹ = IsLocalRing.residue E w := by
        have h1 : IsLocalRing.residue E z * IsLocalRing.residue E w = 1 := by
          rw [← map_mul, hzw, map_one]
        exact inv_eq_of_mul_eq_one_right h1
      rw [hyinv]
      exact Subring.mem_map.mpr ⟨⟨(z:L)⁻¹, hz⟩, Subring.mem_top _, rfl⟩

private noncomputable def resValuation {L : Type*} [Field L] (C E : ValuationSubring L) (h : C ≤ E) :
    ValuationSubring (IsLocalRing.ResidueField E) :=
  ValuationSubring.ofSubring (resImage C E h) (resImage_mem_or_inv_mem C E h)

private theorem mem_resValuation {L : Type*} [Field L] (C E : ValuationSubring L) (h : C ≤ E)
    (y : IsLocalRing.ResidueField E) : y ∈ resValuation C E h ↔ y ∈ resImage C E h :=
  ValuationSubring.mem_ofSubring _ _ y

-- (A) elements of m_E are in every C ≤ E.
private theorem mem_of_maximalIdeal {L : Type*} [Field L] (C E : ValuationSubring L) (h : C ≤ E)
    {x : E} (hx : x ∈ IsLocalRing.maximalIdeal E) : (x : L) ∈ C := by
  have hx' : E.valuation (x : L) < 1 := (ValuationSubring.valuation_lt_one_iff (A := E) x).mp hx
  have hlt := (ValuationSubring.le_iff_forall_valuation_lt_one C E).mp h (x:L) hx'
  exact (ValuationSubring.valuation_le_one_iff C (x:L)).mp (le_of_lt hlt)

-- (B) for x ∉ m_E, membership in C is detected on the residue.
private theorem mem_iff_residue {L : Type*} [Field L] (C E : ValuationSubring L) (h : C ≤ E)
    {x : E} (hx : x ∉ IsLocalRing.maximalIdeal E) :
    (x : L) ∈ C ↔ IsLocalRing.residue E x ∈ resValuation C E h := by
  rw [mem_resValuation, resImage, Subring.mem_map]
  constructor
  · intro hxc
    exact ⟨⟨(x:L), hxc⟩, Subring.mem_top _, rfl⟩
  · rintro ⟨w, -, hw⟩
    have hsub : x - (Subring.inclusion h) w ∈ IsLocalRing.maximalIdeal E := by
      rw [← IsLocalRing.ker_residue, RingHom.mem_ker, map_sub]
      have hw' : IsLocalRing.residue E ((Subring.inclusion h) w) = IsLocalRing.residue E x := hw
      rw [hw', sub_self]
    have hmemC : ((x - (Subring.inclusion h) w : E) : L) ∈ C := mem_of_maximalIdeal C E h hsub
    have hwC : ((Subring.inclusion h w : E) : L) ∈ C := w.2
    have : (x : L) = ((Subring.inclusion h w : E) : L) + ((x - (Subring.inclusion h) w : E) : L) := by
      push_cast; ring
    rw [this]
    exact C.add_mem _ _ hwC hmemC

private theorem le_of_resValuation_le {L : Type*} [Field L] {C D E : ValuationSubring L}
    (hC : C ≤ E) (hD : D ≤ E)
    (h : resValuation C E hC ≤ resValuation D E hD) : C ≤ D := by
  intro a ha
  have haE : a ∈ E := hC ha
  by_cases hx : (⟨a, haE⟩ : E) ∈ IsLocalRing.maximalIdeal E
  · exact mem_of_maximalIdeal D E hD hx
  · have h1 : IsLocalRing.residue E (⟨a, haE⟩ : E) ∈ resValuation C E hC :=
      (mem_iff_residue C E hC (x := ⟨a, haE⟩) hx).mp ha
    have h2 : IsLocalRing.residue E (⟨a, haE⟩ : E) ∈ resValuation D E hD := h h1
    exact (mem_iff_residue D E hD (x := ⟨a, haE⟩) hx).mpr h2

private theorem eq_top_of_resValuation_eq_top {L : Type*} [Field L] {C E : ValuationSubring L}
    (hC : C ≤ E) (h : resValuation C E hC = ⊤) : C = E := by
  apply le_antisymm hC
  intro a ha
  by_cases hx : (⟨a, ha⟩ : E) ∈ IsLocalRing.maximalIdeal E
  · exact mem_of_maximalIdeal C E hC hx
  · have hmem : IsLocalRing.residue E ⟨a, ha⟩ ∈ resValuation C E hC := by
      rw [h]; exact ValuationSubring.mem_top _
    exact (mem_iff_residue C E hC (x := ⟨a, ha⟩) hx).mpr hmem

end Commons.RingTheory.Valuation.ValuationSubring

namespace Commons.RingTheory.Valuation.ValuationSubring

open ValuationSubring

private theorem valuation_lt_one_of_residue_lt {L : Type*} [Field L] (C E : ValuationSubring L)
    (h : C ≤ E) {x : E} (hx : x ∉ IsLocalRing.maximalIdeal E)
    (hres : (resValuation C E h).valuation (IsLocalRing.residue E x) < 1) :
    C.valuation (x : L) < 1 := by
  set W := resValuation C E h with hW
  set z := IsLocalRing.residue E x with hz
  have hzW : z ∈ W := (W.valuation_le_one_iff z).mp (le_of_lt hres)
  have hxC : (x : L) ∈ C := (mem_iff_residue C E h hx).mpr hzW
  have hzne : z ≠ 0 := fun h0 => hx ((IsLocalRing.residue_eq_zero_iff x).mp h0)
  have hxne : (x : L) ≠ 0 := by
    rintro h0
    exact hx (by rw [show x = 0 from Subtype.ext h0]; exact (IsLocalRing.maximalIdeal E).zero_mem)
  by_contra hcon
  have hge : 1 ≤ C.valuation (x : L) := not_lt.mp hcon
  have hle1 : C.valuation (x : L) ≤ 1 := (C.valuation_le_one_iff _).mpr hxC
  have heq1 : C.valuation (x : L) = 1 := le_antisymm hle1 hge
  -- `(x:L)` is a unit of `C`, so `(x:L)⁻¹ ∈ C`
  have hunitC : IsUnit (⟨(x : L), hxC⟩ : C) := (C.valuation_eq_one_iff _).mpr heq1
  obtain ⟨u, hu⟩ := hunitC
  have hxinvC : (x : L)⁻¹ ∈ C := by
    have h1 : ((u⁻¹ : Cˣ) : C) * (⟨(x : L), hxC⟩ : C) = 1 := by rw [← hu]; simp
    have h2 : (((u⁻¹ : Cˣ) : C) : L) * (x : L) = 1 := by
      have := congrArg (fun w : C => (w : L)) h1
      simpa using this
    have h3 : (((u⁻¹ : Cˣ) : C) : L) = (x : L)⁻¹ := eq_inv_of_mul_eq_one_left h2
    rw [← h3]; exact ((u⁻¹ : Cˣ) : C).2
  -- `z⁻¹ ∈ W`
  have hzinvW : z⁻¹ ∈ W := by
    rw [hW, mem_resValuation, resImage, Subring.mem_map]
    refine ⟨⟨(x : L)⁻¹, hxinvC⟩, Subring.mem_top _, ?_⟩
    have hcx : (Subring.inclusion h ⟨(x : L)⁻¹, hxinvC⟩) * x = 1 := by
      ext
      show (x : L)⁻¹ * (x : L) = 1
      exact inv_mul_cancel₀ hxne
    have hres' := congrArg (IsLocalRing.residue E) hcx
    rw [map_mul, map_one] at hres'
    rw [hz]
    exact eq_inv_of_mul_eq_one_left hres'
  -- `z` is a unit of `W`, contradicting `z ∈ W.nonunits`
  have hznot : ¬ IsUnit (⟨z, hzW⟩ : W) := by
    have : (⟨z, hzW⟩ : W) ∈ IsLocalRing.maximalIdeal W := by
      rw [← ValuationSubring.coe_mem_nonunits_iff]
      exact (W.mem_nonunits_iff).mpr hres
    rwa [IsLocalRing.mem_maximalIdeal] at this
  have hunitW : IsUnit (⟨z, hzW⟩ : W) := by
    refine IsUnit.of_mul_eq_one (b := ⟨z⁻¹, hzinvW⟩) ?_
    ext
    show z * z⁻¹ = 1
    exact mul_inv_cancel₀ hzne
  exact hznot hunitW

private noncomputable def compositeSubring {L : Type*} [Field L] (E : ValuationSubring L)
    (W : ValuationSubring (IsLocalRing.ResidueField E)) : Subring L :=
  (Subring.comap (IsLocalRing.residue E) W.toSubring).map (Subring.subtype E.toSubring)

private theorem mem_compositeSubring {L : Type*} [Field L] (E : ValuationSubring L)
    (W : ValuationSubring (IsLocalRing.ResidueField E)) (x : L) :
    x ∈ compositeSubring E W ↔ ∃ (y : E), IsLocalRing.residue E y ∈ W ∧ (y : L) = x := by
  rw [compositeSubring, Subring.mem_map]
  constructor
  · rintro ⟨y, hy, hyx⟩
    exact ⟨y, by rwa [Subring.mem_comap] at hy, hyx⟩
  · rintro ⟨y, hy, hyx⟩
    exact ⟨y, by rw [Subring.mem_comap]; exact hy, hyx⟩

private theorem compositeSubring_val {L : Type*} [Field L] (E : ValuationSubring L)
    (W : ValuationSubring (IsLocalRing.ResidueField E)) :
    ∀ x : L, x ∈ compositeSubring E W ∨ x⁻¹ ∈ compositeSubring E W := by
  intro x
  by_cases hx : x ∈ E
  · by_cases hx0 : (⟨x, hx⟩ : E) ∈ IsLocalRing.maximalIdeal E
    · left
      rw [mem_compositeSubring]
      exact ⟨⟨x, hx⟩, by rw [(IsLocalRing.residue_eq_zero_iff _).mpr hx0]; exact W.zero_mem, rfl⟩
    · have hxu : IsUnit (⟨x, hx⟩ : E) := by
        by_contra hc
        exact hx0 ((IsLocalRing.mem_maximalIdeal _).mpr (by simpa using hc))
      obtain ⟨u, hu⟩ := hxu
      rcases W.mem_or_inv_mem (IsLocalRing.residue E (⟨x, hx⟩ : E)) with hW | hW
      · left; rw [mem_compositeSubring]; exact ⟨⟨x, hx⟩, hW, rfl⟩
      · right
        rw [mem_compositeSubring]
        refine ⟨(u⁻¹ : Eˣ), ?_, ?_⟩
        · have h1 : ((u⁻¹ : Eˣ) : E) * (⟨x, hx⟩ : E) = 1 := by rw [← hu]; simp
          have h2 := congrArg (IsLocalRing.residue E) h1
          rw [map_mul, map_one] at h2
          rw [eq_inv_of_mul_eq_one_left h2]
          exact hW
        · have h1 : (((u⁻¹ : Eˣ) : E) : L) * x = 1 := by
            have := congrArg (fun w : E => (w : L))
              (show ((u⁻¹ : Eˣ) : E) * (⟨x, hx⟩ : E) = 1 by rw [← hu]; simp)
            simpa using this
          exact eq_inv_of_mul_eq_one_left h1
  · right
    have hxinv : x⁻¹ ∈ E := (E.mem_or_inv_mem x).resolve_left hx
    rw [mem_compositeSubring]
    refine ⟨⟨x⁻¹, hxinv⟩, ?_, rfl⟩
    have hxinv0 : (⟨x⁻¹, hxinv⟩ : E) ∈ IsLocalRing.maximalIdeal E := by
      rw [IsLocalRing.mem_maximalIdeal]
      intro hunit
      obtain ⟨v, hv⟩ := hunit
      apply hx
      have hgen : x⁻¹ * (((v⁻¹ : Eˣ) : E) : L) = 1 := by
        have := congrArg (fun w : E => (w : L))
          (show (⟨x⁻¹, hxinv⟩ : E) * ((v⁻¹ : Eˣ) : E) = 1 by rw [← hv]; simp)
        simpa using this
      have : (((v⁻¹ : Eˣ) : E) : L) = x := by
        have := eq_inv_of_mul_eq_one_right hgen
        rwa [inv_inv] at this
      rw [← this]; exact ((v⁻¹ : Eˣ) : E).2
    rw [(IsLocalRing.residue_eq_zero_iff _).mpr hxinv0]; exact W.zero_mem

private theorem sup_resValuation_eq_top {L : Type*} [Field L] {ι : Type*} [Fintype ι] [Nonempty ι]
    (C : ι → ValuationSubring L) (E : ValuationSubring L) (hle : ∀ k, C k ≤ E)
    (hE : E = Finset.univ.sup' Finset.univ_nonempty C) :
    Finset.univ.sup' Finset.univ_nonempty (fun k => resValuation (C k) E (hle k)) = ⊤ := by
  classical
  set W : ValuationSubring (IsLocalRing.ResidueField E) :=
    Finset.univ.sup' Finset.univ_nonempty (fun k => resValuation (C k) E (hle k)) with hW
  set D0 : ValuationSubring L := ValuationSubring.ofSubring (compositeSubring E W)
    (compositeSubring_val E W) with hD0
  have hCD : ∀ k, C k ≤ D0 := by
    intro k x hx
    rw [hD0, ValuationSubring.mem_ofSubring, mem_compositeSubring]
    refine ⟨⟨x, hle k hx⟩, ?_, rfl⟩
    have hmem : IsLocalRing.residue E (⟨x, hle k hx⟩ : E) ∈ resValuation (C k) E (hle k) := by
      rw [mem_resValuation]
      exact Subring.mem_map.mpr ⟨⟨x, hx⟩, Subring.mem_top _, rfl⟩
    rw [hW]
    exact Finset.le_sup' (f := fun j => resValuation (C j) E (hle j)) (Finset.mem_univ k) hmem
  have hED : E ≤ D0 := by
    rw [hE]
    exact (Finset.sup'_le_iff Finset.univ_nonempty C).mpr (fun k _ => hCD k)
  have hDE : D0 ≤ E := by
    intro x hx
    rw [hD0, ValuationSubring.mem_ofSubring, mem_compositeSubring] at hx
    obtain ⟨y, -, hyx⟩ := hx
    rw [← hyx]; exact y.2
  have hEeq : E = D0 := le_antisymm hED hDE
  rw [hW]
  apply le_antisymm le_top
  intro y _
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective y
  have hxD : (x : L) ∈ D0 := hEeq.le x.2
  rw [hD0, ValuationSubring.mem_ofSubring, mem_compositeSubring] at hxD
  obtain ⟨z, hz, hzx⟩ := hxD
  have hres : IsLocalRing.residue E x = IsLocalRing.residue E z :=
    congrArg (IsLocalRing.residue E) (Subtype.ext hzx.symm)
  rw [hres]; exact hz

end Commons.RingTheory.Valuation.ValuationSubring

namespace Commons.RingTheory.Valuation.ValuationSubring

open ValuationSubring

/-- **Glueing step.**  Given a pairwise-incomparable family `C` regrouped into independent
clusters `E ∘ f`, and a solution `τ` of the target problem for the cluster of `i`, produce a
solution for the whole family. -/
private lemma glue {L : Type*} [Field L] {ι σ : Type*} [Fintype ι] [Fintype σ] [Nonempty σ]
    (C : ι → ValuationSubring L) (f : ι → σ) (E : σ → ValuationSubring L)
    (hle : ∀ k, C k ≤ E (f k)) (hind : ∀ s t, s ≠ t → E s ⊔ E t = ⊤)
    (hne : ∀ s, E s ≠ ⊤) (i : ι) {τ : L}
    (hτ1 : (C i).valuation τ > 1)
    (hτ2 : ∀ k, f k = f i → k ≠ i → (C k).valuation τ < 1) :
    ∃ x : L, (C i).valuation x > 1 ∧ ∀ k, k ≠ i → (C k).valuation x < 1 := by
  classical
  let a : ι → L := fun k => if f k = f i then τ else 0
  obtain ⟨x0, hx0⟩ :=
    Commons.RingTheory.Valuation.combine_clusters C f E a (fun _ => (1 : L))
      (fun _ => one_ne_zero) hle hind hne
      (fun s => if s = f i then τ else 0)
      (by
        intro s k hk
        rw [Valuation.map_one]
        have hxa : (if s = f i then τ else 0) - a k = 0 := by
          have hak : a k = (if s = f i then τ else 0) := by
            rw [show a k = (if f k = f i then τ else 0) from rfl, hk]
          rw [hak, sub_self]
        rw [hxa, Valuation.map_zero]
        exact zero_lt_one)
  refine ⟨x0, ?_, ?_⟩
  · have hai : a i = τ := by simp [a]
    have hlt := hx0 i
    rw [hai] at hlt
    have h1 : (C i).valuation (x0 - τ) < (C i).valuation τ := lt_trans hlt hτ1
    have heq : (C i).valuation x0 = (C i).valuation τ := by
      have hx0' : x0 = (x0 - τ) + τ := by ring
      rw [hx0']
      exact Valuation.map_add_eq_of_lt_right _ h1
    rw [heq]; exact hτ1
  · intro k hk
    by_cases hfk : f k = f i
    · have hak : a k = τ := by simp [a, hfk]
      have hlt := hx0 k
      rw [hak] at hlt
      have h2 : (C k).valuation τ < 1 := hτ2 k hfk hk
      have hx0' : x0 = (x0 - τ) + τ := by ring
      rw [hx0']
      exact lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt hlt h2)
    · have hak : a k = 0 := by simp [a, hfk]
      have hlt := hx0 k
      rw [hak, sub_zero] at hlt
      exact hlt

/-- **Main induction.**  The separator theorem for a pairwise-incomparable finite family, by
strong induction on the cardinality of the index set, using the cluster decomposition and
descent to the residue field in the single-cluster case. -/
private theorem main_gen :
    ∀ (n : ℕ) {F : Type*} [Field F] {ι : Type} [Fintype ι] [Nonempty ι]
      (C : ι → ValuationSubring F) (hnt : ∀ i, C i ≠ ⊤)
      (hincomp : ∀ i j, i ≠ j → ¬ (C i ≤ C j)) (i : ι),
      Nat.card ι = n →
      ∃ τ : F, (C i).valuation τ > 1 ∧ ∀ k, k ≠ i → (C k).valuation τ < 1 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro F _ ι _ _ C hnt hincomp i hcard
    classical
    by_cases hn : n ≤ 1
    · have hcard1 : Fintype.card ι ≤ 1 := by rw [← Nat.card_eq_fintype_card]; omega
      have hall : ∀ a b : ι, a = b := Fintype.card_le_one_iff.mp hcard1
      obtain ⟨τ, hτ⟩ := Commons.RingTheory.Valuation.exists_valuation_gt_one (C i) (hnt i)
      exact ⟨τ, hτ, fun k hk => absurd (hall k i) hk⟩
    · push_neg at hn
      -- Descend to the residue field of the supremum of the family.
      set E0 : ValuationSubring F := Finset.univ.sup' Finset.univ_nonempty C with hE0
      have hle0 : ∀ k, C k ≤ E0 := fun k => Finset.le_sup' C (Finset.mem_univ k)
      let W : ι → ValuationSubring (IsLocalRing.ResidueField E0) :=
        fun k => resValuation (C k) E0 (hle0 k)
      have hntW : ∀ k, W k ≠ ⊤ := by
        intro k hk
        have hCkE : C k = E0 := eq_top_of_resValuation_eq_top (hle0 k) hk
        obtain ⟨j, hj⟩ := Fintype.exists_ne_of_one_lt_card (α := ι)
          (by rw [← Nat.card_eq_fintype_card]; omega) k
        exact hincomp j k hj (by rw [hCkE]; exact hle0 j)
      have hincompW : ∀ j k, j ≠ k → ¬ (W j ≤ W k) := by
        intro j k hjk hle'
        exact hincomp j k hjk (le_of_resValuation_le (hle0 j) (hle0 k) hle')
      have hsupW : Finset.univ.sup' Finset.univ_nonempty W = ⊤ := by
        simpa only [W] using sup_resValuation_eq_top C E0 hle0 hE0
      obtain ⟨σ', hσ'fin, hσ'ne, f', E', hf', hle', hne', hind', hsplit'⟩ :=
        Commons.RingTheory.Valuation.exists_cluster_decomposition_nonempty W hntW hincompW
      letI : Fintype σ' := hσ'fin
      letI : Nonempty σ' := hσ'ne
      have hσ'ne1 : Nat.card σ' ≠ 1 := by
        intro h1
        have hcard1' : Fintype.card σ' ≤ 1 := by rw [← Nat.card_eq_fintype_card]; omega
        have hall' : ∀ a b : σ', a = b := Fintype.card_le_one_iff.mp hcard1'
        obtain ⟨s0'⟩ := hσ'ne
        have hle_sup : Finset.univ.sup' Finset.univ_nonempty W ≤ E' s0' :=
          (Finset.sup'_le_iff Finset.univ_nonempty W).mpr (fun k _ => by
            have hk := hle' k
            rwa [hall' (f' k) s0'] at hk)
        rw [hsupW] at hle_sup
        exact hne' s0' (le_top.antisymm hle_sup)
      have hsmall' : ∀ s, Nat.card {k : ι // f' k = s} < Nat.card ι := by
        rcases hsplit' with h | h
        · exact absurd h hσ'ne1
        · exact h
      haveI : Nonempty {k : ι // f' k = f' i} := ⟨⟨i, rfl⟩⟩
      obtain ⟨τbar, hτbar1, hτbar2⟩ :=
        ih (Nat.card {k : ι // f' k = f' i})
          (by rw [← hcard]; exact hsmall' (f' i))
          (fun k : {k : ι // f' k = f' i} => W k.val) (fun k => hntW k.val)
          (fun j k hjk => hincompW j.val k.val (fun h => hjk (Subtype.ext h)))
          ⟨i, rfl⟩ rfl
      obtain ⟨x, hx1, hx2⟩ :=
        glue W f' E' hle' hind' hne' i hτbar1
          (fun k hfk hk => hτbar2 ⟨k, hfk⟩ (fun h => hk (by simpa using congrArg Subtype.val h)))
      obtain ⟨u, hu⟩ := IsLocalRing.residue_surjective x
      have hxne0 : x ≠ 0 := by
        intro h0
        have hxW : x ∈ W i := by rw [h0]; exact (W i).zero_mem
        exact (not_le.mpr hx1) (((W i).valuation_le_one_iff x).mpr hxW)
      have hu_mE : u ∉ IsLocalRing.maximalIdeal E0 := by
        intro hmem
        exact hxne0 (by rw [← hu]; exact (IsLocalRing.residue_eq_zero_iff u).mpr hmem)
      refine ⟨(u : F), ?_, ?_⟩
      · have hnotmem : (u : F) ∉ C i := by
          intro hmem
          have hmemW : x ∈ W i := by
            rw [← hu]
            exact (mem_iff_residue (C i) E0 (hle0 i) hu_mE).mp hmem
          exact (not_le.mpr hx1) (((W i).valuation_le_one_iff x).mpr hmemW)
        exact not_le.mp (fun h1 => hnotmem (((C i).valuation_le_one_iff (u : F)).mp h1))
      · intro k hk
        exact valuation_lt_one_of_residue_lt (C k) E0 (hle0 k) hu_mE (by rw [hu]; exact hx2 k hk)

/-- **Separator theorem.**  For a finite pairwise-incomparable family of proper valuation subrings
`C` of a field `L` and a chosen index `i`, there is `τ : L` which is a non-unit at `C i`
(`(C i).valuation τ > 1`) and lies in the maximal ideal at every `C k`, `k ≠ i`
(`(C k).valuation τ < 1`). -/
theorem exists_separator_lt_one_of_pairwise_incomparable {L : Type*} [Field L] {ι : Type*}
    [Fintype ι] [Nonempty ι] (C : ι → ValuationSubring L) (hnt : ∀ i, C i ≠ ⊤)
    (hincomp : ∀ i j, i ≠ j → ¬ (C i ≤ C j)) (i : ι) :
    ∃ τ : L, (C i).valuation τ > 1 ∧ ∀ k, k ≠ i → (C k).valuation τ < 1 := by
  classical
  let e := Fintype.equivFin ι
  haveI : Nonempty (Fin (Fintype.card ι)) :=
    ⟨e (Classical.choice (inferInstance : Nonempty ι))⟩
  have hnt' : ∀ k : Fin (Fintype.card ι), C (e.symm k) ≠ ⊤ := fun k => hnt _
  have hincomp' : ∀ k l : Fin (Fintype.card ι), k ≠ l → ¬ (C (e.symm k) ≤ C (e.symm l)) := by
    intro k l hkl hle
    exact hincomp (e.symm k) (e.symm l) (fun h => hkl (e.symm.injective h)) hle
  obtain ⟨τ, hτ1, hτ2⟩ :=
    main_gen (Fintype.card ι) (fun k : Fin (Fintype.card ι) => C (e.symm k)) hnt' hincomp'
      (e i) (Nat.card_fin _)
  refine ⟨τ, ?_, ?_⟩
  · rw [show e.symm (e i) = i from Equiv.symm_apply_apply e i] at hτ1
    exact hτ1
  · intro k hk
    have h := hτ2 (e k) (fun h => hk (e.injective h))
    rw [show e.symm (e k) = k from Equiv.symm_apply_apply e k] at h
    exact h

end Commons.RingTheory.Valuation.ValuationSubring
