import Mathlib
import Submission.Work.WilE4.Tower

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Classical
open WilkiesDesign

namespace Work.WilE4.CAD

open Work.WilE4

/-! ## Helper lemmas: the padding operation and the sign condition of a DNF atom -/

/-- Evaluating a polynomial renamed along `Fin.castSucc` is evaluation at the initial segment. -/
theorem eval_rename_castSucc {m : ℕ} (z : Fin (m + 1) → ℝ) (P : MvPolynomial (Fin m) ℝ) :
    MvPolynomial.eval z (MvPolynomial.rename Fin.castSucc P) =
      MvPolynomial.eval (Fin.init z) P := by
  rw [MvPolynomial.eval_rename]
  rfl

/-- The basic sets of a padded DNF, unfolded. -/
theorem pad_basics {m : ℕ} (X : SAd m) :
    (X.pad).basics = X.basics.map (fun B : BasicD m =>
      ⟨B.eqs.map (MvPolynomial.rename Fin.castSucc),
        B.pos.map (MvPolynomial.rename Fin.castSucc)⟩) := rfl

/-- The set of a padded DNF is the set of points whose initial segment lies in the base set. -/
theorem pad_set {m : ℕ} (X : SAd m) :
    (X.pad).set = {z : Fin (m + 1) → ℝ | Fin.init z ∈ X.set} := by
  ext z
  constructor
  · rintro ⟨B, hB, hBz⟩
    rw [pad_basics] at hB
    simp only [List.mem_map] at hB
    obtain ⟨B₀, hB₀, rfl⟩ := hB
    obtain ⟨hz1, hz2⟩ := hBz
    refine ⟨B₀, hB₀, fun f hf => ?_, fun g hg => ?_⟩
    · have h := hz1 (MvPolynomial.rename Fin.castSucc f) (List.mem_map_of_mem hf)
      rwa [eval_rename_castSucc] at h
    · have h := hz2 (MvPolynomial.rename Fin.castSucc g) (List.mem_map_of_mem hg)
      rwa [eval_rename_castSucc] at h
  · rintro ⟨B₀, hB₀, hBz⟩
    refine ⟨⟨B₀.eqs.map (MvPolynomial.rename Fin.castSucc),
      B₀.pos.map (MvPolynomial.rename Fin.castSucc)⟩, ?_, ?_⟩
    · exact List.mem_map_of_mem hB₀
    · obtain ⟨hz1, hz2⟩ := hBz
      refine ⟨fun f hf => ?_, fun g hg => ?_⟩
      · obtain ⟨f₀, hf₀, rfl⟩ := List.mem_map.mp hf
        rw [eval_rename_castSucc]
        exact hz1 f₀ hf₀
      · obtain ⟨g₀, hg₀, rfl⟩ := List.mem_map.mp hg
        rw [eval_rename_castSucc]
        exact hz2 g₀ hg₀

/-- The equation list of `BasicD.ofSign`. -/
theorem ofSign_eqs {m : ℕ} (G : List (MvPolynomial (Fin m) ℝ)) (v : Fin G.length → SignType) :
    (BasicD.ofSign G v).eqs = (List.finRange G.length).filterMap
      (fun i => if v i = 0 then some (G.get i) else none) := rfl

/-- The inequality list of `BasicD.ofSign`. -/
theorem ofSign_pos {m : ℕ} (G : List (MvPolynomial (Fin m) ℝ)) (v : Fin G.length → SignType) :
    (BasicD.ofSign G v).pos = (List.finRange G.length).filterMap
      (fun i => if v i = 1 then some (G.get i)
        else if v i = -1 then some (-(G.get i)) else none) := rfl

/-- Membership in the equation list of `BasicD.ofSign`. -/
theorem mem_ofSign_eqs {m : ℕ} (G : List (MvPolynomial (Fin m) ℝ))
    (v : Fin G.length → SignType) (f : MvPolynomial (Fin m) ℝ) :
    f ∈ (BasicD.ofSign G v).eqs ↔ ∃ i, v i = 0 ∧ G.get i = f := by
  simp only [ofSign_eqs, List.mem_filterMap, List.mem_finRange, true_and]
  constructor
  · rintro ⟨i, hi⟩
    by_cases h : v i = 0
    · rw [if_pos h] at hi
      injection hi with hf
      exact ⟨i, h, hf⟩
    · rw [if_neg h] at hi
      cases hi
  · rintro ⟨i, h, rfl⟩
    exact ⟨i, by rw [if_pos h]⟩

/-- Membership in the inequality list of `BasicD.ofSign`. -/
theorem mem_ofSign_pos {m : ℕ} (G : List (MvPolynomial (Fin m) ℝ))
    (v : Fin G.length → SignType) (g : MvPolynomial (Fin m) ℝ) :
    g ∈ (BasicD.ofSign G v).pos ↔
      ∃ i, (v i = 1 ∧ G.get i = g) ∨ (v i = -1 ∧ -(G.get i) = g) := by
  simp only [ofSign_pos, List.mem_filterMap, List.mem_finRange, true_and]
  constructor
  · rintro ⟨i, hi⟩
    by_cases h1 : v i = 1
    · rw [if_pos h1] at hi
      injection hi with hf
      exact ⟨i, Or.inl ⟨h1, hf⟩⟩
    · by_cases h2 : v i = -1
      · rw [if_neg h1, if_pos h2] at hi
        injection hi with hf
        exact ⟨i, Or.inr ⟨h2, hf⟩⟩
      · rw [if_neg h1, if_neg h2] at hi
        cases hi
  · rintro ⟨i, h | h⟩
    · obtain ⟨h1, rfl⟩ := h
      exact ⟨i, by rw [if_pos h1]⟩
    · obtain ⟨h1, rfl⟩ := h
      exact ⟨i, by rw [if_neg (by rw [h1]; decide), if_pos h1]⟩

/-- The set of a sign-condition DNF is exactly the corresponding sign condition. -/
theorem ofSign_set {m : ℕ} (G : List (MvPolynomial (Fin m) ℝ)) (v : Fin G.length → SignType) :
    (BasicD.ofSign G v).set = signCond G v := by
  ext x
  simp only [BasicD.set, Set.mem_setOf_eq, signCond]
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := h
    intro i
    rcases SignType.trichotomy (v i) with hv | hv | hv
    · have hp : (-(G.get i)) ∈ (BasicD.ofSign G v).pos :=
        (mem_ofSign_pos G v (-(G.get i))).mpr ⟨i, Or.inr ⟨hv, rfl⟩⟩
      have hpos := h2 (-(G.get i)) hp
      have hneg : MvPolynomial.eval x (-(G.get i)) = -MvPolynomial.eval x (G.get i) :=
        (MvPolynomial.eval x).map_neg (G.get i)
      rw [hneg] at hpos
      have hlt : MvPolynomial.eval x (G.get i) < 0 := by linarith
      rw [hv]
      exact sign_neg hlt
    · have he : (G.get i) ∈ (BasicD.ofSign G v).eqs :=
        (mem_ofSign_eqs G v (G.get i)).mpr ⟨i, hv, rfl⟩
      have hz := h1 (G.get i) he
      rw [hv, hz]
      exact sign_zero
    · have hp : (G.get i) ∈ (BasicD.ofSign G v).pos :=
        (mem_ofSign_pos G v (G.get i)).mpr ⟨i, Or.inl ⟨hv, rfl⟩⟩
      have hpos := h2 (G.get i) hp
      rw [hv]
      exact sign_pos hpos
  · intro h
    refine ⟨?_, ?_⟩
    · intro f hf
      obtain ⟨i, hi, rfl⟩ := (mem_ofSign_eqs G v f).mp hf
      have hs : SignType.sign (MvPolynomial.eval x (G.get i)) = 0 := by rw [h i, hi]
      exact sign_eq_zero_iff.mp hs
    · intro g hg
      obtain ⟨i, (⟨hi, rfl⟩ | ⟨hi, rfl⟩)⟩ := (mem_ofSign_pos G v g).mp hg
      · exact sign_eq_one_iff.mp (by rw [h i, hi])
      · have hs : SignType.sign (MvPolynomial.eval x (G.get i)) = -1 := by rw [h i, hi]
        have hlt : MvPolynomial.eval x (G.get i) < 0 := sign_eq_neg_one_iff.mp hs
        have hneg : MvPolynomial.eval x (-(G.get i)) = -MvPolynomial.eval x (G.get i) :=
          (MvPolynomial.eval x).map_neg (G.get i)
        rw [hneg]
        linarith

/-! ## The projection of a cylindrical cell -/

/-- The projection of a cylindrical cell is its base cell, provided the sign vector is realized
over every point of the base cell. -/
theorem cell_proj {m : ℕ} (C : SAd m) (G : List (MvPolynomial (Fin (m+1)) ℝ))
    (v : Fin G.length → SignType)
    (h : ∀ x ∈ C.set, ∃ y : ℝ,
      ∀ i, SignType.sign (MvPolynomial.eval (Fin.snoc x y) (G.get i)) = v i) :
    WilkiesDesign.projLast (cell C G v).set = C.set := by
  ext x
  constructor
  · intro hx
    simp only [WilkiesDesign.projLast, Set.mem_setOf_eq] at hx
    obtain ⟨t, ht⟩ := hx
    simp only [cell, SAd.interBasic_set, Set.mem_inter_iff, pad_set, Set.mem_setOf_eq] at ht
    have h1 : Fin.init (Fin.snoc x t : Fin (m + 1) → ℝ) ∈ C.set := ht.1
    rwa [Fin.init_snoc] at h1
  · intro hx
    obtain ⟨y, hy⟩ := h x hx
    simp only [WilkiesDesign.projLast, Set.mem_setOf_eq]
    refine ⟨y, ?_⟩
    simp only [cell, SAd.interBasic_set, Set.mem_inter_iff, pad_set, Set.mem_setOf_eq,
      ofSign_set, signCond, Fin.init_snoc]
    exact ⟨hx, hy⟩

end Work.WilE4.CAD
