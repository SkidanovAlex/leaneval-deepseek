import Submission.Work.Stems.Hur2.Psi

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Continuity of the filling `Ψcube`, via the corner agreements

The cascade defining `psiFun` has five closed branches; to paste them
(`continuousOn_union_iff_of_isClosed`) one has to know that *on the overlaps the two formulas
agree* (the value lemmas `psiFun_eq_*Val` are only available where the earlier branches have been
ruled out).  On the four shared rays of the sectors the two `K₁`-squares meet at a corner of `σ`,
and on the four inner edges the `K₁`-square meets `σ` itself.
-/

open scoped unitInterval Topology

namespace Work.Stems.Hur2

open Work.Stems.Cubical

noncomputable section

variable {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]

/-! ## The four edges of `σ` as functions of the edge parameter -/

theorem comp_faceCM_11_apply (c : C(IC 2, X)) (w : unitInterval) :
    (c.comp (faceCM (1 : Fin 2) (1 : unitInterval))) (iota w) = c (pair2 w 1) := by
  show c (faceCM (1 : Fin 2) (1 : unitInterval) (iota w)) = c (pair2 w 1)
  rw [faceCM_pair2_11]; rfl

theorem comp_faceCM_01_apply (c : C(IC 2, X)) (w : unitInterval) :
    (c.comp (faceCM (0 : Fin 2) (1 : unitInterval))) (iota w) = c (pair2 1 w) := by
  show c (faceCM (0 : Fin 2) (1 : unitInterval) (iota w)) = c (pair2 1 w)
  rw [faceCM_pair2_01]; rfl

theorem comp_faceCM_10_apply (c : C(IC 2, X)) (w : unitInterval) :
    (c.comp (faceCM (1 : Fin 2) (0 : unitInterval))) (iota w) = c (pair2 w 0) := by
  show c (faceCM (1 : Fin 2) (0 : unitInterval) (iota w)) = c (pair2 w 0)
  rw [faceCM_pair2_10]; rfl

theorem comp_faceCM_00_apply (c : C(IC 2, X)) (w : unitInterval) :
    (c.comp (faceCM (0 : Fin 2) (0 : unitInterval))) (iota w) = c (pair2 0 w) := by
  show c (faceCM (0 : Fin 2) (0 : unitInterval) (iota w)) = c (pair2 0 w)
  rw [faceCM_pair2_00]; rfl

/-! ## Agreement of the two formulas on the overlaps -/

section Agreements

variable {x₀ : X} {c : C(IC 2, X)} {t : IC 2}

theorem topVal_eq_rightVal_of_mem (ht : t ∈ topSet) (hr : t ∈ rightSet) :
    topVal x₀ c t = rightVal x₀ c t := by
  obtain ⟨hb, hc, hab⟩ := ht
  obtain ⟨ha, hd, hba⟩ := hr
  have hab' : (t 0 : ℝ) = (t 1 : ℝ) := le_antisymm hab hba
  have h2a : (1 : ℝ) ≤ 2 * (t 0 : ℝ) - 1/2 := by linarith
  have h2b : (1 : ℝ) ≤ 2 * (t 1 : ℝ) - 1/2 := by linarith
  rw [topVal, rightVal, clamp_of_ge_one h2a, clamp_of_ge_one h2b, K₁_pair2_eq_one,
    K₁_pair2_eq_one,
    show (c.comp (faceCM (1 : Fin 2) (1 : unitInterval))) (1 : IC 1) = c (pair2 1 1) from by
      rw [show (1 : IC 1) = iota 1 from rfl, comp_faceCM_11_apply],
    show (c.comp (faceCM (0 : Fin 2) (1 : unitInterval))) (1 : IC 1) = c (pair2 1 1) from by
      rw [show (1 : IC 1) = iota 1 from rfl, comp_faceCM_01_apply],
    show 4 - 4 * (t 0 : ℝ) = 4 - 4 * (t 1 : ℝ) by rw [hab']]

theorem topVal_eq_leftVal_of_mem (ht : t ∈ topSet) (hl : t ∈ leftSet) :
    topVal x₀ c t = leftVal x₀ c t := by
  obtain ⟨hb, hc, hab⟩ := ht
  obtain ⟨ha, hd, hba⟩ := hl
  have h' : 1 - (t 1 : ℝ) = (t 0 : ℝ) := by linarith
  have h2a : 2 * (t 0 : ℝ) - 1/2 ≤ 0 := by linarith
  have h2b : (1 : ℝ) ≤ 2 * (t 1 : ℝ) - 1/2 := by linarith
  rw [topVal, leftVal, clamp_of_le_zero h2a, clamp_of_ge_one h2b, K₁_pair2_eq_zero,
    K₁_pair2_eq_one,
    show (c.comp (faceCM (1 : Fin 2) (1 : unitInterval))) (0 : IC 1) = c (pair2 0 1) from by
      rw [show (0 : IC 1) = iota 0 from rfl, comp_faceCM_11_apply],
    show (c.comp (faceCM (0 : Fin 2) (0 : unitInterval))) (1 : IC 1) = c (pair2 0 1) from by
      rw [show (1 : IC 1) = iota 1 from rfl, comp_faceCM_00_apply],
    show 4 - 4 * (t 1 : ℝ) = 4 * (t 0 : ℝ) by rw [← h']; ring]

theorem rightVal_eq_botVal_of_mem (hr : t ∈ rightSet) (hb : t ∈ botSet) :
    rightVal x₀ c t = botVal x₀ c t := by
  obtain ⟨ha, hd, hba⟩ := hr
  obtain ⟨hb', hba', hc'⟩ := hb
  have h' : (t 1 : ℝ) = 1 - (t 0 : ℝ) := by linarith
  have h2b : 2 * (t 1 : ℝ) - 1/2 ≤ 0 := by linarith
  have h2a : (1 : ℝ) ≤ 2 * (t 0 : ℝ) - 1/2 := by linarith
  rw [rightVal, botVal, clamp_of_le_zero h2b, clamp_of_ge_one h2a, K₁_pair2_eq_zero,
    K₁_pair2_eq_one,
    show (c.comp (faceCM (0 : Fin 2) (1 : unitInterval))) (0 : IC 1) = c (pair2 1 0) from by
      rw [show (0 : IC 1) = iota 0 from rfl, comp_faceCM_01_apply],
    show (c.comp (faceCM (1 : Fin 2) (0 : unitInterval))) (1 : IC 1) = c (pair2 1 0) from by
      rw [show (1 : IC 1) = iota 1 from rfl, comp_faceCM_10_apply],
    show 4 - 4 * (t 0 : ℝ) = 4 * (t 1 : ℝ) by rw [h']; ring]

theorem botVal_eq_leftVal_of_mem (hb : t ∈ botSet) (hl : t ∈ leftSet) :
    botVal x₀ c t = leftVal x₀ c t := by
  obtain ⟨hb', hba', hc'⟩ := hb
  obtain ⟨ha, hab, hd⟩ := hl
  have h' : (t 0 : ℝ) = (t 1 : ℝ) := le_antisymm hab hba'
  have h2a : 2 * (t 1 : ℝ) - 1/2 ≤ 0 := by linarith
  have h2a' : 2 * (t 0 : ℝ) - 1/2 ≤ 0 := by linarith
  rw [botVal, leftVal, clamp_of_le_zero h2a', clamp_of_le_zero h2a, K₁_pair2_eq_zero,
    K₁_pair2_eq_zero,
    show (c.comp (faceCM (1 : Fin 2) (0 : unitInterval))) (0 : IC 1) = c (pair2 0 0) from by
      rw [show (0 : IC 1) = iota 0 from rfl, comp_faceCM_10_apply],
    show (c.comp (faceCM (0 : Fin 2) (0 : unitInterval))) (0 : IC 1) = c (pair2 0 0) from by
      rw [show (0 : IC 1) = iota 0 from rfl, comp_faceCM_00_apply],
    h']

theorem topVal_eq_innerVal_of_mem (ht : t ∈ topSet) (hi : t ∈ innerSet) :
    topVal x₀ c t = innerVal c t := by
  obtain ⟨hb, hc, hab⟩ := ht
  obtain ⟨hi1, hi2, hi3, hi4⟩ := hi
  have hb' : (t 1 : ℝ) = 3/4 := le_antisymm hi4 hb
  rw [topVal, innerVal, show 4 - 4 * (t 1 : ℝ) = 1 by rw [hb']; ring, clamp_one,
    K₁_pair2_one, comp_faceCM_11_apply,
    show 2 * (t 1 : ℝ) - 1/2 = 1 by rw [hb']; ring, clamp_one]

theorem rightVal_eq_innerVal_of_mem (hr : t ∈ rightSet) (hi : t ∈ innerSet) :
    rightVal x₀ c t = innerVal c t := by
  obtain ⟨ha, hd, hba⟩ := hr
  obtain ⟨hi1, hi2, hi3, hi4⟩ := hi
  have ha' : (t 0 : ℝ) = 3/4 := le_antisymm hi2 ha
  rw [rightVal, innerVal, show 4 - 4 * (t 0 : ℝ) = 1 by rw [ha']; ring, clamp_one,
    K₁_pair2_one, comp_faceCM_01_apply,
    show 2 * (t 0 : ℝ) - 1/2 = 1 by rw [ha']; ring, clamp_one]

theorem botVal_eq_innerVal_of_mem (hb : t ∈ botSet) (hi : t ∈ innerSet) :
    botVal x₀ c t = innerVal c t := by
  obtain ⟨hb', hba', hc'⟩ := hb
  obtain ⟨hi1, hi2, hi3, hi4⟩ := hi
  have hb'' : (t 1 : ℝ) = 1/4 := le_antisymm hb' hi3
  rw [botVal, innerVal, show 4 * (t 1 : ℝ) = 1 by rw [hb'']; ring, clamp_one,
    K₁_pair2_one, comp_faceCM_10_apply,
    show 2 * (t 1 : ℝ) - 1/2 = 0 by rw [hb'']; ring, clamp_zero]

theorem leftVal_eq_innerVal_of_mem (hl : t ∈ leftSet) (hi : t ∈ innerSet) :
    leftVal x₀ c t = innerVal c t := by
  obtain ⟨ha, hab, hd⟩ := hl
  obtain ⟨hi1, hi2, hi3, hi4⟩ := hi
  have ha' : (t 0 : ℝ) = 1/4 := le_antisymm ha hi1
  rw [leftVal, innerVal, show 4 * (t 0 : ℝ) = 1 by rw [ha']; ring, clamp_one,
    K₁_pair2_one, comp_faceCM_00_apply,
    show 2 * (t 0 : ℝ) - 1/2 = 0 by rw [ha']; ring, clamp_zero]

end Agreements

/-! ## The value of `psiFun` on each region, unconditionally -/

theorem psiFun_eq_rightVal' {x₀ : X} {c : C(IC 2, X)} {t : IC 2} (ht : t ∈ rightSet) :
    psiFun x₀ c t = rightVal x₀ c t := by
  by_cases h : t ∈ topSet
  · rw [psiFun_eq_topVal h, topVal_eq_rightVal_of_mem h ht]
  · exact psiFun_eq_rightVal h ht

theorem psiFun_eq_botVal' {x₀ : X} {c : C(IC 2, X)} {t : IC 2} (ht : t ∈ botSet) :
    psiFun x₀ c t = botVal x₀ c t := by
  by_cases h1 : t ∈ topSet
  · exfalso
    obtain ⟨hb, _, _⟩ := h1
    obtain ⟨hb', _, _⟩ := ht
    linarith
  · by_cases h2 : t ∈ rightSet
    · rw [psiFun_eq_rightVal h1 h2, rightVal_eq_botVal_of_mem h2 ht]
    · exact psiFun_eq_botVal h1 h2 ht

theorem psiFun_eq_leftVal' {x₀ : X} {c : C(IC 2, X)} {t : IC 2} (ht : t ∈ leftSet) :
    psiFun x₀ c t = leftVal x₀ c t := by
  by_cases h1 : t ∈ topSet
  · rw [psiFun_eq_topVal h1, topVal_eq_leftVal_of_mem h1 ht]
  · by_cases h2 : t ∈ rightSet
    · exfalso
      obtain ⟨ha, _, _⟩ := h2
      obtain ⟨hb, _, _⟩ := ht
      linarith
    · by_cases h3 : t ∈ botSet
      · rw [psiFun_eq_botVal h1 h2 h3, botVal_eq_leftVal_of_mem h3 ht]
      · exact psiFun_eq_leftVal h1 h2 h3 ht

theorem psiFun_eq_innerVal' {x₀ : X} {c : C(IC 2, X)} {t : IC 2} (ht : t ∈ innerSet) :
    psiFun x₀ c t = innerVal c t := by
  by_cases h1 : t ∈ topSet
  · rw [psiFun_eq_topVal h1, topVal_eq_innerVal_of_mem h1 ht]
  · by_cases h2 : t ∈ rightSet
    · rw [psiFun_eq_rightVal h1 h2, rightVal_eq_innerVal_of_mem h2 ht]
    · by_cases h3 : t ∈ botSet
      · rw [psiFun_eq_botVal h1 h2 h3, botVal_eq_innerVal_of_mem h3 ht]
      · by_cases h4 : t ∈ leftSet
        · rw [psiFun_eq_leftVal h1 h2 h3 h4, leftVal_eq_innerVal_of_mem h4 ht]
        · exact psiFun_eq_innerVal h1 h2 h3 h4

/-! ## Continuity, and the basedness of the filling -/

/-- **Continuity of the filling.** -/
theorem continuous_psiFun (x₀ : X) (c : C(IC 2, X)) : Continuous (psiFun x₀ c) := by
  rw [← continuousOn_univ, univ_eq_regions]
  rw [continuousOn_union_iff_of_isClosed
    (((isClosed_topSet.union isClosed_rightSet).union isClosed_botSet).union isClosed_leftSet)
    isClosed_innerSet]
  refine ⟨?_, ?_⟩
  · rw [continuousOn_union_iff_of_isClosed
      ((isClosed_topSet.union isClosed_rightSet).union isClosed_botSet) isClosed_leftSet]
    refine ⟨?_, ?_⟩
    · rw [continuousOn_union_iff_of_isClosed
        (isClosed_topSet.union isClosed_rightSet) isClosed_botSet]
      refine ⟨?_, ?_⟩
      · rw [continuousOn_union_iff_of_isClosed isClosed_topSet isClosed_rightSet]
        exact ⟨(continuous_topVal x₀ c).continuousOn.congr (fun t ht => psiFun_eq_topVal ht),
          (continuous_rightVal x₀ c).continuousOn.congr (fun t ht => psiFun_eq_rightVal' ht)⟩
      · exact (continuous_botVal x₀ c).continuousOn.congr (fun t ht => psiFun_eq_botVal' ht)
    · exact (continuous_leftVal x₀ c).continuousOn.congr (fun t ht => psiFun_eq_leftVal' ht)
  · exact (continuous_innerVal c).continuousOn.congr (fun t ht => psiFun_eq_innerVal' ht)

/-- **The filling of a 2-cube**, as a continuous map. -/
def PsiCube (x₀ : X) (c : C(IC 2, X)) : C(IC 2, X) :=
  ⟨psiFun x₀ c, continuous_psiFun x₀ c⟩

@[simp] theorem PsiCube_apply (x₀ : X) (c : C(IC 2, X)) (t : IC 2) :
    PsiCube x₀ c t = psiFun x₀ c t := rfl

/-- **`PsiCube` is a based cube**: on the boundary of the square it is `x₀`. -/
theorem PsiCube_mem_boundary {x₀ : X} {c : C(IC 2, X)} {t : IC 2}
    (ht : t ∈ Cube.boundary (Fin 2)) : psiFun x₀ c t = x₀ := by
  rcases ht with ⟨i, hi | hi⟩
  · fin_cases i
    · have h0u : (t 0 : unitInterval) = 0 := hi
      have h0 : ((t 0 : unitInterval) : ℝ) = 0 := by rw [h0u]; rfl
      have h4 : t ∈ leftSet := by
        refine ⟨by rw [h0]; norm_num, by rw [h0]; exact (t 1).2.1,
          by rw [h0]; linarith [(t 1).2.2]⟩
      rw [psiFun_eq_leftVal' h4, leftVal, h0, show (4 : ℝ) * 0 = 0 by norm_num, clamp_zero,
        K₁_pair2_zero]
    · have h1u : (t 1 : unitInterval) = 0 := hi
      have h1 : ((t 1 : unitInterval) : ℝ) = 0 := by rw [h1u]; rfl
      have h3 : t ∈ botSet := by
        refine ⟨by rw [h1]; norm_num, by rw [h1]; exact (t 0).2.1,
          by rw [h1]; linarith [(t 0).2.2]⟩
      rw [psiFun_eq_botVal' h3, botVal, h1, show (4 : ℝ) * 0 = 0 by norm_num, clamp_zero,
        K₁_pair2_zero]
  · fin_cases i
    · have h0u : (t 0 : unitInterval) = 1 := hi
      have h0 : ((t 0 : unitInterval) : ℝ) = 1 := by rw [h0u]; rfl
      have h2 : t ∈ rightSet := by
        refine ⟨by rw [h0]; norm_num, by rw [h0]; linarith [(t 1).2.1],
          by rw [h0]; exact (t 1).2.2⟩
      rw [psiFun_eq_rightVal' h2, rightVal, h0, show (4 : ℝ) - 4 * 1 = 0 by norm_num, clamp_zero,
        K₁_pair2_zero]
    · have h1u : (t 1 : unitInterval) = 1 := hi
      have h1 : ((t 1 : unitInterval) : ℝ) = 1 := by rw [h1u]; rfl
      have h1' : t ∈ topSet := by
        refine ⟨by rw [h1]; norm_num, by rw [h1]; linarith [(t 0).2.1],
          by rw [h1]; exact (t 0).2.2⟩
      rw [psiFun_eq_topVal h1', topVal, h1, show (4 : ℝ) - 4 * 1 = 0 by norm_num, clamp_zero,
        K₁_pair2_zero]

/-- **The filling as an element of `Ω^(Fin 2) X x₀`.** -/
def psiGenLoop (x₀ : X) (c : C(IC 2, X)) : GenLoop (Fin 2) X x₀ :=
  ⟨PsiCube x₀ c, fun t ht => by rw [PsiCube_apply]; exact PsiCube_mem_boundary ht⟩

@[simp] theorem psiGenLoop_apply (x₀ : X) (c : C(IC 2, X)) (t : IC 2) :
    (psiGenLoop x₀ c : C(IC 2, X)) t = psiFun x₀ c t := rfl

end


end Work.Stems.Hur2
