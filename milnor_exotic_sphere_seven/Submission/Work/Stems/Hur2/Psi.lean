import Submission.Work.Stems.Hur2.Kfill

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The filling `Ψcube` of a 2-cube

`Ψcube σ : I² → X` is Hutchings' "make a cube based" construction: the middle quarter-square
carries `σ`, and the four sectors of the square annulus carry the squares `K₁` of the four edges of
`σ`.  On the outer boundary all four sectors give `x₀` (so `Ψcube σ` is a *based* cube), and on the
inner boundary the sectors match `σ` along the faces of `K₁`.

Everything is written with clamped affine expressions (no rational functions): writing
`a := (t 0 : ℝ)`, `b := (t 1 : ℝ)`,
* inner `(1/4 ≤ a ≤ 3/4 ∧ 1/4 ≤ b ≤ 3/4)`: `σ (pair2 (clamp (2a-1/2)) (clamp (2b-1/2)))`;
* top `(b ≥ 3/4 ∧ a ≥ 1-b ∧ a ≤ b)`:   `K₁ (σ.comp (faceCM 1 1)) (pair2 (clamp (4-4b)) (clamp (2a-1/2)))`;
* right `(a ≥ 3/4 ∧ b ≥ 1-a ∧ b ≤ a)`: `K₁ (σ.comp (faceCM 0 1)) (pair2 (clamp (4-4a)) (clamp (2b-1/2)))`;
* bottom `(b ≤ 1/4 ∧ a ≥ b ∧ a ≤ 1-b)`: `K₁ (σ.comp (faceCM 1 0)) (pair2 (clamp (4b)) (clamp (2a-1/2)))`;
* left `(a ≤ 1/4 ∧ b ≥ a ∧ b ≤ 1-a)`:   `K₁ (σ.comp (faceCM 0 0)) (pair2 (clamp (4a)) (clamp (2b-1/2)))`.
-/

open scoped unitInterval Topology

namespace Work.Stems.Hur2

open Work.Stems.Cubical

noncomputable section

variable {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]

/-- The point of `I²` with coordinates `a`, `b`. -/
def pair2 (a b : unitInterval) : IC 2 := fun i => if i = 0 then a else b

@[simp] theorem pair2_zero (a b : unitInterval) : pair2 a b (0 : Fin 2) = a := by
  simp [pair2]

@[simp] theorem pair2_one (a b : unitInterval) : pair2 a b (1 : Fin 2) = b := by
  simp [pair2]

theorem faceCM_pair2_00 (t : IC 1) :
    faceCM (0 : Fin 2) (0 : unitInterval) t = pair2 0 (t 0) := by
  funext i
  fin_cases i <;> simp [faceCM_apply, faceFun_apply, Fin.succAboveCases, pair2]

theorem faceCM_pair2_01 (t : IC 1) :
    faceCM (0 : Fin 2) (1 : unitInterval) t = pair2 1 (t 0) := by
  funext i
  fin_cases i <;> simp [faceCM_apply, faceFun_apply, Fin.succAboveCases, pair2]

theorem faceCM_pair2_10 (t : IC 1) :
    faceCM (1 : Fin 2) (0 : unitInterval) t = pair2 (t 0) 0 := by
  funext i
  fin_cases i <;> simp [faceCM_apply, faceFun_apply, Fin.succAboveCases, pair2]

theorem faceCM_pair2_11 (t : IC 1) :
    faceCM (1 : Fin 2) (1 : unitInterval) t = pair2 (t 0) 1 := by
  funext i
  fin_cases i <;> simp [faceCM_apply, faceFun_apply, Fin.succAboveCases, pair2]

/-- The clamping of a real number into `I`. -/
def clamp (r : ℝ) : unitInterval := Set.projIcc 0 1 zero_le_one r

theorem continuous_clamp : Continuous clamp := by
  unfold clamp
  exact continuous_projIcc

theorem clamp_of_mem {r : ℝ} (h : r ∈ Set.Icc (0 : ℝ) 1) : clamp r = ⟨r, h⟩ := by
  rw [clamp]
  exact Set.projIcc_of_mem zero_le_one h

@[simp] theorem clamp_zero : clamp 0 = 0 := by
  rw [clamp]
  exact Set.projIcc_left zero_le_one

@[simp] theorem clamp_one : clamp 1 = 1 := by
  rw [clamp]
  exact Set.projIcc_right zero_le_one

/-! ## The five regions of the square -/

/-- The inner quarter-square. -/
def innerSet : Set (IC 2) :=
  {t | (1/4 : ℝ) ≤ (t 0 : ℝ) ∧ (t 0 : ℝ) ≤ 3/4 ∧
       (1/4 : ℝ) ≤ (t 1 : ℝ) ∧ (t 1 : ℝ) ≤ 3/4}

/-- The sector attached to the edge `σ(·,1)`. -/
def topSet : Set (IC 2) :=
  {t | (3/4 : ℝ) ≤ (t 1 : ℝ) ∧ 1 - (t 1 : ℝ) ≤ (t 0 : ℝ) ∧ (t 0 : ℝ) ≤ (t 1 : ℝ)}

/-- The sector attached to the edge `σ(1,·)`. -/
def rightSet : Set (IC 2) :=
  {t | (3/4 : ℝ) ≤ (t 0 : ℝ) ∧ 1 - (t 0 : ℝ) ≤ (t 1 : ℝ) ∧ (t 1 : ℝ) ≤ (t 0 : ℝ)}

/-- The sector attached to the edge `σ(·,0)`. -/
def botSet : Set (IC 2) :=
  {t | (t 1 : ℝ) ≤ 1/4 ∧ (t 1 : ℝ) ≤ (t 0 : ℝ) ∧ (t 0 : ℝ) ≤ 1 - (t 1 : ℝ)}

/-- The sector attached to the edge `σ(0,·)`. -/
def leftSet : Set (IC 2) :=
  {t | (t 0 : ℝ) ≤ 1/4 ∧ (t 0 : ℝ) ≤ (t 1 : ℝ) ∧ (t 1 : ℝ) ≤ 1 - (t 0 : ℝ)}

/-- **Every point of the square lies in one of the five closed regions** (right-nested form,
which is the one that is convenient to establish). -/
theorem mem_regions (t : IC 2) :
    t ∈ topSet ∨ t ∈ rightSet ∨ t ∈ botSet ∨ t ∈ leftSet ∨ t ∈ innerSet := by
  have h0 : (0 : ℝ) ≤ (t 0 : ℝ) := (t 0).2.1
  have h1 : (t 0 : ℝ) ≤ 1 := (t 0).2.2
  have h2 : (0 : ℝ) ≤ (t 1 : ℝ) := (t 1).2.1
  have h3 : (t 1 : ℝ) ≤ 1 := (t 1).2.2
  rcases le_or_gt ((3:ℝ)/4) (t 1 : ℝ) with hb | hb
  · rcases le_or_gt (t 0 : ℝ) (t 1 : ℝ) with hab | hab
    · rcases le_or_gt (1 - (t 1 : ℝ)) (t 0 : ℝ) with hc | hc
      · exact Or.inl ⟨hb, hc, hab⟩
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨by linarith, by linarith, by linarith⟩)))
    · exact Or.inr (Or.inl ⟨by linarith, by linarith, by linarith⟩)
  · rcases le_or_gt (t 1 : ℝ) (1/4) with hb' | hb'
    · rcases le_or_gt (t 1 : ℝ) (t 0 : ℝ) with hba | hba
      · rcases le_or_gt (t 0 : ℝ) (1 - (t 1 : ℝ)) with hc | hc
        · exact Or.inr (Or.inr (Or.inl ⟨hb', hba, hc⟩))
        · exact Or.inr (Or.inl ⟨by linarith, by linarith, by linarith⟩)
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨by linarith, by linarith, by linarith⟩)))
    · rcases lt_or_ge (t 0 : ℝ) (1/4) with ha | ha
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨by linarith, by linarith, by linarith⟩)))
      · rcases le_or_gt (t 0 : ℝ) (3/4) with ha' | ha'
        · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨ha, ha', le_of_lt hb', le_of_lt hb⟩)))
        · exact Or.inr (Or.inl ⟨by linarith, by linarith, by linarith⟩)

/-- **The five closed regions tile the square.** -/
theorem univ_eq_regions :
    (Set.univ : Set (IC 2)) = topSet ∪ rightSet ∪ botSet ∪ leftSet ∪ innerSet := by
  ext t
  simp only [Set.mem_univ, Set.mem_union, Set.mem_setOf_eq, true_iff]
  rcases mem_regions t with h | h | h | h | h
  · exact Or.inl (Or.inl (Or.inl (Or.inl h)))
  · exact Or.inl (Or.inl (Or.inl (Or.inr h)))
  · exact Or.inl (Or.inl (Or.inr h))
  · exact Or.inl (Or.inr h)
  · exact Or.inr h

/-! ## The filling function -/

/-- The value on the inner square. -/
def innerVal (c : C(IC 2, X)) (t : IC 2) : X :=
  c (pair2 (clamp (2 * (t 0 : ℝ) - 1/2)) (clamp (2 * (t 1 : ℝ) - 1/2)))

/-- The value on the top sector. -/
def topVal (x₀ : X) (c : C(IC 2, X)) (t : IC 2) : X :=
  K₁ x₀ (c.comp (faceCM (1 : Fin 2) (1 : unitInterval)))
    (pair2 (clamp (4 - 4 * (t 1 : ℝ))) (clamp (2 * (t 0 : ℝ) - 1/2)))

/-- The value on the right sector. -/
def rightVal (x₀ : X) (c : C(IC 2, X)) (t : IC 2) : X :=
  K₁ x₀ (c.comp (faceCM (0 : Fin 2) (1 : unitInterval)))
    (pair2 (clamp (4 - 4 * (t 0 : ℝ))) (clamp (2 * (t 1 : ℝ) - 1/2)))

/-- The value on the bottom sector. -/
def botVal (x₀ : X) (c : C(IC 2, X)) (t : IC 2) : X :=
  K₁ x₀ (c.comp (faceCM (1 : Fin 2) (0 : unitInterval)))
    (pair2 (clamp (4 * (t 1 : ℝ))) (clamp (2 * (t 0 : ℝ) - 1/2)))

/-- The value on the left sector. -/
def leftVal (x₀ : X) (c : C(IC 2, X)) (t : IC 2) : X :=
  K₁ x₀ (c.comp (faceCM (0 : Fin 2) (0 : unitInterval)))
    (pair2 (clamp (4 * (t 0 : ℝ))) (clamp (2 * (t 1 : ℝ) - 1/2)))

/-- **The filling of a 2-cube.** -/
def psiFun (x₀ : X) (c : C(IC 2, X)) (t : IC 2) : X := by
  classical
  exact if _h1 : t ∈ topSet then topVal x₀ c t
  else if _h2 : t ∈ rightSet then rightVal x₀ c t
  else if _h3 : t ∈ botSet then botVal x₀ c t
  else if _h4 : t ∈ leftSet then leftVal x₀ c t
  else innerVal c t

theorem psiFun_eq_topVal {x₀ : X} {c : C(IC 2, X)} {t : IC 2} (h : t ∈ topSet) :
    psiFun x₀ c t = topVal x₀ c t := by
  classical
  rw [psiFun]
  exact dif_pos h

theorem psiFun_eq_rightVal {x₀ : X} {c : C(IC 2, X)} {t : IC 2}
    (h1 : t ∉ topSet) (h : t ∈ rightSet) : psiFun x₀ c t = rightVal x₀ c t := by
  classical
  rw [psiFun]
  rw [dif_neg h1]
  exact dif_pos h

theorem psiFun_eq_botVal {x₀ : X} {c : C(IC 2, X)} {t : IC 2}
    (h1 : t ∉ topSet) (h2 : t ∉ rightSet) (h : t ∈ botSet) :
    psiFun x₀ c t = botVal x₀ c t := by
  classical
  rw [psiFun]
  rw [dif_neg h1, dif_neg h2]
  exact dif_pos h

theorem psiFun_eq_leftVal {x₀ : X} {c : C(IC 2, X)} {t : IC 2}
    (h1 : t ∉ topSet) (h2 : t ∉ rightSet) (h3 : t ∉ botSet) (h : t ∈ leftSet) :
    psiFun x₀ c t = leftVal x₀ c t := by
  classical
  rw [psiFun]
  rw [dif_neg h1, dif_neg h2, dif_neg h3]
  exact dif_pos h

theorem psiFun_eq_innerVal {x₀ : X} {c : C(IC 2, X)} {t : IC 2}
    (h1 : t ∉ topSet) (h2 : t ∉ rightSet) (h3 : t ∉ botSet) (h4 : t ∉ leftSet) :
    psiFun x₀ c t = innerVal c t := by
  classical
  rw [psiFun]
  rw [dif_neg h1, dif_neg h2, dif_neg h3, dif_neg h4]

/-! ## Continuity -/

theorem continuous_coord (i : Fin 2) : Continuous fun t : IC 2 => ((t i : unitInterval) : ℝ) :=
  continuous_subtype_val.comp (continuous_apply i)

theorem continuous_pair2 {α : Type*} [TopologicalSpace α] {f g : α → unitInterval}
    (hf : Continuous f) (hg : Continuous g) :
    Continuous fun t => pair2 (f t) (g t) := by
  apply continuous_pi
  intro i
  fin_cases i
  · simpa [pair2] using hf
  · simpa [pair2] using hg

theorem continuous_innerVal (c : C(IC 2, X)) : Continuous (innerVal c) :=
  c.continuous.comp (continuous_pair2
    (continuous_clamp.comp ((continuous_const.mul (continuous_coord 0)).sub continuous_const))
    (continuous_clamp.comp ((continuous_const.mul (continuous_coord 1)).sub continuous_const)))

theorem continuous_topVal (x₀ : X) (c : C(IC 2, X)) : Continuous (topVal x₀ c) :=
  (K₁ x₀ (c.comp (faceCM (1 : Fin 2) (1 : unitInterval)))).continuous.comp (continuous_pair2
    (continuous_clamp.comp (continuous_const.sub (continuous_const.mul (continuous_coord 1))))
    (continuous_clamp.comp ((continuous_const.mul (continuous_coord 0)).sub continuous_const)))

theorem continuous_rightVal (x₀ : X) (c : C(IC 2, X)) : Continuous (rightVal x₀ c) :=
  (K₁ x₀ (c.comp (faceCM (0 : Fin 2) (1 : unitInterval)))).continuous.comp (continuous_pair2
    (continuous_clamp.comp (continuous_const.sub (continuous_const.mul (continuous_coord 0))))
    (continuous_clamp.comp ((continuous_const.mul (continuous_coord 1)).sub continuous_const)))

theorem continuous_botVal (x₀ : X) (c : C(IC 2, X)) : Continuous (botVal x₀ c) :=
  (K₁ x₀ (c.comp (faceCM (1 : Fin 2) (0 : unitInterval)))).continuous.comp (continuous_pair2
    (continuous_clamp.comp (continuous_const.mul (continuous_coord 1)))
    (continuous_clamp.comp ((continuous_const.mul (continuous_coord 0)).sub continuous_const)))

theorem continuous_leftVal (x₀ : X) (c : C(IC 2, X)) : Continuous (leftVal x₀ c) :=
  (K₁ x₀ (c.comp (faceCM (0 : Fin 2) (0 : unitInterval)))).continuous.comp (continuous_pair2
    (continuous_clamp.comp (continuous_const.mul (continuous_coord 0)))
    (continuous_clamp.comp ((continuous_const.mul (continuous_coord 1)).sub continuous_const)))

/-! ### Closedness of the regions -/

theorem isClosed_topSet : IsClosed topSet := by
  have h1 : IsClosed {t : IC 2 | (3/4 : ℝ) ≤ (t 1 : ℝ)} := isClosed_le continuous_const (continuous_coord 1)
  have h2 : IsClosed {t : IC 2 | 1 - (t 1 : ℝ) ≤ (t 0 : ℝ)} :=
    isClosed_le (continuous_const.sub (continuous_coord 1)) (continuous_coord 0)
  have h3 : IsClosed {t : IC 2 | (t 0 : ℝ) ≤ (t 1 : ℝ)} := isClosed_le (continuous_coord 0) (continuous_coord 1)
  have h : topSet = {t : IC 2 | (3/4 : ℝ) ≤ (t 1 : ℝ)} ∩ {t : IC 2 | 1 - (t 1 : ℝ) ≤ (t 0 : ℝ)}
      ∩ {t : IC 2 | (t 0 : ℝ) ≤ (t 1 : ℝ)} := by
    ext t; simp only [topSet, Set.mem_setOf_eq, Set.mem_inter_iff]; tauto
  rw [h]; exact (h1.inter h2).inter h3

theorem isClosed_rightSet : IsClosed rightSet := by
  have h1 : IsClosed {t : IC 2 | (3/4 : ℝ) ≤ (t 0 : ℝ)} := isClosed_le continuous_const (continuous_coord 0)
  have h2 : IsClosed {t : IC 2 | 1 - (t 0 : ℝ) ≤ (t 1 : ℝ)} :=
    isClosed_le (continuous_const.sub (continuous_coord 0)) (continuous_coord 1)
  have h3 : IsClosed {t : IC 2 | (t 1 : ℝ) ≤ (t 0 : ℝ)} := isClosed_le (continuous_coord 1) (continuous_coord 0)
  have h : rightSet = {t : IC 2 | (3/4 : ℝ) ≤ (t 0 : ℝ)} ∩ {t : IC 2 | 1 - (t 0 : ℝ) ≤ (t 1 : ℝ)}
      ∩ {t : IC 2 | (t 1 : ℝ) ≤ (t 0 : ℝ)} := by
    ext t; simp only [rightSet, Set.mem_setOf_eq, Set.mem_inter_iff]; tauto
  rw [h]; exact (h1.inter h2).inter h3

theorem isClosed_botSet : IsClosed botSet := by
  have h1 : IsClosed {t : IC 2 | (t 1 : ℝ) ≤ 1/4} := isClosed_le (continuous_coord 1) continuous_const
  have h2 : IsClosed {t : IC 2 | (t 1 : ℝ) ≤ (t 0 : ℝ)} := isClosed_le (continuous_coord 1) (continuous_coord 0)
  have h3 : IsClosed {t : IC 2 | (t 0 : ℝ) ≤ 1 - (t 1 : ℝ)} :=
    isClosed_le (continuous_coord 0) (continuous_const.sub (continuous_coord 1))
  have h : botSet = {t : IC 2 | (t 1 : ℝ) ≤ 1/4} ∩ {t : IC 2 | (t 1 : ℝ) ≤ (t 0 : ℝ)}
      ∩ {t : IC 2 | (t 0 : ℝ) ≤ 1 - (t 1 : ℝ)} := by
    ext t; simp only [botSet, Set.mem_setOf_eq, Set.mem_inter_iff]; tauto
  rw [h]; exact (h1.inter h2).inter h3

theorem isClosed_leftSet : IsClosed leftSet := by
  have h1 : IsClosed {t : IC 2 | (t 0 : ℝ) ≤ 1/4} := isClosed_le (continuous_coord 0) continuous_const
  have h2 : IsClosed {t : IC 2 | (t 0 : ℝ) ≤ (t 1 : ℝ)} := isClosed_le (continuous_coord 0) (continuous_coord 1)
  have h3 : IsClosed {t : IC 2 | (t 1 : ℝ) ≤ 1 - (t 0 : ℝ)} :=
    isClosed_le (continuous_coord 1) (continuous_const.sub (continuous_coord 0))
  have h : leftSet = {t : IC 2 | (t 0 : ℝ) ≤ 1/4} ∩ {t : IC 2 | (t 0 : ℝ) ≤ (t 1 : ℝ)}
      ∩ {t : IC 2 | (t 1 : ℝ) ≤ 1 - (t 0 : ℝ)} := by
    ext t; simp only [leftSet, Set.mem_setOf_eq, Set.mem_inter_iff]; tauto
  rw [h]; exact (h1.inter h2).inter h3

theorem isClosed_innerSet : IsClosed innerSet := by
  have h1 : IsClosed {t : IC 2 | (1/4 : ℝ) ≤ (t 0 : ℝ)} := isClosed_le continuous_const (continuous_coord 0)
  have h2 : IsClosed {t : IC 2 | (t 0 : ℝ) ≤ 3/4} := isClosed_le (continuous_coord 0) continuous_const
  have h3 : IsClosed {t : IC 2 | (1/4 : ℝ) ≤ (t 1 : ℝ)} := isClosed_le continuous_const (continuous_coord 1)
  have h4 : IsClosed {t : IC 2 | (t 1 : ℝ) ≤ 3/4} := isClosed_le (continuous_coord 1) continuous_const
  have h : innerSet = {t : IC 2 | (1/4 : ℝ) ≤ (t 0 : ℝ)} ∩ {t : IC 2 | (t 0 : ℝ) ≤ 3/4}
      ∩ ({t : IC 2 | (1/4 : ℝ) ≤ (t 1 : ℝ)} ∩ {t : IC 2 | (t 1 : ℝ) ≤ 3/4}) := by
    ext t; simp only [innerSet, Set.mem_setOf_eq, Set.mem_inter_iff]; tauto
  rw [h]; exact (h1.inter h2).inter (h3.inter h4)

/-! ## `pair2` versus the faces, and the value of `K₁` in the corners -/

theorem pair2_one_eq (w : unitInterval) :
    pair2 1 w = faceCM (0 : Fin 2) (1 : unitInterval) (iota w) := by
  rw [faceCM_pair2_01]; rfl

theorem pair2_zero_eq (w : unitInterval) :
    pair2 0 w = faceCM (0 : Fin 2) (0 : unitInterval) (iota w) := by
  rw [faceCM_pair2_00]; rfl

theorem pair2_eq_one (w : unitInterval) :
    pair2 w 1 = faceCM (1 : Fin 2) (1 : unitInterval) (iota w) := by
  rw [faceCM_pair2_11]; rfl

theorem pair2_eq_zero (w : unitInterval) :
    pair2 w 0 = faceCM (1 : Fin 2) (0 : unitInterval) (iota w) := by
  rw [faceCM_pair2_10]; rfl

theorem K₁_pair2_one (x₀ : X) (e : C(IC 1, X)) (w : unitInterval) :
    K₁ x₀ e (pair2 1 w) = e (iota w) := by
  rw [pair2_one_eq, K₁_face_01]

theorem K₁_pair2_zero (x₀ : X) (e : C(IC 1, X)) (w : unitInterval) :
    K₁ x₀ e (pair2 0 w) = x₀ := by
  rw [pair2_zero_eq, K₁_face_00]

theorem K₁_pair2_eq_zero (x₀ : X) (e : C(IC 1, X)) (w : unitInterval) :
    K₁ x₀ e (pair2 w 0) = K₀ x₀ (e 0) w := by
  rw [pair2_eq_zero, K₁_face_10]; rfl

theorem K₁_pair2_eq_one (x₀ : X) (e : C(IC 1, X)) (w : unitInterval) :
    K₁ x₀ e (pair2 w 1) = K₀ x₀ (e 1) w := by
  rw [pair2_eq_one, K₁_face_11]; rfl

theorem clamp_of_ge_one {r : ℝ} (h : 1 ≤ r) : clamp r = 1 := by
  rw [clamp]
  exact Set.projIcc_of_right_le (a := (0 : ℝ)) (b := 1) (h := zero_le_one) h

theorem clamp_of_le_zero {r : ℝ} (h : r ≤ 0) : clamp r = 0 := by
  rw [clamp]
  exact Set.projIcc_of_le_left (a := (0 : ℝ)) (b := 1) (h := zero_le_one) h

end

end Work.Stems.Hur2
