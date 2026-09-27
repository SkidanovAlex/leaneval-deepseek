import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.KT.ExtGen.Basic

/-!
# `Work.KT.ExtGen.Triple` — the triple product algebra

The common target in which associativity of the external product is compared:
`tripleAlg V W Z = C(S^a × S^b × S^c)`, realised as the subalgebra of
`C(D_V × D_W × D_Z, ℂ)` (i.e. of `C(Ball (V × (W × Z)), ℂ)`) of functions that are constant in
each of the three coordinates whenever that coordinate lies on its own sphere.

All the algebras occurring in the associativity statement map into it, and the comparison maps
commute with the structure maps of the external product (`smashIncl`, `pullFst`, `pullSnd`,
`pairAssocEquiv`); see the lemmas at the end of the file.
-/

namespace Work.KT

namespace ExtGen

noncomputable section

set_option synthInstance.maxHeartbeats 800000

variable (V W Z : Type) [NormedAddCommGroup V] [NormedAddCommGroup W] [NormedAddCommGroup Z]

/-! ## Coordinates, norm bounds and the triple algebra -/

/-- The first coordinate of a point of the triple product ball. -/
def tpV (z : Ball (V × (W × Z))) : V := (z : V × (W × Z)).1

/-- The second coordinate of a point of the triple product ball. -/
def tpW (z : Ball (V × (W × Z))) : W := (z : V × (W × Z)).2.1

/-- The third coordinate of a point of the triple product ball. -/
def tpZ (z : Ball (V × (W × Z))) : Z := (z : V × (W × Z)).2.2

@[simp] lemma tpV_apply (z : Ball (V × (W × Z))) : tpV V W Z z = (z : V × (W × Z)).1 := rfl
@[simp] lemma tpW_apply (z : Ball (V × (W × Z))) : tpW V W Z z = (z : V × (W × Z)).2.1 := rfl
@[simp] lemma tpZ_apply (z : Ball (V × (W × Z))) : tpZ V W Z z = (z : V × (W × Z)).2.2 := rfl

lemma norm_fst_le' (z : Ball (V × (W × Z))) : ‖(z : V × (W × Z)).1‖ ≤ 1 := by
  have h : ‖(z : V × (W × Z))‖ ≤ 1 := by
    have := Metric.mem_closedBall.mp z.2
    rwa [dist_eq_norm, sub_zero] at this
  exact le_trans (norm_fst_le _) h

lemma norm_w_le (z : Ball (V × (W × Z))) : ‖(z : V × (W × Z)).2.1‖ ≤ 1 := by
  have h : ‖(z : V × (W × Z))‖ ≤ 1 := by
    have := Metric.mem_closedBall.mp z.2
    rwa [dist_eq_norm, sub_zero] at this
  exact le_trans (norm_fst_le _) (le_trans (norm_snd_le _) h)

lemma norm_zc_le (z : Ball (V × (W × Z))) : ‖(z : V × (W × Z)).2.2‖ ≤ 1 := by
  have h : ‖(z : V × (W × Z))‖ ≤ 1 := by
    have := Metric.mem_closedBall.mp z.2
    rwa [dist_eq_norm, sub_zero] at this
  exact le_trans (norm_snd_le _) (le_trans (norm_snd_le _) h)

/-- `C(S^a × S^b × S^c) ⊆ C(D_V × D_W × D_Z)`: functions constant in each coordinate whenever
that coordinate lies on its own sphere. -/
def tripleAlg : Subalgebra ℂ C(Ball (V × (W × Z)), ℂ) where
  carrier := {F | (∀ z z' : Ball (V × (W × Z)), ‖(z : V × (W × Z)).1‖ = 1 →
        ‖(z' : V × (W × Z)).1‖ = 1 → (z : V × (W × Z)).2.1 = (z' : V × (W × Z)).2.1 →
        (z : V × (W × Z)).2.2 = (z' : V × (W × Z)).2.2 → F z = F z') ∧
      (∀ z z' : Ball (V × (W × Z)), ‖(z : V × (W × Z)).2.1‖ = 1 →
        ‖(z' : V × (W × Z)).2.1‖ = 1 → (z : V × (W × Z)).2.2 = (z' : V × (W × Z)).2.2 →
        (z : V × (W × Z)).1 = (z' : V × (W × Z)).1 → F z = F z') ∧
      (∀ z z' : Ball (V × (W × Z)), ‖(z : V × (W × Z)).2.2‖ = 1 →
        ‖(z' : V × (W × Z)).2.2‖ = 1 → (z : V × (W × Z)).2.1 = (z' : V × (W × Z)).2.1 →
        (z : V × (W × Z)).1 = (z' : V × (W × Z)).1 → F z = F z')}
  mul_mem' := by
    rintro F G ⟨hF1, hF2, hF3⟩ ⟨hG1, hG2, hG3⟩
    refine ⟨fun z z' a b c d => ?_, fun z z' a b c d => ?_, fun z z' a b c d => ?_⟩
    · rw [ContinuousMap.mul_apply, ContinuousMap.mul_apply,
        hF1 z z' a b c d, hG1 z z' a b c d]
    · rw [ContinuousMap.mul_apply, ContinuousMap.mul_apply,
        hF2 z z' a b c d, hG2 z z' a b c d]
    · rw [ContinuousMap.mul_apply, ContinuousMap.mul_apply,
        hF3 z z' a b c d, hG3 z z' a b c d]
  add_mem' := by
    rintro F G ⟨hF1, hF2, hF3⟩ ⟨hG1, hG2, hG3⟩
    refine ⟨fun z z' a b c d => ?_, fun z z' a b c d => ?_, fun z z' a b c d => ?_⟩
    · rw [ContinuousMap.add_apply, ContinuousMap.add_apply,
        hF1 z z' a b c d, hG1 z z' a b c d]
    · rw [ContinuousMap.add_apply, ContinuousMap.add_apply,
        hF2 z z' a b c d, hG2 z z' a b c d]
    · rw [ContinuousMap.add_apply, ContinuousMap.add_apply,
        hF3 z z' a b c d, hG3 z z' a b c d]
  algebraMap_mem' := fun c => ⟨fun _ _ _ _ _ _ => rfl, fun _ _ _ _ _ _ => rfl,
    fun _ _ _ _ _ _ => rfl⟩

lemma mem_tripleAlg_iff {F : C(Ball (V × (W × Z)), ℂ)} :
    F ∈ tripleAlg V W Z ↔
      (∀ z z' : Ball (V × (W × Z)), ‖(z : V × (W × Z)).1‖ = 1 →
        ‖(z' : V × (W × Z)).1‖ = 1 → (z : V × (W × Z)).2.1 = (z' : V × (W × Z)).2.1 →
        (z : V × (W × Z)).2.2 = (z' : V × (W × Z)).2.2 → F z = F z') ∧
      (∀ z z' : Ball (V × (W × Z)), ‖(z : V × (W × Z)).2.1‖ = 1 →
        ‖(z' : V × (W × Z)).2.1‖ = 1 → (z : V × (W × Z)).2.2 = (z' : V × (W × Z)).2.2 →
        (z : V × (W × Z)).1 = (z' : V × (W × Z)).1 → F z = F z') ∧
      (∀ z z' : Ball (V × (W × Z)), ‖(z : V × (W × Z)).2.2‖ = 1 →
        ‖(z' : V × (W × Z)).2.2‖ = 1 → (z : V × (W × Z)).2.1 = (z' : V × (W × Z)).2.1 →
        (z : V × (W × Z)).1 = (z' : V × (W × Z)).1 → F z = F z') :=
  Iff.rfl

/-! ## Boundary points of the product ball -/

lemma mem_bdry_of_fst {z : Ball (V × (W × Z))} (h : ‖(z : V × (W × Z)).1‖ = 1) :
    z ∈ bdry (V × (W × Z)) := by
  have h1 : ‖(z : V × (W × Z))‖ ≤ 1 := by
    have := Metric.mem_closedBall.mp z.2
    rwa [dist_eq_norm, sub_zero] at this
  show ‖(z : V × (W × Z))‖ = 1
  rw [Prod.norm_def, h]
  exact max_eq_left (le_trans (norm_snd_le _) h1)

lemma mem_bdry_of_w {z : Ball (V × (W × Z))} (h : ‖(z : V × (W × Z)).2.1‖ = 1) :
    z ∈ bdry (V × (W × Z)) := by
  have h1 : ‖(z : V × (W × Z))‖ ≤ 1 := by
    have := Metric.mem_closedBall.mp z.2
    rwa [dist_eq_norm, sub_zero] at this
  have h2 : ‖(z : V × (W × Z)).2‖ ≤ 1 := le_trans (norm_snd_le _) h1
  have h3 : ‖(z : V × (W × Z)).2‖ = 1 := by
    rw [Prod.norm_def, h]
    exact max_eq_left (le_trans (norm_snd_le _) h2)
  show ‖(z : V × (W × Z))‖ = 1
  rw [Prod.norm_def, h3]
  exact max_eq_right (le_trans (norm_fst_le _) h1)

lemma mem_bdry_of_z {z : Ball (V × (W × Z))} (h : ‖(z : V × (W × Z)).2.2‖ = 1) :
    z ∈ bdry (V × (W × Z)) := by
  have h1 : ‖(z : V × (W × Z))‖ ≤ 1 := by
    have := Metric.mem_closedBall.mp z.2
    rwa [dist_eq_norm, sub_zero] at this
  have h2 : ‖(z : V × (W × Z)).2‖ ≤ 1 := le_trans (norm_snd_le _) h1
  have h3 : ‖(z : V × (W × Z)).2‖ = 1 := by
    rw [Prod.norm_def, h]
    exact max_eq_right (le_trans (norm_fst_le _) h2)
  show ‖(z : V × (W × Z))‖ = 1
  rw [Prod.norm_def, h3]
  exact max_eq_right (le_trans (norm_fst_le _) h1)

/-- `ballAssoc` preserves the boundary. -/
lemma bdry_ballAssoc_iff (z : Ball (V × (W × Z))) :
    ballAssoc V W Z z ∈ bdry ((V × W) × Z) ↔ z ∈ bdry (V × (W × Z)) := by
  show ‖((ballAssoc V W Z z : Ball ((V × W) × Z)) : (V × W) × Z)‖ = 1 ↔
    ‖(z : V × (W × Z))‖ = 1
  rw [norm_ballAssoc]

/-! ## The inclusion of `Kpair (V × (W × Z))` -/

/-- The inclusion `C(D_{(V×(W×Z))}/∂) ⊆ C(S^a × S^b × S^c)`: a function constant on the whole
boundary is constant in each coordinate on its sphere. -/
def tripleIncl : Kpair (V × (W × Z)) →ₐ[ℂ] tripleAlg V W Z :=
  AlgHom.codRestrict (Kpair (V × (W × Z))).val (tripleAlg V W Z) (by
    intro F
    refine ⟨fun z z' h1 h2 _ _ => F.2 z (mem_bdry_of_fst V W Z h1) z'
        (mem_bdry_of_fst V W Z h2), fun z z' h1 h2 _ _ =>
        F.2 z (mem_bdry_of_w V W Z h1) z' (mem_bdry_of_w V W Z h2),
      fun z z' h1 h2 _ _ => F.2 z (mem_bdry_of_z V W Z h1) z'
        (mem_bdry_of_z V W Z h2)⟩)

@[simp] lemma tripleIncl_apply (F : Kpair (V × (W × Z))) :
    ((tripleIncl V W Z F : tripleAlg V W Z) : C(Ball (V × (W × Z)), ℂ))
      = (F : C(Ball (V × (W × Z)), ℂ)) := rfl

/-! ## The point maps into the triple product -/

lemma norm_projVW_le (z : Ball (V × (W × Z))) :
    ‖((((z : V × (W × Z)).1, (z : V × (W × Z)).2.1)) : V × W)‖ ≤ 1 := by
  rw [Prod.norm_def]
  exact max_le (norm_fst_le' V W Z z) (norm_w_le V W Z z)

/-- `(v,w,z) ↦ w` as a map of balls. -/
def projTripleW : C(Ball (V × (W × Z)), Ball W) where
  toFun z := ⟨(z : V × (W × Z)).2.1, mem_closedBall_zero_iff.mpr (norm_w_le V W Z z)⟩
  continuous_toFun := by fun_prop

/-- `(v,w,z) ↦ z` as a map of balls. -/
def projTripleZ : C(Ball (V × (W × Z)), Ball Z) where
  toFun z := ⟨(z : V × (W × Z)).2.2, mem_closedBall_zero_iff.mpr (norm_zc_le V W Z z)⟩
  continuous_toFun := by fun_prop

/-- `(v,w,z) ↦ (v,w)` as a map of balls. -/
def projTripleVW : C(Ball (V × (W × Z)), Ball (V × W)) where
  toFun z := ⟨((z : V × (W × Z)).1, (z : V × (W × Z)).2.1),
    mem_closedBall_zero_iff.mpr (norm_projVW_le V W Z z)⟩
  continuous_toFun := by fun_prop

@[simp] lemma projTripleW_apply (z : Ball (V × (W × Z))) :
    (projTripleW V W Z z : W) = (z : V × (W × Z)).2.1 := rfl
@[simp] lemma projTripleZ_apply (z : Ball (V × (W × Z))) :
    (projTripleZ V W Z z : Z) = (z : V × (W × Z)).2.2 := rfl
@[simp] lemma projTripleVW_apply (z : Ball (V × (W × Z))) :
    (projTripleVW V W Z z : V × W) = ((z : V × (W × Z)).1, (z : V × (W × Z)).2.1) := rfl
@[simp] lemma prFst_triple (z : Ball (V × (W × Z))) :
    (prFst V (W × Z) z : V) = (z : V × (W × Z)).1 := rfl
@[simp] lemma prSnd_triple (z : Ball (V × (W × Z))) :
    (prSnd V (W × Z) z : W × Z) = ((z : V × (W × Z)).2.1, (z : V × (W × Z)).2.2) := rfl
@[simp] lemma ballAssoc_coord (z : Ball (V × (W × Z))) :
    ((ballAssoc V W Z z : Ball ((V × W) × Z)) : (V × W) × Z)
      = (((z : V × (W × Z)).1, (z : V × (W × Z)).2.1), (z : V × (W × Z)).2.2) := rfl

lemma prSnd_fst (z : Ball (V × (W × Z))) :
    (prSnd V (W × Z) z : W × Z).1 = (z : V × (W × Z)).2.1 := rfl
lemma prSnd_snd (z : Ball (V × (W × Z))) :
    (prSnd V (W × Z) z : W × Z).2 = (z : V × (W × Z)).2.2 := rfl
lemma ballAssoc_fst (z : Ball (V × (W × Z))) :
    ((ballAssoc V W Z z : Ball ((V × W) × Z)) : (V × W) × Z).1
      = ((z : V × (W × Z)).1, (z : V × (W × Z)).2.1) := rfl
lemma ballAssoc_snd (z : Ball (V × (W × Z))) :
    ((ballAssoc V W Z z : Ball ((V × W) × Z)) : (V × W) × Z).2
      = (z : V × (W × Z)).2.2 := rfl
lemma projW_coord (z : Ball (V × (W × Z))) :
    (projTripleW V W Z z : W) = (z : V × (W × Z)).2.1 := rfl
lemma projZ_coord (z : Ball (V × (W × Z))) :
    (projTripleZ V W Z z : Z) = (z : V × (W × Z)).2.2 := rfl
lemma projVW_fst (z : Ball (V × (W × Z))) :
    (projTripleVW V W Z z : V × W).1 = (z : V × (W × Z)).1 := rfl
lemma projVW_snd (z : Ball (V × (W × Z))) :
    (projTripleVW V W Z z : V × W).2 = (z : V × (W × Z)).2.1 := rfl

/-! ## The inclusions into the triple algebra -/

/-- The inclusion `prodAlg V (W × Z) ⊆ tripleAlg V W Z`. -/
def tripleInclP : prodAlg V (W × Z) →ₐ[ℂ] tripleAlg V W Z :=
  AlgHom.codRestrict (prodAlg V (W × Z)).val (tripleAlg V W Z) (by
    intro F
    obtain ⟨hF1, hF2⟩ := F.2
    refine ⟨fun z z' h1 h2 h3 h4 => hF1 z z' h1 h2 (Prod.ext h3 h4), ?_, ?_⟩
    · intro z z' h1 h2 h3 h4
      refine hF2 z z' ?_ ?_ h4
      · rw [Prod.norm_def, h1]; exact max_eq_left (norm_zc_le V W Z z)
      · rw [Prod.norm_def, h2]; exact max_eq_left (norm_zc_le V W Z z')
    · intro z z' h1 h2 h3 h4
      refine hF2 z z' ?_ ?_ h4
      · rw [Prod.norm_def, h1]; exact max_eq_right (norm_w_le V W Z z)
      · rw [Prod.norm_def, h2]; exact max_eq_right (norm_w_le V W Z z'))

@[simp] lemma tripleInclP_apply (F : prodAlg V (W × Z)) :
    ((tripleInclP V W Z F : tripleAlg V W Z) : C(Ball (V × (W × Z)), ℂ))
      = (F : C(Ball (V × (W × Z)), ℂ)) := rfl

def tripleInclQ : prodAlg (V × W) Z →ₐ[ℂ] tripleAlg V W Z :=
  AlgHom.codRestrict
    ((pullAlg (ballAssoc V W Z)).comp (prodAlg (V × W) Z).val) (tripleAlg V W Z) (by
    intro F
    obtain ⟨hF1, hF2⟩ := F.2
    refine ⟨?_, ?_, ?_⟩
    · intro z z' h1 h2 h3 h4
      refine hF1 (ballAssoc V W Z z) (ballAssoc V W Z z') ?_ ?_ ?_
      · rw [ballAssoc_fst, Prod.norm_def, h1]
        exact max_eq_left (norm_w_le V W Z z)
      · rw [ballAssoc_fst, Prod.norm_def, h2]
        exact max_eq_left (norm_w_le V W Z z')
      · rw [ballAssoc_snd, ballAssoc_snd]; exact h4
    · intro z z' h1 h2 h3 h4
      refine hF1 (ballAssoc V W Z z) (ballAssoc V W Z z') ?_ ?_ ?_
      · rw [ballAssoc_fst, Prod.norm_def, h1]
        exact max_eq_right (norm_fst_le' V W Z z)
      · rw [ballAssoc_fst, Prod.norm_def, h2]
        exact max_eq_right (norm_fst_le' V W Z z')
      · rw [ballAssoc_snd, ballAssoc_snd]; exact h3
    · intro z z' h1 h2 h3 h4
      refine hF2 (ballAssoc V W Z z) (ballAssoc V W Z z') ?_ ?_ ?_
      · rw [ballAssoc_snd]; exact h1
      · rw [ballAssoc_snd]; exact h2
      · rw [ballAssoc_fst, ballAssoc_fst]; exact Prod.ext h4 h3)

@[simp] lemma tripleInclQ_apply (F : prodAlg (V × W) Z) :
    ((tripleInclQ V W Z F : tripleAlg V W Z) : C(Ball (V × (W × Z)), ℂ))
      = (pullAlg (ballAssoc V W Z)) (F : C(Ball ((V × W) × Z), ℂ)) := rfl

def tripleInclPW : prodAlg V W →ₐ[ℂ] tripleAlg V W Z :=
  AlgHom.codRestrict
    ((pullAlg (projTripleVW V W Z)).comp (prodAlg V W).val) (tripleAlg V W Z) (by
    intro F
    obtain ⟨hF1, hF2⟩ := F.2
    refine ⟨?_, ?_, ?_⟩
    · intro z z' h1 h2 h3 h4
      refine hF1 (projTripleVW V W Z z) (projTripleVW V W Z z') ?_ ?_ ?_
      · rw [projVW_fst]; exact h1
      · rw [projVW_fst]; exact h2
      · rw [projVW_snd, projVW_snd]; exact h3
    · intro z z' h1 h2 h3 h4
      refine hF2 (projTripleVW V W Z z) (projTripleVW V W Z z') ?_ ?_ ?_
      · rw [projVW_snd]; exact h1
      · rw [projVW_snd]; exact h2
      · rw [projVW_fst, projVW_fst]; exact h4
    · intro z z' h1 h2 h3 h4
      have hcoord : ∀ z : Ball (V × (W × Z)),
          (projTripleVW V W Z z : V × W) = ((z : V × (W × Z)).1, (z : V × (W × Z)).2.1) :=
        fun z => rfl
      have h : projTripleVW V W Z z = projTripleVW V W Z z' :=
        Subtype.ext (by rw [hcoord]; exact Prod.ext h4 h3)
      exact congrArg (fun w : Ball (V × W) => (F : C(Ball (V × W), ℂ)) w) h)

@[simp] lemma tripleInclPW_apply (F : prodAlg V W) :
    ((tripleInclPW V W Z F : tripleAlg V W Z) : C(Ball (V × (W × Z)), ℂ))
      = (pullAlg (projTripleVW V W Z)) (F : C(Ball (V × W), ℂ)) := rfl

def tripleInclWZ : prodAlg W Z →ₐ[ℂ] tripleAlg V W Z :=
  AlgHom.codRestrict
    ((pullAlg (prSnd V (W × Z))).comp (prodAlg W Z).val) (tripleAlg V W Z) (by
    intro F
    obtain ⟨hF1, hF2⟩ := F.2
    refine ⟨?_, ?_, ?_⟩
    · intro z z' h1 h2 h3 h4
      have hcoord : ∀ z : Ball (V × (W × Z)),
          (prSnd V (W × Z) z : W × Z) = ((z : V × (W × Z)).2.1, (z : V × (W × Z)).2.2) :=
        fun z => rfl
      have h : prSnd V (W × Z) z = prSnd V (W × Z) z' :=
        Subtype.ext (by rw [hcoord]; exact Prod.ext h3 h4)
      exact congrArg (fun w : Ball (W × Z) => (F : C(Ball (W × Z), ℂ)) w) h
    · intro z z' h1 h2 h3 h4
      refine hF1 (prSnd V (W × Z) z) (prSnd V (W × Z) z') ?_ ?_ ?_
      · rw [prSnd_fst]; exact h1
      · rw [prSnd_fst]; exact h2
      · rw [prSnd_snd, prSnd_snd]; exact h3
    · intro z z' h1 h2 h3 h4
      refine hF2 (prSnd V (W × Z) z) (prSnd V (W × Z) z') ?_ ?_ ?_
      · rw [prSnd_snd]; exact h1
      · rw [prSnd_snd]; exact h2
      · rw [prSnd_fst, prSnd_fst]; exact h3)

@[simp] lemma tripleInclWZ_apply (F : prodAlg W Z) :
    ((tripleInclWZ V W Z F : tripleAlg V W Z) : C(Ball (V × (W × Z)), ℂ))
      = (pullAlg (prSnd V (W × Z))) (F : C(Ball (W × Z), ℂ)) := rfl

def tripleIncl' : Kpair ((V × W) × Z) →ₐ[ℂ] tripleAlg V W Z :=
  AlgHom.codRestrict
    ((pullAlg (ballAssoc V W Z)).comp (Kpair ((V × W) × Z)).val) (tripleAlg V W Z) (by
    intro F
    refine ⟨fun z z' h1 h2 _ _ =>
        F.2 _ ((bdry_ballAssoc_iff V W Z z).mpr (mem_bdry_of_fst V W Z h1)) _
          ((bdry_ballAssoc_iff V W Z z').mpr (mem_bdry_of_fst V W Z h2)),
      fun z z' h1 h2 _ _ =>
        F.2 _ ((bdry_ballAssoc_iff V W Z z).mpr (mem_bdry_of_w V W Z h1)) _
          ((bdry_ballAssoc_iff V W Z z').mpr (mem_bdry_of_w V W Z h2)),
      fun z z' h1 h2 _ _ =>
        F.2 _ ((bdry_ballAssoc_iff V W Z z).mpr (mem_bdry_of_z V W Z h1)) _
          ((bdry_ballAssoc_iff V W Z z').mpr (mem_bdry_of_z V W Z h2))⟩)

@[simp] lemma tripleIncl'_apply (F : Kpair ((V × W) × Z)) :
    ((tripleIncl' V W Z F : tripleAlg V W Z) : C(Ball (V × (W × Z)), ℂ))
      = (pullAlg (ballAssoc V W Z)) (F : C(Ball ((V × W) × Z), ℂ)) := rfl

def triplePullV : Kpair V →ₐ[ℂ] tripleAlg V W Z :=
  AlgHom.codRestrict ((pullAlg (prFst V (W × Z))).comp (Kpair V).val) (tripleAlg V W Z) (by
    intro F
    refine ⟨fun z z' h1 h2 _ _ => F.2 _ (by rw [bdry]; exact h1) _
        (by rw [bdry]; exact h2), ?_, ?_⟩
    · intro z z' _ _ _ h4
      have h : prFst V (W × Z) z = prFst V (W × Z) z' := Subtype.ext (by
        rw [prFst_triple, prFst_triple]; exact h4)
      exact congrArg (fun w : Ball V => (F : C(Ball V, ℂ)) w) h
    · intro z z' _ _ _ h4
      have h : prFst V (W × Z) z = prFst V (W × Z) z' := Subtype.ext (by
        rw [prFst_triple, prFst_triple]; exact h4)
      exact congrArg (fun w : Ball V => (F : C(Ball V, ℂ)) w) h)

@[simp] lemma triplePullV_apply (F : Kpair V) :
    ((triplePullV V W Z F : tripleAlg V W Z) : C(Ball (V × (W × Z)), ℂ))
      = (pullAlg (prFst V (W × Z))) (F : C(Ball V, ℂ)) := rfl

def triplePullW : Kpair W →ₐ[ℂ] tripleAlg V W Z :=
  AlgHom.codRestrict ((pullAlg (projTripleW V W Z)).comp (Kpair W).val) (tripleAlg V W Z) (by
    intro F
    refine ⟨?_, fun z z' h1 h2 _ _ => F.2 _ (by rw [bdry]; exact h1) _
        (by rw [bdry]; exact h2), ?_⟩
    · intro z z' _ _ h3 h4
      have h : projTripleW V W Z z = projTripleW V W Z z' := Subtype.ext (by
        rw [projW_coord, projW_coord]; exact h3)
      exact congrArg (fun w : Ball W => (F : C(Ball W, ℂ)) w) h
    · intro z z' _ _ h3 h4
      have h : projTripleW V W Z z = projTripleW V W Z z' := Subtype.ext (by
        rw [projW_coord, projW_coord]; exact h3)
      exact congrArg (fun w : Ball W => (F : C(Ball W, ℂ)) w) h)

@[simp] lemma triplePullW_apply (F : Kpair W) :
    ((triplePullW V W Z F : tripleAlg V W Z) : C(Ball (V × (W × Z)), ℂ))
      = (pullAlg (projTripleW V W Z)) (F : C(Ball W, ℂ)) := rfl

def triplePullZ : Kpair Z →ₐ[ℂ] tripleAlg V W Z :=
  AlgHom.codRestrict ((pullAlg (projTripleZ V W Z)).comp (Kpair Z).val) (tripleAlg V W Z) (by
    intro F
    refine ⟨?_, ?_, fun z z' h1 h2 _ _ => F.2 _ (by rw [bdry]; exact h1) _
        (by rw [bdry]; exact h2)⟩
    · intro z z' _ _ _ h4
      have h : projTripleZ V W Z z = projTripleZ V W Z z' := Subtype.ext (by
        rw [projZ_coord, projZ_coord]; exact h4)
      exact congrArg (fun w : Ball Z => (F : C(Ball Z, ℂ)) w) h
    · intro z z' _ _ h3 h4
      have h : projTripleZ V W Z z = projTripleZ V W Z z' := Subtype.ext (by
        rw [projZ_coord, projZ_coord]; exact h3)
      exact congrArg (fun w : Ball Z => (F : C(Ball Z, ℂ)) w) h)

@[simp] lemma triplePullZ_apply (F : Kpair Z) :
    ((triplePullZ V W Z F : tripleAlg V W Z) : C(Ball (V × (W × Z)), ℂ))
      = (pullAlg (projTripleZ V W Z)) (F : C(Ball Z, ℂ)) := rfl

def triplePullVW : Kpair (V × W) →ₐ[ℂ] tripleAlg V W Z :=
  AlgHom.codRestrict ((pullAlg (projTripleVW V W Z)).comp (Kpair (V × W)).val)
    (tripleAlg V W Z) (by
    intro F
    have hcoord : ∀ z : Ball (V × (W × Z)),
        (projTripleVW V W Z z : V × W) = ((z : V × (W × Z)).1, (z : V × (W × Z)).2.1) :=
      fun z => rfl
    have hbV : ∀ z : Ball (V × (W × Z)), ‖(z : V × (W × Z)).1‖ = 1 →
        projTripleVW V W Z z ∈ bdry (V × W) := by
      intro z h
      show ‖(projTripleVW V W Z z : V × W)‖ = 1
      rw [hcoord, Prod.norm_def, h]
      exact max_eq_left (norm_w_le V W Z z)
    have hbW : ∀ z : Ball (V × (W × Z)), ‖(z : V × (W × Z)).2.1‖ = 1 →
        projTripleVW V W Z z ∈ bdry (V × W) := by
      intro z h
      show ‖(projTripleVW V W Z z : V × W)‖ = 1
      rw [hcoord, Prod.norm_def, h]
      exact max_eq_right (norm_fst_le' V W Z z)
    refine ⟨fun z z' h1 h2 _ _ => F.2 _ (hbV z h1) _ (hbV z' h2), ?_, ?_⟩
    · intro z z' h1 h2 _ _
      exact F.2 _ (hbW z h1) _ (hbW z' h2)
    · intro z z' _ _ h3 h4
      have h : projTripleVW V W Z z = projTripleVW V W Z z' :=
        Subtype.ext (by rw [hcoord]; exact Prod.ext h4 h3)
      exact congrArg (fun w : Ball (V × W) => (F : C(Ball (V × W), ℂ)) w) h)

@[simp] lemma triplePullVW_apply (F : Kpair (V × W)) :
    ((triplePullVW V W Z F : tripleAlg V W Z) : C(Ball (V × (W × Z)), ℂ))
      = (pullAlg (projTripleVW V W Z)) (F : C(Ball (V × W), ℂ)) := rfl

def triplePullWZ : Kpair (W × Z) →ₐ[ℂ] tripleAlg V W Z :=
  AlgHom.codRestrict ((pullAlg (prSnd V (W × Z))).comp (Kpair (W × Z)).val)
    (tripleAlg V W Z) (by
    intro F
    have hcoord : ∀ z : Ball (V × (W × Z)),
        (prSnd V (W × Z) z : W × Z) = ((z : V × (W × Z)).2.1, (z : V × (W × Z)).2.2) :=
      fun z => rfl
    have hbW : ∀ z : Ball (V × (W × Z)), ‖(z : V × (W × Z)).2.1‖ = 1 →
        prSnd V (W × Z) z ∈ bdry (W × Z) := by
      intro z h
      show ‖(prSnd V (W × Z) z : W × Z)‖ = 1
      rw [hcoord, Prod.norm_def, h]
      exact max_eq_left (norm_zc_le V W Z z)
    have hbZ : ∀ z : Ball (V × (W × Z)), ‖(z : V × (W × Z)).2.2‖ = 1 →
        prSnd V (W × Z) z ∈ bdry (W × Z) := by
      intro z h
      show ‖(prSnd V (W × Z) z : W × Z)‖ = 1
      rw [hcoord, Prod.norm_def, h]
      exact max_eq_right (norm_w_le V W Z z)
    refine ⟨?_, fun z z' h1 h2 _ _ => F.2 _ (hbW z h1) _ (hbW z' h2),
      fun z z' h1 h2 _ _ => F.2 _ (hbZ z h1) _ (hbZ z' h2)⟩
    · intro z z' _ _ h3 h4
      have h : prSnd V (W × Z) z = prSnd V (W × Z) z' :=
        Subtype.ext (by rw [hcoord]; exact Prod.ext h3 h4)
      exact congrArg (fun w : Ball (W × Z) => (F : C(Ball (W × Z), ℂ)) w) h)

@[simp] lemma triplePullWZ_apply (F : Kpair (W × Z)) :
    ((triplePullWZ V W Z F : tripleAlg V W Z) : C(Ball (V × (W × Z)), ℂ))
      = (pullAlg (prSnd V (W × Z))) (F : C(Ball (W × Z), ℂ)) := rfl

/-! ## Commutation of the comparison maps -/

lemma tripleInclP_comp_smashIncl :
    (tripleInclP V W Z).comp (smashIncl V (W × Z)) = tripleIncl V W Z :=
  AlgHom.ext fun _ => Subtype.ext rfl

lemma tripleInclP_comp_pullFst :
    (tripleInclP V W Z).comp (pullFst V (W × Z)) = triplePullV V W Z :=
  AlgHom.ext fun _ => Subtype.ext rfl

lemma tripleInclP_comp_pullSnd :
    (tripleInclP V W Z).comp (pullSnd V (W × Z)) = triplePullWZ V W Z :=
  AlgHom.ext fun _ => Subtype.ext rfl

lemma tripleInclWZ_comp_smashIncl :
    (tripleInclWZ V W Z).comp (smashIncl W Z) = triplePullWZ V W Z :=
  AlgHom.ext fun _ => Subtype.ext rfl

lemma tripleInclWZ_comp_pullFst :
    (tripleInclWZ V W Z).comp (pullFst W Z) = triplePullW V W Z :=
  AlgHom.ext fun _ => Subtype.ext rfl

lemma tripleInclWZ_comp_pullSnd :
    (tripleInclWZ V W Z).comp (pullSnd W Z) = triplePullZ V W Z :=
  AlgHom.ext fun _ => Subtype.ext rfl

lemma tripleInclQ_comp_smashIncl :
    (tripleInclQ V W Z).comp (smashIncl (V × W) Z) = tripleIncl' V W Z :=
  AlgHom.ext fun _ => Subtype.ext rfl

lemma tripleInclPW_comp_smashIncl :
    (tripleInclPW V W Z).comp (smashIncl V W) = triplePullVW V W Z :=
  AlgHom.ext fun _ => Subtype.ext rfl

lemma tripleInclPW_comp_pullFst :
    (tripleInclPW V W Z).comp (pullFst V W) = triplePullV V W Z :=
  AlgHom.ext fun _ => Subtype.ext rfl

lemma tripleInclPW_comp_pullSnd :
    (tripleInclPW V W Z).comp (pullSnd V W) = triplePullW V W Z :=
  AlgHom.ext fun _ => Subtype.ext rfl

lemma tripleInclQ_comp_pullFst :
    (tripleInclQ V W Z).comp (pullFst (V × W) Z) = triplePullVW V W Z :=
  AlgHom.ext fun _ => Subtype.ext rfl

lemma tripleInclQ_comp_pullSnd :
    (tripleInclQ V W Z).comp (pullSnd (V × W) Z) = triplePullZ V W Z :=
  AlgHom.ext fun _ => Subtype.ext rfl





lemma tripleIncl'_eq_comp_pairAssoc :
    tripleIncl' V W Z
      = (tripleIncl V W Z).comp (pairAssocEquiv V W Z).toAlgHom :=
  AlgHom.ext fun _ => Subtype.ext rfl

/-! ## Compatibility with the augmentations -/

lemma augPair_comp_pairAssocEquiv (y : Ball (V × (W × Z))) :
    (augPair (V × (W × Z)) y).comp (pairAssocEquiv V W Z).toAlgHom
      = augPair ((V × W) × Z) (ballAssoc V W Z y) := by
  apply AlgHom.ext
  intro F
  have h1 : (((pairAssocEquiv V W Z).toAlgHom F : Kpair (V × (W × Z))) :
      C(Ball (V × (W × Z)), ℂ))
      = ((tripleIncl' V W Z F : tripleAlg V W Z) : C(Ball (V × (W × Z)), ℂ)) := rfl
  change (((pairAssocEquiv V W Z).toAlgHom F : Kpair (V × (W × Z))) :
      C(Ball (V × (W × Z)), ℂ)) y
      = (F : C(Ball ((V × W) × Z), ℂ)) (ballAssoc V W Z y)
  rw [h1, tripleIncl'_apply]
  rfl

end

end ExtGen

end Work.KT
