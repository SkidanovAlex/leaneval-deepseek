import Mathlib
import Submission.Work.WilCruxN.FSMemShapes

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Classical

namespace Work.WilCruxN.FSA

open WilkiesDesign WilkiesDesign.CG
open Work.WilG4c

/-! ## 8. The failure set (first conjunct) -/

/-- The blocks of the big ambient space `(w, ε, δ, z, u)`. -/
def fwSub (a : ℕ) (i : Fin a) : Fin (a + 2) := ⟨i.val, by omega⟩
def feSub (a : ℕ) : Fin (a + 2) := ⟨a, by omega⟩
def fdSub (a : ℕ) : Fin (a + 2) := ⟨a + 1, by omega⟩
def fzSub (b : ℕ) (j : Fin b) : Fin (b + 1) := ⟨j.val, by omega⟩
def fuSub (b : ℕ) : Fin (b + 1) := Fin.last b

def fwIdx (a b : ℕ) (i : Fin a) : Fin ((a + 2) + (b + 1)) := Fin.castAdd (b + 1) (fwSub a i)
def feIdx (a b : ℕ) : Fin ((a + 2) + (b + 1)) := Fin.castAdd (b + 1) (feSub a)
def fdIdx (a b : ℕ) : Fin ((a + 2) + (b + 1)) := Fin.castAdd (b + 1) (fdSub a)
def fzIdx (a b : ℕ) (j : Fin b) : Fin ((a + 2) + (b + 1)) := Fin.natAdd (a + 2) (fzSub b j)
def fuIdx (a b : ℕ) : Fin ((a + 2) + (b + 1)) := Fin.natAdd (a + 2) (fuSub b)

/-- The index map placing the graph point `(w, z, u)` into `(w, ε, δ, z, u)`. -/
def fGIdx (a b : ℕ) : Fin (a + b + 1) → Fin ((a + 2) + (b + 1)) :=
  memIdx (fwIdx a b) (fzIdx a b) (fuIdx a b)

/-- The index map placing `(z, δ)` into `(w, ε, δ, z, u)`. -/
def ballIdx (a b : ℕ) : Fin (b + 1) → Fin ((a + 2) + (b + 1)) :=
  Fin.snoc (fun j : Fin b => fzIdx a b j) (fdIdx a b)

@[simp] lemma append_fwIdx {a b : ℕ} (y : Fin (a + 2) → ℝ) (v : Fin (b + 1) → ℝ) (i : Fin a) :
    (Fin.append y v) (fwIdx a b i) = y (fwSub a i) := by
  rw [fwIdx, Fin.append_left]

@[simp] lemma append_fzIdx {a b : ℕ} (y : Fin (a + 2) → ℝ) (v : Fin (b + 1) → ℝ) (j : Fin b) :
    (Fin.append y v) (fzIdx a b j) = v (fzSub b j) := by
  rw [fzIdx, Fin.append_right]

@[simp] lemma append_fuIdx {a b : ℕ} (y : Fin (a + 2) → ℝ) (v : Fin (b + 1) → ℝ) :
    (Fin.append y v) (fuIdx a b) = v (Fin.last b) := by
  rw [fuIdx, fuSub, Fin.append_right]

@[simp] lemma append_feIdx {a b : ℕ} (y : Fin (a + 2) → ℝ) (v : Fin (b + 1) → ℝ) :
    (Fin.append y v) (feIdx a b) = y (feSub a) := by
  rw [feIdx, Fin.append_left]

@[simp] lemma append_fdIdx {a b : ℕ} (y : Fin (a + 2) → ℝ) (v : Fin (b + 1) → ℝ) :
    (Fin.append y v) (fdIdx a b) = y (fdSub a) := by
  rw [fdIdx, Fin.append_left]

@[simp] lemma snoc_fzSub {b : ℕ} (z : Fin b → ℝ) (u : ℝ) (j : Fin b) :
    ((Fin.snoc (α := fun _ : Fin (b+1) => ℝ) z u)) (fzSub b j) = z j := by
  have h : fzSub b j = j.castSucc := rfl
  rw [h, Fin.snoc_castSucc]

@[simp] lemma snoc2_fwSub {a : ℕ} (w : Fin a → ℝ) (ε δ : ℝ) (i : Fin a) :
    ((Fin.snoc (α := fun _ : Fin (a+2) => ℝ)
        (Fin.snoc (α := fun _ : Fin (a+1) => ℝ) w ε) δ)) (fwSub a i) = w i := by
  have h : fwSub a i = (i.castSucc).castSucc := rfl
  rw [h, Fin.snoc_castSucc, Fin.snoc_castSucc]

@[simp] lemma snoc2_feSub {a : ℕ} (w : Fin a → ℝ) (ε δ : ℝ) :
    ((Fin.snoc (α := fun _ : Fin (a+2) => ℝ)
        (Fin.snoc (α := fun _ : Fin (a+1) => ℝ) w ε) δ)) (feSub a) = ε := by
  have h : feSub a = (Fin.last a).castSucc := rfl
  rw [h, Fin.snoc_castSucc, Fin.snoc_last]

@[simp] lemma snoc2_fdSub {a : ℕ} (w : Fin a → ℝ) (ε δ : ℝ) :
    ((Fin.snoc (α := fun _ : Fin (a+2) => ℝ)
        (Fin.snoc (α := fun _ : Fin (a+1) => ℝ) w ε) δ)) (fdSub a) = δ := by
  have h : fdSub a = Fin.last (a+1) := rfl
  rw [h, Fin.snoc_last]

@[simp] lemma ballIdx_castSucc {a b : ℕ} (j : Fin b) :
    ballIdx a b (Fin.castSucc j) = fzIdx a b j := Fin.snoc_castSucc ..

@[simp] lemma ballIdx_last {a b : ℕ} : ballIdx a b (Fin.last b) = fdIdx a b :=
  Fin.snoc_last ..

/-- `{x | x (feIdx) ≤ |x (fuIdx)|}`. -/
def fEpsU (S : SOMin) (F D : ℕ) (a b : ℕ) : PKS S F D ((a + 2) + (b + 1)) :=
  PKS.neg (PKS.conj
    (PKS.neg (leS S F D (MvPolynomial.X (feIdx a b)) (MvPolynomial.X (fuIdx a b))
      (td_X4 _) (td_X4 _)))
    (PKS.neg (leS S F D (MvPolynomial.X (feIdx a b)) (-(MvPolynomial.X (fuIdx a b)))
      (td_X4 _) (td_negX4 _))))

theorem fEpsU_Real (S : SOMin) (F D a b : ℕ) :
    (fEpsU S F D a b).Real = {x : Fin ((a + 2) + (b + 1)) → ℝ |
      x (feIdx a b) ≤ |x (fuIdx a b)|} := by
  ext x
  simp only [fEpsU, PKS.Real_neg, PKS.Real_conj, leS_Real, Set.mem_compl_iff,
    Set.mem_inter_iff, Set.mem_ofPred_eq, MvPolynomial.eval_X, MvPolynomial.eval_neg]
  rw [le_abs]
  tauto

/-- The inner shape of the failure construction, in the space `(w, ε, δ, z, u)`. -/
def failInner (S : SOMin) (F D : ℕ) {a b : ℕ}
    (f : (Fin a → ℝ) → (Fin b → ℝ) → ℝ) (hG : famGraph f ∈ S.Ω F D (a + b + 1))
    (hSup : supBallSet b ∈ S.Ω F D (b + 1)) : PKS S F D ((a + 2) + (b + 1)) :=
  PKS.conj (PKS.mem (famGraph f) hG (fGIdx a b))
    (PKS.conj (sumSqNe S F D (fzIdx a b))
      (PKS.conj (PKS.mem (supBallSet b) hSup (ballIdx a b)) (fEpsU S F D a b)))

theorem failInner_Real (S : SOMin) (F D : ℕ) {a b : ℕ}
    (f : (Fin a → ℝ) → (Fin b → ℝ) → ℝ) (hG : famGraph f ∈ S.Ω F D (a + b + 1))
    (hSup : supBallSet b ∈ S.Ω F D (b + 1)) :
    (failInner S F D f hG hSup).Real = {x : Fin ((a + 2) + (b + 1)) → ℝ |
      x (fuIdx a b) = f (fun i => x (fwIdx a b i)) (fun j => x (fzIdx a b j)) ∧
      (fun j => x (fzIdx a b j)) ≠ 0 ∧
      (∀ j, (x (fzIdx a b j)) ^ 2 < (x (fdIdx a b)) ^ 2) ∧
      x (feIdx a b) ≤ |x (fuIdx a b)|} := by
  ext x
  simp only [failInner, PKS.Real_conj, Set.mem_inter_iff, PKS.Real_mem, Set.mem_ofPred_eq,
    sumSqNe_Real, fEpsU_Real, fGIdx, memIdx_comp, supBallSet, ballIdx,
    Function.comp_apply, Fin.snoc_castSucc, Fin.snoc_last]
  constructor
  · rintro ⟨hmem, hz, hball, he⟩
    have hmem' : x (fuIdx a b)
        = f (fun i => x (fwIdx a b i)) (fun j => x (fzIdx a b j)) := by
      rw [mem_famGraph_snoc] at hmem
      simpa only [Function.comp_apply, Fin.append_left, Fin.append_right] using hmem
    exact ⟨hmem', hz, hball, he⟩
  · rintro ⟨hmem, hz, hball, he⟩
    refine ⟨?_, hz, hball, he⟩
    rw [mem_famGraph_snoc]
    simpa only [Function.comp_apply, Fin.append_left, Fin.append_right] using hmem

/-- The projection of `failInner` onto `(w, ε, δ)`. -/
def failExb (S : SOMin) (F D : ℕ) {a b : ℕ}
    (f : (Fin a → ℝ) → (Fin b → ℝ) → ℝ) (hG : famGraph f ∈ S.Ω F D (a + b + 1))
    (hSup : supBallSet b ∈ S.Ω F D (b + 1)) : PKS S F D (a + 2) :=
  PKS.exb (k := b + 1) (failInner S F D f hG hSup)

theorem failExb_Real (S : SOMin) (F D : ℕ) {a b : ℕ}
    (f : (Fin a → ℝ) → (Fin b → ℝ) → ℝ) (hG : famGraph f ∈ S.Ω F D (a + b + 1))
    (hSup : supBallSet b ∈ S.Ω F D (b + 1)) :
    (failExb S F D f hG hSup).Real = {y : Fin (a + 2) → ℝ |
      ∃ v : Fin (b + 1) → ℝ, Fin.append y v ∈ (failInner S F D f hG hSup).Real} := by
  rw [failExb, PKS.Real_exb, Work.WilG5.projN]

/-- `δ > 0 → failExb`, as a shape on `(w, ε, δ)`. -/
def failD (S : SOMin) (F D : ℕ) {a b : ℕ}
    (f : (Fin a → ℝ) → (Fin b → ℝ) → ℝ) (hG : famGraph f ∈ S.Ω F D (a + b + 1))
    (hSup : supBallSet b ∈ S.Ω F D (b + 1)) : PKS S F D (a + 2) :=
  PKS.imp (posS S F D (Fin.last (a + 1))) (failExb S F D f hG hSup)

theorem failD_Real (S : SOMin) (F D : ℕ) {a b : ℕ}
    (f : (Fin a → ℝ) → (Fin b → ℝ) → ℝ) (hG : famGraph f ∈ S.Ω F D (a + b + 1))
    (hSup : supBallSet b ∈ S.Ω F D (b + 1)) :
    (failD S F D f hG hSup).Real = {x : Fin (a + 2) → ℝ |
      0 < x (Fin.last (a + 1)) → x ∈ (failExb S F D f hG hSup).Real} := by
  ext x
  rw [failD, PKS.Real_imp, posS_Real]
  simp only [Set.mem_union, Set.mem_compl_iff, Set.mem_ofPred_eq]
  constructor
  · rintro (h | h)
    · intro hc; exact absurd hc h
    · intro _; exact h
  · intro h
    by_cases hc : 0 < x (Fin.last (a + 1))
    · exact Or.inr (h hc)
    · exact Or.inl hc

/-- `∀ δ, failD`, as a shape on `(w, ε)`. -/
def failAll (S : SOMin) (F D : ℕ) {a b : ℕ}
    (f : (Fin a → ℝ) → (Fin b → ℝ) → ℝ) (hG : famGraph f ∈ S.Ω F D (a + b + 1))
    (hSup : supBallSet b ∈ S.Ω F D (b + 1)) : PKS S F D (a + 1) :=
  PKS.allOne (failD S F D f hG hSup)

theorem failAll_Real (S : SOMin) (F D : ℕ) {a b : ℕ}
    (f : (Fin a → ℝ) → (Fin b → ℝ) → ℝ) (hG : famGraph f ∈ S.Ω F D (a + b + 1))
    (hSup : supBallSet b ∈ S.Ω F D (b + 1)) :
    (failAll S F D f hG hSup).Real = {p : Fin (a + 1) → ℝ |
      ∀ t : ℝ, Fin.snoc p t ∈ (failD S F D f hG hSup).Real} := by
  rw [failAll, PKS.Real_allOne]

/-- The failure shape. -/
def failShape (S : SOMin) (F D : ℕ) {a b : ℕ}
    (f : (Fin a → ℝ) → (Fin b → ℝ) → ℝ) (hG : famGraph f ∈ S.Ω F D (a + b + 1))
    (hSup : supBallSet b ∈ S.Ω F D (b + 1)) : PKS S F D a :=
  PKS.exi (PKS.conj (posS S F D (Fin.last a)) (failAll S F D f hG hSup))

theorem failShape_Real (S : SOMin) (F D : ℕ) {a b : ℕ}
    (f : (Fin a → ℝ) → (Fin b → ℝ) → ℝ) (hG : famGraph f ∈ S.Ω F D (a + b + 1))
    (hSup : supBallSet b ∈ S.Ω F D (b + 1)) :
    (failShape S F D f hG hSup).Real =
      {w : Fin a → ℝ | ∃ ε > 0, ∀ δ > 0, ∃ z : Fin b → ℝ,
        z ≠ 0 ∧ (∀ j, (z j) ^ 2 < δ ^ 2) ∧ ε ≤ |f w z|} := by
  ext w
  rw [failShape, PKS.Real_exi]
  simp only [projLast, Set.mem_ofPred_eq, PKS.Real_conj, Set.mem_inter_iff, posS_Real,
    Set.mem_ofPred_eq, failAll_Real]
  constructor
  · rintro ⟨ε, hε, hall⟩
    refine ⟨ε, by simpa using hε, fun δ hδ => ?_⟩
    have h3 := hall δ
    simp only [failD_Real, Set.mem_ofPred_eq] at h3
    have h4 := h3 (by simpa using hδ)
    simp only [failExb_Real, failInner_Real, Set.mem_ofPred_eq] at h4
    obtain ⟨v, hv⟩ := h4
    simp only [append_fwIdx, append_fzIdx, append_fuIdx, append_fdIdx, append_feIdx,
      Function.comp_apply, snoc2_fwSub, snoc2_feSub, snoc2_fdSub] at hv
    refine ⟨fun j => v (fzSub b j), hv.2.1, hv.2.2.1, ?_⟩
    have key : f w (fun j => v (fzSub b j)) = v (Fin.last b) := hv.1.symm
    rw [key]; exact hv.2.2.2
  · rintro ⟨ε, hε, hall⟩
    refine ⟨ε, by simpa using hε, fun δ => ?_⟩
    simp only [failD_Real, Set.mem_ofPred_eq]
    intro hδ
    simp only [failExb_Real, Set.mem_ofPred_eq]
    obtain ⟨z, hz0, hzc, hzε⟩ := hall δ (by simpa using hδ)
    refine ⟨Fin.snoc z (f w z), ?_⟩
    simp only [failInner_Real, Set.mem_ofPred_eq]
    simp only [append_fwIdx, append_fzIdx, append_fuIdx, append_fdIdx, append_feIdx,
      Function.comp_apply, snoc2_fwSub, snoc2_feSub, snoc2_fdSub, snoc_fzSub, Fin.snoc_last]
    exact ⟨trivial, hz0, hzc, hzε⟩

/-! ## The format and atom count of `failShape` are independent of the data -/

lemma failShape_Fmt_eq (S : SOMin) (F : ℕ) {a b : ℕ} (D₁ D₂ : ℕ)
    (f₁ : (Fin a → ℝ) → (Fin b → ℝ) → ℝ) (hG₁ : famGraph f₁ ∈ S.Ω F D₁ (a + b + 1))
    (hS₁ : supBallSet b ∈ S.Ω F D₁ (b + 1))
    (f₂ : (Fin a → ℝ) → (Fin b → ℝ) → ℝ) (hG₂ : famGraph f₂ ∈ S.Ω F D₂ (a + b + 1))
    (hS₂ : supBallSet b ∈ S.Ω F D₂ (b + 1)) :
    (failShape S F D₁ f₁ hG₁ hS₁).Fmt = (failShape S F D₂ f₂ hG₂ hS₂).Fmt := rfl

lemma failShape_Atoms_eq (S : SOMin) (F : ℕ) {a b : ℕ} (D₁ D₂ : ℕ)
    (f₁ : (Fin a → ℝ) → (Fin b → ℝ) → ℝ) (hG₁ : famGraph f₁ ∈ S.Ω F D₁ (a + b + 1))
    (hS₁ : supBallSet b ∈ S.Ω F D₁ (b + 1))
    (f₂ : (Fin a → ℝ) → (Fin b → ℝ) → ℝ) (hG₂ : famGraph f₂ ∈ S.Ω F D₂ (a + b + 1))
    (hS₂ : supBallSet b ∈ S.Ω F D₂ (b + 1)) :
    (failShape S F D₁ f₁ hG₁ hS₁).Atoms = (failShape S F D₂ f₂ hG₂ hS₂).Atoms := rfl

end Work.WilCruxN.FSA
