/-
  WilG4c — self-contained proof of the composition step of the BNZ §5.4 surrogate
  (`Work.WilG4c.surrogateComp`, in case the delegated sibling is unavailable).

  Given an `Ω`-set `A ⊆ ℝ^{p+(n+1)+1}` (the derivative graph `AlDgList`, coordinates `(w,t)`)
  and the `n` coordinate maps `φ_j : ℝ^{p+1} → ℝ` of the curve `γ`, the "surrogate set"
  `{z | (∃ t, (xPt (init z) (φ (init z)), t) ∈ A ∧ z last = (t+2)/4) ∨
        (xPt (init z) (φ (init z)) ∉ projLast A ∧ z last = 1/2)}`

  is `Ω`-definable at format `F₁ + F₂ + C₁` and degree `2*D₁ + n*D₂ + C₂`.

  Construction: in `ℝ^{(p+1+1) + (p+(n+1))}` laid out as `(x : p+1, v, w : p+(n+1))`,
  intersect
  * the branch set of `Work.WilG4c.surrogateBranch` for `A`, transported to the `(v,w)`-block;
  * the `p+1` relations `w_i = x_i`;
  * the `n` relations `w_{p+1+j} = φ_j x`;
  and project the `w`-block away.  The `(v,w)`-block transport keeps `A` at coefficient `1` in
  the format and `2` in the degree, and each `graphOf φ_j` is used once, so the degree of the
  curve contributes exactly `n * D₂`.
-/
import Mathlib
import Submission.Work.Wilkies.CG.Spec
import Submission.Work.Wilkies.Defs
import Submission.Work.WilG1.Basic
import Submission.Work.WilG5.Reindex3
import Submission.Work.WilG0.API
import Submission.Work.WilG0.projLastIter_eq
import Submission.Work.WilG0.projLastIter_mem
import Submission.Work.WilG0.snocIt_castAdd
import Submission.Work.WilG0.snocIt_natAdd
import Submission.Work.WilG0.snocIt_injective
import Submission.Work.WilG4c.surrogateBranch
import Submission.Work.WilG4c.LipDefs

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilG4c

open WilkiesDesign

namespace SurComp

variable (p n : ℕ)

/-! ## 1. Index maps of the auxiliary space `ℝ^{(p+1+1) + (p+(n+1))}` -/

/-- The `i`-th coordinate of the `(l,x)`-part of the final point. -/
def aIdx (i : Fin (p + 1)) : Fin ((p + 1 + 1) + (p + (n + 1))) :=
  Fin.castAdd (p + (n + 1)) (Fin.castSucc i)

/-- The coordinate holding the value `v`. -/
def vIdx : Fin ((p + 1 + 1) + (p + (n + 1))) :=
  Fin.castAdd (p + (n + 1)) (Fin.last (p + 1))

/-- The `k`-th coordinate of the `w`-block. -/
def wIdx (k : Fin (p + (n + 1))) : Fin ((p + 1 + 1) + (p + (n + 1))) :=
  Fin.natAdd (p + 1 + 1) k

/-- The `w`-coordinate matching the `i`-th coordinate of the `(l,x)`-part. -/
def lIdx (i : Fin (p + 1)) : Fin (p + (n + 1)) :=
  Fin.lastCases (Fin.natAdd p 0) (fun i : Fin p => Fin.castAdd (n + 1) i) i

/-- The `w`-coordinate matching the `j`-th curve coordinate `φ_j`. -/
def yIdx (j : Fin n) : Fin (p + (n + 1)) := Fin.natAdd p j.succ

@[simp] theorem lIdx_castSucc (i : Fin p) : lIdx p n (Fin.castSucc i) = Fin.castAdd (n + 1) i :=
  Fin.lastCases_castSucc i

@[simp] theorem lIdx_last : lIdx p n (Fin.last p) = Fin.natAdd p 0 := Fin.lastCases_last

/-- The substitution selecting `(x_i, w_i)`: the diagonal relation `w_i = x_i`. -/
def kIdx (i : Fin (p + 1)) : Fin 2 → Fin ((p + 1 + 1) + (p + (n + 1))) :=
  Fin.cons (aIdx p n i) (fun _ => wIdx p n (lIdx p n i))

/-- The substitution selecting `(x, w_{p+1+j})`: the relation `w_{p+1+j} = φ_j x`. -/
def gIdx (j : Fin n) : Fin (p + 1 + 1) → Fin ((p + 1 + 1) + (p + (n + 1))) :=
  Fin.snoc (fun i : Fin (p + 1) => aIdx p n i) (wIdx p n (yIdx p n j))

/-- The substitution selecting `(v, w)`: the transport of the branch set. -/
def hIdx : Fin (p + (n + 1) + 1) → Fin ((p + 1 + 1) + (p + (n + 1))) :=
  Fin.snoc (fun k : Fin (p + (n + 1)) => wIdx p n k) (vIdx p n)

@[simp] theorem kIdx_zero (i : Fin (p + 1)) : kIdx p n i 0 = aIdx p n i := by
  simp [kIdx]

@[simp] theorem kIdx_one (i : Fin (p + 1)) :
    kIdx p n i 1 = wIdx p n (lIdx p n i) := by
  simp [kIdx]

@[simp] theorem hIdx_castSucc (k : Fin (p + (n + 1))) :
    hIdx p n (Fin.castSucc k) = wIdx p n k := by
  simp [hIdx]

@[simp] theorem hIdx_last : hIdx p n (Fin.last (p + (n + 1))) = vIdx p n := by
  simp [hIdx]

@[simp] theorem gIdx_castSucc (j : Fin n) (i : Fin (p + 1)) :
    gIdx p n j (Fin.castSucc i) = aIdx p n i := by
  simp [gIdx]

@[simp] theorem gIdx_last (j : Fin n) :
    gIdx p n j (Fin.last (p + 1)) = wIdx p n (yIdx p n j) := by
  simp [gIdx]

/-! ## 2. The sets -/

/-- The `p+1` diagonal relations `w_i = x_i`. -/
def diagSet : Set (Fin ((p + 1 + 1) + (p + (n + 1))) → ℝ) :=
  ⋂ i : Fin (p + 1), Work.WilG5.coordPre (kIdx p n i) {v : Fin 2 → ℝ | v 0 = v 1}

/-- The `n` relations `w_{p+1+j} = φ_j x`. -/
def gamSet (φ : (Fin (p + 1) → ℝ) → (Fin n → ℝ)) :
    Set (Fin ((p + 1 + 1) + (p + (n + 1))) → ℝ) :=
  ⋂ j : Fin n, Work.WilG5.coordPre (gIdx p n j) (graphOf (fun x : Fin (p + 1) → ℝ => φ x j))

/-- The branch set of `surrogateBranch` for `A`. -/
def chS (A : Set (Fin (p + (n + 1) + 1) → ℝ)) : Set (Fin (p + (n + 1) + 1) → ℝ) :=
  {z | (∃ t : ℝ, Fin.snoc (Fin.init z) t ∈ A ∧ z (Fin.last (p + (n + 1))) = (t + 2) / 4) ∨
    (Fin.init z ∉ projLast A ∧ z (Fin.last (p + (n + 1))) = 1 / 2)}

/-- The branch set transported to the `(v,w)`-block. -/
def chSet (A : Set (Fin (p + (n + 1) + 1) → ℝ)) :
    Set (Fin ((p + 1 + 1) + (p + (n + 1))) → ℝ) :=
  Work.WilG5.coordPre (hIdx p n) (chS p n A)

/-- The intersection of the diagonal and curve relations. -/
def grSet (φ : (Fin (p + 1) → ℝ) → (Fin n → ℝ)) :
    Set (Fin ((p + 1 + 1) + (p + (n + 1))) → ℝ) :=
  diagSet p n ∩ gamSet p n φ

/-- The full auxiliary set. -/
def uSet (A : Set (Fin (p + (n + 1) + 1) → ℝ))
    (φ : (Fin (p + 1) → ℝ) → (Fin n → ℝ)) :
    Set (Fin ((p + 1 + 1) + (p + (n + 1))) → ℝ) :=
  grSet p n φ ∩ chSet p n A

/-- The target set of the statement. -/
def tSet (A : Set (Fin (p + (n + 1) + 1) → ℝ))
    (φ : (Fin (p + 1) → ℝ) → (Fin n → ℝ)) : Set (Fin (p + 1 + 1) → ℝ) :=
  {z | (∃ t : ℝ,
        Fin.snoc (Work.WilkG4c.xPt (fun i : Fin p => (Fin.init z) (Fin.castSucc i))
          ((Fin.init z) (Fin.last p)) (φ (Fin.init z))) t ∈ A ∧
        z (Fin.last (p + 1)) = (t + 2) / 4) ∨
      (Work.WilkG4c.xPt (fun i : Fin p => (Fin.init z) (Fin.castSucc i))
          ((Fin.init z) (Fin.last p)) (φ (Fin.init z)) ∉ projLast A ∧
        z (Fin.last (p + 1)) = 1 / 2)}

/-! ## 3. Membership lemmas -/

theorem mem_diagSet {u : Fin ((p + 1 + 1) + (p + (n + 1))) → ℝ} :
    u ∈ diagSet p n ↔ ∀ i : Fin (p + 1), u (aIdx p n i) = u (wIdx p n (lIdx p n i)) := by
  simp only [diagSet, Set.mem_iInter, Work.WilG5.coordPre, Set.mem_ofPred_eq,
    Function.comp_apply, kIdx_zero, kIdx_one]

theorem comp_gIdx (j : Fin n) (u : Fin ((p + 1 + 1) + (p + (n + 1))) → ℝ) :
    u ∘ gIdx p n j =
      Fin.snoc (fun i : Fin (p + 1) => u (aIdx p n i)) (u (wIdx p n (yIdx p n j))) := by
  funext k
  refine Fin.lastCases ?_ ?_ k
  · rw [Function.comp_apply, gIdx_last, Fin.snoc_last]
  · intro i
    rw [Function.comp_apply, gIdx_castSucc, Fin.snoc_castSucc]

theorem mem_gamSet {φ : (Fin (p + 1) → ℝ) → (Fin n → ℝ)}
    {u : Fin ((p + 1 + 1) + (p + (n + 1))) → ℝ} :
    u ∈ gamSet p n φ ↔
      ∀ j : Fin n, u (wIdx p n (yIdx p n j)) =
        φ (fun i : Fin (p + 1) => u (aIdx p n i)) j := by
  simp only [gamSet, Set.mem_iInter, Work.WilG5.coordPre, Set.mem_ofPred_eq,
    Function.comp_apply]
  constructor
  · intro h j
    have hj := h j
    rw [comp_gIdx, graphOf, Set.mem_ofPred_eq, Fin.init_snoc, Fin.snoc_last] at hj
    exact hj
  · intro h j
    rw [comp_gIdx, graphOf, Set.mem_ofPred_eq, Fin.init_snoc, Fin.snoc_last]
    exact h j

/-- The graph of a member of a family of functions on `Fin (p+1)` is the set of points whose
last coordinate is the value: `graphOf` in terms of `Fin.init`. -/
theorem mem_graphOf {m : ℕ} {g : (Fin m → ℝ) → ℝ} {z : Fin (m + 1) → ℝ} :
    z ∈ graphOf g ↔ z (Fin.last m) = g (Fin.init z) := Iff.rfl

theorem comp_hIdx (u : Fin ((p + 1 + 1) + (p + (n + 1))) → ℝ) :
    u ∘ hIdx p n =
      Fin.snoc (fun k : Fin (p + (n + 1)) => u (wIdx p n k)) (u (vIdx p n)) := by
  funext k
  refine Fin.lastCases ?_ ?_ k
  · rw [Function.comp_apply, hIdx_last, Fin.snoc_last]
  · intro i
    rw [Function.comp_apply, hIdx_castSucc, Fin.snoc_castSucc]

theorem mem_chSet {A : Set (Fin (p + (n + 1) + 1) → ℝ)}
    {u : Fin ((p + 1 + 1) + (p + (n + 1))) → ℝ} :
    u ∈ chSet p n A ↔
      Fin.snoc (fun k : Fin (p + (n + 1)) => u (wIdx p n k)) (u (vIdx p n)) ∈ chS p n A := by
  rw [chSet, Work.WilG5.coordPre, Set.mem_ofPred_eq, comp_hIdx]

theorem mem_chS_snoc {A : Set (Fin (p + (n + 1) + 1) → ℝ)}
    (w : Fin (p + (n + 1)) → ℝ) (v : ℝ) :
    Fin.snoc w v ∈ chS p n A ↔
      (∃ t : ℝ, Fin.snoc w t ∈ A ∧ v = (t + 2) / 4) ∨ (w ∉ projLast A ∧ v = 1 / 2) := by
  simp only [chS, Set.mem_ofPred_eq, Fin.init_snoc, Fin.snoc_last]

/-! ## 4. Membership of `snocIt` on the index maps -/

theorem snocIt_aIdx (x : Fin (p + 1 + 1) → ℝ) (w : Fin (p + (n + 1)) → ℝ)
    (j : Fin (p + 1)) :
    Work.WilG0.snocIt (p + 1 + 1) (p + (n + 1)) x w (aIdx p n j) = (Fin.init x) j := by
  rw [aIdx, Work.WilG0.snocIt_castAdd]
  simp only [Fin.init]

theorem snocIt_vIdx (x : Fin (p + 1 + 1) → ℝ) (w : Fin (p + (n + 1)) → ℝ) :
    Work.WilG0.snocIt (p + 1 + 1) (p + (n + 1)) x w (vIdx p n) = x (Fin.last (p + 1)) := by
  rw [vIdx, Work.WilG0.snocIt_castAdd]

theorem snocIt_wIdx (x : Fin (p + 1 + 1) → ℝ) (w : Fin (p + (n + 1)) → ℝ)
    (k : Fin (p + (n + 1))) :
    Work.WilG0.snocIt (p + 1 + 1) (p + (n + 1)) x w (wIdx p n k) = w k := by
  rw [wIdx, Work.WilG0.snocIt_natAdd]

theorem sum_const_fin {k : ℕ} (c : ℕ) : (∑ _ : Fin k, c) = k * c := by
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  simp

/-! ## 5. The explicit bounds -/

/-- The ambient dimension. -/
def Dm (p n : ℕ) : ℕ := (p + 1 + 1) + (p + (n + 1))

/-- A common format bound for all the pieces. -/
def FmtB (p n F₁ F₂ Cb₁ : ℕ) : ℕ := F₁ + F₂ + Cb₁ + 1000 * (Dm p n + p + n + Cb₁ + 2)

/-- The degree of the diagonal part. -/
def DegD (p n : ℕ) : ℕ := (p + 1) * (1 + 32 * (Dm p n + 2) + 32)

/-- The degree of the curve part (with the coefficient of `D₂` exposed). -/
def DegG (p n D₂ : ℕ) : ℕ := n * (D₂ + (32 * (Dm p n + (p + 1 + 1)) + 32))

/-- The degree of the branch part (with the coefficient of `D₁` exposed). -/
def DegC (p n D₁ Cb₂ : ℕ) : ℕ := 2 * D₁ + Cb₂ + 32 * (Dm p n + (p + (n + 1) + 1)) + 32

/-- The format slack. -/
def Kfmt (p n Cb₁ : ℕ) : ℕ :=
  Cb₁ + 1000 * (Dm p n + p + n + Cb₁ + 2) + (Dm p n + p + n + 2) + 100

/-- The degree slack: the `D₂`-coefficient is exactly `n`, the `D₁`-coefficient exactly `2`. -/
def Kdeg (p n Cb₂ : ℕ) : ℕ :=
  DegD p n + n * (32 * (Dm p n + (p + 1 + 1)) + 32) + Cb₂ +
    32 * (Dm p n + (p + (n + 1) + 1)) + 32 + 100

/-! ## 6. The composition theorem -/

/-- The composition step of the surrogate: `A` (the derivative graph) contributes at format
coefficient `1` and degree coefficient `2`, each curve coordinate graph at format coefficient
`1` and degree coefficient `1` (so `n * D₂` in total). -/
theorem surrogateCompSelf (S : WilkiesDesign.SOMin) (p n : ℕ) :
    ∃ (C₁ C₂ : ℕ), ∀ (F₁ F₂ D₁ D₂ : ℕ) (A : Set (Fin (p + (n + 1) + 1) → ℝ))
      (φ : (Fin (p + 1) → ℝ) → (Fin n → ℝ)),
      A ∈ S.Ω F₁ D₁ (p + (n + 1) + 1) →
      (∀ j : Fin n, WilkiesDesign.graphOf (fun x : Fin (p + 1) → ℝ => φ x j)
        ∈ S.Ω F₂ D₂ (p + 1 + 1)) →
      {z : Fin (p + 1 + 1) → ℝ |
        (∃ t : ℝ, Fin.snoc (Work.WilkG4c.xPt (fun i : Fin p => (Fin.init z) (Fin.castSucc i))
            ((Fin.init z) (Fin.last p)) (φ (Fin.init z))) t ∈ A ∧
          z (Fin.last (p + 1)) = (t + 2) / 4) ∨
        (Work.WilkG4c.xPt (fun i : Fin p => (Fin.init z) (Fin.castSucc i))
            ((Fin.init z) (Fin.last p)) (φ (Fin.init z)) ∉ WilkiesDesign.projLast A ∧
          z (Fin.last (p + 1)) = 1 / 2)}
      ∈ S.Ω (F₁ + F₂ + C₁) (2 * D₁ + n * D₂ + C₂) (p + 1 + 1) := by
  obtain ⟨Cb₁, Cb₂, hBr⟩ := surrogateBranch S (p + (n + 1))
  refine ⟨Kfmt p n Cb₁, Kdeg p n Cb₂, ?_⟩
  intro F₁ F₂ D₁ D₂ A φ hA hφ
  -- the three pieces, at the common format `FmtB`
  have hrel : ({v : Fin 2 → ℝ | v 0 = v 1}) ∈ S.Ω 2 1 2 := by
    have h := Work.WilG1.Omega.coordEq_mem (S := S) 0 (0 : Fin 2) (1 : Fin 2)
    simpa using h
  have hdiag : ∀ i : Fin (p + 1),
      Work.WilG5.coordPre (kIdx p n i) {v : Fin 2 → ℝ | v 0 = v 1} ∈
        S.Ω (2 + 64 * (Dm p n + 2) + 64) (1 + 32 * (Dm p n + 2) + 32) (Dm p n) :=
    fun i => Work.WilG5.coordPre_mem (S := S) (ι := kIdx p n i) hrel
  have hDiag := S.inter (F := 2 + 64 * (Dm p n + 2) + 64) (n := Dm p n)
    (D := fun _ : Fin (p + 1) => 1 + 32 * (Dm p n + 2) + 32)
    (A := fun i : Fin (p + 1) =>
      Work.WilG5.coordPre (kIdx p n i) {v : Fin 2 → ℝ | v 0 = v 1}) hdiag
  rw [sum_const_fin] at hDiag
  have hDiagRet : diagSet p n ∈ S.Ω (FmtB p n F₁ F₂ Cb₁) (DegD p n) (Dm p n) :=
    Work.WilG1.Omega.mono hDiag (by dsimp only [FmtB, Dm]; omega) le_rfl
  have hgam : ∀ j : Fin n,
      Work.WilG5.coordPre (gIdx p n j) (graphOf (fun x : Fin (p + 1) → ℝ => φ x j)) ∈
        S.Ω (F₂ + 64 * (Dm p n + (p + 1 + 1)) + 64)
          (D₂ + 32 * (Dm p n + (p + 1 + 1)) + 32) (Dm p n) :=
    fun j => Work.WilG5.coordPre_mem (S := S) (ι := gIdx p n j) (hφ j)
  have hGam := S.inter (F := F₂ + 64 * (Dm p n + (p + 1 + 1)) + 64) (n := Dm p n)
    (D := fun _ : Fin n => D₂ + 32 * (Dm p n + (p + 1 + 1)) + 32)
    (A := fun j : Fin n => Work.WilG5.coordPre (gIdx p n j)
      (graphOf (fun x : Fin (p + 1) → ℝ => φ x j))) hgam
  rw [sum_const_fin] at hGam
  have hGamRet : gamSet p n φ ∈ S.Ω (FmtB p n F₁ F₂ Cb₁) (DegG p n D₂) (Dm p n) :=
    Work.WilG1.Omega.mono hGam (by dsimp only [FmtB, Dm]; omega) le_rfl
  have hChS : chS p n A ∈ S.Ω (F₁ + Cb₁) (2 * D₁ + Cb₂) (p + (n + 1) + 1) :=
    hBr F₁ D₁ A hA
  have hCh := Work.WilG5.coordPre_mem (S := S) (ι := hIdx p n) (A := chS p n A) hChS
  have hChRet : chSet p n A ∈ S.Ω (FmtB p n F₁ F₂ Cb₁) (DegC p n D₁ Cb₂) (Dm p n) :=
    Work.WilG1.Omega.mono hCh (by dsimp only [FmtB, Dm]; omega) le_rfl
  -- assemble
  have hChRet' : chSet p n A ∈ S.Ω (FmtB p n F₁ F₂ Cb₁ + 1) (DegC p n D₁ Cb₂) (Dm p n) :=
    Work.WilG1.Omega.mono hChRet (by dsimp only [FmtB, Dm]; omega) le_rfl
  have hGr := Work.WilG0.Omega_inter2 hDiagRet hGamRet
  have hU := Work.WilG0.Omega_inter2 hGr hChRet'
  have hProj := Work.WilG0.projLastIter_mem (S := S) (p + 1 + 1) (p + (n + 1))
    (FmtB p n F₁ F₂ Cb₁ + 1 + 1) (DegD p n + DegG p n D₂ + DegC p n D₁ Cb₂)
    (uSet p n A φ) hU
  -- the projected set is the target
  have hT : Work.WilG0.projLastIter (p + 1 + 1) (p + (n + 1)) (uSet p n A φ)
      = tSet p n A φ := by
    rw [Work.WilG0.projLastIter_eq]
    ext x
    constructor
    · rintro ⟨w, hw⟩
      rw [uSet, Set.mem_inter_iff, grSet, Set.mem_inter_iff] at hw
      obtain ⟨⟨hdgm, hgmm⟩, hchm⟩ := hw
      rw [mem_diagSet] at hdgm
      rw [mem_gamSet] at hgmm
      rw [mem_chSet, mem_chS_snoc] at hchm
      have hvfun : (fun k : Fin (p + (n + 1)) =>
          Work.WilG0.snocIt (p + 1 + 1) (p + (n + 1)) x w (wIdx p n k)) = w := by
        funext k
        rw [snocIt_wIdx]
      have hvval : Work.WilG0.snocIt (p + 1 + 1) (p + (n + 1)) x w (vIdx p n)
          = x (Fin.last (p + 1)) := snocIt_vIdx p n x w
      rw [hvfun, hvval] at hchm
      have hD : ∀ i : Fin (p + 1), w (lIdx p n i) = (Fin.init x) i := by
        intro i
        have h := hdgm i
        rw [snocIt_aIdx, snocIt_wIdx] at h
        exact h.symm
      have hG : ∀ j : Fin n, w (yIdx p n j) = φ (Fin.init x) j := by
        intro j
        have h := hgmm j
        rw [snocIt_wIdx] at h
        have harg : (fun i : Fin (p + 1) =>
            Work.WilG0.snocIt (p + 1 + 1) (p + (n + 1)) x w (aIdx p n i)) = Fin.init x := by
          funext i
          rw [snocIt_aIdx]
        rw [harg] at h
        exact h
      have hwW : w = Work.WilkG4c.xPt (fun i : Fin p => (Fin.init x) (Fin.castSucc i))
          ((Fin.init x) (Fin.last p)) (φ (Fin.init x)) := by
        funext κ
        refine Fin.addCases (fun i : Fin p => ?_) (fun k : Fin (n + 1) => ?_) κ
        · rw [Work.WilkG4c.xPt, Fin.append_left, ← lIdx_castSucc p n i, hD (Fin.castSucc i)]
        · refine Fin.cases ?_ ?_ k
          · rw [Work.WilkG4c.xPt, Fin.append_right, Fin.cons_zero, ← lIdx_last p n,
              hD (Fin.last p)]
          · intro j
            rw [show Fin.natAdd p (Fin.succ j) = yIdx p n j from rfl, hG j]
            simp only [Work.WilkG4c.xPt, yIdx, Fin.append_right, Fin.cons_succ]
      rw [hwW] at hchm
      simp only [tSet, Set.mem_ofPred_eq]
      exact hchm
    · intro hx
      simp only [tSet, Set.mem_ofPred_eq] at hx
      refine ⟨Work.WilkG4c.xPt (fun i : Fin p => (Fin.init x) (Fin.castSucc i))
        ((Fin.init x) (Fin.last p)) (φ (Fin.init x)), ?_⟩
      rw [uSet, Set.mem_inter_iff, grSet, Set.mem_inter_iff, mem_diagSet, mem_gamSet,
        mem_chSet, mem_chS_snoc]
      have harg : (fun i : Fin (p + 1) => Work.WilG0.snocIt (p + 1 + 1) (p + (n + 1)) x
          (Work.WilkG4c.xPt (fun i : Fin p => (Fin.init x) (Fin.castSucc i))
            ((Fin.init x) (Fin.last p)) (φ (Fin.init x))) (aIdx p n i)) = Fin.init x := by
        funext i
        rw [snocIt_aIdx]
      have hvfun : (fun k : Fin (p + (n + 1)) => Work.WilG0.snocIt (p + 1 + 1) (p + (n + 1)) x
          (Work.WilkG4c.xPt (fun i : Fin p => (Fin.init x) (Fin.castSucc i))
            ((Fin.init x) (Fin.last p)) (φ (Fin.init x))) (wIdx p n k))
          = Work.WilkG4c.xPt (fun i : Fin p => (Fin.init x) (Fin.castSucc i))
            ((Fin.init x) (Fin.last p)) (φ (Fin.init x)) := by
        funext k
        rw [snocIt_wIdx]
      have hvval : Work.WilG0.snocIt (p + 1 + 1) (p + (n + 1)) x
          (Work.WilkG4c.xPt (fun i : Fin p => (Fin.init x) (Fin.castSucc i))
            ((Fin.init x) (Fin.last p)) (φ (Fin.init x))) (vIdx p n)
          = x (Fin.last (p + 1)) := snocIt_vIdx p n x _
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · intro i
        rw [snocIt_aIdx, snocIt_wIdx]
        refine Fin.lastCases ?_ ?_ i
        · rw [lIdx_last, Work.WilkG4c.xPt, Fin.append_right, Fin.cons_zero]
        · intro i'
          rw [lIdx_castSucc, Work.WilkG4c.xPt, Fin.append_left]
      · intro j
        rw [snocIt_wIdx, harg]
        simp only [Work.WilkG4c.xPt, yIdx, Fin.append_right, Fin.cons_succ]
      · rw [hvfun, hvval]
        exact hx
  rw [hT] at hProj
  refine Work.WilG5.mem_mono hProj (F₁ + F₂ + Kfmt p n Cb₁)
    (2 * D₁ + n * D₂ + Kdeg p n Cb₂) ?_ ?_
  · dsimp only [FmtB, Kfmt, Dm]
    omega
  · have hDegG : DegG p n D₂ = n * D₂ + n * (32 * (Dm p n + (p + 1 + 1)) + 32) := by
      dsimp only [DegG]
      exact Nat.mul_add n D₂ (32 * (Dm p n + (p + 1 + 1)) + 32)
    rw [hDegG]
    dsimp only [DegD, DegC, Kdeg, Dm]
    omega

end SurComp

end Work.WilG4c
