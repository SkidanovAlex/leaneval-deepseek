import Mathlib
import Submission.Work.ATOM.ZS.Topo.Defs
import Submission.Work.ATOM.ZS.Topo.ePredFun_continuous
import Submission.Work.ATOM.ZS.Topo.betaFun_continuous
import Submission.Work.ATOM.ZS.Topo.psiFun_continuous
import Submission.Work.ATOM.ZS.Topo.phiPFun_continuous

/-!
# AREA ATOM: the continuous maps `ẽ`, `β`, `ψ`, `φ_P` as morphisms of light profinite sets

The underlying functions are defined in `Submission/Work/ATOM/ZS/Topo/Defs.lean`; their continuity
(proved in the sibling files `.../ePredFun_continuous.lean` etc.) turns them into morphisms
`(ℕ∪{∞}) × S ⟶ S`, `(ℕ∪{∞}) × S ⟶ ℕ∪{∞}` and `(ℕ∪{∞})² ⟶ ℕ∪{∞}`.
-/

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed
open OnePoint

noncomputable section

namespace Work.ATOM

variable (S : LightProfinite.{0}) [Infinite S]

/-- `ẽ : (ℕ∪{∞}) ⊗ S ⟶ S`. -/
def ePred : NS S ⟶ S :=
  ConcreteCategory.ofHom ⟨ePredFun S, ZS.Topo.ePredFun_continuous S⟩

/-- `β : (ℕ∪{∞}) ⊗ S ⟶ S` (`(j,x) ↦ e_{n(j)-1}x`, `(∞,x) ↦ x`). -/
def betaN : NS S ⟶ S :=
  ConcreteCategory.ofHom ⟨betaFun S, ZS.Topo.betaFun_continuous S⟩

/-- The second projection `(ℕ∪{∞}) ⊗ S ⟶ S`. -/
def pr₂N : NS S ⟶ S :=
  ConcreteCategory.ofHom ⟨fun p => p.2, continuous_snd⟩

/-- `ψ : (ℕ∪{∞}) ⊗ S ⟶ ℕ∪{∞}`. -/
def psiN : NS S ⟶ LightProfinite.NatUnionInfty :=
  ConcreteCategory.ofHom ⟨psiFun S, ZS.Topo.psiFun_continuous S⟩

/-- `φ_P : (ℕ∪{∞}) ⊗ (ℕ∪{∞}) ⟶ ℕ∪{∞}`. -/
def phiP : NS2 ⟶ LightProfinite.NatUnionInfty :=
  ConcreteCategory.ofHom ⟨phiPFun S, ZS.Topo.phiPFun_continuous S⟩

@[simp] lemma ePred_apply (p : ↥(NS S)) : ePred S p = ePredFun S p := rfl

@[simp] lemma betaN_apply (p : ↥(NS S)) : betaN S p = betaFun S p := rfl

@[simp] lemma pr₂N_apply (p : ↥(NS S)) : pr₂N S p = p.2 := rfl

@[simp] lemma psiN_apply (p : ↥(NS S)) : psiN S p = psiFun S p := rfl

@[simp] lemma phiP_apply (p : ↥NS2) : phiP S p = phiPFun S p := rfl

@[simp] lemma ePred_infty (x : ↥S) : ePred S (mkNS S ∞ x) = x := by
  rw [ePred_apply, ePredFun_infty]

@[simp] lemma ePred_zero (x : ↥S) : ePred S (mkNS S (((0 : ℕ) : ℕ∪{∞})) x) = (levelData S).s₀ := by
  rw [ePred_apply, ePredFun_zero]

@[simp] lemma ePred_succ (k : ℕ) (x : ↥S) :
    ePred S (mkNS S (((k + 1 : ℕ) : ℕ∪{∞})) x) = e S k x := by
  rw [ePred_apply, ePredFun_succ]

@[simp] lemma betaN_infty (x : ↥S) : betaN S (mkNS S ∞ x) = x := by
  rw [betaN_apply, betaFun_infty]

@[simp] lemma psiN_infty (x : ↥S) : psiN S (mkNS S ∞ x) = ∞ := by
  rw [psiN_apply, psiFun_infty]

/-- The defining property of `ψ`: `ψ(n(j),x) = j` whenever `e_{n(j)} x = a_j`. -/
lemma psiN_eq_of (j : ℕ) {x : ↥S} (hx : e S (lvl S j) x = (levelData S).a j) :
    psiN S (mkNS S (((lvl S j : ℕ) : ℕ∪{∞})) x) = ((j : ℕ) : ℕ∪{∞}) := by
  rw [psiN_apply]
  exact psiFun_some_eq (lvl S j) hx rfl

@[simp] lemma phiP_infty_left (q : ↥(ℕ∪{∞})) : phiP S (mkNS2 ∞ q) = ∞ := by
  rw [phiP_apply, phiPFun_infty_left]

@[simp] lemma phiP_some_infty (k : ℕ) : phiP S (mkNS2 (((k : ℕ) : ℕ∪{∞})) ∞) = ∞ := by
  rw [phiP_apply, phiPFun_some_infty]

@[simp] lemma phiP_some_some (k j : ℕ) :
    phiP S (mkNS2 (((k : ℕ) : ℕ∪{∞})) (((j : ℕ) : ℕ∪{∞}))) =
      (if k ≤ lvl S j then ((j : ℕ) : ℕ∪{∞}) else ∞) := by
  rw [phiP_apply, phiPFun_some_some]

lemma phiP_some_some_of_le {k j : ℕ} (h : k ≤ lvl S j) :
    phiP S (mkNS2 (((k : ℕ) : ℕ∪{∞})) (((j : ℕ) : ℕ∪{∞}))) = ((j : ℕ) : ℕ∪{∞}) := by
  rw [phiP_some_some, if_pos h]

lemma phiP_some_some_of_lt {k j : ℕ} (h : lvl S j < k) :
    phiP S (mkNS2 (((k : ℕ) : ℕ∪{∞})) (((j : ℕ) : ℕ∪{∞}))) = ∞ := by
  rw [phiP_some_some, if_neg (by omega)]

end Work.ATOM
