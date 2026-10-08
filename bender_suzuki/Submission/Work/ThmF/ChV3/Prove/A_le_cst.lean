import Mathlib
import Submission.Work.ThmF.ChV3.Step16Defs
import Submission.Work.ThmF.ChV3.Chain17
import Submission.Work.ThmF.Prove.centDLowerCentralizerS

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ThmF.ChV3.Prove

open Work.ThmF.ChV3

/-- If `x` centralises `s` and `t` separately, it centralises `s * t`. -/
theorem centralizer_mul_le_centralizer {G : Type} [Group G] (s t : G) :
    Subgroup.centralizer ({s} : Set G) ⊓ Subgroup.centralizer ({t} : Set G) ≤
      Subgroup.centralizer ({s * t} : Set G) := by
  intro x hx
  obtain ⟨hxs, hxt⟩ := Subgroup.mem_inf.mp hx
  rw [Subgroup.mem_centralizer_singleton_iff] at hxs hxt ⊢
  rw [← mul_assoc, hxs, mul_assoc, hxt, mul_assoc]

theorem A_le_cst {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s r : G} {P : Subgroup G}
    (c : Work.ThmF.ChV3.CtxF H Q t s r P) :
    Work.ThmF.ChV3.Asub H P s t ≤ Work.ThmF.ChV3.Cst s t := by
  -- `C_D(t) ≤ C_G(s)`, by Peterfalvi II Ch. V §2 Lemma 3 a) (`centDLowerCentralizerS`).
  have hVs : Submission.Blueprint.centD H t ≤ Subgroup.centralizer ({s} : Set G) :=
    Work.ThmF.Prove.centDLowerCentralizerS c.split c.s_mem c.s_inv c.r_mem c.sid
  -- `C_D(t) ≤ C_G(t)`, by definition of `centD`.
  have hVt : Submission.Blueprint.centD H t ≤ Subgroup.centralizer ({t} : Set G) :=
    fun _ hx => (Subgroup.mem_inf.mp hx).2
  -- hence `V ≤ C_G(st)`.
  have hV : Submission.Blueprint.centD H t ≤ Work.ThmF.ChV3.Cst s t :=
    (le_inf hVs hVt).trans (centralizer_mul_le_centralizer s t)
  rw [Work.ThmF.ChV3.Asub]
  refine sup_le (sup_le ?_ ?_) ?_
  · -- `Z₁ = ⟨st⟩ ≤ C_G(st)`
    exact Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr rfl)
  · -- `P ≤ V ≤ C_G(st)` (`F1`-reduction, `CtxF.P_le`)
    exact c.P_le.trans hV
  · -- `Σ = C_W(P) ≤ W ≤ V ≤ C_G(st)`
    exact ((inf_le_left : Work.ThmF.ChV3.Sig H t P ≤ Work.ThmF.W H t).trans
      (Work.ThmF.W_le_centD H t)).trans hV

end Work.ThmF.ChV3.Prove
