import Mathlib
import Submission.Work.ThmF.ChV3.Step16Defs
import Submission.Work.ThmF.ChV3.Chain17
import Submission.Work.ThmF.Prove.Step9Defs
import Submission.Work.ThmF.Prove.centDLowerCentralizerS
import Submission.Work.ThmF.ChV12.L5Base
import Submission.Work.ThmF.ChV3.Prove.comm_mem_of_sup_le_normalizer

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ThmF.ChV3.Prove.S2_commS_mem_R` — §3 leaf **S2**: `C_G(P)/R ≅ C_Q(P) ⋊ Σ` with `s` central

`C_G(P)` decomposes as `R · (C_Q(P) · Σ)` (`hdec`/S1) with `R` normal in `C_G(P)` (`hRn`).
Both factors of the complement commute with `s`:

* `C_Q(P) ⊆ Q` and `s ∈ Z(Q)` (Ch. V §1 Prop. 1 (c), `ChV12.prop1c`, via `Bender.DTransitiveInv`
  and `ChV12.Q_nilpotent`);
* `Σ = C_W(P) ⊆ W ≤ V = C_D(t)`, and `V ≤ C_G(s)` (Ch. V §2 Lemma 3 a),
  `Prove.centDLowerCentralizerS`).

Hence every `x ∈ C_Q(P) ⊔ Σ` satisfies `[x, s] = 1`, and the commutator form of the statement
descends from that complement to the whole of `C_G(P)` because `R` is normal there
(`Prove.comm_mem_of_sup_le_normalizer`).

`hFT` and `hpf` are part of the standing hypotheses of the chain but are not used here.
-/

set_option autoImplicit false

open LeanEval.GroupTheory.Defs

namespace Work.ThmF.ChV3.Prove

theorem S2_commS_mem_R {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s r : G} {P : Subgroup G}
    (hFT : Submission.Blueprint.FeitThompsonProp) (hC4 : Submission.Blueprint.ChIIFourProp)
    (c : Work.ThmF.ChV3.CtxF H Q t s r P) (hpf : Nat.card P = orderOf (s * t))
    {R : Subgroup G}
    (hdec : R ⊔ (Work.ThmF.ChV3.CQ Q P ⊔ Work.ThmF.ChV3.Sig H t P) = Work.ThmF.ChV3.CG P)
    (hRn : Work.ThmF.ChV3.CG P ≤ Work.ThmF.ChV3.NG R) :
    ∀ g ∈ Work.ThmF.ChV3.CG P, g * s * g⁻¹ * s⁻¹ ∈ R := by
  classical
  -- ## (1) `V = C_D(t)` centralises `s` (Ch. V §2 Lemma 3 a))
  have hVle : Submission.Blueprint.centD H t ≤ Subgroup.centralizer ({s} : Set G) :=
    Work.ThmF.Prove.centDLowerCentralizerS c.split c.s_mem c.s_inv c.r_mem c.sid
  -- ## (2) `s` centralises `P`, i.e. `s ∈ C_G(P)`
  have hsCG : s ∈ Work.ThmF.ChV3.CG P := by
    rw [Work.ThmF.ChV3.CG, Subgroup.mem_centralizer_iff]
    intro x hx
    exact Subgroup.mem_centralizer_singleton_iff.mp (hVle (c.P_le hx))
  -- ## (3) `s ∈ Z(Q)` (Ch. V §1 Prop. 1 (c))
  have hsInvH : s ∈ Submission.Blueprint.involutions (H : Set G) :=
    ⟨c.split.le c.s_mem, c.s_inv⟩
  have hcentQ : s ∈ Work.ThmF.centerOf Q :=
    Work.ThmF.ChV12.prop1c c.sit H Q t c.split
      (Work.ThmF.Bender.DTransitiveInv (t := t) c.split.stronglyEmbedded c.split.invol
        c.split.not_mem)
      (Work.ThmF.L5.Q_nilpotent c.sit hC4 c.split) s hsInvH
  have hsZQ : ∀ q ∈ Q, q * s = s * q := fun q hq =>
    ((Work.ThmF.mem_centerOf (Q := Q)).mp hcentQ).2 q hq |>.symm
  -- ## (4) the complement `C_Q(P) ⊔ Σ` centralises `s`
  have hMle : Work.ThmF.ChV3.CQ Q P ⊔ Work.ThmF.ChV3.Sig H t P ≤
      Subgroup.centralizer ({s} : Set G) := by
    refine sup_le ?_ ?_
    · intro x hx
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hsZQ x (Subgroup.mem_inf.mp hx).1
    · intro x hx
      exact hVle (Work.ThmF.W_le_centD H t (Subgroup.mem_inf.mp hx).1)
  -- ## (5) descend from the complement to `C_G(P) = R ⊔ (C_Q(P) ⊔ Σ)`
  have hN : R ⊔ (Work.ThmF.ChV3.CQ Q P ⊔ Work.ThmF.ChV3.Sig H t P) ≤
      Subgroup.normalizer (R : Set G) := by
    rw [hdec]
    exact hRn
  have hs : s ∈ R ⊔ (Work.ThmF.ChV3.CQ Q P ⊔ Work.ThmF.ChV3.Sig H t P) := by
    rw [hdec]
    exact hsCG
  have hMcomm : ∀ x ∈ (Work.ThmF.ChV3.CQ Q P ⊔ Work.ThmF.ChV3.Sig H t P),
      x * s * x⁻¹ * s⁻¹ ∈ R := by
    intro x hx
    have hxs : x * s = s * x := Subgroup.mem_centralizer_singleton_iff.mp (hMle hx)
    have h1 : x * s * x⁻¹ * s⁻¹ = 1 := by rw [hxs]; group
    rw [h1]
    exact R.one_mem
  have hkey := comm_mem_of_sup_le_normalizer hN hs hMcomm
  intro g hg
  exact hkey g (by rw [hdec]; exact hg)

end Work.ThmF.ChV3.Prove
