import Mathlib
import Submission.Work.CR.Flat.Holder
import Submission.Work.NN.Core.holder_cauchy_limit
import Submission.Work.CR.Flat.Holder.holderNorm_add_le

noncomputable section

open scoped NNReal ENNReal
open Set Filter

namespace Work.NN.Core

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The `C^{k,α}` norm depends only on the values of the function on the set. -/
lemma holderNorm_eq_of_eqOn {f g : X → ℂ} {Ω : Set X} (h : EqOn f g Ω) (k : ℕ) (α : ℝ) :
    Work.CR.Flat.holderNorm k α f Ω = Work.CR.Flat.holderNorm k α g Ω := by
  have h1 : ∀ i : ℕ, Work.CR.Flat.iterDerivNorm i f Ω = Work.CR.Flat.iterDerivNorm i g Ω := by
    intro i
    refine iSup_congr fun x => iSup_congr fun hx => ?_
    rw [(h.iteratedFDerivWithin i) hx]
  have h2 : ∀ i : ℕ, Work.CR.Flat.holderSeminorm i α f Ω = Work.CR.Flat.holderSeminorm i α g Ω := by
    intro i
    refine iSup_congr fun x => iSup_congr fun hx => iSup_congr fun y => iSup_congr fun hy =>
      iSup_congr fun hxy => ?_
    rw [(h.iteratedFDerivWithin i) hx, (h.iteratedFDerivWithin i) hy]
  simp only [Work.CR.Flat.holderNorm]
  exact Finset.sum_congr rfl fun i _ => by rw [h1 i, h2 i]

theorem holderNorm_le_of_tendsto {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {k : ℕ} {α : ℝ} {P : Set X} (hP : IsOpen P) {C : ℝ} (hC : 0 ≤ C) {F : ℕ → X → ℂ} {v : X → ℂ} (hF : ∀ m, ContDiffOn ℝ (k : ℕ∞) (F m) P) (hbound : ∀ m, Work.CR.Flat.holderNorm k α (F m) P ≤ ENNReal.ofReal C) (hconv : ∀ z ∈ P, Filter.Tendsto (fun m => F m z) Filter.atTop (nhds (v z))) (hcau : ∀ ε : ℝ, 0 < ε → ∃ M : ℕ, ∀ m m' : ℕ, M ≤ m → M ≤ m' → Work.CR.Flat.holderNorm k α (F m - F m') P ≤ ENNReal.ofReal ε) : Work.CR.Flat.holderNorm k α v P ≤ ENNReal.ofReal C ∧ ContDiffOn ℝ (k : ℕ∞) v P := by
  obtain ⟨G, hGcd, hGconv, hGbound⟩ :=
    Work.NN.Core.holder_cauchy_limit (X := X) (k := k) (α := α) (Ω := P) hP hF
      (fun ε hε => by
        obtain ⟨M, hM⟩ := hcau ε hε
        exact ⟨M, fun n m hn hm => hM n m hn hm⟩)
  have hEqOn : EqOn G v P := fun x hx => tendsto_nhds_unique (hGconv x hx) (hconv x hx)
  have htri : ∀ n : ℕ, Work.CR.Flat.holderNorm k α G P ≤
      Work.CR.Flat.holderNorm k α (G - F n) P + Work.CR.Flat.holderNorm k α (F n) P := by
    intro n
    have h := Work.CR.Flat.Holder.holderNorm_add_le (k := k) (α := α) (Ω := P)
      (f := G - F n) (g := F n) (hGcd.sub (hF n)) (hF n) hP.uniqueDiffOn
    rwa [show (G - F n) + F n = G from by funext x; simp] at h
  have hbnd : ∀ ε : ℝ, 0 < ε → Work.CR.Flat.holderNorm k α G P ≤ ENNReal.ofReal (C + ε) := by
    intro ε hε
    obtain ⟨N, hN⟩ := hGbound ε hε
    calc Work.CR.Flat.holderNorm k α G P
        ≤ Work.CR.Flat.holderNorm k α (G - F N) P + Work.CR.Flat.holderNorm k α (F N) P :=
          htri N
      _ ≤ ENNReal.ofReal ε + ENNReal.ofReal C := add_le_add (hN N le_rfl) (hbound N)
      _ = ENNReal.ofReal C + ENNReal.ofReal ε := add_comm _ _
      _ = ENNReal.ofReal (C + ε) := (ENNReal.ofReal_add hC hε.le).symm
  have htop : Work.CR.Flat.holderNorm k α G P ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hbnd 1 one_pos)
  have hreal : (Work.CR.Flat.holderNorm k α G P).toReal ≤ C := by
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have h := hbnd ε hε
    have h2 := ENNReal.toReal_mono (b := ENNReal.ofReal (C + ε)) ENNReal.ofReal_ne_top h
    rwa [ENNReal.toReal_ofReal (by linarith : (0 : ℝ) ≤ C + ε)] at h2
  have hGle : Work.CR.Flat.holderNorm k α G P ≤ ENNReal.ofReal C := by
    calc Work.CR.Flat.holderNorm k α G P
        = ENNReal.ofReal (Work.CR.Flat.holderNorm k α G P).toReal :=
          (ENNReal.ofReal_toReal htop).symm
      _ ≤ ENNReal.ofReal C := ENNReal.ofReal_le_ofReal hreal
  refine ⟨?_, ?_⟩
  · rw [holderNorm_eq_of_eqOn hEqOn.symm k α]
    exact hGle
  · exact hGcd.congr fun x hx => (hEqOn hx).symm

end Work.NN.Core
