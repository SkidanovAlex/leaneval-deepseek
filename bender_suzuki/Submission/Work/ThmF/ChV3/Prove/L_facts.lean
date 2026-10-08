import Mathlib
import Submission.Work.ThmF.ChV3.Step16Defs
import Submission.Work.ThmF.ChV3.Chain17
import Submission.Work.ThmF.ChV12.Lemma5Defs
import Submission.Work.ThmF.ChV3.Prove.L_factsAux

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ThmF.ChV3.Prove

/-- **§3 step (15)**, the facts about `L = ⟨Q₀,K,t⟩ ∩ C_G(st)` used downstream:
`L` is cyclic of order `9`, `s` inverts it, and `st ∈ L`.

This is the source's step (15a).  `L` is the centraliser of the order-`3` element `st` in the
group `X₅ = ⟨Q₀,K,t⟩`, which Ch. V §2 Lemma 5 identifies with `PSL(2,2ⁿ)`; the model fact
`psl2_centralizer_torus` then gives that this centraliser is cyclic of order `2ⁿ + 1` and is
inverted by any involution inverting `st`.  Here `2ⁿ = |Q₀| = 2^{|P|} = 2^3 = 8` (case (10-2)
has `|P| = 3`), so `|L| = 9`, and the hypothesis `3 ∣ 2ⁿ + 1` of the model leaf is exactly
`3 ∣ |Q₀| + 1`.  The transport is packaged in `L_factsAux.centralizer_st_cyclic` (the clash-free
restatement of `ChV12.lemma5d`); the only extra inputs are `Hyp5` (built from `CtxF` and case
(10-2)'s `orderOf (s*t) = 3`) and `|Q₀| = 8`. -/
theorem L_facts {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s r : G} {P : Subgroup G}
    (hFT : Submission.Blueprint.FeitThompsonProp) (hC4 : Submission.Blueprint.ChIIFourProp)
    (c : Work.ThmF.ChV3.CtxF H Q t s r P) (h15 : Work.ThmF.ChV3.Chain15 H Q t s r P)
    (d : Work.ThmF.ChV3.Case102 H Q t s P) :
    IsCyclic ↥(Work.ThmF.ChV3.Lsub H s t) ∧ Nat.card ↥(Work.ThmF.ChV3.Lsub H s t) = 9 ∧
      (∀ x ∈ Work.ThmF.ChV3.Lsub H s t, s * x * s⁻¹ = x⁻¹) ∧
      s * t ∈ Work.ThmF.ChV3.Lsub H s t := by
  -- ## `Hyp5`: the standing hypotheses of Ch. V §2 Lemma 5
  have h5 : Work.ThmF.Lemma5.Hyp5 H Q t s :=
    { sit := c.sit, split := c.split, s_mem := c.s_mem, s_inv := c.s_inv, ord3 := d.f3 }
  -- ## `|Q₀| = 2 ^ |P| = 2 ^ 3 = 8`, so `3 ∣ |Q₀| + 1`
  have hQ0 : Nat.card ↥(Work.ThmF.Q0sub H) = 8 := by
    rw [h15.hQ0, d.p3]; norm_num
  have hq : 3 ∣ Nat.card ↥(Work.ThmF.Q0sub H) + 1 := by
    rw [hQ0]; norm_num
  -- ## the centraliser of `st` inside `X₅ = ⟨Q₀,K,t⟩` (= `L`) is cyclic of order `|Q₀| + 1 = 9`
  obtain ⟨hcyc, hcard, hinv⟩ := centralizer_st_cyclic hFT hC4 h5 hq
  -- ## `st ∈ L`
  have hsQ0 : s ∈ Work.ThmF.Q0 H := Or.inl ⟨c.split.le c.s_mem, c.s_inv⟩
  have hsX : s ∈ Work.ThmF.Lemma5.X5 H t := Work.ThmF.Lemma5.Q0_subset_X5 H t hsQ0
  have htX : t ∈ Work.ThmF.Lemma5.X5 H t := Work.ThmF.Lemma5.t_mem_X5 H t
  have hstX : s * t ∈ Work.ThmF.Lemma5.X5 H t := mul_mem hsX htX
  have hstC : s * t ∈ Work.ThmF.ChV3.Cst s t := by
    rw [Work.ThmF.ChV3.Cst, Subgroup.mem_centralizer_singleton_iff]
  exact ⟨hcyc, hcard.trans (by rw [hQ0]), hinv,
    Subgroup.mem_inf.mpr ⟨hstX, hstC⟩⟩

end Work.ThmF.ChV3.Prove
