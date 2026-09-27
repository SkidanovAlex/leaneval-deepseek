import Submission.Work.Whitney.PathTools.GridGeom2

/-!
# The splitting lemma with finitely supported output

Copied (verbatim) from `Submission/Work/Whitney/PathTools/janiszewski.lean`, which is currently
mid-edit and does not compile, so that the Janiszewski splitting lemma is available for import.
-/

namespace Work.Whitney.PathTools.Grid

open Set Metric Topology

noncomputable section

/-- The splitting lemma of `GridSplit`, with a finitely supported output. -/
theorem exists_chain_avoiding_union' {S₁ S₂ : Set Cell} (hS₁ : S₁.Finite)
    (hdisj : Disjoint (edgeSet S₁) (edgeSet S₂))
    (hsep : ∀ c, c ∈ starCells S₁ → c ∈ starCells S₂ → c ∈ S₁)
    {l₁ l₂ : Chain1} (hb : bdry1 ((l₁ : Chain1) : Edge → ZMod 2) = bdry1 ((l₂ : Chain1) : Edge → ZMod 2))
    (h₁ : ∀ e ∈ l₁.support, e ∉ edgeSet S₁)
    (h₂ : ∀ e ∈ l₂.support, e ∉ edgeSet S₂) :
    ∃ l₀ : Chain1, bdry1 ((l₀ : Chain1) : Edge → ZMod 2) = bdry1 ((l₁ : Chain1) : Edge → ZMod 2) ∧
      ∀ e ∈ l₀.support, e ∉ edgeSet S₁ ∧ e ∉ edgeSet S₂ := by
  classical
  set c : Chain1 := l₁ + l₂ with hc
  have hcb : bdry1 ((c : Chain1) : Edge → ZMod 2) = 0 := by
    rw [hc, Finsupp.coe_add, bdry1_add, hb, CharTwo.add_self_eq_zero]
  set w : C2 := fill c with hw
  have hwb : bdry2 w = (c : Edge → ZMod 2) := bdry2_fill c hcb
  have hcw : ∀ e, bdry2 w e = (l₁ : Edge → ZMod 2) e + (l₂ : Edge → ZMod 2) e := by
    intro e
    have := congrFun hwb e
    rw [hc, Finsupp.coe_add] at this
    simpa using this
  set T : Set Cell := starCells S₁ with hT
  have hTfin : T.Finite := hT ▸ starCells_finite hS₁
  have hfinW : (Function.support (arestrict w T)).Finite :=
    hTfin.subset (fun cc hcc => by
      by_contra hc
      rw [Function.mem_support] at hcc
      exact hcc (arestrict_zero w T cc hc))
  let W : Cell →₀ ZMod 2 := Finsupp.ofSupportFinite (arestrict w T) hfinW
  have hW : ((W : Cell → ZMod 2)) = arestrict w T := Finsupp.ofSupportFinite_coe
  have hW0 : ∀ cc ∉ T, ((W : Cell → ZMod 2)) cc = 0 := by
    intro cc hcc; rw [hW]; exact arestrict_zero w T cc hcc
  have hfinB : (Function.support (bdry2 ((W : Cell → ZMod 2)))).Finite :=
    (edgeSet_finite hTfin).subset (fun e he => by
      rw [Function.mem_support] at he
      exact support_bdry2 ((W : Cell → ZMod 2)) hW0 he)
  let B : Edge →₀ ZMod 2 := Finsupp.ofSupportFinite (bdry2 ((W : Cell → ZMod 2))) hfinB
  have hB : ((B : Edge →₀ ZMod 2) : Edge → ZMod 2) = bdry2 ((W : Cell → ZMod 2)) :=
    Finsupp.ofSupportFinite_coe
  let l₀fun : Edge → ZMod 2 := fun e => (l₂ : Edge → ZMod 2) e + bdry2 (arestrict w T) e
  have hl₀fun : ∀ e, (((l₂ + B : Chain1)) : Edge → ZMod 2) e = l₀fun e := by
    intro e
    rw [Finsupp.coe_add, Pi.add_apply, show ((B : Edge → ZMod 2)) e = bdry2 ((W : Cell → ZMod 2)) e from
      congrFun hB e, hW]
  refine ⟨l₂ + B, ?_, ?_⟩
  · have h1 : bdry1 (((l₂ + B : Chain1)) : Edge → ZMod 2)
        = bdry1 ((l₂ : Chain1) : Edge → ZMod 2) + bdry1 ((B : Chain1) : Edge → ZMod 2) := by
      rw [Finsupp.coe_add, bdry1_add]
    rw [h1, show ((B : Chain1) : Edge → ZMod 2) = bdry2 ((W : Cell → ZMod 2)) from hB,
      bdry1_bdry2, add_zero]
    exact hb.symm
  · intro e he
    have he' : l₀fun e ≠ 0 := by
      rw [← hl₀fun e]; exact Finsupp.mem_support_iff.mp he
    set w' : C2 := fun cc => w cc + arestrict w T cc with hw'def
    have hw'zero : ∀ cc ∈ T, w' cc = 0 := by
      intro cc hcc
      simp only [hw'def]
      rw [add_arestrict_mem w T hcc]
    have hsplit : ∀ e, bdry2 w' e = bdry2 w e + bdry2 (arestrict w T) e := by
      intro e
      simp only [bdry2_apply, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun cc _ => by simp [hw'def]
    have hdecomp : ∀ e, l₀fun e = bdry2 w' e + (l₁ : Edge → ZMod 2) e := by
      intro e
      rw [show l₀fun e = (l₂ : Edge → ZMod 2) e + bdry2 (arestrict w T) e from rfl, hsplit e, hcw e]
      rw [show ((l₁ : Edge → ZMod 2) e + (l₂ : Edge → ZMod 2) e + bdry2 (arestrict w T) e)
            + (l₁ : Edge → ZMod 2) e
          = (l₂ : Edge → ZMod 2) e + bdry2 (arestrict w T) e
            + ((l₁ : Edge → ZMod 2) e + (l₁ : Edge → ZMod 2) e) from by abel,
        CharTwo.add_self_eq_zero, add_zero]
    refine ⟨?_, ?_⟩
    · rw [hdecomp e] at he'
      by_cases hl₁ : (l₁ : Edge → ZMod 2) e = 0
      · have hb' : bdry2 w' e ≠ 0 := by
          intro h0; exact he' (by rw [h0, hl₁, add_zero])
        obtain ⟨cc, hcT, hce⟩ := support_bdry2 w' (S := Tᶜ)
          (fun cc hcc => hw'zero cc (by simpa using hcc)) hb'
        rintro ⟨c₁, hc₁, hc₁e⟩
        exact hcT ⟨c₁, hc₁, e, hce, hc₁e⟩
      · exact fun hc₁ => h₁ e (Finsupp.mem_support_iff.mpr hl₁) hc₁
    · by_cases hl₂ : (l₂ : Edge → ZMod 2) e = 0
      · have hb' : bdry2 (arestrict w T) e ≠ 0 := by
          intro h0
          refine he' ?_
          rw [show l₀fun e = (l₂ : Edge → ZMod 2) e + bdry2 (arestrict w T) e from rfl]
          rw [hl₂, h0, add_zero]
        obtain ⟨cc, hcT, hce⟩ := support_bdry2 (arestrict w T) (arestrict_zero w T) hb'
        rintro ⟨c₂, hc₂, hc₂e⟩
        have hcT' : cc ∈ starCells S₁ := hT ▸ hcT
        have hcS₂ : cc ∈ starCells S₂ := ⟨c₂, hc₂, e, hce, hc₂e⟩
        have hcS₁ : cc ∈ S₁ := hsep cc hcT' hcS₂
        exact (hdisj.le_bot ⟨⟨cc, hcS₁, hce⟩, ⟨c₂, hc₂, hc₂e⟩⟩).elim
      · exact fun hc₂ => h₂ e (Finsupp.mem_support_iff.mpr hl₂) hc₂
end

end Work.Whitney.PathTools.Grid
