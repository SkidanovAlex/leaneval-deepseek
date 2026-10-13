import Mathlib
import Submission.Work.WilG4a.fiber_endpoints
import Submission.Work.WilG4a.fiber_defs
import Submission.Work.WilG4a.NE1_mem
import Submission.Work.WilG4a.LB1_mem
import Submission.Work.WilG4a.UB1_mem
import Submission.Work.WilG4a.GLB1_mem
import Submission.Work.WilG4a.LUB1_mem
import Submission.Work.WilG5.Reindex3
import Submission.Work.WilG0.API

namespace Work.WilG4a

open WilkiesDesign

/-- Pointwise, the graph of `l ↦ sInf {x | (l,x) ∈ Z}` is exactly `A_lo p Z`: the
set characterised by `fiber_endpoints.mem_A_lo` (the "if the fibre is empty the
value is `0`" convention coincides with the junk value `sInf ∅ = 0` of `ℝ`).

The open-unit-interval constraint on the last coordinate of `Z` supplies the
`BddBelow` hypothesis needed for the order characterisation of `sInf`. -/
theorem graphOf_sInf_fibre_eq_A_lo (p : ℕ) (Z : Set (Fin (p + 1) → ℝ))
    (hI : ∀ z ∈ Z, z (Fin.last p) ∈ I) :
    graphOf (fun l : Fin p → ℝ => sInf {x : ℝ | Fin.snoc l x ∈ Z}) = A_lo p Z := by
  ext z
  rw [graphOf, Set.mem_ofPred_eq, mem_A_lo]
  have hbddOf : ∀ u : Fin p → ℝ, BddBelow {x : ℝ | Fin.snoc u x ∈ Z} := by
    intro u
    refine ⟨0, fun x hx => le_of_lt ?_⟩
    have h := hI (Fin.snoc u x) hx
    simp only [Fin.snoc_last] at h
    exact h.1
  by_cases hne : ∃ x : ℝ, Fin.snoc (Fin.init z) x ∈ Z
  · have hf : ({x : ℝ | Fin.snoc (Fin.init z) x ∈ Z} : Set ℝ).Nonempty := hne
    have hbd := hbddOf (Fin.init z)
    constructor
    · intro hz
      left
      refine ⟨⟨hne, ?_⟩, ?_⟩
      · intro x hx; rw [hz]; exact csInf_le hbd hx
      · intro u hu; rw [hz] at hu; exact (csInf_lt_iff hbd hf).mp hu
    · rintro (⟨⟨_, h1⟩, h2⟩ | ⟨hempty, _⟩)
      · exact (eq_sInf_iff _ hf hbd _).mp ⟨h1, h2⟩
      · exact absurd hne hempty
  · have hset : {x : ℝ | Fin.snoc (Fin.init z) x ∈ Z} = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro x hx; exact hne ⟨x, hx⟩
    constructor
    · intro hz
      right
      exact ⟨hne, by rw [hset, Real.sInf_empty] at hz; exact hz⟩
    · rintro (⟨⟨hne', _⟩, _⟩ | ⟨_, h0⟩)
      · exact absurd hne' hne
      · rw [hset, Real.sInf_empty]; exact h0

/-- Pointwise, the graph of `l ↦ sSup {x | (l,x) ∈ Z}` is exactly `A_hi p Z`
(and again `sSup ∅ = 0` matches the empty-fibre convention). -/
theorem graphOf_sSup_fibre_eq_A_hi (p : ℕ) (Z : Set (Fin (p + 1) → ℝ))
    (hI : ∀ z ∈ Z, z (Fin.last p) ∈ I) :
    graphOf (fun l : Fin p → ℝ => sSup {x : ℝ | Fin.snoc l x ∈ Z}) = A_hi p Z := by
  ext z
  rw [graphOf, Set.mem_ofPred_eq, mem_A_hi]
  have hbddOf' : ∀ u : Fin p → ℝ, BddAbove {x : ℝ | Fin.snoc u x ∈ Z} := by
    intro u
    refine ⟨1, fun x hx => le_of_lt ?_⟩
    have h := hI (Fin.snoc u x) hx
    simp only [Fin.snoc_last] at h
    exact h.2
  by_cases hne : ∃ x : ℝ, Fin.snoc (Fin.init z) x ∈ Z
  · have hf : ({x : ℝ | Fin.snoc (Fin.init z) x ∈ Z} : Set ℝ).Nonempty := hne
    have hbd := hbddOf' (Fin.init z)
    constructor
    · intro hz
      left
      refine ⟨⟨hne, ?_⟩, ?_⟩
      · intro x hx; rw [hz]; exact le_csSup hbd hx
      · intro u hu; rw [hz] at hu; exact (lt_csSup_iff hbd hf).mp hu
    · rintro (⟨⟨_, h1⟩, h2⟩ | ⟨hempty, _⟩)
      · exact (eq_sSup_iff _ hf hbd _).mp ⟨h1, h2⟩
      · exact absurd hne hempty
  · have hset : {x : ℝ | Fin.snoc (Fin.init z) x ∈ Z} = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro x hx; exact hne ⟨x, hx⟩
    constructor
    · intro hz
      right
      exact ⟨hne, by rw [hset, Real.sSup_empty] at hz; exact hz⟩
    · rintro (⟨⟨hne', _⟩, _⟩ | ⟨_, h0⟩)
      · exact absurd hne' hne
      · rw [hset, Real.sSup_empty]; exact h0

theorem sInf_sSup_fibre_graph_mem (S : WilkiesDesign.SOMin) (p F : ℕ) :
    ∃ (a c c' : ℕ),
      ∀ (D : ℕ) (Z : Set (Fin (p + 1) → ℝ)),
        Z ∈ S.Ω F D (p + 1) →
        (∀ z ∈ Z, z (Fin.last p) ∈ Work.WilG4a.I) →
        WilkiesDesign.graphOf (fun l : Fin p → ℝ => sInf {x : ℝ | Fin.snoc l x ∈ Z}) ∈
            S.Ω a (c * D + c') (p + 1) ∧
        WilkiesDesign.graphOf (fun l : Fin p → ℝ => sSup {x : ℝ | Fin.snoc l x ∈ Z}) ∈
            S.Ω a (c * D + c') (p + 1) := by
  -- the uniform constants supplied by the sibling membership lemmas
  obtain ⟨A₁, c₁, d₁, hNE⟩ := NE1_mem S p F
  obtain ⟨A₂, c₂, d₂, hLB⟩ := LB1_mem S p F
  obtain ⟨A₃, c₃, d₃, hUB⟩ := UB1_mem S p F
  obtain ⟨A₄, c₄, d₄, hGLB⟩ := GLB1_mem S p F
  obtain ⟨A₅, c₅, d₅, hLUB⟩ := LUB1_mem S p F
  -- a common (crude) format and degree bound
  set A : ℕ := A₁ + A₂ + A₃ + A₄ + A₅ + F + p + 10 with hA
  set cmax : ℕ := c₁ + c₂ + c₃ + c₄ + c₅ + 1 with hcmax
  set dmax : ℕ := d₁ + d₂ + d₃ + d₄ + d₅ + 2 with hdmax
  refine ⟨A + 6, 5 * cmax, 5 * dmax, ?_⟩
  intro D Z hZ hI
  -- the six elementary pieces, all in `Ω A (cmax*D+dmax) (p+1)`
  have hNE1 : NE1 p Z ∈ S.Ω A (cmax * D + dmax) (p + 1) :=
    Work.WilG5.mem_mono (hNE D Z hZ) A (cmax * D + dmax) (by omega)
      (deg_mono (by omega) (by omega))
  have hLB1 : LB1 p Z ∈ S.Ω A (cmax * D + dmax) (p + 1) :=
    Work.WilG5.mem_mono (hLB D Z hZ) A (cmax * D + dmax) (by omega)
      (deg_mono (by omega) (by omega))
  have hUB1 : UB1 p Z ∈ S.Ω A (cmax * D + dmax) (p + 1) :=
    Work.WilG5.mem_mono (hUB D Z hZ) A (cmax * D + dmax) (by omega)
      (deg_mono (by omega) (by omega))
  have hGLB1 : GLB1 p Z ∈ S.Ω A (cmax * D + dmax) (p + 1) :=
    Work.WilG5.mem_mono (hGLB D Z hZ) A (cmax * D + dmax) (by omega)
      (deg_mono (by omega) (by omega))
  have hLUB1 : LUB1 p Z ∈ S.Ω A (cmax * D + dmax) (p + 1) :=
    Work.WilG5.mem_mono (hLUB D Z hZ) A (cmax * D + dmax) (by omega)
      (deg_mono (by omega) (by omega))
  have hyZero : yZero1 p ∈ S.Ω A (cmax * D + dmax) (p + 1) := by
    refine Work.WilG5.mem_mono (yZero1_mem S p) A (cmax * D + dmax) (by omega) ?_
    have h2 : dmax ≤ cmax * D + dmax := Nat.le_add_left dmax (cmax * D)
    omega
  -- assembling the two graphs
  have hX2 : (NE1 p Z ∩ LB1 p Z) ∩ GLB1 p Z ∈
      S.Ω (A + 2) ((cmax * D + dmax) + (cmax * D + dmax) + (cmax * D + dmax)) (p + 1) :=
    Work.WilG0.Omega_inter2 (S := S)
      (Work.WilG0.Omega_inter2 (S := S) hNE1 hLB1)
      (Work.WilG5.mem_mono hGLB1 (A + 1) (cmax * D + dmax) (by omega) le_rfl)
  have hX4 : (NE1 p Z)ᶜ ∩ yZero1 p ∈
      S.Ω (A + 2) ((cmax * D + dmax) + (cmax * D + dmax)) (p + 1) :=
    Work.WilG0.Omega_inter2 (S := S) (S.compl hNE1)
      (Work.WilG5.mem_mono hyZero (A + 1) (cmax * D + dmax) (by omega) le_rfl)
  have hA_lo : A_lo p Z ∈ S.Ω (A + 2)
      (((cmax * D + dmax) + (cmax * D + dmax) + (cmax * D + dmax)) +
        ((cmax * D + dmax) + (cmax * D + dmax))) (p + 1) := by
    unfold A_lo
    exact Work.WilG0.Omega_union2 (S := S) hX2 hX4
  have hY2 : (NE1 p Z ∩ UB1 p Z) ∩ LUB1 p Z ∈
      S.Ω (A + 2) ((cmax * D + dmax) + (cmax * D + dmax) + (cmax * D + dmax)) (p + 1) :=
    Work.WilG0.Omega_inter2 (S := S)
      (Work.WilG0.Omega_inter2 (S := S) hNE1 hUB1)
      (Work.WilG5.mem_mono hLUB1 (A + 1) (cmax * D + dmax) (by omega) le_rfl)
  have hA_hi : A_hi p Z ∈ S.Ω (A + 2)
      (((cmax * D + dmax) + (cmax * D + dmax) + (cmax * D + dmax)) +
        ((cmax * D + dmax) + (cmax * D + dmax))) (p + 1) := by
    unfold A_hi
    exact Work.WilG0.Omega_union2 (S := S) hY2 hX4
  -- the degree is dominated by `(5*cmax)*D + 5*dmax`
  have hdeg : ((cmax * D + dmax) + (cmax * D + dmax) + (cmax * D + dmax)) +
      ((cmax * D + dmax) + (cmax * D + dmax)) ≤ 5 * cmax * D + 5 * dmax := by
    have e1 : ((cmax * D + dmax) + (cmax * D + dmax) + (cmax * D + dmax)) +
        ((cmax * D + dmax) + (cmax * D + dmax)) = 5 * (cmax * D + dmax) := by ring
    rw [e1]
    have e2 : 5 * (cmax * D + dmax) = 5 * cmax * D + 5 * dmax := by ring
    rw [e2]
  have hAlo' : A_lo p Z ∈ S.Ω (A + 6) (5 * cmax * D + 5 * dmax) (p + 1) :=
    Work.WilG5.mem_mono hA_lo (A + 6) (5 * cmax * D + 5 * dmax) (by omega) hdeg
  have hAhi' : A_hi p Z ∈ S.Ω (A + 6) (5 * cmax * D + 5 * dmax) (p + 1) :=
    Work.WilG5.mem_mono hA_hi (A + 6) (5 * cmax * D + 5 * dmax) (by omega) hdeg
  refine ⟨?_, ?_⟩
  · rw [graphOf_sInf_fibre_eq_A_lo p Z hI]; exact hAlo'
  · rw [graphOf_sSup_fibre_eq_A_hi p Z hI]; exact hAhi'

end Work.WilG4a
