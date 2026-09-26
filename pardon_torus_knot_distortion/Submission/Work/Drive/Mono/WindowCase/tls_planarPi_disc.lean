import Mathlib
import Submission.Work.CoreTopology.Disk
import Submission.Work.Drive.Mono.PlanarPi.Defs
import Submission.Work.Drive.Mono.PlanarPi.planarPi_pieces
import Submission.Work.Drive.Mono.exists_discParam_of_two_convex_glued
import Submission.Work.Drive.Mono.exists_discParam_of_disc_glued_convex

namespace Work.Drive.Mono.WindowCase

open Set
open scoped _root_.Topology

/-- The interior of the union of two closed sets is contained in the union of the interiors
together with the intersection. -/
private lemma interior_union_subset_of_isClosed {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsClosed A) (hB : IsClosed B) :
    interior (A ∪ B) ⊆ interior A ∪ interior B ∪ (A ∩ B) := by
  intro x hx
  have hxAB : A ∪ B ∈ 𝓝 x := mem_interior_iff_mem_nhds.mp hx
  by_cases hxB : x ∈ B
  · by_cases hxA : x ∈ A
    · exact Or.inr ⟨hxA, hxB⟩
    · refine Or.inl (Or.inr (mem_interior_iff_mem_nhds.mpr ?_))
      refine Filter.mem_of_superset (Filter.inter_mem hxAB (hA.isOpen_compl.mem_nhds hxA)) ?_
      rintro y ⟨hy, hyA⟩
      rcases hy with h | h
      · exact absurd h hyA
      · exact h
  · refine Or.inl (Or.inl (mem_interior_iff_mem_nhds.mpr ?_))
    refine Filter.mem_of_superset (Filter.inter_mem hxAB (hB.isOpen_compl.mem_nhds hxB)) ?_
    rintro y ⟨hy, hyB⟩
    rcases hy with h | h
    · exact h
    · exact absurd h hyB

/-- The planar `Π`-region over an open convex plane set is a disc. -/
theorem tls_planarPi_disc
    {a h lam : ℝ} (hh : 0 < h)
    (Q : Set (EuclideanSpace ℝ (Fin 2))) (hQc : Convex ℝ Q) (hQo : IsOpen Q)
    (hQb : Bornology.IsBounded Q)
    (p q : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ)
    (hcruxP : ∃ x ∈ Q, a + h < p x ∧ lam < q x)
    (hcruxM : ∃ x ∈ Q, p x < a - h ∧ lam < q x) :
    ∃ e : C(Metric.closedBall (0 : ℂ) 1, EuclideanSpace ℝ (Fin 2)),
      Function.Injective e ∧
      Set.range e =
        closure Q ∩ ({x | a + h ≤ p x} ∪ {x | p x ≤ a - h} ∪ {x | lam ≤ q x}) ∧
      Set.range (fun θ : ℝ => e (Work.CoreTopology.circlePoint θ)) =
        frontier (closure Q ∩ ({x | a + h ≤ p x} ∪ {x | p x ≤ a - h} ∪ {x | lam ≤ q x})) := by
  have hpieces := Work.Drive.Mono.PlanarPi.planarPi_pieces hh Q hQc hQo hQb p q hcruxP hcruxM
  obtain ⟨hBc, hBcl, hK1c, hK1cl, hK1ne, hK1int, hK2c, hK2cl, hK2ne, hK2int,
    hKwc, hKwcl, hKwne, hKwintS, hKwintQ, hdisj, hcw1, hK1wP, hK1w2, hK1wsub,
    hcw2, hK2wP, hK2w2, hK2wsub, hint1, hint2, hregion⟩ := hpieces
  set K1 := Work.Drive.Mono.PlanarPi.piCapP (closure Q) p (a + h) with hK1def
  set K2 := Work.Drive.Mono.PlanarPi.piCapM (closure Q) p (a - h) with hK2def
  set Kw := Work.Drive.Mono.PlanarPi.piWall (closure Q) p q a h lam with hKwdef
  have hK1cl' : IsClosed K1 := hK1cl.isClosed
  have hK2cl' : IsClosed K2 := hK2cl.isClosed
  have hKwcl' : IsClosed Kw := hKwcl.isClosed
  -- the two caps are disjoint
  have hnot12 : ∀ x, x ∈ K1 → x ∈ K2 → False := by
    intro x hx1 hx2
    have hmem : x ∈ K1 ∩ K2 := ⟨hx1, hx2⟩
    rw [hdisj] at hmem
    exact hmem
  -- ### Step 1: `K1 ∪ Kw` is a disc (glue two convex sets)
  have hD1 : ∃ e : C(Metric.closedBall (0 : ℂ) 1, EuclideanSpace ℝ (Fin 2)),
      Function.Injective e ∧ Set.range e = K1 ∪ Kw ∧
      Set.range (fun θ : ℝ => e (Work.CoreTopology.circlePoint θ)) = frontier (K1 ∪ Kw) := by
    refine Work.Drive.Mono.exists_discParam_of_two_convex_glued K1 Kw
      hK1c hK1cl hK1ne hKwc hKwcl hKwne ?_
    obtain ⟨x, hx, y, hy, hxy⟩ := hK1w2
    exact ⟨x, hx, y, hy, hxy⟩
  -- regularity of `K1`, `Kw` and of their union
  have hregK1 : K1 = closure (interior K1) := by
    have h1 : closure (interior K1) = closure K1 :=
      Convex.closure_interior_eq_closure_of_nonempty_interior hK1c hK1ne
    rw [h1, hK1cl'.closure_eq]
  have hregKw : Kw = closure (interior Kw) := by
    have h1 : closure (interior Kw) = closure Kw :=
      Convex.closure_interior_eq_closure_of_nonempty_interior hKwc hKwne
    rw [h1, hKwcl'.closure_eq]
  have hregU : K1 ∪ Kw = closure (interior (K1 ∪ Kw)) := by
    apply Set.Subset.antisymm
    · calc K1 ∪ Kw = closure (interior K1) ∪ closure (interior Kw) := by
            rw [← hregK1, ← hregKw]
        _ = closure (interior K1 ∪ interior Kw) := closure_union.symm
        _ ⊆ closure (interior (K1 ∪ Kw)) :=
            closure_mono (union_subset (interior_mono subset_union_left)
              (interior_mono subset_union_right))
    · calc closure (interior (K1 ∪ Kw)) ⊆ closure (K1 ∪ Kw) := closure_mono interior_subset
        _ = K1 ∪ Kw := (hK1cl'.union hKwcl').closure_eq
  -- `(K1 ∪ Kw) ∩ K2` lies in the common frontier
  have hsubUK2 : (K1 ∪ Kw) ∩ K2 ⊆ frontier (K1 ∪ Kw) ∩ frontier K2 := by
    rintro x ⟨hxu, hx2⟩
    have hxKw : x ∈ Kw := by
      rcases hxu with h | h
      · exact absurd hx2 (hnot12 x h)
      · exact h
    have hxP : p x = a - h := by simpa using hK2wP ⟨hx2, hxKw⟩
    have hxnotInt : x ∉ interior (K1 ∪ Kw) := by
      intro hxint
      have hmem := interior_union_subset_of_isClosed hK1cl' hKwcl' hxint
      rcases hmem with (hy | hy) | hy
      · have hlt : a + h < p x := by simpa using hK1int hy
        rw [hxP] at hlt
        linarith
      · have hlt : |p x - a| < h := by simpa using hKwintS hy
        rw [hxP] at hlt
        rw [show (a - h) - a = -h by ring, abs_neg, abs_of_pos hh] at hlt
        linarith
      · have hlt : p x = a + h := by simpa using hK1wP hy
        rw [hxP] at hlt
        linarith
    have hxcl : x ∈ closure (K1 ∪ Kw) := subset_closure hxu
    exact ⟨⟨hxcl, hxnotInt⟩, (hK2wsub ⟨hx2, hxKw⟩).1⟩
  -- two distinct points survive in `(K1 ∪ Kw) ∩ K2`
  have hneUK2 : ∃ x : EuclideanSpace ℝ (Fin 2), x ∈ (K1 ∪ Kw) ∩ K2 ∧
      ∃ y : EuclideanSpace ℝ (Fin 2), y ∈ (K1 ∪ Kw) ∩ K2 ∧ x ≠ y := by
    obtain ⟨x, hx, y, hy, hxy⟩ := hK2w2
    exact ⟨x, ⟨Or.inr hx.2, hx.1⟩, y, ⟨Or.inr hy.2, hy.1⟩, hxy⟩
  -- disjoint interiors
  have hinter : interior (K1 ∪ Kw) ∩ interior K2 = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro x ⟨hxu, hx2⟩
    have hmem := interior_union_subset_of_isClosed hK1cl' hKwcl' hxu
    have hxlt : p x < a - h := by simpa using hK2int hx2
    rcases hmem with (hy | hy) | hy
    · have hlt : a + h < p x := by simpa using hK1int hy
      linarith
    · have hlt : |p x - a| < h := by simpa using hKwintS hy
      have h1 : p x - a < -h := by linarith
      have h2 : h < |p x - a| := by
        rw [abs_of_neg (by linarith : p x - a < 0)]
        linarith
      linarith
    · have hlt : p x = a + h := by simpa using hK1wP hy
      linarith
  -- `(K1 ∪ Kw) ∩ K2` is convex (it is `Kw ∩ K2`), hence preconnected
  have hconnUK2 : IsPreconnected ((K1 ∪ Kw) ∩ K2) := by
    have hEq : (K1 ∪ Kw) ∩ K2 = K2 ∩ Kw := by
      ext x
      constructor
      · rintro ⟨hxu | hxu, hx2⟩
        · exact absurd hx2 (hnot12 x hxu)
        · exact ⟨hx2, hxu⟩
      · rintro ⟨hx2, hxw⟩
        exact ⟨Or.inr hxw, hx2⟩
    rw [hEq]
    exact hcw2.isPreconnected
  -- ### Step 2: glue the disc `K1 ∪ Kw` to the convex `K2`
  obtain ⟨e2, he2inj, he2range, he2front⟩ :=
    Work.Drive.Mono.exists_discParam_of_disc_glued_convex (K1 ∪ Kw) K2 hD1 hregU
      hK2c hK2cl hK2ne hsubUK2 hneUK2 hinter hconnUK2
  have hdef : closure Q ∩ ({x | a + h ≤ p x} ∪ {x | p x ≤ a - h} ∪ {x | lam ≤ q x})
      = Work.Drive.Mono.PlanarPi.piRegion (closure Q) p q a h lam := rfl
  refine ⟨e2, he2inj, ?_, ?_⟩
  · rw [hdef, he2range, hregion]
  · rw [hdef, he2front, hregion]

end Work.Drive.Mono.WindowCase
