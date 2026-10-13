import Mathlib
import Submission.Work.WilE7.Endgame.E2Aux

namespace Work.WilE7.Endgame.E2B

theorem zList (FZ : ℕ) :
    ∃ (AZ : ℕ) (BZ : Polynomial ℕ),
      ∀ {k : ℕ} (n m K D : ℕ)
        (Pie : List (Fin k × WilkiesDesign.E.Stratum 0 ((n + 1) + m)))
        (Sig : List (WilkiesDesign.E.SemiPf (n + Work.WilE7.CoreStep.pPair n m)))
        (hPie : ∀ p ∈ Pie, (p.2).X.fmt ≤ FZ ∧ (p.2).deg ≤ D)
        (hSig : ∀ S ∈ Sig, S.fmt ≤ FZ ∧ S.deg ≤ D ∧
          Work.WilE7.MainDesign.NullDimLT
            (WilkiesDesign.E.projFirst n (Work.WilE7.CoreStep.pPair n m) '' S.set) K),
        ∃ Zl : List (WilkiesDesign.E.SemiPf ((n + 1) + (m + Work.WilE7.CoreStep.pPair n m))),
          Zl.length ≤ Pie.length * Sig.length ∧
          (∀ Z ∈ Zl, Z.fmt ≤ AZ ∧
            Work.WilE7.MainDesign.NullDimLT
              (Work.WilE7.MainDesign.basePr n (m + Work.WilE7.CoreStep.pPair n m) '' Z.set) K) ∧
          ∀ p ∈ Pie, ∀ S ∈ Sig, ∃ i : Fin Zl.length,
            (Zl.get i).deg ≤ BZ.eval ((p.2).deg + S.deg) ∧
            WilkiesDesign.E.projFirst (n + 1) (m + Work.WilE7.CoreStep.pPair n m) ''
                (Zl.get i).set =
              (WilkiesDesign.E.projFirst (n + 1) m ''
                  Work.WilE7.MainDesign.absSet (p.2)) ∩
                {y : Fin (n + 1) → ℝ |
                  Fin.init y ∈
                    WilkiesDesign.E.projFirst n (Work.WilE7.CoreStep.pPair n m) '' S.set} := by
  classical
  -- The single-stratum version: one glued piece per (stratum, sigma-set) pair.
  obtain ⟨A, B, hB⟩ := Work.CoreStep.fibreProd_sigma_lem FZ
  refine ⟨A, B, ?_⟩
  intro k n m K D Pie Sig hPie hSig
  -- The list of all pairs, kept attached so that each element carries its membership.
  let L : List ((Fin k × WilkiesDesign.E.Stratum 0 ((n + 1) + m)) ×
      WilkiesDesign.E.SemiPf (n + Work.WilE7.CoreStep.pPair n m)) := Pie.product Sig
  have hmemL : ∀ q ∈ L, (q.1 ∈ Pie ∧ q.2 ∈ Sig) := by
    intro q hq
    dsimp only [L] at hq
    exact List.mem_product.mp hq
  -- The glued piece of a pair, chosen by the single-pair lemma.
  let g : {q // q ∈ L} →
      WilkiesDesign.E.SemiPf ((n + 1) + (m + Work.WilE7.CoreStep.pPair n m)) := fun q =>
    (hB n m (Work.WilE7.CoreStep.pPair n m) K q.1.1.2 q.1.2
      (hPie q.1.1 (hmemL q.1 q.2).1).1
      (hSig q.1.2 (hmemL q.1 q.2).2).1
      (hSig q.1.2 (hmemL q.1 q.2).2).2.2).choose
  have hg : ∀ q : {q // q ∈ L},
      (g q).fmt ≤ A ∧ (g q).deg ≤ B.eval (q.1.1.2.deg + q.1.2.deg) ∧
      WilkiesDesign.E.projFirst (n + 1) (m + Work.WilE7.CoreStep.pPair n m) '' (g q).set =
        (WilkiesDesign.E.projFirst (n + 1) m '' Work.WilE7.MainDesign.absSet q.1.1.2) ∩
          {y : Fin (n + 1) → ℝ | Fin.init y ∈
            WilkiesDesign.E.projFirst n (Work.WilE7.CoreStep.pPair n m) '' q.1.2.set} ∧
      Work.WilE7.MainDesign.NullDimLT
        (Work.WilE7.MainDesign.basePr n (m + Work.WilE7.CoreStep.pPair n m) '' (g q).set) K := by
    intro q
    exact (hB n m (Work.WilE7.CoreStep.pPair n m) K q.1.1.2 q.1.2
      (hPie q.1.1 (hmemL q.1 q.2).1).1
      (hSig q.1.2 (hmemL q.1 q.2).2).1
      (hSig q.1.2 (hmemL q.1 q.2).2).2.2).choose_spec
  refine ⟨L.attach.map g, ?_, ?_, ?_⟩
  · have hlen : (L.attach.map g).length = Pie.length * Sig.length := by
      rw [List.length_map, List.length_attach]
      dsimp only [L]
      exact List.length_product Pie Sig
    rw [hlen]
  · intro Z hZ
    rw [List.mem_map] at hZ
    obtain ⟨q, -, rfl⟩ := hZ
    exact ⟨(hg q).1, (hg q).2.2.2⟩
  · intro p hp S hS
    have hpq : (p, S) ∈ L := by
      dsimp only [L]
      exact List.mem_product.mpr ⟨hp, hS⟩
    have hmem : (⟨(p, S), hpq⟩ : {q // q ∈ L}) ∈ L.attach := List.mem_attach L _
    have hmap : g ⟨(p, S), hpq⟩ ∈ L.attach.map g := by
      rw [List.mem_map]
      exact ⟨_, hmem, rfl⟩
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hmap
    refine ⟨i, ?_, ?_⟩
    · rw [hi]
      simpa using (hg ⟨(p, S), hpq⟩).2.1
    · rw [hi]
      simpa using (hg ⟨(p, S), hpq⟩).2.2.1

end Work.WilE7.Endgame.E2B
