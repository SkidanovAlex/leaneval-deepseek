import Mathlib
import Submission.Work.WilE9G.Reduce
import Submission.Work.WilE9G.Amb.stratum_zero_to_amb
import Submission.Work.WilE9G.Assembly.ambOf
import Submission.Work.WilE9G.Assembly.ambOf_api
import Submission.Work.WilE9G.Assembly.reindex_castEquiv_symm

set_option autoImplicit false
open WilkiesDesign WilkiesDesign.E Work.WilE9G

namespace Work.WilE9G.Assembly

/-- Membership in the ambient stratum `ambOf S` in terms of the frozen stratum `S`: a point `z`
of `ℝ^N` lies in `(ambOf S).X.set` exactly when its reindexing along the coordinate relabelling
`Amb.castEquiv N : Fin (0+N) ≃ Fin N` lies in `S.X.set`. -/
theorem mem_ambOf_iff {N : ℕ} (S : Stratum 0 N) (z : Fin N → ℝ) :
    z ∈ (ambOf S).X.set ↔
      (fun i : Fin (0 + N) => z (Work.WilE9G.Amb.castEquiv N i)) ∈ S.X.set := by
  rw [(ambOf_api S).1, Set.mem_ofPred_eq]

theorem exists_ambStrata
    (hE5 : ∀ F : ℕ, ∃ (a : ℕ) (b : Polynomial ℕ), ∀ (p q : ℕ) (X : WilkiesDesign.E.SemiPf (p + q)),
      X.fmt ≤ F →
      ∃ L : List (WilkiesDesign.E.Stratum p q), L.length ≤ b.eval X.deg ∧
        (∀ S ∈ L, S.X.fmt ≤ a ∧ S.deg ≤ b.eval X.deg ∧ S.Good) ∧
        X.set = (⋃ S ∈ L, S.X.set) ∧ L.Pairwise (fun S T => Disjoint S.X.set T.X.set)) :
    ∀ F : ℕ, ∃ (a : ℕ) (b : Polynomial ℕ), ∀ (N : ℕ) (X : WilkiesDesign.E.SemiPf N), X.fmt ≤ F →
      ∃ L : List (Work.WilE9G.AmbStratum N),
        L.length ≤ b.eval X.deg ∧
        (∀ S ∈ L, S.X.fmt ≤ a ∧ S.deg ≤ b.eval X.deg ∧
          S.X.basics.length ≤ b.eval X.deg ∧ S.Good) ∧
        X.set = (⋃ S ∈ L, S.X.set) := by
  intro F
  obtain ⟨a, b, hb⟩ := Work.WilE9G.exists_strata_normalized hE5 F
  refine ⟨a, b, fun N X hX => ?_⟩
  -- Transport `X` to `ℝ^{0+N}`, the ambient space in which the frozen strata live.
  let X' : SemiPf (0 + N) := Work.WilE7.SemiPf.reindex (Work.WilE9G.Amb.castEquiv N).symm X
  have hX'mem : ∀ z : Fin N → ℝ,
      (fun i : Fin (0 + N) => z (Work.WilE9G.Amb.castEquiv N i)) ∈ X'.set ↔ z ∈ X.set :=
    (reindex_castEquiv_symm X).1
  have hX'fmt : X'.fmt = X.fmt := (reindex_castEquiv_symm X).2.1
  have hX'deg : X'.deg = X.deg := (reindex_castEquiv_symm X).2.2.1
  have hX'len : X'.basics.length = X.basics.length := (reindex_castEquiv_symm X).2.2.2
  have hfmt' : X'.fmt ≤ F := by rw [hX'fmt]; exact hX
  -- The normalised ambient stratification of `X'` by frozen strata, transported to `AmbStratum N`.
  obtain ⟨L, hlen, hgood, hunion⟩ := hb N X' hfmt'
  refine ⟨L.map ambOf, ?_, ?_, ?_⟩
  · rw [List.length_map]
    rw [← hX'deg]
    exact hlen
  · intro T hT
    obtain ⟨S, hS, rfl⟩ := List.mem_map.mp hT
    obtain ⟨hSfmt, hSdeg, hSlen, hSgood⟩ := hgood S hS
    obtain ⟨hset, hgood', hdeg, hfmt, hlen_b⟩ := ambOf_api S
    exact ⟨by rw [hfmt]; exact hSfmt,
      by rw [hdeg, ← hX'deg]; exact hSdeg,
      by rw [hlen_b, ← hX'deg]; exact hSlen,
      hgood' hSgood⟩
  · ext z
    constructor
    · intro hz
      have h1 : (fun i : Fin (0 + N) => z (Work.WilE9G.Amb.castEquiv N i)) ∈ X'.set :=
        (hX'mem z).mpr hz
      rw [hunion] at h1
      simp only [Set.mem_iUnion] at h1
      obtain ⟨S, hS, hw⟩ := h1
      refine Set.mem_iUnion.mpr ⟨ambOf S, Set.mem_iUnion.mpr ⟨?_, ?_⟩⟩
      · exact List.mem_map.mpr ⟨S, hS, rfl⟩
      · exact (mem_ambOf_iff S z).mpr hw
    · intro hz
      simp only [Set.mem_iUnion] at hz
      obtain ⟨T, hT, hzT⟩ := hz
      obtain ⟨S₀, hS₀, rfl⟩ := List.mem_map.mp hT
      have hw : (fun i : Fin (0 + N) => z (Work.WilE9G.Amb.castEquiv N i)) ∈ S₀.X.set :=
        (mem_ambOf_iff S₀ z).mp hzT
      have h2 : (fun i : Fin (0 + N) => z (Work.WilE9G.Amb.castEquiv N i)) ∈ X'.set := by
        rw [hunion]
        exact Set.mem_iUnion.mpr ⟨S₀, Set.mem_iUnion.mpr ⟨hS₀, hw⟩⟩
      exact (hX'mem z).mp h2

end Work.WilE9G.Assembly
