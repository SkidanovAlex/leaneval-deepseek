/-
  Subproject WilE9G — the first two assembly steps of `EffStratAE_of_frozen`.

  * `exists_strata_normalized` : the ambient (`p = 0`) instance of the frozen `E5_strat`, with
    every stratum's disjunct list collapsed (G4a / FIX-3), so that the format, the degree AND the
    number of disjuncts of each stratum are bounded.  This is the list of ambient strata on which
    the whole construction runs.

  * `exists_null_of_strata` : the union of the base-critical values of a *list* of ambient `Good`
    strata is null, given the per-stratum Sard statement (G1,
    `Submission.Work.WilE9G.Sard.exists_null_of_Good`).  This is the null set `N₁` of the route.
-/
import Submission.Work.WilE9G.Collapse
import Submission.Work.WilE9G.Amb

set_option autoImplicit false
noncomputable section
open Classical Topology Filter MeasureTheory
namespace Work.WilE9G
open WilkiesDesign WilkiesDesign.E Work.WilE9.Sharp

/-! ## 1. G4a applied to `E5_strat`: a normalised list of ambient strata -/

/-- **The ambient instance of the frozen `E5_strat`, normalised.**  From the frozen
`E5_strat` (assumed as a hypothesis in the form in which it is used, at `p = 0`) one gets, for
every ambient dimension `Q` and every `X : SemiPf Q` of format `≤ F`, a list of `Good` ambient
strata exactly covering `X.set`, with a *uniform* format bound `a`, and with each stratum's
degree *and* number of disjuncts bounded by `b X.deg` — this is FIX-3 of the design review: the
number of disjuncts of a `SemiPf` set is not bounded by its degree unless empty disjuncts are
collapsed, which `stratum_normalize` does (`Collapse.lean`). -/
theorem exists_strata_normalized
    (hE5 : ∀ F : ℕ, ∃ (a : ℕ) (b : Polynomial ℕ), ∀ (p q : ℕ) (X : SemiPf (p + q)),
      X.fmt ≤ F →
      ∃ L : List (Stratum p q), L.length ≤ b.eval X.deg ∧
        (∀ S ∈ L, S.X.fmt ≤ a ∧ S.deg ≤ b.eval X.deg ∧ S.Good) ∧
        X.set = (⋃ S ∈ L, S.X.set) ∧ L.Pairwise (fun S T => Disjoint S.X.set T.X.set)) :
    ∀ F : ℕ, ∃ (a : ℕ) (b : Polynomial ℕ), ∀ (Q : ℕ) (X : SemiPf (0 + Q)), X.fmt ≤ F →
      ∃ L : List (Stratum 0 Q),
        L.length ≤ b.eval X.deg ∧
        (∀ S ∈ L, S.X.fmt ≤ a ∧ S.deg ≤ b.eval X.deg ∧
          S.X.basics.length ≤ b.eval X.deg ∧ S.Good) ∧
        X.set = (⋃ S ∈ L, S.X.set) := by
  intro F
  obtain ⟨a₀, b₀, hb₀⟩ := hE5 F
  refine ⟨a₀, b₀ + 1, fun Q X hX => ?_⟩
  obtain ⟨L, hlen, hgood, hunion, _⟩ := hb₀ 0 Q X hX
  refine ⟨L.map stratum_normalize, ?_, ?_, ?_⟩
  · rw [List.length_map]
    refine le_trans hlen ?_
    rw [Polynomial.eval_add, Polynomial.eval_one]
    exact Nat.le_succ _
  · intro S hS
    obtain ⟨S₀, hS₀, rfl⟩ := List.mem_map.mp hS
    obtain ⟨hfmt, hdeg, hgood'⟩ := hgood S₀ hS₀
    have hev : (b₀ + 1).eval X.deg = b₀.eval X.deg + 1 := by
      rw [Polynomial.eval_add, Polynomial.eval_one]
    refine ⟨?_, ?_, ?_, stratum_normalize_good hgood'⟩
    · rw [stratum_normalize_fmt]; exact hfmt
    · rw [hev]
      exact le_trans (stratum_normalize_deg_le S₀) (le_trans hdeg (Nat.le_succ _))
    · rw [hev]
      refine le_trans (stratum_normalize_basics_length_le S₀) (max_le ?_ ?_)
      · omega
      · have : S₀.X.deg ≤ b₀.eval X.deg := le_trans (Nat.le_add_right _ _) hdeg
        omega
  · rw [hunion]
    ext z
    simp only [Set.mem_iUnion, List.mem_map]
    constructor
    · rintro ⟨S, hS, hz⟩
      exact ⟨stratum_normalize S, ⟨S, hS, rfl⟩, by rwa [stratum_normalize_set]⟩
    · rintro ⟨S, ⟨S₀, hS₀, rfl⟩, hz⟩
      exact ⟨S₀, hS₀, by rwa [stratum_normalize_set] at hz⟩

/-! ## 2. The null set `N₁` of the base-critical values -/

/-- **G1 for a list of ambient strata.**  The union of the base-critical values of the strata of
a list is null, given the per-stratum Sard input `hSard` (which is
`Submission.Work.WilE9G.Sard.exists_null_of_Good`). -/
theorem exists_null_of_strata {Q n : ℕ} (hn : n ≤ Q)
    (hSard : ∀ S : Stratum 0 Q, S.Good → ∃ N₁ : Set (Fin n → ℝ),
      volume N₁ = 0 ∧
      ∀ z ∈ S.X.set, ¬ Work.WilE9G.Stratum.IsBaseSubmersiveAt S hn z → projBase0 hn z ∈ N₁)
    (L : List (Stratum 0 Q)) (hL : ∀ S ∈ L, S.Good) :
    ∃ N₁ : Set (Fin n → ℝ), volume N₁ = 0 ∧
      ∀ S ∈ L, ∀ z ∈ S.X.set, ¬ Work.WilE9G.Stratum.IsBaseSubmersiveAt S hn z → projBase0 hn z ∈ N₁ := by
  classical
  refine ⟨⋃ i : Fin L.length, (hSard (L.get i) (hL _ (List.get_mem L i))).choose, ?_, ?_⟩
  · exact measure_iUnion_null fun i =>
      (hSard (L.get i) (hL _ (List.get_mem L i))).choose_spec.1
  · intro S hS z hz hnot
    obtain ⟨i, hi, hget⟩ := List.exists_mem_iff_getElem.mp (show ∃ T ∈ L, T = S from ⟨S, hS, rfl⟩)
    refine Set.mem_iUnion.mpr ⟨⟨i, hi⟩, ?_⟩
    rw [← hget] at hz hnot
    exact (hSard (L.get ⟨i, hi⟩) (hL _ (List.get_mem L ⟨i, hi⟩))).choose_spec.2 z hz hnot

end Work.WilE9G
