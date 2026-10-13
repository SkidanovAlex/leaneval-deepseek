/-
  WilE9 — the final assembly: **BNZ §3 (E9)**, `genSOMin.SharpDeriv`.

  `Work.WilE9.E9_sharpDeriv_proved` proves the frozen hole `WilkiesDesign.E.E9_sharpDeriv`,
  taking the other areas' frozen holes as leading hypotheses:

  * `E2_components` and `E5_strat`, which subproject `WilE9G` turns into the geometric input
    `Work.WilE9G.EffStratAE` (`Work.WilE9G.EffStratAE_of_frozen`);
  * `E8_reduce` (`Gen ≤ StarR`).

  The core of the proof, `Work.WilE9.E9_sharpDeriv_of_EffStratAE`, takes the geometric input
  `EffStratAE` directly, so it is independent of the in-flight reduction of `WilE9G`.

  The proof uses (`Sharp/STATUS.md` §S5, `Sharp/AE/PLAN.md` §8):

  * `layer_strata` — from `E8_reduce` (`Gen ≤ StarR`), `star_exists_length_le` (a `Star`-set has a
    presentation with at most `D+1` pieces) and `EffStratAE`: for `graphOf f ∈ Gen F D (n+1)` a set
    `Z` with `graphOf f = psiV ⁻¹' Z` and a list `S` of effectively smooth strata whose
    components project into `Z` and cover `Z` off a null set, all of format `≤ a₁` and degree
    `≤ b₁.eval D`;
  * `layer_spec` — the specifications `SecSpec`, `LimSpec` and order-independence of `Eset` for
    that family, from the ψ-analysis of the extended systems (`exSemiPf_fst_gen`,
    `exSemiPf_snd_gen`, `exSemiPf_snd_contDiff_gen`, `exSemiPf_base_gen`, `glDeriv_perm`); the
    locality hypothesis `hQ` of each of those is `component_locality`, the IFT-based fact that the
    zero set of a `Good` stratum near a point of it stays in the point's component;
  * `DomSet2_eq` — the `C^k`-locus is the `DomSet2` domain;
  * `sdSet2_eq` — `sdSet f k v` is the `DomSet2`-domain condition intersected with `Eset`;
  * `DomSet2_gen` and `Eset_gen` — both factors are `Gen`-sets with polynomial degree bounds in
    `(D, k)`, and `poly_eval_compose_bound` collapses their two budgets into one polynomial `b`
    with `Gen.mono`.

  Every constant is existential and polynomial in `(D,k)` for fixed `n`; nothing is evaluated.
-/
import Mathlib
import Submission.Work.WilE9.All
import Submission.Work.WilE9.Sharp.DomSet2_gen
import Submission.Work.WilE9.Sharp.Eset_gen
import Submission.Work.WilE9.Sharp.DomSet2_eq
import Submission.Work.WilE9.Sharp.sdSet2_eq
import Submission.Work.WilE9.Sharp.layer_strata
import Submission.Work.WilE9.Sharp.layer_spec
import Submission.Work.WilE9.Sharp.poly_eval_compose_bound
import Submission.Work.WilE9.Sharp.exSemiPf_fst
import Submission.Work.WilE9.Sharp.exSemiPf_snd
import Submission.Work.WilE9.Sharp.exSemiPf_snd_contDiff
import Submission.Work.WilE9.Sharp.exSemiPf_base
import Submission.Work.WilE9.Sharp.AE.component_locality
import Submission.Work.WilE9.Sharp.AE.exStrat_mem_comp_of_mem_exComp
import Submission.Work.WilE9G.Frozen
import Submission.Work.WilE9G.EffStratAE_of_frozen
import Submission.Work.Sharp.glDeriv_perm
import Submission.Work.Sharp.star_exists_length_le

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section

namespace Work.WilE9

open WilkiesDesign WilkiesDesign.E

/-- **E9: sharp derivatives (BNZ §3)**, from the geometric input `EffStratAE` of subproject
`WilE9G` and the frozen `E8_reduce`.  For every `F` and `n` there are `a` and `b` such that for
every `D` and every `f` whose graph is a `Gen`-set of format `F` and degree `D`, the graph of
every partial derivative of `f` of order `k` is a `Gen`-set of format `a` and degree
`b.eval ![D,k]`. -/
theorem E9_sharpDeriv_of_EffStratAE
    (hE2 : ∀ F : ℕ, ∃ p : Polynomial ℕ, ∀ (k : ℕ) (X : WilkiesDesign.E.SemiPf k),
      X.fmt ≤ F →
      ∃ s : Finset (Fin k → ℝ), s.card ≤ p.eval X.deg ∧ ↑s ⊆ X.set ∧
        ∀ x ∈ X.set, ∃ y ∈ s,
          connectedComponentIn X.set x = connectedComponentIn X.set y)
    (hEff : Work.WilE9G.EffStratAE)
    (hE8 : ∀ F n : ℕ, ∃ (a : ℕ) (p : Polynomial ℕ), p.eval 0 = 0 ∧
      ∀ (D : ℕ) (X : Set (Fin n → ℝ)), WilkiesDesign.E.Gen F D n X →
        WilkiesDesign.E.StarR a (p.eval D) n X) :
    WilkiesDesign.E.genSOMin.SharpDeriv := by
  refine Work.WilE9.sharpDerivGen_iff.mpr ?_
  intro F n
  obtain ⟨a₁, b₁, hlayer⟩ :=
    Work.WilE9.Sharp.layer_strata hE8 (fun h => Work.Sharp.star_exists_length_le h) hEff F n
  obtain ⟨aD, bD, hDomGen⟩ := Work.WilE9.Sharp.DomSet2_gen hE2 n a₁ F
  obtain ⟨aE, bE, hEsetGen⟩ := Work.WilE9.Sharp.Eset_gen hE2 n a₁
  obtain ⟨b, hb⟩ := Work.WilE9.Sharp.poly_eval_compose_bound bD bE Polynomial.X b₁ a₁
  have hb' : ∀ D k : ℕ,
      MvPolynomial.eval ![D, b₁.eval D, k, a₁] bD +
        MvPolynomial.eval ![b₁.eval D, k, a₁] bE ≤ MvPolynomial.eval ![D, k] b := by
    intro D k
    simpa only [Polynomial.eval_X] using hb D k
  refine ⟨max (aD + 1) aE + 1, b, ?_⟩
  intro D f hgr k v
  obtain ⟨Z, S, hZS, hSlen, hSdata, hN, hNvol, hcov⟩ := hlayer D f hgr
  have hGood : ∀ A ∈ S, A.E.Good := fun A hA => (hSdata A hA).2.2.2.1
  have hfmtS : ∀ A ∈ S, A.E.X.fmt ≤ a₁ := fun A hA => (hSdata A hA).1
  have hdegS : ∀ A ∈ S, A.E.deg ≤ b₁.eval D := fun A hA => (hSdata A hA).2.1
  have hblS : ∀ A ∈ S, A.E.X.basics.length ≤ b₁.eval D + 1 :=
    fun A hA => (hSdata A hA).2.2.1
  have hπS : ∀ A ∈ S, ∀ w ∈ A.comp, Work.WilE9.Sharp.stratProj w ∈ Z :=
    fun A hA => (hSdata A hA).2.2.2.2.2
  have hlenS : S.length ≤ b₁.eval D + 1 := by omega
  -- the IFT-based locality of the zero set of a `Good` stratum
  have hQ : ∀ A ∈ S, ∀ z ∈ A.comp, ∀ᶠ z' in nhds z,
      (∀ a, eaEval A.E.X.c (A.E.h a) z' = 0) → z' ∈ A.comp := by
    intro A hA z hz
    have hzX : z ∈ A.E.X.set := connectedComponentIn_subset A.E.X.set A.q hz
    have hloc := Work.WilE9.Sharp.AE.component_locality A.E (hGood A hA) z hzX
    have heq : connectedComponentIn A.E.X.set z = A.comp := (connectedComponentIn_eq hz).symm
    filter_upwards [hloc] with z' hz'
    rwa [heq] at hz'
  obtain ⟨hspec, hperm⟩ := Work.WilE9.Sharp.layer_spec (S := S) hZS hGood hπS ⟨hN, hNvol, hcov⟩
    (fun A hA L y σ hex => by
      obtain ⟨z, hz, hzout⟩ := hex
      exact (Work.WilE9.Sharp.exSemiPf_base_gen hZS A.E A.comp (hπS A hA) L y σ
        ⟨z, Work.WilE9.Sharp.AE.exComp_subset_set A.E A.q L hz, hzout,
          Work.WilE9.Sharp.AE.exStrat_mem_comp_of_mem_exComp A.E A.q L hz⟩).2)
    (fun A hA L x w hw hbase => by
      obtain ⟨z, hz, hzout, hzQ⟩ :=
        Work.WilE9.Sharp.exSemiPf_fst_gen hZS A.E (hGood A hA) A.comp (hQ A hA) (hπS A hA)
          L x w (connectedComponentIn_subset A.E.X.set A.q hw) hw hbase
      exact ⟨z, Work.WilE9.Sharp.mem_exComp_of_mem_set A.E A.q L hz hzQ, hzout⟩)
    (fun A hA L y σ hex => by
      obtain ⟨z, hz, hzout⟩ := hex
      exact Work.WilE9.Sharp.exSemiPf_snd_gen hZS A.E (hGood A hA) A.comp (hQ A hA) (hπS A hA)
        L y σ ⟨z, Work.WilE9.Sharp.AE.exComp_subset_set A.E A.q L hz, hzout,
          Work.WilE9.Sharp.AE.exStrat_mem_comp_of_mem_exComp A.E A.q L hz⟩)
    (fun A hA L y σ hex => by
      obtain ⟨z, hz, hzout⟩ := hex
      exact Work.WilE9.Sharp.exSemiPf_snd_contDiff_gen hZS A.E (hGood A hA) A.comp (hQ A hA)
        (hπS A hA) L y σ ⟨z, Work.WilE9.Sharp.AE.exComp_subset_set A.E A.q L hz, hzout,
          Work.WilE9.Sharp.AE.exStrat_mem_comp_of_mem_exComp A.E A.q L hz⟩)
    (fun y hy L L' hp => Work.Sharp.glDeriv_perm hy hp)
  have hsec : Work.WilE9.Sharp.SecSpec n k S f := (hspec k).1
  have hlim : Work.WilE9.Sharp.LimSpec n k S f := (hspec k).2
  have hperm' : ∀ (L L' : List (Fin n)), L.length ≤ k → L'.length ≤ k → List.Perm L L' →
      Work.WilE9.Sharp.Eset n S L = Work.WilE9.Sharp.Eset n S L' :=
    fun L L' _ _ hp => hperm L L' hp
  have hDom : WilkiesDesign.E.Gen aD
      (MvPolynomial.eval ![D, b₁.eval D, k, a₁] bD) n
      (Work.WilE9.Sharp.DomSet2 n k S (WilkiesDesign.graphOf f)) :=
    hDomGen D k f S (b₁.eval D) hgr hlenS hfmtS hdegS hblS
  have hEset : WilkiesDesign.E.Gen aE
      (MvPolynomial.eval ![b₁.eval D, k, a₁] bE) (n + 1)
      (Work.WilE9.Sharp.Eset n S (List.ofFn v)) := by
    simpa only [List.length_ofFn] using
      hEsetGen (List.ofFn v) S (b₁.eval D) hlenS hfmtS hdegS hblS
  have hLift := WilkiesDesign.E.Gen.prod_right hDom
  have hInter := Work.WilE9.Gen.inter₂ hLift hEset
  rw [← Work.WilE9.Sharp.sdSet2_eq hsec hlim hperm' v] at hInter
  exact Work.WilE9.Gen.mono (le_refl _) (hb' D k) hInter

/-- **E9: sharp derivatives, unfolded form.**  This is `E9_sharpDeriv_of_EffStratAE` written for
the `Prop` `Work.WilE9.SharpDerivGen` (`Work.WilE9.All`), which is *definitionally* the same
statement but does not mention `WilkiesDesign.E.genSOMin`; it is the form to quote in axiom
audits (see `Sharp/_axchkE9.lean`: the statement `SharpDerivGen → SharpDerivGen := id` is
`sorryAx`-free, whereas any statement over `genSOMin.SharpDeriv` lists the frozen `E8_comps`
contained in `genSOMin`'s definition). -/
theorem E9_sharpDerivGen_of_EffStratAE
    (hE2 : ∀ F : ℕ, ∃ p : Polynomial ℕ, ∀ (k : ℕ) (X : WilkiesDesign.E.SemiPf k),
      X.fmt ≤ F →
      ∃ s : Finset (Fin k → ℝ), s.card ≤ p.eval X.deg ∧ ↑s ⊆ X.set ∧
        ∀ x ∈ X.set, ∃ y ∈ s,
          connectedComponentIn X.set x = connectedComponentIn X.set y)
    (hEff : Work.WilE9G.EffStratAE)
    (hE8 : ∀ F n : ℕ, ∃ (a : ℕ) (p : Polynomial ℕ), p.eval 0 = 0 ∧
      ∀ (D : ℕ) (X : Set (Fin n → ℝ)), WilkiesDesign.E.Gen F D n X →
        WilkiesDesign.E.StarR a (p.eval D) n X) :
    Work.WilE9.SharpDerivGen :=
  Work.WilE9.sharpDerivGen_iff.mp (E9_sharpDeriv_of_EffStratAE hE2 hEff hE8)

/-- **E9: sharp derivatives (BNZ §3).**  The frozen hole `WilkiesDesign.E.E9_sharpDeriv`, from the
frozen holes `E2_components` (`hE2`), `E5_strat` (`hE5`) and `E8_reduce` (`hE8`) alone: the two
former feed subproject `WilE9G`'s geometric input `EffStratAE`, which is then consumed by
`E9_sharpDeriv_of_EffStratAE`. -/
theorem E9_sharpDeriv_proved
    (hE2 : ∀ F : ℕ, ∃ p : Polynomial ℕ, ∀ (k : ℕ) (X : WilkiesDesign.E.SemiPf k),
      X.fmt ≤ F →
      ∃ s : Finset (Fin k → ℝ), s.card ≤ p.eval X.deg ∧ ↑s ⊆ X.set ∧
        ∀ x ∈ X.set, ∃ y ∈ s,
          connectedComponentIn X.set x = connectedComponentIn X.set y)
    (hE5 : ∀ F : ℕ, ∃ (a : ℕ) (b : Polynomial ℕ),
      ∀ (p q : ℕ) (X : WilkiesDesign.E.SemiPf (p + q)), X.fmt ≤ F →
      ∃ L : List (WilkiesDesign.E.Stratum p q), L.length ≤ b.eval X.deg ∧
        (∀ S ∈ L, S.X.fmt ≤ a ∧ S.deg ≤ b.eval X.deg ∧ S.Good) ∧
        X.set = (⋃ S ∈ L, S.X.set) ∧ L.Pairwise (fun S T => Disjoint S.X.set T.X.set))
    (hE8 : ∀ F n : ℕ, ∃ (a : ℕ) (p : Polynomial ℕ), p.eval 0 = 0 ∧
      ∀ (D : ℕ) (X : Set (Fin n → ℝ)), WilkiesDesign.E.Gen F D n X →
        WilkiesDesign.E.StarR a (p.eval D) n X) :
    WilkiesDesign.E.genSOMin.SharpDeriv :=
  E9_sharpDeriv_of_EffStratAE hE2 (Work.WilE9G.EffStratAE_of_frozen hE2 hE5) hE8

end Work.WilE9
