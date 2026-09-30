import Mathlib
import Submission.Work.Pi6.SQ.z4
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false

open CategoryTheory Limits AlgebraicTopology Simplicial
open scoped Simplicial
open Work.Cohomology

namespace Work.Pi6.SQ

noncomputable section

/-- **Clause (e) of `Work.Pi6.SQM.SigmaStar`** for the concrete suspension `Work.Pi6.SQM.SIG.sigma`:
`σ` preserves `ℤ/4`-liftability of `𝔽₂` cohomology classes (`Work.Pi6.SQM.Liftable4`).  Route: the
whole construction `σ = δ⁻¹ ∘ q* ∘ ρ` is available over an arbitrary commutative ring; in
particular over `R = ZMod 4` one has `σ_{ℤ/4}` (`SIG.sigma` with the coefficient ring `ZMod 4`, which
is `SIG.Basic` with `F2` replaced by `ZMod 4` — the file is `R`-generic up to that substitution), and
the coefficient reduction `ZMod.castHom (by norm_num : 2 ∣ 4) (ZMod 2)` is a map of rings `ZMod 4 →+*
ZMod 2` commuting with `cochainDiff`, with pull-backs, with `cls` and with the pair maps, so
`r ∘ σ_{ℤ/4} = σ_{𝔽₂} ∘ r`.  A `ℤ/4`-lift of `c` therefore produces a `ℤ/4`-cocycle on `ΩK` (namely
the restriction of the primitive of `q*ã` to the loop space) whose reduction represents
`σ_{𝔽₂} c`, which is exactly `Liftable4 (σ c)`.  (Equivalently: `Liftable4 c ↔ β₂ c = 0` and `σ`
commutes with the cohomology Bockstein `β₂`.) -/
theorem sigmaLift :
    ∀ (K : Type) [TopologicalSpace K] (k₀ : K) (n : ℕ) (c : Work.Pi6.Coh Work.Pi6.SQ.F2 K (n + 1)),
      Work.Pi6.SQM.Liftable4 c → Work.Pi6.SQM.Liftable4 (Work.Pi6.SQM.SIG.sigma K k₀ n c) := by
  intro K _ k₀ n c hc
  rcases n with _ | m
  · -- `σ_0 = 0`
    rw [show Work.Pi6.SQM.SIG.sigma K k₀ 0 c =
      (0 : Work.Pi6.Coh F2 (Path k₀ k₀) 0) from rfl]
    exact liftable4_zero (Path k₀ k₀) 0
  -- `n = m + 1`
  obtain ⟨Y4, hY4, y2, hy2, hcls2, hred2⟩ := hc
  -- (0) the reduction of `Y4` is `y2`
  have hred : red42 (Work.Pi6.SQM.SX K) (m + 1 + 1) Y4 = y2 := by
    apply genEval_ext
    intro σ
    rw [genEval_red42]
    exact hred2 σ
  -- (1) a `ℤ/4` relative cocycle representing `ρ (cls Y4)`
  obtain ⟨ã4, hã4, hrel4⟩ :=
    relSection4 K k₀ m (cohomologyClassOf (ZMod 4) (Work.Pi6.SQM.SX K) Y4 hY4)
  -- the underlying cochain of `ã4`, named at the degree used below
  let A : Cochain (ZMod 4) (Work.Pi6.SQM.SX K) (m + 1 + 1) := ã4.1
  have hA : cochainDiff (ZMod 4) (Work.Pi6.SQM.SX K) A = 0 := by
    have h := congrArg Subtype.val hã4
    simpa only [relDiffLM_coe, Submodule.coe_zero, singularCochain_d_apply, A] using h
  -- (2) `cls A = cls Y4` over `ℤ/4`
  have hcls4 : cohomologyClassOf (ZMod 4) (Work.Pi6.SQM.SX K) A hA =
      cohomologyClassOf (ZMod 4) (Work.Pi6.SQM.SX K) Y4 hY4 :=
    (cohomologyClassOf_congr (ZMod 4) (Work.Pi6.SQM.SX K) rfl hA
      (relClassOf_cochainDiff (ZMod 4) (TopCat.of K) ({k₀} : Set K) ã4 hã4)).trans
      ((relIncl_homologyMap_relClassOf (ZMod 4) (TopCat.of K) ({k₀} : Set K) ã4 hã4).symm.trans
        hrel4)
  -- (3) a cochain-level witness over `ℤ/4`
  obtain ⟨ζ, hζ⟩ := exists_coboundary_of_class_eq (ZMod 4) (Work.Pi6.SQM.SX K) (m + 1)
    A Y4 hA hY4 hcls4
  -- (4) reduction of the class of `A`
  have hcoc42 : cochainDiff F2 (Work.Pi6.SQM.SX K)
      (red42 (Work.Pi6.SQM.SX K) (m + 1 + 1) A) = 0 := by
    rw [← red42_cochainDiff, hA, red42_zero]
  have hdv : cochainDiff F2 (Work.Pi6.SQM.SX K) (red42 (Work.Pi6.SQM.SX K) (m + 1) ζ) =
      red42 (Work.Pi6.SQM.SX K) (m + 1 + 1) A - y2 := by
    rw [← red42_cochainDiff, hζ, red42_sub, hred]
  have hcls42 : cohomologyClassOf F2 (Work.Pi6.SQM.SX K)
      (red42 (Work.Pi6.SQM.SX K) (m + 1 + 1) A) hcoc42 = c :=
    (classEq_of_diff_coboundary' F2 (Work.Pi6.SQM.SX K) (m + 1)
      (red42 (Work.Pi6.SQM.SX K) (m + 1 + 1) A) y2 hcoc42 hy2
      (red42 (Work.Pi6.SQM.SX K) (m + 1) ζ) hdv).trans hcls2
  -- (5) the `𝔽₂` relative cocycle with underlying cochain `red42 A`
  have hz2 : ((restr F2 (TopCat.of K) ({k₀} : Set K)).f (m + 1 + 1)).hom
      (red42 (Work.Pi6.SQM.SX K) (m + 1 + 1) A) = 0 := by
    rw [restr_eq_pbG F2 (TopCat.of K) ({k₀} : Set K), ← pbG_red42,
      pbG_subtypeIncl_relKern (ZMod 4) (TopCat.of K) ({k₀} : Set K) ã4, red42_zero]
  let ã2 : relKern F2 (TopCat.of K) ({k₀} : Set K) (m + 1 + 1) :=
    ⟨red42 (Work.Pi6.SQM.SX K) (m + 1 + 1) A, hz2⟩
  have hã2 : relDiffLM F2 (TopCat.of K) ({k₀} : Set K) (m + 1 + 1) ã2 = 0 := by
    apply Subtype.ext
    rw [relDiffLM_coe, Submodule.coe_zero, singularCochain_d_apply]
    show cochainDiff F2 (Work.Pi6.SQM.SX K) (red42 (Work.Pi6.SQM.SX K) (m + 1 + 1) A) = 0
    rw [← red42_cochainDiff, hA, red42_zero]
  -- (6) a `ℤ/4` primitive of `pb ev A` on the contractible path space
  haveI hcontr : ContractibleSpace (Work.Pi6.SQM.SIG.PK K k₀) :=
    Work.StemsB.contractible_pathSpace K k₀
  have hpcoc : cochainDiff (ZMod 4) (Work.Pi6.SQM.SX (Work.Pi6.SQM.SIG.PK K k₀))
      (pbG (ZMod 4) (Work.Pi6.SQM.SIG.evSSet K k₀) A) = 0 := by
    rw [pbG_cochainDiff, hA, pbG_zero]
  obtain ⟨s4, hs4⟩ := exists_coboundary_of_contractible (ZMod 4) (Work.Pi6.SQM.SIG.PK K k₀) (m + 1)
    (pbG (ZMod 4) (Work.Pi6.SQM.SIG.evSSet K k₀) A) hpcoc
  -- (7) the `ℤ/4` cocycle on the loop space
  have hY4coc : cochainDiff (ZMod 4) (Work.Pi6.SQM.SX (Path k₀ k₀))
      (pbG (ZMod 4) (Work.Pi6.SQM.SIG.loopSSet K k₀) s4) = 0 := by
    rw [pbG_cochainDiff, hs4, ← pbG_comp (ZMod 4) (Work.Pi6.SQM.SIG.loopSSet K k₀)
      (Work.Pi6.SQM.SIG.evSSet K k₀) (m + 1 + 1) A, Work.Pi6.SQM.SIG.comp_loop_ev]
    exact pbG_constSSet_relKern (ZMod 4) K k₀ _ ã4
  -- (8) the `𝔽₂` cocycle which is the reduction of the `ℤ/4` one
  have hy4coc : cochainDiff F2 (Work.Pi6.SQM.SX (Path k₀ k₀))
      (Work.Pi6.SQM.SIG.pb (Work.Pi6.SQM.SIG.loopSSet K k₀)
        (red42 (Work.Pi6.SQM.SX (Work.Pi6.SQM.SIG.PK K k₀)) (m + 1) s4)) = 0 := by
    rw [← pbG_F2]
    rw [pbG_cochainDiff F2, ← red42_cochainDiff, hs4, pbG_red42,
      ← pbG_comp F2 (Work.Pi6.SQM.SIG.loopSSet K k₀) (Work.Pi6.SQM.SIG.evSSet K k₀)
        (m + 1 + 1) (red42 (Work.Pi6.SQM.SX K) (m + 1 + 1) A),
      Work.Pi6.SQM.SIG.comp_loop_ev]
    exact pbG_constSSet_relKern F2 K k₀ _ ã2
  -- (9) the computation rule for `σ` on both sides
  have hclsY : Work.Pi6.SQM.cls y2 hy2 =
      HomologicalComplex.homologyMap (relIncl F2 (TopCat.of K) ({k₀} : Set K)) (m + 1 + 1)
        (relClassOf F2 (TopCat.of K) ({k₀} : Set K) ã2 hã2) :=
    hcls2.trans (hcls42.symm.trans
      ((cohomologyClassOf_congr F2 (Work.Pi6.SQM.SX K) rfl
          (relClassOf_cochainDiff F2 (TopCat.of K) ({k₀} : Set K) ã2 hã2) hcoc42).symm.trans
        (relIncl_homologyMap_relClassOf F2 (TopCat.of K) ({k₀} : Set K) ã2 hã2).symm))
  have hs2 : cochainDiff F2 (Work.Pi6.SQM.SX (Work.Pi6.SQM.SIG.PK K k₀))
      (red42 (Work.Pi6.SQM.SX (Work.Pi6.SQM.SIG.PK K k₀)) (m + 1) s4) =
      Work.Pi6.SQM.SIG.pb (Work.Pi6.SQM.SIG.evSSet K k₀) ã2.1 := by
    rw [← red42_cochainDiff, hs4, pbG_red42]
    simp only [pbG_F2]
    rfl
  have hsigma := Work.Pi6.SQM.SIG.sigma_apply K k₀ m ã2 hã2 y2 hy2 hclsY
    (red42 (Work.Pi6.SQM.SX (Work.Pi6.SQM.SIG.PK K k₀)) (m + 1) s4) hs2 hy4coc
  refine ⟨pbG (ZMod 4) (Work.Pi6.SQM.SIG.loopSSet K k₀) s4, hY4coc,
    Work.Pi6.SQM.SIG.pb (Work.Pi6.SQM.SIG.loopSSet K k₀)
      (red42 (Work.Pi6.SQM.SX (Work.Pi6.SQM.SIG.PK K k₀)) (m + 1) s4), hy4coc, ?_, ?_⟩
  · rw [← hsigma, hcls2]
  · intro σ
    rw [← genEval_red42, pbG_red42]
    rfl

end

end Work.Pi6.SQ
