import Mathlib
import Submission.Work.Gen.eSymDef
import Submission.Work.Gen.CruxDefs
import Submission.Work.Gen.LhCalc
import Submission.Work.Gen.cupChern_zeta_lhTerm
import Submission.Work.Gen.cupChern_zero_lhMap
import Submission.Work.Gen.cupChern_lhTerm_zeta2
import Submission.Work.Gen.cupChern_lhTerm_zeta_top
import Submission.Work.Gen.CohMap_fibreIncl_lhMap
import Submission.Work.Gen.Coh_zero_eq_smul_oneH_of_constFibre
import Submission.Work.Gen.splitsCanonical
import Submission.Work.Gen.fibreComplementTopChern
import Submission.Work.Gen.cruxComparison
import Submission.Work.Gen.crx.Core
import Submission.Work.Gen.lineSumCore_top_chern
import Submission.Work.Kunneth.PointMain
import Submission.Work.LerayHirsch.FibreBasis
import Submission.Work.LerayHirsch.fibreQuotientComparison
import Submission.Work.LerayHirsch.modelQuotientTopChern
import Submission.Work.LerayHirsch.bijective_lhMap_fibre_of_trivCore
import Submission.Work.Cohomology.h0Evaluation
import Submission.Work.Gen.eSymClass
import Submission.Work.Gen.PsiDataDefs
import Submission.Work.Gen.exists_zeta_mul_chern_split
import Submission.Work.Whitney.chernClass_whitneySum_top
import Submission.Work.LerayHirsch.LH
import Submission.Work.LerayHirsch.SplitsOverProj
import Submission.Work.LerayHirsch.paracompactSpace_projSpace
import Submission.Work.LerayHirsch.t2Space_projSpace
import Submission.Work.LerayHirsch.lerayHirsch_of_kunnethCP
import Submission.Work.Kunneth.kunnethCP
import Submission.Work.Cohomology.exists_smul_oneH

import Submission.Work.Gen.CruxDefs
import Submission.Work.Gen.LhCalc
import Submission.Work.Gen.cupChern_zeta_lhTerm
import Submission.Work.Gen.cupChern_zero_lhMap
import Submission.Work.Gen.cupChern_lhTerm_zeta2
import Submission.Work.Gen.cupChern_lhTerm_zeta_top
import Submission.Work.Gen.CohMap_fibreIncl_lhMap
import Submission.Work.Gen.Coh_zero_eq_smul_oneH_of_constFibre
import Submission.Work.Gen.psiTopCoeff_value

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000

namespace Work.Gen

open Work.TangentClasses Work.Thom Work.LerayHirsch

noncomputable section

variable {B : Type} [TopologicalSpace B] {ι : Type} [Fintype ι]

/-- The recursion of `eSym`, with the `dif` resolved (for `k ≥ 1`). -/
theorem eSym_succ_apply {n : ℕ}
    (A : Fin (n + 1) → VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι) {k : ℕ} (hk : 1 ≤ k) :
    eSym (n + 1) A k = eSym n (A ∘ Fin.castSucc) k +
      cohTransport (by omega : 2 * (1 + (k - 1)) = 2 * k)
        (Work.Whitney.cupChern 1 (k - 1) (Work.Thom.chernClass 1 1 (A (Fin.last n)))
          (eSym n (A ∘ Fin.castSucc) (k - 1))) := by
  rw [eSym_succ, dif_pos hk]
  rfl

/-- `eSym` vanishes in degrees above the number of variables. -/
theorem eSym_above {n : ℕ}
    (A : Fin n → VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι) {k : ℕ} (hk : n < k) :
    eSym n A k = 0 := by
  rw [eSym_eq_eSymC]
  exact eSymC_above _ hk

/-! ## The top Chern class of a direct sum of line bundles -/

theorem lineSumCore_top_chern' {P : Type} [TopologicalSpace P] {ι : Type} [Fintype ι] (n : ℕ)
    (A : Fin n → VectorBundleCore ℂ P (EuclideanSpace ℂ (Fin 1)) ι) :
    Work.Thom.chernClass n n (Work.LerayHirsch.lineSumCore n A) = eSym n A n := by
  induction n with
  | zero =>
    rw [Work.LerayHirsch.lineSumCore_zero, eSym_zero]
    rw [Work.Thom.chernClass_zero_eq_oneH]
    congr 1
  | succ n ih =>
    rw [Work.LerayHirsch.lineSumCore_succ, Work.Whitney.chernClass_whitneySum_top]
    rw [ih (A ∘ Fin.castSucc)]
    rw [eSym_succ_apply A (by omega : 1 ≤ n + 1)]
    rw [eSym_above (A ∘ Fin.castSucc) (Nat.lt_succ_self n), zero_add]
    rw [Work.Whitney.ChernRel.cupChern_comm n 1]
    exact Work.LerayHirsch.cohTransport_congr_proof _ _

/-! ## The `ψ`-analysis over the projectivisation -/

section
variable {B : Type} [TopologicalSpace B] [ParacompactSpace B] [T2Space B] {ι : Type} [Fintype ι]

/-- **(A): the `ψ`-existence.**  For a family of `n + 1` line bundles (`n ≥ 1`) with sum `W`, there
is a class `ψ` on `P(W)` with `c_n(Q) = π^*c_n(W) + ζ⌣ψ` for a complement `Q` of the tautological
line in `π^*W`. -/
theorem psi_exists_core {n : ℕ} (hn : 1 ≤ n)
    (M : Fin (n + 1) → VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι) :
    ∃ (Q : VectorBundleCore ℂ
          (Work.LerayHirsch.ProjSpace (Work.LerayHirsch.lineSumCore (n + 1) M))
          (EuclideanSpace ℂ (Fin n))
          (Work.LerayHirsch.lineSumIndex (n + 1) ι × Fin (n + 1)))
      (e : BundleIso
            (bundleComap (Work.LerayHirsch.lineSumCore (n + 1) M)
              (Work.LerayHirsch.projMap (Work.LerayHirsch.lineSumCore (n + 1) M)))
            (Work.Whitney.whitneySum
              (Work.LerayHirsch.tautLine (Work.LerayHirsch.lineSumCore (n + 1) M)) Q))
      (ψ : Coh ℤ (2 * (n - 1))
            (Work.LerayHirsch.ProjSpace (Work.LerayHirsch.lineSumCore (n + 1) M))),
      chernClass n n Q
        = (CohMap (Work.LerayHirsch.projMap (Work.LerayHirsch.lineSumCore (n + 1) M))
              ℤ (2 * n)).hom
            (chernClass (n + 1) n (Work.LerayHirsch.lineSumCore (n + 1) M))
          + cohTransport (by omega : 2 * (1 + (n - 1)) = 2 * n)
              (Work.Whitney.cupChern 1 (n - 1)
                (Work.LerayHirsch.zeta (Work.LerayHirsch.lineSumCore (n + 1) M)) ψ) := by
  haveI : ParacompactSpace (Work.LerayHirsch.ProjSpace
      (Work.LerayHirsch.lineSumCore (n + 1) M)) :=
    Work.LerayHirsch.paracompactSpace_projSpace (Work.LerayHirsch.lineSumCore (n + 1) M)
  haveI : T2Space (Work.LerayHirsch.ProjSpace (Work.LerayHirsch.lineSumCore (n + 1) M)) :=
    Work.LerayHirsch.t2Space_projSpace (Work.LerayHirsch.lineSumCore (n + 1) M)
  obtain ⟨Q, hQ⟩ :=
    Work.LerayHirsch.splitsOverProj_of_paracompact (Work.LerayHirsch.lineSumCore (n + 1) M)
  obtain ⟨e⟩ := hQ
  obtain ⟨ψ, hψ⟩ := Work.Gen.exists_zeta_mul_chern_split (n := n) hn
    (Work.LerayHirsch.lineSumCore (n + 1) M) Q ⟨e⟩
  refine ⟨Q, e, ψ, ?_⟩
  rw [hψ]

/-! ## The top-class equation (the `TopClassMul` side) -/

/-- **(B): the top Chern class of the sum.**  For a family of `n + 1` line bundles with sum `W` and
a complement `Q` of the tautological line in `π^*W`, `c_n(Q)⌣ζ = π^*(e_n)`, where `e_n` is the top
elementary symmetric class of the family. -/
theorem topClass_core {n : ℕ} (hn : 1 ≤ n)
    (M : Fin (n + 1) → VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι)
    (Q : VectorBundleCore ℂ (ProjSpace (lineSumCore (n + 1) M)) (EuclideanSpace ℂ (Fin n))
          (lineSumIndex (n + 1) ι × Fin (n + 1)))
    (e : BundleIso (bundleComap (lineSumCore (n + 1) M) (projMap (lineSumCore (n + 1) M)))
          (Work.Whitney.whitneySum (Work.LerayHirsch.tautLine (lineSumCore (n + 1) M)) Q)) :
    Work.Whitney.cupChern n 1 (chernClass n n Q) (zeta (lineSumCore (n + 1) M))
      = (CohMap (projMap (lineSumCore (n + 1) M)) ℤ (2 * (n + 1))).hom
          (eSym (n + 1) M (n + 1)) := by
  -- step 1: `TopClassMul` on the sum `Q ⊕ ℓ`
  have h1 : Work.Whitney.cupChern n 1 (chernClass n n Q) (zeta (lineSumCore (n + 1) M))
      = chernClass (n + 1) (n + 1)
          (Work.Whitney.whitneySum Q (Work.LerayHirsch.tautLine (lineSumCore (n + 1) M))) := by
    rw [Work.Whitney.chernClass_whitneySum_top, Work.LerayHirsch.zeta_def,
      Work.Thom.cohTransport_rfl]
  rw [h1]
  -- step 2: commutativity of the direct sum
  have h2 : chernClass (n + 1) (n + 1)
        (Work.Whitney.whitneySum Q (Work.LerayHirsch.tautLine (lineSumCore (n + 1) M)))
      = chernClass (1 + n) (n + 1)
          (Work.Whitney.whitneySum (Work.LerayHirsch.tautLine (lineSumCore (n + 1) M)) Q) := by
    obtain ⟨e₀⟩ := Work.Whitney.nonempty_bundleIso_whitneySum_comm Q
      (Work.LerayHirsch.tautLine (lineSumCore (n + 1) M))
    exact Work.Whitney.chernClass_eq_of_cast_fibre_iso (by omega : n + 1 = 1 + n)
      (Work.Whitney.whitneySum Q (Work.LerayHirsch.tautLine (lineSumCore (n + 1) M)))
      (Work.Whitney.whitneySum (Work.LerayHirsch.tautLine (lineSumCore (n + 1) M)) Q) e₀ (n + 1)
  rw [h2]
  -- step 3: the isomorphism `π^*W ≅ ℓ ⊕ Q`
  have h3 : chernClass (1 + n) (n + 1)
        (Work.Whitney.whitneySum (Work.LerayHirsch.tautLine (lineSumCore (n + 1) M)) Q)
      = chernClass (n + 1) (n + 1)
          (bundleComap (lineSumCore (n + 1) M) (projMap (lineSumCore (n + 1) M))) := by
    exact (Work.Whitney.chernClass_eq_of_cast_fibre_iso (by omega : n + 1 = 1 + n)
      (bundleComap (lineSumCore (n + 1) M) (projMap (lineSumCore (n + 1) M)))
      (Work.Whitney.whitneySum (Work.LerayHirsch.tautLine (lineSumCore (n + 1) M)) Q) e (n + 1)).symm
  rw [h3]
  -- step 4: naturality of the Chern classes
  rw [Work.Thom.chernClass_comap]
  -- step 5: the top Chern class of a sum of line bundles
  rw [lineSumCore_top_chern']



/-- The unit law of the graded product in the direction needed below: `1 ⌣ y = y` up to the degree
cast `2*k = 2*(0+k)`. -/
theorem cupChern_oneH_eq {B : Type} [TopologicalSpace B] {k : ℕ} (y : Coh ℤ (2 * k) B) :
    Work.Whitney.cupChern 0 k (Work.Cohomology.oneH ℤ (Work.Whitney.ssB B)) y
      = cohTransport (by omega : 2 * k = 2 * (0 + k)) y := by
  conv_rhs => rw [← Work.LerayHirsch.cohTransport_cupChern_one_left k y]
  rw [Work.Whitney.cohTransport_trans]
  exact (Work.Thom.cohTransport_rfl (Work.Whitney.cupChern 0 k
    (Work.Cohomology.oneH ℤ (Work.Whitney.ssB B)) y)).symm.trans
    (Work.LerayHirsch.cohTransport_congr_proof (x := Work.Whitney.cupChern 0 k
      (Work.Cohomology.oneH ℤ (Work.Whitney.ssB B)) y) rfl _).symm

/-- **The main case of the crux**: a family of `n + 1 ≥ 2` line bundles (the `ψ`-analysis applies
with all quantities indexed by `n`).

The complement of the tautological line bundle is taken to be the *canonical* quotient bundle
`Work.LerayHirsch.quotientBundle W`, whose splitting `π^*W ≅ ℓ ⊕ (π^*W/ℓ)` is
`Work.Gen.splitsCanonical`; this is what makes the fibre computation available
(`Work.LerayHirsch.fibreQuotientComparison`). -/
theorem cruxMain {n : ℕ} (hn : 1 ≤ n)
    {B : Type} [TopologicalSpace B] [ParacompactSpace B] [T2Space B] {ι : Type} [Fintype ι]
    (hroot : ∀ (n : ℕ) {B : Type} [TopologicalSpace B] [ParacompactSpace B] [T2Space B]
      {ι : Type} [Fintype ι] (M : Fin n → VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι),
      Work.LerayHirsch.lhMap (Work.LerayHirsch.lineSumCore n M) n
        (fun i => ((-1 : ℤ) ^ (n + 1 + (i : ℕ))) • Work.Gen.eSym n M (n - (i : ℕ)))
      = Work.LerayHirsch.zetaPow (Work.LerayHirsch.lineSumCore n M) n)
    (M : Fin (n + 1) → VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι) :
    Work.Thom.chernClass (n + 1) n (Work.LerayHirsch.lineSumCore (n + 1) M)
      = ((-(modelK n)) * (-1 : ℤ) ^ (n + 3)) • Work.Gen.eSym (n + 1) M n := by
  have hLH : Work.LerayHirsch.LerayHirsch (Work.LerayHirsch.lineSumCore (n + 1) M) :=
    (Work.LerayHirsch.lerayHirschFull_of_kunnethCP Work.Kunneth.kunnethCP _).1
  -- the canonical complement and its splitting
  haveI : ParacompactSpace (Work.LerayHirsch.ProjSpace (Work.LerayHirsch.lineSumCore (n + 1) M)) :=
    Work.LerayHirsch.paracompactSpace_projSpace _
  haveI : T2Space (Work.LerayHirsch.ProjSpace (Work.LerayHirsch.lineSumCore (n + 1) M)) :=
    Work.LerayHirsch.t2Space_projSpace _
  have hspl := splitsCanonical (n := n) (Work.LerayHirsch.lineSumCore (n + 1) M)
  -- the `ψ`-existence (A) and the top-class equation (B)
  obtain ⟨ψ, hA⟩ := Work.Gen.exists_zeta_mul_chern_split (n := n) hn
    (Work.LerayHirsch.lineSumCore (n + 1) M) (Work.LerayHirsch.quotientBundle _) hspl
  have hB := topClass_core (n := n) hn M (Work.LerayHirsch.quotientBundle _) (Classical.choice hspl)
  -- the Leray–Hirsch decomposition of `ψ` at level `n - 1`
  obtain ⟨ψf, hψ, _⟩ := Work.LerayHirsch.existsUnique_lh_decomposition
    (Work.LerayHirsch.lineSumCore (n + 1) M) hLH (n - 1) ψ
  -- the Chern-root family and the coefficient comparison
  have hcomp := cruxComparison (n := n) hn (Work.LerayHirsch.lineSumCore (n + 1) M) hLH
    (Work.Thom.chernClass (n + 1) n (Work.LerayHirsch.lineSumCore (n + 1) M))
    (Work.Gen.eSym (n + 1) M (n + 1)) ψ
    (Work.Thom.chernClass n n (Work.LerayHirsch.quotientBundle _)) ψf hψ hA hB
    (fun i : {i : Fin (n + 1) // (i : ℕ) ≤ n + 1} =>
      ((-1 : ℤ) ^ (n + 1 + 1 + (i : ℕ))) • Work.Gen.eSym (n + 1) M ((n + 1) - (i : ℕ)))
    (hroot (n + 1) M)
  -- the value of the top coefficient, from the fibre model computation
  have hQ : ∀ b : B,
      (Work.Thom.CohMap (Work.LerayHirsch.fibreIncl (Work.LerayHirsch.lineSumCore (n + 1) M) b)
          ℤ (2 * n)).hom (Work.Thom.chernClass n n (Work.LerayHirsch.quotientBundle _))
      = modelK n • (Work.Thom.CohMap
            (Work.LerayHirsch.fibreIncl (Work.LerayHirsch.lineSumCore (n + 1) M) b) ℤ (2 * n)).hom
          (Work.LerayHirsch.zetaPow (Work.LerayHirsch.lineSumCore (n + 1) M) n) :=
    fun b => fibreComplementTopChern_of_iso n hn _ _ b
      ⟨Work.Thom.BundleIso.ofEq rfl⟩
  have hval := psiTopCoeff_value (n := n) hn (Work.LerayHirsch.lineSumCore (n + 1) M)
    (Work.LerayHirsch.quotientBundle _) ψ
    (Work.Thom.chernClass (n + 1) n (Work.LerayHirsch.lineSumCore (n + 1) M)) ψf hψ hA hQ
  have htop : cohTransport (topCoeffIdx_degree (n := n)) (ψf topCoeffIdx)
      = modelK n • Work.Cohomology.oneH ℤ (Work.Whitney.ssB B) :=
    Coh_zero_eq_smul_oneH_of_constFibre (by omega) (Work.LerayHirsch.lineSumCore (n + 1) M)
      _ (modelK n) hval
  have hγ : cohTransport (topCoeffIdx_degree (n := n)) (-(ψf topCoeffIdx))
      = (-(modelK n)) • Work.Cohomology.oneH ℤ (Work.Whitney.ssB B) := by
    rw [Work.Whitney.ChernRel.cohTransport_neg, htop, neg_zsmul]
  -- the value of the index-`1` Chern-root coefficient
  have hc1 : ((fun i : {i : Fin (n + 1) // (i : ℕ) ≤ n + 1} =>
        ((-1 : ℤ) ^ (n + 1 + 1 + (i : ℕ))) • Work.Gen.eSym (n + 1) M ((n + 1) - (i : ℕ))) :
      (i : {i : Fin (n + 1) // (i : ℕ) ≤ n + 1}) → Coh ℤ (2 * ((n + 1) - (i : ℕ))) B)
        ⟨⟨1, by omega⟩, by omega⟩
      = ((-1 : ℤ) ^ (n + 3)) • Work.Gen.eSym (n + 1) M n := rfl

  -- assembling: `x = (-(k n)) • (c_1) = (-(k n)) • ((-1)^(n+3) • e_{n})`
  have hfinal : cohTransport (by omega : 2 * (0 + ((n + 1) - 1)) = 2 * n)
        (Work.Whitney.cupChern 0 ((n + 1) - 1)
          (Work.Thom.cohTransport (Work.Gen.topCoeffIdx_degree (n := n))
            (-(ψf Work.Gen.topCoeffIdx)))
          ((fun i : {i : Fin (n + 1) // (i : ℕ) ≤ n + 1} =>
            ((-1 : ℤ) ^ (n + 1 + 1 + (i : ℕ))) •
              Work.Gen.eSym (n + 1) M ((n + 1) - (i : ℕ))) ⟨⟨1, by omega⟩, by omega⟩))
      = ((-(modelK n)) * (-1 : ℤ) ^ (n + 3)) • Work.Gen.eSym (n + 1) M n := by
    rw [hγ, hc1, Work.Kunneth.cupChern_zsmul_left, Work.Gen.cupChern_zsmul_right,
      cupChern_oneH_eq, Work.Thom.cohTransport_zsmul, Work.Thom.cohTransport_zsmul,
      ← smul_smul]
    congr 1
    congr 1
    rw [Work.Whitney.cohTransport_trans]
    exact (Work.LerayHirsch.cohTransport_congr_proof
        (x := Work.Gen.eSym (n + 1) M n) (by omega : 2 * n = 2 * n)
        (by omega : 2 * n = 2 * n)).trans (Work.Thom.cohTransport_rfl _)
  rw [hcomp, hfinal]

/-- **The crux of the Whitney sum formula, up to a universal constant, from the Chern-root
relation.**  For every `n` there is an integer `delta n` such that for every family
`M : Fin n ->` (complex line bundles over a paracompact Hausdorff base `B`),

  `c_{n-1}(lineSumCore n M) = delta n . eSym n M (n-1)`.

The content is the `psi`-analysis over `P(W)` (`W = lineSumCore n M`): the psi-existence
(`Work.Gen.exists_zeta_mul_chern_split`, applied with `Z := W`) gives `psi` with
`c_{n-1}(Q) = pi^*(c_{n-1} W) + zeta * psi` for a complement `Q` of `l` in `pi^*W`; `TopClassMul`
at degree `n` gives `zeta * c_{n-1}(Q) = pi^*(e_n)`, hence
`zeta * pi^*(c_{n-1} W) + zeta^2 * psi = pi^*(e_n)`; comparing Leray-Hirsch coefficients at index
`1` (with `zeta^n` expanded by the hypothesis `hroot`, the Chern-root relation) gives
`c_{n-1}(W) = delta * e_{n-1}` with `delta := (-1)^(n+1) * (the zeta^{n-2}-coefficient of psi)`;
the restriction of that equation to a fibre `P(W_b) = P(CC^n)` (`Work.LerayHirsch.fibreIncl`,
`CohMap_fibreIncl_zeta`, and `i_b^*Q = eps^n / l_f` canonically, since any complement of `l_f` in
`eps^n` maps isomorphically to the quotient) shows that coefficient is the same integer for every
`b`, which is what makes `delta` independent of `M`. -/
theorem cruxUpToConstant_of_root
    (hroot : ∀ (n : ℕ) {B : Type} [TopologicalSpace B] [ParacompactSpace B] [T2Space B]
      {ι : Type} [Fintype ι] (M : Fin n → VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι),
      Work.LerayHirsch.lhMap (Work.LerayHirsch.lineSumCore n M) n
        (fun i => ((-1 : ℤ) ^ (n + 1 + (i : ℕ))) • Work.Gen.eSym n M (n - (i : ℕ)))
      = Work.LerayHirsch.zetaPow (Work.LerayHirsch.lineSumCore n M) n) :
    ∃ δ : ℕ → ℤ, ∀ (n : ℕ) {B : Type} [TopologicalSpace B] [ParacompactSpace B] [T2Space B]
      {ι : Type} [Fintype ι]
      (M : Fin n → VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι),
      Work.Thom.chernClass n (n - 1) (Work.LerayHirsch.lineSumCore n M)
        = δ n • Work.Gen.eSym n M (n - 1) := by
  refine ⟨fun N => if 2 ≤ N then (-(modelK (N - 1))) * (-1 : ℤ) ^ (N + 2) else 1, ?_⟩
  intro N B _ _ _ ι _ M
  rcases N with _ | _ | m
  · -- `N = 0`: both sides are the unit class
    show Work.Thom.chernClass 0 (0 - 1) (Work.LerayHirsch.lineSumCore 0 M)
      = (1 : ℤ) • Work.Gen.eSym 0 M (0 - 1)
    rw [Work.Thom.chernClass_zero_eq_oneH, one_smul, Work.Gen.eSym_zero]
    exact ((Work.LerayHirsch.cohTransport_congr_proof (x := Work.Cohomology.oneH ℤ
        (Work.Whitney.ssB B)) _ rfl).trans (Work.Thom.cohTransport_rfl _)).symm
  · -- `N = 1`: both sides are the unit class
    show Work.Thom.chernClass 1 (1 - 1) (Work.LerayHirsch.lineSumCore 1 M)
      = (1 : ℤ) • Work.Gen.eSym 1 M (1 - 1)
    rw [Work.Thom.chernClass_zero_eq_oneH, one_smul, Work.Gen.eSym_succ,
      dif_neg (by omega : ¬1 ≤ 0), add_zero, Work.Gen.eSym_zero]
    exact ((Work.LerayHirsch.cohTransport_congr_proof (x := Work.Cohomology.oneH ℤ
        (Work.Whitney.ssB B)) _ rfl).trans (Work.Thom.cohTransport_rfl _)).symm
  · -- `N = m + 2 ≥ 2`: the main case
    show Work.Thom.chernClass (m + 2) ((m + 2) - 1) (Work.LerayHirsch.lineSumCore (m + 2) M)
      = ((-(modelK (m + 2 - 1))) * (-1 : ℤ) ^ (m + 2 + 2))
          • Work.Gen.eSym (m + 2) M ((m + 2) - 1)
    exact cruxMain (n := m + 1) (by omega) hroot M

end

end

end Work.Gen
