import Mathlib
import Submission.Work.Whitney.cruxDefs
import Submission.Work.LerayHirsch.SplitsOverProj
import Submission.Work.LerayHirsch.LH
import Submission.Work.Gen.eSymClass
import Submission.Work.Gen.lineSumCore_top_chern
import Submission.Work.Whitney.chernClass_whitneySum_top
import Submission.Work.Whitney.chernClass_whitneySum_pullback_eq
import Submission.Work.Whitney.nonempty_bundleIso_whitneySum_comm
import Submission.Work.Gen.exists_zeta_mul_chern_split
import Submission.Work.Gen.CruxDefs
import Submission.Work.LerayHirsch.paracompactSpace_projSpace
import Submission.Work.LerayHirsch.t2Space_projSpace
import Submission.Work.Thom.chernClass_homeo

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

/-!
# The two analytic inputs of the `ψ`-analysis, in the `WHITNEY` area

`Work.Gen.cruxUpToConstant_of_root` contains, besides the (still open) universality step, two
lemmas that the `ψ`-analysis of the crux needs and that are *proved*:

* `psi_exists_core` — the `ψ`-existence: for `W = lineSumCore (n+1) M` there is a complement `Q` of
  the tautological line in `π^*W` with `c_n(Q) = π^*(c_n W) + ζ·ψ`;
* `topClass_core` — the top-class equation `ζ ⌣ c_n(Q) = π^*(eSym (n+1) M (n+1))`.

They are reproduced here (verbatim, same statements) so that the `WHITNEY` crux assembly does not
depend on the build state of `Submission/Work/Gen/cruxUpToConstant_of_root.lean`.
-/

namespace Work.Whitney

open Work.TangentClasses Work.Thom Work.LerayHirsch

noncomputable section

variable {B : Type} [TopologicalSpace B] {ι : Type} [Fintype ι]

/-- The recursion of `eSym`, with the `dif` resolved (for `k ≥ 1`). -/
theorem eSym_succ_apply {n : ℕ}
    (A : Fin (n + 1) → VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι) {k : ℕ} (hk : 1 ≤ k) :
    Work.Gen.eSym (n + 1) A k = Work.Gen.eSym n (A ∘ Fin.castSucc) k +
      cohTransport (by omega : 2 * (1 + (k - 1)) = 2 * k)
        (Work.Whitney.cupChern 1 (k - 1) (Work.Thom.chernClass 1 1 (A (Fin.last n)))
          (Work.Gen.eSym n (A ∘ Fin.castSucc) (k - 1))) := by
  rw [Work.Gen.eSym_succ, dif_pos hk]
  rfl

/-- `eSym` vanishes in degrees above the number of variables. -/
theorem eSym_above {n : ℕ}
    (A : Fin n → VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι) {k : ℕ} (hk : n < k) :
    Work.Gen.eSym n A k = 0 := by
  rw [Work.Gen.eSym_eq_eSymC]
  exact Work.Gen.eSymC_above _ hk

section
variable [ParacompactSpace B] [T2Space B]

/-- **(A): the `ψ`-existence.**  For a family of `n + 1` line bundles (`n ≥ 1`) with sum `W`, there
is a class `ψ` on `P(W)` with `c_n(Q) = π^*c_n(W) + ζ⌣ψ` for a complement `Q` of the tautological
line in `π^*W`. -/
theorem cruxPsiExists {n : ℕ} (hn : 1 ≤ n)
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

/-- **(B): the top Chern class of the sum.**  For a family of `n + 1` line bundles with sum `W` and
a complement `Q` of the tautological line in `π^*W`, `c_n(Q)⌣ζ = π^*(e_n)`, where `e_n` is the top
elementary symmetric class of the family. -/
theorem cruxTopClassEq {n : ℕ} (hn : 1 ≤ n)
    (M : Fin (n + 1) → VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι)
    (Q : VectorBundleCore ℂ (ProjSpace (lineSumCore (n + 1) M)) (EuclideanSpace ℂ (Fin n))
          (lineSumIndex (n + 1) ι × Fin (n + 1)))
    (e : BundleIso (bundleComap (lineSumCore (n + 1) M) (projMap (lineSumCore (n + 1) M)))
          (Work.Whitney.whitneySum (Work.LerayHirsch.tautLine (lineSumCore (n + 1) M)) Q)) :
    Work.Whitney.cupChern n 1 (chernClass n n Q) (zeta (lineSumCore (n + 1) M))
      = (CohMap (projMap (lineSumCore (n + 1) M)) ℤ (2 * (n + 1))).hom
          (Work.Gen.eSym (n + 1) M (n + 1)) := by
  have h1 : Work.Whitney.cupChern n 1 (chernClass n n Q) (zeta (lineSumCore (n + 1) M))
      = chernClass (n + 1) (n + 1)
          (Work.Whitney.whitneySum Q (Work.LerayHirsch.tautLine (lineSumCore (n + 1) M))) := by
    rw [Work.Whitney.chernClass_whitneySum_top, Work.LerayHirsch.zeta_def,
      Work.Thom.cohTransport_rfl]
  rw [h1]
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
  have h3 : chernClass (1 + n) (n + 1)
        (Work.Whitney.whitneySum (Work.LerayHirsch.tautLine (lineSumCore (n + 1) M)) Q)
      = chernClass (n + 1) (n + 1)
          (bundleComap (lineSumCore (n + 1) M) (projMap (lineSumCore (n + 1) M))) := by
    exact (Work.Whitney.chernClass_eq_of_cast_fibre_iso (by omega : n + 1 = 1 + n)
      (bundleComap (lineSumCore (n + 1) M) (projMap (lineSumCore (n + 1) M)))
      (Work.Whitney.whitneySum (Work.LerayHirsch.tautLine (lineSumCore (n + 1) M)) Q) e (n + 1)).symm
  rw [h3]
  rw [Work.Thom.chernClass_comap]
  rw [Work.Gen.lineSumCore_top_chern]

end

end

end Work.Whitney
