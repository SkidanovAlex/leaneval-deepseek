import Mathlib
import Submission.Work.Gen.eSymDef
import Submission.Work.Gen.chernRootTwistTop
import Submission.Work.Whitney.chernClass_whitneySum_top
import Submission.Work.LerayHirsch.LH
import Submission.Work.Gen.chernRootDefs
import Submission.Work.Gen.chernRootGeneral
import Submission.Work.Gen.chernRoot_expand
import Submission.Work.Gen.lineSumCore_top_chern
import Submission.Work.Gen.twist_lineSumCore_iso
import Submission.Work.Gen.twistTaut_c1
import Submission.Work.Gen.dualLineCore_c1_neg

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

namespace Work.Gen

open Work.TangentClasses Work.Thom

noncomputable section

variable {B : Type} [TopologicalSpace B] {ι : Type} [Fintype ι]
variable [ParacompactSpace B] [T2Space B]

/-- The sum of a constant multiple. -/
theorem chernRoot_sum_const_smul {M : Type*} [AddCommGroup M] (c : ℤ) (f : ℕ → M) (n : ℕ) :
    (∑ j ∈ Finset.range n, c • f j) = c • ∑ j ∈ Finset.range n, f j := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, Finset.sum_range_succ, ih, zsmul_add]

/-- **The Chern-root relation** in convolution form, from the vanishing of the top Chern class of
the twist `ℓ^* ⊗ π^*W`. -/
theorem chernRoot_rel {n : ℕ} (hn : 1 ≤ n)
    (M : Fin n → VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι) :
    Work.LerayHirsch.convSeries
        (fun k => eSymC (P := Work.LerayHirsch.ProjSpace (Work.LerayHirsch.lineSumCore n M)) n
          (fun i => (CohMap (Work.LerayHirsch.projMap (Work.LerayHirsch.lineSumCore n M)) ℤ 2).hom
            (Work.Thom.chernClass 1 1 (M i))) k)
        (Work.Whitney.ChernRel.geoSeriesOf
          (Work.LerayHirsch.zeta (Work.LerayHirsch.lineSumCore n M))) n = 0 := by
  let W : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin n))
      (Work.LerayHirsch.lineSumIndex n ι) := Work.LerayHirsch.lineSumCore n M
  let ζ : Coh ℤ 2 (Work.LerayHirsch.ProjSpace W) := Work.LerayHirsch.zeta W
  let t : Fin n → Coh ℤ 2 (Work.LerayHirsch.ProjSpace W) :=
    fun i => (CohMap (Work.LerayHirsch.projMap W) ℤ 2).hom (Work.Thom.chernClass 1 1 (M i))
  let E : (k : ℕ) → Coh ℤ (2 * k) (Work.LerayHirsch.ProjSpace W) := fun k => eSymC n t k
  let G : (k : ℕ) → Coh ℤ (2 * k) (Work.LerayHirsch.ProjSpace W) :=
    Work.Whitney.ChernRel.geoSeriesOf ζ
  let A : Fin n → VectorBundleCore ℂ (Work.LerayHirsch.ProjSpace W)
      (EuclideanSpace ℂ (Fin 1)) ((Work.LerayHirsch.lineSumIndex n ι × Fin n) × ι) :=
    fun i => Work.Gen.twistTaut W (M i)
  show Work.LerayHirsch.convSeries E G n = 0
  have hIso : Nonempty (Work.Thom.BundleIso (twistTautTop W)
      (Work.LerayHirsch.lineSumCore n A)) := twist_lineSumCore_iso n M
  have hTop : Work.Thom.chernClass n n (Work.LerayHirsch.lineSumCore n A)
      = Work.Gen.eSym n A n := lineSumCore_top_chern n A
  have hc1 : ∀ i, Work.Thom.chernClass 1 1 (A i) = t i - ζ :=
    fun i => twistTaut_c1 W (M i)
  have hexp : Work.Gen.eSymC (P := Work.LerayHirsch.ProjSpace W) n (fun i => t i + (-ζ)) n
      = Work.LerayHirsch.convSeries E (Work.Whitney.ChernRel.zPow (-ζ)) n :=
    chernRoot_expand t (-ζ)
  have hvanish : Work.Thom.chernClass n n (twistTautTop W) = 0 := by
    rcases lt_or_ge n 2 with h2 | h2
    · obtain rfl : n = 1 := by omega
      exact chernRoot_twistTop_one W
    · exact chernRoot_twistTop h2 W
  have hiso : Work.Thom.chernClass n n (Work.LerayHirsch.lineSumCore n A)
      = Work.Thom.chernClass n n (twistTautTop W) := by
    obtain ⟨e⟩ := hIso
    exact (Work.Thom.chernClass_BundleIso (twistTautTop W)
      (Work.LerayHirsch.lineSumCore n A) e).symm
  have hstep1 : Work.LerayHirsch.convSeries E G n
      = Work.LerayHirsch.convSeries E (Work.Whitney.ChernRel.zPow (-ζ)) n := by
    change Work.LerayHirsch.convSeries E (Work.Whitney.ChernRel.geoSeriesOf ζ) n
      = Work.LerayHirsch.convSeries E (Work.Whitney.ChernRel.zPow (-ζ)) n
    rw [← Work.Gen.zPow_neg ζ]
  have hstep2 : Work.LerayHirsch.convSeries E (Work.Whitney.ChernRel.zPow (-ζ)) n
      = Work.Gen.eSymC (P := Work.LerayHirsch.ProjSpace W) n (fun i => t i + (-ζ)) n := hexp.symm
  have hstep3 : Work.Gen.eSymC (P := Work.LerayHirsch.ProjSpace W) n (fun i => t i + (-ζ)) n
      = Work.Gen.eSymC (P := Work.LerayHirsch.ProjSpace W) n
          (fun i => Work.Thom.chernClass 1 1 (A i)) n := by
    rw [← Work.Gen.eSymC_congr (n := n)
      (u := fun i => Work.Thom.chernClass 1 1 (A i))
      (v := fun i => t i + (-ζ)) (fun i => by rw [hc1 i, sub_eq_add_neg]) n]
  have hstep4 : Work.Gen.eSymC (P := Work.LerayHirsch.ProjSpace W) n
        (fun i => Work.Thom.chernClass 1 1 (A i)) n = Work.Gen.eSym n A n := by
    rw [← Work.Gen.eSym_eq_eSymC A n]
  have hstep5 : Work.Gen.eSym n A n
      = Work.Thom.chernClass n n (Work.LerayHirsch.lineSumCore n A) := hTop.symm
  have hstep6 : Work.Thom.chernClass n n (Work.LerayHirsch.lineSumCore n A)
      = Work.Thom.chernClass n n (twistTautTop W) := hiso
  have hstep7 : Work.Thom.chernClass n n (twistTautTop W) = 0 := hvanish
  exact hstep1.trans (hstep2.trans (hstep3.trans (hstep4.trans (hstep5.trans (hstep6.trans hstep7)))))

/-- **The Chern-root relation** as a sum over `range n`. -/
theorem chernRoot_sum {n : ℕ} (hn : 1 ≤ n)
    (M : Fin n → VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι) :
    (∑ k ∈ Finset.range n, Work.LerayHirsch.convTerm
        (Work.Whitney.ChernRel.geoSeriesOf
          (Work.LerayHirsch.zeta (Work.LerayHirsch.lineSumCore n M)))
        (fun k => eSymC (P := Work.LerayHirsch.ProjSpace (Work.LerayHirsch.lineSumCore n M)) n
          (fun i => (CohMap (Work.LerayHirsch.projMap (Work.LerayHirsch.lineSumCore n M)) ℤ 2).hom
            (Work.Thom.chernClass 1 1 (M i))) k) n k)
      = (-1 : ℤ) ^ (n + 1) •
        (Work.Whitney.ChernRel.zPow (Work.LerayHirsch.zeta (Work.LerayHirsch.lineSumCore n M))) n := by
  let W : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin n))
      (Work.LerayHirsch.lineSumIndex n ι) := Work.LerayHirsch.lineSumCore n M
  let ζ : Coh ℤ 2 (Work.LerayHirsch.ProjSpace W) := Work.LerayHirsch.zeta W
  let t : Fin n → Coh ℤ 2 (Work.LerayHirsch.ProjSpace W) :=
    fun i => (CohMap (Work.LerayHirsch.projMap W) ℤ 2).hom (Work.Thom.chernClass 1 1 (M i))
  let E : (k : ℕ) → Coh ℤ (2 * k) (Work.LerayHirsch.ProjSpace W) := fun k => eSymC n t k
  let G : (k : ℕ) → Coh ℤ (2 * k) (Work.LerayHirsch.ProjSpace W) :=
    Work.Whitney.ChernRel.geoSeriesOf ζ
  show (∑ k ∈ Finset.range n, Work.LerayHirsch.convTerm G E n k)
      = (-1 : ℤ) ^ (n + 1) • (Work.Whitney.ChernRel.zPow ζ) n
  have hrel := chernRoot_rel (B := B) (ι := ι) hn M
  have hcomm : Work.LerayHirsch.convSeries G E n = 0 := by
    rw [← Work.Whitney.convSeries_comm E G n]
    exact hrel
  rw [Work.LerayHirsch.convSeries] at hcomm
  rw [Finset.sum_range_succ] at hcomm
  have htop : Work.LerayHirsch.convTerm G E n n
      = (-1 : ℤ) ^ n • (Work.Whitney.ChernRel.zPow ζ) n :=
    convTerm_geo_top_eSymC t ζ
  rw [htop] at hcomm
  rw [add_eq_zero_iff_eq_neg] at hcomm
  rw [hcomm]
  rw [← neg_zsmul]
  congr 1
  rw [pow_succ]
  ring

/-- **The Chern-root relation of a direct sum of line bundles, in Leray-Hirsch form.**
For `M : Fin n -> (complex line bundles over B)` with `n >= 1`, put `W = lineSumCore n M`,
`pi = projMap W`, `zeta = zeta W` over `P(W)`, and let `Work.Gen.eSym n M k` be the `k`-th elementary
symmetric class of the `c1(M i)`.  Then the LH expansion of `zeta^n` is

  `zeta^n = sum_{k=0}^{n-1} (-1)^(n+1+k) pi^*(e_{n-k}) cup zeta^k`,

i.e. `lhMap W n (fun i => (-1)^(n+1+i) . eSym n M (n-i)) = zetaPow W n`.

The proof: `c_n(l^* (x) pi^*W) = 0` (`Work.Gen.chernRoot_twistTop`, for `n >= 2`), while
`l^* (x) pi^*W = (+)_i (l^* (x) pi^*M i)` is a sum of `n` line bundles, so by `TopClassMul`
(`Work.Whitney.chernClass_whitneySum_top`) its top class is the product
`prod_i (pi^*c1(M i) - zeta)`; expanding gives
`sum_{k=0}^n (-1)^k pi^*(e_{n-k}) cup zeta^k = 0`, whose leading term is `(-1)^n zeta^n`.  The case
`n = 1` is `zeta = pi^*(c1(M 0))` (`Work.Grothendieck.tautLine_one_bundleComap`). -/
theorem chernRoot_split {n : ℕ} (hn : 1 ≤ n) {B : Type} [TopologicalSpace B]
    [ParacompactSpace B] [T2Space B] {ι : Type} [Fintype ι]
    (M : Fin n → VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι) :
    Work.LerayHirsch.lhMap (Work.LerayHirsch.lineSumCore n M) n
        (fun i => ((-1 : ℤ) ^ (n + 1 + (i : ℕ))) • Work.Gen.eSym n M (n - (i : ℕ)))
      = Work.LerayHirsch.zetaPow (Work.LerayHirsch.lineSumCore n M) n := by
  let W : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin n))
      (Work.LerayHirsch.lineSumIndex n ι) := Work.LerayHirsch.lineSumCore n M
  let ζ : Coh ℤ 2 (Work.LerayHirsch.ProjSpace W) := Work.LerayHirsch.zeta W
  let t : Fin n → Coh ℤ 2 (Work.LerayHirsch.ProjSpace W) :=
    fun i => (CohMap (Work.LerayHirsch.projMap W) ℤ 2).hom (Work.Thom.chernClass 1 1 (M i))
  let E : (k : ℕ) → Coh ℤ (2 * k) (Work.LerayHirsch.ProjSpace W) := fun k => eSymC n t k
  let G : (k : ℕ) → Coh ℤ (2 * k) (Work.LerayHirsch.ProjSpace W) :=
    Work.Whitney.ChernRel.geoSeriesOf ζ
  show Work.LerayHirsch.lhMap W n
      (fun i => ((-1 : ℤ) ^ (n + 1 + (i : ℕ))) • Work.Gen.eSym n M (n - (i : ℕ)))
    = Work.LerayHirsch.zetaPow W n
  rw [lhMap_eq_range_sum W
    (fun i => ((-1 : ℤ) ^ (n + 1 + (i : ℕ))) • Work.Gen.eSym n M (n - (i : ℕ)))]
  have hsplit : (∑ k ∈ Finset.range n,
        (if h : k < n then Work.LerayHirsch.lhTerm W n ⟨⟨k, h⟩, by omega⟩
          ((fun i : {i : Fin n // (i:ℕ) ≤ n} =>
            ((-1 : ℤ) ^ (n + 1 + (i:ℕ))) • Work.Gen.eSym n M (n - (i:ℕ))) ⟨⟨k, h⟩, by omega⟩)
          else 0))
      = ∑ k ∈ Finset.range n, ((-1 : ℤ) ^ (n + 1) • Work.LerayHirsch.convTerm G E n k) := by
    refine Finset.sum_congr rfl (fun k hk => ?_)
    rw [dif_pos (Finset.mem_range.mp hk)]
    exact lhTerm_split_term hn W M k (Finset.mem_range.mp hk)
  rw [hsplit, chernRoot_sum_const_smul (n := n)]
  rw [chernRoot_sum (B := B) (ι := ι) hn M]
  rw [← mul_zsmul]
  rw [show (-1 : ℤ) ^ (n + 1) * (-1 : ℤ) ^ (n + 1) = 1 from by
    rw [← mul_pow]
    norm_num]
  rw [one_zsmul]
  exact congrFun (Work.Whitney.ChernRel.zetaPow_eq_zPow W).symm n

end

end Work.Gen
