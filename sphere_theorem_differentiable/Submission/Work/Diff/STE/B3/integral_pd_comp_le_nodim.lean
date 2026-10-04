import Mathlib
import Submission.Work.Diff.STE.B3.integral_pd_comp_le
import Submission.Work.Diff.STE.B3.pdVecMulCompExpansion
import Submission.Work.Diff.STE.B3.integralCompPeriodicLe
import Submission.Work.Diff.STE.continuous_pdVec
import Submission.Work.Diff.STE.Torus

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.B3

open MeasureTheory BigOperators

/-!
# `integral_pd_comp_le_nodim`: the `L²` bound for `∂^m (f · (u ∘ T))`, without a sup bound

This is the sup-bound-free form of `Work.Diff.STE.B3.integral_pd_comp_le`.  That theorem bounds the
`L²` norm of the top derivative of `f · (u ∘ T)` by `C * (B ^ 2 + H)`, where `B` is an a priori sup
bound for `u` and `H = Σ_{j ≤ m} Σ_{l'} ∫_{unitCube} ‖∂^{l'} u‖²`; the sup bound is an artefact of
the proof *as written* (it enters only through the very last arithmetic step), and in applications
it forces an unwanted Sobolev-embedding hypothesis (`card ι < 2 s`).  Here we prove the honest
statement in which the `B ^ 2` summand is simply absent:

  `∫_{ℝ^ι} ‖∂^m_l (f · (u ∘ T))‖² ≤ C * Σ_{j ≤ m} Σ_{l'} ∫_{unitCube} ‖∂^{l'} u‖²`.

The whole content is the chain-rule expansion `pdVecMulCompExpansion` (the coefficients of which
never mention a sup bound of `u`), the pointwise Cauchy–Schwarz bound, and the change of variables
`integralCompPeriodicLe` applied to each of the (finitely many) transported derivatives of `u`, all
of which are also sup-free.  Consequently the proof below is the proof of
`integral_pd_comp_le` with the final step `M * (Cj * H) ≤ max 1 (M * Cj) * (B ^ 2 + H)` replaced by
`M * (Cj * H) ≤ max 1 (M * Cj) * H`.
-/

noncomputable section

set_option maxHeartbeats 1600000 in
theorem integral_pd_comp_le_nodim {ι : Type*} [Fintype ι] [DecidableEq ι]
    (T : (ι → ℝ) → (ι → ℝ)) (hT : ContDiff ℝ (⊤ : ℕ∞) T)
    (f : (ι → ℝ) → ℂ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hfsupp : Function.support f ⊆ Set.pi Set.univ (fun _ : ι => Set.Ioo (-(1/2:ℝ)) (1/2)))
    (U : Set (ι → ℝ)) (hU : IsOpen U) (hUf : tsupport f ⊆ U)
    (hinj : Set.InjOn T U) (hdet : ∀ z ∈ U, (fderiv ℝ T z).det ≠ 0)
    (m : ℕ) (l : Fin m → ι) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : (ι → ℝ) → ℂ),
      ContDiff ℝ (⊤ : ℕ∞) u → Work.Diff.STE.Periodic1 u →
      ∫ z : ι → ℝ, ‖Work.Diff.STE.pdVec m l (fun z => f z * u (T z)) z‖ ^ 2
        ≤ C * ∑ j ∈ Finset.range (m+1), ∑ l' : Fin j → ι,
            ∫ x in Work.Diff.STE.unitCube (ι := ι), ‖Work.Diff.STE.pdVec j l' u x‖ ^ 2 := by
  classical
  -- the compact support of `f`
  have hKsubset : tsupport f ⊆ Set.pi Set.univ (fun _ : ι => Set.Icc (-(1/2:ℝ)) (1/2)) := by
    refine closure_minimal ?_ (isClosed_set_pi (fun _ _ => isClosed_Icc))
    intro y hy
    have hy' := hfsupp hy
    rw [Set.mem_pi] at hy' ⊢
    intro i _
    obtain ⟨h1, h2⟩ := hy' i (Set.mem_univ i)
    exact ⟨le_of_lt h1, le_of_lt h2⟩
  have hKcompact : IsCompact (tsupport f) :=
    (isCompact_univ_pi (fun _ : ι => isCompact_Icc)).of_isClosed_subset
      (isClosed_tsupport f) hKsubset
  -- the expansion
  obtain ⟨α, hαinst, ord, dir, cc, hord, hcdiff, hcvanish, hexp⟩ :=
    pdVecMulCompExpansion T hT f hf m l
  haveI : Fintype α := hαinst
  -- the weight
  set Cw : (ι → ℝ) → ℝ := fun z => (Fintype.card α : ℝ) * ∑ i : α, ‖cc i z‖ ^ 2 with hCwdef
  have hCwcont : Continuous Cw := by
    simp only [hCwdef]
    exact continuous_const.mul
      (continuous_finset_sum _ fun i _ => ((hcdiff i).continuous.norm).pow 2)
  have hCwnn : ∀ z, 0 ≤ Cw z := by
    intro z
    simp only [hCwdef]
    exact mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg fun i _ => sq_nonneg _)
  have hCwsupp : Function.support Cw ⊆ tsupport f := by
    intro z hz
    by_contra hzf
    exact hz (by
      simp only [hCwdef]
      have hz0 : ∀ i : α, cc i z = 0 := fun i => hcvanish i z hzf
      have hsum : (∑ i : α, ‖cc i z‖ ^ 2) = 0 :=
        Finset.sum_eq_zero fun i _ => by rw [hz0 i, norm_zero]; norm_num
      rw [hsum, mul_zero])
  -- the constant bounding the weight
  obtain ⟨M, hMnn, hMb⟩ : ∃ M : ℝ, 0 ≤ M ∧ ∀ z, Cw z ≤ M := by
    by_cases hKne : (tsupport f).Nonempty
    · obtain ⟨z₀, hz₀, hz₀max⟩ := hKcompact.exists_isMaxOn hKne hCwcont.continuousOn
      refine ⟨max (Cw z₀) 0, le_max_right _ _, fun z => ?_⟩
      by_cases hz : z ∈ tsupport f
      · exact le_trans (hz₀max hz) (le_max_left _ _)
      · have h0 : Cw z = 0 := by
          by_contra h
          exact hz (hCwsupp (Function.mem_support.mpr h))
        rw [h0]
        exact le_max_right _ _
    · refine ⟨0, le_refl 0, fun z => ?_⟩
      have hz : z ∉ tsupport f := fun h => hKne ⟨z, h⟩
      have h0 : Cw z = 0 := by
        by_contra h
        exact hz (hCwsupp (Function.mem_support.mpr h))
      rw [h0]
  -- the change-of-variables constant
  obtain ⟨Cj, hCjnn, hCjb⟩ := integralCompPeriodicLe T hT (tsupport f) hKcompact
    (hinj.mono hUf) (fun z hz => hdet z (hUf hz))
  refine ⟨max 1 (M * Cj), le_trans zero_le_one (le_max_left _ _), ?_⟩
  intro u hu huper
  -- abbreviations
  set S : (ι → ℝ) → ℝ := fun z => ∑ j ∈ Finset.range (m+1), ∑ l' : Fin j → ι,
      ‖Work.Diff.STE.pdVec j l' u (T z)‖ ^ 2 with hSdef
  set H : ℝ := ∑ j ∈ Finset.range (m+1), ∑ l' : Fin j → ι,
      ∫ x in Work.Diff.STE.unitCube (ι := ι), ‖Work.Diff.STE.pdVec j l' u x‖ ^ 2 with hHdef
  have hSnn : ∀ z, 0 ≤ S z := by
    intro z
    rw [hSdef]
    exact Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun l' _ => sq_nonneg _
  have hHnn : 0 ≤ H := by
    rw [hHdef]
    exact Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun l' _ =>
      integral_nonneg fun x => sq_nonneg _
  -- continuity of `S`
  have hScont : Continuous S := by
    rw [hSdef]
    refine continuous_finset_sum _ fun j _ => continuous_finset_sum _ fun l' _ => ?_
    exact (((continuous_pdVec j l' u (hu.of_le (by simp))).comp hT.continuous).norm).pow 2
  -- the instance bridge for the expansion
  have hexp' : ∀ z : ι → ℝ, Work.Diff.STE.pdVec m l (fun z => f z * u (T z)) z
      = ∑ i : α, cc i z * Work.Diff.STE.pdVec (ord i) (dir i) u (T z) := by
    intro z
    rw [hexp u hu z]
    exact Finset.sum_congr (Finset.ext fun x => by simp) (fun i _ => rfl)
  -- the pointwise bound
  have hpoint : ∀ z, ‖Work.Diff.STE.pdVec m l (fun z => f z * u (T z)) z‖ ^ 2 ≤ Cw z * S z := by
    intro z
    rw [hCwdef, hSdef, hexp' z]
    have hterm : ∀ i : α, ‖Work.Diff.STE.pdVec (ord i) (dir i) u (T z)‖ ^ 2
        ≤ ∑ j ∈ Finset.range (m+1), ∑ l' : Fin j → ι,
            ‖Work.Diff.STE.pdVec j l' u (T z)‖ ^ 2 := by
      intro i
      have h1 : ‖Work.Diff.STE.pdVec (ord i) (dir i) u (T z)‖ ^ 2
          ≤ ∑ l' : Fin (ord i) → ι, ‖Work.Diff.STE.pdVec (ord i) l' u (T z)‖ ^ 2 :=
        Finset.single_le_sum
          (s := Finset.univ)
          (f := fun l' : Fin (ord i) → ι => ‖Work.Diff.STE.pdVec (ord i) l' u (T z)‖ ^ 2)
          (fun l' _ => sq_nonneg _) (Finset.mem_univ (dir i))
      have h2 : (∑ l' : Fin (ord i) → ι, ‖Work.Diff.STE.pdVec (ord i) l' u (T z)‖ ^ 2)
          ≤ ∑ j ∈ Finset.range (m+1), ∑ l' : Fin j → ι,
              ‖Work.Diff.STE.pdVec j l' u (T z)‖ ^ 2 :=
        Finset.single_le_sum
          (s := Finset.range (m+1))
          (f := fun j : ℕ => ∑ l' : Fin j → ι, ‖Work.Diff.STE.pdVec j l' u (T z)‖ ^ 2)
          (fun j _ => Finset.sum_nonneg fun l' _ => sq_nonneg _)
          (Finset.mem_range.mpr (Nat.lt_succ_of_le (hord i)))
      exact le_trans h1 h2
    calc ‖∑ i : α, cc i z * Work.Diff.STE.pdVec (ord i) (dir i) u (T z)‖ ^ 2
        ≤ (∑ i : α, ‖cc i z * Work.Diff.STE.pdVec (ord i) (dir i) u (T z)‖) ^ 2 := by
          have h1 := norm_sum_le (Finset.univ : Finset α)
            (fun i => cc i z * Work.Diff.STE.pdVec (ord i) (dir i) u (T z))
          have h2 := norm_nonneg (∑ i : α, cc i z * Work.Diff.STE.pdVec (ord i) (dir i) u (T z))
          have h3 : (0:ℝ) ≤ ∑ i : α, ‖cc i z * Work.Diff.STE.pdVec (ord i) (dir i) u (T z)‖ :=
            Finset.sum_nonneg fun i _ => norm_nonneg _
          nlinarith
      _ ≤ (Finset.univ.card : ℝ) * ∑ i ∈ Finset.univ,
            ‖cc i z * Work.Diff.STE.pdVec (ord i) (dir i) u (T z)‖ ^ 2 :=
          sq_sum_le_card_mul_sum_sq
      _ = (Fintype.card α : ℝ) * ∑ i : α,
            ‖cc i z * Work.Diff.STE.pdVec (ord i) (dir i) u (T z)‖ ^ 2 := by simp
      _ ≤ (Fintype.card α : ℝ) * ((∑ i : α, ‖cc i z‖ ^ 2) *
            (∑ j ∈ Finset.range (m+1), ∑ l' : Fin j → ι,
              ‖Work.Diff.STE.pdVec j l' u (T z)‖ ^ 2)) := by
          apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
          calc ∑ i : α, ‖cc i z * Work.Diff.STE.pdVec (ord i) (dir i) u (T z)‖ ^ 2
              = ∑ i : α, ‖cc i z‖ ^ 2 * ‖Work.Diff.STE.pdVec (ord i) (dir i) u (T z)‖ ^ 2 := by
                apply Finset.sum_congr rfl
                intro i _
                rw [norm_mul]
                ring
            _ ≤ ∑ i : α, ‖cc i z‖ ^ 2 *
                  (∑ j ∈ Finset.range (m+1), ∑ l' : Fin j → ι,
                    ‖Work.Diff.STE.pdVec j l' u (T z)‖ ^ 2) := by
                apply Finset.sum_le_sum
                intro i _
                exact mul_le_mul_of_nonneg_left (hterm i) (sq_nonneg _)
            _ = (∑ i : α, ‖cc i z‖ ^ 2) *
                  (∑ j ∈ Finset.range (m+1), ∑ l' : Fin j → ι,
                    ‖Work.Diff.STE.pdVec j l' u (T z)‖ ^ 2) := (Finset.sum_mul _ _ _).symm
      _ = ((Fintype.card α : ℝ) * ∑ i : α, ‖cc i z‖ ^ 2) *
            (∑ j ∈ Finset.range (m+1), ∑ l' : Fin j → ι,
              ‖Work.Diff.STE.pdVec j l' u (T z)‖ ^ 2) := by ring
  -- the support of the integrand
  have hΦsupp : Function.support (fun z : ι → ℝ =>
      ‖Work.Diff.STE.pdVec m l (fun z => f z * u (T z)) z‖ ^ 2) ⊆ tsupport f := by
    intro z hz
    by_contra hzf
    have hsub : Function.support (fun z : ι → ℝ => f z * u (T z)) ⊆ Function.support f := by
      intro y hy
      rw [Function.mem_support] at hy ⊢
      intro hfy
      exact hy (by rw [hfy, zero_mul])
    have hsupp_pd : Function.support (Work.Diff.STE.pdList (List.ofFn l)
        (fun z : ι → ℝ => f z * u (T z))) ⊆ tsupport f :=
      Set.Subset.trans
        (Work.Diff.STE.csqp_support_pdList_subset_closure (List.ofFn l)
          (fun z : ι → ℝ => f z * u (T z)))
        (closure_minimal (Set.Subset.trans hsub subset_closure) (isClosed_tsupport f))
    have hz0 : Work.Diff.STE.pdVec m l (fun z => f z * u (T z)) z = 0 := by
      have h1 : Work.Diff.STE.pdList (List.ofFn l)
          (fun z : ι → ℝ => f z * u (T z)) z = 0 :=
        Function.notMem_support.mp fun hmem => hzf (hsupp_pd hmem)
      simpa only [Work.Diff.STE.pdVec] using h1
    have h2 : (fun z : ι → ℝ =>
        ‖Work.Diff.STE.pdVec m l (fun z => f z * u (T z)) z‖ ^ 2) z = 0 := by
      beta_reduce
      rw [hz0]
      norm_num
    exact hz h2
  have hΦcont : Continuous (fun z : ι → ℝ =>
      ‖Work.Diff.STE.pdVec m l (fun z => f z * u (T z)) z‖ ^ 2) := by
    have hGcd : ContDiff ℝ (⊤ : ℕ∞) (fun z : ι → ℝ => f z * u (T z)) :=
      hf.mul (hu.comp hT)
    exact (((Work.Diff.STE.csqp_contDiff_pdList_top (List.ofFn l) hGcd).continuous).norm).pow 2
  -- the chain of inequalities
  have step1 : ∫ z : ι → ℝ, ‖Work.Diff.STE.pdVec m l (fun z => f z * u (T z)) z‖ ^ 2
      = ∫ z in tsupport f, ‖Work.Diff.STE.pdVec m l (fun z => f z * u (T z)) z‖ ^ 2 :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz =>
      Function.notMem_support.mp fun hmem => hz (hΦsupp hmem)).symm
  have step2 : ∫ z in tsupport f, ‖Work.Diff.STE.pdVec m l (fun z => f z * u (T z)) z‖ ^ 2
      ≤ ∫ z in tsupport f, Cw z * S z :=
    setIntegral_mono (ContinuousOn.integrableOn_compact hKcompact hΦcont.continuousOn)
      (ContinuousOn.integrableOn_compact hKcompact (hCwcont.mul hScont).continuousOn)
      hpoint
  have step3 : ∫ z in tsupport f, Cw z * S z ≤ ∫ z in tsupport f, M * S z :=
    setIntegral_mono (ContinuousOn.integrableOn_compact hKcompact (hCwcont.mul hScont).continuousOn)
      (ContinuousOn.integrableOn_compact hKcompact (continuous_const.mul hScont).continuousOn)
      (fun z => mul_le_mul_of_nonneg_right (hMb z) (hSnn z))
  have step4 : ∫ z in tsupport f, M * S z = M * ∫ z in tsupport f, S z :=
    integral_const_mul M S
  have step5 : ∫ z in tsupport f, S z = ∑ j ∈ Finset.range (m+1), ∑ l' : Fin j → ι,
      ∫ z in tsupport f, ‖Work.Diff.STE.pdVec j l' u (T z)‖ ^ 2 := by
    have hcont : ∀ (j : ℕ) (l' : Fin j → ι),
        Continuous (fun z : ι → ℝ => ‖Work.Diff.STE.pdVec j l' u (T z)‖ ^ 2) := fun j l' =>
      (((continuous_pdVec j l' u (hu.of_le (by simp))).comp hT.continuous).norm).pow 2
    rw [hSdef]
    rw [integral_finset_sum]
    · apply Finset.sum_congr rfl
      intro j _
      rw [integral_finset_sum]
      intro l' _
      exact ContinuousOn.integrableOn_compact hKcompact (hcont j l').continuousOn
    · intro j _
      exact ContinuousOn.integrableOn_compact hKcompact
        ((continuous_finset_sum _ fun l' _ => hcont j l').continuousOn)
  have step6 : ∑ j ∈ Finset.range (m+1), ∑ l' : Fin j → ι,
      ∫ z in tsupport f, ‖Work.Diff.STE.pdVec j l' u (T z)‖ ^ 2
      ≤ Cj * H := by
    rw [hHdef]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro l' _
    exact hCjb _ (continuous_pdVec j l' u (hu.of_le (by simp)))
      (ipdcl_periodic_pdVec huper hu j l')
  have hMH : M * (Cj * H) ≤ max 1 (M * Cj) * H := by
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) hHnn
  calc ∫ z : ι → ℝ, ‖Work.Diff.STE.pdVec m l (fun z => f z * u (T z)) z‖ ^ 2
      = ∫ z in tsupport f, ‖Work.Diff.STE.pdVec m l (fun z => f z * u (T z)) z‖ ^ 2 := step1
    _ ≤ ∫ z in tsupport f, Cw z * S z := step2
    _ ≤ ∫ z in tsupport f, M * S z := step3
    _ = M * ∫ z in tsupport f, S z := step4
    _ = M * (∑ j ∈ Finset.range (m+1), ∑ l' : Fin j → ι,
          ∫ z in tsupport f, ‖Work.Diff.STE.pdVec j l' u (T z)‖ ^ 2) := by rw [step5]
    _ ≤ M * (Cj * H) := mul_le_mul_of_nonneg_left step6 hMnn
    _ ≤ max 1 (M * Cj) * H := hMH

end

end Work.Diff.STE.B3
