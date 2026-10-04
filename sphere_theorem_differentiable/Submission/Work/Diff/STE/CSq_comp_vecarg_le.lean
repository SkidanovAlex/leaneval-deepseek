import Mathlib
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.CSq_comp_le
import Submission.Work.Diff.STE.Comp.young_conv_lp
import Submission.Work.Diff.STE.Comp.phi_derivBound
import Submission.Work.Diff.STE.norm_seriesFun_le
import Submission.Work.Diff.STE.l1_le_sqrt_CSq
import Submission.Work.Diff.STE.CSq_le_ENormSq
import Submission.Work.Diff.STE.Comp.summable_wt_fourierCoeff
import Submission.Work.Diff.STE.Comp3.faaDiBruno_vec
import Submission.Work.Diff.STE.Comp3.integral_prod_block_general

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The Moser composition estimate for a vector-valued argument

This file proves `Work.Diff.STE.CSq_comp_vecarg_le`: for a smooth `Φ : (Fin m → ℂ) → ℂ` and
coefficient families `c : (ι → ℤ) → (Fin m → ℂ)` whose `ρ`-Sobolev norm is bounded by `B`
(with `card ι < 2ρ ≤ 2s`), the composition

  `x ↦ Φ (fun i => seriesFun (fun k => c k i) x)`

has finite weighted `ℓ²` Fourier coefficients, controlled linearly in the top Sobolev norm
`∑ i, CSq s (fun k => c k i)` of the data — the vector-valued (multivariate) Moser estimate.

The strategy is the same as for the scalar case (`Work.Diff.STE.CSq_comp_le`):

* **Faà di Bruno** (`Comp3.faaDiBruno_vec`) expands `∂^s (Φ ∘ V)` into a sum over ordered
  partitions, the terms being `(D^{r}Φ)(V x)` applied to the block derivatives of `V`.
* Each block derivative of the `j`-th component is again a Fourier series
  (`iteratedFDeriv_seriesFun_component`), with coefficient family a `blockFam`.
* **Young's inequality** for `r`-fold convolutions (`Comp.young_conv_lp`) followed by the sharp
  weighted `ℓ^p` interpolation (`Comp.weighted_lp_le`) bounds the `L²` norm of the product of the
  block derivatives by `C (1 + CSq s γ)` (`Comp3.integral_prod_block_general`), where `γ` is the
  scalar majorant `k ↦ ‖c k‖`.
* Finally `CSq_le_ENormSq` converts the physical-space energy bound into the spectral one.
-/

noncomputable section

namespace Work.Diff.STE

open MeasureTheory BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Auxiliary lemmas -/

/-- `CSq` is nonnegative. -/
lemma CSq_nonneg (s : ℕ) (c : (ι → ℤ) → ℂ) : 0 ≤ CSq s c :=
  tsum_nonneg fun k => mul_nonneg (pow_nonneg (le_of_lt (wt_pos k)) s) (sq_nonneg _)

/-- Sup-norm bound for the iterated derivatives of a smooth `Φ : (Fin m → ℂ) → ℂ` on a closed
ball.  This is the vector-argument analogue of `Work.Diff.STE.Comp.phi_derivBound`. -/
lemma phi_derivBound_pi {m : ℕ} (Φ : (Fin m → ℂ) → ℂ) (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ)
    (R : ℝ) (s : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z : Fin m → ℂ, ‖z‖ ≤ R → ∀ i : ℕ, i ≤ s →
      ‖iteratedFDeriv ℝ i Φ z‖ ≤ M := by
  have hcompact : IsCompact {z : Fin m → ℂ | ‖z‖ ≤ R} := by
    simpa [Metric.closedBall, dist_eq_norm] using isCompact_closedBall (0 : Fin m → ℂ) R
  have hcont : ∀ i : ℕ,
      ContinuousOn (fun z : Fin m → ℂ => iteratedFDeriv ℝ i Φ z) {z | ‖z‖ ≤ R} :=
    fun i => (hΦ.continuous_iteratedFDeriv (by simp)).continuousOn
  choose C hC using fun i : ℕ => hcompact.exists_bound_of_continuousOn (hcont i)
  have hne : (Finset.range (s + 1)).Nonempty := ⟨0, Finset.mem_range.mpr (Nat.succ_pos s)⟩
  refine ⟨(Finset.range (s + 1)).sup' hne (fun i => |C i|), ?_, ?_⟩
  · exact le_trans (abs_nonneg (C 0))
      (Finset.le_sup' (fun i : ℕ => |C i|) (Finset.mem_range.mpr (Nat.succ_pos s)))
  · intro z hz i hi
    have hmem : i ∈ Finset.range (s + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hi)
    have h1 : ‖iteratedFDeriv ℝ i Φ z‖ ≤ C i := hC i z hz
    have h2 : C i ≤ |C i| := le_abs_self (C i)
    have h3 : |C i| ≤ (Finset.range (s + 1)).sup' hne (fun i => |C i|) :=
      Finset.le_sup' (fun i : ℕ => |C i|) hmem
    linarith

/-- The sup norm on `Fin m → ℂ` is dominated by the sum of the squared norms of the components. -/
lemma pi_norm_sq_le_sum_norm_sq {m : ℕ} (z : Fin m → ℂ) :
    ‖z‖ ^ 2 ≤ ∑ j, ‖z j‖ ^ 2 := by
  rcases isEmpty_or_nonempty (Fin m) with h | h
  · have hz : z = 0 := funext fun j => (h.false j).elim
    simp [hz]
  · obtain ⟨j₀, -, hj⟩ := Finset.exists_max_image Finset.univ (fun j => ‖z j‖)
      ⟨Classical.arbitrary (Fin m), Finset.mem_univ _⟩
    have h1 : ‖z‖ ≤ ‖z j₀‖ :=
      (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun j => hj j (Finset.mem_univ j)
    calc ‖z‖ ^ 2 ≤ ‖z j₀‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ ≤ ∑ j, ‖z j‖ ^ 2 :=
          Finset.single_le_sum (f := fun j => ‖z j‖ ^ 2) (fun j _ => sq_nonneg _)
            (Finset.mem_univ j₀)

/-- The moments of a component are controlled by the moments of the vector family. -/
lemma summable_moment_component {m : ℕ} (C : (ι → ℤ) → (Fin m → ℂ))
    (hmom : ∀ N : ℕ, Summable fun k : ι → ℤ => (wt k) ^ N * ‖C k‖) (j : Fin m) (N : ℕ) :
    Summable fun k : ι → ℤ => (wt k) ^ N * ‖C k j‖ := by
  refine Summable.of_nonneg_of_le
    (fun k => mul_nonneg (pow_nonneg (le_of_lt (wt_pos k)) N) (norm_nonneg _))
    (fun k => ?_) (hmom N)
  exact mul_le_mul_of_nonneg_left (norm_le_pi_norm (C k) j) (pow_nonneg (le_of_lt (wt_pos k)) N)

/-- The `s`-fold directional derivative of the `j`-th component of a Fourier series is the
Fourier series of the corresponding differentiated coefficient family. -/
lemma iteratedFDeriv_seriesFun_component {m : ℕ} (s : ℕ) (l : Fin s → ι)
    (C : (ι → ℤ) → (Fin m → ℂ))
    (hmom : ∀ N : ℕ, Summable fun k : ι → ℤ => (wt k) ^ N * ‖C k‖) (j : Fin m) (x : ι → ℝ) :
    iteratedFDeriv ℝ s (fun y => seriesFun (fun k => C k j) y) x (fun j' => Pi.single (l j') 1)
      = seriesFun (dmulV (List.ofFn l) (fun k => C k j)) x := by
  have hm := summable_moment_component C hmom j
  have hcd : ContDiff ℝ (⊤ : ℕ∞) (seriesFun (fun k => C k j)) := contDiff_seriesFun _ hm
  rw [← Comp.pdVec_eq_iteratedFDeriv s (seriesFun (fun k => C k j)) hcd x l]
  exact pdList_seriesFun (List.ofFn l) (fun k => C k j) hm x

/-- A vector of Fourier series is smooth. -/
lemma contDiff_seriesFunVec {m : ℕ} (C : (ι → ℤ) → (Fin m → ℂ))
    (hmom : ∀ N : ℕ, Summable fun k : ι → ℤ => (wt k) ^ N * ‖C k‖) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y : ι → ℝ => fun j : Fin m => seriesFun (fun k => C k j) y) :=
  contDiff_pi.mpr fun j => contDiff_seriesFun _ (summable_moment_component C hmom j)

/-- A vector of Fourier series is `1`-periodic. -/
lemma periodic_seriesFunVec {m : ℕ} (C : (ι → ℤ) → (Fin m → ℂ)) :
    Periodic1 (fun y : ι → ℝ => fun j : Fin m => seriesFun (fun k => C k j) y) :=
  fun i x => funext fun j => periodic_seriesFun (fun k => C k j) i x

/-- **The energy estimate for one derivative tuple.**  Under the product estimate `hprod` for the
block families (supplied by `Comp3.integral_prod_block_general`), the `L²` norm of the `l`-th
order-`s` derivative of `Φ ∘ seriesFun` over the cube is bounded by a constant times
`1 + CSq s γ`, where `γ` is the scalar majorant `k ↦ ‖C k‖`. -/
private lemma integral_pdVec_comp_le {m : ℕ} (s : ℕ) (hs : 0 < s)
    {Kb M Kprod : ℝ} (Φ : (Fin m → ℂ) → ℂ) (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ)
    (hM : ∀ z : Fin m → ℂ, ‖z‖ ≤ Kb → ∀ i : ℕ, i ≤ s → ‖iteratedFDeriv ℝ i Φ z‖ ≤ M)
    (hKprod : 0 ≤ Kprod)
    (C : (ι → ℤ) → (Fin m → ℂ))
    (hmom : ∀ N : ℕ, Summable fun k : ι → ℤ => (wt k) ^ N * ‖C k‖)
    (hsup : ∀ x : ι → ℝ, ‖(fun j : Fin m => seriesFun (fun k => C k j) x)‖ ≤ Kb)
    (hprod : ∀ {r : ℕ} (hr : 1 ≤ r) (hrs : r ≤ s) (d : Fin r → (ι → ℤ) → ℂ) (β : Fin r → ℕ),
      (∀ i, β i ≤ s) → (∑ i, β i = s) →
      (∀ i k, ‖d i k‖ ≤ (2 * Real.pi * ‖k‖) ^ (β i) * ‖C k‖) →
      (∀ i, Summable fun k : ι → ℤ => ‖d i k‖ ^ (yExp s (β i))) →
      ∫ x in unitCube, ‖∏ i, seriesFun (d i) x‖ ^ 2
        ≤ Kprod * (1 + CSq s (fun k => ((‖C k‖ : ℝ) : ℂ))))
    (l : Fin s → ι) :
    ∫ x in unitCube, ‖pdVec s l (fun y => Φ (fun j => seriesFun (fun k => C k j) y)) x‖ ^ 2
      ≤ (Fintype.card (OrderedFinpartition s) : ℝ) ^ 2 * M ^ 2 * ((m : ℝ) + 1) ^ s * Kprod *
          (1 + CSq s (fun k => ((‖C k‖ : ℝ) : ℂ))) := by
  classical
  set V : (ι → ℝ) → (Fin m → ℂ) := fun y => fun j => seriesFun (fun k => C k j) y with hVdef
  have hVdiff : ContDiff ℝ (⊤ : ℕ∞) V := contDiff_seriesFunVec C hmom
  -- summability of the block families
  have hmomBlock : ∀ (c : OrderedFinpartition s) (σ : Fin c.length → Fin m) (i : Fin c.length)
      (N : ℕ), Summable fun k : ι → ℤ => (wt k) ^ N * ‖blockFam (fun k' => C k' (σ i)) l c i k‖ := by
    intro c σ i N
    simpa only [blockFam] using
      summable_dmulV (List.ofFn fun j' => l (c.emb i j')) (fun k' => C k' (σ i))
        (summable_moment_component C hmom (σ i)) N
  have hsmBlock : ∀ (c : OrderedFinpartition s) (σ : Fin c.length → Fin m) (i : Fin c.length),
      Summable fun k : ι → ℤ =>
        ‖blockFam (fun k' => C k' (σ i)) l c i k‖ ^ (yExp s (c.partSize i)) := by
    intro c σ i
    exact summable_blockFam_rpow (fun k' => C k' (σ i)) (summable_moment_component C hmom (σ i))
      (by simpa using summable_moment_component C hmom (σ i) 0) l c i (yExp s (c.partSize i))
      (one_le_yExp s hs (c.partSize i) (c.partSize_le i))
  -- the pointwise bound
  have hpt : ∀ x : ι → ℝ,
      ‖pdVec s l (fun y => Φ (V y)) x‖ ^ 2
        ≤ (Fintype.card (OrderedFinpartition s) : ℝ) *
            ∑ c : OrderedFinpartition s, M ^ 2 * ∑ σ : Fin c.length → Fin m,
              ∏ i, ‖seriesFun (blockFam (fun k => C k (σ i)) l c i) x‖ ^ 2 := by
    intro x
    rw [Comp3.faaDiBruno_vec s Φ hΦ V hVdiff x l]
    refine (pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2).trans ?_
    refine (sq_sum_le_card_mul_sum_sq (s := Finset.univ)
      (f := fun c : OrderedFinpartition s =>
        ‖(iteratedFDeriv ℝ c.length Φ (V x))
          (fun i => (fun j : Fin m =>
            iteratedFDeriv ℝ (c.partSize i) (fun y => V y j) x
              (fun j' => Pi.single (l (c.emb i j')) 1)))‖)).trans ?_
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun c _ => ?_) (Nat.cast_nonneg _)
    -- bound one partition term
    have hbv : ∀ i : Fin c.length,
        ‖(fun j : Fin m => iteratedFDeriv ℝ (c.partSize i) (fun y => V y j) x
            (fun j' => Pi.single (l (c.emb i j')) 1))‖ ^ 2
          ≤ ∑ j : Fin m, ‖seriesFun (blockFam (fun k => C k j) l c i) x‖ ^ 2 := by
      intro i
      refine (pi_norm_sq_le_sum_norm_sq _).trans (Finset.sum_le_sum fun j _ => ?_)
      have hb := iteratedFDeriv_seriesFun_component (c.partSize i) (fun j' => l (c.emb i j')) C
        hmom j x
      have hVj : (fun y => V y j) = fun y => seriesFun (fun k => C k j) y := rfl
      rw [hVj, hb]
      simp only [blockFam]
      exact le_rfl
    have hMb : ‖iteratedFDeriv ℝ c.length Φ (V x)‖ ≤ M :=
      hM (V x) (hsup x) c.length c.length_le
    have hop : ‖(iteratedFDeriv ℝ c.length Φ (V x))
          (fun i => (fun j : Fin m => iteratedFDeriv ℝ (c.partSize i) (fun y => V y j) x
              (fun j' => Pi.single (l (c.emb i j')) 1)))‖
        ≤ M * ∏ i, ‖(fun j : Fin m => iteratedFDeriv ℝ (c.partSize i) (fun y => V y j) x
              (fun j' => Pi.single (l (c.emb i j')) 1))‖ :=
      (ContinuousMultilinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_right hMb (by positivity))
    calc ‖(iteratedFDeriv ℝ c.length Φ (V x))
            (fun i => (fun j : Fin m => iteratedFDeriv ℝ (c.partSize i) (fun y => V y j) x
              (fun j' => Pi.single (l (c.emb i j')) 1)))‖ ^ 2
        ≤ (M * ∏ i, ‖(fun j : Fin m => iteratedFDeriv ℝ (c.partSize i) (fun y => V y j) x
              (fun j' => Pi.single (l (c.emb i j')) 1))‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hop 2
      _ = M ^ 2 * ∏ i, ‖(fun j : Fin m => iteratedFDeriv ℝ (c.partSize i) (fun y => V y j) x
              (fun j' => Pi.single (l (c.emb i j')) 1))‖ ^ 2 := by
          rw [mul_pow, Finset.prod_pow]
      _ ≤ M ^ 2 * ∏ i, ∑ j : Fin m,
              ‖seriesFun (blockFam (fun k => C k j) l c i) x‖ ^ 2 :=
          mul_le_mul_of_nonneg_left (Finset.prod_le_prod₀ (fun i _ => by positivity)
            (fun i _ => hbv i)) (sq_nonneg _)
      _ = M ^ 2 * ∑ σ : Fin c.length → Fin m,
            ∏ i, ‖seriesFun (blockFam (fun k => C k (σ i)) l c i) x‖ ^ 2 := by
          rw [Finset.prod_univ_sum (t := fun _ => Finset.univ), Fintype.piFinset_univ]
  -- continuity / integrability
  have hcontR : Continuous fun x : ι → ℝ =>
      (Fintype.card (OrderedFinpartition s) : ℝ) *
        ∑ c : OrderedFinpartition s, M ^ 2 * ∑ σ : Fin c.length → Fin m,
          ∏ i, ‖seriesFun (blockFam (fun k => C k (σ i)) l c i) x‖ ^ 2 := by
    refine continuous_const.mul (continuous_finsetSum _ fun c _ => ?_)
    refine continuous_const.mul (continuous_finsetSum _ fun σ _ => ?_)
    exact continuous_finsetProd _ fun i _ =>
      ((contDiff_seriesFun _ (hmomBlock c σ i)).continuous.norm).pow 2
  have hcontL : Continuous fun x : ι → ℝ => ‖pdVec s l (fun y => Φ (V y)) x‖ ^ 2 :=
    ((continuous_pdVec s l _ ((hΦ.comp hVdiff).of_le (by simp))).norm).pow 2
  have hInt := MeasureTheory.integral_mono_ae
    (el_integrableOn_unitCube_of_continuous_real hcontL)
    (el_integrableOn_unitCube_of_continuous_real hcontR)
    (Filter.Eventually.of_forall hpt)
  -- evaluate the integral of the right-hand side
  have hstep : ∫ x in unitCube, ((Fintype.card (OrderedFinpartition s) : ℝ) *
        ∑ c : OrderedFinpartition s, M ^ 2 * ∑ σ : Fin c.length → Fin m,
          ∏ i, ‖seriesFun (blockFam (fun k => C k (σ i)) l c i) x‖ ^ 2)
      = (Fintype.card (OrderedFinpartition s) : ℝ) *
        ∑ c : OrderedFinpartition s, M ^ 2 * ∑ σ : Fin c.length → Fin m,
          ∫ x in unitCube, ∏ i, ‖seriesFun (blockFam (fun k => C k (σ i)) l c i) x‖ ^ 2 := by
    rw [MeasureTheory.integral_const_mul]
    congr 1
    rw [MeasureTheory.integral_finsetSum Finset.univ (fun c _ => ?_)]
    · refine Finset.sum_congr rfl fun c _ => ?_
      rw [MeasureTheory.integral_const_mul]
      rw [MeasureTheory.integral_finsetSum Finset.univ (fun σ _ => ?_)]
      exact el_integrableOn_unitCube_of_continuous_real
        (continuous_finsetProd _ fun i _ =>
          ((contDiff_seriesFun _ (hmomBlock c σ i)).continuous.norm).pow 2)
    · exact el_integrableOn_unitCube_of_continuous_real (continuous_const.mul
        (continuous_finsetSum _ fun σ _ => continuous_finsetProd _ fun i _ =>
          ((contDiff_seriesFun _ (hmomBlock c σ i)).continuous.norm).pow 2))
  -- bound each term with the product estimate
  have hterm : ∀ (c : OrderedFinpartition s) (σ : Fin c.length → Fin m),
      ∫ x in unitCube, ∏ i, ‖seriesFun (blockFam (fun k => C k (σ i)) l c i) x‖ ^ 2
        ≤ Kprod * (1 + CSq s (fun k => ((‖C k‖ : ℝ) : ℂ))) := by
    intro c σ
    have hcongr : (∫ x in unitCube,
          ∏ i, ‖seriesFun (blockFam (fun k => C k (σ i)) l c i) x‖ ^ 2)
        = ∫ x in unitCube,
            ‖∏ i, seriesFun (blockFam (fun k => C k (σ i)) l c i) x‖ ^ 2 := by
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      show (∏ i, ‖seriesFun (blockFam (fun k => C k (σ i)) l c i) x‖ ^ 2)
          = ‖∏ i, seriesFun (blockFam (fun k => C k (σ i)) l c i) x‖ ^ 2
      rw [Finset.prod_pow, norm_prod]
    rw [hcongr]
    refine hprod (c.length_pos hs) c.length_le (fun i => blockFam (fun k => C k (σ i)) l c i)
      (fun i => c.partSize i) (fun i => c.partSize_le i) (sum_partSize c) (fun i k => ?_)
      (fun i => hsmBlock c σ i)
    refine (blockFam_norm_le (fun k => C k (σ i)) l c i k).trans ?_
    exact mul_le_mul_of_nonneg_left (norm_le_pi_norm (C k) (σ i))
      (pow_nonneg (by positivity : (0:ℝ) ≤ 2 * Real.pi * ‖k‖) _)
  -- cardinality of the block choices
  have hcard : ∀ c : OrderedFinpartition s,
      (Fintype.card (Fin c.length → Fin m) : ℝ) ≤ ((m : ℝ) + 1) ^ s := by
    intro c
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, Nat.cast_pow]
    exact (pow_le_pow_left₀ (Nat.cast_nonneg m) (by linarith) c.length).trans
      (pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ (m : ℝ) + 1) c.length_le)
  refine hInt.trans ?_
  rw [hstep]
  have h1 : ∀ c : OrderedFinpartition s,
      M ^ 2 * ∑ σ : Fin c.length → Fin m,
          ∫ x in unitCube, ∏ i, ‖seriesFun (blockFam (fun k => C k (σ i)) l c i) x‖ ^ 2
        ≤ M ^ 2 * (((m : ℝ) + 1) ^ s * (Kprod * (1 + CSq s (fun k => ((‖C k‖ : ℝ) : ℂ))))) := by
    intro c
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg M)
    calc ∑ σ : Fin c.length → Fin m,
          ∫ x in unitCube, ∏ i, ‖seriesFun (blockFam (fun k => C k (σ i)) l c i) x‖ ^ 2
        ≤ ∑ _σ : Fin c.length → Fin m, Kprod * (1 + CSq s (fun k => ((‖C k‖ : ℝ) : ℂ))) :=
          Finset.sum_le_sum fun σ _ => hterm c σ
      _ = (Fintype.card (Fin c.length → Fin m) : ℝ) *
            (Kprod * (1 + CSq s (fun k => ((‖C k‖ : ℝ) : ℂ)))) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ ≤ ((m : ℝ) + 1) ^ s * (Kprod * (1 + CSq s (fun k => ((‖C k‖ : ℝ) : ℂ)))) :=
          mul_le_mul_of_nonneg_right (hcard c)
            (mul_nonneg hKprod (by linarith [CSq_nonneg s (fun k : ι → ℤ => ((‖C k‖ : ℝ) : ℂ))]))
  calc (Fintype.card (OrderedFinpartition s) : ℝ) *
        ∑ c : OrderedFinpartition s, M ^ 2 * ∑ σ : Fin c.length → Fin m,
          ∫ x in unitCube, ∏ i, ‖seriesFun (blockFam (fun k => C k (σ i)) l c i) x‖ ^ 2
      ≤ (Fintype.card (OrderedFinpartition s) : ℝ) *
        ∑ _c : OrderedFinpartition s,
          M ^ 2 * (((m : ℝ) + 1) ^ s * (Kprod * (1 + CSq s (fun k => ((‖C k‖ : ℝ) : ℂ))))) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun c _ => h1 c) (Nat.cast_nonneg _)
    _ = (Fintype.card (OrderedFinpartition s) : ℝ) *
        ((Fintype.card (OrderedFinpartition s) : ℝ) *
          (M ^ 2 * (((m : ℝ) + 1) ^ s * (Kprod * (1 + CSq s (fun k => ((‖C k‖ : ℝ) : ℂ))))))) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = (Fintype.card (OrderedFinpartition s) : ℝ) ^ 2 * M ^ 2 * ((m : ℝ) + 1) ^ s * Kprod *
          (1 + CSq s (fun k => ((‖C k‖ : ℝ) : ℂ))) := by
        ring

theorem CSq_comp_vecarg_le {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}
    (s ρ : ℕ) (hρ : Fintype.card ι < 2 * ρ) (hρs : ρ ≤ s)
    (Φ : (Fin m → ℂ) → ℂ) (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (B : ℝ) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ c : (ι → ℤ) → (Fin m → ℂ),
      (∀ N : ℕ, Summable (fun k : ι → ℤ => (Work.Diff.STE.wt k) ^ N * ‖c k‖)) →
      (∑ i : Fin m, Work.Diff.STE.CSq ρ (fun k : ι → ℤ => c k i)) ≤ B ^ 2 →
      Summable (fun k : ι → ℤ => (Work.Diff.STE.wt k) ^ s *
        ‖Work.Diff.STE.fourierCoeff
          (fun x : ι → ℝ => Φ (fun i : Fin m => Work.Diff.STE.seriesFun (fun k => c k i) x)) k‖ ^ 2) ∧
      Work.Diff.STE.CSq s
          (Work.Diff.STE.fourierCoeff
            (fun x : ι → ℝ => Φ (fun i : Fin m => Work.Diff.STE.seriesFun (fun k => c k i) x)))
        ≤ C * (1 + ∑ i : Fin m, Work.Diff.STE.CSq s (fun k : ι → ℤ => c k i)) := by
  classical
  have hρ0 : 0 < ρ := by omega
  have hs0 : 0 < s := lt_of_lt_of_le hρ0 hρs
  obtain ⟨C_l1, hC_l1nn, hC_l1⟩ := l1_le_sqrt_CSq (ι := ι) ρ hρ
  obtain ⟨C_sup, hC_supnn, hC_sup⟩ := norm_seriesFun_le (ι := ι) ρ hρ
  obtain ⟨C0, hC0nn, hC0⟩ := CSq_le_ENormSq (ι := ι) s
  set Kb : ℝ := (C_sup + C_l1) * B with hKbdef
  have hKbnn : 0 ≤ Kb := by rw [hKbdef]; positivity
  set Λb : ℝ := ((m : ℝ) + 1) * Kb with hΛbdef
  set Kprod : ℝ := ((2 * Real.pi) ^ s * (1 + Λb) ^ s) ^ 2 with hKproddef
  have hKprodn : 0 ≤ Kprod := by rw [hKproddef]; positivity
  obtain ⟨M, hMnn, hM⟩ := phi_derivBound_pi Φ hΦ Kb s
  refine ⟨C0 * ((Fintype.card (Fin s → ι) : ℝ) *
      ((Fintype.card (OrderedFinpartition s) : ℝ) ^ 2 * M ^ 2 * ((m : ℝ) + 1) ^ s * Kprod) + M ^ 2),
    by positivity, ?_⟩
  intro c hmom hCSq
  set V0 : (ι → ℝ) → (Fin m → ℂ) := fun x => fun j => seriesFun (fun k => c k j) x with hV0def
  set γ : (ι → ℤ) → ℂ := fun k => ((‖c k‖ : ℝ) : ℂ) with hγdef
  have hγnorm : ∀ k : ι → ℤ, ‖γ k‖ = ‖c k‖ := fun k => by simp [hγdef]
  have hγmom : ∀ N : ℕ, Summable fun k : ι → ℤ => (wt k) ^ N * ‖γ k‖ := by
    intro N; simpa only [hγnorm] using hmom N
  have hγl1 : Summable fun k : ι → ℤ => ‖γ k‖ := by
    simpa only [hγnorm, pow_zero, one_mul] using hmom 0
  have hγQ : Summable fun k : ι → ℤ => (‖k‖ : ℝ) ^ (2 * s) * ‖γ k‖ ^ 2 := by
    refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
      (summable_wt_pow_mul_norm_sq γ hγmom s)
    rw [hγnorm]
    refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    have h2 : (‖k‖ : ℝ) ^ 2 ≤ wt k := sq_norm_le_wt k
    calc (‖k‖ : ℝ) ^ (2 * s) = ((‖k‖ : ℝ) ^ 2) ^ s := by rw [← pow_mul]
      _ ≤ (wt k) ^ s := pow_le_pow_left₀ (sq_nonneg _) h2 s
  -- componentwise consequences of the hypothesis on the data
  have hCSQj : ∀ j : Fin m, CSq ρ (fun k : ι → ℤ => c k j) ≤ B ^ 2 := by
    intro j
    refine (Finset.single_le_sum (f := fun j : Fin m => CSq ρ (fun k : ι → ℤ => c k j))
      (fun j _ => CSq_nonneg ρ _) (Finset.mem_univ j)).trans hCSq
  have hsqrtj : ∀ j : Fin m, Real.sqrt (CSq ρ (fun k : ι → ℤ => c k j)) ≤ B := fun j =>
    Real.sqrt_le_iff.mpr ⟨hB, hCSQj j⟩
  -- sup bound for the vector of series
  have hsup : ∀ x : ι → ℝ, ‖(fun j : Fin m => seriesFun (fun k => c k j) x)‖ ≤ Kb := by
    intro x
    refine (pi_norm_le_iff_of_nonneg hKbnn).mpr fun j => ?_
    have h1 : ‖seriesFun (fun k => c k j) x‖ ≤ C_sup * B :=
      (hC_sup _ (by simpa using
        summable_wt_pow_mul_norm_sq (fun k => c k j) (summable_moment_component c hmom j) ρ)
        x).trans (mul_le_mul_of_nonneg_left (hsqrtj j) hC_supnn)
    refine h1.trans ?_
    rw [hKbdef]
    exact mul_le_mul_of_nonneg_right (by linarith) hB
  -- the ℓ¹ bound
  have hΛc : (∑' k : ι → ℤ, ‖c k‖) ≤ Λb := by
    have h1 : ∀ k : ι → ℤ, ‖c k‖ ≤ ∑ j : Fin m, ‖c k j‖ := fun k =>
      (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun j _ => norm_nonneg _)).mpr fun j =>
        Finset.single_le_sum (f := fun j => ‖c k j‖) (fun j _ => norm_nonneg _) (Finset.mem_univ j)
    have h2 : Summable fun k : ι → ℤ => ∑ j : Fin m, ‖c k j‖ :=
      summable_sum fun j _ => by simpa using summable_moment_component c hmom j 0
    have h3 : (∑' k : ι → ℤ, ∑ j : Fin m, ‖c k j‖) = ∑ j : Fin m, ∑' k : ι → ℤ, ‖c k j‖ :=
      Summable.tsum_finsetSum (s := Finset.univ) (fun j _ => by
        simpa using summable_moment_component c hmom j 0)
    have h4 : ∀ j : Fin m, (∑' k : ι → ℤ, ‖c k j‖) ≤ C_l1 * B := fun j =>
      (hC_l1 (fun k => c k j) (by simpa using
        summable_wt_pow_mul_norm_sq (fun k => c k j) (summable_moment_component c hmom j) ρ)).trans
        (mul_le_mul_of_nonneg_left (hsqrtj j) hC_l1nn)
    rw [hΛbdef]
    calc (∑' k : ι → ℤ, ‖c k‖) ≤ ∑' k : ι → ℤ, ∑ j : Fin m, ‖c k j‖ :=
          Summable.tsum_le_tsum h1 (by simpa using hmom 0) h2
      _ = ∑ j : Fin m, ∑' k : ι → ℤ, ‖c k j‖ := h3
      _ ≤ ∑ _j : Fin m, C_l1 * B := Finset.sum_le_sum fun j _ => h4 j
      _ = (m : ℝ) * (C_l1 * B) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ ≤ ((m : ℝ) + 1) * ((C_sup + C_l1) * B) := by
          have h5 : (0 : ℝ) ≤ C_l1 * B := mul_nonneg hC_l1nn hB
          have h6 : C_l1 ≤ C_sup + C_l1 := by linarith
          have h7 : C_l1 * B ≤ (C_sup + C_l1) * B := mul_le_mul_of_nonneg_right h6 hB
          calc (m : ℝ) * (C_l1 * B) ≤ (m : ℝ) * ((C_sup + C_l1) * B) :=
                mul_le_mul_of_nonneg_left h7 (by positivity : (0:ℝ) ≤ (m:ℝ))
            _ ≤ ((m : ℝ) + 1) * ((C_sup + C_l1) * B) := by
                have h8 : (m : ℝ) ≤ (m : ℝ) + 1 := by linarith
                have h9 : (0 : ℝ) ≤ (C_sup + C_l1) * B :=
                  mul_nonneg (by linarith [hC_supnn, hC_l1nn]) hB
                exact mul_le_mul_of_nonneg_right h8 h9
  have hγΛ : (∑' k : ι → ℤ, ‖γ k‖) ≤ Λb :=
    (le_of_eq (tsum_congr fun k => hγnorm k)).trans hΛc
  -- the product estimate, in terms of the majorant `γ`
  have hprod : ∀ {r : ℕ} (hr : 1 ≤ r) (hrs : r ≤ s) (d : Fin r → (ι → ℤ) → ℂ) (β : Fin r → ℕ),
      (∀ i, β i ≤ s) → (∑ i, β i = s) →
      (∀ i k, ‖d i k‖ ≤ (2 * Real.pi * ‖k‖) ^ (β i) * ‖c k‖) →
      (∀ i, Summable fun k : ι → ℤ => ‖d i k‖ ^ (yExp s (β i))) →
      ∫ x in unitCube, ‖∏ i, seriesFun (d i) x‖ ^ 2
        ≤ Kprod * (1 + CSq s (fun k => ((‖c k‖ : ℝ) : ℂ))) := by
    intro r hr hrs d β hβ hβsum hd hsm
    have h := Comp3.integral_prod_block_general s hs0 γ hγmom hγl1
      hγQ hr hrs d β hβ hβsum (fun i k => by rw [hγnorm]; exact hd i k) hsm
    have hKc : ((2 * Real.pi) ^ s * (1 + ∑' k : ι → ℤ, ‖γ k‖) ^ s) ^ 2 ≤ Kprod := by
      rw [hKproddef]
      have h1 : (0 : ℝ) ≤ 1 + ∑' k : ι → ℤ, ‖γ k‖ := by
        have h1' : (0 : ℝ) ≤ ∑' k : ι → ℤ, ‖γ k‖ := tsum_nonneg fun k => norm_nonneg (γ k)
        linarith
      have h2 : (1 + ∑' k : ι → ℤ, ‖γ k‖) ≤ 1 + Λb := by linarith [hγΛ]
      exact pow_le_pow_left₀ (by positivity)
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h1 h2 s) (by positivity)) 2
    calc ∫ x in unitCube, ‖∏ i, seriesFun (d i) x‖ ^ 2
        ≤ ((2 * Real.pi) ^ s * (1 + ∑' k : ι → ℤ, ‖γ k‖) ^ s) ^ 2 * (1 + CSq s γ) := h
      _ ≤ Kprod * (1 + CSq s γ) :=
          mul_le_mul_of_nonneg_right hKc (by linarith [CSq_nonneg s γ])
      _ ≤ Kprod * (1 + CSq s (fun k => ((‖c k‖ : ℝ) : ℂ))) := le_of_eq (by simp only [hγdef])
  -- per-derivative estimate
  have hpd : ∀ l : Fin s → ι,
      ∫ x in unitCube, ‖pdVec s l (fun y => Φ (fun j => seriesFun (fun k => c k j) y)) x‖ ^ 2
        ≤ (Fintype.card (OrderedFinpartition s) : ℝ) ^ 2 * M ^ 2 * ((m : ℝ) + 1) ^ s * Kprod *
            (1 + CSq s (fun k => ((‖c k‖ : ℝ) : ℂ))) :=
    fun l => integral_pdVec_comp_le s hs0 Φ hΦ hM hKprodn c hmom hsup hprod l
  have hfd : ContDiff ℝ (↑s) (fun x : ι → ℝ => Φ (fun j => seriesFun (fun k => c k j) x)) :=
    (hΦ.comp (contDiff_seriesFunVec c hmom)).of_le (by simp)
  have hper : Periodic1 (fun x : ι → ℝ => Φ (fun j => seriesFun (fun k => c k j) x)) :=
    fun i x => congrArg Φ (periodic_seriesFunVec c i x)
  -- energy estimates
  have hENs : ENormSq s (fun x : ι → ℝ => Φ (fun j => seriesFun (fun k => c k j) x))
      ≤ (Fintype.card (Fin s → ι) : ℝ) *
          ((Fintype.card (OrderedFinpartition s) : ℝ) ^ 2 * M ^ 2 * ((m : ℝ) + 1) ^ s * Kprod) *
        (1 + CSq s (fun k => ((‖c k‖ : ℝ) : ℂ))) := by
    rw [ENormSq]
    calc ∑ l : Fin s → ι,
          ∫ x in unitCube, ‖pdVec s l (fun y => Φ (fun j => seriesFun (fun k => c k j) y)) x‖ ^ 2
        ≤ ∑ _l : Fin s → ι, (Fintype.card (OrderedFinpartition s) : ℝ) ^ 2 * M ^ 2 *
            ((m : ℝ) + 1) ^ s * Kprod * (1 + CSq s (fun k => ((‖c k‖ : ℝ) : ℂ))) :=
          Finset.sum_le_sum fun l _ => hpd l
      _ = (Fintype.card (Fin s → ι) : ℝ) *
          ((Fintype.card (OrderedFinpartition s) : ℝ) ^ 2 * M ^ 2 * ((m : ℝ) + 1) ^ s * Kprod) *
            (1 + CSq s (fun k => ((‖c k‖ : ℝ) : ℂ))) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          ring
  have hEN0 : ENormSq 0 (fun x : ι → ℝ => Φ (fun j => seriesFun (fun k => c k j) x)) ≤ M ^ 2 := by
    rw [ENormSq_zero]
    have h1 : ∀ x : ι → ℝ, ‖Φ (fun j => seriesFun (fun k => c k j) x)‖ ≤ M :=
      fun x => by simpa only [norm_iteratedFDeriv_zero] using hM _ (hsup x) 0 (Nat.zero_le s)
    have hvol : (volume.restrict unitCube : Measure (ι → ℝ)).real Set.univ = 1 := by
      show ((volume.restrict unitCube : Measure (ι → ℝ)) Set.univ).toReal = 1
      rw [MeasureTheory.Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, unitCube,
        Real.volume_pi_Ioc]
      simp
    calc ∫ x in unitCube, ‖Φ (fun j => seriesFun (fun k => c k j) x)‖ ^ 2
        ≤ ∫ _x in unitCube, M ^ 2 :=
          MeasureTheory.integral_mono_ae
            (el_integrableOn_unitCube_of_continuous_real (hfd.continuous.norm.pow 2))
            (el_integrableOn_unitCube_of_continuous_real continuous_const)
            (Filter.Eventually.of_forall fun x => pow_le_pow_left₀ (norm_nonneg _) (h1 x) 2)
      _ = M ^ 2 := by rw [MeasureTheory.integral_const, smul_eq_mul, hvol, one_mul]
  -- the sum bound
  have hCSQsum : CSq s (fun k => ((‖c k‖ : ℝ) : ℂ)) ≤
      ∑ i : Fin m, CSq s (fun k : ι → ℤ => c k i) := by
    have hpt : ∀ k : ι → ℤ, (wt k) ^ s * ‖((‖c k‖ : ℝ) : ℂ)‖ ^ 2 ≤
        ∑ i : Fin m, (wt k) ^ s * ‖c k i‖ ^ 2 := by
      intro k
      have hcn : ‖((‖c k‖ : ℝ) : ℂ)‖ = ‖c k‖ := by simp
      rw [hcn, ← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (pi_norm_sq_le_sum_norm_sq (c k))
        (pow_nonneg (le_of_lt (wt_pos k)) s)
    have hsumm : Summable fun k : ι → ℤ => ∑ i : Fin m, (wt k) ^ s * ‖c k i‖ ^ 2 :=
      summable_sum fun i _ => summable_wt_pow_mul_norm_sq (fun k => c k i)
        (summable_moment_component c hmom i) s
    calc CSq s (fun k => ((‖c k‖ : ℝ) : ℂ))
        = ∑' k : ι → ℤ, (wt k) ^ s * ‖((‖c k‖ : ℝ) : ℂ)‖ ^ 2 := rfl
      _ ≤ ∑' k : ι → ℤ, ∑ i : Fin m, (wt k) ^ s * ‖c k i‖ ^ 2 :=
          Summable.tsum_le_tsum hpt
            (summable_wt_pow_mul_norm_sq _ (fun N => by
              simpa only [hγdef] using hγmom N) s) hsumm
      _ = ∑ i : Fin m, ∑' k : ι → ℤ, (wt k) ^ s * ‖c k i‖ ^ 2 :=
          Summable.tsum_finsetSum (s := Finset.univ) (fun i _ =>
            summable_wt_pow_mul_norm_sq (fun k => c k i) (summable_moment_component c hmom i) s)
      _ = ∑ i : Fin m, CSq s (fun k : ι → ℤ => c k i) := rfl
  refine ⟨Comp.summable_wt_fourierCoeff s _ hfd hper, ?_⟩
  have hCbignn : 0 ≤ C0 * ((Fintype.card (Fin s → ι) : ℝ) *
      ((Fintype.card (OrderedFinpartition s) : ℝ) ^ 2 * M ^ 2 * ((m : ℝ) + 1) ^ s * Kprod) + M ^ 2) :=
    mul_nonneg hC0nn (by positivity)
  have hCSQnn : 0 ≤ 1 + CSq s (fun k => ((‖c k‖ : ℝ) : ℂ)) := by
    have := CSq_nonneg s (fun k => ((‖c k‖ : ℝ) : ℂ)); linarith
  calc CSq s (fourierCoeff (fun x : ι → ℝ => Φ (fun j => seriesFun (fun k => c k j) x)))
      ≤ C0 * (ENormSq s (fun x : ι → ℝ => Φ (fun j => seriesFun (fun k => c k j) x))
          + ENormSq 0 (fun x : ι → ℝ => Φ (fun j => seriesFun (fun k => c k j) x))) :=
        hC0 _ hfd hper
    _ ≤ C0 * ((Fintype.card (Fin s → ι) : ℝ) *
          ((Fintype.card (OrderedFinpartition s) : ℝ) ^ 2 * M ^ 2 * ((m : ℝ) + 1) ^ s * Kprod) *
            (1 + CSq s (fun k => ((‖c k‖ : ℝ) : ℂ))) + M ^ 2) :=
        mul_le_mul_of_nonneg_left (add_le_add hENs hEN0) hC0nn
    _ ≤ C0 * ((Fintype.card (Fin s → ι) : ℝ) *
          ((Fintype.card (OrderedFinpartition s) : ℝ) ^ 2 * M ^ 2 * ((m : ℝ) + 1) ^ s * Kprod) + M ^ 2)
          * (1 + CSq s (fun k => ((‖c k‖ : ℝ) : ℂ))) := by
        have hA : 0 ≤ (Fintype.card (Fin s → ι) : ℝ) *
            ((Fintype.card (OrderedFinpartition s) : ℝ) ^ 2 * M ^ 2 * ((m : ℝ) + 1) ^ s * Kprod) := by
          have hM2 : (0 : ℝ) ≤ M ^ 2 := sq_nonneg M
          have hm2 : (0 : ℝ) ≤ (m : ℝ) + 1 := by positivity
          have hc : (0 : ℝ) ≤ (Fintype.card (OrderedFinpartition s) : ℝ) ^ 2 := sq_nonneg _
          have hA1 : (0 : ℝ) ≤ (Fintype.card (OrderedFinpartition s) : ℝ) ^ 2 * M ^ 2 :=
            mul_nonneg hc hM2
          have hA2 : (0 : ℝ) ≤ ((m : ℝ) + 1) ^ s := pow_nonneg hm2 s
          exact mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (mul_nonneg hA1 hA2) hKprodn)
        have hQnn : 0 ≤ CSq s (fun k : ι → ℤ => ((‖c k‖ : ℝ) : ℂ)) := CSq_nonneg s _
        have hkey : (Fintype.card (Fin s → ι) : ℝ) *
              ((Fintype.card (OrderedFinpartition s) : ℝ) ^ 2 * M ^ 2 * ((m : ℝ) + 1) ^ s * Kprod) *
                (1 + CSq s (fun k => ((‖c k‖ : ℝ) : ℂ))) + M ^ 2
            ≤ ((Fintype.card (Fin s → ι) : ℝ) *
              ((Fintype.card (OrderedFinpartition s) : ℝ) ^ 2 * M ^ 2 * ((m : ℝ) + 1) ^ s * Kprod) + M ^ 2)
              * (1 + CSq s (fun k => ((‖c k‖ : ℝ) : ℂ))) := by
          nlinarith [sq_nonneg M, hQnn, hA, hMnn]
        calc C0 * ((Fintype.card (Fin s → ι) : ℝ) *
              ((Fintype.card (OrderedFinpartition s) : ℝ) ^ 2 * M ^ 2 * ((m : ℝ) + 1) ^ s * Kprod) *
                (1 + CSq s (fun k => ((‖c k‖ : ℝ) : ℂ))) + M ^ 2)
            ≤ C0 * (((Fintype.card (Fin s → ι) : ℝ) *
              ((Fintype.card (OrderedFinpartition s) : ℝ) ^ 2 * M ^ 2 * ((m : ℝ) + 1) ^ s * Kprod) + M ^ 2)
              * (1 + CSq s (fun k => ((‖c k‖ : ℝ) : ℂ)))) :=
              mul_le_mul_of_nonneg_left hkey hC0nn
          _ = C0 * ((Fintype.card (Fin s → ι) : ℝ) *
              ((Fintype.card (OrderedFinpartition s) : ℝ) ^ 2 * M ^ 2 * ((m : ℝ) + 1) ^ s * Kprod) + M ^ 2)
              * (1 + CSq s (fun k => ((‖c k‖ : ℝ) : ℂ))) := by ring
    _ ≤ C0 * ((Fintype.card (Fin s → ι) : ℝ) *
          ((Fintype.card (OrderedFinpartition s) : ℝ) ^ 2 * M ^ 2 * ((m : ℝ) + 1) ^ s * Kprod) + M ^ 2)
          * (1 + ∑ i : Fin m, CSq s (fun k : ι → ℤ => c k i)) := by
        refine mul_le_mul_of_nonneg_left ?_ hCbignn
        linarith [hCSQsum, hCSQnn]

end Work.Diff.STE
