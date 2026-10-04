import Mathlib
import Submission.Work.Diff.EXT.ufslice
import Submission.Work.Diff.EXT.JetConv.slice_jet_comp_inr
import Submission.Work.Diff.EXT.JetConv.tDer_jets_eq_Phi
import Submission.Work.Diff.EXT.JetConv.tDer_smooth
import Submission.Work.Diff.EXT.JetGap.exists_tendsto_of_hasDerivAt_uniform_bound
import Submission.Work.Diff.EXT.JetConv.norm_iteratedFDeriv_Phi_v2
import Submission.Work.Diff.EXT.JetGap.contDiffOn_of_tendstoUniformlyOn_iteratedFDeriv
import Submission.Work.Diff.EXT.borel_jet_on
import Submission.Work.Diff.EXT.heaviside_cut_smooth_at_seam

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.EXT

open Filter Set
open scoped Topology ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]

/-! ## The `k`-th time derivative of a function on `ℝ × E` -/

/-- The `k`-th iterated time derivative of `u : ℝ × E → Z`, as an evaluation of its `k`-th full
jet. -/
private noncomputable def slicePhi (u : ℝ × E → Z) (k : ℕ) : ℝ × E → Z :=
  fun q => (iteratedFDeriv ℝ k u q) (fun _ : Fin k => ((1 : ℝ), 0))

private lemma slicePhi_contDiffOn {u : ℝ × E → Z} {V : Set (ℝ × E)} (hV : IsOpen V)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) u V) (k : ℕ) : ContDiffOn ℝ (⊤ : ℕ∞) (slicePhi u k) V := by
  rw [hV.contDiffOn_iff]
  intro p hp
  have hjet : ContDiffAt ℝ (⊤ : ℕ∞) (fun q => iteratedFDeriv ℝ k u q) p :=
    (hu.contDiffAt (hV.mem_nhds hp)).iteratedFDeriv_right (i := k) (by simp)
  have h := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => ℝ × E) Z
      (fun _ => ((1 : ℝ), 0))).contDiff.contDiffAt.comp p hjet
  have hφ : slicePhi u k = (ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => ℝ × E) Z
      (fun _ => ((1 : ℝ), 0))) ∘ (fun q => iteratedFDeriv ℝ k u q) := by
    funext q
    simp [slicePhi, ContinuousMultilinearMap.apply_apply]
  rw [hφ]; exact h

/-- The `m`-th full jet of the `k`-th time derivative of `u`. -/
private noncomputable def sliceDPhi (u : ℝ × E → Z) (k m : ℕ) :
    ℝ × E → ContinuousMultilinearMap ℝ (fun _ : Fin m => ℝ × E) Z :=
  fun p => iteratedFDeriv ℝ m (slicePhi u k) p


private lemma slicePhi_apply (u : ℝ × E → Z) (k : ℕ) (q : ℝ × E) :
    slicePhi u k q = (iteratedFDeriv ℝ k u q) (fun _ : Fin k => ((1 : ℝ), 0)) := rfl

private lemma sliceDPhi_apply (u : ℝ × E → Z) (k m : ℕ) (p : ℝ × E) :
    sliceDPhi u k m p
      = iteratedFDeriv ℝ m
          (fun q : ℝ × E => (iteratedFDeriv ℝ k u q) (fun _ : Fin k => ((1 : ℝ), 0))) p := rfl

/-- Restriction of a continuous multilinear map on `ℝ × E` to the `E`-directions. -/
private noncomputable def sliceRestr (m : ℕ) :
    ContinuousMultilinearMap ℝ (fun _ : Fin m => ℝ × E) Z →L[ℝ]
      ContinuousMultilinearMap ℝ (fun _ : Fin m => E) Z :=
  ContinuousMultilinearMap.compContinuousLinearMapL (fun _ : Fin m => ContinuousLinearMap.inr ℝ ℝ E)

open scoped Classical in
/-- **The spatial jets of the `t`-derivatives of a function with uniformly bounded ambient jets
converge at the endpoint.**  If `u : ℝ × E → Z` is `C^∞` on `(Ico σ T) ×ˢ U` and every ambient
iterated Fréchet derivative of `u` there is bounded by a constant depending only on its order, then
near any `y₀ ∈ U` there is a smaller open neighbourhood `U'` and a sequence of `C^∞` functions
`f k : E → Z` such that for every `k, m` and every `y ∈ U'` the mixed jet `∂_y^m ∂_t^k u` tends to
`∂^m (f k)` as `p → (T, y)` from the left. -/
theorem slice_jets_converge
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace Z]
    {σ T : ℝ} (hσT : σ < T) {U : Set E} (hU : IsOpen U) {u : ℝ × E → Z}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) u ((Set.Ico σ T) ×ˢ U))
    (hb : ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ (Set.Ico σ T) ×ˢ U,
        ‖iteratedFDeriv ℝ k u p‖ ≤ C)
    {y₀ : E} (hy₀ : y₀ ∈ U) :
    ∃ U' : Set E, IsOpen U' ∧ y₀ ∈ U' ∧ U' ⊆ U ∧ ∃ f : ℕ → E → Z,
      (∀ k, ContDiffOn ℝ (⊤ : ℕ∞) (f k) U') ∧
      (∀ k m : ℕ, ∀ y ∈ U', Filter.Tendsto (fun p : ℝ × E =>
          iteratedFDeriv ℝ m (fun y' : E => iteratedDeriv k (fun s : ℝ => u (s, y')) p.1) p.2
            - iteratedFDeriv ℝ m (f k) p.2)
          (nhdsWithin (T, y) ({p : ℝ × E | p.1 < T} ∩ (Set.univ ×ˢ U'))) (nhds 0)) := by
  classical
  have hOmopen : IsOpen (Set.Ioo σ T ×ˢ U) := isOpen_Ioo.prod hU
  have hsub : Set.Ioo σ T ×ˢ U ⊆ (Set.Ico σ T) ×ˢ U := by
    rintro ⟨t, y⟩ ⟨ht, hy⟩
    exact ⟨⟨le_of_lt ht.1, ht.2⟩, hy⟩
  have huOm : ContDiffOn ℝ (⊤ : ℕ∞) u (Set.Ioo σ T ×ˢ U) := hu.mono hsub
  have hbOm : ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ Set.Ioo σ T ×ˢ U,
      ‖iteratedFDeriv ℝ k u p‖ ≤ C := by
    intro k
    obtain ⟨C, hC, h⟩ := hb k
    exact ⟨C, hC, fun p hp => h p (hsub hp)⟩
  have hphiOm : ∀ k, ContDiffOn ℝ (⊤ : ℕ∞) (slicePhi u k) (Set.Ioo σ T ×ˢ U) :=
    fun k => slicePhi_contDiffOn hOmopen huOm k
  have htderOm : ∀ k, ContDiffOn ℝ (⊤ : ℕ∞)
      (fun q : ℝ × E => iteratedDeriv k (fun s : ℝ => u (s, q.2)) q.1) (Set.Ioo σ T ×ˢ U) :=
    fun k => Work.Diff.EXT.JetConv.tDer_smooth hOmopen huOm k
  have hIoo_mem : Set.Ioo σ T ∈ nhdsWithin T (Set.Iio T) := by
    have h1 : Set.Ioi σ ∈ nhdsWithin T (Set.Iio T) :=
      nhdsWithin_le_nhds (isOpen_Ioi.mem_nhds hσT)
    have h2 : Set.Iio T ∈ nhdsWithin T (Set.Iio T) := self_mem_nhdsWithin
    have h3 := inter_mem h1 h2
    rwa [show Set.Ioi σ ∩ Set.Iio T = Set.Ioo σ T from rfl] at h3
  have hbound : ∀ k m : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ Set.Ioo σ T ×ˢ U,
      ‖sliceDPhi u k m p‖ ≤ C := by
    intro k m
    obtain ⟨C1, hC1, h1⟩ := Work.Diff.EXT.JetConv.norm_iteratedFDeriv_Phi_v2 (E := E) k m
    obtain ⟨C2, hC2, h2⟩ := hbOm (k + m)
    refine ⟨C1 * C2, mul_nonneg hC1 hC2, fun p hp => ?_⟩
    have hp' : ContDiffAt ℝ (⊤ : ℕ∞) u p := huOm.contDiffAt (hOmopen.mem_nhds hp)
    rw [sliceDPhi_apply]
    exact le_trans (h1 u p hp') (mul_le_mul_of_nonneg_left (h2 p hp) hC1)
  have hlim : ∀ k m : ℕ, ∃ (L : E → ContinuousMultilinearMap ℝ (fun _ : Fin m => ℝ × E) Z)
      (C : ℝ), 0 ≤ C ∧
      (∀ y ∈ U, Tendsto (fun t => sliceDPhi u k m (t, y)) (nhdsWithin T (Set.Iio T)) (nhds (L y))) ∧
      (∀ t ∈ Set.Ioo σ T, ∀ y ∈ U, ‖sliceDPhi u k m (t, y) - L y‖ ≤ C * (T - t)) := by
    intro k m
    obtain ⟨C, hC, hCb⟩ := hbound k (m + 1)
    have hex : ∃ L : E → ContinuousMultilinearMap ℝ (fun _ : Fin m => ℝ × E) Z,
        (∀ y ∈ U, Tendsto (fun t => sliceDPhi u k m (t, y)) (nhdsWithin T (Set.Iio T))
          (nhds (L y))) ∧
        (∀ t ∈ Set.Ioo σ T, ∀ y ∈ U, ‖sliceDPhi u k m (t, y) - L y‖ ≤ C * (T - t)) := by
      refine Work.Diff.EXT.JetGap.exists_tendsto_of_hasDerivAt_uniform_bound
        (β := ContinuousMultilinearMap ℝ (fun _ : Fin m => ℝ × E) Z)
        (σ := σ) (T := T) hσT (U := U)
        (F := fun y t => sliceDPhi u k m (t, y))
        (F' := fun t y => (fderiv ℝ (sliceDPhi u k m) (t, y)) (1, 0)) (C := C) ?_ ?_
      · intro t ht y hy
        have hpt : (t, y) ∈ Set.Ioo σ T ×ˢ U := ⟨ht, hy⟩
        have hcd : ContDiffAt ℝ (⊤ : ℕ∞) (sliceDPhi u k m) (t, y) :=
          ((hphiOm k).contDiffAt (hOmopen.mem_nhds hpt)).iteratedFDeriv_right (i := m)
            (by simp)
        have hfd : HasFDerivAt (sliceDPhi u k m) (fderiv ℝ (sliceDPhi u k m) (t, y)) (t, y) :=
          (hcd.differentiableAt (by simp)).hasFDerivAt
        have hcomp := hfd.comp_hasDerivAt t ((hasFDerivAt_prodMk_left (𝕜 := ℝ) t y).hasDerivAt)
        have hdg : (ContinuousLinearMap.inl ℝ ℝ E) (1 : ℝ) = (((1 : ℝ), (0 : E)) : ℝ × E) := by
          rw [ContinuousLinearMap.inl_apply]
        rw [hdg] at hcomp
        exact hcomp
      · intro t ht y hy
        have hpt : (t, y) ∈ Set.Ioo σ T ×ˢ U := ⟨ht, hy⟩
        calc ‖(fderiv ℝ (sliceDPhi u k m) (t, y)) (1, 0)‖
            ≤ ‖fderiv ℝ (sliceDPhi u k m) (t, y)‖ * ‖(((1 : ℝ), (0 : E)) : ℝ × E)‖ :=
              ContinuousLinearMap.le_opNorm _ _
          _ = ‖fderiv ℝ (sliceDPhi u k m) (t, y)‖ := by
              rw [Prod.norm_def, norm_one, norm_zero, max_eq_left zero_le_one, mul_one]
          _ = ‖sliceDPhi u k (m + 1) (t, y)‖ := norm_fderiv_iteratedFDeriv
          _ ≤ C := hCb (t, y) hpt
    obtain ⟨L, hLt, hLb⟩ := hex
    exact ⟨L, C, hC, hLt, hLb⟩
  let Lam : (k m : ℕ) → E → ContinuousMultilinearMap ℝ (fun _ : Fin m => ℝ × E) Z :=
    fun k m => Classical.choose (hlim k m)
  let Clam : ℕ → ℕ → ℝ := fun k m => Classical.choose (Classical.choose_spec (hlim k m))
  have hClam : ∀ k m, 0 ≤ Clam k m :=
    fun k m => (Classical.choose_spec (Classical.choose_spec (hlim k m))).1
  have hLamtend : ∀ k m y, y ∈ U →
      Tendsto (fun t => sliceDPhi u k m (t, y)) (nhdsWithin T (Set.Iio T)) (nhds (Lam k m y)) :=
    fun k m y hy => (Classical.choose_spec (Classical.choose_spec (hlim k m))).2.1 y hy
  have hLambd : ∀ k m t, t ∈ Set.Ioo σ T → ∀ y ∈ U,
      ‖sliceDPhi u k m (t, y) - Lam k m y‖ ≤ Clam k m * (T - t) :=
    fun k m t ht y hy => (Classical.choose_spec (Classical.choose_spec (hlim k m))).2.2 t ht y hy
  have hrestr_le : ∀ (m : ℕ) (A : ContinuousMultilinearMap ℝ (fun _ : Fin m => ℝ × E) Z),
      ‖sliceRestr m A‖ ≤ ‖A‖ := by
    intro m A
    refine ContinuousMultilinearMap.opNorm_le_bound (norm_nonneg _) (fun v => ?_)
    rw [sliceRestr, ContinuousMultilinearMap.compContinuousLinearMapL_apply,
      ContinuousMultilinearMap.compContinuousLinearMap_apply]
    refine le_trans (ContinuousMultilinearMap.le_opNorm A _)
      (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
    refine le_of_eq (Finset.prod_congr rfl (fun i _ => ?_))
    rw [ContinuousLinearMap.inr_apply, Prod.norm_def, norm_zero,
      max_eq_right (norm_nonneg (v i))]
  let f : ℕ → E → Z := fun k y => (Lam k 0 y) Fin.elim0
  have hf_tend : ∀ k y, y ∈ U →
      Tendsto (fun t => slicePhi u k (t, y)) (nhdsWithin T (Set.Iio T)) (nhds (f k y)) := by
    intro k y hy
    have h1 : Tendsto (fun t => sliceDPhi u k 0 (t, y)) (nhdsWithin T (Set.Iio T))
        (nhds (Lam k 0 y)) := hLamtend k 0 y hy
    have hcont : Continuous (fun T : ContinuousMultilinearMap ℝ (fun _ : Fin 0 => ℝ × E) Z =>
        T Fin.elim0) :=
      (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 0 => ℝ × E) Z Fin.elim0).continuous
    have h2 : Tendsto (fun t => (sliceDPhi u k 0 (t, y)) Fin.elim0) (nhdsWithin T (Set.Iio T))
        (nhds ((Lam k 0 y) Fin.elim0)) := (hcont.tendsto (Lam k 0 y)).comp h1
    refine h2.congr' ?_
    filter_upwards with t
    simp [sliceDPhi_apply, slicePhi_apply]
  have hsmooth : ∀ k t, ContDiffOn ℝ (⊤ : ℕ∞)
      (fun y : E => if t ∈ Set.Ioo σ T then slicePhi u k (t, y) else (0 : Z)) U := by
    intro k t
    by_cases ht : t ∈ Set.Ioo σ T
    · have h1 : (fun y : E => (if t ∈ Set.Ioo σ T then slicePhi u k (t, y) else (0 : Z)))
          = fun y : E => slicePhi u k (t, y) := by funext y; simp [ht]
      rw [h1, IsOpen.contDiffOn_iff hU]
      intro y hy
      exact ((hphiOm k).contDiffAt (hOmopen.mem_nhds ⟨ht, hy⟩)).comp y
        ((contDiffAt_const (c := t)).prodMk contDiffAt_id)
    · have h1 : (fun y : E => (if t ∈ Set.Ioo σ T then slicePhi u k (t, y) else (0 : Z)))
          = fun _ : E => (0 : Z) := by funext y; simp [ht]
      rw [h1]; exact contDiffOn_const
  have hm : ∀ k m, 1 ≤ m → TendstoUniformlyOn
      (fun t x => iteratedFDeriv ℝ m
        (fun y : E => if t ∈ Set.Ioo σ T then slicePhi u k (t, y) else (0 : Z)) x)
      (fun x => sliceRestr m (Lam k m x)) (nhdsWithin T (Set.Iio T)) U := by
    intro k m _
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have hCl := hClam k m
    have hpos : (0 : ℝ) < Clam k m + 1 := by linarith
    have hsmall : {t : ℝ | Clam k m * (T - t) < ε} ∈ nhdsWithin T (Set.Iio T) := by
      have hmem : Set.Ioi (T - ε / (Clam k m + 1)) ∈ nhds T :=
        isOpen_Ioi.mem_nhds (by
          have h4 : 0 < ε / (Clam k m + 1) := div_pos hε hpos
          show T - ε / (Clam k m + 1) < T
          linarith)
      have h3 : Set.Ioi (T - ε / (Clam k m + 1)) ∈ nhdsWithin T (Set.Iio T) :=
        nhdsWithin_le_nhds hmem
      refine mem_of_superset h3 (fun t ht => ?_)
      have h5 : T - t < ε / (Clam k m + 1) := by
        have : T - ε / (Clam k m + 1) < t := ht
        linarith
      have h6 : Clam k m * (T - t) ≤ Clam k m * (ε / (Clam k m + 1)) :=
        mul_le_mul_of_nonneg_left (le_of_lt h5) hCl
      have h8 : Clam k m * (ε / (Clam k m + 1)) < ε := by
        have h9 : Clam k m * (ε / (Clam k m + 1)) < (Clam k m + 1) * (ε / (Clam k m + 1)) :=
          mul_lt_mul_of_pos_right (by linarith) (div_pos hε hpos)
        have h10 : (Clam k m + 1) * (ε / (Clam k m + 1)) = ε := by
          rw [mul_comm, div_mul_cancel₀ _ (ne_of_gt hpos)]
        linarith
      exact lt_of_le_of_lt h6 h8
    filter_upwards [hIoo_mem, hsmall] with t htI htS
    intro x hx
    have hpt : (t, x) ∈ Set.Ioo σ T ×ˢ U := ⟨htI, hx⟩
    have h1 : (fun y : E => (if t ∈ Set.Ioo σ T then slicePhi u k (t, y) else (0 : Z)))
        = fun y : E => slicePhi u k (t, y) := by funext y; simp [htI]
    have h2 : (iteratedFDeriv ℝ m (slicePhi u k) (t, x)).compContinuousLinearMap
        (fun _ : Fin m => ContinuousLinearMap.inr ℝ ℝ E) = sliceRestr m (sliceDPhi u k m (t, x)) := by
      rw [sliceRestr, ContinuousMultilinearMap.compContinuousLinearMapL_apply]
      rfl
    have hmap : (sliceRestr m) (sliceDPhi u k m (t, x)) - (sliceRestr m) (Lam k m x)
        = (sliceRestr m) (sliceDPhi u k m (t, x) - Lam k m x) := map_sub (sliceRestr m) _ _
    rw [h1, Work.Diff.EXT.JetConv.slice_jet_comp_inr hOmopen (hphiOm k) hpt m, h2,
      dist_comm, dist_eq_norm, hmap]
    exact lt_of_le_of_lt (le_trans (hrestr_le m _) (hLambd k m t htI x hx)) htS
  have hmain : ∀ k, ContDiffOn ℝ (⊤ : ℕ∞) (f k) U ∧
      ∀ m, 1 ≤ m → ∀ x ∈ U, iteratedFDeriv ℝ m (f k) x = sliceRestr m (Lam k m x) := by
    intro k
    have h0 : ∀ x ∈ U, Tendsto
        (fun t => (if t ∈ Set.Ioo σ T then slicePhi u k (t, x) else (0 : Z)))
        (nhdsWithin T (Set.Iio T)) (nhds (f k x)) := by
      intro x hx
      refine (hf_tend k x hx).congr' ?_
      filter_upwards [hIoo_mem] with t ht
      simp [ht]
    exact Work.Diff.EXT.JetGap.contDiffOn_of_tendstoUniformlyOn_iteratedFDeriv hU
      (fun t x => if t ∈ Set.Ioo σ T then slicePhi u k (t, x) else (0 : Z)) (f k)
      (fun m x => sliceRestr m (Lam k m x)) (hsmooth k) h0 (hm k)
  have hjet_f : ∀ k m, ∀ x ∈ U, iteratedFDeriv ℝ m (f k) x = sliceRestr m (Lam k m x) := by
    intro k m
    induction m with
    | zero =>
      intro x _
      refine ContinuousMultilinearMap.ext (fun v => ?_)
      rw [sliceRestr, ContinuousMultilinearMap.compContinuousLinearMapL_apply,
        ContinuousMultilinearMap.compContinuousLinearMap_apply, iteratedFDeriv_zero_apply]
      have harg : (fun i : Fin 0 => (ContinuousLinearMap.inr ℝ ℝ E) (v i)) = Fin.elim0 := by
        funext i; exact i.elim0
      rw [harg]
    | succ m _ =>
      exact fun x hx => (hmain k).2 (m + 1) (Nat.le_add_left 1 m) x hx
  have hkey_aux : ∀ (k m : ℕ) (t : ℝ) (x : E), (t, x) ∈ Set.Ioo σ T ×ˢ U →
      ‖iteratedFDeriv ℝ m (fun y' : E => iteratedDeriv k (fun s : ℝ => u (s, y')) t) x
          - iteratedFDeriv ℝ m (f k) x‖
        ≤ Clam k m * (T - t) := by
    intro k m t x hpt
    have ht : t ∈ Set.Ioo σ T := hpt.1
    have hx : x ∈ U := hpt.2
    have h1 : iteratedFDeriv ℝ m (fun y' : E => iteratedDeriv k (fun s : ℝ => u (s, y')) t) x
        = sliceRestr m (sliceDPhi u k m (t, x)) := by
      rw [Work.Diff.EXT.JetConv.slice_jet_comp_inr hOmopen (htderOm k) hpt m,
        Work.Diff.EXT.JetConv.tDer_jets_eq_Phi hOmopen huOm hpt m k,
        sliceRestr, ContinuousMultilinearMap.compContinuousLinearMapL_apply]
      rfl
    have hmap : (sliceRestr m) (sliceDPhi u k m (t, x)) - (sliceRestr m) (Lam k m x)
        = (sliceRestr m) (sliceDPhi u k m (t, x) - Lam k m x) := map_sub (sliceRestr m) _ _
    rw [h1, hjet_f k m x hx, hmap]
    exact le_trans (hrestr_le m _) (hLambd k m t ht x hx)
  refine ⟨U, hU, hy₀, Subset.rfl, f, fun k => (hmain k).1, ?_⟩
  intro k m y hy
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hU_mem : Set.univ ×ˢ U
      ∈ nhdsWithin (T, y) ({p : ℝ × E | p.1 < T} ∩ (Set.univ ×ˢ U)) :=
    mem_of_superset self_mem_nhdsWithin (fun p hp => hp.2)
  have hσ_mem : {p : ℝ × E | σ < p.1}
      ∈ nhdsWithin (T, y) ({p : ℝ × E | p.1 < T} ∩ (Set.univ ×ˢ U)) :=
    nhdsWithin_le_nhds
      ((isOpen_lt continuous_const continuous_fst).mem_nhds (show σ < (T, y).1 from hσT))
  have hε_mem : {p : ℝ × E | Clam k m * (T - p.1) < ε}
      ∈ nhdsWithin (T, y) ({p : ℝ × E | p.1 < T} ∩ (Set.univ ×ˢ U)) :=
    nhdsWithin_le_nhds
      ((isOpen_lt (continuous_const.mul (continuous_const.sub continuous_fst))
        continuous_const).mem_nhds (by simpa using hε))
  filter_upwards [self_mem_nhdsWithin, hU_mem, hσ_mem, hε_mem] with p hS hpU hpσ hpε
  have hpt : (p.1, p.2) ∈ Set.Ioo σ T ×ˢ U := ⟨⟨hpσ, hS.1⟩, hpU.2⟩
  rw [dist_eq_norm, sub_zero]
  exact lt_of_le_of_lt (hkey_aux k m p.1 p.2 hpt) hpε

/-! ## Mixed jets: `∂_y^m ∂_t^k G` -/

/-- The `m`-th spatial jet of the `k`-th time derivative of `G`, i.e. the mixed jet `∂_y^m ∂_t^k G`
at `p`.  (Its value at `p` is a continuous multilinear map on `E^m`.) -/
@[reducible] noncomputable def pat (k m : ℕ) (G : ℝ × E → Z) (p : ℝ × E) :
    ContinuousMultilinearMap ℝ (fun _ : Fin m => E) Z :=
  iteratedFDeriv ℝ m (fun y' : E => iteratedDeriv k (fun s : ℝ => G (s, y')) p.1) p.2

/-- Iterated Fréchet derivatives do not change if the function is changed on the complement of an
open set containing the base point. -/
private lemma iteratedFDeriv_congr_open {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f g : E → F} {V : Set E} (hV : IsOpen V) (h : ∀ q ∈ V, f q = g q) {p : E} (hp : p ∈ V)
    (m : ℕ) : iteratedFDeriv ℝ m f p = iteratedFDeriv ℝ m g p := by
  rw [← iteratedFDerivWithin_of_isOpen m hV hp,
    iteratedFDerivWithin_congr (fun q hq => h q hq) hp,
    iteratedFDerivWithin_of_isOpen m hV hp]

/-- The `k`-th time derivative of a function does not change if the function is changed on the
complement of an open set containing the base point. -/
private lemma iteratedDeriv_congr_open {f g : ℝ × E → Z} {V : Set (ℝ × E)} (hV : IsOpen V)
    (h : ∀ q ∈ V, f q = g q) {p : ℝ × E} (hp : p ∈ V) (k : ℕ) :
    iteratedDeriv k (fun s : ℝ => f (s, p.2)) p.1
      = iteratedDeriv k (fun s : ℝ => g (s, p.2)) p.1 := by
  have hV' : IsOpen {s : ℝ | (s, p.2) ∈ V} :=
    hV.preimage (continuous_id.prodMk continuous_const)
  have hp' : p.1 ∈ {s : ℝ | (s, p.2) ∈ V} := hp
  have heq : ∀ s ∈ {s : ℝ | (s, p.2) ∈ V}, f (s, p.2) = g (s, p.2) :=
    fun s hs => h (s, p.2) hs
  rw [iteratedDeriv_eq_iteratedFDeriv, iteratedDeriv_eq_iteratedFDeriv]
  exact congrArg (fun T => T (fun _ : Fin k => (1 : ℝ)))
    (iteratedFDeriv_congr_open hV' heq hp' k)

/-- The mixed jets `∂_y^m ∂_t^k G` do not change if `G` is changed on the complement of an open set
containing the base point. -/
private lemma pat_congr {V : Set (ℝ × E)} (hV : IsOpen V) {f g : ℝ × E → Z}
    (h : ∀ q ∈ V, f q = g q) {p : ℝ × E} (hp : p ∈ V) (k m : ℕ) : pat k m f p = pat k m g p := by
  have hVp : IsOpen {y' : E | (p.1, y') ∈ V} :=
    hV.preimage (continuous_const.prodMk continuous_id)
  have hpp : p.2 ∈ {y' : E | (p.1, y') ∈ V} := hp
  have heq : ∀ y' ∈ {y' : E | (p.1, y') ∈ V},
      iteratedDeriv k (fun s : ℝ => f (s, y')) p.1
        = iteratedDeriv k (fun s : ℝ => g (s, y')) p.1 :=
    fun y' hy' => iteratedDeriv_congr_open hV h hy' k
  exact iteratedFDeriv_congr_open hVp heq hpp m

/-- The linear map `(a, b) ↦ a - b`. -/
private def subCLM (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F] : F × F →L[ℝ] F :=
  (ContinuousLinearMap.fst ℝ F F) - (ContinuousLinearMap.snd ℝ F F)

private lemma subCLM_apply (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F] (a b : F) :
    subCLM F (a, b) = a - b := rfl

/-- **Linearity of the iterated Fréchet derivative in the function**, at a point where the
functions are `C^i`.  (Mathlib's `iteratedFDeriv_sub` requires *global* smoothness; this local
version is obtained by writing the difference as a continuous linear map applied to the pair.) -/
private lemma iteratedFDeriv_sub_of_contDiffAt {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f g : E → F} {x : E} (i : ℕ) (hf : ContDiffAt ℝ (i : ℕ∞ω) f x)
    (hg : ContDiffAt ℝ (i : ℕ∞ω) g x) :
    iteratedFDeriv ℝ i (fun y => f y - g y) x
      = iteratedFDeriv ℝ i f x - iteratedFDeriv ℝ i g x := by
  have hpair : ContDiffAt ℝ (i : ℕ∞ω) (fun y : E => (f y, g y)) x := hf.prodMk hg
  have h2 := (subCLM F).iteratedFDeriv_comp_left hpair le_rfl
  rw [iteratedFDeriv_prodMk hf hg le_rfl] at h2
  exact h2

/-- The inner slice functions of a difference. -/
private lemma iteratedDeriv_slice_sub {V : Set (ℝ × E)} (hV : IsOpen V)
    {f g : ℝ × E → Z} (hf : ContDiffOn ℝ (⊤ : ℕ∞) f V) (hg : ContDiffOn ℝ (⊤ : ℕ∞) g V)
    {p : ℝ × E} (hp : p ∈ V) (k : ℕ) (y' : E) (hy' : (p.1, y') ∈ V) :
    iteratedDeriv k (fun s : ℝ => f (s, y') - g (s, y')) p.1
      = iteratedDeriv k (fun s : ℝ => f (s, y')) p.1
        - iteratedDeriv k (fun s : ℝ => g (s, y')) p.1 := by
  have hfy : ContDiffAt ℝ (k : ℕ∞ω) (fun s : ℝ => f (s, y')) p.1 :=
    ((hf.contDiffAt (hV.mem_nhds hy')).of_le (by simp)).comp p.1
      (contDiffAt_id.prodMk (contDiffAt_const (c := y')))
  have hgy : ContDiffAt ℝ (k : ℕ∞ω) (fun s : ℝ => g (s, y')) p.1 :=
    ((hg.contDiffAt (hV.mem_nhds hy')).of_le (by simp)).comp p.1
      (contDiffAt_id.prodMk (contDiffAt_const (c := y')))
  exact iteratedDeriv_sub hfy hgy

/-- The `m`-th jet of the slice of a smooth function. -/
private lemma contDiffAt_slice_jet {V : Set (ℝ × E)} (hV : IsOpen V) {f : ℝ × E → Z}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f V) {p : ℝ × E} (hp : p ∈ V) (k m : ℕ) :
    ContDiffAt ℝ (m : ℕ∞ω)
      (fun y' : E => iteratedDeriv k (fun s : ℝ => f (s, y')) p.1) p.2 :=
  ((Work.Diff.EXT.JetConv.tDer_smooth hV hf k).contDiffAt (hV.mem_nhds hp)).comp p.2
    ((contDiffAt_const (c := p.1)).prodMk contDiffAt_id) |>.of_le (by simp)

/-- The mixed jets of a difference are the differences of the mixed jets (near a point where both
functions are smooth). -/
private lemma pat_sub {V : Set (ℝ × E)} (hV : IsOpen V) {f g : ℝ × E → Z}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f V) (hg : ContDiffOn ℝ (⊤ : ℕ∞) g V)
    {p : ℝ × E} (hp : p ∈ V) (k m : ℕ) :
    pat k m (fun q => f q - g q) p = pat k m f p - pat k m g p := by
  have hVp : IsOpen {y' : E | (p.1, y') ∈ V} :=
    hV.preimage (continuous_const.prodMk continuous_id)
  have hpp : p.2 ∈ {y' : E | (p.1, y') ∈ V} := hp
  have heq : ∀ y' ∈ {y' : E | (p.1, y') ∈ V},
      iteratedDeriv k (fun s : ℝ => f (s, y') - g (s, y')) p.1
        = iteratedDeriv k (fun s : ℝ => f (s, y')) p.1
          - iteratedDeriv k (fun s : ℝ => g (s, y')) p.1 :=
    fun y' hy' => iteratedDeriv_slice_sub hV hf hg hp k y' hy'
  simp only [pat]
  rw [iteratedFDeriv_congr_open hVp heq hpp m]
  exact iteratedFDeriv_sub_of_contDiffAt m (contDiffAt_slice_jet hV hf hp k m)
    (contDiffAt_slice_jet hV hg hp k m)

section BorelAssembly

/-- The zero-order mixed jet is the value of the function. -/
private lemma pat_zero_zero_apply (G : ℝ × E → Z) (p : ℝ × E) :
    (pat 0 0 G p) (fun i : Fin 0 => i.elim0) = G p := by
  simp only [pat, iteratedDeriv_zero]
  simpa using iteratedFDeriv_zero_apply (𝕜 := ℝ) (f := fun y' : E => G (p.1, y')) (x := p.2)
    (fun i : Fin 0 => i.elim0)

/-- **Continuity of the mixed jets of a smooth function.** -/
private lemma continuousOn_pat {V : Set (ℝ × E)} (hV : IsOpen V) {G : ℝ × E → Z}
    (hG : ContDiffOn ℝ (⊤ : ℕ∞) G V) (k m : ℕ) : ContinuousOn (pat k m G) V := by
  have hΨ : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun q : ℝ × E => iteratedDeriv k (fun s : ℝ => G (s, q.2)) q.1) V :=
    Work.Diff.EXT.JetConv.tDer_smooth hV hG k
  have hjet : ContinuousOn (fun p : ℝ × E => iteratedFDeriv ℝ m
      (fun q : ℝ × E => iteratedDeriv k (fun s : ℝ => G (s, q.2)) q.1) p) V := by
    intro p hp
    have hcd : ContDiffAt ℝ (⊤ : ℕ∞) (fun p : ℝ × E => iteratedFDeriv ℝ m
        (fun q : ℝ × E => iteratedDeriv k (fun s : ℝ => G (s, q.2)) q.1) p) p :=
      (hΨ.contDiffAt (hV.mem_nhds hp)).iteratedFDeriv_right (i := m) (by simp)
    exact hcd.continuousAt.continuousWithinAt
  have hL : Continuous (fun A : ContinuousMultilinearMap ℝ (fun _ : Fin m => ℝ × E) Z =>
      A.compContinuousLinearMap (fun _ : Fin m => ContinuousLinearMap.inr ℝ ℝ E)) :=
    (ContinuousMultilinearMap.compContinuousLinearMapL
      (fun _ : Fin m => ContinuousLinearMap.inr ℝ ℝ E)).continuous
  refine (hL.comp_continuousOn hjet).congr ?_
  intro p hp
  exact Work.Diff.EXT.JetConv.slice_jet_comp_inr hV hΨ hp m

/-- **The Borel realisation, shifted to the seam.** -/
private theorem exists_borel_shifted
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace Z]
    {T : ℝ} {U₁ : Set E} (hU₁ : IsOpen U₁) {f : ℕ → E → Z}
    (hf : ∀ k, ContDiffOn ℝ (⊤ : ℕ∞) (f k) U₁)
    {y₀ : E} (hy₀ : y₀ ∈ U₁) :
    ∃ W : Set E, IsOpen W ∧ y₀ ∈ W ∧ W ⊆ U₁ ∧ ∃ ε > 0, ∃ B : ℝ × E → Z,
      ContDiffOn ℝ (⊤ : ℕ∞) B ((Set.Ioo (T - ε) (T + ε)) ×ˢ W) ∧
      ∀ k : ℕ, ∀ y ∈ W, iteratedDeriv k (fun t : ℝ => B (t, y)) T = f k y := by
  obtain ⟨ε, hε, W, hWopen, hy₀W, hWU, F, hFsm, hFjets⟩ := borel_jet_on hU₁ f hf hy₀
  refine ⟨W, hWopen, hy₀W, hWU, ε, hε, fun p => F (p.1 - T, p.2), ?_, ?_⟩
  · refine ContDiffOn.comp hFsm ?_ ?_
    · exact ((contDiff_fst.sub contDiff_const).prodMk contDiff_snd).contDiffOn
    · intro p hp
      obtain ⟨hp1, hp2⟩ := hp
      exact ⟨⟨by linarith [hp1.1], by linarith [hp1.2]⟩, hp2⟩
  · intro k y hy
    have hshift : ∀ (g : ℝ → Z) (n : ℕ),
        iteratedDeriv n (fun t : ℝ => g (t - T)) T = iteratedDeriv n g 0 := by
      intro g n
      have hfun : (fun t : ℝ => g (t - T)) = fun z : ℝ => g ((-T) + z) := by
        funext t; ring_nf
      rw [hfun, iteratedDeriv_eq_iteratedFDeriv, iteratedDeriv_eq_iteratedFDeriv,
        iteratedFDeriv_comp_add_left n (-T) T]
      have h0 : (-T) + T = (0 : ℝ) := by ring
      rw [h0]
    rw [hshift (fun s : ℝ => F (s, y)) k]
    exact hFjets k y hy

end BorelAssembly

/-- **A `C^∞` function on a half-open slab with uniformly bounded jets extends smoothly across the
endpoint.**  If `u : ℝ × E → Z` is `C^∞` on `(Ico σ T) ×ˢ U` and every ambient iterated Fréchet
derivative of `u` there is bounded by a constant depending only on its order, then near any
`y₀ ∈ U` the function `u` agrees on the left slab with some `V` that is `C^∞` on a two-sided
neighbourhood `(Ioo (T-δ) (T+δ)) ×ˢ U'` of `(T, y₀)`.

Proof route (Borel's realisation of jets + a flat cut):
* `Work.Diff.EXT.jets_converge_of_bounded` gives smooth limits `f k` of the `k`-th `t`-derivative
  slices of `u` near `y₀`, together with the convergence of all their spatial jets;
* `Work.Diff.EXT.borel_jet_on` realises the jet sequence `f` by a smooth `B : ℝ × E → Z` with
  `iteratedDeriv k (fun t => B (t, y)) 0 = f k y`, which after shifting the time coordinate has the
  `t`-jets of `u` at `(T, y)` for every `y` in a neighbourhood;
* hence `w := B - u` has all its mixed jets tending to `0` at the seam, so
  `Work.Diff.EXT.heaviside_cut_smooth_at_seam` makes the Heaviside cut of a time-truncation of `w`
  smooth on a two-sided neighbourhood;
* `V := B - cut` then does the job.

Note on `heaviside_cut_smooth_at_seam`: its hypothesis `hG` asks for smoothness on the whole
half-space `{p | p.1 < T}`, whereas `w = B - u` is smooth only near `t = T` (both `B` and `u` are
given only on slabs).  Handle this by first multiplying `w` by a smooth time cut-off `χ` with
`χ ≡ 1` near `T` and `χ ≡ 0` for `t ≤ T - η` (for `η > 0` so small that `χ w` is smooth on the
whole half-space; near `t = T` the cut function `if p.1 < T then χ p * w p else 0` agrees with the
uncut one, which is what the conclusion needs). -/
theorem ext_of_bounded_jets
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace Z]
    {σ T : ℝ} (hσT : σ < T) {U : Set E} (hU : IsOpen U) {u : ℝ × E → Z}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) u ((Set.Ico σ T) ×ˢ U))
    (hb : ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ (Set.Ico σ T) ×ˢ U,
        ‖iteratedFDeriv ℝ k u p‖ ≤ C)
    {y₀ : E} (hy₀ : y₀ ∈ U) :
    ∃ U' : Set E, IsOpen U' ∧ y₀ ∈ U' ∧ U' ⊆ U ∧ ∃ δ > 0, ∃ V : ℝ × E → Z,
      ContDiffOn ℝ (⊤ : ℕ∞) V ((Set.Ioo (T - δ) (T + δ)) ×ˢ U') ∧
      ∀ t ∈ Set.Ico (T - δ) T, ∀ y ∈ U', V (t, y) = u (t, y) := by
  classical
  -- ### Step 1: the limits of the time derivatives of `u` at the seam
  obtain ⟨U₁, hU₁open, hy₀U₁, hU₁U, f, hf_sm, hf_conv⟩ :=
    slice_jets_converge hσT hU hu hb hy₀
  -- ### Step 2: Borel's realisation of the jet sequence, shifted to the seam
  obtain ⟨W, hWopen, hy₀W, hWU₁, ε, hεpos, B, hBsm, hBjets⟩ :=
    exists_borel_shifted hU₁open hf_sm hy₀U₁
  have hWU : W ⊆ U := fun y hy => hU₁U (hWU₁ hy)
  -- ### Step 3: parameters and the time cut-off
  obtain ⟨c, hcε, hcσ, hcT⟩ : ∃ c : ℝ, T - ε ≤ c ∧ σ ≤ c ∧ c < T :=
    ⟨max σ (T - ε), le_max_right _ _, le_max_left _ _, max_lt hσT (by linarith)⟩
  obtain ⟨b, hcb, hbT⟩ : ∃ b : ℝ, c < b ∧ b < T := ⟨(c + T) / 2, by linarith, by linarith⟩
  obtain ⟨a, hca, hab⟩ : ∃ a : ℝ, c < a ∧ a < b := ⟨(c + b) / 2, by linarith, by linarith⟩
  have hσa : σ < a := lt_of_le_of_lt hcσ hca
  have h0ab : (0 : ℝ) < b - a := by linarith
  -- the cut-off: `0` for `t ≤ a`, `1` for `t ≥ b`
  set θ : ℝ → ℝ := fun t => Real.smoothTransition ((t - a) / (b - a)) with hθdef
  have hθsm : ContDiff ℝ (⊤ : ℕ∞) θ := by
    rw [hθdef]
    exact Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const (b - a))
  have hθzero : ∀ t : ℝ, t ≤ a → θ t = 0 := by
    intro t ht
    rw [hθdef]
    exact Real.smoothTransition.zero_of_nonpos
      (div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith))
  have hθone : ∀ t : ℝ, b ≤ t → θ t = 1 := by
    intro t ht
    rw [hθdef]
    exact Real.smoothTransition.one_of_one_le (by rw [le_div_iff₀ h0ab]; linarith)
  -- ### Step 4: the defect `G = θ • (B - u)`
  set G : ℝ × E → Z := fun p => θ p.1 • (B p - u p) with hGdef
  have hhalf : {p : ℝ × E | p.1 < T} ∩ (Set.univ ×ˢ W)
      ⊆ {p : ℝ × E | p.1 < T} ∩ (Set.univ ×ˢ U₁) := by
    rintro p ⟨hp1, _, hp2⟩
    exact ⟨hp1, trivial, hWU₁ hp2⟩
  have hGsm : ContDiffOn ℝ (⊤ : ℕ∞) G ({p : ℝ × E | p.1 < T} ∩ (Set.univ ×ˢ W)) := by
    intro p hp
    obtain ⟨hpT, _, hpW⟩ := hp
    have hpT' : p.1 < T := hpT
    by_cases hpa : p.1 < a
    · -- `G` vanishes near `p`
      have hnb : {q : ℝ × E | q.1 < a} ∈ 𝓝 p :=
        (isOpen_lt continuous_fst continuous_const).mem_nhds hpa
      have hG0 : G =ᶠ[𝓝 p] fun _ : ℝ × E => (0 : Z) := by
        filter_upwards [hnb] with q hq
        rw [hGdef]
        simp only
        rw [hθzero q.1 hq.le, zero_smul]
      exact ((contDiffAt_const (c := (0 : Z))).congr_of_eventuallyEq hG0).contDiffWithinAt
    · -- `G = θ • (B - u)` is a product of functions smooth at `p`
      have hpa' : a ≤ p.1 := not_lt.mp hpa
      have hpΩ : p ∈ Set.Ioo σ T ×ˢ U := ⟨⟨hσa.trans_le hpa', hpT'⟩, hWU hpW⟩
      have hBp : ContDiffAt ℝ (⊤ : ℕ∞) B p :=
        hBsm.contDiffAt (by
          refine (isOpen_Ioo.prod hWopen).mem_nhds
            ⟨⟨by linarith [hpa', hca, hcε], by linarith [hpT', hεpos]⟩, hpW⟩)
      have hup : ContDiffAt ℝ (⊤ : ℕ∞) u p :=
        (hu.mono (by
          rintro q ⟨hq1, hq2⟩
          exact ⟨⟨hq1.1.le, hq1.2⟩, hq2⟩)).contDiffAt
          ((isOpen_Ioo.prod hU).mem_nhds hpΩ)
      have hθp : ContDiffAt ℝ (⊤ : ℕ∞) (fun q : ℝ × E => θ q.1) p :=
        hθsm.contDiffAt.comp p contDiffAt_fst
      exact (hθp.smul (hBp.sub hup)).contDiffWithinAt
  -- ### Step 5: the mixed jets of `G` tend to `0` at the seam
  have hGflat : ∀ k m : ℕ, ∀ y ∈ W, Filter.Tendsto (fun p : ℝ × E => pat k m G p)
      (nhdsWithin (T, y) ({p : ℝ × E | p.1 < T} ∩ (Set.univ ×ˢ W))) (nhds 0) := by
    intro k m y hy
    set S : Set (ℝ × E) := {p : ℝ × E | p.1 < T} ∩ (Set.univ ×ˢ W) with hS
    have hΩopen : IsOpen (Set.Ioo c T ×ˢ W) := isOpen_Ioo.prod hWopen
    have hBΩ : ContDiffOn ℝ (⊤ : ℕ∞) B (Set.Ioo c T ×ˢ W) :=
      hBsm.mono (by
        rintro q ⟨hq1, hq2⟩
        exact ⟨⟨by linarith [hq1.1, hcε], by linarith [hq1.2]⟩, hq2⟩)
    have huΩ : ContDiffOn ℝ (⊤ : ℕ∞) u (Set.Ioo c T ×ˢ W) :=
      hu.mono (by
        rintro q ⟨hq1, hq2⟩
        exact ⟨⟨le_of_lt (lt_of_le_of_lt hcσ hq1.1), hq1.2⟩, hWU hq2⟩)
    have hmemB : ((T, y) : ℝ × E) ∈ Set.Ioo (T - ε) (T + ε) ×ˢ W :=
      ⟨⟨by linarith, by linarith⟩, hy⟩
    have hBcont : ContinuousAt (pat k m B) (T, y) :=
      (continuousOn_pat (isOpen_Ioo.prod hWopen) hBsm k m).continuousAt
        ((isOpen_Ioo.prod hWopen).mem_nhds hmemB)
    have h1 : Filter.Tendsto (fun p : ℝ × E => pat k m B p) (nhdsWithin (T, y) S)
        (nhds (pat k m B (T, y))) :=
      hBcont.tendsto.mono_left nhdsWithin_le_nhds
    have hBid : pat k m B (T, y) = iteratedFDeriv ℝ m (f k) y :=
      iteratedFDeriv_congr_open hWopen (fun y' hy' => hBjets k y' hy') hy m
    have hfcont : ContinuousAt (fun y' : E => iteratedFDeriv ℝ m (f k) y') y := by
      have hcd : ContDiffAt ℝ (⊤ : ℕ∞) (fun y' : E => iteratedFDeriv ℝ m (f k) y') y :=
        ((hf_sm k).contDiffAt (hU₁open.mem_nhds (hWU₁ hy))).iteratedFDeriv_right
          (i := m) (by simp)
      exact hcd.continuousAt
    have h3 : Filter.Tendsto (fun p : ℝ × E => iteratedFDeriv ℝ m (f k) p.2)
        (nhdsWithin (T, y) S) (nhds (iteratedFDeriv ℝ m (f k) y)) :=
      hfcont.tendsto.comp (continuous_snd.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    have h2 : Filter.Tendsto (fun p : ℝ × E => pat k m u p) (nhdsWithin (T, y) S)
        (nhds (iteratedFDeriv ℝ m (f k) y)) := by
      have hconv : Filter.Tendsto (fun p : ℝ × E => pat k m u p - iteratedFDeriv ℝ m (f k) p.2)
          (nhdsWithin (T, y) S) (nhds 0) :=
        (hf_conv k m y (hWU₁ hy)).mono_left (nhdsWithin_mono _ hhalf)
      simpa using hconv.add h3
    have h4 : Filter.Tendsto (fun p : ℝ × E => pat k m B p - pat k m u p) (nhdsWithin (T, y) S)
        (nhds 0) := by
      have h := h1.sub h2
      rw [hBid] at h
      simpa using h
    have hev_b : ∀ᶠ p in nhdsWithin (T, y) S, b < p.1 :=
      nhdsWithin_le_nhds ((isOpen_lt continuous_const continuous_fst).mem_nhds hbT)
    have hev : (fun p : ℝ × E => pat k m G p)
        =ᶠ[nhdsWithin (T, y) S] (fun p : ℝ × E => pat k m B p - pat k m u p) := by
      filter_upwards [self_mem_nhdsWithin, hev_b] with p hpS hpb
      have hΩ : p ∈ Set.Ioo c T ×ˢ W := ⟨⟨by linarith [hca, hpb], hpS.1⟩, hpS.2.2⟩
      have hGD : pat k m G p = pat k m (fun q : ℝ × E => B q - u q) p := by
        refine pat_congr (V := {q : ℝ × E | b < q.1})
          (isOpen_lt continuous_const continuous_fst) (fun q hq => ?_) hpb k m
        rw [hGdef]
        simp only
        rw [hθone q.1 hq.le, one_smul]
      rw [hGD, pat_sub hΩopen hBΩ huΩ hΩ k m]
    exact h4.congr' hev.symm
  -- ### Step 6: the Heaviside cut of `G` is smooth at the seam
  have hcut : ∀ y ∈ W, ContDiffAt ℝ (⊤ : ℕ∞)
      (fun p : ℝ × E => if p.1 < T then G p else (0 : Z)) (T, y) :=
    fun y hy => heaviside_cut_smooth_at_seam (hWopen.mem_nhds hy) hGsm hGflat
  -- ### Step 7: the extension `V = B - cut` and its smoothness on a two-sided box
  obtain ⟨δ, hδpos, hδε, hδb⟩ : ∃ δ : ℝ, δ > 0 ∧ δ ≤ ε ∧ δ ≤ T - b := by
    refine ⟨min (ε / 2) ((T - b) / 2), ?_, ?_, ?_⟩
    · exact lt_min (by linarith) (by linarith)
    · exact le_trans (min_le_left _ _) (by linarith)
    · exact le_trans (min_le_right _ _) (by linarith)
  refine ⟨W, hWopen, hy₀W, hWU, δ, hδpos,
    fun p => B p - (if p.1 < T then G p else (0 : Z)), ?_, ?_⟩
  · rw [IsOpen.contDiffOn_iff (isOpen_Ioo.prod hWopen)]
    rintro ⟨t, y'⟩ ⟨ht1, hy'⟩
    have ht1a : T - δ < t := ht1.1
    have ht1b : t < T + δ := ht1.2
    -- `B` is smooth on the box because the box sits inside `(T-ε, T+ε) × W`
    have hBbox : ContDiffAt ℝ (⊤ : ℕ∞) B (t, y') :=
      hBsm.contDiffAt ((isOpen_Ioo.prod hWopen).mem_nhds
        ⟨⟨by linarith [ht1a, hδε], by linarith [ht1b, hδε]⟩, hy'⟩)
    rcases lt_trichotomy t T with hlt | heq | hgt
    · -- left of the seam
      have hup : ContDiffAt ℝ (⊤ : ℕ∞) u (t, y') :=
        (hu.mono (by
          rintro q ⟨hq1, hq2⟩
          exact ⟨⟨hq1.1.le, hq1.2⟩, hq2⟩)).contDiffAt
          ((isOpen_Ioo.prod hU).mem_nhds
            ⟨⟨by linarith [ht1a, hδb, hbT, hlt], hlt⟩, hWU hy'⟩)
      have hθp : ContDiffAt ℝ (⊤ : ℕ∞) (fun q : ℝ × E => θ q.1) (t, y') :=
        hθsm.contDiffAt.comp (t, y') contDiffAt_fst
      have hclose : (fun q : ℝ × E => B q - (if q.1 < T then G q else (0 : Z)))
          =ᶠ[𝓝 (t, y')] fun q : ℝ × E => B q - θ q.1 • (B q - u q) := by
        have hnb : {q : ℝ × E | q.1 < T} ∈ 𝓝 (t, y') :=
          (isOpen_lt continuous_fst continuous_const).mem_nhds hlt
        filter_upwards [hnb] with q hq
        simp only [hq, ↓reduceIte, hGdef]
      exact (hBbox.sub (hθp.smul (hBbox.sub hup))).congr_of_eventuallyEq hclose
    · -- on the seam
      rw [heq] at hBbox ⊢
      exact hBbox.sub (hcut y' hy')
    · -- right of the seam
      have hclose : (fun q : ℝ × E => B q - (if q.1 < T then G q else (0 : Z)))
          =ᶠ[𝓝 (t, y')] fun q : ℝ × E => B q := by
        have hnb : {q : ℝ × E | T < q.1} ∈ 𝓝 (t, y') :=
          (isOpen_lt continuous_const continuous_fst).mem_nhds hgt
        filter_upwards [hnb] with q hq
        simp only [not_lt.mpr hq.le, ↓reduceIte, sub_zero]
      exact hBbox.congr_of_eventuallyEq hclose
  · rintro t ⟨ht1, ht2⟩ y hy
    have ht1' : T - δ ≤ t := ht1
    have hbt : b ≤ t := by linarith [hδb, ht1']
    show B (t, y) - (if t < T then G (t, y) else (0 : Z)) = u (t, y)
    simp only [ht2, ↓reduceIte]
    rw [show G (t, y) = θ t • (B (t, y) - u (t, y)) from by rw [hGdef]]
    rw [hθone t hbt, one_smul, sub_sub_cancel]

end Work.Diff.EXT
