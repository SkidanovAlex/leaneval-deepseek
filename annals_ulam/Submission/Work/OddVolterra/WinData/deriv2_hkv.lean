import Submission.Work.OddVolterra.Window.JetCurve_box
import Submission.Work.OddVolterra.WinData.deriv2_jet

/-!
# The second `u`-derivative of `KvecM` on the extended box

This file discharges the hypothesis `hKv` of
`Work.OddVolterra.WinData.thetaM_deriv_close_of_KvecM`: the three clauses of the second
`u`-derivative estimate for the manifest Abel kernel vector `KvecM`.

Each component of `KvecM` is a composition `F ∘ KJet` of one of the two fixed smooth functions
`KF1 n`, `Phi2 n` of the finite jet with the jet curve (`KvecM_row0`, `KvecM_row1`), so the second
derivative is obtained by applying `JetCurve_box` not to `F` but to the "acceleration"

`AccF (x, y) = fderiv ℝ F x y`

along the jet curve `u ↦ VJet n g σ v u = (KJet u, (KJet)' u)`.  The ingredients are the bounds,
the `O(δ)`-closeness and the state-Lipschitz property of the jet (`KJet_bounds_ext`,
`KJet_close_ext`, `KJet_lip_ext`), the identification of `deriv (AccF ∘ VJet)` with the second
`u`-derivative of `KvecM` (`deriv_VJet_AccF0`, `deriv_VJet_AccF1`), and the derivative of the
pair-valued curve (`deriv_prodMk_ext`).
-/

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

namespace Work.OddVolterra.WinData

noncomputable section

open Work.OddVolterra Work.OddVolterra.Window Work.OddVolterra.KernelExt

set_option maxHeartbeats 1600000

/-- **Derivative of a pair-valued curve**, componentwise. -/
lemma deriv_prodMk_ext {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : ℝ → E} {g : ℝ → F} {x : ℝ}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    deriv (fun u : ℝ => (f u, g u)) x = (deriv f x, deriv g x) := by
  have h : HasFDerivAt (fun u : ℝ => (f u, g u)) ((fderiv ℝ f x).prod (fderiv ℝ g x)) x :=
    hf.hasFDerivAt.prodMk hg.hasFDerivAt
  rw [show deriv (fun u : ℝ => (f u, g u)) x
      = fderiv ℝ (fun u : ℝ => (f u, g u)) x 1 from rfl, h.fderiv,
    ContinuousLinearMap.prod_apply,
    show deriv f x = fderiv ℝ f x 1 from rfl, show deriv g x = fderiv ℝ g x 1 from rfl]

/-- **Norm of a pair**, from the two component bounds. -/
lemma norm_prod_le_ext {E F : Type*} [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]
    {x : E} {y : F} {c : ℝ} (hx : ‖x‖ ≤ c) (hy : ‖y‖ ≤ c) : ‖(x, y)‖ ≤ c := by
  rw [Prod.norm_def]; exact max_le hx hy

/-- **The derivative of the jet curve**, in components. -/
lemma deriv_VJet_eq_ext (n : ℕ) {g : ℝ → ℝ} (gg : ContDiff ℝ (⊤ : ℕ∞) g) (σ : ℝ) (v : St)
    (u : ℝ) :
    deriv (VJet n g σ v) u = (deriv (fun u' : ℝ => KJet n g σ v u') u,
      deriv (deriv (fun u' : ℝ => KJet n g σ v u')) u) := by
  have hJ : ContDiff ℝ (⊤ : ℕ∞) (fun u' : ℝ => KJet n g σ v u') := contDiff_KJet n gg σ v
  have hJ1 : ContDiff ℝ (⊤ : ℕ∞) (deriv (fun u' : ℝ => KJet n g σ v u')) :=
    ContDiff.iterate_deriv 1 hJ
  have heq : VJet n g σ v
      = fun u' : ℝ => (KJet n g σ v u', deriv (fun u'' : ℝ => KJet n g σ v u'') u') := rfl
  rw [heq]
  exact deriv_prodMk_ext (f := fun u' : ℝ => KJet n g σ v u')
    (g := fun u' : ℝ => deriv (fun u'' : ℝ => KJet n g σ v u'') u') (x := u)
    (hJ.differentiable (by simp)).differentiableAt
    (hJ1.differentiable (by simp)).differentiableAt

/-- **Second `u`-derivative of `KvecM` on the extended box.**  The three clauses: a bound, the
`O(δ)`-closeness to the unperturbed kernel, and the state-Lipschitz property. -/
theorem KvecM_deriv2_ext (n : ℕ) (hn : 1 ≤ n) :
    ∃ C L : ℝ, 0 < C ∧ 0 < L ∧
      ∀ (h : ℝ → ℝ) (δ : ℝ), ContDiff ℝ (⊤ : ℕ∞) h → 0 < δ → δ ≤ 1 / 100 →
      (∀ k : ℕ, k ≤ n + 3 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ δ) →
      Function.support h ⊆ Set.Icc (1 - 2 * tau) (1 - tau) →
      ∀ u ∈ Set.Icc (3 / 16 : ℝ) 1, ∀ σ ∈ Set.Icc (1 / 4 : ℝ) 1,
      ∀ z : St, (1 / 5 : ℝ) ≤ z 0 → (1 / 5 : ℝ) ≤ z 1 → (∀ i : Fin 4, |z i| ≤ 2) →
      ∀ z' : St, (1 / 5 : ℝ) ≤ z' 0 → (1 / 5 : ℝ) ≤ z' 1 → (∀ i : Fin 4, |z' i| ≤ 2) →
      ∀ j : Fin 2,
      ‖deriv (deriv (fun u' : ℝ => (KvecM n h u' σ (z 0) (z 1) (z 2) (z 3)) j)) u‖ ≤ C ∧
      ‖deriv (deriv (fun u' : ℝ => (KvecM n h u' σ (z 0) (z 1) (z 2) (z 3)) j)) u -
       deriv (deriv (fun u' : ℝ => (KvecM n 0 u' σ (z 0) (z 1) (z 2) (z 3)) j)) u‖
        ≤ C * δ ∧
      ‖deriv (deriv (fun u' : ℝ => (KvecM n h u' σ (z 0) (z 1) (z 2) (z 3)) j)) u -
       deriv (deriv (fun u' : ℝ => (KvecM n h u' σ (z' 0) (z' 1) (z' 2) (z' 3)) j)) u‖
        ≤ L * ‖z - z'‖ := by
  obtain ⟨B, hB0, hBnd⟩ := KJet_bounds_ext n hn
  obtain ⟨Bc, hBc0, hBcl⟩ := KJet_close_ext n hn
  obtain ⟨K, hK0, hKlip⟩ := KJet_lip_ext n hn
  have hBt1 : (1 : ℝ) ≤ max (max B Bc) 1 := le_max_right _ _
  have hBt0 : 0 < max (max B Bc) 1 := lt_of_lt_of_le one_pos hBt1
  have hBBt : B ≤ max (max B Bc) 1 :=
    le_trans (le_max_left B Bc) (le_max_left (max B Bc) 1)
  have hBcBt : Bc ≤ max (max B Bc) 1 :=
    le_trans (le_max_right B Bc) (le_max_left (max B Bc) 1)
  have hUopen : IsOpen (KJopen n ×ˢ (Set.univ : Set (KJIx n → ℝ))) :=
    (isOpen_KJopen n).prod isOpen_univ
  have hcvx : Convex ℝ (Abox n B ×ˢ Metric.closedBall (0 : KJIx n → ℝ) (max (max B Bc) 1)) :=
    (convex_Abox n B).prod (convex_closedBall (0 : KJIx n → ℝ) (max (max B Bc) 1))
  have hcpt : IsCompact (Abox n B ×ˢ Metric.closedBall (0 : KJIx n → ℝ) (max (max B Bc) 1)) :=
    (isCompact_Abox n B).prod (isCompact_closedBall (0 : KJIx n → ℝ) (max (max B Bc) 1))
  have hKcU : (Abox n B ×ˢ Metric.closedBall (0 : KJIx n → ℝ) (max (max B Bc) 1)) ⊆
      (KJopen n ×ˢ (Set.univ : Set (KJIx n → ℝ))) :=
    fun p hp => ⟨Abox_subset_KJopen n B hp.1, trivial⟩
  obtain ⟨C0, hC00, hC0⟩ := JetCurve_box (E := (KJIx n → ℝ) × (KJIx n → ℝ))
    (AccF0 n) hUopen hcvx hcpt hKcU (contDiffOn_AccF0 n) hBt0.le
  obtain ⟨C1, hC10, hC1⟩ := JetCurve_box (E := (KJIx n → ℝ) × (KJIx n → ℝ))
    (AccF1 n) hUopen hcvx hcpt hKcU (contDiffOn_AccF1 n) hBt0.le
  have hCc0 : 0 < max (max C0 C1) 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  refine ⟨max (max C0 C1) 1 * max (max B Bc) 1, max (max C0 C1) 1 * K,
    mul_pos hCc0 hBt0, mul_pos hCc0 hK0, ?_⟩
  intro h δ hh hδ0 hδ1 hjet hsupp u hu σ hσ z hz0 hz1 hz z' hz0' hz1' hz' j
  have hsm : ∀ k : ℕ, k ≤ n + 3 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100 :=
    fun k hk s => le_trans (hjet k hk s) hδ1
  have hsm0 : ∀ k : ℕ, k ≤ n + 3 → ∀ s : ℝ,
      |iteratedDeriv k (0 : ℝ → ℝ) s| ≤ 1 / 100 := by
    intro k hk s; rw [iteratedDeriv_zero_fun]; norm_num
  have hsupp0 : Function.support (0 : ℝ → ℝ) ⊆ Set.Icc (1 - 2 * tau) (1 - tau) := by
    intro x hx; simp at hx
  -- ## the abstract step, once per "acceleration function"
  have key : ∀ (F : (KJIx n → ℝ) × (KJIx n → ℝ) → ℝ) (C : ℝ), 0 ≤ C → C ≤ max (max C0 C1) 1 →
      (∀ (j₁ j₀ : ℝ → (KJIx n → ℝ) × (KJIx n → ℝ)) (a δ' : ℝ), 0 ≤ δ' →
        ContDiff ℝ (⊤ : ℕ∞) j₁ → ContDiff ℝ (⊤ : ℕ∞) j₀ →
        j₁ a ∈ Abox n B ×ˢ Metric.closedBall (0 : KJIx n → ℝ) (max (max B Bc) 1) →
        j₀ a ∈ Abox n B ×ˢ Metric.closedBall (0 : KJIx n → ℝ) (max (max B Bc) 1) →
        ‖deriv j₁ a‖ ≤ max (max B Bc) 1 → ‖deriv j₀ a‖ ≤ max (max B Bc) 1 →
        ‖j₁ a - j₀ a‖ ≤ δ' → ‖deriv j₁ a - deriv j₀ a‖ ≤ δ' →
        |F (j₁ a)| ≤ C ∧ |F (j₀ a)| ≤ C ∧ |deriv (fun x => F (j₁ x)) a| ≤ C ∧
        |deriv (fun x => F (j₀ x)) a| ≤ C ∧ |F (j₁ a) - F (j₀ a)| ≤ C * δ' ∧
        |deriv (fun x => F (j₁ x)) a - deriv (fun x => F (j₀ x)) a| ≤ C * δ') →
      ∀ (D : (ℝ → ℝ) → St → ℝ),
        (∀ (g : ℝ → ℝ) (gg : ContDiff ℝ (⊤ : ℕ∞) g) (v : St),
          KJet n g σ v u ∈ KJopen n → deriv (fun x => F (VJet n g σ v x)) u = D g v) →
      ‖D h z‖ ≤ max (max C0 C1) 1 * max (max B Bc) 1 ∧
      ‖D h z - D 0 z‖ ≤ max (max C0 C1) 1 * max (max B Bc) 1 * δ ∧
      ‖D h z - D h z'‖ ≤ max (max C0 C1) 1 * K * ‖z - z'‖ := by
    intro F C hC hCle hbox D hid
    obtain ⟨hJz, hJvz, hJdz⟩ := hBnd h hh hsm hsupp σ hσ z hz0 hz1 hz u hu
    obtain ⟨hJ0, hJv0, hJd0⟩ := hBnd 0 contDiff_const hsm0 hsupp0 σ hσ z hz0 hz1 hz u hu
    obtain ⟨hJz', hJvz', hJdz'⟩ := hBnd h hh hsm hsupp σ hσ z' hz0' hz1' hz' u hu
    obtain ⟨hJ0', hJv0', hJd0'⟩ := hBnd 0 contDiff_const hsm0 hsupp0 σ hσ z' hz0' hz1' hz' u hu
    have hcl := hBcl h hh δ hδ0 hδ1 hjet hsupp σ hσ z hz0 hz1 hz u hu
    have hlip := hKlip h hh hsm σ hσ z z' hz0 hz1 hz hz0' hz1' hz' u hu
    have hopen := Abox_subset_KJopen n B
    have hmemz : VJet n h σ z u ∈
        Abox n B ×ˢ Metric.closedBall (0 : KJIx n → ℝ) (max (max B Bc) 1) :=
      ⟨hJz, by rw [Metric.mem_closedBall, dist_zero_right]; exact le_trans hJvz hBBt⟩
    have hmem0 : VJet n 0 σ z u ∈
        Abox n B ×ˢ Metric.closedBall (0 : KJIx n → ℝ) (max (max B Bc) 1) :=
      ⟨hJ0, by rw [Metric.mem_closedBall, dist_zero_right]; exact le_trans hJv0 hBBt⟩
    have hmemz' : VJet n h σ z' u ∈
        Abox n B ×ˢ Metric.closedBall (0 : KJIx n → ℝ) (max (max B Bc) 1) :=
      ⟨hJz', by rw [Metric.mem_closedBall, dist_zero_right]; exact le_trans hJvz' hBBt⟩
    have hmem0' : VJet n 0 σ z' u ∈
        Abox n B ×ˢ Metric.closedBall (0 : KJIx n → ℝ) (max (max B Bc) 1) :=
      ⟨hJ0', by rw [Metric.mem_closedBall, dist_zero_right]; exact le_trans hJv0' hBBt⟩
    have hvelz : ‖deriv (VJet n h σ z) u‖ ≤ max (max B Bc) 1 := by
      rw [deriv_VJet_eq_ext n hh σ z u]
      exact le_trans (norm_prod_le_ext hJvz hJdz) hBBt
    have hvel0 : ‖deriv (VJet n 0 σ z) u‖ ≤ max (max B Bc) 1 := by
      rw [deriv_VJet_eq_ext n (g := (0 : ℝ → ℝ)) contDiff_const σ z u]
      exact le_trans (norm_prod_le_ext hJv0 hJd0) hBBt
    have hvelz' : ‖deriv (VJet n h σ z') u‖ ≤ max (max B Bc) 1 := by
      rw [deriv_VJet_eq_ext n hh σ z' u]
      exact le_trans (norm_prod_le_ext hJvz' hJdz') hBBt
    have hvel0' : ‖deriv (VJet n 0 σ z') u‖ ≤ max (max B Bc) 1 := by
      rw [deriv_VJet_eq_ext n (g := (0 : ℝ → ℝ)) contDiff_const σ z' u]
      exact le_trans (norm_prod_le_ext hJv0' hJd0') hBBt
    have hBcδ : Bc * δ ≤ max (max B Bc) 1 * δ := mul_le_mul_of_nonneg_right hBcBt hδ0.le
    have hclval : ‖VJet n h σ z u - VJet n 0 σ z u‖ ≤ max (max B Bc) 1 * δ := by
      have hsub : VJet n h σ z u - VJet n 0 σ z u
          = (KJet n h σ z u - KJet n 0 σ z u,
             deriv (fun u' : ℝ => KJet n h σ z u') u -
               deriv (fun u' : ℝ => KJet n 0 σ z u') u) := rfl
      rw [hsub]
      exact norm_prod_le_ext (le_trans hcl.1 hBcδ) (le_trans hcl.2.1 hBcδ)
    have hclder : ‖deriv (VJet n h σ z) u - deriv (VJet n 0 σ z) u‖
        ≤ max (max B Bc) 1 * δ := by
      have hsub : deriv (VJet n h σ z) u - deriv (VJet n 0 σ z) u
          = (deriv (fun u' : ℝ => KJet n h σ z u') u -
               deriv (fun u' : ℝ => KJet n 0 σ z u') u,
             deriv (deriv (fun u' : ℝ => KJet n h σ z u')) u -
               deriv (deriv (fun u' : ℝ => KJet n 0 σ z u')) u) := by
        rw [deriv_VJet_eq_ext n hh σ z u, deriv_VJet_eq_ext n (g := (0 : ℝ → ℝ)) contDiff_const σ z u]; rfl
      rw [hsub]
      exact norm_prod_le_ext (le_trans hcl.2.1 hBcδ) (le_trans hcl.2.2 hBcδ)
    have hlpval : ‖VJet n h σ z u - VJet n h σ z' u‖ ≤ K * ‖z - z'‖ := by
      have hsub : VJet n h σ z u - VJet n h σ z' u
          = (KJet n h σ z u - KJet n h σ z' u,
             deriv (fun u' : ℝ => KJet n h σ z u') u -
               deriv (fun u' : ℝ => KJet n h σ z' u') u) := rfl
      rw [hsub]
      exact norm_prod_le_ext hlip.1 hlip.2.1
    have hllder : ‖deriv (VJet n h σ z) u - deriv (VJet n h σ z') u‖ ≤ K * ‖z - z'‖ := by
      have hsub : deriv (VJet n h σ z) u - deriv (VJet n h σ z') u
          = (deriv (fun u' : ℝ => KJet n h σ z u') u -
               deriv (fun u' : ℝ => KJet n h σ z' u') u,
             deriv (deriv (fun u' : ℝ => KJet n h σ z u')) u -
               deriv (deriv (fun u' : ℝ => KJet n h σ z' u')) u) := by
        rw [deriv_VJet_eq_ext n hh σ z u, deriv_VJet_eq_ext n hh σ z' u]; rfl
      rw [hsub]
      exact norm_prod_le_ext hlip.2.1 hlip.2.2
    have hBtδ0 : 0 ≤ max (max B Bc) 1 * δ := mul_nonneg hBt0.le hδ0.le
    have hKnn : 0 ≤ K * ‖z - z'‖ := mul_nonneg hK0.le (norm_nonneg _)
    constructor
    · have hb := (hbox (VJet n h σ z) (VJet n h σ z) u 0 (le_refl 0)
        (contDiff_VJet n hh σ z) (contDiff_VJet n hh σ z) hmemz hmemz hvelz hvelz
        (by simp) (by simp)).2.2.1
      have hb' : |D h z| ≤ C := by
        rw [← hid h hh z (hopen hJz)]; exact hb
      have h2 : C ≤ max (max C0 C1) 1 * max (max B Bc) 1 := by
        refine le_trans hCle ?_
        calc max (max C0 C1) 1 = max (max C0 C1) 1 * 1 := (mul_one _).symm
          _ ≤ max (max C0 C1) 1 * max (max B Bc) 1 :=
              mul_le_mul_of_nonneg_left hBt1 hCc0.le
      exact le_trans (le_of_eq (Real.norm_eq_abs _)) (le_trans hb' h2)
    constructor
    · have hb := (hbox (VJet n h σ z) (VJet n 0 σ z) u (max (max B Bc) 1 * δ) hBtδ0
        (contDiff_VJet n hh σ z) (contDiff_VJet n contDiff_const σ z)
        hmemz hmem0 hvelz hvel0 hclval hclder).2.2.2.2.2
      have hb' : |D h z - D 0 z| ≤ C * (max (max B Bc) 1 * δ) := by
        rw [← hid h hh z (hopen hJz), ← hid 0 contDiff_const z (hopen hJ0)]; exact hb
      have h2 : C * (max (max B Bc) 1 * δ)
          ≤ max (max C0 C1) 1 * max (max B Bc) 1 * δ := by
        calc C * (max (max B Bc) 1 * δ)
            ≤ max (max C0 C1) 1 * (max (max B Bc) 1 * δ) :=
              mul_le_mul_of_nonneg_right hCle hBtδ0
          _ = max (max C0 C1) 1 * max (max B Bc) 1 * δ := by ring
      exact le_trans (le_of_eq (Real.norm_eq_abs _)) (le_trans hb' h2)
    · have hb := (hbox (VJet n h σ z) (VJet n h σ z') u (K * ‖z - z'‖) hKnn
        (contDiff_VJet n hh σ z) (contDiff_VJet n hh σ z')
        hmemz hmemz' hvelz hvelz' hlpval hllder).2.2.2.2.2
      have hb' : |D h z - D h z'| ≤ C * (K * ‖z - z'‖) := by
        rw [← hid h hh z (hopen hJz), ← hid h hh z' (hopen hJz')]; exact hb
      have h2 : C * (K * ‖z - z'‖) ≤ max (max C0 C1) 1 * K * ‖z - z'‖ := by
        calc C * (K * ‖z - z'‖) ≤ max (max C0 C1) 1 * (K * ‖z - z'‖) :=
              mul_le_mul_of_nonneg_right hCle hKnn
          _ = max (max C0 C1) 1 * K * ‖z - z'‖ := by ring
      exact le_trans (le_of_eq (Real.norm_eq_abs _)) (le_trans hb' h2)
  -- ## instantiate at the two rows
  have hC0le : C0 ≤ max (max C0 C1) 1 :=
    le_trans (le_max_left C0 C1) (le_max_left (max C0 C1) 1)
  have hC1le : C1 ≤ max (max C0 C1) 1 :=
    le_trans (le_max_right C0 C1) (le_max_left (max C0 C1) 1)
  have h0 := key (AccF0 n) C0 hC00 hC0le hC0
    (fun g (v : St) =>
      deriv (deriv (fun u' : ℝ => (KvecM n g u' σ (v 0) (v 1) (v 2) (v 3)) 0)) u)
    (fun g gg v hmem => deriv_VJet_AccF0 (n := n) (σ := σ) (u := u) gg v hmem)
  have h1 := key (AccF1 n) C1 hC10 hC1le hC1
    (fun g (v : St) =>
      deriv (deriv (fun u' : ℝ => (KvecM n g u' σ (v 0) (v 1) (v 2) (v 3)) 1)) u)
    (fun g gg v hmem => deriv_VJet_AccF1 (n := n) (σ := σ) (u := u) gg v hmem)
  fin_cases j
  · exact h0
  · exact h1

end

end Work.OddVolterra.WinData
