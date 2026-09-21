import Mathlib
import Submission.Work.OddVolterra.WinData.deriv2_kradlip
import Submission.Work.OddVolterra.Window.JetCurve_box
import Submission.Work.OddVolterra.Window.deriv_deriv_pi
import Submission.Work.OddExistence.Manifest.zrad_sharp

/-!
# The finite jet of the odd Abel kernel on the extended box

The three clauses of the second `u`-derivative estimate for `KvecM` are proved by the jet-curve
lemma `JetCurve_box` applied to the "acceleration functions"
`p ↦ fderiv ℝ KF1 p.1 p.2` and `p ↦ fderiv ℝ Phi2 p.1 p.2` along the jet curves
`u ↦ (KJet n g σ v u, deriv (KJet n g σ v) u)`.

This file sets up the box `Abox`, the acceleration functions, the identification of
`deriv (Acc ∘ V)` with the second `u`-derivative of `KvecM`, and the jet data (bounds,
closeness to `h = 0`, and state-Lipschitz) that `JetCurve_box` consumes.
-/

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

namespace Work.OddVolterra.WinData

noncomputable section

open Work.OddVolterra Work.OddVolterra.Window Work.OddVolterra.KernelExt

set_option maxHeartbeats 1600000

/-! ## The box -/

/-- Lower corner of the box containing the jet on the extended box `u ∈ [3/16,1]`,
`σ ∈ [1/4,1]`. -/
def ALo (n : ℕ) (B : ℝ) : KJIx n → ℝ
  | .aa => 3 / 16
  | .sg => 1 / 4
  | .t1 => -2
  | .t2 => 1 / 5
  | .kd1 => kradLo (3 / 16)
  | .kd2 => kradLo (3 / 16)
  | .c2 => -2
  | .c3 => -2
  | .Z1 _ => -B
  | .Z2 _ => -B
  | .w _ => -1 / 100

/-- Upper corner of the box. -/
def AHi (n : ℕ) (B : ℝ) : KJIx n → ℝ
  | .aa => 1
  | .sg => 1
  | .t1 => -(1 / 5)
  | .t2 => 2
  | .kd1 => 20
  | .kd2 => 20
  | .c2 => 2
  | .c3 => 2
  | .Z1 _ => B
  | .Z2 _ => B
  | .w _ => 1 / 100

/-- The compact box of the jet on the extended region. -/
def Abox (n : ℕ) (B : ℝ) : Set (KJIx n → ℝ) := Set.Icc (ALo n B) (AHi n B)

lemma isCompact_Abox (n : ℕ) (B : ℝ) : IsCompact (Abox n B) := isCompact_Icc
lemma convex_Abox (n : ℕ) (B : ℝ) : Convex ℝ (Abox n B) := convex_Icc _ _

lemma kradLo_two_le_twenty : kradLo (3 / 16 : ℝ) ≤ 20 := by
  rw [kradLo]
  have h : min (2 * (3 / 16) / 5) (7 / 50 : ℝ) ≤ 7 / 50 := min_le_right _ _
  nlinarith

lemma Abox_subset_KJopen (n : ℕ) (B : ℝ) : Abox n B ⊆ KJopen n := by
  intro v hv
  have h1 : ALo n B KJIx.kd1 ≤ v KJIx.kd1 := hv.1 KJIx.kd1
  have h2 : ALo n B KJIx.kd2 ≤ v KJIx.kd2 := hv.1 KJIx.kd2
  simp only [ALo] at h1 h2
  exact ⟨lt_of_lt_of_le (kradLo_pos (by norm_num)) h1,
    lt_of_lt_of_le (kradLo_pos (by norm_num)) h2⟩

/-! ## The acceleration functions -/

/-- The "acceleration" of the first row of `KvecM`: the derivative of `KF1` along the jet, in the
direction of the jet velocity. -/
def AccF0 (n : ℕ) (p : (KJIx n → ℝ) × (KJIx n → ℝ)) : ℝ := fderiv ℝ (KF1 n) p.1 p.2

/-- The "acceleration" of the second row of `KvecM`. -/
def AccF1 (n : ℕ) (p : (KJIx n → ℝ) × (KJIx n → ℝ)) : ℝ := fderiv ℝ (Phi2 n) p.1 p.2

lemma contDiffOn_AccF0 (n : ℕ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (AccF0 n) (KJopen n ×ˢ (Set.univ : Set (KJIx n → ℝ))) := by
  have h1 : ContDiffOn ℝ (⊤ : ℕ∞) (fderiv ℝ (KF1 n)) (KJopen n) :=
    (KvecJet_smooth n).1.fderiv_of_isOpen (isOpen_KJopen n) (le_refl _)
  have h2 : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : (KJIx n → ℝ) × (KJIx n → ℝ) => fderiv ℝ (KF1 n) p.1)
      (KJopen n ×ˢ (Set.univ : Set (KJIx n → ℝ))) :=
    h1.comp contDiffOn_fst (fun p hp => hp.1)
  exact h2.clm_apply contDiffOn_id.snd

lemma contDiffOn_AccF1 (n : ℕ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (AccF1 n) (KJopen n ×ˢ (Set.univ : Set (KJIx n → ℝ))) := by
  have h1 : ContDiffOn ℝ (⊤ : ℕ∞) (fderiv ℝ (Phi2 n)) (KJopen n) :=
    (contDiffOn_Phi2 n).fderiv_of_isOpen (isOpen_KJopen n) (le_refl _)
  have h2 : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : (KJIx n → ℝ) × (KJIx n → ℝ) => fderiv ℝ (Phi2 n) p.1)
      (KJopen n ×ˢ (Set.univ : Set (KJIx n → ℝ))) :=
    h1.comp contDiffOn_fst (fun p hp => hp.1)
  exact h2.clm_apply contDiffOn_id.snd

/-! ## The jet curve -/

/-- The jet curve together with its velocity. -/
def VJet (n : ℕ) (g : ℝ → ℝ) (σ : ℝ) (v : St) (u : ℝ) :
    (KJIx n → ℝ) × (KJIx n → ℝ) :=
  (KJet n g σ v u, deriv (fun u' : ℝ => KJet n g σ v u') u)

lemma contDiff_VJet (n : ℕ) {g : ℝ → ℝ} (gg : ContDiff ℝ (⊤ : ℕ∞) g) (σ : ℝ) (v : St) :
    ContDiff ℝ (⊤ : ℕ∞) (VJet n g σ v) := by
  have hJ : ContDiff ℝ (⊤ : ℕ∞) (fun u : ℝ => KJet n g σ v u) := contDiff_KJet n gg σ v
  have hJ1 : ContDiff ℝ (⊤ : ℕ∞) (deriv (fun u : ℝ => KJet n g σ v u)) :=
    ContDiff.iterate_deriv 1 hJ
  exact hJ.prodMk hJ1

/-! ## The identification of the acceleration with the second derivative -/

lemma deriv_VJet_AccF0 {n : ℕ} {g : ℝ → ℝ} (gg : ContDiff ℝ (⊤ : ℕ∞) g)
    {σ u : ℝ} (v : St) (hu : KJet n g σ v u ∈ KJopen n) :
    deriv (fun x : ℝ => AccF0 n (VJet n g σ v x)) u
      = deriv (deriv (fun u' : ℝ => (KvecM n g u' σ (v 0) (v 1) (v 2) (v 3)) 0)) u := by
  have hJ : ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ => KJet n g σ v x) := contDiff_KJet n gg σ v
  have hev : (fun x : ℝ => AccF0 n (VJet n g σ v x))
      =ᶠ[𝓝 u] deriv (fun x : ℝ => KF1 n (KJet n g σ v x)) := by
    have hmem : ∀ᶠ x in 𝓝 u, KJet n g σ v x ∈ KJopen n :=
      hJ.continuous.continuousAt.eventually ((isOpen_KJopen n).mem_nhds hu)
    filter_upwards [hmem] with x hx
    have hphi : DifferentiableAt ℝ (fun w : KJIx n → ℝ => KF1 n w) (KJet n g σ v x) :=
      ((KvecJet_smooth n).1.differentiableOn (by simp)).differentiableAt
        ((isOpen_KJopen n).mem_nhds hx)
    have hd : DifferentiableAt ℝ (fun y : ℝ => KJet n g σ v y) x :=
      (hJ.differentiable (by simp)).differentiableAt
    have hchain := (hphi.hasFDerivAt.comp_hasDerivAt x hd.hasDerivAt).deriv
    rw [AccF0, VJet]
    exact hchain.symm
  rw [Filter.EventuallyEq.deriv_eq hev]
  have hid : (fun x : ℝ => KF1 n (KJet n g σ v x))
      = fun x : ℝ => (KvecM n g x σ (v 0) (v 1) (v 2) (v 3)) 0 := by
    funext x; exact (KvecM_row0 n gg x σ v).symm
  rw [hid]

lemma deriv_VJet_AccF1 {n : ℕ} {g : ℝ → ℝ} (gg : ContDiff ℝ (⊤ : ℕ∞) g)
    {σ u : ℝ} (v : St) (hu : KJet n g σ v u ∈ KJopen n) :
    deriv (fun x : ℝ => AccF1 n (VJet n g σ v x)) u
      = deriv (deriv (fun u' : ℝ => (KvecM n g u' σ (v 0) (v 1) (v 2) (v 3)) 1)) u := by
  have hJ : ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ => KJet n g σ v x) := contDiff_KJet n gg σ v
  have hev : (fun x : ℝ => AccF1 n (VJet n g σ v x))
      =ᶠ[𝓝 u] deriv (fun x : ℝ => Phi2 n (KJet n g σ v x)) := by
    have hmem : ∀ᶠ x in 𝓝 u, KJet n g σ v x ∈ KJopen n :=
      hJ.continuous.continuousAt.eventually ((isOpen_KJopen n).mem_nhds hu)
    filter_upwards [hmem] with x hx
    have hphi : DifferentiableAt ℝ (fun w : KJIx n → ℝ => Phi2 n w) (KJet n g σ v x) :=
      ((contDiffOn_Phi2 n).differentiableOn (by simp)).differentiableAt
        ((isOpen_KJopen n).mem_nhds hx)
    have hd : DifferentiableAt ℝ (fun y : ℝ => KJet n g σ v y) x :=
      (hJ.differentiable (by simp)).differentiableAt
    have hchain := (hphi.hasFDerivAt.comp_hasDerivAt x hd.hasDerivAt).deriv
    rw [AccF1, VJet]
    exact hchain.symm
  rw [Filter.EventuallyEq.deriv_eq hev]
  have hid : (fun x : ℝ => Phi2 n (KJet n g σ v x))
      = fun x : ℝ => (KvecM n g x σ (v 0) (v 1) (v 2) (v 3)) 1 := by
    funext x; exact (KvecM_row1 n gg x σ v).symm
  rw [hid]

/-! ## Norm bounds from componentwise bounds -/

lemma norm_deriv_Jet_le {n : ℕ} {g : ℝ → ℝ} (gg : ContDiff ℝ (⊤ : ℕ∞) g) (σ : ℝ) (v : St)
    (u : ℝ) {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ i : KJIx n, |deriv (fun u' : ℝ => KJet n g σ v u' i) u| ≤ B) :
    ‖deriv (fun u' : ℝ => KJet n g σ v u') u‖ ≤ B := by
  have hJ : ContDiff ℝ (⊤ : ℕ∞) (fun u' : ℝ => KJet n g σ v u') := contDiff_KJet n gg σ v
  have hdiff : ∀ i : KJIx n, DifferentiableAt ℝ (fun u' : ℝ => KJet n g σ v u' i) u :=
    fun i => (differentiableAt_pi.mp (hJ.differentiable (by simp)).differentiableAt) i
  rw [deriv_pi (𝕜 := ℝ) (x := u) (φ := fun u' : ℝ => KJet n g σ v u') hdiff]
  rw [← dist_zero_right, dist_pi_le_iff hB]
  intro i
  rw [Real.dist_eq, Pi.zero_apply, sub_zero]
  exact h i

lemma norm_deriv2_Jet_le {n : ℕ} {g : ℝ → ℝ} (gg : ContDiff ℝ (⊤ : ℕ∞) g) (σ : ℝ) (v : St)
    (u : ℝ) {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ i : KJIx n, |deriv (deriv (fun u' : ℝ => KJet n g σ v u' i)) u| ≤ B) :
    ‖deriv (deriv (fun u' : ℝ => KJet n g σ v u')) u‖ ≤ B := by
  have hJ : ContDiff ℝ (⊤ : ℕ∞) (fun u' : ℝ => KJet n g σ v u') := contDiff_KJet n gg σ v
  rw [deriv_deriv_pi (hJ.contDiffAt.of_le (Work.OddExistence.Manifest.AW.natCast_le_top_enat 2))]
  rw [← dist_zero_right, dist_pi_le_iff hB]
  intro i
  rw [Real.dist_eq, Pi.zero_apply, sub_zero]
  exact h i

/-! ## The jet data: bounds -/

/-- **Bounds for the jet curve `KJet` and its first two `u`-derivatives** on the extended box. -/
theorem KJet_bounds_ext (n : ℕ) (hn : 1 ≤ n) :
    ∃ B : ℝ, 0 < B ∧
      ∀ (g : ℝ → ℝ) (gg : ContDiff ℝ (⊤ : ℕ∞) g)
        (gj : ∀ k : ℕ, k ≤ n + 3 → ∀ s : ℝ, |iteratedDeriv k g s| ≤ 1 / 100)
        (gsupp : Function.support g ⊆ Set.Icc (1 - 2 * tau) (1 - tau))
        (σ : ℝ) (hσ : σ ∈ Set.Icc (1 / 4 : ℝ) 1)
        (v : St) (hv0 : (1 / 5 : ℝ) ≤ v 0) (hv1 : (1 / 5 : ℝ) ≤ v 1)
        (hvb : ∀ i : Fin 4, |v i| ≤ 2) (u : ℝ) (hu : u ∈ Set.Icc (3 / 16 : ℝ) 1),
        KJet n g σ v u ∈ Abox n B ∧
        ‖deriv (fun u' : ℝ => KJet n g σ v u') u‖ ≤ B ∧
        ‖deriv (deriv (fun u' : ℝ => KJet n g σ v u')) u‖ ≤ B := by
  obtain ⟨Bz, hBz0, hZ⟩ := Work.OddExistence.Manifest.ZS.Zrad_jet_bounds_sharp (n + 1)
  obtain ⟨Kk, hKk0, hKk⟩ := krad_deriv2_ext
  refine ⟨max (max Bz 20) Kk, lt_of_lt_of_le (by norm_num : (0 : ℝ) < 20)
    (le_trans (le_max_right Bz 20) (le_max_left (max Bz 20) Kk)), ?_⟩
  intro g gg gj gsupp σ hσ v hv0 hv1 hvb u hu
  have hB0 : (0 : ℝ) ≤ max (max Bz 20) Kk :=
    le_trans hKk0 (le_max_right _ _)
  have hB20 : (20 : ℝ) ≤ max (max Bz 20) Kk :=
    le_trans (le_max_right Bz 20) (le_max_left (max Bz 20) Kk)
  have hBBz : Bz ≤ max (max Bz 20) Kk :=
    le_trans (le_max_left Bz 20) (le_max_left (max Bz 20) Kk)
  have hBKk : Kk ≤ max (max Bz 20) Kk := le_max_right _ _
  have hv0abs : |-(v 0)| ≤ 2 := by rw [abs_neg]; exact hvb 0
  have hv0ge : (1 / 5 : ℝ) ≤ |-(v 0)| := by rw [abs_neg, abs_of_nonneg (by linarith)]; exact hv0
  have hv1abs : |v 1| ≤ 2 := hvb 1
  have hv1ge : (1 / 5 : ℝ) ≤ |v 1| := by rw [abs_of_nonneg (by linarith)]; exact hv1
  -- krad data
  have hk1 := krad_jets_ext (h := g) gg gsupp (by norm_num) (by norm_num)
    (fun k hk s => gj k (by omega) s) (A := (3 / 16 : ℝ)) (a := u) (σ := σ) (t := -(v 0))
    (by norm_num) (by linarith [hu.1]) (by linarith [hσ.1]) hσ.2 (by linarith [hu.2]) hv0ge hv0abs
  have hk2 := krad_jets_ext (h := g) gg gsupp (by norm_num) (by norm_num)
    (fun k hk s => gj k (by omega) s) (A := (3 / 16 : ℝ)) (a := u) (σ := σ) (t := v 1)
    (by norm_num) (by linarith [hu.1]) (by linarith [hσ.1]) hσ.2 (by linarith [hu.2]) hv1ge hv1abs
  have hk1d := hKk g (1 / 100 : ℝ) u σ gg
    (by norm_num) (by norm_num) (fun k hk s => gj k (by omega) s) hu hσ (-(v 0)) hv0ge hv0abs
  have hk2d := hKk g (1 / 100 : ℝ) u σ gg
    (by norm_num) (by norm_num) (fun k hk s => gj k (by omega) s) hu hσ (v 1) hv1ge hv1abs
  have hZb : ∀ (t : ℝ) (j : ℕ), |t| ≤ 2 → j ≤ n + 3 →
      |iteratedDeriv j (fun w : ℝ => KernelExt.Zrad g (w, σ, t)) u| ≤ Bz := by
    intro t j ht hj
    exact (hZ g (1 / 100 : ℝ) gg (by norm_num) (by norm_num)
      (fun k hk s => gj k (by omega) s) σ ⟨by linarith [hσ.1], hσ.2⟩ t ht
      u ⟨by linarith [hu.1], hu.2⟩).1 j hj
  have hZeq : ∀ (t : ℝ) (k : ℕ) (u' : ℝ), kjet g σ t u' k
      = iteratedDeriv k (fun w : ℝ => KernelExt.Zrad g (w, σ, t)) u' :=
    fun t k u' => kjet_eq_Zrad (gg.of_le (by norm_num)) σ t u' k
  have hbox : ∀ i : KJIx n, ALo n (max (max Bz 20) Kk) i ≤ KJet n g σ v u i ∧
      KJet n g σ v u i ≤ AHi n (max (max Bz 20) Kk) i := by
    intro i
    cases i with
    | aa => simp only [KJet_aa, ALo, AHi]; exact ⟨hu.1, hu.2⟩
    | sg => simp only [KJet_sg, ALo, AHi]; exact ⟨hσ.1, hσ.2⟩
    | t1 =>
      simp only [KJet_t1, ALo, AHi]
      exact ⟨by linarith [(abs_le.mp (hvb 0)).2], by linarith [hv0]⟩
    | t2 =>
      simp only [KJet_t2, ALo, AHi]
      exact ⟨hv1, (abs_le.mp (hvb 1)).2⟩
    | kd1 => simp only [KJet_kd1, ALo, AHi]; exact ⟨hk1.1, hk1.2.1⟩
    | kd2 => simp only [KJet_kd2, ALo, AHi]; exact ⟨hk2.1, hk2.2.1⟩
    | c2 =>
      simp only [KJet_c2, ALo, AHi]
      exact ⟨(abs_le.mp (hvb 2)).1, (abs_le.mp (hvb 2)).2⟩
    | c3 =>
      simp only [KJet_c3, ALo, AHi]
      exact ⟨(abs_le.mp (hvb 3)).1, (abs_le.mp (hvb 3)).2⟩
    | Z1 k =>
      simp only [KJet_Z1, ALo, AHi]
      rw [hZeq (-(v 0)) k.1 u]
      have h := hZb (-(v 0)) k.1 hv0abs (by have := k.2; omega)
      rw [abs_le] at h
      exact ⟨by linarith [h.1, hBBz], by linarith [h.2, hBBz]⟩
    | Z2 k =>
      simp only [KJet_Z2, ALo, AHi]
      rw [hZeq (v 1) k.1 u]
      have h := hZb (v 1) k.1 hv1abs (by have := k.2; omega)
      rw [abs_le] at h
      exact ⟨by linarith [h.1, hBBz], by linarith [h.2, hBBz]⟩
    | w j =>
      simp only [KJet_w, ALo, AHi]
      have h : |iteratedDeriv (j.1 + 1) g u| ≤ 1 / 100 := gj (j.1 + 1) (by have := j.2; omega) u
      rw [abs_le] at h
      exact ⟨by linarith [h.1], h.2⟩
  constructor
  · exact ⟨fun i => (hbox i).1, fun i => (hbox i).2⟩
  · constructor
    · -- first derivative
      refine norm_deriv_Jet_le gg σ v u hB0 (fun i => ?_)
      cases i with
      | aa => simp only [KJet_aa]; norm_num [hB20]
      | sg => simp only [KJet_sg]; simpa using hB0
      | t1 => simp only [KJet_t1]; simpa using hB0
      | t2 => simp only [KJet_t2]; simpa using hB0
      | kd1 =>
        simp only [KJet_kd1]
        exact le_trans hk1.2.2.2.1 hB20
      | kd2 =>
        simp only [KJet_kd2]
        exact le_trans hk2.2.2.2.1 hB20
      | c2 => simp only [KJet_c2]; simpa using hB0
      | c3 => simp only [KJet_c3]; simpa using hB0
      | Z1 k =>
        simp only [KJet_Z1]
        have hfun : (fun u' : ℝ => kjet g σ (-(v 0)) u' k.1)
            = fun u' : ℝ => iteratedDeriv k.1 (fun w : ℝ => KernelExt.Zrad g (w, σ, -(v 0))) u' := by
          funext u'; exact hZeq (-(v 0)) k.1 u'
        have he : deriv (fun u' : ℝ => kjet g σ (-(v 0)) u' k.1) u
            = iteratedDeriv (k.1 + 1) (fun w : ℝ => KernelExt.Zrad g (w, σ, -(v 0))) u := by
          rw [hfun, ← iteratedDeriv_succ]
        rw [he]
        exact le_trans (hZb (-(v 0)) (k.1 + 1) hv0abs (by have := k.2; omega)) hBBz
      | Z2 k =>
        simp only [KJet_Z2]
        have hfun : (fun u' : ℝ => kjet g σ (v 1) u' k.1)
            = fun u' : ℝ => iteratedDeriv k.1 (fun w : ℝ => KernelExt.Zrad g (w, σ, v 1)) u' := by
          funext u'; exact hZeq (v 1) k.1 u'
        have he : deriv (fun u' : ℝ => kjet g σ (v 1) u' k.1) u
            = iteratedDeriv (k.1 + 1) (fun w : ℝ => KernelExt.Zrad g (w, σ, v 1)) u := by
          rw [hfun, ← iteratedDeriv_succ]
        rw [he]
        exact le_trans (hZb (v 1) (k.1 + 1) hv1abs (by have := k.2; omega)) hBBz
      | w j =>
        simp only [KJet_w]
        have he : deriv (fun u' : ℝ => iteratedDeriv (j.1 + 1) g u') u
            = iteratedDeriv (j.1 + 1 + 1) g u := by rw [← iteratedDeriv_succ]
        rw [he]
        exact le_trans (gj (j.1 + 2) (by have := j.2; omega) u)
          (le_trans (by norm_num) hB20)
    · -- second derivative
      refine norm_deriv2_Jet_le gg σ v u hB0 (fun i => ?_)
      cases i with
      | aa => simp only [KJet_aa]; simpa using hB0
      | sg => simp only [KJet_sg]; simpa using hB0
      | t1 => simp only [KJet_t1]; simpa using hB0
      | t2 => simp only [KJet_t2]; simpa using hB0
      | kd1 =>
        simp only [KJet_kd1]
        exact le_trans (le_trans hk1d.1 (by linarith [hKk0])) hBKk
      | kd2 =>
        simp only [KJet_kd2]
        exact le_trans (le_trans hk2d.1 (by linarith [hKk0])) hBKk
      | c2 => simp only [KJet_c2]; simpa using hB0
      | c3 => simp only [KJet_c3]; simpa using hB0
      | Z1 k =>
        simp only [KJet_Z1]
        have hfun : (fun u' : ℝ => kjet g σ (-(v 0)) u' k.1)
            = fun u' : ℝ => iteratedDeriv k.1 (fun w : ℝ => KernelExt.Zrad g (w, σ, -(v 0))) u' := by
          funext u'; exact hZeq (-(v 0)) k.1 u'
        have hfun2 : deriv (deriv (fun u' : ℝ => iteratedDeriv k.1
              (fun w : ℝ => KernelExt.Zrad g (w, σ, -(v 0))) u'))
              = iteratedDeriv (k.1 + 2) (fun w : ℝ => KernelExt.Zrad g (w, σ, -(v 0))) := by
          funext x
          rw [← iteratedDeriv_succ, ← iteratedDeriv_succ]
        have he : deriv (deriv (fun u' : ℝ => kjet g σ (-(v 0)) u' k.1)) u
            = iteratedDeriv (k.1 + 2) (fun w : ℝ => KernelExt.Zrad g (w, σ, -(v 0))) u := by
          rw [hfun, hfun2]
        rw [he]
        exact le_trans (hZb (-(v 0)) (k.1 + 2) hv0abs (by have := k.2; omega)) hBBz
      | Z2 k =>
        simp only [KJet_Z2]
        have hfun : (fun u' : ℝ => kjet g σ (v 1) u' k.1)
            = fun u' : ℝ => iteratedDeriv k.1 (fun w : ℝ => KernelExt.Zrad g (w, σ, v 1)) u' := by
          funext u'; exact hZeq (v 1) k.1 u'
        have hfun2 : deriv (deriv (fun u' : ℝ => iteratedDeriv k.1
              (fun w : ℝ => KernelExt.Zrad g (w, σ, v 1)) u'))
              = iteratedDeriv (k.1 + 2) (fun w : ℝ => KernelExt.Zrad g (w, σ, v 1)) := by
          funext x
          rw [← iteratedDeriv_succ, ← iteratedDeriv_succ]
        have he : deriv (deriv (fun u' : ℝ => kjet g σ (v 1) u' k.1)) u
            = iteratedDeriv (k.1 + 2) (fun w : ℝ => KernelExt.Zrad g (w, σ, v 1)) u := by
          rw [hfun, hfun2]
        rw [he]
        exact le_trans (hZb (v 1) (k.1 + 2) hv1abs (by have := k.2; omega)) hBBz
      | w j =>
        simp only [KJet_w]
        have h1 : deriv (fun u' : ℝ => iteratedDeriv (j.1 + 1) g u')
            = iteratedDeriv (j.1 + 2) g := by rw [← iteratedDeriv_succ]
        have he : deriv (deriv (fun u' : ℝ => iteratedDeriv (j.1 + 1) g u')) u
            = iteratedDeriv (j.1 + 3) g u := by rw [h1, ← iteratedDeriv_succ]
        rw [he]
        exact le_trans (gj (j.1 + 3) (by have := j.2; omega) u)
          (le_trans (by norm_num) hB20)

lemma deriv_deriv_const_fun (c x : ℝ) : deriv (deriv (fun _ : ℝ => c)) x = 0 := by
  have h : deriv (fun _ : ℝ => c) = fun _ : ℝ => (0 : ℝ) := by funext y; simp
  rw [h]; simp

lemma iteratedDeriv_zero_fun (k : ℕ) (x : ℝ) : iteratedDeriv k (0 : ℝ → ℝ) x = 0 := by
  rw [show (0 : ℝ → ℝ) = fun _ : ℝ => (0 : ℝ) from rfl, iteratedDeriv_const]
  split_ifs <;> simp

/-! ## The jet data: closeness to `h = 0` -/

/-- Norm bound for a difference of jets from a componentwise bound. -/
lemma norm_sub_le_of_component {n : ℕ} {x y : KJIx n → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ i : KJIx n, |x i - y i| ≤ B) : ‖x - y‖ ≤ B := by
  rw [← dist_eq_norm, dist_pi_le_iff hB]
  intro i
  rw [Real.dist_eq]
  exact h i

/-- **Closeness of the jet curve to the unperturbed one**, on the extended box. -/
theorem KJet_close_ext (n : ℕ) (hn : 1 ≤ n) :
    ∃ B : ℝ, 0 < B ∧
      ∀ (h : ℝ → ℝ) (hh : ContDiff ℝ (⊤ : ℕ∞) h) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 100)
        (hj : ∀ k : ℕ, k ≤ n + 3 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ δ)
        (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * tau) (1 - tau))
        (σ : ℝ) (hσ : σ ∈ Set.Icc (1 / 4 : ℝ) 1)
        (v : St) (hv0 : (1 / 5 : ℝ) ≤ v 0) (hv1 : (1 / 5 : ℝ) ≤ v 1)
        (hvb : ∀ i : Fin 4, |v i| ≤ 2) (u : ℝ) (hu : u ∈ Set.Icc (3 / 16 : ℝ) 1),
        ‖KJet n h σ v u - KJet n 0 σ v u‖ ≤ B * δ ∧
        ‖deriv (fun u' : ℝ => KJet n h σ v u') u -
          deriv (fun u' : ℝ => KJet n 0 σ v u') u‖ ≤ B * δ ∧
        ‖deriv (deriv (fun u' : ℝ => KJet n h σ v u')) u -
          deriv (deriv (fun u' : ℝ => KJet n 0 σ v u')) u‖ ≤ B * δ := by
  obtain ⟨Bz, hBz0, hZ⟩ := Work.OddExistence.Manifest.ZS.Zrad_jet_bounds_sharp (n + 1)
  obtain ⟨Kk, hKk0, hKk⟩ := krad_deriv2_ext
  refine ⟨max (max (3 * Bz) 20) (max 1 Kk), ?_, ?_⟩
  · have : (0:ℝ) < 20 := by norm_num
    exact lt_of_lt_of_le this (le_trans (le_max_right _ 20) (le_max_left _ _))
  intro h hh δ hδ0 hδ1 hj hsupp σ hσ v hv0 hv1 hvb u hu
  have hδ0' : 0 ≤ δ := hδ0.le
  have hv0abs : |-(v 0)| ≤ 2 := by rw [abs_neg]; exact hvb 0
  have hv0ge : (1 / 5 : ℝ) ≤ |-(v 0)| := by rw [abs_neg, abs_of_nonneg (by linarith)]; exact hv0
  have hv1abs : |v 1| ≤ 2 := hvb 1
  have hv1ge : (1 / 5 : ℝ) ≤ |v 1| := by rw [abs_of_nonneg (by linarith)]; exact hv1
  have hB0 : (0 : ℝ) ≤ max (max (3 * Bz) 20) (max 1 Kk) := by positivity
  have hB20 : (20 : ℝ) ≤ max (max (3 * Bz) 20) (max 1 Kk) :=
    le_trans (le_max_right _ 20) (le_max_left _ _)
  have hB3z : 3 * Bz ≤ max (max (3 * Bz) 20) (max 1 Kk) :=
    le_trans (le_max_left _ 20) (le_max_left _ _)
  have hBKk : Kk ≤ max (max (3 * Bz) 20) (max 1 Kk) := le_trans (le_max_right _ _) (le_max_right _ _)
  have hB1 : (1 : ℝ) ≤ max (max (3 * Bz) 20) (max 1 Kk) :=
    le_trans (le_max_left _ _) (le_max_right _ _)
  have hδ1' : δ ≤ 1 := by linarith
  -- krad data
  have hk1 := krad_jets_ext (h := h) hh hsupp hδ0 hδ1 (fun k hk s => hj k (by omega) s)
    (A := (3 / 16 : ℝ)) (a := u) (σ := σ) (t := -(v 0))
    (by norm_num) (by linarith [hu.1]) (by linarith [hσ.1]) hσ.2 (by linarith [hu.2]) hv0ge hv0abs
  have hk2 := krad_jets_ext (h := h) hh hsupp hδ0 hδ1 (fun k hk s => hj k (by omega) s)
    (A := (3 / 16 : ℝ)) (a := u) (σ := σ) (t := v 1)
    (by norm_num) (by linarith [hu.1]) (by linarith [hσ.1]) hσ.2 (by linarith [hu.2]) hv1ge hv1abs
  have hk1d := hKk h δ u σ hh hδ0 hδ1 (fun k hk s => hj k (by omega) s) hu hσ (-(v 0)) hv0ge hv0abs
  have hk2d := hKk h δ u σ hh hδ0 hδ1 (fun k hk s => hj k (by omega) s) hu hσ (v 1) hv1ge hv1abs
  have hZc : ∀ (t : ℝ) (j : ℕ), |t| ≤ 2 → j ≤ n + 3 →
      |iteratedDeriv j (fun w : ℝ => KernelExt.Zrad h (w, σ, t)) u -
       iteratedDeriv j (fun w : ℝ => KernelExt.Zrad 0 (w, σ, t)) u| ≤ 3 * Bz * δ := by
    intro t j ht hj'
    have h := (hZ h δ hh hδ0' hδ1' (fun k hk s => hj k (by omega) s) σ ⟨by linarith [hσ.1], hσ.2⟩
      t ht u ⟨by linarith [hu.1], hu.2⟩).2 j hj'
    refine le_trans h ?_
    have ht3 : |t| + δ ≤ 3 := by linarith [ht, hδ1]
    have hδB : (0:ℝ) ≤ Bz * δ := mul_nonneg hBz0 hδ0'
    calc Bz * δ * (|t| + δ) ≤ Bz * δ * 3 := mul_le_mul_of_nonneg_left ht3 hδB
      _ = 3 * Bz * δ := by ring
  have hZeq : ∀ (t : ℝ) (k : ℕ) (u' : ℝ), kjet h σ t u' k
      = iteratedDeriv k (fun w : ℝ => KernelExt.Zrad h (w, σ, t)) u' :=
    fun t k u' => kjet_eq_Zrad (hh.of_le (by norm_num)) σ t u' k
  have hZeq0 : ∀ (t : ℝ) (k : ℕ) (u' : ℝ), kjet 0 σ t u' k
      = iteratedDeriv k (fun w : ℝ => KernelExt.Zrad 0 (w, σ, t)) u' :=
    fun t k u' => kjet_eq_Zrad ((contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (0 : ℝ → ℝ)).of_le
      (by norm_num)) σ t u' k
  -- componentwise differences: values
  have hV : ∀ i : KJIx n, |KJet n h σ v u i - KJet n 0 σ v u i| ≤
      max (max (3 * Bz) 20) (max 1 Kk) * δ := by
    intro i
    cases i with
    | aa => simp only [KJet_aa]; rw [sub_self, abs_zero]; positivity
    | sg => simp only [KJet_sg]; rw [sub_self, abs_zero]; positivity
    | t1 => simp only [KJet_t1]; rw [sub_self, abs_zero]; positivity
    | t2 => simp only [KJet_t2]; rw [sub_self, abs_zero]; positivity
    | kd1 =>
      simp only [KJet_kd1]
      exact le_trans hk1.2.2.1 (mul_le_mul_of_nonneg_right hB20 hδ0')
    | kd2 =>
      simp only [KJet_kd2]
      exact le_trans hk2.2.2.1 (mul_le_mul_of_nonneg_right hB20 hδ0')
    | c2 => simp only [KJet_c2]; rw [sub_self, abs_zero]; positivity
    | c3 => simp only [KJet_c3]; rw [sub_self, abs_zero]; positivity
    | Z1 k =>
      simp only [KJet_Z1]
      rw [hZeq (-(v 0)) k.1 u, hZeq0 (-(v 0)) k.1 u]
      have h := hZc (-(v 0)) k.1 hv0abs (by have := k.2; omega)
      refine le_trans h ?_
      nlinarith [hB3z, hδ0']
    | Z2 k =>
      simp only [KJet_Z2]
      rw [hZeq (v 1) k.1 u, hZeq0 (v 1) k.1 u]
      have h := hZc (v 1) k.1 hv1abs (by have := k.2; omega)
      refine le_trans h ?_
      nlinarith [hB3z, hδ0']
    | w j =>
      simp only [KJet_w]
      rw [iteratedDeriv_zero_fun, sub_zero]
      exact le_trans (hj (j.1 + 1) (by have := j.2; omega) u)
        (by nlinarith [hB1, hδ0'])
  constructor
  · exact norm_sub_le_of_component (by positivity) hV
  · constructor
    · -- first derivative
      have hD : ∀ i : KJIx n,
          |deriv (fun u' : ℝ => KJet n h σ v u' i) u -
           deriv (fun u' : ℝ => KJet n 0 σ v u' i) u| ≤ max (max (3 * Bz) 20) (max 1 Kk) * δ := by
        intro i
        cases i with
        | aa => simp only [KJet_aa, deriv_id'']; rw [sub_self, abs_zero]; positivity
        | sg => simp only [KJet_sg, deriv_const, deriv_deriv_const_fun, sub_self, abs_zero]; positivity
        | t1 => simp only [KJet_t1, deriv_const, deriv_deriv_const_fun, sub_self, abs_zero]; positivity
        | t2 => simp only [KJet_t2, deriv_const, deriv_deriv_const_fun, sub_self, abs_zero]; positivity
        | kd1 =>
          simp only [KJet_kd1]
          exact le_trans hk1.2.2.2.2.2 (mul_le_mul_of_nonneg_right hB20 hδ0')
        | kd2 =>
          simp only [KJet_kd2]
          exact le_trans hk2.2.2.2.2.2 (mul_le_mul_of_nonneg_right hB20 hδ0')
        | c2 => simp only [KJet_c2, deriv_const, deriv_deriv_const_fun, sub_self, abs_zero]; positivity
        | c3 => simp only [KJet_c3, deriv_const, deriv_deriv_const_fun, sub_self, abs_zero]; positivity
        | Z1 k =>
          simp only [KJet_Z1]
          have hfun : (fun u' : ℝ => kjet h σ (-(v 0)) u' k.1)
              = fun u' : ℝ => iteratedDeriv k.1 (fun w : ℝ => KernelExt.Zrad h (w, σ, -(v 0))) u' := by
            funext u'; exact hZeq (-(v 0)) k.1 u'
          have hfun0 : (fun u' : ℝ => kjet 0 σ (-(v 0)) u' k.1)
              = fun u' : ℝ => iteratedDeriv k.1 (fun w : ℝ => KernelExt.Zrad 0 (w, σ, -(v 0))) u' := by
            funext u'; exact hZeq0 (-(v 0)) k.1 u'
          rw [hfun, hfun0, ← iteratedDeriv_succ, ← iteratedDeriv_succ]
          have h := hZc (-(v 0)) (k.1 + 1) hv0abs (by have := k.2; omega)
          refine le_trans h ?_
          nlinarith [hB3z, hδ0']
        | Z2 k =>
          simp only [KJet_Z2]
          have hfun : (fun u' : ℝ => kjet h σ (v 1) u' k.1)
              = fun u' : ℝ => iteratedDeriv k.1 (fun w : ℝ => KernelExt.Zrad h (w, σ, v 1)) u' := by
            funext u'; exact hZeq (v 1) k.1 u'
          have hfun0 : (fun u' : ℝ => kjet 0 σ (v 1) u' k.1)
              = fun u' : ℝ => iteratedDeriv k.1 (fun w : ℝ => KernelExt.Zrad 0 (w, σ, v 1)) u' := by
            funext u'; exact hZeq0 (v 1) k.1 u'
          rw [hfun, hfun0, ← iteratedDeriv_succ, ← iteratedDeriv_succ]
          have h := hZc (v 1) (k.1 + 1) hv1abs (by have := k.2; omega)
          refine le_trans h ?_
          nlinarith [hB3z, hδ0']
        | w j =>
          simp only [KJet_w]
          have h1 : deriv (fun u' : ℝ => iteratedDeriv (j.1 + 1) h u')
              = iteratedDeriv (j.1 + 1 + 1) h := by rw [← iteratedDeriv_succ]
          have h10 : deriv (fun u' : ℝ => iteratedDeriv (j.1 + 1) (0 : ℝ → ℝ) u')
              = iteratedDeriv (j.1 + 1 + 1) (0 : ℝ → ℝ) := by rw [← iteratedDeriv_succ]
          rw [h1, h10, iteratedDeriv_zero_fun, sub_zero]
          exact le_trans (hj (j.1 + 2) (by have := j.2; omega) u) (by nlinarith [hB1, hδ0'])
      rw [← dist_eq_norm, dist_pi_le_iff (by positivity : (0 : ℝ) ≤
        max (max (3 * Bz) 20) (max 1 Kk) * δ)]
      intro i
      rw [Real.dist_eq]
      have hJh : ∀ i : KJIx n, DifferentiableAt ℝ (fun u' : ℝ => KJet n h σ v u' i) u :=
        fun i => (differentiableAt_pi.mp (((contDiff_KJet n hh σ v).differentiable (by simp))
          ).differentiableAt) i
      have hJ0 : ∀ i : KJIx n, DifferentiableAt ℝ (fun u' : ℝ => KJet n 0 σ v u' i) u :=
        fun i => (differentiableAt_pi.mp (((contDiff_KJet n contDiff_const σ v).differentiable
          (by simp))).differentiableAt) i
      rw [deriv_pi (𝕜 := ℝ) (x := u) (φ := fun u' : ℝ => KJet n h σ v u') hJh,
        deriv_pi (𝕜 := ℝ) (x := u) (φ := fun u' : ℝ => KJet n 0 σ v u') hJ0]
      exact hD i
    · -- second derivative
      have hD2 : ∀ i : KJIx n,
          |deriv (deriv (fun u' : ℝ => KJet n h σ v u' i)) u -
           deriv (deriv (fun u' : ℝ => KJet n 0 σ v u' i)) u| ≤
            max (max (3 * Bz) 20) (max 1 Kk) * δ := by
        intro i
        cases i with
        | aa => simp only [KJet_aa]; rw [sub_self, abs_zero]; positivity
        | sg => simp only [KJet_sg]; rw [sub_self, abs_zero]; positivity
        | t1 => simp only [KJet_t1, deriv_const, deriv_deriv_const_fun, sub_self, abs_zero]; positivity
        | t2 => simp only [KJet_t2, deriv_const, deriv_deriv_const_fun, sub_self, abs_zero]; positivity
        | kd1 =>
          simp only [KJet_kd1]
          exact le_trans hk1d.2 (mul_le_mul_of_nonneg_right hBKk hδ0')
        | kd2 =>
          simp only [KJet_kd2]
          exact le_trans hk2d.2 (mul_le_mul_of_nonneg_right hBKk hδ0')
        | c2 => simp only [KJet_c2, deriv_const, deriv_deriv_const_fun, sub_self, abs_zero]; positivity
        | c3 => simp only [KJet_c3, deriv_const, deriv_deriv_const_fun, sub_self, abs_zero]; positivity
        | Z1 k =>
          simp only [KJet_Z1]
          have hfun : (fun u' : ℝ => kjet h σ (-(v 0)) u' k.1)
              = fun u' : ℝ => iteratedDeriv k.1 (fun w : ℝ => KernelExt.Zrad h (w, σ, -(v 0))) u' := by
            funext u'; exact hZeq (-(v 0)) k.1 u'
          have hfun0 : (fun u' : ℝ => kjet 0 σ (-(v 0)) u' k.1)
              = fun u' : ℝ => iteratedDeriv k.1 (fun w : ℝ => KernelExt.Zrad 0 (w, σ, -(v 0))) u' := by
            funext u'; exact hZeq0 (-(v 0)) k.1 u'
          have hfun2 : deriv (deriv (fun u' : ℝ => iteratedDeriv k.1
              (fun w : ℝ => KernelExt.Zrad h (w, σ, -(v 0))) u'))
              = iteratedDeriv (k.1 + 2) (fun w : ℝ => KernelExt.Zrad h (w, σ, -(v 0))) := by
            funext x; rw [← iteratedDeriv_succ, ← iteratedDeriv_succ]
          have hfun20 : deriv (deriv (fun u' : ℝ => iteratedDeriv k.1
              (fun w : ℝ => KernelExt.Zrad 0 (w, σ, -(v 0))) u'))
              = iteratedDeriv (k.1 + 2) (fun w : ℝ => KernelExt.Zrad 0 (w, σ, -(v 0))) := by
            funext x; rw [← iteratedDeriv_succ, ← iteratedDeriv_succ]
          rw [hfun, hfun0, hfun2, hfun20]
          have h := hZc (-(v 0)) (k.1 + 2) hv0abs (by have := k.2; omega)
          refine le_trans h ?_
          nlinarith [hB3z, hδ0']
        | Z2 k =>
          simp only [KJet_Z2]
          have hfun : (fun u' : ℝ => kjet h σ (v 1) u' k.1)
              = fun u' : ℝ => iteratedDeriv k.1 (fun w : ℝ => KernelExt.Zrad h (w, σ, v 1)) u' := by
            funext u'; exact hZeq (v 1) k.1 u'
          have hfun0 : (fun u' : ℝ => kjet 0 σ (v 1) u' k.1)
              = fun u' : ℝ => iteratedDeriv k.1 (fun w : ℝ => KernelExt.Zrad 0 (w, σ, v 1)) u' := by
            funext u'; exact hZeq0 (v 1) k.1 u'
          have hfun2 : deriv (deriv (fun u' : ℝ => iteratedDeriv k.1
              (fun w : ℝ => KernelExt.Zrad h (w, σ, v 1)) u'))
              = iteratedDeriv (k.1 + 2) (fun w : ℝ => KernelExt.Zrad h (w, σ, v 1)) := by
            funext x; rw [← iteratedDeriv_succ, ← iteratedDeriv_succ]
          have hfun20 : deriv (deriv (fun u' : ℝ => iteratedDeriv k.1
              (fun w : ℝ => KernelExt.Zrad 0 (w, σ, v 1)) u'))
              = iteratedDeriv (k.1 + 2) (fun w : ℝ => KernelExt.Zrad 0 (w, σ, v 1)) := by
            funext x; rw [← iteratedDeriv_succ, ← iteratedDeriv_succ]
          rw [hfun, hfun0, hfun2, hfun20]
          have h := hZc (v 1) (k.1 + 2) hv1abs (by have := k.2; omega)
          refine le_trans h ?_
          nlinarith [hB3z, hδ0']
        | w j =>
          simp only [KJet_w]
          have h1 : deriv (fun u' : ℝ => iteratedDeriv (j.1 + 1) h u')
              = iteratedDeriv (j.1 + 2) h := by rw [← iteratedDeriv_succ]
          have h10 : deriv (fun u' : ℝ => iteratedDeriv (j.1 + 1) (0 : ℝ → ℝ) u')
              = iteratedDeriv (j.1 + 2) (0 : ℝ → ℝ) := by rw [← iteratedDeriv_succ]
          have h2 : deriv (deriv (fun u' : ℝ => iteratedDeriv (j.1 + 1) h u'))
              = iteratedDeriv (j.1 + 3) h := by rw [h1, ← iteratedDeriv_succ]
          have h20 : deriv (deriv (fun u' : ℝ => iteratedDeriv (j.1 + 1) (0 : ℝ → ℝ) u'))
              = iteratedDeriv (j.1 + 3) (0 : ℝ → ℝ) := by rw [h10, ← iteratedDeriv_succ]
          rw [h2, h20, iteratedDeriv_zero_fun, sub_zero]
          exact le_trans (hj (j.1 + 3) (by have := j.2; omega) u) (by nlinarith [hB1, hδ0'])
      rw [← dist_eq_norm, dist_pi_le_iff (by positivity : (0 : ℝ) ≤
        max (max (3 * Bz) 20) (max 1 Kk) * δ)]
      intro i
      rw [Real.dist_eq]
      have hJh : ContDiff ℝ (⊤ : ℕ∞) (fun u' : ℝ => KJet n h σ v u') := contDiff_KJet n hh σ v
      have hJ0 : ContDiff ℝ (⊤ : ℕ∞) (fun u' : ℝ => KJet n 0 σ v u') :=
        contDiff_KJet n contDiff_const σ v
      rw [deriv_deriv_pi (hJh.contDiffAt.of_le (Work.OddExistence.Manifest.AW.natCast_le_top_enat 2)),
        deriv_deriv_pi (hJ0.contDiffAt.of_le (Work.OddExistence.Manifest.AW.natCast_le_top_enat 2))]
      exact hD2 i

/-! ## The jet data: state-Lipschitz -/

/-- **State-Lipschitz of the jet curve `KJet` and of its first two `u`-derivatives.** -/
theorem KJet_lip_ext (n : ℕ) (hn : 1 ≤ n) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (g : ℝ → ℝ) (gg : ContDiff ℝ (⊤ : ℕ∞) g)
        (gj : ∀ k : ℕ, k ≤ n + 3 → ∀ s : ℝ, |iteratedDeriv k g s| ≤ 1 / 100)
        (σ : ℝ) (hσ : σ ∈ Set.Icc (1 / 4 : ℝ) 1)
        (v v' : St) (hv0 : (1 / 5 : ℝ) ≤ v 0) (hv1 : (1 / 5 : ℝ) ≤ v 1)
        (hvb : ∀ i : Fin 4, |v i| ≤ 2) (hv0' : (1 / 5 : ℝ) ≤ v' 0) (hv1' : (1 / 5 : ℝ) ≤ v' 1)
        (hvb' : ∀ i : Fin 4, |v' i| ≤ 2) (u : ℝ) (hu : u ∈ Set.Icc (3 / 16 : ℝ) 1),
        ‖KJet n g σ v u - KJet n g σ v' u‖ ≤ K * ‖v - v'‖ ∧
        ‖deriv (fun u' : ℝ => KJet n g σ v u') u -
          deriv (fun u' : ℝ => KJet n g σ v' u') u‖ ≤ K * ‖v - v'‖ ∧
        ‖deriv (deriv (fun u' : ℝ => KJet n g σ v u')) u -
          deriv (deriv (fun u' : ℝ => KJet n g σ v' u')) u‖ ≤ K * ‖v - v'‖ := by
  obtain ⟨Kz, hKz0, hKz⟩ := Zrad_jet_lipschitz_ext n
  obtain ⟨Kl, hKl0, hKl⟩ := krad_lipschitz_t
  refine ⟨max (max Kl Kz) 1, lt_of_lt_of_le (by norm_num) (le_max_right _ _), ?_⟩
  intro g gg gj σ hσ v v' hv0 hv1 hvb hv0' hv1' hvb' u hu
  have hKKl : Kl ≤ max (max Kl Kz) 1 := le_trans (le_max_left _ _) (le_max_left _ _)
  have hKKz : Kz ≤ max (max Kl Kz) 1 := le_trans (le_max_right _ _) (le_max_left _ _)
  have hK1 : (1 : ℝ) ≤ max (max Kl Kz) 1 := le_max_right _ _
  have hnn : (0 : ℝ) ≤ ‖v - v'‖ := norm_nonneg _
  have ht1 : |v 0 - v' 0| ≤ ‖v - v'‖ := by
    have h := norm_le_pi_norm (v - v') 0
    rwa [Pi.sub_apply, Real.norm_eq_abs] at h
  have ht2 : |v 1 - v' 1| ≤ ‖v - v'‖ := by
    have h := norm_le_pi_norm (v - v') 1
    rwa [Pi.sub_apply, Real.norm_eq_abs] at h
  have ht3 : |v 2 - v' 2| ≤ ‖v - v'‖ := by
    have h := norm_le_pi_norm (v - v') 2
    rwa [Pi.sub_apply, Real.norm_eq_abs] at h
  have ht4 : |v 3 - v' 3| ≤ ‖v - v'‖ := by
    have h := norm_le_pi_norm (v - v') 3
    rwa [Pi.sub_apply, Real.norm_eq_abs] at h
  have htA : |(-(v 0)) - (-(v' 0))| ≤ ‖v - v'‖ := by
    rw [show -(v 0) - -(v' 0) = -(v 0 - v' 0) by ring, abs_neg]; exact ht1
  have hv0abs : |-(v 0)| ≤ 2 := by rw [abs_neg]; exact hvb 0
  have hv0ge : (1 / 5 : ℝ) ≤ |-(v 0)| := by rw [abs_neg, abs_of_nonneg (by linarith)]; exact hv0
  have hv0abs' : |-(v' 0)| ≤ 2 := by rw [abs_neg]; exact hvb' 0
  have hv0ge' : (1 / 5 : ℝ) ≤ |-(v' 0)| := by
    rw [abs_neg, abs_of_nonneg (by linarith)]; exact hv0'
  have hv1abs : |v 1| ≤ 2 := hvb 1
  have hv1ge : (1 / 5 : ℝ) ≤ |v 1| := by rw [abs_of_nonneg (by linarith)]; exact hv1
  have hv1abs' : |v' 1| ≤ 2 := hvb' 1
  have hv1ge' : (1 / 5 : ℝ) ≤ |v' 1| := by rw [abs_of_nonneg (by linarith)]; exact hv1'
  have hkA := hKl g u σ gg (fun k hk s => gj k (by omega) s) hu hσ (-(v 0)) (-(v' 0))
    hv0ge hv0abs hv0ge' hv0abs'
  have hkB := hKl g u σ gg (fun k hk s => gj k (by omega) s) hu hσ (v 1) (v' 1)
    hv1ge hv1abs hv1ge' hv1abs'
  have hZA : ∀ (j : ℕ), j ≤ n + 3 →
      |iteratedDeriv j (fun w : ℝ => KernelExt.Zrad g (w, σ, -(v 0))) u -
       iteratedDeriv j (fun w : ℝ => KernelExt.Zrad g (w, σ, -(v' 0))) u| ≤ Kz * ‖v - v'‖ := by
    intro j hj
    have h := hKz g gg (fun k hk s => gj k (by omega) s) σ hσ u hu j hj (-(v 0))
      ⟨(abs_le.mp hv0abs).1, (abs_le.mp hv0abs).2⟩
      (-(v' 0)) ⟨(abs_le.mp hv0abs').1, (abs_le.mp hv0abs').2⟩
    exact le_trans h (mul_le_mul_of_nonneg_left htA hKz0)
  have hZB : ∀ (j : ℕ), j ≤ n + 3 →
      |iteratedDeriv j (fun w : ℝ => KernelExt.Zrad g (w, σ, v 1)) u -
       iteratedDeriv j (fun w : ℝ => KernelExt.Zrad g (w, σ, v' 1)) u| ≤ Kz * ‖v - v'‖ := by
    intro j hj
    have h := hKz g gg (fun k hk s => gj k (by omega) s) σ hσ u hu j hj (v 1)
      ⟨(abs_le.mp hv1abs).1, (abs_le.mp hv1abs).2⟩
      (v' 1) ⟨(abs_le.mp hv1abs').1, (abs_le.mp hv1abs').2⟩
    exact le_trans h (mul_le_mul_of_nonneg_left ht2 hKz0)
  have hZeqL : ∀ (t : ℝ) (k : ℕ) (u' : ℝ), kjet g σ t u' k
      = iteratedDeriv k (fun w : ℝ => KernelExt.Zrad g (w, σ, t)) u' :=
    fun t k u' => kjet_eq_Zrad (gg.of_le (by norm_num)) σ t u' k
  have hV : ∀ i : KJIx n, |KJet n g σ v u i - KJet n g σ v' u i| ≤
      max (max Kl Kz) 1 * ‖v - v'‖ := by
    intro i
    cases i with
    | aa => simp only [KJet_aa]; rw [sub_self, abs_zero]; positivity
    | sg => simp only [KJet_sg]; rw [sub_self, abs_zero]; positivity
    | t1 =>
      simp only [KJet_t1]
      exact le_trans htA (by nlinarith [hK1, hnn])
    | t2 => simp only [KJet_t2]; exact le_trans ht2 (by nlinarith [hK1, hnn])
    | kd1 =>
      simp only [KJet_kd1]
      refine le_trans (le_trans hkA.1 (mul_le_mul_of_nonneg_left htA hKl0)) ?_
      exact mul_le_mul_of_nonneg_right hKKl hnn
    | kd2 =>
      simp only [KJet_kd2]
      refine le_trans (le_trans hkB.1 (mul_le_mul_of_nonneg_left ht2 hKl0)) ?_
      exact mul_le_mul_of_nonneg_right hKKl hnn
    | c2 => simp only [KJet_c2]; exact le_trans ht3 (by nlinarith [hK1, hnn])
    | c3 => simp only [KJet_c3]; exact le_trans ht4 (by nlinarith [hK1, hnn])
    | Z1 k =>
      simp only [KJet_Z1]
      rw [hZeqL (-(v 0)) k.1 u, hZeqL (-(v' 0)) k.1 u]
      refine le_trans (hZA k.1 (by have := k.2; omega)) ?_
      exact mul_le_mul_of_nonneg_right hKKz hnn
    | Z2 k =>
      simp only [KJet_Z2]
      rw [hZeqL (v 1) k.1 u, hZeqL (v' 1) k.1 u]
      refine le_trans (hZB k.1 (by have := k.2; omega)) ?_
      exact mul_le_mul_of_nonneg_right hKKz hnn
    | w j => simp only [KJet_w]; rw [sub_self, abs_zero]; positivity
  constructor
  · exact norm_sub_le_of_component (by positivity) hV
  · constructor
    · have hD : ∀ i : KJIx n,
          |deriv (fun u' : ℝ => KJet n g σ v u' i) u -
           deriv (fun u' : ℝ => KJet n g σ v' u' i) u| ≤ max (max Kl Kz) 1 * ‖v - v'‖ := by
        intro i
        cases i with
        | aa => simp only [KJet_aa, deriv_id'']; rw [sub_self, abs_zero]; positivity
        | sg => simp only [KJet_sg, deriv_const, deriv_deriv_const_fun, sub_self, abs_zero]; positivity
        | t1 => simp only [KJet_t1, deriv_const, deriv_deriv_const_fun, sub_self, abs_zero]; positivity
        | t2 => simp only [KJet_t2, deriv_const, deriv_deriv_const_fun, sub_self, abs_zero]; positivity
        | kd1 =>
          simp only [KJet_kd1]
          refine le_trans (le_trans hkA.2.1 (mul_le_mul_of_nonneg_left htA hKl0)) ?_
          exact mul_le_mul_of_nonneg_right hKKl hnn
        | kd2 =>
          simp only [KJet_kd2]
          refine le_trans (le_trans hkB.2.1 (mul_le_mul_of_nonneg_left ht2 hKl0)) ?_
          exact mul_le_mul_of_nonneg_right hKKl hnn
        | c2 => simp only [KJet_c2, deriv_const, deriv_deriv_const_fun, sub_self, abs_zero]; positivity
        | c3 => simp only [KJet_c3, deriv_const, deriv_deriv_const_fun, sub_self, abs_zero]; positivity
        | Z1 k =>
          simp only [KJet_Z1]
          have hfun : (fun u' : ℝ => kjet g σ (-(v 0)) u' k.1)
              = fun u' : ℝ => iteratedDeriv k.1
                (fun w : ℝ => KernelExt.Zrad g (w, σ, -(v 0))) u' := by
            funext u'; exact hZeqL (-(v 0)) k.1 u'
          have hfun' : (fun u' : ℝ => kjet g σ (-(v' 0)) u' k.1)
              = fun u' : ℝ => iteratedDeriv k.1
                (fun w : ℝ => KernelExt.Zrad g (w, σ, -(v' 0))) u' := by
            funext u'; exact hZeqL (-(v' 0)) k.1 u'
          rw [hfun, hfun', ← iteratedDeriv_succ, ← iteratedDeriv_succ]
          refine le_trans (hZA (k.1 + 1) (by have := k.2; omega)) ?_
          exact mul_le_mul_of_nonneg_right hKKz hnn
        | Z2 k =>
          simp only [KJet_Z2]
          have hfun : (fun u' : ℝ => kjet g σ (v 1) u' k.1)
              = fun u' : ℝ => iteratedDeriv k.1
                (fun w : ℝ => KernelExt.Zrad g (w, σ, v 1)) u' := by
            funext u'; exact hZeqL (v 1) k.1 u'
          have hfun' : (fun u' : ℝ => kjet g σ (v' 1) u' k.1)
              = fun u' : ℝ => iteratedDeriv k.1
                (fun w : ℝ => KernelExt.Zrad g (w, σ, v' 1)) u' := by
            funext u'; exact hZeqL (v' 1) k.1 u'
          rw [hfun, hfun', ← iteratedDeriv_succ, ← iteratedDeriv_succ]
          refine le_trans (hZB (k.1 + 1) (by have := k.2; omega)) ?_
          exact mul_le_mul_of_nonneg_right hKKz hnn
        | w j => simp only [KJet_w]; rw [sub_self, abs_zero]; positivity
      rw [← dist_eq_norm, dist_pi_le_iff (by positivity : (0 : ℝ) ≤
        max (max Kl Kz) 1 * ‖v - v'‖)]
      intro i
      rw [Real.dist_eq]
      have hJh : ∀ i : KJIx n, DifferentiableAt ℝ (fun u' : ℝ => KJet n g σ v u' i) u :=
        fun i => (differentiableAt_pi.mp (((contDiff_KJet n gg σ v).differentiable (by simp))
          ).differentiableAt) i
      have hJ0 : ∀ i : KJIx n, DifferentiableAt ℝ (fun u' : ℝ => KJet n g σ v' u' i) u :=
        fun i => (differentiableAt_pi.mp (((contDiff_KJet n gg σ v').differentiable (by simp))
          ).differentiableAt) i
      rw [deriv_pi (𝕜 := ℝ) (x := u) (φ := fun u' : ℝ => KJet n g σ v u') hJh,
        deriv_pi (𝕜 := ℝ) (x := u) (φ := fun u' : ℝ => KJet n g σ v' u') hJ0]
      exact hD i
    · have hD2 : ∀ i : KJIx n,
          |deriv (deriv (fun u' : ℝ => KJet n g σ v u' i)) u -
           deriv (deriv (fun u' : ℝ => KJet n g σ v' u' i)) u| ≤
            max (max Kl Kz) 1 * ‖v - v'‖ := by
        intro i
        cases i with
        | aa => simp only [KJet_aa]; rw [sub_self, abs_zero]; positivity
        | sg => simp only [KJet_sg]; rw [sub_self, abs_zero]; positivity
        | t1 => simp only [KJet_t1, deriv_const, deriv_deriv_const_fun, sub_self, abs_zero]; positivity
        | t2 => simp only [KJet_t2, deriv_const, deriv_deriv_const_fun, sub_self, abs_zero]; positivity
        | kd1 =>
          simp only [KJet_kd1]
          refine le_trans (le_trans hkA.2.2 (mul_le_mul_of_nonneg_left htA hKl0)) ?_
          exact mul_le_mul_of_nonneg_right hKKl hnn
        | kd2 =>
          simp only [KJet_kd2]
          refine le_trans (le_trans hkB.2.2 (mul_le_mul_of_nonneg_left ht2 hKl0)) ?_
          exact mul_le_mul_of_nonneg_right hKKl hnn
        | c2 => simp only [KJet_c2, deriv_const, deriv_deriv_const_fun, sub_self, abs_zero]; positivity
        | c3 => simp only [KJet_c3, deriv_const, deriv_deriv_const_fun, sub_self, abs_zero]; positivity
        | Z1 k =>
          simp only [KJet_Z1]
          have hfun : (fun u' : ℝ => kjet g σ (-(v 0)) u' k.1)
              = fun u' : ℝ => iteratedDeriv k.1
                (fun w : ℝ => KernelExt.Zrad g (w, σ, -(v 0))) u' := by
            funext u'; exact hZeqL (-(v 0)) k.1 u'
          have hfun' : (fun u' : ℝ => kjet g σ (-(v' 0)) u' k.1)
              = fun u' : ℝ => iteratedDeriv k.1
                (fun w : ℝ => KernelExt.Zrad g (w, σ, -(v' 0))) u' := by
            funext u'; exact hZeqL (-(v' 0)) k.1 u'
          have hf2 : deriv (deriv (fun u' : ℝ => iteratedDeriv k.1
              (fun w : ℝ => KernelExt.Zrad g (w, σ, -(v 0))) u'))
              = iteratedDeriv (k.1 + 2) (fun w : ℝ => KernelExt.Zrad g (w, σ, -(v 0))) := by
            funext x; rw [← iteratedDeriv_succ, ← iteratedDeriv_succ]
          have hf2' : deriv (deriv (fun u' : ℝ => iteratedDeriv k.1
              (fun w : ℝ => KernelExt.Zrad g (w, σ, -(v' 0))) u'))
              = iteratedDeriv (k.1 + 2) (fun w : ℝ => KernelExt.Zrad g (w, σ, -(v' 0))) := by
            funext x; rw [← iteratedDeriv_succ, ← iteratedDeriv_succ]
          rw [hfun, hfun', hf2, hf2']
          refine le_trans (hZA (k.1 + 2) (by have := k.2; omega)) ?_
          exact mul_le_mul_of_nonneg_right hKKz hnn
        | Z2 k =>
          simp only [KJet_Z2]
          have hfun : (fun u' : ℝ => kjet g σ (v 1) u' k.1)
              = fun u' : ℝ => iteratedDeriv k.1
                (fun w : ℝ => KernelExt.Zrad g (w, σ, v 1)) u' := by
            funext u'; exact hZeqL (v 1) k.1 u'
          have hfun' : (fun u' : ℝ => kjet g σ (v' 1) u' k.1)
              = fun u' : ℝ => iteratedDeriv k.1
                (fun w : ℝ => KernelExt.Zrad g (w, σ, v' 1)) u' := by
            funext u'; exact hZeqL (v' 1) k.1 u'
          have hf2 : deriv (deriv (fun u' : ℝ => iteratedDeriv k.1
              (fun w : ℝ => KernelExt.Zrad g (w, σ, v 1)) u'))
              = iteratedDeriv (k.1 + 2) (fun w : ℝ => KernelExt.Zrad g (w, σ, v 1)) := by
            funext x; rw [← iteratedDeriv_succ, ← iteratedDeriv_succ]
          have hf2' : deriv (deriv (fun u' : ℝ => iteratedDeriv k.1
              (fun w : ℝ => KernelExt.Zrad g (w, σ, v' 1)) u'))
              = iteratedDeriv (k.1 + 2) (fun w : ℝ => KernelExt.Zrad g (w, σ, v' 1)) := by
            funext x; rw [← iteratedDeriv_succ, ← iteratedDeriv_succ]
          rw [hfun, hfun', hf2, hf2']
          refine le_trans (hZB (k.1 + 2) (by have := k.2; omega)) ?_
          exact mul_le_mul_of_nonneg_right hKKz hnn
        | w j => simp only [KJet_w]; rw [sub_self, abs_zero]; positivity
      rw [← dist_eq_norm, dist_pi_le_iff (by positivity : (0 : ℝ) ≤
        max (max Kl Kz) 1 * ‖v - v'‖)]
      intro i
      rw [Real.dist_eq]
      have hJh : ContDiff ℝ (⊤ : ℕ∞) (fun u' : ℝ => KJet n g σ v u') := contDiff_KJet n gg σ v
      have hJ0 : ContDiff ℝ (⊤ : ℕ∞) (fun u' : ℝ => KJet n g σ v' u') := contDiff_KJet n gg σ v'
      rw [deriv_deriv_pi (hJh.contDiffAt.of_le (Work.OddExistence.Manifest.AW.natCast_le_top_enat 2)),
        deriv_deriv_pi (hJ0.contDiffAt.of_le (Work.OddExistence.Manifest.AW.natCast_le_top_enat 2))]
      exact hD2 i

end

end Work.OddVolterra.WinData