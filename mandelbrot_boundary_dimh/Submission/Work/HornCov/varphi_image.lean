import Mathlib
import Submission.Work.Interfaces.HornParts
import Submission.Work.Horn.basic
import Submission.Work.HornCov.critOrbit_injective
import Submission.Work.HornCov.isPreconnected_diff_critOrbit

/-!
# `Work.HornCov.varphi_image`

Claim B (`HornVarphiStatement`) plus the topology of the two components `BuOf`, `BlOf` of
`φ⁻¹(B)` imply that each of them maps **onto** the immediate basin minus the forward critical
orbit:

`B \ critOrbit f₀ c ⊆ φ '' BuOf d B`  and  `B \ critOrbit f₀ c ⊆ φ '' BlOf d B`.

Three ingredients:

* `hVarphi` produces, around every `y ∈ B \ critOrbit`, holomorphic local sections of `φ` over a
  ball `ball y r`, *through any prescribed preimage* `w ∈ BuOf ∪ BlOf` of a point of that ball.
  The image of such a section is a connected subset of the disjoint union `BuOf ∪ BlOf` containing
  the prescribed point, hence it lies in the component of that point
  (`image_ball_of_section`); so the whole ball is contained in `φ '' Dc`.
* Therefore `A := (B \ critOrbit) ∩ φ '' BuOf` is both open and closed in `B \ critOrbit`
  (`hopen`/`hclosed` inside `subset_image_of_component`).
* `B \ critOrbit` is preconnected (`Work.HornCov.isPreconnected_diff_critOrbit`), so `A` is all
  of it as soon as `A ≠ ∅`.  Nonemptiness is elementary (`exists_mem_image_of_component`): for a
  `T`-invariant `Dc ⊆ φ⁻¹(B)` and `w₀ ∈ Dc`, the chain `n ↦ φ (w₀ - n)` is a backward orbit in
  `B`; if all of its points were on the critical orbit, injectivity of the critical orbit
  (`Work.HornCov.critOrbit_injective`) would force the exponents to drop by one at each step,
  which is impossible after `k 0` steps.

The set-up is Shishikura, *The Hausdorff dimension of the boundary of the Mandelbrot set and Julia
sets*, Prop. 5.3 (the maps `φ₀ : B̃^{u}, B̃^{l} → 𝓑 \ P⁺` are surjective).
-/

namespace Work.HornCov

open MandelDim Filter Topology Metric Set
open scoped Topology

noncomputable section

variable {f₀ : ℂ → ℂ} {D₀ B : Set ℂ} {c : ℂ}

/-- If `φ` has local sections over a ball through every point of `Bu ∪ Bl`, then a point `w` of
`Bu` over the ball extends to a section whose image is a connected subset of `Bu ∪ Bl` containing
`w`; by disjointness the image lies in `Bu`, and the whole ball is in `φ '' Bu`. -/
private theorem image_ball_of_section {Bu Bl : Set ℂ} (hBu : IsOpen Bu) (hBl : IsOpen Bl)
    (hdisj : Disjoint Bu Bl) {φ : ℂ → ℂ} {y : ℂ} {r : ℝ}
    (hsec : ∀ w ∈ Bu ∪ Bl, φ w ∈ Metric.ball y r →
      ∃ σ : ℂ → ℂ, DifferentiableOn ℂ σ (Metric.ball y r) ∧
        MapsTo σ (Metric.ball y r) (Bu ∪ Bl) ∧
        (∀ u ∈ Metric.ball y r, φ (σ u) = u) ∧ σ (φ w) = w)
    {w : ℂ} (hw : w ∈ Bu) (hwφ : φ w ∈ Metric.ball y r) :
    Metric.ball y r ⊆ φ '' Bu := by
  obtain ⟨σ, hσd, hσm, hσφ, hσw⟩ := hsec w (Or.inl hw) hwφ
  have hpre : IsPreconnected (σ '' Metric.ball y r) :=
    (convex_ball y r).isPreconnected.image σ hσd.continuousOn
  have hsub : σ '' Metric.ball y r ⊆ Bu :=
    hpre.subset_left_of_subset_union hBu hBl hdisj
      (fun z hz => by obtain ⟨u, hu, rfl⟩ := hz; exact hσm hu)
      ⟨w, ⟨φ w, hwφ, hσw⟩, hw⟩
  intro u hu
  exact ⟨σ u, hsub ⟨u, hu, rfl⟩, hσφ u hu⟩

/-- **Clopen argument.** -/
private theorem subset_of_clopen_in_preconnected {α : Type*} [PseudoMetricSpace α]
    {s A : Set α} (hAs : A ⊆ s) (hpre : IsPreconnected s) (hAne : A.Nonempty)
    (hopen : ∀ y : A, ∃ r : ℝ, 0 < r ∧ Metric.ball (y : α) r ∩ s ⊆ A)
    (hclosed : ∀ y : (s \ A : Set α), ∃ r : ℝ, 0 < r ∧ Metric.ball (y : α) r ∩ A = ∅) :
    s ⊆ A := by
  classical
  let r₁ : A → ℝ := fun y => Classical.choose (hopen y)
  have hr₁ : ∀ y : A, 0 < r₁ y ∧ Metric.ball (y : α) (r₁ y) ∩ s ⊆ A :=
    fun y => Classical.choose_spec (hopen y)
  set U : Set α := ⋃ y : A, Metric.ball (y : α) (r₁ y) with hUdef
  have hUo : IsOpen U := isOpen_iUnion fun y => isOpen_ball
  have hUs : s ∩ U = A := by
    ext z
    constructor
    · rintro ⟨hzs, hzU⟩
      simp only [hUdef, Set.mem_iUnion, Metric.mem_ball] at hzU
      obtain ⟨y, hzy⟩ := hzU
      exact (hr₁ y).2 ⟨hzy, hzs⟩
    · intro hzA
      exact ⟨hAs hzA, by
        simp only [hUdef, Set.mem_iUnion, Metric.mem_ball]
        exact ⟨⟨z, hzA⟩, Metric.mem_ball_self (hr₁ ⟨z, hzA⟩).1⟩⟩
  let r₂ : (s \ A : Set α) → ℝ := fun y => Classical.choose (hclosed y)
  have hr₂ : ∀ y : (s \ A : Set α), 0 < r₂ y ∧ Metric.ball (y : α) (r₂ y) ∩ A = ∅ :=
    fun y => Classical.choose_spec (hclosed y)
  set V : Set α := ⋃ y : (s \ A : Set α), Metric.ball (y : α) (r₂ y) with hVdef
  have hVo : IsOpen V := isOpen_iUnion fun y => isOpen_ball
  have hVs : s ∩ V = s \ A := by
    ext z
    constructor
    · rintro ⟨hzs, hzV⟩
      simp only [hVdef, Set.mem_iUnion, Metric.mem_ball] at hzV
      obtain ⟨y, hzy⟩ := hzV
      refine ⟨hzs, fun hzA => ?_⟩
      have hmem : z ∈ Metric.ball (y : α) (r₂ y) ∩ A := ⟨hzy, hzA⟩
      rw [(hr₂ y).2] at hmem
      exact hmem
    · rintro ⟨hzs, hzA⟩
      exact ⟨hzs, by
        simp only [hVdef, Set.mem_iUnion, Metric.mem_ball]
        exact ⟨⟨z, hzs, hzA⟩, Metric.mem_ball_self (hr₂ ⟨z, hzs, hzA⟩).1⟩⟩
  have hsUV : s ⊆ U ∪ V := by
    intro z hz
    by_cases hzA : z ∈ A
    · left
      have : z ∈ s ∩ U := by rw [hUs]; exact hzA
      exact this.2
    · right
      have : z ∈ s ∩ V := by rw [hVs]; exact ⟨hz, hzA⟩
      exact this.2
  rcases Set.eq_empty_or_nonempty (s ∩ V) with hemp | hne
  · intro z hz
    by_contra hzA
    have : z ∈ s ∩ V := by rw [hVs]; exact ⟨hz, hzA⟩
    rw [hemp] at this
    exact this
  · obtain ⟨z, hzs, hzU, hzV⟩ := hpre U V hUo hVo hsUV
      (by obtain ⟨y, hy⟩ := hAne
          exact ⟨y, by rw [hUs]; exact hy⟩) hne
    have hzA : z ∈ A := by
      have : z ∈ s ∩ U := ⟨hzs, hzU⟩
      rwa [hUs] at this
    have hznotA : z ∉ A := by
      have : z ∈ s ∩ V := ⟨hzs, hzV⟩
      rw [hVs] at this
      exact this.2
    exact absurd hzA hznotA

/-- **Nonemptiness.** -/
private theorem exists_mem_image_of_component (d : MandelDim.ParabData f₀ D₀)
    (hinj : ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → f₀^[a] c = f₀^[b] c → a = b)
    {Dc : Set ℂ} (hDcT : MandelDim.IsTInvariant Dc) (hDcsub : Dc ⊆ MandelDim.Btil d B)
    {w₀ : ℂ} (hw₀ : w₀ ∈ Dc) :
    ∃ y ∈ B \ MandelDim.critOrbit f₀ c, y ∈ d.φ '' Dc := by
  have hmem : ∀ n : ℕ, w₀ - (n : ℂ) ∈ Dc := by
    intro n
    have h := Work.Horn.MandelDim.IsTInvariant.add_int hDcT hw₀ (-(n : ℤ))
    rwa [show w₀ + (((-(n : ℤ)) : ℤ) : ℂ) = w₀ - (n : ℂ) by push_cast; ring] at h
  have hmemBtil : ∀ n : ℕ, w₀ - (n : ℂ) ∈ MandelDim.Btil d B := fun n => hDcsub (hmem n)
  have hφB : ∀ n : ℕ, d.φ (w₀ - (n : ℂ)) ∈ B := fun n => (hmemBtil n).2
  have habel : ∀ n : ℕ, f₀ (d.φ (w₀ - ((n + 1 : ℕ) : ℂ))) = d.φ (w₀ - (n : ℂ)) := by
    intro n
    have h1 : w₀ - ((n + 1 : ℕ) : ℂ) ∈ d.Dφ := (hmemBtil (n + 1)).1
    have h2 : w₀ - ((n + 1 : ℕ) : ℂ) + 1 ∈ d.Dφ := by
      have he : w₀ - ((n + 1 : ℕ) : ℂ) + 1 = w₀ - (n : ℂ) := by push_cast; ring
      rw [he]; exact (hmemBtil n).1
    have h := d.φ_abel (w₀ - ((n + 1 : ℕ) : ℂ)) h1 h2
    rw [show w₀ - ((n + 1 : ℕ) : ℂ) + 1 = w₀ - (n : ℂ) by push_cast; ring] at h
    exact h.symm
  by_contra hcon
  have hall : ∀ n : ℕ, d.φ (w₀ - (n : ℂ)) ∈ MandelDim.critOrbit f₀ c := by
    intro n
    by_contra hn
    exact hcon ⟨d.φ (w₀ - (n : ℂ)), ⟨hφB n, hn⟩, ⟨w₀ - (n : ℂ), hmem n, rfl⟩⟩
  choose k hk1 hk using hall
  have hstep : ∀ n : ℕ, k n = k (n + 1) + 1 := by
    intro n
    have h : f₀^[k n] c = f₀^[k (n + 1) + 1] c := by
      rw [← hk n, ← habel n, Function.iterate_succ_apply', ← hk (n + 1)]
    exact hinj (k n) (k (n + 1) + 1) (hk1 n) (by omega) h
  have hk0 : ∀ n : ℕ, n ≤ k 0 → k n = k 0 - n := by
    intro n
    induction n with
    | zero => intro _; simp
    | succ m ih =>
        intro hm
        have hm' : m ≤ k 0 := by omega
        have hs := hstep m
        have hi := ih hm'
        omega
  have hone : 1 ≤ k (k 0) := hk1 (k 0)
  have hzero : k (k 0) = 0 := by
    have h := hk0 (k 0) le_rfl
    omega
  omega

/-- **Main step for one component.** -/
private theorem subset_image_of_component (hsetup : MandelDim.IsF0Setup f₀ D₀ B c)
    (d : MandelDim.ParabData f₀ D₀)
    {Dc Oc : Set ℂ} (hDcopen : IsOpen Dc) (hOcopen : IsOpen Oc) (hdisj : Disjoint Dc Oc)
    (hDcT : MandelDim.IsTInvariant Dc) (hDcsub : Dc ⊆ MandelDim.Btil d B)
    (hsec : ∀ y ∈ B, y ∉ MandelDim.critOrbit f₀ c → ∃ r : ℝ, 0 < r ∧ Metric.ball y r ⊆ B ∧
      ∀ w ∈ Dc ∪ Oc, d.φ w ∈ Metric.ball y r →
        ∃ σ : ℂ → ℂ, DifferentiableOn ℂ σ (Metric.ball y r) ∧
          MapsTo σ (Metric.ball y r) (Dc ∪ Oc) ∧
          (∀ u ∈ Metric.ball y r, d.φ (σ u) = u) ∧ σ (d.φ w) = w)
    {w₀ : ℂ} (hw₀ : w₀ ∈ Dc) :
    B \ MandelDim.critOrbit f₀ c ⊆ d.φ '' Dc := by
  set s : Set ℂ := B \ MandelDim.critOrbit f₀ c with hsdef
  set A : Set ℂ := s ∩ d.φ '' Dc with hAdef
  obtain ⟨y₀, hy₀s, hy₀im⟩ := exists_mem_image_of_component d
    (critOrbit_injective f₀ D₀ B c hsetup) hDcT hDcsub hw₀
  have hopen : ∀ y : A, ∃ r : ℝ, 0 < r ∧ Metric.ball (y : ℂ) r ∩ s ⊆ A := by
    intro y
    have hys : (y : ℂ) ∈ s := y.2.1
    have hyim : (y : ℂ) ∈ d.φ '' Dc := y.2.2
    rw [Set.mem_image] at hyim
    obtain ⟨w, hwDc, hwφ⟩ := hyim
    obtain ⟨r, hr, -, hsecr⟩ := hsec (y : ℂ) hys.1 hys.2
    refine ⟨r, hr, ?_⟩
    rintro z ⟨hzr, hzs⟩
    exact ⟨hzs, image_ball_of_section hDcopen hOcopen hdisj hsecr hwDc
      (by rw [hwφ]; exact Metric.mem_ball_self hr) hzr⟩
  have hclosed : ∀ y : (s \ A : Set ℂ), ∃ r : ℝ, 0 < r ∧ Metric.ball (y : ℂ) r ∩ A = ∅ := by
    intro y
    have hys : (y : ℂ) ∈ s := y.2.1
    have hyA : (y : ℂ) ∉ A := y.2.2
    obtain ⟨r, hr, -, hsecr⟩ := hsec (y : ℂ) hys.1 hys.2
    refine ⟨r, hr, ?_⟩
    rw [Set.eq_empty_iff_forall_notMem]
    rintro z ⟨hzr, hzs, hzim⟩
    rw [Set.mem_image] at hzim
    obtain ⟨w, hwDc, hwφ⟩ := hzim
    exact hyA ⟨hys, image_ball_of_section hDcopen hOcopen hdisj hsecr hwDc
      (by rw [hwφ]; exact hzr) (Metric.mem_ball_self hr)⟩
  have hmain := subset_of_clopen_in_preconnected (s := s) (A := A) Set.inter_subset_left
    (show IsPreconnected s from isPreconnected_diff_critOrbit f₀ D₀ B c hsetup)
    ⟨y₀, hy₀s, hy₀im⟩ hopen hclosed
  intro z hz
  exact (hmain hz).2

/-- **Claim B, image part.**  Each of the two components of `φ₀⁻¹(B)` maps onto the immediate
basin minus the forward critical orbit. -/
theorem varphi_image (hVarphi : MandelDim.HornVarphiStatement) (hTopo : MandelDim.HornTopoStatement)
    (hSC : MandelDim.HornSCStatement) (f₀ : ℂ → ℂ) (D₀ B : Set ℂ) (c : ℂ)
    (d : MandelDim.ParabData f₀ D₀) (hsetup : MandelDim.IsF0Setup f₀ D₀ B c) :
    B \ MandelDim.critOrbit f₀ c ⊆ d.φ '' (MandelDim.BuOf d B) ∧
      B \ MandelDim.critOrbit f₀ c ⊆ d.φ '' (MandelDim.BlOf d B) := by
  obtain ⟨hBuopen, hBlopen, hBuT, hBlT, hHup, hHlow, -⟩ := hTopo f₀ D₀ B c d hsetup
  obtain ⟨-, -, hdisj⟩ := hSC f₀ D₀ B c d hsetup
  have hw₀u : Complex.I * ((d.η₀ + 1 : ℝ) : ℂ) ∈ MandelDim.BuOf d B := by
    apply hHup; simp
  have hw₀l : -(Complex.I * ((d.η₀ + 1 : ℝ) : ℂ)) ∈ MandelDim.BlOf d B := by
    apply hHlow; simp
  have hsub_u : MandelDim.BuOf d B ⊆ MandelDim.Btil d B := connectedComponentIn_subset _ _
  have hsub_l : MandelDim.BlOf d B ⊆ MandelDim.Btil d B := connectedComponentIn_subset _ _
  refine ⟨subset_image_of_component hsetup d hBuopen hBlopen hdisj hBuT hsub_u ?_ hw₀u,
    subset_image_of_component hsetup d hBlopen hBuopen hdisj.symm hBlT hsub_l ?_ hw₀l⟩
  · intro y hyB hyP
    exact hVarphi f₀ D₀ B c d hsetup y hyB hyP
  · intro y hyB hyP
    obtain ⟨r, hr, hrB, hsec⟩ := hVarphi f₀ D₀ B c d hsetup y hyB hyP
    refine ⟨r, hr, hrB, fun w hw hwφ => ?_⟩
    rw [Set.union_comm] at hw
    obtain ⟨σ, h1, h2, h3, h4⟩ := hsec w hw hwφ
    refine ⟨σ, h1, ?_, h3, h4⟩
    rwa [Set.union_comm]

end

end Work.HornCov
