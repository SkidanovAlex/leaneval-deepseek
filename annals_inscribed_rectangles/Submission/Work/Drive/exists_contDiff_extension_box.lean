import Mathlib
import Submission.Work.Drive.seeleyDescent_ext
import Submission.Work.Drive.exists_contDiff_flattening
import Submission.Work.Drive.exists_contDiff_of_isCompact_local

namespace Work.Drive

open scoped ContDiff Topology
open Set Filter

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ### The box -/

/-- The closed box `[a,b] × [c,d]` in `ℝ × ℝ`. -/
def box (a b c d : ℝ) : Set (ℝ × ℝ) := {q | q.1 ∈ Set.Icc a b ∧ q.2 ∈ Set.Icc c d}

@[simp] lemma mem_box {a b c d : ℝ} {q : ℝ × ℝ} :
    q ∈ box a b c d ↔ q.1 ∈ Set.Icc a b ∧ q.2 ∈ Set.Icc c d := Iff.rfl

lemma box_subset {a b c d a' b' c' d' : ℝ} (ha : a ≤ a') (hb : b' ≤ b) (hc : c ≤ c')
    (hd : d' ≤ d) : box a' b' c' d' ⊆ box a b c d := by
  intro q hq
  exact ⟨⟨le_trans ha hq.1.1, le_trans hq.1.2 hb⟩, ⟨le_trans hc hq.2.1, le_trans hq.2.2 hd⟩⟩

/-! ### Auxiliary lemmas -/

/-- The `√`-descent of a `C^∞` even function, *preserving* evenness in the first variable. -/
theorem seeleyDescentExt_even {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {F : X × ℝ → E}
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F)
    (heven : ∀ (x : X) (t : ℝ), F (x, -t) = F (x, t))
    (heven' : ∀ (x : X) (t : ℝ), F (-x, t) = F (x, t)) :
    ∃ G : X × ℝ → E, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G ∧
      (∀ (x : X) (s : ℝ), 0 ≤ s → G (x, s) = F (x, Real.sqrt s)) ∧
      (∀ (x : X) (s : ℝ), G (-x, s) = G (x, s)) := by
  obtain ⟨G, hG, hGval⟩ := seeleyDescent_ext hF heven
  refine ⟨fun p => (2 : ℝ)⁻¹ • (G p + G (-p.1, p.2)), ?_, ?_, ?_⟩
  · refine ContDiff.const_smul (2 : ℝ)⁻¹ ?_
    refine hG.add ?_
    have hflip : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : X × ℝ => (-p.1, p.2)) :=
      (contDiff_fst.neg).prodMk contDiff_snd
    exact hG.comp hflip
  · intro x s hs
    have h1 : G (x, s) = F (x, Real.sqrt s) := hGval x s hs
    have h2 : G (-x, s) = F (-x, Real.sqrt s) := hGval (-x) s hs
    change (2 : ℝ)⁻¹ • (G (x, s) + G (-x, s)) = F (x, Real.sqrt s)
    rw [h1, h2, heven' x (Real.sqrt s),
      show F (x, Real.sqrt s) + F (x, Real.sqrt s) = (2 : ℝ) • F (x, Real.sqrt s) from by
        rw [two_smul],
      smul_smul, inv_mul_cancel₀ (by norm_num : (2 : ℝ) ≠ 0), one_smul]
  · intro x s
    change (2 : ℝ)⁻¹ • (G (-x, s) + G (-(-x), s))
      = (2 : ℝ)⁻¹ • (G (x, s) + G (-x, s))
    rw [neg_neg, add_comm]

/-- **Smoothness of a cut-off times a composed function.**  If `h` is smooth, `Φ` is smooth and
`S` is a closed set containing the support of `h` whose points all have a neighbourhood mapped
by `Φ` into `K`, then `q ↦ h q • u (Φ q)` is globally `C^∞` (for `u` `C^∞` on `K`). -/
theorem contDiff_smul_comp_of_support_subset {u : ℝ × ℝ → E} {K : Set (ℝ × ℝ)}
    (hu : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u K)
    {h : ℝ × ℝ → ℝ} (hh : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h)
    {Φ : ℝ × ℝ → ℝ × ℝ} (hΦ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    {S : Set (ℝ × ℝ)} (hS : IsClosed S) (hSh : Function.support h ⊆ S)
    (hgood : ∀ q ∈ S, ∃ U ∈ 𝓝 q, MapsTo Φ U K) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun q : ℝ × ℝ => h q • u (Φ q)) := by
  rw [contDiff_iff_contDiffAt]
  intro q
  by_cases hq : q ∈ S
  · obtain ⟨U, hU, hUK⟩ := hgood q hq
    obtain ⟨V, hVU, hVo, hqV⟩ := mem_nhds_iff.mp hU
    have hVK : MapsTo Φ V K := fun y hy => hUK (hVU hy)
    have hcomp : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun q : ℝ × ℝ => u (Φ q)) V :=
      hu.comp hΦ.contDiffOn hVK
    have hat : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun q : ℝ × ℝ => u (Φ q)) q :=
      hcomp.contDiffAt (hVo.mem_nhds hqV)
    exact (hh.contDiffAt).smul hat
  · have hopen : Sᶜ ∈ 𝓝 q := hS.isOpen_compl.mem_nhds hq
    have hev : (fun q : ℝ × ℝ => h q • u (Φ q)) =ᶠ[𝓝 q] (fun _ => (0 : E)) := by
      filter_upwards [hopen] with y hy
      have hy' : h y = 0 := by
        by_contra hc
        exact hy (hSh hc)
      rw [hy', zero_smul]
    exact (contDiffAt_const (c := (0 : E))).congr_of_eventuallyEq hev

/-- Pairing of two one-variable smooth maps into `ℝ × ℝ`. -/
lemma contDiff_pair {φ ψ : ℝ → ℝ} (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ)
    (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun q : ℝ × ℝ => (φ q.1, ψ q.2)) :=
  (hφ.comp contDiff_fst).prodMk (hψ.comp contDiff_snd)

/-! ### The local pieces -/

/-- **Interior piece.**  If `p` lies in the interior of the box, a bump-type piece built from
flat maps of `ℝ` agrees with `u` on a neighbourhood of `p`. -/
theorem piece_middle {a b c d : ℝ} {u : ℝ × ℝ → E}
    (hu : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u (box a b c d)) {p : ℝ × ℝ}
    (h₁ : a < p.1) (h₂ : p.1 < b) (h₃ : c < p.2) (h₄ : p.2 < d) :
    ∃ r : ℝ, 0 < r ∧ ∃ g : ℝ × ℝ → E, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g ∧
      ∀ x ∈ box a b c d, dist x p < r → g x = u x := by
  set η : ℝ := min (p.1 - a) (b - p.1) with hηdef
  have hηpos : 0 < η := lt_min (sub_pos.mpr h₁) (sub_pos.mpr h₂)
  set η' : ℝ := min (p.2 - c) (d - p.2) with hη'def
  have hη'pos : 0 < η' := lt_min (sub_pos.mpr h₃) (sub_pos.mpr h₄)
  obtain ⟨φ₀, hφ₀sm, hφ₀id, hφ₀im⟩ :=
    exists_contDiff_flattening (p.1 - η / 2) (p.1 + η / 2) (by linarith) (η / 2) (by linarith)
  obtain ⟨φ₁, hφ₁sm, hφ₁id, hφ₁im⟩ :=
    exists_contDiff_flattening (p.2 - η' / 2) (p.2 + η' / 2) (by linarith) (η' / 2) (by linarith)
  have hφ₀mem : ∀ t : ℝ, φ₀ t ∈ Set.Icc a b := by
    intro t
    have h := hφ₀im t
    simp only [Set.mem_Ioo] at h
    have h1 : η ≤ p.1 - a := min_le_left _ _
    have h2 : η ≤ b - p.1 := min_le_right _ _
    exact ⟨by linarith, by linarith⟩
  have hφ₁mem : ∀ t : ℝ, φ₁ t ∈ Set.Icc c d := by
    intro t
    have h := hφ₁im t
    simp only [Set.mem_Ioo] at h
    have h1 : η' ≤ p.2 - c := min_le_left _ _
    have h2 : η' ≤ d - p.2 := min_le_right _ _
    exact ⟨by linarith, by linarith⟩
  refine ⟨min (η / 2) (η' / 2), lt_min (by linarith) (by linarith),
    fun x => u (φ₀ x.1, φ₁ x.2), ?_, ?_⟩
  · refine hu.comp_contDiff (contDiff_pair hφ₀sm hφ₁sm) (fun q => ⟨hφ₀mem q.1, hφ₁mem q.2⟩)
  · intro x hx hd
    have h := hd
    rw [Prod.dist_eq] at h
    have h1 : dist x.1 p.1 < η / 2 :=
      lt_of_le_of_lt (le_max_left _ _) (lt_of_lt_of_le h (min_le_left _ _))
    have h2 : dist x.2 p.2 < η' / 2 :=
      lt_of_le_of_lt (le_max_right _ _) (lt_of_lt_of_le h (min_le_right _ _))
    rw [Real.dist_eq] at h1 h2
    have hx0 : x.1 ∈ Set.Icc (p.1 - η / 2) (p.1 + η / 2) := by
      rw [abs_lt] at h1
      exact ⟨by linarith [h1.1], by linarith [h1.2]⟩
    have hx1 : x.2 ∈ Set.Icc (p.2 - η' / 2) (p.2 + η' / 2) := by
      rw [abs_lt] at h2
      exact ⟨by linarith [h2.1], by linarith [h2.2]⟩
    simp only [hφ₀id x.1 hx0, hφ₁id x.2 hx1]


/-- **Left-edge piece.**  Near a point `(a, y₀)` of the left edge of the box (with `y₀` in the
open interval `(c,d)`) there is a global `C^∞` function agreeing with `u` on the box. -/
theorem piece_left {a b c d : ℝ} (hab : a < b) {u : ℝ × ℝ → E}
    (hu : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u (box a b c d)) {y₀ : ℝ}
    (hy₁ : c < y₀) (hy₂ : y₀ < d) :
    ∃ r : ℝ, 0 < r ∧ ∃ g : ℝ × ℝ → E, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g ∧
      ∀ x ∈ box a b c d, dist x (a, y₀) < r → g x = u x := by
  -- tangential flattening
  set η : ℝ := min (y₀ - c) (d - y₀) with hηdef
  have hηpos : 0 < η := lt_min (sub_pos.mpr hy₁) (sub_pos.mpr hy₂)
  obtain ⟨ψ, hψsm, hψid, hψim⟩ :=
    exists_contDiff_flattening (y₀ - η / 2) (y₀ + η / 2) (by linarith) (η / 2) (by linarith)
  have hψmem : ∀ t : ℝ, ψ t ∈ Set.Icc c d := by
    intro t
    have h := hψim t
    simp only [Set.mem_Ioo] at h
    have h1 : η ≤ y₀ - c := min_le_left _ _
    have h2 : η ≤ d - y₀ := min_le_right _ _
    exact ⟨by linarith, by linarith⟩
  -- normal cut-off
  set R : ℝ := Real.sqrt (b - a) / 2 with hRdef
  have hbapos : 0 < b - a := sub_pos.mpr hab
  have hRpos : 0 < R := by rw [hRdef]; positivity
  have hRsq4 : R ^ 2 ≤ (b - a) / 4 := by
    rw [hRdef, div_pow, show (2 : ℝ) ^ 2 = 4 by norm_num, div_le_iff₀ (by norm_num : (0 : ℝ) < 4)]
    linarith [Real.sq_sqrt hbapos.le]
  -- the bump
  set f : ContDiffBump (0 : ℝ) := ⟨R / 2, R, by linarith, by linarith⟩ with hfdef
  have hf1 : ∀ t : ℝ, |t| ≤ R / 2 → f t = 1 := by
    intro t ht
    refine f.one_of_mem_closedBall ?_
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero]
    exact ht
  -- the function whose descent gives the piece
  set F : ℝ × ℝ → E := fun q => f q.2 • u (a + q.2 ^ 2, ψ q.1) with hFdef
  have hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F := by
    have hh : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun q : ℝ × ℝ => f q.2) :=
      (f.contDiff (n := ⊤)).comp contDiff_snd
    have hΦ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun q : ℝ × ℝ => (a + q.2 ^ 2, ψ q.1)) :=
      (contDiff_const.add (contDiff_snd.pow 2)).prodMk (hψsm.comp contDiff_fst)
    have hS : IsClosed (Set.univ ×ˢ Metric.closedBall (0 : ℝ) R) :=
      (isClosed_univ : IsClosed (Set.univ : Set ℝ)).prod Metric.isClosed_closedBall
    have hSh : Function.support (fun q : ℝ × ℝ => f q.2)
        ⊆ Set.univ ×ˢ Metric.closedBall (0 : ℝ) R := by
      intro q hq
      refine ⟨trivial, ?_⟩
      rw [← f.tsupport_eq]
      exact subset_closure hq
    have hgood : ∀ q ∈ Set.univ ×ˢ Metric.closedBall (0 : ℝ) R,
        ∃ U ∈ 𝓝 q, MapsTo (fun q : ℝ × ℝ => (a + q.2 ^ 2, ψ q.1)) U (box a b c d) := by
      intro q hq
      have hq2 : |q.2| ≤ R := by
        have h := hq.2
        rwa [Metric.mem_closedBall, Real.dist_eq, sub_zero] at h
      refine ⟨Metric.ball q (R / 4), Metric.ball_mem_nhds _ (by linarith), fun q' hq' => ?_⟩
      have hdq : dist q' q < R / 4 := Metric.mem_ball.mp hq'
      have h2 : |q'.2 - q.2| ≤ dist q' q := by
        rw [Prod.dist_eq]
        calc |q'.2 - q.2| = dist q'.2 q.2 := by rw [Real.dist_eq]
          _ ≤ max (dist q'.1 q.1) (dist q'.2 q.2) := le_max_right _ _
      have h3 : |q'.2| ≤ 5 * R / 4 := by
        have h := abs_sub_abs_le_abs_sub q'.2 q.2
        linarith [h2, hdq, hq2, h]
      have h4 : q'.2 ^ 2 ≤ b - a := by
        have h5 : q'.2 ^ 2 ≤ (5 * R / 4) ^ 2 := by
          refine (sq_le_sq).mpr ?_
          rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 5 * R / 4)]
          exact h3
        nlinarith [h5, hRsq4, hbapos]
      exact ⟨⟨by linarith [sq_nonneg q'.2], by linarith [h4]⟩, hψmem q'.1⟩
    exact contDiff_smul_comp_of_support_subset hu hh hΦ hS hSh hgood
  obtain ⟨D, hD, hDval⟩ := seeleyDescent_ext hF (fun τ σ => by
    rw [hFdef]
    simp only [f.neg, neg_sq])
  refine ⟨min (η / 2) ((R / 4) ^ 2), lt_min (by linarith) (by positivity),
    fun x => D (x.2, x.1 - a), ?_, ?_⟩
  · have hmap : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun x : ℝ × ℝ => (x.2, x.1 - a)) :=
      contDiff_snd.prodMk (contDiff_fst.sub contDiff_const)
    exact hD.comp hmap
  · intro x hx hd
    show D (x.2, x.1 - a) = u x
    have hxa : a ≤ x.1 := hx.1.1
    have h := hd
    rw [Prod.dist_eq] at h
    have h1 : dist x.1 a < (R / 4) ^ 2 :=
      lt_of_le_of_lt (le_max_left _ _) (lt_of_lt_of_le h (min_le_right _ _))
    have h2 : dist x.2 y₀ < η / 2 :=
      lt_of_le_of_lt (le_max_right _ _) (lt_of_lt_of_le h (min_le_left _ _))
    rw [Real.dist_eq] at h1 h2
    have h3 : x.1 - a ≤ (R / 4) ^ 2 := by
      rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ x.1 - a)] at h1
      exact le_of_lt h1
    have h4 : 0 ≤ x.1 - a := by linarith
    have h5 : x.2 ∈ Set.Icc (y₀ - η / 2) (y₀ + η / 2) := by
      rw [abs_lt] at h2
      exact ⟨by linarith [h2.1], by linarith [h2.2]⟩
    have hDv : D (x.2, x.1 - a) = F (x.2, Real.sqrt (x.1 - a)) := hDval x.2 (x.1 - a) h4
    have hFv : F (x.2, Real.sqrt (x.1 - a))
        = f (Real.sqrt (x.1 - a)) • u (a + (Real.sqrt (x.1 - a)) ^ 2, ψ x.2) := rfl
    rw [hDv, hFv, Real.sq_sqrt h4]
    have h7 : Real.sqrt (x.1 - a) ≤ R / 2 := by
      have h8 : Real.sqrt (x.1 - a) ^ 2 ≤ (R / 2) ^ 2 := by
        rw [Real.sq_sqrt h4]
        nlinarith [h3, hRpos]
      nlinarith [h8, Real.sqrt_nonneg (x.1 - a), hRpos]
    rw [hf1 _ (by rw [abs_of_nonneg (Real.sqrt_nonneg _)]; exact h7), one_smul, hψid x.2 h5]
    congr 1
    exact Prod.ext (by ring) rfl


/-- **Corner piece (lower-left).**  Near the corner `(a,c)` of the box there is a global
`C^∞` function agreeing with `u` on the box. -/
theorem piece_corner {a b c d : ℝ} (hab : a < b) (hcd : c < d) {u : ℝ × ℝ → E}
    (hu : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u (box a b c d)) :
    ∃ r : ℝ, 0 < r ∧ ∃ g : ℝ × ℝ → E, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g ∧
      ∀ x ∈ box a b c d, dist x (a, c) < r → g x = u x := by
  set m : ℝ := min (b - a) (d - c) with hmdef
  have hmpos : 0 < m := lt_min (sub_pos.mpr hab) (sub_pos.mpr hcd)
  set R : ℝ := Real.sqrt m / 2 with hRdef
  have hRpos : 0 < R := by rw [hRdef]; positivity
  have hRsq : R ^ 2 ≤ m / 4 := by
    rw [hRdef, div_pow, show (2 : ℝ) ^ 2 = 4 by norm_num, div_le_iff₀ (by norm_num : (0 : ℝ) < 4)]
    linarith [Real.sq_sqrt hmpos.le]
  have hRm : R ^ 2 ≤ m := le_trans hRsq (by linarith [hmpos])
  have hmba : m ≤ b - a := min_le_left _ _
  have hmdc : m ≤ d - c := min_le_right _ _
  set f : ContDiffBump (0 : ℝ) := ⟨R / 2, R, by linarith, by linarith⟩ with hfdef
  set f' : ContDiffBump (0 : ℝ) := ⟨R / 2, R, by linarith, by linarith⟩ with hf'def
  have hf1 : ∀ t : ℝ, |t| ≤ R / 2 → f t = 1 := by
    intro t ht
    refine f.one_of_mem_closedBall ?_
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero]
    exact ht
  have hf'1 : ∀ t : ℝ, |t| ≤ R / 2 → f' t = 1 := by
    intro t ht
    refine f'.one_of_mem_closedBall ?_
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero]
    exact ht
  set F : ℝ × ℝ → E := fun q => (f q.1 * f' q.2) • u (a + q.1 ^ 2, c + q.2 ^ 2) with hFdef
  have hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F := by
    have hh : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun q : ℝ × ℝ => f q.1 * f' q.2) :=
      ((f.contDiff (n := ⊤)).comp contDiff_fst).mul ((f'.contDiff (n := ⊤)).comp contDiff_snd)
    have hΦ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun q : ℝ × ℝ => (a + q.1 ^ 2, c + q.2 ^ 2)) :=
      (contDiff_const.add (contDiff_fst.pow 2)).prodMk (contDiff_const.add (contDiff_snd.pow 2))
    have hS : IsClosed (Metric.closedBall (0 : ℝ) R ×ˢ Metric.closedBall (0 : ℝ) R) :=
      Metric.isClosed_closedBall.prod Metric.isClosed_closedBall
    have hSh : Function.support (fun q : ℝ × ℝ => f q.1 * f' q.2)
        ⊆ Metric.closedBall (0 : ℝ) R ×ˢ Metric.closedBall (0 : ℝ) R := by
      intro q hq
      rw [Function.mem_support] at hq
      have h1 : f q.1 ≠ 0 := fun h => hq (by rw [h, zero_mul])
      have h2 : f' q.2 ≠ 0 := fun h => hq (by rw [h, mul_zero])
      refine ⟨?_, ?_⟩
      · rw [← f.tsupport_eq]
        exact subset_closure h1
      · rw [← f'.tsupport_eq]
        exact subset_closure h2
    have hgood : ∀ q ∈ Metric.closedBall (0 : ℝ) R ×ˢ Metric.closedBall (0 : ℝ) R,
        ∃ U ∈ 𝓝 q, MapsTo (fun q : ℝ × ℝ => (a + q.1 ^ 2, c + q.2 ^ 2)) U (box a b c d) := by
      intro q hq
      have hq1 : |q.1| ≤ R := by
        have h := hq.1
        rwa [Metric.mem_closedBall, Real.dist_eq, sub_zero] at h
      have hq2 : |q.2| ≤ R := by
        have h := hq.2
        rwa [Metric.mem_closedBall, Real.dist_eq, sub_zero] at h
      refine ⟨Metric.ball q (R / 4), Metric.ball_mem_nhds _ (by linarith), fun q' hq' => ?_⟩
      have hdq : dist q' q < R / 4 := Metric.mem_ball.mp hq'
      have e1 : |q'.1 - q.1| ≤ dist q' q := by
        rw [Prod.dist_eq]
        calc |q'.1 - q.1| = dist q'.1 q.1 := by rw [Real.dist_eq]
          _ ≤ max (dist q'.1 q.1) (dist q'.2 q.2) := le_max_left _ _
      have e2 : |q'.2 - q.2| ≤ dist q' q := by
        rw [Prod.dist_eq]
        calc |q'.2 - q.2| = dist q'.2 q.2 := by rw [Real.dist_eq]
          _ ≤ max (dist q'.1 q.1) (dist q'.2 q.2) := le_max_right _ _
      have h3 : |q'.1| ≤ 5 * R / 4 := by
        have h := abs_sub_abs_le_abs_sub q'.1 q.1
        linarith [e1, hdq, hq1, h]
      have h4 : |q'.2| ≤ 5 * R / 4 := by
        have h := abs_sub_abs_le_abs_sub q'.2 q.2
        linarith [e2, hdq, hq2, h]
      have h5 : q'.1 ^ 2 ≤ b - a := by
        have h6 : q'.1 ^ 2 ≤ (5 * R / 4) ^ 2 := by
          refine (sq_le_sq).mpr ?_
          rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 5 * R / 4)]
          exact h3
        nlinarith [h6, hRsq, hmba, hmpos]
      have h7 : q'.2 ^ 2 ≤ d - c := by
        have h6 : q'.2 ^ 2 ≤ (5 * R / 4) ^ 2 := by
          refine (sq_le_sq).mpr ?_
          rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 5 * R / 4)]
          exact h4
        nlinarith [h6, hRsq, hmdc, hmpos]
      exact ⟨⟨by linarith [sq_nonneg q'.1], by linarith [h5]⟩,
             ⟨by linarith [sq_nonneg q'.2], by linarith [h7]⟩⟩
    exact contDiff_smul_comp_of_support_subset hu hh hΦ hS hSh hgood
  have heven2 : ∀ (σ τ : ℝ), F (σ, -τ) = F (σ, τ) := by
    intro σ τ
    rw [hFdef]
    simp only [f'.neg, neg_sq]
  have heven1 : ∀ (σ τ : ℝ), F (-σ, τ) = F (σ, τ) := by
    intro σ τ
    rw [hFdef]
    simp only [f.neg, neg_sq]
  obtain ⟨D₁, hD₁, hD₁val, hD₁even⟩ := seeleyDescentExt_even hF heven2 heven1
  have hF₂ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun q : ℝ × ℝ => D₁ (q.2, q.1)) :=
    hD₁.comp (contDiff_snd.prodMk contDiff_fst)
  have heven₂ : ∀ (v s : ℝ), (fun q : ℝ × ℝ => D₁ (q.2, q.1)) (v, -s)
      = (fun q : ℝ × ℝ => D₁ (q.2, q.1)) (v, s) := by
    intro v s
    exact hD₁even s v
  obtain ⟨D₂, hD₂, hD₂val⟩ := seeleyDescent_ext hF₂ heven₂
  refine ⟨min ((R / 4) ^ 2) ((R / 4) ^ 2), lt_min (by positivity) (by positivity),
    fun x => D₂ (x.2 - c, x.1 - a), ?_, ?_⟩
  · have hmap : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun x : ℝ × ℝ => (x.2 - c, x.1 - a)) :=
      (contDiff_snd.sub contDiff_const).prodMk (contDiff_fst.sub contDiff_const)
    exact hD₂.comp hmap
  · intro x hx hd
    show D₂ (x.2 - c, x.1 - a) = u x
    have hxa : a ≤ x.1 := hx.1.1
    have hyc : c ≤ x.2 := hx.2.1
    have h := hd
    rw [Prod.dist_eq] at h
    have h1 : dist x.1 a < (R / 4) ^ 2 :=
      lt_of_le_of_lt (le_max_left _ _) (lt_of_lt_of_le h (min_le_left _ _))
    have h2 : dist x.2 c < (R / 4) ^ 2 :=
      lt_of_le_of_lt (le_max_right _ _) (lt_of_lt_of_le h (min_le_right _ _))
    rw [Real.dist_eq] at h1 h2
    have h4 : 0 ≤ x.1 - a := by linarith
    have h4' : 0 ≤ x.2 - c := by linarith
    have h3 : x.1 - a ≤ (R / 4) ^ 2 := by
      rw [abs_of_nonneg h4] at h1
      exact le_of_lt h1
    have h3' : x.2 - c ≤ (R / 4) ^ 2 := by
      rw [abs_of_nonneg h4'] at h2
      exact le_of_lt h2
    have hD₂v : D₂ (x.2 - c, x.1 - a) = (fun q : ℝ × ℝ => D₁ (q.2, q.1)) (x.2 - c, Real.sqrt (x.1 - a)) :=
      hD₂val (x.2 - c) (x.1 - a) h4
    have hD₁v : D₁ (Real.sqrt (x.1 - a), x.2 - c) = F (Real.sqrt (x.1 - a), Real.sqrt (x.2 - c)) :=
      hD₁val (Real.sqrt (x.1 - a)) (x.2 - c) h4'
    have hFv : F (Real.sqrt (x.1 - a), Real.sqrt (x.2 - c))
        = (f (Real.sqrt (x.1 - a)) * f' (Real.sqrt (x.2 - c)))
          • u (a + (Real.sqrt (x.1 - a)) ^ 2, c + (Real.sqrt (x.2 - c)) ^ 2) := rfl
    rw [hD₂v]
    show D₁ (Real.sqrt (x.1 - a), x.2 - c) = u x
    rw [hD₁v, hFv, Real.sq_sqrt h4, Real.sq_sqrt h4']
    have h7 : Real.sqrt (x.1 - a) ≤ R / 2 := by
      have h8 : Real.sqrt (x.1 - a) ^ 2 ≤ (R / 2) ^ 2 := by
        rw [Real.sq_sqrt h4]
        nlinarith [h3, hRpos]
      nlinarith [h8, Real.sqrt_nonneg (x.1 - a), hRpos]
    have h7' : Real.sqrt (x.2 - c) ≤ R / 2 := by
      have h8 : Real.sqrt (x.2 - c) ^ 2 ≤ (R / 2) ^ 2 := by
        rw [Real.sq_sqrt h4']
        nlinarith [h3', hRpos]
      nlinarith [h8, Real.sqrt_nonneg (x.2 - c), hRpos]
    rw [hf1 _ (by rw [abs_of_nonneg (Real.sqrt_nonneg _)]; exact h7),
        hf'1 _ (by rw [abs_of_nonneg (Real.sqrt_nonneg _)]; exact h7'), one_mul, one_smul]
    congr 1
    exact Prod.ext (by ring) (by ring)


/-! ### Transport of local pieces along symmetries of the box -/

/-- Transport of a local piece along an isometric involution preserving the box. -/
theorem piece_transport_iso {a b c d : ℝ} {u : ℝ × ℝ → E} {R : ℝ × ℝ → ℝ × ℝ}
    (hRdiff : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) R) (hRiso : ∀ x y, dist (R x) (R y) = dist x y)
    (hRinv : ∀ x, R (R x) = x) (hRbox : MapsTo R (box a b c d) (box a b c d)) {p : ℝ × ℝ}
    (h : ∃ r : ℝ, 0 < r ∧ ∃ g : ℝ × ℝ → E, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g ∧
      ∀ x ∈ box a b c d, dist x (R p) < r → g x = u (R x)) :
    ∃ r : ℝ, 0 < r ∧ ∃ g : ℝ × ℝ → E, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g ∧
      ∀ x ∈ box a b c d, dist x p < r → g x = u x := by
  obtain ⟨r, hr, g, hg, hgval⟩ := h
  refine ⟨r, hr, fun x => g (R x), hg.comp hRdiff, fun x hx hd => ?_⟩
  have hx' : R x ∈ box a b c d := hRbox hx
  have hd' : dist (R x) (R p) < r := by rw [hRiso]; exact hd
  have h1 : g (R x) = u (R (R x)) := hgval (R x) hx' hd'
  rw [hRinv x] at h1
  exact h1

/-- Transport of a local piece along the coordinate swap (which exchanges the two intervals
of the box). -/
theorem piece_transport_swap {a b c d : ℝ} {u : ℝ × ℝ → E} {x₀ : ℝ}
    (h : ∃ r : ℝ, 0 < r ∧ ∃ g : ℝ × ℝ → E, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g ∧
      ∀ x ∈ box c d a b, dist x (c, x₀) < r → g x = u (x.2, x.1)) :
    ∃ r : ℝ, 0 < r ∧ ∃ g : ℝ × ℝ → E, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g ∧
      ∀ x ∈ box a b c d, dist x (x₀, c) < r → g x = u x := by
  obtain ⟨r, hr, g, hg, hgval⟩ := h
  refine ⟨r, hr, fun x => g (x.2, x.1), ?_, fun x hx hd => ?_⟩
  · exact hg.comp (contDiff_snd.prodMk contDiff_fst)
  · have hx' : (x.2, x.1) ∈ box c d a b := ⟨hx.2, hx.1⟩
    have hd' : dist (x.2, x.1) (c, x₀) < r := by
      simpa only [Prod.dist_eq, max_comm] using hd
    have h1 := hgval (x.2, x.1) hx' hd'
    simpa using h1


/-! ### Reflections of the box -/

/-- Reflection in the middle line of `[a,b]`, acting on the first coordinate. -/
def reflX (a b : ℝ) (q : ℝ × ℝ) : ℝ × ℝ := (a + b - q.1, q.2)

/-- Reflection in the middle line of `[c,d]`, acting on the second coordinate. -/
def reflY (c d : ℝ) (q : ℝ × ℝ) : ℝ × ℝ := (q.1, c + d - q.2)

lemma contDiff_reflX (a b : ℝ) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (reflX a b) :=
  (contDiff_const.sub contDiff_fst).prodMk contDiff_snd

lemma contDiff_reflY (c d : ℝ) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (reflY c d) :=
  contDiff_fst.prodMk (contDiff_const.sub contDiff_snd)

lemma dist_reflX (a b : ℝ) (x y : ℝ × ℝ) : dist (reflX a b x) (reflX a b y) = dist x y := by
  simp only [reflX, Prod.dist_eq, Real.dist_eq]
  rw [show a + b - x.1 - (a + b - y.1) = -(x.1 - y.1) by ring, abs_neg]

lemma dist_reflY (c d : ℝ) (x y : ℝ × ℝ) : dist (reflY c d x) (reflY c d y) = dist x y := by
  simp only [reflY, Prod.dist_eq, Real.dist_eq]
  rw [show c + d - x.2 - (c + d - y.2) = -(x.2 - y.2) by ring, abs_neg]

lemma reflX_invol (a b : ℝ) (x : ℝ × ℝ) : reflX a b (reflX a b x) = x := by
  simp [reflX]

lemma reflY_invol (c d : ℝ) (x : ℝ × ℝ) : reflY c d (reflY c d x) = x := by
  simp [reflY]

lemma mapsTo_reflX (a b c d : ℝ) : MapsTo (reflX a b) (box a b c d) (box a b c d) := by
  intro q hq
  rw [mem_box] at hq ⊢
  refine ⟨⟨?_, ?_⟩, hq.2⟩
  · show a ≤ a + b - q.1
    linarith [hq.1.2]
  · show a + b - q.1 ≤ b
    linarith [hq.1.1]

lemma mapsTo_reflY (a b c d : ℝ) : MapsTo (reflY c d) (box a b c d) (box a b c d) := by
  intro q hq
  rw [mem_box] at hq ⊢
  refine ⟨hq.1, ⟨?_, ?_⟩⟩
  · show c ≤ c + d - q.2
    linarith [hq.2.2]
  · show c + d - q.2 ≤ d
    linarith [hq.2.1]

lemma contDiff_swap : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Prod.swap : ℝ × ℝ → ℝ × ℝ) :=
  contDiff_snd.prodMk contDiff_fst

lemma mapsTo_swap (a b c d : ℝ) : MapsTo (Prod.swap : ℝ × ℝ → ℝ × ℝ) (box c d a b) (box a b c d) := by
  intro q hq
  rw [mem_box] at hq ⊢
  exact ⟨hq.2, hq.1⟩

/-! ### The individual pieces -/

/-- **Bottom-edge piece** (from the left-edge piece by the coordinate swap). -/
theorem piece_bottom {a b c d : ℝ} (hcd : c < d) {u : ℝ × ℝ → E}
    (hu : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u (box a b c d)) {x₀ : ℝ}
    (hx₁ : a < x₀) (hx₂ : x₀ < b) :
    ∃ r : ℝ, 0 < r ∧ ∃ g : ℝ × ℝ → E, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g ∧
      ∀ x ∈ box a b c d, dist x (x₀, c) < r → g x = u x := by
  have hsu : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun q : ℝ × ℝ => u (q.2, q.1))
      (box c d a b) :=
    hu.comp contDiff_swap.contDiffOn (mapsTo_swap a b c d)
  exact piece_transport_swap
    (h := piece_left hcd hsu (by exact hx₁) (by exact hx₂))

/-- **Right-edge piece** (from the left-edge piece by the reflection of the first coordinate). -/
theorem piece_right {a b c d : ℝ} (hab : a < b) {u : ℝ × ℝ → E}
    (hu : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u (box a b c d)) {y₀ : ℝ}
    (hy₁ : c < y₀) (hy₂ : y₀ < d) :
    ∃ r : ℝ, 0 < r ∧ ∃ g : ℝ × ℝ → E, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g ∧
      ∀ x ∈ box a b c d, dist x (b, y₀) < r → g x = u x := by
  have hXu : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (u ∘ reflX a b) (box a b c d) :=
    hu.comp (contDiff_reflX a b).contDiffOn (mapsTo_reflX a b c d)
  have hp := piece_left hab hXu hy₁ hy₂
  refine piece_transport_iso (R := reflX a b) (contDiff_reflX a b) (dist_reflX a b)
    (reflX_invol a b) (mapsTo_reflX a b c d) (p := (b, y₀)) ?_
  simpa only [reflX, Function.comp_apply, add_sub_cancel_right] using hp

/-- **Top-edge piece** (from the bottom-edge piece by the reflection of the second coordinate). -/
theorem piece_top {a b c d : ℝ} (hcd : c < d) {u : ℝ × ℝ → E}
    (hu : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u (box a b c d)) {x₀ : ℝ}
    (hx₁ : a < x₀) (hx₂ : x₀ < b) :
    ∃ r : ℝ, 0 < r ∧ ∃ g : ℝ × ℝ → E, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g ∧
      ∀ x ∈ box a b c d, dist x (x₀, d) < r → g x = u x := by
  have hYu : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (u ∘ reflY c d) (box a b c d) :=
    hu.comp (contDiff_reflY c d).contDiffOn (mapsTo_reflY a b c d)
  have hp := piece_bottom hcd hYu hx₁ hx₂
  refine piece_transport_iso (R := reflY c d) (contDiff_reflY c d) (dist_reflY c d)
    (reflY_invol c d) (mapsTo_reflY a b c d) (p := (x₀, d)) ?_
  simpa only [reflY, Function.comp_apply, add_sub_cancel_right] using hp

/-- **Corner piece at `(a,d)`.** -/
theorem piece_corner_ud {a b c d : ℝ} (hab : a < b) (hcd : c < d) {u : ℝ × ℝ → E}
    (hu : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u (box a b c d)) :
    ∃ r : ℝ, 0 < r ∧ ∃ g : ℝ × ℝ → E, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g ∧
      ∀ x ∈ box a b c d, dist x (a, d) < r → g x = u x := by
  have hYu : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (u ∘ reflY c d) (box a b c d) :=
    hu.comp (contDiff_reflY c d).contDiffOn (mapsTo_reflY a b c d)
  have hp := piece_corner hab hcd hYu
  refine piece_transport_iso (R := reflY c d) (contDiff_reflY c d) (dist_reflY c d)
    (reflY_invol c d) (mapsTo_reflY a b c d) (p := (a, d)) ?_
  simpa only [reflY, Function.comp_apply, add_sub_cancel_right] using hp

/-- **Corner piece at `(b,c)`.** -/
theorem piece_corner_ld {a b c d : ℝ} (hab : a < b) (hcd : c < d) {u : ℝ × ℝ → E}
    (hu : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u (box a b c d)) :
    ∃ r : ℝ, 0 < r ∧ ∃ g : ℝ × ℝ → E, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g ∧
      ∀ x ∈ box a b c d, dist x (b, c) < r → g x = u x := by
  have hXu : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (u ∘ reflX a b) (box a b c d) :=
    hu.comp (contDiff_reflX a b).contDiffOn (mapsTo_reflX a b c d)
  have hp := piece_corner hab hcd hXu
  refine piece_transport_iso (R := reflX a b) (contDiff_reflX a b) (dist_reflX a b)
    (reflX_invol a b) (mapsTo_reflX a b c d) (p := (b, c)) ?_
  simpa only [reflX, Function.comp_apply, add_sub_cancel_right] using hp

/-- **Corner piece at `(b,d)`.** -/
theorem piece_corner_rd {a b c d : ℝ} (hab : a < b) (hcd : c < d) {u : ℝ × ℝ → E}
    (hu : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u (box a b c d)) :
    ∃ r : ℝ, 0 < r ∧ ∃ g : ℝ × ℝ → E, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g ∧
      ∀ x ∈ box a b c d, dist x (b, d) < r → g x = u x := by
  have hXu : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (u ∘ reflX a b) (box a b c d) :=
    hu.comp (contDiff_reflX a b).contDiffOn (mapsTo_reflX a b c d)
  have hp := piece_corner_ud hab hcd hXu
  refine piece_transport_iso (R := reflX a b) (contDiff_reflX a b) (dist_reflX a b)
    (reflX_invol a b) (mapsTo_reflX a b c d) (p := (b, d)) ?_
  simpa only [reflX, Function.comp_apply, add_sub_cancel_right] using hp


/-! ### The local piece at every point, and the global extension -/

/-- The box is compact. -/
lemma isCompact_box (a b c d : ℝ) : IsCompact (box a b c d) := by
  have : box a b c d = Set.Icc a b ×ˢ Set.Icc c d := rfl
  rw [this]
  exact isCompact_Icc.prod isCompact_Icc

/-- **Local piece at every point of the box.** -/
theorem exists_local_piece {a b c d : ℝ} (hab : a < b) (hcd : c < d) {u : ℝ × ℝ → E}
    (hu : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u (box a b c d)) {p : ℝ × ℝ}
    (hp : p ∈ box a b c d) :
    ∃ r : ℝ, 0 < r ∧ ∃ g : ℝ × ℝ → E, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g ∧
      ∀ x ∈ box a b c d, dist x p < r → g x = u x := by
  obtain ⟨x₀, y₀⟩ := p
  have hxa : a ≤ x₀ := hp.1.1
  have hxb : x₀ ≤ b := hp.1.2
  have hyc : c ≤ y₀ := hp.2.1
  have hyd : y₀ ≤ d := hp.2.2
  rcases lt_or_eq_of_le hxa with h1 | h1
  · rcases lt_or_eq_of_le hxb with h2 | h2
    · rcases lt_or_eq_of_le hyc with h3 | h3
      · rcases lt_or_eq_of_le hyd with h4 | h4
        · exact piece_middle hu h1 h2 h3 h4
        · obtain rfl : y₀ = d := h4
          exact piece_top hcd hu h1 h2
      · obtain rfl : y₀ = c := h3.symm
        exact piece_bottom hcd hu h1 h2
    · obtain rfl : x₀ = b := h2
      rcases lt_or_eq_of_le hyc with h3 | h3
      · rcases lt_or_eq_of_le hyd with h4 | h4
        · exact piece_right hab hu h3 h4
        · obtain rfl : y₀ = d := h4
          exact piece_corner_rd hab hcd hu
      · obtain rfl : y₀ = c := h3.symm
        exact piece_corner_ld hab hcd hu
  · obtain rfl : x₀ = a := h1.symm
    rcases lt_or_eq_of_le hyc with h3 | h3
    · rcases lt_or_eq_of_le hyd with h4 | h4
      · exact piece_left hab hu h3 h4
      · obtain rfl : y₀ = d := h4
        exact piece_corner_ud hab hcd hu
    · obtain rfl : y₀ = c := h3.symm
      exact piece_corner hab hcd hu

/-- **Extension from a box in `ℝ × ℝ`.** -/
theorem box_ext_prod {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a b c d : ℝ) (hab : a < b) (hcd : c < d) {u : ℝ × ℝ → E}
    (hu : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u (box a b c d)) :
    ∃ g : ℝ × ℝ → E, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g ∧ ∀ x ∈ box a b c d, g x = u x := by
  refine exists_contDiff_of_isCompact_local (K := box a b c d) (isCompact_box a b c d) ?_
  intro p hp
  exact exists_local_piece hab hcd hu hp

/-! ### The target theorem -/

/-- Every `u : R^2 -> E` that is `C^inf` (Whitney, `ContDiffOn`) on the closed box
`{q | q 0 ∈ [a,b] ∧ q 1 ∈ [c,d]}` (with `a < b`, `c < d`) is the restriction of a globally
`C^inf` map `g : R^2 -> E`. -/
theorem exists_contDiff_extension_box {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (a b c d : ℝ) (hab : a < b) (hcd : c < d)
    {u : EuclideanSpace ℝ (Fin 2) → E}
    (hu : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u
      {q : EuclideanSpace ℝ (Fin 2) | q 0 ∈ Set.Icc a b ∧ q 1 ∈ Set.Icc c d}) :
    ∃ g : EuclideanSpace ℝ (Fin 2) → E, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g ∧
      ∀ x : EuclideanSpace ℝ (Fin 2), x 0 ∈ Set.Icc a b → x 1 ∈ Set.Icc c d → g x = u x := by
  set e := (EuclideanSpace.equiv (Fin 2) ℝ).trans (ContinuousLinearEquiv.finTwoArrow ℝ ℝ)
    with hedef
  have hu' : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (u ∘ e.symm) (box a b c d) := by
    refine hu.comp (e.symm.contDiff).contDiffOn ?_
    intro q hq
    rw [mem_box] at hq
    exact ⟨by rw [show (e.symm q) 0 = q.1 from rfl]; exact hq.1,
           by rw [show (e.symm q) 1 = q.2 from rfl]; exact hq.2⟩
  obtain ⟨g', hg', hg'val⟩ := box_ext_prod a b c d hab hcd hu'
  refine ⟨fun x => g' (e x), hg'.comp e.contDiff, ?_⟩
  intro x hx0 hx1
  have hxe : e x ∈ box a b c d := by
    rw [mem_box]
    exact ⟨by rw [show (e x).1 = x 0 from rfl]; exact hx0,
           by rw [show (e x).2 = x 1 from rfl]; exact hx1⟩
  have h := hg'val (e x) hxe
  change g' (e x) = u x
  rw [h, Function.comp_apply, e.symm_apply_apply]

end Work.Drive
