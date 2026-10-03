import Mathlib
import Submission.Work.L62LD.setup

namespace Work.L62LD

open Set Metric

/-!
# L62LD — `exists_chain_of_sections`

Given a holomorphic section `σb` of `ĥ = d.E - β` over a ball `ball ζc ρr` whose image lies in the
lower horn `hd.Bl`, and a holomorphic self-map `σ` of `hd.Bl` which is a section of `ĥ` on `hd.Bl`,
we produce the backward chain of discs

`W 0 = ball ζc ρ`,  `W 1 = σb '' ball ζc ρ`,  `W j = (σ^[j-1]) '' (σb '' ball ζc ρ)` (`j ≥ 1`),

with `ĥ` mapping `W (j+1)` bijectively (indeed: as the image of an injective section) onto `W j`.

The only analytic input is the open mapping theorem for holomorphic functions, used twice: `σb` is
an open map on `ball ζc ρr` and `σ` is an open map on `hd.Bl`.  Both are injective there, because
`ĥ` is a left inverse of each of them pointwise (the section equations), and a holomorphic function
which is constant on its domain would force the two-point set `{y, y + 1} ⊆ hd.Bl` (resp. the two
points `ζc`, `ζc + ρr/2`) to collapse.  Connectivity of the discs is inherited from the ball and
from the continuity of `σ`.  No differentiability of `d.E` itself is needed.
-/

theorem exists_chain_of_sections {g₀ : ℂ → ℂ} {D : Set ℂ} (d : MandelDim.ParabData g₀ D)
    (hd : MandelDim.HornData d) {β ζc : ℂ} {ρ ρr : ℝ} {σb σ : ℂ → ℂ}
    (hρ : 0 < ρ) (hρr : ρ ≤ ρr)
    (hσbd : DifferentiableOn ℂ σb (Metric.ball ζc ρr))
    (hσbsec : ∀ y ∈ Metric.ball ζc ρr, d.E (σb y) - β = y)
    (hσbBl : ∀ y ∈ Metric.ball ζc ρr, σb y ∈ hd.Bl)
    (hσd : DifferentiableOn ℂ σ hd.Bl) (hσmem : ∀ y ∈ hd.Bl, σ y ∈ hd.Bl)
    (hσsec : ∀ y ∈ hd.Bl, d.E (σ y) - β = y) :
    ∃ W : ℕ → Set ℂ, W 0 = Metric.ball ζc ρ ∧ W 1 = σb '' Metric.ball ζc ρ ∧
      Work.L62LD.Chain d hd β W ∧
      ∀ j : ℕ, 1 ≤ j → W j = (σ^[j-1]) '' (σb '' Metric.ball ζc ρ) := by
  classical
  have hρr_pos : 0 < ρr := lt_of_lt_of_le hρ hρr
  have hball_sub : Metric.ball ζc ρ ⊆ Metric.ball ζc ρr := Metric.ball_subset_ball hρr
  -- `σb` is an open map on the ball `ball ζc ρr`
  have hopen_b : ∀ s ⊆ Metric.ball ζc ρr, IsOpen s → IsOpen (σb '' s) := by
    have hσb_an : AnalyticOnNhd ℂ σb (Metric.ball ζc ρr) :=
      hσbd.analyticOnNhd Metric.isOpen_ball
    rcases hσb_an.is_constant_or_isOpen (convex_ball ζc ρr).isPreconnected with ⟨c, hc⟩ | h
    · -- `σb` cannot be constant: `ĥ ∘ σb = id` would collapse the ball to a point
      exfalso
      have h1 : ζc ∈ Metric.ball ζc ρr := Metric.mem_ball_self hρr_pos
      have h2 : ζc + (ρr / 2 : ℝ) ∈ Metric.ball ζc ρr := by
        rw [Metric.mem_ball, Complex.dist_eq, add_sub_cancel_left,
          show ‖(((ρr / 2 : ℝ)) : ℂ)‖ = ρr/2 from by
            rw [Complex.norm_def, Complex.normSq_ofReal, ← sq, Real.sqrt_sq_eq_abs,
              abs_of_pos (by linarith)]]
        linarith
      have e1 : d.E c - β = ζc := by rw [← hc ζc h1]; exact hσbsec ζc h1
      have e2 : d.E c - β = ζc + (ρr / 2 : ℝ) := by
        rw [← hc (ζc + (ρr/2:ℝ)) h2]; exact hσbsec _ h2
      have h4 : ζc = ζc + ((ρr / 2 : ℝ) : ℂ) := e1.symm.trans e2
      have h5 : ((ρr / 2 : ℝ) : ℂ) = 0 :=
        add_left_cancel (show ζc + ((ρr / 2 : ℝ) : ℂ) = ζc + 0 by rw [add_zero]; exact h4.symm)
      have h6 : ρr / 2 = 0 := Complex.ofReal_eq_zero.mp h5
      linarith
    · exact h
  -- `σ` is an open map on the lower horn `hd.Bl`
  have hopen_σ : ∀ s ⊆ hd.Bl, IsOpen s → IsOpen (σ '' s) := by
    have hσ_an : AnalyticOnNhd ℂ σ hd.Bl := hσd.analyticOnNhd hd.Bl_open
    rcases hσ_an.is_constant_or_isOpen hd.Bl_conn.2 with ⟨c, hc⟩ | h
    · -- `σ` cannot be constant: `hd.Bl` is `T`-invariant, hence has two points
      exfalso
      obtain ⟨w, hw⟩ := hd.Bl_conn.1
      have hw1 : w + 1 ∈ hd.Bl := (hd.Bl_T w).mp hw
      have e1 : d.E c - β = w := by rw [← hc w hw]; exact hσsec w hw
      have e2 : d.E c - β = w + 1 := by rw [← hc (w+1) hw1]; exact hσsec (w+1) hw1
      have h5 : w = w + 1 := e1.symm.trans e2
      have h6 : (0:ℂ) = 1 := add_left_cancel (show w + 0 = w + 1 by rw [add_zero]; exact h5)
      exact zero_ne_one h6
    · exact h
  have hS_open : IsOpen (σb '' Metric.ball ζc ρ) := hopen_b _ hball_sub Metric.isOpen_ball
  have hS_conn : IsConnected (σb '' Metric.ball ζc ρ) :=
    (Metric.isConnected_ball hρ).image σb (hσbd.mono hball_sub).continuousOn
  have hS_sub : (σb '' Metric.ball ζc ρ) ⊆ hd.Bl := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact hσbBl x (hball_sub hx)
  -- the iterates of `S = σb '' ball ζc ρ` stay open, connected and inside `hd.Bl`
  have key : ∀ k : ℕ, IsOpen ((σ^[k]) '' (σb '' Metric.ball ζc ρ)) ∧
      IsConnected ((σ^[k]) '' (σb '' Metric.ball ζc ρ)) ∧
      ((σ^[k]) '' (σb '' Metric.ball ζc ρ)) ⊆ hd.Bl := by
    intro k
    induction k with
    | zero => exact ⟨by simpa using hS_open, by simpa using hS_conn, by simpa using hS_sub⟩
    | succ k ih =>
        obtain ⟨ho, hc, hs⟩ := ih
        have himg : (σ^[k.succ]) '' (σb '' Metric.ball ζc ρ)
            = σ '' ((σ^[k]) '' (σb '' Metric.ball ζc ρ)) := by
          rw [Function.iterate_succ', Set.image_comp]
        refine ⟨?_, ?_, ?_⟩
        · rw [himg]; exact hopen_σ _ hs ho
        · rw [himg]; exact hc.image σ ((hσd.mono hs).continuousOn)
        · rw [himg]
          intro y hy
          obtain ⟨x, hx, rfl⟩ := hy
          exact hσmem x (hs hx)
  -- on `hd.Bl`, `σ` is a bijection onto its image with inverse `ĥ`
  have himg_gen : ∀ s : Set ℂ, s ⊆ hd.Bl → (fun w => d.E w - β) '' (σ '' s) = s := by
    intro s hs
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨z, hz, rfl⟩ := hx
      change d.E (σ z) - β ∈ s
      rw [hσsec z (hs hz)]
      exact hz
    · intro hy
      exact ⟨σ y, ⟨y, hy, rfl⟩, hσsec y (hs hy)⟩
  have hinj_gen : ∀ s : Set ℂ, s ⊆ hd.Bl → Set.InjOn (fun w => d.E w - β) (σ '' s) := by
    intro s hs w1 hw1 w2 hw2 heq
    obtain ⟨y1, hy1, rfl⟩ := hw1
    obtain ⟨y2, hy2, rfl⟩ := hw2
    change d.E (σ y1) - β = d.E (σ y2) - β at heq
    rw [hσsec y1 (hs hy1), hσsec y2 (hs hy2)] at heq
    subst heq
    rfl
  -- the chain of discs
  let W : ℕ → Set ℂ := fun j => match j with
    | 0 => Metric.ball ζc ρ
    | (k+1) => (σ^[k]) '' (σb '' Metric.ball ζc ρ)
  have hW0 : W 0 = Metric.ball ζc ρ := rfl
  have hW1 : W 1 = σb '' Metric.ball ζc ρ := by simp [W]
  have hWvar : ∀ j : ℕ, j ≠ 0 → W j = (σ^[j-1]) '' (σb '' Metric.ball ζc ρ) := by
    intro j hj
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj
    simp [W]
  have hWsucc : ∀ j : ℕ, 1 ≤ j → W (j+1) = σ '' W j := by
    intro j hj
    have hj1 : W j = (σ^[j-1]) '' (σb '' Metric.ball ζc ρ) := hWvar j (by omega)
    have hWj1 : W (j+1) = (σ^[j]) '' (σb '' Metric.ball ζc ρ) := by
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
      simp [W]
    have hiter : (σ^[j]) '' (σb '' Metric.ball ζc ρ)
        = σ '' ((σ^[j-1]) '' (σb '' Metric.ball ζc ρ)) := by
      rw [show (σ^[j]) = σ ∘ (σ^[j-1]) from by
            rw [← Nat.succ_pred_eq_of_pos (show 0 < j by omega)]
            exact Function.iterate_succ' σ (j - 1), Set.image_comp]
    rw [hWj1, hiter, hj1]
  have hWopen : ∀ j : ℕ, IsOpen (W j) := by
    intro j
    rcases eq_or_ne j 0 with rfl | hj
    · rw [hW0]; exact Metric.isOpen_ball
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj
      have h := hWvar (m+1) (by omega)
      rw [show (m+1-1) = m from rfl] at h
      rw [h]
      exact (key m).1
  have hWconn : ∀ j : ℕ, IsConnected (W j) := by
    intro j
    rcases eq_or_ne j 0 with rfl | hj
    · rw [hW0]; exact Metric.isConnected_ball hρ
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj
      have h := hWvar (m+1) (by omega)
      rw [show (m+1-1) = m from rfl] at h
      rw [h]
      exact (key m).2.1
  have hWsub : ∀ j : ℕ, 1 ≤ j → W j ⊆ hd.Bl := by
    intro j hj
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
    have h := hWvar (m+1) (by omega)
    rw [show (m+1-1) = m from rfl] at h
    rw [h]
    exact (key m).2.2
  have hWinj : ∀ j : ℕ, Set.InjOn (fun w => d.E w - β) (W (j+1)) := by
    intro j
    rcases eq_or_ne j 0 with rfl | hj
    · rw [hW1]
      intro w1 hw1 w2 hw2 heq
      obtain ⟨y1, hy1, rfl⟩ := hw1
      obtain ⟨y2, hy2, rfl⟩ := hw2
      change d.E (σb y1) - β = d.E (σb y2) - β at heq
      rw [hσbsec y1 (hball_sub hy1), hσbsec y2 (hball_sub hy2)] at heq
      subst heq
      rfl
    · rw [hWsucc j (by omega)]
      exact hinj_gen (W j) (hWsub j (by omega))
  have hWimg : ∀ j : ℕ, (fun w => d.E w - β) '' W (j+1) = W j := by
    intro j
    rcases eq_or_ne j 0 with rfl | hj
    · rw [hW1, hW0]
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        obtain ⟨z, hz, rfl⟩ := hx
        change d.E (σb z) - β ∈ Metric.ball ζc ρ
        rw [hσbsec z (hball_sub hz)]
        exact hz
      · intro hy
        exact ⟨σb y, ⟨y, hy, rfl⟩, hσbsec y (hball_sub hy)⟩
    · rw [hWsucc j (by omega)]
      exact himg_gen (W j) (hWsub j (by omega))
  exact ⟨W, hW0, hW1, ⟨fun j => ⟨hWopen j, hWconn j⟩, hWinj, hWimg, hWsub⟩,
    fun j hj => hWvar j (by omega)⟩

end Work.L62LD
