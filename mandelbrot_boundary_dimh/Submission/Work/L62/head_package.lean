import Mathlib
import Submission.Work.L62.l62c_end
import Submission.Work.L62.exact_head
import Submission.Work.L62.fin_sep
import Submission.Work.L62.stab_hyp
import Submission.Work.L62.collar_radius
import Submission.Work.Horn.horn_crit_orbit_F0

namespace Work.L62

open MandelDim Set Metric Filter Topology
open scoped Topology

noncomputable section

/-! ## Elementary toolbox -/

/-- The difference of the imaginary parts is bounded by the norm. -/
private lemma abs_im_sub_le (a b : ℂ) : |a.im - b.im| ≤ ‖a - b‖ := by
  have h : (a - b).im = a.im - b.im := Complex.sub_im a b
  rw [← h]
  exact Complex.abs_im_le_norm _

/-- Multiplication by `s = ±1` does not change absolute values of differences. -/
private lemma abs_mul_sub_mul {s : ℝ} (hs : s = 1 ∨ s = -1) (x y : ℝ) :
    |s * x - s * y| = |x - y| := by
  rcases hs with rfl | rfl
  · simp
  · rw [show (-1 : ℝ) * x - (-1) * y = y - x by ring, abs_sub_comm]

/-- `s * Im w` differs from `s * Im z` by at most the norm distance. -/
private lemma abs_smul_im_sub {s : ℝ} (hs : s = 1 ∨ s = -1) {w z : ℂ} {r : ℝ}
    (h : ‖w - z‖ < r) : |s * w.im - s * z.im| < r := by
  calc |s * w.im - s * z.im| = |w.im - z.im| := abs_mul_sub_mul hs w.im z.im
    _ ≤ ‖w - z‖ := abs_im_sub_le w z
    _ < r := h

/-- **`ℤ`-separation of balls.**  If every point of `W i` lies within `r` of `z i` and the centres
`z i` are pairwise separated by `εsep > 2 r` modulo `ℤ`, then the `piExp`-images of the `W i` are
pairwise disjoint. -/
private theorem piExp_disjoint_of_sep {z : ℕ → ℂ} {W : ℕ → Set ℂ} {r εsep : ℝ} {J : ℕ}
    (h2r : 2 * r < εsep)
    (hcent : ∀ i, i ≤ J → ∀ u ∈ W i, ‖u - z i‖ < r)
    (hεsep : ∀ i j, i ≤ J → j ≤ J → i ≠ j → ∀ k : ℤ, εsep ≤ ‖z i - z j - (k : ℂ)‖) :
    ∀ i j, i ≤ J → j ≤ J → i ≠ j → Disjoint (piExp '' W i) (piExp '' W j) := by
  intro i j hi hj hij
  rw [Set.disjoint_left]
  rintro x ⟨u, hu, rfl⟩ ⟨v, hv, huv⟩
  obtain ⟨k, hk⟩ := (piExp_eq_iff_exists_int u v).mp huv.symm
  have hzero : u - v - (k : ℂ) = 0 := by rw [hk]; ring
  have hle : ‖z i - z j - (k : ℂ)‖ ≤ ‖z i - u‖ + ‖u - v - (k : ℂ)‖ + ‖v - z j‖ := by
    have heq : z i - z j - (k : ℂ) = (z i - u) + (u - v - (k : ℂ)) + (v - z j) := by ring
    rw [heq]
    exact norm_add₃_le
  have h1 : ‖z i - u‖ < r := by simpa [norm_sub_rev] using hcent i hi u hu
  have h2 : ‖v - z j‖ < r := hcent j hj v hv
  have h3 := hεsep i j hi hj hij k
  rw [hzero, norm_zero, add_zero] at hle
  linarith

/-! ## The assembly -/

theorem head_package {g₀ : ℂ → ℂ} {D : Set ℂ} (d : MandelDim.ParabData g₀ D)
    (hd : MandelDim.HornData d) {b κ Y : ℝ} (hb : 0 < b) (hκ : 0 < κ) (hY : d.η₀ + 2 < Y)
    (hstab : Work.L62.StabHyp d)
    {cl : ℂ} (hcl : Filter.Tendsto (fun w => d.E w - w) MandelDim.lowerEnd (nhds cl))
    {ζa ζb : ℂ} (hζa : ζa ∉ d.DE) (hζb : ζb ∉ d.DE) (hsep : ∀ k : ℤ, ζa ≠ ζb + (k : ℂ)) :
    ∀ β : ℂ, 0 ≤ β.re → β.re ≤ 1 → |β.im| ≤ b → ∀ s : ℝ,
      ((s = 1 ∧ Work.L62.AvailableUp d hd β ∧ κ ≤ β.im) ∨
        (s = -1 ∧ Work.L62.AvailableDown d hd β ∧ κ ≤ cl.im - β.im)) →
      ∃ (ζ : ℂ) (j₀ : ℕ) (ρ₁ ε δ C C' : ℝ) (A : Set ℂ),
        (ζ = ζa ∨ ζ = ζb) ∧ 0 < j₀ ∧ 0 < ρ₁ ∧ 0 < ε ∧ 0 < δ ∧ 0 < C ∧ 0 < C' ∧
        ρ₁ < κ / 16 ∧ ρ₁ < 1 / 48 ∧ IsCompact A ∧ A ⊆ d.DE ∧
        ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₁ → ∀ β' : ℂ, ‖β' - β‖ < ε →
          ∀ (R : ℂ → ℂ) (DR : Set ℂ), IsOpen DR → A ⊆ DR → DifferentiableOn ℂ R DR →
            (∀ w ∈ A, ‖R w - d.E w‖ < δ) →
            ∃ W : ℕ → Set ℂ, W 0 = Metric.ball ζ ρ ∧
              (∀ j, j ≤ j₀ → IsOpen (W j) ∧ IsConnected (W j) ∧ Bornology.IsBounded (W j) ∧
                Metric.diam (W j) < 1 / 2) ∧
              (∀ j, j < j₀ → W (j + 1) ⊆ A ∧
                Set.InjOn (fun w => R w - β') (W (j + 1)) ∧
                (fun w => R w - β') '' W (j + 1) = W j ∧
                (∀ u ∈ W (j + 1), C < ‖deriv ((fun u => R u - β')^[j + 1]) u‖ ∧
                  ‖deriv ((fun u => R u - β')^[j + 1]) u‖ < C')) ∧
              (∀ i j, i ≤ j₀ → j ≤ j₀ → i ≠ j →
                Disjoint (MandelDim.piExp '' W i) (MandelDim.piExp '' W j)) ∧
              (∀ w ∈ W j₀, Y < s * w.im) ∧
              (∀ j, j < j₀ → ∀ w ∈ W j, s * w.im < Y + κ / 8) ∧
              Metric.diam (W j₀) ≤ 1 / 24 ∧ 3 * Metric.diam (W j₀) < κ / 4 := by
  intro β hβ0 hβ1 hβim s hs
  have hs_sign : s = 1 ∨ s = -1 := hs.imp (fun h => h.1) (fun h => h.1)
  -- the depth at which the exact chain stops
  set Y' : ℝ := Y + κ / 16 - 1 with hY'def
  have hηY' : d.η₀ < Y' := by rw [hY'def]; linarith
  -- the exact (unperturbed) point chain
  obtain ⟨ζ, hζ, j₀, hj₀pos, z, hz0, hzpoint, hzdeep, hzmin, hzsep⟩ :=
    exact_head d hd hb hκ hcl hζa hζb hsep (Y := Y') hηY' β hβ0 hβ1 hβim s hs
  have hζDE : ζ ∉ d.DE := by
    rcases hζ with h | h
    · rw [h]; exact hζa
    · rw [h]; exact hζb
  -- a uniform separation modulus of the points of the chain
  obtain ⟨εsep, hεseppos, hεsep⟩ := fin_sep (z := z) (J := j₀) hzsep
  -- a collar radius around the chain inside `d.DE`
  obtain ⟨r₀, hr₀pos, hr₀sub⟩ :=
    collar_radius (Work.Horn.isOpen_DE d) (fun j h1 h2 => (hzpoint j h1 h2).1)
  -- the working radius
  set r : ℝ := min (min (εsep / 4) (κ / 64)) (min (1 / 96) r₀) with hrdef
  have hrpos : 0 < r := by
    rw [hrdef]
    exact lt_min (lt_min (by linarith) (by linarith)) (lt_min (by norm_num) hr₀pos)
  have hr_le_ε : r ≤ εsep / 4 := by
    rw [hrdef]; exact le_trans (min_le_left _ _) (min_le_left _ _)
  have hr_le_κ : r ≤ κ / 64 := by
    rw [hrdef]; exact le_trans (min_le_left _ _) (min_le_right _ _)
  have hr_le_96 : r ≤ 1 / 96 := by
    rw [hrdef]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hr_le_r₀ : r ≤ r₀ := by
    rw [hrdef]; exact le_trans (min_le_right _ _) (min_le_right _ _)
  have hr8 : r < 1 / 8 := by linarith
  have hcollar : (⋃ j ∈ Finset.Icc 1 j₀, Metric.closedBall (z j) (2 * r)) ⊆ d.DE :=
    Set.Subset.trans
      (Set.iUnion_mono (fun j =>
        Set.iUnion_mono (fun _ => Metric.closedBall_subset_closedBall (by linarith))))
      hr₀sub
  -- the perturbed inverse branches of the head
  obtain ⟨ρ₁, ε, δ, C, C', hρ₁pos, hρ₁le, hεpos, hδpos, hCpos, hC'pos, hKcompact, hmain⟩ :=
    hstab β j₀ hj₀pos ζ z hz0 hzpoint r hrpos hr8 hcollar
  have hρ₁lt16 : ρ₁ < κ / 16 := by
    have : ρ₁ ≤ κ / 64 := le_trans hρ₁le hr_le_κ
    linarith
  have hρ₁lt48 : ρ₁ < 1 / 48 := by
    have : ρ₁ ≤ 1 / 96 := le_trans hρ₁le hr_le_96
    linarith
  let A : Set ℂ := ⋃ j ∈ Finset.Icc 1 j₀, Metric.closedBall (z j) (2 * r)
  have hAcompact : IsCompact A := hKcompact
  have hADE : A ⊆ d.DE := hcollar
  refine ⟨ζ, j₀, ρ₁, ε, δ, C, C', A, hζ, hj₀pos, hρ₁pos, hεpos, hδpos, hCpos, hC'pos,
    hρ₁lt16, hρ₁lt48, hAcompact, hADE, ?_⟩
  intro ρ hρpos hρρ₁ β' hβ' R DR hDRopen hADR hDRdiff hRclose
  have hρr : ρ ≤ r := le_trans hρρ₁ hρ₁le
  obtain ⟨W, hW0, hWchain⟩ :=
    hmain ρ hρpos hρρ₁ β' hβ' R DR hDRopen hADR hDRdiff hRclose
  -- the centre of `W i` is within `r` of `z i`
  have hcent : ∀ i, i ≤ j₀ → ∀ u ∈ W i, ‖u - z i‖ < r := by
    intro i hi u hu
    rcases Nat.eq_zero_or_pos i with hi0 | hipos
    · subst hi0
      rw [hW0, Metric.mem_ball] at hu
      have h1 : ‖u - ζ‖ < ρ := by simpa [dist_eq_norm] using hu
      rw [hz0]
      linarith
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hipos)
      have hk : k < j₀ := by omega
      have hbal : u ∈ Metric.ball (z (k + 1)) r := (hWchain k hk).1 hu
      simpa [Metric.mem_ball, dist_eq_norm] using hbal
  -- diameter of the final disc
  have hdiam0 : Metric.diam (W j₀) ≤ 2 * r := by
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hj₀pos)
    have hk' : j₀ = k + 1 := hk
    have hsub : W (k + 1) ⊆ Metric.ball (z (k + 1)) r := (hWchain k (by omega)).1
    have hd := le_trans (Metric.diam_mono hsub Metric.isBounded_ball)
      (Metric.diam_ball (x := z (k + 1)) (le_of_lt hrpos))
    rw [hk']
    exact hd
  refine ⟨W, hW0, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- every disc of the head is open, connected, bounded and small
    intro j hj
    rcases Nat.eq_zero_or_pos j with hj0 | hjpos
    · subst hj0
      rw [hW0]
      refine ⟨Metric.isOpen_ball, ?_, Metric.isBounded_ball, ?_⟩
      · exact (convex_ball ζ ρ).isConnected ⟨ζ, Metric.mem_ball_self hρpos⟩
      · have h := Metric.diam_ball (x := ζ) (le_of_lt hρpos)
        linarith
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hjpos)
      have hk : k < j₀ := by omega
      obtain ⟨hsub, hopen, hconn, hbdd, -, -, -⟩ := hWchain k hk
      refine ⟨hopen, hconn, hbdd, ?_⟩
      calc Metric.diam (W (k + 1)) ≤ Metric.diam (Metric.ball (z (k + 1)) r) :=
            Metric.diam_mono hsub Metric.isBounded_ball
        _ ≤ 2 * r := Metric.diam_ball (x := z (k + 1)) (le_of_lt hrpos)
        _ < 1 / 2 := by linarith
  · -- the chain conditions and the derivative bounds
    intro j hj
    obtain ⟨hsub, -, -, -, hinj, himg, hder⟩ := hWchain j hj
    refine ⟨?_, hinj, himg, hder⟩
    intro w hw
    exact Set.subset_biUnion_of_mem (u := fun j => Metric.closedBall (z j) (2 * r))
      (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
      (Metric.closedBall_subset_closedBall (by linarith)
        (Metric.ball_subset_closedBall (hsub hw)))
  · -- `ℤ`-separation of the discs
    refine piExp_disjoint_of_sep (z := z) (W := W) (J := j₀) (r := r) (εsep := εsep)
      (by linarith) hcent hεsep
  · -- the last disc is beyond the depth `Y`
    intro w hw
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hj₀pos)
    have hk' : j₀ = k + 1 := hk
    have hbal : w ∈ Metric.ball (z (k + 1)) r := by
      rw [hk'] at hw
      exact (hWchain k (by omega)).1 hw
    have hwz : ‖w - z (k + 1)‖ < r := by simpa [Metric.mem_ball, dist_eq_norm] using hbal
    obtain ⟨hl, hr⟩ := abs_lt.mp (abs_smul_im_sub hs_sign hwz)
    have hdeep : Y' + 1 < s * (z (k + 1)).im := by
      have h := hzdeep
      rw [hk'] at h
      exact h
    linarith
  · -- the discs before the last stay below `Y + κ/8`
    intro j hj w hw
    rcases Nat.eq_zero_or_pos j with hj0 | hjpos
    · subst hj0
      rw [hW0, Metric.mem_ball] at hw
      have h1 : ‖w - ζ‖ < ρ := by simpa [dist_eq_norm] using hw
      obtain ⟨hl, hr⟩ :=
        abs_lt.mp (abs_smul_im_sub hs_sign (lt_of_lt_of_le h1 hρr))
      have hζim : |ζ.im| ≤ d.η₀ := abs_im_le_eta0_of_not_mem_DE d hζDE
      have hup : s * ζ.im ≤ |ζ.im| := by
        rcases hs_sign with rfl | rfl
        · simpa using le_abs_self ζ.im
        · simpa using neg_le_abs ζ.im
      linarith
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hjpos)
      have hk : k < j₀ := by omega
      have hbal : w ∈ Metric.ball (z (k + 1)) r := (hWchain k hk).1 hw
      have hwz : ‖w - z (k + 1)‖ < r := by simpa [Metric.mem_ball, dist_eq_norm] using hbal
      obtain ⟨hl, hr⟩ := abs_lt.mp (abs_smul_im_sub hs_sign hwz)
      have hlow := hzmin (k + 1) (by omega)
      linarith
  · linarith
  · linarith

end

end Work.L62
