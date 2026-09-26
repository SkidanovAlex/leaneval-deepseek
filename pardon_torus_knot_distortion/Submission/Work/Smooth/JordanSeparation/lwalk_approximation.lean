import Mathlib
import Submission.Work.Smooth.JordanSeparation.lwalk_basic
import Submission.Work.Smooth.JordanSeparation.lwalk_stair
import Submission.Work.Smooth.JordanSeparation.lwalk_gen
import Submission.Work.Smooth.JordanSeparation.lwalk_peel
import Submission.Work.Smooth.JordanSeparation.loopNat_homotopy_unpack
import Submission.Work.Smooth.JordanSeparation.gridWalk_approx
import Submission.Work.Smooth.JordanSeparation.plApproxLoop
import Submission.Work.SphereJordan.ladder_walk
import Submission.Work.SphereJordan.ladder_trace

/-!
# Approximation of a loop in an open set by a closed lattice walk

`lwalk_approximation`: a loop `γ` in an open `U ⊆ ℂ` is homotopic *in* `↥U` to a conjugate
`a · loopIn W · a⁻¹` of the realization of a closed lattice walk `W` whose trace lies in `U`.

The walk is built from the **ladder walk** of `Work.SphereJordan.ladder_walk`.
-/

namespace Work.Smooth.JordanSeparation

open Set Metric
open Work.SphereJordan

noncomputable section

set_option maxHeartbeats 8000000



/-- **Splitting a `joinNat` into blocks of length twelve.** -/
theorem joinNat_block_decomp {X : Type*} [TopologicalSpace X] {p : ℕ → X}
    (F : ∀ k, Path (p k) (p (k + 1))) :
    ∀ N : ℕ, Path.Homotopic (joinNat F (12 * N))
      (joinNat (fun k => joinNat (fun j => F (12 * k + j)) 12) N) := by
  intro N
  induction N with
  | zero => exact Path.Homotopic.refl _
  | succ N ih =>
    refine (joinNat_add F (12 * N) 12).trans ?_
    rw [show joinNat (fun k => joinNat (fun j => F (12 * k + j)) 12) (N + 1)
        = (joinNat (fun k => joinNat (fun j => F (12 * k + j)) 12) N).trans
          (joinNat (fun j => F (12 * N + j)) 12) from rfl]
    exact Path.Homotopic.hcomp ih (Path.Homotopic.refl _)

/-- Membership of the values of a `joinNat`, from membership of the pieces. -/
theorem joinNat_mem_le {X : Type*} [TopologicalSpace X] {p : ℕ → X}
    {F : ∀ k, Path (p k) (p (k + 1))} {S : Set X} {n : ℕ}
    (h0 : p 0 ∈ S) (hF : ∀ k, k < n → ∀ u, F k u ∈ S) :
    ∀ j ≤ n, ∀ u, joinNat F j u ∈ S := by
  intro j
  induction j with
  | zero => intro _ u; rw [joinNat, Path.refl_apply]; exact h0
  | succ j ih =>
    intro hj u
    rw [show joinNat F (j + 1) = (joinNat F j).trans (F j) from rfl, Path.trans_apply]
    split_ifs with h
    · exact ih (by omega) _
    · exact hF j (by omega) _

/-- A vertex of the ladder walk whose index lies in the `k`-th block stays within `16 * c` of the
value of `g` at the left end of that block. -/
theorem ladderWalk_pt_near_block {g : unitInterval → ℂ} {t : ℕ → unitInterval} {c : ℝ}
    (hc : 0 < c) {lad : ℕ → ℤ × ℤ} {N : ℕ}
    (hlad : ∀ k ≤ N, lad k = snap (g (t k) / (c : ℂ)))
    (hgstep : ∀ k ≤ N, dist (g (t k)) (g (t (k + 1))) ≤ c)
    {hq : ∀ k ≤ N, |(dl lad k).1| ≤ 6 ∧ |(dl lad k).2| ≤ 6}
    {hp1 : ∀ k ≤ N, (dl lad k).1.natAbs % 2 = 0}
    {hp2 : ∀ k ≤ N, (dl lad k).2.natAbs % 2 = 0}
    {hclosed : lad N = lad 0} {k m : ℕ} (hk : k < N) (hm : 12 * k ≤ m)
    (hm' : m ≤ 12 * (k + 1)) :
    ‖(ladderWalk N c hc lad hq hp1 hp2 hclosed).pt m - g (t k)‖ ≤ 16 * c := by
  have hmN : m ≤ 12 * N := by
    calc m ≤ 12 * (k + 1) := hm'
      _ ≤ 12 * N := Nat.mul_le_mul_left 12 (by omega)
  have h1 := ladderWalk_pt_le (lad := lad) (N := N) (g := g) (t := t) hc hlad
    (hq := hq) (hp1 := hp1) (hp2 := hp2) (hclosed := hclosed) (m := m) hmN
  have hbo : (bo m).1 = k ∨ (bo m).1 = k + 1 := by
    rw [bo_eq_div]
    have h2 : 12 * k ≤ m := hm
    omega
  have hstep : dist (g (t ((bo m).1))) (g (t k)) ≤ c := by
    rcases hbo with h | h
    · rw [h, dist_self]; exact le_of_lt hc
    · rw [h, dist_comm]; exact hgstep k (le_of_lt hk)
  have hstep' : ‖g (t ((bo m).1)) - g (t k)‖ ≤ c := by
    rw [← dist_eq_norm]; exact hstep
  calc ‖(ladderWalk N c hc lad hq hp1 hp2 hclosed).pt m - g (t k)‖
      = ‖((ladderWalk N c hc lad hq hp1 hp2 hclosed).pt m - g (t ((bo m).1)))
          + (g (t ((bo m).1)) - g (t k))‖ := by ring_nf
    _ ≤ ‖(ladderWalk N c hc lad hq hp1 hp2 hclosed).pt m - g (t ((bo m).1))‖
          + ‖g (t ((bo m).1)) - g (t k)‖ := norm_add_le _ _
    _ ≤ 15 * c + c := add_le_add h1 hstep'
    _ = 16 * c := by ring


/-- A vertex of the ladder walk whose index lies in the `k`-th block lies in the ball of radius
`δ` around `g (t k)`. -/
theorem ladderWalk_pt_mem_ball {g : unitInterval → ℂ} {t : ℕ → unitInterval} {c δ : ℝ}
    (hc : 0 < c) (hcδ : 16 * c < δ) {lad : ℕ → ℤ × ℤ} {N : ℕ}
    (hlad : ∀ k ≤ N, lad k = snap (g (t k) / (c : ℂ)))
    (hgstep : ∀ k ≤ N, dist (g (t k)) (g (t (k + 1))) ≤ c)
    {hq : ∀ k ≤ N, |(dl lad k).1| ≤ 6 ∧ |(dl lad k).2| ≤ 6}
    {hp1 : ∀ k ≤ N, (dl lad k).1.natAbs % 2 = 0}
    {hp2 : ∀ k ≤ N, (dl lad k).2.natAbs % 2 = 0}
    {hclosed : lad N = lad 0} {k m : ℕ} (hk : k < N) (hm : 12 * k ≤ m)
    (hm' : m ≤ 12 * (k + 1)) :
    (ladderWalk N c hc lad hq hp1 hp2 hclosed).pt m ∈ Metric.ball (g (t k)) δ := by
  rw [Metric.mem_ball, dist_eq_norm]
  exact lt_of_le_of_lt (ladderWalk_pt_near_block hc hlad hgstep hk hm hm') hcδ

/-- `gpt` is additive for subtraction. -/
theorem gpt_sub_eq (p q : ℤ × ℤ) : gpt (p - q) = gpt p - gpt q := by
  simp only [gpt, Prod.fst_sub, Prod.snd_sub]
  push_cast
  ring

/-- An integer pair whose `gpt`-image is within `5` of the origin has coordinates of absolute
value at most `6`. -/
theorem int_abs_le_of_norm_gpt_le {z : ℤ × ℤ} (h : ‖gpt z‖ ≤ 5) :
    |z.1| ≤ 6 ∧ |z.2| ≤ 6 := by
  have h1 : |((z.1 : ℤ) : ℝ)| ≤ 5 := by
    have := Complex.abs_re_le_norm (gpt z)
    rw [gpt_re] at this
    linarith
  have h2 : |((z.2 : ℤ) : ℝ)| ≤ 5 := by
    have := Complex.abs_im_le_norm (gpt z)
    rw [gpt_im] at this
    linarith
  constructor
  · have hle : ((|z.1| : ℤ) : ℝ) ≤ 6 := by rw [Int.cast_abs]; linarith
    exact (Int.cast_le (R := ℝ)).mp hle
  · have hle : ((|z.2| : ℤ) : ℝ) ≤ 6 := by rw [Int.cast_abs]; linarith
    exact (Int.cast_le (R := ℝ)).mp hle

/-- The parity of a difference of two even integers. -/
theorem natAbs_mod_two_sub {a b : ℤ} (h1 : a.natAbs % 2 = 0) (h2 : b.natAbs % 2 = 0) :
    (a - b).natAbs % 2 = 0 := by
  have e1 : Even a := Int.natAbs_even.mp (Nat.even_iff.mpr h1)
  have e2 : Even b := Int.natAbs_even.mp (Nat.even_iff.mpr h2)
  exact Nat.even_iff.mp (Int.natAbs_even.mpr (Int.even_sub.mpr ⟨fun _ => e2, fun _ => e1⟩))

theorem lwalk_approximation {U : Set ℂ} (hUo : IsOpen U) {x : ℂ} (hx : x ∈ U)
    (γ : Path (⟨x, hx⟩ : ↥U) (⟨x, hx⟩ : ↥U)) :
    ∃ (W : LWalk) (hbase : W.pt 0 ∈ U) (hval : ∀ t, W.path t ∈ U)
      (a : Path (⟨x, hx⟩ : ↥U) (⟨W.pt 0, hbase⟩ : ↥U)),
      Path.Homotopic γ (a.trans ((W.loopIn hbase hval).trans a.symm)) := by
  classical
  obtain ⟨δ, hδpos, hδU⟩ := exists_ball_subset_of_path hUo hx γ
  set c : ℝ := δ / 100 with hcdef
  have hcpos : 0 < c := by rw [hcdef]; linarith
  have hcδ : 16 * c < δ := by rw [hcdef]; linarith
  -- ### the partition of the unit interval
  set cov : unitInterval → Set unitInterval := fun s =>
    (fun u : unitInterval => ((γ u : ↥U) : ℂ)) ⁻¹' Metric.ball (((γ s : ↥U) : ℂ)) (c / 2)
    with hcovdef
  have hcovopen : ∀ s, IsOpen (cov s) := fun s =>
    isOpen_ball.preimage (continuous_subtype_val.comp γ.continuous)
  have hcovuniv : (univ : Set unitInterval) ⊆ ⋃ s, cov s := by
    intro u _
    refine mem_iUnion.mpr ⟨u, ?_⟩
    simp only [hcovdef, mem_preimage, mem_ball]
    exact by simpa using (half_pos hcpos)
  obtain ⟨t, ht0, htmono, ⟨N, hN⟩, hspec⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval hcovopen hcovuniv
  set θ : ℕ → unitInterval := fun k => Classical.choose (hspec k) with hθdef
  have hθ : ∀ k, Set.Icc (t k) (t (k + 1)) ⊆ cov (θ k) :=
    fun k => Classical.choose_spec (hspec k)
  have hmem : ∀ k (s : unitInterval), s ∈ Set.Icc (t k) (t (k + 1)) →
      dist (((γ s : ↥U) : ℂ)) (((γ (θ k) : ↥U) : ℂ)) < c / 2 := by
    intro k s hs
    have h := hθ k hs
    simp only [hcovdef, mem_preimage, mem_ball] at h
    exact h
  have htk : ∀ k, t k ∈ Set.Icc (t k) (t (k + 1)) :=
    fun k => ⟨le_refl _, htmono (Nat.le_succ k)⟩
  have htk1 : ∀ k, t (k + 1) ∈ Set.Icc (t k) (t (k + 1)) :=
    fun k => ⟨htmono (Nat.le_succ k), le_refl _⟩
  have hosc : ∀ k (s : unitInterval), s ∈ Set.Icc (t k) (t (k + 1)) →
      dist (((γ s : ↥U) : ℂ)) (((γ (t k) : ↥U) : ℂ)) ≤ c := by
    intro k s hs
    have h1 := hmem k s hs
    have h2 := hmem k (t k) (htk k)
    have h3 : dist (((γ s : ↥U) : ℂ)) (((γ (t k) : ↥U) : ℂ))
        ≤ dist (((γ s : ↥U) : ℂ)) (((γ (θ k) : ↥U) : ℂ))
          + dist (((γ (θ k) : ↥U) : ℂ)) (((γ (t k) : ↥U) : ℂ)) := dist_triangle _ _ _
    rw [dist_comm (((γ (θ k) : ↥U) : ℂ))] at h3
    linarith
  have hgstep : ∀ k, dist (((γ (t k) : ↥U) : ℂ)) (((γ (t (k + 1)) : ↥U) : ℂ)) ≤ c := by
    intro k
    have h1 := hmem k (t k) (htk k)
    have h2 := hmem k (t (k + 1)) (htk1 k)
    have h3 : dist (((γ (t k) : ↥U) : ℂ)) (((γ (t (k + 1)) : ↥U) : ℂ))
        ≤ dist (((γ (t k) : ↥U) : ℂ)) (((γ (θ k) : ↥U) : ℂ))
          + dist (((γ (θ k) : ↥U) : ℂ)) (((γ (t (k + 1)) : ↥U) : ℂ)) := dist_triangle _ _ _
    rw [dist_comm (((γ (θ k) : ↥U) : ℂ))] at h3
    linarith
  -- ### the ladder anchors
  set lad : ℕ → ℤ × ℤ := fun k => snap (((γ (t k) : ↥U) : ℂ) / (c : ℂ)) with hladdef
  have hNt : t N = 1 := hN N le_rfl
  have hlad : ∀ k ≤ N, lad k
      = snap (((fun u : unitInterval => ((γ u : ↥U) : ℂ)) (t k)) / (c : ℂ)) :=
    fun _ _ => rfl
  have hsnap : ∀ k, ‖gpt (lad k) - (((γ (t k) : ↥U) : ℂ) / (c : ℂ))‖ ≤ 2 :=
    fun k => norm_gpt_snap_sub_le _
  have hgptdl : ∀ k, ‖gpt (dl lad k)‖ ≤ 5 := by
    intro k
    have h1 := hsnap (k + 1)
    have h0 := hsnap k
    have h2 : ‖(((γ (t (k + 1)) : ↥U) : ℂ) / (c : ℂ))
        - (((γ (t k) : ↥U) : ℂ) / (c : ℂ))‖ ≤ 1 := by
      have hsub : (((γ (t (k + 1)) : ↥U) : ℂ) / (c : ℂ))
          - (((γ (t k) : ↥U) : ℂ) / (c : ℂ))
          = ((((γ (t (k + 1)) : ↥U) : ℂ) - ((γ (t k) : ↥U) : ℂ))) / (c : ℂ) := by
        ring
      rw [hsub, norm_div, Complex.norm_real, Real.norm_of_nonneg (le_of_lt hcpos)]
      have hg := hgstep k
      rw [dist_eq_norm] at hg
      rw [div_le_one hcpos]
      rw [← norm_neg, neg_sub]
      exact hg
    have hdd : gpt (dl lad k) = gpt (lad (k + 1)) - gpt (lad k) := by
      simp only [dl]
      exact gpt_sub_eq _ _
    calc ‖gpt (dl lad k)‖
        = ‖(gpt (lad (k + 1)) - (((γ (t (k + 1)) : ↥U) : ℂ) / (c : ℂ)))
            + ((((γ (t (k + 1)) : ↥U) : ℂ) / (c : ℂ))
                - (((γ (t k) : ↥U) : ℂ) / (c : ℂ)))
            + ((((γ (t k) : ↥U) : ℂ) / (c : ℂ)) - gpt (lad k))‖ := by
          rw [hdd]; ring_nf
      _ ≤ ‖gpt (lad (k + 1)) - (((γ (t (k + 1)) : ↥U) : ℂ) / (c : ℂ))‖
            + ‖(((γ (t (k + 1)) : ↥U) : ℂ) / (c : ℂ))
                - (((γ (t k) : ↥U) : ℂ) / (c : ℂ))‖
            + ‖(((γ (t k) : ↥U) : ℂ) / (c : ℂ)) - gpt (lad k)‖ := by
          have ha := norm_add_le
            ((gpt (lad (k + 1)) - (((γ (t (k + 1)) : ↥U) : ℂ) / (c : ℂ)))
              + ((((γ (t (k + 1)) : ↥U) : ℂ) / (c : ℂ))
                  - (((γ (t k) : ↥U) : ℂ) / (c : ℂ))))
            ((((γ (t k) : ↥U) : ℂ) / (c : ℂ)) - gpt (lad k))
          have hb := norm_add_le
            (gpt (lad (k + 1)) - (((γ (t (k + 1)) : ↥U) : ℂ) / (c : ℂ)))
            ((((γ (t (k + 1)) : ↥U) : ℂ) / (c : ℂ))
              - (((γ (t k) : ↥U) : ℂ) / (c : ℂ)))
          linarith
      _ ≤ 5 := by
          rw [norm_sub_rev (((γ (t k) : ↥U) : ℂ) / (c : ℂ)) (gpt (lad k))]
          linarith
  have hq : ∀ k ≤ N, |(dl lad k).1| ≤ 6 ∧ |(dl lad k).2| ≤ 6 :=
    fun k _ => int_abs_le_of_norm_gpt_le (hgptdl k)
  have hp1 : ∀ k ≤ N, (dl lad k).1.natAbs % 2 = 0 := by
    intro k _
    simp only [dl, hladdef, Prod.fst_sub]
    exact natAbs_mod_two_sub (snap_fst_parity _) (snap_fst_parity _)
  have hp2 : ∀ k ≤ N, (dl lad k).2.natAbs % 2 = 0 := by
    intro k _
    simp only [dl, hladdef, Prod.snd_sub]
    exact natAbs_mod_two_sub (snap_snd_parity _) (snap_snd_parity _)
  have hclosed : lad N = lad 0 := by
    simp only [hladdef]
    congr 1
    rw [hNt, ht0, γ.target, γ.source]
  -- ### the ladder walk
  set W : LWalk := ladderWalk N c hcpos lad hq hp1 hp2 hclosed with hWdef
  have hWn : W.n = 12 * N := rfl
  have hval : ∀ s, W.path s ∈ U := by
    refine ladderWalk_trace (g := fun u : unitInterval => ((γ u : ↥U) : ℂ)) (t := t)
      (c := c) (δ := δ) hcpos hcδ ?_ (fun k _ => hgstep k) (fun k _ => hδU (t k))
      (hq := hq) (hp1 := hp1) (hp2 := hp2) (hclosed := hclosed)
    intro k _
    rfl
  have hbase : W.pt 0 ∈ U := W.pt_mem hval (Nat.zero_le _)
  -- ### the vertex family of the walk in `↥U`, and the spokes
  set VP : ℕ → ↥U := fun k => W.ptMin hval k with hVPdef
  set Bal : ℕ → Set ℂ := fun k => Metric.ball (((γ (t k) : ↥U) : ℂ)) δ with hBaldef
  have hBalconv : ∀ k, Convex ℝ (Bal k) := fun k => by rw [hBaldef]; exact convex_ball _ _
  have hBalU : ∀ k, Bal k ⊆ U := fun k => by rw [hBaldef]; exact hδU (t k)
  have hVP12 : ∀ k, k ≤ N → (((VP (12 * k) : ↥U) : ℂ)) = c * gpt (lad k) := by
    intro k hk
    rw [hVPdef, LWalk.ptMin_apply,
      Nat.min_eq_left (by rw [hWn]; exact Nat.mul_le_mul_left 12 hk), hWdef]
    show c * gpt (ladderV lad (12 * k)) = c * gpt (lad k)
    rw [ladderV, bo_twelve_mul, mac_zero, add_zero]
  have hVP0 : (((VP 0 : ↥U) : ℂ)) = c * gpt (lad 0) := by
    rw [hVPdef, LWalk.ptMin_apply, Nat.min_eq_left (Nat.zero_le _), hWdef]
    show c * gpt (ladderV lad 0) = c * gpt (lad 0)
    rw [ladderV, bo_zero, mac_zero, add_zero]
  have hVPB : ∀ k, k ≤ N → (((VP (12 * k) : ↥U) : ℂ)) ∈ Bal k := by
    intro k hk
    rw [hBaldef, Metric.mem_ball, dist_eq_norm, hVP12 k hk]
    have h := norm_pt_lad_le (g := fun u : unitInterval => ((γ u : ↥U) : ℂ)) (t := t)
      (k := k) hcpos (hlad k hk)
    linarith [h, hcδ]
  have hsegB : ∀ k, k ≤ N → ∀ u,
      Path.segment (((γ (t k) : ↥U) : ℂ)) (((VP (12 * k) : ↥U) : ℂ)) u ∈ Bal k := by
    intro k hk u
    exact (hBalconv k).segment_subset (mem_ball_self hδpos) (hVPB k hk)
      (by rw [← Path.range_segment]; exact ⟨u, rfl⟩)
  have hVP0B : (((VP 0 : ↥U) : ℂ)) ∈ Bal 0 := by
    rw [hBaldef, Metric.mem_ball, dist_eq_norm, hVP0]
    have h := norm_pt_lad_le (g := fun u : unitInterval => ((γ u : ↥U) : ℂ)) (t := t)
      (k := 0) hcpos (hlad 0 (Nat.zero_le N))
    linarith [h, hcδ]
  have hN1 : 1 ≤ N := by
    rcases Nat.eq_zero_or_pos N with h | h
    · exfalso
      have : t 0 = (1 : unitInterval) := by rw [← hNt, h]
      rw [ht0] at this
      exact zero_ne_one this
    · exact h
  have htkN : ∀ k, N ≤ k → t k = 1 := fun k hk =>
    le_antisymm (t k).2.2 (by rw [← hNt]; exact htmono hk)
  have hsegU : ∀ k, ∀ u,
      Path.segment (((γ (t k) : ↥U) : ℂ)) (((VP (12 * k) : ↥U) : ℂ)) u ∈ U := by
    intro k u
    by_cases hk : k ≤ N
    · exact hBalU k (hsegB k hk u)
    · have hkN : N ≤ k := le_of_lt (not_le.mp hk)
      have htk : t k = 1 := htkN k hkN
      have hγk : (((γ (t k) : ↥U) : ℂ)) = (((γ (t 0) : ↥U) : ℂ)) := by
        rw [htk, ht0, γ.target, γ.source]
      have hVPk : (((VP (12 * k) : ↥U) : ℂ)) = (((VP 0 : ↥U) : ℂ)) := by
        simp only [hVPdef]
        rw [LWalk.ptMin_apply, LWalk.ptMin_apply]
        have h1 : min (12 * k) W.n = W.n := by
          rw [hWn]; exact Nat.min_eq_right (Nat.mul_le_mul_left 12 hkN)
        have h2 : min 0 W.n = 0 := Nat.min_eq_left (Nat.zero_le _)
        rw [h1, h2, W.pt_last]
      rw [hγk, hVPk]
      exact hBalU 0 (by
        refine (hBalconv 0).segment_subset (mem_ball_self hδpos) hVP0B
          (by rw [← Path.range_segment]; exact ⟨u, rfl⟩))
  set sp : ∀ k, Path (γ (t k)) (VP (12 * k)) := fun k =>
    Path.liftU (γ (t k)).2 (VP (12 * k)).2
      (Path.segment (((γ (t k) : ↥U) : ℂ)) (((VP (12 * k) : ↥U) : ℂ))) (hsegU k)
    with hspdef
  have hspval : ∀ k u, ((sp k u : ↥U) : ℂ)
      = Path.segment (((γ (t k) : ↥U) : ℂ)) (((VP (12 * k) : ↥U) : ℂ)) u := by
    intro k u
    rw [hspdef]
    rfl
  have hspB : ∀ k, k ≤ N → ∀ u, ((sp k u : ↥U) : ℂ) ∈ Bal k := by
    intro k hk u
    rw [hspval k u]
    exact hsegB k hk u

  -- ### the vertices of the walk lie in the block balls
  have hWptBal : ∀ k, k < N → ∀ m, 12 * k ≤ m → m ≤ 12 * (k + 1) → W.pt m ∈ Bal k := by
    intro k hk m hm hm'
    rw [hBaldef, hWdef]
    exact ladderWalk_pt_mem_ball (g := fun u : unitInterval => ((γ u : ↥U) : ℂ)) (t := t)
      (c := c) (δ := δ) hcpos hcδ hlad (fun k _ => hgstep k) hk hm hm'
  -- ### the lifted edges and the block paths
  set F : ∀ k, Path (VP k) (VP (k + 1)) := fun k => W.edgeUNat hval k with hFdef
  have hFval : ∀ k, k < W.n → ∀ u, ((F k u : ↥U) : ℂ) = W.edge k u := by
    intro k hk u
    rw [hFdef, LWalk.edgeUNat_apply, dif_pos hk]
  set S : ∀ k, Path (VP (12 * k)) (VP (12 * k + 12)) :=
    fun k => joinNat (fun j => F (12 * k + j)) 12 with hSdef
  have hSval : ∀ k, k < N → ∀ u, ((S k u : ↥U) : ℂ) ∈ Bal k := by
    intro k hk u
    rw [hSdef]
    refine joinNat_mem_le (p := fun j => VP (12 * k + j)) (F := fun j => F (12 * k + j))
      (S := {z : ↥U | (z : ℂ) ∈ Bal k}) (n := 12) ?_ ?_ 12 le_rfl u
    · exact hVPB k (le_of_lt hk)
    · intro j hj v
      have hmN : 12 * k + j < W.n := by rw [hWn]; omega
      have hb0 : W.pt (12 * k + j) ∈ Bal k := hWptBal k hk _ (by omega) (by omega)
      have hb1 : W.pt (12 * k + j + 1) ∈ Bal k := hWptBal k hk _ (by omega) (by omega)
      show ((F (12 * k + j) v : ↥U) : ℂ) ∈ Bal k
      rw [hFval (12 * k + j) hmN v]
      exact (hBalconv k).segment_subset hb0 hb1 (segPath_mem_segment _ _ _ ⟨v, rfl⟩)
  have hspBk : ∀ k, k < N → ∀ u, ((sp (k + 1) u : ↥U) : ℂ) ∈ Bal k := by
    intro k hk u
    rw [hspval (k + 1) u, hBaldef]
    refine (hBalconv k).segment_subset ?_ ?_
      (by rw [← Path.range_segment]; exact ⟨u, rfl⟩)
    · rw [Metric.mem_ball, dist_eq_norm]
      have h := hosc k (t (k + 1)) (htk1 k)
      rw [dist_eq_norm] at h
      linarith [h, hcδ, hcpos]
    · rw [Metric.mem_ball, hVP12 (k + 1) (Nat.succ_le_of_lt hk)]
      have h1 := norm_pt_lad_le (g := fun u : unitInterval => ((γ u : ↥U) : ℂ)) (t := t)
        (k := k + 1) hcpos (hlad (k + 1) (Nat.succ_le_of_lt hk))
      have h2 := hosc k (t (k + 1)) (htk1 k)
      rw [dist_eq_norm] at h2
      have h3 : dist (c * gpt (lad (k + 1))) (((γ (t k) : ↥U) : ℂ)) ≤ 2 * c + c := by
        rw [dist_eq_norm]
        calc ‖c * gpt (lad (k + 1)) - (((γ (t k) : ↥U) : ℂ))‖
            = ‖(c * gpt (lad (k + 1)) - (((γ (t (k + 1)) : ↥U) : ℂ)))
                + ((((γ (t (k + 1)) : ↥U) : ℂ)) - (((γ (t k) : ↥U) : ℂ)))‖ := by ring_nf
          _ ≤ ‖c * gpt (lad (k + 1)) - (((γ (t (k + 1)) : ↥U) : ℂ))‖
                + ‖(((γ (t (k + 1)) : ↥U) : ℂ)) - (((γ (t k) : ↥U) : ℂ))‖ := norm_add_le _ _
          _ ≤ 2 * c + c := add_le_add h1 h2
      linarith [h3, hcδ, hcpos]
  have hspBk_sym : ∀ k, k < N → ∀ v, (((sp (k + 1)).symm v : ↥U) : ℂ) ∈ Bal k :=
    fun k hk v => hspBk k hk (unitInterval.symm v)
  set tp : ∀ k, Path (γ (t k)) (γ (t (k + 1))) :=
    fun k => (sp k).trans ((S k).trans ((sp (k + 1)).symm)) with htpdef
  -- ### the block comparison inside the convex ball
  have hthree : ∀ k, k < N → Path.Homotopic (γ.restr (t k) (t (k + 1))) (tp k) := by
    intro k hk
    refine homotopic_of_convex_subset (U := U) (B := Bal k) (hBalconv k)
      ⟨(((γ (t k) : ↥U) : ℂ)), mem_ball_self hδpos⟩ (hBalU k)
      (γ.restr (t k) (t (k + 1))) (tp k) ?_ ?_
    · intro u
      exact Path.restr_mem γ (htmono (Nat.le_succ k)) (S := {z : ↥U | (z : ℂ) ∈ Bal k})
        (fun s hs => by
          show ((γ s : ↥U) : ℂ) ∈ Bal k
          rw [hBaldef, Metric.mem_ball, dist_eq_norm]
          have h := hosc k s hs
          rw [dist_eq_norm] at h
          linarith [h, hcδ, hcpos]) u
    · intro u
      rw [htpdef, Path.trans_apply]
      split_ifs with h1
      · exact hspB k (le_of_lt hk) _
      · rw [Path.trans_apply]
        split_ifs with h2
        · exact hSval k hk _
        · exact hspBk_sym k hk _
  -- ### the join of the block paths
  set J : Path (VP 0) (VP (12 * N)) := joinNat S N with hJdef
  have hcum : ∀ k, cumSum (fun _ => 12) k = 12 * k := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [cumSum_succ, ih]; ring
  have hflat : Path.Homotopic (joinNat F (12 * N)) J := by
    have h := joinNat_block_decomp (p := VP) F N
    simp only [hJdef, hSdef] at h ⊢
    exact h
  -- ### the glued homotopy
  have hrestr : Path.Homotopic (γ.restr (t 0) (t N))
      (joinNat (fun k => γ.restr (t k) (t (k + 1))) N) :=
    homotopic_restr_joinNat γ t N
  have hjoin : Path.Homotopic (joinNat (fun k => γ.restr (t k) (t (k + 1))) N)
      (joinNat tp N) :=
    joinNat_congr_lt (p := fun k => γ (t k)) N (fun k hk => hthree k hk)
  have hconj : Path.Homotopic (joinNat tp N) ((sp 0).trans (J.trans ((sp N).symm))) := by
    have h := joinNat_conj (y := fun k => γ (t k)) (w := fun k => VP (12 * k)) sp S N
    simpa only [htpdef, hJdef] using h
  have hchain : Path.Homotopic (γ.restr (t 0) (t N))
      ((sp 0).trans (J.trans ((sp N).symm))) :=
    hrestr.trans (hjoin.trans hconj)
  -- ### the endpoint casts to the loop based at `x`
  have hγt0 : (((γ (t 0) : ↥U) : ℂ)) = x := by rw [ht0, γ.source]
  have hγtN : (((γ (t N) : ↥U) : ℂ)) = x := by rw [hNt, γ.target]
  have e1 : (⟨x, hx⟩ : ↥U) = γ (t 0) := γ.source.symm.trans (congrArg γ ht0.symm)
  have e2 : (⟨x, hx⟩ : ↥U) = γ (t N) := γ.target.symm.trans (congrArg γ hNt.symm)
  have heq : Path.cast (γ.restr (t 0) (t N)) e1 e2 = γ := by
    apply Path.ext
    funext u
    apply Subtype.ext
    rw [path_cast_apply, Path.restr_apply, ht0, hNt, affine_zero_one]
  have hmain : Path.Homotopic γ (Path.cast ((sp 0).trans (J.trans ((sp N).symm))) e1 e2) := by
    have h1 : Path.Homotopic (Path.cast (γ.restr (t 0) (t N)) e1 e2)
        (Path.cast ((sp 0).trans (J.trans ((sp N).symm))) e1 e2) :=
      Path.Homotopic.pathCast hchain e1 e2
    have h2 : Path.Homotopic γ (Path.cast (γ.restr (t 0) (t N)) e1 e2) := by
      rw [heq]
    exact h2.trans h1
  -- ### the spoke from `x` to the base point of the walk
  have hVP0val : (((VP 0 : ↥U) : ℂ)) = W.pt 0 := by
    rw [hVPdef, LWalk.ptMin_apply, Nat.min_eq_left (Nat.zero_le _)]
  have hVPNval : (((VP (12 * N) : ↥U) : ℂ)) = W.pt 0 := by
    rw [hVPdef, LWalk.ptMin_apply, hWn, Nat.min_self, ← hWn, W.pt_last]
  have hQ0 : (⟨W.pt 0, hbase⟩ : ↥U) = VP 0 := Subtype.ext hVP0val.symm
  have hJN : (⟨W.pt 0, hbase⟩ : ↥U) = VP (12 * N) := Subtype.ext hVPNval.symm
  have ha_val : ∀ u, Path.segment x (W.pt 0) u ∈ U := by
    intro u
    refine hBalU 0 ((hBalconv 0).segment_subset ?_ ?_
      (by rw [← Path.range_segment]; exact ⟨u, rfl⟩))
    · rw [hBaldef, Metric.mem_ball, hγt0, dist_self]
      exact hδpos
    · rw [hBaldef, Metric.mem_ball, ← hVP0val]
      exact hVP0B
  set a : Path (⟨x, hx⟩ : ↥U) (⟨W.pt 0, hbase⟩ : ↥U) :=
    Path.liftU hx hbase (Path.segment x (W.pt 0)) ha_val with hadde
  -- ### the three homotopies of the pieces
  have hA : Path.Homotopic (Path.cast (sp 0) e1 hQ0) a := by
    have h : Path.cast (sp 0) e1 hQ0 = a := by
      apply Path.ext
      funext u
      apply Subtype.ext
      show Path.segment (((γ (t 0) : ↥U) : ℂ)) (((VP 0 : ↥U) : ℂ)) u
        = Path.segment x (W.pt 0) u
      rw [hγt0, hVP0val]
    rw [h]
  have hB : Path.Homotopic (Path.cast (sp N) e2 hJN) a := by
    have h : Path.cast (sp N) e2 hJN = a := by
      apply Path.ext
      funext u
      apply Subtype.ext
      show Path.segment (((γ (t N) : ↥U) : ℂ)) (((VP (12 * N) : ↥U) : ℂ)) u
        = Path.segment x (W.pt 0) u
      rw [hγtN, hVPNval]
    rw [h]
  have hloop : Path.Homotopic (Path.cast (joinNat F (12 * N)) hQ0 hJN)
      (W.loopIn hbase hval) := by
    have h : Path.cast (joinNat F (12 * N)) hQ0 hJN = W.loopIn hbase hval := by
      apply Path.ext
      funext u
      apply Subtype.ext
      show ((joinNat F (12 * N)) u : ℂ) = W.path u
      exact joinNat_coe_lt (p := VP) (q := W.pt) (N := W.n)
        (fun k hk => ptMin_val_of_le W hval hk) F (fun k => W.edge k)
        (fun k hk u => hFval k hk u) W.n le_rfl u
    rw [h]
  have hJ : Path.Homotopic (Path.cast J hQ0 hJN) (W.loopIn hbase hval) := by
    have h1 : Path.Homotopic (Path.cast (joinNat F (12 * N)) hQ0 hJN)
        (Path.cast J hQ0 hJN) := by
      have h := Path.Homotopic.pathCast hflat hQ0 hJN
      simpa only [hJdef] using h
    exact h1.symm.trans hloop
  -- ### the cast decomposition
  have hcast : Path.cast ((sp 0).trans (J.trans ((sp N).symm))) e1 e2
      = (Path.cast (sp 0) e1 hQ0).trans
          ((Path.cast J hQ0 hJN).trans ((Path.cast (sp N) e2 hJN).symm)) := by
    rw [Path.cast_trans (sp 0) (J.trans ((sp N).symm)) e1 hQ0 e2,
      Path.cast_trans J ((sp N).symm) hQ0 hJN e2,
      Path.cast_symm (sp N) e2 hJN]
  have hfinal : Path.Homotopic (Path.cast ((sp 0).trans (J.trans ((sp N).symm))) e1 e2)
      (a.trans ((W.loopIn hbase hval).trans a.symm)) := by
    rw [hcast]
    exact Path.Homotopic.hcomp hA (Path.Homotopic.hcomp hJ (Path.Homotopic.symm₂ hB))
  exact ⟨W, hbase, hval, a, hmain.trans hfinal⟩

end

end Work.Smooth.JordanSeparation
