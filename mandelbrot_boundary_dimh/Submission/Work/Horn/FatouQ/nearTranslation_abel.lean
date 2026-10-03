import Mathlib
import Submission.Work.FatouCoord.Exist.exists_eq_of_deriv_close
import Submission.Work.Horn.FatouQ.exists_strip_preimage_of_deriv_close
import Submission.Work.Horn.FatouQ.norm_deriv_le_of_re_majorant
import Submission.Work.Horn.FatouQ.tsum_rpow_halfstep_bound

namespace Work.Horn.FatouQ

open scoped Topology NNReal

theorem nearTranslation_abel
    {N : ℝ} {g X E : ℂ → ℂ} {B θ C0 C1 δ : ℝ}
    (hN : 0 < N) (hδ : 1 < δ) (hB : 0 ≤ B) (hθ : θ < 1) (hC0 : 0 ≤ C0) (hC1 : 0 ≤ C1)
    (hgdiff : DifferentiableOn ℂ g {w : ℂ | N < w.re})
    (hgstep : ∀ w : ℂ, N < w.re → w.re + 1 / 2 ≤ (g w).re)
    (hginj : Set.InjOn g {w : ℂ | N < w.re})
    (hXdiff : DifferentiableOn ℂ X {w : ℂ | N < w.re})
    (hXderiv : ∀ w : ℂ, N < w.re → ‖deriv X w - 1‖ ≤ 1 / 4)
    (hXclose : ∀ w : ℂ, N < w.re → ‖X w - w‖ ≤ C0 * ‖w‖ ^ θ + C1)
    (hEdiff : DifferentiableOn ℂ E {w : ℂ | N < w.re})
    (hEabel : ∀ w : ℂ, N < w.re → E w = X (g w) - X w - 1)
    (hEbound : ∀ w : ℂ, N < w.re → ‖E w‖ ≤ B / w.re ^ δ) :
    ∃ (N' : ℝ) (φ : ℂ → ℂ), N ≤ N' ∧
      DifferentiableOn ℂ φ {w : ℂ | N' < w.re} ∧
      (∀ w : ℂ, N' < w.re → φ (g w) = φ w + 1) ∧
      Set.InjOn φ {w : ℂ | N' < w.re} ∧
      (∀ b : ℝ, ∃ C : ℝ, ∀ τ : ℂ, C < τ.re → |τ.im| ≤ b →
        ∃ w : ℂ, N' < w.re ∧ φ w = τ) := by
  have hδpos : (0:ℝ) < δ := by linarith
  have hUopen : IsOpen {w : ℂ | N < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have hgmaps : Set.MapsTo g {w : ℂ | N < w.re} {w : ℂ | N < w.re} := by
    intro w hw
    exact show N < (g w).re from by
      have hw' : N < w.re := hw
      linarith [hgstep w hw']
  have hgiter_re : ∀ n : ℕ, ∀ w : ℂ, N < w.re → w.re + (n : ℝ) / 2 ≤ (g^[n] w).re := by
    intro n
    induction n with
    | zero => intro w hw; simp
    | succ n ih =>
      intro w hw
      rw [Function.iterate_succ_apply']
      have hstepn : N < (g^[n] w).re := by
        have := ih w hw
        have hnn : (0:ℝ) ≤ (n:ℝ)/2 := by positivity
        linarith
      have h1 := hgstep (g^[n] w) hstepn
      have h2 := ih w hw
      have hcast : ((n:ℝ) + 1)/2 = (n:ℝ)/2 + 1/2 := by ring
      have : w.re + ((n:ℝ)+1)/2 ≤ (g (g^[n] w)).re := by
        rw [hcast]; linarith
      simpa [Nat.cast_add, Nat.cast_one] using this
  -- summable majorant for the Abel series
  obtain ⟨hu, R0, hR0N, hR0bound⟩ := tsum_rpow_halfstep_bound (B := B) (δ := δ) (N := N) hB hδ hN
  -- each summand is holomorphic
  have hsummand : ∀ i : ℕ, DifferentiableOn ℂ (fun w : ℂ => E (g^[i] w)) {w : ℂ | N < w.re} := by
    intro i
    exact hEdiff.comp ((hgdiff.iterate hgmaps) i) (hgmaps.iterate i)
  -- pointwise decay of the summands
  have hE_step : ∀ (v : ℂ) (i : ℕ), N < v.re → ‖E (g^[i] v)‖ ≤ B / (v.re + (i:ℝ)/2)^δ := by
    intro v i hv
    have hgi_re : v.re + (i:ℝ)/2 ≤ (g^[i] v).re := hgiter_re i v hv
    have hgi : N < (g^[i] v).re := by
      have hnn : (0:ℝ) ≤ (i:ℝ)/2 := by positivity
      linarith
    have hpos1 : 0 < v.re + (i:ℝ)/2 := by
      have hnn : (0:ℝ) ≤ (i:ℝ)/2 := by positivity
      linarith
    have hpow : (v.re + (i:ℝ)/2) ^ δ ≤ ((g^[i] v).re) ^ δ :=
      Real.rpow_le_rpow (le_of_lt hpos1) hgi_re (le_of_lt hδpos)
    calc ‖E (g^[i] v)‖ ≤ B / ((g^[i] v).re) ^ δ := hEbound (g^[i] v) hgi
      _ ≤ B / (v.re + (i:ℝ)/2) ^ δ :=
          div_le_div_of_nonneg_left hB (Real.rpow_pos_of_pos hpos1 δ) hpow
  have hbound_summand : ∀ (i : ℕ) (w : ℂ), w ∈ {w : ℂ | N < w.re} →
      ‖E (g^[i] w)‖ ≤ B / (N + (i:ℝ)/2)^δ := by
    intro i w hw
    have hwN : N < w.re := hw
    have h1 := hE_step w i hwN
    have hpos1 : 0 < N + (i:ℝ)/2 := by
      have hnn : (0:ℝ) ≤ (i:ℝ)/2 := by positivity
      linarith
    have hbase : N + (i:ℝ)/2 ≤ w.re + (i:ℝ)/2 := by linarith
    have hpow : (N + (i:ℝ)/2) ^ δ ≤ (w.re + (i:ℝ)/2) ^ δ :=
      Real.rpow_le_rpow (le_of_lt hpos1) hbase (le_of_lt hδpos)
    calc ‖E (g^[i] w)‖ ≤ B / (w.re + (i:ℝ)/2) ^ δ := h1
      _ ≤ B / (N + (i:ℝ)/2) ^ δ :=
          div_le_div_of_nonneg_left hB (Real.rpow_pos_of_pos hpos1 δ) hpow
  -- the Abel correction function
  set h : ℂ → ℂ := fun w => ∑' i : ℕ, E (g^[i] w) with hhdef
  have hhdiff : DifferentiableOn ℂ h {w : ℂ | N < w.re} := by
    change DifferentiableOn ℂ (fun w : ℂ => ∑' i : ℕ, E (g^[i] w)) {w : ℂ | N < w.re}
    exact Complex.differentiableOn_tsum_of_summable_norm (F := fun i w => E (g^[i] w))
      hu hsummand hUopen hbound_summand
  -- summability at each point of the half plane
  have hsumm_E : ∀ w : ℂ, N < w.re → Summable (fun i : ℕ => E (g^[i] w)) := by
    intro w hw
    refine Summable.of_norm_bounded (g := fun i : ℕ => B / (w.re + (i:ℝ)/2)^δ) ?_ ?_
    · exact Summable.of_nonneg_of_le (f := fun i : ℕ => B / (N + (i:ℝ)/2)^δ)
        (fun i => div_nonneg hB (le_of_lt (Real.rpow_pos_of_pos (by
          have hnn : (0:ℝ) ≤ (i:ℝ)/2 := by positivity
          linarith) δ)))
        (fun i => by
          have hpos1 : 0 < N + (i:ℝ)/2 := by
            have hnn : (0:ℝ) ≤ (i:ℝ)/2 := by positivity
            linarith
          have hbase : N + (i:ℝ)/2 ≤ w.re + (i:ℝ)/2 := by linarith
          have hpow : (N + (i:ℝ)/2) ^ δ ≤ (w.re + (i:ℝ)/2) ^ δ :=
            Real.rpow_le_rpow (le_of_lt hpos1) hbase (le_of_lt hδpos)
          exact div_le_div_of_nonneg_left hB (Real.rpow_pos_of_pos hpos1 δ) hpow)
        hu
    · exact fun i => hE_step w i hw
  -- the majorant V and its monotonicity
  set V : ℝ → ℝ := fun y => ∑' i : ℕ, B / (y + (i:ℝ)/2)^δ with hVdef
  have hVsum : ∀ y : ℝ, N ≤ y → Summable (fun i : ℕ => B / (y + (i:ℝ)/2)^δ) := by
    intro y hy
    exact Summable.of_nonneg_of_le (f := fun i : ℕ => B / (N + (i:ℝ)/2)^δ)
      (fun i => div_nonneg hB (le_of_lt (Real.rpow_pos_of_pos (by
        have hnn : (0:ℝ) ≤ (i:ℝ)/2 := by positivity
        linarith) δ)))
      (fun i => by
        have hpos1 : 0 < N + (i:ℝ)/2 := by
          have hnn : (0:ℝ) ≤ (i:ℝ)/2 := by positivity
          linarith
        have hbase : N + (i:ℝ)/2 ≤ y + (i:ℝ)/2 := by linarith
        have hpow : (N + (i:ℝ)/2) ^ δ ≤ (y + (i:ℝ)/2) ^ δ :=
          Real.rpow_le_rpow (le_of_lt hpos1) hbase (le_of_lt hδpos)
        exact div_le_div_of_nonneg_left hB (Real.rpow_pos_of_pos hpos1 δ) hpow)
      hu
  have hVle : ∀ w : ℂ, N < w.re → ‖h w‖ ≤ V w.re := by
    intro w hw
    change ‖∑' i : ℕ, E (g^[i] w)‖ ≤ ∑' i : ℕ, B / (w.re + (i:ℝ)/2)^δ
    have hsum_norm : Summable (fun i : ℕ => ‖E (g^[i] w)‖) :=
      Summable.of_nonneg_of_le (fun i => norm_nonneg _) (fun i => hE_step w i hw)
        (hVsum w.re (le_of_lt hw))
    calc ‖∑' i : ℕ, E (g^[i] w)‖ ≤ ∑' i : ℕ, ‖E (g^[i] w)‖ :=
          norm_tsum_le_tsum_norm hsum_norm
      _ ≤ ∑' i : ℕ, B / (w.re + (i:ℝ)/2)^δ :=
          Summable.tsum_le_tsum (fun i => hE_step w i hw) hsum_norm (hVsum w.re (le_of_lt hw))
  have hVantitone : ∀ x y : ℝ, N ≤ x → x ≤ y → V y ≤ V x := by
    intro x y hx hxy
    change (∑' i : ℕ, B / (y + (i:ℝ)/2)^δ) ≤ ∑' i : ℕ, B / (x + (i:ℝ)/2)^δ
    refine Summable.tsum_le_tsum (fun i => ?_) (hVsum y (le_trans hx hxy)) (hVsum x hx)
    have hpos1 : 0 < x + (i:ℝ)/2 := by
      have hnn : (0:ℝ) ≤ (i:ℝ)/2 := by positivity
      linarith
    have hbase : x + (i:ℝ)/2 ≤ y + (i:ℝ)/2 := by linarith
    have hpow : (x + (i:ℝ)/2) ^ δ ≤ (y + (i:ℝ)/2) ^ δ :=
      Real.rpow_le_rpow (le_of_lt hpos1) hbase (le_of_lt hδpos)
    exact div_le_div_of_nonneg_left hB (Real.rpow_pos_of_pos hpos1 δ) hpow
  have hVnn : ∀ x : ℝ, N ≤ x → 0 ≤ V x := by
    intro x hx
    change 0 ≤ ∑' i : ℕ, B / (x + (i:ℝ)/2)^δ
    exact tsum_nonneg (fun i => div_nonneg hB (le_of_lt (Real.rpow_pos_of_pos (by
      have hnn : (0:ℝ) ≤ (i:ℝ)/2 := by positivity
      linarith) δ)))
  -- the Abel coordinate
  set φ : ℂ → ℂ := X + h with hφdef
  have hphi_apply : ∀ z : ℂ, φ z = X z + h z := by intro z; rw [hφdef]; rfl
  have habel : ∀ w : ℂ, N < w.re → φ (g w) = φ w + 1 := by
    intro w hw
    have hshift : h (g w) = h w - E w := by
      change (∑' i : ℕ, E (g^[i] (g w))) = (∑' i : ℕ, E (g^[i] w)) - E w
      have hgt : (∑' i : ℕ, E (g^[i] (g w))) = ∑' i : ℕ, E (g^[i+1] w) :=
        tsum_congr (fun i => by rw [Function.iterate_succ_apply])
      rw [hgt]
      have hA := Summable.sum_add_tsum_nat_add (f := fun i : ℕ => E (g^[i] w)) 1 (hsumm_E w hw)
      simp only [Finset.sum_range_one, Function.iterate_zero_apply] at hA
      linear_combination hA
    have hXg : X (g w) = X w + 1 + E w := by rw [hEabel w hw]; ring
    rw [hphi_apply (g w), hphi_apply w, hshift, hXg]
    ring
  have habel_iter : ∀ (n : ℕ) (w : ℂ), N < w.re → φ (g^[n] w) = φ w + n := by
    intro n
    induction n with
    | zero => intro w hw; simp
    | succ n ih =>
      intro w hw
      rw [Function.iterate_succ_apply']
      have hgn : N < (g^[n] w).re := by
        have h1 := hgiter_re n w hw
        have hnn : (0:ℝ) ≤ (n:ℝ)/2 := by positivity
        linarith
      rw [habel (g^[n] w) hgn, ih w hw]
      push_cast
      ring
  -- the region where the derivative of `h` is small
  set Rstar : ℝ := max (R0 + 1) (N + 1) with hRstardef
  have hRstar_gt_N : N < Rstar := by
    rw [hRstardef]
    have h := le_max_right (R0 + 1) (N + 1)
    linarith
  have hRstar_pos : 0 < Rstar := lt_trans hN hRstar_gt_N
  have hRstar_ge : R0 + 1 ≤ Rstar := le_max_left _ _
  have hRstar_ge' : N + 1 ≤ Rstar := le_max_right _ _
  have hderiv_small : ∀ w : ℂ, Rstar < w.re → ‖deriv h w‖ ≤ 1 / 4 := by
    intro w hw
    have hwN1 : N + 1 < w.re := lt_of_le_of_lt hRstar_ge' hw
    have hR0le : R0 ≤ w.re - 1 := by have := lt_of_le_of_lt hRstar_ge hw; linarith
    have h1 : ‖deriv h w‖ ≤ V (w.re - 1) :=
      norm_deriv_le_of_re_majorant hhdiff hVantitone hVnn hVle hwN1
    have h2 : V (w.re - 1) ≤ 1 / 4 := by
      change (∑' i : ℕ, B / ((w.re - 1) + (i:ℝ)/2)^δ) ≤ 1 / 4
      exact hR0bound (w.re - 1) hR0le
    linarith
  have hφdiffU : DifferentiableOn ℂ φ {w : ℂ | N < w.re} := by
    rw [hφdef]
    exact hXdiff.add hhdiff
  have hφderiv_far : ∀ w : ℂ, Rstar < w.re → ‖deriv φ w - 1‖ ≤ 1 / 2 := by
    intro w hw
    have hwN : N < w.re := lt_of_lt_of_le hRstar_gt_N (le_of_lt hw)
    have hXat : DifferentiableAt ℂ X w := (hXdiff w hwN).differentiableAt (hUopen.mem_nhds hwN)
    have hhat : DifferentiableAt ℂ h w := (hhdiff w hwN).differentiableAt (hUopen.mem_nhds hwN)
    have hder : deriv φ w = deriv X w + deriv h w := by
      rw [hφdef]
      exact deriv_add hXat hhat
    rw [hder]
    have h1 : ‖deriv X w - 1‖ ≤ 1 / 4 := hXderiv w hwN
    have h2 : ‖deriv h w‖ ≤ 1 / 4 := hderiv_small w hw
    calc ‖deriv X w + deriv h w - 1‖ = ‖(deriv X w - 1) + deriv h w‖ := by
          rw [show deriv X w + deriv h w - 1 = (deriv X w - 1) + deriv h w from by ring]
      _ ≤ ‖deriv X w - 1‖ + ‖deriv h w‖ := norm_add_le _ _
      _ ≤ 1 / 4 + 1 / 4 := add_le_add h1 h2
      _ = 1 / 2 := by norm_num
  have hcloseStrip : ∀ w : ℂ, Rstar < w.re → ‖φ w - w‖ ≤ C0 * ‖w‖ ^ θ + (C1 + V N) := by
    intro w hw
    have hwN : N < w.re := lt_of_lt_of_le hRstar_gt_N (le_of_lt hw)
    have hXb := hXclose w hwN
    have hhb : ‖h w‖ ≤ V N :=
      le_trans (hVle w hwN) (hVantitone N w.re le_rfl (le_of_lt hwN))
    rw [hphi_apply w]
    calc ‖X w + h w - w‖ = ‖(X w - w) + h w‖ := by
          rw [show X w + h w - w = (X w - w) + h w from by ring]
      _ ≤ ‖X w - w‖ + ‖h w‖ := norm_add_le _ _
      _ ≤ (C0 * ‖w‖ ^ θ + C1) + V N := add_le_add hXb hhb
      _ = C0 * ‖w‖ ^ θ + (C1 + V N) := by ring
  have hφdiffRstar : DifferentiableOn ℂ φ {w : ℂ | Rstar < w.re} :=
    hφdiffU.mono (fun w hw => lt_of_lt_of_le hRstar_gt_N (le_of_lt hw))
  -- injectivity in the far right half plane
  have hSconv : Convex ℝ {w : ℂ | Rstar < w.re} := by
    have hset : {w : ℂ | Rstar < w.re} = Complex.reLm ⁻¹' (Set.Ioi Rstar) := by
      ext w; simp [Complex.reLm]
    rw [hset]
    exact (convex_Ioi Rstar).linear_preimage Complex.reLm
  have hHdiff : ∀ x ∈ {w : ℂ | Rstar < w.re},
      DifferentiableAt ℂ (fun w : ℂ => φ w - w) x := by
    intro x hx
    have hxN : N < x.re := lt_of_lt_of_le hRstar_gt_N (le_of_lt hx)
    exact ((hφdiffU x hxN).differentiableAt (hUopen.mem_nhds hxN)).sub differentiableAt_id
  have hHbound : ∀ x ∈ {w : ℂ | Rstar < w.re},
      ‖deriv (fun w : ℂ => φ w - w) x‖₊ ≤ (1 / 2 : ℝ≥0) := by
    intro x hx
    have hxN : N < x.re := lt_of_lt_of_le hRstar_gt_N (le_of_lt hx)
    have hxR : Rstar < x.re := hx
    have hphi_at : DifferentiableAt ℂ φ x := (hφdiffU x hxN).differentiableAt (hUopen.mem_nhds hxN)
    change ‖deriv (φ - id) x‖₊ ≤ (1 / 2 : ℝ≥0)
    rw [deriv_sub hphi_at differentiableAt_id, deriv_id]
    have h1 : ‖deriv φ x - 1‖ ≤ 1 / 2 := hφderiv_far x hxR
    exact_mod_cast h1
  have hlip := hSconv.lipschitzOnWith_of_nnnorm_deriv_le hHdiff hHbound
  have hinjS : Set.InjOn φ {w : ℂ | Rstar < w.re} := by
    intro a ha b hb hab
    have h1 : dist ((fun w : ℂ => φ w - w) a) ((fun w : ℂ => φ w - w) b)
        ≤ (1 / 2 : ℝ) * dist a b := by
      simpa using hlip.dist_le_mul a ha b hb
    have h2 : dist ((fun w : ℂ => φ w - w) a) ((fun w : ℂ => φ w - w) b) = dist a b := by
      rw [dist_eq_norm, dist_eq_norm]
      have hsub : (φ a - a) - (φ b - b) = b - a := by rw [hab]; ring
      rw [hsub, norm_sub_rev]
    have h3 : dist a b ≤ (1 / 2 : ℝ) * dist a b := by
      calc dist a b = dist ((fun w : ℂ => φ w - w) a) ((fun w : ℂ => φ w - w) b) := h2.symm
        _ ≤ 1 / 2 * dist a b := h1
    have h4 : dist a b = 0 := by linarith [dist_nonneg (x := a) (y := b), h3]
    exact dist_eq_zero.mp h4
  -- injectivity on the whole half plane, by pushing orbits to the right
  have hinjU : Set.InjOn φ {w : ℂ | N < w.re} := by
    intro a ha b hb hab
    obtain ⟨n, hn⟩ := exists_nat_gt (2 * (Rstar - min a.re b.re))
    have hn2 : Rstar < (n : ℝ) / 2 + min a.re b.re := by have := hn; linarith
    have hia : Rstar < (g^[n] a).re := by
      have h1 := hgiter_re n a ha
      have h2 : min a.re b.re ≤ a.re := min_le_left _ _
      linarith
    have hib : Rstar < (g^[n] b).re := by
      have h1 := hgiter_re n b hb
      have h2 : min a.re b.re ≤ b.re := min_le_right _ _
      linarith
    have hab' : φ (g^[n] a) = φ (g^[n] b) := by
      rw [habel_iter n a ha, habel_iter n b hb, hab]
    exact (hginj.iterate hgmaps n) ha hb (hinjS hia hib hab')
  -- surjectivity onto vertical strips
  have hsurj : ∀ b : ℝ, ∃ C : ℝ, ∀ τ : ℂ, C < τ.re → |τ.im| ≤ b →
      ∃ w : ℂ, N < w.re ∧ φ w = τ := by
    intro b
    obtain ⟨C, hC⟩ := exists_strip_preimage_of_deriv_close (φ := φ) (R := Rstar) (θ := θ)
      (C0 := C0) (C1 := C1 + V N) hRstar_pos hθ hC0 (add_nonneg hC1 (hVnn N le_rfl))
      hφdiffRstar hφderiv_far hcloseStrip b
    refine ⟨C, fun τ hτ hτim => ?_⟩
    obtain ⟨w, hw, hφw⟩ := hC τ hτ hτim
    exact ⟨w, lt_of_lt_of_le hRstar_gt_N (le_of_lt hw), hφw⟩
  exact ⟨N, φ, le_refl N, hφdiffU, habel, hinjU, hsurj⟩

end Work.Horn.FatouQ
