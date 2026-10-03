import Mathlib
import Submission.Work.Interfaces.Basic
import Submission.Work.Dim.Setup
import Submission.Work.Dim.Packing.packing
import Submission.Work.Dim.Pieces.disjoint
import Submission.Work.Dim.Branch.derivBound
import Submission.Work.Dim.Coding.map
import Submission.Work.Dim.Code.measure

/-!
# Moran cover and Frostman bound for a conformal IFS (area DIM)

This file assembles the dimension lower bound `log N / log K ≤ dimH (codingPt τ p '' cylinder l)`
for a conformal IFS `IsConformalIFS N τ p r K`.

Main ingredients:
* the "Moran antichain" `antichain τ p r σ`: minimal words `w` with `asize τ p w * r ≤ σ`;
* the packing lemma `Work.Dim.Packing.packing`;
* the Koebe-type estimates (`Work.Dim.Koebe.ballBounds`) and the contraction
  (`Work.Dim.Branch.derivBound`), used in `dim_main`.
-/

open MandelDim
open scoped Topology ENNReal
open Set Metric Filter MeasureTheory

noncomputable section

namespace Work.Dim

variable {N : ℕ}

/-- The Moran antichain at scale `σ`: words whose piece-size `asize τ p w * r` is at most `σ`,
minimal with this property. -/
def antichain (τ : Fin N → ℂ → ℂ) (p : ℂ) (r σ : ℝ) : Set (List (Fin N)) :=
  {w | asize τ p w * r ≤ σ ∧ ∀ v : List (Fin N), v <+: w → v ≠ w → σ < asize τ p v * r}

theorem asize_nil (τ : Fin N → ℂ → ℂ) (p : ℂ) : asize τ p ([] : List (Fin N)) = 1 := by
  simp [asize, ifsComp]

/-- Every code has a prefix in the antichain, provided `σ < r`. -/
theorem exists_antichain_of_lt {τ : Fin N → ℂ → ℂ} {p : ℂ} {r θ σ : ℝ}
    (hr : 0 < r) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (hdiff : ∀ i, DifferentiableOn ℂ (τ i) (ball p r))
    (hmaps : ∀ i, MapsTo (τ i) (ball p r) (ball p (r / 2)))
    (hderiv : ∀ i, ∀ z ∈ closedBall p (r / 2), ‖deriv (τ i) z‖ ≤ θ)
    (hσ : 0 < σ) (hσr : σ < r) (ω : ℕ → Fin N) :
    ∃ w ∈ antichain τ p r σ, ω ∈ MandelDim.cylinder w := by
  have hp : p ∈ closedBall p (r / 2) := by rw [mem_closedBall, dist_self]; linarith
  have hub : ∀ k, asize τ p (pref ω k) ≤ θ ^ k := by
    intro k
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      simp [asize, pref, ifsComp]
    · have h := norm_deriv_ifsComp_le hr hdiff hmaps hderiv (pref ω k)
        (by simp [pref, Nat.pos_iff_ne_zero.mp hk]) p hp
      simpa [asize] using h
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (show (0 : ℝ) < σ / r by positivity) hθ1
  have hn2 : θ ^ n * r < σ := by
    have := mul_lt_mul_of_pos_right hn hr
    rwa [div_mul_cancel₀ σ hr.ne'] at this
  have hex : ∃ k, asize τ p (pref ω k) * r ≤ σ :=
    ⟨n, le_of_lt (lt_of_le_of_lt (mul_le_mul_of_nonneg_right (hub n) hr.le) hn2)⟩
  set k := Nat.find hex with hkdef
  have hspec : asize τ p (pref ω k) * r ≤ σ := by
    rw [hkdef]; exact Nat.find_spec hex
  refine ⟨pref ω k, ⟨hspec, ?_⟩, mem_cylinder_pref ω k⟩
  intro v hv hne
  have hlen : v.length ≤ k := by
    have h := List.IsPrefix.length_le hv
    simpa [pref] using h
  have hvk : v.length < k := by
    rcases lt_or_eq_of_le hlen with h | h
    · exact h
    · exfalso
      exact hne (by rw [eq_pref_of_isPrefix ω k hv, h])
  have hveq : v = pref ω v.length := eq_pref_of_isPrefix ω k hv
  rw [hveq]
  exact not_le.mp (Nat.find_min hex hvk)

/-- Two distinct elements of the antichain are prefix-incomparable. -/
theorem antichain_not_prefix {τ : Fin N → ℂ → ℂ} {p : ℂ} {r σ : ℝ} {w w' : List (Fin N)}
    (hw : w ∈ antichain τ p r σ) (hw' : w' ∈ antichain τ p r σ) (hne : w ≠ w') :
    ¬ w <+: w' ∧ ¬ w' <+: w :=
  ⟨fun h => absurd (hw'.2 w h hne) (not_lt.mpr hw.1),
   fun h => absurd (hw.2 w' h (Ne.symm hne)) (not_lt.mpr hw'.1)⟩

/-- For an element `w ≠ []` of the antichain, define its "parent" `u = w.dropLast`; then
`u` is a proper prefix of `w` and hence already has size at least `σ`. -/
theorem antichain_parent {τ : Fin N → ℂ → ℂ} {p : ℂ} {r σ : ℝ} {w : List (Fin N)}
    (hw : w ∈ antichain τ p r σ) (hne : w ≠ []) :
    w.dropLast <+: w ∧ w.dropLast ≠ w ∧ σ < asize τ p w.dropLast * r := by
  have hw_eq : w.dropLast ++ [w.getLast hne] = w := List.dropLast_append_getLast hne
  refine ⟨⟨[w.getLast hne], hw_eq⟩, ?_, hw.2 _ ⟨[w.getLast hne], hw_eq⟩ ?_⟩
  · intro h
    have h2 := congrArg List.length (List.dropLast_append_getLast hne)
    rw [h] at h2
    simp only [List.length_append, List.length_cons, List.length_nil] at h2
    omega
  · intro h
    have h2 := congrArg List.length (List.dropLast_append_getLast hne)
    rw [h] at h2
    simp only [List.length_append, List.length_cons, List.length_nil] at h2
    omega

/-! ### Geometric estimates -/

/-- If two closed balls are disjoint then the distance of their centres is at least the sum of
their radii. -/
theorem le_dist_of_disjoint_closedBall {c c' : ℂ} {ρ ρ' : ℝ} (hρ : 0 ≤ ρ) (hρ' : 0 ≤ ρ')
    (h : Disjoint (closedBall c ρ) (closedBall c' ρ')) : ρ + ρ' ≤ dist c c' := by
  by_contra hlt
  rw [not_le] at hlt
  have hsum : 0 < ρ + ρ' := lt_of_le_of_lt dist_nonneg hlt
  set t : ℝ := ρ / (ρ + ρ') with htdef
  have ht0 : 0 ≤ t := div_nonneg hρ hsum.le
  have ht1 : t * (ρ + ρ') = ρ := div_mul_cancel₀ ρ hsum.ne'
  have htle1 : t ≤ 1 := by
    rw [htdef, div_le_one hsum]
    linarith
  have ht1' : (1 - t) * (ρ + ρ') = ρ' := by
    rw [sub_mul, one_mul, ht1]
    ring
  have hmem1 : AffineMap.lineMap c c' t ∈ closedBall c ρ := by
    rw [mem_closedBall, dist_lineMap_left, Real.norm_of_nonneg ht0]
    calc t * dist c c' ≤ t * (ρ + ρ') := mul_le_mul_of_nonneg_left hlt.le ht0
      _ = ρ := ht1
  have hmem2 : AffineMap.lineMap c c' t ∈ closedBall c' ρ' := by
    rw [mem_closedBall, dist_lineMap_right, Real.norm_of_nonneg (by linarith : (0:ℝ) ≤ 1 - t)]
    calc (1 - t) * dist c c' ≤ (1 - t) * (ρ + ρ') :=
          mul_le_mul_of_nonneg_left hlt.le (by linarith)
      _ = ρ' := ht1'
  exact (Set.disjoint_iff.mp h) ⟨hmem1, hmem2⟩

/-- Scale bound for the antichain: the size of an element is at least `σ / (r * K * Cd)`. -/
theorem antichain_scale {τ : Fin N → ℂ → ℂ} {p : ℂ} {r K Cd σ : ℝ} (hr : 0 < r) (hK : 1 < K)
    (hCd : 0 < Cd)
    (hdiff : ∀ i, DifferentiableOn ℂ (τ i) (ball p r))
    (hinj : ∀ i, InjOn (τ i) (ball p r))
    (hmaps : ∀ i, MapsTo (τ i) (ball p r) (ball p (r / 2)))
    (hlow : ∀ i, ∀ z ∈ ball p (r / 2), K⁻¹ ≤ ‖deriv (τ i) z‖)
    (hdistort : ∀ g : ℂ → ℂ, (∀ z ∈ ball p r, AnalyticAt ℂ g z) → InjOn g (ball p r) →
      ∀ z ∈ closedBall p (r / 2), ‖deriv g p‖ ≤ Cd * ‖deriv g z‖)
    (hσr : σ < r) {w : List (Fin N)} (hw : w ∈ antichain τ p r σ) :
    σ / (r * (K * Cd)) < asize τ p w := by
  have hwne : w ≠ [] := by
    intro h
    rw [h] at hw
    simp only [antichain, Set.mem_setOf_eq] at hw
    rw [asize_nil, one_mul] at hw
    linarith [hw.1, hσr]
  obtain ⟨hpref, hne, hscale⟩ := antichain_parent hw hwne
  set u := w.dropLast with hudef
  set i := w.getLast hwne with hidef
  have hw_eq : u ++ [i] = w := List.dropLast_append_getLast hwne
  have hpu : p ∈ ball p r := by rw [mem_ball, dist_self]; linarith
  have hti : τ i p ∈ ball p (r / 2) := hmaps i hpu
  have hti'' : τ i p ∈ ball p r := by
    rw [mem_ball] at hti ⊢; linarith [hti, hr]
  have hti' : τ i p ∈ closedBall p (r / 2) := by
    rw [mem_closedBall]; rw [mem_ball] at hti; exact le_of_lt hti
  have hd_u : asize τ p u ≤ Cd * ‖deriv (ifsComp τ u) (τ i p)‖ :=
    hdistort (ifsComp τ u) (ifsComp_analyticAt_all hr hdiff hmaps u)
      (ifsComp_injOn_all hr hinj hmaps u) (τ i p) hti'
  have hl : K⁻¹ ≤ ‖deriv (τ i) p‖ := hlow i p (by rw [mem_ball, dist_self]; linarith)
  have hdu : DifferentiableAt ℂ (ifsComp τ u) (τ i p) :=
    ifsComp_differentiableAt_all hr hdiff hmaps u (τ i p) hti''
  have hdi : DifferentiableAt ℂ (τ i) p := (hdiff i).differentiableAt (isOpen_ball.mem_nhds hpu)
  have hchain : deriv (ifsComp τ w) p = deriv (ifsComp τ u) (τ i p) * deriv (τ i) p := by
    rw [← hw_eq]
    exact deriv_ifsComp_append_singleton u i p hdu hdi
  have h1 : σ / r < asize τ p u := (div_lt_iff₀ hr).mpr (by linarith)
  have h2 : σ / (r * Cd) < ‖deriv (ifsComp τ u) (τ i p)‖ := by
    have h3 : σ / r / Cd < asize τ p u / Cd := div_lt_div_of_pos_right h1 hCd
    have h4 : asize τ p u / Cd ≤ ‖deriv (ifsComp τ u) (τ i p)‖ :=
      (div_le_iff₀ hCd).mpr (hd_u.trans_eq (mul_comm _ _))
    calc σ / (r * Cd) = σ / r / Cd := (div_div σ r Cd).symm
      _ < asize τ p u / Cd := h3
      _ ≤ ‖deriv (ifsComp τ u) (τ i p)‖ := h4
  have h5 : σ / (r * (K * Cd)) < ‖deriv (ifsComp τ u) (τ i p)‖ * ‖deriv (τ i) p‖ := by
    have h6 : σ / (r * (K * Cd)) = (σ / (r * Cd)) * K⁻¹ := by field_simp
    rw [h6]
    calc (σ / (r * Cd)) * K⁻¹ < ‖deriv (ifsComp τ u) (τ i p)‖ * K⁻¹ :=
          mul_lt_mul_of_pos_right h2 (inv_pos.mpr (by linarith : (0:ℝ) < K))
      _ ≤ ‖deriv (ifsComp τ u) (τ i p)‖ * ‖deriv (τ i) p‖ :=
          mul_le_mul_of_nonneg_left hl (norm_nonneg _)
  rw [asize, hchain, norm_mul]
  exact h5

/-- Koebe-type inner ball: a piece contains a disc of radius `Ci * asize * r / 2` around the
image of the base point. -/
theorem piece_inner {τ : Fin N → ℂ → ℂ} {p : ℂ} {r Ci : ℝ} (hr : 0 < r)
    (hdiff : ∀ i, DifferentiableOn ℂ (τ i) (ball p r))
    (hinj : ∀ i, InjOn (τ i) (ball p r))
    (hmaps : ∀ i, MapsTo (τ i) (ball p r) (ball p (r / 2)))
    (hkoebe : ∀ g : ℂ → ℂ, (∀ z ∈ ball p (r / 2), AnalyticAt ℂ g z) →
      InjOn g (ball p (r / 2)) →
      closedBall (g p) (Ci * ‖deriv g p‖ * (r / 2)) ⊆ g '' ball p (r / 2))
    (w : List (Fin N)) :
    closedBall (ifsComp τ w p) (Ci * asize τ p w * (r / 2)) ⊆ piece τ p r w := by
  refine Subset.trans (hkoebe (ifsComp τ w) ?_ ?_) ?_
  · intro z hz
    exact ifsComp_analyticAt_all hr hdiff hmaps w z (by rw [mem_ball] at hz ⊢; linarith [hz, hr])
  · exact (ifsComp_injOn_all hr hinj hmaps w).mono
      (by intro z hz; rw [mem_ball] at hz ⊢; linarith [hz, hr])
  · rintro z ⟨ζ, hζ, rfl⟩
    exact ⟨ζ, by rw [mem_ball] at hζ; rw [mem_closedBall]; exact le_of_lt hζ, rfl⟩

/-- The piece is contained in the ball of radius `Cg * asize * r / 2` around the image of the
base point. -/
theorem piece_outer {τ : Fin N → ℂ → ℂ} {p : ℂ} {r Cg : ℝ} (hr : 0 < r) (hCg : 0 ≤ Cg)
    (hdiff : ∀ i, DifferentiableOn ℂ (τ i) (ball p r))
    (hinj : ∀ i, InjOn (τ i) (ball p r))
    (hmaps : ∀ i, MapsTo (τ i) (ball p r) (ball p (r / 2)))
    (hgrowth : ∀ g : ℂ → ℂ, (∀ z ∈ ball p r, AnalyticAt ℂ g z) → InjOn g (ball p r) →
      ∀ z ∈ closedBall p (r / 2), ‖g z - g p‖ ≤ Cg * ‖deriv g p‖ * ‖z - p‖)
    (w : List (Fin N)) {z : ℂ} (hz : z ∈ piece τ p r w) :
    dist z (ifsComp τ w p) ≤ Cg * asize τ p w * (r / 2) := by
  rw [piece] at hz
  obtain ⟨ζ, hζ, rfl⟩ := hz
  rw [dist_eq_norm]
  have h := hgrowth (ifsComp τ w) (ifsComp_analyticAt_all hr hdiff hmaps w)
    (ifsComp_injOn_all hr hinj hmaps w) ζ hζ
  have hζr : ‖ζ - p‖ ≤ r / 2 := by
    rw [← dist_eq_norm]; exact mem_closedBall.mp hζ
  calc ‖ifsComp τ w ζ - ifsComp τ w p‖ ≤ Cg * ‖deriv (ifsComp τ w) p‖ * ‖ζ - p‖ := h
    _ ≤ Cg * ‖deriv (ifsComp τ w) p‖ * (r / 2) :=
          mul_le_mul_of_nonneg_left hζr (mul_nonneg hCg (norm_nonneg _))

/-! ### The Frostman bound -/

/-- **Counting lemma.** Every finite family of words of the Moran antichain whose pieces meet a
set `A` of diameter at most `σ` has at most `Cpack * (1 + 2 K Cd (1 + Cg/2) / Ci)²` elements. -/
theorem count_bound {N : ℕ} (τ : Fin N → ℂ → ℂ) (p : ℂ) (r K σ Cg Ci Cd Cpack : ℝ)
    (hr : 0 < r) (hK : 1 < K) (hσ : 0 < σ) (hσr : σ < r)
    (hCg : 0 < Cg) (hCi : 0 < Ci) (hCd : 0 < Cd)
    (hdiff : ∀ i, DifferentiableOn ℂ (τ i) (ball p r))
    (hinj : ∀ i, InjOn (τ i) (ball p r))
    (hmaps : ∀ i, MapsTo (τ i) (ball p r) (ball p (r / 2)))
    (hdisj : Pairwise fun i j => Disjoint (τ i '' ball p r) (τ j '' ball p r))
    (hlow : ∀ i, ∀ z ∈ ball p (r / 2), K⁻¹ ≤ ‖deriv (τ i) z‖)
    (hdistort : ∀ g : ℂ → ℂ, (∀ z ∈ ball p r, AnalyticAt ℂ g z) → InjOn g (ball p r) →
      ∀ z ∈ closedBall p (r / 2), ‖deriv g p‖ ≤ Cd * ‖deriv g z‖)
    (hkoebe : ∀ g : ℂ → ℂ, (∀ z ∈ ball p (r / 2), AnalyticAt ℂ g z) →
      InjOn g (ball p (r / 2)) →
      closedBall (g p) (Ci * ‖deriv g p‖ * (r / 2)) ⊆ g '' ball p (r / 2))
    (hgrowth : ∀ g : ℂ → ℂ, (∀ z ∈ ball p r, AnalyticAt ℂ g z) → InjOn g (ball p r) →
      ∀ z ∈ closedBall p (r / 2), ‖g z - g p‖ ≤ Cg * ‖deriv g p‖ * ‖z - p‖)
    (hpack : ∀ (x : ℂ) (M ρ : ℝ), 0 < ρ → ∀ t : Finset ℂ,
      (∀ c ∈ t, c ∈ closedBall x M) → (∀ c ∈ t, ∀ c' ∈ t, c ≠ c' → 2 * ρ ≤ dist c c') →
      (t.card : ℝ) ≤ Cpack * (1 + M / ρ) ^ 2)
    {A : Set ℂ} (hdiam : ∀ a ∈ A, ∀ b ∈ A, dist a b ≤ σ)
    {S : Set (List (Fin N))} (hS : ∀ w ∈ S, w ∈ antichain τ p r σ)
    (hSA : ∀ w ∈ S, (piece τ p r w ∩ A).Nonempty)
    (F : Finset {w : List (Fin N) // w ∈ S}) :
    (F.card : ℝ) ≤ Cpack * (1 + 2 * (K * Cd) * (1 + Cg / 2) / Ci) ^ 2 := by
  have hCpack0 : 0 ≤ Cpack := by
    have := hpack 0 0 1 one_pos (∅ : Finset ℂ) (by simp) (by simp)
    simpa using this
  have hKd : 0 < K * Cd := by positivity
  set M : ℝ := σ * (1 + Cg / 2) with hMdef
  set ρ : ℝ := Ci * σ / (2 * (K * Cd)) with hρdef
  have hρpos : 0 < ρ := by
    rw [hρdef]; positivity
  rcases F.eq_empty_or_nonempty with rfl | hFne
  · have : 0 ≤ Cpack * (1 + 2 * (K * Cd) * (1 + Cg / 2) / Ci) ^ 2 :=
      mul_nonneg hCpack0 (sq_nonneg _)
    simpa using this
  obtain ⟨x₀, hx₀⟩ := hFne
  obtain ⟨y₀, -, hy₀A⟩ := hSA x₀.1 x₀.2
  set g : {w : List (Fin N) // w ∈ S} → ℂ := fun x => ifsComp τ x.1 p with hgdef
  have hgc : ∀ x : {w : List (Fin N) // w ∈ S}, g x ∈ piece τ p r x.1 := by
    intro x
    rw [hgdef, piece]
    exact ⟨p, by rw [mem_closedBall, dist_self]; linarith, rfl⟩
  -- the inner radius of the piece of `x`, as a function of `x`
  have hinner : ∀ x : {w : List (Fin N) // w ∈ S},
      closedBall (g x) (Ci * asize τ p x.1 * (r / 2)) ⊆ piece τ p r x.1 :=
    fun x => piece_inner hr hdiff hinj hmaps hkoebe x.1
  have hrad : ∀ x : {w : List (Fin N) // w ∈ S}, ρ < Ci * asize τ p x.1 * (r / 2) := by
    intro x
    have hscale := antichain_scale hr hK hCd hdiff hinj hmaps hlow hdistort hσr (hS x.1 x.2)
    have h2 : σ < asize τ p x.1 * (r * (K * Cd)) := (div_lt_iff₀ (mul_pos hr hKd)).mp hscale
    rw [hρdef, div_lt_iff₀ (mul_pos two_pos hKd)]
    nlinarith [h2, hCi]
  -- the injection
  have hinjF : Set.InjOn g ↑F := by
    intro x hx y hy hxy
    by_contra hne
    have h1 : x.1 ≠ y.1 := fun h => hne (Subtype.ext h)
    have hpxy := antichain_not_prefix (hS x.1 x.2) (hS y.1 y.2) h1
    have hdj := Work.Dim.Pieces.disjoint τ p r hr hmaps hinj hdisj x.1 y.1 hpxy.1 hpxy.2
    exact (Set.disjoint_iff.mp hdj) ⟨hgc x, by rw [hxy]; exact hgc y⟩
  have hcard : (F.image g).card = F.card := Finset.card_image_iff.mpr hinjF
  -- the centres lie in a ball of radius `M`
  have hsub : ∀ c ∈ F.image g, c ∈ closedBall y₀ M := by
    intro c hc
    obtain ⟨x, hxF, rfl⟩ := Finset.mem_image.mp hc
    obtain ⟨y, hyP, hyA⟩ := hSA x.1 x.2
    have h1 : dist (g x) y ≤ Cg * asize τ p x.1 * (r / 2) :=
      (dist_comm (g x) y).trans_le (piece_outer hr hCg.le hdiff hinj hmaps hgrowth x.1 hyP)
    have h2 : asize τ p x.1 * r ≤ σ := (hS x.1 x.2).1
    have h3 : Cg * asize τ p x.1 * (r / 2) ≤ M := by
      rw [hMdef]
      nlinarith [h2, hCg, hσ]
    have h4 : dist y y₀ ≤ σ := hdiam y hyA y₀ hy₀A
    have h5 : Cg * asize τ p x.1 * (r / 2) + σ ≤ M := by
      rw [hMdef]
      nlinarith [h2, hCg, hσ]
    rw [mem_closedBall]
    calc dist (g x) y₀ ≤ dist (g x) y + dist y y₀ := dist_triangle _ _ _
      _ ≤ M := by linarith
  -- the centres are `2ρ`-separated
  have hsep : ∀ c ∈ F.image g, ∀ c' ∈ F.image g, c ≠ c' → 2 * ρ ≤ dist c c' := by
    intro c hc c' hc' hne
    obtain ⟨x, hxF, rfl⟩ := Finset.mem_image.mp hc
    obtain ⟨y, hyF, rfl⟩ := Finset.mem_image.mp hc'
    have hxy : x ≠ y := fun h => hne (by rw [h])
    have h1 : x.1 ≠ y.1 := fun h => hxy (Subtype.ext h)
    have hpxy := antichain_not_prefix (hS x.1 x.2) (hS y.1 y.2) h1
    have hdj := Work.Dim.Pieces.disjoint τ p r hr hmaps hinj hdisj x.1 y.1 hpxy.1 hpxy.2
    have hdj2 : Disjoint (closedBall (g x) (Ci * asize τ p x.1 * (r / 2)))
        (closedBall (g y) (Ci * asize τ p y.1 * (r / 2))) :=
      hdj.mono (hinner x) (hinner y)
    have hdist := le_dist_of_disjoint_closedBall
      (mul_nonneg (mul_nonneg hCi.le (norm_nonneg _)) (by linarith : (0:ℝ) ≤ r / 2))
      (mul_nonneg (mul_nonneg hCi.le (norm_nonneg _)) (by linarith : (0:ℝ) ≤ r / 2)) hdj2
    have hxr := le_of_lt (hrad x)
    have hyr := le_of_lt (hrad y)
    simp only [asize] at hxr hyr
    linarith
  have hpack' := hpack y₀ M ρ hρpos (F.image g) hsub hsep
  rw [hcard] at hpack'
  have hQ : M / ρ = 2 * (K * Cd) * (1 + Cg / 2) / Ci := by
    rw [hMdef, hρdef]
    field_simp
  rw [hQ] at hpack'
  exact hpack'

/-- Arithmetic: the `k`-th power of `N⁻¹` in terms of `K ^ D = N`. -/
theorem inv_pow_eq_rpow {N K D : ℝ} (hK : 1 < K) (hKD : K ^ D = N) {k : ℕ} :
    N⁻¹ ^ k = ((K⁻¹ : ℝ) ^ k) ^ D := by
  have hK0 : (0:ℝ) < K := by linarith
  have h1 : N⁻¹ ^ k = ((K ^ D)⁻¹ : ℝ) ^ k := by rw [hKD]
  have h2 : ((K ^ D)⁻¹ : ℝ) ^ k = (K ^ (D * (k:ℝ)))⁻¹ := by
    rw [inv_pow, ← Real.rpow_natCast (K^D) k, ← Real.rpow_mul hK0.le]
  have h3 : (K ^ (D * (k:ℝ)))⁻¹ = ((K⁻¹ : ℝ) ^ (k:ℝ)) ^ D := by
    have h3a : (K ^ (D * (k:ℝ)))⁻¹ = (K⁻¹ : ℝ) ^ (D * (k:ℝ)) :=
      (Real.inv_rpow hK0.le _).symm
    have h3b : (K⁻¹ : ℝ) ^ (D * (k:ℝ)) = (K⁻¹ : ℝ) ^ ((k:ℝ) * D) := by rw [mul_comm]
    have h3c : (K⁻¹ : ℝ) ^ ((k:ℝ) * D) = ((K⁻¹ : ℝ) ^ (k:ℝ)) ^ D :=
      Real.rpow_mul (by positivity : (0:ℝ) ≤ K⁻¹) (k:ℝ) D
    rw [h3a, h3b, h3c]
  have h4 : ((K⁻¹ : ℝ) ^ (k:ℝ)) ^ D = ((K⁻¹ : ℝ) ^ k) ^ D := by rw [Real.rpow_natCast]
  rw [h1, h2, h3, h4]

/-- **Frostman bound.** For a conformal IFS on `ball p r` with branch derivative at most `θ < 1`
on `closedBall p (r/2)`, any pushforward of the Bernoulli measure by the coding map is a Frostman
measure of exponent `log N / log K`. -/
theorem frostman_bound {N : ℕ} (τ : Fin N → ℂ → ℂ) (p : ℂ) (r K θ Ci Cg Cd : ℝ)
    (hN : 2 ≤ N) (hr : 0 < r) (hK : 1 < K) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (hdiff : ∀ i, DifferentiableOn ℂ (τ i) (ball p r))
    (hinj : ∀ i, InjOn (τ i) (ball p r))
    (hmaps : ∀ i, MapsTo (τ i) (ball p r) (ball p (r / 2)))
    (hdisj : Pairwise fun i j => Disjoint (τ i '' ball p r) (τ j '' ball p r))
    (hlow : ∀ i, ∀ z ∈ ball p (r / 2), K⁻¹ ≤ ‖deriv (τ i) z‖)
    (hderiv : ∀ i, ∀ z ∈ closedBall p (r / 2), ‖deriv (τ i) z‖ ≤ θ)
    (hCi : 0 < Ci) (hCg : 0 < Cg) (hCd : 0 < Cd)
    (hkoebe : ∀ g : ℂ → ℂ, (∀ z ∈ ball p (r / 2), AnalyticAt ℂ g z) →
      InjOn g (ball p (r / 2)) →
      closedBall (g p) (Ci * ‖deriv g p‖ * (r / 2)) ⊆ g '' ball p (r / 2))
    (hdistort : ∀ g : ℂ → ℂ, (∀ z ∈ ball p r, AnalyticAt ℂ g z) → InjOn g (ball p r) →
      ∀ z ∈ closedBall p (r / 2), ‖deriv g p‖ ≤ Cd * ‖deriv g z‖)
    (hgrowth : ∀ g : ℂ → ℂ, (∀ z ∈ ball p r, AnalyticAt ℂ g z) → InjOn g (ball p r) →
      ∀ z ∈ closedBall p (r / 2), ‖g z - g p‖ ≤ Cg * ‖deriv g p‖ * ‖z - p‖)
    (hmem : ∀ (ω : ℕ → Fin N) (k : ℕ), codingPt τ p ω ∈ piece τ p r (pref ω k))
    (ν : Measure (ℕ → Fin N)) (hνprob : IsProbabilityMeasure ν)
    (hνcyl : ∀ w : List (Fin N), ν {ω : ℕ → Fin N | ∀ k : Fin w.length, ω k = w.get k} =
      ((N : ENNReal))⁻¹ ^ w.length) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A : Set ℂ) (σ : ℝ), 0 < σ →
      (∀ a ∈ A, ∀ b ∈ A, dist a b ≤ σ) →
      ν (codingPt τ p ⁻¹' A) ≤
        ENNReal.ofReal C * ENNReal.ofReal (σ ^ (Real.log N / Real.log K)) := by
  classical
  haveI := hνprob
  have hNpos : 0 < N := by omega
  have hK0 : (0 : ℝ) < K := by linarith
  obtain ⟨Cpack, hCpack, hpack⟩ := Work.Dim.Packing.packing
  set D := Real.log N / Real.log K with hDdef
  have hDpos : 0 < D := by
    rw [hDdef]
    exact div_pos (Real.log_pos (by exact_mod_cast hN)) (Real.log_pos hK)
  have hD0 : 0 ≤ D := le_of_lt hDpos
  have hKD : K ^ D = (N : ℝ) := by
    rw [hDdef]
    rw [show Real.log (N:ℝ) / Real.log K = Real.logb K (N:ℝ) from rfl]
    exact Real.rpow_logb hK0 (by linarith) (by exact_mod_cast hNpos)
  -- constants
  set Q : ℝ := 2 * (K * Cd) * (1 + Cg / 2) / Ci with hQdef
  have hQ0 : 0 ≤ Q := by positivity
  set Cpk : ℝ := Cpack * (1 + Q) ^ 2 with hCpkdef
  have hCpk0 : 0 < Cpk := by positivity
  set Cfin : ℝ := max (Cpk * r ^ (-D)) (r ^ (-D)) with hCfindef
  have hCfind : Cfin ≥ r ^ (-D) := le_max_right _ _
  have hCfinCpk : Cfin ≥ Cpk * r ^ (-D) := le_max_left _ _
  have hCfin0 : 0 < Cfin := lt_of_lt_of_le (Real.rpow_pos_of_pos hr _) hCfind
  refine ⟨Cfin, hCfin0, ?_⟩
  intro A σ hσ hdiam
  by_cases hσr : r ≤ σ
  · -- large scale: trivial bound
    have h1 : ν (codingPt τ p ⁻¹' A) ≤ 1 := by
      calc ν (codingPt τ p ⁻¹' A) ≤ ν Set.univ := measure_mono (subset_univ _)
        _ = 1 := measure_univ
    have h2 : (1 : ENNReal) ≤ ENNReal.ofReal Cfin * ENNReal.ofReal (σ ^ D) := by
      have hσr' : 1 ≤ σ / r := (one_le_div hr).mpr hσr
      have h3 : (σ / r) ^ D = σ ^ D * r ^ (-D) := by
        rw [Real.div_rpow (le_of_lt hσ) hr.le, div_eq_mul_inv, ← Real.rpow_neg hr.le]
      calc (1 : ENNReal) = ENNReal.ofReal 1 := ENNReal.ofReal_one.symm
        _ ≤ ENNReal.ofReal ((σ / r) ^ D) :=
              ENNReal.ofReal_le_ofReal (Real.one_le_rpow hσr' hD0)
        _ = ENNReal.ofReal (σ ^ D) * ENNReal.ofReal (r ^ (-D)) := by
              rw [h3, ENNReal.ofReal_mul (Real.rpow_nonneg (le_of_lt hσ) D)]
        _ ≤ ENNReal.ofReal (σ ^ D) * ENNReal.ofReal Cfin :=
              mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal hCfind) (by positivity)
        _ = ENNReal.ofReal Cfin * ENNReal.ofReal (σ ^ D) := mul_comm _ _
    exact le_trans h1 h2
  · -- small scale: Moran antichain
    rw [not_le] at hσr
    set S : Set (List (Fin N)) :=
      {w | w ∈ antichain τ p r σ ∧ (piece τ p r w ∩ A).Nonempty} with hSdef
    have hcyl : ∀ w : List (Fin N), {ω : ℕ → Fin N | ∀ k : Fin w.length, ω k = w.get k} =
        MandelDim.cylinder w := fun w => (cylinder_eq w).symm
    -- the cover
    have hcov : codingPt τ p ⁻¹' A ⊆
        ⋃ w ∈ S, {ω : ℕ → Fin N | ∀ k : Fin w.length, ω k = w.get k} := by
      intro ω hω
      obtain ⟨w, hwA, hwcyl⟩ := exists_antichain_of_lt hr hθ0 hθ1 hdiff hmaps hderiv hσ hσr ω
      refine mem_iUnion.mpr ⟨w, mem_iUnion.mpr ⟨⟨hwA, ?_⟩, ?_⟩⟩
      · exact ⟨codingPt τ p ω, by rw [← pref_eq_of_mem_cylinder hwcyl]; exact hmem ω w.length, hω⟩
      · exact mem_cylinder_iff.mp hwcyl
    -- the mass of the union
    have hmass : ν (codingPt τ p ⁻¹' A) ≤
        ∑' w : {w : List (Fin N) // w ∈ S}, ((N : ENNReal))⁻¹ ^ (w.1.length) := by
      refine le_trans (measure_mono hcov) ?_
      rw [show (⋃ w ∈ S, {ω : ℕ → Fin N | ∀ k : Fin w.length, ω k = w.get k}) =
          ⋃ w : {w : List (Fin N) // w ∈ S},
            {ω : ℕ → Fin N | ∀ k : Fin w.1.length, ω k = w.1.get k} from by
        ext ω; simp only [mem_iUnion, mem_setOf_eq]; constructor
        · rintro ⟨w, hw, h⟩; exact ⟨⟨w, hw⟩, h⟩
        · rintro ⟨⟨w, hw⟩, h⟩; exact ⟨w, hw, h⟩]
      refine le_trans (measure_iUnion_le _) ?_
      exact ENNReal.tsum_le_tsum fun w => le_of_eq (hνcyl w.1)
    -- the finite bound
    have hfin : ∑' w : {w : List (Fin N) // w ∈ S}, ((N : ENNReal))⁻¹ ^ (w.1.length) ≤
        ENNReal.ofReal (Cpk * (σ / r) ^ D) := by
      rw [ENNReal.tsum_eq_iSup_sum]
      refine iSup_le fun F => ?_
      have hterm : ∀ w ∈ F, ((N : ENNReal))⁻¹ ^ (w.1.length) ≤ ENNReal.ofReal ((σ / r) ^ D) := by
        intro w hwF
        have hwS : w.1 ∈ S := w.2
        have hwW : w.1 ∈ antichain τ p r σ := hwS.1
        have hwnil : w.1 ≠ [] := by
          intro h
          rw [h] at hwW
          simp only [antichain, Set.mem_setOf_eq] at hwW
          rw [asize_nil, one_mul] at hwW
          linarith [hwW.1, hσr]
        have hlow' : K⁻¹ ^ (w.1.length) ≤ asize τ p w.1 := by
          have := le_norm_deriv_ifsComp hr hK0 hdiff hmaps hlow w.1 hwnil p
            (by rw [mem_ball, dist_self]; linarith)
          simpa [asize] using this
        have hsc : asize τ p w.1 * r ≤ σ := hwW.1
        have hle : K⁻¹ ^ (w.1.length) ≤ σ / r :=
          (le_div_iff₀ hr).mpr (le_trans (mul_le_mul_of_nonneg_right hlow' hr.le) hsc)
        have heq : (N : ℝ)⁻¹ ^ (w.1.length) = ((K⁻¹ : ℝ) ^ (w.1.length)) ^ D :=
          inv_pow_eq_rpow hK hKD
        have hreal : (N : ℝ)⁻¹ ^ (w.1.length) ≤ (σ / r) ^ D := by
          rw [heq]
          exact Real.rpow_le_rpow (by positivity) hle hD0
        calc ((N : ENNReal))⁻¹ ^ (w.1.length)
            = ENNReal.ofReal ((N : ℝ)⁻¹ ^ w.1.length) := by
              rw [ENNReal.ofReal_pow (by positivity : (0:ℝ) ≤ ((N:ℝ))⁻¹),
                ENNReal.ofReal_inv_of_pos (by exact_mod_cast hNpos), ENNReal.ofReal_natCast]
          _ ≤ ENNReal.ofReal ((σ / r) ^ D) := ENNReal.ofReal_le_ofReal hreal
      calc ∑ w ∈ F, ((N : ENNReal))⁻¹ ^ (w.1.length)
          ≤ ∑ w ∈ F, ENNReal.ofReal ((σ / r) ^ D) := Finset.sum_le_sum hterm
        _ = (F.card : ENNReal) * ENNReal.ofReal ((σ / r) ^ D) := by
              rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ENNReal.ofReal Cpk * ENNReal.ofReal ((σ / r) ^ D) := by
              refine mul_le_mul_of_nonneg_right ?_ (by positivity)
              rw [← ENNReal.ofReal_natCast]
              exact ENNReal.ofReal_le_ofReal (count_bound τ p r K σ Cg Ci Cd Cpack hr hK hσ hσr
                hCg hCi hCd hdiff hinj hmaps hdisj hlow hdistort hkoebe hgrowth hpack hdiam
                (fun w hw => hw.1) (fun w hw => hw.2) F)
        _ = ENNReal.ofReal (Cpk * (σ / r) ^ D) :=
              (ENNReal.ofReal_mul (le_of_lt hCpk0)).symm
    -- the final constant comparison
    have hcmp : Cpk * (σ / r) ^ D ≤ Cfin * σ ^ D := by
      have h1 : (σ / r) ^ D = σ ^ D * r ^ (-D) := by
        rw [Real.div_rpow (le_of_lt hσ) hr.le, div_eq_mul_inv, ← Real.rpow_neg hr.le]
      have h2 : Cpk * (σ ^ D * r ^ (-D)) = Cpk * r ^ (-D) * σ ^ D := by ring
      rw [h1, h2]
      exact mul_le_mul_of_nonneg_right hCfinCpk (Real.rpow_nonneg (le_of_lt hσ) D)
    calc ν (codingPt τ p ⁻¹' A)
        ≤ ∑' w : {w : List (Fin N) // w ∈ S}, ((N : ENNReal))⁻¹ ^ (w.1.length) := hmass
      _ ≤ ENNReal.ofReal (Cpk * (σ / r) ^ D) := hfin
      _ ≤ ENNReal.ofReal (Cfin * σ ^ D) := ENNReal.ofReal_le_ofReal hcmp
      _ = ENNReal.ofReal Cfin * ENNReal.ofReal (σ ^ D) :=
            ENNReal.ofReal_mul (le_of_lt hCfin0)

/-! ### The main theorem -/

open scoped Classical in
/-- **Dimension of the limit set of a conformal IFS.** Assuming the Koebe-type estimates
(`hkoebe0`, `hballbounds`) and the Frostman principle (`hdim`), the Hausdorff dimension of every
cylinder of the limit set is at least `log N / log K`. -/
theorem dim_of_inputs
    (hkoebe0 : ∃ Cup Clow : ℝ, 0 < Cup ∧ 0 < Clow ∧
      ∀ f : ℂ → ℂ, (∀ z ∈ ball (0 : ℂ) 1, AnalyticAt ℂ f z) → InjOn f (ball (0 : ℂ) 1) →
        f 0 = 0 → deriv f 0 = 1 →
        ∀ z : ℂ, ‖z‖ ≤ 1 / 2 → Clow ≤ ‖deriv f z‖ ∧ ‖deriv f z‖ ≤ Cup)
    (hballbounds : ∀ (Cup Clow : ℝ), 0 < Cup → 0 < Clow →
      (∀ f : ℂ → ℂ, (∀ z ∈ ball (0 : ℂ) 1, AnalyticAt ℂ f z) → InjOn f (ball (0 : ℂ) 1) →
        f 0 = 0 → deriv f 0 = 1 →
        ∀ z : ℂ, ‖z‖ ≤ 1 / 2 → Clow ≤ ‖deriv f z‖ ∧ ‖deriv f z‖ ≤ Cup) →
      ∃ Ci Cg Cd : ℝ, 0 < Ci ∧ 0 < Cg ∧ 0 < Cd ∧
        (∀ (g : ℂ → ℂ) (p : ℂ) (ρ : ℝ), 0 < ρ → (∀ z ∈ ball p ρ, AnalyticAt ℂ g z) →
          InjOn g (ball p ρ) → closedBall (g p) (Ci * ‖deriv g p‖ * ρ) ⊆ g '' ball p ρ) ∧
        (∀ (g : ℂ → ℂ) (p : ℂ) (ρ : ℝ), 0 < ρ → (∀ z ∈ ball p ρ, AnalyticAt ℂ g z) →
          InjOn g (ball p ρ) →
          ∀ z ∈ closedBall p (ρ / 2), ‖deriv g p‖ ≤ Cd * ‖deriv g z‖) ∧
        (∀ (g : ℂ → ℂ) (p : ℂ) (ρ : ℝ), 0 < ρ → (∀ z ∈ ball p ρ, AnalyticAt ℂ g z) →
          InjOn g (ball p ρ) →
          ∀ z ∈ closedBall p (ρ / 2), ‖g z - g p‖ ≤ Cg * ‖deriv g p‖ * ‖z - p‖))
    (hdim : ∀ {s : Set ℂ} {d : ℝ}, 0 < d → ∀ μ : MeasureTheory.Measure ℂ, μ s ≠ 0 →
      (∃ C : ℝ, 0 < C ∧ ∀ (A : Set ℂ) (σ : ℝ), 0 < σ →
        (∀ a ∈ A, ∀ b ∈ A, dist a b ≤ σ) → μ A ≤ ENNReal.ofReal (C * σ ^ d)) →
      ENNReal.ofReal d ≤ dimH s) :
    DimStatement := by
  intro N τ p r K hN hIFS l
  obtain ⟨hr, hK1, hdiff, hinj, hmaps, hdisj, hlow⟩ := hIFS
  have hN1 : 1 ≤ N := by omega
  have hNpos : 0 < N := by omega
  -- (1) contraction ratio
  obtain ⟨θ, hθ0, hθ1, hθ⟩ := Work.Dim.Branch.derivBound
  have hderiv : ∀ i, ∀ z ∈ closedBall p (r / 2), ‖deriv (τ i) z‖ ≤ θ :=
    fun i z hz => hθ (τ i) p r hr (hdiff i)
      (fun ζ hζ => ball_subset_closedBall (hmaps i hζ)) z hz
  -- (2) Koebe-type estimates
  obtain ⟨Cup, Clow, hCup, hClow, hdisc⟩ := hkoebe0
  obtain ⟨Ci, Cg, Cd, hCi, hCg, hCd, hkoebeρ, hdistortρ, hgrowthρ⟩ :=
    hballbounds Cup Clow hCup hClow hdisc
  -- (3) the coding map
  obtain ⟨htend, hmem, hcont, hclose⟩ :=
    Work.Dim.Coding.map τ p r θ hr hθ0 hθ1 hmaps hderiv hdiff hdisj
  -- (4) the Bernoulli measure and the Frostman bound
  obtain ⟨ν, hνprob, hνcyl⟩ := Work.Dim.Code.measure N hN1
  obtain ⟨C, hC, hfrost⟩ := frostman_bound τ p r K θ Ci Cg Cd hN hr hK1 hθ0 hθ1 hdiff hinj
    hmaps hdisj hlow hderiv hCi hCg hCd
    (fun g h1 h2 => hkoebeρ g p (r / 2) (by linarith) h1 h2)
    (fun g h1 h2 z hz => hdistortρ g p r hr h1 h2 z hz)
    (fun g h1 h2 z hz => hgrowthρ g p r hr h1 h2 z hz)
    hmem ν hνprob hνcyl
  set μ : MeasureTheory.Measure ℂ := MeasureTheory.Measure.map (codingPt τ p) ν with hμdef
  have hDpos : 0 < Real.log (N : ℝ) / Real.log K :=
    div_pos (Real.log_pos (by exact_mod_cast hN)) (Real.log_pos hK1)
  -- (5) the limit piece is compact, hence Borel
  have hcylclosed : IsClosed (MandelDim.cylinder l) := by
    have h : MandelDim.cylinder l =
        ⋂ k : Fin l.length, {ω : ℕ → Fin N | ω (k : ℕ) = l.get k} := by
      ext ω
      simp only [Set.mem_iInter, Set.mem_setOf_eq, MandelDim.cylinder]
      constructor
      · intro h k; exact h (k : ℕ) k.isLt
      · intro h k hk; exact h ⟨k, hk⟩
    rw [h]
    exact isClosed_iInter fun k : Fin l.length =>
      isClosed_eq (continuous_apply (k : ℕ)) continuous_const
  have hcomp : IsCompact (Set.univ : Set (ℕ → Fin N)) := by
    simpa using isCompact_univ_pi
      (fun _ : ℕ => (isCompact_univ : IsCompact (Set.univ : Set (Fin N))))
  have hcylcompact : IsCompact (MandelDim.cylinder l) :=
    IsCompact.of_isClosed_subset hcomp hcylclosed (subset_univ _)
  have hPmeas : MeasurableSet (codingPt τ p '' MandelDim.cylinder l) :=
    ((hcylcompact.image hcont).isClosed).measurableSet
  -- (6) the measure of the limit piece is positive
  have hνcyl' : ν (MandelDim.cylinder l) = ((N : ENNReal))⁻¹ ^ l.length := by
    rw [cylinder_eq l]; exact hνcyl l
  have hνcyl_ne : ν (MandelDim.cylinder l) ≠ 0 := by
    rw [hνcyl']
    exact pow_ne_zero _ (ENNReal.inv_ne_zero.mpr (by simp [hNpos]))
  have hμP : μ (codingPt τ p '' MandelDim.cylinder l) ≠ 0 := by
    refine fun h0 => hνcyl_ne ?_
    have h1 : ν (MandelDim.cylinder l) ≤ μ (codingPt τ p '' MandelDim.cylinder l) := by
      rw [hμdef, MeasureTheory.Measure.map_apply hcont.measurable hPmeas]
      exact measure_mono fun ω hω => ⟨ω, hω, rfl⟩
    rw [h0] at h1
    exact le_antisymm h1 bot_le
  -- (7) the Frostman bound on ℂ
  have hbound : ∃ C' : ℝ, 0 < C' ∧ ∀ (A : Set ℂ) (σ : ℝ), 0 < σ →
      (∀ a ∈ A, ∀ b ∈ A, dist a b ≤ σ) →
      μ A ≤ ENNReal.ofReal (C' * σ ^ (Real.log (N : ℝ) / Real.log K)) := by
    refine ⟨C, hC, ?_⟩
    intro A σ hσ hdiam
    have hcl : MeasurableSet (closure A) := isClosed_closure.measurableSet
    have hdiamcl : ∀ a ∈ closure A, ∀ b ∈ closure A, dist a b ≤ σ := by
      intro a ha b hb
      have hcl : IsClosed {p : ℂ × ℂ | dist p.1 p.2 ≤ σ} :=
        isClosed_le continuous_dist continuous_const
      have hsub : A ×ˢ A ⊆ {p : ℂ × ℂ | dist p.1 p.2 ≤ σ} := by
        rintro ⟨a', b'⟩ ⟨ha', hb'⟩
        exact hdiam a' ha' b' hb'
      have hsub' : closure A ×ˢ closure A ⊆ {p : ℂ × ℂ | dist p.1 p.2 ≤ σ} := by
        rw [← closure_prod_eq]
        exact (hcl.closure_subset_iff).mpr hsub
      exact hsub' (Set.mk_mem_prod ha hb)
    calc μ A ≤ μ (closure A) := measure_mono subset_closure
      _ = ν (codingPt τ p ⁻¹' closure A) := by
            rw [hμdef, MeasureTheory.Measure.map_apply hcont.measurable hcl]
      _ ≤ ENNReal.ofReal C * ENNReal.ofReal (σ ^ (Real.log (N : ℝ) / Real.log K)) :=
            hfrost (closure A) σ hσ hdiamcl
      _ = ENNReal.ofReal (C * σ ^ (Real.log (N : ℝ) / Real.log K)) :=
            (ENNReal.ofReal_mul (le_of_lt hC)).symm
  exact hdim (s := codingPt τ p '' MandelDim.cylinder l)
    (d := Real.log (N : ℝ) / Real.log K) hDpos μ hμP hbound

end Work.Dim
