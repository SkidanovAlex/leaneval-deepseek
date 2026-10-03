import Mathlib
import Submission.Work.Interfaces.Basic
import Submission.Work.Motion.Basic

/-!
# The coding map of the moving dynamical IFS
-/

namespace Work.Motion

open MandelDim
open LeanEval.Dynamics.MandelbrotBoundary
open Set Metric Filter
open scoped Topology
open Classical

noncomputable section

/-- The composition of the first `k` branches along a code:
`pComp g ω k = g (ω 0) ∘ g (ω 1) ∘ ⋯ ∘ g (ω (k-1))` (`k = 0` gives `id`). -/
def pComp {N : ℕ} (g : Fin N → ℂ → ℂ) (ω : ℕ → Fin N) : ℕ → ℂ → ℂ
  | 0 => id
  | (k + 1) => g (ω 0) ∘ pComp g (fun j => ω (j + 1)) k

@[simp] lemma pComp_zero {N : ℕ} (g : Fin N → ℂ → ℂ) (ω : ℕ → Fin N) :
    pComp g ω 0 = id := rfl

@[simp] lemma pComp_succ {N : ℕ} (g : Fin N → ℂ → ℂ) (ω : ℕ → Fin N) (k : ℕ) :
    pComp g ω (k + 1) = g (ω 0) ∘ pComp g (fun j => ω (j + 1)) k := rfl

lemma pComp_succ_comp {N : ℕ} (g : Fin N → ℂ → ℂ) (ω : ℕ → Fin N) (k : ℕ) :
    pComp g ω (k + 1) = pComp g ω k ∘ g (ω k) := by
  induction k generalizing ω with
  | zero => rfl
  | succ k ih =>
    rw [pComp_succ, ih (fun j => ω (j + 1)), pComp_succ]
    rfl

lemma ifsComp_cons {N : ℕ} (g : Fin N → ℂ → ℂ) (i : Fin N) (l : List (Fin N)) :
    MandelDim.ifsComp g (i :: l) = g i ∘ MandelDim.ifsComp g l := rfl

lemma pComp_eq_ifsComp {N : ℕ} (g : Fin N → ℂ → ℂ) (ω : ℕ → Fin N) (k : ℕ) :
    pComp g ω k = MandelDim.ifsComp g ((List.range k).map ω) := by
  induction k generalizing ω with
  | zero => rfl
  | succ k ih =>
    rw [pComp_succ, List.range_succ_eq_map, List.map_cons, ifsComp_cons]
    have h : List.map ω (List.map Nat.succ (List.range k))
        = List.map (fun j => ω (j + 1)) (List.range k) := by
      rw [List.map_map]
      exact congrArg (List.map · (List.range k)) (funext fun j => rfl)
    rw [h, ← ih (fun j => ω (j + 1))]

/-- A sequence satisfying a geometric two-point bound from below is Cauchy. -/
lemma cauchySeq_of_geometric_bound {u : ℕ → ℂ} {C θ : ℝ} (hC : 0 ≤ C) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (h : ∀ n ≥ 1, ∀ m ≥ n, dist (u m) (u n) ≤ C * θ ^ (n - 1)) : CauchySeq u := by
  rw [Metric.cauchySeq_iff]
  intro ε hε
  obtain ⟨N₀, hN₀⟩ := exists_pow_lt_of_lt_one
    (show (0:ℝ) < ε / (C + 1) by positivity) hθ1
  refine ⟨N₀ + 1, fun m hm n hn => ?_⟩
  have hm1 : 1 ≤ m := by omega
  have hn1 : 1 ≤ n := by omega
  have h5 : C * (ε / (C + 1)) < ε := by
    have hpos : (0:ℝ) < C + 1 := by linarith
    rw [← mul_div_assoc, div_lt_iff₀ hpos]
    nlinarith [hε.le]
  rcases le_total n m with hmn | hmn
  · have h1 := h n hn1 m hmn
    have h2 : θ ^ (n - 1) ≤ θ ^ N₀ := pow_le_pow_of_le_one hθ0 (le_of_lt hθ1) (by omega)
    have h3 : C * θ ^ (n - 1) ≤ C * θ ^ N₀ := mul_le_mul_of_nonneg_left h2 hC
    have h4 : C * θ ^ N₀ ≤ C * (ε / (C + 1)) := mul_le_mul_of_nonneg_left hN₀.le hC
    linarith
  · have h1 := h m hm1 n hmn
    have h2 : θ ^ (m - 1) ≤ θ ^ N₀ := pow_le_pow_of_le_one hθ0 (le_of_lt hθ1) (by omega)
    have h3 : C * θ ^ (m - 1) ≤ C * θ ^ N₀ := mul_le_mul_of_nonneg_left h2 hC
    have h4 : C * θ ^ N₀ ≤ C * (ε / (C + 1)) := mul_le_mul_of_nonneg_left hN₀.le hC
    rw [dist_comm]; linarith

/-- `pComp` only depends on the first `k` letters of the code. -/
lemma pComp_congr {N : ℕ} {g : Fin N → ℂ → ℂ} {ω ω' : ℕ → Fin N} :
    ∀ k, (∀ j < k, ω j = ω' j) → pComp g ω k = pComp g ω' k := by
  intro k
  induction k generalizing ω ω' with
  | zero => intro _; rfl
  | succ k ih =>
    intro h
    rw [pComp_succ, pComp_succ, h 0 (by omega)]
    congr 1
    exact ih (fun j hj => h (j + 1) (by omega))

end

namespace PertData

open MandelDim LeanEval.Dynamics.MandelbrotBoundary Set Metric Filter

noncomputable section

variable {c₀ : ℂ} {N : ℕ} {τ : Fin N → ℂ → ℂ} {n : Fin N → ℕ} {p : ℂ} {r K : ℝ}
variable (D : PertData c₀ N τ n p r K)
include D

lemma r_pos : 0 < r := by
  have h1 : r / 2 < D.r₁ := D.hr₁
  have h2 : D.r₁ < r := D.hr₁'
  linarith

lemma half_mem (c : ℂ) : p ∈ closedBall p (r / 2) := by
  rw [mem_closedBall, dist_self]; linarith [r_pos D]

lemma closedBall_s_subset : closedBall p D.s ⊆ closedBall p (r / 2) :=
  closedBall_subset_closedBall (le_of_lt D.hsr)

lemma closedBall_s_subset' : closedBall p D.s ⊆ ball p D.r₁ := by
  intro z hz
  rw [mem_closedBall] at hz
  rw [mem_ball]
  linarith [D.hsr, D.hr₁]

lemma closedBall_half_subset : closedBall p (r / 2) ⊆ ball p D.r₁ := by
  intro z hz
  rw [mem_closedBall] at hz
  rw [mem_ball]
  linarith [D.hr₁]

lemma diffOn_z (i : Fin N) {c : ℂ} (hc : c ∈ ball c₀ D.ρ) :
    DifferentiableOn ℂ (fun z => D.τc c i z) (ball p D.r₁) :=
  (D.hol i).comp ((differentiableOn_const c).prodMk differentiableOn_id)
    (fun z hz => ⟨hc, hz⟩)

lemma lips_z (i : Fin N) {c : ℂ} (hc : c ∈ ball c₀ D.ρ) :
    ∀ x ∈ closedBall p (r / 2), ∀ y ∈ closedBall p (r / 2),
      ‖D.τc c i y - D.τc c i x‖ ≤ D.θ * ‖y - x‖ := by
  intro x hx y hy
  refine Convex.norm_image_sub_le_of_norm_deriv_le (f := fun z => D.τc c i z)
    (s := closedBall p (r / 2)) (x := x) (y := y) ?_ ?_
    (convex_closedBall p (r / 2)) hx hy
  · intro z hz
    exact (D.diffOn_z i hc).differentiableAt
      (IsOpen.mem_nhds isOpen_ball (closedBall_half_subset D hz))
  · intro z hz
    exact D.deriv_le c hc i z hz

/-- The `(m+1)`-fold composite along a code sends the core into the small ball. -/
lemma pComp_mem (c : ℂ) (hc : c ∈ ball c₀ D.ρ) (ω : ℕ → Fin N) (m : ℕ) :
    ∀ x ∈ closedBall p (r / 2), pComp (D.τc c) ω (m + 1) x ∈ closedBall p D.s := by
  induction m generalizing ω with
  | zero =>
    intro x hx
    have h : pComp (D.τc c) ω (0 + 1) x = D.τc c (ω 0) x := rfl
    rw [h]
    exact D.img c hc (ω 0) hx
  | succ m ih =>
    intro x hx
    rw [pComp_succ, Function.comp_apply]
    exact D.img c hc (ω 0) (closedBall_s_subset D (ih (fun j => ω (j + 1)) x hx))

/-- Diameter estimate: the `(m+1)`-fold composite along a code contracts the core by `θ^m`. -/
lemma pComp_dist_le (c : ℂ) (hc : c ∈ ball c₀ D.ρ) (ω : ℕ → Fin N) (m : ℕ) :
    ∀ x ∈ closedBall p (r / 2), ∀ y ∈ closedBall p (r / 2),
      ‖pComp (D.τc c) ω (m + 1) x - pComp (D.τc c) ω (m + 1) y‖ ≤ 2 * D.s * D.θ ^ m := by
  induction m generalizing ω with
  | zero =>
    intro x hx y hy
    have h : ∀ w : ℂ, pComp (D.τc c) ω (0 + 1) w = D.τc c (ω 0) w := fun w => rfl
    rw [h x, h y, pow_zero, mul_one]
    have hx' := D.img c hc (ω 0) hx
    have hy' := D.img c hc (ω 0) hy
    rw [mem_closedBall] at hx' hy'
    rw [dist_eq_norm] at hx' hy'
    have hy'' : ‖p - D.τc c (ω 0) y‖ ≤ D.s := by rw [norm_sub_rev]; exact hy'
    have htri : ‖D.τc c (ω 0) x - D.τc c (ω 0) y‖
        ≤ ‖D.τc c (ω 0) x - p‖ + ‖p - D.τc c (ω 0) y‖ := by
      have h := dist_triangle (D.τc c (ω 0) x) p (D.τc c (ω 0) y)
      rw [dist_eq_norm, dist_eq_norm, dist_eq_norm] at h
      exact h
    linarith
  | succ m ih =>
    intro x hx y hy
    rw [pComp_succ, Function.comp_apply]
    have hx' : pComp (D.τc c) (fun j => ω (j + 1)) (m + 1) x ∈ closedBall p (r / 2) :=
      closedBall_s_subset D (pComp_mem D c hc (fun j => ω (j + 1)) m x hx)
    have hy' : pComp (D.τc c) (fun j => ω (j + 1)) (m + 1) y ∈ closedBall p (r / 2) :=
      closedBall_s_subset D (pComp_mem D c hc (fun j => ω (j + 1)) m y hy)
    have h1 := D.lips_z (ω 0) hc _ hy' _ hx'
    have h2 := ih (fun j => ω (j + 1)) x hx y hy
    have h3 : D.θ * ‖pComp (D.τc c) (fun j => ω (j + 1)) (m + 1) x
          - pComp (D.τc c) (fun j => ω (j + 1)) (m + 1) y‖
        ≤ D.θ * (2 * D.s * D.θ ^ m) := mul_le_mul_of_nonneg_left h2 D.hθ0
    refine le_trans h1 (le_trans h3 (le_of_eq ?_))
    rw [pow_succ]; ring

/-- Nestedness of consecutive pieces. -/
lemma pComp_image_subset (c : ℂ) (hc : c ∈ ball c₀ D.ρ) (ω : ℕ → Fin N) (k : ℕ) :
    pComp (D.τc c) ω (k + 1) '' closedBall p (r / 2)
      ⊆ pComp (D.τc c) ω k '' closedBall p (r / 2) := by
  rintro z ⟨x, hx, rfl⟩
  rw [pComp_succ_comp, Function.comp_apply]
  exact ⟨D.τc c (ω k) x, closedBall_s_subset D (D.img c hc (ω k) hx), rfl⟩

lemma pComp_image_mono (c : ℂ) (hc : c ∈ ball c₀ D.ρ) (ω : ℕ → Fin N) :
    ∀ m nn : ℕ, nn ≤ m → pComp (D.τc c) ω m '' closedBall p (r / 2)
      ⊆ pComp (D.τc c) ω nn '' closedBall p (r / 2) := by
  intro m
  induction m with
  | zero => intro nn h; interval_cases nn; exact subset_rfl
  | succ m ih =>
    intro nn hnn
    rcases eq_or_lt_of_le hnn with rfl | hlt
    · exact subset_rfl
    · exact (pComp_image_subset D c hc ω m).trans (ih nn (by omega))

/-- Two points of the same level-`m` piece are at distance at most `2 s θ^{m-1}`. -/
lemma pComp_dist_le' (c : ℂ) (hc : c ∈ ball c₀ D.ρ) (ω : ℕ → Fin N) {m nn : ℕ}
    (hm : nn ≤ m) (hn : 1 ≤ nn) :
    ‖pComp (D.τc c) ω m p - pComp (D.τc c) ω nn p‖ ≤ 2 * D.s * D.θ ^ (nn - 1) := by
  obtain ⟨l, rfl⟩ : ∃ l, m = nn + l := ⟨m - nn, by omega⟩
  have hm1 : pComp (D.τc c) ω (nn + l) p
      ∈ pComp (D.τc c) ω nn '' closedBall p (r / 2) :=
    pComp_image_mono D c hc ω (nn + l) nn (by omega) ⟨p, half_mem D c, rfl⟩
  obtain ⟨x, hx, hxeq⟩ := hm1
  obtain ⟨y, hy, hyeq⟩ :
      pComp (D.τc c) ω nn p ∈ pComp (D.τc c) ω nn '' closedBall p (r / 2) :=
    ⟨p, half_mem D c, rfl⟩
  have h := pComp_dist_le D c hc ω (nn - 1) x hx y hy
  have hnn : nn - 1 + 1 = nn := by omega
  rw [hnn] at h
  rw [← hxeq, ← hyeq]
  exact h

/-- The coding map of the perturbed IFS. -/
def coding (D : PertData c₀ N τ n p r K) (c : ℂ) (ω : ℕ → Fin N) : ℂ :=
  if h : ∃ x : ℂ, Tendsto (fun k => pComp (D.τc c) ω k p) atTop (𝓝 x) then h.choose else 0

lemma coding_exists (c : ℂ) (hc : c ∈ ball c₀ D.ρ) (ω : ℕ → Fin N) :
    ∃ x : ℂ, Tendsto (fun k => pComp (D.τc c) ω k p) atTop (𝓝 x) := by
  refine cauchySeq_tendsto_of_complete (cauchySeq_of_geometric_bound
    (show (0:ℝ) ≤ 2 * D.s by linarith [D.hs0]) D.hθ0 D.hθ1 ?_)
  intro m hm l hl
  simpa [dist_eq_norm] using pComp_dist_le' D c hc ω hl hm

lemma coding_tendsto (c : ℂ) (hc : c ∈ ball c₀ D.ρ) (ω : ℕ → Fin N) :
    Tendsto (fun k => pComp (D.τc c) ω k p) atTop (𝓝 (coding D c ω)) := by
  have h := coding_exists D c hc ω
  rw [coding, dif_pos h]
  exact h.choose_spec

lemma coding_mem (c : ℂ) (hc : c ∈ ball c₀ D.ρ) (ω : ℕ → Fin N) :
    coding D c ω ∈ closedBall p D.s := by
  refine IsClosed.mem_of_tendsto isClosed_closedBall (coding_tendsto D c hc ω) ?_
  filter_upwards [eventually_ge_atTop 1] with k hk
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  exact pComp_mem D c hc ω m p (half_mem D c)


/-- The branches of `PertData` agree with `τ` at `c = c₀` along every composite. -/
lemma pComp_base (ω : ℕ → Fin N) :
    ∀ k, ∀ x ∈ closedBall p (r / 2), pComp (D.τc c₀) ω k x = pComp τ ω k x := by
  intro k
  induction k generalizing ω with
  | zero => intro x hx; rfl
  | succ k ih =>
    intro x hx
    rw [pComp_succ, Function.comp_apply, pComp_succ, Function.comp_apply]
    have hmem : pComp (D.τc c₀) (fun j => ω (j + 1)) k x ∈ ball p D.r₁ := by
      rcases Nat.eq_zero_or_pos k with hk | hk
      · subst hk; rw [pComp_zero]; exact closedBall_half_subset D hx
      · have h2 := pComp_mem D c₀ (mem_ball_self D.hρ) (fun j => ω (j + 1)) (k - 1) x hx
        have h3 : k - 1 + 1 = k := by omega
        rw [h3] at h2
        exact closedBall_s_subset' D h2
    rw [D.base (ω 0) _ hmem, ih (fun j => ω (j + 1)) x hx]

end

end PertData

namespace PertData

open MandelDim LeanEval.Dynamics.MandelbrotBoundary Set Metric Filter

noncomputable section

variable {c₀ : ℂ} {N : ℕ} {τ : Fin N → ℂ → ℂ} {n : Fin N → ℕ} {p : ℂ} {r K : ℝ}
variable (D : PertData c₀ N τ n p r K)
include D

/-- The perturbed coding map extends the unperturbed one at `c = c₀`. -/
lemma coding_c₀ (ω : ℕ → Fin N) : coding D c₀ ω = MandelDim.codingPt τ p ω := by
  have hmem : c₀ ∈ ball c₀ D.ρ := mem_ball_self D.hρ
  have h1 : Tendsto (fun k => pComp (D.τc c₀) ω k p) atTop (𝓝 (coding D c₀ ω)) :=
    coding_tendsto D c₀ hmem ω
  have h2 : Tendsto (fun k => MandelDim.ifsComp τ ((List.range k).map ω) p) atTop
      (𝓝 (coding D c₀ ω)) := by
    refine h1.congr fun k => ?_
    rw [pComp_base D ω k p (half_mem D p), pComp_eq_ifsComp]
  exact (Tendsto.limUnder_eq h2).symm

/-- The coding map is continuous on each piece: `pComp` is continuous on the core. -/
lemma pComp_continuousOn (c : ℂ) (hc : c ∈ ball c₀ D.ρ) (ω : ℕ → Fin N) (k : ℕ) :
    ContinuousOn (pComp (D.τc c) ω k) (closedBall p (r / 2)) := by
  induction k generalizing ω with
  | zero => exact continuous_id.continuousOn
  | succ k ih =>
    rw [pComp_succ]
    refine ContinuousOn.comp (t := ball p D.r₁) ?_ (ih (fun j => ω (j + 1))) ?_
    · exact (D.diffOn_z (ω 0) hc).continuousOn
    · intro x hx
      rcases Nat.eq_zero_or_pos k with hk | hk
      · subst hk; rw [pComp_zero]; exact closedBall_half_subset D hx
      · have h2 := pComp_mem D c hc (fun j => ω (j + 1)) (k - 1) x hx
        have h3 : k - 1 + 1 = k := by omega
        rw [h3] at h2
        exact closedBall_s_subset' D h2

/-- Every coding point lies in each of its level pieces. -/
lemma coding_mem_piece (c : ℂ) (hc : c ∈ ball c₀ D.ρ) (ω : ℕ → Fin N) (k : ℕ) :
    coding D c ω ∈ pComp (D.τc c) ω k '' closedBall p (r / 2) := by
  refine IsClosed.mem_of_tendsto
    ((isCompact_closedBall p (r / 2)).image_of_continuousOn
      (pComp_continuousOn D c hc ω k)).isClosed (coding_tendsto D c hc ω) ?_
  filter_upwards [eventually_ge_atTop k] with j hj
  exact pComp_image_mono D c hc ω j k hj ⟨p, half_mem D p, rfl⟩

/-- One step of the coding map: `π c ω = τc c (ω 0) (π c (shift ω))`. -/
lemma coding_step (c : ℂ) (hc : c ∈ ball c₀ D.ρ) (ω : ℕ → Fin N) :
    coding D c ω = D.τc c (ω 0) (coding D c (fun j => ω (j + 1))) := by
  have hcw : coding D c (fun j => ω (j + 1)) ∈ ball p D.r₁ :=
    closedBall_s_subset' D (coding_mem D c hc (fun j => ω (j + 1)))
  have hcont : ContinuousAt (D.τc c (ω 0)) (coding D c (fun j => ω (j + 1))) :=
    ((D.diffOn_z (ω 0) hc).differentiableAt (IsOpen.mem_nhds isOpen_ball hcw)).continuousAt
  have h1 : Tendsto (fun k => D.τc c (ω 0) (pComp (D.τc c) (fun j => ω (j + 1)) k p)) atTop
      (𝓝 (D.τc c (ω 0) (coding D c (fun j => ω (j + 1))))) :=
    hcont.tendsto.comp (coding_tendsto D c hc (fun j => ω (j + 1)))
  have h2 : Tendsto (fun k => D.τc c (ω 0) (pComp (D.τc c) (fun j => ω (j + 1)) k p)) atTop
      (𝓝 (coding D c ω)) := by
    refine ((coding_tendsto D c hc ω).comp (tendsto_add_atTop_nat 1)).congr fun k => ?_
    show pComp (D.τc c) ω (k + 1) p
      = D.τc c (ω 0) (pComp (D.τc c) (fun j => ω (j + 1)) k p)
    rw [pComp_succ, Function.comp_apply]
  exact (tendsto_nhds_unique h1 h2).symm

/-- Equivariance of the coding map. -/
lemma coding_equivar (c : ℂ) (hc : c ∈ ball c₀ D.ρ) (ω : ℕ → Fin N) :
    (Tc c)^[n (ω 0)] (coding D c ω) = coding D c (fun j => ω (j + 1)) := by
  rw [coding_step D c hc ω]
  exact D.dyn c hc (ω 0) _ (closedBall_s_subset' D (coding_mem D c hc (fun j => ω (j + 1))))

/-- Codes sharing their first `k` letters give points in the same level-`k` piece. -/
lemma coding_dist_le (c : ℂ) (hc : c ∈ ball c₀ D.ρ) {k : ℕ} {ω ω' : ℕ → Fin N}
    (h : ∀ j < k, ω j = ω' j) :
    ‖coding D c ω - coding D c ω'‖ ≤ 2 * D.s * D.θ ^ (k - 1) := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    have h1 := coding_mem D c hc ω
    have h2 := coding_mem D c hc ω'
    rw [mem_closedBall] at h1 h2
    rw [dist_eq_norm] at h1 h2
    have htri : ‖coding D c ω - coding D c ω'‖
        ≤ ‖coding D c ω - p‖ + ‖p - coding D c ω'‖ := by
      have hh := dist_triangle (coding D c ω) p (coding D c ω')
      rwa [dist_eq_norm, dist_eq_norm, dist_eq_norm] at hh
    have h3 : ‖p - coding D c ω'‖ ≤ D.s := by rw [norm_sub_rev]; exact h2
    simp only [Nat.zero_sub, pow_zero, mul_one]
    linarith
  · have hm1 := coding_mem_piece D c hc ω k
    have hm2' : coding D c ω' ∈ pComp (D.τc c) ω k '' closedBall p (r / 2) := by
      rw [pComp_congr k h]
      exact coding_mem_piece D c hc ω' k
    obtain ⟨x, hx, hx'⟩ := hm1
    obtain ⟨y, hy, hy'⟩ := hm2'
    rw [← hx', ← hy']
    have hb := pComp_dist_le D c hc ω (k - 1) x hx y hy
    have hk' : k - 1 + 1 = k := by omega
    rw [hk'] at hb
    exact hb

/-- Uniform contraction in the code, with exponent `θ' = (1+θ)/2 < 1`. -/
lemma coding_contract (c : ℂ) (hc : c ∈ ball c₀ D.ρ) {k : ℕ} {ω ω' : ℕ → Fin N}
    (h : ∀ j < k, ω j = ω' j) :
    ‖coding D c ω - coding D c ω'‖ ≤ (2 * D.s / ((1 + D.θ) / 2)) * ((1 + D.θ) / 2) ^ k := by
  set θ' := (1 + D.θ) / 2 with hθ'def
  have hθ'0 : 0 ≤ θ' := by rw [hθ'def]; linarith [D.hθ0]
  have hθ'1 : θ' < 1 := by rw [hθ'def]; linarith [D.hθ1]
  have hθθ' : D.θ ≤ θ' := by rw [hθ'def]; linarith
  have hs : 0 ≤ 2 * D.s := by linarith [D.hs0]
  have hb := coding_dist_le D c hc h
  have hθ'pos : 0 < θ' := by rw [hθ'def]; linarith [D.hθ0]
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    have hb' : ‖coding D c ω - coding D c ω'‖ ≤ 2 * D.s := by
      simpa only [Nat.zero_sub, pow_zero, mul_one] using hb
    simp only [pow_zero, mul_one]
    rw [le_div_iff₀ hθ'pos]
    nlinarith [hb', hs, hθ'0, hθ'1]
  · have h1 : 2 * D.s * D.θ ^ (k - 1) ≤ 2 * D.s * θ' ^ (k - 1) :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ D.hθ0 hθθ' (k - 1)) hs
    have hpow : θ' ^ (k - 1) * θ' = θ' ^ k := by
      rw [← pow_succ, Nat.sub_add_cancel hk]
    have h2 : (2 * D.s / θ') * θ' ^ k = 2 * D.s * θ' ^ (k - 1) := by
      have hdiv : (2 * D.s / θ') * θ' = 2 * D.s := div_mul_cancel₀ _ (ne_of_gt hθ'pos)
      calc (2 * D.s / θ') * θ' ^ k
          = (2 * D.s / θ') * (θ' ^ (k - 1) * θ') := by rw [hpow]
        _ = ((2 * D.s / θ') * θ') * θ' ^ (k - 1) := by ring
        _ = 2 * D.s * θ' ^ (k - 1) := by rw [hdiv]
    rw [h2]
    linarith

end

end PertData

end Work.Motion
