import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.EuclideanDomain.Field
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.StrongEps.E5Aux3.LimDeriv
import Submission.Work.FTS.Galerkin.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.StrongEps.E5Aux.contDiffOn_two_of_locUnif_slots
import Submission.Work.FTS.EllipticEst.ThetaU.OpenSliceAux.pth_DzIter_eqOn_of_isOpen

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open Filter

namespace Work.FTS.StrongEps.E5Aux3

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## Reduction to *locally uniform* convergence of the jets

The target lemma is the `C²`-clause of the E5 limit extraction: the pointwise limit of the jets
(`mixed j i`, `j + i ≤ 2`) of a sequence of `C^∞` functions on the open quadrant, *together with*
a locally uniform bound on the jets of order `≤ 3`, is `C²`.

The already delivered theorem `Work.FTS.StrongEps.E5Aux.contDiffOn_two_of_locUnif_slots` proves
the corresponding statement for *locally uniform* convergence of the jets (order `≤ 2`).  So it
suffices to upgrade the pointwise convergence of the hypotheses to locally uniform convergence
on compacta.  The point is that the bound on the order-`3` jets makes the order-`≤ 2` jets
*equi-Lipschitz* on compact subsets of the quadrant (the `D_z`/`D_θ`-derivatives of a slot
`D_z^jD_θ^i u` are again slots of `u`, of order `j + i + 1`:
`∂_z(D_z^jD_θ^i u) = D_z^{j+1}D_θ^i u / z` by definition and
`∂_θ(D_z^jD_θ^i u) = D_z^jD_θ^{i+1} u / sin(2θ)` by Clairaut), and equi-Lipschitz plus pointwise
convergence on a compact set gives uniform convergence. -/

/-- The operator norm of `clmPair (a, b)` (the linear functional `(x,y) ↦ ax + by` on
`ℝ × ℝ`) is at most `|a| + |b|`. -/
theorem norm_clmPair_le (a b : ℝ) :
    ‖Work.FTS.StrongEps.E5Aux.clmPair (a, b)‖ ≤ |a| + |b| := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
  have h1 : |v.1| ≤ ‖v‖ := by simpa [Real.norm_eq_abs] using norm_fst_le v
  have h2 : |v.2| ≤ ‖v‖ := by simpa [Real.norm_eq_abs] using norm_snd_le v
  rw [Work.FTS.StrongEps.E5Aux.clmPair_apply]
  calc |a * v.1 + b * v.2| ≤ |a * v.1| + |b * v.2| := abs_add_le _ _
    _ = |a| * |v.1| + |b| * |v.2| := by rw [abs_mul, abs_mul]
    _ ≤ |a| * ‖v‖ + |b| * ‖v‖ := by gcongr
    _ = (|a| + |b|) * ‖v‖ := by ring

/-- `D_z^j` of a product with a function of `θ` alone: the factor comes out. -/
theorem DzIter_theta_mul (c : ℝ → ℝ) (w : ℝ → ℝ → ℝ) (j : ℕ) :
    Work.Spaces.DzIter j (fun z θ => c θ * w z θ)
      = fun z θ => c θ * Work.Spaces.DzIter j w z θ := by
  induction j with
  | zero => rfl
  | succ j ih =>
      rw [Work.Spaces.DzIter_succ, ih, Work.Spaces.DzIter_succ]
      funext z θ
      show z * Work.Spaces.pz (fun z θ => c θ * Work.Spaces.DzIter j w z θ) z θ
        = c θ * (z * Work.Spaces.pz (Work.Spaces.DzIter j w) z θ)
      show z * deriv (fun z' => c θ * Work.Spaces.DzIter j w z' θ) z
        = c θ * (z * deriv (fun z' => Work.Spaces.DzIter j w z' θ) z)
      rw [deriv_const_mul_field]
      ring

/-- The slot `D_z^jD_θ^{i+1} u` written through `D_z^j(∂_θ D_θ^i u)`. -/
theorem mixed_succ_right_eq (u : ℝ → ℝ → ℝ) (j i : ℕ) :
    Work.Spaces.mixed j (i + 1) u
      = fun z θ => Real.sin (2 * θ)
          * Work.Spaces.DzIter j (Work.Spaces.pth (Work.Spaces.DthIter i u)) z θ := by
  have h1 : Work.Spaces.mixed j (i + 1) u
      = Work.Spaces.DzIter j (fun z θ => Real.sin (2 * θ)
          * Work.Spaces.pth (Work.Spaces.DthIter i u) z θ) := rfl
  rw [h1, DzIter_theta_mul (fun θ => Real.sin (2 * θ))
    (Work.Spaces.pth (Work.Spaces.DthIter i u)) j]

/-- **`∂_θ` of a slot.**  On the open quadrant, the angular derivative of the slot
`D_z^jD_θ^i u` is the next slot `D_z^jD_θ^{i+1} u` divided by `sin(2θ)`. -/
theorem pth_mixed_eq {u : ℝ → ℝ → ℝ} (hsm : Work.FTS.EllipticEst.SmoothOpen u) (j i : ℕ) :
    ∀ p ∈ Work.FTS.EllipticEst.Q0,
      Work.Spaces.pth (Work.Spaces.mixed j i u) p.1 p.2
        = Work.Spaces.mixed j (i + 1) u p.1 p.2 / Real.sin (2 * p.2) := by
  have hDth : ∀ m : ℕ, ContDiffOn ℝ m (Function.uncurry (Work.Spaces.DthIter i u))
      Work.FTS.EllipticEst.Q0 := fun m => (hsm.DthIter i).forall m
  intro p hp
  have hsin : Real.sin (2 * p.2) ≠ 0 := by
    have hθ := (Work.FTS.EllipticEst.mem_Q0.mp hp).2
    exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
      (by linarith [hθ.2, Real.pi_pos]))
  have h1 : Work.Spaces.pth (Work.Spaces.mixed j i u) p.1 p.2
      = Work.Spaces.DzIter j (Work.Spaces.pth (Work.Spaces.DthIter i u)) p.1 p.2 :=
    Work.FTS.EllipticEst.ThetaU.OpenSliceAux.pth_DzIter_eqOn_of_isOpen
      Work.FTS.EllipticEst.isOpen_Q0 hDth j hp
  have h2 : Work.Spaces.mixed j (i + 1) u p.1 p.2
      = Real.sin (2 * p.2)
          * Work.Spaces.DzIter j (Work.Spaces.pth (Work.Spaces.DthIter i u)) p.1 p.2 := by
    rw [mixed_succ_right_eq]
  rw [h1, h2, mul_div_cancel_left₀ _ hsin]

/-- **Equi-Lipschitz bound for the slots of order `≤ 2`.**  On a compact convex subset of the
open quadrant, the order-`≤ 3` jet bound of the hypotheses bounds the derivative of every slot
of order `≤ 2`, uniformly in the index `n`; the mean value inequality then makes the slots
uniformly Lipschitz. -/
theorem slot_lipschitz {g : ℕ → Work.FTS.Galerkin.Fn}
    (hsm : ∀ n : ℕ, Work.FTS.EllipticEst.SmoothOpen (g n))
    (hbnd : ∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ Work.FTS.EllipticEst.Q0 → ∃ C : ℝ, 0 ≤ C ∧
      ∀ n : ℕ, ∀ (j i : ℕ), j + i ≤ 3 → ∀ z θ : ℝ, (z, θ) ∈ K →
        |Work.Spaces.mixed j i (g n) z θ| ≤ C)
    (j i : ℕ) (hji : j + i ≤ 2) {K : Set (ℝ × ℝ)} (hK : IsCompact K) (hKc : Convex ℝ K)
    (hne : K.Nonempty) (hKQ : K ⊆ Work.FTS.EllipticEst.Q0) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ n : ℕ, ∀ x ∈ K, ∀ y ∈ K,
      |Work.Spaces.mixed j i (g n) x.1 x.2 - Work.Spaces.mixed j i (g n) y.1 y.2|
        ≤ M * dist x y := by
  obtain ⟨C, hC0, hC⟩ := hbnd K hK hKQ
  obtain ⟨x₀, hx₀K, hx₀min⟩ := hK.exists_isMinOn hne (continuous_fst.continuousOn)
  obtain ⟨y₀, hy₀K, hy₀min⟩ := hK.exists_isMinOn hne
    ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn)
  have hx₀pos : 0 < x₀.1 := (Work.FTS.EllipticEst.mem_Q0.mp (hKQ hx₀K)).1
  have hs₀pos : 0 < Real.sin (2 * y₀.2) := by
    have hθ := (Work.FTS.EllipticEst.mem_Q0.mp (hKQ hy₀K)).2
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
      (by linarith [hθ.2, Real.pi_pos])
  refine ⟨C / x₀.1 + C / Real.sin (2 * y₀.2), by positivity, ?_⟩
  intro n x hx y hy
  have hbound : ∀ q ∈ K,
      ‖fderiv ℝ (Function.uncurry (Work.Spaces.mixed j i (g n))) q‖
        ≤ C / x₀.1 + C / Real.sin (2 * y₀.2) := by
    intro q hq
    have hqQ : q ∈ Work.FTS.EllipticEst.Q0 := hKQ hq
    have hzq : 0 < q.1 := (Work.FTS.EllipticEst.mem_Q0.mp hqQ).1
    have hsq : 0 < Real.sin (2 * q.2) := by
      have hθ := (Work.FTS.EllipticEst.mem_Q0.mp hqQ).2
      exact Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
        (by linarith [hθ.2, Real.pi_pos])
    have hdiffq : DifferentiableAt ℝ (Function.uncurry (Work.Spaces.mixed j i (g n))) q :=
      (((hsm n).mixed j i).forall 2).differentiableOn (by norm_num) |>.differentiableAt
        (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hqQ)
    have hmem : (q.1, q.2) ∈ K := by simpa using hq
    have hzm : |Work.Spaces.pz (Work.Spaces.mixed j i (g n)) q.1 q.2| ≤ C / x₀.1 := by
      have hdecomp : Work.Spaces.mixed (j + 1) i (g n) q.1 q.2
          = q.1 * Work.Spaces.pz (Work.Spaces.mixed j i (g n)) q.1 q.2 := rfl
      have hval : Work.Spaces.mixed (j + 1) i (g n) q.1 q.2 / q.1
          = Work.Spaces.pz (Work.Spaces.mixed j i (g n)) q.1 q.2 := by
        rw [hdecomp, mul_div_cancel_left₀ _ (ne_of_gt hzq)]
      rw [← hval, abs_div, abs_of_pos hzq]
      exact div_le_div₀ hC0 (hC n (j + 1) i (by omega) q.1 q.2 hmem) hx₀pos (hx₀min hq)
    have hthm : |Work.Spaces.pth (Work.Spaces.mixed j i (g n)) q.1 q.2|
        ≤ C / Real.sin (2 * y₀.2) := by
      rw [pth_mixed_eq (hsm n) j i q hqQ, abs_div, abs_of_pos hsq]
      exact div_le_div₀ hC0 (hC n j (i + 1) (by omega) q.1 q.2 hmem) hs₀pos (hy₀min hq)
    rw [Work.FTS.StrongEps.E5Aux.fderiv_uncurry_eq_clmPair hdiffq]
    exact le_trans (norm_clmPair_le _ _) (by linarith)
  have hdiff : ∀ q ∈ K,
      DifferentiableAt ℝ (Function.uncurry (Work.Spaces.mixed j i (g n))) q := fun q hq =>
    (((hsm n).mixed j i).forall 2).differentiableOn (by norm_num) |>.differentiableAt
      (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds (hKQ hq))
  have hmvt := hKc.norm_image_sub_le_of_norm_fderiv_le hdiff hbound hx hy
  have hgoal : |Work.Spaces.mixed j i (g n) x.1 x.2
      - Work.Spaces.mixed j i (g n) y.1 y.2| ≤
      (C / x₀.1 + C / Real.sin (2 * y₀.2)) * dist x y := by
    have h := hmvt
    rw [Real.norm_eq_abs] at h
    rw [abs_sub_comm] at h
    rw [← dist_eq_norm, dist_comm] at h
    exact h
  exact hgoal

/-- **Pointwise limits of uniformly Lipschitz families are Lipschitz** (same constant). -/
theorem lipschitz_of_tendsto {F : ℕ → ℝ × ℝ → ℝ} {f : ℝ × ℝ → ℝ} {s : Set (ℝ × ℝ)} {M : ℝ}
    (hLip : ∀ n : ℕ, ∀ x ∈ s, ∀ y ∈ s, |F n x - F n y| ≤ M * dist x y)
    (hconv : ∀ x ∈ s, Tendsto (fun n => F n x) atTop (𝓝 (f x))) :
    ∀ x ∈ s, ∀ y ∈ s, |f x - f y| ≤ M * dist x y := by
  intro x hx y hy
  have h1 : Tendsto (fun n => |F n x - F n y|) atTop (𝓝 |f x - f y|) :=
    (continuous_abs.tendsto _).comp ((hconv x hx).sub (hconv y hy))
  exact le_of_tendsto h1 (Eventually.of_forall fun n => hLip n x hx y hy)

/-- **Pointwise convergence plus a uniform Lipschitz bound gives uniform convergence** on a
compact set. -/
theorem tendstoUniformlyOn_of_tendsto_of_lipschitz {F : ℕ → ℝ × ℝ → ℝ} {f : ℝ × ℝ → ℝ}
    {s : Set (ℝ × ℝ)} {M : ℝ} (hM : 0 ≤ M) (hsc : IsCompact s)
    (hLip : ∀ n : ℕ, ∀ x ∈ s, ∀ y ∈ s, |F n x - F n y| ≤ M * dist x y)
    (hconv : ∀ x ∈ s, Tendsto (fun n => F n x) atTop (𝓝 (f x))) :
    TendstoUniformlyOn F f atTop s := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hLipf := lipschitz_of_tendsto hLip hconv
  obtain ⟨δ, hδ0, hδ⟩ : ∃ δ : ℝ, 0 < δ ∧ 4 * M * δ < ε := by
    rcases eq_or_lt_of_le hM with hM0 | hM0
    · exact ⟨1, one_pos, by rw [← hM0]; linarith⟩
    · refine ⟨ε / (8 * M), by positivity, ?_⟩
      have h8 : (0 : ℝ) < 8 * M := by linarith
      have harith : 4 * M * (ε / (8 * M)) = ε / 2 := by field_simp; ring
      rw [harith]; linarith
  have hcov : s ⊆ ⋃ p ∈ s, Metric.ball p δ := fun x hx =>
    Set.mem_iUnion.mpr ⟨x, Set.mem_iUnion.mpr ⟨hx, Metric.mem_ball_self hδ0⟩⟩
  obtain ⟨b', hb'sub, hb'fin, hb'cov⟩ :=
    hsc.elim_finite_subcover_image (b := s) (c := fun p => Metric.ball p δ)
      (fun p _ => Metric.isOpen_ball) hcov
  have hev : ∀ᶠ n in atTop, ∀ p ∈ hb'fin.toFinset, dist (f p) (F n p) < ε / 2 :=
    (eventually_all_finset _).mpr fun p hp => by
      have hp' : p ∈ s := hb'sub (hb'fin.mem_toFinset.mp hp)
      have ht := hconv p hp'
      rw [Metric.tendsto_atTop] at ht
      obtain ⟨N, hN⟩ := ht (ε / 2) (by linarith)
      exact Filter.eventually_atTop.2 ⟨N, fun n hn => by simpa [dist_comm] using hN n hn⟩
  filter_upwards [hev] with n hn
  intro x hx
  have hxc := hb'cov hx
  obtain ⟨p, hpb', hxp⟩ : ∃ p ∈ b', x ∈ Metric.ball p δ := by
    obtain ⟨p, h2⟩ := Set.mem_iUnion.mp hxc
    obtain ⟨hpb', hxp⟩ := Set.mem_iUnion.mp h2
    exact ⟨p, hpb', hxp⟩
  have hps : p ∈ s := hb'sub hpb'
  have hxp' : dist x p < δ := Metric.mem_ball.mp hxp
  have h1 : dist (f x) (f p) ≤ M * dist x p := by
    rw [Real.dist_eq]; exact hLipf x hx p hps
  have h2 : dist (f p) (F n p) < ε / 2 := hn p (hb'fin.mem_toFinset.mpr hpb')
  have h3 : dist (F n p) (F n x) ≤ M * dist x p := by
    rw [Real.dist_eq, abs_sub_comm]
    exact hLip n x hx p hps
  have h4 : M * dist x p ≤ M * δ := mul_le_mul_of_nonneg_left (le_of_lt hxp') hM
  calc dist (f x) (F n x) ≤ dist (f x) (f p) + dist (f p) (F n p) + dist (F n p) (F n x) :=
        dist_triangle4 (f x) (f p) (F n p) (F n x)
    _ ≤ M * dist x p + ε / 2 + M * dist x p := by linarith
    _ < ε := by linarith

/-- **Uniform convergence of a slot on a compact subset of the quadrant.**  This is the
upgrade of the pointwise hypothesis `hconv` used by
`Work.FTS.StrongEps.E5Aux.contDiffOn_two_of_locUnif_slots`. -/
theorem tendstoUniformlyOn_slot {g : ℕ → Work.FTS.Galerkin.Fn} {G : Work.FTS.Galerkin.Fn}
    (hsm : ∀ n : ℕ, Work.FTS.EllipticEst.SmoothOpen (g n))
    (hconv : ∀ (j i : ℕ), j + i ≤ 2 → ∀ p ∈ Work.FTS.EllipticEst.Q0,
      Tendsto (fun n : ℕ => Work.Spaces.mixed j i (g n) p.1 p.2) atTop
        (𝓝 (Work.Spaces.mixed j i G p.1 p.2)))
    (hbnd : ∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ Work.FTS.EllipticEst.Q0 → ∃ C : ℝ, 0 ≤ C ∧
      ∀ n : ℕ, ∀ (j i : ℕ), j + i ≤ 3 → ∀ z θ : ℝ, (z, θ) ∈ K →
        |Work.Spaces.mixed j i (g n) z θ| ≤ C)
    (j i : ℕ) (hji : j + i ≤ 2) {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (hKQ : K ⊆ Work.FTS.EllipticEst.Q0) :
    TendstoUniformlyOn (fun n : ℕ => fun p : ℝ × ℝ => Work.Spaces.mixed j i (g n) p.1 p.2)
      (fun p : ℝ × ℝ => Work.Spaces.mixed j i G p.1 p.2) atTop K := by
  classical
  rcases K.eq_empty_or_nonempty with rfl | hne
  · rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    exact Eventually.of_forall fun n x hx => absurd hx (by simp)
  · have hex : ∀ p ∈ K, ∃ η : ℝ, 0 < η ∧ Metric.closedBall p (2 * η) ⊆
        Work.FTS.EllipticEst.Q0 := by
      intro p hp
      obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp Work.FTS.EllipticEst.isOpen_Q0 p (hKQ hp)
      refine ⟨r / 4, by linarith, ?_⟩
      have h2 : 2 * (r / 4) = r / 2 := by ring
      rw [h2]
      intro x hx
      exact hsub (Metric.closedBall_subset_ball (by linarith) hx)
    have hex2 : ∀ p : ℝ × ℝ, ∃ η : ℝ,
        p ∈ K → 0 < η ∧ Metric.closedBall p (2 * η) ⊆ Work.FTS.EllipticEst.Q0 := by
      intro p
      by_cases hp : p ∈ K
      · obtain ⟨η, h1, h2⟩ := hex p hp
        exact ⟨η, fun _ => ⟨h1, h2⟩⟩
      · exact ⟨1, fun h => absurd h hp⟩
    let η : ℝ × ℝ → ℝ := fun p => Classical.choose (hex2 p)
    have hηspec : ∀ p : ℝ × ℝ,
        p ∈ K → 0 < η p ∧ Metric.closedBall p (2 * η p) ⊆ Work.FTS.EllipticEst.Q0 :=
      fun p => Classical.choose_spec (hex2 p)
    have hηpos : ∀ p ∈ K, 0 < η p := fun p hp => (hηspec p hp).1
    have hηsub : ∀ p ∈ K, Metric.closedBall p (η p) ⊆ Work.FTS.EllipticEst.Q0 := by
      intro p hp
      have hspec := (hηspec p hp).2
      have hle : η p ≤ 2 * η p := by have := hηpos p hp; linarith
      intro x hx
      exact hspec (Metric.closedBall_subset_closedBall hle hx)
    have hcov : K ⊆ ⋃ p ∈ K, Metric.ball p (η p) := fun x hx =>
      Set.mem_iUnion.mpr ⟨x, Set.mem_iUnion.mpr ⟨hx, Metric.mem_ball_self (hηpos x hx)⟩⟩
    obtain ⟨b', hb'sub, hb'fin, hb'cov⟩ :=
      hK.elim_finite_subcover_image (b := K) (c := fun p => Metric.ball p (η p))
        (fun p _ => Metric.isOpen_ball) hcov
    have hball : ∀ p ∈ b', TendstoUniformlyOn
        (fun n : ℕ => fun q : ℝ × ℝ => Work.Spaces.mixed j i (g n) q.1 q.2)
        (fun q : ℝ × ℝ => Work.Spaces.mixed j i G q.1 q.2) atTop
        (Metric.closedBall p (η p)) := by
      intro p hp
      have hpK : p ∈ K := hb'sub hp
      have hclQ : Metric.closedBall p (η p) ⊆ Work.FTS.EllipticEst.Q0 := hηsub p hpK
      have hcmp : IsCompact (Metric.closedBall p (η p)) := isCompact_closedBall p (η p)
      have hcvx : Convex ℝ (Metric.closedBall p (η p)) := convex_closedBall p (η p)
      have hne' : (Metric.closedBall p (η p)).Nonempty :=
        ⟨p, Metric.mem_closedBall_self (le_of_lt (hηpos p hpK))⟩
      obtain ⟨M, hM0, hM⟩ := slot_lipschitz hsm hbnd j i hji hcmp hcvx hne' hclQ
      exact tendstoUniformlyOn_of_tendsto_of_lipschitz hM0 hcmp hM
        (fun q hq => hconv j i hji q (hclQ hq))
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have hev : ∀ᶠ n in atTop, ∀ p ∈ hb'fin.toFinset, ∀ q ∈ Metric.closedBall p (η p),
        dist (Work.Spaces.mixed j i G q.1 q.2) (Work.Spaces.mixed j i (g n) q.1 q.2) < ε :=
      (eventually_all_finset _).mpr fun p hp =>
        (Metric.tendstoUniformlyOn_iff.mp (hball p (hb'fin.mem_toFinset.mp hp))) ε hε
    filter_upwards [hev] with n hn
    intro x hx
    obtain ⟨p, hpb', hxball⟩ : ∃ p ∈ b', x ∈ Metric.ball p (η p) := by
      obtain ⟨p, h2⟩ := Set.mem_iUnion.mp (hb'cov hx)
      obtain ⟨hpb', hxball⟩ := Set.mem_iUnion.mp h2
      exact ⟨p, hpb', hxball⟩
    exact hn p (hb'fin.mem_toFinset.mpr hpb') x (Metric.ball_subset_closedBall hxball)

theorem contDiffOn_two_of_jetLim {g : ℕ → Work.FTS.Galerkin.Fn} {G : Work.FTS.Galerkin.Fn}
    (hsm : ∀ n : ℕ, Work.FTS.EllipticEst.SmoothOpen (g n))
    (hconv : ∀ (j i : ℕ), j + i ≤ 2 → ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      Filter.Tendsto (fun n : ℕ => Work.Spaces.mixed j i (g n) z θ) Filter.atTop
        (nhds (Work.Spaces.mixed j i G z θ)))
    (hbnd : ∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ Work.FTS.EllipticEst.Q0 → ∃ C : ℝ, 0 ≤ C ∧
      ∀ n : ℕ, ∀ (j i : ℕ), j + i ≤ 3 → ∀ z θ : ℝ, (z, θ) ∈ K →
        |Work.Spaces.mixed j i (g n) z θ| ≤ C) :
    ContDiffOn ℝ 2 (Function.uncurry G) Work.FTS.EllipticEst.Q0 := by
  refine Work.FTS.StrongEps.E5Aux.contDiffOn_two_of_locUnif_slots (F := g) (f := G) ?_ ?_
  · intro n
    exact (hsm n).forall 2
  · intro j i hji K hK hKQ
    exact tendstoUniformlyOn_slot hsm (fun j' i' hji' p hp => hconv j' i' hji' p.1 p.2 hp)
      hbnd j i hji hK hKQ

end Work.FTS.StrongEps.E5Aux3
