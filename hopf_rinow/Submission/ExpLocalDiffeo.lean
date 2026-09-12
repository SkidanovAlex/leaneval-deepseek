import Mathlib

/-!
# Local diffeomorphism structure from a two-point expansion estimate

Task: prove the final theorem `exp_local_diffeomorphism_of_estimates` (replace the placeholder).

A map `exp : E → E` (here: a geodesic exponential map) satisfies `exp 0 = x₀` and the
**two-point expansion estimate** on the closed ball of radius `ρ > 0`:

    ‖(exp u - exp v) - (u - v)‖ ≤ κ * ‖u - v‖     for all u,v ∈ closedBall 0 ρ,

with `0 ≤ κ < 1`.  (Here `κ` is a small constant, obtained by choosing `ρ` small; the estimate
expresses that `exp` is uniformly close to the translation `v ↦ x₀ + v`.)

From this alone derive that `exp` is a local diffeomorphism structure at `0`:

* injectivity on `ball 0 ρ`:  if `exp u = exp v` then `‖u-v‖ ≤ κ‖u-v‖`, hence `u = v`;
* a neighbourhood of `x₀` is covered: for `y` with `‖y - x₀‖ < (1 - κ) ρ`, the map
  `v ↦ (y - x₀) - ((exp v - x₀) - v)` is a contraction on `closedBall 0 ρ`
  (with constant `κ < 1`, using `‖(exp v - x₀) - v‖ ≤ κ‖v‖` from the estimate with `u = v, w = 0`),
  so Banach's fixed point theorem gives `v ∈ ball 0 ρ` with `exp v = y`;
* continuity of `exp` on `ball 0 ρ`: from the estimate, `exp` is `(1+κ)`-Lipschitz there.

Suggested witnesses: `U := ball 0 ρ` and `V := exp '' U` (the image).  Then `MapsTo`/`SurjOn`
are trivial, and `V ∈ 𝓝 x₀` follows from `ball x₀ ((1-κ)ρ) ⊆ exp '' (ball 0 ρ)`.  The inverse
`inv` is obtained by `Classical.choose` from surjectivity, using injectivity for uniqueness.

## Available Mathlib API

* Contraction: `ContractingWith` (in `Mathlib.Topology.MetricSpace.Contracting`);
  `ContractingWith.exists_fixedPoint (hf : ContractingWith K f) (x : α) (hx : edist x (f x) ≠ ∞)`
  returns `∃ y, IsFixedPt f y`.  To apply it to a self-map of `closedBall 0 ρ`, work with the
  subtype `{v : E // v ∈ closedBall 0 ρ}` (a complete space: the typeclass
  `IsClosed.completeSpace_coe` provides `CompleteSpace` for subtypes of closed sets, and
  `closedBall` is closed; the whole space `E` is complete by hypothesis).
  `LipschitzWith.of_dist_le_mul` converts a metric estimate into `LipschitzWith`.
* Membership: `mem_closedBall`, `mem_ball`, `dist_eq_norm`, `Metric.closedBall_subset_closedBall`.
* Norms: `norm_sub_le`, `norm_sub_rev`, `norm_sub_le_norm_sub_add_norm_sub`.
* Neighborhood: `Metric.ball_mem_nhds`, or `mem_nhds_iff` with the open ball.

Do NOT change the statement.  You may add helper lemmas.  No placeholders/axioms may remain.
-/

open Set Metric Filter
open scoped Topology

namespace Submission.ExpLocalDiffeo

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Covering: the open ball around `x₀` of radius `(1 - κ)ρ` is contained in `exp '' ball 0 ρ`. -/
lemma exp_ball_subset_image (exp : E → E) (x₀ : E) (ρ κ : ℝ)
    (hρ : 0 < ρ) (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) (hexp0 : exp 0 = x₀)
    (hest : ∀ ⦃u v : E⦄, u ∈ closedBall (0:E) ρ → v ∈ closedBall (0:E) ρ →
      ‖(exp u - exp v) - (u - v)‖ ≤ κ * ‖u - v‖) :
    ball x₀ ((1 - κ) * ρ) ⊆ exp '' ball (0:E) ρ := by
  intro y hy
  have hyρ : ‖y - x₀‖ < (1 - κ) * ρ := by
    simpa [dist_eq_norm] using hy
  let T : E → E := fun v => y - exp v + v
  have hT0 : T 0 = y - x₀ := by
    simp [T, hexp0]
  have h0B : (0 : E) ∈ closedBall (0:E) ρ := by
    simpa [dist_eq_norm] using (le_of_lt hρ)
  have hTmem : ∀ v : E, v ∈ closedBall (0:E) ρ → T v ∈ ball (0:E) ρ := by
    intro v hv
    have hvρ : ‖v‖ ≤ ρ := by simpa [dist_eq_norm] using hv
    have hc0 : ‖T v - T 0‖ ≤ κ * ‖v‖ := by
      have hd : T v - T 0 = (v - 0) - (exp v - exp 0) := by
        simp [T]
        abel
      have hest01 : ‖(exp v - exp 0) - (v - 0)‖ ≤ κ * ‖v - 0‖ := by
        exact hest hv h0B
      calc
        ‖T v - T 0‖ = ‖(exp v - exp 0) - (v - 0)‖ := by
          rw [hd]
          exact norm_sub_rev (v - 0) (exp v - exp 0)
        _ ≤ κ * ‖v - 0‖ := hest01
        _ = κ * ‖v‖ := by simp
    have hnorm : ‖T v‖ ≤ κ * ‖v‖ + ‖y - x₀‖ := by
      calc
        ‖T v‖ = ‖(T v - T 0) + T 0‖ := by simp
        _ ≤ ‖T v - T 0‖ + ‖T 0‖ := norm_add_le _ _
        _ ≤ κ * ‖v‖ + ‖T 0‖ := by
          exact add_le_add hc0 le_rfl
        _ = κ * ‖v‖ + ‖y - x₀‖ := by rw [hT0]
    have hstrict : ‖T v‖ < ρ := by
      nlinarith [hnorm, hyρ, hvρ, hκ0, mul_le_mul_of_nonneg_left hvρ hκ0]
    simpa [dist_eq_norm] using hstrict
  have hsf : MapsTo T (closedBall (0:E) ρ) (closedBall (0:E) ρ) := by
    intro v hv
    exact ball_subset_closedBall (hTmem v hv)
  let κₙ : NNReal := ⟨κ, hκ0⟩
  have hcT : ∀ u v : E, u ∈ closedBall (0:E) ρ → v ∈ closedBall (0:E) ρ →
      ‖T u - T v‖ ≤ κ * ‖u - v‖ := by
    intro u v hu hv
    have hd : T u - T v = (u - v) - (exp u - exp v) := by
      simp [T]
      abel
    calc
      ‖T u - T v‖ = ‖(exp u - exp v) - (u - v)‖ := by
        rw [hd]
        exact norm_sub_rev (u - v) (exp u - exp v)
      _ ≤ κ * ‖u - v‖ := hest hu hv
  have hκ1nn : κₙ < 1 := by
    exact_mod_cast hκ1
  have hlip : LipschitzWith κₙ (hsf.restrict T (closedBall (0:E) ρ) (closedBall (0:E) ρ)) := by
    refine LipschitzWith.of_dist_le_mul ?_
    intro u v
    change dist (T (u : E)) (T (v : E)) ≤ (κₙ : ℝ) * dist (u : E) (v : E)
    rw [dist_eq_norm, dist_eq_norm]
    exact hcT u.1 v.1 u.2 v.2
  have hf : ContractingWith κₙ (hsf.restrict T (closedBall (0:E) ρ) (closedBall (0:E) ρ)) := ⟨hκ1nn, hlip⟩
  obtain ⟨w, hwB, hwfix, _⟩ :=
    ContractingWith.exists_fixedPoint' (s := closedBall (0:E) ρ) (f := T) (x := (0 : E))
      ((Metric.isClosed_closedBall : IsClosed (closedBall (0:E) ρ)).isComplete) hsf hf h0B
      (edist_ne_top (0 : E) (T 0))
  have hwball : w ∈ ball (0:E) ρ := by
    have hb := hTmem w hwB
    have hb' : ‖T w‖ < ρ := by simpa [dist_eq_norm] using hb
    have hwfixT : T w = w := by simpa [Function.IsFixedPt] using hwfix
    have hwstrict : ‖w‖ < ρ := by simpa [hwfixT] using hb'
    simpa [dist_eq_norm] using hwstrict
  have hwexp : exp w = y := by
    have hwfix' : y - exp w + w = w := hwfix
    have hsub : y - exp w = 0 := by
      calc
        y - exp w = (y - exp w + w) - w := by abel
        _ = w - w := by rw [hwfix']
        _ = 0 := by abel
    exact (sub_eq_zero.mp hsub).symm
  exact ⟨w, hwball, hwexp⟩

/-- A map with `exp 0 = x₀` whose deviation from the translation `v ↦ x₀ + v` is
`κ`-Lipschitz on the closed ball of radius `ρ` (`0 ≤ κ < 1`) restricts to a bijection between
a neighbourhood of `0` and a neighbourhood of `x₀`. -/

theorem exp_local_diffeomorphism_of_estimates (exp : E → E) (x₀ : E) (ρ κ : ℝ)
    (hρ : 0 < ρ) (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) (hexp0 : exp 0 = x₀)
    (hest : ∀ ⦃u v : E⦄, u ∈ closedBall 0 ρ → v ∈ closedBall 0 ρ →
      ‖(exp u - exp v) - (u - v)‖ ≤ κ * ‖u - v‖) :
    ∃ U ∈ 𝓝 (0 : E), ∃ V ∈ 𝓝 x₀,
      Set.MapsTo exp U V ∧ Function.Injective (fun v : U => exp v.1) ∧
      Set.SurjOn exp U V ∧ ContinuousOn exp U ∧
      ∃ inv : E → E, ∀ y ∈ V, inv y ∈ U ∧ exp (inv y) = y ∧
        ∀ v ∈ U, inv (exp v) = v := by

  classical
  let U : Set E := ball (0:E) ρ
  let V : Set E := exp '' U
  have hU : U ∈ 𝓝 (0 : E) := by
    dsimp [U]
    exact Metric.ball_mem_nhds 0 hρ
  have hcover : ball x₀ ((1 - κ) * ρ) ⊆ exp '' (ball (0:E) ρ) :=
    exp_ball_subset_image exp x₀ ρ κ hρ hκ0 hκ1 hexp0 hest
  have hpos : 0 < (1 - κ) * ρ := mul_pos (by linarith) hρ
  have hV : V ∈ 𝓝 x₀ := by
    dsimp [V, U]
    exact mem_of_superset (Metric.ball_mem_nhds x₀ hpos) hcover
  have hmap : Set.MapsTo exp U V := by
    intro x hx
    exact ⟨x, hx, rfl⟩
  have hinj : Function.Injective (fun v : U => exp v.1) := by
    intro u v huv
    apply Subtype.ext
    have huB : (u : E) ∈ closedBall (0:E) ρ := ball_subset_closedBall u.2
    have hvB : (v : E) ∈ closedBall (0:E) ρ := ball_subset_closedBall v.2
    have hneg : (exp (u:E) - exp (v:E)) - ((u:E) - (v:E)) = -((u:E) - (v:E)) := by
      simp [huv]
    have hk : ‖(u : E) - (v : E)‖ ≤ κ * ‖(u : E) - (v : E)‖ := by
      calc
        ‖(u : E) - (v : E)‖ = ‖-((u : E) - (v : E))‖ := by rw [norm_neg]
        _ = ‖(exp (u:E) - exp (v:E)) - ((u:E) - (v:E))‖ := by rw [hneg]
        _ ≤ κ * ‖(u : E) - (v : E)‖ := hest huB hvB
    have hnorm0 : ‖(u : E) - (v : E)‖ = 0 := by
      have hle : (1 - κ) * ‖(u : E) - (v : E)‖ ≤ 0 := by nlinarith [hk]
      nlinarith [hle, hκ1, norm_nonneg ((u : E) - (v : E))]
    exact sub_eq_zero.mp (norm_eq_zero.mp hnorm0)
  have hsurj : Set.SurjOn exp U V := by
    intro y hy
    exact hy
  have hcont : ContinuousOn exp U := by
    rw [Metric.continuousOn_iff]
    intro b hb ε hε
    have h1κ : 0 < 1 + κ := by nlinarith
    refine ⟨ε / (1 + κ), div_pos hε h1κ, ?_⟩
    intro a ha hdist
    have haB : a ∈ closedBall (0:E) ρ := ball_subset_closedBall ha
    have hbB : b ∈ closedBall (0:E) ρ := ball_subset_closedBall hb
    have hest' : ‖(exp a - exp b) - (a - b)‖ ≤ κ * ‖a - b‖ := hest haB hbB
    have hlip : ‖exp a - exp b‖ ≤ (1 + κ) * ‖a - b‖ := by
      calc
        ‖exp a - exp b‖ = ‖((exp a - exp b) - (a - b)) + (a - b)‖ := by
          rw [sub_add_cancel]
        _ ≤ ‖(exp a - exp b) - (a - b)‖ + ‖a - b‖ := norm_add_le _ _
        _ ≤ κ * ‖a - b‖ + ‖a - b‖ := add_le_add hest' le_rfl
        _ = (1 + κ) * ‖a - b‖ := by ring
    have hdist' : ‖a - b‖ < ε / (1 + κ) := by
      simpa [dist_eq_norm] using hdist
    have hmain : (1 + κ) * ‖a - b‖ < ε := by
      have hmult : ‖a - b‖ * (1 + κ) < ε := (lt_div_iff₀ h1κ).mp hdist'
      nlinarith
    calc
      dist (exp a) (exp b) = ‖exp a - exp b‖ := dist_eq_norm _ _
      _ ≤ (1 + κ) * ‖a - b‖ := hlip
      _ < ε := hmain
  -- inverse
  let inv : E → E := fun y => if h : y ∈ V then Classical.choose h else 0
  have hsurj' : ∀ y : E, y ∈ V → ∃ x, x ∈ U ∧ exp x = y := by
    intro y hy
    exact hy
  have hinv1 : ∀ y : E, y ∈ V → inv y ∈ U ∧ exp (inv y) = y := by
    intro y hy
    have hc := Classical.choose_spec hy
    constructor
    · dsimp [inv]
      rw [dif_pos hy]
      exact hc.1
    · dsimp [inv]
      rw [dif_pos hy]
      exact hc.2
  have hinv2 : ∀ v : E, v ∈ U → inv (exp v) = v := by
    intro v hv
    have hmem : exp v ∈ V := by exact ⟨v, hv, rfl⟩
    have hc := Classical.choose_spec hmem
    have hsubeq : (⟨Classical.choose hmem, hc.1⟩ : U) = ⟨v, hv⟩ := by
      exact hinj (by simpa using hc.2)
    have hval : (Classical.choose hmem : E) = v := by
      exact congrArg (fun z : U => (z : E)) hsubeq
    dsimp [inv]
    rw [dif_pos hmem]
    exact hval
  exact ⟨U, hU, V, hV, hmap, hinj, hsurj, hcont, inv, fun y hy => ⟨(hinv1 y hy).1, (hinv1 y hy).2, hinv2⟩⟩


end

end Submission.ExpLocalDiffeo

