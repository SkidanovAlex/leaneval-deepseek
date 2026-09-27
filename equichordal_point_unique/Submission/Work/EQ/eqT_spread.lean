import Mathlib
import Submission.Work.EQ.SymDefs
import Submission.Work.EQ.orbit_tendsto_upper
import Submission.Work.EQ.orbit_tendsto_lower
import Submission.Work.EQ.eq_of_periodic_closed

/-!
# Spreading a germ of a `eqT`-invariant closed set along the `σ`-orbit

Rychlik's equichordal dynamics: for a normalised equichordal curve `ρ₁` about `O₁ = -a/2` the
equichordal map `T = eqT a` sends the point `P θ = polarPt (-(a/2)) (ρ₁ θ) θ` to
`P (σ θ)`, where `σ` is an increasing homeomorphism of `ℝ` commuting with `θ ↦ θ + 2π`,
fixing `0` and `π` and having no other fixed point on `(0, π) ∪ (π, 2π)`.

Let `D` be closed, forward invariant under `eqT a`, and "backward closed along the orbit"
(`eqT a (P θ) ∈ D → P θ ∈ D`).  Then the set `S = {θ | P θ ∈ D}` is closed and invariant
under `σ` and `σ⁻¹`.  Since `σ` is increasing with `σ 0 = 0`, `σ π = π` and no fixed point on
`(0,π)`, `(π,2π)`, every orbit has one of its two ends converging to `π`; combined with a germ
of `D` around `θ = π` this gives `(0, π) ∪ (π, 2π) ⊆ S`, and since `S` is `2π`-periodic and
closed, `S = ℝ`.  This is the lemma `Work.EQ.eqT_spread`.
-/

namespace Work.EQ

open Complex

/-- `polarPt` is `2π`-periodic in the angle. -/
lemma eqT_spread_polarPt_period (c r θ : ℝ) :
    polarPt c r (θ + 2 * Real.pi) = polarPt c r θ := by
  simp only [polarPt]
  rw [show ((↑(θ + 2 * Real.pi) : ℂ)) * Complex.I
      = (↑θ : ℂ) * Complex.I + (2 * ↑Real.pi * Complex.I) by push_cast; ring]
  rw [Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

theorem eqT_spread {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {ρ₁ : ℝ → ℝ}
    (hcont : Continuous ρ₁) (hper : ∀ θ, ρ₁ (θ + 2 * Real.pi) = ρ₁ θ)
    {σ : ℝ ≃o ℝ}
    (hσper : ∀ θ, σ (θ + 2 * Real.pi) = σ θ + 2 * Real.pi)
    (hσeq : ∀ θ, eqT a (polarPt (-(a/2)) (ρ₁ θ) θ) = polarPt (-(a/2)) (ρ₁ (σ θ)) (σ θ))
    (hσ0 : σ 0 = 0) (hσπ : σ Real.pi = Real.pi)
    (hfix1 : ∀ θ, 0 < θ → θ < Real.pi → σ θ ≠ θ)
    (hfix2 : ∀ θ, Real.pi < θ → θ < 2 * Real.pi → σ θ ≠ θ)
    {D : Set ℂ} (hDc : IsClosed D) (hDinv : Set.MapsTo (eqT a) D D)
    (hback : ∀ θ, eqT a (polarPt (-(a/2)) (ρ₁ θ) θ) ∈ D →
      polarPt (-(a/2)) (ρ₁ θ) θ ∈ D)
    {δ : ℝ} (hδ : 0 < δ) (hgerm : ∀ θ, |θ - Real.pi| < δ → polarPt (-(a/2)) (ρ₁ θ) θ ∈ D) :
    ∀ θ, polarPt (-(a/2)) (ρ₁ θ) θ ∈ D := by
  set P : ℝ → ℂ := fun θ => polarPt (-(a / 2)) (ρ₁ θ) θ with hP
  have hPapp : ∀ θ, P θ = polarPt (-(a / 2)) (ρ₁ θ) θ := fun θ => rfl
  set S : Set ℝ := {θ | P θ ∈ D} with hS
  have hSmem : ∀ θ, θ ∈ S ↔ P θ ∈ D := by intro θ; rw [hS]; simp
  have hPcont : Continuous P := by
    show Continuous (fun θ => polarPt (-(a / 2)) (ρ₁ θ) θ)
    unfold polarPt
    fun_prop
  have hSclosed : IsClosed S := by
    rw [show S = P ⁻¹' D by ext θ; rw [hSmem θ]; rfl]
    exact hDc.preimage hPcont
  -- `S` is invariant under `σ` (both directions, because of `hDinv` and `hback`).
  have hSinv : ∀ θ, θ ∈ S ↔ σ θ ∈ S := by
    intro θ
    rw [hSmem θ, hSmem (σ θ), hPapp θ, hPapp (σ θ)]
    constructor
    · intro h
      have h1 : eqT a (polarPt (-(a / 2)) (ρ₁ θ) θ) ∈ D := hDinv h
      rwa [hσeq θ] at h1
    · intro h
      refine hback θ ?_
      rw [hσeq θ]
      exact h
  have hSinv' : ∀ θ, θ ∈ S ↔ σ.symm θ ∈ S := by
    intro θ
    have := hSinv (σ.symm θ)
    rw [OrderIso.apply_symm_apply] at this
    exact this.symm
  have hσ2π : σ (2 * Real.pi) = 2 * Real.pi := by
    have h := hσper 0
    rw [hσ0] at h
    simpa using h
  -- If an orbit accumulates at `π`, its starting point lies in `S`.
  have horb : ∀ (τ : ℝ → ℝ) (hinv : ∀ x, x ∈ S ↔ τ x ∈ S) (θ : ℝ),
      Filter.Tendsto (fun n : ℕ => τ^[n] θ) Filter.atTop (nhds Real.pi) → θ ∈ S := by
    intro τ hinv θ ht
    have hev : ∀ᶠ n : ℕ in Filter.atTop, |τ^[n] θ - Real.pi| < δ := by
      have hb := ht (Metric.ball_mem_nhds Real.pi hδ)
      filter_upwards [hb] with n hn
      simpa only [Set.mem_preimage, Metric.mem_ball, Real.dist_eq] using hn
    obtain ⟨N, hN⟩ := hev.exists
    have hmem : τ^[N] θ ∈ S := by
      rw [hSmem, hPapp]
      exact hgerm _ hN
    have hiter : ∀ n : ℕ, τ^[n] θ ∈ S → θ ∈ S := by
      intro n
      induction n with
      | zero => intro h; simpa using h
      | succ k ih =>
          intro h
          apply ih
          rw [Function.iterate_succ_apply'] at h
          exact (hinv (τ^[k] θ)).mpr h
    exact hiter N hmem
  have hsymm0 : σ.symm 0 = 0 := (OrderIso.symm_apply_eq σ).mpr hσ0.symm
  have hsymmπ : σ.symm Real.pi = Real.pi := (OrderIso.symm_apply_eq σ).mpr hσπ.symm
  have hsymm2π : σ.symm (2 * Real.pi) = 2 * Real.pi :=
    (OrderIso.symm_apply_eq σ).mpr hσ2π.symm
  -- `(0, π) ⊆ S`.
  have hmem1 : ∀ θ, 0 < θ → θ < Real.pi → θ ∈ S := by
    intro θ hθ0 hθπ
    rcases lt_or_gt_of_ne (hfix1 θ hθ0 hθπ) with hlt | hgt
    · have hs : θ < σ.symm θ := by
        have h0 := σ.symm.strictMono hlt
        rwa [OrderIso.symm_apply_apply] at h0
      have hfixs : ∀ x, 0 < x → x < Real.pi → σ.symm x ≠ x :=
        fun x hx0 hxπ hsx => hfix1 x hx0 hxπ ((OrderIso.symm_apply_eq σ).mp hsx).symm
      have ht := orbit_tendsto_upper σ.symm.continuous σ.symm.strictMono Real.pi_pos
          hsymm0 hsymmπ hfixs hθ0 hθπ hs
      exact horb σ.symm hSinv' θ ht
    · have ht := orbit_tendsto_upper σ.continuous σ.strictMono Real.pi_pos hσ0 hσπ
          (fun x hx0 hxπ => hfix1 x hx0 hxπ) hθ0 hθπ hgt
      exact horb σ hSinv θ ht
  -- `(π, 2π) ⊆ S`.
  have hmem2 : ∀ θ, Real.pi < θ → θ < 2 * Real.pi → θ ∈ S := by
    intro θ hθ1 hθ2
    rcases lt_or_gt_of_ne (hfix2 θ hθ1 hθ2) with hlt | hgt
    · have ht := orbit_tendsto_lower σ.continuous σ.strictMono
          (by linarith [Real.pi_pos]) hσπ hσ2π
          (fun x hx1 hx2 => hfix2 x hx1 hx2) hθ1 hθ2 hlt
      exact horb σ hSinv θ ht
    · have hs : σ.symm θ < θ := by
        have h0 := σ.symm.strictMono hgt
        rwa [OrderIso.symm_apply_apply] at h0
      have hfixs : ∀ x, Real.pi < x → x < 2 * Real.pi → σ.symm x ≠ x :=
        fun x hx1 hx2 hsx => hfix2 x hx1 hx2 ((OrderIso.symm_apply_eq σ).mp hsx).symm
      have ht := orbit_tendsto_lower σ.symm.continuous σ.symm.strictMono
          (by linarith [Real.pi_pos]) hsymmπ hsymm2π hfixs hθ1 hθ2 hs
      exact horb σ.symm hSinv' θ ht
  -- The endpoints `0` and `2π` of the fundamental interval lie in `S` by closedness.
  have h0mem : (0 : ℝ) ∈ S := by
    rw [← IsClosed.closure_eq hSclosed, Metric.mem_closure_iff]
    intro ε hε
    refine ⟨min (Real.pi/2) (ε/2), hmem1 _ ?_ ?_, ?_⟩
    · exact lt_min (by linarith [Real.pi_pos]) (by linarith)
    · exact lt_of_le_of_lt (min_le_left _ _) (by linarith [Real.pi_pos])
    · rw [Real.dist_eq, zero_sub, abs_neg,
        abs_of_pos (lt_min (by linarith [Real.pi_pos]) (by linarith))]
      exact lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have h2πmem : (2 * Real.pi) ∈ S := by
    rw [← IsClosed.closure_eq hSclosed, Metric.mem_closure_iff]
    intro ε hε
    have hpos : 0 < min (Real.pi/2) (ε/2) :=
      lt_min (by linarith [Real.pi_pos]) (by linarith)
    refine ⟨2 * Real.pi - min (Real.pi/2) (ε/2), hmem2 _ ?_ ?_, ?_⟩
    · linarith [min_le_left (Real.pi/2) (ε/2), Real.pi_pos]
    · linarith [hpos]
    · rw [Real.dist_eq,
        show 2 * Real.pi - (2 * Real.pi - min (Real.pi/2) (ε/2)) = min (Real.pi/2) (ε/2)
          by ring,
        abs_of_pos hpos]
      exact lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hbase : ∀ x, 0 ≤ x → x ≤ 2 * Real.pi → x ∈ S := by
    intro x h0 h1
    rcases lt_or_eq_of_le h0 with h0' | h0'
    · rcases lt_or_eq_of_le h1 with h1' | h1'
      · rcases lt_trichotomy x Real.pi with hx | hx | hx
        · exact hmem1 x h0' hx
        · rw [hx, hSmem, hPapp]
          exact hgerm Real.pi (by simpa using hδ)
        · exact hmem2 x hx h1'
      · rw [h1']; exact h2πmem
    · rw [← h0']; exact h0mem
  -- `S` is `2π`-periodic, so it is all of `ℝ`.
  have hPper : ∀ θ, P (θ + 2 * Real.pi) = P θ := by
    intro θ
    rw [hPapp (θ + 2 * Real.pi), hPapp θ, hper θ, eqT_spread_polarPt_period]
  have hSper : ∀ x, x ∈ S ↔ x + 2 * Real.pi ∈ S := by
    intro x
    rw [hSmem x, hSmem (x + 2 * Real.pi), hPper x]
  have huniv : S = Set.univ := eq_of_periodic_closed (by positivity) hSclosed hSper hbase
  intro θ
  have hmem : θ ∈ S := by rw [huniv]; exact Set.mem_univ θ
  simpa [hSmem θ, hPapp θ] using hmem

end Work.EQ
