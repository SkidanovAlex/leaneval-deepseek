import Mathlib
import Submission.Work.Motion.Basic
import Submission.Work.Motion.pertBranch

set_option maxHeartbeats 1000000

namespace Work.Motion

open MandelDim
open LeanEval.Dynamics.MandelbrotBoundary
open Set Metric Filter

noncomputable section

/-- **Existence of the moving inverse branches.** Given a dynamical conformal IFS of `Tc c₀` on
`ball p r` (branches `τ i` inverting `(Tc c₀)^[n i]`, univalent, images in `ball p (r/2)`, pairwise
disjoint, `‖τ i'‖ ≥ 1/K` on `ball p (r/2)`), there are `ρ > 0` and branches `τc c i` for
`c ∈ ball c₀ ρ`, holomorphic in `(c,z)` on `ball c₀ ρ × ball p r₁` (`r/2 < r₁ < r`), inverting
`(Tc c)^[n i]` on `ball p r₁`, agreeing with `τ i` at `c = c₀`, mapping the core `closedBall p (r/2)`
into a strictly smaller ball `closedBall p s` (`s < r/2`), with derivative of modulus in `[β,θ]`
there (`θ < 1`, `β > 0`), Lipschitz in `c` with constant `Lc` and with `(c,z)`-Lipschitz derivative
(constant `G`).  `PertData` bundles these data (it is defined in `Submission/Work/Motion/Basic.lean`).

Route (no lambda-lemma, no quasiconformal machinery): fix `i` and put `G(c,x) = (Tc c)^[n i] x`, a
polynomial in `(c,x)`.  Write `x = τ i z + v` and let `A(c,z) = G(c, τ i z) − z`,
`B(c,z) = ∂_x G(c, τ i z)`; on `closedBall p (3r/4)` the unperturbed data give `A(c₀,·) = 0` and
`|B(c₀,·)| ≥ b > 0`, both persisting for `c` near `c₀`.  The iteration
`v₊ = v − (G(c, τ i z + v) − z)/B(c,z)` from `v = 0` is a contraction of `closedBall 0 ε`; its fixed
point `v(c,z)` satisfies `G(c, τ i z + v) = z`, obeys `|v| ≤ ε`, and is holomorphic in `(c,z)`
because the iterates are holomorphic where `B ≠ 0` and converge uniformly on the region
(`TendstoLocallyUniformlyOn.differentiableOn`).  Then `τc c i z := τ i z + v(c,z)` gives `dyn`,
`base`; `img` from `|τc c i z − p| ≤ s₀ + ε` on `closedBall p (r/2)`, `s₀` from `exists_image_bound`;
`deriv_le` from Schwarz–Pick on `ball p r₁`; `deriv_ge` from `‖τ i'‖ ≥ 1/K` plus a Cauchy estimate on
`τc c i − τ i`; `lips_c`, `deriv_lips` from Cauchy estimates in `(c,z)`. -/
theorem exists_pertData {c₀ : ℂ} {N : ℕ} {τ : Fin N → ℂ → ℂ} {n : Fin N → ℕ} {p : ℂ} {r K : ℝ}
    (hN : 2 ≤ N) (hIFS : IsConformalIFS N τ p r K) (hDyn : IsDynIFS c₀ τ n p r) :
    Nonempty (PertData c₀ N τ n p r K) := by
  have hne : Nonempty (Fin N) := ⟨⟨0, by omega⟩⟩
  haveI := hne
  have hb : ∀ i : Fin N, Nonempty (Pert.BranchData c₀ (τ i) (n i) p r K) :=
    fun i => Pert.branch_exists hN hIFS hDyn i
  let D : ∀ i : Fin N, Pert.BranchData c₀ (τ i) (n i) p r K := fun i => (hb i).some
  have hu : (Finset.univ : Finset (Fin N)).Nonempty := Finset.univ_nonempty
  let ρ : ℝ := Finset.univ.inf' hu fun i => (D i).ρ
  let s : ℝ := Finset.univ.sup' hu fun i => (D i).s
  let θ : ℝ := Finset.univ.sup' hu fun i => (D i).θ
  let β : ℝ := Finset.univ.inf' hu fun i => (D i).β
  let Lc : ℝ := Finset.univ.sup' hu fun i => (D i).Lc
  let G : ℝ := Finset.univ.sup' hu fun i => (D i).G
  have hρ : 0 < ρ := by
    rw [show ρ = Finset.univ.inf' hu (fun i => (D i).ρ) from rfl, Finset.lt_inf'_iff]
    intro i _
    exact (D i).hρ
  have hleρ : ∀ i, ρ ≤ (D i).ρ := fun i =>
    show Finset.univ.inf' hu (fun j => (D j).ρ) ≤ (D i).ρ from
      Finset.inf'_le _ (Finset.mem_univ i)
  have hslt : s < r / 2 := by
    rw [show s = Finset.univ.sup' hu (fun i => (D i).s) from rfl, Finset.sup'_lt_iff]
    intro i _
    exact (D i).hs
  have hles : ∀ i, (D i).s ≤ s := fun i =>
    show (D i).s ≤ Finset.univ.sup' hu (fun j => (D j).s) from
      Finset.le_sup' (fun j => (D j).s) (Finset.mem_univ i)
  have hθ1 : θ < 1 := by
    rw [show θ = Finset.univ.sup' hu (fun i => (D i).θ) from rfl, Finset.sup'_lt_iff]
    intro i _
    exact (D i).hθ1
  have hleθ : ∀ i, (D i).θ ≤ θ := fun i =>
    show (D i).θ ≤ Finset.univ.sup' hu (fun j => (D j).θ) from
      Finset.le_sup' (fun j => (D j).θ) (Finset.mem_univ i)
  have hβ : 0 < β := by
    rw [show β = Finset.univ.inf' hu (fun i => (D i).β) from rfl, Finset.lt_inf'_iff]
    intro i _
    exact (D i).hβ
  have hleβ : ∀ i, β ≤ (D i).β := fun i =>
    show Finset.univ.inf' hu (fun j => (D j).β) ≤ (D i).β from
      Finset.inf'_le _ (Finset.mem_univ i)
  have hleLc : ∀ i, (D i).Lc ≤ Lc := fun i =>
    show (D i).Lc ≤ Finset.univ.sup' hu (fun j => (D j).Lc) from
      Finset.le_sup' (fun j => (D j).Lc) (Finset.mem_univ i)
  have hleG : ∀ i, (D i).G ≤ G := fun i =>
    show (D i).G ≤ Finset.univ.sup' hu (fun j => (D j).G) from
      Finset.le_sup' (fun j => (D j).G) (Finset.mem_univ i)
  have hθ0 : 0 ≤ θ := le_trans (D ⟨0, by omega⟩).hθ0 (hleθ ⟨0, by omega⟩)
  have hs0 : 0 ≤ s := le_trans (D ⟨0, by omega⟩).hs0 (hles ⟨0, by omega⟩)
  have hLc0 : 0 ≤ Lc := le_trans (D ⟨0, by omega⟩).hLc (hleLc ⟨0, by omega⟩)
  have hG0 : 0 ≤ G := le_trans (D ⟨0, by omega⟩).hG (hleG ⟨0, by omega⟩)
  obtain ⟨hr, hK, hdiff, hinj, hmaps, hdisj, hder⟩ := hIFS
  have hr₁ : r / 2 < Pert.rInner r := by rw [Pert.rInner]; linarith
  have hr₁' : Pert.rInner r < r := by rw [Pert.rInner]; linarith
  have hbase : ∀ i z, z ∈ ball p (Pert.rInner r) →
      (fun c i z => (D i).τc c z) c₀ i z = τ i z := by
    intro i z hz
    exact (D i).base z hz
  have hhol : ∀ i, DifferentiableOn ℂ (fun q : ℂ × ℂ => (D i).τc q.1 q.2)
      (ball c₀ ρ ×ˢ ball p (Pert.rInner r)) := by
    intro i
    refine ((D i).hol).mono ?_
    intro q hq
    exact mem_prod.mpr ⟨ball_subset_ball (hleρ i) hq.1, hq.2⟩
  have hdyn : ∀ c ∈ ball c₀ ρ, ∀ i z, z ∈ ball p (Pert.rInner r) →
      (Tc c)^[n i] ((fun c i z => (D i).τc c z) c i z) = z := by
    intro c hc i z hz
    exact (D i).dyn c (ball_subset_ball (hleρ i) hc) z hz
  have himg : ∀ c ∈ ball c₀ ρ, ∀ i, MapsTo ((fun c i z => (D i).τc c z) c i)
      (closedBall p (r / 2)) (closedBall p s) := by
    intro c hc i
    exact ((D i).img c (ball_subset_ball (hleρ i) hc)).mono_right
      (closedBall_subset_closedBall (hles i))
  have hderiv_le : ∀ c ∈ ball c₀ ρ, ∀ i, ∀ z ∈ closedBall p (r / 2),
      ‖deriv ((fun c i z => (D i).τc c z) c i) z‖ ≤ θ := by
    intro c hc i z hz
    exact le_trans ((D i).deriv_le c (ball_subset_ball (hleρ i) hc) z hz) (hleθ i)
  have hderiv_ge : ∀ c ∈ ball c₀ ρ, ∀ i, ∀ z ∈ closedBall p (r / 2),
      β ≤ ‖deriv ((fun c i z => (D i).τc c z) c i) z‖ := by
    intro c hc i z hz
    exact le_trans (hleβ i) ((D i).deriv_ge c (ball_subset_ball (hleρ i) hc) z hz)
  have hlips_c : ∀ i, ∀ z ∈ closedBall p (r / 2), ∀ c ∈ ball c₀ ρ,
      ∀ c' ∈ ball c₀ ρ,
      ‖(fun c i z => (D i).τc c z) c i z - (fun c i z => (D i).τc c z) c' i z‖
        ≤ Lc * ‖c - c'‖ := by
    intro i z hz c hc c' hc'
    exact le_trans ((D i).lips_c z hz c (ball_subset_ball (hleρ i) hc)
      c' (ball_subset_ball (hleρ i) hc')) (mul_le_mul_of_nonneg_right (hleLc i) (norm_nonneg _))
  have hderiv_lips : ∀ i, ∀ z ∈ closedBall p (r / 2), ∀ z' ∈ closedBall p (r / 2),
      ∀ c ∈ ball c₀ ρ, ∀ c' ∈ ball c₀ ρ,
      ‖deriv ((fun c i z => (D i).τc c z) c i) z
        - deriv ((fun c i z => (D i).τc c z) c' i) z'‖
        ≤ G * (‖c - c'‖ + ‖z - z'‖) := by
    intro i z hz z' hz' c hc c' hc'
    exact le_trans ((D i).deriv_lips z hz z' hz' c (ball_subset_ball (hleρ i) hc)
      c' (ball_subset_ball (hleρ i) hc'))
      (mul_le_mul_of_nonneg_right (hleG i) (by positivity))
  have hPD : PertData c₀ N τ n p r K :=
    { ρ := ρ, hρ := hρ, r₁ := Pert.rInner r, hr₁ := hr₁, hr₁' := hr₁',
      s := s, hs0 := hs0, hsr := hslt, θ := θ, hθ0 := hθ0, hθ1 := hθ1,
      β := β, hβ := hβ, Lc := Lc, hLc := hLc0, G := G, hG := hG0,
      τc := fun c i z => (D i).τc c z, base := hbase, hol := hhol, dyn := hdyn, img := himg,
      deriv_le := hderiv_le, deriv_ge := hderiv_ge, lips_c := hlips_c,
      deriv_lips := hderiv_lips }
  exact ⟨hPD⟩

end

end Work.Motion
