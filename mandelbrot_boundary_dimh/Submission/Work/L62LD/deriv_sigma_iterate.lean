import Mathlib
import Submission.Work.L62LD.setup
import Submission.Work.L62LD.deriv_iterate_qlow

namespace Work.L62LD

open MandelDim Set Filter Topology
open scoped Topology

noncomputable section

set_option linter.unusedVariables false

variable {g₀ : ℂ → ℂ} {D : Set ℂ}

/-!
# The lower-end lift/cylinder derivative identity for iterates of a *section*

Let `q = qlow = π ∘ flip` be the lower-end cylinder coordinate and let `ĥ = d.E - β` be the
lower-end horn map.  Suppose `σ` is a holomorphic *section* of `ĥ` on the lower horn (`hd.Bl`),
i.e. `d.E (σ w) - β = w` for `w ∈ hd.Bl`, and `H` is the corresponding model map on the cylinder
neighbourhood `lowOmega d hd`, intertwining `σ` with `q` (`H (q w) = q (σ w)`).

Then, along an orbit of `σ` that stays in `hd.Bl` up to time `m - 1`,

  `deriv (σ^[m]) z = deriv (H^[m]) (q z) · q z / (H^[m]) (q z)`.

This is the section analogue of `Work.L62LD.iter_qlow_deriv` (where the map is `ĥ` itself, with
the converse linking `H (q w) = q (ĥ w)`); the proof is the same, and — remarkably — only the
local linking hypothesis is used: neither the section equation nor the invariance property is
needed.  It is used in step 4 of `model_head_down_deep` (diameter bounds on the discs `W j`),
where `W (j+1) = σ (W j)`.
-/

/-- **One-step derivative identity for a section.**  If `H (q w) = q (σ w)` on `hd.Bl`, then at
every point of the lower horn the derivative of `σ` is that of the lift conjugate. -/
theorem one_step_deriv_sigma {d : MandelDim.ParabData g₀ D} (hd : MandelDim.HornData d)
    {σ H : ℂ → ℂ} (hσd : DifferentiableOn ℂ σ hd.Bl)
    (hHdiff : DifferentiableOn ℂ H (Work.L62.lowOmega d hd))
    (hlink : ∀ w ∈ hd.Bl, H (Work.L62.qlow w) = Work.L62.qlow (σ w))
    {x : ℂ} (hx : x ∈ hd.Bl) :
    deriv σ x = deriv H (Work.L62.qlow x) * Work.L62.qlow x / H (Work.L62.qlow x) := by
  have hHd : DifferentiableAt ℂ H (Work.L62.qlow x) :=
    hHdiff.differentiableAt ((Work.L62.isOpen_lowOmega d hd).mem_nhds (qlow_mem_lowOmega d hd hx))
  have hσd_at : DifferentiableAt ℂ σ x := hσd.differentiableAt (hd.Bl_open.mem_nhds hx)
  have hEq : (fun u => H (Work.L62.qlow u)) =ᶠ[𝓝 x] (fun u => Work.L62.qlow (σ u)) :=
    Filter.eventually_of_mem (hd.Bl_open.mem_nhds hx) (fun u hu => hlink u hu)
  have hdeq : deriv (fun u => H (Work.L62.qlow u)) x
      = deriv (fun u => Work.L62.qlow (σ u)) x := hEq.deriv_eq
  have h1 : deriv (fun u => H (Work.L62.qlow u)) x
      = deriv H (Work.L62.qlow x) * deriv Work.L62.qlow x := by
    rw [show (fun u => H (Work.L62.qlow u)) = H ∘ Work.L62.qlow from rfl,
        deriv_comp x hHd (differentiableAt_qlow x)]
  have h2 : deriv (fun u => Work.L62.qlow (σ u)) x
      = deriv Work.L62.qlow (σ x) * deriv σ x := by
    rw [show (fun u => Work.L62.qlow (σ u)) = Work.L62.qlow ∘ σ from rfl,
        deriv_comp x (differentiableAt_qlow _) hσd_at]
  rw [h1, h2, deriv_qlow, deriv_qlow] at hdeq
  have hne : H (Work.L62.qlow x) ≠ 0 := by
    rw [hlink x hx]; exact Work.L62.qlow_ne_zero _
  have hkey : deriv H (Work.L62.qlow x) * Work.L62.qlow x
      = H (Work.L62.qlow x) * deriv σ x := by
    have hcomm : (-(2 * (Real.pi : ℂ) * Complex.I)) *
          (deriv H (Work.L62.qlow x) * Work.L62.qlow x)
        = (-(2 * (Real.pi : ℂ) * Complex.I)) *
          (H (Work.L62.qlow x) * deriv σ x) := by
      rw [← hlink x hx] at hdeq
      calc (-(2 * (Real.pi : ℂ) * Complex.I)) *
            (deriv H (Work.L62.qlow x) * Work.L62.qlow x)
          = deriv H (Work.L62.qlow x) *
            ((-(2 * (Real.pi : ℂ) * Complex.I)) * Work.L62.qlow x) := by ring
        _ = ((-(2 * (Real.pi : ℂ) * Complex.I)) * H (Work.L62.qlow x))
              * deriv σ x := hdeq
        _ = (-(2 * (Real.pi : ℂ) * Complex.I)) *
            (H (Work.L62.qlow x) * deriv σ x) := by ring
    exact mul_left_cancel₀ neg_two_pi_I_ne_zero hcomm
  rw [eq_div_iff hne, mul_comm (deriv σ x) (H (Work.L62.qlow x))]
  exact hkey.symm

/-- **Semiconjugacy of the iterates.**  If `H (q w) = q (σ w)` on the lower horn and the orbit of
`z` under `σ` stays in `hd.Bl` up to time `n - 1`, then `(H^[m]) (q z) = q (σ^[m] z)` for all
`m ≤ n`. -/
theorem iterate_semiconj_sigma {d : MandelDim.ParabData g₀ D} (hd : MandelDim.HornData d)
    {σ H : ℂ → ℂ}
    (hlink : ∀ w ∈ hd.Bl, H (Work.L62.qlow w) = Work.L62.qlow (σ w))
    {z : ℂ} {n : ℕ} (hz : ∀ t : ℕ, t < n → ((σ)^[t]) z ∈ hd.Bl) :
    ∀ m : ℕ, m ≤ n →
      (H^[m]) (Work.L62.qlow z) = Work.L62.qlow (((σ)^[m]) z) := by
  intro m
  induction m with
  | zero => intro _; simp
  | succ k ih =>
      intro hm
      have hk : k < n := by omega
      have hmem : ((σ)^[k]) z ∈ hd.Bl := hz k hk
      simp only [Function.iterate_succ', Function.comp_apply]
      rw [ih (by omega), hlink _ hmem]

theorem deriv_sigma_iterate {g₀ : ℂ → ℂ} {D : Set ℂ} (d : MandelDim.ParabData g₀ D)
    (hd : MandelDim.HornData d) {β : ℂ} {σ H : ℂ → ℂ}
    (hσd : DifferentiableOn ℂ σ hd.Bl) (hσmem : ∀ w ∈ hd.Bl, σ w ∈ hd.Bl)
    (hσsec : ∀ w ∈ hd.Bl, d.E (σ w) - β = w)
    (hHdiff : DifferentiableOn ℂ H (Work.L62.lowOmega d hd))
    (hHmap : Set.MapsTo H (Work.L62.lowOmega d hd) (Work.L62.lowOmega d hd))
    (hlink : ∀ w ∈ hd.Bl, H (Work.L62.qlow w) = Work.L62.qlow (σ w))
    (z : ℂ) (m : ℕ) (hz : ∀ t : ℕ, t < m → ((σ)^[t]) z ∈ hd.Bl) :
    deriv ((σ)^[m]) z =
      deriv (H^[m]) (Work.L62.qlow z) * Work.L62.qlow z / (H^[m]) (Work.L62.qlow z) := by
  have hlink' : ∀ u ∈ hd.Bl, H (Work.L62.qlow u) = Work.L62.qlow (σ u) := hlink
  -- The derivative identity, by induction on the number of iterates.
  have key : ∀ (n : ℕ) (z : ℂ),
      (∀ t : ℕ, t < n → ((σ)^[t]) z ∈ hd.Bl) →
      deriv ((σ)^[n]) z =
        deriv (H^[n]) (Work.L62.qlow z) * Work.L62.qlow z / (H^[n]) (Work.L62.qlow z) := by
    intro n
    induction n with
    | zero =>
        intro z _
        rw [Function.iterate_zero, Function.iterate_zero]
        simp [deriv_id, Work.L62.qlow_ne_zero z]
    | succ k ih =>
        intro z hz
        have hz0 : z ∈ hd.Bl := hz 0 (Nat.succ_pos k)
        have hstep := one_step_deriv_sigma hd hσd hHdiff hlink' hz0
        -- the orbit hypothesis for the shifted starting point `σ z`
        have hz' : ∀ t : ℕ, t < k → ((σ)^[t]) (σ z) ∈ hd.Bl := by
          intro t ht
          rw [← Function.iterate_succ_apply]
          exact hz (t + 1) (by omega)
        have ihz := ih (σ z) hz'
        have hσat : DifferentiableAt ℂ σ z := hσd.differentiableAt (hd.Bl_open.mem_nhds hz0)
        have hitd : DifferentiableAt ℂ ((σ)^[k]) (σ z) :=
          differentiableAt_iterate hd.Bl_open hσd k (σ z) hz'
        have hHd : DifferentiableAt ℂ H (Work.L62.qlow z) :=
          hHdiff.differentiableAt
            ((Work.L62.isOpen_lowOmega d hd).mem_nhds (qlow_mem_lowOmega d hd hz0))
        have hHkd : DifferentiableAt ℂ (H^[k]) (H (Work.L62.qlow z)) :=
          differentiableAt_iterate (Work.L62.isOpen_lowOmega d hd) hHdiff k _
            (fun t ht => by
              rw [← Function.iterate_succ_apply]
              rw [iterate_semiconj_sigma hd hlink' hz (t + 1) (by omega)]
              exact qlow_mem_lowOmega d hd (hz (t + 1) (by omega)))
        have hcr1 : deriv ((σ)^[k+1]) z
            = deriv ((σ)^[k]) (σ z) * deriv σ z := by
          rw [Function.iterate_succ]
          exact deriv_comp z hitd hσat
        have hcr2 : deriv (H^[k+1]) (Work.L62.qlow z)
            = deriv (H^[k]) (H (Work.L62.qlow z)) * deriv H (Work.L62.qlow z) := by
          rw [Function.iterate_succ]
          exact deriv_comp (Work.L62.qlow z) hHkd hHd
        rw [hcr1, hcr2, ihz, hstep]
        have hh : H (Work.L62.qlow z) ≠ 0 := by
          rw [hlink z hz0]; exact Work.L62.qlow_ne_zero _
        have hB : (H^[k]) (H (Work.L62.qlow z)) ≠ 0 := by
          rw [← Function.iterate_succ_apply]
          rw [iterate_semiconj_sigma hd hlink' hz (k + 1) le_rfl]
          exact Work.L62.qlow_ne_zero _
        rw [← hlink z hz0]
        rw [show (H^[k+1]) (Work.L62.qlow z) = (H^[k]) (H (Work.L62.qlow z)) by
              rw [Function.iterate_succ, Function.comp_apply]]
        field_simp
  exact key m z hz

end

end Work.L62LD
