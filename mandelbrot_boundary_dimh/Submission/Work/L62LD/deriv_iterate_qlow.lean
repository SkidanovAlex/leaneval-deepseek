import Mathlib
import Submission.Work.L62.l62c_deriv
import Submission.Work.L62LD.setup

/-!
# L62LD — the lower-end lift/cylinder derivative identity for iterates

`q = qlow = π ∘ flip` is the lower-end cylinder coordinate (`Work.L62.qlow`), with
`q' = -2πi · q` and `q ≠ 0`.  If `H` is holomorphic on the lower-end cylinder neighbourhood
`lowOmega` and intertwines `ĥ = d.E - β` with `q` on the lower horn `hd.Bl`
(`H (q w) = q (ĥ w)`), then along an orbit that stays in `hd.Bl`,

  `deriv (ĥ^[j]) w = deriv (H^[j]) (q w) · q w / (H^[j]) (q w)`,

the lower-end analogue of `Work.L62.deriv_lift_eq` for the full iterate.  This is the step that
turns a derivative bound on the head of `Lemma 6.2` into the derivative of the lifted chain.
-/

namespace Work.L62LD

open MandelDim Set Filter Topology
open scoped Topology

noncomputable section

variable {g₀ : ℂ → ℂ} {D : Set ℂ}

/-! ## The lower-end coordinate `q = qlow` and its derivative -/

/-- `q(w) = π(flip w)` satisfies `q' = -2πi · q`. -/
theorem hasDerivAt_qlow (x : ℂ) :
    HasDerivAt Work.L62.qlow (-(2 * (Real.pi : ℂ) * Complex.I) * Work.L62.qlow x) x := by
  have hpi := Work.Horn.piExp_hasDerivAt (Work.L62.flip x)
  have hflip : HasDerivAt Work.L62.flip (-1) x := by
    have h : HasDerivAt (fun y : ℂ => (1 / 2 : ℂ) - y) (0 - 1) x :=
      (hasDerivAt_const x (1 / 2 : ℂ)).sub (hasDerivAt_id x)
    rw [show (0 : ℂ) - 1 = -1 by ring] at h
    exact h
  have hc := hpi.comp x hflip
  have hval : (2 * (Real.pi : ℂ) * Complex.I * MandelDim.piExp (Work.L62.flip x)) * (-1)
      = -(2 * (Real.pi : ℂ) * Complex.I) * Work.L62.qlow x := by
    rw [Work.L62.qlow]; ring
  rw [hval] at hc
  exact hc

theorem deriv_qlow (x : ℂ) :
    deriv Work.L62.qlow x = -(2 * (Real.pi : ℂ) * Complex.I) * Work.L62.qlow x :=
  (hasDerivAt_qlow x).deriv

theorem differentiableAt_qlow (x : ℂ) : DifferentiableAt ℂ Work.L62.qlow x :=
  (hasDerivAt_qlow x).differentiableAt

theorem neg_two_pi_I_ne_zero : (-(2 * (Real.pi : ℂ) * Complex.I)) ≠ 0 :=
  neg_ne_zero.mpr Complex.two_pi_I_ne_zero

/-! ## Iterates of a map holomorphic on an open set -/

/-- If `f` is holomorphic on the open set `s` and the orbit of `x` up to time `n` stays in `s`,
then `f^[n]` is complex differentiable at `x`. -/
theorem differentiableAt_iterate {s : Set ℂ} {f : ℂ → ℂ} (hs : IsOpen s)
    (hf : DifferentiableOn ℂ f s) :
    ∀ (n : ℕ) (x : ℂ), (∀ m : ℕ, m < n → (f^[m]) x ∈ s) → DifferentiableAt ℂ (f^[n]) x := by
  intro n
  induction n with
  | zero =>
      intro x _
      simpa using (differentiableAt_id (x := x) : DifferentiableAt ℂ id x)
  | succ k ih =>
      intro x hx
      rw [Function.iterate_succ]
      refine (ih (f x) ?_).comp x ?_
      · intro m hm
        rw [← Function.iterate_succ_apply]
        exact hx (m + 1) (Nat.succ_lt_succ hm)
      · exact hf.differentiableAt (hs.mem_nhds (hx 0 (Nat.succ_pos k)))

/-! ## The semiconjugacy of the iterates -/

theorem qlow_mem_lowOmega (d : MandelDim.ParabData g₀ D) (hd : MandelDim.HornData d) {x : ℂ}
    (hx : x ∈ hd.Bl) : Work.L62.qlow x ∈ Work.L62.lowOmega d hd := by
  rw [Work.L62.lowOmega_eq_image_qlow]
  exact Or.inr ⟨x, hx, rfl⟩

/-- `H^[m] ∘ q = q ∘ ĥ^[m]` along an orbit staying in the lower horn. -/
theorem iterate_semiconj (d : MandelDim.ParabData g₀ D) (hd : MandelDim.HornData d) {β : ℂ}
    {H : ℂ → ℂ}
    (hlink : ∀ w ∈ hd.Bl,
      H (Work.L62.qlow w) = Work.L62.qlow ((fun w => d.E w - β) w))
    {w : ℂ} {j : ℕ} (hw : ∀ m : ℕ, m ≤ j → ((fun w => d.E w - β)^[m]) w ∈ hd.Bl) :
    ∀ m : ℕ, m ≤ j →
      (H^[m]) (Work.L62.qlow w) = Work.L62.qlow (((fun w => d.E w - β)^[m]) w) := by
  intro m
  induction m with
  | zero => intro _; simp
  | succ k ih =>
      intro hm
      have hk : ((fun w => d.E w - β)^[k]) w ∈ hd.Bl := hw k (by omega)
      simp only [Function.iterate_succ', Function.comp_apply]
      rw [ih (by omega), hlink _ hk]

/-! ## The one-step derivative identity -/

/-- One step of the lift/cylinder derivative identity at a point of the lower horn. -/
theorem one_step_deriv (d : MandelDim.ParabData g₀ D) (hd : MandelDim.HornData d) {β : ℂ}
    {H : ℂ → ℂ} (hEdiff : DifferentiableOn ℂ d.E hd.Bl)
    (hHdiff : DifferentiableOn ℂ H (Work.L62.lowOmega d hd))
    (hlink : ∀ w ∈ hd.Bl,
      H (Work.L62.qlow w) = Work.L62.qlow ((fun w => d.E w - β) w))
    {x : ℂ} (hx : x ∈ hd.Bl) :
    deriv (fun w => d.E w - β) x
      = deriv H (Work.L62.qlow x) * Work.L62.qlow x / H (Work.L62.qlow x) := by
  have hHd : DifferentiableAt ℂ H (Work.L62.qlow x) :=
    hHdiff.differentiableAt ((Work.L62.isOpen_lowOmega d hd).mem_nhds (qlow_mem_lowOmega d hd hx))
  have hEd : DifferentiableAt ℂ (fun w => d.E w - β) x :=
    (hEdiff.differentiableAt (hd.Bl_open.mem_nhds hx)).sub_const β
  have hEq : (fun u => H (Work.L62.qlow u)) =ᶠ[𝓝 x]
      (fun u => Work.L62.qlow ((fun w => d.E w - β) u)) :=
    Filter.eventually_of_mem (hd.Bl_open.mem_nhds hx) (fun u hu => hlink u hu)
  have hdeq : deriv (fun u => H (Work.L62.qlow u)) x
      = deriv (fun u => Work.L62.qlow ((fun w => d.E w - β) u)) x := hEq.deriv_eq
  have h1 : deriv (fun u => H (Work.L62.qlow u)) x
      = deriv H (Work.L62.qlow x) * deriv Work.L62.qlow x := by
    rw [show (fun u => H (Work.L62.qlow u)) = H ∘ Work.L62.qlow from rfl,
        deriv_comp x hHd (differentiableAt_qlow x)]
  have h2 : deriv (fun u => Work.L62.qlow ((fun w => d.E w - β) u)) x
      = deriv Work.L62.qlow (d.E x - β) * deriv (fun w => d.E w - β) x := by
    rw [show (fun u => Work.L62.qlow ((fun w => d.E w - β) u))
          = Work.L62.qlow ∘ (fun w => d.E w - β) from rfl,
        deriv_comp x (differentiableAt_qlow _) hEd]
  rw [h1, h2, deriv_qlow, deriv_qlow] at hdeq
  have hne : H (Work.L62.qlow x) ≠ 0 := by
    rw [hlink x hx]; exact Work.L62.qlow_ne_zero _
  have hkey : deriv H (Work.L62.qlow x) * Work.L62.qlow x
      = H (Work.L62.qlow x) * deriv (fun w => d.E w - β) x := by
    have hcomm : (-(2 * (Real.pi : ℂ) * Complex.I)) *
          (deriv H (Work.L62.qlow x) * Work.L62.qlow x)
        = (-(2 * (Real.pi : ℂ) * Complex.I)) *
          (H (Work.L62.qlow x) * deriv (fun w => d.E w - β) x) := by
      rw [← hlink x hx] at hdeq
      calc (-(2 * (Real.pi : ℂ) * Complex.I)) *
            (deriv H (Work.L62.qlow x) * Work.L62.qlow x)
          = deriv H (Work.L62.qlow x) *
            ((-(2 * (Real.pi : ℂ) * Complex.I)) * Work.L62.qlow x) := by ring
        _ = ((-(2 * (Real.pi : ℂ) * Complex.I)) * H (Work.L62.qlow x))
              * deriv (fun w => d.E w - β) x := hdeq
        _ = (-(2 * (Real.pi : ℂ) * Complex.I)) *
            (H (Work.L62.qlow x) * deriv (fun w => d.E w - β) x) := by ring
    exact mul_left_cancel₀ neg_two_pi_I_ne_zero hcomm
  rw [eq_div_iff hne, mul_comm (deriv (fun w => d.E w - β) x) (H (Work.L62.qlow x))]
  exact hkey.symm

/-! ## The iterate identity -/

theorem deriv_iterate_qlow {g₀ : ℂ → ℂ} {D : Set ℂ} (d : MandelDim.ParabData g₀ D)
    (hd : MandelDim.HornData d) {β : ℂ} {H : ℂ → ℂ}
    (hEdiff : DifferentiableOn ℂ d.E hd.Bl)
    (hHdiff : DifferentiableOn ℂ H (Work.L62.lowOmega d hd))
    (hHmap : Set.MapsTo H (Work.L62.lowOmega d hd) (Work.L62.lowOmega d hd))
    (hlink : ∀ w ∈ hd.Bl, H (Work.L62.qlow w) = Work.L62.qlow (d.E w - β))
    (w : ℂ) (j : ℕ) (hw : ∀ m : ℕ, m ≤ j → ((fun w => d.E w - β)^[m]) w ∈ hd.Bl) :
    deriv ((fun w => d.E w - β)^[j]) w =
      deriv (H^[j]) (Work.L62.qlow w) * Work.L62.qlow w / (H^[j]) (Work.L62.qlow w) := by
  have hlink' : ∀ u ∈ hd.Bl,
      H (Work.L62.qlow u) = Work.L62.qlow ((fun w => d.E w - β) u) := fun u hu => hlink u hu
  have hEdiff' : DifferentiableOn ℂ (fun w => d.E w - β) hd.Bl := hEdiff.sub_const β
  have key : ∀ (n : ℕ) (z : ℂ),
      (∀ m : ℕ, m ≤ n → ((fun w => d.E w - β)^[m]) z ∈ hd.Bl) →
      deriv ((fun w => d.E w - β)^[n]) z =
        deriv (H^[n]) (Work.L62.qlow z) * Work.L62.qlow z / (H^[n]) (Work.L62.qlow z) := by
    intro n
    induction n with
    | zero =>
        intro z _
        rw [Function.iterate_zero, Function.iterate_zero]
        simp [deriv_id, Work.L62.qlow_ne_zero z]
    | succ k ih =>
        intro z hz
        have hz0 : z ∈ hd.Bl := hz 0 (Nat.zero_le _)
        have hstep := one_step_deriv d hd hEdiff hHdiff hlink' hz0
        have ihz := ih ((fun w => d.E w - β) z) (fun m hm => by
          rw [← Function.iterate_succ_apply]
          exact hz (m + 1) (by omega))
        have hEd : DifferentiableAt ℂ (fun w => d.E w - β) z :=
          (hEdiff.differentiableAt (hd.Bl_open.mem_nhds hz0)).sub_const β
        have hitd : DifferentiableAt ℂ ((fun w => d.E w - β)^[k]) ((fun w => d.E w - β) z) :=
          differentiableAt_iterate hd.Bl_open hEdiff' k _ (fun m hm => by
            rw [← Function.iterate_succ_apply]
            exact hz (m + 1) (by omega))
        have hHd : DifferentiableAt ℂ H (Work.L62.qlow z) :=
          hHdiff.differentiableAt
            ((Work.L62.isOpen_lowOmega d hd).mem_nhds (qlow_mem_lowOmega d hd hz0))
        have hHkd : DifferentiableAt ℂ (H^[k]) (H (Work.L62.qlow z)) :=
          differentiableAt_iterate (Work.L62.isOpen_lowOmega d hd) hHdiff k _ (fun m hm => by
            rw [← Function.iterate_succ_apply]
            rw [iterate_semiconj d hd hlink' hz (m + 1) (by omega)]
            exact qlow_mem_lowOmega d hd (hz (m + 1) (by omega)))
        have hcr1 : deriv ((fun w => d.E w - β)^[k+1]) z
            = deriv ((fun w => d.E w - β)^[k]) ((fun w => d.E w - β) z)
              * deriv (fun w => d.E w - β) z := by
          rw [Function.iterate_succ]
          exact deriv_comp z hitd hEd
        have hcr2 : deriv (H^[k+1]) (Work.L62.qlow z)
            = deriv (H^[k]) (H (Work.L62.qlow z)) * deriv H (Work.L62.qlow z) := by
          rw [Function.iterate_succ]
          exact deriv_comp (Work.L62.qlow z) hHkd hHd
        rw [hcr1, hcr2, ihz, hstep]
        have hh : H (Work.L62.qlow z) ≠ 0 := by
          rw [hlink z hz0]; exact Work.L62.qlow_ne_zero _
        have hB : (H^[k]) (H (Work.L62.qlow z)) ≠ 0 := by
          rw [← Function.iterate_succ_apply]
          rw [iterate_semiconj d hd hlink' hz (k + 1) le_rfl]
          exact Work.L62.qlow_ne_zero _
        rw [← hlink z hz0]
        rw [show (H^[k+1]) (Work.L62.qlow z) = (H^[k]) (H (Work.L62.qlow z)) by
              rw [Function.iterate_succ, Function.comp_apply]]
        field_simp
  exact key j w hw

end

end Work.L62LD
