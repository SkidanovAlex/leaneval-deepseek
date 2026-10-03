import Mathlib
import Submission.Work.L61.Basic
import Submission.Work.L61.Deriv.deriv_ne_zero

/-!
# Lemma 6.1 (Shishikura §6): the only critical value of the pushed-down horn map

`g = pushdown Ẽ_{f₀}` is the pushed-down horn map of §6, with domain
`gdom d hd = {0} ∪ π(B^u ∪ B^ℓ)` and critical value `critVal hd = π v` (`HornData.v` is a lift of
the unique critical value of the lifted horn map `Ẽ = d.E`).

Here we show that `g` has no critical values other than `critVal hd`: every point `ζ ∈ gdom`,
`ζ ≠ 0`, at which `deriv g ζ = 0`, is mapped by `g` to `π v`.  This is the statement that the
covering theorem of Lemma 6.1 is applied to the restriction of `g` to `gdom \ {critVal hd}`.

The mathematics is one line: for `ζ = π w`, `w ∈ B^u ∪ B^ℓ`, the chain rule of §6
(`Work.L61.Deriv.hasDerivAt_pushdown`) gives

  `g'(π w) = π(Ẽ w) · Ẽ'(w) / π w`,

and both factors `π(Ẽ w)`, `π w` are nonzero, so `g'(π w) = 0 ↔ Ẽ'(w) = 0`.  By `HornData.crit`
the latter means `Ẽ w = v + k` for some `k : ℤ`, and then
`g(π w) = π(Ẽ w) = π(v + k) = π v = critVal hd`.

The point `ζ = 0` of `gdom` is excluded by the hypothesis `hζ0`; indeed `HornData.g_deriv` gives
`g'(0) = 1 ≠ 0` (see `Work.L61.Deriv.deriv_ne_zero`).
-/

namespace Work.L61.Branch

open MandelDim Set Function Metric Filter
open scoped Topology

noncomputable section

variable {f₀ : ℂ → ℂ} {D₀ : Set ℂ}

/-- The chain rule of §6 at a point of `π(B^u ∪ B^ℓ)`: the derivative of the pushed-down horn map
is `π(Ẽ w) · Ẽ'(w) / π w`. -/
theorem deriv_g_piExp {d : ParabData f₀ D₀} (hd : HornData d) {w : ℂ}
    (hw : w ∈ hd.Bu ∪ hd.Bl) :
    deriv (Work.L61.g d) (piExp w) = piExp (d.E w) * deriv d.E w / piExp w := by
  have hT : IsTInvariant (hd.Bu ∪ hd.Bl) := fun v => by
    simp only [Set.mem_union, hd.Bu_T v, hd.Bl_T v]
  have heq : IsTEquivariantOn d.E (hd.Bu ∪ hd.Bl) :=
    ⟨hT, fun v hv => Work.L61.E_add_one d (hd.sub hv) (hd.sub ((hT v).mp hv))⟩
  have hdiffE : DifferentiableOn ℂ d.E (hd.Bu ∪ hd.Bl) :=
    (Work.L61.Deriv.differentiableOn_E d).mono hd.sub
  exact (Work.L61.Deriv.hasDerivAt_pushdown (E := d.E) (DR := hd.Bu ∪ hd.Bl)
    (hd.Bu_open.union hd.Bl_open) heq hdiffE hw).deriv

/-- **Lemma 6.1, critical-value part.**  Every critical point of the pushed-down horn map
`g = pushdown Ẽ_{f₀}` that lies in `gdom` and is different from `0` is mapped to the critical
value `critVal hd = π v`. -/
theorem deriv_eq_zero_imp_critVal {f₀ : ℂ → ℂ} {D₀ : Set ℂ} {d : MandelDim.ParabData f₀ D₀}
    (hd : MandelDim.HornData d) {ζ : ℂ} (hζ : ζ ∈ Work.L61.gdom d hd) (hζ0 : ζ ≠ 0)
    (h : deriv (Work.L61.g d) ζ = 0) : Work.L61.g d ζ = Work.L61.critVal hd := by
  rw [Work.L61.gdom, Set.mem_insert_iff] at hζ
  rcases hζ with h0 | hπ
  · exact absurd h0 hζ0
  · -- `ζ = π w` for some `w ∈ B^u ∪ B^ℓ`
    obtain ⟨w, hw, rfl⟩ := hπ
    have hval := deriv_g_piExp hd hw
    have hzero : piExp (d.E w) * deriv d.E w / piExp w = 0 := by rw [← hval]; exact h
    -- the numerator of the chain-rule formula vanishes, and `π(Ẽ w) ≠ 0`
    have hnum : piExp (d.E w) * deriv d.E w = 0 := by
      rcases div_eq_zero_iff.mp hzero with h' | h'
      · exact h'
      · exact absurd h' (Work.L61.piExp_ne_zero w)
    have hE0 : deriv d.E w = 0 :=
      (mul_eq_zero.mp hnum).resolve_left (Work.L61.piExp_ne_zero (d.E w))
    -- `Ẽ'(w) = 0` forces `Ẽ w = v + k`, hence `g (π w) = π v`
    obtain ⟨k, hk⟩ := hd.crit w hw hE0
    rw [Work.L61.g_piExp d hd hw, hk, Work.L61.piExp_add_intCast]
    rfl

end

end Work.L61.Branch
