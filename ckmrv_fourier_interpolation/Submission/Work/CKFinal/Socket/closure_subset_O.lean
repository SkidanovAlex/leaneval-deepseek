/-
# `closure 𝒟 ⊆ O` for the socket construction

`O = U₀ ∪ W₁ ∪ W₋₁` (`Socket.O`) is the open set on which the socket layer `F₂` is defined;
`exists_F2_socket` needs `closure 𝒟 ⊆ O` (CKMRV Proposition 4.6: the contour integral converges on
the closure of the `Γ(2)`-domain `𝒟`).

The closure of `𝒟 = {-1 < Re z < 1, |z ∓ 1/2| > 1/2}` differs from `𝒟` only by points of the two
vertical lines `Re z = ±1`:

* `𝒟 ⊆ U₀` (`Socket.DomainD_subset_U0`), i.e. `𝒟` never comes within `1/4` of `±1/4`, `±3/4`;
* a limit point of `𝒟` in the strip `-1 < Re z < 1` stays outside the closed discs of radius `1/2`
  (the defining conditions of `𝒟` are closed), and outside those discs plus `-1 < Re < 1` is
  exactly `U₀`.  Concretely, `|τ ∓ 1/2| ≥ 1/2` gives `|Re τ| ≤ Re τ² + Im τ²`, and the two pure
  real lemmas below turn that into the four strict disc conditions of `U₀`.
* the whole line `Re τ = 1` lies in `W₁` (`Socket.re_eq_one_mem_W1`: every such point is a window
  centre), and the whole line `Re τ = -1` lies in `W₋₁`
  (`Socket.re_eq_neg_one_mem_Wm1`: shift by `1` to the imaginary axis, which lies in `U₀`, and by
  `2` onto the line `Re = 1`, which lies in `W₁`).
-/
import Mathlib
import Submission.Work.CKFinal.Socket.Region
import Submission.Work.CKFinal.Socket.mem_U0_of_re_nonneg
import Submission.Work.CKFinal.Socket.mem_U0_of_re_nonpos
import Submission.Work.CKFinal.Socket.re_eq_neg_one_mem_Wm1

noncomputable section

open UpperHalfPlane
open scoped Topology Manifold

namespace Work.CKFinal
namespace Socket

/-- `‖τ - 1/2‖²` in coordinates. -/
private lemma norm_coe_sub_half_sq (τ : ℍ) :
    ‖(τ : ℂ) - (1 / 2 : ℂ)‖ ^ 2 = (τ.re - 1 / 2) ^ 2 + τ.im ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
  norm_num
  ring

/-- `‖τ + 1/2‖²` in coordinates. -/
private lemma norm_coe_add_half_sq (τ : ℍ) :
    ‖(τ : ℂ) + (1 / 2 : ℂ)‖ ^ 2 = (τ.re + 1 / 2) ^ 2 + τ.im ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
  norm_num
  ring

/-- Everything in the closure of `𝒟` either lies in `U₀` or on one of the two vertical lines
`Re τ = ±1` (which are the only points of the boundary of `𝒟` not already covered by `U₀`). -/
lemma closure_DomainD_subset_lines :
    closure Work.Asymptotics.DomainD ⊆ U0 ∪ {τ : ℍ | τ.re = 1} ∪ {τ : ℍ | τ.re = -1} := by
  intro τ hτ
  -- the four defining conditions of `𝒟` are closed, hence pass to the closure
  have hge : -1 ≤ τ.re :=
    closure_minimal (fun z hz => le_of_lt hz.1)
      (isClosed_le continuous_const UpperHalfPlane.continuous_re) hτ
  have hle : τ.re ≤ 1 :=
    closure_minimal (fun z hz => le_of_lt hz.2.1)
      (isClosed_le UpperHalfPlane.continuous_re continuous_const) hτ
  have hc1 : τ ∈ {z : ℍ | (1 / 2 : ℝ) ≤ ‖(z : ℂ) - (1 / 2 : ℂ)‖} :=
    closure_minimal (fun z hz => le_of_lt hz.2.2.1)
      (isClosed_le continuous_const (by fun_prop)) hτ
  have hc2 : τ ∈ {z : ℍ | (1 / 2 : ℝ) ≤ ‖(z : ℂ) + (1 / 2 : ℂ)‖} :=
    closure_minimal (fun z hz => le_of_lt hz.2.2.2)
      (isClosed_le continuous_const (by fun_prop)) hτ
  -- `|τ - 1/2| ≥ 1/2` says `Re τ ≤ Re τ² + Im τ²`, `|τ + 1/2| ≥ 1/2` says `-Re τ ≤ …`
  have hP1 : τ.re ≤ τ.re ^ 2 + τ.im ^ 2 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) hc1 2
    rw [norm_coe_sub_half_sq] at h
    nlinarith [h]
  have hP2 : -τ.re ≤ τ.re ^ 2 + τ.im ^ 2 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) hc2 2
    rw [norm_coe_add_half_sq] at h
    nlinarith [h]
  simp only [Set.mem_union, Set.mem_ofPred_eq]
  rcases lt_trichotomy τ.re 1 with h1 | h1 | h1
  · rcases lt_trichotomy τ.re (-1) with h2 | h2 | h2
    · exact absurd hge (not_le.mpr h2)
    · exact Or.inr h2
    · rcases lt_or_ge 0 τ.re with hpos | hnonpos
      · exact Or.inl (Or.inl (mem_U0_of_re_nonneg h2 h1 hpos hP1))
      · exact Or.inl (Or.inl (mem_U0_of_re_nonpos h2 h1 hnonpos hP2))
  · exact Or.inl (Or.inr h1)
  · exact absurd hle (not_le.mpr h1)

/-- **The closure of `𝒟` lies in the socket region `O = U₀ ∪ W₁ ∪ W₋₁`.** -/
theorem closure_subset_O (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    closure Work.Asymptotics.DomainD ⊆ Work.CKFinal.Socket.O ℓ d hd := by
  intro τ hτ
  have h := closure_DomainD_subset_lines hτ
  simp only [O, Set.mem_union, Set.mem_ofPred_eq] at h ⊢
  rcases h with (hU0 | h1) | hm1
  · exact Or.inl (Or.inl hU0)
  · exact Or.inl (Or.inr (re_eq_one_mem_W1 ℓ d hd τ h1))
  · exact Or.inr (re_eq_neg_one_mem_Wm1 ℓ d hd τ hm1)

end Socket
end Work.CKFinal
