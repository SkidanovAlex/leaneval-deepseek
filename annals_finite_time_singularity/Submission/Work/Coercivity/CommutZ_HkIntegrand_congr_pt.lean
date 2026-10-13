/-
# Pointwise congruence of the `H^k` integrand

The `H^k` integrand `HkIntegrand α n f z θ` is built out of the iterated
derivatives `D_z^i f = (z∂_z)^i f` and `D_z^j D_θ^i f = (z∂_z)^j (sin 2θ ∂_θ)^i f`
of `f`, together with weights depending only on `(z,θ)`.  Consequently it is a
*local* functional of `f`:

> if two functions `u`, `v` agree on `(0,∞) × [0,π/2]`, then for every interior
> point `z > 0`, `0 < θ < π/2` one has `HkIntegrand α n u z θ = HkIntegrand α n v z θ`.

The proof is a straightforward induction: derivatives of functions agreeing on a
neighbourhood of the point agree (`Filter.EventuallyEq.deriv_eq`), and both `D_z`
and `D_θ` are a fixed multiplier times such a derivative.
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.Coercivity.CommutZBase

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Coercivity

open scoped Real Topology
open MeasureTheory Set Filter

open Work.Spaces

/-- If `a` and `b` agree on `(0,∞) × [0,π/2]`, then `D_z a` and `D_z b` agree there. -/
private lemma Dz_congr_Iθ {a b : ℝ → ℝ → ℝ}
    (h : ∀ z ∈ Set.Ioi 0, ∀ θ ∈ Iθ, a z θ = b z θ) :
    ∀ z ∈ Set.Ioi 0, ∀ θ ∈ Iθ, Dz a z θ = Dz b z θ := by
  intro z hz θ hθ
  have hev : (fun z' => a z' θ) =ᶠ[𝓝 z] (fun z' => b z' θ) := by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
    exact h z' hz' θ hθ
  simp only [Dz, pz]
  rw [hev.deriv_eq]

/-- If `a` and `b` agree on `(0,∞) × (0,π/2)`, then `D_z a` and `D_z b` agree there. -/
private lemma Dz_congr_Ioo {a b : ℝ → ℝ → ℝ}
    (h : ∀ z ∈ Set.Ioi 0, ∀ θ ∈ Set.Ioo 0 (π / 2), a z θ = b z θ) :
    ∀ z ∈ Set.Ioi 0, ∀ θ ∈ Set.Ioo 0 (π / 2), Dz a z θ = Dz b z θ := by
  intro z hz θ hθ
  have hev : (fun z' => a z' θ) =ᶠ[𝓝 z] (fun z' => b z' θ) := by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
    exact h z' hz' θ hθ
  simp only [Dz, pz]
  rw [hev.deriv_eq]

/-- If `a` and `b` agree on `(0,∞) × (0,π/2)`, then `D_θ a` and `D_θ b` agree there. -/
private lemma Dth_congr_Ioo {a b : ℝ → ℝ → ℝ}
    (h : ∀ z ∈ Set.Ioi 0, ∀ θ ∈ Set.Ioo 0 (π / 2), a z θ = b z θ) :
    ∀ z ∈ Set.Ioi 0, ∀ θ ∈ Set.Ioo 0 (π / 2), Dth a z θ = Dth b z θ := by
  intro z hz θ hθ
  have hev : (fun θ' => a z θ') =ᶠ[𝓝 θ] (fun θ' => b z θ') := by
    filter_upwards [isOpen_Ioo.mem_nhds hθ] with θ' hθ'
    exact h z hz θ' hθ'
  simp only [Dth, pth]
  rw [hev.deriv_eq]

/-- Iterated `D_z` congruence on `(0,∞) × [0,π/2]`. -/
private lemma DzIter_congr_Iθ {u v : ℝ → ℝ → ℝ}
    (h : ∀ z ∈ Set.Ioi 0, ∀ θ ∈ Iθ, u z θ = v z θ) :
    ∀ i, ∀ z ∈ Set.Ioi 0, ∀ θ ∈ Iθ, DzIter i u z θ = DzIter i v z θ := by
  intro i
  induction i with
  | zero => intro z hz θ hθ; simpa using h z hz θ hθ
  | succ i ih =>
      intro z hz θ hθ
      simp only [DzIter_succ]
      exact Dz_congr_Iθ ih z hz θ hθ

/-- Iterated `D_θ` congruence on `(0,∞) × (0,π/2)`. -/
private lemma DthIter_congr_Ioo {u v : ℝ → ℝ → ℝ}
    (h : ∀ z ∈ Set.Ioi 0, ∀ θ ∈ Set.Ioo 0 (π / 2), u z θ = v z θ) :
    ∀ i, ∀ z ∈ Set.Ioi 0, ∀ θ ∈ Set.Ioo 0 (π / 2), DthIter i u z θ = DthIter i v z θ := by
  intro i
  induction i with
  | zero => intro z hz θ hθ; simpa using h z hz θ hθ
  | succ i ih =>
      intro z hz θ hθ
      simp only [DthIter_succ]
      exact Dth_congr_Ioo ih z hz θ hθ

/-- Mixed iterated derivatives agree on `(0,∞) × (0,π/2)`. -/
private lemma mixed_congr_Ioo {u v : ℝ → ℝ → ℝ}
    (h : ∀ z ∈ Set.Ioi 0, ∀ θ ∈ Set.Ioo 0 (π / 2), u z θ = v z θ) :
    ∀ j i, ∀ z ∈ Set.Ioi 0, ∀ θ ∈ Set.Ioo 0 (π / 2),
      mixed j i u z θ = mixed j i v z θ := by
  intro j
  induction j with
  | zero =>
      intro i z hz θ hθ
      simpa only [mixed_zero_left] using DthIter_congr_Ioo h i z hz θ hθ
  | succ j ih =>
      intro i z hz θ hθ
      have hD := Dz_congr_Ioo (ih i) z hz θ hθ
      simpa only [mixed, DzIter_succ] using hD

theorem CommutZ_HkIntegrand_congr_pt (α : ℝ) (n : ℕ) (u v : ℝ → ℝ → ℝ)
    (h : ∀ z ∈ Set.Ioi 0, ∀ θ ∈ Work.Spaces.Iθ, u z θ = v z θ) :
    ∀ z ∈ Set.Ioi 0, ∀ θ ∈ Set.Ioo 0 (π / 2),
      Work.Spaces.HkIntegrand α n u z θ = Work.Spaces.HkIntegrand α n v z θ := by
  intro z hz θ hθ
  have hθIθ : θ ∈ Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hIoo : ∀ z' ∈ Set.Ioi 0, ∀ θ' ∈ Set.Ioo 0 (π / 2), u z' θ' = v z' θ' :=
    fun z' hz' θ' hθ' => h z' hz' θ' ⟨le_of_lt hθ'.1, le_of_lt hθ'.2⟩
  have hDz : ∀ i, DzIter i u z θ = DzIter i v z θ :=
    fun i => DzIter_congr_Iθ h i z hz θ hθIθ
  have hmx : ∀ j i, mixed j i u z θ = mixed j i v z θ :=
    fun j i => mixed_congr_Ioo hIoo j i z hz θ hθ
  simp only [HkIntegrand]
  congr 1
  · exact Finset.sum_congr rfl (fun i _ => by rw [hDz i])
  · exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by
      split_ifs with hc
      · rw [hmx j i]
      · rfl))

end Work.Coercivity
