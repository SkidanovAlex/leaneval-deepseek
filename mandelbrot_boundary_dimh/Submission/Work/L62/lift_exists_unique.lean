import Mathlib
import Submission.Work.L62.l62c_end
import Submission.Work.L62.avail_up
import Submission.Work.L62.l62c_basic
import Submission.Work.Horn.basic

/-!
# `Work.L62.lift_exists_unique` — the lift of `π` through `ĥ = Ẽ - β` is unique

Let `d : ParabData g₀ D` with horn data `hd`, let `β : ℂ`, and let

`ĥ = fun u => d.E u - β`,  `G = pushdown ĥ`

be the lifted level chart and its descent to the cylinder `ℂ/ℤ ≅ ℂ*`.  For `ζ ∈ Ω = {0} ∪ π '' Bu`
with `G ζ = π w`, `w ∈ hd.Bu`, the lift of `ζ` in the horn `Bu` is *unique*:

`∃! u, u ∈ hd.Bu ∧ π u = ζ ∧ d.E u = w + β`.

Note first that `ζ ≠ 0`: `pushdown` is literally `0` at `0` (`Work.Horn.MandelDim.pushdown_zero`)
whereas `π w = piExp w` never vanishes (`Work.Horn.MandelDim.piExp_ne_zero`).  So
`ζ = π u₀` for some `u₀ ∈ hd.Bu` (`Ω = insert 0 (π '' Bu)`), and pushing down with
`Work.Horn.MandelDim.pushdown_piExp` (the equivariance `d.E (u+1) = d.E u + 1` on `Bu` is
`E_add_one_Bu`) turns the hypothesis into `π (d.E u₀ - β) = π w`, i.e. by
`Work.Horn.MandelDim.piExp_eq_iff`

`d.E u₀ - β = w + m`  for some `m : ℤ`.

Integer shifts are absorbed by the `T`-invariance of `Bu` and the equivariance of `d.E`
(`Work.Horn.MandelDim.IsTInvariant.add_int`, `Work.Horn.MandelDim.E_add_int`): all lifts of `ζ`
in `Bu` are the points `u₀ + k`, `k : ℤ`, and `d.E (u₀ + k) = d.E u₀ + k`.  Hence

* **existence**: `u := u₀ - m` lies in `Bu`, still lifts `ζ` (`piExp_add_intCast`), and
  `d.E u = d.E u₀ - m = w + β`;
* **uniqueness**: two solutions have equal `π`-image, so differ by an integer `k`; their
  `d.E`-images then differ by that same `k`, and being both equal to `w + β` this forces
  `k = 0`.

The lemma is exactly the statement that the section `σ` of `ĥ` over `Bu` and the projection `π`
fit together into a bijection between `Bu` and the cylinder: `π` is a bijection on each `ĥ`-fibre
of `Bu`.
-/

namespace Work.L62

theorem lift_exists_unique {g₀ : ℂ → ℂ} {D : Set ℂ} (d : MandelDim.ParabData g₀ D)
    (hd : MandelDim.HornData d) {β w ζ : ℂ} (hw : w ∈ hd.Bu)
    (hζ : ζ ∈ Work.L62.upOmega d hd)
    (hG : MandelDim.pushdown (fun u => d.E u - β) ζ = MandelDim.piExp w) :
    ∃! u : ℂ, u ∈ hd.Bu ∧ MandelDim.piExp u = ζ ∧ d.E u = w + β := by
  -- `pushdown` vanishes at `0`, so `hG` forces `ζ ≠ 0`
  have hζne : ζ ≠ 0 := by
    intro h0
    rw [h0, Work.Horn.MandelDim.pushdown_zero] at hG
    exact Work.Horn.MandelDim.piExp_ne_zero w hG.symm
  -- a lift `u₀ ∈ Bu` of `ζ`
  obtain ⟨u₀, hu₀, hπu₀⟩ : ∃ u₀ ∈ hd.Bu, MandelDim.piExp u₀ = ζ := by
    rcases Set.mem_insert_iff.mp hζ with h | h
    · exact absurd h hζne
    · obtain ⟨u₀, hu₀, hu₀π⟩ := h
      exact ⟨u₀, hu₀, hu₀π⟩
  -- `ĥ = d.E - β` is `T`-equivariant on `Bu`
  have hEq : ∀ u ∈ hd.Bu, u + 1 ∈ hd.Bu →
      (fun u => d.E u - β) (u + 1) = (fun u => d.E u - β) u + 1 := by
    intro u hu _
    show d.E (u + 1) - β = d.E u - β + 1
    rw [E_add_one_Bu d hd hu]
    ring
  -- integer shifts of `d.E` on `Bu`
  have hint : ∀ u ∈ hd.Bu, ∀ k : ℤ, d.E (u + (k : ℂ)) = d.E u + (k : ℂ) := by
    intro u hu k
    have h := Work.Horn.MandelDim.E_add_int (E := fun u => d.E u - β) hd.Bu_T hEq hu k
    linear_combination h
  -- the hypothesis, pushed down at `u₀`
  have hG' : MandelDim.piExp (d.E u₀ - β) = MandelDim.piExp w := by
    rw [← hπu₀, Work.Horn.MandelDim.pushdown_piExp hd.Bu_T hEq hu₀] at hG
    exact hG
  obtain ⟨m, hm⟩ := Work.Horn.MandelDim.piExp_eq_iff.mp hG'
  -- uniqueness: two solutions of the same `π`-image and the same `d.E`-image coincide
  have huniq : ∀ v₁ v₂ : ℂ, v₁ ∈ hd.Bu → MandelDim.piExp v₁ = ζ → d.E v₁ = w + β →
      v₂ ∈ hd.Bu → MandelDim.piExp v₂ = ζ → d.E v₂ = w + β → v₁ = v₂ := by
    intro v₁ v₂ _ hπ₁ hE₁ hv₂ hπ₂ hE₂
    obtain ⟨k, hk⟩ := Work.Horn.MandelDim.piExp_eq_iff.mp (hπ₁.trans hπ₂.symm)
    have hshift := hint v₂ hv₂ k
    rw [hk] at hE₁
    have h1 : d.E v₂ + (k : ℂ) = w + β := by rw [← hshift, hE₁]
    have hk0 : (k : ℂ) = 0 := by linear_combination h1 - hE₂
    have hk0' : k = 0 := Int.cast_eq_zero.mp hk0
    rw [hk, hk0']
    simp
  -- existence: shift `u₀` by `-m`
  have hwit : u₀ + ((-m : ℤ) : ℂ) ∈ hd.Bu ∧ MandelDim.piExp (u₀ + ((-m : ℤ) : ℂ)) = ζ ∧
      d.E (u₀ + ((-m : ℤ) : ℂ)) = w + β := by
    refine ⟨Work.Horn.MandelDim.IsTInvariant.add_int hd.Bu_T hu₀ (-m), ?_, ?_⟩
    · rw [Work.Horn.MandelDim.piExp_add_intCast u₀ (-m), hπu₀]
    · rw [hint u₀ hu₀ (-m)]
      push_cast
      linear_combination hm
  exact ⟨u₀ + ((-m : ℤ) : ℂ), hwit,
    fun v hv => huniq v (u₀ + ((-m : ℤ) : ℂ)) hv.1 hv.2.1 hv.2.2 hwit.1 hwit.2.1 hwit.2.2⟩

end Work.L62
