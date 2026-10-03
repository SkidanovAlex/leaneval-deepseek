import Mathlib
import Submission.Work.Interfaces.HornParts

/-!
# `deriv_iterate_ne_zero` — the derivative of an iterate is nonzero off the postcritical set

For `f₀ ∈ 𝓕₀` with immediate basin `B` and critical point `c` (`MandelDim.IsF0Setup`), every point
`z ∈ B` whose `n`-th iterate does not lie on the forward critical orbit `critOrbit f₀ c` is a
non-critical point of `f₀^[n]`.

Route: `f₀` is holomorphic on the open set `D₀ ⊇ B` and `B` is forward invariant, so the chain
rule applied inductively along the orbit gives

  `deriv (f₀^[n]) z = ∏_{j < n} deriv f₀ (f₀^[j] z)`   (`Work.HornVarphi.deriv_iterate_eq_prod`).

If the product vanished, some factor `deriv f₀ (f₀^[j] z)` (`j < n`) would vanish; since
`f₀^[j] z ∈ B` and `c` is the *unique* critical point of `f₀` in `B`, this forces
`f₀^[j] z = c`, and then `f₀^[n] z = f₀^[n-j] c` with `n - j ≥ 1` lies on the critical orbit,
contradiction.
-/

namespace Work.HornVarphi

open Set

/-- **Chain rule for iterates.**  If `f` maps `B` into itself, is complex-differentiable at every
point of `B`, and `z ∈ B`, then `deriv (f^[n]) z = ∏_{j < n} deriv f (f^[j] z)`. -/
theorem deriv_iterate_eq_prod {f : ℂ → ℂ} {B : Set ℂ} (hB : Set.MapsTo f B B)
    (hd : ∀ w ∈ B, DifferentiableAt ℂ f w) {z : ℂ} (hz : z ∈ B) (n : ℕ) :
    deriv (f^[n]) z = ∏ j ∈ Finset.range n, deriv f (f^[j] z) := by
  have hiter : ∀ j : ℕ, f^[j] z ∈ B := by
    intro j
    induction j with
    | zero => simpa using hz
    | succ k ih => rw [Function.iterate_succ_apply']; exact hB ih
  have main : ∀ n : ℕ, DifferentiableAt ℂ (f^[n]) z ∧
      deriv (f^[n]) z = ∏ j ∈ Finset.range n, deriv f (f^[j] z) := by
    intro n
    induction n with
    | zero =>
        refine ⟨differentiableAt_id, ?_⟩
        simp [Function.iterate_zero]
    | succ k ih =>
        obtain ⟨hdk, hdk'⟩ := ih
        refine ⟨?_, ?_⟩
        · have heq : (f^[k.succ]) = f ∘ (f^[k]) := by
            funext x; rw [Function.iterate_succ_apply']; rfl
          rw [heq]
          exact (hd (f^[k] z) (hiter k)).comp z hdk
        · rw [Function.iterate_succ', deriv_comp z (hd (f^[k] z) (hiter k)) hdk, hdk',
            Finset.prod_range_succ]
          ring
  exact (main n).2

/-- **The requested lemma.**  For `f₀ ∈ 𝓕₀` with immediate basin `B` and critical point `c`, a
point `z ∈ B` whose `n`-th iterate misses the postcritical set is not a critical point of
`f₀^[n]`. -/
theorem deriv_iterate_ne_zero {f₀ : ℂ → ℂ} {D₀ B : Set ℂ} {c : ℂ}
    (hS : MandelDim.IsF0Setup f₀ D₀ B c) (n : ℕ) {z : ℂ} (hz : z ∈ B)
    (hz' : f₀^[n] z ∉ MandelDim.critOrbit f₀ c) : deriv (f₀^[n]) z ≠ 0 := by
  have himm : MandelDim.IsImmediateBasin f₀ D₀ B := hS.2.1
  -- `B` is inside the domain of holomorphy of `f₀`: a basin point has a neighbourhood on which
  -- even the zeroth iterate `id` stays in `D₀`.
  have hBsubD : B ⊆ D₀ := by
    intro w hw
    obtain ⟨U, hU, hmaps, -⟩ := himm.2.2.1 hw
    simpa using hmaps 0 (mem_of_mem_nhds hU)
  have hDopen : IsOpen D₀ := hS.1.1
  have hfdiff : DifferentiableOn ℂ f₀ D₀ := hS.1.2.2.1
  have hBmaps : Set.MapsTo f₀ B B := himm.2.2.2.2.1
  have hderivB : ∀ w ∈ B, DifferentiableAt ℂ f₀ w := fun w hw =>
    hfdiff.differentiableAt (hDopen.mem_nhds (hBsubD hw))
  have hiter : ∀ j : ℕ, f₀^[j] z ∈ B := by
    intro j
    induction j with
    | zero => simpa using hz
    | succ k ih => rw [Function.iterate_succ_apply']; exact hBmaps ih
  have hprod := deriv_iterate_eq_prod hBmaps hderivB hz n
  intro hzero
  rw [hprod] at hzero
  obtain ⟨j, hjmem, hjzero⟩ := Finset.prod_eq_zero_iff.mp hzero
  have hjlt : j < n := Finset.mem_range.mp hjmem
  -- the `j`-th orbit point is a critical point of `f₀` inside `B`, hence it is `c`
  have hjc : f₀^[j] z = c := hS.2.2.2.2 (f₀^[j] z) (hiter j) hjzero
  apply hz'
  refine ⟨n - j, by omega, ?_⟩
  have hadd := Function.iterate_add_apply f₀ (n - j) j z
  rw [Nat.sub_add_cancel (le_of_lt hjlt)] at hadd
  rw [← hjc]
  exact hadd

end Work.HornVarphi
