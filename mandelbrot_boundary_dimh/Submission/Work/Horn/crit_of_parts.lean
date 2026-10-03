import Mathlib
import Submission.Work.Interfaces.HornParts

/-!
# HORN: the critical values of the lifted horn map `Ẽ = Φ₀ ∘ φ₀`

`crit_of_parts`: from the two covering theorems of Shishikura's Prop 5.3 -- `HornPhiStatement`
(local holomorphic sections of `Φ₀` over discs avoiding `Φ₀ c - ℕ`) and `HornVarphiStatement`
(local holomorphic sections of `φ₀` over discs around points of `B` off the forward critical
orbit) -- every critical value of `Ẽ = Φ₀ ∘ φ₀` on `BuOf d B ∪ BlOf d B` lies in `Φ₀ c + ℤ`.

The whole argument rests on one elementary fact (`deriv_ne_zero_of_local_section`): a local
holomorphic section of a holomorphic map `g` through `z` forces `deriv g z ≠ 0`.  On the domain
`DE` the chain rule `Ẽ' = Φ₀'∘φ₀ · φ₀'` holds (`deriv_E_eq`), so at a critical point `w` either

* `Φ₀'(φ₀ w) = 0`, and then `HornPhiStatement` forces `Φ₀ (φ₀ w) = Φ₀ c - n` for some `n ∈ ℕ`
  (the exceptional values of Claim A), i.e. `Ẽ w = Φ₀ c + k` with `k = -n`; or
* `Φ₀'(φ₀ w) ≠ 0`, so `φ₀'(w) = 0`, which `HornVarphiStatement` rules out unless `φ₀ w` lies on
  the forward critical orbit `{f₀^k c | k ≥ 1}`; there the Abel equation gives
  `Ẽ w = Φ₀ (f₀^k c) = Φ₀ c + k`, `k ≥ 1`.
-/

namespace Work.Horn

open Set Metric Filter
open scoped Topology

noncomputable section

variable {f₀ : ℂ → ℂ} {D₀ B : Set ℂ} {c : ℂ}

/-! ## Elementary tools -/

/-- The parabolic basin is open: a witness `U` of convergence can be re-used at every point of
`U`, so `U` itself is contained in the basin. -/
theorem basin_isOpen {f : ℂ → ℂ} {D : Set ℂ} : IsOpen (MandelDim.ParabolicBasin f D) := by
  rw [isOpen_iff_mem_nhds]
  rintro z ⟨U, hU, hiter, hconv⟩
  obtain ⟨V, hVU, hVopen, hzV⟩ := _root_.mem_nhds_iff.mp hU
  refine Filter.mem_of_superset (hVopen.mem_nhds hzV) ?_
  intro w hw
  exact ⟨V, hVopen.mem_nhds hw, fun n x hx => hiter n (hVU hx), hconv.mono hVU⟩

/-- A local holomorphic section of `g` through `z` forces `deriv g z ≠ 0`:
from `g ∘ σ = id` near `g z` and `σ (g z) = z` the chain rule gives
`deriv g z * deriv σ (g z) = 1`. -/
theorem deriv_ne_zero_of_local_section {g σ : ℂ → ℂ} {z : ℂ} {r : ℝ} (hr : 0 < r)
    (hg : DifferentiableAt ℂ g z) (hσ : DifferentiableAt ℂ σ (g z))
    (hid : ∀ u ∈ Metric.ball (g z) r, g (σ u) = u) (hσz : σ (g z) = z) :
    deriv g z ≠ 0 := by
  have hg' : DifferentiableAt ℂ g (σ (g z)) := by rwa [hσz]
  have h1 : deriv (g ∘ σ) (g z) = deriv g (σ (g z)) * deriv σ (g z) :=
    deriv_comp (g z) hg' hσ
  have heq : (g ∘ σ) =ᶠ[𝓝 (g z)] id := by
    filter_upwards [Metric.ball_mem_nhds (g z) hr] with u hu
    exact hid u hu
  have h2 : deriv (g ∘ σ) (g z) = 1 := by
    rw [Filter.EventuallyEq.deriv_eq heq, deriv_id]
  intro hzero
  rw [h1, hσz, hzero, zero_mul] at h2
  exact one_ne_zero h2.symm

/-! ## The chain rule for `Ẽ = Φ₀ ∘ φ₀` and the forward critical orbit -/

/-- The chain rule for the lifted horn map on its domain `DE`. -/
theorem deriv_E_eq (d : MandelDim.ParabData f₀ D₀) {w : ℂ} (hw : w ∈ d.DE) :
    deriv d.E w = deriv d.Φ (d.φ w) * deriv d.φ w := by
  obtain ⟨hw1, hw2⟩ := hw
  have hPhi : DifferentiableAt ℂ d.Φ (d.φ w) :=
    d.Φ_holo.differentiableAt (basin_isOpen.mem_nhds hw2)
  have hφ : DifferentiableAt ℂ d.φ w := d.φ_holo.differentiableAt (d.Dφ_open.mem_nhds hw1)
  exact deriv_comp w hPhi hφ

/-- The Abel equation along the forward orbit of a point of the immediate basin:
`Φ₀ ζ + n = Φ₀ (f₀^[n] ζ)`. -/
theorem Phi_iterate (d : MandelDim.ParabData f₀ D₀) {B : Set ℂ}
    (hBasin : MandelDim.IsImmediateBasin f₀ D₀ B) {ζ : ℂ} (hζ : ζ ∈ B) :
    ∀ n : ℕ, d.Φ ζ + n = d.Φ (f₀^[n] ζ) := by
  have hmem : ∀ n : ℕ, f₀^[n] ζ ∈ B := by
    intro n
    induction n with
    | zero => simpa using hζ
    | succ m ih => rw [Function.iterate_succ_apply']; exact hBasin.2.2.2.2.1 ih
  have hBsub : B ⊆ MandelDim.ParabolicBasin f₀ D₀ := hBasin.2.2.1
  intro n
  induction n with
  | zero => simp
  | succ m ih =>
      rw [Function.iterate_succ_apply', d.Φ_abel _ (hBsub (hmem m)), ← ih]
      push_cast
      ring

/-- The membership in `B̃ᵘ ∪ B̃ˡ` unfolds to membership in `φ₀ ⁻¹' B ∩ Dφ`. -/
theorem mem_Btil_of_mem_BuOf_union_BlOf {d : MandelDim.ParabData f₀ D₀} {w : ℂ}
    (hw : w ∈ MandelDim.BuOf d B ∪ MandelDim.BlOf d B) : w ∈ MandelDim.Btil d B := by
  rcases hw with hw | hw
  · exact connectedComponentIn_subset _ _ hw
  · exact connectedComponentIn_subset _ _ hw

/-! ## The two case inputs from Claims A and B -/

/-- Claim A (`HornPhiStatement`) at a point of the immediate basin: if `Φ₀ z` avoids the
exceptional values `Φ₀ c - n` (`n ∈ ℕ`), then `Φ₀'(z) ≠ 0`. -/
theorem deriv_Phi_ne_zero_of_ne_sub (hPhi : MandelDim.HornPhiStatement)
    (hsetup : MandelDim.IsF0Setup f₀ D₀ B c) {d : MandelDim.ParabData f₀ D₀} {z : ℂ}
    (hzB : z ∈ B) (hz : ∀ n : ℕ, d.Φ z ≠ d.Φ c - n) : deriv d.Φ z ≠ 0 := by
  have hBsub : B ⊆ MandelDim.ParabolicBasin f₀ D₀ := hsetup.2.1.2.2.1
  obtain ⟨-, hsec⟩ := hPhi f₀ D₀ B c d hsetup
  obtain ⟨r, hr, hsecr⟩ := hsec (d.Φ z) hz
  obtain ⟨σ, hσdiff, -, hσid, hσz⟩ :=
    hsecr z hzB (Metric.mem_ball_self hr)
  refine deriv_ne_zero_of_local_section hr ?_ ?_ hσid hσz
  · exact d.Φ_holo.differentiableAt (basin_isOpen.mem_nhds (hBsub hzB))
  · exact hσdiff.differentiableAt (Metric.ball_mem_nhds (d.Φ z) hr)

/-- Claim B (`HornVarphiStatement`): a point `w ∈ B̃ᵘ ∪ B̃ˡ` whose `φ₀`-image lies in the
immediate basin off the forward critical orbit has `φ₀'(w) ≠ 0`. -/
theorem deriv_varphi_ne_zero_of_not_critOrbit (hVarphi : MandelDim.HornVarphiStatement)
    (hsetup : MandelDim.IsF0Setup f₀ D₀ B c) {d : MandelDim.ParabData f₀ D₀} {w : ℂ}
    (hw : w ∈ MandelDim.BuOf d B ∪ MandelDim.BlOf d B)
    (hcrit : d.φ w ∉ MandelDim.critOrbit f₀ c) : deriv d.φ w ≠ 0 := by
  have hwDφ : w ∈ d.Dφ := (mem_Btil_of_mem_BuOf_union_BlOf hw).1
  have hwB : d.φ w ∈ B := (mem_Btil_of_mem_BuOf_union_BlOf hw).2
  obtain ⟨r, hr, -, hsecr⟩ := hVarphi f₀ D₀ B c d hsetup (d.φ w) hwB hcrit
  obtain ⟨σ, hσdiff, -, hσid, hσw⟩ := hsecr w hw (Metric.mem_ball_self hr)
  refine deriv_ne_zero_of_local_section hr ?_ ?_ hσid hσw
  · exact d.φ_holo.differentiableAt (d.Dφ_open.mem_nhds hwDφ)
  · exact hσdiff.differentiableAt (Metric.ball_mem_nhds (d.φ w) hr)

/-! ## The theorem -/

theorem crit_of_parts (hPhi : MandelDim.HornPhiStatement) (hVarphi : MandelDim.HornVarphiStatement) (f₀ : ℂ → ℂ) (D₀ B : Set ℂ) (c : ℂ) (d : MandelDim.ParabData f₀ D₀) (hsetup : MandelDim.IsF0Setup f₀ D₀ B c) : ∀ w ∈ MandelDim.BuOf d B ∪ MandelDim.BlOf d B, deriv d.E w = 0 → ∃ k : ℤ, d.E w = d.Φ c + k := by
  have hBasin : MandelDim.IsImmediateBasin f₀ D₀ B := hsetup.2.1
  have hBsub : B ⊆ MandelDim.ParabolicBasin f₀ D₀ := hsetup.2.1.2.2.1
  have hcB : c ∈ B := hsetup.2.2.1
  intro w hw hcrit
  have hwBtil : w ∈ MandelDim.Btil d B := mem_Btil_of_mem_BuOf_union_BlOf hw
  have hwDφ : w ∈ d.Dφ := hwBtil.1
  have hwB : d.φ w ∈ B := hwBtil.2
  have hwDE : w ∈ d.DE := ⟨hwDφ, hBsub hwB⟩
  have hchain : deriv d.E w = deriv d.Φ (d.φ w) * deriv d.φ w := deriv_E_eq d hwDE
  rw [hchain] at hcrit
  by_cases hcaseA : deriv d.Φ (d.φ w) = 0
  · by_cases hsub : ∃ n : ℕ, d.Φ (d.φ w) = d.Φ c - n
    · obtain ⟨n, hn⟩ := hsub
      refine ⟨-(n : ℤ), ?_⟩
      show d.Φ (d.φ w) = d.Φ c + ((-(n : ℤ) : ℤ) : ℂ)
      rw [hn]
      push_cast
      ring
    · push Not at hsub
      exact absurd ((deriv_Phi_ne_zero_of_ne_sub hPhi hsetup hwB hsub) hcaseA) not_false
  · have hφcrit : deriv d.φ w = 0 := by
      rcases mul_eq_zero.mp hcrit with h | h
      · exact absurd h hcaseA
      · exact h
    by_cases hco : d.φ w ∈ MandelDim.critOrbit f₀ c
    · obtain ⟨k, hk1, hk⟩ := hco
      refine ⟨(k : ℤ), ?_⟩
      have hiter := Phi_iterate d hBasin hcB k
      show d.Φ (d.φ w) = d.Φ c + ((k : ℤ) : ℂ)
      rw [hk, ← hiter]
      push_cast
      ring
    · exact absurd ((deriv_varphi_ne_zero_of_not_critOrbit hVarphi hsetup hw hco) hφcrit) not_false

end

end Work.Horn
