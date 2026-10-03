import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Horn.basic
import Submission.Work.Parab.inversion.deriv_ne_zero_of_injOn
import Submission.Work.Horn.deriv_phi_ne_zero_of_noncrit

/-!
# AREA HORN: the critical value of the horn map is unique

Shishikura, *The Hausdorff dimension of the boundary of the Mandelbrot set* (arXiv math/9201282),
Proposition 5.3: the pushed-down horn map `𝒞_{f₀} : Bᵘ ∪ B^ℓ → ℂ^*` is ramified over exactly one
point `v = π ∘ Φ₀(c)`, `c` the unique critical point of `f₀` in the immediate basin `B`.

In lifted coordinates (`π = MandelDim.piExp`, `Ẽ = d.E = Φ₀ ∘ φ₀`) this says: *all* critical points
`w` of `Ẽ` in the upper half plane (`η < Im w`, so `w ∈ B̃ᵘ`) push down to the same point
`π (Ẽ w) = π (Φ₀ c)`.

The proof is the chain rule `Ẽ'(w) = Φ₀'(φ₀ w) · φ₀'(w)` together with the two structure theorems
for the two factors.

* `φ₀'(w) = 0` (case A).  Then Lemma 5.1 (`ParabData.invOrbit`) applied to the backward orbit
  `z_j = φ₀(w - j)` produces a backward iterate `φ₀(w - j)` which *is* a critical point of `f₀`;
  by `hback` all these points lie in the immediate basin `B`, hence equal the unique critical point
  `c` (`hcB`), and `Ẽ w = Φ₀ c + j`.

* `Φ₀'(φ₀ w) = 0` (case B).  Since `hback` also makes `z_1 = φ₀(w - 1)` lie in `B`, it suffices to
  know that *every* critical point of `Φ₀` inside `B` lies in the backward orbit of `c`.  That is
  `critval_Phi_crit_in_B` below: an orbit from `ζ ∈ B` stays in `B` (`MapsTo f₀ B B`), so it never
  meets `0` (`0 ∉ ParabolicBasin`, because `Φ₀` itself would satisfy `Φ₀ 0 = Φ₀ 0 + 1`), hence
  enters the attracting petal `Ω₊` (`ParabData.basin_enter`); differentiating `Φ₀ ∘ f₀ = Φ₀ + 1`
  along the orbit, criticality of `Φ₀` is propagated forward as long as `f₀` is not critical, so the
  orbit must meet a critical point of `f₀` — i.e. `c` — before reaching `Ω₊`.  On `Ω₊`, `Φ₀` is
  injective (`ParabData.Φ_inj`) and holomorphic, hence `Φ₀' ≠ 0` there
  (`Work.Parab.inversion.deriv_ne_zero_of_injOn`).
-/

namespace Work.Horn

open MandelDim Filter Topology Metric
open scoped Topology

noncomputable section

/-! ## Elementary facts about the parabolic basin defined by the interface -/

/-- The parabolic basin is open: shrink a witness of convergence to its interior. -/
theorem critval_basin_isOpen {f : ℂ → ℂ} {D : Set ℂ} :
    IsOpen (MandelDim.ParabolicBasin f D) := by
  rw [isOpen_iff_mem_nhds]
  intro z hz
  obtain ⟨U, hU, hiter, hconv⟩ := hz
  refine Filter.mem_of_superset (interior_mem_nhds.mpr hU) ?_
  intro w hw
  exact ⟨U, Filter.mem_of_superset (isOpen_interior.mem_nhds hw) interior_subset, hiter, hconv⟩

/-- A point of the parabolic basin lies in the domain of definition of `f`. -/
theorem critval_basin_subset {f : ℂ → ℂ} {D : Set ℂ} :
    MandelDim.ParabolicBasin f D ⊆ D := by
  intro z hz
  obtain ⟨U, hU, hiter, -⟩ := hz
  exact hiter 0 (mem_of_mem_nhds hU)

/-- `0` is not in the parabolic basin: the Abel equation `Φ (f z) = Φ z + 1` at the fixed point
would give `Φ 0 = Φ 0 + 1`. -/
theorem critval_zero_notMem_basin {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (hF0 : MandelDim.InF0 f₀ D₀)
    (d : MandelDim.ParabData f₀ D₀) : (0 : ℂ) ∉ MandelDim.ParabolicBasin f₀ D₀ := by
  intro h0
  have hf0 : f₀ 0 = 0 := hF0.1.2.2.2.1
  have h := d.Φ_abel 0 h0
  rw [hf0] at h
  have h' : d.Φ 0 + 0 = d.Φ 0 + 1 := by rw [add_zero]; exact h
  exact zero_ne_one (add_left_cancel h')

/-! ## The chain rule for `Ẽ` and the propagated relation for `Φ₀` -/

/-- **The Abel relation differentiated**: for `u` and `f₀ u` in the basin,
`Φ₀'(f₀ u) · f₀'(u) = Φ₀'(u)`.  (`Φ₀ ∘ f₀` agrees with the translation `· + 1` on the open set
`basin` containing `u`.) -/
theorem critval_deriv_Phi_comp {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (hF0 : MandelDim.InF0 f₀ D₀)
    (d : MandelDim.ParabData f₀ D₀) {u : ℂ}
    (hu : u ∈ MandelDim.ParabolicBasin f₀ D₀)
    (hu' : f₀ u ∈ MandelDim.ParabolicBasin f₀ D₀) :
    deriv d.Φ (f₀ u) * deriv f₀ u = deriv d.Φ u := by
  have hDopen : IsOpen D₀ := hF0.1.1
  have hfd : DifferentiableOn ℂ f₀ D₀ := hF0.1.2.2.1
  have hfu : DifferentiableAt ℂ f₀ u :=
    hfd.differentiableAt (hDopen.mem_nhds (critval_basin_subset hu))
  have hPhi : DifferentiableAt ℂ d.Φ (f₀ u) :=
    d.Φ_holo.differentiableAt (critval_basin_isOpen.mem_nhds hu')
  have heq : (d.Φ ∘ f₀) =ᶠ[𝓝 u] (fun v => d.Φ v + 1) :=
    Filter.eventually_of_mem (critval_basin_isOpen.mem_nhds hu) (fun v hv => d.Φ_abel v hv)
  have h1 : deriv (d.Φ ∘ f₀) u = deriv d.Φ (f₀ u) * deriv f₀ u := deriv_comp u hPhi hfu
  calc deriv d.Φ (f₀ u) * deriv f₀ u = deriv (d.Φ ∘ f₀) u := h1.symm
    _ = deriv (fun v => d.Φ v + 1) u := Filter.EventuallyEq.deriv_eq heq
    _ = deriv d.Φ u := by simp

/-- The chain rule for the lifted horn map `Ẽ = Φ₀ ∘ φ₀` on its domain. -/
theorem critval_deriv_E {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀) {w : ℂ}
    (hw : w ∈ d.DE) : deriv d.E w = deriv d.Φ (d.φ w) * deriv d.φ w := by
  have hw' : w ∈ d.Dφ ∧ d.φ w ∈ MandelDim.ParabolicBasin f₀ D₀ := hw
  have hPhi : DifferentiableAt ℂ d.Φ (d.φ w) :=
    d.Φ_holo.differentiableAt (critval_basin_isOpen.mem_nhds hw'.2)
  have hφ : DifferentiableAt ℂ d.φ w := d.φ_holo.differentiableAt (d.Dφ_open.mem_nhds hw'.1)
  exact deriv_comp w hPhi hφ

/-! ## Two bookkeeping lemmas for the Fatou coordinate -/

/-- Along the forward orbit of a point of the immediate basin, `Φ₀` increases by `1` at each step:
`Φ₀ ζ + n = Φ₀ (f₀^[n] ζ)`. -/
theorem critval_Phi_iterate {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀)
    {B : Set ℂ} (hB : MandelDim.IsImmediateBasin f₀ D₀ B) {ζ : ℂ} (hζ : ζ ∈ B) :
    ∀ n : ℕ, d.Φ ζ + n = d.Φ (f₀^[n] ζ) := by
  have hmem : ∀ n : ℕ, f₀^[n] ζ ∈ B := by
    intro n
    induction n with
    | zero => simpa using hζ
    | succ m ih => rw [Function.iterate_succ_apply']; exact hB.2.2.2.2.1 ih
  have hBsub : B ⊆ MandelDim.ParabolicBasin f₀ D₀ := hB.2.2.1
  intro n
  induction n with
  | zero => simp
  | succ m ih =>
      rw [Function.iterate_succ_apply', d.Φ_abel _ (hBsub (hmem m)), ← ih]
      push_cast
      ring

/-- The backward orbit of `φ₀`: `f₀^[n] (φ₀ (w - j)) = φ₀ (w - (j - n))` for `n ≤ j`, so the
`j`-th iterate of `φ₀ (w - j)` is `φ₀ w`. -/
theorem critval_f_iterate_phi_sub {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀)
    {w : ℂ} (hw : w ∈ d.Dφ) :
    ∀ j n : ℕ, n ≤ j → f₀^[n] (d.φ (w - (j : ℂ))) = d.φ (w - ((j - n : ℕ) : ℂ)) := by
  have hsubDφ : ∀ j : ℕ, w - (j : ℂ) ∈ d.Dφ := by
    intro j
    induction j with
    | zero => simpa using hw
    | succ m ih =>
        have : w - ((m + 1 : ℕ) : ℂ) = (w - (m : ℂ)) - 1 := by push_cast; ring
        rw [this]; exact d.left_inv _ ih
  intro j n hnj
  induction n with
  | zero => simp
  | succ m ih =>
      have hmj : m ≤ j := by omega
      rw [Function.iterate_succ_apply', ih hmj]
      have h1 : ((j - m : ℕ) : ℂ) = ((j - (m + 1) : ℕ) : ℂ) + 1 := by
        have hnat : j - m = (j - (m + 1)) + 1 := by omega
        rw [hnat]; push_cast; ring
      rw [h1]
      have h2 : w - (((j - (m + 1) : ℕ) : ℂ) + 1) = (w - ((j - (m + 1) : ℕ) : ℂ)) - 1 := by ring
      rw [h2]
      have hmem1 : (w - ((j - (m + 1) : ℕ) : ℂ)) - 1 ∈ d.Dφ := by
        rw [← h2]
        have : w - (((j - (m + 1) : ℕ) : ℂ) + 1) = w - ((j - m : ℕ) : ℂ) := by rw [h1]
        rw [this]; exact hsubDφ (j - m)
      have hmem2 : ((w - ((j - (m + 1) : ℕ) : ℂ)) - 1) + 1 ∈ d.Dφ := by
        rw [sub_add_cancel]; exact hsubDφ (j - (m + 1))
      have h := d.φ_abel ((w - ((j - (m + 1) : ℕ) : ℂ)) - 1) hmem1 hmem2
      rw [sub_add_cancel] at h
      exact h.symm

/-- Shifting a complex number by an integer does not change its `π`-image. -/
theorem critval_piExp_shift {u v : ℂ} {k : ℤ} (h : u = v + (k : ℂ)) :
    MandelDim.piExp u = MandelDim.piExp v := by
  rw [h, Work.Horn.MandelDim.piExp_add_intCast]

/-! ## Critical points of `Φ₀` inside the immediate basin -/

/-- **The critical points of `Φ₀` in the immediate basin are backward iterates of `c`.**
If `ζ ∈ B` and `Φ₀'(ζ) = 0`, then `f₀^[k] ζ = c` for some `k`, and `Φ₀ ζ = Φ₀ c - k`.

The only analytic input is `hOm : Φ₀' ≠ 0` on the attracting petal `Ω₊` (which holds because `Φ₀`
is injective there).  All the dynamical input is `MapsTo f₀ B B`, `0 ∉ B` and
`ParabData.basin_enter`. -/
theorem critval_Phi_crit_in_B {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀)
    (hF0 : MandelDim.InF0 f₀ D₀) {B : Set ℂ} (hB : MandelDim.IsImmediateBasin f₀ D₀ B)
    (_hcB : ∃! c : ℂ, c ∈ B ∧ deriv f₀ c = 0)
    (hOm : ∀ y ∈ d.Ωp, deriv d.Φ y ≠ 0)
    {ζ : ℂ} (hζ : ζ ∈ B) (hcrit : deriv d.Φ ζ = 0) :
    ∃ k : ℕ, f₀^[k] ζ ∈ B ∧ deriv f₀ (f₀^[k] ζ) = 0 ∧ d.Φ ζ + k = d.Φ (f₀^[k] ζ) := by
  have hmem : ∀ n : ℕ, f₀^[n] ζ ∈ B := by
    intro n
    induction n with
    | zero => simpa using hζ
    | succ m ih => rw [Function.iterate_succ_apply']; exact hB.2.2.2.2.1 ih
  have hBsub : B ⊆ MandelDim.ParabolicBasin f₀ D₀ := hB.2.2.1
  have hzero : (0 : ℂ) ∉ B := fun h => critval_zero_notMem_basin hF0 d (hBsub h)
  have hne : ∀ n : ℕ, f₀^[n] ζ ≠ 0 := fun n h => hzero (h ▸ hmem n)
  obtain ⟨n, hn⟩ := d.basin_enter ζ (hBsub hζ) hne
  by_cases hcase : ∃ m : ℕ, m < n ∧ deriv f₀ (f₀^[m] ζ) = 0
  · obtain ⟨m, -, hmcrit⟩ := hcase
    exact ⟨m, hmem m, hmcrit, critval_Phi_iterate d hB hζ m⟩
  · push Not at hcase
    have hd : ∀ k : ℕ, k ≤ n → deriv d.Φ (f₀^[k] ζ) = 0 := by
      intro k
      induction k with
      | zero => intro _; simpa using hcrit
      | succ m ih =>
          intro hm
          have hmn : m < n := by omega
          have hstep : f₀ (f₀^[m] ζ) = f₀^[m + 1] ζ :=
            (Function.iterate_succ_apply' f₀ m ζ).symm
          have hrel := critval_deriv_Phi_comp hF0 d (u := f₀^[m] ζ)
            (hBsub (hmem m)) (by rw [hstep]; exact hBsub (hmem (m + 1)))
          rw [hstep, ih (by omega)] at hrel
          rcases mul_eq_zero.mp hrel with h3 | h3
          · exact h3
          · exact absurd h3 (hcase m hmn)
    exact absurd (hd n le_rfl) (hOm (f₀^[n] ζ) hn)

/-! ## The main argument -/

/-- The mathematical content of `pushdown_critval_unique`, given the case-A input
`deriv φ₀ w ≠ 0` from Lemma 5.1 (proved separately as `deriv_phi_ne_zero_of_noncrit`). -/
theorem critval_aux (f₀ : ℂ → ℂ) (D₀ : Set ℂ) (d : MandelDim.ParabData f₀ D₀)
    (B : Set ℂ) (hB : MandelDim.IsImmediateBasin f₀ D₀ B)
    (hcB : ∃! c : ℂ, c ∈ B ∧ deriv f₀ c = 0)
    (η : ℝ) (Bu Bl : Set ℂ)
    (hsub : Bu ∪ Bl ⊆ d.DE) (hup : {w : ℂ | η < w.im} ⊆ Bu)
    (hback : ∀ v : ℂ, η < v.im → d.φ (v - 1) ∈ B) (hF0 : MandelDim.InF0 f₀ D₀)
    (hD3 : ∀ (w : ℂ), w ∈ d.Dφ → (∀ j : ℕ, 1 ≤ j → d.φ (w - (j : ℂ)) ∈ D₀) →
      (∀ j : ℕ, 1 ≤ j → deriv f₀ (d.φ (w - (j : ℂ))) ≠ 0) → deriv d.φ w ≠ 0) :
    ∃ v₀ : ℂ, ∀ w : ℂ, η < w.im → deriv d.E w = 0 → MandelDim.piExp (d.E w) = v₀ := by
  -- `Φ₀' ≠ 0` on the attracting petal
  have hOm : ∀ y ∈ d.Ωp, deriv d.Φ y ≠ 0 := fun y hy =>
    Work.Parab.inversion.deriv_ne_zero_of_injOn d.Ωp_open (d.Φ_holo.mono d.Ωp_sub) d.Φ_inj y hy
  obtain ⟨c, hc_mem, hc_uniq⟩ := hcB
  refine ⟨MandelDim.piExp (d.Φ c), ?_⟩
  intro w hw hcrit
  have hwDE : w ∈ d.DE := hsub (Or.inl (hup hw))
  have hwDφ : w ∈ d.Dφ := hwDE.1
  -- the whole backward orbit `w - j` stays in `Dφ`
  have hsubDφ : ∀ j : ℕ, w - (j : ℂ) ∈ d.Dφ := by
    intro j
    induction j with
    | zero => simpa using hwDφ
    | succ m ih =>
        have : w - ((m + 1 : ℕ) : ℂ) = (w - (m : ℂ)) - 1 := by push_cast; ring
        rw [this]; exact d.left_inv _ ih
  -- `φ₀ (w - j) ∈ D₀` for `j ≥ 1`
  have hD₀ : ∀ j : ℕ, 1 ≤ j → d.φ (w - (j : ℂ)) ∈ D₀ := by
    intro j hj
    have h1 : w - (j : ℂ) ∈ d.Dφ := hsubDφ j
    have h2 : w - (j : ℂ) + 1 ∈ d.Dφ := by
      have hcast : ((j : ℕ) : ℂ) = ((j - 1 : ℕ) : ℂ) + 1 := by
        have : j = (j - 1) + 1 := by omega
        rw [this]; push_cast; ring
      have : w - (j : ℂ) + 1 = w - ((j - 1 : ℕ) : ℂ) := by rw [hcast]; ring
      rw [this]; exact hsubDφ (j - 1)
    exact (d.succ_iff (w - (j : ℂ)) h1).mp h2
  -- `φ₀ (w - j) ∈ B` for `j ≥ 1`, by `hback`
  have hBmem : ∀ j : ℕ, 1 ≤ j → d.φ (w - (j : ℂ)) ∈ B := by
    intro j _
    have hIm : η < (w - (j : ℂ) + 1).im := by
      have : (w - (j : ℂ) + 1).im = w.im := by simp
      rw [this]; exact hw
    have h := hback (w - (j : ℂ) + 1) hIm
    have harg : w - (j : ℂ) + 1 - 1 = w - (j : ℂ) := by ring
    rwa [harg] at h
  have hchain : deriv d.E w = deriv d.Φ (d.φ w) * deriv d.φ w := critval_deriv_E d hwDE
  have hz1 : d.φ w = f₀ (d.φ (w - 1)) := by
    have h := d.φ_abel (w - 1) (by simpa using hsubDφ 1) (by simpa using hwDφ)
    simpa using h
  by_cases hA : ∃ j : ℕ, 1 ≤ j ∧ deriv f₀ (d.φ (w - (j : ℂ))) = 0
  · -- a backward iterate is the critical point of `B`
    obtain ⟨j, hj, hcritj⟩ := hA
    have hzjB : d.φ (w - (j : ℂ)) ∈ B := hBmem j hj
    have hzjc : d.φ (w - (j : ℂ)) = c := hc_uniq _ ⟨hzjB, hcritj⟩
    have hiter := critval_Phi_iterate d hB hzjB j
    have hfx : f₀^[j] (d.φ (w - (j : ℂ))) = d.φ w := by
      have h := critval_f_iterate_phi_sub d hwDφ j j le_rfl
      simpa using h
    rw [hfx, hzjc] at hiter
    refine critval_piExp_shift (u := d.E w) (v := d.Φ c) (k := (j : ℤ)) ?_
    show d.Φ (d.φ w) = d.Φ c + ((j : ℤ) : ℂ)
    rw [← hiter]; push_cast; ring
  · push Not at hA
    have hz : deriv d.Φ (d.φ w) * deriv d.φ w = 0 := by rw [← hchain]; exact hcrit
    rcases mul_eq_zero.mp hz with hΦ | hφ
    · -- `Φ₀` is critical at `φ₀ w`; reduce to `φ₀ (w-1) ∈ B`
      have hz1B : d.φ (w - 1) ∈ B := by simpa using hBmem 1 le_rfl
      have hrel := critval_deriv_Phi_comp hF0 d (u := d.φ (w - 1))
        (hB.2.2.1 hz1B) (by rw [← hz1]; exact hwDE.2)
      rw [← hz1, hΦ, zero_mul] at hrel
      have hcrit1 : deriv d.Φ (d.φ (w - 1)) = 0 := hrel.symm
      obtain ⟨k, hkB, hkcrit, hkΦ⟩ :=
        critval_Phi_crit_in_B d hF0 hB ⟨c, hc_mem, hc_uniq⟩ hOm hz1B hcrit1
      have hkc : f₀^[k] (d.φ (w - 1)) = c := hc_uniq _ ⟨hkB, hkcrit⟩
      rw [hkc] at hkΦ
      refine critval_piExp_shift (u := d.E w) (v := d.Φ c) (k := (1 : ℤ) - (k : ℤ)) ?_
      show d.Φ (d.φ w) = d.Φ c + (((1 : ℤ) - (k : ℤ) : ℤ) : ℂ)
      rw [hz1, d.Φ_abel (d.φ (w - 1)) (hB.2.2.1 hz1B), ← hkΦ]
      push_cast
      ring
    · -- `φ₀` is critical at `w`: Lemma 5.1 forbids this in case A
      exfalso
      exact (hD3 w hwDφ hD₀ hA) hφ

/-- **The critical value of the pushed-down horn map is unique.**

Every critical point `w` of the lifted horn map `Ẽ = Φ₀ ∘ φ₀` above the line `Im w > η`
(i.e. in the component `B̃ᵘ ⊇ {Im > η}` of `φ₀⁻¹ B`) pushes down to the same point of `ℂ^*`:
Shishikura's `𝒞_{f₀}` (Proposition 5.3) is ramified only over `v = π (Φ₀ c)`, `c` the unique
critical point of `f₀` in the immediate basin `B`. -/
theorem pushdown_critval_unique (f₀ : ℂ → ℂ) (D₀ : Set ℂ) (d : MandelDim.ParabData f₀ D₀)
    (B : Set ℂ) (hB : MandelDim.IsImmediateBasin f₀ D₀ B)
    (hcB : ∃! c : ℂ, c ∈ B ∧ deriv f₀ c = 0)
    (η : ℝ) (Bu Bl : Set ℂ)
    (hBu : Bu = connectedComponentIn (d.φ ⁻¹' B ∩ d.Dφ) (Complex.I * (η + 1)))
    (hBl : Bl = connectedComponentIn (d.φ ⁻¹' B ∩ d.Dφ) (-(Complex.I * (η + 1))))
    (hsub : Bu ∪ Bl ⊆ d.DE) (hup : {w : ℂ | η < w.im} ⊆ Bu) (hlo : {w : ℂ | w.im < -η} ⊆ Bl)
    (hback : ∀ v : ℂ, η < v.im → d.φ (v - 1) ∈ B) (hF0 : MandelDim.InF0 f₀ D₀) :
    ∃ v₀ : ℂ, ∀ w : ℂ, η < w.im → deriv d.E w = 0 → MandelDim.piExp (d.E w) = v₀ :=
  critval_aux f₀ D₀ d B hB hcB η Bu Bl hsub hup hback hF0
    (fun w hw hD₀ hnc => deriv_phi_ne_zero_of_noncrit f₀ D₀ d hw hD₀ hnc)

end

end Work.Horn
