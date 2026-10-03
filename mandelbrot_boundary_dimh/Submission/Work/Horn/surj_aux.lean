import Mathlib
import Submission.Work.Interfaces.HornParts
import Submission.Work.Horn.basic
import Submission.Work.Horn.basin_facts

/-!
# `Work.Horn.surj_aux` — reusable facts for the `surj`/`inf` assembly of `HornData`

Companion to `Submission/Work/Horn/NOTES_SURJ_INF.md`.  These lemmas are the part of
`surj_inf_of_parts` that *is* derivable from the four Horn pieces; the infinite-fibre
conjuncts are not (see the NOTES file).

Contents:
* `E_succ_on`, `E_add_int_on` — `T`-equivariance of `E = Φ ∘ φ` on a `T`-invariant `D ⊆ DE`;
* `piExp_injOn_E_fiber` — `π` is injective on a fibre of `E` (so `piExp '' (E ⁻¹' {y})` is
  infinite exactly when the fibre is);
* `Phi_critOrbit` — `Φ (f^[j] c) = Φ c + j` along the critical orbit;
* `crit_not_mem_critOrbit` — `c ∉ critOrbit f₀ c`;
* `E_image_univ_of_varphi_image` — **the reducible half**: if `B ∖ critOrbit ⊆ φ '' BuOf`
  then `E '' BuOf = ℂ`.  (The inclusion `B ∖ critOrbit ⊆ φ '' BuOf` is proved from `hPhi`,
  `hVarphi`, `hTopo`, `hSC` and `Work.SimplyConnected.ABS.isPreconnected_compl_closedDiscrete`;
  it is the "Claim B ⇒ φ onto" step.)
-/

namespace Work.Horn

noncomputable section

open _root_.MandelDim Filter Topology Metric Set

variable {f₀ : ℂ → ℂ} {D₀ B : Set ℂ} {c : ℂ}

/-- `T`-equivariance of `E = Φ ∘ φ` on a `T`-invariant `D ⊆ DE`. -/
theorem E_succ_on (d : MandelDim.ParabData f₀ D₀) {D : Set ℂ} (hT : MandelDim.IsTInvariant D)
    (hsub : D ⊆ d.DE) :
    ∀ w ∈ D, w + 1 ∈ D → d.E (w + 1) = d.E w + 1 :=
  fun w hw _ => Work.Horn.MandelDim.ParabData.E_add_one d (hsub hw) (hsub ((hT w).mp hw))

/-- Integer version. -/
theorem E_add_int_on (d : MandelDim.ParabData f₀ D₀) {D : Set ℂ} (hT : MandelDim.IsTInvariant D)
    (hsub : D ⊆ d.DE) {w : ℂ} (hw : w ∈ D) (k : ℤ) :
    d.E (w + k) = d.E w + k :=
  Work.Horn.MandelDim.E_add_int hT (E_succ_on d hT hsub) hw k

/-- `π` is injective on a fibre of `E` inside a `T`-invariant set: two points of the fibre
differing by an integer would force `y = y + k`. -/
theorem piExp_injOn_E_fiber (d : MandelDim.ParabData f₀ D₀) {D : Set ℂ}
    (hT : MandelDim.IsTInvariant D) (hsub : D ⊆ d.DE) {y : ℂ} :
    InjOn MandelDim.piExp {w : ℂ | w ∈ D ∧ d.E w = y} := by
  intro u hu v hv huv
  obtain ⟨k, hk⟩ := Work.Horn.MandelDim.piExp_eq_iff.mp huv
  have hE : d.E (v + (k : ℂ)) = d.E v + (k : ℂ) := E_add_int_on d hT hsub hv.1 k
  have hEu : d.E u = y + (k : ℂ) := by rw [hk, hE, hv.2]
  have hEq : y + (k : ℂ) = y := by rw [← hEu, hu.2]
  have hk0 : (k : ℂ) = 0 := by
    have h : (k : ℂ) + y = y := by rw [add_comm]; exact hEq
    have h2 : (k : ℂ) + y = (0 : ℂ) + y := by rw [zero_add]; exact h
    exact add_right_cancel h2
  rw [hk, hk0, add_zero]

/-- Along the critical orbit, `Φ` advances by `1`: `Φ (f^[j] c) = Φ c + j`. -/
theorem Phi_critOrbit (d : MandelDim.ParabData f₀ D₀) (hbas : B ⊆ MandelDim.ParabolicBasin f₀ D₀)
    (hmaps : MapsTo f₀ B B) (hcB : c ∈ B) :
    ∀ j : ℕ, d.Φ (f₀^[j] c) = d.Φ c + j := by
  intro j
  induction j with
  | zero => simp
  | succ n ih =>
      have hmem : f₀^[n] c ∈ B := hmaps.iterate n hcB
      rw [Function.iterate_succ_apply', d.Φ_abel (f₀^[n] c) (hbas hmem), ih]
      push_cast; ring

/-- The critical point is not a positive iterate of itself (the orbit converges to `0 ∉ B`). -/
theorem crit_not_mem_critOrbit (d : MandelDim.ParabData f₀ D₀)
    (hsetup : MandelDim.IsF0Setup f₀ D₀ B c) : c ∉ MandelDim.critOrbit f₀ c := by
  rintro ⟨k, hk1, hk⟩
  obtain ⟨hopen, hzero, hdiff, hfix, hderiv, -⟩ := hsetup.1
  have hbas : B ⊆ MandelDim.ParabolicBasin f₀ D₀ := hsetup.2.1.2.2.1
  have hcB : c ∈ B := hsetup.2.2.1
  have h0nb : (0 : ℂ) ∉ MandelDim.ParabolicBasin f₀ D₀ :=
    Work.Horn.BasinAux.zero_not_mem hopen hzero hdiff hfix hderiv
  -- `f^[k] c = c` forces `f^[k*n] c = c` for all `n`, hence `c` is a limit of `f^[m] c`
  have hfixk : ∀ n : ℕ, f₀^[k * n] c = c := by
    intro n
    induction n with
    | zero => simp
    | succ m ih =>
        rw [show k * (m + 1) = k * m + k by ring, Function.iterate_add_apply, ← hk, ih]
  have htend : Tendsto (fun n : ℕ => f₀^[n] c) atTop (𝓝 0) :=
    Work.Horn.BasinAux.tendsto_zero (hbas hcB)
  have hkpos : 0 < k := by omega
  have hcomp : Tendsto (fun n : ℕ => f₀^[k * n] c) atTop (𝓝 0) :=
    htend.comp (Filter.tendsto_atTop_atTop.mpr fun b => ⟨b, fun n hn =>
      le_trans hn (Nat.le_mul_of_pos_left n hkpos)⟩)
  have hconst : Tendsto (fun _ : ℕ => c) atTop (𝓝 0) := by
    simpa [funext hfixk] using hcomp
  have hc0 : c = 0 := tendsto_nhds_unique tendsto_const_nhds hconst
  exact h0nb (by rw [← hc0]; exact hbas hcB)

/-- **The reducible half of the assembly.**  If every point of `B` off the forward critical
orbit is in the image of `φ` (this is what `hVarphi` + simple connectivity of `BuOf` gives), then
`E = Φ ∘ φ` maps `BuOf` onto `ℂ`: the critical value `Φ c` is attained (at `c`), `T`-equivariance
gives its whole `ℤ`-orbit, and every other value is hit because a `Φ`-preimage off `critOrbit`
lifts through `φ`. -/
theorem E_image_univ_of_varphi_image (d : MandelDim.ParabData f₀ D₀)
    (hPhi : MandelDim.HornPhiStatement) (hsetup : MandelDim.IsF0Setup f₀ D₀ B c)
    (hsub : B \ MandelDim.critOrbit f₀ c ⊆ d.φ '' MandelDim.BuOf d B)
    (hT : MandelDim.IsTInvariant (MandelDim.BuOf d B))
    (hDE : MandelDim.BuOf d B ⊆ d.DE) :
    d.E '' MandelDim.BuOf d B = Set.univ := by
  have hbas : B ⊆ MandelDim.ParabolicBasin f₀ D₀ := hsetup.2.1.2.2.1
  have hmaps : MapsTo f₀ B B := hsetup.2.1.2.2.2.2.1
  have hcB : c ∈ B := hsetup.2.2.1
  have hφc : c ∈ d.φ '' MandelDim.BuOf d B :=
    hsub ⟨hcB, crit_not_mem_critOrbit d hsetup⟩
  ext y
  simp only [Set.mem_image, Set.mem_univ, iff_true]
  by_cases hy : ∃ k : ℤ, y = d.Φ c + k
  · obtain ⟨k, rfl⟩ := hy
    obtain ⟨w, hw, hwφ⟩ := hφc
    refine ⟨w + k, MandelDim.IsTInvariant.add_int hT hw k, ?_⟩
    rw [E_add_int_on d hT hDE hw k, show d.E w = d.Φ c by simp [MandelDim.ParabData.E, hwφ]]
  · obtain ⟨z, hzB, hzy⟩ := (hPhi f₀ D₀ B c d hsetup).1 y
    have hznot : z ∉ MandelDim.critOrbit f₀ c := by
      rintro ⟨j, hj1, hjc⟩
      exact hy ⟨(j : ℤ), by
        rw [← hzy, hjc, Phi_critOrbit d hbas hmaps hcB j]; push_cast; ring⟩
    obtain ⟨w, hw, hwφ⟩ := hsub ⟨hzB, hznot⟩
    exact ⟨w, hw, by simp [MandelDim.ParabData.E, hwφ, hzy]⟩

end

end Work.Horn
