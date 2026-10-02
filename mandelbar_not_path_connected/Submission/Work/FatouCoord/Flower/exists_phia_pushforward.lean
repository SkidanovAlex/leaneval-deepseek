/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FatouCoord team
-/
import Mathlib
import Submission.Work.FatouCoord.Basic
import Submission.Work.FatouCoord.Flower.GermDefs
import Submission.Work.FatouCoord.Flower.exists_antiFatou_of_pushforward

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Pushing an antiholomorphic Fatou coordinate forward to a larger petal

Let `f` be a holomorphic map with an antiholomorphic square root `gU` (`gU ∘ gU = f`),
let `P` be an `f`-invariant set carrying a Fatou coordinate `φ₀` for `f` together with the
antiholomorphic equivariance `φ₀ (gU w) = conj (φ₀ w) + 1/2` (Hubbard–Schleicher Lemma 2.3),
and let `Pa` be a set which

* is `f`-invariant, avoids `0`, has all its `f`-orbits converging to `0` and never hitting `0`;
* `f` is injective on it;
* has the *entry property*: every orbit converging to `0` and never hitting `0` eventually
  meets `P`.

Then the *orbit coordinate*

  `z ↦ φ₀ (f^[n] z) - n`,  where `n` is any time at which `f^[n] z ∈ P`,

is well defined on `Pa` (because `P` is `f`-invariant and `φ₀ ∘ f = φ₀ + 1` on `P`) and is an
antiholomorphic Fatou coordinate for `gU` on `Pa`: it is holomorphic there, it is injective
there, and it satisfies `φa (gU z) = conj (φa z) + 1/2`.

The file proves the three properties of the orbit coordinate as separate lemmas
(`orbitCoord_eq_of_mem_iterate`, `differentiableOn_orbitCoord`, `injOn_orbitCoord`,
`orbitCoord_map_gU`) and then assembles them into the requested statement.  The final glue
(extending `Φ` from `Pa` to all of `ℂ` so that the equivariance also holds at points
`gU z ∉ Pa`) is the lemma `exists_antiFatou_of_pushforward`.
-/

open scoped Topology
open Set Filter Metric Function

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace Work.FatouCoord.Flower

noncomputable section

open Classical

/-! ## Elementary iteration lemmas -/

/-- Iterates of a map injective on a forward invariant set are injective on that set. -/
theorem injOn_iterate_of_mapsTo {α : Type*} {s : Set α} {F : α → α} (hF : Set.InjOn F s)
    (hmap : Set.MapsTo F s s) (n : ℕ) : Set.InjOn (F^[n]) s := by
  induction n with
  | zero => intro x _ y _ h; simpa using h
  | succ n ih =>
    intro x hx y hy h
    have h2 : F (F^[n] x) = F (F^[n] y) := by
      simpa only [Function.iterate_succ_apply'] using h
    exact ih hx hy (hF (mapsTo_iterate_of_mapsTo hmap n hx)
      (mapsTo_iterate_of_mapsTo hmap n hy) h2)

/-- A map whose square is `f` commutes with `f`. -/
theorem comp_self_comm {f g : ℂ → ℂ} (hgg : g ∘ g = f) (z : ℂ) : f (g z) = g (f z) := by
  have hsq : ∀ w : ℂ, f w = g (g w) := fun w => (congrFun hgg w).symm
  rw [hsq (g z), hsq z]

/-- The iterates of a square root of `f` commute with the iterates of `f`. -/
theorem iterate_comp_self_comm {f g : ℂ → ℂ} (hgg : g ∘ g = f) (n : ℕ) (z : ℂ) :
    f^[n] (g z) = g (f^[n] z) := by
  induction n with
  | zero => simp
  | succ n ih => rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply',
      comp_self_comm hgg]

/-- If `g ∘ g = f` then `g` is injective wherever `f` is. -/
theorem injOn_of_comp_self {f g : ℂ → ℂ} {Pa : Set ℂ} (hgg : g ∘ g = f)
    (hfinj : Set.InjOn f Pa) : Set.InjOn g Pa := by
  intro z hz z' hz' heq
  have hsq : ∀ w : ℂ, f w = g (g w) := fun w => (congrFun hgg w).symm
  exact hfinj hz hz' (by rw [hsq z, hsq z', heq])

/-! ## The orbit coordinate -/

/-- The **orbit coordinate** attached to `(f, φ₀, P, Pa, sel)`: for `z ∈ Pa` it is
`φ₀ (f^[sel z] z) - sel z`, and it is `0` off `Pa` (a value which is never used below).
The function `sel` is meant to select, for each `z ∈ Pa`, a time at which the orbit of `z`
meets `P`. -/
def orbitCoord (f φ₀ : ℂ → ℂ) (P Pa : Set ℂ) (sel : ℂ → ℕ) (z : ℂ) : ℂ :=
  dite (z ∈ Pa) (fun _ => φ₀ (f^[sel z] z) - (sel z : ℂ)) (fun _ => 0)

theorem orbitCoord_of_mem {f φ₀ : ℂ → ℂ} {P Pa : Set ℂ} {sel : ℂ → ℕ} {z : ℂ}
    (hz : z ∈ Pa) : orbitCoord f φ₀ P Pa sel z = φ₀ (f^[sel z] z) - (sel z : ℂ) :=
  dite_eq_left hz

theorem orbitCoord_of_not_mem {f φ₀ : ℂ → ℂ} {P Pa : Set ℂ} {sel : ℂ → ℕ} {z : ℂ}
    (hz : z ∉ Pa) : orbitCoord f φ₀ P Pa sel z = 0 :=
  dite_eq_right hz

/-- Specialised value of the orbit coordinate, used for rewriting in the main proof. -/
theorem orbitCoord_eq_of_mem_iterate {f φ₀ : ℂ → ℂ} {P Pa : Set ℂ} {sel : ℂ → ℕ}
    (hsel : ∀ z : ℂ, z ∈ Pa → f^[sel z] z ∈ P)
    (hPmaps : Set.MapsTo f P P) (hφ : IsFatouCoordinateOn f φ₀ P)
    {z : ℂ} (hz : z ∈ Pa) {m : ℕ} (hm : f^[m] z ∈ P) :
    orbitCoord f φ₀ P Pa sel z = φ₀ (f^[m] z) - (m : ℂ) := by
  rw [orbitCoord_of_mem hz]
  have hN : f^[sel z] z ∈ P := hsel z hz
  rcases le_total m (sel z) with hle | hle
  · have h1 : φ₀ (f^[sel z] z) = φ₀ (f^[m] z) + ((sel z - m : ℕ) : ℂ) := by
      have hk := hφ.iterate hPmaps hm (sel z - m)
      rwa [← Function.iterate_add_apply, Nat.sub_add_cancel hle] at hk
    rw [h1, Nat.cast_sub hle]
    ring
  · have h1 : φ₀ (f^[m] z) = φ₀ (f^[sel z] z) + ((m - sel z : ℕ) : ℂ) := by
      have hk := hφ.iterate hPmaps hN (m - sel z)
      rwa [← Function.iterate_add_apply, Nat.sub_add_cancel hle] at hk
    rw [h1, Nat.cast_sub hle]
    ring

/-- Well definedness: on `Pa` the orbit coordinate is independent of the entry time. -/
theorem orbitCoord_congr_iterate {f φ₀ : ℂ → ℂ} {P Pa : Set ℂ} {sel : ℂ → ℕ}
    (hsel : ∀ z : ℂ, z ∈ Pa → f^[sel z] z ∈ P)
    (hPmaps : Set.MapsTo f P P) (hφ : IsFatouCoordinateOn f φ₀ P)
    {z : ℂ} (hz : z ∈ Pa) {m n : ℕ} (hm : f^[m] z ∈ P) (hn : f^[n] z ∈ P) :
    φ₀ (f^[m] z) - (m : ℂ) = φ₀ (f^[n] z) - (n : ℂ) :=
  (orbitCoord_eq_of_mem_iterate hsel hPmaps hφ hz hm).symm.trans
    (orbitCoord_eq_of_mem_iterate hsel hPmaps hφ hz hn)

/-! ## Differentiability of the orbit coordinate -/

/-- The orbit coordinate is holomorphic on `Pa`. -/
theorem differentiableOn_orbitCoord {f φ₀ : ℂ → ℂ} {P Pa : Set ℂ} {sel : ℂ → ℕ}
    (hsel : ∀ z : ℂ, z ∈ Pa → f^[sel z] z ∈ P) (hf : Differentiable ℂ f)
    (hPopen : IsOpen P) (hPmaps : Set.MapsTo f P P) (hφ : IsFatouCoordinateOn f φ₀ P) :
    DifferentiableOn ℂ (orbitCoord f φ₀ P Pa sel) Pa := by
  intro z hz
  have hnm : f^[sel z] z ∈ P := hsel z hz
  have hU : (f^[sel z]) ⁻¹' P ∈ 𝓝 z :=
    ((hf.iterate (sel z)).continuous.continuousAt).preimage_mem_nhds (hPopen.mem_nhds hnm)
  have hψ : DifferentiableOn ℂ (fun w => φ₀ (f^[sel z] w) - ((sel z : ℕ) : ℂ))
      ((f^[sel z]) ⁻¹' P) :=
    (hφ.1.comp ((hf.iterate (sel z)).differentiableOn) (fun w hw => hw)).sub_const _
  have hψat : DifferentiableAt ℂ (fun w => φ₀ (f^[sel z] w) - ((sel z : ℕ) : ℂ)) z :=
    hψ.differentiableAt hU
  have hEv : orbitCoord f φ₀ P Pa sel =ᶠ[𝓝[Pa] z]
      (fun w => φ₀ (f^[sel z] w) - ((sel z : ℕ) : ℂ)) := by
    filter_upwards [nhdsWithin_le_nhds hU, self_mem_nhdsWithin] with w hwU hwPa
    exact orbitCoord_eq_of_mem_iterate hsel hPmaps hφ hwPa hwU
  have hzeq : orbitCoord f φ₀ P Pa sel z = φ₀ (f^[sel z] z) - ((sel z : ℕ) : ℂ) :=
    orbitCoord_eq_of_mem_iterate hsel hPmaps hφ hz hnm
  exact (hEv.differentiableWithinAt_iff hzeq).mpr hψat.differentiableWithinAt

/-! ## The antiholomorphic equivariance of the orbit coordinate -/

/-- **The key identity.**  If `z` and `gU z` both lie in `Pa`, the orbit coordinate of `gU z`
is the conjugate of the orbit coordinate of `z` shifted by `1/2`. -/
theorem orbitCoord_map_gU {f gU φ₀ : ℂ → ℂ} {P Pa : Set ℂ} {sel : ℂ → ℕ}
    (hsel : ∀ z : ℂ, z ∈ Pa → f^[sel z] z ∈ P)
    (hPmaps : Set.MapsTo f P P) (hφ : IsFatouCoordinateOn f φ₀ P)
    (hanti : IsAntiholomorphicFatouOn gU φ₀ P) (hgg : gU ∘ gU = f)
    {z : ℂ} (hz : z ∈ Pa) (hz' : gU z ∈ Pa) :
    orbitCoord f φ₀ P Pa sel (gU z) = star (orbitCoord f φ₀ P Pa sel z) + 1 / 2 := by
  have hKN : sel z ≤ max (sel (gU z)) (sel z) := le_max_right _ _
  have hKM : sel (gU z) ≤ max (sel (gU z)) (sel z) := le_max_left _ _
  have hNmem : f^[sel z] z ∈ P := hsel z hz
  have hMmem : f^[sel (gU z)] (gU z) ∈ P := hsel (gU z) hz'
  have hKmem : f^[max (sel (gU z)) (sel z)] z ∈ P := by
    have h := mapsTo_iterate_of_mapsTo hPmaps (max (sel (gU z)) (sel z) - sel z) hNmem
    rwa [← Function.iterate_add_apply, Nat.sub_add_cancel hKN] at h
  have hKgmem : f^[max (sel (gU z)) (sel z)] (gU z) ∈ P := by
    have h := mapsTo_iterate_of_mapsTo hPmaps (max (sel (gU z)) (sel z) - sel (gU z)) hMmem
    rwa [← Function.iterate_add_apply, Nat.sub_add_cancel hKM] at h
  -- Fatou equivariance for the common time
  have hNval : φ₀ (f^[max (sel (gU z)) (sel z)] z)
      = φ₀ (f^[sel z] z) + ((max (sel (gU z)) (sel z) - sel z : ℕ) : ℂ) := by
    have h := hφ.iterate hPmaps hNmem (max (sel (gU z)) (sel z) - sel z)
    rwa [← Function.iterate_add_apply, Nat.sub_add_cancel hKN] at h
  have hMval : φ₀ (f^[max (sel (gU z)) (sel z)] (gU z))
      = φ₀ (f^[sel (gU z)] (gU z))
        + ((max (sel (gU z)) (sel z) - sel (gU z) : ℕ) : ℂ) := by
    have h := hφ.iterate hPmaps hMmem (max (sel (gU z)) (sel z) - sel (gU z))
    rwa [← Function.iterate_add_apply, Nat.sub_add_cancel hKM] at h
  have hantiK : φ₀ (f^[max (sel (gU z)) (sel z)] (gU z))
      = star (φ₀ (f^[max (sel (gU z)) (sel z)] z)) + 1 / 2 := by
    rw [iterate_comp_self_comm hgg]
    exact hanti.2.2 _ hKmem
  rw [orbitCoord_eq_of_mem_iterate hsel hPmaps hφ hz' hMmem,
    orbitCoord_eq_of_mem_iterate hsel hPmaps hφ hz hNmem]
  have hstep : φ₀ (f^[sel (gU z)] (gU z))
      = φ₀ (f^[max (sel (gU z)) (sel z)] (gU z))
        - ((max (sel (gU z)) (sel z) - sel (gU z) : ℕ) : ℂ) := by
    rw [hMval]; ring
  rw [hstep, hantiK, hNval, Nat.cast_sub hKN, Nat.cast_sub hKM]
  simp only [star_add, star_sub, star_natCast]
  ring

/-! ## Injectivity of the orbit coordinate -/

/-- The orbit coordinate is injective on `Pa`. -/
theorem injOn_orbitCoord {f φ₀ : ℂ → ℂ} {P Pa : Set ℂ} {sel : ℂ → ℕ}
    (hsel : ∀ z : ℂ, z ∈ Pa → f^[sel z] z ∈ P)
    (hPmaps : Set.MapsTo f P P) (hφ : IsFatouCoordinateOn f φ₀ P)
    (hφinj : Set.InjOn φ₀ P) (hfPa : Set.InjOn f Pa) (hPamaps : Set.MapsTo f Pa Pa) :
    Set.InjOn (orbitCoord f φ₀ P Pa sel) Pa := by
  intro z hz z' hz' heq
  have hNz : f^[sel z] z ∈ P := hsel z hz
  have hNz' : f^[sel z'] z' ∈ P := hsel z' hz'
  rcases le_total (sel z) (sel z') with hle | hle
  · have hmz : f^[sel z'] z ∈ P := by
      have h := mapsTo_iterate_of_mapsTo hPmaps (sel z' - sel z) hNz
      rwa [← Function.iterate_add_apply, Nat.sub_add_cancel hle] at h
    have e1 := orbitCoord_eq_of_mem_iterate hsel hPmaps hφ hz hmz
    have e2 := orbitCoord_eq_of_mem_iterate hsel hPmaps hφ hz' hNz'
    have h4 : φ₀ (f^[sel z'] z) = φ₀ (f^[sel z'] z') := by
      have h3 : φ₀ (f^[sel z'] z) - (sel z' : ℂ)
          = φ₀ (f^[sel z'] z') - (sel z' : ℂ) := by
        rw [← e1, heq, e2]
      have h5 := congrArg (· + (sel z' : ℂ)) h3
      simpa using h5
    exact injOn_iterate_of_mapsTo hfPa hPamaps (sel z') hz hz' (hφinj hmz hNz' h4)
  · have hmz' : f^[sel z] z' ∈ P := by
      have h := mapsTo_iterate_of_mapsTo hPmaps (sel z - sel z') hNz'
      rwa [← Function.iterate_add_apply, Nat.sub_add_cancel hle] at h
    have e1 := orbitCoord_eq_of_mem_iterate hsel hPmaps hφ hz hNz
    have e2 := orbitCoord_eq_of_mem_iterate hsel hPmaps hφ hz' hmz'
    have h4 : φ₀ (f^[sel z] z) = φ₀ (f^[sel z] z') := by
      have h3 : φ₀ (f^[sel z] z) - (sel z : ℂ)
          = φ₀ (f^[sel z] z') - (sel z : ℂ) := by
        rw [← e1, heq, e2]
      have h5 := congrArg (· + (sel z : ℂ)) h3
      simpa using h5
    exact injOn_iterate_of_mapsTo hfPa hPamaps (sel z) hz hz' (hφinj hNz hmz' h4)

/-! ## The requested statement -/

theorem exists_phia_pushforward {f gU φ₀ : ℂ → ℂ} {P Pa : Set ℂ}
    (hf : Differentiable ℂ f)
    (hgU_anti : ∀ z : ℂ, DifferentiableAt ℂ (fun z => star (gU z)) z)
    (hPopen : IsOpen P) (hPmaps : Set.MapsTo f P P)
    (hφ : Work.FatouCoord.IsFatouCoordinateOn f φ₀ P) (hφinj : Set.InjOn φ₀ P)
    (hanti : Work.FatouCoord.IsAntiholomorphicFatouOn gU φ₀ P)
    (hgg : gU ∘ gU = f) (hgU0 : gU 0 = 0)
    (hPamaps : Set.MapsTo f Pa Pa) (hPa0 : (0 : ℂ) ∉ Pa)
    (hPalim : ∀ z ∈ Pa, Filter.Tendsto (fun n : ℕ => f^[n] z) Filter.atTop (nhds 0))
    (hPa_ne : ∀ z ∈ Pa, ∀ n : ℕ, f^[n] z ≠ 0)
    (hfinj : Set.InjOn f Pa)
    (hPentry : ∀ x : ℂ, Filter.Tendsto (fun n : ℕ => f^[n] x) Filter.atTop (nhds 0) →
      (∀ n : ℕ, f^[n] x ≠ 0) → ∃ n : ℕ, f^[n] x ∈ P) :
    ∃ φa : ℂ → ℂ, Work.FatouCoord.IsAntiholomorphicFatouOn gU φa Pa ∧ Set.InjOn φa Pa := by
  -- an orbit of a point of `Pa` always meets `P`
  have hex : ∀ z : ℂ, z ∈ Pa → ∃ n : ℕ, f^[n] z ∈ P :=
    fun z hz => hPentry z (hPalim z hz) (hPa_ne z hz)
  -- select the entry time
  let sel : ℂ → ℕ := fun z =>
    dite (z ∈ Pa) (fun hz => Classical.choose (hex z hz)) (fun _ => 0)
  have hsel : ∀ z : ℂ, z ∈ Pa → f^[sel z] z ∈ P := by
    intro z hz
    have hselz : sel z = Classical.choose (hex z hz) := dite_eq_left hz
    rw [hselz]
    exact Classical.choose_spec (hex z hz)
  -- the orbit coordinate
  have hΦdiff : DifferentiableOn ℂ (orbitCoord f φ₀ P Pa sel) Pa :=
    differentiableOn_orbitCoord hsel hf hPopen hPmaps hφ
  have hΦinj : Set.InjOn (orbitCoord f φ₀ P Pa sel) Pa :=
    injOn_orbitCoord hsel hPmaps hφ hφinj hfinj hPamaps
  have hkey : ∀ z ∈ Pa, gU z ∈ Pa →
      orbitCoord f φ₀ P Pa sel (gU z) = star (orbitCoord f φ₀ P Pa sel z) + 1 / 2 :=
    fun z hz hz' => orbitCoord_map_gU hsel hPmaps hφ hanti hgg hz hz'
  have hantiPa : IsAntiholomorphicOn gU Pa :=
    fun z _ => (hgU_anti z).differentiableWithinAt
  have hgUinj : Set.InjOn gU Pa := injOn_of_comp_self hgg hfinj
  exact exists_antiFatou_of_pushforward hantiPa hΦdiff hΦinj hgUinj hkey

end

end Work.FatouCoord.Flower
