import Mathlib
import Submission.Work.Holonomy3.mv_lex_defs
import Submission.Work.Holonomy3.map_fract_add_Icc

/-!
# The diagonal-slice identity on the torus

`torMeasure d` is the normalised measure of the parameter cube `[0,1]^d`.  For a function `f` on
the cube which is `1`-periodic in every coordinate, the "diagonal slice" integral
`F s = ∫_0^1 f (s + u·1) du` has the same total integral as `f`:

`∫_s F s ∂torMeasure = ∫_s f s ∂torMeasure`.

This is the Haar-measure statement `∫_{T^d × T} f (s + u·1) d(s,u) = ∫_{T^d} f`, proved here by
Fubini together with the fact that the map `(s,u) ↦ fract (s + u·1)` pushes `torMeasure d ⊗
(volume.restrict [0,1])` forward to `torMeasure d`: for each fixed `u` the slice map
`s ↦ fract (s + u·1)` preserves the torus measure (a product of the one dimensional fact
`Work.Holonomy3.map_fract_add_Icc`), and the product measure is computed slice by slice.

## Main statement

* `Work.Holonomy3.diag_slice_identity`
-/

namespace Work.Holonomy3

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-! ### Periodicity helpers -/

/-- A function which is `1`-periodic in each coordinate, in the sense of `Function.update`, is
invariant under adding a natural number to one coordinate. -/
theorem diag_periodic_update_nat (g : (Fin d → ℝ) → ℝ)
    (hper : ∀ (s : Fin d → ℝ) (j : Fin d), g (Function.update s j (s j + 1)) = g s)
    (s : Fin d → ℝ) (j : Fin d) (n : ℕ) :
    g (Function.update s j (s j + n)) = g s := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hcast2 : s j + (((n+1 : ℕ)) : ℝ) = s j + (n:ℝ) + 1 := by push_cast; ring
    have hupd : Function.update (Function.update s j (s j + (n:ℝ))) j
        ((Function.update s j (s j + (n:ℝ))) j + 1)
        = Function.update s j (s j + (n:ℝ) + 1) := by
      rw [Function.update_idem, Function.update_self]
    rw [hcast2, ← hupd, hper, ih]

/-- Auxiliary: invariance under subtracting a natural number from one coordinate. -/
theorem diag_periodic_update_neg (g : (Fin d → ℝ) → ℝ)
    (hper : ∀ (s : Fin d → ℝ) (j : Fin d), g (Function.update s j (s j + 1)) = g s)
    (s : Fin d → ℝ) (j : Fin d) (n : ℕ) :
    g (Function.update s j (s j + ((-(n:ℤ) : ℤ) : ℝ))) = g s := by
  let t : Fin d → ℝ := Function.update s j (s j + ((-(n:ℤ) : ℤ) : ℝ))
  have htj : t j = s j + ((-(n:ℤ) : ℤ) : ℝ) := by simp [t]
  have ht : Function.update t j (t j + (n : ℝ)) = s := by
    rw [Function.update_idem]
    have h1 : t j + (n : ℝ) = s j := by rw [htj]; push_cast; ring
    rw [h1, Function.update_eq_self]
  have h := diag_periodic_update_nat g hper t j n
  rw [ht] at h
  exact h.symm

/-- A function which is `1`-periodic in each coordinate is invariant under adding any integer to
one coordinate. -/
theorem diag_periodic_update_int (g : (Fin d → ℝ) → ℝ)
    (hper : ∀ (s : Fin d → ℝ) (j : Fin d), g (Function.update s j (s j + 1)) = g s)
    (s : Fin d → ℝ) (j : Fin d) (m : ℤ) :
    g (Function.update s j (s j + m)) = g s := by
  rcases Int.eq_nat_or_neg m with ⟨n, hn | hn⟩
  · rw [hn]; exact diag_periodic_update_nat g hper s j n
  · rw [hn]; exact diag_periodic_update_neg g hper s j n

/-- A function which is `1`-periodic in each coordinate is invariant under adding an arbitrary
integer vector. -/
theorem diag_periodic_add_intVec (g : (Fin d → ℝ) → ℝ)
    (hper : ∀ (s : Fin d → ℝ) (j : Fin d), g (Function.update s j (s j + 1)) = g s)
    (s : Fin d → ℝ) (c : Fin d → ℤ) :
    g (fun j => s j + c j) = g s := by
  classical
  suffices h : ∀ S : Finset (Fin d),
      g (fun j => s j + (if j ∈ S then (c j : ℝ) else 0)) = g s by
    have hh := h Finset.univ
    simpa using hh
  intro S
  induction S using Finset.induction_on with
  | empty => simp
  | insert k S hk ih =>
    have hkey : (fun j => s j + (if j ∈ insert k S then (c j : ℝ) else 0)) =
        Function.update (fun j => s j + (if j ∈ S then (c j : ℝ) else 0)) k
          ((fun j => s j + (if j ∈ S then (c j : ℝ) else 0)) k + (c k : ℝ)) := by
      funext j
      by_cases hjk : j = k
      · rw [hjk, if_pos (Finset.mem_insert_self k S), Function.update_self]
        show s k + (c k : ℝ) = (s k + (if k ∈ S then (c k : ℝ) else 0)) + (c k : ℝ)
        rw [if_neg hk]; ring
      · rw [Function.update_apply, if_neg hjk]
        congr 1
        simp [Finset.mem_insert, hjk]
    rw [hkey, diag_periodic_update_int g hper _ k (c k), ih]

/-- A `1`-periodic-in-each-coordinate function depends only on the coordinatewise fractional
part of its argument. -/
theorem diag_periodic_eq_comp_fract (g : (Fin d → ℝ) → ℝ)
    (hper : ∀ (s : Fin d → ℝ) (j : Fin d), g (Function.update s j (s j + 1)) = g s)
    (x : Fin d → ℝ) :
    g x = g (fun j => Int.fract (x j)) := by
  have h := diag_periodic_add_intVec g hper (fun j => Int.fract (x j)) (fun j => ⌊x j⌋)
  have hfun : (fun j => Int.fract (x j) + (⌊x j⌋ : ℝ)) = x := by
    funext j; exact Int.fract_add_floor (x j)
  rw [hfun] at h
  exact h

/-! ### The fractional-part shift preserves `torMeasure` -/

/-- The coordinatewise map `s ↦ (j ↦ Int.fract (s j + v))` preserves `torMeasure d` whenever
`0 ≤ v ≤ 1`. -/
theorem diag_torMeasure_map_fract {v : ℝ} (hv : 0 ≤ v) (hv1 : v ≤ 1) :
    MeasureTheory.Measure.map (fun s : Fin d → ℝ => fun j => Int.fract (s j + v))
        (torMeasure d)
      = torMeasure d := by
  have key : MeasureTheory.Measure.map
        (fun s : Fin d → ℝ => fun j => Int.fract (s j + v)) (torMeasure d)
      = MeasureTheory.Measure.pi (fun _ : Fin d =>
          (MeasureTheory.volume.restrict (Set.Icc (0:ℝ) 1)).map
            (fun x => Int.fract (x + v))) := by
    rw [show torMeasure d
        = MeasureTheory.Measure.pi (fun _ : Fin d =>
            MeasureTheory.volume.restrict (Set.Icc (0:ℝ) 1)) from rfl]
    exact MeasureTheory.Measure.pi_map_pi
      (f := fun (_ : Fin d) => fun x : ℝ => Int.fract (x + v))
      (fun _ => measurable_fract.comp (by fun_prop) |>.aemeasurable)
  rw [key, map_fract_add_Icc hv hv1]

/-- The same statement for an arbitrary real shift `u` (only its fractional part matters). -/
theorem diag_torMeasure_map_fract_add (u : ℝ) :
    MeasureTheory.Measure.map (fun s : Fin d → ℝ => fun j => Int.fract (s j + u))
        (torMeasure d)
      = torMeasure d := by
  have hcongr : (fun s : Fin d → ℝ => fun j => Int.fract (s j + u))
      = (fun s : Fin d → ℝ => fun j => Int.fract (s j + Int.fract u)) := by
    funext s j
    have h1 : s j + u = (s j + Int.fract u) + ((⌊u⌋ : ℤ) : ℝ) := by
      have := Int.fract_add_floor u
      linarith
    rw [h1, Int.fract_add_intCast]
  rw [hcongr]
  exact diag_torMeasure_map_fract (Int.fract_nonneg u) (le_of_lt (Int.fract_lt_one u))

/-! ### The main statement -/

/-- Combine Fubini/Tonelli with the invariance of the torus integral under the diagonal shift.
The per-`u` shift identity `∫ s, g (fun j => s j + u) = ∫ s, g s` for `1`-periodic `g` is stated in
`Work.Holonomy3.torus_integral_shift`; it may be imported if that module builds, and otherwise the
same argument (via `Work.Holonomy3.map_fract_add_Icc`) can be reproduced locally. -/
theorem diag_slice_identity {d : ℕ} (f : (Fin d → ℝ) → ℝ)
    (hper : ∀ (s : Fin d → ℝ) (j : Fin d), f (Function.update s j (s j + 1)) = f s)
    (hf : MeasureTheory.Integrable f (torMeasure d)) :
    MeasureTheory.Integrable (fun s : Fin d → ℝ => ∫ u in (0:ℝ)..1, f (fun j => s j + u))
        (torMeasure d) ∧
      ∫ s, (∫ u in (0:ℝ)..1, f (fun j => s j + u)) ∂(torMeasure d)
        = ∫ s, f s ∂(torMeasure d) := by
  classical
  set ν : Measure ℝ := volume.restrict (Set.Icc (0:ℝ) 1) with hνdef
  set φ : (Fin d → ℝ) × ℝ → (Fin d → ℝ) :=
    fun p => fun j => Int.fract (p.1 j + p.2) with hφdef
  -- (1) `φ` is measurable.
  have hφmeas : Measurable φ := by
    rw [hφdef]
    refine measurable_pi_iff.mpr (fun j => ?_)
    exact measurable_fract.comp (by fun_prop)
  -- (2) For each `u`, the slice map `s ↦ φ (s,u)` preserves the torus measure.
  have hslice : ∀ u : ℝ,
      MeasureTheory.Measure.map (fun s : Fin d → ℝ => φ (s, u)) (torMeasure d)
        = torMeasure d := by
    intro u
    have hfun : (fun s : Fin d → ℝ => φ (s, u))
        = (fun s : Fin d → ℝ => fun j => Int.fract (s j + u)) := by
      funext s j
      rw [hφdef]
    rw [hfun]
    exact diag_torMeasure_map_fract_add u
  -- (3) Hence `φ` pushes `torMeasure ⊗ ν` forward to `torMeasure`.
  have hνuniv : ν Set.univ = 1 := by
    rw [hνdef, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, Real.volume_Icc]
    norm_num
  have hmap : MeasureTheory.Measure.map φ ((torMeasure d).prod ν) = torMeasure d := by
    refine Measure.ext fun A hA => ?_
    rw [Measure.map_apply hφmeas hA, Measure.prod_apply_symm (hφmeas hA)]
    have hsliceA : ∀ u : ℝ,
        (torMeasure d) ((fun s : Fin d → ℝ => φ (s, u)) ⁻¹' A) = torMeasure d A := by
      intro u
      have hm : Measurable (fun s : Fin d → ℝ => φ (s, u)) := by fun_prop
      have h := congrArg (fun m : Measure (Fin d → ℝ) => m A) (hslice u)
      rw [Measure.map_apply hm hA] at h
      exact h
    trans ∫⁻ u, (torMeasure d) A ∂ν
    · apply lintegral_congr
      intro u
      exact hsliceA u
    · rw [MeasureTheory.lintegral_const, hνuniv, mul_one]
  have hMP : MeasurePreserving φ ((torMeasure d).prod ν) (torMeasure d) := ⟨hφmeas, hmap⟩
  -- (4) `f ∘ φ` is integrable and has the same integral as `f`.
  have hfφ : MeasureTheory.Integrable (fun p : (Fin d → ℝ) × ℝ => f (φ p))
      ((torMeasure d).prod ν) :=
    hMP.integrable_comp_of_integrable hf
  have hint : ∫ p, f (φ p) ∂((torMeasure d).prod ν) = ∫ s, f s ∂(torMeasure d) := by
    have h := MeasureTheory.integral_map (μ := (torMeasure d).prod ν) (φ := φ) (f := f)
      hφmeas.aemeasurable (by rw [hmap]; exact hf.aestronglyMeasurable)
    rw [hmap] at h
    exact h.symm
  -- (5) Fubini.
  have hFubini : ∫ s : Fin d → ℝ, (∫ u : ℝ, f (φ (s, u)) ∂ν) ∂(torMeasure d)
      = ∫ s, f s ∂(torMeasure d) := by
    rw [← MeasureTheory.integral_prod (fun p : (Fin d → ℝ) × ℝ => f (φ p)) hfφ]
    exact hint
  -- (6) Convert the measure integral over `ν` into an interval integral.
  have hconv : ∀ g : ℝ → ℝ, (∫ u, g u ∂ν) = ∫ u in (0:ℝ)..1, g u := by
    intro g
    rw [hνdef,
      show (∫ u, g u ∂(volume.restrict (Set.Icc (0:ℝ) 1)))
          = ∫ u in Set.Icc (0:ℝ) 1, g u from rfl,
      MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
  -- (7) Pointwise identification of the inner integrals.
  have hinner : ∀ s : Fin d → ℝ,
      (∫ u : ℝ, f (φ (s, u)) ∂ν) = ∫ u in (0:ℝ)..1, f (fun j => s j + u) := by
    intro s
    rw [hconv (fun u => f (φ (s, u)))]
    refine intervalIntegral.integral_congr (fun u _ => ?_)
    rw [hφdef]
    exact (diag_periodic_eq_comp_fract f hper (fun j => s j + u)).symm
  constructor
  · -- integrability of the slice integral
    have h1 : MeasureTheory.Integrable (fun s : Fin d → ℝ => ∫ u, f (φ (s, u)) ∂ν)
        (torMeasure d) := hfφ.integral_prod_left
    refine h1.congr ?_
    filter_upwards with s
    exact hinner s
  · -- the integral identity
    rw [← hFubini]
    refine integral_congr_ae ?_
    filter_upwards with s
    exact (hinner s).symm

end

end Work.Holonomy3
