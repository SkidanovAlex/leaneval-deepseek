import Mathlib
import Submission.Work.LandLeaves.TypeGeometry
import Submission.Work.LandLeaves.finite_of_homeo_expanding
import Submission.Work.LandLeaves.dist_nsmul_eq_of_lt_half

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Finiteness of a closed `d`-tupling-invariant set of angles that is injective

`Work.LandLeaves.finite_of_cyclicOrderPreserving` is the combinatorial core of the finiteness of
the *type* of a repelling periodic point of the tricorn (`Work.LandLeaves.finite_landingAngles`).

**Statement.**  Let `d ≥ 2`, let `K ⊆ [0,1)` be closed, and let `σ x = Int.fract (d * x)` be the
`d`-tupling map of the circle of angles.  Assume that `σ` maps `K` into `K` (`hmaps`), onto `K`
(`hsurj`) and injectively on `K` (`hinj`), and that `σ` preserves the strict cyclic-betweenness
relation `ccBet` on `K` (`hord`).  Then `K` is finite.

**Proof.**  The cyclic-order hypothesis `hord` is *not needed*: the argument below uses only
`hclosed`, `hsub`, `hmaps`, `hsurj`, `hinj`.

The set `K ⊆ [0,1)` is closed and bounded in `ℝ`, hence compact, and so is its trace
`B = ↑''K` on the additive circle `UnitAddCircle = ℝ/ℤ` (the projection `ℝ → ℝ/ℤ` is continuous).
On representatives the `d`-tupling map of the circle is `x ↦ Int.fract (d * x)`
(`fract_nsmul_coe_eq`), so `hmaps` says `d • B ⊆ B`, `hsurj` says `d • B ⊇ B`, and `hinj` together
with the injectivity of `ℝ ∋ x ↦ (x : ℝ/ℤ)` on `[0,1)` says that `d • ·` is *injective* on `B`.
Hence `z ↦ d • z` restricts to a continuous bijection — a homeomorphism `G` — of the compact
space `B`.

The `d`-tupling map of the circle is `d`-Lipschitz (`‖d • a‖ ≤ d ‖a‖`) and multiplies circle
distances by the exact factor `d` on pairs at distance `< 1/(2d)` (`dist_nsmul_eq_of_lt_half`).
The abstract lemma `finite_of_homeo_expanding` — a homeomorphism of a compact metric space that is
`λ`-Lipschitz and *exactly* expands distances by `λ > 1` below some threshold `η > 0` forces the
space to be finite — therefore makes `B` finite, and since `ℝ ∋ x ↦ (x : ℝ/ℤ)` is injective on
`K ⊆ [0,1)`, this gives finiteness of `K`.

The lemma is stated with the extra hypothesis `hord` as requested; being unused here it only
weakens the statement, so the result matches the requested signature.  An alternative route to the
same finiteness (the classical "shrinking gaps" argument, available when `hord` is at hand) shows
that the endpoints of any gap of `K` are periodic for `σ`, whence `K` is contained in the finite
set of fixed points of some iterate `σ ^ q`.

**Remark (for the team).**  The variant
`Submission.Work.LandLeaves.finite_of_closed_invariant_injective` (same conclusion, with `K`
closed in `ℝ` and the additional seam hypothesis `hseam`) is a corollary of the same argument:
`hclosed : IsClosed K` gives `IsClosed (K ∪ {1})` because `K ∪ {1}` is a union of two closed sets,
so its seam hypothesis is redundant as well.
-/

noncomputable section

open Classical
open scoped Topology

namespace Work.LandLeaves

/-- On representatives, the `d`-tupling map of the additive circle is the fractional part map. -/
private lemma fract_nsmul_coe_eq (d : ℕ) (x : ℝ) :
    (d : ℕ) • (x : UnitAddCircle) = ((Int.fract ((d : ℝ) * x) : ℝ) : UnitAddCircle) := by
  rw [← AddCircle.coe_nsmul (1 : ℝ) (n := d) (x := x), AddCircle.coe_fract, nsmul_eq_mul]

/-- Two points of the fundamental domain `[0,1)` with the same class in the circle are equal. -/
private lemma coe_eq_of_mem_Ico {x y : ℝ} (hx : x ∈ Set.Ico (0 : ℝ) 1)
    (hy : y ∈ Set.Ico (0 : ℝ) 1) (h : (x : UnitAddCircle) = (y : UnitAddCircle)) : x = y := by
  refine (AddCircle.coe_eq_coe_iff_of_mem_Ico (p := (1 : ℝ)) (a := (0 : ℝ)) ?_ ?_).mp h
  · simpa using hx
  · simpa using hy

/-- **Finiteness of a closed `d`-tupling-invariant, injective set of angles.**

The cyclic-order hypothesis `hord` is not used; see the module docstring. -/
theorem finite_of_cyclicOrderPreserving (d : ℕ) (hd : 2 ≤ d) {K : Set ℝ}
    (hclosed : IsClosed K) (hsub : ∀ x ∈ K, x ∈ Set.Ico 0 1)
    (hmaps : ∀ x ∈ K, Int.fract ((d : ℝ) * x) ∈ K)
    (hsurj : ∀ y ∈ K, ∃ x ∈ K, Int.fract ((d : ℝ) * x) = y)
    (hinj : ∀ x ∈ K, ∀ y ∈ K, Int.fract ((d : ℝ) * x) = Int.fract ((d : ℝ) * y) → x = y)
    (hord : ∀ a ∈ K, ∀ b ∈ K, ∀ x ∈ K, Work.LandLeaves.ccBet a b x →
      Work.LandLeaves.ccBet (Int.fract ((d : ℝ) * a)) (Int.fract ((d : ℝ) * b))
        (Int.fract ((d : ℝ) * x))) : K.Finite := by
  -- `K` is closed and bounded in `ℝ`, hence compact.
  have hKcpt : IsCompact K :=
    IsCompact.of_isClosed_subset (isCompact_Icc (a := (0 : ℝ)) (b := 1)) hclosed
      (fun x hx => ⟨(hsub x hx).1, le_of_lt (hsub x hx).2⟩)
  -- Its trace `B` on the circle of angles is compact as well.
  let B : Set UnitAddCircle := ((↑) : ℝ → UnitAddCircle) '' K
  have hBcpt : IsCompact B := hKcpt.image (AddCircle.continuous_mk' (1 : ℝ))
  haveI : CompactSpace B := isCompact_iff_compactSpace.mp hBcpt
  -- The `d`-tupling map sends `B` into itself.
  have hmapB : ∀ z ∈ B, (d : ℕ) • z ∈ B := by
    rintro z ⟨x, hxK, rfl⟩
    exact ⟨Int.fract ((d : ℝ) * x), hmaps x hxK, (fract_nsmul_coe_eq d x).symm⟩
  let g : B → B := fun z => ⟨(d : ℕ) • (z : UnitAddCircle), hmapB z z.2⟩
  have hgcont : Continuous g :=
    Continuous.subtype_mk ((continuous_nsmul d).comp continuous_subtype_val)
      (fun z => hmapB z z.2)
  -- `g` is injective, by `hinj` and the choice of the fundamental domain.
  have hginj : Function.Injective g := by
    intro z w hzw
    have hzw' : (d : ℕ) • (z : UnitAddCircle) = (d : ℕ) • (w : UnitAddCircle) := by
      simpa only [g] using congrArg Subtype.val hzw
    obtain ⟨x, hxK, hxz⟩ := z.2
    obtain ⟨y, hyK, hyw⟩ := w.2
    have hzw'' : (d : ℕ) • ((x : ℝ) : UnitAddCircle) = (d : ℕ) • ((y : ℝ) : UnitAddCircle) := by
      rw [← hxz, ← hyw] at hzw'
      exact hzw'
    have h2 : ((Int.fract ((d : ℝ) * x) : ℝ) : UnitAddCircle)
        = ((Int.fract ((d : ℝ) * y) : ℝ) : UnitAddCircle) := by
      rw [← fract_nsmul_coe_eq d x, ← fract_nsmul_coe_eq d y]
      exact hzw''
    have h1 : Int.fract ((d : ℝ) * x) = Int.fract ((d : ℝ) * y) :=
      (AddCircle.coe_eq_coe_iff_of_mem_Ico (p := (1 : ℝ)) (a := (0 : ℝ))
        ⟨Int.fract_nonneg _, by simpa using Int.fract_lt_one ((d : ℝ) * x)⟩
        ⟨Int.fract_nonneg _, by simpa using Int.fract_lt_one ((d : ℝ) * y)⟩).mp h2
    exact Subtype.ext (by rw [← hxz, hinj x hxK y hyK h1, hyw])
  -- `g` is surjective, by `hsurj`.
  have hgsurj : Function.Surjective g := by
    intro z
    obtain ⟨x, hxK, hxz⟩ := z.2
    obtain ⟨x', hx'K, hx'⟩ := hsurj x hxK
    refine ⟨⟨(x' : ℝ), ⟨x', hx'K, rfl⟩⟩, ?_⟩
    apply Subtype.ext
    show (d : ℕ) • ((x' : ℝ) : UnitAddCircle) = (z : UnitAddCircle)
    rw [fract_nsmul_coe_eq, hx', hxz]
  have hbij : Function.Bijective g := ⟨hginj, hgsurj⟩
  let e : B ≃ B := Equiv.ofBijective g hbij
  have hecont : Continuous (e : B → B) := by
    rw [Equiv.coe_ofBijective]; exact hgcont
  -- `G` is a self-homeomorphism of the compact metric space `B`.
  let G : B ≃ₜ B := Continuous.homeoOfEquivCompactToT2 (f := e) hecont
  have hdR : (1 : ℝ) < (d : ℝ) := by exact_mod_cast (by omega : 1 < d)
  have hdRpos : (0 : ℝ) < (d : ℝ) := lt_trans one_pos hdR
  have heta : (0 : ℝ) < 1 / (2 * (d : ℝ)) := one_div_pos.mpr (by positivity)
  have hGval : ∀ a : B, (G a : UnitAddCircle) = (d : ℕ) • (a : UnitAddCircle) := fun _ => rfl
  have hfinB : B.Finite := by
    rw [← Set.finite_coe_iff]
    refine finite_of_homeo_expanding (X := B) G hdR heta ?_ ?_
    · -- the tupling map is `d`-Lipschitz
      intro a b
      simp only [Subtype.dist_eq, hGval]
      rw [dist_eq_norm, dist_eq_norm, ← nsmul_sub]
      exact norm_nsmul_le
    · -- and it expands distances exactly by the factor `d` below `1/(2d)`
      intro a b hab
      simp only [Subtype.dist_eq, hGval]
      refine dist_nsmul_eq_of_lt_half (n := d) ?_
      rw [Subtype.dist_eq] at hab
      have h1 : dist ↑a ↑b < (2 * (d : ℝ))⁻¹ := by rw [one_div] at hab; exact hab
      calc (d : ℝ) * dist ↑a ↑b < (d : ℝ) * (2 * (d : ℝ))⁻¹ :=
            mul_lt_mul_of_pos_left h1 hdRpos
        _ = 1 / 2 := by field_simp
  -- Transfer finiteness back to `K` along the injective map `ℝ → ℝ/ℤ` on `[0,1)`.
  have hfinImg : (((↑) : ℝ → UnitAddCircle) '' K).Finite := hfinB
  refine Set.Finite.of_finite_image hfinImg ?_
  intro x hx y hy hxy
  exact coe_eq_of_mem_Ico (hsub x hx) (hsub y hy) hxy

end Work.LandLeaves
