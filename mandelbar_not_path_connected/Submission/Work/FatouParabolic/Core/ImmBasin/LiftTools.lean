/-
Copyright: subproject `Submission/Work/FatouParabolic/` of `mandelbar_not_path_connected`.

# Lifting tools: the strip lifts of `τ ↦ Φ (τ + n)` through the coverings `F^[n]`

This file packages `Work.FatouParabolic.Core.exists_strip_lift` into a `Classical.choose`-ed
family `petalLift F z₀ p₀ hmap hcover Φ C B hB hΦ n`, together with its basic properties and the
two structural facts used by the Liouville contradiction `false_of_petalInverse_of_covering`:

* `petal_shift_iterate` / `petalLift_iterate_apply`: the Abel equation iterated along a real
  direction, `F^[k] (Φ s) = Φ (s + k)` (resp. `F^[k] (X τ) = Φ (τ + k)`);
* `petalLift_eqOn`: **any two lifts agree on the intersection of their domains** — the key that
  makes the glued function `Ψ τ := (lift of height |Im τ| + 1 at τ) τ` well defined.
-/
import Mathlib
import Submission.Work.FatouParabolic.Core.exists_strip_lift
import Submission.Work.FatouParabolic.Core.ImmBasin.Defs
import Submission.Work.FatouParabolic.Core.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Set Filter
open scoped Topology

namespace Work.FatouParabolic.Core.ImmBasin

noncomputable section

/-- The **strip hypothesis** on the inverse petal coordinate `Φ`: on the tail
`tailStrip C B = {τ | C < Re τ, |Im τ| < B}` the values of `Φ` lie in the immediate basin, `Φ`
satisfies the Abel equation `F (Φ τ) = Φ (τ + 1)`, and `Φ` is complex differentiable there. -/
def StripProp (F : ℂ → ℂ) (z₀ p₀ : ℂ) (Φ : ℂ → ℂ) (C B : ℝ) : Prop :=
  ∀ τ : ℂ, C < τ.re → |τ.im| < B →
    Φ τ ∈ immBasin F z₀ p₀ ∧ F (Φ τ) = Φ (τ + 1) ∧ DifferentiableAt ℂ Φ τ

/-- The lift of `τ ↦ Φ (τ + n)` through the covering `F^[n]` of the immediate basin, on the deep
strip `tailStrip (C - n) B`, produced by `exists_strip_lift`. -/
noncomputable def petalLift (F : ℂ → ℂ) (z₀ p₀ : ℂ)
    (hmap : Set.MapsTo F (immBasin F z₀ p₀) (immBasin F z₀ p₀))
    (hcover : ∀ n : ℕ, IsCoveringMap (immBasinIterate (immBasin F z₀ p₀) F hmap n))
    (Φ : ℂ → ℂ) (C B : ℝ) (hB : 0 < B) (hΦ : StripProp F z₀ p₀ Φ C B) (n : ℕ) : ℂ → ℂ :=
  Classical.choose (exists_strip_lift (F := F) (z₀ := z₀) (p₀ := p₀) (B := B) (C := C)
    hB hmap hcover Φ hΦ n)

variable {F : ℂ → ℂ} {z₀ p₀ : ℂ} {Φ : ℂ → ℂ} {C B C' B' : ℝ}
  {hmap : Set.MapsTo F (immBasin F z₀ p₀) (immBasin F z₀ p₀)}
  {hcover : ∀ n : ℕ, IsCoveringMap (immBasinIterate (immBasin F z₀ p₀) F hmap n)}

theorem petalLift_continuousOn (hB : 0 < B) (hΦ : StripProp F z₀ p₀ Φ C B) (n : ℕ) :
    ContinuousOn (petalLift F z₀ p₀ hmap hcover Φ C B hB hΦ n) (tailStrip (C - (n : ℝ)) B) :=
  (Classical.choose_spec (exists_strip_lift (F := F) (z₀ := z₀) (p₀ := p₀) (B := B) (C := C)
    hB hmap hcover Φ hΦ n)).1

theorem petalLift_mem (hB : 0 < B) (hΦ : StripProp F z₀ p₀ Φ C B) (n : ℕ) {τ : ℂ}
    (hτ : τ ∈ tailStrip (C - (n : ℝ)) B) :
    petalLift F z₀ p₀ hmap hcover Φ C B hB hΦ n τ ∈ immBasin F z₀ p₀ :=
  ((Classical.choose_spec (exists_strip_lift (F := F) (z₀ := z₀) (p₀ := p₀) (B := B) (C := C)
    hB hmap hcover Φ hΦ n)).2.1 τ hτ).1

theorem petalLift_comp (hB : 0 < B) (hΦ : StripProp F z₀ p₀ Φ C B) (n : ℕ) {τ : ℂ}
    (hτ : τ ∈ tailStrip (C - (n : ℝ)) B) :
    (F^[n]) (petalLift F z₀ p₀ hmap hcover Φ C B hB hΦ n τ) = Φ (τ + (n : ℂ)) :=
  ((Classical.choose_spec (exists_strip_lift (F := F) (z₀ := z₀) (p₀ := p₀) (B := B) (C := C)
    hB hmap hcover Φ hΦ n)).2.1 τ hτ).2

theorem petalLift_agree (hB : 0 < B) (hΦ : StripProp F z₀ p₀ Φ C B) (n : ℕ) {τ : ℂ}
    (hτ : τ ∈ tailStrip C B) :
    petalLift F z₀ p₀ hmap hcover Φ C B hB hΦ n τ = Φ τ :=
  (Classical.choose_spec (exists_strip_lift (F := F) (z₀ := z₀) (p₀ := p₀) (B := B) (C := C)
    hB hmap hcover Φ hΦ n)).2.2 τ hτ

/-- Iterated Abel equation along real translations: if `Φ` satisfies the strip hypothesis on
`tailStrip C B`, then `F^[j] (Φ s) = Φ (s + j)` for every `s` in the tail. -/
theorem petal_shift_iterate (hΦ : StripProp F z₀ p₀ Φ C B) {s : ℂ} (hs : C < s.re)
    (hsB : |s.im| < B) (j : ℕ) : (F^[j]) (Φ s) = Φ (s + (j : ℂ)) := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    have hs' : C < (s + (j : ℂ)).re ∧ |(s + (j : ℂ)).im| < B := by
      refine ⟨?_, ?_⟩
      · have h : (s + (j : ℂ)).re = s.re + (j : ℝ) := by simp
        rw [h]; linarith
      · have h : (s + (j : ℂ)).im = s.im := by simp
        rw [h]; exact hsB
    rw [Function.iterate_succ_apply', ih, (hΦ (s + (j : ℂ)) hs'.1 hs'.2).2.1]
    congr 1
    push_cast
    ring

/-- The lift `X = petalLift … n` satisfies `F^[k] (X τ) = Φ (τ + k)` for every `k ≥ n` on its
domain. -/
theorem petalLift_iterate_apply (hB : 0 < B) (hΦ : StripProp F z₀ p₀ Φ C B) {n k : ℕ}
    (hk : n ≤ k) {τ : ℂ} (hτ : τ ∈ tailStrip (C - (n : ℝ)) B) :
    (F^[k]) (petalLift F z₀ p₀ hmap hcover Φ C B hB hΦ n τ) = Φ (τ + (k : ℂ)) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + n := ⟨k - n, (Nat.sub_add_cancel hk).symm⟩
  have hcomp := petalLift_comp (hmap := hmap) (hcover := hcover) hB hΦ n hτ
  have hsre : C < (τ + (n : ℂ)).re := by
    have h : (τ + (n : ℂ)).re = τ.re + (n : ℝ) := by simp
    rw [h]
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith [hτ.1]
  have hsim : |(τ + (n : ℂ)).im| < B := by
    have h : (τ + (n : ℂ)).im = τ.im := by simp
    rw [h]; exact hτ.2
  calc (F^[m + n]) (petalLift F z₀ p₀ hmap hcover Φ C B hB hΦ n τ)
      = (F^[m]) ((F^[n]) (petalLift F z₀ p₀ hmap hcover Φ C B hB hΦ n τ)) :=
        Function.iterate_add_apply F m n _
    _ = (F^[m]) (Φ (τ + (n : ℂ))) := by rw [hcomp]
    _ = Φ (τ + (n : ℂ) + (m : ℂ)) :=
        petal_shift_iterate (z₀ := z₀) (p₀ := p₀) (F := F) hΦ hsre hsim m
    _ = Φ (τ + ((m + n : ℕ) : ℂ)) := by
        congr 1
        push_cast
        ring

/-- **Two lifts agree on the intersection of their domains.**  Both are continuous sections of
iterates of `F` over the same map `τ ↦ Φ (τ + k)` (for `k` large), both take values in the
immediate basin, and they agree on the (nonempty, convex) common strip tail; uniqueness of lifts
through the covering `F^[k]` finishes the job. -/
theorem petalLift_eqOn (hB : 0 < B) (hB' : 0 < B')
    (hΦ : StripProp F z₀ p₀ Φ C B) (hΦ' : StripProp F z₀ p₀ Φ C' B') (n n' : ℕ) {τ : ℂ}
    (hτ : τ ∈ tailStrip (C - (n : ℝ)) B ∩ tailStrip (C' - (n' : ℝ)) B') :
    petalLift F z₀ p₀ hmap hcover Φ C B hB hΦ n τ
      = petalLift F z₀ p₀ hmap hcover Φ C' B' hB' hΦ' n' τ := by
  classical
  set X := petalLift F z₀ p₀ hmap hcover Φ C B hB hΦ n with hXdef
  set Y := petalLift F z₀ p₀ hmap hcover Φ C' B' hB' hΦ' n' with hYdef
  set k := max n n' with hkdef
  set A : Set ℂ := tailStrip (C - (n : ℝ)) B ∩ tailStrip (C' - (n' : ℝ)) B' with hAdef
  have hnk : n ≤ k := le_max_left _ _
  have hn'k : n' ≤ k := le_max_right _ _
  -- A common strip tail inside `A` on which both lifts equal `Φ`.
  have hAconvex : Convex ℝ A := by
    rw [hAdef]; exact (convex_tailStrip _ _).inter (convex_tailStrip _ _)
  have hne : ((max C C' + 1 : ℝ) : ℂ) ∈ tailStrip (max C C') (min B B') := by
    refine ⟨?_, ?_⟩
    · simp
    · have h : (((max C C' + 1 : ℝ) : ℂ)).im = 0 := by simp
      rw [h]
      simpa using lt_min hB hB'
  set τ₁ : ℂ := ((max C C' + 1 : ℝ) : ℂ) with hτ₁def
  have hτ₁ : τ₁ ∈ tailStrip (max C C') (min B B') := hne
  have hτ₁C : τ₁ ∈ tailStrip C B :=
    ⟨lt_of_le_of_lt (le_max_left C C') hτ₁.1, lt_of_lt_of_le hτ₁.2 (min_le_left B B')⟩
  have hτ₁C' : τ₁ ∈ tailStrip C' B' :=
    ⟨lt_of_le_of_lt (le_max_right C C') hτ₁.1, lt_of_lt_of_le hτ₁.2 (min_le_right B B')⟩
  have hτ₁A : τ₁ ∈ A := by
    rw [hAdef]
    refine ⟨tailStrip_subset (by simp) hτ₁C, tailStrip_subset (by simp) hτ₁C'⟩
  -- `A` is preconnected (convex) and both restrictions are continuous into the basin.
  haveI : PreconnectedSpace ↥A := Subtype.preconnectedSpace hAconvex.isPreconnected
  have hXcont : ContinuousOn X A :=
    (petalLift_continuousOn (hmap := hmap) (hcover := hcover) hB hΦ n).mono inter_subset_left
  have hYcont : ContinuousOn Y A :=
    (petalLift_continuousOn (hmap := hmap) (hcover := hcover) hB' hΦ' n').mono inter_subset_right
  let u₁ : ↥A → ↥(immBasin F z₀ p₀) := fun σ => ⟨X σ.1, petalLift_mem hB hΦ n σ.2.1⟩
  let u₂ : ↥A → ↥(immBasin F z₀ p₀) := fun σ => ⟨Y σ.1, petalLift_mem hB' hΦ' n' σ.2.2⟩
  have hcont₁ : Continuous u₁ :=
    Continuous.subtype_mk (continuousOn_iff_continuous_domRestrict.mp hXcont) _
  have hcont₂ : Continuous u₂ :=
    Continuous.subtype_mk (continuousOn_iff_continuous_domRestrict.mp hYcont) _
  have heq : immBasinIterate (immBasin F z₀ p₀) F hmap k ∘ u₁
      = immBasinIterate (immBasin F z₀ p₀) F hmap k ∘ u₂ := by
    funext σ
    apply Subtype.ext
    simp only [Function.comp_apply, immBasinIterate_coe]
    rw [petalLift_iterate_apply (hmap := hmap) (hcover := hcover) hB hΦ hnk σ.2.1,
      petalLift_iterate_apply (hmap := hmap) (hcover := hcover) hB' hΦ' hn'k σ.2.2]
  have hbase : u₁ ⟨τ₁, hτ₁A⟩ = u₂ ⟨τ₁, hτ₁A⟩ := by
    apply Subtype.ext
    simp only [u₁, u₂]
    rw [hXdef, hYdef,
      petalLift_agree (hmap := hmap) (hcover := hcover) hB hΦ n hτ₁C,
      petalLift_agree (hmap := hmap) (hcover := hcover) hB' hΦ' n' hτ₁C']
  have hfin := (hcover k).eq_of_comp_eq hcont₁ hcont₂ heq ⟨τ₁, hτ₁A⟩ hbase
  have hval := congrArg Subtype.val (congrFun hfin ⟨τ, hτ⟩)
  simpa [u₁, u₂] using hval

end

end Work.FatouParabolic.Core.ImmBasin
