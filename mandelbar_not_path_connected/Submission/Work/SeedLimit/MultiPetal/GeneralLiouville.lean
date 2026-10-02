/-
Generalisation of the `Work.FatouParabolic.Core.ImmBasin` Liouville/covering argument
from the immediate basin `immBasin F z₀ p₀` to an arbitrary domain `Ω` on which `F` acts as a
covering.  Everything is a verbatim adaptation of
`Core/exists_strip_lift.lean`, `Core/ImmBasin/LiftTools.lean` and
`Core/ImmBasin/false_of_petalInverse_of_covering.lean` with `immBasin F z₀ p₀` replaced by a
variable `Ω`.
-/
import Mathlib
import Submission.Work.FatouParabolic.Core.ImmBasin.Defs
import Submission.Work.FatouParabolic.Core.ImmBasin.LiftTools
import Submission.Work.FatouParabolic.Core.ImmBasin.differentiableOn_of_comp_iterate_eq
import Submission.Work.FatouParabolic.Core.ImmBasin.false_of_petalInverse_of_covering

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Set Filter
open scoped Topology

namespace Work.SeedLimit.MultiPetal

noncomputable section

/-- **The strip hypothesis** on the inverse petal coordinate `Φ` for a general domain `Ω`: on the
tail `tailStrip C B = {τ | C < Re τ, |Im τ| < B}` the values of `Φ` lie in `Ω`, `Φ` satisfies the
Abel equation `F (Φ τ) = Φ (τ + 1)`, and `Φ` is complex differentiable there. -/
def StripPropG (Ω : Set ℂ) (F Φ : ℂ → ℂ) (C B : ℝ) : Prop :=
  ∀ τ : ℂ, C < τ.re → |τ.im| < B →
    Φ τ ∈ Ω ∧ F (Φ τ) = Φ (τ + 1) ∧ DifferentiableAt ℂ Φ τ

/-- **Lifting the strip coordinate through the coverings `F^[n]` — general domain.**  `Ψ₀` is the
inverse Fatou coordinate on the horizontal tail strip `tailStrip C B`, satisfying the Abel
equation `F (Ψ₀ τ) = Ψ₀ (τ + 1)`.  We lift the map `τ ↦ Ψ₀ (τ + n)` through the covering
`F^[n] : Ω → Ω`: on the deeper strip `tailStrip (C - n) B` — convex, hence contractible, hence
simply connected — there is a continuous `X` with `F^[n] (X τ) = Ψ₀ (τ + n)`, and `X` agrees with
`Ψ₀` on `tailStrip C B` (uniqueness of lifts on the preconnected overlap). -/
theorem exists_strip_lift_general {F : ℂ → ℂ} {Ω : Set ℂ} {B C : ℝ} (hB : 0 < B)
    (hmap : Set.MapsTo F Ω Ω)
    (hcover : ∀ n : ℕ, IsCoveringMap
      (Work.FatouParabolic.Core.immBasinIterate Ω F hmap n))
    (Ψ₀ : ℂ → ℂ) (hΨ₀ : StripPropG Ω F Ψ₀ C B) (n : ℕ) :
    ∃ X : ℂ → ℂ, ContinuousOn X (Work.FatouParabolic.Core.tailStrip (C - (n : ℝ)) B) ∧
      (∀ τ ∈ Work.FatouParabolic.Core.tailStrip (C - (n : ℝ)) B,
        X τ ∈ Ω ∧ (F^[n]) (X τ) = Ψ₀ (τ + n)) ∧
      (∀ τ ∈ Work.FatouParabolic.Core.tailStrip C B, X τ = Ψ₀ τ) := by
  classical
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := by positivity
  -- The Abel equation, iterated: `F^[k] (Ψ₀ τ) = Ψ₀ (τ + k)` on the tail strip.
  have hiter : ∀ (τ : ℂ), τ ∈ Work.FatouParabolic.Core.tailStrip C B → ∀ k : ℕ,
      (F^[k]) (Ψ₀ τ) = Ψ₀ (τ + k) := by
    intro τ hτ k
    have hτre : C < τ.re := hτ.1
    induction k with
    | zero => simp
    | succ k ih =>
      have hk : C < (τ + (k : ℂ)).re ∧ |(τ + (k : ℂ)).im| < B := by
        have hre : (τ + (k : ℂ)).re = τ.re + (k : ℝ) := by simp
        have him : (τ + (k : ℂ)).im = τ.im := by simp
        exact ⟨by rw [hre]; linarith, by rw [him]; exact hτ.2⟩
      rw [Function.iterate_succ_apply', ih, (hΨ₀ (τ + (k : ℂ)) hk.1 hk.2).2.1]
      congr 1
      push_cast
      ring
  -- A base point of `tailStrip C B` (hence of the deeper strip as well).
  let τ₀ : ℂ := ((C + 1 : ℝ) : ℂ)
  have hτ₀re : τ₀.re = C + 1 := by simp [τ₀]
  have hτ₀im : τ₀.im = 0 := by simp [τ₀]
  have hτ₀S : τ₀ ∈ Work.FatouParabolic.Core.tailStrip C B := by
    refine ⟨?_, ?_⟩
    · rw [hτ₀re]; linarith
    · rw [hτ₀im]; simpa using hB
  have hτ₀A : τ₀ ∈ Work.FatouParabolic.Core.tailStrip (C - (n : ℝ)) B :=
    ⟨by rw [hτ₀re]; linarith, hτ₀S.2⟩
  -- `Ψ₀` is holomorphic (hence continuous) on the tail strip.
  have hΨdiff : DifferentiableOn ℂ Ψ₀ (Work.FatouParabolic.Core.tailStrip C B) :=
    fun τ hτ => ((hΨ₀ τ hτ.1 hτ.2).2.2).differentiableWithinAt
  have hΨcont : ContinuousOn Ψ₀ (Work.FatouParabolic.Core.tailStrip C B) := hΨdiff.continuousOn
  -- ... and so is `τ ↦ Ψ₀ (τ + n)` on the deeper strip.
  have hshift_maps : Set.MapsTo (fun z : ℂ => z + (n : ℂ))
      (Work.FatouParabolic.Core.tailStrip (C - (n : ℝ)) B)
      (Work.FatouParabolic.Core.tailStrip C B) := by
    intro z hz
    have hzre : C - (n : ℝ) < z.re := hz.1
    have hre : (z + (n : ℂ)).re = z.re + (n : ℝ) := by simp
    have him : (z + (n : ℂ)).im = z.im := by simp
    exact ⟨by rw [hre]; linarith, by rw [him]; exact hz.2⟩
  have hshift_cont : ContinuousOn (fun z : ℂ => Ψ₀ (z + (n : ℂ)))
      (Work.FatouParabolic.Core.tailStrip (C - (n : ℝ)) B) :=
    hΨcont.comp (continuous_id.add continuous_const).continuousOn hshift_maps
  -- instances on the strips
  haveI : LocallyPathConnectedSpace
      ↥(Work.FatouParabolic.Core.tailStrip (C - (n : ℝ)) B) :=
    (Work.FatouParabolic.Core.isOpen_tailStrip (C - (n : ℝ)) B).locallyPathConnectedSpace
  haveI : ContractibleSpace ↥(Work.FatouParabolic.Core.tailStrip (C - (n : ℝ)) B) :=
    (Work.FatouParabolic.Core.convex_tailStrip (C - (n : ℝ)) B).contractibleSpace ⟨τ₀, hτ₀A⟩
  haveI : SimplyConnectedSpace ↥(Work.FatouParabolic.Core.tailStrip (C - (n : ℝ)) B) :=
    SimplyConnectedSpace.ofContractible _
  haveI : PreconnectedSpace ↥(Work.FatouParabolic.Core.tailStrip C B) :=
    Subtype.preconnectedSpace (Work.FatouParabolic.Core.convex_tailStrip C B).isPreconnected
  -- The map we lift, and its value at the base point.
  let f : C(↥(Work.FatouParabolic.Core.tailStrip (C - (n : ℝ)) B), ↥Ω) :=
    ⟨fun σ => ⟨Ψ₀ (σ.1 + (n : ℂ)), (hΨ₀ _ (hshift_maps σ.2).1 (hshift_maps σ.2).2).1⟩,
      Continuous.subtype_mk (continuousOn_iff_continuous_domRestrict.mp hshift_cont) _⟩
  let e₀ : ↥Ω := ⟨Ψ₀ τ₀, (hΨ₀ τ₀ hτ₀S.1 hτ₀S.2).1⟩
  have hbase : Work.FatouParabolic.Core.immBasinIterate Ω F hmap n e₀ = f ⟨τ₀, hτ₀A⟩ := by
    refine Subtype.ext ?_
    rw [Work.FatouParabolic.Core.immBasinIterate_coe]
    change (F^[n]) (Ψ₀ τ₀) = Ψ₀ (τ₀ + (n : ℂ))
    rw [hiter τ₀ hτ₀S n]
  obtain ⟨Φ, ⟨hΦ0, hΦcomp⟩, -⟩ :=
    (hcover n).existsUnique_continuousMap_lifts f ⟨τ₀, hτ₀A⟩ e₀ hbase
  have hsub : Work.FatouParabolic.Core.tailStrip C B ⊆
      Work.FatouParabolic.Core.tailStrip (C - (n : ℝ)) B :=
    Work.FatouParabolic.Core.tailStrip_subset (by linarith)
  refine ⟨fun τ => if h : τ ∈ Work.FatouParabolic.Core.tailStrip (C - (n : ℝ)) B
      then (Φ ⟨τ, h⟩).1 else Ψ₀ τ, ?_, ?_, ?_⟩
  · rw [continuousOn_iff_continuous_domRestrict]
    have hfun : (Work.FatouParabolic.Core.tailStrip (C - (n : ℝ)) B).domRestrict
        (fun τ => if h : τ ∈ Work.FatouParabolic.Core.tailStrip (C - (n : ℝ)) B
          then (Φ ⟨τ, h⟩).1 else Ψ₀ τ)
        = fun σ : ↥(Work.FatouParabolic.Core.tailStrip (C - (n : ℝ)) B) => (Φ σ).1 := by
      funext σ
      exact dite_eq_left σ.2
    rw [hfun]
    exact continuous_subtype_val.comp Φ.continuous
  · intro τ hτ
    have hX : (if h : τ ∈ Work.FatouParabolic.Core.tailStrip (C - (n : ℝ)) B
        then (Φ ⟨τ, h⟩).1 else Ψ₀ τ) = (Φ ⟨τ, hτ⟩).1 := dite_eq_left hτ
    show (if h : τ ∈ Work.FatouParabolic.Core.tailStrip (C - (n : ℝ)) B
        then (Φ ⟨τ, h⟩).1 else Ψ₀ τ) ∈ Ω ∧
      (F^[n]) ((if h : τ ∈ Work.FatouParabolic.Core.tailStrip (C - (n : ℝ)) B
        then (Φ ⟨τ, h⟩).1 else Ψ₀ τ)) = Ψ₀ (τ + n)
    refine ⟨?_, ?_⟩
    · rw [hX]; exact (Φ ⟨τ, hτ⟩).2
    · rw [hX]
      have h2 := congrArg Subtype.val (congr_fun hΦcomp ⟨τ, hτ⟩)
      simp only [Function.comp_apply, Work.FatouParabolic.Core.immBasinIterate_coe] at h2
      exact h2
  · intro τ hτ
    have hXeq : (Φ ⟨τ, hsub hτ⟩).1 = Ψ₀ τ := by
      let u₁ : ↥(Work.FatouParabolic.Core.tailStrip C B) → ↥Ω :=
        fun σ => Φ ⟨σ.1, hsub σ.2⟩
      let u₂ : ↥(Work.FatouParabolic.Core.tailStrip C B) → ↥Ω :=
        fun σ => ⟨Ψ₀ σ.1, (hΨ₀ σ.1 σ.2.1 σ.2.2).1⟩
      have hcont₁ : Continuous u₁ :=
        Φ.continuous.comp (Continuous.subtype_mk continuous_subtype_val (fun σ => hsub σ.2))
      have hcont₂ : Continuous u₂ := by
        refine Continuous.subtype_mk ?_ _
        exact continuousOn_iff_continuous_domRestrict.mp hΨcont
      have heq : Work.FatouParabolic.Core.immBasinIterate Ω F hmap n ∘ u₁
          = Work.FatouParabolic.Core.immBasinIterate Ω F hmap n ∘ u₂ := by
        funext σ
        apply Subtype.ext
        have h2 := congrArg Subtype.val (congr_fun hΦcomp ⟨σ.1, hsub σ.2⟩)
        simp only [Function.comp_apply, Work.FatouParabolic.Core.immBasinIterate_coe] at h2
        show (F^[n]) ((Φ ⟨σ.1, hsub σ.2⟩).1) = (F^[n]) (Ψ₀ σ.1)
        rw [hiter σ.1 σ.2 n]
        exact h2
      have hbase2 : u₁ ⟨τ₀, hτ₀S⟩ = u₂ ⟨τ₀, hτ₀S⟩ := by
        refine Subtype.ext ?_
        have h1 : (⟨τ₀, hsub hτ₀S⟩ : ↥(Work.FatouParabolic.Core.tailStrip (C - (n : ℝ)) B))
            = ⟨τ₀, hτ₀A⟩ := Subtype.ext rfl
        calc (Φ ⟨τ₀, hsub hτ₀S⟩).1 = (Φ ⟨τ₀, hτ₀A⟩).1 := by rw [h1]
          _ = (e₀ : ℂ) := by rw [hΦ0]
          _ = Ψ₀ τ₀ := rfl
      have hfin := (hcover n).eq_of_comp_eq hcont₁ hcont₂ heq ⟨τ₀, hτ₀S⟩ hbase2
      have hval := congrArg Subtype.val (congrFun hfin ⟨τ, hτ⟩)
      simpa using hval
    show (if h : τ ∈ Work.FatouParabolic.Core.tailStrip (C - (n : ℝ)) B
        then (Φ ⟨τ, h⟩).1 else Ψ₀ τ) = Ψ₀ τ
    rw [dite_eq_left (hsub hτ), hXeq]


/-! ## The lifted family and its properties -/

/-- The lift of `τ ↦ Φ (τ + n)` through the covering `F^[n]` of `Ω`, on the deep strip
`tailStrip (C - n) B`, produced by `exists_strip_lift_general`. -/
noncomputable def petalLiftG (Ω : Set ℂ) (F : ℂ → ℂ)
    (hmap : Set.MapsTo F Ω Ω)
    (hcover : ∀ n : ℕ, IsCoveringMap (Work.FatouParabolic.Core.immBasinIterate Ω F hmap n))
    (Φ : ℂ → ℂ) (C B : ℝ) (hB : 0 < B) (hΦ : StripPropG Ω F Φ C B) (n : ℕ) : ℂ → ℂ :=
  Classical.choose (exists_strip_lift_general (F := F) (Ω := Ω) (B := B) (C := C)
    hB hmap hcover Φ hΦ n)

variable {F : ℂ → ℂ} {Ω : Set ℂ} {Φ : ℂ → ℂ} {C B C' B' : ℝ}
  {hmap : Set.MapsTo F Ω Ω}
  {hcover : ∀ n : ℕ, IsCoveringMap (Work.FatouParabolic.Core.immBasinIterate Ω F hmap n)}

theorem petalLiftG_continuousOn (hB : 0 < B) (hΦ : StripPropG Ω F Φ C B) (n : ℕ) :
    ContinuousOn (petalLiftG Ω F hmap hcover Φ C B hB hΦ n)
      (Work.FatouParabolic.Core.tailStrip (C - (n : ℝ)) B) :=
  (Classical.choose_spec (exists_strip_lift_general (F := F) (Ω := Ω) (B := B) (C := C)
    hB hmap hcover Φ hΦ n)).1

theorem petalLiftG_mem (hB : 0 < B) (hΦ : StripPropG Ω F Φ C B) (n : ℕ) {τ : ℂ}
    (hτ : τ ∈ Work.FatouParabolic.Core.tailStrip (C - (n : ℝ)) B) :
    petalLiftG Ω F hmap hcover Φ C B hB hΦ n τ ∈ Ω :=
  ((Classical.choose_spec (exists_strip_lift_general (F := F) (Ω := Ω) (B := B) (C := C)
    hB hmap hcover Φ hΦ n)).2.1 τ hτ).1

theorem petalLiftG_comp (hB : 0 < B) (hΦ : StripPropG Ω F Φ C B) (n : ℕ) {τ : ℂ}
    (hτ : τ ∈ Work.FatouParabolic.Core.tailStrip (C - (n : ℝ)) B) :
    (F^[n]) (petalLiftG Ω F hmap hcover Φ C B hB hΦ n τ) = Φ (τ + (n : ℂ)) :=
  ((Classical.choose_spec (exists_strip_lift_general (F := F) (Ω := Ω) (B := B) (C := C)
    hB hmap hcover Φ hΦ n)).2.1 τ hτ).2

theorem petalLiftG_agree (hB : 0 < B) (hΦ : StripPropG Ω F Φ C B) (n : ℕ) {τ : ℂ}
    (hτ : τ ∈ Work.FatouParabolic.Core.tailStrip C B) :
    petalLiftG Ω F hmap hcover Φ C B hB hΦ n τ = Φ τ :=
  (Classical.choose_spec (exists_strip_lift_general (F := F) (Ω := Ω) (B := B) (C := C)
    hB hmap hcover Φ hΦ n)).2.2 τ hτ

/-- Iterated Abel equation along real translations. -/
theorem petal_shift_iterateG (hΦ : StripPropG Ω F Φ C B) {s : ℂ} (hs : C < s.re)
    (hsB : |s.im| < B) (j : ℕ) : (F^[j]) (Φ s) = Φ (s + (j : ℂ)) := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hs' : C < (s + (j : ℂ)).re ∧ |(s + (j : ℂ)).im| < B := by
      refine ⟨?_, ?_⟩
      · have h : (s + (j : ℂ)).re = s.re + (j : ℝ) := by simp
        rw [h]; linarith [Nat.cast_nonneg (α := ℝ) j]
      · have h : (s + (j : ℂ)).im = s.im := by simp
        rw [h]; exact hsB
    rw [Function.iterate_succ_apply', ih, (hΦ (s + (j : ℂ)) hs'.1 hs'.2).2.1]
    congr 1
    push_cast
    ring

/-- The lift `X = petalLiftG … n` satisfies `F^[k] (X τ) = Φ (τ + k)` for every `k ≥ n` on its
domain. -/
theorem petalLiftG_iterate_apply (hB : 0 < B) (hΦ : StripPropG Ω F Φ C B) {n k : ℕ}
    (hk : n ≤ k) {τ : ℂ} (hτ : τ ∈ Work.FatouParabolic.Core.tailStrip (C - (n : ℝ)) B) :
    (F^[k]) (petalLiftG Ω F hmap hcover Φ C B hB hΦ n τ) = Φ (τ + (k : ℂ)) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + n := ⟨k - n, (Nat.sub_add_cancel hk).symm⟩
  have hcomp := petalLiftG_comp (hmap := hmap) (hcover := hcover) hB hΦ n hτ
  have hsre : C < (τ + (n : ℂ)).re := by
    have h : (τ + (n : ℂ)).re = τ.re + (n : ℝ) := by simp
    rw [h]
    linarith [hτ.1, Nat.cast_nonneg (α := ℝ) n]
  have hsim : |(τ + (n : ℂ)).im| < B := by
    have h : (τ + (n : ℂ)).im = τ.im := by simp
    rw [h]; exact hτ.2
  calc (F^[m + n]) (petalLiftG Ω F hmap hcover Φ C B hB hΦ n τ)
      = (F^[m]) ((F^[n]) (petalLiftG Ω F hmap hcover Φ C B hB hΦ n τ)) :=
        Function.iterate_add_apply F m n _
    _ = (F^[m]) (Φ (τ + (n : ℂ))) := by rw [hcomp]
    _ = Φ (τ + (n : ℂ) + (m : ℂ)) :=
        petal_shift_iterateG (Ω := Ω) (F := F) (Φ := Φ) (C := C) (B := B) hΦ hsre hsim m
    _ = Φ (τ + ((m + n : ℕ) : ℂ)) := by
        congr 1
        push_cast
        ring

/-- **Two lifts agree on the intersection of their domains.** -/
theorem petalLiftG_eqOn (hB : 0 < B) (hB' : 0 < B')
    (hΦ : StripPropG Ω F Φ C B) (hΦ' : StripPropG Ω F Φ C' B') (n n' : ℕ) {τ : ℂ}
    (hτ : τ ∈ Work.FatouParabolic.Core.tailStrip (C - (n : ℝ)) B ∩
      Work.FatouParabolic.Core.tailStrip (C' - (n' : ℝ)) B') :
    petalLiftG Ω F hmap hcover Φ C B hB hΦ n τ
      = petalLiftG Ω F hmap hcover Φ C' B' hB' hΦ' n' τ := by
  classical
  set X := petalLiftG Ω F hmap hcover Φ C B hB hΦ n with hXdef
  set Y := petalLiftG Ω F hmap hcover Φ C' B' hB' hΦ' n' with hYdef
  set k := max n n' with hkdef
  set A : Set ℂ := Work.FatouParabolic.Core.tailStrip (C - (n : ℝ)) B ∩
    Work.FatouParabolic.Core.tailStrip (C' - (n' : ℝ)) B' with hAdef
  have hnk : n ≤ k := le_max_left _ _
  have hn'k : n' ≤ k := le_max_right _ _
  have hAconvex : Convex ℝ A := by
    rw [hAdef]; exact (Work.FatouParabolic.Core.convex_tailStrip _ _).inter
      (Work.FatouParabolic.Core.convex_tailStrip _ _)
  have hne : ((max C C' + 1 : ℝ) : ℂ) ∈
      Work.FatouParabolic.Core.tailStrip (max C C') (min B B') := by
    refine ⟨?_, ?_⟩
    · simp
    · have h : (((max C C' + 1 : ℝ) : ℂ)).im = 0 := by simp
      rw [h]
      simpa using lt_min hB hB'
  set τ₁ : ℂ := ((max C C' + 1 : ℝ) : ℂ) with hτ₁def
  have hτ₁ : τ₁ ∈ Work.FatouParabolic.Core.tailStrip (max C C') (min B B') := hne
  have hτ₁C : τ₁ ∈ Work.FatouParabolic.Core.tailStrip C B :=
    ⟨lt_of_le_of_lt (le_max_left C C') hτ₁.1, lt_of_lt_of_le hτ₁.2 (min_le_left B B')⟩
  have hτ₁C' : τ₁ ∈ Work.FatouParabolic.Core.tailStrip C' B' :=
    ⟨lt_of_le_of_lt (le_max_right C C') hτ₁.1, lt_of_lt_of_le hτ₁.2 (min_le_right B B')⟩
  have hτ₁A : τ₁ ∈ A := by
    rw [hAdef]
    refine ⟨Work.FatouParabolic.Core.tailStrip_subset (by simp) hτ₁C,
      Work.FatouParabolic.Core.tailStrip_subset (by simp) hτ₁C'⟩
  haveI : PreconnectedSpace ↥A := Subtype.preconnectedSpace hAconvex.isPreconnected
  have hXcont : ContinuousOn X A :=
    (petalLiftG_continuousOn (hmap := hmap) (hcover := hcover) hB hΦ n).mono
      inter_subset_left
  have hYcont : ContinuousOn Y A :=
    (petalLiftG_continuousOn (hmap := hmap) (hcover := hcover) hB' hΦ' n').mono
      inter_subset_right
  let u₁ : ↥A → ↥Ω := fun σ => ⟨X σ.1, petalLiftG_mem hB hΦ n σ.2.1⟩
  let u₂ : ↥A → ↥Ω := fun σ => ⟨Y σ.1, petalLiftG_mem hB' hΦ' n' σ.2.2⟩
  have hcont₁ : Continuous u₁ :=
    Continuous.subtype_mk (continuousOn_iff_continuous_domRestrict.mp hXcont) _
  have hcont₂ : Continuous u₂ :=
    Continuous.subtype_mk (continuousOn_iff_continuous_domRestrict.mp hYcont) _
  have heq : Work.FatouParabolic.Core.immBasinIterate Ω F hmap k ∘ u₁
      = Work.FatouParabolic.Core.immBasinIterate Ω F hmap k ∘ u₂ := by
    funext σ
    apply Subtype.ext
    simp only [Function.comp_apply, Work.FatouParabolic.Core.immBasinIterate_coe]
    rw [petalLiftG_iterate_apply (hmap := hmap) (hcover := hcover) hB hΦ hnk σ.2.1,
      petalLiftG_iterate_apply (hmap := hmap) (hcover := hcover) hB' hΦ' hn'k σ.2.2]
  have hbase : u₁ ⟨τ₁, hτ₁A⟩ = u₂ ⟨τ₁, hτ₁A⟩ := by
    apply Subtype.ext
    simp only [u₁, u₂]
    rw [hXdef, hYdef,
      petalLiftG_agree (hmap := hmap) (hcover := hcover) hB hΦ n hτ₁C,
      petalLiftG_agree (hmap := hmap) (hcover := hcover) hB' hΦ' n' hτ₁C']
  have hfin := (hcover k).eq_of_comp_eq hcont₁ hcont₂ heq ⟨τ₁, hτ₁A⟩ hbase
  have hval := congrArg Subtype.val (congrFun hfin ⟨τ, hτ⟩)
  simpa [u₁, u₂] using hval

/-! ## The Liouville contradiction on a general domain -/

/-- **The Liouville contradiction on a general domain.**  If a domain `Ω` is `F`-invariant and
bounded, if every iterate `F^[n] : Ω → Ω` is a covering when `F` has no critical point on `Ω`, and
if the inverse petal coordinate `Φ` exists on the tail of every horizontal strip, then `F` has a
critical point in `Ω`.  (Stated as `False` under the no-critical-point hypothesis.) -/
theorem false_of_petalInverse_of_covering_general {F : ℂ → ℂ} {Ω : Set ℂ}
    (hFdiff : Differentiable ℂ F) (hmap : Set.MapsTo F Ω Ω)
    (hcover : ∀ n : ℕ, IsCoveringMap (Work.FatouParabolic.Core.immBasinIterate Ω F hmap n))
    (hbdd : Bornology.IsBounded Ω)
    (hnocrit : ∀ w ∈ Ω, deriv F w ≠ 0)
    (hpetal : ∃ Φ : ℂ → ℂ, ∀ B : ℝ, 0 < B → ∃ C : ℝ,
      StripPropG Ω F Φ C B ∧
      Set.InjOn Φ (Work.FatouParabolic.Core.tailStrip C B)) :
    False := by
  obtain ⟨Φ, hΦ⟩ := hpetal
  classical
  have hdata : ∀ B : ℝ, ∀ hB : 0 < B,
      ∃ C : ℝ, StripPropG Ω F Φ C B ∧
        Set.InjOn Φ (Work.FatouParabolic.Core.tailStrip C B) := fun B hB => hΦ B hB
  let Lvl : (B : ℝ) → 0 < B → ℝ := fun B hB => Classical.choose (hdata B hB)
  have Lvl_spec : ∀ (B : ℝ) (hB : 0 < B),
      StripPropG Ω F Φ (Lvl B hB) B ∧
        Set.InjOn Φ (Work.FatouParabolic.Core.tailStrip (Lvl B hB) B) :=
    fun B hB => Classical.choose_spec (hdata B hB)
  let Ht : ℂ → ℝ := fun τ => |τ.im| + 1
  have Ht_pos : ∀ τ : ℂ, 0 < Ht τ := fun τ => by
    have h : (0 : ℝ) ≤ |τ.im| := abs_nonneg _
    simp only [Ht]; linarith
  let Lv : ℂ → ℝ := fun τ => Lvl (Ht τ) (Ht_pos τ)
  have Lv_spec : ∀ τ : ℂ, StripPropG Ω F Φ (Lv τ) (Ht τ) :=
    fun τ => (Lvl_spec (Ht τ) (Ht_pos τ)).1
  let Idx : ℂ → ℕ := fun τ => Classical.choose (exists_nat_gt (Lv τ - τ.re))
  have Idx_spec : ∀ τ : ℂ, Lv τ - ((Idx τ : ℕ) : ℝ) < τ.re := by
    intro τ
    have h := Classical.choose_spec (exists_nat_gt (Lv τ - τ.re))
    simp only [Idx]
    linarith
  let Ψ : ℂ → ℂ := fun τ => petalLiftG Ω F hmap hcover Φ (Lv τ) (Ht τ) (Ht_pos τ)
    (Lv_spec τ) (Idx τ) τ
  have hΨval : ∀ τ : ℂ, Ψ τ = petalLiftG Ω F hmap hcover Φ (Lv τ) (Ht τ) (Ht_pos τ)
      (Lv_spec τ) (Idx τ) τ := fun τ => rfl
  have hΨmem : ∀ τ : ℂ, Ψ τ ∈ Ω := by
    intro τ
    rw [hΨval τ]
    refine petalLiftG_mem (hmap := hmap) (hcover := hcover) (hB := Ht_pos τ) (hΦ := Lv_spec τ)
      (Idx τ) ⟨Idx_spec τ, ?_⟩
    have h : (0 : ℝ) ≤ |τ.im| := abs_nonneg _
    simp only [Ht]; linarith
  have hlift_diff : ∀ (C B : ℝ) (hB : 0 < B) (hΦ' : StripPropG Ω F Φ C B) (n : ℕ),
      DifferentiableOn ℂ (petalLiftG Ω F hmap hcover Φ C B hB hΦ' n)
        (Work.FatouParabolic.Core.tailStrip (C - ((n : ℕ) : ℝ)) B) := by
    intro C B hB hΦ' n
    refine Work.FatouParabolic.Core.ImmBasin.differentiableOn_of_comp_iterate_eq (n := n) hFdiff
      hmap hnocrit (Work.FatouParabolic.Core.isOpen_tailStrip _ _)
      (petalLiftG_continuousOn (hmap := hmap) (hcover := hcover) hB hΦ' n)
      (fun τ hτ => petalLiftG_mem (hmap := hmap) (hcover := hcover) hB hΦ' n hτ)
      ?_ (fun τ hτ => petalLiftG_comp (hmap := hmap) (hcover := hcover) hB hΦ' n hτ)
    intro τ hτ
    have hmem : τ + (n : ℂ) ∈ Work.FatouParabolic.Core.tailStrip C B := by
      refine ⟨?_, ?_⟩
      · have h : (τ + (n : ℂ)).re = τ.re + (n : ℝ) := by simp
        rw [h]
        have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        linarith [hτ.1]
      · have h : (τ + (n : ℂ)).im = τ.im := by simp
        rw [h]; exact hτ.2
    have hg : DifferentiableAt ℂ (fun σ : ℂ => σ + (n : ℂ)) τ :=
      differentiableAt_id.add_const _
    exact (((hΦ' (τ + (n : ℂ)) hmem.1 hmem.2).2.2).comp τ hg).differentiableWithinAt
  have hΨdiff : Differentiable ℂ Ψ := by
    intro τ₀
    set C₀ : ℝ := Lv τ₀ with hC₀def
    set B₀ : ℝ := Ht τ₀ with hB₀def
    set n₀ : ℕ := Idx τ₀ with hn₀def
    have hB₀pos : 0 < B₀ := by rw [hB₀def]; exact Ht_pos τ₀
    have hC₀spec : StripPropG Ω F Φ C₀ B₀ := by rw [hC₀def, hB₀def]; exact Lv_spec τ₀
    have hn₀spec : C₀ - ((n₀ : ℕ) : ℝ) < τ₀.re := by rw [hC₀def, hn₀def]; exact Idx_spec τ₀
    have hδpos : 0 < min (1 / 2 : ℝ) ((τ₀.re - (C₀ - ((n₀ : ℕ) : ℝ))) / 2) :=
      lt_min (by norm_num) (by linarith)
    have hev : Ψ =ᶠ[𝓝 τ₀] (petalLiftG Ω F hmap hcover Φ C₀ B₀ hB₀pos hC₀spec n₀) := by
      refine Filter.eventually_of_mem (Metric.ball_mem_nhds τ₀ hδpos) (fun τ hτ => ?_)
      rw [Metric.mem_ball] at hτ
      have hdist1 : dist τ τ₀ < 1 / 2 := lt_of_lt_of_le hτ (min_le_left _ _)
      have hdist2 : dist τ τ₀ < (τ₀.re - (C₀ - ((n₀ : ℕ) : ℝ))) / 2 :=
        lt_of_lt_of_le hτ (min_le_right _ _)
      have hre : C₀ - ((n₀ : ℕ) : ℝ) < τ.re := by
        have h1 : |τ.re - τ₀.re| ≤ dist τ τ₀ := by
          have h := Complex.abs_re_le_norm (τ - τ₀)
          rw [Complex.sub_re] at h
          rwa [Complex.dist_eq]
        have h2 : τ₀.re - τ.re ≤ dist τ τ₀ := by
          have := (abs_le.mp h1).1
          linarith
        linarith
      have him : |τ.im| < B₀ := by
        have h1 : |τ.im - τ₀.im| ≤ dist τ τ₀ := by
          have h := Complex.abs_im_le_norm (τ - τ₀)
          rw [Complex.sub_im] at h
          rwa [Complex.dist_eq]
        have h2 : |τ.im| - |τ₀.im| ≤ |τ.im - τ₀.im| := abs_sub_abs_le_abs_sub _ _
        have hB₀val : B₀ = |τ₀.im| + 1 := by rw [hB₀def]
        rw [hB₀val]
        linarith
      rw [hΨval τ]
      exact petalLiftG_eqOn (hmap := hmap) (hcover := hcover) (hB := Ht_pos τ) (hB' := hB₀pos)
        (hΦ := Lv_spec τ) (hΦ' := hC₀spec) (n := Idx τ) (n' := n₀)
        ⟨⟨Idx_spec τ, by simp only [Ht]; linarith [abs_nonneg τ.im]⟩, ⟨hre, him⟩⟩
    have hX₀ : DifferentiableAt ℂ (petalLiftG Ω F hmap hcover Φ C₀ B₀ hB₀pos hC₀spec n₀) τ₀ :=
      (hlift_diff C₀ B₀ hB₀pos hC₀spec n₀).differentiableAt
        ((Work.FatouParabolic.Core.isOpen_tailStrip _ _).mem_nhds ⟨hn₀spec, by
          have hB₀val : B₀ = |τ₀.im| + 1 := by rw [hB₀def]
          rw [hB₀val]; linarith [abs_nonneg τ₀.im]⟩)
    exact hev.differentiableAt_iff.mpr hX₀
  have hΨbdd : Bornology.IsBounded (Set.range Ψ) :=
    hbdd.subset (fun z hz => by obtain ⟨τ, rfl⟩ := hz; exact hΨmem τ)
  set C₁ : ℝ := Lvl 1 one_pos with hC₁def
  have hC₁ : StripPropG Ω F Φ C₁ 1 ∧
      Set.InjOn Φ (Work.FatouParabolic.Core.tailStrip C₁ 1) := by
    rw [hC₁def]; exact Lvl_spec 1 one_pos
  have hΨeq : ∀ τ ∈ Work.FatouParabolic.Core.tailStrip C₁ 1, Ψ τ = Φ τ := by
    intro τ hτ
    obtain ⟨m, hm⟩ : ∃ m : ℕ, C₁ - ((m : ℕ) : ℝ) < τ.re := by
      obtain ⟨m, hm⟩ := exists_nat_gt (C₁ - τ.re)
      exact ⟨m, by linarith⟩
    rw [hΨval τ]
    have h1 : petalLiftG Ω F hmap hcover Φ (Lv τ) (Ht τ) (Ht_pos τ) (Lv_spec τ)
        (Idx τ) τ = petalLiftG Ω F hmap hcover Φ C₁ 1 one_pos hC₁.1 m τ :=
      petalLiftG_eqOn (hmap := hmap) (hcover := hcover) (hB := Ht_pos τ) (hB' := one_pos)
        (hΦ := Lv_spec τ) (hΦ' := hC₁.1) (n := Idx τ) (n' := m)
        ⟨⟨Idx_spec τ, by simp only [Ht]; linarith [abs_nonneg τ.im]⟩,
          ⟨hm, by simpa using hτ.2⟩⟩
    have h2 : petalLiftG Ω F hmap hcover Φ C₁ 1 one_pos hC₁.1 m τ = Φ τ :=
      petalLiftG_agree (hmap := hmap) (hcover := hcover) (hB := one_pos) (hΦ := hC₁.1) m hτ
    exact h1.trans h2
  have hconst := hΨdiff.apply_eq_apply_of_bounded hΨbdd
  have hτ₁ : ((C₁ + 1 : ℝ) : ℂ) ∈ Work.FatouParabolic.Core.tailStrip C₁ 1 := by
    refine ⟨?_, ?_⟩ <;> simp
  have hτ₂ : ((C₁ + 2 : ℝ) : ℂ) ∈ Work.FatouParabolic.Core.tailStrip C₁ 1 := by
    refine ⟨?_, ?_⟩ <;> simp
  have hne : ((C₁ + 1 : ℝ) : ℂ) ≠ ((C₁ + 2 : ℝ) : ℂ) := by
    intro h
    have := congrArg Complex.re h
    simp only [Complex.ofReal_re] at this
    linarith
  refine hne (hC₁.2 hτ₁ hτ₂ ?_)
  have hc := hconst ((C₁ + 1 : ℝ) : ℂ) ((C₁ + 2 : ℝ) : ℂ)
  rwa [hΨeq _ hτ₁, hΨeq _ hτ₂] at hc

end
end Work.SeedLimit.MultiPetal
