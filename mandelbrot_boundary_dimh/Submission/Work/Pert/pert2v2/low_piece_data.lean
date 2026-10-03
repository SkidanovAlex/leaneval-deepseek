import Mathlib
import Submission.Work.Pert.RBlock4.Rlow_holo
import Submission.Work.Pert.RBlock
import Submission.Work.Pert.MaxDom
import Submission.Work.Pert.pert2v2.glue_window

namespace Work.Pert.pert2v2

open Set Filter
open scoped Topology

/-- **Image of an open set under a holomorphic map with nowhere vanishing derivative.**  If `U` is
open, contained in the open set `Q` on which `Φ` is holomorphic, and `deriv Φ ≠ 0` at every point of
`U`, then `Φ '' U` is open.  At a point `z₀ ∈ U`, `Φ` has a nonvanishing strict derivative at `z₀`,
so it maps neighbourhoods of `z₀` onto neighbourhoods of `Φ z₀`; since `U` is a neighbourhood of
`z₀`, its image is a neighbourhood of `Φ z₀`. -/
private theorem low_image_open {Φ : ℂ → ℂ} {Q U : Set ℂ} (hQ : IsOpen Q) (hU : IsOpen U)
    (hUQ : U ⊆ Q) (hΦ : DifferentiableOn ℂ Φ Q) (hder : ∀ z ∈ U, deriv Φ z ≠ 0) :
    IsOpen (Φ '' U) := by
  rw [isOpen_iff_mem_nhds]
  rintro y ⟨z₀, hz₀U, rfl⟩
  have hz₀Q : z₀ ∈ Q := hUQ hz₀U
  have hana : AnalyticAt ℂ Φ z₀ := hΦ.analyticAt (hQ.mem_nhds hz₀Q)
  have hmap : map Φ (𝓝 z₀) = 𝓝 (Φ z₀) := hana.hasStrictDerivAt.map_nhds_eq (hder z₀ hz₀U)
  rw [← hmap, Filter.mem_map]
  exact Filter.mem_of_superset (hU.mem_nhds hz₀U) fun x hx => ⟨x, hx, rfl⟩

/-- **Continuity of the iterated orbit map `z ↦ f^[n] (φ z)`.**  If `V` is open, `φ` is
differentiable on `V`, `Df` is open and `f` is differentiable on `Df`, and the first `n` points of
the orbit of `φ w` lie in `Df`, then `z ↦ f^[n] (φ z)` is continuous at `w`. -/
private theorem low_continuousAt_iterate {f φ : ℂ → ℂ} {Df V : Set ℂ} (hV : IsOpen V)
    (hφ : DifferentiableOn ℂ φ V) (hDf : IsOpen Df) (hf : DifferentiableOn ℂ f Df)
    {w : ℂ} (hwV : w ∈ V) (n : ℕ) (horb : ∀ i : ℕ, i < n → f^[i] (φ w) ∈ Df) :
    ContinuousAt (fun z => f^[n] (φ z)) w := by
  have hφc : ContinuousAt φ w := hφ.continuousOn.continuousAt (hV.mem_nhds hwV)
  revert horb
  induction n with
  | zero => intro horb; exact hφc
  | succ n ih =>
    intro horb
    have horb' : ∀ i : ℕ, i < n → f^[i] (φ w) ∈ Df :=
      fun i hi => horb i (lt_trans hi (Nat.lt_succ_self n))
    have hc1 : ContinuousAt (fun z => f^[n] (φ z)) w := ih horb'
    have hfm : f^[n] (φ w) ∈ Df := horb n (Nat.lt_succ_self n)
    have hc2 : ContinuousAt f (f^[n] (φ w)) := hf.continuousOn.continuousAt (hDf.mem_nhds hfm)
    have h := hc2.comp' (f := fun z => f^[n] (φ z)) (g := f) hc1
    simpa [Function.iterate_succ_apply'] using h

/-- **The low piece of the two-piece glue (openness + holomorphy).**  With
`Ulow := {w | w ∈ V ∧ |w.re| < 1/2 ∧ |w.im| < Tb ∧ (∀ j ≤ m, f^[j] (φ w) ∈ Df) ∧ f^[m] (φ w) ∈ τ '' Qp'}`,
show the two inputs `tSat_glue_window` needs for this chart: `Ulow` is open, and
`Work.Pert.Rlow f Qp' τ Φp φ m k dlow` is holomorphic on it.

* Holomorphy: apply `Work.Pert.RBlock4.Rlow_holo` (proved) with `U := Ulow`; its `hwalk`/`hland`
  are literally conjuncts 4 and 5 of `Ulow`, and `hφ : DifferentiableOn ℂ φ V` restricts by `mono`
  because `Ulow ⊆ V`.
* Openness — **use this order** (the naive "intersection of opens" does not work, since continuity
  of `f^[j] ∘ φ` at `w` needs the orbit points to lie in the open `Df`): first show
  `A j := {w | w ∈ V ∧ ∀ i ≤ j, f^[i] (φ w) ∈ Df}` is open by induction on `j` (at
  `w ∈ A j`, `φ` is continuous on the open `V` and `f` is continuous on the open `Df`
  — `DifferentiableOn.continuousOn` — so `f^[j] ∘ φ` is continuous at `w`), then intersect with the
  open preimage `(f^[m] ∘ φ)⁻¹ (τ '' Qp')`, which is legitimate on `A m` by that continuity.
  `τ '' Qp'` is open by the local-inverse argument (holomorphic `τ`, `Qp' ⊆ Qp` open,
  `deriv τ z ≠ 0` on `Qp'`) — the same step as in `Work.Pert.pert2v2.high_piece_data`. -/
theorem low_piece_data {f φ τ Φp : ℂ → ℂ} {Df Qp Qp' V : Set ℂ} {Tb : ℝ} {m : ℕ} {k : ℤ}
    {dlow : ℂ}
    (hV : IsOpen V) (hVsub : {w : ℂ | |w.re| < 1 / 2} ⊆ V) (hφ : DifferentiableOn ℂ φ V)
    (hDf : IsOpen Df) (hf : DifferentiableOn ℂ f Df)
    (hQp : IsOpen Qp) (hQp' : IsOpen Qp') (hQp'sub : Qp' ⊆ Qp)
    (hτ : DifferentiableOn ℂ τ Qp) (hτne : ∀ z ∈ Qp', deriv τ z ≠ 0) (hinj : Set.InjOn τ Qp')
    (hΦp : DifferentiableOn ℂ Φp Qp) :
    IsOpen {w : ℂ | w ∈ V ∧ |w.re| < 1 / 2 ∧ |w.im| < Tb ∧
        (∀ j : ℕ, j ≤ m → f^[j] (φ w) ∈ Df) ∧ f^[m] (φ w) ∈ τ '' Qp'} ∧
      DifferentiableOn ℂ (Work.Pert.Rlow f Qp' τ Φp φ m k dlow)
        {w : ℂ | w ∈ V ∧ |w.re| < 1 / 2 ∧ |w.im| < Tb ∧
          (∀ j : ℕ, j ≤ m → f^[j] (φ w) ∈ Df) ∧ f^[m] (φ w) ∈ τ '' Qp'} := by
  classical
  -- the subgate image is open (the local inverse of `τ` on `Qp'`)
  have himg : IsOpen (τ '' Qp') := low_image_open hQp hQp' hQp'sub hτ hτne
  -- the open strip
  have hstrip : IsOpen {w : ℂ | |w.re| < 1 / 2 ∧ |w.im| < Tb} :=
    (isOpen_lt Complex.continuous_re.abs continuous_const).inter
      (isOpen_lt Complex.continuous_im.abs continuous_const)
  -- the walk condition `A m = {w | w ∈ V ∧ ∀ j ≤ m, f^[j] (φ w) ∈ Df}` is open
  have hA : IsOpen {w : ℂ | w ∈ V ∧ ∀ j : ℕ, j ≤ m → f^[j] (φ w) ∈ Df} := by
    induction m with
    | zero =>
      -- `A 0 = V ∩ φ ⁻¹' Df`
      have hbase : {w : ℂ | w ∈ V ∧ ∀ j : ℕ, j ≤ 0 → f^[j] (φ w) ∈ Df} = V ∩ φ ⁻¹' Df := by
        ext w
        constructor
        · rintro ⟨h1, h2⟩
          exact ⟨h1, by simpa using h2 0 le_rfl⟩
        · rintro ⟨h1, h2⟩
          refine ⟨h1, fun j hj => ?_⟩
          obtain rfl : j = 0 := Nat.le_zero.mp hj
          simpa using h2
      rw [hbase, isOpen_iff_mem_nhds]
      intro w hw
      exact Filter.inter_mem (hV.mem_nhds hw.1)
        ((hφ.continuousOn.continuousAt (hV.mem_nhds hw.1)).preimage_mem_nhds
          (hDf.mem_nhds hw.2))
    | succ n ih =>
      -- `A (n+1) = A n ∩ (f^[n+1] ∘ φ) ⁻¹' Df`
      have hstep : {w : ℂ | w ∈ V ∧ ∀ j : ℕ, j ≤ n + 1 → f^[j] (φ w) ∈ Df} =
          {w : ℂ | w ∈ V ∧ ∀ j : ℕ, j ≤ n → f^[j] (φ w) ∈ Df} ∩
            (fun w => f^[n + 1] (φ w)) ⁻¹' Df := by
        ext w
        constructor
        · rintro ⟨h1, h2⟩
          exact ⟨⟨h1, fun j hj => h2 j (Nat.le_succ_iff.mpr (Or.inl hj))⟩, h2 (n + 1) le_rfl⟩
        · rintro ⟨⟨h1, h2⟩, h3⟩
          refine ⟨h1, fun j hj => ?_⟩
          rcases Nat.lt_or_eq_of_le hj with hlt | heq
          · exact h2 j (Nat.lt_succ_iff.mp hlt)
          · rw [heq]; exact h3
      rw [hstep, isOpen_iff_mem_nhds]
      intro w hw
      obtain ⟨hwA, hwC⟩ := hw
      -- the orbit of `φ w` up to level `n` stays in `Df`
      have horb : ∀ i : ℕ, i < n + 1 → f^[i] (φ w) ∈ Df := by
        intro i hi
        rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hi) with hlt | heq
        · exact hwA.2 i (le_of_lt hlt)
        · rw [heq]; exact hwA.2 n le_rfl
      exact Filter.inter_mem (ih.mem_nhds hwA)
        ((low_continuousAt_iterate hV hφ hDf hf hwA.1 (n + 1) horb).preimage_mem_nhds
          (hDf.mem_nhds hwC))
  -- the preimage of the subgate, taken over the walk condition
  have hpre : IsOpen ({w : ℂ | w ∈ V ∧ ∀ j : ℕ, j ≤ m → f^[j] (φ w) ∈ Df} ∩
      (fun w => f^[m] (φ w)) ⁻¹' (τ '' Qp')) := by
    rw [isOpen_iff_mem_nhds]
    intro w hw
    obtain ⟨hwA, hwC⟩ := hw
    exact Filter.inter_mem (hA.mem_nhds hwA)
      ((low_continuousAt_iterate hV hφ hDf hf hwA.1 m
        (fun i hi => hwA.2 i (le_of_lt hi))).preimage_mem_nhds (himg.mem_nhds hwC))
  -- openness of the low piece
  have hS : IsOpen {w : ℂ | w ∈ V ∧ |w.re| < 1 / 2 ∧ |w.im| < Tb ∧
      (∀ j : ℕ, j ≤ m → f^[j] (φ w) ∈ Df) ∧ f^[m] (φ w) ∈ τ '' Qp'} := by
    have hmain : IsOpen ((V ∩ {w : ℂ | |w.re| < 1 / 2 ∧ |w.im| < Tb}) ∩
        ({w : ℂ | w ∈ V ∧ ∀ j : ℕ, j ≤ m → f^[j] (φ w) ∈ Df} ∩
          (fun w => f^[m] (φ w)) ⁻¹' (τ '' Qp'))) :=
      (hV.inter hstrip).inter hpre
    convert hmain using 1
    ext w
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage]
    tauto
  -- holomorphy of the low return map: `Rlow_holo` with `U := Ulow`
  refine ⟨hS, ?_⟩
  exact Work.Pert.RBlock4.Rlow_holo hS hDf hf hQp hQp' hQp'sub hτ hτne hinj hΦp
    (hφ.mono fun w hw => hw.1) (fun w hw j hj => hw.2.2.2.1 j hj) (fun w hw => hw.2.2.2.2)

end Work.Pert.pert2v2
